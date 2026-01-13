/*
 * sudo_monitor.cpp (sudo_monitor v1.0 [C++20])
  
 * Sudo plugin that intercepts privileged commands and logs everything
   useful about them - who ran what, from where, process details, and
   any child processes that got spawned along the way.
  
 * Build: g++ -std=c++20 -Wall -Wextra -fPIC -shared -O2 -o sudo_monitor.so sudo_monitor.cpp
 
 * By adding "Plugin sudo_monitor sudo_monitor.so" to /etc/sudo.conf,
   we notify sudo about the plugin
 */

#include <string>
#include <string_view>
#include <optional>
#include <vector>
#include <array>
#include <span>
#include <format>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <algorithm>
#include <ranges>
#include <charconv>
#include <cstdio>
#include <cstring>
#include <ctime>
#include <unistd.h>
#include <pwd.h>
#include <grp.h>
#include <sys/stat.h>

namespace fs = std::filesystem;
using namespace std::string_view_literals;

/*
 * Sudo plugin API - this is the "contract" between us and sudo
  I chose version 1.17 becasue it is widely supported
 */
 
constexpr unsigned int SUDO_API_VER = (1u << 16) | 17u;
constexpr unsigned int SUDO_IO_PLUGIN_TYPE = 2u;
constexpr int MSG_INFO = 0x0004;

using PrintFunc = int(*)(int, const char*, ...);

struct io_plugin {
    unsigned int type, version;
    int  (*open)(unsigned int, void*, PrintFunc, char* const[], char* const[],
                 char* const[], int, char* const[], char* const[], char* const[],
                 const char**);
    void (*close)(int, int);
    int  (*show_version)(int);
    int  (*log_ttyin)(const char*, unsigned int, const char**);
    int  (*log_ttyout)(const char*, unsigned int, const char**);
    int  (*log_stdin)(const char*, unsigned int, const char**);
    int  (*log_stdout)(const char*, unsigned int, const char**);
    int  (*log_stderr)(const char*, unsigned int, const char**);
    void (*register_hooks)(int, int(*)(void*));
    void (*deregister_hooks)(int, int(*)(void*));
    int  (*change_winsize)(unsigned int, unsigned int, const char**);
    int  (*log_suspend)(int, const char**);
    void* event_alloc;
};


constexpr auto LOG_PATH = "/var/log/sudo_monitor.log"sv;

// Environment variables worth logging (security-relevant ones)
constexpr std::array WATCHED_ENV = {
    "PATH"sv, "HOME"sv, "SHELL"sv, "USER"sv,"SUDO_USER"sv,
	"SUDO_UID"sv, "SUDO_GID"sv, "SUDO_COMMAND"sv,
    "LD_PRELOAD"sv, "LD_LIBRARY_PATH"sv
};

/*
    Output handler - sends everything to both console and LOG_PATH log file.
    Uses RAII concept.
 */
 
class Output {
    std::ofstream file_;
    PrintFunc print_ = nullptr;

public:
    void setup(PrintFunc pf) {
        print_ = pf;
        file_.open(std::string{LOG_PATH}, std::ios::app);
    }

    
    void log(std::string_view msg) {
        if (print_) print_(MSG_INFO, "%s", msg.data());
        if (file_) { file_ << msg; file_.flush(); }
    }

	// Self-note - std::format C++20
    // Convenience for formatted output
    template<typename... Args>
    void logf(std::format_string<Args...> fmt, Args&&... args) {
        log(std::format(fmt, std::forward<Args>(args)...));
    }

    void done() { if (file_.is_open()) file_.close(); }
    ~Output() { done(); }
};

static Output out;

// Get current time as a string
auto timestamp() -> std::string {
    auto now = std::time(nullptr);
    char buf[32];
    std::strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", std::localtime(&now));
    return buf;
}

// Extract value from sudo's "key=value" string arrays.
auto get_val(char* const arr[], std::string_view key) -> std::optional<std::string> {
    if (!arr) return std::nullopt;

    for (int i = 0; arr[i]; ++i) {
        std::string_view entry{arr[i]};
        // Self-note - starts_with C++20
        if (entry.starts_with(key) && entry.size() > key.size() && entry[key.size()] == '=') {
            return std::string{entry.substr(key.size() + 1)};
        }
    }
    return std::nullopt;
}

auto get_val_or(char* const arr[], std::string_view key, std::string_view def) -> std::string {
    return get_val(arr, key).value_or(std::string{def});
}

// Binary file information - size, permissions, owner, etc.
struct BinInfo {
    bool ok = false;
    size_t size = 0;
    unsigned mode = 0;
    std::string owner, group, mtime;
    bool suid = false, sgid = false;
};

auto inspect_binary(const fs::path& path) -> BinInfo {
    struct stat st;
    if (stat(path.c_str(), &st) != 0) return {};

    BinInfo info {
        .ok = true,
        .size = static_cast<size_t>(st.st_size),
        .mode = static_cast<unsigned>(st.st_mode & 07777),
        .owner = {},
        .group = {},
        .mtime = {},
        .suid = (st.st_mode & S_ISUID) != 0,
        .sgid = (st.st_mode & S_ISGID) != 0
    };

    // Get owner/group names
    if (auto* p = getpwuid(st.st_uid)) info.owner = p->pw_name;
    else info.owner = std::to_string(st.st_uid);

    if (auto* g = getgrgid(st.st_gid)) info.group = g->gr_name;
    else info.group = std::to_string(st.st_gid);

    char tbuf[32];
    std::strftime(tbuf, sizeof(tbuf), "%Y-%m-%d %H:%M:%S", std::localtime(&st.st_mtime));
    info.mtime = tbuf;

    return info;
}

// Child process information

struct ChildInfo {
    pid_t pid = 0;
    std::string name;
    std::string cmdline;
    std::string state;
    uid_t uid = 0;
    gid_t gid = 0;
    unsigned long vmsize = 0;
};

// Global state for tracking children during execution
static std::vector<ChildInfo> g_discovered_children;
static pid_t g_our_pid = 0;

// Parse number from string - returns empty optional on failure
template<typename T>
auto parse_num(std::string_view s) -> std::optional<T> {
    T val{};
    auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), val);
    if (ec == std::errc{} && ptr == s.data() + s.size())
        return val;
    return std::nullopt;
}

// Parse /proc/PID/status file to get process details.

auto parse_proc_status(const fs::path& status_path, pid_t& ppid_out) -> ChildInfo {
    ChildInfo ci;
    std::ifstream f{status_path};
    if (!f) return ci;

    std::string line;
    while (std::getline(f, line)) {
        std::string_view lv{line};
        if (lv.starts_with("Name:")) {
            auto val = lv.substr(6);
            while (!val.empty() && (val[0] == ' ' || val[0] == '\t')) val.remove_prefix(1);
            ci.name = std::string{val};
        }
        else if (lv.starts_with("State:")) {
            auto val = lv.substr(7);
            while (!val.empty() && (val[0] == ' ' || val[0] == '\t')) val.remove_prefix(1);
            ci.state = val.empty() ? "?" : std::string{val.substr(0, 1)};
        }
        else if (lv.starts_with("PPid:")) {
            auto val = lv.substr(5);
            while (!val.empty() && (val[0] == ' ' || val[0] == '\t')) val.remove_prefix(1);
            if (auto p = parse_num<pid_t>(val)) ppid_out = *p;
        }
        else if (lv.starts_with("Uid:")) {
            auto val = lv.substr(4);
            while (!val.empty() && (val[0] == ' ' || val[0] == '\t')) val.remove_prefix(1);
            auto end = val.find('\t');
            if (auto u = parse_num<uid_t>(val.substr(0, end))) ci.uid = *u;
        }
        else if (lv.starts_with("Gid:")) {
            auto val = lv.substr(4);
            while (!val.empty() && (val[0] == ' ' || val[0] == '\t')) val.remove_prefix(1);
            auto end = val.find('\t');
            if (auto g = parse_num<gid_t>(val.substr(0, end))) ci.gid = *g;
        }
        else if (lv.starts_with("VmSize:")) {
            auto val = lv.substr(7);
            while (!val.empty() && (val[0] == ' ' || val[0] == '\t')) val.remove_prefix(1);
            auto end = val.find(' ');
            if (auto v = parse_num<unsigned long>(val.substr(0, end))) ci.vmsize = *v;
        }
    }
    return ci;
}

// Read full command line from /proc/PID/cmdline

auto read_cmdline(const fs::path& path) -> std::string {
    std::ifstream f{path};
    if (!f) return {};

    std::ostringstream oss;
    std::string part;
    bool first = true;
    while (std::getline(f, part, '\0')) {
        if (part.empty()) break;
        if (!first) oss << ' ';
        oss << part;
        first = false;
    }
    return oss.str();
}

// Find all descendant processes

auto find_descendants(pid_t ancestor) -> std::vector<ChildInfo> {
    std::vector<ChildInfo> all;
    std::vector<pid_t> to_check = {ancestor};
    std::error_code ec;

    while (!to_check.empty()) {
        std::vector<pid_t> next_level;

        for (const auto& entry : fs::directory_iterator("/proc", ec)) {
            if (ec || !entry.is_directory()) continue;

            auto dirname = entry.path().filename().string();
            auto maybe_pid = parse_num<pid_t>(dirname);
            if (!maybe_pid) continue;

            pid_t this_pid = *maybe_pid;
            pid_t ppid = 0;

            auto ci = parse_proc_status(entry.path() / "status", ppid);

            // Check if ppid is in our list
			// Self-note - ranges::find C++20
            if (std::ranges::find(to_check, ppid) == to_check.end()) continue;

            ci.pid = this_pid;
            ci.cmdline = read_cmdline(entry.path() / "cmdline");
            if (ci.cmdline.empty()) ci.cmdline = "(exited)";

            all.push_back(std::move(ci));
            next_level.push_back(this_pid);
        }

        to_check = std::move(next_level);
    }

    return all;
}

// Design output

void line()  { out.log("──────────────────────────────────────────────────\n"); }
void dline() { out.log("══════════════════════════════════════════════════\n"); }
void header() {
    out.log("\n┌────────────────────────────────────────────────┐\n");
    out.log("│           SUDO COMMAND INTERCEPTED             │\n");
    out.log("└────────────────────────────────────────────────┘\n");
}

// Check if an environment variable is in our watch list.

bool is_watched_env(std::string_view entry) {
	// Self-note - ranges::find C++20
    return std::ranges::any_of(WATCHED_ENV, [&](auto& var) {
        return entry.starts_with(var) && entry.size() > var.size() && entry[var.size()] == '=';
    });
}

// Plugin Callbacks 
// Sudo defines the function signature - we must match it exactly
// These are the parameters sudo passes to the plugin
// If our function doesn't match, it crashes or reads garbage memory

static int on_open(
    [[maybe_unused]] unsigned int ver,
    [[maybe_unused]] void* conv,
    PrintFunc print,
    char* const settings[],
    char* const user_info[],
    char* const cmd_info[],
    int argc,
    char* const argv[],
    char* const env[],
    [[maybe_unused]] char* const opts[],
    [[maybe_unused]] const char** errstr)
{
    out.setup(print);
    
    // Save our PID for child scanning during execution
    g_our_pid = getpid();
    g_discovered_children.clear();

    // Gather all the info we need
    auto user  = get_val_or(user_info, "user", "?");
    auto uid   = get_val_or(user_info, "uid", "?");
    auto gid   = get_val_or(user_info, "gid", "?");
    auto host  = get_val_or(user_info, "host", "?");
    auto tty   = get_val_or(user_info, "tty", "?");
    auto cwd   = get_val_or(user_info, "cwd", "?");
    auto runas = get_val_or(settings, "runas_user", "root");
    auto cmd   = get_val_or(cmd_info, "command", "");

    header();
	
	// Self-note - std::format C++20
    out.logf("Timestamp: {}\n", timestamp());

    line();
    out.log("INVOKING USER\n");
    out.logf("  Name:      {}\n", user);
    out.logf("  UID/GID:   {}/{}\n", uid, gid);
    out.logf("  Host:      {}\n", host);
    out.logf("  TTY:       {}\n", tty);
    out.logf("  Directory: {}\n", cwd);
    out.logf("  Run as:    {}\n", runas);

    line();
    out.log("COMMAND\n");
    out.logf("  Path: {}\n", cmd);

    // Build full command line
    std::ostringstream full_cmd;
    for (int i = 0; i < argc && argv[i]; ++i) {
        if (i) full_cmd << ' ';
        full_cmd << argv[i];
    }
    out.logf("  Full: {}\n", full_cmd.str());
    out.logf("  Argc: {}\n", argc);

    // Binary details
    if (!cmd.empty()) {
        line();
        out.log("BINARY DETAILS\n");
        auto bi = inspect_binary(cmd);
        if (bi.ok) {
            out.logf("  Size:     {} bytes\n", bi.size);
            char mode_buf[8];
            std::snprintf(mode_buf, sizeof(mode_buf), "%04o", bi.mode);
            out.logf("  Mode:     {}\n", mode_buf);
            out.logf("  Owner:    {}\n", bi.owner);
            out.logf("  Group:    {}\n", bi.group);
            out.logf("  Modified: {}\n", bi.mtime);
            if (bi.suid) out.log("  *** SETUID ***\n");
            if (bi.sgid) out.log("  *** SETGID ***\n");
        } else {
            out.log("  (could not stat binary)\n");
        }
    }

    line();
    out.log("PROCESS\n");
    out.logf("  PID:  {}\n", getpid());
    out.logf("  PPID: {}\n", getppid());
    out.logf("  UID:  real={} eff={}\n", getuid(), geteuid());
    out.logf("  GID:  real={} eff={}\n", getgid(), getegid());

    line();
    out.log("ENVIRONMENT (security-relevant)\n");
    if (env) {
        for (int i = 0; env[i]; ++i) {
            if (is_watched_env(env[i])) {
                out.logf("  {}\n", env[i]);
            }
        }
    }

    dline();
    out.log(">>> COMMAND EXECUTING >>>\n\n");
	
	// allow command
    return 1;  
}

static void on_close(int status, int error) {
    out.log("\n<<< COMMAND COMPLETED <<<\n");

    line();
    out.log("RESULT\n");
    out.logf("  Exit code: {}\n", status);
    if (error) {
        out.logf("  Error:     {} (errno {})\n", std::strerror(error), error);
    }
    out.logf("  Time:      {}\n", timestamp());

    line();
    out.log("CHILD PROCESSES\n");

    // Final scan to catch anything still running
    auto final_scan = find_descendants(g_our_pid);
    for (auto& child : final_scan) {
        bool already_seen = std::ranges::any_of(g_discovered_children,
            [&](const ChildInfo& c) { return c.pid == child.pid; });
        if (!already_seen && child.pid != g_our_pid) {
            g_discovered_children.push_back(std::move(child));
        }
    }

    if (g_discovered_children.empty()) {
        out.log("  (none detected)\n");
    } else {
        for (const auto& c : g_discovered_children) {
            out.log("  ─────\n");
            out.logf("  PID:     {}\n", c.pid);
            out.logf("  Name:    {}\n", c.name.empty() ? "?" : c.name);
            out.logf("  Command: {}\n", c.cmdline);
            out.logf("  State:   {}\n", c.state);
            out.logf("  UID/GID: {}/{}\n", c.uid, c.gid);
            if (c.vmsize > 0) {
                out.logf("  VMSize:  {} kB\n", c.vmsize);
            }
        }
        out.log("  ─────\n");
        out.logf("  Total: {} child(ren)\n", g_discovered_children.size());
    }

    dline();
    out.log("\n");
    out.done();
}

static int on_version(int verbose) {
    out.log("sudo_monitor v1.0 [C++20]\n");
    if (verbose) {
        out.logf("  Log: {}\n", LOG_PATH);
    }
    return 1;
}

static int io_log([[maybe_unused]] const char* buf,
                  [[maybe_unused]] unsigned int len,
                  [[maybe_unused]] const char** errstr) {
    
    if (g_our_pid == 0) return 1;
    
    // Scan for new children
    auto current = find_descendants(g_our_pid);
    
    // Add any new ones we haven't seen
    for (auto& child : current) {
        bool already_seen = std::ranges::any_of(g_discovered_children, 
            [&](const ChildInfo& c) { return c.pid == child.pid; });
        
        if (!already_seen && child.pid != g_our_pid) {
            g_discovered_children.push_back(std::move(child));
        }
    }
    
    return 1;
}

// Plugin export - name must match /etc/sudo.conf entry
// It's how sudo finds and uses our plugin
// Plugin sudo_monitor sudo_monitor.so

extern "C" {
    __attribute__((visibility("default")))
    io_plugin sudo_monitor = {
        SUDO_IO_PLUGIN_TYPE, SUDO_API_VER,
        on_open, on_close, on_version,
        io_log, io_log,                     // ttyin, ttyout - scan for children here
        nullptr, io_log, io_log,            // stdin, stdout, stderr
        nullptr, nullptr, nullptr, nullptr,
        nullptr
    };
}
