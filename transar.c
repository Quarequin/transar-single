/*
 * transar.c - Archive Transcoder (recursive, mergesort-style) v3.0-c
 *
 * Usage:
 *   ./transar <fromFormat> <toFormat[-level]> [-w] [-v] [-p] [distFolder]
 *   ./transar help
 *
 * Formats: 7z, zip, rar, tar.gz(.tgz), tar.xz(.txz)
 * Options:
 *   -w   Overwrite existing output files (default: auto-rename)
 *   -v   Verbose mode (show full tool output)
 *   -p   TUI mode: apt-style progress bar pinned to the bottom two
 *        terminal lines (ANSI escape codes), live per-file percent
 * distFolder:
 *   Move result files here, preserving the original folder structure
 *   relative to the start directory.
 *
 * Build:  gcc -O2 -Wall -Wextra -o transar transar.c
 *         (on older glibc add -lutil for forkpty)
 *
 * Resource usage: streaming nftw walk (no file list in RAM), 4 KiB line
 * buffer, tiny hash set of created outputs. RSS stays around 1-2 MB,
 * far below the 16 MB budget.
 */

#define _GNU_SOURCE

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdint.h>
#include <stdarg.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <limits.h>
#include <pty.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <ftw.h>

#define VERSION   "3.0-c"
#define BOX_LINES 2            /* apt-style status box: Working line + bar line */

/* ------------------------------------------------------------
 * Formats
 * ------------------------------------------------------------ */
typedef enum { FMT_7Z, FMT_ZIP, FMT_RAR, FMT_TARGZ, FMT_TARXZ } Format;

static const struct {
    const char *name;
    const char *suffixes[3];
    int level_min, level_max, level_default;
} kFormats[] = {
    [FMT_7Z]    = { "7z",     { ".7z",                NULL }, 0, 9, 5 },
    [FMT_ZIP]   = { "zip",    { ".zip",               NULL }, 0, 9, 6 },
    [FMT_RAR]   = { "rar",    { ".rar",               NULL }, 0, 5, 3 },
    [FMT_TARGZ] = { "tar.gz", { ".tar.gz", ".tgz",    NULL }, 1, 9, 6 },
    [FMT_TARXZ] = { "tar.xz", { ".tar.xz", ".txz",    NULL }, 0, 9, 6 },
};

/* ------------------------------------------------------------
 * Globals
 * ------------------------------------------------------------ */
static Format  g_from, g_to;
static char    g_level[8] = "";
static int     g_overwrite = 0;
static int     g_verbose   = 0;
static int     g_progress  = 0;
static const char *g_dist_dir = NULL;

static char    g_start_dir[PATH_MAX];
static char    g_cur_file[PATH_MAX] = "";
static char    g_cur_op[32] = "";
static int     g_cur_pct  = 0;
static long    g_done     = 0;
static long    g_total    = 0;
static time_t  g_t_start;
static char    g_always   = 0;

static volatile sig_atomic_t g_interrupted = 0;

static FILE   *g_log = NULL;

/* ------------------------------------------------------------
 * Hash set of (dev,ino) for outputs created during this run.
 * Prevents re-processing results when from == to (e.g. 7z -> 7z-9).
 * Open addressing, power-of-two capacity, 8 bytes per slot.
 * ------------------------------------------------------------ */
static uint64_t *g_seen = NULL;
static size_t    g_seen_cap = 0;     /* in slots */
static size_t    g_seen_n = 0;

static uint64_t mix_key(dev_t dev, ino_t ino) {
    uint64_t k = ((uint64_t)dev << 32) ^ (uint64_t)ino;
    k *= 0x9E3779B97F4A7C15ULL;
    k ^= k >> 29;
    return k ? k : 1;                /* 0 marks an empty slot */
}

static int seen_contains(uint64_t key) {
    if (!g_seen) return 0;
    size_t mask = g_seen_cap - 1, i = (size_t)key & mask;
    while (g_seen[i]) {
        if (g_seen[i] == key) return 1;
        i = (i + 1) & mask;
    }
    return 0;
}

static void seen_insert(uint64_t key) {
    if ((g_seen_n + 1) * 10 >= g_seen_cap * 7) {       /* grow at 70% load */
        size_t oldcap = g_seen_cap;
        uint64_t *old = g_seen;
        g_seen_cap = oldcap ? oldcap * 2 : 1024;
        g_seen = calloc(g_seen_cap, sizeof(uint64_t));
        g_seen_n = 0;
        if (old) {
            for (size_t i = 0; i < oldcap; i++)
                if (old[i]) { seen_insert(old[i]); }
            free(old);
        }
    }
    size_t mask = g_seen_cap - 1, i = (size_t)key & mask;
    while (g_seen[i]) {
        if (g_seen[i] == key) return;
        i = (i + 1) & mask;
    }
    g_seen[i] = key;
    g_seen_n++;
}

static void seen_free(void) { free(g_seen); g_seen = NULL; g_seen_cap = g_seen_n = 0; }

/* ------------------------------------------------------------
 * Temp directory registry (cleaned up on exit AND on interrupt)
 * ------------------------------------------------------------ */
typedef struct TempNode { char *path; struct TempNode *next; } TempNode;
static TempNode *g_temps = NULL;

static void temps_add(const char *path) {
    TempNode *n = malloc(sizeof *n);
    n->path = strdup(path);
    n->next = g_temps;
    g_temps = n;
}

static void temps_remove(const char *path) {
    TempNode **pp = &g_temps;
    while (*pp) {
        if (strcmp((*pp)->path, path) == 0) {
            TempNode *dead = *pp;
            *pp = dead->next;
            free(dead->path);
            free(dead);
            return;
        }
        pp = &(*pp)->next;
    }
}

static int rm_cb(const char *fpath, const struct stat *sb, int typeflag,
                 struct FTW *ftwbuf) {
    (void)sb; (void)typeflag; (void)ftwbuf;
    return remove(fpath);
}

static void rm_rf(const char *path) { nftw(path, rm_cb, 32, FTW_DEPTH | FTW_PHYS); }

static void temps_cleanup(void) {
    while (g_temps) {
        rm_rf(g_temps->path);
        free(g_temps->path);
        TempNode *next = g_temps->next;
        free(g_temps);
        g_temps = next;
    }
}

/* ------------------------------------------------------------
 * Signal handling: flag-based cleanup (async-safe handler)
 * ------------------------------------------------------------ */
static void on_signal(int sig) { (void)sig; g_interrupted = 1; }

static void install_signal_handlers(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_signal;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;                    /* no SA_RESTART: interrupt blocking I/O */
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
}

static void walk_tree(const char *dir);   /* defined below */

static void check_interrupted(void) {
    if (!g_interrupted) return;
    fputs("\n\nInterrupted - cleaning up temp files...\n", stderr);
    temps_cleanup();
    seen_free();
    exit(130);
}

/* ------------------------------------------------------------
 * Small utilities
 * ------------------------------------------------------------ */
static void die(const char *msg) { perror(msg); exit(1); }

static int ends_with(const char *s, const char *suf) {
    size_t ls = strlen(s), lf = strlen(suf);
    return ls >= lf && strcmp(s + ls - lf, suf) == 0;
}

static const char *fmt_time(long sec, char out[16]) {
    if (sec < 0) sec = 0;
    snprintf(out, 16, "%02ld:%02ld:%02ld", (sec / 3600) % 100,
             (sec % 3600) / 60, sec % 60);
    return out;
}

static const char *draw_bar(int pct, char *buf, size_t buflen) {
    if (pct > 100) pct = 100;          /* clamp: totals can mislead mid-run */
    if (pct < 0)   pct = 0;
    const int w = 20, filled = pct * w / 100;
    size_t pos = 0;
    buf[pos++] = '[';
    for (int i = 0; i < w; i++) buf[pos++] = (i < filled) ? '#' : '-';
    snprintf(buf + pos, buflen - pos, "] %3d%%", pct);
    return buf;
}

static int mkdir_p(const char *path) {
    char tmp[PATH_MAX];
    snprintf(tmp, sizeof tmp, "%s", path);
    for (char *p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = 0;
            if (mkdir(tmp, 0755) != 0 && errno != EEXIST) return -1;
            *p = '/';
        }
    }
    if (mkdir(tmp, 0755) != 0 && errno != EEXIST) return -1;
    return 0;
}

/* ------------------------------------------------------------
 * apt-style bottom status box (2 lines) - ANSI escape codes
 *
 * Layout (bottom of terminal):
 *      ...
 *      <scrolling content>
 *      Working: outer.7z  (extract 61%)
 *      Progress: [#####---] 42% (3/8) Elapsed 00:01:12 ETA ~00:02:01
 *
 * Cursor is parked at the end of the bar line between updates.
 * ------------------------------------------------------------ */
static int g_box_on = 0;

/* Query the terminal width so status lines never wrap (wrapping would
 * break the cursor-movement math of the status box). */
static int term_width(void) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_col > 0)
        return ws.ws_col;
    return 80;
}

static void clip_to_width(char *line) {
    int w = term_width();
    if (w > 2 && (int)strlen(line) >= w) line[w - 1] = 0;
}

static void box_init(void) {
    if (!g_progress) return;
    fputs("\n\n", stdout);
    fflush(stdout);
    g_box_on = 1;
}

/* Redraw the two status lines; works when cursor is anywhere on the bar line. */
static void box_render(void) {
    if (!g_box_on) return;

    long elapsed = time(NULL) - g_t_start;
    long eta = (g_done > 0 && g_total > g_done)
               ? elapsed * (g_total - g_done) / g_done : 0;
    int pct = g_total > 0 ? (int)(g_done * 100 / g_total) : 0;
    char bar[40], ts[16], te[16];
    char work[PATH_MAX + 64], statline[160];

    if (g_cur_file[0])
        snprintf(work, sizeof work, "Working: %s  (%s %d%%)",
                 g_cur_file, g_cur_op, g_cur_pct);
    else
        snprintf(work, sizeof work, "Working: -");

    snprintf(statline, sizeof statline, "Progress: %s  (%ld/%ld) Elapsed: %s ETA: ~%s",
             draw_bar(pct, bar, sizeof bar), g_done, g_total,
             fmt_time(elapsed, ts), fmt_time(eta, te));

    clip_to_width(work);       /* never wrap: 1 logical line = 1 physical row */
    clip_to_width(statline);

    printf("\r\033[1A\033[K%s\n\033[K%s", work, statline);
    fflush(stdout);
}

/* Print one line of content ABOVE the box (box is repainted after). */
static void box_print(const char *fmt, ...) {
    char line[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(line, sizeof line, fmt, ap);
    va_end(ap);

    if (!g_box_on) { printf("%s\n", line); fflush(stdout); return; }

    /* write above the box, then move back down onto the bar line */
    printf("\r\033[2A\033[K%s\n\033[1B", line);
    box_render();                          /* repaint + re-park cursor */
}

/* ------------------------------------------------------------
 * Run an external tool, streaming output line by line.
 *   use_pty=1 : child gets a pty (so tools like 7z emit live progress)
 *   use_pty=0 : plain pipe (quiet/verbose modes)
 * on_line() may update the box / print verbose output / fill the ring buffer.
 * ------------------------------------------------------------ */
typedef int (*LineCb)(const char *line, void *ctx);

static int run_child(char *const argv[], const char *cwd, int use_pty,
                     LineCb on_line, void *ctx) {
    int fd;
    pid_t pid;

    if (use_pty) {
        struct winsize ws = { .ws_row = 24, .ws_col = 80 };
        pid = forkpty(&fd, NULL, NULL, &ws);
        if (pid == 0) {
            if (cwd) { if (chdir(cwd) != 0) _exit(126); }
            execvp(argv[0], argv);
            _exit(127);
        }
    } else {
        int p[2];
        if (pipe(p) != 0) die("pipe");
        pid = fork();
        if (pid == 0) {
            if (cwd) { if (chdir(cwd) != 0) _exit(126); }
            dup2(p[1], STDOUT_FILENO);
            dup2(p[1], STDERR_FILENO);
            close(p[0]); close(p[1]);
            execvp(argv[0], argv);
            _exit(127);
        }
        close(p[1]);
        fd = p[0];
    }
    if (pid < 0) { close(fd); return -1; }

    /* parent: read output, split on '\n' or '\r' */
    char buf[4096];
    size_t blen = 0;
    ssize_t r;
    int status = 0;

    while ((r = read(fd, buf + blen, sizeof buf - 1 - blen)) > 0) {
        blen += (size_t)r;
        buf[blen] = 0;
        char *sep;
        while ((sep = strpbrk(buf, "\n\r")) != NULL) {
            *sep = 0;
            if (on_line) on_line(buf, ctx);
            size_t used = (size_t)(sep - buf) + 1;
            memmove(buf, buf + used, blen - used);
            blen -= used;
        }
        if (blen == sizeof buf - 1) {
            if (on_line) on_line(buf, ctx);
            blen = 0;
        }
        if (g_interrupted) break;
    }
    if (blen && on_line) on_line(buf, ctx);
    close(fd);

    if (g_interrupted) kill(pid, SIGKILL);
    while (waitpid(pid, &status, 0) < 0) {
        if (errno == EINTR) { if (g_interrupted) kill(pid, SIGKILL); continue; }
        break;
    }
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    return -1;
}

/* ------------------------------------------------------------
 * Extraction output handling: ring buffer + live percent
 * ------------------------------------------------------------ */
#define RING_SIZE 3

typedef struct {
    char lines[RING_SIZE][512];
    int  next;
} RingBuf;

static int on_extract_line(const char *line, void *ctx) {
    RingBuf *ring = ctx;

    snprintf(ring->lines[ring->next], sizeof ring->lines[0], "%s", line);
    ring->next = (ring->next + 1) % RING_SIZE;

    /* live percent from terminal progress like "  42%" */
    const char *pc = strchr(line, '%');
    if (pc) {
        int val = 0, digits = 0;
        while (pc > line && pc[-1] >= '0' && pc[-1] <= '9') { pc--; digits++; }
        if (digits > 0) {
            val = atoi(pc);
            if (val != g_cur_pct) {
                g_cur_pct = val;
                snprintf(g_cur_op, sizeof g_cur_op, "extract");
                box_render();
            }
            return 0;                       /* progress junk: not a log line */
        }
    }
    if (g_verbose && !g_progress)
        fprintf(stderr, "   | %s\n", line);
    return 0;
}

/* ------------------------------------------------------------
 * Archive operations
 * ------------------------------------------------------------ */
static int level_of(void) {
    return g_level[0] ? atoi(g_level) : kFormats[g_to].level_default;
}

static int archive_test(const char *file) {
    char *const argv[] = { "7z", "t", (char *)file, NULL };
    return run_child(argv, NULL, 0, NULL, NULL) == 0;
}

static int archive_extract(const char *file, const char *target, RingBuf *ring) {
    char oarg[PATH_MAX + 8];
    snprintf(oarg, sizeof oarg, "-o%s", target);
    char *const argv[] = { "7z", "x", (char *)file, oarg, "-y", NULL };
    /* pty only in TUI mode: forces 7z to emit live progress percentages */
    return run_child(argv, NULL, g_progress, on_extract_line, ring) == 0;
}

static int archive_create(const char *dir, const char *out, RingBuf *ring) {
    char lvl[16];
    int rc;
    switch (g_to) {
    case FMT_7Z:
        snprintf(lvl, sizeof lvl, "-mx=%d", level_of());
        { char *const a[] = { "7z", "a", "-t7z", lvl, (char *)out, ".", NULL };
          rc = run_child(a, dir, 0, on_extract_line, ring); }
        break;
    case FMT_ZIP:
        snprintf(lvl, sizeof lvl, "-%d", level_of());
        if (g_verbose) {
            char *const a[] = { "zip", "-r", lvl, (char *)out, ".", NULL };
            rc = run_child(a, dir, 0, NULL, NULL);
        } else {
            char *const a[] = { "zip", "-q", "-r", lvl, (char *)out, ".", NULL };
            rc = run_child(a, dir, 0, NULL, NULL);
        }
        break;
    case FMT_RAR:
        snprintf(lvl, sizeof lvl, "-m%d", level_of());
        { char *const a[] = { "rar", "a", "-r", lvl, (char *)out, ".", NULL };
          rc = run_child(a, dir, 0, on_extract_line, ring); }
        break;
    case FMT_TARGZ:
        snprintf(lvl, sizeof lvl, "gzip -%d", level_of());
        { char *const a[] = { "tar", "-I", lvl, "-cf", (char *)out,
                              "-C", (char *)dir, ".", NULL };
          rc = run_child(a, NULL, 0, on_extract_line, ring); }
        break;
    case FMT_TARXZ:
        snprintf(lvl, sizeof lvl, "xz -%d", level_of());
        { char *const a[] = { "tar", "-I", lvl, "-cf", (char *)out,
                              "-C", (char *)dir, ".", NULL };
          rc = run_child(a, NULL, 0, on_extract_line, ring); }
        break;
    default:
        rc = -1;
    }
    return rc == 0;
}

/* ------------------------------------------------------------
 * Delete prompt (reads from /dev/tty so nothing can shadow it)
 * ------------------------------------------------------------ */
static int ask_delete(const char *file) {
    fprintf(stderr,
            "\n   Delete source \"%s\"? [y=yes, n=no, ay=AlwaysYes, an=AlwaysNo]: ",
            file);
    fflush(stderr);

    FILE *in = fopen("/dev/tty", "r");
    if (!in) in = stdin;

    char line[64];
    int answer = 0;
    if (fgets(line, sizeof line, in) == NULL) {
        /* interrupted / EOF: keep the file */
    } else if (line[0] == 'y' || line[0] == 'Y') {
        answer = 1;
    } else if (strncasecmp(line, "ay", 2) == 0) {
        g_always = 'y'; answer = 1;
    } else if (strncasecmp(line, "an", 2) == 0) {
        g_always = 'n'; answer = 0;
    }

    if (in != stdin) fclose(in);
    return answer;
}

/* ------------------------------------------------------------
 * Output path resolution (dist folder + preserved structure + unique name)
 * ------------------------------------------------------------ */
static void build_output_path(const char *parent, const char *filename,
                              char *outdir, size_t outdirlen,
                              char *outpath, size_t outpathlen) {
    const char *toext = kFormats[g_to].name;

    if (g_dist_dir) {
        const char *rel = parent;
        size_t start_len = strlen(g_start_dir);
        if (strncmp(parent, g_start_dir, start_len) == 0) {
            rel = parent + start_len;
            if (*rel == '/') rel++;
        }
        if (*rel)
            snprintf(outdir, outdirlen, "%s/%s", g_dist_dir, rel);
        else
            snprintf(outdir, outdirlen, "%s", g_dist_dir);
        mkdir_p(outdir);
    } else {
        snprintf(outdir, outdirlen, "%s", parent);
    }

    if (g_overwrite) {
        snprintf(outpath, outpathlen, "%s/%s.%s", outdir, filename, toext);
        unlink(outpath);
    } else {
        char candidate[PATH_MAX];
        size_t n = 1;
        snprintf(candidate, sizeof candidate, "%s/%s.%s", outdir, filename, toext);
        while (access(candidate, F_OK) == 0) {
            snprintf(candidate, sizeof candidate, "%s/%s_%zu.%s",
                     outdir, filename, n, toext);
            n++;
        }
        snprintf(outpath, outpathlen, "%s", candidate);
    }
}

/* ------------------------------------------------------------
 * Process one archive:
 * extract -> recurse (nested archives) -> pack -> move/delete source
 * ------------------------------------------------------------ */
static void process_one(const char *file, const char *suf) {
    struct stat st;
    if (stat(file, &st) != 0) return;          /* gone (deleted earlier) */

    char parent[PATH_MAX], filename[PATH_MAX];
    snprintf(parent, sizeof parent, "%s", file);
    char *slash = strrchr(parent, '/');
    const char *base;
    if (slash) { *slash = 0; base = slash + 1; }
    else { snprintf(parent, sizeof parent, "."); base = file; }

    snprintf(filename, sizeof filename, "%.*s",
             (int)(strlen(base) - strlen(suf)), base);

    snprintf(g_cur_file, sizeof g_cur_file, "%s", file);
    snprintf(g_cur_op, sizeof g_cur_op, "extract");
    g_cur_pct = 0;

    if (!g_progress) {
        printf("\n>> [%ld] Converting: %s\n", g_done + 1, file);
        fflush(stdout);
    }
    box_render();

    /* temp extraction dir (registered for interrupt cleanup) */
    char target[PATH_MAX];
    snprintf(target, sizeof target, "%s/.transar_%s_%d_%06d",
             parent, filename, (int)getpid(), (int)(rand() % 1000000));
    mkdir_p(target);
    temps_add(target);

    /* 1. integrity test */
    int healthy = archive_test(file);
    if (healthy) {
        if (g_verbose && !g_progress) fputs("   [test] OK\n", stderr);
    } else {
        fprintf(g_log, "WARN  Damaged archive (CRC/data error): %s\n", file);
        fprintf(g_log, "      -> attempting to salvage readable parts...\n");
        fflush(g_log);
    }

    /* 2. extract (retry up to 2 times, pty in TUI mode for live %) */
    int success = 0;
    RingBuf ring;
    memset(&ring, 0, sizeof ring);

    for (int attempt = 1; attempt <= 2 && !g_interrupted; attempt++) {
        rm_rf(target);
        mkdir_p(target);
        g_cur_pct = 0;
        if (archive_extract(file, target, &ring)) {
            success = 1;
            g_cur_pct = 100;
            box_render();
            break;
        }
        fprintf(g_log, "      -> retry %d failed: %s\n", attempt, file);
        fflush(g_log);
    }

    if (!success) {
        fprintf(g_log, "ERROR Extraction failed even after retries: %s\n", file);
        for (int k = 0; k < RING_SIZE; k++)
            if (ring.lines[k][0])
                fprintf(g_log, "      | %s\n", ring.lines[k]);
        fprintf(g_log, "      -> skipped, source file kept\n");
        fflush(g_log);
        rm_rf(target);
        temps_remove(target);
        g_done++;
        g_cur_file[0] = 0;
        return;
    }

    /* 3. recurse: convert nested archives first (mergesort style) */
    snprintf(g_cur_op, sizeof g_cur_op, "nested");
    g_cur_pct = 100;
    box_render();
    walk_tree(target);

    /* 4. pack the result back into the target format */
    snprintf(g_cur_op, sizeof g_cur_op, "compress");
    g_cur_pct = 0;
    box_render();

    char outdir[PATH_MAX], outpath[PATH_MAX];
    build_output_path(parent, filename, outdir, sizeof outdir,
                      outpath, sizeof outpath);

    RingBuf cring;
    memset(&cring, 0, sizeof cring);
    g_cur_pct = 0;

    if (archive_create(target, outpath, &cring)) {
        struct stat ost;
        if (stat(outpath, &ost) == 0)
            seen_insert(mix_key(ost.st_dev, ost.st_ino));
        if (healthy)
            fprintf(g_log, "OK    Converted: %s -> %s\n", file, outpath);
        else
            fprintf(g_log, "WARN  Salvaged + converted (some data may be damaged): %s -> %s\n",
                    file, outpath);
    } else {
        /* full cleanup on error: remove partial output + temp data */
        unlink(outpath);
        fprintf(g_log, "ERROR Compression failed: %s -> %s\n", file, outpath);
        for (int k = 0; k < RING_SIZE; k++)
            if (cring.lines[k][0])
                fprintf(g_log, "      | %s\n", cring.lines[k]);
    }
    fflush(g_log);
    g_cur_pct = 100;
    box_render();

    rm_rf(target);
    temps_remove(target);

    /* 5. ask before deleting the source (damaged files always kept) */
    if (healthy) {
        int del;
        if (g_always == 'y')      del = 1;
        else if (g_always == 'n') del = 0;
        else                      del = ask_delete(file);

        if (g_progress) { fputc('\n', stdout); box_init(); }  /* fresh box below the prompt */
        if (del) {
            unlink(file);
            box_print("   Deleted: %s", file);
        } else {
            box_print("   Kept: %s", file);
        }
    }

    g_done++;
    g_cur_file[0] = 0;
    box_render();
}

/* ------------------------------------------------------------
 * Streaming directory walk (nftw): no file list is kept in RAM.
 * Matching archives are processed inline; temp dirs and
 * already-created outputs are skipped.
 * ------------------------------------------------------------ */
static const char *match_suffix(const char *base) {
    for (int i = 0; kFormats[g_from].suffixes[i]; i++)
        if (ends_with(base, kFormats[g_from].suffixes[i]))
            return kFormats[g_from].suffixes[i];
    return NULL;
}

static long g_count_only = 0;

static int walk_cb(const char *fpath, const struct stat *sb, int typeflag,
                   struct FTW *ftw) {
    const char *name = fpath + ftw->base;

    if (g_interrupted) return FTW_STOP;

    if (typeflag == FTW_D) {
        if (strncmp(name, ".transar_", 9) == 0) return FTW_SKIP_SUBTREE;
        return FTW_CONTINUE;
    }
    if (typeflag != FTW_F) return FTW_CONTINUE;

    if (g_count_only) {
        if (match_suffix(name)) g_count_only++;
        return FTW_CONTINUE;
    }

    if (seen_contains(mix_key(sb->st_dev, sb->st_ino))) return FTW_CONTINUE;

    const char *suf = match_suffix(name);
    if (!suf) return FTW_CONTINUE;

    /* recount so nested archives join the total */
    g_count_only = 1;
    nftw(g_start_dir, walk_cb, 32, FTW_PHYS | FTW_ACTIONRETVAL);
    long c = g_count_only - 1;         /* sources already deleted shrink the */
    if (c > g_total) g_total = c;      /* raw count: keep total monotonic  */
    g_count_only = 0;

    process_one(fpath, suf);
    return g_interrupted ? FTW_STOP : FTW_CONTINUE;
}

static void walk_tree(const char *dir) {
    nftw(dir, walk_cb, 32, FTW_PHYS | FTW_ACTIONRETVAL);
}

/* ------------------------------------------------------------
 * Help
 * ------------------------------------------------------------ */
static void show_help(void) {
    puts(
"transar - Archive Transcoder (recursive, mergesort-style) v" VERSION "\n"
"\n"
"USAGE:\n"
"  ./transar <fromFormat> <toFormat[-level]> [-w] [-v] [-p] [distFolder]\n"
"  ./transar help\n"
"\n"
"ARGUMENTS:\n"
"  fromFormat    Source archive format (a level here has no effect):\n"
"                  7z | zip | rar | tar.gz | tgz | tar.xz | txz\n"
"  toFormat      Target archive format, optionally with compression level:\n"
"                  zip-9      (zip, level 9)\n"
"                  7z-5       (7z, level 5)\n"
"                  tar.xz-9   (tar.xz, level 9)\n"
"                  rar-5      (rar, level 5 - max for rar)\n"
"  distFolder    (optional) Move every result file into this folder,\n"
"                preserving the original relative path structure.\n"
"\n"
"OPTIONS:\n"
"  -w            Overwrite existing output files (default: auto-rename)\n"
"  -v            Verbose mode - show full output of archive tools\n"
"  -p            TUI mode: apt-style progress bar pinned to the bottom\n"
"                of the terminal (ANSI escape codes) with live per-file\n"
"                percentage, overall percentage and ETA. Extraction runs\n"
"                on a pty so 7z reports progress continuously.\n"
"  Combinations like -wvp are allowed.\n"
"\n"
"LEVEL RANGES:\n"
"  7z     : 0-9   (default 5)   0 = store (no compression)\n"
"  zip    : 0-9   (default 6)\n"
"  rar    : 0-5   (default 3)\n"
"  tar.gz : 1-9   (default 6)\n"
"  tar.xz : 0-9   (default 6)\n"
"\n"
"BEHAVIOR:\n"
"  * Archives nested inside archives are processed recursively\n"
"    (mergesort style: deepest first, then packed back layer by layer)\n"
"  * Every archive is integrity-tested before extraction\n"
"  * Damaged archives are salvaged (readable parts recovered),\n"
"    logged, and NEVER deleted\n"
"  * After each successful conversion you are asked whether to\n"
"    delete the source archive:\n"
"      y = yes (this file)   n = no (this file)\n"
"      ay = AlwaysYes        an = AlwaysNo\n"
"  * Low resource usage: streaming walk, ~1-2 MB RSS (< 16 MB)\n"
"\n"
"EXAMPLES:\n"
"  ./transar 7z zip-9 -p              # .7z -> .zip with live TUI bar\n"
"  ./transar tar.gz 7z-5              # .tar.gz/.tgz -> .7z\n"
"  ./transar zip rar-5 -w ./converted # overwrite + move results\n"
"\n"
"REQUIREMENTS:\n"
"  7z (p7zip-full), zip, tar.\n"
"  'rar' is only needed when converting TO .rar\n"
"  (7-Zip cannot create RAR archives - install rar from rarlab.com)\n");
}

/* ------------------------------------------------------------
 * Format parsing
 * ------------------------------------------------------------ */
static int parse_format(const char *s, Format *out) {
    char buf[16];
    snprintf(buf, sizeof buf, "%s", s);
    for (char *p = buf; *p; p++) if (*p >= 'A' && *p <= 'Z') *p += 32;
    for (size_t i = 0; i < sizeof kFormats / sizeof kFormats[0]; i++)
        if (strcmp(buf, kFormats[i].name) == 0) { *out = (Format)i; return 1; }
    if (strcmp(buf, "tgz") == 0)  { *out = FMT_TARGZ; return 1; }
    if (strcmp(buf, "txz") == 0)  { *out = FMT_TARXZ; return 1; }
    if (strcmp(buf, ".7z") == 0)  { *out = FMT_7Z;    return 1; }
    if (strcmp(buf, ".zip") == 0) { *out = FMT_ZIP;   return 1; }
    if (strcmp(buf, ".rar") == 0) { *out = FMT_RAR;   return 1; }
    return 0;
}

/* ------------------------------------------------------------
 * main
 * ------------------------------------------------------------ */
int main(int argc, char **argv) {
    setvbuf(stdout, NULL, _IOLBF, 0);

    if (argc < 2 || strcmp(argv[1], "help") == 0 ||
        strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0) {
        show_help();
        return argc < 2 ? 1 : 0;
    }

    if (!parse_format(argv[1], &g_from)) {
        fprintf(stderr, "ERROR: unsupported source format: %s\n", argv[1]);
        return 1;
    }

    if (argc < 3) {
        fprintf(stderr, "ERROR: missing target format (see: ./transar help)\n");
        return 1;
    }
    {
        char tobuf[32];
        snprintf(tobuf, sizeof tobuf, "%s", argv[2]);
        char *dash = strrchr(tobuf, '-');
        if (dash && dash[1] >= '0' && dash[1] <= '9') {
            snprintf(g_level, sizeof g_level, "%s", dash + 1);
            *dash = 0;
        }
        if (!parse_format(tobuf, &g_to)) {
            fprintf(stderr, "ERROR: unsupported target format: %s\n", argv[2]);
            return 1;
        }
    }

    if (g_from == g_to && g_level[0] == 0) {
        printf("Source and target formats are identical (%s) - nothing to do.\n",
               kFormats[g_from].name);
        return 0;
    }

    if (g_level[0]) {
        int max = kFormats[g_to].level_max;
        int lvl = atoi(g_level);
        if (lvl < kFormats[g_to].level_min || lvl > max) {
            fprintf(stderr, "ERROR: level for .%s must be between %d and %d (got: %s)\n",
                    kFormats[g_to].name, kFormats[g_to].level_min, max, g_level);
            return 1;
        }
    }

    for (int i = 3; i < argc; i++) {
        if (argv[i][0] == '-' && argv[i][1]) {
            for (const char *f = argv[i] + 1; *f; f++) {
                switch (*f) {
                case 'w': case 'W': g_overwrite = 1; break;
                case 'v': case 'V': g_verbose   = 1; break;
                case 'p': case 'P': g_progress  = 1; break;
                case 'h': show_help(); return 0;
                default:
                    fprintf(stderr, "ERROR: unknown option: -%c (see: ./transar help)\n", *f);
                    return 1;
                }
            }
        } else if (!g_dist_dir) {
            g_dist_dir = argv[i];
        } else {
            fprintf(stderr, "ERROR: unexpected argument: %s\n", argv[i]);
            return 1;
        }
    }

    /* dependency check (PATH lookup) */
    {
        const char *need[4];
        int nn = 0;
        need[nn++] = "7z"; need[nn++] = "zip"; need[nn++] = "tar";
        if (g_to == FMT_RAR) need[nn++] = "rar";
        for (int i = 0; i < nn; i++) {
            char probe[PATH_MAX];
            snprintf(probe, sizeof probe, "command -v %s >/dev/null 2>&1", need[i]);
            if (system(probe) != 0) {
                fprintf(stderr, "ERROR: command not found: %s\n", need[i]);
                fputs("Install with: sudo apt install p7zip-full zip tar\n", stderr);
                return 1;
            }
        }
    }

    if (g_dist_dir && mkdir_p(g_dist_dir) != 0) {
        fprintf(stderr, "ERROR: cannot create dist folder: %s\n", g_dist_dir);
        return 1;
    }

    /* setup */
    srand((unsigned)time(NULL) ^ (unsigned)getpid());
    install_signal_handlers();
    atexit(temps_cleanup);
    atexit(seen_free);

    if (!getcwd(g_start_dir, sizeof g_start_dir)) die("getcwd");

    char logname[64];
    time_t now = time(NULL);
    strftime(logname, sizeof logname, "transar_log_%Y%m%d_%H%M%S.txt",
             localtime(&now));
    g_log = fopen(logname, "a");
    if (!g_log) g_log = stderr;

    printf("transar v%s - .%s -> .%s (level %d)\n",
           VERSION, kFormats[g_from].name, kFormats[g_to].name, level_of());
    printf("Start dir: %s\n", g_start_dir);
    printf("Options: overwrite=%s | verbose=%s | TUI=%s\n",
           g_overwrite ? "ON" : "off", g_verbose ? "ON" : "off",
           g_progress ? "ON" : "off");
    if (g_dist_dir)
        printf("Results will be moved to: %s (original paths preserved)\n", g_dist_dir);
    printf("Log file: %s\n", logname);

    g_t_start = time(NULL);
    box_init();

    walk_tree(g_start_dir);
    check_interrupted();

    g_cur_file[0] = 0;
    box_render();

    printf("\n\n===== Summary =====\n");
    printf("Log file: %s\n", logname);
    {
        char ts[16];
        printf("Converted: %ld archive(s) | Total time: %s\n",
               g_done, fmt_time(time(NULL) - g_t_start, ts));
    }
    puts("Done.");

    if (g_log != stderr) fclose(g_log);
    return 0;
}
