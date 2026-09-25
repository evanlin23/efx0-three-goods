/* k = 4 construction tester: runs a construction on every strict profile (or a random sample) of every core in a
   cores file (written by tester.py's export() from the certificates) and checks each output against the raw EFX₀
   definition with explicit integer values: v_i(X_i) >= v_i(X_j) - v_i(h) for all i != j and h in X_j (all goods
   counted, v_i = 0 outside R_i). With --d2 it also requires at most one bundle of more than 2 goods.
   Types are enumerated here from scratch, as in k4/check4.py: vectors in [1, 16]^d, one per dense ranking of the
   nonempty subset sums (the lexicographically first); strict = all subset sums distinct; balanced = max < sum of
   the others; an agent with two private goods p, q also needs p + q < s + t. (--ties: every balanced type.)
   The construction is a plugin (k4plugin.h, dlopen), a pipe to any program (--pipe), or the certificate itself
   (--oracle: the first listed allocation that passes; a brute-force coverage check of the certificate).
   Build: gcc -O2 -o tester tester.c -ldl     Usage: see tester.py (it builds, exports and runs this). */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include "k4plugin.h"

static int T3[64][3], T4[2048][4], NT3, NT4;
static void types(int d, int ties) {
    int keys = 0; static uint64_t seen[8192][2];
    int v[4];
    for (long code = 0; code < (1L << (4 * d)); code++) {
        for (int k = 0; k < d; k++) v[k] = (int)(code >> (4 * (d - 1 - k)) & 15) + 1;   /* lexicographic order */
        int S = (1 << d) - 1, sums[16], mx = 0, tot = 0;
        for (int k = 0; k < d; k++) { tot += v[k]; if (v[k] > mx) mx = v[k]; }
        if (mx >= tot - mx) continue;                                        /* balanced */
        for (int s = 1; s <= S; s++) { sums[s] = 0; for (int k = 0; k < d; k++) if (s >> k & 1) sums[s] += v[k]; }
        int distinct = 1;
        for (int s = 1; s <= S && distinct; s++) for (int t = s + 1; t <= S; t++) if (sums[s] == sums[t]) { distinct = 0; break; }
        if (!ties && !distinct) continue;
        uint64_t key[2] = {0, 0};                                            /* dense rank of each subset sum, 4 bits */
        for (int s = 1; s <= S; s++) {
            int r = 0;
            for (int t = 1; t <= S; t++) { int smaller = 1; if (sums[t] >= sums[s]) smaller = 0;
                if (smaller) { int dup = 0; for (int u = 1; u < t; u++) if (sums[u] == sums[t]) { dup = 1; break; } r += !dup; } }
            key[(s - 1) / 16] |= (uint64_t)r << (4 * ((s - 1) % 16));
        }
        int found = 0;
        for (int k = 0; k < keys && !found; k++) found = seen[k][0] == key[0] && seen[k][1] == key[1];
        if (found) continue;
        seen[keys][0] = key[0]; seen[keys][1] = key[1]; keys++;
        if (d == 3) { memcpy(T3[NT3++], v, sizeof(int) * 3); } else { memcpy(T4[NT4++], v, sizeof(int) * 4); }
    }
}

typedef struct { char id[64], src[128]; int n, m, deg[K4_MAXN], goods[K4_MAXN][4], K; int *allocs; } core_t;

static int read_core(FILE *f, core_t *c) {
    char line[4096];
    while (fgets(line, sizeof line, f)) {
        if (line[0] != 'C') continue;
        if (sscanf(line, "C %63s %d %d %127s", c->id, &c->n, &c->m, c->src) != 4) return -1;
        if (c->n > K4_MAXN || c->m > K4_MAXM) return -1;
        if (c->n < 1 || c->m < 1) return -1;
        for (int i = 0; i < c->n; i++) {
            if (fscanf(f, " A %d", &c->deg[i]) != 1 || c->deg[i] < 3 || c->deg[i] > 4) return -1;
            for (int k = 0; k < c->deg[i]; k++)
                if (fscanf(f, "%d", &c->goods[i][k]) != 1 || c->goods[i][k] < 0 || c->goods[i][k] >= c->m) return -1;
        }
        if (fscanf(f, " K %d", &c->K) != 1 || c->K < 0) return -1;
        c->allocs = malloc(sizeof(int) * ((long)c->K * c->m + 1));
        if (!c->allocs) return -1;
        for (long a = 0; a < (long)c->K * c->m; a++)
            if (fscanf(f, "%d", &c->allocs[a]) != 1 || c->allocs[a] < 0 || c->allocs[a] >= c->n) return -1;
        return 1;
    }
    return 0;
}

/* raw EFX0 (and, with d2, the D2 shape); returns 0 if fine, else writes a reason */
static int check(const k4_inst *I, const int *own, int d2, char *why) {
    int n = I->n, m = I->m, v[K4_MAXN][K4_MAXM];
    for (int g = 0; g < m; g++) if (own[g] < 0 || own[g] >= n) { sprintf(why, "invalid owner %d of good %d", own[g], g); return 1; }
    memset(v, 0, sizeof v);
    for (int i = 0; i < n; i++) for (int k = 0; k < I->deg[i]; k++) v[i][I->goods[i][k]] = I->val[i][k];
    for (int i = 0; i < n; i++) {
        int mine = 0; for (int g = 0; g < m; g++) if (own[g] == i) mine += v[i][g];
        for (int j = 0; j < n; j++) {
            if (j == i) continue;
            int tot = 0; for (int g = 0; g < m; g++) if (own[g] == j) tot += v[i][g];
            for (int h = 0; h < m; h++) if (own[h] == j && mine < tot - v[i][h]) {
                sprintf(why, "not EFX0: agent %d (value %d) envies bundle of agent %d minus good %d (value %d)", i, mine, j, h, tot - v[i][h]);
                return 1;
            }
        }
    }
    if (d2) {
        int big = 0; for (int j = 0; j < n; j++) { int c = 0; for (int g = 0; g < m; g++) c += own[g] == j; big += c > 2; }
        if (big > 1) { sprintf(why, "not D2: %d bundles of more than 2 goods", big); return 1; }
    }
    return 0;
}

static int (*construct)(const k4_inst *, int *);
static FILE *pin, *pout; static int oracle, d2;
static const core_t *CUR;
static int run_pipe(const k4_inst *I, int *own) {
    fprintf(pin, "%d %d", I->n, I->m);
    for (int i = 0; i < I->n; i++) {
        fprintf(pin, " %d", I->deg[i]);
        for (int k = 0; k < I->deg[i]; k++) fprintf(pin, " %d", I->goods[i][k]);
        for (int k = 0; k < I->deg[i]; k++) fprintf(pin, " %d", I->val[i][k]);
    }
    fprintf(pin, "\n"); fflush(pin);
    for (int g = 0; g < I->m; g++) if (fscanf(pout, "%d", &own[g]) != 1) { fprintf(stderr, "pipe: construction closed or sent junk\n"); exit(2); }
    return 0;
}
static int run_oracle(const k4_inst *I, int *own) {
    char why[256];
    for (int a = 0; a < CUR->K; a++) if (!check(I, CUR->allocs + a * I->m, d2, why)) { memcpy(own, CUR->allocs + a * I->m, sizeof(int) * I->m); return 0; }
    return 1;
}

static uint64_t rng = 88172645463325252ULL;
static uint64_t xs(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void json_fail(FILE *f, const core_t *c, const k4_inst *I, const int *own, int declined, const char *why) {
    char w2[256]; int wit = -1;
    for (int a = 0; a < c->K && wit < 0; a++) if (!check(I, c->allocs + a * c->m, d2, w2)) wit = a;
    fprintf(f, "{\"core\":\"%s\",\"src\":\"%s\",\"n\":%d,\"m\":%d,\"sets\":[", c->id, c->src, c->n, c->m);
    for (int i = 0; i < c->n; i++) { fprintf(f, "%s[", i ? "," : ""); for (int k = 0; k < c->deg[i]; k++) fprintf(f, "%s%d", k ? "," : "", c->goods[i][k]); fprintf(f, "]"); }
    fprintf(f, "],\"values\":[");
    for (int i = 0; i < c->n; i++) { fprintf(f, "%s[", i ? "," : ""); for (int k = 0; k < c->deg[i]; k++) fprintf(f, "%s%d", k ? "," : "", I->val[i][k]); fprintf(f, "]"); }
    fprintf(f, "],\"alloc\":");
    if (declined) fprintf(f, "null"); else { fprintf(f, "["); for (int g = 0; g < c->m; g++) fprintf(f, "%s%d", g ? "," : "", own[g]); fprintf(f, "]"); }
    fprintf(f, ",\"reason\":\"%s\",\"witness\":", why);
    if (wit < 0) fprintf(f, "null"); else { fprintf(f, "["); for (int g = 0; g < c->m; g++) fprintf(f, "%s%d", g ? "," : "", c->allocs[wit * c->m + g]); fprintf(f, "]"); }
    fprintf(f, "}\n"); fflush(f);
}

int main(int argc, char **argv) {
    const char *cores = NULL, *plugin = NULL, *parg = "", *pipecmd = NULL, *failout = NULL;
    long sample = 0; int maxfail = 3, ties = 0, part = 0, parts = 1; long stop_after = -1;
    for (int a = 1; a < argc; a++) {
        char *s = argv[a];
        if (!strncmp(s, "--cores=", 8)) cores = s + 8;
        else if (!strncmp(s, "--plugin=", 9)) plugin = s + 9;
        else if (!strncmp(s, "--plugin-arg=", 13)) parg = s + 13;
        else if (!strncmp(s, "--pipe=", 7)) pipecmd = s + 7;
        else if (!strcmp(s, "--oracle")) oracle = 1;
        else if (!strcmp(s, "--d2")) d2 = 1;
        else if (!strcmp(s, "--ties")) ties = 1;
        else if (!strncmp(s, "--sample=", 9)) sample = atol(s + 9);
        else if (!strncmp(s, "--seed=", 7)) { rng = 88172645463325252ULL ^ (uint64_t)atoll(s + 7) * 0x9E3779B97F4A7C15ULL; if (!rng) rng = 1; }
        else if (!strncmp(s, "--max-fail=", 11)) maxfail = atoi(s + 11);
        else if (!strncmp(s, "--stop-after=", 13)) stop_after = atol(s + 13);
        else if (!strncmp(s, "--part=", 7)) sscanf(s + 7, "%d/%d", &part, &parts);
        else if (!strncmp(s, "--fail-out=", 11)) failout = s + 11;
        else { fprintf(stderr, "unknown option %s\n", s); return 2; }
    }
    if (!cores || (!!plugin + !!pipecmd + oracle) != 1) { fprintf(stderr, "need --cores= and exactly one of --plugin=, --pipe=, --oracle\n"); return 2; }
    types(3, ties); types(4, ties);
    printf("types: %d (3 goods), %d (4 goods)%s\n", NT3, NT4, ties ? " [balanced, ties allowed]" : " [strict balanced]");
    if ((!ties && (NT3 != 6 || NT4 != 288)) || (ties && (NT3 != 13 || NT4 != 1271))) { fprintf(stderr, "type count mismatch\n"); return 2; }
    if (plugin) {
        void *h = dlopen(plugin, RTLD_NOW); if (!h) { fprintf(stderr, "%s\n", dlerror()); return 2; }
        construct = (int (*)(const k4_inst *, int *))dlsym(h, "k4_construct");
        if (!construct) { fprintf(stderr, "plugin has no k4_construct\n"); return 2; }
        int (*init)(const char *) = (int (*)(const char *))dlsym(h, "k4_init");
        if (init && init(parg)) { fprintf(stderr, "k4_init failed\n"); return 2; }
    } else if (pipecmd) {
        int a[2], b[2]; if (pipe(a) || pipe(b)) return 2;
        signal(SIGPIPE, SIG_DFL);
        if (!fork()) { dup2(a[0], 0); dup2(b[1], 1); close(a[1]); close(b[0]); execl("/bin/sh", "sh", "-c", pipecmd, (char *)0); _exit(127); }
        close(a[0]); close(b[1]); pin = fdopen(a[1], "w"); pout = fdopen(b[0], "r");
        construct = run_pipe;
    } else construct = run_oracle;
    FILE *f = fopen(cores, "r"); if (!f) { perror(cores); return 2; }
    FILE *fo = failout ? fopen(failout, "w") : NULL;
    core_t c; long idx = -1, ncores = 0, nfailcores = 0; double tot = 0, totfail = 0;
    int r;
    while ((r = read_core(f, &c)) == 1) {
        idx++;
        if (idx % parts != part) { free(c.allocs); continue; }
        k4_inst I; memset(&I, 0, sizeof I); I.n = c.n; I.m = c.m;
        for (int i = 0; i < c.n; i++) { I.deg[i] = c.deg[i]; for (int k = 0; k < c.deg[i]; k++) { I.goods[i][k] = c.goods[i][k]; I.ndeg[c.goods[i][k]]++; } }
        int D[K4_MAXN], *dom[K4_MAXN];                                    /* per agent: allowed type indices */
        for (int i = 0; i < c.n; i++) {
            int d = c.deg[i], nt = d == 3 ? NT3 : NT4, p[4], np = 0;
            for (int k = 0; k < d; k++) if (I.ndeg[c.goods[i][k]] == 1) p[np++] = k;
            dom[i] = malloc(sizeof(int) * nt); D[i] = 0;
            for (int t = 0; t < nt; t++) {
                const int *v = d == 3 ? T3[t] : T4[t];
                if (np == 2) { int s = 0; for (int k = 0; k < d; k++) s += v[k]; if (2 * (v[p[0]] + v[p[1]]) >= s) continue; }
                dom[i][D[i]++] = t;
            }
        }
        double total = 1; for (int i = 0; i < c.n; i++) total *= D[i];
        long todo = sample ? sample : (long)total;
        int cnt[K4_MAXN] = {0}, own[K4_MAXM]; long fails = 0; char why[256];
        CUR = &c;
        for (long p = 0; p < todo; p++) {
            if (sample) for (int i = 0; i < c.n; i++) cnt[i] = (int)(xs() % (uint64_t)D[i]);
            for (int i = 0; i < c.n; i++) { const int *v = c.deg[i] == 3 ? T3[dom[i][cnt[i]]] : T4[dom[i][cnt[i]]]; memcpy(I.val[i], v, sizeof(int) * c.deg[i]); }
            for (int g = 0; g < c.m; g++) own[g] = -1;
            int dec = construct(&I, own);
            int bad = dec ? (sprintf(why, "declined"), 1) : check(&I, own, d2, why);
            if (bad) {
                if (fails < maxfail) {
                    printf("  FAIL core %s (n=%d m=%d): %s\n", c.id, c.n, c.m, why);
                    if (fo) json_fail(fo, &c, &I, own, dec, why);
                }
                fails++;
            }
            if (!sample) for (int i = c.n - 1; i >= 0; i--) { if (++cnt[i] < D[i]) break; cnt[i] = 0; }
        }
        ncores++; tot += todo; totfail += fails; nfailcores += fails > 0;
        printf("core %s n=%d m=%d src=%s: %ld profiles%s, %ld failures\n", c.id, c.n, c.m, c.src, todo, sample ? " (sampled)" : "", fails);
        fflush(stdout);
        for (int i = 0; i < c.n; i++) free(dom[i]);
        free(c.allocs);
        if (stop_after >= 0 && nfailcores >= stop_after) break;
    }
    if (r < 0) { fprintf(stderr, "malformed cores file: core record %ld (0-based, in file order)\n", idx + 1); return 2; }
    printf("SUMMARY: %ld cores, %.0f profiles, %.0f failures in %ld cores%s\n", ncores, tot, totfail, nfailcores, d2 ? " (EFX0 + D2)" : " (EFX0)");
    if (fo) fclose(fo);
    return nfailcores ? 1 : 0;
}
