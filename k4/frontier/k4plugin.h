/* Plugin API of k4/frontier/tester.c: a construction maps a k = 4 core instance to an allocation.
   Build a plugin:  gcc -O2 -shared -fPIC -o myplugin.so myplugin.c   (include this header)
   Run:             python3 k4/frontier/tester.py --plugin=myplugin.so [options]   (see tester.py --help) */
#ifndef K4PLUGIN_H
#define K4PLUGIN_H
#define K4_MAXN 16
#define K4_MAXM 48

typedef struct {
    int n, m;                    /* agents 0..n-1, goods 0..m-1 */
    int deg[K4_MAXN];            /* |R_i|: 3 or 4 */
    int goods[K4_MAXN][4];       /* R_i as increasing good indices; goods[i][k] for k < deg[i] */
    int val[K4_MAXN][4];         /* v_i(goods[i][k]) > 0, integers; v_i(g) = 0 for every g outside R_i */
    int ndeg[K4_MAXM];           /* number of agents valuing good g (1 = private) */
} k4_inst;

/* Required. Write owner[g] in 0..n-1 for every good g. Return 0; any other value means the construction declines
   (counted as a failure, reason "declined"). Must be deterministic and must not keep state between calls that
   changes its answers. */
int k4_construct(const k4_inst *I, int *owner);

/* Optional: called once before the first instance with the string given by --plugin-arg (or ""). Return 0. */
int k4_init(const char *arg);
#endif
