/* oc3_grid.c: exhaustive check of OC1 and its variants (kgen/oc3.c) over every three-agent profile with integer
 * values in [0, V] on m goods, every good valued by some agent and every agent valuing some good.  Agents are
 * interchangeable (all six orders are tested), so only profiles with rows in nondecreasing lexicographic order are
 * enumerated.  Goods are NOT identified up to permutation: ties are broken by good index, so relabelings differ.
 *
 *   gcc -O2 -o kgen/oc3_grid kgen/oc3_grid.c && kgen/oc3_grid M V [SHOW]
 * Output: profiles, starts, and failures per class (CODE = OC1 as tested in k4/sdc, STRICT = chains t >= 1,
 * FREEOC = OC, MD, SDC = no order's picks extend), with the first SHOW failing profiles of each class.
 */
#include <stdio.h>
#include <stdlib.h>
#include "oc3.c"

int main(int argc, char **argv)
{
    int m = atoi(argv[1]), V = atoi(argv[2]), SHOW = argc > 3 ? atoi(argv[3]) : 3;
    int L = 3 * m;
    long long v[60]; int dig[60];
    long long out[48]; int wit[18];
    long long prof = 0, starts = 0, f_code = 0, f_strict = 0, f_free = 0, f_md = 0, f_sdc = 0, need1 = 0;
    long long shown[5] = {0, 0, 0, 0, 0};
    for (int k = 0; k < L; k++) dig[k] = 0;
    for (;;) {
        /* rows sorted: row0 <= row1 <= row2 lexicographically */
        int ok = 1;
        for (int r = 0; r < 2 && ok; r++) {
            int c = 0;
            for (int g = 0; g < m; g++) { if (dig[r * m + g] != dig[(r + 1) * m + g]) { c = dig[r * m + g] < dig[(r + 1) * m + g] ? -1 : 1; break; } }
            if (c > 0) ok = 0;
        }
        for (int g = 0; g < m && ok; g++) if (!dig[g] && !dig[m + g] && !dig[2 * m + g]) ok = 0;
        for (int r = 0; r < 3 && ok; r++) { int any = 0; for (int g = 0; g < m; g++) any |= dig[r * m + g]; if (!any) ok = 0; }
        if (ok) {
            for (int k = 0; k < L; k++) v[k] = dig[k];
            oc3(m, v, out, wit);
            prof++;
            int sdc = 0;
            for (int o = 0; o < 6; o++) {
                long long *d = out + o * 8;
                starts++;
                if (d[3]) sdc = 1;
                if (!d[0] && d[1]) need1++;
                int fl[4] = {!d[1], !d[2], !d[4], !d[5]};
                long long *cnt[4] = {&f_code, &f_strict, &f_free, &f_md};
                const char *nm[4] = {"CODE", "STRICT", "FREEOC", "MD"};
                for (int t = 0; t < 4; t++) if (fl[t]) {
                    (*cnt[t])++;
                    if (shown[t] < SHOW) {
                        shown[t]++;
                        printf("FAIL %s order %d%d%d v", nm[t], ORD[o][0], ORD[o][1], ORD[o][2]);
                        for (int k = 0; k < L; k++) printf("%s%lld", k % m ? "," : " ", v[k]);
                        printf("  (EFX0 allocations %lld)\n", d[6]);
                        fflush(stdout);
                    }
                }
            }
            if (!sdc) {
                f_sdc++;
                if (shown[4] < SHOW) {
                    shown[4]++; printf("FAIL SDC v");
                    for (int k = 0; k < L; k++) printf("%s%lld", k % m ? "," : " ", v[k]);
                    printf("\n"); fflush(stdout);
                }
            }
        }
        int k = 0;
        while (k < L && dig[k] == V) dig[k++] = 0;
        if (k == L) break;
        dig[k]++;
    }
    printf("m %d V %d profiles %lld starts %lld need-one-chain %lld fail CODE %lld STRICT %lld FREEOC %lld MD %lld SDC %lld\n",
           m, V, prof, starts, need1, f_code, f_strict, f_free, f_md, f_sdc);
    return 0;
}
