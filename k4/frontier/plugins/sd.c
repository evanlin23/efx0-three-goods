/* Example plugin for k4/frontier/tester.py: serial dictatorship in agent order 0..n-1 (each agent takes its favourite
   remaining good), then every unpicked good to the last agent. Not a correct construction; it shows the API and
   gives the tester something to find. Build: gcc -O2 -shared -fPIC -I.. -o sd.so sd.c */
#include "k4plugin.h"
int k4_construct(const k4_inst *I, int *owner) {
    int taken[K4_MAXM] = {0};
    for (int g = 0; g < I->m; g++) owner[g] = I->n - 1;
    for (int i = 0; i < I->n; i++) {
        int best = -1;
        for (int k = 0; k < I->deg[i]; k++) {
            int g = I->goods[i][k];
            if (!taken[g] && (best < 0 || I->val[i][k] > I->val[i][best])) best = k;
        }
        if (best >= 0) { taken[I->goods[i][best]] = 1; owner[I->goods[i][best]] = i; }
    }
    return 0;
}
