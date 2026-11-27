"""FAIL-STRUCT₀ (k4/sdc.md §31, K4.SDC.FAILSTRUCT0) at the named failing starts outside the exports: the k = 5
instances N3K5, n3_m6_93 and RF5 (ksens / kgen-n3) and the k = 4 set-twin start 5_pure #440 (d1).
    python3 k4/sdc/failstruct_extra.py"""
import failstruct_check as F

CASES = {
    'N3K5 (k=5, n=3)': ([[0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 4, 5]], [[3, 22, 23, 38, 43], [15, 17, 27, 40, 43], [1, 2, 4]], (4, 5, 1)),
    'n3_m6_93 (k=5, n=3)': ([[0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 3, 4, 5]], [[3, 33, 39, 35, 43], [16, 20, 32, 26, 43], [3, 6, 2, 10]], (3, 5, 1)),
    'RF5 (k=5, n=4)': ([[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]], [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]], (6, 5, 4, 3)),
    '5_pure #440 (k=4, n=5)': ([[0, 3, 5, 7], [1, 2, 3, 6], [1, 2, 6, 7], [4, 5, 6, 7], [4, 5, 6, 7]], [[5, 19, 13, 10], [9, 6, 17, 12], [3, 5, 7, 6], [14, 1, 7, 4], [18, 4, 11, 5]], (3, 6, 7, 4, 5)),
}

if __name__ == '__main__':
    print('$ python3 k4/sdc/failstruct_extra.py')
    for name, (s, v, y) in CASES.items():
        C, _ = F.job((s, v, y))
        print(name, sorted(k for k in C if k != 'starts'))
