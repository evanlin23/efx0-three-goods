"""Summarize the threshold search: per (n, k), which m are complete and the counts of each status.

A family (n, m, k) is COMPLETE when its result file has one record per hypergraph of
monotone/hypergraphs.enumerate_hypergraphs(n, m, k) and every record is UNSAT (or SAT, which would be a
counterexample). Files are results/monotone/n{n}_m{m}_k{k}.jsonl. For each (n, k) the admissible m range is
n + 4 (8 when n = 3) .. (k - 1) n (monotone/threshold.md §2).

Usage: python3 monotone/summarize.py [--recount]   (--recount re-enumerates to check completeness)
"""
import sys
import os
import re
import json
import glob
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def main():
    recount = "--recount" in sys.argv
    if recount:
        from hypergraphs import enumerate_hypergraphs
    fams = {}
    for f in glob.glob("results/monotone/n*_m*_k*.jsonl"):
        mt = re.search(r"n(\d+)_m(\d+)_k(\d+)(_only)?\.jsonl$", f)
        n, m, k = map(int, mt.groups()[:3])
        st = defaultdict(int)
        types = set()
        for line in open(f):
            r = json.loads(line)
            st[r["status"]] += 1
            types.add(tuple(r["types"]))
        complete = None
        if recount:
            hs = set(tuple(h) for h in enumerate_hypergraphs(n, m, k))
            if f.endswith("_only.jsonl"):
                # file holds only the hypergraphs whose largest |R_i| equals k (see run_search --only-k)
                hs = set(h for h in hs if max(sum(1 for t in h if (t >> a) & 1) for a in range(n)) == k)
            complete = (hs == types)
        fams[(n, m, k)] = (dict(st), len(types), complete)
    byk = defaultdict(list)
    for (n, m, k), v in sorted(fams.items()):
        byk[(n, k)].append((m, v))
    for (n, k), lst in sorted(byk.items()):
        lo = 8 if n == 3 else n + 4
        hi = (k - 1) * n
        have = {m for m, _ in lst}
        missing = [m for m in range(lo, hi + 1) if m not in have]
        tot = defaultdict(int)
        for m, (st, cnt, comp) in lst:
            for s, c in st.items():
                tot[s] += c
        flag = "" if not recount else ("  all files complete" if all(v[2] for _, v in lst) else "  INCOMPLETE FILE")
        print(f"n={n} k<={k}: m range {lo}..{hi}; files for m = {sorted(have)}; missing m = {missing}; "
              f"statuses {dict(tot)}{flag}")


if __name__ == "__main__":
    main()
