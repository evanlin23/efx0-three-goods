#!/bin/bash
# n = 5 driver (workstream compute/k4-oc1max-cert): OC2^max (and where OC1^max fails) for every strict profile of
# every n = 5 core hypergraph, in chunks of about 1,000 hypergraphs (a list split by --stride/--offset).  For each
# chunk: the CEGAR (k4/oc1cert/run.py --depth=2, streaming certificate to the scratchpad), the independent check
# (k4/oc1cert/check.py), then a commit of the chunk's summary, logs and the certificates of the hypergraphs where
# OC1^max fails plus every 50th certificate (the full certificates, ~10 MB per chunk, stay in the scratchpad; the run
# is deterministic and can be regenerated).
#     bash k4/oc1cert/n5_driver.sh SCRATCH_DIR [LIST ...]
set -u
SP=$1; shift
LISTS=${@:-5_n4_1 5_n4_2 5_n4_3 5_n4_4 5_pure}
cd "$(dirname "$0")/../.."
OUT=results/k4_oc1max/n5
mkdir -p "$OUT" "$SP"
for L in $LISTS; do
  N=$(python3 -c "import json,gzip; print(len(json.load(gzip.open('results/k4_certs_$L.json.gz'))['cores']))")
  S=$(( (N + 999) / 1000 ))
  for ((o = 0; o < S; o++)); do
    TAG=${L}_s${S}o${o}
    [ -f "$OUT/${TAG}_check.log" ] && grep -q '^RESULT' "$OUT/${TAG}_check.log" && continue   # done before
    # everything is written to the scratchpad first and copied into results/ only when the chunk is complete
    python3 k4/oc1cert/run.py "$L" --depth=2 --stride=$S --offset=$o --jobs=4 \
        --out="$SP/${TAG}.jsonl.gz" --summary="$SP/${TAG}_summary.jsonl.gz" > "$SP/${TAG}_run.log" 2>&1
    python3 k4/oc1cert/check.py "$SP/${TAG}.jsonl.gz" > "$SP/${TAG}_check.log" 2>&1
    python3 - "$SP/${TAG}.jsonl.gz" "$SP/${TAG}_certs_selected.jsonl.gz" <<'EOF'
import sys, gzip, json
src, dst = sys.argv[1], sys.argv[2]
with gzip.open(src, 'rt') as f, gzip.open(dst, 'wt') as g:
    g.write(f.readline())
    for k, line in enumerate(f):
        r = json.loads(line)
        if r.get('oc1_fails') or r['result'] != 'certified' or k % 50 == 0: g.write(line)
EOF
    cp "$SP/${TAG}_summary.jsonl.gz" "$SP/${TAG}_run.log" "$SP/${TAG}_certs_selected.jsonl.gz" "$OUT/"
    cp "$SP/${TAG}_check.log" "$OUT/"                     # last: its RESULT line marks the chunk as done
    git add "$OUT/${TAG}"_* && git commit -q -m "[compute/k4-oc1max-cert] n = 5 chunk $TAG: OC2^max CEGAR and independent check (summary, logs, selected certificates)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01BYMGebCRA4DLjCqvLLXBaY" && \
      for t in 1 2 3 4; do git push -q && break; sleep $((2 ** t)); done
    echo "chunk $TAG done: $(grep -E '^result|^hypergraphs where' "$OUT/${TAG}_run.log" | tr '\n' ' ') | $(grep '^RESULT' "$OUT/${TAG}_check.log")"
  done
done
echo "DRIVER FINISHED"
