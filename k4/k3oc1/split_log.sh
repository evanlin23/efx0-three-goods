#!/bin/sh
# split a raw run log into its summary (committed as NAME.log) and its HARD lines (committed as NAME.hard.gz)
# usage: k4/k3oc1/split_log.sh RAW.log OUT_PREFIX
grep -v '^HARD' "$1" > "$2.log"
grep '^HARD' "$1" | gzip -9 > "$2.hard.gz"
