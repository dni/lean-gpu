#!/usr/bin/env bash
# Search benchmark: random batches at a few sizes (half infeasible, half feasible).
# Usage: scripts/bench.sh [COUNT]   (run `make -C gpu` or `make -C gpu cuda` first)
set -euo pipefail
cd "$(dirname "$0")/.."
count=${1:-1000}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
for size in "12 6" "30 10" "60 20"; do
  read -r m n <<<"$size"
  python3 scripts/gen.py "$count" "$m" "$n" 1 >"$tmp/p.txt"
  printf '%3s x %-3s ' "$m" "$n"
  ./gpu/build/farkas "$tmp/p.txt" /dev/null 2>&1 | tail -1
done
