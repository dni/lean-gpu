#!/usr/bin/env bash
# Solve every goal queued by `set_option farkas.batch true` in one solver run.
#   lake build ...            # pass 1: queues goals in .farkas/pending.txt
#   scripts/farkas-batch.sh   # one batched solve, results go to .farkas/cache.txt
#   lake build ...            # pass 2: every goal closes from the cache
# Lake caches pass 1, so touch the files that use `farkas` (or clean) before pass 2.
set -euo pipefail
cd "$(dirname "$0")/.."
solver=${FARKAS_SOLVER:-gpu/build/farkas}
[ -s .farkas/pending.txt ] || { echo "nothing queued"; exit 0; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Pending keys look like `m n|a1 .. an b;...`; turn them into a problems file.
python3 - .farkas/pending.txt "$tmp/problems.txt" "$tmp/keys.txt" <<'PY'
import sys
keys = list(dict.fromkeys(l.strip() for l in open(sys.argv[1]) if l.strip()))
with open(sys.argv[2], "w") as out:
    for i, key in enumerate(keys):
        head, rows = key.split("|")
        out.write(f"q{i} {head}\n" + "\n".join(rows.split(";")) + "\n")
open(sys.argv[3], "w").write("\n".join(keys) + "\n")
PY

"$solver" --certs "$tmp/problems.txt" "$tmp/certs.txt"

python3 - "$tmp/keys.txt" "$tmp/certs.txt" .farkas/cache.txt <<'PY'
import sys
keys = open(sys.argv[1]).read().splitlines()
solved = 0
with open(sys.argv[3], "a") as cache:
    for line in open(sys.argv[2]):
        name, *cert = line.split()
        if cert == ["-"]:
            print(f"no certificate: {keys[int(name[1:])]}", file=sys.stderr)
            continue
        cache.write(f"{keys[int(name[1:])]}\t{' '.join(cert)}\n")
        solved += 1
print(f"{solved}/{len(keys)} queued goals solved")
PY
rm .farkas/pending.txt
