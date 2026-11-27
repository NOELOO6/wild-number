#!/usr/bin/env bash
# Called by graph-bounds.sh with a fresh build directory and pinned mathlib.
set -euo pipefail
source "$root/verification/native.sh"
exact="$root/verification/exact"
compile() {
  "$lean" --root="$exact" -s 65536 -o "$build/$1.olean" "$exact/$1.lean"
}
# Only these data modules need compiled code for the two matching enumerations.
# They use Lean's standard library. The graph theorems use mathlib in addition.
native_module "$root/cases/k16/Delete.lean"
native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
native_module "$exact/GraphSearch.lean" -lEdgeWalk
native_module "$exact/NineData.lean" -lGraphSearch
for name in ExactModel UniversalLower MatchingModel Enumerate Counting NineEncoding; do
  compile "$name"
done

python3 "$root/cases/k13/make_k13_formula.py" "$build/nine.cnf" --without-symmetry
solver="$(dirname "$lean")/cadical"
# CaDiCaL returns 20 for UNSAT. The Lean check below verifies its proof.
status=0
"$solver" -q --lrat "$build/nine.cnf" "$build/nine.lrat" || status=$?
if [[ $status != 20 ]]; then
  echo "CaDiCaL returned $status while producing the nine-point certificate." >&2
  exit 1
fi
python3 - "$build/nine.lrat" "$build/nine.hex" <<'PY'
from binascii import hexlify
from pathlib import Path
import sys
with Path(sys.argv[1]).open("rb") as src, Path(sys.argv[2]).open("wb") as dst:
    while block := src.read(1024 * 1024):
        dst.write(hexlify(block))
PY
for name in NineCertificate NineTrace; do
  cp "$exact/$name.lean" "$build/"
  "$lean" --root="$build" -s 65536 -o "$build/$name.olean" "$build/$name.lean"
done
