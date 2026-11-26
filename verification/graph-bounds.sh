#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lean=$(realpath "$(command -v "${LEAN:-lean}")")
lake="$(dirname "$lean")/lake"
export PATH="$(dirname "$lean"):$PATH"
mathlib=${MATHLIB_DIR:-"$root/.lake/graph-bounds-mathlib"}
if [[ ! -d "$mathlib" ]]; then
    mkdir -p "$(dirname "$mathlib")"
    git clone --depth 1 --branch v4.19.0 https://github.com/leanprover-community/mathlib4.git "$mathlib"
fi
cd "$mathlib"
revision=$(git rev-parse HEAD)
if [[ "$revision" != c44e0c8ee63ca166450922a373c7409c5d26b00b ]]; then
    echo 'Use the mathlib checkout at tag v4.19.0.' >&2
    exit 1
fi
if [[ ! -f .lake/build/lib/lean/Mathlib/Algebra/BigOperators/Ring/Finset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Perm.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/BigOperators.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Powerset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/Order/BigOperators/Group/Finset.olean ]]; then
    "$lake" exe cache get Mathlib/Algebra/BigOperators/Ring/Finset.lean \
      Mathlib/Data/Fintype/Perm.lean Mathlib/Data/Fintype/BigOperators.lean \
      Mathlib/Data/Fintype/Powerset.lean Mathlib/Algebra/Order/BigOperators/Group/Finset.lean
fi
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build:$("$lake" env printenv LEAN_PATH)"
"$lean" --version
for file in "$root/cases/k16/Delete.lean" "$root/cases/k19/EdgeWalk.lean" \
    "$root/cases/k19/LowerBound.lean"; do
    "$lean" --root="$root" -o "$build/$(basename "$file" .lean).olean" "$file"
done
for name in UniformCuts CutRepair GraphLayouts ColorCoordinates LegalEdges Bounds; do
    "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/graph-bounds/$name.lean"
done
