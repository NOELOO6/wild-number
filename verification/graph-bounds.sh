#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
if [[ ${1:-bounds} == exact ]]; then
    "$root/verification/graph-bounds.sh" exact-k13
    "$root/verification/graph-bounds.sh" exact-k17
    "$root/verification/graph-bounds.sh" sieve
    exit 0
fi
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
if [[ ! -f .lake/build/lib/lean/Mathlib/GroupTheory/Perm/Sign.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/BigOperators/Ring/Finset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/BigOperators/Fin.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Perm.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/BigOperators.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Data/Fintype/Powerset.olean ||
      ! -f .lake/build/lib/lean/Mathlib/Algebra/Order/BigOperators/Group/Finset.olean ]]; then
    "$lake" exe cache get Mathlib/GroupTheory/Perm/Sign.lean Mathlib/Algebra/BigOperators/Ring/Finset.lean \
      Mathlib/Data/Fintype/Perm.lean Mathlib/Data/Fintype/BigOperators.lean Mathlib/Algebra/BigOperators/Fin.lean \
      Mathlib/Data/Fintype/Powerset.lean Mathlib/Algebra/Order/BigOperators/Group/Finset.lean
fi
if [[ ${1:-bounds} == regrouping || ${1:-bounds} == sieve ]]; then
    extras=(Mathlib/Combinatorics/Hall/Finite Mathlib/Data/ZMod/Basic Mathlib/Data/Fintype/Prod Mathlib/Data/List/Dedup Mathlib/Data/Int/GCD Mathlib/Tactic/Ring)
    if [[ ${1:-bounds} == sieve ]]; then
        extras=(Mathlib/Tactic/Linarith Mathlib/Tactic/FieldSimp)
    fi
    for module in "${extras[@]}"; do
        if [[ ! -f .lake/build/lib/lean/"$module".olean ]]; then
            "$lake" exe cache get "${extras[@]/%/.lean}"
            break
        fi
    done
fi
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build:$("$lake" env printenv LEAN_PATH)"
"$lean" --version
if [[ ${1:-bounds} == exact-k13 ]]; then
    source "$root/verification/exact-k13.sh"
    exit 0
fi
if [[ ${1:-bounds} == exact-k17 || ${1:-bounds} == exact-k17-pairs ]]; then
    source "$root/verification/exact-k17.sh"
    exit 0
fi
for file in "$root/cases/k16/Delete.lean" "$root/cases/k19/EdgeWalk.lean"; do
    "$lean" --root="$root" -o "$build/$(basename "$file" .lean).olean" "$file"
done
"$lean" --root="$root" -o "$build/LowerBound.olean" "$root/cases/k19/LowerBound.lean"
for name in UniformCuts CutRepair GraphLayouts ColorCoordinates LegalEdges Bounds; do
    "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/graph-bounds/$name.lean"
done
case ${1:-bounds} in
  bounds) ;;
  sieve)
    for name in ExactModel UniversalLower MatchingModel; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/exact/$name.lean"
    done
    for name in FiniteSieve Avoidance TripleParts TripleCounts Coupling Relabel TripleCoupling ClosedEvents SizeBounds MatchingCuts Factors Rainbow FrozenStats FrozenRows RowTotals DegreeChord FrozenLayout PlantedCuts StarDraw Numeric GraphSieve KernelTables ExactRange; do
      "$lean" --root="$root" -j2 -s 65536 -o "$build/$name.olean" "$root/cases/sieve/$name.lean"
    done
    ;;
  regrouping)
    for name in ExactModel UniversalLower GraphSearch MatchingModel; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/verification/exact/$name.lean"
    done
    "$lean" --root="$root" -o "$build/StarDraw.olean" "$root/cases/sieve/StarDraw.lean"
    for name in Periodic RoundRobin Reflection CyclicOrders TwoGroups CommonHalf MergeColors SwapExamples HalfTrap Bounds21; do
      "$lean" --root="$root" -s 65536 -o "$build/$name.olean" "$root/cases/regrouping/$name.lean"
    done
    ;;
  last-colors)
    "$lean" --root="$root" -o "$build/GraphCuts.olean" "$root/cases/k16/last-two/GraphCuts.lean"
    "$lean" --root="$root" -o "$build/Fourteen.olean" "$root/cases/k16/last-two/Fourteen.lean"
    for name in Example19 TwoMoves; do
      "$lean" --root="$root" -o "$build/$name.olean" "$root/cases/k19/two-moves/$name.lean"
    done
    ;;
  redraw)
    source "$root/verification/native.sh"
    redraw="$root/cases/k19/redraw"
    for name in MenuProof MenuTable SevenMore; do
      "$lean" --root="$redraw" -s 65536 -o "$build/$name.olean" "$redraw/$name.lean"
    done
    native_module "$redraw/LossTree.lean"
    native_module "$redraw/RawMenu.lean" -lLossTree
    for name in AllRoots TableLink EightBridge EightMore; do
      "$lean" --root="$redraw" --plugin="$build/libRawMenu.$ext" -j3 -s 65536 \
        -o "$build/$name.olean" "$redraw/$name.lean"
    done
    ;;
  pieces)
    pieces="$root/cases/k19/one-piece"
    for name in FiberMass BinMass GroupMerges PartitionCounts PieceTotals SmallAverage PieceBudget PiecePaths LastPiece; do
      "$lean" --root="$pieces" -s 65536 -o "$build/$name.olean" "$pieces/$name.lean"
    done
    ;;
  *) echo 'Use exact, exact-k13, exact-k17, exact-k17-pairs, bounds, sieve, regrouping, redraw, pieces or last-colors.' >&2; exit 2 ;;
esac
