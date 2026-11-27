#!/usr/bin/env bash
# Called by graph-bounds.sh with the pinned mathlib and a fresh build directory.
set -euo pipefail
source "$root/verification/native.sh"
exact="$root/verification/exact"
native_module "$root/cases/k16/Delete.lean"
native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
native_module "$exact/GraphSearch.lean" -lEdgeWalk
native_module "$root/cases/k17/Groupings.lean"
native_module "$exact/PairData.lean" -lGraphSearch -lGroupings
for name in ExactModel UniversalLower MatchingModel Enumerate Counting RootedMatching PairFrames; do
  "$lean" --root="$exact" -s 65536 -o "$build/$name.olean" "$exact/$name.lean"
done
"$lean" --root="$exact" --plugin="$build/libPairData.$ext" -s 65536 \
  -o "$build/K17Pairs.olean" "$exact/K17Pairs.lean"

if [[ ${1:-} == exact-k17-pairs ]]; then
  return 0
fi

native_module "$exact/LayoutData.lean" -lPairData
native_module "$exact/PairTypes.lean" -lPairData
native_module "$exact/CutData.lean" -lLayoutData
native_module "$exact/CutValidation.lean" -lCutData
native_module "$exact/ThirdData.lean" -lCutData -lPairTypes
"$lean" --root="$root/cases/k17" -o "$build/Connectivity.olean" "$root/cases/k17/Connectivity.lean"

compile17() {
  local name=$1
  shift
  "$lean" --root="$exact" -s 65536 "$@" -o "$build/$name.olean" "$exact/$name.lean"
}
compile17 K17Numeric --plugin="$build/libThirdData.$ext"
compile17 LayoutChecks --plugin="$build/libLayoutData.$ext"
compile17 LayoutTransport
compile17 LayoutPaths --plugin="$build/libLayoutData.$ext"
compile17 TypeTransport --plugin="$build/libPairTypes.$ext"
compile17 CutChecks --plugin="$build/libCutValidation.$ext"
compile17 CutSemantics
compile17 StatsProof
compile17 ThirdState
compile17 ClosedSides
compile17 PairAccount
compile17 Moments
compile17 ColorAccounts
compile17 GlobalCount
compile17 K17K18
compile17 LayoutIdentity --plugin="$build/libCutData.$ext"
