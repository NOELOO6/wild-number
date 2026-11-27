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
