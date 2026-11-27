#!/usr/bin/env bash
# Reuse the checked nine-point obstruction theorem in the K13 graph argument.
source "$root/verification/nine-points.sh"
native_module "$exact/ThirteenData.lean" -lNineData
for name in Anchors GroupingTools FourAnchor NineBounds Thirteen; do
  compile "$name"
done
"$lean" --root="$exact" --plugin="$build/libThirteenData.$ext" -s 65536 \
  -o "$build/K13K14.olean" "$exact/K13K14.lean"
