#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
src="$root/cases/k15"
four="$src/vertex-redraw"
three="$src/three-stars"
native_module "$root/cases/k16/Delete.lean"
native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
native_module "$src/Teams.lean"
native_module "$src/five-colors/WeightedSurvivor.lean" -lTeams
native_module "$root/examples/SearchExample.lean"
core=(-lWeightedSurvivor -lTeams -lEdgeWalk -lDelete)
native_module "$four/VertexRedraw.lean" "${core[@]}"
run_lean() {
    local source=$1
    shift
    "$lean" --root="$(dirname "$source")" -j "${LEAN_JOBS:-3}" -s 65536 "$@" \
        -o "$build/$(basename "$source" .lean).olean" "$source"
}
for name in FourStars Outside Repair FixedSix Separation; do
    run_lean "$four/$name.lean" "--plugin=$build/libVertexRedraw.$ext" "--plugin=$build/libSearchExample.$ext"
done
native_module "$three/ThreeStars.lean" -lVertexRedraw "${core[@]}"
run_lean "$three/StarRows.lean" "--plugin=$build/libThreeStars.$ext"
run_lean "$three/StarTypes.lean" "--plugin=$build/libThreeStars.$ext"
native_module "$three/CutLedger.lean" -lThreeStars -lVertexRedraw "${core[@]}"
native_module "$three/StarGeometry.lean" -lCutLedger -lThreeStars -lVertexRedraw "${core[@]}"
run_lean "$three/GeometryRows.lean" "--plugin=$build/libStarGeometry.$ext"
run_lean "$three/StarBounds.lean" "--plugin=$build/libThreeStars.$ext"
run_lean "$three/AllStars.lean"
run_lean "$three/RestoreRoot.lean"
