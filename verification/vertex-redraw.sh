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
names=(FourStars Outside Repair FixedSix Separation)
if [[ ${3:-stars} != stars ]]; then
    trap_src="$src/six-point-trap"
    native_module "$four/FourStars.lean" -lVertexRedraw "${core[@]}"
    native_module "$four/Outside.lean" -lFourStars -lSearchExample -lVertexRedraw "${core[@]}"
    native_module "$four/Repair.lean" -lOutside -lFourStars -lSearchExample -lVertexRedraw "${core[@]}"
    deps=(-lRepair -lOutside -lFourStars -lSearchExample -lVertexRedraw "${core[@]}")
    native_module "$four/FixedSix.lean" "${deps[@]}"
    native_module "$trap_src/SixTrap.lean" -lFixedSix "${deps[@]}"
    if [[ ${3:-} == seven-point ]]; then
        native_module "$trap_src/SixBoundary.lean" -lSixTrap -lFixedSix "${deps[@]}"
        run_lean "$trap_src/BoundaryProof.lean" "--plugin=$build/libSixBoundary.$ext"
        source "$root/verification/seven-point.sh"
        exit 0
    fi
    run_lean "$trap_src/SixTrapCounts.lean" "--plugin=$build/libSixTrap.$ext"
    run_lean "$trap_src/TwoExceptions.lean" "--plugin=$build/libSixTrap.$ext"
    native_module "$trap_src/SixBoundary.lean" -lSixTrap -lFixedSix "${deps[@]}"
    run_lean "$trap_src/SixBoundaryCounts.lean" "--plugin=$build/libSixBoundary.$ext"
    run_lean "$trap_src/BoundaryProof.lean" "--plugin=$build/libSixBoundary.$ext"
    run_lean "$trap_src/SixBoundaryResult.lean" "--plugin=$build/libSixBoundary.$ext"
    native_module "$trap_src/OutsidePatterns.lean" -lSixBoundary -lSixTrap -lFixedSix "${deps[@]}"
    run_lean "$trap_src/PatternChecks.lean" "--plugin=$build/libOutsidePatterns.$ext"
    run_lean "$trap_src/PatternProof.lean" "--plugin=$build/libOutsidePatterns.$ext"
    native_module "$trap_src/LastNineteen.lean" -lSixTrap -lFixedSix "${deps[@]}"
    run_lean "$trap_src/TwoColors.lean" "--plugin=$build/libLastNineteen.$ext"
    if [[ ${3:-} == six-point-trap ]]; then exit 0; fi
    if [[ ${3:-} == all ]]; then source "$root/verification/seven-point.sh"; fi
    names=(Separation)
fi
for name in "${names[@]}"; do
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
