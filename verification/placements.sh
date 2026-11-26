#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
mode=$3
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
native_module "$root/cases/k16/Delete.lean"
native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
plugins=(--plugin="$build/libEdgeWalk.$ext")
if [[ $mode == paired || $mode == combined ]]; then
    src="$root/cases/k16/paired-colors"
    native_module "$src/Paired.lean" -lEdgeWalk -lDelete
    pp=( "${plugins[@]}" --plugin="$build/libPaired.$ext" )
    "$lean" "${pp[@]}" -o "$build/PairedCertificate.olean" "$src/PairedCertificate.lean"
    "$lean" "${pp[@]}" "$src/NormalForm.lean"
fi
if [[ $mode == six || $mode == combined ]]; then
    src="$root/cases/k16/recoloring"
    native_module "$src/Recolor.lean" -lEdgeWalk -lDelete
    rp=( "${plugins[@]}" --plugin="$build/libRecolor.$ext" )
    "$lean" "${rp[@]}" -o "$build/PlanSound.olean" "$src/PlanSound.lean"
    "$lean" -j "${LEAN_JOBS:-4}" "${rp[@]}" -o "$build/SixRows.olean" "$src/SixRows.lean"
    "$lean" "${rp[@]}" "$src/SixProof.lean"
    "$lean" "${rp[@]}" "$src/Coordinates.lean"
    "$lean" "${rp[@]}" "$src/Example.lean"
fi
if [[ $mode == eight || $mode == combined ]]; then
    src="$root/cases/k15/eight-points"
    native_module "$src/EightPoints.lean" -lEdgeWalk -lDelete
    ep=( "${plugins[@]}" --plugin="$build/libEightPoints.$ext" )
    "$lean" "${ep[@]}" -o "$build/EightCertificate.olean" "$src/EightCertificate.lean"
    "$lean" "${ep[@]}" -o "$build/SparseEight.olean" "$src/SparseEight.lean"
    "$lean" "${ep[@]}" "$src/Examples.lean"
fi
if [[ $mode == k19 || $mode == combined ]]; then
    src="$root/cases/k19"
    native_module "$src/Rotations.lean" -lEdgeWalk -lDelete
    "$lean" "${plugins[@]}" --plugin="$build/libRotations.$ext" -o "$build/CyclicCertificate.olean" "$src/CyclicCertificate.lean"
    native_module "$src/Placement.lean"
    "$lean" --plugin="$build/libPlacement.$ext" -o "$build/PlacementCertificate.olean" "$src/PlacementCertificate.lean"
    "$lean" -o "$build/SlotBridge.olean" "$src/SlotBridge.lean"
    "$lean" "$src/ComponentUpdate.lean"
    "$lean" -o "$build/LowerBound.olean" "$src/LowerBound.lean"
    "$lean" "${plugins[@]}" --plugin="$build/libRotations.$ext" "$src/ExactRotation.lean"
    "$lean" "$src/MatchingCount.lean"
    "$lean" "$src/Repair.lean"
    python3 "$src/construct.py" --lean-out "$build/SuppliedK19.lean"
    "$lean" "${plugins[@]}" "$build/SuppliedK19.lean"
fi
