# Sourced after the fixed-six graph checker has been built.
seven_src="$src/seven-point"
seven_build="$build/seven-point"
mkdir -p "$seven_build"
native_module "$trap_src/BoundaryOptions.lean" -lSixBoundary -lSixTrap -lFixedSix "${deps[@]}"
native_module "$trap_src/CrossBoundary.lean" -lBoundaryOptions -lSixBoundary -lSixTrap -lFixedSix "${deps[@]}"
run_lean "$trap_src/CrossCheck.lean" "--plugin=$build/libCrossBoundary.$ext"
run_lean "$trap_src/CrossResult.lean"
native_module "$trap_src/KeepTwoScan.lean" -lCrossBoundary -lBoundaryOptions -lSixBoundary -lSixTrap -lFixedSix "${deps[@]}"
run_lean "$trap_src/KeepTwoCheck.lean" "--plugin=$build/libKeepTwoScan.$ext"
run_lean "$trap_src/KeepTwo.lean"
run_lean "$trap_src/Replacement.lean" "--plugin=$build/libSixTrap.$ext"
run_lean "$trap_src/FifteenRecord.lean" "--plugin=$build/libSixTrap.$ext"
run_lean "$trap_src/SparseRecord.lean" "--plugin=$build/libSixTrap.$ext"

native_module "$three/ThreeStars.lean" -lVertexRedraw "${core[@]}"
native_module "$three/CutLedger.lean" -lThreeStars -lVertexRedraw "${core[@]}"
native_module "$three/StarGeometry.lean" -lCutLedger -lThreeStars -lVertexRedraw "${core[@]}"
seven_deps=(-lStarGeometry -lCutLedger -lThreeStars -lFixedSix "${deps[@]}")
native_module "$trap_src/SevenProfile.lean" "${seven_deps[@]}"
run_lean "$trap_src/SevenProfileCheck.lean" "--plugin=$build/libSevenProfile.$ext"
native_module "$trap_src/SevenBalance.lean" -lSevenProfile "${seven_deps[@]}"
run_lean "$trap_src/SevenBalanceCheck.lean" "--plugin=$build/libSevenBalance.$ext"
run_lean "$trap_src/SevenNear.lean"

cp "$seven_src/"*.lean "$seven_src/groups.txt" "$seven_build/"
for data in blocker.cnf blocker.vars hints.txt; do
    gzip -dc "$seven_src/$data.gz" > "$seven_build/$data"
done
native_module "$seven_build/RedrawModel.lean" -lBoundaryOptions -lSixBoundary -lSixTrap -lFixedSix "${deps[@]}"
run_lean "$seven_build/RedrawChecks.lean" "--plugin=$build/libRedrawModel.$ext"
run_lean "$seven_build/RedrawSound.lean"
run_lean "$seven_build/CertifiedRedraw.lean"
cp "$seven_src/InsideNames.lean" "$seven_src/OutsideNames.lean" "$seven_src/ReplayRedraw.lean" "$seven_build/"
run_lean "$seven_build/InsideNames.lean"
run_lean "$seven_build/OutsideNames.lean"
cadical_bin=${CADICAL:-"$(dirname "$lean")/cadical"}
if [[ ! -x $cadical_bin ]]; then cadical_bin=$(command -v cadical); fi
solver_status=0
"$cadical_bin" -q --lrat "$seven_build/blocker.cnf" "$seven_build/blocker.lrat" || solver_status=$?
if [[ $solver_status != 20 ]]; then
    echo "CaDiCaL did not certify unsatisfiability (exit $solver_status)." >&2
    exit 1
fi
"$lean" "--plugin=$build/libRedrawModel.$ext" --run "$seven_build/ReplayRedraw.lean" "$seven_build/blocker.lrat"

for data in exterior-prices.txt exterior-repairs.txt; do
    gzip -dc "$seven_src/$data.gz" > "$seven_build/$data"
done
native_module "$seven_build/ExteriorRows.lean" -lBoundaryOptions -lSixBoundary -lSixTrap "${seven_deps[@]}"
run_lean "$seven_build/ExteriorChecks.lean" "--plugin=$build/libExteriorRows.$ext"
run_lean "$seven_build/ExteriorSound.lean"
native_module "$seven_build/ExteriorStars.lean" -lExteriorRows -lBoundaryOptions -lSixBoundary -lSixTrap "${seven_deps[@]}"
run_lean "$seven_build/ExteriorStarCheck.lean" "--plugin=$build/libExteriorStars.$ext"
run_lean "$seven_build/ExteriorEligibility.lean" "--plugin=$build/libExteriorStars.$ext"
cp "$seven_src/WorkedStar.lean" "$seven_src/one-outside-change.txt" "$seven_build/"
run_lean "$seven_build/WorkedStar.lean"
run_lean "$seven_build/SevenOutside.lean"
cp "$seven_src/ending-drawings.txt" "$seven_build/"
run_lean "$seven_build/EndingChoice.lean" "--plugin=$build/libSixTrap.$ext"
