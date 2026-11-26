#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
src="$root/cases/k15/prescribed"
native_module "$src/Prescribed.lean"
plugin="--plugin=$build/libPrescribed.$ext"
"$lean" -o "$build/Incidence.olean" "$root/cases/k17/Incidence.lean"
"$lean" -j "${LEAN_JOBS:-3}" "$plugin" -o "$build/PrescribedRows.olean" "$src/PrescribedRows.lean"
"$lean" "$plugin" "$src/PrescribedProof.lean"
