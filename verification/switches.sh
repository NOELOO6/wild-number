#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
native_module "$root/cases/k15/Seven.lean"
native_module "$root/cases/k16/two-color-switch/Switches.lean" -lSeven
"$lean" --plugin="$build/libSeven.$ext" --plugin="$build/libSwitches.$ext" \
    "$root/cases/k16/two-color-switch/CheckSwitch.lean"
"$lean" "$root/cases/k16/seven-deletions/MovedSeven.lean"
"$lean" "$root/cases/k16/seven-deletions/Example.lean"
native_module "$root/cases/k15/moment-test/FailureCounts.lean"
"$lean" --plugin="$build/libFailureCounts.$ext" "$root/cases/k15/moment-test/CheckMoments.lean"
