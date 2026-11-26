#!/usr/bin/env bash
set -euo pipefail
lean=$1
build=$2
root=$(cd "$(dirname "$0")/.." && pwd)
source "$root/verification/native.sh"
native_module "$root/cases/k16/Delete.lean"
native_module "$root/cases/k19/EdgeWalk.lean" -lDelete
native_module "$root/examples/SearchExample.lean"
src="$root/cases/k16/search-redraw"
native_module "$src/SearchRedraw.lean" -lSearchExample -lEdgeWalk -lDelete
plugin="--plugin=$build/libSearchRedraw.$ext"
for name in RedrawRows RedrawGraph RedrawNames; do
  "$lean" --root="$src" "$plugin" -j "${LEAN_JOBS:-4}" -s 65536 -o "$build/$name.olean" "$src/$name.lean"
done
