#!/bin/bash
# Fast builds: the OneDrive checkout is slow to read from WSL (~7 min per Mathlib-importing file),
# so we keep a copy of the project (including .lake) on the WSL filesystem at ~/heliod-mirror.
# This script syncs the Lean sources there and builds.  Run from Windows Git Bash with:
#   MSYS_NO_PATHCONV=1 wsl bash -l /mnt/c/.../lean/scripts/mirror-build.sh [Heliod/File.lean]
# With an argument, builds just that module *and any stale dependencies* (`lake build Heliod.File`);
# without, runs the default `lake build`.  (Do not use `lake env lean File.lean` for checking: it
# uses the existing .olean files of the imports, which may be stale.)
# One-time setup:  cp -r <lean>/.lake ~/heliod-mirror/   (about 7 GB)
SRC=/mnt/c/Users/msurb/OneDrive/CSC/UMD/projects/ara-typestate/lean
DST=$HOME/heliod-mirror
rm -rf "$DST/Heliod"
cp -r "$SRC/Heliod" "$SRC/Heliod.lean" "$SRC/lakefile.toml" "$SRC/lean-toolchain" "$SRC/lake-manifest.json" "$DST/"
cd "$DST" || exit 1
if [ -n "$1" ]; then
  mod=$(echo "${1%.lean}" | tr '/' '.')
  lake build "$mod" 2>&1 | grep -v "module system" | grep -v "^trace"
else
  lake build 2>&1 | grep -v "module system" | grep -v "^trace"
fi
