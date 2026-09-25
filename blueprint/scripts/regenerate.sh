#!/usr/bin/env bash
# Regenerate blueprint/src from DeGiorgi_Lean_to_Tex.tex and the Lean sources.
# WARNING: this overwrites blueprint/src, including any manual edits.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
rm -rf "$ROOT/blueprint/src"
python3 "$ROOT/blueprint/scripts/convert.py" "$ROOT" "$ROOT/blueprint/src"
python3 "$ROOT/blueprint/scripts/assemble.py" "$ROOT/blueprint"
mv "$ROOT/blueprint/src/_report.json" "$ROOT/blueprint/scripts/conversion_report.json"
echo "Done. Build with: leanblueprint pdf && leanblueprint web && leanblueprint checkdecls"
