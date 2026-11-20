#!/bin/sh
# The canonical auditor remains external and is verified before execution.
set -eu
if [ "$#" -gt 1 ]; then
  printf '%s\n' 'usage: sh tools/estate-audit.sh [absolute-path-to-pinned-auditor]' >&2
  exit 2
fi
cd "$(dirname "$0")/.."
rev=$(python3 -c 'import tomllib; print(next(d["rev"] for d in tomllib.load(open("ESTATE.toml", "rb"))["dep"] if d["id"] == "estate-governance"))')
pin=$(python3 -c 'import tomllib; print(next(d["pin"] for d in tomllib.load(open("ESTATE.toml", "rb"))["dep"] if d["id"] == "estate-governance"))')
python3 - "$rev" "$pin" <<'PY'
import re
import sys
if not re.fullmatch(r"[0-9a-f]{40}", sys.argv[1]):
    raise SystemExit("invalid governance revision")
if not re.fullmatch(r"sha256:[0-9a-f]{64}", sys.argv[2]):
    raise SystemExit("invalid governance auditor pin")
PY
audit=$(mktemp)
trap 'rm -f "$audit"' EXIT
if [ "$#" -eq 1 ]; then
  cp "$1" "$audit"
else
  curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
    --output "$audit" "https://raw.githubusercontent.com/larsbx/estate-governance/$rev/kernel/audit_estate_layout.py"
fi
printf '%s  %s\n' "${pin#sha256:}" "$audit" | sha256sum --check --strict -
python3 "$audit" --root .
