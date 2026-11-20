#!/bin/sh
# Fetch and build the pinned compiler outside the governed source tree.
set -eu
if [ "$#" -ne 1 ]; then
  printf '%s\n' 'usage: sh tools/build_goose.sh /absolute/path/to/new-goose-checkout' >&2
  exit 2
fi
case "$1" in /*) ;; *) printf '%s\n' 'destination must be absolute' >&2; exit 2 ;; esac
cd "$(dirname "$0")/.."
goose_destination=$1
test ! -e "$goose_destination" || {
  printf '%s\n' 'destination already exists; use GOOSE_SOURCE for an existing pinned checkout' >&2
  exit 2
}
python3 - "$goose_destination" <<'PY'
from pathlib import Path
import sys
if Path(sys.argv[1]).resolve().is_relative_to(Path.cwd().resolve()):
    raise SystemExit("compiler source must stay outside this repository")
PY
goose_repository=$(python3 -c 'import json; print(json.load(open("conformance/dependencies.json"))["goose"]["repository"])')
goose_revision=$(python3 -c 'import json; print(json.load(open("conformance/dependencies.json"))["goose"]["revision"])')
git clone --no-checkout "$goose_repository" "$goose_destination"
git -C "$goose_destination" checkout --detach "$goose_revision"
python3 - "$goose_destination" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys
pin = json.loads(Path("conformance/dependencies.json").read_text())["goose"]
source = Path(sys.argv[1])
revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
if revision != pin["revision"]:
    raise SystemExit("Goose revision differs from pin")
archive = subprocess.check_output(["git", "archive", "--format=tar", revision], cwd=source)
if hashlib.sha256(archive).hexdigest() != pin["archive_sha256"]:
    raise SystemExit("Goose source archive differs from pin")
print("Pinned Goose source verified.")
PY
cmake -S "$goose_destination" -B "$goose_destination/build" -DCMAKE_BUILD_TYPE=Release
cmake --build "$goose_destination/build" -j2
printf 'GOOSE_SOURCE=%s\n' "$goose_destination"
