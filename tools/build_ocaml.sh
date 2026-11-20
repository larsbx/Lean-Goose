#!/bin/sh
# Build the existing pinned bytecode comparison toolchain without vendoring it.
set -eu
if [ "$#" -ne 2 ]; then
  printf '%s\n' 'usage: sh tools/build_ocaml.sh /absolute/new-source /absolute/new-install' >&2
  exit 2
fi
case "$1" in /*) ;; *) printf '%s\n' 'source must be absolute' >&2; exit 2 ;; esac
case "$2" in /*) ;; *) printf '%s\n' 'install prefix must be absolute' >&2; exit 2 ;; esac
cd "$(dirname "$0")/.."
ocaml_source=$1
ocaml_install=$2
test ! -e "$ocaml_source" && test ! -e "$ocaml_install" || {
  printf '%s\n' 'source and install destinations must not already exist' >&2
  exit 2
}
python3 - "$ocaml_source" "$ocaml_install" <<'PY'
from pathlib import Path
import sys
root = Path.cwd().resolve()
paths = [Path(p).resolve() for p in sys.argv[1:]]
if paths[0] == paths[1] or any(p.is_relative_to(root) for p in paths):
    raise SystemExit("toolchain destinations must be distinct and outside this repository")
PY
ocaml_url=$(python3 -c 'import json; print(json.load(open("conformance/dependencies.json"))["ocaml"]["source_url"])')
ocaml_version=$(python3 -c 'import json; print(json.load(open("conformance/dependencies.json"))["ocaml"]["version"])')
mkdir -p "$ocaml_source"
curl --fail --silent --show-error --location --proto '=https' --tlsv1.2 \
  -o "$ocaml_source/source.tgz" "$ocaml_url"
python3 - "$ocaml_source/source.tgz" <<'PY'
import base64
import hashlib
import json
from pathlib import Path
import sys
pin = json.loads(Path("conformance/dependencies.json").read_text())["ocaml"]
actual = base64.b64encode(hashlib.sha512(Path(sys.argv[1]).read_bytes()).digest()).decode()
if actual != pin["source_sha512_base64"]:
    raise SystemExit("OCaml source archive differs from pin")
print("Pinned OCaml source verified.")
PY
tar xzf "$ocaml_source/source.tgz" --strip-components=1 -C "$ocaml_source"
(
  cd "$ocaml_source"
  ./configure --disable-native-compiler --prefix="$ocaml_install"
  make -j2 world
  make install
)
test "$("$ocaml_install/bin/ocamlc" -version)" = "$ocaml_version"
printf 'OCAMLC=%s/bin/ocamlc\n' "$ocaml_install"
