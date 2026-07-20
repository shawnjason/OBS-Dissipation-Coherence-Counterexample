#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

# Clean only this project's generated outputs. `lake clean` also removes
# dependency build caches and would force an unnecessary Mathlib source build.
project_root="$(pwd -P)"
project_build="$project_root/.lake/build"
if [[ "$project_build" != "$project_root/.lake/build" ||
      "$project_build" == "/.lake/build" ]]; then
  echo "Refusing to clean unexpected build path: $project_build" >&2
  exit 1
fi
rm -rf -- "$project_build"

{
  printf 'OS: '
  . /etc/os-release
  printf '%s %s (%s)\n' "$PRETTY_NAME" "$(uname -m)" "$(uname -sr)"
  lean --version
  lake --version
  elan --version
  printf 'Toolchain: '
  tr -d '\r\n' < lean-toolchain
  printf '\n'
  printf 'Mathlib revision: '
  if [[ -f lake-manifest.json ]]; then
    python3 - <<'PY'
import json
data = json.load(open('lake-manifest.json', encoding='utf-8'))
for package in data.get('packages', []):
    if package.get('name') == 'mathlib':
        print(package.get('rev', package.get('inputRev', 'unknown')))
        break
else:
    print('not found')
PY
  else
    printf 'lake-manifest.json not generated\n'
  fi
  printf 'Build command: remove project .lake/build only, then lake build\n'
} > LEAN_ENVIRONMENT.txt

if grep -RInE --include='*.lean' '\b(sorry|admit|axiom|unsafe|native_decide)\b' OBS; then
  echo 'Forbidden proof bypass token found in project source.' >&2
  exit 1
fi

lake build 2>&1 | tee BUILD_TRANSCRIPT.txt
