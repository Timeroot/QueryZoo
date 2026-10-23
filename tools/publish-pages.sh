#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
python3 -u build.py --strict
python3 -u tests/run.py

publish_dir=$(mktemp -d "${TMPDIR:-/tmp}/query-zoo-pages.XXXXXXXX")
trap 'rm -rf "$publish_dir"' EXIT
remote=$(git remote get-url origin)

if git ls-remote --exit-code --heads "$remote" gh-pages >/dev/null; then
  git clone --quiet --single-branch --branch gh-pages "$remote" "$publish_dir"
else
  git -C "$publish_dir" init --quiet --initial-branch=gh-pages
  git -C "$publish_dir" remote add origin "$remote"
fi

# Keep the branch history while replacing only generated files.
python3 - "$publish_dir" <<'PY'
from pathlib import Path
import shutil
import sys

target = Path(sys.argv[1])
for item in target.iterdir():
    if item.name == '.git':
        continue
    if item.is_dir():
        shutil.rmtree(item)
    else:
        item.unlink()
shutil.copytree('site', target, dirs_exist_ok=True)
(target / '.nojekyll').touch()
PY

git -C "$publish_dir" add --all
if git -C "$publish_dir" diff --cached --quiet; then
  echo 'The published site is already up to date.'
else
  revision=$(git rev-parse --short HEAD)
  git -C "$publish_dir" -c user.name="$(git config user.name)" \
    -c user.email="$(git config user.email)" \
    commit --quiet -m "Build QueryZoo from $revision"
  git -C "$publish_dir" push --quiet origin gh-pages
fi
