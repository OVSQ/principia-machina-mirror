#!/usr/bin/env bash
# docs_lint.sh - the naming policy's mechanical part (docs/design/pma_naming_policy.md).
#   1. No version suffix (_N_N_N.) in any file name under docs/ or vectors/, docs/v1/ excepted.
#   2. Every document under docs/ (docs/v1/, the phase files docs/progress/phase-N.md, the
#      nightly runs table docs/progress/runs.md and its fragments docs/progress/runs/<date>.md, the
#      landing fragments docs/progress/landing/<task>.md and README.md files excepted)
#      opens with YAML front matter whose name equals the file's stem, whose version is
#      SemVer and whose date is ISO 8601, and ends with "END OF ARTIFACT --- <name>".
#   3. The two machine tables equal their render from ops/machines/machines.json
#      (ops/machines/render_table.py --check): a hand edit is made in machines.json instead.
# Exit 0 clean, 1 on any finding; every finding names its file.
set -u
cd "$(git rev-parse --show-toplevel)" || exit 1
bad=0
while IFS= read -r -d '' f; do
  case "$f" in docs/v1/*) continue ;; esac
  if printf '%s' "$(basename "$f")" | grep -q -E '_[0-9]+_[0-9]+_[0-9]+\.'; then
    echo "docs lint: version suffix in file name: $f"; bad=$((bad + 1))
  fi
done < <(git ls-files -z -- docs vectors)
while IFS= read -r -d '' f; do
  case "$f" in docs/v1/*|docs/progress/phase-*.md|docs/progress/landing/*.md|docs/progress/runs/*.md|docs/progress/runs.md|*/README.md) continue ;; esac
  stem="$(basename "$f" .md)"
  if [ "$(sed -n 1p "$f")" != "---" ]; then
    echo "docs lint: no front matter: $f"; bad=$((bad + 1)); continue
  fi
  fm="$(awk 'NR==1{next} /^---$/{exit} {print}' "$f")"
  name="$(printf '%s\n' "$fm" | sed -n 's/^name:[[:space:]]*//p' | head -1)"
  version="$(printf '%s\n' "$fm" | sed -n 's/^version:[[:space:]]*//p' | head -1)"
  date="$(printf '%s\n' "$fm" | sed -n 's/^date:[[:space:]]*//p' | head -1)"
  [ "$name" = "$stem" ] || { echo "docs lint: name '$name' is not the stem '$stem': $f"; bad=$((bad + 1)); }
  printf '%s' "$version" | grep -q -E '^[0-9]+\.[0-9]+\.[0-9]+$' || { echo "docs lint: version not SemVer: $f"; bad=$((bad + 1)); }
  printf '%s' "$date" | grep -q -E '^[0-9]{4}-[0-9]{2}-[0-9]{2}$' || { echo "docs lint: date not ISO 8601: $f"; bad=$((bad + 1)); }
  last="$(awk 'NF{l=$0} END{print l}' "$f")"
  [ "$last" = "END OF ARTIFACT --- $stem" ] || { echo "docs lint: sentinel missing or wrong: $f"; bad=$((bad + 1)); }
done < <(git ls-files -z -- 'docs/*.md' 'docs/**/*.md')
# 3. The two machine tables equal their render from ops/machines/machines.json.
if ! out="$(python3 -I ops/machines/render_table.py --check 2>&1)"; then
  echo "docs lint: $out"; bad=$((bad + 1))
fi
if [ "$bad" -gt 0 ]; then echo "docs lint: $bad finding(s)"; exit 1; fi
echo "docs lint: clean"
