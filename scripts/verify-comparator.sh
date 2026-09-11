#!/usr/bin/env bash
set -euo pipefail

# Tool revisions pinned to the ones the Palomar verifier uses, as recorded in the registry's public
# repository github.com/PalomarRegistry/PalomarSubmission at commit c605f23466450a52999fcfb3c6d68ed8febc56bf
# (read 2026-09-07). Each is a commit in the public repository cloned below.
readonly comparator_revision=575674928e239f5bc452aab72d1dd7b0f1326494
readonly exporter_revision=15f6055e299ad5b89345e533cc2192f4cc00f659
readonly nanoda_revision=68d5ca9db226849b41a6fff59d796ff19d0a8840
readonly landrun_revision=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
verifier_cache=${PALOMAR_COMPARATOR_CACHE:-"${XDG_CACHE_HOME:-$HOME/.cache}/ry-lean-verifier"}

if [[ $(uname -s) != Linux ]]; then
  echo 'Comparator verification requires Linux and the Landrun sandbox; use the verification workflow.' >&2
  exit 1
fi
for executable in git go cargo lake python3; do
  command -v "$executable" >/dev/null 2>&1 || {
    echo "Required executable is unavailable: $executable" >&2
    exit 1
  }
done

python3 - "$project_dir/comparator.json" <<'PY'
import json
import pathlib
import sys

config = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    raise SystemExit("comparator.json must explicitly enable the mandatory NanoDa replay")
allowed = {"propext", "Classical.choice", "Quot.sound"}
axioms = config.get("permitted_axioms")
if not isinstance(axioms, list) or any(not isinstance(x, str) or x not in allowed for x in axioms):
    raise SystemExit("comparator.json permits an axiom outside Palomar's standard allowlist")
if config.get("challenge_module") == config.get("solution_module"):
    raise SystemExit("Comparator requires distinct Challenge and Solution modules")
if not isinstance(config.get("theorem_names"), list) or not config["theorem_names"]:
    raise SystemExit("Comparator requires at least one theorem declaration")
PY

mkdir -p -- "$verifier_cache/bin"
verifier_cache=$(cd -- "$verifier_cache" && pwd)

checkout_tool() {
  local remote=$1 destination=$2 revision=$3
  local fresh_checkout=0
  if [[ ! -e "$destination" ]]; then
    git clone --filter=blob:none --no-checkout "$remote" "$destination"
    fresh_checkout=1
  elif [[ ! -d "$destination/.git" ]]; then
    echo "Tool cache is not a Git checkout: $destination" >&2
    exit 1
  fi
  if [[ $(git -C "$destination" remote get-url origin) != "$remote" ]]; then
    echo "Tool cache has an unexpected origin: $destination" >&2
    exit 1
  fi
  if [[ "$fresh_checkout" -eq 0 && -n $(git -C "$destination" status --porcelain --untracked-files=all) ]]; then
    echo "Tool cache has local changes: $destination; use a fresh verifier cache." >&2
    exit 1
  fi
  git -C "$destination" fetch --depth 1 origin "$revision"
  git -C "$destination" checkout --detach "$revision"
  [[ $(git -C "$destination" rev-parse HEAD) == "$revision" ]] || {
    echo "Pinned tool revision was not checked out: $destination" >&2
    exit 1
  }
}

checkout_tool https://github.com/leanprover/comparator.git "$verifier_cache/comparator" "$comparator_revision"
checkout_tool https://github.com/leanprover/lean4export.git "$verifier_cache/lean4export" "$exporter_revision"
checkout_tool https://github.com/robsimmons/nanoda_lib.git "$verifier_cache/nanoda" "$nanoda_revision"

project_toolchain=$(tr -d '[:space:]' < "$project_dir/lean-toolchain")
exporter_toolchain=$(tr -d '[:space:]' < "$verifier_cache/lean4export/lean-toolchain")
if [[ "$project_toolchain" != leanprover/lean4:v4.33.0 || "$project_toolchain" != "$exporter_toolchain" ]]; then
  echo 'The project and pinned lean4export must both use leanprover/lean4:v4.33.0.' >&2
  exit 1
fi

CGO_ENABLED=0 GOBIN="$verifier_cache/bin" \
  go install "github.com/zouuup/landrun/cmd/landrun@$landrun_revision"
(cd -- "$verifier_cache/comparator" && lake build comparator)
(cd -- "$verifier_cache/lean4export" && lake build lean4export)
cargo build --release --locked --manifest-path "$verifier_cache/nanoda/Cargo.toml"

cd -- "$project_dir"
python3 scripts/test-landrun-wrapper.py
python3 scripts/check-source.py
lake exe cache get
lake build
lake build Test.Axioms
PALOMAR_LANDRUN_REAL="$verifier_cache/bin/landrun" \
COMPARATOR_LANDRUN="$project_dir/scripts/landrun-wrapper.py" \
COMPARATOR_LEAN4EXPORT="$verifier_cache/lean4export/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$verifier_cache/nanoda/target/release/nanoda_bin" \
  lake env "$verifier_cache/comparator/.lake/build/bin/comparator" comparator.json
