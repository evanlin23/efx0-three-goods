#!/bin/bash
# Installs the Python dependencies, nauty (genbg enumerates the cores) and the Lean toolchain pinned in
# lean/lean-toolchain for Claude Code on the web sessions, so the checkers, search tools and lean/check.sh run.
set -euo pipefail
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi
cd "$CLAUDE_PROJECT_DIR"
python3 -m pip install --quiet --disable-pip-version-check -r requirements.txt
if ! command -v genbg >/dev/null && ! command -v nauty-genbg >/dev/null; then
  { apt-get install -y -q nauty >/dev/null 2>&1 || { apt-get update -q >/dev/null 2>&1 && apt-get install -y -q nauty >/dev/null 2>&1; }; } \
    || echo "session-start: could not install nauty; frontier.py needs genbg (or --enum=python)" >&2
fi
# Lean (core only, lean/): elan fetches toolchains from release.lean-lang.org; where that host is blocked,
# download the same release from GitHub and register it with elan under its official name.
if [ -f lean/lean-toolchain ]; then
  export PATH="$HOME/.elan/bin:$PATH"
  command -v elan >/dev/null || curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none >/dev/null 2>&1 || echo "session-start: could not install elan" >&2
  tc=$(tr -d '[:space:]' < lean/lean-toolchain)
  if command -v elan >/dev/null && ! elan toolchain list 2>/dev/null | grep -qF "$tc"; then
    if ! elan toolchain install "$tc" >/dev/null 2>&1; then
      v=${tc##*:v}
      command -v unzstd >/dev/null || apt-get install -y -q zstd >/dev/null 2>&1 || true
      mkdir -p "$HOME/.elan-github"
      tarball="$HOME/.elan-github/lean-$v-linux.tar.zst"
      { curl -sSfL --retry 4 --retry-all-errors -o "$tarball" \
          "https://github.com/leanprover/lean4/releases/download/v$v/lean-$v-linux.tar.zst" \
        && tar --use-compress-program=unzstd -xf "$tarball" -C "$HOME/.elan-github" \
        && rm -f "$tarball" \
        && elan toolchain link "$tc" "$HOME/.elan-github/lean-$v-linux"; } \
        || echo "session-start: could not install Lean $tc" >&2
    fi
  fi
  if [ -n "${CLAUDE_ENV_FILE:-}" ]; then echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"; fi
fi
