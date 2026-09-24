#!/bin/bash
# Installs the Python dependencies and nauty (genbg enumerates the cores) for Claude Code on the web sessions,
# so the checkers and search tools run.
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
