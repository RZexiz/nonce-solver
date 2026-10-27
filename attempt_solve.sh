#!/bin/bash
# attempt_solve.sh — one-shot solver for a live NONCE attempt on mesin 2.
# Usage: attempt_solve.sh <clauses_json_url> <budget_seconds>
# Downloads the clause file, runs the portfolio race, prints BITS on success.
set -e
URL="$1"
BUDGET="$2"
DIR="/home/ubuntu/nonce-solver"
cd "$DIR"
curl -sL "$URL" -o attempt_clauses.json
ls -la attempt_clauses.json
"/home/ubuntu/nonce-venv/bin/python" race.py attempt_clauses.json "$BUDGET"
