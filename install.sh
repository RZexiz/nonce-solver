#!/bin/bash
# install.sh — NONCE solver stack on mesin 2 (runs as root via board task).
# Downloads this bundle from the public repo, builds everything, smoke-tests.
set -e
REPO_RAW="https://raw.githubusercontent.com/RZexiz/nonce-solver/main"
DIR="/home/ubuntu/nonce-solver"
VENV="/home/ubuntu/nonce-venv"
echo "== deps =="
command -v gcc >/dev/null || apt-get install -y gcc
command -v python3 >/dev/null || apt-get install -y python3 python3-venv
command -v git >/dev/null || apt-get install -y git
echo "== download bundle =="
mkdir -p "$DIR/v3"
cd "$DIR"
for f in solver.py probsab_focus.c race.py attempt_solve.sh; do
  curl -sL "$REPO_RAW/$f" -o "$f"
done
for f in nonce_solver_v3.py probsab.c gen_ksat.py; do
  curl -sL "$REPO_RAW/v3/$f" -o "v3/$f"
done
chmod +x race.py attempt_solve.sh
echo "== venv + pysat =="
python3 -m venv "$VENV" 2>/dev/null || true
"$VENV/bin/pip" install -q python-sat
echo "== build probsab binaries =="
gcc -O3 -march=native -o "$DIR/probsab_focus" "$DIR/probsab_focus.c" -lm
gcc -O3 -march=native -o "$DIR/v3/probsab" "$DIR/v3/probsab.c" -lm
echo "== kissat (optional engine for v3) =="
if [ ! -x /home/ubuntu/my-solver/kissat/build/kissat ]; then
  rm -rf /tmp/kissat-build && git clone -q https://github.com/arminbiere/kissat /tmp/kissat-build
  (cd /tmp/kissat-build && ./configure -q && make -q -j4) || echo "kissat build FAILED (continuing without it)"
  mkdir -p /home/ubuntu/my-solver/kissat/build
  cp /tmp/kissat-build/build/kissat /home/ubuntu/my-solver/kissat/build/kissat 2>/dev/null || echo "kissat binary not found"
fi
ls -la /home/ubuntu/my-solver/kissat/build/kissat 2>/dev/null || echo "no kissat"
echo "== smoke test: planted 5-SAT 384v/8448c r22, race budget 120s =="
cd "$DIR"
python3 v3/gen_ksat.py 384 8448 5 7 smoke384.json
timeout 150 "$VENV/bin/python" race.py smoke384.json 120 | tail -3
echo "== install done =="
ls -la "$DIR" "$DIR/v3"
