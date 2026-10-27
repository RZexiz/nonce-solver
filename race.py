#!/usr/bin/env python3
"""race.py — NONCE solver portfolio for mesin 2 (4 cores).

Usage: race.py clauses.json budget_seconds
Runs 3 workers in parallel (1 core each, v3 uses 2):
  A: solver.py MV + probSAT beta 4.0
  B: solver.py MV + probSAT beta 2.6
  C: nonce_solver_v3.py (cd195/Kissat/probSAT waves, max 2 procs)
First worker to produce a verified SAT assignment wins; prints BITS:<bits>
and WINNER:<name>. Exits nonzero if none solves within budget.
All workers are killed once a winner is verified.
"""
import json, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
VENV_PY = "/home/ubuntu/nonce-venv/bin/python"


def verify(clauses, bits):
    if len(bits) != max(abs(l) for cl in clauses for l in cl):
        return False
    assign = {i + 1: (bits[i] == "1") for i in range(len(bits))}
    return all(any((l > 0) == assign[abs(l)] for l in cl) for cl in clauses)


def main():
    clauses_path, budget = sys.argv[1], int(sys.argv[2])
    clauses = json.load(open(clauses_path))
    n_vars = max(abs(l) for cl in clauses for l in cl)
    print(f"race: {n_vars} vars, {len(clauses)} clauses, budget={budget}s",
          flush=True)
    env = dict(os.environ, NONCE_PY=VENV_PY)
    procs = {}
    logs = {}
    # A: MV+probSAT beta 4.0 (stdout log, BITS: line on SAT)
    logs["A"] = open("race_A.log", "w")
    procs["A"] = subprocess.Popen(
        [VENV_PY, os.path.join(HERE, "solver.py"), clauses_path,
         str(budget), "4.0"],
        stdout=logs["A"], stderr=subprocess.DEVNULL)
    # B: MV+probSAT beta 2.6
    logs["B"] = open("race_B.log", "w")
    procs["B"] = subprocess.Popen(
        [VENV_PY, os.path.join(HERE, "solver.py"), clauses_path,
         str(budget), "2.6"],
        stdout=logs["B"], stderr=subprocess.DEVNULL)
    # C: v3 portfolio, result to file
    if os.path.exists("race_C.bits"):
        os.unlink("race_C.bits")
    logs["C"] = open("race_C.log", "w")
    procs["C"] = subprocess.Popen(
        [VENV_PY, os.path.join(HERE, "v3", "nonce_solver_v3.py"),
         clauses_path, str(budget), "--out", "race_C.bits"],
        stdout=logs["C"], stderr=subprocess.DEVNULL, env=env)
    deadline = time.time() + budget
    winner = None
    while time.time() < deadline:
        # C: file-based result
        if os.path.exists("race_C.bits"):
            bits = open("race_C.bits").read().strip()
            if bits and verify(clauses, bits):
                winner = ("C", bits)
                break
        # A/B: scan logs for RESULT unsat=0 + BITS:
        for name in ("A", "B"):
            try:
                txt = open(f"race_{name}.log").read()
            except OSError:
                continue
            if "RESULT unsat=0" in txt:
                for line in txt.splitlines():
                    if line.startswith("BITS:"):
                        bits = line[5:].strip()
                        if bits and verify(clauses, bits):
                            winner = (name, bits)
                            break
            if winner:
                break
        if winner:
            break
        if all(p.poll() is not None for p in procs.values()):
            break
        time.sleep(2)
    for p in procs.values():
        if p.poll() is None:
            p.kill()
    for f in logs.values():
        f.close()
    if winner:
        print(f"WINNER:{winner[0]}", flush=True)
        print(f"BITS:{winner[1]}", flush=True)
        return 0
    print("RACE UNSOLVED", flush=True)
    return 1


if __name__ == "__main__":
    sys.exit(main())
