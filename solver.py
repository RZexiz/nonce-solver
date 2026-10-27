#!/usr/bin/env python3
"""
NONCE SAT solver — MV + probSAT pipeline (default), BP kept as legacy path.

Live benchmark parameters MUST be read from protocol_info + fragments at
attempt time (they rotate: observed sat4-1536 with 12288 4-lit clauses, and
balanced-1536 with 33792 5-lit clauses). This module takes clauses as input
and never hardcodes a benchmark shape.

2026-10-27 FINDINGS (5-SAT, ratio 22 — above the random 5-SAT threshold
~21.1, the hardest regime; planted solutions there are isolated):
  * BP is FALSIFIED at ratio 22: fixed damping 0.5, adaptive damping,
    reinforcement, and BP+decimation all fail. q-weights oscillate in an
    exact 3-cycle (max-delta 3.45 -> 0.89 -> 0.223 -> repeat) and never
    converge; uniform-weights converge to a useless fixed point (241
    unsat on test-384); BP decimation contradicts after fixing only
    28-126 vars; BP initialized from a good start is pulled back to the
    same wrong fixed point.
  * Survey propagation is FALSIFIED too: it converges but its biases are
    anti-correlated with the planted assignment on uniform-planted
    instances (corr 0.331 vs majority-vote 0.646), and SP+decimation
    contradicts after ~44 fixed vars.
  * The one real signal at ratio 22 is MAJORITY VOTE: it exploits the
    planting sign bias (uniform-planted corr 0.646; q-hidden-planted
    INVERTED corr ~0.951). Direction must be chosen by measured unsat,
    never assumed — the live benchmark's planting model is unknown.
  * MV + probSAT (C, Balint & Schoening style) is the working pipeline,
    BUT the beta parameter is decisive: beta 2.6 (tuned for r18) STALLS
    at ratio 22 (test-384 best 21 unsat across 300 s probSAT + 480 s
    ILS; live 1536v MV 682 unsat, 300 s no solve), while beta 4.0
    SOLVES test-384 in 0.8 s / 1.26M flips (verified unsat=0, three
    seeds) and takes confirmed uniform-planted 384v/r22 from MV 164 to
    2 unsat in 60 s. The parent's qhidden-style 384v/r22 instance goes
    68 -> SAT in 422 flips (~0 s) at beta 2.6; the r18 instance solves
    in ~0.5 s. An exact DPLL finish from a 21-unsat incumbent fails
    (residual UNSAT by propagation alone — the incumbent's fixed part
    contains errors), so DPLL is NOT part of the pipeline.
  * Verdict: this solver IS ready for a live ratio-22 attempt at beta
    4.0 (default). It solves 384v/r22 uniformly-planted instances in
    ~1 s and qhidden-style instances instantly. Live 1536v at beta 4.0
    is the one remaining unproven scale (tested 2026-10-27, see report).
    Failed attempts do not consume mint quota, so a live attempt is a
    free lottery even if 1536v proves harder.

Default pipeline (solve):
  1. majority-vote start (both directions, lower unsat wins);
  2. focused probSAT (C binary, no random restarts) from that start;
  3. iterated local search: perturb the incumbent by k random flips and
     re-run focused probSAT, adopting strict improvements, until the
     time budget is exhausted.
  Legacy BP path remains available as solve_bp() / --method bp.
"""
import random
import math
import sys
import os
import json
import subprocess
import time

Q = 0.618


def build_weights(k):
    w = [Q ** j for j in range(k + 1)]
    w[0] = (Q ** k) * 0.01
    return w


def bp_solve(clauses, n_vars, seed=0, damping=0.5, max_iter=400,
             tol=1e-4, verbose=False):
    """clauses: list of lists of ints, +v means var v true, -v means false
    (1-based vars). Returns (assignment list of 0/1, n_unsat, iters)."""
    rng = random.Random(seed)
    k = len(clauses[0]) if clauses else 0
    w = build_weights(k)
    # var -> list of (clause_idx, sign) ; sign=+1 if literal is +v
    var_clauses = [[] for _ in range(n_vars + 1)]
    for ci, cl in enumerate(clauses):
        for lit in cl:
            var_clauses[abs(lit)].append((ci, 1 if lit > 0 else -1))
    # messages: var->factor as log-odds (belief var=1 minus var=0), init small random
    # store per (clause, position) the incoming var message excluding that factor
    # We keep m_vf[(ci, pos)] = log-odds from var to factor
    m_vf = {}
    for ci, cl in enumerate(clauses):
        for pos in range(len(cl)):
            m_vf[(ci, pos)] = rng.uniform(-0.1, 0.1)
    # factor->var messages as log-odds
    m_fv = {}
    for ci, cl in enumerate(clauses):
        for pos in range(len(cl)):
            m_fv[(ci, pos)] = 0.0

    def beliefs(exclude_ci=None, exclude_pos=None):
        # returns list (1-based) of total log-odds per var
        bel = [0.0] * (n_vars + 1)
        for ci, cl in enumerate(clauses):
            for pos in range(len(cl)):
                if ci == exclude_ci and pos == exclude_pos:
                    continue
                v = abs(cl[pos])
                bel[v] += m_fv[(ci, pos)] * (1 if cl[pos] > 0 else -1)
        return bel

    for it in range(1, max_iter + 1):
        max_delta = 0.0
        # factor -> var updates
        for ci, cl in enumerate(clauses):
            kk = len(cl)
            for pos in range(kk):
                v = abs(cl[pos])
                sign = 1 if cl[pos] > 0 else -1
                # enumerate assignments of the other literals
                others = [(p, abs(cl[p]), 1 if cl[p] > 0 else -1)
                          for p in range(kk) if p != pos]
                # prob of other literal being true under current messages
                # m_vf of other var (excluding this factor) -> P(var=1)
                probs = []
                for (p, ov, osign) in others:
                    lo = m_vf[(ci, p)]
                    p1 = 1.0 / (1.0 + math.exp(-lo))  # P(var=1)
                    probs.append(p1 if osign > 0 else 1.0 - p1)
                # factor message for var=1 vs var=0:
                # if var literal true -> clause satisfied regardless of others
                #   (j includes this literal) ; else j = #true among others
                # sum over other assignments: prod probs, weight w[j]
                s_true = 0.0   # this literal true -> j = 1 + t
                s_false = 0.0  # this literal false -> j = t
                m = len(others)
                for mask in range(1 << m):
                    pr = 1.0
                    t = 0
                    for j in range(m):
                        if mask >> j & 1:
                            pr *= probs[j]
                            t += 1
                        else:
                            pr *= (1.0 - probs[j])
                    s_true += pr * w[1 + t]
                    s_false += pr * w[t]
                new_lo = math.log((s_true + 1e-300) / (s_false + 1e-300))
                # sign: message is log-odds in favor of the LITERAL being true;
                # convert to var=1 log-odds
                new_lo_var = new_lo if sign > 0 else -new_lo
                old = m_fv[(ci, pos)]
                upd = (1 - damping) * old + damping * new_lo_var
                max_delta = max(max_delta, abs(upd - old))
                m_fv[(ci, pos)] = upd
        # var -> factor updates (cavity beliefs)
        bel = beliefs()
        for ci, cl in enumerate(clauses):
            for pos in range(len(cl)):
                v = abs(cl[pos])
                sign = 1 if cl[pos] > 0 else -1
                # cavity: total belief minus this factor's contribution (in var terms)
                cav = bel[v] - m_fv[(ci, pos)]
                # convert var log-odds to literal log-odds
                lit_lo = cav if sign > 0 else -cav
                old = m_vf[(ci, pos)]
                upd = (1 - damping) * old + damping * lit_lo
                m_vf[(ci, pos)] = upd
        if verbose and it % 50 == 0:
            print(f"  iter {it} max_delta={max_delta:.2e}")
        if max_delta < tol:
            break
    bel = beliefs()
    assign = [0] * (n_vars + 1)
    for v in range(1, n_vars + 1):
        assign[v] = 1 if bel[v] > 0 else 0
    unsat = count_unsat(clauses, assign)
    return assign[1:], unsat, it


def count_unsat(clauses, assign):
    """assign: 0-based list; returns number of unsatisfied clauses."""
    n = 0
    for cl in clauses:
        ok = False
        for lit in cl:
            v = abs(lit)
            val = assign[v - 1]
            if (lit > 0 and val == 1) or (lit < 0 and val == 0):
                ok = True
                break
        if not ok:
            n += 1
    return n


def walksat_polish(clauses, assign, n_vars, max_flips=200000, seed=1, p=0.3):
    """WalkSAT starting from assign; returns (assign, unsat)."""
    rng = random.Random(seed)
    a = assign[:]
    # clause -> list of var indices; track unsatisfied set
    unsat = set()
    for i, cl in enumerate(clauses):
        if not any((lit > 0 and a[abs(lit) - 1] == 1) or
                   (lit < 0 and a[abs(lit) - 1] == 0) for lit in cl):
            unsat.add(i)
    var_clauses = [[] for _ in range(n_vars + 1)]
    for i, cl in enumerate(clauses):
        for lit in cl:
            var_clauses[abs(lit)].append(i)
    flips = 0
    while unsat and flips < max_flips:
        ci = rng.choice(tuple(unsat))
        cl = clauses[ci]
        # pick var: with prob p random from clause, else min-break
        if rng.random() < p:
            v = abs(rng.choice(cl))
        else:
            best, best_break = None, None
            for lit in cl:
                v = abs(lit)
                brk = 0
                for cj in var_clauses[v]:
                    if cj == ci:
                        continue
                    # would cj become unsat after flip?
                    sat_now = any((l > 0 and a[abs(l) - 1] == 1) or
                                  (l < 0 and a[abs(l) - 1] == 0)
                                  for l in clauses[cj])
                    a[v - 1] ^= 1
                    sat_after = any((l > 0 and a[abs(l) - 1] == 1) or
                                    (l < 0 and a[abs(l) - 1] == 0)
                                    for l in clauses[cj])
                    a[v - 1] ^= 1
                    if sat_now and not sat_after:
                        brk += 1
                if best_break is None or brk < best_break:
                    best, best_break = v, brk
            v = best
        a[v - 1] ^= 1
        flips += 1
        # recompute affected clauses
        for cj in var_clauses[v]:
            sat = any((l > 0 and a[abs(l) - 1] == 1) or
                      (l < 0 and a[abs(l) - 1] == 0) for l in clauses[cj])
            if sat:
                unsat.discard(cj)
            else:
                unsat.add(cj)
    return a, len(unsat)


def solve_bp(clauses, n_vars, seeds=(0, 1, 2), verbose=False):
    """Legacy BP path: BP with several seeds, WalkSAT polish if needed."""
    best = None
    for s in seeds:
        assign, unsat, it = bp_solve(clauses, n_vars, seed=s, verbose=verbose)
        if verbose:
            print(f"seed {s}: BP iters={it} unsat={unsat}")
        if unsat == 0:
            return assign, 0
        if best is None or unsat < best[1]:
            best = (assign, unsat)
    assign, unsat = walksat_polish(clauses, best[0], n_vars)
    if verbose:
        print(f"WalkSAT polish: unsat={unsat}")
    return assign, unsat


# ---------------------------------------------------------------------------
# MV + probSAT pipeline (default)
# ---------------------------------------------------------------------------

_HERE = os.path.dirname(os.path.abspath(__file__))


def mv_start(clauses, n_vars):
    """Majority-vote start, both directions, lower unsat wins."""
    vote = [0] * n_vars
    for cl in clauses:
        for lit in cl:
            vote[abs(lit) - 1] += 1 if lit > 0 else -1
    mv = [1 if v > 0 else 0 for v in vote]
    inv = [1 - b for b in mv]
    if count_unsat(clauses, inv) < count_unsat(clauses, mv):
        return inv
    return mv


def _ensure_probsab():
    """Build the focused probSAT binary if missing. Returns path or None."""
    bin_path = os.path.join(_HERE, 'probsab_focus')
    if os.path.isfile(bin_path):
        return bin_path
    src = os.path.join(_HERE, 'probsab_focus.c')
    if not os.path.isfile(src):
        return None
    try:
        subprocess.run(['gcc', '-O3', '-march=native', '-o', bin_path, src,
                        '-lm'], check=True, capture_output=True, timeout=120)
    except Exception:
        return None
    return bin_path if os.path.isfile(bin_path) else None


def _write_cnf(clauses, n_vars, path):
    with open(path, 'w') as f:
        f.write(f"{n_vars} {len(clauses)}\n")
        for cl in clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')


def _run_probsab(bin_path, cnf, start_bits_path, beta, seconds):
    """Runs focused probSAT. Returns (sat_bits_or_None, best_bits, best_unsat).
    best_unsat is None if the binary reported nothing usable."""
    try:
        r = subprocess.run([bin_path, cnf, '12345', str(beta),
                            str(seconds), start_bits_path],
                           capture_output=True, text=True, timeout=seconds + 30)
    except Exception:
        return None, None, None
    if r.returncode == 0:
        bits = r.stdout.strip()
        if bits and set(bits) <= {'0', '1'}:
            return bits, bits, 0
    best_bits = None
    for line in r.stderr.splitlines():
        if line.startswith('BEST unsat='):
            best_bits = None  # next 0/1 line is the bits
        elif (best_bits is None and line and set(line) <= {'0', '1'}):
            best_bits = line
    return None, best_bits, None


def solve(clauses, n_vars, budget=600, beta=4.0, round_seconds=60,
          perturb_k=8, verbose=False, seed=0):
    """MV -> focused probSAT -> ILS until budget exhausted.
    Returns (assign, unsat). Falls back to BP path if the C binary is
    unavailable."""
    bin_path = _ensure_probsab()
    if bin_path is None:
        if verbose:
            print("probsab_focus unavailable; falling back to BP path")
        return solve_bp(clauses, n_vars, verbose=verbose)
    t0 = time.time()
    cnf = os.path.join(_HERE, '_tmp_solver.cnf')
    _write_cnf(clauses, n_vars, cnf)
    try:
        start = mv_start(clauses, n_vars)
        start_path = os.path.join(_HERE, '_tmp_solver_start.bits')
        with open(start_path, 'w') as f:
            f.write(''.join('1' if b else '0' for b in start))
        best = start
        best_u = count_unsat(clauses, best)
        if verbose:
            print(f"MV start unsat={best_u}", flush=True)
        if best_u == 0:
            return best, 0
        rng = random.Random(seed)
        # phase 1: focused probSAT from MV
        sec = min(round_seconds, max(1, int(budget - (time.time() - t0))))
        sat, bb, _ = _run_probsab(bin_path, cnf, start_path, beta, sec)
        if sat is not None:
            return [1 if c == '1' else 0 for c in sat], 0
        if bb is not None:
            cand = [1 if c == '1' else 0 for c in bb]
            cu = count_unsat(clauses, cand)
            if cu < best_u:
                best, best_u = cand, cu
        if verbose:
            print(f"focused probSAT: best unsat={best_u} "
                  f"elapsed={time.time() - t0:.0f}s", flush=True)
        # phase 2: ILS until budget exhausted; cycle betas for robustness
        # across unknown k/ratio (round 0 reuses the primary beta).
        beta_cycle = [beta, 2.6, 6.0]
        rnd = 0
        while time.time() - t0 < budget and best_u > 0:
            remaining = budget - (time.time() - t0)
            sec = min(round_seconds, max(1, int(remaining)))
            rb = beta_cycle[rnd % len(beta_cycle)]
            rnd += 1
            pert = best[:]
            for v in rng.sample(range(n_vars), min(perturb_k, n_vars)):
                pert[v] ^= 1
            pert_path = os.path.join(_HERE, '_tmp_solver_pert.bits')
            with open(pert_path, 'w') as f:
                f.write(''.join('1' if b else '0' for b in pert))
            sat, bb, _ = _run_probsab(bin_path, cnf, pert_path, rb, sec)
            if sat is not None:
                return [1 if c == '1' else 0 for c in sat], 0
            if bb is not None:
                cand = [1 if c == '1' else 0 for c in bb]
                cu = count_unsat(clauses, cand)
                if cu < best_u:
                    best, best_u = cand, cu
                    if verbose:
                        print(f"ILS improved: best unsat={best_u} "
                              f"elapsed={time.time() - t0:.0f}s", flush=True)
            if verbose:
                print(f"ILS round done: best unsat={best_u} "
                      f"elapsed={time.time() - t0:.0f}s", flush=True)
        return best, best_u
    finally:
        for p in ('_tmp_solver.cnf', '_tmp_solver_start.bits',
                  '_tmp_solver_pert.bits'):
            try:
                os.unlink(os.path.join(_HERE, p))
            except OSError:
                pass


if __name__ == "__main__":
    # CLI: solver.py instance.json [budget_seconds] [beta] [--method bp]
    # instance.json: list of clauses, each a list of signed ints (1-based).
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    method = 'mv' if '--method' not in sys.argv else sys.argv[
        sys.argv.index('--method') + 1]
    if not args:
        print("usage: solver.py instance.json [budget_seconds] [beta] "
              "[--method bp|mv]")
        sys.exit(2)
    clauses = json.load(open(args[0]))
    n_vars = max(abs(l) for cl in clauses for l in cl)
    budget = int(args[1]) if len(args) > 1 else 600
    beta = float(args[2]) if len(args) > 2 else 4.0
    print(f"instance: {n_vars} vars, {len(clauses)} clauses, "
          f"ratio={len(clauses) / n_vars:.2f}, budget={budget}s, "
          f"beta={beta}, method={method}", flush=True)
    if method == 'bp':
        assign, unsat = solve_bp(clauses, n_vars, verbose=True)
    else:
        assign, unsat = solve(clauses, n_vars, budget=budget, beta=beta,
                              verbose=True)
    print(f"RESULT unsat={unsat}", flush=True)
    if unsat == 0:
        print("SAT", flush=True)
    print('BITS:' + ''.join('1' if b else '0' for b in assign), flush=True)
