#!/usr/bin/env python3
"""nonce_solver_v3.py - NONCE SAT solver: GABUNGAN v2 + spesialis 5-SAT s/d 7-SAT (order Ray 2026-10-27).

Basis = nonce_solver_v2.py (gabungan nonce_solver.py Ray + race_solver.py + my_solver.py
+ jalur cd195-direct pemenang mint #2), DITAMBAH routing 5-SAT.

FAKTA INSTANCE NONCE (terverifikasi dari file clause asli):
  - Varian nonce-logic / connected : 3-SAT murni, rasio 4.5 (dekat ambang 3-SAT 4.27).
  - Varian balanced-384            : 5-SAT murni, rasio 18.0-22.0 (dekat/DI ATAS ambang
    5-SAT ~21.1). Inilah "soal 5-SAT" yang decomposition-nya nggak ngaruh (single
    component) dan yang bikin solver lama timeout.

Routing v3 per komponen (auto-detect k = panjang clause, rasio = clauses/vars):
  - k <= 3  : jalur v2 persis (teruji: decomposition, Kissat/probSAT race, cd195 direct).
  - k 4..7+ : jalur k-SAT, gelombang file-based, max 2 proses. Beta probSAT diskala per k
    (b1=0.5k+0.1, b2=0.8k, b3=0.38k -> k=5: 2.6/4.0/1.9; k=7: 3.6/5.6/2.7):
       Gel.1: cd195 (pemenang e9f84f94 5-SAT rasio 18: 26.9s) vs probSAT-C beta b1
       Gel.2: Kissat vs probSAT-C beta b2 (seed baru)
       Gel.3: g4    vs probSAT-C beta b3 (seed baru)
    probSAT adalah spesialis random k-SAT (Balint & Schoening); beta di-race karena
    tuning optimalnya beda per k dan per rasio -- portfolio, bukan nebak satu angka.
    Ambang rasio random k-SAT: 3-SAT ~4.27, 5-SAT ~21.1, 7-SAT ~87 -- routing membaca
    rasio aktual per komponen, bukan asumsi.

Semua perbaikan v2 tetap berlaku:
  1. TIDAK ADA ProcessPoolExecutor untuk hasil. Worker = subprocess, hasil ke FILE,
     driver mem-poll file. (Bug lama menghilangkan bits kemenangan cd195 di mint #2.)
  2. Maksimal 2 proses berat bersamaan (VM 2 core).
  3. Assignment SELALU diverifikasi ke SEMUA clause sebelum dicetak.
  4. Stdout HANYA bitstring; log ke stderr; --out menulis bitstring ke file juga.

Usage:
  nonce_solver_v3.py clauses.json [timeout_secs] [--out bits.txt]
  nonce_solver_v3.py --worker-pysat <engine> <in.json> <out.txt>   (internal)
"""
import json, sys, os, subprocess, tempfile, time, random
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
PY = os.environ.get("NONCE_PY", "/home/ubuntu/nonce-venv/bin/python")
SELF = os.path.abspath(__file__)

def _find(name, *paths):
    for p in paths:
        if p and os.path.exists(p):
            return p
    return None

KISSAT = _find("kissat",
               os.path.join(HERE, "kissat", "build", "kissat"),
               os.path.join(HERE, "..", "my-solver", "kissat", "build", "kissat"))
PROBSAB = _find("probsab",
                os.path.join(HERE, "probsab"),
                os.path.join(HERE, "..", "my-solver", "probsab"))

def log(*a):
    print(*a, file=sys.stderr, flush=True)

# ---------------------------------------------------------------- decomposition
def components(clauses, nvars):
    parent = list(range(nvars + 1))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    for c in clauses:
        for l in c[1:]:
            union(abs(c[0]), abs(l))
    seen = set()
    for c in clauses:
        for l in c:
            seen.add(abs(l))
    comp_vars = defaultdict(list)
    for v in seen:
        comp_vars[find(v)].append(v)
    comp_clauses = defaultdict(list)
    for c in clauses:
        comp_clauses[find(abs(c[0]))].append(c)
    out = [(sorted(vs), comp_clauses[root]) for root, vs in comp_vars.items()]
    out.sort(key=lambda t: -len(t[0]))
    return out

# ---------------------------------------------------------------- file formats
def write_dimacs(path, vars_, clauses):
    loc = {v: i + 1 for i, v in enumerate(vars_)}
    with open(path, "w") as f:
        f.write(f"p cnf {len(vars_)} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str((1 if l > 0 else -1) * loc[abs(l)]) for l in c) + " 0\n")
    return loc

def write_simple(path, vars_, clauses):
    loc = {v: i + 1 for i, v in enumerate(vars_)}
    with open(path, "w") as f:
        f.write(f"{len(vars_)} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(str((1 if l > 0 else -1) * loc[abs(l)]) for l in c) + " 0\n")
    return loc

def read_model_file(path):
    """File berisi signed ints (model PySAT) -> dict abs(var)->0/1, atau None."""
    try:
        toks = open(path).read().split()
        if not toks:
            return None
        return {abs(int(x)): (1 if int(x) > 0 else 0) for x in toks}
    except Exception:
        return None

def read_kissat_file(path, loc):
    inv = {v: k for k, v in loc.items()}
    vals = {}
    try:
        sat = False
        for line in open(path):
            if line.startswith("s SATISFIABLE"):
                sat = True
            elif line.startswith("v "):
                for x in line[2:].split():
                    if x != "0":
                        xi = int(x)
                        vals[inv[abs(xi)]] = 1 if xi > 0 else 0
        return vals if sat and vals else None
    except Exception:
        return None

def read_probsab_file(path, vars_, loc):
    inv = {v: k for k, v in loc.items()}
    try:
        bits = open(path).read().strip().split()[0]
        if len(bits) != len(vars_):
            return None
        return {inv[i + 1]: int(bits[i]) for i in range(len(vars_))}
    except Exception:
        return None

# ---------------------------------------------------------------- worker mode
def worker_pysat(engine, in_path, out_path):
    from pysat.solvers import Solver
    clauses = json.load(open(in_path))
    with Solver(name=engine, bootstrap_with=clauses) as s:
        if not s.solve():
            return 3
        model = s.get_model()
    with open(out_path, "w") as f:
        f.write(" ".join(str(x) for x in model))
    return 0

# ---------------------------------------------------------------- race engine
class Racer:
    """Satu proses worker yang menulis hasil ke file. Driver mem-poll file, bukan stdout."""
    def __init__(self, kind, proc, out_path, vars_, clauses, loc=None):
        self.kind, self.proc, self.out_path = kind, proc, out_path
        self.vars_, self.clauses, self.loc = vars_, clauses, loc
    def poll_result(self):
        if self.proc.poll() is None:
            return None  # masih jalan
        if self.kind == "pysat":
            m = read_model_file(self.out_path)
            return {v: m.get(v, 0) for v in self.vars_} if m else None
        if self.kind == "kissat":
            return read_kissat_file(self.out_path, self.loc)
        if self.kind == "probsab":
            return read_probsab_file(self.out_path, self.vars_, self.loc)
        return None
    def kill(self):
        try:
            self.proc.kill()
        except Exception:
            pass

def spawn_pysat(engine, vars_, clauses, tmpd, tag):
    cf = os.path.join(tmpd, f"{tag}.json")
    json.dump(clauses, open(cf, "w"))
    out = os.path.join(tmpd, f"{tag}.out")
    p = subprocess.Popen([PY, SELF, "--worker-pysat", engine, cf, out],
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return Racer("pysat", p, out, vars_, clauses)

def spawn_kissat(vars_, clauses, tmpd, tag):
    dim = os.path.join(tmpd, f"{tag}.dimacs")
    loc = write_dimacs(dim, vars_, clauses)
    out = os.path.join(tmpd, f"{tag}.out")
    fh = open(out, "w")
    p = subprocess.Popen([KISSAT, dim], stdout=fh, stderr=subprocess.DEVNULL)
    return Racer("kissat", p, out, vars_, clauses, loc)

def spawn_probsab(vars_, clauses, tmpd, tag, budget, beta=2.06):
    sim = os.path.join(tmpd, f"{tag}.simple")
    loc = write_simple(sim, vars_, clauses)
    out = os.path.join(tmpd, f"{tag}.out")
    fh = open(out, "w")
    seed = random.randrange(1, 2 ** 31)
    p = subprocess.Popen([PROBSAB, sim, str(seed), str(beta), str(max(5, int(budget)))],
                         stdout=fh, stderr=subprocess.DEVNULL)
    return Racer("probsab", p, out, vars_, clauses, loc)

def race(racers, deadline):
    """Poll file hasil semua racer sampai satu menang atau deadline habis."""
    result = None
    winner = None
    while time.time() < deadline and result is None:
        for r in racers:
            res = r.poll_result()
            if res is not None:
                result, winner = res, r.kind
                break
        if result is None:
            time.sleep(0.2)
    for r in racers:
        r.kill()
    if result is not None:
        log(f"  won by {winner}")
    return result

# ---------------------------------------------------------------- per component
def solve_component(vars_, clauses, budget, tmpd, tag):
    k = len(vars_)
    if k == 0:
        return {}
    deadline = time.time() + budget
    ratio = len(clauses) / max(1, k)
    kmax = max(len(c) for c in clauses)
    log(f"  component {tag}: {k} vars, {len(clauses)} clauses, ratio {ratio:.1f}, {kmax}-SAT, budget {budget:.0f}s")

    # komponen kecil: cd195 langsung, fallback mcb (pola nonce_solver Ray)
    if k <= 64:
        for eng in ("cd195", "mcb"):
            r = spawn_pysat(eng, vars_, clauses, tmpd, f"{tag}-{eng}")
            res = race([r], deadline)
            if res is not None:
                return res
            if time.time() >= deadline:
                return None
        return None

    # k-SAT (4..7+): decomposition nggak ngaruh (single component), CDCL murni berat
    # di dekat ambang rasio. Portfolio gelombang: CDCL bergantian dengan probSAT-C
    # (spesialis random k-SAT) dengan beta diskala per k + seed baru tiap gelombang.
    if kmax >= 4:
        b1 = round(0.5 * kmax + 0.1, 2)
        b2 = round(0.8 * kmax, 2)
        b3 = round(0.38 * kmax, 2)
        waves = [
            ("cd195-kissat-probsab", b1),
            ("kissat-probsab", b2),
            ("g4-probsab", b3),
        ]
        wi = 0
        while time.time() < deadline and wi < len(waves):
            name, beta = waves[wi]
            waves_left = len(waves) - wi
            wave_deadline = time.time() + (deadline - time.time()) / waves_left
            log(f"  {kmax}-SAT wave {wi + 1}/{len(waves)}: {name}, probSAT beta {beta}, {wave_deadline - time.time():.0f}s")
            racers = []
            if wi == 0:
                racers.append(spawn_pysat("cd195", vars_, clauses, tmpd, f"{tag}-w0-cd195"))
            elif wi == 1 and KISSAT:
                racers.append(spawn_kissat(vars_, clauses, tmpd, f"{tag}-w1-kissat"))
            elif wi == 2:
                racers.append(spawn_pysat("g4", vars_, clauses, tmpd, f"{tag}-w2-g4"))
            if PROBSAB:
                wbudget = max(5, wave_deadline - time.time())
                racers.append(spawn_probsab(vars_, clauses, tmpd, f"{tag}-w{wi}-probsab", wbudget, beta))
            if not racers:
                racers = [spawn_pysat("cd195", vars_, clauses, tmpd, f"{tag}-w{wi}-cd195")]
            res = race(racers, wave_deadline)
            if res is not None:
                return res
            wi += 1
        return None

    # single/large component, rasio tinggi (balanced): cd195 direct vs Kissat
    # -- jalur cd195 direct = pemenang mint #2 (26.9s)
    if ratio >= 10:
        racers = [spawn_pysat("cd195", vars_, clauses, tmpd, f"{tag}-cd195")]
        if KISSAT:
            racers.append(spawn_kissat(vars_, clauses, tmpd, f"{tag}-kissat"))
        res = race(racers, deadline)
        if res is not None:
            return res
        # gelombang 2: engine PySAT lain
        if time.time() < deadline:
            racers = [spawn_pysat(e, vars_, clauses, tmpd, f"{tag}-{e}") for e in ("g4", "mcb")]
            return race(racers, deadline)
        return None

    # rasio rendah (connected, ~4.5): Kissat vs probSAT-C dulu
    racers = []
    if KISSAT:
        racers.append(spawn_kissat(vars_, clauses, tmpd, f"{tag}-kissat"))
    if PROBSAB:
        racers.append(spawn_probsab(vars_, clauses, tmpd, f"{tag}-probsab", budget))
    if not racers:  # fallback kalau binary nggak ada
        racers = [spawn_pysat("cd195", vars_, clauses, tmpd, f"{tag}-cd195")]
    res = race(racers, deadline)
    if res is not None:
        return res
    # gelombang 2: cd195 vs g4 (file-based, bukan ProcessPoolExecutor)
    if time.time() < deadline:
        racers = [spawn_pysat(e, vars_, clauses, tmpd, f"{tag}-{e}2") for e in ("cd195", "g4")]
        return race(racers, deadline)
    return None

# ---------------------------------------------------------------- main
def main(argv):
    if len(argv) >= 5 and argv[1] == "--worker-pysat":
        return worker_pysat(argv[2], argv[3], argv[4])
    if len(argv) < 2:
        log("usage: nonce_solver_v2.py clauses.json [timeout_secs] [--out bits.txt]")
        return 2
    in_path = argv[1]
    budget = 270.0
    out_path = None
    rest = argv[2:]
    for i, a in enumerate(rest):
        if a == "--out" and i + 1 < len(rest):
            out_path = rest[i + 1]
        elif a != "--out" and (i == 0 or rest[i - 1] != "--out"):
            try:
                budget = float(a)
            except ValueError:
                pass
    clauses = json.load(open(in_path))
    nvars = max(abs(l) for c in clauses for l in c)
    t0 = time.time()
    comps = components(clauses, nvars)
    log(f"v2: {len(clauses)} clauses, {nvars} vars, {len(comps)} component(s), budget {budget:.0f}s")
    assign = {v: 0 for v in range(1, nvars + 1)}
    with tempfile.TemporaryDirectory() as tmpd:
        for idx, (vars_, ccls) in enumerate(comps):
            remaining = budget - (time.time() - t0) - 3
            if remaining <= 5:
                log("budget habis")
                return 1
            sol = solve_component(vars_, ccls, remaining, tmpd, f"c{idx}")
            if sol is None:
                log(f"component c{idx} UNSOLVED")
                return 1
            assign.update(sol)
    bits = "".join(str(assign[v]) for v in range(1, nvars + 1))
    for c in clauses:
        if not any((l > 0) == bool(assign[abs(l)]) for l in c):
            log("VERIFY FAILED")
            return 1
    log(f"verified {nvars} vars in {time.time() - t0:.1f}s")
    if out_path:
        with open(out_path, "w") as f:
            f.write(bits + "\n")
    sys.stdout.write(bits + "\n")
    sys.stdout.flush()
    return 0

if __name__ == "__main__":
    sys.exit(main(sys.argv))
