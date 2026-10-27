import json, random, sys
# gen_ksat.py n m k seed out.json  -- uniform random k-SAT with a planted assignment
n, m, k, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = random.Random(seed)
planted = [rng.random() < 0.5 for _ in range(n + 1)]
clauses = []
while len(clauses) < m:
    vs = rng.sample(range(1, n + 1), k)
    c = [v if rng.random() < 0.5 else -v for v in vs]
    if all((l > 0) != planted[abs(l)] for l in c):
        continue  # would falsify the planted assignment; resample
    clauses.append(c)
json.dump(clauses, open(out, "w"))
print(f"planted {k}-SAT n={n} m={m} ratio={m/n:.1f} -> {out}")
