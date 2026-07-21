# WOW-146

A standalone Lean 4 project for finishing and kernel-checking **Written on the Wall II, Conjecture 146**.

## Statement

For a finite, nontrivial, connected simple graph `G`, let:

- `B` be the set of peripheral vertices;
- `p = max_v dist(v, B)`;
- `t` be the largest induced-tree order;
- `G²` be the square graph;
- `ρ = radius(G²)`.

The conjecture asserts

```text
2p ≤ tρ.
```

The exact Formal Conjectures declaration is:

```lean
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G
```

## Status

- The mathematical proof is complete and has undergone an independent adversarial audit.
- The exceptional radius-2 case has an explicit induced-tree construction.
- A sorry-free Lean formalization is **in progress**.
- This repository will not claim the conjecture is formally solved until CI compiles the exact theorem and `#print axioms` reports only standard Lean axioms.

See [`docs/conjecture146_verification.md`](docs/conjecture146_verification.md) for the audited proof and formalization plan.

## Build

The project is pinned to Lean 4.27.0 and to a Formal Conjectures proof branch containing reusable induced-tree and periphery lemmas.

```bash
lake update
lake exe cache get
lake env lean -DwarningAsError=true WOW146.lean
```

## Repository layout

```text
WOW146.lean                              root build target
WOW146/GraphConjecture146Proof.lean      proof module
AGENTS.md                                parallel work packages
.github/workflows/lean.yml               kernel-checking CI
docs/conjecture146_verification.md       audited human proof
```

## Definition of done

1. The exact upstream theorem is proved without `sorry`, `admit`, or `native_decide`.
2. `lake env lean -DwarningAsError=true WOW146.lean` passes.
3. A full project build passes.
4. `#print axioms` is limited to standard Lean axioms.
5. An independent finite-graph regression check finds no counterexample.
6. An upstream-ready patch and accurate AI-assistance disclosure are prepared.

## License

Apache-2.0, matching the Formal Conjectures project and its reusable proof infrastructure.
