# WOW-146

A standalone Lean 4 project containing a kernel-checked proof of **Written on the Wall II, Conjecture 146**.

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

- The mathematical proof is complete.
- The exact upstream theorem is proved in Lean without `sorry`, `admit`, or `native_decide`.
- The exceptional radius-2 case is proved by explicit induced-tree constructions.
- The root theorem includes an exact-signature guard and `#print axioms` audit command.
- Warning-as-error compilation and the full project build have passed in CI on the integration branch.
- An explicit nonvacuous exceptional-case regression graph is included.
- Final independent sign-off is still pending: transitive-import/axiom review and exhaustive connected-unlabeled-graph enumeration through at least seven vertices remain tracked in issue #6.

Accordingly, this repository contains a complete kernel-checked proof, while the integration PR remains draft until the independent verification gate is closed.

See [`docs/conjecture146_verification.md`](docs/conjecture146_verification.md) for the human proof, the Lean proof architecture, and the remaining verification checklist.

## Proof architecture

The final theorem is assembled in `WOW146/GraphConjecture146Proof.lean` from two components:

1. `WOW146.conjecture146_of_exceptional_case`, which proves the full inequality from the single sharp case
   `(radius, diameter, periphery eccentricity) = (2, 4, 3)`;
2. `WOW146.exceptional_case`, which proves that the sharp case contains an induced tree on at least six vertices.

The supporting modules formalize:

- the square-graph distance and radius identities;
- the diameter/radius bound;
- the strict periphery-distance bound;
- the diametral-geodesic induced-tree bound;
- reusable induced-tree witness constructions;
- an explicit exceptional regression graph.

The pinned Formal Conjectures branch supplies the relevant graph definitions and reusable splice lemmas.

## Coordination

- [Goal and definition of done](../../issues/1)
- [Independent verification gate](../../issues/6)
- [Agent work packages](AGENTS.md)
- [Draft integration PR](../../pull/7)
- Integration branch: `proof/wowii-146`

## Build

The project is pinned to Lean 4.27.0 and to a Formal Conjectures proof branch containing the required graph definitions and reusable induced-tree/periphery infrastructure.

```bash
lake update
lake exe cache get
lake env lean -DwarningAsError=true WOW146.lean
lake --wfail build
```

The root proof module also runs:

```lean
#print axioms WOW146.conjecture146
```

## Repository layout

```text
WOW146.lean                              root build target
WOW146/GraphConjecture146Proof.lean      exact final theorem
WOW146/Reduction.lean                    global metric/arithmetic reduction
WOW146/ExceptionalTheorem.lean           exceptional-case theorem
WOW146/Exceptional.lean                  induced-tree constructions
WOW146/Metric.lean                       square-distance/radius infrastructure
WOW146/GlobalBounds.lean                 diameter, periphery, and tree bounds
WOW146/Regression.lean                   explicit exceptional regression graph
AGENTS.md                                parallel work packages
PROGRESS.md                              integration-branch workboard
.github/workflows/lean.yml               kernel-checking CI
docs/conjecture146_verification.md       proof and verification summary
docs/exceptional_proof_crosscheck.md     independent proof-architecture cross-check
upstream/                                upstream submission bundle
```

## Definition of done

1. The exact upstream theorem is proved without `sorry`, `admit`, or `native_decide`. **Complete.**
2. `lake env lean -DwarningAsError=true WOW146.lean` passes. **Complete on the integration branch.**
3. A full project build passes. **Complete on the integration branch.**
4. `#print axioms` is limited to standard Lean axioms. **Command is included; independent transitive-import sign-off remains.**
5. An independent finite-graph regression check finds no counterexample. **Explicit regression included; exhaustive enumeration remains.**
6. An upstream-ready patch and accurate AI-assistance disclosure are prepared. **Complete, pending final upstream compilation and review.**

## License

Apache-2.0, matching the Formal Conjectures project and its reusable proof infrastructure.
