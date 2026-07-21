# WOWII 146 formalization progress

Integration target: `proof/wowii-146` → `main`.

| Work package | Issue | Status | Integration notes |
|---|---:|---|---|
| Square-graph distance and radius | #2 | Complete | Merged via PR #8; focused and full CI passed. |
| Diameter, periphery, and induced-geodesic bounds | #3 | Complete | Merged via PR #10; focused and full CI passed. |
| Radius-2 exceptional induced-tree lemma | #4 | Complete | `SimpleGraph.exceptional_case` in `WOW146/ExceptionalCase.lean` (sorry-free, standard axioms). |
| Top-level assembly and upstream patch | #5 | Complete | Exact `WOW146.conjecture146` in `WOW146/Conjecture146.lean` wires the reduction to the #4 theorem; warning-free CI and axiom audit pass. |
| Independent verification | #6 | Blocked | Begins after #4 is connected to the issue #5 wrapper. |

## Merge discipline

1. Agent branches target this integration branch, not `main`.
2. Every merged Lean module must compile with warnings as errors.
3. No theorem statement may be weakened or changed.
4. No `sorry`, `admit`, or `native_decide` is accepted in the research proof.
5. The final integration commit must include an axiom audit and exact CI commands.
