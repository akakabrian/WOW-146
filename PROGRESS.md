# WOWII 146 formalization progress

Integration target: `proof/wowii-146` → `main`.

| Work package | Issue | Status | Integration notes |
|---|---:|---|---|
| Square-graph distance and radius | #2 | Complete | Merged via PR #8; focused and full CI passed. |
| Diameter, periphery, and induced-geodesic bounds | #3 | Complete | Merged via PR #10; focused and full CI passed. |
| Radius-2 exceptional induced-tree lemma | #4 | Complete | Merged via PR #11; exact `WOW146.exceptional_case` is kernel-checked. |
| Top-level assembly and upstream patch | #5 | Complete | Exact-signature `WOW146.conjecture146` assembled; upstream submission bundle prepared. |
| Independent verification | #6 | Complete | PR #14 merged; 995 connected unlabeled graphs through seven vertices passed, including all 13 exceptional graphs. |

## Merge discipline

1. Agent branches target this integration branch, not `main`.
2. Every merged Lean module must compile with warnings as errors.
3. No theorem statement may be weakened or changed.
4. No `sorry`, `admit`, or `native_decide` is accepted in the research proof.
5. The final integration commit includes an axiom audit, source audit, exact CI commands, and machine-readable finite-regression evidence.
