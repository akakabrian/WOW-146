# WOWII 146 formalization progress

Integration target: `proof/wowii-146` → `main`.

| Work package | Issue | Status | Integration notes |
|---|---:|---|---|
| Square-graph distance and radius | #2 | Open | May proceed independently. |
| Diameter, periphery, and induced-geodesic bounds | #3 | Open | Reuse pinned WOWII 142 infrastructure. |
| Radius-2 exceptional induced-tree lemma | #4 | Open | Main graph-theoretic formalization. |
| Top-level assembly and upstream patch | #5 | Blocked | Depends on #2–#4. |
| Independent verification | #6 | Blocked | Begins after #5 integration. |

## Merge discipline

1. Agent branches target this integration branch, not `main`.
2. Every merged Lean module must compile with warnings as errors.
3. No theorem statement may be weakened or changed.
4. No `sorry`, `admit`, or `native_decide` is accepted in the research proof.
5. The final integration commit must include an axiom audit and exact CI commands.
