# WOWII 146 formalization progress

Integration target: `proof/wowii-146` → `main`.

| Work package | Issue | Status | Integration notes |
|---|---:|---|---|
| Square-graph distance and radius | #2 | In progress | Implemented on `agent-complete-proof`; awaiting warning-as-error CI. |
| Diameter, periphery, and induced-geodesic bounds | #3 | In progress | Global arithmetic reduction compiles modulo the exceptional lemma. |
| Radius-2 exceptional induced-tree lemma | #4 | In progress | Human proof audited; Lean construction now being encoded. |
| Top-level assembly and upstream patch | #5 | Blocked | Depends on the exceptional lemma and clean axiom audit. |
| Independent verification | #6 | Blocked | Begins after proof integration. |

## Merge discipline

1. Agent branches target the integration branch, not `main`; PR #9 temporarily targets `main` only to obtain CI while the integration branch is moving.
2. Every merged Lean module must compile with warnings as errors.
3. No theorem statement may be weakened or changed.
4. No `sorry`, `admit`, `native_decide`, or project-specific axiom is accepted in the final research proof.
5. The final integration commit must include an axiom audit and exact CI commands.
