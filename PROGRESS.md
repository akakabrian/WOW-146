# WOWII 146 formalization progress

Integration target: `proof/wowii-146` → `main`.

| Work package | Issue | Status | Integration notes |
|---|---:|---|---|
| Square-graph distance and radius | #2 | Complete | Merged via PR #8; focused and full CI passed. |
| Diameter, periphery, and induced-geodesic bounds | #3 | Complete | Merged via PR #10; focused and full CI passed. |
| Radius-2 exceptional induced-tree lemma | #4 | Complete | Merged via PR #11; exact `WOW146.exceptional_case` is kernel-checked. |
| Top-level assembly and upstream patch | #5 | Complete | Exact-signature `WOW146.conjecture146` assembled; upstream submission bundle prepared. |
| Independent verification | #6 | Complete | PR #14 merged; 995 connected unlabeled graphs through seven vertices passed, including all 13 exceptional graphs. |
| Upstream repository port | — | Complete | PR #15 merged; exact target, regression, axiom audit, warning-as-error checks, and full 8,884-job upstream build passed. |

## Completion state

The mathematical proof, Lean kernel checks, finite regression, upstream-native namespace port, and full upstream repository build are complete. The verified submission artifact is `upstream/formal-conjectures.patch`.

The only remaining external administrative action is to apply the patch to a fork of the upstream repository and open the upstream pull request.
