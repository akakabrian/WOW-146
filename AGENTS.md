# Agent coordination guide

Primary goal: issue #1. Integration PR: #7. Integration branch: `proof/wowii-146`.

## Parallel work packages

### Agent A — square metric

Issue: #2  
Suggested branch: `agent-a-square-metric`

Own the identity

```lean
(graphSquare G).dist a b = (G.dist a b + 1) / 2
```

and the corresponding graph-square radius theorem.

### Agent B — global bounds

Issue: #3  
Suggested branch: `agent-b-global-bounds`

Own the diametral induced-path/tree bound, the strict periphery-eccentricity bound, and safe natural-number radius/diameter inequalities. Reuse the pinned WOWII 142 infrastructure where possible.

### Agent C — exceptional case

Issue: #4  
Suggested branch: `agent-c-exceptional-case`

Own the explicit induced-tree proof when radius is 2, diameter is 4, and periphery eccentricity is 3. This is the principal graph-theoretic formalization task.

### Agent D — integration

Issue: #5  
Branch: `proof/wowii-146`

Integrate A–C, perform the arithmetic case split, prove the exact upstream theorem, run the axiom audit, and prepare the upstream patch.

### Agent E — independent audit

Issue: #6  
Suggested branch: `agent-e-independent-audit`

Verify rather than co-author: inspect all proof dependencies, rerun finite graph tests, challenge every `ℕ∞` conversion and forbidden-edge case, and post a signed-off checklist.

## Rules

1. Do not alter or weaken the target theorem.
2. Do not use `sorry`, `admit`, or `native_decide` in the research proof.
3. Agent PRs target `proof/wowii-146`; only the integration PR targets `main`.
4. Each PR must include exact build commands and `#print axioms` output for its main lemmas.
5. Keep mathematical lemmas small and named; avoid one monolithic tactic proof.
6. Preserve accurate attribution and disclose AI assistance in upstream-facing material.
