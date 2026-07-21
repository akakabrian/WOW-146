# Issue #6 independent audit

## Verdict

PASS. The exact theorem, kernel dependencies, local proof sources, exceptional construction, and exhaustive finite regression all passed.

Audit workflow: `29817779056`

## Kernel and signature

`WOW146/Audit.lean` restates the current Formal Conjectures signature verbatim and applies `WOW146.conjecture146`. Lean reports the same hypotheses and conclusion for both declarations.

The final theorem, exceptional theorem, and explicit exceptional regression depend only on:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` or project-specific axiom occurs.

## Source audit

The scanner followed every local `WOW146.*` import reachable from `WOW146.lean`. It checked ten proof-surface files and found no executable `sorry`, `admit`, `native_decide`, or `axiom` declaration. External open conjectures are harmless here because `#print axioms WOW146.conjecture146` excludes their placeholders.

## `ENat` audit

Every `ENat.toNat` conversion is protected by connectedness or a proved non-top hypothesis. The radius, eccentricity, and diameter conversions cannot exploit `top.toNat = 0`, and the arithmetic reduction uses only the resulting natural-valued lemmas.

## Exceptional-case audit

The canonical proof and Claude's independently developed proof derive the same metric configuration and cover both center-distance cases, both cross-arm orientations, and all named exactly-one chord possibilities. Every witness is proved to induce a tree; distinctness and vertex non-membership are established before the cardinality bound is used.

## Exhaustive finite regression

The independent Python audit enumerated every connected unlabeled graph with 2 through 7 vertices from NetworkX's Graph Atlas.

| Vertices | Graphs checked |
|---:|---:|
| 2 | 1 |
| 3 | 2 |
| 4 | 6 |
| 5 | 21 |
| 6 | 112 |
| 7 | 853 |
| **Total** | **995** |

For each graph it independently computed all-pairs distances, periphery eccentricity, graph-square radius, and maximum induced-tree order by exhaustive vertex-subset search.

```text
995 / 995 conjecture checks passed
13 exceptional graphs found
13 / 13 exceptional checks passed
0 inequality failures
0 exceptional failures
minimum slack = 0
six-vertex spider witness found
```

## Commands

```text
python audit/enumerate_graphs.py --json audit/finite_regression_report.json
python audit/source_audit.py
lake build WOW146.Audit
lake env lean -DwarningAsError=true WOW146/Audit.lean
lake env lean -DwarningAsError=true WOW146.lean
lake --wfail build
```

Evidence is committed in `audit/finite_regression_report.json`, `audit/source_audit_report.json`, and `audit/lean_audit.log`.

## Disclosure and residual concern

The AI-assistance disclosure accurately credits ChatGPT/Codex and Claude and leaves submission responsibility with human maintainers. No residual concern remains for the standalone theorem. The final upstream namespace port must still be compiled in the upstream repository before submission; that is a packaging check rather than a gap in the theorem.
