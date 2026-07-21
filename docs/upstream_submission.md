# Upstream submission notes for WOWII Conjecture 146

## Status

The metric identity, square-radius formula, global bounds, exceptional induced-tree theorem, exact top-level theorem, and independent verification are complete in this repository.

Immutable proof commit:

- `0b750ac1ac987d7085fff796b4ea91a0cf4ecd70`
- https://github.com/akakabrian/WOW-146/commit/0b750ac1ac987d7085fff796b4ea91a0cf4ecd70

Independent audit merge commit:

- `bdb4a9d685dd90b2ac87787df5e29de52c50eda6`
- https://github.com/akakabrian/WOW-146/commit/bdb4a9d685dd90b2ac87787df5e29de52c50eda6

The audit checked the kernel signature and axioms, scanned all reachable local proof sources, reviewed every `ENat.toNat` conversion and exceptional induced-tree branch, and exhaustively tested all 995 connected unlabeled graphs with two through seven vertices. All 13 exceptional graphs passed.

## Mathematical summary

For a finite connected graph `G`, let

- `p` be the eccentricity of the peripheral set;
- `d` be the diameter;
- `t` be the largest induced-tree order;
- `r` be the natural-valued radius;
- `rho` be the natural-valued radius of the graph square.

The formal development proves

```text
rho = (r + 1) / 2
p + 1 <= d
d + 1 <= t
d <= 2 * r
```

If `rho >= 2`, then `p <= t`, hence `2*p <= t*rho`.
If `rho = 1`, then `r <= 2`, so `d <= 4` and `p <= 3`.
For `p <= 2`, the inequalities `p + 1 <= d` and `d + 1 <= t`
already give `2*p <= t`. The only remaining corner is

```text
r = 2, d = 4, p = 3,
```

where `WOW146.exceptional_case` supplies `6 <= t`.

## Exact local theorem

```lean
theorem WOW146.conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G
```

Its proof is:

```lean
by
  exact WOW146.conjecture146_of_exceptional_case G h hrad
    (WOW146.exceptional_case G h)
```

## Upstream target-file change

The submission bundle under `upstream/` contains the target-file patch and porting map for the supporting proof modules. After those modules are copied into the upstream tree, the conjecture body becomes a direct application of the ported proof theorem.

The problem annotation may now change from `research open` to `research solved` in the actual upstream submission. The upstream PR description should link the immutable proof and audit commits above rather than a moving branch URL. The final namespace port must be compiled in the upstream repository before submission.

## AI-assistance disclosure

Suggested disclosure:

> The mathematical proof was developed and checked collaboratively with AI
> systems, including OpenAI ChatGPT/Codex and Anthropic Claude. AI systems
> assisted with proof search, adversarial review, Lean API exploration, and
> formalization. Every submitted declaration was compiled by Lean against the
> pinned dependencies; the final `#print axioms` audit and CI results are
> reported in the pull request. Human maintainers remain responsible for the
> submitted claims and review decisions.

## Verification checklist

- [x] Issue #4 exceptional theorem merged.
- [x] Exact theorem signature unchanged.
- [x] No `sorry`, `admit`, `native_decide`, or project-specific axiom in the local proof.
- [x] `lake env lean -DwarningAsError=true WOW146.lean` passes.
- [x] `lake --wfail build` passes.
- [x] `#print axioms` contains only standard Lean axioms.
- [x] Immutable proof commit recorded.
- [x] Independent audit issue #6 completed.
- [x] Connected unlabeled graphs through seven vertices exhaustively tested.
- [x] Upstream target patch and AI-assistance disclosure prepared.
