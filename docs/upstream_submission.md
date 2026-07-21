# Upstream submission notes for WOWII Conjecture 146

## Status

The proof, independent audit, upstream-native port, and complete upstream repository build verification are finished.

Immutable proof commit:

- `0b750ac1ac987d7085fff796b4ea91a0cf4ecd70`

Independent audit merge:

- `bdb4a9d685dd90b2ac87787df5e29de52c50eda6`

Verified upstream-port merge:

- `4cfddef9f3a3185b1995077968df6fe09f47b6fb`

The upstream port was generated and compiled in a pristine checkout of `AlperTheKing/formal-conjectures` at:

```text
b8b5208aa5d01f5f91c49ca516bf09cae8d93693
```

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

## Verified upstream form

The upstream porter places the raw proof in:

```text
WrittenOnTheWallII.GraphConjecture146.Proof
```

It removes the statement/proof import cycle by proving the equivalent raw form using `(graphSquare G).radius.toNat`. The target theorem unfolds its local `graphSquareRadius` abbreviation and applies:

```lean
Proof.conjecture146 G h hrad
```

The target patch also:

- changes `research open` to `research solved`;
- adds `formal_proof using lean4` with the immutable proof link;
- adds the proof and regression modules to `FormalConjecturesForMathlib.lean`;
- carries the required W142 support module from verified commit `46bf39015f5c3c3ba3bfcf9f752b4b1e49b584ac`;
- follows the repository's public-module conventions.

## Upstream verification

The following commands passed inside the actual upstream checkout:

```text
lake build FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.GraphConjecture146Proof
lake build FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.Regression
lake build FormalConjectures.WrittenOnTheWallII.GraphConjecture146
lake build FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture146.Audit
lake env lean -DwarningAsError=true FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture146/GraphConjecture146Proof.lean
lake env lean -DwarningAsError=true FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture146/Regression.lean
lake env lean -DwarningAsError=true FormalConjectures/WrittenOnTheWallII/GraphConjecture146.lean
lake env lean -DwarningAsError=true FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture146/Audit.lean
lake --wfail build
```

The full upstream build completed successfully with 8,884 jobs. The exact patched theorem, raw proof theorem, exceptional theorem, and regression depend only on:

```text
propext
Classical.choice
Quot.sound
```

Verified workflow run: `29822594177`.

## Submission bundle

- `upstream/formal-conjectures.patch` — complete full-index patch;
- `upstream/upstream-build.log` — complete build and axiom log;
- `upstream/upstream-port-manifest.txt` — provenance manifest;
- `upstream/port_to_formal_conjectures.py` — reproducible porter;
- `.github/workflows/upstream-port.yml` — repeatable verification workflow.

The connected GitHub account does not have push access to the upstream repository. The only remaining administrative action is to apply this verified patch to a fork and open the upstream pull request.

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

- [x] Exact theorem signature unchanged.
- [x] No `sorry`, `admit`, `native_decide`, or project-specific axiom in the proof.
- [x] Standalone warning-as-error and full builds pass.
- [x] Standard-axiom audit passes.
- [x] Independent audit completed.
- [x] Connected unlabeled graphs through seven vertices exhaustively tested.
- [x] Upstream-native namespace port completed.
- [x] Exact upstream target compiled with warnings as errors.
- [x] Full upstream `lake --wfail build` completed.
- [x] Complete patch, build log, manifest, and disclosure prepared.
