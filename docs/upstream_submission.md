# Upstream submission notes for WOWII Conjecture 146

## Status

The metric identity, square-radius formula, global bounds, and complete
arithmetic reduction are kernel-checked. The only pending dependency is the
exceptional induced-tree theorem from issue #4. Do **not** mark the upstream
conjecture solved until that theorem is merged and the final axiom audit passes.

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

where issue #4 supplies `6 <= t`.

## Upstream theorem body

After the exceptional theorem is merged, the upstream theorem body should be
a direct application of the integration theorem:

```lean
by
  exact WOW146.conjecture146_of_exceptional_case G h hrad
    (fun hr hd hp => WOW146.exceptional_case G h hr hd hp)
```

The final exceptional theorem name and argument order must be substituted from
the merged issue #4 implementation.

## Annotation update

Only after the final proof is merged and independently audited, change the
problem annotation from `research open` to `research solved`. Include a link to
an immutable commit containing the sorry-free proof rather than a moving branch
URL.

## AI-assistance disclosure

Suggested disclosure:

> The mathematical proof was developed and checked collaboratively with AI
> systems, including OpenAI ChatGPT/Codex and Anthropic Claude. AI systems
> assisted with proof search, adversarial review, Lean API exploration, and
> formalization. Every submitted declaration was compiled by Lean against the
> pinned dependencies; the final `#print axioms` audit and CI results are
> reported in the pull request. Human maintainers remain responsible for the
> submitted claims and review decisions.

## Final verification checklist

- [ ] Issue #4 exceptional theorem merged.
- [ ] Exact theorem signature unchanged.
- [ ] No `sorry`, `admit`, `native_decide`, or project-specific axiom.
- [ ] `lake env lean -DwarningAsError=true WOW146.lean` passes.
- [ ] `lake --wfail build` passes.
- [ ] `#print axioms` contains only standard Lean axioms.
- [ ] Immutable proof commit linked in the upstream annotation/PR.
- [ ] Independent audit issue #6 completed.
