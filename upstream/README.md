# Upstream submission bundle

This directory records the mechanical port from the standalone `WOW-146` project into the Formal Conjectures repository.

## Certified source

The immutable standalone proof commit is:

```text
0b750ac1ac987d7085fff796b4ea91a0cf4ecd70
```

https://github.com/akakabrian/WOW-146/commit/0b750ac1ac987d7085fff796b4ea91a0cf4ecd70

## Supporting modules

Port the following modules into an upstream proof namespace, preserving theorem bodies and dependency order:

```text
WOW146/GraphSquareMetric.lean
WOW146/GraphSquareRadius.lean
WOW146/GlobalBounds.lean
WOW146/Metric.lean
WOW146/Exceptional.lean
WOW146/ExceptionalTheorem.lean
WOW146/Reduction.lean
WOW146/GraphConjecture146Proof.lean
```

A suitable upstream location is:

```text
FormalConjecturesForMathlib/WrittenOnTheWallII/GraphConjecture146/
```

Replace imports beginning with `WOW146.` by the corresponding upstream module paths. The local namespace `WOW146` may either be retained as an implementation namespace or mechanically renamed to `WrittenOnTheWallII.GraphConjecture146.Proof`.

The proof depends on the already formalized WOWII 142 support API, including the `*_splice` lemmas imported from:

```text
FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof
```

## Target theorem

After the supporting modules are present, apply `GraphConjecture146.patch` to the upstream conjecture file. The patch intentionally changes the problem annotation to `research solved`; do this only after the independent audit in issue #6 has completed.

The port must be checked with the upstream pinned Lean and Mathlib versions, warnings treated as errors, a full `lake --wfail build`, and `#print axioms` on the final theorem.
