# Independent exceptional-case proof cross-check

This document records the reconciliation of two independently developed Lean
formalizations of the hardest case in WOWII Conjecture 146.

## Proof artifacts

### Canonical implementation

- Theorems: `WOW146.exceptional_six_vertex_induced_tree` and
  `WOW146.exceptional_case`
- Modules: `WOW146/Metric.lean`, `WOW146/Exceptional.lean`, and
  `WOW146/ExceptionalTheorem.lean`
- Merged by PR #11
- Merge commit: `2282ce9326c52279a399fb0e14f946efd38268e6`

### Independent Claude implementation

- Theorem: `SimpleGraph.exceptional_case`
- Module: `WOW146/ExceptionalCase.lean`
- Regression module: `WOW146/Regression.lean`
- PR #12 head commit: `a05792f3eab54d4bcbafafa9b18478ea3d0215fc`
- PR #13 wrapper head commit: `45df99b352bf342065e6c7d4580f514cc91ca6a3`

The Claude implementation was not merged wholesale because it duplicates the
canonical theorem and was developed against an older integration state. Its
concrete regression graph and exact-signature guard were adapted into the
canonical integration branch.

## Shared mathematical configuration

Both implementations independently extract:

```text
d(x,y) = 4
d(z,x) = d(z,y) = 3
d(c,x) = d(c,y) = 2
d(c,z) ∈ {1,2}
```

Both use a diametral geodesic through a center and split on `d(c,z)`.

## Structural comparison

| Obligation | Canonical proof | Independent Claude proof |
|---|---|---|
| Witness at distance three from the periphery | `exists_eccSet_witness_splice` | same upstream witness API |
| Diametral endpoints are peripheral | WOWII 142 splice lemma | same upstream splice lemma |
| Square-radius conversion | local metric API and `graphSquareRadius_eq` | direct use of `graphSquareRadius_eq` |
| Explicit induced-tree certificate | geodesic support plus unique leaf insertions | singleton tree plus repeated `IsTree.induce_insert_leaf` |
| `d(c,z)=1` case | diametral geodesic plus `z` attached at `c` | same six-vertex construction |
| `d(c,z)=2`, no cross arm | attach midpoint `w` uniquely to the diametral geodesic | explicit leaf-insertion chain |
| Cross-arm cases | `six_le_largestInducedTreeSize_of_cross_arm` | named neither/both/exactly-one lemmas |
| Exactly-one chord case | explicit geodesics and three unique insertions | independent `exceptional_exactly_one_aux` case analysis |
| Pairwise distinctness | derived locally from distances and nonadjacency | explicit named inequalities for every `Finset.card` step |
| Axiom output | `propext`, `Classical.choice`, `Quot.sound` | same standard axiom set |

## Adversarial audit checklist

Issue #6 should confirm the following against both proof terms:

1. Every use of a distance equality is oriented correctly under `dist_comm`.
2. Every inserted vertex is proved absent from the current `Finset`.
3. Every possible chord is either excluded by a distance lower bound or handled
   by a separate branch.
4. The symmetric `u-w` and `v-w` cross-arm branches use genuinely symmetric
   hypotheses after exchanging `x` and `y`.
5. The exactly-one branch covers `b=w`, `u-b`, `w-a`, and `w-b` possibilities
   without silently assuming their negations.
6. The final cardinality lower bound is attached to an induced tree rather than
   merely to a connected subgraph.
7. All `ENat.toNat` conversions occur under connectedness or an explicit
   non-top hypothesis.

## Imported independent regression

The six-vertex spider from Claude's PR #12 has been adapted into the canonical
`WOW146/Regression.lean` module. It verifies, using `decide` rather than
`native_decide`, that a concrete graph has:

```text
radius = 2
diameter = 4
periphery = {0,4}
eccentricity(periphery) = 3
```

and then applies the canonical `WOW146.exceptional_case` theorem.

This cross-check materially strengthens confidence but does not replace the
full independent sign-off and exhaustive finite enumeration required by issue
#6.
