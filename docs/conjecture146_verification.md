# Written on the Wall II — Conjecture 146: Verification Summary

**Claim.** For a finite, nontrivial, connected simple graph $G$:

$$2p \le t\rho,$$

where $B$ is the set of peripheral vertices, $p=\max_v d(v,B)$, $t$ is the largest induced-tree order, $G^2$ is the square graph, and $\rho=\operatorname{rad}(G^2)$.

## Current verdict

The mathematical argument is complete, and the repository now contains a compiling Lean proof of the exact Formal Conjectures declaration without `sorry`, `admit`, or `native_decide`.

The proof has received adversarial review and an independent alternative treatment of the exceptional case. The integration branch has passed warning-as-error compilation and a full project build. Final independent sign-off is still pending on two deliberately separate checks:

1. a transitive-import and axiom audit of the final theorem;
2. exhaustive connected-unlabeled-graph enumeration through at least seven vertices.

Until those checks are recorded in issue #6, the correct description is:

> complete kernel-checked proof, pending final independent verification and upstream review.

Notation below: $r=\operatorname{rad}(G)$ and $d=\operatorname{diam}(G)$.

---

## 1. Mathematical proof

### Geodesic fact

A shortest walk $v_0v_1\cdots v_k$ has distinct vertices. If $v_iv_j$ were an edge with $|i-j|>1$, replacing the corresponding segment by that edge would shorten the walk. Thus every geodesic is an induced path, and its $k+1$ vertices induce a tree.

### Core lemmas

- **A. Square radius.**
  $$d_{G^2}(a,b)=\left\lceil\frac{d_G(a,b)}2\right\rceil,$$
  hence
  $$\rho=\left\lceil\frac r2\right\rceil.$$

- **B. Radius/diameter bound.**
  $$r\le d\le 2r.$$

- **C. Diametral induced tree.** A diametral geodesic has $d+1$ vertices, so
  $$t\ge d+1.$$

- **D. Strict periphery-distance bound.**
  $$p\le d-1.$$

  Indeed, $p\le d$. Equality would give a vertex $z$ with $d(z,B)=d$, hence eccentricity $d$, so $z$ itself would be peripheral; then $d(z,B)=0$, a contradiction.

- **E. Exceptional case.** If
  $$r=2,\qquad d=4,\qquad p=3,$$
  then
  $$t\ge 6.$$

### Arithmetic reduction

Using A–D:

| Regime | Conclusion |
|---|---|
| $r\ge 3$ | $\rho\ge2$, so $t\rho\ge2(d+1)\ge2p$ |
| $r=1$ | $d\le2$, $p\le1$, $t\ge2$, and $\rho=1$ |
| $r=2$, $d\le3$ | $2p\le2(d-1)\le d+1\le t=t\rho$ |
| $r=2$, $d=4$, $p\le2$ | $2p\le4\le5\le t=t\rho$ |
| $r=2$, $d=4$, $p=3$ | Lemma E gives $t\ge6=2p$ |

This proves the conjecture once Lemma E is established.

### Proof of the exceptional case

Choose $z$ with $d(z,B)=3$. Then $z$ is not peripheral. Since the graph has diameter $4$, $z$ cannot have eccentricity $4$; therefore $\operatorname{ecc}(z)=3$. Consequently every peripheral vertex is exactly distance $3$ from $z$.

Choose diametral endpoints $x,y$ and a center $c$. Then

$$d(x,y)=4,\qquad d(z,x)=d(z,y)=3,$$

and

$$d(c,x)=d(c,y)=2,\qquad d(c,z)\in\{1,2\}.$$

#### Case 1: $d(c,z)=1$

Choose midpoints so that

$$x-u-c-v-y$$

is a diametral geodesic. The vertex $z$ is adjacent to $c$ and nonadjacent to $x,u,v,y$, since any such extra adjacency would shorten either $d(z,x)$ or $d(z,y)$. Hence

$$\{x,u,c,v,y,z\}$$

induces the six-vertex tree with edges

$$xu,\ uc,\ cv,\ vy,\ cz.$$

#### Case 2: $d(c,z)=2$

Choose $w$ with $z-w-c$. Among the vertices

$$\{x,u,c,v,y,w,z\},$$

the six arm edges are prescribed, and triangle-inequality arguments rule out every additional edge except possibly $uw$ and $vw$.

- If neither exists, the seven vertices induce a tree.
- If one exists, an explicit six-vertex induced tree is obtained from the cross-arm construction.
- If both exist, deleting the center leaves the six-vertex tree
  $$x-u-w-z,\qquad w-v-y.$$

Thus every exceptional configuration contains an induced tree on at least six vertices.

---

## 2. Lean proof architecture

The final exact theorem is in:

```text
WOW146/GraphConjecture146Proof.lean
```

Its proof is:

```lean
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G := by
  exact conjecture146_of_exceptional_case G h hrad (exceptional_case G h)
```

The two principal components are:

### Global reduction

```text
WOW146/Reduction.lean
```

`WOW146.conjecture146_of_exceptional_case` formalizes the complete metric and arithmetic reduction. It uses:

- `graphSquareRadius_eq`;
- `eccSet_periphery_add_one_le_diam`;
- `diam_succ_le_largestInducedTreeSize`;
- `diam_le_two_mul_radius_toNat`;
- an `omega`-checked case split that isolates exactly the corner
  $(r,d,p)=(2,4,3)$.

### Exceptional theorem

```text
WOW146/ExceptionalTheorem.lean
WOW146/Exceptional.lean
```

`WOW146.exceptional_case` proves

```lean
G.radius.toNat = 2 →
G.diam = 4 →
eccSet G (maxEccentricityVertices G : Set α) = 3 →
6 ≤ largestInducedTreeSize G
```

The implementation extracts the metric configuration, proves all required nonadjacencies from distance lower bounds, and applies explicit induced-tree witness lemmas. The proof branches are constructive rather than delegated to a decision procedure.

### Exact-signature and axiom guards

The final module contains:

```lean
example (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
      largestInducedTreeSize G * graphSquareRadius G :=
  WOW146.conjecture146 G h hrad

#check WrittenOnTheWallII.GraphConjecture146.conjecture146
#check WOW146.conjecture146
#print axioms WOW146.conjecture146
```

This prevents accidental weakening of the theorem statement and exposes the final axiom dependency for review.

### Regression artifact

```text
WOW146/Regression.lean
```

This file contains an explicit nonvacuous graph exhibiting the exceptional parameter pattern and verifies the required six-vertex induced-tree lower bound in Lean.

---

## 3. Build and CI status

The integration branch uses:

```bash
lake update
lake exe cache get
lake env lean -DwarningAsError=true WOW146.lean
lake --wfail build
```

These commands have passed in CI on the complete proof branch. The CI workflow also compiles the exact theorem module and imports the explicit regression.

The research proof contains no project-specific axiom declaration and no use of:

```text
sorry
admit
native_decide
```

A final reviewer should nevertheless inspect all transitive imports and record the exact `#print axioms WOW146.conjecture146` output rather than relying only on the local source files.

---

## 4. Independent cross-checks completed

- The original human proof was audited for distance orientation, vertex distinctness, omitted chords, and exceptional-case coverage.
- A separate Claude-generated exceptional-case proof was preserved as an independent comparison artifact.
- `docs/exceptional_proof_crosscheck.md` compares the two proof architectures.
- The exact upstream theorem signature is restated as a compiling example.
- An explicit exceptional regression graph is included in the root build.

These checks materially strengthen confidence, but they do not replace the final independent sign-off specified in issue #6.

---

## 5. Remaining verification gate

Before upstream submission, issue #6 should record:

1. the exact audited commit SHA;
2. successful warning-as-error and full-build commands;
3. the complete `#print axioms WOW146.conjecture146` output;
4. confirmation that transitive imports contain no placeholders or nonstandard proof axioms;
5. exhaustive connected-unlabeled-graph verification through at least seven vertices;
6. confirmation that the final upstream patch compiles in its destination namespace and pinned dependency revision;
7. accurate attribution and AI-assistance disclosure.

Once those items pass, the repository is ready to be described as a formally verified solution submitted for upstream mathematical and code review.
