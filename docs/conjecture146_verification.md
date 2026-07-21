# Written on the Wall II — Conjecture 146: Verification Summary

**Claim.** For a finite, nontrivial, connected simple graph $G$:
$$2p \le t\rho,$$
where $B$ = peripheral vertices, $p = \max_v d(v,B)$, $t$ = largest induced tree size, $G^2$ = the square graph, and $\rho = \operatorname{rad}(G^2)$.

**Verdict: the proposed proof is SOUND.** No counterexample, no false distance assertion, no broken induced-subgraph claim. The only shortcomings in the original sketch are *presentation gaps* (implicit triangle-inequality bookkeeping), not logical ones. They are discharged below with a single distance table.

Notation: $r = \operatorname{rad}(G)$, $d = \operatorname{diam}(G)$.

---

## Geodesic fact (used throughout)

A shortest walk $v_0 v_1 \cdots v_k$ has distinct vertices, and $v_i v_j \in E$ implies $|i-j| = 1$. Hence every geodesic is an induced path, and its $k+1$ vertices induce a tree.

---

## Part 1 — Audit of the flagged claims

| Claim | Status | Reason |
|---|---|---|
| $\rho = \lceil r/2 \rceil$ | ✅ | $d_{G^2}(a,b) = \lceil d_G(a,b)/2\rceil$ (lower bound: each step covers $\le 2$; upper: jump two-at-a-time). Monotonicity of $\lceil\cdot/2\rceil$ gives $\operatorname{rad}(G^2) = \lceil r/2\rceil$. |
| $p \le d-1$ | ✅ | $p \le d$ since $B \ne \varnothing$. If $d(z,B)=d$ then $\operatorname{ecc}(z)=d$, so $z\in B$, forcing $d(z,B)=0$ — contradiction. |
| $\operatorname{ecc}(z)=3$ (exceptional case) | ✅ | $d(z,B)=3 \Rightarrow \operatorname{ecc}(z)\ge 3$; $z\notin B$ rules out $\operatorname{ecc}(z)=4$. Then $d(z,q)=3$ for **every** $q\in B$. |
| Forbidden-edge list in Case 2 | ✅ | Follows from the distance table below. |
| $u\text-b,\ w\text-a,\ w\text-b$ are the only possible chords (Subcase 2C) | ✅ | Every other chord is forced to distance $\ge 2$ by triangle inequality. |
| Distinctness of the seven vertices | ✅ | $w=u$ or $w=v$ would put $z$ within distance $2$ of $x$ or $y$. |

### Reduction arithmetic

Since $d \le 2r$ always, $r=2 \Rightarrow d \le 4$.

| Regime | Why $2p \le t\rho$ |
|---|---|
| $r \ge 3$ | $\rho\ge 2,\ t\ge d+1$: $t\rho \ge 2(d+1) \ge 2(d-1) \ge 2p$ |
| $r = 1$ | $d\le 2,\ p\le 1,\ \rho=1,\ t\ge 2$: $2p \le 2 \le t\rho$ |
| $r=2,\ d\le 3$ | $2p \le 2(d-1) \le d+1 \le t = t\rho$ |
| $r=2,\ d=4,\ p\le 2$ | $2p \le 4 \le 5 \le t = t\rho$ |
| $r=2,\ d=4,\ p=3$ | needs $t \ge 6$ — **the exceptional case** |

Because $p \le d-1 = 3$ when $d=4$, the last row is the only survivor.

### The distance table (Case 2, $d(c,z)=2$)

Center $c$ ($\operatorname{ecc}(c)=2$), diametral pair $x,y$, and $z$ with midpoints $x\text-u\text-c$, $y\text-v\text-c$, $z\text-w\text-c$. Prescribed: $d(x,y)=4$, $d(x,z)=d(y,z)=3$, $d(c,x)=d(c,y)=d(c,z)=2$, plus the six unit arms. Triangle inequality $d(s,t) \ge d(s,m)-d(m,t)$ yields:

$$d(u,y)\ge 3,\quad d(v,x)\ge 3,\quad d(u,z),d(v,z),d(w,x),d(w,y)\ge 2,$$

and $x\text-u\text-c\text-v\text-y$ is a length-4 walk between distance-4 vertices, hence a geodesic (so $d(u,v)=2$). Adjacency requires distance exactly $1$, so among $\{x,u,c,v,y,w,z\}$ the only pairs not forced to distance $\ge 2$ are the **six arms** plus possibly $u\text-w$ and $v\text-w$.

For Subcase 2C's walk $x\text-u\text-w\text-z\text-b\text-a\text-y$ (with $z\text-b\text-a\text-y$ a geodesic), the same method forces all chords $\ge 2$ except $u\text-b,\ w\text-a,\ w\text-b$.

---

## Part 2 — Polished proof

**Lemmas.**

- **A.** $d_{G^2}(a,b) = \lceil d_G(a,b)/2\rceil$; hence $\rho = \lceil r/2\rceil$.
- **B.** $r \le d \le 2r$.
- **C.** $t \ge d+1$ (a diametral geodesic is an induced path on $d+1$ vertices).
- **D.** $p \le d-1$.
- **E.** If $r=2,\ d=4,\ p=3$, then $t \ge 6$.

**Theorem from A–E.** By A, $\rho=\lceil r/2\rceil$.
- $r\ge 3$: $\rho\ge 2$, $t\rho \ge 2(d+1) \ge 2p$.
- $r=1$: $d\le 2$, $2p\le 2 \le t\rho$.
- $r=2$: $\rho=1$, $d\le 4$. For $d\le 3$: $2p\le 2(d-1)\le d+1\le t$. For $d=4,p\le 2$: $2p\le 4\le 5\le t$. For $d=4,p=3$: E gives $t\ge 6=2p$. $\blacksquare$

**Proof of Lemma E.** Pick $z$ with $d(z,B)=3$; then $\operatorname{ecc}(z)=3$ and $d(z,q)=3$ for all $q\in B$. Fix diametral $x,y$ (so $d(z,x)=d(z,y)=3$) and center $c$; then $d(c,x)=d(c,y)=2$ and $d(c,z)\in\{1,2\}$.

**Case $d(c,z)=1$.** Midpoints give geodesic $x\text-u\text-c\text-v\text-y$. Since $z\sim c$ and $z$ is nonadjacent to $x,y$ (distance 3) and to $u,v$ (else $d(z,x)\le 2$ or $d(z,y)\le 2$), the set $\{x,u,c,v,y,z\}$ induces the tree $xu,uc,cv,vy,cz$. So $t\ge 6$.

**Case $d(c,z)=2$.** Midpoints $u,v,w$. By the table, $\{x,u,c,v,y,w,z\}$ induces exactly the six arms plus possibly $uw,vw$.

- **Neither $uw,vw$:** all seven vertices induce a tree (hub $c$). $t\ge 7$.
- **Both:** delete $c$; $\{x,u,w,z,v,y\}$ induces tree $xu,uw,wz,wv,vy$ (hub $w$). $t\ge 6$.
- **Exactly one** (say $uw$, by symmetry): $x\text-u\text-w\text-z$ is a geodesic. Take a $z\text-y$ geodesic $z\text-b\text-a\text-y$.
  - $b=w$: $\{x,u,w,z,a,y\}$ induces tree $xu,uw,wz,wa,ay$. $t\ge 6$.
  - $b\ne w$: seven distinct vertices; only possible chords of $x\text-u\text-w\text-z\text-b\text-a\text-y$ are $ub,wa,wb$:
    - $ub$ present → $\{x,u,b,z,a,y\}$ induces tree $xu,ub,bz,ba,ay$;
    - else $wa$ present → $\{x,u,w,z,a,y\}$ induces tree $xu,uw,wz,wa,ay$;
    - else $wb$ present → $\{x,u,w,b,a,y\}$ induces path $x\text-u\text-w\text-b\text-a\text-y$;
    - else none → $x\text-u\text-w\text-z\text-b\text-a\text-y$ is an induced 7-path.

  Each is an induced tree on $\ge 6$ vertices. $\blacksquare$

---

## Part 3 — Lean 4 formalization plan

Reduce the `sorry` to five named lemmas, then close with arithmetic (`interval_cases` on radius, then `omega`).

```lean
variable {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]

-- A. square distance and radius
lemma graphSquare_dist (h : G.Connected) (a b : α) :
    (graphSquare G).dist a b = (G.dist a b + 1) / 2
lemma graphSquareRadius_eq (h : G.Connected) :
    graphSquareRadius G = (radius G + 1) / 2

-- B. radius/diameter sandwich
lemma diam_le_two_radius (h : G.Connected) : diam G ≤ 2 * radius G
lemma radius_le_diam     (h : G.Connected) : radius G ≤ diam G

-- C. diametral geodesic ⟹ induced tree of size d+1
lemma diam_succ_le_tree (h : G.Connected) :
    diam G + 1 ≤ largestInducedTreeSize G

-- D. eccentricity of the periphery
lemma eccSet_periph_le (h : G.Connected) :
    eccSet G (maxEccentricityVertices G) + 1 ≤ diam G

-- E. the exceptional case
lemma exceptional_case (h : G.Connected)
    (hr : radius G = 2) (hd : diam G = 4)
    (hp : eccSet G (maxEccentricityVertices G) = 3) :
    6 ≤ largestInducedTreeSize G
```

**Top-level assembly:**

```lean
theorem conjecture146 (h : G.Connected) (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G) ≤
      largestInducedTreeSize G * graphSquareRadius G := by
  have hA := graphSquareRadius_eq G h
  have hB1 := diam_le_two_radius G h
  have hB2 := radius_le_diam G h
  have hC := diam_succ_le_tree G h
  have hD := eccSet_periph_le G h
  -- case split on radius; in the r=2,d=4,p=3 corner invoke exceptional_case
  sorry
```

**Where the real work is:**

- **Lemma A** — no square-distance lemma exists in Mathlib; both bounds are new. Lower bound: induction on a `G`-geodesic `Walk`. Upper bound: a "pair up consecutive edges" construction.
- **Lemma C** — needs "a shortest walk is an induced path" (inducedness/no-chords must be proved) plus a witness API for `largestInducedTreeSize`.
- **Lemma E** — nearly all effort. Recommended reusable lemma:

```lean
lemma induced_tree_of_forbidden
    (S : Finset α) (T : SimpleGraph α)          -- intended edge set on S
    (hsub : ∀ a ∈ S, ∀ b ∈ S, G.Adj a b ↔ T.Adj a b)
    (htree : T.IsTreeOn S) :
    S.card ≤ largestInducedTreeSize G
```

Each of the ~7 configurations then becomes: exhibit `S`, prove the `↔` via the distance table (`d ≥ 2 → ¬Adj`), and hand `htree` a small explicit tree. All distance facts reduce to `SimpleGraph.dist_triangle`, so a custom tactic can close forbidden-edge goals automatically.

---

## Part 4 — Sorry-free status (honest)

A compiling sorry-free proof is **not** included: it depends on the exact definitions of the five primitives, and Mathlib currently lacks radius, eccentricity, `graphSquare`, and any "largest induced tree" API. A real formalization is on the order of a few thousand lines, dominated by Lemma A and the induced-tree witness plumbing.

The **mathematics is settled**: the reduction is arithmetic once A–E hold, A–D are short, and E — the entire content — is fully proved above.

**Recommended next steps.**
1. Paste actual signatures for `graphSquare`, `eccSet`, `maxEccentricityVertices`, `largestInducedTreeSize` → turn the five stubs into concrete skeletons, starting with `graphSquare_dist`.
2. Sanity check: confirm a witness graph with $r=2,d=4,p=3$ exists (else Lemma E is vacuous). Constructing the smallest such graph and verifying $t\ge 6$ makes a good regression test.
