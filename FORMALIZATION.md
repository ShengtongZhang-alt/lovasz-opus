# Formalization notes: paper ↔ Lean

This file records how Theorem 1.1 of [`docs/Polylog_Cayley.pdf`](docs/Polylog_Cayley.pdf)
("Hamilton cycles in Cayley graphs of polylogarithmic degree") is rendered in
[`Challenge.lean`](Challenge.lean), and every modelling decision behind that rendering.

## The theorem

> **Theorem 1.1 (Proposed theorem).** There are absolute constants $C, n_0 > 0$ such that every
> connected Cayley graph on $n \ge n_0$ vertices and of degree at least
> $C (\log n)^{13} / \log\log n$ contains a Hamilton cycle.

Conventions fixed by the paper (Section 2): natural logarithms; $X = \mathrm{Cay}(G,S)$,
$n = |G|$, $d = |S|$, $L = \log n$, where $S = S^{-1} \subseteq G \setminus \{1\}$ and
$\langle S\rangle = G$; edges have the form $x \sim xs$; graphs are simple.

Lean (`Challenge.lean`):

```lean
theorem Lovasz.hamiltonian_of_polylog_degree :
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S : Finset G),
        IsConnectionSet S →
        (cayleyGraph S).Connected →
        n₀ ≤ Fintype.card G →
        C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        (cayleyGraph S).IsHamiltonian
```

## Correspondence

| Paper | Lean | Notes |
|---|---|---|
| finite group $G$ | `G : Type u` with `[Group G] [Fintype G] [DecidableEq G]` | Universe-polymorphic. `DecidableEq` is needed only because Mathlib's `Walk.IsHamiltonian` counts occurrences in a list; any two instances agree (`Subsingleton`). |
| $S = S^{-1} \subseteq G\setminus\{1\}$ | `S : Finset G`, `IsConnectionSet S := (∀ s ∈ S, s⁻¹ ∈ S) ∧ 1 ∉ S` | The paper's standing hypothesis (Section 2). |
| $X = \mathrm{Cay}(G,S)$, edges $x \sim xs$ | `cayleyGraph S := SimpleGraph.mulCayley (S : Set G)` | Mathlib: `x ∼ y ↔ x ≠ y ∧ (x⁻¹y ∈ S ∨ y⁻¹x ∈ S)`. For a connection set this is exactly `x⁻¹ y ∈ S`, i.e. `y = x s` (sanity lemma `cayleyGraph_adj_iff`). Simple graph, as in the paper. |
| "connected Cayley graph", $\langle S \rangle = G$ | `(cayleyGraph S).Connected` | The theorem says "connected"; the sanity lemma `cayleyGraph_connected_iff` proves this is equivalent to `Subgroup.closure S = ⊤`, the paper's $\langle S\rangle = G$. |
| $n = \lvert G\rvert$ | `Fintype.card G` | |
| degree $d = \lvert S\rvert$ | `S.card` | The Cayley graph of a connection set is `|S|`-regular (sanity lemma `cayleyGraph_degree`), so "degree" is unambiguous. |
| $\log$ natural | `Real.log` | |
| $C(\log n)^{13}/\log\log n$ | `C * Real.log n ^ 13 / Real.log (Real.log n)` | Parsed as `(C * (log n)^13) / log (log n)`. |
| $n \ge n_0$ | `n₀ ≤ Fintype.card G`, `n₀ : ℕ`, `0 < n₀` | |
| $C > 0$ | `0 < C`, `C : ℝ` | |
| "contains a Hamilton cycle" | `(cayleyGraph S).IsHamiltonian` | Mathlib: `Fintype.card G ≠ 1 → ∃ a (p : Walk a a), p.IsHamiltonianCycle`. For `n ≥ n₀ ≥ 2` this is the existence of a Hamilton cycle (sanity lemma `isHamiltonian_gives_cycle`). |

## Modelling decisions

1. **Quantifier order.** `∃ C n₀` precede `∀ G S`, so the constants are absolute, as in the
   paper. The statement is universe-polymorphic in `G : Type u`; for each universe the constants
   may a priori depend on the universe, which is harmless (every finite group is isomorphic to
   one in `Type 0`, and the proof in `Lovasz/Main.lean` does not depend on the universe).
2. **Connectivity.** Stated as `(cayleyGraph S).Connected` (the words of the theorem); the paper's
   convention `⟨S⟩ = G` is equivalent (sanity lemma).
3. **Degree.** The paper writes $d = |S|$. We use `S.card`; the sanity lemma shows it equals the
   graph degree of every vertex. We deliberately keep the hypotheses `S = S⁻¹` and `1 ∉ S`:
   Mathlib's `mulCayley` would silently symmetrize `S` and drop `1`, so without them `S.card`
   could exceed the degree by one (if `1 ∈ S`) or undercount it (if `S` is not symmetric).
4. **Junk values.** `Real.log` is `0` on `[0, 1]` and division by `0` is `0` in Lean. For
   `n ≥ 3`, `log log n > 0` (sanity lemma `log_log_pos`), so the threshold is a genuine positive
   real number whenever `n₀ ≥ 3`; since `n₀` is existentially quantified, the junk values at
   `n ≤ 2` cannot make the statement weaker than the paper's. They also cannot make it
   vacuous: for every `C` and `n₀` there are groups satisfying all hypotheses (sanity lemma
   `hypotheses_satisfiable`, via complete Cayley graphs of cyclic groups).
5. **Hamiltonicity convention.** Mathlib's `IsHamiltonian` treats the one-vertex graph as
   Hamiltonian and `K₂` as not Hamiltonian. The latter is a connected Cayley graph
   (`Cay(ℤ/2, {1})`, sanity lemma `small_counterexample`), so some lower bound `n ≥ n₀` is
   genuinely needed; the paper provides it.
6. **Natural numbers.** No truncated subtraction or natural division occurs in the statement:
   the threshold is computed in `ℝ` and `S.card` is cast to `ℝ`.

## Hypotheses deliberately absent

* No hypothesis that `S` generates `G` separately from connectivity (they are equivalent).
* No upper bound on the degree, no abelianness, no normality assumption — none is in the paper.

## Known discrepancies

None in the statement.

## Definitions used only by the proof

`Lovasz/Defs.lean` defines the objects of the intermediate lemmas (weighted graphs, the
normalized gap, matching-absorbing pairs, routers, signed incidence systems, finite probability
distributions). They are not part of the audited statement; their choices are recorded in
[`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). In particular:

* The **normalized upper gap** `1 - λ₂(N_H) ≥ σ` is defined by the variational formula (2.1):
  `WGraph.HasGap H σ :↔ ∀ f, ∃ z, σ ∑_x d_H(x)(f_x - z)^2 ≤ ∑_{xy ∈ E(H)} a_{xy}(f_x - f_y)^2`.
  For positive degrees this is the Courant–Fischer characterization of `1 - λ₂`.
* **Matching-absorbing** (Definition 3.1) is stated through path systems: for every perfect
  matching `J` of `E` there is `P ≤ H` with `E`-vertices of degree one, all others of degree two,
  and `P ⊔ J` connected; then the 2-regular multigraph `P + J` is one Hamilton cycle containing
  every edge of `J`. The requirement that `E` be finite, nonempty and of even size, implicit in
  Definition 3.1 ("Let `E` have positive even size"), is part of the definition.
