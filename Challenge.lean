/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Mathlib

/-!
# Statement surface

The Mathlib-only formal statement of Theorem 1.1 of `docs/Polylog_Cayley.pdf`
("Hamilton cycles in Cayley graphs of polylogarithmic degree"), together with every definition
it uses. See `FORMALIZATION.md` for the paper-to-Lean correspondence.

Conventions of the paper (Section 2): `X = Cay(G, S)`, `n = |G|`, `d = |S|`, `L = log n`
(natural logarithm), where `S = S⁻¹ ⊆ G \ {1}` and `⟨S⟩ = G`; edges have the form `x ∼ xs`;
graphs are simple.
-/

universe u

namespace Lovasz

open SimpleGraph

/-- The paper's standing hypothesis on a connection set (Section 2): `S = S⁻¹` and `1 ∉ S`. -/
def IsConnectionSet {G : Type*} [Group G] (S : Finset G) : Prop :=
  (∀ s ∈ S, s⁻¹ ∈ S) ∧ (1 : G) ∉ S

/-- The Cayley graph `Cay(G, S)`: the simple graph on `G` whose edges are `x ∼ x * s` for
`s ∈ S`. This is Mathlib's `SimpleGraph.mulCayley`. -/
abbrev cayleyGraph {G : Type*} [Group G] (S : Finset G) : SimpleGraph G :=
  mulCayley (S : Set G)

/-- **Theorem 1.1** of `docs/Polylog_Cayley.pdf` (proposed theorem).

There are absolute constants `C, n₀ > 0` such that every connected Cayley graph
`X = Cay(G, S)` on `n ≥ n₀` vertices and of degree `d = |S|` at least
`C (log n)^13 / log log n` contains a Hamilton cycle.

Here `G` is a finite group, `S ⊆ G` is a connection set (`S = S⁻¹`, `1 ∉ S`), so that `X` is
`|S|`-regular, and `log` is the natural logarithm `Real.log`. -/
theorem hamiltonian_of_polylog_degree :
    ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S : Finset G),
        IsConnectionSet S →
        (cayleyGraph S).Connected →
        n₀ ≤ Fintype.card G →
        C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card →
        (cayleyGraph S).IsHamiltonian := by
  sorry

end Lovasz
