/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Template
import Lovasz.WeightedPartition
import Lovasz.Connector
import Lovasz.Perturbation

/-!
# Sections 5–7: the global decomposition

DAG node `GD` of `docs/BLUEPRINT.md`: the output of the weighted partition (Proposition 5.3),
the connecting system (Proposition 6.1), and the parameter check of Section 7, packaged as the
hypotheses of Lemma 3.8 together with the hypotheses of Theorem 3.2 for every part.
-/

universe u

namespace Lovasz

/-- **Sections 5–7.** There is a weight floor `ω > 0` such that, for any constants `c, C > 0`
(those of Theorem 3.2 for `ω`), every connected Cayley graph `X = Cay(G, S)` on `n ≥ n₀`
vertices with `d ≥ C₀ L^{13} / log L` admits: a reserved set `W`, a partition of `G \ W` into
parts carrying bipartite weighted graphs `H i` (supported on edges of `X`), and a connecting
system `M` (a matching plus one path `a_H w_H b_H` per reserved vertex), such that the
hypotheses of Lemma 3.8 hold and every `(H i, E_i)` satisfies the hypotheses of Theorem 3.2,
where `E_i` is the set of endpoints of `M` in part `i`. -/
theorem global_decomposition :
    ∃ ω : ℝ, 0 < ω ∧ ∀ c C : ℝ, 0 < c → 0 < C →
      ∃ C₀ : ℝ, ∃ n₀ : ℕ, 0 < C₀ ∧ 0 < n₀ ∧
        ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S : Finset G),
          IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
          C₀ * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤
            S.card →
          ∃ (t : ℕ) (part : Fin t → Finset G) (W : Set G) (M : SimpleGraph G)
            (H : ∀ i, WGraph (part i)) (col : ∀ i, part i → Bool)
            (E : ∀ i, Finset (part i)) (N ℓ : Fin t → ℕ) (η D σ L g : ℝ),
            IsMergingData (cayleyGraph S) part W M (fun i => (H i).supp) ∧
            (∀ i, (E i : Set (part i)) = connectorEnds M (part i)) ∧
            ∀ i, LocalAbsorptionHyp ω c C (H i) (col i) (N i) (ℓ i) η D σ L g (E i) := by
  sorry

end Lovasz
