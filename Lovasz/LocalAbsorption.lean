/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.GapCut
import Lovasz.LongPath
import Lovasz.Perturbation
import Lovasz.RobustHall
import Lovasz.SpectralConnection
import Lovasz.Comparator
import Lovasz.Router
import Lovasz.ShortCycles
import Lovasz.BipartiteSampling
import Lovasz.ColumnSampling
import Lovasz.Chernoff

/-!
# Theorem 3.2: local absorption

DAG node `T3.2` of `docs/BLUEPRINT.md`. Its proof is Section 3.3 of the paper, from the nodes
of Sections 2 and 3.
-/

universe u

namespace Lovasz

/-- **Theorem 3.2 (Local absorption).** Fix `ω > 0`. There are constants `c, C > 0` such that
if `H` is bipartite with classes of size `N`, weights in `[ω, 1]`, degrees `(1 ± η) D`,
normalized upper gap at least `σ ∈ (0, 1/10]`, `η ≤ cσ`, `L ≥ max {log (2N), 10}`, `g ≥ 4`,
`D ≥ C σ^{-9/2} L² g`, `g ≥ C L / log (2 + σ^{5/2} D / L)`, and `E` contains `ℓ ≥ 1` vertices
of each class with `ℓ ≤ c σ^{5/2} N / (L g)` and `max_v d_H(v, E) ≤ c σ^{5/2} D / L`, then
`(supp H, E)` is matching-absorbing. -/
theorem local_absorption (ω : ℝ) (hω : 0 < ω) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α] (H : WGraph α) (col : α → Bool)
        (N ℓ : ℕ) (η D σ L g : ℝ) (E : Finset α),
        LocalAbsorptionHyp ω c C H col N ℓ η D σ L g E →
        IsMatchingAbsorbing H.supp (E : Set α) := by
  sorry

end Lovasz
