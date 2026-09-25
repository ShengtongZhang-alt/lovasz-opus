/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.GapCut

/-!
# Long paths from the spectral gap (Section 3.2, before Section 3.3)

DAG node `L3.dfs` of `docs/BLUEPRINT.md`.
-/

universe u

namespace Lovasz

open Finset

/-- **Depth-first-search path.** A weighted graph on `M` vertices with degrees in `[aD, bD]`
and normalized gap `σ ∈ (0, 1]` has a path with at least `c σ M` vertices. -/
theorem exists_long_path (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V] (H : WGraph V) (D σ : ℝ),
        0 < D → H.DegBetween (a * D) (b * D) → H.HasGap σ → 0 < σ → σ ≤ 1 →
        ∃ x y, ∃ p : H.supp.Walk x y, p.IsPath ∧ c * σ * Fintype.card V ≤ p.support.length := by
  sorry

end Lovasz
