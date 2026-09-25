/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.TraceConcentration
import Lovasz.SwapRounding

/-!
# Lemma 2.2: column sampling

DAG node `L2.2` of `docs/BLUEPRINT.md`. The paper derives it from the one-sided matrix
Bernstein inequality (2.5); in this DAG the retention step is instead the special case of
Lemma 4.3 in which every move changes one coordinate (independent Bernoulli retention), which
changes the constant in front of `c √t` by a universal factor.
-/

namespace Lovasz

open Finset

open Classical in
/-- **Lemma 2.2 (Column sampling).** Let `F` be an `r × s` real matrix with `‖F‖ ≤ a` and all
columns of Euclidean norm at most `c`, and let `I` be a uniform `k`-subset of the columns,
`q = k/s`. For `t > 0`, `P(‖F[:, I]‖ > √q a + C c √t) ≤ r (s+1) e^{-t}` for a universal
constant `C` (stated by counting `k`-subsets; the operator norm is expressed through the
quadratic form). -/
theorem column_sampling :
    ∃ C : ℝ, 0 < C ∧ ∀ {r s : ℕ} (F : Matrix (Fin r) (Fin s) ℝ) (a c : ℝ),
      (∀ v : Fin s → ℝ, ∑ i, (∑ j, F i j * v j) ^ 2 ≤ a ^ 2 * ∑ j, v j ^ 2) →
      (∀ j, ∑ i, F i j ^ 2 ≤ c ^ 2) → 0 ≤ a → 0 ≤ c →
      ∀ k : ℕ, k ≤ s → ∀ t : ℝ, 0 < t →
        ((((univ : Finset (Fin s)).powersetCard k).filter fun I => ∃ v : Fin s → ℝ,
            (Real.sqrt ((k : ℝ) / s) * a + C * c * Real.sqrt t) ^ 2 * ∑ j ∈ I, v j ^ 2 <
              ∑ i, (∑ j ∈ I, F i j * v j) ^ 2).card : ℝ) ≤
          r * (s + 1) * Real.exp (-t) * s.choose k := by
  sorry

end Lovasz
