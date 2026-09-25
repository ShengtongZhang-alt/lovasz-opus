/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Scalar Chernoff bounds (classical input)

DAG node `K.chernoff` of `docs/BLUEPRINT.md`: the scalar Chernoff bounds of Section 2.2 of the
paper, for independent variables in `[0,1]` and for sampling without replacement ("their
exponents have the usual order `t² / (µ + t)`").
-/

namespace Lovasz

open Finset

/-- The product of finitely supported distributions (independent coordinates). -/
def FinDist.pi {ι α : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist α) :
    FinDist (ι → α) where
  support := Fintype.piFinset fun i => (μ i).support
  prob := fun x => ∏ i, (μ i).prob (x i)
  prob_nonneg := fun x => Finset.prod_nonneg fun i _ => (μ i).prob_nonneg (x i)
  sum_prob := by
    rw [← Finset.prod_univ_sum]
    simp [FinDist.sum_prob]

/-- **Chernoff–Bernstein upper tail.** For independent variables `X_i ∈ [0,1]` with
`µ = ∑ E X_i`, `P(∑ X_i ≥ µ + t) ≤ exp(-t² / (2(µ + t/3)))`. -/
theorem chernoff_upper {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist ℝ)
    (hμ : ∀ i, ∀ x ∈ (μ i).support, 0 ≤ x ∧ x ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (FinDist.pi μ).P (fun x => ∑ i, (μ i).expect id + t ≤ ∑ i, x i) ≤
      Real.exp (-(t ^ 2) / (2 * (∑ i, (μ i).expect id + t / 3))) := by
  sorry

/-- **Chernoff lower tail.** For independent variables `X_i ∈ [0,1]` with `µ = ∑ E X_i`,
`P(∑ X_i ≤ µ - t) ≤ exp(-t² / (2µ))`. -/
theorem chernoff_lower {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist ℝ)
    (hμ : ∀ i, ∀ x ∈ (μ i).support, 0 ≤ x ∧ x ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (FinDist.pi μ).P (fun x => ∑ i, x i ≤ ∑ i, (μ i).expect id - t) ≤
      Real.exp (-(t ^ 2) / (2 * ∑ i, (μ i).expect id)) := by
  sorry

/-- **Sampling without replacement, upper tail.** For weights `a_i ∈ [0,1]` and a uniform
`k`-subset `I` of `ι` (`|ι| = N`), with `µ = (k/N) ∑ a_i`,
`P(∑_{i∈I} a_i ≥ µ + t) ≤ exp(-t² / (2(µ + t/3)))` (stated by counting subsets). -/
theorem hypergeometric_upper {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((((univ : Finset ι).powersetCard k).filter fun I =>
        (k : ℝ) / Fintype.card ι * ∑ i, a i + t ≤ ∑ i ∈ I, a i).card : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * ((k : ℝ) / Fintype.card ι * ∑ i, a i + t / 3))) *
        (Fintype.card ι).choose k := by
  sorry

/-- **Sampling without replacement, lower tail.** With `µ = (k/N) ∑ a_i`,
`P(∑_{i∈I} a_i ≤ µ - t) ≤ exp(-t² / (2µ))`. -/
theorem hypergeometric_lower {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((((univ : Finset ι).powersetCard k).filter fun I =>
        ∑ i ∈ I, a i ≤ (k : ℝ) / Fintype.card ι * ∑ i, a i - t).card : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * ((k : ℝ) / Fintype.card ι * ∑ i, a i))) *
        (Fintype.card ι).choose k := by
  sorry

end Lovasz
