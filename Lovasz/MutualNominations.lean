/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Chernoff

/-!
# Lemma 6.4: mutual nominations

DAG node `L6.4` of `docs/BLUEPRINT.md`. The negative-association argument of the paper is
internal to the proof; the statement records what Section 6.4 uses: a random matching with
edge marginals `p`, an independent marking with probability `1/128`, and Chernoff bounds for
weighted counts (coefficients in `[0, 2]`) of the matching, of the marked edges, and of the
unmarked edges.
-/

namespace Lovasz

open Finset

/-- **Lemma 6.4 (Mutual nominations).** Let `Y` have maximum degree at most `k` and
`0 ≤ p ≤ k^{-2}`. There is a random pair `(R, Z)` of edge sets of `Y`, `Z ⊆ R`, with `R` a
matching, `P(e ∈ R) = p` and `P(e ∈ Z) = p/128` for every edge, such that each of the weighted
counts `∑_{e ∈ R} c_e`, `∑_{e ∈ Z} c_e`, `∑_{e ∈ R \ Z} c_e` (coefficients `c_e ∈ [0, 2]`) with
mean `m` satisfies `P(X ≥ m + t) ≤ exp(-t² / (4(m + t/3)))` and `P(X ≤ m - t) ≤ exp(-t²/(4m))`. -/
theorem mutual_nominations {V : Type*} [Fintype V] [DecidableEq V] (Y : SimpleGraph V)
    [DecidableRel Y.Adj] (k : ℕ) (hk : ∀ v, Y.degree v ≤ k) (p : ℝ) (hp : 0 ≤ p)
    (hpk : p * k ^ 2 ≤ 1) :
    ∃ μ : FinDist (Finset (Sym2 V) × Finset (Sym2 V)),
      (∀ RZ ∈ μ.support, RZ.2 ⊆ RZ.1 ∧ RZ.1 ⊆ Y.edgeFinset ∧
        ∀ e ∈ RZ.1, ∀ f ∈ RZ.1, e ≠ f → ∀ v, v ∈ e → v ∉ f) ∧
      (∀ e ∈ Y.edgeFinset, μ.P (fun RZ => e ∈ RZ.1) = p ∧ μ.P (fun RZ => e ∈ RZ.2) = p / 128) ∧
      ∀ (c : Sym2 V → ℝ), (∀ e, 0 ≤ c e ∧ c e ≤ 2) → ∀ t : ℝ, 0 ≤ t →
        ∀ sel : Finset (Sym2 V) × Finset (Sym2 V) → Finset (Sym2 V),
          (sel = Prod.fst ∨ sel = Prod.snd ∨ sel = fun RZ => RZ.1 \ RZ.2) →
          (μ.P (fun RZ => μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e) + t ≤ ∑ e ∈ sel RZ, c e) ≤
              Real.exp (-(t ^ 2) / (4 * (μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e) + t / 3)))) ∧
          (μ.P (fun RZ => ∑ e ∈ sel RZ, c e ≤ μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e) - t) ≤
              Real.exp (-(t ^ 2) / (4 * μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e)))) := by
  sorry

end Lovasz
