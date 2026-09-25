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

## Proof outline

Every vertex `v` independently nominates one incident edge `e` together with a bit `b`, with
probability `√p · wt b` (`wt true = 1/128`, `wt false = 127/128`), and nothing with the
remaining probability `1 - deg(v) √p`. An edge is retained (`R`) when both endpoints nominate
it, and marked (`Z`) when moreover the bit of its distinguished endpoint `e.out.1` is `true`.
Each of `R`, `Z`, `R \ Z` is the set of edges `e` all of whose vertex events `Ev s v e` hold,
and at every vertex the events of distinct incident edges are disjoint. For such families the
correlation inequality `E ∏_e (1 + γ_e 1_e) ≤ ∏_e (1 + γ_e P(e))` holds when all `γ_e ≥ 0` or
all `γ_e ∈ [-1, 0]` (`moment_aux`, by resampling one vertex at a time); this replaces negative
association and gives the exponential-moment bound `mgf_bound`, from which the Chernoff tails
follow (`tails_of_mgf`).
-/

noncomputable section

namespace Lovasz

open Finset

namespace MutualNom

variable {α β ι κ Ω : Type*}

lemma two_mul_three_pow_le_factorial (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

/-- Bernstein's bound on the exponential: `e^x ≤ 1 + x + x² / (2(1 - x/3))` for `0 ≤ x < 3`. -/
lemma exp_le_bernstein (x : ℝ) (h0 : 0 ≤ x) (h3 : x < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  have hs : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have hs2 := (hasSum_nat_add_iff' 2).mpr hs
  have hg : HasSum (fun n : ℕ => x ^ 2 / 2 * (x / 3) ^ n) (x ^ 2 / 2 * (1 - x / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  have hle := hasSum_le (fun n => ?_) hs2 hg
  · simp [Finset.sum_range_succ] at hle
    have h1 : x ^ 2 / 2 * (1 - x / 3)⁻¹ = x ^ 2 / (2 * (1 - x / 3)) := by
      field_simp
    linarith
  · have hf : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast two_mul_three_pow_le_factorial n
    have h3n : (0 : ℝ) < 3 ^ n := by positivity
    rw [div_pow, pow_add]
    calc x ^ n * x ^ 2 / ((n + 2).factorial : ℝ) ≤ x ^ n * x ^ 2 / (2 * 3 ^ n) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hf
      _ = x ^ 2 / 2 * (x ^ n / 3 ^ n) := by field_simp

/-- `e^{-x} ≤ 1 - x + x²/2` for `x ≥ 0`. -/
lemma exp_neg_le_quadratic (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have hQ : 0 < 1 - x + x ^ 2 / 2 := by nlinarith
  have h2 : 1 ≤ Real.exp x * (1 - x + x ^ 2 / 2) := by nlinarith
  calc Real.exp (-x) = Real.exp (-x) * 1 := by ring
    _ ≤ Real.exp (-x) * (Real.exp x * (1 - x + x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = 1 - x + x ^ 2 / 2 := by
        rw [← mul_assoc, ← Real.exp_add]; simp

lemma upper_exp_choice (μ s : ℝ) (hμ : 0 ≤ μ) (hs : 0 ≤ s) :
    ∃ l : ℝ, 0 ≤ l ∧ -l * (μ + s) + (Real.exp l - 1) * μ ≤ -(s ^ 2) / (2 * (μ + s / 3)) := by
  rcases eq_or_lt_of_le hμ with h | h
  · subst h
    refine ⟨3, by norm_num, ?_⟩
    rcases eq_or_lt_of_le hs with hs' | hs'
    · subst hs'; simp
    · have : -(s ^ 2) / (2 * (0 + s / 3)) = -(3 * s / 2) := by
        field_simp; ring
      rw [this]; nlinarith
  · set D := μ + s / 3 with hD
    have hDpos : 0 < D := by positivity
    refine ⟨s / D, by positivity, ?_⟩
    have hl3 : s / D < 3 := by
      rw [div_lt_iff₀ hDpos]; linarith
    have hb := exp_le_bernstein (s / D) (by positivity) hl3
    have h1 : 1 - s / D / 3 = μ / D := by field_simp; ring
    have h2 : (s / D) ^ 2 / (2 * (1 - s / D / 3)) = s ^ 2 / (2 * μ * D) := by
      rw [h1]; field_simp
    rw [h2] at hb
    have key : -(s / D) * (μ + s) + (1 + s / D + s ^ 2 / (2 * μ * D) - 1) * μ =
        -(s ^ 2) / (2 * D) := by
      field_simp; ring
    calc -(s / D) * (μ + s) + (Real.exp (s / D) - 1) * μ
        ≤ -(s / D) * (μ + s) + (1 + s / D + s ^ 2 / (2 * μ * D) - 1) * μ := by
          nlinarith
      _ = _ := key

lemma lower_exp_choice (μ s : ℝ) (hμ : 0 < μ) (hs : 0 ≤ s) :
    ∃ l : ℝ, 0 ≤ l ∧ l * (μ - s) + (Real.exp (-l) - 1) * μ ≤ -(s ^ 2) / (2 * μ) := by
  refine ⟨s / μ, by positivity, ?_⟩
  have hb := exp_neg_le_quadratic (s / μ) (by positivity)
  have key : s / μ * (μ - s) + (1 - s / μ + (s / μ) ^ 2 / 2 - 1) * μ = -(s ^ 2) / (2 * μ) := by
    field_simp; ring
  calc s / μ * (μ - s) + (Real.exp (-(s / μ)) - 1) * μ
      ≤ s / μ * (μ - s) + (1 - s / μ + (s / μ) ^ 2 / 2 - 1) * μ := by nlinarith
    _ = _ := key



open Classical in
/-- The `0/1` indicator of a proposition. -/
def ind (P : Prop) : ℝ := if P then 1 else 0

lemma ind_of {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]
lemma ind_of_not {P : Prop} (h : ¬P) : ind P = 0 := by simp [ind, h]
lemma ind_nonneg (P : Prop) : 0 ≤ ind P := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (P : Prop) : ind P ≤ 1 := by unfold ind; split_ifs <;> norm_num
lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by rw [propext h]

lemma prod_ind (s : Finset ι) (P : ι → Prop) : ∏ i ∈ s, ind (P i) = ind (∀ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ind]
  | insert a s ha ih =>
    rw [prod_insert ha, ih]
    by_cases h1 : P a <;> by_cases h2 : ∀ i ∈ s, P i <;> simp [ind, h1, h2]

lemma prod_ind_nonneg (s : Finset ι) (P : ι → Prop) : 0 ≤ ∏ i ∈ s, ind (P i) :=
  prod_nonneg fun _ _ => ind_nonneg _

lemma prod_ind_le_one (s : Finset ι) (P : ι → Prop) : ∏ i ∈ s, ind (P i) ≤ 1 := by
  rw [prod_ind]; exact ind_le_one _

/-! ### Elementary facts on `FinDist` -/

lemma P_eq_expect (μ : FinDist α) (E : α → Prop) : μ.P E = μ.expect (fun a => ind (E a)) := by
  unfold FinDist.P FinDist.expect ind
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : E a <;> simp [h]

lemma expect_mono (μ : FinDist α) {f g : α → ℝ} (h : ∀ a ∈ μ.support, f a ≤ g a) :
    μ.expect f ≤ μ.expect g :=
  sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (h a ha) (μ.prob_nonneg a)

lemma expect_nonneg (μ : FinDist α) {f : α → ℝ} (h : ∀ a ∈ μ.support, 0 ≤ f a) :
    0 ≤ μ.expect f :=
  sum_nonneg fun a ha => mul_nonneg (μ.prob_nonneg a) (h a ha)

lemma expect_congr (μ : FinDist α) {f g : α → ℝ} (h : ∀ a ∈ μ.support, f a = g a) :
    μ.expect f = μ.expect g :=
  sum_congr rfl fun a ha => by rw [h a ha]

lemma expect_const (μ : FinDist α) (c : ℝ) : μ.expect (fun _ => c) = c := by
  unfold FinDist.expect; rw [← sum_mul, μ.sum_prob, one_mul]

lemma expect_add (μ : FinDist α) (f g : α → ℝ) :
    μ.expect (fun a => f a + g a) = μ.expect f + μ.expect g := by
  unfold FinDist.expect; rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => by ring

lemma expect_mul_const (μ : FinDist α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun a => f a * c) = μ.expect f * c := by
  unfold FinDist.expect; rw [sum_mul]; exact sum_congr rfl fun a _ => by ring

lemma expect_const_mul (μ : FinDist α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun a => c * f a) = c * μ.expect f := by
  unfold FinDist.expect; rw [mul_sum]; exact sum_congr rfl fun a _ => by ring

lemma expect_sum (μ : FinDist α) (s : Finset κ) (f : κ → α → ℝ) :
    μ.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, μ.expect (f i) := by
  unfold FinDist.expect; simp_rw [mul_sum]; rw [sum_comm]

lemma P_le_one (μ : FinDist α) (E : α → Prop) : μ.P E ≤ 1 := by
  rw [P_eq_expect]
  calc μ.expect (fun a => ind (E a)) ≤ μ.expect (fun _ => 1) :=
        expect_mono μ fun a _ => ind_le_one _
    _ = 1 := expect_const μ 1

lemma P_nonneg (μ : FinDist α) (E : α → Prop) : 0 ≤ μ.P E := by
  rw [P_eq_expect]; exact expect_nonneg μ fun a _ => ind_nonneg _

lemma P_true (μ : FinDist α) (E : α → Prop) (h : ∀ a, E a) : μ.P E = 1 := by
  rw [P_eq_expect, expect_congr μ (g := fun _ => 1) fun a _ => ind_of (h a), expect_const]

/-- Exponential Markov inequality. -/
lemma P_ge_le_exp (μ : FinDist α) (X : α → ℝ) (b θ : ℝ) (hθ : 0 ≤ θ) :
    μ.P (fun a => b ≤ X a) ≤ Real.exp (-θ * b) * μ.expect (fun a => Real.exp (θ * X a)) := by
  unfold FinDist.P FinDist.expect
  rw [mul_sum]
  refine sum_le_sum fun a _ => ?_
  split_ifs with h
  · have h1 : 1 ≤ Real.exp (-θ * b) * Real.exp (θ * X a) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    nlinarith [μ.prob_nonneg a]
  · have := μ.prob_nonneg a
    positivity

/-! ### Pushforward -/

/-- The pushforward of a finitely supported distribution. -/
def fdMap [DecidableEq β] (φ : α → β) (μ : FinDist α) : FinDist β where
  support := μ.support.image φ
  prob b := ∑ a ∈ μ.support with φ a = b, μ.prob a
  prob_nonneg b := sum_nonneg fun a _ => μ.prob_nonneg a
  sum_prob := by
    rw [sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem φ ha)]
    exact μ.sum_prob

lemma expect_fdMap [DecidableEq β] (φ : α → β) (μ : FinDist α) (f : β → ℝ) :
    (fdMap φ μ).expect f = μ.expect (fun a => f (φ a)) := by
  unfold FinDist.expect fdMap
  simp only
  simp_rw [sum_mul]
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem φ ha)
    (f := fun a => μ.prob a * f (φ a))]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a ha => ?_
  rw [(mem_filter.1 ha).2]

lemma P_fdMap [DecidableEq β] (φ : α → β) (μ : FinDist α) (E : β → Prop) :
    (fdMap φ μ).P E = μ.P (fun a => E (φ a)) := by
  rw [P_eq_expect, P_eq_expect, expect_fdMap]

/-! ### Product distributions -/

section Pi

variable [Fintype ι] [DecidableEq ι]

lemma pi_expect_prod (q : ι → FinDist Ω) (g : ι → Ω → ℝ) :
    (FinDist.pi q).expect (fun ν => ∏ i, g i (ν i)) = ∏ i, (q i).expect (g i) := by
  unfold FinDist.expect FinDist.pi
  simp only
  rw [prod_univ_sum]
  refine sum_congr rfl fun ν _ => ?_
  rw [prod_mul_distrib]

lemma prod_update_prob (q : ι → FinDist Ω) (w : ι) (ν : ι → Ω) (ω : Ω) :
    ∏ i, (q i).prob (Function.update ν w ω i) =
      (q w).prob ω * ∏ i ∈ univ.erase w, (q i).prob (ν i) := by
  rw [← mul_prod_erase univ _ (mem_univ w), Function.update_self]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

/-- Resampling one coordinate of a product distribution does not change it. -/
lemma pi_expect_resample (q : ι → FinDist Ω) (w : ι) (f : (ι → Ω) → ℝ) :
    (FinDist.pi q).expect f =
      (FinDist.pi q).expect (fun ν => (q w).expect (fun ω => f (Function.update ν w ω))) := by
  unfold FinDist.expect FinDist.pi
  simp only
  set S := Fintype.piFinset fun i => (q i).support
  set T := (q w).support
  have hL : ∑ ν ∈ S, (∏ i, (q i).prob (ν i)) * f ν =
      ∑ p ∈ S ×ˢ T, (∏ i, (q i).prob (p.1 i)) * ((q w).prob p.2 * f p.1) := by
    rw [sum_product]
    refine sum_congr rfl fun ν _ => ?_
    dsimp only
    rw [← mul_sum, ← sum_mul, (q w).sum_prob, one_mul]
  have hR : ∑ ν ∈ S, (∏ i, (q i).prob (ν i)) *
        ∑ ω ∈ T, (q w).prob ω * f (Function.update ν w ω) =
      ∑ p ∈ S ×ˢ T, (∏ i, (q i).prob (p.1 i)) *
        ((q w).prob p.2 * f (Function.update p.1 w p.2)) := by
    rw [sum_product]
    refine sum_congr rfl fun ν _ => ?_
    dsimp only
    rw [mul_sum]
  rw [hL, hR]
  have hmem : ∀ p ∈ S ×ˢ T, (Function.update p.1 w p.2, p.1 w) ∈ S ×ˢ T := by
    intro p hp
    rw [mem_product] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    rw [Fintype.mem_piFinset] at h1
    refine ⟨?_, h1 w⟩
    rw [Fintype.mem_piFinset]
    intro i
    dsimp only
    by_cases hi : i = w
    · subst hi; rw [Function.update_self]; exact h2
    · rw [Function.update_of_ne hi]; exact h1 i
  refine sum_nbij' (fun p => (Function.update p.1 w p.2, p.1 w))
    (fun p => (Function.update p.1 w p.2, p.1 w)) hmem hmem ?_ ?_ ?_
  · intro p _
    simp [Function.update_idem, Function.update_eq_self]
  · intro p _
    simp [Function.update_idem, Function.update_eq_self]
  · intro p _
    simp only
    rw [prod_update_prob, Function.update_idem, Function.update_eq_self,
      ← mul_prod_erase univ _ (mem_univ w)]
    ring

end Pi

/-! ### The correlation inequality -/

/-- All coefficients nonnegative, or all in `[-1, 0]`. -/
def SameSign (x : κ → ℝ) : Prop := (∀ e, 0 ≤ x e) ∨ (∀ e, -1 ≤ x e ∧ x e ≤ 0)

lemma SameSign.one_add_nonneg {x : κ → ℝ} (h : SameSign x) (e : κ) : 0 ≤ 1 + x e := by
  rcases h with h | h
  · linarith [h e]
  · linarith [(h e).1]

lemma SameSign.mul {x t : κ → ℝ} (h : SameSign x) (ht : ∀ e, 0 ≤ t e ∧ t e ≤ 1) :
    SameSign (fun e => x e * t e) := by
  rcases h with h | h
  · exact Or.inl fun e => mul_nonneg (h e) (ht e).1
  · refine Or.inr fun e => ⟨?_, mul_nonpos_of_nonpos_of_nonneg (h e).2 (ht e).1⟩
    nlinarith [h e, ht e]

lemma one_add_sum_le_prod (s : Finset κ) (x : κ → ℝ) (hx : SameSign x) :
    1 + ∑ e ∈ s, x e ≤ ∏ e ∈ s, (1 + x e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have h0 : 0 ≤ x a * ∑ e ∈ s, x e := by
      rcases hx with h | h
      · exact mul_nonneg (h a) (sum_nonneg fun e _ => h e)
      · exact mul_nonneg_of_nonpos_of_nonpos (h a).2 (sum_nonpos fun e _ => (h e).2)
    have h1 := hx.one_add_nonneg a
    nlinarith [mul_le_mul_of_nonneg_left ih h1]

lemma prod_one_add_eq (s : Finset κ) (x : κ → ℝ)
    (h : ∀ e ∈ s, ∀ f ∈ s, e ≠ f → x e * x f = 0) :
    ∏ e ∈ s, (1 + x e) = 1 + ∑ e ∈ s, x e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha,
      ih fun e he f hf hef => h e (mem_insert_of_mem he) f (mem_insert_of_mem hf) hef]
    have h0 : x a * ∑ e ∈ s, x e = 0 := by
      rw [mul_sum]
      exact sum_eq_zero fun f hf =>
        h a (mem_insert_self a s) f (mem_insert_of_mem hf) (fun h' => ha (h' ▸ hf))
    linear_combination h0

/-- The correlation inequality at one vertex: the events of the incident edges are pairwise
disjoint and the other events are sure. -/
lemma one_vertex (r : FinDist Ω) (E : Finset κ) (B : κ → Ω → Prop) (inc : κ → Prop)
    (htriv : ∀ e ω, ¬inc e → B e ω)
    (hdisj : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → inc e → inc f → ∀ ω, B e ω → ¬B f ω)
    (c : κ → ℝ) (hc : SameSign c) :
    r.expect (fun ω => ∏ e ∈ E, (1 + c e * ind (B e ω))) ≤ ∏ e ∈ E, (1 + c e * r.P (B e)) := by
  classical
  set K := ∏ e ∈ E with ¬inc e, (1 + c e) with hK
  have hK0 : 0 ≤ K := prod_nonneg fun e _ => hc.one_add_nonneg e
  have hpt : ∀ ω, ∏ e ∈ E, (1 + c e * ind (B e ω)) =
      (1 + ∑ e ∈ E with inc e, c e * ind (B e ω)) * K := by
    intro ω
    rw [← prod_filter_mul_prod_filter_not E inc]
    congr 1
    · refine prod_one_add_eq _ _ fun e he f hf hef => ?_
      rw [mem_filter] at he hf
      by_cases hb : B e ω
      · rw [ind_of_not (hdisj e he.1 f hf.1 hef he.2 hf.2 ω hb)]; ring
      · rw [ind_of_not hb]; ring
    · exact prod_congr rfl fun e he => by rw [ind_of (htriv e ω (mem_filter.1 he).2), mul_one]
  rw [expect_congr r (fun ω _ => hpt ω), expect_mul_const, expect_add, expect_const,
    expect_sum]
  simp_rw [expect_const_mul, ← P_eq_expect]
  rw [← prod_filter_mul_prod_filter_not E inc]
  have hK' : ∏ e ∈ E with ¬inc e, (1 + c e * r.P (B e)) = K :=
    prod_congr rfl fun e he => by rw [P_true r _ fun ω => htriv e ω (mem_filter.1 he).2, mul_one]
  rw [hK']
  refine mul_le_mul_of_nonneg_right ?_ hK0
  exact one_add_sum_le_prod _ _ (hc.mul fun e => ⟨P_nonneg _ _, P_le_one _ _⟩)

section Pi

variable [Fintype ι] [DecidableEq ι]

/-- The correlation inequality for independent vertices with one-hot events, by induction on
the set of randomized vertices. -/
lemma moment_aux (q : ι → FinDist Ω) (E : Finset κ) (A : ι → κ → Ω → Prop)
    (inc : ι → κ → Prop) (htriv : ∀ v e ω, ¬inc v e → A v e ω)
    (hdisj : ∀ v, ∀ e ∈ E, ∀ f ∈ E, e ≠ f → inc v e → inc v f → ∀ ω, A v e ω → ¬A v f ω)
    (W : Finset ι) : ∀ γ : κ → ℝ, SameSign γ →
      (FinDist.pi q).expect (fun ν => ∏ e ∈ E, (1 + γ e * ∏ v ∈ W, ind (A v e (ν v)))) ≤
        ∏ e ∈ E, (1 + γ e * ∏ v ∈ W, (q v).P (A v e)) := by
  induction W using Finset.induction_on with
  | empty =>
    intro γ _
    simp only [prod_empty, mul_one]
    rw [expect_const]
  | insert w W hw ih =>
    intro γ hγ
    rw [pi_expect_resample q w]
    have hin : ∀ (ν : ι → Ω) ω e, ∏ v ∈ insert w W, ind (A v e (Function.update ν w ω v)) =
        (∏ v ∈ W, ind (A v e (ν v))) * ind (A w e ω) := by
      intro ν ω e
      rw [prod_insert hw, Function.update_self, mul_comm]
      congr 1
      refine prod_congr rfl fun v hv => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hv hw)]
    have hsign : ∀ ν : ι → Ω, SameSign (fun e => γ e * ∏ v ∈ W, ind (A v e (ν v))) :=
      fun ν => hγ.mul fun e => ⟨prod_ind_nonneg _ _, prod_ind_le_one _ _⟩
    calc _ ≤ (FinDist.pi q).expect (fun ν => ∏ e ∈ E,
          (1 + (γ e * (q w).P (A w e)) * ∏ v ∈ W, ind (A v e (ν v)))) := by
          refine expect_mono _ fun ν _ => ?_
          have h1 := one_vertex (q w) E (fun e => A w e) (inc w) (fun e ω h => htriv w e ω h)
            (hdisj w) _ (hsign ν)
          calc (q w).expect (fun ω => ∏ e ∈ E,
                (1 + γ e * ∏ v ∈ insert w W, ind (A v e (Function.update ν w ω v))))
              = (q w).expect (fun ω => ∏ e ∈ E,
                (1 + (γ e * ∏ v ∈ W, ind (A v e (ν v))) * ind (A w e ω))) := by
                refine expect_congr _ fun ω _ => prod_congr rfl fun e _ => ?_
                rw [hin]; ring
            _ ≤ _ := h1
            _ = _ := prod_congr rfl fun e _ => by ring
      _ ≤ ∏ e ∈ E, (1 + (γ e * (q w).P (A w e)) * ∏ v ∈ W, (q v).P (A v e)) :=
          ih _ (hγ.mul fun e => ⟨P_nonneg _ _, P_le_one _ _⟩)
      _ = _ := prod_congr rfl fun e _ => by rw [prod_insert hw]; ring

end Pi

/-! ### From the moment inequality to Chernoff tails -/

lemma tails_of_mgf (ν : FinDist α) (X : α → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hmgf : ∀ θ : ℝ, ν.expect (fun a => Real.exp (θ * X a)) ≤
      Real.exp ((Real.exp (2 * θ) - 1) * m / 2))
    (t : ℝ) (ht : 0 ≤ t) :
    ν.P (fun a => m + t ≤ X a) ≤ Real.exp (-(t ^ 2) / (4 * (m + t / 3))) ∧
      ν.P (fun a => X a ≤ m - t) ≤ Real.exp (-(t ^ 2) / (4 * m)) := by
  constructor
  · obtain ⟨l, hl0, hl⟩ := upper_exp_choice (m / 2) (t / 2) (by positivity) (by positivity)
    have h1 := P_ge_le_exp ν X (m + t) (l / 2) (by positivity)
    have h2 := hmgf (l / 2)
    rw [show 2 * (l / 2) = l by ring] at h2
    calc _ ≤ _ := h1
      _ ≤ Real.exp (-(l / 2) * (m + t)) * Real.exp ((Real.exp l - 1) * m / 2) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (-l * (m / 2 + t / 2) + (Real.exp l - 1) * (m / 2)) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-((t / 2) ^ 2) / (2 * (m / 2 + t / 2 / 3))) := Real.exp_le_exp.mpr hl
      _ = _ := by
          congr 1
          rw [show (2 : ℝ) * (m / 2 + t / 2 / 3) = m + t / 3 by ring, ← div_div]
          congr 1; ring
  · rcases eq_or_lt_of_le hm with h | h
    · subst h
      simp only [mul_zero, div_zero, Real.exp_zero]
      exact P_le_one _ _
    · obtain ⟨l, hl0, hl⟩ := lower_exp_choice (m / 2) (t / 2) (by positivity) (by positivity)
      have h1 : ν.P (fun a => X a ≤ m - t) ≤
          Real.exp (-(l / 2) * -(m - t)) * ν.expect (fun a => Real.exp (l / 2 * -X a)) := by
        have := P_ge_le_exp ν (fun a => -X a) (-(m - t)) (l / 2) (by positivity)
        simpa only [neg_le_neg_iff] using this
      have h2 := hmgf (-(l / 2))
      rw [show 2 * (-(l / 2)) = -l by ring] at h2
      calc _ ≤ _ := h1
        _ = Real.exp (l / 2 * (m - t)) * ν.expect (fun a => Real.exp (-(l / 2) * X a)) := by
            congr 1
            · congr 1; ring
            · congr 1; ext a; congr 1; ring
        _ ≤ Real.exp (l / 2 * (m - t)) * Real.exp ((Real.exp (-l) - 1) * m / 2) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = Real.exp (l * (m / 2 - t / 2) + (Real.exp (-l) - 1) * (m / 2)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp (-((t / 2) ^ 2) / (2 * (m / 2))) := Real.exp_le_exp.mpr hl
        _ = _ := by
            congr 1
            rw [show (2 : ℝ) * (m / 2) = m by ring, ← div_div]
            congr 1; ring

section Pi

variable [Fintype ι] [DecidableEq ι]

/-- The exponential-moment bound for weighted counts of the "all vertex events hold" edges. -/
lemma mgf_bound (q : ι → FinDist Ω) (E : Finset κ) (A : ι → κ → Ω → Prop)
    (inc : ι → κ → Prop) (htriv : ∀ v e ω, ¬inc v e → A v e ω)
    (hdisj : ∀ v, ∀ e ∈ E, ∀ f ∈ E, e ≠ f → inc v e → inc v f → ∀ ω, A v e ω → ¬A v f ω)
    (c : κ → ℝ) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 2) (X : (ι → Ω) → ℝ)
    (hX : ∀ ν, X ν = ∑ e ∈ E, c e * ∏ v, ind (A v e (ν v))) (θ : ℝ) :
    (FinDist.pi q).expect (fun ν => Real.exp (θ * X ν)) ≤
      Real.exp ((Real.exp (2 * θ) - 1) * (FinDist.pi q).expect X / 2) := by
  set Q : κ → ℝ := fun e => ∏ v, (q v).P (A v e) with hQdef
  have hQ : ∀ e, 0 ≤ Q e ∧ Q e ≤ 1 := fun e =>
    ⟨prod_nonneg fun v _ => P_nonneg _ _,
      prod_le_one₀ (fun v _ => P_nonneg _ _) fun v _ => P_le_one _ _⟩
  have hmean : (FinDist.pi q).expect X = ∑ e ∈ E, c e * Q e := by
    rw [expect_congr _ (fun ν _ => hX ν), expect_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [expect_const_mul, pi_expect_prod (g := fun v ω => ind (A v e ω))]
    simp_rw [← P_eq_expect]
    rfl
  set γ : κ → ℝ := fun e => Real.exp (θ * c e) - 1 with hγdef
  have hγ : SameSign γ := by
    rcases le_total 0 θ with h | h
    · left; intro e
      simp only [hγdef, sub_nonneg]
      exact Real.one_le_exp (mul_nonneg h (hc e).1)
    · right; intro e
      simp only [hγdef]
      constructor
      · linarith [Real.exp_pos (θ * c e)]
      · have := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg h (hc e).1)
        linarith
  have hpt : ∀ ν, Real.exp (θ * X ν) = ∏ e ∈ E, (1 + γ e * ∏ v, ind (A v e (ν v))) := by
    intro ν
    rw [hX, mul_sum, Real.exp_sum]
    refine prod_congr rfl fun e _ => ?_
    rw [prod_ind]
    by_cases h : ∀ v ∈ univ, A v e (ν v)
    · rw [ind_of h]; simp [hγdef]
    · rw [ind_of_not h]; simp
  calc (FinDist.pi q).expect (fun ν => Real.exp (θ * X ν))
      = (FinDist.pi q).expect (fun ν => ∏ e ∈ E, (1 + γ e * ∏ v, ind (A v e (ν v)))) :=
        expect_congr _ fun ν _ => hpt ν
    _ ≤ ∏ e ∈ E, (1 + γ e * Q e) := moment_aux q E A inc htriv hdisj univ γ hγ
    _ ≤ ∏ e ∈ E, Real.exp (γ e * Q e) :=
        prod_le_prod₀ (fun e _ => (hγ.mul hQ).one_add_nonneg e)
          fun e _ => by linarith [Real.add_one_le_exp (γ e * Q e)]
    _ = Real.exp (∑ e ∈ E, γ e * Q e) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp ((Real.exp (2 * θ) - 1) * (∑ e ∈ E, c e * Q e) / 2) := by
        apply Real.exp_le_exp.mpr
        rw [mul_sum, sum_div]
        refine sum_le_sum fun e _ => ?_
        have hconv := convexOn_exp.2 (Set.mem_univ (2 * θ)) (Set.mem_univ 0)
          (by linarith [(hc e).1] : (0 : ℝ) ≤ c e / 2)
          (by linarith [(hc e).2] : (0 : ℝ) ≤ 1 - c e / 2) (by ring)
        simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
        rw [show c e / 2 * (2 * θ) = θ * c e by ring] at hconv
        simp only [hγdef]
        nlinarith [(hQ e).1]
    _ = _ := by rw [hmean]

end Pi

/-! ### The mutual-nominations model -/

section Model

variable {V : Type*} [Fintype V] [DecidableEq V] (Y : SimpleGraph V) [DecidableRel Y.Adj]

/-- The marking weights: a nominating vertex attaches the bit `true` with probability `1/128`. -/
def wt (b : Bool) : ℝ := if b then 1 / 128 else 127 / 128

lemma wt_true : wt true = 1 / 128 := by simp [wt]
lemma wt_false : wt false = 127 / 128 := by simp [wt]

/-- The nomination distribution at `v`: each incident edge `e` with a bit `b` has mass
`a · wt b`; nothing is nominated with the remaining mass `1 - deg(v) a`. -/
def nomProb (a : ℝ) (v : V) (ω : Option (Sym2 V × Bool)) : ℝ :=
  ω.elim (1 - Y.degree v * a) fun eb => if eb.1 ∈ Y.incidenceFinset v then a * wt eb.2 else 0

lemma sum_wt_ite (P : Prop) [Decidable P] (a : ℝ) :
    ∑ b : Bool, (if P then a * wt b else 0) = if P then a else 0 := by
  split_ifs
  · simp [wt]; ring
  · simp

/-- The nomination distribution at a vertex. -/
def nomDist (a : ℝ) (ha : 0 ≤ a) (hdeg : ∀ v, (Y.degree v : ℝ) * a ≤ 1) (v : V) :
    FinDist (Option (Sym2 V × Bool)) where
  support := univ
  prob := nomProb Y a v
  prob_nonneg ω := by
    cases ω with
    | none => simp only [nomProb, Option.elim]; linarith [hdeg v]
    | some eb =>
      simp only [nomProb, Option.elim]
      split_ifs
      · unfold wt; split_ifs <;> positivity
      · exact le_rfl
  sum_prob := by
    rw [Fintype.sum_option]
    simp only [nomProb, Option.elim]
    rw [Fintype.sum_prod_type]
    simp only [sum_wt_ite]
    rw [sum_ite_mem, univ_inter, sum_const, SimpleGraph.card_incidenceFinset_eq_degree,
      nsmul_eq_mul]
    ring

/-- The vertex event for edge `e` at `v` (for a mark predicate `s`): if `v ∈ e`, then `v`
nominates `e`, and the distinguished endpoint `e.out.1` attaches a bit satisfying `s`. -/
def Ev (s : Bool → Prop) (v : V) (e : Sym2 V) (ω : Option (Sym2 V × Bool)) : Prop :=
  v ∈ e → ∃ b, ω = some (e, b) ∧ (v = e.out.1 → s b)

/-- The edges all of whose vertex events hold. -/
def selSet (s : Bool → Prop) (ν : V → Option (Sym2 V × Bool)) : Finset (Sym2 V) :=
  @Finset.filter _ (fun e => ∀ v, Ev s v e (ν v)) (Classical.decPred _) Y.edgeFinset

omit [DecidableEq V] in
lemma mem_selSet (s : Bool → Prop) (ν : V → Option (Sym2 V × Bool)) (e : Sym2 V) :
    e ∈ selSet Y s ν ↔ e ∈ Y.edgeFinset ∧ ∀ v, Ev s v e (ν v) := by
  simp only [selSet, Finset.mem_filter]

/-- The retained matching and its marked part. -/
def nomPair (ν : V → Option (Sym2 V × Bool)) : Finset (Sym2 V) × Finset (Sym2 V) :=
  (selSet Y (fun _ => True) ν, selSet Y (fun b => b = true) ν)

omit [Fintype V] [DecidableEq V] in
lemma Ev_triv (s : Bool → Prop) (v : V) (e : Sym2 V) (ω : Option (Sym2 V × Bool))
    (h : ¬v ∈ e) : Ev s v e ω := fun h' => absurd h' h

omit [Fintype V] [DecidableEq V] in
lemma Ev_disj (s : Bool → Prop) (v : V) (e f : Sym2 V) (hef : e ≠ f) (he : v ∈ e) (hf : v ∈ f)
    (ω : Option (Sym2 V × Bool)) (h1 : Ev s v e ω) : ¬Ev s v f ω := by
  intro h2
  obtain ⟨b, hb, _⟩ := h1 he
  obtain ⟨b', hb', _⟩ := h2 hf
  rw [hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  exact hef hb'.1

lemma sdiff_selSet (ν : V → Option (Sym2 V × Bool)) :
    selSet Y (fun _ => True) ν \ selSet Y (fun b => b = true) ν =
      selSet Y (fun b => b = false) ν := by
  ext e
  rw [mem_sdiff, mem_selSet, mem_selSet, mem_selSet]
  constructor
  · rintro ⟨⟨he, hR⟩, hZ⟩
    refine ⟨he, fun v hv => ?_⟩
    obtain ⟨b, hb, -⟩ := hR v hv
    refine ⟨b, hb, fun hvo => ?_⟩
    cases b
    · rfl
    · exfalso
      refine hZ ⟨he, fun v' hv' => ?_⟩
      obtain ⟨b', hb', -⟩ := hR v' hv'
      refine ⟨b', hb', fun hv'o => ?_⟩
      have : ν v' = ν v := by rw [hv'o, hvo]
      rw [hb', hb] at this
      simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact this.2
  · rintro ⟨he, hU⟩
    refine ⟨⟨he, fun v hv => ?_⟩, fun ⟨_, hZ⟩ => ?_⟩
    · obtain ⟨b, hb, -⟩ := hU v hv
      exact ⟨b, hb, fun _ => trivial⟩
    · obtain ⟨b, hb, hb1⟩ := hU e.out.1 (Sym2.out_fst_mem e)
      obtain ⟨b', hb', hb2⟩ := hZ e.out.1 (Sym2.out_fst_mem e)
      rw [hb] at hb'
      simp only [Option.some.injEq, Prod.mk.injEq] at hb'
      have h1 := hb1 rfl
      have h2 := hb2 rfl
      rw [hb'.2] at h1
      rw [h1] at h2
      exact Bool.false_ne_true h2

/-- The mark weight of a mark predicate. -/
def Wsum (s : Bool → Prop) : ℝ := ind (s true) * wt true + ind (s false) * wt false

variable (a : ℝ) (ha : 0 ≤ a) (hdeg : ∀ v, (Y.degree v : ℝ) * a ≤ 1)

lemma P_Ev (s : Bool → Prop) (v : V) (e : Sym2 V) (he : e ∈ Y.edgeFinset) (hv : v ∈ e) :
    (nomDist Y a ha hdeg v).P (Ev s v e) = a * (if v = e.out.1 then Wsum s else 1) := by
  classical
  have hinc : e ∈ Y.incidenceFinset v := by
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.1 he, hv⟩
  rw [P_eq_expect]
  unfold FinDist.expect nomDist
  simp only
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hnone : ¬Ev s v e none := by
    intro h; obtain ⟨b, hb, -⟩ := h hv; cases hb
  rw [ind_of_not hnone, mul_zero, zero_add]
  have hsome : ∀ (e' : Sym2 V) (b : Bool), Ev s v e (some (e', b)) ↔
      e' = e ∧ (v = e.out.1 → s b) := by
    intro e' b
    constructor
    · intro h
      obtain ⟨b', hb', hs⟩ := h hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      exact ⟨rfl, hs⟩
    · rintro ⟨rfl, hs⟩ _
      exact ⟨b, rfl, hs⟩
  have hT : ∀ b, (e = e ∧ (v = e.out.1 → s b)) ↔ (v = e.out.1 → s b) :=
    fun b => ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  rw [sum_eq_single e]
  · simp only [nomProb, Option.elim, hinc, ↓reduceIte, Fintype.sum_bool]
    rw [ind_congr ((hsome e true).trans (hT true)), ind_congr ((hsome e false).trans (hT false))]
    unfold Wsum
    by_cases ho : v = e.out.1
    · rw [ite_eq_left ho, ind_congr ⟨fun h => h ho, fun h _ => h⟩,
        ind_congr ⟨fun h => h ho, fun h _ => h⟩]
      ring
    · rw [ite_eq_right ho, ind_of (fun h => absurd h ho), ind_of (fun h => absurd h ho), wt_true,
        wt_false]
      ring
  · intro e' _ he'
    refine sum_eq_zero fun b _ => ?_
    rw [ind_congr (hsome e' b), ind_of_not (fun h => he' h.1), mul_zero]
  · intro h; exact absurd (mem_univ e) h

lemma prod_P_Ev (s : Bool → Prop) (e : Sym2 V) (he : e ∈ Y.edgeFinset) :
    ∏ v, (nomDist Y a ha hdeg v).P (Ev s v e) = a ^ 2 * Wsum s := by
  have hexy : e = s(e.out.1, e.out.2) := (Quot.out_eq e).symm
  have hxy : e.out.1 ≠ e.out.2 := by
    intro h
    have := SimpleGraph.not_isDiag_of_mem_edgeSet Y (SimpleGraph.mem_edgeFinset.1 he)
    rw [hexy, Sym2.mk_isDiag_iff] at this
    exact this h
  rw [Fintype.prod_eq_mul e.out.1 e.out.2 hxy]
  · rw [P_Ev Y a ha hdeg s _ e he (Sym2.out_fst_mem e),
      P_Ev Y a ha hdeg s _ e he (Sym2.out_snd_mem e), ite_eq_left rfl,
      ite_eq_right (Ne.symm hxy)]
    ring
  · rintro v ⟨hvx, hvy⟩
    refine P_true _ _ fun ω => Ev_triv s v e ω ?_
    rw [hexy, Sym2.mem_iff]
    tauto

omit [DecidableEq V] in
lemma ind_mem_selSet (s : Bool → Prop) (ν : V → Option (Sym2 V × Bool)) (e : Sym2 V)
    (he : e ∈ Y.edgeFinset) : ind (e ∈ selSet Y s ν) = ∏ v, ind (Ev s v e (ν v)) := by
  rw [prod_ind]
  exact ind_congr ((mem_selSet Y s ν e).trans (by simp [he]))

omit [DecidableEq V] in
lemma sum_selSet (s : Bool → Prop) (ν : V → Option (Sym2 V × Bool)) (c : Sym2 V → ℝ) :
    ∑ e ∈ selSet Y s ν, c e = ∑ e ∈ Y.edgeFinset, c e * ∏ v, ind (Ev s v e (ν v)) := by
  rw [selSet, sum_filter]
  refine sum_congr rfl fun e he => ?_
  rw [prod_ind]
  split_ifs with h
  · rw [ind_of (fun v _ => h v), mul_one]
  · rw [ind_of_not (fun h' => h fun v => h' v (mem_univ v)), mul_zero]

lemma P_selSet (s : Bool → Prop) (e : Sym2 V) (he : e ∈ Y.edgeFinset) :
    (FinDist.pi (nomDist Y a ha hdeg)).P (fun ν => e ∈ selSet Y s ν) = a ^ 2 * Wsum s := by
  rw [P_eq_expect]
  rw [expect_congr _ (fun ν _ => ind_mem_selSet Y s ν e he),
    pi_expect_prod (g := fun v ω => ind (Ev s v e ω))]
  simp_rw [← P_eq_expect]
  exact prod_P_Ev Y a ha hdeg s e he

lemma sel_tails (s : Bool → Prop)
    (sel : Finset (Sym2 V) × Finset (Sym2 V) → Finset (Sym2 V))
    (hS : ∀ ν, sel (nomPair Y ν) = selSet Y s ν) (c : Sym2 V → ℝ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    let μ := fdMap (nomPair Y) (FinDist.pi (nomDist Y a ha hdeg))
    (μ.P (fun RZ => μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e) + t ≤ ∑ e ∈ sel RZ, c e) ≤
        Real.exp (-(t ^ 2) / (4 * (μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e) + t / 3)))) ∧
      (μ.P (fun RZ => ∑ e ∈ sel RZ, c e ≤ μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e) - t) ≤
        Real.exp (-(t ^ 2) / (4 * μ.expect (fun RZ' => ∑ e ∈ sel RZ', c e)))) := by
  intro μ
  refine tails_of_mgf μ (fun RZ => ∑ e ∈ sel RZ, c e) _
    (expect_nonneg _ fun RZ _ => sum_nonneg fun e _ => (hc e).1) ?_ t ht
  intro θ
  simp only [μ, expect_fdMap, hS]
  exact mgf_bound _ Y.edgeFinset (Ev s) (fun v e => v ∈ e)
    (fun v e ω h => Ev_triv s v e ω h)
    (fun v e _ f _ hef he hf ω h1 => Ev_disj s v e f hef he hf ω h1) c hc
    (fun ν => ∑ e ∈ selSet Y s ν, c e) (fun ν => sum_selSet Y s ν c) θ

end Model

end MutualNom


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
  have ha : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have ha2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hdeg : ∀ v, (Y.degree v : ℝ) * Real.sqrt p ≤ 1 := by
    intro v
    have h1 : (Y.degree v : ℝ) ≤ k := by exact_mod_cast hk v
    have h0 : (0 : ℝ) ≤ Y.degree v := Nat.cast_nonneg _
    have h2 : ((Y.degree v : ℝ) * Real.sqrt p) ^ 2 ≤ 1 := by
      rw [mul_pow, ha2]
      have : (Y.degree v : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by gcongr
      nlinarith
    have h3 : 0 ≤ (Y.degree v : ℝ) * Real.sqrt p := mul_nonneg h0 ha
    nlinarith
  refine ⟨MutualNom.fdMap (MutualNom.nomPair Y)
    (FinDist.pi (MutualNom.nomDist Y (Real.sqrt p) ha hdeg)), ?_, ?_, ?_⟩
  · intro RZ hRZ
    simp only [MutualNom.fdMap, mem_image] at hRZ
    obtain ⟨ν, -, rfl⟩ := hRZ
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      simp only [MutualNom.nomPair, MutualNom.mem_selSet] at he ⊢
      exact ⟨he.1, fun v hv => (he.2 v hv).elim fun b hb => ⟨b, hb.1, fun _ => trivial⟩⟩
    · intro e he
      exact ((MutualNom.mem_selSet Y _ ν e).1 he).1
    · intro e he f hf hef v hve hvf
      exact MutualNom.Ev_disj _ v e f hef hve hvf (ν v)
        (((MutualNom.mem_selSet Y _ ν e).1 he).2 v) (((MutualNom.mem_selSet Y _ ν f).1 hf).2 v)
  · intro e he
    constructor
    · rw [MutualNom.P_fdMap]
      simp only [MutualNom.nomPair]
      rw [MutualNom.P_selSet Y _ ha hdeg _ e he, ha2]
      simp [MutualNom.Wsum, MutualNom.wt, MutualNom.ind]
      norm_num
    · rw [MutualNom.P_fdMap]
      simp only [MutualNom.nomPair]
      rw [MutualNom.P_selSet Y _ ha hdeg _ e he, ha2]
      simp [MutualNom.Wsum, MutualNom.wt, MutualNom.ind]
      ring
  · intro c hc t ht sel hsel
    rcases hsel with rfl | rfl | rfl
    · exact MutualNom.sel_tails Y _ ha hdeg (fun _ => True) Prod.fst (fun ν => rfl) c hc t ht
    · exact MutualNom.sel_tails Y _ ha hdeg (fun b => b = true) Prod.snd (fun ν => rfl) c hc t ht
    · exact MutualNom.sel_tails Y _ ha hdeg (fun b => b = false) _
        (fun ν => MutualNom.sdiff_selSet Y ν) c hc t ht

end Lovasz
