/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 4.3: bounded-support concentration

DAG node `L4.3` of `docs/BLUEPRINT.md` (trace-exponential supermartingale).

For a fixed symmetric `H` and `|θ| b ≤ 1/16` the potential
`Ψ(y) = tr exp(H + θ ∑ y_j A_j + 8θ² ∑ y_j (1 - y_j) A_j²)` is concave on every allowed line,
hence a supermartingale along the line process; Markov's inequality then gives the tails.

* `TraceConc.trexp`: `tr exp E` as the series `∑ₙ tr(Eⁿ)/n!`.
* `TraceConc.concaveOn_trexp_qpath`: along a quadratic path `Q(s)` of symmetric matrices with
  `Q'' + Q'² ⪯ 0`, `s ↦ tr exp Q(s)` is concave (inequality (4.4), proved by differentiating the
  series termwise and evaluating the second derivative in an eigenbasis of `Q(s)`, where the
  coefficient of `|Q'ᵢⱼ|²` is the logarithmic mean of `e^{qᵢ}, e^{qⱼ}`).
* `TraceConc.line_neg`: `Q'' + Q'² ⪯ 0` on allowed lines.
* `TraceConc.tail_general`: the resulting tail bound for either sign of `θ`.
-/

open Matrix Finset

namespace Lovasz.TraceConc

variable {q : ℕ}

/-! ### An entrywise matrix norm -/

/-- Sum of the absolute values of the entries (a submultiplicative norm). -/
noncomputable def mnorm (A : Matrix (Fin q) (Fin q) ℝ) : ℝ := ∑ i, ∑ j, |A i j|

lemma mnorm_nonneg (A : Matrix (Fin q) (Fin q) ℝ) : 0 ≤ mnorm A := by
  unfold mnorm; positivity

lemma mnorm_mul (A B : Matrix (Fin q) (Fin q) ℝ) : mnorm (A * B) ≤ mnorm A * mnorm B := by
  unfold mnorm
  calc ∑ i, ∑ j, |(A * B) i j| ≤ ∑ i, ∑ j, ∑ k, |A i k| * |B k j| := by
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp [abs_mul]
    _ = ∑ i, ∑ k, |A i k| * ∑ j, |B k j| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |A i k| * ∑ k', ∑ j, |B k' j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun k' => ∑ j, |B k' j|)
          (fun _ _ => by positivity) (Finset.mem_univ k)) (abs_nonneg _)
    _ = (∑ i, ∑ j, |A i j|) * ∑ i, ∑ j, |B i j| := by
        simp [Finset.sum_mul]

lemma mnorm_add (A B : Matrix (Fin q) (Fin q) ℝ) : mnorm (A + B) ≤ mnorm A + mnorm B := by
  unfold mnorm
  rw [← Finset.sum_add_distrib]
  gcongr with i _
  rw [← Finset.sum_add_distrib]
  gcongr with j _
  exact abs_add_le _ _

lemma mnorm_smul (c : ℝ) (A : Matrix (Fin q) (Fin q) ℝ) : mnorm (c • A) = |c| * mnorm A := by
  unfold mnorm; simp [abs_mul, Finset.mul_sum]

lemma mnorm_one : mnorm (1 : Matrix (Fin q) (Fin q) ℝ) = q := by
  unfold mnorm
  simp [Matrix.one_apply, apply_ite]

lemma mnorm_zero : mnorm (0 : Matrix (Fin q) (Fin q) ℝ) = 0 := by
  unfold mnorm; simp

lemma mnorm_pow (A : Matrix (Fin q) (Fin q) ℝ) (n : ℕ) : mnorm (A ^ n) ≤ q * mnorm A ^ n := by
  induction n with
  | zero => simp [mnorm_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    calc mnorm (A ^ n * A) ≤ mnorm (A ^ n) * mnorm A := mnorm_mul _ _
      _ ≤ (q * mnorm A ^ n) * mnorm A := by gcongr; exact mnorm_nonneg _
      _ = _ := by ring

lemma abs_trace_le (A : Matrix (Fin q) (Fin q) ℝ) : |A.trace| ≤ mnorm A := by
  unfold Matrix.trace
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold mnorm
  gcongr with i _
  exact Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-! ### Entrywise derivatives of matrix paths -/

/-- Entrywise derivative of a matrix path. -/
def MHasDerivAt (P : ℝ → Matrix (Fin q) (Fin q) ℝ) (P' : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) :
    Prop :=
  ∀ i j, HasDerivAt (fun s => P s i j) (P' i j) t

lemma MHasDerivAt.mul {A B : ℝ → Matrix (Fin q) (Fin q) ℝ} {A' B' : Matrix (Fin q) (Fin q) ℝ}
    {t : ℝ} (hA : MHasDerivAt A A' t) (hB : MHasDerivAt B B' t) :
    MHasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB k j)

lemma MHasDerivAt.trace {P : ℝ → Matrix (Fin q) (Fin q) ℝ} {P' : Matrix (Fin q) (Fin q) ℝ}
    {t : ℝ} (h : MHasDerivAt P P' t) : HasDerivAt (fun s => (P s).trace) P'.trace t := by
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum fun i _ => h i i

lemma MHasDerivAt.const (C : Matrix (Fin q) (Fin q) ℝ) (t : ℝ) :
    MHasDerivAt (fun _ => C) 0 t := fun i j => by
  simpa using hasDerivAt_const t (C i j)

/-- The derivative of `Q ↦ Q ^ n` in the direction `X`. -/
noncomputable def dpow (Q X : Matrix (Fin q) (Fin q) ℝ) : ℕ → Matrix (Fin q) (Fin q) ℝ
  | 0 => 0
  | n + 1 => X * Q ^ n + Q * dpow Q X n

lemma MHasDerivAt.pow {P : ℝ → Matrix (Fin q) (Fin q) ℝ} {P' : Matrix (Fin q) (Fin q) ℝ}
    {t : ℝ} (h : MHasDerivAt P P' t) (n : ℕ) :
    MHasDerivAt (fun s => P s ^ n) (dpow (P t) P' n) t := by
  induction n with
  | zero => simpa [dpow] using MHasDerivAt.const (1 : Matrix (Fin q) (Fin q) ℝ) t
  | succ n ih =>
    have := h.mul ih
    simp only [dpow]
    have e : (fun s => P s ^ (n + 1)) = fun s => P s * P s ^ n := funext fun s => pow_succ' _ _
    rw [e]
    exact this

lemma trace_pow_mul_dpow (Q X : Matrix (Fin q) (Fin q) ℝ) (n : ℕ) :
    ∀ j : ℕ, (Q ^ j * dpow Q X (n + 1)).trace = (n + 1) * (Q ^ (n + j) * X).trace := by
  induction n with
  | zero => intro j; simp [dpow]
  | succ n ih =>
    intro j
    rw [dpow, mul_add, Matrix.trace_add, ← mul_assoc (Q ^ j) Q, ← pow_succ, ih (j + 1),
      Matrix.trace_mul_comm (Q ^ j), mul_assoc, ← pow_add, Matrix.trace_mul_comm X]
    have e : n + (j + 1) = n + 1 + j := by omega
    rw [e]
    push_cast
    ring

lemma trace_dpow (Q X : Matrix (Fin q) (Fin q) ℝ) (n : ℕ) :
    (dpow Q X (n + 1)).trace = (n + 1) * (Q ^ n * X).trace := by
  simpa using trace_pow_mul_dpow Q X n 0

lemma mnorm_dpow (Q X : Matrix (Fin q) (Fin q) ℝ) (n : ℕ) :
    mnorm (dpow Q X n) ≤ q * mnorm X * (2 * (mnorm Q + 1)) ^ n := by
  have ha := mnorm_nonneg Q
  have hx := mnorm_nonneg X
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  induction n with
  | zero => simp [dpow, mnorm_zero]; positivity
  | succ n ih =>
    simp only [dpow]
    have h1 : mnorm Q ^ n ≤ (2 * (mnorm Q + 1)) ^ n := pow_le_pow_left₀ ha (by linarith) n
    have h2 : 0 ≤ (2 * (mnorm Q + 1)) ^ n := by positivity
    calc mnorm (X * Q ^ n + Q * dpow Q X n)
        ≤ mnorm (X * Q ^ n) + mnorm (Q * dpow Q X n) := mnorm_add _ _
      _ ≤ mnorm X * (q * mnorm Q ^ n) + mnorm Q * (q * mnorm X * (2 * (mnorm Q + 1)) ^ n) := by
          gcongr
          · exact (mnorm_mul _ _).trans (by gcongr; exact mnorm_pow _ _)
          · exact (mnorm_mul _ _).trans (by gcongr)
      _ ≤ mnorm X * (q * (2 * (mnorm Q + 1)) ^ n)
            + mnorm Q * (q * mnorm X * (2 * (mnorm Q + 1)) ^ n) := by gcongr
      _ ≤ q * mnorm X * (2 * (mnorm Q + 1)) ^ (n + 1) := by
          rw [pow_succ]
          have h3 : 0 ≤ q * mnorm X * (2 * (mnorm Q + 1)) ^ n := by positivity
          nlinarith [mul_nonneg h3 ha]

/-! ### The trace exponential -/

/-- `tr exp E = ∑ₙ tr(Eⁿ)/n!`. -/
noncomputable def trexp (E : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  ∑' n, ((n.factorial : ℝ))⁻¹ * (E ^ n).trace

lemma summable_of_le_geom {f : ℕ → ℝ} (C c : ℝ) (h : ∀ n, |f n| ≤ C * c ^ n) :
    Summable fun n => ((n.factorial : ℝ))⁻¹ * f n := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial c).mul_left C) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
  calc ((n.factorial : ℝ))⁻¹ * |f n| ≤ ((n.factorial : ℝ))⁻¹ * (C * c ^ n) := by
        gcongr; exact h n
    _ = C * (c ^ n / n.factorial) := by ring

/-! ### Quadratic matrix paths -/

section Path

variable (Q0 Q1 Q2 : Matrix (Fin q) (Fin q) ℝ)

/-- The path `Q(s) = Q₀ + s Q₁ + s² Q₂`. -/
noncomputable def qpath (s : ℝ) : Matrix (Fin q) (Fin q) ℝ := Q0 + s • Q1 + s ^ 2 • Q2

/-- Its derivative `Q'(s) = Q₁ + 2 s Q₂`. -/
noncomputable def rpath (s : ℝ) : Matrix (Fin q) (Fin q) ℝ := Q1 + (2 * s) • Q2

lemma hasDerivAt_qpath (t : ℝ) : MHasDerivAt (qpath Q0 Q1 Q2) (rpath Q1 Q2 t) t := by
  intro i j
  simp only [qpath, rpath, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := (hasDerivAt_id t).mul_const (Q1 i j)
  have h2 := (hasDerivAt_pow 2 t).mul_const (Q2 i j)
  exact (((hasDerivAt_const t (Q0 i j)).add h1).add h2).congr_deriv (by simp)

lemma hasDerivAt_rpath (t : ℝ) : MHasDerivAt (rpath Q1 Q2) ((2 : ℝ) • Q2) t := by
  intro i j
  simp only [rpath, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := ((hasDerivAt_id t).const_mul 2).mul_const (Q2 i j)
  exact ((hasDerivAt_const t (Q1 i j)).add h1).congr_deriv (by simp)

lemma mnorm_qpath_le {T s : ℝ} (hs : |s| < T) :
    mnorm (qpath Q0 Q1 Q2 s) ≤ mnorm Q0 + T * mnorm Q1 + T ^ 2 * mnorm Q2 := by
  have h0 : 0 ≤ |s| := abs_nonneg s
  have hT : |s| ≤ T := hs.le
  have e1 := mnorm_add (Q0 + s • Q1) (s ^ 2 • Q2)
  have e2 := mnorm_add Q0 (s • Q1)
  have e3 := mnorm_smul s Q1
  have e4 := mnorm_smul (s ^ 2) Q2
  have n1 := mnorm_nonneg Q1
  have n2 := mnorm_nonneg Q2
  have f1 : |s| * mnorm Q1 ≤ T * mnorm Q1 := mul_le_mul_of_nonneg_right hT n1
  have f2 : |s ^ 2| * mnorm Q2 ≤ T ^ 2 * mnorm Q2 := by
    rw [abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hT 2) n2
  unfold qpath
  linarith

lemma mnorm_rpath_le {T s : ℝ} (hs : |s| < T) :
    mnorm (rpath Q1 Q2 s) ≤ mnorm Q1 + 2 * T * mnorm Q2 := by
  have hT : |s| ≤ T := hs.le
  have e1 := mnorm_add Q1 ((2 * s) • Q2)
  have e2 := mnorm_smul (2 * s) Q2
  have n2 := mnorm_nonneg Q2
  have f : |2 * s| * mnorm Q2 ≤ 2 * T * mnorm Q2 := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_right (by linarith) n2
  unfold rpath
  linarith

/-- First derivative of `s ↦ tr exp Q(s)`. -/
theorem hasDerivAt_trexp_qpath (s : ℝ) :
    HasDerivAt (fun s => trexp (qpath Q0 Q1 Q2 s))
      (∑' m, ((m.factorial : ℝ))⁻¹ * (qpath Q0 Q1 Q2 s ^ m * rpath Q1 Q2 s).trace) s := by
  set T := |s| + 1
  set a := mnorm Q0 + T * mnorm Q1 + T ^ 2 * mnorm Q2 with ha_def
  set r := mnorm Q1 + 2 * T * mnorm Q2 with hr_def
  set c := 2 * (a + 1) with hc_def
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hT : 0 ≤ T := by positivity
  have ha : 0 ≤ a := by
    have := mnorm_nonneg Q0; have := mnorm_nonneg Q1; have := mnorm_nonneg Q2; positivity
  have hr : 0 ≤ r := by have := mnorm_nonneg Q1; have := mnorm_nonneg Q2; positivity
  have hsT : s ∈ Set.Ioo (-T) T := by
    constructor <;> [linarith [neg_abs_le s]; linarith [le_abs_self s]]
  have hmem : ∀ y ∈ Set.Ioo (-T) T, |y| < T := fun y hy => abs_lt.2 hy
  let g : ℕ → ℝ → ℝ := fun n y => ((n.factorial : ℝ))⁻¹ * (qpath Q0 Q1 Q2 y ^ n).trace
  let g' : ℕ → ℝ → ℝ := fun n y =>
    ((n.factorial : ℝ))⁻¹ * (dpow (qpath Q0 Q1 Q2 y) (rpath Q1 Q2 y) n).trace
  have hg : ∀ n y, y ∈ Set.Ioo (-T) T → HasDerivAt (g n) (g' n y) y := fun n y _ =>
    (((hasDerivAt_qpath Q0 Q1 Q2 y).pow n).trace).const_mul _
  have hbound : ∀ n y, |y| < T → |(dpow (qpath Q0 Q1 Q2 y) (rpath Q1 Q2 y) n).trace|
      ≤ q * r * c ^ n := by
    intro n y hy
    refine (abs_trace_le _).trans ((mnorm_dpow _ _ n).trans ?_)
    have h1 := mnorm_qpath_le Q0 Q1 Q2 hy
    have h2 := mnorm_rpath_le Q1 Q2 hy
    have h3 := mnorm_nonneg (qpath Q0 Q1 Q2 y)
    have h5 : 2 * (mnorm (qpath Q0 Q1 Q2 y) + 1) ≤ c := by rw [hc_def, ha_def]; linarith
    gcongr
  have hu : Summable fun n => q * r * (c ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial c).mul_left _
  have hg' : ∀ n y, y ∈ Set.Ioo (-T) T → ‖g' n y‖ ≤ q * r * (c ^ n / n.factorial) := by
    intro n y hy
    simp only [g', Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
    calc ((n.factorial : ℝ))⁻¹ * |(dpow (qpath Q0 Q1 Q2 y) (rpath Q1 Q2 y) n).trace|
        ≤ ((n.factorial : ℝ))⁻¹ * (q * r * c ^ n) := by gcongr; exact hbound n y (hmem y hy)
      _ = _ := by ring
  have hg0 : Summable fun n => g n s := by
    refine summable_of_le_geom q (mnorm (qpath Q0 Q1 Q2 s)) fun n => ?_
    exact (abs_trace_le _).trans (mnorm_pow _ _)
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hsT hg0 hsT
  refine key.congr_deriv ?_
  have hsum : Summable fun n => g' n s := Summable.of_norm_bounded hu fun n => hg' n s hsT
  rw [hsum.tsum_eq_zero_add]
  have h0 : g' 0 s = 0 := by simp [g', dpow]
  rw [h0, zero_add]
  refine tsum_congr fun m => ?_
  simp only [g']
  rw [trace_dpow, Nat.factorial_succ]
  push_cast
  field_simp

/-- Second derivative of `s ↦ tr exp Q(s)`. -/
theorem hasDerivAt_trexp_qpath' (s : ℝ) :
    HasDerivAt (fun s => ∑' m, ((m.factorial : ℝ))⁻¹ *
        (qpath Q0 Q1 Q2 s ^ m * rpath Q1 Q2 s).trace)
      (∑' m, ((m.factorial : ℝ))⁻¹ * (dpow (qpath Q0 Q1 Q2 s) (rpath Q1 Q2 s) m * rpath Q1 Q2 s
        + qpath Q0 Q1 Q2 s ^ m * ((2 : ℝ) • Q2)).trace) s := by
  set T := |s| + 1
  set a := mnorm Q0 + T * mnorm Q1 + T ^ 2 * mnorm Q2 with ha_def
  set r := mnorm Q1 + 2 * T * mnorm Q2 with hr_def
  set c := 2 * (a + 1) with hc_def
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hT : 0 ≤ T := by positivity
  have ha : 0 ≤ a := by
    have := mnorm_nonneg Q0; have := mnorm_nonneg Q1; have := mnorm_nonneg Q2; positivity
  have hr : 0 ≤ r := by have := mnorm_nonneg Q1; have := mnorm_nonneg Q2; positivity
  have hw : 0 ≤ mnorm ((2 : ℝ) • Q2) := mnorm_nonneg _
  have hsT : s ∈ Set.Ioo (-T) T := by
    constructor <;> [linarith [neg_abs_le s]; linarith [le_abs_self s]]
  have hmem : ∀ y ∈ Set.Ioo (-T) T, |y| < T := fun y hy => abs_lt.2 hy
  let g : ℕ → ℝ → ℝ := fun n y =>
    ((n.factorial : ℝ))⁻¹ * (qpath Q0 Q1 Q2 y ^ n * rpath Q1 Q2 y).trace
  let g' : ℕ → ℝ → ℝ := fun n y => ((n.factorial : ℝ))⁻¹ *
    (dpow (qpath Q0 Q1 Q2 y) (rpath Q1 Q2 y) n * rpath Q1 Q2 y
      + qpath Q0 Q1 Q2 y ^ n * ((2 : ℝ) • Q2)).trace
  have hg : ∀ n y, y ∈ Set.Ioo (-T) T → HasDerivAt (g n) (g' n y) y := fun n y _ =>
    ((((hasDerivAt_qpath Q0 Q1 Q2 y).pow n).mul (hasDerivAt_rpath Q1 Q2 y)).trace).const_mul _
  have hbound : ∀ n y, |y| < T → |(dpow (qpath Q0 Q1 Q2 y) (rpath Q1 Q2 y) n * rpath Q1 Q2 y
      + qpath Q0 Q1 Q2 y ^ n * ((2 : ℝ) • Q2)).trace|
      ≤ (q * r * r + q * mnorm ((2 : ℝ) • Q2)) * c ^ n := by
    intro n y hy
    refine (abs_trace_le _).trans ((mnorm_add _ _).trans ?_)
    have h1 := mnorm_qpath_le Q0 Q1 Q2 hy
    have h2 := mnorm_rpath_le Q1 Q2 hy
    have h3 := mnorm_nonneg (qpath Q0 Q1 Q2 y)
    have h4 := mnorm_nonneg (rpath Q1 Q2 y)
    have h5 : 2 * (mnorm (qpath Q0 Q1 Q2 y) + 1) ≤ c := by rw [hc_def, ha_def]; linarith
    have e1 : mnorm (dpow (qpath Q0 Q1 Q2 y) (rpath Q1 Q2 y) n * rpath Q1 Q2 y) ≤
        q * r * c ^ n * r :=
      (mnorm_mul _ _).trans (by
        gcongr
        exact (mnorm_dpow _ _ n).trans (by gcongr))
    have e2 : mnorm (qpath Q0 Q1 Q2 y ^ n * ((2 : ℝ) • Q2)) ≤ q * c ^ n * mnorm ((2 : ℝ) • Q2) :=
      (mnorm_mul _ _).trans (by
        gcongr
        refine (mnorm_pow _ _).trans ?_
        gcongr
        linarith)
    nlinarith [e1, e2]
  have hu : Summable fun n => (q * r * r + q * mnorm ((2 : ℝ) • Q2)) * (c ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial c).mul_left _
  have hg' : ∀ n y, y ∈ Set.Ioo (-T) T →
      ‖g' n y‖ ≤ (q * r * r + q * mnorm ((2 : ℝ) • Q2)) * (c ^ n / n.factorial) := by
    intro n y hy
    simp only [g', Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
    calc _ ≤ ((n.factorial : ℝ))⁻¹ * ((q * r * r + q * mnorm ((2 : ℝ) • Q2)) * c ^ n) := by
          gcongr; exact hbound n y (hmem y hy)
      _ = _ := by ring
  have hg0 : Summable fun n => g n s := by
    refine summable_of_le_geom (q * mnorm (rpath Q1 Q2 s)) (mnorm (qpath Q0 Q1 Q2 s))
      fun n => ?_
    refine (abs_trace_le _).trans ((mnorm_mul _ _).trans ?_)
    have := mnorm_pow (qpath Q0 Q1 Q2 s) n
    have := mnorm_nonneg (rpath Q1 Q2 s)
    nlinarith
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg' hsT hg0 hsT

end Path

/-! ### Scalar facts: the logarithmic mean -/

/-- `hh n a b = ∑_{k<n} a^k b^{n-1-k}`. -/
def hh : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, a, b => b ^ n + a * hh n a b

lemma hh_mul_sub (n : ℕ) (a b : ℝ) : hh n a b * (a - b) = a ^ n - b ^ n := by
  induction n with
  | zero => simp [hh]
  | succ n ih => simp only [hh]; rw [add_mul, mul_assoc, ih]; ring

lemma hh_self (n : ℕ) (a : ℝ) : hh (n + 1) a a = (n + 1) * a ^ n := by
  induction n with
  | zero => simp [hh]
  | succ n ih => rw [hh, ih]; push_cast; ring

lemma hasSum_exp (x : ℝ) : HasSum (fun n => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

/-- The logarithmic mean of `eᵃ` and `eᵇ`. -/
noncomputable def lmean (a b : ℝ) : ℝ :=
  if a = b then Real.exp a else (Real.exp a - Real.exp b) / (a - b)

lemma hasSum_hh (a b : ℝ) :
    HasSum (fun m => ((m.factorial : ℝ))⁻¹ * hh m a b) (lmean a b) := by
  unfold lmean
  split_ifs with h
  · subst h
    rw [← hasSum_nat_add_iff' 1]
    convert hasSum_exp a using 1
    · funext n
      rw [hh_self, Nat.factorial_succ]
      push_cast
      field_simp
    · simp [hh]
  · have hab : a - b ≠ 0 := sub_ne_zero.2 h
    convert ((hasSum_exp a).sub (hasSum_exp b)).div_const (a - b) using 1
    funext m
    rw [eq_div_iff hab, mul_assoc, hh_mul_sub]
    ring

lemma two_mul_exp_sub_one_le (u : ℝ) (hu : 0 ≤ u) :
    2 * (Real.exp u - 1) ≤ u * (Real.exp u + 1) := by
  let f : ℝ → ℝ := fun x => x * (Real.exp x + 1) - 2 * (Real.exp x - 1)
  have hf : ∀ x, HasDerivAt f (1 + (x - 1) * Real.exp x) x := by
    intro x
    have := ((hasDerivAt_id' x).mul ((Real.hasDerivAt_exp x).add_const 1)).sub
      (((Real.hasDerivAt_exp x).sub_const 1).const_mul 2)
    convert this using 1
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hf x).continuousAt.continuousWithinAt) (fun x _ => (hf x).hasDerivWithinAt) ?_
    intro x _
    have h1 := Real.add_one_le_exp (-x)
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos x).le
    nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) hu hu
  simp only [f] at this
  simp at this
  linarith

lemma lmean_le_of_lt {a b : ℝ} (h : b < a) :
    (Real.exp a - Real.exp b) / (a - b) ≤ (Real.exp a + Real.exp b) / 2 := by
  have hu := two_mul_exp_sub_one_le (a - b) (sub_nonneg.2 h.le)
  have e : Real.exp a = Real.exp b * Real.exp (a - b) := by rw [← Real.exp_add]; ring_nf
  rw [div_le_iff₀ (sub_pos.2 h), e]
  have hb := Real.exp_pos b
  nlinarith [mul_le_mul_of_nonneg_left hu hb.le]

lemma lmean_le (a b : ℝ) : lmean a b ≤ (Real.exp a + Real.exp b) / 2 := by
  unfold lmean
  split_ifs with h
  · subst h; linarith
  · rcases lt_or_gt_of_ne h with h' | h'
    · have := lmean_le_of_lt h'
      have e : (Real.exp a - Real.exp b) / (a - b) = (Real.exp b - Real.exp a) / (b - a) := by
        rw [← neg_sub (Real.exp b), ← neg_sub b, neg_div_neg_eq]
      rw [e]; linarith
    · exact lmean_le_of_lt h'

/-! ### Orthogonal diagonalization -/

lemma exists_diag (E : Matrix (Fin q) (Fin q) ℝ) (hE : Eᵀ = E) :
    ∃ (U : Matrix (Fin q) (Fin q) ℝ) (d : Fin q → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      E = U * diagonal d * Uᵀ := by
  have hH : E.IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_eq_transpose_of_trivial, hE]
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose] using this

lemma conj_pow {U : Matrix (Fin q) (Fin q) ℝ} (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (D : Matrix (Fin q) (Fin q) ℝ) (m : ℕ) : (U * D * Uᵀ) ^ m = U * D ^ m * Uᵀ := by
  induction m with
  | zero => simp [hU']
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (U * D ^ m) Uᵀ U, hU, Matrix.mul_one]

lemma conj_dpow {U : Matrix (Fin q) (Fin q) ℝ} (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (D Y : Matrix (Fin q) (Fin q) ℝ) (m : ℕ) :
    dpow (U * D * Uᵀ) (U * Y * Uᵀ) m = U * dpow D Y m * Uᵀ := by
  induction m with
  | zero => simp [dpow]
  | succ m ih =>
    rw [dpow, dpow, ih, conj_pow hU hU' D m]
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (U * Y) Uᵀ U, hU, Matrix.mul_one, Matrix.mul_assoc (U * D) Uᵀ U, hU,
      Matrix.mul_one]

lemma dpow_diag_apply (d : Fin q → ℝ) (Y : Matrix (Fin q) (Fin q) ℝ) (m : ℕ) (i j : Fin q) :
    dpow (diagonal d) Y m i j = Y i j * hh m (d i) (d j) := by
  induction m with
  | zero => simp [dpow, hh]
  | succ m ih =>
    simp only [dpow, Matrix.add_apply, Matrix.diagonal_pow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, ih, hh, Pi.pow_apply]
    ring

lemma conj_diag_apply (U M : Matrix (Fin q) (Fin q) ℝ) (i : Fin q) :
    (Uᵀ * M * U) i i = (fun k => U k i) ⬝ᵥ (M *ᵥ fun k => U k i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma trace_eval {U : Matrix (Fin q) (Fin q) ℝ} (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (d : Fin q → ℝ) (X W : Matrix (Fin q) (Fin q) ℝ) (hX : Xᵀ = X) (m : ℕ) :
    (dpow (U * diagonal d * Uᵀ) X m * X + (U * diagonal d * Uᵀ) ^ m * W).trace =
      ∑ i, ∑ j, (Uᵀ * X * U) i j ^ 2 * hh m (d i) (d j) + ∑ i, d i ^ m * (Uᵀ * W * U) i i := by
  set Y := Uᵀ * X * U with hY
  have hXY : X = U * Y * Uᵀ := by
    rw [hY]; simp only [← Matrix.mul_assoc]; rw [hU', Matrix.one_mul, Matrix.mul_assoc, hU',
      Matrix.mul_one]
  have hYs : ∀ i j, Y j i = Y i j := by
    intro i j
    have : Yᵀ = Y := by rw [hY, Matrix.transpose_mul, Matrix.transpose_mul, hX,
      Matrix.transpose_transpose, Matrix.mul_assoc]
    have := congrFun (congrFun this i) j
    simpa using this
  have e1 : (dpow (U * diagonal d * Uᵀ) X m * X).trace = (dpow (diagonal d) Y m * Y).trace := by
    conv_lhs => rw [hXY]
    rw [conj_dpow hU hU']
    rw [show U * dpow (diagonal d) Y m * Uᵀ * (U * Y * Uᵀ) = U * (dpow (diagonal d) Y m * Y) * Uᵀ by
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (U * dpow (diagonal d) Y m) Uᵀ U, hU, Matrix.mul_one]]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have e2 : ((U * diagonal d * Uᵀ) ^ m * W).trace = (diagonal d ^ m * (Uᵀ * W * U)).trace := by
    rw [conj_pow hU hU', Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm U]
    simp only [Matrix.mul_assoc]
  rw [Matrix.trace_add, e1, e2]
  congr 1
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dpow_diag_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hYs]; ring
  · simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_pow, Matrix.diagonal_mul, Pi.pow_apply]

/-- The second derivative is nonpositive when `W + X² ⪯ 0` (inequality (4.4)). -/
theorem tsum_second_nonpos (Q X W : Matrix (Fin q) (Fin q) ℝ) (hQ : Qᵀ = Q) (hX : Xᵀ = X)
    (h : ∀ v, v ⬝ᵥ ((W + X * X) *ᵥ v) ≤ 0) :
    ∑' m, ((m.factorial : ℝ))⁻¹ * (dpow Q X m * X + Q ^ m * W).trace ≤ 0 := by
  obtain ⟨U, d, hU, hU', rfl⟩ := exists_diag Q hQ
  set Y := Uᵀ * X * U with hY
  set V := Uᵀ * W * U with hV
  have hYs : ∀ i j, Y j i = Y i j := by
    intro i j
    have : Yᵀ = Y := by rw [hY, Matrix.transpose_mul, Matrix.transpose_mul, hX,
      Matrix.transpose_transpose, Matrix.mul_assoc]
    have := congrFun (congrFun this i) j
    simpa using this
  have hs : HasSum (fun m => ((m.factorial : ℝ))⁻¹ *
      (dpow (U * diagonal d * Uᵀ) X m * X + (U * diagonal d * Uᵀ) ^ m * W).trace)
      (∑ i, ∑ j, Y i j ^ 2 * lmean (d i) (d j) + ∑ i, V i i * Real.exp (d i)) := by
    have := (hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_sum fun j (_ : j ∈ Finset.univ) =>
      (hasSum_hh (d i) (d j)).mul_left (Y i j ^ 2)).add
      (hasSum_sum fun i (_ : i ∈ Finset.univ) => (hasSum_exp (d i)).mul_left (V i i))
    convert this using 1
    funext m
    rw [trace_eval hU hU' d X W hX m, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs.tsum_eq]
  have hdiag : ∀ i, ∑ j, Y i j ^ 2 + V i i ≤ 0 := by
    intro i
    have e : ∑ j, Y i j ^ 2 + V i i = (Uᵀ * (W + X * X) * U) i i := by
      have hYY : Y * Y = Uᵀ * (X * X) * U := by
        rw [hY]
        calc Uᵀ * X * U * (Uᵀ * X * U) = Uᵀ * X * (U * Uᵀ) * X * U := by
              simp only [Matrix.mul_assoc]
          _ = Uᵀ * (X * X) * U := by rw [hU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      have : Uᵀ * (W + X * X) * U = V + Y * Y := by
        rw [hV, hYY, Matrix.mul_add, Matrix.add_mul]
      rw [this, Matrix.add_apply, Matrix.mul_apply, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hYs, sq]
    rw [e, conj_diag_apply]
    exact h _
  have hswap : ∑ i, ∑ j, Y i j ^ 2 * Real.exp (d j) = ∑ i, ∑ j, Y i j ^ 2 * Real.exp (d i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hYs]
  calc ∑ i, ∑ j, Y i j ^ 2 * lmean (d i) (d j) + ∑ i, V i i * Real.exp (d i)
      ≤ ∑ i, ∑ j, Y i j ^ 2 * ((Real.exp (d i) + Real.exp (d j)) / 2)
          + ∑ i, V i i * Real.exp (d i) := by
        gcongr with i _ j _
        exact lmean_le _ _
    _ = ∑ i, Real.exp (d i) * (∑ j, Y i j ^ 2 + V i i) := by
        have h1 : ∑ i, ∑ j, Y i j ^ 2 * ((Real.exp (d i) + Real.exp (d j)) / 2) =
            (∑ i, ∑ j, Y i j ^ 2 * Real.exp (d i) + ∑ i, ∑ j, Y i j ^ 2 * Real.exp (d j)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by ring
        have h2 : ∑ i, ∑ j, Y i j ^ 2 * ((Real.exp (d i) + Real.exp (d j)) / 2) =
            ∑ i, ∑ j, Y i j ^ 2 * Real.exp (d i) := by
          rw [h1, hswap]; ring
        rw [h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by ring
        · ring
    _ ≤ 0 := Finset.sum_nonpos fun i _ =>
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hdiag i)

/-! ### `tr exp` via eigenvalues -/

lemma trexp_conj {U : Matrix (Fin q) (Fin q) ℝ} (hU : Uᵀ * U = 1) (hU' : U * Uᵀ = 1)
    (d : Fin q → ℝ) : trexp (U * diagonal d * Uᵀ) = ∑ i, Real.exp (d i) := by
  unfold trexp
  refine HasSum.tsum_eq ?_
  have := hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_exp (d i)
  convert this using 1
  funext n
  rw [conj_pow hU hU' _ n, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.pow_apply]
  ring

lemma trexp_nonneg (E : Matrix (Fin q) (Fin q) ℝ) (hE : Eᵀ = E) : 0 ≤ trexp E := by
  obtain ⟨U, d, hU, hU', rfl⟩ := exists_diag E hE
  rw [trexp_conj hU hU']
  positivity

lemma trexp_le (E : Matrix (Fin q) (Fin q) ℝ) (hE : Eᵀ = E) (c : ℝ)
    (h : ∀ v, v ⬝ᵥ (E *ᵥ v) ≤ c * (v ⬝ᵥ v)) : trexp E ≤ q * Real.exp c := by
  obtain ⟨U, d, hU, hU', rfl⟩ := exists_diag E hE
  rw [trexp_conj hU hU']
  have hd : ∀ i, d i ≤ c := by
    intro i
    have h1 := h (fun k => U k i)
    have e1 : (fun k => U k i) ⬝ᵥ ((U * diagonal d * Uᵀ) *ᵥ fun k => U k i) = d i := by
      rw [← conj_diag_apply]
      rw [show Uᵀ * (U * diagonal d * Uᵀ) * U = diagonal d by
        simp only [← Matrix.mul_assoc]
        rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]]
      simp
    have e2 : (fun k => U k i) ⬝ᵥ (fun k => U k i) = 1 := by
      have := congrFun (congrFun hU i) i
      simpa [Matrix.mul_apply, dotProduct] using this
    rw [e1, e2, mul_one] at h1
    exact h1
  calc ∑ i, Real.exp (d i) ≤ ∑ _i : Fin q, Real.exp c :=
        Finset.sum_le_sum fun i _ => Real.exp_le_exp.2 (hd i)
    _ = q * Real.exp c := by simp

lemma one_le_trexp (E : Matrix (Fin q) (Fin q) ℝ) (hE : Eᵀ = E) (v : Fin q → ℝ)
    (hv : v ⬝ᵥ v = 1) (h : 0 ≤ v ⬝ᵥ (E *ᵥ v)) : 1 ≤ trexp E := by
  obtain ⟨U, d, hU, hU', rfl⟩ := exists_diag E hE
  rw [trexp_conj hU hU']
  set w := Uᵀ *ᵥ v with hw_def
  have hw : w ⬝ᵥ w = 1 := by
    rw [hw_def]
    conv_lhs => arg 1; rw [Matrix.mulVec_transpose]
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec, hv]
  have hq : v ⬝ᵥ ((U * diagonal d * Uᵀ) *ᵥ v) = ∑ i, d i * w i ^ 2 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← hw_def]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := by
    rcases (Finset.univ : Finset (Fin q)).eq_empty_or_nonempty with h0 | h0
    · simp [dotProduct, h0] at hv
    · exact h0
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ d hne
  have hd0 : 0 ≤ d i0 := by
    have h1 : ∑ i, d i * w i ^ 2 ≤ ∑ i, d i0 * w i ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi0 i (Finset.mem_univ i))
        (sq_nonneg _)
    rw [← Finset.mul_sum] at h1
    have hw' : ∑ i, w i ^ 2 = 1 := by simpa [dotProduct, sq] using hw
    rw [hw', mul_one] at h1
    linarith [hq ▸ h]
  calc (1 : ℝ) ≤ Real.exp (d i0) := Real.one_le_exp hd0
    _ ≤ ∑ i, Real.exp (d i) :=
        Finset.single_le_sum (f := fun i => Real.exp (d i)) (fun i _ => (Real.exp_pos _).le)
          (Finset.mem_univ i0)

/-! ### Concavity of `tr exp` along quadratic paths -/

lemma transpose_qpath (Q0 Q1 Q2 : Matrix (Fin q) (Fin q) ℝ) (h0 : Q0ᵀ = Q0) (h1 : Q1ᵀ = Q1)
    (h2 : Q2ᵀ = Q2) (s : ℝ) : (qpath Q0 Q1 Q2 s)ᵀ = qpath Q0 Q1 Q2 s := by
  simp [qpath, Matrix.transpose_add, Matrix.transpose_smul, h0, h1, h2]

lemma transpose_rpath (Q1 Q2 : Matrix (Fin q) (Fin q) ℝ) (h1 : Q1ᵀ = Q1)
    (h2 : Q2ᵀ = Q2) (s : ℝ) : (rpath Q1 Q2 s)ᵀ = rpath Q1 Q2 s := by
  simp [rpath, Matrix.transpose_add, Matrix.transpose_smul, h1, h2]

/-- If `Q'' + Q'² ⪯ 0` along the quadratic path `Q(s) = Q₀ + s Q₁ + s² Q₂` on `[a, b]`, then
`s ↦ tr exp Q(s)` is concave on `[a, b]`. -/
theorem concaveOn_trexp_qpath (Q0 Q1 Q2 : Matrix (Fin q) (Fin q) ℝ) (h0 : Q0ᵀ = Q0)
    (h1 : Q1ᵀ = Q1) (h2 : Q2ᵀ = Q2) (a b : ℝ)
    (hneg : ∀ s ∈ Set.Icc a b, ∀ v : Fin q → ℝ,
      v ⬝ᵥ (((2 : ℝ) • Q2 + rpath Q1 Q2 s * rpath Q1 Q2 s) *ᵥ v) ≤ 0) :
    ConcaveOn ℝ (Set.Icc a b) (fun s => trexp (qpath Q0 Q1 Q2 s)) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
    (f' := fun s => ∑' m, ((m.factorial : ℝ))⁻¹ * (qpath Q0 Q1 Q2 s ^ m * rpath Q1 Q2 s).trace)
    (f'' := fun s => ∑' m, ((m.factorial : ℝ))⁻¹ * (dpow (qpath Q0 Q1 Q2 s) (rpath Q1 Q2 s) m
        * rpath Q1 Q2 s + qpath Q0 Q1 Q2 s ^ m * ((2 : ℝ) • Q2)).trace)
    (fun s _ => (hasDerivAt_trexp_qpath Q0 Q1 Q2 s).continuousAt.continuousWithinAt)
    (fun s _ => (hasDerivAt_trexp_qpath Q0 Q1 Q2 s).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_trexp_qpath' Q0 Q1 Q2 s).hasDerivWithinAt) ?_
  intro s hs
  exact tsum_second_nonpos _ _ _ (transpose_qpath Q0 Q1 Q2 h0 h1 h2 s)
    (transpose_rpath Q1 Q2 h1 h2 s) (hneg s (interior_subset hs))

/-! ### Quadratic forms -/

section Forms

variable {ι : Type*}

/-- The quadratic form `v ↦ vᵀ M v`. -/
def qf (M : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) : ℝ := v ⬝ᵥ (M *ᵥ v)

lemma qf_add (M N : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    qf (M + N) v = qf M v + qf N v := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

lemma qf_sub (M N : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    qf (M - N) v = qf M v - qf N v := by
  simp [qf, Matrix.sub_mulVec, dotProduct_sub]

lemma qf_smul (c : ℝ) (M : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    qf (c • M) v = c * qf M v := by
  simp [qf, Matrix.smul_mulVec, dotProduct_smul]

lemma qf_sum (s : Finset ι) (M : ι → Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    qf (∑ j ∈ s, M j) v = ∑ j ∈ s, qf (M j) v := by
  simp [qf, Matrix.sum_mulVec, dotProduct_sum]

lemma qf_one (v : Fin q → ℝ) : qf 1 v = v ⬝ᵥ v := by
  simp [qf]

lemma qf_mul_self (A : Matrix (Fin q) (Fin q) ℝ) (hA : Aᵀ = A) (v : Fin q → ℝ) :
    qf (A * A) v = (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  simp only [qf]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

lemma dot_self_nonneg (v : Fin q → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

lemma psd_symm {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosSemidef) : Aᵀ = A := by
  have := hA.isHermitian.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma psd_qf_nonneg {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosSemidef) (v : Fin q → ℝ) :
    0 ≤ qf A v := by
  have := hA.dotProduct_mulVec_nonneg v
  simpa [qf] using this

/-- Cauchy–Schwarz for a positive semidefinite form. -/
lemma psd_cs {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosSemidef) (u w : Fin q → ℝ) :
    (u ⬝ᵥ (A *ᵥ w)) ^ 2 ≤ qf A u * qf A w := by
  have hsym := psd_symm hA
  have hswap : w ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ w) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  have key : ∀ s : ℝ, 0 ≤ qf A w * (s * s) + 2 * (u ⬝ᵥ (A *ᵥ w)) * s + qf A u := by
    intro s
    have h0 := psd_qf_nonneg hA (u + s • w)
    have e : qf A (u + s • w) = qf A w * (s * s) + 2 * (u ⬝ᵥ (A *ᵥ w)) * s + qf A u := by
      simp only [qf, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hswap]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

/-- `A² ⪯ b A` for `0 ⪯ A ⪯ b I`. -/
lemma psd_sq_le {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosSemidef) {b : ℝ} (hAb : QuadLe A b)
    (hb : 0 ≤ b) (w : Fin q → ℝ) : (A *ᵥ w) ⬝ᵥ (A *ᵥ w) ≤ b * qf A w := by
  set u := A *ᵥ w with hu
  have hcs := psd_cs hA u w
  have h1 : qf A u ≤ b * (u ⬝ᵥ u) := hAb u
  have h2 : 0 ≤ qf A w := psd_qf_nonneg hA w
  have h3 : 0 ≤ u ⬝ᵥ u := dot_self_nonneg u
  rcases h3.eq_or_lt with h | h
  · rw [← h]; positivity
  · have h4 : (u ⬝ᵥ u) ^ 2 ≤ (b * (u ⬝ᵥ u)) * qf A w :=
      hcs.trans (mul_le_mul_of_nonneg_right h1 h2)
    have h5 : u ⬝ᵥ u * (u ⬝ᵥ u) ≤ u ⬝ᵥ u * (b * qf A w) := by nlinarith [h4]
    exact le_of_mul_le_mul_left h5 h

lemma norm_add_smul_le {A : Matrix (Fin q) (Fin q) ℝ} (hA : A.PosSemidef) {b : ℝ}
    (hAb : QuadLe A b) (hb : 0 ≤ b) (w : Fin q → ℝ) (c : ℝ) :
    (w + c • (A *ᵥ w)) ⬝ᵥ (w + c • (A *ᵥ w)) ≤ (1 + |c| * b) ^ 2 * (w ⬝ᵥ w) := by
  have e : (w + c • (A *ᵥ w)) ⬝ᵥ (w + c • (A *ᵥ w)) =
      w ⬝ᵥ w + 2 * c * qf A w + c ^ 2 * ((A *ᵥ w) ⬝ᵥ (A *ᵥ w)) := by
    simp only [qf, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [dotProduct_comm (A *ᵥ w) w]
    ring
  rw [e]
  have h1 := psd_qf_nonneg hA w
  have h2 : qf A w ≤ b * (w ⬝ᵥ w) := hAb w
  have h3 := psd_sq_le hA hAb hb w
  have hc : 2 * c * qf A w ≤ 2 * |c| * (b * (w ⬝ᵥ w)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self c) h1
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
    linarith
  have hc2 : c ^ 2 * ((A *ᵥ w) ⬝ᵥ (A *ᵥ w)) ≤ c ^ 2 * (b * (b * (w ⬝ᵥ w))) :=
    mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h2 hb)) (sq_nonneg c)
  have e2 : (1 + |c| * b) ^ 2 * (w ⬝ᵥ w) =
      w ⬝ᵥ w + 2 * |c| * (b * (w ⬝ᵥ w)) + |c| ^ 2 * (b * (b * (w ⬝ᵥ w))) := by ring
  rw [e2, sq_abs]
  linarith

lemma dot_sum_le (s : Finset ι) (u : ι → Fin q → ℝ) :
    (∑ j ∈ s, u j) ⬝ᵥ (∑ j ∈ s, u j) ≤ s.card * ∑ j ∈ s, u j ⬝ᵥ u j := by
  simp only [dotProduct, Finset.sum_apply]
  calc ∑ k, (∑ j ∈ s, u j k) * (∑ j ∈ s, u j k)
      ≤ ∑ k, (s.card * ∑ j ∈ s, u j k ^ 2) :=
        Finset.sum_le_sum fun k _ => by rw [← sq]; exact sq_sum_le_card_mul_sum_sq
    _ = s.card * ∑ j ∈ s, ∑ k, u j k * u j k := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp [sq]

end Forms

/-! ### The potential along a line -/

section Line

variable {ι : Type*} [Fintype ι]

/-- The random part of the exponent: `θ ∑ y_j A_j + 8θ² ∑ y_j (1 - y_j) A_j²`. -/
noncomputable def lin (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (y : ι → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  ∑ j, (θ * y j) • A j + ∑ j, (8 * θ ^ 2 * (y j * (1 - y j))) • (A j * A j)

/-- The coefficient of `t` along the line `x + t h`. -/
noncomputable def lineQ1 (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (x h : ι → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  ∑ j, (θ * h j) • (A j + (8 * θ * (1 - 2 * x j)) • (A j * A j))

/-- The coefficient of `t²` along the line `x + t h`. -/
noncomputable def lineQ2 (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (h : ι → ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  ∑ j, (-(8 * θ ^ 2) * h j ^ 2) • (A j * A j)

lemma lin_line (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ) :
    lin A θ (x + t • h) = lin A θ x + t • lineQ1 A θ x h + t ^ 2 • lineQ2 A θ h := by
  simp only [lin, lineQ1, lineQ2, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_add, smul_smul]
  module

lemma rpath_line (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (x h : ι → ℝ) (t : ℝ) :
    rpath (lineQ1 A θ x h) (lineQ2 A θ h) t =
      ∑ j, (θ * h j) • (A j + (8 * θ * (1 - 2 * (x j + t * h j))) • (A j * A j)) := by
  simp only [rpath, lineQ1, lineQ2, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_add, smul_smul]
  module

lemma two_lineQ2 (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (h : ι → ℝ) :
    (2 : ℝ) • lineQ2 A θ h = ∑ j, (-(16 * θ ^ 2) * h j ^ 2) • (A j * A j) := by
  simp only [lineQ2, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

lemma transpose_sum_smul (c : ι → ℝ) (B : ι → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ j, (B j)ᵀ = B j) : (∑ j, c j • B j)ᵀ = ∑ j, c j • B j := by
  rw [Matrix.transpose_sum]
  simp [Matrix.transpose_smul, hB]

lemma transpose_mul_self {B : Matrix (Fin q) (Fin q) ℝ} (hB : Bᵀ = B) : (B * B)ᵀ = B * B := by
  rw [Matrix.transpose_mul, hB]

lemma transpose_lin (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ j, (A j)ᵀ = A j) (θ : ℝ)
    (y : ι → ℝ) : (lin A θ y)ᵀ = lin A θ y := by
  unfold lin
  rw [Matrix.transpose_add, transpose_sum_smul _ _ hA,
    transpose_sum_smul _ _ fun j => transpose_mul_self (hA j)]

lemma transpose_lineQ1 (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ j, (A j)ᵀ = A j) (θ : ℝ)
    (x h : ι → ℝ) : (lineQ1 A θ x h)ᵀ = lineQ1 A θ x h := by
  unfold lineQ1
  refine transpose_sum_smul _ _ fun j => ?_
  rw [Matrix.transpose_add, Matrix.transpose_smul, transpose_mul_self (hA j), hA j]

lemma transpose_lineQ2 (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ j, (A j)ᵀ = A j) (θ : ℝ)
    (h : ι → ℝ) : (lineQ2 A θ h)ᵀ = lineQ2 A θ h :=
  transpose_sum_smul _ _ fun j => transpose_mul_self (hA j)

/-- `Q'' + Q'² ⪯ 0` along an allowed line (Lemma 4.3). -/
lemma line_neg (S : Finset ι) (A : ι → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ i, (A i).PosSemidef) {b : ℝ} (hb : 0 < b) (hAb : ∀ i, QuadLe (A i) b)
    (hAS : ∀ i ∉ S, A i = 0) {θ : ℝ} (hθ : |θ| * b ≤ 1 / 16) (h : ι → ℝ)
    (hcard : (S.filter fun i => h i ≠ 0).card ≤ 4) (y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (v : Fin q → ℝ) :
    qf (∑ j, (-(16 * θ ^ 2) * h j ^ 2) • (A j * A j) +
      (∑ j, (θ * h j) • (A j + (8 * θ * (1 - 2 * y j)) • (A j * A j))) *
      (∑ j, (θ * h j) • (A j + (8 * θ * (1 - 2 * y j)) • (A j * A j)))) v ≤ 0 := by
  have hsym : ∀ j, (A j)ᵀ = A j := fun j => psd_symm (hA j)
  set R := ∑ j, (θ * h j) • (A j + (8 * θ * (1 - 2 * y j)) • (A j * A j)) with hR
  have hRs : Rᵀ = R := by
    rw [hR]
    refine transpose_sum_smul _ _ fun j => ?_
    rw [Matrix.transpose_add, Matrix.transpose_smul, transpose_mul_self (hsym j), hsym j]
  set w : ι → Fin q → ℝ := fun j => A j *ᵥ v with hw
  set c : ι → ℝ := fun j => 8 * θ * (1 - 2 * y j) with hc
  set u : ι → Fin q → ℝ := fun j => (θ * h j) • (w j + c j • (A j *ᵥ w j)) with hu
  have hRv : R *ᵥ v = ∑ j, u j := by
    rw [hR, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu, hw, hc, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  set K := ∑ j, h j ^ 2 * (w j ⬝ᵥ w j) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (dot_self_nonneg _)
  have hW : qf (∑ j, (-(16 * θ ^ 2) * h j ^ 2) • (A j * A j)) v = -(16 * θ ^ 2) * K := by
    rw [qf_sum, hK, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [qf_smul, qf_mul_self _ (hsym j)]
    ring
  -- the terms vanish off the support of `h` in `S`
  set J := S.filter fun i => h i ≠ 0 with hJ
  have hu0 : ∀ j ∉ J, u j = 0 := by
    intro j hj
    rw [hJ, Finset.mem_filter, not_and_or, not_not] at hj
    rcases hj with hj | hj
    · simp [hu, hw, hAS j hj]
    · simp [hu, hj]
  have hsumJ : ∑ j, u j = ∑ j ∈ J, u j :=
    (Finset.sum_subset (Finset.subset_univ J) fun j _ hj => hu0 j hj).symm
  have huu : ∀ j, u j ⬝ᵥ u j ≤ θ ^ 2 * (9 / 4) * (h j ^ 2 * (w j ⬝ᵥ w j)) := by
    intro j
    have e : u j ⬝ᵥ u j = (θ * h j) ^ 2 * ((w j + c j • (A j *ᵥ w j)) ⬝ᵥ
        (w j + c j • (A j *ᵥ w j))) := by
      simp only [hu, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [e]
    have h1 := norm_add_smul_le (hA j) (hAb j) hb.le (w j) (c j)
    have hcb : |c j| * b ≤ 1 / 2 := by
      have hy1 : |1 - 2 * y j| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(hy j).1, (hy j).2]
      simp only [hc, abs_mul]
      have : |(8 : ℝ)| = 8 := by norm_num
      rw [this]
      calc 8 * |θ| * |1 - 2 * y j| * b ≤ 8 * |θ| * 1 * b := by
            gcongr
        _ ≤ 1 / 2 := by nlinarith [hθ]
    have h2 : (1 + |c j| * b) ^ 2 ≤ 9 / 4 := by
      have : 0 ≤ |c j| * b := mul_nonneg (abs_nonneg _) hb.le
      nlinarith
    have h3 : (1 + |c j| * b) ^ 2 * (w j ⬝ᵥ w j) ≤ 9 / 4 * (w j ⬝ᵥ w j) :=
      mul_le_mul_of_nonneg_right h2 (dot_self_nonneg _)
    calc (θ * h j) ^ 2 * ((w j + c j • (A j *ᵥ w j)) ⬝ᵥ (w j + c j • (A j *ᵥ w j)))
        ≤ (θ * h j) ^ 2 * (9 / 4 * (w j ⬝ᵥ w j)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) (sq_nonneg _)
      _ = θ ^ 2 * (9 / 4) * (h j ^ 2 * (w j ⬝ᵥ w j)) := by ring
  have hRR : qf (R * R) v ≤ 9 * θ ^ 2 * K := by
    rw [qf_mul_self R hRs, hRv, hsumJ]
    calc (∑ j ∈ J, u j) ⬝ᵥ (∑ j ∈ J, u j) ≤ J.card * ∑ j ∈ J, u j ⬝ᵥ u j := dot_sum_le J u
      _ ≤ 4 * ∑ j, u j ⬝ᵥ u j := by
          have h1 : (J.card : ℝ) ≤ 4 := by exact_mod_cast hcard
          have h2 : ∑ j ∈ J, u j ⬝ᵥ u j ≤ ∑ j, u j ⬝ᵥ u j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
              fun j _ _ => dot_self_nonneg _
          have h3 : 0 ≤ ∑ j ∈ J, u j ⬝ᵥ u j := Finset.sum_nonneg fun j _ => dot_self_nonneg _
          nlinarith
      _ ≤ 4 * ∑ j, θ ^ 2 * (9 / 4) * (h j ^ 2 * (w j ⬝ᵥ w j)) := by
          gcongr with j _
          exact huu j
      _ = 9 * θ ^ 2 * K := by rw [hK, ← Finset.mul_sum]; ring
  rw [qf_add, hW]
  nlinarith [sq_nonneg θ]

/-- The exponent `H + θ ∑ y_j A_j + 8θ² ∑ y_j(1 - y_j) A_j²` of the potential. -/
noncomputable def expo (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (H : Matrix (Fin q) (Fin q) ℝ)
    (y : ι → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  H + lin A θ y

lemma expo_line (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (H : Matrix (Fin q) (Fin q) ℝ)
    (x h : ι → ℝ) (t : ℝ) :
    expo A θ H (x + t • h) = qpath (expo A θ H x) (lineQ1 A θ x h) (lineQ2 A θ h) t := by
  simp only [expo, qpath, lin_line]
  abel

/-- The supermartingale inequality for one two-point move (Lemma 4.3). -/
theorem move_ineq (S : Finset ι) (A : ι → Matrix (Fin q) (Fin q) ℝ)
    (hA : ∀ i, (A i).PosSemidef) {b : ℝ} (hb : 0 < b) (hAb : ∀ i, QuadLe (A i) b)
    (hAS : ∀ i ∉ S, A i = 0) {θ : ℝ} (hθ : |θ| * b ≤ 1 / 16) (H : Matrix (Fin q) (Fin q) ℝ)
    (hH : Hᵀ = H) (x h : ι → ℝ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hcard : (S.filter fun i => h i ≠ 0).card ≤ 4)
    (h1 : ∀ i, 0 ≤ (x + α • h) i ∧ (x + α • h) i ≤ 1)
    (h2 : ∀ i, 0 ≤ (x - β • h) i ∧ (x - β • h) i ≤ 1) :
    β / (α + β) * trexp (expo A θ H (x + α • h)) +
        (1 - β / (α + β)) * trexp (expo A θ H (x - β • h)) ≤ trexp (expo A θ H x) := by
  have hsym : ∀ j, (A j)ᵀ = A j := fun j => psd_symm (hA j)
  have hQ0 : (expo A θ H x)ᵀ = expo A θ H x := by
    rw [expo, Matrix.transpose_add, hH, transpose_lin A hsym]
  have hneg : ∀ s ∈ Set.Icc (-β) α, ∀ v : Fin q → ℝ,
      v ⬝ᵥ (((2 : ℝ) • lineQ2 A θ h + rpath (lineQ1 A θ x h) (lineQ2 A θ h) s *
        rpath (lineQ1 A θ x h) (lineQ2 A θ h) s) *ᵥ v) ≤ 0 := by
    intro s hs v
    have hy : ∀ i, 0 ≤ x i + s * h i ∧ x i + s * h i ≤ 1 := by
      intro i
      have a1 := h1 i
      have a2 := h2 i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a1 a2
      rcases le_total 0 (h i) with hh | hh
      · have b1 : s * h i ≤ α * h i := mul_le_mul_of_nonneg_right hs.2 hh
        have b2 : -β * h i ≤ s * h i := mul_le_mul_of_nonneg_right hs.1 hh
        constructor <;> nlinarith
      · have b1 : α * h i ≤ s * h i := mul_le_mul_of_nonpos_right hs.2 hh
        have b2 : s * h i ≤ -β * h i := mul_le_mul_of_nonpos_right hs.1 hh
        constructor <;> nlinarith
    have := line_neg S A hA hb hAb hAS hθ h hcard (fun i => x i + s * h i) hy v
    rw [two_lineQ2, rpath_line]
    exact this
  have hconc := concaveOn_trexp_qpath (expo A θ H x) (lineQ1 A θ x h) (lineQ2 A θ h) hQ0
    (transpose_lineQ1 A hsym θ x h) (transpose_lineQ2 A hsym θ h) (-β) α hneg
  have hab : 0 < α + β := by linarith
  have hp0 : 0 ≤ β / (α + β) := div_nonneg hβ.le hab.le
  have hp1 : 0 ≤ 1 - β / (α + β) := by
    rw [sub_nonneg, div_le_one hab]; linarith
  have key := hconc.2 (x := α) ⟨by linarith, le_rfl⟩ (y := -β) ⟨le_rfl, by linarith⟩ hp0 hp1
    (by ring)
  simp only [smul_eq_mul] at key
  have hz : β / (α + β) * α + (1 - β / (α + β)) * -β = 0 := by
    field_simp
    ring
  rw [hz] at key
  have e1 : qpath (expo A θ H x) (lineQ1 A θ x h) (lineQ2 A θ h) α = expo A θ H (x + α • h) :=
    (expo_line A θ H x h α).symm
  have e2 : qpath (expo A θ H x) (lineQ1 A θ x h) (lineQ2 A θ h) (-β) =
      expo A θ H (x - β • h) := by
    rw [← expo_line, neg_smul, ← sub_eq_add_neg]
  have e3 : qpath (expo A θ H x) (lineQ1 A θ x h) (lineQ2 A θ h) 0 = expo A θ H x := by
    simp [qpath]
  rw [e1, e2, e3] at key
  exact key

end Line

/-! ### The supermartingale argument -/

section Process

variable {α : Type*}

lemma expect_dirac (a : α) (f : α → ℝ) : (FinDist.dirac a).expect f = f a := by
  simp [FinDist.expect, FinDist.dirac]

open Classical in
lemma expect_mix (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ₁ μ₂ : FinDist α)
    (h₁ : μ₁.IsExact) (h₂ : μ₂.IsExact) (f : α → ℝ) :
    (FinDist.mix p hp μ₁ μ₂ h₁ h₂).expect f = p * μ₁.expect f + (1 - p) * μ₂.expect f := by
  have hs1 : μ₁.support ⊆ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support := Finset.subset_union_left
  have hs2 : μ₂.support ⊆ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support := Finset.subset_union_right
  have e₁ : ∑ a ∈ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support, μ₁.prob a * f a = μ₁.expect f :=
    (Finset.sum_subset hs1 fun a _ ha => by simp [h₁ a ha]).symm
  have e₂ : ∑ a ∈ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support, μ₂.prob a * f a = μ₂.expect f :=
    (Finset.sum_subset hs2 fun a _ ha => by simp [h₂ a ha]).symm
  rw [← e₁, ← e₂, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (p * μ₁.prob a + (1 - p) * μ₂.prob a) * f a = _
  ring

open Classical in
lemma P_eq_expect (μ : FinDist α) (E : α → Prop) :
    μ.P E = μ.expect fun a => if E a then 1 else 0 := by
  unfold FinDist.P FinDist.expect
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hE : E a <;> simp [hE]

variable {ι : Type*}

lemma lp_start_mem {ok : (ι → ℝ) → Prop} {x : ι → ℝ} {μ : FinDist (ι → ℝ)}
    (hμ : LineProcess ok x μ) : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  cases hμ with
  | stop _ hx => exact hx
  | move _ _ _ _ _ _ _ _ _ _ hx _ _ _ => exact hx

/-- Monotonicity of the terminal expectation, for functions ordered on the cube. -/
lemma lp_expect_mono {ok : (ι → ℝ) → Prop} {x : ι → ℝ} {μ : FinDist (ι → ℝ)}
    (hμ : LineProcess ok x μ) (f g : (ι → ℝ) → ℝ)
    (hfg : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → f y ≤ g y) : μ.expect f ≤ μ.expect g := by
  induction hμ with
  | stop x hx => rw [expect_dirac, expect_dirac]; exact hfg x hx
  | move x h α β μ₁ μ₂ hα hβ h₁ h₂ hx hok _ _ ih₁ ih₂ =>
    rw [expect_mix, expect_mix]
    have hp0 : 0 ≤ β / (α + β) := div_nonneg hβ.le (add_pos hα hβ).le
    have hp1 : 0 ≤ 1 - β / (α + β) := by
      rw [sub_nonneg, div_le_one (add_pos hα hβ)]; linarith
    have := mul_le_mul_of_nonneg_left ih₁ hp0
    have := mul_le_mul_of_nonneg_left ih₂ hp1
    linarith

/-- The supermartingale inequality `E Ψ(z) ≤ Ψ(x)`. -/
lemma lp_expect_le {ok : (ι → ℝ) → Prop} {x : ι → ℝ} {μ : FinDist (ι → ℝ)}
    (hμ : LineProcess ok x μ) (Ψ : (ι → ℝ) → ℝ)
    (hΨ : ∀ (x h : ι → ℝ) (α β : ℝ), 0 < α → 0 < β → ok h →
      (∀ i, 0 ≤ (x + α • h) i ∧ (x + α • h) i ≤ 1) →
      (∀ i, 0 ≤ (x - β • h) i ∧ (x - β • h) i ≤ 1) →
      β / (α + β) * Ψ (x + α • h) + (1 - β / (α + β)) * Ψ (x - β • h) ≤ Ψ x) :
    μ.expect Ψ ≤ Ψ x := by
  induction hμ with
  | stop x hx => rw [expect_dirac]
  | move x h α β μ₁ μ₂ hα hβ h₁ h₂ hx hok hp₁ hp₂ ih₁ ih₂ =>
    rw [expect_mix]
    have hp0 : 0 ≤ β / (α + β) := div_nonneg hβ.le (add_pos hα hβ).le
    have hp1 : 0 ≤ 1 - β / (α + β) := by
      rw [sub_nonneg, div_le_one (add_pos hα hβ)]; linarith
    have := mul_le_mul_of_nonneg_left ih₁ hp0
    have := mul_le_mul_of_nonneg_left ih₂ hp1
    have := hΨ x h α β hα hβ hok (lp_start_mem hp₁) (lp_start_mem hp₂)
    linarith

end Process

/-! ### The tail bounds -/

section Tail

variable {ι : Type*} [Fintype ι]

lemma qf_lin (A : ι → Matrix (Fin q) (Fin q) ℝ) (θ : ℝ) (y : ι → ℝ) (v : Fin q → ℝ) :
    qf (lin A θ y) v = θ * ∑ j, y j * qf (A j) v +
      8 * θ ^ 2 * ∑ j, (y j * (1 - y j)) * qf (A j * A j) v := by
  rw [lin, qf_add, qf_sum, qf_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by rw [qf_smul]; ring

lemma qf_sum_smul (A : ι → Matrix (Fin q) (Fin q) ℝ) (y : ι → ℝ) (v : Fin q → ℝ) :
    qf (∑ i, y i • A i) v = ∑ i, y i * qf (A i) v := by
  rw [qf_sum]
  exact Finset.sum_congr rfl fun i _ => qf_smul _ _ _

/-- Markov's inequality for the trace-exponential supermartingale. -/
theorem tail_bound (S : Finset ι) (ok : (ι → ℝ) → Prop)
    (hok : ∀ h, ok h → (S.filter fun i => h i ≠ 0).card ≤ 4)
    (x : ι → ℝ) (μ : FinDist (ι → ℝ)) (hμ : LineProcess ok x μ)
    (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ i, (A i).PosSemidef) {b : ℝ} (hb : 0 < b)
    (hAb : ∀ i, QuadLe (A i) b) (hAS : ∀ i ∉ S, A i = 0) {θ : ℝ} (hθ : |θ| * b ≤ 1 / 16)
    (H : Matrix (Fin q) (Fin q) ℝ) (hH : Hᵀ = H) (Ev : (ι → ℝ) → Prop)
    (hEv : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) → Ev z → 1 ≤ trexp (expo A θ H z)) :
    μ.P Ev ≤ trexp (expo A θ H x) := by
  have hsym : ∀ j, (A j)ᵀ = A j := fun j => psd_symm (hA j)
  have hEs : ∀ y, (expo A θ H y)ᵀ = expo A θ H y := fun y => by
    rw [expo, Matrix.transpose_add, hH, transpose_lin A hsym]
  rw [P_eq_expect]
  refine (lp_expect_mono hμ _ (fun y => trexp (expo A θ H y)) fun y hy => ?_).trans ?_
  · split_ifs with hE
    · exact hEv y hy hE
    · exact trexp_nonneg _ (hEs y)
  · refine lp_expect_le hμ _ fun x h α β hα hβ hokh h1 h2 => ?_
    exact move_ineq S A hA hb hAb hAS hθ H hH x h α β hα hβ (hok h hokh) h1 h2

/-- The tail estimate for a signed parameter `θ` (upper tail `θ > 0`, lower tail `θ < 0`). -/
theorem tail_general (S : Finset ι) (ok : (ι → ℝ) → Prop)
    (hok : ∀ h, ok h → (S.filter fun i => h i ≠ 0).card ≤ 4)
    (x : ι → ℝ) (μ : FinDist (ι → ℝ)) (hμ : LineProcess ok x μ)
    (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ i, (A i).PosSemidef) {b ν t : ℝ} (hb : 0 < b)
    (hAb : ∀ i, QuadLe (A i) b) (hAS : ∀ i ∉ S, A i = 0) (hM : QuadLe (∑ i, x i • A i) ν)
    {θ : ℝ} (hθ : |θ| * b ≤ 1 / 16) (Ev : (ι → ℝ) → Prop)
    (hEv : ∀ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ 1) → Ev z → ∃ v : Fin q → ℝ, v ⬝ᵥ v = 1 ∧
      |θ| * t ≤ θ * qf (∑ i, z i • A i - ∑ i, x i • A i) v) :
    μ.P Ev ≤ q * Real.exp (-|θ| * t + 8 * θ ^ 2 * b * ν) := by
  set M := ∑ i, x i • A i with hMdef
  set H : Matrix (Fin q) (Fin q) ℝ := (-θ) • M - (|θ| * t) • 1 with hHdef
  have hsym : ∀ j, (A j)ᵀ = A j := fun j => psd_symm (hA j)
  have hMs : Mᵀ = M := transpose_sum_smul _ _ hsym
  have hH : Hᵀ = H := by
    rw [hHdef, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, hMs,
      Matrix.transpose_one]
  have hEs : ∀ y, (expo A θ H y)ᵀ = expo A θ H y := fun y => by
    rw [expo, Matrix.transpose_add, hH, transpose_lin A hsym]
  have hqH : ∀ v, qf H v = -θ * ∑ i, x i * qf (A i) v - |θ| * t * (v ⬝ᵥ v) := by
    intro v
    rw [hHdef, qf_sub, qf_smul, qf_smul, qf_one, hMdef, qf_sum_smul]
  have hx := lp_start_mem hμ
  have hn : ∀ i v, 0 ≤ qf (A i * A i) v := fun i v => by
    rw [qf_mul_self _ (hsym i)]; exact dot_self_nonneg _
  refine (tail_bound S ok hok x μ hμ A hA hb hAb hAS hθ H hH Ev ?_).trans ?_
  · intro z hz hE
    obtain ⟨v, hv, hineq⟩ := hEv z hz hE
    refine one_le_trexp _ (hEs z) v hv ?_
    change 0 ≤ qf (expo A θ H z) v
    rw [expo, qf_add, hqH, qf_lin, hv]
    rw [qf_sub, qf_sum_smul, qf_sum_smul] at hineq
    have h1 : 0 ≤ ∑ j, (z j * (1 - z j)) * qf (A j * A j) v :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hz j).1 (by linarith [(hz j).2]))
        (hn j v)
    have h2 : 0 ≤ 8 * θ ^ 2 * ∑ j, (z j * (1 - z j)) * qf (A j * A j) v := by positivity
    nlinarith
  · refine trexp_le _ (hEs x) _ fun v => ?_
    change qf (expo A θ H x) v ≤ _
    rw [expo, qf_add, hqH, qf_lin]
    have hMv : qf M v ≤ ν * (v ⬝ᵥ v) := hM v
    rw [hMdef, qf_sum_smul] at hMv
    have h1 : ∑ j, (x j * (1 - x j)) * qf (A j * A j) v ≤ b * ∑ j, x j * qf (A j) v := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have a1 : qf (A j * A j) v ≤ b * qf (A j) v := by
        rw [qf_mul_self _ (hsym j)]; exact psd_sq_le (hA j) (hAb j) hb.le v
      have a2 := hn j v
      have a3 := (hx j).1
      have a4 := (hx j).2
      nlinarith [mul_nonneg a3 a2, mul_nonneg (mul_nonneg a3 a3) a2]
    have h2 : 8 * θ ^ 2 * ∑ j, (x j * (1 - x j)) * qf (A j * A j) v ≤
        8 * θ ^ 2 * (b * (ν * (v ⬝ᵥ v))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact h1.trans (mul_le_mul_of_nonneg_left hMv hb.le)
    nlinarith

end Tail

end Lovasz.TraceConc

namespace Lovasz

open TraceConc

/-- **Lemma 4.3 (Bounded-support concentration).** Let a line process start at `x` and suppose
each of its directions has at most four nonzero coordinates in `S`. For positive semidefinite
`q × q` matrices `A_j` (zero for `j ∉ S`) with `‖A_j‖ ≤ b`, put `M = ∑ x_j A_j` and
`Z = ∑ z_j A_j` for the terminal point `z`. If `‖M‖ ≤ ν`, then for `t > 0`,
`P(λ_max(Z - M) ≥ t) ≤ q exp(-t² / (32 b (ν + t)))`, and the same bound holds for
`P(λ_min(Z - M) ≤ -t)`. -/
theorem bounded_support_concentration {ι : Type*} [Fintype ι] {q : ℕ}
    (S : Finset ι) (ok : (ι → ℝ) → Prop)
    (hok : ∀ h, ok h → (S.filter fun i => h i ≠ 0).card ≤ 4)
    (x : ι → ℝ) (μ : FinDist (ι → ℝ)) (hμ : LineProcess ok x μ)
    (A : ι → Matrix (Fin q) (Fin q) ℝ) (hA : ∀ i, (A i).PosSemidef) (b ν t : ℝ) (hb : 0 < b)
    (hAb : ∀ i, QuadLe (A i) b) (hAS : ∀ i ∉ S, A i = 0)
    (hM : QuadLe (∑ i, x i • A i) ν) (ht : 0 < t) :
    μ.P (fun z => LamMaxGe (∑ i, z i • A i - ∑ i, x i • A i) t) ≤
        q * Real.exp (-(t ^ 2) / (32 * b * (ν + t))) ∧
      μ.P (fun z => LamMinLe (∑ i, z i • A i - ∑ i, x i • A i) (-t)) ≤
        q * Real.exp (-(t ^ 2) / (32 * b * (ν + t))) := by
  rcases Nat.eq_zero_or_pos q with hq0 | hq
  · subst hq0
    simp [FinDist.P, LamMaxGe, LamMinLe, dotProduct]
  have hx := lp_start_mem hμ
  have hν : 0 ≤ ν := by
    set v : Fin q → ℝ := Pi.single ⟨0, hq⟩ 1 with hvdef
    have hv : v ⬝ᵥ v = 1 := by simp [hvdef]
    have h1 := hM v
    have h0 : 0 ≤ qf (∑ i, x i • A i) v := by
      rw [qf_sum_smul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hx i).1 (psd_qf_nonneg (hA i) v)
    change qf (∑ i, x i • A i) v ≤ ν * (v ⬝ᵥ v) at h1
    rw [hv, mul_one] at h1
    linarith
  have hD : 0 < ν + t := by linarith
  set θ₀ := t / (16 * b * (ν + t)) with hθ₀def
  have hθ₀ : 0 < θ₀ := by positivity
  have hθb : |θ₀| * b ≤ 1 / 16 := by
    rw [abs_of_pos hθ₀, hθ₀def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hθb' : |-θ₀| * b ≤ 1 / 16 := by rwa [abs_neg]
  have hexp : -|θ₀| * t + 8 * θ₀ ^ 2 * b * ν ≤ -(t ^ 2) / (32 * b * (ν + t)) := by
    rw [abs_of_pos hθ₀]
    have e : -θ₀ * t + 8 * θ₀ ^ 2 * b * ν =
        -(t ^ 2) / (32 * b * (ν + t)) - t ^ 3 / (32 * b * (ν + t) ^ 2) := by
      rw [hθ₀def]
      field_simp
      ring
    rw [e]
    have : 0 ≤ t ^ 3 / (32 * b * (ν + t) ^ 2) := by positivity
    linarith
  have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  constructor
  · refine (tail_general S ok hok x μ hμ A hA hb hAb hAS hM (t := t) hθb _ ?_).trans ?_
    · rintro z - ⟨v, hv, hvt⟩
      refine ⟨v, hv, ?_⟩
      rw [abs_of_pos hθ₀]
      exact mul_le_mul_of_nonneg_left hvt hθ₀.le
    · gcongr
  · refine (tail_general S ok hok x μ hμ A hA hb hAb hAS hM (t := t) hθb' _ ?_).trans ?_
    · rintro z - ⟨v, hv, hvt⟩
      refine ⟨v, hv, ?_⟩
      rw [abs_neg, abs_of_pos hθ₀]
      change v ⬝ᵥ ((∑ i, z i • A i - ∑ i, x i • A i) *ᵥ v) ≤ -t at hvt
      change θ₀ * t ≤ -θ₀ * (v ⬝ᵥ ((∑ i, z i • A i - ∑ i, x i • A i) *ᵥ v))
      nlinarith
    · rw [abs_neg, neg_sq]
      gcongr

end Lovasz
