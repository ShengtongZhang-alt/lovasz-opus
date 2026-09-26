/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.3: distances after deletion

DAG node `L3.3` of `docs/BLUEPRINT.md`.

Proof, following the paper: `P = (I + N)/2` with `N = D^{-1/2} A D^{-1/2}` is symmetric, positive
semidefinite, fixes the stationary unit vector `u`, and has quadratic form at most `1 - σ/2` on
`u^⊥` (from `HasGap`). The compression `QPQ` to `Uᶜ` is diagonalized with
`Matrix.IsHermitian.eigenvectorBasis`; its top eigenvalue `θ ≥ 1 - σ/4` has an eigenvector `f`
with `‖f - u‖² ≤ 8‖u_U‖²/σ`, and all other eigenvalues lie in `[0, 1 - σ/2]`. The set `K` is
`{v ∉ U : f_v ≥ u_v/2}`. Entries of the Chebyshev polynomial `T_r(2 QPQ/(1 - σ/2) - 1)` are
positive on `K × K` for `r ≈ σ^{-1/2} log M`, and a nonzero entry of a degree-`r` polynomial in
`QPQ` yields a walk of length at most `r` in `F - U`.
-/

universe u

namespace Lovasz

open Finset

namespace DistanceDeletion

open Matrix Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Entries of powers of a matrix supported on lazy steps of `G - U` vanish unless there is a
short walk avoiding `U`. -/
lemma walk_of_pow_ne_zero (G : SimpleGraph V) (U : Finset V) (B : Matrix V V ℝ)
    (hB : ∀ z y, B z y ≠ 0 → z = y ∨ (y ∉ U ∧ G.Adj z y)) :
    ∀ (k : ℕ) (x y : V), x ∉ U → (B ^ k) x y ≠ 0 →
      ∃ p : G.Walk x y, (∀ z ∈ p.support, z ∉ U) ∧ p.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro x y hx h
    rw [pow_zero] at h
    by_cases hxy : x = y
    · subst hxy
      exact ⟨SimpleGraph.Walk.nil, by simpa using hx, by simp⟩
    · exact absurd (Matrix.one_apply_ne hxy) h
  | succ k ih =>
    intro x y hx h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (B ^ k) x z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
    have h2 : B z y ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    obtain ⟨p, hp, hpl⟩ := ih x z hx h1
    rcases hB z y h2 with rfl | ⟨hy, hadj⟩
    · exact ⟨p, hp, by omega⟩
    · refine ⟨p.concat hadj, ?_, ?_⟩
      · intro w hw
        rw [SimpleGraph.Walk.support_concat] at hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact hp w hw
        · exact hy
      · rw [SimpleGraph.Walk.length_concat]; omega

/-- Entries of a polynomial in such a matrix vanish unless there is a walk avoiding `U` of
length at most the degree. -/
lemma walk_of_aeval_ne_zero (G : SimpleGraph V) (U : Finset V) (B : Matrix V V ℝ)
    (hB : ∀ z y, B z y ≠ 0 → z = y ∨ (y ∉ U ∧ G.Adj z y)) (p : ℝ[X]) (x y : V) (hx : x ∉ U)
    (h : (aeval B p) x y ≠ 0) :
    ∃ w : G.Walk x y, (∀ z ∈ w.support, z ∉ U) ∧ w.length ≤ p.natDegree := by
  rw [aeval_eq_sum_range, Matrix.sum_apply] at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Matrix.smul_apply, smul_eq_mul] at hne
  have : (B ^ i) x y ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  obtain ⟨w, hw, hl⟩ := walk_of_pow_ne_zero G U B hB i x y hx this
  refine ⟨w, hw, hl.trans ?_⟩
  simp only [Finset.mem_range] at hi
  omega

/-- A polynomial in a matrix acts on an eigenvector by the evaluation at the eigenvalue. -/
lemma aeval_mulVec_of_mulVec_eq (B : Matrix V V ℝ) (w : V → ℝ) (c : ℝ) (hw : B *ᵥ w = c • w)
    (p : ℝ[X]) : aeval B p *ᵥ w = p.eval c • w := by
  have hpow : ∀ n : ℕ, (B ^ n) *ᵥ w = c ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, hpow, smul_smul]

/-- Expansion of the entries of a matrix acting diagonally on a complete orthonormal family. -/
lemma entry_eq_sum_of_eigen (v : V → V → ℝ)
    (hcomp : ∀ x y, ∑ i, v i x * v i y = if x = y then 1 else 0)
    (M : Matrix V V ℝ) (c : V → ℝ) (hM : ∀ i, M *ᵥ v i = c i • v i) (x y : V) :
    M x y = ∑ i, c i * v i x * v i y := by
  have hey : (fun z => if z = y then (1 : ℝ) else 0) = ∑ i, v i y • v i := by
    ext z
    rw [Finset.sum_apply, ← hcomp z y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hM' : M x y = (M *ᵥ (fun z => if z = y then (1 : ℝ) else 0)) x := by
    simp [Matrix.mulVec, dotProduct]
  rw [hM', hey, Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, hM i]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq V] in
/-- The quadratic form of `∑ᵢ cᵢ vᵢ vᵢᵀ`. -/
lemma quad_sum (v : V → V → ℝ) (c : V → ℝ) (g : V → ℝ) :
    ∑ x, g x * ∑ y, (∑ i, c i * v i x * v i y) * g y =
      ∑ i, c i * (∑ x, v i x * g x) ^ 2 := by
  calc ∑ x, g x * ∑ y, (∑ i, c i * v i x * v i y) * g y
      = ∑ x, ∑ y, ∑ i, c i * (v i x * g x) * (v i y * g y) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ x, ∑ i, ∑ y, c i * (v i x * g x) * (v i y * g y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, c i * (v i x * g x) * (v i y * g y) := Finset.sum_comm
    _ = ∑ i, c i * (∑ x, v i x * g x) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring

/-- Growth of Chebyshev polynomials beyond `1`. -/
lemma cheb_growth (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (x₀ : ℝ) (hx : 1 + σ / 2 ≤ x₀) (r : ℕ) :
    Real.exp (r * Real.sqrt σ / 2) / 2 ≤ (Chebyshev.T ℝ r).eval x₀ := by
  have hx1 : 1 ≤ x₀ := by linarith
  set q := Real.sqrt (x₀ ^ 2 - 1) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqsq : q ^ 2 = x₀ ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hsσ : Real.sqrt σ ≤ q := by
    rw [hq]
    exact Real.sqrt_le_sqrt (by nlinarith)
  set e := x₀ + q with he
  have he0 : 0 < e := by linarith
  have heinv : e⁻¹ = x₀ - q := by
    apply inv_eq_of_mul_eq_one_right
    rw [he]
    nlinarith
  set s := Real.log e with hs
  have hes : Real.exp s = e := Real.exp_log he0
  have hcosh : Real.cosh s = x₀ := by
    rw [Real.cosh_eq, Real.exp_neg, hes, heinv]
    ring
  have hsqrt0 : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt σ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hσ1
  have hs_lb : Real.sqrt σ / 2 ≤ s := by
    have h1 : Real.log (1 + Real.sqrt σ) ≤ s := Real.log_le_log (by linarith) (by linarith)
    have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + Real.sqrt σ by linarith)
    have h3 : Real.sqrt σ / 2 ≤ 1 - (1 + Real.sqrt σ)⁻¹ := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : (1 + Real.sqrt σ)⁻¹ = 1 / (1 + Real.sqrt σ) := by rw [one_div]
      rw [this]
      rw [sub_mul, div_mul_eq_mul_div, one_mul]
      rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hT : (Chebyshev.T ℝ r).eval x₀ = Real.cosh (r * s) := by
    rw [← hcosh]
    exact_mod_cast Polynomial.Chebyshev.T_real_cosh s (r : ℤ)
  rw [hT, Real.cosh_eq]
  have h1 : Real.exp (r * Real.sqrt σ / 2) ≤ Real.exp (r * s) := by
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  have h2 : 0 < Real.exp (-(r * s)) := Real.exp_pos _
  linarith

/-- The indicator of the complement of `U`. -/
noncomputable def ind (U : Finset V) (x : V) : ℝ := if x ∈ U then 0 else 1

/-- Restriction of a vector to the complement of `U` (extension by zero). -/
noncomputable def mask (U : Finset V) (g : V → ℝ) : V → ℝ := fun x => ind U x * g x

/-- The compression `Q P Q` of `P` to the complement of `U`. -/
noncomputable def maskMat (U : Finset V) (P : Matrix V V ℝ) : Matrix V V ℝ :=
  Matrix.of fun x y => ind U x * P x y * ind U y

omit [Fintype V] in
lemma ind_mul_self (U : Finset V) (x : V) : ind U x * ind U x = ind U x := by
  unfold ind; split_ifs <;> norm_num

omit [Fintype V] in
lemma mask_mask (U : Finset V) (g : V → ℝ) : mask U (mask U g) = mask U g := by
  ext x; simp only [mask, ← mul_assoc, ind_mul_self]

lemma maskMat_bil (U : Finset V) (P : Matrix V V ℝ) (g h : V → ℝ) :
    g ⬝ᵥ (maskMat U P *ᵥ h) = mask U g ⬝ᵥ (P *ᵥ mask U h) := by
  simp only [dotProduct, Matrix.mulVec, maskMat, mask, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma maskMat_mulVec_apply (U : Finset V) (P : Matrix V V ℝ) (h : V → ℝ) (x : V) :
    (maskMat U P *ᵥ h) x = ind U x * (P *ᵥ mask U h) x := by
  simp only [dotProduct, Matrix.mulVec, maskMat, mask, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

omit [DecidableEq V] in
lemma quad_of_entry (v : V → V → ℝ) (c : V → ℝ) (M : Matrix V V ℝ)
    (hM : ∀ x y, M x y = ∑ i, c i * v i x * v i y) (g : V → ℝ) :
    g ⬝ᵥ (M *ᵥ g) = ∑ i, c i * (∑ x, v i x * g x) ^ 2 := by
  rw [← quad_sum]
  simp only [dotProduct, Matrix.mulVec, hM]

omit [DecidableEq V] in
lemma dot_self_nonneg (g : V → ℝ) : 0 ≤ g ⬝ᵥ g :=
  Finset.sum_nonneg fun x _ => mul_self_nonneg (g x)

lemma abs_mul_le_half (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]

/-- Entries of Chebyshev polynomials of a matrix with a complete orthonormal eigenbasis whose
eigenvalues, apart from the one at `i₀`, lie in `[0, b₀]`. -/
lemma cheb_entry (v : V → V → ℝ) (hcomp : ∀ x y, ∑ i, v i x * v i y = if x = y then 1 else 0)
    (A : Matrix V V ℝ) (lam : V → ℝ) (hv : ∀ i, A *ᵥ v i = lam i • v i) (i₀ : V) (b₀ : ℝ)
    (hb₀ : 0 < b₀) (hother : ∀ i, i ≠ i₀ → 0 ≤ lam i ∧ lam i ≤ b₀) (r : ℕ) (x y : V) :
    (Chebyshev.T ℝ r).eval (2 * lam i₀ / b₀ - 1) * (v i₀ x * v i₀ y) - 1 ≤
      aeval ((2 / b₀) • A - 1) (Chebyshev.T ℝ r) x y := by
  have hBv : ∀ i, ((2 / b₀) • A - 1) *ᵥ v i = (2 / b₀ * lam i - 1) • v i := by
    intro i
    rw [sub_mulVec, smul_mulVec, hv i, one_mulVec, smul_smul, sub_smul, one_smul]
  rw [entry_eq_sum_of_eigen v hcomp (aeval ((2 / b₀) • A - 1) (Chebyshev.T ℝ r))
    (fun i => (Chebyshev.T ℝ r).eval (2 / b₀ * lam i - 1))
    (fun i => aeval_mulVec_of_mulVec_eq _ (v i) _ (hBv i) _) x y,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have hbound : ∀ i ∈ univ.erase i₀, -((v i x ^ 2 + v i y ^ 2) / 2) ≤
      (Chebyshev.T ℝ r).eval (2 / b₀ * lam i - 1) * v i x * v i y := by
    intro i hi
    obtain ⟨hl0, hl1⟩ := hother i (Finset.ne_of_mem_erase hi)
    have hμ : |2 / b₀ * lam i - 1| ≤ 1 := by
      have h0 : 0 ≤ 2 / b₀ * lam i := mul_nonneg (div_nonneg (by norm_num) hb₀.le) hl0
      have h2 : 2 / b₀ * lam i ≤ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hb₀]
        linarith
      rw [abs_le]
      constructor <;> linarith
    have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (r : ℤ) hμ
    have h1 : |(Chebyshev.T ℝ r).eval (2 / b₀ * lam i - 1) * v i x * v i y| ≤
        |v i x * v i y| := by
      rw [mul_assoc, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hT
    linarith [neg_abs_le ((Chebyshev.T ℝ r).eval (2 / b₀ * lam i - 1) * v i x * v i y),
      abs_mul_le_half (v i x) (v i y)]
  have hsum : ∑ i ∈ univ.erase i₀, (v i x ^ 2 + v i y ^ 2) / 2 ≤ 1 := by
    calc ∑ i ∈ univ.erase i₀, (v i x ^ 2 + v i y ^ 2) / 2
        ≤ ∑ i, (v i x ^ 2 + v i y ^ 2) / 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun i _ _ => by positivity)
      _ = 1 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
          simp only [sq, hcomp x x, hcomp y y]
          norm_num
  have h3 := Finset.sum_le_sum hbound
  rw [Finset.sum_neg_distrib] at h3
  have h4 : (Chebyshev.T ℝ r).eval (2 / b₀ * lam i₀ - 1) * v i₀ x * v i₀ y =
      (Chebyshev.T ℝ r).eval (2 * lam i₀ / b₀ - 1) * (v i₀ x * v i₀ y) := by
    rw [mul_assoc, div_mul_eq_mul_div]
  linarith

omit [DecidableEq V] in
/-- The variational step "every other eigenvalue is at most `b₀`": a unit vector `g ⊥ f` with
`fᵀ P g = 0` has Rayleigh quotient at most `b₀`, provided `f` is not orthogonal to `u` and has
Rayleigh quotient at least `b₀`. -/
lemma second_eig_le (P : Matrix V V ℝ) (u f g : V → ℝ) (b₀ θ lam α : ℝ)
    (hgap : ∀ h, h ⬝ᵥ u = 0 → h ⬝ᵥ (P *ᵥ h) ≤ b₀ * (h ⬝ᵥ h))
    (hff : f ⬝ᵥ f = 1) (hgg : g ⬝ᵥ g = 1) (hgf : g ⬝ᵥ f = 0) (hfu : f ⬝ᵥ u = α)
    (hα : 0 < α ^ 2) (hfPf : f ⬝ᵥ (P *ᵥ f) = θ) (hθ : b₀ ≤ θ) (hgPg : g ⬝ᵥ (P *ᵥ g) = lam)
    (hfPg : f ⬝ᵥ (P *ᵥ g) = 0) (hgPf : g ⬝ᵥ (P *ᵥ f) = 0) : lam ≤ b₀ := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = g ⬝ᵥ u := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : V → ℝ, h = β • f - α • g := ⟨_, rfl⟩
  have hhu : h ⬝ᵥ u = 0 := by
    rw [hhdef, sub_dotProduct, smul_dotProduct, smul_dotProduct, hfu, ← hβ, smul_eq_mul,
      smul_eq_mul]
    ring
  have hhPh : h ⬝ᵥ (P *ᵥ h) = β ^ 2 * θ + α ^ 2 * lam := by
    simp only [hhdef, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hfPf, hfPg, hgPf, hgPg]
    ring
  have hhh : h ⬝ᵥ h = β ^ 2 + α ^ 2 := by
    simp only [hhdef, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hff, hgg, hgf, dotProduct_comm f g]
    ring
  have := hgap h hhu
  rw [hhPh, hhh] at this
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hθ), mul_pos hα (sub_pos.mpr hcon)]

/-- The spectral core of Lemma 3.3, for an abstract lazy operator `P`: the compression of `P` to
the complement of `U` has a top eigenvector `f` close to `u`, and Chebyshev polynomials of the
compression have large entries on the support of `f`. -/
lemma spectral_core [Nonempty V] (P : Matrix V V ℝ) (hPs : Pᵀ = P) (u : V → ℝ)
    (hu1 : u ⬝ᵥ u = 1) (hPu : P *ᵥ u = u) (hpsd : ∀ h, 0 ≤ h ⬝ᵥ (P *ᵥ h))
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hgap : ∀ h, h ⬝ᵥ u = 0 → h ⬝ᵥ (P *ᵥ h) ≤ (1 - σ / 2) * (h ⬝ᵥ h))
    (U : Finset V) (hτ : ∑ x ∈ U, u x ^ 2 ≤ σ / 8) :
    ∃ f : V → ℝ, ∃ θ : ℝ, 1 - σ / 4 ≤ θ ∧
      ∑ x, (f x - u x) ^ 2 ≤ 8 * (∑ x ∈ U, u x ^ 2) / σ ∧
      ∀ (r : ℕ) (x y : V),
        (Chebyshev.T ℝ r).eval (2 * θ / (1 - σ / 2) - 1) * (f x * f y) - 1 ≤
          aeval ((2 / (1 - σ / 2)) • maskMat U P - 1) (Chebyshev.T ℝ r) x y := by
  set τ := ∑ x ∈ U, u x ^ 2 with hτdef
  have hτ0 : 0 ≤ τ := Finset.sum_nonneg fun x _ => sq_nonneg _
  set A := maskMat U P with hAdef
  have hPsymm : ∀ g h, g ⬝ᵥ (P *ᵥ h) = h ⬝ᵥ (P *ᵥ g) := by
    intro g h
    rw [dotProduct_mulVec, ← mulVec_transpose, hPs, dotProduct_comm]
  have hAbil : ∀ g h, g ⬝ᵥ (A *ᵥ h) = mask U g ⬝ᵥ (P *ᵥ mask U h) := fun g h =>
    maskMat_bil U P g h
  have hA : A.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    have hji : P j i = P i j := by
      have := congrFun (congrFun hPs i) j
      rwa [Matrix.transpose_apply] at this
    simp only [hAdef, maskMat, Matrix.of_apply, star_trivial, hji]
    ring
  set v : V → V → ℝ := fun i => ⇑(hA.eigenvectorBasis i) with hvdef
  set lam : V → ℝ := hA.eigenvalues with hlamdef
  have hv : ∀ i, A *ᵥ v i = lam i • v i := fun i => hA.mulVec_eigenvectorBasis i
  have hcomp : ∀ x y, ∑ i, v i x * v i y = if x = y then 1 else 0 := by
    intro x y
    have h1 := congrFun (congrFun (Unitary.coe_mul_star_self hA.eigenvectorUnitary) x) y
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h1
  have horth : ∀ i j, v i ⬝ᵥ v j = if i = j then 1 else 0 := by
    intro i j
    have h1 := congrFun (congrFun (Unitary.coe_star_mul_self hA.eigenvectorUnitary) i) j
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, dotProduct] using h1
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max lam
  set θ := lam i₀ with hθdef
  have hAexp : ∀ x y, A x y = ∑ i, lam i * v i x * v i y :=
    entry_eq_sum_of_eigen v hcomp A lam hv
  have hnorm : ∀ g : V → ℝ, g ⬝ᵥ g = ∑ i, (∑ x, v i x * g x) ^ 2 := by
    intro g
    have h1 : ∀ x y, (1 : Matrix V V ℝ) x y = ∑ i, (fun _ => (1 : ℝ)) i * v i x * v i y := by
      intro x y
      simp only [one_mul, hcomp x y, Matrix.one_apply]
    have := quad_of_entry v (fun _ => 1) 1 h1 g
    rw [one_mulVec] at this
    simpa using this
  have hray : ∀ g, g ⬝ᵥ (A *ᵥ g) ≤ θ * (g ⬝ᵥ g) := by
    intro g
    rw [quad_of_entry v lam A hAexp g, hnorm g, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hi₀ i) (sq_nonneg _)
  -- lower bound for the top eigenvalue
  have hsumU : ∀ φ : V → ℝ, ∑ x, (if x ∈ U then φ x else 0) = ∑ x ∈ U, φ x :=
    fun φ => Fintype.sum_ite_mem U φ
  obtain ⟨w, hwdef⟩ : ∃ w : V → ℝ, w = mask U u := ⟨_, rfl⟩
  obtain ⟨wU, hwUdef⟩ : ∃ wU : V → ℝ, wU = fun x => (1 - ind U x) * u x := ⟨_, rfl⟩
  have hw' : w = u - wU := by
    ext x; simp only [hwdef, hwUdef, mask, Pi.sub_apply]; ring
  have hwU_u : wU ⬝ᵥ u = τ := by
    rw [hτdef, ← hsumU]
    simp only [dotProduct, hwUdef, ind]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  have hww : w ⬝ᵥ w = 1 - τ := by
    rw [← hu1, hτdef, ← hsumU]
    simp only [dotProduct, hwdef, mask, ind]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  have hwPw : 1 - 2 * τ ≤ w ⬝ᵥ (P *ᵥ w) := by
    rw [hw', mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hPu, hu1,
      hPsymm u wU, hPu, hwU_u]
    have := hpsd wU
    linarith
  have hθ2 : 1 - 2 * τ ≤ θ := by
    have h1 := hray w
    rw [hAbil, hwdef, mask_mask, ← hwdef, hww] at h1
    have h2 : 1 - 2 * τ ≤ θ * (1 - τ) := le_trans hwPw h1
    nlinarith
  have hθ : 1 - σ / 4 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  -- eigenvectors with nonzero eigenvalue vanish on `U`
  have hsupp : ∀ i, lam i ≠ 0 → mask U (v i) = v i := by
    intro i hi
    ext x
    have hx := congrFun (hv i) x
    rw [hAdef, maskMat_mulVec_apply, Pi.smul_apply, smul_eq_mul] at hx
    by_cases hxU : x ∈ U
    · have hind : ind U x = 0 := by simp [ind, hxU]
      rw [hind, zero_mul] at hx
      simp only [mask, hind, zero_mul]
      rcases mul_eq_zero.mp hx.symm with h | h
      · exact absurd h hi
      · exact h.symm
    · have hind : ind U x = 1 := by simp [ind, hxU]
      simp only [mask, hind, one_mul]
  have hlam : ∀ i, lam i = v i ⬝ᵥ (A *ᵥ v i) := by
    intro i
    rw [hv i, dotProduct_smul, horth i i, ite_eq_left rfl, smul_eq_mul, mul_one]
  have hlam_nonneg : ∀ i, 0 ≤ lam i := by
    intro i
    rw [hlam i, hAbil]
    exact hpsd _
  -- the (sign-normalized) top eigenvector
  obtain ⟨ε, hε1, hεα⟩ : ∃ ε : ℝ, ε * ε = 1 ∧ 0 ≤ ε * (v i₀ ⬝ᵥ u) := by
    by_cases h : 0 ≤ v i₀ ⬝ᵥ u
    · exact ⟨1, by norm_num, by linarith⟩
    · exact ⟨-1, by norm_num, by linarith⟩
  obtain ⟨f, hfdef⟩ : ∃ f : V → ℝ, f = ε • v i₀ := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = f ⬝ᵥ u := ⟨_, rfl⟩
  have hfu : f ⬝ᵥ u = α := hαdef.symm
  have hα0 : 0 ≤ α := by rw [hαdef, hfdef, smul_dotProduct, smul_eq_mul]; exact hεα
  have hff : f ⬝ᵥ f = 1 := by
    rw [hfdef, smul_dotProduct, dotProduct_smul, horth i₀ i₀, ite_eq_left rfl, smul_eq_mul,
      smul_eq_mul, mul_one, hε1]
  have hfmask : mask U f = f := by
    have h0 := hsupp i₀ hθpos.ne'
    rw [hfdef]
    ext x
    have := congrFun h0 x
    simp only [mask, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [mul_left_comm, this]
  have hAf : A *ᵥ f = θ • f := by
    rw [hfdef, mulVec_smul, hv i₀, smul_comm]
  have hfPf : f ⬝ᵥ (P *ᵥ f) = θ := by
    have := hAbil f f
    rw [hfmask, hAf, dotProduct_smul, hff, smul_eq_mul, mul_one] at this
    exact this.symm
  obtain ⟨z, hzdef⟩ : ∃ z : V → ℝ, z = f - α • u := ⟨_, rfl⟩
  have hzu : z ⬝ᵥ u = 0 := by
    rw [hzdef, sub_dotProduct, smul_dotProduct, hu1, hfu, smul_eq_mul]; ring
  have hzz : z ⬝ᵥ z = 1 - α ^ 2 := by
    simp only [hzdef, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hff, hu1, hfu, dotProduct_comm u f]
    ring
  have hPf_u : u ⬝ᵥ (P *ᵥ f) = α := by rw [hPsymm, hPu, hfu]
  have hzPz : z ⬝ᵥ (P *ᵥ z) = θ - α ^ 2 := by
    simp only [hzdef, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hPu, hfPf, hPf_u, hu1, hfu]
    ring
  have hθle : θ - α ^ 2 ≤ (1 - σ / 2) * (1 - α ^ 2) := by
    have := hgap z hzu
    rwa [hzPz, hzz] at this
  have h1α : (1 - α ^ 2) * σ ≤ 4 * τ := by linarith
  have hα2 : 1 / 2 ≤ α ^ 2 := by nlinarith
  have hα1 : α ≤ 1 := by
    have := dot_self_nonneg z
    rw [hzz] at this
    nlinarith
  have hdist : ∑ x, (f x - u x) ^ 2 ≤ 8 * τ / σ := by
    have h1 : ∑ x, (f x - u x) ^ 2 = 2 - 2 * α := by
      have : ∑ x, (f x - u x) ^ 2 = f ⬝ᵥ f - 2 * (f ⬝ᵥ u) + u ⬝ᵥ u := by
        simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this, hff, hfu, hu1]; ring
    rw [h1, le_div_iff₀ hσ0]
    nlinarith [mul_nonneg (mul_nonneg hα0 (by linarith : (0 : ℝ) ≤ 1 - α)) hσ0.le]
  -- all other eigenvalues lie in `[0, 1 - σ/2]`
  have hother : ∀ i, i ≠ i₀ → 0 ≤ lam i ∧ lam i ≤ 1 - σ / 2 := by
    intro i hi
    refine ⟨hlam_nonneg i, ?_⟩
    by_cases hl : lam i ≤ 0
    · linarith
    rw [not_le] at hl
    have hgmask : mask U (v i) = v i := hsupp i hl.ne'
    have hgf : v i ⬝ᵥ f = 0 := by
      rw [hfdef, dotProduct_smul, horth i i₀, ite_eq_right hi, smul_zero]
    have hfPg : f ⬝ᵥ (P *ᵥ v i) = 0 := by
      have := hAbil f (v i)
      rw [hfmask, hgmask, hv i, dotProduct_smul, dotProduct_comm, hgf, smul_zero] at this
      exact this.symm
    have hgPg : v i ⬝ᵥ (P *ᵥ v i) = lam i := by
      have := hAbil (v i) (v i)
      rw [hgmask, ← hlam i] at this
      exact this.symm
    exact second_eig_le P u f (v i) (1 - σ / 2) θ (lam i) α hgap hff
      (by rw [horth i i, ite_eq_left rfl]) hgf hfu (by linarith) hfPf (by linarith) hgPg hfPg
      (by rw [hPsymm]; exact hfPg)
  -- Chebyshev polynomials of the compression
  refine ⟨f, θ, hθ, hdist, fun r x y => ?_⟩
  have hfxy : f x * f y = v i₀ x * v i₀ y := by
    rw [hfdef]
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (v i₀ x * v i₀ y) * hε1
  rw [hfxy]
  exact cheb_entry v hcomp A lam hv i₀ (1 - σ / 2) (by linarith) hother r x y

section Graph

variable (F : WGraph V)

/-- `√d(x)`. -/
noncomputable def sdeg (x : V) : ℝ := Real.sqrt (F.deg x)

/-- The normalized adjacency matrix `N = D^{-1/2} A D^{-1/2}`. -/
noncomputable def normAdj : Matrix V V ℝ :=
  Matrix.of fun x y => F.w x y / (sdeg F x * sdeg F y)

/-- The lazy normalized operator `P = (I + N) / 2`. -/
noncomputable def lazyP : Matrix V V ℝ := (1 / 2 : ℝ) • (1 + normAdj F)

/-- The stationary unit vector `u_x = √(d(x) / vol V)`. -/
noncomputable def statVec : V → ℝ := fun x => sdeg F x / Real.sqrt (F.vol univ)

variable {F}

omit [DecidableEq V] in
lemma sdeg_pos (hd : ∀ x, 0 < F.deg x) (x : V) : 0 < sdeg F x := Real.sqrt_pos.mpr (hd x)

omit [DecidableEq V] in
lemma sdeg_mul_self (hd : ∀ x, 0 < F.deg x) (x : V) : sdeg F x * sdeg F x = F.deg x :=
  Real.mul_self_sqrt (hd x).le

omit [DecidableEq V] in
lemma normAdj_transpose : (normAdj F)ᵀ = normAdj F := by
  ext x y
  simp only [Matrix.transpose_apply, normAdj, Matrix.of_apply, F.symm y x, mul_comm (sdeg F y)]

lemma lazyP_transpose : (lazyP F)ᵀ = lazyP F := by
  rw [lazyP, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one, normAdj_transpose]

omit [DecidableEq V] in
lemma wsum (φ : V → ℝ) (t : ℝ) :
    ∑ x, ∑ y, F.w x y * (φ x + t * φ y) ^ 2 =
      (1 + t ^ 2) * ∑ x, F.deg x * φ x ^ 2 + 2 * t * ∑ x, ∑ y, F.w x y * φ x * φ y := by
  have h1 : ∑ x, ∑ y, F.w x y * φ x ^ 2 = ∑ x, F.deg x * φ x ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [WGraph.deg, Finset.sum_mul]
  have h2 : ∑ x, ∑ y, F.w x y * φ y ^ 2 = ∑ x, F.deg x * φ x ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [WGraph.deg, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [F.symm]
  have h3 : ∑ x, ∑ y, F.w x y * (φ x + t * φ y) ^ 2 =
      ∑ x, ∑ y, F.w x y * φ x ^ 2 + t ^ 2 * ∑ x, ∑ y, F.w x y * φ y ^ 2 +
        2 * t * ∑ x, ∑ y, F.w x y * φ x * φ y := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [h3, h1, h2]
  ring

omit [DecidableEq V] in
lemma normAdj_quad (h : V → ℝ) :
    h ⬝ᵥ (normAdj F *ᵥ h) = ∑ x, ∑ y, F.w x y * (h x / sdeg F x) * (h y / sdeg F y) := by
  simp only [dotProduct, Matrix.mulVec, normAdj, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

omit [DecidableEq V] in
lemma self_quad (hd : ∀ x, 0 < F.deg x) (h : V → ℝ) :
    h ⬝ᵥ h = ∑ x, F.deg x * (h x / sdeg F x) ^ 2 := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := sdeg_pos hd x
  rw [← sdeg_mul_self hd x]
  field_simp

lemma lazyP_quad (h : V → ℝ) :
    h ⬝ᵥ (lazyP F *ᵥ h) = (h ⬝ᵥ h + h ⬝ᵥ (normAdj F *ᵥ h)) / 2 := by
  rw [lazyP, Matrix.smul_mulVec, Matrix.add_mulVec, one_mulVec, dotProduct_smul, dotProduct_add,
    smul_eq_mul]
  ring

lemma lazyP_psd (hd : ∀ x, 0 < F.deg x) (h : V → ℝ) : 0 ≤ h ⬝ᵥ (lazyP F *ᵥ h) := by
  rw [lazyP_quad, self_quad hd, normAdj_quad]
  have h1 := wsum (F := F) (fun x => h x / sdeg F x) 1
  have h2 : 0 ≤ ∑ x, ∑ y, F.w x y * (h x / sdeg F x + 1 * (h y / sdeg F y)) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (F.nonneg x y) (sq_nonneg _)
  linarith

omit [DecidableEq V] in
lemma gap_quad {σ : ℝ} (hgap : F.HasGap σ) (hσ : 0 ≤ σ) (φ : V → ℝ)
    (hφ : ∑ x, F.deg x * φ x = 0) (hdeg0 : 0 ≤ ∑ x, F.deg x) :
    ∑ x, ∑ y, F.w x y * φ x * φ y ≤ (1 - σ) * ∑ x, F.deg x * φ x ^ 2 := by
  obtain ⟨z, hz⟩ := hgap φ
  have hsplit : ∑ x, F.deg x * (φ x - z) ^ 2 =
      ∑ x, F.deg x * φ x ^ 2 - 2 * z * ∑ x, F.deg x * φ x + z ^ 2 * ∑ x, F.deg x := by
    rw [eq_comm]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hdir : F.dirichlet φ = ∑ x, F.deg x * φ x ^ 2 - ∑ x, ∑ y, F.w x y * φ x * φ y := by
    have h1 := wsum (F := F) φ (-1)
    unfold WGraph.dirichlet
    have h2 : ∑ x, ∑ y, F.w x y * (φ x - φ y) ^ 2 =
        ∑ x, ∑ y, F.w x y * (φ x + -1 * φ y) ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [h2, h1]
    ring
  rw [hsplit, hφ, hdir] at hz
  nlinarith [mul_nonneg hσ (mul_nonneg (sq_nonneg z) hdeg0)]

lemma lazyP_gap [Nonempty V] (hd : ∀ x, 0 < F.deg x) {σ : ℝ} (hgap : F.HasGap σ)
    (hσ : 0 ≤ σ) (h : V → ℝ) (hh : h ⬝ᵥ statVec F = 0) :
    h ⬝ᵥ (lazyP F *ᵥ h) ≤ (1 - σ / 2) * (h ⬝ᵥ h) := by
  have hvol : 0 < F.vol univ := Finset.sum_pos (fun x _ => hd x) univ_nonempty
  have hsv : 0 < Real.sqrt (F.vol univ) := Real.sqrt_pos.mpr hvol
  have hdφ : ∑ x, F.deg x * (h x / sdeg F x) = 0 := by
    have : ∑ x, F.deg x * (h x / sdeg F x) = Real.sqrt (F.vol univ) * (h ⬝ᵥ statVec F) := by
      simp only [dotProduct, statVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have := sdeg_pos hd x
      rw [← sdeg_mul_self hd x]
      field_simp
    rw [this, hh, mul_zero]
  have hdeg0 : 0 ≤ ∑ x, F.deg x := Finset.sum_nonneg fun x _ => (hd x).le
  have key := gap_quad hgap hσ (fun x => h x / sdeg F x) hdφ hdeg0
  rw [lazyP_quad, self_quad hd, normAdj_quad]
  have hS : 0 ≤ ∑ x, F.deg x * (h x / sdeg F x) ^ 2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hd x).le (sq_nonneg _)
  linarith

omit [DecidableEq V] in
lemma statVec_norm [Nonempty V] (hd : ∀ x, 0 < F.deg x) : statVec F ⬝ᵥ statVec F = 1 := by
  have hvol : 0 < F.vol univ := Finset.sum_pos (fun x _ => hd x) univ_nonempty
  simp only [dotProduct, statVec]
  have : ∀ x, sdeg F x / Real.sqrt (F.vol univ) * (sdeg F x / Real.sqrt (F.vol univ)) =
      F.deg x / F.vol univ := by
    intro x
    rw [div_mul_div_comm, sdeg_mul_self hd, Real.mul_self_sqrt hvol.le]
  simp only [this, ← Finset.sum_div]
  rw [show ∑ x, F.deg x = F.vol univ from rfl]
  exact div_self hvol.ne'

omit [DecidableEq V] in
lemma normAdj_statVec [Nonempty V] (hd : ∀ x, 0 < F.deg x) :
    normAdj F *ᵥ statVec F = statVec F := by
  have hvol : 0 < F.vol univ := Finset.sum_pos (fun x _ => hd x) univ_nonempty
  have hsv : 0 < Real.sqrt (F.vol univ) := Real.sqrt_pos.mpr hvol
  ext x
  simp only [Matrix.mulVec, dotProduct, normAdj, statVec, Matrix.of_apply]
  have hx := sdeg_pos hd x
  have : ∀ y, F.w x y / (sdeg F x * sdeg F y) * (sdeg F y / Real.sqrt (F.vol univ)) =
      F.w x y / (sdeg F x * Real.sqrt (F.vol univ)) := by
    intro y
    have hy := sdeg_pos hd y
    field_simp
  simp only [this, ← Finset.sum_div]
  rw [show ∑ y, F.w x y = F.deg x from rfl, ← sdeg_mul_self hd x]
  field_simp

lemma lazyP_statVec [Nonempty V] (hd : ∀ x, 0 < F.deg x) :
    lazyP F *ᵥ statVec F = statVec F := by
  rw [lazyP, Matrix.smul_mulVec, Matrix.add_mulVec, one_mulVec, normAdj_statVec hd]
  ext x
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

lemma lazyP_apply_ne {z y : V} (hzy : z ≠ y) :
    lazyP F z y = F.w z y / (sdeg F z * sdeg F y) / 2 := by
  simp only [lazyP, normAdj, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_ne hzy,
    Matrix.of_apply, smul_eq_mul, zero_add]
  ring

end Graph

end DistanceDeletion

/-- **Lemma 3.3 (Distances after deletion).** Let `F` be a weighted graph on `M` vertices with
degrees between `aD` and `bD` and normalized upper gap at least `σ ∈ (0, 1]`. There are
constants `c, C > 0` (depending on `a, b`) such that whenever `|U| ≤ cσM` there is a set
`K ⊆ V(F) \ U` with `|V(F) \ K| ≤ C|U|/σ` such that every two vertices of `K` are joined in
`F - U` by a walk (hence a path) of length at most `C σ^{-1/2} log (2M)`. -/
theorem distances_after_deletion (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (F : WGraph V) (D σ : ℝ),
        0 < D → F.DegBetween (a * D) (b * D) → F.HasGap σ → 0 < σ → σ ≤ 1 →
        ∀ U : Finset V, (U.card : ℝ) ≤ c * σ * Fintype.card V →
          ∃ K : Finset V, Disjoint K U ∧ ((univ \ K).card : ℝ) ≤ C * U.card / σ ∧
            ∀ x ∈ K, ∀ y ∈ K, ∃ p : F.supp.Walk x y, (∀ z ∈ p.support, z ∉ U) ∧
              (p.length : ℝ) ≤ C * σ ^ (-(1 / 2 : ℝ)) * Real.log (2 * Fintype.card V) := by
  open DistanceDeletion in
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = b / a := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by rw [hκdef, le_div_iff₀ ha]; linarith
  have hκ0 : 0 < κ := by linarith
  have hlog4κ : 0 ≤ Real.log (4 * κ) := Real.log_nonneg (by linarith)
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 1 + 32 * κ ^ 2 + (8 + 4 * Real.log (4 * κ)) := ⟨_, rfl⟩
  have hC1 : 1 + 32 * κ ^ 2 ≤ C := by rw [hCdef]; linarith
  have hC2 : 8 + 4 * Real.log (4 * κ) ≤ C := by rw [hCdef]; nlinarith [sq_nonneg κ]
  refine ⟨1 / (8 * κ), C, div_pos one_pos (by linarith), by nlinarith [sq_nonneg κ], ?_⟩
  intro V _ _ F D σ hD hdeg hgap hσ0 hσ1 U hU
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨∅, Finset.disjoint_empty_left _, ?_, ?_⟩
    · have hU0 : U = ∅ := Finset.eq_empty_of_isEmpty U
      simp [hU0]
    · intro x hx
      simp at hx
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Fintype.card V := ⟨_, rfl⟩
  rw [← hM] at hU ⊢
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; exact_mod_cast Fintype.card_pos
  have hM0 : (0 : ℝ) < M := by linarith
  have hκM : 0 < κ * M := mul_pos hκ0 hM0
  have hb : b = κ * a := by rw [hκdef]; field_simp
  have hdpos : ∀ x, 0 < F.deg x := fun x => lt_of_lt_of_le (mul_pos ha hD) (hdeg x).1
  have hvol_lb : (M : ℝ) * (a * D) ≤ F.vol univ := by
    unfold WGraph.vol
    calc (M : ℝ) * (a * D) = ∑ _x : V, a * D := by simp [hM]
      _ ≤ ∑ x, F.deg x := Finset.sum_le_sum fun x _ => (hdeg x).1
  have hvol_ub : F.vol univ ≤ M * (b * D) := by
    unfold WGraph.vol
    calc ∑ x, F.deg x ≤ ∑ _x : V, b * D := Finset.sum_le_sum fun x _ => (hdeg x).2
      _ = (M : ℝ) * (b * D) := by simp [hM]
  have hvol_pos : 0 < F.vol univ := lt_of_lt_of_le (mul_pos hM0 (mul_pos ha hD)) hvol_lb
  have hu_sq : ∀ x, statVec F x ^ 2 = F.deg x / F.vol univ := by
    intro x
    simp only [statVec, div_pow, sdeg, Real.sq_sqrt (hdpos x).le, Real.sq_sqrt hvol_pos.le]
  have hu_pos : ∀ x, 0 < statVec F x := fun x =>
    div_pos (sdeg_pos hdpos x) (Real.sqrt_pos.mpr hvol_pos)
  have hu_lb : ∀ x, 1 / (κ * M) ≤ statVec F x ^ 2 := by
    intro x
    rw [hu_sq, div_le_div_iff₀ hκM hvol_pos]
    calc 1 * F.vol univ ≤ M * (b * D) := by linarith
      _ = (κ * M) * (a * D) := by rw [hb]; ring
      _ ≤ (κ * M) * F.deg x := mul_le_mul_of_nonneg_left (hdeg x).1 hκM.le
      _ = F.deg x * (κ * M) := by ring
  have hτ_le : ∑ x ∈ U, statVec F x ^ 2 ≤ κ * U.card / M := by
    have h1 : ∀ x ∈ U, statVec F x ^ 2 ≤ b * D / F.vol univ := fun x _ => by
      rw [hu_sq]; exact div_le_div_of_nonneg_right (hdeg x).2 hvol_pos.le
    calc ∑ x ∈ U, statVec F x ^ 2 ≤ ∑ _x ∈ U, b * D / F.vol univ := Finset.sum_le_sum h1
      _ = U.card * (b * D) / F.vol univ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ U.card * (b * D) / (M * (a * D)) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) hD.le))
            (mul_pos hM0 (mul_pos ha hD)) hvol_lb
      _ = κ * U.card / M * ((a * D) / (a * D)) := by rw [hb]; ring
      _ = κ * U.card / M := by rw [div_self (mul_pos ha hD).ne', mul_one]
  have hτ : ∑ x ∈ U, statVec F x ^ 2 ≤ σ / 8 := by
    calc ∑ x ∈ U, statVec F x ^ 2 ≤ κ * U.card / M := hτ_le
      _ ≤ κ * (1 / (8 * κ) * σ * M) / M :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hU hκ0.le) hM0.le
      _ = σ / 8 * (κ / κ) * (M / M) := by ring
      _ = σ / 8 := by rw [div_self hκ0.ne', div_self hM0.ne', mul_one, mul_one]
  obtain ⟨f, θ, hθ, hdist, hentry⟩ := spectral_core (lazyP F) lazyP_transpose (statVec F)
    (statVec_norm hdpos) (lazyP_statVec hdpos) (lazyP_psd hdpos) σ hσ0 hσ1
    (fun h hh => lazyP_gap hdpos hgap hσ0.le h hh) U hτ
  refine ⟨univ.filter (fun v => v ∉ U ∧ statVec F v / 2 ≤ f v), ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  · -- the exceptional set is small
    obtain ⟨Bad, hBad⟩ : ∃ Bad : Finset V,
        Bad = univ.filter (fun v => v ∉ U ∧ f v < statVec F v / 2) := ⟨_, rfl⟩
    have hsub : univ \ univ.filter (fun v => v ∉ U ∧ statVec F v / 2 ≤ f v) ⊆ U ∪ Bad := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and, not_and,
        not_le] at hx
      rw [Finset.mem_union]
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr (hBad ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxU, hx hxU⟩)
    have hcard1 : ((univ \ univ.filter (fun v => v ∉ U ∧ statVec F v / 2 ≤ f v)).card : ℝ) ≤
        U.card + Bad.card := by
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le U Bad)
      exact_mod_cast this
    have hbad_each : ∀ x ∈ Bad, 1 / (4 * (κ * M)) ≤ (f x - statVec F x) ^ 2 := by
      intro x hx
      rw [hBad] at hx
      obtain ⟨-, -, hfx⟩ := Finset.mem_filter.mp hx
      have h1 := hu_lb x
      have h2 := hu_pos x
      have h4 : (statVec F x / 2) ^ 2 ≤ (f x - statVec F x) ^ 2 := by
        rw [show (f x - statVec F x) ^ 2 = (statVec F x - f x) ^ 2 by ring]
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      calc 1 / (4 * (κ * M)) = (1 / (κ * M)) / 4 := by ring
        _ ≤ statVec F x ^ 2 / 4 := by linarith
        _ = (statVec F x / 2) ^ 2 := by ring
        _ ≤ _ := h4
    have hbad_sum : (Bad.card : ℝ) * (1 / (4 * (κ * M))) ≤ 8 * (κ * U.card / M) / σ := by
      calc (Bad.card : ℝ) * (1 / (4 * (κ * M))) = ∑ _x ∈ Bad, 1 / (4 * (κ * M)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ Bad, (f x - statVec F x) ^ 2 := Finset.sum_le_sum hbad_each
        _ ≤ ∑ x, (f x - statVec F x) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun _ _ _ => sq_nonneg _
        _ ≤ 8 * (∑ x ∈ U, statVec F x ^ 2) / σ := hdist
        _ ≤ 8 * (κ * U.card / M) / σ := by
            apply div_le_div_of_nonneg_right _ hσ0.le
            linarith [hτ_le]
    have hbad : (Bad.card : ℝ) ≤ 32 * κ ^ 2 * U.card / σ := by
      have hpos : 0 < 4 * (κ * M) := by linarith
      calc (Bad.card : ℝ) = (Bad.card : ℝ) * (1 / (4 * (κ * M))) * (4 * (κ * M)) := by
            rw [mul_assoc, one_div, inv_mul_cancel₀ hpos.ne', mul_one]
        _ ≤ 8 * (κ * U.card / M) / σ * (4 * (κ * M)) :=
            mul_le_mul_of_nonneg_right hbad_sum hpos.le
        _ = 32 * κ ^ 2 * U.card / σ * (M / M) := by ring
        _ = 32 * κ ^ 2 * U.card / σ := by rw [div_self hM0.ne', mul_one]
    have hUσ : (U.card : ℝ) ≤ U.card / σ := by
      rw [le_div_iff₀ hσ0]
      nlinarith [(Nat.cast_nonneg U.card : (0 : ℝ) ≤ U.card)]
    calc _ ≤ (U.card : ℝ) + Bad.card := hcard1
      _ ≤ U.card / σ + 32 * κ ^ 2 * U.card / σ := by linarith
      _ = (1 + 32 * κ ^ 2) * (U.card / σ) := by ring
      _ ≤ C * (U.card / σ) :=
          mul_le_mul_of_nonneg_right hC1 (div_nonneg (Nat.cast_nonneg _) hσ0.le)
      _ = C * U.card / σ := by ring
  · -- short walks between vertices of `K`
    intro x hx y hy
    obtain ⟨-, hxU, hfx⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hyU, hfy⟩ := Finset.mem_filter.mp hy
    have hb₀ : 0 < 1 - σ / 2 := by linarith
    have hx₀ : 1 + σ / 2 ≤ 2 * θ / (1 - σ / 2) - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hb₀]
      nlinarith
    have hsq0 : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ0
    have hsq1 : Real.sqrt σ ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hσ1
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (2 * M) := ⟨_, rfl⟩
    rw [← hLdef]
    have hL : 1 / 2 ≤ L := by
      have : Real.log 2 ≤ L := by
        rw [hLdef]
        exact Real.log_le_log (by norm_num) (by linarith)
      linarith [Real.log_two_gt_d9]
    have hlog8 : Real.log (8 * κ * M) = Real.log (4 * κ) + L := by
      rw [hLdef, show 8 * κ * M = (4 * κ) * (2 * M) by ring,
        Real.log_mul (by linarith) (by linarith)]
    have hA0 : 0 ≤ 2 * (Real.log (8 * κ * M) + 1) / Real.sqrt σ := by
      rw [hlog8]
      exact div_nonneg (by linarith) hsq0.le
    obtain ⟨r, hr⟩ : ∃ r : ℕ, r = ⌈2 * (Real.log (8 * κ * M) + 1) / Real.sqrt σ⌉₊ :=
      ⟨_, rfl⟩
    have hr_ge : 2 * (Real.log (8 * κ * M) + 1) / Real.sqrt σ ≤ r := hr ▸ Nat.le_ceil _
    have hr_lt : (r : ℝ) < 2 * (Real.log (8 * κ * M) + 1) / Real.sqrt σ + 1 :=
      hr ▸ Nat.ceil_lt_add_one hA0
    have hrs : Real.log (8 * κ * M) + 1 ≤ r * Real.sqrt σ / 2 := by
      rw [div_le_iff₀ hsq0] at hr_ge
      linarith
    have hexp : 8 * κ * M < Real.exp (r * Real.sqrt σ / 2) := by
      have h8 : 0 < 8 * κ * M := by linarith
      calc 8 * κ * M = Real.exp (Real.log (8 * κ * M)) := (Real.exp_log h8).symm
        _ < Real.exp (r * Real.sqrt σ / 2) := Real.exp_lt_exp.mpr (by linarith)
    have hT := cheb_growth σ hσ0 hσ1 _ hx₀ r
    have hfxy : 1 / (4 * (κ * M)) ≤ f x * f y := by
      have hux := hu_pos x
      have huy := hu_pos y
      have h1 : statVec F x / 2 * (statVec F y / 2) ≤ f x * f y :=
        mul_le_mul hfx hfy (by linarith) (by linarith)
      have h2 : 1 / (κ * M) ≤ statVec F x * statVec F y := by
        have h3 : (1 / (κ * M)) ^ 2 ≤ (statVec F x * statVec F y) ^ 2 := by
          rw [mul_pow, sq]
          exact mul_le_mul (hu_lb x) (hu_lb y) (by positivity) (by positivity)
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h3
      calc 1 / (4 * (κ * M)) = (1 / (κ * M)) / 4 := by ring
        _ ≤ statVec F x * statVec F y / 4 := by linarith
        _ = statVec F x / 2 * (statVec F y / 2) := by ring
        _ ≤ f x * f y := h1
    have hTge : 4 * (κ * M) < (Polynomial.Chebyshev.T ℝ r).eval (2 * θ / (1 - σ / 2) - 1) := by
      linarith
    have hpos : 1 < (Polynomial.Chebyshev.T ℝ r).eval (2 * θ / (1 - σ / 2) - 1) * (f x * f y) := by
      calc (1 : ℝ) = 4 * (κ * M) * (1 / (4 * (κ * M))) :=
            (mul_one_div_cancel (by linarith)).symm
        _ < (Polynomial.Chebyshev.T ℝ r).eval (2 * θ / (1 - σ / 2) - 1) * (f x * f y) :=
            mul_lt_mul hTge hfxy (by positivity) (by linarith)
    have hne : Polynomial.aeval ((2 / (1 - σ / 2)) • maskMat U (lazyP F) - 1) (Polynomial.Chebyshev.T ℝ r) x y ≠ 0 :=
      (lt_of_lt_of_le (by linarith) (hentry r x y)).ne'
    have hB : ∀ z w, ((2 / (1 - σ / 2)) • maskMat U (lazyP F) - 1) z w ≠ 0 →
        z = w ∨ (w ∉ U ∧ F.supp.Adj z w) := by
      intro z w hzw
      by_cases h : z = w
      · exact Or.inl h
      · right
        rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero, Matrix.smul_apply,
          smul_eq_mul] at hzw
        simp only [maskMat, Matrix.of_apply] at hzw
        have hwU : w ∉ U := by
          intro hw
          apply hzw
          simp [ind, hw]
        refine ⟨hwU, ?_⟩
        have hP : lazyP F z w ≠ 0 := fun h0 => hzw (by rw [h0]; ring)
        rw [lazyP_apply_ne h] at hP
        have hw : F.w z w ≠ 0 := fun h0 => hP (by rw [h0]; simp)
        exact lt_of_le_of_ne (F.nonneg z w) (Ne.symm hw)
    obtain ⟨p, hp, hlen⟩ := walk_of_aeval_ne_zero F.supp U _ hB (Polynomial.Chebyshev.T ℝ r) x y hxU hne
    refine ⟨p, hp, ?_⟩
    rw [Polynomial.Chebyshev.natDegree_T] at hlen
    have hlenR : (p.length : ℝ) ≤ r := by exact_mod_cast hlen
    rw [Real.rpow_neg hσ0.le, ← Real.sqrt_eq_rpow]
    have hnum : 2 * Real.log (4 * κ) + 2 * L + 3 ≤ C * L := by
      nlinarith [mul_nonneg hlog4κ (by linarith : (0 : ℝ) ≤ L - 1 / 2),
        mul_le_mul_of_nonneg_right hC2 (by linarith : (0 : ℝ) ≤ L)]
    have hr_le : (r : ℝ) ≤ (2 * Real.log (4 * κ) + 2 * L + 3) / Real.sqrt σ := by
      have h1 : 1 ≤ 1 / Real.sqrt σ := by rw [le_div_iff₀ hsq0]; linarith
      have h2 : (2 * Real.log (4 * κ) + 2 * L + 3) / Real.sqrt σ =
          2 * (Real.log (8 * κ * M) + 1) / Real.sqrt σ + 1 / Real.sqrt σ := by
        rw [hlog8]; ring
      rw [h2]
      linarith
    calc (p.length : ℝ) ≤ r := hlenR
      _ ≤ (2 * Real.log (4 * κ) + 2 * L + 3) / Real.sqrt σ := hr_le
      _ ≤ C * L / Real.sqrt σ := div_le_div_of_nonneg_right hnum hsq0.le
      _ = C * (Real.sqrt σ)⁻¹ * L := by ring

end Lovasz
