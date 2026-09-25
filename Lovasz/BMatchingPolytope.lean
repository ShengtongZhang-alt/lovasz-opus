/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# The unit-capacitated perfect b-matching polytope (classical input)

DAG node `K.bmatch` of `docs/BLUEPRINT.md`; Edmonds' theorem as stated in Section 4.1 of the
paper (Letchford–Reinelt–Theis, Section 1; Schrijver, *Combinatorial Optimization*, Cor. 33.2a).

## Proof

1. *Core theorem* (`BMatch.thmA`). For a loopless multigraph (edge set `F`, ends `u e, v e`) with
   demands `b` such that every edge has an end of demand `1`, every `x ≥ 0` supported on `F`
   with the degree equations and the odd-set inequalities `x(δ(U)) ≥ 1` (`b(U)` odd) is a convex
   combination of integral perfect `b`-matchings. Strong induction on `|F| + b(V)`:
   an edge with `x_e = 0` is deleted; a nontrivial tight odd set (`b(U), b(Uᶜ) ≥ 2`) is
   contracted on both sides and the two decompositions are glued along `δ(U)`; an edge with
   `x_e = 1` is removed together with one unit of demand at both ends; otherwise a nonzero
   direction `d` with `d(δ(v)) = 0` exists (dimension count, or a direct construction when the
   support is `2`-regular), and `x` is a convex combination of the two points where the line
   `x + t d` leaves the polytope, each of which has a zero coordinate or a nontrivial tight set.
2. *Reduction* (`bmatching_polytope`). Subdivide every edge `e = uv` into the path
   `u — (e,false) — (e,true) — v` with demand `1` at the new vertices and values
   `y_e, 1 - y_e, y_e`; the blossom inequalities for `y` give the odd-set inequalities of the
   subdivided point, and projecting onto the first edge of each path gives the result.
-/

namespace Lovasz

open Finset

namespace BMatch

open Classical
open scoped Pointwise

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Weighted degree of `w` in the multigraph with edge set `F` and ends `u e, v e`. -/
noncomputable def dsum (u v : E → V) (F : Finset E) (x : E → ℝ) (w : V) : ℝ :=
  ∑ e ∈ F.filter (fun e => u e = w ∨ v e = w), x e

/-- The edges of `F` crossing `U`. -/
noncomputable def cut (u v : E → V) (F : Finset E) (U : Finset V) : Finset E :=
  F.filter (fun e => (u e ∈ U) ≠ (v e ∈ U))

/-- The edges of `F` inside `U`. -/
noncomputable def inside (u v : E → V) (F : Finset E) (U : Finset V) : Finset E :=
  F.filter (fun e => u e ∈ U ∧ v e ∈ U)

/-- The fractional perfect `b`-matching polytope with odd-set constraints. -/
def PS (u v : E → V) (F : Finset E) (b : V → ℕ) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ e ∉ F, x e = 0) ∧ (∀ w, dsum u v F x w = b w) ∧
    ∀ U : Finset V, Odd (∑ z ∈ U, b z) → 1 ≤ ∑ e ∈ cut u v F U, x e}

/-- Integral perfect `b`-matchings supported on `F`. -/
def IS (u v : E → V) (F : Finset E) (b : V → ℕ) : Set (E → ℝ) :=
  {z | (∀ e, z e = 0 ∨ z e = 1) ∧ (∀ e ∉ F, z e = 0) ∧ ∀ w, dsum u v F z w = b w}

/-- Loopless, and every edge has an end of demand `1`. -/
def Good (u v : E → V) (F : Finset E) (b : V → ℕ) : Prop :=
  (∀ e ∈ F, u e ≠ v e) ∧ ∀ e ∈ F, b (u e) = 1 ∨ b (v e) = 1

omit [Fintype V] [Fintype E] in
lemma dsum_add (u v : E → V) (F : Finset E) (x d : E → ℝ) (t : ℝ) (w : V) :
    dsum u v F (x + t • d) w = dsum u v F x w + t * dsum u v F d w := by
  simp [dsum, Finset.sum_add_distrib, Finset.mul_sum]

omit [Fintype V] [Fintype E] in
lemma dsum_neg (u v : E → V) (F : Finset E) (d : E → ℝ) (w : V) :
    dsum u v F (-d) w = - dsum u v F d w := by
  simp [dsum]

omit [Fintype V] [Fintype E] in
lemma dsum_sub {u v : E → V} {F : Finset E} (d d' : E → ℝ) (w : V) :
    dsum u v F (fun f => d f - d' f) w = dsum u v F d w - dsum u v F d' w := by
  simp [dsum, Finset.sum_sub_distrib]

omit [Fintype E] in
/-- Double counting. -/
lemma sum_mul_dsum (u v : E → V) (F : Finset E) (hl : ∀ e ∈ F, u e ≠ v e) (φ : V → ℝ)
    (d : E → ℝ) : ∑ z, φ z * dsum u v F d z = ∑ e ∈ F, d e * (φ (u e) + φ (v e)) := by
  simp only [dsum, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have hne := hl e he
  have : ∀ z, φ z * (if u e = z ∨ v e = z then d e else 0) =
      (if u e = z then d e * φ (u e) else 0) + (if v e = z then d e * φ (v e) else 0) := by
    intro z
    by_cases h1 : u e = z <;> by_cases h2 : v e = z
    · exact absurd (h1.trans h2.symm) hne
    · simp [h1, h2, mul_comm]
    · simp [h1, h2, mul_comm]
    · simp [h1, h2]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

omit [Fintype E] in
lemma handshake (u v : E → V) (F : Finset E) (hl : ∀ e ∈ F, u e ≠ v e) (U : Finset V)
    (d : E → ℝ) :
    ∑ z ∈ U, dsum u v F d z = ∑ e ∈ cut u v F U, d e + 2 * ∑ e ∈ inside u v F U, d e := by
  have h := sum_mul_dsum u v F hl (fun z => if z ∈ U then 1 else 0) d
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] at h
  rw [h, cut, inside, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : u e ∈ U <;> by_cases h2 : v e ∈ U <;> simp [h1, h2]
  all_goals ring

omit [Fintype E] in
lemma cut_compl (u v : E → V) (F : Finset E) (U : Finset V) :
    cut u v F Uᶜ = cut u v F U := by
  unfold cut
  refine Finset.filter_congr fun e _ => ?_
  simp only [Finset.mem_compl, ne_eq, eq_iff_iff, not_iff_not]

omit [Fintype E] in
lemma even_total {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ}
    (hx : x ∈ PS u v F b) : Even (∑ z, b z) := by
  by_contra h
  have h1 := hx.2.2.2 univ (Nat.not_even_iff_odd.mp h)
  have : cut u v F univ = ∅ := by
    unfold cut
    simp
  rw [this, Finset.sum_empty] at h1
  linarith

omit [Fintype E] in
lemma odd_compl {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ}
    (hx : x ∈ PS u v F b) {U : Finset V} (hU : Odd (∑ z ∈ U, b z)) :
    Odd (∑ z ∈ Uᶜ, b z) := by
  have h1 := even_total hx
  have h2 := Finset.sum_add_sum_compl U b
  rw [Nat.odd_iff] at hU ⊢
  rw [Nat.even_iff] at h1
  omega

omit [Fintype E] in
lemma exists_kernel (u v : E → V) (F : Finset E) (S : Finset V) (hS : S.card < F.card) :
    ∃ d : E → ℝ, d ≠ 0 ∧ (∀ e ∉ F, d e = 0) ∧ ∀ z ∈ S, dsum u v F d z = 0 := by
  let col : F → (S → ℝ) := fun e z => if u e.1 = z.1 ∨ v e.1 = z.1 then 1 else 0
  have hli : ¬ LinearIndependent ℝ col := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at this
    simp only [Fintype.card_coe] at this
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hli
  refine ⟨fun e => if h : e ∈ F then g ⟨e, h⟩ else 0, ?_, ?_, ?_⟩
  · intro h0
    apply hi
    have := congrFun h0 i.1
    simpa using this
  · intro e he
    simp [he]
  · intro z hz
    have h1 := congrFun hg ⟨z, hz⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, Pi.zero_apply] at h1
    have h2 : dsum u v F (fun e => if h : e ∈ F then g ⟨e, h⟩ else 0) z =
        ∑ x : F, g x * (if u x.1 = z ∨ v x.1 = z then 1 else 0) := by
      rw [dsum, Finset.sum_filter, ← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [e.2]
    rw [h2, h1]

omit [Fintype V] [Fintype E] in
lemma le_dsum {u v : E → V} {F : Finset E} {x : E → ℝ} (hx0 : ∀ e, 0 ≤ x e) {e : E}
    (he : e ∈ F) {w : V} (hw : u e = w ∨ v e = w) : x e ≤ dsum u v F x w :=
  Finset.single_le_sum (fun f _ => hx0 f) (Finset.mem_filter.mpr ⟨he, hw⟩)

omit [Fintype V] [Fintype E] in
lemma one_le_b {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ} (hx : x ∈ PS u v F b)
    (hpos : ∀ e ∈ F, 0 < x e) {e : E} (he : e ∈ F) {w : V} (hw : u e = w ∨ v e = w) :
    1 ≤ b w := by
  have h1 := le_dsum hx.1 he hw
  rw [hx.2.2.1 w] at h1
  have := hpos e he
  have h2 : (0:ℝ) < b w := by linarith
  have : 0 < b w := by exact_mod_cast h2
  omega

omit [Fintype V] in
lemma add_le_sum_b (b : V → ℕ) {U : Finset V} {p q : V} (hp : p ∈ U) (hq : q ∈ U)
    (hpq : p ≠ q) : b p + b q ≤ ∑ z ∈ U, b z := by
  have hsub : ({p, q} : Finset V) ⊆ U := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset (f := b) hsub
  rwa [Finset.sum_pair hpq] at this

omit [Fintype E] in
lemma rate_zero {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ} (hG : Good u v F b)
    (hx : x ∈ PS u v F b) (hpos : ∀ e ∈ F, 0 < x e) {d : E → ℝ}
    (hdD : ∀ w, dsum u v F d w = 0) {U : Finset V}
    (htriv : ∑ z ∈ U, b z < 2 ∨ ∑ z ∈ Uᶜ, b z < 2) : ∑ e ∈ cut u v F U, d e = 0 := by
  have key : ∀ W : Finset V, ∑ z ∈ W, b z < 2 → ∑ e ∈ cut u v F W, d e = 0 := by
    intro W hW
    have h := handshake u v F hG.1 W d
    have hin : inside u v F W = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [inside, Finset.mem_filter] at he
      have h1 := one_le_b hx hpos he.1 (Or.inl rfl)
      have h2 := one_le_b hx hpos he.1 (Or.inr rfl)
      have := add_le_sum_b b he.2.1 he.2.2 (hG.1 e he.1)
      omega
    simp only [hdD, Finset.sum_const_zero, hin, Finset.sum_empty, mul_zero, add_zero] at h
    exact h.symm
  rcases htriv with h | h
  · exact key U h
  · rw [← cut_compl]; exact key Uᶜ h

lemma line {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ} (hx : x ∈ PS u v F b)
    (hpos : ∀ e ∈ F, 0 < x e) {d : E → ℝ} (hdF : ∀ e ∉ F, d e = 0)
    (hdD : ∀ w, dsum u v F d w = 0) (hneg : ∃ e, d e < 0)
    (htr : ∀ U : Finset V, Odd (∑ z ∈ U, b z) → ∑ e ∈ cut u v F U, x e = 1 →
      ∑ e ∈ cut u v F U, d e = 0) :
    ∃ t : ℝ, 0 < t ∧ x + t • d ∈ PS u v F b ∧ ((∃ e ∈ F, x e + t * d e = 0) ∨
      ∃ U : Finset V, Odd (∑ z ∈ U, b z) ∧ ∑ e ∈ cut u v F U, (x e + t * d e) = 1 ∧
        ∑ e ∈ cut u v F U, d e < 0) := by
  set A := univ.filter (fun e => d e < 0) with hA
  set B := (univ : Finset (Finset V)).filter
    (fun U => Odd (∑ z ∈ U, b z) ∧ ∑ e ∈ cut u v F U, d e < 0) with hB
  let rA : E → ℝ := fun e => x e / (-d e)
  let rB : Finset V → ℝ := fun U =>
    (∑ e ∈ cut u v F U, x e - 1) / (-(∑ e ∈ cut u v F U, d e))
  set R := A.image rA ∪ B.image rB with hR
  obtain ⟨e0, he0⟩ := hneg
  have hRne : R.Nonempty :=
    ⟨rA e0, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [hA, he0]))⟩
  set t := R.min' hRne with ht
  have hAF : ∀ e ∈ A, e ∈ F := by
    intro e he
    by_contra h
    simp [hA, hdF e h] at he
  have hrA : ∀ e ∈ A, 0 < rA e := by
    intro e he
    have := (Finset.mem_filter.mp he).2
    exact div_pos (hpos e (hAF e he)) (by linarith)
  have hBslack : ∀ U ∈ B, 1 < ∑ e ∈ cut u v F U, x e := by
    intro U hU
    obtain ⟨hU1, hU2⟩ := (Finset.mem_filter.mp hU).2
    have h1 := hx.2.2.2 U hU1
    rcases h1.lt_or_eq with h | h
    · exact h
    · have := htr U hU1 h.symm; linarith
  have hrB : ∀ U ∈ B, 0 < rB U := by
    intro U hU
    have := (Finset.mem_filter.mp hU).2.2
    exact div_pos (by linarith [hBslack U hU]) (by linarith)
  have htA : ∀ e ∈ A, t ≤ rA e := fun e he =>
    Finset.min'_le _ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he))
  have htB : ∀ U ∈ B, t ≤ rB U := fun U hU =>
    Finset.min'_le _ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hU))
  have htR : t ∈ R := Finset.min'_mem _ _
  have htpos : 0 < t := by
    rcases Finset.mem_union.mp htR with h | h
    · obtain ⟨e, he, hre⟩ := Finset.mem_image.mp h
      rw [← hre]; exact hrA e he
    · obtain ⟨U, hU, hrU⟩ := Finset.mem_image.mp h
      rw [← hrU]; exact hrB U hU
  refine ⟨t, htpos, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hde : d e < 0
    · have he : e ∈ A := by simp [hA, hde]
      have := htA e he
      have h2 : t * (-d e) ≤ x e := (le_div_iff₀ (by linarith)).mp this
      linarith
    · replace hde := not_lt.mp hde
      have := hx.1 e
      have : 0 ≤ t * d e := mul_nonneg htpos.le hde
      linarith
  · intro e he
    simp [hx.2.1 e he, hdF e he]
  · intro w
    rw [dsum_add, hx.2.2.1 w, hdD w, mul_zero, add_zero]
  · intro U hU
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    by_cases hdU : ∑ e ∈ cut u v F U, d e < 0
    · have hUB : U ∈ B := by simp [hB, hU, hdU]
      have := htB U hUB
      have h2 : t * (-(∑ e ∈ cut u v F U, d e)) ≤ ∑ e ∈ cut u v F U, x e - 1 :=
        (le_div_iff₀ (by linarith)).mp this
      linarith
    · replace hdU := not_lt.mp hdU
      have := hx.2.2.2 U hU
      have : 0 ≤ t * ∑ e ∈ cut u v F U, d e := mul_nonneg htpos.le hdU
      linarith
  · rcases Finset.mem_union.mp htR with h | h
    · obtain ⟨e, he, hre⟩ := Finset.mem_image.mp h
      left
      refine ⟨e, hAF e he, ?_⟩
      have hde := (Finset.mem_filter.mp he).2
      rw [← hre]
      simp only [rA]
      have : d e ≠ 0 := hde.ne
      field_simp
      ring
    · obtain ⟨U, hU, hrU⟩ := Finset.mem_image.mp h
      right
      obtain ⟨hU1, hU2⟩ := (Finset.mem_filter.mp hU).2
      refine ⟨U, hU1, ?_, hU2⟩
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hrU]
      simp only [rB]
      have : (∑ e ∈ cut u v F U, d e) ≠ 0 := hU2.ne
      field_simp
      ring

/-- The induction hypothesis: the statement for all instances of smaller size. -/
def IHP (F : Finset E) (b : V → ℕ) : Prop :=
  ∀ (u' v' : E → V) (F' : Finset E) (b' : V → ℕ), F'.card + ∑ z, b' z < F.card + ∑ z, b z →
    Good u' v' F' b' → PS u' v' F' b' ⊆ convexHull ℝ (IS u' v' F' b')

omit [Fintype V] [Fintype E] in
lemma dsum_congr {u v : E → V} {F : Finset E} {y y' : E → ℝ} (h : ∀ f ∈ F, y f = y' f)
    (w : V) : dsum u v F y w = dsum u v F y' w :=
  Finset.sum_congr rfl fun f hf => h f (Finset.mem_filter.mp hf).1

omit [Fintype V] [Fintype E] in
lemma dsum_split {u v : E → V} {F : Finset E} {e : E} (he : e ∈ F) (y : E → ℝ) (z : V) :
    dsum u v F y z = dsum u v (F.erase e) y z + (if u e = z ∨ v e = z then y e else 0) := by
  unfold dsum
  rw [Finset.filter_erase]
  by_cases h : u e = z ∨ v e = z
  · simp only [h, ite_true]
    rw [Finset.sum_erase_add _ _ (Finset.mem_filter.mpr ⟨he, h⟩)]
  · simp only [h, ite_false]
    rw [Finset.erase_eq_of_notMem (by simp [h]), add_zero]

omit [Fintype V] [Fintype E] in
lemma dsum_erase {u v : E → V} {F : Finset E} {y : E → ℝ} {e : E} (hy : y e = 0) (w : V) :
    dsum u v (F.erase e) y w = dsum u v F y w := by
  unfold dsum
  rw [Finset.filter_erase, Finset.sum_erase _ hy]

omit [Fintype V] [Fintype E] in
lemma le_dsum_two {u v : E → V} {F : Finset E} {x : E → ℝ} (hx0 : ∀ e, 0 ≤ x e) {e f : E}
    (hef : e ≠ f) (he : e ∈ F) (hf : f ∈ F) {w : V} (hwe : u e = w ∨ v e = w)
    (hwf : u f = w ∨ v f = w) : x e + x f ≤ dsum u v F x w := by
  have hsub : ({e, f} : Finset E) ⊆ F.filter (fun e => u e = w ∨ v e = w) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨he, hwe⟩
    · exact Finset.mem_filter.mpr ⟨hf, hwf⟩
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hx0 g)
  rwa [Finset.sum_pair hef] at this

omit [Fintype E] in
lemma step_zero {u v : E → V} {F : Finset E} {b : V → ℕ} (hIH : IHP F b) (hG : Good u v F b)
    {x : E → ℝ} (hx : x ∈ PS u v F b) {e : E} (he : e ∈ F) (hxe : x e = 0) :
    x ∈ convexHull ℝ (IS u v F b) := by
  have hmeas : (F.erase e).card + ∑ z, b z < F.card + ∑ z, b z := by
    rw [Finset.card_erase_of_mem he]
    have := Finset.card_pos.mpr ⟨e, he⟩
    omega
  have hG' : Good u v (F.erase e) b :=
    ⟨fun f hf => hG.1 f (Finset.mem_of_mem_erase hf),
      fun f hf => hG.2 f (Finset.mem_of_mem_erase hf)⟩
  have hx' : x ∈ PS u v (F.erase e) b := by
    refine ⟨hx.1, fun f hf => ?_, fun w => ?_, fun U hU => ?_⟩
    · by_cases hfe : f = e
      · rw [hfe]; exact hxe
      · exact hx.2.1 f (fun h => hf (Finset.mem_erase.mpr ⟨hfe, h⟩))
    · rw [dsum_erase hxe]; exact hx.2.2.1 w
    · rw [cut, Finset.filter_erase, Finset.sum_erase _ hxe]; exact hx.2.2.2 U hU
  refine convexHull_mono ?_ (hIH u v (F.erase e) b hmeas hG' hx')
  intro z hz
  refine ⟨hz.1, fun f hf => hz.2.1 f (fun h => hf (Finset.mem_of_mem_erase h)), fun w => ?_⟩
  have hze : z e = 0 := hz.2.1 e (Finset.notMem_erase e F)
  rw [← dsum_erase hze]; exact hz.2.2 w

omit [Fintype E] in
lemma step_one_core {u v : E → V} {F : Finset E} {b : V → ℕ} (hIH : IHP F b)
    (hG : Good u v F b) {x : E → ℝ} (hx : x ∈ PS u v F b) (hpos : ∀ f ∈ F, 0 < x f) {e : E}
    (he : e ∈ F) (hxe : x e = 1) {w s : V} (hws : w ≠ s)
    (hends : ∀ z, (u e = z ∨ v e = z) ↔ (z = w ∨ z = s)) (hbs : b s = 1) :
    x ∈ convexHull ℝ (IS u v F b) := by
  have hes : u e = s ∨ v e = s := (hends s).mpr (Or.inr rfl)
  have hew : u e = w ∨ v e = w := (hends w).mpr (Or.inl rfl)
  have hs_only : ∀ f ∈ F, f ≠ e → ¬(u f = s ∨ v f = s) := by
    intro f hf hfe hfs
    have h1 := le_dsum_two hx.1 (Ne.symm hfe) he hf hes hfs
    rw [hx.2.2.1 s, hbs, hxe] at h1
    have := hpos f hf
    push_cast at h1
    linarith
  have hbw : 1 ≤ b w := one_le_b hx hpos he hew
  set b' : V → ℕ := fun z => if z = s then 0 else if z = w then b w - 1 else b z with hb'def
  have hb' : ∀ z, b' z + (if z = w then 1 else 0) + (if z = s then 1 else 0) = b z := by
    intro z
    by_cases h1 : z = s
    · subst h1; simp [hb'def, Ne.symm hws, hbs]
    · by_cases h2 : z = w
      · subst h2; simp [hb'def, h1]; omega
      · simp [hb'def, h1, h2]
  have hb'R : ∀ z, (b' z : ℝ) + (if u e = z ∨ v e = z then 1 else 0) = b z := by
    intro z
    have h := hb' z
    by_cases hz : u e = z ∨ v e = z
    · simp only [hz, ite_true]
      rcases (hends z).mp hz with h1 | h1
      · subst h1
        simp [hws] at h
        rw [← h]; push_cast; ring
      · subst h1
        simp [Ne.symm hws] at h
        rw [← h]; push_cast; ring
    · simp only [hz, ite_false]
      have h1 : z ≠ w := fun h' => hz ((hends z).mpr (Or.inl h'))
      have h2 : z ≠ s := fun h' => hz ((hends z).mpr (Or.inr h'))
      simp only [h1, h2, ite_false, add_zero] at h
      rw [← h, add_zero]
  set x' : E → ℝ := fun f => if f = e then 0 else x f with hx'def
  have hx'e : ∀ f ∈ F.erase e, x' f = x f := by
    intro f hf
    simp [hx'def, Finset.ne_of_mem_erase hf]
  -- membership transfer for odd sets
  have hodd : ∀ W : Finset V, Odd (∑ z ∈ W, b' z) →
      1 ≤ ∑ f ∈ cut u v (F.erase e) W, x' f := by
    intro W hW
    set W' : Finset V := if w ∈ W then insert s W else W.erase s with hW'def
    have hmem : ∀ z, z ≠ s → (z ∈ W' ↔ z ∈ W) := by
      intro z hz
      by_cases hw : w ∈ W <;> simp [hW'def, hw, hz]
    have hsmem : s ∈ W' ↔ w ∈ W := by
      by_cases hw : w ∈ W <;> simp [hW'def, hw]
    have hsumW : ∑ z ∈ W, b z = ∑ z ∈ W, b' z + (if w ∈ W then 1 else 0) +
        (if s ∈ W then 1 else 0) := by
      rw [← Finset.sum_congr rfl (fun z _ => hb' z), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    have hpar : Odd (∑ z ∈ W', b z) := by
      rw [Nat.odd_iff] at hW ⊢
      by_cases hw : w ∈ W <;> by_cases hs : s ∈ W
      · have : W' = W := by simp [hW'def, hw, hs]
        rw [this, hsumW]; simp [hw, hs]; omega
      · have : W' = insert s W := by simp [hW'def, hw]
        rw [this, Finset.sum_insert hs, hsumW, hbs]; simp [hw, hs]; omega
      · have : W' = W.erase s := by simp [hW'def, hw]
        have h2 := Finset.sum_erase_add W b hs
        rw [this]; rw [hsumW, hbs] at *; simp [hw, hs] at h2 ⊢; omega
      · have : W' = W := by simp [hW'def, hw, Finset.erase_eq_of_notMem hs]
        rw [this, hsumW]; simp [hw, hs]; omega
    have hcut : cut u v (F.erase e) W = cut u v F W' := by
      ext f
      simp only [cut, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hfe, hf⟩, hne⟩
        have h1 := hs_only f hf hfe
        push Not at h1
        refine ⟨hf, ?_⟩
        rwa [hmem _ h1.1, hmem _ h1.2]
      · rintro ⟨hf, hne⟩
        by_cases hfe : f = e
        · exfalso
          subst hfe
          apply hne
          have key : ∀ z, (u f = z ∨ v f = z) → (z ∈ W' ↔ w ∈ W) := by
            intro z hz
            rcases (hends z).mp hz with rfl | rfl
            · exact hmem _ hws
            · exact hsmem
          rw [eq_iff_iff, key _ (Or.inl rfl), key _ (Or.inr rfl)]
        · have h1 := hs_only f hf hfe
          push Not at h1
          refine ⟨⟨hfe, hf⟩, ?_⟩
          rwa [← hmem _ h1.1, ← hmem _ h1.2]
    have h1 := hx.2.2.2 W' hpar
    rw [← hcut] at h1
    have h2 : ∑ f ∈ cut u v (F.erase e) W, x' f = ∑ f ∈ cut u v (F.erase e) W, x f :=
      Finset.sum_congr rfl (fun f hf => hx'e f (by simp only [cut, Finset.mem_filter] at hf; exact hf.1))
    rw [h2]; exact h1
  have hx' : x' ∈ PS u v (F.erase e) b' := by
    refine ⟨fun f => ?_, fun f hf => ?_, fun z => ?_, hodd⟩
    · by_cases hfe : f = e
      · simp [hx'def, hfe]
      · simp [hx'def, hfe, hx.1 f]
    · by_cases hfe : f = e
      · simp [hx'def, hfe]
      · simp only [hx'def, hfe, ite_false]
        exact hx.2.1 f (fun h => hf (Finset.mem_erase.mpr ⟨hfe, h⟩))
    · rw [dsum_congr hx'e]
      have h1 := dsum_split (u := u) (v := v) he x z
      rw [hx.2.2.1 z] at h1
      have h2 := hb'R z
      by_cases hz : u e = z ∨ v e = z
      · simp only [hz, ite_true] at h1 h2; rw [hxe] at h1; linarith
      · simp only [hz, ite_false] at h1 h2; linarith
  have hG' : Good u v (F.erase e) b' := by
    refine ⟨fun f hf => hG.1 f (Finset.mem_of_mem_erase hf), fun f hf => ?_⟩
    have hfe := Finset.ne_of_mem_erase hf
    have hfF := Finset.mem_of_mem_erase hf
    have hsf := hs_only f hfF hfe
    have key : ∀ p, (u f = p ∨ v f = p) → b p = 1 → b' p = 1 := by
      intro p hp hbp
      have hps : p ≠ s := by
        rintro rfl; exact hsf hp
      have hpw : p ≠ w := by
        rintro rfl
        have h1 := le_dsum_two hx.1 (Ne.symm hfe) he hfF hew hp
        rw [hx.2.2.1 p, hbp, hxe] at h1
        have := hpos f hfF
        push_cast at h1
        linarith
      simp [hb'def, hps, hpw, hbp]
    rcases hG.2 f hfF with h | h
    · exact Or.inl (key _ (Or.inl rfl) h)
    · exact Or.inr (key _ (Or.inr rfl) h)
  have hmeas : (F.erase e).card + ∑ z, b' z < F.card + ∑ z, b z := by
    rw [Finset.card_erase_of_mem he]
    have h1 : ∑ z, b z = ∑ z, b' z + 1 + 1 := by
      rw [← Finset.sum_congr rfl (fun z _ => hb' z), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp
    have := Finset.card_pos.mpr ⟨e, he⟩
    omega
  have hconv := hIH u v (F.erase e) b' hmeas hG' hx'
  set δe : E → ℝ := fun f => if f = e then 1 else 0 with hδe
  have hxeq : x = δe +ᵥ x' := by
    funext f
    simp only [vadd_eq_add, Pi.add_apply, hδe, hx'def]
    by_cases hfe : f = e
    · simp [hfe, hxe]
    · simp [hfe]
  rw [hxeq]
  have h1 : δe +ᵥ x' ∈ δe +ᵥ convexHull ℝ (IS u v (F.erase e) b') := Set.vadd_mem_vadd_set hconv
  rw [← convexHull_vadd] at h1
  refine convexHull_mono ?_ h1
  rintro _ ⟨z, hz, rfl⟩
  have hze : z e = 0 := hz.2.1 e (Finset.notMem_erase e F)
  refine ⟨fun f => ?_, fun f hf => ?_, fun p => ?_⟩
  · simp only [vadd_eq_add, Pi.add_apply, hδe]
    by_cases hfe : f = e
    · simp [hfe, hze]
    · simp only [hfe, ite_false, zero_add]; exact hz.1 f
  · have hfe : f ≠ e := fun h => hf (h ▸ he)
    simp only [vadd_eq_add, Pi.add_apply, hδe, hfe, ite_false, zero_add]
    exact hz.2.1 f (fun h => hf (Finset.mem_of_mem_erase h))
  · rw [dsum_split he]
    have h2 : dsum u v (F.erase e) (δe +ᵥ z) p = dsum u v (F.erase e) z p := by
      apply dsum_congr
      intro f hf
      simp [hδe, Finset.ne_of_mem_erase hf]
    rw [h2, hz.2.2 p, ← hb'R p]
    simp [hδe, hze]

omit [Fintype E] in
lemma step_one {u v : E → V} {F : Finset E} {b : V → ℕ} (hIH : IHP F b)
    (hG : Good u v F b) {x : E → ℝ} (hx : x ∈ PS u v F b) (hpos : ∀ f ∈ F, 0 < x f) {e : E}
    (he : e ∈ F) (hxe : x e = 1) : x ∈ convexHull ℝ (IS u v F b) := by
  have hne := hG.1 e he
  rcases hG.2 e he with h | h
  · refine step_one_core hIH hG hx hpos he hxe (w := v e) (s := u e) (Ne.symm hne) ?_ h
    intro z; constructor
    · rintro (h1 | h1) <;> [right; left] <;> exact h1.symm
    · rintro (h1 | h1) <;> [right; left] <;> exact h1.symm
  · refine step_one_core hIH hG hx hpos he hxe (w := u e) (s := v e) hne ?_ h
    intro z; constructor
    · rintro (h1 | h1) <;> [left; right] <;> exact h1.symm
    · rintro (h1 | h1) <;> [left; right] <;> exact h1.symm

omit [Fintype V] [Fintype E] in
lemma mem_cut {u v : E → V} {F : Finset E} {U : Finset V} {e : E} :
    e ∈ cut u v F U ↔ e ∈ F ∧ (u e ∈ U) ≠ (v e ∈ U) := Finset.mem_filter

/-- The map contracting `U` to `r`. -/
noncomputable def cmap (U : Finset V) (r : V) (z : V) : V := if z ∈ U then r else z

/-- The edges of `F` not inside `U`. -/
noncomputable def cF (u v : E → V) (F : Finset E) (U : Finset V) : Finset E :=
  F.filter (fun e => ¬(u e ∈ U ∧ v e ∈ U))

/-- Demands after contracting `U` to `r`. -/
noncomputable def cb (b : V → ℕ) (U : Finset V) (r : V) (z : V) : ℕ :=
  if z = r then 1 else if z ∈ U then 0 else b z

/-- Restriction of `x` to `F'`. -/
noncomputable def cx (x : E → ℝ) (F' : Finset E) (e : E) : ℝ := if e ∈ F' then x e else 0

omit [Fintype V] in
lemma cmap_eq_r {U : Finset V} {r : V} (hr : r ∈ U) (p : V) : cmap U r p = r ↔ p ∈ U := by
  unfold cmap
  by_cases hp : p ∈ U
  · simp [hp]
  · simp only [hp, ite_false, iff_false]
    rintro rfl; exact hp hr

omit [Fintype V] in
lemma cmap_eq_out {U : Finset V} {r : V} (hr : r ∈ U) {w : V} (hw : w ∉ U) (p : V) :
    cmap U r p = w ↔ p = w := by
  unfold cmap
  by_cases hp : p ∈ U
  · simp only [hp, ite_true]
    constructor
    · rintro rfl; exact absurd hr hw
    · rintro rfl; exact absurd hp hw
  · simp [hp]

omit [Fintype V] in
lemma cmap_ne_in {U : Finset V} {r : V} {w : V} (hw : w ∈ U) (hwr : w ≠ r) (p : V) :
    cmap U r p ≠ w := by
  unfold cmap
  by_cases hp : p ∈ U
  · simp only [hp, ite_true]; exact Ne.symm hwr
  · simp only [hp, ite_false]; rintro rfl; exact hp hw

omit [Fintype E] [Fintype V] in
lemma cdsum_out (u v : E → V) (F : Finset E) {U : Finset V} {r : V} (hr : r ∈ U) {w : V}
    (hw : w ∉ U) (y : E → ℝ) :
    dsum (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) y w = dsum u v F y w := by
  unfold dsum
  congr 1
  ext e
  simp only [cF, Finset.mem_filter, Function.comp, cmap_eq_out hr hw]
  constructor
  · rintro ⟨⟨he, _⟩, h⟩; exact ⟨he, h⟩
  · rintro ⟨he, h⟩
    refine ⟨⟨he, ?_⟩, h⟩
    rintro ⟨h1, h2⟩
    rcases h with rfl | rfl
    · exact hw h1
    · exact hw h2

omit [Fintype E] [Fintype V] in
lemma cdsum_r (u v : E → V) (F : Finset E) {U : Finset V} {r : V} (hr : r ∈ U) (y : E → ℝ) :
    dsum (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) y r = ∑ e ∈ cut u v F U, y e := by
  unfold dsum cut
  congr 1
  ext e
  simp only [cF, Finset.mem_filter, Function.comp, cmap_eq_r hr]
  by_cases h1 : u e ∈ U <;> by_cases h2 : v e ∈ U <;> simp [h1, h2]

omit [Fintype E] [Fintype V] in
lemma cdsum_in (u v : E → V) (F : Finset E) {U : Finset V} {r : V} {w : V} (hw : w ∈ U)
    (hwr : w ≠ r) (y : E → ℝ) :
    dsum (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) y w = 0 := by
  unfold dsum
  rw [Finset.sum_eq_zero]
  intro e he
  simp only [Finset.mem_filter, Function.comp] at he
  rcases he.2 with h | h
  · exact absurd h (cmap_ne_in hw hwr _)
  · exact absurd h (cmap_ne_in hw hwr _)

omit [Fintype E] in
lemma ccut (u v : E → V) (F : Finset E) {U : Finset V} {r : V} (hr : r ∈ U) (W : Finset V) :
    cut (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) W =
      cut u v F (univ.filter (fun p => cmap U r p ∈ W)) := by
  ext e
  simp only [cut, cF, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨⟨he, _⟩, h⟩; exact ⟨he, h⟩
  · rintro ⟨he, h⟩
    refine ⟨⟨he, ?_⟩, h⟩
    rintro ⟨h1, h2⟩
    apply h
    rw [(cmap_eq_r hr _).mpr h1, (cmap_eq_r hr _).mpr h2]

lemma cb_sum (b : V → ℕ) {U : Finset V} {r : V} (hr : r ∈ U) (W : Finset V) :
    ∑ z ∈ W, cb b U r z = (if r ∈ W then 1 else 0) + ∑ z ∈ Uᶜ, (if z ∈ W then b z else 0) := by
  have h0 : ∑ z ∈ W, cb b U r z = ∑ z, (if z ∈ W then cb b U r z else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h0, ← Finset.sum_add_sum_compl U]
  congr 1
  · rw [Finset.sum_congr rfl (g := fun z => if z = r then (if r ∈ W then 1 else 0) else 0)]
    · rw [Finset.sum_ite_eq' U r]; simp [hr]
    · intro z hz
      by_cases hzr : z = r
      · subst hzr; simp [cb]
      · simp [cb, hzr, hz]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hzU : z ∉ U := Finset.mem_compl.mp hz
    have hzr : z ≠ r := fun h => hzU (h ▸ hr)
    simp [cb, hzr, hzU]

lemma pre_sum (b : V → ℕ) {U : Finset V} {r : V} (W : Finset V) :
    ∑ p ∈ univ.filter (fun p => cmap U r p ∈ W), b p =
      (if r ∈ W then ∑ p ∈ U, b p else 0) + ∑ z ∈ Uᶜ, (if z ∈ W then b z else 0) := by
  rw [Finset.sum_filter, ← Finset.sum_add_sum_compl U]
  congr 1
  · by_cases hrW : r ∈ W
    · simp only [hrW, ite_true]
      refine Finset.sum_congr rfl fun p hp => ?_
      simp [cmap, hp, hrW]
    · simp only [hrW, ite_false]
      refine Finset.sum_eq_zero fun p hp => ?_
      simp [cmap, hp, hrW]
  · refine Finset.sum_congr rfl fun z hz => ?_
    simp [cmap, Finset.mem_compl.mp hz]

omit [Fintype E] in
lemma contract_PS {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ}
    (hx : x ∈ PS u v F b) {U : Finset V} {r : V} (hr : r ∈ U)
    (hU : Odd (∑ z ∈ U, b z)) (ht : ∑ e ∈ cut u v F U, x e = 1) :
    cx x (cF u v F U) ∈ PS (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) (cb b U r) := by
  have hcx : ∀ e ∈ cF u v F U, cx x (cF u v F U) e = x e := fun e he => by simp [cx, he]
  refine ⟨fun e => ?_, fun e he => by simp [cx, he], fun w => ?_, fun W hW => ?_⟩
  · unfold cx; split_ifs <;> simp [hx.1 e]
  · rw [dsum_congr hcx]
    by_cases hwr : w = r
    · subst hwr; rw [cdsum_r u v F hr, ht]; simp [cb]
    · by_cases hwU : w ∈ U
      · rw [cdsum_in u v F hwU hwr]; simp [cb, hwr, hwU]
      · rw [cdsum_out u v F hr hwU, hx.2.2.1 w]; simp [cb, hwr, hwU]
  · have h1 : ∑ e ∈ cut (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) W, cx x (cF u v F U) e =
        ∑ e ∈ cut (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) W, x e :=
      Finset.sum_congr rfl (fun e he => hcx e (mem_cut.mp he).1)
    rw [h1, ccut u v F hr]
    apply hx.2.2.2
    rw [pre_sum b]
    rw [cb_sum b hr] at hW
    rw [Nat.odd_iff] at hW hU ⊢
    by_cases hrW : r ∈ W
    · simp only [hrW, ite_true] at hW ⊢; omega
    · simp only [hrW, ite_false] at hW ⊢; omega

omit [Fintype E] [Fintype V] in
lemma contract_Good {u v : E → V} {F : Finset E} {b : V → ℕ} (hG : Good u v F b)
    {U : Finset V} {r : V} (hr : r ∈ U) :
    Good (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) (cb b U r) := by
  constructor
  · intro e he
    simp only [cF, Finset.mem_filter] at he
    simp only [Function.comp]
    by_cases h1 : u e ∈ U <;> by_cases h2 : v e ∈ U
    · exact absurd ⟨h1, h2⟩ he.2
    · rw [(cmap_eq_r hr _).mpr h1]; intro h; exact h2 ((cmap_eq_r hr _).mp h.symm)
    · rw [(cmap_eq_r hr _).mpr h2]; intro h; exact h1 ((cmap_eq_r hr _).mp h)
    · simp only [cmap, h1, h2, ite_false]; exact hG.1 e he.1
  · intro e he
    simp only [cF, Finset.mem_filter] at he
    simp only [Function.comp]
    by_cases h1 : u e ∈ U
    · left; rw [(cmap_eq_r hr _).mpr h1]; simp [cb]
    · by_cases h2 : v e ∈ U
      · right; rw [(cmap_eq_r hr _).mpr h2]; simp [cb]
      · have hr1 : u e ≠ r := fun h => h1 (h ▸ hr)
        have hr2 : v e ≠ r := fun h => h2 (h ▸ hr)
        simp only [cmap, h1, h2, ite_false, cb, hr1, hr2]
        exact hG.2 e he.1

omit [Fintype E] in
lemma contract_measure (u v : E → V) (F : Finset E) (b : V → ℕ) {U : Finset V} {r : V}
    (hr : r ∈ U) (h2 : 2 ≤ ∑ z ∈ U, b z) :
    (cF u v F U).card + ∑ z, cb b U r z < F.card + ∑ z, b z := by
  have h1 : (cF u v F U).card ≤ F.card := Finset.card_le_card (Finset.filter_subset _ _)
  have h3 : ∑ z, cb b U r z = 1 + ∑ z ∈ Uᶜ, b z := by
    have := cb_sum b hr univ
    simp only [Finset.mem_univ, ite_true] at this
    rw [this]
  have h4 := Finset.sum_add_sum_compl U b
  omega

omit [Fintype E] [Fintype V] in
lemma contract_IS {u v : E → V} {F : Finset E} {b : V → ℕ} {U : Finset V} {r : V}
    (hr : r ∈ U) {z : E → ℝ}
    (hz : z ∈ IS (cmap U r ∘ u) (cmap U r ∘ v) (cF u v F U) (cb b U r)) :
    ∑ e ∈ cut u v F U, z e = 1 ∧ ∀ w ∉ U, dsum u v F z w = b w := by
  refine ⟨?_, fun w hw => ?_⟩
  · have := hz.2.2 r
    rw [cdsum_r u v F hr] at this
    rw [this]; simp [cb]
  · have := hz.2.2 w
    rw [cdsum_out u v F hr hw] at this
    have hwr : w ≠ r := fun h => hw (h ▸ hr)
    rw [this]; simp [cb, hwr, hw]

omit [Fintype E] in
lemma eq_zero_of_sum_one {C : Finset E} {z : E → ℝ} (h01 : ∀ e ∈ C, z e = 0 ∨ z e = 1)
    (hs : ∑ e ∈ C, z e = 1) {e : E} (he : e ∈ C) (hze : z e = 1) {f : E} (hf : f ∈ C)
    (hfe : f ≠ e) : z f = 0 := by
  have h1 := Finset.add_sum_erase C z he
  rw [hze, hs] at h1
  have h2 : ∑ g ∈ C.erase e, z g = 0 := by linarith
  have hnn : ∀ g ∈ C.erase e, 0 ≤ z g := fun g hg => by
    rcases h01 g (Finset.mem_of_mem_erase hg) with h | h <;> simp [h]
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h2 f (Finset.mem_erase.mpr ⟨hfe, hf⟩)

omit [Fintype E] in
lemma glue_mem {ι ι' : Type*} [Fintype ι] [Fintype ι'] (C : Finset E) (x : E → ℝ)
    (hxC : ∀ e ∈ C, 0 < x e) (hsum : ∑ e ∈ C, x e = 1)
    (lam : ι → ℝ) (mu : ι' → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j)
    (Z1 : ι → E → ℝ) (Z2 : ι' → E → ℝ)
    (hZ1 : ∀ i, ∀ e ∈ C, Z1 i e = 0 ∨ Z1 i e = 1) (hZ2 : ∀ j, ∀ e ∈ C, Z2 j e = 0 ∨ Z2 j e = 1)
    (hZ1s : ∀ i, ∑ e ∈ C, Z1 i e = 1) (hZ2s : ∀ j, ∑ e ∈ C, Z2 j e = 1)
    (hx1 : ∀ e ∈ C, ∑ i, lam i * Z1 i e = x e) (hx2 : ∀ e ∈ C, ∑ j, mu j * Z2 j e = x e)
    (P : E → Prop) (S : Set (E → ℝ))
    (hS : ∀ e ∈ C, ∀ i j, Z1 i e = 1 → Z2 j e = 1 →
      (fun f => if P f then Z2 j f else Z1 i f) ∈ S) :
    (fun f => if P f then ∑ j, mu j * Z2 j f else ∑ i, lam i * Z1 i f) ∈ convexHull ℝ S := by
  set t := (C ×ˢ (univ ×ˢ univ)).filter
    (fun p : E × ι × ι' => Z1 p.2.1 p.1 = 1 ∧ Z2 p.2.2 p.1 = 1) with ht
  set ω : E × ι × ι' → ℝ := fun p => lam p.2.1 * mu p.2.2 / x p.1 with hω
  set g : E × ι × ι' → E → ℝ := fun p f => if P f then Z2 p.2.2 f else Z1 p.2.1 f with hg
  have key : ∀ h : E × ι × ι' → ℝ,
      ∑ p ∈ t, h p = ∑ e ∈ C, ∑ i, ∑ j, Z1 i e * Z2 j e * h (e, i, j) := by
    intro h
    rw [ht, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases hZ1 i e he with h1 | h1 <;> rcases hZ2 j e he with h2 | h2
    all_goals simp [h1, h2]
  have hω0 : ∀ p ∈ t, 0 ≤ ω p := by
    intro p hp
    have hpC : p.1 ∈ C := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    exact div_nonneg (mul_nonneg (hlam _) (hmu _)) (hxC _ hpC).le
  have hω1 : ∑ p ∈ t, ω p = 1 := by
    rw [key, ← hsum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hxe := (hxC e he).ne'
    calc ∑ i, ∑ j, Z1 i e * Z2 j e * ω (e, i, j)
        = (∑ i, lam i * Z1 i e) * (∑ j, mu j * Z2 j e) / x e := by
          rw [Finset.sum_mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hω]; ring
      _ = x e := by rw [hx1 e he, hx2 e he]; field_simp
  have hg0 : ∀ p ∈ t, g p ∈ convexHull ℝ S := by
    intro p hp
    simp only [ht, Finset.mem_filter, Finset.mem_product] at hp
    exact subset_convexHull ℝ S (hS _ hp.1.1 _ _ hp.2.1 hp.2.2)
  have hmem := (convex_convexHull ℝ S).sum_mem hω0 hω1 hg0
  convert hmem using 1
  funext f
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [key]
  by_cases hf : P f
  · simp only [hg, hf, ite_true]
    have h1 : ∀ e ∈ C, ∑ i, ∑ j, Z1 i e * Z2 j e * (ω (e, i, j) * Z2 j f) =
        ∑ j, mu j * Z2 j f * Z2 j e := by
      intro e he
      have hxe := (hxC e he).ne'
      calc ∑ i, ∑ j, Z1 i e * Z2 j e * (ω (e, i, j) * Z2 j f)
          = (∑ i, lam i * Z1 i e) * (∑ j, mu j * Z2 j f * Z2 j e) / x e := by
            rw [Finset.sum_mul_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hω]; ring
        _ = _ := by rw [hx1 e he]; field_simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, hZ2s j, mul_one]
  · simp only [hg, hf, ite_false]
    have h1 : ∀ e ∈ C, ∑ i, ∑ j, Z1 i e * Z2 j e * (ω (e, i, j) * Z1 i f) =
        ∑ i, lam i * Z1 i f * Z1 i e := by
      intro e he
      have hxe := (hxC e he).ne'
      calc ∑ i, ∑ j, Z1 i e * Z2 j e * (ω (e, i, j) * Z1 i f)
          = (∑ i, lam i * Z1 i f * Z1 i e) * (∑ j, mu j * Z2 j e) / x e := by
            rw [Finset.sum_mul_sum, Finset.sum_div]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hω]; ring
        _ = _ := by rw [hx2 e he]; field_simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hZ1s i, mul_one]

omit [Fintype E] in
lemma step_contract {u v : E → V} {F : Finset E} {b : V → ℕ} (hIH : IHP F b)
    (hG : Good u v F b) {x : E → ℝ} (hx : x ∈ PS u v F b) (hpos : ∀ f ∈ F, 0 < x f)
    {U : Finset V} (hU : Odd (∑ z ∈ U, b z)) (ht : ∑ e ∈ cut u v F U, x e = 1)
    (h2 : 2 ≤ ∑ z ∈ U, b z) (h2' : 2 ≤ ∑ z ∈ Uᶜ, b z) : x ∈ convexHull ℝ (IS u v F b) := by
  obtain ⟨r, hr⟩ : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at h2
  obtain ⟨r', hr'⟩ : Uᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at h2'; simp at h2'
  have hUc : Odd (∑ z ∈ Uᶜ, b z) := odd_compl hx hU
  have htc : ∑ e ∈ cut u v F Uᶜ, x e = 1 := by rw [cut_compl]; exact ht
  have hc1 := hIH _ _ _ _ (contract_measure u v F b hr h2) (contract_Good hG hr)
    (contract_PS hx hr hU ht)
  have hc2 := hIH _ _ _ _ (contract_measure u v F b hr' h2') (contract_Good hG hr')
    (contract_PS hx hr' hUc htc)
  obtain ⟨ι, _, lam, Z1, hlam, hlam1, hZ1, hsum1⟩ := mem_convexHull_iff_exists_fintype.mp hc1
  obtain ⟨ι', _, mu, Z2, hmu, hmu1, hZ2, hsum2⟩ := mem_convexHull_iff_exists_fintype.mp hc2
  have hev1 : ∀ f, ∑ i, lam i * Z1 i f = cx x (cF u v F U) f := by
    intro f; rw [← hsum1, Finset.sum_apply]; simp
  have hev2 : ∀ f, ∑ j, mu j * Z2 j f = cx x (cF u v F Uᶜ) f := by
    intro f; rw [← hsum2, Finset.sum_apply]; simp
  have hcutF : ∀ e ∈ cut u v F U, e ∈ cF u v F U ∧ e ∈ cF u v F Uᶜ := by
    intro e he
    rw [mem_cut] at he
    simp only [cF, Finset.mem_filter, Finset.mem_compl]
    refine ⟨⟨he.1, fun h => he.2 ?_⟩, ⟨he.1, fun h => he.2 ?_⟩⟩
    · rw [eq_iff_iff]; exact ⟨fun _ => h.2, fun _ => h.1⟩
    · rw [eq_iff_iff]; exact ⟨fun h' => absurd h' h.1, fun h' => absurd h' h.2⟩
  have hglue := glue_mem (cut u v F U) x (fun e he => hpos e (mem_cut.mp he).1) ht lam mu
    hlam hmu Z1 Z2 (fun i e _ => (hZ1 i).1 e) (fun j e _ => (hZ2 j).1 e)
    (fun i => (contract_IS hr (hZ1 i)).1)
    (fun j => by rw [← cut_compl]; exact (contract_IS hr' (hZ2 j)).1)
    (fun e he => by rw [hev1]; simp [cx, (hcutF e he).1])
    (fun e he => by rw [hev2]; simp [cx, (hcutF e he).2])
    (fun f => u f ∈ U ∧ v f ∈ U) (IS u v F b) ?_
  · convert hglue using 1
    funext f
    by_cases hf : u f ∈ U ∧ v f ∈ U
    · simp only [hf, and_self, ite_true]
      rw [hev2]
      by_cases hfF : f ∈ F
      · have : f ∈ cF u v F Uᶜ := by
          simp only [cF, Finset.mem_filter, Finset.mem_compl]; exact ⟨hfF, fun h => h.1 hf.1⟩
        simp [cx, this]
      · have : f ∉ cF u v F Uᶜ := fun h => hfF (Finset.mem_filter.mp h).1
        simp [cx, this, hx.2.1 f hfF]
    · simp only [hf, ite_false]
      rw [hev1]
      by_cases hfF : f ∈ F
      · have : f ∈ cF u v F U := by
          simp only [cF, Finset.mem_filter]; exact ⟨hfF, hf⟩
        simp [cx, this]
      · have : f ∉ cF u v F U := fun h => hfF (Finset.mem_filter.mp h).1
        simp [cx, this, hx.2.1 f hfF]
  · intro e he i j h1 h2
    have hz1 := hZ1 i
    have hz2 := hZ2 j
    obtain ⟨hs1, hd1⟩ := contract_IS hr hz1
    obtain ⟨hs2, hd2⟩ := contract_IS hr' hz2
    rw [cut_compl] at hs2
    have hagree : ∀ f ∈ cut u v F U, Z1 i f = Z2 j f := by
      intro f hf
      by_cases hfe : f = e
      · rw [hfe, h1, h2]
      · rw [eq_zero_of_sum_one (fun g _ => hz1.1 g) hs1 he h1 hf hfe,
          eq_zero_of_sum_one (fun g _ => hz2.1 g) hs2 he h2 hf hfe]
    refine ⟨fun f => ?_, fun f hf => ?_, fun w => ?_⟩
    · by_cases hf : u f ∈ U ∧ v f ∈ U
      · simp only [hf, and_self, ite_true]; exact hz2.1 f
      · simp only [hf, ite_false]; exact hz1.1 f
    · by_cases hf' : u f ∈ U ∧ v f ∈ U
      · simp only [hf', and_self, ite_true]
        exact hz2.2.1 f (fun h => hf (Finset.mem_filter.mp h).1)
      · simp only [hf', ite_false]
        exact hz1.2.1 f (fun h => hf (Finset.mem_filter.mp h).1)
    · by_cases hwU : w ∈ U
      · rw [← hd2 w (fun h => (Finset.mem_compl.mp h) hwU)]
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [Finset.mem_filter] at hf
        by_cases hfin : u f ∈ U ∧ v f ∈ U
        · simp only [hfin, and_self, ite_true]
        · simp only [hfin, ite_false]
          apply hagree f
          rw [mem_cut]
          refine ⟨hf.1, fun h => hfin ?_⟩
          rw [eq_iff_iff] at h
          rcases hf.2 with h' | h'
          · rw [h'] at h ⊢; exact ⟨hwU, h.mp hwU⟩
          · rw [h'] at h ⊢; exact ⟨h.mpr hwU, hwU⟩
      · rw [← hd1 w hwU]
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [Finset.mem_filter] at hf
        have hfin : ¬(u f ∈ U ∧ v f ∈ U) := by
          rintro ⟨h1', h2'⟩
          rcases hf.2 with h' | h'
          · rw [h'] at h1'; exact hwU h1'
          · rw [h'] at h2'; exact hwU h2'
        simp only [hfin, ite_false]

omit [Fintype V] [Fintype E] in
lemma other_end {u v : E → V} {e : E} (hl : u e ≠ v e) {w : V} (hw : u e = w ∨ v e = w) :
    ∃ a, a ≠ w ∧ ∀ z, (u e = z ∨ v e = z) ↔ (z = w ∨ z = a) := by
  rcases hw with h | h
  · refine ⟨v e, fun h' => hl (h.trans h'.symm), fun z => ?_⟩
    rw [h]; constructor <;> rintro (h1 | h1) <;> first | exact Or.inl h1.symm | exact Or.inr h1.symm
  · refine ⟨u e, fun h' => hl (h'.trans h.symm), fun z => ?_⟩
    rw [h]; constructor <;> rintro (h1 | h1) <;> first | exact Or.inr h1.symm | exact Or.inl h1.symm

omit [Fintype V] [Fintype E] in
lemma dsum_single {u v : E → V} {F : Finset E} {e : E} (he : e ∈ F) (z : V) :
    dsum u v F (fun f => if f = e then 1 else 0) z = if u e = z ∨ v e = z then 1 else 0 := by
  unfold dsum
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_filter, he]

lemma deg_kernel {u v : E → V} {F : Finset E} {b : V → ℕ} {x : E → ℝ} (hG : Good u v F b)
    (hx : x ∈ PS u v F b) (hpos : ∀ e ∈ F, 0 < x e) (hlt : ∀ e ∈ F, x e < 1)
    (hne : F.Nonempty)
    (hnt : ∀ U : Finset V, Odd (∑ z ∈ U, b z) → ∑ e ∈ cut u v F U, x e = 1 →
      ∑ z ∈ U, b z < 2 ∨ ∑ z ∈ Uᶜ, b z < 2) :
    ∃ d : E → ℝ, d ≠ 0 ∧ (∀ e ∉ F, d e = 0) ∧ ∀ w, dsum u v F d w = 0 := by
  set N := univ.filter (fun z => b z ≠ 0) with hN
  have hiso : ∀ z, b z = 0 → ∀ e ∈ F, ¬(u e = z ∨ v e = z) := by
    intro z hz e he h
    have := one_le_b hx hpos he h
    omega
  have hiso' : ∀ (d : E → ℝ) z, b z = 0 → dsum u v F d z = 0 := by
    intro d z hz
    unfold dsum
    rw [Finset.sum_eq_zero]
    intro e he
    exact absurd (Finset.mem_filter.mp he).2 (hiso z hz e (Finset.mem_filter.mp he).1)
  by_cases hcard : N.card < F.card
  · obtain ⟨d, hd0, hdF, hdS⟩ := exists_kernel u v F N hcard
    refine ⟨d, hd0, hdF, fun w => ?_⟩
    by_cases hw : b w = 0
    · exact hiso' d w hw
    · exact hdS w (by simp [hN, hw])
  replace hcard := not_lt.mp hcard
  set deg : V → ℕ := fun z => (F.filter (fun e => u e = z ∨ v e = z)).card with hdeg
  have hdegR : ∀ z, dsum u v F (fun _ => 1) z = deg z := by
    intro z; simp [dsum, hdeg]
  have hdegsum : ∑ z, deg z = 2 * F.card := by
    have h := sum_mul_dsum u v F hG.1 (fun _ => 1) (fun _ => 1)
    simp only [one_mul, hdegR, Finset.sum_const, nsmul_eq_mul] at h
    have h2 : ((∑ z, deg z : ℕ) : ℝ) = ((2 * F.card : ℕ) : ℝ) := by
      push_cast; rw [h]; ring
    exact_mod_cast h2
  have hdeg0 : ∀ z, b z = 0 → deg z = 0 := by
    intro z hz
    simp only [hdeg, Finset.card_eq_zero]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    exact hiso z hz e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  have hdeg2 : ∀ z ∈ N, 2 ≤ deg z := by
    intro z hz
    have hbz : b z ≠ 0 := (Finset.mem_filter.mp hz).2
    by_contra h
    have h' : deg z = 0 ∨ deg z = 1 := by omega
    rcases h' with h0 | h1
    · have : dsum u v F x z = 0 := by
        unfold dsum
        rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
      rw [hx.2.2.1 z] at this
      exact hbz (by exact_mod_cast this)
    · obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
      have h3 : dsum u v F x z = x e := by
        unfold dsum; rw [he, Finset.sum_singleton]
      have heF : e ∈ F := (Finset.mem_filter.mp (he ▸ Finset.mem_singleton_self e)).1
      rw [hx.2.2.1 z] at h3
      have h4 : (1 : ℝ) ≤ b z := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hbz
      linarith [hlt e heF]
  have hsumN : ∑ z ∈ N, deg z = 2 * F.card := by
    rw [← hdegsum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : b z = 0
    · simp [hz, hdeg0 z hz]
    · simp [hz]
  have hFN : F.card = N.card := by
    have := Finset.sum_le_sum hdeg2
    simp only [Finset.sum_const, smul_eq_mul] at this
    omega
  have hdegeq : ∀ z ∈ N, deg z = 2 := by
    have h1 : ∑ z ∈ N, deg z = ∑ z ∈ N, 2 := by
      rw [hsumN, Finset.sum_const, smul_eq_mul, hFN, mul_comm]
    intro z hz
    exact ((Finset.sum_eq_sum_iff_of_le hdeg2).mp h1.symm z hz).symm
  have hb1 : ∀ z ∈ N, b z = 1 := by
    intro z hz
    have hbz : b z ≠ 0 := (Finset.mem_filter.mp hz).2
    have h1 : dsum u v F x z < deg z := by
      rw [← hdegR]
      unfold dsum
      apply Finset.sum_lt_sum_of_nonempty
      · rw [← Finset.card_pos]; have := hdegeq z hz; simp only [hdeg] at this; omega
      · intro e he; exact hlt e (Finset.mem_filter.mp he).1
    rw [hx.2.2.1 z, hdegeq z hz] at h1
    have : b z < 2 := by exact_mod_cast h1
    omega
  -- the vector x - 1/2
  set d0 : E → ℝ := fun e => if e ∈ F then x e - 1 / 2 else 0 with hd0
  have hd0D : ∀ w, dsum u v F d0 w = 0 := by
    intro w
    by_cases hw : b w = 0
    · exact hiso' d0 w hw
    · have hwN : w ∈ N := by simp [hN, hw]
      have h1 : dsum u v F d0 w = dsum u v F x w - deg w / 2 := by
        unfold dsum
        rw [Finset.sum_congr rfl (g := fun e => x e - 1 / 2)]
        · rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
        · intro e he; simp [hd0, (Finset.mem_filter.mp he).1]
      rw [h1, hx.2.2.1 w, hb1 w hwN, hdegeq w hwN]; norm_num
  by_cases hd0z : d0 ≠ 0
  · exact ⟨d0, hd0z, fun e he => by simp [hd0, he], hd0D⟩
  replace hd0z : d0 = 0 := not_not.mp hd0z
  have hhalf : ∀ e ∈ F, x e = 1 / 2 := by
    intro e he
    have := congrFun hd0z e
    simp only [hd0, he, ite_true, Pi.zero_apply] at this
    linarith
  obtain ⟨e0, he0⟩ := hne
  set w := u e0 with hw
  have hwN : w ∈ N := by
    have : 1 ≤ b w := one_le_b hx hpos he0 (Or.inl rfl : u e0 = w ∨ v e0 = w)
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  obtain ⟨e1, e2, he12, hfil⟩ := Finset.card_eq_two.mp (hdegeq w hwN)
  have he1 : e1 ∈ F.filter (fun e => u e = w ∨ v e = w) := by rw [hfil]; simp
  have he2 : e2 ∈ F.filter (fun e => u e = w ∨ v e = w) := by rw [hfil]; simp
  rw [Finset.mem_filter] at he1 he2
  obtain ⟨a, haw, ha⟩ := other_end (hG.1 e1 he1.1) he1.2
  obtain ⟨c, hcw, hc⟩ := other_end (hG.1 e2 he2.1) he2.2
  by_cases hac : a = c
  · subst hac
    refine ⟨fun f => (if f = e1 then 1 else 0) - (if f = e2 then 1 else 0), ?_, ?_, ?_⟩
    · intro h
      have := congrFun h e1
      simp [he12] at this
    · intro f hf
      have h1 : f ≠ e1 := fun h => hf (h ▸ he1.1)
      have h2 : f ≠ e2 := fun h => hf (h ▸ he2.1)
      simp [h1, h2]
    · intro z
      have h := dsum_sub (u := u) (v := v) (F := F) (fun f => if f = e1 then (1:ℝ) else 0)
        (fun f => if f = e2 then (1:ℝ) else 0) z
      rw [h, dsum_single he1.1, dsum_single he2.1]
      have : (u e1 = z ∨ v e1 = z) ↔ (u e2 = z ∨ v e2 = z) := by rw [ha, hc]
      by_cases hz : u e1 = z ∨ v e1 = z
      · simp [hz, this.mp hz]
      · have hz' : ¬(u e2 = z ∨ v e2 = z) := fun h' => hz (this.mpr h')
        simp only [hz, hz', ite_false, sub_zero]
  · -- the three-vertex set
    set U : Finset V := {a, w, c} with hU
    have haN : a ∈ N := by
      have := one_le_b hx hpos he1.1 ((ha a).mpr (Or.inr rfl))
      simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hcN : c ∈ N := by
      have := one_le_b hx hpos he2.1 ((hc c).mpr (Or.inr rfl))
      simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hbU : ∑ z ∈ U, b z = 3 := by
      rw [hU, Finset.sum_insert (by simp [haw, hac]), Finset.sum_insert (by simp [Ne.symm hcw]),
        Finset.sum_singleton, hb1 a haN, hb1 w hwN, hb1 c hcN]
      norm_num
    have hUodd : Odd (∑ z ∈ U, b z) := by rw [hbU]; decide
    have hins1 : e1 ∈ inside u v F U := by
      simp only [inside, Finset.mem_filter, hU, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨he1.1, ?_, ?_⟩
      · rcases (ha (u e1)).mp (Or.inl rfl) with h | h <;> simp [h]
      · rcases (ha (v e1)).mp (Or.inr rfl) with h | h <;> simp [h]
    have hins2 : e2 ∈ inside u v F U := by
      simp only [inside, Finset.mem_filter, hU, Finset.mem_insert, Finset.mem_singleton]
      refine ⟨he2.1, ?_, ?_⟩
      · rcases (hc (u e2)).mp (Or.inl rfl) with h | h <;> simp [h]
      · rcases (hc (v e2)).mp (Or.inr rfl) with h | h <;> simp [h]
    have hhs := handshake u v F hG.1 U x
    have hlhs : ∑ z ∈ U, dsum u v F x z = 3 := by
      rw [Finset.sum_congr rfl (fun z _ => hx.2.2.1 z)]
      have : ((∑ z ∈ U, b z : ℕ) : ℝ) = 3 := by rw [hbU]; norm_num
      rw [← this]; push_cast; rfl
    have hin_ge : x e1 + x e2 ≤ ∑ e ∈ inside u v F U, x e := by
      have hsub : ({e1, e2} : Finset E) ⊆ inside u v F U := by
        intro f hf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl
        · exact hins1
        · exact hins2
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hx.1 g)
      rwa [Finset.sum_pair he12] at this
    have hcut1 := hx.2.2.2 U hUodd
    rw [hhalf e1 he1.1, hhalf e2 he2.1] at hin_ge
    have htight : ∑ e ∈ cut u v F U, x e = 1 := by linarith
    have hin1 : ∑ e ∈ inside u v F U, x e = 1 := by linarith
    have hbUc : ∑ z ∈ Uᶜ, b z = 1 := by
      have h1 := hnt U hUodd htight
      have h2 := odd_compl hx hUodd
      rw [hbU] at h1
      rw [Nat.odd_iff] at h2
      omega
    obtain ⟨t, htU, htb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Uᶜ) (f := b)
      (by rw [hbUc]; norm_num)
    have hothers : ∀ z ∈ Uᶜ, z ≠ t → b z = 0 := by
      intro z hz hzt
      have := add_le_sum_b b hz htU hzt
      omega
    have hinside : inside u v F U = {e1, e2} := by
      apply Finset.Subset.antisymm
      · intro f hf
        by_contra hf'
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf'
        have hsub : ({f, e1, e2} : Finset E) ⊆ inside u v F U := by
          intro g hg
          simp only [Finset.mem_insert, Finset.mem_singleton] at hg
          rcases hg with rfl | rfl | rfl
          · exact hf
          · exact hins1
          · exact hins2
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => hx.1 g)
        rw [Finset.sum_insert (by simp [hf'.1, hf'.2]), Finset.sum_pair he12,
          hhalf e1 he1.1, hhalf e2 he2.1] at this
        have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
        linarith [hpos f hfF]
      · intro f hf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl
        · exact hins1
        · exact hins2
    have hinsidec : inside u v F Uᶜ = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro f hf
      simp only [inside, Finset.mem_filter] at hf
      have h1 := one_le_b hx hpos hf.1 (Or.inl rfl)
      have h2 := one_le_b hx hpos hf.1 (Or.inr rfl)
      have hu : u f = t := by
        by_contra h; have := hothers _ hf.2.1 h; omega
      have hv : v f = t := by
        by_contra h; have := hothers _ hf.2.2 h; omega
      exact hG.1 f hf.1 (hu.trans hv.symm)
    have hUcard : U.card = 3 := by
      rw [hU, Finset.card_insert_of_notMem (by simp [haw, hac]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hcw]), Finset.card_singleton]
    have hNcard : 4 ≤ N.card := by
      have hsub : insert t U ⊆ N := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · simp [hN, htb]
        · simp only [hU, Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact haN
          · exact hwN
          · exact hcN
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp htU), hUcard] at this
      exact this
    obtain ⟨d, hd0, hdF, hdU⟩ := exists_kernel u v F U (by omega)
    refine ⟨d, hd0, hdF, fun z => ?_⟩
    by_cases hzU : z ∈ U
    · exact hdU z hzU
    by_cases hzt : z = t
    · subst hzt
      have h1 := handshake u v F hG.1 U d
      have h2 := handshake u v F hG.1 Uᶜ d
      rw [Finset.sum_eq_zero hdU, hinside, Finset.sum_pair he12] at h1
      rw [hinsidec, Finset.sum_empty, cut_compl] at h2
      have hw0 : d e1 + d e2 = 0 := by
        have := hdU w (by simp [hU])
        unfold dsum at this
        rw [hfil, Finset.sum_pair he12] at this
        exact this
      have h3 : ∑ y ∈ Uᶜ, dsum u v F d y = dsum u v F d z := by
        apply Finset.sum_eq_single_of_mem z htU
        intro y hy hyz
        exact hiso' d y (hothers y hy hyz)
      linarith
    · exact hiso' d z (hothers z (Finset.mem_compl.mpr hzU) hzt)

lemma main_step {u v : E → V} {F : Finset E} {b : V → ℕ} (hIH : IHP F b) (hG : Good u v F b)
    {x : E → ℝ} (hx : x ∈ PS u v F b) : x ∈ convexHull ℝ (IS u v F b) := by
  have hA : ∀ y ∈ PS u v F b, ((∃ e ∈ F, y e = 0) ∨ ∃ U : Finset V, Odd (∑ z ∈ U, b z) ∧
      ∑ e ∈ cut u v F U, y e = 1 ∧ 2 ≤ ∑ z ∈ U, b z ∧ 2 ≤ ∑ z ∈ Uᶜ, b z) →
      y ∈ convexHull ℝ (IS u v F b) := by
    intro y hy h
    by_cases h0 : ∃ e ∈ F, y e = 0
    · obtain ⟨e, he, hye⟩ := h0
      exact step_zero hIH hG hy he hye
    · have hpos : ∀ e ∈ F, 0 < y e := fun e he =>
        lt_of_le_of_ne (hy.1 e) (fun h => h0 ⟨e, he, h.symm⟩)
      rcases h with ⟨e, he, hye⟩ | ⟨U, hU, ht, h2, h2'⟩
      · exact absurd ⟨e, he, hye⟩ h0
      · exact step_contract hIH hG hy hpos hU ht h2 h2'
  by_cases h0 : ∃ e ∈ F, x e = 0
  · exact hA x hx (Or.inl h0)
  have hpos : ∀ e ∈ F, 0 < x e := fun e he =>
    lt_of_le_of_ne (hx.1 e) (fun h => h0 ⟨e, he, h.symm⟩)
  by_cases hT : ∃ U : Finset V, Odd (∑ z ∈ U, b z) ∧ ∑ e ∈ cut u v F U, x e = 1 ∧
      2 ≤ ∑ z ∈ U, b z ∧ 2 ≤ ∑ z ∈ Uᶜ, b z
  · exact hA x hx (Or.inr hT)
  have hnt : ∀ U : Finset V, Odd (∑ z ∈ U, b z) → ∑ e ∈ cut u v F U, x e = 1 →
      ∑ z ∈ U, b z < 2 ∨ ∑ z ∈ Uᶜ, b z < 2 := by
    intro U hU ht
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    exact hT ⟨U, hU, ht, h.1, h.2⟩
  by_cases h1 : ∃ e ∈ F, x e = 1
  · obtain ⟨e, he, hxe⟩ := h1
    exact step_one hIH hG hx hpos he hxe
  have hle1 : ∀ e ∈ F, x e ≤ 1 := by
    intro e he
    rcases hG.2 e he with h | h
    · have := le_dsum (u := u) (v := v) hx.1 he (Or.inl rfl)
      rw [hx.2.2.1, h] at this; simpa using this
    · have := le_dsum (u := u) (v := v) hx.1 he (Or.inr rfl)
      rw [hx.2.2.1, h] at this; simpa using this
  have hlt : ∀ e ∈ F, x e < 1 := fun e he =>
    lt_of_le_of_ne (hle1 e he) (fun h => h1 ⟨e, he, h⟩)
  by_cases hFe : F = ∅
  · apply subset_convexHull
    exact ⟨fun e => Or.inl (hx.2.1 e (by simp [hFe])), hx.2.1, hx.2.2.1⟩
  obtain ⟨d, hd0, hdF, hdD⟩ :=
    deg_kernel hG hx hpos hlt (Finset.nonempty_iff_ne_empty.mpr hFe) hnt
  have hsum0 : ∑ e ∈ F, d e = 0 := by
    have h := sum_mul_dsum u v F hG.1 (fun _ => 1) d
    simp only [hdD, mul_zero, Finset.sum_const_zero] at h
    rw [← Finset.sum_mul] at h
    linarith
  have hzero : ∀ d' : E → ℝ, (∀ e ∉ F, d' e = 0) → ∑ e ∈ F, d' e = 0 → (∀ e, 0 ≤ d' e) →
      d' = 0 := by
    intro d' hd'F hs hnn
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hnn e)).mp hs
    funext e
    by_cases he : e ∈ F
    · exact this e he
    · exact hd'F e he
  have hneg : ∃ e, d e < 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hd0 (hzero d hdF hsum0 h)
  have hposd : ∃ e, (-d) e < 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    apply hd0
    have := hzero (-d) (fun e he => by simp [hdF e he])
      (by simp [Finset.sum_neg_distrib, hsum0]) h
    simpa using this
  have hdD' : ∀ w, dsum u v F (-d) w = 0 := fun w => by rw [dsum_neg, hdD, neg_zero]
  have htr : ∀ U : Finset V, Odd (∑ z ∈ U, b z) → ∑ e ∈ cut u v F U, x e = 1 →
      ∑ e ∈ cut u v F U, d e = 0 := fun U hU ht => rate_zero hG hx hpos hdD (hnt U hU ht)
  have htr' : ∀ U : Finset V, Odd (∑ z ∈ U, b z) → ∑ e ∈ cut u v F U, x e = 1 →
      ∑ e ∈ cut u v F U, (-d) e = 0 := fun U hU ht => by
    simp [Finset.sum_neg_distrib, htr U hU ht]
  obtain ⟨t1, ht1, hx1, hc1⟩ := line hx hpos hdF hdD hneg htr
  obtain ⟨t2, ht2, hx2, hc2⟩ :=
    line hx hpos (d := -d) (fun e he => by simp [hdF e he]) hdD' hposd htr'
  have hend : ∀ (s : ℝ) (d' : E → ℝ), x + s • d' ∈ PS u v F b → (∀ w, dsum u v F d' w = 0) →
      ((∃ e ∈ F, x e + s * d' e = 0) ∨ ∃ U : Finset V, Odd (∑ z ∈ U, b z) ∧
        ∑ e ∈ cut u v F U, (x e + s * d' e) = 1 ∧ ∑ e ∈ cut u v F U, d' e < 0) →
      x + s • d' ∈ convexHull ℝ (IS u v F b) := by
    intro s d' hmem hd'D hc
    apply hA _ hmem
    rcases hc with ⟨e, he, h⟩ | ⟨U, hU, ht, hneg'⟩
    · left; exact ⟨e, he, by simp [h]⟩
    · by_cases hz : ∃ e ∈ F, (x + s • d') e = 0
      · left; exact hz
      · right
        have hpos' : ∀ e ∈ F, 0 < (x + s • d') e := fun e he =>
          lt_of_le_of_ne (hmem.1 e) (fun h => hz ⟨e, he, h.symm⟩)
        refine ⟨U, hU, by simpa using ht, ?_⟩
        by_contra hnt'
        have htriv : ∑ z ∈ U, b z < 2 ∨ ∑ z ∈ Uᶜ, b z < 2 := by
          by_contra h'
          rw [not_or, not_lt, not_lt] at h'
          exact hnt' h'
        have := rate_zero hG hmem hpos' hd'D htriv
        linarith
  have hy1 := hend t1 d hx1 hdD hc1
  have hy2 := hend t2 (-d) hx2 hdD' hc2
  have hsum12 : 0 < t1 + t2 := add_pos ht1 ht2
  have hconv := (convex_convexHull ℝ (IS u v F b)) hy1 hy2
    (div_nonneg ht2.le hsum12.le) (div_nonneg ht1.le hsum12.le)
    (by rw [← add_div, add_comm, div_self hsum12.ne'])
  convert hconv using 1
  funext e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp
  ring

theorem thmA (n : ℕ) : ∀ (u v : E → V) (F : Finset E) (b : V → ℕ),
    F.card + ∑ z, b z = n → Good u v F b → PS u v F b ⊆ convexHull ℝ (IS u v F b) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v F b hn hG x hx
  have hIH : IHP F b := fun u' v' F' b' hlt hG' =>
    ih _ (hn ▸ hlt) u' v' F' b' rfl hG'
  exact main_step hIH hG hx

/-! ### The subdivision gadget -/

/-- First ends of the edges of the subdivided graph: edge `(e, i)` is the `i`-th of the three
edges of the path `u e — (e, false) — (e, true) — v e`. -/
def gu (u : E → V) (p : E × Fin 3) : V ⊕ (E × Bool) :=
  ![Sum.inl (u p.1), Sum.inr (p.1, false), Sum.inr (p.1, true)] p.2

/-- Second ends of the edges of the subdivided graph. -/
def gv (v : E → V) (p : E × Fin 3) : V ⊕ (E × Bool) :=
  ![Sum.inr (p.1, false), Sum.inr (p.1, true), Sum.inl (v p.1)] p.2

/-- Demands of the subdivided graph. -/
def gb (b : V → ℕ) : V ⊕ (E × Bool) → ℕ := Sum.elim b (fun _ => 1)

/-- The point of the subdivided graph corresponding to `y`. -/
def gy (y : E → ℝ) (p : E × Fin 3) : ℝ := ![y p.1, 1 - y p.1, y p.1] p.2

lemma sum_E3 (P : E × Fin 3 → Prop) [DecidablePred P] (g : E × Fin 3 → ℝ) :
    ∑ p ∈ univ.filter P, g p = ∑ e, ((if P (e, 0) then g (e, 0) else 0) +
      (if P (e, 1) then g (e, 1) else 0) + (if P (e, 2) then g (e, 2) else 0)) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_three]

omit [Fintype V] in
lemma gdsum_inl (u v : E → V) (z : E × Fin 3 → ℝ) (w : V) :
    dsum (gu u) (gv v) univ z (Sum.inl w) =
      ∑ e, ((if u e = w then z (e, 0) else 0) + (if v e = w then z (e, 2) else 0)) := by
  rw [dsum, sum_E3]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [gu, gv]

omit [Fintype V] in
lemma gdsum_inr0 (u v : E → V) (z : E × Fin 3 → ℝ) (e0 : E) :
    dsum (gu u) (gv v) univ z (Sum.inr (e0, false)) = z (e0, 0) + z (e0, 1) := by
  rw [dsum, sum_E3]
  simp [gu, gv, Finset.sum_add_distrib]

omit [Fintype V] in
lemma gdsum_inr1 (u v : E → V) (z : E × Fin 3 → ℝ) (e0 : E) :
    dsum (gu u) (gv v) univ z (Sum.inr (e0, true)) = z (e0, 1) + z (e0, 2) := by
  rw [dsum, sum_E3]
  simp [gu, gv, Finset.sum_add_distrib]

omit [Fintype V] in
lemma gcut_sum (u v : E → V) (z : E × Fin 3 → ℝ) (W : Finset (V ⊕ (E × Bool))) :
    ∑ p ∈ cut (gu u) (gv v) univ W, z p = ∑ e,
      ((if (Sum.inl (u e) ∈ W) ≠ (Sum.inr (e, false) ∈ W) then z (e, 0) else 0) +
       (if (Sum.inr (e, false) ∈ W) ≠ (Sum.inr (e, true) ∈ W) then z (e, 1) else 0) +
       (if (Sum.inr (e, true) ∈ W) ≠ (Sum.inl (v e) ∈ W) then z (e, 2) else 0)) := by
  rw [cut, sum_E3]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [gu, gv]

lemma gb_sum (b : V → ℕ) (W : Finset (V ⊕ (E × Bool))) :
    ∑ q ∈ W, gb b q = ∑ w ∈ univ.filter (fun w => Sum.inl w ∈ W), b w +
      ∑ e, ((if Sum.inr (e, false) ∈ W then 1 else 0) +
        (if Sum.inr (e, true) ∈ W then 1 else 0)) := by
  have h0 : ∑ q ∈ W, gb b q = ∑ q, if q ∈ W then gb b q else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h0, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fintype.sum_bool]
  simp only [gb, Sum.elim_inr]
  ring

omit [Fintype E] in
lemma gy_0 (y : E → ℝ) (e : E) : gy y (e, 0) = y e := rfl

omit [Fintype E] in
lemma gy_1 (y : E → ℝ) (e : E) : gy y (e, 1) = 1 - y e := rfl

omit [Fintype E] in
lemma gy_2 (y : E → ℝ) (e : E) : gy y (e, 2) = y e := rfl

lemma edge_c_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (α β γ δ : Prop) [Decidable α]
    [Decidable β] [Decidable γ] [Decidable δ] :
    0 ≤ (if α ≠ β then y else 0) + (if β ≠ γ then 1 - y else 0) + (if γ ≠ δ then y else 0) := by
  have h1 : 0 ≤ (if α ≠ β then y else 0) := by split_ifs <;> linarith
  have h2 : 0 ≤ (if β ≠ γ then 1 - y else 0) := by split_ifs <;> linarith
  have h3 : 0 ≤ (if γ ≠ δ then y else 0) := by split_ifs <;> linarith
  linarith

lemma edge_c_A (y : ℝ) (α β γ δ : Prop) [Decidable α] [Decidable β] [Decidable γ]
    [Decidable δ] (hαδ : α ↔ δ) (hβγ : β ≠ γ) :
    1 ≤ (if α ≠ β then y else 0) + (if β ≠ γ then 1 - y else 0) + (if γ ≠ δ then y else 0) := by
  by_cases hα : α <;> by_cases hβ : β <;> by_cases hγ : γ <;> by_cases hδ : δ <;>
    simp_all

lemma edge_c_B (y : ℝ) (hy0 : 0 ≤ y) (α β γ δ : Prop) [Decidable α] [Decidable β]
    [Decidable γ] [Decidable δ] (h : (α ↔ δ) → β = γ) :
    (if (α ≠ δ) ∧ ¬((α ≠ δ) ∧ (β ≠ γ)) then y else 0) +
      (if (α ≠ δ) ∧ (β ≠ γ) then 1 - y else 0) ≤
    (if α ≠ β then y else 0) + (if β ≠ γ then 1 - y else 0) + (if γ ≠ δ then y else 0) := by
  by_cases hα : α <;> by_cases hβ : β <;> by_cases hγ : γ <;> by_cases hδ : δ <;>
    simp_all <;> linarith

lemma edge_par (α β γ δ : Prop) [Decidable α] [Decidable β] [Decidable γ] [Decidable δ]
    (h : (α ↔ δ) → β = γ) :
    (if β then 1 else 0) + (if γ then 1 else 0) =
      (if (α ≠ δ) ∧ (β ≠ γ) then 1 else 0) + 2 * (if β ∧ γ then (1 : ℕ) else 0) := by
  by_cases hα : α <;> by_cases hβ : β <;> by_cases hγ : γ <;> by_cases hδ : δ <;>
    simp_all

lemma gb_sum' (b : V → ℕ) (W : Finset (V ⊕ (E × Bool))) (U : Finset V)
    (hU : ∀ w, w ∈ U ↔ Sum.inl w ∈ W) :
    ∑ q ∈ W, gb b q = ∑ w ∈ U, b w + ∑ e, ((if Sum.inr (e, false) ∈ W then 1 else 0) +
      (if Sum.inr (e, true) ∈ W then 1 else 0)) := by
  rw [gb_sum]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext w; simp [hU]

omit [Fintype V] in
lemma g_good (u v : E → V) (b : V → ℕ) : Good (gu u) (gv v) univ (gb b) := by
  refine ⟨fun p _ => ?_, fun p _ => ?_⟩
  · obtain ⟨e, i⟩ := p
    fin_cases i <;> simp [gu, gv]
  · obtain ⟨e, i⟩ := p
    fin_cases i <;> simp [gu, gv, gb]

omit [Fintype E] in
lemma gy_nonneg {y : E → ℝ} (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1) (p : E × Fin 3) : 0 ≤ gy y p := by
  obtain ⟨e, i⟩ := p
  fin_cases i
  · exact (hy e).1
  · show 0 ≤ 1 - y e; linarith [(hy e).2]
  · exact (hy e).1

lemma gy_odd (u v : E → V) (b : V → ℕ) (y : E → ℝ) (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hbl : ∀ (U : Finset V) (J : Finset E), (∀ e ∈ J, (u e ∈ U) ≠ (v e ∈ U)) →
      Odd (∑ x ∈ U, b x + J.card) →
      1 ≤ ∑ e ∈ univ.filter (fun e => (u e ∈ U) ≠ (v e ∈ U) ∧ e ∉ J), y e +
        ∑ e ∈ J, (1 - y e))
    (W : Finset (V ⊕ (E × Bool))) (hW : Odd (∑ q ∈ W, gb b q)) :
    1 ≤ ∑ p ∈ cut (gu u) (gv v) univ W, gy y p := by
  set U : Finset V := univ.filter (fun w => Sum.inl w ∈ W) with hUdef
  have hmemU : ∀ w, w ∈ U ↔ Sum.inl w ∈ W := fun w => by simp [hUdef]
  rw [gb_sum' b W U hmemU] at hW
  rw [gcut_sum]
  simp only [gy_0, gy_1, gy_2]
  by_cases hA : ∃ e, ((Sum.inl (u e) ∈ W) ↔ (Sum.inl (v e) ∈ W)) ∧
      (Sum.inr (e, false) ∈ W) ≠ (Sum.inr (e, true) ∈ W)
  · obtain ⟨e, h1, h2⟩ := hA
    refine le_trans ?_ (Finset.single_le_sum (fun e' _ => ?_) (Finset.mem_univ e))
    · exact edge_c_A (y e) _ _ _ _ h1 h2
    · exact edge_c_nonneg (y e') (hy e').1 (hy e').2 _ _ _ _
  · have hB : ∀ e, ((Sum.inl (u e) ∈ W) ↔ (Sum.inl (v e) ∈ W)) →
        (Sum.inr (e, false) ∈ W) = (Sum.inr (e, true) ∈ W) := by
      intro e h; by_contra h'; exact hA ⟨e, h, h'⟩
    set J : Finset E := univ.filter (fun e => (u e ∈ U) ≠ (v e ∈ U) ∧
      (Sum.inr (e, false) ∈ W) ≠ (Sum.inr (e, true) ∈ W)) with hJdef
    have hJ : ∀ e ∈ J, (u e ∈ U) ≠ (v e ∈ U) := fun e he => (Finset.mem_filter.mp he).2.1
    have hpar : Odd (∑ x ∈ U, b x + J.card) := by
      have hsplit : ∑ e, ((if Sum.inr (e, false) ∈ W then 1 else 0) +
          (if Sum.inr (e, true) ∈ W then 1 else 0)) = J.card + 2 * ∑ e,
          (if Sum.inr (e, false) ∈ W ∧ Sum.inr (e, true) ∈ W then (1 : ℕ) else 0) := by
        rw [Finset.card_eq_sum_ones, hJdef, Finset.sum_filter, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        have := edge_par _ _ _ _ (hB e)
        simp only [hmemU]
        exact this
      rw [hsplit] at hW
      rw [Nat.odd_iff] at hW ⊢
      omega
    refine le_trans (hbl U J hJ hpar) ?_
    rw [Finset.sum_filter, hJdef, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    simp only [hmemU, Finset.mem_filter, Finset.mem_univ, true_and]
    exact edge_c_B (y e) (hy e).1 _ _ _ _ (hB e)

/-- The theorem with classical decidability instances. -/
theorem core
    (u v : E → V) (hloop : ∀ e, u e ≠ v e) (b : V → ℕ) (y : E → ℝ)
    (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hdeg : ∀ x, ∑ e ∈ univ.filter (fun e => u e = x ∨ v e = x), y e = b x)
    (hblossom : ∀ (U : Finset V) (J : Finset E), (∀ e ∈ J, (u e ∈ U) ≠ (v e ∈ U)) →
      Odd (∑ x ∈ U, b x + J.card) →
      1 ≤ ∑ e ∈ univ.filter (fun e => (u e ∈ U) ≠ (v e ∈ U) ∧ e ∉ J), y e +
        ∑ e ∈ J, (1 - y e)) :
    y ∈ convexHull ℝ {z : E → ℝ | (∀ e, z e = 0 ∨ z e = 1) ∧
      ∀ x, ∑ e ∈ univ.filter (fun e => u e = x ∨ v e = x), z e = b x} := by
  have hPS : gy y ∈ PS (gu u) (gv v) univ (gb b) := by
    refine ⟨gy_nonneg hy, fun p hp => absurd (Finset.mem_univ p) hp, fun q => ?_,
      fun W hW => gy_odd u v b y hy hblossom W hW⟩
    rcases q with w | ⟨e0, s⟩
    · rw [gdsum_inl]
      simp only [gb, Sum.elim_inl]
      rw [← hdeg w, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [gy_0, gy_2]
      by_cases h1 : u e = w <;> by_cases h2 : v e = w
      · exact absurd (h1.trans h2.symm) (hloop e)
      all_goals simp [h1, h2]
    · cases s
      · rw [gdsum_inr0, gy_0, gy_1]; simp [gb]
      · rw [gdsum_inr1, gy_1, gy_2]; simp [gb]
  have hconv := thmA _ (gu u) (gv v) univ (gb b) rfl
    (g_good u v b) hPS
  let π : (E × Fin 3 → ℝ) →ₗ[ℝ] (E → ℝ) := LinearMap.funLeft ℝ ℝ (fun e => (e, (0 : Fin 3)))
  have hπ : π (gy y) = y := rfl
  rw [← hπ]
  have h1 : π (gy y) ∈
      π '' convexHull ℝ (IS (gu u) (gv v) univ (gb b)) :=
    Set.mem_image_of_mem _ hconv
  rw [LinearMap.image_convexHull] at h1
  refine convexHull_mono ?_ h1
  rintro _ ⟨z, hz, rfl⟩
  have hz20 : ∀ e, z (e, 2) = z (e, 0) := by
    intro e
    have h0 := hz.2.2 (Sum.inr (e, false))
    have h1 := hz.2.2 (Sum.inr (e, true))
    rw [gdsum_inr0] at h0
    rw [gdsum_inr1] at h1
    simp only [gb, Sum.elim_inr, Nat.cast_one] at h0 h1
    linarith
  refine ⟨fun e => hz.1 (e, 0), fun w => ?_⟩
  have h := hz.2.2 (Sum.inl w)
  rw [gdsum_inl] at h
  simp only [gb, Sum.elim_inl] at h
  rw [← h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hπe : π z e = z (e, 0) := rfl
  rw [hπe, hz20 e]
  by_cases h1 : u e = w <;> by_cases h2 : v e = w
  · exact absurd (h1.trans h2.symm) (hloop e)
  all_goals simp [h1, h2]

end BMatch

open Classical in
/-- **Capacitated b-matching polytope.** For a loopless multigraph with edge ends `u e ≠ v e` and
a demand `b : V → ℕ`, the convex hull of the edge sets with degree `b_v` at every vertex consists
of the vectors `y` with the degree equations, `0 ≤ y ≤ 1`, and the blossom inequalities (4.1):
`y(δ(U) \ J) + (1 - y)(J) ≥ 1` whenever `J ⊆ δ(U)` and `b(U) + |J|` is odd. -/
theorem bmatching_polytope {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (u v : E → V) (hloop : ∀ e, u e ≠ v e) (b : V → ℕ) (y : E → ℝ)
    (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hdeg : ∀ x, ∑ e ∈ univ.filter (fun e => u e = x ∨ v e = x), y e = b x)
    (hblossom : ∀ (U : Finset V) (J : Finset E), (∀ e ∈ J, (u e ∈ U) ≠ (v e ∈ U)) →
      Odd (∑ x ∈ U, b x + J.card) →
      1 ≤ ∑ e ∈ univ.filter (fun e => (u e ∈ U) ≠ (v e ∈ U) ∧ e ∉ J), y e +
        ∑ e ∈ J, (1 - y e)) :
    y ∈ convexHull ℝ {z : E → ℝ | (∀ e, z e = 0 ∨ z e = 1) ∧
      ∀ x, ∑ e ∈ univ.filter (fun e => u e = x ∨ v e = x), z e = b x} := by
  have h := BMatch.core u v hloop b y hy ?_ ?_
  · convert h
  · intro x; convert hdeg x
  · intro U J hJ hodd; convert hblossom U J hJ hodd

end Lovasz
