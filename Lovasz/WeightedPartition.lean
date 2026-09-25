/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Allocation
import Lovasz.SignedIntegrality
import Lovasz.SwapRounding
import Lovasz.TraceConcentration
import Lovasz.Chernoff
import Lovasz.Perturbation

/-!
# Proposition 5.3: the weighted partition

DAG node `P5.3` of `docs/BLUEPRINT.md` (Sections 5.2–5.3 of the paper). Its proof uses the
translate cover (5.2) (Chernoff bounds), Lemma 5.2, Lemmas 4.1–4.3 and the positive-part bound
(2.3)–(2.4).

The helpers live in the namespace `Lovasz.WP` and follow the paper:

* `translate_cover` (5.2); the fractional allocation `wG`, `xG`, `πG` with the identities (5.4)
  (`sum_xG_eq_one`, `xG_balance`) and the bounds (5.5) (`Standing.πG_bounds`);
* the signed incidence system `Γ` of §5.2 (auxiliary coset nodes in the odd case), its parity
  (`parity`) and slack-cut (`slack`, via `slack_split` = Lemma 5.2 and `slack_shore`)
  conditions; `rounding_exists` applies Lemmas 4.1 and 4.2;
* independent rounding in the cosets, realized as a product of independent copies of one rounding
  law, the variables of a coset being read from its own copy (`glue`, `alloc`); the law (5.7)
  of the reserved vertices (`reservation_law`, `reservation_product`);
* the weights (5.8)–(5.10) (`aG`, `Dref`, `Standing.aG_bounds`, `Standing.aG_mean`);
* the scalar events (5.11) (`prob_size`, `prob_deg`, `prob_nbhd`, from Lemma 4.3 with `1 × 1`
  matrices) and the spectral event (5.13)–(5.14) (`prob_gap`, from Lemma 4.3 with the matrices
  built from the positive part `posPart_factor` of `B - uuᵀ`);
* the deterministic part `good_of_copies`; the gap of `H_i` is obtained from (5.12) in the
  variational form (2.1), testing with the unweighted mean over `V_i` (`gapOK_of_event`,
  `hasGap_of_quad`), which replaces the interlacing and reference-degree perturbation;
* the numerical bookkeeping `numeric_choice` and the assembly `Lovasz.weighted_partition`.
-/

universe u

noncomputable section

namespace Lovasz

open Finset

namespace WP

/-! ## Finite distributions -/

section Dist

variable {α β : Type*}

open Classical in
/-- Push-forward of a finite distribution. -/
def pushDist (f : α → β) (μ : FinDist α) : FinDist β where
  support := μ.support.image f
  prob b := ∑ a ∈ μ.support with f a = b, μ.prob a
  prob_nonneg b := sum_nonneg fun a _ => μ.prob_nonneg a
  sum_prob := by
    rw [sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha)]
    exact μ.sum_prob

theorem P_pushDist (f : α → β) (μ : FinDist α) (E : β → Prop) :
    (pushDist f μ).P E = μ.P (fun a => E (f a)) := by
  classical
  simp only [FinDist.P, pushDist]
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha)
    (fun a => if E (f a) then μ.prob a else 0)]
  refine sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · refine sum_congr rfl fun a ha => ?_
    rw [(mem_filter.1 ha).2, ite_eq_left hb]
  · symm; refine sum_eq_zero fun a ha => ?_
    rw [(mem_filter.1 ha).2, ite_eq_right hb]

theorem P_nonneg (μ : FinDist α) (E : α → Prop) : 0 ≤ μ.P E := by
  classical
  unfold FinDist.P
  exact sum_nonneg fun a _ => by split_ifs <;> simp [μ.prob_nonneg]

theorem P_mono (μ : FinDist α) {E F : α → Prop} (h : ∀ a ∈ μ.support, E a → F a) :
    μ.P E ≤ μ.P F := by
  classical
  unfold FinDist.P
  refine sum_le_sum fun a ha => ?_
  by_cases hE : E a
  · rw [ite_eq_left hE, ite_eq_left (h a ha hE)]
  · rw [ite_eq_right hE]; split_ifs <;> simp [μ.prob_nonneg]

theorem P_or_le (μ : FinDist α) (E F : α → Prop) :
    μ.P (fun a => E a ∨ F a) ≤ μ.P E + μ.P F := by
  classical
  unfold FinDist.P
  rw [← sum_add_distrib]
  refine sum_le_sum fun a _ => ?_
  have := μ.prob_nonneg a
  split_ifs <;> simp_all

theorem P_exists_le {ι : Type*} (s : Finset ι) (μ : FinDist α) (E : ι → α → Prop) :
    μ.P (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, μ.P (E i) := by
  classical
  unfold FinDist.P
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  have hp := μ.prob_nonneg a
  split_ifs with h
  · obtain ⟨i, hi, hE⟩ := h
    calc μ.prob a = if E i a then μ.prob a else 0 := by rw [ite_eq_left hE]
      _ ≤ ∑ j ∈ s, if E j a then μ.prob a else 0 :=
        single_le_sum (f := fun j => if E j a then μ.prob a else 0)
          (fun j _ => by split_ifs <;> simp [hp]) hi
  · exact sum_nonneg fun j _ => by split_ifs <;> simp [hp]

theorem P_true (μ : FinDist α) : μ.P (fun _ => True) = 1 := by
  classical
  simp [FinDist.P, μ.sum_prob]

theorem pi_P_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist α)
    (E : ι → α → Prop) :
    (FinDist.pi μ).P (fun x => ∀ i, E i (x i)) = ∏ i, (μ i).P (E i) := by
  classical
  simp only [FinDist.P, FinDist.pi]
  rw [prod_univ_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [prod_ite_zero]
  simp

theorem pi_P_eval {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist α) (k : ι)
    (E : α → Prop) : (FinDist.pi μ).P (fun x => E (x k)) = (μ k).P E := by
  classical
  have h := pi_P_forall μ (fun i a => i = k → E a)
  have e1 : (fun x : ι → α => ∀ i, i = k → E (x i)) = fun x => E (x k) := by
    funext x; apply propext; constructor
    · intro h; exact h k rfl
    · rintro h i rfl; exact h
  rw [e1] at h
  rw [h]
  have e2 : ∀ i, (μ i).P (fun a => i = k → E a) = if i = k then (μ k).P E else 1 := by
    intro i
    split_ifs with hi
    · subst hi; congr 1; funext a; apply propext; simp
    · rw [← P_true (μ i)]; congr 1; funext a; apply propext; simp [hi]
  simp only [e2]
  rw [prod_ite_eq']
  simp

theorem mem_pi_support {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist α)
    (x : ι → α) : x ∈ (FinDist.pi μ).support ↔ ∀ i, x i ∈ (μ i).support := by
  simp [FinDist.pi]

theorem sum01_eq_card {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h01 : ∀ i ∈ s, f i = 0 ∨ f i = 1) :
    ∑ i ∈ s, f i = (s.filter fun i => f i = 1).card := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun i hi => ?_
  rcases h01 i hi with h | h <;> simp [h]

end Dist

/-! ## The template and the translate cover (5.2) -/

section Setup

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/-- `u = |⟨T⟩|`. -/
def uu (T : Finset G) : ℕ := Nat.card (Subgroup.closure (T : Set G))

/-- `θ` of (5.6): `1 - 1/u` if `u` is odd, `1` otherwise. -/
def θ (T : Finset G) : ℝ := if Odd (uu T) then 1 - 1 / (uu T : ℝ) else 1

variable (T Ap Am : Finset G) {t : ℕ} (g : Fin t → G)

open Classical in
/-- `c_e` for the physical edge `{x, xs}`: the number of selected copies containing it. -/
def occ (x s : G) : ℕ := (univ.filter fun i : Fin t =>
    (templateGraph T Ap Am).Adj ((g i)⁻¹ * x) ((g i)⁻¹ * (x * s))).card

/-- The conclusion of the Chernoff step (5.2) for the selected copies `g i • F`: every vertex
lies in at most `2λ` copies and every `T`-edge of class `s` in between `λ f_s / 2` and `2λ f_s`
copies. -/
structure CoverOK (lam : ℝ) : Prop where
  mult : ∀ v, (((univ : Finset (Fin t)).filter fun i => v ∈ copyVerts Ap Am (g i)).card : ℝ) ≤
    2 * lam
  occ_lower : ∀ x, ∀ s ∈ T, lam * labelDensity T Ap Am s / 2 ≤ occ T Ap Am g x s
  occ_upper : ∀ x, ∀ s ∈ T, (occ T Ap Am g x s : ℝ) ≤ 2 * lam * labelDensity T Ap Am s

/-- `R = d(F) = ∑_{s ∈ T} f_s`. -/
def Rsum : ℝ := ∑ s ∈ T, labelDensity T Ap Am s

open Classical in
/-- The weight `w_{i,e} = f_s / c_e` of the occurrence in `F_i` of the edge `e = {x, y}` of
class `s = x⁻¹ y` (zero if `xy` is not an edge of `F_i`). -/
def wG (i : Fin t) (x y : G) : ℝ :=
  if (copyGraph T Ap Am (g i)).Adj x y then
    labelDensity T Ap Am (x⁻¹ * y) / occ T Ap Am g x (x⁻¹ * y) else 0

/-- `x_{v,i}` of (5.3). -/
def xG (i : Fin t) (x : G) : ℝ := (∑ y, wG T Ap Am g i x y) / Rsum T Ap Am

/-- `π_{v,i} = θ x_{v,i}` of (5.6). -/
def πG (i : Fin t) (x : G) : ℝ := θ T * xG T Ap Am g i x

/-- The weights (5.8) `a_{i,uv} = κρ w_{i,uv} / (π_{u,i} π_{v,i})`, `ρ = 1/λ`. -/
def aG (κ lam : ℝ) (i : Fin t) (x y : G) : ℝ :=
  κ / lam * wG T Ap Am g i x y / (πG T Ap Am g i x * πG T Ap Am g i y)

/-- The reference degree `D = κρR/θ` of (5.8). -/
def Dref (κ lam : ℝ) : ℝ := κ / lam * Rsum T Ap Am / θ T

/-- Standing hypotheses of Sections 5.2–5.3 for a fixed translate cover: the template (5.1)
with constant `c ≤ 1`, the cover (5.2), `λ ≥ 64` (so all coordinates are below `1/2`), and
`6λ ≤ c² d` (so that the cut slack `Ω(ρd)` of Lemma 5.2 exceeds one). -/
structure Standing (S : Finset G) (c lam : ℝ) : Prop where
  conn : IsConnectionSet S
  temp : IsTemplate S T Ap Am c
  c_pos : 0 < c
  c_le : c ≤ 1
  cover : CoverOK T Ap Am g lam
  lam_ge : 64 ≤ lam
  slack : 6 * lam ≤ c ^ 2 * S.card
  logn_ge : 1 ≤ Real.log (Fintype.card G)

end Setup

/-! ## Basic facts on the template and the fractional allocation (5.3)–(5.5) -/

section Basic

open Classical

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G}

theorem mem_copyVerts {h v : G} : v ∈ copyVerts Ap Am h ↔ h⁻¹ * v ∈ Ap ∪ Am := by
  unfold copyVerts
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    simpa using ha
  · intro hv
    exact mem_image.2 ⟨_, hv, by simp⟩

theorem card_copyVerts (h : G) : (copyVerts Ap Am h).card = (Ap ∪ Am).card :=
  card_image_of_injective _ (mul_right_injective h)

theorem templateGraph_mem {a b : G} (h : (templateGraph T Ap Am).Adj a b) :
    a ∈ Ap ∪ Am ∧ b ∈ Ap ∪ Am := by
  rcases h.2.1 with h' | h'
  · exact ⟨mem_union_left _ h'.1, mem_union_right _ h'.2⟩
  · exact ⟨mem_union_right _ h'.1, mem_union_left _ h'.2⟩

theorem templateGraph_label (hT : ∀ s ∈ T, s⁻¹ ∈ T) {a b : G}
    (h : (templateGraph T Ap Am).Adj a b) : a⁻¹ * b ∈ T := by
  rcases h.2.2 with h' | h'
  · exact h'
  · simpa using hT _ h'

theorem copyAdj_iff {i : Fin t} {x y : G} :
    (copyGraph T Ap Am (g i)).Adj x y ↔ (templateGraph T Ap Am).Adj ((g i)⁻¹ * x) ((g i)⁻¹ * y) :=
  Iff.rfl

theorem copyAdj_label (hT : ∀ s ∈ T, s⁻¹ ∈ T) {i : Fin t} {x y : G}
    (h : (copyGraph T Ap Am (g i)).Adj x y) : x⁻¹ * y ∈ T := by
  have := templateGraph_label hT h
  simpa [mul_assoc] using this

theorem copyAdj_mem {i : Fin t} {x y : G} (h : (copyGraph T Ap Am (g i)).Adj x y) :
    x ∈ copyVerts Ap Am (g i) ∧ y ∈ copyVerts Ap Am (g i) := by
  have := templateGraph_mem h
  exact ⟨mem_copyVerts.2 this.1, mem_copyVerts.2 this.2⟩

theorem labelDensity_nonneg (s : G) : 0 ≤ labelDensity T Ap Am s := by
  unfold labelDensity; positivity

theorem labelDensity_le_one (s : G) : labelDensity T Ap Am s ≤ 1 := by
  classical
  unfold labelDensity
  rcases Nat.eq_zero_or_pos (Ap ∪ Am).card with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_filter_le _ _

theorem labelDensity_inv (s : G) : labelDensity T Ap Am s⁻¹ = labelDensity T Ap Am s := by
  unfold labelDensity
  congr 2
  refine card_nbij' (fun a => a * s⁻¹) (fun b => b * s) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, Set.mem_ofPred_eq] at ha ⊢
    have h2 := (templateGraph_mem ha.2).2
    refine ⟨h2, ?_⟩
    simpa using ha.2.symm
  · intro b hb
    simp only [coe_filter, Set.mem_ofPred_eq] at hb ⊢
    have h2 := (templateGraph_mem hb.2).2
    refine ⟨h2, ?_⟩
    simpa using hb.2.symm
  · intro a _; simp
  · intro b _; simp

theorem uu_pos (T : Finset G) : 0 < uu T := Nat.card_pos

theorem uu_ge_two (h1 : (1 : G) ∉ T) (hne : T.Nonempty) : 2 ≤ uu T := by
  obtain ⟨s, hs⟩ := hne
  have : 1 < uu T := by
    unfold uu
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hmem : s ∈ Subgroup.closure (T : Set G) := Subgroup.subset_closure hs
    rw [hbot, Subgroup.mem_bot] at hmem
    exact h1 (hmem ▸ hs)
  omega

theorem θ_nonneg (T : Finset G) : 0 ≤ θ T := by
  unfold θ
  split_ifs
  · have : (1 : ℝ) ≤ uu T := by exact_mod_cast uu_pos T
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  · norm_num

theorem θ_le_one (T : Finset G) : θ T ≤ 1 := by
  unfold θ
  split_ifs
  · have : (0 : ℝ) < uu T := by exact_mod_cast uu_pos T
    have : 0 ≤ 1 / (uu T : ℝ) := by positivity
    linarith
  · norm_num

theorem θ_ge (h2 : 2 ≤ uu T) : 2 / 3 ≤ θ T := by
  unfold θ
  split_ifs with hodd
  · have h3 : 3 ≤ uu T := by
      rcases hodd with ⟨k, hk⟩; omega
    have : (3 : ℝ) ≤ uu T := by exact_mod_cast h3
    have : 1 / (uu T : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  · norm_num


theorem wG_self (i : Fin t) (x : G) : wG T Ap Am g i x x = 0 := by
  unfold wG
  rw [ite_eq_right]
  exact (copyGraph T Ap Am (g i)).loopless.irrefl x

theorem wG_nonneg (i : Fin t) (x y : G) : 0 ≤ wG T Ap Am g i x y := by
  unfold wG
  split_ifs
  · exact div_nonneg (labelDensity_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem occ_symm (x y : G) :
    occ T Ap Am g y (y⁻¹ * x) = occ T Ap Am g x (x⁻¹ * y) := by
  unfold occ
  congr 1
  refine filter_congr fun i _ => ?_
  simp only [mul_inv_cancel_left]
  exact (templateGraph T Ap Am).adj_comm _ _

theorem wG_symm (i : Fin t) (x y : G) : wG T Ap Am g i x y = wG T Ap Am g i y x := by
  unfold wG
  by_cases hxy : (copyGraph T Ap Am (g i)).Adj x y
  · rw [ite_eq_left hxy, ite_eq_left hxy.symm, occ_symm]
    congr 1
    rw [show y⁻¹ * x = (x⁻¹ * y)⁻¹ by group, labelDensity_inv]
  · have hyx : ¬ (copyGraph T Ap Am (g i)).Adj y x := fun h => hxy h.symm
    rw [ite_eq_right hxy, ite_eq_right hyx]

theorem Rsum_nonneg : 0 ≤ Rsum T Ap Am := sum_nonneg fun s _ => labelDensity_nonneg s

theorem xG_nonneg (i : Fin t) (x : G) : 0 ≤ xG T Ap Am g i x :=
  div_nonneg (sum_nonneg fun y _ => wG_nonneg i x y) Rsum_nonneg

theorem πG_nonneg (i : Fin t) (x : G) : 0 ≤ πG T Ap Am g i x :=
  mul_nonneg (θ_nonneg T) (xG_nonneg i x)

theorem wG_eq_zero {i : Fin t} {x y : G} (h : ¬ (copyGraph T Ap Am (g i)).Adj x y) :
    wG T Ap Am g i x y = 0 := by
  unfold wG; rw [ite_eq_right h]

theorem xG_eq_zero {i : Fin t} {x : G} (hx : x ∉ copyVerts Ap Am (g i)) :
    xG T Ap Am g i x = 0 := by
  unfold xG
  rw [sum_eq_zero fun y _ => wG_eq_zero fun h => hx (copyAdj_mem h).1, zero_div]

theorem πG_eq_zero {i : Fin t} {x : G} (hx : x ∉ copyVerts Ap Am (g i)) :
    πG T Ap Am g i x = 0 := by
  unfold πG; rw [xG_eq_zero hx, mul_zero]

/-- Neighbourhood count in the template as a finset. -/
theorem ncard_neighborSet (a : G) :
    ((templateGraph T Ap Am).neighborSet a).ncard =
      (univ.filter fun b => (templateGraph T Ap Am).Adj a b).card := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext b; simp

theorem IsTemplate.mono {c c' : ℝ} (h : IsTemplate S T Ap Am c) (_hc' : 0 ≤ c') (hcc : c' ≤ c) :
    IsTemplate S T Ap Am c' where
  sub := h.sub
  symm := h.symm
  disjoint := h.disjoint
  connected := h.connected
  deg_lower v hv := le_trans (mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg _)) (h.deg_lower v hv)
  gap f := by
    obtain ⟨z, hz⟩ := h.gap f
    refine ⟨z, le_trans ?_ hz⟩
    apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcc (sq_nonneg _))
    exact sum_nonneg fun x _ => mul_nonneg (sum_nonneg fun y _ => WGraph.nonneg _ _ _) (sq_nonneg _)
  density := h.density
  card_T := le_trans (mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg _)) h.card_T

theorem card_VF {c : ℝ} (_hc : 0 ≤ c) (htemp : IsTemplate S T Ap Am c) :
    (Ap ∪ Am).Nonempty ∧ c * S.card ≤ (Ap ∪ Am).card ∧ (Ap ∪ Am).card ≤ Fintype.card G := by
  obtain ⟨⟨a, ha⟩⟩ := htemp.connected.nonempty
  have ha' : a ∈ Ap ∪ Am := by simpa using ha
  refine ⟨⟨a, ha'⟩, ?_, card_le_univ _⟩
  refine le_trans (htemp.deg_lower a ha') ?_
  rw [ncard_neighborSet]
  exact_mod_cast card_le_card fun b hb => (templateGraph_mem (mem_filter.1 hb).2).2

theorem template_coset
    (hF : ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Connected) :
    ∀ a ∈ Ap ∪ Am, ∀ b ∈ Ap ∪ Am, a⁻¹ * b ∈ Subgroup.closure (T : Set G) := by
  have htemp : ∀ a b : G, (templateGraph T Ap Am).Adj a b →
      a⁻¹ * b ∈ Subgroup.closure (T : Set G) := by
    intro a b h
    rcases h.2.2 with h' | h'
    · exact Subgroup.subset_closure h'
    · have := inv_mem (Subgroup.subset_closure h' : b⁻¹ * a ∈ Subgroup.closure (T : Set G))
      simpa using this
  intro a ha
  have key : ∀ w : ↥((Ap ∪ Am : Finset G) : Set G),
      ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Reachable ⟨a, ha⟩ w →
        a⁻¹ * w.1 ∈ Subgroup.closure (T : Set G) := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => simp
    | tail _ hadj ih =>
      rename_i c d _
      have h2 := htemp _ _ hadj
      rw [show a⁻¹ * d.1 = (a⁻¹ * c.1) * (c.1⁻¹ * d.1) by group]
      exact mul_mem ih h2
  intro b hb
  exact key ⟨b, hb⟩ (hF.preconnected _ _)

/-- All vertices of the copy `g_i F` lie in the left coset `g_i a₀ U`. -/
theorem copy_coset
    (hF : ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Connected)
    {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am) {i : Fin t} {v : G} (hv : v ∈ copyVerts Ap Am (g i)) :
    (QuotientGroup.mk (g i * a₀) : G ⧸ Subgroup.closure (T : Set G)) = QuotientGroup.mk v := by
  rw [QuotientGroup.eq]
  have := template_coset hF a₀ ha₀ _ (mem_copyVerts.1 hv)
  simpa [mul_assoc] using this

theorem deg_le_card_T (hT : ∀ s ∈ T, s⁻¹ ∈ T) (a : G) :
    (univ.filter fun b => (templateGraph T Ap Am).Adj a b).card ≤ T.card := by
  refine card_le_card_of_injOn (fun b => a⁻¹ * b) ?_ ?_
  · intro b hb
    exact templateGraph_label hT (mem_filter.1 hb).2
  · intro b _ b' _ h
    simpa using h

variable {c lam : ℝ}

theorem Standing.d_pos (hst : Standing T Ap Am g S c lam) : 0 < (S.card : ℝ) := by
  have := hst.slack; have := hst.lam_ge; have := hst.c_pos
  by_contra h
  push Not at h
  nlinarith [sq_nonneg c]

theorem Standing.lam_pos (hst : Standing T Ap Am g S c lam) : 0 < lam := by
  linarith [hst.lam_ge]

theorem Standing.T_le_S (hst : Standing T Ap Am g S c lam) : (T.card : ℝ) ≤ S.card := by
  exact_mod_cast card_le_card hst.temp.sub

theorem Standing.T_pos (hst : Standing T Ap Am g S c lam) : 0 < (T.card : ℝ) :=
  lt_of_lt_of_le (mul_pos hst.c_pos hst.d_pos) hst.temp.card_T

theorem Standing.one_notMem (hst : Standing T Ap Am g S c lam) : (1 : G) ∉ T :=
  fun h => hst.conn.2 (hst.temp.sub h)

theorem Standing.uu_ge_two (hst : Standing T Ap Am g S c lam) : 2 ≤ uu T :=
  WP.uu_ge_two hst.one_notMem (card_pos.1 (by exact_mod_cast hst.T_pos))

theorem Standing.θ_ge (hst : Standing T Ap Am g S c lam) : 2 / 3 ≤ θ T :=
  WP.θ_ge hst.uu_ge_two

theorem Standing.Rsum_bounds (hst : Standing T Ap Am g S c lam) :
    (T.card : ℝ) / 8 ≤ Rsum T Ap Am ∧ Rsum T Ap Am ≤ T.card := by
  unfold Rsum
  constructor
  · have := card_nsmul_le_sum T (fun s => labelDensity T Ap Am s) (1 / 8) hst.temp.density
    simp only [nsmul_eq_mul] at this
    linarith
  · have := sum_le_card_nsmul T (fun s => labelDensity T Ap Am s) 1
      (fun s _ => labelDensity_le_one s)
    simpa using this

theorem Standing.Rsum_pos (hst : Standing T Ap Am g S c lam) : 0 < Rsum T Ap Am := by
  have := hst.Rsum_bounds.1; have := hst.T_pos; linarith

theorem Standing.wG_bounds (hst : Standing T Ap Am g S c lam) {i : Fin t} {x y : G}
    (h : (copyGraph T Ap Am (g i)).Adj x y) :
    1 / (2 * lam) ≤ wG T Ap Am g i x y ∧ wG T Ap Am g i x y ≤ 2 / lam := by
  have hs := copyAdj_label hst.temp.symm h
  have hf := hst.temp.density _ hs
  have hlo := hst.cover.occ_lower x _ hs
  have hhi := hst.cover.occ_upper x _ hs
  have hlam := hst.lam_pos
  unfold wG
  rw [ite_eq_left h]
  set f := labelDensity T Ap Am (x⁻¹ * y)
  set o : ℝ := (occ T Ap Am g x (x⁻¹ * y) : ℝ)
  have hf0 : 0 < f := by linarith
  have ho : 0 < o := lt_of_lt_of_le (by positivity) hlo
  constructor
  · rw [div_le_div_iff₀ (by positivity) ho]; nlinarith
  · rw [div_le_div_iff₀ ho hlam]; nlinarith

theorem Standing.copy_deg (hst : Standing T Ap Am g S c lam) {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    c * S.card ≤ (univ.filter fun y => (copyGraph T Ap Am (g i)).Adj x y).card ∧
      ((univ.filter fun y => (copyGraph T Ap Am (g i)).Adj x y).card : ℝ) ≤ T.card := by
  have hcard : (univ.filter fun y => (copyGraph T Ap Am (g i)).Adj x y).card =
      (univ.filter fun b => (templateGraph T Ap Am).Adj ((g i)⁻¹ * x) b).card := by
    refine card_nbij' (fun y => (g i)⁻¹ * y) (fun b => g i * b) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      exact hy
    · intro b hb
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      show (templateGraph T Ap Am).Adj ((g i)⁻¹ * x) ((g i)⁻¹ * (g i * b))
      simpa using hb
    · intro y _; simp
    · intro b _; simp
  rw [hcard]
  constructor
  · have := hst.temp.deg_lower _ (mem_copyVerts.1 hx)
    rwa [ncard_neighborSet] at this
  · exact_mod_cast deg_le_card_T hst.temp.symm _

theorem Standing.sumwG_bounds (hst : Standing T Ap Am g S c lam) {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    c * S.card / (2 * lam) ≤ ∑ y, wG T Ap Am g i x y ∧
      ∑ y, wG T Ap Am g i x y ≤ 2 * T.card / lam := by
  classical
  set N := univ.filter fun y => (copyGraph T Ap Am (g i)).Adj x y
  have hsum : ∑ y, wG T Ap Am g i x y = ∑ y ∈ N, wG T Ap Am g i x y := by
    rw [sum_filter_of_ne]
    intro y _ hy
    by_contra h; exact hy (wG_eq_zero h)
  have hdeg := hst.copy_deg hx
  have hlam := hst.lam_pos
  rw [hsum]
  constructor
  · have := card_nsmul_le_sum N (fun y => wG T Ap Am g i x y) (1 / (2 * lam))
      (fun y hy => (hst.wG_bounds (mem_filter.1 hy).2).1)
    simp only [nsmul_eq_mul] at this
    calc c * S.card / (2 * lam) = c * S.card * (1 / (2 * lam)) := by ring
      _ ≤ N.card * (1 / (2 * lam)) := by gcongr; exact hdeg.1
      _ ≤ _ := this
  · have := sum_le_card_nsmul N (fun y => wG T Ap Am g i x y) (2 / lam)
      (fun y hy => (hst.wG_bounds (mem_filter.1 hy).2).2)
    simp only [nsmul_eq_mul] at this
    calc _ ≤ N.card * (2 / lam) := this
      _ ≤ T.card * (2 / lam) := mul_le_mul_of_nonneg_right hdeg.2 (by positivity)
      _ = 2 * T.card / lam := by ring

theorem Standing.xG_bounds (hst : Standing T Ap Am g S c lam) {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    c / (2 * lam) ≤ xG T Ap Am g i x ∧ xG T Ap Am g i x ≤ 16 / lam := by
  obtain ⟨h1, h2⟩ := hst.sumwG_bounds hx
  obtain ⟨hR1, hR2⟩ := hst.Rsum_bounds
  have hR := hst.Rsum_pos
  have hT := hst.T_pos
  have hTS := hst.T_le_S
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  unfold xG
  constructor
  · rw [le_div_iff₀ hR]
    calc c / (2 * lam) * Rsum T Ap Am ≤ c / (2 * lam) * T.card := by gcongr
      _ ≤ c * S.card / (2 * lam) := by
        rw [div_mul_eq_mul_div]
        gcongr
      _ ≤ _ := h1
  · rw [div_le_iff₀ hR]
    calc _ ≤ 2 * T.card / lam := h2
      _ = 16 / lam * (T.card / 8) := by ring
      _ ≤ 16 / lam * Rsum T Ap Am := by gcongr

theorem Standing.πG_bounds (hst : Standing T Ap Am g S c lam) {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    c / (3 * lam) ≤ πG T Ap Am g i x ∧ πG T Ap Am g i x ≤ 16 / lam := by
  obtain ⟨h1, h2⟩ := hst.xG_bounds hx
  have hθ := hst.θ_ge
  have hθ1 := θ_le_one T
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  have hx0 : 0 ≤ xG T Ap Am g i x := xG_nonneg i x
  unfold πG
  constructor
  · calc c / (3 * lam) = 2 / 3 * (c / (2 * lam)) := by field_simp
      _ ≤ θ T * xG T Ap Am g i x := by gcongr
  · calc θ T * xG T Ap Am g i x ≤ 1 * xG T Ap Am g i x := by gcongr
      _ ≤ 16 / lam := by linarith

theorem Standing.aG_bounds (hst : Standing T Ap Am g S c lam) {i : Fin t} {x y : G}
    (h : (copyGraph T Ap Am (g i)).Adj x y) :
    c ^ 2 / 9216 ≤ aG T Ap Am g (c ^ 2 / 18) lam i x y ∧
      aG T Ap Am g (c ^ 2 / 18) lam i x y ≤ 1 := by
  obtain ⟨hw1, hw2⟩ := hst.wG_bounds h
  obtain ⟨hx1, hx2⟩ := hst.πG_bounds (copyAdj_mem h).1
  obtain ⟨hy1, hy2⟩ := hst.πG_bounds (copyAdj_mem h).2
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  set w := wG T Ap Am g i x y
  set p := πG T Ap Am g i x
  set q := πG T Ap Am g i y
  have hp : 0 < p := lt_of_lt_of_le (by positivity) hx1
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hy1
  unfold aG
  constructor
  · rw [le_div_iff₀ (mul_pos hp hq)]
    have hpq : p * q ≤ (16 / lam) * (16 / lam) := mul_le_mul hx2 hy2 hq.le (by positivity)
    calc c ^ 2 / 9216 * (p * q) ≤ c ^ 2 / 9216 * ((16 / lam) * (16 / lam)) := by gcongr
      _ = c ^ 2 / 18 / lam * (1 / (2 * lam)) := by field_simp; ring
      _ ≤ c ^ 2 / 18 / lam * w := by gcongr
  · rw [div_le_one (mul_pos hp hq)]
    have hpq : (c / (3 * lam)) * (c / (3 * lam)) ≤ p * q :=
      mul_le_mul hx1 hy1 (by positivity) hp.le
    calc c ^ 2 / 18 / lam * w ≤ c ^ 2 / 18 / lam * (2 / lam) := by gcongr
      _ = (c / (3 * lam)) * (c / (3 * lam)) := by field_simp; ring
      _ ≤ p * q := hpq

theorem Dref_bounds' (hst : Standing T Ap Am g S c lam) {κ : ℝ} (hκ : 0 < κ) :
    κ * c * S.card / (8 * lam) ≤ Dref T Ap Am κ lam ∧
      Dref T Ap Am κ lam ≤ 3 * κ * S.card / (2 * lam) := by
  obtain ⟨hR1, hR2⟩ := hst.Rsum_bounds
  have hθ := hst.θ_ge
  have hθ1 := θ_le_one T
  have hlam := hst.lam_pos
  have hT := hst.temp.card_T
  have hTS := hst.T_le_S
  have hR := hst.Rsum_pos
  unfold Dref
  constructor
  · rw [le_div_iff₀ (by linarith)]
    have := hst.c_pos; have := hst.d_pos
    calc κ * c * S.card / (8 * lam) * θ T ≤ κ * c * S.card / (8 * lam) * 1 := by
          gcongr
      _ = κ / lam * (c * S.card / 8) := by field_simp
      _ ≤ κ / lam * (T.card / 8) := by gcongr
      _ ≤ κ / lam * Rsum T Ap Am := by gcongr
  · rw [div_le_iff₀ (by linarith)]
    calc κ / lam * Rsum T Ap Am ≤ κ / lam * S.card := by gcongr; linarith
      _ = 3 * κ * S.card / (2 * lam) * (2 / 3) := by field_simp
      _ ≤ 3 * κ * S.card / (2 * lam) * θ T := by
          have := hst.d_pos
          gcongr

end Basic

/-! ## The translate cover (5.2): Chernoff bounds and a union bound -/

section Cover

open Classical

/-- The Bernoulli distribution with parameter `p`. -/
def bern (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : FinDist ℝ where
  support := {0, 1}
  prob x := if x = 1 then p else if x = 0 then 1 - p else 0
  prob_nonneg x := by
    split_ifs
    · exact hp.1
    · linarith [hp.2]
    · exact le_rfl
  sum_prob := by
    rw [sum_pair (by norm_num : (0 : ℝ) ≠ 1)]
    simp

theorem mem_bern_support {p : ℝ} {hp : 0 ≤ p ∧ p ≤ 1} {x : ℝ} (hx : x ∈ (bern p hp).support) :
    x = 0 ∨ x = 1 := by
  simpa [bern] using hx

theorem expect_pushDist {α β : Type*} (f : α → β) (μ : FinDist α) (φ : β → ℝ) :
    (pushDist f μ).expect φ = μ.expect (fun a => φ (f a)) := by
  unfold FinDist.expect pushDist
  simp only
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem f ha)
    (fun a => μ.prob a * φ (f a))]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun a ha => ?_
  rw [(mem_filter.1 ha).2]

/-- Push-forward commutes with products (coordinatewise maps). -/
theorem pi_pushDist_P {ι α β : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → FinDist α)
    (φ : ι → α → β) (E : (ι → β) → Prop) :
    (FinDist.pi fun i => pushDist (φ i) (μ i)).P E =
      (FinDist.pi μ).P (fun x => E (fun i => φ i (x i))) := by
  simp only [FinDist.P, FinDist.pi, pushDist]
  set Φ : (ι → α) → (ι → β) := fun x i => φ i (x i) with hΦ
  have hmaps : ∀ x ∈ Fintype.piFinset (fun i => (μ i).support),
      Φ x ∈ Fintype.piFinset (fun i => (μ i).support.image (φ i)) := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    exact fun i => mem_image_of_mem _ (hx i)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun y hy => ?_
  split_ifs with hE
  · rw [prod_univ_sum]
    have hset : (Fintype.piFinset fun i => (μ i).support.filter (fun a => φ i a = y i)) =
        (Fintype.piFinset fun i => (μ i).support).filter (fun x => Φ x = y) := by
      ext x
      simp only [Fintype.mem_piFinset, mem_filter, hΦ]
      constructor
      · intro h; exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩
      · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, congrFun h2 i⟩
    rw [hset]
    refine sum_congr rfl fun x hx => ?_
    have hxy : (fun i => φ i (x i)) = y := (mem_filter.1 hx).2
    rw [ite_eq_left (hxy.symm ▸ hE)]
  · refine (sum_eq_zero fun x hx => ?_).symm
    have hxy : (fun i => φ i (x i)) = y := (mem_filter.1 hx).2
    rw [ite_eq_right (fun h => hE (hxy ▸ h))]

theorem P_add_P_not {α : Type*} (μ : FinDist α) (E : α → Prop) :
    μ.P E + μ.P (fun a => ¬ E a) = 1 := by
  unfold FinDist.P
  rw [← sum_add_distrib, ← μ.sum_prob]
  refine sum_congr rfl fun a _ => ?_
  by_cases h : E a <;> simp [h]

theorem exists_of_P_pos {α : Type*} (μ : FinDist α) {E : α → Prop} (h : 0 < μ.P E) :
    ∃ a ∈ μ.support, E a := by
  by_contra hc
  push Not at hc
  have : μ.P E = 0 := by
    unfold FinDist.P
    exact sum_eq_zero fun a ha => by rw [ite_eq_right (hc a ha)]
  linarith

theorem card_filter_equivFin {G : Type u} [DecidableEq G] (I : Finset G) (P : G → Prop)
    [DecidablePred P] :
    (univ.filter fun i : Fin I.card => P (I.equivFin.symm i)).card = (I.filter P).card := by
  rw [card_filter, card_filter]
  rw [← sum_coe_sort I (fun x => if P x then 1 else 0)]
  exact Equiv.sum_comp I.equivFin.symm (fun x : ↥I => if P x then 1 else 0)

/-- **Chernoff bound for a `0/1`-weighted sum** of independent Bernoulli coordinates. -/
theorem chernoff01 {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (co : ι → ℝ) (hco : ∀ i, co i = 0 ∨ co i = 1) (t : ℝ) (ht : 0 ≤ t) :
    (FinDist.pi fun _ : ι => bern p hp).P (fun ξ => p * ∑ i, co i + t ≤ ∑ i, co i * ξ i) ≤
        Real.exp (-(t ^ 2) / (2 * (p * ∑ i, co i + t / 3))) ∧
      (FinDist.pi fun _ : ι => bern p hp).P (fun ξ => ∑ i, co i * ξ i ≤ p * ∑ i, co i - t) ≤
        Real.exp (-(t ^ 2) / (2 * (p * ∑ i, co i))) := by
  set μ' : ι → FinDist ℝ := fun i => pushDist (fun a => co i * a) (bern p hp) with hμ'
  have hsupp : ∀ i, ∀ x ∈ (μ' i).support, 0 ≤ x ∧ x ≤ 1 := by
    intro i x hx
    simp only [hμ', pushDist, mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rcases mem_bern_support ha with h | h <;> rcases hco i with h' | h' <;> simp [h, h']
  have hexp : ∑ i, (μ' i).expect id = p * ∑ i, co i := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [hμ']
    rw [expect_pushDist]
    simp only [FinDist.expect, bern, id]
    rw [sum_pair (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  have hpush : ∀ E : (ι → ℝ) → Prop, (FinDist.pi μ').P E =
      (FinDist.pi fun _ : ι => bern p hp).P (fun ξ => E (fun i => co i * ξ i)) :=
    fun E => pi_pushDist_P (fun _ => bern p hp) (fun i a => co i * a) E
  constructor
  · have h := chernoff_upper μ' hsupp t ht
    rw [hexp, hpush] at h
    exact h
  · have h := chernoff_lower μ' hsupp t ht
    rw [hexp, hpush] at h
    exact h

end Cover

/-- **(5.2) Translate cover.** Retaining each indexed translate `gF` independently with
probability `λ/m`, Chernoff bounds and a union bound over the `≤ n + 2n²` tests give (with
positive probability, hence for some outcome) a family of copies with every vertex in at most
`2λ` copies and `λ f_s/2 ≤ c_e ≤ 2λ f_s` for every `T`-edge `e` of class `s`, provided
`λ ≥ 256 log n` and `λ ≤ m`. -/
theorem translate_cover {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    (T Ap Am : Finset G) (lam : ℝ) (hn : 2 ≤ Fintype.card G)
    (hlam : 256 * Real.log (Fintype.card G) ≤ lam) (hm : lam ≤ (Ap ∪ Am).card)
    (hdens : ∀ s ∈ T, 1 / 8 ≤ labelDensity T Ap Am s) :
    ∃ (t : ℕ) (g : Fin t → G), t ≤ Fintype.card G ∧ CoverOK T Ap Am g lam := by
  classical
  set n := Fintype.card G with hn_def
  set m := (Ap ∪ Am).card with hm_def
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := by linarith [mul_pos (by norm_num : (0 : ℝ) < 256) hL]
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hlam0 hm
  set p := lam / m with hp_def
  have hp : 0 ≤ p ∧ p ≤ 1 := ⟨div_nonneg hlam0.le hmpos.le, div_le_one_of_le₀ hm hmpos.le⟩
  have hpm : p * m = lam := by rw [hp_def]; field_simp
  set Ω := FinDist.pi fun _ : G => bern p hp with hΩ
  set cV : G → G → ℝ := fun v h => if v ∈ copyVerts Ap Am h then 1 else 0 with hcV
  set cE : G → G → G → ℝ := fun x s h =>
    if (templateGraph T Ap Am).Adj (h⁻¹ * x) (h⁻¹ * (x * s)) then 1 else 0 with hcE
  have hcV01 : ∀ v h, cV v h = 0 ∨ cV v h = 1 := fun v h => by
    simp only [hcV]; split_ifs <;> simp
  have hcE01 : ∀ x s h, cE x s h = 0 ∨ cE x s h = 1 := fun x s h => by
    simp only [hcE]; split_ifs <;> simp
  -- the numbers of indexed translates containing a vertex or an edge
  have hsumV : ∀ v, ∑ h, cV v h = m := by
    intro v
    simp only [hcV]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    congr 1
    refine card_nbij' (fun h => h⁻¹ * v) (fun a => v * a⁻¹) ?_ ?_ ?_ ?_
    · intro h hh; simpa [mem_copyVerts] using hh
    · intro a ha; simpa [mem_copyVerts] using ha
    · intro h _; simp
    · intro a _; simp
  have hsumE : ∀ x s, ∑ h, cE x s h = m * labelDensity T Ap Am s := by
    intro x s
    simp only [hcE]
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    unfold labelDensity
    rw [mul_div_cancel₀ _ hmpos.ne']
    congr 1
    refine card_nbij' (fun h => h⁻¹ * x) (fun a => x * a⁻¹) ?_ ?_ ?_ ?_
    · intro h hh
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
      refine ⟨(templateGraph_mem hh).1, by simpa [mul_assoc] using hh⟩
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      simpa [mul_assoc] using ha.2
    · intro h _; simp
    · intro a _; simp
  -- the failure event and its probability
  set fail : (G → ℝ) → Prop := fun ξ =>
    (∃ v ∈ (univ : Finset G), p * ∑ h, cV v h + lam ≤ ∑ h, cV v h * ξ h) ∨
      ∃ xs ∈ (univ : Finset G) ×ˢ T,
        (∑ h, cE xs.1 xs.2 h * ξ h ≤ p * ∑ h, cE xs.1 xs.2 h - lam * labelDensity T Ap Am xs.2 / 2 ∨
          p * ∑ h, cE xs.1 xs.2 h + lam * labelDensity T Ap Am xs.2 ≤ ∑ h, cE xs.1 xs.2 h * ξ h)
    with hfail
  have hE : Real.exp (-(lam / 64)) ≤ 1 / (n : ℝ) ^ 4 := by
    have : 4 * Real.log n ≤ lam / 64 := by linarith
    calc Real.exp (-(lam / 64)) ≤ Real.exp (-(4 * Real.log n)) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / (n : ℝ) ^ 4 := by
          rw [Real.exp_neg, ← Real.log_rpow (by linarith), Real.exp_log (by positivity)]
          norm_num
  have hPV : ∀ v, Ω.P (fun ξ => p * ∑ h, cV v h + lam ≤ ∑ h, cV v h * ξ h) ≤
      Real.exp (-(lam / 64)) := by
    intro v
    refine ((chernoff01 hp (cV v) (hcV01 v) lam hlam0.le).1).trans (Real.exp_le_exp.2 ?_)
    rw [hsumV, hpm]
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    nlinarith
  have hPE : ∀ xs ∈ (univ : Finset G) ×ˢ T,
      Ω.P (fun ξ => ∑ h, cE xs.1 xs.2 h * ξ h ≤ p * ∑ h, cE xs.1 xs.2 h -
          lam * labelDensity T Ap Am xs.2 / 2 ∨
        p * ∑ h, cE xs.1 xs.2 h + lam * labelDensity T Ap Am xs.2 ≤ ∑ h, cE xs.1 xs.2 h * ξ h) ≤
      2 * Real.exp (-(lam / 64)) := by
    rintro ⟨x, s⟩ hxs
    have hs : s ∈ T := (mem_product.1 hxs).2
    have hf := hdens s hs
    set f := labelDensity T Ap Am s
    have hf0 : 0 < f := by linarith
    have hch := chernoff01 hp (cE x s) (hcE01 x s) (lam * f / 2) (by positivity)
    have hch' := chernoff01 hp (cE x s) (hcE01 x s) (lam * f) (by positivity)
    have hmean : p * ∑ h, cE x s h = lam * f := by rw [hsumE, ← mul_assoc, hpm]
    refine (P_or_le _ _ _).trans ?_
    rw [two_mul]
    apply add_le_add
    · refine hch.2.trans (Real.exp_le_exp.2 ?_)
      rw [hmean, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      nlinarith
    · refine hch'.1.trans (Real.exp_le_exp.2 ?_)
      rw [hmean, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      nlinarith
  have hPfail : Ω.P fail < 1 := by
    have hT : (T.card : ℝ) ≤ n := by exact_mod_cast card_le_univ T
    calc Ω.P fail ≤ Ω.P (fun ξ => ∃ v ∈ (univ : Finset G),
          p * ∑ h, cV v h + lam ≤ ∑ h, cV v h * ξ h) +
        Ω.P (fun ξ => ∃ xs ∈ (univ : Finset G) ×ˢ T,
          (∑ h, cE xs.1 xs.2 h * ξ h ≤ p * ∑ h, cE xs.1 xs.2 h -
            lam * labelDensity T Ap Am xs.2 / 2 ∨
          p * ∑ h, cE xs.1 xs.2 h + lam * labelDensity T Ap Am xs.2 ≤
            ∑ h, cE xs.1 xs.2 h * ξ h)) := P_or_le _ _ _
      _ ≤ ∑ _v : G, Real.exp (-(lam / 64)) +
          ∑ _xs ∈ (univ : Finset G) ×ˢ T, 2 * Real.exp (-(lam / 64)) := by
        apply add_le_add
        · exact (P_exists_le _ _ _).trans (sum_le_sum fun v _ => hPV v)
        · exact (P_exists_le _ _ _).trans (sum_le_sum fun xs hxs => hPE xs hxs)
      _ = n * Real.exp (-(lam / 64)) + (n * T.card) * (2 * Real.exp (-(lam / 64))) := by
        simp only [sum_const, card_product, card_univ, nsmul_eq_mul, Nat.cast_mul, hn_def]
      _ ≤ n * (1 / (n : ℝ) ^ 4) + (n * n) * (2 * (1 / (n : ℝ) ^ 4)) := by
        have := Real.exp_pos (-(lam / 64))
        gcongr
      _ < 1 := by
        have hn0 : (0 : ℝ) < n := by linarith
        rw [show (n : ℝ) * (1 / n ^ 4) + n * n * (2 * (1 / n ^ 4)) =
          1 / n ^ 3 + 2 / n ^ 2 by field_simp]
        have h8 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
          calc (8 : ℝ) = 2 ^ 3 := by norm_num
            _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn2 3
        have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
          calc (4 : ℝ) = 2 ^ 2 := by norm_num
            _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hn2 2
        have h3 : 1 / (n : ℝ) ^ 3 ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) h8
        have h2 : 2 / (n : ℝ) ^ 2 ≤ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
        linarith
  have hgood : 0 < Ω.P (fun ξ => ¬ fail ξ) := by
    have := P_add_P_not Ω fail
    linarith
  obtain ⟨ξ, hξ, hnf⟩ := exists_of_P_pos Ω hgood
  have hξ01 : ∀ h, ξ h = 0 ∨ ξ h = 1 := fun h =>
    mem_bern_support (((mem_pi_support _ ξ).1 hξ) h)
  set I := univ.filter fun h => ξ h = 1 with hI
  have hcount : ∀ (P : G → Prop) [DecidablePred P],
      ∑ h, (if P h then (1 : ℝ) else 0) * ξ h = (I.filter P).card := by
    intro P _
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, hI, sum_filter]
    refine sum_congr rfl fun h _ => ?_
    rcases hξ01 h with e | e <;> by_cases hP : P h <;> simp [e, hP]
  refine ⟨I.card, fun i => (I.equivFin.symm i : G), card_le_univ _, ?_, ?_, ?_⟩
  · intro v
    rw [card_filter_equivFin I (fun h => v ∈ copyVerts Ap Am h), ← hcount]
    by_contra hc
    push Not at hc
    apply hnf
    left
    refine ⟨v, mem_univ _, ?_⟩
    rw [hsumV, hpm]
    simp only [hcV]
    linarith
  · intro x s hs
    have h := card_filter_equivFin I
      (fun h => (templateGraph T Ap Am).Adj (h⁻¹ * x) (h⁻¹ * (x * s)))
    unfold occ
    rw [h, ← hcount]
    by_contra hc
    push Not at hc
    apply hnf
    right
    refine ⟨(x, s), mem_product.2 ⟨mem_univ _, hs⟩, Or.inl ?_⟩
    simp only
    rw [hsumE, ← mul_assoc, hpm]
    simp only [hcE]
    linarith
  · intro x s hs
    have h := card_filter_equivFin I
      (fun h => (templateGraph T Ap Am).Adj (h⁻¹ * x) (h⁻¹ * (x * s)))
    unfold occ
    rw [h, ← hcount]
    by_contra hc
    push Not at hc
    apply hnf
    right
    refine ⟨(x, s), mem_product.2 ⟨mem_univ _, hs⟩, Or.inr ?_⟩
    simp only
    rw [hsumE, ← mul_assoc, hpm]
    simp only [hcE]
    linarith

/-! ## The signed incidence system of §5.2 -/

section Signed

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (T Ap Am : Finset G) {t : ℕ} (g : Fin t → G)

/-- The left cosets of `U = ⟨T⟩`. -/
abbrev QT (T : Finset G) := G ⧸ Subgroup.closure (T : Set G)

instance instFintypeQT (T : Finset G) : Fintype (QT T) := Fintype.ofFinite _

instance instDecEqQT (T : Finset G) : DecidableEq (QT T) := Classical.decEq _

open Classical in
/-- The signed incidence system of §5.2. Vertices: original vertices `inl v`, copy nodes
`inr (inl i)`, auxiliary coset nodes `inr (inr H)`. Edges: ownership incidences
`inl (i, x)` (sign `+1` at `x`, the local sign `s_i(x)` at copy `i`; a zero loop if
`x ∉ V(F_i)`), and reservation incidences `inr v` (sign `+1` at both ends, joining `v` to its
coset node) when `u` is odd (a zero loop when `u` is even). -/
def Γ : SignedGraph (G ⊕ Fin t ⊕ QT T) ((Fin t × G) ⊕ G) where
  fst e := match e with
    | .inl p => .inl p.2
    | .inr v => .inl v
  snd e := match e with
    | .inl p => if p.2 ∈ copyVerts Ap Am (g p.1) then .inr (.inl p.1) else .inl p.2
    | .inr v => if Odd (uu T) then .inr (.inr (QuotientGroup.mk v)) else .inl v
  sfst _ := true
  ssnd e := match e with
    | .inl p => if p.2 ∈ copyVerts Ap Am (g p.1) then decide ((g p.1)⁻¹ * p.2 ∈ Ap) else false
    | .inr _ => decide (Odd (uu T))

open Classical in
/-- Demands: one at original vertices, zero at copies, one at the auxiliary nodes (odd case). -/
def bd : G ⊕ Fin t ⊕ QT T → ℤ
  | .inl _ => 1
  | .inr (.inl _) => 0
  | .inr (.inr _) => if Odd (uu T) then 1 else 0

open Classical in
/-- The fractional point `π` of §5.2: `π_{v,i} = θ x_{v,i}`, `z_v = 1/u` (odd case). -/
def xvec : (Fin t × G) ⊕ G → ℝ
  | .inl p => πG T Ap Am g p.1 p.2
  | .inr _ => if Odd (uu T) then 1 / (uu T : ℝ) else 0

open Classical in
/-- A rounding outcome law: the terminal law of a line process started at `π` whose moves change
at most four variables at every vertex, supported on integral solutions (Lemmas 4.1–4.2). -/
def IsRounding (μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)) : Prop :=
  ∃ ok : ((Fin t × G) ⊕ G → ℝ) → Prop,
    (∀ h, ok h → ∀ v, (univ.filter fun e => h e ≠ 0 ∧
      ((Γ T Ap Am g).fst e = v ∨ (Γ T Ap Am g).snd e = v)).card ≤ 4) ∧
    LineProcess ok (xvec T Ap Am g) μ₀ ∧
    ∀ z ∈ μ₀.support, z ∈ (Γ T Ap Am g).integralSolutions (fun v => (bd T v : ℝ))

end Signed

section Incidence

open Classical

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {T Ap Am : Finset G} {t : ℕ} {g : Fin t → G}

@[simp] theorem Γ_fst_inl (p : Fin t × G) : (Γ T Ap Am g).fst (.inl p) = .inl p.2 := rfl
@[simp] theorem Γ_fst_inr (v : G) : (Γ T Ap Am g).fst (.inr v) = .inl v := rfl
@[simp] theorem Γ_sfst (e : (Fin t × G) ⊕ G) : (Γ T Ap Am g).sfst e = true := rfl
theorem Γ_snd_inl (p : Fin t × G) : (Γ T Ap Am g).snd (.inl p) =
    if p.2 ∈ copyVerts Ap Am (g p.1) then .inr (.inl p.1) else .inl p.2 := rfl
theorem Γ_snd_inr (v : G) : (Γ T Ap Am g).snd (.inr v) =
    if Odd (uu T) then .inr (.inr (QuotientGroup.mk v)) else .inl v := rfl
theorem Γ_ssnd_inl (p : Fin t × G) : (Γ T Ap Am g).ssnd (.inl p) =
    if p.2 ∈ copyVerts Ap Am (g p.1) then decide ((g p.1)⁻¹ * p.2 ∈ Ap) else false := rfl
theorem Γ_ssnd_inr (v : G) : (Γ T Ap Am g).ssnd (.inr v) = decide (Odd (uu T)) := rfl

theorem inc_inl_inl (v : G) (i : Fin t) (x : G) :
    (Γ T Ap Am g).incidence (.inl v) (.inl (i, x)) =
      if x ∈ copyVerts Ap Am (g i) ∧ x = v then 1 else 0 := by
  unfold SignedGraph.incidence
  rw [Γ_snd_inl, Γ_ssnd_inl]
  simp only [Γ_fst_inl, Γ_sfst]
  by_cases hx : x ∈ copyVerts Ap Am (g i)
  · rw [ite_eq_left hx, ite_eq_left hx]
    by_cases hv : x = v
    · subst hv; simp [hx, SignedGraph.signVal]
    · simp [hx, hv]
  · rw [ite_eq_right hx, ite_eq_right hx]
    by_cases hv : x = v
    · subst hv; simp [hx, SignedGraph.signVal]
    · simp [hx, hv]

theorem inc_inl_inr (v w : G) :
    (Γ T Ap Am g).incidence (.inl v) (.inr w) = if Odd (uu T) ∧ w = v then 1 else 0 := by
  unfold SignedGraph.incidence
  rw [Γ_snd_inr, Γ_ssnd_inr]
  by_cases ho : Odd (uu T) <;> by_cases hv : w = v <;> simp [ho, hv, SignedGraph.signVal]

theorem inc_copy_inl (j i : Fin t) (x : G) :
    (Γ T Ap Am g).incidence (.inr (.inl j)) (.inl (i, x)) =
      if x ∈ copyVerts Ap Am (g i) ∧ i = j then
        SignedGraph.signVal (decide ((g i)⁻¹ * x ∈ Ap)) else 0 := by
  unfold SignedGraph.incidence
  rw [Γ_snd_inl, Γ_ssnd_inl]
  simp only [Γ_fst_inl]
  by_cases hx : x ∈ copyVerts Ap Am (g i)
  · rw [ite_eq_left hx, ite_eq_left hx]
    by_cases hv : i = j
    · subst hv; simp [hx]
    · simp [hx, hv]
  · rw [ite_eq_right hx, ite_eq_right hx]
    simp [hx]

theorem inc_copy_inr (j : Fin t) (w : G) :
    (Γ T Ap Am g).incidence (.inr (.inl j)) (.inr w) = 0 := by
  unfold SignedGraph.incidence
  rw [Γ_snd_inr]
  by_cases ho : Odd (uu T) <;> simp [ho]

theorem inc_aux_inl (q : QT T) (i : Fin t) (x : G) :
    (Γ T Ap Am g).incidence (.inr (.inr q)) (.inl (i, x)) = 0 := by
  unfold SignedGraph.incidence
  rw [Γ_snd_inl]
  by_cases hx : x ∈ copyVerts Ap Am (g i) <;> simp [hx]

theorem inc_aux_inr (q : QT T) (w : G) :
    (Γ T Ap Am g).incidence (.inr (.inr q)) (.inr w) =
      if Odd (uu T) ∧ (QuotientGroup.mk w : QT T) = q then 1 else 0 := by
  unfold SignedGraph.incidence
  rw [Γ_snd_inr, Γ_ssnd_inr]
  by_cases ho : Odd (uu T) <;> by_cases hv : (QuotientGroup.mk w : QT T) = q <;>
    simp [ho, hv, SignedGraph.signVal]

theorem apply_inl (z : (Fin t × G) ⊕ G → ℝ) (v : G) :
    (Γ T Ap Am g).apply z (.inl v) =
      ∑ i, (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) +
        if Odd (uu T) then z (.inr v) else 0 := by
  unfold SignedGraph.apply
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    simp only [inc_inl_inl]
    by_cases hv : v ∈ copyVerts Ap Am (g i)
    · rw [ite_eq_left hv, sum_eq_single v]
      · simp [hv]
      · intro x _ hx; simp [hx]
      · simp
    · rw [ite_eq_right hv]
      refine sum_eq_zero fun x _ => ?_
      by_cases hx : x = v
      · subst hx; simp [hv]
      · simp [hx]
  · simp only [inc_inl_inr]
    by_cases ho : Odd (uu T)
    · rw [ite_eq_left ho, sum_eq_single v]
      · simp [ho]
      · intro w _ hw; simp [hw]
      · simp
    · simp [ho]

theorem apply_copy (z : (Fin t × G) ⊕ G → ℝ) (j : Fin t) :
    (Γ T Ap Am g).apply z (.inr (.inl j)) =
      ∑ x ∈ copyVerts Ap Am (g j),
        SignedGraph.signVal (decide ((g j)⁻¹ * x ∈ Ap)) * z (.inl (j, x)) := by
  unfold SignedGraph.apply
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [inc_copy_inr, zero_mul, sum_const_zero, add_zero, inc_copy_inl]
  rw [sum_eq_single j]
  · simp only [and_true, ite_mul, zero_mul]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  · intro i _ hij
    refine sum_eq_zero fun x _ => ?_
    simp [hij]
  · simp

theorem apply_aux (z : (Fin t × G) ⊕ G → ℝ) (q : QT T) :
    (Γ T Ap Am g).apply z (.inr (.inr q)) =
      if Odd (uu T) then
        ∑ v ∈ univ.filter (fun v => (QuotientGroup.mk v : QT T) = q), z (.inr v) else 0 := by
  unfold SignedGraph.apply
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [inc_aux_inl, zero_mul, sum_const_zero, zero_add, inc_aux_inr]
  by_cases ho : Odd (uu T)
  · rw [ite_eq_left ho, sum_filter]
    refine sum_congr rfl fun v _ => ?_
    by_cases hv : (QuotientGroup.mk v : QT T) = q <;> simp [ho, hv]
  · simp [ho]

end Incidence


/-! ## The allocation built from the rounding, independently in every coset -/

section Alloc

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (T Ap Am : Finset G) {t : ℕ} (g : Fin t → G)

/-- The coset of the copy node `i` (or of an edge), `a₀ ∈ V(F)` a fixed base vertex. -/
def cosE (a₀ : G) : (Fin t × G) ⊕ G → QT T
  | .inl p => (QuotientGroup.mk (g p.1 * a₀) : QT T)
  | .inr v => (QuotientGroup.mk v : QT T)

/-- The outcome of independent roundings in the cosets: the variables of coset `H` are read
from the `H`-th independent sample. -/
def glue (a₀ : G) (ζ : QT T → ((Fin t × G) ⊕ G → ℝ)) : (Fin t × G) ⊕ G → ℝ :=
  fun e => ζ (cosE T g a₀ e) e

open Classical in
/-- The part `V_i = {v : X_{v,i} = 1}`. -/
def partZ (z : (Fin t × G) ⊕ G → ℝ) (i : Fin t) : Finset G :=
  (copyVerts Ap Am (g i)).filter fun x => z (.inl (i, x)) = 1

theorem aG_symm (κ lam : ℝ) (i : Fin t) (x y : G) :
    aG T Ap Am g κ lam i x y = aG T Ap Am g κ lam i y x := by
  unfold aG; rw [wG_symm (T := T), mul_comm (πG T Ap Am g i x)]

theorem aG_nonneg {κ lam : ℝ} (h : 0 ≤ κ / lam) (i : Fin t) (x y : G) :
    0 ≤ aG T Ap Am g κ lam i x y := by
  unfold aG
  exact div_nonneg (mul_nonneg h (wG_nonneg _ _ _))
    (mul_nonneg (πG_nonneg _ _) (πG_nonneg _ _))

open Classical in
/-- The allocation read off an integral point: parts, reserved set, and `H_i = F_i[V_i]` with
the weights (5.8). -/
def alloc (κ lam : ℝ) (hkl : 0 ≤ κ / lam) (z : (Fin t × G) ⊕ G → ℝ) : Allocation G where
  t := t
  g := g
  part := partZ Ap Am g z
  W := if Odd (uu T) then univ.filter fun v => z (.inr v) = 1 else ∅
  H i :=
    { w := fun x y => aG T Ap Am g κ lam i x y
      symm := fun x y => aG_symm T Ap Am g κ lam i x y
      nonneg := fun x y => aG_nonneg T Ap Am g hkl i x y
      loopless := fun x => by simp [aG, wG_self] }


end Alloc

/-! ## The law (5.7) of the reserved vertices -/

section Reservation

open Classical

theorem P_congr {α : Type*} (μ : FinDist α) {E F : α → Prop}
    (h : ∀ a ∈ μ.support, E a ↔ F a) : μ.P E = μ.P F :=
  le_antisymm (P_mono μ fun a ha => (h a ha).1) (P_mono μ fun a ha => (h a ha).2)

theorem P_false {α : Type*} (μ : FinDist α) : μ.P (fun _ => False) = 0 := by
  simp [FinDist.P]

theorem P_eq_sum_fiber {α β : Type*} [Fintype β] (μ : FinDist α) (f : α → β)
    (E : α → Prop) : μ.P E = ∑ b, μ.P (fun a => f a = b ∧ E a) := by
  unfold FinDist.P
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single (f a)]
  · simp
  · intro b _ hb
    have : ¬ f a = b := fun h => hb h.symm
    simp [this]
  · simp

/-- **(5.7), with independence across cosets.** If in every coset sample exactly one vertex of
each coset is marked, and every vertex is marked with probability `1/|U|`, then the set of
marked vertices of independent samples (one per coset) is a uniformly random transversal. -/
theorem reservation_product {G : Type u} [Group G] [Fintype G] [DecidableEq G] (U : Subgroup G)
    [Fintype (G ⧸ U)] [DecidableEq (G ⧸ U)] {α : Type*} (ν : FinDist α) (r : α → G → Prop)
    (hr : ∀ a ∈ ν.support, ∀ x : G,
      ∃! v, (QuotientGroup.mk v : G ⧸ U) = QuotientGroup.mk x ∧ r a v)
    (hp : ∀ v, ν.P (fun a => r a v) = 1 / Nat.card U) (Q : Finset G → Prop) :
    (FinDist.pi fun _ : G ⧸ U => ν).P
        (fun ζ => Q (univ.filter fun v => r (ζ (QuotientGroup.mk v)) v)) =
      ((univ.filter fun W : Finset G =>
          (∀ x, (W.filter fun w => x⁻¹ * w ∈ U).card = 1) ∧ Q W).card : ℝ) /
        (univ.filter fun W : Finset G => ∀ x, (W.filter fun w => x⁻¹ * w ∈ U).card = 1).card := by
  set π := FinDist.pi fun _ : G ⧸ U => ν with hπ
  set Wf : ((G ⧸ U) → α) → Finset G :=
    fun ζ => univ.filter fun v => r (ζ (QuotientGroup.mk v)) v with hWf
  set Tr : Finset G → Prop := fun W => ∀ x, (W.filter fun w => x⁻¹ * w ∈ U).card = 1 with hTr
  set k := Fintype.card (G ⧸ U)
  set u := Nat.card U
  have hq : ∀ v x : G, (QuotientGroup.mk v : G ⧸ U) = QuotientGroup.mk x ↔ x⁻¹ * v ∈ U :=
    fun v x => eq_comm.trans QuotientGroup.eq
  have hfib : ∀ W₀ : Finset G,
      π.P (fun ζ => Wf ζ = W₀) = if Tr W₀ then (1 / (u : ℝ)) ^ k else 0 := by
    intro W₀
    have e : (fun ζ => Wf ζ = W₀) = fun ζ => ∀ q, (fun q a =>
        ∀ v, (QuotientGroup.mk v : G ⧸ U) = q → (r a v ↔ v ∈ W₀)) q (ζ q) := by
      funext ζ
      apply propext
      simp only [hWf]
      constructor
      · rintro h q v rfl
        rw [← h]
        simp
      · intro h
        ext v
        simp only [mem_filter, mem_univ, true_and]
        exact h _ v rfl
    rw [e, hπ, pi_P_forall (fun _ : G ⧸ U => ν)
      (fun q a => ∀ v, (QuotientGroup.mk v : G ⧸ U) = q → (r a v ↔ v ∈ W₀))]
    split_ifs with hT
    · have hfac : ∀ q : G ⧸ U, ν.P (fun a =>
          ∀ v, (QuotientGroup.mk v : G ⧸ U) = q → (r a v ↔ v ∈ W₀)) = 1 / (u : ℝ) := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨w, hw⟩ := card_eq_one.1 (hT x)
        have hwmem : w ∈ W₀ ∧ x⁻¹ * w ∈ U := by
          have := mem_singleton_self w
          rw [← hw] at this
          exact mem_filter.1 this
        rw [← hp w]
        apply P_congr
        intro a ha
        obtain ⟨v₀, ⟨hv₀q, hv₀r⟩, huniq⟩ := hr a ha x
        constructor
        · intro h
          exact (h w ((hq w x).2 hwmem.2)).2 hwmem.1
        · intro hrw v hv
          constructor
          · intro hrv
            have h1 := huniq v ⟨hv, hrv⟩
            have h2 := huniq w ⟨(hq w x).2 hwmem.2, hrw⟩
            rw [h1, ← h2]
            exact hwmem.1
          · intro hvW
            have : v ∈ W₀.filter (fun w => x⁻¹ * w ∈ U) :=
              mem_filter.2 ⟨hvW, (hq v x).1 hv⟩
            rw [hw, mem_singleton] at this
            rw [this]
            exact hrw
      rw [prod_congr rfl (fun q _ => hfac q), prod_const, card_univ]
    · simp only [hTr, not_forall] at hT
      obtain ⟨x, hx⟩ := hT
      apply prod_eq_zero (mem_univ (QuotientGroup.mk x))
      rw [← P_false ν]
      apply P_congr
      intro a ha
      simp only [iff_false]
      intro h
      apply hx
      obtain ⟨v₀, ⟨hv₀q, hv₀r⟩, huniq⟩ := hr a ha x
      rw [card_eq_one]
      refine ⟨v₀, ?_⟩
      ext v
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hvW, hvU⟩
        have hvq := (hq v x).2 hvU
        exact huniq v ⟨hvq, (h v hvq).2 hvW⟩
      · intro hv
        rw [hv]
        exact ⟨(h v₀ hv₀q).1 hv₀r, (hq v₀ x).1 hv₀q⟩
  have hsum : ∀ Q' : Finset G → Prop, π.P (fun ζ => Q' (Wf ζ)) =
      ((univ.filter fun W => Tr W ∧ Q' W).card : ℝ) * (1 / (u : ℝ)) ^ k := by
    intro Q'
    rw [P_eq_sum_fiber π Wf]
    have hterm : ∀ W₀, π.P (fun ζ => Wf ζ = W₀ ∧ Q' (Wf ζ)) =
        if Tr W₀ ∧ Q' W₀ then (1 / (u : ℝ)) ^ k else 0 := by
      intro W₀
      by_cases hQ : Q' W₀
      · rw [show (fun ζ => Wf ζ = W₀ ∧ Q' (Wf ζ)) = fun ζ => Wf ζ = W₀ from by
          funext ζ; apply propext
          exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hQ⟩⟩]
        rw [hfib]
        simp [hQ]
      · rw [show (fun ζ => Wf ζ = W₀ ∧ Q' (Wf ζ)) = fun _ => False from by
          funext ζ; apply propext
          simp only [iff_false, not_and]
          intro h; rw [h]; exact hQ]
        rw [P_false]
        simp [hQ]
    simp only [hterm]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have h1 : π.P (fun _ => True) = ((univ.filter fun W => Tr W).card : ℝ) * (1 / (u : ℝ)) ^ k := by
    have := hsum (fun _ => True)
    simp only [and_true] at this
    exact this
  rw [P_true] at h1
  rw [hsum Q]
  have hne : ((univ.filter fun W => Tr W).card : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    norm_num at h1
  rw [eq_div_iff hne]
  calc ((univ.filter fun W => Tr W ∧ Q W).card : ℝ) * (1 / (u : ℝ)) ^ k *
        ((univ.filter fun W => Tr W).card : ℝ) =
      ((univ.filter fun W => Tr W ∧ Q W).card : ℝ) *
        (((univ.filter fun W => Tr W).card : ℝ) * (1 / (u : ℝ)) ^ k) := by ring
    _ = _ := by rw [← h1, mul_one]

end Reservation

/-- **(5.7) and independence across cosets.** The reserved set of the product of independent
roundings is a uniformly random transversal of the left `U`-cosets. -/
theorem reservation_law {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    (T Ap Am : Finset G) {t : ℕ} (g : Fin t → G) {S : Finset G} {c lam κ : ℝ}
    (hkl : 0 ≤ κ / lam) (_hst : Standing T Ap Am g S c lam)
    {μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)} (hμ : IsRounding T Ap Am g μ₀) (a₀ : G) :
    ReservationLaw (pushDist (fun ζ => alloc T Ap Am g κ lam hkl (glue T g a₀ ζ))
      (FinDist.pi fun _ : QT T => μ₀)) T := by
  classical
  obtain ⟨ok, -, hlp, hint⟩ := hμ
  intro ho Q
  have ho' : Odd (uu T) := ho
  rw [P_pushDist]
  have hW : ∀ ζ : QT T → ((Fin t × G) ⊕ G → ℝ),
      (alloc T Ap Am g κ lam hkl (glue T g a₀ ζ)).W =
        univ.filter fun v => ζ (QuotientGroup.mk v) (.inr v) = 1 := by
    intro ζ
    change (if Odd (uu T) then univ.filter (fun v => glue T g a₀ ζ (.inr v) = 1) else ∅) = _
    rw [ite_eq_left ho']
    rfl
  simp only [hW]
  unfold IsTransversal
  have hr : ∀ z ∈ μ₀.support, ∀ x : G, ∃! v, (QuotientGroup.mk v : QT T) = QuotientGroup.mk x ∧
      z (.inr v) = 1 := by
    intro z hz x
    have h := (hint z hz).2 (.inr (.inr (QuotientGroup.mk x)))
    rw [apply_aux, ite_eq_left ho'] at h
    have hb : ((bd T (.inr (.inr (QuotientGroup.mk x)) : G ⊕ Fin t ⊕ QT T) : ℤ) : ℝ) = 1 := by
      simp [bd, ho']
    dsimp only at h
    rw [hb, sum01_eq_card _ _ (fun v _ => (hint z hz).1 _)] at h
    have h' : ((univ.filter (fun v => (QuotientGroup.mk v : QT T) = QuotientGroup.mk x)).filter
        fun v => z (.inr v) = 1).card = 1 := by exact_mod_cast h
    obtain ⟨v₀, hv₀⟩ := card_eq_one.1 h'
    refine ⟨v₀, ?_, ?_⟩
    · have := mem_singleton_self v₀
      rw [← hv₀] at this
      simp only [mem_filter, mem_univ, true_and] at this
      exact this
    · intro v hv
      have : v ∈ (univ.filter (fun v => (QuotientGroup.mk v : QT T) = QuotientGroup.mk x)).filter
          fun v => z (.inr v) = 1 := by
        simp only [mem_filter, mem_univ, true_and]
        exact hv
      rw [hv₀] at this
      exact mem_singleton.1 this
  have hp : ∀ v, μ₀.P (fun z => z (.inr v) = 1) =
      1 / Nat.card (Subgroup.closure (T : Set G)) := by
    intro v
    have hexp := LineProcess.expect_eq hlp (.inr v)
    have hx : xvec T Ap Am g (.inr v) = 1 / (uu T : ℝ) := by simp [xvec, ho']
    rw [hx] at hexp
    show _ = 1 / (uu T : ℝ)
    rw [← hexp]
    unfold FinDist.P FinDist.expect
    refine sum_congr rfl fun z hz => ?_
    rcases (hint z hz).1 (.inr v) with h | h <;> simp [h]
  convert reservation_product (Subgroup.closure (T : Set G)) μ₀ (fun z v => z (.inr v) = 1)
    hr hp Q using 3
  all_goals congr


/-! ## The per-copy events of §5.3 -/

section Events

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (T Ap Am : Finset G) {t : ℕ} (g : Fin t → G)

/-- Size event of (5.11): `|V_i| ≥ E|V_i| / 2`. -/
def sizeOK (i : Fin t) (z : (Fin t × G) ⊕ G → ℝ) : Prop :=
  (∑ x ∈ copyVerts Ap Am (g i), πG T Ap Am g i x) / 2 ≤
    ∑ x ∈ copyVerts Ap Am (g i), z (.inl (i, x))

/-- Degree event of (5.11) at the full-copy vertex `x`: `∑_u X_{u,i} a_{i,ux} = (1 ± η) D`. -/
def degOK (κ lam η : ℝ) (i : Fin t) (z : (Fin t × G) ⊕ G → ℝ) (x : G) : Prop :=
  |∑ y ∈ copyVerts Ap Am (g i), z (.inl (i, y)) * aG T Ap Am g κ lam i x y - Dref T Ap Am κ lam|
    ≤ η * Dref T Ap Am κ lam

open Classical in
/-- `E |N_{F_i}(x) ∩ V_i| = ∑_{y ∼ x} π_{y,i}`. -/
def nbhdMean (i : Fin t) (x : G) : ℝ :=
  ∑ y ∈ copyVerts Ap Am (g i), if (copyGraph T Ap Am (g i)).Adj x y then πG T Ap Am g i y else 0

open Classical in
/-- Support-count event of (5.11) at the full-copy vertex `x`. -/
def nbhdOK (i : Fin t) (z : (Fin t × G) ⊕ G → ℝ) (x : G) : Prop :=
  nbhdMean T Ap Am g i x / 2 ≤ ∑ y ∈ copyVerts Ap Am (g i),
      (if (copyGraph T Ap Am (g i)).Adj x y then z (.inl (i, y)) else 0) ∧
    ∑ y ∈ copyVerts Ap Am (g i),
      (if (copyGraph T Ap Am (g i)).Adj x y then z (.inl (i, y)) else 0) ≤
      2 * nbhdMean T Ap Am g i x

/-- The spectral event (consequence of (5.13)–(5.14) and (5.12)): on functions with zero sum
over `V_i`, the quadratic form of `H_i` is at most `(1 - 7σ₀/8) D ‖f‖²`. -/
def gapOK (κ lam σ0 : ℝ) (i : Fin t) (z : (Fin t × G) ⊕ G → ℝ) : Prop :=
  ∀ f : G → ℝ, ∑ x ∈ partZ Ap Am g z i, f x = 0 →
    ∑ x ∈ partZ Ap Am g z i, ∑ y ∈ partZ Ap Am g z i, aG T Ap Am g κ lam i x y * f x * f y ≤
      (1 - 7 * σ0 / 8) * Dref T Ap Am κ lam * ∑ x ∈ partZ Ap Am g z i, f x ^ 2

/-- All the per-copy events. -/
def GoodCopy (κ lam η σ0 : ℝ) (i : Fin t) (z : (Fin t × G) ⊕ G → ℝ) : Prop :=
  sizeOK T Ap Am g i z ∧
    (∀ x ∈ copyVerts Ap Am (g i), degOK T Ap Am g κ lam η i z x ∧ nbhdOK T Ap Am g i z x) ∧
    gapOK T Ap Am g κ lam σ0 i z

end Events

/-! ## The deterministic part of Proposition 5.3 -/

section Deterministic

open Classical

/-- **Gap of `H_i` from the spectral event.** If, on functions with zero sum over `P`, the
quadratic form of the weights is at most `(1 - 7σ₀/8) D ‖f‖²`, and all degrees are at least
`(1 - η) D` with `η ≤ σ₀/4`, then the normalized upper gap is at least `σ₀/2` (variational form
(2.1), tested with the unweighted mean). This replaces the interlacing and reference-degree
perturbation at the end of §5.3. -/
theorem hasGap_of_quad {V : Type*} [DecidableEq V] (P : Finset V) (a : V → V → ℝ)
    (H : WGraph P) (hH : ∀ x y : P, H.w x y = a x y) (hsymm : ∀ x y, a x y = a y x)
    {D η σ0 : ℝ} (hD : 0 < D) (hσ0 : 0 < σ0) (hσ01 : σ0 ≤ 1) (hη : 0 ≤ η)
    (hησ : η ≤ σ0 / 4)
    (hdeg : ∀ x ∈ P, |∑ y ∈ P, a x y - D| ≤ η * D)
    (hquad : ∀ f : V → ℝ, ∑ x ∈ P, f x = 0 →
      ∑ x ∈ P, ∑ y ∈ P, a x y * f x * f y ≤ (1 - 7 * σ0 / 8) * D * ∑ x ∈ P, f x ^ 2) :
    H.HasGap (σ0 / 2) := by
  intro f
  set F : V → ℝ := fun x => if h : x ∈ P then f ⟨x, h⟩ else 0 with hF
  have hFf : ∀ x : P, F x = f x := fun x => by simp [hF, x.2]
  set z := (∑ x ∈ P, F x) / P.card with hz
  refine ⟨z, ?_⟩
  set g' : V → ℝ := fun x => F x - z with hg'
  have hg0 : ∑ x ∈ P, g' x = 0 := by
    simp only [hg', sum_sub_distrib, sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos P.card with h | h
    · simp [card_eq_zero.1 h]
    · rw [hz, mul_div_cancel₀ _ (by exact_mod_cast h.ne')]
      ring
  have hq := hquad g' hg0
  have hdegH : ∀ x : P, H.deg x = ∑ y ∈ P, a x y := by
    intro x
    unfold WGraph.deg
    rw [← sum_coe_sort P (fun y => a x y)]
    exact sum_congr rfl fun y _ => hH x y
  have hlhs : ∑ x : P, H.deg x * (f x - z) ^ 2 = ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2 := by
    rw [← sum_coe_sort P (fun x => (∑ y ∈ P, a x y) * g' x ^ 2)]
    refine sum_congr rfl fun x _ => ?_
    rw [hdegH, ← hFf]
  have hexp : ∑ x ∈ P, ∑ y ∈ P, a x y * (g' x - g' y) ^ 2 =
      2 * ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2 -
        2 * ∑ x ∈ P, ∑ y ∈ P, a x y * g' x * g' y := by
    have e1 : ∑ x ∈ P, ∑ y ∈ P, a x y * g' y ^ 2 = ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2 := by
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun x _ => by rw [hsymm]
    have e2 : ∑ x ∈ P, ∑ y ∈ P, a x y * g' x ^ 2 = ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2 := by
      refine sum_congr rfl fun x _ => ?_
      rw [sum_mul]
    calc _ = ∑ x ∈ P, ∑ y ∈ P, (a x y * g' x ^ 2 + a x y * g' y ^ 2 -
          2 * (a x y * g' x * g' y)) :=
          sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
      _ = _ := by
          simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
          rw [e1, e2]
          ring
  have hrhs : H.dirichlet f = ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2 -
      ∑ x ∈ P, ∑ y ∈ P, a x y * g' x * g' y := by
    unfold WGraph.dirichlet
    have : ∑ x : P, ∑ y : P, H.w x y * (f x - f y) ^ 2 =
        ∑ x ∈ P, ∑ y ∈ P, a x y * (g' x - g' y) ^ 2 := by
      rw [← sum_coe_sort P]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_coe_sort P]
      refine sum_congr rfl fun y _ => ?_
      rw [hH, ← hFf, ← hFf]
      simp only [hg']
      ring
    rw [this, hexp]
    ring
  set Q := ∑ x ∈ P, g' x ^ 2 with hQ
  have hQ0 : 0 ≤ Q := sum_nonneg fun x _ => sq_nonneg _
  have hdeg_lo : (1 - η) * D * Q ≤ ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2 := by
    rw [hQ, mul_sum]
    refine sum_le_sum fun x hx => ?_
    have := (abs_le.1 (hdeg x hx)).1
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  rw [hlhs, hrhs]
  set X := ∑ x ∈ P, (∑ y ∈ P, a x y) * g' x ^ 2
  set Y := ∑ x ∈ P, ∑ y ∈ P, a x y * g' x * g' y
  have hc1 : 1 - 7 * σ0 / 8 ≤ (1 - σ0 / 2) * (1 - η) := by nlinarith
  have hDQ : 0 ≤ D * Q := mul_nonneg hD.le hQ0
  have h1 : (1 - 7 * σ0 / 8) * D * Q ≤ (1 - σ0 / 2) * ((1 - η) * D * Q) := by
    calc (1 - 7 * σ0 / 8) * D * Q = (1 - 7 * σ0 / 8) * (D * Q) := by ring
      _ ≤ ((1 - σ0 / 2) * (1 - η)) * (D * Q) := mul_le_mul_of_nonneg_right hc1 hDQ
      _ = _ := by ring
  have h2 : (1 - σ0 / 2) * ((1 - η) * D * Q) ≤ (1 - σ0 / 2) * X :=
    mul_le_mul_of_nonneg_left hdeg_lo (by linarith)
  linarith

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}

theorem Standing.size_mean_ge (hst : Standing T Ap Am g S c lam) (i : Fin t) :
    c ^ 2 * S.card / (3 * lam) ≤ ∑ x ∈ copyVerts Ap Am (g i), πG T Ap Am g i x := by
  have hm := (card_VF hst.c_pos.le hst.temp).2.1
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  have := card_nsmul_le_sum (copyVerts Ap Am (g i)) (fun x => πG T Ap Am g i x) (c / (3 * lam))
    (fun x hx => (hst.πG_bounds hx).1)
  rw [nsmul_eq_mul, card_copyVerts] at this
  calc c ^ 2 * S.card / (3 * lam) = c * S.card * (c / (3 * lam)) := by ring
    _ ≤ (Ap ∪ Am).card * (c / (3 * lam)) := by gcongr
    _ ≤ _ := this

theorem Standing.nbhdMean_bounds (hst : Standing T Ap Am g S c lam) {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    c ^ 2 * S.card / (3 * lam) ≤ nbhdMean T Ap Am g i x ∧
      nbhdMean T Ap Am g i x ≤ 16 * S.card / lam := by
  set N := univ.filter fun y => (copyGraph T Ap Am (g i)).Adj x y with hN
  have hNe : nbhdMean T Ap Am g i x = ∑ y ∈ N, πG T Ap Am g i y := by
    unfold nbhdMean
    rw [← sum_filter]
    congr 1
    ext y
    simp only [hN, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    exact fun h => (copyAdj_mem h).2
  have hdeg := hst.copy_deg hx
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  have hTS := hst.T_le_S
  rw [hNe]
  constructor
  · have := card_nsmul_le_sum N (fun y => πG T Ap Am g i y) (c / (3 * lam))
      (fun y hy => (hst.πG_bounds (copyAdj_mem (mem_filter.1 hy).2).2).1)
    rw [nsmul_eq_mul] at this
    calc c ^ 2 * S.card / (3 * lam) = c * S.card * (c / (3 * lam)) := by ring
      _ ≤ N.card * (c / (3 * lam)) := by gcongr; exact hdeg.1
      _ ≤ _ := this
  · have := sum_le_card_nsmul N (fun y => πG T Ap Am g i y) (16 / lam)
      (fun y hy => (hst.πG_bounds (copyAdj_mem (mem_filter.1 hy).2).2).2)
    rw [nsmul_eq_mul] at this
    calc _ ≤ N.card * (16 / lam) := this
      _ ≤ S.card * (16 / lam) := mul_le_mul_of_nonneg_right (hdeg.2.trans hTS) (by positivity)
      _ = 16 * S.card / lam := by ring

end Deterministic

/-! ## Concentration: the scalar events of (5.11) via Lemma 4.3 -/

section Concentration

open Classical Matrix

/-- Lemma 4.3 for `1 × 1` matrices: scalar bounded-support concentration. -/
theorem scalar_conc {ι : Type*} [Fintype ι] (Sset : Finset ι) (ok : (ι → ℝ) → Prop)
    (hok : ∀ h, ok h → (Sset.filter fun i => h i ≠ 0).card ≤ 4)
    (x : ι → ℝ) (μ : FinDist (ι → ℝ)) (hμ : LineProcess ok x μ)
    (a : ι → ℝ) (b ν t : ℝ) (hb : 0 < b) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ b)
    (haS : ∀ i ∉ Sset, a i = 0) (hM : ∑ i, x i * a i ≤ ν) (ht : 0 < t) :
    μ.P (fun z => ∑ i, x i * a i + t ≤ ∑ i, z i * a i) ≤
        Real.exp (-(t ^ 2) / (32 * b * (ν + t))) ∧
      μ.P (fun z => ∑ i, z i * a i ≤ ∑ i, x i * a i - t) ≤
        Real.exp (-(t ^ 2) / (32 * b * (ν + t))) := by
  set A : ι → Matrix (Fin 1) (Fin 1) ℝ := fun i => a i • (1 : Matrix (Fin 1) (Fin 1) ℝ) with hA
  have hsum : ∀ z : ι → ℝ, ∑ i, z i • A i = (∑ i, z i * a i) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    intro z
    simp only [hA, smul_smul, ← Finset.sum_smul]
  have hquad : ∀ (s : ℝ) (v : Fin 1 → ℝ),
      v ⬝ᵥ ((s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) *ᵥ v) = s * (v ⬝ᵥ v) := by
    intro s v
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hvv : ∀ v : Fin 1 → ℝ, 0 ≤ v ⬝ᵥ v := fun v => by
    simp only [dotProduct]
    exact sum_nonneg fun i _ => mul_self_nonneg _
  have hpsd : ∀ i, (A i).PosSemidef := fun i =>
    Matrix.PosSemidef.smul Matrix.PosSemidef.one (ha i).1
  have h := bounded_support_concentration Sset ok hok x μ hμ A hpsd b ν t hb
    (fun i v => by rw [hquad]; exact mul_le_mul_of_nonneg_right (ha i).2 (hvv v))
    (fun i hi => by simp [hA, haS i hi])
    (fun v => by rw [hsum, hquad]; exact mul_le_mul_of_nonneg_right hM (hvv v)) ht
  simp only [Nat.cast_one, one_mul] at h
  set v1 : Fin 1 → ℝ := fun _ => 1 with hv1def
  have hv1 : v1 ⬝ᵥ v1 = 1 := by simp [hv1def, dotProduct]
  constructor
  · refine le_trans (P_mono μ fun z _ hz => ?_) h.1
    refine ⟨v1, hv1, ?_⟩
    rw [hsum, hsum, ← sub_smul, hquad, hv1, mul_one]
    linarith
  · refine le_trans (P_mono μ fun z _ hz => ?_) h.2
    refine ⟨v1, hv1, ?_⟩
    rw [hsum, hsum, ← sub_smul, hquad, hv1, mul_one]
    linarith

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}

/-- Coefficients supported on the ownership variables of the copy `i`. -/
def cvec (i : Fin t) (α : G → ℝ) : (Fin t × G) ⊕ G → ℝ
  | .inl p => if p.1 = i then α p.2 else 0
  | .inr _ => 0

theorem sum_cvec (z : (Fin t × G) ⊕ G → ℝ) (i : Fin t) (α : G → ℝ) :
    ∑ e, z e * cvec i α e = ∑ y, z (.inl (i, y)) * α y := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [cvec, mul_zero, sum_const_zero, add_zero]
  rw [sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The ownership edges of the copy node `i`. -/
def copyEdges (T Ap Am : Finset G) (g : Fin t → G) (i : Fin t) : Finset ((Fin t × G) ⊕ G) :=
  univ.filter fun e => (Γ T Ap Am g).snd e = .inr (.inl i)

theorem cvec_supp {i : Fin t} {α : G → ℝ} (hα : ∀ y ∉ copyVerts Ap Am (g i), α y = 0) :
    ∀ e ∉ copyEdges T Ap Am g i, cvec i α e = 0 := by
  intro e he
  rcases e with ⟨j, y⟩ | w
  · simp only [cvec]
    by_cases hj : j = i
    · rw [ite_eq_left hj]
      subst hj
      apply hα
      intro hy
      apply he
      simp [copyEdges, Γ_snd_inl, hy]
    · rw [ite_eq_right hj]
  · rfl

theorem hok_copy {ok : ((Fin t × G) ⊕ G → ℝ) → Prop}
    (hok : ∀ h, ok h → ∀ v, (univ.filter fun e => h e ≠ 0 ∧
      ((Γ T Ap Am g).fst e = v ∨ (Γ T Ap Am g).snd e = v)).card ≤ 4) (i : Fin t) :
    ∀ h, ok h → ((copyEdges T Ap Am g i).filter fun e => h e ≠ 0).card ≤ 4 := by
  intro h hh
  refine le_trans (card_le_card ?_) (hok h hh (.inr (.inl i)))
  intro e he
  simp only [copyEdges, mem_filter, mem_univ, true_and] at he ⊢
  exact ⟨he.2, Or.inr he.1⟩

theorem sum_xvec_cvec (i : Fin t) (α : G → ℝ) :
    ∑ e, xvec T Ap Am g e * cvec i α e = ∑ y, πG T Ap Am g i y * α y :=
  sum_cvec _ i α

/-- A sum over the whole group of a function supported on the copy. -/
theorem sum_copy_eq {i : Fin t} (φ : G → ℝ) (hφ : ∀ y ∉ copyVerts Ap Am (g i), φ y = 0) :
    ∑ y, φ y = ∑ y ∈ copyVerts Ap Am (g i), φ y :=
  (sum_subset (subset_univ _) (fun y _ hy => hφ y hy)).symm

theorem aG_eq_zero {κ lam : ℝ} {i : Fin t} {x y : G}
    (h : ¬ (copyGraph T Ap Am (g i)).Adj x y) : aG T Ap Am g κ lam i x y = 0 := by
  unfold aG; rw [wG_eq_zero h]; simp

/-- **(5.10)**: the weighted degree has exact mean `D`. -/
theorem Standing.aG_mean (hst : Standing T Ap Am g S c lam) {κ : ℝ} {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    ∑ y, πG T Ap Am g i y * aG T Ap Am g κ lam i x y = Dref T Ap Am κ lam := by
  have hxpos : 0 < xG T Ap Am g i x := lt_of_lt_of_le (by have := hst.c_pos; have := hst.lam_pos; positivity) (hst.xG_bounds hx).1
  have hθ : 0 < θ T := lt_of_lt_of_le (by norm_num) hst.θ_ge
  have hR := hst.Rsum_pos
  have hterm : ∀ y, πG T Ap Am g i y * aG T Ap Am g κ lam i x y =
      κ / lam * wG T Ap Am g i x y / πG T Ap Am g i x := by
    intro y
    by_cases hadj : (copyGraph T Ap Am (g i)).Adj x y
    · have hy : 0 < πG T Ap Am g i y := lt_of_lt_of_le (by have := hst.c_pos; have := hst.lam_pos; positivity) (hst.πG_bounds (copyAdj_mem hadj).2).1
      unfold aG
      field_simp
    · rw [aG_eq_zero hadj, wG_eq_zero hadj]; simp
  simp only [hterm]
  rw [← sum_div, ← mul_sum]
  have hsum : ∑ y, wG T Ap Am g i x y = Rsum T Ap Am * xG T Ap Am g i x := by
    unfold xG; field_simp
  rw [hsum]
  unfold Dref πG
  field_simp

theorem Standing.aG_le_one (hst : Standing T Ap Am g S c lam) (i : Fin t) (x y : G) :
    aG T Ap Am g (c ^ 2 / 18) lam i x y ≤ 1 := by
  by_cases hadj : (copyGraph T Ap Am (g i)).Adj x y
  · exact (hst.aG_bounds hadj).2
  · rw [aG_eq_zero hadj]; norm_num

/-- Size tail of (5.11). -/
theorem prob_size (hst : Standing T Ap Am g S c lam) {μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)}
    (hμ : IsRounding T Ap Am g μ₀) (i : Fin t) :
    μ₀.P (fun z => ¬ sizeOK T Ap Am g i z) ≤
      Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) := by
  obtain ⟨ok, hok, hlp, -⟩ := hμ
  set α : G → ℝ := fun y => if y ∈ copyVerts Ap Am (g i) then 1 else 0 with hα
  set M := ∑ y ∈ copyVerts Ap Am (g i), πG T Ap Am g i y with hM
  have hMlo := hst.size_mean_ge i
  have hMpos : 0 < M := lt_of_lt_of_le (by have := hst.c_pos; have := hst.d_pos; have := hst.lam_pos; positivity) hMlo
  have hmean : ∑ e, xvec T Ap Am g e * cvec i α e = M := by
    rw [sum_xvec_cvec, hM, sum_copy_eq]
    · refine sum_congr rfl fun y hy => ?_; simp [hα, hy]
    · intro y hy; simp [hα, hy]
  have hsz : ∀ z : (Fin t × G) ⊕ G → ℝ, ∑ e, z e * cvec i α e = ∑ x ∈ copyVerts Ap Am (g i), z (.inl (i, x)) := by
    intro z
    rw [sum_cvec, sum_copy_eq]
    · refine sum_congr rfl fun y hy => ?_; simp [hα, hy]
    · intro y hy; simp [hα, hy]
  have h := (scalar_conc (copyEdges T Ap Am g i) ok (hok_copy hok i) _ μ₀ hlp (cvec i α) 1 M
    (M / 2) one_pos (fun e => ?_) (cvec_supp fun y hy => by simp [hα, hy]) hmean.le
    (by positivity)).2
  · refine le_trans (P_mono μ₀ fun z _ hz => ?_) (le_trans h ?_)
    · unfold sizeOK at hz
      rw [hmean, hsz z]
      linarith
    · apply Real.exp_le_exp.2
      have : -(M / 2) ^ 2 / (32 * 1 * (M + M / 2)) = -(M / 192) := by field_simp; ring
      rw [this]
      linarith
  · rcases e with ⟨j, y⟩ | w
    · simp only [cvec]; split_ifs <;> simp [hα] <;> split_ifs <;> norm_num
    · simp [cvec]

/-- Support-count tails of (5.11) at a full-copy vertex. -/
theorem prob_nbhd (hst : Standing T Ap Am g S c lam) {μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)}
    (hμ : IsRounding T Ap Am g μ₀) (i : Fin t) {x : G} (hx : x ∈ copyVerts Ap Am (g i)) :
    μ₀.P (fun z => ¬ nbhdOK T Ap Am g i z x) ≤
      2 * Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) := by
  obtain ⟨ok, hok, hlp, -⟩ := hμ
  set α : G → ℝ := fun y => if (copyGraph T Ap Am (g i)).Adj x y then 1 else 0 with hα
  have hαS : ∀ y ∉ copyVerts Ap Am (g i), α y = 0 := by
    intro y hy
    have : ¬ (copyGraph T Ap Am (g i)).Adj x y := fun h => hy (copyAdj_mem h).2
    simp [hα, this]
  set M := nbhdMean T Ap Am g i x with hM
  obtain ⟨hMlo, -⟩ := hst.nbhdMean_bounds hx
  have hMpos : 0 < M := lt_of_lt_of_le (by have := hst.c_pos; have := hst.d_pos; have := hst.lam_pos; positivity) hMlo
  have hmean : ∑ e, xvec T Ap Am g e * cvec i α e = M := by
    rw [sum_xvec_cvec, hM, sum_copy_eq _ (fun y hy => by rw [hαS y hy, mul_zero])]
    unfold nbhdMean
    refine sum_congr rfl fun y _ => ?_
    simp only [hα]; split_ifs <;> simp
  have hcount : ∀ z : (Fin t × G) ⊕ G → ℝ, ∑ e, z e * cvec i α e = ∑ y ∈ copyVerts Ap Am (g i),
      (if (copyGraph T Ap Am (g i)).Adj x y then z (.inl (i, y)) else 0) := by
    intro z
    rw [sum_cvec, sum_copy_eq _ (fun y hy => by rw [hαS y hy, mul_zero])]
    refine sum_congr rfl fun y _ => ?_
    simp only [hα]; split_ifs <;> simp
  have hα01 : ∀ e, 0 ≤ cvec i α e ∧ cvec i α e ≤ 1 := by
    intro e
    rcases e with ⟨j, y⟩ | w
    · simp only [cvec, hα]; split_ifs <;> norm_num
    · simp [cvec]
  have hlo := (scalar_conc (copyEdges T Ap Am g i) ok (hok_copy hok i) _ μ₀ hlp (cvec i α) 1 M
    (M / 2) one_pos hα01 (cvec_supp hαS) hmean.le (by positivity)).2
  have hhi := (scalar_conc (copyEdges T Ap Am g i) ok (hok_copy hok i) _ μ₀ hlp (cvec i α) 1 M
    M one_pos hα01 (cvec_supp hαS) hmean.le hMpos).1
  have e1 : Real.exp (-(M / 2) ^ 2 / (32 * 1 * (M + M / 2))) ≤
      Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) := by
    apply Real.exp_le_exp.2
    have : -(M / 2) ^ 2 / (32 * 1 * (M + M / 2)) = -(M / 192) := by field_simp; ring
    rw [this]; linarith
  have e2 : Real.exp (-M ^ 2 / (32 * 1 * (M + M))) ≤
      Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) := by
    apply Real.exp_le_exp.2
    have : -M ^ 2 / (32 * 1 * (M + M)) = -(M / 64) := by field_simp; ring
    rw [this]; linarith
  calc μ₀.P (fun z => ¬ nbhdOK T Ap Am g i z x) ≤
        μ₀.P (fun z => (∑ e, z e * cvec i α e ≤ ∑ e, xvec T Ap Am g e * cvec i α e - M / 2) ∨
          ∑ e, xvec T Ap Am g e * cvec i α e + M ≤ ∑ e, z e * cvec i α e) := by
        refine P_mono μ₀ fun z _ hz => ?_
        unfold nbhdOK at hz
        rw [hmean, hcount z]
        rw [← hM] at hz
        by_contra hcon
        push Not at hcon
        exact hz ⟨by linarith [hcon.1], by linarith [hcon.2]⟩
    _ ≤ _ := P_or_le _ _ _
    _ ≤ Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) +
        Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) := add_le_add (hlo.trans e1) (hhi.trans e2)
    _ = _ := by ring

/-- Degree tails of (5.11) at a full-copy vertex, using the exact mean (5.10). -/
theorem prob_deg (hst : Standing T Ap Am g S c lam) {μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)}
    (hμ : IsRounding T Ap Am g μ₀) (i : Fin t) {x : G} (hx : x ∈ copyVerts Ap Am (g i))
    {η : ℝ} (hη : 0 < η) :
    μ₀.P (fun z => ¬ degOK T Ap Am g (c ^ 2 / 18) lam η i z x) ≤
      2 * Real.exp (-((η * Dref T Ap Am (c ^ 2 / 18) lam) ^ 2 /
        (32 * (Dref T Ap Am (c ^ 2 / 18) lam + η * Dref T Ap Am (c ^ 2 / 18) lam)))) := by
  obtain ⟨ok, hok, hlp, -⟩ := hμ
  set D := Dref T Ap Am (c ^ 2 / 18) lam with hD
  have hDpos : 0 < D :=
    lt_of_lt_of_le (by have := hst.c_pos; have := hst.d_pos; have := hst.lam_pos; positivity)
      (Dref_bounds' hst (κ := c ^ 2 / 18) (by have := hst.c_pos; positivity)).1
  set α : G → ℝ := fun y => aG T Ap Am g (c ^ 2 / 18) lam i x y with hα
  have hαS : ∀ y ∉ copyVerts Ap Am (g i), α y = 0 := by
    intro y hy
    exact aG_eq_zero fun h => hy (copyAdj_mem h).2
  have hkl : 0 ≤ c ^ 2 / 18 / lam := by have := hst.lam_pos; positivity
  have hα01 : ∀ e, 0 ≤ cvec i α e ∧ cvec i α e ≤ 1 := by
    intro e
    rcases e with ⟨j, y⟩ | w
    · simp only [cvec]
      split_ifs
      · exact ⟨aG_nonneg T Ap Am g hkl _ _ _, hst.aG_le_one _ _ _⟩
      · norm_num
    · simp [cvec]
  have hmean : ∑ e, xvec T Ap Am g e * cvec i α e = D := by
    rw [sum_xvec_cvec]
    exact hst.aG_mean hx
  have hdeg : ∀ z : (Fin t × G) ⊕ G → ℝ, ∑ e, z e * cvec i α e =
      ∑ y ∈ copyVerts Ap Am (g i), z (.inl (i, y)) * aG T Ap Am g (c ^ 2 / 18) lam i x y := by
    intro z
    rw [sum_cvec, sum_copy_eq _ (fun y hy => by rw [hαS y hy, mul_zero])]
  have hc := scalar_conc (copyEdges T Ap Am g i) ok (hok_copy hok i) _ μ₀ hlp (cvec i α) 1 D
    (η * D) one_pos hα01 (cvec_supp hαS) hmean.le (by positivity)
  simp only [mul_one] at hc
  calc μ₀.P (fun z => ¬ degOK T Ap Am g (c ^ 2 / 18) lam η i z x) ≤
        μ₀.P (fun z => ∑ e, xvec T Ap Am g e * cvec i α e + η * D ≤ ∑ e, z e * cvec i α e ∨
          ∑ e, z e * cvec i α e ≤ ∑ e, xvec T Ap Am g e * cvec i α e - η * D) := by
        refine P_mono μ₀ fun z _ hz => ?_
        unfold degOK at hz
        rw [hmean, hdeg z]
        rw [← hD] at hz
        by_contra hcon
        push Not at hcon
        exact hz (abs_le.2 ⟨by linarith [hcon.2], by linarith [hcon.1]⟩)
    _ ≤ _ := P_or_le _ _ _
    _ ≤ _ := add_le_add hc.1 hc.2
    _ = _ := by ring_nf

end Concentration

/-! ## Linear algebra for the spectral event: (2.1), (2.3)–(2.4), duality -/

section PosPart

open Matrix

/-- **Positive part (2.3).** For a real symmetric `E` with `vᵀEv ≤ ν|v|²` (`ν ≥ 0`), the positive
part `E₊ = YYᵀ` satisfies `E ⪯ E₊`, `‖E₊‖ = ‖YᵀY‖ ≤ ν`, and `(E₊)_{kk}² ≤ (E²)_{kk}`. -/
theorem posPart_factor {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℝ)
    (hE : E.IsHermitian) {ν : ℝ} (hν : 0 ≤ ν)
    (hle : ∀ v : n → ℝ, v ⬝ᵥ (E *ᵥ v) ≤ ν * (v ⬝ᵥ v)) :
    ∃ Y : Matrix n n ℝ,
      (∀ v : n → ℝ, v ⬝ᵥ (E *ᵥ v) ≤ ∑ j, (∑ k, Y k j * v k) ^ 2) ∧
      (∀ w : n → ℝ, ∑ k, (∑ j, Y k j * w j) ^ 2 ≤ ν * ∑ j, w j ^ 2) ∧
      (∀ k, (∑ j, Y k j ^ 2) ^ 2 ≤ ∑ l, E k l ^ 2) := by
  set U : Matrix n n ℝ := (hE.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  set lam := hE.eigenvalues with hlam
  have horth : ∀ i j, ∑ k, U k i * U k j = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun (Unitary.coe_star_mul_self hE.eigenvectorUnitary) i) j
    simpa [hUdef, Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  have hcomp : ∀ k l, ∑ j, U k j * U l j = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun (Unitary.coe_mul_star_self hE.eigenvectorUnitary) k) l
    simpa [hUdef, Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  have heig : ∀ j k, ∑ m, E k m * U m j = lam j * U k j := by
    intro j k
    have h := congrFun (hE.mulVec_eigenvectorBasis j) k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simpa [hUdef, Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have hdecomp : ∀ k l, E k l = ∑ j, lam j * U k j * U l j := by
    intro k l
    calc E k l = ∑ m, E k m * (if m = l then 1 else 0) := by simp
      _ = ∑ m, E k m * ∑ j, U m j * U l j := by simp_rw [hcomp]
      _ = ∑ j, (∑ m, E k m * U m j) * U l j := by
          simp_rw [mul_sum, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun j _ => sum_congr rfl fun m _ => by ring
      _ = ∑ j, lam j * U k j * U l j := by simp_rw [heig]
  -- Parseval in both directions
  have pars1 : ∀ s : n → ℝ, ∑ k, (∑ j, U k j * s j) ^ 2 = ∑ j, s j ^ 2 := by
    intro s
    calc ∑ k, (∑ j, U k j * s j) ^ 2 = ∑ k, ∑ j, ∑ i, U k j * s j * (U k i * s i) := by
          refine sum_congr rfl fun k _ => ?_
          rw [sq, sum_mul_sum]
      _ = ∑ j, ∑ i, s j * s i * ∑ k, U k j * U k i := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by ring
      _ = ∑ j, s j ^ 2 := by
          refine sum_congr rfl fun j _ => ?_
          simp only [horth, mul_ite, mul_one, mul_zero]
          rw [sum_ite_eq]
          simp [sq]
  have pars2 : ∀ v : n → ℝ, ∑ j, (∑ k, U k j * v k) ^ 2 = ∑ k, v k ^ 2 := by
    intro v
    calc ∑ j, (∑ k, U k j * v k) ^ 2 = ∑ j, ∑ k, ∑ l, U k j * v k * (U l j * v l) := by
          refine sum_congr rfl fun j _ => ?_
          rw [sq, sum_mul_sum]
      _ = ∑ k, ∑ l, v k * v l * ∑ j, U k j * U l j := by
          rw [sum_comm]
          refine sum_congr rfl fun k _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ = ∑ k, v k ^ 2 := by
          refine sum_congr rfl fun k _ => ?_
          simp only [hcomp, mul_ite, mul_one, mul_zero]
          rw [sum_ite_eq]
          simp [sq]
  have hquad : ∀ v : n → ℝ, v ⬝ᵥ (E *ᵥ v) = ∑ j, lam j * (∑ k, U k j * v k) ^ 2 := by
    intro v
    have : ∀ j, lam j * (∑ k, U k j * v k) ^ 2 =
        ∑ k, ∑ l, v k * (lam j * U k j * U l j * v l) := by
      intro j
      rw [sq, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun l _ => by ring
    simp_rw [this]
    rw [sum_comm]
    simp only [dotProduct, Matrix.mulVec]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [hdecomp, sum_mul, mul_sum]
  have hlamle : ∀ j, lam j ≤ ν := by
    intro j
    have h := hle (fun k => U k j)
    rw [hquad] at h
    have e1 : (fun k => U k j) ⬝ᵥ (fun k => U k j) = 1 := by
      simp only [dotProduct]
      rw [horth]; simp
    have e2 : ∀ i, ∑ k, U k i * U k j = if i = j then 1 else 0 := fun i => horth i j
    simp only [e2, e1] at h
    simpa using h
  set lp : n → ℝ := fun j => max (lam j) 0 with hlp
  refine ⟨Matrix.of fun k j => U k j * √(lp j), ?_, ?_, ?_⟩
  · intro v
    rw [hquad]
    refine sum_le_sum fun j _ => ?_
    simp only [Matrix.of_apply]
    have : ∑ k, U k j * √(lp j) * v k = √(lp j) * ∑ k, U k j * v k := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    rw [this, mul_pow, Real.sq_sqrt (le_max_right _ _)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · intro w
    simp only [Matrix.of_apply]
    have : ∀ k, ∑ j, U k j * √(lp j) * w j = ∑ j, U k j * (√(lp j) * w j) :=
      fun k => sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [pars1, mul_sum]
    refine sum_le_sum fun j _ => ?_
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]
    exact mul_le_mul_of_nonneg_right (max_le (hlamle j) hν) (sq_nonneg _)
  · intro k
    simp only [Matrix.of_apply]
    have hrow : ∑ l, E k l ^ 2 = ∑ j, (lam j * U k j) ^ 2 := by
      simp_rw [hdecomp]
      have : ∀ l, ∑ j, lam j * U k j * U l j = ∑ j, U l j * (lam j * U k j) :=
        fun l => sum_congr rfl fun j _ => by ring
      simp_rw [this]
      exact pars1 _
    have hsq : ∑ j, (U k j * √(lp j)) ^ 2 = ∑ j, U k j * (U k j * lp j) := by
      refine sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]; ring
    rw [hsq, hrow]
    calc (∑ j, U k j * (U k j * lp j)) ^ 2
        ≤ (∑ j, U k j ^ 2) * ∑ j, (U k j * lp j) ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ j, (U k j * lp j) ^ 2 := by
          have : ∑ j, U k j ^ 2 = 1 := by
            have := hcomp k k
            rw [ite_eq_left rfl] at this
            rw [← this]; exact sum_congr rfl fun j _ => by ring
          rw [this, one_mul]
      _ ≤ ∑ j, (lam j * U k j) ^ 2 := by
          refine sum_le_sum fun j _ => ?_
          rw [mul_pow, mul_pow, mul_comm]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          rcases le_total 0 (lam j) with h | h
          · rw [show lp j = lam j from max_eq_left h]
          · rw [show lp j = 0 from max_eq_right h]
            nlinarith [sq_nonneg (lam j)]

section Spectral

variable {n : Type*} [Fintype n]

/-- Weighted degrees. -/
def degw (w : n → n → ℝ) (k : n) : ℝ := ∑ l, w k l

/-- Volume. -/
def volw (w : n → n → ℝ) : ℝ := ∑ k, degw w k

/-- `E = B - uuᵀ`, where `B = D^{-1/2} W D^{-1/2}` is the normalized adjacency matrix and
`u = D^{1/2} 𝟙 / √vol` its top eigenvector (Section 2.1). -/
def Emat (w : n → n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun k l => w k l / (√(degw w k) * √(degw w l)) - √(degw w k) * √(degw w l) / volw w

theorem Emat_isHermitian {w : n → n → ℝ} (hsymm : ∀ k l, w k l = w l k) :
    (Emat w).IsHermitian := by
  ext k l
  simp only [Matrix.conjTranspose_apply, Emat, Matrix.of_apply, star_trivial]
  rw [hsymm, mul_comm (√(degw w l))]

/-- **(2.1) ⇒ `λ₂(B) ≤ 1 - σ`.** The variational gap `σ` gives `vᵀ(B - uuᵀ)v ≤ (1 - σ)|v|²`. -/
theorem quad_Emat (w : n → n → ℝ) (hsymm : ∀ k l, w k l = w l k)
    (hd : ∀ k, 0 < degw w k) (hV : 0 < volw w) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hgap : ∀ f : n → ℝ, ∃ z, σ * ∑ k, degw w k * (f k - z) ^ 2 ≤
      (∑ k, ∑ l, w k l * (f k - f l) ^ 2) / 2) :
    ∀ v : n → ℝ, v ⬝ᵥ (Emat w *ᵥ v) ≤ (1 - σ) * (v ⬝ᵥ v) := by
  intro v
  set d := degw w with hd_def
  set V := volw w with hV_def
  have hs : ∀ k, 0 < √(d k) := fun k => Real.sqrt_pos.2 (hd k)
  have hsq : ∀ k, √(d k) * √(d k) = d k := fun k => Real.mul_self_sqrt (hd k).le
  set f : n → ℝ := fun k => v k / √(d k) with hf
  have hvf : ∀ k, v k = √(d k) * f k := fun k => by
    simp only [hf]; field_simp [(hs k).ne']
  have hq : v ⬝ᵥ (Emat w *ᵥ v) =
      ∑ k, ∑ l, w k l * f k * f l - (∑ k, d k * f k) ^ 2 / V := by
    simp only [dotProduct, Matrix.mulVec, Emat, Matrix.of_apply, ← hd_def, ← hV_def]
    have hterm : ∀ k l, v k * ((w k l / (√(d k) * √(d l)) - √(d k) * √(d l) / V) * v l) =
        w k l * f k * f l - d k * f k * (d l * f l) / V := by
      intro k l
      have key : ∀ s s' ww VV fk fl : ℝ, s ≠ 0 → s' ≠ 0 → VV ≠ 0 →
          s * fk * ((ww / (s * s') - s * s' / VV) * (s' * fl)) =
            ww * fk * fl - (s * s) * fk * ((s' * s') * fl) / VV := by
        intros; field_simp
      rw [hvf k, hvf l, key _ _ _ _ _ _ (hs k).ne' (hs l).ne' hV.ne', hsq k, hsq l]
    simp_rw [mul_sum, hterm, sum_sub_distrib]
    congr 1
    rw [sq, sum_mul_sum, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_div]
  have hvv : v ⬝ᵥ v = ∑ k, d k * f k ^ 2 := by
    simp only [dotProduct]
    refine sum_congr rfl fun k _ => ?_
    rw [hvf k, show √(d k) * f k * (√(d k) * f k) = (√(d k) * √(d k)) * f k ^ 2 by ring, hsq k]
  have hdir : (∑ k, ∑ l, w k l * (f k - f l) ^ 2) / 2 =
      ∑ k, d k * f k ^ 2 - ∑ k, ∑ l, w k l * f k * f l := by
    have e1 : ∑ k, ∑ l, w k l * f l ^ 2 = ∑ k, d k * f k ^ 2 := by
      rw [sum_comm]
      refine sum_congr rfl fun l _ => ?_
      simp only [hd_def, degw, sum_mul]
      exact sum_congr rfl fun k _ => by rw [hsymm]
    have e2 : ∑ k, ∑ l, w k l * f k ^ 2 = ∑ k, d k * f k ^ 2 := by
      refine sum_congr rfl fun k _ => ?_
      simp only [hd_def, degw, sum_mul]
    have : ∑ k, ∑ l, w k l * (f k - f l) ^ 2 =
        ∑ k, ∑ l, w k l * f k ^ 2 + ∑ k, ∑ l, w k l * f l ^ 2 -
          2 * ∑ k, ∑ l, w k l * f k * f l := by
      simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
    rw [this, e1, e2]; ring
  obtain ⟨z, hz⟩ := hgap f
  rw [hdir] at hz
  set X := ∑ k, d k * f k ^ 2
  set Aw := ∑ k, ∑ l, w k l * f k * f l
  set Sm := ∑ k, d k * f k
  have hmin : X - Sm ^ 2 / V ≤ ∑ k, d k * (f k - z) ^ 2 := by
    have e : ∑ k, d k * (f k - z) ^ 2 = X - 2 * z * Sm + z ^ 2 * V := by
      simp only [X, Sm, hV_def, volw, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [e]
    have : 0 ≤ (z * V - Sm) ^ 2 / V := div_nonneg (sq_nonneg _) hV.le
    have e2 : (z * V - Sm) ^ 2 / V = z ^ 2 * V - 2 * z * Sm + Sm ^ 2 / V := by
      field_simp; ring
    linarith
  rw [hq, hvv]
  have h1 := mul_le_mul_of_nonneg_left hmin hσ0
  have h2 : 0 ≤ (1 - σ) * (Sm ^ 2 / V) :=
    mul_nonneg (by linarith) (div_nonneg (sq_nonneg _) hV.le)
  nlinarith

/-- **(2.4)**: the squared row norms of `E = B - uuᵀ` are small when weights are bounded, degrees
are large, and supports are small. -/
theorem row_Emat (w : n → n → ℝ) (hnn : ∀ k l, 0 ≤ w k l) (hd : ∀ k, 0 < degw w k)
    (hV : 0 < volw w) {W dmin N : ℝ} (hW : ∀ k l, w k l ≤ W) (hdmin : ∀ k, dmin ≤ degw w k)
    (hdmin0 : 0 < dmin) (hN : ∀ k, ((univ.filter fun l => w k l ≠ 0).card : ℝ) ≤ N) (k : n) :
    ∑ l, Emat w k l ^ 2 ≤ 2 * (N * (W ^ 2 / dmin ^ 2)) + 2 * (degw w k / volw w) := by
  classical
  set d := degw w with hd_def
  set V := volw w with hV_def
  have hs : ∀ k, 0 < √(d k) := fun k => Real.sqrt_pos.2 (hd k)
  have hsq : ∀ k, √(d k) * √(d k) = d k := fun k => Real.mul_self_sqrt (hd k).le
  have h1 : ∀ l, Emat w k l ^ 2 ≤ 2 * (w k l / (√(d k) * √(d l))) ^ 2 +
      2 * (√(d k) * √(d l) / V) ^ 2 := by
    intro l
    simp only [Emat, Matrix.of_apply]
    nlinarith [sq_nonneg (w k l / (√(d k) * √(d l)) + √(d k) * √(d l) / V)]
  have hA : ∀ l, (w k l / (√(d k) * √(d l))) ^ 2 ≤
      if w k l ≠ 0 then W ^ 2 / dmin ^ 2 else 0 := by
    intro l
    split_ifs with hw
    · rw [div_pow, mul_pow, Real.sq_sqrt (hd k).le, Real.sq_sqrt (hd l).le]
      have hWnn : 0 ≤ W := (hnn k l).trans (hW k l)
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (hnn k l) (hW k l) 2) (by positivity)
      nlinarith [hdmin k, hdmin l, mul_le_mul (hdmin k) (hdmin l) hdmin0.le (hd k).le]
    · push Not at hw; rw [hw]; simp
  have hB : ∑ l, (√(d k) * √(d l) / V) ^ 2 = d k / V := by
    have : ∀ l, (√(d k) * √(d l) / V) ^ 2 = d k * d l / V ^ 2 := fun l => by
      rw [div_pow, mul_pow, Real.sq_sqrt (hd k).le, Real.sq_sqrt (hd l).le]
    simp_rw [this]
    rw [← sum_div, ← mul_sum]
    show d k * V / V ^ 2 = d k / V
    field_simp
  calc ∑ l, Emat w k l ^ 2 ≤ ∑ l, (2 * (w k l / (√(d k) * √(d l))) ^ 2 +
        2 * (√(d k) * √(d l) / V) ^ 2) := sum_le_sum fun l _ => h1 l
    _ = 2 * ∑ l, (w k l / (√(d k) * √(d l))) ^ 2 + 2 * ∑ l, (√(d k) * √(d l) / V) ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 2 * (N * (W ^ 2 / dmin ^ 2)) + 2 * (d k / V) := by
        rw [hB]
        gcongr
        calc ∑ l, (w k l / (√(d k) * √(d l))) ^ 2
            ≤ ∑ l, (if w k l ≠ 0 then W ^ 2 / dmin ^ 2 else 0) := sum_le_sum fun l _ => hA l
          _ = (univ.filter fun l => w k l ≠ 0).card * (W ^ 2 / dmin ^ 2) := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ N * (W ^ 2 / dmin ^ 2) := by gcongr; exact hN k

/-- Duality: `‖N‖ = ‖Nᵀ‖`, in quadratic-form terms. -/
theorem dual_bound {m q : Type*} [Fintype m] [Fintype q] (N : m → q → ℝ) {c' : ℝ} (hc' : 0 ≤ c')
    (hN : ∀ w : q → ℝ, ∑ k, (∑ j, N k j * w j) ^ 2 ≤ c' * ∑ j, w j ^ 2) (h : m → ℝ) :
    ∑ j, (∑ k, N k j * h k) ^ 2 ≤ c' * ∑ k, h k ^ 2 := by
  set w : q → ℝ := fun j => ∑ k, N k j * h k with hw
  set A := ∑ j, w j ^ 2 with hA
  have hA' : A = ∑ k, h k * ∑ j, N k j * w j := by
    simp only [hA, sq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    simp only [hw, sum_mul]
    exact sum_congr rfl fun k _ => by ring
  have hcs : A ^ 2 ≤ (∑ k, h k ^ 2) * ∑ k, (∑ j, N k j * w j) ^ 2 := by
    rw [hA']; exact sum_mul_sq_le_sq_mul_sq _ _ _
  have hH : 0 ≤ ∑ k, h k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have h2 := mul_le_mul_of_nonneg_left (hN w) hH
  have hA0 : 0 ≤ A := sum_nonneg fun j _ => sq_nonneg _
  show A ≤ c' * ∑ k, h k ^ 2
  rcases hA0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : A * A ≤ (c' * ∑ k, h k ^ 2) * A := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end Spectral

end PosPart

/-! ## The spectral event (5.12)–(5.14) -/

section CopyCoords

open Classical Matrix

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}

/-- Copy coordinates `Fin m ≃ V(F)`. -/
def eF (Ap Am : Finset G) : Fin (Ap ∪ Am).card ≃ ↥(Ap ∪ Am) := (Ap ∪ Am).equivFin.symm

/-- The vertex `g_i a_k` of the copy `i`. -/
def vtx (Ap Am : Finset G) (g : Fin t → G) (i : Fin t) (k : Fin (Ap ∪ Am).card) : G :=
  g i * (eF Ap Am k : G)

/-- The full-copy weights `w_{i,e}` in copy coordinates. -/
def wF (T Ap Am : Finset G) (g : Fin t → G) (i : Fin t) (k l : Fin (Ap ∪ Am).card) : ℝ :=
  wG T Ap Am g i (vtx Ap Am g i k) (vtx Ap Am g i l)

theorem sum_copy_fin (i : Fin t) (φ : G → ℝ) :
    ∑ x ∈ copyVerts Ap Am (g i), φ x = ∑ k, φ (vtx Ap Am g i k) := by
  unfold copyVerts
  rw [sum_image (fun a _ b _ h => mul_left_cancel h)]
  rw [← sum_coe_sort (Ap ∪ Am) (fun a => φ (g i * a))]
  exact (Equiv.sum_comp (eF Ap Am) (fun a : ↥(Ap ∪ Am) => φ (g i * (a : G)))).symm

theorem vtx_mem (i : Fin t) (k : Fin (Ap ∪ Am).card) :
    vtx Ap Am g i k ∈ copyVerts Ap Am (g i) :=
  mem_copyVerts.2 (by simp [vtx])

theorem wF_symm (i : Fin t) (k l : Fin (Ap ∪ Am).card) :
    wF T Ap Am g i k l = wF T Ap Am g i l k := wG_symm i _ _

theorem wF_nonneg (i : Fin t) (k l : Fin (Ap ∪ Am).card) : 0 ≤ wF T Ap Am g i k l :=
  wG_nonneg i _ _

theorem degw_wF (hst : Standing T Ap Am g S c lam) (i : Fin t) (k : Fin (Ap ∪ Am).card) :
    degw (wF T Ap Am g i) k = Rsum T Ap Am / θ T * πG T Ap Am g i (vtx Ap Am g i k) := by
  have hθ : 0 < θ T := lt_of_lt_of_le (by norm_num) hst.θ_ge
  have hR := hst.Rsum_pos
  unfold degw wF
  rw [← sum_copy_fin i (fun y => wG T Ap Am g i (vtx Ap Am g i k) y)]
  rw [← sum_copy_eq _ (fun y hy => wG_eq_zero fun h => hy (copyAdj_mem h).2)]
  unfold πG xG
  field_simp

theorem degw_wF_bounds (hst : Standing T Ap Am g S c lam) (i : Fin t) (k : Fin (Ap ∪ Am).card) :
    c * S.card / (2 * lam) ≤ degw (wF T Ap Am g i) k ∧
      degw (wF T Ap Am g i) k ≤ 2 * S.card / lam := by
  have h := hst.sumwG_bounds (vtx_mem (g := g) i k)
  have hdeg : degw (wF T Ap Am g i) k = ∑ y, wG T Ap Am g i (vtx Ap Am g i k) y := by
    unfold degw wF
    rw [← sum_copy_fin i (fun y => wG T Ap Am g i (vtx Ap Am g i k) y)]
    rw [← sum_copy_eq _ (fun y hy => wG_eq_zero fun h => hy (copyAdj_mem h).2)]
  rw [hdeg]
  refine ⟨h.1, h.2.trans ?_⟩
  have := hst.T_le_S; have := hst.lam_pos
  gcongr

/-- **Weight comparison.** The weighted full copy inherits a quarter of the template gap:
multiplying the edge weights by factors in `[ρ/2, 2ρ]` changes the gap (2.1) by at most a
factor four. -/
theorem wF_gap (hst : Standing T Ap Am g S c lam) (i : Fin t) :
    ∀ f : Fin (Ap ∪ Am).card → ℝ, ∃ z, (c / Real.log (Fintype.card G) ^ 2 / 4) *
      ∑ k, degw (wF T Ap Am g i) k * (f k - z) ^ 2 ≤
        (∑ k, ∑ l, wF T Ap Am g i k l * (f k - f l) ^ 2) / 2 := by
  intro f
  set σT := c / Real.log (Fintype.card G) ^ 2 with hσT
  have hσT0 : 0 ≤ σT := by have := hst.c_pos; positivity
  have hlam := hst.lam_pos
  set H := (WGraph.ofSimpleGraph (templateGraph T Ap Am)).induce (Ap ∪ Am) with hH
  obtain ⟨z, hz⟩ := hst.temp.gap (fun a => f ((eF Ap Am).symm a))
  refine ⟨z, ?_⟩
  set w1 : Fin (Ap ∪ Am).card → Fin (Ap ∪ Am).card → ℝ :=
    fun k l => if (templateGraph T Ap Am).Adj (eF Ap Am k) (eF Ap Am l) then 1 else 0 with hw1
  have hHw : ∀ a b : ↥(Ap ∪ Am), H.w a b =
      if (templateGraph T Ap Am).Adj a b then 1 else 0 := fun a b => rfl
  have hsumF : ∀ F : ↥(Ap ∪ Am) → ℝ, ∑ a, F a = ∑ k, F (eF Ap Am k) :=
    fun F => (Equiv.sum_comp (eF Ap Am) F).symm
  have hz' : σT * ∑ k, (∑ l, w1 k l) * (f k - z) ^ 2 ≤
      (∑ k, ∑ l, w1 k l * (f k - f l) ^ 2) / 2 := by
    have e1 : ∑ x, H.deg x * ((fun a => f ((eF Ap Am).symm a)) x - z) ^ 2 =
        ∑ k, (∑ l, w1 k l) * (f k - z) ^ 2 := by
      rw [hsumF]
      refine sum_congr rfl fun k _ => ?_
      unfold WGraph.deg
      rw [hsumF]
      simp [hHw, hw1]
    have e2 : H.dirichlet (fun a => f ((eF Ap Am).symm a)) =
        (∑ k, ∑ l, w1 k l * (f k - f l) ^ 2) / 2 := by
      unfold WGraph.dirichlet
      congr 1
      rw [hsumF]
      refine sum_congr rfl fun k _ => ?_
      rw [hsumF]
      simp [hHw, hw1]
    rw [← e1, ← e2]
    exact hz
  have hwlo : ∀ k l, 1 / (2 * lam) * w1 k l ≤ wF T Ap Am g i k l := by
    intro k l
    simp only [hw1]
    split_ifs with h
    · rw [mul_one]
      exact (hst.wG_bounds (i := i) (x := vtx Ap Am g i k) (y := vtx Ap Am g i l)
        (by simpa [copyAdj_iff, vtx] using h)).1
    · rw [mul_zero]; exact wF_nonneg i k l
  have hwhi : ∀ k l, wF T Ap Am g i k l ≤ 2 / lam * w1 k l := by
    intro k l
    simp only [hw1]
    split_ifs with h
    · rw [mul_one]
      exact (hst.wG_bounds (i := i) (x := vtx Ap Am g i k) (y := vtx Ap Am g i l)
        (by simpa [copyAdj_iff, vtx] using h)).2
    · rw [mul_zero]
      have : ¬ (copyGraph T Ap Am (g i)).Adj (vtx Ap Am g i k) (vtx Ap Am g i l) := by
        simpa [copyAdj_iff, vtx] using h
      exact (wG_eq_zero this).le
  calc σT / 4 * ∑ k, degw (wF T Ap Am g i) k * (f k - z) ^ 2
      ≤ σT / 4 * ∑ k, (2 / lam * ∑ l, w1 k l) * (f k - z) ^ 2 := by
        gcongr with k
        unfold degw
        rw [mul_sum]
        exact sum_le_sum fun l _ => hwhi k l
    _ = 1 / (2 * lam) * (σT * ∑ k, (∑ l, w1 k l) * (f k - z) ^ 2) := by
        rw [mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
    _ ≤ 1 / (2 * lam) * ((∑ k, ∑ l, w1 k l * (f k - f l) ^ 2) / 2) := by gcongr
    _ ≤ (∑ k, ∑ l, wF T Ap Am g i k l * (f k - f l) ^ 2) / 2 := by
        have hcmp : 1 / (2 * lam) * (∑ k, ∑ l, w1 k l * (f k - f l) ^ 2) ≤
            ∑ k, ∑ l, wF T Ap Am g i k l * (f k - f l) ^ 2 := by
          rw [mul_sum]
          refine sum_le_sum fun k _ => ?_
          rw [mul_sum]
          refine sum_le_sum fun l _ => ?_
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hwlo k l) (sq_nonneg _)
        linarith

end CopyCoords

section GapEvent

open Classical Matrix

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}

theorem qf_sum_smul {ι : Type*} [Fintype ι] {q : ℕ} (a : ι → ℝ)
    (A : ι → Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) :
    v ⬝ᵥ ((∑ e, a e • A e) *ᵥ v) = ∑ e, a e * (v ⬝ᵥ (A e *ᵥ v)) := by
  rw [sum_mulVec, dotProduct_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem qf_vecMulVec {q : ℕ} (a v : Fin q → ℝ) :
    v ⬝ᵥ (vecMulVec a a *ᵥ v) = (∑ j, a j * v j) ^ 2 := by
  simp only [dotProduct, mulVec, vecMulVec, of_apply]
  rw [sq, sum_mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-- From `¬ λ_max(A) ≥ t`: `vᵀAv ≤ t|v|²` for all `v`. -/
theorem quad_of_not_lamMaxGe {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (t : ℝ)
    (h : ¬ LamMaxGe A t) (v : Fin q → ℝ) : v ⬝ᵥ (A *ᵥ v) ≤ t * (v ⬝ᵥ v) := by
  have hvv : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]; exact sum_nonneg fun i _ => mul_self_nonneg _
  rcases hvv.eq_or_lt with h0 | hpos
  · have hv : v = 0 := dotProduct_self_eq_zero.1 h0.symm
    subst hv; simp
  · set s := √(v ⬝ᵥ v) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hpos
    have hss : s * s = v ⬝ᵥ v := Real.mul_self_sqrt hpos.le
    set u := s⁻¹ • v with hu
    have huu : u ⬝ᵥ u = 1 := by
      rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
      field_simp
    have hlt : u ⬝ᵥ (A *ᵥ u) < t := by
      by_contra hc; push Not at hc; exact h ⟨u, huu, hc⟩
    have : u ⬝ᵥ (A *ᵥ u) = (v ⬝ᵥ (A *ᵥ v)) / (v ⬝ᵥ v) := by
      rw [hu, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
      field_simp
    rw [this, div_lt_iff₀ hpos] at hlt
    exact hlt.le

/-- **(5.12) and interlacing, variationally.** On the event that the matrix sum of (5.13) is
at most `c'` in norm, the weights (5.8) restricted to `V_i` have quadratic form at most
`c' D ‖f‖²` on functions with zero sum over `V_i`. -/
theorem gapOK_of_event (hst : Standing T Ap Am g S c lam) (i : Fin t)
    {z : (Fin t × G) ⊕ G → ℝ} (h01 : ∀ e, z e = 0 ∨ z e = 1) {κ : ℝ} (hκ : 0 ≤ κ / lam)
    (Y : Matrix (Fin (Ap ∪ Am).card) (Fin (Ap ∪ Am).card) ℝ)
    (hY : ∀ v, v ⬝ᵥ (Emat (wF T Ap Am g i) *ᵥ v) ≤ ∑ j, (∑ k, Y k j * v k) ^ 2)
    {c' : ℝ} (hc' : 0 ≤ c')
    (hZ : ∀ w : Fin (Ap ∪ Am).card → ℝ, ∑ k, z (.inl (i, vtx Ap Am g i k)) *
      (πG T Ap Am g i (vtx Ap Am g i k))⁻¹ * (∑ j, Y k j * w j) ^ 2 ≤ c' * ∑ j, w j ^ 2) :
    ∀ f : G → ℝ, ∑ x ∈ partZ Ap Am g z i, f x = 0 →
      ∑ x ∈ partZ Ap Am g z i, ∑ y ∈ partZ Ap Am g z i, aG T Ap Am g κ lam i x y * f x * f y ≤
        c' * Dref T Ap Am κ lam * ∑ x ∈ partZ Ap Am g z i, f x ^ 2 := by
  intro f hf
  set p : Fin (Ap ∪ Am).card → ℝ := fun k => πG T Ap Am g i (vtx Ap Am g i k) with hp_def
  set zk : Fin (Ap ∪ Am).card → ℝ := fun k => z (.inl (i, vtx Ap Am g i k)) with hzk
  set F : Fin (Ap ∪ Am).card → ℝ := fun k => f (vtx Ap Am g i k) with hF
  have hp : ∀ k, 0 < p k := fun k => lt_of_lt_of_le
    (by have := hst.c_pos; have := hst.lam_pos; positivity) (hst.πG_bounds (vtx_mem i k)).1
  have hz01 : ∀ k, zk k = 0 ∨ zk k = 1 := fun k => h01 _
  have hzz : ∀ k, zk k * zk k = zk k := fun k => by
    rcases hz01 k with h | h <;> rw [h] <;> norm_num
  have hP : ∀ φ : G → ℝ, ∑ x ∈ partZ Ap Am g z i, φ x = ∑ k, zk k * φ (vtx Ap Am g i k) := by
    intro φ
    rw [partZ, sum_filter, sum_copy_fin]
    refine sum_congr rfl fun k _ => ?_
    rcases hz01 k with h | h
    · simp only [hzk] at h; simp [h, hzk]
    · simp only [hzk] at h; simp [h, hzk]
  have hθ : 0 < θ T := lt_of_lt_of_le (by norm_num) hst.θ_ge
  have hR := hst.Rsum_pos
  set r := Rsum T Ap Am / θ T with hr_def
  have hr : 0 < r := div_pos hR hθ
  have hdeg : ∀ k, degw (wF T Ap Am g i) k = r * p k := degw_wF hst i
  have hsd : ∀ k, √(degw (wF T Ap Am g i) k) = √r * √(p k) := fun k => by
    rw [hdeg, Real.sqrt_mul hr.le]
  have hsp : ∀ k, √(p k) * √(p k) = p k := fun k => Real.mul_self_sqrt (hp k).le
  have hsr : √r * √r = r := Real.mul_self_sqrt hr.le
  have hsp0 : ∀ k, 0 < √(p k) := fun k => Real.sqrt_pos.2 (hp k)
  have hsr0 : 0 < √r := Real.sqrt_pos.2 hr
  set v : Fin (Ap ∪ Am).card → ℝ := fun k => zk k * F k / √(p k) with hv
  set V := volw (wF T Ap Am g i) with hVdef
  have hsum0 : ∑ k, zk k * F k = 0 := by rw [← hP f]; exact hf
  -- the quadratic form of `E` on `v`
  have hvE : v ⬝ᵥ (Emat (wF T Ap Am g i) *ᵥ v) =
      (1 / r) * ∑ k, ∑ l, zk k * zk l * (wF T Ap Am g i k l / (p k * p l)) * F k * F l := by
    simp only [dotProduct, mulVec, Emat, of_apply, hsd, ← hVdef]
    have key : ∀ (s s' tt zz zz' ff ff' ww VV : ℝ), s ≠ 0 → s' ≠ 0 → tt ≠ 0 →
        zz * ff / s * ((ww / (tt * s * (tt * s')) - tt * s * (tt * s') / VV) * (zz' * ff' / s')) =
          1 / (tt * tt) * (zz * zz' * (ww / ((s * s) * (s' * s'))) * ff * ff') -
            tt * (zz * ff) * (tt * (zz' * ff')) / VV := by
      intros; field_simp
    have hterm : ∀ k l, v k * ((wF T Ap Am g i k l / (√r * √(p k) * (√r * √(p l))) -
        √r * √(p k) * (√r * √(p l)) / V) * v l) =
        1 / r * (zk k * zk l * (wF T Ap Am g i k l / (p k * p l)) * F k * F l) -
          √r * (zk k * F k) * (√r * (zk l * F l)) / V := by
      intro k l
      simp only [hv]
      rw [key _ _ _ _ _ _ _ _ _ (hsp0 k).ne' (hsp0 l).ne' hsr0.ne', hsr, hsp k, hsp l]
    simp_rw [mul_sum, hterm, sum_sub_distrib]
    have h2 : ∑ k, ∑ l, √r * (zk k * F k) * (√r * (zk l * F l)) / V = 0 := by
      have : ∀ k, ∑ l, √r * (zk k * F k) * (√r * (zk l * F l)) / V =
          √r * (zk k * F k) * (√r * ∑ l, zk l * F l) / V := by
        intro k; rw [← sum_div, mul_sum, mul_sum]
      simp_rw [this, hsum0]
      simp
    rw [h2, sub_zero]
  -- the left side of the goal
  have hlhs : ∑ x ∈ partZ Ap Am g z i, ∑ y ∈ partZ Ap Am g z i,
      aG T Ap Am g κ lam i x y * f x * f y =
      κ / lam * ∑ k, ∑ l, zk k * zk l * (wF T Ap Am g i k l / (p k * p l)) * F k * F l := by
    rw [hP, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hP, mul_sum, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [aG, wF, hp_def, hF]
    ring
  -- duality
  have hdual : ∑ j, (∑ k, Y k j * v k) ^ 2 ≤ c' * ∑ k, zk k * F k ^ 2 := by
    set N : Fin (Ap ∪ Am).card → Fin (Ap ∪ Am).card → ℝ :=
      fun k j => zk k * Y k j / √(p k) with hN
    have hNw : ∀ w : Fin (Ap ∪ Am).card → ℝ,
        ∑ k, (∑ j, N k j * w j) ^ 2 ≤ c' * ∑ j, w j ^ 2 := by
      intro w
      refine le_trans (le_of_eq ?_) (hZ w)
      refine sum_congr rfl fun k _ => ?_
      have : ∑ j, N k j * w j = zk k / √(p k) * ∑ j, Y k j * w j := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by simp only [hN]; ring
      rw [this, mul_pow, div_pow, Real.sq_sqrt (hp k).le, sq (zk k), hzz]
      simp only [hzk, hp_def]
      ring
    have := dual_bound N hc' hNw (fun k => zk k * F k)
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · refine sum_congr rfl fun j _ => ?_
      congr 1
      refine sum_congr rfl fun k _ => ?_
      have e : N k j * (zk k * F k) = (zk k * zk k) * Y k j * F k / √(p k) := by
        simp only [hN]; ring
      rw [e, hzz k]
      simp only [hv]
      ring
    · congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [mul_pow, sq (zk k), hzz]
  have hDref : Dref T Ap Am κ lam = κ / lam * r := by
    unfold Dref; rw [hr_def]; ring
  have hrhs : ∑ x ∈ partZ Ap Am g z i, f x ^ 2 = ∑ k, zk k * F k ^ 2 := hP _
  have hmain := (hY v).trans hdual
  rw [hvE] at hmain
  rw [hlhs, hDref, hrhs]
  -- κ/λ * Q ≤ c' * (κ/λ * r) * ∑ ...,  with (1/r) Q ≤ c' ∑
  set Q := ∑ k, ∑ l, zk k * zk l * (wF T Ap Am g i k l / (p k * p l)) * F k * F l
  have hQ : Q ≤ r * (c' * ∑ k, zk k * F k ^ 2) := by
    have := mul_le_mul_of_nonneg_left hmain hr.le
    rwa [← mul_assoc, mul_one_div_cancel hr.ne', one_mul] at this
  calc κ / lam * Q ≤ κ / lam * (r * (c' * ∑ k, zk k * F k ^ 2)) :=
        mul_le_mul_of_nonneg_left hQ hκ
    _ = c' * (κ / lam * r) * ∑ k, zk k * F k ^ 2 := by ring


/-- The matrices `A_v = π_v⁻¹ (K₊^{1/2} e_v)(K₊^{1/2} e_v)ᵀ` of (5.13), indexed by the ownership
variables of the copy `i` (zero elsewhere). -/
def Amat (T Ap Am : Finset G) (g : Fin t → G) (i : Fin t)
    (Y : Matrix (Fin (Ap ∪ Am).card) (Fin (Ap ∪ Am).card) ℝ) :
    (Fin t × G) ⊕ G → Matrix (Fin (Ap ∪ Am).card) (Fin (Ap ∪ Am).card) ℝ :=
  Sum.elim (fun q => if q.1 = i then ∑ k, if vtx Ap Am g i k = q.2 then
    (πG T Ap Am g i q.2)⁻¹ • vecMulVec (Y k) (Y k) else 0 else 0) (fun _ => 0)

theorem vtx_injective (i : Fin t) : Function.Injective (vtx Ap Am g i) := by
  intro k l h
  simp only [vtx, mul_right_inj] at h
  exact (eF Ap Am).injective (Subtype.ext h)

theorem qf_Amat (i : Fin t) (Y : Matrix (Fin (Ap ∪ Am).card) (Fin (Ap ∪ Am).card) ℝ)
    (z : (Fin t × G) ⊕ G → ℝ) (v : Fin (Ap ∪ Am).card → ℝ) :
    v ⬝ᵥ ((∑ e, z e • Amat T Ap Am g i Y e) *ᵥ v) =
      ∑ k, z (.inl (i, vtx Ap Am g i k)) * (πG T Ap Am g i (vtx Ap Am g i k))⁻¹ *
        (∑ j, Y k j * v j) ^ 2 := by
  rw [qf_sum_smul, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Amat, Sum.elim_inl, Sum.elim_inr, zero_mulVec, dotProduct_zero, mul_zero,
    sum_const_zero, add_zero]
  rw [sum_eq_single i]
  · simp only [ite_true]
    have : ∀ y, v ⬝ᵥ ((∑ k, if vtx Ap Am g i k = y then
        (πG T Ap Am g i y)⁻¹ • vecMulVec (Y k) (Y k) else 0) *ᵥ v) =
        ∑ k, if vtx Ap Am g i k = y then (πG T Ap Am g i y)⁻¹ * (∑ j, Y k j * v j) ^ 2
          else 0 := by
      intro y
      rw [sum_mulVec, dotProduct_sum]
      refine sum_congr rfl fun k _ => ?_
      split_ifs
      · rw [smul_mulVec, dotProduct_smul, smul_eq_mul, qf_vecMulVec]
      · simp
    simp_rw [this, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_eq_single (vtx Ap Am g i k)]
    · simp only [ite_true]; ring
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- **Spectral event (5.13)–(5.14).** Lemma 4.3 applied to the matrices `A_v` of (5.13) built from
the positive part (2.3)–(2.4) of the normalized full-copy adjacency matrix, with deviation
`σ₀/8` and `‖A_v‖ ≤ 21λ/(c²√d)`, followed by the identity (5.12). -/
theorem prob_gap (hst : Standing T Ap Am g S c lam) {μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)}
    (hμ : IsRounding T Ap Am g μ₀) (i : Fin t) :
    μ₀.P (fun z => ¬ gapOK T Ap Am g (c ^ 2 / 18) lam
        (c / Real.log (Fintype.card G) ^ 2 / 4) i z) ≤
      (Ap ∪ Am).card * Real.exp (-((c / Real.log (Fintype.card G) ^ 2 / 4) ^ 2 * c ^ 2 *
        √(S.card : ℝ) / (43008 * lam))) := by
  obtain ⟨ok, hok, hlp, hint⟩ := hμ
  set L := Real.log (Fintype.card G) with hL
  set σ0 := c / L ^ 2 / 4 with hσ0_def
  have hc := hst.c_pos
  have hc1 := hst.c_le
  have hlam := hst.lam_pos
  have hd := hst.d_pos
  have hL1 := hst.logn_ge
  have hσ0 : 0 < σ0 := by positivity
  have hσ01 : σ0 ≤ 1 := by
    rw [hσ0_def, div_div, div_le_one (by positivity)]
    nlinarith [one_le_pow₀ (n := 2) hL1]
  set w := wF T Ap Am g i with hw
  have hdpos : ∀ k, 0 < degw w k := fun k =>
    lt_of_lt_of_le (by positivity) (degw_wF_bounds hst i k).1
  have hm : 0 < (Ap ∪ Am).card := (card_VF hc.le hst.temp).1.card_pos
  have hmd := (card_VF hc.le hst.temp).2.1
  have hV : 0 < volw w := sum_pos (fun k _ => hdpos k) ⟨⟨0, hm⟩, mem_univ _⟩
  have hEle := quad_Emat w (wF_symm i) hdpos hV hσ0.le hσ01 (wF_gap hst i)
  obtain ⟨Y, hY1, hY2, hY3⟩ := posPart_factor (Emat w) (Emat_isHermitian (wF_symm i))
    (by linarith : (0 : ℝ) ≤ 1 - σ0) hEle
  -- (2.4): the diagonal of the positive part is `O(d^{-1/2})`
  have hrowE : ∀ k, ∑ l, Emat w k l ^ 2 ≤ 40 / (c ^ 2 * S.card) := by
    intro k
    have hN : ∀ k, ((univ.filter fun l => w k l ≠ 0).card : ℝ) ≤ S.card := by
      intro k
      have hsub : (univ.filter fun l => w k l ≠ 0).map ⟨vtx Ap Am g i, vtx_injective i⟩ ⊆
          univ.filter fun y => (copyGraph T Ap Am (g i)).Adj (vtx Ap Am g i k) y := by
        intro y hy
        simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hy ⊢
        obtain ⟨l, hl, rfl⟩ := hy
        by_contra hadj
        exact hl (wG_eq_zero hadj)
      have := card_le_card hsub
      rw [card_map] at this
      calc ((univ.filter fun l => w k l ≠ 0).card : ℝ) ≤
            (univ.filter fun y => (copyGraph T Ap Am (g i)).Adj (vtx Ap Am g i k) y).card := by
            exact_mod_cast this
        _ ≤ T.card := (hst.copy_deg (vtx_mem i k)).2
        _ ≤ S.card := hst.T_le_S
    have hW : ∀ k l, w k l ≤ 2 / lam := by
      intro k l
      by_cases h : (copyGraph T Ap Am (g i)).Adj (vtx Ap Am g i k) (vtx Ap Am g i l)
      · exact (hst.wG_bounds h).2
      · show wG T Ap Am g i _ _ ≤ _
        rw [wG_eq_zero h]; positivity
    have h := row_Emat w (wF_nonneg i) hdpos hV hW (fun k => (degw_wF_bounds hst i k).1)
      (by positivity) hN k
    have hvol : (Ap ∪ Am).card * (c * S.card / (2 * lam)) ≤ volw w := by
      have := card_nsmul_le_sum (univ : Finset (Fin (Ap ∪ Am).card)) (degw w)
        (c * S.card / (2 * lam)) (fun k _ => (degw_wF_bounds hst i k).1)
      simpa [nsmul_eq_mul, volw] using this
    have hratio : degw w k / volw w ≤ 4 / (c ^ 2 * S.card) := by
      rw [div_le_div_iff₀ hV (by positivity)]
      have h1 := (degw_wF_bounds hst i k).2
      calc degw w k * (c ^ 2 * S.card) ≤ 2 * S.card / lam * (c ^ 2 * S.card) := by gcongr
        _ = 4 * ((c * S.card) * (c * S.card / (2 * lam))) := by field_simp; ring
        _ ≤ 4 * ((Ap ∪ Am).card * (c * S.card / (2 * lam))) := by gcongr
        _ ≤ 4 * volw w := by gcongr
    have hfirst : 2 * (S.card * ((2 / lam) ^ 2 / (c * S.card / (2 * lam)) ^ 2)) =
        32 / (c ^ 2 * S.card) := by field_simp; ring
    have hsum40 : 32 / (c ^ 2 * (S.card : ℝ)) + 2 * (4 / (c ^ 2 * S.card)) =
        40 / (c ^ 2 * S.card) := by ring
    linarith
  have hrowY : ∀ k, ∑ j, Y k j ^ 2 ≤ 7 / (c * √(S.card : ℝ)) := by
    intro k
    have h1 := (hY3 k).trans (hrowE k)
    have h0 : 0 ≤ ∑ j, Y k j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
    have hsd : 0 < √(S.card : ℝ) := Real.sqrt_pos.2 hd
    have h2 : (∑ j, Y k j ^ 2) ^ 2 ≤ (7 / (c * √(S.card : ℝ))) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hd.le]
      refine h1.trans ?_
      gcongr
      norm_num
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 h2
  set b := 21 * lam / (c ^ 2 * √(S.card : ℝ)) with hb_def
  have hsd : 0 < √(S.card : ℝ) := Real.sqrt_pos.2 hd
  have hb : 0 < b := by positivity
  set A := Amat T Ap Am g i Y with hA
  have hApsd : ∀ e, (A e).PosSemidef := by
    intro e
    rcases e with ⟨j, y⟩ | v
    · simp only [hA, Amat, Sum.elim_inl]
      split_ifs
      · refine Matrix.posSemidef_sum _ fun k _ => ?_
        split_ifs
        · have h1 := Matrix.posSemidef_vecMulVec_self_star (Y k)
          simp only [star_trivial] at h1
          exact h1.smul (inv_nonneg.2 (πG_nonneg _ _))
        · exact Matrix.PosSemidef.zero
      · exact Matrix.PosSemidef.zero
    · exact Matrix.PosSemidef.zero
  have hvv : ∀ v : Fin (Ap ∪ Am).card → ℝ, v ⬝ᵥ v = ∑ j, v j ^ 2 := fun v => by
    simp only [dotProduct, sq]
  have hAquad : ∀ e, QuadLe (A e) b := by
    intro e v
    have hvv0 : 0 ≤ v ⬝ᵥ v := by rw [hvv]; exact sum_nonneg fun j _ => sq_nonneg _
    rcases e with ⟨j, y⟩ | u
    · simp only [hA, Amat, Sum.elim_inl]
      split_ifs with hj
      · rw [sum_mulVec, dotProduct_sum]
        have hterm : ∀ k, v ⬝ᵥ ((if vtx Ap Am g i k = y then
            (πG T Ap Am g i y)⁻¹ • vecMulVec (Y k) (Y k) else 0) *ᵥ v) ≤
            if vtx Ap Am g i k = y then b * (v ⬝ᵥ v) else 0 := by
          intro k
          split_ifs with hk
          · rw [smul_mulVec, dotProduct_smul, smul_eq_mul, qf_vecMulVec]
            have hpk := (hst.πG_bounds (i := i) (x := y) (hk ▸ vtx_mem i k)).1
            have hpk0 : 0 < πG T Ap Am g i y := lt_of_lt_of_le (by positivity) hpk
            have hcs : (∑ j, Y k j * v j) ^ 2 ≤ (∑ j, Y k j ^ 2) * (v ⬝ᵥ v) := by
              rw [hvv]; exact sum_mul_sq_le_sq_mul_sq _ _ _
            calc (πG T Ap Am g i y)⁻¹ * (∑ j, Y k j * v j) ^ 2
                ≤ (3 * lam / c) * ((7 / (c * √(S.card : ℝ))) * (v ⬝ᵥ v)) := by
                  apply mul_le_mul _ (hcs.trans (mul_le_mul_of_nonneg_right (hrowY k) hvv0))
                    (sq_nonneg _) (by positivity)
                  rw [inv_le_comm₀ hpk0 (by positivity)]
                  calc (3 * lam / c)⁻¹ = c / (3 * lam) := by rw [inv_div]
                    _ ≤ _ := hpk
              _ = b * (v ⬝ᵥ v) := by rw [hb_def]; field_simp; ring
          · simp
        calc ∑ k, v ⬝ᵥ ((if vtx Ap Am g i k = y then
              (πG T Ap Am g i y)⁻¹ • vecMulVec (Y k) (Y k) else 0) *ᵥ v)
            ≤ ∑ k, (if vtx Ap Am g i k = y then b * (v ⬝ᵥ v) else 0) := sum_le_sum fun k _ => hterm k
          _ = ((univ.filter fun k => vtx Ap Am g i k = y).card : ℝ) * (b * (v ⬝ᵥ v)) := by
              rw [← sum_filter, sum_const, nsmul_eq_mul]
          _ ≤ 1 * (b * (v ⬝ᵥ v)) := by
              gcongr
              have : (univ.filter fun k => vtx Ap Am g i k = y).card ≤ 1 := by
                rw [card_le_one]
                intro a ha b' hb'
                simp only [mem_filter] at ha hb'
                exact vtx_injective i (ha.2.trans hb'.2.symm)
              exact_mod_cast this
          _ = b * (v ⬝ᵥ v) := one_mul _
      · simp only [zero_mulVec, dotProduct_zero]; positivity
    · simp only [hA, Amat, Sum.elim_inr, zero_mulVec, dotProduct_zero]; positivity
  have hAS : ∀ e ∉ copyEdges T Ap Am g i, A e = 0 := by
    intro e he
    rcases e with ⟨j, y⟩ | u
    · simp only [hA, Amat, Sum.elim_inl]
      split_ifs with hj
      · refine sum_eq_zero fun k _ => ?_
        rw [ite_eq_right]
        intro hk
        apply he
        subst hj
        simp [copyEdges, Γ_snd_inl, ← hk, vtx_mem]
      · rfl
    · rfl
  have hM : QuadLe (∑ e, xvec T Ap Am g e • A e) (1 - σ0) := by
    intro v
    rw [hA, qf_Amat, hvv]
    refine le_trans (le_of_eq ?_) (hY2 v)
    refine sum_congr rfl fun k _ => ?_
    have hpk0 : 0 < πG T Ap Am g i (vtx Ap Am g i k) :=
      lt_of_lt_of_le (by positivity) (hst.πG_bounds (vtx_mem i k)).1
    show πG T Ap Am g i (vtx Ap Am g i k) * _ * _ = _
    rw [mul_inv_cancel₀ hpk0.ne', one_mul]
  have hconc := (bounded_support_concentration (copyEdges T Ap Am g i) ok (hok_copy hok i)
    (xvec T Ap Am g) μ₀ hlp A hApsd b (1 - σ0) (σ0 / 8) hb hAquad hAS hM (by positivity)).1
  refine le_trans (P_mono μ₀ fun z hz hng => ?_) (hconc.trans ?_)
  · by_contra hlm
    apply hng
    have hq : ∀ v : Fin (Ap ∪ Am).card → ℝ, ∑ k, z (.inl (i, vtx Ap Am g i k)) *
        (πG T Ap Am g i (vtx Ap Am g i k))⁻¹ * (∑ j, Y k j * v j) ^ 2 ≤
        (1 - 7 * σ0 / 8) * ∑ j, v j ^ 2 := by
      intro v
      have h1 := quad_of_not_lamMaxGe _ _ hlm v
      rw [sub_mulVec, dotProduct_sub] at h1
      have h2 := hM v
      rw [hA, qf_Amat] at h1
      rw [← hvv]
      linarith
    exact gapOK_of_event hst i (hint z hz).1 (by positivity) Y hY1 (by linarith) hq
  · gcongr
    rw [neg_div, neg_le_neg_iff]
    have hden : 0 < 32 * b * (1 - σ0 + σ0 / 8) := by
      have : 0 < 1 - σ0 + σ0 / 8 := by linarith
      positivity
    calc σ0 ^ 2 * c ^ 2 * √(S.card : ℝ) / (43008 * lam) = (σ0 / 8) ^ 2 / (32 * b * 1) := by
          rw [hb_def]; field_simp; ring
      _ ≤ (σ0 / 8) ^ 2 / (32 * b * (1 - σ0 + σ0 / 8)) := by
          gcongr
          linarith

end GapEvent


/-- The events of §5.3 fail for a fixed copy with small probability: the scalar tails of (5.11)
and the spectral tail of (5.13)–(5.14), combined by a union bound over the full-copy
vertices. -/
theorem prob_copy {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}
    (hst : Standing T Ap Am g S c lam) {μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ)}
    (hμ : IsRounding T Ap Am g μ₀) (i : Fin t) (η : ℝ) (hη : 0 < η) (_hη1 : η ≤ 1) :
    μ₀.P (fun z => ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η
        (c / Real.log (Fintype.card G) ^ 2 / 4) i z) ≤
      3 * Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) +
      (Ap ∪ Am).card * (2 * Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) +
        2 * Real.exp (-((η * Dref T Ap Am (c ^ 2 / 18) lam) ^ 2 /
          (32 * (Dref T Ap Am (c ^ 2 / 18) lam + η * Dref T Ap Am (c ^ 2 / 18) lam))))) +
      (Ap ∪ Am).card * Real.exp (-((c / Real.log (Fintype.card G) ^ 2 / 4) ^ 2 * c ^ 2 *
        √(S.card : ℝ) / (43008 * lam))) := by
  set σ0 := c / Real.log (Fintype.card G) ^ 2 / 4
  set E₁ := Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192))
  set E₂ := Real.exp (-((η * Dref T Ap Am (c ^ 2 / 18) lam) ^ 2 /
          (32 * (Dref T Ap Am (c ^ 2 / 18) lam + η * Dref T Ap Am (c ^ 2 / 18) lam))))
  set Eg := Real.exp (-(σ0 ^ 2 * c ^ 2 * √(S.card : ℝ) / (43008 * lam)))
  set Ci := copyVerts Ap Am (g i)
  have hE₁ : 0 ≤ E₁ := (Real.exp_pos _).le
  calc μ₀.P (fun z => ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i z)
      ≤ μ₀.P (fun z => ¬ sizeOK T Ap Am g i z ∨ ((∃ x ∈ Ci,
          ¬ degOK T Ap Am g (c ^ 2 / 18) lam η i z x ∨ ¬ nbhdOK T Ap Am g i z x) ∨
          ¬ gapOK T Ap Am g (c ^ 2 / 18) lam σ0 i z)) := by
        refine P_mono μ₀ fun z _ hz => ?_
        unfold GoodCopy at hz
        by_contra h
        push Not at h
        exact hz ⟨h.1, fun x hx => h.2.1 x hx, h.2.2⟩
    _ ≤ μ₀.P (fun z => ¬ sizeOK T Ap Am g i z) + (μ₀.P (fun z => ∃ x ∈ Ci,
          ¬ degOK T Ap Am g (c ^ 2 / 18) lam η i z x ∨ ¬ nbhdOK T Ap Am g i z x) +
          μ₀.P (fun z => ¬ gapOK T Ap Am g (c ^ 2 / 18) lam σ0 i z)) :=
        (P_or_le _ _ _).trans (add_le_add le_rfl (P_or_le _ _ _))
    _ ≤ E₁ + (∑ x ∈ Ci, (μ₀.P (fun z => ¬ degOK T Ap Am g (c ^ 2 / 18) lam η i z x) +
          μ₀.P (fun z => ¬ nbhdOK T Ap Am g i z x)) + (Ap ∪ Am).card * Eg) := by
        gcongr
        · exact prob_size hst hμ i
        · exact (P_exists_le _ _ _).trans (sum_le_sum fun x _ => P_or_le _ _ _)
        · exact prob_gap hst hμ i
    _ ≤ E₁ + (∑ x ∈ Ci, (2 * E₂ + 2 * E₁) + (Ap ∪ Am).card * Eg) := by
        gcongr with x hx
        · exact prob_deg hst hμ i hx hη
        · exact prob_nbhd hst hμ i hx
    _ ≤ 3 * E₁ + (Ap ∪ Am).card * (2 * E₁ + 2 * E₂) + (Ap ∪ Am).card * Eg := by
        rw [sum_const, card_copyVerts, nsmul_eq_mul]
        nlinarith [Real.exp_pos (-((η * Dref T Ap Am (c ^ 2 / 18) lam) ^ 2 /
          (32 * (Dref T Ap Am (c ^ 2 / 18) lam + η * Dref T Ap Am (c ^ 2 / 18) lam))))]


/-- **Deterministic part of Proposition 5.3.** An integral point all of whose copies satisfy the
events of §5.3 gives a successful allocation: the exact identities (5.4) give the partition and
balance, (5.9) the weights, (5.11) the sizes, degrees and (5.16), and the spectral event with
the degree event gives the gap `σ₀/2` of `H_i`. -/
theorem good_of_copies {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}
    (hst : Standing T Ap Am g S c lam) (hkl : 0 ≤ c ^ 2 / 18 / lam)
    {z : (Fin t × G) ⊕ G → ℝ} (hz : z ∈ (Γ T Ap Am g).integralSolutions (fun v => (bd T v : ℝ)))
    {η η' σ0 : ℝ} (hη' : 0 ≤ η') (hηη : η' ≤ η) (hσ0 : 0 < σ0) (hσ01 : σ0 ≤ 1)
    (hη'σ : η' ≤ σ0 / 4)
    (hcop : ∀ i, GoodCopy T Ap Am g (c ^ 2 / 18) lam η' σ0 i z) :
    (alloc T Ap Am g (c ^ 2 / 18) lam hkl z).Good S T Ap Am lam (Dref T Ap Am (c ^ 2 / 18) lam)
      (σ0 / 2) η (c ^ 2 / 9216) (c ^ 2 / 6) 32 := by
  classical
  obtain ⟨h01, heq⟩ := hz
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  have hd := hst.d_pos
  have hvert : ∀ v, ∑ i, (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) +
      (if Odd (uu T) then z (.inr v) else 0) = 1 := by
    intro v; have := heq (.inl v); rw [apply_inl] at this; simpa [bd] using this
  have hcopyeq : ∀ j, ∑ x ∈ copyVerts Ap Am (g j),
      SignedGraph.signVal (decide ((g j)⁻¹ * x ∈ Ap)) * z (.inl (j, x)) = 0 := by
    intro j; have := heq (.inr (.inl j)); rw [apply_copy] at this; simpa [bd] using this
  have haux : Odd (uu T) → ∀ q : QT T,
      ∑ v ∈ univ.filter (fun v => (QuotientGroup.mk v : QT T) = q), z (.inr v) = 1 := by
    intro ho q; have := heq (.inr (.inr q)); rw [apply_aux, ite_eq_left ho] at this
    simpa [bd, ho] using this
  have hpartsum : ∀ i (φ : G → ℝ), ∑ x ∈ copyVerts Ap Am (g i), z (.inl (i, x)) * φ x =
      ∑ x ∈ partZ Ap Am g z i, φ x := by
    intro i φ
    rw [partZ, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    rcases h01 (.inl (i, x)) with h | h <;> simp [h]
  have hterm01 : ∀ v i, (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 0 ∨
      (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 1 := by
    intro v i; split_ifs
    · exact h01 _
    · exact Or.inl rfl
  have hmem : ∀ v i, v ∈ partZ Ap Am g z i ↔
      (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 1 := by
    intro v i; unfold partZ; rw [mem_filter]; split_ifs with h <;> simp [h]
  have hDpos : 0 < Dref T Ap Am (c ^ 2 / 18) lam :=
    lt_of_lt_of_le (by positivity) (Dref_bounds' hst (κ := c ^ 2 / 18) (by positivity)).1
  refine
    { part_sub := fun i => filter_subset _ _
      part_unique := ?_
      part_disjoint := ?_
      balanced := ?_
      size_lower := ?_
      H_supp := ?_
      H_weights := ?_
      H_deg := ?_
      H_gap := ?_
      nbhd_lower := ?_
      nbhd_upper := ?_
      cover_mult := hst.cover.mult
      cover_edges := ?_
      reserved := ?_ }
  · -- part_unique
    intro v hvW
    have hres : (if Odd (uu T) then z (.inr v) else 0) = 0 := by
      by_cases ho : Odd (uu T)
      · rw [ite_eq_left ho]
        rcases h01 (.inr v) with h | h
        · exact h
        · exfalso; apply hvW
          change v ∈ (if Odd (uu T) then univ.filter (fun v => z (.inr v) = 1) else ∅)
          rw [ite_eq_left ho]; simp [h]
      · rw [ite_eq_right ho]
    have hs := hvert v
    rw [hres, add_zero, sum01_eq_card _ _ (fun i _ => hterm01 v i)] at hs
    have hs' : (univ.filter fun i =>
        (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 1).card = 1 := by
      exact_mod_cast hs
    obtain ⟨i, hi⟩ := card_eq_one.1 hs'
    have hiS : i ∈ univ.filter fun i =>
        (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 1 := by
      rw [hi]; exact mem_singleton_self i
    refine ⟨i, (hmem v i).2 (mem_filter.1 hiS).2, fun j hj => ?_⟩
    have : j ∈ univ.filter (fun i =>
        (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 1) :=
      mem_filter.2 ⟨mem_univ _, (hmem v j).1 hj⟩
    rw [hi] at this
    exact mem_singleton.1 this
  · -- part_disjoint
    intro (i : Fin t)
    rw [Finset.disjoint_left]
    intro v hvP hvW
    change v ∈ (if Odd (uu T) then univ.filter (fun v => z (.inr v) = 1) else ∅) at hvW
    by_cases ho : Odd (uu T)
    · rw [ite_eq_left ho, mem_filter] at hvW
      have hs := hvert v
      rw [ite_eq_left ho, hvW.2] at hs
      have hz0 : ∑ i, (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) = 0 := by
        linarith
      have hnn : ∀ i ∈ (univ : Finset (Fin t)),
          0 ≤ (if v ∈ copyVerts Ap Am (g i) then z (.inl (i, v)) else 0) := fun i _ => by
        rcases hterm01 v i with h | h <;> rw [h] <;> norm_num
      have := (sum_eq_zero_iff_of_nonneg hnn).1 hz0 i (mem_univ i)
      rw [(hmem v i).1 hvP] at this
      norm_num at this
    · rw [ite_eq_right ho] at hvW
      simp at hvW
  · -- balanced
    intro (i : Fin t)
    change ((partZ Ap Am g z i).filter fun v => (g i)⁻¹ * v ∈ Ap).card =
      ((partZ Ap Am g z i).filter fun v => (g i)⁻¹ * v ∈ Am).card
    have h := hcopyeq i
    have e1 : ∑ x ∈ copyVerts Ap Am (g i),
        SignedGraph.signVal (decide ((g i)⁻¹ * x ∈ Ap)) * z (.inl (i, x)) =
        ∑ x ∈ partZ Ap Am g z i, (if (g i)⁻¹ * x ∈ Ap then (1 : ℝ) else -1) := by
      rw [← hpartsum]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_comm]
      congr 1
      unfold SignedGraph.signVal
      by_cases hA : (g i)⁻¹ * x ∈ Ap <;> simp [hA]
    rw [e1, sum_ite, sum_const, sum_const] at h
    simp only [nsmul_eq_mul, mul_one, mul_neg] at h
    have e2 : (partZ Ap Am g z i).filter (fun x => ¬ (g i)⁻¹ * x ∈ Ap) =
        (partZ Ap Am g z i).filter (fun x => (g i)⁻¹ * x ∈ Am) := by
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨hx, hA⟩
        refine ⟨hx, ?_⟩
        have := mem_copyVerts.1 (filter_subset _ _ hx)
        rcases mem_union.1 this with h' | h'
        · exact absurd h' hA
        · exact h'
      · rintro ⟨hx, hA⟩
        exact ⟨hx, fun h' => disjoint_left.1 hst.temp.disjoint h' hA⟩
    rw [e2] at h
    have h' : (((partZ Ap Am g z i).filter fun v => (g i)⁻¹ * v ∈ Ap).card : ℝ) =
        ((partZ Ap Am g z i).filter fun v => (g i)⁻¹ * v ∈ Am).card := by linarith
    exact_mod_cast h'
  · -- size_lower
    intro (i : Fin t)
    obtain ⟨hsz, -, -⟩ := hcop i
    unfold sizeOK at hsz
    have hcard : ∑ x ∈ copyVerts Ap Am (g i), z (.inl (i, x)) = (partZ Ap Am g z i).card := by
      have := hpartsum i (fun _ => 1)
      simp only [mul_one] at this
      rw [this]; simp
    have hmean := hst.size_mean_ge i
    change c ^ 2 / 6 * S.card / lam ≤ (partZ Ap Am g z i).card
    calc c ^ 2 / 6 * S.card / lam = (c ^ 2 * S.card / (3 * lam)) / 2 := by field_simp; ring
      _ ≤ (∑ x ∈ copyVerts Ap Am (g i), πG T Ap Am g i x) / 2 := by gcongr
      _ ≤ _ := hsz
      _ = _ := hcard
  · -- H_supp
    intro (i : Fin t) x y hpos
    change 0 < aG T Ap Am g (c ^ 2 / 18) lam i x y at hpos
    by_contra hadj
    have hadj' : ¬ (copyGraph T Ap Am (g i)).Adj x y := hadj
    unfold aG at hpos
    rw [wG_eq_zero hadj'] at hpos
    simp at hpos
  · -- H_weights
    intro (i : Fin t) x y hpos
    change 0 < aG T Ap Am g (c ^ 2 / 18) lam i x y at hpos
    have hadj : (copyGraph T Ap Am (g i)).Adj x y := by
      by_contra hadj
      unfold aG at hpos
      rw [wG_eq_zero hadj] at hpos
      simp at hpos
    exact hst.aG_bounds hadj
  · -- H_deg
    intro (i : Fin t) x
    obtain ⟨-, hdg, -⟩ := hcop i
    have hx : (x : G) ∈ copyVerts Ap Am (g i) := filter_subset _ _ x.2
    have h1 := (hdg x hx).1
    unfold degOK at h1
    rw [hpartsum i (fun y => aG T Ap Am g (c ^ 2 / 18) lam i x y)] at h1
    change |∑ y : ↥(partZ Ap Am g z i), aG T Ap Am g (c ^ 2 / 18) lam i x y -
      Dref T Ap Am (c ^ 2 / 18) lam| ≤ η * Dref T Ap Am (c ^ 2 / 18) lam
    rw [sum_coe_sort (partZ Ap Am g z i) (fun y => aG T Ap Am g (c ^ 2 / 18) lam i x y)]
    exact h1.trans (mul_le_mul_of_nonneg_right hηη hDpos.le)
  · -- H_gap
    intro (i : Fin t)
    obtain ⟨-, hdg, hgap⟩ := hcop i
    refine hasGap_of_quad (partZ Ap Am g z i) (aG T Ap Am g (c ^ 2 / 18) lam i) _
      (fun x y => rfl) (aG_symm T Ap Am g _ _ i) hDpos hσ0 hσ01 hη' hη'σ ?_ hgap
    intro x hx
    have h1 := (hdg x (filter_subset _ _ hx)).1
    unfold degOK at h1
    rwa [hpartsum i] at h1
  · -- nbhd_lower
    intro (i : Fin t) v hv
    obtain ⟨-, hdg, -⟩ := hcop i
    obtain ⟨hlo, -⟩ := (hdg v hv).2
    have hcnt : ∑ y ∈ copyVerts Ap Am (g i),
        (if (copyGraph T Ap Am (g i)).Adj v y then z (.inl (i, y)) else 0) =
        ((partZ Ap Am g z i).filter fun y => (copyGraph T Ap Am (g i)).Adj v y).card := by
      have := hpartsum i (fun y => if (copyGraph T Ap Am (g i)).Adj v y then 1 else 0)
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
      simp only [Nat.cast_one]
      rw [← this]
      refine sum_congr rfl fun y _ => ?_
      split_ifs <;> simp
    obtain ⟨hM1, -⟩ := hst.nbhdMean_bounds hv
    change c ^ 2 / 6 * S.card / lam ≤
      ((partZ Ap Am g z i).filter fun y => (copyGraph T Ap Am (g i)).Adj v y).card
    rw [← hcnt]
    calc c ^ 2 / 6 * S.card / lam = (c ^ 2 * S.card / (3 * lam)) / 2 := by field_simp; ring
      _ ≤ nbhdMean T Ap Am g i v / 2 := by gcongr
      _ ≤ _ := hlo
  · -- nbhd_upper
    intro (i : Fin t) v hv
    obtain ⟨-, hdg, -⟩ := hcop i
    obtain ⟨-, hhi⟩ := (hdg v hv).2
    have hcnt : ∑ y ∈ copyVerts Ap Am (g i),
        (if (copyGraph T Ap Am (g i)).Adj v y then z (.inl (i, y)) else 0) =
        ((partZ Ap Am g z i).filter fun y => (copyGraph T Ap Am (g i)).Adj v y).card := by
      have := hpartsum i (fun y => if (copyGraph T Ap Am (g i)).Adj v y then 1 else 0)
      rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
      simp only [Nat.cast_one]
      rw [← this]
      refine sum_congr rfl fun y _ => ?_
      split_ifs <;> simp
    obtain ⟨-, hM2⟩ := hst.nbhdMean_bounds hv
    change (((partZ Ap Am g z i).filter fun y => (copyGraph T Ap Am (g i)).Adj v y).card : ℝ) ≤
      32 * S.card / lam
    rw [← hcnt]
    calc _ ≤ 2 * nbhdMean T Ap Am g i v := hhi
      _ ≤ 2 * (16 * S.card / lam) := by gcongr
      _ = 32 * S.card / lam := by ring
  · -- cover_edges
    intro x s hs
    have h := hst.cover.occ_lower x s hs
    have hf := hst.temp.density s hs
    have hpos : 0 < occ T Ap Am g x s := by
      have : (0 : ℝ) < occ T Ap Am g x s := lt_of_lt_of_le (by positivity) h
      exact_mod_cast this
    unfold occ at hpos
    obtain ⟨i, hi⟩ := card_pos.1 hpos
    exact ⟨i, (mem_filter.1 hi).2⟩
  · -- reserved
    refine ⟨fun ho => ?_, fun he => ?_⟩
    · have ho' : Odd (uu T) := ho
      intro x
      change ((if Odd (uu T) then univ.filter (fun v => z (.inr v) = 1) else ∅).filter
        fun w => x⁻¹ * w ∈ Subgroup.closure (T : Set G)).card = 1
      rw [ite_eq_left ho']
      have h := haux ho' (QuotientGroup.mk x)
      rw [sum01_eq_card _ _ (fun v _ => h01 _)] at h
      have h' : ((univ.filter (fun v => (QuotientGroup.mk v : QT T) = QuotientGroup.mk x)).filter
          fun v => z (.inr v) = 1).card = 1 := by exact_mod_cast h
      rw [← h']
      congr 1
      ext w
      simp only [mem_filter, mem_univ, true_and]
      rw [eq_comm (a := (QuotientGroup.mk w : QT T)), QuotientGroup.eq]
      tauto
    · have he' : ¬ Odd (uu T) := Nat.not_odd_iff_even.2 he
      change (if Odd (uu T) then univ.filter (fun v => z (.inr v) = 1) else ∅) = ∅
      rw [ite_eq_right he']

/-- The glued point is integral when each coset sample is (every constraint involves only the
variables of one coset). -/
theorem glue_integral {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}
    (hst : Standing T Ap Am g S c lam) {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am)
    (ζ : QT T → ((Fin t × G) ⊕ G → ℝ))
    (hζ : ∀ q, ζ q ∈ (Γ T Ap Am g).integralSolutions (fun v => (bd T v : ℝ))) :
    glue T g a₀ ζ ∈ (Γ T Ap Am g).integralSolutions (fun v => (bd T v : ℝ)) := by
  refine ⟨fun e => (hζ _).1 e, fun v => ?_⟩
  rcases v with v | j | q
  · have h := (hζ (QuotientGroup.mk v)).2 (.inl v)
    rw [apply_inl] at h ⊢
    rw [← h]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    by_cases hv : v ∈ copyVerts Ap Am (g i)
    · rw [ite_eq_left hv, ite_eq_left hv]
      show ζ (QuotientGroup.mk (g i * a₀)) _ = ζ (QuotientGroup.mk v) _
      rw [copy_coset hst.temp.connected ha₀ hv]
    · rw [ite_eq_right hv, ite_eq_right hv]
  · have h := (hζ (QuotientGroup.mk (g j * a₀))).2 (.inr (.inl j))
    rw [apply_copy] at h ⊢
    exact h
  · have h := (hζ q).2 (.inr (.inr q))
    rw [apply_aux] at h ⊢
    rw [← h]
    congr 1
    refine sum_congr rfl fun v hv => ?_
    show ζ (QuotientGroup.mk v) _ = ζ q _
    rw [(mem_filter.1 hv).2]




/-! ## §5.2: the fractional point satisfies the hypotheses of Lemma 4.1 -/

section Rounding

open Classical

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}

/-- **(5.4), first identity**: `∑_i x_{v,i} = 1`, since the occurrences of each physical
`s`-edge carry total weight `f_s` and `∑_{s ∈ T} f_s = R`. -/
theorem sum_xG_eq_one (hst : Standing T Ap Am g S c lam) (v : G) :
    ∑ i, xG T Ap Am g i v = 1 := by
  have hR := hst.Rsum_pos
  unfold xG
  rw [← sum_div, div_eq_one_iff_eq hR.ne', sum_comm]
  have hy : ∀ y, ∑ i, wG T Ap Am g i v y =
      if v⁻¹ * y ∈ T then labelDensity T Ap Am (v⁻¹ * y) else 0 := by
    intro y
    have hocc : ((univ.filter fun i => (copyGraph T Ap Am (g i)).Adj v y).card : ℝ) =
        occ T Ap Am g v (v⁻¹ * y) := by
      unfold occ
      congr 2
      refine filter_congr fun i _ => ?_
      simp [copyAdj_iff]
    unfold wG
    rw [← sum_filter, sum_const, nsmul_eq_mul, hocc]
    split_ifs with hT
    · have hf := hst.temp.density _ hT
      have ho := hst.cover.occ_lower v _ hT
      have hopos : (0 : ℝ) < occ T Ap Am g v (v⁻¹ * y) :=
        lt_of_lt_of_le (by have := hst.lam_pos; positivity) ho
      field_simp
    · have : ((univ.filter fun i => (copyGraph T Ap Am (g i)).Adj v y).card : ℝ) = 0 := by
        rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
        intro i _ h
        exact hT (copyAdj_label hst.temp.symm h)
      rw [← hocc, this, zero_mul]
  simp_rw [hy]
  rw [Fintype.sum_equiv (Equiv.mulLeft v⁻¹)
    (fun y => if v⁻¹ * y ∈ T then labelDensity T Ap Am (v⁻¹ * y) else 0)
    (fun s => if s ∈ T then labelDensity T Ap Am s else 0) (fun y => rfl)]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  rfl

/-- **(5.4), second identity**: every copy is balanced, `∑_v s_i(v) x_{v,i} = 0`. -/
theorem xG_balance (hst : Standing T Ap Am g S c lam) (j : Fin t) :
    ∑ x ∈ copyVerts Ap Am (g j),
      SignedGraph.signVal (decide ((g j)⁻¹ * x ∈ Ap)) * πG T Ap Am g j x = 0 := by
  set σf : G → ℝ := fun x => if (g j)⁻¹ * x ∈ Ap then 1 else -1 with hσf
  have hsig : ∀ x, SignedGraph.signVal (decide ((g j)⁻¹ * x ∈ Ap)) = σf x := by
    intro x; unfold SignedGraph.signVal; by_cases h : (g j)⁻¹ * x ∈ Ap <;> simp [hσf, h]
  have hanti : ∀ x y, σf x * wG T Ap Am g j x y = -(σf y * wG T Ap Am g j x y) := by
    intro x y
    by_cases hadj : (copyGraph T Ap Am (g j)).Adj x y
    · have h2 := hadj.2.1
      have hdis := hst.temp.disjoint
      rcases h2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hy' : (g j)⁻¹ * y ∉ Ap := fun h => disjoint_left.1 hdis h hy
        simp [hσf, hx, hy']
      · have hx' : (g j)⁻¹ * x ∉ Ap := fun h => disjoint_left.1 hdis h hx
        simp [hσf, hy, hx']
    · rw [wG_eq_zero hadj]; ring
  set Sm := ∑ x, ∑ y, σf x * wG T Ap Am g j x y with hSm
  have hS0 : Sm = 0 := by
    have : Sm = -Sm := by
      calc Sm = ∑ x, ∑ y, -(σf y * wG T Ap Am g j x y) :=
            sum_congr rfl fun x _ => sum_congr rfl fun y _ => hanti x y
        _ = -∑ y, ∑ x, σf y * wG T Ap Am g j y x := by
            rw [sum_comm]
            simp only [sum_neg_distrib]
            exact congrArg _ (sum_congr rfl fun y _ => sum_congr rfl fun x _ => by
              rw [wG_symm])
        _ = -Sm := rfl
    linarith
  simp_rw [hsig]
  rw [← sum_copy_eq (i := j) (fun x => σf x * πG T Ap Am g j x)
    (fun x hx => by rw [πG_eq_zero hx, mul_zero])]
  unfold πG xG
  have : ∀ x, σf x * (θ T * ((∑ y, wG T Ap Am g j x y) / Rsum T Ap Am)) =
      θ T / Rsum T Ap Am * ∑ y, σf x * wG T Ap Am g j x y := by
    intro x; rw [← mul_sum]; ring
  simp_rw [this]
  rw [← mul_sum, ← hSm, hS0, mul_zero]

theorem coset_card (q : QT T) :
    ((univ.filter fun v => (QuotientGroup.mk v : QT T) = q).card : ℝ) = uu T := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have : (univ.filter fun v => (QuotientGroup.mk v : QT T) = QuotientGroup.mk x) =
      (univ.filter fun w => w ∈ Subgroup.closure (T : Set G)).map (Equiv.mulLeft x).toEmbedding := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply,
      Equiv.coe_mulLeft]
    constructor
    · intro h
      refine ⟨x⁻¹ * v, QuotientGroup.eq.1 h.symm, by group⟩
    · rintro ⟨w, hw, rfl⟩
      rw [eq_comm, QuotientGroup.eq]
      simpa using hw
  rw [this, card_map]
  unfold uu
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The coset label of the vertices of `Γ`. -/
def cosV (T : Finset G) (g : Fin t → G) (a₀ : G) : G ⊕ Fin t ⊕ QT T → QT T
  | .inl v => QuotientGroup.mk v
  | .inr (.inl i) => QuotientGroup.mk (g i * a₀)
  | .inr (.inr q) => q

theorem underlying_adj_iff {v w : G ⊕ Fin t ⊕ QT T} :
    (Γ T Ap Am g).underlying.Adj v w ↔ v ≠ w ∧
      ((∃ e, (Γ T Ap Am g).fst e = v ∧ (Γ T Ap Am g).snd e = w) ∨
        (∃ e, (Γ T Ap Am g).fst e = w ∧ (Γ T Ap Am g).snd e = v)) :=
  SimpleGraph.fromRel_adj _ _ _

theorem edge_coset (hst : Standing T Ap Am g S c lam) {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am)
    (e : (Fin t × G) ⊕ G) : (Γ T Ap Am g).fst e = (Γ T Ap Am g).snd e ∨
      cosV T g a₀ ((Γ T Ap Am g).fst e) = cosV T g a₀ ((Γ T Ap Am g).snd e) := by
  rcases e with ⟨i, x⟩ | v
  · by_cases hx : x ∈ copyVerts Ap Am (g i)
    · right
      rw [Γ_fst_inl, Γ_snd_inl, ite_eq_left hx]
      exact (copy_coset hst.temp.connected ha₀ hx).symm
    · left
      rw [Γ_fst_inl, Γ_snd_inl, ite_eq_right hx]
  · by_cases ho : Odd (uu T)
    · right
      rw [Γ_fst_inr, Γ_snd_inr, ite_eq_left ho]
      rfl
    · left
      rw [Γ_fst_inr, Γ_snd_inr, ite_eq_right ho]

theorem reach_coset (hst : Standing T Ap Am g S c lam) {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am)
    {v w : G ⊕ Fin t ⊕ QT T} (h : (Γ T Ap Am g).underlying.Reachable v w) :
    cosV T g a₀ v = cosV T g a₀ w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    rename_i b d _
    rw [ih]
    rw [underlying_adj_iff] at hadj
    obtain ⟨hne, ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩⟩ := hadj
    · rcases edge_coset hst ha₀ e with h | h
      · exact absurd (h1.symm.trans (h.trans h2)) hne
      · rw [← h1, ← h2]; exact h
    · rcases edge_coset hst ha₀ e with h | h
      · exact absurd (h2.symm.trans (h.symm.trans h1)) hne
      · rw [← h1, ← h2]; exact h.symm

theorem aux_isolated (he : ¬ Odd (uu T)) (q : QT T) (w : G ⊕ Fin t ⊕ QT T) :
    ¬ (Γ T Ap Am g).underlying.Adj (.inr (.inr q)) w := by
  rw [underlying_adj_iff]
  rintro ⟨-, ⟨e, h1, -⟩ | ⟨e, -, h2⟩⟩
  · rcases e with ⟨i, x⟩ | v <;> simp at h1
  · rcases e with ⟨i, x⟩ | v
    · rw [Γ_snd_inl] at h2; split_ifs at h2 <;> simp at h2
    · rw [Γ_snd_inr, ite_eq_right he] at h2; simp at h2

theorem reach_aux_even (he : ¬ Odd (uu T)) {q : QT T} {w : G ⊕ Fin t ⊕ QT T}
    (h : (Γ T Ap Am g).underlying.Reachable (.inr (.inr q)) w) : w = .inr (.inr q) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih =>
    rw [ih] at hadj
    exact absurd hadj (aux_isolated he q _)

theorem adj_of_mem {i : Fin t} {x : G} (hx : x ∈ copyVerts Ap Am (g i)) :
    (Γ T Ap Am g).underlying.Adj (.inl x) (.inr (.inl i)) := by
  rw [underlying_adj_iff]
  refine ⟨by simp, Or.inl ⟨.inl (i, x), rfl, ?_⟩⟩
  rw [Γ_snd_inl, ite_eq_left hx]

theorem reach_step (hst : Standing T Ap Am g S c lam) (x : G) {s : G} (hs : s ∈ T) :
    (Γ T Ap Am g).underlying.Reachable (.inl x) (.inl (x * s)) := by
  have h := hst.cover.occ_lower x s hs
  have hf := hst.temp.density s hs
  have hpos : 0 < occ T Ap Am g x s := by
    have : (0 : ℝ) < occ T Ap Am g x s :=
      lt_of_lt_of_le (by have := hst.lam_pos; positivity) h
    exact_mod_cast this
  unfold occ at hpos
  obtain ⟨i, hi⟩ := card_pos.1 hpos
  have hadj : (copyGraph T Ap Am (g i)).Adj x (x * s) := (mem_filter.1 hi).2
  obtain ⟨h1, h2⟩ := copyAdj_mem hadj
  exact (adj_of_mem h1).reachable.trans (adj_of_mem h2).reachable.symm

theorem reach_inl (hst : Standing T Ap Am g S c lam) {v w : G}
    (h : v⁻¹ * w ∈ Subgroup.closure (T : Set G)) :
    (Γ T Ap Am g).underlying.Reachable (.inl v) (.inl w) := by
  have key : ∀ y ∈ Subgroup.closure (T : Set G), ∀ x : G,
      (Γ T Ap Am g).underlying.Reachable (.inl x) (.inl (x * y)) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs => exact fun x => reach_step hst x hs
    | one => exact fun x => by simp
    | mul a b _ _ ha hb =>
      intro x
      rw [← mul_assoc]
      exact (ha x).trans (hb (x * a))
    | inv a _ ha =>
      intro x
      have := ha (x * a⁻¹)
      simp only [inv_mul_cancel_right] at this
      exact this.symm
  simpa using key _ h v

theorem reach_copy {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am) (i : Fin t) :
    (Γ T Ap Am g).underlying.Reachable (.inr (.inl i)) (.inl (g i * a₀)) :=
  (adj_of_mem (mem_copyVerts.2 (by simpa using ha₀))).reachable.symm

theorem reach_aux_odd (ho : Odd (uu T)) (v : G) :
    (Γ T Ap Am g).underlying.Reachable (.inl v) (.inr (.inr (QuotientGroup.mk v))) := by
  refine SimpleGraph.Adj.reachable ?_
  rw [underlying_adj_iff]
  refine ⟨by simp, Or.inl ⟨.inr v, rfl, ?_⟩⟩
  rw [Γ_snd_inr, ite_eq_left ho]

end Rounding

section Rounding2

open Classical

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}

theorem coset_card_nat (q : QT T) :
    (univ.filter fun v => (QuotientGroup.mk v : QT T) = q).card = uu T := by
  exact_mod_cast coset_card q

/-- **Parity** in Lemma 4.1: the demand of every component (a coset with its copies and, in
the odd case, its auxiliary node) is `u` or `u + 1`, hence even. -/
theorem parity (hst : Standing T Ap Am g S c lam) {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am)
    (v' : G ⊕ Fin t ⊕ QT T) :
    Even (∑ w ∈ univ.filter (fun w => (Γ T Ap Am g).underlying.Reachable v' w), bd T w) := by
  by_cases hiso : ¬ Odd (uu T) ∧ ∃ q, v' = .inr (.inr q)
  · obtain ⟨he, q, rfl⟩ := hiso
    have : univ.filter (fun w => (Γ T Ap Am g).underlying.Reachable (.inr (.inr q)) w) =
        {.inr (.inr q)} := by
      ext w
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨reach_aux_even he, fun h => h ▸ SimpleGraph.Reachable.refl _⟩
    rw [this, sum_singleton]
    simp [bd, he]
  · set q := cosV T g a₀ v' with hq
    have hx : ∃ x : G, (QuotientGroup.mk x : QT T) = q ∧
        (Γ T Ap Am g).underlying.Reachable v' (.inl x) := by
      rcases v' with v | j | q'
      · exact ⟨v, rfl, SimpleGraph.Reachable.refl _⟩
      · exact ⟨g j * a₀, rfl, reach_copy ha₀ j⟩
      · have ho : Odd (uu T) := by
          by_contra he; exact hiso ⟨he, q', rfl⟩
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective q'
        refine ⟨x, hx, ?_⟩
        have := reach_aux_odd (Ap := Ap) (Am := Am) (g := g) ho x
        rw [hx] at this
        exact this.symm
    obtain ⟨x, hxq, hxr⟩ := hx
    have hinl : ∀ w : G, (Γ T Ap Am g).underlying.Reachable v' (.inl w) ↔
        (QuotientGroup.mk w : QT T) = q := by
      intro w
      constructor
      · intro h; exact (reach_coset hst ha₀ h).symm
      · intro h
        refine hxr.trans (reach_inl hst ?_)
        rw [← QuotientGroup.eq, hxq, h]
    have hauxr : Odd (uu T) → ∀ q' : QT T,
        (Γ T Ap Am g).underlying.Reachable v' (.inr (.inr q')) ↔ q' = q := by
      intro ho q'
      constructor
      · intro h; exact (reach_coset hst ha₀ h).symm
      · intro h
        subst h
        have := reach_aux_odd (Ap := Ap) (Am := Am) (g := g) ho x
        rw [hxq] at this
        exact hxr.trans this
    rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h1 : ∑ w : G, (if (Γ T Ap Am g).underlying.Reachable v' (.inl w) then
        bd T (.inl w : G ⊕ Fin t ⊕ QT T) else 0) = (uu T : ℤ) := by
      simp only [bd]
      rw [← sum_filter]
      simp_rw [hinl]
      rw [sum_const, nsmul_eq_mul, mul_one, coset_card_nat]
    have h2 : ∑ j : Fin t, (if (Γ T Ap Am g).underlying.Reachable v' (.inr (.inl j)) then
        bd T (.inr (.inl j) : G ⊕ Fin t ⊕ QT T) else 0) = 0 := by
      simp [bd]
    have h3 : ∑ q' : QT T, (if (Γ T Ap Am g).underlying.Reachable v' (.inr (.inr q')) then
        bd T (.inr (.inr q') : G ⊕ Fin t ⊕ QT T) else 0) = if Odd (uu T) then 1 else 0 := by
      by_cases ho : Odd (uu T)
      · simp only [bd, ite_eq_left ho]
        simp_rw [hauxr ho]
        rw [sum_ite_eq']
        simp
      · simp [bd, ho]
    rw [h1, h2, h3, zero_add]
    by_cases ho : Odd (uu T)
    · rw [ite_eq_left ho]
      exact ((Int.odd_coe_nat _).2 ho).add_one
    · rw [ite_eq_right ho, add_zero]
      exact (Int.even_coe_nat _).2 (Nat.not_odd_iff_even.1 ho)

theorem xvec_nonneg (e : (Fin t × G) ⊕ G) : 0 ≤ xvec T Ap Am g e := by
  rcases e with ⟨i, x⟩ | v
  · exact πG_nonneg i x
  · show 0 ≤ (if Odd (uu T) then 1 / (uu T : ℝ) else 0)
    split_ifs
    · have : (0 : ℝ) < uu T := by exact_mod_cast uu_pos T
      positivity
    · exact le_rfl

theorem xvec_le_half (hst : Standing T Ap Am g S c lam) (e : (Fin t × G) ⊕ G) :
    xvec T Ap Am g e ≤ 1 / 2 := by
  rcases e with ⟨i, x⟩ | v
  · show πG T Ap Am g i x ≤ 1 / 2
    by_cases hx : x ∈ copyVerts Ap Am (g i)
    · have h1 := (hst.πG_bounds hx).2
      have h2 := hst.lam_ge
      have : 16 / lam ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      linarith
    · rw [πG_eq_zero hx]; norm_num
  · show (if Odd (uu T) then 1 / (uu T : ℝ) else 0) ≤ 1 / 2
    split_ifs
    · have : (2 : ℝ) ≤ uu T := by exact_mod_cast hst.uu_ge_two
      exact one_div_le_one_div_of_le (by norm_num) this
    · norm_num

theorem cross_sum_split (Sh : Finset (G ⊕ Fin t ⊕ QT T)) (f : (Fin t × G) ⊕ G → ℝ) :
    ∑ e ∈ univ.filter (fun e => (Γ T Ap Am g).crosses (Sh : Set _) e), f e =
      ∑ p : Fin t × G, (if (Γ T Ap Am g).crosses (Sh : Set _) (.inl p) then f (.inl p) else 0) +
      ∑ v : G, (if (Γ T Ap Am g).crosses (Sh : Set _) (.inr v) then f (.inr v) else 0) := by
  rw [sum_filter, Fintype.sum_sum_type]

theorem crosses_own {Sh : Finset (G ⊕ Fin t ⊕ QT T)} {i : Fin t} {x : G}
    (hx : x ∈ copyVerts Ap Am (g i)) :
    (Γ T Ap Am g).crosses (Sh : Set _) (.inl (i, x)) ↔
      ((.inl x : G ⊕ Fin t ⊕ QT T) ∈ Sh ↔ ¬ (.inr (.inl i) : G ⊕ Fin t ⊕ QT T) ∈ Sh) := by
  unfold SignedGraph.crosses
  rw [Γ_fst_inl, Γ_snd_inl, ite_eq_left hx]
  simp only [mem_coe, ne_eq]
  tauto

theorem crosses_res (ho : Odd (uu T)) {Sh : Finset (G ⊕ Fin t ⊕ QT T)} {v : G} :
    (Γ T Ap Am g).crosses (Sh : Set _) (.inr v) ↔
      ((.inl v : G ⊕ Fin t ⊕ QT T) ∈ Sh ↔
        ¬ (.inr (.inr (QuotientGroup.mk v)) : G ⊕ Fin t ⊕ QT T) ∈ Sh) := by
  unfold SignedGraph.crosses
  rw [Γ_fst_inr, Γ_snd_inr, ite_eq_left ho]
  simp only [mem_coe, ne_eq]
  tauto

/-- **Slack for cuts splitting the copies of a coset** (Lemma 5.2): at least `min(m, |T|/2)`
vertices lie in copies on both sides, each contributing an incidence of value `≥ c/(3λ)`. -/
theorem slack_split (hst : Standing T Ap Am g S c lam) {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am)
    (U' : Finset (G ⊕ Fin t ⊕ QT T)) (q : QT T) (hU' : ∀ u ∈ U', cosV T g a₀ u = q)
    {i₁ i₂ : Fin t} (h1 : (.inr (.inl i₁) : G ⊕ Fin t ⊕ QT T) ∈ U')
    (h2 : (.inr (.inl i₂) : G ⊕ Fin t ⊕ QT T) ∉ U')
    (h2q : (QuotientGroup.mk (g i₂ * a₀) : QT T) = q) :
    1 ≤ ∑ e ∈ univ.filter (fun e => (Γ T Ap Am g).crosses (U' : Set _) e), xvec T Ap Am g e := by
  set I₁ := univ.filter fun i : Fin t => (.inr (.inl i) : G ⊕ Fin t ⊕ QT T) ∈ U' with hI₁
  set I₂ := univ.filter fun i : Fin t => (.inr (.inl i) : G ⊕ Fin t ⊕ QT T) ∉ U' ∧
    (QuotientGroup.mk (g i * a₀) : QT T) = q with hI₂
  set x₀ := g i₁ * a₀ with hx₀
  have hx₀q : (QuotientGroup.mk x₀ : QT T) = q := hU' _ h1
  have hlam := hst.lam_pos
  have hc := hst.c_pos
  have hcover : ∀ x : G, ∀ s ∈ T, ∃ i,
      (templateGraph T Ap Am).Adj ((g i)⁻¹ * x) ((g i)⁻¹ * (x * s)) := by
    intro x s hs
    have h := hst.cover.occ_lower x s hs
    have hf := hst.temp.density s hs
    have hpos : 0 < occ T Ap Am g x s := by
      have : (0 : ℝ) < occ T Ap Am g x s := lt_of_lt_of_le (by positivity) h
      exact_mod_cast this
    unfold occ at hpos
    obtain ⟨i, hi⟩ := card_pos.1 hpos
    exact ⟨i, (mem_filter.1 hi).2⟩
  have hcoset : ∀ i, i ∈ I₁ ∪ I₂ ↔ ∃ v ∈ copyVerts Ap Am (g i),
      x₀⁻¹ * v ∈ Subgroup.closure (T : Set G) := by
    intro i
    constructor
    · intro hi
      have hiq : (QuotientGroup.mk (g i * a₀) : QT T) = q := by
        rcases mem_union.1 hi with h | h
        · exact hU' _ (mem_filter.1 h).2
        · exact (mem_filter.1 h).2.2
      refine ⟨g i * a₀, mem_copyVerts.2 (by simpa using ha₀), ?_⟩
      rw [← QuotientGroup.eq, hx₀q, hiq]
    · rintro ⟨v, hv, hvU⟩
      have hvq : (QuotientGroup.mk v : QT T) = q := by
        rw [← hx₀q]; exact (QuotientGroup.eq.2 hvU).symm
      have hiq : (QuotientGroup.mk (g i * a₀) : QT T) = q :=
        (copy_coset hst.temp.connected ha₀ hv).trans hvq
      by_cases hin : (.inr (.inl i) : G ⊕ Fin t ⊕ QT T) ∈ U'
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hin⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hin, hiq⟩)
  have hdisj : Disjoint I₁ I₂ := by
    rw [disjoint_left]
    intro i hi hi'
    exact (mem_filter.1 hi').2.1 (mem_filter.1 hi).2
  have hT : IsConnectionSet T := ⟨hst.temp.symm, hst.one_notMem⟩
  have hTne : T.Nonempty := card_pos.1 (by exact_mod_cast hst.T_pos)
  have hB := incidence_cut T Ap Am hT hTne hst.temp.connected g hcover x₀ I₁ I₂ hdisj
    ⟨i₁, mem_filter.2 ⟨mem_univ _, h1⟩⟩ ⟨i₂, mem_filter.2 ⟨mem_univ _, h2, h2q⟩⟩ hcoset
  set B := univ.filter fun v => (∃ i ∈ I₁, v ∈ copyVerts Ap Am (g i)) ∧
    (∃ i ∈ I₂, v ∈ copyVerts Ap Am (g i)) with hBdef
  have hBcard : c * S.card / 2 ≤ B.card := by
    have hmd := (card_VF hc.le hst.temp).2.1
    have hTd := hst.temp.card_T
    have hd := hst.d_pos
    rcases hB with h | h
    · have : ((Ap ∪ Am).card : ℝ) ≤ B.card := by exact_mod_cast h
      nlinarith
    · have : (T.card : ℝ) ≤ 2 * B.card := by exact_mod_cast h
      linarith
  rw [cross_sum_split]
  have hinr : 0 ≤ ∑ v : G, (if (Γ T Ap Am g).crosses (U' : Set _) (.inr v) then
      xvec T Ap Am g (.inr v) else 0) :=
    sum_nonneg fun v _ => by split_ifs; exacts [xvec_nonneg _, le_rfl]
  have hnn : ∀ p : Fin t × G, 0 ≤ (if (Γ T Ap Am g).crosses (U' : Set _) (.inl p) then
      xvec T Ap Am g (.inl p) else 0) := fun p => by
    split_ifs; exacts [xvec_nonneg _, le_rfl]
  have hinl : ∑ v ∈ B, c / (3 * lam) ≤ ∑ p : Fin t × G,
      (if (Γ T Ap Am g).crosses (U' : Set _) (.inl p) then xvec T Ap Am g (.inl p) else 0) := by
    rw [Fintype.sum_prod_type, sum_comm]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ B)
      (fun v _ _ => sum_nonneg fun i _ => hnn (i, v)))
    refine sum_le_sum fun v hv => ?_
    obtain ⟨⟨i, hi, hvi⟩, ⟨j, hj, hvj⟩⟩ := (mem_filter.1 hv).2
    have key : ∀ k, v ∈ copyVerts Ap Am (g k) →
        (Γ T Ap Am g).crosses (U' : Set _) (.inl (k, v)) →
        c / (3 * lam) ≤ ∑ i', (if (Γ T Ap Am g).crosses (U' : Set _) (.inl (i', v)) then
          xvec T Ap Am g (.inl (i', v)) else 0) := by
      intro k hk hcr
      refine le_trans ?_ (single_le_sum (fun i' _ => hnn (i', v)) (mem_univ k))
      rw [ite_eq_left hcr]
      exact (hst.πG_bounds hk).1
    by_cases hvU : (.inl v : G ⊕ Fin t ⊕ QT T) ∈ U'
    · refine key j hvj ((crosses_own hvj).2 ?_)
      have := (mem_filter.1 hj).2.1
      tauto
    · refine key i hvi ((crosses_own hvi).2 ?_)
      have := (mem_filter.1 hi).2
      tauto
  have : 1 ≤ ∑ v ∈ B, c / (3 * lam) := by
    rw [sum_const, nsmul_eq_mul]
    have hsl := hst.slack
    calc (1 : ℝ) ≤ c * S.card / 2 * (c / (3 * lam)) := by
          rw [show c * S.card / 2 * (c / (3 * lam)) = c ^ 2 * S.card / (6 * lam) by
            field_simp; ring, le_div_iff₀ (by positivity)]
          linarith
      _ ≤ B.card * (c / (3 * lam)) := by gcongr
  linarith

/-- **Slack for cuts with all copies on one side**: the shore without copy nodes has weight
`|A|` (no auxiliary node) or `θ|A| + (u - |A|)/u = 1 + (1 - 2/u)|A|` (with it). -/
theorem slack_shore (hst : Standing T Ap Am g S c lam) {a₀ : G}
    (Sh : Finset (G ⊕ Fin t ⊕ QT T)) (q : QT T) (hSh : ∀ u ∈ Sh, cosV T g a₀ u = q)
    (hnocopy : ∀ i : Fin t, (.inr (.inl i) : G ⊕ Fin t ⊕ QT T) ∉ Sh)
    (hne : (∃ v : G, (.inl v : G ⊕ Fin t ⊕ QT T) ∈ Sh) ∨
      (Odd (uu T) ∧ (.inr (.inr q) : G ⊕ Fin t ⊕ QT T) ∈ Sh)) :
    1 ≤ ∑ e ∈ univ.filter (fun e => (Γ T Ap Am g).crosses (Sh : Set _) e), xvec T Ap Am g e := by
  set A := univ.filter fun v : G => (.inl v : G ⊕ Fin t ⊕ QT T) ∈ Sh with hA
  have hAq : ∀ v ∈ A, (QuotientGroup.mk v : QT T) = q := fun v hv => hSh _ (mem_filter.1 hv).2
  rw [cross_sum_split]
  have hown : θ T * A.card ≤ ∑ p : Fin t × G,
      (if (Γ T Ap Am g).crosses (Sh : Set _) (.inl p) then xvec T Ap Am g (.inl p) else 0) := by
    have hterm : ∀ p : Fin t × G, (if (.inl p.2 : G ⊕ Fin t ⊕ QT T) ∈ Sh then
        πG T Ap Am g p.1 p.2 else 0) ≤
        (if (Γ T Ap Am g).crosses (Sh : Set _) (.inl p) then xvec T Ap Am g (.inl p) else 0) := by
      rintro ⟨i, x⟩
      by_cases hxS : (.inl x : G ⊕ Fin t ⊕ QT T) ∈ Sh
      · rw [ite_eq_left hxS]
        by_cases hx : x ∈ copyVerts Ap Am (g i)
        · rw [ite_eq_left ((crosses_own hx).2 (by have := hnocopy i; tauto))]
          rfl
        · rw [πG_eq_zero hx]
          split_ifs
          · exact xvec_nonneg _
          · exact le_rfl
      · rw [ite_eq_right hxS]
        split_ifs
        · exact xvec_nonneg _
        · exact le_rfl
    refine le_trans (le_of_eq ?_) (sum_le_sum fun p _ => hterm p)
    rw [Fintype.sum_prod_type, sum_comm]
    have : ∀ v : G, ∑ i : Fin t, (if (.inl v : G ⊕ Fin t ⊕ QT T) ∈ Sh then
        πG T Ap Am g i v else 0) = if v ∈ A then θ T else 0 := by
      intro v
      by_cases hv : (.inl v : G ⊕ Fin t ⊕ QT T) ∈ Sh
      · have hvA : v ∈ A := mem_filter.2 ⟨mem_univ _, hv⟩
        simp only [ite_eq_left hv, ite_eq_left hvA]
        unfold πG
        rw [← mul_sum, sum_xG_eq_one hst, mul_one]
      · have hvA : v ∉ A := fun h => hv (mem_filter.1 h).2
        simp only [ite_eq_right hv, ite_eq_right hvA, sum_const_zero]
    simp_rw [this]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul, mul_comm]
  have hsub_ge : ∀ s : Finset G, (∀ v ∈ s, (Γ T Ap Am g).crosses (Sh : Set _) (.inr v)) →
      ∑ v ∈ s, xvec T Ap Am g (.inr v) ≤ ∑ v : G,
        (if (Γ T Ap Am g).crosses (Sh : Set _) (.inr v) then xvec T Ap Am g (.inr v) else 0) := by
    intro s hs
    calc ∑ v ∈ s, xvec T Ap Am g (.inr v) = ∑ v ∈ s,
          (if (Γ T Ap Am g).crosses (Sh : Set _) (.inr v) then xvec T Ap Am g (.inr v) else 0) :=
          sum_congr rfl fun v hv => (ite_eq_left (hs v hv)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun v _ _ => by
          split_ifs
          · exact xvec_nonneg _
          · exact le_rfl)
  have hres0 : 0 ≤ ∑ v : G,
      (if (Γ T Ap Am g).crosses (Sh : Set _) (.inr v) then xvec T Ap Am g (.inr v) else 0) :=
    sum_nonneg fun v _ => by
      split_ifs
      · exact xvec_nonneg _
      · exact le_rfl
  have hAne : (∃ v : G, (.inl v : G ⊕ Fin t ⊕ QT T) ∈ Sh) → (1 : ℝ) ≤ A.card := by
    rintro ⟨v, hv⟩
    exact_mod_cast card_pos.2 ⟨v, mem_filter.2 ⟨mem_univ _, hv⟩⟩
  by_cases ho : Odd (uu T)
  · have hu3 : (3 : ℝ) ≤ uu T := by
      have h2 := hst.uu_ge_two
      have : 3 ≤ uu T := by rcases ho with ⟨k, hk⟩; omega
      exact_mod_cast this
    have hxres : ∀ v, xvec T Ap Am g (.inr v) = 1 / (uu T : ℝ) := fun v => by
      simp [xvec, ho]
    have hθval : θ T = 1 - 1 / (uu T : ℝ) := by simp [θ, ho]
    by_cases haux : (.inr (.inr q) : G ⊕ Fin t ⊕ QT T) ∈ Sh
    · set Bq := (univ.filter fun v : G => (QuotientGroup.mk v : QT T) = q) \ A with hBq
      have hsub : A ⊆ univ.filter fun v : G => (QuotientGroup.mk v : QT T) = q :=
        fun v hv => mem_filter.2 ⟨mem_univ _, hAq v hv⟩
      have hBqcard : (Bq.card : ℝ) = uu T - A.card := by
        rw [hBq, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub), coset_card_nat]
      have h2 := hsub_ge Bq (fun v hv => by
        have hv' := mem_sdiff.1 hv
        have hvq : (QuotientGroup.mk v : QT T) = q := (mem_filter.1 hv'.1).2
        have hvS : (.inl v : G ⊕ Fin t ⊕ QT T) ∉ Sh := fun h => hv'.2 (mem_filter.2 ⟨mem_univ _, h⟩)
        refine (crosses_res ho).2 ?_
        rw [hvq]
        tauto)
      rw [sum_congr rfl (fun v _ => hxres v), sum_const, nsmul_eq_mul, hBqcard] at h2
      have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
      have key : 1 ≤ θ T * A.card + (uu T - A.card) * (1 / uu T) := by
        rw [hθval]
        have hu0 : (0 : ℝ) < uu T := by linarith
        rw [← sub_nonneg]
        have : θ T * 0 = 0 := by ring
        have e : (1 - 1 / (uu T : ℝ)) * A.card + (uu T - A.card) * (1 / uu T) - 1 =
            A.card * (uu T - 2) / uu T := by field_simp; ring
        rw [e]
        exact div_nonneg (mul_nonneg hA0 (by linarith)) hu0.le
      linarith
    · have hA1 := hAne (hne.resolve_right (fun h => haux h.2))
      have h2 := hsub_ge A (fun v hv => by
        refine (crosses_res ho).2 ?_
        rw [hAq v hv]
        have := (mem_filter.1 hv).2
        tauto)
      rw [sum_congr rfl (fun v _ => hxres v), sum_const, nsmul_eq_mul] at h2
      have e : θ T * A.card + A.card * (1 / uu T) = A.card := by
        rw [hθval]
        have hu0 : (0 : ℝ) < uu T := by linarith
        field_simp
        ring
      linarith
  · have hθ1 : θ T = 1 := by simp [θ, ho]
    have hA1 := hAne (hne.resolve_right (fun h => ho h.1))
    rw [hθ1, one_mul] at hown
    linarith

/-- **The slack-cut condition (4.2)** for the signed system of §5.2. -/
theorem slack (hst : Standing T Ap Am g S c lam) {a₀ : G} (ha₀ : a₀ ∈ Ap ∪ Am)
    (U' : Finset (G ⊕ Fin t ⊕ QT T))
    (hU1 : ∀ v ∈ U', ∀ w ∈ U', (Γ T Ap Am g).underlying.Reachable v w)
    (hU2 : ∃ v ∈ U', ∃ w ∉ U', (Γ T Ap Am g).underlying.Reachable v w) :
    1 ≤ ∑ e ∈ univ.filter (fun e => (Γ T Ap Am g).crosses (U' : Set _) e),
      min (xvec T Ap Am g e) (1 - xvec T Ap Am g e) := by
  have hmin : ∀ e, min (xvec T Ap Am g e) (1 - xvec T Ap Am g e) = xvec T Ap Am g e :=
    fun e => min_eq_left (by linarith [xvec_le_half hst e])
  simp_rw [hmin]
  obtain ⟨v₀, hv₀, w₀, hw₀, hr⟩ := hU2
  set q := cosV T g a₀ v₀ with hq
  have hU'q : ∀ u ∈ U', cosV T g a₀ u = q :=
    fun u hu => (reach_coset hst ha₀ (hU1 v₀ hv₀ u hu)).symm
  have hw₀q : cosV T g a₀ w₀ = q := (reach_coset hst ha₀ hr).symm
  by_cases hsplit : ∃ i₁ i₂ : Fin t, (.inr (.inl i₁) : G ⊕ Fin t ⊕ QT T) ∈ U' ∧
      (.inr (.inl i₂) : G ⊕ Fin t ⊕ QT T) ∉ U' ∧ (QuotientGroup.mk (g i₂ * a₀) : QT T) = q
  · obtain ⟨i₁, i₂, h1, h2, h3⟩ := hsplit
    exact slack_split hst ha₀ U' q hU'q h1 h2 h3
  · push Not at hsplit
    by_cases hcop : ∃ i : Fin t, (.inr (.inl i) : G ⊕ Fin t ⊕ QT T) ∈ U'
    · obtain ⟨i₁, hi₁⟩ := hcop
      set Sh := (univ.filter fun w => cosV T g a₀ w = q) \ U' with hSh
      have hcross : ∀ e, (Γ T Ap Am g).crosses (U' : Set _) e ↔
          (Γ T Ap Am g).crosses (Sh : Set _) e := by
        intro e
        unfold SignedGraph.crosses
        simp only [mem_coe, hSh, mem_sdiff, mem_filter, mem_univ, true_and]
        rcases edge_coset hst ha₀ e with h | h
        · rw [h]; simp
        · by_cases hq' : cosV T g a₀ ((Γ T Ap Am g).fst e) = q
          · have hq'' : cosV T g a₀ ((Γ T Ap Am g).snd e) = q := h ▸ hq'
            simp only [hq', hq'', true_and]
            tauto
          · have hq'' : cosV T g a₀ ((Γ T Ap Am g).snd e) ≠ q := h ▸ hq'
            have n1 : (Γ T Ap Am g).fst e ∉ U' := fun hh => hq' (hU'q _ hh)
            have n2 : (Γ T Ap Am g).snd e ∉ U' := fun hh => hq'' (hU'q _ hh)
            simp [hq', hq'', n1, n2]
      rw [filter_congr (fun e _ => hcross e)]
      refine slack_shore hst Sh q (fun u hu => (mem_filter.1 (mem_sdiff.1 hu).1).2)
        (fun i hi => ?_) ?_
      · have hi' := mem_sdiff.1 hi
        exact hsplit i₁ i hi₁ hi'.2 (mem_filter.1 hi'.1).2
      · rcases w₀ with x | j | q'
        · exact Or.inl ⟨x, mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, hw₀q⟩, hw₀⟩⟩
        · exact absurd hw₀q (hsplit i₁ j hi₁ hw₀)
        · right
          have ho : Odd (uu T) := by
            by_contra he
            have := reach_aux_even he hr.symm
            exact hw₀ (by rw [← this]; exact hv₀)
          refine ⟨ho, ?_⟩
          have hq' : q' = q := hw₀q
          rw [← hq']
          exact mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, hw₀q⟩, hw₀⟩
    · push Not at hcop
      refine slack_shore hst U' q hU'q hcop ?_
      rcases v₀ with x | j | q'
      · exact Or.inl ⟨x, hv₀⟩
      · exact absurd hv₀ (hcop j)
      · right
        have ho : Odd (uu T) := by
          by_contra he
          have := reach_aux_even he hr
          exact hw₀ (by rw [this]; exact hv₀)
        exact ⟨ho, hv₀⟩

end Rounding2

/-- **§5.2, application of Lemmas 4.1 and 4.2.** The point `π` satisfies the equations, the
parity condition (total demand `u` or `u + 1` per coset), and the slack-cut condition (4.2)
(Lemma 5.2 for cuts splitting copies; the computation `θ|A| + (u - |A|)/u ≥ 1` otherwise), so
it lies in the integral hull and signed swap rounding gives a rounding law. -/
theorem rounding_exists {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    {S T Ap Am : Finset G} {t : ℕ} {g : Fin t → G} {c lam : ℝ}
    (hst : Standing T Ap Am g S c lam) :
    ∃ μ₀ : FinDist ((Fin t × G) ⊕ G → ℝ), IsRounding T Ap Am g μ₀ := by
  classical
  obtain ⟨a₀, ha₀⟩ := (card_VF hst.c_pos.le hst.temp).1
  have hx : ∀ e, 0 ≤ xvec T Ap Am g e ∧ xvec T Ap Am g e ≤ 1 :=
    fun e => ⟨xvec_nonneg e, by linarith [xvec_le_half hst e]⟩
  have hBx : ∀ v, (Γ T Ap Am g).apply (xvec T Ap Am g) v = (bd T v : ℝ) := by
    intro v
    rcases v with v | j | q
    · rw [apply_inl]
      have : ∑ i, (if v ∈ copyVerts Ap Am (g i) then xvec T Ap Am g (.inl (i, v)) else 0) =
          θ T := by
        rw [← mul_one (θ T), ← sum_xG_eq_one hst v, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        by_cases hv : v ∈ copyVerts Ap Am (g i)
        · rw [ite_eq_left hv]; rfl
        · rw [ite_eq_right hv, xG_eq_zero hv, mul_zero]
      rw [this]
      by_cases ho : Odd (uu T)
      · simp [xvec, bd, θ, ho]
      · simp [bd, θ, ho]
    · rw [apply_copy]
      have := xG_balance hst j
      simpa [bd, xvec] using this
    · rw [apply_aux]
      by_cases ho : Odd (uu T)
      · rw [ite_eq_left ho]
        have hxr : ∀ v, xvec T Ap Am g (.inr v) = 1 / (uu T : ℝ) := fun v => by simp [xvec, ho]
        simp only [hxr]
        rw [sum_const, nsmul_eq_mul, coset_card]
        have hu0 : (0 : ℝ) < uu T := by exact_mod_cast uu_pos T
        field_simp
        simp [bd, ho]
      · simp [bd, ho]
  have hconv := robust_signed_integrality (Γ T Ap Am g) (bd T) (parity hst ha₀)
    (xvec T Ap Am g) hx hBx (slack hst ha₀)
  obtain ⟨μ, hlp, hsupp⟩ := signed_swap_rounding (Γ T Ap Am g) (fun v => (bd T v : ℝ))
    (xvec T Ap Am g) hconv
  exact ⟨μ, _, fun h hh => hh, hlp, hsupp⟩


/-- The numerical requirements of §5.3 on `d ≥ K L^{12}`. -/
theorem numeric_choice (c η : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ L d : ℝ, 1 ≤ L → K * L ^ 12 ≤ d →
      256 * L ≤ c * d ∧ 6 * (256 * L) ≤ c ^ 2 * d ∧
      4 * L ≤ (c ^ 2 * d / (3 * (256 * L))) / 192 ∧
      (∀ D : ℝ, c ^ 2 / 18 * c * d / (8 * (256 * L)) ≤ D →
        4 * L ≤ (η * (c / L ^ 2 / 8) * D) ^ 2 / (32 * (D + η * (c / L ^ 2 / 8) * D))) ∧
      5 * L ≤ (c / L ^ 2 / 4) ^ 2 * c ^ 2 * √d / (43008 * (256 * L)) := by
  set K1 := 256 / c with hK1
  set K2 := 1536 / c ^ 2 with hK2
  set K3 := 589824 / c ^ 2 with hK3
  set K4 := 603979776 / (η ^ 2 * c ^ 5) with hK4
  set Q := 880803840 / c ^ 4 with hQ
  have h1 : 0 < K1 := by positivity
  have h2 : 0 < K2 := by positivity
  have h3 : 0 < K3 := by positivity
  have h4 : 0 < K4 := by positivity
  have h5 : 0 < Q ^ 2 := by positivity
  refine ⟨K1 + K2 + K3 + K4 + Q ^ 2, by positivity, ?_⟩
  intro L d hL hd
  have hL0 : 0 < L := by linarith
  have hdK : ∀ K' : ℝ, 0 ≤ K' → K' ≤ K1 + K2 + K3 + K4 + Q ^ 2 → ∀ k ≤ 12, K' * L ^ k ≤ d := by
    intro K' hK' hle k hk
    calc K' * L ^ k ≤ (K1 + K2 + K3 + K4 + Q ^ 2) * L ^ 12 :=
          mul_le_mul hle (pow_le_pow_right₀ hL hk) (by positivity) (by positivity)
      _ ≤ d := hd
  have d1 := hdK K1 h1.le (by linarith) 1 (by norm_num)
  have d2 := hdK K2 h2.le (by linarith) 1 (by norm_num)
  have d3 := hdK K3 h3.le (by linarith) 2 (by norm_num)
  have d4 := hdK K4 h4.le (by linarith) 6 (by norm_num)
  have d5 := hdK (Q ^ 2) h5.le (by linarith) 12 le_rfl
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) d1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc 256 * L = c * (K1 * L ^ 1) := by rw [hK1]; field_simp
      _ ≤ c * d := by gcongr
  · calc 6 * (256 * L) = c ^ 2 * (K2 * L ^ 1) := by rw [hK2]; field_simp; ring
      _ ≤ c ^ 2 * d := by gcongr
  · rw [div_div, le_div_iff₀ (by positivity)]
    calc 4 * L * (3 * (256 * L) * 192) = c ^ 2 * (K3 * L ^ 2) := by rw [hK3]; field_simp; ring
      _ ≤ c ^ 2 * d := by gcongr
  · intro D hD
    set a := η * (c / L ^ 2 / 8) with ha_def
    have ha0 : 0 < a := by positivity
    have ha1 : a ≤ 1 := by
      have : c / L ^ 2 / 8 ≤ 1 := by
        rw [div_div, div_le_one (by positivity)]
        nlinarith [one_le_pow₀ (n := 2) hL]
      calc a ≤ 1 * 1 := mul_le_mul hη1 this (by positivity) (by norm_num)
        _ = 1 := by norm_num
    have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
    have hkey : 256 * L ≤ a ^ 2 * D := by
      calc 256 * L = a ^ 2 * (c ^ 2 / 18 * c * (K4 * L ^ 6) / (8 * (256 * L))) := by
            rw [ha_def, hK4]; field_simp; ring
        _ ≤ a ^ 2 * (c ^ 2 / 18 * c * d / (8 * (256 * L))) := by gcongr
        _ ≤ a ^ 2 * D := by gcongr
    rw [le_div_iff₀ (by positivity)]
    calc 4 * L * (32 * (D + a * D)) ≤ 4 * L * (32 * (D + 1 * D)) := by gcongr
      _ = 256 * L * D := by ring
      _ ≤ a ^ 2 * D * D := by gcongr
      _ = (a * D) ^ 2 := by ring
  · have hsq : Q * L ^ 6 ≤ √d := by
      rw [Real.le_sqrt (by positivity) hd0.le]
      calc (Q * L ^ 6) ^ 2 = Q ^ 2 * L ^ 12 := by ring
        _ ≤ d := d5
    rw [le_div_iff₀ (by positivity)]
    calc 5 * L * (43008 * (256 * L)) = (c / L ^ 2 / 4) ^ 2 * c ^ 2 * (Q * L ^ 6) := by
          rw [hQ]; field_simp; ring
      _ ≤ (c / L ^ 2 / 4) ^ 2 * c ^ 2 * √d := by gcongr

end WP

open WP in
/-- **Proposition 5.3 (Weighted partition).** Given the template of Lemma 5.1 (constant `cT`),
there are constants such that, for every `c₁ > 0`, if `d ≥ K L^{12}` and `n` is large, there is a
reference degree `D = Θ(d/L)` and a random allocation (the outcome of the rounding experiment of
Sections 5.2–5.3, for a fixed good translate cover) which, with probability at least `7/8`,
satisfies (5.15)–(5.16) with `λ = A₀ L`, `σ = cσ L^{-2}`, degree error `c₁ σ` and weights in
`[ω, 1]`; moreover, when `u = |⟨T⟩|` is odd, the reserved set is a uniformly random transversal
of the left `⟨T⟩`-cosets (5.7). -/
theorem weighted_partition (cT : ℝ) (hcT : 0 < cT) :
    ∃ ω A₀ cσ cD CD cN CN : ℝ, 0 < ω ∧ 0 < A₀ ∧ 0 < cσ ∧ 0 < cD ∧ cD ≤ CD ∧ 0 < cN ∧
      cN ≤ CN ∧
      ∀ c₁ : ℝ, 0 < c₁ → ∃ K : ℝ, ∃ n₀ : ℕ,
        ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (S T Ap Am : Finset G),
          IsConnectionSet S → (cayleyGraph S).Connected → n₀ ≤ Fintype.card G →
          K * Real.log (Fintype.card G) ^ 12 ≤ S.card →
          IsTemplate S T Ap Am cT →
          ∃ D : ℝ, cD * S.card / Real.log (Fintype.card G) ≤ D ∧
            D ≤ CD * S.card / Real.log (Fintype.card G) ∧
            ∃ μ : FinDist (Allocation G),
              μ.P (fun 𝒜 => ¬ 𝒜.Good S T Ap Am (A₀ * Real.log (Fintype.card G)) D
                (cσ / Real.log (Fintype.card G) ^ 2)
                (c₁ * (cσ / Real.log (Fintype.card G) ^ 2)) ω cN CN) ≤ 1 / 8 ∧
              ReservationLaw μ T := by
  set c := min cT 1 with hc_def
  have hc : 0 < c := lt_min hcT one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hccT : c ≤ cT := min_le_left _ _
  refine ⟨c ^ 2 / 9216, 256, c / 8, c ^ 2 / 18 * c / (8 * 256), 3 * (c ^ 2 / 18) / (2 * 256),
    c ^ 2 / 6, 32, by positivity, by norm_num, by positivity, by positivity, ?_, by positivity,
    ?_, ?_⟩
  · have h3 : c ^ 3 ≤ c ^ 2 := by nlinarith [sq_nonneg c]
    have : c ^ 2 / 18 * c / (8 * 256) = c ^ 3 / 36864 := by ring
    rw [this]
    have : 3 * (c ^ 2 / 18) / (2 * 256) = c ^ 2 / 3072 := by ring
    rw [this]
    nlinarith [sq_nonneg c]
  · nlinarith [sq_nonneg c]
  intro c₁ hc₁
  set η' := min c₁ (1 / 4) with hη'_def
  have hη' : 0 < η' := lt_min hc₁ (by norm_num)
  have hη'c : η' ≤ c₁ := min_le_left _ _
  have hη'4 : η' ≤ 1 / 4 := min_le_right _ _
  obtain ⟨K, hK, hnum⟩ := numeric_choice c η' hc hc1 hη' (by linarith)
  refine ⟨K, 8, ?_⟩
  intro G _ _ _ S T Ap Am hS hconn hn hd htemp
  have htemp' := WP.IsTemplate.mono htemp hc.le hccT
  set n := Fintype.card G with hn_def
  set L := Real.log n with hL_def
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hexpL : Real.exp L = n := Real.exp_log hnpos
  have hL : 1 ≤ L := by
    rw [hL_def, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨hne, hmd, hmn⟩ := card_VF hc.le htemp'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hnum L S.card hL hd
  set lam := 256 * L with hlam_def
  obtain ⟨t, g, htn, hcov⟩ := translate_cover T Ap Am lam (by omega) le_rfl (by linarith)
    htemp'.density
  have hst : Standing T Ap Am g S c lam := ⟨hS, htemp', hc, hc1, hcov, by linarith, h2, hL⟩
  obtain ⟨μ₀, hμ₀⟩ := rounding_exists hst
  obtain ⟨a₀, ha₀⟩ := hne
  have hlampos : 0 < lam := by positivity
  have hkl : 0 ≤ c ^ 2 / 18 / lam := by positivity
  obtain ⟨hD1, hD2⟩ := Dref_bounds' hst (κ := c ^ 2 / 18) (by positivity)
  set D := Dref T Ap Am (c ^ 2 / 18) lam with hD_def
  refine ⟨D, ?_, ?_, pushDist (fun ζ => alloc T Ap Am g (c ^ 2 / 18) lam hkl (glue T g a₀ ζ))
    (FinDist.pi fun _ : QT T => μ₀), ?_, reservation_law T Ap Am g hkl hst hμ₀ a₀⟩
  · calc c ^ 2 / 18 * c / (8 * 256) * S.card / L = c ^ 2 / 18 * c * S.card / (8 * lam) := by
          rw [hlam_def]; field_simp
      _ ≤ D := hD1
  · calc D ≤ 3 * (c ^ 2 / 18) * S.card / (2 * lam) := hD2
      _ = 3 * (c ^ 2 / 18) / (2 * 256) * S.card / L := by rw [hlam_def]; field_simp
  · obtain ⟨ok, hok, hlp, hint⟩ := hμ₀
    set σ0 := c / L ^ 2 / 4 with hσ0_def
    have hσ0 : 0 < σ0 := by positivity
    have hσ01 : σ0 ≤ 1 := by
      rw [hσ0_def, div_div, div_le_one (by positivity)]
      nlinarith
    set η := η' * (c / L ^ 2 / 8) with hη_def
    have hηpos : 0 < η := by positivity
    have hσ : c / 8 / L ^ 2 = σ0 / 2 := by rw [hσ0_def]; ring
    have hηη : η ≤ c₁ * (c / 8 / L ^ 2) := by
      rw [hη_def, show c / 8 / L ^ 2 = c / L ^ 2 / 8 by ring]
      exact mul_le_mul_of_nonneg_right hη'c (by positivity)
    have hησ : η ≤ σ0 / 4 := by
      rw [hη_def, hσ0_def]
      have : 0 ≤ c / L ^ 2 := by positivity
      nlinarith
    have hη1 : η ≤ 1 := by linarith
    rw [P_pushDist]
    -- the failure of `Good` forces the failure of some copy event
    have hstep : ∀ ζ ∈ (FinDist.pi fun _ : QT T => μ₀).support,
        ¬ (alloc T Ap Am g (c ^ 2 / 18) lam hkl (glue T g a₀ ζ)).Good S T Ap Am
          (256 * L) D (c / 8 / L ^ 2) (c₁ * (c / 8 / L ^ 2)) (c ^ 2 / 9216) (c ^ 2 / 6) 32 →
        ∃ i ∈ (univ : Finset (Fin t)), ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i
          (ζ (QuotientGroup.mk (g i * a₀))) := by
      intro ζ hζ hbad
      by_contra hall
      push Not at hall
      apply hbad
      have hz := glue_integral hst ha₀ ζ
        (fun q => hint _ ((mem_pi_support _ ζ).1 hζ q))
      rw [hσ] at hηη ⊢
      exact good_of_copies hst hkl hz hηpos.le hηη hσ0 hσ01 hησ
        (fun i => hall i (mem_univ i))
    have hcopy : ∀ i : Fin t, μ₀.P (fun z => ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i z) ≤
        8 * (Ap ∪ Am).card * Real.exp (-(4 * L)) := by
      intro i
      have hb := prob_copy hst ⟨ok, hok, hlp, hint⟩ i η hηpos hη1
      have hm1 : (1 : ℝ) ≤ (Ap ∪ Am).card := by
        have := (card_VF hc.le htemp').1.card_pos
        exact_mod_cast this
      have e1 : Real.exp (-((c ^ 2 * S.card / (3 * lam)) / 192)) ≤ Real.exp (-(4 * L)) :=
        Real.exp_le_exp.2 (by linarith)
      have e2 : Real.exp (-((η * D) ^ 2 / (32 * (D + η * D)))) ≤ Real.exp (-(4 * L)) := by
        apply Real.exp_le_exp.2
        have := h4 D hD1
        rw [hη_def]
        linarith
      have e3 : (Ap ∪ Am).card * Real.exp (-((c / L ^ 2 / 4) ^ 2 * c ^ 2 * √(S.card : ℝ) /
          (43008 * lam))) ≤ Real.exp (-(4 * L)) := by
        calc (Ap ∪ Am).card * Real.exp (-((c / L ^ 2 / 4) ^ 2 * c ^ 2 * √(S.card : ℝ) /
              (43008 * lam))) ≤ Real.exp L * Real.exp (-(5 * L)) := by
              apply mul_le_mul _ (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
                (Real.exp_pos _).le
              rw [hexpL]; exact_mod_cast hmn
          _ = Real.exp (-(4 * L)) := by rw [← Real.exp_add]; ring_nf
      have hE := Real.exp_pos (-(4 * L))
      calc _ ≤ _ := hb
        _ ≤ 3 * Real.exp (-(4 * L)) + (Ap ∪ Am).card * (2 * Real.exp (-(4 * L)) +
            2 * Real.exp (-(4 * L))) + Real.exp (-(4 * L)) := by
          gcongr
        _ ≤ 8 * (Ap ∪ Am).card * Real.exp (-(4 * L)) := by
          have hEm : Real.exp (-(4 * L)) ≤ (Ap ∪ Am).card * Real.exp (-(4 * L)) :=
            le_mul_of_one_le_left hE.le hm1
          linarith
    calc (FinDist.pi fun _ : QT T => μ₀).P (fun ζ =>
          ¬ (alloc T Ap Am g (c ^ 2 / 18) lam hkl (glue T g a₀ ζ)).Good S T Ap Am
            (256 * L) D (c / 8 / L ^ 2) (c₁ * (c / 8 / L ^ 2)) (c ^ 2 / 9216) (c ^ 2 / 6) 32)
        ≤ (FinDist.pi fun _ : QT T => μ₀).P (fun ζ => ∃ i ∈ (univ : Finset (Fin t)),
            ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i (ζ (QuotientGroup.mk (g i * a₀)))) :=
          P_mono _ hstep
      _ ≤ ∑ i : Fin t, (FinDist.pi fun _ : QT T => μ₀).P (fun ζ =>
            ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i (ζ (QuotientGroup.mk (g i * a₀)))) :=
          P_exists_le _ _ _
      _ = ∑ i : Fin t, μ₀.P (fun z => ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i z) := by
          refine sum_congr rfl fun i _ => ?_
          exact pi_P_eval (fun _ : QT T => μ₀) (QuotientGroup.mk (g i * a₀))
            (fun z => ¬ GoodCopy T Ap Am g (c ^ 2 / 18) lam η σ0 i z)
      _ ≤ ∑ _i : Fin t, 8 * (Ap ∪ Am).card * Real.exp (-(4 * L)) := sum_le_sum fun i _ => hcopy i
      _ = t * (8 * (Ap ∪ Am).card * Real.exp (-(4 * L))) := by simp
      _ ≤ n * (8 * n * Real.exp (-(4 * L))) := by
          have ht' : (t : ℝ) ≤ n := by exact_mod_cast htn
          have hm' : ((Ap ∪ Am).card : ℝ) ≤ n := by exact_mod_cast hmn
          have := Real.exp_pos (-(4 * L))
          gcongr
      _ = 8 * Real.exp (-(2 * L)) := by
          rw [← hexpL]
          rw [show Real.exp L * (8 * Real.exp L * Real.exp (-(4 * L))) =
            8 * (Real.exp L * Real.exp L * Real.exp (-(4 * L))) by ring, ← Real.exp_add,
            ← Real.exp_add]
          ring_nf
      _ ≤ 1 / 8 := by
          have h64 : (64 : ℝ) ≤ Real.exp (2 * L) := by
            rw [show 2 * L = L + L by ring, Real.exp_add, hexpL]; nlinarith
          rw [Real.exp_neg]
          rw [div_eq_mul_inv] at *
          have := Real.exp_pos (2 * L)
          have : (Real.exp (2 * L))⁻¹ ≤ 64⁻¹ := inv_anti₀ (by norm_num) h64
          linarith

end Lovasz