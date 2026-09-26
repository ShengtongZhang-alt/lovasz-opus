/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.BMatchingPolytope

/-!
# Lemma 4.1: robust signed integrality

DAG node `L4.1` of `docs/BLUEPRINT.md`. Depends on the b-matching polytope.

Proof: every signed edge `e` is replaced by a gadget on the auxiliary vertices `a_e, c_e`
(a path `fst e — a_e — c_e — snd e` if both signs agree, a path `fst e — a_e — snd e` plus a
pendant edge `a_e — c_e` forced to `0` otherwise), and `bmatching_polytope` is applied to the
whole expanded graph at once. The blossom inequalities are checked gadget by gadget: a shore
whose original part splits a component uses the slack-cut hypothesis; otherwise the original
part is a union of components, has even demand, and some gadget has odd local parity.
-/

namespace Lovasz

open Finset

namespace SignedIntegrality

/-- The value carried by an edge end of sign `s` when the edge variable is `r`. -/
noncomputable def val (s : Bool) (r : ℝ) : ℝ := if s then r else 1 - r

/-- The value of the middle gadget edge: `1 - val s r` for a same-sign edge, `0` otherwise. -/
noncomputable def mid (s t : Bool) (r : ℝ) : ℝ := if s = t then 1 - val s r else 0

open Classical in
/-- Contribution of an edge to the left side of a blossom inequality: `c` says the edge
crosses the shore, `j` that it lies in `J`. -/
noncomputable def T (c j : Prop) (r : ℝ) : ℝ := if c then (if j then 1 - r else r) else 0

open Classical in
/-- Indicator of a proposition, as an integer. -/
noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

lemma val_mem (s : Bool) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ val s r ∧ val s r ≤ 1 := by
  cases s <;> simp [val] <;> constructor <;> linarith

lemma mid_mem (s t : Bool) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ mid s t r ∧ mid s t r ≤ 1 := by
  have := val_mem s h0 h1
  unfold mid; split_ifs <;> constructor <;> linarith

lemma T_nonneg (c j : Prop) {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ T c j r := by
  unfold T; split_ifs <;> linarith

lemma gadget_cross_aux (s t : Bool) {x m : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (hm1 : m ≤ x)
    (hm2 : m ≤ 1 - x) (P Q A C j0 j1 j2 : Prop) (hPQ : ¬(P ↔ Q)) :
    m ≤ T (¬(P ↔ A)) j0 (val s x) + T (¬(A ↔ C)) j1 (mid s t x) +
      T (¬((if s = t then C else A) ↔ Q)) j2 (val t x) := by
  classical
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hA : A <;> by_cases hC : C <;>
    cases s <;> cases t <;> simp [T, val, mid, hP, hQ, hA, hC] at hPQ ⊢ <;>
    split_ifs <;> linarith

lemma gadget_odd (s t : Bool) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (P A C j0 j1 j2 : Prop)
    (hj0 : j0 → ¬(P ↔ A)) (hj1 : j1 → ¬(A ↔ C)) (hj2 : j2 → ¬((if s = t then C else A) ↔ P))
    (hodd : Odd (ind A + ind (C ∧ s = t) + ind (P ∧ s = false) + ind (P ∧ t = false) +
      ind j0 + ind j1 + ind j2)) :
    1 ≤ T (¬(P ↔ A)) j0 (val s x) + T (¬(A ↔ C)) j1 (mid s t x) +
      T (¬((if s = t then C else A) ↔ P)) j2 (val t x) := by
  classical
  rw [Int.odd_iff] at hodd
  by_cases hP : P <;> by_cases hA : A <;> by_cases hC : C <;> cases s <;> cases t <;>
    by_cases h0' : j0 <;> by_cases h1' : j1 <;> by_cases h2' : j2 <;>
    simp [T, val, mid, ind, hP, hA, hC, h0', h1', h2'] at hodd hj0 hj1 hj2 ⊢ <;> linarith

section Expanded

variable {V E : Type*} (Γ : SignedGraph V E)

/-- First end of an edge of the expanded graph. The gadget of `e` is the path
`fst e — a_e — c_e — snd e` for a same-sign edge and `fst e — a_e — snd e` plus a pendant edge
`a_e — c_e` (forced to `0`) for a mixed-sign edge; `a_e = inr (inl e)`, `c_e = inr (inr e)`. -/
def eu (f : E × Fin 3) : V ⊕ E ⊕ E :=
  ![Sum.inl (Γ.fst f.1), Sum.inr (Sum.inl f.1),
    Sum.inr (if Γ.sfst f.1 = Γ.ssnd f.1 then Sum.inr f.1 else Sum.inl f.1)] f.2

/-- Second end of an edge of the expanded graph. -/
def ev (f : E × Fin 3) : V ⊕ E ⊕ E :=
  ![Sum.inr (Sum.inl f.1), Sum.inr (Sum.inr f.1), Sum.inl (Γ.snd f.1)] f.2

/-- The expanded point. -/
noncomputable def ey (x : E → ℝ) (f : E × Fin 3) : ℝ :=
  ![val (Γ.sfst f.1) (x f.1), mid (Γ.sfst f.1) (Γ.ssnd f.1) (x f.1), val (Γ.ssnd f.1) (x f.1)] f.2

@[simp] lemma eu_zero (e : E) : eu Γ (e, 0) = Sum.inl (Γ.fst e) := rfl
@[simp] lemma eu_one (e : E) : eu Γ (e, 1) = Sum.inr (Sum.inl e) := rfl
@[simp] lemma eu_two (e : E) :
    eu Γ (e, 2) = Sum.inr (if Γ.sfst e = Γ.ssnd e then Sum.inr e else Sum.inl e) := rfl
@[simp] lemma ev_zero (e : E) : ev Γ (e, 0) = Sum.inr (Sum.inl e) := rfl
@[simp] lemma ev_one (e : E) : ev Γ (e, 1) = Sum.inr (Sum.inr e) := rfl
@[simp] lemma ev_two (e : E) : ev Γ (e, 2) = Sum.inl (Γ.snd e) := rfl
@[simp] lemma ey_zero (x : E → ℝ) (e : E) : ey Γ x (e, 0) = val (Γ.sfst e) (x e) := rfl
@[simp] lemma ey_one (x : E → ℝ) (e : E) :
    ey Γ x (e, 1) = mid (Γ.sfst e) (Γ.ssnd e) (x e) := rfl
@[simp] lemma ey_two (x : E → ℝ) (e : E) : ey Γ x (e, 2) = val (Γ.ssnd e) (x e) := rfl

lemma eu_ne_ev (f : E × Fin 3) : eu Γ f ≠ ev Γ f := by
  obtain ⟨e, i⟩ := f
  fin_cases i <;> simp

/-- The coordinate of the expanded point that equals `x e`. -/
def idx (e : E) : Fin 3 := if Γ.sfst e then 0 else if Γ.ssnd e then 2 else 1

lemma ey_idx (x : E → ℝ) (e : E) : ey Γ x (e, idx Γ e) = x e := by
  unfold idx
  cases hs : Γ.sfst e <;> cases ht : Γ.ssnd e <;> simp [hs, ht, val, mid]

lemma ey_mem (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (f : E × Fin 3) :
    0 ≤ ey Γ x f ∧ ey Γ x f ≤ 1 := by
  obtain ⟨e, i⟩ := f
  fin_cases i
  · exact val_mem _ (hx e).1 (hx e).2
  · exact mid_mem _ _ (hx e).1 (hx e).2
  · exact val_mem _ (hx e).1 (hx e).2

lemma aux_relations (z : E × Fin 3 → ℝ) (e : E)
    (ha : z (e, 0) + z (e, 1) + (if Γ.sfst e = Γ.ssnd e then 0 else z (e, 2)) = 1)
    (hc : z (e, 1) + (if Γ.sfst e = Γ.ssnd e then z (e, 2) else 0) =
      if Γ.sfst e = Γ.ssnd e then 1 else 0) :
    z (e, 0) = val (Γ.sfst e) (z (e, idx Γ e)) ∧ z (e, 2) = val (Γ.ssnd e) (z (e, idx Γ e)) := by
  unfold idx val
  cases hs : Γ.sfst e <;> cases ht : Γ.ssnd e <;> simp [hs, ht] at ha hc ⊢ <;>
    first | (constructor <;> linarith) | linarith

section Deg

variable [Fintype E] [DecidableEq V]

open Classical in
/-- Number of negative incidences of `e` at `v`. -/
noncomputable def negInc (v : V) (e : E) : ℤ :=
  (if Γ.fst e = v then (if Γ.sfst e then 0 else 1) else 0) +
    (if Γ.snd e = v then (if Γ.ssnd e then 0 else 1) else 0)

/-- Number of negative incidences at `v`. -/
noncomputable def negCount (v : V) : ℤ := ∑ e, negInc Γ v e

/-- The expanded demand. -/
noncomputable def eb (b : V → ℤ) : V ⊕ E ⊕ E → ℕ :=
  Sum.elim (fun v => (b v + negCount Γ v).toNat)
    (Sum.elim (fun _ => 1) (fun e => if Γ.sfst e = Γ.ssnd e then 1 else 0))

open Classical in
lemma deg_inl (z : E × Fin 3 → ℝ) (v : V) :
    ∑ f ∈ univ.filter (fun f => eu Γ f = Sum.inl v ∨ ev Γ f = Sum.inl v), z f =
      ∑ e, ((if Γ.fst e = v then z (e, 0) else 0) + (if Γ.snd e = v then z (e, 2) else 0)) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.sum_univ_three]
  simp

open Classical in
lemma deg_a (z : E × Fin 3 → ℝ) (e : E) :
    ∑ f ∈ univ.filter (fun f => eu Γ f = Sum.inr (Sum.inl e) ∨ ev Γ f = Sum.inr (Sum.inl e)),
      z f = z (e, 0) + z (e, 1) + (if Γ.sfst e = Γ.ssnd e then 0 else z (e, 2)) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single e]
  · rw [Fin.sum_univ_three]
    by_cases h : Γ.sfst e = Γ.ssnd e <;> simp [h]
  · intro e' _ hne
    rw [Fin.sum_univ_three]
    by_cases h : Γ.sfst e' = Γ.ssnd e' <;> simp [h, hne]
  · simp

open Classical in
lemma deg_c (z : E × Fin 3 → ℝ) (e : E) :
    ∑ f ∈ univ.filter (fun f => eu Γ f = Sum.inr (Sum.inr e) ∨ ev Γ f = Sum.inr (Sum.inr e)),
      z f = z (e, 1) + (if Γ.sfst e = Γ.ssnd e then z (e, 2) else 0) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single e]
  · rw [Fin.sum_univ_three]
    by_cases h : Γ.sfst e = Γ.ssnd e <;> simp [h]
  · intro e' _ hne
    rw [Fin.sum_univ_three]
    by_cases h : Γ.sfst e' = Γ.ssnd e' <;> simp [h, hne]
  · simp

omit [Fintype E] in
lemma end_identity (w : E → ℝ) (v : V) (e : E) :
    (if Γ.fst e = v then val (Γ.sfst e) (w e) else 0) +
      (if Γ.snd e = v then val (Γ.ssnd e) (w e) else 0) =
      Γ.incidence v e * w e + (negInc Γ v e : ℝ) := by
  unfold SignedGraph.incidence negInc val SignedGraph.signVal
  cases Γ.sfst e <;> cases Γ.ssnd e <;> split_ifs <;> push_cast <;> ring

lemma deg_sum_eq (w : E → ℝ) (v : V) :
    ∑ e, ((if Γ.fst e = v then val (Γ.sfst e) (w e) else 0) +
      (if Γ.snd e = v then val (Γ.ssnd e) (w e) else 0)) = Γ.apply w v + negCount Γ v := by
  simp only [end_identity, Finset.sum_add_distrib, SignedGraph.apply, negCount]
  push_cast
  rfl

end Deg

end Expanded

section Blossom

variable {V E : Type*} [Fintype E] [DecidableEq V] (Γ : SignedGraph V E)

omit [Fintype E] [DecidableEq V] in
lemma reach_fst_snd (e : E) : Γ.underlying.Reachable (Γ.fst e) (Γ.snd e) := by
  by_cases h : Γ.fst e = Γ.snd e
  · rw [h]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨h, Or.inl ⟨e, rfl, rfl⟩⟩)

omit [Fintype E] [DecidableEq V] in
lemma mem_of_reachable (S : Finset V) (hS : ∀ e, Γ.fst e ∈ S ↔ Γ.snd e ∈ S) {v w : V}
    (h : Γ.underlying.Reachable v w) (hv : v ∈ S) : w ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hv
  | tail _ hadj ih =>
    rw [SignedGraph.underlying, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨_, ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩⟩ := hadj
    · rw [← h2, ← hS e, h1]; exact ih
    · rw [← h1, hS e, h2]; exact ih

omit [Fintype E] in
open Classical in
/-- A vertex set closed under the edges is a union of components, so its demand is even. -/
lemma even_of_closed [Fintype V] (b : V → ℤ)
    (hpar : ∀ v, Even (∑ w ∈ univ.filter (fun w => Γ.underlying.Reachable v w), b w))
    (S : Finset V) (hS : ∀ e, Γ.fst e ∈ S ↔ Γ.snd e ∈ S) : Even (∑ v ∈ S, b v) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    set C := univ.filter (fun w => Γ.underlying.Reachable v w) with hC
    have hCS : C ⊆ S := fun w hw => mem_of_reachable Γ S hS (mem_filter.1 hw).2 hv
    have hvC : v ∈ C := mem_filter.2 ⟨mem_univ _, SimpleGraph.Reachable.refl v⟩
    rw [← Finset.sum_sdiff hCS]
    refine Even.add (ih _ (Finset.sdiff_ssubset hCS ⟨v, hvC⟩) fun e => ?_) (hpar v)
    have hr := reach_fst_snd Γ e
    have : Γ.fst e ∈ C ↔ Γ.snd e ∈ C := by
      simp only [hC, mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩
    simp only [mem_sdiff, hS e, this]

omit [Fintype E] [DecidableEq V] in
/-- Contribution of the gadget of `e` to the left side of a blossom inequality. -/
noncomputable def G (x : E → ℝ) (U : Finset (V ⊕ E ⊕ E)) (J : Finset (E × Fin 3)) (e : E) : ℝ :=
  T (¬((Sum.inl (Γ.fst e) ∈ U) ↔ (Sum.inr (Sum.inl e) ∈ U))) ((e, 0) ∈ J)
      (val (Γ.sfst e) (x e)) +
    T (¬((Sum.inr (Sum.inl e) ∈ U) ↔ (Sum.inr (Sum.inr e) ∈ U))) ((e, 1) ∈ J)
      (mid (Γ.sfst e) (Γ.ssnd e) (x e)) +
    T (¬((if Γ.sfst e = Γ.ssnd e then Sum.inr (Sum.inr e) ∈ U else Sum.inr (Sum.inl e) ∈ U) ↔
      (Sum.inl (Γ.snd e) ∈ U))) ((e, 2) ∈ J) (val (Γ.ssnd e) (x e))

omit [Fintype E] [DecidableEq V] in
lemma G_nonneg (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (U : Finset (V ⊕ E ⊕ E))
    (J : Finset (E × Fin 3)) (e : E) : 0 ≤ G Γ x U J e := by
  have h1 := val_mem (Γ.sfst e) (hx e).1 (hx e).2
  have h2 := mid_mem (Γ.sfst e) (Γ.ssnd e) (hx e).1 (hx e).2
  have h3 := val_mem (Γ.ssnd e) (hx e).1 (hx e).2
  unfold G
  have := T_nonneg (¬((Sum.inl (Γ.fst e) ∈ U) ↔ (Sum.inr (Sum.inl e) ∈ U))) ((e, 0) ∈ J) h1.1 h1.2
  have := T_nonneg (¬((Sum.inr (Sum.inl e) ∈ U) ↔ (Sum.inr (Sum.inr e) ∈ U))) ((e, 1) ∈ J)
    h2.1 h2.2
  have := T_nonneg (¬((if Γ.sfst e = Γ.ssnd e then Sum.inr (Sum.inr e) ∈ U
    else Sum.inr (Sum.inl e) ∈ U) ↔ (Sum.inl (Γ.snd e) ∈ U))) ((e, 2) ∈ J) h3.1 h3.2
  linarith

open Classical in
lemma lhs_eq (x : E → ℝ) (U : Finset (V ⊕ E ⊕ E)) (J : Finset (E × Fin 3))
    (hJ : ∀ f ∈ J, (eu Γ f ∈ U) ≠ (ev Γ f ∈ U)) :
    ∑ f ∈ univ.filter (fun f => (eu Γ f ∈ U) ≠ (ev Γ f ∈ U) ∧ f ∉ J), ey Γ x f +
      ∑ f ∈ J, (1 - ey Γ x f) = ∑ e, G Γ x U J e := by
  have hJs : ∑ f ∈ J, (1 - ey Γ x f) = ∑ f, if f ∈ J then 1 - ey Γ x f else 0 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter]
  rw [hJs, Finset.sum_filter, ← Finset.sum_add_distrib]
  have hpt : ∀ f, ((if (eu Γ f ∈ U) ≠ (ev Γ f ∈ U) ∧ f ∉ J then ey Γ x f else 0) +
      if f ∈ J then 1 - ey Γ x f else 0) =
      T ((eu Γ f ∈ U) ≠ (ev Γ f ∈ U)) (f ∈ J) (ey Γ x f) := by
    intro f
    unfold T
    by_cases hf : f ∈ J
    · rw [ite_eq_right (fun h => h.2 hf), ite_eq_left hf, ite_eq_left (hJ f hf), ite_eq_left hf,
        zero_add]
    · rw [ite_eq_right hf, add_zero]
      by_cases hc : (eu Γ f ∈ U) ≠ (ev Γ f ∈ U)
      · rw [ite_eq_left ⟨hc, hf⟩, ite_eq_left hc, ite_eq_right hf]
      · rw [ite_eq_right (fun h => hc h.1), ite_eq_right hc]
  rw [Finset.sum_congr rfl fun f _ => hpt f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.sum_univ_three]
  unfold G
  by_cases h : Γ.sfst e = Γ.ssnd e <;> simp [h]

omit [Fintype E] [DecidableEq V] in
/-- Local blossom parity of the gadget of `e`. -/
noncomputable def pe (U : Finset (V ⊕ E ⊕ E)) (J : Finset (E × Fin 3)) (e : E) : ℤ :=
  ind ((Sum.inr (Sum.inl e) : V ⊕ E ⊕ E) ∈ U) +
    ind ((Sum.inr (Sum.inr e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.sfst e = Γ.ssnd e) +
    ind ((Sum.inl (Γ.fst e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.sfst e = false) +
    ind ((Sum.inl (Γ.snd e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.ssnd e = false) +
    ind ((e, 0) ∈ J) + ind ((e, 1) ∈ J) + ind ((e, 2) ∈ J)

open Classical in
lemma parity_decomp [Fintype V] (b : V → ℤ) (hnn : ∀ v, 0 ≤ b v + negCount Γ v)
    (U : Finset (V ⊕ E ⊕ E)) (J : Finset (E × Fin 3)) :
    ((∑ w ∈ U, eb Γ b w + J.card : ℕ) : ℤ) =
      ∑ v ∈ univ.filter (fun v => (Sum.inl v : V ⊕ E ⊕ E) ∈ U), b v + ∑ e, pe Γ U J e := by
  have hU : ∑ w ∈ U, (eb Γ b w : ℤ) = ∑ w, if w ∈ U then (eb Γ b w : ℤ) else 0 := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter]
  have hJ : (J.card : ℤ) = ∑ f, ind (f ∈ J) := by
    rw [← Finset.sum_subset (subset_univ J) (fun f _ hf => by simp [ind, hf]),
      Finset.sum_congr rfl (fun f hf => by simp [ind, hf] : ∀ f ∈ J, ind (f ∈ J) = 1)]
    simp
  have h1 : ∀ v, (if (Sum.inl v : V ⊕ E ⊕ E) ∈ U then ((eb Γ b (Sum.inl v) : ℕ) : ℤ) else 0) =
      (if (Sum.inl v : V ⊕ E ⊕ E) ∈ U then b v else 0) +
        ∑ e, (if (Sum.inl v : V ⊕ E ⊕ E) ∈ U then negInc Γ v e else 0) := by
    intro v
    split_ifs
    · simp only [eb, Sum.elim_inl, negCount]
      exact Int.toNat_of_nonneg (hnn v)
    · simp
  have h2 : ∀ e, ∑ v, (if (Sum.inl v : V ⊕ E ⊕ E) ∈ U then negInc Γ v e else 0) =
      ind ((Sum.inl (Γ.fst e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.sfst e = false) +
        ind ((Sum.inl (Γ.snd e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.ssnd e = false) := by
    intro e
    have : ∀ v, (if (Sum.inl v : V ⊕ E ⊕ E) ∈ U then negInc Γ v e else 0) =
        (if Γ.fst e = v then ind ((Sum.inl (Γ.fst e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.sfst e = false)
          else 0) +
        (if Γ.snd e = v then ind ((Sum.inl (Γ.snd e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.ssnd e = false)
          else 0) := by
      intro v
      unfold negInc ind
      by_cases h1 : Γ.fst e = v <;> by_cases h2 : Γ.snd e = v <;> cases hs : Γ.sfst e <;>
        cases ht : Γ.ssnd e <;> by_cases hu : (Sum.inl v : V ⊕ E ⊕ E) ∈ U <;>
        simp [h1, h2, hu]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, mem_univ, ite_true]
  have hA1 : ∑ v, (if (Sum.inl v : V ⊕ E ⊕ E) ∈ U then ((eb Γ b (Sum.inl v) : ℕ) : ℤ) else 0) =
      ∑ v ∈ univ.filter (fun v => (Sum.inl v : V ⊕ E ⊕ E) ∈ U), b v +
        ∑ e, (ind ((Sum.inl (Γ.fst e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.sfst e = false) +
          ind ((Sum.inl (Γ.snd e) : V ⊕ E ⊕ E) ∈ U ∧ Γ.ssnd e = false)) := by
    simp only [h1, Finset.sum_add_distrib, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [h2, Finset.sum_add_distrib]
  push_cast
  rw [hU, hJ, Fintype.sum_sum_type, Fintype.sum_sum_type, hA1, Fintype.sum_prod_type]
  simp only [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.sum_univ_three]
  unfold pe ind
  by_cases hA : (Sum.inr (Sum.inl e) : V ⊕ E ⊕ E) ∈ U <;>
    by_cases hC : (Sum.inr (Sum.inr e) : V ⊕ E ⊕ E) ∈ U <;>
    by_cases hs : Γ.sfst e = Γ.ssnd e <;> simp [eb, hA, hC, hs] <;> ring

open Classical in
lemma blossom [Fintype V] (b : V → ℤ)
    (hpar : ∀ v, Even (∑ w ∈ univ.filter (fun w => Γ.underlying.Reachable v w), b w))
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hslack : ∀ U : Finset V, (∀ v ∈ U, ∀ w ∈ U, Γ.underlying.Reachable v w) →
      (∃ v ∈ U, ∃ w ∉ U, Γ.underlying.Reachable v w) →
      1 ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (U : Set V) e), min (x e) (1 - x e))
    (hnn : ∀ v, 0 ≤ b v + negCount Γ v)
    (U : Finset (V ⊕ E ⊕ E)) (J : Finset (E × Fin 3))
    (hJ : ∀ f ∈ J, (eu Γ f ∈ U) ≠ (ev Γ f ∈ U))
    (hodd : Odd (∑ w ∈ U, eb Γ b w + J.card)) :
    1 ≤ ∑ f ∈ univ.filter (fun f => (eu Γ f ∈ U) ≠ (ev Γ f ∈ U) ∧ f ∉ J), ey Γ x f +
      ∑ f ∈ J, (1 - ey Γ x f) := by
  rw [lhs_eq Γ x U J hJ]
  have hG0 : ∀ e, 0 ≤ G Γ x U J e := fun e => G_nonneg Γ x hx U J e
  by_cases hA : ∃ e₀, ¬((Sum.inl (Γ.fst e₀) : V ⊕ E ⊕ E) ∈ U ↔
      (Sum.inl (Γ.snd e₀) : V ⊕ E ⊕ E) ∈ U)
  · obtain ⟨e₀, he₀⟩ := hA
    set W : Finset V := univ.filter (fun v => (Sum.inl v : V ⊕ E ⊕ E) ∈ U ∧
      Γ.underlying.Reachable (Γ.fst e₀) v) with hW
    have hW1 : ∀ v ∈ W, ∀ w ∈ W, Γ.underlying.Reachable v w := by
      intro v hv w hw
      simp only [hW, mem_filter, mem_univ, true_and] at hv hw
      exact hv.2.symm.trans hw.2
    have hW2 : ∃ v ∈ W, ∃ w ∉ W, Γ.underlying.Reachable v w := by
      by_cases hr : (Sum.inl (Γ.fst e₀) : V ⊕ E ⊕ E) ∈ U
      · refine ⟨Γ.fst e₀, ?_, Γ.snd e₀, ?_, reach_fst_snd Γ e₀⟩
        · simp only [hW, mem_filter, mem_univ, true_and]
          exact ⟨hr, SimpleGraph.Reachable.refl _⟩
        · simp only [hW, mem_filter, mem_univ, true_and, not_and]
          intro h
          exact absurd ⟨fun _ => h, fun _ => hr⟩ he₀
      · have hq : (Sum.inl (Γ.snd e₀) : V ⊕ E ⊕ E) ∈ U := by
          by_contra hq
          exact he₀ ⟨fun h => absurd h hr, fun h => absurd h hq⟩
        refine ⟨Γ.snd e₀, ?_, Γ.fst e₀, ?_, (reach_fst_snd Γ e₀).symm⟩
        · simp only [hW, mem_filter, mem_univ, true_and]
          exact ⟨hq, reach_fst_snd Γ e₀⟩
        · simp only [hW, mem_filter, mem_univ, true_and, not_and]
          intro h
          exact absurd h hr
    have hcross : ∀ e, Γ.crosses (W : Set V) e → ¬((Sum.inl (Γ.fst e) : V ⊕ E ⊕ E) ∈ U ↔
        (Sum.inl (Γ.snd e) : V ⊕ E ⊕ E) ∈ U) := by
      intro e he hiffU
      have hr := reach_fst_snd Γ e
      have hiff : Γ.underlying.Reachable (Γ.fst e₀) (Γ.fst e) ↔
          Γ.underlying.Reachable (Γ.fst e₀) (Γ.snd e) :=
        ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩
      simp only [SignedGraph.crosses, Finset.mem_coe, hW, mem_filter, mem_univ, true_and] at he
      apply he
      rw [hiff, hiffU]
    calc (1 : ℝ) ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (W : Set V) e), min (x e) (1 - x e) :=
          hslack W hW1 hW2
      _ ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (W : Set V) e), G Γ x U J e := by
          refine Finset.sum_le_sum fun e he => ?_
          unfold G
          exact gadget_cross_aux _ _ (hx e).1 (hx e).2 (min_le_left _ _) (min_le_right _ _)
            _ _ _ _ _ _ _ (hcross e (mem_filter.1 he).2)
      _ ≤ ∑ e, G Γ x U J e :=
          Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ => hG0 e
  · push Not at hA
    have heven := even_of_closed Γ b hpar (univ.filter fun v => (Sum.inl v : V ⊕ E ⊕ E) ∈ U)
      (fun e => by simp only [mem_filter, mem_univ, true_and]; exact hA e)
    have hodd' : Odd (∑ e, pe Γ U J e) := by
      have h1 : Odd (((∑ w ∈ U, eb Γ b w + J.card : ℕ) : ℤ)) := by exact_mod_cast hodd
      rw [parity_decomp Γ b hnn U J] at h1
      exact (Int.odd_add'.mp h1).mpr heven
    obtain ⟨e, he⟩ : ∃ e, Odd (pe Γ U J e) := by
      by_contra hne
      push Not at hne
      have : Even (∑ e, pe Γ U J e) :=
        Finset.even_sum _ fun e _ => Int.not_odd_iff_even.mp (hne e)
      exact (Int.not_even_iff_odd.mpr hodd') this
    refine le_trans ?_ (Finset.single_le_sum (fun e _ => hG0 e) (mem_univ e))
    have hQ : ((Sum.inl (Γ.snd e) : V ⊕ E ⊕ E) ∈ U) = ((Sum.inl (Γ.fst e) : V ⊕ E ⊕ E) ∈ U) :=
      propext (hA e).symm
    unfold G
    unfold pe at he
    rw [hQ] at he ⊢
    refine gadget_odd _ _ (hx e).1 (hx e).2 _ _ _ _ _ _ ?_ ?_ ?_ he
    · intro h
      simpa using hJ _ h
    · intro h
      simpa using hJ _ h
    · intro h
      rw [← hQ]
      by_cases hs : Γ.sfst e = Γ.ssnd e <;> simpa [hs] using hJ _ h

open Classical in
theorem main_aux [Fintype V] (b : V → ℤ)
    (hpar : ∀ v, Even (∑ w ∈ univ.filter (fun w => Γ.underlying.Reachable v w), b w))
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hBx : ∀ v, Γ.apply x v = b v)
    (hslack : ∀ U : Finset V, (∀ v ∈ U, ∀ w ∈ U, Γ.underlying.Reachable v w) →
      (∃ v ∈ U, ∃ w ∉ U, Γ.underlying.Reachable v w) →
      1 ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (U : Set V) e), min (x e) (1 - x e)) :
    x ∈ convexHull ℝ (Γ.integralSolutions fun v => (b v : ℝ)) := by
  have hnn : ∀ v, 0 ≤ b v + negCount Γ v := by
    intro v
    have h := deg_sum_eq Γ x v
    rw [hBx v] at h
    have h0 : (0 : ℝ) ≤ ∑ e, ((if Γ.fst e = v then val (Γ.sfst e) (x e) else 0) +
        (if Γ.snd e = v then val (Γ.ssnd e) (x e) else 0)) := by
      refine Finset.sum_nonneg fun e _ => add_nonneg ?_ ?_ <;> split_ifs <;>
        first | exact le_refl 0 | exact (val_mem _ (hx e).1 (hx e).2).1
    rw [h] at h0
    exact_mod_cast h0
  have heb : ∀ v, ((eb Γ b (Sum.inl v) : ℕ) : ℝ) = (b v : ℝ) + (negCount Γ v : ℝ) := by
    intro v
    have : ((eb Γ b (Sum.inl v) : ℕ) : ℤ) = b v + negCount Γ v := by
      simp only [eb, Sum.elim_inl]
      exact Int.toNat_of_nonneg (hnn v)
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) this
  have hea : ∀ e, ((eb Γ b (Sum.inr (Sum.inl e)) : ℕ) : ℝ) = 1 := by
    intro e
    simp [eb]
  have hec : ∀ e, ((eb Γ b (Sum.inr (Sum.inr e)) : ℕ) : ℝ) =
      if Γ.sfst e = Γ.ssnd e then 1 else 0 := by
    intro e
    simp only [eb, Sum.elim_inr]
    split_ifs <;> simp
  have hdeg : ∀ w, ∑ f ∈ univ.filter (fun f => eu Γ f = w ∨ ev Γ f = w), ey Γ x f =
      (eb Γ b w : ℝ) := by
    rintro (v | e | e)
    · rw [deg_inl, heb]
      simp only [ey_zero, ey_two]
      rw [deg_sum_eq, hBx]
    · rw [deg_a, hea]
      simp only [ey_zero, ey_one, ey_two]
      unfold mid val
      cases hs : Γ.sfst e <;> cases ht : Γ.ssnd e <;> simp
    · rw [deg_c, hec]
      simp only [ey_one, ey_two]
      unfold mid val
      cases hs : Γ.sfst e <;> cases ht : Γ.ssnd e <;> simp
  have hy := bmatching_polytope (eu Γ) (ev Γ) (eu_ne_ev Γ) (eb Γ b) (ey Γ x) (ey_mem Γ x hx)
    hdeg (fun U J hJ hodd => by convert blossom Γ b hpar x hx hslack hnn U J hJ hodd)
  have hmap : LinearMap.funLeft ℝ ℝ (fun e => (e, idx Γ e)) (ey Γ x) = x := by
    funext e
    rw [LinearMap.funLeft_apply]
    exact ey_idx Γ x e
  have h1 := Set.mem_image_of_mem (LinearMap.funLeft ℝ ℝ (fun e : E => (e, idx Γ e))) hy
  rw [LinearMap.image_convexHull, hmap] at h1
  refine convexHull_mono ?_ h1
  rintro _ ⟨z, ⟨hz01, hzdeg⟩, rfl⟩
  have hfz : LinearMap.funLeft ℝ ℝ (fun e : E => (e, idx Γ e)) z = fun e => z (e, idx Γ e) := by
    funext e
    rw [LinearMap.funLeft_apply]
  rw [hfz]
  refine ⟨fun e => hz01 _, fun v => ?_⟩
  have hrel : ∀ e, z (e, 0) = val (Γ.sfst e) (z (e, idx Γ e)) ∧
      z (e, 2) = val (Γ.ssnd e) (z (e, idx Γ e)) := by
    intro e
    refine aux_relations Γ z e ?_ ?_
    · have := hzdeg (Sum.inr (Sum.inl e))
      rwa [deg_a, hea] at this
    · have := hzdeg (Sum.inr (Sum.inr e))
      rwa [deg_c, hec] at this
  have hrel0 : ∀ e, val (Γ.sfst e) (z (e, idx Γ e)) = z (e, 0) := fun e => (hrel e).1.symm
  have hrel2 : ∀ e, val (Γ.ssnd e) (z (e, idx Γ e)) = z (e, 2) := fun e => (hrel e).2.symm
  have hv := hzdeg (Sum.inl v)
  rw [deg_inl, heb] at hv
  have h2 := deg_sum_eq Γ (fun e => z (e, idx Γ e)) v
  simp only [hrel0, hrel2] at h2
  linarith

end Blossom

end SignedIntegrality


open Classical in
/-- **Lemma 4.1 (Robust signed integrality).** Let `B` be a signed incidence matrix and
`b ∈ ℤ^V` with `∑_{v ∈ K} b_v` even on every connected component `K` of the underlying graph.
If `Bx = b`, `x ∈ [0,1]^E`, and within every component every nonempty proper vertex set `U`
has `∑_{e ∈ δ(U)} min {x_e, 1 - x_e} ≥ 1`, then `x ∈ conv {z ∈ {0,1}^E : Bz = b}`. -/
theorem robust_signed_integrality {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (Γ : SignedGraph V E) (b : V → ℤ)
    (hpar : ∀ v, Even (∑ w ∈ univ.filter (fun w => Γ.underlying.Reachable v w), b w))
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hBx : ∀ v, Γ.apply x v = b v)
    (hslack : ∀ U : Finset V, (∀ v ∈ U, ∀ w ∈ U, Γ.underlying.Reachable v w) →
      (∃ v ∈ U, ∃ w ∉ U, Γ.underlying.Reachable v w) →
      1 ≤ ∑ e ∈ univ.filter (fun e => Γ.crosses (U : Set V) e), min (x e) (1 - x e)) :
    x ∈ convexHull ℝ (Γ.integralSolutions fun v => (b v : ℝ)) :=
  SignedIntegrality.main_aux Γ b hpar x hx hBx hslack

end Lovasz
