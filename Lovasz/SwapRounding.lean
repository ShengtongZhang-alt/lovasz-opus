/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 4.2: signed swap rounding

DAG node `L4.2` of `docs/BLUEPRINT.md`, and the mean-preservation property of line processes
(node `L4.2m`).

The combinatorial core is `SwapRounding.exists_small_balanced`: a nonempty edge set of a signed
graph whose signed incidence sums vanish at every vertex contains a nonempty such subset with at
most four edges at every vertex. It is obtained from an alternating closed trail whose states
(vertex, sign) are distinct, found by extending an alternating trail until its free state repeats.
-/

namespace Lovasz

open Finset

namespace SwapRounding

theorem expect_mix {α : Type*} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (μ₁ μ₂ : FinDist α)
    (h₁ : ∀ a ∉ μ₁.support, μ₁.prob a = 0) (h₂ : ∀ a ∉ μ₂.support, μ₂.prob a = 0)
    (f : α → ℝ) :
    (FinDist.mix p hp μ₁ μ₂ h₁ h₂).expect f = p * μ₁.expect f + (1 - p) * μ₂.expect f := by
  classical
  have hs₁ : μ₁.support ⊆ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support := Finset.subset_union_left
  have hs₂ : μ₂.support ⊆ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support := Finset.subset_union_right
  have e₁ : ∑ a ∈ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support, μ₁.prob a * f a = μ₁.expect f :=
    (Finset.sum_subset hs₁ fun a _ ha => by rw [h₁ a ha, zero_mul]).symm
  have e₂ : ∑ a ∈ (FinDist.mix p hp μ₁ μ₂ h₁ h₂).support, μ₂.prob a * f a = μ₂.expect f :=
    (Finset.sum_subset hs₂ fun a _ ha => by rw [h₂ a ha, zero_mul]).symm
  rw [← e₁, ← e₂, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  unfold FinDist.expect
  refine Finset.sum_congr rfl fun a _ => ?_
  show (p * μ₁.prob a + (1 - p) * μ₂.prob a) * f a = _
  ring

theorem isExact_aux {ι : Type*} {ok : (ι → ℝ) → Prop} {x : ι → ℝ} {μ : FinDist (ι → ℝ)}
    (h : LineProcess ok x μ) : μ.IsExact := by
  cases h with
  | stop x hx =>
    intro a ha
    simp only [FinDist.dirac, Finset.mem_singleton] at ha ⊢
    exact ite_eq_right ha
  | move x h α β μ₁ μ₂ hα hβ h₁ h₂ _ _ _ _ =>
    intro a ha
    simp only [FinDist.mix, Finset.mem_union, not_or] at ha ⊢
    rw [h₁ a ha.1, h₂ a ha.2]
    ring

end SwapRounding

/-- **Mean preservation.** The terminal distribution of a line process has mean equal to its
starting point, and is supported in `[0,1]^ι`. -/
theorem LineProcess.expect_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {ok : (ι → ℝ) → Prop}
    {x : ι → ℝ} {μ : FinDist (ι → ℝ)} (h : LineProcess ok x μ) (i : ι) :
    μ.expect (fun z => z i) = x i := by
  induction h with
  | stop x hx => simp [FinDist.expect, FinDist.dirac]
  | move x h α β μ₁ μ₂ hα hβ h₁ h₂ hx hok _ _ ih₁ ih₂ =>
    refine (SwapRounding.expect_mix (β / (α + β)) ⟨div_nonneg hβ.le (add_pos hα hβ).le,
      (div_le_one (add_pos hα hβ)).2 (le_add_of_nonneg_left hα.le)⟩ μ₁ μ₂ h₁ h₂
      (fun z => z i)).trans ?_
    rw [ih₁, ih₂]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- The terminal distribution of a line process has exact support. -/
theorem LineProcess.isExact {ι : Type*} [DecidableEq ι] {ok : (ι → ℝ) → Prop}
    {x : ι → ℝ} {μ : FinDist (ι → ℝ)} (h : LineProcess ok x μ) : μ.IsExact :=
  SwapRounding.isExact_aux h

namespace SwapRounding

open SignedGraph

/-! ### Alternating trails in a signed graph -/

section Trails

variable {V E : Type*} (Γ : SignedGraph V E)

theorem signVal_not (s : Bool) : signVal (!s) = -signVal s := by
  cases s <;> simp [signVal]

theorem signVal_mul_self (s : Bool) : signVal s * signVal s = 1 := by
  cases s <;> simp [signVal]

/-- The signed weight of a state `(vertex, sign)` at the vertex `v`. -/
noncomputable def stW [DecidableEq V] (v : V) (w : V × Bool) : ℝ :=
  if w.1 = v then signVal w.2 else 0

theorem incidence_eq [DecidableEq V] (v : V) (e : E) :
    Γ.incidence v e = (if Γ.fst e = v then signVal (Γ.sfst e) else 0) +
      (if Γ.snd e = v then signVal (Γ.ssnd e) else 0) := by
  unfold SignedGraph.incidence
  by_cases h1 : Γ.fst e = v <;> by_cases h2 : Γ.snd e = v <;> simp [h1, h2]

/-- The incidence of an edge at `v`, read off from either of its twin arcs. -/
theorem incidence_eq_arc [DecidableEq V] (v : V) (c : E × Bool) :
    Γ.incidence v c.1 = stW v (Γ.twinTail c) - stW v (Γ.twinHead c) := by
  rw [incidence_eq]
  rcases c with ⟨e, _ | _⟩ <;>
  · simp only [SignedGraph.twinTail, SignedGraph.twinHead, stW, signVal_not]
    by_cases h1 : Γ.fst e = v <;> by_cases h2 : Γ.snd e = v <;> simp [h1, h2] <;> ring

theorem arc_vertex (a : E × Bool) (v : V) :
    ((Γ.twinTail a).1 = v ∨ (Γ.twinHead a).1 = v) ↔ (Γ.fst a.1 = v ∨ Γ.snd a.1 = v) := by
  rcases a with ⟨e, _ | _⟩ <;> simp [SignedGraph.twinTail, SignedGraph.twinHead, or_comm]

/-- The head of the last arc of the list `c :: L`. -/
def lastHead : E × Bool → List (E × Bool) → V × Bool
  | c, [] => Γ.twinHead c
  | _, d :: L => lastHead d L

theorem lastHead_mem (c : E × Bool) (L : List (E × Bool)) :
    lastHead Γ c L ∈ (c :: L).map Γ.twinHead := by
  induction L generalizing c with
  | nil => simp [lastHead]
  | cons d L ih =>
    simp only [lastHead]
    exact List.mem_cons_of_mem _ (ih d)

theorem sum_incidence_trail [DecidableEq V] (v : V) (c : E × Bool) (L : List (E × Bool))
    (hc : List.IsChain (fun a b => Γ.twinHead a = Γ.twinTail b) (c :: L)) :
    ((c :: L).map fun a => Γ.incidence v a.1).sum =
      stW v (Γ.twinTail c) - stW v (lastHead Γ c L) := by
  induction L generalizing c with
  | nil => simp [lastHead, incidence_eq_arc]
  | cons d L ih =>
    rw [List.isChain_cons_cons] at hc
    rw [List.map_cons, List.sum_cons, ih d hc.2, incidence_eq_arc, hc.1]
    simp only [lastHead]
    ring

theorem map_heads (c : E × Bool) (L : List (E × Bool))
    (hc : List.IsChain (fun a b => Γ.twinHead a = Γ.twinTail b) (c :: L)) :
    Γ.twinTail c :: (c :: L).map Γ.twinHead = (c :: L).map Γ.twinTail ++ [lastHead Γ c L] := by
  induction L generalizing c with
  | nil => simp [lastHead]
  | cons d L ih =>
    rw [List.isChain_cons_cons] at hc
    have h := ih d hc.2
    simp only [List.map_cons, lastHead] at h ⊢
    rw [hc.1, h]
    simp

/-- An alternating trail with distinct edges from `D` and distinct head states. -/
structure IsTrail (D : Finset E) (L : List (E × Bool)) : Prop where
  chain : List.IsChain (fun a b => Γ.twinHead a = Γ.twinTail b) L
  nodup_edges : (L.map Prod.fst).Nodup
  mem : ∀ a ∈ L, a.1 ∈ D
  nodup_heads : (L.map Γ.twinHead).Nodup

theorem IsTrail.prefix {Γ : SignedGraph V E} {D : Finset E} {L L' : List (E × Bool)}
    (h : IsTrail Γ D L) (hp : L' <+: L) : IsTrail Γ D L' :=
  ⟨h.chain.prefix hp, h.nodup_edges.sublist (hp.sublist.map _),
    fun a ha => h.mem a (hp.sublist.subset ha), h.nodup_heads.sublist (hp.sublist.map _)⟩

theorem exists_prefix (s : V × Bool) (c : E × Bool) (L : List (E × Bool))
    (h : s ∈ (c :: L).map Γ.twinHead) : ∃ L', L' <+: L ∧ lastHead Γ c L' = s := by
  induction L generalizing c with
  | nil =>
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact ⟨[], List.nil_prefix, by simp [lastHead, h]⟩
  | cons d L ih =>
    by_cases hc : Γ.twinHead c = s
    · exact ⟨[], List.nil_prefix, by simp [lastHead, hc]⟩
    · rw [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm hc
      obtain ⟨L', hL', hl⟩ := ih d h
      exact ⟨d :: L', (List.prefix_cons_inj d).2 hL', by simp [lastHead, hl]⟩

theorem length_filter_le_two [DecidableEq V] (v : V) (l : List (V × Bool)) (hl : l.Nodup) :
    (l.filter fun w => decide (w.1 = v)).length ≤ 2 := by
  have hnd := hl.filter (fun w => decide (w.1 = v))
  rw [← List.toFinset_card_of_nodup hnd]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_le_two (a := (v, true)) (b := (v, false)))
  intro w hw
  rw [List.mem_toFinset, List.mem_filter] at hw
  obtain ⟨-, hw⟩ := hw
  rcases w with ⟨u, s⟩
  simp only [decide_eq_true_eq] at hw
  subst hw
  cases s <;> simp

/-- A closed alternating trail with distinct states yields a balanced edge set with at most four
edges at every vertex. -/
theorem good_of_closed [DecidableEq V] [DecidableEq E] {D : Finset E} {c : E × Bool}
    {L : List (E × Bool)} (hT : IsTrail Γ D (c :: L)) (hcl : lastHead Γ c L = Γ.twinTail c) :
    ∃ F ⊆ D, F.Nonempty ∧ (∀ v, ∑ e ∈ F, Γ.incidence v e = 0) ∧
      ∀ v, (F.filter fun e => Γ.fst e = v ∨ Γ.snd e = v).card ≤ 4 := by
  refine ⟨((c :: L).map Prod.fst).toFinset, ?_, ⟨c.1, by simp⟩, ?_, ?_⟩
  · intro e he
    rw [List.mem_toFinset, List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact hT.mem a ha
  · intro v
    rw [List.sum_toFinset _ hT.nodup_edges, List.map_map]
    have h := sum_incidence_trail Γ v c L hT.chain
    rw [hcl, sub_self] at h
    exact h
  · intro v
    have hperm : ((c :: L).map Γ.twinHead).Perm ((c :: L).map Γ.twinTail) := by
      have h := map_heads Γ c L hT.chain
      rw [hcl] at h
      have h2 : (Γ.twinTail c :: (c :: L).map Γ.twinHead).Perm
          (Γ.twinTail c :: (c :: L).map Γ.twinTail) := by
        rw [h]
        exact List.perm_append_singleton _ _
      exact h2.cons_inv
    have htails : ((c :: L).map Γ.twinTail).Nodup := hperm.nodup_iff.1 hT.nodup_heads
    have hA : ((((c :: L).filter fun a => decide ((Γ.twinTail a).1 = v)).map
        Prod.fst).toFinset).card ≤ 2 := by
      refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      have := length_filter_le_two v _ htails
      rwa [List.filter_map, List.length_map] at this
    have hB : ((((c :: L).filter fun a => decide ((Γ.twinHead a).1 = v)).map
        Prod.fst).toFinset).card ≤ 2 := by
      refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      have := length_filter_le_two v _ hT.nodup_heads
      rwa [List.filter_map, List.length_map] at this
    refine le_trans (Finset.card_le_card ?_) ((Finset.card_union_le _ _).trans
      (Nat.add_le_add hA hB))
    intro e he
    rw [Finset.mem_filter, List.mem_toFinset, List.mem_map] at he
    obtain ⟨⟨a, ha, rfl⟩, hv⟩ := he
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
    rcases (arc_vertex Γ a v).2 hv with k | k
    · exact Or.inl (List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, by simpa using k⟩, rfl⟩)
    · exact Or.inr (List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, by simpa using k⟩, rfl⟩)

theorem sign_neg_aux [DecidableEq V] (v : V) (σ : Bool) (w : V × Bool) (hw : w ≠ (v, σ)) :
    signVal σ * (stW v w - stW v (v, σ)) < 0 := by
  rcases w with ⟨u, τ⟩
  have hv : stW v (v, σ) = signVal σ := by simp [stW]
  rw [hv]
  unfold stW
  split_ifs with h
  · simp only at h
    subst h
    have hτ : τ = !σ := by
      cases τ <;> cases σ <;> simp_all
    subst hτ
    cases σ <;> norm_num [signVal]
  · cases σ <;> norm_num [signVal]

theorem end_of_neg [DecidableEq V] (v : V) (σ : Bool) (e : E) (h : signVal σ * Γ.incidence v e < 0) :
    ∃ c' : E × Bool, c'.1 = e ∧ Γ.twinHead c' = (v, σ) := by
  by_cases h1 : Γ.fst e = v ∧ Γ.sfst e = !σ
  · exact ⟨(e, true), rfl, by simp [SignedGraph.twinHead, h1.1, h1.2]⟩
  by_cases h2 : Γ.snd e = v ∧ Γ.ssnd e = !σ
  · exact ⟨(e, false), rfl, by simp [SignedGraph.twinHead, h2.1, h2.2]⟩
  exfalso
  rw [incidence_eq, mul_add] at h
  have hA : 0 ≤ signVal σ * (if Γ.fst e = v then signVal (Γ.sfst e) else 0) := by
    split_ifs with hf
    · have hs : Γ.sfst e ≠ !σ := fun h' => h1 ⟨hf, h'⟩
      revert hs
      cases Γ.sfst e <;> cases σ <;> simp [signVal]
    · simp
  have hB : 0 ≤ signVal σ * (if Γ.snd e = v then signVal (Γ.ssnd e) else 0) := by
    split_ifs with hf
    · have hs : Γ.ssnd e ≠ !σ := fun h' => h2 ⟨hf, h'⟩
      revert hs
      cases Γ.ssnd e <;> cases σ <;> simp [signVal]
    · simp
  linarith

/-- If the free state of a trail is new, the trail can be extended backwards along an unused edge
of `D`. -/
theorem exists_ext [DecidableEq V] [DecidableEq E] {D : Finset E}
    (hbal : ∀ v, ∑ e ∈ D, Γ.incidence v e = 0) {c : E × Bool} {L : List (E × Bool)}
    (hT : IsTrail Γ D (c :: L)) (hs : Γ.twinTail c ∉ (c :: L).map Γ.twinHead) :
    ∃ c' : E × Bool, Γ.twinHead c' = Γ.twinTail c ∧ c'.1 ∈ D ∧
      c'.1 ∉ (c :: L).map Prod.fst := by
  rcases hts : Γ.twinTail c with ⟨v, σ⟩
  rw [hts] at hs
  have hUD : ((c :: L).map Prod.fst).toFinset ⊆ D := by
    intro e he
    rw [List.mem_toFinset, List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact hT.mem a ha
  have hsumU : ∑ e ∈ ((c :: L).map Prod.fst).toFinset, Γ.incidence v e =
      stW v (v, σ) - stW v (lastHead Γ c L) := by
    rw [List.sum_toFinset _ hT.nodup_edges, List.map_map, ← hts]
    exact sum_incidence_trail Γ v c L hT.chain
  have hsplit : ∑ e ∈ D \ ((c :: L).map Prod.fst).toFinset, Γ.incidence v e +
      ∑ e ∈ ((c :: L).map Prod.fst).toFinset, Γ.incidence v e = ∑ e ∈ D, Γ.incidence v e :=
    Finset.sum_sdiff hUD
  rw [hbal v, hsumU] at hsplit
  have hlast_ne : lastHead Γ c L ≠ (v, σ) := fun h => hs (h ▸ lastHead_mem Γ c L)
  have hneg : ∑ e ∈ D \ ((c :: L).map Prod.fst).toFinset, signVal σ * Γ.incidence v e <
      ∑ e ∈ D \ ((c :: L).map Prod.fst).toFinset, (0 : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_const_zero]
    have : ∑ e ∈ D \ ((c :: L).map Prod.fst).toFinset, Γ.incidence v e =
        stW v (lastHead Γ c L) - stW v (v, σ) := by linarith
    rw [this]
    exact sign_neg_aux v σ _ hlast_ne
  obtain ⟨e, he, hlt⟩ := Finset.exists_lt_of_sum_lt hneg
  rw [Finset.mem_sdiff, List.mem_toFinset] at he
  obtain ⟨c', hc'e, hc'h⟩ := end_of_neg Γ v σ e hlt
  exact ⟨c', hc'h, hc'e ▸ he.1, hc'e ▸ he.2⟩

theorem exists_closed_aux [DecidableEq V] [DecidableEq E] {D : Finset E}
    (hbal : ∀ v, ∑ e ∈ D, Γ.incidence v e = 0) (n : ℕ) :
    ∀ (c : E × Bool) (L : List (E × Bool)), IsTrail Γ D (c :: L) → D.card - L.length = n →
      ∃ F ⊆ D, F.Nonempty ∧ (∀ v, ∑ e ∈ F, Γ.incidence v e = 0) ∧
        ∀ v, (F.filter fun e => Γ.fst e = v ∨ Γ.snd e = v).card ≤ 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c L hT hn
  by_cases hs : Γ.twinTail c ∈ (c :: L).map Γ.twinHead
  · obtain ⟨L', hL', hlast⟩ := exists_prefix Γ _ c L hs
    exact good_of_closed Γ (hT.prefix ((List.prefix_cons_inj c).2 hL')) hlast
  · obtain ⟨c', hc'h, hc'D, hc'U⟩ := exists_ext Γ hbal hT hs
    have hT' : IsTrail Γ D (c' :: c :: L) := by
      refine ⟨List.IsChain.cons_cons hc'h hT.chain, ?_, ?_, ?_⟩
      · rw [List.map_cons]
        exact List.nodup_cons.2 ⟨hc'U, hT.nodup_edges⟩
      · intro a ha
        rw [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hc'D
        · exact hT.mem a ha
      · rw [List.map_cons]
        exact List.nodup_cons.2 ⟨hc'h ▸ hs, hT.nodup_heads⟩
    have hlen : (c' :: c :: L).length ≤ D.card := by
      rw [← List.length_map Prod.fst, ← List.toFinset_card_of_nodup hT'.nodup_edges]
      refine Finset.card_le_card fun e he => ?_
      rw [List.mem_toFinset, List.mem_map] at he
      obtain ⟨a, ha, rfl⟩ := he
      exact hT'.mem a ha
    simp only [List.length_cons] at hlen
    exact ih _ (by simp only [List.length_cons]; omega) c' (c :: L) hT' rfl

/-- **Small balanced subsets.** A nonempty edge set whose signed incidence sums vanish at every
vertex contains a nonempty subset with the same property and at most four edges at every
vertex. -/
theorem exists_small_balanced [DecidableEq V] [DecidableEq E] (D : Finset E) (hD : D.Nonempty)
    (hbal : ∀ v, ∑ e ∈ D, Γ.incidence v e = 0) :
    ∃ F ⊆ D, F.Nonempty ∧ (∀ v, ∑ e ∈ F, Γ.incidence v e = 0) ∧
      ∀ v, (F.filter fun e => Γ.fst e = v ∨ Γ.snd e = v).card ≤ 4 := by
  obtain ⟨e, he⟩ := hD
  refine exists_closed_aux Γ hbal _ (e, false) [] ⟨List.isChain_singleton _, by simp, ?_, by simp⟩
    rfl
  intro a ha
  rw [List.mem_singleton] at ha
  subst ha
  exact he

end Trails

/-! ### One swap step -/

section Swap

variable {V E : Type*} (Γ : SignedGraph V E)

/-- Flip both signs of every edge on which `z₂ < z₁`. -/
noncomputable def flip (z₁ z₂ : E → ℝ) : SignedGraph V E where
  fst := Γ.fst
  snd := Γ.snd
  sfst e := if z₂ e < z₁ e then !Γ.sfst e else Γ.sfst e
  ssnd e := if z₂ e < z₁ e then !Γ.ssnd e else Γ.ssnd e

theorem flip_incidence (z₁ z₂ : E → ℝ) (v : V) (e : E) :
    (flip Γ z₁ z₂).incidence v e = (if z₂ e < z₁ e then -1 else 1) * Γ.incidence v e := by
  have key : ∀ s : Bool, signVal (if z₂ e < z₁ e then !s else s) =
      (if z₂ e < z₁ e then -1 else 1) * signVal s := by
    intro s
    by_cases h0 : z₂ e < z₁ e <;> simp [h0, signVal_not]
  simp only [SignedGraph.incidence, flip, key]
  by_cases h1 : Γ.fst e = v <;> by_cases h2 : Γ.snd e = v <;> simp [h1, h2, mul_add]

theorem apply_add [Fintype E] (x y : E → ℝ) (v : V) :
    Γ.apply (x + y) v = Γ.apply x v + Γ.apply y v := by
  simp only [SignedGraph.apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem apply_sub [Fintype E] (x y : E → ℝ) (v : V) :
    Γ.apply (x - y) v = Γ.apply x v - Γ.apply y v := by
  simp only [SignedGraph.apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

open Classical in
/-- The number of coordinates where two vectors differ. -/
noncomputable def hdist [Fintype E] (z₁ z₂ : E → ℝ) : ℕ :=
  (univ.filter fun e => z₁ e ≠ z₂ e).card

open Classical in
/-- **One swap step.** Two distinct integral solutions can be moved towards each other along a
common direction with at most four nonzero entries at every vertex. -/
theorem exists_delta [Fintype E] [DecidableEq V] [DecidableEq E] (b : V → ℝ) {z₁ z₂ : E → ℝ}
    (h₁ : z₁ ∈ Γ.integralSolutions b) (h₂ : z₂ ∈ Γ.integralSolutions b) (hne : z₁ ≠ z₂) :
    ∃ δ : E → ℝ, (∀ v, (univ.filter fun e =>
        δ e ≠ 0 ∧ (Γ.fst e = v ∨ Γ.snd e = v)).card ≤ 4) ∧
      z₁ + δ ∈ Γ.integralSolutions b ∧ z₂ - δ ∈ Γ.integralSolutions b ∧
      hdist (z₁ + δ) z₂ < hdist z₁ z₂ ∧ hdist z₁ (z₂ - δ) < hdist z₁ z₂ := by
  obtain ⟨hb₁, ha₁⟩ := h₁
  obtain ⟨hb₂, ha₂⟩ := h₂
  have hD : ∀ e, e ∈ (univ.filter fun e => z₁ e ≠ z₂ e) ↔ z₁ e ≠ z₂ e := by simp
  have hDne : (univ.filter fun e => z₁ e ≠ z₂ e).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    refine hne (funext fun e => ?_)
    by_contra he
    have := (hD e).2 he
    rw [h] at this
    exact Finset.notMem_empty e this
  have hcoef : ∀ e, z₁ e ≠ z₂ e → (if z₂ e < z₁ e then (-1 : ℝ) else 1) = z₂ e - z₁ e := by
    intro e he
    rcases hb₁ e with h1 | h1 <;> rcases hb₂ e with h2 | h2 <;> rw [h1, h2] at he ⊢ <;>
      first | exact absurd rfl he | norm_num
  have hbal : ∀ v, ∑ e ∈ (univ.filter fun e => z₁ e ≠ z₂ e), (flip Γ z₁ z₂).incidence v e = 0 := by
    intro v
    have h1 : ∑ e ∈ (univ.filter fun e => z₁ e ≠ z₂ e), (flip Γ z₁ z₂).incidence v e =
        ∑ e ∈ (univ.filter fun e => z₁ e ≠ z₂ e), Γ.incidence v e * (z₂ e - z₁ e) := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [flip_incidence, hcoef e ((hD e).1 he), mul_comm]
    have h2 : ∑ e ∈ (univ.filter fun e => z₁ e ≠ z₂ e), Γ.incidence v e * (z₂ e - z₁ e) =
        ∑ e, Γ.incidence v e * (z₂ e - z₁ e) := by
      refine Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_
      have : z₁ e = z₂ e := by
        by_contra h
        exact he ((hD e).2 h)
      rw [this, sub_self, mul_zero]
    rw [h1, h2]
    have h3 : ∑ e, Γ.incidence v e * (z₂ e - z₁ e) = Γ.apply z₂ v - Γ.apply z₁ v :=
      apply_sub Γ z₂ z₁ v
    rw [h3, ha₁ v, ha₂ v, sub_self]
  obtain ⟨F, hFD, hFne, hFbal, hFdeg⟩ := exists_small_balanced (flip Γ z₁ z₂) _ hDne hbal
  have hFdeg' : ∀ v, (F.filter fun e => Γ.fst e = v ∨ Γ.snd e = v).card ≤ 4 := hFdeg
  have hFne' : ∀ e ∈ F, z₁ e ≠ z₂ e := fun e he => (hD e).1 (hFD he)
  let δ : E → ℝ := fun e => if e ∈ F then z₂ e - z₁ e else 0
  have hδ : ∀ e, δ e = if e ∈ F then z₂ e - z₁ e else 0 := fun e => rfl
  have hδapply : ∀ v, Γ.apply δ v = 0 := by
    intro v
    have h1 : ∑ e, Γ.incidence v e * δ e = ∑ e ∈ F, Γ.incidence v e * δ e :=
      (Finset.sum_subset (Finset.subset_univ F) fun e _ he => by rw [hδ, ite_eq_right he, mul_zero]).symm
    rw [SignedGraph.apply, h1, ← hFbal v]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [flip_incidence, hcoef e (hFne' e he), hδ, ite_eq_left he, mul_comm]
  have hadd : ∀ e, (z₁ + δ) e = if e ∈ F then z₂ e else z₁ e := by
    intro e
    rw [Pi.add_apply, hδ]
    split_ifs <;> ring
  have hsub : ∀ e, (z₂ - δ) e = if e ∈ F then z₁ e else z₂ e := by
    intro e
    rw [Pi.sub_apply, hδ]
    split_ifs <;> ring
  obtain ⟨e₀, he₀⟩ := hFne
  refine ⟨δ, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro v
    refine le_trans (Finset.card_le_card fun e he => ?_) (hFdeg' v)
    rw [Finset.mem_filter] at he ⊢
    refine ⟨?_, he.2.2⟩
    by_contra hF
    exact he.2.1 (by rw [hδ, ite_eq_right hF])
  · intro e
    rw [hadd]
    split_ifs
    exacts [hb₂ e, hb₁ e]
  · intro v
    rw [apply_add, ha₁ v, hδapply v, add_zero]
  · intro e
    rw [hsub]
    split_ifs
    exacts [hb₁ e, hb₂ e]
  · intro v
    rw [apply_sub, ha₂ v, hδapply v, sub_zero]
  · unfold hdist
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun e he => ?_).2 ⟨e₀, ?_, ?_⟩)
    · rw [Finset.mem_filter, hadd] at he
      rw [hD]
      split_ifs at he with h
      · exact absurd rfl he.2
      · exact he.2
    · exact (hD e₀).2 (hFne' e₀ he₀)
    · rw [Finset.mem_filter, hadd, ite_eq_left he₀]
      simp
  · unfold hdist
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun e he => ?_).2 ⟨e₀, ?_, ?_⟩)
    · rw [Finset.mem_filter, hsub] at he
      rw [hD]
      split_ifs at he with h
      · exact absurd rfl he.2
      · exact he.2
    · exact (hD e₀).2 (hFne' e₀ he₀)
    · rw [Finset.mem_filter, hsub, ite_eq_left he₀]
      simp

end Swap

/-! ### Merging a convex decomposition -/

section Rounding

variable {E : Type*}

/-- `x` can be rounded into `S` by a line process whose directions satisfy `ok`. -/
def Good (ok : (E → ℝ) → Prop) (S : Set (E → ℝ)) (x : E → ℝ) : Prop :=
  ∃ μ : FinDist (E → ℝ), LineProcess ok x μ ∧ ∀ z ∈ μ.support, z ∈ S

theorem good_stop {ok : (E → ℝ) → Prop} {S : Set (E → ℝ)} {z : E → ℝ}
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (hzS : z ∈ S) : Good ok S z := by
  refine ⟨FinDist.dirac z, LineProcess.stop z hz, fun z' hz' => ?_⟩
  simp only [FinDist.dirac, Finset.mem_singleton] at hz'
  rw [hz']
  exact hzS

theorem good_move [DecidableEq E] {ok : (E → ℝ) → Prop} {S : Set (E → ℝ)} {x δ : E → ℝ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hok : ok δ)
    (h₁ : Good ok S (x + α • δ)) (h₂ : Good ok S (x - β • δ)) : Good ok S x := by
  obtain ⟨μ₁, hμ₁, hs₁⟩ := h₁
  obtain ⟨μ₂, hμ₂, hs₂⟩ := h₂
  refine ⟨_, LineProcess.move x δ α β μ₁ μ₂ hα hβ hμ₁.isExact hμ₂.isExact hx hok hμ₁ hμ₂,
    fun z hz => ?_⟩
  classical
  rcases Finset.mem_union.1 hz with h | h
  exacts [hs₁ z h, hs₂ z h]

theorem pair_merge [DecidableEq E] {ok : (E → ℝ) → Prop} {S : Set (E → ℝ)} (d : (E → ℝ) → (E → ℝ) → ℕ)
    (hstep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ δ, ok δ ∧ a + δ ∈ S ∧ b - δ ∈ S ∧
      d (a + δ) b < d a b ∧ d a (b - δ) < d a b)
    {y : E → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (h1 : ∀ c ∈ S, Good ok S (y + (α + β) • c))
    (h01 : ∀ a ∈ S, ∀ b ∈ S, ∀ i, 0 ≤ (y + α • a + β • b) i ∧ (y + α • a + β • b) i ≤ 1)
    (n : ℕ) : ∀ a ∈ S, ∀ b ∈ S, d a b = n → Good ok S (y + α • a + β • b) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a ha b hb hn
  by_cases hab : a = b
  · subst hab
    have e : y + α • a + β • a = y + (α + β) • a := by rw [add_smul, add_assoc]
    rw [e]
    exact h1 a ha
  obtain ⟨δ, hok, haδ, hbδ, hd₁, hd₂⟩ := hstep a ha b hb hab
  refine good_move hα hβ (h01 a ha b hb) hok ?_ ?_
  · have e : y + α • a + β • b + α • δ = y + α • (a + δ) + β • b := by
      rw [smul_add]; abel
    rw [e]
    exact ih _ (hn ▸ hd₁) (a + δ) haδ b hb rfl
  · have e : y + α • a + β • b - β • δ = y + α • a + β • (b - δ) := by
      rw [smul_sub]; abel
    rw [e]
    exact ih _ (hn ▸ hd₂) a ha (b - δ) hbδ rfl

theorem mean_bounds {S : Set (E → ℝ)} (hS : ∀ z ∈ S, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (L : List (ℝ × (E → ℝ))) (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ∈ S) (i : E) :
    0 ≤ (L.map fun p => p.1 • p.2).sum i ∧
      (L.map fun p => p.1 • p.2).sum i ≤ (L.map Prod.fst).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih := ih fun q hq => hL q (by simp [hq])
    have hz := hS p.2 hp.2 i
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · nlinarith
    · nlinarith

theorem good_list [DecidableEq E] {ok : (E → ℝ) → Prop} {S : Set (E → ℝ)} (d : (E → ℝ) → (E → ℝ) → ℕ)
    (hstep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ δ, ok δ ∧ a + δ ∈ S ∧ b - δ ∈ S ∧
      d (a + δ) b < d a b ∧ d a (b - δ) < d a b)
    (hS : ∀ z ∈ S, ∀ i, 0 ≤ z i ∧ z i ≤ 1) (n : ℕ) :
    ∀ L : List (ℝ × (E → ℝ)), L.length = n → (∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ∈ S) →
      (L.map Prod.fst).sum = 1 → Good ok S (L.map fun p => p.1 • p.2).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hL hsum
  rcases L with _ | ⟨p, L₁⟩
  · simp at hsum
  have hp := hL p (by simp)
  by_cases hp0 : p.1 = 0
  · have := ih L₁.length (by simp at hn; omega) L₁ rfl (fun q hq => hL q (by simp [hq]))
      (by simpa [hp0] using hsum)
    simpa [hp0] using this
  have hpos : 0 < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  rcases L₁ with _ | ⟨q, R⟩
  · have h1 : p.1 = 1 := by simpa using hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, h1,
      one_smul]
    exact good_stop (hS p.2 hp.2) hp.2
  have hq := hL q (by simp)
  have hR : ∀ r ∈ R, 0 ≤ r.1 ∧ r.2 ∈ S := fun r hr => hL r (by simp [hr])
  by_cases hq0 : q.1 = 0
  · have := ih (R.length + 1) (by simp at hn; omega) (p :: R) rfl
      (fun r hr => by
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        exacts [hp, hR r hr])
      (by simp [hq0] at hsum ⊢; linarith)
    simpa [hq0] using this
  have hqpos : 0 < q.1 := lt_of_le_of_ne hq.1 (Ne.symm hq0)
  have hRsum : (R.map Prod.fst).sum = 1 - p.1 - q.1 := by
    simp only [List.map_cons, List.sum_cons] at hsum
    linarith
  have key := pair_merge d hstep hpos hqpos (y := (R.map fun p => p.1 • p.2).sum)
    (fun c hc => by
      have := ih (R.length + 1) (by simp at hn; omega) ((p.1 + q.1, c) :: R) rfl
        (fun r hr => by
          rw [List.mem_cons] at hr
          rcases hr with rfl | hr
          exacts [⟨by linarith, hc⟩, hR r hr])
        (by simp only [List.map_cons, List.sum_cons]; linarith)
      simpa [add_comm] using this)
    (fun a ha b hb i => by
      have hy := mean_bounds hS R hR i
      have hza := hS a ha i
      have hzb := hS b hb i
      rw [hRsum] at hy
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      constructor <;> nlinarith)
    _ p.2 hp.2 q.2 hq.2 rfl
  have e : ((p :: q :: R).map fun p => p.1 • p.2).sum =
      (R.map fun p => p.1 • p.2).sum + p.1 • p.2 + q.1 • q.2 := by
    simp only [List.map_cons, List.sum_cons]
    abel
  rw [e]
  exact key

end Rounding

end SwapRounding

open Classical in
/-- **Lemma 4.2 (Signed swap rounding).** If `x ∈ conv {z ∈ {0,1}^E : Bz = b}`, then `x` can be
rounded to one of these integral points by a finite sequence of mean-preserving two-point line
moves, each of which changes at most four edge variables incident with any fixed vertex. -/
theorem signed_swap_rounding {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (Γ : SignedGraph V E) (b : V → ℝ) (x : E → ℝ)
    (hx : x ∈ convexHull ℝ (Γ.integralSolutions b)) :
    ∃ μ : FinDist (E → ℝ),
      LineProcess (fun h => ∀ v, (univ.filter fun e =>
        h e ≠ 0 ∧ (Γ.fst e = v ∨ Γ.snd e = v)).card ≤ 4) x μ ∧
      ∀ z ∈ μ.support, z ∈ Γ.integralSolutions b := by
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hxz⟩ := mem_convexHull_iff_exists_fintype.1 hx
  have hS01 : ∀ z ∈ Γ.integralSolutions b, ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
    intro z hz i
    rcases hz.1 i with h | h <;> simp [h]
  have := SwapRounding.good_list SwapRounding.hdist
    (fun a ha b' hb' hne => SwapRounding.exists_delta Γ b ha hb' hne) hS01 _
    ((univ : Finset ι).toList.map fun i => (w i, z i)) rfl
    (fun p hp => by
      rw [List.mem_map] at hp
      obtain ⟨i, -, rfl⟩ := hp
      exact ⟨hw0 i, hz i⟩)
    (by rw [List.map_map, Finset.sum_map_toList]; exact hw1)
  obtain ⟨μ, hμ, hsupp⟩ := this
  have hmean : (((univ : Finset ι).toList.map fun i => (w i, z i)).map
      fun p => p.1 • p.2).sum = x := by
    rw [List.map_map, Finset.sum_map_toList]
    exact hxz
  rw [hmean] at hμ
  exact ⟨μ, hμ, hsupp⟩

end Lovasz
