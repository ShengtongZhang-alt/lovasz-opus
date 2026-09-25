/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Watkins

/-!
# Lemma 5.2: cuts of the vertex–copy incidence graph

DAG node `L5.2` of `docs/BLUEPRINT.md`. Depends on Watkins's bound.
-/

universe u

namespace Lovasz

open Finset

/-- The vertex set `g (A⁺ ∪ A⁻)` of the translated copy `gF`. -/
def copyVerts {G : Type u} [Group G] [DecidableEq G] (Ap Am : Finset G) (g : G) : Finset G :=
  (Ap ∪ Am).image (g * ·)

/-- **Lemma 5.2.** Let the translates `g_i F` cover every `T`-edge. Fix a left coset `C` of
`U = ⟨T⟩` and split the copies lying in `C` into two nonempty families `I₁, I₂`. Let `B` be the
set of vertices belonging to copies of both families. Then `|B| ≥ min (m, |T|/2)`, where
`m = |V(F)|`; hence every cut of the incidence graph with copy indices on both shores has at
least `cd` crossing incidences. -/
theorem incidence_cut {G : Type u} [Group G] [Fintype G] [DecidableEq G]
    (T Ap Am : Finset G) (hT : IsConnectionSet T) (hTne : T.Nonempty)
    (hF : ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Connected)
    {t : ℕ} (g : Fin t → G)
    (hcover : ∀ x : G, ∀ s ∈ T, ∃ i, (templateGraph T Ap Am).Adj ((g i)⁻¹ * x) ((g i)⁻¹ * (x * s)))
    (x₀ : G) (I₁ I₂ : Finset (Fin t)) (hdisj : Disjoint I₁ I₂) (hne₁ : I₁.Nonempty)
    (hne₂ : I₂.Nonempty)
    (hcoset : ∀ i, i ∈ I₁ ∪ I₂ ↔ ∃ v ∈ copyVerts Ap Am (g i),
      x₀⁻¹ * v ∈ Subgroup.closure (T : Set G)) :
    (Ap ∪ Am).card ≤ (univ.filter fun v => (∃ i ∈ I₁, v ∈ copyVerts Ap Am (g i)) ∧
        (∃ i ∈ I₂, v ∈ copyVerts Ap Am (g i))).card ∨
      T.card ≤ 2 * (univ.filter fun v => (∃ i ∈ I₁, v ∈ copyVerts Ap Am (g i)) ∧
        (∃ i ∈ I₂, v ∈ copyVerts Ap Am (g i))).card := by
  set U := Subgroup.closure (T : Set G) with hU
  set B : Finset G := univ.filter fun v => (∃ i ∈ I₁, v ∈ copyVerts Ap Am (g i)) ∧
    (∃ i ∈ I₂, v ∈ copyVerts Ap Am (g i)) with hBdef
  have hmemB : ∀ v, v ∈ B ↔ (∃ i ∈ I₁, v ∈ copyVerts Ap Am (g i)) ∧
      (∃ i ∈ I₂, v ∈ copyVerts Ap Am (g i)) := fun v => by
    simp only [B, mem_filter, mem_univ, true_and]
  by_cases hm : (Ap ∪ Am).card ≤ B.card
  · exact Or.inl hm
  right
  by_contra hTB
  rw [not_le] at hTB hm
  have hmemcopy : ∀ (h v : G), v ∈ copyVerts Ap Am h ↔ h⁻¹ * v ∈ Ap ∪ Am := by
    intro h v
    unfold copyVerts
    constructor
    · intro hv
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
      simpa using ha
    · intro hv
      exact mem_image.2 ⟨_, hv, by simp⟩
  -- The template is connected, so its vertex set lies in one left coset of `U`.
  have htemp : ∀ a b : G, (templateGraph T Ap Am).Adj a b → a⁻¹ * b ∈ U := by
    intro a b h
    rcases h.2.2 with h' | h'
    · exact Subgroup.subset_closure h'
    · have := inv_mem (Subgroup.subset_closure h' : b⁻¹ * a ∈ U)
      simpa using this
  have hFU : ∀ a ∈ Ap ∪ Am, ∀ b ∈ Ap ∪ Am, a⁻¹ * b ∈ U := by
    intro a ha
    have key : ∀ w : ↥((Ap ∪ Am : Finset G) : Set G),
        ((templateGraph T Ap Am).induce ((Ap ∪ Am : Finset G) : Set G)).Reachable ⟨a, ha⟩ w →
          a⁻¹ * w.1 ∈ U := by
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
  have hcopyU : ∀ i, ∀ u ∈ copyVerts Ap Am (g i), ∀ v ∈ copyVerts Ap Am (g i), u⁻¹ * v ∈ U := by
    intro i u hu v hv
    have := hFU _ ((hmemcopy _ _).1 hu) _ ((hmemcopy _ _).1 hv)
    simpa [mul_assoc] using this
  have hcosetU : ∀ i ∈ I₁ ∪ I₂, ∀ v ∈ copyVerts Ap Am (g i), x₀⁻¹ * v ∈ U := by
    intro i hi v hv
    obtain ⟨u, hu, hxu⟩ := (hcoset i).1 hi
    rw [show x₀⁻¹ * v = (x₀⁻¹ * u) * (u⁻¹ * v) by group]
    exact mul_mem hxu (hcopyU i u hu v hv)
  -- Every copy has a vertex outside `B`, since `|B| < m`.
  have hexists : ∀ i ∈ I₁ ∪ I₂, ∃ v ∈ copyVerts Ap Am (g i), v ∉ B ∧ x₀⁻¹ * v ∈ U := by
    intro i hi
    have hcard : (copyVerts Ap Am (g i)).card = (Ap ∪ Am).card :=
      card_image_of_injective _ (mul_right_injective (g i))
    have hns : ¬ copyVerts Ap Am (g i) ⊆ B := fun hs => by
      have := card_le_card hs
      omega
    obtain ⟨v, hv, hvB⟩ := not_subset.1 hns
    exact ⟨v, hv, hvB, hcosetU i hi v hv⟩
  -- Every `T`-edge lies in some copy.
  have hedge : ∀ u w : G, (cayleyGraph T).Adj u w →
      ∃ j, u ∈ copyVerts Ap Am (g j) ∧ w ∈ copyVerts Ap Am (g j) := by
    have hts : ∀ u, ∀ s ∈ T, ∃ j, u ∈ copyVerts Ap Am (g j) ∧
        u * s ∈ copyVerts Ap Am (g j) := by
      intro u s hs
      obtain ⟨j, hj⟩ := hcover u s hs
      have hmem : ∀ a b : G, (templateGraph T Ap Am).Adj a b → a ∈ Ap ∪ Am ∧ b ∈ Ap ∪ Am := by
        intro a b h
        rcases h.2.1 with h' | h'
        · exact ⟨mem_union_left _ h'.1, mem_union_right _ h'.2⟩
        · exact ⟨mem_union_right _ h'.1, mem_union_left _ h'.2⟩
      obtain ⟨h1, h2⟩ := hmem _ _ hj
      exact ⟨j, (hmemcopy _ _).2 h1, (hmemcopy _ _).2 h2⟩
    intro u w huw
    rw [SimpleGraph.mulCayley_adj] at huw
    rcases huw.2 with h | h
    · obtain ⟨j, hj1, hj2⟩ := hts u _ h
      rw [mul_inv_cancel_left] at hj2
      exact ⟨j, hj1, hj2⟩
    · obtain ⟨j, hj1, hj2⟩ := hts w _ h
      rw [mul_inv_cancel_left] at hj2
      exact ⟨j, hj2, hj1⟩
  obtain ⟨i1, hi1⟩ := hne₁
  obtain ⟨i2, hi2⟩ := hne₂
  obtain ⟨v1, hv1c, hv1B, hv1U⟩ := hexists i1 (mem_union_left _ hi1)
  obtain ⟨v2, hv2c, hv2B, hv2U⟩ := hexists i2 (mem_union_right _ hi2)
  have hv12 : v1⁻¹ * v2 ∈ U := by
    rw [show v1⁻¹ * v2 = (x₀⁻¹ * v1)⁻¹ * (x₀⁻¹ * v2) by group]
    exact mul_mem (inv_mem hv1U) hv2U
  have hreach := watkins_cayley T hT B hTB v1 v2 hv1B hv2B hv12
  -- Along a walk avoiding `B`, one stays inside copies of the first family.
  have key : ∀ w : ↥((B : Set G)ᶜ),
      ((cayleyGraph T).induce ((B : Set G)ᶜ)).Reachable ⟨v1, hv1B⟩ w →
        x₀⁻¹ * w.1 ∈ U ∧ ∃ i ∈ I₁, w.1 ∈ copyVerts Ap Am (g i) := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => exact ⟨hv1U, i1, hi1, hv1c⟩
    | tail _ hadj ih =>
      rename_i c d _
      obtain ⟨hcU, i, hi, hci⟩ := ih
      obtain ⟨j, hcj, hdj⟩ := hedge c.1 d.1 hadj
      have hjI : j ∈ I₁ ∪ I₂ := (hcoset j).2 ⟨c.1, hcj, hcU⟩
      have hj1 : j ∈ I₁ := by
        rcases mem_union.1 hjI with h | h
        · exact h
        · exact absurd ((hmemB c.1).2 ⟨⟨i, hi, hci⟩, ⟨j, h, hcj⟩⟩) c.2
      exact ⟨hcosetU j hjI d.1 hdj, j, hj1, hdj⟩
  obtain ⟨-, i, hi, hv2i⟩ := key _ hreach
  exact hv2B ((hmemB v2).2 ⟨⟨i, hi, hv2i⟩, ⟨i2, hi2, hv2c⟩⟩)

end Lovasz
