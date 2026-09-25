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
  sorry

end Lovasz
