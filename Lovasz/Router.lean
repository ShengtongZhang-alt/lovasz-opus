/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.6: linear-size Hamilton routers

DAG node `L3.6` of `docs/BLUEPRINT.md`.
-/

namespace Lovasz

open Set

/-- **Lemma 3.6 (Linear-size router).** For `w ≥ 2`, place comparators `0, …, w-2` in
succession between logical wires `j` and `j+1`. The fixed connections of the template are
`I₀ – x₁(0)`, `I₁ – x₂(0)`, `y₂(j) – x₁(j+1)` and `I_{j+2} – x₂(j+1)` for `j + 2 < w`,
`y₁(j) – O_j` for `j < w - 1`, and `y₂(w-2) – O_{w-1}`. Replacing the comparators by arbitrary
comparators on disjoint vertex sets and the fixed connections by vertex-disjoint paths (a path
system `Q` on `B` meeting each comparator only in its terminals) gives an `I, O`-Hamilton
router. -/
theorem router_of_comparators {V : Type*} [Fintype V] [DecidableEq V] (w : ℕ) (hw : 2 ≤ w)
    (A : ℕ → Set V) (K : ℕ → SimpleGraph V) (x₁ x₂ y₁ y₂ : ℕ → V) (I O : ℕ → V)
    (hcomp : ∀ j < w - 1, IsComparator (K j) (A j) (x₁ j) (x₂ j) (y₁ j) (y₂ j))
    (hAdisj : ∀ j < w - 1, ∀ j' < w - 1, j ≠ j' → Disjoint (A j) (A j'))
    (hI : InjOn I (Iio w)) (hO : InjOn O (Iio w)) (hIO : ∀ k < w, ∀ k' < w, I k ≠ O k')
    (hIOA : ∀ k < w, ∀ j < w - 1, I k ∉ A j ∧ O k ∉ A j)
    (Q : SimpleGraph V) (B : Set V)
    (hQ : IsPathSystem Q B (I '' Iio w ∪ O '' Iio w ∪
      ⋃ j ∈ Iio (w - 1), ({x₁ j, x₂ j, y₁ j, y₂ j} : Set V)))
    (hB : ∀ j < w - 1, B ∩ A j = {x₁ j, x₂ j, y₁ j, y₂ j})
    (hc₁ : Q.Reachable (I 0) (x₁ 0)) (hc₂ : Q.Reachable (I 1) (x₂ 0))
    (hc₃ : ∀ j, j + 2 < w → Q.Reachable (y₂ j) (x₁ (j + 1)) ∧ Q.Reachable (I (j + 2)) (x₂ (j + 1)))
    (hc₄ : ∀ j < w - 1, Q.Reachable (y₁ j) (O j)) (hc₅ : Q.Reachable (y₂ (w - 2)) (O (w - 1))) :
    IsHamRouter (Q ⊔ ⨆ j ∈ Iio (w - 1), K j) (B ∪ ⋃ j ∈ Iio (w - 1), A j) (I '' Iio w)
      (O '' Iio w) := by
  sorry

end Lovasz
