/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Mathlib

/-!
# Toolchain smoke test

Checks that the Mathlib API a formalization of `docs/Polylog_Cayley.pdf`, Theorem 1.1, is likely
to need (simple graphs, connectivity, Hamiltonian cycles, subgroup closure, real logarithms) is
available at the pinned Mathlib revision, and that tactics run.
-/

namespace Lovasz

open SimpleGraph

example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  G.IsHamiltonian

example {V : Type*} [DecidableEq V] (G : SimpleGraph V) {a : V} (p : G.Walk a a) : Prop :=
  p.IsHamiltonianCycle

example {V : Type*} (G : SimpleGraph V) : Prop := G.Connected

example {G : Type*} [Group G] (S : Set G) : Subgroup G := Subgroup.closure S

example {G : Type*} [Group G] (S : Set G) (u v : G) :
    (mulCayley S).Adj u v ↔ u ≠ v ∧ (u⁻¹ * v ∈ S ∨ v⁻¹ * u ∈ S) :=
  mulCayley_adj S u v

example : (⊤ : SimpleGraph (Fin 2)).Connected := connected_top

example (x : ℝ) (hx : 1 < x) : 0 < Real.log x := Real.log_pos hx

example : (2 : ℕ) + 2 = 4 := by norm_num

end Lovasz
