/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Challenge

/-!
# Sanity checks for the statement surface

Fully proved lemmas showing that the definitions used in `Challenge.lean` mean what
`docs/Polylog_Cayley.pdf` means, and that the hypotheses of
`Lovasz.hamiltonian_of_polylog_degree` are satisfiable.

* `isConnectionSet_iff`: `IsConnectionSet S` is the paper's `S = S⁻¹ ⊆ G \ {1}`.
* `cayleyGraph_adj_iff`, `cayleyGraph_adj_mul_iff`: the edges of `cayleyGraph S` are exactly
  `x ∼ x * s` with `s ∈ S`.
* `cayleyGraph_degree`, `cayleyGraph_isRegularOfDegree`: `cayleyGraph S` is `|S|`-regular, so the
  paper's `d = |S|` is the graph degree.
* `cayleyGraph_connected_iff`: connectivity is the paper's convention `⟨S⟩ = G`.
* `log_log_pos`, `threshold_pos`: for `n ≥ 3` the degree threshold `C (log n)^13 / log log n` is a
  genuine positive real (no division by zero).
* `hypotheses_satisfiable`, `hypotheses_satisfiable_noncomplete`: for every `C` and `n₀` there
  are (complete, resp. non-complete) connected Cayley graphs meeting all the hypotheses, so the
  theorem is not vacuous.
* `small_counterexample`, `small_counterexample_of_nonneg`: `Cay(ℤ/2, {1}) = K₂` is a connected
  Cayley graph meeting the degree bound that is not Hamiltonian, so the hypothesis `n ≥ n₀`
  cannot be dropped.
* `isHamiltonian_gives_cycle`: the conclusion `IsHamiltonian` yields a genuine Hamilton cycle
  through every vertex.
-/

universe u

namespace Lovasz

open SimpleGraph Filter Pointwise

section Graph

variable {G : Type*} [Group G]

/-- `IsConnectionSet S` is the paper's hypothesis `S = S⁻¹ ⊆ G \ {1}`. -/
theorem isConnectionSet_iff [DecidableEq G] (S : Finset G) :
    IsConnectionSet S ↔ S⁻¹ = S ∧ (S : Set G) ⊆ {1}ᶜ := by
  constructor
  · rintro ⟨hinv, h1⟩
    refine ⟨?_, fun s hs hs1 => h1 (by rw [Set.mem_singleton_iff.1 hs1] at hs; exact hs)⟩
    ext s
    rw [Finset.mem_inv']
    exact ⟨fun h => by simpa using hinv _ h, fun h => hinv s h⟩
  · rintro ⟨hinv, h1⟩
    refine ⟨fun s hs => ?_, fun h => h1 h rfl⟩
    rw [← Finset.mem_inv', hinv]
    exact hs

/-- The edges of `Cay(G, S)` are exactly the pairs `x ∼ y` with `x⁻¹ * y ∈ S`. -/
theorem cayleyGraph_adj_iff {S : Finset G} (hS : IsConnectionSet S) (x y : G) :
    (cayleyGraph S).Adj x y ↔ x⁻¹ * y ∈ S := by
  rw [cayleyGraph, mulCayley_adj]
  simp only [Finset.mem_coe]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · simpa using hS.1 _ h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact hS.2 (by simpa using h)

/-- The edges of `Cay(G, S)` are exactly `x ∼ x * s` with `s ∈ S`. -/
theorem cayleyGraph_adj_mul_iff {S : Finset G} (hS : IsConnectionSet S) (x s : G) :
    (cayleyGraph S).Adj x (x * s) ↔ s ∈ S := by
  rw [cayleyGraph_adj_iff hS, inv_mul_cancel_left]

/-- The neighbourhood of `v` in `Cay(G, S)` is `v S`. -/
theorem cayleyGraph_neighborSet {S : Finset G} (hS : IsConnectionSet S) (v : G) :
    (cayleyGraph S).neighborSet v = (v * ·) '' (S : Set G) := by
  ext w
  simp only [mem_neighborSet, cayleyGraph_adj_iff hS, Set.mem_image, Finset.mem_coe]
  constructor
  · intro h
    exact ⟨v⁻¹ * w, h, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    simpa using hs

/-- Every vertex of `Cay(G, S)` has exactly `|S|` neighbours. -/
theorem cayleyGraph_ncard_neighborSet {S : Finset G} (hS : IsConnectionSet S) (v : G) :
    ((cayleyGraph S).neighborSet v).ncard = S.card := by
  rw [cayleyGraph_neighborSet hS, Set.ncard_image_of_injective _ (mul_right_injective v),
    Set.ncard_coe_finset]

/-- The paper's `d = |S|` is the degree of every vertex of `Cay(G, S)` (for any `Fintype`
instance on the neighbourhood). -/
theorem cayleyGraph_degree {S : Finset G} (hS : IsConnectionSet S) (v : G)
    [Fintype ((cayleyGraph S).neighborSet v)] : (cayleyGraph S).degree v = S.card := by
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    cayleyGraph_ncard_neighborSet hS]

/-- `Cay(G, S)` is `|S|`-regular. -/
theorem cayleyGraph_isRegularOfDegree [Fintype G] [DecidableEq G] {S : Finset G}
    (hS : IsConnectionSet S) : (cayleyGraph S).IsRegularOfDegree S.card :=
  fun v => cayleyGraph_degree hS v

/-- Every vertex reachable from `⟨s⟩` in `mulCayley s` lies in `⟨s⟩`. -/
theorem mem_closure_of_walk {s : Set G} {u v : G} (p : (mulCayley s).Walk u v)
    (hu : u ∈ Subgroup.closure s) : v ∈ Subgroup.closure s := by
  induction p with
  | nil => exact hu
  | @cons a b c h p ih =>
    apply ih
    rw [mulCayley_adj] at h
    rcases h.2 with h' | h'
    · simpa using mul_mem hu (Subgroup.subset_closure h')
    · simpa using mul_mem hu (inv_mem (Subgroup.subset_closure h'))

/-- `x` and `x * y` are joined in `mulCayley s` for `y ∈ s` (equal if `y = 1`). -/
theorem mulCayley_reachable_mul {s : Set G} (x : G) {y : G} (hy : y ∈ s) :
    (mulCayley s).Reachable x (x * y) := by
  by_cases hy1 : y = 1
  · subst hy1
    simp
  · refine Adj.reachable ((mulCayley_adj' s x (x * y)).2 ⟨?_, y, hy, Or.inl rfl⟩)
    simpa using hy1

/-- A Cayley graph is connected iff its generators generate the group. -/
theorem mulCayley_connected_iff (s : Set G) :
    (mulCayley s).Connected ↔ Subgroup.closure s = ⊤ := by
  constructor
  · intro h
    rw [Subgroup.eq_top_iff']
    intro x
    obtain ⟨p⟩ := h.preconnected 1 x
    exact mem_closure_of_walk p (one_mem _)
  · intro h
    rw [connected_iff_exists_forall_reachable]
    refine ⟨1, fun x => ?_⟩
    have hx : x ∈ Subgroup.closure s := h ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction_right with
    | one => rfl
    | mul_right x _ y hy ih => exact ih.trans (mulCayley_reachable_mul x hy)
    | mul_inv_cancel x _ y hy ih =>
      have := mulCayley_reachable_mul (x * y⁻¹) hy
      rw [inv_mul_cancel_right] at this
      exact ih.trans this.symm

/-- `Cay(G, S)` is connected iff `⟨S⟩ = G`, the paper's convention. -/
theorem cayleyGraph_connected_iff (S : Finset G) :
    (cayleyGraph S).Connected ↔ Subgroup.closure (S : Set G) = ⊤ :=
  mulCayley_connected_iff _

end Graph

section Threshold

/-- For `n ≥ 3 > e`, `log n > 1`. -/
theorem one_lt_log {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  calc Real.exp 1 < 3 := Real.exp_one_lt_three
    _ ≤ n := by exact_mod_cast hn

/-- For `n ≥ 3`, `log log n > 0`, so the threshold involves no division by zero. -/
theorem log_log_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Real.log (Real.log n) :=
  Real.log_pos (one_lt_log hn)

/-- For `C > 0` and `n ≥ 3`, the degree threshold `C (log n)^13 / log log n` is positive. -/
theorem threshold_pos {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 3 ≤ n) :
    0 < C * Real.log n ^ 13 / Real.log (Real.log n) :=
  div_pos (mul_pos hC (pow_pos (by linarith [one_lt_log hn]) 13)) (log_log_pos hn)

/-- `C (log n)^13 / log log n ≤ n / 2` for all large `n`. -/
theorem eventually_threshold_le_half (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * Real.log n ^ 13 / Real.log (Real.log n) ≤ (n : ℝ) / 2 := by
  have hc : 0 < Real.log (Real.log (3 : ℕ)) := log_log_pos le_rfl
  set c := Real.log (Real.log (3 : ℕ))
  have hε : 0 < c / (2 * (|C| + 1)) := by positivity
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 13)).def hε
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2, eventually_ge_atTop 3] with n hn h3
  have hL : 1 < Real.log n := one_lt_log h3
  have hP0 : 0 ≤ Real.log n ^ 13 := pow_nonneg (by linarith) 13
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hP0, abs_of_nonneg hn0] at hn
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hn
  have hcD : c ≤ Real.log (Real.log n) := by
    apply Real.log_le_log (Real.log_pos (by norm_num))
    apply Real.log_le_log (by norm_num)
    exact_mod_cast h3
  have hD : 0 < Real.log (Real.log n) := log_log_pos h3
  rw [div_le_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) hP0,
    mul_le_mul_of_nonneg_right hcD hn0, abs_nonneg C]

/-- For every `C` and `n₀` there is an even `n = 2m ≥ n₀` with `m ≥ 2` and
`C (log n)^13 / log log n ≤ n / 2`. -/
theorem exists_even_threshold_le (C : ℝ) (n₀ : ℕ) :
    ∃ m : ℕ, n₀ ≤ 2 * m ∧ 2 ≤ m ∧
      C * Real.log ((2 * m : ℕ) : ℝ) ^ 13 / Real.log (Real.log ((2 * m : ℕ) : ℝ)) ≤
        ((2 * m : ℕ) : ℝ) / 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_threshold_le_half C)
  refine ⟨N + n₀ + 2, by omega, by omega, hN _ (by omega)⟩

end Threshold

section Witnesses

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- `G \ {1}` is a connection set. -/
theorem isConnectionSet_univ_erase_one : IsConnectionSet (Finset.univ.erase (1 : G)) := by
  refine ⟨fun s hs => ?_, Finset.notMem_erase 1 _⟩
  simpa using hs

/-- The complete Cayley graph `Cay(G, G \ {1})` is connected. -/
theorem cayleyGraph_univ_erase_one_connected :
    (cayleyGraph (Finset.univ.erase (1 : G))).Connected := by
  rw [cayleyGraph_connected_iff, Subgroup.eq_top_iff']
  intro x
  by_cases hx : x = 1
  · subst hx
    exact one_mem _
  · exact Subgroup.subset_closure (by simp [hx])

/-- The complete Cayley graph `Cay(G, G \ {1})` has degree `|G| - 1`. -/
theorem card_univ_erase_one : (Finset.univ.erase (1 : G)).card = Fintype.card G - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ]

/-- For an involution `g ≠ 1` in a group of order at least `3`, `G \ {1, g}` is a connection set
generating a connected Cayley graph of degree `|G| - 2`. -/
theorem univ_erase_involution {g : G} (hg1 : g ≠ 1) (hg2 : g⁻¹ = g)
    (h3 : 3 ≤ Fintype.card G) :
    IsConnectionSet ((Finset.univ.erase (1 : G)).erase g) ∧
      (cayleyGraph ((Finset.univ.erase (1 : G)).erase g)).Connected ∧
      ((Finset.univ.erase (1 : G)).erase g).card = Fintype.card G - 2 := by
  refine ⟨⟨fun s hs => ?_, by simp⟩, ?_, ?_⟩
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hs ⊢
    refine ⟨fun h => hs.1 ?_, by simpa using hs.2⟩
    rw [← inv_inv s, h, hg2]
  · rw [cayleyGraph_connected_iff, Subgroup.eq_top_iff']
    intro x
    by_cases hx1 : x = 1
    · subst hx1
      exact one_mem _
    by_cases hxg : x = g
    · subst hxg
      have hlt : ({1, x} : Finset G).card < (Finset.univ : Finset G).card := by
        rw [Finset.card_univ]
        have := Finset.card_insert_le (1 : G) {x}
        rw [Finset.card_singleton] at this
        omega
      obtain ⟨h, -, hh⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
      have hmem1 : h ∈ (((Finset.univ.erase (1 : G)).erase x : Finset G) : Set G) := by
        simp [hh.1, hh.2]
      have hmem2 : h⁻¹ * x ∈ (((Finset.univ.erase (1 : G)).erase x : Finset G) : Set G) := by
        simp [hh.1, hh.2, inv_mul_eq_one]
      simpa using mul_mem (Subgroup.subset_closure hmem1) (Subgroup.subset_closure hmem2)
    · exact Subgroup.subset_closure (by simp [hx1, hxg])
  · rw [Finset.card_erase_of_mem (by simp [hg1]), card_univ_erase_one]
    omega

end Witnesses

/-- Non-vacuity: for every `C` and `n₀` the hypotheses of `hamiltonian_of_polylog_degree` are
satisfied by some connected Cayley graph (a complete graph `Cay(ℤ/n, ℤ/n \ {0})`). -/
theorem hypotheses_satisfiable (C : ℝ) (n₀ : ℕ) :
    ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (_ : DecidableEq G) (S : Finset G),
      IsConnectionSet S ∧ (cayleyGraph S).Connected ∧ n₀ ≤ Fintype.card G ∧
      C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card := by
  obtain ⟨m, hn₀, hm, hC⟩ := exists_even_threshold_le C n₀
  have : NeZero (2 * m) := ⟨by omega⟩
  have hcard : Fintype.card (ULift.{u} (Multiplicative (ZMod (2 * m)))) = 2 * m := by
    simp
  refine ⟨ULift.{u} (Multiplicative (ZMod (2 * m))), inferInstance, inferInstance, inferInstance,
    Finset.univ.erase 1, isConnectionSet_univ_erase_one, cayleyGraph_univ_erase_one_connected,
    by rw [hcard]; exact hn₀, ?_⟩
  rw [card_univ_erase_one, hcard]
  refine hC.trans ?_
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Nat.cast_sub (by omega)]
  push_cast
  linarith

/-- Non-vacuity beyond complete graphs: for every `C` and `n₀` the hypotheses of
`hamiltonian_of_polylog_degree` are satisfied by a connected Cayley graph that is not complete
(`Cay(ℤ/2m, ℤ/2m \ {0, m})`, of degree `n - 2`). -/
theorem hypotheses_satisfiable_noncomplete (C : ℝ) (n₀ : ℕ) :
    ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (_ : DecidableEq G) (S : Finset G),
      IsConnectionSet S ∧ (cayleyGraph S).Connected ∧ n₀ ≤ Fintype.card G ∧
      C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card ∧
      S.card < Fintype.card G - 1 := by
  obtain ⟨m, hn₀, hm, hC⟩ := exists_even_threshold_le C n₀
  have : NeZero (2 * m) := ⟨by omega⟩
  have hcard : Fintype.card (ULift.{u} (Multiplicative (ZMod (2 * m)))) = 2 * m := by
    simp
  let g : ULift.{u} (Multiplicative (ZMod (2 * m))) :=
    ULift.up (Multiplicative.ofAdd (m : ZMod (2 * m)))
  have hg1 : g ≠ 1 := by
    intro h
    have h' : (m : ZMod (2 * m)) = 0 := congrArg (fun x => Multiplicative.toAdd (ULift.down x)) h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by omega) h'
    omega
  have hg2 : g⁻¹ = g := by
    have h2m : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
    apply ULift.ext
    change Multiplicative.ofAdd (-(m : ZMod (2 * m))) = Multiplicative.ofAdd (m : ZMod (2 * m))
    congr 1
    push_cast at h2m
    linear_combination -h2m
  obtain ⟨hS, hconn, hSc⟩ := univ_erase_involution hg1 hg2 (by omega)
  refine ⟨ULift.{u} (Multiplicative (ZMod (2 * m))), inferInstance, inferInstance, inferInstance,
    (Finset.univ.erase 1).erase g, hS, hconn, by rw [hcard]; exact hn₀, ?_, ?_⟩
  · rw [hSc, hcard]
    refine hC.trans ?_
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  · rw [hSc, hcard]
    omega

section Small

/-- The connection set `{1}` in `ℤ/2` (written multiplicatively). -/
abbrev k2Set : Finset (Multiplicative (ZMod 2)) := {Multiplicative.ofAdd 1}

/-- `Cay(ℤ/2, {1}) = K₂` is a connected Cayley graph that is not Hamiltonian: the hypothesis
`n ≥ n₀` cannot be dropped. -/
theorem small_counterexample :
    IsConnectionSet k2Set ∧ (cayleyGraph k2Set).Connected ∧
      ¬ (cayleyGraph k2Set).IsHamiltonian := by
  refine ⟨⟨by decide, by decide⟩, ?_, not_isHamiltonian_of_card_eq_two (by simp)⟩
  rw [cayleyGraph_connected_iff, Subgroup.eq_top_iff']
  intro x
  fin_cases x
  · exact one_mem _
  · exact Subgroup.subset_closure (by decide)

/-- For every `C ≥ 0` there is a connected Cayley graph (on `2` vertices, in any universe)
meeting the degree bound `C (log n)^13 / log log n ≤ |S|` that is not Hamiltonian; so the
theorem needs `n₀ ≥ 3`. -/
theorem small_counterexample_of_nonneg (C : ℝ) (hC : 0 ≤ C) :
    ∃ (G : Type u) (_ : Group G) (_ : Fintype G) (_ : DecidableEq G) (S : Finset G),
      IsConnectionSet S ∧ (cayleyGraph S).Connected ∧ Fintype.card G = 2 ∧
      C * Real.log (Fintype.card G) ^ 13 / Real.log (Real.log (Fintype.card G)) ≤ S.card ∧
      ¬ (cayleyGraph S).IsHamiltonian := by
  have hcard : Fintype.card (ULift.{u} (Multiplicative (ZMod 2))) = 2 := by simp
  refine ⟨ULift.{u} (Multiplicative (ZMod 2)), inferInstance, inferInstance, inferInstance,
    Finset.univ.erase 1, isConnectionSet_univ_erase_one, cayleyGraph_univ_erase_one_connected,
    hcard, ?_, not_isHamiltonian_of_card_eq_two hcard⟩
  rw [hcard]
  have hl0 : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  have hl1 : Real.log ((2 : ℕ) : ℝ) < 1 := by
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hll : Real.log (Real.log ((2 : ℕ) : ℝ)) ≤ 0 := Real.log_nonpos hl0.le hl1.le
  exact (div_nonpos_of_nonneg_of_nonpos (by positivity) hll).trans (Nat.cast_nonneg _)

end Small

/-- The conclusion `IsHamiltonian` yields, through every vertex, a Hamilton cycle: a cycle of
length `n` visiting every vertex. -/
theorem isHamiltonian_gives_cycle {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Nontrivial G] {S : Finset G} (h : (cayleyGraph S).IsHamiltonian) (v : G) :
    ∃ p : (cayleyGraph S).Walk v v, p.IsHamiltonianCycle ∧ p.IsCycle ∧
      p.length = Fintype.card G ∧ ∀ w, w ∈ p.support := by
  obtain ⟨p, hp⟩ := h.exists_isHamiltonianCycle v
  exact ⟨p, hp, hp.isCycle, hp.length_eq, hp.mem_support⟩

end Lovasz
