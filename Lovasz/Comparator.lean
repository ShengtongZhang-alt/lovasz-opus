/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Lovasz.Defs

/-!
# Lemma 3.5: even-cycle comparators

DAG node `L3.5` of `docs/BLUEPRINT.md`.
-/

namespace Lovasz

open Finset

/-- The endpoints of the pairing (3.4) of a `2r`-cycle. -/
def comparatorPairEnds {V : Type*} {r : ℕ} (hr : 0 < r) (c : Fin (2 * r) → V) : Set V :=
  {v | ∃ p ∈ comparatorPairs r, v = cyc hr c p.1 ∨ v = cyc hr c p.2}

namespace Comparator

variable {V : Type*}

/-! ### Index arithmetic -/

theorem mem_comparatorPairs {r : ℕ} {p : ℕ × ℕ} :
    p ∈ comparatorPairs r ↔ 3 ≤ r ∧
      ((∃ J, 1 ≤ J ∧ J + 3 ≤ r ∧ p = (2 * J + 1, 2 * J + 4)) ∨ p = (2 * r - 3, 2 * r - 1)) := by
  unfold comparatorPairs
  split_ifs with h
  · simp only [List.not_mem_nil, false_iff, not_and]
    intro h'; omega
  · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
    constructor
    · rintro (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨by omega, Or.inl ⟨j + 1, by omega, by omega, by ext <;> simp⟩⟩
      · exact ⟨by omega, Or.inr rfl⟩
    · rintro ⟨-, ⟨J, hJ1, hJ2, rfl⟩ | rfl⟩
      · refine Or.inl ⟨J - 1, by omega, ?_⟩
        ext <;> simp <;> omega
      · exact Or.inr rfl

theorem pair_facts {r : ℕ} {p : ℕ × ℕ} (hp : p ∈ comparatorPairs r) :
    3 ≤ r ∧ 3 ≤ p.1 ∧ p.1 % 2 = 1 ∧ (p.2 = p.1 + 3 ∨ p.2 = p.1 + 2) ∧ p.2 < 2 * r := by
  obtain ⟨hr, ⟨J, hJ1, hJ2, rfl⟩ | rfl⟩ := mem_comparatorPairs.1 hp
  · refine ⟨hr, ?_⟩
    show 3 ≤ 2 * J + 1 ∧ (2 * J + 1) % 2 = 1 ∧
      (2 * J + 4 = 2 * J + 1 + 3 ∨ 2 * J + 4 = 2 * J + 1 + 2) ∧ 2 * J + 4 < 2 * r
    omega
  · refine ⟨hr, ?_⟩
    show 3 ≤ 2 * r - 3 ∧ (2 * r - 3) % 2 = 1 ∧
      (2 * r - 1 = 2 * r - 3 + 3 ∨ 2 * r - 1 = 2 * r - 3 + 2) ∧ 2 * r - 1 < 2 * r
    omega

theorem mod_cases (a n : ℕ) (h : a < 2 * n) :
    (a % n = a ∧ a < n) ∨ (a % n = a - n ∧ n ≤ a) := by
  rcases lt_or_ge a n with h' | h'
  · exact Or.inl ⟨Nat.mod_eq_of_lt h', h'⟩
  · refine Or.inr ⟨?_, h'⟩
    rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]

/-- The partner of `i` in the matching `{2k, 2k+1}`. -/
def mate (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

theorem mate_cases (i : ℕ) : (i % 2 = 0 ∧ mate i = i + 1) ∨ (i % 2 = 1 ∧ mate i = i - 1) := by
  unfold mate; split_ifs <;> omega

/-! ### Cycle vertices -/

theorem cycleOn_adj_gen {n : ℕ} (hn : 2 ≤ n) (d : Fin n → V) (hd : Function.Injective d)
    (k : ℕ) :
    (cycleOn d).Adj (d ⟨k % n, Nat.mod_lt _ (by omega)⟩)
      (d ⟨(k + 1) % n, Nat.mod_lt _ (by omega)⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold cycleOn
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨⟨k % (m + 1), Nat.mod_lt _ (by omega)⟩, ?_⟩, ?_⟩
  · congr 2
    rw [finRotate_apply]
    ext
    simp only [Fin.val_add]
    simp [Nat.add_mod]
  · intro h
    have := congrArg Fin.val (hd h)
    simp only at this
    have h1 : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [Nat.add_mod, h1] at this
    have h2 := Nat.mod_lt k (show 0 < m + 1 by omega)
    rcases mod_cases (k % (m + 1) + 1) (m + 1) (by omega) with h3 | h3 <;> omega

section Cyc

variable {r : ℕ} (hr : 0 < r) {c : Fin (2 * r) → V}

theorem cyc_eq_iff (hc : Function.Injective c) {a b : ℕ} :
    cyc hr c a = cyc hr c b ↔ a % (2 * r) = b % (2 * r) := by
  unfold cyc
  constructor
  · intro h; exact congrArg Fin.val (hc h)
  · intro h; congr 1; exact Fin.ext h

theorem cyc_mem_range (k : ℕ) : cyc hr c k ∈ Set.range c := ⟨_, rfl⟩

theorem cyc_val (j : Fin (2 * r)) : cyc hr c j.val = c j := by
  unfold cyc; congr 1; exact Fin.ext (Nat.mod_eq_of_lt j.isLt)

theorem cycleOn_adj_cyc (hr2 : 2 ≤ r) (hc : Function.Injective c) (k : ℕ) :
    (cycleOn c).Adj (cyc hr c k) (cyc hr c (k + 1)) :=
  cycleOn_adj_gen (by omega) c hc k

end Cyc

/-! ### Perfect matchings of consecutive indices -/

/-- The perfect matching `{f (2k), f (2k+1)}`, `k < r`. -/
def matchG (f : ℕ → V) (r : ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ k < r, e = s(f (2 * k), f (2 * k + 1))}

section Match

variable {f : ℕ → V} {r : ℕ}

theorem matchG_adj_iff {x y : V} :
    (matchG f r).Adj x y ↔ (∃ k < r, s(x, y) = s(f (2 * k), f (2 * k + 1))) ∧ x ≠ y := by
  unfold matchG; rw [SimpleGraph.fromEdgeSet_adj]; rfl

theorem matchG_neighborSet (hf : ∀ a < 2 * r, ∀ b < 2 * r, f a = f b → a = b) {i : ℕ}
    (hi : i < 2 * r) : (matchG f r).neighborSet (f i) = {f (mate i)} := by
  ext y
  rw [SimpleGraph.mem_neighborSet, matchG_adj_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨k, hk, he⟩, -⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hf _ hi _ (by omega) h1
      rw [h2]; congr 1; rcases mate_cases i with h | h <;> omega
    · have := hf _ hi _ (by omega) h1
      rw [h2]; congr 1; rcases mate_cases i with h | h <;> omega
  · rintro rfl
    refine ⟨⟨i / 2, by omega, ?_⟩, ?_⟩
    · rcases mate_cases i with ⟨h, h'⟩ | ⟨h, h'⟩
      · rw [h', show 2 * (i / 2) = i by omega]
      · rw [h', show 2 * (i / 2) = i - 1 by omega, show i - 1 + 1 = i by omega, Sym2.eq_swap]
    · intro h
      have := hf _ hi _ (by rcases mate_cases i with h | h <;> omega) h
      rcases mate_cases i with h | h <;> omega

theorem matchG_neighborSet_eq_empty {x : V} (hx : ∀ k < 2 * r, f k ≠ x) :
    (matchG f r).neighborSet x = ∅ := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, matchG_adj_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨k, hk, he⟩, -⟩
  rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hx _ (by omega) h1.symm
  · exact hx _ (by omega) h1.symm

theorem matchG_adj (hf : ∀ a < 2 * r, ∀ b < 2 * r, f a = f b → a = b) {k : ℕ} (hk : k < r) :
    (matchG f r).Adj (f (2 * k)) (f (2 * k + 1)) :=
  matchG_adj_iff.2 ⟨⟨k, hk, rfl⟩, fun h => by have := hf _ (by omega) _ (by omega) h; omega⟩

theorem matchG_le {G : SimpleGraph V} (h : ∀ k < r, G.Adj (f (2 * k)) (f (2 * k + 1))) :
    matchG f r ≤ G := by
  intro x y hxy
  obtain ⟨⟨k, hk, he⟩, -⟩ := matchG_adj_iff.1 hxy
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h k hk
  · exact (h k hk).symm

end Match

/-! ### Path systems -/

/-- In a graph where `x ∼ y` both have degree one, the component of `x` is `{x, y}`. -/
theorem reach_of_adj_deg_one {Q : SimpleGraph V} {x y z : V} (hxy : Q.Adj x y)
    (hx : (Q.neighborSet x).ncard = 1) (hy : (Q.neighborSet y).ncard = 1)
    (hz : Q.Reachable x z) : z = x ∨ z = y := by
  have hN : ∀ u v, Q.Adj u v → (Q.neighborSet u).ncard = 1 → Q.neighborSet u = {v} := by
    intro u v huv hu
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hu
    have : v ∈ Q.neighborSet u := huv
    rw [ha, Set.mem_singleton_iff] at this
    rw [ha, this]
  have hNx := hN x y hxy hx
  have hNy := hN y x hxy.symm hy
  obtain ⟨w⟩ := hz
  suffices ∀ u v (p : Q.Walk u v), (u = x ∨ u = y) → (v = x ∨ v = y) from this _ _ w (Or.inl rfl)
  intro u v p
  induction p with
  | nil => exact id
  | cons h p ih =>
    intro hu
    apply ih
    rcases hu with rfl | rfl
    · have : _ ∈ Q.neighborSet _ := h
      rw [hNx, Set.mem_singleton_iff] at this
      exact Or.inr this
    · have : _ ∈ Q.neighborSet _ := h
      rw [hNy, Set.mem_singleton_iff] at this
      exact Or.inl this

/-- A perfect matching of `C` together with a path system `Q` meeting `C` in its endpoint set
`E` is a path system with endpoint set `T`, under the degree and reachability conditions. -/
theorem pathSystem_matching_sup [Finite V] {r : ℕ} {C : Set V} (f : ℕ → V)
    (hf : ∀ a < 2 * r, ∀ b < 2 * r, f a = f b → a = b)
    (hfC : ∀ k, f k ∈ C) (hCf : ∀ x ∈ C, ∃ i < 2 * r, f i = x)
    {Q : SimpleGraph V} {B E T : Set V}
    (hQ : IsPathSystem Q B E) (hB : B ∩ C = E)
    (hQf : ∀ i < 2 * r, ¬ Q.Adj (f i) (f (mate i)))
    (hTE : ∀ x ∈ T, x ∈ C ∧ x ∉ E)
    (hcov : ∀ x ∈ C, x ∉ T → x ∈ E)
    (hreach : ∀ x ∈ C, ∃ t ∈ T, (matchG f r ⊔ Q).Reachable x t) :
    IsPathSystem (matchG f r ⊔ Q) (C ∪ B) T where
  adj_mem x y h := by
    rcases h with h | h
    · obtain ⟨⟨k, hk, he⟩, -⟩ := matchG_adj_iff.1 h
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        exact ⟨Or.inl (hfC _), Or.inl (hfC _)⟩
    · obtain ⟨h1, h2⟩ := hQ.adj_mem x y h
      exact ⟨Or.inr h1, Or.inr h2⟩
  subset x hx := Or.inl (hTE x hx).1
  deg_end x hx := by
    obtain ⟨hxC, hxE⟩ := hTE x hx
    obtain ⟨i, hi, rfl⟩ := hCf x hxC
    have hQe : Q.neighborSet (f i) = ∅ := by
      ext y
      simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hxE
      rw [← hB]
      exact ⟨(hQ.adj_mem _ _ h).1, hxC⟩
    rw [SimpleGraph.neighborSet_sup, matchG_neighborSet hf hi, hQe, Set.union_empty,
      Set.ncard_singleton]
  deg_inner x hx hxT := by
    by_cases hxC : x ∈ C
    · have hxE := hcov x hxC hxT
      obtain ⟨i, hi, rfl⟩ := hCf x hxC
      rw [SimpleGraph.neighborSet_sup, matchG_neighborSet hf hi, Set.ncard_union_eq,
        Set.ncard_singleton, hQ.deg_end _ hxE]
      rw [Set.disjoint_singleton_left]
      exact hQf i hi
    · have hxB : x ∈ B := hx.resolve_left hxC
      have hxE : x ∉ E := by
        intro h
        rw [← hB] at h
        exact hxC h.2
      rw [SimpleGraph.neighborSet_sup,
        matchG_neighborSet_eq_empty (fun k _ (h : f k = x) => hxC (h ▸ hfC k)), Set.empty_union]
      exact hQ.deg_inner x hxB hxE
  reach_end x hx := by
    rcases hx with hxC | hxB
    · exact hreach x hxC
    · obtain ⟨t', ht', hxt'⟩ := hQ.reach_end x hxB
      have ht'C : t' ∈ C := by
        rw [← hB] at ht'
        exact ht'.2
      obtain ⟨t, ht, h⟩ := hreach t' ht'C
      exact ⟨t, ht, (hxt'.mono le_sup_right).trans h⟩

/-! ### The pairing (3.4) -/

section Pairing

variable {r : ℕ} (hr0 : 0 < r) {c : Fin (2 * r) → V}

/-- `Q` contains no edge of the matchings `M₀` (`s = 0`) or `M₁` (`s = 1`). -/
theorem no_Q_mate (hc : Function.Injective c) {Q : SimpleGraph V} {B : Set V}
    (hQ : IsPathSystem Q B (comparatorPairEnds hr0 c))
    (hpairs : ∀ p ∈ comparatorPairs r, Q.Reachable (cyc hr0 c p.1) (cyc hr0 c p.2))
    (hB : B ∩ Set.range c = comparatorPairEnds hr0 c) (s : ℕ) (hs : s ≤ 1) {i : ℕ}
    (hi : i < 2 * r) : ¬ Q.Adj (cyc hr0 c (i + s)) (cyc hr0 c (mate i + s)) := by
  intro hadj
  have hxE : cyc hr0 c (i + s) ∈ comparatorPairEnds hr0 c := by
    rw [← hB]; exact ⟨(hQ.adj_mem _ _ hadj).1, cyc_mem_range _ _⟩
  have hyE : cyc hr0 c (mate i + s) ∈ comparatorPairEnds hr0 c := by
    rw [← hB]; exact ⟨(hQ.adj_mem _ _ hadj).2, cyc_mem_range _ _⟩
  have key : ∀ z, Q.Reachable (cyc hr0 c (i + s)) z →
      z = cyc hr0 c (i + s) ∨ z = cyc hr0 c (mate i + s) :=
    fun z hz => reach_of_adj_deg_one hadj (hQ.deg_end _ hxE) (hQ.deg_end _ hyE) hz
  obtain ⟨p, hp, hxp⟩ := hxE
  obtain ⟨hr3, hp1, hp1o, hp2, hp2r⟩ := pair_facts hp
  have hm1 : p.1 % (2 * r) = p.1 := Nat.mod_eq_of_lt (by omega)
  have hm2 : p.2 % (2 * r) = p.2 := Nat.mod_eq_of_lt hp2r
  have hmc := mate_cases i
  have hc1 := mod_cases (i + s) (2 * r) (by omega)
  have hc2 := mod_cases (mate i + s) (2 * r) (by rcases hmc with h | h <;> omega)
  rcases hxp with hxp | hxp
  · have h := key (cyc hr0 c p.2) (by rw [hxp]; exact hpairs p hp)
    rw [cyc_eq_iff hr0 hc] at hxp
    rcases h with h | h <;> rw [cyc_eq_iff hr0 hc] at h <;> omega
  · have h := key (cyc hr0 c p.1) (by rw [hxp]; exact (hpairs p hp).symm)
    rw [cyc_eq_iff hr0 hc] at hxp
    rcases h with h | h <;> rw [cyc_eq_iff hr0 hc] at h <;> omega

/-- Reachability in `M₀ ∪ P`: every `M₀`-edge `c_{2k} c_{2k+1}`, `1 ≤ k ≤ r-1`, lies on the
path starting at `c₂`. -/
theorem reach_M0 (c : Fin (2 * r) → V) (P : SimpleGraph V)
    (he : ∀ k, k < r → P.Adj (cyc hr0 c (2 * k)) (cyc hr0 c (2 * k + 1)))
    (hq : ∀ p ∈ comparatorPairs r, P.Reachable (cyc hr0 c p.1) (cyc hr0 c p.2))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ r) :
    P.Reachable (cyc hr0 c 2) (cyc hr0 c (2 * k)) := by
  have hodd : ∀ m, 2 * m + 2 ≤ r →
      P.Reachable (cyc hr0 c 2) (cyc hr0 c (2 * (2 * m + 1))) := by
    intro m
    induction m with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 := (he (2 * m + 1) (by omega)).reachable
      have h3 : P.Reachable (cyc hr0 c (2 * (2 * m + 1) + 1)) (cyc hr0 c (2 * (2 * m + 1) + 4)) :=
        hq _ (mem_comparatorPairs.2 ⟨by omega, Or.inl ⟨2 * m + 1, by omega, by omega, rfl⟩⟩)
      rw [show 2 * (2 * (m + 1) + 1) = 2 * (2 * m + 1) + 4 by ring]
      exact h1.trans (h2.trans h3)
  have htop : ∀ k, k % 2 = 0 → 2 ≤ k → k + 1 ≤ r → r ≤ k + 2 →
      P.Reachable (cyc hr0 c 2) (cyc hr0 c (2 * k)) := by
    intro k hk0 hk2 hk3 hk4
    have hlast : P.Reachable (cyc hr0 c (2 * r - 3)) (cyc hr0 c (2 * r - 1)) :=
      hq _ (mem_comparatorPairs.2 ⟨by omega, Or.inr rfl⟩)
    rcases (show k = r - 1 ∨ k = r - 2 by omega) with rfl | rfl
    · have h1 := hodd ((r - 3) / 2) (by omega)
      rw [show 2 * (2 * ((r - 3) / 2) + 1) = 2 * (r - 2) by omega] at h1
      have h2 := (he (r - 2) (by omega)).reachable
      have h3 := (he (r - 1) (by omega)).reachable
      rw [show 2 * (r - 2) + 1 = 2 * r - 3 by omega] at h2
      rw [show 2 * (r - 1) + 1 = 2 * r - 1 by omega] at h3
      exact h1.trans (h2.trans (hlast.trans h3.symm))
    · have h1 := hodd ((r - 2) / 2) (by omega)
      rw [show 2 * (2 * ((r - 2) / 2) + 1) = 2 * (r - 1) by omega] at h1
      have h2 := (he (r - 1) (by omega)).reachable
      have h3 := (he (r - 2) (by omega)).reachable
      rw [show 2 * (r - 1) + 1 = 2 * r - 1 by omega] at h2
      rw [show 2 * (r - 2) + 1 = 2 * r - 3 by omega] at h3
      exact h1.trans (h2.trans (hlast.symm.trans h3.symm))
  have heven : ∀ d k, k % 2 = 0 → 2 ≤ k → k + 1 ≤ r → r ≤ k + 2 + 2 * d →
      P.Reachable (cyc hr0 c 2) (cyc hr0 c (2 * k)) := by
    intro d
    induction d with
    | zero => intro k h0 h2 h3 h4; exact htop k h0 h2 h3 (by omega)
    | succ d ih =>
      intro k h0 h2 h3 h4
      by_cases hk : r ≤ k + 2
      · exact htop k h0 h2 h3 hk
      · have h1 := ih (k + 2) (by omega) (by omega) (by omega) (by omega)
        have hp : P.Reachable (cyc hr0 c (2 * k + 1)) (cyc hr0 c (2 * k + 4)) :=
          hq _ (mem_comparatorPairs.2 ⟨by omega, Or.inl ⟨k, by omega, by omega, rfl⟩⟩)
        have h2 := (he k (by omega)).reachable
        rw [show 2 * (k + 2) = 2 * k + 4 by ring] at h1
        exact h1.trans (hp.symm.trans h2.symm)
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · exact heven r (2 * m) (by omega) (by omega) hk2 (by omega)
  · exact hodd m (by omega)

/-- Reachability in `M₁ ∪ P`: every `M₁`-edge `c_{2k+1} c_{2k+2}`, `1 ≤ k ≤ r-1`, lies on the
path starting at `c_t` (where `c_t` reaches `c₃`). -/
theorem reach_M1 (c : Fin (2 * r) → V) (P : SimpleGraph V) (t : ℕ)
    (he : ∀ k, k < r → P.Adj (cyc hr0 c (2 * k + 1)) (cyc hr0 c (2 * k + 2)))
    (hq : ∀ p ∈ comparatorPairs r, P.Reachable (cyc hr0 c p.1) (cyc hr0 c p.2))
    (ht : P.Reachable (cyc hr0 c t) (cyc hr0 c 3))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ r) :
    P.Reachable (cyc hr0 c t) (cyc hr0 c (2 * k + 1)) := by
  have key : ∀ m, m + 2 ≤ r → P.Reachable (cyc hr0 c t) (cyc hr0 c (2 * (m + 1) + 1)) := by
    intro m
    induction m with
    | zero => intro _; exact ht
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      by_cases hm4 : m + 4 ≤ r
      · have hp : P.Reachable (cyc hr0 c (2 * (m + 1) + 1)) (cyc hr0 c (2 * (m + 1) + 4)) :=
          hq _ (mem_comparatorPairs.2 ⟨by omega, Or.inl ⟨m + 1, by omega, by omega, rfl⟩⟩)
        have h2 := (he (m + 2) (by omega)).reachable
        rw [show 2 * (m + 2) + 2 = 2 * (m + 1) + 4 by ring] at h2
        rw [show 2 * (m + 1 + 1) + 1 = 2 * (m + 2) + 1 by ring]
        exact h1.trans (hp.trans h2.symm)
      · have hlast : P.Reachable (cyc hr0 c (2 * r - 3)) (cyc hr0 c (2 * r - 1)) :=
          hq _ (mem_comparatorPairs.2 ⟨by omega, Or.inr rfl⟩)
        rw [show 2 * r - 3 = 2 * (m + 1) + 1 by omega,
          show 2 * r - 1 = 2 * (m + 1 + 1) + 1 by omega] at hlast
        exact h1.trans hlast
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact key m (by omega)

end Pairing

end Comparator

open Comparator

/-- **Lemma 3.5 (Even-cycle comparator).** Let `c₀ c₁ ⋯ c_{2r-1}` be an even cycle, `r ≥ 2`.
Take inputs `c₀, c₂` and outputs `c₁, c₃` (for `r = 2`) or `c₁, c₄` (for `r ≥ 3`), and pair
the remaining cycle vertices by (3.4). If `Q` is any system of vertex-disjoint paths (on a
vertex set `B` meeting the cycle exactly in the paired vertices) joining the pairs, then the
cycle together with `Q` is a comparator. -/
theorem even_cycle_comparator {V : Type*} [Finite V] (r : ℕ) (hr : 2 ≤ r)
    (c : Fin (2 * r) → V) (hc : Function.Injective c) (Q : SimpleGraph V) (B : Set V)
    (hQ : IsPathSystem Q B (comparatorPairEnds (by omega) c))
    (hpairs : ∀ p ∈ comparatorPairs r,
      Q.Reachable (cyc (by omega) c p.1) (cyc (by omega) c p.2))
    (hB : B ∩ Set.range c = comparatorPairEnds (by omega) c) :
    IsComparator (cycleOn c ⊔ Q) (Set.range c ∪ B) (cyc (by omega) c 0) (cyc (by omega) c 2)
      (cyc (by omega) c 1) (cyc (by omega) c (if r = 2 then 3 else 4)) := by
  have hr0 : 0 < r := by omega
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ, t = if r = 2 then 3 else 4 := ⟨_, rfl⟩
  rw [← ht_def]
  have ht : (r = 2 ∧ t = 3) ∨ (3 ≤ r ∧ t = 4) := by rw [ht_def]; split_ifs <;> omega
  have htr : t < 2 * r := by omega
  -- the two enumerations of the cycle used for `M₀` and `M₁`
  have hf0 : ∀ a < 2 * r, ∀ b < 2 * r, cyc hr0 c a = cyc hr0 c b → a = b := by
    intro a ha b hb h
    rwa [cyc_eq_iff hr0 hc, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have hf1 : ∀ a < 2 * r, ∀ b < 2 * r,
      (fun k => cyc hr0 c (k + 1)) a = (fun k => cyc hr0 c (k + 1)) b → a = b := by
    intro a ha b hb h
    simp only at h
    rw [cyc_eq_iff hr0 hc] at h
    rcases mod_cases (a + 1) (2 * r) (by omega) with h1 | h1 <;>
      rcases mod_cases (b + 1) (2 * r) (by omega) with h2 | h2 <;> omega
  have hCf0 : ∀ x ∈ Set.range c, ∃ i < 2 * r, cyc hr0 c i = x := by
    rintro _ ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, cyc_val hr0 j⟩
  have hCf1 : ∀ x ∈ Set.range c, ∃ i < 2 * r, (fun k => cyc hr0 c (k + 1)) i = x := by
    rintro _ ⟨j, rfl⟩
    refine ⟨if j.val = 0 then 2 * r - 1 else j.val - 1, by split_ifs <;> omega, ?_⟩
    simp only
    rw [← cyc_val hr0 (c := c) j, cyc_eq_iff hr0 hc, Nat.mod_eq_of_lt j.isLt]
    split_ifs with h
    · rw [show 2 * r - 1 + 1 = 2 * r by omega, Nat.mod_self, h]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  -- terminals are exactly the cycle vertices outside the pairing
  have hTE : ∀ x ∈ ({cyc hr0 c 0, cyc hr0 c 2, cyc hr0 c 1, cyc hr0 c t} : Set V),
      x ∈ Set.range c ∧ x ∉ comparatorPairEnds hr0 c := by
    intro x hx
    have : ∃ i, (i = 0 ∨ i = 2 ∨ i = 1 ∨ i = t) ∧ x = cyc hr0 c i := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h <;> exact ⟨_, by simp, h⟩
    obtain ⟨i, hi, rfl⟩ := this
    refine ⟨cyc_mem_range hr0 i, ?_⟩
    rintro ⟨p, hp, hpi⟩
    obtain ⟨hr3, hp1, hp1o, hp2, hp2r⟩ := pair_facts hp
    have hi' : i % (2 * r) = i := Nat.mod_eq_of_lt (by omega)
    simp only [cyc_eq_iff hr0 hc, hi', Nat.mod_eq_of_lt (show p.1 < 2 * r by omega),
      Nat.mod_eq_of_lt hp2r] at hpi
    omega
  have hcov : ∀ x ∈ Set.range c,
      x ∉ ({cyc hr0 c 0, cyc hr0 c 2, cyc hr0 c 1, cyc hr0 c t} : Set V) →
      x ∈ comparatorPairEnds hr0 c := by
    rintro _ ⟨j, rfl⟩ hjT
    rw [← cyc_val hr0 (c := c) j] at hjT ⊢
    have hj : j.val ≠ 0 ∧ j.val ≠ 2 ∧ j.val ≠ 1 ∧ j.val ≠ t := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> apply hjT <;> simp [h]
    have hjr := j.isLt
    have hr3 : 3 ≤ r := by omega
    rcases Nat.even_or_odd' j.val with ⟨m, hm | hm⟩
    · refine ⟨(2 * (m - 2) + 1, 2 * (m - 2) + 4),
        mem_comparatorPairs.2 ⟨hr3, Or.inl ⟨m - 2, by omega, by omega, rfl⟩⟩, Or.inr ?_⟩
      show cyc hr0 c j.val = cyc hr0 c (2 * (m - 2) + 4)
      congr 1; omega
    · by_cases hm' : m + 3 ≤ r
      · refine ⟨(2 * m + 1, 2 * m + 4),
          mem_comparatorPairs.2 ⟨hr3, Or.inl ⟨m, by omega, hm', rfl⟩⟩, Or.inl ?_⟩
        show cyc hr0 c j.val = cyc hr0 c (2 * m + 1)
        rw [hm]
      · refine ⟨(2 * r - 3, 2 * r - 1), mem_comparatorPairs.2 ⟨hr3, Or.inr rfl⟩, ?_⟩
        rcases (show j.val = 2 * r - 3 ∨ j.val = 2 * r - 1 by omega) with h | h
        · left
          show cyc hr0 c j.val = cyc hr0 c (2 * r - 3)
          rw [h]
        · right
          show cyc hr0 c j.val = cyc hr0 c (2 * r - 1)
          rw [h]
  -- `Q` shares no edge with `M₀` or `M₁`
  have hQf0 : ∀ i < 2 * r, ¬ Q.Adj (cyc hr0 c i) (cyc hr0 c (mate i)) :=
    fun i hi => no_Q_mate hr0 hc hQ hpairs hB 0 (by omega) hi
  have hQf1 : ∀ i < 2 * r, ¬ Q.Adj ((fun k => cyc hr0 c (k + 1)) i)
      ((fun k => cyc hr0 c (k + 1)) (mate i)) :=
    fun i hi => no_Q_mate hr0 hc hQ hpairs hB 1 le_rfl hi
  -- the first path system `M₀ ∪ Q`
  set P0 := matchG (cyc hr0 c) r ⊔ Q with hP0
  have he0 : ∀ k, k < r → P0.Adj (cyc hr0 c (2 * k)) (cyc hr0 c (2 * k + 1)) :=
    fun k hk => (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (matchG_adj hf0 hk))
  have hq0 : ∀ p ∈ comparatorPairs r, P0.Reachable (cyc hr0 c p.1) (cyc hr0 c p.2) :=
    fun p hp => (hpairs p hp).mono le_sup_right
  have R0 := fun k (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ r) => reach_M0 hr0 c P0 he0 hq0 hk1 hk2
  have hreach0 : ∀ x ∈ Set.range c, ∃ s ∈ ({cyc hr0 c 0, cyc hr0 c 2, cyc hr0 c 1,
      cyc hr0 c t} : Set V), P0.Reachable x s := by
    rintro _ ⟨j, rfl⟩
    rw [← cyc_val hr0 (c := c) j]
    have hjr := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 ∨ 2 ≤ j.val by omega) with h | h | h
    · exact ⟨cyc hr0 c j.val, by simp [h], SimpleGraph.Reachable.refl _⟩
    · refine ⟨cyc hr0 c 0, by simp, ?_⟩
      rw [h]; exact (he0 0 hr0).reachable.symm
    · refine ⟨cyc hr0 c 2, by simp, ?_⟩
      have h1 := R0 (j.val / 2) (by omega) (by omega)
      rcases Nat.even_or_odd' j.val with ⟨m, hm | hm⟩
      · rw [show j.val / 2 = m by omega, ← hm] at h1
        exact h1.symm
      · rw [show j.val / 2 = m by omega] at h1
        rw [hm]
        exact (h1.trans (he0 m (by omega)).reachable).symm
  -- the second path system `M₁ ∪ Q`
  set P1 := matchG (fun k => cyc hr0 c (k + 1)) r ⊔ Q with hP1
  have he1 : ∀ k, k < r → P1.Adj (cyc hr0 c (2 * k + 1)) (cyc hr0 c (2 * k + 2)) :=
    fun k hk => (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (matchG_adj hf1 hk))
  have hq1 : ∀ p ∈ comparatorPairs r, P1.Reachable (cyc hr0 c p.1) (cyc hr0 c p.2) :=
    fun p hp => (hpairs p hp).mono le_sup_right
  have ht3 : P1.Reachable (cyc hr0 c t) (cyc hr0 c 3) := by
    rcases ht with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]
    · rw [h]; exact (he1 1 (by omega)).reachable.symm
  have R1 := fun k (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ r) => reach_M1 hr0 c P1 t he1 hq1 ht3 hk1 hk2
  have hreach1 : ∀ x ∈ Set.range c, ∃ s ∈ ({cyc hr0 c 0, cyc hr0 c 2, cyc hr0 c 1,
      cyc hr0 c t} : Set V), P1.Reachable x s := by
    rintro _ ⟨j, rfl⟩
    rw [← cyc_val hr0 (c := c) j]
    have hjr := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ 3 ≤ j.val by omega) with h | h | h | h
    · exact ⟨cyc hr0 c j.val, by simp [h], SimpleGraph.Reachable.refl _⟩
    · exact ⟨cyc hr0 c j.val, by simp [h], SimpleGraph.Reachable.refl _⟩
    · refine ⟨cyc hr0 c 1, by simp, ?_⟩
      rw [h]; exact (he1 0 hr0).reachable.symm
    · refine ⟨cyc hr0 c t, by simp, ?_⟩
      have h1 := R1 ((j.val - 1) / 2) (by omega) (by omega)
      rcases Nat.even_or_odd' j.val with ⟨m, hm | hm⟩
      · rw [show (j.val - 1) / 2 = m - 1 by omega] at h1
        have h2 := (he1 (m - 1) (by omega)).reachable
        rw [show 2 * (m - 1) + 2 = j.val by omega] at h2
        exact (h1.trans h2).symm
      · rw [show 2 * ((j.val - 1) / 2) + 1 = j.val by omega] at h1
        exact h1.symm
  refine ⟨?_, ⟨P0, ?_, ?_, ?_, ?_⟩, ⟨P1, ?_, ?_, ?_, ?_⟩⟩
  · show List.Nodup ([0, 2, 1, t].map (cyc hr0 c))
    refine List.Nodup.map_on ?_ ?_
    · intro x hx y hy h
      simp at hx hy
      exact hf0 x (by omega) y (by omega) h
    · rcases ht with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  · exact sup_le_sup_right (matchG_le fun k _ => cycleOn_adj_cyc hr0 hr hc (2 * k)) Q
  · exact pathSystem_matching_sup (cyc hr0 c) hf0 (cyc_mem_range hr0) hCf0 hQ hB hQf0 hTE hcov
      hreach0
  · exact (he0 0 hr0).reachable
  · rcases ht with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact (he0 1 (by omega)).reachable
    · exact R0 2 (by omega) (by omega)
  · exact sup_le_sup_right (matchG_le fun k _ => cycleOn_adj_cyc hr0 hr hc (2 * k + 1)) Q
  · exact pathSystem_matching_sup (fun k => cyc hr0 c (k + 1)) hf1
      (fun k => cyc_mem_range hr0 _) hCf1 hQ hB hQf1 hTE hcov hreach1
  · have h1 := R1 (r - 1) (by omega) (by omega)
    have h2 := (he1 (r - 1) (by omega)).reachable
    have h3 : cyc hr0 c (2 * (r - 1) + 2) = cyc hr0 c 0 := by
      rw [cyc_eq_iff hr0 hc, show 2 * (r - 1) + 2 = 2 * r by omega, Nat.mod_self, Nat.zero_mod]
    rw [h3] at h2
    exact (h1.trans h2).symm
  · exact (he1 0 hr0).reachable.symm

end Lovasz
