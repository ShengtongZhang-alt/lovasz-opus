/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent)
-/
import Lovasz.Absorption.Basic

/-!
# `T3.2c`: the Hamilton router of Section 3.3

DAG node `T3.2c` of `docs/BLUEPRINT.md` (from Lemmas 3.4–3.7).

The wiring of the router is described on abstract *slots*: `Slot.inp k` and `Slot.out k` are
the terminals `I_k`, `O_k`, and `Slot.cy j i` is vertex `i` of the `j`-th cycle. The involution
`RouterStep.mt` sends each slot to the other end of the connection it needs (the fixed
connections of Lemma 3.6 and the pairing (3.4) of Lemma 3.5); `RouterStep.side` orients each
connection, and `RouterStep.kind` records whether it is internal to comparator `j`
(`some j`) or a fixed connection (`none`). All connections are realized at once by Lemma 3.4.
-/

universe u

namespace Lovasz

open Finset

namespace LocalAbsorption

namespace RouterStep

/-! ### Index arithmetic of one cycle -/

/-- The index of the second output of the comparator on a `2r`-cycle (Lemma 3.5). -/
def tIdx (r : ℕ) : ℕ := if r = 2 then 3 else 4

lemma tIdx_cases (r : ℕ) : (r = 2 ∧ tIdx r = 3) ∨ (r ≠ 2 ∧ tIdx r = 4) := by
  unfold tIdx; split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- The partner of a non-terminal index of a `2r`-cycle in the pairing (3.4). -/
def cm (r i : ℕ) : ℕ :=
  if i % 2 = 0 then i - 3 else if i + 5 ≤ 2 * r then i + 3
  else if i + 3 = 2 * r then 2 * r - 1 else 2 * r - 3

/-- The terminal indices `0, 1, 2, t` of a `2r`-cycle comparator. -/
abbrev IsTerm (r i : ℕ) : Prop := i = 0 ∨ i = 1 ∨ i = 2 ∨ i = tIdx r

/-- `cm r` is a fixed-point-free involution of the non-terminal indices. -/
lemma cm_spec {r i : ℕ} (hr : 2 ≤ r) (hi : i < 2 * r) (ht : ¬ IsTerm r i) :
    cm r i < 2 * r ∧ ¬ IsTerm r (cm r i) ∧ cm r (cm r i) = i ∧ cm r i ≠ i := by
  rcases tIdx_cases r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [IsTerm, h2] at ht <;>
    rw [IsTerm, h2] <;> unfold cm <;> split_ifs <;>
    (try simp only [false_or] at *) <;> omega

/-- The non-terminal indices are exactly the indices occurring in the pairing (3.4). -/
lemma nonterm_iff {r i : ℕ} (hr : 2 ≤ r) (hi : i < 2 * r) :
    ¬ IsTerm r i ↔ ∃ p ∈ comparatorPairs r, i = p.1 ∨ i = p.2 := by
  rw [IsTerm]
  constructor
  · intro ht
    rcases tIdx_cases r with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at ht; omega
    rw [h2] at ht
    have hr3 : 3 ≤ r := by omega
    rcases Nat.even_or_odd i with ⟨J, hJ⟩ | ⟨J, hJ⟩
    · -- even `i = 2J' + 4` with `J' ≥ 1`
      refine ⟨(2 * (J - 2) + 1, 2 * (J - 2) + 4), Comparator.mem_comparatorPairs.2
        ⟨hr3, Or.inl ⟨J - 2, by omega, by omega, rfl⟩⟩, Or.inr (by simp only; omega)⟩
    · by_cases hlast : i + 3 ≥ 2 * r
      · exact ⟨(2 * r - 3, 2 * r - 1), Comparator.mem_comparatorPairs.2 ⟨hr3, Or.inr rfl⟩,
          by simp only; omega⟩
      · exact ⟨(2 * J + 1, 2 * J + 4), Comparator.mem_comparatorPairs.2
          ⟨hr3, Or.inl ⟨J, by omega, by omega, rfl⟩⟩, Or.inl (by simp only; omega)⟩
  · rintro ⟨p, hp, hip⟩
    obtain ⟨hr3, ⟨J, hJ1, hJ2, rfl⟩ | rfl⟩ := Comparator.mem_comparatorPairs.1 hp <;>
      rcases tIdx_cases r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> simp only at hip <;> omega

/-- `cm` realizes the pairing (3.4). -/
lemma cm_pair {r : ℕ} {p : ℕ × ℕ} (hp : p ∈ comparatorPairs r) :
    cm r p.1 = p.2 ∧ ¬ IsTerm r p.1 ∧ p.1 < 2 * r ∧ p.2 < 2 * r := by
  obtain ⟨hr3, ⟨J, hJ1, hJ2, rfl⟩ | rfl⟩ := Comparator.mem_comparatorPairs.1 hp <;>
    rcases tIdx_cases r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [IsTerm, h2] <;> unfold cm <;>
    simp only <;> split_ifs <;> (try simp only [false_or, true_and] at *) <;> omega

lemma tIdx_ge (r : ℕ) : 3 ≤ tIdx r ∧ tIdx r ≤ 4 := by
  rcases tIdx_cases r with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

lemma tIdx_lt {r : ℕ} (hr : 2 ≤ r) : tIdx r < 2 * r := by
  rcases tIdx_cases r with ⟨h1, h⟩ | ⟨h1, h⟩ <;> omega

/-! ### Slots and the wiring involution -/

/-- A slot of the router: the terminals `I_k`, `O_k`, and vertex `i` of cycle `j`. -/
inductive Slot
  | inp (k : ℕ)
  | out (k : ℕ)
  | cy (j i : ℕ)
  deriving DecidableEq

variable (w : ℕ) (r : ℕ → ℕ)

/-- The other end of the connection at a slot: the fixed connections `I₀ – x₁(0)`,
`I_{j+1} – x₂(j)`, `y₂(j) – x₁(j+1)`, `y₁(j) – O_j`, `y₂(w-2) – O_{w-1}` of Lemma 3.6 (with
`x₁, x₂, y₁, y₂` the cycle vertices `0, 2, 1, t`), and the pairing (3.4) inside each cycle. -/
def mt : Slot → Slot
  | .inp k => if k = 0 then .cy 0 0 else .cy (k - 1) 2
  | .out k => if k + 1 < w then .cy k 1 else .cy (w - 2) (tIdx (r (w - 2)))
  | .cy j i =>
    if i = 0 then (if j = 0 then .inp 0 else .cy (j - 1) (tIdx (r (j - 1))))
    else if i = 1 then .out j
    else if i = 2 then .inp (j + 1)
    else if i = tIdx (r j) then (if j + 2 < w then .cy (j + 1) 0 else .out (w - 1))
    else .cy j (cm (r j) i)

/-- The slots in use: `w` inputs, `w` outputs, and the vertices of cycles `0, …, w - 2`. -/
def Valid : Slot → Prop
  | .inp k => k < w
  | .out k => k < w
  | .cy j i => j + 1 < w ∧ i < 2 * r j

/-- The orientation of the connections (`true` at exactly one end). -/
def side : Slot → Bool
  | .inp _ => false
  | .out _ => true
  | .cy j i => if i = 0 ∨ i = 2 then true else if i = 1 ∨ i = tIdx (r j) then false
      else decide (i < cm (r j) i)

/-- `some j` for the connections internal to comparator `j`, `none` for fixed connections. -/
def kind : Slot → Option ℕ
  | .inp _ => none
  | .out _ => none
  | .cy j i => if IsTerm (r j) i then none else some j

variable {w r}

/-- `mt` is an involution of the valid slots that reverses `side` and preserves `kind`. -/
lemma mt_spec (hw : 2 ≤ w) (hr : ∀ j, j + 1 < w → 2 ≤ r j) {s : Slot} (hs : Valid w r s) :
    Valid w r (mt w r s) ∧ mt w r (mt w r s) = s ∧ side r (mt w r s) = !side r s ∧
      kind r (mt w r s) = kind r s := by
  cases s with
  | inp k =>
    simp only [Valid] at hs
    by_cases hk : k = 0
    · subst hk
      have h0 := hr 0 (by omega)
      simp [mt, Valid, side, kind, IsTerm]
      omega
    · have h1 := hr (k - 1) (by omega)
      have e : k - 1 + 1 = k := by omega
      simp [mt, hk, Valid, side, kind, IsTerm, e]
      omega
  | out k =>
    simp only [Valid] at hs
    by_cases hk : k + 1 < w
    · have h1 := hr k hk
      simp [mt, hk, Valid, side, kind, IsTerm]
      omega
    · have hk' : k = w - 1 := by omega
      subst hk'
      have h1 := hr (w - 2) (by omega)
      have ht := tIdx_ge (r (w - 2))
      have ht' := tIdx_lt h1
      have e : ¬ (w - 2 + 2 < w) := by omega
      simp [mt, hk, Valid, side, kind, IsTerm, e, show tIdx (r (w - 2)) ≠ 0 by omega,
        show tIdx (r (w - 2)) ≠ 1 by omega, show tIdx (r (w - 2)) ≠ 2 by omega]
      omega
  | cy j i =>
    obtain ⟨hj, hi⟩ := hs
    have hrj := hr j hj
    have ht := tIdx_ge (r j)
    by_cases h0 : i = 0
    · subst h0
      by_cases hj0 : j = 0
      · subst hj0
        simp [mt, Valid, side, kind, IsTerm]
        omega
      · have hr' := hr (j - 1) (by omega)
        have ht' := tIdx_ge (r (j - 1))
        have ht'' := tIdx_lt hr'
        have e : j - 1 + 1 = j := by omega
        have e2 : j - 1 + 2 < w := by omega
        simp [mt, hj0, Valid, side, kind, IsTerm, e, e2, show tIdx (r (j - 1)) ≠ 0 by omega,
          show tIdx (r (j - 1)) ≠ 1 by omega, show tIdx (r (j - 1)) ≠ 2 by omega]
        omega
    by_cases h1 : i = 1
    · subst h1
      simp [mt, Valid, side, kind, IsTerm, hj]
      omega
    by_cases h2 : i = 2
    · subst h2
      simp [mt, Valid, side, kind, IsTerm]
      omega
    by_cases h3 : i = tIdx (r j)
    · subst h3
      have n0 : tIdx (r j) ≠ 0 := by omega
      have n1 : tIdx (r j) ≠ 1 := by omega
      have n2 : tIdx (r j) ≠ 2 := by omega
      by_cases hj2 : j + 2 < w
      · have hr' := hr (j + 1) hj2
        simp [mt, n0, n1, n2, hj2, Valid, side, kind, IsTerm]
        omega
      · have e : w - 2 = j := by omega
        have e' : w - 1 = j + 1 := by omega
        simp [mt, n0, n1, n2, hj2, Valid, side, kind, IsTerm, e, e']
        omega
    · have hnt : ¬ IsTerm (r j) i := by
        simp only [IsTerm, not_or]; exact ⟨h0, h1, h2, h3⟩
      obtain ⟨c1, c2, c3, c4⟩ := cm_spec hrj hi hnt
      simp only [IsTerm, not_or] at c2
      obtain ⟨d0, d1, d2, d3⟩ := c2
      simp [mt, h0, h1, h2, h3, d0, d1, d2, d3, c3, Valid, side, kind, IsTerm, hj, c1]
      rcases Nat.lt_or_gt_of_ne c4 with h | h <;> simp [h, Nat.lt_asymm h]

lemma kind_cy_of_not {r : ℕ → ℕ} {j i : ℕ} (h : ¬ IsTerm (r j) i) : kind r (.cy j i) = some j :=
  ite_eq_right h

lemma kind_cy_of_term {r : ℕ → ℕ} {j i : ℕ} (h : IsTerm (r j) i) : kind r (.cy j i) = none :=
  ite_eq_left h

lemma kind_eq_some {r : ℕ → ℕ} {x : Slot} {j : ℕ} (h : kind r x = some j) :
    ∃ i, x = .cy j i ∧ ¬ IsTerm (r j) i := by
  cases x with
  | inp k => exact absurd h (by simp [kind])
  | out k => exact absurd h (by simp [kind])
  | cy j' i =>
    by_cases h' : IsTerm (r j') i
    · rw [kind_cy_of_term h'] at h; exact absurd h (by simp)
    · rw [kind_cy_of_not h'] at h
      obtain rfl := Option.some.inj h
      exact ⟨i, rfl, h'⟩

lemma mt_inp_zero : mt w r (.inp 0) = .cy 0 0 := by simp [mt]

lemma mt_inp_pos {k : ℕ} (hk : k ≠ 0) : mt w r (.inp k) = .cy (k - 1) 2 := by simp [mt, hk]

lemma mt_cy_one {j : ℕ} : mt w r (.cy j 1) = .out j := by simp [mt]

lemma mt_cy_t {j : ℕ} :
    mt w r (.cy j (tIdx (r j))) = if j + 2 < w then .cy (j + 1) 0 else .out (w - 1) := by
  have := tIdx_ge (r j)
  simp [mt, show tIdx (r j) ≠ 0 by omega, show tIdx (r j) ≠ 1 by omega,
    show tIdx (r j) ≠ 2 by omega]

lemma mt_cy_of_not {j i : ℕ} (h : ¬ IsTerm (r j) i) : mt w r (.cy j i) = .cy j (cm (r j) i) := by
  simp only [IsTerm, not_or] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp [mt, h0, h1, h2, h3]

/-! ### Vertices of the slots -/

section Assembly

variable {V : Type*}

/-- The vertex at a slot. -/
def vt (Ie Oe : ℕ → V) (cf : ℕ → ℕ → V) : Slot → V
  | .inp k => Ie k
  | .out k => Oe k
  | .cy j i => cf j i

/-- The finite set of slots in use. -/
def validSet (w : ℕ) (r : ℕ → ℕ) : Finset Slot :=
  (range w).image Slot.inp ∪ (range w).image Slot.out ∪
    (range (w - 1)).biUnion fun j => (range (2 * r j)).image (Slot.cy j)

lemma mem_validSet {s : Slot} : s ∈ validSet w r ↔ Valid w r s := by
  cases s with
  | inp k => simp [validSet, Valid]
  | out k => simp [validSet, Valid]
  | cy j i => simp [validSet, Valid]; omega

/-- One slot for each connection. -/
def goodSet (w : ℕ) (r : ℕ → ℕ) : Finset Slot := (validSet w r).filter fun s => side r s = true

lemma mem_goodSet {s : Slot} : s ∈ goodSet w r ↔ Valid w r s ∧ side r s = true := by
  simp [goodSet, mem_validSet]

/-- The data of the router: `w - 1` disjoint even cycles `cf j` of length `2 r j` in `C`, and
enumerations `Ie`, `Oe` of `I`, `O`. -/
structure Data (G : SimpleGraph V) (C I O : Finset V) (w : ℕ) (r : ℕ → ℕ) (Ie Oe : ℕ → V)
    (cf : ℕ → ℕ → V) : Prop where
  two_le : 2 ≤ w
  r_ge : ∀ j, j + 1 < w → 2 ≤ r j
  cf_mem : ∀ j i, j + 1 < w → i < 2 * r j → cf j i ∈ C
  cf_adj : ∀ j i, j + 1 < w → i < 2 * r j → G.Adj (cf j i) (cf j ((i + 1) % (2 * r j)))
  cf_inj : ∀ j i j' i', j + 1 < w → i < 2 * r j → j' + 1 < w → i' < 2 * r j' →
    cf j i = cf j' i' → j = j' ∧ i = i'
  Ie_mem : ∀ k < w, Ie k ∈ I
  Oe_mem : ∀ k < w, Oe k ∈ O
  Ie_inj : ∀ k < w, ∀ k' < w, Ie k = Ie k' → k = k'
  Oe_inj : ∀ k < w, ∀ k' < w, Oe k = Oe k' → k = k'
  Ie_surj : ∀ v ∈ I, ∃ k < w, Ie k = v
  Oe_surj : ∀ v ∈ O, ∃ k < w, Oe k = v
  disj_CI : Disjoint C I
  disj_CO : Disjoint C O
  disj_IO : Disjoint I O

namespace Data

variable {G : SimpleGraph V} {C I O : Finset V} {Ie Oe : ℕ → V} {cf : ℕ → ℕ → V}

lemma vt_mem [DecidableEq V] (hD : Data G C I O w r Ie Oe cf) {s : Slot} (hs : Valid w r s) :
    vt Ie Oe cf s ∈ C ∪ I ∪ O := by
  cases s with
  | inp k => exact mem_union_left _ (mem_union_right _ (hD.Ie_mem k hs))
  | out k => exact mem_union_right _ (hD.Oe_mem k hs)
  | cy j i => exact mem_union_left _ (mem_union_left _ (hD.cf_mem j i hs.1 hs.2))

lemma vt_inj (hD : Data G C I O w r Ie Oe cf) {s s' : Slot} (hs : Valid w r s)
    (hs' : Valid w r s') (h : vt Ie Oe cf s = vt Ie Oe cf s') : s = s' := by
  have hIO := disjoint_left.1 hD.disj_IO
  have hCI := disjoint_left.1 hD.disj_CI
  have hCO := disjoint_left.1 hD.disj_CO
  cases s <;> cases s' <;> simp only [vt, Valid] at h hs hs'
  · rw [hD.Ie_inj _ hs _ hs' h]
  · have h1 := hD.Ie_mem _ hs; rw [h] at h1; exact (hIO h1 (hD.Oe_mem _ hs')).elim
  · have h1 := hD.Ie_mem _ hs; rw [h] at h1; exact (hCI (hD.cf_mem _ _ hs'.1 hs'.2) h1).elim
  · have h1 := hD.Oe_mem _ hs; rw [h] at h1; exact (hIO (hD.Ie_mem _ hs') h1).elim
  · rw [hD.Oe_inj _ hs _ hs' h]
  · have h1 := hD.Oe_mem _ hs; rw [h] at h1; exact (hCO (hD.cf_mem _ _ hs'.1 hs'.2) h1).elim
  · have h1 := hD.cf_mem _ _ hs.1 hs.2; rw [h] at h1; exact (hCI h1 (hD.Ie_mem _ hs')).elim
  · have h1 := hD.cf_mem _ _ hs.1 hs.2; rw [h] at h1; exact (hCO h1 (hD.Oe_mem _ hs')).elim
  · obtain ⟨rfl, rfl⟩ := hD.cf_inj _ _ _ _ hs.1 hs.2 hs'.1 hs'.2 h
    rfl

/-- The chosen end of a connection and its other end are valid slots. -/
lemma good (hD : Data G C I O w r Ie Oe cf) (s : goodSet w r) :
    Valid w r s.1 ∧ side r s.1 = true ∧ Valid w r (mt w r s.1) := by
  obtain ⟨h1, h2⟩ := mem_goodSet.1 s.2
  exact ⟨h1, h2, (mt_spec hD.two_le hD.r_ge h1).1⟩

/-- Distinct connections have distinct ends. -/
lemma ends_inj (hD : Data G C I O w r Ie Oe cf) (s s' : goodSet w r) (x y : Slot)
    (hx : x = s.1 ∨ x = mt w r s.1) (hy : y = s'.1 ∨ y = mt w r s'.1)
    (hxy : vt Ie Oe cf x = vt Ie Oe cf y) : s = s' := by
  obtain ⟨hs, hss, hms⟩ := hD.good s
  obtain ⟨hs', hss', hms'⟩ := hD.good s'
  have hmt := mt_spec hD.two_le hD.r_ge hs
  have hmt' := mt_spec hD.two_le hD.r_ge hs'
  have hxv : Valid w r x := by rcases hx with rfl | rfl; exacts [hs, hms]
  have hyv : Valid w r y := by rcases hy with rfl | rfl; exacts [hs', hms']
  obtain rfl := hD.vt_inj hxv hyv hxy
  rcases hx with rfl | rfl <;> rcases hy with h | h
  · exact Subtype.ext h
  · have := hmt'.2.2.1; rw [← h, hss, hss'] at this; simp at this
  · have := hmt.2.2.1; rw [h, hss, hss'] at this; simp at this
  · have := hmt.2.1; rw [h, hmt'.2.1] at this; exact Subtype.ext this.symm

/-- The two ends of a connection are distinct vertices. -/
lemma ends_ne (hD : Data G C I O w r Ie Oe cf) (s : goodSet w r) :
    vt Ie Oe cf s.1 ≠ vt Ie Oe cf (mt w r s.1) := by
  intro h
  obtain ⟨hs, hss, hms⟩ := hD.good s
  have e := hD.vt_inj hs hms h
  have := (mt_spec hD.two_le hD.r_ge hs).2.2.1
  rw [← e, hss] at this
  simp at this

end Data

lemma val_finRotate {n : ℕ} (i : Fin n) : ((finRotate n i : Fin n) : ℕ) = (i + 1) % n := by
  have : NeZero n := i.neZero
  rw [finRotate_apply, Fin.val_add]
  simp [Nat.add_mod]

/-- The cycle `c` is a subgraph of `G` if consecutive vertices are adjacent in `G`. -/
lemma cycleOn_le {G : SimpleGraph V} {n : ℕ} (c : Fin n → V) (f : ℕ → V)
    (hcf : ∀ i : Fin n, c i = f i) (h : ∀ i < n, G.Adj (f i) (f ((i + 1) % n))) :
    cycleOn c ≤ G := by
  intro u v huv
  rw [cycleOn, SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨i, hi⟩, -⟩ := huv
  have hadj := h i i.2
  rw [← hcf, ← val_finRotate, ← hcf] at hadj
  rcases Sym2.eq_iff.1 hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · exact hadj.symm

/-- **Assembly of the router.** Given the cycles and enumerations `hD`, and one path `p s` of
`G` for each connection `s`, with interiors in `Q` and pairwise disjoint there, the cycles with
their internal connections are comparators (Lemma 3.5), and together with the fixed connections
they form an `I, O`-Hamilton router (Lemma 3.6). -/
theorem assemble [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C Q I O : Finset V} {w : ℕ}
    {r : ℕ → ℕ} {Ie Oe : ℕ → V} {cf : ℕ → ℕ → V} (hD : Data G C I O w r Ie Oe cf)
    (hCQ : Disjoint C Q) (hIQ : Disjoint I Q) (hOQ : Disjoint O Q)
    (p : ∀ s : goodSet w r, G.Walk (vt Ie Oe cf s) (vt Ie Oe cf (mt w r s)))
    (hp : ∀ s, (p s).IsPath)
    (hint : ∀ s, ∀ z ∈ (p s).support, z ≠ vt Ie Oe cf s → z ≠ vt Ie Oe cf (mt w r s) → z ∈ Q)
    (hdisj : ∀ s s', s ≠ s' → ∀ z ∈ Q, z ∈ (p s).support → z ∉ (p s').support) :
    ∃ A : Finset V, I ∪ O ⊆ A ∧ A ⊆ C ∪ Q ∪ I ∪ O ∧ IsHamRouter G ↑A ↑I ↑O := by
  classical
  have hw := hD.two_le
  have hr := hD.r_ge
  let f := vt Ie Oe cf
  have hmt : ∀ {x}, Valid w r x → _ := fun {x} (hx : Valid w r x) => mt_spec hw hr hx
  have hfQ : ∀ x, Valid w r x → f x ∉ Q := by
    intro x hx hxQ
    rcases mem_union.1 (hD.vt_mem hx) with h | h
    · rcases mem_union.1 h with h | h
      · exact disjoint_left.1 hCQ h hxQ
      · exact disjoint_left.1 hIQ h hxQ
    · exact disjoint_left.1 hOQ h hxQ
  have hsupp : ∀ s : goodSet w r, ∀ z ∈ (p s).support,
      z = f s.1 ∨ z = f (mt w r s.1) ∨ z ∈ Q := by
    intro s z hz
    by_cases h1 : z = f s.1
    · exact Or.inl h1
    by_cases h2 : z = f (mt w r s.1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hint s z hz h1 h2))
  have hsupp' : ∀ s : goodSet w r, ∀ z ∈ (p s).support,
      z ∈ Q ∨ ∃ x, (x = s.1 ∨ x = mt w r s.1) ∧ z = f x ∧ Valid w r x := by
    intro s z hz
    obtain ⟨hs, -, hms⟩ := hD.good s
    rcases hsupp s z hz with h | h | h
    · exact Or.inr ⟨_, Or.inl rfl, h, hs⟩
    · exact Or.inr ⟨_, Or.inr rfl, h, hms⟩
    · exact Or.inl h
  have hsdisj : ∀ s s' : goodSet w r, s ≠ s' → ∀ z ∈ (p s).support, z ∉ (p s').support := by
    intro s s' hne z hz hz'
    rcases hsupp' s z hz with h | ⟨x, hx, rfl, hxv⟩
    · exact hdisj s s' hne z h hz hz'
    · rcases hsupp' s' _ hz' with h' | ⟨y, hy, hxy, -⟩
      · exact hfQ x hxv h'
      · exact hne (hD.ends_inj s s' x y hx hy hxy)
  -- the connections of each kind form a path system
  let κ : Option ℕ → Type := fun k => {s : goodSet w r // kind r s.1 = k}
  let Qk : Option ℕ → SimpleGraph V := fun k =>
    SimpleGraph.fromEdgeSet {e | ∃ s : κ k, e ∈ (p s.1).edges}
  let Bk : Option ℕ → Set V := fun k => {v | ∃ s : κ k, v ∈ (p s.1).support}
  let Tk : Option ℕ → Set V := fun k => {v | ∃ s : κ k, v = f s.1.1 ∨ v = f (mt w r s.1.1)}
  have hPS : ∀ k, Qk k ≤ G ∧ IsPathSystem (Qk k) (Bk k) (Tk k) ∧
      ∀ s : κ k, ∀ v ∈ (p s.1).support, (Qk k).Reachable v (f s.1.1) := fun k =>
    pathSystem_of_paths (fun s : κ k => f s.1.1) (fun s => f (mt w r s.1.1)) (fun s => p s.1)
      (fun s => hp s.1) (fun s => hD.ends_ne s.1)
      (fun s s' h => hsdisj s.1 s'.1 (fun h' => h (Subtype.ext h')))
  have hconn : ∀ x, Valid w r x → (Qk (kind r x)).Reachable (f x) (f (mt w r x)) := by
    intro x hx
    by_cases hsx : side r x = true
    · let s : κ (kind r x) := ⟨⟨x, mem_goodSet.2 ⟨hx, hsx⟩⟩, rfl⟩
      exact ((hPS _).2.2 s _ (p s.1).end_mem_support).symm
    · have hy := hmt hx
      have hsy : side r (mt w r x) = true := by rw [hy.2.2.1]; simpa using hsx
      let s : κ (kind r x) := ⟨⟨mt w r x, mem_goodSet.2 ⟨hy.1, hsy⟩⟩, hy.2.2.2⟩
      have h2 : (Qk (kind r x)).Reachable (f (mt w r (mt w r x))) (f (mt w r x)) :=
        (hPS _).2.2 s _ (p s.1).end_mem_support
      rwa [hy.2.1] at h2
  have hT : ∀ k v, v ∈ Tk k ↔ ∃ x, Valid w r x ∧ kind r x = k ∧ f x = v := by
    intro k v
    constructor
    · rintro ⟨s, hv | hv⟩
      · exact ⟨s.1.1, (hD.good s.1).1, s.2, hv.symm⟩
      · have hy := hmt (hD.good s.1).1
        exact ⟨mt w r s.1.1, hy.1, hy.2.2.2.trans s.2, hv.symm⟩
    · rintro ⟨x, hx, hk, rfl⟩
      by_cases hsx : side r x = true
      · exact ⟨⟨⟨x, mem_goodSet.2 ⟨hx, hsx⟩⟩, hk⟩, Or.inl rfl⟩
      · have hy := hmt hx
        have hsy : side r (mt w r x) = true := by rw [hy.2.2.1]; simpa using hsx
        exact ⟨⟨⟨mt w r x, mem_goodSet.2 ⟨hy.1, hsy⟩⟩, hy.2.2.2.trans hk⟩,
          Or.inr (by simp only [hy.2.1])⟩
  have hBsub : ∀ k v, v ∈ Bk k → v ∈ Tk k ∨ v ∈ Q := by
    rintro k v ⟨s, hv⟩
    rcases hsupp s.1 v hv with h | h | h
    · exact Or.inl ⟨s, Or.inl h⟩
    · exact Or.inl ⟨s, Or.inr h⟩
    · exact Or.inr h
  have hTB : ∀ k, Tk k ⊆ Bk k := fun k => (hPS k).2.1.subset
  have hBdisj : ∀ k k', k ≠ k' → ∀ v ∈ Bk k, v ∉ Bk k' := by
    rintro k k' hkk v ⟨s, hs⟩ ⟨s', hs'⟩
    refine hsdisj s.1 s'.1 (fun h => hkk ?_) v hs hs'
    rw [← s.2, ← s'.2, h]
  have hBC : ∀ k v, v ∈ Bk k → v ∈ C → v ∈ Tk k := by
    intro k v hv hvC
    rcases hBsub k v hv with h | h
    · exact h
    · exact absurd h (disjoint_left.1 hCQ hvC)
  have hTcy : ∀ j v, v ∈ Tk (some j) → ∃ i < 2 * r j, cf j i = v ∧ j + 1 < w := by
    intro j v hv
    obtain ⟨x, hx, hk, rfl⟩ := (hT _ _).1 hv
    obtain ⟨i, rfl, -⟩ := kind_eq_some hk
    exact ⟨i, hx.2, rfl, hx.1⟩
  -- the comparators
  let cfin : ∀ j, Fin (2 * r j) → V := fun j i => cf j i
  have hcfin_inj : ∀ j, j + 1 < w → Function.Injective (cfin j) := fun j hj a b h =>
    Fin.ext (hD.cf_inj j a j b hj a.2 hj b.2 h).2
  have hcyc : ∀ j (h0 : 0 < r j) k, k < 2 * r j → cyc h0 (cfin j) k = cf j k := by
    intro j h0 k hk
    simp only [cyc, cfin, Nat.mod_eq_of_lt hk]
  have hends : ∀ j, j + 1 < w → ∀ (h0 : 0 < r j),
      comparatorPairEnds h0 (cfin j) = Tk (some j) := by
    intro j hj h0
    ext v
    rw [hT]
    simp only [comparatorPairEnds, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, hv⟩
      obtain ⟨c1, c2, c3, c4⟩ := cm_pair hq
      rcases hv with rfl | rfl
      · exact ⟨.cy j q.1, ⟨hj, c3⟩, kind_cy_of_not c2, (hcyc j h0 _ c3).symm⟩
      · have hnt : ¬ IsTerm (r j) q.2 :=
          (nonterm_iff (hr j hj) c4).2 ⟨q, hq, Or.inr rfl⟩
        exact ⟨.cy j q.2, ⟨hj, c4⟩, kind_cy_of_not hnt, (hcyc j h0 _ c4).symm⟩
    · rintro ⟨x, hx, hk, rfl⟩
      obtain ⟨i, rfl, hi⟩ := kind_eq_some hk
      obtain ⟨q, hq, hiq⟩ := (nonterm_iff (hr j hj) hx.2).1 hi
      obtain ⟨c1, c2, c3, c4⟩ := cm_pair hq
      refine ⟨q, hq, ?_⟩
      rcases hiq with rfl | rfl
      · exact Or.inl (hcyc j h0 _ c3).symm
      · exact Or.inr (hcyc j h0 _ c4).symm
  have hpairs : ∀ j, j + 1 < w → ∀ (h0 : 0 < r j), ∀ q ∈ comparatorPairs (r j),
      (Qk (some j)).Reachable (cyc h0 (cfin j) q.1) (cyc h0 (cfin j) q.2) := by
    intro j hj h0 q hq
    obtain ⟨c1, c2, c3, c4⟩ := cm_pair hq
    rw [hcyc j h0 _ c3, hcyc j h0 _ c4]
    have := hconn (.cy j q.1) ⟨hj, c3⟩
    rw [kind_cy_of_not c2, mt_cy_of_not c2, c1] at this
    exact this
  have hBint : ∀ j, j + 1 < w → ∀ (h0 : 0 < r j),
      Bk (some j) ∩ Set.range (cfin j) = comparatorPairEnds h0 (cfin j) := by
    intro j hj h0
    rw [hends j hj h0]
    ext v
    constructor
    · rintro ⟨hv, i, rfl⟩
      exact hBC _ _ hv (hD.cf_mem j i hj i.2)
    · intro hv
      refine ⟨hTB _ hv, ?_⟩
      obtain ⟨x, hx, hk, rfl⟩ := (hT _ _).1 hv
      obtain ⟨i, rfl, -⟩ := kind_eq_some hk
      exact ⟨⟨i, hx.2⟩, rfl⟩
  have hcomp : ∀ j < w - 1, IsComparator (cycleOn (cfin j) ⊔ Qk (some j))
      (Set.range (cfin j) ∪ Bk (some j)) (cf j 0) (cf j 2) (cf j 1) (cf j (tIdx (r j))) := by
    intro j hj
    have hj' : j + 1 < w := by omega
    have hrj := hr j hj'
    have h0 : 0 < r j := by omega
    have H := even_cycle_comparator (r j) hrj (cfin j) (hcfin_inj j hj') (Qk (some j))
      (Bk (some j)) (by rw [hends j hj' h0]; exact (hPS _).2.1) (hpairs j hj' h0)
      (hBint j hj' h0)
    have ht : (if r j = 2 then 3 else 4) < 2 * r j := tIdx_lt hrj
    rw [hcyc j _ 0 (by omega), hcyc j _ 2 (by omega), hcyc j _ 1 (by omega),
      hcyc j _ _ ht] at H
    exact H
  -- the hypotheses of Lemma 3.6
  have hAdisj : ∀ j < w - 1, ∀ j' < w - 1, j ≠ j' →
      Disjoint (Set.range (cfin j) ∪ Bk (some j)) (Set.range (cfin j') ∪ Bk (some j')) := by
    have key : ∀ j j', j < w - 1 → j' < w - 1 → j ≠ j' → ∀ v ∈ Set.range (cfin j),
        v ∉ Set.range (cfin j') ∪ Bk (some j') := by
      rintro j j' hj hj' hne v ⟨i, rfl⟩ hv'
      rcases hv' with ⟨i', hi'⟩ | hv'
      · exact hne (hD.cf_inj j i j' i' (by omega) i.2 (by omega) i'.2 hi'.symm).1
      · obtain ⟨i', hi', he, -⟩ := hTcy j' _ (hBC _ _ hv' (hD.cf_mem j i (by omega) i.2))
        exact hne (hD.cf_inj j i j' i' (by omega) i.2 (by omega) hi' he.symm).1
    intro j hj j' hj' hne
    rw [Set.disjoint_left]
    intro v hv hv'
    rcases hv with hv | hv
    · exact key j j' hj hj' hne v hv hv'
    · rcases hv' with hv' | hv'
      · exact key j' j hj' hj (Ne.symm hne) v hv' (Or.inr hv)
      · exact hBdisj _ _ (by simpa using hne) v hv hv'
  have hIinj : Set.InjOn Ie (Set.Iio w) := fun k hk k' hk' h => hD.Ie_inj k hk k' hk' h
  have hOinj : Set.InjOn Oe (Set.Iio w) := fun k hk k' hk' h => hD.Oe_inj k hk k' hk' h
  have hIO : ∀ k < w, ∀ k' < w, Ie k ≠ Oe k' := fun k hk k' hk' h =>
    disjoint_left.1 hD.disj_IO (hD.Ie_mem k hk) (h ▸ hD.Oe_mem k' hk')
  have hIOA : ∀ k < w, ∀ j < w - 1, Ie k ∉ Set.range (cfin j) ∪ Bk (some j) ∧
      Oe k ∉ Set.range (cfin j) ∪ Bk (some j) := by
    have key : ∀ v, v ∉ C → v ∉ Q → ∀ j < w - 1, v ∉ Set.range (cfin j) ∪ Bk (some j) := by
      intro v hvC hvQ j hj hv
      rcases hv with ⟨i, rfl⟩ | hv
      · exact hvC (hD.cf_mem j i (by omega) i.2)
      · rcases hBsub _ v hv with h | h
        · obtain ⟨i, hi, rfl, hj'⟩ := hTcy j v h
          exact hvC (hD.cf_mem j i hj' hi)
        · exact hvQ h
    intro k hk j hj
    exact ⟨key _ (fun h => disjoint_left.1 hD.disj_CI h (hD.Ie_mem k hk))
        (disjoint_left.1 hIQ (hD.Ie_mem k hk)) j hj,
      key _ (fun h => disjoint_left.1 hD.disj_CO h (hD.Oe_mem k hk))
        (disjoint_left.1 hOQ (hD.Oe_mem k hk)) j hj⟩
  have hTnone : Tk none = Ie '' Set.Iio w ∪ Oe '' Set.Iio w ∪
      ⋃ j ∈ Set.Iio (w - 1), ({cf j 0, cf j 2, cf j 1, cf j (tIdx (r j))} : Set V) := by
    ext v
    rw [hT]
    constructor
    · rintro ⟨x, hx, hk, rfl⟩
      cases x with
      | inp k => exact Or.inl (Or.inl ⟨k, hx, rfl⟩)
      | out k => exact Or.inl (Or.inr ⟨k, hx, rfl⟩)
      | cy j i =>
        have hi : IsTerm (r j) i := by
          by_contra h
          rw [kind_cy_of_not h] at hk
          exact absurd hk (by simp)
        have hj : j ∈ Set.Iio (w - 1) := by simp only [Set.mem_Iio]; have := hx.1; omega
        refine Or.inr (Set.mem_biUnion (x := j) hj ?_)
        rcases hi with rfl | rfl | rfl | rfl <;> simp [f, vt]
    · rintro ((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | hv)
      · exact ⟨.inp k, hk, rfl, rfl⟩
      · exact ⟨.out k, hk, rfl, rfl⟩
      · obtain ⟨j, hj, hv⟩ := Set.mem_iUnion₂.1 hv
        have hj' : j + 1 < w := by simp only [Set.mem_Iio] at hj; omega
        have hrj := hr j hj'
        have ht := tIdx_lt hrj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact ⟨.cy j 0, ⟨hj', by omega⟩, kind_cy_of_term (Or.inl rfl), rfl⟩
        · exact ⟨.cy j 2, ⟨hj', by omega⟩, kind_cy_of_term (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
        · exact ⟨.cy j 1, ⟨hj', by omega⟩, kind_cy_of_term (Or.inr (Or.inl rfl)), rfl⟩
        · exact ⟨.cy j (tIdx (r j)), ⟨hj', ht⟩,
            kind_cy_of_term (Or.inr (Or.inr (Or.inr rfl))), rfl⟩
  have hBA : ∀ j < w - 1, Bk none ∩ (Set.range (cfin j) ∪ Bk (some j)) =
      ({cf j 0, cf j 2, cf j 1, cf j (tIdx (r j))} : Set V) := by
    intro j hj
    have hj' : j + 1 < w := by omega
    have hrj := hr j hj'
    have ht := tIdx_lt hrj
    ext v
    constructor
    · rintro ⟨hv, ⟨i, rfl⟩ | hv'⟩
      · have hT' := hBC _ _ hv (hD.cf_mem j i hj' i.2)
        obtain ⟨x, hx, hk, hxv⟩ := (hT _ _).1 hT'
        have e := hD.vt_inj hx (show Valid w r (.cy j i) from ⟨hj', i.2⟩) hxv
        subst e
        have hi : IsTerm (r j) i := by
          by_contra h
          rw [kind_cy_of_not h] at hk
          exact absurd hk (by simp)
        show cf j i ∈ _
        rcases hi with h | h | h | h <;> rw [h] <;> simp
      · exact absurd hv' (hBdisj none (some j) (by simp) v hv)
    · intro hv
      have hv' : v ∈ Tk none := by
        rw [hTnone]; exact Or.inr (Set.mem_biUnion (x := j) (by simpa using hj) hv)
      refine ⟨hTB _ hv', Or.inl ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, rfl⟩
      · exact ⟨⟨2, by omega⟩, rfl⟩
      · exact ⟨⟨1, by omega⟩, rfl⟩
      · exact ⟨⟨tIdx (r j), ht⟩, rfl⟩
  have hc₁ : (Qk none).Reachable (Ie 0) (cf 0 0) := by
    have := hconn (.inp 0) (show 0 < w by omega)
    rwa [mt_inp_zero] at this
  have hc₂ : (Qk none).Reachable (Ie 1) (cf 0 2) := by
    have := hconn (.inp 1) (show 1 < w by omega)
    rwa [mt_inp_pos one_ne_zero] at this
  have hc₃ : ∀ j, j + 2 < w → (Qk none).Reachable (cf j (tIdx (r j))) (cf (j + 1) 0) ∧
      (Qk none).Reachable (Ie (j + 2)) (cf (j + 1) 2) := by
    intro j hj
    have hrj := hr j (by omega)
    constructor
    · have := hconn (.cy j (tIdx (r j))) ⟨by omega, tIdx_lt hrj⟩
      rwa [kind_cy_of_term (Or.inr (Or.inr (Or.inr rfl))), mt_cy_t, ite_eq_left hj] at this
    · have := hconn (.inp (j + 2)) (show j + 2 < w from hj)
      rwa [mt_inp_pos (by omega), show j + 2 - 1 = j + 1 by omega] at this
  have hc₄ : ∀ j < w - 1, (Qk none).Reachable (cf j 1) (Oe j) := by
    intro j hj
    have hrj := hr j (by omega)
    have := hconn (.cy j 1) ⟨by omega, by omega⟩
    rwa [kind_cy_of_term (Or.inr (Or.inl rfl)), mt_cy_one] at this
  have hc₅ : (Qk none).Reachable (cf (w - 2) (tIdx (r (w - 2)))) (Oe (w - 1)) := by
    have hrj := hr (w - 2) (by omega)
    have := hconn (.cy (w - 2) (tIdx (r (w - 2)))) ⟨by omega, tIdx_lt hrj⟩
    rwa [kind_cy_of_term (Or.inr (Or.inr (Or.inr rfl))), mt_cy_t,
      ite_eq_right (show ¬ (w - 2 + 2 < w) by omega)] at this
  have hR := router_of_comparators w hw (fun j => Set.range (cfin j) ∪ Bk (some j))
    (fun j => cycleOn (cfin j) ⊔ Qk (some j)) (fun j => cf j 0) (fun j => cf j 2)
    (fun j => cf j 1) (fun j => cf j (tIdx (r j))) Ie Oe hcomp hAdisj hIinj hOinj hIO hIOA
    (Qk none) (Bk none) (by rw [← hTnone]; exact (hPS none).2.1) hBA hc₁ hc₂ hc₃ hc₄ hc₅
  have hIimg : Ie '' Set.Iio w = ↑I := by
    ext v
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hD.Ie_mem k hk
    · intro hv; obtain ⟨k, hk, rfl⟩ := hD.Ie_surj v hv; exact ⟨k, hk, rfl⟩
  have hOimg : Oe '' Set.Iio w = ↑O := by
    ext v
    constructor
    · rintro ⟨k, hk, rfl⟩; exact hD.Oe_mem k hk
    · intro hv; obtain ⟨k, hk, rfl⟩ := hD.Oe_surj v hv; exact ⟨k, hk, rfl⟩
  rw [hIimg, hOimg] at hR
  set AA : Set V := Bk none ∪ ⋃ j ∈ Set.Iio (w - 1), (Set.range (cfin j) ∪ Bk (some j))
    with hAA
  have hcoe : (↑(univ.filter (· ∈ AA)) : Set V) = AA := by ext; simp
  refine ⟨univ.filter (· ∈ AA), ?_, ?_, ?_⟩
  · intro v hv
    have := hR.2.2.1 (by simpa using hv)
    simpa using this
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    have hBsub' : ∀ k v, v ∈ Bk k → v ∈ C ∪ Q ∪ I ∪ O := by
      intro k v hv
      rcases hBsub k v hv with h | h
      · obtain ⟨x, hx, -, rfl⟩ := (hT _ _).1 h
        have := hD.vt_mem hx
        simp only [mem_union] at this ⊢
        tauto
      · simp [h]
    rcases hv with hv | hv
    · exact hBsub' _ _ hv
    · obtain ⟨j, hj, hv⟩ := Set.mem_iUnion₂.1 hv
      rcases hv with ⟨i, rfl⟩ | hv
      · have := hD.cf_mem j i (by simp only [Set.mem_Iio] at hj; omega) i.2
        simp [cfin, this]
      · exact hBsub' _ _ hv
  · rw [hcoe]
    refine isHamRouter_mono ?_ hR
    refine sup_le (hPS none).1 ?_
    refine iSup₂_le fun j hj => sup_le ?_ (hPS (some j)).1
    have hj' : j + 1 < w := by simp only [Set.mem_Iio] at hj; omega
    exact cycleOn_le (cfin j) (cf j) (fun i => rfl) (fun i hi => hD.cf_adj j i hj' hi)

end Assembly

/-! ### The cycles of Lemma 3.7 and the enumerations of `I`, `O` -/

section Cycles

variable {V : Type*}

/-- An enumeration by `0, …, w - 1` of a finset of size `w > 0`. -/
lemma exists_enum (s : Finset V) (w : ℕ) (hs : s.card = w) (hw : 0 < w) :
    ∃ e : ℕ → V, (∀ k < w, e k ∈ s) ∧ (∀ k < w, ∀ k' < w, e k = e k' → k = k') ∧
      ∀ v ∈ s, ∃ k < w, e k = v := by
  classical
  obtain ⟨v0, -⟩ := s.card_pos.1 (by omega)
  refine ⟨fun k => if h : k < w then (s.equivFin.symm ⟨k, by omega⟩ : V) else v0, ?_, ?_, ?_⟩
  · intro k hk
    simp only [hk, dite_true]
    exact (s.equivFin.symm _).2
  · intro k hk k' hk' h
    simp only [hk, hk', dite_true] at h
    have := congrArg Fin.val (s.equivFin.symm.injective (Subtype.ext h))
    simpa using this
  · intro v hv
    have hlt : (s.equivFin ⟨v, hv⟩ : ℕ) < w := by
      have := (s.equivFin ⟨v, hv⟩).2; omega
    refine ⟨s.equivFin ⟨v, hv⟩, hlt, ?_⟩
    simp only [hlt, dite_true, Fin.eta, Equiv.symm_apply_apply]

/-- A cycle of a bipartite graph `H[C]` has even length `2 rr ≥ 4`, and its vertices
`getVert 0, …, getVert (2 rr - 1)` are distinct and cyclically adjacent. -/
lemma cycle_data [Fintype V] (H : WGraph V) (col : V → Bool) (C : Finset V)
    (hbip : H.IsBipartiteWith col) {x : C} (p : (H.induce C).supp.Walk x x) (hp : p.IsCycle) :
    ∃ rr, 2 ≤ rr ∧ (∀ i < 2 * rr, ∀ i' < 2 * rr, p.getVert i = p.getVert i' → i = i') ∧
      ∀ i < 2 * rr, H.supp.Adj (p.getVert i : V) (p.getVert ((i + 1) % (2 * rr)) : V) := by
  have hbipC : (H.induce C).IsBipartiteWith (fun y => col y) := fun a b h => hbip a b h
  have hcol := col_walk (H.induce C) (fun y => col y) hbipC p
  have heven : Even p.length := by
    by_contra h
    simp [h] at hcol
  obtain ⟨rr, hrr⟩ := heven
  have h3 := hp.three_le_length
  refine ⟨rr, by omega, ?_, ?_⟩
  · intro i hi i' hi' h
    exact hp.getVert_injOn' (show i ≤ p.length - 1 by omega) (show i' ≤ p.length - 1 by omega) h
  · intro i hi
    have hadj := p.adj_getVert_succ (show i < p.length by omega)
    have e : p.getVert ((i + 1) % (2 * rr)) = p.getVert (i + 1) := by
      rcases Nat.lt_or_ge (i + 1) (2 * rr) with h | h
      · rw [Nat.mod_eq_of_lt h]
      · have e1 : i + 1 = 2 * rr := by omega
        rw [e1, Nat.mod_self, SimpleGraph.Walk.getVert_zero, show 2 * rr = p.length by omega,
          SimpleGraph.Walk.getVert_length]
    rw [e]
    exact hadj

/-- `n` vertex-disjoint even cycles `cf j` (of length `2 r j ≥ 4`) in `C`, from a packing `Z` of
at least `n` disjoint cycles of `H[C]` (Lemma 3.7). -/
lemma exists_cycles [Fintype V] [DecidableEq V] [Nonempty V] (H : WGraph V) (col : V → Bool)
    (C : Finset V) (hbip : H.IsBipartiteWith col) (n : ℕ) (Z : Finset (Finset C))
    (hZ : n ≤ Z.card) (hdisj : (Z : Set (Finset C)).PairwiseDisjoint id)
    (hcyc : ∀ z ∈ Z, ∃ x, ∃ p : (H.induce C).supp.Walk x x, p.IsCycle ∧ p.support.toFinset = z) :
    ∃ r : ℕ → ℕ, ∃ cf : ℕ → ℕ → V, (∀ j < n, 2 ≤ r j) ∧ (∀ j < n, ∀ i < 2 * r j, cf j i ∈ C) ∧
      (∀ j < n, ∀ i < 2 * r j, H.supp.Adj (cf j i) (cf j ((i + 1) % (2 * r j)))) ∧
      (∀ j i j' i', j < n → i < 2 * r j → j' < n → i' < 2 * r j' → cf j i = cf j' i' →
        j = j' ∧ i = i') := by
  classical
  let zf : ℕ → Finset C := fun j =>
    if h : j < Z.card then (Z.equivFin.symm ⟨j, h⟩ : Finset C) else ∅
  have hzf : ∀ j < n, zf j ∈ Z := fun j hj => by
    simp only [zf, show j < Z.card by omega, dite_true]
    exact (Z.equivFin.symm _).2
  have hzf_inj : ∀ j < n, ∀ j' < n, zf j = zf j' → j = j' := by
    intro j hj j' hj' h
    simp only [zf, show j < Z.card by omega, show j' < Z.card by omega, dite_true] at h
    have := congrArg Fin.val (Z.equivFin.symm.injective (Subtype.ext h))
    simpa using this
  have hex : ∀ j, ∃ rr : ℕ, ∃ c : ℕ → V, j < n → 2 ≤ rr ∧
      (∀ i, c i ∈ C ∧ ∃ y ∈ zf j, (y : V) = c i) ∧
      (∀ i < 2 * rr, ∀ i' < 2 * rr, c i = c i' → i = i') ∧
      ∀ i < 2 * rr, H.supp.Adj (c i) (c ((i + 1) % (2 * rr))) := by
    intro j
    by_cases hj : j < n
    · obtain ⟨x, p, hp, hpz⟩ := hcyc _ (hzf j hj)
      obtain ⟨rr, hrr, hinj, hadj⟩ := cycle_data H col C hbip p hp
      refine ⟨rr, fun i => p.getVert i, fun _ => ⟨hrr, fun i => ⟨(p.getVert i).2, p.getVert i,
        ?_, rfl⟩, fun i hi i' hi' h => hinj i hi i' hi' (Subtype.ext h), hadj⟩⟩
      rw [← hpz, List.mem_toFinset]
      exact p.getVert_mem_support i
    · exact ⟨0, fun _ => Classical.arbitrary V, fun h => absurd h hj⟩
  choose r cf hcf using hex
  refine ⟨r, cf, fun j hj => (hcf j hj).1, fun j hj i _ => ((hcf j hj).2.1 i).1,
    fun j hj => (hcf j hj).2.2.2, ?_⟩
  intro j i j' i' hj hi hj' hi' h
  obtain ⟨y, hy, hyi⟩ := ((hcf j hj).2.1 i).2
  obtain ⟨y', hy', hyi'⟩ := ((hcf j' hj').2.1 i').2
  have hyy : y = y' := Subtype.ext (hyi.trans (h.trans hyi'.symm))
  subst hyy
  have hjj : j = j' := by
    by_contra hne
    have hne' : zf j ≠ zf j' := fun h' => hne (hzf_inj j hj j' hj' h')
    exact Finset.disjoint_left.1 (hdisj (Finset.mem_coe.2 (hzf j hj))
      (Finset.mem_coe.2 (hzf j' hj')) hne') hy hy'
  subst hjj
  exact ⟨rfl, (hcf j hj).2.2.1 i hi i' hi' h⟩

end Cycles

end RouterStep

/-- **`T3.2c` (the router).** Lemma 3.7 gives at least `w` disjoint short even cycles in `C`;
Lemma 3.5 turns `w - 1` of them into comparators, Lemma 3.6 arranges them, and Lemma 3.4 in `Q`
supplies all the internally disjoint connections. The result is an `I, O`-Hamilton router on
a vertex set inside `C ∪ Q ∪ I ∪ O`. -/
theorem router_step (ω : ℝ) (hω : 0 < ω) :
    ∃ ε c₇ C₇ : ℝ, 0 < ε ∧ 0 < c₇ ∧ 0 < C₇ ∧ RouterSpec.{u} ω ε c₇ C₇ := by
  obtain ⟨c₇, C₇, hc₇, hC₇, h37⟩ := many_short_cycles.{u} ω (1 / 2) 2 hω (by norm_num)
    (by norm_num)
  obtain ⟨c₄, C₄, hc₄, -, h34⟩ := spectral_connection.{u, 0} (1 / 2) (by norm_num) (by norm_num)
  refine ⟨c₄ * (1 / 4), c₇, C₇, by positivity, hc₇, hC₇, ?_⟩
  intro V _ _ H col C Q I O w DC Δ σQ L g hbip hW hCQ hCI hCO hQI hQO hIO hIw hOw hw hdegC hDC
    hgC hwC hΔ hdegQ hgapQ hσ hσ1 hLQ hdQ hsparse
  have : Nonempty V := by
    obtain ⟨v, -⟩ := I.card_pos.1 (by omega)
    exact ⟨v⟩
  -- Lemma 3.7 in `C`
  have hbipC : (H.induce C).IsBipartiteWith (fun x => col x) := fun x y h => hbip x y h
  have hWC : (H.induce C).WeightsIn ω := fun x y h => hW x y h
  obtain ⟨Z, hZcard, hZdisj, hZcyc⟩ := h37 (H.induce C) (fun x => col x) DC g hbipC hWC hdegC hDC
    (by rwa [Fintype.card_coe])
  rw [Fintype.card_coe] at hZcard
  have hwZ : w - 1 ≤ Z.card := by
    have h1 : (w : ℝ) ≤ Z.card := hwC.trans hZcard
    have h2 : w ≤ Z.card := by exact_mod_cast h1
    omega
  obtain ⟨r, cf, hr, hcfC, hcfadj, hcfinj⟩ := RouterStep.exists_cycles H col C hbip (w - 1) Z hwZ
    hZdisj (fun z hz => by obtain ⟨x, p, hp, -, hpz⟩ := hZcyc z hz; exact ⟨x, p, hp, hpz⟩)
  obtain ⟨Ie, hIe1, hIe2, hIe3⟩ := RouterStep.exists_enum I w hIw (by omega)
  obtain ⟨Oe, hOe1, hOe2, hOe3⟩ := RouterStep.exists_enum O w hOw (by omega)
  have hD : RouterStep.Data H.supp C I O w r Ie Oe cf :=
    { two_le := hw
      r_ge := fun j hj => hr j (by omega)
      cf_mem := fun j i hj hi => hcfC j (by omega) i hi
      cf_adj := fun j i hj hi => hcfadj j (by omega) i hi
      cf_inj := fun j i j' i' hj hi hj' hi' h => hcfinj j i j' i' (by omega) hi (by omega) hi' h
      Ie_mem := hIe1
      Oe_mem := hOe1
      Ie_inj := hIe2
      Oe_inj := hOe2
      Ie_surj := hIe3
      Oe_surj := hOe3
      disj_CI := hCI
      disj_CO := hCO
      disj_IO := hIO }
  have hQ' : ∀ x ∈ C ∪ I ∪ O, x ∉ Q := by
    intro x hx hxQ
    simp only [mem_union] at hx
    rcases hx with (hx | hx) | hx
    · exact disjoint_left.1 hCQ hx hxQ
    · exact disjoint_left.1 hQI hxQ hx
    · exact disjoint_left.1 hQO hxQ hx
  -- Lemma 3.4 in `Q`, for all connections at once
  obtain ⟨p, hp, -, hint, hdisjQ⟩ := h34 H Q Δ σQ L (1 / 4) (κ := RouterStep.goodSet w r)
    (fun s => RouterStep.vt Ie Oe cf s.1) (fun s => RouterStep.vt Ie Oe cf (RouterStep.mt w r s.1))
    hΔ hdegQ hgapQ hσ hσ1 hLQ (by norm_num) (by norm_num)
    (fun s => ⟨hQ' _ (hD.vt_mem (hD.good s).1), hQ' _ (hD.vt_mem (hD.good s).2.2),
      hD.ends_ne s⟩)
    (fun x => by
      refine le_trans (Finset.card_le_one.2 fun a ha b hb => ?_) (by norm_num)
      simp only [mem_filter, mem_univ, true_and] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hD.ends_inj a b _ _ (Or.inl rfl) (Or.inl rfl) (ha.trans hb.symm)
      · exact hD.ends_inj a b _ _ (Or.inl rfl) (Or.inr rfl) (ha.trans hb.symm)
      · exact hD.ends_inj a b _ _ (Or.inr rfl) (Or.inl rfl) (ha.trans hb.symm)
      · exact hD.ends_inj a b _ _ (Or.inr rfl) (Or.inr rfl) (ha.trans hb.symm))
    (fun s => ⟨hdQ _ (hD.vt_mem (hD.good s).1), hdQ _ (hD.vt_mem (hD.good s).2.2)⟩)
    (fun v hv => by
      refine le_trans (degOn_mono H v ?_) (hsparse v hv)
      intro x hx
      simp only [mem_union, mem_image, mem_univ, true_and] at hx
      rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact hD.vt_mem (hD.good s).1
      · exact hD.vt_mem (hD.good s).2.2)
  exact RouterStep.assemble hD hCQ (disjoint_comm.1 hQI) (disjoint_comm.1 hQO) p hp hint hdisjQ

end LocalAbsorption

end Lovasz
