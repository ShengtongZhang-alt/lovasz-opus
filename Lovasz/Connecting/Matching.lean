/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Connecting.Basic

/-!
# The random matching (6.13)–(6.17)

DAG node `E6.13` of `docs/BLUEPRINT.md` (Section 6.4 of the paper).
-/

universe u

noncomputable section

namespace Lovasz

open Finset Classical

namespace Connector

/-! ### Step E6.13: the random matching -/

section Matching

variable {G : Type u} [Fintype G] [DecidableEq G]

/-- **The matching `R` and the marks `Z₀` (§6.4, (6.13)–(6.17)).** Apply Lemma 6.4 to `Y` with
edge probability `p` and marking probability `1/128`. Given directional balance, the gap
`s(J) ∈ {0} ∪ [µ, ∞)`, the part-cut bound and cut counting for the state cuts, and endpoint tests
`(A, τ)` with mean `≤ pk|A| ≤ τ/2`, a union bound gives an outcome with
`|δ^±_{D(R)}(J)| ≥ ps/12`, `|δ_{D(R)}(J)| ≤ 2ps`, `|δ_{D(Z₀)}(J)| ≤ ps/64` for every state set
`J` (`s = s(J)`), a marked edge across every nontrivial part cut, at least `256` unmarked
matching edges across every nontrivial part cut (6.15), and `|A ∩ V(R)| ≤ τ` for every test
(6.17).

Proof sketch (constants checked): for a state set `J` with `s = s(J) ≥ µ`, the tails of Lemma 6.4
give failure probabilities at most `e^{-3ps/64}` (each direction, mean `≥ ps/3`), `e^{-3ps/16}`
(`|δ_{D(R)}| > 2ps`, mean `ps`), `e^{-3ps/2048}` (`|δ_{D(Z₀)}| > ps/64`, mean `ps/128`); for a part
cut `I` with `s = s(I × Bool) ≥ µ`, at most `e^{-ps/1024}` (no marked crossing edge, mean `ps/256`)
and `e^{-127ps/4096}` (fewer than `256` unmarked crossing edges, mean `127ps/256 ≥ 512`). All are
`≤ e^{-ps/2048}`, so the cut events cost `≤ ∑_{j ≥ 1} 6 N^{16(j+1)} e^{-jpµ/2048} ≤ 6∑_j e^{-4j}`
by `hcount` and `hpµ₂`; state sets with `s(J) = 0` impose nothing. A test `(A, τ)` fails with
probability `≤ e^{-3τ/40}` (mean `≤ τ/2`), and these sum to `≤ e^{-2}`. The total is `< 1`. -/
theorem exists_matching {t : ℕ} (Y : SimpleGraph G) (π : G → Fin t) (sg : G → Bool) (k : ℕ)
    (hk : ∀ v, Y.degree v ≤ k) (p μ : ℝ) (hp : 0 < p) (hpk : p * k ^ 2 ≤ 1) (hμ : 6 ≤ μ)
    (hpμ₁ : 1100 ≤ p * μ)
    (hpμ₂ : 32 * Real.log (4 * (t + Y.edgeFinset.card)) + 4 ≤ p * μ / 2048)
    (hbal : ∀ J : Finset (Fin t × Bool),
      (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * outCnt π sg J Y.edgeFinset ∧
        (cutCnt π sg J Y.edgeFinset : ℝ) ≤ 3 * inCnt π sg J Y.edgeFinset)
    (hgap : ∀ J : Finset (Fin t × Bool),
      cutCnt π sg J Y.edgeFinset = 0 ∨ μ ≤ cutCnt π sg J Y.edgeFinset)
    (hpart : ∀ I : Finset (Fin t), I.Nonempty → I ≠ univ →
      μ ≤ cutCnt π sg (I ×ˢ univ) Y.edgeFinset)
    (hcount : ∀ j : ℕ, (((univ : Finset (Finset (Fin t × Bool))).filter fun J =>
      (cutCnt π sg J Y.edgeFinset : ℝ) < (j + 1) * μ).card : ℝ) ≤
        (4 * (t + Y.edgeFinset.card)) ^ (16 * (j + 1)))
    (tests : Finset (Finset G × ℝ))
    (htests : ∀ q ∈ tests, p * k * q.1.card ≤ q.2 / 2 ∧
      Real.log tests.card + 2 ≤ 3 / 40 * q.2) :
    ∃ R Z₀ : Finset (Sym2 G), Z₀ ⊆ R ∧ R ⊆ Y.edgeFinset ∧
      (∀ e ∈ R, ∀ f ∈ R, e ≠ f → ∀ v ∈ e, v ∉ f) ∧
      (∀ J : Finset (Fin t × Bool),
        p * cutCnt π sg J Y.edgeFinset / 12 ≤ outCnt π sg J R ∧
        p * cutCnt π sg J Y.edgeFinset / 12 ≤ inCnt π sg J R ∧
        (cutCnt π sg J R : ℝ) ≤ 2 * p * cutCnt π sg J Y.edgeFinset ∧
        (cutCnt π sg J Z₀ : ℝ) ≤ p * cutCnt π sg J Y.edgeFinset / 64) ∧
      (∀ I : Finset (Fin t), I.Nonempty → I ≠ univ → ∃ e ∈ Z₀, PartCross π I e) ∧
      (∀ I : Finset (Fin t), I.Nonempty → I ≠ univ →
        256 ≤ ((R \ Z₀).filter (PartCross π I)).card) ∧
      ∀ q ∈ tests, ((q.1.filter (· ∈ vtx R)).card : ℝ) ≤ q.2 := by
  sorry

end Matching

end Connector

end Lovasz
