/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
import Lovasz.Defs

/-!
# The normalized Cheeger inequality (classical input)

DAG node `K.cheeger` of `docs/BLUEPRINT.md`; cited in Section 2.1 of the paper (Chung,
*Spectral Graph Theory*). Only the hard direction `1 - λ₂(N_H) ≥ Φ(H)² / 2` is used.
-/

namespace Lovasz

open Finset

namespace WGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Normalized Cheeger inequality.** If every vertex set `U` with
`vol(U) ≤ vol(V) / 2` has `e_H(U, Uᶜ) ≥ φ vol(U)` (conductance `Φ(H) ≥ φ`) and all degrees are
positive, then the normalized upper gap is at least `φ² / 2`. -/
theorem hasGap_of_conductance (H : WGraph V) (φ : ℝ) (hφ : 0 ≤ φ) (hdeg : ∀ x, 0 < H.deg x)
    (hcond : ∀ U : Finset V, 2 * H.vol U ≤ H.vol univ →
      φ * H.vol U ≤ H.edgeWeight U (univ \ U)) :
    H.HasGap (φ ^ 2 / 2) := by
  sorry

end WGraph

end Lovasz
