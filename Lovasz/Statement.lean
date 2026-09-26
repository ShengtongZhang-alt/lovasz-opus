/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5.5 (AI agent), directed by Shengtong Zhang
-/
import Mathlib

/-!
# Statement definitions for the proof development

The two definitions used by the statement of Theorem 1.1, for use by the proof development.
They are copied verbatim from `Challenge.lean`, which must import only Mathlib; Comparator
checks that the copies in the `Challenge` and `Solution` environments are identical.
-/

namespace Lovasz

open SimpleGraph

/-- The paper's standing hypothesis on a connection set (Section 2): `S = S⁻¹` and `1 ∉ S`. -/
def IsConnectionSet {G : Type*} [Group G] (S : Finset G) : Prop :=
  (∀ s ∈ S, s⁻¹ ∈ S) ∧ (1 : G) ∉ S

/-- The Cayley graph `Cay(G, S)`: the simple graph on `G` whose edges are `x ∼ x * s` for
`s ∈ S`. This is Mathlib's `SimpleGraph.mulCayley`. -/
abbrev cayleyGraph {G : Type*} [Group G] (S : Finset G) : SimpleGraph G :=
  mulCayley (S : Set G)

end Lovasz
