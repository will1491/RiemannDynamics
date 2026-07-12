/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.GroupTheory.PresentedGroup
import RiemannDynamics.Surface.GenusSurface

/-!
# The surface group of genus `g`

The abstract fundamental group of the closed orientable surface of genus
`g`: the group presented by generators `a_1, b_1, …, a_g, b_g` and the
single relator `∏ⱼ a_j b_j a_j⁻¹ b_j⁻¹`.

The target identification — that the fundamental group of the `4g`-gon
model is this presented group,

`Nonempty (FundamentalGroup (GenusSurface g) (basePoint g) ≃* surfaceGroup g)`,

is the polygon case of the Seifert–van Kampen theorem and is not stated
here: with the current infrastructure it would require either the universal
`4g`-gon tiling (the Poincaré polygon theorem) together with a deck-group
bridge, or edge-path combinatorics on the polygon complex. This file only
pins the group-theoretic interface.
-/

open Set

namespace RiemannDynamics

/-- The generators of the genus-`g` surface group: `Sum.inl j` is `a_{j+1}`
and `Sum.inr j` is `b_{j+1}`. -/
def SurfaceGen (g : ℕ) : Type := Fin g ⊕ Fin g

/-- The single relator of the genus-`g` surface group: the product of the
commutators `a_j b_j a_j⁻¹ b_j⁻¹` over the `g` handles. -/
noncomputable def surfaceRelator (g : ℕ) : FreeGroup (SurfaceGen g) :=
  (List.ofFn fun j : Fin g =>
    (FreeGroup.of (Sum.inl j) * FreeGroup.of (Sum.inr j) *
      (FreeGroup.of (Sum.inl j))⁻¹ * (FreeGroup.of (Sum.inr j))⁻¹ :
        FreeGroup (SurfaceGen g))).prod

/-- The genus-`g` surface group: `2g` generators and the single commutator
relator. -/
noncomputable def surfaceGroup (g : ℕ) : Type :=
  PresentedGroup ({surfaceRelator g} : Set (FreeGroup (SurfaceGen g)))

noncomputable instance (g : ℕ) : Group (surfaceGroup g) :=
  inferInstanceAs
    (Group (PresentedGroup ({surfaceRelator g} : Set (FreeGroup (SurfaceGen g)))))

end RiemannDynamics
