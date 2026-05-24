/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Hyperbolic.DiskMetric
import RiemannDynamics.Hyperbolic.ModularFunction

/-!
# Hyperbolic metric on the triply-punctured sphere `ℂ ∖ {0, 1}`

The triply-punctured plane `ℂ ∖ {0, 1}` is a hyperbolic Riemann surface;
its universal cover is the unit disk `𝔻` via the modular function
`modularLambda` from `ModularFunction.lean`. We define the hyperbolic
distance on `ℂ ∖ {0, 1}` as the infimum of disk hyperbolic distances
over pairs of preimages.

This file is currently architecture only: the proof that the infimum
gives a metric, and the proof that holomorphic maps `f : U → ℂ ∖ {0, 1}`
from simply connected `U ⊆ ℂ` lift to `f̃ : U → 𝔻` (used in
`StrongMontel`), are deferred to subsequent prover passes.
-/

namespace RiemannDynamics

open Complex Metric Set

/-- The hyperbolic distance on the triply-punctured plane, defined as
the infimum of `hyperbolicDistDisk z₁ z₂` over pairs of disk preimages
of `w₁` and `w₂` under `modularLambda`. For `w₁ = 0` or `w₁ = 1` (or
likewise for `w₂`) the preimage in `𝔻` is empty and the formula returns
the Lean junk value `0`. -/
noncomputable def hyperbolicDistTriplyPunctured (w₁ w₂ : ℂ) : ℝ :=
  sInf (Set.image2 hyperbolicDistDisk
    (modularLambda ⁻¹' {w₁} ∩ ball (0 : ℂ) 1)
    (modularLambda ⁻¹' {w₂} ∩ ball (0 : ℂ) 1))

/-! ## Distance axioms on `ℂ ∖ {0, 1}` -/

/-- `hyperbolicDistTriplyPunctured w w = 0` for `w ∈ ℂ ∖ {0, 1}`. -/
theorem hyperbolicDistTriplyPunctured_self {w : ℂ} (_hw : w ≠ 0 ∧ w ≠ 1) :
    hyperbolicDistTriplyPunctured w w = 0 := by
  unfold hyperbolicDistTriplyPunctured
  by_cases h : (modularLambda ⁻¹' {w} ∩ ball (0 : ℂ) 1).Nonempty
  · obtain ⟨z, hz⟩ := h
    apply le_antisymm
    · refine csInf_le ⟨0, ?_⟩ ⟨z, hz, z, hz, hyperbolicDistDisk_self z⟩
      rintro d ⟨z₁, _, z₂, _, rfl⟩
      exact hyperbolicDistDisk_nonneg z₁ z₂
    · refine Real.sInf_nonneg ?_
      rintro d ⟨z₁, _, z₂, _, rfl⟩
      exact hyperbolicDistDisk_nonneg z₁ z₂
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.image2_empty_left, Real.sInf_empty]

/-- Symmetry of the triply-punctured hyperbolic distance. -/
theorem hyperbolicDistTriplyPunctured_comm (w₁ w₂ : ℂ) :
    hyperbolicDistTriplyPunctured w₁ w₂ = hyperbolicDistTriplyPunctured w₂ w₁ := by
  unfold hyperbolicDistTriplyPunctured
  apply congr_arg sInf
  ext d
  simp only [Set.mem_image2]
  refine ⟨fun ⟨z₁, hz₁, z₂, hz₂, hd⟩ => ?_, fun ⟨z₁, hz₁, z₂, hz₂, hd⟩ => ?_⟩ <;>
    exact ⟨z₂, hz₂, z₁, hz₁, by rw [← hd]; exact hyperbolicDistDisk_comm _ _⟩

/-- Non-negativity of the triply-punctured hyperbolic distance. -/
theorem hyperbolicDistTriplyPunctured_nonneg (w₁ w₂ : ℂ) :
    0 ≤ hyperbolicDistTriplyPunctured w₁ w₂ := by
  unfold hyperbolicDistTriplyPunctured
  refine Real.sInf_nonneg ?_
  rintro d ⟨z₁, _, z₂, _, rfl⟩
  exact hyperbolicDistDisk_nonneg z₁ z₂

/-- Non-degeneracy: on `ℂ ∖ {0, 1}`, the distance vanishes only on the
diagonal.

**Deferred proof sketch.** The `←` direction is direct from
`hyperbolicDistTriplyPunctured_self`. The `→` direction (distance zero
implies equal) requires the covering map structure of
`modularLambda : 𝔻 → ℂ ∖ {0, 1}`: distinct fibers
`λ⁻¹{w₁}` and `λ⁻¹{w₂}` for `w₁ ≠ w₂` are mutually positively
separated in the disk hyperbolic distance (since the fibers form a
`Γ(2)`-orbit, which is discrete and properly discontinuous). Status:
blocked on `modularLambda_isCoveringMapOn`. -/
theorem hyperbolicDistTriplyPunctured_eq_zero_iff {w₁ w₂ : ℂ}
    (hw₁ : w₁ ≠ 0 ∧ w₁ ≠ 1) (hw₂ : w₂ ≠ 0 ∧ w₂ ≠ 1) :
    hyperbolicDistTriplyPunctured w₁ w₂ = 0 ↔ w₁ = w₂ := by
  sorry

/-- Triangle inequality for the triply-punctured hyperbolic distance.

**Deferred proof sketch.** Standard infimum-triangle argument requires
synchronizing preimages: for `ε > 0`, pick near-minimal
`(z₁, z₂) ∈ λ⁻¹{w₁} × λ⁻¹{w₂}` and `(z₂', z₃) ∈ λ⁻¹{w₂} × λ⁻¹{w₃}`,
then apply a `Γ(2)`-deck transformation to bring `z₂' = z₂` while
preserving the disk distance from `z₂'` to `z₃`. Status: blocked on
`Γ(2)` deck transformations being disk isometries. -/
theorem hyperbolicDistTriplyPunctured_triangle {w₁ w₂ w₃ : ℂ}
    (hw₁ : w₁ ≠ 0 ∧ w₁ ≠ 1) (hw₂ : w₂ ≠ 0 ∧ w₂ ≠ 1) (hw₃ : w₃ ≠ 0 ∧ w₃ ≠ 1) :
    hyperbolicDistTriplyPunctured w₁ w₃
      ≤ hyperbolicDistTriplyPunctured w₁ w₂ + hyperbolicDistTriplyPunctured w₂ w₃ := by
  sorry

/-! ## Schwarz–Pick on the triply-punctured sphere -/

/-- The covering property of `modularLambda` makes the triply-punctured
distance non-expansive under holomorphic self-maps of the
triply-punctured plane. Stated as an architecture placeholder; the
real consumer is the Montel–Carathéodory lift in `StrongMontel`.

**Deferred proof sketch.** Lift `f : U → ℂ ∖ {0, 1}` to
`f̃ : U → 𝔻` via the universal-cover lifting property of
`modularLambda : 𝔻 → ℂ ∖ {0, 1}` (using that `U` is simply connected;
the actual signature should add `SimplyConnectedSpace U` as a
hypothesis). Then apply Schwarz–Pick to `f̃` on `𝔻`. Status: blocked on
both `modularLambda_isCoveringMapOn` and `Mathlib.Topology.Homotopy.Lifting`
adaptation. -/
theorem hyperbolicDistTriplyPunctured_schwarzPick
    {f : ℂ → ℂ} {U : Set ℂ} (_hU : IsOpen U)
    (_hd : DifferentiableOn ℂ f U)
    (_hf : ∀ z ∈ U, f z ≠ 0 ∧ f z ≠ 1)
    {z w : ℂ} (_hz : z ∈ U) (_hw : w ∈ U) :
    hyperbolicDistTriplyPunctured (f z) (f w) ≤ hyperbolicDistTriplyPunctured z w := by
  sorry

end RiemannDynamics
