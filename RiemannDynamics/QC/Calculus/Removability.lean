/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Defs.Geometric
import RiemannDynamics.QC.LengthArea.CurveModulus

/-!
# Quasiconformal calculus: removability

Curves that travel along a Lebesgue-null set carry no conformal modulus (Fuglede), so such a set
is removable from the modulus distortion bound: a sense-preserving homeomorphism whose distortion
bound `M(f(Q)) ≤ K · M(Q)` holds after discarding the image curves that spend positive arc length
on a null set `N` is geometrically `K`-quasiconformal. The discarded curves form a zero-modulus
subfamily, so removing them leaves the image-family modulus unchanged.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Removability of a null set from the distortion bound.** Let `N ⊆ ℂ` be measurable and
Lebesgue-null. If `f` is a topologically sense-preserving homeomorphism and, for every
quadrilateral `Q`, the modulus of the image connecting curves that do *not* spend positive arc
length on `N` is at most `K · M(Q)`, then `f` is geometrically `K`-quasiconformal. The image curves
that do linger on `N` form a zero-modulus subfamily (`curveModulus_meetsNullSet_zero`), so
discarding them does not change the modulus of the full image family
(`curveModulus_sdiff_modulus_zero`), and the bound extends to every image curve. -/
theorem isQCGeometric_of_removable_nullSet {f : ℂ → ℂ} {K : ℝ} {N : Set ℂ}
    (hf : SensePreserving f) (hK : 1 ≤ K)
    (hNmeas : MeasurableSet N) (hNnull : volume N = 0)
    (hqc : ∀ Q : Quadrilateral,
      curveModulus (Q.imageCurveFamily f \
        {γ ∈ Q.imageCurveFamily f | 1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ})
        ≤ ENNReal.ofReal K * Q.modulus) :
    IsQCGeometric f K := by
  refine ⟨hK, hf, fun Q => ?_⟩
  have hzero : curveModulus {γ ∈ Q.imageCurveFamily f |
      1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ} = 0 :=
    curveModulus_meetsNullSet_zero hNmeas hNnull (Q.imageCurveFamily f)
  have hsub : {γ ∈ Q.imageCurveFamily f |
      1 ≤ arcLengthLineIntegral (N.indicator (fun _ => ∞)) γ} ⊆ Q.imageCurveFamily f :=
    fun γ hγ => hγ.1
  rw [← curveModulus_sdiff_modulus_zero hsub hzero]
  exact hqc Q

end RiemannDynamics
