/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.InverseQC

/-!
# The analytic ⇔ geometric quasiconformal equivalence (clean endpoints)

This file states the Milestone 9.2 headline theorems in their clean, hypothesis-free form:

* `isQCGeometric_of_isQCAnalytic` — analytic ⇒ geometric;
* `qc_analytic_iff_geometric` — the full equivalence.

The analytic ⇒ geometric direction is necessarily proved **here**, downstream of
`QC/InverseQC.lean`, rather than in `QC/Equivalence.lean`: its image-side modulus argument
needs the planar Lusin-(N) fact `IsQCAnalytic.image_lusinN`, which in turn rests on the
higher-integrability machinery (`Beltrami.lean`, importing `QC/LengthArea.lean`) and therefore
sits strictly below the `Equivalence` file. The upstream files expose the result with the
Lusin-(N) fact threaded as an explicit hypothesis
(`isQCGeometric_of_isQCAnalytic_of_lusinN`); here that hypothesis is discharged by
`image_lusinN`.
-/

open MeasureTheory Complex Set

namespace RiemannDynamics

/-- **Analytic ⇒ geometric** (clean endpoint). A map carrying an analytic-quasiconformal
structure with Beltrami norm `≤ (K − 1)/(K + 1)` is `K`-quasiconformal in the geometric
(modulus) sense. The planar Lusin-(N) hypothesis of `isQCGeometric_of_isQCAnalytic_of_lusinN`
is discharged by `IsQCAnalytic.image_lusinN` (available at this layer). -/
theorem isQCGeometric_of_isQCAnalytic {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    {b : BeltramiCoeff} (hb : b.normInf ≤ (K - 1) / (K + 1)) (hf : IsQCAnalytic f b) :
    IsQCGeometric f K := by
  refine isQCGeometric_of_isQCAnalytic_of_lusinN hK hb hf ?_
  -- `image_lusinN` is stated on `{¬diff ∨ ¬0<det}`; the wall's degeneracy set is
  -- `{¬(diff ∧ 0<det)}`; the two coincide by De Morgan.
  have hset : {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}
      = {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det} := by
    ext z; exact not_and_or
  rw [hset]; exact hf.image_lusinN

/-- **Equivalence of the analytic and geometric quasiconformal definitions.** For `1 ≤ K`, a
map admits an analytic-quasiconformal structure with Beltrami norm at most `(K − 1)/(K + 1)`
if and only if it is `K`-quasiconformal in the geometric (modulus) sense. -/
theorem qc_analytic_iff_geometric {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K) :
    (∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧ IsQCAnalytic f b) ↔
      IsQCGeometric f K :=
  ⟨fun ⟨_, hb, hf⟩ => isQCGeometric_of_isQCAnalytic hK hb hf,
    isQCAnalytic_of_isQCGeometric hK⟩

end RiemannDynamics
