/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.Analytic
import RiemannDynamics.QC.LengthArea
import RiemannDynamics.Analysis.Sobolev.SobolevToACL

/-!
# Equivalence of the analytic and geometric quasiconformal definitions

The two standard definitions of a quasiconformal map — the **analytic** one
(`IsQCAnalytic`, an orientation-preserving `W^{1,2}_loc` homeomorphism satisfying
the Beltrami equation `∂̄f = μ ∂f` with `‖μ‖∞ < 1`) and the **geometric** one
(`IsQCGeometric`, modulus quasi-invariance of quadrilaterals) — describe the same
maps, with the dilatation `K` and the Beltrami bound `‖μ‖∞` related by
`‖μ‖∞ ≤ (K − 1)/(K + 1)`.

This file proves the bridge `qc_analytic_iff_geometric`, splitting it into the two
directions:

* `isQCGeometric_of_isQCAnalytic` — analytic ⇒ geometric. Uses the
  `Sobolev ⇒ ACL` theorems (`exists_aclHorizontal_of_hasWeakDirDeriv_one`,
  `exists_aclVertical_of_hasWeakDirDeriv_I`) to extract absolute continuity on
  lines from `MemW12loc`, then the length–area modulus estimate bounds the modulus
  distortion by the dilatation `K`.
* `isQCAnalytic_of_isQCGeometric` — geometric ⇒ analytic (the hard direction). A
  modulus-quasi-invariant homeomorphism is absolutely continuous on lines (a
  length–area argument), hence in `W^{1,2}_loc` via `memWklocP_one_of_acl`, and the
  modulus bound forces the Beltrami coefficient to satisfy `‖μ‖∞ ≤ (K − 1)/(K + 1)`.

The analytic and geometric tracks meet only here; results stated in one track are
transferred to the other through this equivalence.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Geometric ⇒ analytic** (the hard direction). A `K`-quasiconformal map in the
geometric (modulus) sense is absolutely continuous on lines, hence lies in
`W^{1,2}_loc`, and satisfies the Beltrami equation with a coefficient of norm at
most `(K − 1)/(K + 1)`. -/
theorem isQCAnalytic_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hf : IsQCGeometric f K) :
    ∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧ IsQCAnalytic f b := by
  sorry

/-! The clean, hypothesis-free analytic ⇒ geometric endpoint `isQCGeometric_of_isQCAnalytic`
and the equivalence `qc_analytic_iff_geometric` are proved downstream in `QC/QCEquivalence.lean`,
where the planar Lusin-(N) fact `IsQCAnalytic.image_lusinN` (from the higher-integrability
machinery, which sits below this file) is available. The earlier Lusin-(N)-hypothesised
analytic ⇒ geometric scaffold that lived in this file has since been removed and superseded by
that downstream rebuild. -/

end RiemannDynamics
