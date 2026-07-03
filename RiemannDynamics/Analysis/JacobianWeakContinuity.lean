/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.LengthArea.Mollification
import RiemannDynamics.Analysis.WeakCompactness
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weak continuity of the Jacobian (the null-Lagrangian cluster)

The real Jacobian determinant of a planar map `f : ℂ → ℂ` is a *null Lagrangian*:
tested against a smooth compactly supported function it can be integrated by parts
into a lower-order expression that involves only first derivatives linearly against
`Re f`. This "divergence structure" is what makes the Jacobian **weakly continuous**:
along a sequence `fₙ → g` locally uniformly whose gradients converge weakly in `L²`,
the tested Jacobians `∫ (J fₙ)·φ` converge to `∫ (J g)·φ`.

The file develops this in the repo's weak-derivative vocabulary
(`HasWeakDirDeriv`/`HasWeakGradient`, `RiemannDynamics.Analysis.Sobolev.WeakDeriv`):

* `partialX`, `partialY` — the coordinate partial derivatives `∂ₓ`, `∂ᵧ` as the
  directional Fréchet derivatives in the directions `1` and `I`.
* `jacobianWeak gx gy` — the Jacobian written in a pair of weak partial derivatives
  `(gx, gy)`: `(Re gx)(Im gy) − (Re gy)(Im gx)`. When `gx = ∂ₓf`, `gy = ∂ᵧf` this is
  the real determinant of `Df`.
* `integral_jacobian_smul_eq` (J1) — the null-Lagrangian integration-by-parts
  identity for a `C²` map: `∫ (J f)·φ = ∫ (Re f)·(∂ₓ(Im f)·∂ᵧφ − ∂ᵧ(Im f)·∂ₓφ)`.
  The `C²` hypothesis is exactly what makes the mixed second partials of `Im f`
  cancel (Clairaut); the sole consumer feeds mollified (`C^∞`) functions.
* `integral_jacobianWeak_smul_eq` (J2) — the same identity for a continuous `W^{1,2}`
  map, obtained by mollification and passage to the limit.
* `tendsto_integral_jacobianWeak_smul` (J3) — weak continuity of the tested Jacobian
  along a locally-uniformly convergent sequence with weakly-`L²`-convergent gradients.
* `le_liminf_integral_normSq_smul` (J4) — weighted weak lower semicontinuity of the
  `L²` norm: `∫ ‖h‖²·w ≤ liminf ∫ ‖hₙ‖²·w` for a bounded nonnegative weight `w`.
* `hasWeakDirDeriv_of_tendsto` (J5) — a weak directional derivative passes to a
  locally-uniform limit whose derivatives converge weakly in `L²`.

Weak `L²` convergence is phrased through the pairing against `L²` test functions
`∫ hₙ·ψ → ∫ h·ψ` (`TendstoWeaklyL2`), which is the form the divergence identity tests
and which the Hilbert-space inner-product convergence of
`RiemannDynamics.Analysis.WeakCompactness` specializes to.
-/

open MeasureTheory Complex
open scoped ContDiff ENNReal NNReal

namespace RiemannDynamics

variable {f : ℂ → ℂ} {φ : ℂ → ℝ}

/-- The coordinate partial derivative `∂ₓ h` as the Fréchet directional derivative in
the direction `1`. -/
noncomputable def partialX (h : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ h z) 1

/-- The coordinate partial derivative `∂ᵧ h` as the Fréchet directional derivative in
the direction `I`. -/
noncomputable def partialY (h : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ h z) Complex.I

/-- Unfolding lemma for `partialX`: `∂ₓ h z = (Df z) 1`. -/
theorem partialX_def (h : ℂ → ℂ) (z : ℂ) : partialX h z = (fderiv ℝ h z) 1 := rfl

/-- Unfolding lemma for `partialY`: `∂ᵧ h z = (Df z) I`. -/
theorem partialY_def (h : ℂ → ℂ) (z : ℂ) : partialY h z = (fderiv ℝ h z) Complex.I := rfl

attribute [irreducible] partialX partialY

/-- The Jacobian determinant written in a pair of weak partial derivatives
`(gx, gy)` standing for `(∂ₓf, ∂ᵧf)`: `(Re gx)(Im gy) − (Re gy)(Im gx)`. When
`gx = ∂ₓf` and `gy = ∂ᵧf` this equals the real determinant of the differential
`Df`. -/
def jacobianWeak (gx gy : ℂ → ℂ) (z : ℂ) : ℝ :=
  (gx z).re * (gy z).im - (gy z).re * (gx z).im

/-- Unfolding lemma for `jacobianWeak`: `J gx gy z = (gx z).re·(gy z).im − (gy z).re·(gx z).im`. -/
theorem jacobianWeak_def (gx gy : ℂ → ℂ) (z : ℂ) :
    jacobianWeak gx gy z = (gx z).re * (gy z).im - (gy z).re * (gx z).im := rfl

/-- **Weak `L²` convergence tested against `L²` functions.** The sequence `hₙ`
converges weakly in `L²(volume)` to `h` if the pairing `∫ (hₙ z) * ψ z` converges to
`∫ (h z) * ψ z` for every complex `L²(volume)` test function `ψ`. This is the concrete
integral-pairing form of weak `L²` convergence; the Hilbert inner-product convergence
of `exists_weak_subseq_of_bounded` specializes to it. -/
def TendstoWeaklyL2 (hₙ : ℕ → ℂ → ℂ) (h : ℂ → ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, MemLp ψ 2 volume →
    Filter.Tendsto (fun n => ∫ z, hₙ n z * ψ z) Filter.atTop (nhds (∫ z, h z * ψ z))

/-- The real determinant of the differential in the two coordinate partial
derivatives: `det (Df) = (∂ₓ(Re f))(∂ᵧ(Im f)) − (∂ᵧ(Re f))(∂ₓ(Im f))`. Equivalently,
in terms of the complex partials `∂ₓf`, `∂ᵧf` this is
`(∂ₓf).re·(∂ᵧf).im − (∂ᵧf).re·(∂ₓf).im`. -/
theorem det_fderiv_eq_partials (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℝ f z).det = (partialX f z).re * (partialY f z).im
      - (partialY f z).re * (partialX f z).im := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f z with hA
  have key : ∀ M : ℂ →ₗ[ℝ] ℂ, LinearMap.det M
      = (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI M).det := fun M =>
    (LinearMap.det_toMatrix Complex.basisOneI M).symm
  have hdet : A.det = (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
    rw [ContinuousLinearMap.det, key]
    have hb0 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 0 = (1 : ℂ) := by
      simp [Complex.coe_basisOneI]
    have hb1 : (Complex.basisOneI : Module.Basis (Fin 2) ℝ ℂ) 1 = Complex.I := by
      simp [Complex.coe_basisOneI]
    have c00 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 0 = (A 1).re := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c10 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 0 = (A 1).im := by
      rw [LinearMap.toMatrix_apply, hb0, Complex.coe_basisOneI_repr]
      rfl
    have c01 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 0 1 = (A Complex.I).re := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have c11 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ)) 1 1 = (A Complex.I).im := by
      rw [LinearMap.toMatrix_apply, hb1, Complex.coe_basisOneI_repr]
      rfl
    have h0 : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (↑A : ℂ →ₗ[ℝ] ℂ))
        = !![(A 1).re, (A Complex.I).re; (A 1).im, (A Complex.I).im] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one] <;>
        first | exact c00 | exact c01 | exact c10 | exact c11
    rw [h0, Matrix.det_fin_two_of]; ring
  have hx : partialX f z = A 1 := by rw [partialX_def, hA]
  have hy : partialY f z = A Complex.I := by rw [partialY_def, hA]
  rw [hx, hy, hdet]; ring

/-- **(J1) Null-Lagrangian integration-by-parts identity, `C²` case.** For a
twice–continuously-differentiable `f : ℂ → ℂ` and a smooth compactly supported real
test function `φ`, the Jacobian determinant integrates by parts to a first-order
expression against `Re f`:
`∫ (J f)·φ = ∫ (Re f)·(∂ₓ(Im f)·∂ᵧφ − ∂ᵧ(Im f)·∂ₓφ)`.

The `C²` hypothesis is used exactly to cancel the mixed second partials
`∂ᵧ∂ₓ(Im f) = ∂ₓ∂ᵧ(Im f)` (Clairaut / `second_derivative_symmetric`). -/
theorem integral_jacobian_smul_eq (hf : ContDiff ℝ 2 f)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ z, (fderiv ℝ f z).det * φ z
      = ∫ z, (f z).re * ((partialX f z).im * (fderiv ℝ φ z) Complex.I
          - (partialY f z).im * (fderiv ℝ φ z) 1) := by
  -- Real components of `f`; both are `C²`.
  set u : ℂ → ℝ := fun z => (f z).re with hu_def
  set p : ℂ → ℝ := fun z => (f z).im with hp_def
  have hu_c2 : ContDiff ℝ 2 u := by
    rw [hu_def]
    have := Complex.reCLM.contDiff.comp hf
    simpa [Function.comp] using this
  have hp_c2 : ContDiff ℝ 2 p := by
    rw [hp_def]
    have := Complex.imCLM.contDiff.comp hf
    simpa [Function.comp] using this
  have hu_diff : Differentiable ℝ u := hu_c2.differentiable (by norm_num)
  have hp_diff : Differentiable ℝ p := hp_c2.differentiable (by norm_num)
  -- `fderiv ℝ p` is `C¹`, hence differentiable.
  have hfp_c1 : ContDiff ℝ 1 (fderiv ℝ p) := hp_c2.fderiv_right (by norm_num)
  have hfp_diff : Differentiable ℝ (fderiv ℝ p) := hfp_c1.differentiable (by norm_num)
  -- The two first partials of `p`, with their smoothness.
  set px : ℂ → ℝ := fun z => (fderiv ℝ p z) 1 with hpx_def
  set py : ℂ → ℝ := fun z => (fderiv ℝ p z) Complex.I with hpy_def
  have hpx_c1 : ContDiff ℝ 1 px := by
    rw [hpx_def]; exact hfp_c1.clm_apply contDiff_const
  have hpy_c1 : ContDiff ℝ 1 py := by
    rw [hpy_def]; exact hfp_c1.clm_apply contDiff_const
  have hpx_diff : Differentiable ℝ px := by
    rw [hpx_def]; exact fun z => (hfp_diff z).clm_apply (differentiableAt_const _)
  have hpy_diff : Differentiable ℝ py := by
    rw [hpy_def]; exact fun z => (hfp_diff z).clm_apply (differentiableAt_const _)
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_c1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hu_c1 : ContDiff ℝ 1 u := hu_c2.of_le (by norm_num)
  -- Bridge: directional partials of `u`, `p` are the components of those of `f`.
  have hbridge_re : ∀ (z w : ℂ), (fderiv ℝ u z) w = ((fderiv ℝ f z) w).re := by
    intro z w
    have hfd : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiable (by norm_num) z).hasFDerivAt
    have hcomp : HasFDerivAt u (Complex.reCLM.comp (fderiv ℝ f z)) z := by
      rw [hu_def]
      have := (Complex.reCLM.hasFDerivAt (x := f z)).comp z hfd
      simpa [Function.comp] using this
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have hbridge_im : ∀ (z w : ℂ), (fderiv ℝ p z) w = ((fderiv ℝ f z) w).im := by
    intro z w
    have hfd : HasFDerivAt f (fderiv ℝ f z) z := (hf.differentiable (by norm_num) z).hasFDerivAt
    have hcomp : HasFDerivAt p (Complex.imCLM.comp (fderiv ℝ f z)) z := by
      rw [hp_def]
      have := (Complex.imCLM.hasFDerivAt (x := f z)).comp z hfd
      simpa [Function.comp] using this
    rw [hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  -- Differentiating the evaluation of `fderiv ℝ p` at a constant direction.
  have hclm_apply : ∀ (c d z : ℂ),
      (fderiv ℝ (fun w => (fderiv ℝ p w) c) z) d = ((fderiv ℝ (fderiv ℝ p) z) d) c := by
    intro c d z
    have hc : HasFDerivAt (fderiv ℝ p) (fderiv ℝ (fderiv ℝ p) z) z := (hfp_diff z).hasFDerivAt
    have hcst : HasFDerivAt (fun _ : ℂ => c) (0 : ℂ →L[ℝ] ℂ) z := hasFDerivAt_const c z
    rw [(hc.clm_apply hcst).fderiv]
    simp
  -- A coordinate partial of a compactly supported `C¹` real function integrates to `0`.
  have hvanish : ∀ (G : ℂ → ℝ) (w : ℂ), ContDiff ℝ 1 G → HasCompactSupport G →
      ∫ z, (fderiv ℝ G z) w = 0 := by
    intro G w hG hGc
    set cf : ℂ → ℝ := fun _ => (1 : ℝ) with hcf
    have hGcont : Continuous G := hG.continuous
    have hdcont : Continuous (fun z => (fderiv ℝ G z) w) :=
      (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdcs : HasCompactSupport (fun z => (fderiv ℝ G z) w) :=
      HasCompactSupport.fderiv_apply ℝ hGc w
    have h1 : Integrable (fun z => (fderiv ℝ cf z) w • G z) volume := by
      have he : (fun z => (fderiv ℝ cf z) w • G z) = fun _ => (0 : ℝ) := by
        funext z; simp [hcf]
      rw [he]; exact integrable_zero _ _ _
    have h2 : Integrable (fun z => cf z • (fderiv ℝ G z) w) volume := by
      have he : (fun z => cf z • (fderiv ℝ G z) w) = fun z => (fderiv ℝ G z) w := by
        funext z; simp [hcf]
      rw [he]; exact hdcont.integrable_of_hasCompactSupport hdcs
    have h3 : Integrable (fun z => cf z • G z) volume := by
      have he : (fun z => cf z • G z) = G := by funext z; simp [hcf]
      rw [he]; exact hGcont.integrable_of_hasCompactSupport hGc
    have hdf1 : ∀ x ∈ tsupport G, DifferentiableAt ℝ cf x :=
      fun x _ => (differentiable_const (1 : ℝ)).differentiableAt
    have hdf2 : ∀ x ∈ tsupport cf, DifferentiableAt ℝ G x :=
      fun x _ => (hG.differentiable (by norm_num)).differentiableAt
    have L := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3 hdf1 hdf2
    have hrw1 : (fun z => cf z • (fderiv ℝ G z) w) = fun z => (fderiv ℝ G z) w := by
      funext z; simp [hcf]
    have hrw2 : (fun z => (fderiv ℝ cf z) w • G z) = fun _ => (0 : ℝ) := by
      funext z; simp [hcf]
    rw [hrw1, hrw2] at L
    simpa using L
  -- The two divergence fluxes: `P` is differentiated in `x`, `Q` in `y`.
  set P : ℂ → ℝ := fun z => u z * py z * φ z with hP_def
  set Q : ℂ → ℝ := fun z => u z * px z * φ z with hQ_def
  have hP_c1 : ContDiff ℝ 1 P := by
    rw [hP_def]; exact (hu_c1.mul hpy_c1).mul hφ_c1
  have hQ_c1 : ContDiff ℝ 1 Q := by
    rw [hQ_def]; exact (hu_c1.mul hpx_c1).mul hφ_c1
  have hP_cs : HasCompactSupport P := by
    rw [hP_def]; exact hφc.mul_left
  have hQ_cs : HasCompactSupport Q := by
    rw [hQ_def]; exact hφc.mul_left
  -- Product rule for a triple product, evaluated at a direction `v`.
  have htriple : ∀ (a b c : ℂ → ℝ) (z v : ℂ), DifferentiableAt ℝ a z → DifferentiableAt ℝ b z →
      DifferentiableAt ℝ c z →
      (fderiv ℝ (fun z => a z * b z * c z) z) v
        = (fderiv ℝ a z) v * b z * c z + a z * (fderiv ℝ b z) v * c z
          + a z * b z * (fderiv ℝ c z) v := by
    intro a b c z v ha hb hc
    have hab : DifferentiableAt ℝ (fun z => a z * b z) z := ha.mul hb
    rw [show (fun z => a z * b z * c z) = (fun z => a z * b z) * c from rfl]
    rw [fderiv_mul hab hc]
    rw [show (fun z => a z * b z) = a * b from rfl, fderiv_mul ha hb]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- Pointwise divergence identity: the second derivatives of `p` cancel by Clairaut.
  have hpt : ∀ z, ((fderiv ℝ u z) 1 * py z - (fderiv ℝ u z) Complex.I * px z) * φ z
      = ((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I)
        + u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
    intro z
    have hdP := htriple u py φ z 1 (hu_diff z) (hpy_diff z) (hφ_diff z)
    have hdQ := htriple u px φ z Complex.I (hu_diff z) (hpx_diff z) (hφ_diff z)
    rw [hP_def, hQ_def, hdP, hdQ]
    have hmix1 : (fderiv ℝ py z) 1 = ((fderiv ℝ (fderiv ℝ p) z) 1) Complex.I := by
      rw [hpy_def]; exact hclm_apply Complex.I 1 z
    have hmix2 : (fderiv ℝ px z) Complex.I = ((fderiv ℝ (fderiv ℝ p) z) Complex.I) 1 := by
      rw [hpx_def]; exact hclm_apply 1 Complex.I z
    have hclairaut : ((fderiv ℝ (fderiv ℝ p) z) 1) Complex.I
        = ((fderiv ℝ (fderiv ℝ p) z) Complex.I) 1 := by
      have hff : ∀ y, HasFDerivAt p (fderiv ℝ p y) y := fun y => (hp_diff y).hasFDerivAt
      have hff' : HasFDerivAt (fderiv ℝ p) (fderiv ℝ (fderiv ℝ p) z) z :=
        (hfp_diff z).hasFDerivAt
      exact second_derivative_symmetric hff hff' 1 Complex.I
    rw [hmix1, hmix2, hclairaut]
    ring
  -- The determinant integrand in terms of the real partials.
  have hdet_eq : ∀ z, (fderiv ℝ f z).det * φ z
      = ((fderiv ℝ u z) 1 * py z - (fderiv ℝ u z) Complex.I * px z) * φ z := by
    intro z
    rw [det_fderiv_eq_partials f z]
    have h1 : (partialX f z).re = (fderiv ℝ u z) 1 := by
      simp only [partialX_def]; exact (hbridge_re z 1).symm
    have h2 : (partialY f z).im = py z := by
      simp only [partialY_def, hpy_def]; exact (hbridge_im z Complex.I).symm
    have h3 : (partialY f z).re = (fderiv ℝ u z) Complex.I := by
      simp only [partialY_def]; exact (hbridge_re z Complex.I).symm
    have h4 : (partialX f z).im = px z := by
      simp only [partialX_def, hpx_def]; exact (hbridge_im z 1).symm
    rw [h1, h2, h3, h4]
  -- The target right-hand integrand in terms of the real partials.
  have hrhs_eq : ∀ z, (f z).re * ((partialX f z).im * (fderiv ℝ φ z) Complex.I
        - (partialY f z).im * (fderiv ℝ φ z) 1)
      = u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
    intro z
    have h4 : (partialX f z).im = px z := by
      simp only [partialX_def, hpx_def]; exact (hbridge_im z 1).symm
    have h2 : (partialY f z).im = py z := by
      simp only [partialY_def, hpy_def]; exact (hbridge_im z Complex.I).symm
    rw [h4, h2, hu_def]
  -- Integrability of the flux divergence and of the first-order remainder.
  have hintP : Integrable (fun z => (fderiv ℝ P z) 1) volume := by
    have hcP : Continuous (fun z => (fderiv ℝ P z) 1) :=
      (hP_c1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcP.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hP_cs 1)
  have hintQ : Integrable (fun z => (fderiv ℝ Q z) Complex.I) volume := by
    have hcQ : Continuous (fun z => (fderiv ℝ Q z) Complex.I) :=
      (hQ_c1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hcQ.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hQ_cs Complex.I)
  have hintR : Integrable (fun z =>
      u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) volume := by
    have hcφI : Continuous (fun z => (fderiv ℝ φ z) Complex.I) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcφ1 : Continuous (fun z => (fderiv ℝ φ z) 1) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcont : Continuous (fun z =>
        u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) :=
      hu_c2.continuous.mul ((hpx_c1.continuous.mul hcφI).sub (hpy_c1.continuous.mul hcφ1))
    have hcs : HasCompactSupport (fun z =>
        u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) := by
      have hsI : HasCompactSupport (fun z => px z * (fderiv ℝ φ z) Complex.I) :=
        (HasCompactSupport.fderiv_apply ℝ hφc Complex.I).mul_left
      have hs1 : HasCompactSupport (fun z => py z * (fderiv ℝ φ z) 1) :=
        (HasCompactSupport.fderiv_apply ℝ hφc 1).mul_left
      have hsub : HasCompactSupport (fun z =>
          px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
        simpa [sub_eq_add_neg] using hsI.add hs1.neg
      exact hsub.mul_left
    exact hcont.integrable_of_hasCompactSupport hcs
  -- Assemble: integrate the pointwise identity; the flux terms vanish.
  calc ∫ z, (fderiv ℝ f z).det * φ z
      = ∫ z, (((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I)
          + u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1)) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hdet_eq z, hpt z]
    _ = (∫ z, ((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I))
          + ∫ z, u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) :=
        integral_add (hintP.sub hintQ) hintR
    _ = ∫ z, u z * (px z * (fderiv ℝ φ z) Complex.I - py z * (fderiv ℝ φ z) 1) := by
        have hsplit : (∫ z, ((fderiv ℝ P z) 1 - (fderiv ℝ Q z) Complex.I))
            = (∫ z, (fderiv ℝ P z) 1) - ∫ z, (fderiv ℝ Q z) Complex.I :=
          integral_sub hintP hintQ
        rw [hsplit, hvanish P 1 hP_c1 hP_cs, hvanish Q Complex.I hQ_c1 hQ_cs]
        simp
    _ = ∫ z, (f z).re * ((partialX f z).im * (fderiv ℝ φ z) Complex.I
          - (partialY f z).im * (fderiv ℝ φ z) 1) := by
        apply integral_congr_ae
        filter_upwards with z
        exact (hrhs_eq z).symm

set_option maxHeartbeats 400000 in
-- This mollification-and-limit proof carries a large local context (four Hölder
-- estimates, two dominating sequences, per-`n` integrability), so the elaboration
-- of its `calc` chains exceeds the default heartbeat budget.
/-- **(J2) Null-Lagrangian identity, `W^{1,2}` case.** For a continuous `W^{1,2}_loc`
map `f` with weak partial derivatives `gx` (direction `1`) and `gy` (direction `I`),
both locally `L²`, the weak Jacobian integrates by parts against a smooth compactly
supported real test function `φ`:
`∫ (jacobianWeak gx gy)·φ = ∫ (Re f)·((Im gx)·∂ᵧφ − (Im gy)·∂ₓφ)`.

Obtained from `integral_jacobian_smul_eq` by mollification: the mollifications `fε` are
`C^∞`, converge locally uniformly to `f`, and their differentials converge to `(gx, gy)`
in `L²_loc`; the quadratic left-hand side and the bilinear right-hand side both pass to
the limit. -/
theorem integral_jacobianWeak_smul_eq (hfcont : Continuous f)
    (hdiff : ∀ᵐ z, DifferentiableAt ℝ f z) (hW12 : MemW12loc f)
    {gx gy : ℂ → ℂ} (hg : HasWeakGradient gx gy f Set.univ)
    (hgx : MemLpLocOn gx 2 Set.univ) (hgy : MemLpLocOn gy 2 Set.univ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ z, jacobianWeak gx gy z * φ z
      = ∫ z, (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1) := by
  classical
  -- The support of the test function and an enclosing ball.
  set K : Set ℂ := tsupport φ with hK_def
  have hKc : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  obtain ⟨R, hKR⟩ := hKc.isBounded.subset_ball (0 : ℂ)
  have hK2 : K ⊆ Metric.ball (0 : ℂ) (R + 2) :=
    hKR.trans (Metric.ball_subset_ball (by linarith))
  -- Local integrability of `f`, `gx`, `gy`.
  have hfLI : LocallyIntegrable f := hfcont.locallyIntegrable
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ → LocallyIntegrable g := by
    intro g hgl
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((hgl k (Set.subset_univ _) hk).mono_exponent (by norm_num))
  have hgxLI : LocallyIntegrable gx := memLpLoc_to_loc hgx
  have hgyLI : LocallyIntegrable gy := memLpLoc_to_loc hgy
  have hfLp : MemLpLocOn f 2 Set.univ := by
    intro k _ hkc
    haveI : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hkc.measure_lt_top⟩
    obtain ⟨Cf', hCf'⟩ := hkc.exists_bound_of_continuousOn hfcont.continuousOn
    refine MemLp.of_bound hfcont.aestronglyMeasurable.restrict Cf' ?_
    rw [ae_restrict_iff' hkc.isClosed.measurableSet]
    exact ae_of_all _ hCf'
  -- The mollifier sequence, with outer radius tending to `0`.
  set φb : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨((n : ℝ) + 2)⁻¹, 2 * ((n : ℝ) + 2)⁻¹, by positivity, by
      have h2 : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
      linarith⟩ with hφb_def
  have hrout : Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 := h1.inv_tendsto_atTop.const_mul (2 : ℝ)
    have he : (fun n => (φb n).rOut) = fun n : ℕ => 2 * ((n : ℝ) + 2)⁻¹ := rfl
    rw [he]
    simpa using h3
  set ρ : ℕ → ℂ → ℝ := fun n => (φb n).normed volume with hρ_def
  have hρsm : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ n) := fun n =>
    (φb n).contDiff_normed (n := ⊤)
  have hρcs : ∀ n, HasCompactSupport (ρ n) := fun n => (φb n).hasCompactSupport_normed
  -- Smoothness and continuity of the mollifications.
  have hFC2 : ∀ n, ContDiff ℝ 2
      (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n => by
    have := HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρcs n) ((φb n).contDiff_normed (n := 2)) hfLI
    exact_mod_cast this
  have hXc : ∀ n, Continuous
      (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρcs n)
      ((φb n).contDiff_normed (n := 0)).continuous hgxLI
  have hYc : ∀ n, Continuous
      (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n =>
    HasCompactSupport.continuous_convolution_left _ (hρcs n)
      ((φb n).contDiff_normed (n := 0)).continuous hgyLI
  have hFc : ∀ n, Continuous
      (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) := fun n =>
    (hFC2 n).continuous
  -- The two partial derivatives of the mollification are the mollified weak partials.
  have hpx : ∀ n z, partialX (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
      = convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z := fun n z => by
    rw [partialX_def]
    exact fderiv_convolution_normed_apply_eq hg.1 hfLI hgxLI (hρsm n) (hρcs n) z
  have hpy : ∀ n z, partialY (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
      = convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z := fun n z => by
    rw [partialY_def]
    exact fderiv_convolution_normed_apply_eq hg.2 hfLI hgyLI (hρsm n) (hρcs n) z
  -- J1 applied to each mollification, rewritten through the identified partials.
  have hJ1 : ∀ n, ∫ z, (fderiv ℝ (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) z).det * φ z
      = ∫ z, (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((partialX (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) Complex.I
            - (partialY (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) 1) := fun n =>
    integral_jacobian_smul_eq (hFC2 n) hφ hφc
  have hAB : ∀ n, ∫ z, jacobianWeak
        (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
      = ∫ z, (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := by
    intro n
    have h1 : (fun z => jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z)
        = fun z => (fderiv ℝ (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ)
            volume) z).det * φ z := by
      funext z
      rw [det_fderiv_eq_partials (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ)
        volume) z, hpx n z, hpy n z, jacobianWeak_def]
    have h2 : (fun z => (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((partialX (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) Complex.I
            - (partialY (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) z).im
              * (fderiv ℝ φ z) 1))
        = fun z => (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := by
      funext z; rw [hpx n z, hpy n z]
    rw [h1, hJ1 n, h2]
  -- Truncation of a locally-`L²` function to a global `L²` function.
  have htrunc : ∀ {h : ℂ → ℂ}, MemLpLocOn h 2 Set.univ →
      MemLp ((Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume := by
    intro h hh
    rw [memLp_indicator_iff_restrict measurableSet_ball]
    exact (hh (Metric.closedBall 0 (R + 2)) (Set.subset_univ _)
      (isCompact_closedBall _ _)).mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  -- Squared `eLpNorm` as a squared-`enorm` integral.
  have heLpSq : ∀ (μ : Measure ℂ) (h : ℂ → ℂ),
      (eLpNorm h 2 μ) ^ 2 = ∫⁻ z, ‖h z‖ₑ ^ 2 ∂μ := by
    intro μ h
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num]
    have hin : (∫⁻ z, ‖h z‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ z, ‖h z‖ₑ ^ 2 ∂μ := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast (‖h z‖ₑ) 2]; norm_num
    rw [hin, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  -- Convolution on `K` only sees the truncation once the bump radius is `≤ 1`.
  have hconv_trunc : ∀ (h : ℂ → ℂ), ∀ n, (φb n).rOut ≤ 1 → ∀ z ∈ K,
      convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z
        = convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro h n hr1 z hz
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    by_cases ht : ρ n t = 0
    · simp [ht]
    · have htsupp : t ∈ Function.support (ρ n) := ht
      simp only [hρ_def] at htsupp
      rw [(φb n).support_normed_eq] at htsupp
      rw [Metric.mem_ball, dist_zero_right] at htsupp
      have hzR : ‖z‖ < R := by
        have := hKR hz
        rwa [Metric.mem_ball, dist_zero_right] at this
      have hmem : z - t ∈ Metric.ball (0 : ℂ) (R + 2) := by
        rw [Metric.mem_ball, dist_zero_right]
        have ht1 : ‖t‖ < 1 := lt_of_lt_of_le htsupp hr1
        calc ‖z - t‖ ≤ ‖z‖ + ‖t‖ := norm_sub_le _ _
          _ < R + 2 := by linarith
      rw [Set.indicator_of_mem hmem]
  -- The `K`-localized `L²` convergence of the mollification to the function.
  have hloc : ∀ (h : ℂ → ℂ), LocallyIntegrable h → MemLpLocOn h 2 Set.univ →
      Filter.Tendsto (fun n => ∫⁻ z in K,
        ‖convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z‖ₑ ^ 2)
        Filter.atTop (nhds 0) := by
    intro h hLI hLp
    have hT2 : MemLp ((Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume := htrunc hLp
    have hE : Filter.Tendsto (fun n => eLpNorm
        (convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          - (Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume)
        Filter.atTop (nhds 0) :=
      eLpNorm_convolution_normed_sub_tendsto_zero hT2 φb hrout
    have hev : ∀ᶠ n in Filter.atTop, (φb n).rOut ≤ 1 :=
      hrout.eventually (eventually_le_nhds one_pos)
    have hbd : ∀ᶠ n in Filter.atTop, (∫⁻ z in K,
        ‖convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z‖ₑ ^ 2)
        ≤ (eLpNorm (convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume
          - (Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume) ^ 2 := by
      filter_upwards [hev] with n hr1
      calc (∫⁻ z in K,
          ‖convolution (ρ n) h (ContinuousLinearMap.lsmul ℝ ℝ) volume z - h z‖ₑ ^ 2)
          = ∫⁻ z in K, ‖convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - (Metric.ball (0 : ℂ) (R + 2)).indicator h z‖ₑ ^ 2 := by
            refine setLIntegral_congr_fun hKm fun z hz => ?_
            rw [hconv_trunc h n hr1 z hz, Set.indicator_of_mem (hK2 hz)]
        _ ≤ ∫⁻ z, ‖convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - (Metric.ball (0 : ℂ) (R + 2)).indicator h z‖ₑ ^ 2 :=
            setLIntegral_le_lintegral _ _
        _ = (eLpNorm (convolution (ρ n) ((Metric.ball (0 : ℂ) (R + 2)).indicator h)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume
            - (Metric.ball (0 : ℂ) (R + 2)).indicator h) 2 volume) ^ 2 :=
            (heLpSq volume _).symm
    have hE2 := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp hE
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => zero_le _) hbd
    simpa [Function.comp] using hE2
  have hTf := hloc f hfLI hfLp
  have hTx := hloc gx hgxLI hgx
  have hTy := hloc gy hgyLI hgy
  -- Finite masses of `gx`, `gy` on `K`.
  have hgxK : MemLp gx 2 (volume.restrict K) := hgx K (Set.subset_univ K) hKc
  have hgyK : MemLp gy 2 (volume.restrict K) := hgy K (Set.subset_univ K) hKc
  have hGX : (∫⁻ z in K, ‖gx z‖ₑ ^ 2) < ⊤ := by
    rw [← heLpSq (volume.restrict K) gx]
    exact ENNReal.pow_lt_top hgxK.2
  have hGY : (∫⁻ z in K, ‖gy z‖ₑ ^ 2) < ⊤ := by
    rw [← heLpSq (volume.restrict K) gy]
    exact ENNReal.pow_lt_top hgyK.2
  have hvolK : volume K < ⊤ := hKc.measure_lt_top
  -- The `(a+b)² ≤ 2(a²+b²)` inequality in `ℝ≥0∞`.
  have hsq2 : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    intro a b
    have hkey := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (by norm_num : (1 : ℝ) ≤ 2)
    have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
    rw [htwo] at hkey
    rw [← ENNReal.rpow_natCast (a + b) 2, ← ENNReal.rpow_natCast a 2,
      ← ENNReal.rpow_natCast b 2]
    push_cast
    exact hkey
  -- Cauchy–Schwarz for the lower integral on `K`.
  have holder : ∀ (u v : ℂ → ℝ≥0∞), AEMeasurable u (volume.restrict K) →
      AEMeasurable v (volume.restrict K) →
      ∫⁻ z in K, u z * v z
        ≤ (∫⁻ z in K, u z ^ 2) ^ (1/2 : ℝ) * (∫⁻ z in K, v z ^ 2) ^ (1/2 : ℝ) := by
    intro u v hu hv
    have h2 : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
    have hup : (∫⁻ z in K, u z ^ (2 : ℝ)) = ∫⁻ z in K, u z ^ 2 := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast (u z) 2]; norm_num
    have hvp : (∫⁻ z in K, v z ^ (2 : ℝ)) = ∫⁻ z in K, v z ^ 2 := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast (v z) 2]; norm_num
    have hmain := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict K) h2 hu hv
    rw [hup, hvp] at hmain
    exact hmain
  -- Mass comparison: an `L²`-mass within distance `1` of a fixed one is controlled.
  have hmass : ∀ (u g0 : ℂ → ℂ), AEStronglyMeasurable u (volume.restrict K) →
      AEStronglyMeasurable g0 (volume.restrict K) →
      (∫⁻ z in K, ‖u z - g0 z‖ₑ ^ 2) ≤ 1 →
      (∫⁻ z in K, ‖u z‖ₑ ^ 2) ≤ 2 * (1 + ∫⁻ z in K, ‖g0 z‖ₑ ^ 2) := by
    intro u g0 hu hg0 hle
    have hpt : ∀ z, ‖u z‖ₑ ^ 2 ≤ 2 * (‖u z - g0 z‖ₑ ^ 2 + ‖g0 z‖ₑ ^ 2) := by
      intro z
      calc ‖u z‖ₑ ^ 2 = ‖(u z - g0 z) + g0 z‖ₑ ^ 2 := by rw [sub_add_cancel]
        _ ≤ (‖u z - g0 z‖ₑ + ‖g0 z‖ₑ) ^ 2 := by
            gcongr
            exact enorm_add_le _ _
        _ ≤ 2 * (‖u z - g0 z‖ₑ ^ 2 + ‖g0 z‖ₑ ^ 2) := hsq2 _ _
    have hmeas : AEMeasurable (fun z => ‖u z - g0 z‖ₑ ^ 2) (volume.restrict K) :=
      ((hu.sub hg0).enorm).pow_const 2
    calc (∫⁻ z in K, ‖u z‖ₑ ^ 2)
        ≤ ∫⁻ z in K, 2 * (‖u z - g0 z‖ₑ ^ 2 + ‖g0 z‖ₑ ^ 2) := lintegral_mono hpt
      _ = 2 * ((∫⁻ z in K, ‖u z - g0 z‖ₑ ^ 2) + ∫⁻ z in K, ‖g0 z‖ₑ ^ 2) := by
          rw [lintegral_const_mul' 2 _ (by norm_num), lintegral_add_left' hmeas]
      _ ≤ 2 * (1 + ∫⁻ z in K, ‖g0 z‖ₑ ^ 2) := by gcongr
  -- The global bound on the test function, and componentwise `L²` truncations.
  obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hφe : ∀ z, ‖φ z‖ₑ ≤ ENNReal.ofReal Cφ := by
    intro z
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by rw [← Real.norm_eq_abs]; exact hCφ z)
  have hmemRe : ∀ (g0 : ℂ → ℂ), MemLp g0 2 (volume.restrict K) →
      MemLp (K.indicator fun z => (g0 z).re) 2 volume := by
    intro g0 hg0
    rw [memLp_indicator_iff_restrict hKm]
    refine hg0.norm.mono'
      (Complex.continuous_re.comp_aestronglyMeasurable hg0.aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have hmemIm : ∀ (g0 : ℂ → ℂ), MemLp g0 2 (volume.restrict K) →
      MemLp (K.indicator fun z => (g0 z).im) 2 volume := by
    intro g0 hg0
    rw [memLp_indicator_iff_restrict hKm]
    refine hg0.norm.mono'
      (Complex.continuous_im.comp_aestronglyMeasurable hg0.aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  -- Pointwise four-term bound for a difference of Jacobians.
  have hjac_pt : ∀ a b c d : ℂ,
      ‖(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)‖ₑ
        ≤ ‖a - c‖ₑ * ‖b‖ₑ + ‖c‖ₑ * ‖b - d‖ₑ
          + (‖b - d‖ₑ * ‖a‖ₑ + ‖d‖ₑ * ‖a - c‖ₑ) := by
    intro a b c d
    have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
    have h1 : (a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)
        = ((a - c).re * b.im + c.re * (b - d).im)
          - ((b - d).re * a.im + d.re * (a - c).im) := by
      simp only [Complex.sub_re, Complex.sub_im]; ring
    have habs : |(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)|
        ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ + (‖b - d‖ * ‖a‖ + ‖d‖ * ‖a - c‖) := by
      rw [h1]
      have t1 := habs_sub ((a - c).re * b.im + c.re * (b - d).im)
        ((b - d).re * a.im + d.re * (a - c).im)
      have t2 : |(a - c).re * b.im + c.re * (b - d).im|
          ≤ |(a - c).re| * |b.im| + |c.re| * |(b - d).im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
      have t3 : |(b - d).re * a.im + d.re * (a - c).im|
          ≤ |(b - d).re| * |a.im| + |d.re| * |(a - c).im| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
      have b1 : |(a - c).re| * |b.im| ≤ ‖a - c‖ * ‖b‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      have b2 : |c.re| * |(b - d).im| ≤ ‖c‖ * ‖b - d‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      have b3 : |(b - d).re| * |a.im| ≤ ‖b - d‖ * ‖a‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      have b4 : |d.re| * |(a - c).im| ≤ ‖d‖ * ‖a - c‖ := by
        gcongr
        · exact Complex.abs_re_le_norm _
        · exact Complex.abs_im_le_norm _
      linarith
    calc ‖(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)‖ₑ
        = ENNReal.ofReal
            |(a.re * b.im - b.re * a.im) - (c.re * d.im - d.re * c.im)| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖
            + (‖b - d‖ * ‖a‖ + ‖d‖ * ‖a - c‖)) := ENNReal.ofReal_le_ofReal habs
      _ = ‖a - c‖ₑ * ‖b‖ₑ + ‖c‖ₑ * ‖b - d‖ₑ
            + (‖b - d‖ₑ * ‖a‖ₑ + ‖d‖ₑ * ‖a - c‖ₑ) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
            ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _)]
          simp only [ofReal_norm_eq_enorm]
  -- Measurability data on `K`.
  have hgxm : AEStronglyMeasurable gx (volume.restrict K) := hgxK.aestronglyMeasurable
  have hgym : AEStronglyMeasurable gy (volume.restrict K) := hgyK.aestronglyMeasurable
  -- Passage to the limit on both sides of the per-`n` identity.
  have hAtend : Filter.Tendsto (fun n => ∫ z, jacobianWeak
        (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z)
      Filter.atTop (nhds (∫ z, jacobianWeak gx gy z * φ z)) := by
    -- Integrability of the target.
    have h1 : Integrable ((K.indicator fun z => (gx z).re)
        * (K.indicator fun z => (gy z).im)) volume :=
      (hmemRe gx hgxK).integrable_mul (hmemIm gy hgyK)
    have h2 : Integrable ((K.indicator fun z => (gy z).re)
        * (K.indicator fun z => (gx z).im)) volume :=
      (hmemRe gy hgyK).integrable_mul (hmemIm gx hgxK)
    have h1' : Integrable (fun z => φ z * ((K.indicator fun w => (gx w).re) z
        * (K.indicator fun w => (gy w).im) z)) volume :=
      h1.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all _ hCφ)
    have h2' : Integrable (fun z => φ z * ((K.indicator fun w => (gy w).re) z
        * (K.indicator fun w => (gx w).im) z)) volume :=
      h2.bdd_mul hφ.continuous.aestronglyMeasurable (ae_of_all _ hCφ)
    have heq : (fun z => jacobianWeak gx gy z * φ z)
        = fun z => φ z * ((K.indicator fun w => (gx w).re) z
            * (K.indicator fun w => (gy w).im) z)
          - φ z * ((K.indicator fun w => (gy w).re) z
            * (K.indicator fun w => (gx w).im) z) := by
      funext z
      by_cases hz : z ∈ K
      · simp only [Set.indicator_of_mem hz, jacobianWeak]
        ring
      · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [jacobianWeak, hφz]
    have hA_int : Integrable (fun z => jacobianWeak gx gy z * φ z) volume := by
      rw [heq]; exact h1'.sub h2'
    -- Integrability of each approximant.
    have hAn_int : ∀ n, Integrable (fun z => jacobianWeak
        (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
        (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z) volume := by
      intro n
      have hjc : Continuous (fun z => jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z) :=
        ((Complex.continuous_re.comp (hXc n)).mul
            (Complex.continuous_im.comp (hYc n))).sub
          ((Complex.continuous_re.comp (hYc n)).mul (Complex.continuous_im.comp (hXc n)))
      exact (hjc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    -- The `L¹` convergence of the integrands, localized to `K`.
    refine tendsto_integral_of_L1 _ hA_int (Filter.Eventually.of_forall hAn_int) ?_
    have hred : ∀ n, (∫⁻ z, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ)
        = ∫⁻ z in K, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ := by
      intro n
      rw [← lintegral_indicator hKm]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [Set.indicator_of_notMem hz, hφz]
        simp
    -- Constants for the dominating sequence.
    set BX : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gx z‖ₑ ^ 2) with hBX_def
    set BY : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gy z‖ₑ ^ 2) with hBY_def
    have hBXfin : BX ≠ ⊤ := by
      rw [hBX_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGX⟩)).ne
    have hBYfin : BY ≠ ⊤ := by
      rw [hBY_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGY⟩)).ne
    have hGXfin : (∫⁻ z in K, ‖gx z‖ₑ ^ 2) ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hGX.ne).ne
    have hGYfin : (∫⁻ z in K, ‖gy z‖ₑ ^ 2) ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hGY.ne).ne
    -- The dominating sequence.
    set D : ℕ → ℝ≥0∞ := fun n =>
      ((∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ)
        + (∫⁻ z in K, ‖gx z‖ₑ ^ 2) ^ (1/2 : ℝ)
          * (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ)
        + ((∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ)
          + (∫⁻ z in K, ‖gy z‖ₑ ^ 2) ^ (1/2 : ℝ)
            * (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                - gx z‖ₑ ^ 2) ^ (1/2 : ℝ)))
        * ENNReal.ofReal Cφ with hD_def
    -- The dominating sequence tends to `0`.
    have hx12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gx z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTx
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hy12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gy z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTy
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hD0 : Filter.Tendsto D Filter.atTop (nhds 0) := by
      have hBY12 : BY ^ (1/2 : ℝ) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBYfin).ne
      have hBX12 : BX ^ (1/2 : ℝ) ≠ ⊤ :=
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBXfin).ne
      have t1 := ENNReal.Tendsto.mul_const hx12 (Or.inr hBY12)
      have t2 := ENNReal.Tendsto.const_mul hy12 (Or.inr hGXfin)
      have t3 := ENNReal.Tendsto.mul_const hy12 (Or.inr hBX12)
      have t4 := ENNReal.Tendsto.const_mul hx12 (Or.inr hGYfin)
      have hsum := (t1.add t2).add (t3.add t4)
      have hfin := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Cφ) hsum
        (Or.inr ENNReal.ofReal_ne_top)
      rw [hD_def]
      simpa using hfin
    -- The eventual domination.
    have hex1 := (ENNReal.tendsto_nhds_zero.mp hTx) 1 (by norm_num)
    have hey1 := (ENNReal.tendsto_nhds_zero.mp hTy) 1 (by norm_num)
    have hDbd : ∀ᶠ n in Filter.atTop, (∫⁻ z in K, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ) ≤ D n := by
      filter_upwards [hex1, hey1] with n hx1 hy1
      have hXm : AEStronglyMeasurable
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hXc n).aestronglyMeasurable.restrict
      have hYm : AEStronglyMeasurable
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hYc n).aestronglyMeasurable.restrict
      have hmassX := hmass _ gx hXm hgxm hx1
      have hmassY := hmass _ gy hYm hgym hy1
      -- the four `enorm` factors and their measurability
      have me1 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          (volume.restrict K) := (hXm.sub hgxm).enorm
      have me2 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          (volume.restrict K) := (hYm.sub hgym).enorm
      have me3 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hXm.enorm
      have me4 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hYm.enorm
      have mgx : AEMeasurable (fun z => ‖gx z‖ₑ) (volume.restrict K) := hgxm.enorm
      have mgy : AEMeasurable (fun z => ‖gy z‖ₑ) (volume.restrict K) := hgym.enorm
      -- Hölder estimates for the four products
      have e1 : (∫⁻ z in K,
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ
            * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ) := by
        refine (holder _ _ me1 me4).trans ?_
        gcongr
      have e2 : (∫⁻ z in K, ‖gx z‖ₑ
            * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          ≤ (∫⁻ z in K, ‖gx z‖ₑ ^ 2) ^ (1/2 : ℝ)
            * (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) := holder _ _ mgx me2
      have e3 : (∫⁻ z in K,
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ
            * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ) := by
        refine (holder _ _ me2 me3).trans ?_
        gcongr
      have e4 : (∫⁻ z in K, ‖gy z‖ₑ
            * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          ≤ (∫⁻ z in K, ‖gy z‖ₑ ^ 2) ^ (1/2 : ℝ)
            * (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) := holder _ _ mgy me1
      -- assemble
      calc (∫⁻ z in K, ‖jacobianWeak
            (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
            (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
          - jacobianWeak gx gy z * φ z‖ₑ)
          ≤ ∫⁻ z in K, ‖jacobianWeak
              (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
            - jacobianWeak gx gy z‖ₑ * ENNReal.ofReal Cφ := by
            refine lintegral_mono fun z => ?_
            have hz : jacobianWeak
                (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
                (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
                - jacobianWeak gx gy z * φ z
                = (jacobianWeak
                    (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
                    (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
                  - jacobianWeak gx gy z) * φ z := by ring
            rw [hz, enorm_mul]
            exact mul_le_mul' le_rfl (hφe z)
        _ = (∫⁻ z in K, ‖jacobianWeak
              (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
              (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
            - jacobianWeak gx gy z‖ₑ) * ENNReal.ofReal Cφ :=
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ D n := by
            rw [hD_def]
            refine mul_le_mul' ?_ le_rfl
            calc (∫⁻ z in K, ‖jacobianWeak
                  (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
                  (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z
                - jacobianWeak gx gy z‖ₑ)
                ≤ ∫⁻ z in K,
                    (‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                        - gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                    + ‖gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ
                    + (‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                      + ‖gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                            - gx z‖ₑ)) := by
                  refine lintegral_mono fun z => ?_
                  exact hjac_pt
                    (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
                    (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
                    (gx z) (gy z)
              _ = (∫⁻ z in K,
                    ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                        - gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
                  + (∫⁻ z in K, ‖gx z‖ₑ
                      * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ)
                  + ((∫⁻ z in K,
                      ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                          - gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
                    + ∫⁻ z in K, ‖gy z‖ₑ
                        * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
                            - gx z‖ₑ) := by
                  rw [lintegral_add_left' ((me1.mul me4).add (mgx.mul me2)),
                    lintegral_add_left' (me1.mul me4), lintegral_add_left' (me2.mul me3)]
              _ ≤ _ := add_le_add (add_le_add e1 e2) (add_le_add e3 e4)
    -- squeeze, then transfer from `K` back to the whole plane
    have hKlim : Filter.Tendsto (fun n => ∫⁻ z in K, ‖jacobianWeak
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume) z * φ z
        - jacobianWeak gx gy z * φ z‖ₑ) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD0
        (Filter.Eventually.of_forall fun n => zero_le _) hDbd
    exact hKlim.congr fun n => (hred n).symm
  have hBtend : Filter.Tendsto (fun n =>
      ∫ z, (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1))
      Filter.atTop (nhds (∫ z, (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1))) := by
    -- Continuity, compact support, and bounds for the test-function partials.
    have hqc : Continuous fun z => (fderiv ℝ φ z) Complex.I :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hpc : Continuous fun z => (fderiv ℝ φ z) 1 :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hqcs : HasCompactSupport fun z => (fderiv ℝ φ z) Complex.I :=
      HasCompactSupport.fderiv_apply ℝ hφc Complex.I
    have hpcs : HasCompactSupport fun z => (fderiv ℝ φ z) 1 :=
      HasCompactSupport.fderiv_apply ℝ hφc 1
    obtain ⟨Cq, hCq⟩ := hqcs.exists_bound_of_continuous hqc
    obtain ⟨Cp, hCp⟩ := hpcs.exists_bound_of_continuous hpc
    have hCq0 : 0 ≤ Cq := le_trans (norm_nonneg _) (hCq 0)
    have hCp0 : 0 ≤ Cp := le_trans (norm_nonneg _) (hCp 0)
    obtain ⟨Cf1, hCf1⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    set Cf : ℝ := max Cf1 0 with hCf_def
    have hCf : ∀ z ∈ K, ‖f z‖ ≤ Cf := fun z hz =>
      le_trans (hCf1 z hz) (le_max_left _ _)
    have hCf0 : 0 ≤ Cf := le_max_right _ _
    -- Vanishing of the partials off `K`.
    have hqzero : ∀ z, z ∉ K → (fderiv ℝ φ z) Complex.I = 0 := by
      intro z hz
      have hnot : z ∉ tsupport (fun x => (fderiv ℝ φ x) Complex.I) := fun hmem =>
        hz (tsupport_fderiv_apply_subset ℝ Complex.I hmem)
      have := image_eq_zero_of_notMem_tsupport (f := fun x => (fderiv ℝ φ x) Complex.I) hnot
      exact this
    have hpzero : ∀ z, z ∉ K → (fderiv ℝ φ z) 1 = 0 := by
      intro z hz
      have hnot : z ∉ tsupport (fun x => (fderiv ℝ φ x) 1) := fun hmem =>
        hz (tsupport_fderiv_apply_subset ℝ 1 hmem)
      have := image_eq_zero_of_notMem_tsupport (f := fun x => (fderiv ℝ φ x) 1) hnot
      exact this
    -- Integrability of the target.
    have hq2 : MemLp (fun z => (fderiv ℝ φ z) Complex.I) 2 volume :=
      hqc.memLp_of_hasCompactSupport hqcs
    have hp2 : MemLp (fun z => (fderiv ℝ φ z) 1) 2 volume :=
      hpc.memLp_of_hasCompactSupport hpcs
    have ht1 : Integrable ((K.indicator fun w => (gx w).im)
        * fun z => (fderiv ℝ φ z) Complex.I) volume :=
      (hmemIm gx hgxK).integrable_mul hq2
    have ht2 : Integrable ((K.indicator fun w => (gy w).im)
        * fun z => (fderiv ℝ φ z) 1) volume :=
      (hmemIm gy hgyK).integrable_mul hp2
    have heq1 : (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I)
        = (K.indicator fun w => (gx w).im) * fun z => (fderiv ℝ φ z) Complex.I := by
      funext z
      by_cases hz : z ∈ K
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz, hqzero z hz]
    have heq2 : (fun z => (gy z).im * (fderiv ℝ φ z) 1)
        = (K.indicator fun w => (gy w).im) * fun z => (fderiv ℝ φ z) 1 := by
      funext z
      by_cases hz : z ∈ K
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz, hpzero z hz]
    have hsub12 : Integrable (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I
        - (gy z).im * (fderiv ℝ φ z) 1) volume := by
      rw [show (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1)
        = (fun z => (gx z).im * (fderiv ℝ φ z) Complex.I)
          - fun z => (gy z).im * (fderiv ℝ φ z) 1 from rfl, heq1, heq2]
      exact ht1.sub ht2
    have hfreK : AEStronglyMeasurable (K.indicator fun w => (f w).re) volume :=
      (Complex.continuous_re.comp hfcont).aestronglyMeasurable.indicator hKm
    have hfreKbd : ∀ z, ‖(K.indicator fun w => (f w).re) z‖ ≤ Cf := by
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Real.norm_eq_abs]
        exact le_trans (Complex.abs_re_le_norm _) (hCf z hz)
      · rw [Set.indicator_of_notMem hz]
        simpa using hCf0
    have heqB : (fun z => (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
          - (gy z).im * (fderiv ℝ φ z) 1))
        = fun z => (K.indicator fun w => (f w).re) z
            * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1) := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hqzero z hz, hpzero z hz]
        ring
    have hB_int : Integrable (fun z => (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
        - (gy z).im * (fderiv ℝ φ z) 1)) volume := by
      rw [heqB]
      exact hsub12.bdd_mul hfreK (ae_of_all _ hfreKbd)
    -- Integrability of each approximant.
    have hBn_int : ∀ n, Integrable (fun z =>
        (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
          * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1)) volume := by
      intro n
      have hcont : Continuous (fun z =>
          (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)) :=
        (Complex.continuous_re.comp (hFc n)).mul
          (((Complex.continuous_im.comp (hXc n)).mul hqc).sub
            ((Complex.continuous_im.comp (hYc n)).mul hpc))
      have hcs : HasCompactSupport (fun z =>
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I
            - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := by
        have h1 : HasCompactSupport (fun z =>
            (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) Complex.I) := hqcs.mul_left
        have h2 : HasCompactSupport (fun z =>
            (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
              * (fderiv ℝ φ z) 1) := hpcs.mul_left
        exact h1.sub h2
      exact hcont.integrable_of_hasCompactSupport hcs.mul_left
    refine tendsto_integral_of_L1 _ hB_int (Filter.Eventually.of_forall hBn_int) ?_
    -- Reduce the `L¹` distance to `K`.
    have hred : ∀ n, (∫⁻ z,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ)
        = ∫⁻ z in K,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ := by
      intro n
      rw [← lintegral_indicator hKm]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hqzero z hz, hpzero z hz]
        simp
    -- Pointwise bound in `ℝ≥0∞` for the difference of the integrands.
    have hB_pt : ∀ (A a b c cx cy : ℂ) (qv pv : ℝ), |qv| ≤ Cq → |pv| ≤ Cp → ‖c‖ ≤ Cf →
        ‖A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)‖ₑ
          ≤ ‖A - c‖ₑ * ‖a‖ₑ * ENNReal.ofReal Cq + ‖A - c‖ₑ * ‖b‖ₑ * ENNReal.ofReal Cp
            + (‖a - cx‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
              + ‖b - cy‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) := by
      intro A a b c cx cy qv pv hqv hpv hc
      have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
      have h1 : A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)
          = (A - c).re * (a.im * qv - b.im * pv)
            + c.re * ((a - cx).im * qv - (b - cy).im * pv) := by
        simp only [Complex.sub_re, Complex.sub_im]; ring
      have s1 : |a.im * qv - b.im * pv| ≤ ‖a‖ * Cq + ‖b‖ * Cp := by
        refine (habs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
        · exact Complex.abs_im_le_norm _
        · exact Complex.abs_im_le_norm _
      have s2 : |(a - cx).im * qv - (b - cy).im * pv|
          ≤ ‖a - cx‖ * Cq + ‖b - cy‖ * Cp := by
        refine (habs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
        · exact Complex.abs_im_le_norm _
        · exact Complex.abs_im_le_norm _
      have habs : |A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)|
          ≤ ‖A - c‖ * ‖a‖ * Cq + ‖A - c‖ * ‖b‖ * Cp
            + (‖a - cx‖ * (Cf * Cq) + ‖b - cy‖ * (Cf * Cp)) := by
        rw [h1]
        have tX : |(A - c).re * (a.im * qv - b.im * pv)|
            ≤ ‖A - c‖ * (‖a‖ * Cq + ‖b‖ * Cp) := by
          rw [abs_mul]
          exact mul_le_mul (Complex.abs_re_le_norm _) s1 (abs_nonneg _) (norm_nonneg _)
        have tY : |c.re * ((a - cx).im * qv - (b - cy).im * pv)|
            ≤ Cf * (‖a - cx‖ * Cq + ‖b - cy‖ * Cp) := by
          rw [abs_mul]
          exact mul_le_mul (le_trans (Complex.abs_re_le_norm _) hc) s2
            (abs_nonneg _) hCf0
        calc |(A - c).re * (a.im * qv - b.im * pv)
              + c.re * ((a - cx).im * qv - (b - cy).im * pv)|
            ≤ |(A - c).re * (a.im * qv - b.im * pv)|
              + |c.re * ((a - cx).im * qv - (b - cy).im * pv)| := abs_add_le _ _
          _ ≤ ‖A - c‖ * (‖a‖ * Cq + ‖b‖ * Cp)
              + Cf * (‖a - cx‖ * Cq + ‖b - cy‖ * Cp) := add_le_add tX tY
          _ = ‖A - c‖ * ‖a‖ * Cq + ‖A - c‖ * ‖b‖ * Cp
              + (‖a - cx‖ * (Cf * Cq) + ‖b - cy‖ * (Cf * Cp)) := by ring
      calc ‖A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)‖ₑ
          = ENNReal.ofReal
              |A.re * (a.im * qv - b.im * pv) - c.re * (cx.im * qv - cy.im * pv)| :=
            Real.enorm_eq_ofReal_abs _
        _ ≤ ENNReal.ofReal (‖A - c‖ * ‖a‖ * Cq + ‖A - c‖ * ‖b‖ * Cp
              + (‖a - cx‖ * (Cf * Cq) + ‖b - cy‖ * (Cf * Cp))) :=
            ENNReal.ofReal_le_ofReal habs
        _ = ‖A - c‖ₑ * ‖a‖ₑ * ENNReal.ofReal Cq + ‖A - c‖ₑ * ‖b‖ₑ * ENNReal.ofReal Cp
              + (‖a - cx‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
                + ‖b - cy‖ₑ * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) := by
            rw [← ofReal_norm_eq_enorm (A - c), ← ofReal_norm_eq_enorm a,
              ← ofReal_norm_eq_enorm b, ← ofReal_norm_eq_enorm (a - cx),
              ← ofReal_norm_eq_enorm (b - cy),
              ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul hCf0, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul hCf0, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
    -- Constants and the dominating sequence.
    set BX : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gx z‖ₑ ^ 2) with hBX_def
    set BY : ℝ≥0∞ := 2 * (1 + ∫⁻ z in K, ‖gy z‖ₑ ^ 2) with hBY_def
    have hBXfin : BX ≠ ⊤ := by
      rw [hBX_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGX⟩)).ne
    have hBYfin : BY ≠ ⊤ := by
      rw [hBY_def]
      exact (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hGY⟩)).ne
    have hBX12 : BX ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBXfin).ne
    have hBY12 : BY ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBYfin).ne
    have hvol12 : (volume K) ^ (1/2 : ℝ) ≠ ⊤ :=
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvolK.ne).ne
    have hfq' : ENNReal.ofReal Cf * ENNReal.ofReal Cq ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    have hfp' : ENNReal.ofReal Cf * ENNReal.ofReal Cp ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    set D : ℕ → ℝ≥0∞ := fun n =>
      (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ) * ENNReal.ofReal Cq
        + (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
            - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ) * ENNReal.ofReal Cp
        + ((∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ)
            * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
          + (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ)
            * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) with hD_def
    have hf12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - f z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTf
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hx12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gx z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTx
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hy12 : Filter.Tendsto (fun n =>
        (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
          - gy z‖ₑ ^ 2) ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have hc := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.tendsto.comp hTy
      have h0 : ((0 : ℝ≥0∞) ^ (1/2 : ℝ)) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [Function.comp_def] at hc
      rwa [h0] at hc
    have hD0 : Filter.Tendsto D Filter.atTop (nhds 0) := by
      have t1 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Cq)
        (ENNReal.Tendsto.mul_const hf12 (Or.inr hBX12)) (Or.inr ENNReal.ofReal_ne_top)
      have t2 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal Cp)
        (ENNReal.Tendsto.mul_const hf12 (Or.inr hBY12)) (Or.inr ENNReal.ofReal_ne_top)
      have hfq : ENNReal.ofReal Cf * ENNReal.ofReal Cq ≠ ⊤ :=
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
      have hfp : ENNReal.ofReal Cf * ENNReal.ofReal Cp ≠ ⊤ :=
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
      have t3 := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const hx12 (Or.inr hvol12)) (Or.inr hfq)
      have t4 := ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const hy12 (Or.inr hvol12)) (Or.inr hfp)
      have hsum := (t1.add t2).add (t3.add t4)
      rw [hD_def]
      simpa using hsum
    -- The eventual domination.
    have hex1 := (ENNReal.tendsto_nhds_zero.mp hTx) 1 (by norm_num)
    have hey1 := (ENNReal.tendsto_nhds_zero.mp hTy) 1 (by norm_num)
    have hDbd : ∀ᶠ n in Filter.atTop, (∫⁻ z in K,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ) ≤ D n := by
      filter_upwards [hex1, hey1] with n hx1 hy1
      have hXm : AEStronglyMeasurable
          (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hXc n).aestronglyMeasurable.restrict
      have hYm : AEStronglyMeasurable
          (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hYc n).aestronglyMeasurable.restrict
      have hFm : AEStronglyMeasurable
          (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume)
          (volume.restrict K) := (hFc n).aestronglyMeasurable.restrict
      have hfm : AEStronglyMeasurable f (volume.restrict K) :=
        hfcont.aestronglyMeasurable.restrict
      have hmassX := hmass _ gx hXm hgxm hx1
      have hmassY := hmass _ gy hYm hgym hy1
      have mef : AEMeasurable (fun z =>
          ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ)
          (volume.restrict K) := (hFm.sub hfm).enorm
      have me1 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          (volume.restrict K) := (hXm.sub hgxm).enorm
      have me2 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          (volume.restrict K) := (hYm.sub hgym).enorm
      have me3 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hXm.enorm
      have me4 : AEMeasurable (fun z =>
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          (volume.restrict K) := hYm.enorm
      -- Hölder estimates.
      have e1 : (∫⁻ z in K,
          ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
            * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BX ^ (1/2 : ℝ) := by
        refine (holder _ _ mef me3).trans ?_
        gcongr
      have e2 : (∫⁻ z in K,
          ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
            * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - f z‖ₑ ^ 2) ^ (1/2 : ℝ) * BY ^ (1/2 : ℝ) := by
        refine (holder _ _ mef me4).trans ?_
        gcongr
      have e3 : (∫⁻ z in K,
          ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gx z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ) := by
        have h := holder _ (fun _ => (1 : ℝ≥0∞)) me1 aemeasurable_const
        simpa [setLIntegral_one] using h
      have e4 : (∫⁻ z in K,
          ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
          ≤ (∫⁻ z in K, ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z
              - gy z‖ₑ ^ 2) ^ (1/2 : ℝ) * (volume K) ^ (1/2 : ℝ) := by
        have h := holder _ (fun _ => (1 : ℝ≥0∞)) me2 aemeasurable_const
        simpa [setLIntegral_one] using h
      -- Assemble via the pointwise bound.
      calc (∫⁻ z in K,
          ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
              * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                  * (fderiv ℝ φ z) Complex.I
                - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                  * (fderiv ℝ φ z) 1)
            - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
                - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ)
          ≤ ∫⁻ z in K,
            (‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                * ENNReal.ofReal Cq
              + ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ
                * ENNReal.ofReal Cp
              + (‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ
                  * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
                + ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ
                  * (ENNReal.ofReal Cf * ENNReal.ofReal Cp))) := by
            refine lintegral_mono_ae ((ae_restrict_iff' hKm).mpr (ae_of_all _
              fun z hz => ?_))
            have hb := hB_pt
              (convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
              (convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
              (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
              (f z) (gx z) (gy z) ((fderiv ℝ φ z) Complex.I) ((fderiv ℝ φ z) 1)
              (by rw [← Real.norm_eq_abs]; exact hCq z)
              (by rw [← Real.norm_eq_abs]; exact hCp z) (hCf z hz)
            exact hb
        _ = (∫⁻ z in K,
              ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
              * ENNReal.ofReal Cq
            + (∫⁻ z in K,
              ‖convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z - f z‖ₑ
                * ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z‖ₑ)
              * ENNReal.ofReal Cp
            + ((∫⁻ z in K,
                ‖convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gx z‖ₑ)
                * (ENNReal.ofReal Cf * ENNReal.ofReal Cq)
              + (∫⁻ z in K,
                ‖convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z - gy z‖ₑ)
                * (ENNReal.ofReal Cf * ENNReal.ofReal Cp)) := by
            rw [lintegral_add_left' (((mef.mul me3).mul_const _).add
                ((mef.mul me4).mul_const _)),
              lintegral_add_left' ((mef.mul me3).mul_const _),
              lintegral_add_left' (me1.mul_const _),
              lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
              lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
              lintegral_mul_const' _ _ hfq', lintegral_mul_const' _ _ hfp']
        _ ≤ D n := by
            rw [hD_def]
            refine add_le_add (add_le_add ?_ ?_) (add_le_add ?_ ?_)
            · exact mul_le_mul' e1 le_rfl
            · exact mul_le_mul' e2 le_rfl
            · exact mul_le_mul' e3 le_rfl
            · exact mul_le_mul' e4 le_rfl
    have hKlim : Filter.Tendsto (fun n => ∫⁻ z in K,
        ‖(convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume z).re
            * ((convolution (ρ n) gx (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) Complex.I
              - (convolution (ρ n) gy (ContinuousLinearMap.lsmul ℝ ℝ) volume z).im
                * (fderiv ℝ φ z) 1)
          - (f z).re * ((gx z).im * (fderiv ℝ φ z) Complex.I
              - (gy z).im * (fderiv ℝ φ z) 1)‖ₑ) Filter.atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD0
        (Filter.Eventually.of_forall fun n => zero_le _) hDbd
    exact hKlim.congr fun n => (hred n).symm
  exact tendsto_nhds_unique (hAtend.congr hAB) hBtend

/-- **(J4) Weighted weak lower semicontinuity of the `L²` norm.** If `hₙ` converges
weakly in `L²(volume)` to `h` and `w : ℂ → ℝ` is a measurable weight with
`0 ≤ w ≤ C`, then the weighted energy is weakly lower semicontinuous:
`∫ ‖h z‖²·w z ≤ liminf ∫ ‖hₙ z‖²·w z`.

The `√w`-multiplier preserves weak convergence, and lower semicontinuity of the norm
under weak convergence in the `√w`-weighted `L²` space gives the bound. -/
theorem le_liminf_integral_normSq_smul {hₙ : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hw_conv : TendstoWeaklyL2 hₙ h)
    (hmemH : MemLp h 2 volume) (hmemHn : ∀ n, MemLp (hₙ n) 2 volume)
    {w : ℂ → ℝ} (hwmeas : Measurable w) {C : ℝ} (hwnn : ∀ z, 0 ≤ w z)
    (hwle : ∀ z, w z ≤ C) :
    ∫ z, ‖h z‖ ^ 2 * w z
      ≤ (Filter.liminf (fun n => ∫ z, ‖hₙ n z‖ ^ 2 * w z) Filter.atTop) := by
  set s : ℂ → ℝ := fun z => Real.sqrt (w z) with hs
  have hsmeas : Measurable s := hwmeas.sqrt
  have hsnn : ∀ z, 0 ≤ s z := fun z => Real.sqrt_nonneg _
  -- Multiplication by the bounded multiplier `s` preserves `L²`-membership.
  have hmemLp_smul : ∀ g : ℂ → ℂ, MemLp g 2 volume →
      MemLp (fun z => (s z : ℂ) * g z) 2 volume := by
    intro g hg
    have hbound : MemLp (fun z => Real.sqrt C * ‖g z‖) 2 volume := by
      simpa using hg.norm.const_mul (Real.sqrt C)
    refine hbound.mono' ?_ ?_
    · exact (Complex.measurable_ofReal.comp hsmeas).aestronglyMeasurable.mul
        hg.aestronglyMeasurable
    · filter_upwards with z
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsnn z)]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hwle z)) (norm_nonneg _)
  set sh : ℂ → ℂ := fun z => (s z : ℂ) * h z with hsh
  set shₙ : ℕ → ℂ → ℂ := fun n z => (s z : ℂ) * hₙ n z with hshₙ
  have hmemSH : MemLp sh 2 volume := hmemLp_smul h hmemH
  have hmemSHn : ∀ n, MemLp (shₙ n) 2 volume := fun n => hmemLp_smul (hₙ n) (hmemHn n)
  -- The `√w`-weighted energies are the norms-squared of `sh` and `shₙ` in `L²`.
  set X : Lp ℂ 2 (volume : Measure ℂ) := hmemSH.toLp sh with hX
  set Xₙ : ℕ → Lp ℂ 2 (volume : Measure ℂ) :=
    fun n => (hmemSHn n).toLp (shₙ n) with hXₙ
  -- For any `L²` function `f`, `∫ ‖f‖² = ‖toLp f‖²`.
  have intSq : ∀ (f : ℂ → ℂ) (hf : MemLp f 2 volume),
      (∫ z, ‖f z‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
    intro f hf
    have hinner : (inner ℂ (hf.toLp f) (hf.toLp f) : ℂ) = ∫ z, (‖f z‖ ^ 2 : ℝ) := by
      rw [L2.inner_def, ← integral_complex_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with z hz
      rw [RCLike.inner_apply, hz, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hns := inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f)
    rw [hinner] at hns
    simpa using hns
  -- The weighted energy of `h` equals `‖X‖²`.
  have hLHS : (∫ z, ‖h z‖ ^ 2 * w z) = ‖X‖ ^ 2 := by
    rw [hX, ← intSq sh hmemSH]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hsh]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsnn z),
      mul_pow, Real.sq_sqrt (hwnn z)]
    ring
  -- The weighted energy of each `hₙ n` equals `‖Xₙ n‖²`.
  have hRHSn : ∀ n, (∫ z, ‖hₙ n z‖ ^ 2 * w z) = ‖Xₙ n‖ ^ 2 := by
    intro n
    rw [hXₙ, ← intSq (shₙ n) (hmemSHn n)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [hshₙ]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsnn z),
      mul_pow, Real.sq_sqrt (hwnn z)]
    ring
  rw [hLHS]
  have hRHSeq : (fun n => ∫ z, ‖hₙ n z‖ ^ 2 * w z) = fun n => ‖Xₙ n‖ ^ 2 :=
    funext hRHSn
  rw [hRHSeq]
  -- Transport of weak convergence along the bounded multiplier `s`.
  have hconvSH : TendstoWeaklyL2 shₙ sh := by
    intro ψ hψ
    have hconv := hw_conv (fun z => (s z : ℂ) * ψ z) (hmemLp_smul ψ hψ)
    have hrhs : (∫ z, h z * ((s z : ℂ) * ψ z)) = ∫ z, sh z * ψ z :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => by rw [hsh]; ring))
    rw [hrhs] at hconv
    exact hconv.congr (fun n => integral_congr_ae (Filter.Eventually.of_forall
      (fun z => by rw [hshₙ]; ring)))
  -- The inner products `⟪X, Xₙ⟫` converge to `⟪X, X⟫`.
  have hpair : ∀ (F : ℂ → ℂ) (hF : MemLp F 2 volume),
      (inner ℂ (hmemSH.toLp sh) (hF.toLp F) : ℂ)
        = ∫ z, F z * (starRingEnd ℂ) (sh z) := by
    intro F hF
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmemSH.coeFn_toLp, hF.coeFn_toLp] with z h1 h2
    rw [RCLike.inner_apply, h1, h2, mul_comm]
  have hconvInner : Filter.Tendsto (fun n => (inner ℂ X (Xₙ n) : ℂ)) Filter.atTop
      (nhds (inner ℂ X X)) := by
    -- Test `hconvSH` against `ψ := star sh`.
    have hc := hconvSH (fun z => (starRingEnd ℂ) (sh z)) hmemSH.star
    have hXXn : ∀ n,
        (inner ℂ X (Xₙ n) : ℂ) = ∫ z, shₙ n z * (starRingEnd ℂ) (sh z) := by
      intro n
      rw [hX, hXₙ]; exact hpair (shₙ n) (hmemSHn n)
    have hXX : (inner ℂ X X : ℂ) = ∫ z, sh z * (starRingEnd ℂ) (sh z) := by
      rw [hX]; exact hpair sh hmemSH
    rw [hXX]
    exact (by simpa only [hXXn] using hc.congr (fun n => rfl))
  -- Uniform bound on `‖Xₙ‖` via the uniform boundedness principle.
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n, ‖Xₙ n‖ ≤ B := by
    set v : ℕ → Lp ℂ 2 (volume : Measure ℂ) :=
      fun n => (hmemSHn n).star.toLp (star (shₙ n)) with hv
    have hptwise : ∀ y : Lp ℂ 2 (volume : Measure ℂ),
        ∃ D, ∀ n, ‖(innerSL ℂ (v n)) y‖ ≤ D := by
      intro y
      have hy : MemLp (y : ℂ → ℂ) 2 volume := Lp.memLp y
      have hpairing : ∀ n,
          ((innerSL ℂ (v n)) y : ℂ) = ∫ z, shₙ n z * (y : ℂ → ℂ) z := by
        intro n
        rw [innerSL_apply_apply, hv, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [(hmemSHn n).star.coeFn_toLp] with z h1
        rw [RCLike.inner_apply, h1]
        simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_conj]
        rw [mul_comm]
      have hconv : Filter.Tendsto (fun n => (innerSL ℂ (v n)) y) Filter.atTop
          (nhds (∫ z, sh z * (y : ℂ → ℂ) z)) := by
        have hc := hconvSH (y : ℂ → ℂ) hy
        exact hc.congr (fun n => (hpairing n).symm)
      obtain ⟨D, hD⟩ := hconv.norm.bddAbove_range
      exact ⟨D, fun n => hD ⟨n, rfl⟩⟩
    obtain ⟨M, hM⟩ := banach_steinhaus hptwise
    refine ⟨M, fun n => ?_⟩
    have hnorm : ‖innerSL ℂ (v n)‖ = ‖v n‖ := innerSL_apply_norm (𝕜 := ℂ) (v n)
    have hveq : ‖v n‖ = ‖Xₙ n‖ := by
      rw [hv, hXₙ, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_star]
    rw [← hveq, ← hnorm]; exact hM n
  -- The weak lower-semicontinuity argument.
  have hre : Filter.Tendsto (fun n => (RCLike.re (inner ℂ X (Xₙ n)) : ℝ)) Filter.atTop
      (nhds (RCLike.re (inner ℂ X X))) :=
    (Complex.reCLM.continuous.tendsto _).comp hconvInner
  have hnormsq : RCLike.re (inner ℂ X X) = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
  set g : ℕ → ℝ := fun n => 2 * RCLike.re (inner ℂ X (Xₙ n)) - ‖X‖ ^ 2 with hg
  have hgconv : Filter.Tendsto g Filter.atTop (nhds (‖X‖ ^ 2)) := by
    have hlim : Filter.Tendsto (fun n => 2 * RCLike.re (inner ℂ X (Xₙ n)) - ‖X‖ ^ 2)
        Filter.atTop (nhds (2 * RCLike.re (inner ℂ X X) - ‖X‖ ^ 2)) :=
      (hre.const_mul 2).sub_const (‖X‖ ^ 2)
    rwa [hnormsq, show 2 * ‖X‖ ^ 2 - ‖X‖ ^ 2 = ‖X‖ ^ 2 by ring] at hlim
  have hle : ∀ n, g n ≤ ‖Xₙ n‖ ^ 2 := by
    intro n
    have h1 : RCLike.re (inner ℂ X (Xₙ n)) ≤ ‖X‖ * ‖Xₙ n‖ :=
      re_inner_le_norm (𝕜 := ℂ) X (Xₙ n)
    have h2 : 2 * (‖X‖ * ‖Xₙ n‖) ≤ ‖X‖ ^ 2 + ‖Xₙ n‖ ^ 2 := by
      nlinarith [sq_nonneg (‖X‖ - ‖Xₙ n‖)]
    rw [hg]; nlinarith [h1, h2]
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (fun n => ‖Xₙ n‖ ^ 2) := by
    refine Filter.isCoboundedUnder_ge_of_le Filter.atTop (x := B ^ 2) (fun n => ?_)
    have hn : (0 : ℝ) ≤ ‖Xₙ n‖ := norm_nonneg _
    nlinarith [hB n, hn]
  calc ‖X‖ ^ 2 = Filter.liminf g Filter.atTop := (hgconv.liminf_eq).symm
    _ ≤ Filter.liminf (fun n => ‖Xₙ n‖ ^ 2) Filter.atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
          hgconv.isBoundedUnder_ge hcobdd

/-- **(J5) Weak-derivative limit passage.** If `fₙ → g` locally uniformly (all
continuous and locally integrable), each `gxₙ` is a weak directional derivative of `fₙ`
in the real direction `v`, and `gxₙ` converges weakly in `L²` to `u`, then `u` is a
weak directional derivative of `g` in the direction `v`.

Both sides of the integration-by-parts identity `∫ (∂ᵥφ)·fₙ = − ∫ φ·gxₙ` pass to the
limit: the left through locally uniform convergence against the compactly supported
`∂ᵥφ`, the right through weak `L²` convergence tested against the `L²` function `φ`. -/
theorem hasWeakDirDeriv_of_tendsto {fₙ : ℕ → ℂ → ℂ} {g u : ℂ → ℂ} {v : ℂ}
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hfcont : ∀ n, Continuous (fₙ n)) (hgcont : Continuous g)
    {gxₙ : ℕ → ℂ → ℂ} (hgxₙ : ∀ n, HasWeakDirDeriv v (gxₙ n) (fₙ n) Set.univ)
    (hweak : TendstoWeaklyL2 gxₙ u) :
    HasWeakDirDeriv v u g Set.univ := by
  intro φ hφ hcs _htsupp
  change ∫ z, ((fderiv ℝ φ z) v) • g z = - ∫ z, φ z • u z
  -- The directional-derivative weight `m := ∂ᵥφ`: continuous with compact support.
  set m : ℂ → ℝ := fun z => (fderiv ℝ φ z) v with hm
  have hmcont : Continuous m := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmcs : HasCompactSupport m := HasCompactSupport.fderiv_apply ℝ hcs v
  have hmint : Integrable (fun z => ‖m z‖) volume :=
    (hmcont.integrable_of_hasCompactSupport hmcs).norm
  -- Integrability of `m • h` for continuous `h`.
  haveI : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul
  haveI : ContinuousSMul ℝ ℂ := IsBoundedSMul.continuousSMul
  have integ : ∀ {h : ℂ → ℂ}, Continuous h → Integrable (fun z => m z • h z) volume := by
    intro h hh
    exact (hmcont.smul hh).integrable_of_hasCompactSupport hmcs.smul_right
  -- LHS limit: `∫ m • fₙ n → ∫ m • g` by uniform convergence on the compact `tsupport m`.
  have hL : Filter.Tendsto (fun n => ∫ z, m z • fₙ n z) Filter.atTop
      (nhds (∫ z, m z • g z)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hC0 : (0 : ℝ) ≤ ∫ z, ‖m z‖ := integral_nonneg fun z => norm_nonneg _
    set C : ℝ := (∫ z, ‖m z‖) + 1 with hC
    have hCpos : 0 < C := by linarith
    have huc : TendstoUniformlyOn fₙ g Filter.atTop (tsupport m) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hmcs).mp
        hconv.tendstoLocallyUniformlyOn
    have hev := (Metric.tendstoUniformlyOn_iff.mp huc) (ε / (2 * C)) (by positivity)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    have hsub : (∫ z, m z • fₙ n z) - ∫ z, m z • g z = ∫ z, m z • (fₙ n z - g z) := by
      rw [← integral_sub (integ (hfcont n)) (integ hgcont)]
      congr 1; funext z; exact (smul_sub (m z) (fₙ n z) (g z)).symm
    rw [dist_eq_norm, hsub]
    have hbd : ∀ z, ‖m z • (fₙ n z - g z)‖ ≤ (ε / (2 * C)) * ‖m z‖ := by
      intro z
      by_cases hz : z ∈ tsupport m
      · have hd := hN n hn z hz
        rw [dist_comm, dist_eq_norm] at hd
        rw [Complex.real_smul, norm_mul, Complex.norm_real, mul_comm]
        exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hz]
        simp
    calc ‖∫ z, m z • (fₙ n z - g z)‖
        ≤ ∫ z, ‖m z • (fₙ n z - g z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, (ε / (2 * C)) * ‖m z‖ := by
          refine integral_mono_of_nonneg ?_ (hmint.const_mul _) ?_
          · filter_upwards with z using norm_nonneg _
          · filter_upwards with z using hbd z
      _ = (ε / (2 * C)) * ∫ z, ‖m z‖ := integral_const_mul _ _
      _ < ε := by
          have hlt : (∫ z, ‖m z‖) < C := by rw [hC]; linarith
          calc (ε / (2 * C)) * ∫ z, ‖m z‖ ≤ (ε / (2 * C)) * C :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = ε / 2 := by field_simp
            _ < ε := by linarith
  -- RHS limit: `∫ φ • gxₙ n → ∫ φ • u` by the weak `L²` pairing against `φ`.
  have hφC : Continuous fun z => ((φ z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hφ.continuous
  have hφcs : HasCompactSupport fun z => ((φ z : ℝ) : ℂ) :=
    hcs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hφL2 : MemLp (fun z => ((φ z : ℝ) : ℂ)) 2 volume :=
    hφC.memLp_of_hasCompactSupport hφcs
  have hpair : ∀ h : ℂ → ℂ, (∫ z, h z * ((φ z : ℝ) : ℂ)) = ∫ z, φ z • h z := by
    intro h; congr 1; funext z; rw [Complex.real_smul, mul_comm]
  have hR : Filter.Tendsto (fun n => ∫ z, φ z • gxₙ n z) Filter.atTop
      (nhds (∫ z, φ z • u z)) := by
    have hw := hweak (fun z => ((φ z : ℝ) : ℂ)) hφL2
    rw [hpair u] at hw
    exact hw.congr fun n => hpair (gxₙ n)
  -- The per-`n` identity and uniqueness of limits.
  have hEq : ∀ n, ∫ z, m z • fₙ n z = - ∫ z, φ z • gxₙ n z := fun n =>
    hgxₙ n φ hφ hcs (Set.subset_univ _)
  have hL' : Filter.Tendsto (fun n => ∫ z, m z • fₙ n z) Filter.atTop
      (nhds (- ∫ z, φ z • u z)) :=
    hR.neg.congr fun n => (hEq n).symm
  exact tendsto_nhds_unique hL hL'

/-- **(J3) Weak continuity of the tested Jacobian.** Along a sequence `fₙ → g` locally
uniformly (continuous, `W^{1,2}_loc`, a.e. differentiable) whose weak gradients
`(gxₙ, gyₙ)` converge weakly in `L²` to the weak gradient `(gx, gy)` of `g`, with
uniform `L²`-bounds on the gradients, the tested Jacobians converge:
`∫ (jacobianWeak gxₙ gyₙ)·φ → ∫ (jacobianWeak gx gy)·φ`.

Each `∫ (jacobianWeak · ·)·φ` is rewritten by `integral_jacobianWeak_smul_eq` into the
first-order form `∫ (Re fₙ)·((Im gxₙ)·∂ᵧφ − (Im gyₙ)·∂ₓφ)`, whose two limits split into
a uniform-convergence term (`(Re fₙ − Re g)` times a uniformly-`L²`-bounded factor) and
a weak-`L²`-convergence term (the gradient tested against the fixed `L²` function
`Re g·∂φ`). -/
theorem tendsto_integral_jacobianWeak_smul {fₙ : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly fₙ g Filter.atTop)
    (hfcont : ∀ n, Continuous (fₙ n)) (hgcont : Continuous g)
    (hfdiff : ∀ n, ∀ᵐ z, DifferentiableAt ℝ (fₙ n) z) (hfW12 : ∀ n, MemW12loc (fₙ n))
    (hgdiff : ∀ᵐ z, DifferentiableAt ℝ g z) (hgW12 : MemW12loc g)
    {gxₙ gyₙ : ℕ → ℂ → ℂ} {gxLim gyLim : ℂ → ℂ}
    (hgn : ∀ n, HasWeakGradient (gxₙ n) (gyₙ n) (fₙ n) Set.univ)
    (hgnx : ∀ n, MemLpLocOn (gxₙ n) 2 Set.univ) (hgny : ∀ n, MemLpLocOn (gyₙ n) 2 Set.univ)
    (hgLim : HasWeakGradient gxLim gyLim g Set.univ)
    (hgLimx : MemLpLocOn gxLim 2 Set.univ) (hgLimy : MemLpLocOn gyLim 2 Set.univ)
    (hweakx : TendstoWeaklyL2 gxₙ gxLim) (hweaky : TendstoWeaklyL2 gyₙ gyLim)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {M : ℝ}
    (hMx : ∀ n, ∫ z in tsupport φ, ‖gxₙ n z‖ ^ 2 ≤ M)
    (hMy : ∀ n, ∫ z in tsupport φ, ‖gyₙ n z‖ ^ 2 ≤ M) :
    Filter.Tendsto (fun n => ∫ z, jacobianWeak (gxₙ n) (gyₙ n) z * φ z)
      Filter.atTop (nhds (∫ z, jacobianWeak gxLim gyLim z * φ z)) := by
  classical
  set K : Set ℂ := tsupport φ with hK_def
  have hKc : IsCompact K := hφc
  have hKm : MeasurableSet K := (isClosed_tsupport φ).measurableSet
  set q : ℂ → ℝ := fun z => (fderiv ℝ φ z) Complex.I with hq_def
  set p : ℂ → ℝ := fun z => (fderiv ℝ φ z) 1 with hp_def
  have hqc : Continuous q := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hpc : Continuous p := (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hqcs : HasCompactSupport q := HasCompactSupport.fderiv_apply ℝ hφc Complex.I
  have hpcs : HasCompactSupport p := HasCompactSupport.fderiv_apply ℝ hφc 1
  have hqsub : tsupport q ⊆ K := tsupport_fderiv_apply_subset ℝ Complex.I
  have hpsub : tsupport p ⊆ K := tsupport_fderiv_apply_subset ℝ 1
  -- J2 rewrites the tested Jacobian into the first-order divergence form.
  have hBn : ∀ n, (∫ z, jacobianWeak (gxₙ n) (gyₙ n) z * φ z)
      = ∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z) := fun n =>
    integral_jacobianWeak_smul_eq (f := fₙ n) (φ := φ) (hfcont n) (hfdiff n) (hfW12 n)
      (hgn n) (hgnx n) (hgny n) hφ hφc
  have hBg : (∫ z, jacobianWeak gxLim gyLim z * φ z)
      = ∫ z, (g z).re * ((gxLim z).im * q z - (gyLim z).im * p z) :=
    integral_jacobianWeak_smul_eq (f := g) (φ := φ) hgcont hgdiff hgW12 hgLim hgLimx hgLimy
      hφ hφc
  rw [show (fun n => ∫ z, jacobianWeak (gxₙ n) (gyₙ n) z * φ z)
      = fun n => ∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z)
      from funext hBn, hBg]
  -- Uniform convergence of `fₙ → g` on the compact support `K`.
  have huc : TendstoUniformlyOn fₙ g Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKc).mp
      hconv.tendstoLocallyUniformlyOn
  -- `√M` bounds the `L²` masses of the sequence gradients on `K`.
  have hM0 : 0 ≤ M := le_trans (integral_nonneg fun z => by positivity) (hMx 0)
  -- `K` has finite volume.
  have hvolK : volume K < ⊤ := hKc.measure_lt_top
  -- Integrability of a first-order product `(Re h)·(Im w)·t` supported in `K`.
  have hint : ∀ (h w : ℂ → ℂ) (t : ℂ → ℝ), Continuous h → Continuous t →
      HasCompactSupport t → tsupport t ⊆ K → MemLpLocOn w 2 Set.univ →
      Integrable (fun z => (h z).re * (w z).im * t z) volume := by
    intro h w t hh ht htcs htsub hw
    have hwK : MemLp w 2 (volume.restrict K) := hw K (Set.subset_univ K) hKc
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolK⟩
    have hwim1 : Integrable (K.indicator fun z => (w z).im) volume := by
      rw [integrable_indicator_iff hKm]
      exact memLp_one_iff_integrable.mp (hwK.im.mono_exponent (p := 1) (by norm_num))
    have hst_cs : HasCompactSupport (fun z => (h z).re * t z) :=
      htcs.mul_left (f := fun z => (h z).re)
    obtain ⟨Ch, hCh⟩ := hst_cs.exists_bound_of_continuous (by fun_prop)
    have hbdd : Integrable (fun z => ((h z).re * t z)
        * (K.indicator fun z => (w z).im) z) volume :=
      hwim1.bdd_mul ((by fun_prop : Continuous fun z => (h z).re * t z)).aestronglyMeasurable
        (ae_of_all _ hCh)
    refine hbdd.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ K
    · simp only [Set.indicator_of_mem hz]; ring
    · have htz : t z = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
      simp [Set.indicator_of_notMem hz, htz]
  -- The core per-term convergence, applied to `(gxₙ, q)` and `(gyₙ, p)`.
  have hcore : ∀ (wₙ : ℕ → ℂ → ℂ) (wLim : ℂ → ℂ) (t : ℂ → ℝ),
      Continuous t → tsupport t ⊆ K → (∀ n, MemLpLocOn (wₙ n) 2 Set.univ) →
      MemLpLocOn wLim 2 Set.univ → TendstoWeaklyL2 wₙ wLim →
      (∀ n, ∫ z in K, ‖wₙ n z‖ ^ 2 ≤ M) →
      Filter.Tendsto (fun n => ∫ z, (fₙ n z).re * (wₙ n z).im * t z) Filter.atTop
        (nhds (∫ z, (g z).re * (wLim z).im * t z)) := by
    intro wₙ wLim t htc htsub hwn hwL hwweak hMw
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolK⟩
    have htcs : HasCompactSupport t :=
      HasCompactSupport.of_support_subset_isCompact hKc (subset_trans subset_closure htsub)
    -- Integrability of each first-order product.
    have hIn : ∀ n, Integrable (fun z => (fₙ n z).re * (wₙ n z).im * t z) volume := fun n =>
      hint (fₙ n) (wₙ n) t (hfcont n) htc htcs htsub (hwn n)
    have hIg : Integrable (fun z => (g z).re * (wLim z).im * t z) volume :=
      hint g wLim t hgcont htc htcs htsub hwL
    -- WEAK TERM: `∫ g.re·(wₙ).im·t → ∫ g.re·(wLim).im·t` by weak-`L²` pairing.
    have hweakterm : Filter.Tendsto (fun n => ∫ z, (g z).re * (wₙ n z).im * t z)
        Filter.atTop (nhds (∫ z, (g z).re * (wLim z).im * t z)) := by
      -- The fixed real weight `s = g.re·t` and the complex test function `ψ = s·(-i)`.
      set s : ℂ → ℝ := fun z => (g z).re * t z with hs_def
      have hscont : Continuous s := by fun_prop
      have hscs : HasCompactSupport s := htcs.mul_left (f := fun z => (g z).re)
      set ψ : ℂ → ℂ := fun z => (s z : ℂ) * (-Complex.I) with hψ_def
      have hψcont : Continuous ψ := by fun_prop
      have hψcs : HasCompactSupport ψ :=
        (hscs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right
      have hψLp : MemLp ψ 2 volume := hψcont.memLp_of_hasCompactSupport hψcs
      -- Pairing rewrite: `(∫ w·ψ).re = ∫ g.re·w.im·t` for any `L²_loc` `w`.
      have hpairing : ∀ (w : ℂ → ℂ), MemLpLocOn w 2 Set.univ →
          (∫ z, w z * ψ z).re = ∫ z, (g z).re * (w z).im * t z := by
        intro w hw
        have hInt : Integrable (fun z => w z * ψ z) volume := by
          have hwK : MemLp w 2 (volume.restrict K) := hw K (Set.subset_univ K) hKc
          have hprodK : Integrable (fun z => w z * ψ z) (volume.restrict K) :=
            hwK.integrable_mul (hψLp.restrict K)
          rw [← integrableOn_iff_integrable_of_support_subset (s := K)]
          · exact hprodK
          · intro z hz
            by_contra hzK
            have hψz : ψ z = 0 := by
              have : s z = 0 := by
                have htz : t z = 0 :=
                  image_eq_zero_of_notMem_tsupport (fun hmem => hzK (htsub hmem))
                simp [hs_def, htz]
              simp [hψ_def, this]
            exact hz (by simp [hψz])
        have hre : (∫ z, w z * ψ z).re = ∫ z, (w z * ψ z).re :=
          (integral_re hInt).symm
        rw [hre]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hψ_def, hs_def]
        push_cast
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [← hpairing wLim hwL]
      refine (Complex.reCLM.continuous.tendsto _).comp (hwweak ψ hψLp) |>.congr fun n => ?_
      rw [Function.comp_apply, Complex.reCLM_apply, hpairing (wₙ n) (hwn n)]
    -- UNIFORM TERM: `∫ (fₙ.re − g.re)·(wₙ).im·t → 0`.
    have hunifterm : Filter.Tendsto
        (fun n => ∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z)
        Filter.atTop (nhds 0) := by
      -- Cauchy–Schwarz constant: the `L²(K)`-norm of the fixed weight `t`.
      have htLp : MemLp t 2 (volume.restrict K) := (htc.memLp_of_hasCompactSupport htcs).restrict K
      set Ct : ℝ := (∫ z in K, |t z| ^ 2) ^ (1 / 2 : ℝ) with hCt_def
      have hCt0 : 0 ≤ Ct := by positivity
      have h2conj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
      -- Uniform Cauchy–Schwarz bound: `∫_K |(wₙ).im·t| ≤ √M · Ct`.
      have hCSbd : ∀ n, (∫ z in K, |(wₙ n z).im| * |t z|) ≤ Real.sqrt M * Ct := by
        intro n
        have hwimLp : MemLp (fun z => (wₙ n z).im) 2 (volume.restrict K) :=
          ((hwn n) K (Set.subset_univ K) hKc).im
        have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict K) h2conj
          (f := fun z => |(wₙ n z).im|) (g := fun z => |t z|)
          (ae_of_all _ fun z => abs_nonneg _) (ae_of_all _ fun z => abs_nonneg _)
          (by simpa using hwimLp.abs) (by simpa using htLp.abs)
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at hcs
        simp only [Real.rpow_natCast] at hcs
        refine hcs.trans ?_
        have hwimK2 : Integrable (fun z => ‖wₙ n z‖ ^ 2) (volume.restrict K) := by
          have := ((hwn n) K (Set.subset_univ K) hKc).norm.integrable_sq
          simpa using this
        have hmono : (∫ z in K, |(wₙ n z).im| ^ 2) ≤ ∫ z in K, ‖wₙ n z‖ ^ 2 := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) hwimK2
            (ae_of_all _ fun z => ?_)
          change |(wₙ n z).im| ^ 2 ≤ ‖wₙ n z‖ ^ 2
          exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
        have hwbd : (∫ z in K, |(wₙ n z).im| ^ 2) ^ (1 / 2 : ℝ) ≤ Real.sqrt M := by
          rw [Real.sqrt_eq_rpow]
          refine Real.rpow_le_rpow (integral_nonneg fun z => by positivity)
            (hmono.trans (hMw n)) (by norm_num)
        exact mul_le_mul hwbd (le_of_eq hCt_def.symm) (by positivity) (Real.sqrt_nonneg _)
      -- The uniform constant `Cu = √M·Ct`.
      set Cu : ℝ := Real.sqrt M * Ct with hCu_def
      have hCu0 : 0 ≤ Cu := by positivity
      -- Integrability of `|(wₙ).im|·|t|` on the whole plane (supported in `K`).
      have hprodInt : ∀ n, Integrable (fun z => |(wₙ n z).im| * |t z|) volume := by
        intro n
        have h0 := hint (fun _ => (1 : ℂ)) (wₙ n) t continuous_const htc htcs htsub (hwn n)
        have := h0.abs
        refine this.congr (Filter.Eventually.of_forall fun z => ?_)
        simp [abs_mul]
      -- `‖∫ Iₙ‖ ≤ Cu·δ` whenever `‖fₙ n − g‖ ≤ δ` on `K`.
      have hbd : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ →
          (∀ z ∈ K, ‖fₙ n z - g z‖ ≤ δ) →
          ‖∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖ ≤ δ * Cu := by
        intro n δ hδ0 hδ
        calc ‖∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖
            ≤ ∫ z, ‖((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ z, δ * (|(wₙ n z).im| * |t z|) := by
              refine integral_mono_of_nonneg (ae_of_all _ fun z => norm_nonneg _)
                ((hprodInt n).const_mul δ) (ae_of_all _ fun z => ?_)
              simp only
              by_cases hz : z ∈ K
              · rw [Real.norm_eq_abs, abs_mul, abs_mul]
                have h1 : |(fₙ n z).re - (g z).re| ≤ δ := by
                  have hsub : (fₙ n z).re - (g z).re = (fₙ n z - g z).re := by
                    rw [Complex.sub_re]
                  rw [hsub]
                  exact le_trans (Complex.abs_re_le_norm _) (hδ z hz)
                calc |(fₙ n z).re - (g z).re| * |(wₙ n z).im| * |t z|
                    ≤ δ * |(wₙ n z).im| * |t z| := by gcongr
                  _ = δ * (|(wₙ n z).im| * |t z|) := by ring
              · have htz : t z = 0 :=
                  image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
                simp [htz]
          _ = δ * ∫ z, |(wₙ n z).im| * |t z| := integral_const_mul _ _
          _ ≤ δ * Cu := by
              refine mul_le_mul_of_nonneg_left ?_ hδ0
              have hle : (∫ z, |(wₙ n z).im| * |t z|)
                  = ∫ z in K, |(wₙ n z).im| * |t z| := by
                rw [← integral_indicator hKm]
                refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
                by_cases hz : z ∈ K
                · rw [Set.indicator_of_mem hz]
                · have htz : t z = 0 :=
                    image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
                  rw [Set.indicator_of_notMem hz]; simp [htz]
              rw [hle]; exact hCSbd n
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hunif := Metric.tendstoUniformlyOn_iff.mp huc (ε / (Cu + 1)) (by positivity)
      rw [Filter.eventually_atTop] at hunif
      obtain ⟨N, hN⟩ := hunif
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, sub_zero]
      have hδ : ∀ z ∈ K, ‖fₙ n z - g z‖ ≤ ε / (Cu + 1) := by
        intro z hz
        have := hN n hn z hz
        rw [dist_comm, dist_eq_norm] at this
        exact this.le
      calc ‖∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z‖
          ≤ (ε / (Cu + 1)) * Cu := hbd n (ε / (Cu + 1)) (by positivity) hδ
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [hCu0, hε]
    -- Assemble: `∫ (fₙ).re·… = ∫ (fₙ.re − g.re)·… + ∫ g.re·…`.
    have hIg' : ∀ n, Integrable (fun z => (g z).re * (wₙ n z).im * t z) volume := fun n =>
      hint g (wₙ n) t hgcont htc htcs htsub (hwn n)
    have hIu : ∀ n, Integrable
        (fun z => ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z) volume := fun n =>
      ((hIn n).sub (hIg' n)).congr (Filter.Eventually.of_forall fun z => by
        simp only [Pi.sub_apply]; ring)
    have hcomb : ∀ n, (∫ z, (fₙ n z).re * (wₙ n z).im * t z)
        = (∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z)
          + ∫ z, (g z).re * (wₙ n z).im * t z := by
      intro n
      rw [← integral_add (hIu n) (hIg' n)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    rw [show (fun n => ∫ z, (fₙ n z).re * (wₙ n z).im * t z)
        = fun n => (∫ z, ((fₙ n z).re - (g z).re) * (wₙ n z).im * t z)
          + ∫ z, (g z).re * (wₙ n z).im * t z from funext hcomb]
    have := hunifterm.add hweakterm
    simpa using this
  -- The two weights `q`, `p` and their `L²`-membership.
  have hxlim := hcore gxₙ gxLim q hqc hqsub hgnx hgLimx hweakx hMx
  have hylim := hcore gyₙ gyLim p hpc hpsub hgny hgLimy hweaky hMy
  -- `K` has finite volume.
  have hvolK : volume K < ⊤ := hKc.measure_lt_top
  -- Integrability of a first-order product `(Re h)·(Im w)·t` supported in `K`.
  have hint : ∀ (h w : ℂ → ℂ) (t : ℂ → ℝ), Continuous h → Continuous t →
      HasCompactSupport t → tsupport t ⊆ K → MemLpLocOn w 2 Set.univ →
      Integrable (fun z => (h z).re * (w z).im * t z) volume := by
    intro h w t hh ht htcs htsub hw
    -- The imaginary part of `w`, restricted to `K` by an indicator, is `L¹`.
    have hwK : MemLp w 2 (volume.restrict K) := hw K (Set.subset_univ K) hKc
    haveI : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolK⟩
    have hwim1 : Integrable (K.indicator fun z => (w z).im) volume := by
      rw [integrable_indicator_iff hKm]
      exact memLp_one_iff_integrable.mp (hwK.im.mono_exponent (p := 1) (by norm_num))
    -- The continuous factor `h.re · t` is bounded (it vanishes off compact `tsupport t`).
    have hst_cs : HasCompactSupport (fun z => (h z).re * t z) :=
      htcs.mul_left (f := fun z => (h z).re)
    obtain ⟨Ch, hCh⟩ := hst_cs.exists_bound_of_continuous (by fun_prop)
    -- `(Re h · t)` is bounded and measurable, so multiplying preserves `L¹`.
    have hbdd : Integrable (fun z => ((h z).re * t z)
        * (K.indicator fun z => (w z).im) z) volume :=
      hwim1.bdd_mul ((by fun_prop : Continuous fun z => (h z).re * t z)).aestronglyMeasurable
        (ae_of_all _ hCh)
    refine hbdd.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ K
    · simp only [Set.indicator_of_mem hz]; ring
    · have htz : t z = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hz (htsub hmem))
      simp [Set.indicator_of_notMem hz, htz]
  -- The difference-of-integrals split and the combined limit.
  have hsplit : ∀ (h wx wy : ℂ → ℂ),
      Integrable (fun z => (h z).re * (wx z).im * q z) volume →
      Integrable (fun z => (h z).re * (wy z).im * p z) volume →
      (∫ z, (h z).re * ((wx z).im * q z - (wy z).im * p z))
        = (∫ z, (h z).re * (wx z).im * q z) - ∫ z, (h z).re * (wy z).im * p z := by
    intro h wx wy hix hiy
    rw [← integral_sub hix hiy]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  -- Split each tested integral into the `q`- and `p`-pieces and pass to the two limits.
  have hseqeq : ∀ n, (∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z))
      = (∫ z, (fₙ n z).re * (gxₙ n z).im * q z)
        - ∫ z, (fₙ n z).re * (gyₙ n z).im * p z := fun n =>
    hsplit (fₙ n) (gxₙ n) (gyₙ n)
      (hint (fₙ n) (gxₙ n) q (hfcont n) hqc hqcs hqsub (hgnx n))
      (hint (fₙ n) (gyₙ n) p (hfcont n) hpc hpcs hpsub (hgny n))
  have hlimeq : (∫ z, (g z).re * ((gxLim z).im * q z - (gyLim z).im * p z))
      = (∫ z, (g z).re * (gxLim z).im * q z) - ∫ z, (g z).re * (gyLim z).im * p z :=
    hsplit g gxLim gyLim
      (hint g gxLim q hgcont hqc hqcs hqsub hgLimx)
      (hint g gyLim p hgcont hpc hpcs hpsub hgLimy)
  rw [show (fun n => ∫ z, (fₙ n z).re * ((gxₙ n z).im * q z - (gyₙ n z).im * p z))
      = fun n => (∫ z, (fₙ n z).re * (gxₙ n z).im * q z)
        - ∫ z, (fₙ n z).re * (gyₙ n z).im * p z from funext hseqeq, hlimeq]
  exact hxlim.sub hylim

end RiemannDynamics
