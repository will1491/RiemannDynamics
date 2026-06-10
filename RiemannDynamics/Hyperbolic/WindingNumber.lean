/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import RiemannDynamics.Hyperbolic.StarShapedPrimitive

/-!
# Winding number, Cauchy-Goursat on non-rectangular regions, and the argument principle

Winding-number theory and contour-integral infrastructure used by the
modular-covering proof `modularLambdaH_existsUnique_in_F_interior_of_im_pos`
in `ModularCoveringMap.lean` (which counts preimages of `w` under
`λ : F^o ≅ {Im w > 0}` via the argument principle on the truncated
fundamental domain).

## Winding-number definitions

* `Complex.circleWindingNumber c R w` — circle case,
  `(2πi)⁻¹ ∮_{|z−c|=R} (z − w)⁻¹ dz`.
* `Complex.pathContourIntegral γ a b f` — contour integral
  `∫_a^b f(γ t) · γ'(t) dt` of `f` along the path `γ : ℝ → ℂ`
  from parameter `a` to `b`.
* `Complex.pathWindingNumber γ a b w` — winding number of a closed
  parameterized path `γ : [a, b] → ℂ` around `w`, defined as
  `(2πi)⁻¹ ∫_a^b γ'(t) / (γ(t) − w) dt`.

## Circle and rectangle winding numbers

* `Complex.circleWindingNumber_inside` — winding number `1` for points
  strictly inside the circle.
* `Complex.circleWindingNumber_outside` — winding number `0` for
  points strictly outside the closed disk.
* `Complex.circleWindingNumber_self` — special case `w = c`.
* `Complex.rectangleWindingNumber_inside_eq_one` — winding number `1`
  for points strictly inside an axis-aligned rectangle.

## Cauchy-Goursat on lunes and half-annuli

The argument-principle application below needs Cauchy-Goursat for
**non-rectangular** regions arising from the truncated fundamental
domain. The four building-block CG theorems are:

* `Complex.integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn`,
  `Complex.integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn`
  — CG on a **lune** (axis-aligned rectangle corner minus a quarter
  disk), star-shaped from the outer corner. Closed by combining three
  `starPrimitive` identities in `StarShapedPrimitive.lean`
  (horizontal/vertical segment substitutions and the ε-arc limit).
* `Complex.integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn`
  — CG on a rectangle with the upper half of a disk on the bottom
  edge removed: `(Icc a b ×ℂ Icc e.im d) \ ball e R₀`, with `e.im` the
  rectangle's bottom y. This is the **truncated `Γ(2)` fundamental
  domain shape** (rectangle minus upper half-disk on the bottom
  boundary). Proved by 5-piece decomposition: 3 sub-rectangles
  (Mathlib's rect CG) plus the two top lunes, with shared edges
  cancelling and the lune arc contributions combining into the upper
  semicircle.

## Argument-principle theorems

* `cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk` — for
  `g` holomorphic on a neighborhood of a rectangle with the upper
  half-disk on the bottom boundary removed, and `g` non-vanishing on
  the four rectangle edges and the upper semicircle,
  `(2πi)⁻¹ ∮_{∂F_Y} g'(z)/g(z) dz` is a non-negative integer counting
  zeros of `g` inside `F_Y^o`. This is the argument principle used to
  prove existence/uniqueness of `λ`-preimages in the truncated `Γ(2)`
  fundamental domain.
* Analogous circle and rectangle argument-principle theorems for the
  simpler closed-disk and closed-rectangle base cases.

## Log-lift bridges (in `PathWinding.lean`)

The definitions `pathContourIntegral` / `pathWindingNumber` introduced
here are connected to continuous logarithms in `PathWinding.lean`,
which completes the path-winding toolkit on top of this file:

* continuous log lifts through the universal cover `z ↦ exp z` of
  `ℂ \ {0}`, both for a single curve on a closed interval
  (`continuous_log_lift_of_continuous_ne_zero_Icc`) and jointly in a
  parameter over a rectangle
  (`continuous_log_lift_param_of_continuous_ne_zero`);
* FTC bridges identifying `pathContourIntegral γ a b ((z − w)⁻¹)` with
  the boundary difference `L b − L a` of any continuous log lift `L`
  of `γ − w` — for globally `C¹` paths
  (`pathContourIntegral_inv_eq_log_lift_diff_of_contDiff`), for paths
  `C¹` on an open neighborhood of `[a, b]` (`…_of_contDiffOn`), and
  for the piecewise-`C¹` image curve `λ ∘ ∂F_Y`
  (`…_F_Y_image_curve`).

Consequently the winding number of a closed curve avoiding `w` can be
read off as `(2πi)⁻¹ (L b − L a)`, the total change of a continuous
argument along the curve.
-/

namespace Complex

open MeasureTheory

/-- The winding number of the standard counterclockwise parameterization of
the circle `|z − c| = R` around a point `w`, defined as
`(2πi)⁻¹ ∮_{|z−c|=R} (z − w)⁻¹ dz`. -/
noncomputable def circleWindingNumber (c : ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹

/-- For a point `w` strictly inside the circle of radius `R` around `c`,
the winding number equals `1`. -/
theorem circleWindingNumber_inside (c : ℂ) {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball c R) :
    circleWindingNumber c R w = 1 := by
  unfold circleWindingNumber
  rw [circleIntegral.integral_sub_inv_of_mem_ball hw]
  have h_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  field_simp

/-- For a point `w` strictly outside the closed disk of radius `R` around
`c`, the winding number equals `0`. (Cauchy-Goursat applied to the
holomorphic integrand `(z − w)⁻¹` on the closed disk.) -/
theorem circleWindingNumber_outside (c : ℂ) {R : ℝ} (hR : 0 ≤ R) {w : ℂ}
    (hw : w ∉ Metric.closedBall c R) :
    circleWindingNumber c R w = 0 := by
  unfold circleWindingNumber
  have h_diff : DifferentiableOn ℂ (fun z : ℂ => (z - w)⁻¹) (Metric.closedBall c R) := by
    intro z hz
    have hz_ne : z - w ≠ 0 := by
      intro h
      apply hw
      have : z = w := by linear_combination h
      rw [← this]; exact hz
    exact ((differentiableAt_id.sub_const w).inv hz_ne).differentiableWithinAt
  have h_cont : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (Metric.closedBall c R) :=
    h_diff.continuousOn
  have h_integral : (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR
      Set.countable_empty h_cont ?_
    intro z hz
    have hz_ball : z ∈ Metric.ball c R := hz.1
    have hz_ne : z - w ≠ 0 := by
      intro h
      apply hw
      have : z = w := by linear_combination h
      rw [← this]; exact Metric.ball_subset_closedBall hz_ball
    exact (differentiableAt_id.sub_const w).inv hz_ne
  rw [h_integral, mul_zero]

/-- The winding number of a circle around its own center is `1` (for
positive radius). -/
theorem circleWindingNumber_self (c : ℂ) {R : ℝ} (hR : 0 < R) :
    circleWindingNumber c R c = 1 :=
  circleWindingNumber_inside c (Metric.mem_ball_self hR)

/-! ## Path-integral winding number

The following definitions and theorems extend the toolkit to general
parameterized paths and rectangle / argument-principle versions used
by `modularLambdaH_image_fundamentalDomainInterior` (in
`Gamma2FundamentalDomain.lean`) to count preimages of `w` under the
modular function `λ` inside a fundamental domain. -/

/-- Contour integral of `f : ℂ → ℂ` along a parameterized path
`γ : ℝ → ℂ` from `a` to `b`:
`∫_a^b f(γ(t)) · γ'(t) dt`. -/
noncomputable def pathContourIntegral (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ t in a..b, f (γ t) * deriv γ t

/-- Winding number of the parameterized path `γ : [a, b] → ℂ` around a
point `w`. For a closed path `γ` not passing through `w`, this is
integer-valued and equals the number of times `γ` winds around `w`
counterclockwise. -/
noncomputable def pathWindingNumber (γ : ℝ → ℂ) (a b : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * pathContourIntegral γ a b (fun z => (z - w)⁻¹)

/-- **Argument principle for circles (analytic form).** For a holomorphic
function `g` on a closed disk (analytic in an open neighborhood of every
point of the disk) that is nonzero on the boundary sphere, the contour
integral `(2πi)⁻¹ ∮_{C(c, R)} g'(z)/g(z) dz` is a non-negative integer,
equal to the count of zeros of `g` inside the open disk (with
multiplicity).

This is the analytic form of the argument principle, with `g` playing the
role of `f − w`. The `AnalyticOnNhd` hypothesis (rather than mere
`DifferentiableOn`) is needed because `deriv g z` at boundary points of
the closed disk is the Fréchet derivative, which requires full
differentiability in a neighborhood, not just differentiability within
the disk.

The proof factors `g = (∏ᶠ u, (· − u)^{n_u}) · h` (Weierstrass-style
factorization), where the `n_u` are the multiplicities of the zeros of
`g` inside the disk and `h` is analytic and non-vanishing on the closed
disk. The logarithmic derivative splits as
`g'/g = ∑ᶠ u, n_u / (· − u) + h'/h`. Integrating term by term, each
pole contributes `2πi · n_u` and the non-vanishing remainder
contributes `0` (Cauchy-Goursat), yielding `2πi · ∑ᶠ u, n_u`. -/
theorem cIntegralLogDeriv_isNat_of_nonzero_on_sphere
    (g : ℂ → ℂ) (c : ℂ) {R : ℝ} (_hR : 0 < R)
    (_hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (_hg_sphere : ∀ z ∈ Metric.sphere c R, g z ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), deriv g z / g z) = (n : ℂ) := by
  -- Setup: g is meromorphic on the closed disk.
  have hg_mer : MeromorphicOn g (Metric.closedBall c R) := _hg.meromorphicOn
  -- The closed disk is preconnected.
  have hcb_preconn : IsPreconnected (Metric.closedBall c R) :=
    (Metric.isConnected_closedBall _hR.le).isPreconnected
  -- Pick a sphere point as a witness where g ≠ 0.
  have hsphere_nonempty : (Metric.sphere c R).Nonempty :=
    ⟨c + R, by simp [Complex.norm_real, abs_of_pos _hR]⟩
  obtain ⟨z₀, hz₀_sphere⟩ := hsphere_nonempty
  have hz₀_cb : z₀ ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz₀_sphere
  have hz₀_g_ne : g z₀ ≠ 0 := _hg_sphere z₀ hz₀_sphere
  have hz₀_analytic : AnalyticAt ℂ g z₀ := _hg z₀ hz₀_cb
  -- Step: meromorphicOrderAt g z₀ ≠ ⊤ since g z₀ ≠ 0.
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    rw [hz₀_analytic.meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g z₀ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hz₀_g_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  -- Spread to all of closedBall via preconnectedness.
  have hg_order : ∀ u ∈ Metric.closedBall c R, meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    exact hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hcb_preconn
      hz₀_cb hu hz₀_order_ne_top
  -- Divisor support is finite (closedBall is compact).
  have hdiv_finite : (MeromorphicOn.divisor g (Metric.closedBall c R)).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ (isCompact_closedBall c R)
  -- Apply extract_zeros_poles to factor `g = (rational) • h`.
  obtain ⟨h, h_analytic, h_nonzero, h_factor⟩ :=
    hg_mer.extract_zeros_poles
      (fun u : Metric.closedBall c R => hg_order u.1 u.2)
      hdiv_finite
  -- The divisor is non-negative because `g` is analytic.
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g (Metric.closedBall c R) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg _hg
  -- Name the rational factor for readability.
  set r : ℂ → ℂ :=
    ∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor g (Metric.closedBall c R)) u) with hr_def
  -- r is analytic everywhere on ℂ (divisor is non-negative integer-valued).
  have hr_analytic : ∀ z, AnalyticAt ℂ r z := fun z =>
    Function.FactorizedRational.analyticAt (hD_nonneg z)
  -- Every point of the closed disk is an accumulation point of the disk
  -- (the disk is nontrivial preconnected, hence preperfect).
  have hcb_ntriv : (Metric.closedBall c R).Nontrivial := by
    refine ⟨c, Metric.mem_closedBall_self _hR.le, c + R, ?_, ?_⟩
    · simp [Metric.mem_closedBall, Complex.norm_real, abs_of_pos _hR]
    · intro h
      have : (R : ℂ) = 0 := by linear_combination -h
      simp at this
      linarith
  have h_accpt : ∀ z ∈ Metric.closedBall c R,
      AccPt z (Filter.principal (Metric.closedBall c R)) :=
    fun z hz => hcb_preconn.preperfect_of_nontrivial hcb_ntriv z hz
  -- Rewrite the codiscrete factorization in `mul` form (for ℂ-valued, smul = mul).
  have h_factor_mul : g =ᶠ[Filter.codiscreteWithin (Metric.closedBall c R)]
      (fun w => r w * h w) := by
    filter_upwards [h_factor] with w hw
    simpa [smul_eq_mul] using hw
  -- At each sphere point, get nhds equality via codiscrete + AccPt + analyticity.
  have h_nhds_eq : ∀ z ∈ Metric.sphere c R, g =ᶠ[nhds z] (fun w => r w * h w) := by
    intro z hz
    have hz_cb : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
    have hz_g_an : AnalyticAt ℂ g z := _hg z hz_cb
    have hz_r_an : AnalyticAt ℂ r z := hr_analytic z
    have hz_h_an : AnalyticAt ℂ h z := h_analytic z hz_cb
    have hz_rh_an : AnalyticAt ℂ (fun w => r w * h w) z := hz_r_an.mul hz_h_an
    have h_pnctd := hz_g_an.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hz_rh_an.meromorphicAt hz_cb (h_accpt z hz_cb) h_factor_mul
    exact (AnalyticAt.frequently_eq_iff_eventually_eq hz_g_an hz_rh_an).mp h_pnctd.frequently
  -- Pointwise equality on sphere: g = r * h, deriv g = deriv (r * h).
  have h_g_eq : ∀ z ∈ Metric.sphere c R, g z = r z * h z := fun z hz =>
    (h_nhds_eq z hz).eq_of_nhds
  have h_deriv_eq : ∀ z ∈ Metric.sphere c R,
      deriv g z = deriv (fun w => r w * h w) z := fun z hz =>
    (h_nhds_eq z hz).deriv_eq
  -- Equate integrands on sphere; rewrite the integral via `circleIntegral.integral_congr`.
  have h_int_eq : (∮ z in C(c, R), deriv g z / g z) =
      (∮ z in C(c, R), deriv (fun w => r w * h w) z / (r z * h z)) := by
    apply circleIntegral.integral_congr _hR.le
    intro z hz_sphere
    simp only []
    rw [h_g_eq z hz_sphere, h_deriv_eq z hz_sphere]
  -- The divisor is zero on the sphere (sphere has no zeros of g).
  have h_div_zero_sphere : ∀ z ∈ Metric.sphere c R,
      (MeromorphicOn.divisor g (Metric.closedBall c R)) z = 0 := by
    intro z hz
    have hz_cb := Metric.sphere_subset_closedBall hz
    rw [MeromorphicOn.divisor_apply hg_mer hz_cb,
        (_hg z hz_cb).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr (_hg_sphere z hz))]
    simp
  -- r is nonzero on sphere (divisor zero there).
  have hr_ne_sphere : ∀ z ∈ Metric.sphere c R, r z ≠ 0 := fun z hz =>
    Function.FactorizedRational.ne_zero (h_div_zero_sphere z hz)
  -- Decompose the integrand via logDeriv_mul on the sphere.
  have h_logDeriv_eq : ∀ z ∈ Metric.sphere c R,
      deriv (fun w => r w * h w) z / (r z * h z) =
      deriv r z / r z + deriv h z / h z := by
    intro z hz
    have hz_cb := Metric.sphere_subset_closedBall hz
    have hr_ne := hr_ne_sphere z hz
    have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz_cb⟩
    have hr_diff : DifferentiableAt ℂ r z := (hr_analytic z).differentiableAt
    have hh_diff : DifferentiableAt ℂ h z := (h_analytic z hz_cb).differentiableAt
    have := logDeriv_mul z hr_ne hh_ne hr_diff hh_diff
    simp only [logDeriv_apply] at this
    exact this
  -- Rewrite the integral via the logDeriv decomposition.
  have h_int_decomp : (∮ z in C(c, R), deriv (fun w => r w * h w) z / (r z * h z)) =
      (∮ z in C(c, R), deriv r z / r z + deriv h z / h z) := by
    apply circleIntegral.integral_congr _hR.le
    intro z hz_sphere
    exact h_logDeriv_eq z hz_sphere
  -- Each of `deriv r / r` and `deriv h / h` is continuous on the sphere,
  -- so circle-integrable.
  have hr_deriv_analytic : ∀ z, AnalyticAt ℂ (deriv r) z := fun z =>
    (hr_analytic z).deriv
  have hh_deriv_analytic : AnalyticOnNhd ℂ (deriv h) (Metric.closedBall c R) :=
    h_analytic.deriv
  have h_cont_dr_div_r : ContinuousOn (fun z => deriv r z / r z) (Metric.sphere c R) := by
    intro z hz
    have hr_ne := hr_ne_sphere z hz
    exact (((hr_deriv_analytic z).continuousAt).continuousWithinAt.div
      ((hr_analytic z).continuousAt).continuousWithinAt hr_ne)
  have h_cont_dh_div_h : ContinuousOn (fun z => deriv h z / h z) (Metric.sphere c R) := by
    intro z hz
    have hz_cb := Metric.sphere_subset_closedBall hz
    have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz_cb⟩
    exact (((hh_deriv_analytic z hz_cb).continuousAt).continuousWithinAt.div
      ((h_analytic z hz_cb).continuousAt).continuousWithinAt hh_ne)
  have h_int_split : (∮ z in C(c, R), deriv r z / r z + deriv h z / h z) =
      (∮ z in C(c, R), deriv r z / r z) + (∮ z in C(c, R), deriv h z / h z) :=
    circleIntegral.integral_add
      (h_cont_dr_div_r.circleIntegrable _hR.le)
      (h_cont_dh_div_h.circleIntegrable _hR.le)
  -- `∮ deriv h / h = 0` because h is analytic and non-vanishing on the closed disk
  -- (Cauchy-Goursat applied to the holomorphic integrand `deriv h / h`).
  have h_int_h_zero : (∮ z in C(c, R), deriv h z / h z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable _hR.le
      Set.countable_empty
    · intro z hz_cb
      have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz_cb⟩
      exact ((hh_deriv_analytic z hz_cb).continuousAt.continuousWithinAt.div
        (h_analytic z hz_cb).continuousAt.continuousWithinAt hh_ne)
    · intro z hz
      have hz_cb : z ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hz.1
      have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz_cb⟩
      have hdh_diff : DifferentiableAt ℂ (deriv h) z :=
        (hh_deriv_analytic z hz_cb).differentiableAt
      have hh_diff : DifferentiableAt ℂ h z := (h_analytic z hz_cb).differentiableAt
      exact hdh_diff.div hh_diff hh_ne
  -- Finset form of the divisor support, for explicit sum manipulations.
  set Dsupp := hdiv_finite.toFinset with hDsupp_def
  -- Support of `D` is contained in the open ball (the divisor vanishes off the zeros
  -- of `g`, and the sphere has no zeros). So every `u ∈ Dsupp` lies inside the disk.
  have hsupp_in_ball :
      ∀ u ∈ Dsupp, u ∈ Metric.ball c R := by
    intro u hu
    have hu_supp : u ∈ (MeromorphicOn.divisor g (Metric.closedBall c R)).support := by
      simpa [hDsupp_def] using hu
    have hu_cb : u ∈ Metric.closedBall c R :=
      (MeromorphicOn.divisor g (Metric.closedBall c R)).supportWithinDomain hu_supp
    -- u is not on the sphere because there `D u = 0`.
    by_contra hu_not_ball
    have hu_sphere : u ∈ Metric.sphere c R := by
      rw [Metric.mem_sphere]
      have hu_le := hu_cb
      simp [Metric.mem_closedBall] at hu_le
      simp [Metric.mem_ball, not_lt] at hu_not_ball
      linarith
    have := h_div_zero_sphere u hu_sphere
    exact hu_supp this
  -- Express `r z` as a Finset product over `Dsupp`.
  have hD_hfs : (fun u : ℂ => MeromorphicOn.divisor g (Metric.closedBall c R) u).HasFiniteSupport :=
    hdiv_finite
  have hr_eq_finset : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ (MeromorphicOn.divisor g (Metric.closedBall c R) u) := by
    intro z
    have heq := Function.FactorizedRational.finprod_eq_fun hD_hfs
    have : r z = ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor g (Metric.closedBall c R) u) := by
      rw [hr_def, heq]
    rw [this]
    rw [finprod_eq_prod_of_mulSupport_subset
      (f := fun u => (z - u) ^ (MeromorphicOn.divisor g (Metric.closedBall c R) u))
      (s := Dsupp)]
    intro u hu
    -- u is in the mulSupport, hence (z - u)^{D u} ≠ 1, so D u ≠ 0.
    simp only [Function.mem_mulSupport, ne_eq] at hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro h_zero
    apply hu
    rw [h_zero]
    simp
  -- For the integral computation, we use natural-power form (since divisor is non-negative).
  -- Define `(D u).toNat` and verify the equivalence.
  have hzpow_eq_pow : ∀ u : ℂ, ∀ z : ℂ,
      (z - u) ^ (MeromorphicOn.divisor g (Metric.closedBall c R) u) =
      (z - u) ^ ((MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat) := by
    intro u z
    rw [← zpow_natCast (z - u) ((MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat),
        Int.toNat_of_nonneg (hD_nonneg u)]
  -- r as a natural-power finset product.
  have hr_eq_natpow : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ ((MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat) := by
    intro z
    rw [hr_eq_finset z]
    apply Finset.prod_congr rfl
    intro u _
    exact hzpow_eq_pow u z
  -- Pointwise log-derivative decomposition of r on the sphere via logDeriv_prod.
  have h_logDeriv_r_eq : ∀ z ∈ Metric.sphere c R,
      deriv r z / r z = ∑ u ∈ Dsupp,
        ((MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) / (z - u)) := by
    intro z hz_sphere
    have hz_ne_u : ∀ u ∈ Dsupp, z - u ≠ 0 := by
      intro u hu hzu
      have hu_in_ball := hsupp_in_ball u hu
      have hz_eq : z = u := by linear_combination hzu
      rw [hz_eq] at hz_sphere
      have h1 : ‖u - c‖ = R := by
        rw [Metric.mem_sphere, dist_eq_norm] at hz_sphere
        exact hz_sphere
      have h2 : ‖u - c‖ < R := by
        rw [Metric.mem_ball, dist_eq_norm] at hu_in_ball
        exact hu_in_ball
      linarith
    -- Rewrite r as a finset product of natural powers (function-level).
    set D := MeromorphicOn.divisor g (Metric.closedBall c R)
    have hr_funext_nat : r = fun y => ∏ u ∈ Dsupp, (y - u) ^ ((D u).toNat) := by
      funext y; exact hr_eq_natpow y
    rw [show deriv r z / r z = logDeriv r z from rfl, hr_funext_nat]
    rw [logDeriv_prod]
    · -- Each summand: logDeriv (fun w => (w - u)^{n_u}) z = (n_u) / (z - u)
      apply Finset.sum_congr rfl
      intro u _
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
      rw [show (fun w : ℂ => (w - u) ^ ((D u).toNat)) =
          (fun w : ℂ => (fun w' => w' - u) w ^ ((D u).toNat)) from rfl,
          logDeriv_fun_pow hd, logDeriv_apply]
      have hnat_eq : ((D u).toNat : ℤ) = D u := Int.toNat_of_nonneg (hD_nonneg u)
      have hnat : ((D u).toNat : ℂ) = (D u : ℂ) := by exact_mod_cast hnat_eq
      rw [hnat]
      simp
      ring
    · -- (y - u)^{n_u} ≠ 0
      intro u hu
      exact pow_ne_zero _ (hz_ne_u u hu)
    · -- DifferentiableAt
      intro u _
      exact ((differentiable_id.sub_const u).pow _).differentiableAt
  -- Rewrite the integral of `deriv r / r` via the pointwise decomposition.
  have h_int_r_eq : (∮ z in C(c, R), deriv r z / r z) =
      (∮ z in C(c, R),
        ∑ u ∈ Dsupp, ((MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) / (z - u))) := by
    apply circleIntegral.integral_congr _hR.le
    intro z hz_sphere
    exact h_logDeriv_r_eq z hz_sphere
  -- Integrability of each summand on the sphere.
  have h_int_summand_cont : ∀ u ∈ Dsupp,
      ContinuousOn (fun z => (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) / (z - u))
        (Metric.sphere c R) := by
    intro u hu
    have hu_in_ball := hsupp_in_ball u hu
    refine continuousOn_const.div ((continuousOn_id.sub continuousOn_const)) (fun z hz => ?_)
    intro hzu_eq
    have hz_eq : z = u := by linear_combination hzu_eq
    rw [hz_eq] at hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm] at hu_in_ball
    linarith
  have h_summand_circleIntegrable : ∀ u ∈ Dsupp,
      CircleIntegrable (fun z => (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) / (z - u))
        c R := fun u hu => (h_int_summand_cont u hu).circleIntegrable _hR.le
  -- Each term: ∮ (D u) / (z - u) = (D u) * ∮ 1/(z - u) = (D u) * 2πi.
  have h_int_per_pole : ∀ u ∈ Dsupp,
      (∮ z in C(c, R), (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) / (z - u)) =
      (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) * (2 * Real.pi * Complex.I) := by
    intro u hu
    have hu_in_ball := hsupp_in_ball u hu
    have h_int1 : (∮ z in C(c, R), (z - u)⁻¹) = 2 * Real.pi * Complex.I :=
      circleIntegral.integral_sub_inv_of_mem_ball hu_in_ball
    calc (∮ z in C(c, R),
            (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) / (z - u))
        = (∮ z in C(c, R),
            (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) * (z - u)⁻¹) := by
          simp_rw [div_eq_mul_inv]
      _ = (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) *
            (∮ z in C(c, R), (z - u)⁻¹) :=
          circleIntegral.integral_const_mul _ _ _ _
      _ = (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ) * (2 * Real.pi * Complex.I) := by
          rw [h_int1]
  -- Sum the contributions.
  have h_int_r_final : (∮ z in C(c, R), deriv r z / r z) =
      (∑ u ∈ Dsupp, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) *
      (2 * Real.pi * Complex.I) := by
    rw [h_int_r_eq, circleIntegral.integral_fun_sum h_summand_circleIntegrable,
        Finset.sum_congr rfl h_int_per_pole, ← Finset.sum_mul]
  -- Convert finset sum to finsum.
  have h_finset_eq_finsum :
      (∑ u ∈ Dsupp, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) =
      (∑ᶠ u, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Dsupp)]
    · intro u hu
      change u ∈ hdiv_finite.toFinset
      rw [Set.Finite.mem_toFinset]
      intro hzero
      apply hu
      simp only [Function.mem_support, ne_eq] at hu
      push_cast at hu ⊢
      simp [hzero] at hu
  -- Express n in terms of the divisor sum.
  have h_finsum_int_eq_nat :
      (∑ᶠ u, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) =
      (((∑ᶠ u, MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat : ℤ) : ℂ) := by
    have h_nonneg : 0 ≤ ∑ᶠ u, MeromorphicOn.divisor g (Metric.closedBall c R) u :=
      finsum_nonneg (fun u => hD_nonneg u)
    rw [Int.toNat_of_nonneg h_nonneg]
    -- ∑ᶠ u, (D u : ℂ) = ((∑ᶠ u, D u) : ℂ)
    have hcast := AddMonoidHom.map_finsum (Int.castRingHom ℂ).toAddMonoidHom
      (f := fun u => MeromorphicOn.divisor g (Metric.closedBall c R) u) hdiv_finite
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Int.coe_castRingHom] at hcast
    rw [← hcast]
  -- The natural number we use is the (non-negative) sum of orders.
  refine ⟨(∑ᶠ u, MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat, ?_⟩
  -- Combine all steps to get the result.
  have hpi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  calc (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(c, R), deriv g z / g z)
      = (2 * Real.pi * Complex.I)⁻¹ *
          (∮ z in C(c, R), deriv (fun w => r w * h w) z / (r z * h z)) := by
        rw [h_int_eq]
    _ = (2 * Real.pi * Complex.I)⁻¹ *
          (∮ z in C(c, R), deriv r z / r z + deriv h z / h z) := by
        rw [h_int_decomp]
    _ = (2 * Real.pi * Complex.I)⁻¹ *
          ((∮ z in C(c, R), deriv r z / r z) + (∮ z in C(c, R), deriv h z / h z)) := by
        rw [h_int_split]
    _ = (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(c, R), deriv r z / r z) := by
        rw [h_int_h_zero, add_zero]
    _ = (2 * Real.pi * Complex.I)⁻¹ *
          ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) *
            (2 * Real.pi * Complex.I)) := by
        rw [h_int_r_final]
    _ = (∑ u ∈ Dsupp, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) := by
        field_simp
    _ = (∑ᶠ u, (MeromorphicOn.divisor g (Metric.closedBall c R) u : ℂ)) := h_finset_eq_finsum
    _ = (((∑ᶠ u, MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat : ℤ) : ℂ) :=
        h_finsum_int_eq_nat
    _ = (((∑ᶠ u, MeromorphicOn.divisor g (Metric.closedBall c R) u).toNat : ℂ)) := by push_cast; rfl

/-- **Argument principle for circles.** For a holomorphic function `f` on
a neighborhood of `closedBall c R` (analytic at every point of the closed
disk), with `f(z) ≠ w` on the sphere `|z − c| = R`, the contour integral
`(2πi)⁻¹ ∮_{C(c, R)} f'(z) / (f(z) − w) dz` is a natural number, equal to
the count of preimages of `w` inside the open disk (with multiplicity).
Follows from `cIntegralLogDeriv_isNat_of_nonzero_on_sphere` applied to
`g(z) := f(z) − w` (whose derivative coincides with `deriv f` since the
additive constant `w` contributes zero). -/
theorem argumentPrinciple_circle
    (f : ℂ → ℂ) (c : ℂ) {R : ℝ} (_hR : 0 < R) (_w : ℂ)
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (_hf_ne_w : ∀ z ∈ Metric.sphere c R, f z ≠ _w) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ *
      (∮ z in C(c, R), deriv f z / (f z - _w)) = (n : ℂ) := by
  have hg : AnalyticOnNhd ℂ (fun z => f z - _w) (Metric.closedBall c R) :=
    fun z hz => (_hf z hz).sub analyticAt_const
  have hg_sphere : ∀ z ∈ Metric.sphere c R, (fun z => f z - _w) z ≠ 0 := by
    intro z hz hzero
    exact _hf_ne_w z hz (sub_eq_zero.mp hzero)
  obtain ⟨n, hn⟩ :=
    cIntegralLogDeriv_isNat_of_nonzero_on_sphere (fun z => f z - _w) c _hR hg hg_sphere
  refine ⟨n, ?_⟩
  rw [← hn]
  congr 1
  apply circleIntegral.integral_congr _hR.le
  intro z _
  change deriv f z / (f z - _w) = deriv (fun y => f y - _w) z / (f z - _w)
  rw [deriv_sub_const _w]

/-- **Rectangle winding number.** The winding number of the
counterclockwise boundary of the closed rectangle `[a, b] × [c, d]`
around an interior point `w` equals `1`.

The four edges are evaluated separately by FTC. On the bottom, top,
and right edges the relevant path stays in `Complex.slitPlane`, so the
principal `Complex.log` antiderivative applies directly. The left
edge `x = a` crosses the negative real axis at `y = w.im` (because
`a < w.re`), so we instead use the translated branch
`logL z := Complex.log(-z)` (analytic for `Re z < 0`); the
contribution from this branch is shifted by `2π i` compared to the
principal log, and supplies the answer. Summing the four edges and
applying `Complex.arg_neg_eq_arg_*_pi_of_im_*` collapses the result to
`2π i`, which divided by `2π i` gives `1`. -/
theorem rectangleWindingNumber_inside_eq_one
    (a b c d : ℝ) (_hab : a < b) (_hcd : c < d) {w : ℂ}
    (hw_re : a < w.re ∧ w.re < b) (hw_im : c < w.im ∧ w.im < d) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹))
    = 1 := by
  -- 2πi ≠ 0, used for the final division.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- Real/imag formulas on each edge.
  have him_bot : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I - w).im = c - w.im := by
    intro x; simp
  have him_top : ∀ x : ℝ, ((x : ℂ) + (d : ℂ) * Complex.I - w).im = d - w.im := by
    intro x; simp
  have hre_right : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I - w).re = b - w.re := by
    intro y; simp
  have hre_left_neg : ∀ y : ℝ, (-((a : ℂ) + (y : ℂ) * Complex.I - w)).re = w.re - a := by
    intro y; simp
  -- Slit-plane membership.
  have hslit_bot : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_bot]
    intro h; linarith [hw_im.1]
  have hslit_top : ∀ x : ℝ, ((x : ℂ) + (d : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    right
    rw [him_top]
    intro h; linarith [hw_im.2]
  have hslit_right : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre_right]
    linarith [hw_re.2]
  have hslit_left_neg : ∀ y : ℝ,
      -((a : ℂ) + (y : ℂ) * Complex.I - w) ∈ Complex.slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hre_left_neg]
    linarith [hw_re.1]
  -- Non-vanishing.
  have hne_bot : ∀ x : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I - w) ≠ 0 := by
    intro x heq
    have := him_bot x
    rw [heq] at this; simp at this
    linarith [hw_im.1]
  have hne_top : ∀ x : ℝ, ((x : ℂ) + (d : ℂ) * Complex.I - w) ≠ 0 := by
    intro x heq
    have := him_top x
    rw [heq] at this; simp at this
    linarith [hw_im.2]
  have hne_right : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I - w) ≠ 0 := by
    intro y heq
    have := hre_right y
    rw [heq] at this; simp at this
    linarith [hw_re.2]
  have hne_left_neg : ∀ y : ℝ, -((a : ℂ) + (y : ℂ) * Complex.I - w) ≠ 0 := by
    intro y heq
    have := hre_left_neg y
    rw [heq] at this; simp at this
    linarith [hw_re.1]
  -- Bottom edge: ∫_a^b (x + ci - w)⁻¹ dx = log(b + ci - w) - log(a + ci - w).
  have h_bot : (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) =
      Complex.log ((b : ℂ) + (c : ℂ) * Complex.I - w) -
      Complex.log ((a : ℂ) + (c : ℂ) * Complex.I - w) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Complex.log ((y : ℂ) + (c : ℂ) * Complex.I - w))
    · intro x _
      have h_log := Complex.hasDerivAt_log (hslit_bot x)
      have h_inner : HasDerivAt (fun z : ℂ => z + (c : ℂ) * Complex.I - w) 1 (x : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc] using
          (hasDerivAt_id (x : ℂ)).add_const ((c : ℂ) * Complex.I - w)
      have h_comp := h_log.comp (x : ℂ) h_inner
      simpa using h_comp.comp_ofReal
    · apply Continuous.intervalIntegrable
      exact (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I - w)).inv₀ hne_bot
  -- Top edge: ∫_a^b (x + di - w)⁻¹ dx = log(b + di - w) - log(a + di - w).
  have h_top : (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) =
      Complex.log ((b : ℂ) + (d : ℂ) * Complex.I - w) -
      Complex.log ((a : ℂ) + (d : ℂ) * Complex.I - w) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => Complex.log ((y : ℂ) + (d : ℂ) * Complex.I - w))
    · intro x _
      have h_log := Complex.hasDerivAt_log (hslit_top x)
      have h_inner : HasDerivAt (fun z : ℂ => z + (d : ℂ) * Complex.I - w) 1 (x : ℂ) := by
        simpa [sub_eq_add_neg, add_assoc] using
          (hasDerivAt_id (x : ℂ)).add_const ((d : ℂ) * Complex.I - w)
      have h_comp := h_log.comp (x : ℂ) h_inner
      simpa using h_comp.comp_ofReal
    · apply Continuous.intervalIntegrable
      exact (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I - w)).inv₀ hne_top
  -- Right edge: ∫_c^d (b + yi - w)⁻¹ dy = -I · (log(b + di - w) - log(b + ci - w)).
  -- Antiderivative: F(y) = -I · log(b + yi - w). F'(y) = -I · I · (b+yi-w)⁻¹ = (b+yi-w)⁻¹.
  have h_right : (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      (-Complex.I) * Complex.log ((b : ℂ) + (d : ℂ) * Complex.I - w) -
      (-Complex.I) * Complex.log ((b : ℂ) + (c : ℂ) * Complex.I - w) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (-Complex.I) * Complex.log ((b : ℂ) + (y : ℂ) * Complex.I - w))
    · intro y _
      have h_log := Complex.hasDerivAt_log (hslit_right y)
      have h_inner : HasDerivAt (fun z : ℂ => (b : ℂ) + z * Complex.I - w) Complex.I (y : ℂ) := by
        have h1 : HasDerivAt (fun z : ℂ => z * Complex.I) Complex.I (y : ℂ) := by
          simpa using (hasDerivAt_id (y : ℂ)).mul_const Complex.I
        have h2 : HasDerivAt (fun z : ℂ => (b : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
          simpa using h1.const_add ((b : ℂ))
        simpa [sub_eq_add_neg] using h2.add_const (-w)
      have h_comp := h_log.comp (y : ℂ) h_inner
      have h_real := h_comp.comp_ofReal
      -- h_real has derivative (b+yi-w)⁻¹ * I.
      have h_mul := h_real.const_mul (-Complex.I)
      -- h_mul has derivative -I * ((b+yi-w)⁻¹ * I).
      -- Show this equals (b+yi-w)⁻¹.
      have h_simp : (-Complex.I) * (((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ * Complex.I) =
          ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ := by
        have h1 : (-Complex.I) * Complex.I = (1 : ℂ) := by
          rw [neg_mul, Complex.I_mul_I, neg_neg]
        linear_combination
          (((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) * h1
      rw [show (-Complex.I) * (((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ * Complex.I) =
          ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ from h_simp] at h_mul
      convert h_mul using 1
    · apply Continuous.intervalIntegrable
      have h_cont : Continuous fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I - w) := by
        fun_prop
      exact h_cont.inv₀ hne_right
  -- Left edge: ∫_c^d (a + yi - w)⁻¹ dy.
  -- Path real part = a - w.re < 0; imag part crosses 0 at y = w.im.
  -- Principal log is discontinuous; use the translated branch log(-z), analytic on
  -- Re z < 0. Antiderivative: F(y) = -I · log(-(a + yi - w)).
  -- F'(y) = -I · log'(-z) · (-I) = -I · (-(a+yi-w))⁻¹ · (-I)
  --       = -I · (-(a+yi-w)⁻¹) · (-I) = (a+yi-w)⁻¹.
  have h_left : (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      (-Complex.I) * Complex.log (-((a : ℂ) + (d : ℂ) * Complex.I - w)) -
      (-Complex.I) * Complex.log (-((a : ℂ) + (c : ℂ) * Complex.I - w)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (-Complex.I) *
        Complex.log (-((a : ℂ) + (y : ℂ) * Complex.I - w)))
    · intro y _
      have h_log := Complex.hasDerivAt_log (hslit_left_neg y)
      have h_inner : HasDerivAt (fun z : ℂ => -((a : ℂ) + z * Complex.I - w))
          (-Complex.I) (y : ℂ) := by
        have h1 : HasDerivAt (fun z : ℂ => z * Complex.I) Complex.I (y : ℂ) := by
          simpa using (hasDerivAt_id (y : ℂ)).mul_const Complex.I
        have h2 : HasDerivAt (fun z : ℂ => (a : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
          simpa using h1.const_add ((a : ℂ))
        have h3 : HasDerivAt (fun z : ℂ => (a : ℂ) + z * Complex.I - w) Complex.I (y : ℂ) := by
          simpa [sub_eq_add_neg] using h2.add_const (-w)
        exact h3.neg
      have h_comp := h_log.comp (y : ℂ) h_inner
      have h_real := h_comp.comp_ofReal
      -- h_real has derivative (-(a+yi-w))⁻¹ * (-I).
      have h_mul := h_real.const_mul (-Complex.I)
      -- h_mul has derivative -I * ((-(a+yi-w))⁻¹ * -I).
      have h_simp : (-Complex.I) *
          ((-((a : ℂ) + (y : ℂ) * Complex.I - w))⁻¹ * (-Complex.I)) =
          ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ := by
        rw [inv_neg]
        have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
          rw [neg_mul_neg, Complex.I_mul_I]
        linear_combination -(((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) * hII
      rw [show (-Complex.I) *
            ((-((a : ℂ) + (y : ℂ) * Complex.I - w))⁻¹ * (-Complex.I)) =
            ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹ from h_simp] at h_mul
      convert h_mul using 1
    · apply Continuous.intervalIntegrable
      have h_cont : Continuous fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - w) := by
        fun_prop
      have hne_left : ∀ y : ℝ, ((a : ℂ) + (y : ℂ) * Complex.I - w) ≠ 0 := by
        intro y heq
        apply hne_left_neg y
        rw [heq]; ring
      exact h_cont.inv₀ hne_left
  -- Auxiliary: I * I = -1 (for collapsing the I-factors picked up on right/left edges).
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  -- Branch-cut identities for the two left-edge corners: log(-z) - log(z) = ±π·I.
  -- Bottom-left corner: im < 0, so log(-z) = log(z) + π·I.
  have h_log_diff_BL : Complex.log (-((a : ℂ) + (c : ℂ) * Complex.I - w)) -
      Complex.log ((a : ℂ) + (c : ℂ) * Complex.I - w) =
      (Real.pi : ℂ) * Complex.I := by
    have him : ((a : ℂ) + (c : ℂ) * Complex.I - w).im < 0 := by
      have := him_bot a; rw [this]; linarith [hw_im.1]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.log_re, norm_neg, sub_self,
                 Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_zero, zero_mul]
    · simp only [Complex.sub_im, Complex.log_im,
                 Complex.arg_neg_eq_arg_add_pi_of_im_neg him,
                 Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
                 add_sub_cancel_left]
  -- Top-left corner: im > 0, so log(-z) = log(z) - π·I, i.e. log(z) - log(-z) = π·I.
  have h_log_diff_TL : Complex.log ((a : ℂ) + (d : ℂ) * Complex.I - w) -
      Complex.log (-((a : ℂ) + (d : ℂ) * Complex.I - w)) =
      (Real.pi : ℂ) * Complex.I := by
    have him : 0 < ((a : ℂ) + (d : ℂ) * Complex.I - w).im := by
      have := him_top a; rw [this]; linarith [hw_im.2]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.log_re, norm_neg, sub_self,
                 Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_zero, zero_mul]
    · simp only [Complex.sub_im, Complex.log_im,
                 Complex.arg_neg_eq_arg_sub_pi_of_im_pos him,
                 Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      ring
  -- Sum the four edges: telescoping cancels log of right-column corners, and the
  -- two remaining pairs collapse to 2πI via the branch-cut identities.
  have h_num : (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      2 * Real.pi * Complex.I := by
    rw [h_bot, h_right, h_top, h_left]
    linear_combination
      (Complex.log ((b : ℂ) + (c : ℂ) * Complex.I - w) -
       Complex.log ((b : ℂ) + (d : ℂ) * Complex.I - w) +
       Complex.log (-((a : ℂ) + (d : ℂ) * Complex.I - w)) -
       Complex.log (-((a : ℂ) + (c : ℂ) * Complex.I - w))) * hII +
      h_log_diff_BL + h_log_diff_TL
  rw [h_num]
  exact inv_mul_cancel₀ hpi

/-! ## Basic properties of `pathContourIntegral` -/

/-- Contour integral of the zero function vanishes. -/
theorem pathContourIntegral_zero (γ : ℝ → ℂ) (a b : ℝ) :
    pathContourIntegral γ a b (fun _ => 0) = 0 := by
  unfold pathContourIntegral
  simp

/-- Contour integral is additive in the integrand. -/
theorem pathContourIntegral_add (γ : ℝ → ℂ) (a b : ℝ) (f g : ℂ → ℂ)
    (hfγ : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b)
    (hgγ : IntervalIntegrable (fun t => g (γ t) * deriv γ t) MeasureTheory.volume a b) :
    pathContourIntegral γ a b (fun z => f z + g z) =
    pathContourIntegral γ a b f + pathContourIntegral γ a b g := by
  unfold pathContourIntegral
  simp only [add_mul]
  exact intervalIntegral.integral_add hfγ hgγ

/-- Contour integral is homogeneous: scaling the integrand by a constant
scales the integral. -/
theorem pathContourIntegral_const_smul (γ : ℝ → ℂ) (a b : ℝ) (k : ℂ) (f : ℂ → ℂ) :
    pathContourIntegral γ a b (fun z => k * f z) =
    k * pathContourIntegral γ a b f := by
  unfold pathContourIntegral
  simp only [mul_assoc]
  exact intervalIntegral.integral_const_mul k _

/-! ## Argument principle on rectangles

The rectangular analog of `cIntegralLogDeriv_isNat_of_nonzero_on_sphere`
/ `argumentPrinciple_circle`. Used by the modular `λ` to count
preimages inside a truncated fundamental-domain rectangle. The proofs
follow the same Weierstrass-factorization recipe as the circular
versions, with the four rectangle edge integrals replacing the single
circle integral. -/

set_option maxHeartbeats 400000 in
-- The proof clones the structure of `cIntegralLogDeriv_isNat_of_nonzero_on_sphere`
-- (Weierstrass factorization + log-derivative split + integration of each piece),
-- swapping the circle integral computations for the four rectangle edge integrals.
-- The combined elaboration pressure (codiscrete + AccPt + 4 pointwise edge
-- equalities + finite-sum manipulations) exceeds the default heartbeat limit.
/-- **Argument principle on rectangles (log-derivative form).** For a
function `g` analytic on a neighborhood of the closed rectangle
`Set.Icc a b ×ℂ Set.Icc c d`, with `g` non-vanishing on each of the
four boundary edges, the contour integral of `g'/g` around the
boundary (parameterized as bottom-CCW + right-up + top-CCW-reversed +
left-up-reversed) is `2πi` times the count of zeros of `g` inside the
open rectangle (with multiplicity).

The proof factors `g = (∏ᶠ u, (· − u)^{n_u}) · h` (Weierstrass-style
factorization on the closed rectangle, which is compact preconnected),
where the `n_u` are the multiplicities of the zeros of `g` inside the
open rectangle and `h` is analytic and non-vanishing on the closed
rectangle. The logarithmic derivative splits as
`g'/g = ∑ᶠ u, n_u / (· − u) + h'/h`. Integrating each summand around
the rectangle: `(2πi)⁻¹ ∮ n_u / (· − u) dz = n_u` by
`rectangleWindingNumber_inside_eq_one`, and `∮ h'/h dz = 0` by
Cauchy-Goursat applied to the holomorphic integrand. -/
theorem cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary
    (g : ℂ → ℂ) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hg : AnalyticOnNhd ℂ g (Set.Icc a b ×ℂ Set.Icc c d))
    (hg_bot : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc c d, g ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc c d, g ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * Complex.I) /
        g ((x : ℂ) + (c : ℂ) * Complex.I)) +
      Complex.I * (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
        g ((b : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
        g ((x : ℂ) + (d : ℂ) * Complex.I)) -
      Complex.I * (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
        g ((a : ℂ) + (y : ℂ) * Complex.I))) = (n : ℂ) := by
  -- Closed rectangle R and its convexity → preconnectedness.
  set R : Set ℂ := Set.Icc a b ×ℂ Set.Icc c d with hR_def
  have hg_mer : MeromorphicOn g R := hg.meromorphicOn
  have hR_convex : Convex ℝ R := by
    intro z₀ hz₀ z₁ hz₁ s t hs ht hst
    rw [hR_def, Complex.mem_reProdIm] at hz₀ hz₁
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · have hre : (s • z₀ + t • z₁).re = s * z₀.re + t * z₁.re := by
        simp [Complex.add_re]
      rw [hre]
      exact convex_Icc a b hz₀.1 hz₁.1 hs ht hst
    · have him : (s • z₀ + t • z₁).im = s * z₀.im + t * z₁.im := by
        simp [Complex.add_im]
      rw [him]
      exact convex_Icc c d hz₀.2 hz₁.2 hs ht hst
  have hR_preconn : IsPreconnected R := hR_convex.isPreconnected
  -- Witness corner z₀ = (a, c) where g ≠ 0.
  set z₀ : ℂ := (a : ℂ) + (c : ℂ) * Complex.I with hz₀_def
  have hz₀_re : z₀.re = a := by
    simp [hz₀_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_im : z₀.im = c := by
    simp [hz₀_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_in_R : z₀ ∈ R := by
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [hz₀_re]; exact Set.left_mem_Icc.mpr hab.le
    · rw [hz₀_im]; exact Set.left_mem_Icc.mpr hcd.le
  have hz₀_g_ne : g z₀ ≠ 0 := hg_bot a (Set.left_mem_Icc.mpr hab.le)
  have hz₀_analytic : AnalyticAt ℂ g z₀ := hg z₀ hz₀_in_R
  -- meromorphicOrderAt g z₀ ≠ ⊤ since g z₀ ≠ 0.
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    rw [hz₀_analytic.meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g z₀ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hz₀_g_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  -- Spread to all of R via preconnectedness.
  have hg_order : ∀ u ∈ R, meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    exact hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hR_preconn
      hz₀_in_R hu hz₀_order_ne_top
  -- Divisor support finite (R is compact).
  have hR_compact : IsCompact R :=
    IsCompact.reProdIm isCompact_Icc isCompact_Icc
  have hdiv_finite : (MeromorphicOn.divisor g R).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hR_compact
  -- extract_zeros_poles: g = r · h on codiscrete set.
  obtain ⟨h, h_analytic, h_nonzero, h_factor⟩ :=
    hg_mer.extract_zeros_poles
      (fun u : R => hg_order u.1 u.2)
      hdiv_finite
  -- Divisor non-negative (g analytic).
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g R :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  -- r := ∏ᶠ (·-u)^(D u). Analytic everywhere (D ≥ 0).
  set r : ℂ → ℂ :=
    ∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor g R) u) with hr_def
  have hr_analytic : ∀ z, AnalyticAt ℂ r z := fun z =>
    Function.FactorizedRational.analyticAt (hD_nonneg z)
  -- R is non-trivial (contains z₀ and the opposite corner).
  have hR_ntriv : R.Nontrivial := by
    refine ⟨z₀, hz₀_in_R, (b : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [hR_def, Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show ((b : ℂ) + (d : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]
        exact Set.right_mem_Icc.mpr hab.le
      · show ((b : ℂ) + (d : ℂ) * Complex.I).im ∈ Set.Icc c d
        have : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]
        exact Set.right_mem_Icc.mpr hcd.le
    · intro h_eq
      -- z₀ = (a, c) ≠ (b, d) since a < b.
      have h_re : z₀.re = ((b : ℂ) + (d : ℂ) * Complex.I).re := by rw [h_eq]
      rw [hz₀_re] at h_re
      have : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this] at h_re
      linarith
  -- Every point of R is an accumulation point (preconnected + nontrivial).
  have h_accpt : ∀ z ∈ R, AccPt z (Filter.principal R) :=
    fun z hz => hR_preconn.preperfect_of_nontrivial hR_ntriv z hz
  -- Codiscrete equality in `mul` form.
  have h_factor_mul : g =ᶠ[Filter.codiscreteWithin R]
      (fun w => r w * h w) := by
    filter_upwards [h_factor] with w hw
    simpa [smul_eq_mul] using hw
  -- For every point of R, get an nhds equality g = r · h (via codiscrete + AccPt + analyticity).
  have h_nhds_eq : ∀ z ∈ R, g =ᶠ[nhds z] (fun w => r w * h w) := by
    intro z hz
    have hz_g_an : AnalyticAt ℂ g z := hg z hz
    have hz_r_an : AnalyticAt ℂ r z := hr_analytic z
    have hz_h_an : AnalyticAt ℂ h z := h_analytic z hz
    have hz_rh_an : AnalyticAt ℂ (fun w => r w * h w) z := hz_r_an.mul hz_h_an
    have h_pnctd := hz_g_an.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hz_rh_an.meromorphicAt hz (h_accpt z hz) h_factor_mul
    exact (AnalyticAt.frequently_eq_iff_eventually_eq hz_g_an hz_rh_an).mp h_pnctd.frequently
  -- Pointwise equality g = r·h and deriv equality on each edge.
  have h_g_eq : ∀ z ∈ R, g z = r z * h z := fun z hz =>
    (h_nhds_eq z hz).eq_of_nhds
  have h_deriv_eq : ∀ z ∈ R, deriv g z = deriv (fun w => r w * h w) z := fun z hz =>
    (h_nhds_eq z hz).deriv_eq
  -- Divisor zero on each boundary edge (g ≠ 0 there).
  have h_div_zero_at_edge : ∀ z ∈ R, g z ≠ 0 →
      (MeromorphicOn.divisor g R) z = 0 := by
    intro z hz hz_g_ne
    rw [MeromorphicOn.divisor_apply hg_mer hz,
        (hg z hz).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hz_g_ne)]
    simp
  -- r ≠ 0 on each edge (where divisor zero).
  have hr_ne_at_edge : ∀ z ∈ R, g z ≠ 0 → r z ≠ 0 := fun z hz hz_g_ne =>
    Function.FactorizedRational.ne_zero (h_div_zero_at_edge z hz hz_g_ne)
  -- Membership of edge points in R.
  have h_bot_mem : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (c : ℂ) * Complex.I) ∈ R := by
    intro x hx
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · show ((x : ℂ) + (c : ℂ) * Complex.I).re ∈ Set.Icc a b
      have : ((x : ℂ) + (c : ℂ) * Complex.I).re = x := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact hx
    · show ((x : ℂ) + (c : ℂ) * Complex.I).im ∈ Set.Icc c d
      have : ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact Set.left_mem_Icc.mpr hcd.le
  have h_top_mem : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (d : ℂ) * Complex.I) ∈ R := by
    intro x hx
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · show ((x : ℂ) + (d : ℂ) * Complex.I).re ∈ Set.Icc a b
      have : ((x : ℂ) + (d : ℂ) * Complex.I).re = x := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact hx
    · show ((x : ℂ) + (d : ℂ) * Complex.I).im ∈ Set.Icc c d
      have : ((x : ℂ) + (d : ℂ) * Complex.I).im = d := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact Set.right_mem_Icc.mpr hcd.le
  have h_right_mem : ∀ y ∈ Set.Icc c d, ((b : ℂ) + (y : ℂ) * Complex.I) ∈ R := by
    intro y hy
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · show ((b : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
      have : ((b : ℂ) + (y : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact Set.right_mem_Icc.mpr hab.le
    · show ((b : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc c d
      have : ((b : ℂ) + (y : ℂ) * Complex.I).im = y := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact hy
  have h_left_mem : ∀ y ∈ Set.Icc c d, ((a : ℂ) + (y : ℂ) * Complex.I) ∈ R := by
    intro y hy
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · show ((a : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
      have : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact Set.left_mem_Icc.mpr hab.le
    · show ((a : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc c d
      have : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this]; exact hy
  -- logDeriv decomposition on each edge: (rh)'/(rh) = r'/r + h'/h.
  have h_logDeriv_split : ∀ z ∈ R, g z ≠ 0 →
      deriv (fun w => r w * h w) z / (r z * h z) =
      deriv r z / r z + deriv h z / h z := by
    intro z hz hz_g_ne
    have hr_ne := hr_ne_at_edge z hz hz_g_ne
    have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz⟩
    have hr_diff : DifferentiableAt ℂ r z := (hr_analytic z).differentiableAt
    have hh_diff : DifferentiableAt ℂ h z := (h_analytic z hz).differentiableAt
    have := logDeriv_mul z hr_ne hh_ne hr_diff hh_diff
    simp only [logDeriv_apply] at this
    exact this
  -- Combine: deriv g z / g z = r'/r + h'/h on each edge (where g ≠ 0).
  have h_int_eq_at_edge : ∀ z ∈ R, g z ≠ 0 →
      deriv g z / g z = deriv r z / r z + deriv h z / h z := by
    intro z hz hz_g_ne
    rw [h_g_eq z hz, h_deriv_eq z hz]
    exact h_logDeriv_split z hz hz_g_ne
  -- Apply on each edge: integrand of g'/g equals integrand of r'/r + h'/h.
  have h_int_bot : (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * Complex.I) /
      g ((x : ℂ) + (c : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
        h ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hab.le] at hx; exact hx
    exact h_int_eq_at_edge _ (h_bot_mem x hx_Icc) (hg_bot x hx_Icc)
  have h_int_top : (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
      g ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hab.le] at hx; exact hx
    exact h_int_eq_at_edge _ (h_top_mem x hx_Icc) (hg_top x hx_Icc)
  have h_int_right : (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
      g ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc c d := by
      rw [Set.uIcc_of_le hcd.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_right_mem y hy_Icc) (hg_right y hy_Icc)
  have h_int_left : (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
      g ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc c d := by
      rw [Set.uIcc_of_le hcd.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_left_mem y hy_Icc) (hg_left y hy_Icc)
  -- For Cauchy-Goursat applied to h'/h: h is analytic and non-vanishing on R.
  have h_h_ne : ∀ z ∈ R, h z ≠ 0 := fun z hz => h_nonzero ⟨z, hz⟩
  have h_dh_div_h_diff : DifferentiableOn ℂ (fun z => deriv h z / h z) R := by
    intro z hz
    have hh_ne := h_h_ne z hz
    have h_dh_an : AnalyticAt ℂ (deriv h) z := (h_analytic z hz).deriv
    have h_h_an : AnalyticAt ℂ h z := h_analytic z hz
    exact (h_dh_an.div h_h_an hh_ne).differentiableAt.differentiableWithinAt
  -- Rectangle Cauchy-Goursat for h'/h.
  have h_uIcc_re : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab.le
  have h_uIcc_im : Set.uIcc c d = Set.Icc c d := Set.uIcc_of_le hcd.le
  have h_z_w_re : (((a : ℂ) + (c : ℂ) * Complex.I).re,
      ((b : ℂ) + (d : ℂ) * Complex.I).re) = (a, b) := by
    refine Prod.ext ?_ ?_ <;>
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_z_w_im : (((a : ℂ) + (c : ℂ) * Complex.I).im,
      ((b : ℂ) + (d : ℂ) * Complex.I).im) = (c, d) := by
    refine Prod.ext ?_ ?_ <;>
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_cauchy_h :
      ((∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
          h ((x : ℂ) + (c : ℂ) * Complex.I)) -
        (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
          h ((x : ℂ) + (d : ℂ) * Complex.I))) +
      Complex.I • (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    have h_cg := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (fun z => deriv h z / h z) ((a : ℂ) + (c : ℂ) * Complex.I)
      ((b : ℂ) + (d : ℂ) * Complex.I) ?Hc ?Hd
    · -- Rewrite z.re, w.re, z.im, w.im
      have hzre : ((a : ℂ) + (c : ℂ) * Complex.I).re = a := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hwre : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hzim : ((a : ℂ) + (c : ℂ) * Complex.I).im = c := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hwim : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [hzre, hwre, hzim, hwim] at h_cg
      exact h_cg
    case Hc =>
      have hzre : ((a : ℂ) + (c : ℂ) * Complex.I).re = a := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hwre : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hzim : ((a : ℂ) + (c : ℂ) * Complex.I).im = c := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hwim : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [hzre, hwre, hzim, hwim, h_uIcc_re, h_uIcc_im]
      exact h_dh_div_h_diff.continuousOn
    case Hd =>
      have hzre : ((a : ℂ) + (c : ℂ) * Complex.I).re = a := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hwre : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hzim : ((a : ℂ) + (c : ℂ) * Complex.I).im = c := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hwim : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [hzre, hwre, hzim, hwim]
      rw [min_eq_left hab.le, max_eq_right hab.le, min_eq_left hcd.le, max_eq_right hcd.le]
      apply h_dh_div_h_diff.mono
      intro z hz
      rw [hR_def, Complex.mem_reProdIm]
      rw [Complex.mem_reProdIm] at hz
      refine ⟨?_, ?_⟩
      · exact Set.Ioo_subset_Icc_self hz.1
      · exact Set.Ioo_subset_Icc_self hz.2
  -- Express r as a Finset product over Dsupp.
  set Dsupp := hdiv_finite.toFinset with hDsupp_def
  -- Every u ∈ Dsupp is strictly inside the open rectangle.
  have hsupp_in_open : ∀ u ∈ Dsupp, u.re ∈ Set.Ioo a b ∧ u.im ∈ Set.Ioo c d := by
    intro u hu
    have hu_supp : u ∈ (MeromorphicOn.divisor g R).support := by
      simpa [hDsupp_def] using hu
    have hu_R : u ∈ R :=
      (MeromorphicOn.divisor g R).supportWithinDomain hu_supp
    -- u not on any of the four edges: if it were, divisor at u = 0, contradiction.
    have hu_re_Icc : u.re ∈ Set.Icc a b := (Complex.mem_reProdIm.mp hu_R).1
    have hu_im_Icc : u.im ∈ Set.Icc c d := (Complex.mem_reProdIm.mp hu_R).2
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo]
      refine ⟨lt_of_le_of_ne hu_re_Icc.1 (fun h_eq => ?_),
              lt_of_le_of_ne hu_re_Icc.2 (fun h_eq => ?_)⟩
      · -- u.re = a, then u is on left edge.
        have hu_eq : u = (a : ℂ) + (u.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        rw [hu_eq] at hu_supp
        apply hu_supp
        exact h_div_zero_at_edge ((a : ℂ) + (u.im : ℂ) * Complex.I)
          (h_left_mem u.im hu_im_Icc) (hg_left u.im hu_im_Icc)
      · -- u.re = b, then u is on right edge.
        have hu_eq : u = (b : ℂ) + (u.im : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_eq]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
        rw [hu_eq] at hu_supp
        apply hu_supp
        exact h_div_zero_at_edge ((b : ℂ) + (u.im : ℂ) * Complex.I)
          (h_right_mem u.im hu_im_Icc) (hg_right u.im hu_im_Icc)
    · rw [Set.mem_Ioo]
      refine ⟨lt_of_le_of_ne hu_im_Icc.1 (fun h_eq => ?_),
              lt_of_le_of_ne hu_im_Icc.2 (fun h_eq => ?_)⟩
      · -- u.im = c, then u is on bottom edge.
        have hu_eq : u = (u.re : ℂ) + (c : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
        rw [hu_eq] at hu_supp
        apply hu_supp
        exact h_div_zero_at_edge ((u.re : ℂ) + (c : ℂ) * Complex.I)
          (h_bot_mem u.re hu_re_Icc) (hg_bot u.re hu_re_Icc)
      · -- u.im = d, then u is on top edge.
        have hu_eq : u = (u.re : ℂ) + (d : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, h_eq]
        rw [hu_eq] at hu_supp
        apply hu_supp
        exact h_div_zero_at_edge ((u.re : ℂ) + (d : ℂ) * Complex.I)
          (h_top_mem u.re hu_re_Icc) (hg_top u.re hu_re_Icc)
  -- For each u, apply the rectangle winding number = 1.
  have h_per_pole : ∀ u ∈ Dsupp,
      (2 * Real.pi * Complex.I)⁻¹ * (
        (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹))
      = 1 := by
    intro u hu
    obtain ⟨hu_re, hu_im⟩ := hsupp_in_open u hu
    exact rectangleWindingNumber_inside_eq_one a b c d hab hcd hu_re hu_im
  -- finsum bridge.
  have hD_hfs : (fun u : ℂ => MeromorphicOn.divisor g R u).HasFiniteSupport :=
    hdiv_finite
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- Express r as a Finset product over Dsupp.
  have hr_eq_finset : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ (MeromorphicOn.divisor g R u) := by
    intro z
    have heq := Function.FactorizedRational.finprod_eq_fun hD_hfs
    have hrz : r z = ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor g R u) := by
      rw [hr_def, heq]
    rw [hrz]
    rw [finprod_eq_prod_of_mulSupport_subset
      (f := fun u => (z - u) ^ (MeromorphicOn.divisor g R u))
      (s := Dsupp)]
    intro u hu
    simp only [Function.mem_mulSupport, ne_eq] at hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro h_zero
    apply hu
    rw [h_zero]
    simp
  -- Natural-power form.
  have hzpow_eq_pow : ∀ u : ℂ, ∀ z : ℂ,
      (z - u) ^ (MeromorphicOn.divisor g R u) =
      (z - u) ^ ((MeromorphicOn.divisor g R u).toNat) := by
    intro u z
    rw [← zpow_natCast (z - u) ((MeromorphicOn.divisor g R u).toNat),
        Int.toNat_of_nonneg (hD_nonneg u)]
  have hr_eq_natpow : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ ((MeromorphicOn.divisor g R u).toNat) := by
    intro z
    rw [hr_eq_finset z]
    apply Finset.prod_congr rfl
    intro u _
    exact hzpow_eq_pow u z
  -- logDeriv r at boundary points (where g ≠ 0).
  have h_logDeriv_r_eq : ∀ z ∈ R, g z ≠ 0 →
      deriv r z / r z = ∑ u ∈ Dsupp,
        ((MeromorphicOn.divisor g R u : ℂ) / (z - u)) := by
    intro z hz hz_g_ne
    have hz_ne_u : ∀ u ∈ Dsupp, z - u ≠ 0 := by
      intro u hu hzu
      have hz_eq : z = u := by linear_combination hzu
      have hu_supp : u ∈ (MeromorphicOn.divisor g R).support := by
        simpa [hDsupp_def] using hu
      apply hu_supp
      rw [← hz_eq]
      exact h_div_zero_at_edge z hz hz_g_ne
    set D := MeromorphicOn.divisor g R
    have hr_funext_nat : r = fun y => ∏ u ∈ Dsupp, (y - u) ^ ((D u).toNat) := by
      funext y; exact hr_eq_natpow y
    rw [show deriv r z / r z = logDeriv r z from rfl, hr_funext_nat]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u _
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
      rw [show (fun w : ℂ => (w - u) ^ ((D u).toNat)) =
          (fun w : ℂ => (fun w' => w' - u) w ^ ((D u).toNat)) from rfl,
          logDeriv_fun_pow hd, logDeriv_apply]
      have hnat_eq : ((D u).toNat : ℤ) = D u := Int.toNat_of_nonneg (hD_nonneg u)
      have hnat : ((D u).toNat : ℂ) = (D u : ℂ) := by exact_mod_cast hnat_eq
      rw [hnat]
      simp
      ring
    · intro u hu
      exact pow_ne_zero _ (hz_ne_u u hu)
    · intro u _
      exact ((differentiable_id.sub_const u).pow _).differentiableAt
  -- Non-vanishing of (z - u) on each edge for u ∈ Dsupp.
  -- Contradiction comes from the boundary edge coordinate not matching
  -- the open-interior coordinate of u (e.g., bottom edge has Im z = c,
  -- but u ∈ Dsupp has Im u > c).
  have h_ne_bot : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (c : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨_, hu_im⟩ := hsupp_in_open u hu
    have h_im : ((x : ℂ) + (c : ℂ) * Complex.I - u).im = c - u.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_im_eq : c - u.im = 0 := by
      have := congrArg Complex.im h_eq
      rw [h_im] at this
      simpa using this
    obtain ⟨h1, _⟩ := hu_im
    linarith
  have h_ne_top : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (d : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨_, hu_im⟩ := hsupp_in_open u hu
    have h_im : ((x : ℂ) + (d : ℂ) * Complex.I - u).im = d - u.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_im_eq : d - u.im = 0 := by
      have := congrArg Complex.im h_eq
      rw [h_im] at this
      simpa using this
    obtain ⟨_, h2⟩ := hu_im
    linarith
  have h_ne_right : ∀ u ∈ Dsupp, ∀ _y : ℝ,
      (b : ℂ) + (_y : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu y h_eq
    obtain ⟨hu_re, _⟩ := hsupp_in_open u hu
    have h_re : ((b : ℂ) + (y : ℂ) * Complex.I - u).re = b - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : b - u.re = 0 := by
      have := congrArg Complex.re h_eq
      rw [h_re] at this
      simpa using this
    obtain ⟨_, h2⟩ := hu_re
    linarith
  have h_ne_left : ∀ u ∈ Dsupp, ∀ _y : ℝ,
      (a : ℂ) + (_y : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu y h_eq
    obtain ⟨hu_re, _⟩ := hsupp_in_open u hu
    have h_re : ((a : ℂ) + (y : ℂ) * Complex.I - u).re = a - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : a - u.re = 0 := by
      have := congrArg Complex.re h_eq
      rw [h_re] at this
      simpa using this
    obtain ⟨h1, _⟩ := hu_re
    linarith
  -- IntervalIntegrable for each summand on each edge.
  have h_summand_int_bot : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g R u : ℂ) / ((x : ℂ) + (c : ℂ) * Complex.I - u))
        MeasureTheory.volume a b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I - u) := by
      fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_bot u hu x)
  have h_summand_int_top : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g R u : ℂ) / ((x : ℂ) + (d : ℂ) * Complex.I - u))
        MeasureTheory.volume a b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I - u) := by
      fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_top u hu x)
  have h_summand_int_right : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g R u : ℂ) / ((b : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume c d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I - u) := by
      fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_right u hu y)
  have h_summand_int_left : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g R u : ℂ) / ((a : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume c d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - u) := by
      fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_left u hu y)
  -- IntervalIntegrable of r'/r and h'/h on each edge.
  have hr_diff_global : Differentiable ℂ r := fun z => (hr_analytic z).differentiableAt
  have hr_cont : Continuous r := hr_diff_global.continuous
  have h_dr_cont : Continuous (deriv r) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    exact (hr_analytic z).deriv.continuousAt
  have h_dr_div_r_int_bot : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_bot u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_top : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_top u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_right : IntervalIntegrable
      (fun y : ℝ => deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume c d := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ y : ℝ, r ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_right u hu y))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_left : IntervalIntegrable
      (fun y : ℝ => deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume c d := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ y : ℝ, r ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_left u hu y))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  -- h'/h interval-integrable on each edge via continuity on R + parametrization.
  have h_dh_div_h_int_bot : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
        h ((x : ℂ) + (c : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I))
        (Set.uIcc a b) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I)
        (Set.uIcc a b) R := by
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_bot_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_top : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I))
        (Set.uIcc a b) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I)
        (Set.uIcc a b) R := by
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_top_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_right : IntervalIntegrable
      (fun y : ℝ => deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume c d := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I))
        (Set.uIcc c d) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc c d) R := by
      intro y hy
      rw [Set.uIcc_of_le hcd.le] at hy
      exact h_right_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_left : IntervalIntegrable
      (fun y : ℝ => deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume c d := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I))
        (Set.uIcc c d) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc c d) R := by
      intro y hy
      rw [Set.uIcc_of_le hcd.le] at hy
      exact h_left_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  -- Per-edge r-integral decomposition: ∫ r'/r = ∑_u (D u : ℂ) * ∫ (z - u)⁻¹.
  have h_bot_r_decomp : (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
        (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
          r ((x : ℂ) + (c : ℂ) * Complex.I)) =
        (∫ x in a..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) /
          ((x : ℂ) + (c : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_logDeriv_r_eq _ (h_bot_mem x hx) (hg_bot x hx)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_bot]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_top_r_decomp : (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
          r ((x : ℂ) + (d : ℂ) * Complex.I)) =
        (∫ x in a..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) /
          ((x : ℂ) + (d : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_logDeriv_r_eq _ (h_top_mem x hx) (hg_top x hx)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_top]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_right_r_decomp : (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
        (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
          r ((b : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in c..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) /
          ((b : ℂ) + (y : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hcd.le] at hy
      exact h_logDeriv_r_eq _ (h_right_mem y hy) (hg_right y hy)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_right]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_left_r_decomp : (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
        (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
          r ((a : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in c..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) /
          ((a : ℂ) + (y : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hcd.le] at hy
      exact h_logDeriv_r_eq _ (h_left_mem y hy) (hg_left y hy)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_left]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  -- Per-pole 4-edge combination = 2πi.
  have h_per_pole_eq : ∀ u ∈ Dsupp,
      (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) =
      2 * Real.pi * Complex.I := by
    intro u hu
    have h := h_per_pole u hu
    -- (2πi)⁻¹ * X = 1 ⇒ X = 2πi (multiplying both sides by 2πi).
    have hk : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ *
        ((∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹))) =
        (2 * Real.pi * Complex.I) * 1 := by
      rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at hk
    exact hk
  -- h-edges sum = 0 (rearrange h_cauchy_h from `bot - top + I•right - I•left` to the goal form).
  have h_h_sum_zero :
      ((∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
          h ((x : ℂ) + (c : ℂ) * Complex.I)) +
       Complex.I * (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
          h ((b : ℂ) + (y : ℂ) * Complex.I)) -
       (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
          h ((x : ℂ) + (d : ℂ) * Complex.I)) -
       Complex.I * (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
          h ((a : ℂ) + (y : ℂ) * Complex.I))) = 0 := by
    have := h_cauchy_h
    simp only [smul_eq_mul] at this
    linear_combination this
  -- Per-edge split: ∫ (r'/r + h'/h) = ∫ r'/r + ∫ h'/h.
  have h_bot_split : (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
        h ((x : ℂ) + (c : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I)) +
      (∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
        h ((x : ℂ) + (c : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_bot h_dh_div_h_int_bot
  have h_top_split : (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_top h_dh_div_h_int_top
  have h_right_split : (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_right h_dh_div_h_int_right
  have h_left_split : (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_left h_dh_div_h_int_left
  -- Convert Finset sum to finsum.
  have h_finset_eq_finsum :
      (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ)) =
      (∑ᶠ u, (MeromorphicOn.divisor g R u : ℂ)) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Dsupp)]
    intro u hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro hzero
    apply hu
    simp only [Function.mem_support, ne_eq] at hu
    push_cast at hu ⊢
    simp [hzero] at hu
  have h_finsum_int_eq_nat :
      (∑ᶠ u, (MeromorphicOn.divisor g R u : ℂ)) =
      (((∑ᶠ u, MeromorphicOn.divisor g R u).toNat : ℤ) : ℂ) := by
    have h_nonneg : 0 ≤ ∑ᶠ u, MeromorphicOn.divisor g R u :=
      finsum_nonneg (fun u => hD_nonneg u)
    rw [Int.toNat_of_nonneg h_nonneg]
    have hcast := AddMonoidHom.map_finsum (Int.castRingHom ℂ).toAddMonoidHom
      (f := fun u => MeromorphicOn.divisor g R u) hdiv_finite
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Int.coe_castRingHom] at hcast
    rw [← hcast]
  -- The natural number we use is the (non-negative) sum of orders.
  refine ⟨(∑ᶠ u, MeromorphicOn.divisor g R u).toNat, ?_⟩
  -- Final calc.
  calc (2 * Real.pi * Complex.I)⁻¹ * (
        (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * Complex.I) /
          g ((x : ℂ) + (c : ℂ) * Complex.I)) +
        Complex.I * (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
          g ((b : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
          g ((x : ℂ) + (d : ℂ) * Complex.I)) -
        Complex.I * (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
          g ((a : ℂ) + (y : ℂ) * Complex.I)))
      = (2 * Real.pi * Complex.I)⁻¹ * (
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
            (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
            h ((x : ℂ) + (c : ℂ) * Complex.I))) +
        Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
            (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
         (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
            h ((b : ℂ) + (y : ℂ) * Complex.I))) -
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
            (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
            h ((x : ℂ) + (d : ℂ) * Complex.I))) -
        Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
            (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
         (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
            h ((a : ℂ) + (y : ℂ) * Complex.I)))) := by
          rw [h_int_bot, h_int_top, h_int_right, h_int_left,
              h_bot_split, h_top_split, h_right_split, h_left_split,
              h_bot_r_decomp, h_top_r_decomp, h_right_r_decomp, h_left_r_decomp]
    _ = (((∑ᶠ u, MeromorphicOn.divisor g R u).toNat : ℂ)) := by
          have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
            refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
            · exact two_ne_zero
            · exact_mod_cast Real.pi_ne_zero
          -- Key combining lemma: 4 weighted Finset sums + per-pole reduction give
          -- `(∑ u ∈ Dsupp, D u) * 2πi`.
          have h_combine :
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
              Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
              Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) =
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ)) *
                (2 * Real.pi * Complex.I) := by
            simp only [Finset.mul_sum]
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
                ← Finset.sum_sub_distrib, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro u hu
            have h := h_per_pole_eq u hu
            linear_combination (MeromorphicOn.divisor g R u : ℂ) * h
          -- Rearrange the goal expression: separate r-part from h-part.
          rw [show
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
                    h ((x : ℂ) + (c : ℂ) * Complex.I))) +
              Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
                (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
                    h ((b : ℂ) + (y : ℂ) * Complex.I))) -
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
                    h ((x : ℂ) + (d : ℂ) * Complex.I))) -
              Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
                (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
                    h ((a : ℂ) + (y : ℂ) * Complex.I))) =
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
                Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
                Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ) *
                  (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹))) +
              ((∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
                  h ((x : ℂ) + (c : ℂ) * Complex.I)) +
                Complex.I * (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
                  h ((b : ℂ) + (y : ℂ) * Complex.I)) -
                (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
                  h ((x : ℂ) + (d : ℂ) * Complex.I)) -
                Complex.I * (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
                  h ((a : ℂ) + (y : ℂ) * Complex.I))) from by ring]
          rw [h_combine, h_h_sum_zero, add_zero]
          rw [mul_comm ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g R u : ℂ))) (2 * Real.pi * Complex.I)]
          rw [inv_mul_cancel_left₀ hpi]
          exact h_finset_eq_finsum.trans (h_finsum_int_eq_nat.trans (by push_cast; rfl))

/-- **Argument principle on rectangles (preimage form).** For a function
`f` analytic on a neighborhood of the closed rectangle
`Set.Icc a b ×ℂ Set.Icc c d`, with `f ≠ w` on each of the four boundary
edges, the contour integral of `f'/(f − w)` around the boundary
(parameterized as bottom-CCW + right-up + top-CCW-reversed +
left-up-reversed) is `2πi` times the count of preimages of `w` inside
the open rectangle (with multiplicity). Follows from
`cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary` applied to
`g(z) := f(z) − w`. -/
theorem argumentPrinciple_rectangle
    (f : ℂ → ℂ) (a b c d : ℝ) (_hab : a < b) (_hcd : c < d) (_w : ℂ)
    (_hf : AnalyticOnNhd ℂ f (Set.Icc a b ×ℂ Set.Icc c d))
    (_hf_bot : ∀ x ∈ Set.Icc a b, f ((x : ℂ) + (c : ℂ) * Complex.I) ≠ _w)
    (_hf_top : ∀ x ∈ Set.Icc a b, f ((x : ℂ) + (d : ℂ) * Complex.I) ≠ _w)
    (_hf_right : ∀ y ∈ Set.Icc c d, f ((b : ℂ) + (y : ℂ) * Complex.I) ≠ _w)
    (_hf_left : ∀ y ∈ Set.Icc c d, f ((a : ℂ) + (y : ℂ) * Complex.I) ≠ _w) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..b, deriv f ((x : ℂ) + (c : ℂ) * Complex.I) /
        (f ((x : ℂ) + (c : ℂ) * Complex.I) - _w)) +
      Complex.I * (∫ y in c..d, deriv f ((b : ℂ) + (y : ℂ) * Complex.I) /
        (f ((b : ℂ) + (y : ℂ) * Complex.I) - _w)) -
      (∫ x in a..b, deriv f ((x : ℂ) + (d : ℂ) * Complex.I) /
        (f ((x : ℂ) + (d : ℂ) * Complex.I) - _w)) -
      Complex.I * (∫ y in c..d, deriv f ((a : ℂ) + (y : ℂ) * Complex.I) /
        (f ((a : ℂ) + (y : ℂ) * Complex.I) - _w))) = (n : ℂ) := by
  -- Apply the log-derivative form to g(z) := f(z) - w.
  have hg : AnalyticOnNhd ℂ (fun z => f z - _w) (Set.Icc a b ×ℂ Set.Icc c d) :=
    fun z hz => (_hf z hz).sub analyticAt_const
  have hg_bot : ∀ x ∈ Set.Icc a b, (fun z => f z - _w) ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0 := by
    intro x hx h_eq
    exact _hf_bot x hx (sub_eq_zero.mp h_eq)
  have hg_top : ∀ x ∈ Set.Icc a b, (fun z => f z - _w) ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0 := by
    intro x hx h_eq
    exact _hf_top x hx (sub_eq_zero.mp h_eq)
  have hg_right : ∀ y ∈ Set.Icc c d, (fun z => f z - _w) ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y hy h_eq
    exact _hf_right y hy (sub_eq_zero.mp h_eq)
  have hg_left : ∀ y ∈ Set.Icc c d, (fun z => f z - _w) ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y hy h_eq
    exact _hf_left y hy (sub_eq_zero.mp h_eq)
  obtain ⟨n, hn⟩ :=
    cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary
      (fun z => f z - _w) a b c d _hab _hcd hg hg_bot hg_top hg_right hg_left
  refine ⟨n, ?_⟩
  rw [← hn]
  -- The two expressions differ in their integrands: f'(z)/(f(z) - w) vs
  -- (deriv (fun y => f y - w) z)/(f z - w). Since deriv (·-w) = deriv f,
  -- the integrands are equal pointwise, so the integrals are equal.
  congr 1
  have h_deriv_eq : ∀ z : ℂ, deriv (fun y => f y - _w) z = deriv f z := fun z => deriv_sub_const _w
  simp only [h_deriv_eq]

/-- **Cauchy-Goursat for the upper-left lune (rectangle corner minus
upper-left quarter disk).** The "upper-left lune" is the closed region
`(Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀`
— a small region in the upper-left corner of the disk's bounding rectangle,
outside the disk. It is bounded by:
* Left edge: `x = e.re - R₀`, `y ∈ [e.im, e.im + R₀]`.
* Top edge: `y = e.im + R₀`, `x ∈ [e.re - R₀, e.re]`.
* Upper-left quarter arc: `θ ∈ [π/2, π]` of `circleMap e R₀`.

The closed lune is **star-shaped from the outer corner** `(e.re - R₀, e.im + R₀)`
(verified geometrically: for any lune point `(x, y)` the segment to the outer
corner stays outside the disk). For `f` continuous on the closed lune and
complex-differentiable on its open interior, the boundary contour integral
(traversed CCW with the lune interior on the left) equals zero.

This lemma + its top-right mirror power the decomposition proof of
`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn` (the
F_Y-shape CG): the region splits into three rectangles (closed under
Mathlib's `integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`)
plus the two lunes. Shared edges cancel and the lune contributions
provide the upper semicircle integral.

**Hypothesis form.** `Hd` asks for differentiability on the open box
`(Ioo a e.re) × (Ioo e.im d)` minus `closedBall e R₀`, where
`a < e.re - R₀` and `e.im + R₀ < d`. This open set is star-shaped from
the outer corner `V = (e.re - R₀, e.im + R₀)`: the segment from `V` to
any point in the upper-left-of-`e` open region outside `closedBall`
stays outside `closedBall`. At the half-annulus call site, the broader
`Hd` on `(Ioo a b) × (Ioo e.im d)` restricts to this form by `mono`.

**Proof strategy.** Define `F := starPrimitive V f` on the star-shaped
open set `U' := (Ioo a e.re) × (Ioo e.im d) \ closedBall e R₀`. By
`hasDerivAt_starPrimitive`, `F` has derivative `f` on `U'`. The left
and top edge integrals equal `F(B) - F(V)` and `F(T) - F(V)`
respectively by direct parameter substitution in the `starPrimitive`
definition. The arc integral equals `F(B) - F(T)` by an ε-arc
limiting argument: for ε > 0 small, parametrize a slightly outer
ε-arc `z_ε(θ) := e + (R₀+ε) e^{iθ}` on `θ ∈ [π/2 + ε, π - ε]`; both
endpoints lie in `U'`, FTC applies, and the limit ε → 0 recovers the
arc integral on `[π/2, π]` via dominated convergence and continuity
of `F` at `T` and `B`. The three boundary-piece identities telescope
to zero. -/
theorem integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (a d : ℝ) (h_a_lune : a < e.re - R₀) (h_d_lune : e.im + R₀ < d)
    (Hc : ContinuousOn f
      ((Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    -Complex.I * (∫ y in e.im..(e.im + R₀), f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x in (e.re - R₀)..e.re, f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) -
    (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- Top edge integral via horizontal-segment `starPrimitive` substitution.
  have hF_T :=
    Complex.starPrimitive_horizontal_eq_intervalIntegral f (e.re - R₀) e.re (e.im + R₀)
  -- F(B) via vertical-segment `starPrimitive` substitution (from `y = e.im + R₀`
  -- down to `y = e.im`), then reversing the integration direction.
  have hF_B_raw :=
    Complex.starPrimitive_vertical_eq_intervalIntegral f (e.re - R₀) (e.im + R₀) e.im
  have hF_B :
      Complex.starPrimitive
          ((↑(e.re - R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re - R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) =
        -Complex.I *
          ∫ y in e.im..(e.im + R₀),
            f ((↑(e.re - R₀) : ℂ) + (↑y : ℂ) * Complex.I) := by
    rw [hF_B_raw, intervalIntegral.integral_symm]
    ring
  -- Arc identity from the dedicated sub-lemma.
  have h_arc :=
    Complex.topLeftLune_arc_integral_eq_starPrimitive_sub
      f e R₀ hR₀ a d h_a_lune h_d_lune Hc Hd
  -- Goal collapses to `F(B) - F(T) - (F(B) - F(T)) = 0` after substitution;
  -- `linear_combination` with coercion normalization closes it.
  linear_combination (norm := (push_cast; ring)) -h_arc + hF_T - hF_B

/-- **Cauchy-Goursat for the upper-right lune (rectangle corner minus
upper-right quarter disk).** The mirror of
`integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn`
across `x = e.re`. The "upper-right lune" is the closed region
`(Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀`,
star-shaped from the outer corner `(e.re + R₀, e.im + R₀)`.

**Hypothesis form.** `Hd` asks for differentiability on
`(Ioo e.re b) × (Ioo e.im d)` minus `closedBall e R₀`, where
`e.re + R₀ < b` and `e.im + R₀ < d` — the upper-right-of-`e` open box
minus the closed disk, star-shaped from `V_R = (e.re + R₀, e.im + R₀)`.
The proof mirrors the top-left case across `x = e.re`. -/
theorem integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (b d : ℝ) (h_b_lune : e.re + R₀ < b) (h_d_lune : e.im + R₀ < d)
    (Hc : ContinuousOn f
      ((Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    Complex.I * (∫ y in e.im..(e.im + R₀), f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x in e.re..(e.re + R₀), f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) -
    (∫ θ in (0:ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- F(T): horizontal substitution from V_R (x = e.re + R₀) to T (x = e.re),
  -- then reverse direction so the integral goes `e.re..(e.re + R₀)`.
  have hF_T_raw :=
    Complex.starPrimitive_horizontal_eq_intervalIntegral f (e.re + R₀) e.re (e.im + R₀)
  have hF_T :
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑e.re : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) =
        -∫ x in e.re..(e.re + R₀),
            f ((↑x : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) := by
    rw [hF_T_raw, intervalIntegral.integral_symm]
  -- F(W): vertical substitution from V_R (y = e.im + R₀) down to W (y = e.im),
  -- reversing direction.
  have hF_W_raw :=
    Complex.starPrimitive_vertical_eq_intervalIntegral f (e.re + R₀) (e.im + R₀) e.im
  have hF_W :
      Complex.starPrimitive
          ((↑(e.re + R₀) : ℂ) + (↑(e.im + R₀) : ℂ) * Complex.I) f
          ((↑(e.re + R₀) : ℂ) + (↑e.im : ℂ) * Complex.I) =
        -Complex.I *
          ∫ y in e.im..(e.im + R₀),
            f ((↑(e.re + R₀) : ℂ) + (↑y : ℂ) * Complex.I) := by
    rw [hF_W_raw, intervalIntegral.integral_symm]
    ring
  -- Arc identity from the dedicated sub-lemma (mirror of the top-left case).
  have h_arc :=
    Complex.topRightLune_arc_integral_eq_starPrimitive_sub
      f e R₀ hR₀ b d h_b_lune h_d_lune Hc Hd
  -- Goal collapses to `F(T) - F(W) - (F(T) - F(W)) = 0` after substitution.
  linear_combination (norm := (push_cast; ring)) -h_arc - hF_T + hF_W

/-- **Cauchy-Goursat for a rectangle with an upper half-disk removed
from the bottom boundary.** For `f` continuous on the closed region
`(Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀` (the rectangle
`[a, b] × [e.im, d]` with the open upper half of the disk centered at
`e` on the bottom edge removed) and complex-differentiable on its open
interior, the contour integral around the boundary equals zero.

The region is the **truncated `Γ(2)` fundamental domain shape** with
`e.im = 0` (the rectangle's bottom y coincides with the disk center's
imaginary part). The boundary, traversed counter-clockwise (region
interior on the left), consists of:
* Bottom-left cut segment: `(a, e.im) → (e.re − R₀, e.im)`, contributing
  `∫_a^{e.re−R₀} f(x + e.im·i) dx`.
* Upper semicircle (clockwise around the disk center, from
  `(e.re − R₀, e.im)` through `(e.re, e.im + R₀)` to `(e.re + R₀, e.im)`),
  contributing `−∫_0^π f(circleMap e R₀ θ) · (i·R₀·exp(i·θ)) dθ`.
* Bottom-right cut segment: `(e.re + R₀, e.im) → (b, e.im)`, contributing
  `∫_{e.re+R₀}^b f(x + e.im·i) dx`.
* Right edge: `(b, e.im) → (b, d)`, contributing
  `i·∫_{e.im}^d f(b + y·i) dy`.
* Top edge (reversed): `(b, d) → (a, d)`, contributing
  `−∫_a^b f(x + d·i) dx`.
* Left edge (reversed): `(a, d) → (a, e.im)`, contributing
  `−i·∫_{e.im}^d f(a + y·i) dy`.

The region is simply-connected; Cauchy-Goursat for simply-connected
regions then gives zero. The proof uses a 5-piece decomposition into
3 sub-rectangles (Mathlib's rect CG) plus the two top lunes
(`topLeftLune`, `topRightLune`), with shared edges cancelling and the
lune arc contributions combining into the upper semicircle. -/
theorem integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (_hab : a < b) (h_e_im_d : e.im < d) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (Hc : ContinuousOn f ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀')) :
    (∫ x in a..(e.re - R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    (∫ x in (e.re + R₀)..b, f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    Complex.I * (∫ y in e.im..d, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) -
    Complex.I * (∫ y in e.im..d, f ((a : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ θ in (0:ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- Strengthened `Hd` is existential: extract the underlying differentiability
  -- on the slightly enlarged set `(Ioo a b × Ioo e.im d) \ closedBall e R₀'` for
  -- some `R₀' < R₀`. The rectangle Cauchy-Goursat call only needs the original
  -- `closedBall e R₀` form, derived by `mono` from the enlargement. The lune
  -- CG calls take the existential form directly.
  obtain ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'⟩ := Hd
  have Hd_orig : DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀) := by
    apply Hd'.mono
    rintro z ⟨hz_box, hz_not_R0⟩
    exact ⟨hz_box, fun hz_R0' =>
      hz_not_R0 (Metric.closedBall_subset_closedBall hR₀'_lt.le hz_R0')⟩
  -- 5-piece decomposition: 3 rectangles + 2 lunes.
  -- All sub-rectangles strictly avoid the disk (distance ≥ R₀ from e via real or
  -- imaginary part of (z - e)).
  -- Step 1: subset inclusions for rect A = [a, e.re-R₀] × [e.im, d].
  have h_A_closed_sub :
      (Set.Icc a (e.re - R₀) ×ℂ Set.Icc e.im d) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Icc] at hz ⊢
      exact ⟨hz.1.1, by linarith [hz.1.2]⟩
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      rw [Set.mem_Icc] at hz
      have h_re_diff : (z - e).re ≤ -R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.2]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| ≥ R₀ := by
        rw [abs_of_nonpos (by linarith : (z - e).re ≤ 0)]; linarith
      linarith
  have h_A_open_sub :
      (Set.Ioo a (e.re - R₀) ×ℂ Set.Ioo e.im d) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Ioo] at hz ⊢
      exact ⟨hz.1.1, by linarith [hz.1.2]⟩
    · intro h_ball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_ball
      rw [Set.mem_Ioo] at hz
      have h_re_diff : (z - e).re < -R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.2]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| > R₀ := by
        rw [abs_of_neg (by linarith : (z - e).re < 0)]; linarith
      linarith
  -- Subset inclusions for rect B = [e.re+R₀, b] × [e.im, d].
  have h_B_closed_sub :
      (Set.Icc (e.re + R₀) b ×ℂ Set.Icc e.im d) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Icc] at hz ⊢
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      rw [Set.mem_Icc] at hz
      have h_re_diff : (z - e).re ≥ R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.1]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| ≥ R₀ := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (z - e).re)]; linarith
      linarith
  have h_B_open_sub :
      (Set.Ioo (e.re + R₀) b ×ℂ Set.Ioo e.im d) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, hz.2⟩
      rw [Set.mem_Ioo] at hz ⊢
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    · intro h_ball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_ball
      rw [Set.mem_Ioo] at hz
      have h_re_diff : (z - e).re > R₀ := by
        rw [Complex.sub_re]; linarith [hz.1.1]
      have h_norm_ge : |((z - e).re)| ≤ ‖z - e‖ := Complex.abs_re_le_norm _
      have h_abs : |((z - e).re)| > R₀ := by
        rw [abs_of_pos (by linarith : (0:ℝ) < (z - e).re)]; linarith
      linarith
  -- Subset inclusions for rect C = [e.re-R₀, e.re+R₀] × [e.im+R₀, d].
  have h_C_closed_sub :
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc (e.im + R₀) d) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc] at hz ⊢
        exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      · rw [Set.mem_Icc] at hz ⊢
        exact ⟨by linarith [hz.2.1], hz.2.2⟩
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      rw [Set.mem_Icc] at hz
      have h_im_diff : (z - e).im ≥ R₀ := by
        rw [Complex.sub_im]; linarith [hz.2.1]
      have h_norm_ge : |((z - e).im)| ≤ ‖z - e‖ := Complex.abs_im_le_norm _
      have h_abs : |((z - e).im)| ≥ R₀ := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (z - e).im)]; linarith
      linarith
  have h_C_open_sub :
      (Set.Ioo (e.re - R₀) (e.re + R₀) ×ℂ Set.Ioo (e.im + R₀) d) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Ioo] at hz ⊢
        exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
      · rw [Set.mem_Ioo] at hz ⊢
        exact ⟨by linarith [hz.2.1], hz.2.2⟩
    · intro h_ball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_ball
      rw [Set.mem_Ioo] at hz
      have h_im_diff : (z - e).im > R₀ := by
        rw [Complex.sub_im]; linarith [hz.2.1]
      have h_norm_ge : |((z - e).im)| ≤ ‖z - e‖ := Complex.abs_im_le_norm _
      have h_abs : |((z - e).im)| > R₀ := by
        rw [abs_of_pos (by linarith : (0:ℝ) < (z - e).im)]; linarith
      linarith
  -- Subset inclusions for lunes D, E (in half-annulus closed and open regions).
  have h_D_closed_sub :
      ((Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z ⟨hz_rect, hz_not_ball⟩
    refine ⟨?_, hz_not_ball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  have h_D_open_sub :
      ((Set.Ioo (e.re - R₀) e.re ×ℂ Set.Ioo e.im (e.im + R₀)) \ Metric.closedBall e R₀) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_rect, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  -- Subset target for the TOP-LEFT lune CG: the half-annulus
  -- Hd domain `(Ioo a b × Ioo e.im d) \ closedBall` restricts (via mono)
  -- to `(Ioo a e.re × Ioo e.im d) \ closedBall`, which is the star-shaped
  -- open set used in the lune CG proof (star center at `(e.re - R₀, e.im + R₀)`).
  have h_D_lune_Hd_sub :
      (Set.Ioo a e.re ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_box, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨hz_box.1.1, by linarith [hz_box.1.2]⟩
  have h_E_closed_sub :
      ((Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \ Metric.ball e R₀) ⊆
        (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ := by
    intro z ⟨hz_rect, hz_not_ball⟩
    refine ⟨?_, hz_not_ball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Icc] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  have h_E_open_sub :
      ((Set.Ioo e.re (e.re + R₀) ×ℂ Set.Ioo e.im (e.im + R₀)) \ Metric.closedBall e R₀) ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_rect, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_rect ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨by linarith [hz_rect.1.1], by linarith [hz_rect.1.2]⟩
    · rw [Set.mem_Ioo] at hz_rect ⊢
      exact ⟨hz_rect.2.1, by linarith [hz_rect.2.2]⟩
  -- Subset target for the TOP-RIGHT lune CG: shrink left bound
  -- `a` up to `e.re`, giving `(Ioo e.re b × Ioo e.im d) \ closedBall`, the
  -- star-shaped open set used in the right lune's CG proof (star center at
  -- `(e.re + R₀, e.im + R₀)`).
  have h_E_lune_Hd_sub :
      (Set.Ioo e.re b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ ⊆
        (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro z ⟨hz_box, hz_not_cball⟩
    refine ⟨?_, hz_not_cball⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨by linarith [hz_box.1.1], hz_box.1.2⟩
  -- Step 2: apply rect CG to A.
  -- Rect endpoints: z = a + e.im·I, w = (e.re-R₀) + d·I.
  have hA_z_re : (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_z_im : (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im = e.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_w_re : ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = e.re - R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_w_im : ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hA_Hc : ContinuousOn f
      (Set.uIcc (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im) := by
    rw [hA_z_re, hA_z_im, hA_w_re, hA_w_im,
      Set.uIcc_of_le h_a_lt.le, Set.uIcc_of_le h_e_im_d.le]
    exact Hc.mono h_A_closed_sub
  have hA_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re)
       (max (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)
       (max (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)) := by
    rw [hA_z_re, hA_z_im, hA_w_re, hA_w_im,
      min_eq_left h_a_lt.le, max_eq_right h_a_lt.le,
      min_eq_left h_e_im_d.le, max_eq_right h_e_im_d.le]
    exact Hd_orig.mono h_A_open_sub
  have hA := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (((a : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I)
    ((((e.re - R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I) hA_Hc hA_Hd
  rw [hA_z_re, hA_z_im, hA_w_re, hA_w_im] at hA
  simp only [smul_eq_mul] at hA
  -- Step 3: apply rect CG to B.
  have hB_z_re : ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re = e.re + R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_z_im : ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im = e.im := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_w_re : (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = b := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_w_im : (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hB_Hc : ContinuousOn f
      (Set.uIcc ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im) := by
    rw [hB_z_re, hB_z_im, hB_w_re, hB_w_im,
      Set.uIcc_of_le h_lt_b.le, Set.uIcc_of_le h_e_im_d.le]
    exact Hc.mono h_B_closed_sub
  have hB_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re)
       (max ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)
       (max ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)) := by
    rw [hB_z_re, hB_z_im, hB_w_re, hB_w_im,
      min_eq_left h_lt_b.le, max_eq_right h_lt_b.le,
      min_eq_left h_e_im_d.le, max_eq_right h_e_im_d.le]
    exact Hd_orig.mono h_B_open_sub
  have hB := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ((((e.re + R₀) : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I)
    (((b : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I) hB_Hc hB_Hd
  rw [hB_z_re, hB_z_im, hB_w_re, hB_w_im] at hB
  simp only [smul_eq_mul] at hB
  -- Step 4: apply rect CG to C.
  have hC_z_re : ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
      = e.re - R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hC_z_im : ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
      = e.im + R₀ := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hC_w_re : ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re = e.re + R₀ := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hC_w_im : ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_eRm_le_eRp : e.re - R₀ ≤ e.re + R₀ := by linarith
  have hC_Hc : ContinuousOn f
      (Set.uIcc ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im) := by
    rw [hC_z_re, hC_z_im, hC_w_re, hC_w_im,
      Set.uIcc_of_le h_eRm_le_eRp, Set.uIcc_of_le h_e_im_R0_lt_d.le]
    exact Hc.mono h_C_closed_sub
  have hC_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re)
       (max ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).re
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)
       (max ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I).im
        ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im)) := by
    rw [hC_z_re, hC_z_im, hC_w_re, hC_w_im,
      min_eq_left h_eRm_le_eRp, max_eq_right h_eRm_le_eRp,
      min_eq_left h_e_im_R0_lt_d.le, max_eq_right h_e_im_R0_lt_d.le]
    exact Hd_orig.mono h_C_open_sub
  have hC := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f ((((e.re - R₀) : ℝ) : ℂ) + (((e.im + R₀) : ℝ) : ℂ) * Complex.I)
    ((((e.re + R₀) : ℝ) : ℂ) + ((d : ℝ) : ℂ) * Complex.I) hC_Hc hC_Hd
  rw [hC_z_re, hC_z_im, hC_w_re, hC_w_im] at hC
  simp only [smul_eq_mul] at hC
  -- Step 5: apply lune CG to D, E.
  -- Lune CG hypotheses: each lune CG takes a star-shaped open box
  -- `(Ioo a e.re × Ioo e.im d)` or `(Ioo e.re b × Ioo e.im d)` minus a
  -- slightly shrunken closed ball `closedBall e R₀'` (strengthened form);
  -- this is built from `Hd'` (mono'd to the lune-side box) and the
  -- enlarging existential witness `R₀'`.
  have hD := integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ a d h_a_lt h_e_im_R0_lt_d
    (Hc.mono h_D_closed_sub)
    ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'.mono (by
      rintro z ⟨hz_box, hz_not_cball⟩
      refine ⟨?_, hz_not_cball⟩
      rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, hz_box.2⟩
      rw [Set.mem_Ioo] at hz_box ⊢
      exact ⟨hz_box.1.1, by linarith [hz_box.1.2]⟩)⟩
  have hE := integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ b d h_lt_b h_e_im_R0_lt_d
    (Hc.mono h_E_closed_sub)
    ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'.mono (by
      rintro z ⟨hz_box, hz_not_cball⟩
      refine ⟨?_, hz_not_cball⟩
      rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, hz_box.2⟩
      rw [Set.mem_Ioo] at hz_box ⊢
      exact ⟨by linarith [hz_box.1.1], hz_box.1.2⟩)⟩
  -- Step 6: continuity on each boundary edge for interval combination.
  -- Continuity on top edge `y = d`.
  have h_top_cont : ContinuousOn (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      (Set.Icc a b) := by
    have h_inner_cont : Continuous (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I) := by fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((x : ℂ) + (d : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((x : ℂ) + (d : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact hx
      · change ((x : ℂ) + (d : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((x : ℂ) + (d : ℂ) * Complex.I).im = d := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact Set.right_mem_Icc.mpr h_e_im_d.le
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have him : ((x : ℂ) + (d : ℂ) * Complex.I - e).im = d - e.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((x : ℂ) + (d : ℂ) * Complex.I - e).im| ≤
          ‖((x : ℂ) + (d : ℂ) * Complex.I) - e‖ := Complex.abs_im_le_norm _
      rw [him, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_norm_ge
      linarith
  have h_top_int_a_eR : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re - R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_a_lt.le]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_top_int_eRm_eRp : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume (e.re - R₀) (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_eRm_le_eRp]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc <;> linarith
  have h_top_int_eRp_b : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume (e.re + R₀) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_lt_b.le]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_top_combine_left :
      (∫ x in a..(e.re - R₀), f ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∫ x in a..(e.re + R₀), f ((x : ℂ) + (d : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_top_int_a_eR h_top_int_eRm_eRp
  have h_top_int_a_eRp : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : a ≤ e.re + R₀)]
    apply h_top_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_top_combine_full :
      (∫ x in a..(e.re + R₀), f ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_top_int_a_eRp h_top_int_eRp_b
  -- Continuity on left edge `x = e.re - R₀`.
  have h_left_lune_cont : ContinuousOn
      (fun y : ℝ => f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc e.im d) := by
    have h_inner_cont : Continuous (fun y : ℝ => (e.re - R₀ : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).re = e.re - R₀ := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re]
        rw [this]; exact ⟨by linarith, by linarith⟩
      · change ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact hy
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have hre : ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I - e).re = -R₀ := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I - e).re| ≤
          ‖((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I) - e‖ := Complex.abs_re_le_norm _
      rw [hre, abs_of_neg (by linarith : -R₀ < 0)] at h_norm_ge
      linarith
  have h_left_int_low : IntervalIntegrable
      (fun y : ℝ => f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im (e.im + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.im ≤ e.im + R₀)]
    apply h_left_lune_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_left_int_high : IntervalIntegrable
      (fun y : ℝ => f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (e.im + R₀) d := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_e_im_R0_lt_d.le]
    apply h_left_lune_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_left_combine :
      (∫ y in e.im..(e.im + R₀), f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in (e.im + R₀)..d, f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in e.im..d, f ((e.re - R₀ : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_left_int_low h_left_int_high
  -- Continuity on right edge `x = e.re + R₀`.
  have h_right_lune_cont : ContinuousOn
      (fun y : ℝ => f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc e.im d) := by
    have h_inner_cont : Continuous (fun y : ℝ => (e.re + R₀ : ℂ) + (y : ℂ) * Complex.I) := by
      fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).re = e.re + R₀ := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact ⟨by linarith, by linarith⟩
      · change ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact hy
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have hre : ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I - e).re = R₀ := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I - e).re| ≤
          ‖((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I) - e‖ := Complex.abs_re_le_norm _
      rw [hre, abs_of_pos hR₀] at h_norm_ge
      linarith
  have h_right_int_low : IntervalIntegrable
      (fun y : ℝ => f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im (e.im + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.im ≤ e.im + R₀)]
    apply h_right_lune_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_right_int_high : IntervalIntegrable
      (fun y : ℝ => f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume (e.im + R₀) d := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_e_im_R0_lt_d.le]
    apply h_right_lune_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_right_combine :
      (∫ y in e.im..(e.im + R₀), f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in (e.im + R₀)..d, f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in e.im..d, f ((e.re + R₀ : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_right_int_low h_right_int_high
  -- Continuity on arc (upper semicircle, θ ∈ [0, π]).
  have h_arc_cont : ContinuousOn
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (Set.Icc (0:ℝ) Real.pi) := by
    have h_cm : Continuous (_root_.circleMap e R₀) := continuous_circleMap _ _
    have h_factor_cont : ContinuousOn (fun θ : ℝ =>
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (0:ℝ) Real.pi) := Continuous.continuousOn (by fun_prop)
    refine ContinuousOn.mul ?_ h_factor_cont
    -- Show f ∘ circleMap is ContinuousOn [0, π]: each point maps into the closed half-annulus.
    apply Hc.comp h_cm.continuousOn
    intro θ hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show (_root_.circleMap e R₀ θ).re ∈ Set.Icc a b
        have h_re : (_root_.circleMap e R₀ θ).re = e.re + R₀ * Real.cos θ := by
          simp [_root_.circleMap]
        rw [h_re]
        refine ⟨?_, ?_⟩
        · nlinarith [Real.neg_one_le_cos θ]
        · nlinarith [Real.cos_le_one θ]
      · show (_root_.circleMap e R₀ θ).im ∈ Set.Icc e.im d
        have h_im : (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
          simp [_root_.circleMap]
        rw [h_im]
        have h_sin_nn : Real.sin θ ≥ 0 := Real.sin_nonneg_of_mem_Icc
          ⟨hθ.1, hθ.2⟩
        refine ⟨?_, ?_⟩
        · nlinarith [h_sin_nn]
        · nlinarith [Real.sin_le_one θ]
    · intro h_ball
      rw [Metric.mem_ball] at h_ball
      have h_sphere : _root_.circleMap e R₀ θ ∈ Metric.sphere e R₀ :=
        _root_.circleMap_mem_sphere e hR₀.le θ
      rw [Metric.mem_sphere] at h_sphere
      linarith
  have h_arc_int_0_half : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)]
    apply h_arc_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith [Real.pi_pos]
  have h_arc_int_half_pi : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      MeasureTheory.volume (Real.pi / 2) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)]
    apply h_arc_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith [Real.pi_pos]
  have h_arc_combine :
      (∫ θ in (0:ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) +
      (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      ∫ θ in (0:ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    intervalIntegral.integral_add_adjacent_intervals h_arc_int_0_half h_arc_int_half_pi
  -- Continuity on middle bottom edge `y = e.im + R₀` for adjacent interval combination.
  have h_middle_cont : ContinuousOn
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I))
      (Set.Icc (e.re - R₀) (e.re + R₀)) := by
    have h_inner_cont : Continuous (fun x : ℝ => (x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I) := by
      fun_prop
    apply Hc.comp h_inner_cont.continuousOn
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · change ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).re ∈ Set.Icc a b
        have : ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · change ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).im ∈ Set.Icc e.im d
        have : ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I).im = e.im + R₀ := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [this]; exact ⟨by linarith, by linarith⟩
    · intro h_in_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_in_ball
      have him : ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I - e).im = R₀ := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_norm_ge : |((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I - e).im| ≤
          ‖((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I) - e‖ := Complex.abs_im_le_norm _
      rw [him, abs_of_pos hR₀] at h_norm_ge
      linarith
  have h_middle_int_left : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I))
      MeasureTheory.volume (e.re - R₀) e.re := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.re - R₀ ≤ e.re)]
    apply h_middle_cont.mono
    apply Set.Icc_subset_Icc le_rfl
    linarith
  have h_middle_int_right : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I))
      MeasureTheory.volume e.re (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : e.re ≤ e.re + R₀)]
    apply h_middle_cont.mono
    apply Set.Icc_subset_Icc _ le_rfl
    linarith
  have h_middle_combine :
      (∫ x in (e.re - R₀)..e.re, f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) +
      (∫ x in e.re..(e.re + R₀), f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I)) =
      ∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + ((e.im + R₀) : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_middle_int_left h_middle_int_right
  -- Step 7: combine A + B + C + D + E + interval combinations. Coercions
  -- `↑(e.re - R₀)` vs `↑e.re - ↑R₀` need to be normalized via `push_cast`.
  linear_combination
    (norm := (push_cast; ring))
    hA + hB + hC + hD + hE + h_top_combine_left + h_top_combine_full +
    h_middle_combine + Complex.I * h_left_combine - Complex.I * h_right_combine + h_arc_combine

/-- **Cauchy-Goursat for the closed upper half-disk
(rectangular-enlargement hypothesis form).** For `f` continuous
on the closed small rectangle `[e.re − R₀, e.re + R₀] × [e.im, e.im + R₀]`
(which contains the closed upper half-disk centered at `e` with radius
`R₀`) and complex-differentiable on a slight rectangular enlargement
`(e.re − R₀ − ε, e.re + R₀ + ε) × (e.im, e.im + R₀ + ε)`, the contour
integral around the boundary of the upper half-disk (bottom diameter
left-to-right + upper semicircle from right to left via top) equals
zero.

This is the easier hypothesis form usable when the integrand is
analytic on a full rectangular neighborhood of the closed small rect
(e.g., for `f` itself in the main F_Y argument-principle theorem, where
the modular function is analytic on the upper half-plane). The proof
combines the two upper lune CGs (`topLeftLune`, `topRightLune`) and
the small rectangle CG via algebraic linear combination: the rect CG
bottom term, the rect CG top + lune top terms, the rect CG vertical
edge terms, and the lune arc terms together collapse into the upper
half-disk identity. -/
theorem integral_boundary_upperHalfDisk_eq_zero_of_continuousOn_of_differentiableOn
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (Hc : ContinuousOn f
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)))
    (Hd : ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ f
      (Set.Ioo (e.re - R₀ - ε) (e.re + R₀ + ε) ×ℂ
       Set.Ioo e.im (e.im + R₀ + ε))) :
    (∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    (∫ θ in (0 : ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  obtain ⟨ε, hε_pos, Hd_box⟩ := Hd
  -- Lune subset for continuity.
  have h_LL_sub : (Set.Icc (e.re - R₀) e.re ×ℂ Set.Icc e.im (e.im + R₀)) \
      Metric.ball e R₀ ⊆
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Icc] at hz_box ⊢
    exact ⟨hz_box.1.1, by linarith [hz_box.1.2, hR₀]⟩
  have h_RL_sub : (Set.Icc e.re (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) \
      Metric.ball e R₀ ⊆
      (Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Icc] at hz_box ⊢
    exact ⟨by linarith [hz_box.1.1, hR₀], hz_box.1.2⟩
  -- Existential `Hd` for each lune (with R₀' = R₀/2).
  set R₀' := R₀ / 2 with hR₀'_def
  have hR₀'_pos : 0 < R₀' := by simp [hR₀'_def]; linarith
  have hR₀'_lt : R₀' < R₀ := by simp [hR₀'_def]; linarith
  have h_LL_Hd_sub :
      (Set.Ioo (e.re - R₀ - ε) e.re ×ℂ Set.Ioo e.im (e.im + R₀ + ε)) \
        Metric.closedBall e R₀' ⊆
        (Set.Ioo (e.re - R₀ - ε) (e.re + R₀ + ε) ×ℂ
          Set.Ioo e.im (e.im + R₀ + ε)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨hz_box.1.1, by linarith [hz_box.1.2, hR₀, hε_pos]⟩
  have h_RL_Hd_sub :
      (Set.Ioo e.re (e.re + R₀ + ε) ×ℂ Set.Ioo e.im (e.im + R₀ + ε)) \
        Metric.closedBall e R₀' ⊆
        (Set.Ioo (e.re - R₀ - ε) (e.re + R₀ + ε) ×ℂ
          Set.Ioo e.im (e.im + R₀ + ε)) := by
    rintro z ⟨hz_box, _⟩
    rw [Complex.mem_reProdIm] at hz_box ⊢
    refine ⟨?_, hz_box.2⟩
    rw [Set.mem_Ioo] at hz_box ⊢
    exact ⟨by linarith [hz_box.1.1, hR₀, hε_pos], hz_box.1.2⟩
  -- Apply topLeftLune CG.
  have h_LL := integral_boundary_topLeftLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ (e.re - R₀ - ε) (e.im + R₀ + ε) (by linarith) (by linarith)
    (Hc.mono h_LL_sub) ⟨R₀', hR₀'_pos, hR₀'_lt, Hd_box.mono h_LL_Hd_sub⟩
  -- Apply topRightLune CG.
  have h_RL := integral_boundary_topRightLune_eq_zero_of_continuousOn_of_differentiableOn
    f e R₀ hR₀ (e.re + R₀ + ε) (e.im + R₀ + ε) (by linarith) (by linarith)
    (Hc.mono h_RL_sub) ⟨R₀', hR₀'_pos, hR₀'_lt, Hd_box.mono h_RL_Hd_sub⟩
  -- Apply small rect CG.
  have h_re_le : e.re - R₀ ≤ e.re + R₀ := by linarith
  have h_im_le : e.im ≤ e.im + R₀ := by linarith
  have h_rect_Hc : ContinuousOn f
      (Set.uIcc (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
        (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).re ×ℂ
       Set.uIcc (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
        (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).im) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.I_im, mul_one, sub_self, Complex.mul_im, zero_add]
    rw [Set.uIcc_of_le h_re_le, Set.uIcc_of_le h_im_le]
    exact Hc
  have h_rect_Hd : DifferentiableOn ℂ f
      (Set.Ioo (min (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).re)
        (max (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).re
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).re) ×ℂ
       Set.Ioo (min (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).im)
        (max (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I).im
          (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I).im)) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero,
      Complex.I_im, mul_one, sub_self, Complex.mul_im, zero_add,
      min_eq_left h_re_le, max_eq_right h_re_le, min_eq_left h_im_le,
      max_eq_right h_im_le]
    apply Hd_box.mono
    rintro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.mem_Ioo] at hz ⊢
      exact ⟨by linarith [hz.1.1, hε_pos], by linarith [hz.1.2, hε_pos]⟩
    · rw [Set.mem_Ioo] at hz ⊢
      exact ⟨hz.2.1, by linarith [hz.2.2, hε_pos]⟩
  have h_rect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I)
    (((e.re + R₀ : ℝ) : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I) h_rect_Hc h_rect_Hd
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.I_im, mul_one, sub_self, Complex.mul_im, zero_add,
    smul_eq_mul] at h_rect
  -- Continuity of integrand pieces for interval additivity.
  have h_inner_top_cont : Continuous fun x : ℝ =>
      (x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I := by fun_prop
  have h_top_maps : ∀ x ∈ Set.Icc (e.re - R₀) (e.re + R₀),
      ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I) ∈
        Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀) := by
    intro x hx
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
        add_zero]
      exact hx
    · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, zero_add,
        add_zero]
      exact ⟨by linarith, le_refl _⟩
  have h_top_cont : ContinuousOn (fun x : ℝ =>
      f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I))
      (Set.Icc (e.re - R₀) (e.re + R₀)) :=
    Hc.comp h_inner_top_cont.continuousOn h_top_maps
  have h_top_int_left : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (e.re - R₀) e.re := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    apply h_top_cont.mono
    intro x hx; exact ⟨hx.1, by linarith [hx.2, hR₀]⟩
  have h_top_int_right : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume e.re (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    apply h_top_cont.mono
    intro x hx; exact ⟨by linarith [hx.1, hR₀], hx.2⟩
  have h_top_split :
      (∫ x in (e.re - R₀)..(e.re + R₀),
        f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I)) =
      (∫ x in (e.re - R₀)..e.re,
        f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I)) +
      (∫ x in e.re..(e.re + R₀),
        f ((x : ℂ) + ((e.im + R₀ : ℝ) : ℂ) * Complex.I)) :=
    (intervalIntegral.integral_add_adjacent_intervals h_top_int_left h_top_int_right).symm
  -- Continuity for arc.
  have h_circleMap_maps : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      _root_.circleMap e R₀ θ ∈
        Set.Icc (e.re - R₀) (e.re + R₀) ×ℂ Set.Icc e.im (e.im + R₀) := by
    intro θ hθ
    have h_pi_pos := Real.pi_pos
    have h_cos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have h_cos_ge : Real.cos θ ≥ -1 := Real.neg_one_le_cos θ
    have h_sin_nn : Real.sin θ ≥ 0 :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have h_z_re : (_root_.circleMap e R₀ θ).re = e.re + R₀ * Real.cos θ := by
      rw [_root_.circleMap, Complex.exp_mul_I]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have h_z_im : (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
      rw [_root_.circleMap, Complex.exp_mul_I]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [h_z_re, Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have : R₀ * Real.cos θ ≥ R₀ * (-1) :=
          mul_le_mul_of_nonneg_left h_cos_ge hR₀.le
        linarith
      · have : R₀ * Real.cos θ ≤ R₀ * 1 :=
          mul_le_mul_of_nonneg_left h_cos_le hR₀.le
        linarith
    · rw [h_z_im, Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have : R₀ * Real.sin θ ≥ 0 := mul_nonneg hR₀.le h_sin_nn
        linarith
      · have : R₀ * Real.sin θ ≤ R₀ * 1 :=
          mul_le_mul_of_nonneg_left h_sin_le hR₀.le
        linarith
  have h_arc_cont : ContinuousOn (fun θ : ℝ =>
      f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      (Set.Icc (0 : ℝ) Real.pi) := by
    apply ContinuousOn.mul
    · exact Hc.comp (continuous_circleMap _ _).continuousOn h_circleMap_maps
    · apply Continuous.continuousOn
      exact ((continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)))
  have h_pi_div_two_le_pi : Real.pi / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have h_pi_div_two_nn : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h_arc_int_left : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume (0 : ℝ) (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_div_two_nn]
    exact h_arc_cont.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have h_arc_int_right : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume (Real.pi / 2) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_div_two_le_pi]
    exact h_arc_cont.mono (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have h_arc_split :
      (∫ θ in (0 : ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) +
      (∫ θ in (Real.pi / 2)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) :=
    (intervalIntegral.integral_add_adjacent_intervals h_arc_int_left h_arc_int_right).symm
  -- Linear-combination assembly.
  linear_combination (norm := (push_cast; ring))
    -h_LL - h_RL + h_rect + h_top_split + h_arc_split

/-- **Cauchy-Goursat for the closed upper half-disk (AnalyticOnNhd
hypothesis form).** For `f` analytic on an open neighborhood of every
point of the closed upper half-disk `closedBall e R₀ ∩ {z : e.im ≤ z.im}`,
the contour integral around the boundary (bottom diameter
left-to-right + upper semicircle from right to left via top) equals
zero.

This is the cleanest hypothesis form, accommodating integrands with
singularities in the rectangular corners outside the half-disk (e.g.,
`1/(z − w)` where `w` is in the upper-corner region inside the closed
small rect but outside the closed disk). Used in the
`rectMinusUpperHalfDiskWindingNumber_inside_eq_one` derivation.

**Proof strategy.** Use compactness of the closed upper half-disk
together with `AnalyticAt.eventually_analyticAt` to extract a uniform
δ > 0 such that the open convex neighborhood
`U := Metric.ball e (R₀ + δ) ∩ {z : z.im > e.im − δ}` is contained in
the analyticity domain. `U` is open (intersection of two open sets)
and convex (intersection of two convex sets); it contains the closed
upper half-disk. Apply `hasDerivAt_starPrimitive` with star center
`p := e + (R₀/2) · I ∈ U` (interior) to get a primitive
`F := starPrimitive p f` with `HasDerivAt F (f z) z` for every `z ∈ U`.
The boundary path of the closed upper half-disk lies in `U` (since
`closedBall ∩ upper half-plane ⊆ U`); FTC gives
`∫_(bottom diameter) f = F((e.re+R₀, e.im)) − F((e.re−R₀, e.im))` and
`∫_(upper semicircle) f = F((e.re−R₀, e.im)) − F((e.re+R₀, e.im))`,
which sum to zero. -/
theorem integral_boundary_upperHalfDisk_eq_zero_of_analyticOnNhd
    (f : ℂ → ℂ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (Hf : AnalyticOnNhd ℂ f
      (Metric.closedBall e R₀ ∩ {z : ℂ | e.im ≤ z.im})) :
    (∫ x in (e.re - R₀)..(e.re + R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    (∫ θ in (0 : ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- The closed upper half-disk S is compact.
  set S : Set ℂ := Metric.closedBall e R₀ ∩ {z : ℂ | e.im ≤ z.im} with hS_def
  have hS_compact : IsCompact S :=
    (isCompact_closedBall e R₀).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  -- The analyticity domain V := {z : AnalyticAt ℂ f z} is open and contains S.
  set V : Set ℂ := {z : ℂ | AnalyticAt ℂ f z} with hV_def
  have hV_open : IsOpen V := by
    rw [isOpen_iff_eventually]
    intro z hz
    exact hz.eventually_analyticAt
  have hS_sub_V : S ⊆ V := fun z hz => Hf z hz
  -- Extract uniform δ > 0 with Metric.thickening δ S ⊆ V.
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    hS_compact.exists_thickening_subset_open hV_open hS_sub_V
  -- The convex open thickening U := ball e (R₀ + δ/2) ∩ {z : e.im - δ/2 < z.im}.
  set U : Set ℂ :=
    Metric.ball e (R₀ + δ/2) ∩ {z : ℂ | e.im - δ/2 < z.im} with hU_def
  have hU_open : IsOpen U :=
    Metric.isOpen_ball.inter (isOpen_Ioi.preimage Complex.continuous_im)
  have h_im_linear : IsLinearMap ℝ (fun z : ℂ => z.im) :=
    ⟨fun _ _ => Complex.add_im _ _, fun r z => Complex.smul_im r z⟩
  have hU_convex : Convex ℝ U :=
    (convex_ball _ _).inter (convex_halfSpace_gt h_im_linear (e.im - δ/2))
  -- Show U ⊆ Metric.thickening δ S via projection + radial projection.
  have hU_sub_thickening : U ⊆ Metric.thickening δ S := by
    intro z hz
    obtain ⟨h_ball, h_half⟩ := hz
    rw [Metric.mem_ball, Complex.dist_eq] at h_ball
    change e.im - δ/2 < z.im at h_half
    rw [Metric.mem_thickening_iff]
    by_cases h_above : e.im ≤ z.im
    · -- z.im ≥ e.im: direct or radial projection.
      by_cases h_in_disk : ‖z - e‖ ≤ R₀
      · refine ⟨z, ⟨?_, h_above⟩, by rw [dist_self]; exact hδ_pos⟩
        rw [Metric.mem_closedBall, Complex.dist_eq]; exact h_in_disk
      · push Not at h_in_disk
        have h_norm_pos : 0 < ‖z - e‖ := by linarith
        have h_norm_ne : ‖z - e‖ ≠ 0 := ne_of_gt h_norm_pos
        set s : ℂ := e + ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) with hs_def
        have hs_sub : s - e = ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
          rw [hs_def]; ring
        have h_pos_div : (0 : ℝ) ≤ R₀ / ‖z - e‖ :=
          div_nonneg hR₀.le (norm_nonneg _)
        have hs_norm : ‖s - e‖ = R₀ := by
          rw [hs_sub, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg h_pos_div, div_mul_cancel₀ _ h_norm_ne]
        have hs_im : e.im ≤ s.im := by
          have h_diff_im : s.im = e.im + (R₀ / ‖z - e‖) * (z.im - e.im) := by
            rw [hs_def]
            simp [Complex.add_im, Complex.mul_im, Complex.sub_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_diff_im]
          have h_nn : 0 ≤ R₀ / ‖z - e‖ * (z.im - e.im) :=
            mul_nonneg h_pos_div (by linarith)
          linarith
        have hs_in_S : s ∈ S := by
          refine ⟨?_, hs_im⟩
          rw [Metric.mem_closedBall, Complex.dist_eq, hs_norm]
        refine ⟨s, hs_in_S, ?_⟩
        rw [Complex.dist_eq]
        have h_z_sub : z - s = ((1 - R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
          rw [hs_def]; push_cast; field_simp; ring
        have h_one_minus_pos : (0 : ℝ) ≤ 1 - R₀ / ‖z - e‖ := by
          rw [sub_nonneg, div_le_one h_norm_pos]; linarith
        rw [h_z_sub, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg h_one_minus_pos]
        have h_mul_eq : (1 - R₀ / ‖z - e‖) * ‖z - e‖ = ‖z - e‖ - R₀ := by
          field_simp
        linarith [h_mul_eq]
    · -- z.im < e.im: project to z' on bottom diameter, then possibly radially.
      push Not at h_above
      set z' : ℂ := (z.re : ℂ) + (e.im : ℂ) * Complex.I with hz'_def
      have hz'_re : z'.re = z.re := by
        simp [hz'_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have hz'_im : z'.im = e.im := by
        simp [hz'_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      have h_dist_z_z' : dist z z' = e.im - z.im := by
        rw [Complex.dist_eq]
        have h_diff : z - z' = ((z.im - e.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [hz'_def, Complex.sub_re, Complex.add_re, Complex.mul_re,
              Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im]
          · simp [hz'_def, Complex.sub_im, Complex.add_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re,
              Complex.ofReal_im]
        rw [h_diff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_neg (by linarith : z.im - e.im < 0)]
        linarith
      have hz'_norm_le_sq : ‖z' - e‖^2 ≤ ‖z - e‖^2 := by
        have h_z'_sq : ‖z' - e‖^2 = (z.re - e.re)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
            Complex.sub_re, Complex.sub_im, hz'_re, hz'_im]; ring
        have h_z_sq : ‖z - e‖^2 = (z.re - e.re)^2 + (z.im - e.im)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
            Complex.sub_re, Complex.sub_im]; ring
        nlinarith [sq_nonneg (z.im - e.im), h_z_sq, h_z'_sq]
      have hz'_norm_le : ‖z' - e‖ ≤ ‖z - e‖ := by
        have h_z'_nn : 0 ≤ ‖z' - e‖ := norm_nonneg _
        have h_z_nn : 0 ≤ ‖z - e‖ := norm_nonneg _
        nlinarith [hz'_norm_le_sq, sq_nonneg (‖z - e‖ - ‖z' - e‖),
          sq_nonneg (‖z - e‖ + ‖z' - e‖)]
      by_cases h_z'_in_disk : ‖z' - e‖ ≤ R₀
      · have hz'_in_S : z' ∈ S := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, Complex.dist_eq]; exact h_z'_in_disk
          · change e.im ≤ z'.im; rw [hz'_im]
        refine ⟨z', hz'_in_S, ?_⟩
        rw [h_dist_z_z']; linarith
      · push Not at h_z'_in_disk
        have h_z'_norm_pos : 0 < ‖z' - e‖ := by linarith
        have h_z'_norm_ne : ‖z' - e‖ ≠ 0 := ne_of_gt h_z'_norm_pos
        set s : ℂ := e + ((R₀ / ‖z' - e‖ : ℝ) : ℂ) * (z' - e) with hs_def
        have hs_sub : s - e = ((R₀ / ‖z' - e‖ : ℝ) : ℂ) * (z' - e) := by
          rw [hs_def]; ring
        have h_pos_div : (0 : ℝ) ≤ R₀ / ‖z' - e‖ :=
          div_nonneg hR₀.le (norm_nonneg _)
        have hs_norm : ‖s - e‖ = R₀ := by
          rw [hs_sub, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg h_pos_div, div_mul_cancel₀ _ h_z'_norm_ne]
        have hs_im : e.im ≤ s.im := by
          have h_diff_im : s.im = e.im + (R₀ / ‖z' - e‖) * (z'.im - e.im) := by
            rw [hs_def]
            simp [Complex.add_im, Complex.mul_im, Complex.sub_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_diff_im, hz'_im]
          simp
        have hs_in_S : s ∈ S := by
          refine ⟨?_, hs_im⟩
          rw [Metric.mem_closedBall, Complex.dist_eq, hs_norm]
        refine ⟨s, hs_in_S, ?_⟩
        have h_dist_z'_s : dist z' s = ‖z' - e‖ - R₀ := by
          rw [Complex.dist_eq]
          have h_z'_s_sub :
              z' - s = ((1 - R₀ / ‖z' - e‖ : ℝ) : ℂ) * (z' - e) := by
            rw [hs_def]; push_cast; field_simp; ring
          have h_one_minus_pos : (0 : ℝ) ≤ 1 - R₀ / ‖z' - e‖ := by
            rw [sub_nonneg, div_le_one h_z'_norm_pos]; linarith
          rw [h_z'_s_sub, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg h_one_minus_pos]
          have h_mul_eq : (1 - R₀ / ‖z' - e‖) * ‖z' - e‖ = ‖z' - e‖ - R₀ := by
            field_simp
          exact h_mul_eq
        have h_dist_z'_s_lt : dist z' s < δ/2 := by
          rw [h_dist_z'_s]; linarith
        have h_dist_z_z'_lt : dist z z' < δ/2 := by rw [h_dist_z_z']; linarith
        calc dist z s
            ≤ dist z z' + dist z' s := dist_triangle _ _ _
          _ < δ/2 + δ/2 := by linarith
          _ = δ := by ring
  -- U ⊆ V.
  have hU_sub_V : U ⊆ V := fun z hz => hδ_sub (hU_sub_thickening hz)
  -- f differentiable on U.
  have hf_diff_U : DifferentiableOn ℂ f U := fun z hz =>
    (hU_sub_V hz).differentiableAt.differentiableWithinAt
  -- Star center p ∈ U.
  set p : ℂ := e + ((R₀ / 2 : ℝ) : ℂ) * Complex.I with hp_def
  have hp_in_U : p ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h_diff : p - e = ((R₀ / 2 : ℝ) : ℂ) * Complex.I := by
        rw [hp_def]; ring
      rw [h_diff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      linarith
    · change e.im - δ/2 < p.im
      have h_p_im : p.im = e.im + R₀/2 := by
        rw [hp_def]
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [h_p_im]; linarith
  have hU_starConvex : StarConvex ℝ p U := hU_convex.starConvex hp_in_U
  -- The primitive F := starPrimitive p f.
  set F : ℂ → ℂ := Complex.starPrimitive p f with hF_def
  have hF_derivAt : ∀ z ∈ U, HasDerivAt F (f z) z := fun z hz =>
    Complex.hasDerivAt_starPrimitive hU_open hU_starConvex hf_diff_U hz
  -- Bottom-diameter path is in U.
  have h_bot_in_U : ∀ x : ℝ, x ∈ Set.Icc (e.re - R₀) (e.re + R₀) →
      ((x : ℂ) + (e.im : ℂ) * Complex.I) ∈ U := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h_norm_sq :
          ‖((x : ℂ) + (e.im : ℂ) * Complex.I) - e‖^2 = (x - e.re)^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      have h_x_sq_bound : (x - e.re)^2 ≤ R₀^2 := by
        rw [Set.mem_Icc] at hx; nlinarith [hx.1, hx.2]
      have h_nonneg : 0 ≤ ‖((x : ℂ) + (e.im : ℂ) * Complex.I) - e‖ :=
        norm_nonneg _
      nlinarith [h_norm_sq, h_x_sq_bound, hR₀, hδ_pos]
    · change e.im - δ/2 < ((x : ℂ) + (e.im : ℂ) * Complex.I).im
      have h_im_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).im = e.im := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [h_im_eq]; linarith
  -- Upper-semicircle path is in U.
  have h_arc_in_U : ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) Real.pi →
      _root_.circleMap e R₀ θ ∈ U := by
    intro θ hθ
    have h_arc_norm : ‖_root_.circleMap e R₀ θ - e‖ = R₀ := by
      rw [_root_.circleMap,
        show e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
          (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR₀.le,
        Complex.norm_exp_ofReal_mul_I]
      ring
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, h_arc_norm]; linarith
    · change e.im - δ/2 < (_root_.circleMap e R₀ θ).im
      have h_im_eq : (_root_.circleMap e R₀ θ).im = e.im + R₀ * Real.sin θ := by
        rw [_root_.circleMap, Complex.exp_mul_I]
        simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [h_im_eq]
      have h_sin_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
      have h_R_sin_nn : 0 ≤ R₀ * Real.sin θ := mul_nonneg hR₀.le h_sin_nn
      linarith
  -- HasDerivAt of bottom-diameter composition.
  have h_bot_inner_deriv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I) 1 x := fun x =>
    (Complex.ofRealCLM.hasDerivAt).add_const _
  have h_G_bot_deriv : ∀ x ∈ Set.Ioo (e.re - R₀) (e.re + R₀),
      HasDerivAt (fun x : ℝ => F ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (f ((x : ℂ) + (e.im : ℂ) * Complex.I)) x := by
    intro x hx
    have hx_Icc : x ∈ Set.Icc (e.re - R₀) (e.re + R₀) := ⟨hx.1.le, hx.2.le⟩
    have h_z_in_U := h_bot_in_U x hx_Icc
    have h_F_at := hF_derivAt _ h_z_in_U
    have h_comp := h_F_at.comp x (h_bot_inner_deriv x)
    simpa using h_comp
  -- ContinuousOn F on U and f on U.
  have hF_cont_on : ContinuousOn F U := fun z hz =>
    (hF_derivAt z hz).continuousAt.continuousWithinAt
  have hf_cont_on : ContinuousOn f U := fun z hz =>
    (hU_sub_V hz).differentiableAt.continuousAt.continuousWithinAt
  have h_bot_inner_cont :
      Continuous (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I) := by fun_prop
  -- ContinuousOn of G_bot.
  have h_G_bot_cont :
      ContinuousOn (fun x : ℝ => F ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.Icc (e.re - R₀) (e.re + R₀)) :=
    hF_cont_on.comp h_bot_inner_cont.continuousOn h_bot_in_U
  -- Integrand continuity on the bottom diameter.
  have h_bot_integrand_cont :
      ContinuousOn (fun x : ℝ => f ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.Icc (e.re - R₀) (e.re + R₀)) :=
    hf_cont_on.comp h_bot_inner_cont.continuousOn h_bot_in_U
  have h_re_le : e.re - R₀ ≤ e.re + R₀ := by linarith
  have h_bot_integrable :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (e.im : ℂ) * Complex.I))
        MeasureTheory.volume (e.re - R₀) (e.re + R₀) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_re_le]
    exact h_bot_integrand_cont
  -- FTC on bottom diameter.
  have h_bot_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    h_re_le h_G_bot_cont h_G_bot_deriv h_bot_integrable
  -- HasDerivAt of arc composition.
  have h_arc_inner_deriv : ∀ θ : ℝ,
      HasDerivAt (_root_.circleMap e R₀)
        (_root_.circleMap 0 R₀ θ * Complex.I) θ := fun θ =>
    hasDerivAt_circleMap _ _ _
  have h_arc_deriv_simplify : ∀ θ : ℝ,
      _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    intro θ
    rw [_root_.circleMap,
      show ((θ : ℂ) * Complex.I) = Complex.I * (θ : ℂ) from mul_comm _ _]
    ring
  have h_G_arc_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt (fun θ : ℝ => F (_root_.circleMap e R₀ θ))
        (f (_root_.circleMap e R₀ θ) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) θ := by
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hθ.1.le, hθ.2.le⟩
    have h_z_in_U := h_arc_in_U θ hθ_Icc
    have h_F_at := hF_derivAt _ h_z_in_U
    have h_comp := h_F_at.comp θ (h_arc_inner_deriv θ)
    rw [h_arc_deriv_simplify] at h_comp
    exact h_comp
  -- ContinuousOn of G_arc.
  have h_G_arc_cont :
      ContinuousOn (fun θ : ℝ => F (_root_.circleMap e R₀ θ))
        (Set.Icc (0 : ℝ) Real.pi) := by
    intro θ hθ
    have h_z_in_U := h_arc_in_U θ hθ
    have h_F_cont_at : ContinuousAt F (_root_.circleMap e R₀ θ) :=
      (hF_derivAt _ h_z_in_U).continuousAt
    have h_circle_cont : Continuous (_root_.circleMap e R₀) :=
      continuous_circleMap _ _
    exact (h_F_cont_at.comp h_circle_cont.continuousAt).continuousWithinAt
  -- Integrand continuity on the arc.
  have h_arc_integrand_cont :
      ContinuousOn (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (Set.Icc (0 : ℝ) Real.pi) := by
    apply ContinuousOn.mul
    · intro θ hθ
      have h_z_in_U := h_arc_in_U θ hθ
      have h_f_cont_at : ContinuousAt f (_root_.circleMap e R₀ θ) :=
        (hU_sub_V h_z_in_U).differentiableAt.continuousAt
      exact (h_f_cont_at.comp
        (continuous_circleMap _ _).continuousAt).continuousWithinAt
    · apply Continuous.continuousOn
      fun_prop
  have h_pi_pos : 0 ≤ Real.pi := Real.pi_pos.le
  have h_arc_integrable :
      IntervalIntegrable (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        MeasureTheory.volume (0 : ℝ) Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h_pi_pos]
    exact h_arc_integrand_cont
  -- FTC on arc.
  have h_arc_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    h_pi_pos h_G_arc_cont h_G_arc_deriv h_arc_integrable
  -- Compute circleMap endpoints.
  have h_circle_pi : _root_.circleMap e R₀ Real.pi =
      ((e.re - R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I := by
    rw [_root_.circleMap, Complex.exp_mul_I]
    rw [show Complex.cos ((Real.pi : ℂ)) = -1 by
        rw [← Complex.ofReal_cos, Real.cos_pi]; push_cast; ring]
    rw [show Complex.sin ((Real.pi : ℂ)) = 0 by
        rw [← Complex.ofReal_sin, Real.sin_pi]; push_cast; ring]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    · simp [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_circle_0 : _root_.circleMap e R₀ 0 =
      ((e.re + R₀ : ℝ) : ℂ) + ((e.im : ℝ) : ℂ) * Complex.I := by
    rw [_root_.circleMap]
    have h_exp_0 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    rw [h_exp_0]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
  -- Combine.
  rw [h_bot_FTC, h_arc_FTC, h_circle_pi, h_circle_0]
  push_cast
  ring

/-- **F_Y winding number.** The winding number of the F_Y boundary
(rectangle `[a, b] × [e.im, d]` with the upper half-disk centered at
`e` with radius `R₀` removed) around an interior point `w` equals `1`.

The F_Y boundary integral of `(z − w)⁻¹` is `∮_∂rect − ∮_(bottom
diameter) − ∮_(upper semicircle)`. The rect integral equals `2πi` by
`rectangleWindingNumber_inside_eq_one`, and the bottom-diameter plus
upper-semicircle integrals together equal `0` by the upper half-disk
Cauchy-Goursat (since `w` is outside the closed upper half-disk).
Subtraction yields `2πi`, dividing by `2πi` gives `1`. -/
theorem rectMinusUpperHalfDiskWindingNumber_inside_eq_one
    (a b d : ℝ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hab : a < b) (_h_a_lt : a < e.re - R₀) (_h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d) {w : ℂ}
    (hw_in : w ∈ (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - w)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 1 := by
  obtain ⟨hw_box, hw_not_ball⟩ := hw_in
  rw [Complex.mem_reProdIm] at hw_box
  obtain ⟨hw_re_in, hw_im_in⟩ := hw_box
  rw [Set.mem_Ioo] at hw_re_in hw_im_in
  -- w outside closed ball: ‖w - e‖ > R₀.
  have hw_dist_gt : R₀ < ‖w - e‖ := by
    by_contra h
    push Not at h
    exact hw_not_ball (by rw [Metric.mem_closedBall, Complex.dist_eq]; exact h)
  -- e.im < d so we can chain im inequalities.
  have h_e_im_lt_d : e.im < d := by linarith
  -- Step 1: Apply rectangleWindingNumber on the full rectangle.
  have hw_re_pair : a < w.re ∧ w.re < b := hw_re_in
  have hw_im_pair : e.im < w.im ∧ w.im < d := hw_im_in
  have h_rect_wn :=
    rectangleWindingNumber_inside_eq_one a b e.im d hab h_e_im_lt_d hw_re_pair hw_im_pair
  -- 2πi ≠ 0.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- From h_rect_wn, get full rect integral = 2πi.
  have h_rect_eq :
      (∫ x in a..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) =
      2 * Real.pi * Complex.I := by
    have := h_rect_wn
    have hk : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ *
        ((∫ x in a..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
        Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
        Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹))) =
        (2 * Real.pi * Complex.I) * 1 := by rw [this]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at hk
    exact hk
  -- Step 2: AnalyticOnNhd of (·-w)⁻¹ on the upper half-disk.
  have h_analytic_inv : AnalyticOnNhd ℂ (fun z : ℂ => (z - w)⁻¹)
      (Metric.closedBall e R₀ ∩ {z : ℂ | e.im ≤ z.im}) := by
    intro z hz
    have hz_in_ball : z ∈ Metric.closedBall e R₀ := hz.1
    have h_dist_z : ‖z - e‖ ≤ R₀ := by
      rw [Metric.mem_closedBall, Complex.dist_eq] at hz_in_ball; exact hz_in_ball
    have h_ne : z - w ≠ 0 := by
      intro h_eq
      have hz_eq : z = w := by linear_combination h_eq
      rw [hz_eq] at h_dist_z
      linarith
    have h_id_an : AnalyticAt ℂ (fun ζ : ℂ => ζ - w) z := by
      exact (analyticAt_id (𝕜 := ℂ)).sub analyticAt_const
    exact h_id_an.inv h_ne
  -- Apply upper half-disk Cauchy-Goursat to (·-w)⁻¹.
  have h_uhd_cg :=
    integral_boundary_upperHalfDisk_eq_zero_of_analyticOnNhd
      (fun z : ℂ => (z - w)⁻¹) e R₀ hR₀ h_analytic_inv
  -- Step 3: Non-vanishing of (x + e.im·I - w) when w.im > e.im.
  have h_ne_bot : ∀ x : ℝ, ((x : ℂ) + (e.im : ℂ) * Complex.I - w) ≠ 0 := by
    intro x h_eq
    have h_im : ((x : ℂ) + (e.im : ℂ) * Complex.I - w).im = e.im - w.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
    have h_zero : e.im - w.im = 0 := by
      have := congrArg Complex.im h_eq; rw [h_im] at this; simpa using this
    linarith [hw_im_pair.1]
  -- Step 4: Continuity & interval integrability for (·-w)⁻¹ on the bottom diameter.
  have h_bot_cont : Continuous fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹ := by
    apply Continuous.inv₀
    · fun_prop
    · exact h_ne_bot
  have h_bot_intIntegrable : ∀ p q : ℝ,
      IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹)
        MeasureTheory.volume p q :=
    fun p q => h_bot_cont.intervalIntegrable p q
  -- Step 5: Split full bottom integral via additivity: a → (e.re-R₀) → (e.re+R₀) → b.
  have h_bot_split :
      (∫ x in a..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) =
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re - R₀)..(e.re + R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (h_bot_intIntegrable a (e.re - R₀)) (h_bot_intIntegrable (e.re - R₀) b),
        ← intervalIntegral.integral_add_adjacent_intervals
          (h_bot_intIntegrable (e.re - R₀) (e.re + R₀))
          (h_bot_intIntegrable (e.re + R₀) b)]
    ring
  -- The middle bottom integral equals the upper-half-disk diameter integral.
  -- Step 6: Combine.
  have h_uhd_eq :
      (∫ x in (e.re - R₀)..(e.re + R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - w)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := h_uhd_cg
  -- Final calc.
  have h_fY :
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - w)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - w)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - w)⁻¹) -
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - w)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      2 * Real.pi * Complex.I := by
    linear_combination h_rect_eq - h_uhd_eq - h_bot_split
  rw [h_fY]
  exact inv_mul_cancel₀ hpi

/-- **Path-connectedness of `F_Y` (closed form).** The closed F_Y region
`(Icc a b ×ℂ Icc e.im d) \ ball e R₀` (rectangle minus upper half of an
open disk centered on the bottom edge) is path-connected. Used to spread
the `MeromorphicOn` order propagation argument in the F_Y argument
principle. -/
theorem isPathConnected_rectMinusUpperHalfDisk
    (a b d : ℝ) (e : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀) (_hab : a < b)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d) :
    IsPathConnected ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  set p : ℂ := (e.re : ℂ) + (d : ℂ) * Complex.I with hp_def
  have hp_re : p.re = e.re := by
    simp [hp_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hp_im : p.im = d := by
    simp [hp_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  -- p ∉ ball e R₀ because |p - e| = d - e.im > R₀.
  have h_p_dist : R₀ < ‖p - e‖ := by
    have h_im_diff : (p - e).im = d - e.im := by
      simp [hp_def, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_abs := Complex.abs_im_le_norm (p - e)
    rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
    linarith
  have hp_in : p ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hp_re, Set.mem_Icc]; exact ⟨by linarith, by linarith⟩
      · rw [hp_im, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; linarith
  refine ⟨p, hp_in, fun z hz => ?_⟩
  obtain ⟨hz_rect, hz_not_ball⟩ := hz
  rw [Complex.mem_reProdIm] at hz_rect
  obtain ⟨hz_re_in, hz_im_in⟩ := hz_rect
  rw [Set.mem_Icc] at hz_re_in hz_im_in
  have hz_dist_ge : R₀ ≤ ‖z - e‖ := by
    by_contra h
    push Not at h
    exact hz_not_ball (Metric.mem_ball.mpr (by rw [Complex.dist_eq]; exact h))
  set mid : ℂ := (z.re : ℂ) + (d : ℂ) * Complex.I with hmid_def
  have hmid_re : mid.re = z.re := by
    simp [hmid_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hmid_im : mid.im = d := by
    simp [hmid_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have h_mid_dist : R₀ < ‖mid - e‖ := by
    have h_im_diff : (mid - e).im = d - e.im := by
      simp [hmid_def, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_abs := Complex.abs_im_le_norm (mid - e)
    rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
    linarith
  have hmid_in : mid ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hmid_re, Set.mem_Icc]; exact hz_re_in
      · rw [hmid_im, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; linarith
  -- JoinedIn F p z via p → mid (horizontal at top) then mid → z (vertical down).
  refine JoinedIn.trans (y := mid) ?_ ?_
  · -- JoinedIn F p mid: horizontal segment at y = d.
    apply JoinedIn.ofLine
      (f := fun t : ℝ => (((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I)
    · exact (by fun_prop : Continuous fun t : ℝ =>
        (((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I).continuousOn
    · push_cast; ring
    · push_cast; ring
    · rintro w ⟨t, ht, h_eq⟩
      rw [Set.mem_Icc] at ht
      rw [← h_eq]
      refine ⟨?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
            add_zero]
          rw [Set.mem_Icc]
          obtain ⟨hz_re_lo, hz_re_hi⟩ := hz_re_in
          refine ⟨?_, ?_⟩
          · nlinarith [ht.1, ht.2, hz_re_lo, h_a_lt, hR₀]
          · nlinarith [ht.1, ht.2, hz_re_hi, h_lt_b, hR₀]
        · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, zero_add,
            add_zero]
          rw [Set.mem_Icc]
          refine ⟨by linarith, le_refl _⟩
      · rw [Metric.mem_ball, Complex.dist_eq]
        push Not
        have h_im_diff :
            ((((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I - e).im
              = d - e.im := by
          simp only [Complex.sub_im, Complex.add_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, mul_one, zero_add, add_zero]
        have h_abs := Complex.abs_im_le_norm
          ((((1 - t) * e.re + t * z.re : ℝ) : ℂ) + (d : ℂ) * Complex.I - e)
        rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
        linarith
  · -- JoinedIn F mid z via vertical segment at x = z.re.
    apply JoinedIn.ofLine
      (f := fun t : ℝ => (z.re : ℂ) + (((1 - t) * d + t * z.im : ℝ) : ℂ) * Complex.I)
    · exact (by fun_prop : Continuous fun t : ℝ =>
        (z.re : ℂ) + (((1 - t) * d + t * z.im : ℝ) : ℂ) * Complex.I).continuousOn
    · show (z.re : ℂ) + (((1 - (0:ℝ)) * d + (0:ℝ) * z.im : ℝ) : ℂ) * Complex.I = mid
      rw [hmid_def]; push_cast; ring
    · show (z.re : ℂ) + (((1 - (1:ℝ)) * d + (1:ℝ) * z.im : ℝ) : ℂ) * Complex.I = z
      push_cast
      apply Complex.ext
      · simp
      · simp
    · rintro w ⟨t, ht, h_eq⟩
      rw [Set.mem_Icc] at ht
      rw [← h_eq]
      refine ⟨?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
            add_zero]
          rw [Set.mem_Icc]; exact hz_re_in
        · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, mul_zero,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, mul_one, zero_add,
            add_zero]
          rw [Set.mem_Icc]
          obtain ⟨hz_im_lo, hz_im_hi⟩ := hz_im_in
          refine ⟨?_, ?_⟩
          · nlinarith [ht.1, ht.2, hz_im_lo, h_e_im_R0_lt_d, hR₀]
          · nlinarith [ht.1, ht.2, hz_im_hi]
      · rw [Metric.mem_ball, Complex.dist_eq]
        push Not
        -- The point w = (z.re, s) where s = (1-t)·d + t·z.im ∈ [z.im, d].
        -- Squared distance to e: (z.re - e.re)² + (s - e.im)².
        -- s - e.im = (1-t)·(d - e.im) + t·(z.im - e.im). Both terms ≥ z.im - e.im ≥ 0
        -- (first since d > e.im + R₀ > e.im; second since z.im ≥ e.im).
        -- Specifically, s - e.im ≥ z.im - e.im, so (s - e.im)² ≥ (z.im - e.im)².
        -- Hence ‖w - e‖² ≥ (z.re - e.re)² + (z.im - e.im)² = ‖z - e‖² ≥ R₀².
        set s : ℝ := (1 - t) * d + t * z.im with hs_def
        have hs_ge : s ≥ z.im := by nlinarith [ht.1, ht.2, h_e_im_R0_lt_d, hR₀]
        have hs_im_diff_nn : 0 ≤ s - e.im := by linarith [hz_im_in.1]
        have hz_im_diff_nn : 0 ≤ z.im - e.im := by linarith [hz_im_in.1]
        have hw_re : ((z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e).re = z.re - e.re := by
          simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have hw_im : ((z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e).im = s - e.im := by
          simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have h_norm_sq_w : ‖(z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e‖^2 =
            (z.re - e.re)^2 + (s - e.im)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hw_re, hw_im]
          ring
        have h_norm_sq_z : ‖z - e‖^2 = (z.re - e.re)^2 + (z.im - e.im)^2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
              Complex.sub_re, Complex.sub_im]
          ring
        have h_sq_compare : (s - e.im)^2 ≥ (z.im - e.im)^2 := by
          have h1 : s - e.im ≥ z.im - e.im := by linarith
          nlinarith [hs_im_diff_nn, hz_im_diff_nn, h1]
        have h_z_sq_ge : ‖z - e‖^2 ≥ R₀^2 := by
          nlinarith [hz_dist_ge, norm_nonneg (z - e), hR₀.le]
        have h_wn_sq_ge :
            ‖(z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e‖^2 ≥ R₀^2 := by
          linarith [h_norm_sq_w, h_norm_sq_z, h_sq_compare]
        have h_wn_nn : 0 ≤ ‖(z.re : ℂ) + ((s : ℝ) : ℂ) * Complex.I - e‖ :=
          norm_nonneg _
        have h_sqrt := Real.sqrt_le_sqrt h_wn_sq_ge
        rw [Real.sqrt_sq hR₀.le, Real.sqrt_sq h_wn_nn] at h_sqrt
        exact h_sqrt

set_option maxHeartbeats 400000 in
-- The proof clones the Weierstrass-factorization structure of
-- `cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary` over the F_Y
-- region (closed rectangle minus open upper half-disk on the bottom
-- edge), applying `rectBoundary` and the upper-semicircle integral to
-- the rational factor `r` and the F_Y-shape Cauchy-Goursat
-- (`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn`) to
-- the analytic non-vanishing factor `h`. The combined elaboration
-- pressure (codiscrete + AccPt + 5 edge-membership +
-- arc-membership + divisor-support strict-interior analysis) exceeds
-- the default heartbeat limit.
/-- **Argument principle on a rectangle with an upper half-disk removed
from the bottom boundary.** For a function `g` analytic on a neighborhood
of the closed region `F_Y := (Icc a b ×ℂ Icc e.im d) \ ball e R₀` — the
rectangle `[a, b] × [e.im, d]` with the open upper half of the disk
centered at `e` on the bottom edge removed — and non-vanishing on each
of the five boundary pieces (the four rectangle edges and the upper
semicircle `|z − e| = R₀, Im z ≥ e.im`), the contour integral around
`∂F_Y` (CCW with the region interior on the left) of `g'/g` is `2πi`
times the count of zeros of `g` inside `F_Y^o`.

This is the **truncated `Γ(2)` fundamental domain argument principle**:
with `a = 0`, `b = 1`, `e.im = 0`, `e = 1/2`, `R₀ = 1/2`, `d = Y`, the
region `F_Y` is the truncation of the half-fundamental-domain
`F = {0 ≤ Re τ ≤ 1, 1 ≤ |2τ − 1|, Im τ > 0}` to `Im τ ≤ Y`. Applying
this theorem to `g(τ) := λ(τ) − w` (analytic on `ℍ ⊃ F_Y`,
non-vanishing on `∂F_Y` for `Im w > 0` by the boundary-image analysis
of `λ`) counts preimages of `w` under `λ` inside `F^o`.

The proof clones the Weierstrass-factorization structure of
`cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary`: factor
`g = (∏ᶠ u, (· − u)^{n_u}) · h` (with `n_u` the multiplicities of
zeros of `g` in `F_Y^o` and `h` analytic + non-vanishing on a
neighborhood of `F_Y`), split the log-derivative as
`g'/g = r'/r + h'/h`, integrate `h'/h` around `∂F_Y` via
`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn` (giving
zero), and reduce the `r'/r` integral to a Finset sum of single-zero
contributions, each evaluated via the rectangle and upper-semicircle
winding numbers. -/
theorem cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (hg_bot_left : ∀ x ∈ Set.Icc a (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (e.re + R₀) b,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc e.im d, g ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc e.im d, g ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0) :
    (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      Complex.I * (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
        g ((b : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
        g ((x : ℂ) + (d : ℂ) * Complex.I)) -
      Complex.I * (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
        g ((a : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ θ in (0 : ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
        g (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
    ((∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat : ℂ) := by
  -- Closed F_Y region.
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have h_e_im_lt_d : e.im < d := by linarith
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  -- Witness corner z₀ = (a, e.im).
  set z₀ : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hz₀_def
  have hz₀_re : z₀.re = a := by
    simp [hz₀_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_im : z₀.im = e.im := by
    simp [hz₀_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_in_F : z₀ ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hz₀_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hz₀_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (z₀ - e).re = a - e.re := by
        rw [Complex.sub_re, hz₀_re]
      have h_abs := Complex.abs_re_le_norm (z₀ - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hz₀_g_ne : g z₀ ≠ 0 :=
    hg_bot_left a (Set.left_mem_Icc.mpr (by linarith))
  have hz₀_analytic : AnalyticAt ℂ g z₀ := hg z₀ hz₀_in_F
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    rw [hz₀_analytic.meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g z₀ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hz₀_g_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  have hg_order : ∀ u ∈ F, meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    exact hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
      hz₀_in_F hu hz₀_order_ne_top
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  obtain ⟨h, h_analytic, h_nonzero, h_factor⟩ :=
    hg_mer.extract_zeros_poles
      (fun u : F => hg_order u.1 u.2)
      hdiv_finite
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  set r : ℂ → ℂ :=
    ∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor g F) u) with hr_def
  have hr_analytic : ∀ z, AnalyticAt ℂ r z := fun z =>
    Function.FactorizedRational.analyticAt (hD_nonneg z)
  have hF_ntriv : F.Nontrivial := by
    refine ⟨z₀, hz₀_in_F, (b : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · show _ ∈ Set.Icc a b
          have h_eq : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
            simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_eq]; exact Set.right_mem_Icc.mpr hab.le
        · show _ ∈ Set.Icc e.im d
          have h_eq : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
            simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [h_eq]; exact Set.right_mem_Icc.mpr (by linarith)
      · rw [Metric.mem_ball, Complex.dist_eq]; push Not
        have h_re_diff : (((b : ℂ) + (d : ℂ) * Complex.I) - e).re = b - e.re := by
          simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
            Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        have h_abs := Complex.abs_re_le_norm
          (((b : ℂ) + (d : ℂ) * Complex.I) - e)
        rw [h_re_diff, abs_of_pos (by linarith : 0 < b - e.re)] at h_abs
        linarith
    · intro h_eq
      have h_re : z₀.re = ((b : ℂ) + (d : ℂ) * Complex.I).re := by rw [h_eq]
      rw [hz₀_re] at h_re
      have : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this] at h_re
      linarith
  have h_accpt : ∀ z ∈ F, AccPt z (Filter.principal F) :=
    fun z hz => hF_preconn.preperfect_of_nontrivial hF_ntriv z hz
  have h_factor_mul : g =ᶠ[Filter.codiscreteWithin F] (fun w => r w * h w) := by
    filter_upwards [h_factor] with w hw
    simpa [smul_eq_mul] using hw
  have h_nhds_eq : ∀ z ∈ F, g =ᶠ[nhds z] (fun w => r w * h w) := by
    intro z hz
    have hz_g_an : AnalyticAt ℂ g z := hg z hz
    have hz_r_an : AnalyticAt ℂ r z := hr_analytic z
    have hz_h_an : AnalyticAt ℂ h z := h_analytic z hz
    have hz_rh_an : AnalyticAt ℂ (fun w => r w * h w) z := hz_r_an.mul hz_h_an
    have h_pnctd := hz_g_an.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hz_rh_an.meromorphicAt hz (h_accpt z hz) h_factor_mul
    exact (AnalyticAt.frequently_eq_iff_eventually_eq hz_g_an hz_rh_an).mp h_pnctd.frequently
  have h_g_eq : ∀ z ∈ F, g z = r z * h z := fun z hz =>
    (h_nhds_eq z hz).eq_of_nhds
  have h_deriv_eq : ∀ z ∈ F, deriv g z = deriv (fun w => r w * h w) z := fun z hz =>
    (h_nhds_eq z hz).deriv_eq
  have h_div_zero_at_edge : ∀ z ∈ F, g z ≠ 0 →
      (MeromorphicOn.divisor g F) z = 0 := by
    intro z hz hz_g_ne
    rw [MeromorphicOn.divisor_apply hg_mer hz,
        (hg z hz).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hz_g_ne)]
    simp
  have hr_ne_at_edge : ∀ z ∈ F, g z ≠ 0 → r z ≠ 0 := fun z hz hz_g_ne =>
    Function.FactorizedRational.ne_zero (h_div_zero_at_edge z hz hz_g_ne)
  -- Boundary membership (5 edges + arc) in F.
  have h_bot_left_mem : ∀ x ∈ Set.Icc a (e.re - R₀),
      ((x : ℂ) + (e.im : ℂ) * Complex.I) ∈ F := by
    intro x hx
    rw [Set.mem_Icc] at hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨hx.1, by linarith [hx.2]⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).im = e.im := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((x : ℂ) + (e.im : ℂ) * Complex.I) - e).re = x - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((x : ℂ) + (e.im : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_nonpos (by linarith [hx.2] : x - e.re ≤ 0)] at h_abs
      linarith
  have h_bot_right_mem : ∀ x ∈ Set.Icc (e.re + R₀) b,
      ((x : ℂ) + (e.im : ℂ) * Complex.I) ∈ F := by
    intro x hx
    rw [Set.mem_Icc] at hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨by linarith [hx.1], hx.2⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((x : ℂ) + (e.im : ℂ) * Complex.I).im = e.im := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((x : ℂ) + (e.im : ℂ) * Complex.I) - e).re = x - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((x : ℂ) + (e.im : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - e.re)] at h_abs
      linarith
  have h_top_mem : ∀ x ∈ Set.Icc a b,
      ((x : ℂ) + (d : ℂ) * Complex.I) ∈ F := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((x : ℂ) + (d : ℂ) * Complex.I).re = x := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq]; exact hx
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((x : ℂ) + (d : ℂ) * Complex.I).im = d := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_im_diff : (((x : ℂ) + (d : ℂ) * Complex.I) - e).im = d - e.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_im_le_norm
        (((x : ℂ) + (d : ℂ) * Complex.I) - e)
      rw [h_im_diff, abs_of_pos (by linarith : (0:ℝ) < d - e.im)] at h_abs
      linarith
  have h_right_mem : ∀ y ∈ Set.Icc e.im d,
      ((b : ℂ) + (y : ℂ) * Complex.I) ∈ F := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((b : ℂ) + (y : ℂ) * Complex.I).re = b := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨hab.le, le_refl _⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((b : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq]; exact hy
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((b : ℂ) + (y : ℂ) * Complex.I) - e).re = b - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((b : ℂ) + (y : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_pos (by linarith : 0 < b - e.re)] at h_abs
      linarith
  have h_left_mem : ∀ y ∈ Set.Icc e.im d,
      ((a : ℂ) + (y : ℂ) * Complex.I) ∈ F := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        have h_re_eq : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_re_eq, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · show _ ∈ Set.Icc e.im d
        have h_im_eq : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [h_im_eq]; exact hy
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (((a : ℂ) + (y : ℂ) * Complex.I) - e).re = a - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      have h_abs := Complex.abs_re_le_norm
        (((a : ℂ) + (y : ℂ) * Complex.I) - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have h_arc_mem : ∀ θ ∈ Set.Icc (0:ℝ) Real.pi,
      _root_.circleMap e R₀ θ ∈ F := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show _ ∈ Set.Icc a b
        rw [_root_.circleMap]
        have h_re_eq : (e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re =
            e.re + R₀ * Real.cos θ := by
          rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          ring
        rw [h_re_eq, Set.mem_Icc]
        have h_cos := Real.cos_le_one θ
        have h_cos_ge := Real.neg_one_le_cos θ
        exact ⟨by nlinarith [hR₀], by nlinarith [hR₀]⟩
      · show _ ∈ Set.Icc e.im d
        rw [_root_.circleMap]
        have h_im_eq : (e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im =
            e.im + R₀ * Real.sin θ := by
          rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          ring
        rw [h_im_eq, Set.mem_Icc]
        have h_sin_nn := Real.sin_nonneg_of_mem_Icc (Set.mem_Icc.mpr hθ)
        have h_sin_le_one := Real.sin_le_one θ
        exact ⟨by nlinarith [hR₀], by nlinarith [hR₀]⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      rw [_root_.circleMap]
      have h_norm_eq : ‖e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e‖ = R₀ := by
        rw [show e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
            (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from by ring,
          norm_mul, Complex.norm_real,
          Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg hR₀.le]
      rw [h_norm_eq]
  -- g'/g = r'/r + h'/h on boundary points where g ≠ 0.
  have h_logDeriv_split : ∀ z ∈ F, g z ≠ 0 →
      deriv (fun w => r w * h w) z / (r z * h z) =
      deriv r z / r z + deriv h z / h z := by
    intro z hz hz_g_ne
    have hr_ne := hr_ne_at_edge z hz hz_g_ne
    have hh_ne : h z ≠ 0 := h_nonzero ⟨z, hz⟩
    have hr_diff : DifferentiableAt ℂ r z := (hr_analytic z).differentiableAt
    have hh_diff : DifferentiableAt ℂ h z := (h_analytic z hz).differentiableAt
    have := logDeriv_mul z hr_ne hh_ne hr_diff hh_diff
    simp only [logDeriv_apply] at this
    exact this
  have h_int_eq_at_edge : ∀ z ∈ F, g z ≠ 0 →
      deriv g z / g z = deriv r z / r z + deriv h z / h z := by
    intro z hz hz_g_ne
    rw [h_g_eq z hz, h_deriv_eq z hz]
    exact h_logDeriv_split z hz hz_g_ne
  -- Per-edge/arc integrand equality.
  have h_int_bot_left : (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
      g ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a (e.re - R₀) := by
      rw [Set.uIcc_of_le (by linarith : a ≤ e.re - R₀)] at hx; exact hx
    exact h_int_eq_at_edge _ (h_bot_left_mem x hx_Icc) (hg_bot_left x hx_Icc)
  have h_int_bot_right :
      (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc (e.re + R₀) b := by
      rw [Set.uIcc_of_le (by linarith : e.re + R₀ ≤ b)] at hx; exact hx
    exact h_int_eq_at_edge _ (h_bot_right_mem x hx_Icc) (hg_bot_right x hx_Icc)
  have h_int_top : (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
      g ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hab.le] at hx; exact hx
    exact h_int_eq_at_edge _ (h_top_mem x hx_Icc) (hg_top x hx_Icc)
  have h_int_right : (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
      g ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc e.im d := by
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_right_mem y hy_Icc) (hg_right y hy_Icc)
  have h_int_left : (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
      g ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc e.im d := by
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_left_mem y hy_Icc) (hg_left y hy_Icc)
  have h_int_arc : (∫ θ in (0:ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
      g (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      (∫ θ in (0:ℝ)..Real.pi,
        (deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) +
          deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ)) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ_Icc : θ ∈ Set.Icc (0:ℝ) Real.pi := by
      rw [Set.uIcc_of_le Real.pi_nonneg] at hθ; exact hθ
    have h_eq := h_int_eq_at_edge _ (h_arc_mem θ hθ_Icc) (hg_arc θ hθ_Icc)
    change deriv g (_root_.circleMap e R₀ θ) / g (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ)) =
      (deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) +
        deriv h (_root_.circleMap e R₀ θ) / h (_root_.circleMap e R₀ θ)) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))
    rw [h_eq]
  -- h analytic & nonzero on F → h'/h is DifferentiableOn F.
  have h_h_ne : ∀ z ∈ F, h z ≠ 0 := fun z hz => h_nonzero ⟨z, hz⟩
  have h_dh_div_h_diff : DifferentiableOn ℂ (fun z => deriv h z / h z) F := by
    intro z hz
    have hh_ne := h_h_ne z hz
    have h_dh_an : AnalyticAt ℂ (deriv h) z := (h_analytic z hz).deriv
    have h_h_an : AnalyticAt ℂ h z := h_analytic z hz
    exact (h_dh_an.div h_h_an hh_ne).differentiableAt.differentiableWithinAt
  -- For each z ∈ F, AnalyticAt h z + h z ≠ 0 give an open nhd of z where h is analytic & ≠ 0.
  have h_an_and_ne_open : IsOpen ({z : ℂ | AnalyticAt ℂ h z} ∩ {z : ℂ | h z ≠ 0}) := by
    rw [isOpen_iff_eventually]
    rintro z ⟨hz_an, hz_ne⟩
    have h_an_ev : ∀ᶠ w in nhds z, AnalyticAt ℂ h w := hz_an.eventually_analyticAt
    have h_ne_ev : ∀ᶠ w in nhds z, h w ≠ 0 :=
      hz_an.continuousAt.eventually_ne hz_ne
    filter_upwards [h_an_ev, h_ne_ev] with w hw_an hw_ne
    exact ⟨hw_an, hw_ne⟩
  have h_F_sub_an_ne : F ⊆ {z : ℂ | AnalyticAt ℂ h z} ∩ {z : ℂ | h z ≠ 0} :=
    fun z hz => ⟨h_analytic z hz, h_h_ne z hz⟩
  obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
    hF_compact.exists_thickening_subset_open h_an_and_ne_open h_F_sub_an_ne
  -- Reduce δ to be ≤ R₀ for use in R₀'.
  set δ' : ℝ := min δ R₀ with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hR₀
  have hδ'_le_δ : δ' ≤ δ := min_le_left _ _
  have hδ'_le_R₀ : δ' ≤ R₀ := min_le_right _ _
  -- Define R₀' := R₀ - δ'/2.
  set R₀' : ℝ := R₀ - δ' / 2 with hR₀'_def
  have hR₀'_pos : 0 < R₀' := by
    rw [hR₀'_def]; linarith [hδ'_le_R₀, hδ'_pos]
  have hR₀'_lt : R₀' < R₀ := by rw [hR₀'_def]; linarith [hδ'_pos]
  -- Sub : (Ioo a b ×ℂ Ioo e.im d) \ closedBall e R₀' ⊆ thickening δ F.
  have h_sub_thickening :
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') ⊆
        Metric.thickening δ F := by
    rintro z ⟨hz_box, hz_not_closedR₀'⟩
    rw [Complex.mem_reProdIm] at hz_box
    obtain ⟨hz_re_Ioo, hz_im_Ioo⟩ := hz_box
    rw [Set.mem_Ioo] at hz_re_Ioo hz_im_Ioo
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz_not_closedR₀'
    push Not at hz_not_closedR₀'
    have hz_dist_gt : R₀' < ‖z - e‖ := hz_not_closedR₀'
    rw [Metric.mem_thickening_iff]
    by_cases hz_in_F : ‖z - e‖ ≥ R₀
    · -- z ∈ F (or close).
      refine ⟨z, ⟨?_, ?_⟩, by rw [dist_self]; exact hδ_pos⟩
      · rw [Complex.mem_reProdIm]
        refine ⟨Set.Ioo_subset_Icc_self hz_re_Ioo |> Set.mem_Icc.mpr ∘ id, ?_⟩
        · exact Set.Ioo_subset_Icc_self hz_im_Ioo
      · rw [Metric.mem_ball, Complex.dist_eq]; push Not; exact hz_in_F
    · -- z in annulus: R₀' < ‖z - e‖ < R₀.
      push Not at hz_in_F
      have h_z_norm_pos : 0 < ‖z - e‖ := by linarith [hR₀'_pos]
      have h_z_norm_ne : ‖z - e‖ ≠ 0 := ne_of_gt h_z_norm_pos
      -- Project radially outward: z' := e + (R₀/‖z - e‖) · (z - e).
      set z' : ℂ := e + ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) with hz'_def
      have hz'_sub : z' - e = ((R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
        rw [hz'_def]; ring
      have h_R₀_div_pos : 0 < R₀ / ‖z - e‖ := div_pos hR₀ h_z_norm_pos
      have h_R₀_div_ge_one : 1 ≤ R₀ / ‖z - e‖ := by
        rw [le_div_iff₀ h_z_norm_pos]; linarith
      have hz'_norm : ‖z' - e‖ = R₀ := by
        rw [hz'_sub, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg h_R₀_div_pos.le, div_mul_cancel₀ _ h_z_norm_ne]
      -- z' is in F.
      have hz'_re_diff : (z' - e).re = (R₀ / ‖z - e‖) * (z - e).re := by
        rw [hz'_sub]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hz'_im_diff : (z' - e).im = (R₀ / ‖z - e‖) * (z - e).im := by
        rw [hz'_sub]
        simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      have hz'_re : z'.re = e.re + (R₀ / ‖z - e‖) * (z.re - e.re) := by
        have h1 : z'.re = e.re + (z' - e).re := by simp [Complex.sub_re]
        rw [h1, hz'_re_diff, Complex.sub_re]
      have hz'_im : z'.im = e.im + (R₀ / ‖z - e‖) * (z.im - e.im) := by
        have h1 : z'.im = e.im + (z' - e).im := by simp [Complex.sub_im]
        rw [h1, hz'_im_diff, Complex.sub_im]
      -- |z'.re - e.re| ≤ R₀ and z'.im - e.im ≥ 0 with ≤ R₀.
      have h_z'_re_abs : |z'.re - e.re| ≤ R₀ := by
        have h_re_eq : z'.re - e.re = (R₀ / ‖z - e‖) * (z.re - e.re) := by
          rw [hz'_re]; ring
        have h_abs_le := Complex.abs_re_le_norm (z' - e)
        rw [show (z' - e).re = z'.re - e.re from by simp [Complex.sub_re], h_re_eq,
            hz'_norm] at h_abs_le
        rw [h_re_eq]; exact h_abs_le
      have h_z'_im_abs : |z'.im - e.im| ≤ R₀ := by
        have h_im_eq : z'.im - e.im = (R₀ / ‖z - e‖) * (z.im - e.im) := by
          rw [hz'_im]; ring
        have h_abs_le := Complex.abs_im_le_norm (z' - e)
        rw [show (z' - e).im = z'.im - e.im from by simp [Complex.sub_im], h_im_eq,
            hz'_norm] at h_abs_le
        rw [h_im_eq]; exact h_abs_le
      have h_z'_im_nn : 0 ≤ z'.im - e.im := by
        have h_im_eq : z'.im - e.im = (R₀ / ‖z - e‖) * (z.im - e.im) := by
          rw [hz'_im]; ring
        have h_z_im_nn : 0 ≤ z.im - e.im := by linarith [hz_im_Ioo.1]
        rw [h_im_eq]; exact mul_nonneg h_R₀_div_pos.le h_z_im_nn
      have hz'_in_F : z' ∈ F := by
        refine ⟨?_, ?_⟩
        · rw [Complex.mem_reProdIm]
          refine ⟨?_, ?_⟩
          · rw [Set.mem_Icc]
            refine ⟨?_, ?_⟩
            · have h_le := abs_le.mp h_z'_re_abs
              linarith [h_le.1, h_a_lt]
            · have h_le := abs_le.mp h_z'_re_abs
              linarith [h_le.2, h_lt_b]
          · rw [Set.mem_Icc]
            refine ⟨by linarith [h_z'_im_nn], ?_⟩
            have h_le := abs_le.mp h_z'_im_abs
            linarith [h_le.2, h_e_im_R0_lt_d]
        · rw [Metric.mem_ball, Complex.dist_eq, hz'_norm]
          exact lt_irrefl R₀
      -- ‖z - z'‖ < δ/2 ≤ δ.
      have h_z_z'_sub : z - z' = ((1 - R₀ / ‖z - e‖ : ℝ) : ℂ) * (z - e) := by
        rw [hz'_def]; push_cast; ring
      have h_one_minus : 1 - R₀ / ‖z - e‖ ≤ 0 := by linarith
      have h_dist_z_z' : dist z z' = R₀ - ‖z - e‖ := by
        rw [dist_eq_norm, h_z_z'_sub, norm_mul, Complex.norm_real,
            Real.norm_eq_abs,
            abs_of_nonpos h_one_minus]
        rw [neg_sub, sub_mul, div_mul_cancel₀ _ h_z_norm_ne, one_mul]
      have h_dist_lt : dist z z' < δ := by
        rw [h_dist_z_z']
        have : R₀ - ‖z - e‖ < δ' / 2 := by linarith
        linarith [hδ'_le_δ]
      exact ⟨z', hz'_in_F, h_dist_lt⟩
  -- h'/h DifferentiableOn (Ioo a b ×ℂ Ioo e.im d) \ closedBall e R₀'.
  have h_dh_div_h_diff_enlarged : DifferentiableOn ℂ (fun z => deriv h z / h z)
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') := by
    intro z hz
    have hz_in : z ∈ Metric.thickening δ F := h_sub_thickening hz
    have hz_in_an_ne := hδ_sub hz_in
    obtain ⟨hz_an, hz_ne⟩ := hz_in_an_ne
    have h_dh_an : AnalyticAt ℂ (deriv h) z := hz_an.deriv
    exact (h_dh_an.div hz_an hz_ne).differentiableAt.differentiableWithinAt
  -- Apply F_Y CG to h'/h.
  have h_h_cont_F : ContinuousOn (fun z => deriv h z / h z) F :=
    h_dh_div_h_diff.continuousOn
  have h_cauchy_h :=
    integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn
      (fun z => deriv h z / h z) a b d e R₀
      hab h_e_im_lt_d hR₀ h_a_lt h_lt_b h_e_im_R0_lt_d h_h_cont_F
      ⟨R₀', hR₀'_pos, hR₀'_lt, h_dh_div_h_diff_enlarged⟩
  -- Dsupp.
  set Dsupp := hdiv_finite.toFinset with hDsupp_def
  -- Strict interior characterization of Dsupp.
  have hsupp_in_open : ∀ u ∈ Dsupp,
      u ∈ (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀ := by
    intro u hu
    have hu_supp : u ∈ (MeromorphicOn.divisor g F).support := by
      simpa [hDsupp_def] using hu
    have hu_F : u ∈ F :=
      (MeromorphicOn.divisor g F).supportWithinDomain hu_supp
    -- u not on any boundary piece.
    obtain ⟨hu_box, hu_not_ball⟩ := hu_F
    rw [Complex.mem_reProdIm] at hu_box
    obtain ⟨hu_re_Icc, hu_im_Icc⟩ := hu_box
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Ioo]
        refine ⟨lt_of_le_of_ne hu_re_Icc.1 (fun h_eq => ?_),
                lt_of_le_of_ne hu_re_Icc.2 (fun h_eq => ?_)⟩
        · -- u.re = a, then u is on left edge.
          have hu_eq : u = (a : ℂ) + (u.im : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((a : ℂ) + (u.im : ℂ) * Complex.I)
            (h_left_mem u.im hu_im_Icc) (hg_left u.im hu_im_Icc)
        · -- u.re = b, then u is on right edge.
          have hu_eq : u = (b : ℂ) + (u.im : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, h_eq]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((b : ℂ) + (u.im : ℂ) * Complex.I)
            (h_right_mem u.im hu_im_Icc) (hg_right u.im hu_im_Icc)
      · rw [Set.mem_Ioo]
        refine ⟨lt_of_le_of_ne hu_im_Icc.1 (fun h_eq => ?_),
                lt_of_le_of_ne hu_im_Icc.2 (fun h_eq => ?_)⟩
        · -- u.im = e.im, then u is on bottom: split into bot_left, bot_middle (arc actually,
          -- but u ∉ ball means u not in middle), bot_right.
          have hu_eq : u = (u.re : ℂ) + (e.im : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
          -- u.re ∈ [a, e.re - R₀] ∪ [e.re + R₀, b] because u ∉ ball.
          have h_u_re_outside : u.re ≤ e.re - R₀ ∨ e.re + R₀ ≤ u.re := by
            by_contra h
            push Not at h
            obtain ⟨h1, h2⟩ := h
            apply hu_not_ball
            rw [Metric.mem_ball, Complex.dist_eq]
            have h_uminus_im : (u - e).im = 0 := by
              rw [Complex.sub_im, ← h_eq]; ring
            have h_norm_eq_re : ‖u - e‖ = |(u - e).re| := by
              have h_sq : ‖u - e‖^2 = (u - e).re^2 := by
                rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, h_uminus_im]
                ring
              have h_nn : 0 ≤ ‖u - e‖ := norm_nonneg _
              have h_abs_nn : 0 ≤ |(u - e).re| := abs_nonneg _
              have h_abs_sq : |(u - e).re|^2 = (u - e).re^2 := sq_abs _
              have h_eq_sq : ‖u - e‖^2 = |(u - e).re|^2 := by rw [h_sq, h_abs_sq]
              nlinarith [sq_nonneg (‖u - e‖ - |(u - e).re|),
                sq_nonneg (‖u - e‖ + |(u - e).re|), h_eq_sq, h_nn, h_abs_nn]
            rw [h_norm_eq_re, Complex.sub_re, abs_lt]
            constructor <;> linarith
          rcases h_u_re_outside with h_left | h_right
          · rw [hu_eq] at hu_supp
            apply hu_supp
            exact h_div_zero_at_edge ((u.re : ℂ) + (e.im : ℂ) * Complex.I)
              (h_bot_left_mem u.re (Set.mem_Icc.mpr ⟨hu_re_Icc.1, h_left⟩))
              (hg_bot_left u.re (Set.mem_Icc.mpr ⟨hu_re_Icc.1, h_left⟩))
          · rw [hu_eq] at hu_supp
            apply hu_supp
            exact h_div_zero_at_edge ((u.re : ℂ) + (e.im : ℂ) * Complex.I)
              (h_bot_right_mem u.re (Set.mem_Icc.mpr ⟨h_right, hu_re_Icc.2⟩))
              (hg_bot_right u.re (Set.mem_Icc.mpr ⟨h_right, hu_re_Icc.2⟩))
        · -- u.im = d, then u is on top edge.
          have hu_eq : u = (u.re : ℂ) + (d : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, h_eq]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((u.re : ℂ) + (d : ℂ) * Complex.I)
            (h_top_mem u.re hu_re_Icc) (hg_top u.re hu_re_Icc)
    · -- u ∉ closedBall e R₀: u ∉ ball + u not on arc → strict outside.
      intro h_in_closed
      rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_closed
      -- u not on ball (open).
      have h_norm_lt_or_eq : ‖u - e‖ < R₀ ∨ ‖u - e‖ = R₀ :=
        lt_or_eq_of_le h_in_closed
      rcases h_norm_lt_or_eq with h_lt | h_eq
      · apply hu_not_ball
        rw [Metric.mem_ball, Complex.dist_eq]; exact h_lt
      · -- ‖u - e‖ = R₀: u on the circle |z - e| = R₀.
        -- u.im ≥ e.im (since u ∈ Icc e.im d and u ∉ middle bottom).
        -- Hence u = circleMap e R₀ θ for some θ ∈ [0, π]. Apply hg_arc.
        have hu_im_ge : e.im ≤ u.im := hu_im_Icc.1
        have h_uminus_im_nn : 0 ≤ (u - e).im := by
          rw [Complex.sub_im]; linarith
        -- u = e + R₀ * exp(I*θ) where θ = arg(u - e), which is in [0, π].
        have h_arg_in : (u - e).arg ∈ Set.Icc (0 : ℝ) Real.pi := by
          rw [Set.mem_Icc]
          have h_uminus_ne : u - e ≠ 0 := by
            intro h_z; rw [h_z, norm_zero] at h_eq; linarith
          refine ⟨?_, Complex.arg_le_pi (u - e)⟩
          exact Complex.arg_nonneg_iff.mpr h_uminus_im_nn
        have h_circle : _root_.circleMap e R₀ (u - e).arg = u := by
          rw [_root_.circleMap]
          have h_norm_mul := Complex.norm_mul_exp_arg_mul_I (u - e)
          rw [h_eq] at h_norm_mul
          linear_combination h_norm_mul
        rw [← h_circle] at hu_supp
        apply hu_supp
        exact h_div_zero_at_edge (_root_.circleMap e R₀ (u - e).arg)
          (h_arc_mem (u - e).arg h_arg_in) (hg_arc (u - e).arg h_arg_in)
  -- Per-pole F_Y winding = 1.
  have h_per_pole : ∀ u ∈ Dsupp,
      (2 * Real.pi * Complex.I)⁻¹ * (
        (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 1 := by
    intro u hu
    exact rectMinusUpperHalfDiskWindingNumber_inside_eq_one a b d e R₀ hR₀ hab
      h_a_lt h_lt_b h_e_im_R0_lt_d (hsupp_in_open u hu)
  -- 2πi ≠ 0.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  -- Express r as Finset product.
  have hD_hfs : (fun u : ℂ => MeromorphicOn.divisor g F u).HasFiniteSupport :=
    hdiv_finite
  have hr_eq_finset : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ (MeromorphicOn.divisor g F u) := by
    intro z
    have heq := Function.FactorizedRational.finprod_eq_fun hD_hfs
    have hrz : r z = ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor g F u) := by
      rw [hr_def, heq]
    rw [hrz]
    rw [finprod_eq_prod_of_mulSupport_subset
      (f := fun u => (z - u) ^ (MeromorphicOn.divisor g F u))
      (s := Dsupp)]
    intro u hu
    simp only [Function.mem_mulSupport, ne_eq] at hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro h_zero
    apply hu
    rw [h_zero]; simp
  have hzpow_eq_pow : ∀ u : ℂ, ∀ z : ℂ,
      (z - u) ^ (MeromorphicOn.divisor g F u) =
      (z - u) ^ ((MeromorphicOn.divisor g F u).toNat) := by
    intro u z
    rw [← zpow_natCast (z - u) ((MeromorphicOn.divisor g F u).toNat),
        Int.toNat_of_nonneg (hD_nonneg u)]
  have hr_eq_natpow : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ ((MeromorphicOn.divisor g F u).toNat) := by
    intro z
    rw [hr_eq_finset z]
    apply Finset.prod_congr rfl
    intro u _
    exact hzpow_eq_pow u z
  -- logDeriv r at boundary points (where g ≠ 0).
  have h_logDeriv_r_eq : ∀ z ∈ F, g z ≠ 0 →
      deriv r z / r z = ∑ u ∈ Dsupp,
        ((MeromorphicOn.divisor g F u : ℂ) / (z - u)) := by
    intro z hz hz_g_ne
    have hz_ne_u : ∀ u ∈ Dsupp, z - u ≠ 0 := by
      intro u hu hzu
      have hz_eq : z = u := by linear_combination hzu
      have hu_supp : u ∈ (MeromorphicOn.divisor g F).support := by
        simpa [hDsupp_def] using hu
      apply hu_supp
      rw [← hz_eq]
      exact h_div_zero_at_edge z hz hz_g_ne
    set D := MeromorphicOn.divisor g F
    have hr_funext_nat : r = fun y => ∏ u ∈ Dsupp, (y - u) ^ ((D u).toNat) := by
      funext y; exact hr_eq_natpow y
    rw [show deriv r z / r z = logDeriv r z from rfl, hr_funext_nat]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u _
      have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := by fun_prop
      rw [show (fun w : ℂ => (w - u) ^ ((D u).toNat)) =
          (fun w : ℂ => (fun w' => w' - u) w ^ ((D u).toNat)) from rfl,
          logDeriv_fun_pow hd, logDeriv_apply]
      have hnat_eq : ((D u).toNat : ℤ) = D u := Int.toNat_of_nonneg (hD_nonneg u)
      have hnat : ((D u).toNat : ℂ) = (D u : ℂ) := by exact_mod_cast hnat_eq
      rw [hnat]
      simp; ring
    · intro u hu
      exact pow_ne_zero _ (hz_ne_u u hu)
    · intro u _
      exact ((differentiable_id.sub_const u).pow _).differentiableAt
  -- Non-vanishing of (z - u) on each edge/arc for u ∈ Dsupp.
  have h_ne_bot_left : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (e.im : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_im_Ioo : u.im ∈ Set.Ioo e.im d := hu_box.2
    rw [Set.mem_Ioo] at hu_im_Ioo
    have h_im : ((x : ℂ) + (e.im : ℂ) * Complex.I - u).im = e.im - u.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_im_eq : e.im - u.im = 0 := by
      have := congrArg Complex.im h_eq; rw [h_im] at this; simpa using this
    linarith [hu_im_Ioo.1]
  have h_ne_top : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (d : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_im_Ioo : u.im ∈ Set.Ioo e.im d := hu_box.2
    rw [Set.mem_Ioo] at hu_im_Ioo
    have h_im : ((x : ℂ) + (d : ℂ) * Complex.I - u).im = d - u.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_im_eq : d - u.im = 0 := by
      have := congrArg Complex.im h_eq; rw [h_im] at this; simpa using this
    linarith [hu_im_Ioo.2]
  have h_ne_right : ∀ u ∈ Dsupp, ∀ _y : ℝ,
      (b : ℂ) + (_y : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu y h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_re_Ioo : u.re ∈ Set.Ioo a b := hu_box.1
    rw [Set.mem_Ioo] at hu_re_Ioo
    have h_re : ((b : ℂ) + (y : ℂ) * Complex.I - u).re = b - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : b - u.re = 0 := by
      have := congrArg Complex.re h_eq; rw [h_re] at this; simpa using this
    linarith [hu_re_Ioo.2]
  have h_ne_left : ∀ u ∈ Dsupp, ∀ _y : ℝ,
      (a : ℂ) + (_y : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu y h_eq
    obtain ⟨hu_box, _⟩ := hsupp_in_open u hu
    rw [Complex.mem_reProdIm] at hu_box
    have hu_re_Ioo : u.re ∈ Set.Ioo a b := hu_box.1
    rw [Set.mem_Ioo] at hu_re_Ioo
    have h_re : ((a : ℂ) + (y : ℂ) * Complex.I - u).re = a - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : a - u.re = 0 := by
      have := congrArg Complex.re h_eq; rw [h_re] at this; simpa using this
    linarith [hu_re_Ioo.1]
  have h_ne_arc : ∀ u ∈ Dsupp, ∀ θ : ℝ,
      _root_.circleMap e R₀ θ - u ≠ 0 := by
    intro u hu θ h_eq
    obtain ⟨_, hu_not_closed⟩ := hsupp_in_open u hu
    apply hu_not_closed
    have h_eq' : u = _root_.circleMap e R₀ θ := by linear_combination -h_eq
    rw [Metric.mem_closedBall, Complex.dist_eq, h_eq', _root_.circleMap]
    have h_sub : e + (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - e =
        (R₀ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by ring
    rw [h_sub, norm_mul, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg hR₀.le]
  -- IntervalIntegrable for each summand on each edge/arc.
  have h_summand_int_bot_left : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((x : ℂ) + (e.im : ℂ) * Complex.I - u))
        MeasureTheory.volume a (e.re - R₀) := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_bot_left u hu x)
  have h_summand_int_bot_right : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((x : ℂ) + (e.im : ℂ) * Complex.I - u))
        MeasureTheory.volume (e.re + R₀) b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_bot_left u hu x)
  have h_summand_int_top : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((x : ℂ) + (d : ℂ) * Complex.I - u))
        MeasureTheory.volume a b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_top u hu x)
  have h_summand_int_right : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((b : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume e.im d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_right u hu y)
  have h_summand_int_left : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / ((a : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume e.im d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_left u hu y)
  have h_summand_int_arc : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun θ : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / (_root_.circleMap e R₀ θ - u) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
        MeasureTheory.volume 0 Real.pi := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont1 : Continuous fun θ : ℝ => (_root_.circleMap e R₀ θ - u) := by
      unfold _root_.circleMap
      fun_prop
    have h_cont2 : Continuous fun θ : ℝ =>
        (MeromorphicOn.divisor g F u : ℂ) / (_root_.circleMap e R₀ θ - u) :=
      continuous_const.div h_cont1 (fun θ => h_ne_arc u hu θ)
    have h_cont3 : Continuous fun θ : ℝ =>
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by fun_prop
    exact h_cont2.mul h_cont3
  -- IntervalIntegrability of r'/r on each edge/arc.
  have hr_diff_global : Differentiable ℂ r := fun z => (hr_analytic z).differentiableAt
  have hr_cont : Continuous r := hr_diff_global.continuous
  have h_dr_cont : Continuous (deriv r) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    exact (hr_analytic z).deriv.continuousAt
  have h_dr_div_r_int_bot_left : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re - R₀) := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_bot_left u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_bot_right : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume (e.re + R₀) b := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_bot_left u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_top : IntervalIntegrable
      (fun x : ℝ => deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ x : ℝ, r ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0 := by
      intro x
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_top u hu x))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_right : IntervalIntegrable
      (fun y : ℝ => deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ y : ℝ, r ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_right u hu y))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_left : IntervalIntegrable
      (fun y : ℝ => deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I)) := by fun_prop
    have h_r_param_ne : ∀ y : ℝ, r ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_left u hu y))
    exact (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
  have h_dr_div_r_int_arc : IntervalIntegrable
      (fun θ : ℝ => deriv r (_root_.circleMap e R₀ θ) /
        r (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (fun θ : ℝ => _root_.circleMap e R₀ θ) := by
      unfold _root_.circleMap; fun_prop
    have h_r_param_ne : ∀ θ : ℝ, r (_root_.circleMap e R₀ θ) ≠ 0 := by
      intro θ
      rw [hr_eq_natpow]
      exact Finset.prod_ne_zero_iff.mpr
        (fun u hu => pow_ne_zero _ (h_ne_arc u hu θ))
    have h_dr_r_param : Continuous fun θ : ℝ =>
        deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) :=
      (h_dr_cont.comp h_param_cont).div (hr_cont.comp h_param_cont) h_r_param_ne
    have h_ie_cont : Continuous fun θ : ℝ =>
        Complex.I * R₀ * Complex.exp (Complex.I * θ) := by fun_prop
    exact h_dr_r_param.mul h_ie_cont
  -- IntervalIntegrability of h'/h on each edge/arc.
  have h_dh_div_h_int_bot_left : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume a (e.re - R₀) := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.uIcc a (e.re - R₀)) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I)
        (Set.uIcc a (e.re - R₀)) F := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : a ≤ e.re - R₀)] at hx
      exact h_bot_left_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_bot_right : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I))
      MeasureTheory.volume (e.re + R₀) b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (e.im : ℂ) * Complex.I))
        (Set.uIcc (e.re + R₀) b) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (e.im : ℂ) * Complex.I)
        (Set.uIcc (e.re + R₀) b) F := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : e.re + R₀ ≤ b)] at hx
      exact h_bot_right_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_top : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I))
        (Set.uIcc a b) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I)
        (Set.uIcc a b) F := by
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_top_mem x hx
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_right : IntervalIntegrable
      (fun y : ℝ => deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I))
        (Set.uIcc e.im d) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc e.im d) F := by
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_right_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_left : IntervalIntegrable
      (fun y : ℝ => deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume e.im d := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I))
        (Set.uIcc e.im d) := by
      apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc e.im d) F := by
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_left_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  have h_dh_div_h_int_arc : IntervalIntegrable
      (fun θ : ℝ => deriv h (_root_.circleMap e R₀ θ) /
        h (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))
      MeasureTheory.volume 0 Real.pi := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun θ : ℝ => _root_.circleMap e R₀ θ)
        (Set.uIcc 0 Real.pi) := by
      apply Continuous.continuousOn
      unfold _root_.circleMap; fun_prop
    have h_param_maps_to : Set.MapsTo (fun θ : ℝ => _root_.circleMap e R₀ θ)
        (Set.uIcc 0 Real.pi) F := by
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_nonneg] at hθ
      exact h_arc_mem θ hθ
    have h_dh_r_param : ContinuousOn (fun θ : ℝ => deriv h (_root_.circleMap e R₀ θ) /
        h (_root_.circleMap e R₀ θ)) (Set.uIcc 0 Real.pi) :=
      h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
    have h_ie_cont : ContinuousOn (fun θ : ℝ =>
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) (Set.uIcc 0 Real.pi) := by
      apply Continuous.continuousOn; fun_prop
    exact h_dh_r_param.mul h_ie_cont
  -- Per-edge r-integral decomposition.
  have h_bot_left_r_decomp :
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        (∫ x in a..(e.re - R₀), ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((x : ℂ) + (e.im : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : a ≤ e.re - R₀)] at hx
      exact h_logDeriv_r_eq _ (h_bot_left_mem x hx) (hg_bot_left x hx)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_bot_left]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_bot_right_r_decomp :
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          r ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        (∫ x in (e.re + R₀)..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((x : ℂ) + (e.im : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : e.re + R₀ ≤ b)] at hx
      exact h_logDeriv_r_eq _ (h_bot_right_mem x hx) (hg_bot_right x hx)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_bot_right]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_top_r_decomp :
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
          r ((x : ℂ) + (d : ℂ) * Complex.I)) =
        (∫ x in a..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((x : ℂ) + (d : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      exact h_logDeriv_r_eq _ (h_top_mem x hx) (hg_top x hx)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_top]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_right_r_decomp :
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
          r ((b : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in e.im..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((b : ℂ) + (y : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_logDeriv_r_eq _ (h_right_mem y hy) (hg_right y hy)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_right]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_left_r_decomp :
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise :
        (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
          r ((a : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in e.im..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          ((a : ℂ) + (y : ℂ) * Complex.I - u)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le h_e_im_lt_d.le] at hy
      exact h_logDeriv_r_eq _ (h_left_mem y hy) (hg_left y hy)
    rw [h_pointwise, intervalIntegral.integral_finset_sum h_summand_int_left]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have h_arc_r_decomp :
      (∫ θ in (0:ℝ)..Real.pi, deriv r (_root_.circleMap e R₀ θ) /
        r (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
        (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    have h_pointwise :
        (∫ θ in (0:ℝ)..Real.pi, deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (∫ θ in (0:ℝ)..Real.pi,
          (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
            (_root_.circleMap e R₀ θ - u)) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_nonneg] at hθ
      have h_eq := h_logDeriv_r_eq _ (h_arc_mem θ hθ) (hg_arc θ hθ)
      change deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) =
        (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
          (_root_.circleMap e R₀ θ - u)) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))
      rw [h_eq]
    rw [h_pointwise]
    rw [show (fun θ : ℝ => (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
            (_root_.circleMap e R₀ θ - u)) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (fun θ : ℝ => ∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) /
            (_root_.circleMap e R₀ θ - u) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ))) from by
      funext θ; rw [Finset.sum_mul]]
    rw [intervalIntegral.integral_finset_sum h_summand_int_arc]
    apply Finset.sum_congr rfl
    intro u _
    simp_rw [div_eq_mul_inv]
    rw [show (fun θ : ℝ => (MeromorphicOn.divisor g F u : ℂ) *
          (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (fun θ : ℝ => (MeromorphicOn.divisor g F u : ℂ) *
          ((_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) from by funext θ; ring]
    exact intervalIntegral.integral_const_mul _ _
  -- Per-pole 6-piece combination = 2πi.
  have h_per_pole_eq : ∀ u ∈ Dsupp,
      (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
      (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
      Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
      Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
      (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      2 * Real.pi * Complex.I := by
    intro u hu
    have h := h_per_pole u hu
    have hk : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ *
        ((∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ θ in (0 : ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))))) =
        (2 * Real.pi * Complex.I) * 1 := by rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at hk
    exact hk
  -- h-pieces sum to 0 (rearrange h_cauchy_h).
  have h_h_sum_zero :
      ((∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
       (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
       Complex.I * (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
          h ((b : ℂ) + (y : ℂ) * Complex.I)) -
       (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
          h ((x : ℂ) + (d : ℂ) * Complex.I)) -
       Complex.I * (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
          h ((a : ℂ) + (y : ℂ) * Complex.I)) -
       (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = 0 := by
    have := h_cauchy_h
    linear_combination this
  -- Per-edge/arc split: ∫ (r'/r + h'/h) = ∫ r'/r + ∫ h'/h.
  have h_bot_left_split :
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in a..(e.re - R₀), deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_bot_left h_dh_div_h_int_bot_left
  have h_bot_right_split :
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
      (∫ x in (e.re + R₀)..b, deriv r ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        r ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        h ((x : ℂ) + (e.im : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_bot_right h_dh_div_h_int_bot_right
  have h_top_split :
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I)) +
      (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_top h_dh_div_h_int_top
  have h_right_split :
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_right h_dh_div_h_int_right
  have h_left_split :
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in e.im..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_left h_dh_div_h_int_left
  have h_arc_split :
      (∫ θ in (0:ℝ)..Real.pi,
        (deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) +
          deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ)) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      (∫ θ in (0:ℝ)..Real.pi, deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) +
      (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    rw [show (fun θ : ℝ => (deriv r (_root_.circleMap e R₀ θ) /
            r (_root_.circleMap e R₀ θ) +
            deriv h (_root_.circleMap e R₀ θ) /
            h (_root_.circleMap e R₀ θ)) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
        (fun θ : ℝ => deriv r (_root_.circleMap e R₀ θ) /
          r (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ)) +
          deriv h (_root_.circleMap e R₀ θ) /
          h (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))) from by funext θ; ring]
    exact intervalIntegral.integral_add h_dr_div_r_int_arc h_dh_div_h_int_arc
  -- Convert Finset sum to finsum.
  have h_finset_eq_finsum :
      (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ)) =
      (∑ᶠ u, (MeromorphicOn.divisor g F u : ℂ)) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Dsupp)]
    intro u hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro hzero
    apply hu
    simp only [Function.mem_support, ne_eq] at hu
    push_cast at hu ⊢
    simp [hzero] at hu
  have h_finsum_int_eq_nat :
      (∑ᶠ u, (MeromorphicOn.divisor g F u : ℂ)) =
      (((∑ᶠ u, MeromorphicOn.divisor g F u).toNat : ℤ) : ℂ) := by
    have h_nonneg : 0 ≤ ∑ᶠ u, MeromorphicOn.divisor g F u :=
      finsum_nonneg (fun u => hD_nonneg u)
    rw [Int.toNat_of_nonneg h_nonneg]
    have hcast := AddMonoidHom.map_finsum (Int.castRingHom ℂ).toAddMonoidHom
      (f := fun u => MeromorphicOn.divisor g F u) hdiv_finite
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Int.coe_castRingHom] at hcast
    rw [← hcast]
  calc (2 * Real.pi * Complex.I)⁻¹ * (
        (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
        (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
          g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
        Complex.I * (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
          g ((b : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
          g ((x : ℂ) + (d : ℂ) * Complex.I)) -
        Complex.I * (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
          g ((a : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ θ in (0 : ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
          g (_root_.circleMap e R₀ θ) *
          (Complex.I * R₀ * Complex.exp (Complex.I * θ))))
      = (2 * Real.pi * Complex.I)⁻¹ * (
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
            h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
            h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
        Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
         (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
            h ((b : ℂ) + (y : ℂ) * Complex.I))) -
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
         (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
            h ((x : ℂ) + (d : ℂ) * Complex.I))) -
        Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
         (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
            h ((a : ℂ) + (y : ℂ) * Complex.I))) -
        ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
            (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
              (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) +
         (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
            h (_root_.circleMap e R₀ θ) *
            (Complex.I * R₀ * Complex.exp (Complex.I * θ))))) := by
          rw [h_int_bot_left, h_int_bot_right, h_int_top, h_int_right, h_int_left,
              h_int_arc,
              h_bot_left_split, h_bot_right_split, h_top_split, h_right_split,
              h_left_split, h_arc_split,
              h_bot_left_r_decomp, h_bot_right_r_decomp, h_top_r_decomp,
              h_right_r_decomp, h_left_r_decomp, h_arc_r_decomp]
    _ = (((∑ᶠ u, MeromorphicOn.divisor g F u).toNat : ℂ)) := by
          have h_combine :
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
              Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
              Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
                    (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
              (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ)) *
                (2 * Real.pi * Complex.I) := by
            simp only [Finset.mul_sum]
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
                ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
                ← Finset.sum_sub_distrib, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro u hu
            have h := h_per_pole_eq u hu
            linear_combination (MeromorphicOn.divisor g F u : ℂ) * h
          rw [show
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                    h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                    h ((x : ℂ) + (e.im : ℂ) * Complex.I))) +
              Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
                (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
                    h ((b : ℂ) + (y : ℂ) * Complex.I))) -
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
                (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
                    h ((x : ℂ) + (d : ℂ) * Complex.I))) -
              Complex.I * ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
                (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
                    h ((a : ℂ) + (y : ℂ) * Complex.I))) -
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
                    (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) +
                (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
                  h (_root_.circleMap e R₀ θ) *
                  (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) =
              ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..(e.re - R₀), ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in (e.re + R₀)..b, ((x : ℂ) + (e.im : ℂ) * Complex.I - u)⁻¹)) +
                Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
                Complex.I * (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ y in e.im..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
                (∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ) *
                  (∫ θ in (0:ℝ)..Real.pi, (_root_.circleMap e R₀ θ - u)⁻¹ *
                    (Complex.I * R₀ * Complex.exp (Complex.I * θ))))) +
              ((∫ x in a..(e.re - R₀), deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                  h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
                (∫ x in (e.re + R₀)..b, deriv h ((x : ℂ) + (e.im : ℂ) * Complex.I) /
                  h ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
                Complex.I * (∫ y in e.im..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
                  h ((b : ℂ) + (y : ℂ) * Complex.I)) -
                (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
                  h ((x : ℂ) + (d : ℂ) * Complex.I)) -
                Complex.I * (∫ y in e.im..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
                  h ((a : ℂ) + (y : ℂ) * Complex.I)) -
                (∫ θ in (0:ℝ)..Real.pi, deriv h (_root_.circleMap e R₀ θ) /
                  h (_root_.circleMap e R₀ θ) *
                  (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) from by ring]
          rw [h_combine, h_h_sum_zero, add_zero]
          rw [mul_comm ((∑ u ∈ Dsupp, (MeromorphicOn.divisor g F u : ℂ))) (2 * Real.pi * Complex.I)]
          rw [inv_mul_cancel_left₀ hpi]
          exact h_finset_eq_finsum.trans (h_finsum_int_eq_nat.trans (by push_cast; rfl))


/-- **Argument principle on the truncated region (existential form).**
The `(2πi)⁻¹`-normalized boundary integral of `g'/g` is a non-negative
integer: the existential weakening of
`cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk`,
which identifies the integer as the divisor sum (total zero count with
multiplicity) of `g` on the region. -/
theorem cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (hg_bot_left : ∀ x ∈ Set.Icc a (e.re - R₀),
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_bot_right : ∀ x ∈ Set.Icc (e.re + R₀) b,
      g ((x : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc e.im d, g ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc e.im d, g ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_arc : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      g (_root_.circleMap e R₀ θ) ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      (∫ x in a..(e.re - R₀), deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      (∫ x in (e.re + R₀)..b, deriv g ((x : ℂ) + (e.im : ℂ) * Complex.I) /
        g ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
      Complex.I * (∫ y in e.im..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
        g ((b : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
        g ((x : ℂ) + (d : ℂ) * Complex.I)) -
      Complex.I * (∫ y in e.im..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
        g ((a : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ θ in (0 : ℝ)..Real.pi, deriv g (_root_.circleMap e R₀ θ) /
        g (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)))) = (n : ℂ) :=
  ⟨_, cIntegralLogDeriv_eq_divisor_sum_of_nonzero_on_rectMinusUpperHalfDisk
    g a b d e R₀ hab hR₀ h_a_lt h_lt_b h_e_im_R0_lt_d hg
    hg_bot_left hg_bot_right hg_top hg_right hg_left hg_arc⟩


/-- **Lower bound for the zero count.** If `g` vanishes at a point of
the truncated region (and is nonzero at the bottom-left corner, so its
orders are finite throughout), the total divisor sum is at least one. -/
theorem one_le_divisor_sum_toNat_of_zero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (h_corner_ne : g ((a : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    {z₀ : ℂ}
    (hz₀_mem : z₀ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₀_zero : g z₀ = 0) :
    1 ≤ (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b
      h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  -- The corner is in F and g does not vanish there, so all orders are finite.
  set z₁ : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hz₁_def
  have hz₁_re : z₁.re = a := by
    simp [hz₁_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₁_im : z₁.im = e.im := by
    simp [hz₁_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₁_in_F : z₁ ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hz₁_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hz₁_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (z₁ - e).re = a - e.re := by
        rw [Complex.sub_re, hz₁_re]
      have h_abs := Complex.abs_re_le_norm (z₁ - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hz₁_order_ne_top : meromorphicOrderAt g z₁ ≠ ⊤ := by
    rw [(hg z₁ hz₁_in_F).meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g z₁ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_corner_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ :=
    hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
      hz₁_in_F hz₀_mem hz₁_order_ne_top
  -- The divisor value at z₀ is at least 1.
  have hD_z₀ : 1 ≤ (MeromorphicOn.divisor g F) z₀ := by
    rw [MeromorphicOn.divisor_apply hg_mer hz₀_mem]
    rw [(hg z₀ hz₀_mem).meromorphicOrderAt_eq] at hz₀_order_ne_top ⊢
    have h_ord_ne_zero : analyticOrderAt g z₀ ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨hg z₀ hz₀_mem, by simpa using hz₀_zero⟩
    have h_ord_ne_top : analyticOrderAt g z₀ ≠ ⊤ := by
      intro h
      rw [h] at hz₀_order_ne_top
      simp at hz₀_order_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h1
      · exfalso; apply h_ord_ne_zero; rw [← hn, h0]; rfl
      · exact h1
    rw [← hn, ENat.map_coe]
    simp only [WithTop.untop₀_coe]
    exact_mod_cast hn_pos
  -- The total divisor sum dominates the single value at z₀.
  have h_single := single_le_finsum z₀
    (hdiv_finite : Function.HasFiniteSupport
      (⇑(MeromorphicOn.divisor g F)))
    (fun u => hD_nonneg u)
  have h_sum_ge : 1 ≤ ∑ᶠ u, (MeromorphicOn.divisor g F) u :=
    le_trans hD_z₀ h_single
  rw [Int.le_toNat (le_trans zero_le_one h_sum_ge)]
  exact_mod_cast h_sum_ge


/-- **Upper bound for the zero count.** If `z₀` is the only possible
zero of `g` on the truncated region and it is simple (nonvanishing
derivative), the total divisor sum is at most one. -/
theorem divisor_sum_toNat_le_one_of_unique_simple_zero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    {z₀ : ℂ}
    (h_unique : ∀ z ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀,
      g z = 0 → z = z₀)
    (h_simple : g z₀ = 0 → deriv g z₀ ≠ 0) :
    (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat ≤ 1 := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  -- The divisor vanishes away from z₀.
  have h_supp : ∀ z, z ≠ z₀ → (MeromorphicOn.divisor g F) z = 0 := by
    intro z hz_ne
    by_contra h_ne_zero
    have hz_in_F : z ∈ F :=
      (MeromorphicOn.divisor g F).supportWithinDomain
        (by simpa [Function.mem_support] using h_ne_zero)
    have hg_z_ne : g z ≠ 0 := fun h0 => hz_ne (h_unique z hz_in_F h0)
    apply h_ne_zero
    rw [MeromorphicOn.divisor_apply hg_mer hz_in_F,
      (hg z hz_in_F).meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr hg_z_ne)]
    simp
  have h_sum_eq : (∑ᶠ u, (MeromorphicOn.divisor g F) u) =
      (MeromorphicOn.divisor g F) z₀ :=
    finsum_eq_single _ z₀ h_supp
  rw [h_sum_eq]
  -- The divisor value at z₀ is at most 1.
  by_cases hz₀_in : z₀ ∈ F
  · by_cases hz₀_zero : g z₀ = 0
    · have h_ord : analyticOrderAt g z₀ = 1 :=
        (hg z₀ hz₀_in).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz₀_zero
          (h_simple hz₀_zero)
      rw [MeromorphicOn.divisor_apply hg_mer hz₀_in,
        (hg z₀ hz₀_in).meromorphicOrderAt_eq, h_ord,
        show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ENat.map_coe]
      rfl
    · rw [MeromorphicOn.divisor_apply hg_mer hz₀_in,
        (hg z₀ hz₀_in).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hz₀_zero)]
      simp
  · have h_zero : (MeromorphicOn.divisor g F) z₀ = 0 := by
      by_contra h_ne
      exact hz₀_in ((MeromorphicOn.divisor g F).supportWithinDomain
        (by simpa [Function.mem_support] using h_ne))
    rw [h_zero]
    simp


/-- **Two distinct zeros force a zero count of at least two.** If `g`
vanishes at two distinct points of the truncated region (and is nonzero
at the bottom-left corner), the total divisor sum is at least two. -/
theorem two_le_divisor_sum_toNat_of_two_zeros_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (h_corner_ne : g ((a : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    {z₀ z₁ : ℂ} (h_ne : z₀ ≠ z₁)
    (hz₀_mem : z₀ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₀_zero : g z₀ = 0)
    (hz₁_mem : z₁ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₁_zero : g z₁ = 0) :
    2 ≤ (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b
      h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  -- The corner is in F and g does not vanish there, so all orders are finite.
  set zc : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hzc_def
  have hzc_re : zc.re = a := by
    simp [hzc_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_im : zc.im = e.im := by
    simp [hzc_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_in_F : zc ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hzc_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hzc_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (zc - e).re = a - e.re := by
        rw [Complex.sub_re, hzc_re]
      have h_abs := Complex.abs_re_le_norm (zc - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hzc_order_ne_top : meromorphicOrderAt g zc ≠ ⊤ := by
    rw [(hg zc hzc_in_F).meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g zc = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_corner_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  -- Each of the two zeros has divisor value at least 1.
  have hD_ge_one : ∀ z ∈ F, g z = 0 → 1 ≤ (MeromorphicOn.divisor g F) z := by
    intro z hz_mem hz_zero
    have hz_order_ne_top : meromorphicOrderAt g z ≠ ⊤ :=
      hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
        hzc_in_F hz_mem hzc_order_ne_top
    rw [MeromorphicOn.divisor_apply hg_mer hz_mem]
    rw [(hg z hz_mem).meromorphicOrderAt_eq] at hz_order_ne_top ⊢
    have h_ord_ne_zero : analyticOrderAt g z ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨hg z hz_mem, by simpa using hz_zero⟩
    have h_ord_ne_top : analyticOrderAt g z ≠ ⊤ := by
      intro h
      rw [h] at hz_order_ne_top
      simp at hz_order_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h1
      · exfalso; apply h_ord_ne_zero; rw [← hn, h0]; rfl
      · exact h1
    rw [← hn, ENat.map_coe]
    simp only [WithTop.untop₀_coe]
    exact_mod_cast hn_pos
  -- Sum over the support dominates the two-point sum.
  have h_sum_repr : (∑ᶠ u, (MeromorphicOn.divisor g F) u) =
      ∑ u ∈ hdiv_finite.toFinset, (MeromorphicOn.divisor g F) u := by
    refine finsum_eq_sum_of_support_subset _ ?_
    rw [Set.Finite.coe_toFinset]
  have hz₀_supp : z₀ ∈ hdiv_finite.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have := hD_ge_one z₀ hz₀_mem hz₀_zero
    omega
  have hz₁_supp : z₁ ∈ hdiv_finite.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have := hD_ge_one z₁ hz₁_mem hz₁_zero
    omega
  have h_pair_le : ∑ u ∈ ({z₀, z₁} : Finset ℂ), (MeromorphicOn.divisor g F) u ≤
      ∑ u ∈ hdiv_finite.toFinset, (MeromorphicOn.divisor g F) u := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₀_supp
      · rw [Finset.mem_singleton.mp h]; exact hz₁_supp
    · intro u _ _
      exact hD_nonneg u
  have h_pair_sum : ∑ u ∈ ({z₀, z₁} : Finset ℂ), (MeromorphicOn.divisor g F) u =
      (MeromorphicOn.divisor g F) z₀ + (MeromorphicOn.divisor g F) z₁ :=
    Finset.sum_pair h_ne
  have h_two_le : 2 ≤ ∑ᶠ u, (MeromorphicOn.divisor g F) u := by
    rw [h_sum_repr]
    calc (2 : ℤ) ≤ (MeromorphicOn.divisor g F) z₀ + (MeromorphicOn.divisor g F) z₁ := by
          have h0 := hD_ge_one z₀ hz₀_mem hz₀_zero
          have h1 := hD_ge_one z₁ hz₁_mem hz₁_zero
          omega
      _ = ∑ u ∈ ({z₀, z₁} : Finset ℂ), (MeromorphicOn.divisor g F) u := h_pair_sum.symm
      _ ≤ _ := h_pair_le
  rw [Int.le_toNat (le_trans (by norm_num) h_two_le)]
  exact_mod_cast h_two_le


/-- **A double zero forces a zero count of at least two.** If `g` and
its derivative both vanish at a point of the truncated region (and `g`
is nonzero at the bottom-left corner), the total divisor sum is at
least two: the analytic order at the point is at least `2` by
`AnalyticAt.analyticOrderAt_deriv_add_one`. -/
theorem two_le_divisor_sum_toNat_of_double_zero_on_rectMinusUpperHalfDisk
    (g : ℂ → ℂ) (a b d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_e_im_R0_lt_d : e.im + R₀ < d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀))
    (h_corner_ne : g ((a : ℂ) + (e.im : ℂ) * Complex.I) ≠ 0)
    {z₀ : ℂ}
    (hz₀_mem : z₀ ∈ (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀)
    (hz₀_zero : g z₀ = 0) (hz₀_deriv : deriv g z₀ = 0) :
    2 ≤ (∑ᶠ u, MeromorphicOn.divisor g
      ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) u).toNat := by
  set F : Set ℂ := (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ with hF_def
  have hg_mer : MeromorphicOn g F := hg.meromorphicOn
  have hF_pathConnected : IsPathConnected F :=
    isPathConnected_rectMinusUpperHalfDisk a b d e R₀ hR₀ hab h_a_lt h_lt_b
      h_e_im_R0_lt_d
  have hF_preconn : IsPreconnected F := hF_pathConnected.isConnected.isPreconnected
  have hF_compact : IsCompact F :=
    (IsCompact.reProdIm isCompact_Icc isCompact_Icc).diff Metric.isOpen_ball
  have hdiv_finite : (MeromorphicOn.divisor g F).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hF_compact
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g F :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  set zc : ℂ := (a : ℂ) + (e.im : ℂ) * Complex.I with hzc_def
  have hzc_re : zc.re = a := by
    simp [hzc_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_im : zc.im = e.im := by
    simp [hzc_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hzc_in_F : zc ∈ F := by
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hzc_re, Set.mem_Icc]; exact ⟨le_refl _, hab.le⟩
      · rw [hzc_im, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩
    · rw [Metric.mem_ball, Complex.dist_eq]; push Not
      have h_re_diff : (zc - e).re = a - e.re := by
        rw [Complex.sub_re, hzc_re]
      have h_abs := Complex.abs_re_le_norm (zc - e)
      rw [h_re_diff, abs_of_neg (by linarith : a - e.re < 0)] at h_abs
      linarith
  have hzc_order_ne_top : meromorphicOrderAt g zc ≠ ⊤ := by
    rw [(hg zc hzc_in_F).meromorphicOrderAt_eq]
    intro h
    rw [ENat.map_eq_top_iff] at h
    have h0 : analyticOrderAt g zc = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr h_corner_ne)
    rw [h0] at h
    exact ENat.zero_ne_top h
  -- The double zero has divisor value at least 2.
  have hD_z₀ : 2 ≤ (MeromorphicOn.divisor g F) z₀ := by
    have hz_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ :=
      hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hF_preconn
        hzc_in_F hz₀_mem hzc_order_ne_top
    have h_an : AnalyticAt ℂ g z₀ := hg z₀ hz₀_mem
    -- analyticOrderAt g z₀ = analyticOrderAt (deriv g) z₀ + 1 ≥ 2.
    have h_key := h_an.analyticOrderAt_deriv_add_one
    have h_sub_eq : (fun x => g x - g z₀) = g := by
      funext x
      rw [hz₀_zero, sub_zero]
    rw [h_sub_eq] at h_key
    have h_deriv_ord_ne_zero : analyticOrderAt (deriv g) z₀ ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨h_an.deriv, by simpa using hz₀_deriv⟩
    have h_ord_ge_two : 2 ≤ analyticOrderAt g z₀ := by
      rw [← h_key]
      have h_one_le : 1 ≤ analyticOrderAt (deriv g) z₀ :=
        ENat.one_le_iff_ne_zero.mpr h_deriv_ord_ne_zero
      calc (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ analyticOrderAt (deriv g) z₀ + 1 :=
            add_le_add h_one_le (le_refl 1)
    rw [MeromorphicOn.divisor_apply hg_mer hz₀_mem]
    rw [(hg z₀ hz₀_mem).meromorphicOrderAt_eq] at hz_order_ne_top ⊢
    have h_ord_ne_top : analyticOrderAt g z₀ ≠ ⊤ := by
      intro h
      rw [h] at hz_order_ne_top
      simp at hz_order_ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h_ord_ne_top
    have hn_ge : 2 ≤ n := by
      rw [← hn] at h_ord_ge_two
      exact_mod_cast h_ord_ge_two
    rw [← hn, ENat.map_coe]
    simp only [WithTop.untop₀_coe]
    exact_mod_cast hn_ge
  have h_single := single_le_finsum z₀
    (hdiv_finite : Function.HasFiniteSupport
      (⇑(MeromorphicOn.divisor g F)))
    (fun u => hD_nonneg u)
  have h_sum_ge : 2 ≤ ∑ᶠ u, (MeromorphicOn.divisor g F) u :=
    le_trans hD_z₀ h_single
  rw [Int.le_toNat (le_trans (by norm_num) h_sum_ge)]
  exact_mod_cast h_sum_ge

end Complex
