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
  — CG on the top half of a rectangle-minus-disk annular region.
  Proved by 5-piece decomposition: 3 sub-rectangles (Mathlib's rect CG)
  plus the two top lunes, with shared edges cancelling and the lune arc
  contributions combining into the upper semicircle.
* `Complex.integral_boundary_bottomHalfAnnulus_eq_zero_of_differentiableOn`
  — CG on the bottom half-annulus. Proved by 180° rotation around `e`:
  the map `f̃(z) := f(2·e − z)` carries the bottom hypotheses into the
  top hypotheses, so the top half-annulus CG applied to `f̃` reduces
  (via `intervalIntegral.integral_comp_sub_left` for the axis edges and
  `intervalIntegral.integral_comp_add_right` plus `Complex.exp_pi_mul_I`
  for the arc) to the negative of the bottom identity.
* `Complex.integral_boundary_rectMinusDisk_eq_zero_of_differentiableOn`
  — CG on a full rectangle-minus-disk annular region. Obtained by
  cutting horizontally at `Im z = e.im` and adding the two
  half-annulus CGs (the cut contributions cancel).

## Argument-principle theorems

* `cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusDisk` — for `g`
  holomorphic on a neighborhood of a rectangle-minus-disk region and
  non-vanishing on its boundary, `(2πi)⁻¹ ∮_{∂(R \ D)} g'(z)/g(z) dz`
  is a non-negative integer counting zeros of `g` inside.
* Analogous circle and rectangle argument-principle theorems for the
  simpler closed-disk and closed-rectangle base cases.
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
`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn`: the top
half-annulus splits into three rectangles (closed under Mathlib's
`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`) plus
the two lunes. Shared edges cancel and the lune contributions provide the
upper semicircle integral.

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

/-- **Cauchy-Goursat for the top half of a rect-minus-disk annular region.**
For `f` continuous on the closed top half-annulus
`(Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀` and complex-
differentiable on its open interior, the contour integral around the top
half-annulus boundary equals zero.

The top half-annulus boundary, traversed counter-clockwise (annulus
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

The top half-annulus is simply-connected; Cauchy-Goursat for simply-
connected regions then gives zero. This is one of two helper lemmas
(top + bottom half-annulus CG) that together prove the full annular CG
`integral_boundary_rectMinusDisk_eq_zero_of_differentiableOn` via the
horizontal cut at `Im z = e.im`. -/
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

/-- **Cauchy-Goursat for the bottom half of a rect-minus-disk annular
region.** Mirror image of
`integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn`: for `f`
continuous on the closed bottom half-annulus and complex-differentiable
on its open interior, the contour integral around the bottom half-
annulus boundary equals zero.

The bottom half-annulus boundary, traversed CCW (interior on the left),
consists of:
* Bottom edge: `(a, c) → (b, c)`, contributing `∫_a^b f(x + c·i) dx`.
* Right edge: `(b, c) → (b, e.im)`, contributing
  `i·∫_c^{e.im} f(b + y·i) dy`.
* Top-right cut segment (reversed): `(b, e.im) → (e.re + R₀, e.im)`,
  contributing `−∫_{e.re+R₀}^b f(x + e.im·i) dx`.
* Lower semicircle (clockwise around the disk center, from
  `(e.re + R₀, e.im)` through `(e.re, e.im − R₀)` to
  `(e.re − R₀, e.im)`), contributing
  `−∫_π^{2π} f(circleMap e R₀ θ) · (i·R₀·exp(i·θ)) dθ`.
* Top-left cut segment (reversed): `(e.re − R₀, e.im) → (a, e.im)`,
  contributing `−∫_a^{e.re−R₀} f(x + e.im·i) dx`.
* Left edge (reversed): `(a, e.im) → (a, c)`, contributing
  `−i·∫_c^{e.im} f(a + y·i) dy`. -/
theorem integral_boundary_bottomHalfAnnulus_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (a b c : ℝ) (e : ℂ) (R₀ : ℝ)
    (_hab : a < b) (_h_c_e_im : c < e.im) (hR₀ : 0 < R₀)
    (h_a_lt : a < e.re - R₀) (h_lt_b : e.re + R₀ < b)
    (h_c_lt_e_im_R0 : c < e.im - R₀)
    (Hc : ContinuousOn f ((Set.Icc a b ×ℂ Set.Icc c e.im) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo c e.im) \ Metric.closedBall e R₀')) :
    (∫ x in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I)) -
    (∫ x in a..(e.re - R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I)) -
    (∫ x in (e.re + R₀)..b, f ((x : ℂ) + (e.im : ℂ) * Complex.I)) +
    Complex.I * (∫ y in c..e.im, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y in c..e.im, f ((a : ℂ) + (y : ℂ) * Complex.I)) -
    (∫ θ in (Real.pi:ℝ)..(2 * Real.pi), f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) = 0 := by
  -- Extract the underlying differentiability on the slightly enlarged set
  -- `(Ioo a b × Ioo c e.im) \ closedBall e R₀'` for some `R₀' < R₀`.
  obtain ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'⟩ := Hd
  -- Use 180° rotation around `e`: the map `g(z) := 2*e − z` is biholomorphic
  -- and maps the bottom half-annulus to the top half-annulus. Define
  -- `f̃(z) := f(g z) = f(2*e − z)` and apply the (already-proven) top
  -- half-annulus CG to `f̃`. Each integral of `f̃` transforms via
  -- `intervalIntegral.integral_comp_sub_left` (real-axis substitution
  -- `u = d − x`) back into an integral of `f`; the arc integral
  -- transforms via `intervalIntegral.integral_comp_add_right`
  -- (substitution `φ = θ + π`). The translated identity is the negative
  -- of the bottom half-annulus identity, which we close via
  -- `linear_combination`.
  set f_tilde : ℂ → ℂ := fun z => f (2 * e - z) with hf_tilde_def
  set a' : ℝ := 2 * e.re - b with ha'_def
  set b' : ℝ := 2 * e.re - a with hb'_def
  set d' : ℝ := 2 * e.im - c with hd'_def
  -- Parameter inequalities for the top half-annulus CG.
  have h_a'_lt_b' : a' < b' := by simp [ha'_def, hb'_def]; linarith
  have h_e_im_lt_d' : e.im < d' := by simp [hd'_def]; linarith
  have h_a'_lt : a' < e.re - R₀ := by simp [ha'_def]; linarith
  have h_lt_b' : e.re + R₀ < b' := by simp [hb'_def]; linarith
  have h_e_im_R0_lt_d' : e.im + R₀ < d' := by simp [hd'_def]; linarith
  -- The reflection map `g(z) := 2*e − z` is continuous and ℂ-differentiable.
  have h_g_cont : Continuous (fun z : ℂ => 2 * e - z) := by fun_prop
  have h_g_diff : Differentiable ℂ (fun z : ℂ => 2 * e - z) := by fun_prop
  -- `g` maps the top half-annulus's closed region to the bottom's
  -- (with `c, e.im` flipped via `2*e.im − ·`, and similarly for `x`).
  have h_maps_to_closed : Set.MapsTo (fun z : ℂ => 2 * e - z)
      ((Set.Icc a' b' ×ℂ Set.Icc e.im d') \ Metric.ball e R₀)
      ((Set.Icc a b ×ℂ Set.Icc c e.im) \ Metric.ball e R₀) := by
    intro z hz
    obtain ⟨hz_box, hz_not_ball⟩ := hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, ?_⟩
      · have h_re : (2 * e - z).re = 2 * e.re - z.re := by
          simp [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
        rw [h_re]
        rw [Set.mem_Icc] at hz_box ⊢
        refine ⟨?_, ?_⟩
        · linarith [hz_box.1.2, hb'_def]
        · linarith [hz_box.1.1, ha'_def]
      · have h_im : (2 * e - z).im = 2 * e.im - z.im := by
          simp [Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
        rw [h_im]
        rw [Set.mem_Icc] at hz_box ⊢
        refine ⟨?_, ?_⟩
        · linarith [hz_box.2.2, hd'_def]
        · linarith [hz_box.2.1]
    · intro h_ball
      apply hz_not_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball ⊢
      have h_eq : 2 * e - z - e = -(z - e) := by ring
      rw [h_eq, norm_neg] at h_ball
      exact h_ball
  -- Similarly for the open version (with `Ioo` and `closedBall`).
  have h_maps_to_open : Set.MapsTo (fun z : ℂ => 2 * e - z)
      ((Set.Ioo a' b' ×ℂ Set.Ioo e.im d') \ Metric.closedBall e R₀)
      ((Set.Ioo a b ×ℂ Set.Ioo c e.im) \ Metric.closedBall e R₀) := by
    intro z hz
    obtain ⟨hz_box, hz_not_cball⟩ := hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, ?_⟩
      · have h_re : (2 * e - z).re = 2 * e.re - z.re := by
          simp [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
        rw [h_re]
        rw [Set.mem_Ioo] at hz_box ⊢
        refine ⟨?_, ?_⟩
        · linarith [hz_box.1.2, hb'_def]
        · linarith [hz_box.1.1, ha'_def]
      · have h_im : (2 * e - z).im = 2 * e.im - z.im := by
          simp [Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
        rw [h_im]
        rw [Set.mem_Ioo] at hz_box ⊢
        refine ⟨?_, ?_⟩
        · linarith [hz_box.2.2, hd'_def]
        · linarith [hz_box.2.1]
    · intro h_cball
      apply hz_not_cball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_cball ⊢
      have h_eq : 2 * e - z - e = -(z - e) := by ring
      rw [h_eq, norm_neg] at h_cball
      exact h_cball
  -- R₀'-analog: reflection also maps the slightly enlarged top
  -- `(Ioo a' b' × Ioo e.im d') \ closedBall e R₀'` into the slightly enlarged
  -- bottom `(Ioo a b × Ioo c e.im) \ closedBall e R₀'`.
  have h_maps_to_open' : Set.MapsTo (fun z : ℂ => 2 * e - z)
      ((Set.Ioo a' b' ×ℂ Set.Ioo e.im d') \ Metric.closedBall e R₀')
      ((Set.Ioo a b ×ℂ Set.Ioo c e.im) \ Metric.closedBall e R₀') := by
    intro z hz
    obtain ⟨hz_box, hz_not_cball⟩ := hz
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm] at hz_box ⊢
      refine ⟨?_, ?_⟩
      · have h_re : (2 * e - z).re = 2 * e.re - z.re := by
          simp [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
        rw [h_re]
        rw [Set.mem_Ioo] at hz_box ⊢
        refine ⟨?_, ?_⟩
        · linarith [hz_box.1.2, hb'_def]
        · linarith [hz_box.1.1, ha'_def]
      · have h_im : (2 * e - z).im = 2 * e.im - z.im := by
          simp [Complex.sub_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
        rw [h_im]
        rw [Set.mem_Ioo] at hz_box ⊢
        refine ⟨?_, ?_⟩
        · linarith [hz_box.2.2, hd'_def]
        · linarith [hz_box.2.1]
    · intro h_cball
      apply hz_not_cball
      rw [Metric.mem_closedBall, dist_eq_norm] at h_cball ⊢
      have h_eq : 2 * e - z - e = -(z - e) := by ring
      rw [h_eq, norm_neg] at h_cball
      exact h_cball
  -- `f̃` satisfies the top half-annulus CG hypotheses on the box `[a', b'] × [e.im, d']`.
  have h_f_tilde_cont : ContinuousOn f_tilde
      ((Set.Icc a' b' ×ℂ Set.Icc e.im d') \ Metric.ball e R₀) :=
    Hc.comp h_g_cont.continuousOn h_maps_to_closed
  have h_f_tilde_diff' : DifferentiableOn ℂ f_tilde
      ((Set.Ioo a' b' ×ℂ Set.Ioo e.im d') \ Metric.closedBall e R₀') :=
    Hd'.comp h_g_diff.differentiableOn h_maps_to_open'
  -- Apply the top half-annulus CG to `f̃` (existential form).
  have h_top := integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn
    f_tilde a' b' d' e R₀ h_a'_lt_b' h_e_im_lt_d' hR₀ h_a'_lt h_lt_b' h_e_im_R0_lt_d'
    h_f_tilde_cont ⟨R₀', hR₀'_pos, hR₀'_lt, h_f_tilde_diff'⟩
  -- Now translate each `f̃` integral back to `f` via `integral_comp_sub_left`
  -- (real-axis substitution) and `integral_comp_add_right` (for the arc).
  -- The pointwise identity `f̃(x + y·I) = f((2*e.re − x) + (2*e.im − y)·I)`
  -- factors each substitution cleanly.
  -- Generic reflection identity: `2 * e - (x + y·I) = (2*e.re - x) + (2*e.im - y)·I`.
  -- Proven via `linear_combination` using `Complex.re_add_im e : (e.re : ℂ) + e.im·I = e`.
  have h_2e_minus : ∀ x y : ℝ,
      2 * e - ((x : ℂ) + (y : ℂ) * Complex.I) =
        ((2 * e.re - x : ℝ) : ℂ) + ((2 * e.im - y : ℝ) : ℂ) * Complex.I := by
    intro x y
    linear_combination (norm := (push_cast; ring)) -(2 : ℂ) * Complex.re_add_im e
  -- Reflection identity at fixed `y = e.im`:
  have h_refl_em : ∀ x : ℝ, f_tilde ((x : ℂ) + (e.im : ℂ) * Complex.I) =
      f (((2 * e.re - x : ℝ) : ℂ) + (e.im : ℂ) * Complex.I) := by
    intro x
    change f (2 * e - ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
         f (((2 * e.re - x : ℝ) : ℂ) + (e.im : ℂ) * Complex.I)
    rw [h_2e_minus]
    congr 1
    push_cast; ring
  -- Reflection identity at fixed `y = d' = 2*e.im - c`:
  have h_refl_d' : ∀ x : ℝ, f_tilde ((x : ℂ) + (d' : ℂ) * Complex.I) =
      f (((2 * e.re - x : ℝ) : ℂ) + (c : ℂ) * Complex.I) := by
    intro x
    change f (2 * e - ((x : ℂ) + (d' : ℂ) * Complex.I)) =
         f (((2 * e.re - x : ℝ) : ℂ) + (c : ℂ) * Complex.I)
    rw [h_2e_minus]
    congr 1
    rw [hd'_def]
    push_cast; ring
  -- Reflection identity at fixed `x = b' = 2*e.re - a`:
  have h_refl_b' : ∀ y : ℝ, f_tilde ((b' : ℂ) + (y : ℂ) * Complex.I) =
      f ((a : ℂ) + ((2 * e.im - y : ℝ) : ℂ) * Complex.I) := by
    intro y
    change f (2 * e - ((b' : ℂ) + (y : ℂ) * Complex.I)) =
         f ((a : ℂ) + ((2 * e.im - y : ℝ) : ℂ) * Complex.I)
    rw [h_2e_minus]
    congr 1
    rw [hb'_def]
    push_cast; ring
  -- Reflection identity at fixed `x = a' = 2*e.re - b`:
  have h_refl_a' : ∀ y : ℝ, f_tilde ((a' : ℂ) + (y : ℂ) * Complex.I) =
      f ((b : ℂ) + ((2 * e.im - y : ℝ) : ℂ) * Complex.I) := by
    intro y
    change f (2 * e - ((a' : ℂ) + (y : ℂ) * Complex.I)) =
         f ((b : ℂ) + ((2 * e.im - y : ℝ) : ℂ) * Complex.I)
    rw [h_2e_minus]
    congr 1
    rw [ha'_def]
    push_cast; ring
  -- Generic horizontal-strip substitution: ∫ x ∈ α..β, f̃(x + y₀·I) at fixed `y₀ = e.im`.
  have h_subst_em : ∀ (α β : ℝ),
      (∫ x in α..β, f_tilde ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        ∫ x in (2 * e.re - β)..(2 * e.re - α), f ((x : ℂ) + (e.im : ℂ) * Complex.I) := by
    intros α β
    rw [intervalIntegral.integral_congr (fun x _ => h_refl_em x)]
    exact intervalIntegral.integral_comp_sub_left
            (fun u : ℝ => f ((u : ℂ) + (e.im : ℂ) * Complex.I)) (2 * e.re)
  -- Generic horizontal-strip substitution at fixed `y = d' (= 2*e.im - c)`.
  have h_subst_d' : ∀ (α β : ℝ),
      (∫ x in α..β, f_tilde ((x : ℂ) + (d' : ℂ) * Complex.I)) =
        ∫ x in (2 * e.re - β)..(2 * e.re - α), f ((x : ℂ) + (c : ℂ) * Complex.I) := by
    intros α β
    rw [intervalIntegral.integral_congr (fun x _ => h_refl_d' x)]
    exact intervalIntegral.integral_comp_sub_left
            (fun u : ℝ => f ((u : ℂ) + (c : ℂ) * Complex.I)) (2 * e.re)
  -- Generic vertical-strip substitution at fixed `x = b' (= 2*e.re - a)`.
  have h_subst_b' : ∀ (α β : ℝ),
      (∫ y in α..β, f_tilde ((b' : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ y in (2 * e.im - β)..(2 * e.im - α), f ((a : ℂ) + (y : ℂ) * Complex.I) := by
    intros α β
    rw [intervalIntegral.integral_congr (fun y _ => h_refl_b' y)]
    exact intervalIntegral.integral_comp_sub_left
            (fun v : ℝ => f ((a : ℂ) + (v : ℂ) * Complex.I)) (2 * e.im)
  -- Generic vertical-strip substitution at fixed `x = a' (= 2*e.re - b)`.
  have h_subst_a' : ∀ (α β : ℝ),
      (∫ y in α..β, f_tilde ((a' : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ y in (2 * e.im - β)..(2 * e.im - α), f ((b : ℂ) + (y : ℂ) * Complex.I) := by
    intros α β
    rw [intervalIntegral.integral_congr (fun y _ => h_refl_a' y)]
    exact intervalIntegral.integral_comp_sub_left
            (fun v : ℝ => f ((b : ℂ) + (v : ℂ) * Complex.I)) (2 * e.im)
  -- Apply the generic substitutions to each `f̃-CG` term.
  have hT1 :
      (∫ x in a'..(e.re - R₀), f_tilde ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        ∫ x in (e.re + R₀)..b, f ((x : ℂ) + (e.im : ℂ) * Complex.I) := by
    rw [h_subst_em]
    congr 1
    · show 2 * e.re - (e.re - R₀) = e.re + R₀; ring
    · show 2 * e.re - a' = b; rw [ha'_def]; ring
  have hT2 :
      (∫ x in (e.re + R₀)..b', f_tilde ((x : ℂ) + (e.im : ℂ) * Complex.I)) =
        ∫ x in a..(e.re - R₀), f ((x : ℂ) + (e.im : ℂ) * Complex.I) := by
    rw [h_subst_em]
    congr 1
    · show 2 * e.re - b' = a; rw [hb'_def]; ring
    · show 2 * e.re - (e.re + R₀) = e.re - R₀; ring
  have hT3 :
      (∫ y in e.im..d', f_tilde ((b' : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ y in c..e.im, f ((a : ℂ) + (y : ℂ) * Complex.I) := by
    rw [h_subst_b']
    congr 1
    · show 2 * e.im - d' = c; rw [hd'_def]; ring
    · show 2 * e.im - e.im = e.im; ring
  have hT4 :
      (∫ x in a'..b', f_tilde ((x : ℂ) + (d' : ℂ) * Complex.I)) =
        ∫ x in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I) := by
    rw [h_subst_d']
    congr 1
    · show 2 * e.re - b' = a; rw [hb'_def]; ring
    · show 2 * e.re - a' = b; rw [ha'_def]; ring
  have hT5 :
      (∫ y in e.im..d', f_tilde ((a' : ℂ) + (y : ℂ) * Complex.I)) =
        ∫ y in c..e.im, f ((b : ℂ) + (y : ℂ) * Complex.I) := by
    rw [h_subst_a']
    congr 1
    · show 2 * e.im - d' = c; rw [hd'_def]; ring
    · show 2 * e.im - e.im = e.im; ring
  -- Arc substitution: the arc integral for `f̃` over `[0, π]` equals the
  -- *negative* of the arc integral for `f` over `[π, 2π]`. This uses
  -- `f̃(circleMap e R₀ θ) = f(circleMap e R₀ (θ + π))` and
  -- `exp(I·θ) = −exp(I·(θ + π))`.
  have h_refl_circleMap : ∀ θ : ℝ,
      f_tilde (_root_.circleMap e R₀ θ) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      -(f (_root_.circleMap e R₀ (θ + Real.pi)) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ)))) := by
    intro θ
    -- `exp(I·(θ + π)) = -exp(I·θ)` via `Complex.exp_pi_mul_I`.
    have h_exp_shift : Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ)) =
        -Complex.exp (Complex.I * (θ : ℂ)) := by
      have : Complex.I * (((θ + Real.pi : ℝ)) : ℂ) =
          Complex.I * (θ : ℂ) + (Real.pi : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    -- `2 * e - circleMap e R₀ θ = circleMap e R₀ (θ + π)`.
    have h_arg : 2 * e - _root_.circleMap e R₀ θ = _root_.circleMap e R₀ (θ + Real.pi) := by
      simp only [_root_.circleMap]
      have h_alt : Complex.exp ((((θ + Real.pi : ℝ)) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) * (-1) := by
        have h_eq : (((θ + Real.pi : ℝ)) : ℂ) * Complex.I =
            (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I := by push_cast; ring
        rw [h_eq, Complex.exp_add, Complex.exp_pi_mul_I]
      rw [h_alt]; ring
    change f (2 * e - _root_.circleMap e R₀ θ) * _ = _
    rw [h_arg, h_exp_shift]
    ring
  -- Generic arc substitution: ∫ over `[α, β]` of `f(circleMap (φ + π)) · (dz/dφ at φ + π)`
  -- equals ∫ over `[α + π, β + π]` of `f(circleMap φ) · (dz/dφ at φ)`.
  have h_subst_arc : ∀ (α β : ℝ),
      (∫ θ in α..β, f (_root_.circleMap e R₀ (θ + Real.pi)) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * ((θ + Real.pi : ℝ) : ℂ)))) =
        ∫ θ in (α + Real.pi)..(β + Real.pi), f (_root_.circleMap e R₀ θ) *
            (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    intros α β
    exact intervalIntegral.integral_comp_add_right
            (fun φ : ℝ => f (_root_.circleMap e R₀ φ) *
              (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (φ : ℂ))))
            Real.pi
  have hT6 :
      (∫ θ in (0:ℝ)..Real.pi, f_tilde (_root_.circleMap e R₀ θ) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        -∫ θ in (Real.pi:ℝ)..(2 * Real.pi), f (_root_.circleMap e R₀ θ) *
          (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    rw [intervalIntegral.integral_congr (fun θ _ => h_refl_circleMap θ)]
    rw [intervalIntegral.integral_neg]
    rw [h_subst_arc]
    congr 1
    congr 1
    · show (0 : ℝ) + Real.pi = Real.pi; ring
    · show Real.pi + Real.pi = 2 * Real.pi; ring
  -- The translated `f̃-CG` is exactly the negative of the bottom half-annulus
  -- goal. Substituting each `hT*` into `h_top` and negating yields the goal.
  linear_combination (norm := (push_cast; ring))
    -h_top + hT1 + hT2 + Complex.I * hT3 - hT4 - Complex.I * hT5 - hT6

/-- **Cauchy-Goursat for a rectangle minus a disk (annular region).** For
a function `f` continuous on the closed annular region
`(Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀` and complex-
differentiable on its open interior, the boundary integral around the
annulus (outer rectangle CCW minus inner circle CCW) equals zero.

The proof splits the annulus into two simply-connected halves via the
horizontal cut at `Im z = e.im`, applies the simply-connected Cauchy-
Goursat to each half (via `integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn`
and `integral_boundary_bottomHalfAnnulus_eq_zero_of_differentiableOn`),
and observes the cut contributions cancel.

This is the rectangle-minus-disk analog of
`Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
(Mathlib's CG for circular annuli) and complements
`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
(Mathlib's CG for rectangles). -/
theorem integral_boundary_rectMinusDisk_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (a b c d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (_hcd : c < d) (hR₀ : 0 < R₀)
    (hdisk_in_rect : Metric.closedBall e R₀ ⊆ Set.Ioo a b ×ℂ Set.Ioo c d)
    (Hc : ContinuousOn f ((Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀))
    (Hd : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧ DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo c d) \ Metric.closedBall e R₀')) :
    ((∫ x in a..b, f ((x : ℂ) + (c : ℂ) * Complex.I)) +
      Complex.I * (∫ y in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      (∫ x in a..b, f ((x : ℂ) + (d : ℂ) * Complex.I)) -
      Complex.I * (∫ y in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I))) -
    (∮ z in C(e, R₀), f z) = 0 := by
  -- Extract the geometric constraints (a < e.re - R₀, e.re + R₀ < b,
  -- c < e.im - R₀, e.im + R₀ < d) from `hdisk_in_rect`. Each follows
  -- from `hdisk_in_rect` applied to a specific extreme point on the
  -- sphere `|z − e| = R₀`.
  have h_a_lt_e_re_R0 : a < e.re - R₀ := by
    have h_pt : (e - (R₀ : ℂ)) ∈ Metric.closedBall e R₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm,
          show e - (R₀ : ℂ) - e = -(R₀ : ℂ) from by ring, norm_neg,
          Complex.norm_real, Real.norm_of_nonneg hR₀.le]
    have h_in := hdisk_in_rect h_pt
    rw [Complex.mem_reProdIm] at h_in
    have h_re : (e - (R₀ : ℂ)).re = e.re - R₀ := by
      simp [Complex.sub_re, Complex.ofReal_re]
    rw [h_re] at h_in
    exact h_in.1.1
  have h_e_re_R0_lt_b : e.re + R₀ < b := by
    have h_pt : (e + (R₀ : ℂ)) ∈ Metric.closedBall e R₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm,
          show e + (R₀ : ℂ) - e = (R₀ : ℂ) from by ring,
          Complex.norm_real, Real.norm_of_nonneg hR₀.le]
    have h_in := hdisk_in_rect h_pt
    rw [Complex.mem_reProdIm] at h_in
    have h_re : (e + (R₀ : ℂ)).re = e.re + R₀ := by
      simp [Complex.add_re, Complex.ofReal_re]
    rw [h_re] at h_in
    exact h_in.1.2
  have h_c_lt_e_im_R0 : c < e.im - R₀ := by
    have h_pt : (e - (R₀ : ℂ) * Complex.I) ∈ Metric.closedBall e R₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm,
          show e - (R₀ : ℂ) * Complex.I - e = -((R₀ : ℂ) * Complex.I) from by ring,
          norm_neg, Complex.norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hR₀.le, Complex.norm_I, mul_one]
    have h_in := hdisk_in_rect h_pt
    rw [Complex.mem_reProdIm] at h_in
    have h_im : (e - (R₀ : ℂ) * Complex.I).im = e.im - R₀ := by
      simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [h_im] at h_in
    exact h_in.2.1
  have h_e_im_R0_lt_d : e.im + R₀ < d := by
    have h_pt : (e + (R₀ : ℂ) * Complex.I) ∈ Metric.closedBall e R₀ := by
      rw [Metric.mem_closedBall, dist_eq_norm,
          show e + (R₀ : ℂ) * Complex.I - e = (R₀ : ℂ) * Complex.I from by ring,
          Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hR₀.le,
          Complex.norm_I, mul_one]
    have h_in := hdisk_in_rect h_pt
    rw [Complex.mem_reProdIm] at h_in
    have h_im : (e + (R₀ : ℂ) * Complex.I).im = e.im + R₀ := by
      simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [h_im] at h_in
    exact h_in.2.2
  -- Extract continuity/differentiability hypotheses for the two halves.
  have h_top_subset : (Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀ ⊆
      (Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀ := by
    rintro z ⟨h_rect, h_not_ball⟩
    refine ⟨?_, h_not_ball⟩
    rw [Complex.mem_reProdIm] at h_rect ⊢
    refine ⟨h_rect.1, ?_⟩
    rw [Set.mem_Icc] at h_rect ⊢
    refine ⟨?_, h_rect.2.2⟩
    linarith [h_rect.2.1, h_c_lt_e_im_R0]
  have h_bot_subset : (Set.Icc a b ×ℂ Set.Icc c e.im) \ Metric.ball e R₀ ⊆
      (Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀ := by
    rintro z ⟨h_rect, h_not_ball⟩
    refine ⟨?_, h_not_ball⟩
    rw [Complex.mem_reProdIm] at h_rect ⊢
    refine ⟨h_rect.1, ?_⟩
    rw [Set.mem_Icc] at h_rect ⊢
    refine ⟨h_rect.2.1, ?_⟩
    linarith [h_rect.2.2, h_e_im_R0_lt_d]
  have Hc_top : ContinuousOn f ((Set.Icc a b ×ℂ Set.Icc e.im d) \ Metric.ball e R₀) :=
    Hc.mono h_top_subset
  have Hc_bot : ContinuousOn f ((Set.Icc a b ×ℂ Set.Icc c e.im) \ Metric.ball e R₀) :=
    Hc.mono h_bot_subset
  -- Extract the R₀'-witnessed differentiability from the existential `Hd`.
  obtain ⟨R₀', hR₀'_pos, hR₀'_lt, Hd'⟩ := Hd
  have h_top_subset_open' : (Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀' ⊆
      (Set.Ioo a b ×ℂ Set.Ioo c d) \ Metric.closedBall e R₀' := by
    rintro z ⟨h_rect, h_not_ball⟩
    refine ⟨?_, h_not_ball⟩
    rw [Complex.mem_reProdIm] at h_rect ⊢
    refine ⟨h_rect.1, ?_⟩
    rw [Set.mem_Ioo] at h_rect ⊢
    refine ⟨?_, h_rect.2.2⟩
    linarith [h_rect.2.1, h_c_lt_e_im_R0]
  have h_bot_subset_open' : (Set.Ioo a b ×ℂ Set.Ioo c e.im) \ Metric.closedBall e R₀' ⊆
      (Set.Ioo a b ×ℂ Set.Ioo c d) \ Metric.closedBall e R₀' := by
    rintro z ⟨h_rect, h_not_ball⟩
    refine ⟨?_, h_not_ball⟩
    rw [Complex.mem_reProdIm] at h_rect ⊢
    refine ⟨h_rect.1, ?_⟩
    rw [Set.mem_Ioo] at h_rect ⊢
    refine ⟨h_rect.2.1, ?_⟩
    linarith [h_rect.2.2, h_e_im_R0_lt_d]
  have Hd_top' : DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo e.im d) \ Metric.closedBall e R₀') :=
    Hd'.mono h_top_subset_open'
  have Hd_bot' : DifferentiableOn ℂ f
      ((Set.Ioo a b ×ℂ Set.Ioo c e.im) \ Metric.closedBall e R₀') :=
    Hd'.mono h_bot_subset_open'
  -- Get the two half-annulus CG results (existential form for `Hd`).
  have h_e_im_lt_d : e.im < d := by linarith
  have h_c_lt_e_im : c < e.im := by linarith
  have hT := integral_boundary_topHalfAnnulus_eq_zero_of_differentiableOn
    f a b d e R₀ hab h_e_im_lt_d hR₀ h_a_lt_e_re_R0 h_e_re_R0_lt_b h_e_im_R0_lt_d Hc_top
    ⟨R₀', hR₀'_pos, hR₀'_lt, Hd_top'⟩
  have hB := integral_boundary_bottomHalfAnnulus_eq_zero_of_differentiableOn
    f a b c e R₀ hab h_c_lt_e_im hR₀ h_a_lt_e_re_R0 h_e_re_R0_lt_b h_c_lt_e_im_R0 Hc_bot
    ⟨R₀', hR₀'_pos, hR₀'_lt, Hd_bot'⟩
  -- Aggregate T + B = 0: cuts at `y = e.im` cancel, the right/left edges
  -- concatenate via `intervalIntegral.integral_add_adjacent_intervals`, and
  -- the two semicircular arcs `0..π` and `π..2π` combine into the full
  -- `circleIntegral` (over `0..2π`).
  -- Local abbreviations for the closed annulus.
  set R_ann : Set ℂ := (Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀ with hR_ann_def
  -- Step 1: edge / arc points lie in `R_ann`, so `f` is continuous there.
  have h_right_in_R_ann : ∀ y, y ∈ Set.Icc c d →
      ((b : ℂ) + (y : ℂ) * Complex.I) ∈ R_ann := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show ((b : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
        have h_re : ((b : ℂ) + (y : ℂ) * Complex.I).re = b := by
          simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        rw [h_re]; exact Set.right_mem_Icc.mpr hab.le
      · show ((b : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc c d
        have h_im : ((b : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        rw [h_im]; exact hy
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      have h_re_eq : ((b : ℂ) + (y : ℂ) * Complex.I - e).re = b - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have h_norm_ge_re : |((b : ℂ) + (y : ℂ) * Complex.I - e).re| ≤
          ‖((b : ℂ) + (y : ℂ) * Complex.I) - e‖ := abs_re_le_norm _
      rw [h_re_eq, abs_of_pos (by linarith : (0:ℝ) < b - e.re)] at h_norm_ge_re
      linarith
  have h_left_in_R_ann : ∀ y, y ∈ Set.Icc c d →
      ((a : ℂ) + (y : ℂ) * Complex.I) ∈ R_ann := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show ((a : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.Icc a b
        have h_re : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
          simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        rw [h_re]; exact Set.left_mem_Icc.mpr hab.le
      · show ((a : ℂ) + (y : ℂ) * Complex.I).im ∈ Set.Icc c d
        have h_im : ((a : ℂ) + (y : ℂ) * Complex.I).im = y := by
          simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]
        rw [h_im]; exact hy
    · intro h_ball
      rw [Metric.mem_ball, dist_eq_norm] at h_ball
      have h_re_eq : ((a : ℂ) + (y : ℂ) * Complex.I - e).re = a - e.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have h_norm_ge_re : |((a : ℂ) + (y : ℂ) * Complex.I - e).re| ≤
          ‖((a : ℂ) + (y : ℂ) * Complex.I) - e‖ := abs_re_le_norm _
      rw [h_re_eq] at h_norm_ge_re
      have h_abs : |a - e.re| = e.re - a := by
        rw [abs_of_neg (by linarith : a - e.re < 0)]; linarith
      rw [h_abs] at h_norm_ge_re
      linarith
  have h_sphere_in_R_ann : ∀ θ : ℝ, _root_.circleMap e R₀ θ ∈ R_ann := by
    intro θ
    have h_sphere : _root_.circleMap e R₀ θ ∈ Metric.sphere e R₀ :=
      _root_.circleMap_mem_sphere e hR₀.le θ
    have h_cb : _root_.circleMap e R₀ θ ∈ Metric.closedBall e R₀ :=
      Metric.sphere_subset_closedBall h_sphere
    refine ⟨?_, ?_⟩
    · have h_in_open := hdisk_in_rect h_cb
      rw [Complex.mem_reProdIm]
      rw [Complex.mem_reProdIm] at h_in_open
      exact ⟨Set.Ioo_subset_Icc_self h_in_open.1, Set.Ioo_subset_Icc_self h_in_open.2⟩
    · intro hb_mem
      rw [Metric.mem_sphere] at h_sphere
      rw [Metric.mem_ball] at hb_mem
      linarith
  -- Step 2: continuity of edge integrands on `[c, d]`.
  have h_right_map_cont : Continuous (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I) := by
    fun_prop
  have h_left_map_cont : Continuous (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) := by
    fun_prop
  have h_right_cont : ContinuousOn (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc c d) :=
    Hc.comp h_right_map_cont.continuousOn (fun y hy => h_right_in_R_ann y hy)
  have h_left_cont : ContinuousOn (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc c d) :=
    Hc.comp h_left_map_cont.continuousOn (fun y hy => h_left_in_R_ann y hy)
  -- Step 3: arc integrand is globally continuous (since `circleMap e R₀` maps into R_ann).
  have h_arc_cont : Continuous (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
      (Complex.I * R₀ * Complex.exp (Complex.I * θ))) := by
    refine Continuous.mul ?_ ?_
    · exact Hc.comp_continuous (continuous_circleMap _ _) (fun θ => h_sphere_in_R_ann θ)
    · fun_prop
  -- Step 4: split each edge / arc integral at the midpoint.
  have h_right_int_c_eim : IntervalIntegrable
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume c e.im := by
    refine (h_right_cont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le h_c_lt_e_im.le]
    exact Set.Icc_subset_Icc le_rfl h_e_im_lt_d.le
  have h_right_int_eim_d : IntervalIntegrable
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume e.im d := by
    refine (h_right_cont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le h_e_im_lt_d.le]
    exact Set.Icc_subset_Icc h_c_lt_e_im.le le_rfl
  have h_right_split :
      (∫ y in c..e.im, f ((b : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in e.im..d, f ((b : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in c..d, f ((b : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_right_int_c_eim h_right_int_eim_d
  have h_left_int_c_eim : IntervalIntegrable
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume c e.im := by
    refine (h_left_cont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le h_c_lt_e_im.le]
    exact Set.Icc_subset_Icc le_rfl h_e_im_lt_d.le
  have h_left_int_eim_d : IntervalIntegrable
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume e.im d := by
    refine (h_left_cont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le h_e_im_lt_d.le]
    exact Set.Icc_subset_Icc h_c_lt_e_im.le le_rfl
  have h_left_split :
      (∫ y in c..e.im, f ((a : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in e.im..d, f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in c..d, f ((a : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_add_adjacent_intervals h_left_int_c_eim h_left_int_eim_d
  have h_arc_int_0_pi : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) MeasureTheory.volume 0 Real.pi :=
    h_arc_cont.intervalIntegrable _ _
  have h_arc_int_pi_2pi : IntervalIntegrable
      (fun θ : ℝ => f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) MeasureTheory.volume
        Real.pi (2 * Real.pi) :=
    h_arc_cont.intervalIntegrable _ _
  have h_arc_split :
      (∫ θ in (0:ℝ)..Real.pi, f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) +
      (∫ θ in (Real.pi:ℝ)..(2 * Real.pi), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ))) =
      ∫ θ in (0:ℝ)..(2 * Real.pi), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) :=
    intervalIntegral.integral_add_adjacent_intervals h_arc_int_0_pi h_arc_int_pi_2pi
  -- Step 5: rewrite `∮ z in C(e, R₀), f z` to the arc-integral form.
  have h_circ_form : (∮ z in C(e, R₀), f z) =
      ∫ θ in (0:ℝ)..(2 * Real.pi), f (_root_.circleMap e R₀ θ) *
        (Complex.I * R₀ * Complex.exp (Complex.I * θ)) := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    change deriv (_root_.circleMap e R₀) θ • f (_root_.circleMap e R₀ θ) =
      f (_root_.circleMap e R₀ θ) *
        (Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    rw [deriv_circleMap, smul_eq_mul]
    have key : _root_.circleMap 0 R₀ θ * Complex.I =
        Complex.I * (R₀ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      unfold _root_.circleMap
      ring_nf
    linear_combination f (_root_.circleMap e R₀ θ) * key
  -- Step 6: T + B = 0 combined with the three splits gives the annular CG.
  linear_combination hT + hB - Complex.I * h_right_split + Complex.I * h_left_split +
    h_arc_split - h_circ_form

/-- **Path-connectedness of a closed rectangle minus an open disk.** When
the closed ball `closedBall e R₀` is strictly inside the open rectangle
`Set.Ioo a b ×ℂ Set.Ioo c d`, the annular region
`(Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀` is path-connected.

Proof sketch: every point `p` of the annulus is connected to the sphere
`|z − e| = R₀` via the radial segment `[p, e + R₀ * (p − e) / |p − e|]`
(which stays in the annulus since `|p − e| ≥ R₀` everywhere on the
segment); the sphere is itself path-connected (via `Complex.circleMap`).
Hence any two annular points are connected through a sphere intermediary. -/
theorem isPathConnected_rectMinusDisk
    (a b c d : ℝ) (e : ℂ) (R₀ : ℝ)
    (_hab : a < b) (_hcd : c < d) (hR₀ : 0 < R₀)
    (hdisk_in_rect : Metric.closedBall e R₀ ⊆ Set.Ioo a b ×ℂ Set.Ioo c d) :
    IsPathConnected ((Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀) := by
  set R_ann : Set ℂ := (Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀ with hR_ann_def
  -- Sphere is a subset of R_ann.
  have hsphere_subset : Metric.sphere e R₀ ⊆ R_ann := by
    intro z hz
    have hz_cb : z ∈ Metric.closedBall e R₀ := Metric.sphere_subset_closedBall hz
    refine ⟨?_, ?_⟩
    · have := hdisk_in_rect hz_cb
      rw [Complex.mem_reProdIm] at this ⊢
      exact ⟨Set.Ioo_subset_Icc_self this.1, Set.Ioo_subset_Icc_self this.2⟩
    · intro hb
      rw [Metric.mem_sphere] at hz; rw [Metric.mem_ball] at hb; linarith
  -- Sphere is path-connected via `isPathConnected_sphere` (rank ℂ as ℝ-module is 2 > 1).
  have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [_root_.Complex.rank_real_complex]
    exact_mod_cast (by norm_num : 1 < 2)
  have hsphere_pathconn : IsPathConnected (Metric.sphere e R₀) :=
    isPathConnected_sphere h_rank e hR₀.le
  -- Closed rectangle is convex.
  have hrect_convex : Convex ℝ ((Set.Icc a b ×ℂ Set.Icc c d) : Set ℂ) := by
    intro x hx y hy s t hs ht hst
    rw [Complex.mem_reProdIm] at hx hy ⊢
    refine ⟨?_, ?_⟩
    · have h_re_eq : (s • x + t • y).re = s * x.re + t * y.re := by simp [Complex.add_re]
      rw [h_re_eq]; exact convex_Icc a b hx.1 hy.1 hs ht hst
    · have h_im_eq : (s • x + t • y).im = s * x.im + t * y.im := by simp [Complex.add_im]
      rw [h_im_eq]; exact convex_Icc c d hx.2 hy.2 hs ht hst
  set p₀ : ℂ := _root_.circleMap e R₀ 0 with hp₀_def
  have hp₀_sphere : p₀ ∈ Metric.sphere e R₀ :=
    _root_.circleMap_mem_sphere e hR₀.le 0
  have hp₀_in_R_ann : p₀ ∈ R_ann := hsphere_subset hp₀_sphere
  refine ⟨p₀, hp₀_in_R_ann, ?_⟩
  intro q hq
  obtain ⟨hq_rect, hq_not_ball⟩ := hq
  rw [Metric.mem_ball, not_lt] at hq_not_ball
  have hq_dist_pos : 0 < dist q e := lt_of_lt_of_le hR₀ hq_not_ball
  -- Sphere projection scale k₀.
  set k₀ : ℝ := R₀ / dist q e with hk₀_def
  have hk₀_pos : 0 < k₀ := div_pos hR₀ hq_dist_pos
  set π_q : ℂ := e + k₀ • (q - e) with hπq_def
  have h_q_sub_e_norm : ‖q - e‖ = dist q e := (dist_eq_norm q e).symm
  -- π_q ∈ sphere.
  have hπq_sphere : π_q ∈ Metric.sphere e R₀ := by
    rw [Metric.mem_sphere, dist_eq_norm]
    have h_sub : π_q - e = (k₀ : ℂ) * (q - e) := by
      rw [hπq_def, Complex.real_smul]; ring
    rw [h_sub, Complex.norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hk₀_pos.le, h_q_sub_e_norm, hk₀_def]
    field_simp
  have hπq_in_R_ann : π_q ∈ R_ann := hsphere_subset hπq_sphere
  -- Segment from π_q to q lies in R_ann.
  have hseg_subset : segment ℝ π_q q ⊆ R_ann := by
    rintro z ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hrect_convex hπq_in_R_ann.1 hq_rect hs ht hst
    · intro hz_ball
      rw [Metric.mem_ball] at hz_ball
      -- Compute the algebraic identity z - e = (s * k₀ + t) * (q - e).
      have hst_c : (s : ℂ) + (t : ℂ) = 1 := by
        rw [← Complex.ofReal_add, hst]; simp
      have h_z_sub_e : (s • π_q + t • q) - e = ((s * k₀ + t : ℝ) : ℂ) * (q - e) := by
        rw [hπq_def, Complex.real_smul, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination e * hst_c
      rw [dist_eq_norm, h_z_sub_e, Complex.norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ s * k₀ + t),
          h_q_sub_e_norm] at hz_ball
      -- Substitute k₀ and simplify.
      have h_dist_eq : (s * k₀ + t) * dist q e = s * R₀ + t * dist q e := by
        rw [hk₀_def]; field_simp
      rw [h_dist_eq] at hz_ball
      have h_t_ineq : t * R₀ ≤ t * dist q e :=
        mul_le_mul_of_nonneg_left hq_not_ball ht
      have h_sum : s * R₀ + t * R₀ = R₀ := by rw [← add_mul, hst, one_mul]
      linarith
  -- JoinedIn segment π_q q via convexity + path-connectedness.
  have hjoin_πq_q_seg : JoinedIn (segment ℝ π_q q) π_q q :=
    IsPathConnected.joinedIn
      ((convex_segment π_q q).isPathConnected ⟨π_q, left_mem_segment _ _ _⟩)
      π_q (left_mem_segment _ _ _) q (right_mem_segment _ _ _)
  have hjoin_πq_q : JoinedIn R_ann π_q q := hjoin_πq_q_seg.mono hseg_subset
  -- Sphere connects p₀ to π_q; lift to R_ann.
  have hjoin_p₀_πq : JoinedIn R_ann p₀ π_q :=
    (IsPathConnected.joinedIn hsphere_pathconn p₀ hp₀_sphere π_q
      hπq_sphere).mono hsphere_subset
  exact hjoin_p₀_πq.trans hjoin_πq_q

set_option maxHeartbeats 400000 in
-- The proof clones the Weierstrass-factorization structure of
-- `cIntegralLogDeriv_isNat_of_nonzero_on_rectBoundary` over the annular
-- region (closed rectangle minus open ball), applying `rectBoundary` and
-- `circle AP` to the rational factor `r` and annular Cauchy-Goursat to the
-- analytic non-vanishing factor `h`. The combined elaboration pressure
-- (codiscrete + AccPt + 4 edge-membership + sphere-membership +
-- divisor-support strict-interior analysis) exceeds the default limit.
/-- **Argument principle on a rectangle with a circular hole.** For a
function `g` analytic on a neighborhood of the closed region
`R := (Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀` (a closed
rectangle with an open disk removed), with `g` non-vanishing on the
rectangle boundary AND on the sphere `|z − e| = R₀`, the contour
integral around `∂R` (outer rectangle CCW minus inner circle CCW) is
`2πi` times the count of zeros of `g` inside `R`. This is the additive
combination of the rectangle and circle argument principles, used for
counting preimages in regions where a "bite" of a half-disk has been
removed (e.g., the truncated `Γ(2)` fundamental domain). -/
theorem cIntegralLogDeriv_isNat_of_nonzero_on_rectMinusDisk
    (g : ℂ → ℂ) (a b c d : ℝ) (e : ℂ) (R₀ : ℝ)
    (hab : a < b) (hcd : c < d) (hR₀ : 0 < R₀)
    (hdisk_in_rect : Metric.closedBall e R₀ ⊆ Set.Ioo a b ×ℂ Set.Ioo c d)
    (hg : AnalyticOnNhd ℂ g
      ((Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀))
    (hg_bot : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0)
    (hg_top : ∀ x ∈ Set.Icc a b, g ((x : ℂ) + (d : ℂ) * Complex.I) ≠ 0)
    (hg_right : ∀ y ∈ Set.Icc c d, g ((b : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_left : ∀ y ∈ Set.Icc c d, g ((a : ℂ) + (y : ℂ) * Complex.I) ≠ 0)
    (hg_sphere : ∀ z ∈ Metric.sphere e R₀, g z ≠ 0) :
    ∃ n : ℕ, (2 * Real.pi * Complex.I)⁻¹ * (
      ((∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * Complex.I) /
        g ((x : ℂ) + (c : ℂ) * Complex.I)) +
       Complex.I * (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
        g ((b : ℂ) + (y : ℂ) * Complex.I)) -
       (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
        g ((x : ℂ) + (d : ℂ) * Complex.I)) -
       Complex.I * (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
        g ((a : ℂ) + (y : ℂ) * Complex.I))) -
      (∮ z in C(e, R₀), deriv g z / g z)) = (n : ℂ) := by
  -- Annular region R_ann := closed rect \ open ball.
  set R_ann : Set ℂ := (Set.Icc a b ×ℂ Set.Icc c d) \ Metric.ball e R₀ with hR_ann_def
  set R : Set ℂ := Set.Icc a b ×ℂ Set.Icc c d with hR_def
  have hg_mer : MeromorphicOn g R_ann := hg.meromorphicOn
  -- R_ann is preconnected (via the helper) and compact.
  have hR_ann_preconn : IsPreconnected R_ann :=
    ((isPathConnected_rectMinusDisk a b c d e R₀ hab hcd hR₀
      hdisk_in_rect).isConnected).isPreconnected
  have hR_ann_compact : IsCompact R_ann := by
    refine IsCompact.diff ?_ Metric.isOpen_ball
    exact IsCompact.reProdIm isCompact_Icc isCompact_Icc
  -- Witness corner z₀ = (a, c). In R_ann since rect corner is in closed rect
  -- and outside closed ball (by hdisk_in_rect: closed ball ⊆ open rect).
  set z₀ : ℂ := (a : ℂ) + (c : ℂ) * Complex.I with hz₀_def
  have hz₀_re : z₀.re = a := by
    simp [hz₀_def, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_im : z₀.im = c := by
    simp [hz₀_def, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
  have hz₀_in_rect : z₀ ∈ R := by
    rw [hR_def, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [hz₀_re]; exact Set.left_mem_Icc.mpr hab.le
    · rw [hz₀_im]; exact Set.left_mem_Icc.mpr hcd.le
  have hz₀_not_in_ball : z₀ ∉ Metric.ball e R₀ := by
    intro h
    have h_cb : z₀ ∈ Metric.closedBall e R₀ := Metric.ball_subset_closedBall h
    have h_in_open := hdisk_in_rect h_cb
    rw [Complex.mem_reProdIm] at h_in_open
    obtain ⟨h_re, _⟩ := h_in_open
    rw [hz₀_re, Set.mem_Ioo] at h_re
    linarith [h_re.1]
  have hz₀_in_R_ann : z₀ ∈ R_ann := ⟨hz₀_in_rect, hz₀_not_in_ball⟩
  have hz₀_g_ne : g z₀ ≠ 0 := hg_bot a (Set.left_mem_Icc.mpr hab.le)
  have hz₀_analytic : AnalyticAt ℂ g z₀ := hg z₀ hz₀_in_R_ann
  -- meromorphicOrderAt g z₀ ≠ ⊤.
  have hz₀_order_ne_top : meromorphicOrderAt g z₀ ≠ ⊤ := by
    rw [hz₀_analytic.meromorphicOrderAt_eq]
    intro h_top
    rw [ENat.map_eq_top_iff] at h_top
    have h0 : analyticOrderAt g z₀ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hz₀_g_ne)
    rw [h0] at h_top
    exact ENat.zero_ne_top h_top
  -- Spread via preconnectedness.
  have hg_order : ∀ u ∈ R_ann, meromorphicOrderAt g u ≠ ⊤ := by
    intro u hu
    exact hg_mer.meromorphicOrderAt_ne_top_of_isPreconnected hR_ann_preconn
      hz₀_in_R_ann hu hz₀_order_ne_top
  -- Divisor finite (compactness).
  have hdiv_finite : (MeromorphicOn.divisor g R_ann).support.Finite :=
    Function.locallyFinsuppWithin.finiteSupport _ hR_ann_compact
  -- Extract zeros and poles: g = r · h codiscretely on R_ann.
  obtain ⟨h, h_analytic, h_nonzero, h_factor⟩ :=
    hg_mer.extract_zeros_poles
      (fun u : R_ann => hg_order u.1 u.2)
      hdiv_finite
  -- Divisor is non-negative (g analytic).
  have hD_nonneg : 0 ≤ MeromorphicOn.divisor g R_ann :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg
  -- r := ∏ᶠ u, (·-u)^(D u). Globally analytic.
  set r : ℂ → ℂ :=
    ∏ᶠ u, (· - u) ^ ((MeromorphicOn.divisor g R_ann) u) with hr_def
  have hr_analytic : ∀ z, AnalyticAt ℂ r z := fun z =>
    Function.FactorizedRational.analyticAt (hD_nonneg z)
  -- R_ann is non-trivial (has 2 distinct points).
  have hR_ann_ntriv : R_ann.Nontrivial := by
    refine ⟨z₀, hz₀_in_R_ann, (b : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · -- (b, d) is the opposite corner, also in R_ann.
      have hbd_in_rect : ((b : ℂ) + (d : ℂ) * Complex.I) ∈ R := by
        rw [hR_def, Complex.mem_reProdIm]
        refine ⟨?_, ?_⟩
        · show ((b : ℂ) + (d : ℂ) * Complex.I).re ∈ Set.Icc a b
          have : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
            simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [this]; exact Set.right_mem_Icc.mpr hab.le
        · show ((b : ℂ) + (d : ℂ) * Complex.I).im ∈ Set.Icc c d
          have : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by
            simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
          rw [this]; exact Set.right_mem_Icc.mpr hcd.le
      have hbd_not_in_ball : ((b : ℂ) + (d : ℂ) * Complex.I) ∉ Metric.ball e R₀ := by
        intro h
        have h_cb : ((b : ℂ) + (d : ℂ) * Complex.I) ∈ Metric.closedBall e R₀ :=
          Metric.ball_subset_closedBall h
        have h_in_open := hdisk_in_rect h_cb
        rw [Complex.mem_reProdIm] at h_in_open
        obtain ⟨h_re, _⟩ := h_in_open
        have hre_eq : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [hre_eq, Set.mem_Ioo] at h_re
        linarith [h_re.2]
      exact ⟨hbd_in_rect, hbd_not_in_ball⟩
    · intro h_eq
      have h_re : z₀.re = ((b : ℂ) + (d : ℂ) * Complex.I).re := by rw [h_eq]
      rw [hz₀_re] at h_re
      have : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [this] at h_re
      linarith
  -- Every point of R_ann is an accumulation point.
  have h_accpt : ∀ z ∈ R_ann, AccPt z (Filter.principal R_ann) :=
    fun z hz => hR_ann_preconn.preperfect_of_nontrivial hR_ann_ntriv z hz
  -- Codiscrete equality g = r · h in `mul` form.
  have h_factor_mul : g =ᶠ[Filter.codiscreteWithin R_ann]
      (fun w => r w * h w) := by
    filter_upwards [h_factor] with w hw
    simpa [smul_eq_mul] using hw
  -- For every point of R_ann, get nhds equality g = r · h.
  have h_nhds_eq : ∀ z ∈ R_ann, g =ᶠ[nhds z] (fun w => r w * h w) := by
    intro z hz
    have hz_g_an : AnalyticAt ℂ g z := hg z hz
    have hz_r_an : AnalyticAt ℂ r z := hr_analytic z
    have hz_h_an : AnalyticAt ℂ h z := h_analytic z hz
    have hz_rh_an : AnalyticAt ℂ (fun w => r w * h w) z := hz_r_an.mul hz_h_an
    have h_pnctd := hz_g_an.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hz_rh_an.meromorphicAt hz (h_accpt z hz) h_factor_mul
    exact (AnalyticAt.frequently_eq_iff_eventually_eq hz_g_an hz_rh_an).mp h_pnctd.frequently
  have h_g_eq : ∀ z ∈ R_ann, g z = r z * h z := fun z hz =>
    (h_nhds_eq z hz).eq_of_nhds
  have h_deriv_eq : ∀ z ∈ R_ann, deriv g z = deriv (fun w => r w * h w) z := fun z hz =>
    (h_nhds_eq z hz).deriv_eq
  -- h non-vanishing on R_ann.
  have h_h_ne : ∀ z ∈ R_ann, h z ≠ 0 := fun z hz => h_nonzero ⟨z, hz⟩
  -- Divisor zero at boundary points (g ≠ 0 there).
  have h_div_zero_at_edge : ∀ z ∈ R_ann, g z ≠ 0 →
      (MeromorphicOn.divisor g R_ann) z = 0 := by
    intro z hz hz_g_ne
    rw [MeromorphicOn.divisor_apply hg_mer hz,
        (hg z hz).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr hz_g_ne)]
    simp
  -- r ≠ 0 where divisor is zero.
  have hr_ne_at_edge : ∀ z ∈ R_ann, g z ≠ 0 → r z ≠ 0 := fun z hz hz_g_ne =>
    Function.FactorizedRational.ne_zero (h_div_zero_at_edge z hz hz_g_ne)
  -- Membership of boundary edge points in R_ann.
  have h_bot_mem : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (c : ℂ) * Complex.I) ∈ R_ann := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
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
    · -- Not in open ball: edge point has Im = c, but disk interior has Im in (c, d)
      intro h
      have h_cb := Metric.ball_subset_closedBall h
      have h_in_open := hdisk_in_rect h_cb
      rw [Complex.mem_reProdIm] at h_in_open
      have him_eq : ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [him_eq, Set.mem_Ioo] at h_in_open
      linarith [h_in_open.2.1]
  have h_top_mem : ∀ x ∈ Set.Icc a b, ((x : ℂ) + (d : ℂ) * Complex.I) ∈ R_ann := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
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
    · intro h
      have h_cb := Metric.ball_subset_closedBall h
      have h_in_open := hdisk_in_rect h_cb
      rw [Complex.mem_reProdIm] at h_in_open
      have him_eq : ((x : ℂ) + (d : ℂ) * Complex.I).im = d := by
        simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [him_eq, Set.mem_Ioo] at h_in_open
      linarith [h_in_open.2.2]
  have h_right_mem : ∀ y ∈ Set.Icc c d, ((b : ℂ) + (y : ℂ) * Complex.I) ∈ R_ann := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
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
    · intro h
      have h_cb := Metric.ball_subset_closedBall h
      have h_in_open := hdisk_in_rect h_cb
      rw [Complex.mem_reProdIm] at h_in_open
      have hre_eq : ((b : ℂ) + (y : ℂ) * Complex.I).re = b := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [hre_eq, Set.mem_Ioo] at h_in_open
      linarith [h_in_open.1.2]
  have h_left_mem : ∀ y ∈ Set.Icc c d, ((a : ℂ) + (y : ℂ) * Complex.I) ∈ R_ann := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
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
    · intro h
      have h_cb := Metric.ball_subset_closedBall h
      have h_in_open := hdisk_in_rect h_cb
      rw [Complex.mem_reProdIm] at h_in_open
      have hre_eq : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [hre_eq, Set.mem_Ioo] at h_in_open
      linarith [h_in_open.1.1]
  -- Sphere points are in R_ann.
  have h_sphere_mem : ∀ z ∈ Metric.sphere e R₀, z ∈ R_ann := by
    intro z hz
    have hz_cb : z ∈ Metric.closedBall e R₀ := Metric.sphere_subset_closedBall hz
    refine ⟨?_, ?_⟩
    · have h_in_open := hdisk_in_rect hz_cb
      rw [Complex.mem_reProdIm] at h_in_open ⊢
      exact ⟨Set.Ioo_subset_Icc_self h_in_open.1, Set.Ioo_subset_Icc_self h_in_open.2⟩
    · rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball]
      linarith
  -- Express r as a Finset product over Dsupp.
  set Dsupp := hdiv_finite.toFinset with hDsupp_def
  have hD_hfs : (fun u : ℂ => MeromorphicOn.divisor g R_ann u).HasFiniteSupport :=
    hdiv_finite
  -- D supported strictly in open rect interior of R_ann (not on edges, not on sphere).
  have hsupp_in_open : ∀ u ∈ Dsupp, u ∈ Set.Ioo a b ×ℂ Set.Ioo c d ∧
      u ∉ Metric.closedBall e R₀ := by
    intro u hu
    have hu_supp : u ∈ (MeromorphicOn.divisor g R_ann).support := by
      simpa [hDsupp_def] using hu
    have hu_R_ann : u ∈ R_ann :=
      (MeromorphicOn.divisor g R_ann).supportWithinDomain hu_supp
    obtain ⟨hu_rect, hu_not_ball⟩ := hu_R_ann
    have hu_re_Icc : u.re ∈ Set.Icc a b := (Complex.mem_reProdIm.mp hu_rect).1
    have hu_im_Icc : u.im ∈ Set.Icc c d := (Complex.mem_reProdIm.mp hu_rect).2
    refine ⟨?_, ?_⟩
    · -- u in open inner rect: strict inequalities (since u ∉ rect boundary).
      rw [Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Ioo]
        refine ⟨lt_of_le_of_ne hu_re_Icc.1 (fun h_eq => ?_),
                lt_of_le_of_ne hu_re_Icc.2 (fun h_eq => ?_)⟩
        · -- u.re = a → u on left edge.
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
        · -- u.re = b → u on right edge.
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
        · have hu_eq : u = (u.re : ℂ) + (c : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, ← h_eq]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((u.re : ℂ) + (c : ℂ) * Complex.I)
            (h_bot_mem u.re hu_re_Icc) (hg_bot u.re hu_re_Icc)
        · have hu_eq : u = (u.re : ℂ) + (d : ℂ) * Complex.I := by
            apply Complex.ext
            · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
            · simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im, h_eq]
          rw [hu_eq] at hu_supp
          apply hu_supp
          exact h_div_zero_at_edge ((u.re : ℂ) + (d : ℂ) * Complex.I)
            (h_top_mem u.re hu_re_Icc) (hg_top u.re hu_re_Icc)
    · -- u ∉ closed ball: u ∉ open ball (since u ∈ R_ann) and u ∉ sphere
      -- (since D=0 on sphere).
      intro h_cb
      rw [Metric.mem_closedBall, le_iff_lt_or_eq] at h_cb
      rcases h_cb with h_lt | h_eq_dist
      · exact hu_not_ball (Metric.mem_ball.mpr h_lt)
      · -- u on sphere.
        have hu_sphere : u ∈ Metric.sphere e R₀ := by
          rw [Metric.mem_sphere]; exact h_eq_dist
        have : (MeromorphicOn.divisor g R_ann) u = 0 :=
          h_div_zero_at_edge u (h_sphere_mem u hu_sphere) (hg_sphere u hu_sphere)
        exact hu_supp this
  -- The final algebraic aggregation: applies the rect-boundary argument to
  -- `r` on each rect edge plus the sphere, uses `∮ (z-u)⁻¹ = 0` for `u`
  -- outside the closed ball (so the `r`-circle integral vanishes), and
  -- combines with the annular CG applied to `h'/h` (`h` analytic
  -- non-vanishing on `R_ann`).
  -- logDeriv decomposition `(rh)'/(rh) = r'/r + h'/h`.
  have h_logDeriv_split : ∀ z ∈ R_ann, g z ≠ 0 →
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
  have h_int_eq_at_edge : ∀ z ∈ R_ann, g z ≠ 0 →
      deriv g z / g z = deriv r z / r z + deriv h z / h z := fun z hz hz_g_ne => by
    rw [h_g_eq z hz, h_deriv_eq z hz]
    exact h_logDeriv_split z hz hz_g_ne
  -- Pointwise integrand equality on each of the four rectangle edges.
  have h_int_bot : (∫ x in a..b, deriv g ((x : ℂ) + (c : ℂ) * Complex.I) /
      g ((x : ℂ) + (c : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
        h ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := by rw [Set.uIcc_of_le hab.le] at hx; exact hx
    exact h_int_eq_at_edge _ (h_bot_mem x hx_Icc) (hg_bot x hx_Icc)
  have h_int_top : (∫ x in a..b, deriv g ((x : ℂ) + (d : ℂ) * Complex.I) /
      g ((x : ℂ) + (d : ℂ) * Complex.I)) =
      (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
        r ((x : ℂ) + (d : ℂ) * Complex.I) +
        deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
        h ((x : ℂ) + (d : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx_Icc : x ∈ Set.Icc a b := by rw [Set.uIcc_of_le hab.le] at hx; exact hx
    exact h_int_eq_at_edge _ (h_top_mem x hx_Icc) (hg_top x hx_Icc)
  have h_int_right : (∫ y in c..d, deriv g ((b : ℂ) + (y : ℂ) * Complex.I) /
      g ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc c d := by rw [Set.uIcc_of_le hcd.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_right_mem y hy_Icc) (hg_right y hy_Icc)
  have h_int_left : (∫ y in c..d, deriv g ((a : ℂ) + (y : ℂ) * Complex.I) /
      g ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy_Icc : y ∈ Set.Icc c d := by rw [Set.uIcc_of_le hcd.le] at hy; exact hy
    exact h_int_eq_at_edge _ (h_left_mem y hy_Icc) (hg_left y hy_Icc)
  -- Pointwise integrand equality on the sphere.
  have h_int_circle : (∮ z in C(e, R₀), deriv g z / g z) =
      (∮ z in C(e, R₀), deriv r z / r z + deriv h z / h z) := by
    apply circleIntegral.integral_congr hR₀.le
    intro z hz
    exact h_int_eq_at_edge z (h_sphere_mem z hz) (hg_sphere z hz)
  -- `h'/h` is differentiable on R_ann.
  have h_dh_div_h_diff : DifferentiableOn ℂ (fun z => deriv h z / h z) R_ann := by
    intro z hz
    have hh_ne := h_h_ne z hz
    have h_dh_an : AnalyticAt ℂ (deriv h) z := (h_analytic z hz).deriv
    have h_h_an : AnalyticAt ℂ h z := h_analytic z hz
    exact (h_dh_an.div h_h_an hh_ne).differentiableAt.differentiableWithinAt
  -- Strengthened differentiability hypothesis for `rectMinusDisk` CG:
  -- `h'/h` is differentiable on the slightly enlarged open set
  -- `(Ioo a b × Ioo c d) \ closedBall e R₀'` for some `R₀' < R₀`. The proof
  -- builds an open `V := {z : AnalyticAt ℂ h z ∧ h z ≠ 0}` containing `R_ann`,
  -- uses `IsCompact.exists_thickening_subset_open` to extract a uniform
  -- δ > 0 with `Metric.thickening δ R_ann ⊆ V`, and sets
  -- `R₀' := R₀ − (min R₀ δ) / 2`. For each `z ∈ (Ioo box) \ closedBall e R₀'`,
  -- either `R₀ ≤ ‖z − e‖` (then `z ∈ R_ann` directly) or `‖z − e‖ < R₀`
  -- (then the radial projection `w := e + (R₀/‖z−e‖)·(z−e)` is on the
  -- sphere `⊂ R_ann` via `hdisk_in_rect`, at distance `R₀ − ‖z − e‖ < δ`
  -- from `z`); hence `z ∈ Metric.thickening δ R_ann ⊆ V`, so `h'/h` is
  -- analytic at `z`.
  -- `h'/h` is differentiable on a slightly enlarged open set
  -- `(Ioo a b × Ioo c d) \ closedBall e R₀'` for some `R₀' < R₀`.
  --   1. `V := {z : AnalyticAt ℂ h z ∧ h z ≠ 0}` is open (AnalyticAt is open
  --      under perturbation via `AnalyticAt.eventually_analyticAt`; `h ≠ 0`
  --      open by `ContinuousAt.eventually_ne`).
  --   2. `R_ann ⊆ V` (from `h_analytic` and `h_h_ne`).
  --   3. By `IsCompact.exists_thickening_subset_open` applied to
  --      `hR_ann_compact`, `hV_open`, get δ > 0 with
  --      `Metric.thickening δ R_ann ⊆ V`.
  --   4. Set `R₀' := R₀ − min(R₀, δ)/2`.
  --   5. For each `z ∈ (Ioo a b × Ioo c d) \ closedBall e R₀'`:
  --      • if `R₀ ≤ ‖z − e‖`: `z ∈ R_ann` itself.
  --      • else `R₀' < ‖z − e‖ < R₀`: radial projection
  --        `w := e + (R₀/‖z − e‖)·(z − e)` lies on the sphere `⊂ R_ann`
  --        (via `hdisk_in_rect` for the box condition); `dist z w =
  --        R₀ − ‖z − e‖ < δ_eff/2 ≤ δ`, so `z ∈ Metric.thickening δ R_ann`.
  --   6. Therefore `z ∈ V`, giving `AnalyticAt h z ∧ h z ≠ 0`, hence
  --      `AnalyticAt (deriv h / h) z` via `AnalyticAt.deriv.div`.
  have h_dh_div_h_diff_existential : ∃ R₀' : ℝ, 0 < R₀' ∧ R₀' < R₀ ∧
      DifferentiableOn ℂ (fun z => deriv h z / h z)
        ((Set.Ioo a b ×ℂ Set.Ioo c d) \ Metric.closedBall e R₀') := by
    set V : Set ℂ := {z | AnalyticAt ℂ h z ∧ h z ≠ 0} with hV_def
    have hV_open : IsOpen V := by
      rw [isOpen_iff_eventually]
      intro z hz
      obtain ⟨h_an, h_ne⟩ := hz
      have h_an_evt : ∀ᶠ w in nhds z, AnalyticAt ℂ h w := h_an.eventually_analyticAt
      have h_ne_evt : ∀ᶠ w in nhds z, h w ≠ 0 := h_an.continuousAt.eventually_ne h_ne
      filter_upwards [h_an_evt, h_ne_evt] with w hw_an hw_ne using ⟨hw_an, hw_ne⟩
    have hR_ann_sub_V : R_ann ⊆ V := fun z hz =>
      ⟨h_analytic z hz, h_h_ne z hz⟩
    obtain ⟨δ, hδ_pos, hδ_sub⟩ :=
      hR_ann_compact.exists_thickening_subset_open hV_open hR_ann_sub_V
    set δ_eff := min R₀ δ with hδ_eff_def
    have hδ_eff_pos : 0 < δ_eff := lt_min hR₀ hδ_pos
    have hδ_eff_le_R₀ : δ_eff ≤ R₀ := min_le_left _ _
    have hδ_eff_le_δ : δ_eff ≤ δ := min_le_right _ _
    refine ⟨R₀ - δ_eff / 2, by linarith, by linarith, ?_⟩
    intro z hz
    obtain ⟨hz_box, hz_not_cball⟩ := hz
    rw [Metric.mem_closedBall, Complex.dist_eq, not_le] at hz_not_cball
    have hz_in_V : z ∈ V := by
      apply hδ_sub
      rw [Metric.mem_thickening_iff]
      by_cases h_inside : ‖z - e‖ < R₀
      · have h_norm_pos : 0 < ‖z - e‖ := by
          linarith [hz_not_cball, hδ_eff_pos]
        have h_norm_ne : ‖z - e‖ ≠ 0 := ne_of_gt h_norm_pos
        have h_norm_ne_c : (‖z - e‖ : ℂ) ≠ 0 := by exact_mod_cast h_norm_ne
        set w : ℂ := e + (R₀ / ‖z - e‖ : ℂ) * (z - e) with hw_def
        have h_w_sub : w - e = (R₀ / ‖z - e‖ : ℂ) * (z - e) := by
          rw [hw_def]; ring
        have h_w_norm : ‖w - e‖ = R₀ := by
          have h_coerce_div : (R₀ / ‖z - e‖ : ℂ) = ((R₀ / ‖z - e‖ : ℝ) : ℂ) := by
            push_cast; ring
          rw [h_w_sub, h_coerce_div, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (div_nonneg hR₀.le (norm_nonneg _)),
              div_mul_cancel₀ _ h_norm_ne]
        have h_w_in_cb : w ∈ Metric.closedBall e R₀ := by
          rw [Metric.mem_closedBall, Complex.dist_eq, h_w_norm]
        have h_w_in_Ioo : w ∈ Set.Ioo a b ×ℂ Set.Ioo c d := hdisk_in_rect h_w_in_cb
        have h_w_in_Icc : w ∈ Set.Icc a b ×ℂ Set.Icc c d := by
          rw [Complex.mem_reProdIm] at h_w_in_Ioo ⊢
          exact ⟨Set.Ioo_subset_Icc_self h_w_in_Ioo.1,
                 Set.Ioo_subset_Icc_self h_w_in_Ioo.2⟩
        have h_w_not_in_ball : w ∉ Metric.ball e R₀ := by
          rw [Metric.mem_ball, Complex.dist_eq, h_w_norm]; exact lt_irrefl R₀
        refine ⟨w, ⟨h_w_in_Icc, h_w_not_in_ball⟩, ?_⟩
        rw [dist_comm, Complex.dist_eq]
        have h_w_minus_z : w - z = ((R₀ - ‖z - e‖) / ‖z - e‖ : ℂ) * (z - e) := by
          rw [hw_def]; field_simp; ring
        have h_coerce_diff : ((R₀ - ‖z - e‖) / ‖z - e‖ : ℂ) =
            (((R₀ - ‖z - e‖) / ‖z - e‖ : ℝ) : ℂ) := by
          push_cast; ring
        rw [h_w_minus_z, h_coerce_diff, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg
              (div_nonneg (by linarith [h_inside]) (norm_nonneg _)),
            div_mul_cancel₀ _ h_norm_ne]
        linarith [hz_not_cball, hδ_eff_le_δ]
      · push_neg at h_inside
        refine ⟨z, ⟨?_, ?_⟩, by rw [dist_self]; exact hδ_pos⟩
        · rw [Complex.mem_reProdIm] at hz_box ⊢
          exact ⟨Set.Ioo_subset_Icc_self hz_box.1,
                 Set.Ioo_subset_Icc_self hz_box.2⟩
        · intro h_in_ball
          rw [Metric.mem_ball, Complex.dist_eq] at h_in_ball
          linarith
    obtain ⟨h_an, h_ne⟩ := hz_in_V
    exact (h_an.deriv.div h_an h_ne).differentiableAt.differentiableWithinAt
  -- Annular Cauchy-Goursat for `h'/h`.
  have h_annular_h :
      ((∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
          h ((x : ℂ) + (c : ℂ) * Complex.I)) +
        Complex.I * (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
          h ((b : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
          h ((x : ℂ) + (d : ℂ) * Complex.I)) -
        Complex.I * (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
          h ((a : ℂ) + (y : ℂ) * Complex.I))) -
      (∮ z in C(e, R₀), deriv h z / h z) = 0 :=
    integral_boundary_rectMinusDisk_eq_zero_of_differentiableOn
      (fun z => deriv h z / h z) a b c d e R₀ hab hcd hR₀ hdisk_in_rect
      h_dh_div_h_diff.continuousOn h_dh_div_h_diff_existential
  -- Express `r` as a Finset product over Dsupp.
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) Complex.I_ne_zero
    · exact two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
  have hr_eq_finset : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ (MeromorphicOn.divisor g R_ann u) := by
    intro z
    have heq := Function.FactorizedRational.finprod_eq_fun hD_hfs
    have hrz : r z = ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor g R_ann u) := by
      rw [hr_def, heq]
    rw [hrz]
    rw [finprod_eq_prod_of_mulSupport_subset
      (f := fun u => (z - u) ^ (MeromorphicOn.divisor g R_ann u))
      (s := Dsupp)]
    intro u hu
    simp only [Function.mem_mulSupport, ne_eq] at hu
    change u ∈ hdiv_finite.toFinset
    rw [Set.Finite.mem_toFinset]
    intro h_zero
    apply hu
    rw [h_zero]
    simp
  have hzpow_eq_pow : ∀ u : ℂ, ∀ z : ℂ,
      (z - u) ^ (MeromorphicOn.divisor g R_ann u) =
      (z - u) ^ ((MeromorphicOn.divisor g R_ann u).toNat) := by
    intro u z
    rw [← zpow_natCast (z - u) ((MeromorphicOn.divisor g R_ann u).toNat),
        Int.toNat_of_nonneg (hD_nonneg u)]
  have hr_eq_natpow : ∀ z, r z =
      ∏ u ∈ Dsupp, (z - u) ^ ((MeromorphicOn.divisor g R_ann u).toNat) := by
    intro z
    rw [hr_eq_finset z]
    apply Finset.prod_congr rfl
    intro u _
    exact hzpow_eq_pow u z
  -- logDeriv r = ∑_u (D u : ℂ) / (z - u) where g ≠ 0.
  have h_logDeriv_r_eq : ∀ z ∈ R_ann, g z ≠ 0 →
      deriv r z / r z = ∑ u ∈ Dsupp,
        ((MeromorphicOn.divisor g R_ann u : ℂ) / (z - u)) := by
    intro z hz hz_g_ne
    have hz_ne_u : ∀ u ∈ Dsupp, z - u ≠ 0 := by
      intro u hu hzu
      have hz_eq : z = u := by linear_combination hzu
      have hu_supp : u ∈ (MeromorphicOn.divisor g R_ann).support := by
        simpa [hDsupp_def] using hu
      apply hu_supp
      rw [← hz_eq]
      exact h_div_zero_at_edge z hz hz_g_ne
    set D := MeromorphicOn.divisor g R_ann
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
  -- Non-vanishing of (z - u) on each of the four edges and on the sphere
  -- (since u ∈ Dsupp is in the open rect interior and ∉ closed ball).
  have h_ne_bot : ∀ u ∈ Dsupp, ∀ _x : ℝ,
      (_x : ℂ) + (c : ℂ) * Complex.I - u ≠ 0 := by
    intro u hu x h_eq
    obtain ⟨hu_rect, _⟩ := hsupp_in_open u hu
    have hu_im : u.im ∈ Set.Ioo c d := (Complex.mem_reProdIm.mp hu_rect).2
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
    obtain ⟨hu_rect, _⟩ := hsupp_in_open u hu
    have hu_im : u.im ∈ Set.Ioo c d := (Complex.mem_reProdIm.mp hu_rect).2
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
    obtain ⟨hu_rect, _⟩ := hsupp_in_open u hu
    have hu_re : u.re ∈ Set.Ioo a b := (Complex.mem_reProdIm.mp hu_rect).1
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
    obtain ⟨hu_rect, _⟩ := hsupp_in_open u hu
    have hu_re : u.re ∈ Set.Ioo a b := (Complex.mem_reProdIm.mp hu_rect).1
    have h_re : ((a : ℂ) + (y : ℂ) * Complex.I - u).re = a - u.re := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    have h_re_eq : a - u.re = 0 := by
      have := congrArg Complex.re h_eq
      rw [h_re] at this
      simpa using this
    obtain ⟨h1, _⟩ := hu_re
    linarith
  have h_ne_sphere : ∀ u ∈ Dsupp, ∀ θ : ℝ,
      _root_.circleMap e R₀ θ - u ≠ 0 := by
    intro u hu θ h_eq
    obtain ⟨_, hu_not_cb⟩ := hsupp_in_open u hu
    have hsp : _root_.circleMap e R₀ θ ∈ Metric.closedBall e R₀ :=
      Metric.sphere_subset_closedBall (_root_.circleMap_mem_sphere e hR₀.le θ)
    have : _root_.circleMap e R₀ θ = u := by linear_combination h_eq
    rw [this] at hsp
    exact hu_not_cb hsp
  -- IntervalIntegrability of the per-pole summand on each edge.
  have h_summand_int_bot : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g R_ann u : ℂ) / ((x : ℂ) + (c : ℂ) * Complex.I - u))
        MeasureTheory.volume a b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_bot u hu x)
  have h_summand_int_top : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun x : ℝ =>
        (MeromorphicOn.divisor g R_ann u : ℂ) / ((x : ℂ) + (d : ℂ) * Complex.I - u))
        MeasureTheory.volume a b := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun x : ℝ => ((x : ℂ) + (d : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun x => h_ne_top u hu x)
  have h_summand_int_right : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g R_ann u : ℂ) / ((b : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume c d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((b : ℂ) + (y : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_right u hu y)
  have h_summand_int_left : ∀ u ∈ Dsupp,
      IntervalIntegrable (fun y : ℝ =>
        (MeromorphicOn.divisor g R_ann u : ℂ) / ((a : ℂ) + (y : ℂ) * Complex.I - u))
        MeasureTheory.volume c d := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_cont : Continuous fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - u) := by fun_prop
    exact continuous_const.div h_cont (fun y => h_ne_left u hu y)
  -- IntervalIntegrability of the per-pole summand parametrized by the circle.
  have h_summand_int_circle : ∀ u ∈ Dsupp,
      IntervalIntegrable
        (fun θ : ℝ => deriv (_root_.circleMap e R₀) θ •
          ((MeromorphicOn.divisor g R_ann u : ℂ) /
            (_root_.circleMap e R₀ θ - u)))
        MeasureTheory.volume 0 (2 * Real.pi) := by
    intro u hu
    apply Continuous.intervalIntegrable
    have h_param_cont : Continuous (_root_.circleMap e R₀) := continuous_circleMap _ _
    have h_deriv_cont : Continuous (deriv (_root_.circleMap e R₀)) := by
      have h_eq : deriv (_root_.circleMap e R₀) =
          fun θ : ℝ => _root_.circleMap 0 R₀ θ * Complex.I := by
        funext θ; exact deriv_circleMap _ _ _
      rw [h_eq]; fun_prop
    have h_sub_cont : Continuous (fun θ : ℝ => _root_.circleMap e R₀ θ - u) :=
      h_param_cont.sub continuous_const
    have h_inv_cont : Continuous (fun θ : ℝ =>
        (MeromorphicOn.divisor g R_ann u : ℂ) / (_root_.circleMap e R₀ θ - u)) :=
      continuous_const.div h_sub_cont (fun θ => h_ne_sphere u hu θ)
    exact h_deriv_cont.smul h_inv_cont
  -- IntervalIntegrability of `r'/r` on each edge.
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
  -- IntervalIntegrability of `h'/h` on each edge.
  have h_dh_div_h_int_bot : IntervalIntegrable
      (fun x : ℝ => deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
        h ((x : ℂ) + (c : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have h_param_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) + (c : ℂ) * Complex.I))
        (Set.uIcc a b) := by apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I)
        (Set.uIcc a b) R_ann := by
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
        (Set.uIcc a b) := by apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I)
        (Set.uIcc a b) R_ann := by
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
        (Set.uIcc c d) := by apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc c d) R_ann := by
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
        (Set.uIcc c d) := by apply Continuous.continuousOn; fun_prop
    have h_param_maps_to : Set.MapsTo (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I)
        (Set.uIcc c d) R_ann := by
      intro y hy
      rw [Set.uIcc_of_le hcd.le] at hy
      exact h_left_mem y hy
    exact h_dh_div_h_diff.continuousOn.comp h_param_cont h_param_maps_to
  -- Per-edge `r`-integral decomposition.
  have h_bot_r_decomp : (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
        r ((x : ℂ) + (c : ℂ) * Complex.I)) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) *
        (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ x in a..b, deriv r ((x : ℂ) + (c : ℂ) * Complex.I) /
          r ((x : ℂ) + (c : ℂ) * Complex.I)) =
        (∫ x in a..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) /
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
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) *
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ x in a..b, deriv r ((x : ℂ) + (d : ℂ) * Complex.I) /
          r ((x : ℂ) + (d : ℂ) * Complex.I)) =
        (∫ x in a..b, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) /
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
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) *
        (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
          r ((b : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in c..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) /
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
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) *
        (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) := by
    have h_pointwise : (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
          r ((a : ℂ) + (y : ℂ) * Complex.I)) =
        (∫ y in c..d, ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) /
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
  -- Circle integral decomposition for `r'/r`.
  -- Unfold to interval integral, swap with the Finset sum, and recognize each
  -- summand as `(D u) * ∮ (z-u)⁻¹`.
  have h_circle_r_decomp : (∮ z in C(e, R₀), deriv r z / r z) =
      ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) *
        (∮ z in C(e, R₀), (z - u)⁻¹) := by
    have h_pointwise_sphere : ∀ θ : ℝ,
        deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ) =
        ∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ) /
          (_root_.circleMap e R₀ θ - u) := by
      intro θ
      have hsp : _root_.circleMap e R₀ θ ∈ Metric.sphere e R₀ :=
        _root_.circleMap_mem_sphere e hR₀.le θ
      exact h_logDeriv_r_eq _ (h_sphere_mem _ hsp) (hg_sphere _ hsp)
    change (∫ θ in (0:ℝ)..(2 * Real.pi),
        deriv (_root_.circleMap e R₀) θ •
          (deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ))) = _
    have h_integrand_eq : ∀ θ : ℝ,
        deriv (_root_.circleMap e R₀) θ •
          (deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ)) =
        ∑ u ∈ Dsupp, deriv (_root_.circleMap e R₀) θ •
          ((MeromorphicOn.divisor g R_ann u : ℂ) /
            (_root_.circleMap e R₀ θ - u)) := by
      intro θ
      rw [h_pointwise_sphere θ, Finset.smul_sum]
    rw [show (fun θ : ℝ => deriv (_root_.circleMap e R₀) θ •
          (deriv r (_root_.circleMap e R₀ θ) / r (_root_.circleMap e R₀ θ))) =
        (fun θ : ℝ => ∑ u ∈ Dsupp, deriv (_root_.circleMap e R₀) θ •
          ((MeromorphicOn.divisor g R_ann u : ℂ) /
            (_root_.circleMap e R₀ θ - u))) from funext h_integrand_eq]
    rw [intervalIntegral.integral_finset_sum h_summand_int_circle]
    apply Finset.sum_congr rfl
    intro u _
    change (∫ θ in (0:ℝ)..(2 * Real.pi), deriv (_root_.circleMap e R₀) θ •
        ((MeromorphicOn.divisor g R_ann u : ℂ) /
          (_root_.circleMap e R₀ θ - u))) =
        (MeromorphicOn.divisor g R_ann u : ℂ) *
          (∫ θ in (0:ℝ)..(2 * Real.pi),
            deriv (_root_.circleMap e R₀) θ • (_root_.circleMap e R₀ θ - u)⁻¹)
    rw [show (fun θ : ℝ => deriv (_root_.circleMap e R₀) θ •
        ((MeromorphicOn.divisor g R_ann u : ℂ) /
          (_root_.circleMap e R₀ θ - u))) =
        (fun θ : ℝ => (MeromorphicOn.divisor g R_ann u : ℂ) *
          (deriv (_root_.circleMap e R₀) θ •
            (_root_.circleMap e R₀ θ - u)⁻¹)) from by
      funext θ
      simp only [smul_eq_mul]
      ring]
    exact intervalIntegral.integral_const_mul _ _
  -- For `u ∈ Dsupp`, `∮ (z-u)⁻¹ = 0` since `u ∉ closedBall e R₀`.
  have h_circle_inv_zero : ∀ u ∈ Dsupp, (∮ z in C(e, R₀), (z - u)⁻¹) = 0 := by
    intro u hu
    obtain ⟨_, hu_not_cb⟩ := hsupp_in_open u hu
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR₀.le
      (s := ∅) Set.countable_empty
    · intro z hz
      have hzne : z - u ≠ 0 := by
        intro h
        have : z = u := by linear_combination h
        rw [this] at hz
        exact hu_not_cb hz
      exact ((continuous_id.sub continuous_const).continuousAt.inv₀ hzne).continuousWithinAt
    · intro z hz
      simp only [Set.mem_diff, Set.mem_empty_iff_false, not_false_eq_true, and_true] at hz
      have hzne : z ≠ u := by
        intro h_eq
        rw [h_eq] at hz
        exact hu_not_cb (Metric.ball_subset_closedBall hz)
      exact (differentiableAt_id.sub_const u).inv (sub_ne_zero.mpr hzne)
  -- Per-pole rectangle contribution = 2πi (winding = 1 inside open rect).
  have h_per_pole_rect : ∀ u ∈ Dsupp,
      (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) +
      Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
      (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
      Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) =
      2 * Real.pi * Complex.I := by
    intro u hu
    obtain ⟨hu_rect, _⟩ := hsupp_in_open u hu
    have hu_re : u.re ∈ Set.Ioo a b := (Complex.mem_reProdIm.mp hu_rect).1
    have hu_im : u.im ∈ Set.Ioo c d := (Complex.mem_reProdIm.mp hu_rect).2
    have h_one := rectangleWindingNumber_inside_eq_one a b c d hab hcd hu_re hu_im
    have hk : (2 * Real.pi * Complex.I) * ((2 * Real.pi * Complex.I)⁻¹ *
        ((∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹))) =
        (2 * Real.pi * Complex.I) * 1 := by rw [h_one]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul, mul_one] at hk
    exact hk
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
  have h_right_split_int : (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((b : ℂ) + (y : ℂ) * Complex.I) /
        r ((b : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
        h ((b : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_right h_dh_div_h_int_right
  have h_left_split_int : (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I) +
        deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (∫ y in c..d, deriv r ((a : ℂ) + (y : ℂ) * Complex.I) /
        r ((a : ℂ) + (y : ℂ) * Complex.I)) +
      (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
        h ((a : ℂ) + (y : ℂ) * Complex.I)) :=
    intervalIntegral.integral_add h_dr_div_r_int_left h_dh_div_h_int_left
  -- Circle integral split: ∮ (r'/r + h'/h) = ∮ r'/r + ∮ h'/h.
  have h_circle_split : (∮ z in C(e, R₀), deriv r z / r z + deriv h z / h z) =
      (∮ z in C(e, R₀), deriv r z / r z) + (∮ z in C(e, R₀), deriv h z / h z) := by
    apply circleIntegral.integral_add
    · -- CircleIntegrable r'/r: r'/r is continuous on the sphere
      -- since r is non-vanishing there.
      have hr_ne_sphere : ∀ z ∈ Metric.sphere e R₀, r z ≠ 0 := by
        intro z hz
        rw [hr_eq_natpow]
        refine Finset.prod_ne_zero_iff.mpr (fun u hu => pow_ne_zero _ ?_)
        intro h_eq
        obtain ⟨_, hu_not_cb⟩ := hsupp_in_open u hu
        have : z = u := by linear_combination h_eq
        rw [this] at hz
        exact hu_not_cb (Metric.sphere_subset_closedBall hz)
      apply ContinuousOn.circleIntegrable hR₀.le
      exact h_dr_cont.continuousOn.div hr_cont.continuousOn hr_ne_sphere
    · -- CircleIntegrable h'/h: h'/h is differentiable on R_ann ⊃ sphere.
      apply ContinuousOn.circleIntegrable hR₀.le
      apply h_dh_div_h_diff.continuousOn.mono
      intro z hz
      exact h_sphere_mem z hz
  -- finsum bridge.
  have h_finset_eq_finsum :
      (∑ u ∈ Dsupp, (MeromorphicOn.divisor g R_ann u : ℂ)) =
      (∑ᶠ u, (MeromorphicOn.divisor g R_ann u : ℂ)) := by
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
      (∑ᶠ u, (MeromorphicOn.divisor g R_ann u : ℂ)) =
      (((∑ᶠ u, MeromorphicOn.divisor g R_ann u).toNat : ℤ) : ℂ) := by
    have h_nonneg : 0 ≤ ∑ᶠ u, MeromorphicOn.divisor g R_ann u :=
      finsum_nonneg (fun u => hD_nonneg u)
    rw [Int.toNat_of_nonneg h_nonneg]
    have hcast := AddMonoidHom.map_finsum (Int.castRingHom ℂ).toAddMonoidHom
      (f := fun u => MeromorphicOn.divisor g R_ann u) hdiv_finite
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, Int.coe_castRingHom] at hcast
    rw [← hcast]
  -- Per-pole equation combining 4 rect edges (= 2πi) with 0 circle contribution.
  have h_per_pole_combined : ∀ u ∈ Dsupp,
      ((∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹) +
        Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹) -
        Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
      (∮ z in C(e, R₀), (z - u)⁻¹) = 2 * Real.pi * Complex.I := by
    intro u hu
    rw [h_circle_inv_zero u hu, sub_zero]
    exact h_per_pole_rect u hu
  -- Final calc.
  refine ⟨(∑ᶠ u, MeromorphicOn.divisor g R_ann u).toNat, ?_⟩
  -- Rewrite all g-integrals to (r + h) form.
  rw [h_int_bot, h_int_top, h_int_right, h_int_left, h_int_circle,
      h_bot_split, h_top_split, h_right_split_int, h_left_split_int,
      h_circle_split,
      h_bot_r_decomp, h_top_r_decomp, h_right_r_decomp, h_left_r_decomp,
      h_circle_r_decomp]
  -- Now the goal involves: (4 r-rect sums + 4 h-rect terms) - (r-circle sum + h-circle).
  -- Combine: (r-rect sums - r-circle sum) gives ∑ u (D u) * 2πi via h_per_pole_combined.
  --         (h-rect 4 - h-circle) = 0 via h_annular_h.
  set D := MeromorphicOn.divisor g R_ann
  -- Compute the r-part as a single Finset sum.
  have h_r_combine :
      (∑ u ∈ Dsupp, (D u : ℂ) * (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
      Complex.I * (∑ u ∈ Dsupp, (D u : ℂ) *
        (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
      (∑ u ∈ Dsupp, (D u : ℂ) * (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
      Complex.I * (∑ u ∈ Dsupp, (D u : ℂ) *
        (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
      (∑ u ∈ Dsupp, (D u : ℂ) * (∮ z in C(e, R₀), (z - u)⁻¹)) =
      (∑ u ∈ Dsupp, (D u : ℂ)) * (2 * Real.pi * Complex.I) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u hu
    have hpp := h_per_pole_combined u hu
    linear_combination (D u : ℂ) * hpp
  -- Reshape goal so the r-part and h-part separate, then apply h_r_combine and h_annular_h.
  rw [show
      (((∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
        (∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
          h ((x : ℂ) + (c : ℂ) * Complex.I))) +
       Complex.I * ((∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
        (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
          h ((b : ℂ) + (y : ℂ) * Complex.I))) -
       ((∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) +
        (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
          h ((x : ℂ) + (d : ℂ) * Complex.I))) -
       Complex.I * ((∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) +
        (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
          h ((a : ℂ) + (y : ℂ) * Complex.I)))) -
      ((∑ u ∈ Dsupp, (D u : ℂ) * (∮ z in C(e, R₀), (z - u)⁻¹)) +
        (∮ z in C(e, R₀), deriv h z / h z)) =
      ((∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - u)⁻¹)) +
        Complex.I * (∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
        (∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I - u)⁻¹)) -
        Complex.I * (∑ u ∈ Dsupp, (D u : ℂ) *
          (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I - u)⁻¹)) -
        (∑ u ∈ Dsupp, (D u : ℂ) * (∮ z in C(e, R₀), (z - u)⁻¹))) +
      (((∫ x in a..b, deriv h ((x : ℂ) + (c : ℂ) * Complex.I) /
            h ((x : ℂ) + (c : ℂ) * Complex.I)) +
        Complex.I * (∫ y in c..d, deriv h ((b : ℂ) + (y : ℂ) * Complex.I) /
            h ((b : ℂ) + (y : ℂ) * Complex.I)) -
        (∫ x in a..b, deriv h ((x : ℂ) + (d : ℂ) * Complex.I) /
            h ((x : ℂ) + (d : ℂ) * Complex.I)) -
        Complex.I * (∫ y in c..d, deriv h ((a : ℂ) + (y : ℂ) * Complex.I) /
            h ((a : ℂ) + (y : ℂ) * Complex.I))) -
        (∮ z in C(e, R₀), deriv h z / h z)) from by ring]
  rw [h_r_combine, h_annular_h, add_zero]
  rw [mul_comm ((∑ u ∈ Dsupp, (D u : ℂ))) (2 * Real.pi * Complex.I)]
  rw [inv_mul_cancel_left₀ hpi]
  exact h_finset_eq_finsum.trans (h_finsum_int_eq_nat.trans (by push_cast; rfl))

end Complex
