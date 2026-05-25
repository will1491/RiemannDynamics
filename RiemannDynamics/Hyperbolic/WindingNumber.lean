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

/-!
# Winding number and the argument principle

Winding-number theory for the `λ : F^o ≅ {Im w > 0}` biholomorphism
in `Gamma2FundamentalDomain.lean`.

## Definitions

* `Complex.circleWindingNumber c R w` — circle case,
  `(2πi)⁻¹ ∮_{|z−c|=R} (z − w)⁻¹ dz`.
* `Complex.pathContourIntegral γ a b f` — contour integral
  `∫_a^b f(γ t) · γ'(t) dt` of `f` along the path `γ : ℝ → ℂ`
  from parameter `a` to `b`.
* `Complex.pathWindingNumber γ a b w` — winding number of a closed
  parameterized path `γ : [a, b] → ℂ` around `w`, defined as
  `(2πi)⁻¹ ∫_a^b γ'(t) / (γ(t) − w) dt`.

## Main results

* `Complex.circleWindingNumber_inside` — winding number `1` for points
  strictly inside the circle.
* `Complex.circleWindingNumber_outside` — winding number `0` for
  points strictly outside the closed disk.
* `Complex.circleWindingNumber_self` — special case `w = c`.
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

end Complex
