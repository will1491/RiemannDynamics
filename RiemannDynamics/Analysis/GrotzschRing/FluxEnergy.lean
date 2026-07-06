/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib
import RiemannDynamics.Analysis.Baernstein.BaernsteinComparison
import RiemannDynamics.Analysis.GrotzschRing.GrotzschPotential
import RiemannDynamics.QC.Regularity.ModulusEnergy
import RiemannDynamics.QC.Regularity.RingModulus

/-!
# Flux–energy identities for harmonic ring potentials

For a potential `u` harmonic on the collar annulus `RoundAnnulus 0 r₀ 1`, the log-polar pullback
`u ∘ exp` is smooth on the vertical strip `{log r₀ < Re w < 0}` and its Wirtinger derivative
`expGrad u = w ↦ gradC u (e^w) · e^w` is holomorphic there.  This yields:

* `RiemannDynamics.logCircleMean_affineOn` — the circle mean `ξ ↦ ∫_{(−π,π)} u(e^{ξ+iθ}) dθ` is
  an affine function `a + b·ξ` of the log-radius on `(log r₀, 0)`;
* `RiemannDynamics.logCircleMean_tendsto_two_pi` — if `u` is continuous on the closed collar and
  `u = 1` on the unit circle, the circle mean tends to `2π` as `ξ → 0⁻`;
* `RiemannDynamics.dirichletEnergy_roundAnnulus_eq_ringFlux_sub` — the Dirichlet energy of `u`
  over a sub-annulus `{e^{ξ₁} < |z| < e^{ξ₂}}` of the collar equals the increment
  `ringFlux u ξ₂ − ringFlux u ξ₁` of the flux `ξ ↦ ∫_{(−π,π)} u · (r ∂_r u) dθ`;
* `RiemannDynamics.integral_expGrad_re_eq_slope` — when the circle mean is `2π + b·ξ`, the angle
  integral of the scale-invariant radial derivative `r ∂_r u` equals the slope `b` at every
  log-radius of the collar;
* `RiemannDynamics.ringFlux_monotoneOn` — the ring flux is nondecreasing in the log-radius.

The derivative computations run through differentiation under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), holomorphy of `expGrad u`
on the strip, integration by parts in the angle with `2π`-periodic boundary terms, and the planar
change of variables `z = e^{ξ+iθ}` via `Complex.lintegral_comp_polarCoord_symm`.
-/

open MeasureTheory Set ENNReal Filter Topology Complex

open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-! ### The log-polar holomorphic gradient and the ring flux -/

/-- The **log-polar holomorphic gradient**: the Wirtinger derivative `w ↦ gradC u (e^w) · e^w` of
the log-polar pullback `u ∘ exp`.  Its real part is the radial derivative `∂_ξ (u ∘ exp)` and
minus its imaginary part is the angular derivative `∂_θ (u ∘ exp)`; it is holomorphic on the
vertical strip corresponding to any annulus on which `u` is harmonic. -/
def expGrad (u : ℂ → ℝ) (w : ℂ) : ℂ := gradC u (Complex.exp w) * Complex.exp w

/-- The **ring flux** of a potential `u` at log-radius `ξ`: the angle integral
`∫_{(−π,π)} u(e^{ξ+iθ}) · (∇u(e^{ξ+iθ}) · e^{ξ+iθ}) dθ` of the potential against its
scale-invariant radial derivative `r ∂_r u` over the circle of radius `e^ξ`. -/
def ringFlux (u : ℂ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Ioo (-π) π,
    u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-! ### Log-polar points, the strip, and the annulus -/

/-- The real part of the log-polar point `ξ + θ·I` is the log-radius `ξ`. -/
theorem re_logPolar (ξ θ : ℝ) : ((ξ : ℂ) + (θ : ℂ) * Complex.I).re = ξ := by simp

/-- The imaginary part of the log-polar point `ξ + θ·I` is the angle `θ`. -/
theorem im_logPolar (ξ θ : ℝ) : ((ξ : ℂ) + (θ : ℂ) * Complex.I).im = θ := by simp

/-- The round annulus is open. -/
theorem isOpen_roundAnnulus (z₀ : ℂ) (r R : ℝ) : IsOpen (RoundAnnulus z₀ r R) := by
  have h1 : IsOpen {z : ℂ | r < dist z z₀} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have h2 : IsOpen {z : ℂ | dist z z₀ < R} :=
    isOpen_lt (continuous_id.dist continuous_const) continuous_const
  exact h1.inter h2

/-- The vertical strip `{a < Re w < b}` is open. -/
theorem isOpen_logStrip (a b : ℝ) : IsOpen {w : ℂ | a < w.re ∧ w.re < b} := by
  have h : {w : ℂ | a < w.re ∧ w.re < b} = Complex.re ⁻¹' Ioo a b := by
    ext w; simp [Set.mem_Ioo]
  rw [h]
  exact isOpen_Ioo.preimage Complex.continuous_re

/-- The exponential maps the strip `{log r₀ < Re w < 0}` into the annulus `{r₀ < |z| < 1}`. -/
theorem exp_mem_roundAnnulus {r₀ : ℝ} (h0 : 0 < r₀) {w : ℂ}
    (h1 : Real.log r₀ < w.re) (h2 : w.re < 0) :
    Complex.exp w ∈ RoundAnnulus 0 r₀ 1 := by
  have hdist : dist (Complex.exp w) 0 = Real.exp w.re := by
    rw [dist_zero_right, Complex.norm_exp]
  simp only [RoundAnnulus, Set.mem_setOf_eq, hdist]
  constructor
  · calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log h0).symm
      _ < Real.exp w.re := Real.exp_lt_exp.mpr h1
  · calc Real.exp w.re < Real.exp 0 := Real.exp_lt_exp.mpr h2
      _ = 1 := Real.exp_zero

/-- The exponential is `2π·I`-periodic between the two angle endpoints `±π` of a circle. -/
theorem exp_logPolar_pi_eq (ξ : ℝ) :
    Complex.exp ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
  have h : (ξ : ℂ) + (π : ℂ) * Complex.I
      = ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_periodic _]

/-! ### Chain rules along the radial and angular directions -/

/-- The radial line `x ↦ x + θ·I` (real `x`) has derivative `1`. -/
theorem hasDerivAt_logPolar_radial (ξ θ : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + (θ : ℂ) * Complex.I) 1 ξ :=
  Complex.ofRealCLM.hasDerivAt.add_const _

/-- The angular line `t ↦ ξ + t·I` has derivative `I`. -/
theorem hasDerivAt_logPolar_angular (ξ θ : ℝ) :
    HasDerivAt (fun t : ℝ => (ξ : ℂ) + (t : ℂ) * Complex.I) Complex.I θ := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
  simpa using h.const_add ((ξ : ℂ))

/-- The radial curve `x ↦ e^{x+θi}` has derivative `e^{ξ+θi}` at `x = ξ`. -/
theorem hasDerivAt_exp_logPolar_radial (ξ θ : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
      (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ξ := by
  simpa using (hasDerivAt_logPolar_radial ξ θ).cexp

/-- The angular curve `t ↦ e^{ξ+ti}` has derivative `e^{ξ+θi}·I` at `t = θ`. -/
theorem hasDerivAt_exp_logPolar_angular (ξ θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
      (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) * Complex.I) θ := by
  simpa using (hasDerivAt_logPolar_angular ξ θ).cexp

/-- **Radial derivative of the pullback.** For `u` differentiable at `e^{ξ+θi}`, the log-polar
pullback `x ↦ u(e^{x+θi})` has derivative `Re (expGrad u (ξ+θi))` at `x = ξ`. -/
theorem hasDerivAt_uexp_radial {u : ℂ → ℝ} {ξ θ : ℝ}
    (hdiff : DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :
    HasDerivAt (fun x : ℝ => u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)))
      (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ξ := by
  have hcomp :=
    hdiff.hasFDerivAt.comp_hasDerivAt ξ (hasDerivAt_exp_logPolar_radial ξ θ)
  have heq : fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      = (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
    rw [fderiv_eq_re_gradC_mul]; rfl
  rw [heq] at hcomp
  simpa [Function.comp] using hcomp

/-- **Angular derivative of the pullback.** For `u` differentiable at `e^{ξ+θi}`, the log-polar
pullback `t ↦ u(e^{ξ+ti})` has derivative `−Im (expGrad u (ξ+θi))` at `t = θ`. -/
theorem hasDerivAt_uexp_angular {u : ℂ → ℝ} {ξ θ : ℝ}
    (hdiff : DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :
    HasDerivAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
      (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ := by
  have hcomp :=
    hdiff.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_exp_logPolar_angular ξ θ)
  have heq : fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) * Complex.I)
      = -(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im := by
    rw [fderiv_eq_re_gradC_mul]
    have : gradC u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) * Complex.I)
        = expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I) * Complex.I := by
      rw [expGrad]; ring
    rw [this, Complex.mul_I_re]
  rw [heq] at hcomp
  simpa [Function.comp] using hcomp

/-- **Radial derivative of the holomorphic gradient.** If `expGrad u` is complex-differentiable
at `ξ + θ·I`, its restriction to the radial line has derivative `deriv (expGrad u) (ξ+θi)`. -/
theorem hasDerivAt_expGrad_radial {u : ℂ → ℝ} {ξ θ : ℝ}
    (hd : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :
    HasDerivAt (fun x : ℝ => expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I))
      (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ξ := by
  have h := hd.hasDerivAt.comp ξ (hasDerivAt_logPolar_radial ξ θ)
  simpa [Function.comp] using h

/-- **Angular derivative of the holomorphic gradient.** If `expGrad u` is complex-differentiable
at `ξ + θ·I`, its restriction to the angular line has derivative `I · deriv (expGrad u)`. -/
theorem hasDerivAt_expGrad_angular {u : ℂ → ℝ} {ξ θ : ℝ}
    (hd : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I))
      (Complex.I * deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) θ := by
  have h := hd.hasDerivAt.comp θ (hasDerivAt_logPolar_angular ξ θ)
  simpa [Function.comp, mul_comm] using h

/-! ### Regularity of the pullback and of the holomorphic gradient on the strip -/

/-- A function harmonic on a neighbourhood of each point of a set is real-differentiable there. -/
theorem differentiableAt_of_harmonicOnNhd {u : ℂ → ℝ} {U : Set ℂ}
    (hu : InnerProductSpace.HarmonicOnNhd u U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ u z :=
  (hu z hz).1.differentiableAt (by norm_num)

/-- **Holomorphy of the log-polar gradient.** For `u` harmonic on the collar annulus, `expGrad u`
is complex-differentiable at every point of the strip `{log r₀ < Re w < 0}`. -/
theorem expGrad_differentiableAt {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {w : ℂ}
    (h1 : Real.log r₀ < w.re) (h2 : w.re < 0) :
    DifferentiableAt ℂ (expGrad u) w := by
  have hg : DifferentiableAt ℂ (gradC u) (Complex.exp w) :=
    (gradC_differentiableOn hu).differentiableAt
      ((isOpen_roundAnnulus 0 r₀ 1).mem_nhds (exp_mem_roundAnnulus h0 h1 h2))
  exact ((hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w))

/-- The log-polar gradient is continuous on the strip. -/
theorem continuousOn_expGrad {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (expGrad u) {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} := fun _ hw =>
  (expGrad_differentiableAt h0 hu hw.1 hw.2).continuousAt.continuousWithinAt

/-- The derivative of the log-polar gradient is continuous on the strip: `expGrad u` is
holomorphic on the open strip, hence analytic, and so is its derivative. -/
theorem continuousOn_deriv_expGrad {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (deriv (expGrad u)) {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} := by
  have hdiff : DifferentiableOn ℂ (expGrad u) {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    fun w hw => (expGrad_differentiableAt h0 hu hw.1 hw.2).differentiableWithinAt
  have hanalytic := hdiff.analyticOnNhd (isOpen_logStrip _ _)
  exact (hanalytic.deriv_of_isOpen (isOpen_logStrip _ _)).continuousOn

/-- The log-polar pullback `u ∘ exp` is continuous on the strip. -/
theorem continuousOn_uexp {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (fun w => u (Complex.exp w)) {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} := by
  intro w hw
  have hc : ContinuousAt u (Complex.exp w) :=
    (hu _ (exp_mem_roundAnnulus h0 hw.1 hw.2)).1.continuousAt
  exact (hc.comp (Complex.continuous_exp.continuousAt)).continuousWithinAt

/-! ### Parametric-integral toolbox -/

/-- A set integral over an open interval agrees with the interval integral. -/
theorem integral_Ioo_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℝ) :
    ∫ θ in Ioo a b, F θ = ∫ θ in a..b, F θ := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- A real function with vanishing derivative at every point of an open interval takes the same
value at any two points of the interval. -/
theorem eqOn_Ioo_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) {x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) : f x = f y := by
  have key : ∀ p q : ℝ, p ∈ Ioo a b → q ∈ Ioo a b → p ≤ q → f q = f p := by
    intro p q hp hq hpq
    have hsub : Icc p q ⊆ Ioo a b := fun z hz =>
      ⟨lt_of_lt_of_le hp.1 hz.1, lt_of_le_of_lt hz.2 hq.2⟩
    exact constant_of_has_deriv_right_zero
      (fun z hz => (hf z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => (hf z (hsub (Ico_subset_Icc_self hz))).hasDerivWithinAt)
      q (right_mem_Icc.mpr hpq)
  rcases le_total x y with hxy | hxy
  · exact (key x y hx hy hxy).symm
  · exact key y x hy hx hxy

/-- An inner closed slab `[ξ₀ − δ, ξ₀ + δ]` around a point of an open interval. -/
theorem exists_closed_slab {a b ξ₀ : ℝ} (ha : a < ξ₀) (hb : ξ₀ < b) :
    ∃ δ, 0 < δ ∧ Icc (ξ₀ - δ) (ξ₀ + δ) ⊆ Ioo a b := by
  refine ⟨min (ξ₀ - a) (b - ξ₀) / 2, by
    have h1 : 0 < ξ₀ - a := by linarith
    have h2 : 0 < b - ξ₀ := by linarith
    positivity, fun x hx => ?_⟩
  have h1 : min (ξ₀ - a) (b - ξ₀) / 2 ≤ (ξ₀ - a) / 2 := by
    gcongr
    exact min_le_left _ _
  have h2 : min (ξ₀ - a) (b - ξ₀) / 2 ≤ (b - ξ₀) / 2 := by
    gcongr
    exact min_le_right _ _
  obtain ⟨hx1, hx2⟩ := hx
  exact ⟨by linarith, by linarith⟩

/-- Continuity of a horizontal slice `t ↦ F (x + t·I)` of a function continuous on the strip. -/
theorem continuous_slice_of_continuousOn_logStrip {F : ℂ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F {w : ℂ | a < w.re ∧ w.re < b}) {x : ℝ} (hx1 : a < x) (hx2 : x < b) :
    Continuous fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I) := by
  rw [continuous_iff_continuousAt]
  intro t
  refine ContinuousAt.comp ?_ (by fun_prop)
  refine hF.continuousAt ((isOpen_logStrip a b).mem_nhds ?_)
  simp only [Set.mem_setOf_eq, re_logPolar]
  exact ⟨hx1, hx2⟩

/-- A function continuous on the strip is bounded on every compact slab
`[ξ₀ − δ, ξ₀ + δ] × [−π, π]` of log-polar parameters contained in the strip. -/
theorem exists_bound_on_slab {F : ℂ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F {w : ℂ | a < w.re ∧ w.re < b}) {δ ξ₀ : ℝ}
    (hδsub : Icc (ξ₀ - δ) (ξ₀ + δ) ⊆ Ioo a b) :
    ∃ C : ℝ, ∀ x ∈ Icc (ξ₀ - δ) (ξ₀ + δ), ∀ t ∈ Icc (-π) π,
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hmap : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  set K : Set ℂ := (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
    (Icc (ξ₀ - δ) (ξ₀ + δ) ×ˢ Icc (-π) π) with hK
  have hKcpt : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hmap
  have hKsub : K ⊆ {w : ℂ | a < w.re ∧ w.re < b} := by
    rintro w ⟨p, hp, rfl⟩
    have hmem := hδsub hp.1
    simp only [Set.mem_setOf_eq, re_logPolar]
    exact ⟨hmem.1, hmem.2⟩
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn (hF.mono hKsub)
  exact ⟨C, fun x hx t ht => hC _ ⟨(x, t), ⟨hx, ht⟩, rfl⟩⟩

/-- **Differentiation under the integral sign on the strip.** For integrands `G`, `G'` continuous
on the strip `{a < Re w < b}` such that `G'` is the radial derivative of `G` along every
horizontal line, the angle integral `ξ ↦ ∫_{(−π,π)} G(ξ+θi) dθ` has derivative
`∫_{(−π,π)} G'(ξ₀+θi) dθ` at every `ξ₀ ∈ (a, b)`. -/
theorem hasDerivAt_integral_logStrip {G G' : ℂ → ℝ} {a b ξ₀ : ℝ}
    (hG : ContinuousOn G {w : ℂ | a < w.re ∧ w.re < b})
    (hG' : ContinuousOn G' {w : ℂ | a < w.re ∧ w.re < b})
    (hd : ∀ x θ : ℝ, a < x → x < b →
      HasDerivAt (fun y : ℝ => G ((y : ℂ) + (θ : ℂ) * Complex.I))
        (G' ((x : ℂ) + (θ : ℂ) * Complex.I)) x)
    (ha : a < ξ₀) (hb : ξ₀ < b) :
    HasDerivAt (fun ξ : ℝ => ∫ θ in Ioo (-π) π, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (∫ θ in Ioo (-π) π, G' ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I)) ξ₀ := by
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab ha hb
  obtain ⟨C, hC⟩ := exists_bound_on_slab hG' hδsub
  have hball : ∀ x ∈ Metric.ball ξ₀ δ, x ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := -π) (b := π) (bound := fun _ => C)
    (F := fun (x : ℝ) (t : ℝ) => G ((x : ℂ) + (t : ℂ) * Complex.I))
    (F' := fun (x : ℝ) (t : ℝ) => G' ((x : ℂ) + (t : ℂ) * Complex.I))
    (Metric.ball_mem_nhds ξ₀ hδpos)
    ?_ ?_ ?_ ?_ ?_ ?_
  · have hfun : (fun ξ : ℝ => ∫ θ in Ioo (-π) π, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        = fun ξ : ℝ => ∫ θ in (-π)..π, G ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      funext fun ξ => integral_Ioo_eq_intervalIntegral hπ _
    rw [hfun, integral_Ioo_eq_intervalIntegral hπ]
    exact hmain.2
  · filter_upwards [Ioo_mem_nhds ha hb] with x hx
    exact (continuous_slice_of_continuousOn_logStrip hG hx.1 hx.2).aestronglyMeasurable
  · exact (continuous_slice_of_continuousOn_logStrip hG ha hb).intervalIntegrable _ _
  · exact (continuous_slice_of_continuousOn_logStrip hG' ha hb).aestronglyMeasurable
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [Set.uIoc_of_le hπ] at ht
    exact hC x (hball x hx) t (Ioc_subset_Icc_self ht)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t _ x hx => ?_
    have hmem := hδsub (hball x hx)
    exact hd x t hmem.1 hmem.2

/-- **Continuity of the parametric angle integral on the strip.** For `G` continuous on the strip
`{a < Re w < b}`, the angle integral `ξ ↦ ∫_{(−π,π)} G(ξ+θi) dθ` is continuous on `(a, b)`. -/
theorem continuousOn_integral_logStrip {G : ℂ → ℝ} {a b : ℝ}
    (hG : ContinuousOn G {w : ℂ | a < w.re ∧ w.re < b}) :
    ContinuousOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (Ioo a b) := by
  intro ξ₀ hξ₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab hξ₀.1 hξ₀.2
  obtain ⟨C, hC⟩ := exists_bound_on_slab hG hδsub
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [Ioo_mem_nhds hξ₀.1 hξ₀.2] with x hx
    exact (continuous_slice_of_continuousOn_logStrip hG hx.1 hx.2).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with x hx
    have hx' : x ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    exact hC x hx' θ (Ioo_subset_Icc_self hθ)
  · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
  · refine Eventually.of_forall fun θ => ?_
    refine ContinuousAt.comp ?_ (by fun_prop)
    refine hG.continuousAt ((isOpen_logStrip a b).mem_nhds ?_)
    simp only [Set.mem_setOf_eq, re_logPolar]
    exact hξ₀

/-! ### The circle mean of a harmonic ring potential is affine in the log-radius -/

/-- The circle mean about the origin is the angle integral of the log-polar pullback. -/
theorem logCircleMean_zero_eq (u : ℂ → ℝ) (ξ : ℝ) :
    logCircleMean 0 u ξ
      = ∫ θ in Ioo (-π) π, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  unfold logCircleMean
  simp only [zero_add]

/-- The real part of `expGrad u` is continuous on the strip. -/
theorem continuousOn_expGrad_re {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (fun w => (expGrad u w).re) {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
  Complex.continuous_re.comp_continuousOn (continuousOn_expGrad h0 hu)

/-- The real part of `deriv (expGrad u)` is continuous on the strip. -/
theorem continuousOn_deriv_expGrad_re {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (fun w => (deriv (expGrad u) w).re)
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
  Complex.continuous_re.comp_continuousOn (continuousOn_deriv_expGrad h0 hu)

/-- **Cauchy–Riemann exactness of the flux integrand.** The angle integral of
`Re (deriv (expGrad u))` over a full circle vanishes: the integrand is the exact angular
derivative of `Im (expGrad u)`, which is `2π`-periodic in the angle. -/
theorem integral_re_deriv_expGrad_eq_zero {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ : ℝ}
    (hξ1 : Real.log r₀ < ξ) (hξ2 : ξ < 0) :
    ∫ θ in Ioo (-π) π, (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re = 0 := by
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  have hkey : ∀ θ ∈ uIcc (-π) π,
      HasDerivAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ _
    have hD := hasDerivAt_expGrad_angular (u := u) (ξ := ξ) (θ := θ)
      (expGrad_differentiableAt h0 hu (by rw [re_logPolar]; exact hξ1)
        (by rw [re_logPolar]; exact hξ2))
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [Function.comp, Complex.mul_im] using hcomp
  have hint : IntervalIntegrable
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) volume (-π) π :=
    (continuous_slice_of_continuousOn_logStrip
      (continuousOn_deriv_expGrad_re h0 hu) hξ1 hξ2).intervalIntegrable _ _
  rw [integral_Ioo_eq_intervalIntegral hπ,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hkey hint]
  have hper : expGrad u ((ξ : ℂ) + ((π : ℝ) : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    simp only [expGrad, exp_logPolar_pi_eq]
  rw [hper, sub_self]

/-- **The derivative of the circle mean is the flux integrand.** For `u` harmonic on the collar
annulus, the circle mean `ξ ↦ ∫_{(−π,π)} u(e^{ξ+iθ}) dθ` has derivative
`∫_{(−π,π)} Re (expGrad u (ξ+θi)) dθ` at every `ξ ∈ (log r₀, 0)`. -/
theorem hasDerivAt_logCircleMean {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ : ℝ}
    (hξ1 : Real.log r₀ < ξ) (hξ2 : ξ < 0) :
    HasDerivAt (fun x => logCircleMean 0 u x)
      (∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) ξ := by
  have hfun : (fun x => logCircleMean 0 u x)
      = fun x : ℝ => ∫ θ in Ioo (-π) π, u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) :=
    funext fun x => logCircleMean_zero_eq u x
  rw [hfun]
  exact hasDerivAt_integral_logStrip (continuousOn_uexp h0 hu) (continuousOn_expGrad_re h0 hu)
    (fun x θ hx1 hx2 => hasDerivAt_uexp_radial
      (differentiableAt_of_harmonicOnNhd hu
        (exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact hx1)
          (by rw [re_logPolar]; exact hx2))))
    hξ1 hξ2

/-- **The flux integrand is constant on the collar.** The angle integral of the radial derivative
`Re (expGrad u)` over the circle of log-radius `ξ` does not depend on `ξ ∈ (log r₀, 0)`. -/
theorem integral_expGrad_re_constant {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ η : ℝ}
    (hξ : ξ ∈ Ioo (Real.log r₀) 0) (hη : η ∈ Ioo (Real.log r₀) 0) :
    (∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      = ∫ θ in Ioo (-π) π, (expGrad u ((η : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hd : ∀ x ∈ Ioo (Real.log r₀) 0, HasDerivAt
      (fun y : ℝ => ∫ θ in Ioo (-π) π, (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re) 0 x := by
    intro x hx
    have hstep := hasDerivAt_integral_logStrip (continuousOn_expGrad_re h0 hu)
      (continuousOn_deriv_expGrad_re h0 hu)
      (fun y θ hy1 hy2 => by
        have hD := hasDerivAt_expGrad_radial (u := u) (ξ := y) (θ := θ)
          (expGrad_differentiableAt h0 hu (by rw [re_logPolar]; exact hy1)
            (by rw [re_logPolar]; exact hy2))
        have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hD
        simpa [Function.comp] using hcomp)
      hx.1 hx.2
    rwa [integral_re_deriv_expGrad_eq_zero h0 hu hx.1 hx.2] at hstep
  exact eqOn_Ioo_of_hasDerivAt_zero hd hξ hη

/-- **The circle mean is affine in the log-radius.** For `u` harmonic on the collar annulus
`{r₀ < |z| < 1}` with `0 < r₀ < 1`, there are `a b : ℝ` with
`∫_{(−π,π)} u(e^{ξ+iθ}) dθ = a + b·ξ` for every `ξ ∈ (log r₀, 0)`. -/
theorem logCircleMean_affineOn {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ∃ a b : ℝ, ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = a + b * ξ := by
  have hlog : Real.log r₀ < 0 := Real.log_neg h0 h1
  set ξc : ℝ := Real.log r₀ / 2 with hξc
  have hξcmem : ξc ∈ Ioo (Real.log r₀) 0 := by
    constructor <;> · rw [hξc]; linarith
  set b : ℝ := ∫ θ in Ioo (-π) π, (expGrad u ((ξc : ℂ) + (θ : ℂ) * Complex.I)).re with hb
  refine ⟨logCircleMean 0 u ξc - b * ξc, b, fun ξ hξ => ?_⟩
  have hgderiv : ∀ x ∈ Ioo (Real.log r₀) 0,
      HasDerivAt (fun y => logCircleMean 0 u y - b * y) 0 x := by
    intro x hx
    have hm := hasDerivAt_logCircleMean h0 hu hx.1 hx.2
    have hx' : (∫ θ in Ioo (-π) π, (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re) = b :=
      integral_expGrad_re_constant h0 hu hx hξcmem
    rw [hx'] at hm
    have hsub := hm.sub ((hasDerivAt_id x).const_mul b)
    simpa using hsub
  have hgeq := eqOn_Ioo_of_hasDerivAt_zero hgderiv hξ hξcmem
  simp only at hgeq
  linarith [hgeq]

/-! ### Boundary limit of the circle mean at the unit circle -/

/-- **The circle mean tends to `2π` at the unit circle.** For `u` continuous on the closed collar
`{r₀ ≤ |z| ≤ 1}` with `u = 1` on the unit circle, the circle mean
`ξ ↦ ∫_{(−π,π)} u(e^{ξ+iθ}) dθ` tends to `2π` as `ξ → 0⁻`: the closed collar is compact, so `u`
is uniformly continuous there and `u(e^{ξ+iθ}) → 1` uniformly in the angle. -/
theorem logCircleMean_tendsto_two_pi {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1) :
    Tendsto (fun ξ => logCircleMean 0 u ξ) (𝓝[<] 0) (𝓝 (2 * π)) := by
  have hπpos := Real.pi_pos
  have hKcpt : IsCompact {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
    have hKeq : {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1}
        = Metric.closedBall 0 1 ∩ (Metric.ball 0 r₀)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, Set.mem_compl_iff,
        Metric.mem_ball, not_lt]
      tauto
    rw [hKeq]
    exact (isCompact_closedBall 0 1).inter_right Metric.isOpen_ball.isClosed_compl
  have hunif := hKcpt.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hunif (ε / (4 * π)) (by positivity)
  have hlogneg : Real.log r₀ < 0 := Real.log_neg h0 h1
  refine ⟨min δ₀ (-Real.log r₀), lt_min hδ₀pos (by linarith), fun ξ hξmem hξdist => ?_⟩
  have hξneg : ξ < 0 := hξmem
  have hdist : |ξ| < min δ₀ (-Real.log r₀) := by rwa [Real.dist_eq, sub_zero] at hξdist
  have hξlog : Real.log r₀ < ξ := by
    have habs : |ξ| < -Real.log r₀ := lt_of_lt_of_le hdist (min_le_right _ _)
    rw [abs_of_neg hξneg] at habs
    linarith
  have hξδ₀ : |ξ| < δ₀ := lt_of_lt_of_le hdist (min_le_left _ _)
  -- the moving point on the circle of radius `e^ξ` and its projection to the unit circle
  have hzK : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)
      ∈ {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
    intro θ
    have hnorm : dist (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) 0 = Real.exp ξ := by
      rw [dist_zero_right, Complex.norm_exp, re_logPolar]
    constructor
    · rw [hnorm]
      calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log h0).symm
        _ ≤ Real.exp ξ := Real.exp_le_exp.mpr hξlog.le
    · rw [hnorm]
      calc Real.exp ξ ≤ Real.exp 0 := Real.exp_le_exp.mpr hξneg.le
        _ = 1 := Real.exp_zero
  have hwsphere : ∀ θ : ℝ, dist (Complex.exp ((θ : ℂ) * Complex.I)) 0 = 1 := by
    intro θ
    rw [dist_zero_right, Complex.norm_exp]
    simp
  have hwK : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I)
      ∈ {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} := fun θ =>
    ⟨by rw [hwsphere θ]; exact h1.le, by rw [hwsphere θ]⟩
  -- uniform closeness of the two circles
  have hzw : ∀ θ : ℝ, dist (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I)) < δ₀ := by
    intro θ
    have hfactor : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)
        - Complex.exp ((θ : ℂ) * Complex.I)
        = (Complex.exp ((ξ : ℂ)) - 1) * Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_add]
      ring
    have hn1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [dist_eq_norm, hfactor, norm_mul, hn1, mul_one, ← Complex.ofReal_exp,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hexple : Real.exp ξ ≤ 1 := by
      calc Real.exp ξ ≤ Real.exp 0 := Real.exp_le_exp.mpr hξneg.le
        _ = 1 := Real.exp_zero
    rw [abs_of_nonpos (by linarith)]
    have hineq : 1 - Real.exp ξ ≤ -ξ := by
      have := Real.add_one_le_exp ξ
      linarith
    have habs : -ξ ≤ |ξ| := by rw [abs_of_neg hξneg]
    calc -(Real.exp ξ - 1) = 1 - Real.exp ξ := by ring
      _ ≤ -ξ := hineq
      _ ≤ |ξ| := habs
      _ < δ₀ := hξδ₀
  -- pointwise closeness of the potential to `1`
  have hpt : ∀ θ : ℝ, |u (0 + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - 1| ≤ ε / (4 * π) := by
    intro θ
    have hw1 : u (Complex.exp ((θ : ℂ) * Complex.I)) = 1 :=
      hone _ (Metric.mem_sphere.mpr (hwsphere θ))
    have hclose := hδ₀ _ (hzK θ) _ (hwK θ) (hzw θ)
    rw [Real.dist_eq, hw1] at hclose
    rw [zero_add]
    exact hclose.le
  -- integrability of the circle slice
  have hsub : Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
    intro z hz
    rw [Metric.mem_sphere] at hz
    constructor
    · rw [hz]
      calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log h0).symm
        _ ≤ Real.exp ξ := Real.exp_le_exp.mpr hξlog.le
    · rw [hz]
      calc Real.exp ξ ≤ Real.exp 0 := Real.exp_le_exp.mpr hξneg.le
        _ = 1 := Real.exp_zero
  have hint : IntegrableOn (fun θ : ℝ => u (0 + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Ioo (-π) π) := integrableOn_logCircleMean_param (hcont.mono hsub)
  -- assemble: `m(ξ) − 2π` is the integral of `u − 1`, bounded by `ε/2`
  have h2π : (2 * π : ℝ) = ∫ _ in Ioo (-π) π, (1 : ℝ) := by
    rw [setIntegral_const, measureReal_def, Real.volume_Ioo, smul_eq_mul, mul_one,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmsub : logCircleMean 0 u ξ - 2 * π
      = ∫ θ in Ioo (-π) π, (u (0 + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - 1) := by
    have hm : logCircleMean 0 u ξ
        = ∫ θ in Ioo (-π) π, u (0 + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := rfl
    rw [hm, h2π]
    exact (integral_sub hint (integrableOn_const (hs := measure_Ioo_lt_top.ne))).symm
  have hvol : (volume : Measure ℝ).real (Ioo (-π) π) = 2 * π := by
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-π) π)
    (C := ε / (4 * π)) measure_Ioo_lt_top
    (fun θ _ => by rw [Real.norm_eq_abs]; exact hpt θ)
  rw [hvol] at hbound
  have hhalf : ε / (4 * π) * (2 * π) = ε / 2 := by
    field_simp
    ring
  rw [Real.dist_eq]
  calc |logCircleMean 0 u ξ - 2 * π|
      = ‖∫ θ in Ioo (-π) π, (u (0 + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - 1)‖ := by
        rw [hmsub, Real.norm_eq_abs]
    _ ≤ ε / (4 * π) * (2 * π) := hbound
    _ = ε / 2 := hhalf
    _ < ε := by linarith

/-! ### The Dirichlet energy of a collar sub-annulus as a flux increment -/

/-- **Pointwise polar form of the energy integrand.** The squared operator norm of the real
Fréchet derivative of `u : ℂ → ℝ` equals `|gradC u|²`: expanding `‖L‖² = (L 1)² + (L I)²` in the
orthonormal basis `{1, I}` recovers the norm square of the Wirtinger gradient. -/
theorem nnnorm_fderiv_sq_eq_ofReal_normSq_gradC (u : ℂ → ℝ) (z : ℂ) :
    ((‖fderiv ℝ u z‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (Complex.normSq (gradC u z)) := by
  have hnorm : ‖fderiv ℝ u z‖ ^ 2 = Complex.normSq (gradC u z) := by
    have hbasis := Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ u z)
    rw [Fin.sum_univ_two] at hbasis
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hbasis
    rw [hbasis]
    simp only [gradC, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [← hnorm, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rfl

/-- The Wirtinger gradient of any `u : ℂ → ℝ` is a measurable function. -/
theorem measurable_gradC (u : ℂ → ℝ) : Measurable (gradC u) := by
  have hfder : Measurable fun z : ℂ => fderiv ℝ u z := measurable_fderiv ℝ u
  have hbil : Continuous fun q : (ℂ →L[ℝ] ℝ) × ℂ => q.1 q.2 :=
    isBoundedBilinearMap_apply.continuous
  have h1 : Measurable fun z : ℂ => (fderiv ℝ u z) 1 :=
    hbil.measurable.comp (hfder.prodMk measurable_const)
  have hI : Measurable fun z : ℂ => (fderiv ℝ u z) Complex.I :=
    hbil.measurable.comp (hfder.prodMk measurable_const)
  change Measurable fun z : ℂ =>
    (((fderiv ℝ u z) 1 : ℝ) : ℂ) - Complex.I * (((fderiv ℝ u z) Complex.I : ℝ) : ℂ)
  exact (Complex.measurable_ofReal.comp h1).sub
    ((Complex.measurable_ofReal.comp hI).const_mul Complex.I)

/-- The polar parametrisation at radius `e^ξ` and angle `θ` is the log-polar exponential. -/
theorem polarCoord_symm_exp (ξ θ : ℝ) :
    Complex.polarCoord.symm (Real.exp ξ, θ)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, ← Complex.ofReal_exp]

/-- The exponential image of an open interval. -/
theorem image_exp_Ioo (ξ₁ ξ₂ : ℝ) :
    Real.exp '' Ioo ξ₁ ξ₂ = Ioo (Real.exp ξ₁) (Real.exp ξ₂) := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.exp_lt_exp.mpr hx.1, Real.exp_lt_exp.mpr hx.2⟩
  · intro hr
    have hrpos : 0 < r := lt_trans (Real.exp_pos ξ₁) hr.1
    exact ⟨Real.log r, ⟨(Real.lt_log_iff_exp_lt hrpos).mpr hr.1,
      (Real.log_lt_iff_lt_exp hrpos).mpr hr.2⟩, Real.exp_log hrpos⟩

/-- The Jacobian–gradient combination in log-polar coordinates: the conformal factor `e^{2ξ}`
absorbs into the norm square of `expGrad u`. -/
theorem normSq_expGrad_eq (u : ℂ → ℝ) (ξ θ : ℝ) :
    Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      = Real.exp ξ * (Real.exp ξ
          * Complex.normSq (gradC u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))) := by
  have hsq : Complex.normSq (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      = Real.exp ξ * Real.exp ξ := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, re_logPolar]
    ring
  change Complex.normSq (gradC u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = _
  rw [Complex.normSq_mul, hsq]
  ring

/-- **Log-polar change of variables for the annulus energy.** For any potential `u : ℂ → ℝ`, the
Dirichlet energy over the round annulus `{e^{ξ₁} < |z| < e^{ξ₂}}` is the iterated log-polar
integral of `|expGrad u|²`: the Jacobian of `z = e^{ξ+iθ}` combines with the squared gradient
into the conformally invariant integrand `normSq (expGrad u)`. -/
theorem dirichletEnergy_roundAnnulus_eq_lintegral (u : ℂ → ℝ) (ξ₁ ξ₂ : ℝ) :
    dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
      = ∫⁻ ξ in Ioo ξ₁ ξ₂, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
  classical
  set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Complex.normSq (gradC u z)) with hG
  set R : Set (ℝ × ℝ) := Ioo (Real.exp ξ₁) (Real.exp ξ₂) ×ˢ Ioo (-π) π with hR
  have hGmeas : Measurable G :=
    ENNReal.measurable_ofReal.comp (Complex.continuous_normSq.measurable.comp (measurable_gradC u))
  have hAnnMeas : MeasurableSet (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂)) :=
    (isOpen_roundAnnulus _ _ _).measurableSet
  have hRMeas : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  -- Step 2: polar change of variables to the radius-angle rectangle
  have h2 : ∫⁻ z in RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂), G z
      = ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) := by
    have hcov := Complex.lintegral_comp_polarCoord_symm
      (fun z => (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂)).indicator G z)
    rw [lintegral_indicator hAnnMeas] at hcov
    have hpt : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂)).indicator G
            (Complex.polarCoord.symm p)
          = R.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * G (Complex.polarCoord.symm q))
              p := by
      intro p hp
      rw [polarCoord_target] at hp
      have hnorm : dist (Complex.polarCoord.symm p) 0 = p.1 := by
        rw [dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      by_cases hmem : p.1 ∈ Ioo (Real.exp ξ₁) (Real.exp ξ₂)
      · have hin : Complex.polarCoord.symm p ∈ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂) := by
          simp only [RoundAnnulus, Set.mem_setOf_eq, hnorm]
          exact ⟨hmem.1, hmem.2⟩
        rw [Set.indicator_of_mem hin, Set.indicator_of_mem (Set.mem_prod.mpr ⟨hmem, hp.2⟩),
          smul_eq_mul]
      · have hnotin : Complex.polarCoord.symm p
            ∉ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂) := by
          simp only [RoundAnnulus, Set.mem_setOf_eq, hnorm]
          intro hc
          exact hmem ⟨hc.1, hc.2⟩
        have hnotin' : p ∉ R := fun hc => hmem hc.1
        rw [Set.indicator_of_notMem hnotin, Set.indicator_of_notMem hnotin', smul_zero]
    have hRsub : R ⊆ polarCoord.target := by
      rintro p ⟨hp1, hp2⟩
      rw [polarCoord_target]
      exact ⟨lt_trans (Real.exp_pos ξ₁) hp1.1, hp2⟩
    calc ∫⁻ z in RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂), G z
        = ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂)).indicator G
              (Complex.polarCoord.symm p) := hcov.symm
      _ = ∫⁻ p in polarCoord.target,
            R.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * G (Complex.polarCoord.symm q))
              p := setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt
      _ = ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)
            ∂(volume.restrict polarCoord.target) := lintegral_indicator hRMeas _
      _ = ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) := by
          rw [Measure.restrict_restrict hRMeas, Set.inter_eq_self_of_subset_left hRsub]
  -- Step 3: Tonelli on the rectangle
  have hsymmMeas : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have heq : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p
      rw [Complex.polarCoord_symm_apply]
    rw [heq]
    exact Continuous.measurable (by fun_prop)
  have h3 : ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)
      = ∫⁻ r in Ioo (Real.exp ξ₁) (Real.exp ξ₂), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict R
        = ((volume : Measure ℝ).restrict (Ioo (Real.exp ξ₁) (Real.exp ξ₂))).prod
            ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
      rw [hR, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hprod]
    exact lintegral_prod _
      (((ENNReal.measurable_ofReal.comp measurable_fst).mul
        (hGmeas.comp hsymmMeas)).aemeasurable)
  -- Step 4: radial substitution `r = e^ξ`
  have h4 : ∫⁻ r in Ioo (Real.exp ξ₁) (Real.exp ξ₂), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))
      = ∫⁻ ξ in Ioo ξ₁ ξ₂, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ)) := by
    rw [← image_exp_Ioo ξ₁ ξ₂]
    exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn _
  -- Step 5: absorb the Jacobian into the log-polar gradient
  have h5 : ∀ ξ : ℝ, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ))
      = ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
    intro ξ
    rw [abs_of_pos (Real.exp_pos ξ), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [polarCoord_symm_exp, normSq_expGrad_eq u ξ θ, ENNReal.ofReal_mul (Real.exp_pos ξ).le,
      ENNReal.ofReal_mul (Real.exp_pos ξ).le]
  calc dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
      = ∫⁻ z in RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂), G z :=
        lintegral_congr fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC u z
    _ = ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) := h2
    _ = ∫⁻ r in Ioo (Real.exp ξ₁) (Real.exp ξ₂), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) := h3
    _ = ∫⁻ ξ in Ioo ξ₁ ξ₂, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ)) := h4
    _ = ∫⁻ ξ in Ioo ξ₁ ξ₂, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :=
        lintegral_congr fun ξ => h5 ξ

/-- The ring flux in log-polar form: the integrand `u · (∇u · z)` is `u(e^w) · Re (expGrad u w)`
at `w = ξ + θ·I`. -/
theorem ringFlux_eq (u : ℂ → ℝ) (ξ : ℝ) :
    ringFlux u ξ = ∫ θ in Ioo (-π) π,
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  unfold ringFlux
  congr 1
  funext θ
  rw [fderiv_eq_re_gradC_mul]
  rfl

/-- The imaginary part of `expGrad u` is continuous on the strip. -/
theorem continuousOn_expGrad_im {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (fun w => (expGrad u w).im) {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
  Complex.continuous_im.comp_continuousOn (continuousOn_expGrad h0 hu)

/-- The log-polar gradient takes equal values at the two angle endpoints `±π`. -/
theorem expGrad_logPolar_pi_eq (u : ℂ → ℝ) (ξ : ℝ) :
    expGrad u ((ξ : ℂ) + ((π : ℝ) : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
  simp only [expGrad, exp_logPolar_pi_eq]

/-- **Angular integration by parts.** On the collar strip, the angle integral of
`u(e^{ξ+iθ}) · Re (deriv (expGrad u))` equals the integral of `(Im (expGrad u))²`: the factor
`Re (deriv (expGrad u))` is the exact angular derivative of `Im (expGrad u)`, the angular
derivative of the potential is `−Im (expGrad u)`, and the boundary terms at `θ = ±π` cancel by
`2π`-periodicity. -/
theorem integral_uexp_re_deriv_expGrad {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ : ℝ}
    (hξ1 : Real.log r₀ < ξ) (hξ2 : ξ < 0) :
    ∫ θ in Ioo (-π) π, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  have hcont_f : Continuous fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
    continuous_slice_of_continuousOn_logStrip (continuousOn_uexp h0 hu) hξ1 hξ2
  have hcont_g : Continuous fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im :=
    continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_im h0 hu) hξ1 hξ2
  have hcont_g' : Continuous
      fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re :=
    continuous_slice_of_continuousOn_logStrip (continuousOn_deriv_expGrad_re h0 hu) hξ1 hξ2
  have hf' : ∀ θ ∈ Ioo (min (-π) π) (max (-π) π),
      HasDerivAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
        (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ := fun θ _ =>
    hasDerivAt_uexp_angular (differentiableAt_of_harmonicOnNhd hu
      (exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact hξ1) (by rw [re_logPolar]; exact hξ2)))
  have hg' : ∀ θ ∈ Ioo (min (-π) π) (max (-π) π),
      HasDerivAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ _
    have hD := hasDerivAt_expGrad_angular (u := u) (ξ := ξ) (θ := θ)
      (expGrad_differentiableAt h0 hu (by rw [re_logPolar]; exact hξ1)
        (by rw [re_logPolar]; exact hξ2))
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [Function.comp, Complex.mul_im] using hcomp
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f.continuousOn hcont_g.continuousOn hf' hg'
    (hcont_g.neg.intervalIntegrable _ _) (hcont_g'.intervalIntegrable _ _)
  have halg : ∫ θ in (-π)..π, (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im
      = - ∫ θ in (-π)..π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
    have heq : (fun θ : ℝ => (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
        = fun θ : ℝ => -((expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) := by
      funext θ
      ring
    rw [heq, intervalIntegral.integral_neg]
  rw [integral_Ioo_eq_intervalIntegral hπ, integral_Ioo_eq_intervalIntegral hπ, hIBP, halg,
    exp_logPolar_pi_eq, expGrad_logPolar_pi_eq]
  ring

/-- The squared-gradient angle integral `ξ ↦ ∫_{(−π,π)} |expGrad u (ξ+θi)|² dθ` is continuous on
the collar interval. -/
theorem continuousOn_integral_normSq_expGrad {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    ContinuousOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Ioo (Real.log r₀) 0) :=
  continuousOn_integral_logStrip
    (Complex.continuous_normSq.comp_continuousOn (continuousOn_expGrad h0 hu))

/-- **Derivative of the ring flux.** On the collar strip the ring flux has derivative the full
squared-gradient angle integral `∫_{(−π,π)} |expGrad u|² dθ`: differentiation under the integral
sign and the product rule produce `(Re expGrad u)² + u · Re (deriv (expGrad u))`, and angular
integration by parts converts the second term into `(Im expGrad u)²`. -/
theorem hasDerivAt_ringFlux {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ : ℝ}
    (hξ1 : Real.log r₀ < ξ) (hξ2 : ξ < 0) :
    HasDerivAt (ringFlux u)
      (∫ θ in Ioo (-π) π, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) ξ := by
  have hfun : ringFlux u = fun x : ℝ => ∫ θ in Ioo (-π) π,
      u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re :=
    funext fun x => ringFlux_eq u x
  -- continuity of the integrand and of its radial derivative on the strip
  have hGcont : ContinuousOn (fun w => u (Complex.exp w) * (expGrad u w).re)
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    (continuousOn_uexp h0 hu).mul (continuousOn_expGrad_re h0 hu)
  have hG'cont : ContinuousOn
      (fun w => (expGrad u w).re ^ 2 + u (Complex.exp w) * (deriv (expGrad u) w).re)
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    ((continuousOn_expGrad_re h0 hu).pow 2).add
      ((continuousOn_uexp h0 hu).mul (continuousOn_deriv_expGrad_re h0 hu))
  -- product rule along each radial line
  have hd : ∀ x θ : ℝ, Real.log r₀ < x → x < 0 →
      HasDerivAt (fun y : ℝ => u (Complex.exp ((y : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
            * (deriv (expGrad u) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
    intro x θ hx1 hx2
    have hu' := hasDerivAt_uexp_radial (u := u) (ξ := x) (θ := θ)
      (differentiableAt_of_harmonicOnNhd hu
        (exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact hx1)
          (by rw [re_logPolar]; exact hx2)))
    have hD := hasDerivAt_expGrad_radial (u := u) (ξ := x) (θ := θ)
      (expGrad_differentiableAt h0 hu (by rw [re_logPolar]; exact hx1)
        (by rw [re_logPolar]; exact hx2))
    have hDre : HasDerivAt (fun y : ℝ => (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((deriv (expGrad u) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
      have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hD
      simpa [Function.comp] using hcomp
    have hmul := hu'.mul hDre
    refine hmul.congr_deriv ?_
    ring
  have hDUI := hasDerivAt_integral_logStrip hGcont hG'cont hd hξ1 hξ2
  -- convert the derivative value via angular integration by parts
  have hint1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2) (Ioo (-π) π) :=
    (((continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_re h0 hu) hξ1
      hξ2).pow 2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo (-π) π) :=
    (((continuous_slice_of_continuousOn_logStrip (continuousOn_uexp h0 hu) hξ1 hξ2).mul
      (continuous_slice_of_continuousOn_logStrip (continuousOn_deriv_expGrad_re h0 hu) hξ1
        hξ2)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint3 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) (Ioo (-π) π) :=
    (((continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_im h0 hu) hξ1
      hξ2).pow 2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hval : (∫ θ in Ioo (-π) π,
      ((expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = ∫ θ in Ioo (-π) π, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    rw [integral_add hint1 hint2, integral_uexp_re_deriv_expGrad h0 hu hξ1 hξ2,
      ← integral_add hint1 hint3]
    congr 1
    funext θ
    rw [Complex.normSq_apply]
    ring
  rw [hval] at hDUI
  rw [hfun]
  exact hDUI

/-- **Flux–energy identity on collar sub-annuli.** For `u` harmonic on the collar annulus
`{r₀ < |z| < 1}` and `log r₀ < ξ₁ ≤ ξ₂ < 0`, the Dirichlet energy of `u` over the sub-annulus
`{e^{ξ₁} < |z| < e^{ξ₂}}` equals the flux increment `ringFlux u ξ₂ − ringFlux u ξ₁`. -/
theorem dirichletEnergy_roundAnnulus_eq_ringFlux_sub {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ₁ ξ₂ : ℝ}
    (hξ₁ : Real.log r₀ < ξ₁) (h12 : ξ₁ ≤ ξ₂) (hξ₂ : ξ₂ < 0) :
    dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
      = ENNReal.ofReal (ringFlux u ξ₂ - ringFlux u ξ₁) := by
  rw [dirichletEnergy_roundAnnulus_eq_lintegral u ξ₁ ξ₂]
  have hsub : Icc ξ₁ ξ₂ ⊆ Ioo (Real.log r₀) 0 := fun x hx =>
    ⟨lt_of_lt_of_le hξ₁ hx.1, lt_of_le_of_lt hx.2 hξ₂⟩
  -- inner bridge: the angle `∫⁻` of the continuous nonnegative integrand is an `ofReal`
  have hinner : ∀ ξ ∈ Ioo ξ₁ ξ₂,
      (∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
      = ENNReal.ofReal (∫ θ in Ioo (-π) π,
          Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
    intro ξ hξ
    have hmem := hsub (Ioo_subset_Icc_self hξ)
    have hcont : Continuous fun θ : ℝ =>
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      continuous_slice_of_continuousOn_logStrip
        (Complex.continuous_normSq.comp_continuousOn (continuousOn_expGrad h0 hu))
        hmem.1 hmem.2
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcont.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
      (ae_of_all _ fun θ => Complex.normSq_nonneg _)]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner]
  -- outer bridge and the fundamental theorem of calculus for the flux
  have hQcont : ContinuousOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc ξ₁ ξ₂) :=
    (continuousOn_integral_normSq_expGrad h0 hu).mono hsub
  have hQint : IntegrableOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo ξ₁ ξ₂) :=
    (hQcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hQnn : ∀ ξ : ℝ, 0 ≤ ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun ξ =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hQint (ae_of_all _ fun ξ => hQnn ξ)]
  congr 1
  rw [integral_Ioo_eq_intervalIntegral h12]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => by
      have hmem := hsub (by rwa [uIcc_of_le h12] at hx)
      exact hasDerivAt_ringFlux h0 hu hmem.1 hmem.2)
    ((hQcont.mono (by rw [uIcc_of_le h12])).intervalIntegrable)

/-- **Monotonicity of the ring flux.** For `u` harmonic on the collar annulus, the ring flux is
nondecreasing on `(log r₀, 0)`: its derivative is the nonnegative squared-gradient integral. -/
theorem ringFlux_monotoneOn {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) :
    MonotoneOn (ringFlux u) (Ioo (Real.log r₀) 0) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Ioo (Real.log r₀) 0 := fun z hz =>
    ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := ringFlux u)
    (f' := fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
    (fun z hz => by
      have hmem := hsub (by rwa [uIcc_of_le hxy] at hz)
      exact hasDerivAt_ringFlux h0 hu hmem.1 hmem.2)
    ((((continuousOn_integral_normSq_expGrad h0 hu).mono hsub).mono
      (by rw [uIcc_of_le hxy])).intervalIntegrable)
  have hnn : 0 ≤ ∫ z in x..y, ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((z : ℂ) + (θ : ℂ) * Complex.I)) :=
    intervalIntegral.integral_nonneg hxy fun z _ =>
      setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  linarith [hFTC, hnn]

/-- **The flux integrand equals the slope.** If the circle mean of the ring potential is the
affine function `2π + b·ξ` of the log-radius on the collar, then the angle integral of the
scale-invariant radial derivative `Re (expGrad u)` equals the slope `b` at every log-radius. -/
theorem integral_expGrad_re_eq_slope {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (Real.log r₀) 0) :
    ∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re = b := by
  have hm := hasDerivAt_logCircleMean h0 hu hξ.1 hξ.2
  have haffine : HasDerivAt (fun x => logCircleMean 0 u x) b ξ := by
    have hax : HasDerivAt (fun x : ℝ => 2 * π + b * x) b ξ := by
      simpa using ((hasDerivAt_id ξ).const_mul b).const_add (2 * π)
    refine hax.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with x hx
    exact hslope x hx
  exact hm.unique haffine

/-! ### The outer collar: exhaustion up to the unit circle -/

/-- A set lintegral over a monotone countable union is the supremum of the set lintegrals. -/
theorem lintegral_iUnion_of_monotone {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : ℕ → Set α} (hmeas : ∀ n, MeasurableSet (S n)) (hmono : Monotone S)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in ⋃ n, S n, g x ∂μ = ⨆ n, ∫⁻ x in S n, g x ∂μ := by
  rw [← lintegral_indicator (MeasurableSet.iUnion hmeas) g]
  have hpt : (fun x => (⋃ n, S n).indicator g x)
      = fun x => ⨆ n : ℕ, (S n).indicator g x := by
    funext x
    by_cases hx : x ∈ ⋃ n, S n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      rw [Set.indicator_of_mem hx]
      refine le_antisymm (le_iSup_of_le n (by rw [Set.indicator_of_mem hn])) ?_
      refine iSup_le fun m => ?_
      by_cases hm : x ∈ S m
      · rw [Set.indicator_of_mem hm]
      · rw [Set.indicator_of_notMem hm]
        exact zero_le _
    · rw [Set.indicator_of_notMem hx]
      refine (ENNReal.iSup_eq_zero.mpr fun n => ?_).symm
      exact Set.indicator_of_notMem (fun hc => hx (Set.mem_iUnion.mpr ⟨n, hc⟩)) g
  rw [hpt, lintegral_iSup (fun n => hg.indicator (hmeas n))
    (fun n m hnm x => Set.indicator_le_indicator_of_subset (hmono hnm) (fun _ => zero_le _) x)]
  exact iSup_congr fun n => lintegral_indicator (hmeas n) g

/-- The outer collar `{e^{ξ₁} < |z| < 1}` is the monotone union of the sub-annuli with outer
radii `e^{ξ₁/(n+1)} ↑ 1`. -/
theorem roundAnnulus_outer_eq_iUnion {ξ₁ : ℝ} (hξ₁0 : ξ₁ < 0) :
    RoundAnnulus 0 (Real.exp ξ₁) 1
      = ⋃ n : ℕ, RoundAnnulus 0 (Real.exp ξ₁) (Real.exp (ξ₁ / (n + 1))) := by
  ext z
  simp only [RoundAnnulus, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨h1, h2⟩
    have hzpos : 0 < dist z 0 := lt_trans (Real.exp_pos ξ₁) h1
    have hlog : Real.log (dist z 0) < 0 := Real.log_neg hzpos h2
    obtain ⟨n, hn⟩ := exists_nat_gt (ξ₁ / Real.log (dist z 0))
    have hn1 : ξ₁ / Real.log (dist z 0) < (n : ℝ) + 1 := lt_trans hn (by linarith)
    have hmul : ((n : ℝ) + 1) * Real.log (dist z 0) < ξ₁ :=
      (div_lt_iff_of_neg hlog).mp hn1
    have hstep : Real.log (dist z 0) < ξ₁ / ((n : ℝ) + 1) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      linarith
    exact ⟨n, h1, (Real.log_lt_iff_lt_exp hzpos).mp hstep⟩
  · rintro ⟨n, h1, h2⟩
    refine ⟨h1, lt_trans h2 ?_⟩
    have hneg : ξ₁ / ((n : ℝ) + 1) < 0 :=
      div_neg_of_neg_of_pos hξ₁0 (by positivity)
    calc Real.exp (ξ₁ / ((n : ℝ) + 1)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero

/-- **Flux exhaustion of the outer-collar energy.** For `u` harmonic on the collar annulus and
`log r₀ < ξ₁ < 0`, the Dirichlet energy of `u` over the outer collar `{e^{ξ₁} < |z| < 1}` is the
supremum of the flux increments up to the outer radii `e^{ξ₁/(n+1)} ↑ 1`. -/
theorem dirichletEnergy_outerCollar_eq_iSup_ringFlux {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1)) {ξ₁ : ℝ}
    (hξ₁ : Real.log r₀ < ξ₁) (hξ₁0 : ξ₁ < 0) :
    dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) 1)
      = ⨆ n : ℕ, ENNReal.ofReal (ringFlux u (ξ₁ / (n + 1)) - ringFlux u ξ₁) := by
  have hmono : Monotone fun n : ℕ =>
      RoundAnnulus 0 (Real.exp ξ₁) (Real.exp (ξ₁ / (n + 1))) := by
    intro n m hnm z hz
    refine ⟨hz.1, lt_of_lt_of_le hz.2 (Real.exp_le_exp.mpr ?_)⟩
    have hd : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
      have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      linarith
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    exact mul_le_mul_of_nonpos_left hd hξ₁0.le
  have hgmeas : Measurable fun z : ℂ => ((‖fderiv ℝ u z‖₊ : ℝ≥0∞)) ^ 2 := by
    have heq : (fun z : ℂ => ((‖fderiv ℝ u z‖₊ : ℝ≥0∞)) ^ 2)
        = fun z => ENNReal.ofReal (Complex.normSq (gradC u z)) :=
      funext fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC u z
    rw [heq]
    exact ENNReal.measurable_ofReal.comp
      (Complex.continuous_normSq.measurable.comp (measurable_gradC u))
  calc dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) 1)
      = ∫⁻ z in ⋃ n : ℕ, RoundAnnulus 0 (Real.exp ξ₁) (Real.exp (ξ₁ / (n + 1))),
          ((‖fderiv ℝ u z‖₊ : ℝ≥0∞)) ^ 2 := by
        rw [← roundAnnulus_outer_eq_iUnion hξ₁0]
        rfl
    _ = ⨆ n : ℕ, ∫⁻ z in RoundAnnulus 0 (Real.exp ξ₁) (Real.exp (ξ₁ / (n + 1))),
          ((‖fderiv ℝ u z‖₊ : ℝ≥0∞)) ^ 2 :=
        lintegral_iUnion_of_monotone (fun n => (isOpen_roundAnnulus _ _ _).measurableSet)
          hmono hgmeas
    _ = ⨆ n : ℕ, ENNReal.ofReal (ringFlux u (ξ₁ / (n + 1)) - ringFlux u ξ₁) := by
        refine iSup_congr fun n => ?_
        have hle : ξ₁ ≤ ξ₁ / ((n : ℝ) + 1) := by
          have h1n : 1 / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith [Nat.cast_nonneg (α := ℝ) n]
          calc ξ₁ = ξ₁ * 1 := by ring
            _ ≤ ξ₁ * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonpos_left h1n hξ₁0.le
            _ = ξ₁ / ((n : ℝ) + 1) := by ring
        exact dirichletEnergy_roundAnnulus_eq_ringFlux_sub h0 hu hξ₁ hle
          (div_neg_of_neg_of_pos hξ₁0 (by positivity))

/-! ### The outer logarithmic barrier -/

/-- The logarithm of the norm is harmonic away from the origin: `log ‖z‖` is locally the real
part of a holomorphic branch of the complex logarithm. -/
theorem harmonicAt_log_norm {z : ℂ} (hz : z ≠ 0) :
    InnerProductSpace.HarmonicAt (fun w : ℂ => Real.log ‖w‖) z := by
  simpa using AnalyticAt.harmonicAt_log_norm (f := id) (analyticAt_id) hz

/-- The closed collar `{r ≤ |z| ≤ R}` is a closed set. -/
theorem isClosed_closedCollar (r R : ℝ) :
    IsClosed {z : ℂ | r ≤ dist z 0 ∧ dist z 0 ≤ R} := by
  have h1 : IsClosed {z : ℂ | r ≤ dist z 0} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have h2 : IsClosed {z : ℂ | dist z 0 ≤ R} :=
    isClosed_le (continuous_id.dist continuous_const) continuous_const
  exact h1.inter h2

/-- **Outer logarithmic barrier.** For a ring potential `u` — harmonic on the collar annulus
`{r₀ < |z| < 1}`, continuous on the closed collar, nonnegative, equal to `1` on the unit
circle — the deficit `1 − u` is dominated on the outer sub-annulus `{r₁ < |z| < 1}` by the
harmonic barrier `log |z| / log r₁`, which vanishes on the unit circle and equals `1` on the
circle of radius `r₁`. -/
theorem one_sub_le_log_barrier {u : ℂ → ℝ} {r₀ r₁ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hnn : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z)
    (hr₁ : r₀ < r₁) (hr₁1 : r₁ < 1) :
    ∀ z ∈ RoundAnnulus 0 r₁ 1, 1 - u z ≤ Real.log (dist z 0) / Real.log r₁ := by
  have hr₁0 : 0 < r₁ := lt_trans h0 hr₁
  have hlogr₁ : Real.log r₁ < 0 := Real.log_neg hr₁0 hr₁1
  have hfeq : ∀ z : ℂ, ((fun _ : ℂ => (1 : ℝ)) - u
      - (Real.log r₁)⁻¹ • fun w : ℂ => Real.log ‖w‖) z
      = 1 - u z - Real.log (dist z 0) / Real.log r₁ := by
    intro z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dist_zero_right]
    ring
  set f : ℂ → ℝ := (fun _ : ℂ => (1 : ℝ)) - u
    - (Real.log r₁)⁻¹ • fun w : ℂ => Real.log ‖w‖ with hf
  have hUsub : RoundAnnulus 0 r₁ 1 ⊆ RoundAnnulus 0 r₀ 1 := fun z hz =>
    ⟨lt_trans hr₁ hz.1, hz.2⟩
  have hUK : RoundAnnulus 0 r₁ 1 ⊆ {z : ℂ | r₁ ≤ dist z 0 ∧ dist z 0 ≤ 1} := fun z hz =>
    ⟨hz.1.le, hz.2.le⟩
  have hclU : closure (RoundAnnulus 0 r₁ 1) ⊆ {z : ℂ | r₁ ≤ dist z 0 ∧ dist z 0 ≤ 1} :=
    closure_minimal hUK (isClosed_closedCollar r₁ 1)
  -- the comparison function is harmonic on the outer sub-annulus
  have hharm : InnerProductSpace.HarmonicOnNhd f (RoundAnnulus 0 r₁ 1) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hc
      have h1 : r₁ < dist x 0 := hx.1
      rw [hc, dist_self] at h1
      exact absurd h1 (not_lt.mpr hr₁0.le)
    exact ((InnerProductSpace.harmonicAt_const (1 : ℝ)).sub (hu x (hUsub hx))).sub
      ((harmonicAt_log_norm hx0).const_smul)
  -- continuity on the closure of the outer sub-annulus
  have hfc : ContinuousOn f (closure (RoundAnnulus 0 r₁ 1)) := by
    have hfc' : ContinuousOn (fun z : ℂ => 1 - u z - Real.log (dist z 0) / Real.log r₁)
        {z : ℂ | r₁ ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
      refine (continuousOn_const.sub (hcont.mono fun z hz =>
        ⟨le_trans hr₁.le hz.1, hz.2⟩)).sub (ContinuousOn.div_const ?_ _)
      intro z hz
      have hz0 : dist z 0 ≠ 0 := (lt_of_lt_of_le hr₁0 hz.1).ne'
      have hdc : ContinuousAt (fun w : ℂ => dist w 0) z := by fun_prop
      exact (hdc.log hz0).continuousWithinAt
    exact (hfc'.mono hclU).congr fun z _ => hfeq z
  -- the boundary bound: `f ≤ 0` on the two frontier circles
  have hle : ∀ z ∈ frontier (RoundAnnulus 0 r₁ 1), f z ≤ 0 := by
    intro z hz
    rw [(isOpen_roundAnnulus 0 r₁ 1).frontier_eq] at hz
    have hzK := hclU hz.1
    have hcases : dist z 0 = r₁ ∨ dist z 0 = 1 := by
      rcases lt_or_eq_of_le hzK.1 with h1 | h1
      · rcases lt_or_eq_of_le hzK.2 with h2 | h2
        · exact absurd ⟨h1, h2⟩ hz.2
        · exact Or.inr h2
      · exact Or.inl h1.symm
    rw [show f z = 1 - u z - Real.log (dist z 0) / Real.log r₁ from hfeq z]
    rcases hcases with h | h
    · have hnnz : 0 ≤ u z := hnn z ⟨h ▸ hr₁, h ▸ hr₁1⟩
      rw [h, div_self hlogr₁.ne]
      linarith
    · have huz : u z = 1 := hone z (by simpa [grotzschOuter, Metric.mem_sphere] using h)
      rw [h, huz, Real.log_one, zero_div]
      norm_num
  -- maximum principle
  intro z hz
  have hmax := SubharmonicOn.le_of_frontier_le (isOpen_roundAnnulus 0 r₁ 1)
    (Metric.isBounded_ball.subset fun w hw => Metric.mem_ball.mpr hw.2)
    (HarmonicOnNhd.subharmonicOn hharm) hfc hle z hz
  rw [show f z = 1 - u z - Real.log (dist z 0) / Real.log r₁ from hfeq z] at hmax
  linarith

/-- The logarithmic barrier along circles: at log-radius `ξ ∈ (log r₁, 0)` the deficit of the
ring potential satisfies `1 − u(e^{ξ+iθ}) ≤ ξ / log r₁` at every angle. -/
theorem one_sub_uexp_le_barrier {u : ℂ → ℝ} {r₀ r₁ : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hnn : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z)
    (hr₁ : r₀ < r₁) (hr₁1 : r₁ < 1)
    {ξ : ℝ} (hξ1 : Real.log r₁ < ξ) (hξ2 : ξ < 0) (θ : ℝ) :
    1 - u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≤ ξ / Real.log r₁ := by
  have hr₁0 : 0 < r₁ := lt_trans h0 hr₁
  have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ RoundAnnulus 0 r₁ 1 :=
    exp_mem_roundAnnulus hr₁0 (by rw [re_logPolar]; exact hξ1)
      (by rw [re_logPolar]; exact hξ2)
  have hbar := one_sub_le_log_barrier h0 hu hcont hone hnn hr₁ hr₁1 _ hmem
  have hdist : dist (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) 0 = Real.exp ξ := by
    rw [dist_zero_right, Complex.norm_exp, re_logPolar]
  rwa [hdist, Real.log_exp] at hbar

/-- **Derivative of the deficit square mean.** For `u` harmonic on the collar annulus with circle
mean `2π + b·ξ`, the angle integral `ξ ↦ ∫_{(−π,π)} (1 − u(e^{ξ+iθ}))² dθ` has derivative
`2·(ringFlux u ξ − b)` at every `ξ ∈ (log r₀, 0)`: differentiation under the integral sign gives
the integrand `−2·(1 − u)·Re (expGrad u)`, and the angle integral of `Re (expGrad u)` is the
slope `b`. -/
theorem hasDerivAt_integral_one_sub_sq {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    {ξ : ℝ} (hξ : ξ ∈ Ioo (Real.log r₀) 0) :
    HasDerivAt (fun x : ℝ => ∫ θ in Ioo (-π) π,
        (1 - u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ^ 2)
      (2 * (ringFlux u ξ - b)) ξ := by
  have hGcont : ContinuousOn (fun w => (1 - u (Complex.exp w)) ^ 2)
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    (continuousOn_const.sub (continuousOn_uexp h0 hu)).pow 2
  have hG'cont : ContinuousOn
      (fun w => -2 * ((1 - u (Complex.exp w)) * (expGrad u w).re))
      {w : ℂ | Real.log r₀ < w.re ∧ w.re < 0} :=
    continuousOn_const.mul ((continuousOn_const.sub (continuousOn_uexp h0 hu)).mul
      (continuousOn_expGrad_re h0 hu))
  have hd : ∀ x θ' : ℝ, Real.log r₀ < x → x < 0 →
      HasDerivAt (fun y : ℝ => (1 - u (Complex.exp ((y : ℂ) + (θ' : ℂ) * Complex.I))) ^ 2)
        (-2 * ((1 - u (Complex.exp ((x : ℂ) + (θ' : ℂ) * Complex.I)))
          * (expGrad u ((x : ℂ) + (θ' : ℂ) * Complex.I)).re)) x := by
    intro x θ' hx1 hx2
    have hu' := hasDerivAt_uexp_radial (u := u) (ξ := x) (θ := θ')
      (differentiableAt_of_harmonicOnNhd hu
        (exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact hx1)
          (by rw [re_logPolar]; exact hx2)))
    have hpow := (hu'.const_sub 1).pow 2
    refine hpow.congr_deriv ?_
    push_cast
    ring
  have hDUI := hasDerivAt_integral_logStrip hGcont hG'cont hd hξ.1 hξ.2
  have hint1 : IntegrableOn (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      (Ioo (-π) π) :=
    ((continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_re h0 hu) hξ.1
      hξ.2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo (-π) π) :=
    (((continuous_slice_of_continuousOn_logStrip (continuousOn_uexp h0 hu) hξ.1 hξ.2).mul
      (continuous_slice_of_continuousOn_logStrip (continuousOn_expGrad_re h0 hu) hξ.1
        hξ.2)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hval : (∫ θ in Ioo (-π) π,
      -2 * ((1 - u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = 2 * (ringFlux u ξ - b) := by
    rw [integral_const_mul]
    have hsplit : (∫ θ in Ioo (-π) π,
        (1 - u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
          * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        = (∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
          - ∫ θ in Ioo (-π) π, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
              * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
      rw [← integral_sub hint1 hint2]
      congr 1
      funext θ
      ring
    rw [hsplit, integral_expGrad_re_eq_slope h0 hu hslope hξ, ← ringFlux_eq]
    ring
  rw [hval] at hDUI
  exact hDUI

/-- **Boundary limit of the ring flux.** For a ring potential `u` — harmonic on the collar
annulus, continuous on the closed collar, with values in `[0, 1]`, equal to `1` on the unit
circle — whose circle mean is `2π + b·ξ` in the log-radius, the ring flux tends to the slope `b`
at the unit circle: the deficit square mean `ψ(ξ) = ∫ (1−u)² dθ` is `O(ξ²)` by the logarithmic
barrier, its derivative is `2·(ringFlux − b)`, and the monotonicity of the flux squeezes
`ringFlux − b → 0`. -/
theorem ringFlux_tendsto_slope {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ) :
    Tendsto (ringFlux u) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
  have hπpos := Real.pi_pos
  set r₁ : ℝ := (r₀ + 1) / 2 with hr₁def
  have hr₁ : r₀ < r₁ := by rw [hr₁def]; linarith
  have hr₁1 : r₁ < 1 := by rw [hr₁def]; linarith
  have hr₁0 : 0 < r₁ := lt_trans h0 hr₁
  have hL : Real.log r₁ < 0 := Real.log_neg hr₁0 hr₁1
  have hLr₀ : Real.log r₀ < Real.log r₁ := Real.log_lt_log h0 hr₁
  set C : ℝ := 2 * π / (Real.log r₁) ^ 2 with hCdef
  set ψ : ℝ → ℝ := fun x => ∫ θ in Ioo (-π) π,
      (1 - u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ^ 2 with hψdef
  have hψnn : ∀ x : ℝ, 0 ≤ ψ x := fun x =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => sq_nonneg _
  -- quadratic decay of the deficit square mean from the logarithmic barrier
  have hψbound : ∀ x ∈ Ioo (Real.log r₁) 0, ψ x ≤ C * x ^ 2 := by
    intro x hx
    have hbound : ∀ θ ∈ Ioo (-π) π,
        ‖(1 - u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ^ 2‖
          ≤ (x / Real.log r₁) ^ 2 := by
      intro θ _
      have hmem : Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ RoundAnnulus 0 r₀ 1 :=
        exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact lt_trans hLr₀ hx.1)
          (by rw [re_logPolar]; exact hx.2)
      have h01 := hrange _ hmem
      have hbar := one_sub_uexp_le_barrier h0 hu hcont hone
        (fun z hz => (hrange z hz).1) hr₁ hr₁1 hx.1 hx.2 θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hbar, h01.2]
    have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-π) π)
      (C := (x / Real.log r₁) ^ 2) measure_Ioo_lt_top hbound
    have hvol : (volume : Measure ℝ).real (Ioo (-π) π) = 2 * π := by
      rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol] at hnorm
    calc ψ x ≤ ‖ψ x‖ := le_abs_self _
      _ ≤ (x / Real.log r₁) ^ 2 * (2 * π) := hnorm
      _ = C * x ^ 2 := by rw [hCdef, div_pow]; field_simp
  have hderiv : ∀ t ∈ Ioo (Real.log r₀) 0, HasDerivAt ψ (2 * (ringFlux u t - b)) t :=
    fun t ht => hasDerivAt_integral_one_sub_sq h0 hu hslope ht
  have hmono := ringFlux_monotoneOn h0 hu
  have hFluxCont : ∀ t ∈ Ioo (Real.log r₀) 0,
      ContinuousAt (fun s : ℝ => 2 * (ringFlux u s - b)) t := by
    intro t ht
    have h1 : ContinuousAt (ringFlux u) t := (hasDerivAt_ringFlux h0 hu ht.1 ht.2).continuousAt
    exact continuousAt_const.mul (h1.sub continuousAt_const)
  have hFTC : ∀ {x y : ℝ}, x ∈ Ioo (Real.log r₀) 0 → y ∈ Ioo (Real.log r₀) 0 → x ≤ y →
      ψ y - ψ x = ∫ t in x..y, 2 * (ringFlux u t - b) := by
    intro x y hx hy hxy
    have hsub : Icc x y ⊆ Ioo (Real.log r₀) 0 := fun t ht =>
      ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv t (hsub (by rwa [uIcc_of_le hxy] at ht)))
      (ContinuousOn.intervalIntegrable fun t ht =>
        (hFluxCont t (hsub (by rwa [uIcc_of_le hxy] at ht))).continuousWithinAt)).symm
  -- upper squeeze bound on `(log r₁, 0)`
  have hupper : ∀ ξ ∈ Ioo (Real.log r₁) 0, ringFlux u ξ - b ≤ C * (-ξ) / 4 := by
    intro ξ hξmem
    have hξneg : ξ < 0 := hξmem.2
    have hξIoo : ξ ∈ Ioo (Real.log r₀) 0 := ⟨lt_trans hLr₀ hξmem.1, hξneg⟩
    have hhalfIoo : ξ / 2 ∈ Ioo (Real.log r₀) 0 := ⟨lt_trans hξIoo.1 (by linarith), by linarith⟩
    have hhalfL : ξ / 2 ∈ Ioo (Real.log r₁) 0 := ⟨lt_trans hξmem.1 (by linarith), by linarith⟩
    have hle2 : ξ ≤ ξ / 2 := by linarith
    have hsub : Icc ξ (ξ / 2) ⊆ Ioo (Real.log r₀) 0 := fun t ht =>
      ⟨lt_of_lt_of_le hξIoo.1 ht.1, lt_of_le_of_lt ht.2 hhalfIoo.2⟩
    have hint : IntervalIntegrable (fun t => 2 * (ringFlux u t - b)) volume ξ (ξ / 2) :=
      ContinuousOn.intervalIntegrable fun t ht =>
        (hFluxCont t (hsub (by rwa [uIcc_of_le hle2] at ht))).continuousWithinAt
    have hmonoInt : (∫ _ in ξ..(ξ / 2), 2 * (ringFlux u ξ - b))
        ≤ ∫ t in ξ..(ξ / 2), 2 * (ringFlux u t - b) := by
      refine intervalIntegral.integral_mono_on hle2 intervalIntegrable_const hint fun t ht => ?_
      have := hmono hξIoo (hsub ht) ht.1
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmonoInt
    have hkey : (ξ / 2 - ξ) * (2 * (ringFlux u ξ - b)) ≤ C * (ξ / 2) ^ 2 :=
      hmonoInt.trans (by linarith [hFTC hξIoo hhalfIoo hle2, hψbound _ hhalfL, hψnn ξ])
    nlinarith [hkey, hξneg]
  -- lower squeeze bound on `(log r₁ / 2, 0)`
  have hlower : ∀ ξ ∈ Ioo (Real.log r₁ / 2) 0, 2 * C * ξ ≤ ringFlux u ξ - b := by
    intro ξ hξmem
    have hξneg : ξ < 0 := hξmem.2
    have h2ξL : 2 * ξ ∈ Ioo (Real.log r₁) 0 := ⟨by linarith [hξmem.1], by linarith⟩
    have h2ξIoo : 2 * ξ ∈ Ioo (Real.log r₀) 0 := ⟨lt_trans hLr₀ h2ξL.1, h2ξL.2⟩
    have hξIoo : ξ ∈ Ioo (Real.log r₀) 0 := ⟨by linarith [h2ξIoo.1], hξneg⟩
    have hle2 : 2 * ξ ≤ ξ := by linarith
    have hsub : Icc (2 * ξ) ξ ⊆ Ioo (Real.log r₀) 0 := fun t ht =>
      ⟨lt_of_lt_of_le h2ξIoo.1 ht.1, lt_of_le_of_lt ht.2 hξIoo.2⟩
    have hint : IntervalIntegrable (fun t => 2 * (ringFlux u t - b)) volume (2 * ξ) ξ :=
      ContinuousOn.intervalIntegrable fun t ht =>
        (hFluxCont t (hsub (by rwa [uIcc_of_le hle2] at ht))).continuousWithinAt
    have hmonoInt : (∫ t in (2 * ξ)..ξ, 2 * (ringFlux u t - b))
        ≤ ∫ _ in (2 * ξ)..ξ, 2 * (ringFlux u ξ - b) := by
      refine intervalIntegral.integral_mono_on hle2 hint intervalIntegrable_const fun t ht => ?_
      have := hmono (hsub ht) hξIoo ht.2
      linarith
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmonoInt
    have hkey : -(C * (2 * ξ) ^ 2) ≤ (ξ - 2 * ξ) * (2 * (ringFlux u ξ - b)) :=
      le_trans (by linarith [hFTC h2ξIoo hξIoo hle2, hψbound _ h2ξL, hψnn ξ]) hmonoInt
    nlinarith [hkey, hξneg]
  -- squeeze
  have hL2 : Real.log r₁ / 2 < 0 := by linarith
  have hup' : ∀ᶠ ξ in 𝓝[<] (0 : ℝ), ringFlux u ξ ≤ b + C * (-ξ) / 4 := by
    filter_upwards [Ioo_mem_nhdsLT hL2] with ξ hξ
    have h' := hupper ξ ⟨by linarith [hξ.1], hξ.2⟩
    linarith
  have hlo' : ∀ᶠ ξ in 𝓝[<] (0 : ℝ), b + 2 * C * ξ ≤ ringFlux u ξ := by
    filter_upwards [Ioo_mem_nhdsLT hL2] with ξ hξ
    have h' := hlower ξ hξ
    linarith
  have htop : Tendsto (fun ξ : ℝ => b + C * (-ξ) / 4) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
    have hc : Continuous fun ξ : ℝ => b + C * (-ξ) / 4 := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  have hbot : Tendsto (fun ξ : ℝ => b + 2 * C * ξ) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
    have hc : Continuous fun ξ : ℝ => b + 2 * C * ξ := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hbot htop hlo' hup'

/-- **The collar circle mean is `2π + b·ξ`.** For a ring potential harmonic on the collar
annulus, continuous on the closed collar, equal to `1` on the unit circle, the affine circle
mean has intercept `2π` at the unit circle: there is a slope `b` with
`logCircleMean 0 u ξ = 2π + b·ξ` on `(log r₀, 0)`. -/
theorem exists_logCircleMean_slope {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1) :
    ∃ b : ℝ, ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ := by
  obtain ⟨a, b, hab⟩ := logCircleMean_affineOn h0 h1 hu
  have hlim := logCircleMean_tendsto_two_pi h0 h1 hcont hone
  have hlog : Real.log r₀ < 0 := Real.log_neg h0 h1
  have haff : Tendsto (fun ξ : ℝ => a + b * ξ) (𝓝[<] (0 : ℝ)) (𝓝 a) := by
    have hc : Continuous fun ξ : ℝ => a + b * ξ := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simpa using this
  have hcong : Tendsto (fun ξ => logCircleMean 0 u ξ) (𝓝[<] (0 : ℝ)) (𝓝 a) := by
    refine haff.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hlog] with ξ hξ
    exact (hab ξ hξ).symm
  have ha : a = 2 * π := tendsto_nhds_unique hcong hlim
  exact ⟨b, fun ξ hξ => by rw [hab ξ hξ, ha]⟩

/-- **Exact outer-collar energy.** For a ring potential with values in `[0, 1]`, equal to `1` on
the unit circle, whose circle mean is `2π + b·ξ`, the Dirichlet energy over the outer collar
`{e^{ξ₁} < |z| < 1}` equals `b − ringFlux u ξ₁` exactly: the flux increments to the exhausting
radii converge to the boundary flux `b`. -/
theorem dirichletEnergy_outerCollar_eq_ofReal_sub {u : ℂ → ℝ} {r₀ b : ℝ} (h0 : 0 < r₀)
    (h1 : r₀ < 1)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    {ξ₁ : ℝ} (hξ₁ : ξ₁ ∈ Ioo (Real.log r₀) 0) :
    dirichletEnergy u (RoundAnnulus 0 (Real.exp ξ₁) 1)
      = ENNReal.ofReal (b - ringFlux u ξ₁) := by
  rw [dirichletEnergy_outerCollar_eq_iSup_ringFlux h0 hu hξ₁.1 hξ₁.2]
  have hmem : ∀ n : ℕ, ξ₁ / (n + 1) ∈ Ioo (Real.log r₀) 0 := by
    intro n
    constructor
    · refine lt_of_lt_of_le hξ₁.1 ?_
      have h1n : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      calc ξ₁ = ξ₁ * 1 := by ring
        _ ≤ ξ₁ * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonpos_left h1n hξ₁.2.le
        _ = ξ₁ / ((n : ℝ) + 1) := by ring
    · exact div_neg_of_neg_of_pos hξ₁.2 (by positivity)
  have hseqmono : Monotone fun n : ℕ =>
      ENNReal.ofReal (ringFlux u (ξ₁ / (n + 1)) - ringFlux u ξ₁) := by
    intro n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : ξ₁ / ((n : ℝ) + 1) ≤ ξ₁ / ((m : ℝ) + 1) := by
      have hd : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
        have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
        linarith
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)
        (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      exact mul_le_mul_of_nonpos_left hd hξ₁.2.le
    have := ringFlux_monotoneOn h0 hu (hmem n) (hmem m) hle
    linarith
  have htendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (ringFlux u (ξ₁ / (n + 1))
      - ringFlux u ξ₁)) atTop (𝓝 (ENNReal.ofReal (b - ringFlux u ξ₁))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine Tendsto.sub_const ?_ _
    refine (ringFlux_tendsto_slope h0 h1 hu hcont hone hrange hslope).comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => Set.mem_Iio.mpr (hmem n).2)
    have h0' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := h0'.const_mul ξ₁
    simpa [one_div, div_eq_mul_inv] using hmul
  exact tendsto_nhds_unique (tendsto_atTop_iSup hseqmono) htendsto

/-! ### Null sets and energy over sets differing by a null set -/

/-- The real axis `{z : ℂ | z.im = 0}` has planar Lebesgue measure zero: it is a proper real
subspace of `ℂ`. -/
theorem volume_realAxis_eq_zero :
    (volume : Measure ℂ) {z : ℂ | z.im = 0} = 0 := by
  have hker : {z : ℂ | z.im = 0} = (LinearMap.ker Complex.imCLM.toLinearMap : Set ℂ) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [hker]
  refine MeasureTheory.Measure.addHaar_submodule _ _ ?_
  intro htop
  have hI : Complex.I ∈ (⊤ : Submodule ℝ ℂ) := Submodule.mem_top
  rw [← htop, LinearMap.mem_ker] at hI
  simp at hI

/-- The Grötzsch slit `grotzschInner s` has planar Lebesgue measure zero: it lies in the real
axis. -/
theorem volume_grotzschInner_eq_zero {s : ℝ} (hs0 : 0 ≤ s) :
    (volume : Measure ℂ) (grotzschInner s) = 0 := by
  refine measure_mono_null (fun z hz => ?_) volume_realAxis_eq_zero
  rw [grotzschInner_eq hs0] at hz
  exact hz.1

/-- The Dirichlet energy is unchanged when the domain is enlarged or shrunk by a null set. -/
theorem dirichletEnergy_congr_ae {u : ℂ → ℝ} {U V : Set ℂ}
    (h : U =ᵐ[volume] V) : dirichletEnergy u U = dirichletEnergy u V := by
  unfold dirichletEnergy
  rw [Measure.restrict_congr_set h]

/-- The Grötzsch ring differs from the open unit disk by the null slit, so their Dirichlet
energies agree. -/
theorem dirichletEnergy_grotzschRing_eq_ball {u : ℂ → ℝ} {s : ℝ} (hs0 : 0 ≤ s) :
    dirichletEnergy u (grotzschRing s) = dirichletEnergy u (Metric.ball (0 : ℂ) 1) := by
  refine dirichletEnergy_congr_ae ?_
  rw [ae_eq_set]
  refine ⟨measure_mono_null (fun z hz => absurd hz.1.1 hz.2) measure_empty, ?_⟩
  refine measure_mono_null (fun z hz => ?_) (volume_grotzschInner_eq_zero hs0)
  by_contra hno
  exact hz.2 ⟨hz.1, hno⟩

/-- The circle `{z : ℂ | dist z 0 = s}` has planar Lebesgue measure zero. -/
theorem volume_sphere_eq_zero (s : ℝ) :
    (volume : Measure ℂ) {z : ℂ | dist z 0 = s} = 0 := by
  have hle : {z : ℂ | dist z 0 = s} ⊆ Metric.sphere (0 : ℂ) s := fun z hz =>
    Metric.mem_sphere.mpr hz
  exact measure_mono_null hle (MeasureTheory.Measure.addHaar_sphere _ _ _)

/-- **Radial split of the disk energy.** For any potential `u`, the Dirichlet energy over the
open unit disk splits along the circle `|z| = s` into the inner-disk energy and the outer round
annulus energy: the separating circle is null. -/
theorem dirichletEnergy_ball_split {u : ℂ → ℝ} {s : ℝ} (hs1 : s < 1) :
    dirichletEnergy u (Metric.ball (0 : ℂ) 1)
      = dirichletEnergy u (Metric.ball (0 : ℂ) s)
        + dirichletEnergy u (RoundAnnulus 0 s 1) := by
  unfold dirichletEnergy
  set g : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ^ 2 with hg
  have hballmeas : MeasurableSet (Metric.ball (0 : ℂ) s) := Metric.isOpen_ball.measurableSet
  have hannmeas : MeasurableSet (RoundAnnulus 0 s 1) := (isOpen_roundAnnulus _ _ _).measurableSet
  have hdisj : Disjoint (Metric.ball (0 : ℂ) s) (RoundAnnulus 0 s 1) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact absurd hz' (fun h => absurd (Metric.mem_ball.mp hz) (not_lt.mpr h.1.le))
  have hsplit : Metric.ball (0 : ℂ) 1
      =ᵐ[volume] (Metric.ball (0 : ℂ) s ∪ RoundAnnulus 0 s 1 : Set ℂ) := by
    rw [ae_eq_set]
    refine ⟨measure_mono_null (fun z hz => ?_) (volume_sphere_eq_zero s), ?_⟩
    · have hzball : dist z 0 < 1 := Metric.mem_ball.mp hz.1
      have hznotin : z ∉ Metric.ball (0 : ℂ) s ∪ RoundAnnulus 0 s 1 := hz.2
      rw [Set.mem_union, Metric.mem_ball, not_or] at hznotin
      have h1 : ¬ dist z 0 < s := hznotin.1
      have h2 : ¬ (s < dist z 0 ∧ dist z 0 < 1) := hznotin.2
      have : ¬ s < dist z 0 := fun h => h2 ⟨h, hzball⟩
      exact le_antisymm (not_lt.mp this) (not_lt.mp h1)
    · refine measure_mono_null (fun z hz => ?_) measure_empty
      exfalso
      rcases hz.1 with hb | ha
      · exact hz.2 (Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hb) hs1))
      · exact hz.2 (Metric.mem_ball.mpr ha.2)
  rw [Measure.restrict_congr_set hsplit, ← lintegral_union hannmeas hdisj]

/-- The full outer annulus `{s < |z| < 1}` is the monotone union of the sub-annuli whose inner
radii `e^{ξ_n} ↓ s` shrink toward `s`, where `ξ_n = (log s)·(n+1)/(n+2)`. -/
theorem roundAnnulus_full_eq_iUnion {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    RoundAnnulus 0 s 1
      = ⋃ n : ℕ, RoundAnnulus 0 (Real.exp (Real.log s * (n + 1) / (n + 2))) 1 := by
  have hL : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlt0 : ∀ n : ℕ, Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) < 0 := by
    intro n
    rw [mul_div_assoc]
    exact mul_neg_of_neg_of_pos hL (by positivity)
  have hgtL : ∀ n : ℕ, Real.log s < Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
    intro n
    have hc : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    rw [mul_div_assoc]
    calc Real.log s = Real.log s * 1 := by ring
      _ < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := mul_lt_mul_of_neg_left hc hL
  have hexp : ∀ n : ℕ, Real.exp (Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2)) < 1 := fun n =>
    Real.exp_lt_one_iff.mpr (hlt0 n)
  have hgt : ∀ n : ℕ, s < Real.exp (Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := fun n =>
    (Real.log_lt_iff_lt_exp hs0).mp (hgtL n)
  ext z
  simp only [RoundAnnulus, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨h1, h2⟩
    have hzpos : 0 < dist z 0 := lt_trans hs0 h1
    have hlog : Real.log s < Real.log (dist z 0) := Real.log_lt_log hs0 h1
    -- pick `n` large enough that `ξ_n < log (dist z 0)`
    have htend : Filter.Tendsto
        (fun n : ℕ => Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2)) Filter.atTop
        (𝓝 (Real.log s)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) Filter.atTop
          (𝓝 1) := by
        have hz : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hz2 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
          have := (hz.comp (Filter.tendsto_add_atTop_nat 1))
          refine this.congr fun n => ?_
          simp only [Function.comp_apply]
          push_cast
          ring_nf
        have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hz2
        rw [sub_zero] at hsub
        refine hsub.congr fun n => ?_
        have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
        field_simp
        ring
      have h2 := (h1.const_mul (Real.log s))
      simp only [mul_one] at h2
      convert h2 using 2 with n
      ring
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) < Real.log (dist z 0) :=
      htend.eventually_lt_const hlog
    obtain ⟨n, hn⟩ := hev.exists
    refine ⟨n, ?_, h2⟩
    calc Real.exp (Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2))
        < Real.exp (Real.log (dist z 0)) := Real.exp_lt_exp.mpr hn
      _ = dist z 0 := Real.exp_log hzpos
  · rintro ⟨n, h1, h2⟩
    exact ⟨lt_trans (hgt n) h1, h2⟩

/-- **Exact outer-annulus energy.** For a ring potential `v` on the Grötzsch ring with values in
`[0, 1]`, equal to `1` on the unit circle, whose circle mean is `2π + b·ξ`, the Dirichlet energy
over the full outer annulus `{s < |z| < 1}` is the supremum of the flux increments up to the
exhausting inner radii `e^{ξ_n} ↓ s`. -/
theorem dirichletEnergy_fullAnnulus_eq_iSup {v : ℂ → ℝ} {s b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hu : InnerProductSpace.HarmonicOnNhd v (RoundAnnulus 0 s 1))
    (hcont : ContinuousOn v {z : ℂ | s ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, v z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 s 1, 0 ≤ v z ∧ v z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + b * ξ) :
    dirichletEnergy v (RoundAnnulus 0 s 1)
      = ⨆ n : ℕ, ENNReal.ofReal (b - ringFlux v (Real.log s * (n + 1) / (n + 2))) := by
  have hL : Real.log s < 0 := Real.log_neg hs0 hs1
  set ξf : ℕ → ℝ := fun n => Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) with hξf
  have hξmem : ∀ n : ℕ, ξf n ∈ Ioo (Real.log s) 0 := by
    intro n
    refine ⟨?_, ?_⟩
    · have hc : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      have : Real.log s * 1 < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
        mul_lt_mul_of_neg_left hc hL
      simp only [hξf, mul_one] at this ⊢
      calc Real.log s = Real.log s * 1 := by ring
        _ < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := mul_lt_mul_of_neg_left hc hL
        _ = Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by ring
    · have hpos : 0 < ((n : ℝ) + 1) / ((n : ℝ) + 2) := by positivity
      simp only [hξf]
      rw [mul_div_assoc]
      exact mul_neg_of_neg_of_pos hL hpos
  have hgmeas : Measurable fun z : ℂ => ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 := by
    have heq : (fun z : ℂ => ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2)
        = fun z => ENNReal.ofReal (Complex.normSq (gradC v z)) :=
      funext fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC v z
    rw [heq]
    exact ENNReal.measurable_ofReal.comp
      (Complex.continuous_normSq.measurable.comp (measurable_gradC v))
  have hmono : Monotone fun n : ℕ => RoundAnnulus 0 (Real.exp (ξf n)) 1 := by
    intro n m hnm z hz
    refine ⟨lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hz.1, hz.2⟩
    have hcast : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    simp only [hξf]
    rw [mul_div_assoc, mul_div_assoc]
    apply mul_le_mul_of_nonpos_left _ hL.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcast]
  calc dirichletEnergy v (RoundAnnulus 0 s 1)
      = ∫⁻ z in ⋃ n : ℕ, RoundAnnulus 0 (Real.exp (ξf n)) 1,
          ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 := by
        rw [← roundAnnulus_full_eq_iUnion hs0 hs1]
        rfl
    _ = ⨆ n : ℕ, ∫⁻ z in RoundAnnulus 0 (Real.exp (ξf n)) 1,
          ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 :=
        lintegral_iUnion_of_monotone (fun n => (isOpen_roundAnnulus _ _ _).measurableSet)
          hmono hgmeas
    _ = ⨆ n : ℕ, ENNReal.ofReal (b - ringFlux v (ξf n)) := by
        refine iSup_congr fun n => ?_
        have := dirichletEnergy_outerCollar_eq_ofReal_sub hs0 hs1 hu hcont hone hrange hslope
          (hξmem n)
        exact this

/-! ### Angle-generalized differentiation under the integral sign -/

/-- The **log-polar strip box** `{a < Re w < b, c ≤ Im w ≤ d}`: the vertical strip of
log-radii `(a, b)`, closed in the angle direction over `[c, d]`. -/
def stripBox (a b c d : ℝ) : Set ℂ :=
  {w : ℂ | a < w.re ∧ w.re < b ∧ c ≤ w.im ∧ w.im ≤ d}

/-- Continuity of a horizontal slice `t ↦ F (x + t·I)` over `[c, d]` of a function continuous on
the strip box. -/
theorem continuousOn_slice_of_continuousOn_stripBox {F : ℂ → ℝ} {a b c d : ℝ}
    (hF : ContinuousOn F (stripBox a b c d)) {x : ℝ} (hx1 : a < x) (hx2 : x < b) :
    ContinuousOn (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) (Icc c d) := by
  have hmapsto : Set.MapsTo (fun t : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I))
      (Icc c d) (stripBox a b c d) := by
    intro s hs
    simp only [stripBox, Set.mem_setOf_eq, re_logPolar, im_logPolar]
    exact ⟨hx1, hx2, hs.1, hs.2⟩
  exact hF.comp (by fun_prop) hmapsto

/-- A function continuous on the strip box is bounded on every compact slab
`[ξ₀ − δ, ξ₀ + δ] × [c, d]` contained in the strip box. -/
theorem exists_bound_on_stripBox {F : ℂ → ℝ} {a b c d : ℝ}
    (hF : ContinuousOn F (stripBox a b c d)) {δ ξ₀ : ℝ}
    (hδsub : Icc (ξ₀ - δ) (ξ₀ + δ) ⊆ Ioo a b) :
    ∃ C : ℝ, ∀ x ∈ Icc (ξ₀ - δ) (ξ₀ + δ), ∀ t ∈ Icc c d,
      ‖F ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hmap : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  set K : Set ℂ := (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
    (Icc (ξ₀ - δ) (ξ₀ + δ) ×ˢ Icc c d) with hK
  have hKcpt : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hmap
  have hKsub : K ⊆ stripBox a b c d := by
    rintro w ⟨p, hp, rfl⟩
    have hmem := hδsub hp.1
    simp only [stripBox, Set.mem_setOf_eq, re_logPolar, im_logPolar]
    exact ⟨hmem.1, hmem.2, hp.2.1, hp.2.2⟩
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn (hF.mono hKsub)
  exact ⟨C, fun x hx t ht => hC _ ⟨(x, t), ⟨hx, ht⟩, rfl⟩⟩

/-- **Angle-generalized differentiation under the integral sign.** For an integrand `G` continuous
on the strip box `{a < Re w < b, c ≤ Im w ≤ d}`, with radial-derivative function `G'` continuous
there and equal to the radial derivative of `G` along each horizontal line at every interior angle
`θ ∈ (c, d)`, the angle integral `ξ ↦ ∫_{(c,d)} G(ξ+θi) dθ` has derivative
`∫_{(c,d)} G'(ξ₀+θi) dθ` at every `ξ₀ ∈ (a, b)`. -/
theorem hasDerivAt_integral_stripBox {G G' : ℂ → ℝ} {a b c d ξ₀ : ℝ} (hcd : c ≤ d)
    (hG : ContinuousOn G (stripBox a b c d))
    (hG' : ContinuousOn G' (stripBox a b c d))
    (hd : ∀ x θ : ℝ, a < x → x < b → c < θ → θ < d →
      HasDerivAt (fun y : ℝ => G ((y : ℂ) + (θ : ℂ) * Complex.I))
        (G' ((x : ℂ) + (θ : ℂ) * Complex.I)) x)
    (ha : a < ξ₀) (hb : ξ₀ < b) :
    HasDerivAt (fun ξ : ℝ => ∫ θ in Ioo c d, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      (∫ θ in Ioo c d, G' ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I)) ξ₀ := by
  obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab ha hb
  obtain ⟨C, hC⟩ := exists_bound_on_stripBox hG' hδsub
  have hball : ∀ x ∈ Metric.ball ξ₀ δ, x ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hGslice : ∀ x : ℝ, a < x → x < b →
      ContinuousOn (fun t : ℝ => G ((x : ℂ) + (t : ℂ) * Complex.I)) (Icc c d) :=
    fun x hx1 hx2 => continuousOn_slice_of_continuousOn_stripBox hG hx1 hx2
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := c) (b := d) (bound := fun _ => C)
    (F := fun (x : ℝ) (t : ℝ) => G ((x : ℂ) + (t : ℂ) * Complex.I))
    (F' := fun (x : ℝ) (t : ℝ) => G' ((x : ℂ) + (t : ℂ) * Complex.I))
    (Metric.ball_mem_nhds ξ₀ hδpos)
    ?_ ?_ ?_ ?_ ?_ ?_
  · have hfun : (fun ξ : ℝ => ∫ θ in Ioo c d, G ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        = fun ξ : ℝ => ∫ θ in c..d, G ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      funext fun ξ => integral_Ioo_eq_intervalIntegral hcd _
    rw [hfun, integral_Ioo_eq_intervalIntegral hcd]
    exact hmain.2
  · filter_upwards [Ioo_mem_nhds ha hb] with x hx
    rw [Set.uIoc_of_le hcd]
    exact ((hGslice x hx.1 hx.2).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact ((hGslice ξ₀ ha hb).intervalIntegrable_of_Icc hcd)
  · rw [Set.uIoc_of_le hcd]
    exact ((continuousOn_slice_of_continuousOn_stripBox hG' ha hb).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [Set.uIoc_of_le hcd] at ht
    exact hC x (hball x hx) t (Ioc_subset_Icc_self ht)
  · exact intervalIntegrable_const
  · have hnull : volume ({d} : Set ℝ) = 0 := by simp
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hnull)] with t htne ht x hx
    rw [Set.uIoc_of_le hcd] at ht
    have hmem := hδsub (hball x hx)
    have htd : t ≠ d := fun h => htne (by rw [h]; exact rfl)
    exact hd x t hmem.1 hmem.2 ht.1 (lt_of_le_of_ne ht.2 htd)

/-! ### The slit-chart ring flux -/

/-- The **slit-chart ring flux** of a potential `u` at log-radius `ξ`: the angle integral of
`u · (r ∂_r u)` over the circle of radius `e^ξ`, parametrised by the geometric angle
`θ ∈ (0, 2π)` measured from the positive real axis — the chart adapted to a slit on the
positive real axis. -/
def ringFluxSlit (u : ℂ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Ioo 0 (2 * π),
    u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- The flux integrand is `2π`-periodic in the angle. -/
theorem fluxIntegrand_periodic (u : ℂ → ℝ) (ξ : ℝ) :
    Function.Periodic (fun θ : ℝ =>
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
            (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (2 * π) := by
  intro θ
  have hexp : Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    have h : ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
        = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.exp_periodic _]
  simp only [hexp]

/-- **Chart gluing for the ring flux.** The slit-chart flux (angles in `(0, 2π)`) equals the
collar-chart flux (angles in `(−π, π)`): the flux integrand is `2π`-periodic in the angle, so
the two full-circle parametrisations integrate identically. -/
theorem ringFluxSlit_eq_ringFlux (u : ℂ → ℝ) (ξ : ℝ) :
    ringFluxSlit u ξ = ringFlux u ξ := by
  have hπ := Real.pi_pos
  unfold ringFluxSlit ringFlux
  rw [integral_Ioo_eq_intervalIntegral (by linarith : (0 : ℝ) ≤ 2 * π),
    integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π)]
  have hkey := (fluxIntegrand_periodic u ξ).intervalIntegral_add_eq 0 (-π)
  have hend : -π + 2 * π = π := by ring
  rw [zero_add, hend] at hkey
  exact hkey

/-! ### The collar of the Grötzsch ring -/

/-- The collar annulus `{s < |z| < 1}` avoids the slit `[0, s]`: it is contained in the
Grötzsch ring. -/
theorem roundAnnulus_subset_grotzschRing {s : ℝ} (hs0 : 0 ≤ s) :
    RoundAnnulus 0 s 1 ⊆ grotzschRing s := by
  intro z hz
  refine ⟨Metric.mem_ball.mpr hz.2, fun hmem => ?_⟩
  obtain ⟨a, c, _, hc, hac, rfl⟩ := hmem
  have hnorm : dist (a • (0 : ℂ) + c • (s : ℂ)) 0 ≤ s := by
    have hzero : a • (0 : ℂ) + c • (s : ℂ) = ((c * s : ℝ) : ℂ) := by
      simp [Complex.real_smul]
    rw [dist_zero_right, hzero, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hs0)]
    calc c * s ≤ 1 * s := mul_le_mul_of_nonneg_right (by linarith) hs0
      _ = s := one_mul s
  exact absurd hz.1 (not_lt.mpr hnorm)

/-- **Collar flux data for the Grötzsch potential.** For a potential `v` of the Grötzsch ring —
harmonic on the ring, continuous on the closed disk, `1` on the unit circle, with values in
`[0, 1]` — there is a slope `b` such that on the collar `(log s, 0)` the circle mean is
`2π + b·ξ`, the ring flux tends to `b` at the unit circle, and the outer-collar Dirichlet
energy is exactly `b − ringFlux v ξ`. -/
theorem grotzschPotential_collar_energy {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ∃ b : ℝ, (∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + b * ξ) ∧
      Tendsto (ringFlux v) (𝓝[<] (0 : ℝ)) (𝓝 b) ∧
      ∀ ξ ∈ Ioo (Real.log s) 0,
        dirichletEnergy v (RoundAnnulus 0 (Real.exp ξ) 1)
          = ENNReal.ofReal (b - ringFlux v ξ) := by
  have hsub := roundAnnulus_subset_grotzschRing hs0.le
  have hu : InnerProductSpace.HarmonicOnNhd v (RoundAnnulus 0 s 1) := fun z hz => hvh z (hsub hz)
  have hcont : ContinuousOn v {z : ℂ | s ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
    refine hvc.mono fun z hz => ?_
    rw [closure_grotzschRing hs0.le]
    exact Metric.mem_closedBall.mpr hz.2
  have hrange : ∀ z ∈ RoundAnnulus 0 s 1, 0 ≤ v z ∧ v z ≤ 1 := fun z hz => hvrange z (hsub hz)
  obtain ⟨b, hb⟩ := exists_logCircleMean_slope hs0 hs1 hu hcont hv1
  exact ⟨b, hb, ringFlux_tendsto_slope hs0 hs1 hu hcont hv1 hrange hb,
    fun ξ hξ => dirichletEnergy_outerCollar_eq_ofReal_sub hs0 hs1 hu hcont hv1 hrange hb hξ⟩

/-! ### Odd reflection across the real axis: the Poisson integral of odd data -/

/-- The Poisson kernel about a conjugation-fixed centre is invariant under simultaneous
conjugation of the interior and boundary points. -/
theorem poissonKernel_conj {c : ℂ} (hc : (starRingEnd ℂ) c = c) (w z : ℂ) :
    poissonKernel c ((starRingEnd ℂ) w) ((starRingEnd ℂ) z) = poissonKernel c w z := by
  rw [poissonKernel_def, poissonKernel_def]
  have key : ∀ a : ℂ, ‖(starRingEnd ℂ) a - c‖ = ‖a - c‖ := by
    intro a
    calc ‖(starRingEnd ℂ) a - c‖ = ‖(starRingEnd ℂ) a - (starRingEnd ℂ) c‖ := by rw [hc]
      _ = ‖(starRingEnd ℂ) (a - c)‖ := by rw [map_sub]
      _ = ‖a - c‖ := RCLike.norm_conj _
  have h3 : ‖(starRingEnd ℂ) z - c - ((starRingEnd ℂ) w - c)‖ = ‖z - c - (w - c)‖ := by
    have hl : (starRingEnd ℂ) z - c - ((starRingEnd ℂ) w - c) = (starRingEnd ℂ) (z - w) := by
      rw [map_sub]
      ring
    have hr : z - c - (w - c) = z - w := by ring
    rw [hl, hr, RCLike.norm_conj]
  rw [key z, key w, h3]

/-- Conjugation reverses the angle of the circle parametrisation about a conjugation-fixed
centre. -/
theorem conj_circleMap {c : ℂ} (hc : (starRingEnd ℂ) c = c) (R θ : ℝ) :
    (starRingEnd ℂ) (circleMap c R θ) = circleMap c R (-θ) := by
  unfold circleMap
  rw [map_add, hc, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.conj_ofReal]
  have harg : (θ : ℂ) * -Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg]

/-- **The Poisson integral of odd boundary data is odd.** About a conjugation-fixed centre, if
the boundary data is odd under conjugation on the circle, so is the Poisson integral:
`P(z̄) = −P(z)`. -/
theorem poissonIntegral_conj_neg {g : ℂ → ℝ} {c : ℂ} (hc : (starRingEnd ℂ) c = c) {R : ℝ}
    (hR : 0 ≤ R) (hodd : ∀ z ∈ Metric.sphere c R, g ((starRingEnd ℂ) z) = -g z) (w : ℂ) :
    poissonIntegral g c R ((starRingEnd ℂ) w) = -poissonIntegral g c R w := by
  unfold poissonIntegral
  rw [Real.circleAverage_def, Real.circleAverage_def, smul_eq_mul, smul_eq_mul, ← mul_neg]
  congr 1
  have hpt : ∀ θ : ℝ,
      poissonKernel c ((starRingEnd ℂ) w) (circleMap c R θ) * g (circleMap c R θ)
        = -(poissonKernel c w (circleMap c R (-θ)) * g (circleMap c R (-θ))) := by
    intro θ
    have hz := conj_circleMap hc R (-θ)
    rw [neg_neg] at hz
    rw [← hz, poissonKernel_conj hc, hodd _ (circleMap_mem_sphere c hR (-θ))]
    ring
  have hper : Function.Periodic
      (fun θ : ℝ => poissonKernel c w (circleMap c R θ) * g (circleMap c R θ)) (2 * π) :=
    (periodic_circleMap c R).comp fun z => poissonKernel c w z * g z
  calc ∫ θ in (0 : ℝ)..2 * π,
      poissonKernel c ((starRingEnd ℂ) w) (circleMap c R θ) * g (circleMap c R θ)
      = ∫ θ in (0 : ℝ)..2 * π,
          -(poissonKernel c w (circleMap c R (-θ)) * g (circleMap c R (-θ))) :=
        intervalIntegral.integral_congr fun θ _ => hpt θ
    _ = -∫ θ in (0 : ℝ)..2 * π,
          poissonKernel c w (circleMap c R (-θ)) * g (circleMap c R (-θ)) :=
        intervalIntegral.integral_neg
    _ = -∫ θ in (-(2 * π))..(-(0 : ℝ)),
          poissonKernel c w (circleMap c R θ) * g (circleMap c R θ) := by
        congr 1
        exact intervalIntegral.integral_comp_neg (a := 0) (b := 2 * π)
          (f := fun t : ℝ => poissonKernel c w (circleMap c R t) * g (circleMap c R t))
    _ = -∫ θ in (0 : ℝ)..2 * π,
          poissonKernel c w (circleMap c R θ) * g (circleMap c R θ) := by
        have hgl := hper.intervalIntegral_add_eq (-(2 * π)) 0
        have he1 : -(2 * π) + 2 * π = 0 := by ring
        have he2 : (0 : ℝ) + 2 * π = 2 * π := by ring
        rw [he1, he2] at hgl
        rw [neg_zero, hgl]

open Classical in
/-- The Dirichlet solution on a disk glued to its boundary data: the Poisson integral on the
open ball, the boundary data outside. -/
noncomputable def dirichletGlue (g : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  (Metric.ball c R).piecewise (poissonIntegral g c R) g

theorem dirichletGlue_eq_poisson {g : ℂ → ℝ} {c : ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball c R) : dirichletGlue g c R z = poissonIntegral g c R z := by
  simp [dirichletGlue, Set.piecewise, hz]

theorem dirichletGlue_eq_boundary {g : ℂ → ℝ} {c : ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∉ Metric.ball c R) : dirichletGlue g c R z = g z := by
  simp [dirichletGlue, Set.piecewise, hz]

/-- Points of the sphere are not in the open ball. -/
theorem notMem_ball_of_mem_sphere {c z : ℂ} {R : ℝ} (hz : z ∈ Metric.sphere c R) :
    z ∉ Metric.ball c R := by
  intro hmem
  have h' : dist z c < R := Metric.mem_ball.mp hmem
  rw [Metric.mem_sphere.mp hz] at h'
  exact lt_irrefl R h'

/-- The glued Dirichlet solution is harmonic on the open ball. -/
theorem dirichletGlue_harmonicOnNhd (g : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (Metric.sphere c R)) :
    InnerProductSpace.HarmonicOnNhd (dirichletGlue g c R) (Metric.ball c R) := by
  intro z hz
  have hP := poissonIntegral_harmonicOn g c hR hg z hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hP
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  exact (dirichletGlue_eq_poisson hy).symm

/-- The glued Dirichlet solution is continuous on the closed ball: harmonicity gives interior
continuity, and the boundary limit of the Poisson integral matches the boundary data. -/
theorem dirichletGlue_continuousOn (g : ℂ → ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hg : ContinuousOn g (Metric.sphere c R)) :
    ContinuousOn (dirichletGlue g c R) (Metric.closedBall c R) := by
  intro z hz
  rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
  · have hzball : z ∈ Metric.ball c R := Metric.mem_ball.mpr hlt
    refine ContinuousAt.continuousWithinAt ?_
    have hP : ContinuousAt (poissonIntegral g c R) z :=
      (poissonIntegral_harmonicOn g c hR hg z hzball).1.continuousAt
    refine hP.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with y hy
    exact (dirichletGlue_eq_poisson hy).symm
  · have hzs : z ∈ Metric.sphere c R := Metric.mem_sphere.mpr heq
    have h1 : ContinuousWithinAt (dirichletGlue g c R) (Metric.ball c R) z := by
      have hb := poissonIntegral_tendsto_boundary g c hR hg hzs
      have hgz : dirichletGlue g c R z = g z :=
        dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hzs)
      change Tendsto _ _ _
      rw [hgz]
      refine hb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (dirichletGlue_eq_poisson hy).symm
    have h2 : ContinuousWithinAt (dirichletGlue g c R) (Metric.sphere c R) z := by
      refine (hg z hzs).congr ?_ ?_
      · intro y hy
        exact dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hy)
      · exact dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hzs)
    have hu := h1.union h2
    rwa [Metric.ball_union_sphere] at hu

/-- **Odd harmonic reflection across the real axis.** A function continuous on a closed disk
about a conjugation-fixed centre, harmonic off the real axis, vanishing on the real diameter,
and odd under conjugation is harmonic on the whole open disk: it agrees there with the Poisson
integral of its boundary values, by the maximum principle on the two half-disks and the odd
symmetry of the Poisson integral. -/
theorem harmonicOnNhd_of_odd_reflection {h : ℂ → ℝ} {c : ℂ} (hc : (starRingEnd ℂ) c = c)
    {R : ℝ} (hR : 0 < R)
    (hharm : InnerProductSpace.HarmonicOnNhd h {z | z ∈ Metric.ball c R ∧ z.im ≠ 0})
    (hcont : ContinuousOn h (Metric.closedBall c R))
    (hzero : ∀ z ∈ Metric.closedBall c R, z.im = 0 → h z = 0)
    (hodd : ∀ z ∈ Metric.closedBall c R, h ((starRingEnd ℂ) z) = -h z) :
    InnerProductSpace.HarmonicOnNhd h (Metric.ball c R) := by
  have hg : ContinuousOn h (Metric.sphere c R) := hcont.mono Metric.sphere_subset_closedBall
  have hPharm := dirichletGlue_harmonicOnNhd h c hR hg
  have hPcont := dirichletGlue_continuousOn h c hR hg
  -- oddness of the Poisson solution, hence its vanishing on the real diameter
  have hPodd : ∀ w ∈ Metric.ball c R,
      dirichletGlue h c R ((starRingEnd ℂ) w) = -dirichletGlue h c R w := by
    intro w hw
    have hwconj : (starRingEnd ℂ) w ∈ Metric.ball c R := by
      rw [Metric.mem_ball] at hw ⊢
      calc dist ((starRingEnd ℂ) w) c = dist ((starRingEnd ℂ) w) ((starRingEnd ℂ) c) := by
            rw [hc]
        _ = dist w c := by rw [dist_eq_norm, ← map_sub, RCLike.norm_conj, ← dist_eq_norm]
        _ < R := hw
    rw [dirichletGlue_eq_poisson hwconj, dirichletGlue_eq_poisson hw]
    exact poissonIntegral_conj_neg hc hR.le
      (fun z hz => hodd z (Metric.sphere_subset_closedBall hz)) w
  have hPzero : ∀ w ∈ Metric.ball c R, w.im = 0 → dirichletGlue h c R w = 0 := by
    intro w hw him
    have hwfix : (starRingEnd ℂ) w = w := Complex.conj_eq_iff_im.mpr him
    have hval := hPodd w hw
    rw [hwfix] at hval
    linarith
  -- maximum-principle comparison on a half-disk
  have key : ∀ S : Set ℂ, IsOpen S → (∀ z ∈ S, z.im ≠ 0) →
      (∀ z, z ∈ closure (Metric.ball c R ∩ S) → z ∉ Metric.ball c R ∩ S →
        z ∈ Metric.sphere c R ∨ z.im = 0) →
      ∀ w ∈ Metric.ball c R ∩ S, h w = dirichletGlue h c R w := by
    intro S hSopen hSim hfr w hw
    have hUopen : IsOpen (Metric.ball c R ∩ S) := Metric.isOpen_ball.inter hSopen
    have hUbdd : Bornology.IsBounded (Metric.ball c R ∩ S) :=
      Metric.isBounded_ball.subset Set.inter_subset_left
    have hclosU : closure (Metric.ball c R ∩ S) ⊆ Metric.closedBall c R :=
      closure_minimal (Set.inter_subset_left.trans Metric.ball_subset_closedBall)
        Metric.isClosed_closedBall
    have hdiff1 : InnerProductSpace.HarmonicOnNhd (fun z => h z - dirichletGlue h c R z)
        (Metric.ball c R ∩ S) := fun z hz =>
      (hharm z ⟨hz.1, hSim z hz.2⟩).sub (hPharm z hz.1)
    have hdiff2 : InnerProductSpace.HarmonicOnNhd (fun z => dirichletGlue h c R z - h z)
        (Metric.ball c R ∩ S) := fun z hz =>
      (hPharm z hz.1).sub (hharm z ⟨hz.1, hSim z hz.2⟩)
    have hfrbound : ∀ z ∈ frontier (Metric.ball c R ∩ S), h z - dirichletGlue h c R z = 0 := by
      intro z hz
      rw [hUopen.frontier_eq] at hz
      have hzcb : z ∈ Metric.closedBall c R := hclosU hz.1
      rcases hfr z hz.1 hz.2 with hs | him
      · rw [dirichletGlue_eq_boundary (notMem_ball_of_mem_sphere hs), sub_self]
      · rw [hzero z hzcb him]
        rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzcb) with hlt | heq
        · rw [hPzero z (Metric.mem_ball.mpr hlt) him]
          ring
        · rw [dirichletGlue_eq_boundary
            (notMem_ball_of_mem_sphere (Metric.mem_sphere.mpr heq)), hzero z hzcb him]
          ring
    have hle1 := SubharmonicOn.le_of_frontier_le hUopen hUbdd
      (HarmonicOnNhd.subharmonicOn hdiff1)
      ((hcont.mono hclosU).sub (hPcont.mono hclosU))
      (fun z hz => le_of_eq (hfrbound z hz)) w hw
    have hfrbound2 : ∀ z ∈ frontier (Metric.ball c R ∩ S),
        dirichletGlue h c R z - h z ≤ 0 := by
      intro z hz
      have := hfrbound z hz
      linarith
    have hle2 := SubharmonicOn.le_of_frontier_le hUopen hUbdd
      (HarmonicOnNhd.subharmonicOn hdiff2)
      ((hPcont.mono hclosU).sub (hcont.mono hclosU))
      hfrbound2 w hw
    linarith
  -- frontier classification for the upper and lower half-disks
  have hfrUp : ∀ z, z ∈ closure (Metric.ball c R ∩ {z : ℂ | 0 < z.im}) →
      z ∉ Metric.ball c R ∩ {z : ℂ | 0 < z.im} → z ∈ Metric.sphere c R ∨ z.im = 0 := by
    intro z hzclos hznot
    have hzmem : z ∈ Metric.closedBall c R ∩ {z : ℂ | 0 ≤ z.im} := by
      refine closure_minimal (Set.inter_subset_inter Metric.ball_subset_closedBall
        fun y hy => le_of_lt hy) (Metric.isClosed_closedBall.inter
          (isClosed_le continuous_const Complex.continuous_im)) hzclos
    have him0 : (0 : ℝ) ≤ z.im := hzmem.2
    rcases eq_or_lt_of_le him0 with him | him
    · exact Or.inr him.symm
    · refine Or.inl (Metric.mem_sphere.mpr ?_)
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzmem.1) with hlt | heq
      · exact absurd ⟨Metric.mem_ball.mpr hlt, him⟩ hznot
      · exact heq
  have hfrLow : ∀ z, z ∈ closure (Metric.ball c R ∩ {z : ℂ | z.im < 0}) →
      z ∉ Metric.ball c R ∩ {z : ℂ | z.im < 0} → z ∈ Metric.sphere c R ∨ z.im = 0 := by
    intro z hzclos hznot
    have hzmem : z ∈ Metric.closedBall c R ∩ {z : ℂ | z.im ≤ 0} := by
      refine closure_minimal (Set.inter_subset_inter Metric.ball_subset_closedBall
        fun y hy => le_of_lt hy) (Metric.isClosed_closedBall.inter
          (isClosed_le Complex.continuous_im continuous_const)) hzclos
    have him0 : z.im ≤ (0 : ℝ) := hzmem.2
    rcases eq_or_lt_of_le him0 with him | him
    · exact Or.inr him
    · refine Or.inl (Metric.mem_sphere.mpr ?_)
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hzmem.1) with hlt | heq
      · exact absurd ⟨Metric.mem_ball.mpr hlt, him⟩ hznot
      · exact heq
  -- equality with the Poisson solution on the whole disk
  have hball_eq : ∀ w ∈ Metric.ball c R, h w = dirichletGlue h c R w := by
    intro w hw
    rcases lt_trichotomy w.im 0 with hneg | him | hpos
    · exact key {z : ℂ | z.im < 0} (isOpen_lt Complex.continuous_im continuous_const)
        (fun z hz => ne_of_lt hz) hfrLow w ⟨hw, hneg⟩
    · rw [hzero w (Metric.ball_subset_closedBall hw) him, hPzero w hw him]
    · exact key {z : ℂ | 0 < z.im} (isOpen_lt continuous_const Complex.continuous_im)
        (fun z hz => ne_of_gt hz) hfrUp w ⟨hw, hpos⟩
  intro z hz
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (hPharm z hz)
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
  exact (hball_eq y hy).symm

/-! ### Bank regularity of the log-polar gradient via odd reflection -/

/-- The **odd reflection across the real axis** of a real function: `v` on the closed upper
half-plane, minus `v` of the conjugate on the lower half-plane. -/
noncomputable def reflectReal (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then v z else -v ((starRingEnd ℂ) z)

/-- The odd reflection agrees with `v` on the closed upper half-plane. -/
theorem reflectReal_of_im_nonneg {v : ℂ → ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    reflectReal v z = v z := by
  simp [reflectReal, hz]

/-- The odd reflection is odd under conjugation whenever `v` vanishes on the real axis. -/
theorem reflectReal_conj {v : ℂ → ℝ} (hv0 : ∀ z : ℂ, z.im = 0 → v z = 0) (z : ℂ) :
    reflectReal v ((starRingEnd ℂ) z) = -reflectReal v z := by
  simp only [reflectReal, Complex.conj_im, Complex.conj_conj]
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [if_pos (by linarith : 0 ≤ -z.im), if_neg (by linarith : ¬ 0 ≤ z.im), neg_neg]
  · rw [if_pos (by rw [h, neg_zero]), if_pos (le_of_eq h.symm)]
    have hz : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr h
    rw [hz, hv0 z h, neg_zero]
  · rw [if_neg (by linarith : ¬ 0 ≤ -z.im), if_pos (le_of_lt h)]

/-- The odd reflection vanishes on the real axis when `v` does. -/
theorem reflectReal_zero_of_im_zero {v : ℂ → ℝ} (hv0 : ∀ z : ℂ, z.im = 0 → v z = 0)
    {z : ℂ} (hz : z.im = 0) : reflectReal v z = 0 := by
  rw [reflectReal_of_im_nonneg (le_of_eq hz.symm), hv0 z hz]

/-- **Bank ball geometry.** At an interior slit point `x₀ ∈ (0, s)` (on the positive real axis),
the ball of radius `min x₀ (s − x₀)` about `x₀` lies in the open unit disk and meets the slit only
in its real diameter: off the real axis it is contained in the Grötzsch ring. -/
theorem ball_bank_subset_grotzschRing {s x₀ : ℝ} (hs1 : s < 1) (hx0 : 0 < x₀) (hxs : x₀ < s) :
    (∀ z ∈ Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀)), 0 < z.re ∧ z.re < s ∧ ‖z‖ < 1) ∧
      {z : ℂ | z ∈ Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀)) ∧ z.im ≠ 0} ⊆ grotzschRing s := by
  set ρ : ℝ := min x₀ (s - x₀) with hρ
  have hρpos : 0 < ρ := lt_min hx0 (by linarith)
  have hρ1 : ρ ≤ x₀ := min_le_left _ _
  have hρ2 : ρ ≤ s - x₀ := min_le_right _ _
  have hcore : ∀ z ∈ Metric.ball ((x₀ : ℝ) : ℂ) ρ, 0 < z.re ∧ z.re < s ∧ ‖z‖ < 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ))
      simpa [Complex.sub_re] using this
    have hre1 : |z.re - x₀| < ρ := lt_of_le_of_lt hre hz
    rw [abs_sub_lt_iff] at hre1
    refine ⟨by linarith [hre1.1, hρ1], by linarith [hre1.2, hρ2], ?_⟩
    calc ‖z‖ = ‖(z - (x₀ : ℂ)) + (x₀ : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (x₀ : ℂ)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
      _ < ρ + x₀ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
      _ ≤ s := by linarith [hρ2]
      _ < 1 := hs1
  refine ⟨hcore, fun z hz => ?_⟩
  obtain ⟨hzball, hzim⟩ := hz
  obtain ⟨hre0, hres, hnorm⟩ := hcore z hzball
  refine ⟨mem_ball_zero_iff.mpr hnorm, fun hslit => ?_⟩
  have hslit' : z ∈ grotzschInner s := hslit
  rw [grotzschInner_eq (le_of_lt (lt_trans hx0 hxs))] at hslit'
  exact hzim hslit'.1

/-- **Continuity of the odd reflection on the bank ball.** For the Grötzsch potential `v` (harmonic
on the ring, continuous on the closed disk, zero on the slit), the odd reflection `reflectReal v`
is continuous on the closed bank ball about an interior slit point `x₀ ∈ (0, s)`. -/
theorem continuousOn_reflectReal_bankBall {s x₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x₀) (hxs : x₀ < s) {v : ℂ → ℝ}
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0) :
    ContinuousOn (reflectReal v) (Metric.closedBall ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀))) := by
  set ρ : ℝ := min x₀ (s - x₀) with hρ
  have hρpos : 0 < ρ := lt_min hx0 (by linarith)
  have hρ1 : ρ ≤ x₀ := min_le_left _ _
  have hρ2 : ρ ≤ s - x₀ := min_le_right _ _
  -- the closed ball lies in the closed unit disk and every point has real part in (0, s)
  have hclsub : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ,
      0 ≤ z.re ∧ z.re ≤ s ∧ ‖z‖ < 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ)); simpa [Complex.sub_re] using this
    have hre1 : |z.re - x₀| ≤ ρ := le_trans hre hz
    rw [abs_le] at hre1
    refine ⟨by linarith [hre1.1, hρ1], by linarith [hre1.2, hρ2], ?_⟩
    calc ‖z‖ = ‖(z - (x₀ : ℂ)) + (x₀ : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (x₀ : ℂ)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
      _ ≤ ρ + x₀ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]; linarith
      _ ≤ s := by linarith [hρ2]
      _ < 1 := hs1
  have hvc' : ContinuousOn v (Metric.closedBall (0 : ℂ) 1) := by
    rwa [← closure_grotzschRing hs0.le]
  have hcball : Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun z hz => Metric.mem_closedBall.mpr (by
      rw [dist_zero_right]; exact le_of_lt (hclsub z hz).2.2)
  have hvcball : ContinuousOn v (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ) := hvc'.mono hcball
  -- continuity of `-v ∘ conj` on the ball
  have hconjmaps : Set.MapsTo (starRingEnd ℂ) (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ)
      (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right, RCLike.norm_conj]
    exact le_of_lt (hclsub z hz).2.2
  have hnegconjc : ContinuousOn (fun z => -v ((starRingEnd ℂ) z))
      (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ) :=
    (hvc'.comp Complex.continuous_conj.continuousOn hconjmaps).neg
  -- glue on the closed upper and lower half-balls
  have hup : ContinuousOn (reflectReal v)
      (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im}) := by
    refine (hvcball.mono Set.inter_subset_left).congr fun z hz => ?_
    exact reflectReal_of_im_nonneg hz.2
  have hlow : ContinuousOn (reflectReal v)
      (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
    refine (hnegconjc.mono Set.inter_subset_left).congr fun z hz => ?_
    have hzle : z.im ≤ 0 := hz.2
    have hbz := hclsub z hz.1
    rcases eq_or_lt_of_le hzle with him | him
    · have hvz : v z = 0 := hv0 z him hbz.1 hbz.2.1
      rw [reflectReal_of_im_nonneg (le_of_eq him.symm), hvz]
      have hzfix : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr him
      rw [hzfix, hvz, neg_zero]
    · rw [reflectReal, if_neg (by linarith)]
  have hcover : Metric.closedBall ((x₀ : ℝ) : ℂ) ρ
      = (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im})
        ∪ (Metric.closedBall ((x₀ : ℝ) : ℂ) ρ ∩ {z : ℂ | z.im ≤ 0}) := by
    rw [← Set.inter_union_distrib_left]
    ext z; simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · intro hz; exact ⟨hz, le_total 0 z.im⟩
    · intro hz; exact hz.1
  rw [hcover]
  refine hup.union_of_isClosed hlow ?_ ?_
  · exact (Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
  · exact (Metric.isClosed_closedBall.inter (isClosed_le Complex.continuous_im continuous_const))

/-- **Harmonicity of the odd reflection off the real axis.** On the bank ball about an interior
slit point, away from the real axis the odd reflection of the Grötzsch potential is harmonic: on
the upper half it equals `v` (harmonic on the ring), on the lower half `−v ∘ conj` (harmonic since
conjugation is an isometry). -/
theorem harmonicOnNhd_reflectReal_offAxis {s x₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x₀) (hxs : x₀ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    InnerProductSpace.HarmonicOnNhd (reflectReal v)
      {z | z ∈ Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀)) ∧ z.im ≠ 0} := by
  obtain ⟨_, hsub⟩ := ball_bank_subset_grotzschRing hs1 hx0 hxs
  intro z hz
  obtain ⟨hzball, hzim⟩ := hz
  have hzring : z ∈ grotzschRing s := hsub ⟨hzball, hzim⟩
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · -- lower half: `reflectReal v = -v ∘ conj` near `z`, harmonic by conjugation symmetry
    have hconjring : (starRingEnd ℂ) z ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hzring
    have hharmconj : InnerProductSpace.HarmonicAt (fun w => v ((starRingEnd ℂ) w)) z := by
      have hpt : InnerProductSpace.HarmonicAt v (Complex.conjLIE z) := by
        rw [show Complex.conjLIE z = (starRingEnd ℂ) z from Complex.conjLIE_apply z]
        exact hvh _ hconjring
      have h := harmonicAt_comp_linearIsometryEquiv Complex.conjLIE hpt
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp h
      exact Filter.Eventually.of_forall fun y => by
        simp [Function.comp_apply, Complex.conjLIE_apply]
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hharmconj.neg
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with y hy
    rw [Pi.neg_apply, reflectReal, if_neg (by exact not_le.mpr hy)]
  · exact absurd hzero hzim
  · -- upper half: `reflectReal v = v` near `z`, harmonic on the ring
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (hvh z hzring)
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos] with y hy
    rw [reflectReal_of_im_nonneg (le_of_lt hy)]

/-- **The odd reflection is harmonic across the bank.** By the odd-reflection principle, the odd
reflection of the Grötzsch potential is harmonic on the entire bank ball about an interior slit
point, in particular across the real axis. -/
theorem harmonicOnNhd_reflectReal_bankBall {s x₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hx0 : 0 < x₀) (hxs : x₀ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0) :
    InnerProductSpace.HarmonicOnNhd (reflectReal v)
      (Metric.ball ((x₀ : ℝ) : ℂ) (min x₀ (s - x₀))) := by
  set ρ : ℝ := min x₀ (s - x₀) with hρ
  have hρpos : 0 < ρ := lt_min hx0 (by linarith)
  have hcfix : (starRingEnd ℂ) ((x₀ : ℝ) : ℂ) = ((x₀ : ℝ) : ℂ) :=
    Complex.conj_eq_iff_im.mpr (by simp)
  -- inside the closed bank ball every point has real part in `[0, s]`
  have hclre : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ, 0 ≤ z.re ∧ z.re ≤ s := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - x₀| ≤ ‖z - (x₀ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (x₀ : ℂ)); simpa [Complex.sub_re] using this
    have hre1 : |z.re - x₀| ≤ ρ := le_trans hre hz
    rw [abs_le] at hre1
    exact ⟨by linarith [hre1.1, min_le_left x₀ (s - x₀)],
      by linarith [hre1.2, min_le_right x₀ (s - x₀)]⟩
  refine harmonicOnNhd_of_odd_reflection hcfix hρpos
    (harmonicOnNhd_reflectReal_offAxis hs0 hs1 hx0 hxs hvh)
    (continuousOn_reflectReal_bankBall hs0 hs1 hx0 hxs hvc hv0) ?_ ?_
  · intro z hzcl hzim
    have hbz := hclre z hzcl
    rw [reflectReal_of_im_nonneg (le_of_eq hzim.symm), hv0 z hzim hbz.1 hbz.2]
  · intro z hzcl
    simp only [reflectReal, Complex.conj_im, Complex.conj_conj]
    rcases lt_trichotomy z.im 0 with h | h | h
    · rw [if_pos (by linarith : 0 ≤ -z.im), if_neg (by linarith : ¬ 0 ≤ z.im), neg_neg]
    · have hbz := hclre z hzcl
      rw [if_pos (by rw [h, neg_zero]), if_pos (le_of_eq h.symm)]
      have hzfix : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr h
      rw [hzfix, hv0 z h hbz.1 hbz.2, neg_zero]
    · rw [if_neg (by linarith : ¬ 0 ≤ -z.im), if_pos (le_of_lt h)]

/-- The norm of the holomorphic gradient equals the operator norm of the real Fréchet derivative. -/
theorem norm_gradC_eq_norm_fderiv (v : ℂ → ℝ) (z : ℂ) :
    ‖gradC v z‖ = ‖fderiv ℝ v z‖ := by
  have hnorm : ‖fderiv ℝ v z‖ ^ 2 = Complex.normSq (gradC v z) := by
    have hbasis := Complex.orthonormalBasisOneI.norm_dual (fderiv ℝ v z)
    rw [Fin.sum_univ_two] at hbasis
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hbasis
    rw [hbasis]
    simp only [gradC, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hgnorm : ‖gradC v z‖ ^ 2 = Complex.normSq (gradC v z) := (Complex.normSq_eq_norm_sq _).symm
  nlinarith [hnorm, hgnorm, norm_nonneg (gradC v z), norm_nonneg (fderiv ℝ v z)]

/-- **Conjugation invariance of the gradient norm.** For a potential invariant under conjugation on
the closed disk (as the Grötzsch potential is), the norm of the holomorphic gradient is the same at
conjugate interior points. -/
theorem norm_gradC_conj {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {z : ℂ} (hz : z ∈ grotzschRing s) :
    ‖gradC v ((starRingEnd ℂ) z)‖ = ‖gradC v z‖ := by
  have hconjz : (starRingEnd ℂ) z ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hz
  have hnb : (fun w => v ((starRingEnd ℂ) w)) =ᶠ[𝓝 z] v := by
    filter_upwards [(isOpen_grotzschRing hs0.le).mem_nhds hz] with w hw
    exact grotzschPotential_conj hs0 hs1 hvh hvc hv0 hv1 w (subset_closure hw)
  have hdvcz : DifferentiableAt ℝ v ((starRingEnd ℂ) z) :=
    differentiableAt_of_harmonicOnNhd hvh hconjz
  have hconjd : HasFDerivAt (fun w : ℂ => (starRingEnd ℂ) w)
      (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) z := by
    have := Complex.conjLIE.toContinuousLinearEquiv.hasFDerivAt (x := z)
    refine this.congr_fderiv ?_
    ext w
    simp [Complex.conjLIE_apply, Complex.conjCLE_apply]
  have hcomp : HasFDerivAt v
      ((fderiv ℝ v ((starRingEnd ℂ) z)).comp
        (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap)) z :=
    (hdvcz.hasFDerivAt.comp z hconjd).congr_of_eventuallyEq hnb.symm
  have hfeq : fderiv ℝ v z
      = (fderiv ℝ v ((starRingEnd ℂ) z)).comp
          (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) := hcomp.fderiv
  rw [norm_gradC_eq_norm_fderiv, norm_gradC_eq_norm_fderiv, hfeq,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- **Local off-axis bound for the gradient near the annulus.** For the Grötzsch potential `v` and
a point `z₀` of the closed annulus `{r₁ ≤ |z| ≤ r₂}` with `0 < r₁` and `r₂ < s`, there is a
neighbourhood of `z₀` and a constant bounding `‖gradC v‖` off the real axis: away from the slit `v`
is harmonic, near an interior slit point the odd reflection is harmonic across the bank and the
gradient norm is conjugation-invariant. -/
theorem exists_localBound_gradC {s r₁ r₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hr₁ : 0 < r₁) (hr₂ : r₂ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {z₀ : ℂ} (hz₀ : r₁ ≤ ‖z₀‖ ∧ ‖z₀‖ ≤ r₂) :
    ∃ U ∈ 𝓝 z₀, ∃ C : ℝ, ∀ z ∈ U, z.im ≠ 0 → ‖gradC v z‖ ≤ C := by
  have hz₀norm1 : ‖z₀‖ < 1 := lt_trans (lt_of_le_of_lt hz₀.2 hr₂) hs1
  have hz₀pos : 0 < ‖z₀‖ := lt_of_lt_of_le hr₁ hz₀.1
  by_cases hax : z₀.im = 0 ∧ 0 ≤ z₀.re ∧ z₀.re ≤ s
  · -- interior slit point: `z₀.re ∈ (0, s)`; reflect across the bank
    obtain ⟨him, hre0, _⟩ := hax
    have hnre : ‖z₀‖ = z₀.re := by
      have hz₀re : z₀ = ((z₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [hz₀re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0, Complex.ofReal_re]
    have hrepos : 0 < z₀.re := by rw [hnre] at hz₀pos; exact hz₀pos
    have hres : z₀.re < s := by rw [hnre] at hz₀; exact lt_of_le_of_lt hz₀.2 hr₂
    have hz₀eq : ((z₀.re : ℝ) : ℂ) = z₀ := (Complex.ext (by simp) (by simp [him])).symm
    set x₀ : ℝ := z₀.re with hx₀
    set ρ : ℝ := min x₀ (s - x₀) with hρ
    have hρpos : 0 < ρ := lt_min hrepos (by linarith)
    have hWharm := harmonicOnNhd_reflectReal_bankBall hs0 hs1 hrepos hres hvh hvc
      (fun z hz hz0 hzs => hv0 z (by rw [grotzschInner_eq hs0.le]; exact ⟨hz, hz0, hzs⟩))
    -- `gradC (reflectReal v)` is continuous on the ball, hence bounded on a smaller closed ball
    have hgWcont : ContinuousOn (gradC (reflectReal v))
        (Metric.ball ((x₀ : ℝ) : ℂ) ρ) := fun z hz =>
      ((gradC_differentiableOn hWharm).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)).continuousAt.continuousWithinAt
    set ρ' : ℝ := ρ / 2 with hρ'
    have hρ'pos : 0 < ρ' := by positivity
    have hsubball : Metric.closedBall ((x₀ : ℝ) : ℂ) ρ' ⊆ Metric.ball ((x₀ : ℝ) : ℂ) ρ :=
      fun z hz => Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by
        rw [hρ']; linarith))
    obtain ⟨C, hC⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (hgWcont.mono hsubball)
    -- the closed ball `closedBall x₀ ρ'` is symmetric under conjugation
    have hconjcb : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ',
        (starRingEnd ℂ) z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ' := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      have : (starRingEnd ℂ) z - (x₀ : ℂ) = (starRingEnd ℂ) (z - (x₀ : ℂ)) := by
        rw [map_sub, Complex.conj_ofReal]
      rw [this, RCLike.norm_conj]; exact hz
    obtain ⟨_, hringsub⟩ := ball_bank_subset_grotzschRing hs1 hrepos hres
    -- `gradC v` bounded on the upper part of the ball by `C`
    have hupbound : ∀ z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ', 0 < z.im →
        ‖gradC v z‖ ≤ C := by
      intro z hzcb hup
      have hgeq : gradC v z = gradC (reflectReal v) z := by
        have hnb : v =ᶠ[𝓝 z] reflectReal v := by
          filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hup]
            with w hw
          rw [reflectReal_of_im_nonneg (le_of_lt hw)]
        rw [gradC, gradC, hnb.fderiv_eq]
      rw [hgeq]; exact hC z hzcb
    have hnbhd : Metric.ball ((x₀ : ℝ) : ℂ) ρ' ∈ 𝓝 z₀ := by
      rw [← hz₀eq]; exact Metric.ball_mem_nhds _ hρ'pos
    refine ⟨Metric.ball ((x₀ : ℝ) : ℂ) ρ', hnbhd, C, fun z hzU hzim => ?_⟩
    have hzcb : z ∈ Metric.closedBall ((x₀ : ℝ) : ℂ) ρ' := Metric.ball_subset_closedBall hzU
    rcases lt_trichotomy z.im 0 with hlow | hz0 | hup
    · -- lower half: conjugation invariance reduces to the upper bound at `conj z`
      have hzring : z ∈ grotzschRing s := hringsub ⟨hsubball hzcb, hzim⟩
      rw [← norm_gradC_conj hs0 hs1 hvh hvc hv0 hv1 hzring]
      exact hupbound _ (hconjcb z hzcb) (by simp [Complex.conj_im]; linarith)
    · exact absurd hz0 hzim
    · exact hupbound z hzcb hup
  · -- off-slit point: `z₀ ∈ grotzschRing s`, `gradC v` continuous there
    have hz₀ring : z₀ ∈ grotzschRing s := by
      refine ⟨mem_ball_zero_iff.mpr hz₀norm1, fun hslit => ?_⟩
      have hslit' : z₀ ∈ grotzschInner s := hslit
      rw [grotzschInner_eq hs0.le] at hslit'
      exact hax hslit'
    have hcont : ContinuousAt (fun z => ‖gradC v z‖) z₀ :=
      (((gradC_differentiableOn hvh).differentiableAt
        ((isOpen_grotzschRing hs0.le).mem_nhds hz₀ring)).continuousAt).norm
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδpos, hδ⟩ := hcont 1 one_pos
    refine ⟨Metric.ball z₀ δ, Metric.ball_mem_nhds _ hδpos, ‖gradC v z₀‖ + 1, fun z hz _ => ?_⟩
    have := hδ (Metric.mem_ball.mp hz)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]

/-- **Global off-axis gradient bound on the closed annulus.** The holomorphic gradient of the
Grötzsch potential is bounded, off the real axis, on the closed annulus `{r₁ ≤ |z| ≤ r₂}` with
`0 < r₁` and `r₂ < s`: the local bounds patch together by compactness. -/
theorem exists_bound_gradC_annulus {s r₁ r₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hr₁ : 0 < r₁) (hr₂ : r₂ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ∃ C : ℝ, ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖z‖ ≤ r₂ → z.im ≠ 0 → ‖gradC v z‖ ≤ C := by
  set A : Set ℂ := {z : ℂ | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂} with hA
  have hAcompact : IsCompact A := by
    have h1 : IsClosed {z : ℂ | r₁ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
    have h2 : IsClosed {z : ℂ | ‖z‖ ≤ r₂} := isClosed_le continuous_norm continuous_const
    refine (Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_)
    refine (Metric.isBounded_iff.mpr ⟨2 * r₂, fun x hx y hy => ?_⟩)
    calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact (norm_sub_le x y)
      _ ≤ 2 * r₂ := by have := hx.2; have := hy.2; linarith
  -- local bounds at every point of the annulus
  have hloc : ∀ z₀ ∈ A, ∃ U ∈ 𝓝 z₀, ∃ C : ℝ, ∀ z ∈ U, z.im ≠ 0 → ‖gradC v z‖ ≤ C :=
    fun z₀ hz₀ => exists_localBound_gradC hs0 hs1 hr₁ hr₂ hvh hvc hv0 hv1 hz₀
  choose! U hU C hC using hloc
  obtain ⟨t, htA, htcov⟩ := hAcompact.elim_nhds_subcover U (fun z hz => hU z hz)
  refine ⟨t.sum (fun z => max (C z) 0), fun z hz1 hz2 hzim => ?_⟩
  have hzA : z ∈ A := ⟨hz1, hz2⟩
  obtain ⟨z₀, hz₀t, hz₀U⟩ := Set.mem_iUnion₂.mp (htcov hzA)
  have hbound : ‖gradC v z‖ ≤ C z₀ := hC z₀ (htA z₀ hz₀t) z hz₀U hzim
  calc ‖gradC v z‖ ≤ C z₀ := hbound
    _ ≤ max (C z₀) 0 := le_max_left _ _
    _ ≤ t.sum (fun z => max (C z) 0) :=
        Finset.single_le_sum (fun i _ => le_max_right _ _) hz₀t

/-! ### The exponential image of the slit box lies in the Grötzsch ring -/

/-- For `ξ < log s` and geometric angle `θ ∈ (0, 2π)`, the point `e^{ξ+θi}` avoids the slit and
lies in the Grötzsch ring: its modulus `e^ξ` is below `s < 1`, and off the endpoints `θ = 0, 2π`
the point is not on the closed slit (positive real axis segment). -/
theorem exp_mem_grotzschRing_slitBox {s ξ θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ : ξ < Real.log s) (hθ0 : 0 < θ) (hθ2 : θ < 2 * π) :
    Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s := by
  have hnorm : ‖Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ = Real.exp ξ := by
    rw [Complex.norm_exp, re_logPolar]
  have hlt1 : Real.exp ξ < 1 := by
    calc Real.exp ξ < Real.exp (Real.log s) := Real.exp_lt_exp.mpr hξ
      _ = s := Real.exp_log hs0
      _ < 1 := hs1
  have hlts : Real.exp ξ < s := by
    calc Real.exp ξ < Real.exp (Real.log s) := Real.exp_lt_exp.mpr hξ
      _ = s := Real.exp_log hs0
  refine ⟨mem_ball_zero_iff.mpr (by rw [hnorm]; exact hlt1), fun hslit => ?_⟩
  have hslit' : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschInner s := hslit
  rw [grotzschInner_eq hs0.le] at hslit'
  obtain ⟨him, hre0, _⟩ := hslit'
  -- the imaginary part is `e^ξ sin θ`; it vanishes only at `θ = π`, where the real part is negative
  have himval : (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im = Real.exp ξ * Real.sin θ := by
    rw [Complex.exp_im, re_logPolar, im_logPolar]
  have hreval : (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re = Real.exp ξ * Real.cos θ := by
    rw [Complex.exp_re, re_logPolar, im_logPolar]
  rw [himval] at him
  have hsin0 : Real.sin θ = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h (Real.exp_pos ξ).ne'
    · exact h
  -- on `(0, 2π)` the sine vanishes only at `π`, where `cos π = -1`, contradicting `re ≥ 0`
  rcases lt_trichotomy θ π with hθπ | hθπ | hθπ
  · exact absurd hsin0 (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  · rw [hreval, hθπ, Real.cos_pi] at hre0
    nlinarith [Real.exp_pos ξ]
  · have hsinneg : Real.sin θ < 0 := by
      have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at this
      linarith
    exact absurd hsin0 hsinneg.ne

/-- The **open slit box** `{ξ₁ < Re w < ξ₂, 0 < Im w < 2π}` of log-polar parameters. -/
def openSlitBox (ξ₁ ξ₂ : ℝ) : Set ℂ :=
  {w : ℂ | ξ₁ < w.re ∧ w.re < ξ₂ ∧ 0 < w.im ∧ w.im < 2 * π}

theorem isOpen_openSlitBox (ξ₁ ξ₂ : ℝ) : IsOpen (openSlitBox ξ₁ ξ₂) := by
  have h1 : IsOpen {w : ℂ | ξ₁ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {w : ℂ | w.re < ξ₂} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {w : ℂ | w.im < 2 * π} := isOpen_lt Complex.continuous_im continuous_const
  have : openSlitBox ξ₁ ξ₂ = {w : ℂ | ξ₁ < w.re} ∩ {w : ℂ | w.re < ξ₂}
      ∩ {w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < 2 * π} := by
    ext w; simp only [openSlitBox, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

/-- **Holomorphy of the log-polar gradient on the slit box.** For the Grötzsch potential `v`
(harmonic on the ring), `expGrad v` is complex-differentiable at every point of the open slit box
whose log-radius is below `log s`. -/
theorem expGrad_differentiableAt_slitBox {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) {w : ℂ}
    (h1 : w.re < Real.log s) (h2 : 0 < w.im) (h3 : w.im < 2 * π) :
    DifferentiableAt ℂ (expGrad v) w := by
  have hw : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hmem : Complex.exp w ∈ grotzschRing s := by
    rw [hw]
    exact exp_mem_grotzschRing_slitBox hs0 hs1 h1 h2 h3
  have hg : DifferentiableAt ℂ (gradC v) (Complex.exp w) :=
    (gradC_differentiableOn hvh).differentiableAt
      ((isOpen_grotzschRing hs0.le).mem_nhds hmem)
  exact ((hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w))

/-- `expGrad v` is continuous on the open slit box. -/
theorem continuousOn_expGrad_slitBox {s ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) (hξ₂ : ξ₂ ≤ Real.log s)
    {ξ₁ : ℝ} :
    ContinuousOn (expGrad v) (openSlitBox ξ₁ ξ₂) := fun _w hw =>
  (expGrad_differentiableAt_slitBox hs0 hs1 hvh (lt_of_lt_of_le hw.2.1 hξ₂) hw.2.2.1
    hw.2.2.2).continuousAt.continuousWithinAt

/-- The derivative of `expGrad v` is continuous on the open slit box. -/
theorem continuousOn_deriv_expGrad_slitBox {s ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) (hξ₂ : ξ₂ ≤ Real.log s)
    {ξ₁ : ℝ} :
    ContinuousOn (deriv (expGrad v)) (openSlitBox ξ₁ ξ₂) := by
  have hdiff : DifferentiableOn ℂ (expGrad v) (openSlitBox ξ₁ ξ₂) := fun w hw =>
    (expGrad_differentiableAt_slitBox hs0 hs1 hvh (lt_of_lt_of_le hw.2.1 hξ₂) hw.2.2.1
      hw.2.2.2).differentiableWithinAt
  have hanalytic := hdiff.analyticOnNhd (isOpen_openSlitBox _ _)
  exact (hanalytic.deriv_of_isOpen (isOpen_openSlitBox _ _)).continuousOn

/-- **Off-axis bound for `expGrad v` on the slit box.** For log-radii in `[ξ₁, ξ₂]` with
`e^{ξ₂} < s` and any angle `θ` whose point is off the real axis, `‖expGrad v (ξ+θi)‖` is bounded
by a single constant: the modulus factor `e^ξ` is bounded on `[ξ₁, ξ₂]` and `‖gradC v‖` is bounded
off the axis on the closed annulus. -/
theorem exists_bound_expGrad_slitBox {s ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : Real.exp ξ₂ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ∃ C : ℝ, ∀ ξ ∈ Icc ξ₁ ξ₂, ∀ θ : ℝ, Real.sin θ ≠ 0 →
      ‖expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨Cg, hCg⟩ := exists_bound_gradC_annulus (r₁ := Real.exp ξ₁) (r₂ := Real.exp ξ₂)
    hs0 hs1 (Real.exp_pos ξ₁) hξ₂ hvh hvc hv0 hv1
  refine ⟨Real.exp ξ₂ * max Cg 0, fun ξ hξ θ hθ => ?_⟩
  set z : ℂ := Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) with hz
  have hznorm : ‖z‖ = Real.exp ξ := by rw [hz, Complex.norm_exp, re_logPolar]
  have hzim : z.im ≠ 0 := by
    rw [hz, Complex.exp_im, re_logPolar, im_logPolar]
    exact mul_ne_zero (Real.exp_pos ξ).ne' hθ
  have hr1 : Real.exp ξ₁ ≤ ‖z‖ := by rw [hznorm]; exact Real.exp_le_exp.mpr hξ.1
  have hr2 : ‖z‖ ≤ Real.exp ξ₂ := by rw [hznorm]; exact Real.exp_le_exp.mpr hξ.2
  have hgbound : ‖gradC v z‖ ≤ max Cg 0 := le_trans (hCg z hr1 hr2 hzim) (le_max_left _ _)
  have heq : expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I) = gradC v z * z := rfl
  rw [heq, norm_mul, hznorm]
  calc ‖gradC v z‖ * Real.exp ξ ≤ (max Cg 0) * Real.exp ξ₂ := by
        apply mul_le_mul hgbound (Real.exp_le_exp.mpr hξ.2) (Real.exp_pos ξ).le
          (le_max_right _ _)
    _ = Real.exp ξ₂ * max Cg 0 := by ring

/-- The pullback `w ↦ v(e^w)` is continuous on the left half-plane `{Re w < 0}` when `v` is
continuous on the closed unit disk: the exponential maps that half-plane into the open disk. -/
theorem continuous_slice_uexp_of_continuousOn_closedBall {v : ℂ → ℝ}
    (hvc : ContinuousOn v (Metric.closedBall (0 : ℂ) 1)) {ξ : ℝ} (hξ : ξ < 0) :
    Continuous fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp, re_logPolar]
    exact le_of_lt (by calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξ
      _ = 1 := Real.exp_zero)
  have hmemint : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp, re_logPolar]
    exact by calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξ
      _ = 1 := Real.exp_zero
  have hnb : Metric.closedBall (0 : ℂ) 1
      ∈ 𝓝 (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmemint) Metric.ball_subset_closedBall
  have hcv : ContinuousAt v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := hvc.continuousAt hnb
  have hg : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
    fun_prop
  exact ContinuousAt.comp hcv hg

/-! ### The slit-chart flux derivative via limiting integration by parts -/

/-- The log-polar point `ξ + θ·I` lies in the open slit box `{ξ₁ < Re < ξ₂, 0 < Im < 2π}` for
`ξ₁ < ξ < ξ₂` and `θ ∈ (0, 2π)`. -/
theorem logPolar_mem_openSlitBox {ξ₁ ξ₂ ξ θ : ℝ} (h1 : ξ₁ < ξ) (h2 : ξ < ξ₂)
    (hθ1 : 0 < θ) (hθ2 : θ < 2 * π) :
    ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ openSlitBox ξ₁ ξ₂ := by
  simp only [openSlitBox, Set.mem_setOf_eq, re_logPolar, im_logPolar]
  exact ⟨h1, h2, hθ1, hθ2⟩

/-- A horizontal slice `θ ↦ F(ξ+θi)` over `(0, 2π)` of a function continuous on the open slit
box is continuous there. -/
theorem continuousOn_slice_of_continuousOn_openSlitBox {F : ℂ → ℝ} {ξ₁ ξ₂ : ℝ}
    (hF : ContinuousOn F (openSlitBox ξ₁ ξ₂)) {ξ : ℝ} (h1 : ξ₁ < ξ) (h2 : ξ < ξ₂) :
    ContinuousOn (fun θ : ℝ => F ((ξ : ℂ) + (θ : ℂ) * Complex.I)) (Ioo 0 (2 * π)) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt (ContinuousAt.comp ?_ (by fun_prop))
  exact hF.continuousAt ((isOpen_openSlitBox _ _).mem_nhds
    (logPolar_mem_openSlitBox h1 h2 hθ.1 hθ.2))

/-- The endpoint offsets `π/(n+2)` tend to `0`. -/
theorem tendsto_piDivShrink : Tendsto (fun n : ℕ => π / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := hc.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]; push_cast; ring_nf
  have hmul : Tendsto (fun n : ℕ => π * ((1 : ℝ) / ((n : ℝ) + 2))) atTop (𝓝 (π * 0)) :=
    h.const_mul π
  rw [mul_zero] at hmul
  refine hmul.congr fun n => ?_
  rw [mul_one_div]

/-- **Endpoint-shrinking limit of the full-circle integral.** For a bounded measurable integrand
`f` on `(0, 2π)`, the integral over the shrunk interval `(π/(n+2), 2π − π/(n+2))` tends to the
integral over `(0, 2π)`: dominated convergence with the constant bound on the finite measure
`(0, 2π)`. -/
theorem tendsto_setIntegral_slitShrink {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioo 0 (2 * π))))
    (hbound : ∀ᵐ θ ∂(volume.restrict (Ioo 0 (2 * π))), ‖f θ‖ ≤ M) :
    Tendsto (fun n : ℕ => ∫ θ in Ioo (π / ((n : ℝ) + 2)) (2 * π - π / ((n : ℝ) + 2)), f θ)
      atTop (𝓝 (∫ θ in Ioo 0 (2 * π), f θ)) := by
  have hπ := Real.pi_pos
  set aₙ : ℕ → ℝ := fun n => π / ((n : ℝ) + 2) with haₙ
  have hsub : ∀ n : ℕ, Ioo (aₙ n) (2 * π - aₙ n) ⊆ Ioo 0 (2 * π) := by
    intro n θ hθ
    have hpn : (0 : ℝ) < aₙ n := by positivity
    exact ⟨lt_trans hpn hθ.1, lt_of_lt_of_le hθ.2 (by linarith)⟩
  -- rewrite each integral as an integral of the indicator over `(0, 2π)`
  set F : ℕ → ℝ → ℝ := fun n => (Ioo (aₙ n) (2 * π - aₙ n)).indicator f with hF
  have hFint : ∀ n : ℕ,
      (∫ θ in Ioo (aₙ n) (2 * π - aₙ n), f θ) = ∫ θ in Ioo 0 (2 * π), F n θ := by
    intro n
    rw [hF, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_self_of_subset_right (hsub n)]
  have hlimeq : (∫ θ in Ioo 0 (2 * π), f θ)
      = ∫ θ in Ioo 0 (2 * π), (Ioo 0 (2 * π)).indicator f θ := by
    rw [setIntegral_indicator measurableSet_Ioo, Set.inter_self]
  rw [hlimeq]
  refine (tendsto_integral_filter_of_norm_le_const (μ := volume.restrict (Ioo 0 (2 * π)))
    ?_ ?_ ?_).congr (fun n => (hFint n).symm)
  · exact Eventually.of_forall fun n =>
      (hmeas.indicator measurableSet_Ioo)
  · refine ⟨M, Eventually.of_forall fun n => ?_⟩
    filter_upwards [hbound] with θ hθb
    simp only [hF]
    by_cases hmem : θ ∈ Ioo (aₙ n) (2 * π - aₙ n)
    · rw [Set.indicator_of_mem hmem]; exact hθb
    · rw [Set.indicator_of_notMem hmem, norm_zero]; exact hM
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    rw [Set.indicator_of_mem hθ]
    -- eventually `θ ∈ Ioo (aₙ n) (2π − aₙ n)`, so `F n θ = f θ`
    have haθ : ∀ᶠ n : ℕ in atTop, aₙ n < min θ (2 * π - θ) := by
      have hminpos : 0 < min θ (2 * π - θ) := lt_min hθ.1 (by linarith [hθ.2])
      exact tendsto_piDivShrink.eventually_lt_const hminpos
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [haθ] with n hn
    have h1 : aₙ n < θ := lt_of_lt_of_le hn (min_le_left _ _)
    have h2 : θ < 2 * π - aₙ n := by
      have := lt_of_lt_of_le hn (min_le_right _ _); linarith
    have hmem : θ ∈ Ioo (aₙ n) (2 * π - aₙ n) := ⟨h1, h2⟩
    simp only [hF, Set.indicator_of_mem hmem]

/-- **Slit-chart angular derivative of the pullback.** For the Grötzsch potential `v` and a
log-radius `ξ < log s`, the pullback `θ ↦ v(e^{ξ+θi})` has angular derivative
`−Im (expGrad v (ξ+θi))` at every geometric angle `θ ∈ (0, 2π)`. -/
theorem hasDerivAt_uexp_angular_slit {s ξ θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ : ξ < Real.log s) (hθ1 : 0 < θ) (hθ2 : θ < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    HasDerivAt (fun t : ℝ => v (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
      (-(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ :=
  hasDerivAt_uexp_angular (differentiableAt_of_harmonicOnNhd hvh
    (exp_mem_grotzschRing_slitBox hs0 hs1 hξ hθ1 hθ2))

/-- **Slit-chart angular derivative of `Im (expGrad v)`.** For the Grötzsch potential `v` and a
log-radius `ξ < log s`, the map `θ ↦ Im (expGrad v (ξ+θi))` has angular derivative
`Re (deriv (expGrad v) (ξ+θi))` at every geometric angle `θ ∈ (0, 2π)`. -/
theorem hasDerivAt_im_expGrad_angular_slit {s ξ θ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ : ξ < Real.log s) (hθ1 : 0 < θ) (hθ2 : θ < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    HasDerivAt (fun t : ℝ => (expGrad v ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
      ((deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
  have hD := hasDerivAt_expGrad_angular (u := v) (ξ := ξ) (θ := θ)
    (expGrad_differentiableAt_slitBox hs0 hs1 hvh (by rw [re_logPolar]; exact hξ)
      (by rw [im_logPolar]; exact hθ1) (by rw [im_logPolar]; exact hθ2))
  have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
  simpa [Function.comp, Complex.mul_im] using hcomp

/-- **Angular integration by parts on a closed subinterval of the slit chart.** For the Grötzsch
potential `v` and a log-radius `ξ` with `e^ξ < s`, on a closed subinterval `[a, b] ⊆ (0, 2π)` the
angle integral of `v(e^{ξ+θi}) · Re (deriv (expGrad v))` equals the boundary term
`[v · Im (expGrad v)]_a^b` plus the integral of `(Im (expGrad v))²`. -/
theorem integral_uexp_re_deriv_expGrad_slit_Icc {s ξ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) (hξ0 : ξ < 0) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) :
    ∫ θ in a..b, v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in a..b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  have hπ := Real.pi_pos
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  have hvcball : ContinuousOn v (Metric.closedBall (0 : ℂ) 1) := by
    rwa [← closure_grotzschRing hs0.le]
  -- continuity of the three slice factors on `[a, b]`
  have hcont_f : ContinuousOn (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (uIcc a b) :=
    (continuous_slice_uexp_of_continuousOn_closedBall hvcball hξ0).continuousOn
  have hIcc : uIcc a b ⊆ Ioo 0 (2 * π) := by
    rw [uIcc_of_le hab]
    exact fun θ hθ => ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  have hcont_g : ContinuousOn (fun θ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      (uIcc a b) := by
    have hbox : ContinuousOn (fun w : ℂ => (expGrad v w).im) (openSlitBox (ξ - 1) (Real.log s)) :=
      Complex.continuous_im.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1))
    exact (continuousOn_slice_of_continuousOn_openSlitBox hbox
      (by linarith : ξ - 1 < ξ) hξlog).mono hIcc
  have hcont_g' : ContinuousOn
      (fun θ : ℝ => (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (uIcc a b) := by
    have hbox : ContinuousOn (fun w : ℂ => (deriv (expGrad v) w).re)
        (openSlitBox (ξ - 1) (Real.log s)) :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_deriv_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1))
    exact (continuousOn_slice_of_continuousOn_openSlitBox hbox
      (by linarith : ξ - 1 < ξ) hξlog).mono hIcc
  -- pointwise derivatives on the open interval
  have hf' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => v (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
        (-(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact hasDerivAt_uexp_angular_slit hs0 hs1 hξlog (lt_trans ha hθ.1)
      (lt_trans hθ.2 hb) hvh
  have hg' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => (expGrad v ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact hasDerivAt_im_expGrad_angular_slit hs0 hs1 hξlog (lt_trans ha hθ.1)
      (lt_trans hθ.2 hb) hvh
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f hcont_g hf' hg'
    (hcont_g.neg.intervalIntegrable) (hcont_g'.intervalIntegrable)
  have halg : ∫ θ in a..b, (-(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im
      = - ∫ θ in a..b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [hIBP, halg]
  ring

/-- The pullback `v(e^{ξ+θi})` vanishes at the slit endpoints `θ = 0` and `θ = 2π`: the point
`e^ξ` lies on the slit `[0, s]` when `e^ξ ≤ s`, and `e^{ξ+2πi} = e^ξ`. -/
theorem uexp_slit_endpoint_zero {s ξ : ℝ} (hξs : Real.exp ξ ≤ s) {v : ℂ → ℝ}
    (hv0 : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0) :
    v (Complex.exp ((ξ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = 0
      ∧ v (Complex.exp ((ξ : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I)) = 0 := by
  have hexp0 : Complex.exp ((ξ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = ((Real.exp ξ : ℝ) : ℂ) := by
    rw [show ((ξ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (ξ : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hexp2 : Complex.exp ((ξ : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I)
      = ((Real.exp ξ : ℝ) : ℂ) := by
    rw [show ((ξ : ℂ) + ((2 * π : ℝ) : ℂ) * Complex.I)
        = (ξ : ℂ) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, ← Complex.ofReal_exp]
  have hzero : v ((Real.exp ξ : ℝ) : ℂ) = 0 := by
    refine hv0 _ (by simp) ?_ ?_
    · rw [Complex.ofReal_re]; exact (Real.exp_pos ξ).le
    · rw [Complex.ofReal_re]; exact hξs
  exact ⟨by rw [hexp0, hzero], by rw [hexp2, hzero]⟩

/-! ### Conjugation symmetry of the log-polar gradient and its derivative -/

/-- **Conjugation of the holomorphic gradient.** For a conjugation-invariant potential `v`
(as the Grötzsch potential is), the holomorphic gradient satisfies
`gradC v (z̄) = conj (gradC v z)` at interior points. -/
theorem gradC_conj_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {z : ℂ} (hz : z ∈ grotzschRing s) :
    gradC v ((starRingEnd ℂ) z) = (starRingEnd ℂ) (gradC v z) := by
  have hconjz : (starRingEnd ℂ) z ∈ grotzschRing s := conj_mem_grotzschRing hs0.le hz
  -- near `z`, `v ∘ conj = v`
  have hnb : (fun w => v ((starRingEnd ℂ) w)) =ᶠ[𝓝 z] v := by
    filter_upwards [(isOpen_grotzschRing hs0.le).mem_nhds hz] with w hw
    exact grotzschPotential_conj hs0 hs1 hvh hvc hv0 hv1 w (subset_closure hw)
  have hdvcz : DifferentiableAt ℝ v ((starRingEnd ℂ) z) :=
    differentiableAt_of_harmonicOnNhd hvh hconjz
  have hconjd : HasFDerivAt (fun w : ℂ => (starRingEnd ℂ) w)
      (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) z := by
    have := Complex.conjLIE.toContinuousLinearEquiv.hasFDerivAt (x := z)
    refine this.congr_fderiv ?_
    ext w
    simp [Complex.conjLIE_apply, Complex.conjCLE_apply]
  have hcomp : HasFDerivAt v
      ((fderiv ℝ v ((starRingEnd ℂ) z)).comp
        (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap)) z :=
    (hdvcz.hasFDerivAt.comp z hconjd).congr_of_eventuallyEq hnb.symm
  have hfeq : fderiv ℝ v z
      = (fderiv ℝ v ((starRingEnd ℂ) z)).comp
          (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) := hcomp.fderiv
  -- evaluate `gradC` using `fderiv v z = (fderiv v z̄) ∘ conj`
  have hcoe : ∀ x : ℂ, (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap) x
      = (starRingEnd ℂ) x := fun x => by
    simp [Complex.conjLIE_apply]
  have hval1 : (fderiv ℝ v z) 1 = (fderiv ℝ v ((starRingEnd ℂ) z)) 1 := by
    rw [hfeq, ContinuousLinearMap.comp_apply, hcoe, map_one]
  have hvalI : (fderiv ℝ v z) Complex.I = -(fderiv ℝ v ((starRingEnd ℂ) z)) Complex.I := by
    rw [hfeq, ContinuousLinearMap.comp_apply, hcoe, Complex.conj_I, map_neg]
  rw [gradC, gradC, hval1, hvalI]
  simp only [map_sub, map_mul, Complex.conj_I, Complex.ofReal_neg, map_neg,
    Complex.conj_ofReal]
  ring

/-- **Conjugation of the log-polar gradient.** For a conjugation-invariant potential `v`, the
log-polar holomorphic gradient satisfies `expGrad v (w̄) = conj (expGrad v w)` whenever `e^w`
lies in the ring. -/
theorem expGrad_conj_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {w : ℂ} (hw : Complex.exp w ∈ grotzschRing s) :
    expGrad v ((starRingEnd ℂ) w) = (starRingEnd ℂ) (expGrad v w) := by
  have hexpconj : Complex.exp ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Complex.exp w) := by
    rw [← Complex.exp_conj]
  rw [expGrad, expGrad, hexpconj, gradC_conj_eq hs0 hs1 hvh hvc hv0 hv1 hw, map_mul]

/-- **Holomorphy of the log-polar gradient over the ring.** For the Grötzsch potential `v`,
`expGrad v` is complex-differentiable at every `w` whose exponential lies in the ring. -/
theorem expGrad_differentiableAt_ring {s : ℝ} (hs0 : 0 < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) {w : ℂ}
    (hw : Complex.exp w ∈ grotzschRing s) :
    DifferentiableAt ℂ (expGrad v) w := by
  have hg : DifferentiableAt ℂ (gradC v) (Complex.exp w) :=
    (gradC_differentiableOn hvh).differentiableAt
      ((isOpen_grotzschRing hs0.le).mem_nhds hw)
  exact ((hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w))

/-- **Conjugation of the derivative of the log-polar gradient.** For a conjugation-invariant
potential `v`, the derivative of `expGrad v` satisfies
`deriv (expGrad v) (w̄) = conj (deriv (expGrad v) w)` at points where `e^w` and a neighborhood
lie in the ring. -/
theorem deriv_expGrad_conj_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    {w : ℂ} (hw : Complex.exp w ∈ grotzschRing s) :
    deriv (expGrad v) ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv (expGrad v) w) := by
  have hdw : HasDerivAt (expGrad v) (deriv (expGrad v) w) w :=
    (expGrad_differentiableAt_ring hs0 hvh hw).hasDerivAt
  -- `conj ∘ expGrad v ∘ conj` has derivative `conj (deriv (expGrad v) w)` at `conj w`
  have hconj := hdw.conj_conj
  -- near `conj w`, `conj ∘ expGrad v ∘ conj = expGrad v`
  have hopen : IsOpen {x : ℂ | Complex.exp x ∈ grotzschRing s} :=
    (isOpen_grotzschRing hs0.le).preimage Complex.continuous_exp
  have hmemcw : (starRingEnd ℂ) w ∈ {x : ℂ | Complex.exp x ∈ grotzschRing s} := by
    change Complex.exp ((starRingEnd ℂ) w) ∈ grotzschRing s
    rw [Complex.exp_conj]; exact conj_mem_grotzschRing hs0.le hw
  have hnb : (⇑(starRingEnd ℂ) ∘ expGrad v ∘ ⇑(starRingEnd ℂ))
      =ᶠ[𝓝 ((starRingEnd ℂ) w)] expGrad v := by
    filter_upwards [hopen.mem_nhds hmemcw] with x hx
    have hxring : Complex.exp x ∈ grotzschRing s := hx
    -- `expGrad v (conj x) = conj (expGrad v x)`
    have heq := expGrad_conj_eq hs0 hs1 hvh hvc hv0 hv1 hxring
    simp only [Function.comp_apply, heq, Complex.conj_conj]
  have hconj' : HasDerivAt (expGrad v) ((starRingEnd ℂ) (deriv (expGrad v) w))
      ((starRingEnd ℂ) w) := hconj.congr_of_eventuallyEq hnb.symm
  exact hconj'.deriv

/-! ### Continuity of the flux integrand on interior slit boxes -/

/-- Every point of the strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}` with `ξ₂ ≤ log s`,
`0 < a`, `b < 2π` has its exponential in the Grötzsch ring. -/
theorem stripBox_exp_mem_grotzschRing {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {w : ℂ}
    (hw : w ∈ stripBox ξ₁ ξ₂ a b) :
    Complex.exp w ∈ grotzschRing s := by
  obtain ⟨_, hre, him1, him2⟩ := hw
  have hwrepr : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hwrepr]
  exact exp_mem_grotzschRing_slitBox hs0 hs1 (lt_of_lt_of_le hre hξ₂)
    (lt_of_lt_of_le ha him1) (lt_of_le_of_lt him2 hb)

/-- The pullback `w ↦ v(e^w)` is continuous on any interior slit strip box. -/
theorem continuousOn_uexp_stripBox {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (fun w => v (Complex.exp w)) (stripBox ξ₁ ξ₂ a b) := by
  intro w hw
  have hmem := stripBox_exp_mem_grotzschRing hs0 hs1 hξ₂ ha hb hw
  have hc : ContinuousAt v (Complex.exp w) := (hvh _ hmem).1.continuousAt
  exact (hc.comp Complex.continuous_exp.continuousAt).continuousWithinAt

/-- `expGrad v` is continuous on any interior slit strip box. -/
theorem continuousOn_expGrad_stripBox {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (expGrad v) (stripBox ξ₁ ξ₂ a b) := fun _w hw =>
  (expGrad_differentiableAt_ring hs0 hvh
    (stripBox_exp_mem_grotzschRing hs0 hs1 hξ₂ ha hb hw)).continuousAt.continuousWithinAt

/-- The derivative of `expGrad v` is continuous on any interior slit strip box. -/
theorem continuousOn_deriv_expGrad_stripBox {s ξ₁ ξ₂ a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂ : ξ₂ ≤ Real.log s) (ha : 0 < a) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (deriv (expGrad v)) (stripBox ξ₁ ξ₂ a b) := by
  intro w hw
  obtain ⟨hre1, hre2, him1, him2⟩ := hw
  have hmemopen : w ∈ openSlitBox ξ₁ (Real.log s) :=
    ⟨hre1, lt_of_lt_of_le hre2 hξ₂, lt_of_lt_of_le ha him1, lt_of_le_of_lt him2 hb⟩
  exact ((continuousOn_deriv_expGrad_slitBox hs0 hs1 hvh (le_refl _)).continuousAt
    ((isOpen_openSlitBox _ _).mem_nhds hmemopen)).continuousWithinAt

/-! ### The truncated slit flux and its derivative -/

/-- The **truncated slit flux** of `v` over the angle window `(a, b)`: the angle integral of
`v(e^{ξ+θi}) · Re (expGrad v (ξ+θi))`. -/
def truncFlux (v : ℂ → ℝ) (a b ξ : ℝ) : ℝ :=
  ∫ θ in Ioo a b, v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re

/-- **Derivative of the truncated slit flux.** For the Grötzsch potential `v` and a window
`[a, b] ⊆ (0, 2π)`, at a log-radius `ξ < log s`, `ξ < 0`, the truncated flux has derivative the
window integral of `|expGrad v|²`: differentiation under the integral sign gives
`(Re expGrad)² + v · Re (deriv expGrad)`, and the angular integration by parts on the closed
window `[a, b]` converts the second term into the boundary term plus `(Im expGrad)²`. -/
theorem hasDerivAt_truncFlux {s a b ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) (hξ0 : ξ < 0) (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π)
    {v : ℂ → ℝ} (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s))) :
    HasDerivAt (truncFlux v a b)
      (v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))) ξ := by
  have hπ := Real.pi_pos
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  -- work over the strip box `{ξ − 1 < Re < log s, a ≤ Im ≤ b}`
  set ξ₁ : ℝ := ξ - 1 with hξ₁
  set ξ₂ : ℝ := Real.log s with hξ₂
  have hξ₂le : ξ₂ ≤ Real.log s := le_refl _
  have hGcont : ContinuousOn (fun w => v (Complex.exp w) * (expGrad v w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    (continuousOn_uexp_stripBox hs0 hs1 hξ₂le ha hb hvh).mul
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_stripBox hs0 hs1 hξ₂le ha hb hvh))
  have hG'cont : ContinuousOn
      (fun w => (expGrad v w).re ^ 2 + v (Complex.exp w) * (deriv (expGrad v) w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    (((Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_stripBox hs0 hs1 hξ₂le ha hb hvh)).pow 2).add
      ((continuousOn_uexp_stripBox hs0 hs1 hξ₂le ha hb hvh).mul
        (Complex.continuous_re.comp_continuousOn
          (continuousOn_deriv_expGrad_stripBox hs0 hs1 hξ₂le ha hb hvh))))
  -- product rule along each radial line
  have hd : ∀ x θ : ℝ, ξ₁ < x → x < ξ₂ → a < θ → θ < b →
      HasDerivAt (fun y : ℝ => v (Complex.exp ((y : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad v ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((expGrad v ((x : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + v (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
            * (deriv (expGrad v) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
    intro x θ hx1 hx2 hθ1 hθ2
    have hmemring : Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hx2 (lt_trans ha hθ1) (lt_trans hθ2 hb)
    have hu' := hasDerivAt_uexp_radial (u := v) (ξ := x) (θ := θ)
      (differentiableAt_of_harmonicOnNhd hvh hmemring)
    have hD := hasDerivAt_expGrad_radial (u := v) (ξ := x) (θ := θ)
      (expGrad_differentiableAt_ring hs0 hvh hmemring)
    have hDre : HasDerivAt (fun y : ℝ => (expGrad v ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((deriv (expGrad v) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
      have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hD
      simpa [Function.comp] using hcomp
    refine (hu'.mul hDre).congr_deriv ?_
    ring
  have hDUI := hasDerivAt_integral_stripBox hab hGcont hG'cont hd
    (show ξ₁ < ξ by rw [hξ₁]; linarith) hξlog
  -- convert the derivative value via the slit-chart integration by parts
  have hint1 : IntegrableOn
      (fun θ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2) (Ioo a b) := by
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact (((hsl.pow 2).mono (fun θ hθ =>
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
  have hint2 : IntegrableOn
      (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b) := by
    have hslv := (continuous_slice_uexp_of_continuousOn_closedBall
      (by rwa [← closure_grotzschRing hs0.le] : ContinuousOn v (Metric.closedBall (0 : ℂ) 1))
      hξ0).continuousOn (s := Icc a b)
    have hsld := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_deriv_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact ((hslv.mul ((hsld.mono (fun θ hθ =>
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)))).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
  have hint3 : IntegrableOn
      (fun θ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) (Ioo a b) := by
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_im.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact (((hsl.pow 2).mono (fun θ hθ =>
      ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self)
  have hval : (∫ θ in Ioo a b,
      ((expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    rw [integral_add hint1 hint2]
    -- convert the second term via the slit integration by parts (in `Ioo` form)
    have hIBP := integral_uexp_re_deriv_expGrad_slit_Icc hs0 hs1 hξs hξ0 hvh hvc ha hab hb
    have hIBP' : (∫ θ in Ioo a b, v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad v) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        = v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
          - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
              * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
          + ∫ θ in Ioo a b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
      rw [integral_Ioo_eq_intervalIntegral hab, hIBP,
        integral_Ioo_eq_intervalIntegral hab]
    rw [hIBP']
    have hnormeq : (∫ θ in Ioo a b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2)
          + ∫ θ in Ioo a b, (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        = ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [← integral_add hint1 hint3]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [Complex.normSq_apply]; ring
    linarith [hnormeq]
  rw [hval] at hDUI
  exact hDUI

/-- The derivative value of the truncated slit flux: the angular boundary term of the integration
by parts plus the window integral of the squared log-polar gradient. -/
def truncFluxDeriv (v : ℂ → ℝ) (a b ξ : ℝ) : ℝ :=
  v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
      * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
    - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
    + ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- Continuity in the log-radius of the pullback `ξ ↦ v(e^{ξ+θi})` at a ring point. -/
theorem continuousAt_uexp_line {θ ξ : ℝ} {s : ℝ} {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s) :
    ContinuousAt (fun x : ℝ => v (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ξ :=
  (hasDerivAt_uexp_radial (differentiableAt_of_harmonicOnNhd hvh hmem)).continuousAt

/-- Continuity in the log-radius of `ξ ↦ expGrad v (ξ+θi)` at a ring point. -/
theorem continuousAt_expGrad_line {s θ ξ : ℝ} (hs0 : 0 < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s) :
    ContinuousAt (fun x : ℝ => expGrad v ((x : ℂ) + (θ : ℂ) * Complex.I)) ξ :=
  (hasDerivAt_expGrad_radial (expGrad_differentiableAt_ring hs0 hvh hmem)).continuousAt

/-- **Continuity of the truncated-flux derivative.** For the Grötzsch potential `v` and a window
`[a, b] ⊆ (0, 2π)`, the derivative value `truncFluxDeriv v a b` is continuous on the half-line
`(−∞, log s)`. -/
theorem continuousOn_truncFluxDeriv {s a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ContinuousOn (truncFluxDeriv v a b) (Iio (Real.log s)) := by
  have hπ := Real.pi_pos
  -- the boundary factors are continuous in `ξ` (fixed angle in `(0, 2π)`)
  have hbdry : ∀ θ : ℝ, 0 < θ → θ < 2 * π →
      ContinuousOn (fun ξ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) (Iio (Real.log s)) := by
    intro θ hθ1 hθ2 ξ hξ
    have hξlt : ξ < Real.log s := hξ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξlt hθ1 hθ2
    have hcv := continuousAt_uexp_line hvh hmem
    have hcg : ContinuousAt
        (fun ξ : ℝ => (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) ξ :=
      Complex.continuous_im.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hmem)
    exact (hcv.mul hcg).continuousWithinAt
  -- the window integral of `normSq` is continuous in `ξ`
  have hint : ContinuousOn (fun ξ : ℝ =>
      ∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Iio (Real.log s)) := by
    intro ξ₀ hξ₀
    have hξ₀lt : ξ₀ < Real.log s := hξ₀
    obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab (show ξ₀ - 1 < ξ₀ by linarith) hξ₀lt
    have hcont : ContinuousOn (fun w => Complex.normSq (expGrad v w))
        (stripBox (ξ₀ - 1) (Real.log s) a b) :=
      Complex.continuous_normSq.comp_continuousOn
        (continuousOn_expGrad_stripBox hs0 hs1 (le_refl _) ha hb hvh)
    obtain ⟨C, hC⟩ := exists_bound_on_stripBox hcont hδsub
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated (bound := fun _ => C)
    · filter_upwards [Iio_mem_nhds hξ₀lt] with ξ hξ
      have hξlt : ξ < Real.log s := hξ
      have hsl := continuousOn_slice_of_continuousOn_openSlitBox
        (Complex.continuous_normSq.comp_continuousOn
          (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
        (show ξ - 1 < ξ by linarith) hξlt
      have hIoosub : Ioo a b ⊆ Ioo 0 (2 * π) :=
        fun θ hθ => ⟨lt_trans ha hθ.1, lt_trans hθ.2 hb⟩
      exact (hsl.mono hIoosub).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with ξ hξ
      have hξ' : ξ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hξ
        exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      exact hC ξ hξ' θ (Ioo_subset_Icc_self hθ)
    · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      have hmem : Complex.exp ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
        exp_mem_grotzschRing_slitBox hs0 hs1 hξ₀lt (lt_trans ha hθ.1) (lt_trans hθ.2 hb)
      exact Complex.continuous_normSq.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hmem)
  exact ((hbdry b (lt_of_lt_of_le ha hab) hb).sub (hbdry a ha (lt_of_le_of_lt hab hb))).add hint

/-- **Fundamental theorem of calculus for the truncated slit flux.** For the Grötzsch potential
`v` and a window `[a, b] ⊆ (0, 2π)`, on the half-line of log-radii below `log s` the increment of
the truncated flux is the integral of its derivative value. -/
theorem truncFlux_sub_eq_integral {s a b ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (h12 : ξ₁ ≤ ξ₂) (hξ₂ : ξ₂ < 0) (hξ₂s : ξ₂ < Real.log s) :
    truncFlux v a b ξ₂ - truncFlux v a b ξ₁
      = ∫ ξ in ξ₁..ξ₂, truncFluxDeriv v a b ξ := by
  have hsub : Icc ξ₁ ξ₂ ⊆ Iio (Real.log s) := fun x hx => lt_of_le_of_lt hx.2 hξ₂s
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_).symm
  · rw [uIcc_of_le h12] at hx
    have hxlt : x < Real.log s := lt_of_le_of_lt hx.2 hξ₂s
    have hxexp : Real.exp x < s := (Real.lt_log_iff_exp_lt hs0).mp hxlt
    have hx0 : x < 0 := lt_of_le_of_lt hx.2 hξ₂
    have := hasDerivAt_truncFlux hs0 hs1 hxexp hx0 ha hab hb hvh hvc
    exact this
  · exact ((continuousOn_truncFluxDeriv hs0 hs1 ha hab hb hvh).mono
      (by rw [uIcc_of_le h12]; exact hsub)).intervalIntegrable

/-- The slit-chart ring flux in log-polar form: `ringFluxSlit v ξ` is the angle integral
`∫_{(0,2π)} v(e^{ξ+θi}) · Re (expGrad v (ξ+θi))`. -/
theorem ringFluxSlit_eq (v : ℂ → ℝ) (ξ : ℝ) :
    ringFluxSlit v ξ = ∫ θ in Ioo 0 (2 * π),
      v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  unfold ringFluxSlit
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [fderiv_eq_re_gradC_mul]
  rfl

/-- `truncFlux v a b ξ` equals `ringFluxSlit v ξ` restricted to the window `(a, b)`. -/
theorem truncFlux_eq_setIntegral (v : ℂ → ℝ) (a b ξ : ℝ) :
    truncFlux v a b ξ = ∫ θ in Ioo a b,
      v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := rfl

/-- The single-circle energy density `ξ ↦ ∫_{(0,2π)} |expGrad v (ξ+θi)|²`. -/
def sliceEnergy (v : ℂ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ θ in Ioo 0 (2 * π), Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- **The angle at the shrink endpoint has nonzero sine, eventually.** For `θ ∈ (0, π)`,
`sin θ ≠ 0`. -/
theorem sin_ne_zero_of_mem_Ioo_pi {θ : ℝ} (h1 : 0 < θ) (h2 : θ < π) : Real.sin θ ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi h1 h2).ne'

/-- **A.e. bound for `sin θ ≠ 0` on `(0, 2π)`.** The sine vanishes on `(0, 2π)` only at `θ = π`,
a single point, so `sin θ ≠ 0` holds almost everywhere on the window. -/
theorem ae_sin_ne_zero_Ioo :
    ∀ᵐ θ ∂(volume.restrict (Ioo 0 (2 * π))), Real.sin θ ≠ 0 := by
  have hnull : volume ({π} : Set ℝ) = 0 := by simp
  refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
  filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hnull)] with θ hθπ hmem
  have hθ : θ ∈ Ioo 0 (2 * π) := hmem
  rcases lt_trichotomy θ π with hlt | heq | hgt
  · exact sin_ne_zero_of_mem_Ioo_pi hθ.1 hlt
  · exact absurd (by rw [heq]; rfl : θ ∈ ({π} : Set ℝ)) hθπ
  · have := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith [hθ.2])
    rw [Real.sin_sub_pi] at this
    linarith

/-- **Convergence of the truncated flux to the slit flux.** For the Grötzsch potential `v` with
values in `[0, 1]`, at a log-radius `ξ` with `e^ξ < s`, the truncated flux over the shrinking
windows converges to the slit-chart flux. -/
theorem tendsto_truncFlux_ringFluxSlit {s ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    Tendsto (fun n : ℕ =>
      truncFlux v (π / ((n : ℝ) + 2)) (2 * π - π / ((n : ℝ) + 2)) ξ)
      atTop (𝓝 (ringFluxSlit v ξ)) := by
  have hπ := Real.pi_pos
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξs hvh hvc hv0 hv1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
    (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
  rw [ringFluxSlit_eq]
  have hf : (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      = fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := rfl
  -- the integrand is a.e. measurable and bounded on `(0, 2π)`
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      (volume.restrict (Ioo 0 (2 * π))) := by
    have hslv : ContinuousOn (fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (Ioo 0 (2 * π)) :=
      (continuous_slice_uexp_of_continuousOn_closedBall
        (by rwa [← closure_grotzschRing hs0.le] : ContinuousOn v (Metric.closedBall (0 : ℂ) 1))
        (by linarith [(Real.exp_lt_one_iff.mp (lt_trans hξs hs1))] : ξ < 0)).continuousOn
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) ((Real.lt_log_iff_exp_lt hs0).mpr hξs)
    exact (hslv.mul hsl).aestronglyMeasurable measurableSet_Ioo
  have hbound : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo 0 (2 * π))),
      ‖v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re‖ ≤ M := by
    have hmemfilter : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo 0 (2 * π))),
        θ ∈ Ioo 0 (2 * π) := (ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall fun θ hθ => hθ)
    filter_upwards [ae_sin_ne_zero_Ioo, hmemfilter] with θ hsin hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 ((Real.lt_log_iff_exp_lt hs0).mpr hξs) hθ.1 hθ.2
    have hv1' : |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [(hvrange _ hmem).1], (hvrange _ hmem).2⟩
    have hre : |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ M :=
      le_trans (Complex.abs_re_le_norm _) (hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin)
    rw [Real.norm_eq_abs, abs_mul]
    calc |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))|
          * |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|
        ≤ 1 * M := mul_le_mul hv1' hre (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  exact tendsto_setIntegral_slitShrink hMnn hmeas hbound

/-- **Pointwise convergence of the truncated-flux derivative to the slice energy.** For the
Grötzsch potential `v`, at a log-radius `ξ` with `e^ξ < s`, the truncated-flux derivative over
the shrinking windows converges to the single-circle energy density: the boundary terms vanish
because the potential vanishes at the slit endpoints while `Im (expGrad v)` stays bounded, and the
window energy converges to the full-circle energy. -/
theorem tendsto_truncFluxDeriv_sliceEnergy {s ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    Tendsto (fun n : ℕ =>
      truncFluxDeriv v (π / ((n : ℝ) + 2)) (2 * π - π / ((n : ℝ) + 2)) ξ)
      atTop (𝓝 (sliceEnergy v ξ)) := by
  have hπ := Real.pi_pos
  have hξ0 : ξ < 0 := by
    have := Real.exp_lt_one_iff.mp (lt_trans hξs hs1); linarith
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  have hv0' : ∀ z : ℂ, z.im = 0 → 0 ≤ z.re → z.re ≤ s → v z = 0 := fun z hzi hz0 hzs =>
    hv0 z (by rw [grotzschInner_eq hs0.le]; exact ⟨hzi, hz0, hzs⟩)
  set aₙ : ℕ → ℝ := fun n => π / ((n : ℝ) + 2) with haₙ
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξs hvh hvc hv0 hv1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
    (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
  -- the window energy converges to the full-circle energy
  have hwin : Tendsto (fun n : ℕ =>
      ∫ θ in Ioo (aₙ n) (2 * π - aₙ n),
        Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      atTop (𝓝 (sliceEnergy v ξ)) := by
    have hmeas : AEStronglyMeasurable
        (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (volume.restrict (Ioo 0 (2 * π))) := by
      have hsl := continuousOn_slice_of_continuousOn_openSlitBox
        (Complex.continuous_normSq.comp_continuousOn
          (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
        (by linarith : ξ - 1 < ξ) hξlog
      exact hsl.aestronglyMeasurable measurableSet_Ioo
    have hbound : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo 0 (2 * π))),
        ‖Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖ ≤ M ^ 2 := by
      filter_upwards [ae_sin_ne_zero_Ioo] with θ hsin
      have hb := hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb, hMnn]
    exact tendsto_setIntegral_slitShrink (by positivity) hmeas hbound
  -- the boundary terms vanish
  obtain ⟨hva0, hvb0⟩ := uexp_slit_endpoint_zero hξs.le hv0'
  have hbdry : Tendsto (fun n : ℕ =>
      v (Complex.exp ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)).im)
      atTop (𝓝 0) := by
    -- `v(e^{ξ+aₙi}) → 0` and `Im(expGrad)` bounded, so each product → 0
    have hvcont : Continuous fun θ : ℝ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      continuous_slice_uexp_of_continuousOn_closedBall
        (by rwa [← closure_grotzschRing hs0.le]) hξ0
    have haₙ0 : Tendsto aₙ atTop (𝓝 0) := tendsto_piDivShrink
    have hb2π : Tendsto (fun n => 2 * π - aₙ n) atTop (𝓝 (2 * π)) := by
      have := haₙ0.const_sub (2 * π); simpa using this
    -- `v` at the moving endpoints tends to the endpoint values `0`
    have hva : Tendsto (fun n => v (Complex.exp ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
      have hc := (hvcont.tendsto 0).comp haₙ0
      simp only [Function.comp_def, hva0] at hc
      exact hc
    have hvb : Tendsto (fun n => v (Complex.exp ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)))
        atTop (𝓝 0) := by
      have hc := (hvcont.tendsto (2 * π)).comp hb2π
      simp only [Function.comp_def, hvb0] at hc
      exact hc
    -- boundedness of `Im (expGrad)` at the moving endpoints
    have hboundedA : ∀ᶠ n : ℕ in atTop,
        ‖(expGrad v ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)).im‖ ≤ M := by
      filter_upwards [haₙ0.eventually_lt_const (show (0:ℝ) < π by linarith),
        eventually_gt_atTop 0] with n hlt _
      have hpos : 0 < aₙ n := by positivity
      exact le_trans (Complex.abs_im_le_norm _)
        (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (aₙ n) (sin_ne_zero_of_mem_Ioo_pi hpos hlt))
    have hboundedB : ∀ᶠ n : ℕ in atTop,
        ‖(expGrad v ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)).im‖ ≤ M := by
      filter_upwards [haₙ0.eventually_lt_const (show (0:ℝ) < π by linarith)] with n hlt
      have hpos : 0 < aₙ n := by positivity
      have hgt : π < 2 * π - aₙ n := by linarith
      have hlt2 : 2 * π - aₙ n < 2 * π := by linarith
      have hsin : Real.sin (2 * π - aₙ n) ≠ 0 := by
        have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * π - aₙ n - π) (by linarith) (by linarith)
        rw [Real.sin_sub_pi] at this; linarith
      exact le_trans (Complex.abs_im_le_norm _)
        (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (2 * π - aₙ n) hsin)
    have hlimz : Tendsto (fun n : ℕ => ‖v (Complex.exp ((ξ : ℂ)
        + ((aₙ n : ℝ) : ℂ) * Complex.I))‖ * M) atTop (𝓝 0) := by
      have := hva.norm.mul_const M; simpa using this
    have hlimzB : Tendsto (fun n : ℕ => ‖v (Complex.exp ((ξ : ℂ)
        + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I))‖ * M) atTop (𝓝 0) := by
      have := hvb.norm.mul_const M; simpa using this
    have hprodA : Tendsto (fun n => v (Complex.exp ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + ((aₙ n : ℝ) : ℂ) * Complex.I)).im) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlimz
      filter_upwards [hboundedA] with n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have hprodB : Tendsto (fun n => v (Complex.exp ((ξ : ℂ)
        + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + ((2 * π - aₙ n : ℝ) : ℂ) * Complex.I)).im) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlimzB
      filter_upwards [hboundedB] with n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have := hprodB.sub hprodA
    simpa using this
  -- combine: truncFluxDeriv = boundary + window energy
  have hcomb := hbdry.add hwin
  rw [zero_add] at hcomb
  refine hcomb.congr fun n => ?_
  rw [truncFluxDeriv]

/-- **Uniform bound on the truncated-flux derivative.** With the log-polar gradient bound `M` on
the closed slab `[ξ₁, ξ₂]`, and `v` valued in `[0, 1]`, the truncated-flux derivative is bounded
by `2M + 2π·M²` uniformly over the shrinking windows and over `ξ ∈ [ξ₁, ξ₂]`. -/
theorem truncFluxDeriv_norm_le {s ξ₁ ξ₂ a b ξ M : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξlt : ξ < Real.log s) (ha : 0 < a) (hab : a ≤ b) (hb : b < 2 * π) {v : ℂ → ℝ}
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1)
    (hM : ∀ ξ ∈ Icc ξ₁ ξ₂, ∀ θ : ℝ, Real.sin θ ≠ 0 →
      ‖expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ M) (hMnn : 0 ≤ M)
    (hξIcc : ξ ∈ Icc ξ₁ ξ₂) (hsa : Real.sin a ≠ 0) (hsb : Real.sin b ≠ 0) :
    ‖truncFluxDeriv v a b ξ‖ ≤ 2 * M + 2 * π * M ^ 2 := by
  have hπ := Real.pi_pos
  -- bound on the boundary factor at an off-axis angle in `(0, 2π)`
  have hbdry : ∀ θ : ℝ, 0 < θ → θ < 2 * π → Real.sin θ ≠ 0 →
      ‖v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im‖ ≤ M := by
    intro θ hθ1 hθ2 hsin
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξlt hθ1 hθ2
    have hv1' : |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [(hvrange _ hmem).1], (hvrange _ hmem).2⟩
    have him : |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im| ≤ M :=
      le_trans (Complex.abs_im_le_norm _) (hM ξ hξIcc θ hsin)
    rw [Real.norm_eq_abs, abs_mul]
    calc |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))|
          * |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im|
        ≤ 1 * M := mul_le_mul hv1' him (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  -- bound on the window energy integral (a.e. away from `θ = π`)
  have hwin : ‖∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖
      ≤ 2 * π * M ^ 2 := by
    have hbd : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ioo a b)),
        ‖Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖ ≤ M ^ 2 := by
      have hsubset : Ioo a b ⊆ Ioo 0 (2 * π) :=
        fun θ hθ => ⟨lt_trans ha hθ.1, lt_trans hθ.2 hb⟩
      have hsub : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo a b)), Real.sin θ ≠ 0 :=
        ae_mono (Measure.restrict_mono hsubset (le_refl _)) ae_sin_ne_zero_Ioo
      filter_upwards [hsub] with θ hsin
      have hb2 := hM ξ hξIcc θ hsin
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb2, hMnn]
    have hnorm := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (s := Ioo a b)
      (C := M ^ 2) measure_Ioo_lt_top hbd
    have hvol : (volume : Measure ℝ).real (Ioo a b) ≤ 2 * π := by
      rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; linarith
    calc ‖∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖
        ≤ M ^ 2 * (volume : Measure ℝ).real (Ioo a b) := hnorm
      _ ≤ M ^ 2 * (2 * π) := mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = 2 * π * M ^ 2 := by ring
  rw [truncFluxDeriv]
  calc ‖_ + _‖ ≤ ‖v (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - v (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad v ((ξ : ℂ) + (a : ℂ) * Complex.I)).im‖
      + ‖∫ θ in Ioo a b, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))‖ :=
        norm_add_le _ _
    _ ≤ (M + M) + 2 * π * M ^ 2 := by
        refine add_le_add (le_trans (norm_sub_le _ _) (add_le_add
          (hbdry b (lt_of_lt_of_le ha hab) hb hsb) (hbdry a ha (lt_of_le_of_lt hab hb) hsa))) hwin
    _ = 2 * M + 2 * π * M ^ 2 := by ring

/-- **Slit flux increment as a slice-energy integral.** For the Grötzsch potential `v` with values
in `[0, 1]`, on the log-radii below `log s` the increment of the slit-chart flux equals the
integral of the single-circle energy density: the truncated-window fundamental theorem of calculus
passes to the limit, the interior integrals converging by bounded convergence with the log-polar
gradient bound. -/
theorem ringFluxSlit_sub_eq_integral {s ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂s : Real.exp ξ₂ < s) (h12 : ξ₁ ≤ ξ₂) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ringFluxSlit v ξ₂ - ringFluxSlit v ξ₁ = ∫ ξ in ξ₁..ξ₂, sliceEnergy v ξ := by
  have hπ := Real.pi_pos
  have hξ₂log : ξ₂ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξ₂s
  have hξ₂0 : ξ₂ < 0 := by
    have := Real.exp_lt_one_iff.mp (lt_trans hξ₂s hs1); linarith
  set aₙ : ℕ → ℝ := fun n => π / ((n : ℝ) + 2) with haₙ
  have haₙpos : ∀ n, 0 < aₙ n := fun n => by positivity
  have haₙle : ∀ n, aₙ n ≤ 2 * π - aₙ n := by
    intro n
    have h2 : aₙ n ≤ π / 2 := by
      rw [haₙ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have haₙlt : ∀ n, 2 * π - aₙ n < 2 * π := fun n => by linarith [haₙpos n]
  -- slab bound on `expGrad` over `[ξ₁, ξ₂]`
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ₁) (ξ₂ := ξ₂) hs0 hs1 hξ₂s hvh hvc hv0 hv1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
    (hM ξ₂ (right_mem_Icc.mpr h12) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
  -- the per-`n` fundamental theorem of calculus
  have hFTC : ∀ n : ℕ, truncFlux v (aₙ n) (2 * π - aₙ n) ξ₂
      - truncFlux v (aₙ n) (2 * π - aₙ n) ξ₁
      = ∫ ξ in ξ₁..ξ₂, truncFluxDeriv v (aₙ n) (2 * π - aₙ n) ξ := fun n =>
    truncFlux_sub_eq_integral hs0 hs1 (haₙpos n) (haₙle n) (haₙlt n) hvh hvc h12 hξ₂0 hξ₂log
  -- LHS converges to the slit-flux increment
  have hLHS : Tendsto (fun n : ℕ => truncFlux v (aₙ n) (2 * π - aₙ n) ξ₂
      - truncFlux v (aₙ n) (2 * π - aₙ n) ξ₁) atTop
      (𝓝 (ringFluxSlit v ξ₂ - ringFluxSlit v ξ₁)) :=
    (tendsto_truncFlux_ringFluxSlit hs0 hs1 hξ₂s hvh hvc hv0 hv1 hvrange).sub
      (tendsto_truncFlux_ringFluxSlit hs0 hs1 (lt_of_le_of_lt (Real.exp_le_exp.mpr h12) hξ₂s)
        hvh hvc hv0 hv1 hvrange)
  -- RHS converges to the slice-energy integral, by bounded convergence over `[ξ₁, ξ₂]`
  -- eventual nonzero-sine of the shrink endpoints (needed for the uniform bound)
  have hsaₙ : ∀ n : ℕ, Real.sin (aₙ n) ≠ 0 := by
    intro n
    have h2 : aₙ n ≤ π / 2 := by
      rw [haₙ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact sin_ne_zero_of_mem_Ioo_pi (haₙpos n) (by linarith)
  have hsbₙ : ∀ n : ℕ, Real.sin (2 * π - aₙ n) ≠ 0 := by
    intro n
    have h2 : aₙ n ≤ π / 2 := by
      rw [haₙ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have := Real.sin_pos_of_pos_of_lt_pi (x := 2 * π - aₙ n - π)
      (by linarith [haₙpos n]) (by linarith [haₙpos n])
    rw [Real.sin_sub_pi] at this; linarith
  have hRHS : Tendsto (fun n : ℕ => ∫ ξ in ξ₁..ξ₂, truncFluxDeriv v (aₙ n) (2 * π - aₙ n) ξ)
      atTop (𝓝 (∫ ξ in ξ₁..ξ₂, sliceEnergy v ξ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => 2 * M + 2 * π * M ^ 2) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      have hmono : Set.uIoc ξ₁ ξ₂ ⊆ Iio (Real.log s) := by
        rw [Set.uIoc_of_le h12]; exact fun ξ hξ => lt_of_le_of_lt hξ.2 hξ₂log
      exact ((continuousOn_truncFluxDeriv hs0 hs1 (haₙpos n) (haₙle n) (haₙlt n) hvh).mono
        hmono).aestronglyMeasurable measurableSet_uIoc
    · refine Eventually.of_forall fun n => Eventually.of_forall fun ξ hξ => ?_
      rw [Set.uIoc_of_le h12] at hξ
      have hξlt : ξ < Real.log s := lt_of_le_of_lt hξ.2 hξ₂log
      have hξIcc : ξ ∈ Icc ξ₁ ξ₂ := ⟨le_of_lt hξ.1, hξ.2⟩
      exact truncFluxDeriv_norm_le hs0 hs1 hξlt (haₙpos n) (haₙle n) (haₙlt n)
        hvrange hM hMnn hξIcc (hsaₙ n) (hsbₙ n)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun ξ hξ => ?_
      rw [Set.uIoc_of_le h12] at hξ
      have hξs' : Real.exp ξ < s := lt_of_le_of_lt (Real.exp_le_exp.mpr hξ.2) hξ₂s
      exact tendsto_truncFluxDeriv_sliceEnergy hs0 hs1 hξs' hvh hvc hv0 hv1
  have heq := tendsto_nhds_unique
    (by simpa only [hFTC] using hRHS) hLHS
  exact heq.symm

/-- The squared log-polar gradient integrand is `2π`-periodic in the angle. -/
theorem normSq_expGrad_periodic (v : ℂ → ℝ) (ξ : ℝ) :
    Function.Periodic
      (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (2 * π) := by
  intro θ
  have hexp : Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    rw [show ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
        = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  simp only [expGrad, hexp]

/-- The single-circle energy density in the collar chart: the slice energy over `(0, 2π)` equals
the angle integral of `|expGrad v|²` over `(−π, π)`. -/
theorem sliceEnergy_eq_neg_pi_pi (v : ℂ → ℝ) (ξ : ℝ) :
    sliceEnergy v ξ
      = ∫ θ in Ioo (-π) π, Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  have hπ := Real.pi_pos
  unfold sliceEnergy
  rw [integral_Ioo_eq_intervalIntegral (by linarith : (0 : ℝ) ≤ 2 * π),
    integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π)]
  have hkey := (normSq_expGrad_periodic v ξ).intervalIntegral_add_eq 0 (-π)
  have hend : -π + 2 * π = π := by ring
  rw [zero_add, hend] at hkey
  exact hkey

/-- **Continuity of the slice energy on the slit chart.** For the Grötzsch potential `v` with
values in `[0, 1]`, the single-circle energy density `sliceEnergy v` is continuous on
`(−∞, log s)`. -/
theorem continuousOn_sliceEnergy {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    ContinuousOn (sliceEnergy v) (Iio (Real.log s)) := by
  have hπ := Real.pi_pos
  unfold sliceEnergy
  intro ξ₀ hξ₀
  have hξ₀lt : ξ₀ < Real.log s := hξ₀
  obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab (show ξ₀ - 1 < ξ₀ by linarith) hξ₀lt
  -- slab bound on `expGrad` over `[ξ₀ − δ, ξ₀ + δ]`; hence a constant bound `M²` on `normSq`
  have hξ₂mem : ξ₀ + δ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := ⟨by linarith, le_refl _⟩
  have hξ₂lt : ξ₀ + δ < Real.log s := (hδsub hξ₂mem).2
  have hexpξ₂ : Real.exp (ξ₀ + δ) < s := (Real.lt_log_iff_exp_lt hs0).mp hξ₂lt
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ₀ - δ) (ξ₂ := ξ₀ + δ) hs0 hs1
    hexpξ₂ hvh hvc hv0 hv1
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ => M ^ 2)
  · filter_upwards [Iio_mem_nhds hξ₀lt] with ξ hξ
    have hξlt : ξ < Real.log s := hξ
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_normSq.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlt
    exact hsl.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with ξ hξ
    have hξ' : ξ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hξ
      exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
    filter_upwards [ae_sin_ne_zero_Ioo] with θ hsin
    have hb := hM ξ hξ' θ hsin
    rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb,
      le_trans (norm_nonneg _) (hM ξ hξ' (π / 2)
        (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))]
  · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    have hmem : Complex.exp ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξ₀lt hθ.1 hθ.2
    exact Complex.continuous_normSq.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hmem)

/-- Integrability of the squared log-polar gradient slice over `(0, 2π)` at a slit-chart
log-radius `ξ < log s`, from the a.e. constant bound off the axis. -/
theorem integrableOn_normSq_expGrad_slit {s ξ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξs : Real.exp ξ < s) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1) :
    IntegrableOn (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Ioo 0 (2 * π)) := by
  have hπ := Real.pi_pos
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξs hvh hvc hv0 hv1
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (volume.restrict (Ioo 0 (2 * π))) := by
    have hsl := continuousOn_slice_of_continuousOn_openSlitBox
      (Complex.continuous_normSq.comp_continuousOn
        (continuousOn_expGrad_slitBox hs0 hs1 hvh (le_refl (Real.log s)) (ξ₁ := ξ - 1)))
      (by linarith : ξ - 1 < ξ) hξlog
    exact hsl.aestronglyMeasurable measurableSet_Ioo
  refine ⟨hmeas, HasFiniteIntegral.restrict_of_bounded (C := M ^ 2) measure_Ioo_lt_top ?_⟩
  filter_upwards [ae_sin_ne_zero_Ioo] with θ hsin
  have hb := hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb,
    le_trans (norm_nonneg _) (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
      (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))]

/-- **Flux–energy identity on slit sub-annuli.** For the Grötzsch potential `v` and log-radii
`ξ₁ ≤ ξ₂` with `e^{ξ₂} < s`, the Dirichlet energy of `v` over the round sub-annulus
`{e^{ξ₁} < |z| < e^{ξ₂}}` (which lies below the slit tip, so `v` is not harmonic across it) equals
the slit-chart flux increment `ringFluxSlit v ξ₂ − ringFluxSlit v ξ₁`. -/
theorem dirichletEnergy_roundAnnulus_eq_ringFluxSlit_sub {s ξ₁ ξ₂ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hξ₂s : Real.exp ξ₂ < s) (h12 : ξ₁ ≤ ξ₂) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    dirichletEnergy v (RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
      = ENNReal.ofReal (ringFluxSlit v ξ₂ - ringFluxSlit v ξ₁) := by
  have hπ := Real.pi_pos
  have hξ₂log : ξ₂ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξ₂s
  rw [dirichletEnergy_roundAnnulus_eq_lintegral v ξ₁ ξ₂]
  -- inner bridge: the `(0, 2π)` slice energy `ofReal` matches the `(−π, π)` lintegral
  have hinner : ∀ ξ ∈ Ioo ξ₁ ξ₂,
      (∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
      = ENNReal.ofReal (sliceEnergy v ξ) := by
    intro ξ hξ
    have hξ₂s' : Real.exp ξ < s := lt_of_lt_of_le (Real.exp_lt_exp.mpr hξ.2) hξ₂s.le
    -- the `(−π, π)` and `(0, 2π)` charts give the same real integral
    obtain ⟨M, hM⟩ := exists_bound_expGrad_slitBox (ξ₁ := ξ) (ξ₂ := ξ) hs0 hs1 hξ₂s'
      hvh hvc hv0 hv1
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _)
      (hM ξ (left_mem_Icc.mpr (le_refl ξ)) (π / 2)
        (sin_ne_zero_of_mem_Ioo_pi (by linarith) (by linarith)))
    have hmeasfun : Measurable
        (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
      have h1 : Measurable fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
        (Complex.continuous_exp.comp (by fun_prop)).measurable
      have h2 : Measurable fun θ : ℝ => expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
        ((measurable_gradC v).comp h1).mul h1
      exact Complex.continuous_normSq.measurable.comp h2
    have hintNeg : IntegrableOn
        (fun θ : ℝ => Complex.normSq (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (Ioo (-π) π) := by
      refine Measure.integrableOn_of_bounded (M := M ^ 2) measure_Ioo_lt_top.ne
        hmeasfun.aestronglyMeasurable ?_
      have hae : ∀ᵐ (θ : ℝ) ∂((volume : Measure ℝ).restrict (Ioo (-π) π)), Real.sin θ ≠ 0 := by
        have hnull : volume ({(0:ℝ), π} : Set ℝ) = 0 :=
          ((Set.finite_singleton π).insert 0).measure_zero _
        refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with θ hθn hθ
        rcases lt_trichotomy θ 0 with hneg | hz | hpos
        · rcases lt_trichotomy θ (-π) with _ | _ | h3
          · linarith [hθ.1]
          · linarith [hθ.1]
          · have := Real.sin_pos_of_pos_of_lt_pi (x := θ + π) (by linarith) (by linarith [hθ.2])
            rw [Real.sin_add_pi] at this; linarith
        · exact absurd (show θ ∈ ({(0:ℝ), π} : Set ℝ) from Set.mem_insert_iff.mpr (Or.inl hz))
            hθn
        · rcases lt_trichotomy θ π with h3 | h3 | h3
          · exact (Real.sin_pos_of_pos_of_lt_pi hpos h3).ne'
          · exact absurd (show θ ∈ ({(0:ℝ), π} : Set ℝ) from
              Set.mem_insert_iff.mpr (Or.inr h3)) hθn
          · linarith [hθ.2]
      filter_upwards [hae] with θ hsin
      have hb := hM ξ (left_mem_Icc.mpr (le_refl ξ)) θ hsin
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)), hb, hMnn]
    rw [← ofReal_integral_eq_lintegral_ofReal hintNeg
      (ae_of_all _ fun θ => Complex.normSq_nonneg _), sliceEnergy_eq_neg_pi_pi]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner]
  -- outer bridge and the fundamental theorem of calculus for the slit flux
  have hsub : Icc ξ₁ ξ₂ ⊆ Iio (Real.log s) := fun x hx => lt_of_le_of_lt hx.2 hξ₂log
  have hScont : ContinuousOn (sliceEnergy v) (Icc ξ₁ ξ₂) :=
    (continuousOn_sliceEnergy hs0 hs1 hvh hvc hv0 hv1).mono hsub
  have hSint : IntegrableOn (sliceEnergy v) (Ioo ξ₁ ξ₂) :=
    (hScont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hSnn : ∀ ξ : ℝ, 0 ≤ sliceEnergy v ξ := fun ξ =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ fun ξ => hSnn ξ)]
  congr 1
  rw [integral_Ioo_eq_intervalIntegral h12,
    ← ringFluxSlit_sub_eq_integral hs0 hs1 hξ₂s h12 hvh hvc hv0 hv1 hvrange]

/-- **Monotonicity of the slit-chart flux.** For the Grötzsch potential `v` with values in
`[0, 1]`, the slit-chart flux is nondecreasing on `(−∞, log s)`: its increments are Dirichlet
energies, hence nonnegative. -/
theorem ringFluxSlit_monotoneOn {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    MonotoneOn (ringFluxSlit v) (Iio (Real.log s)) := by
  intro x hx y hy hxy
  have hys : Real.exp y < s := (Real.lt_log_iff_exp_lt hs0).mp hy
  have hFTC := ringFluxSlit_sub_eq_integral hs0 hs1 hys hxy hvh hvc hv0 hv1 hvrange
  have hnn : (0 : ℝ) ≤ ∫ ξ in x..y, sliceEnergy v ξ :=
    intervalIntegral.integral_nonneg hxy fun ξ _ =>
      setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  linarith [hFTC, hnn]

end RiemannDynamics
