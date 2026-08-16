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
# Flux–energy for ring potentials: the log-polar gradient and the ring flux

This is the first of three files on flux–energy identities for potentials harmonic on a collar
annulus `RoundAnnulus 0 r₀ 1`.  It installs the log-polar chart `z = e^{ξ+iθ}`: the holomorphic
gradient `expGrad`, the ring flux `ringFlux`, the chain rules and strip regularity these satisfy,
a toolbox for differentiating and taking limits of parametric angle integrals, and the resulting
flux–energy identity on collar sub-annuli together with its exhaustion up to the unit circle.
The two later files `FluxEnergy.BankRegularity` and `FluxEnergy.SlitFlux` build on this one and
reuse `expGrad`, the log-polar chain rules and the small bridging lemmas
`differentiableAt_of_harmonicOnNhd` and `integral_Ioo_eq_intervalIntegral` throughout.

## Main definitions

* `RiemannDynamics.expGrad` — the log-polar holomorphic gradient `expGrad u w = gradC u (e^w)·e^w`
  of a real function `u`, where `gradC u = u_x − i·u_y`.  At points where `u` is real-differentiable
  its real part is the radial derivative `∂_ξ (u ∘ exp)` and minus its imaginary part is the
  angular derivative `∂_θ (u ∘ exp)`.
* `RiemannDynamics.ringFlux` — the ring flux at log-radius `ξ`: the unnormalised integral over the
  angle interval `(−π, π)` of `u` against its scale-invariant radial derivative `r ∂_r u`, that is
  of `u(e^{ξ+iθ}) · Re (expGrad u (ξ+iθ))` (`ringFlux_eq`).

## Main results

* `RiemannDynamics.hasDerivAt_integral_logStrip` — differentiation under the integral sign on a
  vertical strip: if `G` and `G'` are both continuous on `{a < Re w < b}` and `G'(x+iθ)` is the
  derivative of `y ↦ G(y+iθ)` at every `x ∈ (a, b)` and every real `θ`, then the angle integral
  `ξ ↦ ∫_{(−π,π)} G(ξ+iθ) dθ` has derivative `∫_{(−π,π)} G'(ξ₀+iθ) dθ` at each `ξ₀ ∈ (a, b)`.
* `RiemannDynamics.logCircleMean_affineOn` — for `0 < r₀ < 1` and `u` harmonic on a neighbourhood of
  every point of the collar `{r₀ < |z| < 1}`, one single affine function `a + b·ξ` computes the
  circle mean `logCircleMean 0 u ξ = ∫_{(−π,π)} u(e^{ξ+iθ}) dθ` at every `ξ ∈ (log r₀, 0)`.
* `RiemannDynamics.logCircleMean_tendsto_two_pi` — if `0 < r₀ < 1`, `u` is continuous on the closed
  collar `{r₀ ≤ |z| ≤ 1}` and `u = 1` on the unit circle `grotzschOuter`, then the circle mean tends
  to `2π` as `ξ → 0⁻`.  No harmonicity is needed: the closed collar is compact, so `u` is uniformly
  continuous there and `u(e^{ξ+iθ}) → 1` uniformly in the angle.
* `RiemannDynamics.dirichletEnergy_roundAnnulus_eq_lintegral` — for an arbitrary `u : ℂ → ℝ` and
  arbitrary reals `ξ₁ ξ₂` (no harmonicity, no ordering assumed), the Dirichlet energy over the
  round annulus `{e^{ξ₁} < |z| < e^{ξ₂}}` is the iterated log-polar integral of `|expGrad u|²`
  over `(ξ₁, ξ₂) × (−π, π)`; the polar Jacobian is absorbed by the factor `e^w` of `expGrad`.
* `RiemannDynamics.dirichletEnergy_roundAnnulus_eq_ringFlux_sub` — for `0 < r₀`, `u` harmonic on a
  neighbourhood of every point of `{r₀ < |z| < 1}`, and `log r₀ < ξ₁ ≤ ξ₂ < 0`, the Dirichlet energy
  over the sub-annulus `{e^{ξ₁} < |z| < e^{ξ₂}}` is the flux increment
  `ENNReal.ofReal (ringFlux u ξ₂ − ringFlux u ξ₁)`.
* `RiemannDynamics.ringFlux_monotoneOn` — for `0 < r₀` and `u` harmonic on a neighbourhood of every
  point of `{r₀ < |z| < 1}`, the ring flux is nondecreasing on the open interval `(log r₀, 0)`,
  its derivative there being the nonnegative angle integral of `|expGrad u|²`.
* `RiemannDynamics.dirichletEnergy_outerCollar_eq_iSup_ringFlux` — for `0 < r₀`, `u` harmonic on a
  neighbourhood of every point of `{r₀ < |z| < 1}`, and `log r₀ < ξ₁ < 0`, the energy over the outer
  collar `{e^{ξ₁} < |z| < 1}` is the supremum over `n : ℕ` of the flux increments
  `ENNReal.ofReal (ringFlux u (ξ₁/(n+1)) − ringFlux u ξ₁)`, taken along the exhaustion by
  sub-annuli whose outer radii `e^{ξ₁/(n+1)}` increase to `1`.
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
  simp only [RoundAnnulus, Set.mem_ofPred_eq, hdist]
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
  simpa [Function.comp] using! hcomp

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
  simpa [Function.comp] using! hcomp

/-- **Radial derivative of the holomorphic gradient.** If `expGrad u` is complex-differentiable
at `ξ + θ·I`, its restriction to the radial line has derivative `deriv (expGrad u) (ξ+θi)`. -/
theorem hasDerivAt_expGrad_radial {u : ℂ → ℝ} {ξ θ : ℝ}
    (hd : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :
    HasDerivAt (fun x : ℝ => expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I))
      (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ξ := by
  have h := hd.hasDerivAt.comp ξ (hasDerivAt_logPolar_radial ξ θ)
  simpa [Function.comp] using! h

/-- **Angular derivative of the holomorphic gradient.** If `expGrad u` is complex-differentiable
at `ξ + θ·I`, its restriction to the angular line has derivative `I · deriv (expGrad u)`. -/
theorem hasDerivAt_expGrad_angular {u : ℂ → ℝ} {ξ θ : ℝ}
    (hd : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I))
      (Complex.I * deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)) θ := by
  have h := hd.hasDerivAt.comp θ (hasDerivAt_logPolar_angular ξ θ)
  simpa [Function.comp, mul_comm] using! h

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
  simp only [Set.mem_ofPred_eq, re_logPolar]
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
    simp only [Set.mem_ofPred_eq, re_logPolar]
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
    simp only [Set.mem_ofPred_eq, re_logPolar]
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
    simpa [Function.comp, Complex.mul_im] using! hcomp
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
        simpa [Function.comp] using! hcomp)
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
    simpa using! hsub
  have hgeq := eqOn_Ioo_of_hasDerivAt_zero hgderiv hξ hξcmem
  try simp only at hgeq
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
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, Set.mem_compl_iff,
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
  rw [← hnorm, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
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
          simp only [RoundAnnulus, Set.mem_ofPred_eq, hnorm]
          exact ⟨hmem.1, hmem.2⟩
        rw [Set.indicator_of_mem hin, Set.indicator_of_mem (Set.mem_prod.mpr ⟨hmem, hp.2⟩),
          smul_eq_mul]
      · have hnotin : Complex.polarCoord.symm p
            ∉ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂) := by
          simp only [RoundAnnulus, Set.mem_ofPred_eq, hnorm]
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
    simpa [Function.comp, Complex.mul_im] using! hcomp
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
      simpa [Function.comp] using! hcomp
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
        exact zero_le
    · rw [Set.indicator_of_notMem hx]
      refine (ENNReal.iSup_eq_zero.mpr fun n => ?_).symm
      exact Set.indicator_of_notMem (fun hc => hx (Set.mem_iUnion.mpr ⟨n, hc⟩)) g
  rw [hpt, lintegral_iSup (fun n => hg.indicator (hmeas n))
    (fun n m hnm x => Set.indicator_le_indicator_of_subset (hmono hnm) (fun _ => zero_le) x)]
  exact iSup_congr fun n => lintegral_indicator (hmeas n) g

/-- The outer collar `{e^{ξ₁} < |z| < 1}` is the monotone union of the sub-annuli with outer
radii `e^{ξ₁/(n+1)} ↑ 1`. -/
theorem roundAnnulus_outer_eq_iUnion {ξ₁ : ℝ} (hξ₁0 : ξ₁ < 0) :
    RoundAnnulus 0 (Real.exp ξ₁) 1
      = ⋃ n : ℕ, RoundAnnulus 0 (Real.exp ξ₁) (Real.exp (ξ₁ / (n + 1))) := by
  ext z
  simp only [RoundAnnulus, Set.mem_ofPred_eq, Set.mem_iUnion]
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

end RiemannDynamics
