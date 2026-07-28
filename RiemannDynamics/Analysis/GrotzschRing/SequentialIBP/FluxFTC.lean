/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.SequentialIBP.Basic

/-!
# Radial flux FTC, the collar flux–energy identity, and the level-set truncated flux

This file turns the per-arc bricks of `RiemannDynamics.Analysis.GrotzschRing.SequentialIBP.Basic`
into radial statements about the rough flux `RiemannDynamics.roughFlux`.  On a fixed angular window
`[a, b]` whose closed log-polar box maps into an open set `U` under `exp`, the truncated flux
`RiemannDynamics.truncFlux u a b` is differentiable in the log-radius, with derivative the angular
boundary term plus the window integral of `|expGrad u|²`, and its increment is the integral of that
derivative.  Taking the window to be the whole circle makes the `±π` boundary terms cancel by
`2π`-periodicity, which yields an exact flux–energy identity on a full-circle collar and, at the end
of the file, the slope bound `b ≤ D(u; U)` for an open set containing every circle of radius `< 1`.
The last section introduces the superlevel set `{u > δ}` and its `δ`-rough flux together with the
`δ → 0` recovery of the rough flux; these are the objects that
`RiemannDynamics.Analysis.GrotzschRing.SequentialIBP.TruncatedFlux` and `…LevelSetNullity` use when
the keystone geometry blocks full circles.

## Main definitions

* `RiemannDynamics.truncFluxDerivU` — the derivative value of the fixed-window flux for a general
  open set: the angular boundary term `u · Im (expGrad u)` at `b` minus its value at `a`, plus the
  integral of `|expGrad u|²` over the open window `(a, b)`.
* `RiemannDynamics.superLevelU` — the superlevel set `{z ∈ U | δ < u z}`.  For `u` harmonic on the
  open `U` it is open, and its `δ`-rough flux `RiemannDynamics.roughFluxδ` — the rough flux with the
  slice indicator refined to it — is the rough flux of `u` over that superlevel set.

## Main results

* `RiemannDynamics.hasDerivAt_truncFlux_of_mapsTo` — for `u` harmonic on an open `U`, `a ≤ b`, and a
  *closed* log-polar box `[ξ₁, ξ₂] × [a, b]` mapping into `U` under `exp`, at every interior
  log-radius `ξ ∈ (ξ₁, ξ₂)` the fixed-window flux `truncFlux u a b` has derivative
  `truncFluxDerivU u a b ξ`.
* `RiemannDynamics.truncFlux_sub_eq_integral_of_mapsTo` — under the same hypotheses (`U` open, `u`
  harmonic on `U`, `a ≤ b`, closed box mapping into `U`), for `ξ₁ < ζ₁ ≤ ζ₂ < ξ₂` the increment
  `truncFlux u a b ζ₂ - truncFlux u a b ζ₁` is the interval integral of `truncFluxDerivU u a b`
  from `ζ₁` to `ζ₂`.
* `RiemannDynamics.roughFlux_sub_eq_dirichletEnergy_roundAnnulus` — when the angular window is all
  of `[-π, π]`, so that every circle of log-radius in `[ξ₁, ξ₂]` lies in the open set `U` on which
  `u` is harmonic, the boundary terms cancel and the rough-flux increment over `ξ₁ < ζ₁ ≤ ζ₂ < ξ₂`
  is *exactly* the Dirichlet energy of the round annulus `{e^{ζ₁} < |z| < e^{ζ₂}}`.
* `RiemannDynamics.setLIntegral_tail_ofReal_sliceEnergyU_le` — for any `u` and any *open* `U`, with
  no harmonicity and no finiteness assumed, the lower integral of
  `ENNReal.ofReal (sliceEnergyU u U ξ)` over `ξ ∈ (-∞, ξ₀]` is at most `dirichletEnergy u U`; the
  log-polar change of variables identifies it with the energy over `U ∩ {0 < |z| < e^{ξ₀}}`, which
  is monotone below `D(u; U)`.
* `RiemannDynamics.closure_superLevel_window_subset` — if `u` is continuous on `closure U` and
  vanishes at every point of `frontier U` of norm `< 1`, then for `δ > 0` and `ζ₂ < 0` the closure
  of `superLevelU U u δ ∩ {e^{ζ₁} < |z| < e^{ζ₂}}` is compact *and* contained in `U`.  Both `0 < δ`
  and the frontier-vanishing hypothesis are load-bearing: together they force `u ≥ δ > 0` on the
  closure, so no point of it can lie on `frontier U`.  Openness of `U` is not assumed.
* `RiemannDynamics.tendsto_roughFluxδ_atZero` — for `u` harmonic and *strictly positive* on the open
  `U`, at a log-radius `ξ` where `|u|` is bounded by some `M ≥ 0` on the angular slice and
  `θ ↦ Re (expGrad u)` is integrable over that slice, `roughFluxδ u U (δ n) ξ → roughFlux u U ξ`
  along any real sequence `δ n → 0` (positivity of `δ n` is not needed).
* `RiemannDynamics.roughFlux_sub_le_of_roughFluxδ_sub_le` — for `u` harmonic and strictly positive
  on the open `U`, with the bound `M ≥ 0` on `|u|` and the integrability of `Re (expGrad u)` imposed
  on the angular slices at *both* `ζ₁` and `ζ₂`: if
  `roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ D` holds for every `δ > 0`, then the rough-flux
  increment `roughFlux u U ζ₂ - roughFlux u U ζ₁` satisfies the same bound.
* `RiemannDynamics.slope_le_energy` — for `u` harmonic on an open `U` containing every circle
  `{|z| = e^ξ}` with `ξ < 0` and with `dirichletEnergy u U ≠ ⊤`, if `roughFlux u U ξ → b` as `ξ → 0`
  from the left and `roughFlux u U ξ → 0` as `ξ → -∞`, then `b ≤ (dirichletEnergy u U).toReal`.
-/

namespace RiemannDynamics

open MeasureTheory intervalIntegral Filter Set
open scoped Real ENNReal Topology
open Complex

/-! ### Fixed-window flux FTC for a general open set

For a general open `U` and a window `[a, b]` whose log-polar strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}`
maps into `U` under `exp`, the truncated flux `truncFlux u a b` obeys the flux–energy exchange
`d/dξ (truncFlux u a b) = boundary + ∫ |expGrad u|²` exactly (the fixed-domain heart of the
exchange), mirroring `RiemannDynamics.hasDerivAt_truncFlux` with the Grötzsch ring replaced by `U`.
-/

/-- Every point of the strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}` has its exponential in `U`, provided
the whole closed box of log-polar parameters maps into `U`. -/
theorem stripBox_exp_mem_of_mapsTo {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) {w : ℂ}
    (hw : w ∈ stripBox ξ₁ ξ₂ a b) :
    Complex.exp w ∈ U := by
  obtain ⟨hre1, hre2, him1, him2⟩ := hw
  have hwrepr : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hwrepr]
  exact hmaps w.re ⟨hre1.le, hre2.le⟩ w.im ⟨him1, him2⟩

/-- The pullback `w ↦ u(e^w)` is continuous on a strip box mapping into `U`. -/
theorem continuousOn_uexp_stripBox_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (fun w => u (Complex.exp w)) (stripBox ξ₁ ξ₂ a b) := by
  intro w hw
  have hmem := stripBox_exp_mem_of_mapsTo hmaps hw
  have hc : ContinuousAt u (Complex.exp w) := (hu _ hmem).1.continuousAt
  exact (hc.comp Complex.continuous_exp.continuousAt).continuousWithinAt

/-- `expGrad u` is continuous on a strip box mapping into the open set `U`. -/
theorem continuousOn_expGrad_stripBox_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (expGrad u) (stripBox ξ₁ ξ₂ a b) := fun _w hw =>
  (expGrad_differentiableAt_open hU hu
    (stripBox_exp_mem_of_mapsTo hmaps hw)).continuousAt.continuousWithinAt

/-- The derivative of `expGrad u` is continuous on a strip box whose *interior* maps into the open
set `U`: on the open log-strip `expGrad u` is holomorphic hence analytic, so its derivative is
continuous there.  The interior-mapping hypothesis is packaged as membership of an open strip box in
the preimage. -/
theorem continuousOn_deriv_expGrad_stripBox_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (deriv (expGrad u)) (stripBox ξ₁ ξ₂ a b) := by
  -- `expGrad u` is holomorphic on the open preimage of `U`, so its derivative is continuous there
  set O : Set ℂ := Complex.exp ⁻¹' U with hO
  have hOopen : IsOpen O := hU.preimage Complex.continuous_exp
  have hdiff : DifferentiableOn ℂ (expGrad u) O := fun w hw =>
    (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
  have hanalytic := hdiff.analyticOnNhd hOopen
  have hderivCont : ContinuousOn (deriv (expGrad u)) O :=
    (hanalytic.deriv_of_isOpen hOopen).continuousOn
  refine hderivCont.mono (fun w hw => ?_)
  exact stripBox_exp_mem_of_mapsTo hmaps hw

/-- **Angular integration by parts with boundary terms on a window mapping into `U`.** For `u`
harmonic on the open set `U` and a closed window `[a, b]` whose slice at log-radius `ξ` maps into
`U`, the angle integral of `u · Re (deriv (expGrad u))` equals the boundary term
`[u · Im (expGrad u)]_a^b` plus the integral of `(Im (expGrad u))²`.  Unlike the endpoint-vanishing
per-arc identity, the boundary term is kept explicit — this is the form consumed by the fixed-window
flux FTC. -/
theorem integral_uexp_re_deriv_expGrad_window_Icc {u : ℂ → ℝ} {U : Set ℂ} {ξ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ θ ∈ Icc a b, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ∫ θ in a..b, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  -- differentiability of `u` and holomorphy of `expGrad u` at each window point
  have hdiffR : ∀ θ ∈ Icc a b,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ hθ =>
    differentiableAt_of_harmonicOnNhd hu (hmaps θ hθ)
  have hdiffC : ∀ θ ∈ Icc a b,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ hθ =>
    expGrad_differentiableAt_open hU hu (hmaps θ hθ)
  -- continuity of the three slice factors on the window (from differentiability)
  have hcont_f : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun θ hθ => ((hasDerivAt_uexp_angular (hdiffR θ hθ)).continuousAt).continuousWithinAt
  have hcont_g : ContinuousOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine fun θ hθ => ?_
    have hD := hasDerivAt_expGrad_angular (hdiffC θ hθ)
    exact ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD).continuousAt).continuousWithinAt
  have hcont_g' : ContinuousOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (uIcc a b) := by
    -- `deriv (expGrad u)` is continuous on the open preimage of `U`, restricted to the slice
    set O : Set ℂ := Complex.exp ⁻¹' U with hO
    have hOopen : IsOpen O := hU.preimage Complex.continuous_exp
    have hdiff : DifferentiableOn ℂ (expGrad u) O := fun w hw =>
      (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
    have hderivCont : ContinuousOn (deriv (expGrad u)) O :=
      ((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn
    rw [uIcc_of_le hab]
    refine fun θ hθ => ?_
    have hmem : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ O := hmaps θ hθ
    have hcont : ContinuousAt (fun w : ℂ => (deriv (expGrad u) w).re)
        ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      (Complex.continuous_re.comp_continuousOn hderivCont).continuousAt (hOopen.mem_nhds hmem)
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    exact (ContinuousAt.comp (g := fun w : ℂ => (deriv (expGrad u) w).re)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hcont hinner).continuousWithinAt
  -- pointwise angular derivatives on the open window
  have hf' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
        (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact hasDerivAt_uexp_angular (hdiffR θ (Ioo_subset_Icc_self hθ))
  have hg' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ (Ioo_subset_Icc_self hθ))
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [Function.comp, Complex.mul_im] using hcomp
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f hcont_g hf' hg' hcont_g.neg.intervalIntegrable hcont_g'.intervalIntegrable
  have halg : ∫ θ in a..b, (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im
      = - ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [hIBP, halg]; ring

/-- **Fixed-window flux FTC derivative for a general open set.** For `u` harmonic on the open set
`U` and a window `[a, b]` whose *closed* strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}` maps into `U` under
`exp`, the truncated flux `truncFlux u a b` has, at every interior log-radius `ξ ∈ (ξ₁, ξ₂)`,
derivative the angular boundary term plus the window integral of `|expGrad u|²`.  Differentiation
under the integral sign gives `(Re expGrad)² + u · Re (deriv expGrad)`, and the angular integration
by parts converts the second term into the boundary term plus `(Im expGrad)²`; adding
`(Re expGrad)² + (Im expGrad)² = |expGrad|²` gives the window slice energy.  This mirrors
`RiemannDynamics.hasDerivAt_truncFlux` with the Grötzsch ring replaced by `U`. -/
theorem hasDerivAt_truncFlux_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hξ1 : ξ₁ < ξ) (hξ2 : ξ < ξ₂) :
    HasDerivAt (truncFlux u a b)
      (u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) ξ := by
  -- continuity of the integrand `G` and its radial derivative `G'` on the strip box
  have hUexp := continuousOn_uexp_stripBox_of_mapsTo hu hmaps
  have hEG := continuousOn_expGrad_stripBox_of_mapsTo hU hu hmaps
  have hDEG := continuousOn_deriv_expGrad_stripBox_of_mapsTo hU hu hmaps
  have hGcont : ContinuousOn (fun w => u (Complex.exp w) * (expGrad u w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    hUexp.mul (Complex.continuous_re.comp_continuousOn hEG)
  have hG'cont : ContinuousOn
      (fun w => (expGrad u w).re ^ 2 + u (Complex.exp w) * (deriv (expGrad u) w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    ((Complex.continuous_re.comp_continuousOn hEG).pow 2).add
      (hUexp.mul (Complex.continuous_re.comp_continuousOn hDEG))
  -- radial product rule at each interior strip-box point
  have hd : ∀ x θ : ℝ, ξ₁ < x → x < ξ₂ → a < θ → θ < b →
      HasDerivAt (fun y : ℝ => u (Complex.exp ((y : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
            * (deriv (expGrad u) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
    intro x θ hx1 hx2 hθ1 hθ2
    have hmem : Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U :=
      hmaps x ⟨hx1.le, hx2.le⟩ θ ⟨hθ1.le, hθ2.le⟩
    have hu' := hasDerivAt_uexp_radial (differentiableAt_of_harmonicOnNhd hu hmem)
    have hD := hasDerivAt_expGrad_radial (expGrad_differentiableAt_open hU hu hmem)
    have hDre : HasDerivAt (fun y : ℝ => (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((deriv (expGrad u) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
      have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hD
      simpa [Function.comp] using hcomp
    exact (hu'.mul hDre).congr_deriv (by ring)
  have hDUI := hasDerivAt_integral_stripBox hab hGcont hG'cont hd hξ1 hξ2
  -- integrability of the three interior integrands on `(a, b)` via real-valued slice continuity
  have hsliceEGre : ContinuousOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox
      (Complex.continuous_re.comp_continuousOn hEG) hξ1 hξ2
  have hsliceEGim : ContinuousOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox
      (Complex.continuous_im.comp_continuousOn hEG) hξ1 hξ2
  have hsliceU : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox hUexp hξ1 hξ2
  have hsliceDEGre : ContinuousOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox
      (Complex.continuous_re.comp_continuousOn hDEG) hξ1 hξ2
  have hint1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2) (Ioo a b) :=
    ((hsliceEGre.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b) :=
    ((hsliceU.mul hsliceDEGre).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint3 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) (Ioo a b) :=
    ((hsliceEGim.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  -- convert the DUI derivative value via the window integration by parts
  have hval : (∫ θ in Ioo a b,
      ((expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    rw [integral_add hint1 hint2]
    have hIBP := integral_uexp_re_deriv_expGrad_window_Icc hU hu hab
      (fun θ hθ => hmaps ξ ⟨hξ1.le, hξ2.le⟩ θ hθ)
    have hIBP' : (∫ θ in Ioo a b, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        = u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
          - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
              * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
          + ∫ θ in Ioo a b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
      rw [integral_Ioo_eq_intervalIntegral hab, hIBP, integral_Ioo_eq_intervalIntegral hab]
    rw [hIBP']
    have hnormeq : (∫ θ in Ioo a b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2)
          + ∫ θ in Ioo a b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        = ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [← integral_add hint1 hint3]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [Complex.normSq_apply]; ring
    linarith [hnormeq]
  rw [hval] at hDUI
  exact hDUI

/-- The derivative value of the fixed-window flux for a general open set: the angular boundary term
of the integration by parts plus the window integral of `|expGrad u|²`. -/
noncomputable def truncFluxDerivU (u : ℂ → ℝ) (a b ξ : ℝ) : ℝ :=
  u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
      * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
    - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
    + ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- **Continuity of the fixed-window flux derivative value.** Under the strip-box mapping
hypothesis, the derivative value `truncFluxDerivU u a b` is continuous on the open log-radius
interval `(ξ₁, ξ₂)`: the two boundary factors are continuous in `ξ` (fixed angle in `U`), and the
window integral of `|expGrad u|²` is continuous by dominated convergence with a strip-box bound. -/
theorem continuousOn_truncFluxDerivU {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (truncFluxDerivU u a b) (Ioo ξ₁ ξ₂) := by
  have hUexp := continuousOn_uexp_stripBox_of_mapsTo hu hmaps
  have hEG := continuousOn_expGrad_stripBox_of_mapsTo hU hu hmaps
  -- the boundary factors `ξ ↦ u(e^{ξ+ci}) · Im (expGrad u (ξ+ci))` are continuous on `(ξ₁, ξ₂)`
  have hbdry : ∀ c : ℝ, c ∈ Icc a b →
      ContinuousOn (fun ξ : ℝ => u (Complex.exp ((ξ : ℂ) + (c : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (c : ℂ) * Complex.I)).im) (Ioo ξ₁ ξ₂) := by
    intro c hc ξ hξ
    have hmem : Complex.exp ((ξ : ℂ) + (c : ℂ) * Complex.I) ∈ U :=
      hmaps ξ (Ioo_subset_Icc_self hξ) c hc
    have hcu : ContinuousAt (fun ξ : ℝ => u (Complex.exp ((ξ : ℂ) + (c : ℂ) * Complex.I))) ξ :=
      (hasDerivAt_uexp_radial (differentiableAt_of_harmonicOnNhd hu hmem)).continuousAt
    have hcg : ContinuousAt (fun ξ : ℝ => (expGrad u ((ξ : ℂ) + (c : ℂ) * Complex.I)).im) ξ :=
      Complex.continuous_im.continuousAt.comp
        (hasDerivAt_expGrad_radial (expGrad_differentiableAt_open hU hu hmem)).continuousAt
    exact (hcu.mul hcg).continuousWithinAt
  -- the window integral of `|expGrad u|²` is continuous on `(ξ₁, ξ₂)`
  have hint : ContinuousOn (fun ξ : ℝ =>
      ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Ioo ξ₁ ξ₂) := by
    intro ξ₀ hξ₀
    obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab hξ₀.1 hξ₀.2
    have hcont : ContinuousOn (fun w => Complex.normSq (expGrad u w))
        (stripBox ξ₁ ξ₂ a b) :=
      Complex.continuous_normSq.comp_continuousOn hEG
    obtain ⟨C, hC⟩ := exists_bound_on_stripBox hcont hδsub
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated (bound := fun _ => C)
    · filter_upwards [Ioo_mem_nhds hξ₀.1 hξ₀.2] with ξ hξ
      exact ((continuousOn_slice_of_continuousOn_stripBox hcont hξ.1 hξ.2).mono
        Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with ξ hξ
      have hξ' : ξ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hξ
        exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      exact hC ξ hξ' θ (Ioo_subset_Icc_self hθ)
    · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      have hmem : Complex.exp ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I) ∈ U :=
        hmaps ξ₀ (Ioo_subset_Icc_self hξ₀) θ (Ioo_subset_Icc_self hθ)
      exact Complex.continuous_normSq.continuousAt.comp
        (hasDerivAt_expGrad_radial (expGrad_differentiableAt_open hU hu hmem)).continuousAt
  exact ((hbdry b (right_mem_Icc.mpr hab)).sub (hbdry a (left_mem_Icc.mpr hab))).add hint

/-- **Fundamental theorem of calculus for the fixed-window flux (general open set).** Under the
strip-box mapping hypothesis, the increment of the truncated flux over `[ξ₁', ξ₂'] ⊆ (ξ₁, ξ₂)` is
the integral of its derivative value. -/
theorem truncFlux_sub_eq_integral_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (h1 : ξ₁ < ζ₁) (h12 : ζ₁ ≤ ζ₂) (h2 : ζ₂ < ξ₂) :
    truncFlux u a b ζ₂ - truncFlux u a b ζ₁ = ∫ ξ in ζ₁..ζ₂, truncFluxDerivU u a b ξ := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_).symm
  · rw [uIcc_of_le h12] at hx
    exact hasDerivAt_truncFlux_of_mapsTo hU hu hab hmaps
      (lt_of_lt_of_le h1 hx.1) (lt_of_le_of_lt hx.2 h2)
  · refine ((continuousOn_truncFluxDerivU hU hu hab hmaps).mono ?_).intervalIntegrable
    rw [uIcc_of_le h12]
    exact fun x hx => ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h2⟩

/-! ### The full-circle collar flux–energy identity for a general open set

When the *whole* circle at log-radius `ξ` lies in `U`, the rough flux is the full-window flux
`truncFlux u (−π) π ξ` and its FTC derivative is the whole-circle slice energy — the `±π` boundary
terms cancel by `2π`-periodicity.  This yields an exact flux–energy identity on any full-circle
collar for a general open `U`, without needing the varying-domain radial FTC. -/

/-- On a full-circle collar (`exp(ξ+θi) ∈ U` for all `θ`), the rough flux equals the full-window
flux `truncFlux u (−π) π ξ`. -/
theorem roughFlux_eq_truncFlux_full {u : ℂ → ℝ} {U : Set ℂ} {ξ : ℝ} (hU : IsOpen U)
    (hfull : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    roughFlux u U ξ = truncFlux u (-π) π ξ := by
  rw [roughFlux_eq_setIntegral_slice hU, truncFlux]
  refine setIntegral_congr_set ?_
  have hsub : angularSlice U ξ = Ioo (-π) π := by
    ext θ; simp only [angularSlice, mem_setOf_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hfull θ⟩⟩
  rw [hsub]

/-- On a full-circle collar, the fixed-window derivative value `truncFluxDerivU u (−π) π ξ` equals
the whole-circle slice energy: the `±π` boundary terms cancel by `2π`-periodicity of the log-polar
pullback and of `expGrad u`. -/
theorem truncFluxDerivU_full_eq_sliceEnergy {u : ℂ → ℝ} (ξ : ℝ) :
    truncFluxDerivU u (-π) π ξ
      = ∫ θ in Ioo (-π) π, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  unfold truncFluxDerivU
  have hexp : Complex.exp ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    rw [show ((ξ : ℂ) + (π : ℂ) * Complex.I)
        = ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  have heg : expGrad u ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    simp only [expGrad, hexp]
  rw [show ((π : ℝ) : ℂ) = ((π : ℝ) : ℂ) from rfl, hexp, heg]
  push_cast
  ring

/-- **Full-circle collar flux–energy identity.** For `u` harmonic on the open set `U`, if the whole
strip box `{ξ₁ < Re < ξ₂, −π ≤ Im ≤ π}` maps into `U`, then the increment of the rough flux over
`[ζ₁, ζ₂] ⊆ (ξ₁, ξ₂)` equals the Dirichlet energy of the round sub-annulus
`{e^{ζ₁} < |z| < e^{ζ₂}}`.  The `±π` boundary terms cancel by periodicity, so the fixed-window FTC
integrates the whole-circle slice energy, which is the round-annulus energy by the log-polar change
of variables. -/
theorem roughFlux_sub_eq_dirichletEnergy_roundAnnulus {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (h1 : ξ₁ < ζ₁) (h12 : ζ₁ ≤ ζ₂) (h2 : ζ₂ < ξ₂) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁
      = (dirichletEnergy u (RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂))).toReal := by
  have hπ := Real.pi_pos
  -- each `ζ` in `[ζ₁, ζ₂]` is a full-circle collar radius
  have hfull : ∀ ζ : ℝ, ζ ∈ Icc ξ₁ ξ₂ → ∀ θ : ℝ,
      Complex.exp ((ζ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro ζ hζ θ
    -- reduce the angle to `(−π, π]` by periodicity; the strip box covers `[−π, π]`
    set α : ℝ := (Complex.exp ((θ : ℂ) * Complex.I)).arg with hα
    have hunit : Complex.exp ((α : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
      have hx := Complex.norm_mul_exp_arg_mul_I (Complex.exp ((θ : ℂ) * Complex.I))
      rw [Complex.norm_exp] at hx
      simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero,
        Complex.ofReal_one, one_mul] at hx
      rw [hα]; exact hx
    have hper : Complex.exp ((ζ : ℂ) + (θ : ℂ) * Complex.I)
        = Complex.exp ((ζ : ℂ) + (α : ℂ) * Complex.I) := by
      rw [Complex.exp_add, Complex.exp_add, hunit]
    rw [hper]
    exact hmaps ζ hζ α ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hζ₁mem : ζ₁ ∈ Icc ξ₁ ξ₂ := ⟨h1.le, le_trans h12 h2.le⟩
  have hζ₂mem : ζ₂ ∈ Icc ξ₁ ξ₂ := ⟨le_trans h1.le h12, h2.le⟩
  have hmaps' : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hmaps
  -- rough flux = full-window flux at both radii; the FTC integrates the derivative value
  rw [roughFlux_eq_truncFlux_full hU (hfull ζ₂ hζ₂mem),
    roughFlux_eq_truncFlux_full hU (hfull ζ₁ hζ₁mem),
    truncFlux_sub_eq_integral_of_mapsTo hU hu (by linarith : -π ≤ π) hmaps' h1 h12 h2]
  -- the derivative value is the whole-circle slice energy (boundary terms cancel)
  have hderiveq : (∫ ξ in ζ₁..ζ₂, truncFluxDerivU u (-π) π ξ)
      = ∫ ξ in ζ₁..ζ₂,
        ∫ θ in Ioo (-π) π, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr (fun ξ _ => truncFluxDerivU_full_eq_sliceEnergy (u := u) ξ)
  rw [hderiveq]
  -- the round-annulus energy is the log-polar box lintegral of `normSq (expGrad u)`
  rw [dirichletEnergy_roundAnnulus_eq_lintegral u ζ₁ ζ₂]
  -- inner bridge: the `ofReal` of the whole-circle slice energy is the inner slice lintegral
  have hSnn : ∀ ξ : ℝ, 0 ≤ ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun ξ =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  -- integrability of the whole-circle slice energy over `[ζ₁, ζ₂]` for the outer bridge
  have hScont : ContinuousOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc ζ₁ ζ₂) := by
    have hfulld : ContinuousOn (truncFluxDerivU u (-π) π) (Icc ζ₁ ζ₂) :=
      (continuousOn_truncFluxDerivU hU hu (by linarith : -π ≤ π) hmaps').mono
        (fun x hx => ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h2⟩)
    exact hfulld.congr (fun ξ _ => (truncFluxDerivU_full_eq_sliceEnergy (u := u) ξ).symm)
  have hSint : IntegrableOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo ζ₁ ζ₂) :=
    (hScont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hinner : ∀ ξ ∈ Ioo ζ₁ ζ₂,
      (∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
      = ENNReal.ofReal (∫ θ in Ioo (-π) π,
          Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
    intro ξ hξ
    have hmem : ξ ∈ Icc ξ₁ ξ₂ := ⟨le_trans hζ₁mem.1 hξ.1.le, le_trans hξ.2.le hζ₂mem.2⟩
    have hintNeg : IntegrableOn
        (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (Ioo (-π) π) :=
      (continuousOn_slice_of_continuousOn_stripBox
        (Complex.continuous_normSq.comp_continuousOn
          (continuousOn_expGrad_stripBox_of_mapsTo hU hu hmaps'))
        (lt_trans h1 hξ.1) (lt_trans hξ.2 h2)).integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hintNeg
      (ae_of_all _ fun θ => Complex.normSq_nonneg _)]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner,
    ← ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ fun ξ => hSnn ξ),
    integral_Ioo_eq_intervalIntegral h12]
  rw [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg h12 (fun ξ _ => hSnn ξ))]

/-- **Monotonicity of the Dirichlet energy in the domain.** The Dirichlet energy is monotone under
inclusion of the integration set: `E ⊆ F ⇒ D(u; E) ≤ D(u; F)`. -/
theorem dirichletEnergy_mono {u : ℂ → ℝ} {E F : Set ℂ} (hEF : E ⊆ F) :
    dirichletEnergy u E ≤ dirichletEnergy u F :=
  lintegral_mono_set hEF

/-- **The `ofReal` of a set integral is dominated by the set lower integral.** For a nonnegative `g`
on a measurable set `s`, `ofReal (∫_s g) ≤ ∫⁻_s ofReal (g)`: if `g` is integrable this is equality,
otherwise the Bochner integral is `0`. -/
theorem ofReal_setIntegral_le_setLIntegral_ofReal {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hgnn : ∀ t ∈ s, 0 ≤ g t) :
    ENNReal.ofReal (∫ t in s, g t) ≤ ∫⁻ t in s, ENNReal.ofReal (g t) := by
  by_cases hint : IntegrableOn g s
  · rw [ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' hs).mpr (ae_of_all _ hgnn))]
  · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le

/-- **Log-polar change of variables for the energy over an open set below a radius.** For any `u`
and log-radius `ξ₀`, the Dirichlet energy over `U ∩ {0 < |z| < e^{ξ₀}}` is the iterated log-polar
integral of `normSq (expGrad u)` restricted to the angular slice of `U`: the polar Jacobian combines
the squared gradient into `normSq (expGrad u)`, and the indicator of `U` becomes the slice
indicator. -/
theorem dirichletEnergy_inter_ball_eq_lintegral_slice (u : ℂ → ℝ) {U : Set ℂ} (hU : IsOpen U)
    (ξ₀ : ℝ) :
    dirichletEnergy u {z : ℂ | z ∈ U ∧ 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀}
      = ∫⁻ ξ in Iio ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
  classical
  set A : Set ℂ := {z : ℂ | z ∈ U ∧ 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀} with hA
  set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Complex.normSq (gradC u z)) with hG
  set R : Set (ℝ × ℝ) := Ioo (0 : ℝ) (Real.exp ξ₀) ×ˢ Ioo (-π) π with hR
  have hGmeas : Measurable G :=
    ENNReal.measurable_ofReal.comp (Complex.continuous_normSq.measurable.comp (measurable_gradC u))
  have hAMeas : MeasurableSet A := by
    have : A = U ∩ {z : ℂ | 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀} := by
      ext z; simp only [hA, mem_setOf_eq, mem_inter_iff]
    rw [this]
    refine hU.measurableSet.inter ?_
    exact (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const) |>.measurableSet
  have hRMeas : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  have hsymmMeas : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have heq : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [heq]; exact Continuous.measurable (by fun_prop)
  -- Step 1: polar change of variables, folding the indicator of `A` into the slice indicator
  have h2 : ∫⁻ z in A, G z
      = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
          * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := by
    have hcov := Complex.lintegral_comp_polarCoord_symm (fun z => A.indicator G z)
    rw [lintegral_indicator hAMeas] at hcov
    have hpt : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • A.indicator G (Complex.polarCoord.symm p)
          = R.indicator (fun q : ℝ × ℝ =>
              (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm q))
                * (ENNReal.ofReal q.1 * G (Complex.polarCoord.symm q))) p := by
      intro p hp
      rw [polarCoord_target] at hp
      have hnorm : dist (Complex.polarCoord.symm p) 0 = p.1 := by
        rw [dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      by_cases hmemA : Complex.polarCoord.symm p ∈ A
      · have hUin : Complex.polarCoord.symm p ∈ U := hmemA.1
        have hlt : dist (Complex.polarCoord.symm p) 0 < Real.exp ξ₀ := hmemA.2.2
        have hpR : p ∈ R := ⟨⟨hp.1, by rwa [hnorm] at hlt⟩, hp.2⟩
        rw [Set.indicator_of_mem hmemA, Set.indicator_of_mem hpR,
          Set.indicator_of_mem hUin, smul_eq_mul, one_mul]
      · rw [Set.indicator_of_notMem hmemA, smul_zero]
        by_cases hpR : p ∈ R
        · rw [Set.indicator_of_mem hpR]
          rw [Set.indicator_of_notMem (fun hUin => hmemA
            ⟨hUin, by rw [hnorm]; exact hp.1, by rw [hnorm]; exact hpR.1.2⟩), zero_mul]
        · rw [Set.indicator_of_notMem hpR]
    have hRsub : R ⊆ polarCoord.target := by
      rintro p ⟨hp1, hp2⟩
      rw [polarCoord_target]; exact ⟨hp1.1, hp2⟩
    calc ∫⁻ z in A, G z
        = ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • A.indicator G (Complex.polarCoord.symm p) := hcov.symm
      _ = ∫⁻ p in polarCoord.target,
            R.indicator (fun q : ℝ × ℝ =>
              (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm q))
                * (ENNReal.ofReal q.1 * G (Complex.polarCoord.symm q))) p :=
          setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt
      _ = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
            * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p))
            ∂(volume.restrict polarCoord.target) := lintegral_indicator hRMeas _
      _ = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
            * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := by
          rw [Measure.restrict_restrict hRMeas, Set.inter_eq_self_of_subset_left hRsub]
  -- Step 2: Tonelli on the rectangle
  have hUindeq : (fun p : ℝ × ℝ => U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
      = ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    by_cases hp : Complex.polarCoord.symm p ∈ U
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ _ from hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ _ from hp)]
  have hintegrand_meas : Measurable fun p : ℝ × ℝ =>
      (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
        * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := by
    refine Measurable.mul ?_ ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hGmeas.comp hsymmMeas))
    rw [hUindeq]
    exact measurable_const.indicator (hU.measurableSet.preimage hsymmMeas)
  have h3 : ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
        * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p))
      = ∫⁻ r in Ioo (0 : ℝ) (Real.exp ξ₀), ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (r, θ)))
            * (ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict R
        = ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) (Real.exp ξ₀))).prod
            ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
      rw [hR, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hprod]; exact lintegral_prod _ hintegrand_meas.aemeasurable
  -- Step 3: radial substitution `r = e^ξ`, restricting to `Iio ξ₀`
  have h4 : ∫⁻ r in Ioo (0 : ℝ) (Real.exp ξ₀), ∫⁻ θ in Ioo (-π) π,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (r, θ)))
          * (ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)))
      = ∫⁻ ξ in Iio ξ₀, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (Real.exp ξ, θ)))
            * (ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ))) := by
    have himg : Real.exp '' Iio ξ₀ = Ioo (0 : ℝ) (Real.exp ξ₀) := by
      ext r; simp only [mem_image, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨Real.exp_pos x, Real.exp_lt_exp.mpr hx⟩
      · intro hr; exact ⟨Real.log r, (Real.log_lt_iff_lt_exp hr.1).mpr hr.2,
          Real.exp_log hr.1⟩
    rw [← himg]
    exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn _
  -- Step 4: absorb the Jacobian and fold the `U`-indicator into the slice indicator
  have h5 : ∀ ξ : ℝ, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (Real.exp ξ, θ)))
          * (ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ)))
      = ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
    intro ξ
    rw [abs_of_pos (Real.exp_pos ξ), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [polarCoord_symm_exp]
    by_cases hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show θ ∈ angularSlice U ξ from
        ⟨hθ, hmem⟩), one_mul, hG, normSq_expGrad_eq u ξ θ,
        ENNReal.ofReal_mul (Real.exp_pos ξ).le, ENNReal.ofReal_mul (Real.exp_pos ξ).le]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem
        (show θ ∉ angularSlice U ξ from fun h => hmem h.2), zero_mul, mul_zero]
  -- assemble the calc
  calc dirichletEnergy u A
      = ∫⁻ z in A, G z :=
        lintegral_congr fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC u z
    _ = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
          * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := h2
    _ = ∫⁻ r in Ioo (0 : ℝ) (Real.exp ξ₀), ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (r, θ)))
            * (ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))) := h3
    _ = ∫⁻ ξ in Iio ξ₀, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (Real.exp ξ, θ)))
            * (ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ))) := h4
    _ = ∫⁻ ξ in Iio ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ :=
        lintegral_congr fun ξ => h5 ξ

/-- **The tail slice-energy lower integral is bounded by the total Dirichlet energy (`F2`).** For
`u` harmonic on the open set `U` with finite Dirichlet energy, the tail integral of the single-slice
energy `∫⁻_{Iic ξ₀} ofReal (sliceEnergyU u U ξ)` is at most `D(u; U)`: `ofReal` of the slice
integral is dominated by the slice lower integral, whose `ξ`-integral over `(-∞, ξ₀)` is — log-polar
change of variables — the energy over `U ∩ {|z| < e^{ξ₀}}`, monotone below `D(u; U)`. -/
theorem setLIntegral_tail_ofReal_sliceEnergyU_le {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (ξ₀ : ℝ) :
    (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ)) ≤ dirichletEnergy u U := by
  -- slice-wise: `ofReal` of the slice integral is dominated by the slice lower integral
  have hslice : ∀ ξ : ℝ, ENNReal.ofReal (sliceEnergyU u U ξ)
      ≤ ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
    intro ξ
    have hsub : angularSlice U ξ ⊆ Ioo (-π) π := angularSlice_subset U ξ
    have hsmeas : MeasurableSet (angularSlice U ξ) := (isOpen_angularSlice hU ξ).measurableSet
    calc ENNReal.ofReal (sliceEnergyU u U ξ)
        ≤ ∫⁻ θ in angularSlice U ξ,
            ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :=
          ofReal_setIntegral_le_setLIntegral_ofReal hsmeas
            (fun θ _ => Complex.normSq_nonneg _)
      _ = ∫⁻ θ in Ioo (-π) π,
            (angularSlice U ξ).indicator
              (fun θ' => ENNReal.ofReal
                (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
          rw [lintegral_indicator hsmeas,
            Measure.restrict_restrict hsmeas, Set.inter_eq_self_of_subset_left hsub]
  -- integrate the slice bound in `ξ`; `Iic` and `Iio` agree up to the null endpoint
  calc (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ))
      ≤ ∫⁻ ξ in Iic ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ :=
        lintegral_mono hslice
    _ = ∫⁻ ξ in Iio ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ :=
        (setLIntegral_congr Iio_ae_eq_Iic).symm
    _ = dirichletEnergy u {z : ℂ | z ∈ U ∧ 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀} :=
        (dirichletEnergy_inter_ball_eq_lintegral_slice u hU ξ₀).symm
    _ ≤ dirichletEnergy u U := dirichletEnergy_mono (fun z hz => hz.1)

/-- **The single-slice energy is measurable in the log-radius.** For `u` harmonic on the open set
`U`, the map `ξ ↦ sliceEnergyU u U ξ` is measurable: it is the `θ`-Bochner integral of the jointly
measurable integrand `(ξ, θ) ↦ (angularSlice U ξ).indicator (normSq (expGrad u)) θ`, whose
underlying set `{(ξ, θ) | θ ∈ (-π, π) ∧ e^{ξ+iθ} ∈ U}` is open. -/
theorem measurable_sliceEnergyU {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) :
    Measurable (sliceEnergyU u U) := by
  -- the joint slice set in `(ξ, θ)` is open, hence measurable
  set W : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π ∧ Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ U} with hW
  have hcontmap : Continuous fun p : ℝ × ℝ =>
      Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hWopen : IsOpen W := by
    have : W = (Prod.snd ⁻¹' Ioo (-π) π) ∩
        ((fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ⁻¹' U) := by
      ext p; simp only [hW, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]
    exact (isOpen_Ioo.preimage continuous_snd).inter (hU.preimage hcontmap)
  -- the jointly measurable integrand, folded through the slice indicator
  have hjoint : Measurable fun p : ℝ × ℝ =>
      W.indicator (fun q : ℝ × ℝ =>
        ENNReal.ofReal (Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)))) p :=
    (ENNReal.measurable_ofReal.comp (measurable_normSq_expGrad_logPolar u)).indicator
      hWopen.measurableSet
  -- `sliceEnergyU` as a full `θ`-Bochner integral of the folded integrand
  have hrepr : ∀ ξ : ℝ, sliceEnergyU u U ξ
      = ∫ θ : ℝ, (angularSlice U ξ).indicator
          (fun θ' => Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ := by
    intro ξ
    rw [sliceEnergyU, ← MeasureTheory.integral_indicator (isOpen_angularSlice hU ξ).measurableSet]
  rw [show sliceEnergyU u U = fun ξ => ∫ θ : ℝ, (angularSlice U ξ).indicator
      (fun θ' => Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ from
    funext hrepr]
  -- reduce to strong measurability of the joint real integrand
  have hjointR : StronglyMeasurable fun p : ℝ × ℝ =>
      (angularSlice U p.1).indicator
        (fun θ' => Complex.normSq (expGrad u ((p.1 : ℂ) + (θ' : ℂ) * Complex.I))) p.2 := by
    have hmeasR : Measurable fun p : ℝ × ℝ =>
        W.indicator (fun q : ℝ × ℝ =>
          Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))) p :=
      (measurable_normSq_expGrad_logPolar u).indicator hWopen.measurableSet
    have hfeq : (fun p : ℝ × ℝ =>
          (angularSlice U p.1).indicator
            (fun θ' => Complex.normSq (expGrad u ((p.1 : ℂ) + (θ' : ℂ) * Complex.I))) p.2)
        = fun p : ℝ × ℝ => W.indicator (fun q : ℝ × ℝ =>
            Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))) p := by
      funext p
      by_cases hp : p ∈ W
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p.2 ∈ angularSlice U p.1 from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p.2 ∉ angularSlice U p.1 from hp)]
    rw [hfeq]; exact hmeasR.stronglyMeasurable
  exact (hjointR.integral_prod_right').measurable

/-- **Rough-flux increment bounded by the total energy (full-circle collar window).** For `u`
harmonic on the open set `U`, if the whole strip box over `[ξ₁, ξ₂] × [−π, π]` maps into `U` and the
round sub-annulus `{e^{ζ₁} < |z| < e^{ζ₂}}` is contained in `U`, then the rough-flux increment over
`[ζ₁, ζ₂] ⊆ (ξ₁, ξ₂)` is at most the total Dirichlet energy `D(u; U)`.  Combines the exact
full-circle collar identity with monotonicity of the energy in the domain. -/
theorem roughFlux_sub_le_dirichletEnergy {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hsub : RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂) ⊆ U)
    (h1 : ξ₁ < ζ₁) (h12 : ζ₁ ≤ ζ₂) (h2 : ζ₂ < ξ₂)
    (hEfin : dirichletEnergy u U ≠ ⊤) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
  rw [roughFlux_sub_eq_dirichletEnergy_roundAnnulus hU hu hmaps h1 h12 h2]
  exact ENNReal.toReal_mono hEfin (dirichletEnergy_mono hsub)

/-! ### The level-set truncated rough flux and its `δ → 0` recovery

For `δ ∈ (0, 1)` the **superlevel set** `V_δ := {z ∈ U | δ < u z}` is open (`u` continuous on the
open `U`); its angular slice `angularSliceδ U u δ ξ` and the **δ-rough flux** `roughFluxδ` mirror
the angular slice and the rough flux with the indicator refined to the superlevel.  As `δ ↓ 0` the
superlevel slices increase to the slice of `U ∩ {u > 0}`, which — by the strong minimum principle
`u > 0` on a connected `U` where `u` is nonnegative and not identically `0` — is the full slice,
so `roughFluxδ u U · ξ → roughFlux u U ξ` by dominated convergence at any log-radius where the
slice radial-derivative integrand is slice-`L¹`. -/

/-- The **superlevel set** of a potential `u` above level `δ` inside an open set `U`: the points of
`U` where `u` strictly exceeds `δ`.  For continuous `u` on the open `U` it is open. -/
def superLevelU (U : Set ℂ) (u : ℂ → ℝ) (δ : ℝ) : Set ℂ := {z : ℂ | z ∈ U ∧ δ < u z}

/-- The **δ-angular slice**: the angles whose log-polar image lies in the superlevel set. -/
def angularSliceδ (U : Set ℂ) (u : ℂ → ℝ) (δ ξ : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ}

/-- The **δ-rough flux**: the rough flux with the slice indicator refined to the superlevel set. -/
noncomputable def roughFluxδ (u : ℂ → ℝ) (U : Set ℂ) (δ ξ : ℝ) : ℝ :=
  ∫ θ in Ioo (-π) π,
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}.indicator
      (fun θ' : ℝ => u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)).re) θ

/-- The superlevel set is open, for `u` harmonic (hence continuous) on the open `U`. -/
theorem isOpen_superLevelU {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ : ℝ) : IsOpen (superLevelU U u δ) := by
  have hcont : ContinuousOn u U := hu.continuousOn
  have hrw : superLevelU U u δ = U ∩ (u ⁻¹' Ioi δ) := by
    ext z; simp only [superLevelU, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi]
  rw [hrw]
  exact hcont.isOpen_inter_preimage hU isOpen_Ioi

/-- The δ-angular slice is the angular slice of the superlevel set. -/
theorem angularSliceδ_eq {U : Set ℂ} {u : ℂ → ℝ} (δ ξ : ℝ) :
    angularSliceδ U u δ ξ = angularSlice (superLevelU U u δ) ξ := rfl

/-- The δ-angular slice is open, for `u` harmonic on the open `U`. -/
theorem isOpen_angularSliceδ {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    IsOpen (angularSliceδ U u δ ξ) :=
  isOpen_angularSlice (isOpen_superLevelU hU hu δ) ξ

/-- The δ-angular slice is contained in `(−π, π)`, hence measurable. -/
theorem angularSliceδ_subset {U : Set ℂ} {u : ℂ → ℝ} (δ ξ : ℝ) :
    angularSliceδ U u δ ξ ⊆ Ioo (-π) π := fun _ hθ => hθ.1

/-- The δ-angular slice sits inside the full angular slice: superlevel points lie in `U`. -/
theorem angularSliceδ_subset_angularSlice {U : Set ℂ} {u : ℂ → ℝ} (δ ξ : ℝ) :
    angularSliceδ U u δ ξ ⊆ angularSlice U ξ :=
  fun _ hθ => ⟨hθ.1, hθ.2.1⟩

/-- **The δ-rough flux is the set integral over the δ-angular slice.** The indicator integral
defining `roughFluxδ` unfolds, exactly as for `roughFlux`, to the set integral of
`u · Re (expGrad u)` over the open δ-angular slice. -/
theorem roughFluxδ_eq_setIntegral_slice {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    roughFluxδ u U δ ξ = ∫ θ in angularSliceδ U u δ ξ,
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hπ := Real.pi_pos
  have hVopen : IsOpen (superLevelU U u δ) := isOpen_superLevelU hU hu δ
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hmeasset :
      MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} :=
    hcontmap.measurable hVopen.measurableSet
  unfold roughFluxδ
  rw [setIntegral_indicator hmeasset]
  refine setIntegral_congr_set ?_
  rw [angularSliceδ, superLevelU]
  refine (ae_eq_set.mpr ⟨?_, ?_⟩) <;>
    · refine measure_mono_null (fun θ hθ => ?_) measure_empty
      simp only [mem_diff, mem_inter_iff, mem_setOf_eq] at hθ
      tauto

/-- **The δ-rough flux is the rough flux of the superlevel set.** The δ-rough flux restricts the
slice indicator to the superlevel set `V_δ = {u > δ} ∩ U`, which is exactly the rough flux of `u`
over the open set `V_δ`. -/
theorem roughFluxδ_eq_roughFlux_superLevelU {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    roughFluxδ u U δ ξ = roughFlux u (superLevelU U u δ) ξ := by
  rw [roughFluxδ_eq_setIntegral_slice hU hu,
    roughFlux_eq_setIntegral_slice (isOpen_superLevelU hU hu δ), angularSliceδ_eq]

/-- **Compact containment of a superlevel window.** For `u` continuous on `closure U` and vanishing
on the part of `frontier U` inside the unit disc, the closure of the intersection of the superlevel
set `{u > δ}` (`δ > 0`) with a window annulus `{e^{ζ₁} < |z| < e^{ζ₂}}` (`ζ₂ < 0`) is a compact
subset of `U`.  It is closed and bounded (the window sits in the disc of radius `e^{ζ₂} < 1`), and
each of its points `w` has `u w ≥ δ > 0` by continuity — a frontier point with `‖w‖ < 1` would force
`u w = 0`, so `w` is an interior point of `U`. -/
theorem closure_superLevel_window_subset {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hδ : 0 < δ) (hζ₂ : ζ₂ < 0) :
    IsCompact (closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂))) ∧
      closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) ⊆ U := by
  set W : Set ℂ := RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂) with hW
  set V : Set ℂ := superLevelU U u δ with hV
  set K : Set ℂ := closure (V ∩ W) with hK
  have hexp1 : Real.exp ζ₂ < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hζ₂
  have hWsub : W ⊆ {z : ℂ | dist z 0 ≤ Real.exp ζ₂} := fun z hz => hz.2.le
  have hclW : closure W ⊆ {z : ℂ | dist z 0 ≤ Real.exp ζ₂} :=
    closure_minimal hWsub (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hKdisc : K ⊆ {z : ℂ | dist z 0 ≤ Real.exp ζ₂} :=
    (closure_mono inter_subset_right).trans hclW
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨Real.exp ζ₂, fun z hz => ?_⟩
    rw [Metric.mem_closedBall]; exact hKdisc hz
  have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_closure hKbdd
  refine ⟨hKcompact, ?_⟩
  intro w hw
  have hVWU : V ∩ W ⊆ U := inter_subset_left.trans (fun z hz => hz.1)
  have hwclU : w ∈ closure U := closure_mono hVWU hw
  have hwnorm : ‖w‖ < 1 := by
    have hle := hKdisc hw
    rw [mem_setOf_eq, dist_zero_right] at hle
    exact lt_of_le_of_lt hle hexp1
  have huwge : δ ≤ u w := by
    have hmap : MapsTo u (V ∩ W) (Ici δ) := fun z hz => le_of_lt hz.1.2
    have hclsub : closure (V ∩ W) ⊆ closure U := closure_mono hVWU
    have hcl : MapsTo u (closure (V ∩ W)) (closure (Ici δ)) :=
      hmap.closure_of_continuousOn (hucont.mono hclsub)
    have := hcl hw
    rwa [closure_Ici, mem_Ici] at this
  have hnotfront : w ∉ frontier U := by
    intro hfront
    have := hE0 w hfront hwnorm
    linarith
  rw [closure_eq_self_union_frontier] at hwclU
  exact hwclU.resolve_right hnotfront

/-- **Strict positivity of a nonnegative nonconstant harmonic potential.** For `u` harmonic on the
open preconnected set `U`, nonnegative on `U` and strictly positive at one point, the strong minimum
principle gives `0 < u` throughout `U`: a zero would force `u ≡ 0`, contradicting the positive
point. -/
theorem pos_of_harmonic_nonneg {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hnn : ∀ z ∈ U, 0 ≤ u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hpos : 0 < u z₀) : ∀ z ∈ U, 0 < u z := by
  intro z hz
  refine lt_of_le_of_ne (hnn z hz) (fun heq => ?_)
  have hzero := harmonic_eq_zero_of_nonneg_eq_zero hU hUconn hu hnn hz heq.symm
  exact absurd (hzero z₀ hz₀) hpos.ne'

/-- **`δ`-monotone pointwise recovery of the slice indicator.** For `u` strictly positive on `U`,
each angle `θ` of the full angular slice enters the δ-angular slice once `δ < u (e^{ξ+iθ})`; hence
along any positive null-sequence `δ n → 0`, the δ-slice indicator of the flux integrand converges
pointwise to the full-slice indicator. -/
theorem tendsto_indicator_angularSliceδ {u : ℂ → ℝ} {U : Set ℂ} {ξ : ℝ}
    (hpos : ∀ z ∈ U, 0 < u z) {d : ℕ → ℝ} (hdto : Tendsto d atTop (𝓝 0))
    (F : ℝ → ℝ) (θ : ℝ) :
    Tendsto (fun n => {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)}.indicator F θ)
      atTop (𝓝 ({θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator F θ)) := by
  by_cases hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
  · -- `θ` in the full slice: eventually `d n < u(e^{ξ+iθ})`, so the δ-indicator is `F θ`
    rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
    have hupos : 0 < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := hpos _ hmem
    have hev : ∀ᶠ n in atTop, d n < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      hdto.eventually_lt_const hupos
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with n hn
    rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
      superLevelU U u (d n)} from ⟨hmem, hn⟩)]
  · -- `θ` outside the full slice: both indicators are `0`
    rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
      superLevelU U u (d n)} from fun h => hmem h.1)]

/-- **`δ → 0` recovery of the rough flux.** For `u` harmonic and strictly positive on the open set
`U`, if at log-radius `ξ` the slice radial-derivative integrand `θ ↦ Re (expGrad u)` is integrable
on the angular slice, then along any positive null-sequence `δ n → 0` the δ-rough flux tends to the
rough flux: the δ-slice indicators of the integrand `u · Re (expGrad u)` increase pointwise to the
full-slice indicator, dominated by the slice-`L¹` bound `|u| · |Re (expGrad u)|`, so dominated
convergence applies on `(−π, π)`. -/
theorem tendsto_roughFluxδ_atZero {u : ℂ → ℝ} {U : Set ℂ} {ξ M : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z) (hMnn : 0 ≤ M)
    (hM : ∀ θ ∈ angularSlice U ξ, |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hReInt : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    {d : ℕ → ℝ} (hdto : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => roughFluxδ u U (d n) ξ) atTop (𝓝 (roughFlux u U ξ)) := by
  have hπ := Real.pi_pos
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hssub : s ⊆ Ioo (-π) π := angularSlice_subset U ξ
  set I : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hI
  -- the fixed dominating function: the full-slice indicator of `|I|`
  set B : ℝ → ℝ := s.indicator (fun θ => M * |(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|)
    with hB
  -- `I` is continuous on the full slice `s`
  have hcontI : ContinuousOn I s := by
    intro θ hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2
    have hcm : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
      fun_prop
    have hcu : ContinuousAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))) θ :=
      (ContinuousAt.comp (g := u)
        (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hcm)
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hmem
    have hcg : ContinuousAt
        (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      (ContinuousAt.comp (g := fun w : ℂ => (expGrad u w).re)
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (Complex.continuous_re.continuousAt.comp hdC.continuousAt) (by fun_prop))
    exact (hcu.mul hcg).continuousWithinAt
  have hBint : IntegrableOn B (Ioo (-π) π) := by
    have hsint : IntegrableOn
        (fun θ : ℝ => M * |(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|) s :=
      hReInt.abs.const_mul M
    rw [hB, integrableOn_indicator_iff hsmeas, Set.inter_eq_self_of_subset_left hssub]
    exact hsint
  -- indicator a.e.-strong-measurability of each δ-integrand on `(−π, π)`
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun θ => {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)}.indicator I θ) (volume.restrict (Ioo (-π) π)) := by
    intro n
    have hVmeas : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable
          (isOpen_superLevelU hU hu (d n)).measurableSet
    rw [aestronglyMeasurable_indicator_iff hVmeas]
    -- `I` on `(Ioo (-π) π) ∩ V`; since `V ∩ Ioo ⊆ s`, restrict `I`'s slice measurability
    have hIslice : AEStronglyMeasurable I (volume.restrict s) :=
      hcontI.aestronglyMeasurable hsmeas
    refine hIslice.mono_measure ?_
    rw [Measure.restrict_restrict hVmeas]
    refine Measure.restrict_mono (fun θ hθ => ?_) le_rfl
    exact (show θ ∈ s from ⟨hθ.2, hθ.1.1⟩)
  -- rewrite both sides as indicator integrals over the fixed `(−π, π)`
  have hδform : ∀ n, roughFluxδ u U (d n) ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
          superLevelU U u (d n)}.indicator I θ := fun n => rfl
  have hlimform : roughFlux u U ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator I θ := by
    rw [roughFlux_eq_setIntegral_slice hU, ← hs]
    rw [show (∫ θ in Ioo (-π) π, {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator I θ)
        = ∫ θ in Ioo (-π) π, s.indicator I θ from
      setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)]
    · rw [MeasureTheory.integral_indicator hsmeas, Measure.restrict_restrict hsmeas,
        Set.inter_eq_self_of_subset_left hssub]
    · by_cases hθU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
      · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hθU),
          Set.indicator_of_mem (show θ ∈ s from ⟨hθ, hθU⟩)]
      · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hθU),
          Set.indicator_of_notMem (show θ ∉ s from fun h => hθU h.2)]
  simp only [hδform]
  rw [hlimform]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence B hFmeas hBint ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    by_cases hθV : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u (d n)
    · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV)]
      have hθs : θ ∈ s := ⟨hθ, hθV.1⟩
      rw [hB, Set.indicator_of_mem hθs, hI, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM θ hθs) (abs_nonneg _)
    · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV),
        norm_zero, hB]
      by_cases hθs : θ ∈ s
      · rw [Set.indicator_of_mem hθs]; positivity
      · rw [Set.indicator_of_notMem hθs]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    exact tendsto_indicator_angularSliceδ hpos hdto I θ

/-- **Rough-flux increment from the level-set increment bound.** For `u` harmonic and strictly
positive on the open set `U`, uniformly bounded by `M` on both slices at `ζ₁` and `ζ₂` with the
slice radial-derivative integrand integrable there, if the δ-rough-flux increment is bounded by a
constant `D` for every `δ > 0`, then the rough-flux increment is bounded by `D`: pass to `δ → 0`
using the `δ`-recovery of the rough flux at each of the two log-radii. -/
theorem roughFlux_sub_le_of_roughFluxδ_sub_le {u : ℂ → ℝ} {U : Set ℂ} {ζ₁ ζ₂ M D : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hMnn : 0 ≤ M)
    (hM1 : ∀ θ ∈ angularSlice U ζ₁, |u (Complex.exp ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hM2 : ∀ θ ∈ angularSlice U ζ₂, |u (Complex.exp ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hRe1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₁))
    (hRe2 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₂))
    (hδbd : ∀ δ : ℝ, 0 < δ → roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ D) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ D := by
  -- a concrete positive null-sequence `δ n = 1/(n+1) → 0`
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hd
  have hdpos : ∀ n, 0 < d n := fun n => by positivity
  have hdto : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- `δ`-recovery at both log-radii
  have hlim1 : Tendsto (fun n => roughFluxδ u U (d n) ζ₁) atTop (𝓝 (roughFlux u U ζ₁)) :=
    tendsto_roughFluxδ_atZero hU hu hpos hMnn hM1 hRe1 hdto
  have hlim2 : Tendsto (fun n => roughFluxδ u U (d n) ζ₂) atTop (𝓝 (roughFlux u U ζ₂)) :=
    tendsto_roughFluxδ_atZero hU hu hpos hMnn hM2 hRe2 hdto
  have hlim : Tendsto (fun n => roughFluxδ u U (d n) ζ₂ - roughFluxδ u U (d n) ζ₁) atTop
      (𝓝 (roughFlux u U ζ₂ - roughFlux u U ζ₁)) := hlim2.sub hlim1
  refine le_of_tendsto hlim ?_
  filter_upwards with n
  exact hδbd (d n) (hdpos n)

/-- **The slope is bounded by the total energy.** Let `u` be harmonic on an open set `U` containing
the whole punctured collar `{0 < |z| < 1}` (every circle `e^{ξ+iθ}`, `ξ < 0`, lies in `U`), with
finite Dirichlet energy `D(u; U) < ∞`.  If the rough flux tends to the boundary slope `b` as the
log-radius rises to `0` and tends to `0` as it falls to `−∞` (the potential vanishing at the
origin), then the slope is bounded by the total energy: `b ≤ D(u; U)`.

The two flux limits are the boundary data of the flux–energy exchange: on every full-circle window
`[ζ₁, ζ₂] ⊆ (−∞, 0)` the rough-flux increment is the sub-annulus energy, bounded by `D(u; U)`;
letting `ζ₂ ↑ 0` and `ζ₁ ↓ −∞` sends the increment to `b − 0 = b`. -/
theorem slope_le_energy {u : ℂ → ℝ} {U : Set ℂ} {b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ ξ : ℝ, ξ < 0 → ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hEfin : dirichletEnergy u U ≠ ⊤)
    (hTop : Tendsto (roughFlux u U) (𝓝[<] (0 : ℝ)) (𝓝 b))
    (hBot : Tendsto (roughFlux u U) atBot (𝓝 0)) :
    b ≤ (dirichletEnergy u U).toReal := by
  -- box-mapping over any slab strictly below `0`
  have hbox : ∀ ξ₁ ξ₂ : ℝ, ξ₂ < 0 → ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro ξ₁ ξ₂ hξ₂ x hx θ _
    exact hmaps x (lt_of_le_of_lt hx.2 hξ₂) θ
  -- the whole round sub-annulus below `0` lies in `U`
  have hann : ∀ ζ₁ ζ₂ : ℝ, ζ₂ < 0 → RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂) ⊆ U := by
    intro ζ₁ ζ₂ hζ₂ z hz
    obtain ⟨hz1, hz2⟩ := hz
    -- write `z = e^{ξ+θi}` with `ξ = log|z| < ζ₂ < 0`
    set ξ : ℝ := Real.log (dist z 0) with hξ
    have hdpos : 0 < dist z 0 := lt_of_le_of_lt (Real.exp_pos _).le hz1
    have hznorm : dist z 0 = Real.exp ξ := by rw [hξ, Real.exp_log hdpos]
    have hξ0 : ξ < 0 := by
      have hlt : Real.exp ξ < Real.exp ζ₂ := by rw [← hznorm]; exact hz2
      exact lt_trans (Real.exp_lt_exp.mp hlt) hζ₂
    have hzrepr : z = Complex.exp ((ξ : ℂ) + ((z.arg : ℝ) : ℂ) * Complex.I) := by
      have hnz := Complex.norm_mul_exp_arg_mul_I z
      have hnorm : (‖z‖ : ℂ) = ((Real.exp ξ : ℝ) : ℂ) := by
        rw [← dist_zero_right, hznorm]
      rw [Complex.exp_add, ← Complex.ofReal_exp, ← hnorm, hnz]
    rw [hzrepr]; exact hmaps ξ hξ0 z.arg
  -- windowed increment inequality for any `ζ₁ ≤ ζ₂ < 0`
  have hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
    intro ζ₁ ζ₂ h12 hζ₂
    exact roughFlux_sub_le_dirichletEnergy hU hu
      (hbox (ζ₁ - 1) (ζ₂ + (-ζ₂) / 2) (by linarith))
      (hann ζ₁ ζ₂ hζ₂) (by linarith) h12 (by linarith) hEfin
  -- fix an inner radius `ζ₁` and let the outer radius rise to `0`: `b − roughFlux ζ₁ ≤ D`
  have hfix : ∀ ζ₁ : ℝ, ζ₁ < 0 → b - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
    intro ζ₁ hζ₁
    have hlim : Tendsto (fun ζ₂ : ℝ => roughFlux u U ζ₂ - roughFlux u U ζ₁)
        (𝓝[<] (0 : ℝ)) (𝓝 (b - roughFlux u U ζ₁)) := hTop.sub_const _
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hζ₁, self_mem_nhdsWithin] with ζ₂ hζ₂mem hζ₂neg
    exact hwin ζ₁ ζ₂ hζ₂mem.1.le hζ₂neg
  -- let the inner radius fall to `−∞`: `roughFlux ζ₁ → 0`, giving `b ≤ D`
  have hlim2 : Tendsto (fun ζ₁ : ℝ => b - roughFlux u U ζ₁) atBot (𝓝 (b - 0)) :=
    hBot.const_sub b
  rw [sub_zero] at hlim2
  refine le_of_tendsto hlim2 ?_
  filter_upwards [Iio_mem_atBot (0 : ℝ)] with ζ₁ hζ₁
  exact hfix ζ₁ hζ₁

end RiemannDynamics
