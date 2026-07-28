/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.SequentialIBP.FluxFTC

/-!
# The keystone slope bound and the truncated rough flux

This file converts the rough-ring flux of `SequentialIBP.Basic` into the keystone slope inequality
`b ≤ (dirichletEnergy u U).toReal`, and then builds the truncated apparatus that
`SequentialIBP.LevelSetNullity` runs on.  Two flux limits are discharged from ring-potential data on
a round collar `{r₀ < |z| < 1}` whose full circles lie in `U` — the boundary limit `roughFlux ξ → b`
as `ξ ↑ 0`, and a null sequence `ξ n → −∞` along which the rough flux vanishes — and are combined
with a windowed increment inequality over the windows `ζ₁ ≤ ζ₂ < 0` that genuinely exist for a
keystone `U`, whose small circles are blocked by the continuum on its frontier.  The second half
replaces the potential factor `u` by its truncation `(u − δ)⁺` on the superlevel set
`superLevelU U u δ = {u > δ} ∩ U` of `SequentialIBP.FluxFTC`: the truncated angular integration by
parts, the truncated rough flux with its `δ → 0` recovery of `roughFlux`, and the windowed truncated
integrand.  The last three are what `SequentialIBP.LevelSetNullity` differentiates in `ξ` for the
moving-domain flux FTC and, with it, the level-set discharge of the windowed increment inequality.

## Main definitions

* `RiemannDynamics.truncRoughFlux` — the **truncated rough flux**: the angle integral over
  `(−π, π)` of the superlevel-slice indicator against `(u − δ)⁺ · Re (expGrad u)`.  For `U` open and
  `u` harmonic on `U` it is the set integral of `(u − δ)⁺ · Re (expGrad u)` over the open δ-slice
  `angularSliceδ U u δ ξ` (`truncRoughFlux_eq_setIntegral_slice`).
* `RiemannDynamics.windowedTruncIntegrand` — the **windowed truncated integrand**
  `H w = 1_U (e^w) · (u (e^w) − δ)⁺ · Re (expGrad u w)`, a function of the log-polar variable `w`.
  With no hypotheses at all, `truncRoughFlux u U δ ξ` is the `θ`-integral of `H (ξ + θi)` over
  `(−π, π)` (`truncRoughFlux_eq_integral_windowedTruncIntegrand`).

## Main results

* `RiemannDynamics.roughFlux_tendsto_slope_ringPotential` — for `0 < r₀ < 1`, if every full circle
  of log-radius in `(log r₀, 0)` lies in `U`, and `u` is harmonic on the round collar
  `{r₀ < |z| < 1}`, continuous on `{r₀ ≤ |z| ≤ 1}`, equal to `1` on `grotzschOuter`, with
  `0 ≤ u ≤ 1` on the collar and log-circle mean `logCircleMean 0 u ξ = 2π + b·ξ` for
  `ξ ∈ (log r₀, 0)`, then `roughFlux u U ξ → b` as `ξ ↑ 0`.  This is the upper flux limit; `U` is
  otherwise unconstrained, since on the collar the slice indicator is trivial.
* `RiemannDynamics.exists_seq_roughFlux_tendsto_zero_atBot'` — for `u` harmonic on an open `U`,
  bounded by a constant `M ≥ 0` on *every* angular slice, and of finite Dirichlet energy
  `dirichletEnergy u U ≠ ⊤`, there is a sequence `ξ n → −∞` along which `roughFlux u U (ξ n) → 0`.
  The radii are selected off a null set so that the per-slice Cauchy–Schwarz bound
  `|roughFlux| ≤ M · √(2π) · √(sliceEnergyU)` (`abs_roughFlux_le_slice`) applies and the slice
  energy vanishes along them.
* `RiemannDynamics.slope_le_energy_of_windowed_seq` — a pure limit assembly, with no harmonicity,
  openness or integrability assumed: from `roughFlux u U ξ → b` as `ξ ↑ 0`, a sequence `ξ n → −∞`
  with `roughFlux u U (ξ n) → 0`, and `roughFlux u U ζ₂ − roughFlux u U ζ₁ ≤ D` for all
  `ζ₁ ≤ ζ₂ < 0`, one gets `b ≤ D`.  Only windows lying below log-radius `0` are consumed.
* `RiemannDynamics.slope_le_energy_ringPotential'` — the keystone-shaped slope bound
  `b ≤ (dirichletEnergy u U).toReal`, for `u` harmonic on the open `U` with `0 ≤ u ≤ 1` on `U` and
  `dirichletEnergy u U ≠ ⊤`, given the collar ring-potential data above and, as the one remaining
  hypothesis, the windowed increment inequality
  `roughFlux u U ζ₂ − roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal` for `ζ₁ ≤ ζ₂ < 0`.
  `slope_le_energy_ringPotential''` trades that hypothesis for the per-level `roughFluxδ` increment
  bound.
* `RiemannDynamics.setIntegral_slice_posPart_re_deriv_expGrad` — **truncated angular integration by
  parts on a full δ-slice**, valid across the `±π` branch cut.  For `u` harmonic on the open `U`
  with `θ ↦ u (e^{ξ+θi})` continuous on all of `ℝ`, with `u = δ` at every circle point lying in
  `closure (superLevelU U u δ)` but not in `superLevelU U u δ`, and with one constant `C` bounding
  both `normSq (expGrad u)` and `|Re (deriv (expGrad u))|` at the superlevel circle points, the
  integral of `(u − δ)⁺ · Re (deriv (expGrad u))` over `angularSliceδ U u δ ξ` equals that of
  `(Im (expGrad u))²`.  It is assembled from the per-arc identity
  `integral_posPart_re_deriv_expGrad_arc`, whose boundary term dies because `(u − δ)⁺` vanishes at
  the arc endpoints.
* `RiemannDynamics.roughFlux_sub_le_of_truncRoughFlux_sub_le` — for `u` harmonic and *strictly
  positive* on the open `U`, bounded by `M ≥ 0` on the two slices at `ζ₁` and `ζ₂` with
  `Re (expGrad u)` integrable on both, a bound `truncRoughFlux δ ζ₂ − truncRoughFlux δ ζ₁ ≤ D`
  holding for every `δ > 0` passes to `roughFlux u U ζ₂ − roughFlux u U ζ₁ ≤ D`.  Strict positivity
  is what makes the superlevel slices exhaust the full slice as `δ ↓ 0`
  (`tendsto_truncRoughFlux_atZero`).
* `RiemannDynamics.continuousOn_windowedTruncIntegrand` — the windowed truncated integrand is
  continuous on the log-strip box `stripBox ξ₁ ξ₂ (−π) π`, for `u` harmonic on the open `U` and
  under the compact-containment hypothesis
  `closure (superLevelU U u δ ∩ RoundAnnulus 0 (exp ξ₁) (exp ξ₂)) ⊆ U`.  Without that containment
  the indicator can jump across the frontier of `U`; with it, `H` vanishes on a neighbourhood of
  every strip-box point outside the containment.
-/

namespace RiemannDynamics

open MeasureTheory intervalIntegral Filter Set
open scoped Real ENNReal Topology
open Complex

/-! ### The keystone-shaped slope bound: discharging the two flux limits

For the keystone open set `U` (whose frontier contains a connected continuum `E ∋ 0` blocking small
circles) the full-circle hypothesis of `slope_le_energy` fails.  The lemmas below discharge the two
flux limits from ring-potential data on a *round collar* `{r₀ < |z| < 1}` whose full circles lie in
`U`, and package the slope bound consuming the windowed increment inequality over the genuine window
family (log-radii below `0`, where the collar circles are full). -/

/-- **Set-integral Cauchy–Schwarz.** For `g` with `g` and `g²` integrable on a finite-measure set
`s`, `(∫_s |g|)² ≤ (volume s).toReal · ∫_s g²`, via the discriminant of the nonnegative quadratic
`x ↦ ∫_s (x·|g| + 1)²`. -/
theorem sq_setIntegral_abs_le {g : ℝ → ℝ} {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hsfin : volume s ≠ ⊤) (hg : IntegrableOn g s)
    (hg2 : IntegrableOn (fun t => (g t) ^ 2) s) :
    (∫ t in s, |g t|) ^ 2 ≤ (volume s).toReal * ∫ t in s, (g t) ^ 2 := by
  set A := ∫ t in s, (g t) ^ 2 with hA
  set B := ∫ t in s, |g t| with hB
  set V := (volume s).toReal with hV
  have hQ : ∀ x : ℝ, 0 ≤ A * (x * x) + (2 * B) * x + V := by
    intro x
    have key : ∀ t, (x * |g t| + 1) ^ 2 = x ^ 2 * (g t) ^ 2 + (2 * x) * |g t| + 1 := by
      intro t; rw [← sq_abs (g t)]; ring
    have hi1 : IntegrableOn (fun t => x ^ 2 * (g t) ^ 2) s := hg2.const_mul (x ^ 2)
    have hi2 : IntegrableOn (fun t => (2 * x) * |g t|) s := hg.abs.const_mul (2 * x)
    have hi3 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s := integrableOn_const hsfin (by simp)
    have hnn : (0 : ℝ) ≤ ∫ t in s, (x * |g t| + 1) ^ 2 :=
      setIntegral_nonneg hsmeas fun t _ => by positivity
    have hexp : (∫ t in s, (x * |g t| + 1) ^ 2) = A * (x * x) + (2 * B) * x + V := by
      have hcong : (∫ t in s, (x * |g t| + 1) ^ 2)
          = ∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t| + 1) :=
        setIntegral_congr_fun hsmeas fun t _ => key t
      have hsplit1 : (∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t| + 1))
          = (∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t|)) + ∫ _t in s, (1 : ℝ) :=
        integral_add (hi1.add hi2) hi3
      have hsplit2 : (∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t|))
          = (∫ t in s, x ^ 2 * (g t) ^ 2) + ∫ t in s, (2 * x) * |g t| :=
        integral_add hi1 hi2
      rw [hcong, hsplit1, hsplit2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]
      rw [← hA, ← hB, hV, ← measureReal_def]
      ring
    rw [hexp] at hnn; exact hnn
  have hdisc : discrim A (2 * B) V ≤ 0 := discrim_le_zero hQ
  have hdisc' : (2 * B) ^ 2 - 4 * A * V ≤ 0 := by
    have : discrim A (2 * B) V = (2 * B) ^ 2 - 4 * A * V := by unfold discrim; ring
    rwa [this] at hdisc
  nlinarith [hdisc']

/-- **Per-slice Cauchy–Schwarz bound on the rough flux.** For `u` harmonic on the open set `U`, if
on the angular slice at log-radius `ξ` the potential is bounded by `M`, the slice radial-derivative
integrand is integrable and the slice squared gradient is integrable, then the rough flux is bounded
by `M · √(2π) · √(sliceEnergyU u U ξ)`: the flux is the slice integral of `u · Re (expGrad u)`,
bounded pointwise by `M · |Re (expGrad u)|`, whose slice `L¹` norm is Cauchy–Schwarz-dominated by
`√(2π) · √(∫ (Re expGrad)²) ≤ √(2π) · √(slice energy)`. -/
theorem abs_roughFlux_le_slice {u : ℂ → ℝ} {U : Set ℂ} {ξ M : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hMnn : 0 ≤ M)
    (hM : ∀ θ ∈ angularSlice U ξ, |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hReInt : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    (hEInt : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ)) :
    |roughFlux u U ξ| ≤ M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ)) := by
  have hπ := Real.pi_pos
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hsvol : volume s ≤ ENNReal.ofReal (2 * π) := by
    refine le_trans (measure_mono (angularSlice_subset U ξ)) ?_
    rw [Real.volume_Ioo]; exact le_of_eq (by rw [show π - -π = 2 * π by ring])
  have hsvol' : (volume s).toReal ≤ 2 * π := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsvol
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  set F : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hG
  -- `(Re expGrad)² ≤ normSq expGrad`, so `∫ G² ≤ sliceEnergyU`
  have hG2int : IntegrableOn (fun θ => (G θ) ^ 2) s := by
    refine (hEInt).mono' (hReInt.aestronglyMeasurable.pow 2) ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.normSq_apply]
    nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im]
  have hG2le : (∫ θ in s, (G θ) ^ 2) ≤ sliceEnergyU u U ξ := by
    rw [hs, sliceEnergyU]
    refine setIntegral_mono_on hG2int (hEInt.mono_set (by rw [hs])) ?_ (fun θ _ => ?_)
    · exact (isOpen_angularSlice hU ξ).measurableSet
    · rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im]
  -- `u ∘ exp` is continuous on the open slice, hence a.e.-strongly-measurable there
  have hFmeas : AEStronglyMeasurable F (volume.restrict s) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hsmeas
    intro θ hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2
    have hc : ContinuousAt u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt
    have hcm : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
      fun_prop
    exact (ContinuousAt.comp (g := u)
      (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) hc hcm).continuousWithinAt
  have hFGint : IntegrableOn (fun θ => F θ * G θ) s := by
    refine (hReInt.abs.const_mul M).mono' (hFmeas.mul hReInt.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM θ hθ) (abs_nonneg _)
  -- Cauchy–Schwarz: `∫_s |G| ≤ √(vol s) · √(∫_s G²) ≤ √(2π)·√(sliceEnergyU)`
  have hCS : (∫ θ in s, |G θ|) ≤ Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ) := by
    have hcs := sq_setIntegral_abs_le hsmeas (by
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsvol) hReInt hG2int
    have h0 : (0 : ℝ) ≤ ∫ θ in s, |G θ| := setIntegral_nonneg hsmeas fun θ _ => abs_nonneg _
    have hstep : (∫ θ in s, |G θ|) ≤ Real.sqrt ((volume s).toReal * ∫ θ in s, (G θ) ^ 2) := by
      rw [show (∫ θ in s, |G θ|) = Real.sqrt ((∫ θ in s, |G θ|) ^ 2) from (Real.sqrt_sq h0).symm]
      exact Real.sqrt_le_sqrt hcs
    calc (∫ θ in s, |G θ|)
        ≤ Real.sqrt ((volume s).toReal * ∫ θ in s, (G θ) ^ 2) := hstep
      _ = Real.sqrt ((volume s).toReal) * Real.sqrt (∫ θ in s, (G θ) ^ 2) :=
          Real.sqrt_mul ENNReal.toReal_nonneg _
      _ ≤ Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ) :=
          mul_le_mul (Real.sqrt_le_sqrt hsvol') (Real.sqrt_le_sqrt hG2le)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- assemble
  rw [roughFlux_eq_setIntegral_slice hU, ← hs]
  calc |∫ θ in s, F θ * G θ|
      ≤ ∫ θ in s, |F θ * G θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in s, M * |G θ| := by
        refine setIntegral_mono_on hFGint.abs ((hReInt.abs.const_mul M)) hsmeas fun θ hθ => ?_
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM θ hθ) (abs_nonneg _)
    _ = M * ∫ θ in s, |G θ| := by rw [MeasureTheory.integral_const_mul]
    _ ≤ M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ)) :=
        mul_le_mul_of_nonneg_left hCS hMnn

/-- **A finite tail integral has a null-sequence of small values escaping to `−∞`.** For a
nonnegative measurable `f` with finite integral over `Iic ξ₀`, there is a sequence `ξ n → −∞` inside
`Iic ξ₀` along which `f (ξ n) → 0`: for each `n`, the set `{ξ ≤ ξ₀ - n | f ξ < 1/(n+1)}` is
nonempty, since otherwise `f ≥ 1/(n+1)` on the infinite-measure set `Iic (ξ₀ - n)`, forcing an
infinite integral. -/
theorem exists_seq_tendsto_zero_atBot_of_lintegral_ne_top {f : ℝ → ℝ} {ξ₀ : ℝ}
    (hfmeas : Measurable f) (hfnn : ∀ ξ, 0 ≤ f ξ)
    (hfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (f ξ)) ≠ ⊤) :
    ∃ ξ : ℕ → ℝ, (∀ n, ξ n ≤ ξ₀) ∧ Tendsto ξ atTop atBot ∧
      Tendsto (fun n => f (ξ n)) atTop (𝓝 0) := by
  have hncast : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have key : ∀ n : ℕ, ∃ x : ℝ, x ≤ ξ₀ - n ∧ f x < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra hcon0
    have hcon : ∀ x : ℝ, x ≤ ξ₀ - (n : ℝ) → 1 / ((n : ℝ) + 1) ≤ f x := by
      intro x hx
      by_contra hlt
      exact hcon0 ⟨x, hx, lt_of_not_ge hlt⟩
    -- `f ≥ 1/(n+1)` on `Iic (ξ₀ - n)`, an infinite-measure set, forces an infinite integral
    have hsub : Iic (ξ₀ - (n : ℝ)) ⊆ Iic ξ₀ := Iic_subset_Iic.mpr (by linarith [hncast n])
    have hmono : (∫⁻ _ξ in Iic (ξ₀ - (n : ℝ)), ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        ≤ ∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (f ξ) := by
      refine le_trans ?_ (lintegral_mono_set hsub)
      refine setLIntegral_mono hfmeas.ennreal_ofReal (fun ξ hξ => ?_)
      exact ENNReal.ofReal_le_ofReal (hcon ξ (mem_Iic.mp hξ))
    rw [setLIntegral_const, Real.volume_Iic] at hmono
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact hfin (top_le_iff.mp (le_trans (by rw [ENNReal.mul_top hpos.ne']) hmono))
  choose ξ hξ using key
  refine ⟨ξ, fun n => le_trans (hξ n).1 (by linarith [hncast n]), ?_, ?_⟩
  · refine tendsto_atBot_mono (fun n => (hξ n).1) ?_
    exact tendsto_atBot_add_const_left _ ξ₀
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => hfnn _) (fun n => (hξ n).2.le) h1

/-- **A finite tail integral has a null-sequence of small values escaping to `−∞`, avoiding a null
set.** Strengthening of `exists_seq_tendsto_zero_atBot_of_lintegral_ne_top`: if additionally a
predicate `P` holds almost everywhere, the escaping sequence can be chosen inside `{ξ | P ξ}`.  For
each `n` the small-value tail set `{ξ ≤ ξ₀ - n | f ξ < 1/(n+1)}` has infinite measure (else the
integral diverges), so removing the null set `{¬P}` leaves it nonempty. -/
theorem exists_seq_tendsto_zero_atBot_of_lintegral_ne_top_ae {f : ℝ → ℝ} {ξ₀ : ℝ} {P : ℝ → Prop}
    (hfmeas : Measurable f) (hfnn : ∀ ξ, 0 ≤ f ξ)
    (hfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (f ξ)) ≠ ⊤)
    (hP : ∀ᵐ ξ : ℝ, P ξ) :
    ∃ ξ : ℕ → ℝ, (∀ n, ξ n ≤ ξ₀) ∧ (∀ n, P (ξ n)) ∧ Tendsto ξ atTop atBot ∧
      Tendsto (fun n => f (ξ n)) atTop (𝓝 0) := by
  have hncast : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  set N : Set ℝ := {ξ : ℝ | ¬ P ξ} with hN
  have hNnull : volume N = 0 := hP
  have key : ∀ n : ℕ, ∃ x : ℝ, x ≤ ξ₀ - n ∧ f x < 1 / ((n : ℝ) + 1) ∧ P x := by
    intro n
    set T : Set ℝ := {x : ℝ | x ≤ ξ₀ - (n : ℝ) ∧ f x < 1 / ((n : ℝ) + 1)} with hT
    have hTmeas : MeasurableSet T :=
      (measurableSet_Iic).inter (measurableSet_lt hfmeas measurable_const)
    -- `T` has infinite measure: else `Iic (ξ₀-n) ⊆ T ∪ Big` bounds `⊤` by finite mass
    set Big : Set ℝ := {x : ℝ | x ≤ ξ₀ - (n : ℝ) ∧ 1 / ((n : ℝ) + 1) ≤ f x} with hBig
    have hBigsub : Big ⊆ Iic ξ₀ := fun x hx => mem_Iic.mpr (by linarith [hx.1, hncast n])
    have hBigmeas : MeasurableSet Big :=
      measurableSet_Iic.inter (measurableSet_le measurable_const hfmeas)
    have hcompl : Iic (ξ₀ - (n : ℝ)) ⊆ T ∪ Big := by
      intro x hx
      by_cases hlt : f x < 1 / ((n : ℝ) + 1)
      · exact Or.inl ⟨mem_Iic.mp hx, hlt⟩
      · exact Or.inr ⟨mem_Iic.mp hx, le_of_not_gt hlt⟩
    have hIicinf : volume (Iic (ξ₀ - (n : ℝ))) = ⊤ := by rw [Real.volume_Iic]
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    -- the large-value tail set carries only finite measure (Markov, restricted to `Iic ξ₀`)
    have hgefin : volume Big ≠ ⊤ := by
      intro hgeinf
      have hbig : (∫⁻ ξ in Big, ENNReal.ofReal (f ξ)) = ⊤ := by
        refine top_le_iff.mp ?_
        calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) * volume Big := by
              rw [hgeinf, ENNReal.mul_top hpos.ne']
          _ = ∫⁻ _ξ in Big, ENNReal.ofReal (1 / ((n : ℝ) + 1)) := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ ξ in Big, ENNReal.ofReal (f ξ) := by
              refine setLIntegral_mono hfmeas.ennreal_ofReal (fun ξ hξ => ?_)
              exact ENNReal.ofReal_le_ofReal hξ.2
      exact hfin (top_le_iff.mp (hbig ▸ lintegral_mono_set hBigsub))
    have hTinf : volume T = ⊤ := by
      have hle : volume (Iic (ξ₀ - (n : ℝ))) ≤ volume T + volume Big :=
        (measure_mono hcompl).trans (measure_union_le T Big)
      rw [hIicinf] at hle
      by_contra hfinT
      exact (ENNReal.add_ne_top.mpr ⟨hfinT, hgefin⟩) (top_le_iff.mp hle)
    -- removing the null set `N` keeps `T` nonempty
    have hTN : volume (T \ N) = ⊤ := by
      rw [measure_diff_null hNnull]; exact hTinf
    obtain ⟨x, hxT, hxN⟩ := nonempty_of_measure_ne_zero (by rw [hTN]; exact ENNReal.top_ne_zero)
    exact ⟨x, hxT.1, hxT.2, not_not.mp hxN⟩
  choose ξ hξ using key
  refine ⟨ξ, fun n => le_trans (hξ n).1 (by linarith [hncast n]), fun n => (hξ n).2.2, ?_, ?_⟩
  · refine tendsto_atBot_mono (fun n => (hξ n).1) ?_
    exact tendsto_atBot_add_const_left _ ξ₀
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => hfnn _) (fun n => (hξ n).2.1.le) h1

/-- **Upper flux limit for a ring potential (discharging `hTop`).** If the full circles of every
collar radius `ξ ∈ (log r₀, 0)` lie in `U` and `u` is a ring potential on the round collar
`{r₀ < |z| < 1}` with affine circle mean `2π + b·ξ`, then the rough flux of `u` on `U` tends to the
boundary slope `b` as the log-radius rises to `0`: on the collar the indicator is trivial, so the
rough flux agrees with the round-annulus ring flux, whose boundary limit is `b`. -/
theorem roughFlux_tendsto_slope_ringPotential {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ) :
    Tendsto (roughFlux u U) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
  have hring := ringFlux_tendsto_slope h0 h1 hu hcont hone hrange hslope
  refine hring.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (Real.log_neg h0 h1)] with ξ hξ
  exact (roughFlux_eq_ringFlux (fun θ => hcollar ξ hξ.1 hξ.2 θ)).symm

/-- **A.e. slice integrability of the squared gradient from finite total energy (`W1c`, a.e.).** For
`u` harmonic on the open set `U` with finite Dirichlet energy, at almost every log-radius `ξ ≤ ξ₀`
the squared log-polar gradient `θ ↦ normSq (expGrad u (ξ+iθ))` is integrable on the angular slice
`angularSlice U ξ`: the slice lower-integral is the `ξ`-integrand of a finite total, hence a.e.
finite by Markov, and finiteness of `∫⁻ ofReal` of a nonnegative function is integrability. -/
theorem ae_integrableOn_slice_normSq_of_energy_lt_top {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    {ξ₀ : ℝ} (hDfin : dirichletEnergy u U ≠ ⊤) :
    ∀ᵐ ξ : ℝ ∂(volume.restrict (Iic ξ₀)),
      IntegrableOn (fun θ : ℝ =>
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (angularSlice U ξ) := by
  -- the slice lower-integral is measurable in `ξ` and its `ξ`-integral is finite
  set g : ℝ → ℝ≥0∞ := fun ξ => ∫⁻ θ in Ioo (-π) π,
    (angularSlice U ξ).indicator
      (fun θ' => ENNReal.ofReal
        (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ with hg
  have hWopen : IsOpen {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π ∧
      Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ U} := by
    have hcontmap : Continuous fun p : ℝ × ℝ =>
        Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
    have : {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π ∧
          Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ U}
        = (Prod.snd ⁻¹' Ioo (-π) π) ∩
          ((fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ⁻¹' U) := by
      ext p; simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]; exact (isOpen_Ioo.preimage continuous_snd).inter (hU.preimage hcontmap)
  have hgmeas : Measurable g := by
    refine Measurable.lintegral_prod_right (ν := volume.restrict (Ioo (-π) π)) ?_
    have hjoint : Measurable fun p : ℝ × ℝ =>
        {q : ℝ × ℝ | q.2 ∈ Ioo (-π) π ∧
          Complex.exp ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ U}.indicator
          (fun q : ℝ × ℝ => ENNReal.ofReal
            (Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)))) p :=
      (ENNReal.measurable_ofReal.comp (measurable_normSq_expGrad_logPolar u)).indicator
        hWopen.measurableSet
    have hfeq : (Function.uncurry fun ξ : ℝ => (angularSlice U ξ).indicator
          (fun θ' => ENNReal.ofReal
            (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))))
        = fun p : ℝ × ℝ => {q : ℝ × ℝ | q.2 ∈ Ioo (-π) π ∧
            Complex.exp ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ U}.indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal
              (Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)))) p := by
      funext p
      rw [Function.uncurry_apply_pair]
      by_cases hp : p ∈ {q : ℝ × ℝ | q.2 ∈ Ioo (-π) π ∧
          Complex.exp ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ U}
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p.2 ∈ angularSlice U p.1 from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p.2 ∉ angularSlice U p.1 from hp)]
    rw [hfeq]; exact hjoint
  have hgfin : (∫⁻ ξ in Iic ξ₀, g ξ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hDfin ?_
    rw [(setLIntegral_congr Iio_ae_eq_Iic).symm,
      ← dirichletEnergy_inter_ball_eq_lintegral_slice u hU ξ₀]
    exact dirichletEnergy_mono (fun z hz => hz.1)
  -- Markov: a.e. `ξ` the slice lower-integral is finite, giving slice integrability
  filter_upwards [ae_lt_top hgmeas hgfin] with ξ hξ
  have hsmeas : MeasurableSet (angularSlice U ξ) := (isOpen_angularSlice hU ξ).measurableSet
  have hslicefin : (∫⁻ θ in angularSlice U ξ,
      ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))) ≠ ⊤ := by
    simp only [hg] at hξ
    rw [lintegral_indicator hsmeas, Measure.restrict_restrict hsmeas,
      Set.inter_eq_self_of_subset_left (angularSlice_subset U ξ)] at hξ
    exact hξ.ne
  refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hslicefin
  · exact ((measurable_normSq_expGrad_logPolar u).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun θ => Complex.normSq_nonneg _)

/-- **Lower flux limit along a sequence (discharging `hBot`).** For `u` harmonic on the open set
`U`, suppose the potential admits a boundary modulus `Mbound ξ` dominating `|u|` on every angular
slice with `Mbound → 0` as `ξ → −∞` (the potential vanishing at the origin, `F1`), the slice
radial-derivative and squared gradient are integrable on the slice at each log-radius (`W1c`), and
the tail slice-energy integral `∫⁻_{Iic ξ₀} sliceEnergyU` is finite (`F2`, from `D(u; U) < ∞`).
Then there is a sequence `ξ n → −∞` along which the rough flux tends to `0`: pick the sequence of
the finite tail integral along which the slice energy vanishes, and squeeze the per-slice C.–S.
bound `|roughFlux| ≤ Mbound · √(2π) · √(sliceEnergyU)` by `Mbound → 0` and `sliceEnergyU → 0`. -/
theorem exists_seq_roughFlux_tendsto_zero_atBot {u : ℂ → ℝ} {U : Set ℂ} {Mbound : ℝ → ℝ} {ξ₀ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hMbnn : ∀ ξ, 0 ≤ Mbound ξ)
    (hMb : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ Mbound ξ)
    (hMbtop : Tendsto Mbound atBot (𝓝 0))
    (hReInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hEmeas : Measurable (sliceEnergyU u U))
    (hEfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ)) ≠ ⊤) :
    ∃ ξ : ℕ → ℝ, Tendsto ξ atTop atBot ∧
      Tendsto (fun n => roughFlux u U (ξ n)) atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hEnn : ∀ ξ, 0 ≤ sliceEnergyU u U ξ := fun ξ =>
    setIntegral_nonneg (isOpen_angularSlice hU ξ).measurableSet
      fun θ _ => Complex.normSq_nonneg _
  -- `F2`: the sequence escaping to `−∞` along which the slice energy vanishes
  obtain ⟨ξ, hξle, hξbot, hξE⟩ :=
    exists_seq_tendsto_zero_atBot_of_lintegral_ne_top hEmeas hEnn hEfin
  refine ⟨ξ, hξbot, ?_⟩
  -- the per-slice Cauchy–Schwarz bound, applied along the sequence
  have hbound : ∀ n, |roughFlux u U (ξ n)|
      ≤ Mbound (ξ n) * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n))) := fun n =>
    abs_roughFlux_le_slice hU hu (hMbnn (ξ n)) (hMb (ξ n)) (hReInt (ξ n)) (hEInt (ξ n))
  -- the bounding sequence tends to `0`: `Mbound (ξ n) → 0` and `√(sliceEnergyU (ξ n)) → 0`
  have hMto : Tendsto (fun n => Mbound (ξ n)) atTop (𝓝 0) := hMbtop.comp hξbot
  have hEto : Tendsto (fun n => Real.sqrt (sliceEnergyU u U (ξ n))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hξE
    simpa [Function.comp_def, Real.sqrt_zero] using this
  have hinner : Tendsto (fun n => Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n)))
      atTop (𝓝 (Real.sqrt (2 * π) * 0)) :=
    (tendsto_const_nhds (x := Real.sqrt (2 * π))).mul hEto
  rw [mul_zero] at hinner
  have hprod : Tendsto (fun n =>
      Mbound (ξ n) * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n))))
      atTop (𝓝 (0 * 0)) := hMto.mul hinner
  rw [mul_zero] at hprod
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _) hbound hprod

/-- **Slice integrability of the real part from the squared gradient.** On the finite-measure
angular slice, integrability of `θ ↦ normSq (expGrad u)` implies integrability of
`θ ↦ Re (expGrad u)`: `|Re| ≤ √(normSq)` is dominated by the integrable `(1 + normSq)/2`. -/
theorem integrableOn_slice_re_of_normSq {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (ξ : ℝ)
    (hE : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ)) :
    IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ) := by
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hsfin : volume s ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono (hs ▸ angularSlice_subset U ξ))
  -- `θ ↦ Re (expGrad u)` is continuous on the open slice, hence a.e.-strongly-measurable
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (volume.restrict s) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hsmeas
    intro θ hθ
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hθ.2
    have houter : ContinuousAt (fun w : ℂ => (expGrad u w).re)
        ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      Complex.continuous_re.continuousAt.comp hdC.continuousAt
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    exact (ContinuousAt.comp (g := fun w : ℂ => (expGrad u w).re)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) houter hinner).continuousWithinAt
  refine ((hE.add (integrableOn_const (C := (1 : ℝ)) hsfin (by simp))).const_mul
    (1 / 2)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem hsmeas] with θ _
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [Complex.normSq_apply]
  nlinarith [abs_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re,
    sq_abs (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re,
    sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im,
    sq_nonneg (|(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| - 1)]

/-- **Lower flux limit along a sequence, from a uniform potential bound and finite energy.** For `u`
harmonic on the open set `U` with finite Dirichlet energy, if the potential is uniformly bounded by
a constant `M` on every angular slice, then there is a sequence `ξ n → −∞` along which the rough
flux tends to `0`.  The escaping sequence is chosen — via the co-null null-value selector — at radii
whose slice squared gradient is integrable (a.e. from finite energy) and whose slice energy
vanishes; the per-slice Cauchy–Schwarz bound `|roughFlux| ≤ M · √(2π) · √(sliceEnergyU)` squeezed by
`sliceEnergyU (ξ n) → 0`.  Unlike `exists_seq_roughFlux_tendsto_zero_atBot`, this needs neither
`Mbound → 0` nor slice integrability at every log-radius — only the uniform bound and `D(u; U) < ∞`,
which the keystone data (`0 ≤ u ≤ 1`) supplies directly. -/
theorem exists_seq_roughFlux_tendsto_zero_atBot' {u : ℂ → ℝ} {U : Set ℂ} {M : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hMnn : 0 ≤ M)
    (hbdd : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hDfin : dirichletEnergy u U ≠ ⊤) :
    ∃ ξ : ℕ → ℝ, Tendsto ξ atTop atBot ∧
      Tendsto (fun n => roughFlux u U (ξ n)) atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hEnn : ∀ ξ, 0 ≤ sliceEnergyU u U ξ := fun ξ =>
    setIntegral_nonneg (isOpen_angularSlice hU ξ).measurableSet
      fun θ _ => Complex.normSq_nonneg _
  -- `F2`: the tail slice-energy integral is finite (from `D(u; U) < ∞`)
  have hEfin : (∫⁻ ξ in Iic (0 : ℝ), ENNReal.ofReal (sliceEnergyU u U ξ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (setLIntegral_tail_ofReal_sliceEnergyU_le hU 0)
  -- `W1c` a.e.: the slice squared gradient is integrable at a.e. log-radius below `0`
  have hae : ∀ᵐ ξ : ℝ ∂(volume.restrict (Iic (0 : ℝ))),
      IntegrableOn (fun θ : ℝ =>
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (angularSlice U ξ) :=
    ae_integrableOn_slice_normSq_of_energy_lt_top hU hDfin
  -- pick the escaping sequence at integrable, low-energy log-radii
  obtain ⟨ξ, hξle, hξInt, hξbot, hξE⟩ :=
    exists_seq_tendsto_zero_atBot_of_lintegral_ne_top_ae (measurable_sliceEnergyU hU) hEnn hEfin
      ((ae_restrict_iff' measurableSet_Iic).mp hae)
  refine ⟨ξ, hξbot, ?_⟩
  -- along the sequence, the log-radii lie in `Iic 0`, so the a.e.-selected integrability applies
  have hEInt : ∀ n, IntegrableOn (fun θ : ℝ =>
      Complex.normSq (expGrad u ((ξ n : ℂ) + (θ : ℂ) * Complex.I))) (angularSlice U (ξ n)) :=
    fun n => hξInt n (hξle n)
  have hReInt : ∀ n, IntegrableOn (fun θ : ℝ =>
      (expGrad u ((ξ n : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U (ξ n)) :=
    fun n => integrableOn_slice_re_of_normSq hU hu (ξ n) (hEInt n)
  -- the per-slice Cauchy–Schwarz bound, with the uniform constant `M`
  have hbound : ∀ n, |roughFlux u U (ξ n)|
      ≤ M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n))) := fun n =>
    abs_roughFlux_le_slice hU hu hMnn (hbdd (ξ n)) (hReInt n) (hEInt n)
  -- squeeze: `√(sliceEnergyU (ξ n)) → 0`
  have hEto : Tendsto (fun n => Real.sqrt (sliceEnergyU u U (ξ n))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hξE
    simpa [Function.comp_def, Real.sqrt_zero] using this
  have hinner : Tendsto (fun n => Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n)))
      atTop (𝓝 (Real.sqrt (2 * π) * 0)) :=
    (tendsto_const_nhds (x := Real.sqrt (2 * π))).mul hEto
  rw [mul_zero] at hinner
  have hprod : Tendsto (fun n =>
      M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n)))) atTop (𝓝 (M * 0)) :=
    (tendsto_const_nhds (x := M)).mul hinner
  rw [mul_zero] at hprod
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _) hbound hprod

/-- **The slope is bounded by the total energy (sequential, windowed).** Given the upper flux limit
`hTop`, a sequence `ξ n → −∞` along which the rough flux tends to `0` (`hBotSeq`), and the windowed
increment inequality `roughFlux ζ₂ − roughFlux ζ₁ ≤ D` over the window family `ζ₁ ≤ ζ₂ < 0`, the
boundary slope is bounded by the total energy: fix an inner radius and let the outer radius rise to
`0` to get `b − roughFlux ζ₁ ≤ D`; then let `ζ₁` run along the null sequence to send
`roughFlux ζ₁ → 0`, giving `b ≤ D`.  This is the shape consumable by the keystone `U` (whose small
circles are blocked by the continuum on its frontier, so the full-circle hypothesis of
`slope_le_energy` fails): only the rough windows that genuinely exist are used. -/
theorem slope_le_energy_of_windowed_seq {u : ℂ → ℝ} {U : Set ℂ} {b D : ℝ} {ξ : ℕ → ℝ}
    (hTop : Tendsto (roughFlux u U) (𝓝[<] (0 : ℝ)) (𝓝 b))
    (hBotSeq : Tendsto ξ atTop atBot ∧ Tendsto (fun n => roughFlux u U (ξ n)) atTop (𝓝 0))
    (hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 → roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ D) :
    b ≤ D := by
  obtain ⟨hξbot, hξ0⟩ := hBotSeq
  -- fix an inner radius `ζ₁` and let the outer radius rise to `0`: `b − roughFlux ζ₁ ≤ D`
  have hfix : ∀ ζ₁ : ℝ, ζ₁ < 0 → b - roughFlux u U ζ₁ ≤ D := by
    intro ζ₁ hζ₁
    have hlim : Tendsto (fun ζ₂ : ℝ => roughFlux u U ζ₂ - roughFlux u U ζ₁)
        (𝓝[<] (0 : ℝ)) (𝓝 (b - roughFlux u U ζ₁)) := hTop.sub_const _
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hζ₁, self_mem_nhdsWithin] with ζ₂ hζ₂mem hζ₂neg
    exact hwin ζ₁ ζ₂ hζ₂mem.1.le hζ₂neg
  -- run `ζ₁` along the null sequence `ξ n → −∞`: `roughFlux (ξ n) → 0`, giving `b ≤ D`
  have hlim2 : Tendsto (fun n : ℕ => b - roughFlux u U (ξ n)) atTop (𝓝 (b - 0)) :=
    hξ0.const_sub b
  rw [sub_zero] at hlim2
  refine le_of_tendsto hlim2 ?_
  have hev : ∀ᶠ n in atTop, ξ n < 0 := hξbot.eventually (eventually_lt_atBot 0)
  filter_upwards [hev] with n hn
  exact hfix (ξ n) hn

/-- **Keystone slope bound for a ring potential.** Assemble the discharged flux limits into the
final consumable slope inequality `b ≤ D(u; U)`.  From the collar full-circle mapping and
ring-potential data the upper flux limit `hTop` is `roughFlux_tendsto_slope_ringPotential`; from the
boundary modulus (`F1`), the a.e.-slice integrabilities (`W1c`), and the finite tail slice-energy
integral (`F2`) the null-sequence flux limit is `exists_seq_roughFlux_tendsto_zero_atBot`; the
windowed increment inequality `hwin` — the rough-window flux–energy content over the window family
that genuinely exists for the keystone `U` — is supplied as a hypothesis, and
`slope_le_energy_of_windowed_seq` combines them. -/
theorem slope_le_energy_ringPotential {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ} {Mbound : ℝ → ℝ} {ξ₀ : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hMbnn : ∀ ξ, 0 ≤ Mbound ξ)
    (hMb : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ Mbound ξ)
    (hMbtop : Tendsto Mbound atBot (𝓝 0))
    (hReInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hEmeas : Measurable (sliceEnergyU u U))
    (hEfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ)) ≠ ⊤)
    (hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal) :
    b ≤ (dirichletEnergy u U).toReal := by
  have hTop := roughFlux_tendsto_slope_ringPotential h0 h1 hcollar hucollar hcont hone hrange hslope
  have hBotSeq := exists_seq_roughFlux_tendsto_zero_atBot hU hu hMbnn hMb hMbtop hReInt hEInt
    hEmeas hEfin
  obtain ⟨ξ, hξbot, hξ0⟩ := hBotSeq
  exact slope_le_energy_of_windowed_seq (ξ := ξ) hTop ⟨hξbot, hξ0⟩ hwin

/-- **Keystone slope bound for a ring potential (self-contained flux limits).** The keystone-shaped
version of `slope_le_energy_ringPotential`: from the collar full-circle mapping and ring-potential
data (giving the upper flux limit `hTop`), the uniform bound `0 ≤ u ≤ 1` on `U`, and finite
Dirichlet energy `D(u; U) < ∞`, the boundary slope is bounded by the total energy `b ≤ D(u; U)`.

All the auxiliary hypotheses of `slope_le_energy_ringPotential` are discharged here:
* the lower flux limit is `exists_seq_roughFlux_tendsto_zero_atBot'`, which needs only the uniform
  potential bound and `D(u; U) < ∞` — measurability of `sliceEnergyU`
  (`measurable_sliceEnergyU`), the finite tail slice-energy integral
  (`setLIntegral_tail_ofReal_sliceEnergyU_le`), and a.e. slice integrability of the squared
  gradient (`ae_integrableOn_slice_normSq_of_energy_lt_top`, threaded into the sequence) are
  internal;
* the windowed increment inequality `hwin` — the rough-window flux–energy content over the window
  family that genuinely exists for the keystone `U` — remains a hypothesis (its discharge is the
  varying-domain radial flux–energy exchange, not available for the keystone `U` whose small circles
  are blocked by the continuum on its frontier). -/
theorem slope_le_energy_ringPotential' {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hDfin : dirichletEnergy u U ≠ ⊤)
    (hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal) :
    b ≤ (dirichletEnergy u U).toReal := by
  have hTop := roughFlux_tendsto_slope_ringPotential h0 h1 hcollar hucollar hcont hone hrange hslope
  -- the uniform slice bound `|u| ≤ 1` from `0 ≤ u ≤ 1` on `U`
  have hbdd : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
    intro ξ θ hθ
    obtain ⟨hnn, hle⟩ := hrangeU _ hθ.2
    rw [abs_of_nonneg hnn]; exact hle
  obtain ⟨ξ, hξbot, hξ0⟩ :=
    exists_seq_roughFlux_tendsto_zero_atBot' hU hu (by norm_num : (0:ℝ) ≤ 1) hbdd hDfin
  exact slope_le_energy_of_windowed_seq (ξ := ξ) hTop ⟨hξbot, hξ0⟩ hwin

/-! ### The windowed increment inequality from the level-set exhaustion

The windowed increment inequality `hwin` — `roughFlux ζ₂ − roughFlux ζ₁ ≤ D(u; U)` for
`ζ₁ ≤ ζ₂ < 0` — is produced from the **level-set exhaustion**: writing `roughFluxδ u U δ`
(= the rough flux of the superlevel set `V_δ = {u > δ} ∩ U`, `roughFluxδ_eq_roughFlux_superLevelU`)
and letting `δ ↓ 0`, the rough flux is recovered (`tendsto_roughFluxδ_atZero`).  It therefore
suffices to bound the δ-increment `roughFluxδ ζ₂ − roughFluxδ ζ₁ ≤ D(u; U)` uniformly in `δ > 0`;
this is the per-level flux–energy content of the superlevel set (whose closure meets `U` compactly
inside any window `{e^{ζ₁} < |z| < e^{ζ₂}}`, `ζ₂ < 0`, so all slab bounds apply). -/

/-- **The windowed increment inequality from the level-set δ-increment bound.** For `u` harmonic and
strictly positive on the open set `U`, uniformly bounded by `1` on `U`, with the slice
radial-derivative integrand integrable on every slice, if for every window `ζ₁ ≤ ζ₂ < 0` and every
`δ > 0` the level-set δ-rough-flux increment is bounded by `D(u; U)`, then the rough-flux increment
is bounded by `D(u; U)` on every such window.  This packages the `δ → 0` recovery of the rough flux
into the windowed increment inequality `hwin` consumed by `slope_le_energy_ringPotential'`. -/
theorem roughFlux_sub_le_dirichletEnergy_rough {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hδwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 → ∀ δ : ℝ, 0 < δ →
      roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ (dirichletEnergy u U).toReal) :
    ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
  intro ζ₁ ζ₂ h12 hζ₂
  -- the uniform `|u| ≤ 1` slice bound
  have hbdd : ∀ ξ : ℝ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
    intro ξ θ hθ
    obtain ⟨hnn, hle⟩ := hrangeU _ hθ.2
    rw [abs_of_nonneg hnn]; exact hle
  -- slice radial-derivative integrand integrable at each of the two log-radii
  have hRe : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ) :=
    fun ξ => integrableOn_slice_re_of_normSq hU hu ξ (hEInt ξ)
  exact roughFlux_sub_le_of_roughFluxδ_sub_le hU hu hpos (by norm_num : (0:ℝ) ≤ 1)
    (hbdd ζ₁) (hbdd ζ₂) (hRe ζ₁) (hRe ζ₂) (hδwin ζ₁ ζ₂ h12 hζ₂)

/-- **Keystone slope bound for a ring potential (level-set δ-increment residual).** The
`slope_le_energy_ringPotential'` slope bound `b ≤ D(u; U)`, with the windowed increment hypothesis
`hwin` eliminated in favour of the strictly more local **level-set δ-increment bound** `hδwin`:
the flux–energy content of each superlevel set `{u > δ} ∩ U` (whose closure sits compactly inside
`U` on any window `{e^{ζ₁} < |z| < e^{ζ₂}}`, `ζ₂ < 0`).  The `δ → 0` recovery
(`roughFlux_sub_le_dirichletEnergy_rough`) turns `hδwin` into `hwin`. -/
theorem slope_le_energy_ringPotential'' {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤)
    (hδwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 → ∀ δ : ℝ, 0 < δ →
      roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ (dirichletEnergy u U).toReal) :
    b ≤ (dirichletEnergy u U).toReal :=
  slope_le_energy_ringPotential' h0 h1 hU hu hcollar hucollar hcont hone hrange hslope hrangeU hDfin
    (roughFlux_sub_le_dirichletEnergy_rough hU hu hpos hrangeU hEInt hδwin)

/-! ### The truncated per-arc integration-by-parts identity for a superlevel arc

On a single angular arc `(a, b)` of the superlevel slice `V_δ ∩ C_{e^ξ}` — whose interior maps
into `{u > δ} ∩ U`, so `u > δ` throughout the open arc, and whose endpoints escape the superlevel
set, where `u = δ` — the truncated potential `(u − δ)⁺` vanishes at both endpoints and equals
`u − δ` on the interior.  The two sequential boundary bricks therefore annihilate the
integration-by-parts boundary term, giving the exact per-arc identity
`∫_a^b (u − δ)⁺ · Re (deriv (expGrad u)) = ∫_a^b (Im (expGrad u))²`. -/

/-- **Truncated per-arc flux identity.** For `u` harmonic on an open set `U`, a log-radius `ξ` and a
closed arc `[a, b]` whose interior maps under `θ ↦ e^{ξ+θi}` into `U` with `δ < u` throughout, and
whose endpoints map to superlevel-boundary points where `u = δ`, with the slice squared gradient and
slice radial-derivative integrand integrable, the angle integral over the arc of
`(u(e^{ξ+θi}) − δ)⁺ · Re (deriv (expGrad u))` equals the integral of `(Im (expGrad u))²`.  The
truncation `(u − δ)⁺` vanishes at both endpoints, so the two sequential boundary bricks kill the
integration-by-parts boundary term exactly as in `integral_uexp_re_deriv_expGrad_arc`. -/
theorem integral_posPart_re_deriv_expGrad_arc {u : ℂ → ℝ} {U : Set ℂ} {δ ξ a b : ℝ}
    (hU : IsOpen U) (hab : a < b)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (harc : ∀ θ ∈ Ioo a b, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hsup : ∀ θ ∈ Ioo a b, δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
    (hcont : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc a b))
    (hslice : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo a b))
    (hg'int : IntegrableOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b))
    (ha0 : u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I)) = δ)
    (hb0 : u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I)) = δ) :
    ∫ θ in a..b, (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  set uexp : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with huexp
  set f : ℝ → ℝ := fun θ => (uexp θ - δ)⁺ with hf
  set g : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgdef
  set g' : ℝ → ℝ :=
    fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hg'def
  -- differentiability on the open arc
  have hdiffR : ∀ θ ∈ Ioo a b,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ hθ =>
    differentiableAt_of_harmonicOnNhd hu (harc θ hθ)
  have hdiffC : ∀ θ ∈ Ioo a b,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ hθ =>
    expGrad_differentiableAt_open hU hu (harc θ hθ)
  -- `uexp` is continuous on the open arc, and on the interior `f = uexp - δ` (since `uexp > δ`)
  have huexpcont : ContinuousOn uexp (Ioo a b) := (hcont.mono Ioo_subset_Icc_self)
  -- `f = (uexp - δ)⁺` has, on the open arc, derivative `-Im (expGrad u)` (`= deriv uexp`)
  have hfderiv : ∀ θ ∈ Ioo a b, HasDerivAt f (deriv f θ) θ := by
    intro θ hθ
    -- near `θ`, `uexp > δ`, so `f =ᶠ uexp - δ` and shares its derivative
    have hgtθ : δ < uexp θ := hsup θ hθ
    have hnhd : ∀ᶠ t in nhds θ, δ < uexp t := by
      have hcθ : ContinuousAt uexp θ :=
        (huexpcont.continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
      exact hcθ.eventually_const_lt hgtθ
    have hnhdsub : ∀ᶠ t in nhds θ, t ∈ Ioo a b := Ioo_mem_nhds hθ.1 hθ.2
    have hfeq : f =ᶠ[nhds θ] fun t => uexp t - δ := by
      filter_upwards [hnhd] with t ht
      rw [hf]; simp only [posPart_eq_self.mpr (by linarith : (0:ℝ) ≤ uexp t - δ)]
    have huderiv : HasDerivAt uexp (-(g θ)) θ := hasDerivAt_uexp_angular (hdiffR θ hθ)
    have hshift : HasDerivAt (fun t => uexp t - δ) (-(g θ)) θ := by
      simpa using huderiv.sub_const δ
    have hfd : HasDerivAt f (-(g θ)) θ := hshift.congr_of_eventuallyEq hfeq
    rw [hfd.deriv]; exact hfd
  have hfg : ∀ θ ∈ Ioo a b, deriv f θ = -g θ := by
    intro θ hθ
    have hgtθ : δ < uexp θ := hsup θ hθ
    have hnhd : ∀ᶠ t in nhds θ, δ < uexp t := by
      have hcθ : ContinuousAt uexp θ := (huexpcont.continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
      exact hcθ.eventually_const_lt hgtθ
    have hfeq : f =ᶠ[nhds θ] fun t => uexp t - δ := by
      filter_upwards [hnhd] with t ht
      rw [hf]; simp only [posPart_eq_self.mpr (by linarith : (0:ℝ) ≤ uexp t - δ)]
    have huderiv : HasDerivAt uexp (-(g θ)) θ := hasDerivAt_uexp_angular (hdiffR θ hθ)
    have hshift : HasDerivAt (fun t => uexp t - δ) (-(g θ)) θ := by
      simpa using huderiv.sub_const δ
    exact (hshift.congr_of_eventuallyEq hfeq).deriv
  have hgderiv : ∀ θ ∈ Ioo a b, HasDerivAt g (g' θ) θ := by
    intro θ hθ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ hθ)
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [hgdef, hg'def, Function.comp, Complex.mul_im] using hcomp
  have hgcont : ContinuousOn g (Ioo a b) := fun θ hθ =>
    (hgderiv θ hθ).continuousAt.continuousWithinAt
  -- `(deriv f)² = g² ≤ normSq (expGrad u)` gives square-integrability of `deriv f`
  have hf2 : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Ioo a b) := by
    have hg2meas : AEStronglyMeasurable (fun θ => (deriv f θ) ^ 2)
        (volume.restrict (Ioo a b)) := by
      refine ((hgcont.aestronglyMeasurable measurableSet_Ioo).pow 2).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hfg θ hθ]; simp [hgdef]
    refine Integrable.mono' hslice hg2meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [hfg θ hθ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        ≤ Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [Complex.normSq_apply]; nlinarith [sq_nonneg
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
    simpa [hgdef] using this
  have hg2int : IntegrableOn (fun θ => (g θ) ^ 2) (Ioo a b) :=
    hf2.congr_fun (fun θ hθ => by rw [hfg θ hθ]; simp [hgdef]) measurableSet_Ioo
  have hgint : IntegrableOn g (Ioo a b) := by
    have hvol : volume (Ioo a b) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2) (Ioo a b) :=
      integrableOn_const hvol (by simp)
    have hsum : IntegrableOn (fun θ => (1 : ℝ) / 2 + (g θ) ^ 2 / 2) (Ioo a b) :=
      hconst.add (hg2int.div_const 2)
    have hdom : IntegrableOn (fun θ => (1 + (g θ) ^ 2) / 2) (Ioo a b) :=
      hsum.congr_fun (fun θ _ => by ring) measurableSet_Ioo
    refine hdom.mono' (hgcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|g θ| - 1), abs_nonneg (g θ), sq_abs (g θ)]
  -- `f` is continuous on the closed arc (composition of the Lipschitz `posPart` with `uexp - δ`)
  have hfcont : ContinuousOn f (Icc a b) := by
    have : ContinuousOn (fun θ => uexp θ - δ) (Icc a b) := hcont.sub continuousOn_const
    exact (lipschitzWith_posPart.continuous.comp_continuousOn this)
  -- endpoint vanishing: `uexp = δ` there, so `(uexp - δ)⁺ = 0`
  have hfa : f a = 0 := by
    rw [hf]; simp only [huexp, ha0, sub_self, posPart_zero]
  have hfb : f b = 0 := by
    rw [hf]; simp only [huexp, hb0, sub_self, posPart_zero]
  exact integral_mul_deriv_eq_integral_sq_of_endpoints_zero hab hfderiv hfg hgderiv hf2
    hfcont hgint hg'int hfa hfb

/-- **Window-general summed truncated per-slice flux identity.** Fix a log-radius `ξ`, a level `δ`,
and a window `(lo, hi)`.  On the windowed superlevel slice
`O = {θ ∈ (lo, hi) | e^{ξ+θi} ∈ U ∧ u > δ}` — with `u` harmonic on `U`, continuous on the closure of
the slice, `u = δ` at every circle boundary point of the superlevel set, the window seams `lo`, `hi`
escaping the superlevel set, and the slice squared gradient and slice radial-derivative integrand
integrable — the angle integral over the slice of
`(u − δ)⁺ · Re (deriv (expGrad u))` equals the integral of `(Im (expGrad u))²`: decompose `O` into
its countable disjoint open arcs (each with endpoints where `u = δ`) and sum the exact truncated
per-arc identities. -/
theorem setIntegral_windowSlice_posPart_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {δ ξ lo hi : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcont : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (closure {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}))
    (hEsc : ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ closure (superLevelU U u δ) →
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∉ superLevelU U u δ →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ)
    (hloOut : Complex.exp ((ξ : ℂ) + (lo : ℂ) * Complex.I) ∉ superLevelU U u δ)
    (hhiOut : Complex.exp ((ξ : ℂ) + (hi : ℂ) * Complex.I) ∉ superLevelU U u δ)
    (hsliceInt : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ})
    (hradInt : IntegrableOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}) :
    ∫ θ in {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ},
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ},
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  classical
  set O : Set ℝ := {θ' : ℝ | θ' ∈ Ioo lo hi ∧
    Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} with hO
  have hOopen : IsOpen O := by
    have h1 : IsOpen (Ioo lo hi) := isOpen_Ioo
    have h2 : IsOpen {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} :=
      (isOpen_superLevelU hU hu δ).preimage (by fun_prop)
    exact h1.inter h2
  have hOsub : O ⊆ Ioo lo hi := fun _ hθ => hθ.1
  obtain ⟨S, hcount, hdisj, hunion, hSend⟩ := isOpen_eq_iUnion_Ioo hOopen hOsub
  have _ := hcount.to_subtype
  set F : ℝ → ℝ := fun θ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
      * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 with hG
  set s : S → Set ℝ := fun p => Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hs
  have hsu : O = ⋃ p : S, s p := by rw [hunion, hs, iUnion_subtype]
  have hsmeas : ∀ p : S, MeasurableSet (s p) := fun _ => measurableSet_Ioo
  have hsdisj : Pairwise (Function.onFun Disjoint s) := fun p q hpq =>
    hdisj p.2 q.2 (fun h => hpq (Subtype.ext h))
  have harcmem : ∀ p : S, ∀ θ ∈ s p, θ ∈ O := fun p θ hθ => hsu ▸ mem_iUnion.mpr ⟨p, hθ⟩
  have harcU : ∀ p : S, ∀ θ ∈ s p, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := fun p θ hθ =>
    (harcmem p θ hθ).2.1
  have harcSup : ∀ p : S, ∀ θ ∈ s p,
      δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun p θ hθ => (harcmem p θ hθ).2.2
  -- each arc's closed interval lies in the closure of `O` (interior in `O`, endpoints are limits)
  have harcIcc : ∀ p : S, (p : ℝ × ℝ).1 < (p : ℝ × ℝ).2 →
      Icc (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 ⊆ closure O := by
    intro p hlt
    have hIooO : Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 ⊆ O := fun θ hθ => harcmem p θ hθ
    calc Icc (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 = closure (Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2) := by
          rw [closure_Ioo hlt.ne]
      _ ⊆ closure O := closure_mono hIooO
  -- membership of the exponential in the superlevel set as a set on the circle
  have hmemexp : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by fun_prop
  have hper : ∀ p : S, ∫ θ in s p, F θ = ∫ θ in s p, G θ := by
    intro p
    rcases lt_or_ge (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hlt | hle
    · obtain ⟨hn1, hn2, hlo, hhi⟩ := hSend p p.2
      -- both endpoints are in `closure (super)` (limits of arc-interior super points)
      set p1 : ℝ := (p : ℝ × ℝ).1 with hp1
      set p2 : ℝ := (p : ℝ × ℝ).2 with hp2
      have hseq1 : Filter.Tendsto (fun n : ℕ => p1 + 1 / (n + 2 : ℝ) * (p2 - p1))
          Filter.atTop (nhds p1) := by
        have h0 : Filter.Tendsto (fun n : ℕ => p1 + 1 / (n + 2 : ℝ) * (p2 - p1))
            Filter.atTop (nhds (p1 + 0 * (p2 - p1))) :=
          Filter.Tendsto.const_add _ (Filter.Tendsto.mul_const _
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
              |>.congr (fun n => by simp only [Function.comp_apply]; push_cast; ring)))
        simpa using h0
      have hseq2 : Filter.Tendsto (fun n : ℕ => p2 - 1 / (n + 2 : ℝ) * (p2 - p1))
          Filter.atTop (nhds p2) := by
        have h0 : Filter.Tendsto (fun n : ℕ => p2 - 1 / (n + 2 : ℝ) * (p2 - p1))
            Filter.atTop (nhds (p2 - 0 * (p2 - p1))) :=
          Filter.Tendsto.const_sub _ (Filter.Tendsto.mul_const _
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
              |>.congr (fun n => by simp only [Function.comp_apply]; push_cast; ring)))
        simpa using h0
      have hnbelow : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 2 : ℝ) ∧ 1 / (n + 2 : ℝ) < 1 := by
        intro n
        refine ⟨by positivity, ?_⟩
        rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hclos1 : Complex.exp ((ξ : ℂ) + (p1 : ℂ) * Complex.I)
          ∈ closure (superLevelU U u δ) :=
        mem_closure_of_tendsto (hmemexp.continuousAt.tendsto.comp hseq1)
          (Filter.Eventually.of_forall fun n => (harcmem p _
            (Set.mem_Ioo.mpr ⟨by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2],
             by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2]⟩)).2)
      have hclos2 : Complex.exp ((ξ : ℂ) + (p2 : ℂ) * Complex.I)
          ∈ closure (superLevelU U u δ) :=
        mem_closure_of_tendsto (hmemexp.continuousAt.tendsto.comp hseq2)
          (Filter.Eventually.of_forall fun n => (harcmem p _
            (Set.mem_Ioo.mpr ⟨by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2],
             by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2]⟩)).2)
      have hnot1 : Complex.exp ((ξ : ℂ) + (p1 : ℂ) * Complex.I)
          ∉ superLevelU U u δ := by
        rcases eq_or_lt_of_le hlo with heq | hlt'
        · rw [← heq]; exact hloOut
        · intro hsup; exact hn1 ⟨⟨hlt', lt_of_lt_of_le hlt hhi⟩, hsup⟩
      have hnot2 : Complex.exp ((ξ : ℂ) + (p2 : ℂ) * Complex.I)
          ∉ superLevelU U u δ := by
        rcases eq_or_lt_of_le hhi with heq | hlt'
        · rw [heq]; exact hhiOut
        · intro hsup; exact hn2 ⟨⟨lt_of_le_of_lt hlo hlt, hlt'⟩, hsup⟩
      have hEnd1 : u (Complex.exp ((ξ : ℂ) + ((p : ℝ × ℝ).1 : ℂ) * Complex.I)) = δ :=
        hEsc _ hclos1 hnot1
      have hEnd2 : u (Complex.exp ((ξ : ℂ) + ((p : ℝ × ℝ).2 : ℂ) * Complex.I)) = δ :=
        hEsc _ hclos2 hnot2
      have hid := integral_posPart_re_deriv_expGrad_arc hU hlt hu (fun θ hθ => harcU p θ hθ)
        (fun θ hθ => harcSup p θ hθ) (hcont.mono (harcIcc p hlt))
        (hsliceInt.mono_set (harcmem p)) (hradInt.mono_set (harcmem p))
        hEnd1 hEnd2
      rw [hF, hG, hs]
      rw [intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo] at hid
      exact hid
    · rw [hs]; simp only [Ioo_eq_empty (not_lt.mpr hle), setIntegral_empty]
  have hOmeas : MeasurableSet O := hOopen.measurableSet
  have hOclosCpt : IsCompact (closure O) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      ((Metric.isBounded_Ioo lo hi).subset hOsub).closure
  have hcontO : ContinuousOn (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) O :=
    hcont.mono subset_closure
  have hFint : IntegrableOn F O := by
    obtain ⟨C, hC⟩ := (hOclosCpt.exists_bound_of_continuousOn
      (lipschitzWith_posPart.continuous.comp_continuousOn (hcont.sub continuousOn_const)))
    refine Integrable.mono' (hradInt.norm.const_mul C) ?_ ?_
    · exact ((lipschitzWith_posPart.continuous.comp_continuousOn
        (hcontO.sub continuousOn_const)).aestronglyMeasurable hOmeas).mul
        hradInt.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hOmeas] with θ hθ
      rw [hF, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hC _ (subset_closure hθ)) (norm_nonneg _)
  have hexpGradO : ContinuousOn
      (fun θ : ℝ => expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) O := by
    intro θ hθ
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hθ.2.1
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    exact (ContinuousAt.comp (g := expGrad u)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hdC.continuousAt
      hinner).continuousWithinAt
  have hGint : IntegrableOn G O := by
    refine Integrable.mono' hsliceInt ?_ ?_
    · exact ((Complex.continuous_im.comp_continuousOn hexpGradO).pow 2).aestronglyMeasurable hOmeas
    · filter_upwards [ae_restrict_mem hOmeas] with θ _
      rw [hG, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.normSq_apply]
      nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
  rw [hsu, integral_iUnion hsmeas hsdisj (hsu ▸ hFint),
    integral_iUnion hsmeas hsdisj (hsu ▸ hGint)]
  exact tsum_congr hper

/-- **Full-circle truncated angular integration by parts.** Fix a log-radius `ξ` and level `δ`.
If the *whole* circle at log-radius `ξ` lies in `U` and `u > δ` everywhere on it, then the
truncation `(u − δ)⁺` coincides with the smooth `u − δ` on the circle, and the periodic angular
integration by parts (with `±π` boundary terms cancelling by `2π`-periodicity) gives
`∫_{(−π,π)} (u − δ)⁺ · Re (deriv (expGrad u)) = ∫_{(−π,π)} (Im (expGrad u))²`. -/
theorem integral_full_posPart_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {δ ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hfull : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hsup : ∀ θ : ℝ, δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :
    ∫ θ in Ioo (-π) π,
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  -- on the whole circle the truncation is smooth: `(u − δ)⁺ = u − δ`
  have hpos : ∀ θ : ℝ, (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
      = u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ := fun θ =>
    posPart_eq_self.mpr (by linarith [hsup θ])
  -- rewrite the truncation factor to `u − δ`
  have hinteq : ∫ θ in Ioo (-π) π,
      (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in Ioo (-π) π,
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by rw [hpos θ])
  rw [hinteq]
  set f : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ with hf
  set g : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgdef
  set g' : ℝ → ℝ :=
    fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hg'def
  have hdiffR : ∀ θ : ℝ,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ =>
    differentiableAt_of_harmonicOnNhd hu (hfull θ)
  have hdiffC : ∀ θ : ℝ,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ =>
    expGrad_differentiableAt_open hU hu (hfull θ)
  -- `f` and `g` are continuous, and `f' = -g`, `g' = Re (deriv expGrad)`
  have hcont_f : Continuous f := by
    refine continuous_iff_continuousAt.mpr (fun θ => ?_)
    exact ((hasDerivAt_uexp_angular (hdiffR θ)).continuousAt.sub continuousAt_const)
  have hgderiv : ∀ θ : ℝ, HasDerivAt g (g' θ) θ := by
    intro θ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ)
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [hgdef, hg'def, Function.comp, Complex.mul_im] using hcomp
  have hcont_g : Continuous g :=
    continuous_iff_continuousAt.mpr (fun θ => (hgderiv θ).continuousAt)
  -- `deriv (expGrad u)` is continuous on the open preimage `O = exp ⁻¹' U`, which the circle enters
  have hOcont : ContinuousOn (deriv (expGrad u)) (Complex.exp ⁻¹' U) := by
    set O : Set ℂ := Complex.exp ⁻¹' U with hO
    have hOopen : IsOpen O := hU.preimage Complex.continuous_exp
    have hdiff : DifferentiableOn ℂ (expGrad u) O := fun w hw =>
      (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
    exact ((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn
  have hcont_g' : Continuous g' := by
    refine continuous_iff_continuousAt.mpr (fun θ => ?_)
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hfull θ
    have hOopen : IsOpen (Complex.exp ⁻¹' U) := hU.preimage Complex.continuous_exp
    have hderivC : ContinuousAt (deriv (expGrad u)) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      (hOcont.continuousAt (hOopen.mem_nhds hmemO))
    have hcomp : ContinuousAt
        (fun t : ℝ => deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := deriv (expGrad u))
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hderivC hinner
    exact Complex.continuous_re.continuousAt.comp hcomp
  have hf' : ∀ θ ∈ Ioo (min (-π) π) (max (-π) π), HasDerivAt f (-(g θ)) θ := fun θ _ => by
    simpa [hf, hgdef] using (hasDerivAt_uexp_angular (hdiffR θ)).sub_const δ
  have hg'' : ∀ θ ∈ Ioo (min (-π) π) (max (-π) π), HasDerivAt g (g' θ) θ := fun θ _ => hgderiv θ
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f.continuousOn hcont_g.continuousOn hf' hg''
    (hcont_g.neg.intervalIntegrable _ _) (hcont_g'.intervalIntegrable _ _)
  have halg : ∫ θ in (-π)..π, (-(g θ)) * g θ = - ∫ θ in (-π)..π, (g θ) ^ 2 := by
    rw [show (fun θ : ℝ => (-(g θ)) * g θ) = fun θ : ℝ => -((g θ) ^ 2) from
      funext fun θ => by ring, intervalIntegral.integral_neg]
  -- boundary terms cancel by `2π`-periodicity
  have hexp : Complex.exp ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    rw [show ((ξ : ℂ) + (π : ℂ) * Complex.I)
        = ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  have hfper : f π = f (-π) := by simp only [hf]; rw [show ((π : ℝ) : ℂ) = ((π : ℝ) : ℂ) from rfl,
    hexp]
  have hgper : g π = g (-π) := by
    simp only [hgdef, expGrad]; rw [show ((π : ℝ) : ℂ) = ((π : ℝ) : ℂ) from rfl, hexp]
  rw [integral_Ioo_eq_intervalIntegral hπ, integral_Ioo_eq_intervalIntegral hπ, hIBP, halg,
    hfper, hgper]
  ring

/-- **Branch-cut-free truncated angular integration by parts.** Fix a log-radius `ξ` and level `δ`.
On the standard superlevel slice `angularSliceδ U u δ ξ = {θ ∈ (−π, π) | e^{ξ+θi} ∈ U ∧ u > δ}`,
with `u` harmonic on `U`, continuous on the closure of the slice, `u = δ` at every circle boundary
point of the superlevel set, and the slice squared gradient and slice radial-derivative integrand
integrable, the angle integral over the slice of `(u − δ)⁺ · Re (deriv (expGrad u))` equals the
integral of `(Im (expGrad u))²`.  Unlike the arc decomposition, this handles the case where the
superlevel set straddles the `±π` branch cut: if the whole circle is superlevel, the periodic
angular IBP applies (`integral_full_posPart_re_deriv_expGrad`); otherwise a rotation to a window
`(α, α+2π)` whose seam `α` escapes the superlevel set makes the arc decomposition valid
(`setIntegral_windowSlice_posPart_re_deriv_expGrad`), and the `2π`-periodicity of the integrands
transfers the identity back to the standard chart. -/
theorem setIntegral_slice_posPart_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {δ ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcontR : Continuous
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEsc : ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ closure (superLevelU U u δ) →
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∉ superLevelU U u δ →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ)
    (hbdd : ∃ C : ℝ, ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ →
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≤ C
      ∧ |(deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ C) :
    ∫ θ in angularSliceδ U u δ ξ,
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in angularSliceδ U u δ ξ,
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  classical
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  set V : Set ℂ := superLevelU U u δ with hVdef
  have hVopen : IsOpen V := isOpen_superLevelU hU hu δ
  set F : ℝ → ℝ := fun θ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
      * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 with hG
  set P : Set ℝ := {θ : ℝ | Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ V} with hP
  have hPmeas : MeasurableSet P := (hVopen.preimage (by fun_prop)).measurableSet
  -- both integrands, cut by the superlevel indicator, are `2π`-periodic in the angle
  have hexpper : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    intro θ
    rw [show ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
        = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  have hloctwo : ∀ θ : ℝ, ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
    intro θ; push_cast; ring
  have hEGper : ∀ θ : ℝ, expGrad u ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    intro θ; simp only [expGrad, hexpper θ]
  -- `expGrad u` is `2π·I`-periodic on `ℂ`, hence so is its derivative
  have hExp2πI : Complex.exp (2 * (π : ℂ) * Complex.I) = 1 := by
    rw [show (2 * (π : ℂ) * Complex.I) = 2 * ↑π * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  have hEGperC : Function.Periodic (expGrad u) (2 * (π : ℂ) * Complex.I) := by
    intro w
    simp only [expGrad]
    rw [show w + 2 * (π : ℂ) * Complex.I = w + 2 * π * Complex.I by ring, Complex.exp_add,
      show Complex.exp (2 * ↑π * Complex.I) = 1 from hExp2πI, mul_one]
  have hshiftfun : (fun x : ℂ => expGrad u (x + 2 * (π : ℂ) * Complex.I)) = expGrad u :=
    funext fun x => hEGperC x
  have hDEGper : ∀ θ : ℝ, deriv (expGrad u) ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    intro θ
    rw [hloctwo θ, ← deriv_comp_add_const (expGrad u) (2 * (π : ℂ) * Complex.I), hshiftfun]
  have hPper : Function.Periodic (P.indicator F) (2 * π) := by
    intro θ
    simp only [hP, Set.indicator_apply, hF, mem_setOf_eq, hexpper θ, hDEGper θ]
  have hQper : Function.Periodic (P.indicator G) (2 * π) := by
    intro θ
    simp only [hP, Set.indicator_apply, hG, mem_setOf_eq, hexpper θ, hEGper θ]
  -- `angularSliceδ = Ioo(-π)π ∩ P`, so its set integral is the indicator interval integral
  have hslicedef : angularSliceδ U u δ ξ = Ioo (-π) π ∩ P := by
    ext θ; simp only [angularSliceδ, hP, mem_inter_iff, mem_setOf_eq]; tauto
  have hindF : (∫ θ in angularSliceδ U u δ ξ, F θ) = ∫ θ in (-π)..π, P.indicator F θ := by
    rw [hslicedef, ← setIntegral_indicator hPmeas,
      ← integral_Ioo_eq_intervalIntegral hπ]
  have hindG : (∫ θ in angularSliceδ U u δ ξ, G θ) = ∫ θ in (-π)..π, P.indicator G θ := by
    rw [hslicedef, ← setIntegral_indicator hPmeas,
      ← integral_Ioo_eq_intervalIntegral hπ]
  -- integrands are continuous on the open slice and bounded on `V`, hence integrable on any
  -- bounded window slice
  obtain ⟨C, hC⟩ := hbdd
  have hwinInt : ∀ a b : ℝ,
      IntegrableOn (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        {θ' : ℝ | θ' ∈ Ioo a b ∧ Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V}
      ∧ IntegrableOn (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        {θ' : ℝ | θ' ∈ Ioo a b ∧ Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} := by
    intro a b
    set W : Set ℝ := {θ' : ℝ | θ' ∈ Ioo a b ∧
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} with hW
    have hWopen : IsOpen W := isOpen_Ioo.inter (hVopen.preimage (by fun_prop))
    have hWmeas : MeasurableSet W := hWopen.measurableSet
    have hWbdd : volume W ≠ ⊤ := by
      refine (measure_mono (fun θ hθ => hθ.1)).trans_lt ?_ |>.ne
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hDEGcont : ContinuousOn (deriv (expGrad u)) (Complex.exp ⁻¹' U) := by
      have hOopen : IsOpen (Complex.exp ⁻¹' U) := hU.preimage Complex.continuous_exp
      have hdiff : DifferentiableOn ℂ (expGrad u) (Complex.exp ⁻¹' U) := fun w hw =>
        (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
      exact ((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn
    have hEGmeas : AEStronglyMeasurable
        (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (volume.restrict W) := by
      refine (ContinuousOn.aestronglyMeasurable ?_ hWmeas)
      intro θ hθ
      have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
        expGrad_differentiableAt_open hU hu hθ.2.1
      have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
      have hcomp : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
        ContinuousAt.comp (g := expGrad u)
          (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hdC.continuousAt hinner
      exact (Complex.continuous_normSq.continuousAt.comp hcomp).continuousWithinAt
    have hRDmeas : AEStronglyMeasurable
        (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        (volume.restrict W) := by
      refine (ContinuousOn.aestronglyMeasurable ?_ hWmeas)
      intro θ hθ
      have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hθ.2.1
      have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
      have hcomp : ContinuousAt
          (fun t : ℝ => deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
        ContinuousAt.comp (g := deriv (expGrad u))
          (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
          (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hinner
      exact (Complex.continuous_re.continuousAt.comp hcomp).continuousWithinAt
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' (integrableOn_const hWbdd (C := C)) hEGmeas ?_
      filter_upwards [ae_restrict_mem hWmeas] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]; exact (hC θ hθ.2).1
    · refine Integrable.mono' (integrableOn_const hWbdd (C := C)) hRDmeas ?_
      filter_upwards [ae_restrict_mem hWmeas] with θ hθ
      rw [Real.norm_eq_abs]; exact (hC θ hθ.2).2
  rw [hindF, hindG]
  -- CASE SPLIT: the whole circle is superlevel, or some angle escapes it
  by_cases hfull : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ V
  · -- FULL CASE: `P = ℝ`, so the indicator drops and the periodic IBP applies directly
    have hPeq : P = univ := by
      ext θ; simp only [hP, mem_setOf_eq, mem_univ, iff_true]; exact hfull θ
    have hFind : ∀ θ : ℝ, P.indicator F θ = F θ := fun θ => by rw [hPeq]; simp
    have hGind : ∀ θ : ℝ, P.indicator G θ = G θ := fun θ => by rw [hPeq]; simp
    simp only [hFind, hGind]
    rw [← integral_Ioo_eq_intervalIntegral hπ, ← integral_Ioo_eq_intervalIntegral hπ]
    exact integral_full_posPart_re_deriv_expGrad hU hu (fun θ => (hfull θ).1)
      (fun θ => (hfull θ).2)
  · -- PROPER CASE: pick a seam `α` escaping the superlevel set and rotate to `(α, α+2π)`
    push Not at hfull
    obtain ⟨α, hα⟩ := hfull
    set W : Set ℝ := {θ' : ℝ | θ' ∈ Ioo α (α + 2 * π) ∧
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} with hWdef
    have hWmeas : MeasurableSet W :=
      (isOpen_Ioo.inter (hVopen.preimage (by fun_prop))).measurableSet
    -- transfer the two `(−π, π)` indicator interval integrals to the window `(α, α+2π)`
    have haddπ : (-π) + 2 * π = π := by ring
    have hαle : α ≤ α + 2 * π := by linarith [Real.pi_pos]
    have hWeq : W = Ioo α (α + 2 * π) ∩ P := by
      ext θ; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
    have htransF : (∫ θ in (-π)..π, P.indicator F θ) = ∫ θ in W, F θ := by
      have hkey := hPper.intervalIntegral_add_eq (-π) α
      rw [haddπ] at hkey
      rw [hkey, ← integral_Ioo_eq_intervalIntegral hαle, hWeq, ← setIntegral_indicator hPmeas]
    have htransG : (∫ θ in (-π)..π, P.indicator G θ) = ∫ θ in W, G θ := by
      have hkey := hQper.intervalIntegral_add_eq (-π) α
      rw [haddπ] at hkey
      rw [hkey, ← integral_Ioo_eq_intervalIntegral hαle, hWeq, ← setIntegral_indicator hPmeas]
    rw [htransF, htransG]
    -- the window slice IBP: the seam `α` (and `α+2π`) escape the superlevel set
    have hαπOut : Complex.exp ((ξ : ℂ) + ((α + 2 * π : ℝ) : ℂ) * Complex.I) ∉ V := by
      rw [hexpper α]; exact hα
    have hcontClos : ContinuousOn
        (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (closure W) :=
      hcontR.continuousOn
    exact setIntegral_windowSlice_posPart_re_deriv_expGrad hU hu hcontClos hEsc hα hαπOut
      (hwinInt α (α + 2 * π)).1 (hwinInt α (α + 2 * π)).2

/-! ### The truncated rough flux and its `δ → 0` recovery of `roughFlux`

The **truncated rough flux** `truncRoughFlux u U δ ξ` is the δ-rough flux with the potential factor
`u` replaced by its truncation `(u − δ)⁺`, integrated over the superlevel slice.  For `u` strictly
positive on `U`, `(u − δ)⁺ → u` pointwise as `δ ↓ 0` and the superlevel slices increase to the full
slice, so — dominated by the slice-`L¹` radial-derivative bound (`|(u − δ)⁺| ≤ |u| ≤ M` on the
slice) — the truncated rough flux converges to `roughFlux u U ξ`.  The convergence is even more
elementary than `tendsto_roughFluxδ_atZero`: on the superlevel slice `|(u − δ)⁺ − u| = δ` uniformly.
-/

/-- The **truncated rough flux**: the angle integral over the superlevel slice of the truncated
potential `(u − δ)⁺` against the radial-derivative factor `Re (expGrad u)`. -/
noncomputable def truncRoughFlux (u : ℂ → ℝ) (U : Set ℂ) (δ ξ : ℝ) : ℝ :=
  ∫ θ in Ioo (-π) π,
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}.indicator
      (fun θ' : ℝ => (u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I)) - δ)⁺
        * (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)).re) θ

/-- **The truncated rough flux is the set integral over the superlevel slice.** The indicator
integral defining `truncRoughFlux` unfolds, exactly as for `roughFluxδ`, to the set integral of
`(u − δ)⁺ · Re (expGrad u)` over the open δ-angular slice. -/
theorem truncRoughFlux_eq_setIntegral_slice {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    truncRoughFlux u U δ ξ = ∫ θ in angularSliceδ U u δ ξ,
      (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hπ := Real.pi_pos
  have hVopen : IsOpen (superLevelU U u δ) := isOpen_superLevelU hU hu δ
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hmeasset :
      MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} :=
    hcontmap.measurable hVopen.measurableSet
  unfold truncRoughFlux
  rw [setIntegral_indicator hmeasset]
  refine setIntegral_congr_set ?_
  rw [angularSliceδ, superLevelU]
  refine (ae_eq_set.mpr ⟨?_, ?_⟩) <;>
    · refine measure_mono_null (fun θ hθ => ?_) measure_empty
      simp only [mem_diff, mem_inter_iff, mem_setOf_eq] at hθ
      tauto

/-- **`δ → 0` recovery of the rough flux via the truncated flux.** For `u` harmonic and strictly
positive on the open set `U`, uniformly bounded by `M` on the angular slice at log-radius `ξ` with
the slice radial-derivative integrand integrable, along any positive null-sequence `δ n → 0` the
truncated rough flux tends to the rough flux: the superlevel-slice indicators of the integrand
`(u − δ n)⁺ · Re (expGrad u)` converge pointwise to the full-slice `u · Re (expGrad u)` (both the
superlevel slices increase to the full slice and `(u − δ n)⁺ → u`), dominated by the slice-`L¹`
bound `M · |Re (expGrad u)|`, so dominated convergence applies on `(−π, π)`. -/
theorem tendsto_truncRoughFlux_atZero {u : ℂ → ℝ} {U : Set ℂ} {ξ M : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z) (hMnn : 0 ≤ M)
    (hM : ∀ θ ∈ angularSlice U ξ, |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hReInt : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hdto : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => truncRoughFlux u U (d n) ξ) atTop (𝓝 (roughFlux u U ξ)) := by
  have hπ := Real.pi_pos
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hssub : s ⊆ Ioo (-π) π := angularSlice_subset U ξ
  set I : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hI
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
  -- the truncated-flux integrand and its target, as indicator integrals over `(−π, π)`
  set J : ℝ → ℝ → ℝ := fun δ θ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
    * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hJ
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun θ => {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)}.indicator (J (d n)) θ) (volume.restrict (Ioo (-π) π)) := by
    intro n
    have hVmeas : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable
          (isOpen_superLevelU hU hu (d n)).measurableSet
    rw [aestronglyMeasurable_indicator_iff hVmeas]
    -- `J (d n)` on `(Ioo (-π) π) ∩ V`; since `V ∩ Ioo ⊆ s`, restrict its slice measurability
    have hucontS : ContinuousOn (fun θ : ℝ =>
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) s := fun θ hθ =>
      (ContinuousAt.comp (g := u)
        (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hθ.2).continuousAt (by fun_prop)).continuousWithinAt
    have hposS : ContinuousOn (fun θ : ℝ =>
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n)⁺) s :=
      lipschitzWith_posPart.continuous.comp_continuousOn (hucontS.sub continuousOn_const)
    have hJslice : AEStronglyMeasurable (J (d n)) (volume.restrict s) :=
      (hposS.aestronglyMeasurable hsmeas).mul hReInt.aestronglyMeasurable
    refine hJslice.mono_measure ?_
    rw [Measure.restrict_restrict hVmeas]
    refine Measure.restrict_mono (fun θ hθ => ?_) le_rfl
    exact (show θ ∈ s from ⟨hθ.2, hθ.1.1⟩)
  have hδform : ∀ n, truncRoughFlux u U (d n) ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
          superLevelU U u (d n)}.indicator (J (d n)) θ := fun n => rfl
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
      rw [hB, Set.indicator_of_mem hθs, hJ, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      -- `|(u − δ)⁺| ≤ |u| ≤ M`
      have hule : |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M := hM θ hθs
      have hnn : 0 ≤ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := (hpos _ hθV.1).le
      rw [abs_of_nonneg (posPart_nonneg _)]
      calc (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n)⁺
          ≤ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
            rw [show (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n)⁺
              = max (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n) 0 from rfl]
            exact max_le (by linarith [(hdpos n)]) hnn
        _ ≤ M := le_trans (le_abs_self _) hule
    · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV),
        norm_zero, hB]
      by_cases hθs : θ ∈ s
      · rw [Set.indicator_of_mem hθs]; positivity
      · rw [Set.indicator_of_notMem hθs]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    -- pointwise convergence of the superlevel-slice truncated integrand to the full-slice `I θ`
    by_cases hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
    · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
      have hupos : 0 < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := hpos _ hmem
      have hev : ∀ᶠ n in atTop, d n < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
        hdto.eventually_lt_const hupos
      refine Tendsto.congr' ?_
        (show Tendsto (fun n : ℕ => J (d n) θ) atTop (𝓝 (I θ)) from ?_)
      · filter_upwards [hev] with n hn
        rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)}
          from ⟨hmem, hn⟩)]
      · have hJto : Tendsto (fun n : ℕ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
            - d n)⁺) atTop (𝓝 ((u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - 0)⁺)) := by
          exact (continuous_posPart.tendsto _).comp (tendsto_const_nhds.sub hdto)
        rw [hJ, hI, sub_zero, posPart_eq_self.mpr hupos.le] at *
        exact hJto.mul_const _
    · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with n
      rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)}
        from fun h => hmem h.1)]

/-- **Rough-flux increment from the truncated-flux increment bound.** For `u` harmonic and strictly
positive on the open set `U`, uniformly bounded by `M` on both slices at `ζ₁` and `ζ₂` with the
slice radial-derivative integrand integrable there, if the truncated-flux increment is bounded by a
constant `D` for every `δ > 0`, then the rough-flux increment is bounded by `D`: pass to `δ → 0`
using the truncated-flux recovery of the rough flux at each of the two log-radii. -/
theorem roughFlux_sub_le_of_truncRoughFlux_sub_le {u : ℂ → ℝ} {U : Set ℂ} {ζ₁ ζ₂ M D : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hMnn : 0 ≤ M)
    (hM1 : ∀ θ ∈ angularSlice U ζ₁, |u (Complex.exp ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hM2 : ∀ θ ∈ angularSlice U ζ₂, |u (Complex.exp ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hRe1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₁))
    (hRe2 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₂))
    (hδbd : ∀ δ : ℝ, 0 < δ → truncRoughFlux u U δ ζ₂ - truncRoughFlux u U δ ζ₁ ≤ D) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ D := by
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hd
  have hdpos : ∀ n, 0 < d n := fun n => by positivity
  have hdto : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim1 : Tendsto (fun n => truncRoughFlux u U (d n) ζ₁) atTop (𝓝 (roughFlux u U ζ₁)) :=
    tendsto_truncRoughFlux_atZero hU hu hpos hMnn hM1 hRe1 hdpos hdto
  have hlim2 : Tendsto (fun n => truncRoughFlux u U (d n) ζ₂) atTop (𝓝 (roughFlux u U ζ₂)) :=
    tendsto_truncRoughFlux_atZero hU hu hpos hMnn hM2 hRe2 hdpos hdto
  have hlim : Tendsto (fun n => truncRoughFlux u U (d n) ζ₂ - truncRoughFlux u U (d n) ζ₁) atTop
      (𝓝 (roughFlux u U ζ₂ - roughFlux u U ζ₁)) := hlim2.sub hlim1
  refine le_of_tendsto hlim ?_
  filter_upwards with n
  exact hδbd (d n) (hdpos n)

/-! ### The truncated-flux increment inequality (fixed-window FTC on the superlevel set)

The truncated-flux increment `truncRoughFlux u U δ ζ₂ − truncRoughFlux u U δ ζ₁` is, on a window
`{e^{ζ₁} < |z| < e^{ζ₂}}` (`ζ₂ < 0`) whose superlevel intersection sits compactly inside `U`, the
Dirichlet energy of `{u > δ} ∩ U` over the window annulus, bounded above by the total energy
`D(u; U)`.  The truncated integrand is supported in the superlevel slice and — because `(u − δ)⁺`
vanishes continuously across the superlevel boundary while `Re (expGrad u)` stays bounded on the
compact containment `K = closure({u > δ} ∩ window) ⊆ U` — extends to a continuous integrand on the
whole fixed window box, so the fixed-window flux–energy FTC applies without a moving domain. -/

/-! ### The windowed truncated integrand and the moving-domain flux FTC

Fix a window annulus `W = {e^{ξ₁} < |z| < e^{ξ₂}}` whose superlevel intersection `V ∩ W` has compact
closure `K ⊆ U`.  On the log-strip box `stripBox ξ₁ ξ₂ (−π) π` the **windowed truncated integrand**
`H w = 1_{e^w ∈ U} · (u(e^w) − δ)⁺ · Re (expGrad u w)` is continuous: near a point whose exponential
lies in `U` the two smooth factors are continuous, while off `K` (in particular at any strip-box
point whose exponential escapes `U`) `H` vanishes on a whole neighbourhood since `{H ≠ 0}` maps into
`V ∩ W ⊆ K`.  The truncated rough flux is the `θ`-integral of `H` over the full circle, so the
strip-box Lipschitz differentiation under the integral sign gives its `ξ`-FTC with the superlevel
slice energy as derivative. -/

/-- The **windowed truncated integrand** `H w = 1_{e^w ∈ U} · (u(e^w) − δ)⁺ · Re (expGrad u w)`. -/
noncomputable def windowedTruncIntegrand (u : ℂ → ℝ) (U : Set ℂ) (δ : ℝ) (w : ℂ) : ℝ :=
  U.indicator (fun z => (u z - δ)⁺ * (gradC u z * z).re) (Complex.exp w)

/-- Off the compact containment `K ⊇ V ∩ W`, the windowed truncated integrand vanishes on any point
of the strip box (whose exponential lies in the window annulus). -/
theorem windowedTruncIntegrand_eq_zero_of_notMem {u : ℂ → ℝ} {U : Set ℂ} {δ ξ₁ ξ₂ : ℝ}
    {w : ℂ} (hw : w ∈ stripBox ξ₁ ξ₂ (-π) π)
    (hwK : Complex.exp w ∉ closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ξ₁)
      (Real.exp ξ₂))) :
    windowedTruncIntegrand u U δ w = 0 := by
  unfold windowedTruncIntegrand
  by_cases hU : Complex.exp w ∈ U
  · rw [Set.indicator_of_mem hU]
    by_cases hgt : δ < u (Complex.exp w)
    · exfalso
      apply hwK
      apply subset_closure
      refine ⟨⟨hU, hgt⟩, ?_⟩
      obtain ⟨hre1, hre2, _, _⟩ := hw
      have hdist : dist (Complex.exp w) 0 = Real.exp w.re := by
        rw [dist_zero_right, Complex.norm_exp]
      refine ⟨?_, ?_⟩
      · rw [hdist]; exact Real.exp_lt_exp.mpr hre1
      · rw [hdist]; exact Real.exp_lt_exp.mpr hre2
    · rw [posPart_eq_zero.mpr (by rw [not_lt] at hgt; linarith), zero_mul]
  · rw [Set.indicator_of_notMem hU]

/-- **Continuity of the windowed truncated integrand on the strip box.** For `u` harmonic on the
open set `U` with the superlevel window intersection compactly contained in `U`
(`hK : closure (V ∩ W) ⊆ U`), the windowed truncated integrand `H` is continuous on the log-strip
box `stripBox ξ₁ ξ₂ (−π) π`.  At a point whose exponential lies in `U` the two smooth factors are
continuous; off the compact containment `K` (in particular where the exponential escapes `U`), `H`
vanishes on a whole neighbourhood since `exp ⁻¹' Kᶜ` is open and `H` is supported in `exp ⁻¹' K`. -/
theorem continuousOn_windowedTruncIntegrand {u : ℂ → ℝ} {U : Set ℂ} {δ ξ₁ ξ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hK : closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂)) ⊆ U) :
    ContinuousOn (windowedTruncIntegrand u U δ) (stripBox ξ₁ ξ₂ (-π) π) := by
  set K : Set ℂ := closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
    with hKdef
  intro w hw
  by_cases hwU : Complex.exp w ∈ U
  · -- near a point whose exponential lies in `U`, both factors are continuous
    have hnhdU : (fun z : ℂ => Complex.exp z) ⁻¹' U ∈ nhds w :=
      (hU.preimage Complex.continuous_exp).mem_nhds hwU
    have hHeq : windowedTruncIntegrand u U δ
        =ᶠ[nhds w] fun z : ℂ => (u (Complex.exp z) - δ)⁺ * (expGrad u z).re := by
      filter_upwards [hnhdU] with z hz
      unfold windowedTruncIntegrand
      rw [Set.indicator_of_mem (show Complex.exp z ∈ U from hz), expGrad]
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (hHeq.filter_mono nhdsWithin_le_nhds)
      (hHeq.self_of_nhds)
    -- continuity of `(u∘exp − δ)⁺ · Re (expGrad u)` at `w`
    have hcu : ContinuousAt (fun z : ℂ => u (Complex.exp z)) w :=
      (differentiableAt_of_harmonicOnNhd hu hwU).continuousAt.comp
        Complex.continuous_exp.continuousAt
    have hpos : ContinuousAt (fun z : ℂ => (u (Complex.exp z) - δ)⁺) w :=
      (continuous_posPart.continuousAt).comp (hcu.sub continuousAt_const)
    have hre : ContinuousAt (fun z : ℂ => (expGrad u z).re) w :=
      Complex.continuous_re.continuousAt.comp
        (expGrad_differentiableAt_open hU hu hwU).continuousAt
    exact (hpos.mul hre).continuousWithinAt
  · -- off `U`, `exp w ∉ K` (since `K ⊆ U`), so `H` vanishes on a neighbourhood within the strip box
    have hwK : Complex.exp w ∉ K := fun h => hwU (hK h)
    have hnhd : (fun z : ℂ => Complex.exp z) ⁻¹' Kᶜ ∈ nhds w :=
      (isClosed_closure.isOpen_compl.preimage Complex.continuous_exp).mem_nhds hwK
    have hHeq : windowedTruncIntegrand u U δ
        =ᶠ[nhdsWithin w (stripBox ξ₁ ξ₂ (-π) π)] fun _ : ℂ => (0 : ℝ) := by
      have hnhdW : (fun z : ℂ => Complex.exp z) ⁻¹' Kᶜ
          ∈ nhdsWithin w (stripBox ξ₁ ξ₂ (-π) π) := nhdsWithin_le_nhds hnhd
      filter_upwards [hnhdW, self_mem_nhdsWithin] with z hz hzstrip
      exact windowedTruncIntegrand_eq_zero_of_notMem hzstrip hz
    refine ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hHeq ?_
    exact windowedTruncIntegrand_eq_zero_of_notMem hw hwK

/-- **The truncated rough flux is the full-circle integral of the windowed truncated integrand.**
For each log-radius `ξ`, `truncRoughFlux u U δ ξ` equals the `θ`-integral over `(−π, π)` of
`windowedTruncIntegrand u U δ (ξ + θi)`: pointwise the two integrands agree — on the superlevel
slice both are `(u − δ)⁺ · Re (expGrad u)`, and off it both vanish (either the exponential escapes
`U`, or `u ≤ δ` makes `(u − δ)⁺ = 0`). -/
theorem truncRoughFlux_eq_integral_windowedTruncIntegrand {u : ℂ → ℝ} {U : Set ℂ} (δ ξ : ℝ) :
    truncRoughFlux u U δ ξ
      = ∫ θ in Ioo (-π) π, windowedTruncIntegrand u U δ ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
  unfold truncRoughFlux windowedTruncIntegrand
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  by_cases hU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
  · by_cases hgt : δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    · rw [Set.indicator_of_mem
          (show θ ∈ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
            from ⟨hU, hgt⟩), Set.indicator_of_mem hU, expGrad]
    · rw [Set.indicator_of_notMem
          (show θ ∉ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
            from fun h => hgt h.2), Set.indicator_of_mem hU,
        posPart_eq_zero.mpr (by rw [not_lt] at hgt; linarith), zero_mul]
  · rw [Set.indicator_of_notMem
        (show θ ∉ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
          from fun h => hU h.1), Set.indicator_of_notMem hU]

end RiemannDynamics
