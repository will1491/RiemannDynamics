/-
Copyright (c) 2026 RiemannDynamics contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy
import RiemannDynamics.Analysis.GrotzschRing.GrotzschTipRegularity

/-!
# The Grötzsch potential energy identity

For the Grötzsch potential `v` on the Grötzsch ring `grotzschRing s` and the collar slope `b`
extracted from the affine circle mean `logCircleMean 0 v ξ = 2π + b·ξ`, the total Dirichlet energy
equals `ENNReal.ofReal b`.

The energy splits along the slit tip circle `|z| = s` into an inner-disk part and an outer-collar
part.  Both are exact `ofReal` flux increments of the single monotone flux function `F = ringFlux v`
(equal to `ringFluxSlit v` on every circle).  On the inner disk the flux runs from its limit `0` at
the puncture up to the one-sided value `F_s⁻` at the tip; on the outer collar it runs from `F_s⁺` up
to the boundary slope `b`.  The flux is continuous across the tip circle (`F_s⁻ = F_s⁺`), so the two
pieces telescope to `ofReal b`.

## Main results
* `ringFluxSlit_tendsto_atBot_zero` — the inner flux limit is `0`.
* `dirichletEnergy_grotzschRing_eq_slope` — the total energy equals `ENNReal.ofReal b`.
-/

open MeasureTheory Set ENNReal Filter Topology Complex

open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-! ### The inner flux limit at the puncture -/

/-- **Tip bound on the slit flux.** For the Grötzsch potential `v`, on circles of radius `e^ξ`
below the near-tip radius `r₁`, the slit-chart flux is bounded by `2π · C · e^ξ`: the integrand is
`v · Re (expGrad v)`, dominated by `v · ‖gradC v‖ · e^ξ ≤ C · e^ξ`. -/
theorem abs_ringFluxSlit_le_tip {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ∃ C r₁ : ℝ, 0 < r₁ ∧ 0 ≤ C ∧ ∀ ξ : ℝ, Real.exp ξ < r₁ → Real.exp ξ < s →
      |ringFluxSlit v ξ| ≤ 2 * π * C * Real.exp ξ := by
  have hπ := Real.pi_pos
  obtain ⟨C, r₁, hr₁, hb⟩ := grotzschPotential_flux_bound_near hs0 hs1 hvh hvc hv0
  refine ⟨max C 0, r₁, hr₁, le_max_right _ _, fun ξ hξr hξs => ?_⟩
  have hξlog : ξ < Real.log s := (Real.lt_log_iff_exp_lt hs0).mpr hξs
  rw [ringFluxSlit_eq]
  -- pointwise bound of the integrand by `C · e^ξ` on the shrunk circle
  have hpt : ∀ θ ∈ Ioo (0 : ℝ) (2 * π),
      ‖v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re‖ ≤ max C 0 * Real.exp ξ := by
    intro θ hθ
    set z : ℂ := Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) with hz
    have hzmem : z ∈ grotzschRing s :=
      exp_mem_grotzschRing_slitBox hs0 hs1 hξlog hθ.1 hθ.2
    have hznorm : ‖z‖ = Real.exp ξ := by rw [hz, Complex.norm_exp, re_logPolar]
    have hzr : ‖z‖ < r₁ := by rw [hznorm]; exact hξr
    have hvnn : 0 ≤ v z := (hvrange z hzmem).1
    -- `|Re (expGrad v w)| ≤ ‖expGrad v w‖ = ‖gradC v z‖ · e^ξ`
    have hre : |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|
        ≤ ‖gradC v z‖ * Real.exp ξ := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [expGrad, norm_mul, Complex.norm_exp, re_logPolar]
    have hflux : v z * ‖gradC v z‖ ≤ C := hb z hzmem hzr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hvnn]
    calc v z * |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|
        ≤ v z * (‖gradC v z‖ * Real.exp ξ) :=
          mul_le_mul_of_nonneg_left hre hvnn
      _ = (v z * ‖gradC v z‖) * Real.exp ξ := by ring
      _ ≤ C * Real.exp ξ := mul_le_mul_of_nonneg_right hflux (Real.exp_pos ξ).le
      _ ≤ max C 0 * Real.exp ξ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos ξ).le
  -- integrate the pointwise bound over `(0, 2π)`
  have hmeasreal : (volume : Measure ℝ).real (Ioo (0 : ℝ) (2 * π)) = 2 * π := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 2 * π - 0)]
    ring
  have hbnd : ‖∫ θ in Ioo (0 : ℝ) (2 * π),
      v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re‖
      ≤ (max C 0 * Real.exp ξ) * (2 * π) := by
    refine le_trans (norm_setIntegral_le_of_norm_le_const (C := max C 0 * Real.exp ξ)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) hpt) ?_
    rw [hmeasreal]
  rw [Real.norm_eq_abs] at hbnd
  calc |∫ θ in Ioo (0 : ℝ) (2 * π),
        v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|
      ≤ (max C 0 * Real.exp ξ) * (2 * π) := hbnd
    _ = 2 * π * max C 0 * Real.exp ξ := by ring

/-- **The inner flux limit vanishes.** For the Grötzsch potential `v`, the slit-chart flux tends to
`0` at the puncture: the tip bound `|ringFluxSlit v ξ| ≤ 2π · C · e^ξ` is squeezed to `0` as
`ξ → −∞`. -/
theorem ringFluxSlit_tendsto_atBot_zero {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    Tendsto (fun ξ : ℝ => ringFluxSlit v ξ) atBot (𝓝 0) := by
  obtain ⟨C, r₁, hr₁, hCnn, hb⟩ := abs_ringFluxSlit_le_tip hs0 hs1 hvh hvc hv0 hvrange
  -- eventually `e^ξ < min r₁ s`, so the tip bound applies
  have hev : ∀ᶠ ξ : ℝ in atBot, |ringFluxSlit v ξ - 0| ≤ 2 * π * C * Real.exp ξ := by
    filter_upwards [Iio_mem_atBot (Real.log (min r₁ s))] with ξ hξ
    have hξexp : Real.exp ξ < min r₁ s := by
      have hmp : 0 < min r₁ s := lt_min hr₁ hs0
      calc Real.exp ξ < Real.exp (Real.log (min r₁ s)) := Real.exp_lt_exp.mpr hξ
        _ = min r₁ s := Real.exp_log hmp
    rw [sub_zero]
    exact hb ξ (lt_of_lt_of_le hξexp (min_le_left _ _)) (lt_of_lt_of_le hξexp (min_le_right _ _))
  -- squeeze between `0` and `2π C e^ξ → 0`
  have hbound : Tendsto (fun ξ : ℝ => 2 * π * C * Real.exp ξ) atBot (𝓝 0) := by
    have hexp : Tendsto (fun ξ : ℝ => Real.exp ξ) atBot (𝓝 0) := Real.tendsto_exp_atBot
    have := hexp.const_mul (2 * π * C)
    simpa using this
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hev] with ξ hξ
  simpa [Real.norm_eq_abs] using hξ

/-- **`ofReal` commutes with the supremum of a convergent monotone real sequence.** If a monotone
sequence `g : ℕ → ℝ` converges to `A`, then `⨆ n, ENNReal.ofReal (g n) = ENNReal.ofReal A`. -/
theorem iSup_ofReal_of_tendsto {g : ℕ → ℝ} {A : ℝ} (hmono : Monotone g)
    (htends : Tendsto g atTop (𝓝 A)) :
    ⨆ n, ENNReal.ofReal (g n) = ENNReal.ofReal A := by
  have hmono' : Monotone fun n => ENNReal.ofReal (g n) :=
    fun n m hnm => ENNReal.ofReal_le_ofReal (hmono hnm)
  have h1 : Tendsto (fun n => ENNReal.ofReal (g n)) atTop (𝓝 (⨆ n, ENNReal.ofReal (g n))) :=
    tendsto_atTop_iSup hmono'
  have h2 : Tendsto (fun n => ENNReal.ofReal (g n)) atTop (𝓝 (ENNReal.ofReal A)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp htends
  exact tendsto_nhds_unique h1 h2

/-! ### The inner-disk energy -/

/-- The punctured inner disk `{0 < |z| < s}` is the monotone union of the sub-annuli
`{e^{log s − (n+1)} < |z| < e^{log s − 1/(n+2)}}` whose inner radii shrink to `0` and outer radii
grow to `s`. -/
theorem roundAnnulus_inner_eq_iUnion {s : ℝ} (hs0 : 0 < s) :
    RoundAnnulus 0 0 s
      = ⋃ n : ℕ, RoundAnnulus 0 (Real.exp (Real.log s - (n + 1)))
          (Real.exp (Real.log s - 1 / (n + 2))) := by
  ext z
  simp only [RoundAnnulus, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨h1, h2⟩
    have hzpos : 0 < dist z 0 := h1
    have hlog : Real.log (dist z 0) < Real.log s := Real.log_lt_log hzpos h2
    -- pick `n` with `log s − (n+1) < log (dist z 0)` and `log (dist z 0) < log s − 1/(n+2)`
    set L : ℝ := Real.log (dist z 0) with hL
    have hgap : 0 < Real.log s - L := by rw [hL]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max (Real.log s - L) (1 / (Real.log s - L)))
    have hn1 : Real.log s - L < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hn2 : 1 / (Real.log s - L) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    refine ⟨n, ?_, ?_⟩
    · have hlt : Real.log s - ((n : ℝ) + 1) < L := by linarith
      calc Real.exp (Real.log s - ((n : ℝ) + 1))
          < Real.exp L := Real.exp_lt_exp.mpr hlt
        _ = dist z 0 := by rw [hL, Real.exp_log hzpos]
    · have hupper : L < Real.log s - 1 / ((n : ℝ) + 2) := by
        have h1 : 1 < (Real.log s - L) * (n : ℝ) := by
          rw [div_lt_iff₀ hgap] at hn2; linarith [mul_comm (n : ℝ) (Real.log s - L)]
        have hinv : 1 / ((n : ℝ) + 2) < Real.log s - L := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [hgap, Nat.cast_nonneg (α := ℝ) n]
        linarith
      calc dist z 0 = Real.exp L := (Real.exp_log hzpos).symm
        _ < Real.exp (Real.log s - 1 / ((n : ℝ) + 2)) := Real.exp_lt_exp.mpr hupper
  · rintro ⟨n, h1, h2⟩
    refine ⟨lt_of_le_of_lt (Real.exp_pos _).le h1, ?_⟩
    have hupper : Real.exp (Real.log s - 1 / ((n : ℝ) + 2)) < s := by
      calc Real.exp (Real.log s - 1 / ((n : ℝ) + 2))
          < Real.exp (Real.log s) := Real.exp_lt_exp.mpr (by
            have : 0 < 1 / ((n : ℝ) + 2) := by positivity
            linarith)
        _ = s := Real.exp_log hs0
    exact lt_trans h2 hupper

/-- **Exact inner-disk energy at a limit flux value.** For the Grötzsch potential `v`, if the
slit-chart flux tends to `L` along the sequence `bₙ = log s − 1/(n+2) ↑ log s` (its one-sided tip
limit), then the Dirichlet energy over the punctured inner disk `{0 < |z| < s}` equals
`ofReal L`: the exhausting sub-annuli have energy `ofReal (F(bₙ) − F(aₙ))`, with `F(aₙ) → 0` at the
puncture and `F(bₙ) → L`. -/
theorem dirichletEnergy_innerDisk_eq_ofReal {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1)
    (hLtend : Tendsto (fun n : ℕ => ringFluxSlit v (Real.log s - 1 / (n + 2))) atTop (𝓝 L)) :
    dirichletEnergy v (RoundAnnulus 0 0 s) = ENNReal.ofReal L := by
  set aₙ : ℕ → ℝ := fun n => Real.log s - ((n : ℝ) + 1) with haₙ
  set bₙ : ℕ → ℝ := fun n => Real.log s - 1 / ((n : ℝ) + 2) with hbₙ
  have hbₙlt : ∀ n, bₙ n < Real.log s := fun n => by
    simp only [hbₙ]
    have hp : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hbₙexp : ∀ n, Real.exp (bₙ n) < s := fun n =>
    (Real.lt_log_iff_exp_lt hs0).mp (hbₙlt n)
  have haₙle : ∀ n, aₙ n ≤ bₙ n := fun n => by
    simp only [haₙ, hbₙ]
    have h1 : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  -- gradient integrand is measurable (for the monotone-union `lintegral`)
  have hgmeas : Measurable fun z : ℂ => ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2 := by
    have heq : (fun z : ℂ => ((‖fderiv ℝ v z‖₊ : ℝ≥0∞)) ^ 2)
        = fun z => ENNReal.ofReal (Complex.normSq (gradC v z)) :=
      funext fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC v z
    rw [heq]
    exact ENNReal.measurable_ofReal.comp
      (Complex.continuous_normSq.measurable.comp (measurable_gradC v))
  -- the sub-annuli are monotone in `n`
  have hmono : Monotone fun n : ℕ => RoundAnnulus 0 (Real.exp (aₙ n)) (Real.exp (bₙ n)) := by
    intro n m hnm z hz
    refine ⟨lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) hz.1,
      lt_of_lt_of_le hz.2 (Real.exp_le_exp.mpr ?_)⟩
    · simp only [haₙ]; have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm; linarith
    · simp only [hbₙ]
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      have hle : 1 / ((m : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      linarith
  -- monotone-union energy = sup of sub-annulus energies
  have hunion : dirichletEnergy v (RoundAnnulus 0 0 s)
      = ⨆ n : ℕ, dirichletEnergy v (RoundAnnulus 0 (Real.exp (aₙ n)) (Real.exp (bₙ n))) := by
    unfold dirichletEnergy
    rw [roundAnnulus_inner_eq_iUnion hs0]
    exact lintegral_iUnion_of_monotone (fun n => (isOpen_roundAnnulus _ _ _).measurableSet)
      hmono hgmeas
  -- each sub-annulus energy is an `ofReal` flux increment
  have hpiece : ∀ n : ℕ,
      dirichletEnergy v (RoundAnnulus 0 (Real.exp (aₙ n)) (Real.exp (bₙ n)))
      = ENNReal.ofReal (ringFluxSlit v (bₙ n) - ringFluxSlit v (aₙ n)) := fun n =>
    dirichletEnergy_roundAnnulus_eq_ringFluxSlit_sub hs0 hs1 (hbₙexp n) (haₙle n)
      hvh hvc hv0 hv1 hvrange
  rw [hunion]
  simp only [hpiece]
  -- `F(aₙ) → 0` at the puncture; `F(bₙ) → L` by hypothesis
  have hFmono : MonotoneOn (ringFluxSlit v) (Iio (Real.log s)) :=
    ringFluxSlit_monotoneOn hs0 hs1 hvh hvc hv0 hv1 hvrange
  have haₙmem : ∀ n, aₙ n ∈ Iio (Real.log s) := fun n => by
    simp only [haₙ, Set.mem_Iio]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbₙmem : ∀ n, bₙ n ∈ Iio (Real.log s) := fun n => hbₙlt n
  have hbₙmono : Monotone bₙ := fun n m hnm => by
    simp only [hbₙ]
    have hle : 1 / ((m : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hnm 2
    linarith
  have haₙanti : Antitone aₙ := fun n m hnm => by
    simp only [haₙ]; have hc : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm; linarith
  -- monotone increments: `F(bₙ)` increases, `F(aₙ)` decreases
  have hincmono : Monotone fun n : ℕ => ringFluxSlit v (bₙ n) - ringFluxSlit v (aₙ n) := by
    intro n m hnm
    have hb := hFmono (hbₙmem n) (hbₙmem m) (hbₙmono hnm)
    have ha := hFmono (haₙmem m) (haₙmem n) (haₙanti hnm)
    simp only
    linarith
  -- limit of the increments is `L − 0`
  have haₙatbot : Tendsto aₙ atTop atBot := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hneg : Tendsto (fun n : ℕ => -((n : ℝ) + 1)) atTop atBot :=
      tendsto_neg_atBot_iff.mpr hbase
    refine (Filter.tendsto_atBot_add_const_left atTop (Real.log s) hneg).congr ?_
    intro n; simp only [haₙ]; ring
  have haₙtend : Tendsto (fun n => ringFluxSlit v (aₙ n)) atTop (𝓝 0) :=
    (ringFluxSlit_tendsto_atBot_zero hs0 hs1 hvh hvc hv0 hvrange).comp haₙatbot
  have hinctend : Tendsto (fun n => ringFluxSlit v (bₙ n) - ringFluxSlit v (aₙ n)) atTop
      (𝓝 (L - 0)) := hLtend.sub haₙtend
  rw [iSup_ofReal_of_tendsto hincmono hinctend, sub_zero]

/-! ### Continuity of the flux across the tip circle -/

/-- For a log-radius `ξ` inside the disk (`e^ξ < 1`) and a geometric angle `θ ∈ (0, 2π)`, the point
`e^{ξ+θi}` lies in the Grötzsch ring: its modulus is below `1` and, off the endpoints `θ = 0, 2π`,
it avoids the positive-real slit (its imaginary part vanishes only at `θ = π`, where the real part
is negative). -/
theorem exp_mem_grotzschRing_disk {s ξ θ : ℝ} (hs0 : 0 < s) (hξ1 : Real.exp ξ < 1)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * π) :
    Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s := by
  have hnorm : ‖Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ = Real.exp ξ := by
    rw [Complex.norm_exp, re_logPolar]
  refine ⟨mem_ball_zero_iff.mpr (by rw [hnorm]; exact hξ1), fun hslit => ?_⟩
  have hslit' : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschInner s := hslit
  rw [grotzschInner_eq hs0.le] at hslit'
  obtain ⟨him, hre0, _⟩ := hslit'
  -- `im (e^{ξ+θi}) = e^ξ · sin θ = 0` forces `sin θ = 0`, i.e. `θ = π` in `(0, 2π)`
  have himval : (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im = Real.exp ξ * Real.sin θ := by
    rw [Complex.exp_im, re_logPolar, im_logPolar]
  rw [himval] at him
  have hsin : Real.sin θ = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h (Real.exp_pos ξ).ne'
    · exact h
  -- `sin θ = 0` on `(0, 2π)` gives `θ = π`; then `re = −e^ξ < 0`, contradicting `re ≥ 0`
  have hθπ : θ = π := by
    rcases lt_trichotomy θ π with hlt | heq | hgt
    · exact absurd hsin (Real.sin_pos_of_pos_of_lt_pi hθ0 hlt).ne'
    · exact heq
    · have hp := Real.sin_pos_of_pos_of_lt_pi (x := θ - π) (by linarith) (by linarith)
      rw [Real.sin_sub_pi] at hp; linarith [hsin]
  have hreval : (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re = -Real.exp ξ := by
    rw [Complex.exp_re, re_logPolar, im_logPolar, hθπ, Real.cos_pi]; ring
  rw [hreval] at hre0
  linarith [Real.exp_pos ξ]

/-- **Off-slit gradient bound straddling the tip circle.** For the Grötzsch potential `v` and a
straddle half-width `δ` small enough that the closed annulus `{s·e^{−δ} ≤ |z| ≤ s·e^δ}` meets the
slit only within the tip ball `{|z − s| < r₀}` (and stays inside the disk), the gradient `gradC v`
is bounded on the part of that annulus away from the tip: every such `z` is an off-slit point of the
ring, where `gradC v` is continuous, so compactness yields a uniform bound. -/
theorem exists_bound_gradC_straddle {s δ r₀ : ℝ} (hs0 : 0 < s)
    (hdisk : s * Real.exp δ < 1)
    (hslit : s - r₀ < s * Real.exp (-δ)) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s)) :
    ∃ C : ℝ, ∀ z : ℂ, s * Real.exp (-δ) ≤ ‖z‖ → ‖z‖ ≤ s * Real.exp δ →
      r₀ ≤ ‖z - (s : ℂ)‖ → ‖gradC v z‖ ≤ C := by
  set A : Set ℂ := {z : ℂ | s * Real.exp (-δ) ≤ ‖z‖ ∧ ‖z‖ ≤ s * Real.exp δ
    ∧ r₀ ≤ ‖z - (s : ℂ)‖} with hA
  -- every point of `A` lies in the (open) Grötzsch ring
  have hAring : ∀ z ∈ A, z ∈ grotzschRing s := by
    intro z hz
    obtain ⟨hlo, hhi, htip⟩ := hz
    have hznorm1 : ‖z‖ < 1 := lt_of_le_of_lt hhi hdisk
    refine ⟨mem_ball_zero_iff.mpr hznorm1, fun hslitmem => ?_⟩
    -- a slit point `z = x`, `x ∈ [0, s]`, would need `|z| ≥ s e^{−δ}` and `s − x ≥ r₀`
    have hslitmem' : z ∈ grotzschInner s := hslitmem
    rw [grotzschInner_eq hs0.le] at hslitmem'
    obtain ⟨him, hx0, hxs⟩ := hslitmem'
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hznorm : ‖z‖ = z.re := by
      rw [hzre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, Complex.ofReal_re]
    have htipeq : ‖z - (s : ℂ)‖ = s - z.re := by
      conv_lhs => rw [hzre]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : z.re - s ≤ 0)]
      ring
    have h1 : s * Real.exp (-δ) ≤ z.re := by rw [hznorm] at hlo; exact hlo
    have h2 : r₀ ≤ s - z.re := by rw [htipeq] at htip; exact htip
    linarith
  -- `A` is compact
  have hAcompact : IsCompact A := by
    have h1 : IsClosed {z : ℂ | s * Real.exp (-δ) ≤ ‖z‖} :=
      isClosed_le continuous_const continuous_norm
    have h2 : IsClosed {z : ℂ | ‖z‖ ≤ s * Real.exp δ} :=
      isClosed_le continuous_norm continuous_const
    have h3 : IsClosed {z : ℂ | r₀ ≤ ‖z - (s : ℂ)‖} :=
      isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    have hclosed : IsClosed A := by
      rw [hA]
      have : {z : ℂ | s * Real.exp (-δ) ≤ ‖z‖ ∧ ‖z‖ ≤ s * Real.exp δ ∧ r₀ ≤ ‖z - (s : ℂ)‖}
          = {z : ℂ | s * Real.exp (-δ) ≤ ‖z‖} ∩ ({z : ℂ | ‖z‖ ≤ s * Real.exp δ}
            ∩ {z : ℂ | r₀ ≤ ‖z - (s : ℂ)‖}) := by ext z; simp
      rw [this]; exact h1.inter (h2.inter h3)
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    refine Metric.isBounded_iff.mpr ⟨2 * (s * Real.exp δ), fun x hx y hy => ?_⟩
    calc dist x y ≤ ‖x‖ + ‖y‖ := by rw [dist_eq_norm]; exact norm_sub_le x y
      _ ≤ 2 * (s * Real.exp δ) := by linarith [hx.2.1, hy.2.1]
  -- local off-slit bound at every point of `A`
  have hloc : ∀ z₀ ∈ A, ∃ U ∈ 𝓝 z₀, ∃ C : ℝ, ∀ z ∈ U, ‖gradC v z‖ ≤ C := by
    intro z₀ hz₀
    have hz₀ring : z₀ ∈ grotzschRing s := hAring z₀ hz₀
    have hcont : ContinuousAt (fun z => ‖gradC v z‖) z₀ :=
      (((gradC_differentiableOn hvh).differentiableAt
        ((isOpen_grotzschRing hs0.le).mem_nhds hz₀ring)).continuousAt).norm
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨η, hηpos, hη⟩ := hcont 1 one_pos
    refine ⟨Metric.ball z₀ η, Metric.ball_mem_nhds _ hηpos, ‖gradC v z₀‖ + 1, fun z hz => ?_⟩
    have := hη (Metric.mem_ball.mp hz)
    rw [Real.dist_eq, abs_lt] at this; linarith [this.2]
  choose! U hU C hC using hloc
  obtain ⟨t, htA, htcov⟩ := hAcompact.elim_nhds_subcover U (fun z hz => hU z hz)
  refine ⟨t.sum (fun z => max (C z) 0), fun z hz1 hz2 hz3 => ?_⟩
  have hzA : z ∈ A := ⟨hz1, hz2, hz3⟩
  obtain ⟨z₀, hz₀t, hz₀U⟩ := Set.mem_iUnion₂.mp (htcov hzA)
  calc ‖gradC v z‖ ≤ C z₀ := hC z₀ (htA z₀ hz₀t) z hz₀U
    _ ≤ max (C z₀) 0 := le_max_left _ _
    _ ≤ t.sum (fun z => max (C z) 0) :=
        Finset.single_le_sum (fun i _ => le_max_right _ _) hz₀t

/-- **Uniform flux-integrand bound straddling the tip circle.** For the Grötzsch potential `v`
there is a straddle half-width `δ` (with `s·e^δ < 1`) and a constant `K` bounding the flux integrand
`|v · Re (expGrad v)|` on the closed annulus `{|log|z| − log s| ≤ δ}`, uniformly in the angle: near
the tip the flux bound `v·‖gradC v‖ ≤ C₁` applies, and away from it the straddling gradient bound
`‖gradC v‖ ≤ K₂` (with `v ≤ 1`) applies; both are multiplied by `e^ξ ≤ s·e^δ`. -/
theorem exists_dominator_flux_seam {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ∃ K δ : ℝ, 0 < δ ∧ s * Real.exp δ < 1 ∧ 0 ≤ K ∧
      ∀ ξ θ : ℝ, |ξ - Real.log s| ≤ δ → 0 < θ → θ < 2 * π →
        |v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ K := by
  -- tip flux bound `v·‖gradC v‖ ≤ C₁` on `‖z − s‖ < r₁`
  obtain ⟨C₁, r₁, hr₁, hC₁⟩ := grotzschPotential_flux_bound_far hs0 hs1 hvh hvc hv0
  -- pick `δ` small: stay in the disk and empty the slit intersection with the straddle annulus
  have hlogpos : 0 < Real.log (1 / s) := Real.log_pos (by rw [lt_div_iff₀ hs0]; linarith)
  -- shrink factor `q = min r₁ s / (3 s) < 1`, giving a strict slit margin at `min r₁ s / 2`
  set q : ℝ := min r₁ s / (3 * s) with hqdef
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hqlt : q < 1 := by
    rw [hqdef, div_lt_one (by positivity)]
    calc min r₁ s ≤ s := min_le_right _ _
      _ < 3 * s := by linarith
  have hlogq : 0 < Real.log (1 / (1 - q)) :=
    Real.log_pos (by rw [lt_div_iff₀ (by linarith), one_mul]; linarith)
  set δ : ℝ := min (Real.log (1 / s) / 2) (Real.log (1 / (1 - q))) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) hlogq
  have hδ1 : δ ≤ Real.log (1 / s) / 2 := min_le_left _ _
  have hδ2 : δ ≤ Real.log (1 / (1 - q)) := min_le_right _ _
  -- `s·e^δ < 1`
  have hdisk : s * Real.exp δ < 1 := by
    have hlt : Real.exp δ < 1 / s := by
      calc Real.exp δ ≤ Real.exp (Real.log (1 / s) / 2) := Real.exp_le_exp.mpr hδ1
        _ < Real.exp (Real.log (1 / s)) := Real.exp_lt_exp.mpr (by linarith)
        _ = 1 / s := Real.exp_log (by positivity)
    rw [mul_comm, ← lt_div_iff₀ hs0]; exact hlt
  -- `s − min r₁ s / 2 < s·e^{−δ}`  ⇒  slit points excluded from the straddle annulus off the tip
  have hexpnegδ : s * Real.exp (-δ) = s / Real.exp δ := by rw [Real.exp_neg]; ring
  have hq1 : (0:ℝ) < 1 - q := by linarith
  have hslit : s - min r₁ s / 2 < s * Real.exp (-δ) := by
    have hexpδle : Real.exp δ ≤ 1 / (1 - q) := by
      calc Real.exp δ ≤ Real.exp (Real.log (1 / (1 - q))) := Real.exp_le_exp.mpr hδ2
        _ = 1 / (1 - q) := Real.exp_log (by positivity)
    -- lower bound `1 − q ≤ e^{−δ}`
    have hlb : 1 - q ≤ Real.exp (-δ) := by
      rw [one_div] at hexpδle
      rw [Real.exp_neg]
      exact (le_inv_comm₀ hq1 (Real.exp_pos δ)).mpr hexpδle
    have hsq : s * q = min r₁ s / 3 := by rw [hqdef]; field_simp
    calc s - min r₁ s / 2 < s - min r₁ s / 3 := by
          have : (0:ℝ) < min r₁ s := lt_min hr₁ hs0
          linarith
      _ = s - s * q := by rw [hsq]
      _ = s * (1 - q) := by ring
      _ ≤ s * Real.exp (-δ) := mul_le_mul_of_nonneg_left hlb hs0.le
  -- straddle gradient bound off the tip ball `‖z − s‖ ≥ min r₁ s / 2`
  obtain ⟨K₂, hK₂⟩ := exists_bound_gradC_straddle (r₀ := min r₁ s / 2) hs0 hdisk hslit hvh
  refine ⟨2 * (max (max C₁ K₂) 0 * (s * Real.exp δ)), δ, hδpos, hdisk, by positivity,
    fun ξ θ hξ hθ0 hθ2 => ?_⟩
  set z : ℂ := Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) with hz
  have hznorm : ‖z‖ = Real.exp ξ := by rw [hz, Complex.norm_exp, re_logPolar]
  have hξ1 : Real.exp ξ < 1 := by
    have : ξ ≤ Real.log s + δ := by rw [abs_le] at hξ; linarith [hξ.2]
    calc Real.exp ξ ≤ Real.exp (Real.log s + δ) := Real.exp_le_exp.mpr this
      _ = s * Real.exp δ := by rw [Real.exp_add, Real.exp_log hs0]
      _ < 1 := hdisk
  have hzmem : z ∈ grotzschRing s := exp_mem_grotzschRing_disk hs0 hξ1 hθ0 hθ2
  have hvnn : 0 ≤ v z := (hvrange z hzmem).1
  have hv1 : v z ≤ 1 := (hvrange z hzmem).2
  have hexpξle : Real.exp ξ ≤ s * Real.exp δ := by
    have : ξ ≤ Real.log s + δ := by rw [abs_le] at hξ; linarith [hξ.2]
    calc Real.exp ξ ≤ Real.exp (Real.log s + δ) := Real.exp_le_exp.mpr this
      _ = s * Real.exp δ := by rw [Real.exp_add, Real.exp_log hs0]
  -- `|Re (expGrad v w)| ≤ ‖gradC v z‖ · e^ξ`
  have hre : |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ ‖gradC v z‖ * Real.exp ξ := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [expGrad, norm_mul, Complex.norm_exp, re_logPolar]
  -- bound `v·‖gradC v‖ ≤ max (max C₁ K₂) 0`, splitting near/far from the tip
  have hflux : v z * ‖gradC v z‖ ≤ max (max C₁ K₂) 0 := by
    rcases lt_or_ge ‖z - (s : ℂ)‖ r₁ with htip | hfar
    · calc v z * ‖gradC v z‖ ≤ C₁ := hC₁ z hzmem htip
        _ ≤ max (max C₁ K₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
    · have hlo : s * Real.exp (-δ) ≤ ‖z‖ := by
        rw [hznorm]
        have : Real.log s - δ ≤ ξ := by rw [abs_le] at hξ; linarith [hξ.1]
        calc s * Real.exp (-δ) = Real.exp (Real.log s - δ) := by
              rw [Real.exp_sub, Real.exp_log hs0, hexpnegδ]
          _ ≤ Real.exp ξ := Real.exp_le_exp.mpr this
      have hfar' : min r₁ s / 2 ≤ ‖z - (s : ℂ)‖ :=
        le_trans (by rw [div_le_iff₀ (by norm_num)]; nlinarith [min_le_left r₁ s]) hfar
      have hgrad : ‖gradC v z‖ ≤ K₂ := hK₂ z hlo (by rw [hznorm]; exact hexpξle) hfar'
      calc v z * ‖gradC v z‖ ≤ 1 * K₂ :=
            mul_le_mul hv1 hgrad (norm_nonneg _) (by norm_num)
        _ = K₂ := one_mul K₂
        _ ≤ max (max C₁ K₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  -- assemble the pointwise bound
  rw [abs_mul, abs_of_nonneg hvnn]
  calc v z * |(expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|
      ≤ v z * (‖gradC v z‖ * Real.exp ξ) := mul_le_mul_of_nonneg_left hre hvnn
    _ = (v z * ‖gradC v z‖) * Real.exp ξ := by ring
    _ ≤ (max (max C₁ K₂) 0) * (s * Real.exp δ) :=
        mul_le_mul hflux hexpξle (Real.exp_pos ξ).le (le_max_right _ _)
    _ ≤ 2 * (max (max C₁ K₂) 0 * (s * Real.exp δ)) := by
        have hnn : (0:ℝ) ≤ max (max C₁ K₂) 0 * (s * Real.exp δ) :=
          mul_nonneg (le_max_right _ _) (by positivity)
        linarith

/-- **Continuity of the slit flux at the tip circle.** For the Grötzsch potential `v`, the
slit-chart flux `ringFluxSlit v` is continuous at `log s`: the flux integrand converges pointwise as
`ξ → log s` at every off-slit angle and is dominated by the uniform straddle bound, so dominated
convergence gives continuity. -/
theorem continuousAt_ringFluxSlit_logS {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ContinuousAt (ringFluxSlit v) (Real.log s) := by
  have hπ := Real.pi_pos
  obtain ⟨K, δ, hδpos, hdisk, hKnn, hK⟩ :=
    exists_dominator_flux_seam hs0 hs1 hvh hvc hv0 hvrange
  set F : ℝ → ℝ → ℝ := fun ξ θ => v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hF
  have hfluxeq : (fun ξ => ringFluxSlit v ξ) = fun ξ => ∫ θ in Ioo 0 (2 * π), F ξ θ :=
    funext fun ξ => ringFluxSlit_eq v ξ
  rw [show (ringFluxSlit v) = fun ξ => ∫ θ in Ioo 0 (2 * π), F ξ θ from hfluxeq]
  set μ : Measure ℝ := volume.restrict (Ioo 0 (2 * π)) with hμ
  -- each slice is continuous on `(0, 2π)`, hence a.e. strongly measurable, near `log s`
  have hslicecont : ∀ ξ : ℝ, Real.exp ξ < 1 → ContinuousOn (F ξ) (Ioo 0 (2 * π)) := by
    intro ξ hξ1 θ hθ
    have hzmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_disk hs0 hξ1 hθ.1 hθ.2
    set w₀ : ℂ := (ξ : ℂ) + (θ : ℂ) * Complex.I with hw₀
    have hv := (differentiableAt_of_harmonicOnNhd hvh hzmem)
    have hg : DifferentiableAt ℂ (gradC v) (Complex.exp w₀) :=
      (gradC_differentiableOn hvh).differentiableAt
        ((isOpen_grotzschRing hs0.le).mem_nhds hzmem)
    have hlin : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    have hcw : ContinuousAt (fun w : ℂ => v (Complex.exp w)) w₀ :=
      hv.continuousAt.comp (Complex.continuous_exp.continuousAt)
    have heq : (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ = w₀ := rfl
    have hcv : ContinuousAt (fun t : ℝ =>
        v (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))) θ := hcw.comp_of_eq hlin heq
    have hew : ContinuousAt (fun w : ℂ => (expGrad v w).re) w₀ := by
      have hexpg : ContinuousAt (expGrad v) w₀ :=
        ((hg.comp _ (Complex.differentiable_exp _)).mul
          (Complex.differentiable_exp _)).continuousAt
      exact Complex.continuous_re.continuousAt.comp hexpg
    have hce : ContinuousAt (fun t : ℝ =>
        (expGrad v ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ := hew.comp_of_eq hlin heq
    exact ((hcv.mul hce).continuousWithinAt)
  refine continuousAt_of_dominated (bound := fun _ => K) ?_ ?_ ?_ ?_
  · -- a.e. strong measurability for `ξ` in a neighbourhood of `log s`
    filter_upwards [Metric.ball_mem_nhds (Real.log s) hδpos] with ξ hξ
    have hξ1 : Real.exp ξ < 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hξ
      have : ξ < Real.log s + δ := by rw [abs_sub_lt_iff] at hξ; linarith [hξ.1]
      calc Real.exp ξ < Real.exp (Real.log s + δ) := Real.exp_lt_exp.mpr this
        _ = s * Real.exp δ := by rw [Real.exp_add, Real.exp_log hs0]
        _ < 1 := hdisk
    exact (hslicecont ξ hξ1).aestronglyMeasurable measurableSet_Ioo
  · -- domination near `log s`
    filter_upwards [Metric.closedBall_mem_nhds (Real.log s) hδpos] with ξ hξ
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact hK ξ θ (by rw [Metric.mem_closedBall, Real.dist_eq] at hξ; exact hξ) hθ.1 hθ.2
  · rw [hμ]; exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
  · -- pointwise convergence at every off-slit angle
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
    have hzmem : Complex.exp (((Real.log s) : ℂ) + (θ : ℂ) * Complex.I) ∈ grotzschRing s :=
      exp_mem_grotzschRing_disk hs0 (by rw [Real.exp_log hs0]; exact hs1) hθ.1 hθ.2
    have hcv : ContinuousAt (fun ξ : ℝ =>
        v (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Real.log s) :=
      continuousAt_uexp_line hvh hzmem
    have hce : ContinuousAt (fun ξ : ℝ =>
        (expGrad v ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Real.log s) :=
      Complex.continuous_re.continuousAt.comp (continuousAt_expGrad_line hs0 hvh hzmem)
    exact hcv.mul hce

/-! ### The Grötzsch potential energy identity -/

/-- **The Grötzsch potential energy identity.** For the Grötzsch potential `v` (harmonic on the
ring, `0` on the slit, `1` on the circle) and the collar slope `b` from its affine circle mean
`logCircleMean 0 v ξ = 2π + b·ξ`, the total Dirichlet energy over the Grötzsch ring equals
`ENNReal.ofReal b`.  The energy splits along the tip circle `|z| = s` into an inner-disk part
`ofReal (F_s)` and an outer-collar part `ofReal (b − F_s)`, where `F_s = ringFluxSlit v (log s)` is
the shared one-sided flux value; the pieces telescope because the flux is continuous across the tip
circle. -/
theorem dirichletEnergy_grotzschRing_eq_slope {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) {b : ℝ}
    (hslope : ∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + b * ξ) :
    dirichletEnergy v (grotzschRing s) = ENNReal.ofReal b := by
  have hLlog : Real.log s < 0 := Real.log_neg hs0 hs1
  -- collar hypotheses on the round annulus `{s < |z| < 1}`
  have hclos : {z : ℂ | s ≤ dist z 0 ∧ dist z 0 ≤ 1} ⊆ closure (grotzschRing s) := by
    rw [closure_grotzschRing hs0.le]
    exact fun z hz => Metric.mem_closedBall.mpr hz.2
  have hcont : ContinuousOn v {z : ℂ | s ≤ dist z 0 ∧ dist z 0 ≤ 1} := hvc.mono hclos
  have hann : InnerProductSpace.HarmonicOnNhd v (RoundAnnulus 0 s 1) :=
    hvh.mono (roundAnnulus_subset_grotzschRing hs0.le)
  have hannrange : ∀ z ∈ RoundAnnulus 0 s 1, 0 ≤ v z ∧ v z ≤ 1 :=
    fun z hz => hvrange z (roundAnnulus_subset_grotzschRing hs0.le hz)
  -- the shared flux value `F_s = ringFluxSlit v (log s) = ringFlux v (log s)`
  set Fs : ℝ := ringFluxSlit v (Real.log s) with hFs
  have hFcont : ContinuousAt (ringFluxSlit v) (Real.log s) :=
    continuousAt_ringFluxSlit_logS hs0 hs1 hvh hvc hv0 hvrange
  -- inner flux `F(bₙ) → F_s` with `bₙ = log s − 1/(n+2) ↑ log s`
  have hone_div_add_two : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hcomp := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    refine hcomp.congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring_nf
  have hbₙtend : Tendsto (fun n : ℕ => ringFluxSlit v (Real.log s - 1 / (n + 2))) atTop (𝓝 Fs) := by
    refine hFcont.tendsto.comp ?_
    have h2 := (tendsto_const_nhds (x := Real.log s)).sub hone_div_add_two
    rw [sub_zero] at h2
    refine h2.congr fun n => ?_
    ring
  -- INNER: `D(ball s) = ofReal F_s`
  have hinnerdisk : dirichletEnergy v (RoundAnnulus 0 0 s) = ENNReal.ofReal Fs :=
    dirichletEnergy_innerDisk_eq_ofReal hs0 hs1 hvh hvc hv0 hv1 hvrange hbₙtend
  have hball_eq_ann : dirichletEnergy v (Metric.ball (0 : ℂ) s) = ENNReal.ofReal Fs := by
    rw [← hinnerdisk]
    refine dirichletEnergy_congr_ae ?_
    rw [ae_eq_set]
    refine ⟨measure_mono_null (fun z hz => ?_) (measure_singleton (0 : ℂ)), ?_⟩
    · -- `ball s \ RoundAnnulus 0 0 s ⊆ {0}`
      have hzs : dist z 0 < s := Metric.mem_ball.mp hz.1
      have hznotin : z ∉ RoundAnnulus 0 0 s := hz.2
      simp only [RoundAnnulus, Set.mem_setOf_eq, not_and, not_lt] at hznotin
      have hle : dist z 0 ≤ 0 := by
        by_contra hpos
        exact absurd (hznotin (lt_of_not_ge hpos)) (not_le.mpr hzs)
      simp only [Set.mem_singleton_iff]
      rw [← dist_eq_zero]; exact le_antisymm hle dist_nonneg
    · refine measure_mono_null (fun z hz => ?_) measure_empty
      exact absurd (Metric.mem_ball.mpr hz.1.2) hz.2
  -- OUTER: `D(Ann(s,1)) = ofReal (b − F_s)`
  have houter : dirichletEnergy v (RoundAnnulus 0 s 1) = ENNReal.ofReal (b - Fs) := by
    rw [dirichletEnergy_fullAnnulus_eq_iSup hs0 hs1 hann hcont hv1 hannrange hslope]
    -- `ξ_n = log s·(n+1)/(n+2) ↓ log s`, flux `ringFlux v ξ_n → F_s`
    set ξf : ℕ → ℝ := fun n => Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) with hξf
    have hξftend : Tendsto ξf atTop (𝓝 (Real.log s)) := by
      have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
        have hsub := (tendsto_const_nhds (x := (1:ℝ))).sub hone_div_add_two
        rw [sub_zero] at hsub
        refine hsub.congr fun n => ?_
        have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
        field_simp; ring
      have := hc.const_mul (Real.log s)
      rw [mul_one] at this
      refine this.congr fun n => ?_
      rw [hξf]; ring
    have hfluxtend : Tendsto (fun n : ℕ => ringFlux v (ξf n)) atTop (𝓝 Fs) := by
      have hrfeq : (ringFlux v) = (ringFluxSlit v) :=
        funext fun ξ => (ringFluxSlit_eq_ringFlux v ξ).symm
      rw [hrfeq]
      exact hFcont.tendsto.comp hξftend
    have hξfmem : ∀ k : ℕ, ξf k ∈ Ioo (Real.log s) 0 := by
      intro k
      refine ⟨?_, ?_⟩
      · have hck : ((k : ℝ) + 1) / ((k : ℝ) + 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        have hlt : Real.log s * 1 < Real.log s * (((k : ℝ) + 1) / ((k : ℝ) + 2)) :=
          mul_lt_mul_of_neg_left hck hLlog
        rw [hξf]; simp only [mul_div_assoc]; nlinarith [hlt]
      · rw [hξf]; simp only [mul_div_assoc]
        exact mul_neg_of_neg_of_pos hLlog (by positivity)
    have hincmono : Monotone fun n : ℕ => b - ringFlux v (ξf n) := by
      have hFmono : MonotoneOn (ringFlux v) (Ioo (Real.log s) 0) :=
        ringFlux_monotoneOn hs0 hann
      intro n m hnm
      -- `ξf` is antitone (decreasing to log s), so `ringFlux v (ξf ·)` is antitone
      have hξfanti : ξf m ≤ ξf n := by
        rw [hξf]; simp only
        rw [mul_div_assoc, mul_div_assoc]
        apply mul_le_mul_of_nonpos_left _ hLlog.le
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hc : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
        nlinarith [hc]
      have := hFmono (hξfmem m) (hξfmem n) hξfanti
      simp only; linarith
    have hbFstend : Tendsto (fun n : ℕ => b - ringFlux v (ξf n)) atTop (𝓝 (b - Fs)) :=
      tendsto_const_nhds.sub hfluxtend
    rw [iSup_ofReal_of_tendsto hincmono hbFstend]
  -- `0 ≤ b − ringFlux v ξ` for `ξ ∈ (log s, 0)`: flux monotone up to the boundary slope `b`
  have hbnd := ringFlux_tendsto_slope hs0 hs1 hann hcont hv1 hannrange hslope
  have hringmono : MonotoneOn (ringFlux v) (Ioo (Real.log s) 0) := ringFlux_monotoneOn hs0 hann
  have hringle_b : ∀ ξ ∈ Ioo (Real.log s) 0, ringFlux v ξ ≤ b := by
    intro ξ hξ
    refine ge_of_tendsto hbnd ?_
    filter_upwards [Ioo_mem_nhdsLT hξ.2] with ζ hζ
    have hζmem : ζ ∈ Ioo (Real.log s) 0 := ⟨lt_trans hξ.1 hζ.1, hζ.2⟩
    exact hringmono hξ hζmem (le_of_lt hζ.1)
  -- `0 ≤ F_s` : the slit flux is `≥ 0` below `log s`, so its limit `F_s` is `≥ 0`
  have hFslitmono : MonotoneOn (ringFluxSlit v) (Iio (Real.log s)) :=
    ringFluxSlit_monotoneOn hs0 hs1 hvh hvc hv0 hv1 hvrange
  have hFsnn : 0 ≤ Fs := by
    have hFnn : ∀ ξ : ℝ, ξ < Real.log s → 0 ≤ ringFluxSlit v ξ := by
      intro ξ hξ
      refine le_of_tendsto (ringFluxSlit_tendsto_atBot_zero hs0 hs1 hvh hvc hv0 hvrange) ?_
      filter_upwards [Iic_mem_atBot ξ] with ζ hζ
      have hζmem : ζ ∈ Iio (Real.log s) := lt_of_le_of_lt hζ hξ
      exact hFslitmono hζmem (Set.mem_Iio.mpr hξ) hζ
    refine ge_of_tendsto' hbₙtend (fun n => hFnn _ ?_)
    have hp : (0:ℝ) < 1 / ((n:ℝ) + 2) := by positivity
    linarith
  -- `0 ≤ b − F_s` : `F_s` is a limit of collar flux values `ringFlux v ηf n`, each `≤ b`
  have hbFsnn : 0 ≤ b - Fs := by
    -- `ηf n = log s·(n+1)/(n+2) ↓ log s` stays in `(log s, 0)` and `ringFluxSlit v ηf n → F_s`
    set ηf : ℕ → ℝ := fun n => Real.log s * ((n : ℝ) + 1) / ((n : ℝ) + 2) with hηf
    have hηfmem : ∀ n, ηf n ∈ Ioo (Real.log s) 0 := by
      intro n
      refine ⟨?_, ?_⟩
      · have hcn : ((n : ℝ) + 1) / ((n : ℝ) + 2) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        have hlt : Real.log s * 1 < Real.log s * (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
          mul_lt_mul_of_neg_left hcn hLlog
        rw [hηf]; simp only [mul_div_assoc]; nlinarith [hlt]
      · rw [hηf]; simp only [mul_div_assoc]
        exact mul_neg_of_neg_of_pos hLlog (by positivity)
    have hηftend : Tendsto ηf atTop (𝓝 (Real.log s)) := by
      have hc : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
        have hsub := (tendsto_const_nhds (x := (1:ℝ))).sub hone_div_add_two
        rw [sub_zero] at hsub
        refine hsub.congr fun n => ?_
        have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
        field_simp; ring
      have hmul := hc.const_mul (Real.log s)
      rw [mul_one] at hmul
      refine hmul.congr fun n => ?_
      rw [hηf]; ring
    have hFtend : Tendsto (fun n => ringFluxSlit v (ηf n)) atTop (𝓝 Fs) :=
      hFcont.tendsto.comp hηftend
    have hFle : Fs ≤ b := by
      refine le_of_tendsto' hFtend (fun n => ?_)
      rw [ringFluxSlit_eq_ringFlux]
      exact hringle_b (ηf n) (hηfmem n)
    linarith
  -- ASSEMBLE
  rw [dirichletEnergy_grotzschRing_eq_ball hs0.le, dirichletEnergy_ball_split hs1,
    hball_eq_ann, houter, ← ENNReal.ofReal_add hFsnn hbFsnn]
  congr 1; ring

end RiemannDynamics
