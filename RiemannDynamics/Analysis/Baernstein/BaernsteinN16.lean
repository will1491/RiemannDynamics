/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Baernstein.CircularPolyaSzegoExtension
import RiemannDynamics.Analysis.Baernstein.BaernsteinComparison
import RiemannDynamics.Analysis.GrotzschRing.GrotzschPotential
import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy

/-!
# Baernstein N16: the star comparison `J ≤ 0` and circle-means comparison

Structural ingredients of Baernstein's circular-symmetrization comparison, in the log-polar star
formulation. For a ring potential `u` on a ring domain `U` (with `E = frontier U ∩ ball` the inner
continuum, `grotzschOuter` the outer circle) and the Grötzsch potential `v`, one compares the two
Baernstein star surfaces `ω̃★ := starPlane 0 (indicator U u)` and `ṽ★ := starPlane 0 (indicator
(grotzschRing s) v)` on the log-polar half-strip `S = {re < 0, 0 < im < π}` via the tilted maximum
principle.

* `starPlane_aperture_lipschitz` — the star surface is Lipschitz in the aperture `θ` (fixed
  log-radius) with constant `2·M` when the potential is `≤ M` on the circle.
* `starFunction_apex_toReal` (imported) gives the apex value as `logCircleMean`.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

/-- Pointwise `ENNReal` estimate: `min a c ≤ min b c + (a − b)` when `b ≤ a`. -/
theorem min_le_min_add_sub {a b c : ℝ≥0∞} (hba : b ≤ a) :
    min a c ≤ min b c + (a - b) := by
  rcases le_total a c with hac | hac
  · rw [min_eq_left hac, min_eq_left (le_trans hba hac), add_tsub_cancel_of_le hba]
  · rw [min_eq_right hac]
    rcases le_total b c with hbc | hbc
    · rw [min_eq_left hbc]
      calc c ≤ a := hac
        _ = b + (a - b) := (add_tsub_cancel_of_le hba).symm
    · rw [min_eq_right hbc]; exact le_add_right le_rfl

/-! ### N16.1 Apex saturation from a zero of the potential -/

/-- **Positive-measure sublevel arc from a zero.** For a continuous `F : ℝ → ℝ` with a zero
`F φ₀ = 0` at `φ₀ ∈ [0, 2π]` and a threshold `t₀ > 0`, the super-level set
`{φ ∈ [0, 2π] | t₀ < F φ}` has measure `≤ ofReal (2π − c₀)` for some `c₀ > 0`: continuity yields an
interval around `φ₀`
(clipped to `[0, 2π]`) on which `F < t₀`, and its complement is the super-level set. -/
theorem sublevel_arc_measure {F : ℝ → ℝ} (hF : Continuous F) {φ₀ t₀ : ℝ}
    (hφ₀ : φ₀ ∈ Icc (0 : ℝ) (2 * π)) (hFφ₀ : F φ₀ = 0) (ht₀ : 0 < t₀) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      volume {φ ∈ Icc (0 : ℝ) (2 * π) | t₀ < F φ} ≤ ENNReal.ofReal (2 * π - c₀) := by
  -- Continuity: `F < t₀` on `Ioo (φ₀ − δ) (φ₀ + δ)` for some `δ > 0`.
  have hopen : IsOpen (F ⁻¹' Iio t₀) := isOpen_Iio.preimage hF
  have hmem : φ₀ ∈ F ⁻¹' Iio t₀ := by simp [hFφ₀, ht₀]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen φ₀ hmem
  -- The clipped open interval `I = Ioo a b` with `a = max (φ₀ − δ) 0`, `b = min (φ₀ + δ) (2π)`.
  set a : ℝ := max (φ₀ - δ / 2) 0 with hadef
  set b : ℝ := min (φ₀ + δ / 2) (2 * π) with hbdef
  rcases hφ₀ with ⟨h0, h2π⟩
  have hπ0 : (0 : ℝ) < 2 * π := by positivity
  have hab : a < b := by
    rw [hadef, hbdef]
    refine max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) hπ0)
  have hasub : 0 ≤ a := le_max_right _ _
  have hbsub : b ≤ 2 * π := min_le_right _ _
  have hIoosub : Ioo a b ⊆ Icc (0 : ℝ) (2 * π) :=
    fun x hx => ⟨le_of_lt (lt_of_le_of_lt hasub hx.1), le_of_lt (lt_of_lt_of_le hx.2 hbsub)⟩
  set c₀ : ℝ := b - a with hc₀def
  have hc₀ : 0 < c₀ := by rw [hc₀def]; linarith
  refine ⟨c₀, hc₀, ?_⟩
  -- On `Ioo a b`, `F < t₀`, so `Ioo a b` misses the super-level set.
  have hsub : Ioo a b ⊆ {φ ∈ Icc (0 : ℝ) (2 * π) | F φ ≤ t₀} := by
    intro φ hφ
    have hφball : φ ∈ Metric.ball φ₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      rcases hφ with ⟨hφa, hφb⟩
      constructor
      · have : a ≥ φ₀ - δ / 2 := le_max_left _ _
        linarith
      · have : b ≤ φ₀ + δ / 2 := min_le_left _ _
        linarith
    have hFφ : F φ < t₀ := hball hφball
    refine ⟨⟨?_, ?_⟩, hFφ.le⟩
    · exact le_trans (le_max_right _ _) (le_of_lt hφ.1)
    · exact le_trans (le_of_lt hφ.2) (min_le_right _ _)
  -- Complement bound: super-level ⊆ Icc 0 2π \ Ioo a b.
  have hcompl : {φ ∈ Icc (0 : ℝ) (2 * π) | t₀ < F φ} ⊆ Icc (0 : ℝ) (2 * π) \ Ioo a b := by
    intro φ hφ
    refine ⟨hφ.1, ?_⟩
    intro hin
    exact absurd (hsub hin).2 (not_le.mpr hφ.2)
  calc volume {φ ∈ Icc (0 : ℝ) (2 * π) | t₀ < F φ}
      ≤ volume (Icc (0 : ℝ) (2 * π) \ Ioo a b) := measure_mono hcompl
    _ = volume (Icc (0 : ℝ) (2 * π)) - volume (Ioo a b) :=
        measure_diff hIoosub measurableSet_Ioo.nullMeasurableSet
          (ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ofReal_ne_top) le_rfl)
    _ = ENNReal.ofReal (2 * π - c₀) := by
        rw [Real.volume_Icc, Real.volume_Ioo, sub_zero, hc₀def,
          ← ENNReal.ofReal_sub _ (le_of_lt (by linarith))]

/-- **Apex saturation of the star function.** If `f` is continuous, nonnegative and measurable on
the circle of radius `r > 0` about the origin and vanishes at some point of that circle, then near
full aperture the star deficit is `o(π − θ)`: for every `ε > 0` there is `θ₀ ∈ [0, π)` with
`(starFunction 0 f r π).toReal − (starFunction 0 f r θ).toReal ≤ ε · (π − θ)` for all
`θ ∈ [θ₀, π]`. The zero and continuity give an arc of positive measure on which `f` is below the
threshold `ε/2`; the distribution function there is bounded away from `2π`, so the top part of the
layer-cake integral vanishes once `θ` is close enough to `π`. -/
theorem starFunction_apex_saturation {f : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (Metric.sphere (0 : ℂ) r)) (hf0 : ∀ z, 0 ≤ f z)
    (hzero : ∃ z ∈ Metric.sphere (0 : ℂ) r, f z = 0) :
    ∀ ε > 0, ∃ θ₀ ∈ Ico (0 : ℝ) π, ∀ θ ∈ Icc θ₀ π,
      (starFunction (0 : ℂ) f r π).toReal - (starFunction (0 : ℂ) f r θ).toReal ≤ ε * (π - θ) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  -- The circle sampling map and its continuity.
  set F : ℝ → ℝ := fun φ => f ((r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I)) with hFdef
  have hmemF : ∀ φ : ℝ, (r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I)
      ∈ Metric.sphere (0 : ℂ) r := by
    intro φ; simp [Complex.norm_exp, abs_of_pos hr]
  have hFcont : Continuous F := by
    have hparam : Continuous fun φ : ℝ =>
        (r : ℂ) * Complex.exp (((φ - π : ℝ) : ℂ) * Complex.I) := by fun_prop
    exact hcont.comp_continuous hparam hmemF
  have hFnn : ∀ φ : ℝ, 0 ≤ F φ := fun φ => hf0 _
  -- A zero of `F` in `[0, 2π]`, extracted from the sphere zero via polar form.
  obtain ⟨z, hzsph, hzf⟩ := hzero
  have hznorm : ‖z‖ = r := by rwa [Metric.mem_sphere, dist_zero_right] at hzsph
  set φ₀ : ℝ := Complex.arg z + π with hφ₀def
  have hzpolar : (r : ℂ) * Complex.exp (((φ₀ - π : ℝ) : ℂ) * Complex.I) = z := by
    rw [hφ₀def]
    have : ((Complex.arg z + π - π : ℝ) : ℂ) = (Complex.arg z : ℂ) := by push_cast; ring
    rw [this, ← hznorm, Complex.norm_mul_exp_arg_mul_I]
  have hFφ₀ : F φ₀ = 0 := by rw [hFdef]; simp only; rw [hzpolar, hzf]
  have hφ₀mem : φ₀ ∈ Icc (0 : ℝ) (2 * π) := by
    rw [hφ₀def]
    have h1 : -π < Complex.arg z := Complex.neg_pi_lt_arg z
    have h2 : Complex.arg z ≤ π := Complex.arg_le_pi z
    exact ⟨by linarith, by linarith⟩
  -- The angular profile equals `ofReal ∘ F`.
  set g : ℝ → ℝ≥0∞ := fun φ =>
    ENNReal.ofReal ((angularProfile 0 (fun z => ENNReal.ofReal (f z)) r φ).toReal) with hgdef
  have hgF : ∀ φ : ℝ, g φ = ENNReal.ofReal (F φ) := by
    intro φ
    rw [hgdef]; simp only [angularProfile, zero_add]
    rw [ofReal_toReal_ofReal]
  intro ε hε
  set t₀ : ℝ := ε / 2 with ht₀def
  have ht₀ : 0 < t₀ := by rw [ht₀def]; positivity
  -- Arc bound on the distribution function at level `t₀`.
  obtain ⟨c₀, hc₀, harc⟩ := sublevel_arc_measure hFcont hφ₀mem hFφ₀ ht₀
  set θ₀ : ℝ := max 0 (π - c₀ / 2) with hθ₀def
  refine ⟨θ₀, ⟨le_max_left _ _, ?_⟩, ?_⟩
  · rw [hθ₀def]; exact max_lt hπ (by linarith)
  intro θ hθ
  rcases hθ with ⟨hθlo, hθhi⟩
  have hθ0 : 0 ≤ θ := le_trans (le_max_left _ _) hθlo
  have hθbig : 2 * π - c₀ ≤ 2 * θ := by
    have : π - c₀ / 2 ≤ θ := le_trans (le_max_right _ _) hθlo
    linarith
  -- Layer-cake for both apertures; `D` is the distribution function of `g`.
  have hπle : π ≤ 2 * π / 2 := by linarith
  have hθle : θ ≤ 2 * π / 2 := by linarith
  set D : ℝ → ℝ≥0∞ := fun t => distribFun (2 * π) g (ENNReal.ofReal t) with hDdef
  -- `D t ≤ ofReal (2π)` always.
  have hDle : ∀ t : ℝ, D t ≤ ENNReal.ofReal (2 * π) := fun t => distribFun_le_ofReal_T _
  -- Distribution at `t₀` is bounded by `ofReal (2π − c₀)` via the arc.
  have hDt₀ : D t₀ ≤ ENNReal.ofReal (2 * π - c₀) := by
    have hset : {φ ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t₀ < g φ}
        = {φ ∈ Icc (0 : ℝ) (2 * π) | t₀ < F φ} := by
      ext φ
      simp only [mem_setOf_eq, hgF φ,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht₀.le]
    calc D t₀ = volume {φ ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t₀ < g φ} := rfl
      _ = volume {φ ∈ Icc (0 : ℝ) (2 * π) | t₀ < F φ} := by rw [hset]
      _ ≤ ENNReal.ofReal (2 * π - c₀) := harc
  -- Pointwise comparison of the two layer-cake integrands on `Ioi 0`.
  have hpt : ∀ t ∈ Ioi (0 : ℝ), min (ENNReal.ofReal (2 * π)) (D t)
      ≤ min (ENNReal.ofReal (2 * θ)) (D t)
        + (Ioo (0 : ℝ) t₀).indicator (fun _ => ENNReal.ofReal (2 * (π - θ))) t := by
    intro t ht
    rcases lt_or_ge t t₀ with htt₀ | htt₀
    · rw [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) t₀ from ⟨ht, htt₀⟩)]
      have hsub2 : ENNReal.ofReal (2 * (π - θ))
          = ENNReal.ofReal (2 * π) - ENNReal.ofReal (2 * θ) := by
        have : (2 : ℝ) * (π - θ) = 2 * π - 2 * θ := by ring
        rw [this, ENNReal.ofReal_sub (2 * π) (by positivity)]
      rw [hsub2]
      exact min_le_min_add_sub (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [Set.indicator_of_notMem (by simp only [mem_Ioo, not_and, not_lt]; exact fun _ => htt₀)]
      rw [add_zero]
      have hDtsmall : D t ≤ ENNReal.ofReal (2 * θ) := by
        calc D t ≤ D t₀ := distribFun_antitone (ENNReal.ofReal_le_ofReal htt₀)
          _ ≤ ENNReal.ofReal (2 * π - c₀) := hDt₀
          _ ≤ ENNReal.ofReal (2 * θ) := ENNReal.ofReal_le_ofReal (by linarith)
      rw [min_eq_right hDtsmall, min_eq_right (le_trans hDtsmall (ENNReal.ofReal_le_ofReal
        (by linarith)))]
  -- Assemble: `star(π) ≤ star(θ) + ofReal (ε (π − θ))`.
  have hstar_ineq : starFunction (0 : ℂ) f r π
      ≤ starFunction (0 : ℂ) f r θ + ENNReal.ofReal (ε * (π - θ)) := by
    rw [show starFunction (0 : ℂ) f r π = starProfile (2 * π) g π from rfl,
      show starFunction (0 : ℂ) f r θ = starProfile (2 * π) g θ from rfl,
      starProfile_eq_lintegral_min (by positivity) hπ.le hπle,
      starProfile_eq_lintegral_min (by positivity) hθ0 hθle]
    calc ∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * π)) (D t)
        ≤ ∫⁻ t in Ioi (0 : ℝ), (min (ENNReal.ofReal (2 * θ)) (D t)
            + (Ioo (0 : ℝ) t₀).indicator (fun _ => ENNReal.ofReal (2 * (π - θ))) t) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = (∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ)) (D t))
            + ∫⁻ t in Ioi (0 : ℝ),
                (Ioo (0 : ℝ) t₀).indicator (fun _ => ENNReal.ofReal (2 * (π - θ))) t :=
          lintegral_add_right _ (Measurable.indicator measurable_const measurableSet_Ioo)
      _ ≤ (∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ)) (D t))
            + ENNReal.ofReal (ε * (π - θ)) := by
          gcongr
          rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const]
          have hvol : (volume.restrict (Ioi (0 : ℝ))) (Ioo (0 : ℝ) t₀) = ENNReal.ofReal t₀ := by
            rw [Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioi,
              sup_of_le_right le_rfl, Real.volume_Ioo, sub_zero]
          rw [hvol, ← ENNReal.ofReal_mul (by linarith [hθhi])]
          exact ENNReal.ofReal_le_ofReal (by rw [ht₀def]; nlinarith [hθhi])
  -- Convert to real values, using compactness for an upper bound on `f` on the circle.
  obtain ⟨zM, hzMsph, hzMmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hcont
  have hbdd : ∀ φ : ℝ, f ((0 : ℂ) + (r : ℂ) * Complex.exp (φ * Complex.I)) ≤ f zM := by
    intro φ
    have hmem : (r : ℂ) * Complex.exp (φ * Complex.I) ∈ Metric.sphere (0 : ℂ) r := by
      simp [Complex.norm_exp, abs_of_pos hr]
    simpa using hzMmax hmem
  have hfinπ : starFunction (0 : ℂ) f r π < ⊤ :=
    starFunction_lt_top hπ.le le_rfl ⟨f zM, hbdd⟩
  have hfinθ : starFunction (0 : ℂ) f r θ < ⊤ :=
    starFunction_lt_top hθ0 (by linarith) ⟨f zM, hbdd⟩
  have htoReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinθ.ne, ENNReal.ofReal_ne_top⟩) hstar_ineq
  rw [ENNReal.toReal_add hfinθ.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by nlinarith [hθhi, hε.le])] at htoReal
  linarith [htoReal]

/-! ### N16.3 Aperture-Lipschitz continuity of the star surface -/

/-- **Aperture-monotone increment bound (profile level).** For a nonnegative profile `g` on `[0, T]`
bounded above by `ofReal M` on `Icc 0 T` (`0 ≤ M`), and half-apertures `0 ≤ θ' ≤ θ ≤ T/2`, the star
profile increment is controlled linearly: `starProfile T g θ ≤ starProfile T g θ' +
ofReal (2 · M · (θ − θ'))`. The distribution function vanishes above level `M`, so the layer-cake
integrand differs only on `t ∈ (0, M)`, where it grows by at most `ofReal (2θ) − ofReal (2θ')`. -/
theorem starProfile_incr_le {T M : ℝ} {g : ℝ → ℝ≥0∞} (hT : 0 ≤ T)
    (hg : ∀ x ∈ Icc (0 : ℝ) T, g x ≤ ENNReal.ofReal M) {θ θ' : ℝ}
    (hθ'0 : 0 ≤ θ') (hθθ' : θ' ≤ θ) (hθT : θ ≤ T / 2) :
    starProfile T g θ ≤ starProfile T g θ' + ENNReal.ofReal (2 * M * (θ - θ')) := by
  have hθ0 : 0 ≤ θ := le_trans hθ'0 hθθ'
  rw [starProfile_eq_lintegral_min hT hθ0 hθT,
    starProfile_eq_lintegral_min hT hθ'0 (le_trans hθθ' hθT)]
  set D : ℝ → ℝ≥0∞ := fun t => distribFun T g (ENNReal.ofReal t) with hDdef
  -- Above level `M` the distribution function vanishes.
  have hDzero : ∀ t : ℝ, M ≤ t → D t = 0 := by
    intro t ht
    have : {x ∈ Icc (0 : ℝ) T | ENNReal.ofReal t < g x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx
      exact not_lt.mpr (le_trans (hg x hx) (ENNReal.ofReal_le_ofReal ht))
    simp only [hDdef, distribFun, this, measure_empty]
  -- Pointwise bound on `Ioi 0`, splitting at `M`.
  have hpt : ∀ t ∈ Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ)) (D t)
      ≤ min (ENNReal.ofReal (2 * θ')) (D t)
        + (Ioo (0 : ℝ) M).indicator (fun _ => ENNReal.ofReal (2 * (θ - θ'))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases lt_or_ge t M with htM | htM
    · rw [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) M from ⟨ht0, htM⟩)]
      have hsub : ENNReal.ofReal (2 * (θ - θ'))
          = ENNReal.ofReal (2 * θ) - ENNReal.ofReal (2 * θ') := by
        have : (2 : ℝ) * (θ - θ') = 2 * θ - 2 * θ' := by ring
        rw [this, ENNReal.ofReal_sub (2 * θ) (by positivity)]
      rw [hsub]
      exact min_le_min_add_sub (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [hDzero t htM, min_zero, min_zero]; exact zero_le _
  calc ∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ)) (D t)
      ≤ ∫⁻ t in Ioi (0 : ℝ), (min (ENNReal.ofReal (2 * θ')) (D t)
          + (Ioo (0 : ℝ) M).indicator (fun _ => ENNReal.ofReal (2 * (θ - θ'))) t) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ')) (D t))
          + ∫⁻ t in Ioi (0 : ℝ),
              (Ioo (0 : ℝ) M).indicator (fun _ => ENNReal.ofReal (2 * (θ - θ'))) t :=
        lintegral_add_right _ (Measurable.indicator measurable_const measurableSet_Ioo)
    _ ≤ (∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ')) (D t))
          + ENNReal.ofReal (2 * M * (θ - θ')) := by
        gcongr
        rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const]
        have hvol : (volume.restrict (Ioi (0 : ℝ))) (Ioo (0 : ℝ) M) = ENNReal.ofReal M := by
          rw [Measure.restrict_apply measurableSet_Ioo,
            Ioo_inter_Ioi, sup_of_le_right le_rfl, Real.volume_Ioo, sub_zero]
        rw [hvol, ← ENNReal.ofReal_mul (by linarith [hθθ'])]
        exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- The angular profile `g φ = ofReal ((angularProfile p (ofReal ∘ u) r φ).toReal)` of a potential
`u` bounded above by `M` on the circle of radius `r` is bounded above by `ofReal M`. -/
theorem angularProfile_toReal_le {p : ℂ} {u : ℂ → ℝ} {r M : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ φ : ℝ, u (p + (r : ℂ) * Complex.exp (φ * Complex.I)) ≤ M) (φ : ℝ) :
    ENNReal.ofReal
        ((angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal) ≤ ENNReal.ofReal M := by
  simp only [angularProfile]
  refine ENNReal.ofReal_le_ofReal ?_
  refine ENNReal.toReal_le_of_le_ofReal hM ?_
  exact ENNReal.ofReal_le_ofReal (hbdd (φ - π))

/-- **Uniform upper bound for the star function.** For `u ≤ M` (`0 ≤ M`) on the circle of radius `r`
and half-aperture `0 ≤ θ ≤ π`, `(starFunction p u r θ).toReal ≤ 2 · M · θ`: each layer-cake
integrand `min (2θ) (D t)` is `≤ ofReal (2θ)` and `D t = 0` above level `M`. -/
theorem starFunction_toReal_le {p : ℂ} {u : ℂ → ℝ} {r M θ : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ φ : ℝ, u (p + (r : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    (starFunction p u r θ).toReal ≤ 2 * M * θ := by
  set g : ℝ → ℝ≥0∞ := fun φ => ENNReal.ofReal
    ((angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal) with hgdef
  have hπ2 : θ ≤ 2 * π / 2 := by linarith [Real.pi_pos]
  set D : ℝ → ℝ≥0∞ := fun t => distribFun (2 * π) g (ENNReal.ofReal t) with hDdef
  have hDzero : ∀ t : ℝ, M ≤ t → D t = 0 := by
    intro t ht
    have hemp : {x ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t < g x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro _
      exact not_lt.mpr (le_trans (angularProfile_toReal_le hM hbdd x)
        (ENNReal.ofReal_le_ofReal ht))
    simp only [hDdef, distribFun, hemp, measure_empty]
  have hle : starFunction p u r θ ≤ ENNReal.ofReal (2 * θ * M) := by
    rw [show starFunction p u r θ = starProfile (2 * π) g θ from rfl,
      starProfile_eq_lintegral_min (by positivity) hθ0 hπ2]
    calc ∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ)) (D t)
        ≤ ∫⁻ t in Ioi (0 : ℝ),
            (Ioo (0 : ℝ) M).indicator (fun _ => ENNReal.ofReal (2 * θ)) t := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro t ht
          rcases lt_or_ge t M with htM | htM
          · rw [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) M from ⟨ht, htM⟩)]
            exact min_le_left _ _
          · have hnotmem : t ∉ Ioo (0 : ℝ) M := by
              simp only [mem_Ioo, not_and, not_lt]; exact fun _ => htM
            rw [Set.indicator_of_notMem hnotmem, hDzero t htM, min_zero]
      _ = ENNReal.ofReal (2 * θ * M) := by
          rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const,
            Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioi, sup_of_le_right le_rfl,
            Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  calc (starFunction p u r θ).toReal ≤ (ENNReal.ofReal (2 * θ * M)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = 2 * θ * M := ENNReal.toReal_ofReal (by positivity)
    _ = 2 * M * θ := by ring

/-- **Aperture increment bound for the star function.** For `u ≤ M` on the circle of radius `r`
(`0 ≤ M`) and half-apertures `0 ≤ θ' ≤ θ ≤ π`, the star value increment is linear:
`(starFunction p u r θ).toReal ≤ (starFunction p u r θ').toReal + 2 · M · (θ − θ')`. -/
theorem starFunction_incr_toReal_le {p : ℂ} {u : ℂ → ℝ} {r M θ θ' : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ φ : ℝ, u (p + (r : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ'0 : 0 ≤ θ') (hθθ' : θ' ≤ θ) (hθπ : θ ≤ π) :
    (starFunction p u r θ).toReal
      ≤ (starFunction p u r θ').toReal + 2 * M * (θ - θ') := by
  have hπ2 : θ ≤ 2 * π / 2 := by linarith [Real.pi_pos]
  have hincr := starProfile_incr_le (T := 2 * π) (M := M)
    (g := fun φ => ENNReal.ofReal
      ((angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal))
    (by positivity) (fun x _ => angularProfile_toReal_le hM hbdd x) hθ'0 hθθ' hπ2
  have hfin' : starFunction p u r θ' < ⊤ :=
    starFunction_lt_top hθ'0 (le_trans hθθ' hθπ) ⟨M, hbdd⟩
  have hincr' : starFunction p u r θ
      ≤ starFunction p u r θ' + ENNReal.ofReal (2 * M * (θ - θ')) := hincr
  have htoReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfin'.ne, ENNReal.ofReal_ne_top⟩) hincr'
  rw [ENNReal.toReal_add hfin'.ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by nlinarith [hθθ'])] at htoReal
  exact htoReal

/-- **Aperture-Lipschitz continuity of the star surface.** For two log-polar points `w, w'` with the
same log-radius `w.re = w'.re` and apertures `w.im, w'.im ∈ [0, π]`, if the potential `u` is bounded
above by `M` (`0 ≤ M`) on the circle of radius `exp w.re`, then the star surface values differ by at
most `2 · M · |w.im − w'.im|`. -/
theorem starPlane_aperture_lipschitz {p : ℂ} {u : ℂ → ℝ} {M : ℝ} {w w' : ℂ} (hM : 0 ≤ M)
    (hre : w.re = w'.re)
    (hbdd : ∀ φ : ℝ, u (p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ0 : 0 ≤ w.im) (hθπ : w.im ≤ π) (hθ'0 : 0 ≤ w'.im) (hθ'π : w'.im ≤ π) :
    |starPlane p u w - starPlane p u w'| ≤ 2 * M * |w.im - w'.im| := by
  set r : ℝ := Real.exp w.re with hrdef
  have hstarw : starPlane p u w = (starFunction p u r w.im).toReal := rfl
  have hstarw' : starPlane p u w' = (starFunction p u r w'.im).toReal := by
    simp only [starPlane, hrdef, hre]
  rw [hstarw, hstarw']
  rcases le_total w'.im w.im with hcmp | hcmp
  · have h := starFunction_incr_toReal_le hM hbdd hθ'0 hcmp hθπ
    have hge : (starFunction p u r w'.im).toReal ≤ (starFunction p u r w.im).toReal := by
      have hb : starFunction p u r w.im < ⊤ := starFunction_lt_top hθ0 hθπ ⟨M, hbdd⟩
      exact ENNReal.toReal_mono hb.ne (monotone_starFunction p u r hθ'0 hθ0 hcmp)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have h := starFunction_incr_toReal_le hM hbdd hθ0 hcmp hθ'π
    have hge : (starFunction p u r w.im).toReal ≤ (starFunction p u r w'.im).toReal := by
      have hb : starFunction p u r w'.im < ⊤ := starFunction_lt_top hθ'0 hθ'π ⟨M, hbdd⟩
      exact ENNReal.toReal_mono hb.ne (monotone_starFunction p u r hθ0 hθ'0 hcmp)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- **Apex value of the star surface.** At aperture `w.im = π` the star surface equals the log-polar
circle mean of `u` on the circle of radius `exp w.re`, for `u` measurable and nonnegative on that
circle. -/
theorem starPlane_apex_eq {p : ℂ} {u : ℂ → ℝ} {w : ℂ} (hw : w.im = π) (hu : Measurable u)
    (hnn : ∀ z ∈ Metric.sphere p (Real.exp w.re), 0 ≤ u z) :
    starPlane p u w = logCircleMean p u w.re := by
  have hr : (0 : ℝ) < Real.exp w.re := Real.exp_pos _
  have : starPlane p u w = (starFunction p u (Real.exp w.re) π).toReal := by
    simp only [starPlane, hw]
  rw [this, starFunction_apex_toReal hr hu hnn, Real.log_exp]

/-- **Aperture-to-apex bound.** For `u` measurable, nonnegative and bounded above by `M` (`0 ≤ M`)
on the circle of radius `exp w.re`, and aperture `w.im ∈ [0, π]`, the star surface value differs
from the apex circle mean by at most `2 · M · (π − w.im)`. -/
theorem starPlane_sub_logCircleMean_le {p : ℂ} {u : ℂ → ℝ} {M : ℝ} {w : ℂ} (hM : 0 ≤ M)
    (hu : Measurable u) (hnn : ∀ z ∈ Metric.sphere p (Real.exp w.re), 0 ≤ u z)
    (hbdd : ∀ φ : ℝ, u (p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ0 : 0 ≤ w.im) (hθπ : w.im ≤ π) :
    |starPlane p u w - logCircleMean p u w.re| ≤ 2 * M * (π - w.im) := by
  set w' : ℂ := Complex.mk w.re π with hw'def
  have hw're : w'.re = w.re := rfl
  have hw'im : w'.im = π := rfl
  have hlip := starPlane_aperture_lipschitz (p := p) (u := u) (M := M) (w := w) (w' := w')
    hM hw're.symm hbdd hθ0 hθπ (by rw [hw'im]; exact Real.pi_pos.le) (by rw [hw'im])
  have hapex : starPlane p u w' = logCircleMean p u w.re :=
    starPlane_apex_eq hw'im hu (by rw [hw're]; exact hnn)
  rw [hapex] at hlip
  rw [hw'im] at hlip
  calc |starPlane p u w - logCircleMean p u w.re| ≤ 2 * M * |w.im - π| := hlip
    _ = 2 * M * (π - w.im) := by rw [abs_of_nonpos (by linarith)]; ring

/-! ### N16.5(a) Bottom-edge decay of the star surface -/

/-- **Bottom-edge decay.** The star surface vanishes at aperture `0`, so for aperture
`w.im ∈ [0, π]` and a potential `u` bounded above by `M` (`0 ≤ M`) on the circle of radius
`exp w.re`, one has `starPlane p u w ≤ 2 · M · w.im`; in particular it tends to `0` as
`w.im → 0⁺`. -/
theorem starPlane_le_two_mul_aperture {p : ℂ} {u : ℂ → ℝ} {M : ℝ} {w : ℂ} (hM : 0 ≤ M)
    (hbdd : ∀ φ : ℝ, u (p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ0 : 0 ≤ w.im) (hθπ : w.im ≤ π) :
    starPlane p u w ≤ 2 * M * w.im := by
  set w' : ℂ := Complex.mk w.re 0 with hw'def
  have hw're : w'.re = w.re := rfl
  have hw'im : w'.im = 0 := rfl
  have hlip := starPlane_aperture_lipschitz (p := p) (u := u) (M := M) (w := w) (w' := w')
    hM hw're.symm hbdd hθ0 hθπ (by rw [hw'im]) (by rw [hw'im]; exact Real.pi_pos.le)
  have hbot : starPlane p u w' = 0 := by
    simp only [starPlane, hw'im, hw're]
    rw [starFunction_zero]; simp
  rw [hbot, sub_zero, hw'im, sub_zero, abs_of_nonneg hθ0] at hlip
  have hnn : (0 : ℝ) ≤ starPlane p u w := by
    have : starPlane p u w = (starFunction p u (Real.exp w.re) w.im).toReal := rfl
    rw [this]; exact ENNReal.toReal_nonneg
  calc starPlane p u w = |starPlane p u w| := (abs_of_nonneg hnn).symm
    _ ≤ 2 * M * w.im := hlip

/-! ### N16.5(c) Uniform (left-edge) upper bound of the star surface -/

/-- **Uniform upper bound.** For aperture `w.im ∈ [0, π]` and a potential `u` bounded above by `M`
(`0 ≤ M`) on the circle of radius `exp w.re`, `starPlane p u w ≤ 2 · π · M`. As `w.re → −∞` the
supremum of a potential continuous at (and vanishing at) the inner continuum tends to `0`, driving
the left-edge value of the star surface to `0`. -/
theorem starPlane_le_two_pi_mul {p : ℂ} {u : ℂ → ℝ} {M : ℝ} {w : ℂ} (hM : 0 ≤ M)
    (hbdd : ∀ φ : ℝ, u (p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ0 : 0 ≤ w.im) (hθπ : w.im ≤ π) :
    starPlane p u w ≤ 2 * π * M := by
  have hval : starPlane p u w = (starFunction p u (Real.exp w.re) w.im).toReal := rfl
  rw [hval]
  calc (starFunction p u (Real.exp w.re) w.im).toReal ≤ 2 * M * w.im :=
        starFunction_toReal_le hM hbdd hθ0 hθπ
    _ ≤ 2 * π * M := by nlinarith [hθπ, hθ0, hM]

/-! ### N16.4 Radial reach of the inner continuum -/

/-- **Radial reach.** If `E` is connected, contains the origin and the point `s > 0` on the real
axis, then every sphere of radius `r ∈ [0, s]` about `0` meets `E`: the norm image `‖·‖ '' E` is a
connected subset of `ℝ` containing `0` and `s`, hence contains the whole interval `[0, s]`. -/
theorem radial_reach {E : Set ℂ} {s : ℝ} (hs : 0 < s) (hEconn : IsConnected E)
    (h0 : (0 : ℂ) ∈ E) (hsE : (s : ℂ) ∈ E) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) s) :
    (Metric.sphere (0 : ℂ) r ∩ E).Nonempty := by
  have hcont : ContinuousOn (fun z : ℂ => ‖z‖) E := continuous_norm.continuousOn
  have hsub : Icc ((fun z : ℂ => ‖z‖) 0) ((fun z : ℂ => ‖z‖) (s : ℂ))
      ⊆ (fun z : ℂ => ‖z‖) '' E :=
    hEconn.isPreconnected.intermediate_value h0 hsE hcont
  have hnorm0 : (fun z : ℂ => ‖z‖) 0 = 0 := by simp
  have hnorms : (fun z : ℂ => ‖z‖) (s : ℂ) = s := by simp [abs_of_pos hs]
  rw [hnorm0, hnorms] at hsub
  obtain ⟨z, hzE, hznorm⟩ := hsub hr
  refine ⟨z, ?_, hzE⟩
  simp only [Metric.mem_sphere, dist_zero_right]
  exact hznorm

/-! ### N16.6 support: the full-circle log-radius set -/

/-- **Openness of the full-circle log-radius set.** For `U` open, the set
`A = {ξ | ξ < 0 ∧ sphere 0 (exp ξ) ⊆ U}` of log-radii whose full circle lies inside `U` is open in
`ℝ`: the sphere is compact, so a closed thickening of it stays inside `U`, and every nearby sphere
(radius `exp ξ'` with `ξ'` close to `ξ`) lies in that thickening via the radial scaling `z ↦
(exp ξ / exp ξ') • z`. -/
theorem fullCircle_set_isOpen {U : Set ℂ} (hU : IsOpen U) :
    IsOpen {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U} := by
  rw [Metric.isOpen_iff]
  rintro ξ ⟨hξ0, hξU⟩
  have hexpξ : (0 : ℝ) < Real.exp ξ := Real.exp_pos _
  -- A closed thickening of the compact sphere stays inside `U`.
  obtain ⟨δ, hδ0, hδU⟩ :=
    (isCompact_sphere (0 : ℂ) (Real.exp ξ)).exists_cthickening_subset_open hU hξU
  -- Continuity of `exp`: pick a log-radius radius `ρ` so that `|exp ξ' − exp ξ| ≤ δ` and `ξ' < 0`.
  have hcontExp : ContinuousAt Real.exp ξ := Real.continuous_exp.continuousAt
  have hnhds : Real.exp ⁻¹' (Metric.ball (Real.exp ξ) δ) ∈ nhds ξ :=
    hcontExp (Metric.ball_mem_nhds _ hδ0)
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := hnhds
  refine ⟨min ρ₁ (-ξ), lt_min hρ₁0 (by linarith), fun ξ' hξ' => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hξ'
  have hξ'ρ₁ : |ξ' - ξ| < ρ₁ := lt_of_lt_of_le hξ' (min_le_left _ _)
  have hξ'ξ : |ξ' - ξ| < -ξ := lt_of_lt_of_le hξ' (min_le_right _ _)
  have hξ'0 : ξ' < 0 := by
    rcases abs_lt.mp hξ'ξ with ⟨_, h2⟩; linarith
  refine ⟨hξ'0, fun z' hz' => ?_⟩
  -- `z'` on the sphere of radius `exp ξ'`; its scaled image lies on the sphere of radius `exp ξ`.
  have hz'norm : ‖z'‖ = Real.exp ξ' := by rwa [Metric.mem_sphere, dist_zero_right] at hz'
  have hexpξ' : (0 : ℝ) < Real.exp ξ' := Real.exp_pos _
  set z : ℂ := ((Real.exp ξ / Real.exp ξ' : ℝ) : ℂ) * z' with hzdef
  have hznorm : ‖z‖ = Real.exp ξ := by
    rw [hzdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), hz'norm, div_mul_cancel₀ _ hexpξ'.ne']
  have hzsph : z ∈ Metric.sphere (0 : ℂ) (Real.exp ξ) := by
    rw [Metric.mem_sphere, dist_zero_right, hznorm]
  -- `z'` is within `δ` of `z`, hence in the closed thickening.
  have hdist : dist z' z ≤ δ := by
    have hfac : z' - z = (((Real.exp ξ' - Real.exp ξ) / Real.exp ξ' : ℝ) : ℂ) * z' := by
      rw [hzdef]; push_cast
      field_simp
    rw [dist_eq_norm, hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, hz'norm]
    rw [abs_div, abs_of_pos hexpξ']
    rw [div_mul_cancel₀ _ hexpξ'.ne']
    have := hρ₁ (Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact hξ'ρ₁))
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at this
    exact this.le
  exact hδU (Metric.mem_cthickening_of_dist_le z' z δ (Metric.sphere (0 : ℂ) (Real.exp ξ))
    hzsph hdist)

/-- **Maximal full-circle interval.** If `A ⊆ ℝ` is open and bounded inside `Ioo lo hi` and
`ξ* ∈ A`, then the connected component of `ξ*` in `A` is an open interval `(α, β)` with
`lo ≤ α < ξ* < β ≤ hi`, `Ioo α β ⊆ A`, and `α ∉ A` (the left endpoint escapes `A`): openness of
`A` would otherwise extend the component past its infimum. -/
theorem maximal_interval {A : Set ℝ} {lo hi ξ : ℝ} (hA : IsOpen A) (hAsub : A ⊆ Ioo lo hi)
    (hξ : ξ ∈ A) :
    ∃ α β : ℝ, lo ≤ α ∧ α < ξ ∧ ξ < β ∧ β ≤ hi ∧ Ioo α β ⊆ A ∧ α ∉ A := by
  set C : Set ℝ := connectedComponentIn A ξ with hCdef
  have hξC : ξ ∈ C := mem_connectedComponentIn hξ
  have hCA : C ⊆ A := connectedComponentIn_subset A ξ
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCord : OrdConnected C := hCpre.ordConnected
  have hCbdd : C ⊆ Ioo lo hi := hCA.trans hAsub
  have hbelow : BddBelow C := ⟨lo, fun x hx => (hCbdd hx).1.le⟩
  have habove : BddAbove C := ⟨hi, fun x hx => (hCbdd hx).2.le⟩
  set α : ℝ := sInf C with hαdef
  set β : ℝ := sSup C with hβdef
  have hαle : α ≤ ξ := csInf_le hbelow hξC
  have hleβ : ξ ≤ β := le_csSup habove hξC
  -- `Ioo α β ⊆ C` via ordConnectedness and approximating from both sides.
  have hIooC : Ioo α β ⊆ C := by
    intro y hy
    obtain ⟨a, haC, hay⟩ := exists_lt_of_csInf_lt ⟨ξ, hξC⟩ hy.1
    obtain ⟨b, hbC, hyb⟩ := exists_lt_of_lt_csSup ⟨ξ, hξC⟩ hy.2
    exact hCord.out haC hbC ⟨hay.le, hyb.le⟩
  -- `α ∉ A`: openness of `A` would extend the component below its infimum.
  have hαnotA : α ∉ A := by
    intro hαA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA α hαA
    -- A point of `C` near `α` and the interval `(α − ε, α + ε) ⊆ A` glue to a bigger connected set.
    obtain ⟨a, haC, haα⟩ := exists_lt_of_csInf_lt ⟨ξ, hξC⟩ (by linarith : α < α + ε)
    have hIball : Ioo (α - ε) (α + ε) ⊆ A := by
      intro x hx
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have haInBall : a ∈ Ioo (α - ε) (α + ε) := ⟨by linarith [csInf_le hbelow haC], haα⟩
    have hunion : IsPreconnected (C ∪ Ioo (α - ε) (α + ε)) :=
      hCpre.union' ⟨a, haC, haInBall⟩ isPreconnected_Ioo
    have hunionA : C ∪ Ioo (α - ε) (α + ε) ⊆ A := union_subset hCA hIball
    have hsub : C ∪ Ioo (α - ε) (α + ε) ⊆ C :=
      hunion.subset_connectedComponentIn (Or.inl hξC) hunionA
    have hmemBig : α - ε / 2 ∈ C :=
      hsub (Or.inr ⟨by linarith, by linarith⟩)
    have := csInf_le hbelow hmemBig
    linarith
  -- Strictness of `α < ξ` and `ξ < β`: `ξ ∈ A` but `α ∉ A`, and `β ∉ C`-limit gives `ξ < β`.
  have hαξ : α < ξ := lt_of_le_of_ne hαle (fun h => hαnotA (h ▸ hξ))
  have hξβ : ξ < β := by
    rcases lt_or_eq_of_le hleβ with h | h
    · exact h
    · -- `ξ = β = sSup C`: then `A` open at `ξ` would push the sup up, contradiction.
      exfalso
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA ξ hξ
      have hIball : Ioo (ξ - ε) (ξ + ε) ⊆ A := by
        intro x hx
        apply hball
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hunion : IsPreconnected (C ∪ Ioo (ξ - ε) (ξ + ε)) :=
        hCpre.union' ⟨ξ, hξC, by constructor <;> linarith⟩ isPreconnected_Ioo
      have hsub : C ∪ Ioo (ξ - ε) (ξ + ε) ⊆ C :=
        hunion.subset_connectedComponentIn (Or.inl hξC) (union_subset hCA hIball)
      have hmemBig : ξ + ε / 2 ∈ C := hsub (Or.inr ⟨by linarith, by linarith⟩)
      have := le_csSup habove hmemBig
      rw [← hβdef, ← h] at this
      linarith
  have hloα : lo ≤ α := le_csInf ⟨ξ, hξC⟩ (fun x hx => (hCbdd hx).1.le)
  have hβhi : β ≤ hi := csSup_le ⟨ξ, hξC⟩ (fun x hx => (hCbdd hx).2.le)
  exact ⟨α, β, hloα, hαξ, hξβ, hβhi, hIooC.trans hCA, hαnotA⟩

/-- **An affine function with an interior maximum is constant.** If `g ξ = a + b·ξ` and the value at
some interior point `ξ₀ ∈ (α, β)` dominates `g` on all of `(α, β)`, then the slope `b` vanishes, so
`g` is constant on `(α, β)`: a nonzero slope makes `g` strictly monotone, contradicting the interior
maximum from one side. -/
theorem affine_interior_max_constant {a b α β ξ₀ : ℝ} (g : ℝ → ℝ)
    (hg : ∀ ξ ∈ Ioo α β, g ξ = a + b * ξ) (hξ₀ : ξ₀ ∈ Ioo α β)
    (hmax : ∀ ξ ∈ Ioo α β, g ξ ≤ g ξ₀) :
    b = 0 ∧ ∀ ξ ∈ Ioo α β, g ξ = g ξ₀ := by
  have hαβ : α < β := lt_trans hξ₀.1 hξ₀.2
  -- The slope is zero.
  have hb : b = 0 := by
    by_contra hbne
    rcases lt_or_gt_of_ne hbne with hbneg | hbpos
    · -- `b < 0`: `g` decreasing, a point below `ξ₀` exceeds `g ξ₀`.
      obtain ⟨y, hy₁, hy₂⟩ := exists_between hξ₀.1
      have hymem : y ∈ Ioo α β := ⟨hy₁, lt_trans hy₂ hξ₀.2⟩
      have := hmax y hymem
      rw [hg y hymem, hg ξ₀ hξ₀] at this
      nlinarith [hy₂]
    · -- `b > 0`: `g` increasing, a point above `ξ₀` exceeds `g ξ₀`.
      obtain ⟨y, hy₁, hy₂⟩ := exists_between hξ₀.2
      have hymem : y ∈ Ioo α β := ⟨lt_trans hξ₀.1 hy₁, hy₂⟩
      have := hmax y hymem
      rw [hg y hymem, hg ξ₀ hξ₀] at this
      nlinarith [hy₁]
  refine ⟨hb, fun ξ hξ => ?_⟩
  rw [hg ξ hξ, hg ξ₀ hξ₀, hb]; ring

/-- **A zero of the zero-extension on a sphere not contained in `U`.** If the sphere of radius `r`
about the origin is not contained in `U`, then the zero-extension `Set.indicator U u` vanishes at
some point of that sphere (a point off `U`, where the indicator is `0`). -/
theorem indicator_zero_of_sphere_not_subset {U : Set ℂ} {u : ℂ → ℝ} {r : ℝ}
    (hns : ¬ Metric.sphere (0 : ℂ) r ⊆ U) :
    ∃ z ∈ Metric.sphere (0 : ℂ) r, Set.indicator U u z = 0 := by
  rw [Set.not_subset] at hns
  obtain ⟨z, hzsph, hzU⟩ := hns
  exact ⟨z, hzsph, Set.indicator_of_notMem hzU u⟩

/-! ### N16.2 Affine circle mean on a full-circle sub-annulus -/

/-- The exponential maps the strip `{log R₁ < Re w < log R₂}` into the annulus
`{R₁ < |z| < R₂}`, for `0 < R₁ < R₂`. -/
theorem exp_mem_roundAnnulus_gen {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂) {w : ℂ}
    (ha : Real.log R₁ < w.re) (hb : w.re < Real.log R₂) :
    Complex.exp w ∈ RoundAnnulus 0 R₁ R₂ := by
  have h2 : (0 : ℝ) < R₂ := lt_trans h1 h12
  have hdist : dist (Complex.exp w) 0 = Real.exp w.re := by
    rw [dist_zero_right, Complex.norm_exp]
  simp only [RoundAnnulus, Set.mem_setOf_eq, hdist]
  refine ⟨?_, ?_⟩
  · calc R₁ = Real.exp (Real.log R₁) := (Real.exp_log h1).symm
      _ < Real.exp w.re := Real.exp_lt_exp.mpr ha
  · calc Real.exp w.re < Real.exp (Real.log R₂) := Real.exp_lt_exp.mpr hb
      _ = R₂ := Real.exp_log h2

/-- `expGrad u` is complex-differentiable at every point of the strip `{log R₁ < Re w < log R₂}`
whenever `u` is harmonic on `RoundAnnulus 0 R₁ R₂`. -/
theorem expGrad_differentiableAt_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) {w : ℂ}
    (ha : Real.log R₁ < w.re) (hb : w.re < Real.log R₂) :
    DifferentiableAt ℂ (expGrad u) w := by
  have hg : DifferentiableAt ℂ (gradC u) (Complex.exp w) :=
    (gradC_differentiableOn hu).differentiableAt
      ((isOpen_roundAnnulus 0 R₁ R₂).mem_nhds (exp_mem_roundAnnulus_gen h1 h12 ha hb))
  exact (hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w)

/-- The log-polar gradient `expGrad u` is continuous on the strip `{log R₁ < Re w < log R₂}`. -/
theorem continuousOn_expGrad_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) :
    ContinuousOn (expGrad u) {w : ℂ | Real.log R₁ < w.re ∧ w.re < Real.log R₂} := fun _ hw =>
  (expGrad_differentiableAt_gen h1 h12 hu hw.1 hw.2).continuousAt.continuousWithinAt

/-- The real part of `expGrad u` is continuous on the strip `{log R₁ < Re w < log R₂}`. -/
theorem continuousOn_expGrad_re_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) :
    ContinuousOn (fun w => (expGrad u w).re)
      {w : ℂ | Real.log R₁ < w.re ∧ w.re < Real.log R₂} :=
  Complex.continuous_re.comp_continuousOn (continuousOn_expGrad_gen h1 h12 hu)

/-- The derivative of `expGrad u` is continuous on the strip `{log R₁ < Re w < log R₂}`. -/
theorem continuousOn_deriv_expGrad_re_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) :
    ContinuousOn (fun w => (deriv (expGrad u) w).re)
      {w : ℂ | Real.log R₁ < w.re ∧ w.re < Real.log R₂} := by
  have hdiff : DifferentiableOn ℂ (expGrad u)
      {w : ℂ | Real.log R₁ < w.re ∧ w.re < Real.log R₂} :=
    fun w hw => (expGrad_differentiableAt_gen h1 h12 hu hw.1 hw.2).differentiableWithinAt
  have hanalytic := hdiff.analyticOnNhd (isOpen_logStrip _ _)
  exact Complex.continuous_re.comp_continuousOn
    (hanalytic.deriv_of_isOpen (isOpen_logStrip _ _)).continuousOn

/-- The log-polar pullback `u ∘ exp` is continuous on the strip `{log R₁ < Re w < log R₂}`. -/
theorem continuousOn_uexp_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) :
    ContinuousOn (fun w => u (Complex.exp w))
      {w : ℂ | Real.log R₁ < w.re ∧ w.re < Real.log R₂} := by
  intro w hw
  have hc : ContinuousAt u (Complex.exp w) :=
    (hu _ (exp_mem_roundAnnulus_gen h1 h12 hw.1 hw.2)).1.continuousAt
  exact (hc.comp Complex.continuous_exp.continuousAt).continuousWithinAt

/-- The circle mean `ξ ↦ ∫_{(−π,π)} u(e^{ξ+iθ}) dθ` has derivative the flux integrand
`∫_{(−π,π)} Re (expGrad u (ξ+θi)) dθ` at every `ξ ∈ (log R₁, log R₂)`. -/
theorem hasDerivAt_logCircleMean_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) {ξ : ℝ}
    (ha : Real.log R₁ < ξ) (hb : ξ < Real.log R₂) :
    HasDerivAt (fun x => logCircleMean 0 u x)
      (∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) ξ := by
  have hfun : (fun x => logCircleMean 0 u x)
      = fun x : ℝ => ∫ θ in Ioo (-π) π, u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) :=
    funext fun x => logCircleMean_zero_eq u x
  rw [hfun]
  exact hasDerivAt_integral_logStrip (continuousOn_uexp_gen h1 h12 hu)
    (continuousOn_expGrad_re_gen h1 h12 hu)
    (fun x θ hx1 hx2 => hasDerivAt_uexp_radial
      (differentiableAt_of_harmonicOnNhd hu
        (exp_mem_roundAnnulus_gen h1 h12 (by rw [re_logPolar]; exact hx1)
          (by rw [re_logPolar]; exact hx2))))
    ha hb

/-- The angle integral of `Re (deriv (expGrad u))` over a full circle vanishes on the strip. -/
theorem integral_re_deriv_expGrad_eq_zero_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) {ξ : ℝ}
    (ha : Real.log R₁ < ξ) (hb : ξ < Real.log R₂) :
    ∫ θ in Ioo (-π) π, (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re = 0 := by
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  have hkey : ∀ θ ∈ uIcc (-π) π,
      HasDerivAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ _
    have hD := hasDerivAt_expGrad_angular (u := u) (ξ := ξ) (θ := θ)
      (expGrad_differentiableAt_gen h1 h12 hu (by rw [re_logPolar]; exact ha)
        (by rw [re_logPolar]; exact hb))
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [Function.comp, Complex.mul_im] using hcomp
  have hint : IntervalIntegrable
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) volume (-π) π :=
    (continuous_slice_of_continuousOn_logStrip
      (continuousOn_deriv_expGrad_re_gen h1 h12 hu) ha hb).intervalIntegrable _ _
  rw [integral_Ioo_eq_intervalIntegral hπ,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hkey hint]
  have hper : expGrad u ((ξ : ℂ) + ((π : ℝ) : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    simp only [expGrad, exp_logPolar_pi_eq]
  rw [hper, sub_self]

/-- The flux integrand `∫_{(−π,π)} Re (expGrad u) dθ` is constant on `(log R₁, log R₂)`. -/
theorem integral_expGrad_re_constant_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) {ξ η : ℝ}
    (hξ : ξ ∈ Ioo (Real.log R₁) (Real.log R₂)) (hη : η ∈ Ioo (Real.log R₁) (Real.log R₂)) :
    (∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      = ∫ θ in Ioo (-π) π, (expGrad u ((η : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hd : ∀ x ∈ Ioo (Real.log R₁) (Real.log R₂), HasDerivAt
      (fun y : ℝ => ∫ θ in Ioo (-π) π, (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re) 0 x := by
    intro x hx
    have hstep := hasDerivAt_integral_logStrip (continuousOn_expGrad_re_gen h1 h12 hu)
      (continuousOn_deriv_expGrad_re_gen h1 h12 hu)
      (fun y θ hy1 hy2 => by
        have hD := hasDerivAt_expGrad_radial (u := u) (ξ := y) (θ := θ)
          (expGrad_differentiableAt_gen h1 h12 hu (by rw [re_logPolar]; exact hy1)
            (by rw [re_logPolar]; exact hy2))
        have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hD
        simpa [Function.comp] using hcomp)
      hx.1 hx.2
    rwa [integral_re_deriv_expGrad_eq_zero_gen h1 h12 hu hx.1 hx.2] at hstep
  exact eqOn_Ioo_of_hasDerivAt_zero hd hξ hη

/-- **Affine circle mean (general annulus).** For `u` harmonic on `RoundAnnulus 0 R₁ R₂` with
`0 < R₁ < R₂`, the circle mean `ξ ↦ logCircleMean 0 u ξ` is an affine function `a + b·ξ` of the
log-radius on `(log R₁, log R₂)`. -/
theorem logCircleMean_affineOn_gen {u : ℂ → ℝ} {R₁ R₂ : ℝ} (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) :
    ∃ a b : ℝ, ∀ ξ ∈ Ioo (Real.log R₁) (Real.log R₂), logCircleMean 0 u ξ = a + b * ξ := by
  have hlog : Real.log R₁ < Real.log R₂ := Real.log_lt_log h1 h12
  set ξc : ℝ := (Real.log R₁ + Real.log R₂) / 2 with hξc
  have hξcmem : ξc ∈ Ioo (Real.log R₁) (Real.log R₂) := by
    constructor <;> · rw [hξc]; linarith
  set b : ℝ := ∫ θ in Ioo (-π) π, (expGrad u ((ξc : ℂ) + (θ : ℂ) * Complex.I)).re with hb
  refine ⟨logCircleMean 0 u ξc - b * ξc, b, fun ξ hξ => ?_⟩
  have hgderiv : ∀ x ∈ Ioo (Real.log R₁) (Real.log R₂),
      HasDerivAt (fun y => logCircleMean 0 u y - b * y) 0 x := by
    intro x hx
    have hm := hasDerivAt_logCircleMean_gen h1 h12 hu hx.1 hx.2
    have hx' : (∫ θ in Ioo (-π) π, (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re) = b :=
      integral_expGrad_re_constant_gen h1 h12 hu hx hξcmem
    rw [hx'] at hm
    have hsub := hm.sub ((hasDerivAt_id x).const_mul b)
    simpa using hsub
  have hgeq := eqOn_Ioo_of_hasDerivAt_zero hgderiv hξ hξcmem
  simp only at hgeq
  linarith [hgeq]

/-- The circle mean of the zero-extension `Set.indicator U u` agrees with the circle mean of `u`
on a full circle contained in `U`. -/
theorem logCircleMean_indicator_eq {U : Set ℂ} {u : ℂ → ℝ} {ξ : ℝ}
    (hsub : Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U) :
    logCircleMean 0 (Set.indicator U u) ξ = logCircleMean 0 u ξ := by
  unfold logCircleMean
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  have hmem : (0 : ℂ) + Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)
      ∈ Metric.sphere (0 : ℂ) (Real.exp ξ) := by
    simpa using logCircleMean_point_mem_sphere 0 ξ θ
  rw [Set.indicator_of_mem (hsub hmem)]

/-- **N16.2 (potential level).** For `0 < R₁ < R₂ ≤ 1` with the open full-circle annulus
`{R₁ < |z| < R₂}` contained in `U` and `u` harmonic there, the log-polar circle mean of the
zero-extension `Set.indicator U u` is affine in the log-radius on `(log R₁, log R₂)`. -/
theorem logCircleMean_affine_on_fullCircles {U : Set ℂ} {u : ℂ → ℝ} {R₁ R₂ : ℝ}
    (h1 : 0 < R₁) (h12 : R₁ < R₂)
    (hAU : RoundAnnulus 0 R₁ R₂ ⊆ U)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 R₁ R₂)) :
    ∃ a b : ℝ, ∀ ξ ∈ Ioo (Real.log R₁) (Real.log R₂),
      logCircleMean 0 (Set.indicator U u) ξ = a + b * ξ := by
  obtain ⟨a, b, hab⟩ := logCircleMean_affineOn_gen h1 h12 hu
  refine ⟨a, b, fun ξ hξ => ?_⟩
  have hsphereU : Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U := by
    refine subset_trans (fun z hz => ?_) hAU
    have hznorm : ‖z‖ = Real.exp ξ := by
      rwa [Metric.mem_sphere, dist_zero_right] at hz
    have hlo : R₁ < Real.exp ξ := by
      calc R₁ = Real.exp (Real.log R₁) := (Real.exp_log h1).symm
        _ < Real.exp ξ := Real.exp_lt_exp.mpr hξ.1
    have hhi : Real.exp ξ < R₂ := by
      calc Real.exp ξ < Real.exp (Real.log R₂) := Real.exp_lt_exp.mpr hξ.2
        _ = R₂ := Real.exp_log (lt_trans h1 h12)
    simp only [RoundAnnulus, Set.mem_setOf_eq, dist_zero_right, hznorm]
    exact ⟨hlo, hhi⟩
  rw [logCircleMean_indicator_eq hsphereU]
  exact hab ξ hξ

/-! ### N16.5(b) Right-edge decay of the star comparison -/

/-- **Uniform lower bound for the star function.** For a potential `u ≥ m` (`0 ≤ m`) on the circle
of radius `r` about `p` and half-aperture `0 ≤ θ ≤ π`, `2 · m · θ ≤ (starFunction p u r θ).toReal`:
the angular profile is `≥ ofReal m` everywhere, so its distribution function equals the full measure
`2π` below level `m`, and the layer-cake integrand `min (2θ) (D t) = ofReal (2θ)` on `(0, m)`. -/
theorem le_starFunction_toReal {p : ℂ} {u : ℂ → ℝ} {r m M θ : ℝ} (hm : 0 ≤ m)
    (hbdd : ∀ φ : ℝ, m ≤ u (p + (r : ℂ) * Complex.exp (φ * Complex.I)))
    (hbddM : ∀ φ : ℝ, u (p + (r : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    2 * m * θ ≤ (starFunction p u r θ).toReal := by
  set g : ℝ → ℝ≥0∞ := fun φ => ENNReal.ofReal
    ((angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal) with hgdef
  have hπ2 : θ ≤ 2 * π / 2 := by linarith [Real.pi_pos]
  set D : ℝ → ℝ≥0∞ := fun t => distribFun (2 * π) g (ENNReal.ofReal t) with hDdef
  -- Below level `m` the distribution function is the full measure `ofReal (2π)`.
  have hgm : ∀ φ : ℝ, ENNReal.ofReal m ≤ g φ := by
    intro φ
    rw [hgdef]
    simp only [angularProfile]
    rw [ofReal_toReal_ofReal]
    exact ENNReal.ofReal_le_ofReal (hbdd (φ - π))
  have hDfull : ∀ t : ℝ, 0 < t → t < m → D t = ENNReal.ofReal (2 * π) := by
    intro t ht htm
    have hset : {x ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t < g x} = Icc (0 : ℝ) (2 * π) := by
      ext x
      simp only [mem_setOf_eq, and_iff_left_iff_imp]
      intro _
      exact lt_of_lt_of_le
        (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨htm, by linarith⟩) (hgm x)
    simp only [hDdef, distribFun, hset, Real.volume_Icc, sub_zero]
  have hle : ENNReal.ofReal (2 * θ * m) ≤ starFunction p u r θ := by
    rw [show starFunction p u r θ = starProfile (2 * π) g θ from rfl,
      starProfile_eq_lintegral_min (by positivity) hθ0 hπ2]
    calc ENNReal.ofReal (2 * θ * m)
        = ∫⁻ t in Ioi (0 : ℝ),
            (Ioo (0 : ℝ) m).indicator (fun _ => ENNReal.ofReal (2 * θ)) t := by
          rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const,
            Measure.restrict_apply measurableSet_Ioo, Ioo_inter_Ioi, sup_of_le_right le_rfl,
            Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), min (ENNReal.ofReal (2 * θ)) (D t) := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro t ht
          rcases lt_or_ge t m with htm | htm
          · rw [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) m from ⟨ht, htm⟩)]
            rw [hDfull t ht htm]
            exact le_min le_rfl (ENNReal.ofReal_le_ofReal (by linarith))
          · rw [Set.indicator_of_notMem (by
              simp only [mem_Ioo, not_and, not_lt]; exact fun _ => htm)]
            exact zero_le _
  calc 2 * m * θ = (ENNReal.ofReal (2 * θ * m)).toReal := by
        rw [ENNReal.toReal_ofReal (by positivity)]; ring
    _ ≤ (starFunction p u r θ).toReal := by
        refine ENNReal.toReal_mono ?_ hle
        exact (starFunction_lt_top hθ0 hθπ ⟨M, hbddM⟩).ne

/-- **Uniform collar bound.** For `u` continuous on the closed collar `{r₀ ≤ |z| ≤ 1}`
(`0 < r₀ < 1`) with `u = 1` on the unit circle, and any `η > 0`, there is a log-radius margin
`ξ₀ ∈ (log r₀, 0)` so that `1 − η ≤ u(e^{ξ+iφ})` for every angle `φ` and every `ξ ∈ (ξ₀, 0)`:
the closed collar is compact, so `u` is uniformly continuous, and `u(e^{ξ+iφ})` is uniformly close
to `u(e^{iφ}) = 1`. -/
theorem collar_lower_bound {u : ℂ → ℝ} {r₀ : ℝ} (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1) {η : ℝ} (hη : 0 < η) :
    ∃ ξ₀ : ℝ, Real.log r₀ < ξ₀ ∧ ξ₀ < 0 ∧
      ∀ ξ : ℝ, ξ₀ < ξ → ξ < 0 → ∀ φ : ℝ,
        1 - η ≤ u ((Real.exp ξ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
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
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hunif η hη
  have hlogneg : Real.log r₀ < 0 := Real.log_neg h0 h1
  refine ⟨max (Real.log r₀ / 2) (-δ₀), ?_, ?_, fun ξ hξlo hξneg φ => ?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact max_lt (by linarith) (by linarith)
  have hmax1 : Real.log r₀ / 2 ≤ max (Real.log r₀ / 2) (-δ₀) := le_max_left _ _
  have hξlog : Real.log r₀ < ξ := by linarith [hξlo, hmax1]
  have hξδ₀ : -δ₀ < ξ := lt_of_le_of_lt (le_max_right _ _) hξlo
  -- Moving point on the circle of radius `e^ξ` and its unit-circle projection lie in the collar.
  have hexple : Real.exp ξ ≤ 1 := by
    calc Real.exp ξ ≤ Real.exp 0 := Real.exp_le_exp.mpr hξneg.le
      _ = 1 := Real.exp_zero
  have hexpge : r₀ ≤ Real.exp ξ := by
    calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log h0).symm
      _ ≤ Real.exp ξ := Real.exp_le_exp.mpr hξlog.le
  have hzK : (Real.exp ξ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
      ∈ {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} := by
    have hnorm : dist ((Real.exp ξ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) 0 = Real.exp ξ := by
      rw [dist_zero_right, norm_mul, Complex.norm_exp]
      simp
    exact ⟨by rw [hnorm]; exact hexpge, by rw [hnorm]; exact hexple⟩
  have hwsphere : dist (Complex.exp ((φ : ℂ) * Complex.I)) 0 = 1 := by
    rw [dist_zero_right, Complex.norm_exp]; simp
  have hwK : Complex.exp ((φ : ℂ) * Complex.I)
      ∈ {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} :=
    ⟨by rw [hwsphere]; exact h1.le, by rw [hwsphere]⟩
  -- The two points are within `δ₀`, so their `u`-values are within `η`.
  have hzw : dist ((Real.exp ξ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
      (Complex.exp ((φ : ℂ) * Complex.I)) < δ₀ := by
    have hfactor : (Real.exp ξ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)
        - Complex.exp ((φ : ℂ) * Complex.I)
        = ((Real.exp ξ : ℂ) - 1) * Complex.exp ((φ : ℂ) * Complex.I) := by ring
    have hn1 : ‖Complex.exp ((φ : ℂ) * Complex.I)‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [dist_eq_norm, hfactor, norm_mul, hn1, mul_one, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hineq : 1 - Real.exp ξ ≤ -ξ := by linarith [Real.add_one_le_exp ξ]
    linarith
  have hw1 : u (Complex.exp ((φ : ℂ) * Complex.I)) = 1 :=
    hone _ (Metric.mem_sphere.mpr hwsphere)
  have hclose := hδ₀ _ hzK _ hwK hzw
  rw [Real.dist_eq, hw1] at hclose
  have := abs_lt.mp hclose
  linarith [this.1]

/-- A circle of radius `r ∈ (s, 1)` about the origin lies inside the Grötzsch ring `grotzschRing s`
(it stays in the open unit disk and cannot meet the slit `[0, s]`, all of whose points have norm
`≤ s`). -/
theorem sphere_subset_grotzschRing {s r : ℝ} (hs0 : 0 ≤ s) (hsr : s < r) (hr1 : r < 1) :
    Metric.sphere (0 : ℂ) r ⊆ grotzschRing s := by
  intro z hz
  have hznorm : ‖z‖ = r := by rwa [Metric.mem_sphere, dist_zero_right] at hz
  refine ⟨by rw [mem_ball_zero_iff, hznorm]; exact hr1, ?_⟩
  intro hzslit
  have h0eq : (0 : ℂ) = ((0 : ℝ) : ℂ) := by norm_num
  rw [h0eq, mem_segment_ofReal, Set.uIcc_of_le hs0] at hzslit
  have hzim : z.im = 0 := hzslit.1
  have hzre : z.re ≤ s := hzslit.2.2
  have hnorms : ‖z‖ ≤ s := by
    rw [Complex.norm_def, Complex.normSq_apply, hzim]
    have hsq : z.re * z.re + 0 * 0 = z.re ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs]
    exact abs_le.mpr ⟨by linarith [hzslit.2.1], hzre⟩
  rw [hznorm] at hnorms
  linarith

/-- **N16.5(b) right-edge decay.** Let `ω̃ = Set.indicator U u` with `ω̃ ≤ 1`, and let
`ṽ = Set.indicator (grotzschRing s) v` for `v` continuous on the closure of the Grötzsch ring,
equal to `1` on the unit circle and with `0 ≤ v ≤ 1` on the ring. Then the star comparison
`J w := starPlane 0 ω̃ w − starPlane 0 ṽ w` decays at the right edge: for every `c > 0` there is
`δ > 0` with `J w ≤ c` for every `w ∈ S = {re < 0, 0 < im < π}` with `−δ < w.re`. The upper star
bound `ω̃★ ≤ 2·im` uses `ω̃ ≤ 1`; the lower star bound `ṽ★ ≥ 2·(1 − η)·im` uses the uniform collar
bound `v ≥ 1 − η` near the unit circle, so `J ≤ 2·im·η ≤ 2π·η`. -/
theorem baernstein_right_edge {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {u v : ℂ → ℝ} {U : Set ℂ}
    (hω1 : ∀ z, Set.indicator U u z ≤ 1)
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvb : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) :
    ∀ c > 0, ∃ δ > 0, ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, -δ < w.re →
      starPlane 0 (Set.indicator U u) w - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ c := by
  intro c hc
  set r₀ : ℝ := (s + 1) / 2 with hr₀def
  have hr₀0 : 0 < r₀ := by rw [hr₀def]; linarith
  have hr₀1 : r₀ < 1 := by rw [hr₀def]; linarith
  have hsr₀ : s < r₀ := by rw [hr₀def]; linarith
  set η : ℝ := min (c / (2 * π)) 1 with hηdef
  have hη : 0 < η := by rw [hηdef]; exact lt_min (by positivity) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηc : 2 * π * η ≤ c := by
    have h1 : η ≤ c / (2 * π) := min_le_left _ _
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
    rwa [mul_div_cancel₀ _ (by positivity : (2 : ℝ) * π ≠ 0)] at this
  -- Continuity of `v` on the closed collar `{r₀ ≤ |z| ≤ 1}`.
  have hcoll : {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1} ⊆ closure (grotzschRing s) := by
    rw [closure_grotzschRing hs0.le]
    exact fun z hz => by rw [Metric.mem_closedBall]; exact hz.2
  obtain ⟨ξ₀, hξ₀lo, hξ₀0, hcollbd⟩ :=
    collar_lower_bound hr₀0 hr₀1 (hvc.mono hcoll) hv1 hη
  refine ⟨-ξ₀, by linarith, fun w hw hwre => ?_⟩
  obtain ⟨hwre0, hwim0, hwimπ⟩ := hw
  have hξw : ξ₀ < w.re := by linarith
  -- Upper bound on the subharmonic star surface via `ω̃ ≤ 1`.
  have hUB : starPlane 0 (Set.indicator U u) w ≤ 2 * w.im := by
    have := starPlane_le_two_mul_aperture (p := (0 : ℂ)) (u := Set.indicator U u) (M := 1)
      (w := w) (by norm_num) (fun φ => by simpa using hω1 _) hwim0.le hwimπ.le
    simpa using this
  -- On the circle of radius `e^{w.re} ∈ (s, 1)`, `ṽ = v ≥ 1 − η`.
  have hexpre_lo : s < Real.exp w.re := by
    have : Real.exp ξ₀ < Real.exp w.re := Real.exp_lt_exp.mpr hξw
    have hlo : r₀ < Real.exp ξ₀ := by
      calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log hr₀0).symm
        _ < Real.exp ξ₀ := Real.exp_lt_exp.mpr hξ₀lo
    linarith
  have hexpre_hi : Real.exp w.re < 1 := by
    calc Real.exp w.re < Real.exp 0 := Real.exp_lt_exp.mpr hwre0
      _ = 1 := Real.exp_zero
  have hvind : ∀ φ : ℝ, 1 - η ≤ Set.indicator (grotzschRing s) v
      ((0 : ℂ) + (Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
    intro φ
    have hzmem : (Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∈ grotzschRing s := by
      apply sphere_subset_grotzschRing hs0.le hexpre_lo hexpre_hi
      rw [Metric.mem_sphere, dist_zero_right, norm_mul, Complex.norm_exp]
      simp
    rw [zero_add, Set.indicator_of_mem hzmem]
    exact hcollbd w.re hξw hwre0 φ
  have hvindM : ∀ φ : ℝ, Set.indicator (grotzschRing s) v
      ((0 : ℂ) + (Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ≤ 1 := by
    intro φ
    have hzmem : (Real.exp w.re : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ∈ grotzschRing s := by
      apply sphere_subset_grotzschRing hs0.le hexpre_lo hexpre_hi
      rw [Metric.mem_sphere, dist_zero_right, norm_mul, Complex.norm_exp]
      simp
    rw [zero_add, Set.indicator_of_mem hzmem]
    exact (hvb _ hzmem).2
  -- Lower bound on the harmonic star surface via the collar bound.
  have hLB : 2 * (1 - η) * w.im ≤ starPlane 0 (Set.indicator (grotzschRing s) v) w := by
    have hstar : starPlane 0 (Set.indicator (grotzschRing s) v) w
        = (starFunction 0 (Set.indicator (grotzschRing s) v) (Real.exp w.re) w.im).toReal := rfl
    rw [hstar]
    exact le_starFunction_toReal (M := 1) (by linarith) hvind hvindM hwim0.le hwimπ.le
  -- Assemble: `J ≤ 2·im − 2·(1−η)·im = 2·im·η ≤ 2π·η ≤ c`.
  have hcomb : starPlane 0 (Set.indicator U u) w
      - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 2 * w.im * η := by
    have : 2 * w.im - 2 * (1 - η) * w.im = 2 * w.im * η := by ring
    linarith [hUB, hLB]
  calc starPlane 0 (Set.indicator U u) w
        - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 2 * w.im * η := hcomb
    _ ≤ 2 * π * η := by
        apply mul_le_mul_of_nonneg_right _ hη.le
        nlinarith [hwimπ.le, Real.pi_pos]
    _ ≤ c := hηc

/-! ### N16.6 support: continuity of the circle mean -/

/-- **Continuity of the log-polar circle mean.** For `f` measurable, nonnegative and bounded above
by `M` (`0 ≤ M`) on all circles of log-radius in `(log rI, log rO)`, whose star surface
`starPlane 0 f` is continuous on the log-polar strip, the apex circle mean `ξ ↦ logCircleMean 0 f ξ`
is continuous on `(log rI, log rO)`: it is the uniform (rate `2M(π − θ)`) limit as `θ → π` of the
continuous slices `ξ ↦ starPlane 0 f (ξ + iθ)`, via the aperture-to-apex bound. -/
theorem logCircleMean_continuousOn {f : ℂ → ℝ} {rI rO M : ℝ}
    (hM : 0 ≤ M) (hf : Measurable f) (hnn : ∀ z, 0 ≤ f z)
    (hbdd : ∀ ξ ∈ Ioo (Real.log rI) (Real.log rO), ∀ φ : ℝ,
      f ((0 : ℂ) + (Real.exp ξ : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hstar : ContinuousOn (starPlane 0 f) (logPolarStrip rI rO)) :
    ContinuousOn (fun ξ => logCircleMean 0 f ξ) (Ioo (Real.log rI) (Real.log rO)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Metric.continuousOn_iff]
  intro ξ₀ hξ₀ ε hε
  -- Choose an aperture `θ` close to `π` so the apex deficit is `< ε/3`.
  set θ : ℝ := π - min (π / 2) (ε / (3 * (2 * M + 1))) with hθdef
  have hθlo : 0 < θ := by
    rw [hθdef]; have := min_le_left (π / 2) (ε / (3 * (2 * M + 1))); linarith
  have hθhi : θ < π := by
    rw [hθdef]; have : 0 < min (π / 2) (ε / (3 * (2 * M + 1))) :=
      lt_min (by linarith) (by positivity); linarith
  have hπθ : π - θ = min (π / 2) (ε / (3 * (2 * M + 1))) := by rw [hθdef]; ring
  have hdefsmall : 2 * M * (π - θ) < ε / 3 := by
    rw [hπθ]
    have h1 : min (π / 2) (ε / (3 * (2 * M + 1))) ≤ ε / (3 * (2 * M + 1)) := min_le_right _ _
    calc 2 * M * min (π / 2) (ε / (3 * (2 * M + 1)))
        ≤ 2 * M * (ε / (3 * (2 * M + 1))) := by
          apply mul_le_mul_of_nonneg_left h1 (by linarith)
      _ < ε / 3 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hε, hM]
  -- The slice point `P ξ = ξ + iθ`, with `re = ξ` and `im = θ`.
  set P : ℝ → ℂ := fun ξ => (ξ : ℂ) + (θ : ℂ) * Complex.I with hPdef
  have hPre : ∀ ξ : ℝ, (P ξ).re = ξ := by intro ξ; simp [hPdef]
  have hPim : ∀ ξ : ℝ, (P ξ).im = θ := by intro ξ; simp [hPdef]
  -- Apex-deficit bound at any log-radius, applied through `starPlane_sub_logCircleMean_le`.
  have hdeficit : ∀ ξ ∈ Ioo (Real.log rI) (Real.log rO),
      |starPlane 0 f (P ξ) - logCircleMean 0 f ξ| ≤ 2 * M * (π - θ) := by
    intro ξ hξ
    have hbdd' : ∀ φ : ℝ, f ((0 : ℂ) + (Real.exp (P ξ).re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M :=
      fun φ => by rw [hPre ξ]; exact hbdd ξ hξ φ
    have := starPlane_sub_logCircleMean_le (p := (0 : ℂ)) (u := f) (M := M) (w := P ξ) hM hf
      (fun z _ => hnn z) hbdd' (by rw [hPim ξ]; exact hθlo.le) (by rw [hPim ξ]; exact hθhi.le)
    rw [hPre ξ, hPim ξ] at this
    exact this
  -- Continuity of the slice `ξ ↦ starPlane 0 f (P ξ)` at `ξ₀`.
  have hslice : ContinuousWithinAt (fun ξ : ℝ => starPlane 0 f (P ξ))
      (Ioo (Real.log rI) (Real.log rO)) ξ₀ := by
    have hmap : ContinuousWithinAt P (Ioo (Real.log rI) (Real.log rO)) ξ₀ := by
      apply Continuous.continuousWithinAt; rw [hPdef]; fun_prop
    have hmaps : Set.MapsTo P (Ioo (Real.log rI) (Real.log rO)) (logPolarStrip rI rO) :=
      fun ξ hξ => ⟨by rw [hPre ξ]; exact hξ, by rw [hPim ξ]; exact ⟨hθlo, hθhi⟩⟩
    exact (hstar _ (hmaps hξ₀)).comp hmap hmaps
  rw [Metric.continuousWithinAt_iff] at hslice
  obtain ⟨δ, hδ, hδprop⟩ := hslice (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun ξ hξ hξδ => ?_⟩
  -- Triangle inequality: `|m ξ − m ξ₀| ≤ deficit + slice diff + deficit`.
  have hd1 := hdeficit ξ hξ
  have hd2 := hdeficit ξ₀ hξ₀
  have hs := hδprop hξ hξδ
  rw [Real.dist_eq] at hs ⊢
  have ht1 : |logCircleMean 0 f ξ - starPlane 0 f (P ξ)|
      = |starPlane 0 f (P ξ) - logCircleMean 0 f ξ| := abs_sub_comm _ _
  have ht2 : |logCircleMean 0 f ξ - logCircleMean 0 f ξ₀|
      ≤ |logCircleMean 0 f ξ - starPlane 0 f (P ξ)|
        + |starPlane 0 f (P ξ) - logCircleMean 0 f ξ₀| := abs_sub_le _ _ _
  have ht3 : |starPlane 0 f (P ξ) - logCircleMean 0 f ξ₀|
      ≤ |starPlane 0 f (P ξ) - starPlane 0 f (P ξ₀)|
        + |starPlane 0 f (P ξ₀) - logCircleMean 0 f ξ₀| := abs_sub_le _ _ _
  rw [ht1] at ht2
  linarith [ht2, ht3, hd1, hd2, hs, hdefsmall]

/-! ### H6 The star comparison `J ≤ 0` -/

/-- **The tilted comparison surface `w ↦ ε·Im w` is harmonic.** It is the imaginary part of the
entire function `w ↦ ε·w`. -/
theorem harmonicOnNhd_tilt (ε : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun w : ℂ => ε * w.im) Set.univ := by
  have heq : (fun w : ℂ => ε * w.im) = fun w : ℂ => ((ε : ℂ) * w).im := by
    funext w
    simp [Complex.mul_im]
  rw [heq]
  intro x _
  exact (analyticAt_const.mul analyticAt_id).harmonicAt_im

/-- **Top-edge transfer.** With `J w = ω★ w − v★ w` the star comparison, `Q w = J w − ε·Im w` the
tilted surface and `g ξ = m_ω ξ − m_v ξ − ε·π` the top-edge profile (`m_ω`, `m_v` the circle means),
for both potentials bounded by `1` on the circle of radius `exp w.re`, the tilted surface differs
from its top-edge value by at most `(4 + ε)·(π − Im w)`. -/
theorem baernstein_top_transfer {ω vt : ℂ → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hωm : Measurable ω) (hvm : Measurable vt)
    (hωnn : ∀ z, 0 ≤ ω z) (hvnn : ∀ z, 0 ≤ vt z) {w : ℂ}
    (hωb : ∀ φ : ℝ, ω ((0 : ℂ) + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ 1)
    (hvb : ∀ φ : ℝ, vt ((0 : ℂ) + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ 1)
    (hθ0 : 0 ≤ w.im) (hθπ : w.im ≤ π) :
    |(starPlane 0 ω w - starPlane 0 vt w - ε * w.im)
        - (logCircleMean 0 ω w.re - logCircleMean 0 vt w.re - ε * π)|
      ≤ (4 + ε) * (π - w.im) := by
  have hπθ : 0 ≤ π - w.im := by linarith
  have hbω := starPlane_sub_logCircleMean_le (p := (0 : ℂ)) (u := ω) (M := 1) (w := w)
    (by norm_num) hωm (fun z _ => hωnn z) (fun φ => by simpa using hωb φ) hθ0 hθπ
  have hbv := starPlane_sub_logCircleMean_le (p := (0 : ℂ)) (u := vt) (M := 1) (w := w)
    (by norm_num) hvm (fun z _ => hvnn z) (fun φ => by simpa using hvb φ) hθ0 hθπ
  rw [show (2 : ℝ) * 1 = 2 by norm_num] at hbω hbv
  have hkey : (starPlane 0 ω w - starPlane 0 vt w - ε * w.im)
      - (logCircleMean 0 ω w.re - logCircleMean 0 vt w.re - ε * π)
      = (starPlane 0 ω w - logCircleMean 0 ω w.re)
        - (starPlane 0 vt w - logCircleMean 0 vt w.re) + ε * (π - w.im) := by ring
  rw [hkey]
  have h1 : |(starPlane 0 ω w - logCircleMean 0 ω w.re)
      - (starPlane 0 vt w - logCircleMean 0 vt w.re)| ≤ 2 * (π - w.im) + 2 * (π - w.im) :=
    (abs_sub _ _).trans (add_le_add hbω hbv)
  have h2 : |ε * (π - w.im)| = ε * (π - w.im) := abs_of_nonneg (mul_nonneg hε hπθ)
  calc |(starPlane 0 ω w - logCircleMean 0 ω w.re)
          - (starPlane 0 vt w - logCircleMean 0 vt w.re) + ε * (π - w.im)|
      ≤ |(starPlane 0 ω w - logCircleMean 0 ω w.re)
          - (starPlane 0 vt w - logCircleMean 0 vt w.re)| + |ε * (π - w.im)| := abs_add_le _ _
    _ ≤ (2 * (π - w.im) + 2 * (π - w.im)) + ε * (π - w.im) := by rw [h2]; linarith
    _ = (4 + ε) * (π - w.im) := by ring

/-- **Case-(a) pinch.** At a log-radius `ξ` whose circle carries a zero of the (continuous,
nonnegative, `≤ 1`) potential `ω`, and where the comparison potential `vt` is measurable,
nonnegative and `≤ 1` on that circle, near full aperture the tilted surface strictly exceeds `g`:
for every `ε > 0` there is `θ₀ ∈ [0, π)` so that for all `θ ∈ [θ₀, π)`,
`(ω★ − vt★ − ε·θ)(ξ+iθ) ≥ g(ξ) + (ε/2)(π − θ)`, where `g(ξ) = m_ω − m_vt − ε·π`. The `ω` side uses
apex saturation with parameter `ε/2` (`starFunction_apex_saturation`); the `vt` side uses aperture
monotonicity `vt★(θ) ≤ vt★(π) = m_vt`. -/
theorem baernstein_case_a_pinch {ω vt : ℂ → ℝ} {ξ : ℝ} (hωmeas : Measurable ω)
    (hωcont : ContinuousOn ω (Metric.sphere (0 : ℂ) (Real.exp ξ)))
    (hωnn : ∀ z, 0 ≤ ω z) (hωzero : ∃ z ∈ Metric.sphere (0 : ℂ) (Real.exp ξ), ω z = 0)
    (hvm : Measurable vt) (hvnn : ∀ z, 0 ≤ vt z)
    (hvb : ∀ φ : ℝ, vt ((0 : ℂ) + (Real.exp ξ : ℂ) * Complex.exp (φ * Complex.I)) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ₀ ∈ Ico (0 : ℝ) π, ∀ θ ∈ Ico θ₀ π,
      (logCircleMean 0 ω ξ - logCircleMean 0 vt ξ - ε * π) + ε / 2 * (π - θ)
        ≤ starPlane 0 ω ((ξ : ℂ) + (θ : ℂ) * Complex.I)
          - starPlane 0 vt ((ξ : ℂ) + (θ : ℂ) * Complex.I) - ε * θ := by
  have hr : (0 : ℝ) < Real.exp ξ := Real.exp_pos _
  -- Apex saturation for `ω` with parameter `ε/2`.
  obtain ⟨θ₀, hθ₀mem, hsat⟩ :=
    starFunction_apex_saturation hr hωcont hωnn hωzero (ε / 2) (by positivity)
  refine ⟨θ₀, hθ₀mem, fun θ hθ => ?_⟩
  obtain ⟨hθlo, hθhi⟩ := hθ
  have hθ0 : 0 ≤ θ := le_trans hθ₀mem.1 hθlo
  have hπθ : 0 ≤ π - θ := by linarith
  -- The two star-surface points, with `re = ξ`, `im = θ` (resp. `π`).
  set wθ : ℂ := (ξ : ℂ) + (θ : ℂ) * Complex.I with hwθ
  have hwθre : wθ.re = ξ := by simp [hwθ]
  have hwθim : wθ.im = θ := by simp [hwθ]
  -- `ω★(θ) ≥ m_ω(ξ) − (ε/2)(π − θ)` from apex saturation and `starPlane_apex_eq`.
  have hωstar : starPlane 0 ω wθ = (starFunction 0 ω (Real.exp ξ) θ).toReal := by
    simp [starPlane, hwθre, hwθim]
  have hωapex : (starFunction 0 ω (Real.exp ξ) π).toReal = logCircleMean 0 ω ξ := by
    rw [starFunction_apex_toReal hr hωmeas (fun z _ => hωnn z), Real.log_exp]
  have hsatθ := hsat θ ⟨hθlo, hθhi.le⟩
  rw [hωapex] at hsatθ
  have hωlb : logCircleMean 0 ω ξ - ε / 2 * (π - θ) ≤ starPlane 0 ω wθ := by
    rw [hωstar]; linarith [hsatθ]
  -- `vt★(θ) ≤ m_vt(ξ)` from aperture monotonicity and `starPlane_apex_eq`.
  have hvstar : starPlane 0 vt wθ = (starFunction 0 vt (Real.exp ξ) θ).toReal := by
    simp [starPlane, hwθre, hwθim]
  have hvfinπ : starFunction 0 vt (Real.exp ξ) π < ⊤ :=
    starFunction_lt_top Real.pi_pos.le le_rfl ⟨1, hvb⟩
  have hvmono : starFunction 0 vt (Real.exp ξ) θ ≤ starFunction 0 vt (Real.exp ξ) π :=
    monotone_starFunction 0 vt (Real.exp ξ) hθ0 Real.pi_pos.le hθhi.le
  have hvapex : (starFunction 0 vt (Real.exp ξ) π).toReal = logCircleMean 0 vt ξ := by
    rw [starFunction_apex_toReal hr hvm (fun z _ => hvnn z), Real.log_exp]
  have hvub : starPlane 0 vt wθ ≤ logCircleMean 0 vt ξ := by
    rw [hvstar, ← hvapex]
    exact ENNReal.toReal_mono hvfinπ.ne hvmono
  -- Assemble.
  have hid : ε * π - ε * θ = ε * (π - θ) := by ring
  have hid2 : ε * (π - θ) = ε / 2 * (π - θ) + ε / 2 * (π - θ) := by ring
  have hgoal : starPlane 0 ω wθ - starPlane 0 vt wθ - ε * θ
      ≥ (logCircleMean 0 ω ξ - logCircleMean 0 vt ξ - ε * π) + ε / 2 * (π - θ) := by
    linarith [hωlb, hvub, hid, hid2]
  simpa [hwθ] using hgoal

/-- **Left-edge decay.** If `ω` is uniformly small near the origin (for every `c > 0`
some ball around `0` has `ω ≤ c`), then the star comparison `J = ω★ − vt★` decays at the left edge:
for every `c > 0` there is `T > 0` so that `J w ≤ c` whenever `w ∈ S = {re < 0, 0 < im < π}` has
`re w < −T`. The upper star bound `ω★ ≤ 2π · sup ω` uses the smallness of `ω` on the shrinking
circle; the star `vt★ ≥ 0` is nonnegative. -/
theorem baernstein_left_edge {ω vt : ℂ → ℝ}
    (hsmall : ∀ c > 0, ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → ω z ≤ c) :
    ∀ c > 0, ∃ T > 0, ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, w.re < -T →
      starPlane 0 ω w - starPlane 0 vt w ≤ c := by
  intro c hc
  have hπ : (0 : ℝ) < π := Real.pi_pos
  -- Uniform smallness `ω ≤ c / (2π)` inside the ball of radius `ρ`.
  obtain ⟨ρ, hρ, hball⟩ := hsmall (c / (2 * π)) (by positivity)
  refine ⟨max 1 (-Real.log ρ + 1), lt_of_lt_of_le one_pos (le_max_left _ _), fun w hw hwT => ?_⟩
  obtain ⟨hwre0, hwim0, hwimπ⟩ := hw
  have hTge : -Real.log ρ + 1 ≤ max 1 (-Real.log ρ + 1) := le_max_right _ _
  -- `exp (re w) < ρ`, so every point of the circle of radius `exp (re w)` lies in the ρ-ball.
  have hexpρ : Real.exp w.re < ρ := by
    have hre : w.re < Real.log ρ := by linarith [hwT, hTge]
    calc Real.exp w.re < Real.exp (Real.log ρ) := Real.exp_lt_exp.mpr hre
      _ = ρ := Real.exp_log hρ
  -- The potential is `≤ c / (2π)` on that circle.
  have hωbd : ∀ φ : ℝ,
      ω ((0 : ℂ) + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ c / (2 * π) := by
    intro φ
    apply hball
    rw [zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      abs_of_pos (Real.exp_pos _)]
    simpa using hexpρ
  -- Upper bound on the subharmonic star surface via the smallness bound.
  have hUB : starPlane 0 ω w ≤ 2 * π * (c / (2 * π)) :=
    starPlane_le_two_pi_mul (by positivity) hωbd hwim0.le hwimπ.le
  have hcbd : 2 * π * (c / (2 * π)) = c := by field_simp
  -- The comparison star surface is nonnegative.
  have hvnn0 : (0 : ℝ) ≤ starPlane 0 vt w := by
    have : starPlane 0 vt w = (starFunction 0 vt (Real.exp w.re) w.im).toReal := rfl
    rw [this]; exact ENNReal.toReal_nonneg
  linarith [hUB, hvnn0]

/-- **Rectangle maximum bound.** For `Q` subharmonic on the half-strip `S = {re < 0, 0 < im < π}`,
continuous on `closure S`, and a rectangle `R = (−T, −δ) ×ℂ (η, π − η) ⊆ S` (`−T < −δ < 0`,
`0 < η < π − η`), if `Q ≤ B` on each of the four edges of `R` (bottom `im = η`, top `im = π − η`,
left `re = −T`, right `re = −δ`), then `Q ≤ B` throughout `R`, by the maximum principle. -/
theorem baernstein_rect_max {Q : ℂ → ℝ} {T δ η B : ℝ}
    (hQsub : SubharmonicOn Q {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (hQcont : ContinuousOn Q {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (hδT : -T < -δ) (hδ0 : -δ < 0) (hη0 : 0 < η) (hηπ : η < π - η)
    (hbot : ∀ ξ ∈ Icc (-T) (-δ), Q ((ξ : ℂ) + (η : ℂ) * Complex.I) ≤ B)
    (htop : ∀ ξ ∈ Icc (-T) (-δ), Q ((ξ : ℂ) + ((π - η : ℝ) : ℂ) * Complex.I) ≤ B)
    (hleft : ∀ y ∈ Icc η (π - η), Q ((-T : ℝ) + (y : ℂ) * Complex.I) ≤ B)
    (hright : ∀ y ∈ Icc η (π - η), Q ((-δ : ℝ) + (y : ℂ) * Complex.I) ≤ B) :
    ∀ w ∈ Ioo (-T) (-δ) ×ℂ Ioo η (π - η), Q w ≤ B := by
  set R : Set ℂ := Ioo (-T) (-δ) ×ℂ Ioo η (π - η) with hR
  have hRclS : closure R ⊆ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := by
    intro w hw
    rw [hR, Complex.closure_reProdIm, closure_Ioo hδT.ne, closure_Ioo hηπ.ne,
      Complex.mem_reProdIm, mem_Icc, mem_Icc] at hw
    exact ⟨lt_of_le_of_lt hw.1.2 hδ0, lt_of_lt_of_le hη0 hw.2.1,
      lt_of_le_of_lt hw.2.2 (by linarith)⟩
  have hRS : R ⊆ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := subset_closure.trans hRclS
  have hRopen : IsOpen R := IsOpen.reProdIm isOpen_Ioo isOpen_Ioo
  have hRbdd : Bornology.IsBounded R :=
    (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)
  have hQsubR : SubharmonicOn Q R := hQsub.mono hRS
  have hQcontR : ContinuousOn Q (closure R) := hQcont.mono hRclS
  have hfr : ∀ z ∈ frontier R, Q z ≤ B := by
    intro z hz
    have hedge4 : z.re = -T ∨ z.re = -δ ∨ z.im = η ∨ z.im = π - η := by
      have h := hz
      rw [hR, Complex.frontier_reProdIm, frontier_Ioo hδT, frontier_Ioo hηπ] at h
      rcases h with h | h <;> rw [Complex.mem_reProdIm] at h
      · rcases h.2 with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
      · rcases h.1 with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    -- On the closed rectangle the coordinates lie in the closed edge intervals.
    have hzcl := frontier_subset_closure hz
    rw [hR, Complex.closure_reProdIm, closure_Ioo hδT.ne, closure_Ioo hηπ.ne,
      Complex.mem_reProdIm, mem_Icc, mem_Icc] at hzcl
    obtain ⟨⟨hre1, hre2⟩, hy1, hy2⟩ := hzcl
    have hzeq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
    rcases hedge4 with hcase | hcase | hcase | hcase
    · have := hleft z.im ⟨hy1, hy2⟩
      rw [hcase] at hzeq; rw [hzeq]; exact this
    · have := hright z.im ⟨hy1, hy2⟩
      rw [hcase] at hzeq; rw [hzeq]; exact this
    · have := hbot z.re ⟨hre1, hre2⟩
      rw [hcase] at hzeq; rw [hzeq]; exact this
    · have := htop z.re ⟨hre1, hre2⟩
      rw [hcase] at hzeq; rw [hzeq]; exact this
  exact hQsubR.le_of_frontier_le hRopen hRbdd hQcontR hfr

/-- **Case-(b) reduction.** In the top-edge exclusion, at a full-circle log-radius `xh ∈ A`
(where `A = {ξ < 0 | e^ξ ⊆ U}`, open and inside `(log s, 0)`) that maximizes the affine top-edge
profile `g` over the band `[-T, -δ]`, the maximal full-circle interval `(α, β) ∋ xh` has affine `g`;
the interior maximum forces `g` constant, so `g α = g xh = Mtop` by continuity, and `α ∉ A` is a
case-(a) point in the band — contradicting the case-(a) exclusion at `α`. -/
theorem baernstein_case_b_reduce {U : Set ℂ} {s T δ : ℝ} {g : ℝ → ℝ} {xh Mtop : ℝ}
    (hUopen : IsOpen U) (hTlogs' : -T < Real.log s) (hδ0' : -δ < 0)
    (hωnotU : ∀ ξ : ℝ, ξ ≤ Real.log s → ¬ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U)
    (hgaff : ∀ α β : ℝ, Real.log s ≤ α → β ≤ 0 →
      Ioo α β ⊆ {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U} →
      ∃ a b : ℝ, ∀ ξ ∈ Ioo α β, g ξ = a + b * ξ)
    (hgcont : ContinuousOn g (Icc (-T) (-δ)))
    (hxhint : -T < xh ∧ xh < -δ)
    (hxhmax : IsMaxOn g (Icc (-T) (-δ)) xh) (hMtopdef : Mtop = g xh)
    (hxhA : xh ∈ {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U})
    (hcaseA : ∀ ζ : ℝ, -T < ζ → ζ < -δ → g ζ = Mtop →
      ¬ Metric.sphere (0 : ℂ) (Real.exp ζ) ⊆ U → False) : False := by
  set A : Set ℝ := {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U} with hAdef
  have hAopen : IsOpen A := fullCircle_set_isOpen (U := U) hUopen
  have hAsub : A ⊆ Ioo (Real.log s) 0 := by
    intro ξ hξ
    refine ⟨?_, hξ.1⟩
    by_contra hle
    rw [not_lt] at hle
    exact hωnotU ξ hle hξ.2
  obtain ⟨α, β, hloα, hαxh, hxhβ, hβ0, hIooA, hαnotA⟩ := maximal_interval hAopen hAsub hxhA
  set β' : ℝ := min β (-δ) with hβ'def
  have hxhβ' : xh < β' := lt_min hxhβ hxhint.2
  have hαβ' : α < β' := lt_trans hαxh hxhβ'
  obtain ⟨a, b, hgeq⟩ := hgaff α β hloα hβ0 (fun ξ hξ => hIooA hξ)
  have hβ'band : Ioo α β' ⊆ Icc (-T) (-δ) := by
    intro ξ hξ
    exact ⟨le_of_lt (by linarith [hTlogs', hloα, hξ.1]),
      le_of_lt (lt_of_lt_of_le hξ.2 (min_le_right _ _))⟩
  have hgaffβ' : ∀ ξ ∈ Ioo α β', g ξ = a + b * ξ :=
    fun ξ hξ => hgeq ξ ⟨hξ.1, lt_of_lt_of_le hξ.2 (min_le_left _ _)⟩
  have hxhmaxβ' : ∀ ξ ∈ Ioo α β', g ξ ≤ g xh := fun ξ hξ => hxhmax (hβ'band hξ)
  obtain ⟨_, hgconst⟩ := affine_interior_max_constant g hgaffβ' ⟨hαxh, hxhβ'⟩ hxhmaxβ'
  have hαband : α ∈ Icc (-T) (-δ) := ⟨by linarith [hloα, hTlogs'], by linarith [hαxh, hxhint.2]⟩
  have hgαMtop : g α = Mtop := by
    have hconstval : ∀ ξ ∈ Ioo α β', g ξ = Mtop := fun ξ hξ => by rw [hgconst ξ hξ, ← hMtopdef]
    have hcontα : ContinuousWithinAt g (Ioo α β') α := (hgcont α hαband).mono hβ'band
    have htend : Filter.Tendsto g (nhdsWithin α (Ioo α β')) (nhds (g α)) := hcontα
    have htendM : Filter.Tendsto g (nhdsWithin α (Ioo α β')) (nhds Mtop) := by
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with ξ hξ
      exact (hconstval ξ hξ).symm
    haveI hne : (nhdsWithin α (Ioo α β')).NeBot := left_nhdsWithin_Ioo_neBot hαβ'
    exact tendsto_nhds_unique htend htendM
  have hαns : ¬ Metric.sphere (0 : ℂ) (Real.exp α) ⊆ U := by
    intro hsub; exact hαnotA ⟨by linarith [hαxh, hxhint.2, hδ0'], hsub⟩
  exact hcaseA α (by linarith [hloα, hTlogs']) (by linarith [hαxh, hxhint.2]) hgαMtop hαns

/-- **H6: the star comparison `J ≤ 0`.** For the ring potential `ω = 1_U · u` (`0 ≤ ω ≤ 1`, `U`
open, star surface subharmonic and continuous on `S = {re < 0, 0 < im < π}`, small near `0`,
circles of log-radius `≤ log s` never fully inside `U`, circle mean continuous and affine on
full-circle log-radius intervals) and the Grötzsch potential `vt = 1_{grotzschRing s} · v`
(`0 ≤ vt ≤ 1`, star surface harmonic on `S`, circle mean continuous and affine, right-edge collar
bound), the star comparison `J w = ω★ w − vt★ w` is nonpositive on `S`. Fix `ε > 0` and tilt to
`Q = J − ε·Im`; a strict interior maximum `c* > 0` propagates by the shrinking-rectangle maximum
principle to the top edge, where apex saturation of `ω` (case `e^ξ ⊄ U`) or affineness of the circle
means (case `e^ξ ⊆ U`, reduced to the former at the interval endpoint) yields a contradiction.
Sending `ε → 0` gives `J ≤ 0`. -/
theorem baernstein_J_nonpos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {u v : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hωsub : SubharmonicOn (starPlane 0 (Set.indicator U u))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (hωcont : ContinuousOn (starPlane 0 (Set.indicator U u))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (hvharm : InnerProductSpace.HarmonicOnNhd (starPlane 0 (Set.indicator (grotzschRing s) v))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π})
    (hω1 : ∀ z, Set.indicator U u z ≤ 1) (hω0 : ∀ z, 0 ≤ Set.indicator U u z)
    (hωmeas : Measurable (Set.indicator U u))
    (hωsmall : ∀ c > 0, ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → Set.indicator U u z ≤ c)
    (hωcircle : ∀ ξ : ℝ, ContinuousOn (Set.indicator U u) (Metric.sphere (0 : ℂ) (Real.exp ξ)))
    (hωnotU : ∀ ξ : ℝ, ξ ≤ Real.log s → ¬ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U)
    (hmωcont : ContinuousOn (logCircleMean 0 (Set.indicator U u)) (Iio (0 : ℝ)))
    (hmωaff : ∀ α β : ℝ, Ioo α β ⊆ {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U} →
      ∃ a b : ℝ, ∀ ξ ∈ Ioo α β, logCircleMean 0 (Set.indicator U u) ξ = a + b * ξ)
    (hvmeas : Measurable (Set.indicator (grotzschRing s) v))
    (hv0 : ∀ z, 0 ≤ Set.indicator (grotzschRing s) v z)
    (hv1 : ∀ z, Set.indicator (grotzschRing s) v z ≤ 1)
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hvouter : ∀ z ∈ grotzschOuter, v z = 1)
    (hvb : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1)
    (hmvcont : ContinuousOn (logCircleMean 0 (Set.indicator (grotzschRing s) v)) (Iio (0 : ℝ)))
    (hmvaff : ∀ α β : ℝ, Real.log s ≤ α → β ≤ 0 →
      ∃ a b : ℝ, ∀ ξ ∈ Ioo α β, logCircleMean 0 (Set.indicator (grotzschRing s) v) ξ = a + b * ξ) :
    ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      starPlane 0 (Set.indicator U u) w - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 0 := by
  classical
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set S : Set ℂ := {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} with hSdef
  set ω : ℂ → ℝ := Set.indicator U u with hωdef
  set vt : ℂ → ℝ := Set.indicator (grotzschRing s) v with hvtdef
  set J : ℂ → ℝ := fun w => starPlane 0 ω w - starPlane 0 vt w with hJdef
  -- The star comparison `J` is subharmonic on `S`.
  have hJsub : SubharmonicOn J S := hωsub.sub_harmonicOnNhd hvharm
  have hJcont : ContinuousOn J S := hωcont.sub hvharm.continuousOn
  -- Right- and left-edge decay of `J`.
  have hright := baernstein_right_edge hs0 hs1 hω1 hvc hvouter hvb
  have hleft := baernstein_left_edge (ω := ω) (vt := vt) hωsmall
  -- It suffices to show `J w₀ ≤ ε · Im w₀` for every `ε > 0`.
  suffices hkey : ∀ ε : ℝ, 0 < ε → ∀ w ∈ S, J w - ε * w.im ≤ 0 by
    intro w₀ hw₀
    have hle : ∀ ε : ℝ, 0 < ε → J w₀ ≤ ε * w₀.im := fun ε hε => by linarith [hkey ε hε w₀ hw₀]
    by_contra hcon
    rw [not_le] at hcon
    have hw₀im : 0 < w₀.im := hw₀.2.1
    have hstep := hle (J w₀ / (2 * w₀.im)) (by positivity)
    have heq : J w₀ / (2 * w₀.im) * w₀.im = J w₀ / 2 := by
      field_simp
    rw [heq] at hstep
    linarith [hstep, hcon]
  -- Fix `ε > 0`; set the tilted surface `Q = J − ε·Im` and suppose it is positive somewhere.
  intro ε hε
  set Q : ℂ → ℝ := fun w => J w - ε * w.im with hQdef
  have hQsub : SubharmonicOn Q S :=
    hJsub.sub_harmonicOnNhd ((harmonicOnNhd_tilt ε).mono (subset_univ S))
  have hQcont : ContinuousOn Q S := hJcont.sub (by fun_prop)
  by_contra hcon
  simp only [not_forall, not_le, exists_prop] at hcon
  obtain ⟨w', hw'S, hw'pos⟩ := hcon
  set cs : ℝ := Q w' with hcsdef
  have hcs : 0 < cs := hw'pos
  obtain ⟨hw're, hw'im0, hw'imπ⟩ := hw'S
  -- Right-edge margin `δ' > 0` and left-edge threshold `T' > 0` for the level `cs / 2`.
  obtain ⟨δ', hδ'0, hδ'⟩ := hright (cs / 2) (by positivity)
  obtain ⟨T', hT'0, hT'⟩ := hleft (cs / 2) (by positivity)
  -- The band walls, strictly inside the decay regions, with `w'` in the open band.
  set δ : ℝ := min (δ' / 2) (-w'.re / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδδ' : δ < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδw' : w'.re < -δ := by
    have : δ ≤ -w'.re / 2 := min_le_right _ _; linarith
  have hδ0' : -δ < 0 := by linarith
  set T : ℝ := max (max (T' + 1) (-Real.log s + 1)) (-w'.re + 1) with hTdef
  have hTT' : T' < T := lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hTlogs : -Real.log s < T :=
    lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hTw' : -T < w'.re := by
    have : -w'.re + 1 ≤ T := le_max_right _ _; linarith
  have hδT : -T < -δ := lt_trans hTw' hδw'
  have hTlogs' : -T < Real.log s := by linarith
  -- `[-T, -δ] ⊆ Iio 0`, the domain of circle-mean continuity.
  have hbandIio : Icc (-T) (-δ) ⊆ Iio (0 : ℝ) := fun ξ hξ => lt_of_le_of_lt hξ.2 hδ0'
  -- The top-edge profile `g ξ = m_ω ξ − m_vt ξ − ε·π`, continuous on the band.
  set g : ℝ → ℝ := fun ξ => logCircleMean 0 ω ξ - logCircleMean 0 vt ξ - ε * π with hgdef
  have hgcont : ContinuousOn g (Icc (-T) (-δ)) := by
    apply ContinuousOn.sub _ continuousOn_const
    exact (hmωcont.mono hbandIio).sub (hmvcont.mono hbandIio)
  -- `M_top = sup g` over the compact band, attained at `ξ̂`.
  obtain ⟨xh, hxhmem, hxhmax⟩ := (isCompact_Icc).exists_isMaxOn
    (nonempty_Icc.mpr hδT.le) hgcont
  set Mtop : ℝ := g xh with hMtopdef
  -- Circle bounds `ω, vt ≤ 1` on every circle, for the transfer lemma.
  have hωbd : ∀ ξ : ℝ, ∀ φ : ℝ,
      ω ((0 : ℂ) + (Real.exp ξ : ℂ) * Complex.exp (φ * Complex.I)) ≤ 1 := fun ξ φ => hω1 _
  have hvbd : ∀ ξ : ℝ, ∀ φ : ℝ,
      vt ((0 : ℂ) + (Real.exp ξ : ℂ) * Complex.exp (φ * Complex.I)) ≤ 1 := fun ξ φ => hv1 _
  -- Wedge bound: `Q w ≤ 2·Im w` on `S`.
  have hwedge : ∀ w ∈ S, Q w ≤ 2 * w.im := by
    intro w hw
    obtain ⟨_, hwim0, hwimπ⟩ := hw
    have hUB : starPlane 0 ω w ≤ 2 * w.im := by
      have := starPlane_le_two_mul_aperture (p := (0 : ℂ)) (u := ω) (M := 1) (w := w)
        (by norm_num) (fun φ => by simpa using hωbd w.re φ) hwim0.le hwimπ.le
      simpa using this
    have hvnn0 : (0 : ℝ) ≤ starPlane 0 vt w := ENNReal.toReal_nonneg
    have hεim : 0 ≤ ε * w.im := by positivity
    simp only [hQdef, hJdef]; linarith [hUB, hvnn0, hεim]
  -- Two-sided transfer bound: `|Q(ξ+iθ) − g ξ| ≤ (4+ε)(π−θ)`.
  have htransfer : ∀ ξ θ : ℝ, 0 ≤ θ → θ ≤ π → |Q ((ξ : ℂ) + (θ : ℂ) * Complex.I) - g ξ|
      ≤ (4 + ε) * (π - θ) := by
    intro ξ θ hθ0 hθπ
    set w : ℂ := (ξ : ℂ) + (θ : ℂ) * Complex.I with hwdef
    have hwre : w.re = ξ := by simp [hwdef]
    have hwim : w.im = θ := by simp [hwdef]
    have h := baernstein_top_transfer (ω := ω) (vt := vt) (ε := ε) hε.le hωmeas hvmeas
      hω0 hv0 (w := w) (by rw [hwre]; exact hωbd ξ) (by rw [hwre]; exact hvbd ξ)
      (by rw [hwim]; exact hθ0) (by rw [hwim]; exact hθπ)
    rw [hwre, hwim] at h
    simpa only [hQdef, hJdef, hgdef, hwre, hwim] using h
  -- Box bound: any interior band point is dominated by `max Mtop (cs/2)`.
  have hbox : ∀ pre pim : ℝ, -T < pre → pre < -δ → 0 < pim → pim < π →
      Q ((pre : ℂ) + (pim : ℂ) * Complex.I) ≤ max Mtop (cs / 2) := by
    intro pre pim hpre1 hpre2 hpim0 hpimπ
    set p : ℂ := (pre : ℂ) + (pim : ℂ) * Complex.I with hpdef
    have hpre : p.re = pre := by simp [hpdef]
    have hpim : p.im = pim := by simp [hpdef]
    -- For every small `η` the rectangle bound gives `Q p ≤ max Mtop (cs/2) + (6+ε)η`.
    have hstep : ∀ η : ℝ, 0 < η → η < pim → η < π - pim → η < π - η →
        Q p ≤ max Mtop (cs / 2) + (6 + ε) * η := by
      intro η hη0 hηpim hηπpim hηhalf
      set B : ℝ := max (max (2 * η) (Mtop + (4 + ε) * η)) (cs / 2) with hBdef
      have hbot : ∀ ξ ∈ Icc (-T) (-δ), Q ((ξ : ℂ) + (η : ℂ) * Complex.I) ≤ B := by
        intro ξ hξ
        have hmem : ((ξ : ℂ) + (η : ℂ) * Complex.I) ∈ S := by
          refine ⟨by simp; linarith [hξ.2], by simp [hη0], by simp; linarith [hηhalf]⟩
        have hw := hwedge _ hmem
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hw
        calc Q ((ξ : ℂ) + (η : ℂ) * Complex.I) ≤ 2 * η := hw
          _ ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
      have htop : ∀ ξ ∈ Icc (-T) (-δ),
          Q ((ξ : ℂ) + ((π - η : ℝ) : ℂ) * Complex.I) ≤ B := by
        intro ξ hξ
        have ht := htransfer ξ (π - η) (by linarith) (by linarith)
        have hg : g ξ ≤ Mtop := hxhmax hξ
        rw [show π - (π - η) = η by ring] at ht
        have habs := (abs_le.mp ht).2
        calc Q ((ξ : ℂ) + ((π - η : ℝ) : ℂ) * Complex.I)
            ≤ g ξ + (4 + ε) * η := by linarith [habs]
          _ ≤ Mtop + (4 + ε) * η := by linarith [hg]
          _ ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
      have hleftw : ∀ y ∈ Icc η (π - η), Q ((-T : ℝ) + (y : ℂ) * Complex.I) ≤ B := by
        intro y hy
        have hmem : ((-T : ℝ) + (y : ℂ) * Complex.I) ∈ S := by
          refine ⟨by simp; linarith [hT'0, hTT'], by simp; linarith [hy.1],
            by simp; linarith [hy.2, hη0]⟩
        have hJle := hT' _ hmem (by simp; linarith [hTT'])
        have hy0 : (0 : ℝ) ≤ y := le_trans hη0.le hy.1
        have hqj : Q ((-T : ℝ) + (y : ℂ) * Complex.I) ≤ J ((-T : ℝ) + (y : ℂ) * Complex.I) := by
          simp only [hQdef, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
          linarith [mul_nonneg hε.le hy0]
        calc Q ((-T : ℝ) + (y : ℂ) * Complex.I) ≤ cs / 2 := le_trans hqj hJle
          _ ≤ B := le_max_right _ _
      have hrightw : ∀ y ∈ Icc η (π - η), Q ((-δ : ℝ) + (y : ℂ) * Complex.I) ≤ B := by
        intro y hy
        have hmem : ((-δ : ℝ) + (y : ℂ) * Complex.I) ∈ S := by
          refine ⟨by simp [hδ0'], by simp; linarith [hy.1],
            by simp; linarith [hy.2, hη0]⟩
        have hJle := hδ' _ hmem (by simp; linarith [hδδ'])
        have hy0 : (0 : ℝ) ≤ y := le_trans hη0.le hy.1
        have hqj : Q ((-δ : ℝ) + (y : ℂ) * Complex.I) ≤ J ((-δ : ℝ) + (y : ℂ) * Complex.I) := by
          simp only [hQdef, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
          linarith [mul_nonneg hε.le hy0]
        calc Q ((-δ : ℝ) + (y : ℂ) * Complex.I) ≤ cs / 2 := le_trans hqj hJle
          _ ≤ B := le_max_right _ _
      have hpmem : p ∈ Ioo (-T) (-δ) ×ℂ Ioo η (π - η) := by
        rw [Complex.mem_reProdIm, hpre, hpim]
        exact ⟨⟨hpre1, hpre2⟩, hηpim, by linarith [hηπpim]⟩
      have hpQ : Q p ≤ B :=
        baernstein_rect_max hQsub hQcont hδT hδ0' hη0 (by linarith) hbot htop hleftw hrightw p hpmem
      have hBle : B ≤ max Mtop (cs / 2) + (6 + ε) * η := by
        rw [hBdef]
        refine max_le (max_le ?_ ?_) ?_
        · have : (0 : ℝ) ≤ max Mtop (cs / 2) := le_trans (by positivity) (le_max_right _ _)
          nlinarith [this, hη0, hε.le]
        · have h1 : Mtop ≤ max Mtop (cs / 2) := le_max_left _ _
          nlinarith [h1, hη0, hε.le]
        · have : (0 : ℝ) ≤ (6 + ε) * η := by positivity
          linarith [le_max_right Mtop (cs / 2)]
      linarith [hpQ, hBle]
    -- Send `η → 0`.
    by_contra hcon
    rw [not_le] at hcon
    set d : ℝ := Q p - max Mtop (cs / 2) with hddef
    have hd0 : 0 < d := by rw [hddef]; linarith
    set η : ℝ := min (min (pim / 2) ((π - pim) / 2)) (min (π / 4) (d / (2 * (6 + ε)))) with hηdef
    have hη0 : 0 < η := by
      rw [hηdef]; refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) ?_)
      positivity
    have hηpim : η < pim := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    have hηπpim : η < π - pim :=
      lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    have hηhalf : η < π - η := by
      have : η ≤ π / 4 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hηd : η ≤ d / (2 * (6 + ε)) := (min_le_right _ _).trans (min_le_right _ _)
    have hstepη := hstep η hη0 hηpim hηπpim hηhalf
    have h6ε : (0 : ℝ) < 6 + ε := by linarith
    have hlt : (6 + ε) * η ≤ d / 2 := by
      have hstep2 := mul_le_mul_of_nonneg_left hηd h6ε.le
      have heq : (6 + ε) * (d / (2 * (6 + ε))) = d / 2 := by
        field_simp
      rw [heq] at hstep2
      exact hstep2
    rw [hddef] at hlt; linarith [hstepη]
  -- The box bound at `w'` forces `Mtop ≥ cs`.
  have hMtopcs : cs ≤ Mtop := by
    have hbw' := hbox w'.re w'.im hTw' hδw' hw'im0 hw'imπ
    rw [Complex.re_add_im] at hbw'
    rcases le_max_iff.mp hbw' with h | h
    · exact h
    · linarith [h, hcs]
  have hMtop0 : 0 < Mtop := lt_of_lt_of_le hcs hMtopcs
  -- Edge bounds: `g (-T) ≤ cs/2` and `g (-δ) ≤ cs/2`, forcing `xh` to be interior.
  have hgedge : ∀ ξ : ℝ, (ξ = -T ∨ ξ = -δ) → g ξ ≤ cs / 2 := by
    intro ξ hξ
    -- `g ξ ≤ Q(ξ+iθ) + (4+ε)(π−θ) ≤ cs/2 + (4+ε)(π−θ)` for `θ → π`.
    have hgle : ∀ θ : ℝ, 0 < θ → θ < π → g ξ ≤ cs / 2 + (4 + ε) * (π - θ) := by
      intro θ hθ0 hθπ
      have hmem : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ S := by
        rcases hξ with h | h <;> subst h
        · exact ⟨by simp; linarith [hT'0, hTT'], by simp [hθ0], by simp; linarith⟩
        · exact ⟨by simp [hδ0'], by simp [hθ0], by simp; linarith⟩
      have hQle : Q ((ξ : ℂ) + (θ : ℂ) * Complex.I) ≤ cs / 2 := by
        have him : ((ξ : ℂ) + (θ : ℂ) * Complex.I).im = θ := by simp
        have hQJ : Q ((ξ : ℂ) + (θ : ℂ) * Complex.I) ≤ J ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
          simp only [hQdef]; rw [him]; linarith [mul_nonneg hε.le hθ0.le]
        have hJle : J ((ξ : ℂ) + (θ : ℂ) * Complex.I) ≤ cs / 2 := by
          rcases hξ with h | h <;> subst h
          · exact hT' _ hmem (by simp; linarith [hTT'])
          · exact hδ' _ hmem (by simp; linarith [hδδ'])
        linarith [hQJ, hJle]
      have ht := (abs_le.mp (htransfer ξ θ hθ0.le hθπ.le)).1
      linarith [hQle, ht]
    -- Take `θ → π`: the residual `(4+ε)(π−θ)` vanishes.
    by_contra hcon
    rw [not_le] at hcon
    set r : ℝ := g ξ - cs / 2 with hrdef
    have hr0 : 0 < r := by rw [hrdef]; linarith
    set θ : ℝ := π - min (π / 2) (r / (2 * (4 + ε))) with hθdef
    have hmin0 : 0 < min (π / 2) (r / (2 * (4 + ε))) := lt_min (by linarith) (by positivity)
    have hθ0 : 0 < θ := by
      rw [hθdef]; have := min_le_left (π / 2) (r / (2 * (4 + ε))); linarith
    have hθπ : θ < π := by rw [hθdef]; linarith
    have hπθ : π - θ = min (π / 2) (r / (2 * (4 + ε))) := by rw [hθdef]; ring
    have hle := hgle θ hθ0 hθπ
    have hπθr : (4 + ε) * (π - θ) < r := by
      rw [hπθ]
      have h1 : min (π / 2) (r / (2 * (4 + ε))) ≤ r / (2 * (4 + ε)) := min_le_right _ _
      have h2 : (4 + ε) * (r / (2 * (4 + ε))) = r / 2 := by field_simp
      calc (4 + ε) * min (π / 2) (r / (2 * (4 + ε)))
          ≤ (4 + ε) * (r / (2 * (4 + ε))) := by
            apply mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = r / 2 := h2
        _ < r := by linarith
    rw [hrdef] at hπθr; linarith [hle]
  -- `xh` is strictly interior: the edge values are `< Mtop`.
  have hxhint : -T < xh ∧ xh < -δ := by
    obtain ⟨hxh1, hxh2⟩ := hxhmem
    refine ⟨lt_of_le_of_ne hxh1 (fun h => ?_), lt_of_le_of_ne hxh2 (fun h => ?_)⟩
    · have : Mtop ≤ cs / 2 := by rw [hMtopdef, ← h]; exact hgedge _ (Or.inl rfl)
      linarith [hMtopcs, hcs]
    · have : Mtop ≤ cs / 2 := by rw [hMtopdef, h]; exact hgedge _ (Or.inr rfl)
      linarith [hMtopcs, hcs]
  have hxhre0 : xh < 0 := lt_trans hxhint.2 hδ0'
  -- A helper: the case-(a) exclusion at any log-radius `ζ ∈ [-T, -δ]` where `e^ζ ⊄ U` and
  -- `g ζ = Mtop`, contradicting the box bound via the pinch.
  have hcaseA : ∀ ζ : ℝ, -T < ζ → ζ < -δ → g ζ = Mtop →
      ¬ Metric.sphere (0 : ℂ) (Real.exp ζ) ⊆ U → False := by
    intro ζ hζ1 hζ2 hζg hζU
    -- The zero-extension `ω` has a zero on the circle of radius `e^ζ` (case (a)).
    obtain ⟨z, hzsph, hzω⟩ := indicator_zero_of_sphere_not_subset (u := u) hζU
    have hzero : ∃ z ∈ Metric.sphere (0 : ℂ) (Real.exp ζ), ω z = 0 := ⟨z, hzsph, hzω⟩
    -- Pinch: near full aperture `Q(ζ+iθ)` strictly exceeds `g ζ = Mtop`.
    obtain ⟨θ₀, hθ₀mem, hpinch⟩ := baernstein_case_a_pinch (ω := ω) (vt := vt) (ξ := ζ)
      hωmeas (hωcircle ζ) hω0 hzero hvmeas hv0 (fun φ => hvbd ζ φ) hε
    -- Choose `θ ∈ [θ₀, π)` close enough to `π` to sit inside the band.
    set θ : ℝ := max θ₀ (π / 2) with hθdef
    have hθ0lo : θ₀ ≤ θ := le_max_left _ _
    have hθπ2 : π / 2 ≤ θ := le_max_right _ _
    have hθπ : θ < π := max_lt hθ₀mem.2 (by linarith)
    have hθ0 : 0 < θ := lt_of_lt_of_le (by linarith) hθπ2
    have hpθ := hpinch θ ⟨hθ0lo, hθπ⟩
    -- Box bound at the interior point `ζ + iθ`.
    have hboxθ := hbox ζ θ hζ1 hζ2 hθ0 hθπ
    -- `Q(ζ+iθ) = starPlane 0 ω − starPlane 0 vt − ε·θ` (the pinch form).
    have hQform : Q ((ζ : ℂ) + (θ : ℂ) * Complex.I)
        = starPlane 0 ω ((ζ : ℂ) + (θ : ℂ) * Complex.I)
          - starPlane 0 vt ((ζ : ℂ) + (θ : ℂ) * Complex.I) - ε * θ := by
      have him : ((ζ : ℂ) + (θ : ℂ) * Complex.I).im = θ := by simp
      simp only [hQdef, hJdef]; rw [him]
    rw [hQform] at hboxθ
    -- The pinch gives `Q(ζ+iθ) ≥ g ζ + (ε/2)(π−θ) = Mtop + (ε/2)(π−θ) > Mtop ≥ max Mtop (cs/2)`.
    have hgζMtop : logCircleMean 0 ω ζ - logCircleMean 0 vt ζ - ε * π = Mtop := by
      rw [← hζg, hgdef]
    have hπθpos : 0 < ε / 2 * (π - θ) := _root_.mul_pos (by positivity) (by linarith)
    have hMax : max Mtop (cs / 2) = Mtop := max_eq_left (by linarith [hMtopcs, hcs])
    rw [hMax] at hboxθ
    linarith [hpθ, hboxθ, hπθpos, hgζMtop]
  -- Final case split at `xh`, where `g xh = Mtop`.
  set A : Set ℝ := {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U} with hAdef
  -- The top-edge profile `g` is affine on every full-circle log-radius interval inside `A`.
  have hgaffAll : ∀ α β : ℝ, Real.log s ≤ α → β ≤ 0 →
      Ioo α β ⊆ A → ∃ a b : ℝ, ∀ ξ ∈ Ioo α β, g ξ = a + b * ξ := by
    intro α β hloα hβ0 hsubA
    obtain ⟨aω, bω, hmωeq⟩ := hmωaff α β (fun ξ hξ => hsubA hξ)
    obtain ⟨av, bv, hmveq⟩ := hmvaff α β hloα hβ0
    exact ⟨aω - av - ε * π, bω - bv, fun ξ hξ => by
      rw [hgdef]; simp only; rw [hmωeq ξ hξ, hmveq ξ hξ]; ring⟩
  by_cases hxhA : xh ∈ A
  · -- Case (b): full circle `e^xh` inside `U`; reduce to case (a) at the interval endpoint.
    exact baernstein_case_b_reduce (s := s) hUopen hTlogs' hδ0' hωnotU hgaffAll hgcont
      hxhint hxhmax hMtopdef hxhA hcaseA
  · -- Case (a): the full circle `e^xh` is not inside `U`.
    have hns : ¬ Metric.sphere (0 : ℂ) (Real.exp xh) ⊆ U := by
      intro hsub; exact hxhA ⟨hxhre0, hsub⟩
    exact hcaseA xh hxhint.1 hxhint.2 rfl hns

/-! ### H7 The circle-means comparison -/

/-- **H7: the circle-means comparison.** For two potentials `ω`, `vt` (measurable, nonnegative and
bounded by `1`) whose star comparison `J = ω★ − vt★` is nonpositive on the
half-strip `S = {re < 0, 0 < im < π}` (the conclusion of `baernstein_J_nonpos`), the circle means
satisfy `logCircleMean 0 ω ξ ≤ logCircleMean 0 vt ξ` for every log-radius `ξ < 0`. Writing the mean
difference as `(m_ω − ω★) + J + (vt★ − m_v)` at aperture `θ`, the two apex deficits and `J` are each
`≤ 4·(π − θ) + 0`, which vanishes as `θ → π`. -/
theorem logCircleMean_comparison {ω vt : ℂ → ℝ}
    (hωmeas : Measurable ω) (hvmeas : Measurable vt)
    (hωnn : ∀ z, 0 ≤ ω z) (hvnn : ∀ z, 0 ≤ vt z)
    (hω1 : ∀ z, ω z ≤ 1) (hv1 : ∀ z, vt z ≤ 1)
    (hJ : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      starPlane 0 ω w - starPlane 0 vt w ≤ 0) :
    ∀ ξ : ℝ, ξ < 0 → logCircleMean 0 ω ξ ≤ logCircleMean 0 vt ξ := by
  intro ξ hξ
  have hπ : (0 : ℝ) < π := Real.pi_pos
  -- The mean difference is `≤ 4·(π − θ)` for every aperture `θ ∈ (0, π)`.
  have hbound : ∀ θ : ℝ, 0 < θ → θ < π →
      logCircleMean 0 ω ξ - logCircleMean 0 vt ξ ≤ 4 * (π - θ) := by
    intro θ hθ0 hθπ
    set w : ℂ := (ξ : ℂ) + (θ : ℂ) * Complex.I with hwdef
    have hwre : w.re = ξ := by simp [hwdef]
    have hwim : w.im = θ := by simp [hwdef]
    have hwS : w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} :=
      ⟨by rw [hwre]; exact hξ, by rw [hwim]; exact hθ0, by rw [hwim]; exact hθπ⟩
    have hJw := hJ w hwS
    -- Apex deficits, both bounded by `2·(π − θ)`.
    have hbω := starPlane_sub_logCircleMean_le (p := (0 : ℂ)) (u := ω) (M := 1) (w := w)
      (by norm_num) hωmeas (fun z _ => hωnn z) (fun φ => by simpa using hω1 _)
      (by rw [hwim]; exact hθ0.le) (by rw [hwim]; exact hθπ.le)
    have hbv := starPlane_sub_logCircleMean_le (p := (0 : ℂ)) (u := vt) (M := 1) (w := w)
      (by norm_num) hvmeas (fun z _ => hvnn z) (fun φ => by simpa using hv1 _)
      (by rw [hwim]; exact hθ0.le) (by rw [hwim]; exact hθπ.le)
    rw [show (2 : ℝ) * 1 = 2 by norm_num, hwre, hwim] at hbω hbv
    have h1 := (abs_le.mp hbω).1
    have h2 := (abs_le.mp hbv).2
    linarith [hJw, h1, h2]
  -- Take `θ → π`: the residual `4·(π − θ)` vanishes.
  by_contra hcon
  rw [not_le] at hcon
  set r : ℝ := logCircleMean 0 ω ξ - logCircleMean 0 vt ξ with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  set θ : ℝ := π - min (π / 2) (r / 8) with hθdef
  have hmin0 : 0 < min (π / 2) (r / 8) := lt_min (by linarith) (by positivity)
  have hθ0 : 0 < θ := by
    rw [hθdef]; have := min_le_left (π / 2) (r / 8); linarith
  have hθπ : θ < π := by rw [hθdef]; linarith
  have hπθ : π - θ = min (π / 2) (r / 8) := by rw [hθdef]; ring
  have hle := hbound θ hθ0 hθπ
  have hlt : 4 * (π - θ) < r := by
    rw [hπθ]
    calc 4 * min (π / 2) (r / 8) ≤ 4 * (r / 8) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ < r := by linarith
  rw [hrdef] at hlt; linarith [hle]

end RiemannDynamics
