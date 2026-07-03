import RiemannDynamics.Analysis.GrotzschEnergy
import RiemannDynamics.Analysis.SequentialIBP
import RiemannDynamics.Analysis.GrotzschPotential
import RiemannDynamics.Analysis.BaernsteinN16
import RiemannDynamics.QC.Regularity.ModulusEnergy
import RiemannDynamics.QC.Regularity.RingModulus

/-!
# The Grötzsch keystone: modulus dominated by ring-potential energy

For `0 < s < 1`, the Grötzsch modulus is bounded above by the Dirichlet energy of any admissible
ring potential of a competing ring `(E, U)` whose boundary data matches the Grötzsch problem.

## Main result

* `grotzschModulus_le_dirichletEnergy_ringPotential` — assembling the four links
  `curveModulus_connecting_le_dirichletEnergy` (M0-upper), `dirichletEnergy_grotzschRing_eq_slope`
  (energy = collar slope), the star-comparison slope reversal `b_v ≤ b_u`, and
  `slope_le_energy_ringPotential'''` (slope ≤ energy).
-/

open Set Real MeasureTheory Complex
open scoped ENNReal

namespace RiemannDynamics

/-- **Continuity of the zero-extension across the low-modulus frontier.** For a ring potential `u`
continuous up to `closure U` and vanishing on the part of `frontier U` inside the unit disk, the
zero-extension `Set.indicator U u` is continuous on any open annulus `{rI < ‖z‖ < rO}` capped by the
unit circle (`rO ≤ 1`): interior points see `u`, exterior points see `0`, and frontier points inside
the disk carry `u = 0`, so the two branches agree there. -/
theorem indicator_continuousOn_annulus {u : ℂ → ℝ} {U : Set ℂ} {rI rO : ℝ} (hUopen : IsOpen U)
    (hrO1 : rO ≤ 1) (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0) :
    ContinuousOn (Set.indicator U u) {z : ℂ | rI < ‖z‖ ∧ ‖z‖ < rO} := by
  set A : Set ℂ := {z : ℂ | rI < ‖z‖ ∧ ‖z‖ < rO} with hAdef
  -- On `A ∩ closure U` the indicator agrees with `u`; off `closure U` it is `0`.
  have hIu : ∀ z ∈ A ∩ closure U, Set.indicator U u z = u z := by
    rintro z ⟨hzA, hzcl⟩
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]
    · rw [Set.indicator_of_notMem hzU]
      have hzfr : z ∈ frontier U := by
        rw [frontier, hUopen.interior_eq]; exact ⟨hzcl, hzU⟩
      exact (hE0 z hzfr (lt_of_lt_of_le hzA.2 hrO1)).symm
  have hI0 : ∀ z ∈ A ∩ (closure U)ᶜ, Set.indicator U u z = (fun _ : ℂ => (0 : ℝ)) z := by
    rintro z ⟨-, hzcl⟩
    exact Set.indicator_of_notMem (a := z) (f := u) (fun hzU => hzcl (subset_closure hzU))
  -- The two pieces are continuous; their union covers `A`.
  have hcont_cl : ContinuousOn (Set.indicator U u) (A ∩ closure U) :=
    (hucont.mono Set.inter_subset_right).congr hIu
  have hcont_out : ContinuousOn (Set.indicator U u) (A ∩ (closure U)ᶜ) :=
    continuousOn_const.congr hI0
  -- Glue pointwise via `A = (A ∩ closure U) ∪ (A ∩ (closure U)ᶜ)`.
  have hcover : A = (A ∩ closure U) ∪ (A ∩ (closure U)ᶜ) := by
    rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  rw [hcover]
  intro z hzA
  refine ContinuousWithinAt.union ?_ ?_
  · -- The closed piece `A ∩ closure U`.
    rcases em (z ∈ closure U) with hzcl | hzcl
    · exact hcont_cl z ⟨(hcover ▸ hzA), hzcl⟩
    · refine continuousWithinAt_of_notMem_closure (fun hz => hzcl ?_)
      exact closure_minimal Set.inter_subset_right isClosed_closure hz
  · -- The relatively open piece `A ∩ (closure U)ᶜ`, on which the value is the constant `0`.
    by_cases hzU : z ∈ U
    · -- Interior: the piece lies in the closed set `Uᶜ`, which excludes `z`.
      refine continuousWithinAt_of_notMem_closure (fun hz => ?_)
      have hsub : closure (A ∩ (closure U)ᶜ) ⊆ Uᶜ := by
        refine closure_minimal ?_ hUopen.isClosed_compl
        exact fun w hw => fun hwU => hw.2 (subset_closure hwU)
      exact (hsub hz) hzU
    · by_cases hzcl : z ∈ closure U
      · -- Frontier: `indicator z = 0`, matching the constant value on the piece.
        have hindz : Set.indicator U u z = 0 := Set.indicator_of_notMem (f := u) hzU
        exact (continuousWithinAt_const (x := z) (s := A ∩ (closure U)ᶜ)).congr
          (fun w hw => (hI0 w hw)) hindz
      · -- Exterior: `z ∈ (closure U)ᶜ`, an open neighbourhood, so lies in the piece if in `A`.
        exact hcont_out z ⟨(hcover ▸ hzA), hzcl⟩

/-- **Subharmonicity of the zero-extended star surface on the half-strip.** For a ring potential `u`
harmonic on the open competing ring `U`, valued nonnegatively, continuous up to `closure U`, and
vanishing on the frontier inside the unit disk, the log-polar star surface of `Set.indicator U u` is
subharmonic on the whole unbounded half-strip `{re < 0, 0 < im < π}`.  Subharmonicity is a local
property (`subharmonicOn_of_locally`): each point sits in a bounded log-polar strip capped by the
unit circle, where `starPlane_subharmonicOn_indicator` applies (its annulus-continuity input is the
across-frontier continuity `indicator_continuousOn_annulus`). -/
theorem starPlane_subharmonicOn_halfStrip {u : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hu0 : ∀ z, 0 ≤ Set.indicator U u z)
    (hum : Measurable (Set.indicator U u)) (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0) :
    SubharmonicOn (starPlane 0 (Set.indicator U u))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} := by
  set S : Set ℂ := {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} with hSdef
  have hSopen : IsOpen S := by
    have h1 : IsOpen {w : ℂ | w.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    have h2 : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    have h3 : IsOpen {w : ℂ | w.im < π} := isOpen_lt Complex.continuous_im continuous_const
    have : S = {w : ℂ | w.re < 0} ∩ ({w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < π}) := by
      ext w; simp [hSdef, Set.mem_inter_iff]
    rw [this]; exact h1.inter (h2.inter h3)
  -- For each `w ∈ S`, a bounded log-polar strip through `w` inside `S` carrying subharmonicity.
  have hstrip : ∀ w ∈ S, ∃ rI rO : ℝ, 0 < rI ∧ rI < rO ∧ rO ≤ 1 ∧
      w ∈ logPolarStrip rI rO ∧
      SubharmonicOn (starPlane 0 (Set.indicator U u)) (logPolarStrip rI rO) := by
    intro w hw
    obtain ⟨hwre, hwim0, hwimπ⟩ := hw
    refine ⟨Real.exp (w.re - 1), min 1 (Real.exp (w.re + 1)), Real.exp_pos _, ?_, ?_, ?_, ?_⟩
    · exact lt_min (by
        have : Real.exp (w.re - 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        simpa using this) (Real.exp_lt_exp.mpr (by linarith))
    · exact min_le_left _ _
    · refine ⟨⟨?_, ?_⟩, hwim0, hwimπ⟩
      · rw [Real.log_exp]; linarith
      · rcases le_or_gt (Real.exp (w.re + 1)) 1 with hle | hlt
        · rw [min_eq_right hle, Real.log_exp]; linarith
        · rw [min_eq_left hlt.le, Real.log_one]; exact hwre
    · have hrI : (0 : ℝ) < Real.exp (w.re - 1) := Real.exp_pos _
      have hrO1 : min 1 (Real.exp (w.re + 1)) ≤ 1 := min_le_left _ _
      have hrIrO : Real.exp (w.re - 1) < min 1 (Real.exp (w.re + 1)) :=
        lt_min (by
          have : Real.exp (w.re - 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
          simpa using this) (Real.exp_lt_exp.mpr (by linarith))
      have hharm : InnerProductSpace.HarmonicOnNhd u
          (U ∩ {z : ℂ | Real.exp (w.re - 1) < ‖z - (0 : ℂ)‖ ∧
            ‖z - (0 : ℂ)‖ < min 1 (Real.exp (w.re + 1))}) :=
        hu.mono Set.inter_subset_left
      have hcont : ContinuousOn (Set.indicator U u)
          {z : ℂ | Real.exp (w.re - 1) < ‖z - (0 : ℂ)‖ ∧
            ‖z - (0 : ℂ)‖ < min 1 (Real.exp (w.re + 1))} := by
        have := indicator_continuousOn_annulus (u := u) (U := U)
          (rI := Real.exp (w.re - 1)) (rO := min 1 (Real.exp (w.re + 1)))
          hUopen hrO1 hucont hE0
        simpa only [sub_zero] using this
      exact starPlane_subharmonicOn_indicator hrI hrIrO hUopen hharm hu0 hum hcont
  -- Each strip is open and lies in `S`.
  have hstripOpen : ∀ rI rO : ℝ, IsOpen (logPolarStrip rI rO) := by
    intro rI rO
    have heq : logPolarStrip rI rO
        = (Complex.re ⁻¹' Set.Ioo (Real.log rI) (Real.log rO))
          ∩ (Complex.im ⁻¹' Set.Ioo (0 : ℝ) π) := by
      ext w; simp [logPolarStrip, Set.mem_inter_iff]
    rw [heq]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  -- Glue via `subharmonicOn_of_locally`.
  refine subharmonicOn_of_locally hSopen ?_ ?_
  · intro w hw
    obtain ⟨rI, rO, hrI, hrIrO, hrO1, hwmem, hsub⟩ := hstrip w hw
    refine (hsub.1 w hwmem).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin_of_mem_nhds ((hstripOpen rI rO).mem_nhds hwmem)
  · intro c hc
    obtain ⟨rI, rO, _, _, _, hcmem, hsub⟩ := hstrip c hc
    obtain ⟨r₀, hr₀0, hr₀⟩ := Metric.isOpen_iff.mp (hstripOpen rI rO) c hcmem
    refine ⟨r₀, hr₀0, fun r hr hrr₀ _ => ?_⟩
    refine hsub.2 c hcmem r hr ?_
    exact (Metric.closedBall_subset_ball hrr₀).trans hr₀

/-- **Continuity of the zero-extended circle mean below the unit circle.** For a ring potential `u`
harmonic on the open ring `U`, valued in `[0, 1]`, continuous up to `closure U`, and vanishing on
the frontier inside the unit disk, the log-polar circle mean of `Set.indicator U u` is continuous on
`Iio 0`: the star surface is continuous on every bounded strip
(`starPlane_subharmonicOn_halfStrip`), and `logCircleMean_continuousOn` transfers this to the mean
on the corresponding log-radius interval, covering `Iio 0`. -/
theorem logCircleMean_indicator_continuousOn_Iio {u : ℂ → ℝ} {U : Set ℂ} (hUopen : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hu0 : ∀ z, 0 ≤ Set.indicator U u z)
    (hu1 : ∀ z, Set.indicator U u z ≤ 1) (hum : Measurable (Set.indicator U u))
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0) :
    ContinuousOn (logCircleMean 0 (Set.indicator U u)) (Iio (0 : ℝ)) := by
  have hsub := starPlane_subharmonicOn_halfStrip hUopen hu hu0 hum hucont hE0
  intro ξ₀ hξ₀
  have hξ₀neg : ξ₀ < 0 := hξ₀
  -- A bounded strip around `ξ₀`: log-radii in `(ξ₀ - 1, 0)` capped by the unit circle.
  set rI : ℝ := Real.exp (ξ₀ - 1) with hrIdef
  have hlogrI : Real.log rI = ξ₀ - 1 := by rw [hrIdef, Real.log_exp]
  have hcont : ContinuousOn (starPlane 0 (Set.indicator U u)) (logPolarStrip rI 1) := by
    refine (hsub.1).mono (fun w hw => ?_)
    obtain ⟨⟨hre1, hre2⟩, him0, himπ⟩ := hw
    rw [Real.log_one] at hre2
    exact ⟨hre2, him0, himπ⟩
  have hmean := logCircleMean_continuousOn (f := Set.indicator U u) (rI := rI) (rO := 1) (M := 1)
    (by norm_num) hum hu0 (fun ξ _ φ => hu1 _) hcont
  rw [Real.log_one] at hmean
  have hmemIoo : ξ₀ ∈ Ioo (Real.log rI) (0 : ℝ) := ⟨by rw [hlogrI]; linarith, hξ₀neg⟩
  refine (hmean ξ₀ hmemIoo).mono_of_mem_nhdsWithin ?_
  refine mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hmemIoo)

/-- **Link L1 + L2 (Grötzsch potential side).** For `0 < s < 1` and `v` the Grötzsch potential of
`grotzschRing s` (harmonic, continuous up to the closure, `0` on the slit, `1` on the circle,
range `[0, 1]`), whose collar circle mean is `2π + b·ξ`, the Grötzsch modulus is bounded by
`ENNReal.ofReal b`: the connecting-family modulus is `≤ D(v)` by M0-upper, and `D(v)` equals
`ofReal b` by the collar-slope identity. -/
theorem grotzschModulus_le_ofReal_slope {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {v : ℂ → ℝ}
    (hvh : InnerProductSpace.HarmonicOnNhd v (grotzschRing s))
    (hvc : ContinuousOn v (closure (grotzschRing s)))
    (hv0 : ∀ z ∈ grotzschInner s, v z = 0) (hv1 : ∀ z ∈ grotzschOuter, v z = 1)
    (hvrange : ∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) {b : ℝ}
    (hslope : ∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + b * ξ) :
    grotzschModulus s ≤ ENNReal.ofReal b := by
  have hL1 : curveModulus (connectingCurveFamily (grotzschInner s) grotzschOuter (grotzschRing s))
      ≤ dirichletEnergy v (grotzschRing s) := by
    refine curveModulus_connecting_le_dirichletEnergy (isOpen_grotzschRing hs0.le)
      (hvh.contDiffOn.of_le (by norm_num)) hvc hv0 hv1
  rw [grotzschModulus]
  calc curveModulus (connectingCurveFamily (grotzschInner s) grotzschOuter (grotzschRing s))
      ≤ dirichletEnergy v (grotzschRing s) := hL1
    _ = ENNReal.ofReal b :=
        dirichletEnergy_grotzschRing_eq_slope hs0 hs1 hvh hvc hv0 hv1 hvrange hslope

/-- **Link L3 (slope reversal).** With `ω̃ = 1_U · u` and `ṽ = 1_{grotzschRing s} · v` measurable,
valued in `[0, 1]`, if the star comparison `starPlane 0 ω̃ − starPlane 0 ṽ ≤ 0` holds on the open
half-strip `{re < 0, 0 < im < π}`, then `Baernstein`'s circle-mean comparison forces the collar
slopes to reverse: `b_v ≤ b_u`.  On the common collar `(log r₀, 0)` (where full circles lie in both
`U` and `grotzschRing s`) the indicator means agree with the potential means `2π + b_u·ξ` and
`2π + b_v·ξ`; the inequality at a single negative log-radius flips the slope. -/
theorem slope_reversal {s r₀ : ℝ} (hs0 : 0 < s) (hsr₀ : s < r₀) (hr₀1 : r₀ < 1)
    {u v : ℂ → ℝ} {U : Set ℂ} (bu bv : ℝ)
    (humeas : Measurable (Set.indicator U u))
    (hvmeas : Measurable (Set.indicator (grotzschRing s) v))
    (hunn : ∀ z, 0 ≤ Set.indicator U u z) (hvnn : ∀ z, 0 ≤ Set.indicator (grotzschRing s) v z)
    (hu1 : ∀ z, Set.indicator U u z ≤ 1) (hv1 : ∀ z, Set.indicator (grotzschRing s) v z ≤ 1)
    (hcollarU : ∀ ξ ∈ Ioo (Real.log r₀) 0, Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U)
    (huslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + bu * ξ)
    (hvslope : ∀ ξ ∈ Ioo (Real.log s) 0, logCircleMean 0 v ξ = 2 * π + bv * ξ)
    (hJ : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      starPlane 0 (Set.indicator U u) w - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 0) :
    bv ≤ bu := by
  have hloglt : Real.log r₀ < 0 := Real.log_neg (lt_trans hs0 hsr₀) hr₀1
  -- Baernstein circle-mean comparison for the indicator extensions.
  have hcmp := logCircleMean_comparison humeas hvmeas hunn hvnn hu1 hv1 hJ
  -- Pick a single negative log-radius in the common collar `(log r₀, 0)`.
  set ξ₀ : ℝ := Real.log r₀ / 2 with hξ₀def
  have hξ₀mem : ξ₀ ∈ Ioo (Real.log r₀) 0 := ⟨by rw [hξ₀def]; linarith, by rw [hξ₀def]; linarith⟩
  have hξ₀neg : ξ₀ < 0 := hξ₀mem.2
  -- Full circles at `ξ₀` lie in both domains, so indicator means agree with potential means.
  have hsphU : Metric.sphere (0 : ℂ) (Real.exp ξ₀) ⊆ U := hcollarU ξ₀ hξ₀mem
  have hsphV : Metric.sphere (0 : ℂ) (Real.exp ξ₀) ⊆ grotzschRing s := by
    refine sphere_subset_grotzschRing hs0.le ?_ ?_
    · calc s = Real.exp (Real.log s) := (Real.exp_log hs0).symm
        _ < Real.exp ξ₀ := Real.exp_lt_exp.mpr (by
            have : Real.log s < Real.log r₀ := Real.log_lt_log hs0 hsr₀
            linarith [hξ₀mem.1])
    · calc Real.exp ξ₀ < Real.exp 0 := Real.exp_lt_exp.mpr hξ₀neg
        _ = 1 := Real.exp_zero
  have hξ₀v : ξ₀ ∈ Ioo (Real.log s) 0 :=
    ⟨lt_trans (Real.log_lt_log hs0 hsr₀) hξ₀mem.1, hξ₀neg⟩
  have hmu : logCircleMean 0 (Set.indicator U u) ξ₀ = 2 * π + bu * ξ₀ := by
    rw [logCircleMean_indicator_eq hsphU, huslope ξ₀ hξ₀mem]
  have hmv : logCircleMean 0 (Set.indicator (grotzschRing s) v) ξ₀ = 2 * π + bv * ξ₀ := by
    rw [logCircleMean_indicator_eq hsphV, hvslope ξ₀ hξ₀v]
  -- `2π + bu·ξ₀ ≤ 2π + bv·ξ₀` with `ξ₀ < 0` gives `bu·ξ₀ ≤ bv·ξ₀`, i.e. `bv ≤ bu`.
  have hchain := hcmp ξ₀ hξ₀neg
  rw [hmu, hmv] at hchain
  have hmul : bu * ξ₀ ≤ bv * ξ₀ := by linarith
  exact (mul_le_mul_right_of_neg hξ₀neg).mp hmul

/-- **The Grötzsch keystone (ring-potential form).** For `0 < s < 1` let `U` be an open competing
ring in the unit disk with `s < r₀ < 1`, whose full outer collar `{r₀ < |z| < 1}` lies in `U`, and
let `u` be an admissible ring potential: harmonic on `U`, continuous up to `closure U`, `1` on the
unit circle, vanishing on the low-modulus frontier, valued in `[0, 1]`.  Then the Grötzsch modulus
is bounded by the Dirichlet energy of `u`.

The proof chains the four links: `grotzschModulus s ≤ ofReal b_v` (M0-upper plus the collar-slope
energy identity for the Grötzsch potential `v`), the star-comparison slope reversal `b_v ≤ b_u`, and
`b_u ≤ (D u U).toReal` (the flux–energy slope bound), reassembled as
`D u U = ofReal (D u U).toReal` when `D u U` is finite (trivial otherwise).

The single genuinely open input is `hstar`, the Baernstein star-surface comparison on the half-strip
(subharmonicity of the zero-extended star surface on the whole punctured disk is not available in
this form); everything else is discharged from the ring-potential data. -/
theorem grotzschModulus_le_dirichletEnergy_ringPotential {s r₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsr₀ : s < r₀) (hr₀1 : r₀ < 1) {u : ℂ → ℝ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hcollarSub : RoundAnnulus 0 r₀ 1 ⊆ U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U))
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hstar : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π}, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (grotzschRing s) →
      ContinuousOn v (closure (grotzschRing s)) →
      (∀ z ∈ grotzschInner s, v z = 0) → (∀ z ∈ grotzschOuter, v z = 1) →
      (∀ z ∈ grotzschRing s, 0 ≤ v z ∧ v z ≤ 1) →
      starPlane 0 (Set.indicator U u) w
        - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 0) :
    grotzschModulus s ≤ dirichletEnergy u U := by
  classical
  have hr₀0 : 0 < r₀ := lt_trans hs0 hsr₀
  -- The Grötzsch potential `v` and its collar slope `b_v`.
  obtain ⟨v, hvh, hvc, hv0, hv1, hvrange⟩ := exists_grotzschPotential hs0 hs1
  obtain ⟨bv, hbv⟩ := exists_logCircleMean_slope hs0 hs1
    (hvh.mono (roundAnnulus_subset_grotzschRing hs0.le))
    (hvc.mono (by
      rw [closure_grotzschRing hs0.le]
      exact fun z hz => Metric.mem_closedBall.mpr hz.2))
    hv1
  -- The ring-potential collar data: annulus harmonicity, exp-membership, ranges, slope `b_u`.
  have hann : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1) := hu.mono hcollarSub
  have hcollarExp : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro ξ hξlo hξhi θ
    refine hcollarSub ?_
    have hnorm : ‖Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ = Real.exp ξ := by
      rw [Complex.norm_exp]; simp
    refine ⟨?_, ?_⟩
    · rw [dist_zero_right, hnorm]
      calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log hr₀0).symm
        _ < Real.exp ξ := Real.exp_lt_exp.mpr hξlo
    · rw [dist_zero_right, hnorm]
      calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξhi
        _ = 1 := Real.exp_zero
  have hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1 :=
    fun z hz => hrangeU z (hcollarSub hz)
  obtain ⟨bu, hbu⟩ := exists_logCircleMean_slope hr₀0 hr₀1 hann hcont hone
  -- L1 + L2: `grotzschModulus s ≤ ofReal b_v`.
  have hstep12 : grotzschModulus s ≤ ENNReal.ofReal bv :=
    grotzschModulus_le_ofReal_slope hs0 hs1 hvh hvc hv0 hv1 hvrange hbv
  -- L3: slope reversal `b_v ≤ b_u` from the star comparison `hstar`.
  have hJ : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      starPlane 0 (Set.indicator U u) w
        - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 0 :=
    fun w hw => hstar w hw v hvh hvc hv0 hv1 hvrange
  have humeas : Measurable (Set.indicator U u) := by
    have := ContinuousOn.measurable_piecewise hu.continuousOn continuous_zero.continuousOn
      hUopen.measurableSet
    rwa [Set.piecewise_eq_indicator] at this
  have hvmeas : Measurable (Set.indicator (grotzschRing s) v) := by
    have := ContinuousOn.measurable_piecewise hvh.continuousOn continuous_zero.continuousOn
      (isOpen_grotzschRing hs0.le).measurableSet
    rwa [Set.piecewise_eq_indicator] at this
  have hstep3 : bv ≤ bu := by
    refine slope_reversal hs0 hsr₀ hr₀1 bu bv humeas hvmeas ?_ ?_ ?_ ?_
      ?_ hbu hbv hJ
    · intro z
      by_cases hz : z ∈ U
      · rw [Set.indicator_of_mem hz]; exact (hrangeU z hz).1
      · rw [Set.indicator_of_notMem hz]
    · intro z
      by_cases hz : z ∈ grotzschRing s
      · rw [Set.indicator_of_mem hz]; exact (hvrange z hz).1
      · rw [Set.indicator_of_notMem hz]
    · intro z
      by_cases hz : z ∈ U
      · rw [Set.indicator_of_mem hz]; exact (hrangeU z hz).2
      · rw [Set.indicator_of_notMem hz]; norm_num
    · intro z
      by_cases hz : z ∈ grotzschRing s
      · rw [Set.indicator_of_mem hz]; exact (hvrange z hz).2
      · rw [Set.indicator_of_notMem hz]; norm_num
    · intro ξ hξ
      refine subset_trans (fun z hz => ?_) hcollarSub
      have hznorm : ‖z‖ = Real.exp ξ := by rwa [Metric.mem_sphere, dist_zero_right] at hz
      refine ⟨?_, ?_⟩
      · rw [dist_zero_right, hznorm]
        calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log hr₀0).symm
          _ < Real.exp ξ := Real.exp_lt_exp.mpr hξ.1
      · rw [dist_zero_right, hznorm]
        calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξ.2
          _ = 1 := Real.exp_zero
  -- L4: slope ≤ energy `b_u ≤ (D u U).toReal`, then reassemble the chain.
  by_cases hDfin : dirichletEnergy u U = ⊤
  · rw [hDfin]; exact le_top
  · have hstep4 : bu ≤ (dirichletEnergy u U).toReal :=
      slope_le_energy_ringPotential''' hr₀0 hr₀1 hUopen hu hpos hnc hcontR hcollarExp hann hcont
        hone hrange hbu hrangeU hucont hE0 hEInt hDfin
    calc grotzschModulus s ≤ ENNReal.ofReal bv := hstep12
      _ ≤ ENNReal.ofReal bu := ENNReal.ofReal_le_ofReal hstep3
      _ ≤ ENNReal.ofReal (dirichletEnergy u U).toReal := ENNReal.ofReal_le_ofReal hstep4
      _ = dirichletEnergy u U := ENNReal.ofReal_toReal hDfin

/-- **The Grötzsch keystone (ring-potential form, Baernstein premise discharged).** Identical to
`grotzschModulus_le_dirichletEnergy_ringPotential`, except the opaque star-comparison premise
`hstar` (which is essentially the conclusion of Baernstein's inequality) is replaced by the three
concrete geometric facts about the competing ring `U` that Baernstein's argument actually consumes:

* `hωsmall` — the potential vanishes (uniformly) near the puncture at the origin;
* `hωcircle` — the zero-extension is continuous on every centred circle;
* `hωnotU` — no full circle of radius `≤ s` is contained in `U` (the separation property).

All the *local* Baernstein inputs — subharmonicity of the zero-extended star surface on the whole
half-strip (`starPlane_subharmonicOn_halfStrip`), harmonicity of the Grötzsch star surface
(`starPlane_harmonicOn_grotzsch`), circle-mean continuity
(`logCircleMean_indicator_continuousOn_Iio`) and affinity on full-circle intervals
(`logCircleMean_affine_on_fullCircles`) — are discharged here from the ring-potential data, so
`baernstein_J_nonpos` supplies the slope-reversal comparison and the keystone chain closes. -/
theorem grotzschModulus_le_dirichletEnergy_ringPotential' {s r₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsr₀ : s < r₀) (hr₀1 : r₀ < 1) {u : ℂ → ℝ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hcollarSub : RoundAnnulus 0 r₀ 1 ⊆ U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U))
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hωsmall : ∀ c > 0, ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → Set.indicator U u z ≤ c)
    (hωcircle : ∀ ξ : ℝ, ContinuousOn (Set.indicator U u) (Metric.sphere (0 : ℂ) (Real.exp ξ)))
    (hωnotU : ∀ ξ : ℝ, ξ ≤ Real.log s → ¬ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U) :
    grotzschModulus s ≤ dirichletEnergy u U := by
  classical
  -- Zero-extension bookkeeping shared with the base keystone.
  have hω0 : ∀ z, 0 ≤ Set.indicator U u z := by
    intro z
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz]; exact (hrangeU z hz).1
    · rw [Set.indicator_of_notMem hz]
  have hω1 : ∀ z, Set.indicator U u z ≤ 1 := by
    intro z
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz]; exact (hrangeU z hz).2
    · rw [Set.indicator_of_notMem hz]; norm_num
  have humeas : Measurable (Set.indicator U u) := by
    have := ContinuousOn.measurable_piecewise hu.continuousOn continuous_zero.continuousOn
      hUopen.measurableSet
    rwa [Set.piecewise_eq_indicator] at this
  -- Local Baernstein inputs on the `ω`-side, discharged from the ring-potential data.
  have hωsub : SubharmonicOn (starPlane 0 (Set.indicator U u))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} :=
    starPlane_subharmonicOn_halfStrip hUopen hu hω0 humeas hucont hE0
  have hmωcont : ContinuousOn (logCircleMean 0 (Set.indicator U u)) (Iio (0 : ℝ)) :=
    logCircleMean_indicator_continuousOn_Iio hUopen hu hω0 hω1 humeas hucont hE0
  have hmωaff : ∀ α β : ℝ,
      Ioo α β ⊆ {ξ : ℝ | ξ < 0 ∧ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U} →
      ∃ a b : ℝ, ∀ ξ ∈ Ioo α β, logCircleMean 0 (Set.indicator U u) ξ = a + b * ξ := by
    intro α β hsub
    rcases lt_or_ge α β with hαβ | hαβ
    · have hexpαβ : Real.exp α < Real.exp β := Real.exp_lt_exp.mpr hαβ
      have hAU : RoundAnnulus 0 (Real.exp α) (Real.exp β) ⊆ U := by
        intro z hz
        obtain ⟨hlo, hhi⟩ := hz
        rw [dist_zero_right] at hlo hhi
        have hzξ : Real.log ‖z‖ ∈ Ioo α β := by
          constructor
          · have := Real.log_lt_log (Real.exp_pos α) hlo; rwa [Real.log_exp] at this
          · have := Real.log_lt_log (lt_of_lt_of_le (Real.exp_pos α) hlo.le) hhi
            rwa [Real.log_exp] at this
        have hmem := (hsub hzξ).2
        refine hmem (Metric.mem_sphere.mpr ?_)
        rw [dist_zero_right, Real.exp_log (lt_of_lt_of_le (Real.exp_pos α) hlo.le)]
      have hharm : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 (Real.exp α) (Real.exp β)) :=
        hu.mono hAU
      obtain ⟨a, b, hab⟩ := logCircleMean_affine_on_fullCircles (Real.exp_pos α) hexpαβ hAU hharm
      refine ⟨a, b, fun ξ hξ => hab ξ ?_⟩
      rw [Real.log_exp, Real.log_exp]; exact hξ
    · exact ⟨0, 0, fun ξ hξ => absurd hξ (by simp [Ioo_eq_empty (not_lt.mpr hαβ)])⟩
  -- The Grötzsch potential `v`, its star surface (harmonic on the half-strip) and slope `b_v`.
  obtain ⟨v, hvh, hvc, hv0, hv1, hvrange⟩ := exists_grotzschPotential hs0 hs1
  have hvmeas : Measurable (Set.indicator (grotzschRing s) v) := by
    have := ContinuousOn.measurable_piecewise hvh.continuousOn continuous_zero.continuousOn
      (isOpen_grotzschRing hs0.le).measurableSet
    rwa [Set.piecewise_eq_indicator] at this
  have hvharm : InnerProductSpace.HarmonicOnNhd
      (starPlane 0 (Set.indicator (grotzschRing s) v))
      {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π} :=
    starPlane_harmonicOn_grotzsch hs0 hs1 hvh hvc hv0 hv1 hvrange
  have hv0' : ∀ z, 0 ≤ Set.indicator (grotzschRing s) v z := by
    intro z
    by_cases hz : z ∈ grotzschRing s
    · rw [Set.indicator_of_mem hz]; exact (hvrange z hz).1
    · rw [Set.indicator_of_notMem hz]
  have hv1' : ∀ z, Set.indicator (grotzschRing s) v z ≤ 1 := by
    intro z
    by_cases hz : z ∈ grotzschRing s
    · rw [Set.indicator_of_mem hz]; exact (hvrange z hz).2
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hmvcont : ContinuousOn (logCircleMean 0 (Set.indicator (grotzschRing s) v)) (Iio (0 : ℝ)) :=
    logCircleMean_indicator_continuousOn_Iio (isOpen_grotzschRing hs0.le)
      (hvh) hv0' hv1' hvmeas hvc
      (by
        -- On `frontier (grotzschRing s) ∩ {‖z‖ < 1}` the potential `v` vanishes: those points lie
        -- on the slit `grotzschInner s`, where `hv0` applies.
        intro z hzfr hzlt
        have hzcl : z ∈ closure (grotzschRing s) := frontier_subset_closure hzfr
        rw [closure_grotzschRing hs0.le] at hzcl
        by_cases hzslit : z ∈ grotzschInner s
        · exact hv0 z hzslit
        · exfalso
          have hznotU : z ∉ grotzschRing s := by
            rw [frontier, (isOpen_grotzschRing hs0.le).interior_eq] at hzfr; exact hzfr.2
          exact hznotU ⟨Metric.mem_ball.mpr (by rwa [dist_zero_right]), hzslit⟩)
  have hmvaff : ∀ α β : ℝ, Real.log s ≤ α → β ≤ 0 →
      ∃ a b : ℝ, ∀ ξ ∈ Ioo α β,
        logCircleMean 0 (Set.indicator (grotzschRing s) v) ξ = a + b * ξ := by
    intro α β hloα hβ0
    rcases lt_or_ge α β with hαβ | hαβ
    · have hexpαβ : Real.exp α < Real.exp β := Real.exp_lt_exp.mpr hαβ
      have hAU : RoundAnnulus 0 (Real.exp α) (Real.exp β) ⊆ grotzschRing s := by
        intro z hz
        obtain ⟨hlo, hhi⟩ := hz
        rw [dist_zero_right] at hlo hhi
        have hslo : s < ‖z‖ := by
          calc s = Real.exp (Real.log s) := (Real.exp_log hs0).symm
            _ ≤ Real.exp α := Real.exp_le_exp.mpr hloα
            _ < ‖z‖ := hlo
        have hhi1 : ‖z‖ < 1 := by
          calc ‖z‖ < Real.exp β := hhi
            _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hβ0
            _ = 1 := Real.exp_zero
        exact sphere_subset_grotzschRing hs0.le hslo hhi1
          (Metric.mem_sphere.mpr (by rw [dist_zero_right]))
      have hharm : InnerProductSpace.HarmonicOnNhd v
          (RoundAnnulus 0 (Real.exp α) (Real.exp β)) := hvh.mono hAU
      obtain ⟨a, b, hab⟩ := logCircleMean_affine_on_fullCircles (Real.exp_pos α) hexpαβ hAU hharm
      refine ⟨a, b, fun ξ hξ => hab ξ ?_⟩
      rw [Real.log_exp, Real.log_exp]; exact hξ
    · exact ⟨0, 0, fun ξ hξ => absurd hξ (by simp [Ioo_eq_empty (not_lt.mpr hαβ)])⟩
  -- Baernstein's slope-reversal comparison, fully discharged.
  have hJ : ∀ w ∈ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < π},
      starPlane 0 (Set.indicator U u) w
        - starPlane 0 (Set.indicator (grotzschRing s) v) w ≤ 0 :=
    baernstein_J_nonpos hs0 hs1 hUopen hωsub hωsub.1 hvharm hω1 hω0 humeas
      hωsmall hωcircle hωnotU hmωcont hmωaff hvmeas hv0' hv1' hvc hv1 hvrange hmvcont hmvaff
  -- Assemble the keystone chain (L1+L2, L3 slope reversal via `hJ`, L4 slope ≤ energy).
  have hr₀0 : 0 < r₀ := lt_trans hs0 hsr₀
  obtain ⟨bv, hbv⟩ := exists_logCircleMean_slope hs0 hs1
    (hvh.mono (roundAnnulus_subset_grotzschRing hs0.le))
    (hvc.mono (by
      rw [closure_grotzschRing hs0.le]
      exact fun z hz => Metric.mem_closedBall.mpr hz.2))
    hv1
  have hann : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1) := hu.mono hcollarSub
  have hcollarExp : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro ξ hξlo hξhi θ
    refine hcollarSub ?_
    have hnorm : ‖Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)‖ = Real.exp ξ := by
      rw [Complex.norm_exp]; simp
    refine ⟨?_, ?_⟩
    · rw [dist_zero_right, hnorm]
      calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log hr₀0).symm
        _ < Real.exp ξ := Real.exp_lt_exp.mpr hξlo
    · rw [dist_zero_right, hnorm]
      calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξhi
        _ = 1 := Real.exp_zero
  have hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1 :=
    fun z hz => hrangeU z (hcollarSub hz)
  obtain ⟨bu, hbu⟩ := exists_logCircleMean_slope hr₀0 hr₀1 hann hcont hone
  have hstep12 : grotzschModulus s ≤ ENNReal.ofReal bv :=
    grotzschModulus_le_ofReal_slope hs0 hs1 hvh hvc hv0 hv1 hvrange hbv
  have hstep3 : bv ≤ bu :=
    slope_reversal hs0 hsr₀ hr₀1 bu bv humeas hvmeas hω0 hv0' hω1 hv1'
      (fun ξ hξ => by
        refine subset_trans (fun z hz => ?_) hcollarSub
        have hznorm : ‖z‖ = Real.exp ξ := by rwa [Metric.mem_sphere, dist_zero_right] at hz
        refine ⟨?_, ?_⟩
        · rw [dist_zero_right, hznorm]
          calc r₀ = Real.exp (Real.log r₀) := (Real.exp_log hr₀0).symm
            _ < Real.exp ξ := Real.exp_lt_exp.mpr hξ.1
        · rw [dist_zero_right, hznorm]
          calc Real.exp ξ < Real.exp 0 := Real.exp_lt_exp.mpr hξ.2
            _ = 1 := Real.exp_zero)
      hbu hbv hJ
  by_cases hDfin : dirichletEnergy u U = ⊤
  · rw [hDfin]; exact le_top
  · have hstep4 : bu ≤ (dirichletEnergy u U).toReal :=
      slope_le_energy_ringPotential''' hr₀0 hr₀1 hUopen hu hpos hnc hcontR hcollarExp hann hcont
        hone hrange hbu hrangeU hucont hE0 hEInt hDfin
    calc grotzschModulus s ≤ ENNReal.ofReal bv := hstep12
      _ ≤ ENNReal.ofReal bu := ENNReal.ofReal_le_ofReal hstep3
      _ ≤ ENNReal.ofReal (dirichletEnergy u U).toReal := ENNReal.ofReal_le_ofReal hstep4
      _ = dirichletEnergy u U := ENNReal.ofReal_toReal hDfin

/-- **The Grötzsch keystone (ring-potential form, all Baernstein premises discharged).** Identical
to `grotzschModulus_le_dirichletEnergy_ringPotential'`, except the three concrete ω-side geometric
premises `hωsmall`, `hωcircle`, `hωnotU` are replaced by the underlying ring geometry that produces
them: the competing ring `U` lies in the unit disk (`hUball`), its low-modulus frontier continuum
`E` is connected, contains the puncture `0` and the slit tip `s`, and sits inside the frontier
(`hEfront`).  From this row Baernstein's three consumed facts are derived:

* `hωnotU` — since `E ⊆ frontier U` is disjoint from the open `U` and `radial_reach` puts a point of
  `E` on every sphere of radius `≤ s`, no such sphere lies inside `U`;
* `hωcircle` — the zero-extension is continuous on every centred circle: circles of radius `> 1` and
  the unit circle avoid `U` (giving the constant `0`), and circles inside the disk are handled by
  `indicator_continuousOn_annulus`;
* `hωsmall` — `u` is continuous at the puncture `0 ∈ closure U` with value `0` (from `0 ∈ E` and the
  frontier-vanishing `hE0`), so the zero-extension is uniformly small near `0`. -/
theorem grotzschModulus_le_dirichletEnergy_ringPotential'' {s r₀ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsr₀ : s < r₀) (hr₀1 : r₀ < 1) {u : ℂ → ℝ} {U E : Set ℂ}
    (hUopen : IsOpen U)
    (hUball : U ⊆ Metric.ball (0 : ℂ) 1)
    (hcollarSub : RoundAnnulus 0 r₀ 1 ⊆ U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U))
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hEconn : IsConnected E) (h0E : (0 : ℂ) ∈ E) (hsE : (s : ℂ) ∈ E)
    (hEfront : E ⊆ frontier U) :
    grotzschModulus s ≤ dirichletEnergy u U := by
  classical
  -- Frontier points of the open set `U` are outside `U`; in particular `E ∩ U = ∅`.
  have hfrontNotU : ∀ z ∈ frontier U, z ∉ U := by
    intro z hz
    rw [frontier, hUopen.interior_eq] at hz; exact hz.2
  -- `D1` `hωnotU`: no sphere of radius `≤ s` lies inside `U`.
  have hωnotU : ∀ ξ : ℝ, ξ ≤ Real.log s → ¬ Metric.sphere (0 : ℂ) (Real.exp ξ) ⊆ U := by
    intro ξ hξ hsub
    have hexpξ : Real.exp ξ ≤ s := by
      calc Real.exp ξ ≤ Real.exp (Real.log s) := Real.exp_le_exp.mpr hξ
        _ = s := Real.exp_log hs0
    obtain ⟨z, hzsph, hzE⟩ :=
      radial_reach hs0 hEconn h0E hsE ⟨(Real.exp_pos ξ).le, hexpξ⟩
    exact hfrontNotU z (hEfront hzE) (hsub hzsph)
  -- `D3` `hωcircle`: the zero-extension is continuous on every centred circle.
  have hωcircle : ∀ ξ : ℝ,
      ContinuousOn (Set.indicator U u) (Metric.sphere (0 : ℂ) (Real.exp ξ)) := by
    intro ξ
    rcases lt_or_ge (Real.exp ξ) 1 with hlt | hge
    · -- Inside the disk: the sphere sits in the open annulus `{exp ξ / 2 < ‖z‖ < 1}`.
      have hsphsub : Metric.sphere (0 : ℂ) (Real.exp ξ)
          ⊆ {z : ℂ | Real.exp ξ / 2 < ‖z‖ ∧ ‖z‖ < 1} := by
        intro z hz
        have hznorm : ‖z‖ = Real.exp ξ := by rwa [Metric.mem_sphere, dist_zero_right] at hz
        exact ⟨by rw [hznorm]; linarith [Real.exp_pos ξ], by rw [hznorm]; exact hlt⟩
      exact (indicator_continuousOn_annulus (rI := Real.exp ξ / 2) (rO := 1)
        hUopen le_rfl hucont hE0).mono hsphsub
    · -- Radius `≥ 1`: the whole sphere avoids `U ⊆ ball 0 1`, so the indicator is the constant `0`.
      have hconst : ∀ z ∈ Metric.sphere (0 : ℂ) (Real.exp ξ),
          Set.indicator U u z = (fun _ : ℂ => (0 : ℝ)) z := by
        intro z hz
        have hznorm : ‖z‖ = Real.exp ξ := by rwa [Metric.mem_sphere, dist_zero_right] at hz
        have hzU : z ∉ U := fun hzU => by
          have := hUball hzU; rw [mem_ball_zero_iff, hznorm] at this; linarith
        exact Set.indicator_of_notMem (f := u) hzU
      exact continuousOn_const.congr hconst
  -- `D2` `hωsmall`: the zero-extension is uniformly small near the puncture `0`.
  have h0front : (0 : ℂ) ∈ frontier U := hEfront h0E
  have hu00 : u 0 = 0 := hE0 0 h0front (by simp)
  have h0cl : (0 : ℂ) ∈ closure U := frontier_subset_closure h0front
  have hωsmall : ∀ c > 0, ∃ ρ > 0, ∀ z : ℂ, ‖z‖ < ρ → Set.indicator U u z ≤ c := by
    intro c hc
    have hcwa : ContinuousWithinAt u (closure U) 0 := hucont 0 h0cl
    rw [Metric.continuousWithinAt_iff] at hcwa
    obtain ⟨ρ, hρ0, hρ⟩ := hcwa c hc
    refine ⟨ρ, hρ0, fun z hz => ?_⟩
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]
      have hzcl : z ∈ closure U := subset_closure hzU
      have hzball : dist z 0 < ρ := by rw [dist_zero_right]; exact hz
      have := hρ hzcl hzball
      rw [hu00, Real.dist_eq, sub_zero] at this
      exact le_of_lt (lt_of_abs_lt this)
    · rw [Set.indicator_of_notMem hzU]; exact hc.le
  exact grotzschModulus_le_dirichletEnergy_ringPotential' hs0 hs1 hsr₀ hr₀1 hUopen hcollarSub hu
    hucont hone hE0 hrangeU hpos hnc hcontR hEInt hcont hωsmall hωcircle hωnotU

end RiemannDynamics
