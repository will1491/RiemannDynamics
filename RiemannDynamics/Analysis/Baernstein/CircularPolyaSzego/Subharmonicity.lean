/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Baernstein.CircularPolyaSzego.ArcComparison

/-!
# Baernstein's theorem: the star function is subharmonic

Final part of the Baernstein star-function development
(`Analysis/Baernstein/CircularPolyaSzego/Basic.lean`,
`Analysis/Baernstein/CircularPolyaSzego/ArcComparison.lean`).
The star surface `starPlane p u` on the log-polar strip is realized locally as a supremum of the
harmonic arc integrals of the first file, attained on the structured arc supplied by the second.
Continuity plus that local supremum representation give the sub-mean-value inequality, hence
subharmonicity.

## Main results

* `RiemannDynamics.starPlane_continuousOn` — continuity of the star function on the open strip.
* `RiemannDynamics.starPlane_subMeanValue_small` — the sub-mean-value inequality at a point of the
  strip for all sufficiently small radii, given a structured attaining set there and
  subharmonicity of the arc integrals.
* `RiemannDynamics.starPlane_subharmonicOn` — **Baernstein's theorem**: the star function of a
  nonnegative harmonic function is subharmonic in log-polar coordinates on the open strip.
* `RiemannDynamics.starPlane_subMeanValue` — the sub-mean-value inequality at every centre and
  radius whose closed disk lies in the strip.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

variable {T : ℝ} {g : ℝ → ℝ≥0∞}

/-- **Continuity of the star function on the log-polar strip.** For `u` continuous on the annulus
and nonnegative, `starPlane p u` is continuous on the open strip: the aperture dependence is
continuous from the layer-cake representation by dominated convergence, and the radial dependence
is continuous because the circle profiles of a continuous function vary continuously in `L¹`. -/
theorem starPlane_continuousOn {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hucont : ContinuousOn u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u) :
    ContinuousOn (starPlane p u) (logPolarStrip rI rO) := by
  intro w₀ hw₀
  obtain ⟨hw₀re, hw₀im⟩ := hw₀
  -- A compact log-radius window `[a, b]` around `Re w₀` inside `(log rI, log rO)`.
  set a : ℝ := (Real.log rI + w₀.re) / 2 with hadef
  set b : ℝ := (w₀.re + Real.log rO) / 2 with hbdef
  have ha1 : Real.log rI < a := by rw [hadef]; linarith [hw₀re.1]
  have ha2 : a < w₀.re := by rw [hadef]; linarith [hw₀re.1]
  have hb1 : w₀.re < b := by rw [hbdef]; linarith [hw₀re.2]
  have hb2 : b < Real.log rO := by rw [hbdef]; linarith [hw₀re.2]
  have hw₀ab : w₀.re ∈ Icc a b := ⟨ha2.le, hb1.le⟩
  -- The radial family of circle profiles entering `starFunction`.
  set g : ℝ → ℝ → ℝ≥0∞ := fun ξ φ => ENNReal.ofReal
    ((angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp ξ) φ).toReal) with hgdef
  have hgm : ∀ ξ : ℝ, Measurable (g ξ) := by
    intro ξ
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp ξ)))
  have hgV : ∀ ξ φ : ℝ, g ξ φ
      = ENNReal.ofReal (u (p + (Real.exp ξ : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I))) := by
    intro ξ φ
    rw [hgdef]
    simp only [angularProfile]
    rw [ENNReal.toReal_ofReal (hu0 _)]
  have hSP : ∀ w : ℂ, starPlane p u w = (starProfile (2 * π) (g w.re) w.im).toReal := by
    intro w
    rw [hgdef]
    rfl
  -- The circle sample map is continuous on the compact window.
  have hQcomp : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) (2 * π)) := isCompact_Icc.prod isCompact_Icc
  have hVcont : ContinuousOn
      (fun q : ℝ × ℝ => u (p + (Real.exp q.1 : ℂ) * Complex.exp ((q.2 - π : ℝ) * Complex.I)))
      (Icc a b ×ˢ Icc (0 : ℝ) (2 * π)) := by
    have hPhi : Continuous
        (fun q : ℝ × ℝ => p + (Real.exp q.1 : ℂ) * Complex.exp ((q.2 - π : ℝ) * Complex.I)) := by
      fun_prop
    refine hucont.comp hPhi.continuousOn ?_
    rintro ⟨ξ, φ⟩ ⟨hξ, -⟩
    simp only [Set.mem_setOf_eq]
    have hnorm : ‖p + (Real.exp ξ : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I) - p‖
        = Real.exp ξ := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, Real.abs_exp]
      simp [Complex.mul_re]
    rw [hnorm]
    constructor
    · have hlt := Real.exp_lt_exp.mpr (lt_of_lt_of_le ha1 hξ.1)
      rwa [Real.exp_log hrI] at hlt
    · have hlt := Real.exp_lt_exp.mpr (lt_of_le_of_lt hξ.2 hb2)
      rwa [Real.exp_log (lt_trans hrI hrO)] at hlt
  -- A uniform bound `M` for the circle samples over the window.
  obtain ⟨M, hM⟩ := hQcomp.exists_bound_of_continuousOn hVcont
  have hM0 : 0 ≤ M := by
    have h0mem : ((w₀.re, 0) : ℝ × ℝ) ∈ Icc a b ×ˢ Icc (0 : ℝ) (2 * π) :=
      Set.mk_mem_prod hw₀ab ⟨le_refl 0, by positivity⟩
    exact le_trans (norm_nonneg _) (hM _ h0mem)
  have hgle : ∀ ξ ∈ Icc a b, ∀ φ ∈ Icc (0 : ℝ) (2 * π), g ξ φ ≤ ENNReal.ofReal M := by
    intro ξ hξ φ hφ
    rw [hgV ξ φ]
    exact ENNReal.ofReal_le_ofReal
      (le_trans (le_abs_self _) (hM (ξ, φ) (Set.mk_mem_prod hξ hφ)))
  -- The pointwise bound transfers to the symmetric-decreasing rearrangement.
  have hrearr : ∀ ξ ∈ Icc a b, ∀ x : ℝ,
      decreasingRearrangeSymm (2 * π) (g ξ) x ≤ ENNReal.ofReal M := by
    intro ξ hξ x
    by_contra hcon
    have hlt : ENNReal.ofReal M < decreasingRearrange (2 * π) (g ξ) (2 * |x - 2 * π / 2|) :=
      not_le.mp hcon
    rw [lt_decreasingRearrange_iff] at hlt
    have hempty : distribFun (2 * π) (g ξ) (ENNReal.ofReal M) = 0 := by
      have hset : {y ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal M < g ξ y} = ∅ := by
        ext y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro hy
        exact not_lt.mpr (hgle ξ hξ y hy)
      rw [distribFun, hset, measure_empty]
    rw [hempty] at hlt
    exact absurd hlt (not_lt.mpr (zero_le _))
  -- Aperture Lipschitz bound: widening the centered arc adds at most the boundary mass.
  have hthetaLip : ∀ ξ ∈ Icc a b, ∀ θ θ' : ℝ, θ ≤ θ' →
      starProfile (2 * π) (g ξ) θ'
        ≤ starProfile (2 * π) (g ξ) θ + ENNReal.ofReal (2 * M * (θ' - θ)) := by
    intro ξ hξ θ θ' hθθ'
    have hMθ : 0 ≤ M * (θ' - θ) := mul_nonneg hM0 (by linarith)
    have hpiece : ∀ c d : ℝ, d - c ≤ θ' - θ →
        (∫⁻ x in Icc c d, decreasingRearrangeSymm (2 * π) (g ξ) x)
          ≤ ENNReal.ofReal (M * (θ' - θ)) := by
      intro c d hcd
      calc (∫⁻ x in Icc c d, decreasingRearrangeSymm (2 * π) (g ξ) x)
          ≤ ∫⁻ _ in Icc c d, ENNReal.ofReal M := lintegral_mono fun x => hrearr ξ hξ x
        _ = ENNReal.ofReal M * volume (Icc c d) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal M * ENNReal.ofReal (θ' - θ) := by
            refine mul_le_mul_right ?_ _
            rw [Real.volume_Icc]
            exact ENNReal.ofReal_le_ofReal hcd
        _ = ENNReal.ofReal (M * (θ' - θ)) := (ENNReal.ofReal_mul hM0).symm
    have hsub : Icc (2 * π / 2 - θ') (2 * π / 2 + θ')
        ⊆ Icc (2 * π / 2 - θ) (2 * π / 2 + θ)
          ∪ (Icc (2 * π / 2 - θ') (2 * π / 2 - θ) ∪ Icc (2 * π / 2 + θ) (2 * π / 2 + θ')) := by
      intro x hx
      rcases le_or_gt x (2 * π / 2 - θ) with h | h
      · exact Or.inr (Or.inl ⟨hx.1, h⟩)
      · rcases le_or_gt x (2 * π / 2 + θ) with h2 | h2
        · exact Or.inl ⟨h.le, h2⟩
        · exact Or.inr (Or.inr ⟨h2.le, hx.2⟩)
    calc starProfile (2 * π) (g ξ) θ'
        = ∫⁻ x in Icc (2 * π / 2 - θ') (2 * π / 2 + θ'),
            decreasingRearrangeSymm (2 * π) (g ξ) x := rfl
      _ ≤ ∫⁻ x in Icc (2 * π / 2 - θ) (2 * π / 2 + θ)
            ∪ (Icc (2 * π / 2 - θ') (2 * π / 2 - θ)
              ∪ Icc (2 * π / 2 + θ) (2 * π / 2 + θ')),
            decreasingRearrangeSymm (2 * π) (g ξ) x := lintegral_mono_set hsub
      _ ≤ (∫⁻ x in Icc (2 * π / 2 - θ) (2 * π / 2 + θ),
              decreasingRearrangeSymm (2 * π) (g ξ) x)
            + ∫⁻ x in Icc (2 * π / 2 - θ') (2 * π / 2 - θ)
                ∪ Icc (2 * π / 2 + θ) (2 * π / 2 + θ'),
                decreasingRearrangeSymm (2 * π) (g ξ) x := lintegral_union_le _ _ _
      _ ≤ starProfile (2 * π) (g ξ) θ
            + ((∫⁻ x in Icc (2 * π / 2 - θ') (2 * π / 2 - θ),
                  decreasingRearrangeSymm (2 * π) (g ξ) x)
              + ∫⁻ x in Icc (2 * π / 2 + θ) (2 * π / 2 + θ'),
                  decreasingRearrangeSymm (2 * π) (g ξ) x) :=
          add_le_add le_rfl (lintegral_union_le _ _ _)
      _ ≤ starProfile (2 * π) (g ξ) θ
            + (ENNReal.ofReal (M * (θ' - θ)) + ENNReal.ofReal (M * (θ' - θ))) :=
          add_le_add le_rfl (add_le_add (hpiece _ _ (by linarith)) (hpiece _ _ (by linarith)))
      _ = starProfile (2 * π) (g ξ) θ + ENNReal.ofReal (2 * M * (θ' - θ)) := by
          rw [← ENNReal.ofReal_add hMθ hMθ,
            show M * (θ' - θ) + M * (θ' - θ) = 2 * M * (θ' - θ) from by ring]
  -- Two-sided aperture estimate via monotonicity.
  have htheta : ∀ ξ ∈ Icc a b, ∀ θ θ' : ℝ, 0 ≤ θ → 0 ≤ θ' →
      starProfile (2 * π) (g ξ) θ'
        ≤ starProfile (2 * π) (g ξ) θ + ENNReal.ofReal (2 * M * |θ' - θ|) := by
    intro ξ hξ θ θ' hθ0 hθ'0
    rcases le_total θ' θ with h | h
    · exact le_trans
        (monotone_starProfile (2 * π) (g ξ) (Set.mem_Ici.mpr hθ'0) (Set.mem_Ici.mpr hθ0) h)
        le_self_add
    · have hLip := hthetaLip ξ hξ θ θ' h
      rwa [abs_of_nonneg (sub_nonneg.mpr h)]
  -- Radial comparison: uniformly close circle profiles have close star profiles.
  have hxi : ∀ ξ ξ' θ : ℝ, 0 ≤ θ → θ ≤ π → ∀ ε : ℝ,
      (∀ φ ∈ Icc (0 : ℝ) (2 * π), g ξ φ ≤ g ξ' φ + ENNReal.ofReal ε) →
      starProfile (2 * π) (g ξ) θ
        ≤ starProfile (2 * π) (g ξ') θ + ENNReal.ofReal ε * ENNReal.ofReal (2 * π) := by
    intro ξ ξ' θ hθ0 hθπ ε hcomp
    rw [starProfile_eq_iSup_setLIntegral (by positivity) (hgm ξ) hθ0 (by linarith)]
    refine iSup₂_le ?_
    rintro E ⟨hEmeas, hEsub, hEvol⟩
    have h1 : (∫⁻ φ in E, g ξ φ) ≤ ∫⁻ φ in E, (g ξ' φ + ENNReal.ofReal ε) :=
      setLIntegral_mono' hEmeas fun φ hφ => hcomp φ (hEsub hφ)
    have h2 : (∫⁻ φ in E, (g ξ' φ + ENNReal.ofReal ε))
        = (∫⁻ φ in E, g ξ' φ) + ENNReal.ofReal ε * volume E := by
      rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    have h3 : (∫⁻ φ in E, g ξ' φ) ≤ starProfile (2 * π) (g ξ') θ := by
      rw [starProfile_eq_iSup_setLIntegral (by positivity) (hgm ξ') hθ0 (by linarith)]
      exact le_iSup₂_of_le E ⟨hEmeas, hEsub, hEvol⟩ le_rfl
    calc (∫⁻ φ in E, g ξ φ)
        ≤ (∫⁻ φ in E, g ξ' φ) + ENNReal.ofReal ε * volume E := h2 ▸ h1
      _ ≤ starProfile (2 * π) (g ξ') θ + ENNReal.ofReal ε * ENNReal.ofReal (2 * π) := by
          refine add_le_add h3 (mul_le_mul_right ?_ _)
          rw [hEvol]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Finiteness of star values over the window.
  have hfin : ∀ ξ ∈ Icc a b, ∀ θ : ℝ, starProfile (2 * π) (g ξ) θ ≠ ⊤ := by
    intro ξ hξ θ
    have hle : starProfile (2 * π) (g ξ) θ
        ≤ ENNReal.ofReal M * volume (Icc (2 * π / 2 - θ) (2 * π / 2 + θ)) := by
      calc starProfile (2 * π) (g ξ) θ
          = ∫⁻ x in Icc (2 * π / 2 - θ) (2 * π / 2 + θ),
              decreasingRearrangeSymm (2 * π) (g ξ) x := rfl
        _ ≤ ∫⁻ _ in Icc (2 * π / 2 - θ) (2 * π / 2 + θ), ENNReal.ofReal M :=
            lintegral_mono fun x => hrearr ξ hξ x
        _ = _ := setLIntegral_const _ _
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hle
  -- ε–δ assembly.
  rw [Metric.continuousWithinAt_iff]
  intro ε' hε'
  have hεpos : 0 < ε' / (2 * (2 * π + 1)) := div_pos hε' (by positivity)
  have hδ₂pos : 0 < ε' / (2 * (2 * M + 1)) := div_pos hε' (by linarith)
  have hUC := hQcomp.uniformContinuousOn_of_continuous hVcont
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hUC (ε' / (2 * (2 * π + 1))) hεpos
  refine ⟨min (min δ₁ (ε' / (2 * (2 * M + 1)))) (min (w₀.re - a) (b - w₀.re)),
    lt_min (lt_min hδ₁pos hδ₂pos) (lt_min (by linarith) (by linarith)), ?_⟩
  intro w hws hwd
  obtain ⟨-, hwim⟩ := hws
  have hre : |w.re - w₀.re| ≤ dist w w₀ := by
    rw [Complex.dist_eq, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have him : |w.im - w₀.im| ≤ dist w w₀ := by
    rw [Complex.dist_eq, ← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  have hd₁ : dist w w₀ < δ₁ :=
    lt_of_lt_of_le hwd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd₂ : dist w w₀ < ε' / (2 * (2 * M + 1)) :=
    lt_of_lt_of_le hwd (le_trans (min_le_left _ _) (min_le_right _ _))
  have hd₃ : dist w w₀ < w₀.re - a :=
    lt_of_lt_of_le hwd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd₄ : dist w w₀ < b - w₀.re :=
    lt_of_lt_of_le hwd (le_trans (min_le_right _ _) (min_le_right _ _))
  have hwab : w.re ∈ Icc a b := by
    have h5 := abs_lt.mp (lt_of_le_of_lt hre hd₃)
    have h6 := abs_lt.mp (lt_of_le_of_lt hre hd₄)
    exact ⟨by linarith [h5.1], by linarith [h6.2]⟩
  -- The circle samples at radii `exp (Re w)` and `exp (Re w₀)` are uniformly close.
  have hVclose : ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      |u (p + (Real.exp w.re : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I))
        - u (p + (Real.exp w₀.re : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I))|
        < ε' / (2 * (2 * π + 1)) := by
    intro φ hφ
    have hdp : dist ((w.re, φ) : ℝ × ℝ) ((w₀.re, φ) : ℝ × ℝ) < δ₁ := by
      refine lt_of_le_of_lt (le_trans ?_ hre) hd₁
      rw [Prod.dist_eq]
      apply max_le
      · exact le_of_eq (Real.dist_eq _ _)
      · exact le_trans (le_of_eq (dist_self φ)) (abs_nonneg _)
    have hd := hδ₁ (w.re, φ) (Set.mk_mem_prod hwab hφ) (w₀.re, φ)
      (Set.mk_mem_prod hw₀ab hφ) hdp
    rwa [Real.dist_eq] at hd
  have hcomp1 : ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      g w.re φ ≤ g w₀.re φ + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) := by
    intro φ hφ
    have habs := abs_lt.mp (hVclose φ hφ)
    rw [hgV w.re φ, hgV w₀.re φ]
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith [habs.2])) ENNReal.ofReal_add_le
  have hcomp2 : ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      g w₀.re φ ≤ g w.re φ + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) := by
    intro φ hφ
    have habs := abs_lt.mp (hVclose φ hφ)
    rw [hgV w.re φ, hgV w₀.re φ]
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith [habs.1])) ENNReal.ofReal_add_le
  -- Two-sided ENNReal estimate between the two star values.
  have hchain1 : starProfile (2 * π) (g w.re) w.im
      ≤ starProfile (2 * π) (g w₀.re) w₀.im
        + (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)) := by
    calc starProfile (2 * π) (g w.re) w.im
        ≤ starProfile (2 * π) (g w₀.re) w.im
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          hxi w.re w₀.re w.im hwim.1.le hwim.2.le _ hcomp1
      _ ≤ (starProfile (2 * π) (g w₀.re) w₀.im + ENNReal.ofReal (2 * M * |w.im - w₀.im|))
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          add_le_add_left (htheta w₀.re hw₀ab w₀.im w.im hw₀im.1.le hwim.1.le) _
      _ = _ := add_assoc _ _ _
  have hchain2 : starProfile (2 * π) (g w₀.re) w₀.im
      ≤ starProfile (2 * π) (g w.re) w.im
        + (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)) := by
    calc starProfile (2 * π) (g w₀.re) w₀.im
        ≤ starProfile (2 * π) (g w.re) w₀.im
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          hxi w₀.re w.re w₀.im hw₀im.1.le hw₀im.2.le _ hcomp2
      _ ≤ (starProfile (2 * π) (g w.re) w.im + ENNReal.ofReal (2 * M * |w₀.im - w.im|))
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          add_le_add_left (htheta w.re hwab w.im w₀.im hwim.1.le hw₀im.1.le) _
      _ = _ := by rw [abs_sub_comm w₀.im w.im, add_assoc]
  -- Transfer to real values.
  have hCne : (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
      + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hCtR : (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
      + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)).toReal
      = 2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π) := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by linarith) (abs_nonneg _)),
      ENNReal.toReal_ofReal hεpos.le, ENNReal.toReal_ofReal (by positivity)]
  have ht1 : (starProfile (2 * π) (g w.re) w.im).toReal
      ≤ (starProfile (2 * π) (g w₀.re) w₀.im).toReal
        + (2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π)) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfin w₀.re hw₀ab w₀.im, hCne⟩) hchain1
    rwa [ENNReal.toReal_add (hfin w₀.re hw₀ab w₀.im) hCne, hCtR] at hmono
  have ht2 : (starProfile (2 * π) (g w₀.re) w₀.im).toReal
      ≤ (starProfile (2 * π) (g w.re) w.im).toReal
        + (2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π)) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfin w.re hwab w.im, hCne⟩) hchain2
    rwa [ENNReal.toReal_add (hfin w.re hwab w.im) hCne, hCtR] at hmono
  -- The explicit bound is below `ε'`.
  have hnum : 2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π) < ε' := by
    have h1 : |w.im - w₀.im| < ε' / (2 * (2 * M + 1)) := lt_of_le_of_lt him hd₂
    have h2 : 2 * M * |w.im - w₀.im| ≤ 2 * M * (ε' / (2 * (2 * M + 1))) :=
      mul_le_mul_of_nonneg_left h1.le (by linarith)
    have h3 : 2 * M * (ε' / (2 * (2 * M + 1))) ≤ ε' / 2 := by
      have hstep : 2 * M * (ε' / (2 * (2 * M + 1)))
          ≤ (2 * M + 1) * (ε' / (2 * (2 * M + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) hδ₂pos.le
      have heq : (2 * M + 1) * (ε' / (2 * (2 * M + 1))) = ε' / 2 := by
        rw [← mul_div_assoc, div_eq_div_iff
          (ne_of_gt (by linarith : (0 : ℝ) < 2 * (2 * M + 1))) (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      linarith
    have h4 : ε' / (2 * (2 * π + 1)) * (2 * π) < ε' / 2 := by
      have hstep : ε' / (2 * (2 * π + 1)) * (2 * π)
          < ε' / (2 * (2 * π + 1)) * (2 * π + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hεpos
      have heq : ε' / (2 * (2 * π + 1)) * (2 * π + 1) = ε' / 2 := by
        rw [div_mul_eq_mul_div, div_eq_div_iff
          (by positivity : (2 * (2 * π + 1) : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      linarith
    linarith
  rw [hSP w, hSP w₀, Real.dist_eq, abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Small-radius sub-mean-value inequality for the star function.** At each point of the strip
the sub-mean-value inequality holds for all sufficiently small circles; the threshold reflects the
level structure of the extremal set at the centre (Baernstein's translate bound applies below the
minimal component length/gap of the extremal level set). The inputs are: continuity of `u` on the
annulus, a structured extremal attaining set for the star value at the centre (`hattain`), and
subharmonicity of every fixed-arc integral of `u` on the log-polar band (`hsub`); for `u` harmonic
these are supplied by `exists_attaining_structured` and `arcIntegral_harmonicOn`. -/
theorem starPlane_subMeanValue_small {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {w₀ : ℂ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hucont : ContinuousOn u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u)
    (hattain : ∃ (τ δ : ℝ) (F : Set ℝ), 0 < δ ∧ MeasurableSet F ∧
      F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
      volume F = ENNReal.ofReal (2 * w₀.im) ∧
      (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
      (∫⁻ ψ in F, ENNReal.ofReal
          ((angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w₀.re) ψ).toReal))
        = starFunction p u (Real.exp w₀.re) w₀.im)
    (hsub : ∀ E : Set ℝ, MeasurableSet E → Bornology.IsBounded E →
      SubharmonicOn (arcIntegral p u E) {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO})
    (hw₀ : w₀ ∈ logPolarStrip rI rO) :
    ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → Metric.closedBall w₀ ρ ⊆ logPolarStrip rI rO →
      starPlane p u w₀ ≤ Real.circleAverage (starPlane p u) w₀ ρ := by
  classical
  obtain ⟨hw₀re, hw₀im⟩ := hw₀
  -- Structured extremal attaining set at the centre: window slack `δ`, leftmost full interval.
  obtain ⟨τ, δ, F, hδ, hFmeas, hFwin, hFvol, ⟨x₀, hx₀least, hx₀Icc⟩, hFint⟩ := hattain
  have hδπ : δ ≤ π := by
    have h := hFwin hx₀least.1
    linarith [h.1, h.2]
  -- The structural threshold: any radius below `δ/2` keeps the translate bound valid.
  refine ⟨δ / 2, by positivity, fun ρ hρ hρδ hball => ?_⟩
  have harcnn : ∀ (E : Set ℝ) (w : ℂ), 0 ≤ arcIntegral p u E w := by
    intro E w
    rw [arcIntegral]
    exact integral_nonneg (fun φ => hu0 _)
  -- The de-rotated extremal arc-parameter set.
  set E₀ : Set ℝ := (fun ψ' : ℝ => ψ' + (-(w₀.im + π))) '' F with hE₀def
  have hE₀meas : MeasurableSet E₀ :=
    (measurableEmbedding_addRight (-(w₀.im + π))).measurableSet_image.2 hFmeas
  have hE₀bdd : Bornology.IsBounded E₀ := by
    refine (Metric.isBounded_Icc (τ + δ + (-(w₀.im + π)))
      (τ + 2 * π - δ + (-(w₀.im + π)))).subset ?_
    rw [hE₀def]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨by linarith [(hFwin hx).1], by linarith [(hFwin hx).2]⟩
  have hE₀vol : volume E₀ = ENNReal.ofReal (2 * w₀.im) := by
    rw [hE₀def, Set.image_add_right, measure_preimage_add_right, hFvol]
  have hEfinE₀ : volume E₀ ≠ ⊤ := by rw [hE₀vol]; exact ENNReal.ofReal_ne_top
  have himg₀ : (fun φ : ℝ => φ + (w₀.im + π)) '' E₀ = F := by
    rw [hE₀def, ← Set.image_comp]
    convert Set.image_id F using 1
    apply Set.image_congr'
    intro x
    simp only [Function.comp_apply, id_eq]
    ring
  -- A uniform bound for `u` on the compact log-radius shell spanned by the closed ball.
  have hmem₁ : w₀ - (ρ : ℂ) ∈ Metric.closedBall w₀ ρ := by
    have h : dist (w₀ - (ρ : ℂ)) w₀ = ρ := by
      rw [dist_eq_norm]
      have h2 : w₀ - (ρ : ℂ) - w₀ = -(ρ : ℂ) := by ring
      rw [h2, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact Metric.mem_closedBall.mpr (le_of_eq h)
  have hmem₂ : w₀ + (ρ : ℂ) ∈ Metric.closedBall w₀ ρ := by
    have h : dist (w₀ + (ρ : ℂ)) w₀ = ρ := by
      rw [dist_eq_norm]
      have h2 : w₀ + (ρ : ℂ) - w₀ = (ρ : ℂ) := by ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact Metric.mem_closedBall.mpr (le_of_eq h)
  obtain ⟨hs₁, -⟩ := hball hmem₁
  obtain ⟨hs₂, -⟩ := hball hmem₂
  have hlo : Real.log rI < w₀.re - ρ := by
    have h := hs₁.1
    rwa [Complex.sub_re, Complex.ofReal_re] at h
  have hhi : w₀.re + ρ < Real.log rO := by
    have h := hs₂.2
    rwa [Complex.add_re, Complex.ofReal_re] at h
  set K : Set ℂ :=
    {z : ℂ | Real.exp (w₀.re - ρ) ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ Real.exp (w₀.re + ρ)} with hKdef
  have hKsub : K ⊆ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
    rw [hKdef]
    rintro z ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
        _ < Real.exp (w₀.re - ρ) := Real.exp_lt_exp.mpr hlo
        _ ≤ ‖z - p‖ := h1
    · calc ‖z - p‖ ≤ Real.exp (w₀.re + ρ) := h2
        _ < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hhi
        _ = rO := Real.exp_log (hrI.trans hrO)
  have hKclosed : IsClosed K := by
    rw [hKdef]
    have h1 : IsClosed {z : ℂ | Real.exp (w₀.re - ρ) ≤ ‖z - p‖} :=
      isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {z : ℂ | ‖z - p‖ ≤ Real.exp (w₀.re + ρ)} :=
      isClosed_le (by fun_prop) continuous_const
    simpa [Set.setOf_and] using h1.inter h2
  have hKcompact : IsCompact K := by
    refine (isCompact_closedBall p (Real.exp (w₀.re + ρ))).of_isClosed_subset hKclosed ?_
    rw [hKdef]
    rintro z ⟨-, h2⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact h2
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn (hucont.mono hKsub)
  have hKmem : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ z : ℂ, ‖z - p‖ = Real.exp w.re → z ∈ K := by
    intro w hw z hz
    have hre : |w.re - w₀.re| ≤ ρ := by
      have h1 : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h1
      calc |w.re - w₀.re| ≤ ‖w - w₀‖ := h1
        _ = dist w w₀ := (dist_eq_norm w w₀).symm
        _ ≤ ρ := Metric.mem_closedBall.mp hw
    rw [abs_le] at hre
    rw [hKdef]
    exact ⟨by rw [hz]; exact Real.exp_le_exp.mpr (by linarith [hre.1]),
      by rw [hz]; exact Real.exp_le_exp.mpr (by linarith [hre.2])⟩
  have hMbd : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ φ : ℝ,
      u (p + Complex.exp (w + φ * Complex.I)) ≤ M := by
    intro w hw φ
    have hz := hKmem w hw _ (norm_arcPoint_sub p w φ)
    have h := hM _ hz
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h
  have hMcirc : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ φ : ℝ,
      u (p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M := by
    intro w hw φ
    have hnorm : ‖p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I) - p‖
        = Real.exp w.re := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have him : ((φ : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
      rw [him, Real.exp_zero, mul_one, abs_of_pos (Real.exp_pos _)]
    have hz := hKmem w hw _ hnorm
    have h := hM _ hz
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h
  -- The rotated-frame profile at log-radius `ξ`, and the arc-integral/profile-integral chain.
  set gr : ℝ → ℝ → ℝ≥0∞ := fun ξ φ' => ENNReal.ofReal
    ((angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp ξ) φ').toReal) with hgrdef
  have hintg : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ E : Set ℝ, volume E ≠ ⊤ →
      Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
        ((volume : Measure ℝ).restrict E) := by
    intro w hw E hEfin
    haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict E) := isFiniteMeasure_restrict.2 hEfin
    have hfibmeas : Measurable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I))) := by
      apply hum.comp
      fun_prop
    refine Integrable.of_bound hfibmeas.aestronglyMeasurable M ?_
    filter_upwards with φ
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 _)]
    exact hMbd w hw φ
  have hchain : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ E : Set ℝ, MeasurableSet E → volume E ≠ ⊤ →
      ENNReal.ofReal (arcIntegral p u E w)
        = ∫⁻ ψ' in (fun φ : ℝ => φ + (w.im + π)) '' E, gr w.re ψ' := by
    intro w hw E hEmeas hEfin
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal (hintg w hw E hEfin)
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w + φ * Complex.I)))
        = gr w.re (φ + (w.im + π)) := by
      intro φ
      simp only [hgrdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w + (φ : ℂ) * Complex.I
          = (w.re : ℂ) + ((φ + w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring_nf
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hmp : MeasurePreserving (fun φ : ℝ => φ + (w.im + π)) volume volume :=
      measurePreserving_add_right volume (w.im + π)
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w.im + π))
      (gr w.re) ((fun φ : ℝ => φ + (w.im + π)) '' E)
    rw [Set.preimage_image_eq _ (add_left_injective (w.im + π))] at hkey
    rw [hkey]
  -- Extremality at the centre: the de-rotated attaining set reproduces the star value.
  have hw₀ball : w₀ ∈ Metric.closedBall w₀ ρ := Metric.mem_closedBall_self hρ.le
  have hext : arcIntegral p u E₀ w₀ = starPlane p u w₀ := by
    have heq : ENNReal.ofReal (arcIntegral p u E₀ w₀)
        = starFunction p u (Real.exp w₀.re) w₀.im := by
      rw [hchain w₀ hw₀ball E₀ hE₀meas hEfinE₀, himg₀]
      simp only [hgrdef]
      exact hFint
    have harc0 : (0 : ℝ) ≤ arcIntegral p u E₀ w₀ := harcnn E₀ w₀
    rw [starPlane, ← heq, ENNReal.toReal_ofReal harc0]
  -- Coordinates of the circle points.
  have hcoord : ∀ x : ℝ, (circleMap w₀ ρ x).re = w₀.re + ρ * Real.cos x
      ∧ (circleMap w₀ ρ x).im = w₀.im + ρ * Real.sin x := by
    intro x
    constructor
    · simp [circleMap, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    · simp [circleMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  -- Sjögren's paired surgery: the two opposite circle points share their radius, and the
  -- translated extremal sets are cut and re-glued into competitors of the two target apertures.
  have hpair : ∀ ψ : ℝ, 0 ≤ Real.sin ψ →
      arcIntegral p u E₀ (circleMap w₀ ρ ψ) + arcIntegral p u E₀ (circleMap w₀ ρ (-ψ))
        ≤ starPlane p u (circleMap w₀ ρ ψ) + starPlane p u (circleMap w₀ ρ (-ψ)) := by
    intro ψ hsin
    set α : ℝ := ρ * Real.sin ψ with hαdef
    have hα0 : 0 ≤ α := mul_nonneg hρ.le hsin
    have hαρ : α ≤ ρ := by
      rw [hαdef]
      calc ρ * Real.sin ψ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one ψ) hρ.le
        _ = ρ := mul_one ρ
    have h2αδ : 2 * α ≤ δ := by linarith
    set wp : ℂ := circleMap w₀ ρ ψ with hwpdef
    set wm : ℂ := circleMap w₀ ρ (-ψ) with hwmdef
    have hwpball : wp ∈ Metric.closedBall w₀ ρ := circleMap_mem_closedBall w₀ hρ.le ψ
    have hwmball : wm ∈ Metric.closedBall w₀ ρ := circleMap_mem_closedBall w₀ hρ.le (-ψ)
    obtain ⟨-, hwpim⟩ := hball hwpball
    obtain ⟨-, hwmim⟩ := hball hwmball
    have hpre : wp.re = w₀.re + ρ * Real.cos ψ := (hcoord ψ).1
    have hpim : wp.im = w₀.im + α := by rw [hαdef]; exact (hcoord ψ).2
    have hmre : wm.re = w₀.re + ρ * Real.cos ψ := by
      have h := (hcoord (-ψ)).1
      rwa [Real.cos_neg] at h
    have hmim : wm.im = w₀.im - α := by
      have h := (hcoord (-ψ)).2
      rw [Real.sin_neg, mul_neg] at h
      rw [h, hαdef]; ring
    have hrere : wm.re = wp.re := by rw [hmre, hpre]
    have hwp0 : (0 : ℝ) ≤ wp.im := hwpim.1.le
    have hwpπ : wp.im ≤ π := hwpim.2.le
    have hwm0 : (0 : ℝ) ≤ wm.im := hwmim.1.le
    have hwmπ : wm.im ≤ π := hwmim.2.le
    have hαlt : α < w₀.im := by
      have h := hwmim.1
      rw [hmim] at h
      linarith
    -- The two translates of the attaining set.
    set Ep : Set ℝ := (fun x : ℝ => x + α) '' F with hEpdef
    set Em : Set ℝ := (fun x : ℝ => x - α) '' F with hEmdef
    have hEmeq : Em = (fun x : ℝ => x + (-α)) '' F := by
      rw [hEmdef]
      apply Set.image_congr'
      intro x
      ring
    have hEpmeas : MeasurableSet Ep := by
      rw [hEpdef]; exact (measurableEmbedding_addRight α).measurableSet_image.2 hFmeas
    have hEmmeas : MeasurableSet Em := by
      rw [hEmeq]; exact (measurableEmbedding_addRight (-α)).measurableSet_image.2 hFmeas
    have hvol_img : ∀ c : ℝ, volume ((fun x : ℝ => x + c) '' F) = volume F := by
      intro c; rw [Set.image_add_right, measure_preimage_add_right]
    have hEpvol : volume Ep = ENNReal.ofReal (2 * w₀.im) := by
      rw [hEpdef, hvol_img, hFvol]
    have hEmvol : volume Em = ENNReal.ofReal (2 * w₀.im) := by
      rw [hEmeq, hvol_img, hFvol]
    have hEpsub : Ep ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) := by
      rw [hEpdef]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by linarith [(hFwin hx).1], by linarith [(hFwin hx).2]⟩
    have hEmsub : Em ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) := by
      rw [hEmdef]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by linarith [(hFwin hx).1], by linarith [(hFwin hx).2]⟩
    have hUsub : Ep ∪ Em ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) :=
      Set.union_subset hEpsub hEmsub
    -- Baernstein's translate bound at the leftmost full interval of `F`.
    have hIvol : volume (Ep ∩ Em) ≤ ENNReal.ofReal (2 * w₀.im - 2 * α) := by
      have h := volume_translate_inter_le hx₀least hx₀Icc h2αδ
      rw [← hEpdef, ← hEmdef, hFvol,
        ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 2 * α)] at h
      exact h
    have hIfin : volume (Ep ∩ Em) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIvol
    obtain ⟨t, htnn, hteq⟩ : ∃ t : ℝ, 0 ≤ t ∧ volume (Ep ∩ Em) = ENNReal.ofReal t :=
      ⟨(volume (Ep ∩ Em)).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hIfin).symm⟩
    have htle : t ≤ 2 * w₀.im - 2 * α := by
      rw [hteq] at hIvol
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hIvol
    have hUfin : volume (Ep ∪ Em) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_union_le Ep Em)
      rw [hEpvol, hEmvol]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    obtain ⟨ut, hutnn, huteq⟩ : ∃ s : ℝ, 0 ≤ s ∧ volume (Ep ∪ Em) = ENNReal.ofReal s :=
      ⟨(volume (Ep ∪ Em)).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hUfin).symm⟩
    have h2θnn : (0 : ℝ) ≤ 2 * w₀.im := by linarith [hw₀im.1]
    have hut4 : ut = 4 * w₀.im - t := by
      have h := measure_union_add_inter (μ := volume) Ep hEmmeas
      rw [hEpvol, hEmvol, hteq, huteq, ← ENNReal.ofReal_add hutnn htnn,
        ← ENNReal.ofReal_add h2θnn h2θnn] at h
      have h' := (ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)).mp h
      linarith
    -- Transfer a measurable piece of prescribed measure from the union to the intersection.
    have hUImeas : MeasurableSet ((Ep ∪ Em) \ (Ep ∩ Em)) :=
      (hEpmeas.union hEmmeas).diff (hEpmeas.inter hEmmeas)
    have hab : τ + δ - α ≤ τ + 2 * π - δ + α := by linarith
    have hm0 : (0 : ℝ) ≤ 2 * w₀.im - 2 * α - t := by linarith
    have hDvol : volume ((Ep ∪ Em) \ (Ep ∩ Em)) = ENNReal.ofReal (ut - t) := by
      rw [measure_diff (Set.inter_subset_left.trans Set.subset_union_left)
        (hEpmeas.inter hEmmeas).nullMeasurableSet hIfin, hteq, huteq,
        ← ENNReal.ofReal_sub _ htnn]
    have hmD : ENNReal.ofReal (2 * w₀.im - 2 * α - t)
        ≤ volume ((Ep ∪ Em) \ (Ep ∩ Em)) := by
      rw [hDvol]
      apply ENNReal.ofReal_le_ofReal
      rw [hut4]
      linarith
    obtain ⟨C, hCsub, hCmeas, hCvol⟩ := exists_measurableSet_subset_volume hab
      ((Ep ∪ Em) \ (Ep ∩ Em)) hUImeas (fun x hx => hUsub hx.1) hm0 hmD
    have hCdisjI : Disjoint (Ep ∩ Em) C :=
      Set.disjoint_of_subset_right hCsub Set.disjoint_sdiff_right
    have hCU : C ⊆ Ep ∪ Em := hCsub.trans Set.diff_subset
    have hCfin : volume C ≠ ⊤ := by rw [hCvol]; exact ENNReal.ofReal_ne_top
    -- The re-glued competitors of the two target apertures.
    have hAvol : volume ((Ep ∩ Em) ∪ C) = ENNReal.ofReal (2 * wm.im) := by
      rw [measure_union hCdisjI hCmeas, hteq, hCvol, ← ENNReal.ofReal_add htnn hm0]
      congr 1
      rw [hmim]
      ring
    have hBvol : volume ((Ep ∪ Em) \ C) = ENNReal.ofReal (2 * wp.im) := by
      rw [measure_diff hCU hCmeas.nullMeasurableSet hCfin, huteq, hCvol,
        ← ENNReal.ofReal_sub _ hm0]
      congr 1
      rw [hut4, hpim]
      ring
    have hIccA : (Ep ∩ Em) ∪ C ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) := by
      refine Set.union_subset (fun x hx => hUsub (Set.subset_union_left hx.1)) ?_
      exact fun x hx => hUsub (hCU hx)
    -- The lintegral surgery: cut-and-glue preserves the total profile mass.
    have hsplitEm : Em = (Ep ∩ Em) ∪ (Em \ Ep) := by
      rw [Set.inter_comm Ep Em]
      exact (Set.inter_union_diff Em Ep).symm
    have hsplitU : Ep ∪ Em = Ep ∪ (Em \ Ep) := Set.union_diff_self.symm
    have hUCsplit : Ep ∪ Em = C ∪ ((Ep ∪ Em) \ C) := (Set.union_diff_cancel hCU).symm
    have hEmPmeas : MeasurableSet (Em \ Ep) := hEmmeas.diff hEpmeas
    have hdisj1 : Disjoint (Ep ∩ Em) (Em \ Ep) :=
      Set.disjoint_of_subset_left Set.inter_subset_left Set.disjoint_sdiff_right
    have hdisj2 : Disjoint Ep (Em \ Ep) := Set.disjoint_sdiff_right
    have hEmint : (∫⁻ x in Em, gr wp.re x)
        = (∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x := by
      conv_lhs => rw [hsplitEm]
      exact lintegral_union hEmPmeas hdisj1
    have hUint : (∫⁻ x in Ep ∪ Em, gr wp.re x)
        = (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x := by
      conv_lhs => rw [hsplitU]
      exact lintegral_union hEmPmeas hdisj2
    have hAint : (∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x)
        = (∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in C, gr wp.re x :=
      lintegral_union hCmeas hCdisjI
    have hUCint : (∫⁻ x in Ep ∪ Em, gr wp.re x)
        = (∫⁻ x in C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
      conv_lhs => rw [hUCsplit]
      exact lintegral_union ((hEpmeas.union hEmmeas).diff hCmeas) Set.disjoint_sdiff_right
    have hsurg : (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em, gr wp.re x
        = (∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
      have hkeyU : (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x
          = (∫⁻ x in C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
        rw [← hUint, hUCint]
      rw [hEmint, hAint]
      calc (∫⁻ x in Ep, gr wp.re x)
          + ((∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x)
          = (∫⁻ x in Ep ∩ Em, gr wp.re x)
            + ((∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x) := by ring
        _ = (∫⁻ x in Ep ∩ Em, gr wp.re x)
            + ((∫⁻ x in C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x) := by rw [hkeyU]
        _ = ((∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in C, gr wp.re x)
            + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by ring
    -- The rotated frames of the arc integrals at the two circle points.
    have himgp : (fun φ : ℝ => φ + (wp.im + π)) '' E₀ = Ep := by
      rw [hE₀def, Set.image_image, hEpdef]
      apply Set.image_congr'
      intro x
      rw [hpim]
      ring
    have himgm : (fun φ : ℝ => φ + (wm.im + π)) '' E₀ = Em := by
      rw [hE₀def, Set.image_image, hEmdef]
      apply Set.image_congr'
      intro x
      rw [hmim]
      ring
    have hch_p : ENNReal.ofReal (arcIntegral p u E₀ wp) = ∫⁻ x in Ep, gr wp.re x := by
      rw [hchain wp hwpball E₀ hE₀meas hEfinE₀, himgp]
    have hch_m : ENNReal.ofReal (arcIntegral p u E₀ wm) = ∫⁻ x in Em, gr wp.re x := by
      rw [hchain wm hwmball E₀ hE₀meas hEfinE₀, himgm, hrere]
    -- De-rotate the competitors and dominate through the windowed star-function bound.
    set EA : Set ℝ := (fun x : ℝ => x + (-(wm.im + π))) '' ((Ep ∩ Em) ∪ C) with hEAdef
    set EB : Set ℝ := (fun x : ℝ => x + (-(wp.im + π))) '' ((Ep ∪ Em) \ C) with hEBdef
    have hEAmeas : MeasurableSet EA := by
      rw [hEAdef]
      exact (measurableEmbedding_addRight _).measurableSet_image.2
        ((hEpmeas.inter hEmmeas).union hCmeas)
    have hEBmeas : MeasurableSet EB := by
      rw [hEBdef]
      exact (measurableEmbedding_addRight _).measurableSet_image.2
        ((hEpmeas.union hEmmeas).diff hCmeas)
    have hEAvol : volume EA = ENNReal.ofReal (2 * wm.im) := by
      rw [hEAdef, Set.image_add_right, measure_preimage_add_right, hAvol]
    have hEBvol : volume EB = ENNReal.ofReal (2 * wp.im) := by
      rw [hEBdef, Set.image_add_right, measure_preimage_add_right, hBvol]
    have hEAfin : volume EA ≠ ⊤ := by rw [hEAvol]; exact ENNReal.ofReal_ne_top
    have hEBfin : volume EB ≠ ⊤ := by rw [hEBvol]; exact ENNReal.ofReal_ne_top
    have himgA : (fun φ : ℝ => φ + (wm.im + π)) '' EA = (Ep ∩ Em) ∪ C := by
      rw [hEAdef, ← Set.image_comp]
      convert Set.image_id _ using 1
      apply Set.image_congr'
      intro x
      simp only [Function.comp_apply, id_eq]
      ring
    have himgB : (fun φ : ℝ => φ + (wp.im + π)) '' EB = (Ep ∪ Em) \ C := by
      rw [hEBdef, ← Set.image_comp]
      convert Set.image_id _ using 1
      apply Set.image_congr'
      intro x
      simp only [Function.comp_apply, id_eq]
      ring
    have hdomA : ENNReal.ofReal (arcIntegral p u EA wm)
        ≤ starFunction p u (Real.exp wm.re) wm.im := by
      refine arcIntegral_le_starFunction_window (τ + δ - α) hu0 hum
        (hintg wm hwmball EA hEAfin) hEAmeas hwm0 hwmπ ?_ (le_of_eq hEAvol)
      rw [himgA]
      intro x hx
      have h := hIccA hx
      exact ⟨h.1, by linarith [h.2]⟩
    have hdomB : ENNReal.ofReal (arcIntegral p u EB wp)
        ≤ starFunction p u (Real.exp wp.re) wp.im := by
      refine arcIntegral_le_starFunction_window (τ + δ - α) hu0 hum
        (hintg wp hwpball EB hEBfin) hEBmeas hwp0 hwpπ ?_ (le_of_eq hEBvol)
      rw [himgB]
      intro x hx
      have h := hUsub hx.1
      exact ⟨h.1, by linarith [h.2]⟩
    have hchA : ENNReal.ofReal (arcIntegral p u EA wm)
        = ∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x := by
      rw [hchain wm hwmball EA hEAmeas hEAfin, himgA, hrere]
    have hchB : ENNReal.ofReal (arcIntegral p u EB wp)
        = ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
      rw [hchain wp hwpball EB hEBmeas hEBfin, himgB]
    -- Assemble the paired inequality in `ℝ≥0∞` and descend to the reals.
    have hsfinp : starFunction p u (Real.exp wp.re) wp.im < ⊤ :=
      starFunction_lt_top hwp0 hwpπ ⟨M, fun φ => hMcirc wp hwpball φ⟩
    have hsfinm : starFunction p u (Real.exp wm.re) wm.im < ⊤ :=
      starFunction_lt_top hwm0 hwmπ ⟨M, fun φ => hMcirc wm hwmball φ⟩
    have hmain : ENNReal.ofReal (arcIntegral p u E₀ wp) + ENNReal.ofReal (arcIntegral p u E₀ wm)
        ≤ starFunction p u (Real.exp wp.re) wp.im
          + starFunction p u (Real.exp wm.re) wm.im := by
      calc ENNReal.ofReal (arcIntegral p u E₀ wp) + ENNReal.ofReal (arcIntegral p u E₀ wm)
          = (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em, gr wp.re x := by rw [hch_p, hch_m]
        _ = (∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x)
            + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := hsurg
        _ = ENNReal.ofReal (arcIntegral p u EA wm)
            + ENNReal.ofReal (arcIntegral p u EB wp) := by rw [hchA, hchB]
        _ ≤ starFunction p u (Real.exp wm.re) wm.im
            + starFunction p u (Real.exp wp.re) wp.im := add_le_add hdomA hdomB
        _ = starFunction p u (Real.exp wp.re) wp.im
            + starFunction p u (Real.exp wm.re) wm.im := add_comm _ _
    have hofsum : ENNReal.ofReal (arcIntegral p u E₀ wp + arcIntegral p u E₀ wm)
        = ENNReal.ofReal (arcIntegral p u E₀ wp) + ENNReal.ofReal (arcIntegral p u E₀ wm) :=
      ENNReal.ofReal_add (harcnn _ _) (harcnn _ _)
    have hsum_fin : starFunction p u (Real.exp wp.re) wp.im
        + starFunction p u (Real.exp wm.re) wm.im ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hsfinp.ne, hsfinm.ne⟩
    have hmain' : ENNReal.ofReal (arcIntegral p u E₀ wp + arcIntegral p u E₀ wm)
        ≤ starFunction p u (Real.exp wp.re) wp.im
          + starFunction p u (Real.exp wm.re) wm.im := by
      rw [hofsum]
      exact hmain
    have hfinal := ENNReal.toReal_mono hsum_fin hmain'
    rw [ENNReal.toReal_ofReal (add_nonneg (harcnn _ _) (harcnn _ _)),
      ENNReal.toReal_add hsfinp.ne hsfinm.ne] at hfinal
    simp only [starPlane]
    exact hfinal
  -- Fold the pairing over the whole circle: the reflected pairs cover every angle.
  have key : ∀ ψ : ℝ,
      arcIntegral p u E₀ (circleMap w₀ ρ ψ) + arcIntegral p u E₀ (circleMap w₀ ρ (-ψ))
        ≤ starPlane p u (circleMap w₀ ρ ψ) + starPlane p u (circleMap w₀ ρ (-ψ)) := by
    intro ψ
    rcases le_or_gt 0 (Real.sin ψ) with h | h
    · exact hpair ψ h
    · have h' := hpair (-ψ) (by rw [Real.sin_neg]; linarith)
      rw [neg_neg] at h'
      linarith
  -- Continuity of the two circle profiles.
  have hHsub : SubharmonicOn (arcIntegral p u E₀)
      {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := hsub E₀ hE₀meas hE₀bdd
  have hmapS : ∀ x : ℝ,
      circleMap w₀ ρ x ∈ {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := by
    intro x
    obtain ⟨h1, -⟩ := hball (circleMap_mem_closedBall w₀ hρ.le x)
    exact ⟨h1.1, h1.2⟩
  have hmapStrip : ∀ x : ℝ, circleMap w₀ ρ x ∈ logPolarStrip rI rO :=
    fun x => hball (circleMap_mem_closedBall w₀ hρ.le x)
  have hΦcont : Continuous (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ x)) :=
    hHsub.1.comp_continuous (continuous_circleMap w₀ ρ) hmapS
  have hΨcont : Continuous (fun x : ℝ => starPlane p u (circleMap w₀ ρ x)) :=
    (starPlane_continuousOn hrI hrO hucont hu0 hum).comp_continuous
      (continuous_circleMap w₀ ρ) hmapStrip
  have hΦint : IntervalIntegrable (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ x))
      volume 0 (2 * π) := hΦcont.intervalIntegrable 0 (2 * π)
  have hΦnint : IntervalIntegrable (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ (-x)))
      volume 0 (2 * π) := (hΦcont.comp continuous_neg).intervalIntegrable 0 (2 * π)
  have hΨint : IntervalIntegrable (fun x : ℝ => starPlane p u (circleMap w₀ ρ x))
      volume 0 (2 * π) := hΨcont.intervalIntegrable 0 (2 * π)
  have hΨnint : IntervalIntegrable (fun x : ℝ => starPlane p u (circleMap w₀ ρ (-x)))
      volume 0 (2 * π) := (hΨcont.comp continuous_neg).intervalIntegrable 0 (2 * π)
  -- Reflection invariance of the two circle integrals.
  have hΦper : Function.Periodic (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ x)) (2 * π) :=
    fun x => congrArg (arcIntegral p u E₀) (periodic_circleMap w₀ ρ x)
  have hΨper : Function.Periodic (fun x : ℝ => starPlane p u (circleMap w₀ ρ x)) (2 * π) :=
    fun x => congrArg (starPlane p u) (periodic_circleMap w₀ ρ x)
  have hreflΦ : (∫ x in (0 : ℝ)..(2 * π), arcIntegral p u E₀ (circleMap w₀ ρ (-x)))
      = ∫ x in (0 : ℝ)..(2 * π), arcIntegral p u E₀ (circleMap w₀ ρ x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => arcIntegral p u E₀ (circleMap w₀ ρ x)),
      neg_zero]
    have h := hΦper.intervalIntegral_add_eq (-(2 * π)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  have hreflΨ : (∫ x in (0 : ℝ)..(2 * π), starPlane p u (circleMap w₀ ρ (-x)))
      = ∫ x in (0 : ℝ)..(2 * π), starPlane p u (circleMap w₀ ρ x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => starPlane p u (circleMap w₀ ρ x)),
      neg_zero]
    have h := hΨper.intervalIntegral_add_eq (-(2 * π)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  -- Integrate the pointwise pairing over one period.
  have hintsum : (∫ x in (0 : ℝ)..(2 * π),
      (arcIntegral p u E₀ (circleMap w₀ ρ x) + arcIntegral p u E₀ (circleMap w₀ ρ (-x))))
      ≤ ∫ x in (0 : ℝ)..(2 * π),
      (starPlane p u (circleMap w₀ ρ x) + starPlane p u (circleMap w₀ ρ (-x))) :=
    intervalIntegral.integral_mono_on (by positivity) (hΦint.add hΦnint) (hΨint.add hΨnint)
      (fun x _ => key x)
  rw [intervalIntegral.integral_add hΦint hΦnint, intervalIntegral.integral_add hΨint hΨnint,
    hreflΦ, hreflΨ] at hintsum
  have hint_le : (∫ x in (0 : ℝ)..(2 * π), arcIntegral p u E₀ (circleMap w₀ ρ x))
      ≤ ∫ x in (0 : ℝ)..(2 * π), starPlane p u (circleMap w₀ ρ x) := by linarith
  -- Sub-mean-value property of the subharmonic competitor, and conclusion.
  have hMVP : arcIntegral p u E₀ w₀ ≤ Real.circleAverage (arcIntegral p u E₀) w₀ ρ := by
    refine hHsub.2 w₀ ⟨hw₀re.1, hw₀re.2⟩ ρ hρ ?_
    intro w hw
    obtain ⟨h1, -⟩ := hball hw
    exact ⟨h1.1, h1.2⟩
  have hcavg : Real.circleAverage (arcIntegral p u E₀) w₀ ρ
      ≤ Real.circleAverage (starPlane p u) w₀ ρ := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hint_le (by positivity)
  calc starPlane p u w₀ = arcIntegral p u E₀ w₀ := hext.symm
    _ ≤ Real.circleAverage (arcIntegral p u E₀) w₀ ρ := hMVP
    _ ≤ Real.circleAverage (starPlane p u) w₀ ρ := hcavg

/-- **Baernstein's theorem: the star function of a nonnegative harmonic function is subharmonic**
in log-polar coordinates on the open strip. Packages the continuity and the sub-mean-value
inequality into the `SubharmonicOn` predicate. -/
theorem starPlane_subharmonicOn {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u) :
    SubharmonicOn (starPlane p u) (logPolarStrip rI rO) := by
  have hopen : IsOpen (logPolarStrip rI rO) := by
    have heq : logPolarStrip rI rO
        = Complex.re ⁻¹' Set.Ioo (Real.log rI) (Real.log rO)
          ∩ Complex.im ⁻¹' Set.Ioo (0 : ℝ) Real.pi := rfl
    rw [heq]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  refine subharmonicOn_of_locally hopen (starPlane_continuousOn hrI hrO hu.continuousOn hu0 hum)
    fun c hc => starPlane_subMeanValue_small hrI hrO hu.continuousOn hu0 hum ?_ ?_ hc
  · have hrmem : Real.exp c.re ∈ Set.Ioo rI rO := by
      constructor
      · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
          _ < Real.exp c.re := Real.exp_lt_exp.mpr hc.1.1
      · calc Real.exp c.re < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hc.1.2
          _ = rO := Real.exp_log (hrI.trans hrO)
    exact exists_attaining_structured hrI hu hu0 hum hrmem hc.2
  · exact fun E hE hEbdd =>
      HarmonicOnNhd.subharmonicOn (arcIntegral_harmonicOn hrI hrO hu hE hEbdd)

/-- **Sub-mean-value inequality for the star function** (Baernstein). For `u` harmonic and
nonnegative on the annulus `{rI < ‖z - p‖ < rO}`, the log-polar star function `starPlane p u`
satisfies the sub-mean-value inequality at every point of the open strip: its value at the centre
is at most its circle average over any circle whose closed disk lies in the strip. Specializes the
subharmonicity of the star surface (`starPlane_subharmonicOn`) to a single centre and radius. -/
theorem starPlane_subMeanValue {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {w₀ : ℂ} {ρ : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u)
    (hw₀ : w₀ ∈ logPolarStrip rI rO) (hρ : 0 < ρ)
    (hball : Metric.closedBall w₀ ρ ⊆ logPolarStrip rI rO) :
    starPlane p u w₀ ≤ Real.circleAverage (starPlane p u) w₀ ρ :=
  (starPlane_subharmonicOn hrI hrO hu hu0 hum).2 w₀ hw₀ ρ hρ hball

end RiemannDynamics
