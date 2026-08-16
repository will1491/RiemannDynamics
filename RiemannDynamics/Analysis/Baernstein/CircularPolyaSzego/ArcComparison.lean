/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Baernstein.CircularPolyaSzego.Basic

/-!
# Arc integrals are dominated by the star plane

Second part of the Baernstein star-function development begun in
`Analysis/Baernstein/CircularPolyaSzego/Basic.lean`. Here the star function is identified as the
*supremum of arc integrals*: the arc integral of `u` over a measurable set `E` of measure at most
`2 · Im w`, fitting after rotation inside one period, is at most the star value, and the bound is
attained.

The final result, `RiemannDynamics.exists_attaining_structured`, produces an attaining set together
with the structure needed downstream. It attains at the single point `(r, θ)`, not on a
neighbourhood; what it adds is geometry at that point — the set sits inside a `2π`-window with slack
`δ > 0` at each end, and its least element starts a full interval `[x₀, x₀ + δ]`. That slack is what
lets translates of the set be spliced into admissible competitors at *nearby* log-polar points,
which is what turns the pointwise supremum into a local sub-mean-value inequality in
`Analysis/Baernstein/CircularPolyaSzego/Subharmonicity.lean`.

## Main results

* `RiemannDynamics.exists_measurableSet_superset_volume` — a measurable superset of prescribed
  measure inside a bounded interval.
* `RiemannDynamics.arcIntegral_le_starFunction`, `RiemannDynamics.arcIntegral_le_starPlane` — for
  `u` nonnegative and measurable and `E` measurable of measure at most `2 · Im w`, whose rotate by
  `Im w + π` lies in `[0, 2π]`, the arc integral is at most the star value (extended-real and real
  forms).
* `RiemannDynamics.arcIntegral_eq_starPlane_extremal` — the bound is attained.
* `RiemannDynamics.volume_translate_inter_le` — a translation estimate for the measure of an
  intersection, used to control how the attaining arc moves.
* `RiemannDynamics.arcIntegral_le_starFunction_window` — the same comparison with the rotated set
  allowed to sit in an arbitrary window `[a, a + 2π]`.
* `RiemannDynamics.exists_attaining_structured` — for `u` harmonic and nonnegative, an attaining
  set of measure `2θ` inside a `2π`-window with slack `δ > 0`, whose least element starts a full
  interval.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

variable {T : ℝ} {g : ℝ → ℝ≥0∞}

/-!
## The upper-half fixed-arc domination

The sub-mean-value inequality for the log-polar star surface `starPlane p u` rests on the following
*domination* of the fixed-arc harmonic integral by the star function. The measure-extension lemma
below, together with `exists_measurableSet_subset_volume` in
`Analysis/Baernstein/CircularPolyaSzego/Basic.lean` (a 1-Lipschitz intermediate-value argument, the
same pattern used inside `starProfile_eq_iSup_setLIntegral`), turns a measurable subset of a bounded
interval into a subset of *prescribed* measure, or extends it to a *superset* of prescribed larger
measure inside the interval.
-/

/-- **Prescribed-measure superset inside a bounded interval.** For a measurable `A ⊆ Icc a b` and a
target `0 ≤ m` with `|A| ≤ ofReal m` and `m ≤ b − a`, there is a measurable superset `A ⊆ F ⊆ Icc a
b` of measure exactly `ofReal m`. Take `F = A ∪ B` where `B` is a prescribed-measure subset of the
complement `Icc a b \ A` (of the exact deficit `m − |A|`), produced by
`exists_measurableSet_subset_volume`. -/
theorem exists_measurableSet_superset_volume {a b : ℝ} (hab : a ≤ b) (A : Set ℝ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc a b) {m : ℝ} (hm0 : 0 ≤ m)
    (hmA : volume A ≤ ENNReal.ofReal m) (hmb : m ≤ b - a) :
    ∃ F, A ⊆ F ∧ F ⊆ Set.Icc a b ∧ MeasurableSet F ∧ volume F = ENNReal.ofReal m := by
  have hAfin : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hAsub)
    rw [Real.volume_Icc]; exact ofReal_ne_top
  -- Work with the real number `dA = |A|`; both `A` and `Icc a b` have finite measure.
  obtain ⟨dA, hdAnn, hAeq⟩ : ∃ dA : ℝ, 0 ≤ dA ∧ volume A = ENNReal.ofReal dA :=
    ⟨(volume A).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hAfin).symm⟩
  have hdAle_m : dA ≤ m := ENNReal.ofReal_le_ofReal_iff hm0 |>.mp (hAeq ▸ hmA)
  have hdAle_ba : dA ≤ b - a := by
    have := (measure_mono hAsub).trans (le_of_eq (Real.volume_Icc (a := a) (b := b)))
    rw [hAeq] at this
    exact ENNReal.ofReal_le_ofReal_iff (by linarith) |>.mp this
  set C : Set ℝ := Set.Icc a b \ A with hCdef
  have hCmeas : MeasurableSet C := measurableSet_Icc.diff hA
  have hCsub : C ⊆ Set.Icc a b := sdiff_subset
  have hCvol : volume C = ENNReal.ofReal (b - a) - volume A := by
    rw [hCdef, measure_sdiff (by exact hAsub) hA.nullMeasurableSet hAfin, Real.volume_Icc]
  have hdefnn : 0 ≤ m - dA := by linarith
  have hCge : ENNReal.ofReal (m - dA) ≤ volume C := by
    rw [hCvol, hAeq, ← ENNReal.ofReal_sub _ hdAnn]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨B, hBsub, hBmeas, hBvol⟩ :=
    exists_measurableSet_subset_volume hab C hCmeas hCsub hdefnn hCge
  refine ⟨A ∪ B, subset_union_left, ?_, hA.union hBmeas, ?_⟩
  · exact union_subset hAsub (hBsub.trans hCsub)
  · have hdisj : Disjoint A B := Set.disjoint_of_subset_right hBsub (by
      rw [hCdef]; exact Set.disjoint_sdiff_right)
    rw [measure_union hdisj hBmeas, hBvol, hAeq,
      ← ENNReal.ofReal_add hdAnn hdefnn]
    congr 1; ring

/-- **Upper-half fixed-arc domination (extended-real form).** For a nonnegative measurable ring
potential `u` (`0 ≤ u`, `Measurable u`), a measurable arc-parameter set `E` on which the arc fibre
`φ ↦ u (p + exp (w + φ·I))` is integrable, and a log-polar point `w` with `0 ≤ Im w ≤ π`, the
extended-real value of the arc integral is dominated by the star function at radius `exp (Re w)` and
half-aperture `Im w`, *provided* the arc — rotated by `w` into the profile parametrisation, i.e.
`E' = (· + (Im w + π)) '' E` — lands in the parameter interval `Icc 0 (2π)` and has measure at most
`2·Im w`.

The load-bearing hypotheses are `volume E ≤ ofReal (2·Im w)` and `Im w ≤ π`: the rotated arc `E'`
(same measure as `E`, being a translate) is then *extended* to a subset `F ⊆ Icc 0 (2π)` of measure
exactly `2·Im w` via `exists_measurableSet_superset_volume`, and since the profile `g ≥ 0`,

`ofReal (arcIntegral p u E w) = ∫⁻_{E'} g ≤ ∫⁻_F g ≤ ⨆_{|F'| = 2·Im w} ∫⁻_{F'} g
  = starFunction p u (exp (Re w)) (Im w)`,

the last equality being the Hardy–Littlewood characterisation `starProfile_eq_iSup_setLIntegral`.
The constraint `E' ⊆ Icc 0 (2π)` (equivalently: the arc, once rotated, fits in one period) is
exactly what confines the direct argument to circle points with `Im w ≥ Im w₀`; below the centre
the extremal set is first trimmed along the uncovered window (Sjögren's surgery) before this
lemma applies. -/
theorem arcIntegral_le_starFunction {p : ℂ} {u : ℂ → ℝ} {E : Set ℝ} {w : ℂ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E))
    (hEmeas : MeasurableSet E) (hwim0 : 0 ≤ w.im) (hwimπ : w.im ≤ π)
    (hE'sub : (fun φ : ℝ => φ + (w.im + π)) '' E ⊆ Set.Icc 0 (2 * π))
    (hEvol : volume E ≤ ENNReal.ofReal (2 * w.im)) :
    ENNReal.ofReal (arcIntegral p u E w) ≤ starFunction p u (Real.exp w.re) w.im := by
  classical
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal
      (angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w.re) ψ).toReal with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp w.re)))
  set E' : Set ℝ := (fun φ : ℝ => φ + (w.im + π)) '' E with hE'def
  have hE'meas : MeasurableSet E' :=
    (measurableEmbedding_addRight (w.im + π)).measurableSet_image.2 hEmeas
  have hmp : MeasurePreserving (fun φ : ℝ => φ + (w.im + π)) volume volume :=
    measurePreserving_add_right volume (w.im + π)
  have hE'vol : volume E' = volume E := by
    rw [hE'def, image_add_right, measure_preimage_add_right]
  -- Integral chain: `ofReal (arcIntegral) = ∫⁻_{E'} g`.
  have hchain : ENNReal.ofReal (arcIntegral p u E w) = ∫⁻ ψ in E', g ψ := by
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w + φ * Complex.I)))
        = g (φ + (w.im + π)) := by
      intro φ
      rw [hgdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w + (φ : ℂ) * Complex.I = (w.re : ℂ) + ((φ + w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring_nf
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w.im + π)) g
      ((fun φ : ℝ => φ + (w.im + π)) '' E)
    rw [Set.preimage_image_eq _ (add_left_injective (w.im + π))] at hkey
    rw [hkey]
  -- Extend `E'` to a set `F ⊆ Icc 0 (2π)` of measure exactly `2·Im w`.
  obtain ⟨F, hE'F, hFsub, hFmeas, hFvol⟩ :=
    exists_measurableSet_superset_volume (m := 2 * w.im)
      (by positivity : (0 : ℝ) ≤ 2 * π) E' hE'meas hE'sub
      (by positivity) (by rw [hE'vol]; exact hEvol) (by linarith)
  -- `∫⁻_{E'} g ≤ ∫⁻_F g ≤ sup = starFunction`.
  have hmono : (∫⁻ ψ in E', g ψ) ≤ ∫⁻ ψ in F, g ψ := lintegral_mono_set hE'F
  have hsup : starFunction p u (Real.exp w.re) w.im
      = ⨆ F' ∈ {F' : Set ℝ | MeasurableSet F' ∧ F' ⊆ Icc (0 : ℝ) (2 * π)
          ∧ volume F' = ENNReal.ofReal (2 * w.im)}, ∫⁻ ψ in F', g ψ := by
    rw [show starFunction p u (Real.exp w.re) w.im = starProfile (2 * π) g w.im from rfl]
    exact starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hwim0 (by linarith)
  rw [hchain, hsup]
  exact le_trans hmono (le_iSup₂_of_le F ⟨hFmeas, hFsub, hFvol⟩ le_rfl)

/-- **Upper-half fixed-arc domination (real form).** The real-valued restatement of
`arcIntegral_le_starFunction`: under the same hypotheses, and provided the star value is finite (so
its `.toReal` is faithful; use `starFunction_lt_top` under an upper bound on `u`), the arc integral
is dominated by the log-polar star surface `starPlane p u w`. Since `arcIntegral_harmonicOn` shows
`arcIntegral p u E` is harmonic — hence equal to its own circle average — this domination on the
upper half of a sub-mean-value circle is the buildable half of the star-surface sub-mean-value. -/
theorem arcIntegral_le_starPlane {p : ℂ} {u : ℂ → ℝ} {E : Set ℝ} {w : ℂ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E))
    (hEmeas : MeasurableSet E) (hwim0 : 0 ≤ w.im) (hwimπ : w.im ≤ π)
    (hE'sub : (fun φ : ℝ => φ + (w.im + π)) '' E ⊆ Set.Icc 0 (2 * π))
    (hEvol : volume E ≤ ENNReal.ofReal (2 * w.im))
    (hfin : starFunction p u (Real.exp w.re) w.im < ⊤) :
    arcIntegral p u E w ≤ starPlane p u w := by
  have hdom := arcIntegral_le_starFunction hu0 hu hint hEmeas hwim0 hwimπ hE'sub hEvol
  have harc0 : (0 : ℝ) ≤ arcIntegral p u E w := by
    rw [arcIntegral]
    exact integral_nonneg (fun φ => hu0 _)
  have := ENNReal.toReal_mono hfin.ne hdom
  rwa [ENNReal.toReal_ofReal harc0] at this

/-- **The extremal-arc identity at the centre.** At any log-polar point `w₀` of the strip
`logPolarStrip rI rO` (so `0 < Im w₀ < π`), the star value `starPlane p u w₀` is *attained* by a
genuine fixed arc-parameter set `E₀`: there is a measurable, bounded `E₀ ⊆ ℝ` of measure exactly
`2·Im w₀` such that the fixed-arc harmonic integral `arcIntegral p u E₀` agrees with the star
surface at `w₀`,

`arcIntegral p u E₀ w₀ = starPlane p u w₀`.

Take `F` to be the extremal super-level set of `exists_attaining_set` for the angular profile `g` at
radius `exp (Re w₀)` and half-aperture `Im w₀` (so `∫⁻_F g = starFunction p u (exp (Re w₀)) (Im w₀)`
and `|F| = 2·Im w₀`), and let `E₀ = (· − (Im w₀ + π)) '' F` be its de-rotation into the
arc-parameter frame. The measure-preserving translation and the pointwise `u ↔ g` circle-point
matching give `ofReal (arcIntegral p u E₀ w₀) = ∫⁻_F g = starFunction p u (exp (Re w₀)) (Im w₀)`,
and taking `.toReal` (faithful since the star value is finite by `starFunction_lt_top` and the arc
integral is nonnegative) yields the identity. The extremal arc reproduces the star value at its
centre, seeding the harmonic competitor `arcIntegral p u E₀`. -/
theorem arcIntegral_eq_starPlane_extremal {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {w₀ : ℂ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hbdd : ∃ M : ℝ, ∀ φ : ℝ,
        u (p + (Real.exp w₀.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hw₀ : w₀ ∈ logPolarStrip rI rO) :
    ∃ E₀ : Set ℝ, MeasurableSet E₀ ∧ Bornology.IsBounded E₀ ∧
      volume E₀ = ENNReal.ofReal (2 * w₀.im) ∧
      arcIntegral p u E₀ w₀ = starPlane p u w₀ := by
  classical
  obtain ⟨hw₀re, hw₀im⟩ := hw₀
  have hwim0 : 0 ≤ w₀.im := hw₀im.1.le
  have hwimπ : w₀.im ≤ π := hw₀im.2.le
  -- The angular profile `g` at radius `exp (Re w₀)`; `starFunction … = starProfile (2π) g (Im w₀)`.
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal
      (angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w₀.re) ψ).toReal with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp w₀.re)))
  -- STEP A: the extremal attaining set `F ⊆ Icc 0 (2π)` with `∫⁻_F g = starFunction …`.
  obtain ⟨F, hFmeas, hFsub, hFvol, hFint⟩ :=
    exists_attaining_set (T := 2 * π) (g := g) (θ := w₀.im) (by positivity) hgmeas hwim0
      (by linarith)
  have hFstar : (∫⁻ ψ in F, g ψ) = starFunction p u (Real.exp w₀.re) w₀.im := hFint
  -- STEP B: de-rotate `F` into the arc-parameter frame: `E₀ = (· + (−(Im w₀ + π))) '' F`.
  set E₀ : Set ℝ := (fun ψ : ℝ => ψ + (-(w₀.im + π))) '' F with hE₀def
  have hE₀meas : MeasurableSet E₀ :=
    (measurableEmbedding_addRight (-(w₀.im + π))).measurableSet_image.2 hFmeas
  -- `E₀` is bounded: it is a translate of the bounded `F ⊆ Icc 0 (2π)`.
  have hFbdd : Bornology.IsBounded F := (Metric.isBounded_Icc _ _).subset hFsub
  have hE₀bdd : Bornology.IsBounded E₀ := by
    refine (Metric.isBounded_Icc (0 + (-(w₀.im + π))) (2 * π + (-(w₀.im + π)))).subset ?_
    rw [hE₀def]
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨by linarith [(hFsub hψ).1], by linarith [(hFsub hψ).2]⟩
  -- Measure of `E₀` equals that of `F` (translation preserves measure).
  have hE₀vol : volume E₀ = volume F := by
    rw [hE₀def, image_add_right, measure_preimage_add_right]
  -- Rotating `E₀` back gives `F`: `(· + (Im w₀ + π)) '' E₀ = F`.
  have hrotback : (fun φ : ℝ => φ + (w₀.im + π)) '' E₀ = F := by
    rw [hE₀def, ← Set.image_comp]
    convert Set.image_id F using 1
    apply Set.image_congr'
    intro ψ
    simp only [Function.comp_apply, id_eq]
    ring
  -- Integrability of the arc fibre on `E₀` (bounded on a finite-measure set).
  obtain ⟨M, hM⟩ := hbdd
  have hE₀fin : volume E₀ ≠ ⊤ := by
    rw [hE₀vol]
    exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ofReal_ne_top) (measure_mono hFsub)
  have hfibmeas : Measurable (fun φ : ℝ => u (p + Complex.exp (w₀ + φ * Complex.I))) := by
    apply hu.comp
    fun_prop
  have hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w₀ + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E₀) := by
    have : IsFiniteMeasure ((volume : Measure ℝ).restrict E₀) :=
      isFiniteMeasure_restrict.2 hE₀fin
    refine Integrable.of_bound hfibmeas.aestronglyMeasurable (max M 0) ?_
    filter_upwards with φ
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨by linarith [hu0 (p + Complex.exp (w₀ + φ * Complex.I)), le_max_right M 0], ?_⟩
    -- `u (p + exp (w₀ + φI)) = u (p + exp (Re w₀) · exp ((Im w₀ + φ)I)) ≤ M ≤ max M 0`.
    have hsplit : w₀ + (φ : ℂ) * Complex.I
        = (w₀.re : ℂ) + ((w₀.im + φ : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp
    have hpt : (p + Complex.exp (w₀ + φ * Complex.I))
        = p + (Real.exp w₀.re : ℂ) * Complex.exp ((w₀.im + φ : ℝ) * Complex.I) := by
      rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
    rw [hpt]
    exact le_trans (hM (w₀.im + φ)) (le_max_left M 0)
  -- STEP C: `ofReal (arcIntegral p u E₀ w₀) = ∫⁻_F g`, via the same chain as the domination lemma.
  have hchain : ENNReal.ofReal (arcIntegral p u E₀ w₀) = ∫⁻ ψ in F, g ψ := by
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w₀ + φ * Complex.I)))
        = g (φ + (w₀.im + π)) := by
      intro φ
      rw [hgdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w₀ + (φ : ℂ) * Complex.I = (w₀.re : ℂ) + ((φ + w₀.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring_nf
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hmp : MeasurePreserving (fun φ : ℝ => φ + (w₀.im + π)) volume volume :=
      measurePreserving_add_right volume (w₀.im + π)
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w₀.im + π)) g
      ((fun φ : ℝ => φ + (w₀.im + π)) '' E₀)
    rw [Set.preimage_image_eq _ (add_left_injective (w₀.im + π)), hrotback] at hkey
    rw [hkey]
  -- Finiteness of the star value and nonnegativity of the arc integral: `.toReal` is faithful.
  have hfin : starFunction p u (Real.exp w₀.re) w₀.im < ⊤ :=
    starFunction_lt_top hwim0 hwimπ ⟨M, hM⟩
  have harc0 : (0 : ℝ) ≤ arcIntegral p u E₀ w₀ := by
    rw [arcIntegral]; exact integral_nonneg (fun φ => hu0 _)
  refine ⟨E₀, hE₀meas, hE₀bdd, by rw [hE₀vol, hFvol], ?_⟩
  -- `ofReal (arcIntegral) = ∫⁻_F g = starFunction`, so `arcIntegral = starPlane` after `.toReal`.
  have heq : ENNReal.ofReal (arcIntegral p u E₀ w₀) = starFunction p u (Real.exp w₀.re) w₀.im := by
    rw [hchain, hFstar]
  rw [starPlane, ← heq, ENNReal.toReal_ofReal harc0]

/-!
## The star-surface sub-mean-value inequality (Sjögren's surgery)

The sub-mean-value inequality for `starPlane p u` at a strip point `w₀` is driven by the harmonic
competitor `arcIntegral p u E₀`, where `E₀` de-rotates an extremal structured set
(`exists_attaining_structured`): a set of measure `2·Im w₀` attaining the star value at the centre
and carrying a full leftmost interval of length `δ`. Four ingredients combine:

* **translate bound** (`volume_translate_inter_le`): the translates `E₀ ± ε` overlap in measure at
  most `|E₀| − 2ε` once `2ε ≤ δ` — sliding the leftmost interval uncovers a window of length `2ε`;
* **window domination** (`arcIntegral_le_starPlane`): opposite circle points `w₀ ± ρe^{iψ}` share
  their radius, and cutting/re-gluing the translated extremal sets along the uncovered window
  yields admissible competitors for both target apertures `2·Im w₀ ± 2ρ·sin ψ`;
* **MVP pairing**: `arcIntegral p u E₀` is harmonic on the strip, so its centre value equals its
  circle average; averaging the paired domination gives the sub-mean-value inequality on all
  circles of radius `ρ < δ/2` (`starPlane_subMeanValue_small`);
* **local-to-global**: continuity (`starPlane_continuousOn`) and the Poisson-modification principle
  (`subharmonicOn_of_locally`) extend the inequality to every admissible radius
  (`starPlane_subharmonicOn`).
-/

/-- **Baernstein's translate bound.** For a set `E` with least element `x₀` carrying a full
interval `[x₀, x₀ + ℓ] ⊆ E` (the leftmost component of `E` has length at least `ℓ`), the two
translates `E + ε` and `E − ε` overlap in measure at most `|E| − 2ε` whenever `2ε ≤ ℓ`: the sliding
of the leftmost component uncovers an interval of length `2ε` that belongs to `E − ε` but meets no
point of `E + ε`. -/
theorem volume_translate_inter_le {E : Set ℝ} {x₀ ℓ : ℝ}
    (hx₀ : IsLeast E x₀) (hIcc : Set.Icc x₀ (x₀ + ℓ) ⊆ E) {ε : ℝ}
    (hεℓ : 2 * ε ≤ ℓ) :
    volume ((fun x => x + ε) '' E ∩ (fun x => x - ε) '' E)
      ≤ volume E - ENNReal.ofReal (2 * ε) := by
  -- The uncovered window `[x₀ − ε, x₀ + ε)` lies inside `E − ε` but misses `E + ε` entirely.
  have hwin : Ico (x₀ - ε) (x₀ + ε) ⊆ (fun x => x - ε) '' E := by
    intro x hx
    refine ⟨x + ε, hIcc ⟨by linarith [hx.1], by linarith [hx.2]⟩, by ring⟩
  have hsub : (fun x => x + ε) '' E ∩ (fun x => x - ε) '' E
      ⊆ (fun x => x - ε) '' E \ Ico (x₀ - ε) (x₀ + ε) := by
    rintro y ⟨⟨e₁, he₁, rfl⟩, hy₂⟩
    refine ⟨hy₂, fun hy => ?_⟩
    exact absurd hy.2 (not_lt.mpr (by linarith [hx₀.2 he₁]))
  -- Translates preserve volume; removing the window subtracts exactly `2ε`.
  have hvol₂ : volume ((fun x => x - ε) '' E) = volume E := by
    have himg : (fun x : ℝ => x - ε) '' E = (fun x : ℝ => x + (-ε)) '' E := by
      apply Set.image_congr'
      intro x; ring
    rw [himg, image_add_right, measure_preimage_add_right]
  calc volume ((fun x => x + ε) '' E ∩ (fun x => x - ε) '' E)
      ≤ volume ((fun x => x - ε) '' E \ Ico (x₀ - ε) (x₀ + ε)) := measure_mono hsub
    _ = volume ((fun x => x - ε) '' E) - volume (Ico (x₀ - ε) (x₀ + ε)) :=
        measure_sdiff hwin measurableSet_Ico.nullMeasurableSet
          (by rw [Real.volume_Ico]; exact ofReal_ne_top)
    _ = volume E - ENNReal.ofReal (2 * ε) := by
        rw [hvol₂, Real.volume_Ico]
        congr 1
        ring_nf

/-- **Windowed fixed-arc domination.** The conclusion of `arcIntegral_le_starFunction` under a
relaxed window hypothesis: the rotated arc `E' = (· + (Im w + π)) '' E` need only fit in *some*
interval `[a, a + 2π]` of length `2π`, not necessarily `[0, 2π]`. Since the angular profile is
`2π`-periodic, the two pieces of `E'` on either side of the lattice point `2π·⌈a/(2π)⌉` can be
shifted by integer multiples of `2π` into the standard window `[0, 2π]` without changing the
integral or the measure, and the standard supremum characterisation of the star profile applies. -/
theorem arcIntegral_le_starFunction_window {p : ℂ} {u : ℂ → ℝ} {E : Set ℝ} {w : ℂ} (a : ℝ)
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E))
    (hEmeas : MeasurableSet E) (hwim0 : 0 ≤ w.im) (hwimπ : w.im ≤ π)
    (hE'sub : (fun φ : ℝ => φ + (w.im + π)) '' E ⊆ Set.Icc a (a + 2 * π))
    (hEvol : volume E ≤ ENNReal.ofReal (2 * w.im)) :
    ENNReal.ofReal (arcIntegral p u E w) ≤ starFunction p u (Real.exp w.re) w.im := by
  classical
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal
      (angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w.re) ψ).toReal with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp w.re)))
  -- The profile is `2π`-periodic (through any integer number of turns).
  have hgper : ∀ (n : ℤ) (φ : ℝ), g (φ + 2 * π * n) = g φ := by
    intro n φ
    rw [hgdef]
    simp only [angularProfile]
    congr 3
    have hsplit : ((φ + 2 * π * n - π : ℝ) : ℂ) * Complex.I
        = ((φ - π : ℝ) : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set E' : Set ℝ := (fun φ : ℝ => φ + (w.im + π)) '' E with hE'def
  have hE'meas : MeasurableSet E' :=
    (measurableEmbedding_addRight (w.im + π)).measurableSet_image.2 hEmeas
  have hE'vol : volume E' = volume E := by
    rw [hE'def, image_add_right, measure_preimage_add_right]
  -- Integral chain: `ofReal (arcIntegral) = ∫⁻_{E'} g`.
  have hchain : ENNReal.ofReal (arcIntegral p u E w) = ∫⁻ ψ in E', g ψ := by
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w + φ * Complex.I)))
        = g (φ + (w.im + π)) := by
      intro φ
      rw [hgdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w + (φ : ℂ) * Complex.I = (w.re : ℂ) + ((φ + w.im : ℝ) : ℂ) * Complex.I := by
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
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w.im + π)) g
      ((fun φ : ℝ => φ + (w.im + π)) '' E)
    rw [Set.preimage_image_eq _ (add_left_injective (w.im + π))] at hkey
    rw [hkey]
  -- Split `E'` at the lattice point `2π·k`, `k = ⌈a/(2π)⌉`.
  set k : ℤ := ⌈a / (2 * π)⌉ with hkdef
  have hπpos : (0 : ℝ) < 2 * π := by positivity
  have ha1 : a ≤ 2 * π * k := by
    have := Int.le_ceil (a / (2 * π))
    rw [div_le_iff₀ hπpos] at this
    linarith [this]
  have ha2 : 2 * π * k ≤ a + 2 * π := by
    have := Int.ceil_lt_add_one (a / (2 * π))
    have h2 : (k : ℝ) * (2 * π) < (a / (2 * π) + 1) * (2 * π) :=
      mul_lt_mul_of_pos_right this hπpos
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hπpos), one_mul] at h2
    linarith
  set s₀ : ℝ := a + 2 * π - 2 * π * k with hs₀def
  have hs₀0 : 0 ≤ s₀ := by rw [hs₀def]; linarith
  have hs₀2π : s₀ ≤ 2 * π := by rw [hs₀def]; linarith
  set E₁ : Set ℝ := E' ∩ Iio (2 * π * k) with hE₁def
  set E₂ : Set ℝ := E' ∩ Ici (2 * π * k) with hE₂def
  have hE₁meas : MeasurableSet E₁ := hE'meas.inter measurableSet_Iio
  have hE₂meas : MeasurableSet E₂ := hE'meas.inter measurableSet_Ici
  have hEsplit : E' = E₁ ∪ E₂ := by
    rw [hE₁def, hE₂def, ← inter_union_distrib_left, Iio_union_Ici, inter_univ]
  have hEdisj : Disjoint E₁ E₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
    exact absurd (mem_Ici.mp hx2) (not_le.mpr (mem_Iio.mp hx1))
  -- Shift each piece by an integer multiple of `2π` into `[0, 2π]`.
  set c₁ : ℝ := 2 * π * (1 - k) with hc₁def
  set c₂ : ℝ := 2 * π * (0 - k) with hc₂def
  set D₁ : Set ℝ := (fun x => x + c₁) '' E₁ with hD₁def
  set D₂ : Set ℝ := (fun x => x + c₂) '' E₂ with hD₂def
  have hD₁meas : MeasurableSet D₁ := (measurableEmbedding_addRight c₁).measurableSet_image.2 hE₁meas
  have hD₂meas : MeasurableSet D₂ := (measurableEmbedding_addRight c₂).measurableSet_image.2 hE₂meas
  -- Periodic shift invariance of the profile integral.
  have hshift : ∀ (n : ℤ) (S : Set ℝ),
      (∫⁻ ψ in (fun x => x + 2 * π * (n : ℝ)) '' S, g ψ) = ∫⁻ φ in S, g φ := by
    intro n S
    have hmp : MeasurePreserving (fun φ : ℝ => φ + 2 * π * (n : ℝ)) volume volume :=
      measurePreserving_add_right volume _
    have hkey := hmp.setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight (2 * π * (n : ℝ))) g ((fun x => x + 2 * π * (n : ℝ)) '' S)
    rw [Set.preimage_image_eq _ (add_left_injective _)] at hkey
    rw [← hkey]
    exact lintegral_congr_ae (Filter.Eventually.of_forall (fun φ => hgper n φ))
  have hint₁ : (∫⁻ ψ in D₁, g ψ) = ∫⁻ ψ in E₁, g ψ := by
    rw [hD₁def, hc₁def, show (2 * π * ((1 : ℝ) - k)) = 2 * π * (((1 - k : ℤ) : ℝ)) from by
      push_cast; ring]
    exact hshift (1 - k) E₁
  have hint₂ : (∫⁻ ψ in D₂, g ψ) = ∫⁻ ψ in E₂, g ψ := by
    rw [hD₂def, hc₂def, show (2 * π * ((0 : ℝ) - k)) = 2 * π * (((0 - k : ℤ) : ℝ)) from by
      push_cast; ring]
    exact hshift (0 - k) E₂
  have hvol₁ : volume D₁ = volume E₁ := by rw [hD₁def, image_add_right, measure_preimage_add_right]
  have hvol₂ : volume D₂ = volume E₂ := by rw [hD₂def, image_add_right, measure_preimage_add_right]
  -- The shifted pieces land in `[0, 2π]`, meeting at most at the seam point `s₀`.
  have hD₁sub : D₁ ⊆ Ico s₀ (2 * π) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE', hxlt⟩ := hx
    have hxa : a ≤ x := (hE'sub hxE').1
    constructor
    · rw [hs₀def, hc₁def]; push_cast; linarith
    · rw [hc₁def]; push_cast; linarith [mem_Iio.mp hxlt]
  have hD₂sub : D₂ ⊆ Icc 0 s₀ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE', hxge⟩ := hx
    have hxa : x ≤ a + 2 * π := (hE'sub hxE').2
    constructor
    · rw [hc₂def]; push_cast; linarith [mem_Ici.mp hxge]
    · rw [hs₀def, hc₂def]; push_cast; linarith
  have hDinter : volume (D₁ ∩ D₂) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_singleton s₀)
    have h1 := hD₁sub hx.1
    have h2 := hD₂sub hx.2
    exact le_antisymm h2.2 h1.1
  -- Sum of the two shifted integrals is the integral over the union.
  have hsum : (∫⁻ ψ in D₁, g ψ) + ∫⁻ ψ in D₂, g ψ = ∫⁻ ψ in D₁ ∪ D₂, g ψ := by
    have hd₁ : (∫⁻ ψ in D₁, g ψ) = ∫⁻ ψ in D₁ \ D₂, g ψ := by
      conv_lhs => rw [← Set.sdiff_union_inter D₁ D₂]
      rw [lintegral_union (hD₁meas.inter hD₂meas) Set.disjoint_sdiff_inter,
        setLIntegral_measure_zero _ _ hDinter, add_zero]
    rw [hd₁, ← lintegral_union hD₂meas disjoint_sdiff_left, Set.sdiff_union_self]
  -- The union is an admissible competitor for the star profile.
  set D : Set ℝ := D₁ ∪ D₂ with hDdef
  have hDmeas : MeasurableSet D := hD₁meas.union hD₂meas
  have hDsub : D ⊆ Icc 0 (2 * π) := by
    rintro x (hx | hx)
    · exact ⟨le_trans hs₀0 (hD₁sub hx).1, (hD₁sub hx).2.le⟩
    · exact ⟨(hD₂sub hx).1, le_trans (hD₂sub hx).2 hs₀2π⟩
  have hDvol : volume D ≤ ENNReal.ofReal (2 * w.im) := by
    calc volume D ≤ volume D₁ + volume D₂ := measure_union_le _ _
      _ = volume E₁ + volume E₂ := by rw [hvol₁, hvol₂]
      _ = volume E' := by rw [← measure_union hEdisj hE₂meas, ← hEsplit]
      _ ≤ ENNReal.ofReal (2 * w.im) := by rw [hE'vol]; exact hEvol
  -- Extend `D` to measure exactly `2·Im w` and conclude via the supremum characterisation.
  obtain ⟨F, hDF, hFsub, hFmeas, hFvol⟩ :=
    exists_measurableSet_superset_volume (m := 2 * w.im)
      (by positivity : (0 : ℝ) ≤ 2 * π) D hDmeas hDsub
      (by positivity) hDvol (by linarith)
  have hmono : (∫⁻ ψ in D, g ψ) ≤ ∫⁻ ψ in F, g ψ := lintegral_mono_set hDF
  have hsup : starFunction p u (Real.exp w.re) w.im
      = ⨆ F' ∈ {F' : Set ℝ | MeasurableSet F' ∧ F' ⊆ Icc (0 : ℝ) (2 * π)
          ∧ volume F' = ENNReal.ofReal (2 * w.im)}, ∫⁻ ψ in F', g ψ := by
    rw [show starFunction p u (Real.exp w.re) w.im = starProfile (2 * π) g w.im from rfl]
    exact starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hwim0 (by linarith)
  calc ENNReal.ofReal (arcIntegral p u E w) = ∫⁻ ψ in E', g ψ := hchain
    _ = (∫⁻ ψ in E₁, g ψ) + ∫⁻ ψ in E₂, g ψ := by
        rw [hEsplit, lintegral_union hE₂meas hEdisj]
    _ = (∫⁻ ψ in D₁, g ψ) + ∫⁻ ψ in D₂, g ψ := by rw [hint₁, hint₂]
    _ = ∫⁻ ψ in D, g ψ := hsum
    _ ≤ ∫⁻ ψ in F, g ψ := hmono
    _ ≤ starFunction p u (Real.exp w.re) w.im := by
        rw [hsup]
        exact le_iSup₂_of_le F ⟨hFmeas, hFsub, hFvol⟩ le_rfl

/-- **Structured extremal attaining set for a harmonic profile.** For `u` harmonic and nonnegative
on the annulus and a radius `r ∈ (rI, rO)`, the star value at half-aperture `θ ∈ (0, π)` is
attained by a set `F` carrying the level structure of the real-analytic circle profile: `F` sits
in a `2π`-window `[τ + δ, τ + 2π − δ]` with slack `δ > 0`, has measure exactly `2θ`, and its least
point carries a full interval `[x₀, x₀ + δ] ⊆ F` (the leftmost component of `F` is an honest
interval). For a non-constant circle profile `G`, the level `c` of the rearrangement has finite
level set on any compact window (one-dimensional identity theorem for the real-analytic `G`), and
`F` is the union of the closed arcs between consecutive zeros of `G − c` on which `G > c`; the
window base `τ` is a point with `G τ < c`, which exists because the super-level measure `2θ` is
less than the full circle `2π`. For a constant profile a centered arc attains. -/
theorem exists_attaining_structured {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {r θ : ℝ}
    (hrI : 0 < rI)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u)
    (hr : r ∈ Set.Ioo rI rO) (hθ : θ ∈ Set.Ioo 0 π) :
    ∃ (τ δ : ℝ) (F : Set ℝ), 0 < δ ∧ MeasurableSet F ∧
      F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
      volume F = ENNReal.ofReal (2 * θ) ∧
      (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
      (∫⁻ ψ in F, ENNReal.ofReal
          ((angularProfile p (fun z => ENNReal.ofReal (u z)) r ψ).toReal))
        = starFunction p u r θ := by
  classical
  obtain ⟨hθ0, hθπ⟩ := hθ
  set A : Set ℂ := {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} with hA
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal ((angularProfile p (fun z => ENNReal.ofReal (u z)) r ψ).toReal)
    with hgdef
  set G : ℝ → ℝ := fun ψ => u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) with hGdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) r))
  have hgG : ∀ ψ : ℝ, g ψ = ENNReal.ofReal (G ψ) := by
    intro ψ
    simp only [hgdef, hGdef, angularProfile]
    rw [ENNReal.toReal_ofReal (hu0 _)]
  have hG0 : ∀ ψ : ℝ, 0 ≤ G ψ := fun ψ => hu0 _
  rcases Classical.em (∀ ψ₁ ψ₂ : ℝ, G ψ₁ = G ψ₂) with hconst | hconst
  · -- Constant circle profile: any measure-`2θ` set attains; take the centered arc.
    have hgc : ∀ ψ : ℝ, g ψ = ENNReal.ofReal (G 0) := by
      intro ψ; rw [hgG ψ, hconst ψ 0]
    have hval : ∀ E : Set ℝ, volume E = ENNReal.ofReal (2 * θ) →
        (∫⁻ ψ in E, g ψ) = ENNReal.ofReal (G 0) * ENNReal.ofReal (2 * θ) := by
      intro E hE
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hgc), setLIntegral_const, hE]
    have hFsub' : Icc (π - θ) (π + θ) ⊆ Icc (0 : ℝ) (2 * π) := by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hFvol' : volume (Icc (π - θ) (π + θ)) = ENNReal.ofReal (2 * θ) := by
      rw [Real.volume_Icc]; congr 1; ring
    have hFmem : Icc (π - θ) (π + θ) ∈ {E : Set ℝ | MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) (2 * π)
        ∧ volume E = ENNReal.ofReal (2 * θ)} := ⟨measurableSet_Icc, hFsub', hFvol'⟩
    have hstar : starFunction p u r θ = ENNReal.ofReal (G 0) * ENNReal.ofReal (2 * θ) := by
      rw [show starFunction p u r θ = starProfile (2 * π) g θ from rfl,
        starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hθ0.le (by linarith)]
      apply le_antisymm
      · exact iSup₂_le fun E hE => le_of_eq (hval E hE.2.2)
      · exact le_iSup₂_of_le _ hFmem (le_of_eq (hval _ hFvol').symm)
    refine ⟨0, min (π - θ) θ, Icc (π - θ) (π + θ), lt_min (by linarith) hθ0,
      measurableSet_Icc, ?_, hFvol', ⟨π - θ, ⟨⟨le_rfl, by linarith⟩, fun y hy => hy.1⟩, ?_⟩, ?_⟩
    · intro x hx
      constructor
      · have := min_le_left (π - θ) θ; linarith [hx.1]
      · have := min_le_left (π - θ) θ; linarith [hx.2]
    · intro x hx
      have := min_le_right (π - θ) θ
      exact ⟨hx.1, by linarith [hx.2]⟩
    · rw [hval _ hFvol', hstar]
  · -- Non-constant circle profile: identity theorem + arcs between consecutive zeros of `G − c`.
    push Not at hconst
    obtain ⟨ψ₁, ψ₂, hne⟩ := hconst
    have hπpos : (0 : ℝ) < 2 * π := by positivity
    -- Continuity, membership, analyticity of the circle profile.
    have hAopen : IsOpen A := by
      have h1 : IsOpen {z : ℂ | rI < ‖z - p‖} := isOpen_lt continuous_const (by fun_prop)
      have h2 : IsOpen {z : ℂ | ‖z - p‖ < rO} := isOpen_lt (by fun_prop) continuous_const
      simpa [hA, Set.ofPred_and] using h1.inter h2
    have hmA : ∀ ψ : ℝ, (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) ∈ A := by
      intro ψ
      have hn : ‖(p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) - p‖ = r := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real,
          Real.norm_eq_abs]
        have him : ((((ψ - π : ℝ)) : ℂ) * Complex.I).re = 0 := by
          simp [Complex.mul_re]
        rw [him, Real.exp_zero, mul_one, abs_of_pos (lt_trans hrI hr.1)]
      rw [hA]
      exact ⟨by rw [hn]; exact hr.1, by rw [hn]; exact hr.2⟩
    have hucont : ContinuousOn u A := hu.continuousOn
    have hGcont : Continuous G := by
      rw [continuous_iff_continuousAt]
      intro ψ
      have hmc : Continuous
          (fun ψ : ℝ => p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) := by fun_prop
      have hcomp := ContinuousAt.comp (x := ψ) (g := u)
        (hucont.continuousAt (hAopen.mem_nhds (hmA ψ))) hmc.continuousAt
      exact hcomp
    have hGanal : ∀ ψ : ℝ, AnalyticAt ℝ G ψ := by
      intro ψ
      have h0 : AnalyticAt ℝ (fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I) ψ := by
        have heqf : (fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I)
            = fun ψ : ℝ => (Complex.ofRealCLM ψ - ((π : ℝ) : ℂ)) * Complex.I := by
          funext φ
          rw [Complex.ofRealCLM_apply, Complex.ofReal_sub]
        rw [heqf]
        exact ((Complex.ofRealCLM.analyticAt ψ).sub analyticAt_const).mul analyticAt_const
      have hexpR : AnalyticAt ℝ Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I) :=
        @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
          IsScalarTower.right _ _ analyticAt_cexp
      have h1 : AnalyticAt ℝ
          (fun ψ : ℝ => Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) ψ :=
        AnalyticAt.comp (g := Complex.exp)
          (f := fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I) hexpR h0
      have h2 : AnalyticAt ℝ
          (fun ψ : ℝ => p + (r : ℂ) * Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) ψ :=
        analyticAt_const.add (analyticAt_const.mul h1)
      have h3 : AnalyticAt ℝ u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) :=
        HarmonicAt.analyticAt (hu _ (hmA ψ))
      have h4 := AnalyticAt.comp (g := u)
        (f := fun ψ : ℝ => p + (r : ℂ) * Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) h3 h2
      exact h4
    -- Periodicity of the profile in the angle, through any integer number of turns.
    have hGperZ : ∀ (n : ℤ) (ψ : ℝ), G (ψ + 2 * π * n) = G ψ := by
      intro n ψ
      have harg : Complex.exp (((ψ + 2 * π * n - π : ℝ)) * Complex.I)
          = Complex.exp (((ψ - π : ℝ)) * Complex.I) := by
        have hsplit : (((ψ + 2 * π * n - π : ℝ)) : ℂ) * Complex.I
            = (((ψ - π : ℝ)) : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
          push_cast; ring
        rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      simp only [hGdef, harg]
    have hGper : ∀ ψ : ℝ, G (ψ + 2 * π) = G ψ := by
      intro ψ; simpa using hGperZ 1 ψ
    have hgperZ : ∀ (n : ℤ) (ψ : ℝ), g (ψ + 2 * π * n) = g ψ := by
      intro n ψ; rw [hgG, hgG, hGperZ]
    -- Uniform bound on the profile, by compactness and periodic reduction.
    have hred : ∀ ψ : ℝ, ∃ s ∈ Icc (0 : ℝ) (2 * π), G ψ = G s := by
      intro ψ
      set n : ℤ := ⌊ψ / (2 * π)⌋ with hn
      have h1 : (n : ℝ) * (2 * π) ≤ ψ := by
        have := Int.floor_le (ψ / (2 * π))
        rwa [le_div_iff₀ hπpos] at this
      have h2 : ψ < ((n : ℝ) + 1) * (2 * π) := by
        have := Int.lt_floor_add_one (ψ / (2 * π))
        rwa [div_lt_iff₀ hπpos] at this
      refine ⟨ψ - 2 * π * n, ⟨by linarith, by linarith⟩, ?_⟩
      have := hGperZ n (ψ - 2 * π * n)
      rwa [sub_add_cancel] at this
    obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcont.continuousOn
    have hMle : ∀ ψ : ℝ, G ψ ≤ max M0 0 := by
      intro ψ
      obtain ⟨s, hs, hGs⟩ := hred ψ
      rw [hGs]
      calc G s ≤ |G s| := le_abs_self _
        _ ≤ M0 := hM0 s hs
        _ ≤ max M0 0 := le_max_left _ _
    have hgleM : ∀ ψ : ℝ, g ψ ≤ ENNReal.ofReal (max M0 0) := by
      intro ψ
      rw [hgG]
      exact ENNReal.ofReal_le_ofReal (hMle ψ)
    -- The rearrangement level `c` at measure `2θ`, and its real form `c'`.
    set c : ℝ≥0∞ := decreasingRearrange (2 * π) g (2 * θ) with hcdef
    have hP1 : distribFun (2 * π) g c ≤ ENNReal.ofReal (2 * θ) :=
      distribFun_decreasingRearrange_le (2 * θ)
    have hlt : ∀ t : ℝ≥0∞, t < c → ENNReal.ofReal (2 * θ) < distribFun (2 * π) g t :=
      fun t ht => (lt_decreasingRearrange_iff (2 * θ) t).mp ht
    have hcne : c ≠ ⊤ := by
      intro hctop
      have h1 : ENNReal.ofReal (max M0 0) < c := by rw [hctop]; exact ENNReal.ofReal_lt_top
      have h2 := hlt _ h1
      have hempty : distribFun (2 * π) g (ENNReal.ofReal (max M0 0)) = 0 := by
        have hset : {y ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal (max M0 0) < g y} = ∅ := by
          ext y
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun _ => not_lt.mpr (hgleM y)
        rw [distribFun, hset, measure_empty]
      rw [hempty] at h2
      exact absurd h2 (not_lt.mpr (zero_le))
    set c' : ℝ := c.toReal with hc'def
    have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
    have hcoe : c = ENNReal.ofReal c' := (ENNReal.ofReal_toReal hcne).symm
    have hsuper_iff : ∀ ψ : ℝ, c < g ψ ↔ c' < G ψ := by
      intro ψ
      rw [hgG, hcoe]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc'0
    have heq_iff : ∀ ψ : ℝ, g ψ = c ↔ G ψ = c' := by
      intro ψ
      rw [hgG, hcoe]
      exact ENNReal.ofReal_eq_ofReal_iff (hG0 ψ) hc'0
    -- Lower distribution bound at the level `c` (right-continuity of the distribution function).
    have hP2 : ENNReal.ofReal (2 * θ) ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} := by
      rcases eq_or_ne c 0 with hc0 | hc0
      · have hset : {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} = Icc (0 : ℝ) (2 * π) := by
          ext x; simp only [mem_ofPred_eq, hc0, zero_le, and_true]
        rw [hset, Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · obtain ⟨v, hvmono, hvmem, hvtend⟩ :=
          exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr hc0)
        set s : ℕ → Set ℝ := fun n => {x ∈ Icc (0 : ℝ) (2 * π) | v n < g x} with hs
        have hsmeas : ∀ n, MeasurableSet (s n) :=
          fun n => measurableSet_Icc.inter (measurableSet_lt measurable_const hgmeas)
        have hsanti : Antitone s :=
          fun i j hij x hx => ⟨hx.1, lt_of_le_of_lt (hvmono.monotone hij) hx.2⟩
        have hsfin : ∃ n, volume (s n) ≠ ⊤ := by
          refine ⟨0, ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))⟩
          rw [Real.volume_Icc]; exact ofReal_ne_top
        have hInter : ⋂ n, s n = {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} := by
          ext x
          simp only [mem_iInter, hs, mem_ofPred_eq]
          constructor
          · intro h; exact ⟨(h 0).1, le_of_tendsto' hvtend (fun n => (h n).2.le)⟩
          · rintro ⟨hxI, hxc⟩ n; exact ⟨hxI, lt_of_lt_of_le (hvmem n).2 hxc⟩
        have htend : Tendsto (fun n => volume (s n)) atTop (𝓝 (volume (⋂ n, s n))) :=
          tendsto_measure_iInter_atTop (fun n => (hsmeas n).nullMeasurableSet) hsanti hsfin
        rw [hInter] at htend
        exact ge_of_tendsto' htend (fun n => (hlt (v n) (hvmem n).2).le)
    -- Finiteness of every level set of `G` on every compact window: identity theorem.
    have hlevfin : ∀ d lo hi : ℝ, Set.Finite {ψ ∈ Icc lo hi | G ψ = d} := by
      intro d lo hi
      by_contra hinf
      rw [Set.not_finite] at hinf
      obtain ⟨x, -, hacc⟩ :=
        hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun ψ hψ => hψ.1)
      have hfreq : ∃ᶠ y in 𝓝[≠] x, G y - d = 0 := by
        rw [frequently_nhdsWithin_iff]
        exact (accPt_iff_frequently.mp hacc).mono
          (fun y hy => ⟨by rw [sub_eq_zero]; exact hy.2.2, hy.1⟩)
      have hanal : AnalyticOnNhd ℝ (fun ψ => G ψ - d) univ :=
        fun ψ _ => (hGanal ψ).sub analyticAt_const
      have heqz := hanal.eqOn_zero_of_preconnected_of_frequently_eq_zero
        isPreconnected_univ (mem_univ x) hfreq
      have h1 := heqz (mem_univ ψ₁)
      have h2 := heqz (mem_univ ψ₂)
      simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
      exact hne (h1.trans h2.symm)
    -- Null atoms and the exact super-level measure `2θ`.
    have hatomnull : volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} = 0 := by
      have hset : {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}
          = {x ∈ Icc (0 : ℝ) (2 * π) | G x = c'} := by
        ext x
        simp only [mem_ofPred_eq]
        exact and_congr_right (fun _ => heq_iff x)
      rw [hset]
      exact ((hlevfin c' 0 (2 * π)).countable).measure_zero _
    have hsupvol : volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} = ENNReal.ofReal (2 * θ) := by
      refine le_antisymm hP1 (le_trans hP2 ?_)
      have hsplit : {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x}
          ⊆ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := by
        rintro x ⟨hxI, hxc⟩
        rcases eq_or_lt_of_le hxc with h | h
        · exact Or.inr ⟨hxI, h.symm⟩
        · exact Or.inl ⟨hxI, h⟩
      calc volume {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x}
          ≤ volume ({x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}) := measure_mono hsplit
        _ ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              + volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := measure_union_le _ _
        _ = volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} := by rw [hatomnull, add_zero]
    -- The window base `τ`: a point strictly below the level.
    obtain ⟨τ, hτlt⟩ : ∃ τ : ℝ, G τ < c' := by
      by_contra hcon
      push Not at hcon
      have hsubs : Icc (0 : ℝ) (2 * π) ⊆ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
          ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := by
        intro x hx
        rcases eq_or_lt_of_le (hcon x) with h | h
        · exact Or.inr ⟨hx, (heq_iff x).mpr h.symm⟩
        · exact Or.inl ⟨hx, (hsuper_iff x).mpr h⟩
      have hchain : ENNReal.ofReal (2 * π) ≤ ENNReal.ofReal (2 * θ) := by
        calc ENNReal.ofReal (2 * π) = volume (Icc (0 : ℝ) (2 * π)) := by
              rw [Real.volume_Icc, sub_zero]
          _ ≤ volume ({x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}) := measure_mono hsubs
          _ ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              + volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := measure_union_le _ _
          _ = ENNReal.ofReal (2 * θ) := by rw [hsupvol, hatomnull, add_zero]
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
      linarith
    have hGτ2π : G (τ + 2 * π) < c' := by rw [hGper τ]; exact hτlt
    -- The finite zero set of `G − c'` on the window `[τ, τ + 2π]`.
    have hZfin : Set.Finite {ψ ∈ Icc τ (τ + 2 * π) | G ψ = c'} := hlevfin c' τ (τ + 2 * π)
    set Zs : Finset ℝ := hZfin.toFinset with hZsdef
    have hZmem : ∀ z : ℝ, z ∈ Zs ↔ z ∈ Icc τ (τ + 2 * π) ∧ G z = c' := by
      intro z
      rw [hZsdef, Set.Finite.mem_toFinset]
      exact Iff.rfl
    -- Sign constancy on zero-free open intervals, by the intermediate value theorem.
    have hsign : ∀ z₁ z₂ : ℝ, (∀ y ∈ Ioo z₁ z₂, G y ≠ c') →
        ∀ y₁ ∈ Ioo z₁ z₂, c' < G y₁ → ∀ y ∈ Ioo z₁ z₂, c' < G y := by
      intro z₁ z₂ hnz y₁ hy₁ hy₁gt y hy
      rcases lt_trichotomy (G y) c' with hlt2 | heq2 | hgt2
      · exfalso
        rcases lt_trichotomy y y₁ with hyy | rfl | hyy
        · obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo hyy.le hGcont.continuousOn
            (show c' ∈ Ioo (G y) (G y₁) from ⟨hlt2, hy₁gt⟩)
          exact hnz z ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hy₁.2⟩ hzval
        · exact absurd hy₁gt (not_lt.mpr hlt2.le)
        · obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo' hyy.le hGcont.continuousOn
            (show c' ∈ Ioo (G y) (G y₁) from ⟨hlt2, hy₁gt⟩)
          exact hnz z ⟨lt_trans hy₁.1 hz.1, lt_trans hz.2 hy.2⟩ hzval
      · exact absurd heq2 (hnz y hy)
      · exact hgt2
    -- Every super-level point has zeros of `G − c'` on both sides within the window.
    have hlevbelow : ∀ ψ : ℝ, ψ ∈ Ioo τ (τ + 2 * π) → c' < G ψ → ∃ z ∈ Zs, z < ψ := by
      intro ψ hψ hψgt
      obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo hψ.1.le hGcont.continuousOn
        (show c' ∈ Ioo (G τ) (G ψ) from ⟨hτlt, hψgt⟩)
      exact ⟨z, (hZmem z).mpr ⟨⟨hz.1.le, by linarith [hz.2, hψ.2]⟩, hzval⟩, hz.2⟩
    have hlevabove : ∀ ψ : ℝ, ψ ∈ Ioo τ (τ + 2 * π) → c' < G ψ → ∃ z ∈ Zs, ψ < z := by
      intro ψ hψ hψgt
      obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo' hψ.2.le hGcont.continuousOn
        (show c' ∈ Ioo (G (τ + 2 * π)) (G ψ) from ⟨hGτ2π, hψgt⟩)
      exact ⟨z, (hZmem z).mpr ⟨⟨by linarith [hz.1, hψ.1], hz.2.le⟩, hzval⟩, hz.1⟩
    -- The qualifying zero pairs and the attaining set `F`.
    set Q : Finset (ℝ × ℝ) :=
      (Zs ×ˢ Zs).filter (fun q => q.1 < q.2 ∧ ∀ y ∈ Ioo q.1 q.2, c' < G y) with hQdef
    set F : Set ℝ := ⋃ q ∈ Q, Icc q.1 q.2 with hFdef
    have hQprop : ∀ q ∈ Q, q.1 ∈ Zs ∧ q.2 ∈ Zs ∧ q.1 < q.2 ∧ ∀ y ∈ Ioo q.1 q.2, c' < G y := by
      intro q hq
      rw [hQdef, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
    have hFmeas : MeasurableSet F :=
      hFdef ▸ Q.measurableSet_biUnion (fun q _ => measurableSet_Icc)
    have hFmem : ∀ y : ℝ, y ∈ F ↔ ∃ q ∈ Q, y ∈ Icc q.1 q.2 := by
      intro y
      rw [hFdef]
      simp only [Set.mem_iUnion, exists_prop]
    -- The core super-level set and the two-sided sandwich for `F`.
    set S : Set ℝ := {ψ : ℝ | c' < G ψ} with hSdef
    have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hGcont.measurable
    have hFcore : S ∩ Ioo τ (τ + 2 * π) ⊆ F := by
      rintro ψ ⟨hψgt, hψI⟩
      rw [hSdef, mem_ofPred_eq] at hψgt
      obtain ⟨zb, hzbZ, hzblt⟩ := hlevbelow ψ hψI hψgt
      obtain ⟨za, hzaZ, hzagt⟩ := hlevabove ψ hψI hψgt
      have hbne : (Zs.filter (fun z => z < ψ)).Nonempty :=
        ⟨zb, Finset.mem_filter.mpr ⟨hzbZ, hzblt⟩⟩
      have hane : (Zs.filter (fun z => ψ < z)).Nonempty :=
        ⟨za, Finset.mem_filter.mpr ⟨hzaZ, hzagt⟩⟩
      set zl : ℝ := (Zs.filter (fun z => z < ψ)).max' hbne with hzldef
      set zr : ℝ := (Zs.filter (fun z => ψ < z)).min' hane with hzrdef
      have hzlmem := Finset.mem_filter.mp ((Zs.filter (fun z => z < ψ)).max'_mem hbne)
      have hzrmem := Finset.mem_filter.mp ((Zs.filter (fun z => ψ < z)).min'_mem hane)
      have hnolevel : ∀ y ∈ Ioo zl zr, G y ≠ c' := by
        intro y hy hyval
        have hyZs : y ∈ Zs := by
          refine (hZmem y).mpr ⟨⟨?_, ?_⟩, hyval⟩
          · exact le_trans ((hZmem zl).mp hzlmem.1).1.1 hy.1.le
          · exact le_trans hy.2.le ((hZmem zr).mp hzrmem.1).1.2
        rcases lt_trichotomy y ψ with h | h | h
        · exact absurd (Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hyZs, h⟩))
            (not_le.mpr hy.1)
        · exact absurd (h ▸ hyval).symm (ne_of_lt hψgt)
        · exact absurd (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyZs, h⟩))
            (not_le.mpr hy.2)
      have hqQ : (zl, zr) ∈ Q := by
        rw [hQdef, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hzlmem.1, hzrmem.1⟩, lt_trans hzlmem.2 hzrmem.2,
          hsign zl zr hnolevel ψ ⟨hzlmem.2, hzrmem.2⟩ hψgt⟩
      exact (hFmem ψ).mpr ⟨(zl, zr), hqQ, ⟨hzlmem.2.le, hzrmem.2.le⟩⟩
    have hFsub : F ⊆ (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ) := by
      intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hFmem y).mp hy
      obtain ⟨hq1, hq2, hqlt, hqpos⟩ := hQprop q hqQ
      rcases eq_or_lt_of_le hyq.1 with h1 | h1
      · exact Or.inr (Finset.mem_coe.mpr (h1 ▸ hq1))
      · rcases eq_or_lt_of_le hyq.2 with h2 | h2
        · exact Or.inr (Finset.mem_coe.mpr (h2 ▸ hq2))
        · refine Or.inl ⟨hqpos y ⟨h1, h2⟩, ?_, ?_⟩
          · exact lt_of_le_of_lt ((hZmem q.1).mp hq1).1.1 h1
          · exact lt_of_lt_of_le h2 ((hZmem q.2).mp hq2).1.2
    -- Periodic transfer of measure and integral from the `τ`-window to the standard window.
    have hshiftIoc : ∀ (f : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), f (x + 2 * π * n) = f x) →
        ∀ (n : ℤ) (a b : ℝ),
          (∫⁻ x in Ioc a b, f x) = ∫⁻ x in Ioc (a + 2 * π * n) (b + 2 * π * n), f x := by
      intro f hper n a b
      have hmp : MeasurePreserving (fun x : ℝ => x + 2 * π * (n : ℝ)) volume volume :=
        measurePreserving_add_right volume _
      have hkey2 := hmp.setLIntegral_comp_preimage_emb
        (measurableEmbedding_addRight (2 * π * (n : ℝ))) f
        (Ioc (a + 2 * π * (n : ℝ)) (b + 2 * π * (n : ℝ)))
      have hpre : (fun x : ℝ => x + 2 * π * (n : ℝ)) ⁻¹'
          Ioc (a + 2 * π * (n : ℝ)) (b + 2 * π * (n : ℝ)) = Ioc a b := by
        ext x
        simp only [mem_preimage, mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [hpre] at hkey2
      rw [← hkey2]
      exact lintegral_congr_ae (Filter.Eventually.of_forall (fun x => (hper n x).symm))
    have hperwin : ∀ (f : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), f (x + 2 * π * n) = f x) →
        (∫⁻ x in Ioc τ (τ + 2 * π), f x) = ∫⁻ x in Ioc 0 (2 * π), f x := by
      intro f hper
      set k : ℤ := ⌈τ / (2 * π)⌉ with hkdef
      have ha1 : τ ≤ 2 * π * k := by
        have h1 := Int.le_ceil (τ / (2 * π))
        rw [div_le_iff₀ hπpos] at h1
        linarith
      have ha2 : 2 * π * k ≤ τ + 2 * π := by
        have h1 := Int.ceil_lt_add_one (τ / (2 * π))
        have h2 : (k : ℝ) * (2 * π) < (τ / (2 * π) + 1) * (2 * π) :=
          mul_lt_mul_of_pos_right h1 hπpos
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hπpos), one_mul] at h2
        linarith
      set s₀ : ℝ := τ + 2 * π - 2 * π * k with hs₀def
      have hs₀0 : 0 ≤ s₀ := by rw [hs₀def]; linarith
      have hs₀2π : s₀ ≤ 2 * π := by rw [hs₀def]; linarith
      have hdisj1 : Disjoint (Ioc τ (2 * π * k)) (Ioc (2 * π * k) (τ + 2 * π)) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, h1⟩ ⟨h2, -⟩
        exact absurd h2 (not_lt.mpr h1)
      have hdisj2 : Disjoint (Ioc (0 : ℝ) s₀) (Ioc s₀ (2 * π)) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, h1⟩ ⟨h2, -⟩
        exact absurd h2 (not_lt.mpr h1)
      have hs1 : (∫⁻ x in Ioc τ (2 * π * k), f x) = ∫⁻ x in Ioc s₀ (2 * π), f x := by
        rw [hshiftIoc f hper (1 - k) τ (2 * π * k)]
        have he1 : τ + 2 * π * ((1 - k : ℤ) : ℝ) = s₀ := by push_cast; rw [hs₀def]; ring
        have he2 : 2 * π * k + 2 * π * ((1 - k : ℤ) : ℝ) = 2 * π := by push_cast; ring
        rw [he1, he2]
      have hs2 : (∫⁻ x in Ioc (2 * π * k) (τ + 2 * π), f x) = ∫⁻ x in Ioc 0 s₀, f x := by
        rw [hshiftIoc f hper (0 - k) (2 * π * k) (τ + 2 * π)]
        have he1 : 2 * π * k + 2 * π * ((0 - k : ℤ) : ℝ) = 0 := by push_cast; ring
        have he2 : τ + 2 * π + 2 * π * ((0 - k : ℤ) : ℝ) = s₀ := by push_cast; rw [hs₀def]; ring
        rw [he1, he2]
      calc (∫⁻ x in Ioc τ (τ + 2 * π), f x)
          = (∫⁻ x in Ioc τ (2 * π * k), f x) + ∫⁻ x in Ioc (2 * π * k) (τ + 2 * π), f x := by
            rw [← lintegral_union measurableSet_Ioc hdisj1, Ioc_union_Ioc_eq_Ioc ha1 ha2]
        _ = (∫⁻ x in Ioc s₀ (2 * π), f x) + ∫⁻ x in Ioc 0 s₀, f x := by rw [hs1, hs2]
        _ = (∫⁻ x in Ioc (0 : ℝ) s₀, f x) + ∫⁻ x in Ioc s₀ (2 * π), f x := add_comm _ _
        _ = ∫⁻ x in Ioc 0 (2 * π), f x := by
            rw [← lintegral_union measurableSet_Ioc hdisj2, Ioc_union_Ioc_eq_Ioc hs₀0 hs₀2π]
    have hSmemper : ∀ (n : ℤ) (x : ℝ), x + 2 * π * n ∈ S ↔ x ∈ S := by
      intro n x
      simp only [hSdef, mem_ofPred_eq, hGperZ]
    have hindper : ∀ (h : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), h (x + 2 * π * n) = h x) →
        ∀ (n : ℤ) (x : ℝ), S.indicator h (x + 2 * π * n) = S.indicator h x := by
      intro h hper n x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem ((hSmemper n x).mpr hx), Set.indicator_of_mem hx, hper]
      · rw [Set.indicator_of_notMem (fun hc => hx ((hSmemper n x).mp hc)),
          Set.indicator_of_notMem hx]
    have hindint : ∀ T : Set ℝ, (∫⁻ x in T, S.indicator g x) = ∫⁻ x in S ∩ T, g x := by
      intro T
      rw [lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas]
    have hindvol : ∀ T : Set ℝ,
        (∫⁻ x in T, S.indicator (fun _ => (1 : ℝ≥0∞)) x) = volume (S ∩ T) := by
      intro T
      rw [lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas, setLIntegral_one]
    have hIoo : (volume : Measure ℝ).restrict (Ioo τ (τ + 2 * π))
        = volume.restrict (Ioc τ (τ + 2 * π)) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
    have hIcc : (volume : Measure ℝ).restrict (Icc (0 : ℝ) (2 * π))
        = volume.restrict (Ioc (0 : ℝ) (2 * π)) := Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
    have hcorevol : volume (S ∩ Ioo τ (τ + 2 * π)) = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by
      rw [← hindvol (Ioo τ (τ + 2 * π)), ← hindvol (Icc (0 : ℝ) (2 * π))]
      calc (∫⁻ x in Ioo τ (τ + 2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x)
          = ∫⁻ x in Ioc τ (τ + 2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x := by rw [hIoo]
        _ = ∫⁻ x in Ioc 0 (2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x :=
            hperwin _ (hindper _ (fun n x => rfl))
        _ = ∫⁻ x in Icc (0 : ℝ) (2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x := by rw [hIcc]
    have hcoreint : (∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ)
        = ∫⁻ ψ in S ∩ Icc (0 : ℝ) (2 * π), g ψ := by
      rw [← hindint (Ioo τ (τ + 2 * π)), ← hindint (Icc (0 : ℝ) (2 * π))]
      calc (∫⁻ x in Ioo τ (τ + 2 * π), S.indicator g x)
          = ∫⁻ x in Ioc τ (τ + 2 * π), S.indicator g x := by rw [hIoo]
        _ = ∫⁻ x in Ioc 0 (2 * π), S.indicator g x := hperwin _ (hindper _ hgperZ)
        _ = ∫⁻ x in Icc (0 : ℝ) (2 * π), S.indicator g x := by rw [hIcc]
    -- Identify the standard-window core with the super-level set of `g`.
    have hident : {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} = S ∩ Icc (0 : ℝ) (2 * π) := by
      ext x
      simp only [mem_ofPred_eq, mem_inter_iff, hSdef]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hsuper_iff x).mp h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, (hsuper_iff x).mpr h1⟩
    have hZsnull : volume (Zs : Set ℝ) = 0 := Zs.countable_toSet.measure_zero _
    -- Volume of `F` is exactly `2θ`.
    have hFvol : volume F = ENNReal.ofReal (2 * θ) := by
      apply le_antisymm
      · calc volume F ≤ volume ((S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ)) := measure_mono hFsub
          _ ≤ volume (S ∩ Ioo τ (τ + 2 * π)) + volume (Zs : Set ℝ) := measure_union_le _ _
          _ = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by rw [hZsnull, add_zero, hcorevol]
          _ = ENNReal.ofReal (2 * θ) := by rw [← hident]; exact hsupvol
      · calc ENNReal.ofReal (2 * θ) = volume (S ∩ Ioo τ (τ + 2 * π)) := by
              rw [hcorevol, ← hident]; exact hsupvol.symm
          _ ≤ volume F := measure_mono hFcore
    -- Layer-cake attainment: the integral over the super-level core is the star value.
    have hEstar : (∫⁻ x in {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}, g x)
        = starFunction p u r θ := by
      have hkey : ∀ t : ℝ, volume {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
          = min (ENNReal.ofReal (2 * θ)) (distribFun (2 * π) g (ENNReal.ofReal t)) := by
        intro t
        rcases le_or_gt c (ENNReal.ofReal t) with hct | hct
        · have hset : {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
              = {x ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t < g x} := by
            ext x
            simp only [mem_ofPred_eq]
            constructor
            · rintro ⟨⟨hxI, -⟩, hlt2⟩; exact ⟨hxI, hlt2⟩
            · rintro ⟨hxI, hlt2⟩; exact ⟨⟨hxI, lt_of_le_of_lt hct hlt2⟩, hlt2⟩
          rw [hset]
          change distribFun (2 * π) g (ENNReal.ofReal t) = _
          rw [min_eq_right (le_trans (distribFun_antitone hct) hP1)]
        · have hset : {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
              = {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} := by
            ext x
            simp only [mem_ofPred_eq]
            constructor
            · rintro ⟨hx, -⟩; exact hx
            · intro hx; exact ⟨hx, lt_trans hct hx.2⟩
          rw [hset, hsupvol, min_eq_left (hlt _ hct).le]
      rw [show starFunction p u r θ = starProfile (2 * π) g θ from rfl,
        starProfile_eq_lintegral_min (by positivity) hθ0.le (by linarith),
        lintegral_eq_lintegral_meas_lt_ennreal hgmeas]
      exact lintegral_congr (fun t => hkey t)
    -- Integral of `g` over `F` equals the star value.
    have hFstar : (∫⁻ ψ in F, g ψ) = starFunction p u r θ := by
      have hup : (∫⁻ ψ in F, g ψ) ≤ ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ := by
        calc (∫⁻ ψ in F, g ψ)
            ≤ ∫⁻ ψ in (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ), g ψ := lintegral_mono_set hFsub
          _ ≤ (∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ) + ∫⁻ ψ in (Zs : Set ℝ), g ψ :=
              lintegral_union_le _ _ _
          _ = ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ := by
              rw [setLIntegral_measure_zero _ _ hZsnull, add_zero]
      have heq1 : (∫⁻ ψ in F, g ψ) = ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ :=
        le_antisymm hup (lintegral_mono_set hFcore)
      rw [heq1, hcoreint, ← hident, hEstar]
    -- Nonemptiness and the extremal endpoints.
    have hFne : F.Nonempty := by
      apply nonempty_of_measure_ne_zero (μ := volume)
      rw [hFvol]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    obtain ⟨y₀, hy₀F⟩ := hFne
    obtain ⟨qq, hqqQ, -⟩ := (hFmem y₀).mp hy₀F
    have hQne : Q.Nonempty := ⟨qq, hqqQ⟩
    have hZsne : Zs.Nonempty := ⟨qq.1, (hQprop qq hqqQ).1⟩
    have hminτ : τ < Zs.min' hZsne := by
      have hmem := (hZmem _).mp (Zs.min'_mem hZsne)
      rcases eq_or_lt_of_le hmem.1.1 with h | h
      · exact absurd (h ▸ hmem.2) (ne_of_lt hτlt)
      · exact h
    have hmaxτ : Zs.max' hZsne < τ + 2 * π := by
      have hmem := (hZmem _).mp (Zs.max'_mem hZsne)
      rcases eq_or_lt_of_le hmem.1.2 with h | h
      · exact absurd (h ▸ hmem.2) (ne_of_lt hGτ2π)
      · exact h
    have hFwin : F ⊆ Icc (Zs.min' hZsne) (Zs.max' hZsne) := by
      intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hFmem y).mp hy
      obtain ⟨h1, h2, -, -⟩ := hQprop q hqQ
      exact ⟨le_trans (Finset.min'_le _ _ h1) hyq.1, le_trans hyq.2 (Finset.le_max' _ _ h2)⟩
    have hfne : (Q.image Prod.fst).Nonempty := hQne.image _
    obtain ⟨q₀, hq₀Q, hq₀eq⟩ := Finset.mem_image.mp ((Q.image Prod.fst).min'_mem hfne)
    obtain ⟨hq₀1Z, hq₀2Z, hq₀lt, -⟩ := hQprop q₀ hq₀Q
    -- Assemble the slack `δ` and conclude.
    refine ⟨τ, min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1), F,
      lt_min (lt_min (by linarith) (by linarith)) (by linarith), hFmeas, ?_, hFvol,
      ⟨q₀.1, ⟨(hFmem q₀.1).mpr ⟨q₀, hq₀Q, ⟨le_rfl, hq₀lt.le⟩⟩, ?_⟩, ?_⟩, hFstar⟩
    · intro y hy
      have h := hFwin hy
      constructor
      · have hδ1 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
            ≤ Zs.min' hZsne - τ := le_trans (min_le_left _ _) (min_le_left _ _)
        linarith [h.1]
      · have hδ2 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
            ≤ τ + 2 * π - Zs.max' hZsne := le_trans (min_le_left _ _) (min_le_right _ _)
        linarith [h.2]
    · intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hFmem y).mp hy
      have hle : (Q.image Prod.fst).min' hfne ≤ q.1 :=
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hqQ, rfl⟩)
      rw [← hq₀eq] at hle
      linarith [hyq.1]
    · intro y hy
      refine (hFmem y).mpr ⟨q₀, hq₀Q, ⟨hy.1, ?_⟩⟩
      have hδ3 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
          ≤ q₀.2 - q₀.1 := min_le_right _ _
      linarith [hy.2]

end RiemannDynamics
