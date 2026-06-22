/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.SensePreserving
import RiemannDynamics.QC.ReverseLengthAreaForward
import RiemannDynamics.Analysis.Sobolev.Stepanov
import RiemannDynamics.Analysis.Sobolev.Coarea
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# A.e. differentiability of a geometric quasiconformal map (the direct metric / Stepanov route)

This file proves, **directly from the geometric definition and Stepanov's theorem**, that a
geometric `K`-quasiconformal map `f : ℂ → ℂ` is real-Fréchet-differentiable at almost every
point:

> `IsQCGeometric.ae_differentiableAt' : ∀ᵐ z, DifferentiableAt ℝ f z`.

This is an **independent route** to a.e. differentiability that does *not* pass through the
reverse-length-area / ACL machinery (`IsQCGeometric.reverseLengthArea_data` in
`QC/GeometricToAnalytic.lean`, which carries the large Gehring–Lehto `sorry`). Instead it uses
only the **finite-upper-metric-derivative** form of the Stepanov hypothesis.

## The classical chain

1. **Volume derivative finite a.e. (Lebesgue differentiation).** Since `f` is a homeomorphism
   (`SensePreserving.isHomeomorph`), the pushforward set function `B ↦ volume (f '' B)` is the
   honest Borel measure `ν = Measure.map f.symm volume`. It is locally finite (`f` continuous
   ⟹ `f '' compact` is compact, hence of finite volume). On the Besicovitch-covering space `ℂ`,
   Lebesgue differentiation (`Besicovitch.ae_tendsto_rnDeriv`) gives, for almost every `x`, that
   `ν (closedBall x r) / volume (closedBall x r) → ν.rnDeriv volume x`, and the limit is finite
   a.e. (`Measure.rnDeriv_lt_top`). So `ν (closedBall x r) ≲ r²` for all small `r`, a.e. `x`.

2. **QC roundness (`qc_image_ball_diam_sq_le_volume`, the single genuine QC residual).** For a
   geometric `K`-quasiconformal map,
   `(diam (f '' closedBall x r))² ≤ C(K) · volume (f '' closedBall x r)`:
   the image of a ball is "round", its squared diameter controlled by its area. This is the one
   genuinely two-dimensional quasiconformal estimate; it is isolated below as a single precise
   `sorry`. Its classical proof uses the modulus of a ring/annulus (Grötzsch / Teichmüller
   extremal estimates), which is **absent from both Mathlib and this repository** (the repository
   has the rectangle modulus `axisRect_modulus` but no ring-modulus or separating-continua
   estimate). See the docstring of `qc_image_ball_diam_sq_le_volume`.

3. **Combine.** For `y` with `ρ := ‖y − x‖` small, `‖f y − f x‖ ≤ diam (f '' closedBall x ρ)
   ≤ √(C · ν(closedBall x ρ)) ≲ √(C · M · π) · ρ = √(C · M · π) · ‖y − x‖`, where `M = rnDeriv + 1`.
   This is exactly the finite-upper-metric-derivative Stepanov hypothesis, and
   `RiemannDynamics.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top` finishes.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Real

namespace RiemannDynamics

/-! ## STEP 1 — elementary reduction of the ball to two concentric axis squares

The Euclidean closed ball `closedBall x r` sits between two concentric axis-aligned squares:
the inscribed square `qcInnerSquare x r` of half-side `r/√2` (its far corner lies exactly on the
circle of radius `r`) and the circumscribed square `qcOuterSquare x r` of half-side `r`. Since the
quasiconformal map `f` is a homeomorphism — in particular injective with continuous, hence compact,
images — these set inclusions transport to the images, and `Metric.diam`/`volume` are monotone
under inclusion. This reduces the ball roundness estimate to a roundness estimate comparing the
**diameter of the outer image square** with the **area of the inner image square**
(`qc_image_outerSquare_diam_sq_le_innerSquare_volume`). All lemmas of this section are elementary
plane geometry; they carry no quasiconformal content. -/

/-- The inscribed axis-aligned square of the ball `closedBall x r`: the closed axis square centred
at `x` with half-side `r/√2`. Its four corners lie on the circle of radius `r`, so it is contained
in the ball. -/
noncomputable def qcInnerSquare (x : ℂ) (r : ℝ) : Set ℂ :=
  axisRect (x.re - r / Real.sqrt 2) (x.re + r / Real.sqrt 2)
    (x.im - r / Real.sqrt 2) (x.im + r / Real.sqrt 2)

/-- The circumscribed axis-aligned square of the ball `closedBall x r`: the closed axis square
centred at `x` with half-side `r`. It contains the ball, since `|z.re − x.re| ≤ ‖z − x‖` and
`|z.im − x.im| ≤ ‖z − x‖`. -/
noncomputable def qcOuterSquare (x : ℂ) (r : ℝ) : Set ℂ :=
  axisRect (x.re - r) (x.re + r) (x.im - r) (x.im + r)

/-- **Inscribed square ⊆ ball.** Every point of the inner axis square (half-side `r/√2`) is within
distance `r` of the centre: `(z.re−x.re)² + (z.im−x.im)² ≤ (r/√2)² + (r/√2)² = r²`. -/
theorem qcInnerSquare_subset_closedBall (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    qcInnerSquare x r ⊆ Metric.closedBall x r := by
  intro z hz
  simp only [qcInnerSquare, axisRect, Set.mem_setOf_eq] at hz
  obtain ⟨⟨hre0, hre1⟩, him0, him1⟩ := hz
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  -- Coordinate bounds: `|z.re − x.re| ≤ r/√2` and `|z.im − x.im| ≤ r/√2`.
  have hreabs : |z.re - x.re| ≤ r / Real.sqrt 2 := by
    rw [abs_le]; constructor <;> linarith
  have himabs : |z.im - x.im| ≤ r / Real.sqrt 2 := by
    rw [abs_le]; constructor <;> linarith
  -- `(r/√2)² = r²/2`.
  have hhalf : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [Metric.mem_closedBall, Complex.dist_eq_re_im]
  rw [show √((z.re - x.re) ^ 2 + (z.im - x.im) ^ 2) ≤ r
      ↔ (z.re - x.re) ^ 2 + (z.im - x.im) ^ 2 ≤ r ^ 2 from Real.sqrt_le_left hr]
  have h1 : (z.re - x.re) ^ 2 ≤ r ^ 2 / 2 := by
    rw [← hhalf]; exact sq_le_sq' (by linarith [abs_le.1 hreabs]) (abs_le.1 hreabs).2
  have h2 : (z.im - x.im) ^ 2 ≤ r ^ 2 / 2 := by
    rw [← hhalf]; exact sq_le_sq' (by linarith [abs_le.1 himabs]) (abs_le.1 himabs).2
  linarith

/-- **Ball ⊆ circumscribed square.** For `z` in `closedBall x r`, both coordinate deviations are
bounded by `‖z − x‖ ≤ r`: `|z.re − x.re| ≤ ‖z − x‖` and `|z.im − x.im| ≤ ‖z − x‖`. -/
theorem closedBall_subset_qcOuterSquare (x : ℂ) (r : ℝ) :
    Metric.closedBall x r ⊆ qcOuterSquare x r := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  simp only [qcOuterSquare, axisRect, Set.mem_setOf_eq]
  have hre : |(z - x).re| ≤ ‖z - x‖ := Complex.abs_re_le_norm _
  have him : |(z - x).im| ≤ ‖z - x‖ := Complex.abs_im_le_norm _
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rw [abs_le] at hre him
  refine ⟨⟨by linarith [hre.1, hz], by linarith [hre.2, hz]⟩,
    by linarith [him.1, hz], by linarith [him.2, hz]⟩

/-- The inner square's image is contained in the ball's image (`f` need only be a map). -/
theorem image_qcInnerSquare_subset (f : ℂ → ℂ) (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    f '' qcInnerSquare x r ⊆ f '' Metric.closedBall x r :=
  Set.image_mono (qcInnerSquare_subset_closedBall x hr)

/-- The ball's image is contained in the outer square's image. -/
theorem image_closedBall_subset_qcOuterSquare (f : ℂ → ℂ) (x : ℂ) (r : ℝ) :
    f '' Metric.closedBall x r ⊆ f '' qcOuterSquare x r :=
  Set.image_mono (closedBall_subset_qcOuterSquare x r)

/-- The circumscribed square is contained in `closedBall x (2r)` (since `‖z − x‖ ≤ |z.re − x.re| +
|z.im − x.im| ≤ 2r`), hence is bounded; combined with closedness it is compact. -/
theorem isCompact_qcOuterSquare (x : ℂ) (r : ℝ) : IsCompact (qcOuterSquare x r) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · -- closed: an intersection of four closed coordinate half-planes.
    simp only [qcOuterSquare, axisRect, Set.setOf_and]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  · -- bounded: contained in `closedBall x (2r)`.
    refine (Metric.isBounded_closedBall (x := x) (r := 2 * r)).subset (fun z hz => ?_)
    simp only [qcOuterSquare, axisRect, Set.mem_setOf_eq] at hz
    obtain ⟨⟨hre0, hre1⟩, him0, him1⟩ := hz
    rw [Metric.mem_closedBall, Complex.dist_eq]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have hre : |z.re - x.re| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    have him : |z.im - x.im| ≤ r := abs_le.2 ⟨by linarith, by linarith⟩
    linarith

/-! ## STEP 2 — Rengel's inequality (the elementary length–area area lower bound)

The reduction above leaves the two-dimensional quasiconformal estimate: the squared diameter of
the **outer** image square is controlled by the area of the **inner** image square. We dissect it
into three pieces and prove the elementary one (**Rengel's inequality**) in full:

* **Rengel's inequality** (PROVEN below, `rengel_area_lower_bound`): for a curve family `Γ` whose
  curves connect two sets `A₁, A₂` at distance `≥ d` while staying inside a measurable region `R`,
  `d² · M(Γ) ≤ area(R)`. The proof is the admissible-density argument (template:
  `axisRect_modulus_upper_bound`): the density `(1/d)·𝟙_R` is admissible (each connecting curve
  has arc length `≥` chord `≥ d`), so `M(Γ) ≤ ∫ ρ² = area(R)/d²`. This turns a modulus *lower*
  bound into the area *lower* bound.

* **Modulus lower bound** (`square_imageCurveFamily_modulus_ge`, isolated TRUE residual): the image
  crossing family of an axis *square* has modulus `≥ 1/K`. This is the genuine extremal-length
  reciprocity wall.

* **Quasiround distortion** (`qc_quasiround_data`, isolated TRUE residual): the outer image square
  has diameter `≤ C(K) ·` (inner image side-distance), and the inner image sides are at positive
  distance. This is the genuine QC two-point-distortion wall.

The first piece is genuinely elementary; the latter two are the two-dimensional quasiconformal
content absent from Mathlib and this repository, isolated as precise TRUE residuals below. -/

/-- **Functional-increment ≤ arc length.** For an absolutely continuous curve `δ : ℝ → ℂ` on
`[0, 1]` and a real-linear continuous functional `L : ℂ →L[ℝ] ℝ` of operator norm `≤ 1`, the
increment `L(δ 1) − L(δ 0)` is at most the total arc length `∫₀¹ ‖δ'‖`. The projection inequality
`|L(δ')| ≤ ‖L‖ · ‖δ'‖ ≤ ‖δ'‖` integrated through the fundamental theorem of calculus for the
absolutely continuous real function `L ∘ δ`. (Generalizes `reIncrement_le_arcLength`, which is the
case `L = Complex.reCLM`.) -/
theorem funcIncrement_le_arcLength {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ENNReal.ofReal (L (δ 1) - L (δ 0))
      ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
  set g : ℝ → ℝ := fun t => L (δ t) with hg_def
  have hg_ac : AbsolutelyContinuousOnInterval g 0 1 := by
    have hl : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (k : NNReal),
        LipschitzWith k l → ∀ {a c : ℝ}, AbsolutelyContinuousOnInterval F a c →
        AbsolutelyContinuousOnInterval (fun t => l (F t)) a c := by
      intro F Y _ l k hl a c hF
      rw [absolutelyContinuousOnInterval_iff] at hF ⊢
      intro ε hε
      obtain ⟨δ', hδ', hδ''⟩ := hF (ε / (k + 1)) (by positivity)
      refine ⟨δ', hδ', fun E hE hlen => ?_⟩
      have key := hδ'' E hE hlen
      have hknn : (0 : ℝ) ≤ (k : ℝ) := k.coe_nonneg
      calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
          ≤ ∑ i ∈ Finset.range E.1, (k : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
            Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
        _ = (k : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
            rw [Finset.mul_sum]
        _ ≤ (k : ℝ) * (ε / (k + 1)) := mul_le_mul_of_nonneg_left key.le hknn
        _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hknn]
    exact hl L ‖L‖₊ L.lipschitz hδac
  have hg_int : IntervalIntegrable (deriv g) volume 0 1 := hg_ac.intervalIntegrable_deriv
  have hftc : ∫ t in (0:ℝ)..1, deriv g t = L (δ 1) - L (δ 0) := hg_ac.integral_deriv_eq_sub
  have hioc : ∫ t in (0:ℝ)..1, deriv g t = ∫ t in Set.Ioc (0:ℝ) 1, deriv g t :=
    intervalIntegral.integral_of_le (by norm_num)
  have hg_int' : IntegrableOn (deriv g) (Set.Ioc (0:ℝ) 1) volume := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hg_int
    exact hg_int
  have hbound1 : ENNReal.ofReal (L (δ 1) - L (δ 0))
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞) := by
    rw [← hftc, hioc]
    calc ENNReal.ofReal (∫ t in Set.Ioc (0:ℝ) 1, deriv g t)
        ≤ ENNReal.ofReal (∫ t in Set.Ioc (0:ℝ) 1, ‖deriv g t‖) := by
          apply ENNReal.ofReal_le_ofReal
          refine integral_mono hg_int' hg_int'.norm (fun t => ?_)
          exact Real.le_norm_self _
      _ = ∫⁻ t in Set.Ioc (0:ℝ) 1, ‖deriv g t‖ₑ := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hg_int']
      _ = ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞) := by
          apply lintegral_congr; intro t; rw [enorm_eq_nnnorm]
  have hδ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ t :=
    hδac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hbound2 : ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv g t‖₊ : ℝ≥0∞)
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hδ_diff] with t htdiff htmem
    have hd : DifferentiableAt ℝ δ t :=
      htdiff (Set.mem_uIcc.mpr (Or.inl (Set.Ioc_subset_Icc_self htmem)))
    have hderiv_g : deriv g t = L (deriv δ t) := by
      have hh : HasDerivAt g (L (deriv δ t)) t := by
        have := L.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt
        simpa [hg_def] using this
      exact hh.deriv
    rw [hderiv_g, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
    calc ‖L (deriv δ t)‖ ≤ ‖L‖ * ‖deriv δ t‖ := L.le_opNorm _
      _ ≤ 1 * ‖deriv δ t‖ := by gcongr
      _ = ‖deriv δ t‖ := one_mul _
  refine hbound1.trans (hbound2.trans ?_)
  exact lintegral_mono_set Set.Ioc_subset_Icc_self

/-- The norm-`≤ 1` functional realizing the norm of a complex number `w`: as a real-linear
continuous map `ℂ →L[ℝ] ℝ`, `v ↦ ‖w‖⁻¹ · Re(conj w · v)`. It sends `w` to `‖w‖` (so it witnesses
`‖w‖` as a `1`-Lipschitz projection), used to derive `chord_le_arcLength`. -/
noncomputable def normFunctional (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (‖w‖⁻¹ : ℝ) • (Complex.reCLM.comp
    ((ContinuousLinearMap.mul ℝ ℂ (starRingEnd ℂ w)).restrictScalars ℝ))

theorem normFunctional_apply (w v : ℂ) :
    normFunctional w v = ‖w‖⁻¹ * ((starRingEnd ℂ w) * v).re := by
  simp [normFunctional]

theorem normFunctional_self {w : ℂ} (hw : w ≠ 0) : normFunctional w w = ‖w‖ := by
  rw [normFunctional_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    show w.re * w.re - -w.im * w.im = Complex.normSq w by rw [Complex.normSq_apply]; ring,
    Complex.normSq_eq_norm_sq]
  field_simp

theorem norm_normFunctional_le (w : ℂ) : ‖normFunctional w‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [normFunctional_apply, one_mul]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_norm, inv_mul_le_iff₀ (by positivity)]
    calc |((starRingEnd ℂ w) * v).re| ≤ ‖(starRingEnd ℂ w) * v‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * ‖v‖ := by rw [norm_mul, RCLike.norm_conj]

/-- **Chord ≤ arc length.** For an absolutely continuous curve `δ : ℝ → ℂ` on `[0, 1]`, the
straight-line chord distance `‖δ 1 − δ 0‖` is at most the total arc length `∫₀¹ ‖δ'‖`. Obtained from
`funcIncrement_le_arcLength` with the `1`-Lipschitz functional `normFunctional (δ 1 − δ 0)`, which
sends the chord vector to its own norm. -/
theorem chord_le_arcLength {δ : ℝ → ℂ} (hδac : AbsolutelyContinuousOnInterval δ 0 1) :
    ENNReal.ofReal ‖δ 1 - δ 0‖
      ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, (‖deriv δ t‖₊ : ℝ≥0∞) := by
  rcases eq_or_ne (δ 1 - δ 0) 0 with hz | hz
  · rw [hz, norm_zero, ENNReal.ofReal_zero]; exact zero_le _
  · set w : ℂ := δ 1 - δ 0 with hw
    have hkey := funcIncrement_le_arcLength hδac (normFunctional w) (norm_normFunctional_le w)
    have hval : normFunctional w (δ 1) - normFunctional w (δ 0) = ‖w‖ := by
      rw [← map_sub, ← hw, normFunctional_self hz]
    rwa [hval] at hkey

/-- The **Rengel density** `(1/d)·𝟙_R` is admissible for any curve family `Γ` whose curves connect
two sets `A₁, A₂` at distance `≥ d` while staying inside the measurable region `R`. The
admissibility computation: along each curve the indicator is `1`, so its arc-length line integral is
`(1/d) · ∫ ‖δ'‖ ≥ (1/d) · ‖δ 1 − δ 0‖ ≥ (1/d) · d = 1`, using `chord_le_arcLength` and that
endpoints lie at distance `≥ d`. The template is `axisRectDensity_admissible`. -/
theorem rengelDensity_admissible {R : Set ℂ} (hRmeas : MeasurableSet R)
    {A₁ A₂ : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hdist : ∀ p ∈ A₁, ∀ q ∈ A₂, d ≤ dist p q)
    {Γ : Set (ℝ → ℂ)}
    (hΓ : ∀ δ ∈ Γ, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ A₁ ∧ δ 1 ∈ A₂ ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ R) :
    IsAdmissibleDensity (R.indicator (fun _ => ENNReal.ofReal (1 / d))) Γ := by
  refine ⟨Measurable.indicator measurable_const hRmeas, ?_⟩
  intro δ hδ
  obtain ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩ := hΓ δ hδ
  have harc : arcLengthLineIntegral (R.indicator (fun _ => ENNReal.ofReal (1 / d))) δ
      = ENNReal.ofReal (1 / d) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv δ u‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only
    rw [Set.indicator_of_mem (hδimg u hu)]
  rw [harc]
  have hchord : ENNReal.ofReal d ≤ ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv δ u‖₊ : ℝ≥0∞) := by
    have hdle : d ≤ ‖δ 1 - δ 0‖ := by
      rw [← dist_eq_norm, dist_comm]; exact hdist (δ 0) hδ0 (δ 1) hδ1
    exact le_trans (ENNReal.ofReal_le_ofReal hdle) (chord_le_arcLength hδac)
  calc (1 : ℝ≥0∞)
      = ENNReal.ofReal (1 / d) * ENNReal.ofReal d := by
        rw [← ENNReal.ofReal_mul (by positivity), one_div,
          inv_mul_cancel₀ (ne_of_gt hd), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (1 / d) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv δ u‖₊ : ℝ≥0∞) := by gcongr

/-- **Rengel's inequality (area lower bound).** For a curve family `Γ` whose curves connect two sets
`A₁, A₂` at distance `≥ d` while staying inside the measurable region `R`,
`d² · M(Γ) ≤ area(R)`. The admissible Rengel density `(1/d)·𝟙_R` bounds `M(Γ) ≤ area(R)/d²`;
clearing denominators gives the area lower bound. This is the length–area / extremal-length module
estimate, in the form that converts a modulus *lower* bound into an area *lower* bound. -/
theorem rengel_area_lower_bound {R : Set ℂ} (hRmeas : MeasurableSet R)
    {A₁ A₂ : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hdist : ∀ p ∈ A₁, ∀ q ∈ A₂, d ≤ dist p q)
    {Γ : Set (ℝ → ℂ)}
    (hΓ : ∀ δ ∈ Γ, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ A₁ ∧ δ 1 ∈ A₂ ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ R) :
    ENNReal.ofReal (d ^ 2) * curveModulus Γ ≤ volume R := by
  set ρ₀ : ℂ → ℝ≥0∞ := R.indicator (fun _ => ENNReal.ofReal (1 / d)) with hρ₀
  have hadm := rengelDensity_admissible hRmeas hd hdist hΓ
  have hmod_le : curveModulus Γ ≤ ∫⁻ z, (ρ₀ z) ^ 2 := iInf₂_le ρ₀ hadm
  have henergy : ∫⁻ z, (ρ₀ z) ^ 2 = ENNReal.ofReal (1 / d ^ 2) * volume R := by
    have hsq : (fun z => (ρ₀ z) ^ 2)
        = R.indicator (fun _ => ENNReal.ofReal (1 / d) ^ 2) := by
      funext z; rw [hρ₀]; by_cases hz : z ∈ R <;> simp [hz]
    have hscalar : ENNReal.ofReal (1 / d) ^ 2 = ENNReal.ofReal (1 / d ^ 2) := by
      rw [← ENNReal.ofReal_pow (by positivity), div_pow, one_pow]
    rw [hsq, lintegral_indicator hRmeas, setLIntegral_const, hscalar, mul_comm]
  rw [henergy] at hmod_le
  calc ENNReal.ofReal (d ^ 2) * curveModulus Γ
      ≤ ENNReal.ofReal (d ^ 2) * (ENNReal.ofReal (1 / d ^ 2) * volume R) := by gcongr
    _ = volume R := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          mul_one_div, div_self (by positivity), ENNReal.ofReal_one, one_mul]

/-! ## STEP 3 — the two genuine quasiconformal residuals

After Rengel, two genuinely two-dimensional quasiconformal estimates remain, both absent from
Mathlib and this repository. Each is isolated below as a single precise `sorry` whose statement is
**TRUE** and whose precise missing classical ingredient is named. -/

/-! ### The conjugate (swapped) square and modulus reciprocity

The modulus *lower* bound `M(Γ) ≥ 1/K` for the image crossing family `Γ` of a square is obtained
from **modulus reciprocity**: a square has two *conjugate* families — the crossing family `Γ`
(left ↔ right) and the separating family `Γ*` (bottom ↔ top). For their `f`-images one has the
reciprocity `M(Γ) · M(Γ*) ≥ 1`, and the geometric upper bound applied to the *swapped* square gives
`M(Γ*) ≤ K · 1 = K`; combining, `M(Γ) ≥ 1/M(Γ*) ≥ 1/K`.

The conjugate family `Γ*` is realized as the image crossing family of the **swapped** square
`axisRectQuadrilateralSwap`, whose left/right sides are the bottom/top of the rectangle. Its modulus
*upper* bound — all we need to instantiate `M(Γ*) ≤ K` — is the swapped analogue of
`axisRect_modulus_upper_bound` and is proved in full below (the admissible density
`(1/(t−s))·𝟙_R`, with the imaginary-part projection inequality
`funcIncrement_le_arcLength … Complex.imCLM`). The one genuinely two-dimensional input that remains
is the reciprocity inequality itself, isolated as the precise residual
`conjugateImageModulus_reciprocity` (its docstring names the absent classical ingredient). -/

/-- The **swapped** axis-rectangle quadrilateral: the parametrization
`⟨x, y⟩ ↦ ⟨a + (b−a)·y, s + (t−s)·x⟩` of the unit square onto `[a, b] × [s, t]`, i.e. the standard
`axisRectMap` precomposed with the coordinate swap `Prod.swap`. Its **left** side is the *bottom*
edge `[a, b] × {s}`, its **right** side is the *top* edge `[a, b] × {t}`, and its image region is
the same rectangle `[a, b] × [s, t]`. Its connecting (crossing) family is therefore the *separating*
(bottom ↔ top) family of the rectangle — the conjugate of the standard crossing family. -/
noncomputable def axisRectQuadrilateralSwap (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    Quadrilateral where
  toFun := axisRectMap a b s t ∘ Prod.swap
  continuous_toFun := (axisRectMap_continuous a b s t).comp continuous_swap
  injOn_unitSquare := by
    intro p hp q hq h
    have hswap : unitSquare = Prod.swap ⁻¹' unitSquare := by
      ext w; simp only [unitSquare, Set.mem_preimage, Set.mem_prod, Prod.fst_swap, Prod.snd_swap]
      exact and_comm
    have hps : Prod.swap p ∈ unitSquare := by rw [hswap] at hp; exact hp
    have hqs : Prod.swap q ∈ unitSquare := by rw [hswap] at hq; exact hq
    have := axisRectMap_injOn hab hst hps hqs h
    exact Prod.swap_injective this

@[simp] theorem axisRectQuadrilateralSwap_toFun (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).toFun = axisRectMap a b s t ∘ Prod.swap := rfl

/-- The image region of the swapped rectangle quadrilateral is the same rectangle `[a, b] × [s, t]`
as the unswapped one: the coordinate swap is a bijection of the unit square. -/
theorem axisRectQuadrilateralSwap_image {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).image
      = (axisRectQuadrilateral a b s t hab hst).image := by
  rw [Quadrilateral.image, Quadrilateral.image, axisRectQuadrilateralSwap_toFun,
    axisRectQuadrilateral_toFun, Set.image_comp]
  congr 1
  -- `swap '' unitSquare = unitSquare`, since `swap` is a self-bijection of the (symmetric) square.
  rw [unitSquare, Set.image_swap_prod]

/-- The left side of the swapped rectangle is its *bottom* edge `{z | s ≤ z.im, z.re ∈ [a, b],
z.im = s}`. -/
theorem axisRectQuadrilateralSwap_leftSide {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).leftSide
      = {z : ℂ | z.im = s ∧ (a ≤ z.re ∧ z.re ≤ b)} := by
  have hbma : (0:ℝ) < b - a := by linarith
  ext z
  simp only [Quadrilateral.leftSide, axisRectQuadrilateralSwap_toFun, Function.comp_apply,
    axisRectMap, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_setOf_eq,
    Prod.fst_swap, Prod.snd_swap, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨rfl, hx0, hx1⟩, rfl⟩
    refine ⟨by dsimp only [Complex.im]; ring, ?_, ?_⟩ <;>
      dsimp only [Complex.re] <;> nlinarith
  · rintro ⟨him, hre0, hre1⟩
    refine ⟨0, (z.re - a)/(b - a), ⟨rfl, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hbma.le
    · rw [div_le_one hbma]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im]
      · field_simp; ring
      · rw [mul_zero, add_zero]; exact him.symm

/-- The right side of the swapped rectangle is its *top* edge `{z | z.im = t, z.re ∈ [a, b]}`. -/
theorem axisRectQuadrilateralSwap_rightSide {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).rightSide
      = {z : ℂ | z.im = t ∧ (a ≤ z.re ∧ z.re ≤ b)} := by
  have hbma : (0:ℝ) < b - a := by linarith
  ext z
  simp only [Quadrilateral.rightSide, axisRectQuadrilateralSwap_toFun, Function.comp_apply,
    axisRectMap, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc, Set.mem_setOf_eq,
    Prod.fst_swap, Prod.snd_swap, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨rfl, hx0, hx1⟩, rfl⟩
    refine ⟨by dsimp only [Complex.im]; ring, ?_, ?_⟩ <;>
      dsimp only [Complex.re] <;> nlinarith
  · rintro ⟨him, hre0, hre1⟩
    refine ⟨1, (z.re - a)/(b - a), ⟨rfl, ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) hbma.le
    · rw [div_le_one hbma]; linarith
    · apply Complex.ext <;> dsimp only [Complex.re, Complex.im]
      · field_simp; ring
      · rw [mul_one]; linarith [him]

/-- The constant density `(1/(t−s))·𝟙_R` on the rectangle is **admissible** for the swapped
(bottom ↔ top) connecting family: every absolutely continuous curve from the bottom side to the top
side staying in the rectangle has imaginary-part increment `t − s ≤` its arc length (the projection
inequality `funcIncrement_le_arcLength` with the norm-`1` functional `Complex.imCLM`), so its
arc-length line integral is `≥ (1/(t−s))·(t−s) = 1`. This is the swapped analogue of
`axisRectDensity_admissible`. -/
theorem axisRectDensitySwap_admissible {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    IsAdmissibleDensity
      ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))))
      (axisRectQuadrilateralSwap a b s t hab hst).curveFamily := by
  have htms : (0:ℝ) < t - s := by linarith
  refine ⟨Measurable.indicator measurable_const (measurableSet_axisRect a b s t), ?_⟩
  rintro γ ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩
  -- The endpoints lie on the bottom/top sides: `Im(γ 0) = s`, `Im(γ 1) = t`.
  rw [axisRectQuadrilateralSwap_leftSide] at hγ0
  rw [axisRectQuadrilateralSwap_rightSide] at hγ1
  obtain ⟨hγ0im, _⟩ := hγ0
  obtain ⟨hγ1im, _⟩ := hγ1
  -- On `[0, 1]`, `γ t` is in the rectangle, so the density there is `ofReal (1/(t−s))`.
  have hγimg' : ∀ u ∈ Set.Icc (0:ℝ) 1, γ u ∈ axisRect a b s t := by
    intro u hu
    have hmem := hγimg u hu
    rw [axisRectQuadrilateralSwap_image, axisRectQuadrilateral_image] at hmem
    exact hmem
  have hργ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      (axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))) (γ u)
        = ENNReal.ofReal (1 / (t - s)) := by
    intro u hu
    rw [Set.indicator_of_mem (hγimg' u hu)]
  have harc : arcLengthLineIntegral
      ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s)))) γ
      = ENNReal.ofReal (1 / (t - s)) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    simp only
    rw [hργ u hu]
  rw [harc]
  -- Imaginary-part increment `t − s ≤ ∫⁻ ‖γ'‖`, so the product is `≥ 1`.
  have hincr : ENNReal.ofReal (t - s)
      ≤ ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
    have hnorm : ‖Complex.imCLM‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa only [Complex.imCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_im_le_norm v
    have := funcIncrement_le_arcLength hγac Complex.imCLM hnorm
    rwa [show Complex.imCLM (γ 1) = (γ 1).im from rfl,
      show Complex.imCLM (γ 0) = (γ 0).im from rfl, hγ1im, hγ0im] at this
  calc (1 : ℝ≥0∞)
      = ENNReal.ofReal (1 / (t - s)) * ENNReal.ofReal (t - s) := by
        rw [← ENNReal.ofReal_mul (by positivity), one_div,
          inv_mul_cancel₀ (by linarith : (t - s) ≠ 0), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (1 / (t - s)) * ∫⁻ u in Set.Icc (0:ℝ) 1, (‖deriv γ u‖₊ : ℝ≥0∞) := by
        gcongr

/-- **Modulus upper bound for the swapped rectangle.** The swapped (bottom ↔ top) family has modulus
at most `(b − a)/(t − s)`: the admissible density `(1/(t−s))·𝟙_R` has energy
`∫⁻ ρ² = area(R)/(t−s)² = (b−a)/(t−s)`. (For a *square* `b − a = t − s` this gives `≤ 1`.) -/
theorem axisRectSwap_modulus_upper_bound {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    (axisRectQuadrilateralSwap a b s t hab hst).modulus
      ≤ ENNReal.ofReal ((b - a) / (t - s)) := by
  have hbma : (0:ℝ) < b - a := by linarith
  have htms : (0:ℝ) < t - s := by linarith
  have henergy : ∫⁻ z, ((axisRect a b s t).indicator
        (fun _ => ENNReal.ofReal (1 / (t - s))) z) ^ 2
      = ENNReal.ofReal ((b - a) / (t - s)) := by
    have hsq : (fun z => ((axisRect a b s t).indicator
          (fun _ => ENNReal.ofReal (1 / (t - s))) z) ^ 2)
        = (axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s)) ^ 2) := by
      funext z; by_cases hz : z ∈ axisRect a b s t <;> simp [hz]
    rw [hsq, lintegral_indicator (measurableSet_axisRect a b s t), setLIntegral_const,
      volume_axisRect a b s t]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, inv_pow]
    field_simp
  unfold Quadrilateral.modulus curveModulus
  calc ⨅ ρ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ
          (axisRectQuadrilateralSwap a b s t hab hst).curveFamily}, ∫⁻ z, (ρ z) ^ 2
      ≤ ∫⁻ z, ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))) z) ^ 2 :=
        iInf₂_le ((axisRect a b s t).indicator (fun _ => ENNReal.ofReal (1 / (t - s))))
          (axisRectDensitySwap_admissible hab hst)
    _ = ENNReal.ofReal ((b - a) / (t - s)) := henergy

/-! ### Reduction of conjugate-image reciprocity to the per-density length–area inequality

The reciprocity `1 ≤ M(Γ) · M(Γ*)` is the infimum, over admissible density pairs `(ρ, σ)`, of the
**per-pair** length–area inequality `1 ≤ (∫∫ ρ²) · (∫∫ σ²)`. We make this reduction sound and
explicit: the `curveModulus`/`iInf` wrappers and all the `ℝ≥0∞` finiteness bookkeeping are
discharged below (an `ℝ≥0∞` lemma `one_le_biInf_mul_biInf'` plus finiteness witnesses for the two
image families via Rengel densities), leaving the *single* genuinely two-dimensional residual
`imageConjugate_lengthArea_pairwise` (the per-pair inequality), whose proof is the co-area /
length–area decomposition over the image foliation that is absent from Mathlib and this repository.

Crucially, the naïve route "Cauchy–Schwarz `(∫∫ ρσ)² ≤ (∫∫ ρ²)(∫∫ σ²)` then `∫∫ ρσ ≥ 1` then `inf`
over independent `ρ, σ`" is **unsound**: `∫∫ ρσ ≥ 1` is *false* for arbitrary admissible pairs
(it holds only at the extremal pair; the perturbation `ρ = 1 + a(x)`, `σ = 1 + b(y)` with
`∫ a = ∫ b = 0` keeps `ρ, σ` admissible while making `∫∫ ρσ` drop below `1` once the perturbations
are correlated across the two constraints). The per-pair *product* inequality
`1 ≤ (∫∫ ρ²)(∫∫ σ²)` does hold for every admissible pair and is exactly equivalent (via the
infimum) to the goal, so it is the honest atomic residual. -/

/-- **Positive uniform separation of two disjoint nonempty compacta.** In a metric space, two
disjoint nonempty compact sets `A`, `B` are at a uniform positive distance: there is `d > 0` with
`d ≤ dist p q` for all `p ∈ A`, `q ∈ B`. The witness is `d = min over A of infDist · B`, positive
because the (closed) `B` does not meet the point of `A` realizing the minimum. -/
theorem exists_pos_setSeparation_of_disjoint_compact {α : Type*} [MetricSpace α] {A B : Set α}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ A, ∀ q ∈ B, d ≤ dist p q := by
  have hcont : Continuous (fun p => Metric.infDist p B) := continuous_infDist_pt B
  obtain ⟨p₀, hp₀A, hp₀min⟩ := hA.exists_isMinOn hAne hcont.continuousOn
  refine ⟨Metric.infDist p₀ B, ?_, ?_⟩
  · rw [← hB.isClosed.notMem_iff_infDist_pos hBne]
    intro hp₀B; exact (hdisj.ne_of_mem hp₀A hp₀B) rfl
  · intro p hpA q hqB
    exact (hp₀min hpA).trans (Metric.infDist_le_dist_of_mem hqB)

/-- **Reduction lemma (`ℝ≥0∞` arithmetic).** If every pair `(ρ, σ)` from two index sets `I`, `J`
satisfies `1 ≤ g ρ · h σ`, the set `I` has a member with `g`-value in `(0, ∞)`, and `J` is
nonempty with a member of finite `h`-value, then `1 ≤ (⨅_{ρ∈I} g ρ) · (⨅_{σ∈J} h σ)`.

This is the sound passage from the per-pair inequality to the product of infima. The finiteness
side conditions are what rules out the degenerate `0 · ∞` failures: a finite nonzero `g ρ₀`
together with the per-pair bound forces `⨅ h > 0`, and a finite `h σ₀` bounds `⨅ h < ∞`, after
which `(⨅ h)⁻¹ ≤ ⨅ g` gives the product `≥ 1`. (All edge cases `g ρ = ∞`, `⨅ h ∈ {0, ∞}` are
handled.) -/
theorem one_le_biInf_mul_biInf' {ιS ιT : Type*} {I : Set ιS} {J : Set ιT}
    (g : ιS → ℝ≥0∞) (h : ιT → ℝ≥0∞)
    (hSfin : ∃ ρ₀ ∈ I, g ρ₀ ≠ 0 ∧ g ρ₀ ≠ ⊤)
    (hTne : J.Nonempty) (hTtop : ∃ σ₀ ∈ J, h σ₀ ≠ ⊤)
    (hpair : ∀ ρ ∈ I, ∀ σ ∈ J, 1 ≤ g ρ * h σ) :
    1 ≤ (⨅ ρ ∈ I, g ρ) * (⨅ σ ∈ J, h σ) := by
  obtain ⟨ρ₀, hρ₀I, hρ₀0, hρ₀top⟩ := hSfin
  obtain ⟨σt, hσtJ, hσttop⟩ := hTtop
  obtain ⟨σn, hσnJ⟩ := hTne
  set A := ⨅ ρ ∈ I, g ρ with hAdef
  set B := ⨅ σ ∈ J, h σ with hBdef
  have hBtop : B ≠ ⊤ := ne_top_of_le_ne_top hσttop (biInf_le _ hσtJ)
  have hB0 : B ≠ 0 := by
    have hle : (g ρ₀)⁻¹ ≤ B := by
      apply le_iInf₂; intro σ hσ
      rw [ENNReal.inv_le_iff_le_mul (fun _ => hρ₀0) (fun hh => absurd hh hρ₀top)]
      exact hpair ρ₀ hρ₀I σ hσ
    exact (lt_of_lt_of_le (ENNReal.inv_pos.mpr hρ₀top) hle).ne'
  have hxB : ∀ ρ ∈ I, 1 ≤ g ρ * B := by
    intro ρ hρI
    have hx0 : g ρ ≠ 0 := by
      rintro hh; have := hpair _ hρI σn hσnJ; rw [hh, zero_mul] at this; simp at this
    have hxinv_le : (g ρ)⁻¹ ≤ B := by
      apply le_iInf₂; intro σ hσJ
      rcases eq_or_ne (g ρ) ⊤ with hgtop | hgtop
      · rw [hgtop]; simp
      · rw [ENNReal.inv_le_iff_le_mul (fun _ => hx0) (fun hh => absurd hh hgtop)]
        exact hpair ρ hρI σ hσJ
    rcases eq_or_ne (g ρ) ⊤ with hgtop | hgtop
    · rw [hgtop, ENNReal.top_mul hB0]; exact le_top
    · calc (1:ℝ≥0∞) = g ρ * (g ρ)⁻¹ := (ENNReal.mul_inv_cancel hx0 hgtop).symm
        _ ≤ g ρ * B := by gcongr
  have hkey : B⁻¹ ≤ A := by
    apply le_iInf₂; intro ρ hρI
    rw [ENNReal.inv_le_iff_le_mul (fun _ => hB0) (fun hh => absurd hh hBtop), mul_comm]
    exact hxB ρ hρI
  calc (1:ℝ≥0∞) = B * B⁻¹ := (ENNReal.mul_inv_cancel hB0 hBtop).symm
    _ ≤ B * A := by gcongr
    _ = A * B := mul_comm _ _

/-- **Finiteness witness for the image connecting family.** For a homeomorphism `f` and a
quadrilateral `Q` whose image region `f''Q.image` has positive (necessarily finite, by compactness)
volume and whose two image sides are disjoint, the Rengel density `(1/d)·𝟙_{f''image}` (with `d`
the positive separation of the disjoint compact image sides) is an admissible density for
`Q.imageCurveFamily f` of finite, nonzero energy `∫∫ ρ₀² = (1/d²)·volume(f''image) ∈ (0, ∞)`. (If
the image right side is empty the connecting family is empty and the unweighted indicator of
`f''image` is vacuously admissible with the same finite, nonzero energy.) -/
theorem imageCurveFamily_finiteWitness {f : ℂ → ℂ} (hf : IsHomeomorph f) (Q : Quadrilateral)
    (hposvol : 0 < volume (f '' Q.image))
    (hdisj : Disjoint (f '' Q.leftSide) (f '' Q.rightSide)) (hneL : Q.leftSide.Nonempty) :
    ∃ ρ₀ ∈ {ρ : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ (Q.imageCurveFamily f)},
      (∫⁻ z, (ρ₀ z) ^ 2) ≠ 0 ∧ (∫⁻ z, (ρ₀ z) ^ 2) ≠ ⊤ := by
  have hfc : Continuous f := hf.continuous
  have hsqcpt : IsCompact (unitSquare : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hQimgcpt : IsCompact (Q.image) := hsqcpt.image Q.continuous_toFun
  have hfQimgcpt : IsCompact (f '' Q.image) := hQimgcpt.image hfc
  have hRmeas : MeasurableSet (f '' Q.image) := hfQimgcpt.measurableSet
  have hRfin : volume (f '' Q.image) ≠ ⊤ := hfQimgcpt.measure_lt_top.ne
  have hcptL : IsCompact (Q.leftSide) := by
    unfold Quadrilateral.leftSide
    exact (isCompact_singleton.prod isCompact_Icc).image Q.continuous_toFun
  have hcptR : IsCompact (Q.rightSide) := by
    unfold Quadrilateral.rightSide
    exact (isCompact_singleton.prod isCompact_Icc).image Q.continuous_toFun
  have hcptfL : IsCompact (f '' Q.leftSide) := hcptL.image hfc
  have hcptfR : IsCompact (f '' Q.rightSide) := hcptR.image hfc
  have hnefL : (f '' Q.leftSide).Nonempty := hneL.image f
  by_cases hneR : (f '' Q.rightSide).Nonempty
  · obtain ⟨d, hd, hdist⟩ :=
      exists_pos_setSeparation_of_disjoint_compact hcptfL hcptfR hnefL hneR hdisj
    set ρ₀ : ℂ → ℝ≥0∞ := (f '' Q.image).indicator (fun _ => ENNReal.ofReal (1 / d)) with hρ₀
    have hΓ : ∀ δ ∈ Q.imageCurveFamily f, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
        δ 0 ∈ f '' Q.leftSide ∧ δ 1 ∈ f '' Q.rightSide ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1, δ u ∈ f '' Q.image := fun δ hδ => hδ
    have henergy : ∫⁻ z, (ρ₀ z) ^ 2 = ENNReal.ofReal (1 / d ^ 2) * volume (f '' Q.image) := by
      have hsq : (fun z => (ρ₀ z) ^ 2)
          = (f '' Q.image).indicator (fun _ => ENNReal.ofReal (1 / d) ^ 2) := by
        funext z; rw [hρ₀]; by_cases hz : z ∈ f '' Q.image <;> simp [hz]
      have hscalar : ENNReal.ofReal (1 / d) ^ 2 = ENNReal.ofReal (1 / d ^ 2) := by
        rw [← ENNReal.ofReal_pow (by positivity), div_pow, one_pow]
      rw [hsq, lintegral_indicator hRmeas, setLIntegral_const, hscalar, mul_comm]
    refine ⟨ρ₀, rengelDensity_admissible hRmeas hd hdist hΓ, ?_, ?_⟩
    · rw [henergy]
      exact mul_ne_zero
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) hposvol.ne'
    · rw [henergy]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRfin
  · have hempty : Q.imageCurveFamily f = ∅ := by
      ext δ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, _, _, hδ1, _⟩; exact hneR ⟨δ 1, hδ1⟩
    set ρ₀ : ℂ → ℝ≥0∞ := (f '' Q.image).indicator (fun _ => 1) with hρ₀
    have hadm : IsAdmissibleDensity ρ₀ (Q.imageCurveFamily f) := by
      refine ⟨Measurable.indicator measurable_const hRmeas, ?_⟩
      rw [hempty]; intro δ hδ; exact absurd hδ (Set.notMem_empty δ)
    have henergy : ∫⁻ z, (ρ₀ z) ^ 2 = volume (f '' Q.image) := by
      have hsq : (fun z => (ρ₀ z) ^ 2) = (f '' Q.image).indicator (fun _ => (1:ℝ≥0∞)) := by
        funext z; rw [hρ₀]; by_cases hz : z ∈ f '' Q.image <;> simp [hz]
      rw [hsq, lintegral_indicator hRmeas, setLIntegral_const, one_mul]
    exact ⟨ρ₀, hadm, by rw [henergy]; exact hposvol.ne', by rw [henergy]; exact hRfin⟩

/-- **Positive volume of the image of an axis rectangle quadrilateral** under a homeomorphism `f`.
The open box `(a, b) × (s, t) ⊆ Q.image` maps (via the open map `f`) to a nonempty open set inside
`f''Q.image`, which therefore has positive measure. -/
theorem image_axisRectQuadrilateral_volume_pos {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    0 < volume (f '' (axisRectQuadrilateral a b s t hab hst).image) := by
  set Q := axisRectQuadrilateral a b s t hab hst
  set U : Set ℂ := {z : ℂ | (a < z.re ∧ z.re < b) ∧ (s < z.im ∧ z.im < t)} with hU
  have hUopen : IsOpen U := by
    have hUeq : U = {z : ℂ | a < z.re ∧ z.re < b} ∩ {z : ℂ | s < z.im ∧ z.im < t} := by
      ext z; simp [hU, and_assoc]
    rw [hUeq]
    exact ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hUsub : U ⊆ Q.image := by
    rw [show Q.image = _ from axisRectQuadrilateral_image hab hst]
    rintro z ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
  have hUne : U.Nonempty :=
    ⟨Complex.mk ((a + b) / 2) ((s + t) / 2), by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [Complex.re, Complex.im] <;> linarith⟩
  calc (0 : ℝ≥0∞) < volume (f '' U) := (hf.isOpenMap U hUopen).measure_pos _ (hUne.image f)
    _ ≤ volume (f '' Q.image) := measure_mono (Set.image_mono hUsub)

/-- The standard axis-rectangle quadrilateral's image left/right sides are disjoint under `f`, and
the left side is nonempty. The source sides lie on `{re = a}`, `{re = b}` (disjoint as `a ≠ b`); `f`
injective transports the disjointness. -/
theorem image_axisRectQuadrilateral_sides_disjoint {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    Disjoint (f '' (axisRectQuadrilateral a b s t hab hst).leftSide)
        (f '' (axisRectQuadrilateral a b s t hab hst).rightSide) ∧
      (axisRectQuadrilateral a b s t hab hst).leftSide.Nonempty := by
  set Q := axisRectQuadrilateral a b s t hab hst
  have hdisjsrc : Disjoint Q.leftSide Q.rightSide := by
    rw [show Q.leftSide = _ from axisRectQuadrilateral_leftSide hab hst,
      show Q.rightSide = _ from axisRectQuadrilateral_rightSide hab hst, Set.disjoint_left]
    rintro z ⟨hzre, _⟩ ⟨hzre', _⟩; rw [hzre] at hzre'; exact absurd hzre' (by linarith)
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro p ⟨zl, hzlL, rfl⟩ ⟨zr, hzrR, hpr⟩
    have hzz : zl = zr := hf.injective hpr.symm
    subst hzz; exact (Set.disjoint_left.mp hdisjsrc hzlL) hzrR
  · rw [show Q.leftSide = _ from axisRectQuadrilateral_leftSide hab hst]
    exact ⟨Complex.mk a s, rfl, le_refl s, hst.le⟩

/-- The swapped axis-rectangle quadrilateral's image left/right sides (bottom `{im = s}`, top
`{im = t}`) are disjoint under `f`, and the left side is nonempty. -/
theorem image_axisRectQuadrilateralSwap_sides_disjoint {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    Disjoint (f '' (axisRectQuadrilateralSwap a b s t hab hst).leftSide)
        (f '' (axisRectQuadrilateralSwap a b s t hab hst).rightSide) ∧
      (axisRectQuadrilateralSwap a b s t hab hst).leftSide.Nonempty := by
  set Q := axisRectQuadrilateralSwap a b s t hab hst
  have hdisjsrc : Disjoint Q.leftSide Q.rightSide := by
    rw [show Q.leftSide = _ from axisRectQuadrilateralSwap_leftSide hab hst,
      show Q.rightSide = _ from axisRectQuadrilateralSwap_rightSide hab hst, Set.disjoint_left]
    rintro z ⟨hzim, _⟩ ⟨hzim', _⟩; rw [hzim] at hzim'; exact absurd hzim' (by linarith)
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro p ⟨zl, hzlL, rfl⟩ ⟨zr, hzrR, hpr⟩
    have hzz : zl = zr := hf.injective hpr.symm
    subst hzz; exact (Set.disjoint_left.mp hdisjsrc hzlL) hzrR
  · rw [show Q.leftSide = _ from axisRectQuadrilateralSwap_leftSide hab hst]
    exact ⟨Complex.mk a s, rfl, le_refl a, hab.le⟩

/-- **Cauchy–Schwarz reduction (`ℝ≥0∞` arithmetic).** If the cross integral of two measurable
densities dominates `1`, i.e. `1 ≤ ∫⁻ z, ρ z · σ z`, then the product of the two energies dominates
`1`: `1 ≤ (∫∫ ρ²) · (∫∫ σ²)`.

This is the *final* sound step of the ρ-potential / co-area route to
`imageConjugate_lengthArea_pairwise`: it consumes the (genuinely hard, co-area-supplied) lower bound
`∫∫ ρσ ≥ 1` and discharges the rest by the Hölder/Cauchy–Schwarz inequality
`ENNReal.lintegral_mul_le_Lp_mul_Lq` at the conjugate exponents `(2, 2)`, then squaring.

It is **not** itself the residual: the hypothesis `1 ≤ ∫∫ ρσ` is *false* for arbitrary admissible
pairs (it holds only when `ρ, σ` are related through the extremal foliation — see the docstring of
`imageConjugate_lengthArea_pairwise`), so this lemma is stated as an *implication* and must be fed
the cross bound by the co-area argument. As a pure `ℝ≥0∞` inequality it is unconditionally true and
axiom-clean; it isolates the only part of the classical Cauchy–Schwarz route that *is* sound. -/
theorem one_le_energy_mul_energy_of_one_le_lintegral_mul {ρ σ : ℂ → ℝ≥0∞}
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hcross : 1 ≤ ∫⁻ z, ρ z * σ z) :
    1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) := by
  set A : ℝ≥0∞ := ∫⁻ z, (ρ z) ^ 2 with hA
  set B : ℝ≥0∞ := ∫⁻ z, (σ z) ^ 2 with hB
  -- Hölder at the conjugate exponents `(2, 2)`: `∫⁻ ρσ ≤ (∫⁻ ρ^(2:ℝ))^(1/2) · (∫⁻ σ^(2:ℝ))^(1/2)`.
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℂ)
    (Real.HolderConjugate.two_two) (f := ρ) (g := σ) hρm.aemeasurable hσm.aemeasurable
  -- Identify the `rpow`-`2` energies with the `npow`-`2` energies appearing in the goal.
  have hAeq : (∫⁻ z, (ρ z) ^ (2 : ℝ)) = A := by
    rw [hA]; exact lintegral_congr fun z => ENNReal.rpow_two _
  have hBeq : (∫⁻ z, (σ z) ^ (2 : ℝ)) = B := by
    rw [hB]; exact lintegral_congr fun z => ENNReal.rpow_two _
  -- so `1 ≤ ∫⁻ ρσ ≤ A^(1/2) · B^(1/2)`.
  have hmul : (fun z => (ρ * σ) z) = fun z => ρ z * σ z := rfl
  rw [hmul, hAeq, hBeq] at hCS
  have h1le : (1 : ℝ≥0∞) ≤ A ^ (1 / (2:ℝ)) * B ^ (1 / (2:ℝ)) := le_trans hcross hCS
  -- Square: `1 = 1^(2:ℝ) ≤ (A^(1/2) · B^(1/2))^(2:ℝ) = A · B`.
  have hsq : (A ^ (1 / (2:ℝ)) * B ^ (1 / (2:ℝ))) ^ (2 : ℝ) = A * B := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  calc (1 : ℝ≥0∞) = (1 : ℝ≥0∞) ^ (2 : ℝ) := by rw [ENNReal.one_rpow]
    _ ≤ (A ^ (1 / (2:ℝ)) * B ^ (1 / (2:ℝ))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1le (by norm_num)
    _ = A * B := hsq

/-! ### The ρ-potential and the co-area cross-bound `1 ≤ ∫∫ ρσ`

We now build the sound ρ-potential / co-area route to the cross-bound `1 ≤ ∫⁻ z, ρ z · σ z` that
`one_le_energy_mul_energy_of_one_le_lintegral_mul` consumes. The classical chain is:

1. Define `u = rhoPotential` = the `ρ`-geodesic distance from the image **left** side; `u = 0` on
   the left side and `u ≥ 1` on the right side (every connecting image curve has `ρ`-length `≥ 1`).
2. `u` is Lipschitz (after the standard truncation `ρ_n = min(ρ, n)`, which makes the potential
   `n·diam`-Lipschitz; the full `ρ ∈ L²` case follows by monotone convergence `n → ∞`) and satisfies
   the eikonal bound `‖∇u‖ ≤ ρ` a.e.
3. For each level `c ∈ (0, 1)` the level set `{u = c}` carries a **separating** curve, so its
   `σ`-arclength `μH[1]`-integral is `≥ 1` (admissibility of `σ`).
4. The **Eilenberg co-area inequality** (`RiemannDynamics.Coarea.eilenberg_coarea_grad_le`) plus the
   eikonal bound gives
   `∫⁻ ρσ ≥ ∫⁻ σ‖∇u‖ ≥ ∫⁻ c, (∫_{u=c} σ dμH[1]) dc ≥ ∫₀¹ 1 dc = 1`.

Each net-new geometric ingredient is isolated as a precise, TRUE, correctly-directed residual; the
final assembly `cross_bound_of_rhoPotential` wires them together and is sound modulo exactly those
residuals plus the co-area atom in `Coarea.lean`. -/

open RiemannDynamics.Coarea in
/-- The **`ρ`-potential** of a homeomorphism `f`, density `ρ`, and quadrilateral `Q`: the
`ρ`-geodesic distance from the image **left** side `f '' Q.leftSide` to the point `w`, i.e. the
infimum of `arcLengthLineIntegral ρ δ` over absolutely continuous curves `δ : ℝ → ℂ` on `[0, 1]`
that start on the image left side, end at `w`, and stay inside the image region `f '' Q.image`.

This is the standard potential whose level sets foliate the image quadrilateral; `u = 0` on the
left side, `u ≥ 1` on the right side (by `ρ`-admissibility), and (after truncation) `u` is Lipschitz
with eikonal bound `‖∇u‖ ≤ ρ`. The infimum over the empty family is `⊤` (points not reachable by an
AC image curve from the left side); on the connected image region all points are reachable. -/
noncomputable def rhoPotential (ρ : ℂ → ℝ≥0∞) (f : ℂ → ℂ) (Q : Quadrilateral) (w : ℂ) : ℝ≥0∞ :=
  ⨅ δ ∈ {δ : ℝ → ℂ | Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ f '' Q.leftSide ∧ δ 1 = w ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ f '' Q.image},
    arcLengthLineIntegral ρ δ

/-- **The ρ-potential vanishes on the image left side.**

`rhoPotential ρ f Q w = 0` for every `w ∈ f '' Q.leftSide`: the constant curve `δ ≡ w` starts and
ends on the left side, stays in the image (the left side is contained in the image), and has zero
arc-length line integral (its derivative is `0`).

## Truth and direction

**TRUE**, direction correct (the potential is `0`, not merely `≤ 0`). The constant curve is an
admissible connector with `arcLengthLineIntegral ρ (const) = 0`, and the potential is an infimum of
nonnegative quantities, so it is exactly `0`. The only content is that `f '' Q.leftSide ⊆ f ''
Q.image` (left side ⊆ image) and that the constant curve is continuous and absolutely continuous. -/
theorem rhoPotential_eq_zero_of_mem_leftSide {ρ : ℂ → ℝ≥0∞} {f : ℂ → ℂ} {Q : Quadrilateral}
    {w : ℂ} (hw : w ∈ f '' Q.leftSide)
    (hleft_sub : f '' Q.leftSide ⊆ f '' Q.image) :
    rhoPotential ρ f Q w = 0 := by
  -- The constant curve `δ ≡ w` is an admissible connector with zero ρ-length.
  refine le_antisymm ?_ (zero_le _)
  refine iInf₂_le_of_le (fun _ : ℝ => w) ?_ ?_
  · refine ⟨continuous_const, ?_, hw, rfl, fun t _ => hleft_sub hw⟩
    -- a constant function is absolutely continuous on any interval (it is `0`-Lipschitz)
    exact ((LipschitzWith.const' w).lipschitzOnWith (s := Set.uIcc 0 1)
      (K := 0)).absolutelyContinuousOnInterval
  · -- `arcLengthLineIntegral ρ (const w) = 0` since `deriv (const w) = 0`.
    unfold arcLengthLineIntegral
    have hderiv : ∀ t : ℝ, deriv (fun _ : ℝ => w) t = 0 := fun t => deriv_const t w
    simp only [hderiv, nnnorm_zero, ENNReal.coe_zero, mul_zero, lintegral_zero, le_refl]

/-- **The ρ-potential is at least `1` on the image right side (the admissibility bound).**

If `ρ` is admissible for `Q.imageCurveFamily f`, then `rhoPotential ρ f Q w ≥ 1` for every
`w ∈ f '' Q.rightSide`: any AC image curve `δ` from the left side to `w` (staying in the image) is a
member of `Q.imageCurveFamily f`, so `arcLengthLineIntegral ρ δ ≥ 1`; the infimum over such curves
is `≥ 1`.

## Truth and direction

**TRUE**, direction correct (`≥ 1`). This is exactly where the `ρ`-admissibility hypothesis
`hρ.2` enters: a connecting curve to a right-side point is a crossing curve of the image family, so
its `ρ`-length is `≥ 1`. The infimum of a family bounded below by `1` is `≥ 1` (vacuously `⊤ ≥ 1`
if the family is empty). -/
theorem one_le_rhoPotential_of_mem_rightSide {ρ : ℂ → ℝ≥0∞} {f : ℂ → ℂ} {Q : Quadrilateral}
    {w : ℂ} (hw : w ∈ f '' Q.rightSide)
    (hρ : IsAdmissibleDensity ρ (Q.imageCurveFamily f)) :
    1 ≤ rhoPotential ρ f Q w := by
  -- Every connector to a right-side point is a member of the image crossing family.
  refine le_iInf₂ ?_
  rintro δ ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩
  refine hρ.2 δ ?_
  -- `δ ∈ Q.imageCurveFamily f`: it is continuous, AC, starts on `f '' leftSide`, ends on
  -- `f '' rightSide` (since `δ 1 = w ∈ f '' rightSide`), and stays in `f '' image`.
  exact ⟨hδcont, hδac, hδ0, hδ1 ▸ hw, hδimg⟩

/-- **Per-density cross-bound from the ρ-potential (the co-area assembly).**

Given a homeomorphism `f`, a quadrilateral `Q`, an admissible `ρ` for `Q.imageCurveFamily f` and an
admissible `σ` for the conjugate (separating) image family, the cross integral dominates `1`:
`1 ≤ ∫⁻ z, ρ z · σ z`.

The proof wires together the ρ-potential properties, the eikonal bound, the level-set separation,
and the Eilenberg co-area inequality. The three genuinely net-new geometric ingredients are taken as
explicit hypotheses (each TRUE and correctly directed, proved/isolated elsewhere):

* `hLip` — the (truncated) potential `u` is `K`-Lipschitz;
* `heik` — the eikonal bound `‖∇u‖ ≤ ρ` a.e. (`‖fderiv ℝ u z‖₊ ≤ ρ z`);
* `hlevel` — each level set `{u = c}`, `c ∈ (0, 1)`, carries `σ`-arclength `≥ 1`:
  `1 ≤ ∫⁻ z in u⁻¹{c}, σ z ∂μH[1]`.

From these, `∫⁻ ρσ ≥ ∫⁻ σ‖∇u‖ ≥ ∫⁻ c, (∫_{u=c} σ dμH[1]) dc ≥ ∫_{(0,1)} 1 dc = 1` by
`eilenberg_coarea_grad_le`. -/
theorem cross_bound_of_rhoPotential {ρ σ : ℂ → ℝ≥0∞}
    {u : ℂ → ℝ} {K : ℝ≥0} (hσm : Measurable σ) (hLip : LipschitzWith K u)
    (heik : ∀ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ρ z)
    (hlevel : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      1 ≤ ∫⁻ z in u ⁻¹' {c}, σ z ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)) :
    1 ≤ ∫⁻ z, ρ z * σ z := by
  classical
  -- STEP 1: Eilenberg co-area inequality with weight `g = σ`.
  have hcoarea := RiemannDynamics.Coarea.eilenberg_coarea_grad_le hLip hσm
  -- STEP 2: the gradient-weighted integral is dominated by `∫⁻ ρσ` via the eikonal bound.
  have hgrad_le : ∫⁻ z, σ z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ z, ρ z * σ z := by
    refine lintegral_mono fun z => ?_
    rw [mul_comm (ρ z) (σ z)]
    exact mul_le_mul' (le_refl (σ z)) (heik z)
  -- STEP 3: the integrated level-set bound `1 ≤ ∫⁻ c, (∫_{u=c} σ dμH[1])`.
  have hlevel_int :
      (1 : ℝ≥0∞) ≤ ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, σ z
        ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)) := by
    -- Lower-bound the integrand *pointwise* by the indicator of `(0, 1)` (no measurability of the
    -- inner integral needed), then evaluate the indicator integral.
    have hpt : ∀ c : ℝ, (Set.Ioo (0:ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) c
        ≤ ∫⁻ z in u ⁻¹' {c}, σ z
            ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) := by
      intro c
      by_cases hc : c ∈ Set.Ioo (0:ℝ) 1
      · rw [Set.indicator_of_mem hc]; exact hlevel c hc
      · rw [Set.indicator_of_notMem hc]; exact zero_le _
    calc (1 : ℝ≥0∞)
        = ∫⁻ c, (Set.Ioo (0:ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) c := by
          rw [lintegral_indicator measurableSet_Ioo, setLIntegral_const, Real.volume_Ioo]
          norm_num
      _ ≤ ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, σ z
            ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)) :=
          lintegral_mono hpt
  -- Chain: 1 ≤ ∫⁻ c (level) ≤ ∫⁻ σ‖∇u‖ ≤ ∫⁻ ρσ.
  exact hlevel_int.trans (hcoarea.trans hgrad_le)

/-! ### Background: the per-density length–area inequality and the co-area route

For a homeomorphism `f` and an axis rectangle `(a, b) × (s, t)`, every density `ρ` admissible for
the image crossing family `Γ` and every `σ` admissible for the image separating family `Γ*` satisfy
`1 ≤ (∫∫ ρ²) · (∫∫ σ²)` (`imageConjugate_lengthArea_pairwise` below). The route is the ρ-potential /
co-area argument assembled above: `exists_rhoPotential_data` provides the Lipschitz potential and
its eikonal / level-set data, `cross_bound_of_rhoPotential` runs the Eilenberg co-area inequality to
the cross-bound `1 ≤ ∫∫ ρσ`, and `one_le_energy_mul_energy_of_one_le_lintegral_mul` finishes by
Cauchy–Schwarz.

## Truth and direction

**TRUE**, direction `≥ 1` correct. Taking the infimum over admissible `ρ` then over admissible `σ`,
this per-pair inequality is *exactly equivalent* to the conjugate-image reciprocity
`1 ≤ M(Γ) · M(Γ*)` (the equivalence is the proven `one_le_biInf_mul_biInf'`, given the
finiteness witnesses `imageCurveFamily_finiteWitness`). It is the **easy** direction of reciprocity
(Ahlfors, *Conformal Invariants*, Ch. 4; Väisälä §II; Lehto–Virtanen Ch. I §3); the reverse
`M(Γ) · M(Γ*) ≤ 1` requires the extremal metric / conformal structure and is *false* for a mere
homeomorphism. No conformality or differentiability of `f` is used.

## The precise missing classical ingredient (and what *is* now proved around it)

This is the irreducible atomic residual. The naïve Cauchy–Schwarz route via
`1 ≤ (∫∫ ρσ)² ≤ (∫∫ ρ²)(∫∫ σ²)` together with `∫∫ ρσ ≥ 1` is **unsound** *as stated*: `∫∫ ρσ ≥ 1`
is *false* for arbitrary admissible pairs (it holds only at the extremal pair). The genuinely sound
route is the **ρ-potential / co-area** argument: let `u(w)` be the `ρ`-geodesic distance from the
image left side to `w` inside `f''(rect)` (the infimum of `arcLengthLineIntegral ρ γ` over AC curves
`γ` from the left image side to `w`). Then `u = 0` on the left image side and `u ≥ 1` on the right
image side (every connecting curve has `ρ`-length `≥ 1` by `hρ`); `u` is `1`-Lipschitz in the
`ρ`-length metric with the *eikonal* bound `‖∇u‖ ≤ ρ` a.e.; the level sets `{u = c}`, `c ∈ (0, 1)`,
**separate** the two image sides, so each carries `σ`-arc-length `≥ 1` by `hσ`; and the **co-area /
Eilenberg inequality** for `u` gives `∫∫ ρσ ≥ ∫∫ ‖∇u‖σ ≥ ∫₀¹ (∫_{u=c} σ dH¹) dc ≥ 1`. Feeding that
cross bound into the proved `one_le_energy_mul_energy_of_one_le_lintegral_mul` closes the goal.

**Status of this route in the repository (recon performed).** The *final* Cauchy–Schwarz step
`(∫∫ ρσ ≥ 1) ⟹ (∫∫ ρ²)(∫∫ σ²) ≥ 1` is **fully proved and axiom-clean**
(`one_le_energy_mul_energy_of_one_le_lintegral_mul`, via `ENNReal.lintegral_mul_le_Lp_mul_Lq` at the
conjugate pair `(2, 2)`). What remains genuinely **absent from Mathlib and this repository** is the
co-area core that supplies `∫∫ ρσ ≥ 1`:

* Mathlib has **no co-area formula and no Eilenberg inequality** (an exhaustive search finds neither
  `coarea` nor `eilenberg`; no arc length / rectifiability theory; the only change-of-variables
  tool, `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, needs an *injective differentiable* map
  with a known differential, not a level-set foliation of a mere homeomorphism);
* it has no eikonal / metric-derivative `‖∇u‖ ≤ ρ` infrastructure (and for `ρ ∉ L^∞` the potential
  `u` is only Sobolev, not Lipschitz, so even the regularity of `u` is net-new);
* it has no Jordan / plane-separation theory to certify that the level sets `{u = c}` are members of
  (or dominate) the `σ`-admissible separating family.

So the ρ-potential route **does not close the residual**; it *relocates* the wall from the abstract
"co-area / disintegration of `volume ⌞ f''(rect)` along the image foliation" to the equally
Mathlib-absent **Lipschitz/Sobolev co-area (Eilenberg) inequality for the potential `u`** (plus its
eikonal bound and level-set separation). For the affine rectangle (`f = id`) this degenerates to
plain Fubini (exactly the proven `lengthArea_modulus_lower_bound`); for the curved image foliation
under a mere homeomorphism the leaves need not be rectifiable, so the co-area decomposition is
genuine net-new extremal-length infrastructure. This is the single honest, atomic residual on the
lower-modulus route; only the cross-bound `∫∫ ρσ ≥ 1` is missing, the surrounding reduction is
done. -/
/-- **The ρ-potential cross-bound is achievable (the isolated potential-regularity residual).**

For a homeomorphism `f`, an admissible `ρ` for the image crossing family and an admissible `σ` for
the conjugate (separating) image family of an axis rectangle, there exist a `K`-Lipschitz function
`u : ℂ → ℝ` and constant `K` satisfying the three hypotheses of `cross_bound_of_rhoPotential`:

* the eikonal bound `‖∇u‖ ≤ ρ` everywhere, and
* the level-set separation `1 ≤ ∫⁻ z in u⁻¹{c}, σ dμH[1]` for every `c ∈ (0, 1)`.

## Truth and direction

**TRUE**. The witness is the (truncated) ρ-potential `u = rhoPotential ρ f Q` of
`rhoPotential_eq_zero_of_mem_leftSide` / `one_le_rhoPotential_of_mem_rightSide`. The standard
construction: replace `ρ` by `ρ_n = min(ρ, n)` so that `u_n` becomes `n`-Lipschitz (each segment of
length `ℓ` contributes `≤ n·ℓ` to the `ρ_n`-distance), with the *pointwise* eikonal `‖∇u_n‖ ≤ ρ_n ≤
ρ` (the potential is `1`-Lipschitz in the `ρ_n`-length metric, whose metric derivative is `ρ_n`);
the level sets `{u_n = c}` for `c ∈ (0, 1)` separate the image left and right sides (a separating
arc of the swapped family lies in each), so by `σ`-admissibility of the separating family each
carries `σ`-arclength `≥ 1`; the `n → ∞` monotone-convergence passage recovers the bound for `ρ`.
Each step is classical extremal-length theory (Ahlfors, *Conformal Invariants* Ch. 4; Väisälä §II).

## Missing classical ingredient

The Lipschitz regularity and eikonal bound of the geodesic ρ-potential (Mathlib has no
geodesic-distance / length-structure theory), and the topological separation certifying that the
level sets of `u` dominate a `σ`-admissible separating curve (no Jordan-separation / level-set
rectifiability for Lipschitz functions in Mathlib). These are the genuine net-new extremal-length
ingredients; the co-area atom itself is `Coarea.eilenberg_coarea_grad_le`. -/
theorem exists_rhoPotential_data {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    ∃ (u : ℂ → ℝ) (K : ℝ≥0), LipschitzWith K u ∧
      (∀ z, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ρ z) ∧
      (∀ c ∈ Set.Ioo (0 : ℝ) 1,
        1 ≤ ∫⁻ z in u ⁻¹' {c}, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)) := by
  sorry

theorem imageConjugate_lengthArea_pairwise {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) := by
  -- Obtain the (truncated) ρ-potential data, then run the co-area cross-bound and Cauchy–Schwarz.
  obtain ⟨u, K, hLip, heik, hlevel⟩ := exists_rhoPotential_data hf hab hst hρ hσ
  have hcross : 1 ≤ ∫⁻ z, ρ z * σ z :=
    cross_bound_of_rhoPotential hσ.1 hLip heik hlevel
  exact one_le_energy_mul_energy_of_one_le_lintegral_mul hρ.1 hσ.1 hcross

/-- **Conjugate-image modulus reciprocity.**

For a homeomorphism `f : ℂ → ℂ` and an axis *square* `S = (a, b) × (s, t)` (`b − a = t − s`), the
two conjugate **image** families of `S` — the crossing family `Γ = S.imageCurveFamily f`
(`f`-image of left ↔ right) and the separating family `Γ* = (swapped S).imageCurveFamily f`
(`f`-image of bottom ↔ top) — satisfy modulus reciprocity `1 ≤ M(Γ) · M(Γ*)`.

This is **fully reduced** to the single isolated residual `imageConjugate_lengthArea_pairwise` (the
per-density length–area inequality, the genuine co-area core; see its docstring). The reduction is
the `ℝ≥0∞` lemma `one_le_biInf_mul_biInf'` fed by the two Rengel finiteness witnesses
`imageCurveFamily_finiteWitness` (constructed from `image_axisRectQuadrilateral_volume_pos` /
`…Swap` and the disjoint-image-sides lemmas), all proved above. -/
theorem conjugateImageModulus_reciprocity {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    1 ≤ curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)
      * curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) := by
  obtain ⟨hdisjC, hneLC⟩ := image_axisRectQuadrilateral_sides_disjoint hf hab hst
  obtain ⟨hdisjS, hneLS⟩ := image_axisRectQuadrilateralSwap_sides_disjoint hf hab hst
  have hwitC := imageCurveFamily_finiteWitness hf (axisRectQuadrilateral a b s t hab hst)
    (image_axisRectQuadrilateral_volume_pos hf hab hst) hdisjC hneLC
  obtain ⟨ρ₀, hρ₀adm, hρ₀0, hρ₀top⟩ := hwitC
  -- the swapped family's image region equals the same rectangle, so its volume is positive too
  have hposvolS : 0 < volume (f '' (axisRectQuadrilateralSwap a b s t hab hst).image) := by
    rw [axisRectQuadrilateralSwap_image]
    exact image_axisRectQuadrilateral_volume_pos hf hab hst
  have hwitS := imageCurveFamily_finiteWitness hf (axisRectQuadrilateralSwap a b s t hab hst)
    hposvolS hdisjS hneLS
  obtain ⟨σ₀, hσ₀adm, _, hσ₀top⟩ := hwitS
  -- Apply the reduction lemma with explicit index sets and value functions, so no expensive
  -- unification of the `biInf` shape is needed.
  have hpair : ∀ ρ ∈ {ρ : ℂ → ℝ≥0∞ |
        IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)},
      ∀ σ ∈ {σ : ℂ → ℝ≥0∞ |
        IsAdmissibleDensity σ ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)},
      1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) :=
    fun ρ hρ σ hσ => imageConjugate_lengthArea_pairwise hf hab hst hρ hσ
  have hmain := one_le_biInf_mul_biInf'
    (I := {ρ : ℂ → ℝ≥0∞ |
      IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)})
    (J := {σ : ℂ → ℝ≥0∞ |
      IsAdmissibleDensity σ ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)})
    (fun ρ => ∫⁻ z, (ρ z) ^ 2) (fun σ => ∫⁻ z, (σ z) ^ 2)
    ⟨ρ₀, hρ₀adm, hρ₀0, hρ₀top⟩ ⟨σ₀, hσ₀adm⟩ ⟨σ₀, hσ₀adm, hσ₀top⟩ hpair
  exact hmain

/-- **Modulus lower bound for the image of an axis square.**

For a geometric `K`-quasiconformal map `f` and an axis-aligned **square** `Q = (a, b) × (s, t)`
(`b − a = t − s`, so `Q` has crossing modulus `1`), the modulus of the image crossing family is at
least `1/K`:
`ENNReal.ofReal (1/K) ≤ curveModulus (Q.imageCurveFamily f)`.

## Proof (the reciprocity route)

This is **fully reduced** to the single quasiconformal residual
`conjugateImageModulus_reciprocity` (modulus reciprocity `M(Γ) · M(Γ*) ≥ 1` for the two conjugate
image families). Writing `Γ = Q.imageCurveFamily f` (crossing) and `Γ* = Q♯.imageCurveFamily f` for
the swapped square `Q♯` (separating), the steps are:
* `M(Γ*) ≤ K`: the geometric upper bound `hf.2.2` applied to the **swapped** square `Q♯`, whose
  modulus is `≤ (b − a)/(t − s) = 1` for a square (`axisRectSwap_modulus_upper_bound`);
* reciprocity `1 ≤ M(Γ) · M(Γ*)` (`conjugateImageModulus_reciprocity`);
* combine: `1 ≤ M(Γ) · M(Γ*) ≤ M(Γ) · K`, i.e. `1 ≤ M(Γ) · ofReal K`.

Multiplying by `ofReal (1/K)` (and cancelling) yields `M(Γ) ≥ 1/K`. All steps except
`conjugateImageModulus_reciprocity` are proved here. -/
theorem square_imageCurveFamily_modulus_ge {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) (hsquare : b - a = t - s) :
    ENNReal.ofReal (1 / K)
      ≤ curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) := by
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  have hfhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  set M := curveModulus ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f) with hM
  set N := curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) with hN
  -- `M(Γ*) ≤ K`: geometric upper bound on the swapped square; its modulus is `≤ 1` (square).
  have hNK : N ≤ ENNReal.ofReal K := by
    have hmod := hf.2.2 (axisRectQuadrilateralSwap a b s t hab hst)
    have hupper : (axisRectQuadrilateralSwap a b s t hab hst).modulus ≤ 1 := by
      refine le_trans (axisRectSwap_modulus_upper_bound hab hst) ?_
      rw [hsquare, div_self (by linarith : t - s ≠ 0), ENNReal.ofReal_one]
    calc N = curveModulus ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) := hN
      _ ≤ ENNReal.ofReal K * (axisRectQuadrilateralSwap a b s t hab hst).modulus := hmod
      _ ≤ ENNReal.ofReal K * 1 := by gcongr
      _ = ENNReal.ofReal K := mul_one _
  -- Reciprocity `1 ≤ M · N`.
  have hrecip : 1 ≤ M * N := conjugateImageModulus_reciprocity hfhomeo hab hst
  -- Chain: `1 ≤ M · N ≤ M · ofReal K`.
  have hchain : (1 : ℝ≥0∞) ≤ M * ENNReal.ofReal K :=
    le_trans hrecip (by gcongr)
  -- `1 ≤ M · ofReal K`  ⟹  `ofReal (1/K) ≤ M`.
  have hcancel : ENNReal.ofReal (1 / K) * ENNReal.ofReal K = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (ne_of_gt hKpos),
      ENNReal.ofReal_one]
  have hmul : ENNReal.ofReal (1 / K) * 1
      ≤ ENNReal.ofReal (1 / K) * (M * ENNReal.ofReal K) := by gcongr
  have hrw : ENNReal.ofReal (1 / K) * (M * ENNReal.ofReal K) = M := by
    rw [show M * ENNReal.ofReal K = ENNReal.ofReal K * M from mul_comm _ _,
      ← mul_assoc, hcancel, one_mul]
  rwa [mul_one, hrw] at hmul

/-- **Quasiround distortion data for the image of concentric squares (distortion residual).**

For a geometric `K`-quasiconformal map `f` there is a constant `C' ≥ 0` (depending only on `K`)
such that, for every ball `closedBall x r` (`0 < r`) with inner half-side `h = r/√2`, there is a
distance `d > 0` such that:
* the images of the two opposite (left, right) sides of the **inner** square are at distance `≥ d`,
  i.e. `∀ p ∈ f '' innerLeft, ∀ q ∈ f '' innerRight, d ≤ dist p q`; and
* the diameter of the **outer** image square is bounded: `diam (f '' qcOuterSquare x r) ≤ C' · d`.

## Truth and direction

**TRUE**, both `≥`/`≤` directions correct. Take `d = infDist (f '' innerLeft) (f '' innerRight)`:
the two image sides are disjoint compacta (`f` is an injective homeomorphism, the two source sides
are disjoint compacta), so `d > 0`, giving the first clause. The second clause is the
**quasiround / two-point-distortion** estimate: under a `K`-quasiconformal map, the image of the
outer square (a fixed `√2` linear scaling of the inner square, concentric) has diameter comparable
to the inner image side-separation, with a constant depending only on `K` (scale/translation
invariance of QC distortion makes `C'` uniform in `x, r`).

## The precise missing classical ingredient

The load-bearing absent theorem is the **two-point distortion / quasisymmetry** estimate for
`K`-quasiconformal maps (Mori-type, or equivalently a lower bound on the modulus of the Teichmüller
ring separating `{x, innerSide}` from `{outerCorner, ∞}`): it controls the diameter of an image set
by the separation of two interior reference sets. This requires the Grötzsch/Teichmüller ring
modulus estimate, absent from Mathlib and this repository (which has only the rectangle modulus, no
ring modulus). It is genuinely independent of Rengel (there is no upper-diameter analogue of
Rengel's area lower bound) and of reciprocity. -/
theorem qc_quasiround_data {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∀ (h : ℝ), h = r / Real.sqrt 2 →
        ∀ (hlt : x.re - h < x.re + h) (hlt2 : x.im - h < x.im + h),
      ∃ d : ℝ, 0 < d ∧
        (∀ p ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
              hlt hlt2).leftSide,
         ∀ q ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
              hlt hlt2).rightSide,
          d ≤ dist p q) ∧
        Metric.diam (f '' qcOuterSquare x r) ≤ C' * d :=
  sorry

/-! ## STEP 4 — assembly of the QC roundness residual

The single residual `qc_image_outerSquare_diam_sq_le_innerSquare_volume` is now assembled from the
proven **Rengel** inequality and the two isolated TRUE residuals: Rengel gives
`d² · M(innerImageFamily) ≤ area(f '' inner)`, the reciprocity residual gives `M ≥ 1/K` (so
`d² ≤ K · area`), and the distortion residual gives `diam(f '' outer) ≤ C' · d`, whence
`diam² ≤ C'² · d² ≤ C'² · K · area`. -/

/-- **QC roundness for the image of an axis square.**

For a geometric `K`-quasiconformal map `f` there is a constant `C` (depending only on `K`) such
that, for the two concentric axis-aligned squares of every ball `closedBall x r` (`0 < r`), the
squared diameter of the outer image square is bounded by the area of the inner image square:
`(diam (f '' qcOuterSquare x r))² ≤ C · (volume (f '' qcInnerSquare x r)).toReal`, with
`C = C'² · K`.

## Status

The elementary length–area content (**Rengel's inequality**, `rengel_area_lower_bound`) is fully
proven; the assembly here is mechanical. The two genuinely two-dimensional quasiconformal
ingredients remain isolated as the precise TRUE residuals `square_imageCurveFamily_modulus_ge`
(modulus reciprocity) and `qc_quasiround_data` (two-point distortion); see their docstrings for the
exact missing classical theorems. -/
theorem qc_image_outerSquare_diam_sq_le_innerSquare_volume {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      (Metric.diam (f '' qcOuterSquare x r)) ^ 2
        ≤ C * (volume (f '' qcInnerSquare x r)).toReal := by
  have hfc : Continuous f := hf.2.1.isHomeomorph.continuous
  have hK1 : (1:ℝ) ≤ K := hf.1
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  obtain ⟨C', hC'0, hquasi⟩ := qc_quasiround_data hf
  refine ⟨C' ^ 2 * K, by positivity, fun x r hr => ?_⟩
  set h : ℝ := r / Real.sqrt 2 with hh
  have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hhpos : 0 < h := by rw [hh]; positivity
  have hlt : x.re - h < x.re + h := by linarith
  have hlt2 : x.im - h < x.im + h := by linarith
  set Q := axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h) hlt hlt2 with hQ
  have hinner_eq : qcInnerSquare x r = Q.image := by
    rw [hQ, axisRectQuadrilateral_image]; rfl
  obtain ⟨d, hdpos, hdist, hdiam_le⟩ := hquasi x r hr h hh hlt hlt2
  -- `Q.image` is compact, hence `f '' Q.image` is a compact (so measurable, finite-volume) set.
  have hQimg_cpt : IsCompact (f '' Q.image) :=
    (IsCompact.image (isCompact_Icc.prod isCompact_Icc) Q.continuous_toFun).image hfc
  have hRmeas : MeasurableSet (f '' Q.image) := hQimg_cpt.measurableSet
  have harea_fin : volume (f '' Q.image) ≠ ⊤ := hQimg_cpt.measure_lt_top.ne
  -- Rengel on the inner image family.
  have hΓ : ∀ δ ∈ Q.imageCurveFamily f, Continuous δ ∧
      AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ f '' Q.leftSide ∧ δ 1 ∈ f '' Q.rightSide ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ f '' Q.image := fun δ hδ => hδ
  have hrengel := rengel_area_lower_bound (A₁ := f '' Q.leftSide) (A₂ := f '' Q.rightSide)
    hRmeas hdpos hdist hΓ
  -- Reciprocity residual: the square's image crossing modulus is `≥ 1/K`.
  have hsquare : (x.re + h) - (x.re - h) = (x.im + h) - (x.im - h) := by ring
  have hmod := square_imageCurveFamily_modulus_ge hf hlt hlt2 hsquare
  -- Combine: `d²/K ≤ area(f '' inner)`.
  have hkey : ENNReal.ofReal (d ^ 2) * ENNReal.ofReal (1 / K) ≤ volume (f '' Q.image) :=
    calc ENNReal.ofReal (d ^ 2) * ENNReal.ofReal (1 / K)
        ≤ ENNReal.ofReal (d ^ 2) * curveModulus (Q.imageCurveFamily f) := by gcongr
      _ ≤ volume (f '' Q.image) := hrengel
  have hdK : d ^ 2 * (1 / K) ≤ (volume (f '' Q.image)).toReal := by
    have h1 : ENNReal.ofReal (d ^ 2 * (1 / K)) ≤ volume (f '' Q.image) := by
      rw [ENNReal.ofReal_mul (by positivity)]; exact hkey
    rwa [ENNReal.ofReal_le_iff_le_toReal harea_fin] at h1
  have hd2 : d ^ 2 ≤ K * (volume (f '' Q.image)).toReal := by
    have hstep : K * (d ^ 2 * (1 / K)) ≤ K * (volume (f '' Q.image)).toReal :=
      mul_le_mul_of_nonneg_left hdK hKpos.le
    have heq : K * (d ^ 2 * (1 / K)) = d ^ 2 := by field_simp
    rwa [heq] at hstep
  -- Distortion residual: `diam(f '' outer) ≤ C' · d`, then square and chain.
  have hdiam_nn : 0 ≤ Metric.diam (f '' qcOuterSquare x r) := Metric.diam_nonneg
  calc (Metric.diam (f '' qcOuterSquare x r)) ^ 2
      ≤ (C' * d) ^ 2 := pow_le_pow_left₀ hdiam_nn hdiam_le 2
    _ = C' ^ 2 * d ^ 2 := by ring
    _ ≤ C' ^ 2 * (K * (volume (f '' Q.image)).toReal) := by gcongr
    _ = C' ^ 2 * K * (volume (f '' qcInnerSquare x r)).toReal := by rw [hinner_eq]; ring

/-- **QC roundness: squared diameter of the image of a ball is controlled by its area.**

For a geometric `K`-quasiconformal map `f`, there is a constant `C` (depending only on `K`) with
`(diam (f '' closedBall x r))² ≤ C · (volume (f '' closedBall x r)).toReal` for every ball.

This is the **true** direction of the roundness estimate: quasiconformal maps send balls to sets
whose diameter² is bounded by their area (the image of a ball is round; for the unit-area
comparison `area ≍ diam²` holds with constants depending on `K`). The *reverse* inequality
`volume ≤ C · diam²` is trivially true for every bounded set, so all the content is in this
stated direction.

## Status

The genuinely two-dimensional quasiconformal content is isolated, via the elementary STEP-1
square-sandwiching, into the single residual
`qc_image_outerSquare_diam_sq_le_innerSquare_volume` (whose docstring names the precise missing
classical ingredient — **Rengel's inequality** / a modulus lower bound, absent from Mathlib and
this repository). The reduction here is pure monotonicity of `Metric.diam` and `volume` under the
inclusions `qcInnerSquare x r ⊆ closedBall x r ⊆ qcOuterSquare x r`. The `r ≤ 0` cases are trivial
(the image is empty or a single point, so the diameter is `0`). -/
theorem qc_image_ball_diam_sq_le_volume {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℂ) (r : ℝ),
      (Metric.diam (f '' Metric.closedBall x r)) ^ 2
        ≤ C * (volume (f '' Metric.closedBall x r)).toReal := by
  -- `f` is continuous (it is a homeomorphism), so image sets are bounded / finite-measure.
  have hfc : Continuous f := hf.2.1.isHomeomorph.continuous
  obtain ⟨C, hC0, hsq⟩ := qc_image_outerSquare_diam_sq_le_innerSquare_volume hf
  refine ⟨C, hC0, fun x r => ?_⟩
  by_cases hr : 0 < r
  · -- `0 < r`: monotonicity sandwich between the inner and outer image squares.
    -- The outer image square is compact, hence bounded; `diam` is monotone under `⊆`.
    have hout_cpt : IsCompact (f '' qcOuterSquare x r) := (isCompact_qcOuterSquare x r).image hfc
    have hdiam : Metric.diam (f '' Metric.closedBall x r)
        ≤ Metric.diam (f '' qcOuterSquare x r) :=
      Metric.diam_mono (image_closedBall_subset_qcOuterSquare f x r) hout_cpt.isBounded
    -- The ball image has finite measure (continuous image of a compact set).
    have hball_cpt : IsCompact (f '' Metric.closedBall x r) :=
      (isCompact_closedBall x r).image hfc
    have hball_fin : volume (f '' Metric.closedBall x r) < ⊤ := hball_cpt.measure_lt_top
    -- The inner image square's area is ≤ the ball image's area (monotonicity + finiteness).
    have hvol : (volume (f '' qcInnerSquare x r)).toReal
        ≤ (volume (f '' Metric.closedBall x r)).toReal :=
      ENNReal.toReal_mono hball_fin.ne
        (measure_mono (image_qcInnerSquare_subset f x hr.le))
    -- Chain: diam(f''ball)² ≤ diam(f''outer)² ≤ C·area(f''inner) ≤ C·area(f''ball).
    calc (Metric.diam (f '' Metric.closedBall x r)) ^ 2
        ≤ (Metric.diam (f '' qcOuterSquare x r)) ^ 2 :=
          pow_le_pow_left₀ Metric.diam_nonneg hdiam 2
      _ ≤ C * (volume (f '' qcInnerSquare x r)).toReal := hsq x r hr
      _ ≤ C * (volume (f '' Metric.closedBall x r)).toReal :=
          mul_le_mul_of_nonneg_left hvol hC0
  · -- `r ≤ 0`: the ball is empty (`r < 0`) or a singleton (`r = 0`); its image diameter is `0`.
    have hdiam0 : Metric.diam (f '' Metric.closedBall x r) = 0 := by
      rcases lt_trichotomy r 0 with hrlt | hreq | hrgt
      · rw [Metric.closedBall_eq_empty.2 hrlt, Set.image_empty, Metric.diam_empty]
      · subst hreq; rw [Metric.closedBall_zero, Set.image_singleton, Metric.diam_singleton]
      · exact absurd hrgt hr
    rw [hdiam0, zero_pow (by norm_num)]
    exact mul_nonneg hC0 ENNReal.toReal_nonneg

/-- The pushforward set function `B ↦ volume (f '' B)` of a homeomorphism `f`, as the honest Borel
measure `Measure.map f.symm volume`, evaluated on a measurable set `B`, equals `volume (f '' B)`. -/
private theorem map_symm_volume_apply {f : ℂ → ℂ} (hf : IsHomeomorph f) {B : Set ℂ}
    (hB : MeasurableSet B) :
    (Measure.map (hf.homeomorph f).symm volume) B = volume (f '' B) := by
  rw [Measure.map_apply ((hf.homeomorph f).symm.continuous.measurable) hB]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro h
    refine ⟨(hf.homeomorph f).symm z, h, ?_⟩
    have : f ((hf.homeomorph f).symm z) = (hf.homeomorph f) ((hf.homeomorph f).symm z) := rfl
    rw [this, (hf.homeomorph f).apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    have hfw : f w = (hf.homeomorph f) w := rfl
    rw [hfw, (hf.homeomorph f).symm_apply_apply]; exact hw

/-- The pushforward measure `Measure.map f.symm volume` of a homeomorphism `f` is locally finite:
`f.symm` is continuous, so it maps compacts to compacts, which have finite volume. -/
private theorem isFiniteMeasureOnCompacts_map_symm {f : ℂ → ℂ} (hf : IsHomeomorph f) :
    IsFiniteMeasureOnCompacts (Measure.map (hf.homeomorph f).symm volume) := by
  constructor
  intro K hK
  rw [Measure.map_apply ((hf.homeomorph f).symm.continuous.measurable) hK.measurableSet]
  have he : ⇑(hf.homeomorph f).symm ⁻¹' K = ⇑(hf.homeomorph f) '' K :=
    (congrFun (Set.image_eq_preimage_of_inverse (hf.homeomorph f).symm_apply_apply
      (hf.homeomorph f).apply_symm_apply) K).symm
  rw [he]
  exact ((hK.image (hf.homeomorph f).continuous)).measure_lt_top

/-- **A.e. differentiability of a geometric quasiconformal map (direct Stepanov / metric route).**

A geometric `K`-quasiconformal map `f : ℂ → ℂ` is real-Fréchet-differentiable at almost every
point. The proof verifies the **finite-upper-metric-derivative** Stepanov hypothesis from the QC
roundness estimate `qc_image_ball_diam_sq_le_volume` and the Lebesgue differentiation theorem
(`Besicovitch.ae_tendsto_rnDeriv` applied to the pushforward measure `Measure.map f.symm volume`),
then invokes `RiemannDynamics.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top`.

This is independent of the reverse-length-area / ACL route used by
`IsQCGeometric.ae_differentiableAt`. -/
theorem IsQCGeometric.ae_differentiableAt' {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ᵐ z : ℂ, DifferentiableAt ℝ f z := by
  classical
  -- `f` is a homeomorphism (continuous, injective, open) and `f` is continuous.
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  have hfc : Continuous f := hhomeo.continuous
  -- The QC roundness constant.
  obtain ⟨C, _hC0, hround⟩ := qc_image_ball_diam_sq_le_volume hf
  -- The pushforward measure `ν B = volume (f '' B)`.
  set ν : Measure ℂ := Measure.map (hhomeo.homeomorph f).symm volume with hν
  have hνloc : IsFiniteMeasureOnCompacts ν := isFiniteMeasureOnCompacts_map_symm hhomeo
  have : IsLocallyFiniteMeasure ν := by infer_instance
  -- It suffices to verify the finite-upper-metric-derivative Stepanov hypothesis a.e.
  apply RiemannDynamics.Stepanov.ae_differentiableAt_of_ae_limsup_slope_lt_top
  -- STEP 1 — Lebesgue differentiation: a.e. `ν(closedBall x r)/vol(closedBall x r)` tends to the
  -- finite RN-derivative.
  have htend := Besicovitch.ae_tendsto_rnDeriv ν (volume : Measure ℂ)
  have hfin : ∀ᵐ x : ℂ, ν.rnDeriv volume x < ∞ := Measure.rnDeriv_lt_top ν volume
  -- Combine the two a.e. statements; build the Stepanov hypothesis at each good `x`.
  filter_upwards [htend, hfin] with x hx hxfin
  -- The Stepanov hypothesis at `x`: a constant `C'` with `‖f y - f x‖ ≤ C' ‖y - x‖` near `x`.
  -- Set `M = rnDeriv + 1`; eventually `ν(closedBall x ρ) ≤ M · vol(closedBall x ρ)`.
  set d : ℝ≥0∞ := ν.rnDeriv volume x with hd
  set M : ℝ≥0∞ := d + 1 with hM
  have hMlt : M < ∞ := by rw [hM]; exact ENNReal.add_lt_top.2 ⟨hxfin, ENNReal.one_lt_top⟩
  -- `d < M` so the density ratio is eventually `< M` (since it tends to `d`).
  have hdM : d < M := by rw [hM]; exact ENNReal.lt_add_right hxfin.ne one_ne_zero
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (closedBall x r) / volume (closedBall x r) < M :=
    hx.eventually (eventually_lt_nhds hdM)
  -- Turn the ratio bound into a product bound: for small `r`,
  -- `ν(closedBall x r) ≤ M · vol(closedBall x r)`. Volume of the ball is positive and finite.
  have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (ν (closedBall x r)).toReal ≤ M.toReal * (volume (closedBall x r)).toReal := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : (0 : ℝ) < r := hrpos
    have hvol_pos : 0 < volume (closedBall x r) := measure_closedBall_pos volume x hrpos'
    have hvol_top : volume (closedBall x r) < ∞ := measure_closedBall_lt_top
    -- From `a / b < M` with `0 < b < ∞`, get `a ≤ M * b` (≤ since `a/b < M` ⟹ `a < M*b`).
    have hle : ν (closedBall x r) ≤ M * volume (closedBall x r) := by
      rw [ENNReal.div_lt_iff (Or.inl hvol_pos.ne') (Or.inl hvol_top.ne)] at hr
      exact hr.le
    have hνtop : ν (closedBall x r) < ∞ := lt_of_le_of_lt hle
      (ENNReal.mul_lt_top hMlt hvol_top)
    calc (ν (closedBall x r)).toReal
        ≤ (M * volume (closedBall x r)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top hMlt hvol_top).ne hle
      _ = M.toReal * (volume (closedBall x r)).toReal := ENNReal.toReal_mul
  -- The Stepanov constant.
  refine ⟨Real.sqrt (C * M.toReal * π), ?_⟩
  -- We must show `‖f y - f x‖ ≤ √(C·M·π) · ‖y - x‖` eventually as `y → x`.
  -- Reduce to: for all small `ρ > 0`, the bound holds at radius `ρ`, then plug `ρ = ‖y - x‖`.
  -- First: a uniform radius-`ρ` statement from `hev2` translated through roundness.
  have hradius : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      Metric.diam (f '' closedBall x ρ) ≤ Real.sqrt (C * M.toReal * π) * ρ := by
    filter_upwards [hev2, self_mem_nhdsWithin] with ρ hρ hρpos
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- roundness: diam² ≤ C · (vol (f''closedBall x ρ)).toReal = C · (ν(closedBall x ρ)).toReal.
    have hνeq : (ν (closedBall x ρ)).toReal = (volume (f '' closedBall x ρ)).toReal := by
      rw [hν, map_symm_volume_apply hhomeo measurableSet_closedBall]
    have hdiam_sq : (Metric.diam (f '' closedBall x ρ)) ^ 2
        ≤ C * (ν (closedBall x ρ)).toReal := by
      rw [hνeq]; exact hround x ρ
    -- vol(closedBall x ρ).toReal = π ρ².
    have hvolball : (volume (closedBall x ρ)).toReal = π * ρ ^ 2 := by
      rw [Complex.volume_closedBall, ENNReal.toReal_mul]
      rw [show ((NNReal.pi : ℝ≥0∞)).toReal = π by simp]
      rw [show ((ENNReal.ofReal ρ ^ 2).toReal) = ρ ^ 2 by
        rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hρpos'.le]]
      ring
    -- chain: diam² ≤ C·(ν).toReal ≤ C·M·vol.toReal = C·M·π·ρ².
    have hchain : (Metric.diam (f '' closedBall x ρ)) ^ 2 ≤ C * M.toReal * π * ρ ^ 2 := by
      calc (Metric.diam (f '' closedBall x ρ)) ^ 2
          ≤ C * (ν (closedBall x ρ)).toReal := hdiam_sq
        _ ≤ C * (M.toReal * (volume (closedBall x ρ)).toReal) := by
              apply mul_le_mul_of_nonneg_left hρ _hC0
        _ = C * M.toReal * π * ρ ^ 2 := by rw [hvolball]; ring
    -- Take square roots: diam ≤ √(C·M·π)·ρ.
    have hdiam_nonneg : 0 ≤ Metric.diam (f '' closedBall x ρ) := Metric.diam_nonneg
    have hconst_nonneg : 0 ≤ C * M.toReal * π := by positivity
    have : Metric.diam (f '' closedBall x ρ) ≤ Real.sqrt (C * M.toReal * π * ρ ^ 2) := by
      rw [show C * M.toReal * π * ρ ^ 2 = (C * M.toReal * π) * ρ ^ 2 by ring]
      calc Metric.diam (f '' closedBall x ρ)
          = Real.sqrt ((Metric.diam (f '' closedBall x ρ)) ^ 2) := by
            rw [Real.sqrt_sq hdiam_nonneg]
        _ ≤ Real.sqrt ((C * M.toReal * π) * ρ ^ 2) := by
            apply Real.sqrt_le_sqrt
            rw [show (C * M.toReal * π) * ρ ^ 2 = C * M.toReal * π * ρ ^ 2 by ring]
            exact hchain
    calc Metric.diam (f '' closedBall x ρ)
        ≤ Real.sqrt (C * M.toReal * π * ρ ^ 2) := this
      _ = Real.sqrt (C * M.toReal * π) * ρ := by
          rw [show C * M.toReal * π * ρ ^ 2 = (C * M.toReal * π) * ρ ^ 2 by ring,
            Real.sqrt_mul hconst_nonneg, Real.sqrt_sq hρpos'.le]
  -- Now translate the radius-`ρ` bound to the pointwise Stepanov bound near `x`.
  -- For `y` with `0 < ‖y - x‖` small, set `ρ = ‖y - x‖`; then `y ∈ closedBall x ρ` and
  -- `‖f y - f x‖ ≤ diam (f''closedBall x ρ) ≤ √(C·M·π)·ρ = √(C·M·π)·‖y - x‖`.
  -- Pull back the eventual radius statement to an eventual neighborhood statement of `y`.
  rw [eventually_nhdsWithin_iff] at hradius
  rw [Metric.eventually_nhds_iff] at hradius ⊢
  obtain ⟨ε, hεpos, hε⟩ := hradius
  refine ⟨ε, hεpos, ?_⟩
  intro y hy
  rcases eq_or_ne y x with rfl | hyx
  · simp
  · -- `ρ = dist y x = ‖y - x‖ ∈ (0, ε)`.
    have hdist_pos : 0 < dist y x := dist_pos.2 hyx
    have hdist_lt : dist y x < ε := hy
    have hdist0 : dist (dist y x) 0 < ε := by
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    have hbound := hε hdist0 (Set.mem_Ioi.2 hdist_pos)
    -- y ∈ closedBall x (dist y x).
    have hymem : y ∈ closedBall x (dist y x) := Metric.mem_closedBall.2 le_rfl
    have hxmem : x ∈ closedBall x (dist y x) := by
      rw [Metric.mem_closedBall, dist_self]; exact dist_nonneg
    have hdiam_bd : dist (f y) (f x) ≤ Metric.diam (f '' closedBall x (dist y x)) :=
      Metric.dist_le_diam_of_mem ((isCompact_closedBall x (dist y x)).image hfc).isBounded
        (mem_image_of_mem f hymem) (mem_image_of_mem f hxmem)
    calc ‖f y - f x‖ = dist (f y) (f x) := (dist_eq_norm _ _).symm
      _ ≤ Metric.diam (f '' closedBall x (dist y x)) := hdiam_bd
      _ ≤ Real.sqrt (C * M.toReal * π) * dist y x := hbound
      _ = Real.sqrt (C * M.toReal * π) * ‖y - x‖ := by rw [dist_eq_norm]

end RiemannDynamics
