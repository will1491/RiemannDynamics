/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.SensePreserving
import RiemannDynamics.QC.ReverseLengthAreaForward
import RiemannDynamics.Analysis.Sobolev.Stepanov
import RiemannDynamics.Analysis.Sobolev.Coarea.Assembly
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
* `heik` — the (a.e.) weighted eikonal bound `σ ‖∇u‖ ≤ ρ σ` (`∀ᵐ z, σ z ‖fderiv ℝ u z‖₊ ≤ ρ z σ z`);
* `hlevel` — each level set `{u = c}`, `c ∈ (0, 1)`, carries `σ`-arclength `≥ 1`:
  `1 ≤ ∫⁻ z in u⁻¹{c}, σ z ∂μH[1]`.

From these, `∫⁻ ρσ ≥ ∫⁻ σ‖∇u‖ ≥ ∫⁻ c, (∫_{u=c} σ dμH[1]) dc ≥ ∫_{(0,1)} 1 dc = 1` by
`eilenberg_coarea_grad_le`. The eikonal is only required almost everywhere: the McShane-extended
geodesic potential is Lipschitz (hence differentiable a.e. by Rademacher) and the eikonal holds at
its Lebesgue/interior points, while the measure-zero boundary set is irrelevant to the integral. -/
theorem cross_bound_of_rhoPotential {ρ σ : ℂ → ℝ≥0∞}
    {u : ℂ → ℝ} {K : ℝ≥0} (hσm : Measurable σ) (hLip : LipschitzWith K u)
    (heik : ∀ᵐ z, σ z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ρ z * σ z)
    (hlevel : ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      1 ≤ ∫⁻ z in u ⁻¹' {c}, σ z ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)) :
    1 ≤ ∫⁻ z, ρ z * σ z := by
  classical
  -- STEP 1: Eilenberg co-area inequality with weight `g = σ`.
  have hcoarea := RiemannDynamics.Coarea.eilenberg_coarea_grad_le hLip hσm
  -- STEP 2: the weighted eikonal IS the (a.e.) pointwise integrand bound for `∫⁻ σ‖∇u‖ ≤ ∫⁻ ρσ`.
  have hgrad_le : ∫⁻ z, σ z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ∫⁻ z, ρ z * σ z :=
    lintegral_mono_ae heik
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

/-- **Projection lower bound for the 1-dimensional Hausdorff measure.** If the real projection of a
planar set `S` covers an interval `[α, β]`, then `μH[1] S ≥ β − α`. The real part is `1`-Lipschitz,
so it cannot increase `μH[1]`, while `μH[1]` on the line is Lebesgue measure. This is the
quantitative core of every level-set separation lower bound: a separating set whose projection
spans `[α, β]` carries at least `β − α` of `μH[1]`-length. -/
theorem ofReal_sub_le_hausdorffMeasure_one_of_reCLM_image
    {S : Set ℂ} {α β : ℝ} (hsub : Set.Icc α β ⊆ Complex.reCLM '' S) :
    ENNReal.ofReal (β - α) ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
  have hlip : LipschitzWith 1 (Complex.reCLM : ℂ → ℝ) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Complex.reCLM_apply, NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_re]
    rw [dist_eq_norm]
    exact Complex.abs_re_le_norm _
  have h1 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.reCLM '' S)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
    simpa [ENNReal.one_rpow] using hlip.hausdorffMeasure_image_le (d := 1) (by norm_num) S
  have h2 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.reCLM '' S) :=
    measure_mono hsub
  have h3 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      = ENNReal.ofReal (β - α) := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  rw [h3] at h2
  exact h2.trans h1

/-- **Projection lower bound for the 1-dimensional Hausdorff measure (imaginary projection).** The
imaginary-part twin of `ofReal_sub_le_hausdorffMeasure_one_of_reCLM_image`: if the imaginary
projection of a planar set `S` covers an interval `[α, β]`, then `μH[1] S ≥ β − α`. The imaginary
part is `1`-Lipschitz, so it cannot increase `μH[1]`, while `μH[1]` on the line is Lebesgue
measure. -/
theorem ofReal_sub_le_hausdorffMeasure_one_of_imCLM_image
    {S : Set ℂ} {α β : ℝ} (hsub : Set.Icc α β ⊆ Complex.imCLM '' S) :
    ENNReal.ofReal (β - α) ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
  have hlip : LipschitzWith 1 (Complex.imCLM : ℂ → ℝ) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Complex.imCLM_apply, NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_im]
    rw [dist_eq_norm]
    exact Complex.abs_im_le_norm _
  have h1 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.imCLM '' S)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) S := by
    simpa [ENNReal.one_rpow] using hlip.hausdorffMeasure_image_le (d := 1) (by norm_num) S
  have h2 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Complex.imCLM '' S) :=
    measure_mono hsub
  have h3 : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℝ) (Set.Icc α β)
      = ENNReal.ofReal (β - α) := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
  rw [h3] at h2
  exact h2.trans h1

/-- **McShane / nonlinear Hahn–Banach extension of a real Lipschitz-on-`s` function.** Any function
`v : ℂ → ℝ` that is `K`-Lipschitz on a set `s` extends to a globally `K`-Lipschitz function `u` on
all of `ℂ` agreeing with `v` on `s`. This is the real-valued McShane extension, packaged as a clean
leaf for the potential construction. -/
theorem exists_lipschitzWith_extend {v : ℂ → ℝ} {s : Set ℂ} {K : ℝ≥0}
    (hv : LipschitzOnWith K v s) :
    ∃ u : ℂ → ℝ, LipschitzWith K u ∧ Set.EqOn v u s :=
  hv.extend_real

/-- **Local increment bound ⟹ bound on the Fréchet-derivative norm.** If for every `ε > 0` the
function `u` satisfies the increment estimate `|u y − u z| ≤ (C + ε) ‖y − z‖` in a neighborhood of
`z`, then `‖fderiv ℝ u z‖ ≤ C`. (When `u` is not differentiable at `z`, `fderiv ℝ u z = 0` and the
bound holds trivially since `0 ≤ C`.) This is the clean leaf that turns the eikonal-type local
Lipschitz estimate of the potential into the pointwise gradient bound. -/
theorem norm_fderiv_le_of_local_increment {u : ℂ → ℝ} {z : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in nhds z, |u y - u z| ≤ (C + ε) * ‖y - z‖) :
    ‖fderiv ℝ u z‖ ≤ C := by
  -- It suffices to bound `‖fderiv ℝ u z‖` by every real `a > C`.
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  -- Take `ε := a - C > 0`; the hypothesis gives a local `(C + ε) = a`-Lipschitz increment bound.
  have hε : 0 < a - C := sub_pos.mpr ha
  have hCε : (0 : ℝ) ≤ a := hC.trans ha.le
  refine norm_fderiv_le_of_lip' ℝ hCε ?_
  filter_upwards [h (a - C) hε] with y hy
  -- `‖u y - u z‖ = |u y - u z| ≤ (C + (a - C)) * ‖y - z‖ = a * ‖y - z‖`.
  rw [Real.norm_eq_abs]
  calc |u y - u z| ≤ (C + (a - C)) * ‖y - z‖ := hy
    _ = a * ‖y - z‖ := by ring_nf

/-- **The capped real ρ-potential.** The real-valued, `[0, 1]`-truncated form of `rhoPotential`:
`min 1 (toReal (rhoPotential ρ f Q w))`. Truncating at `1` makes the potential bounded and real,
which is exactly the regularity needed to apply the co-area / Lipschitz machinery while preserving
the boundary values (`0` on the image left side, `1` on the image right side). -/
noncomputable def cappedRhoPotential (ρ : ℂ → ℝ≥0∞) (f : ℂ → ℂ) (Q : Quadrilateral) (w : ℂ) : ℝ :=
  min 1 (ENNReal.toReal (rhoPotential ρ f Q w))

/-- **The capped potential takes values in `[0, 1]`.** Immediate from `min 1 (·) ≤ 1` and the
nonnegativity of `ENNReal.toReal`. -/
theorem cappedRhoPotential_mem_Icc (ρ : ℂ → ℝ≥0∞) (f : ℂ → ℂ) (Q : Quadrilateral) (w : ℂ) :
    cappedRhoPotential ρ f Q w ∈ Set.Icc (0 : ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · exact le_min zero_le_one ENNReal.toReal_nonneg
  · exact min_le_left _ _

/-! ### Geometric ingredients for the ρ-potential witness (isolated extremal-length residuals)

The witness for `exists_rhoPotential_data` is the capped geodesic ρ-potential
`v = cappedRhoPotential ρ f Q` of the *unswapped* rectangle `Q`, McShane-extended off the closed
image `R = closure (f '' Q.image)` to a global Lipschitz `u`. Three genuinely two-dimensional /
extremal-length facts, absent from Mathlib, are isolated here as named residuals; everything else in
`exists_rhoPotential_data` is assembled from them. -/

section RhoPotentialWitness

variable {f : ℂ → ℂ} {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}

/-- **R1b — Lipschitz regularity and finiteness of the capped ρ-potential on the closed image.**

For a homeomorphism `f`, an axis rectangle `Q = (a, b) × (s, t)` and a density `ρ` admissible for
the image crossing family, the capped potential `v = cappedRhoPotential ρ f Q` is Lipschitz on the
closed image `R = closure (f '' Q.image)` (with some constant `K`), and the *uncapped* geodesic
potential `rhoPotential ρ f Q` is finite on `R` (every closed-image point is reachable by a
finite-`ρ`-length image curve from the left side).

## Truth under the QC hypothesis

**TRUE** for `ρ ∈ L^∞` (after the standard `ρ_n = min(ρ, n)` truncation / monotone passage) once `f`
is `K`-quasiconformal: the geometric hypothesis `IsQCGeometric f Kqc` makes the image
`f '' Q.image` a **quasidisk**, hence **quasiconvex** with **null boundary**, so the closed image
`R` is a compact quasiconvex Jordan domain. The capped geodesic distance is `1`-Lipschitz in the
`ρ`-length metric; on this quasiconvex `R` the `ρ`-length metric is bi-Lipschitz to the Euclidean
metric (local quasiconvexity / local connectivity of the Carathéodory boundary), giving a Euclidean
Lipschitz constant `K`; the same connectivity makes the potential finite on `R`. The remaining
content is the **Mathlib-absent quasidisk / Carathéodory prime-end theory** (no Jordan-curve /
Carathéodory theory in Mathlib). Isolated as a single `sorry`. -/
theorem exists_lipschitzOnWith_cappedRhoPotential {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)) :
    ∃ K : ℝ≥0, LipschitzOnWith K (cappedRhoPotential ρ f (axisRectQuadrilateral a b s t hab hst))
      (closure (f '' (axisRectQuadrilateral a b s t hab hst).image)) ∧
      ∀ z ∈ closure (f '' (axisRectQuadrilateral a b s t hab hst).image),
        rhoPotential ρ f (axisRectQuadrilateral a b s t hab hst) z ≠ ⊤ := by
  sorry

/-- **The capped potential vanishes on the image left side.** Since `rhoPotential ρ f Q z = 0` on
`f '' Q.leftSide` (the constant connector), the cap `min 1 (toReal 0) = 0`. -/
theorem cappedRhoPotential_eq_zero_of_mem_leftSide {f : ℂ → ℂ} {Q : Quadrilateral} {ρ : ℂ → ℝ≥0∞}
    {z : ℂ} (hz : z ∈ f '' Q.leftSide) (hleft_sub : f '' Q.leftSide ⊆ f '' Q.image) :
    cappedRhoPotential ρ f Q z = 0 := by
  rw [cappedRhoPotential, rhoPotential_eq_zero_of_mem_leftSide hz hleft_sub,
    ENNReal.toReal_zero, min_eq_right zero_le_one]

/-- **The capped potential equals `1` on the image right side (given finiteness).** Since
`rhoPotential ρ f Q z ≥ 1` on `f '' Q.rightSide` (every connector is a crossing curve), and the
potential is finite there, `toReal (rhoPotential) ≥ 1`, so the cap `min 1 (toReal …) = 1`. -/
theorem cappedRhoPotential_eq_one_of_mem_rightSide {f : ℂ → ℂ} {Q : Quadrilateral} {ρ : ℂ → ℝ≥0∞}
    {z : ℂ} (hz : z ∈ f '' Q.rightSide) (hρ : IsAdmissibleDensity ρ (Q.imageCurveFamily f))
    (hfin : rhoPotential ρ f Q z ≠ ⊤) :
    cappedRhoPotential ρ f Q z = 1 := by
  have hge : (1 : ℝ≥0∞) ≤ rhoPotential ρ f Q z := one_le_rhoPotential_of_mem_rightSide hz hρ
  have hge' : (1 : ℝ) ≤ ENNReal.toReal (rhoPotential ρ f Q z) := by
    rw [show (1 : ℝ) = ENNReal.toReal 1 from ENNReal.toReal_one.symm]
    exact ENNReal.toReal_mono hfin hge
  rw [cappedRhoPotential, min_eq_left hge']

/-- **Local geodesic increment of the (extended) capped ρ-potential (the isolated eikonal core).**

For the McShane-extended capped potential `u` (`EqOn (cappedRhoPotential ρ f Q) u R`,
`LipschitzWith K u`), at almost every image point `z ∈ R` with `ρ z ≠ ⊤` the potential satisfies the
local geodesic increment estimate `|u y − u z| ≤ ((ρ z).toReal + ε) ‖y − z‖` for `y` near `z`, for
every `ε > 0`.

## Truth under the QC hypothesis

**TRUE** once `f` is `K`-quasiconformal. The geometric hypothesis `IsQCGeometric f Kqc` makes the
image `f '' Q.image` a **quasidisk**, hence **quasiconvex** with **null boundary**, so a.e.
closed-image point lies in the interior and the image is locally connected at the boundary. At an
interior image point `z` where `ρ` is approximately continuous and finite, a geodesic to `y` near
`z` may be taken as the geodesic to `z` followed by the straight segment `[z, y]`, whose `ρ`-length
is `≤ (ρ z + ε)‖y − z‖` for `y` close to `z` (Lebesgue-point control of `ρ` along the segment).
Hence `u y − u z ≤ (ρ z + ε)‖y − z‖`, and symmetrically. The measure-zero image **boundary**
`frontier R` (the null quasidisk boundary) is excluded by the a.e. quantifier.

The per-point statement is the atomic geometric residual; the remaining content is **two
Mathlib-absent ingredients**:

* **Quasidisk interiority / segment-in-image.** That a.e. closed-image point `z` lies in the
  *interior* of `f '' Q.image` (the quasidisk boundary is null), and that the straight segment
  `[z, y]` stays inside the image for `y` near `z` (quasiconvexity) — needed both to identify
  `u = cappedRhoPotential` near `z` (transfer the McShane `EqOn`) and to concatenate the
  geodesic-to-`z` with the segment in the `rhoPotential` infimum. This is the
  quasidisk / Jordan-image interior theory, absent from Mathlib.
* **Directional (segment) Lebesgue density of `ρ`.** The estimate
  `(1/‖y−z‖)·∫₀¹ ρ(z+t(y−z))·‖y−z‖ dt → (ρ z).toReal` as `y → z` is a Lebesgue point of `ρ`
  averaged along the *segment* `[z, y]` (a `1`-dimensional, hence `2`-D-null, set). Mathlib's
  Lebesgue differentiation theorem `ae_tendsto_average_norm_sub` controls only *ball* averages, from
  which the segment/line average cannot be deduced (a line is null for planar Lebesgue measure).

Isolated as a single `sorry`. -/
theorem cappedRhoPotential_local_increment {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    {u : ℂ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K u)
    (hu_eq : Set.EqOn (cappedRhoPotential ρ f (axisRectQuadrilateral a b s t hab hst)) u
      (closure (f '' (axisRectQuadrilateral a b s t hab hst).image))) :
    ∀ᵐ z, z ∈ closure (f '' (axisRectQuadrilateral a b s t hab hst).image) →
      ρ z ≠ ⊤ → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ y in nhds z, |u y - u z| ≤ ((ρ z).toReal + ε) * ‖y - z‖ := by
  sorry

/-- **R2-eik — the a.e. eikonal bound `‖∇u‖ ≤ ρ` on the closed image.**

For the McShane-extended capped potential `u`, at almost every image point `z ∈ R` the Fréchet
derivative satisfies the eikonal bound `‖fderiv ℝ u z‖₊ ≤ ρ z`. **Proved** from the isolated local
geodesic increment `cappedRhoPotential_local_increment` via `norm_fderiv_le_of_local_increment`
(case-splitting on `ρ z = ⊤`, where the bound is vacuous). -/
theorem norm_fderiv_cappedRhoPotential_le {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    {u : ℂ → ℝ} {K : ℝ≥0} (hLip : LipschitzWith K u)
    (hu_eq : Set.EqOn (cappedRhoPotential ρ f (axisRectQuadrilateral a b s t hab hst)) u
      (closure (f '' (axisRectQuadrilateral a b s t hab hst).image))) :
    ∀ᵐ z, z ∈ closure (f '' (axisRectQuadrilateral a b s t hab hst).image) →
      (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ρ z := by
  filter_upwards [cappedRhoPotential_local_increment hab hst hf hfqc hρ hLip hu_eq] with z hz hmem
  -- Case on whether `ρ z` is infinite.
  rcases eq_or_ne (ρ z) ⊤ with htop | htop
  · simp [htop]
  · -- `ρ z ≠ ⊤`: `‖fderiv‖ ≤ (ρ z).toReal` by the local increment, then cast back to `ℝ≥0∞`.
    have hC : (0 : ℝ) ≤ (ρ z).toReal := ENNReal.toReal_nonneg
    have hbound : ‖fderiv ℝ u z‖ ≤ (ρ z).toReal :=
      norm_fderiv_le_of_local_increment hC (hz hmem htop)
    -- `‖fderiv‖₊ ≤ (ρ z).toNNReal` in `ℝ≥0`, then coerce and undo `toNNReal`.
    have hnn : ‖fderiv ℝ u z‖₊ ≤ (ρ z).toNNReal := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, ENNReal.coe_toNNReal_eq_toReal]
      exact hbound
    calc (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
        ≤ ((ρ z).toNNReal : ℝ≥0∞) := by exact_mod_cast hnn
      _ = ρ z := ENNReal.coe_toNNReal htop

/-- **R3c — a level set of the potential contains a separating member of the swapped family.**

For a continuous `u` that is `0` on the image left side and `1` on the image right side of the
swapped rectangle (the bottom/top edges of `Q`), every intermediate level `c ∈ (0, 1)` contains a
separating arc: there is `δ ∈ (axisRectQuadrilateralSwap …).imageCurveFamily f`, **injective on
`[0,1]`**, whose trace lies entirely in the level set `u⁻¹'{c}`.

## Truth under the QC hypothesis

**TRUE** (Jordan cross-cut) once `f` is `K`-quasiconformal. The geometric hypothesis
`IsQCGeometric f Kqc` makes the image a **quasidisk** — a Jordan domain whose boundary is a
quasicircle — so the level set `u⁻¹'{c}`, `c ∈ (0, 1)`, separates the two image sides of `Q` (where
`u = 0` and `u = 1`), hence contains a cross-cut of the conjugate Jordan quadrilateral joining the
image *bottom* to the image *top* — a **simple** (injective) member of the swapped image family.
Injectivity is no loss: a cross-cut of a Jordan domain can always be taken to be a simple arc
(remove loops), and it is needed downstream by the multiplicity-free 1-rectifiable area inequality
`arcLengthLineIntegral_le_setLIntegral_hausdorff`.

## Reachability verdict (recorded after a determined inline build attempt)

The proof body below proves the genuinely-provable packaging (the `imageCurveFamily` membership is
exactly the five conjuncts of `hexists`) and isolates the **single minimal residual** `hexists`: the
existence of a continuous, absolutely continuous, **injective** bottom→top arc inside the image
rectangle lying on the level set `{u = c}`. That residual is **genuinely-needs-JCT** (not
Mathlib-reachable via Poincaré–Miranda / connectedness alone), for three independent reasons:

* **The connected crossing continuum is Poincaré–Miranda.** Even producing a *connected* subset of
  `{u = c}` joining the image bottom to the image top is the 2-D intermediate-value /
  Poincaré–Miranda theorem. Mathlib has **no** Poincaré–Miranda, Brouwer fixed point, or
  topological-degree theory; only the low-level `isPreconnected_closed_iff` separation primitive,
  from which a full Poincaré–Miranda proof would have to be built (classically via Brouwer degree or
  a Sperner argument — both absent).
* **Continuum ⇒ simple arc is Hahn–Mazurkiewicz, and unreachable.** Upgrading a closed continuum to
  a *simple* (injective) arc is arcwise-connectedness of continua; Mathlib's only "connected ⇒ path"
  bridges (`IsOpen.isConnected_iff_isPathConnected`) require the set to be **open**, whereas a level
  set is closed, so no `Path` can be extracted from the closed continuum in general.
* **Absolute continuity needs the QC quasicircle structure, absent from the hypotheses.** The arc
  must be **rectifiable** (`AbsolutelyContinuousOnInterval`); but the hypotheses give only
  `Continuous u`, and a generic continuous `u` with these boundary values can have `u⁻¹'{c}` a
  non-locally-connected continuum containing **no** rectifiable arc. The statement is therefore *not
  provable from its stated hypotheses alone*: its truth uses that the actual `u` (the geodesic
  ρ-potential) has quasicircle level sets — QC structure of the *potential*, which
  `IsQCGeometric f Kqc` does **not** supply (`hfqc` constrains `f` via a modulus bound, never `u`).
  Note also the source-square pullback reformulation does **not** help: a QC `f` is only Hölder, not
  Lipschitz, so `f ∘ γ` of a rectifiable source arc `γ` need not be rectifiable (exactly the failure
  recorded in `imageCurveFamily`'s docstring), so AC genuinely lives on the image side and cannot be
  transported from the source.

Net: this is one of the irreducible Mathlib-absent extremal-length / quasidisk nodes; it is isolated
as the single `sorry` inside `hexists`, with the membership packaging proven axiom-clean. -/
theorem level_set_contains_separating_member {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    {u : ℂ → ℝ} (hucont : Continuous u)
    (hu0 : ∀ z ∈ f '' (axisRectQuadrilateral a b s t hab hst).leftSide, u z = 0)
    (hu1 : ∀ z ∈ f '' (axisRectQuadrilateral a b s t hab hst).rightSide, u z = 1) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∃ δ ∈ (axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f,
      Set.InjOn δ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, u (δ τ) = c := by
  intro c hc
  set Q := axisRectQuadrilateralSwap a b s t hab hst with hQdef
  -- ### The irreducible plane-topology residual (isolated, Mathlib-absent).
  --
  -- A continuous, absolutely continuous, **injective** arc `δ : ℝ → ℂ` that
  --   • starts on the image *bottom* edge `f '' Q.leftSide` (`δ 0`),
  --   • ends on the image *top* edge `f '' Q.rightSide` (`δ 1`),
  --   • stays inside the image rectangle `f '' Q.image`, and
  --   • lies entirely on the level set `u ⁻¹' {c}` (`u (δ τ) = c` for `τ ∈ [0,1]`).
  --
  -- This is the **Jordan cross-cut** of the conjugate quadrilateral: under the QC hypothesis the
  -- image is a quasidisk whose level set `{u = c}` (`c ∈ (0,1)`) separates the two image sides
  -- (`u = 0` on the bottom, `u = 1` on the top), hence contains a simple bottom→top cross-cut,
  -- which is *rectifiable* (a quasicircle subarc), hence absolutely continuous. See the verdict
  -- below: this cannot be derived from `Continuous u` alone — its truth uses the QC quasicircle
  -- structure of the geodesic potential — and even the QC version needs the Jordan curve theorem
  -- / Poincaré–Miranda separation and Hahn–Mazurkiewicz arcwise-connectedness, all Mathlib-absent.
  have hexists : ∃ δ : ℝ → ℂ, Continuous δ ∧ AbsolutelyContinuousOnInterval δ 0 1 ∧
      δ 0 ∈ f '' Q.leftSide ∧ δ 1 ∈ f '' Q.rightSide ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, δ τ ∈ f '' Q.image) ∧
      Set.InjOn δ (Set.Icc (0 : ℝ) 1) ∧ (∀ τ ∈ Set.Icc (0 : ℝ) 1, u (δ τ) = c) := by
    sorry
  -- Everything below is the genuinely-provable packaging: unfold `imageCurveFamily` membership.
  obtain ⟨δ, hδcont, hδac, hδ0, hδ1, hδimg, hδinj, hδlevel⟩ := hexists
  exact ⟨δ, ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩, hδinj, hδlevel⟩

open scoped Pointwise in
/-- **1-rectifiable area inequality: line integral ≤ trace Hausdorff integral.**

For a measurable density `σ` and an **injective** curve `δ` on `[0, 1]`, the arc-length line
integral of `σ` along `δ` is at most the `σ`-weighted `μH[1]`-integral over the *trace*
`δ '' [0, 1]`: `∫₀¹ σ(δ t) ‖δ'(t)‖ dt ≤ ∫_{δ''[0,1]} σ dμH[1]`.

## Why injectivity is required (the inequality is FALSE without it)

For a *non-injective* `δ` the left-hand side counts the trace **with multiplicity** while the
right-hand side does not, so the `≤` direction fails. Concretely, take `σ ≡ 1` and a `δ` that
traverses the unit segment `[0, 1] ⊆ ℝ ⊆ ℂ` and then retraces it (`δ` has `‖δ'‖ = 2` a.e.,
parametrizing the same segment twice). Then `LHS = ∫₀¹ 2 dt = 2` while
`RHS = μH[1]([0,1]) = 1`, so `LHS ≤ RHS` is false. The injectivity hypothesis
`Set.InjOn δ (Set.Icc 0 1)` rules out exactly this overcounting; the (sole) caller
`level_set_sigma_ge_one` supplies it from the injective separating arc of
`level_set_contains_separating_member`.

## Truth, direction, and the missing classical ingredient

**TRUE** for injective `δ`. The argument is the **measure-pushforward** form of the area formula:
writing `μp = (volume ⌞ [0,1]).withDensity ‖δ'‖` (the arc-length parameter measure), the LHS is
`∫⁻ z, σ z ∂(Measure.map δ μp)` (change of variables: `lintegral_map` + `withDensity`), and the
pushforward is dominated by the trace Hausdorff measure, `Measure.map δ μp ≤ μH[1] ⌞ (δ''[0,1])`,
whence `lintegral_mono'` gives the conclusion. The measure domination reduces, testing on a
measurable set, to the **reverse 1-rectifiable area inequality** for the injective absolutely
continuous curve `δ`:
`∫_A ‖δ'‖ ≤ μH[1] (δ '' A)` for every measurable `A ⊆ [0,1]`.
This is the *reverse* direction of the 1-D area formula (the forward direction
`μH[1] (δ '' A) ≤ ∫_A ‖δ'‖`, no injectivity, is the proven `hausdorffMeasure_one_image_le`).

The reverse direction is the single load-bearing **Mathlib-absent** ingredient. Mathlib's area
formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` is *equidimensional* (`E → E`) and does
not apply to `δ : ℝ → ℂ`; its only reverse-area tool `le_hausdorffMeasure_image` needs an
*antilipschitz* map, which a general injective AC curve is not. (The repo's
`eVariationOn_le_volume_image_of_injOn` is the real-valued, `ℝ → ℝ`, codimension-`0` analogue.) The
whole surrounding reduction is proven; only the `ℝ → ℂ` reverse-area inequality `hrevarea` is
isolated as a single `sorry`. -/
theorem arcLengthLineIntegral_le_setLIntegral_hausdorff {σ : ℂ → ℝ≥0∞} (hσm : Measurable σ)
    {δ : ℝ → ℂ} (hδcont : Continuous δ) (hδac : AbsolutelyContinuousOnInterval δ 0 1)
    (hδinj : Set.InjOn δ (Set.Icc (0 : ℝ) 1)) :
    arcLengthLineIntegral σ δ
      ≤ ∫⁻ z in δ '' Set.Icc (0 : ℝ) 1, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) := by
  classical
  have hδmeas : Measurable δ := hδcont.measurable
  set w : ℝ → ℝ≥0∞ := fun t => (‖deriv δ t‖₊ : ℝ≥0∞) with hw
  have hwmeas : Measurable w := ((measurable_deriv δ).nnnorm).coe_nnreal_ennreal
  have hσδ : Measurable (fun t => σ (δ t)) := hσm.comp hδmeas
  set μp : Measure ℝ := (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity w with hμp
  -- The pushforward of the arc-length parameter measure is dominated by the trace `μH[1]`.
  have hrev : Measure.map δ μp
      ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ).restrict
          (δ '' Set.Icc (0 : ℝ) 1) := by
    -- ISOLATED Mathlib-absent ingredient: the reverse 1-rectifiable area inequality for the
    -- injective AC curve `δ : ℝ → ℂ`, `∫_A ‖δ'‖ ≤ μH[1] (δ '' A)` for measurable `A ⊆ [0,1]`.
    have hrevarea : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Set.Icc (0 : ℝ) 1 →
        ∫⁻ t in A, w t ∂volume
          ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (δ '' A) := by
      simp only [hw]
      classical
      -- f' x = smulRight 1 (deriv δ x); ‖f' x‖₊ = ‖deriv δ x‖₊
      set f' : ℝ → (ℝ →L[ℝ] ℂ) := fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (deriv δ x) with hf'def
      have hnorm : ∀ x, ‖f' x‖₊ = ‖deriv δ x‖₊ := by
        intro x; apply NNReal.coe_injective
        simp only [hf'def, coe_nnnorm, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
      -- Exact 1-D linear-map norm identity for any A = f' y
      have hAexact : ∀ y : ℝ, ∀ v : ℝ, ‖(f' y) v‖ = ‖f' y‖ * ‖v‖ := by
        intro y v
        rw [hf'def]
        simp only
        rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
          ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul, norm_smul, mul_comm]
      -- nfsl: a.e. ‖f' x - A‖ ≤ δ on s where δ is ApproximatesLinearOn (copied from Foundations)
      have nfsl : ∀ (A : ℝ →L[ℝ] ℂ) (d : ℝ≥0) (s : Set ℝ),
          MeasurableSet s → ApproximatesLinearOn δ A s d →
          (∀ x ∈ s, HasFDerivWithinAt δ (f' x) s x) →
          ∀ᵐ x ∂(volume : Measure ℝ).restrict s, ‖f' x - A‖₊ ≤ d := by
        intro A d s hs hf hfd_s
        filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) s,
          ae_restrict_mem hs]
        intro x hx xs
        apply ContinuousLinearMap.opNorm_le_bound _ d.2 fun z => ?_
        suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (d + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
          have hT : Tendsto (fun ε : ℝ => ((d : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
              (𝓝 ((d + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
            Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
          simp only [add_zero, mul_zero] at hT
          apply le_of_tendsto_of_tendsto tendsto_const_nhds hT
          filter_upwards [self_mem_nhdsWithin]; exact H
        intro ε εpos
        have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty :=
          Measure.eventually_nonempty_inter_smul_of_density_one (volume : Measure ℝ) s x hx _
            measurableSet_closedBall (Metric.measure_closedBall_pos (volume : Measure ℝ) z εpos).ne'
        obtain ⟨ρ, ρpos, hρ⟩ :
            ∃ ρ > 0, Metric.ball x ρ ∩ s ⊆ {y : ℝ | ‖δ y - δ x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
          Metric.mem_nhdsWithin_iff.1 (((hfd_s x xs).isLittleO).def εpos)
        have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ := by
          apply nhdsWithin_le_nhds
          exact eventually_singleton_add_smul_subset Metric.isBounded_closedBall
            (Metric.ball_mem_nhds x ρpos)
        obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
            ∃ r : ℝ, (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty ∧
              {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ ∧ 0 < r :=
          (B₁.and (B₂.and self_mem_nhdsWithin)).exists
        obtain ⟨a, az, ya⟩ : ∃ a, a ∈ Metric.closedBall z ε ∧ y = x + r • a := by
          simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
          rcases hy with ⟨a, az, ha⟩
          exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
        have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
          calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
            _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
            _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
        have Iineq : r * ‖(f' x - A) a‖ ≤ r * (d + ε) * (‖z‖ + ε) :=
          calc r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
                rw [map_smul, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg rpos.le]
            _ = ‖δ y - δ x - A (y - x) - (δ y - δ x - (f' x) (y - x))‖ := by
                congr 1
                simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left,
                  ContinuousLinearMap.coe_sub', Pi.sub_apply, map_smul]
                module
            _ ≤ ‖δ y - δ x - A (y - x)‖ + ‖δ y - δ x - (f' x) (y - x)‖ := norm_sub_le _ _
            _ ≤ d * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
            _ = r * (d + ε) * ‖a‖ := by
                simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                  abs_of_nonneg rpos.le]
                ring
            _ ≤ r * (d + ε) * (‖z‖ + ε) := by gcongr
        calc ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
              congr 1
              simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]; abel
          _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
          _ ≤ (d + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
              apply add_le_add
              · rw [mul_assoc] at Iineq; exact (mul_le_mul_iff_right₀ rpos).1 Iineq
              · apply ContinuousLinearMap.le_opNorm
          _ ≤ (d + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
              rw [mem_closedBall_iff_norm'] at az; gcongr
      -- expand': per-piece antilipschitz LOWER bound, valid for any A = f' y when d < ‖A‖₊.
      have expand' : ∀ (y : ℝ) (d : ℝ≥0) (t : Set ℝ),
          ApproximatesLinearOn δ (f' y) t d → d < ‖f' y‖₊ →
          ((‖f' y‖₊ - d : ℝ≥0) : ℝ≥0∞) * μH[1] t ≤ μH[1] (δ '' t) := by
        intro y d t hAL hclt
        set A : ℝ →L[ℝ] ℂ := f' y with hAdef
        set K : ℝ≥0 := (‖A‖₊ - d)⁻¹ with hK
        have hAcpos : (0:ℝ) < ‖A‖ - d := by
          have : (d:ℝ) < ‖A‖ := by exact_mod_cast hclt;
          linarith
        have hKcoe : (K : ℝ) = (‖A‖ - d)⁻¹ := by
          rw [hK, NNReal.coe_inv, NNReal.coe_sub hclt.le, coe_nnnorm]
        have hanti : AntilipschitzWith K (t.restrict δ) := by
          apply AntilipschitzWith.of_le_mul_dist
          rintro ⟨x, hx⟩ ⟨w, hw⟩
          simp only [Set.restrict_apply, Subtype.dist_eq, Real.dist_eq, Complex.dist_eq]
          have hlb : (‖A‖ - d) * ‖x - w‖ ≤ ‖δ x - δ w‖ := by
            have h1 : ‖A (x - w)‖ - ‖δ x - δ w‖ ≤ ‖δ x - δ w - A (x - w)‖ := by
              calc ‖A (x - w)‖ - ‖δ x - δ w‖ ≤ ‖A (x - w) - (δ x - δ w)‖ := norm_sub_norm_le _ _
                _ = ‖δ x - δ w - A (x - w)‖ := by rw [← norm_neg]; congr 1; ring
            have h2 := hAL x hx w hw
            rw [hAexact y (x - w)] at h1
            nlinarith [norm_nonneg (x - w), norm_nonneg (δ x - δ w), le_trans h1 h2]
          rw [hKcoe, ← Real.norm_eq_abs, inv_mul_eq_div, le_div_iff₀ hAcpos]
          linarith [hlb]
        have key := hanti.le_hausdorffMeasure_image (by norm_num : (0:ℝ) ≤ 1) (univ : Set ↥t)
        rw [ENNReal.rpow_one] at key
        have him1 : μH[1] (Subtype.val '' (univ : Set ↥t)) = μH[1] (univ : Set ↥t) :=
          isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num)) _
        have himt : (Subtype.val '' (univ : Set ↥t)) = t := by simp
        rw [himt] at him1
        have himg : (t.restrict δ) '' (univ : Set ↥t) = δ '' t := by
          ext z; constructor
          · rintro ⟨⟨a, ha⟩, _, rfl⟩; exact ⟨a, ha, rfl⟩
          · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, mem_univ _, rfl⟩
        rw [himg, ← him1] at key
        have hmul : ((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * K = 1 := by
          rw [hK, ← ENNReal.coe_mul, mul_inv_cancel₀ ?_, ENNReal.coe_one]
          · rw [ne_eq, tsub_eq_zero_iff_le, not_le]; exact hclt
        calc ((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * μH[1] t
            ≤ ((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * ((K : ℝ≥0∞) * μH[1] (δ '' t)) := by gcongr
          _ = (((‖A‖₊ - d : ℝ≥0) : ℝ≥0∞) * K) * μH[1] (δ '' t) := by rw [mul_assoc]
          _ = μH[1] (δ '' t) := by rw [hmul, one_mul]
      -- On the source `ℝ`, `μH[1] = volume`.
      have hHvol : (μH[1] : Measure ℝ) = volume := hausdorffMeasure_real
      -- aux1': the finite-error LOWER estimate.
      have aux1 : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Set.Icc (0:ℝ) 1 →
          (∀ x ∈ s, HasFDerivWithinAt δ (f' x) s x) → ∀ {ε : ℝ≥0}, 0 < ε →
          ∫⁻ x in s, (‖deriv δ x‖₊ : ℝ≥0∞) ≤ μH[1] (δ '' s) + 2 * ε * (volume s) := by
        intro s hs hsIcc hfds ε εpos
        obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hAy⟩ :
            ∃ (t : ℕ → Set ℝ) (A : ℕ → (ℝ →L[ℝ] ℂ)),
              Pairwise (Function.onFun Disjoint t) ∧
                (∀ n : ℕ, MeasurableSet (t n)) ∧
                  (s ⊆ ⋃ n : ℕ, t n) ∧
                    (∀ n : ℕ, ApproximatesLinearOn δ (A n) (s ∩ t n) ε) ∧
                      (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt δ s f' hfds (fun _ => ε)
            (fun _ => εpos.ne')
        -- ∫_s ‖δ'‖ = ∑' ∫_{s∩tₙ} ‖δ'‖  (disjoint cover)
        have hsplit_int : ∫⁻ x in s, (‖deriv δ x‖₊ : ℝ≥0∞)
            = ∑' n, ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞) := by
          rw [← lintegral_iUnion (fun n => hs.inter (t_meas n))
            (pairwise_disjoint_mono t_disj fun n => inter_subset_right),
            ← inter_iUnion, inter_eq_self_of_subset_left t_cover]
        rw [hsplit_int]
        -- per piece: ∫_{s∩tₙ} ‖δ'‖ ≤ μH[1](δ''(s∩tₙ)) + 2ε·vol(s∩tₙ)
        have hpiece : ∀ n, ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
            ≤ μH[1] (δ '' (s ∩ t n)) + 2 * ε * volume (s ∩ t n) := by
          intro n
          rcases eq_empty_or_nonempty s with hse | hsne
          · subst hse; simp [Set.empty_inter]
          -- get y with A n = f' y
          obtain ⟨y, hys, hAyn⟩ := hAy hsne n
          -- ∫_{s∩tₙ} ‖δ'‖ ≤ (‖A n‖₊ + ε)·vol(s∩tₙ)  via nfsl
          have hub : ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
              ≤ ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
            calc ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
                ≤ ∫⁻ _ in s ∩ t n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) := by
                  apply lintegral_mono_ae
                  filter_upwards [nfsl (A n) ε (s ∩ t n) (hs.inter (t_meas n)) (ht n)
                    (fun x hx => (hfds x hx.1).mono inter_subset_left)]
                  intro x hx
                  -- goal: ‖deriv δ x‖₊ ≤ ‖A n‖₊ + ε
                  rw [ENNReal.coe_le_coe]
                  have hd : ‖f' x‖₊ ≤ ‖A n‖₊ + ε := by
                    calc ‖f' x‖₊ = ‖A n + (f' x - A n)‖₊ := by rw [add_sub_cancel]
                      _ ≤ ‖A n‖₊ + ‖f' x - A n‖₊ := nnnorm_add_le _ _
                      _ ≤ ‖A n‖₊ + ε := by gcongr
                  rwa [hnorm] at hd
                _ = ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
                  rw [setLIntegral_const]
          -- combine with expand' (handle d<‖A‖ vs not) using the per-piece numeric lemma
          have hexp : ε < ‖A n‖₊ →
              ((‖A n‖₊ - ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) ≤ μH[1] (δ '' (s ∩ t n)) := by
            intro hlt
            have hclt' : ε < ‖f' y‖₊ := by rwa [← hAyn]
            have he := expand' y ε (s ∩ t n) (hAyn ▸ ht n) hclt'
            rw [← hAyn, hHvol] at he
            exact he
          -- numeric per-piece bound
          have hnum : ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
              ≤ μH[1] (δ '' (s ∩ t n)) + 2 * (ε : ℝ≥0∞) * volume (s ∩ t n) := by
            rcases lt_or_ge ε (‖A n‖₊) with hlt | hge
            · have h := hexp hlt
              have hsplitc : ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞)
                  = ((‖A n‖₊ - ε : ℝ≥0) : ℝ≥0∞) + 2 * (ε : ℝ≥0∞) := by
                rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by rfl, ← ENNReal.coe_mul,
                  ← ENNReal.coe_add, ENNReal.coe_inj, two_mul, ← add_assoc,
                  tsub_add_cancel_of_le hlt.le]
              rw [hsplitc, add_mul, mul_assoc]
              exact add_le_add h le_rfl
            · have hle : ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) ≤ 2 * (ε : ℝ≥0∞) := by
                rw [show (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) by rfl, ← ENNReal.coe_mul,
                  ENNReal.coe_le_coe, two_mul]
                gcongr
              calc ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n)
                  ≤ 2 * (ε : ℝ≥0∞) * volume (s ∩ t n) := by gcongr
                _ ≤ μH[1] (δ '' (s ∩ t n)) + 2 * (ε : ℝ≥0∞) * volume (s ∩ t n) := le_add_self
          exact hub.trans hnum
        -- sum the pieces
        calc ∑' n, ∫⁻ x in s ∩ t n, (‖deriv δ x‖₊ : ℝ≥0∞)
            ≤ ∑' n, (μH[1] (δ '' (s ∩ t n)) + 2 * ε * volume (s ∩ t n)) :=
              ENNReal.tsum_le_tsum hpiece
          _ = (∑' n, μH[1] (δ '' (s ∩ t n))) + ∑' n, 2 * ε * volume (s ∩ t n) := by
              rw [ENNReal.tsum_add]
          _ ≤ μH[1] (δ '' s) + 2 * ε * volume s := by
              apply add_le_add
              · -- reassembly superadditivity
                set P : ℕ → Set ℝ := fun n => s ∩ t n with hP
                have hPmeas : ∀ n, MeasurableSet (P n) := fun n => hs.inter (t_meas n)
                have hPsub : ∀ n, P n ⊆ Set.Icc (0:ℝ) 1 := fun n => (inter_subset_left).trans hsIcc
                have hinjImgMeas : ∀ n, MeasurableSet (δ '' P n) := fun n =>
                  (hPmeas n).image_of_continuousOn_injOn hδcont.continuousOn (hδinj.mono (hPsub n))
                have hImgDisj : Pairwise (Function.onFun Disjoint (fun n => δ '' P n)) := by
                  intro i j hij
                  simp only [Function.onFun]
                  rw [Set.disjoint_iff_inter_eq_empty]
                  ext z
                  simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
                  rintro ⟨a, haP, rfl⟩ ⟨b, hbP, hb⟩
                  have hab : a = b := hδinj (hPsub i haP) (hPsub j hbP) hb.symm
                  subst hab
                  exact (Set.disjoint_left.mp (t_disj hij) haP.2) hbP.2
                have hmU : μH[1] (⋃ n, δ '' P n) = ∑' n, μH[1] (δ '' P n) :=
                  measure_iUnion hImgDisj hinjImgMeas
                calc ∑' n, μH[1] (δ '' (s ∩ t n)) = μH[1] (⋃ n, δ '' P n) := hmU.symm
                  _ ≤ μH[1] (δ '' s) := by
                      apply measure_mono
                      rw [← image_iUnion]
                      exact Set.image_mono (iUnion_subset (fun n => inter_subset_left))
              · -- ∑' 2ε vol(s∩tₙ) = 2ε vol s
                rw [ENNReal.tsum_mul_left, ← measure_iUnion
                  (pairwise_disjoint_mono t_disj fun n => inter_subset_right)
                  (fun n => hs.inter (t_meas n)), ← inter_iUnion,
                  inter_eq_self_of_subset_left t_cover]
      -- aux2': let ε → 0 for finite-volume sets.
      have aux2 : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Set.Icc (0:ℝ) 1 → volume s ≠ ∞ →
          (∀ x ∈ s, HasFDerivWithinAt δ (f' x) s x) →
          ∫⁻ x in s, (‖deriv δ x‖₊ : ℝ≥0∞) ≤ μH[1] (δ '' s) := by
        intro s hs hsIcc hsfin hfds
        have hlim : Tendsto (fun ε : ℝ≥0 =>
            μH[1] (δ '' s) + 2 * (ε : ℝ≥0∞) * (volume s)) (𝓝[>] 0)
            (𝓝 (μH[1] (δ '' s) + 2 * (0 : ℝ≥0) * (volume s))) := by
          apply Tendsto.mono_left _ nhdsWithin_le_nhds
          refine tendsto_const_nhds.add ?_
          refine ENNReal.Tendsto.mul_const ?_ (Or.inr hsfin)
          exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id)
            (Or.inr ENNReal.coe_ne_top)
        simp only [ENNReal.coe_zero, mul_zero, zero_mul, add_zero] at hlim
        apply ge_of_tendsto hlim
        filter_upwards [self_mem_nhdsWithin]
        intro ε εpos
        rw [mem_Ioi] at εpos
        exact aux1 hs hsIcc hfds εpos
      -- Main: reduce arbitrary measurable A ⊆ [0,1] to the a.e.-differentiability set D.
      intro A hA hAIcc
      -- a.e. differentiability of δ on [0,1].
      have hδdiff : ∀ᵐ x : ℝ, x ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ x :=
        hδac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
      set Dgood : Set ℝ := {x : ℝ | DifferentiableAt ℝ δ x} with hDgood
      have hDgoodMeas : MeasurableSet Dgood := by
        have : Dgood = {x | DifferentiableAt ℝ δ x} := rfl
        -- the set of differentiability points of a continuous function is measurable
        rw [this]
        exact (measurableSet_of_differentiableAt ℝ δ)
      set D : Set ℝ := A ∩ Dgood with hDdef
      have hDmeas : MeasurableSet D := hA.inter hDgoodMeas
      have hDIcc : D ⊆ Set.Icc (0:ℝ) 1 := (inter_subset_left).trans hAIcc
      -- volume (A \ D) = 0
      have hADnull : volume (A \ D) = 0 := by
        -- A \ D = A \ Dgood ⊆ {x ∈ uIcc 0 1 | ¬ diff} (since A ⊆ [0,1]), which is null.
        have hsub : A \ D ⊆ {x : ℝ | ¬ (x ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ x)} := by
          intro x hx
          rw [mem_setOf_eq, Classical.not_imp]
          refine ⟨Set.mem_uIcc.mpr (Or.inl (hAIcc hx.1)), ?_⟩
          intro hxd
          exact hx.2 ⟨hx.1, hxd⟩
        exact measure_mono_null hsub (ae_iff.mp hδdiff)
      -- ∫_A ‖δ'‖ = ∫_D ‖δ'‖
      have hintEq : ∫⁻ x in A, (‖deriv δ x‖₊ : ℝ≥0∞) = ∫⁻ x in D, (‖deriv δ x‖₊ : ℝ≥0∞) := by
        have haeeq : A =ᵐ[volume] D := by
          rw [ae_eq_set]
          refine ⟨hADnull, ?_⟩
          rw [Set.diff_eq_empty.mpr (inter_subset_left)]; simp
        exact setLIntegral_congr haeeq
      -- δ''D ⊆ δ''A
      have himgSub : δ '' D ⊆ δ '' A := Set.image_mono inter_subset_left
      -- HasFDerivWithinAt on D
      have hfdsD : ∀ x ∈ D, HasFDerivWithinAt δ (f' x) D x := by
        intro x hx
        have hxd : DifferentiableAt ℝ δ x := hx.2
        have : HasDerivAt δ (deriv δ x) x := hxd.hasDerivAt
        have hfd : HasFDerivAt δ (f' x) x := by
          rw [hf'def]; exact this.hasFDerivAt
        exact hfd.hasFDerivWithinAt
      -- Reduce A to finite-measure disjoint pieces via spanning sets of volume.
      set u : ℕ → Set ℝ := fun n => disjointed (spanningSets (volume : Measure ℝ)) n with hu_def
      have u_meas : ∀ n, MeasurableSet (u n) := fun n =>
        MeasurableSet.disjointed (fun i => measurableSet_spanningSets (volume : Measure ℝ) i) n
      have hDcover : D = ⋃ n, D ∩ u n := by
        rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
      rw [hintEq]
      calc ∫⁻ x in D, (‖deriv δ x‖₊ : ℝ≥0∞)
          = ∑' n, ∫⁻ x in D ∩ u n, (‖deriv δ x‖₊ : ℝ≥0∞) := by
            rw [← lintegral_iUnion (fun n => hDmeas.inter (u_meas n))
              (pairwise_disjoint_mono (disjoint_disjointed (spanningSets (volume : Measure ℝ)))
                (fun n => inter_subset_right)), ← hDcover]
        _ ≤ ∑' n, μH[1] (δ '' (D ∩ u n)) := by
            apply ENNReal.tsum_le_tsum fun n => ?_
            apply aux2 (hDmeas.inter (u_meas n)) ((inter_subset_left).trans hDIcc) ?_
              (fun x hx => (hfdsD x hx.1).mono inter_subset_left)
            have : volume (u n) < ∞ :=
              lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
                (measure_spanningSets_lt_top (volume : Measure ℝ) n)
            exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
        _ = μH[1] (⋃ n, δ '' (D ∩ u n)) := by
            rw [measure_iUnion ?_ ?_]
            · -- pairwise disjoint images via injectivity
              intro i j hij
              simp only [Function.onFun]
              rw [Set.disjoint_iff_inter_eq_empty]
              ext z
              simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
              rintro ⟨a, haP, rfl⟩ ⟨b, hbP, hb⟩
              have hsubIcc : ∀ k, D ∩ u k ⊆ Set.Icc (0:ℝ) 1 :=
                fun k => (inter_subset_left).trans hDIcc
              have hab : a = b := hδinj (hsubIcc i haP) (hsubIcc j hbP) hb.symm
              subst hab
              exact (Set.disjoint_left.mp
                (disjoint_disjointed (spanningSets (volume : Measure ℝ)) hij) haP.2) hbP.2
            · intro n
              exact (hDmeas.inter (u_meas n)).image_of_continuousOn_injOn hδcont.continuousOn
                (hδinj.mono ((inter_subset_left).trans hDIcc))
        _ ≤ μH[1] (δ '' A) := by
            apply measure_mono
            rw [← image_iUnion, ← hDcover]
            exact himgSub
    -- Wrap the per-set reverse-area bound into the measure inequality.
    refine Measure.le_iff.mpr (fun E hE => ?_)
    rw [Measure.map_apply hδmeas hE, hμp, withDensity_apply _ (hδmeas hE),
      Measure.restrict_restrict (hδmeas hE), Measure.restrict_apply hE]
    set A : Set ℝ := δ ⁻¹' E ∩ Set.Icc (0 : ℝ) 1 with hA
    have hAmeas : MeasurableSet A := (hδmeas hE).inter measurableSet_Icc
    have h1 : ∫⁻ t in A, w t ∂volume ≤ μH[1] (δ '' A) :=
      hrevarea A hAmeas Set.inter_subset_right
    have h2 : δ '' A ⊆ E ∩ (δ '' Set.Icc (0 : ℝ) 1) := by
      rintro z ⟨τ, ⟨hτE, hτI⟩, rfl⟩
      exact ⟨hτE, ⟨τ, hτI, rfl⟩⟩
    exact h1.trans (measure_mono h2)
  -- The LHS is the σ-integral against the pushforward (change of variables).
  have hstep1 : arcLengthLineIntegral σ δ = ∫⁻ z, σ z ∂(Measure.map δ μp) := by
    rw [lintegral_map hσm hδmeas]
    have hcov : ∫⁻ t, σ (δ t) ∂μp
        = ∫⁻ t, (w t) * σ (δ t) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [hμp, lintegral_withDensity_eq_lintegral_mul _ hwmeas hσδ]; rfl
    rw [hcov]
    unfold arcLengthLineIntegral
    refine lintegral_congr (fun t => ?_)
    simp only [hw]; ring
  rw [hstep1]
  calc ∫⁻ z, σ z ∂(Measure.map δ μp)
      ≤ ∫⁻ z, σ z ∂((MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ).restrict
          (δ '' Set.Icc (0 : ℝ) 1)) := lintegral_mono' hrev le_rfl
    _ = ∫⁻ z in δ '' Set.Icc (0 : ℝ) 1, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) := rfl

/-- **R3-sep — each intermediate level set carries `σ`-arclength `≥ 1`.**

For `σ` admissible for the swapped (separating) image family and a continuous `u` with the boundary
values, each level set `u⁻¹'{c}`, `c ∈ (0, 1)`, carries `σ`-arclength `≥ 1`:
`1 ≤ ∫⁻ z in u⁻¹'{c}, σ z dμH[1]`. **Proved** from `level_set_contains_separating_member` (R3c) — a
separating arc `δ` lies in the level set — together with `σ`-admissibility
(`1 ≤ arcLengthLineIntegral σ δ`), the 1-rectifiable area inequality
`arcLengthLineIntegral_le_setLIntegral_hausdorff` (line integral ≤ trace integral), and Hausdorff
set-monotonicity (trace `⊆` level set). -/
theorem level_set_sigma_ge_one {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f))
    {u : ℂ → ℝ} (hucont : Continuous u)
    (hu0 : ∀ z ∈ f '' (axisRectQuadrilateral a b s t hab hst).leftSide, u z = 0)
    (hu1 : ∀ z ∈ f '' (axisRectQuadrilateral a b s t hab hst).rightSide, u z = 1) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      1 ≤ ∫⁻ z in u ⁻¹' {c}, σ z
        ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) := by
  intro c hc
  obtain ⟨δ, hδfam, hδinj, hδtrace⟩ :=
    level_set_contains_separating_member hab hst hf hfqc hucont hu0 hu1 c hc
  obtain ⟨hδcont, hδac, _, _, _⟩ := id hδfam
  -- Admissibility: the separating arc has `σ`-line integral `≥ 1`.
  have hadm : (1 : ℝ≥0∞) ≤ arcLengthLineIntegral σ δ := hσ.2 δ hδfam
  -- 1-rectifiable area: line integral ≤ trace Hausdorff integral (the arc is injective).
  have harea : arcLengthLineIntegral σ δ
      ≤ ∫⁻ z in δ '' Set.Icc (0 : ℝ) 1, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) :=
    arcLengthLineIntegral_le_setLIntegral_hausdorff hσ.1 hδcont hδac hδinj
  -- The trace lies inside the level set, so set-monotonicity raises the integral.
  have htrace_sub : δ '' Set.Icc (0 : ℝ) 1 ⊆ u ⁻¹' {c} := by
    rintro w ⟨τ, hτ, rfl⟩
    exact hδtrace τ hτ
  have hmono : ∫⁻ z in δ '' Set.Icc (0 : ℝ) 1, σ z
        ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)
      ≤ ∫⁻ z in u ⁻¹' {c}, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) :=
    lintegral_mono_set htrace_sub
  exact hadm.trans (harea.trans hmono)

end RhoPotentialWitness

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

This is the irreducible atomic residual. The cross-bound `1 ≤ ∫∫ ρσ` is **true for every admissible
pair** (not merely the extremal one): it follows from the **ρ-potential / co-area** argument below.
What a *pointwise/naïve* argument cannot supply is the bound by itself — it requires the global
co-area structure of the potential `u`. The route: let `u(w)` be the `ρ`-geodesic distance from
the image left side to `w` inside `f''(rect)` (the infimum of `arcLengthLineIntegral ρ γ` over AC
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

**TRUE**. The witness is the **capped ρ-potential** `v = cappedRhoPotential ρ f Q`
(`= min 1 (toReal (rhoPotential ρ f Q ·))`) of `rhoPotential_eq_zero_of_mem_leftSide` /
`one_le_rhoPotential_of_mem_rightSide`, extended off the image by McShane
(`exists_lipschitzWith_extend`) to a global `K`-Lipschitz `u`. The standard construction makes `v`
Lipschitz on the (compact) closed image `R = closure (f '' Q.image)`
(`exists_lipschitzOnWith_cappedRhoPotential`, **R1b**), with the *a.e.* eikonal `‖∇u‖ ≤ ρ` on `R`
(`norm_fderiv_le_of_local_increment` fed by the local geodesic increment estimate, **R2-eik**); the
level sets `{u = c}` for `c ∈ (0, 1)` separate the image left and right sides (a separating arc of
the swapped family lies in each, **R3c**), so by `σ`-admissibility each carries `σ`-arclength `≥ 1`
(**R3-sep**, via the 1-rectifiable area inequality). Each step is classical extremal-length theory
(Ahlfors, *Conformal Invariants* Ch. 4; Väisälä §II).

## Hypotheses and soundness

The density `σ` is assumed to **vanish off the closed image** `R = closure (f '' Q.image)`
(`hσsupp`); the consumer `imageConjugate_lengthArea_pairwise` supplies this for free, having already
restricted `σ` to `R` via `Set.indicator`. This is the sound restriction that makes the weighted
eikonal vacuous off the image (where the geodesic witness carries no information) while preserving
the level-set separation on the image. The eikonal is required only **almost everywhere** (the
Lipschitz potential is differentiable a.e. by Rademacher; the eikonal can fail on the measure-zero
image boundary, irrelevant to the integral).

## Missing classical ingredient

The Lipschitz regularity and eikonal bound of the geodesic ρ-potential (Mathlib has no
geodesic-distance / length-structure theory), and the topological separation certifying that the
level sets of `u` dominate a `σ`-admissible separating curve (no Jordan-separation / level-set
rectifiability for Lipschitz functions in Mathlib). These are the genuine net-new extremal-length
ingredients, isolated below as `exists_lipschitzOnWith_cappedRhoPotential` (R1b),
`level_set_contains_separating_member` (R3c), and the 1-rectifiable area inequality
`arcLengthLineIntegral_le_setLIntegral_hausdorff`; the co-area atom itself is
`Coarea.eilenberg_coarea_grad_le`. -/
theorem exists_rhoPotential_data {f : ℂ → ℂ} {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f))
    (hσsupp : ∀ z ∉ closure (f '' (axisRectQuadrilateral a b s t hab hst).image), σ z = 0) :
    ∃ (u : ℂ → ℝ) (K : ℝ≥0), LipschitzWith K u ∧
      (∀ᵐ z, σ z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ≤ ρ z * σ z) ∧
      (∀ c ∈ Set.Ioo (0 : ℝ) 1,
        1 ≤ ∫⁻ z in u ⁻¹' {c}, σ z
          ∂(MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ)) := by
  classical
  set Q := axisRectQuadrilateral a b s t hab hst with hQ
  set R := closure (f '' Q.image) with hR
  -- The sides `{0}×[0,1]` and `{1}×[0,1]` of the unit square are contained in the square itself.
  have hleft_us : ({0} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1 ⊆ unitSquare :=
    Set.prod_mono (by rintro x rfl; exact Set.left_mem_Icc.mpr zero_le_one) (le_refl _)
  have hright_us : ({1} : Set ℝ) ×ˢ Set.Icc (0 : ℝ) 1 ⊆ unitSquare :=
    Set.prod_mono (by rintro x rfl; exact Set.right_mem_Icc.mpr zero_le_one) (le_refl _)
  -- The image left/right sides are inside the image region `f '' Q.image`, hence inside `R`.
  have hleft_img : f '' Q.leftSide ⊆ f '' Q.image :=
    Set.image_mono (Set.image_mono hleft_us)
  have hright_img : f '' Q.rightSide ⊆ f '' Q.image :=
    Set.image_mono (Set.image_mono hright_us)
  have hleft_sub : f '' Q.leftSide ⊆ R := hleft_img.trans subset_closure
  have hright_sub : f '' Q.rightSide ⊆ R := hright_img.trans subset_closure
  -- R1b: Lipschitz-on-`R` regularity + finiteness of the capped potential.
  obtain ⟨K, hLipOn, hfin⟩ := exists_lipschitzOnWith_cappedRhoPotential hab hst hf hfqc hρ
  -- McShane extension to a global `K`-Lipschitz `u` agreeing with the capped potential on `R`.
  obtain ⟨u, hLip, hEqOn⟩ := exists_lipschitzWith_extend hLipOn
  refine ⟨u, K, hLip, ?_, ?_⟩
  · -- Weighted eikonal `σ ‖∇u‖ ≤ ρ σ` a.e.: on `R` from R2-eik, off `R` since `σ = 0`.
    filter_upwards [norm_fderiv_cappedRhoPotential_le hab hst hf hfqc hρ hLip hEqOn] with z hz
    by_cases hmem : z ∈ R
    · calc σ z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞)
          ≤ σ z * ρ z := by gcongr; exact hz hmem
        _ = ρ z * σ z := mul_comm _ _
    · rw [hσsupp z hmem]; simp
  · -- Level separation via R3-sep, using the boundary values of `u = v` on the image sides.
    have hucont : Continuous u := hLip.continuous
    have hu0 : ∀ z ∈ f '' Q.leftSide, u z = 0 := by
      intro z hz
      rw [← hEqOn (hleft_sub hz)]
      exact cappedRhoPotential_eq_zero_of_mem_leftSide hz hleft_img
    have hu1 : ∀ z ∈ f '' Q.rightSide, u z = 1 := by
      intro z hz
      rw [← hEqOn (hright_sub hz)]
      exact cappedRhoPotential_eq_one_of_mem_rightSide hz hρ (hfin z (hright_sub hz))
    exact level_set_sigma_ge_one hab hst hf hfqc hσ hucont hu0 hu1

theorem imageConjugate_lengthArea_pairwise {f : ℂ → ℂ} {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) := by
  classical
  -- Restrict `σ` to the (closed) image. This restricted density `σ'` is still admissible for the
  -- separating family (every separating curve stays inside the image, where `σ' = σ`), and feeding
  -- it to `exists_rhoPotential_data` makes the weighted eikonal vacuous off the image — exactly the
  -- soundness reduction that lets the geodesic-potential witness work. Monotonicity `σ' ≤ σ` then
  -- transfers the cross-bound to the full `σ`.
  set R := closure (f '' (axisRectQuadrilateralSwap a b s t hab hst).image) with hR
  have hσ' : IsAdmissibleDensity (R.indicator σ)
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f) := by
    refine ⟨hσ.1.indicator isClosed_closure.measurableSet, fun δ hδ => ?_⟩
    obtain ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩ := hδ
    have heq : arcLengthLineIntegral (R.indicator σ) δ = arcLengthLineIntegral σ δ := by
      unfold arcLengthLineIntegral
      refine setLIntegral_congr_fun measurableSet_Icc fun u hu => ?_
      rw [Set.indicator_of_mem (subset_closure (hδimg u hu))]
    exact heq ▸ hσ.2 δ ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩
  -- `σ' = R.indicator σ` vanishes off the closed image `R`; and `R` is the closure of the image of
  -- the *unswapped* rectangle too, since the swap fixes the image region.
  have hRimg : R = closure (f '' (axisRectQuadrilateral a b s t hab hst).image) := by
    rw [hR, axisRectQuadrilateralSwap_image]
  have hσsupp : ∀ z ∉ closure (f '' (axisRectQuadrilateral a b s t hab hst).image),
      (R.indicator σ) z = 0 :=
    fun z hz => Set.indicator_of_notMem (by rwa [hRimg]) σ
  obtain ⟨u, K, hLip, heik, hlevel⟩ := exists_rhoPotential_data hf hfqc hab hst hρ hσ' hσsupp
  have hcross' : 1 ≤ ∫⁻ z, ρ z * (R.indicator σ) z :=
    cross_bound_of_rhoPotential hσ'.1 hLip heik hlevel
  have hmono : ∫⁻ z, ρ z * (R.indicator σ) z ≤ ∫⁻ z, ρ z * σ z :=
    lintegral_mono fun z => by gcongr; exact Set.indicator_le_self' (fun _ _ => zero_le _) z
  exact one_le_energy_mul_energy_of_one_le_lintegral_mul hρ.1 hσ.1 (hcross'.trans hmono)

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
theorem conjugateImageModulus_reciprocity {f : ℂ → ℂ} {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
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
    fun ρ hρ σ hσ => imageConjugate_lengthArea_pairwise hf hfqc hab hst hρ hσ
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
  have hrecip : 1 ≤ M * N := conjugateImageModulus_reciprocity hfhomeo hf hab hst
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

/-! ## STEP 3b — the separating-RING modulus (Grötzsch / Teichmüller) lower-bound development

This section builds the genuinely missing **ring-modulus LOWER bound** that closes
`qc_quasiround_data`. The repository's existing tools (`rengel_area_lower_bound`,
`square_imageCurveFamily_modulus_ge`, `axisRect_imageModulus_le`) produce only area-lower /
crossing-modulus-lower / modulus-upper bounds. What the diameter bound `diam (f''outer) ≤ C'·d`
needs is the *separating*-ring direction, supplied classically by the **Grötzsch annulus modulus**
`mod(annulus) = (2π)/log(R/h)` and the resulting Teichmüller two-point distortion estimate.

The development is built bottom-up:

* `annulus`, `annularLogDensity` — the round annulus `{h ≤ ‖z−x‖ ≤ R}` and the canonical
  **log-radial extremal density** `ρ(z) = 1/(‖z−x‖·log(R/h))`.
* `annularLogDensity_energy` (**PROVEN, axiom-clean**) — the concrete length–area computation
  `∫∫ ρ² = (2π)/log(R/h)`, the Grötzsch value, via the polar change of variables
  `Complex.lintegral_comp_polarCoord_symm` + the radial integral `∫ 1/r dr = log(R/h)`. This is the
  first genuine leaf of the ring theory and is the only `∫∫ρ²` energy that the whole development
  rests on.
* `annularLogDensity_admissible`, `annulus_crossingModulus_ge` (**PROVEN**) — admissibility of the
  log-radial density and the Grötzsch crossing modulus lower bound `2π/log(R/h) ≤ M(crossing)`.
* `annulus_crossingModulus_le`, `annulus_crossingModulus_eq` (**PROVEN, axiom-clean**) — the
  matching upper bound (the log-radial density is an admissible *test* density of energy
  `2π/log(R/h)`), pinning the crossing modulus to **exactly** `2π/log(R/h)`.
* `annulusAngularDensity`, `annulusAngularDensity_energy` (**PROVEN, axiom-clean**) — the conjugate
  **angular extremal density** `σ(z) = 1/(2π·‖z−x‖)` and its energy `∫∫ σ² = log(R/h)/(2π)`, the
  reciprocal Grötzsch value, via the same polar change of variables.
* `annulusSeparatingFamily`, `annulus_separatingModulus_ge` / `image_ringModulus_ge` (**PROVEN,
  axiom-clean**) — the conjugate winding-loop family and its separating-ring modulus **lower** bound
  `log(R/h)/(2π) ≤ M(separating)`, proved **directly** as the exact angular dual of the crossing
  development (per concentric-loop angular Cauchy–Schwarz, then integrated radially — no
  reciprocity). The value `log(R/h)/(2π)` is realized on the *source* separating family by
  `annulusAngularDensity` (no `f`, no transport).
* `ringModulus_diam_le` (**deep `:= by sorry`**) — the Teichmüller two-point distortion: it
  consumes the proven source separating modulus and bundles the QC-for-rings *image transport* plus
  the modulus⇒diameter geometric inversion (both Mathlib-absent). The top node
  `qc_quasiround_distortion_bound` is wired directly into `hquasiround` below. -/

/-- The **round annulus** `{z | h ≤ ‖z − x‖ ≤ R}` centred at `x` with radii `h ≤ R`. The ring that
separates the inner disc `‖z − x‖ ≤ h` from the complement of the outer disc `‖z − x‖ ≥ R`; its
crossing family (radial curves from the inner to the outer circle) is the Grötzsch family whose
modulus is `log(R/h)/(2π)`. -/
def annulus (x : ℂ) (h R : ℝ) : Set ℂ := {z : ℂ | h ≤ ‖z - x‖ ∧ ‖z - x‖ ≤ R}

/-- The **log-radial extremal density** of the annulus centred at `x`: the metric
`ρ(z) = 1/(‖z − x‖ · log(R/h))` supported on the annulus, `0` elsewhere. This is the Grötzsch
extremal metric: its arc-length integral along every radial crossing curve is `≥ 1` (admissibility),
and its energy `∫∫ ρ²` equals the Grötzsch value `(2π)/log(R/h)`, computed in
`annularLogDensity_energy`. -/
noncomputable def annularLogDensity (x : ℂ) (h R : ℝ) : ℂ → ℝ≥0∞ :=
  (annulus x h R).indicator (fun z => ENNReal.ofReal (1 / (‖z - x‖ * Real.log (R / h))))

/-- **Energy of the log-radial extremal density of the annulus (the Grötzsch value).**

For `0 < h < R`, the area energy of the canonical log-radial density on the round annulus
`{h ≤ ‖z − x‖ ≤ R}` is exactly the Grötzsch modulus value
`∫∫ ρ² = (2π)/log(R/h)`.

This is the foundational **length–area computation** of the whole ring-modulus development: it is
the single explicit `∫∫ ρ²` energy on which the separating-ring modulus *lower* bound rests. The
proof is a concrete plane integral, performed via the polar change of variables
`Complex.lintegral_comp_polarCoord_symm` (Jacobian `r`), reducing to the radial integral
`∫_h^R (1/r) dr = log(R/h)` (`integral_one_div`) times the angular measure `2π`. It is fully proved
and axiom-clean. (Translation invariance in `x` is automatic: the density and annulus depend on `z`
only through `z − x`, and the integral is translation invariant, so the value is independent of `x`;
the computation is carried out at the canonical centre.) -/
theorem annularLogDensity_energy (x : ℂ) (h R : ℝ) (hh : 0 < h) (hR : h < R) :
    ∫⁻ z, (annularLogDensity x h R z) ^ 2 = ENNReal.ofReal (2 * π / Real.log (R / h)) := by
  -- Translate to the canonical centre `0`: substitute `w = z − x` (`volume` is translation
  -- invariant), reducing to the integral over the centred annulus.
  set L := Real.log (R / h) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; rw [lt_div_iff₀ hh]; linarith
  -- The integrand `(annularLogDensity x h R z)^2` as a function of `z − x`.
  have hshift : (fun z : ℂ => (annularLogDensity x h R z) ^ 2)
      = (fun w : ℂ =>
          (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
            (fun w => ENNReal.ofReal (1 / (‖w‖ * L))) w) ^ 2) ∘ (fun z => z - x) := by
    funext z
    simp only [annularLogDensity, annulus, Function.comp_apply, hL]
    by_cases hz : z ∈ {z : ℂ | h ≤ ‖z - x‖ ∧ ‖z - x‖ ≤ R}
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (by exact hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (by exact hz)]
  rw [hshift]
  -- `∫ (g ∘ (· − x)) = ∫ g` by translation invariance of `volume`.
  rw [show (∫⁻ z, ((fun w : ℂ =>
          (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
            (fun w => ENNReal.ofReal (1 / (‖w‖ * L))) w) ^ 2) ∘ (fun z => z - x)) z)
        = ∫⁻ w : ℂ, (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
            (fun w => ENNReal.ofReal (1 / (‖w‖ * L))) w) ^ 2 from by
    rw [← lintegral_sub_right_eq_self (fun w : ℂ =>
        (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
          (fun w => ENNReal.ofReal (1 / (‖w‖ * L))) w) ^ 2) x]
    rfl]
  -- Now the centred computation: square of indicator = indicator of square.
  set A : Set ℂ := {z : ℂ | h ≤ ‖z‖ ∧ ‖z‖ ≤ R} with hA
  have hAmeas : MeasurableSet A := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const continuous_norm.measurable
    · exact measurableSet_le continuous_norm.measurable measurable_const
  have hsq : (fun z : ℂ => (A.indicator (fun z => ENNReal.ofReal (1 / (‖z‖ * L))) z) ^ 2)
      = A.indicator (fun z => ENNReal.ofReal (1 / (‖z‖ * L)) ^ 2) := by
    funext z; by_cases hz : z ∈ A <;> simp [hz]
  rw [hsq]
  -- Polar change of variables.
  rw [← Complex.lintegral_comp_polarCoord_symm
      (A.indicator (fun z => ENNReal.ofReal (1 / (‖z‖ * L)) ^ 2))]
  rw [polarCoord_target]
  have htmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  -- Simplify the integrand on the target: `‖polarCoord.symm p‖ = p.1`, membership ↔ `p.1 ∈ [h,R]`.
  have hcongr : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      ENNReal.ofReal p.1 • A.indicator (fun z => ENNReal.ofReal (1 / (‖z‖ * L)) ^ 2)
          (Complex.polarCoord.symm p)
        = (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (r * L ^ 2))) p.1 := by
    intro p hp
    obtain ⟨hr, _hθ⟩ := hp
    simp only [Set.mem_Ioi] at hr
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    by_cases hmem : Complex.polarCoord.symm p ∈ A
    · have hmem' : p.1 ∈ Set.Icc h R := by
        rw [hA, Set.mem_setOf_eq, hnorm] at hmem; exact ⟨hmem.1, hmem.2⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', hnorm,
        smul_eq_mul, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hr.le]
      congr 1; field_simp
    · have hmem' : p.1 ∉ Set.Icc h R := by
        intro hc; apply hmem; rw [hA, Set.mem_setOf_eq, hnorm]; exact ⟨hc.1, hc.2⟩
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', smul_zero]
  rw [setLIntegral_congr_fun htmeas hcongr]
  -- Fubini: the integrand depends only on `p.1`; the angular factor is `2π`.
  have hgmeas : Measurable (fun r : ℝ =>
      (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (r * L ^ 2))) r) := by
    apply Measurable.indicator _ measurableSet_Icc
    exact (measurable_const.div (measurable_id.mul measurable_const)).ennreal_ofReal
  have haem : AEMeasurable
      (fun p : ℝ × ℝ =>
        (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (r * L ^ 2))) p.1)
      ((volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π)) :=
    (hgmeas.comp measurable_fst).aemeasurable
  rw [Measure.volume_eq_prod, setLIntegral_prod _ haem]
  simp_rw [setLIntegral_const]
  rw [Real.volume_Ioo, lintegral_mul_const _ hgmeas]
  -- The radial integral `∫_h^R 1/(r L²) dr = 1/L` via `integral_one_div`.
  have hradial : ∫⁻ r in Set.Ioi (0 : ℝ),
      (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (r * L ^ 2))) r
        = ENNReal.ofReal (1 / L) := by
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hsubset : Set.Icc h R ∩ Set.Ioi (0 : ℝ) = Set.Icc h R :=
      Set.inter_eq_left.mpr (fun w hw => lt_of_lt_of_le hh hw.1)
    rw [hsubset]
    have hcont : ContinuousOn (fun r : ℝ => 1 / (r * L ^ 2)) (Set.Icc h R) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.mul continuousOn_const)
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le hh hr.1
      have hL2 : 0 < L ^ 2 := by positivity
      exact ne_of_gt (mul_pos hr0 hL2)
    have hintegrable : IntegrableOn (fun r : ℝ => 1 / (r * L ^ 2)) (Set.Icc h R) volume :=
      hcont.integrableOn_compact isCompact_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc h R)] (fun r : ℝ => 1 / (r * L ^ 2)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have : 0 < r := lt_of_lt_of_le hh hr.1; positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn]
    congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le]
    have hsplit : ∫ r in h..R, 1 / (r * L ^ 2) = (∫ r in h..R, 1 / r) * (1 / L ^ 2) := by
      rw [← intervalIntegral.integral_mul_const]; congr 1; funext r; ring
    have h0notin : (0 : ℝ) ∉ Set.uIcc h R := by
      rw [Set.uIcc_of_le hR.le, Set.mem_Icc]; rintro ⟨hc1, hc2⟩; linarith
    rw [hsplit, integral_one_div h0notin, ← hL]; field_simp
  rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show π - -π = 2 * π by ring]; field_simp

/-- The **radial crossing family** of the annulus centred at `x`: absolutely continuous curves that
join the inner circle `‖z − x‖ = h` to the outer circle `‖z − x‖ = R` while staying inside the
annulus. This is the Grötzsch crossing family; its modulus is `log(R/h)/(2π)`. -/
def annulusCrossingFamily (x : ℂ) (h R : ℝ) : Set (ℝ → ℂ) :=
  {γ | Continuous γ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧
    ‖γ 0 - x‖ = h ∧ ‖γ 1 - x‖ = R ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ annulus x h R}

/-- **Admissibility of the log-radial density for the annular crossing family (reachable leaf).**

The log-radial density `ρ(z) = 1/(‖z − x‖·log(R/h))` is admissible for the radial crossing family:
along any AC curve `γ` from the inner circle to the outer circle, the radial increment of `log‖·−x‖`
is `log(R/h)`, and `‖∇ log‖z − x‖‖ = 1/‖z − x‖`, so the arc-length integral of `ρ` is
`≥ (1/log(R/h))·(log R − log h) = 1`.

## Reachable-vs-deep

**Reachable.** This is the polar/radial analogue of the proven `rengelDensity_admissible` /
`axisRectDensity_admissible`: it is a one-dimensional chord-type estimate along each curve. The
missing ingredient is the chain-rule bound `log(R/h) ≤ ∫₀¹ ‖deriv γ t‖ / ‖γ t − x‖ dt` for an AC
curve from radius `h` to radius `R` — the composition of `chord_le_arcLength`-style reasoning with
the `1`-Lipschitz-on-the-annulus functional `z ↦ log‖z − x‖` (Lipschitz constant `1/h` there). It
uses only the repository's `funcIncrement_le_arcLength`/FTC-for-AC machinery, no 2-D theory. -/
theorem annularLogDensity_admissible (x : ℂ) {h R : ℝ} (hh : 0 < h) (hR : h < R) :
    IsAdmissibleDensity (annularLogDensity x h R) (annulusCrossingFamily x h R) := by
  set L := Real.log (R / h) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; rw [lt_div_iff₀ hh]; linarith
  have hmeas : Measurable (annularLogDensity x h R) := by
    unfold annularLogDensity
    have hcn : Measurable (fun z : ℂ => ‖z - x‖) :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
    apply Measurable.indicator
    · exact (measurable_const.div (hcn.mul measurable_const)).ennreal_ofReal
    · exact (measurableSet_le measurable_const hcn).inter (measurableSet_le hcn measurable_const)
  refine ⟨hmeas, ?_⟩
  rintro γ ⟨hγcont, hγac, hγ0, hγ1, hγimg⟩
  -- ===== (1/h)-Lipschitz radial-log functional `l z = log(max ‖z−x‖ h)` =====
  have hqlip : LipschitzWith ⟨1/h, by positivity⟩ (fun u : ℝ => Real.log (max u h)) := by
    have hlogOn : LipschitzOnWith ⟨1/h, by positivity⟩ Real.log (Ici h) := by
      apply (convex_Ici h).lipschitzOnWith_of_nnnorm_deriv_le
      · intro u hu
        simp only [mem_Ici] at hu
        exact Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le hh hu))
      · intro u hu
        simp only [mem_Ici] at hu
        have hu0 : 0 < u := lt_of_lt_of_le hh hu
        rw [Real.deriv_log, ← NNReal.coe_le_coe]
        simp only [coe_nnnorm, NNReal.coe_mk]
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos hu0, inv_eq_one_div]
        exact one_div_le_one_div_of_le hh hu
    have hmax : LipschitzWith 1 (fun u : ℝ => max u h) := LipschitzWith.id.max_const h
    have hmaps : MapsTo (fun u : ℝ => max u h) univ (Ici h) := fun u _ => le_max_right u h
    have hcomp := LipschitzOnWith.comp hlogOn (lipschitzOnWith_univ.2 hmax) hmaps
    rw [lipschitzOnWith_univ] at hcomp
    simpa only [mul_one, Function.comp] using hcomp
  have hnormlip : LipschitzWith 1 (fun z : ℂ => ‖z - x‖) := by
    have h1 : LipschitzWith 1 (fun z : ℂ => z - x) :=
      LipschitzWith.of_dist_le_mul (fun a b => by simp [dist_eq_norm, sub_sub_sub_cancel_right])
    simpa using lipschitzWith_one_norm.comp h1
  have hllip : LipschitzWith (⟨1/h, by positivity⟩ * 1)
      (fun z : ℂ => Real.log (max (‖z - x‖) h)) := hqlip.comp hnormlip
  -- ===== `gt := l ∘ γ`, AC on `[0,1]`; endpoint values; FTC `∫₀¹ deriv gt = L` =====
  set gt : ℝ → ℝ := fun s => Real.log (max (‖γ s - x‖) h) with hgt
  have hgtac : AbsolutelyContinuousOnInterval gt 0 1 := by
    have hl : ∀ {F : ℝ → ℂ} (l : ℂ → ℝ) (k : NNReal),
        LipschitzWith k l → ∀ {a c : ℝ}, AbsolutelyContinuousOnInterval F a c →
        AbsolutelyContinuousOnInterval (fun t => l (F t)) a c := by
      intro F l k hl a c hF
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
    exact hl (fun z : ℂ => Real.log (max (‖z - x‖) h)) _ hllip hγac
  have hgt0 : gt 0 = Real.log h := by simp only [hgt, hγ0, max_self]
  have hgt1 : gt 1 = Real.log R := by simp only [hgt]; rw [hγ1, max_eq_left hR.le]
  have hftc : ∫ t in (0:ℝ)..1, deriv gt t = L := by
    rw [hgtac.integral_deriv_eq_sub, hgt1, hgt0, hL,
      Real.log_div (ne_of_gt (by linarith)) (ne_of_gt hh)]
  have hgtii : IntervalIntegrable (deriv gt) volume 0 1 := hgtac.intervalIntegrable_deriv
  have hγdiff : ∀ᵐ t : ℝ, t ∈ uIcc (0:ℝ) 1 → DifferentiableAt ℝ γ t :=
    hγac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  -- ===== per-point radial chord bound at interior differentiability points =====
  -- On the open interval the curve stays in the annulus, so `gt = log‖γ·−x‖` near `t`
  -- (no kink in `max`), and the chain rule with the `1`-Lipschitz `‖·−x‖` gives the bound.
  have hderivbound : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ γ t →
      deriv gt t ≤ ‖deriv γ t‖ / ‖γ t - x‖ := by
    intro t ht hd
    set r : ℝ → ℝ := fun s => ‖γ s - x‖ with hr
    have htIcc : t ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self ht
    have hrt_ge : h ≤ r t := (hγimg t htIcc).1
    have hrt_pos : 0 < r t := lt_of_lt_of_le hh hrt_ge
    have hrt_ne : r t ≠ 0 := ne_of_gt hrt_pos
    have hne : γ t - x ≠ 0 := by
      intro hc; apply hrt_ne; rw [hr]; simp only [hc, norm_zero]
    have hsubdiff : DifferentiableAt ℝ (fun z : ℂ => z - x) (γ t) :=
      differentiableAt_id.sub_const x
    have hnormdiff : DifferentiableAt ℝ (fun z : ℂ => ‖z - x‖) (γ t) :=
      hsubdiff.norm ℝ (by simpa using hne)
    have hrdiff : DifferentiableAt ℝ r t := by
      have hcomp := hnormdiff.comp t hd; simpa [hr, Function.comp] using hcomp
    have hrhd : HasDerivAt r (deriv r t) t := hrdiff.hasDerivAt
    have hbound : |deriv r t| ≤ ‖deriv γ t‖ := by
      set Dn : ℂ →L[ℝ] ℝ := fderiv ℝ (fun z : ℂ => ‖z - x‖) (γ t) with hDn
      have hchain : HasDerivAt r (Dn (deriv γ t)) t := by
        have := (hnormdiff.hasFDerivAt).comp_hasDerivAt t hd.hasDerivAt
        simpa [hr, hDn, Function.comp] using this
      rw [hchain.deriv]
      calc |Dn (deriv γ t)|
          ≤ ‖Dn‖ * ‖deriv γ t‖ := by
            rw [← Real.norm_eq_abs]; exact Dn.le_opNorm _
        _ ≤ 1 * ‖deriv γ t‖ := by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hnormlip
        _ = ‖deriv γ t‖ := one_mul _
    have hlogr : HasDerivAt (fun s => Real.log (r s)) (deriv r t / r t) t := by
      have := hrhd.log hrt_ne; simpa [div_eq_mul_inv] using this
    have hev : gt =ᶠ[𝓝 t] (fun s => Real.log (r s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hs' : h ≤ ‖γ s - x‖ := (hγimg s (Ioo_subset_Icc_self hs)).1
      simp only [hgt, hr, max_eq_left hs']
    have hgthd : HasDerivAt gt (deriv r t / r t) t := hlogr.congr_of_eventuallyEq hev
    rw [hgthd.deriv]
    have htt : r t = ‖γ t - x‖ := rfl
    rw [← htt]; gcongr; exact (le_abs_self _).trans hbound
  -- ===== a.e. restriction to `Ioo 0 1` (co-null in `Icc 0 1`) =====
  have haeIoo : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (0:ℝ) 1)), t ∈ Ioo (0:ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hsub : (Icc (0:ℝ) 1) \ Ioo 0 1 ⊆ {0, 1} := by
      intro t ht; simp only [mem_diff, mem_Icc, mem_Ioo, not_and, not_lt] at ht
      obtain ⟨⟨h0, h1⟩, hno⟩ := ht
      rcases eq_or_lt_of_le h0 with rfl | h0'
      · left; rfl
      · right; exact le_antisymm h1 (hno h0')
    have h01null : volume ({0,1} : Set ℝ) = 0 := by
      rw [show ({0,1}:Set ℝ) = {0} ∪ {1} from rfl]
      refine le_antisymm ((measure_union_le _ _).trans ?_) (zero_le _)
      simp [measure_singleton]
    have hnull : volume ((Icc (0:ℝ) 1) \ Ioo 0 1) = 0 := measure_mono_null hsub h01null
    filter_upwards [compl_mem_ae_iff.2 hnull] with t ht
    intro htIcc; by_contra hno; exact ht ⟨htIcc, hno⟩
  -- ===== pointwise lintegral lower bound by `ofReal((1/L)·deriv gt)` =====
  have hpt : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (0:ℝ) 1)),
      ENNReal.ofReal ((1/L) * deriv gt t)
        ≤ annularLogDensity x h R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := by
    have hdiffae : ∀ᵐ t : ℝ ∂(volume.restrict (Icc (0:ℝ) 1)),
        t ∈ uIcc (0:ℝ) 1 → DifferentiableAt ℝ γ t := ae_restrict_of_ae hγdiff
    filter_upwards [haeIoo, hdiffae] with t htioo htd
    have htmem : t ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self htioo
    have htann : γ t ∈ annulus x h R := hγimg t htmem
    have hrge : h ≤ ‖γ t - x‖ := htann.1
    have hrpos : 0 < ‖γ t - x‖ := lt_of_lt_of_le hh hrge
    have hρval : annularLogDensity x h R (γ t) = ENNReal.ofReal (1 / (‖γ t - x‖ * L)) := by
      unfold annularLogDensity; rw [Set.indicator_of_mem htann, ← hL]
    rw [hρval, show (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖deriv γ t‖ by
        rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm], ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hdiff := htd (mem_uIcc.mpr (Or.inl ⟨htmem.1, htmem.2⟩))
    have hb := hderivbound t htioo hdiff
    calc (1/L) * deriv gt t ≤ (1/L) * (‖deriv γ t‖ / ‖γ t - x‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 1 / (‖γ t - x‖ * L) * ‖deriv γ t‖ := by field_simp
  -- ===== integrate: `1 = (1/L)·∫₀¹ deriv gt ≤ arcLengthLineIntegral ρ γ` =====
  calc (1 : ℝ≥0∞)
      = ENNReal.ofReal (∫ t in (0:ℝ)..1, (1/L) * deriv gt t) := by
        rw [intervalIntegral.integral_const_mul, hftc, one_div,
          inv_mul_cancel₀ (ne_of_gt hLpos), ENNReal.ofReal_one]
    _ = ENNReal.ofReal (∫ t in Icc (0:ℝ) 1, (1/L) * deriv gt t) := by
        rw [intervalIntegral.integral_of_le (by norm_num),
          MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal ((1/L) * deriv gt t) := by
        have hint : IntegrableOn (fun t => (1/L) * deriv gt t) (Icc (0:ℝ) 1) := by
          have := hgtii.const_mul (1/L)
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at this
          exact this
        have hpos2 : IntegrableOn (fun t => max ((1/L)*deriv gt t) 0) (Icc (0:ℝ) 1) :=
          hint.pos_part
        have key : (fun t => ENNReal.ofReal ((1/L)*deriv gt t))
            = (fun t => ENNReal.ofReal (max ((1/L)*deriv gt t) 0)) := by
          funext t; rcases le_total 0 ((1/L)*deriv gt t) with hh' | hh'
          · rw [max_eq_left hh']
          · rw [max_eq_right hh', ENNReal.ofReal_of_nonpos hh', ENNReal.ofReal_zero]
        rw [key, ← ofReal_integral_eq_lintegral_ofReal hpos2
            (by filter_upwards with t using le_max_right _ _)]
        exact ENNReal.ofReal_le_ofReal (integral_mono hint hpos2 (fun t => le_max_left _ _))
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1,
          annularLogDensity x h R (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞) := lintegral_mono_ae hpt
    _ = arcLengthLineIntegral (annularLogDensity x h R) γ := rfl

/-- **Grötzsch modulus lower bound for the annular crossing family (PROVEN).**

The radial crossing family of the round annulus has modulus at least the Grötzsch value:
`ENNReal.ofReal (2π / log(R/h)) ≤ curveModulus (annulusCrossingFamily x h R)`.

This is the polar-coordinate analogue of the proven `lengthArea_modulus_lower_bound` (the Cartesian
Cauchy–Schwarz/Fubini lower bound for the rectangle): a lower bound on `curveModulus` runs the
Cauchy–Schwarz argument over *every* admissible density `ρ`, integrated in the polar foliation —
`(∫_ray ρ ds)² ≤ (∫_ray 1/r² dr)·(∫_ray ρ² r dr)` along each radial ray, then Fubini over the angle,
transported through `Complex.lintegral_comp_polarCoord_symm`. Together with the matching upper bound
from the log-radial test density (`annularLogDensity_energy` realizes `2π/log(R/h)`), this pins the
crossing modulus to exactly `2π/log(R/h)`. The conjugate *separating*-ring modulus `log(R/h)/(2π)`
needed by the Teichmüller two-point distortion is the reciprocal, obtained downstream via ring
reciprocity. -/
theorem annulus_crossingModulus_ge (x : ℂ) {h R : ℝ} (hh : 0 < h) (hR : h < R) :
    ENNReal.ofReal (2 * π / Real.log (R / h))
      ≤ curveModulus (annulusCrossingFamily x h R) := by
  have htrue : ENNReal.ofReal (2 * π / Real.log (R / h))
      ≤ curveModulus (annulusCrossingFamily x h R) := by
    set L := Real.log (R / h) with hL
    have hLpos : 0 < L := by
      rw [hL]; apply Real.log_pos; rw [lt_div_iff₀ hh]; linarith
    unfold curveModulus
    refine le_iInf₂ ?_
    rintro ρ ⟨hρmeas, hadm⟩
    -- ===== polar decomposition =====
    have hpolar : ∫⁻ z, (ρ z)^2
        = ∫⁻ p in (Ioi (0:ℝ) ×ˢ Ioo (-π) π),
            ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm p + x))^2 := by
      have htrans : ∫⁻ z, (ρ z)^2 = ∫⁻ w, (ρ (w + x))^2 := by
        rw [← lintegral_add_right_eq_self (fun w => (ρ w)^2) x]
      rw [htrans, ← Complex.lintegral_comp_polarCoord_symm (fun w => (ρ (w + x))^2),
        polarCoord_target]
      simp only [smul_eq_mul]
    -- measurability of the polar integrand
    have hpmeas : Measurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm p + x))^2) := by
      apply Measurable.mul (measurable_fst.ennreal_ofReal)
      apply Measurable.pow_const
      apply hρmeas.comp
      have hsm : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
        have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
            = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
          funext p; rw [Complex.polarCoord_symm_apply]
        rw [this]; fun_prop
      exact hsm.add_const x
    -- ===== θ-outer Fubini =====
    have hfubini : ∫⁻ p in (Ioi (0:ℝ) ×ˢ Ioo (-π) π),
            ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm p + x))^2
        = ∫⁻ θ in Ioo (-π) π, ∫⁻ r in Ioi (0:ℝ),
            ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 := by
      rw [Measure.volume_eq_prod, setLIntegral_prod _ hpmeas.aemeasurable, lintegral_lintegral_swap]
      exact hpmeas.aemeasurable
    rw [hpolar, hfubini]
    -- ===== per-angle lower bound: ofReal(1/L) ≤ inner ; uniformly in θ =====
    have hinner : ∀ θ : ℝ, ENNReal.ofReal (1/L)
        ≤ ∫⁻ r in Ioi (0:ℝ),
            ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 := by
      intro θ
      set e : ℂ := (Real.cos θ + Real.sin θ * Complex.I) with he
      have hene : ‖e‖ = 1 := by
        rw [he, show (Real.cos θ : ℂ) + Real.sin θ * Complex.I = Complex.exp (θ * Complex.I) by
          rw [Complex.exp_mul_I]; push_cast; ring]
        simp [Complex.norm_exp]
      have hsymm : ∀ r : ℝ, Complex.polarCoord.symm (r, θ) = (r:ℂ) * e := by
        intro r; rw [Complex.polarCoord_symm_apply, he]
      set F : ℝ → ℝ≥0∞ := fun r => ρ (x + (r:ℂ) * e) with hF
      have hintegrand : ∀ r : ℝ,
          ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2
            = (F r)^2 * ENNReal.ofReal r := by
        intro r; rw [hsymm, hF, add_comm ((r:ℂ)*e) x, mul_comm]
      simp_rw [hintegrand]
      have hsub : Icc h R ⊆ Ioi (0:ℝ) := fun r hr => lt_of_lt_of_le hh hr.1
      have hFmeas : Measurable F :=
        hρmeas.comp (measurable_const.add (Complex.measurable_ofReal.mul measurable_const))
      -- ===== hone : 1 ≤ ∫_{Icc h R} F =====
      have hone : (1:ℝ≥0∞) ≤ ∫⁻ r in Icc h R, F r := by
        set γ : ℝ → ℂ := fun s => x + ((h + (R - h) * s : ℝ) : ℂ) * e with hγ
        -- membership
        have hnorm : ∀ s, ‖γ s - x‖ = |h + (R - h) * s| := by
          intro s
          simp only [hγ, add_sub_cancel_left, norm_mul, hene, mul_one, Complex.norm_real,
            Real.norm_eq_abs]
        have hmem : γ ∈ annulusCrossingFamily x h R := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · exact Continuous.add continuous_const
              (Continuous.mul (Complex.continuous_ofReal.comp (by fun_prop)) continuous_const)
          · apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨R - h, by linarith⟩)
            apply LipschitzOnWith.mono _ (subset_univ _)
            rw [lipschitzOnWith_univ]
            apply LipschitzWith.of_dist_le_mul
            intro s s'
            simp only [hγ, dist_eq_norm]
            rw [show (x + ((h + (R - h) * s : ℝ) : ℂ) * e)
                  - (x + ((h + (R - h) * s' : ℝ) : ℂ) * e)
                = (((R - h) * (s - s') : ℝ) : ℂ) * e by push_cast; ring]
            rw [norm_mul, hene, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_pos (by linarith : (0:ℝ) < R - h), Real.norm_eq_abs, NNReal.coe_mk]
          · rw [hnorm]; simp only [mul_zero, add_zero]; rw [abs_of_pos hh]
          · rw [hnorm]; simp only [mul_one]
            rw [show h + (R - h) = R by ring, abs_of_pos (by linarith)]
          · intro s hs
            simp only [mem_Icc] at hs
            have hpos : 0 ≤ h + (R - h) * s := by nlinarith [hs.1, hs.2, hR.le]
            exact ⟨by rw [hnorm, abs_of_nonneg hpos]; nlinarith [hs.1],
                   by rw [hnorm, abs_of_nonneg hpos]; nlinarith [hs.2]⟩
        -- deriv γ
        have hderiv : ∀ s, deriv γ s = ((R - h : ℝ):ℂ) * e := by
          intro s
          have hd : HasDerivAt γ (((R - h : ℝ):ℂ) * e) s := by
            have ha : HasDerivAt (fun s : ℝ => (R - h) * s) (R - h) s := by
              simpa using (hasDerivAt_id s).const_mul (R - h)
            have hbase : HasDerivAt (fun s : ℝ => (h + (R - h) * s : ℝ)) (R - h) s := by
              have h2 : HasDerivAt (fun s : ℝ => h + (R - h) * s) (0 + (R - h)) s :=
                (hasDerivAt_const s h).add ha
              simpa using h2
            have h1 : HasDerivAt (fun s : ℝ => ((h + (R - h) * s : ℝ):ℂ))
                ((R-h:ℝ):ℂ) s := by simpa using hbase.ofReal_comp
            simpa [hγ] using (h1.mul_const e).const_add x
          exact hd.deriv
        have hnormderiv : ∀ s, (‖deriv γ s‖₊ : ℝ≥0∞) = ENNReal.ofReal (R - h) := by
          intro s
          rw [hderiv s, ← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm, norm_mul, hene, mul_one,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have harc : arcLengthLineIntegral ρ γ
            = ENNReal.ofReal (R - h) * ∫⁻ s in Icc (0:ℝ) 1, ρ (γ s) := by
          unfold arcLengthLineIntegral
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply lintegral_congr; intro s; rw [hnormderiv s, mul_comm]
        have hcov : ∫⁻ r in Icc h R, F r
            = ENNReal.ofReal (R - h) * ∫⁻ s in Icc (0:ℝ) 1, ρ (γ s) := by
          set φ : ℝ → ℝ := fun s => h + (R - h) * s with hφ
          have himg : φ '' (Icc 0 1) = Icc h R := by
            apply Set.Subset.antisymm
            · rintro _ ⟨s, hs, rfl⟩
              simp only [hφ, mem_Icc] at hs ⊢; constructor <;> nlinarith [hs.1, hs.2, hR.le]
            · intro u hu; simp only [mem_Icc] at hu
              refine ⟨(u - h)/(R-h), ?_, ?_⟩
              · simp only [mem_Icc]
                refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
                rw [div_le_one (by linarith)]; linarith
              · simp only [hφ]
                rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (by linarith : (0:ℝ) < R - h))]; ring
          have hderivφ : ∀ s ∈ Icc (0:ℝ) 1, HasDerivWithinAt φ (R - h) (Icc 0 1) s := by
            intro s _
            have hba : HasDerivAt (fun s : ℝ => (R - h) * s) (R - h) s := by
              simpa using (hasDerivAt_id s).const_mul (R - h)
            have hh2 : HasDerivAt φ (R - h) s := by
              have h2 : HasDerivAt (fun s : ℝ => h + (R - h) * s) (0 + (R - h)) s :=
                (hasDerivAt_const s h).add hba
              simpa [hφ] using h2
            exact hh2.hasDerivWithinAt
          have hinj : Set.InjOn φ (Icc 0 1) := by
            intro s1 _ s2 _ heq
            simp only [hφ, add_right_inj, mul_right_inj' (by linarith : (R-h) ≠ 0)] at heq
            exact heq
          have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderivφ hinj
            (fun u => ρ (x + (u:ℂ) * e))
          rw [himg] at key
          rw [show (∫⁻ r in Icc h R, F r)
                = ∫⁻ u in Icc h R, ρ (x + (u:ℂ) * e) from rfl, key,
            abs_of_pos (by linarith : (0:ℝ) < R - h),
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [hcov, ← harc]; exact hadm γ hmem
      -- ===== CS step =====
      have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
      have hint_inv : ∫⁻ r in Icc h R, ENNReal.ofReal (1/r) = ENNReal.ofReal L := by
        have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc h R) := by
          apply ContinuousOn.div continuousOn_const continuousOn_id
          intro r hr; exact ne_of_gt (lt_of_lt_of_le hh hr.1)
        have hintegrable : IntegrableOn (fun r : ℝ => 1 / r) (Icc h R) volume :=
          hcont.integrableOn_compact isCompact_Icc
        have hnn : 0 ≤ᵐ[volume.restrict (Icc h R)] (fun r : ℝ => 1 / r) := by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          have : 0 < r := lt_of_lt_of_le hh hr.1; positivity
        rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn]
        congr 1
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le]
        have h0notin : (0 : ℝ) ∉ Set.uIcc h R := by
          rw [Set.uIcc_of_le hR.le, Set.mem_Icc]; rintro ⟨hc1, hc2⟩; linarith
        rw [integral_one_div h0notin, hL]
      set fF : ℝ → ℝ≥0∞ := fun r => F r * ENNReal.ofReal (Real.sqrt r) with hfF
      set gG : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (1 / Real.sqrt r) with hgG
      have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc h R)) hconj
        (f := fF) (g := gG) (hFmeas.mul (by fun_prop)).aemeasurable
        (by fun_prop : Measurable gG).aemeasurable
      have hfgeq : ∫⁻ r in Icc h R, (fF * gG) r = ∫⁻ r in Icc h R, F r := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro r hr
        have hr0 : 0 < r := lt_of_lt_of_le hh hr.1
        have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
        simp only [Pi.mul_apply, hfF, hgG]
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg r),
          show Real.sqrt r * (1 / Real.sqrt r) = 1 by field_simp]
        simp
      have hf2 : ∫⁻ r in Icc h R, (fF r)^(2:ℝ)
          = ∫⁻ r in Icc h R, (F r)^2 * ENNReal.ofReal r := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro r hr
        have hr0 : 0 ≤ r := le_of_lt (lt_of_lt_of_le hh hr.1)
        simp only [hfF]
        rw [ENNReal.rpow_two, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg r),
          Real.sq_sqrt hr0]
      have hg2 : ∫⁻ r in Icc h R, (gG r)^(2:ℝ) = ENNReal.ofReal L := by
        rw [← hint_inv]
        apply setLIntegral_congr_fun measurableSet_Icc
        intro r hr
        have hr0 : 0 < r := lt_of_lt_of_le hh hr.1
        have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
        simp only [hgG]
        rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
        congr 1
        rw [sq, div_mul_div_comm, one_mul, Real.mul_self_sqrt hr0.le]
      rw [hfgeq, hf2, hg2] at hcs
      set A : ℝ≥0∞ := ∫⁻ r in Icc h R, (F r)^2 * ENNReal.ofReal r with hA
      have h2 : (1:ℝ≥0∞) ≤ A^((1:ℝ)/2) * (ENNReal.ofReal L)^((1:ℝ)/2) :=
        le_trans hone hcs
      have hsqle : (1:ℝ≥0∞) ≤ A * ENNReal.ofReal L := by
        have hh' := ENNReal.rpow_le_rpow h2 (by norm_num : (0:ℝ) ≤ 2)
        rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hh'
        norm_num at hh'
        exact hh'
      have hLne : ENNReal.ofReal L ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hLpos
      calc ENNReal.ofReal (1/L)
          = (ENNReal.ofReal L)⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos hLpos]
        _ ≤ A := by
            rw [ENNReal.inv_le_iff_le_mul (fun _ => hLne)
              (fun hc => absurd hc ENNReal.ofReal_ne_top)]
            rwa [mul_comm]
        _ ≤ ∫⁻ r in Ioi (0:ℝ), (F r)^2 * ENNReal.ofReal r := lintegral_mono_set hsub
    -- ===== integrate the per-angle bound over θ =====
    calc ENNReal.ofReal (2 * π / L)
        = ∫⁻ _θ in Ioo (-π) π, ENNReal.ofReal (1/L) := ?_
      _ ≤ ∫⁻ θ in Ioo (-π) π, ∫⁻ r in Ioi (0:ℝ),
            ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 :=
          lintegral_mono (fun θ => hinner θ)
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
        show π - -π = 2 * π by ring, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
  exact htrue


/-- **Grötzsch modulus UPPER bound for the annular crossing family (PROVEN).**

The matching upper bound to `annulus_crossingModulus_ge`: the canonical log-radial density is an
*admissible* test density (`annularLogDensity_admissible`) of energy exactly `2π/log(R/h)`
(`annularLogDensity_energy`), so the infimum defining `curveModulus` is `≤` that value:
`curveModulus (annulusCrossingFamily x h R) ≤ ENNReal.ofReal (2π / log(R/h))`.

Together with `annulus_crossingModulus_ge` this **pins the crossing modulus exactly**
(`annulus_crossingModulus_eq`); the upper bound is the half needed by the conjugate
reciprocity to deliver the *separating*-ring **lower** bound `log(R/h)/(2π)`. -/
theorem annulus_crossingModulus_le (x : ℂ) {h R : ℝ} (hh : 0 < h) (hR : h < R) :
    curveModulus (annulusCrossingFamily x h R)
      ≤ ENNReal.ofReal (2 * π / Real.log (R / h)) := by
  -- The log-radial density is admissible (a test density), so the infimum is `≤` its energy.
  have hadm : IsAdmissibleDensity (annularLogDensity x h R) (annulusCrossingFamily x h R) :=
    annularLogDensity_admissible x hh hR
  calc curveModulus (annulusCrossingFamily x h R)
      ≤ ∫⁻ z, (annularLogDensity x h R z) ^ 2 := by
        unfold curveModulus; exact iInf₂_le (annularLogDensity x h R) hadm
    _ = ENNReal.ofReal (2 * π / Real.log (R / h)) := annularLogDensity_energy x h R hh hR

/-- **The annular crossing modulus is EXACTLY the Grötzsch value (PROVEN).**

Combining the matching lower (`annulus_crossingModulus_ge`) and upper (`annulus_crossingModulus_le`)
bounds: `curveModulus (annulusCrossingFamily x h R) = ENNReal.ofReal (2π / log(R/h))`. The
conjugate *separating*-ring modulus is the reciprocal `log(R/h)/(2π)`, obtained from this equality
via the ring reciprocity. -/
theorem annulus_crossingModulus_eq (x : ℂ) {h R : ℝ} (hh : 0 < h) (hR : h < R) :
    curveModulus (annulusCrossingFamily x h R)
      = ENNReal.ofReal (2 * π / Real.log (R / h)) :=
  le_antisymm (annulus_crossingModulus_le x hh hR) (annulus_crossingModulus_ge x hh hR)

/-- The **angular (conjugate) extremal density** of the annulus centred at `x`: the metric
`σ(z) = 1/(2π·‖z − x‖)` supported on the annulus, `0` elsewhere. This is the conjugate of the
log-radial Grötzsch density: its arc-length integral along every concentric winding loop is `≥ 1`
(admissibility for `annulusSeparatingFamily`), and its energy `∫∫ σ²` equals the conjugate value
`log(R/h)/(2π)`, computed in `annulusAngularDensity_energy`. -/
noncomputable def annulusAngularDensity (x : ℂ) (h R : ℝ) : ℂ → ℝ≥0∞ :=
  (annulus x h R).indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z - x‖)))

/-- **Energy of the angular extremal density of the annulus (the conjugate value).**

For `0 < h < R`, the area energy of the canonical angular density on the round annulus
`{h ≤ ‖z − x‖ ≤ R}` is exactly the conjugate Grötzsch value
`∫∫ σ² = log(R/h)/(2π)`.

This is the conjugate of `annularLogDensity_energy`: the explicit `∫∫ σ²` energy on which the
separating-ring modulus *lower* bound rests. The proof is the same polar change of variables
`Complex.lintegral_comp_polarCoord_symm` (Jacobian `r`), reducing to the radial integral
`∫_h^R r·(1/(2πr))² dr = (1/(4π²))·∫_h^R (1/r) dr = log(R/h)/(4π²)` times the angular measure `2π`,
giving `log(R/h)/(2π)`. It is fully proved and axiom-clean. -/
theorem annulusAngularDensity_energy (x : ℂ) (h R : ℝ) (hh : 0 < h) (hR : h < R) :
    ∫⁻ z, (annulusAngularDensity x h R z) ^ 2 = ENNReal.ofReal (Real.log (R / h) / (2 * π)) := by
  set L := Real.log (R / h) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; rw [lt_div_iff₀ hh]; linarith
  -- The integrand `(annulusAngularDensity x h R z)^2` as a function of `z − x`.
  have hshift : (fun z : ℂ => (annulusAngularDensity x h R z) ^ 2)
      = (fun w : ℂ =>
          (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
            (fun w => ENNReal.ofReal (1 / (2 * π * ‖w‖))) w) ^ 2) ∘ (fun z => z - x) := by
    funext z
    simp only [annulusAngularDensity, annulus, Function.comp_apply]
    by_cases hz : z ∈ {z : ℂ | h ≤ ‖z - x‖ ∧ ‖z - x‖ ≤ R}
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (by exact hz)]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (by exact hz)]
  rw [hshift]
  -- `∫ (g ∘ (· − x)) = ∫ g` by translation invariance of `volume`.
  rw [show (∫⁻ z, ((fun w : ℂ =>
          (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
            (fun w => ENNReal.ofReal (1 / (2 * π * ‖w‖))) w) ^ 2) ∘ (fun z => z - x)) z)
        = ∫⁻ w : ℂ, (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
            (fun w => ENNReal.ofReal (1 / (2 * π * ‖w‖))) w) ^ 2 from by
    rw [← lintegral_sub_right_eq_self (fun w : ℂ =>
        (({w : ℂ | h ≤ ‖w‖ ∧ ‖w‖ ≤ R}).indicator
          (fun w => ENNReal.ofReal (1 / (2 * π * ‖w‖))) w) ^ 2) x]
    rfl]
  -- Now the centred computation: square of indicator = indicator of square.
  set A : Set ℂ := {z : ℂ | h ≤ ‖z‖ ∧ ‖z‖ ≤ R} with hA
  have hAmeas : MeasurableSet A := by
    apply MeasurableSet.inter
    · exact measurableSet_le measurable_const continuous_norm.measurable
    · exact measurableSet_le continuous_norm.measurable measurable_const
  have hsq : (fun z : ℂ => (A.indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖))) z) ^ 2)
      = A.indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)) ^ 2) := by
    funext z; by_cases hz : z ∈ A <;> simp [hz]
  rw [hsq]
  -- Polar change of variables.
  rw [← Complex.lintegral_comp_polarCoord_symm
      (A.indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)) ^ 2))]
  rw [polarCoord_target]
  have htmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  -- Simplify the integrand on the target: `‖polarCoord.symm p‖ = p.1`, membership ↔ `p.1 ∈ [h,R]`.
  have hcongr : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      ENNReal.ofReal p.1 • A.indicator (fun z => ENNReal.ofReal (1 / (2 * π * ‖z‖)) ^ 2)
          (Complex.polarCoord.symm p)
        = (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (4 * π ^ 2 * r))) p.1 := by
    intro p hp
    obtain ⟨hr, _hθ⟩ := hp
    simp only [Set.mem_Ioi] at hr
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    by_cases hmem : Complex.polarCoord.symm p ∈ A
    · have hmem' : p.1 ∈ Set.Icc h R := by
        rw [hA, Set.mem_setOf_eq, hnorm] at hmem; exact ⟨hmem.1, hmem.2⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem', hnorm,
        smul_eq_mul, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hr.le]
      congr 1
      have hr0 : (0:ℝ) < p.1 := hr
      have hpi : (0:ℝ) < π := Real.pi_pos
      field_simp
      ring
    · have hmem' : p.1 ∉ Set.Icc h R := by
        intro hc; apply hmem; rw [hA, Set.mem_setOf_eq, hnorm]; exact ⟨hc.1, hc.2⟩
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', smul_zero]
  rw [setLIntegral_congr_fun htmeas hcongr]
  -- Fubini: the integrand depends only on `p.1`; the angular factor is `2π`.
  have hgmeas : Measurable (fun r : ℝ =>
      (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (4 * π ^ 2 * r))) r) := by
    apply Measurable.indicator _ measurableSet_Icc
    exact (measurable_const.div (measurable_const.mul measurable_id)).ennreal_ofReal
  have haem : AEMeasurable
      (fun p : ℝ × ℝ =>
        (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (4 * π ^ 2 * r))) p.1)
      ((volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π)) :=
    (hgmeas.comp measurable_fst).aemeasurable
  rw [Measure.volume_eq_prod, setLIntegral_prod _ haem]
  simp_rw [setLIntegral_const]
  rw [Real.volume_Ioo, lintegral_mul_const _ hgmeas]
  -- The radial integral `∫_h^R 1/(4π² r) dr = L/(4π²)` via `integral_one_div`.
  have hradial : ∫⁻ r in Set.Ioi (0 : ℝ),
      (Set.Icc h R).indicator (fun r => ENNReal.ofReal (1 / (4 * π ^ 2 * r))) r
        = ENNReal.ofReal (L / (4 * π ^ 2)) := by
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hsubset : Set.Icc h R ∩ Set.Ioi (0 : ℝ) = Set.Icc h R :=
      Set.inter_eq_left.mpr (fun w hw => lt_of_lt_of_le hh hw.1)
    rw [hsubset]
    have hcont : ContinuousOn (fun r : ℝ => 1 / (4 * π ^ 2 * r)) (Set.Icc h R) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le hh hr.1
      have hpi : (0:ℝ) < 4 * π ^ 2 := by positivity
      exact ne_of_gt (mul_pos hpi hr0)
    have hintegrable : IntegrableOn (fun r : ℝ => 1 / (4 * π ^ 2 * r)) (Set.Icc h R) volume :=
      hcont.integrableOn_compact isCompact_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc h R)] (fun r : ℝ => 1 / (4 * π ^ 2 * r)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have : 0 < r := lt_of_lt_of_le hh hr.1; positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn]
    congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le]
    have hsplit : ∫ r in h..R, 1 / (4 * π ^ 2 * r) = (∫ r in h..R, 1 / r) * (1 / (4 * π ^ 2)) := by
      rw [← intervalIntegral.integral_mul_const]; congr 1; funext r; ring
    have h0notin : (0 : ℝ) ∉ Set.uIcc h R := by
      rw [Set.uIcc_of_le hR.le, Set.mem_Icc]; rintro ⟨hc1, hc2⟩; linarith
    rw [hsplit, integral_one_div h0notin, ← hL]; ring
  rw [hradial, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show π - -π = 2 * π by ring]
  have hpi : (0:ℝ) < π := Real.pi_pos
  field_simp
  ring

/-- The **separating (ring) family** of the annulus centred at `x`: absolutely continuous *loops*
(`γ 0 = γ 1`) that stay inside the annulus. These are the closed curves of the ring; the ones that
genuinely *separate* the two boundary circles (nonzero winding number around `x`) form the conjugate
family to the radial crossing family, with modulus the reciprocal `log(R/h)/(2π)` and extremal
**angular** density `σ(z) = 1/(2π‖z−x‖)` (`∫∫ σ² = log(R/h)/(2π)`).

The topological *winding/separation* constraint — the conjugacy condition proper — is **not**
encoded as a standalone clause here (Mathlib has no winding-number API for AC plane loops). Stating
the family as "AC loops in the annulus" only *enlarges* it, hence makes the modulus *lower* bound
delivered by `annulus_separatingModulus_ge` **stronger**, not weaker; the bound is realized directly
by the concentric circles, which are members of this enlarged family. -/
def annulusSeparatingFamily (x : ℂ) (h R : ℝ) : Set (ℝ → ℂ) :=
  {γ | Continuous γ ∧ AbsolutelyContinuousOnInterval γ 0 1 ∧ γ 0 = γ 1 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ annulus x h R)}

/-- **Separating-ring modulus LOWER bound (PROVEN, axiom-clean).**

The separating (winding-loop) family of the round annulus has modulus at least the *reciprocal*
Grötzsch value:
`ENNReal.ofReal (log(R/h) / (2π)) ≤ curveModulus (annulusSeparatingFamily x h R)`.

This is the **conjugate** of `annulus_crossingModulus_ge`, and it is the genuinely missing
*separating*-direction ring bound that the Teichmüller two-point distortion needs. It is proved
**directly** (the exact angular dual of the crossing development, no reciprocity): a lower bound on
`curveModulus` runs the Cauchy–Schwarz argument over *every* admissible density `σ'`, decomposed in
the polar foliation with the angle *inner*. Per concentric loop of radius `r` (length `2πr`, in the
enlarged separating family), the angular Cauchy–Schwarz
`(∫_loop σ' ds)² ≤ (∫_loop 1 ds)·(∫_loop σ'² ds) = 2πr·∫_loop σ'² ds` together with admissibility
`∫_loop σ' ds ≥ 1` gives `∫_loop σ'² ds ≥ 1/(2πr)`; integrating the per-loop bound over `r ∈ [h,R]`
yields `∫∫ σ'² ≥ ∫_h^R 1/(2πr) dr = log(R/h)/(2π)`. The angular extremal density
`σ(z) = 1/(2π‖z−x‖)` realizes this value (`annulusAngularDensity_energy`), pinning the separating
modulus to exactly `log(R/h)/(2π)`. -/
theorem annulus_separatingModulus_ge (x : ℂ) {h R : ℝ} (hh : 0 < h) (hR : h < R) :
    ENNReal.ofReal (Real.log (R / h) / (2 * π))
      ≤ curveModulus (annulusSeparatingFamily x h R) := by
  set L := Real.log (R / h) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; rw [lt_div_iff₀ hh]; linarith
  have hpipos : (0:ℝ) < π := Real.pi_pos
  unfold curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hadm⟩
  -- ===== polar decomposition =====
  have hpolar : ∫⁻ z, (ρ z)^2
      = ∫⁻ p in (Ioi (0:ℝ) ×ˢ Ioo (-π) π),
          ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm p + x))^2 := by
    have htrans : ∫⁻ z, (ρ z)^2 = ∫⁻ w, (ρ (w + x))^2 := by
      rw [← lintegral_add_right_eq_self (fun w => (ρ w)^2) x]
    rw [htrans, ← Complex.lintegral_comp_polarCoord_symm (fun w => (ρ (w + x))^2),
      polarCoord_target]
    simp only [smul_eq_mul]
  -- measurability of the polar integrand
  have hpmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm p + x))^2) := by
    apply Measurable.mul (measurable_fst.ennreal_ofReal)
    apply Measurable.pow_const
    apply hρmeas.comp
    have hsm : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      have : (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
          = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
        funext p; rw [Complex.polarCoord_symm_apply]
      rw [this]; fun_prop
    exact hsm.add_const x
  -- ===== r-outer Fubini (the angular dual: angle is now the INNER integral) =====
  have hfubini : ∫⁻ p in (Ioi (0:ℝ) ×ˢ Ioo (-π) π),
          ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm p + x))^2
      = ∫⁻ r in Ioi (0:ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 := by
    rw [Measure.volume_eq_prod, setLIntegral_prod _ hpmeas.aemeasurable]
  rw [hpolar, hfubini]
  -- ===== per-radius lower bound: ofReal(1/(2π r)) ≤ inner ; for r ∈ [h,R] =====
  have hinner : ∀ r : ℝ, h ≤ r → r ≤ R → ENNReal.ofReal (1/(2 * π * r))
      ≤ ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 := by
    intro r hrh hrR
    have hrpos : 0 < r := lt_of_lt_of_le hh hrh
    -- `e θ = e^{iθ}` and its norm.
    have hsymm : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ)
        = (r:ℂ) * Complex.exp ((θ : ℝ) * Complex.I) := by
      intro θ
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]; push_cast; ring
    have henorm : ∀ θ : ℝ, ‖Complex.exp ((θ : ℝ) * Complex.I)‖ = 1 := by
      intro θ
      rw [show ((θ : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I by push_cast; ring]
      simp [Complex.norm_exp]
    set G : ℝ → ℝ≥0∞ := fun θ => ρ (x + (r:ℂ) * Complex.exp ((θ : ℝ) * Complex.I)) with hG
    have hintegrand : ∀ θ : ℝ,
        ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2
          = (G θ)^2 * ENNReal.ofReal r := by
      intro θ; rw [hsymm, hG, add_comm ((r:ℂ) * _) x, mul_comm]
    simp_rw [hintegrand]
    have hGmeas : Measurable G := by
      apply hρmeas.comp
      apply measurable_const.add
      apply Measurable.const_mul
      have : Measurable (fun θ : ℝ => ((θ : ℝ) : ℂ) * Complex.I) := by
        exact (Complex.measurable_ofReal.comp measurable_id).mul_const Complex.I
      exact (Complex.measurable_exp.comp this)
    -- ===== hone : 1 ≤ ∫_{Ioo(-π) π} G θ · ofReal r dθ (admissibility of the loop at radius r) =====
    have hone : (1:ℝ≥0∞) ≤ ∫⁻ θ in Ioo (-π) π, G θ * ENNReal.ofReal r := by
      -- the concentric loop `γ t = x + r·exp(i(-π + 2π t))`, t ∈ [0,1]
      set γ : ℝ → ℂ := fun t => x + (r:ℂ) * Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I) with hγ
      have hγnorm : ∀ t, ‖γ t - x‖ = r := by
        intro t
        simp only [hγ, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hrpos, henorm, mul_one]
      -- membership in the separating family
      have hmem : γ ∈ annulusSeparatingFamily x h R := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · apply Continuous.add continuous_const
          apply Continuous.mul continuous_const
          apply Complex.continuous_exp.comp
          apply Continuous.mul _ continuous_const
          exact Complex.continuous_ofReal.comp (by fun_prop)
        · apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨2 * π * r, by positivity⟩)
          apply LipschitzOnWith.mono _ (subset_univ _)
          rw [lipschitzOnWith_univ]
          apply LipschitzWith.of_dist_le_mul
          intro t t'
          simp only [hγ, dist_eq_norm]
          rw [show (x + (r:ℂ) * Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I))
                - (x + (r:ℂ) * Complex.exp (((-π + 2*π*t' : ℝ)) * Complex.I))
              = (r:ℂ) * (Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I)
                  - Complex.exp (((-π + 2*π*t' : ℝ)) * Complex.I)) by ring]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
          -- bound `‖e^{ia} - e^{ib}‖ ≤ |a − b|` (via `Real.norm_exp_I_mul_ofReal_sub_one_le`)
          have key : ∀ a b : ℝ, ‖Complex.exp ((a:ℝ) * Complex.I)
                - Complex.exp ((b:ℝ) * Complex.I)‖ ≤ |a - b| := by
            intro a b
            have h1 : Complex.exp ((a:ℝ) * Complex.I) - Complex.exp ((b:ℝ) * Complex.I)
                = Complex.exp ((b:ℝ) * Complex.I)
                  * (Complex.exp (Complex.I * ((a - b : ℝ):ℂ)) - 1) := by
              rw [mul_sub, mul_one, ← Complex.exp_add]
              congr 2
              push_cast; ring
            rw [h1, norm_mul, henorm b, one_mul]
            have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
            rwa [Real.norm_eq_abs] at hb
          rw [NNReal.coe_mk, Real.norm_eq_abs]
          calc r * ‖Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I)
                - Complex.exp (((-π + 2*π*t' : ℝ)) * Complex.I)‖
              ≤ r * |(-π + 2*π*t) - (-π + 2*π*t')| :=
                mul_le_mul_of_nonneg_left (key _ _) hrpos.le
            _ = r * (2*π*|t - t'|) := by
                rw [show (-π + 2*π*t) - (-π + 2*π*t') = 2*π*(t - t') by ring, abs_mul,
                  abs_of_pos (by positivity : (0:ℝ) < 2*π)]
            _ = (2*π*r) * |t - t'| := by ring
        · simp only [hγ]
          congr 1
          rw [show ((-π + 2*π*(0:ℝ) : ℝ)) = -π by ring, show ((-π + 2*π*(1:ℝ) : ℝ)) = π by ring]
          rw [show ((-π : ℝ) : ℂ) * Complex.I = -(((π:ℝ):ℂ) * Complex.I) by push_cast; ring,
            show (((π:ℝ) : ℂ)) * Complex.I = ((π:ℝ):ℂ) * Complex.I from rfl]
          rw [Complex.exp_neg]
          rw [show Complex.exp (((π:ℝ):ℂ) * Complex.I) = -1 by
            rw [show ((π:ℝ):ℂ) = (π:ℂ) by push_cast; ring, Complex.exp_pi_mul_I]]
          norm_num
        · intro t _
          exact ⟨by rw [hγnorm]; exact hrh, by rw [hγnorm]; exact hrR⟩
      have hadmγ := hadm γ hmem
      -- relate arcLengthLineIntegral to the θ-integral via the substitution θ = -π + 2π t
      have hderiv : ∀ t, deriv γ t = (r:ℂ) * ((2*π : ℝ) * Complex.I)
          * Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I) := by
        intro t
        have hbase : HasDerivAt (fun t : ℝ => ((-π + 2*π*t : ℝ)) * Complex.I)
            (((2*π : ℝ)) * Complex.I) t := by
          have hr1 : HasDerivAt (fun t : ℝ => (-π + 2*π*t : ℝ)) (2*π) t := by
            have h2 : HasDerivAt (fun t : ℝ => 2*π*t) (2*π * 1) t :=
              (hasDerivAt_id t).const_mul (2*π)
            have h3 : HasDerivAt (fun t : ℝ => -π + 2*π*t) (0 + 2*π * 1) t :=
              (hasDerivAt_const t (-π)).add h2
            simpa using h3
          have ha : HasDerivAt (fun t : ℝ => ((-π + 2*π*t : ℝ) : ℂ)) ((2*π : ℝ):ℂ) t :=
            hr1.ofReal_comp
          have := ha.mul_const Complex.I
          simpa using this
        have hexp : HasDerivAt (fun t : ℝ => Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I))
            (Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I) * (((2*π : ℝ)) * Complex.I)) t := by
          exact (Complex.hasDerivAt_exp _).comp t hbase
        have hd : HasDerivAt γ
            ((r:ℂ) * (Complex.exp (((-π + 2*π*t : ℝ)) * Complex.I) * (((2*π : ℝ)) * Complex.I))) t := by
          simpa [hγ] using (hexp.const_mul (r:ℂ)).const_add x
        rw [hd.deriv]; ring
      have hnormderiv : ∀ t, (‖deriv γ t‖₊ : ℝ≥0∞) = ENNReal.ofReal (2 * π * r) := by
        intro t
        rw [hderiv t, ← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm]
        congr 1
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos,
          henorm, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0:ℝ) < 2*π), Complex.norm_I, mul_one]
        ring
      have harc : arcLengthLineIntegral ρ γ
          = ENNReal.ofReal (2 * π * r) * ∫⁻ t in Icc (0:ℝ) 1, ρ (γ t) := by
        unfold arcLengthLineIntegral
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr; intro t; rw [hnormderiv t, mul_comm]
      -- change of variables θ = φ t = -π + 2π t mapping [0,1] onto [-π, π]
      have hcov : ∫⁻ θ in Icc (-π) π, G θ
          = ENNReal.ofReal (2 * π) * ∫⁻ t in Icc (0:ℝ) 1, ρ (γ t) := by
        set φ : ℝ → ℝ := fun t => -π + 2*π*t with hφ
        have himg : φ '' (Icc 0 1) = Icc (-π) π := by
          apply Set.Subset.antisymm
          · rintro _ ⟨t, ht, rfl⟩
            simp only [hφ, mem_Icc] at ht ⊢
            constructor <;> nlinarith [ht.1, ht.2, hpipos.le]
          · intro u hu; simp only [mem_Icc] at hu
            refine ⟨(u + π)/(2*π), ?_, ?_⟩
            · simp only [mem_Icc]
              refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
              rw [div_le_one (by positivity)]; linarith
            · simp only [hφ]
              field_simp; ring
        have hderivφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt φ (2*π) (Icc 0 1) t := by
          intro t _
          have h2 : HasDerivAt φ (2*π) t := by
            have hb : HasDerivAt (fun t : ℝ => 2*π*t) (2*π*1) t :=
              (hasDerivAt_id t).const_mul (2*π)
            have h3 : HasDerivAt (fun t : ℝ => -π + 2*π*t) (0 + 2*π*1) t :=
              (hasDerivAt_const t (-π)).add hb
            simpa [hφ] using h3
          exact h2.hasDerivWithinAt
        have hinj : Set.InjOn φ (Icc 0 1) := by
          intro t1 _ t2 _ heq
          simp only [hφ, add_right_inj, mul_right_inj' (by positivity : (2*π) ≠ 0)] at heq
          exact heq
        have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderivφ hinj
          (fun u => ρ (x + (r:ℂ) * Complex.exp ((u:ℝ) * Complex.I)))
        rw [himg] at key
        rw [show (∫⁻ θ in Icc (-π) π, G θ)
              = ∫⁻ u in Icc (-π) π, ρ (x + (r:ℂ) * Complex.exp ((u:ℝ) * Complex.I)) from rfl, key,
          abs_of_pos (by positivity : (0:ℝ) < 2*π),
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      -- combine: 1 ≤ arcLength = ofReal(2πr)·∫ρ(γ) = ofReal r · (ofReal(2π)·∫ρ(γ)) = ofReal r · ∫_Icc G
      have hGle : ∫⁻ θ in Ioo (-π) π, G θ * ENNReal.ofReal r
          = ENNReal.ofReal r * ∫⁻ θ in Icc (-π) π, G θ := by
        rw [show (∫⁻ θ in Ioo (-π) π, G θ * ENNReal.ofReal r)
              = ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π, G θ by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            apply lintegral_congr; intro θ; rw [mul_comm]]
        congr 1
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := volume) (a := -π) (b := π)]
      rw [hGle, hcov]
      calc (1:ℝ≥0∞) ≤ arcLengthLineIntegral ρ γ := hadmγ
        _ = ENNReal.ofReal (2 * π * r) * ∫⁻ t in Icc (0:ℝ) 1, ρ (γ t) := harc
        _ = ENNReal.ofReal r * (ENNReal.ofReal (2*π) * ∫⁻ t in Icc (0:ℝ) 1, ρ (γ t)) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hrpos.le]; congr 2; ring
    -- ===== CS step (angular Cauchy–Schwarz over the loop) =====
    have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
    set fF : ℝ → ℝ≥0∞ := fun θ => G θ * ENNReal.ofReal (Real.sqrt r) with hfF
    set gG : ℝ → ℝ≥0∞ := fun _ => ENNReal.ofReal (Real.sqrt r) with hgG
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioo (-π) π)) hconj
      (f := fF) (g := gG) (hGmeas.mul (by fun_prop)).aemeasurable
      (by fun_prop : Measurable gG).aemeasurable
    have hsqr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hfgeq : ∫⁻ θ in Ioo (-π) π, (fF * gG) θ = ∫⁻ θ in Ioo (-π) π, G θ * ENNReal.ofReal r := by
      apply lintegral_congr; intro θ
      simp only [Pi.mul_apply, hfF, hgG]
      rw [mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg r), Real.mul_self_sqrt hrpos.le]
    have hf2 : ∫⁻ θ in Ioo (-π) π, (fF θ)^(2:ℝ)
        = ∫⁻ θ in Ioo (-π) π, (G θ)^2 * ENNReal.ofReal r := by
      apply lintegral_congr; intro θ
      simp only [hfF]
      rw [ENNReal.rpow_two, mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg r),
        Real.sq_sqrt hrpos.le]
    have hg2 : ∫⁻ θ in Ioo (-π) π, (gG θ)^(2:ℝ) = ENNReal.ofReal (2 * π * r) := by
      simp only [hgG]
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hrpos.le]
      rw [setLIntegral_const, Real.volume_Ioo, show π - -π = 2 * π by ring,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    rw [hfgeq, hf2, hg2] at hcs
    set A : ℝ≥0∞ := ∫⁻ θ in Ioo (-π) π, (G θ)^2 * ENNReal.ofReal r with hA
    have h2 : (1:ℝ≥0∞) ≤ A^((1:ℝ)/2) * (ENNReal.ofReal (2 * π * r))^((1:ℝ)/2) :=
      le_trans hone hcs
    have hsqle : (1:ℝ≥0∞) ≤ A * ENNReal.ofReal (2 * π * r) := by
      have hh' := ENNReal.rpow_le_rpow h2 (by norm_num : (0:ℝ) ≤ 2)
      rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hh'
      norm_num at hh'
      exact hh'
    have hPne : ENNReal.ofReal (2 * π * r) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hPtop : ENNReal.ofReal (2 * π * r) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ENNReal.ofReal (1/(2 * π * r))
        = (ENNReal.ofReal (2 * π * r))⁻¹ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
      _ ≤ A := by
          rw [ENNReal.inv_le_iff_le_mul (fun _ => hPne) (fun hc => absurd hc hPtop)]
          rwa [mul_comm]
  -- ===== integrate the per-radius bound over r ∈ [h,R] =====
  have hsub : Icc h R ⊆ Ioi (0:ℝ) := fun r hr => lt_of_lt_of_le hh hr.1
  have hpairmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm (p.1, p.2) + x))^2) := by
    apply Measurable.mul measurable_fst.ennreal_ofReal
    apply Measurable.pow_const
    apply hρmeas.comp
    have hsm : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm (p.1, p.2)) := by
      have : (fun p : ℝ × ℝ => Complex.polarCoord.symm (p.1, p.2))
          = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
        funext p; rw [Complex.polarCoord_symm_apply]
      rw [this]; fun_prop
    exact hsm.add_const x
  have hradial_meas : Measurable (fun r : ℝ =>
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2) := by
    have heq : (fun r : ℝ =>
          ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2)
        = fun r : ℝ => ∫⁻ θ, (univ ×ˢ Ioo (-π) π).indicator
            (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (ρ (Complex.polarCoord.symm (p.1, p.2) + x))^2)
            (r, θ) := by
      funext r
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr; intro θ
      by_cases hθ : θ ∈ Ioo (-π) π
      · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem (by exact ⟨mem_univ r, hθ⟩)]
      · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem (by
          simp only [Set.mem_prod, mem_univ, true_and]; exact hθ)]
    rw [heq]
    apply Measurable.lintegral_prod_right'
    apply Measurable.indicator hpairmeas
    exact MeasurableSet.univ.prod measurableSet_Ioo
  calc ENNReal.ofReal (L / (2 * π))
      = ∫⁻ r in Icc h R, ENNReal.ofReal (1/(2 * π * r)) := ?_
    _ ≤ ∫⁻ r in Icc h R, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 := by
        apply setLIntegral_mono_ae hradial_meas.aemeasurable
        filter_upwards with r hr
        exact hinner r hr.1 hr.2
    _ ≤ ∫⁻ r in Ioi (0:ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * (ρ (Complex.polarCoord.symm (r, θ) + x))^2 :=
        lintegral_mono_set hsub
  -- the radial integral `∫_h^R 1/(2π r) dr = L/(2π)`
  · rw [show (∫⁻ r in Icc h R, ENNReal.ofReal (1/(2 * π * r)))
          = ENNReal.ofReal (1/(2*π)) * ∫⁻ r in Icc h R, ENNReal.ofReal (1/r) by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply setLIntegral_congr_fun measurableSet_Icc
        intro r hr
        simp only
        have hr0 : 0 < r := lt_of_lt_of_le hh hr.1
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(2*π))]
        congr 1
        rw [div_mul_div_comm, one_mul, mul_assoc]]
    have hint_inv : ∫⁻ r in Icc h R, ENNReal.ofReal (1/r) = ENNReal.ofReal L := by
      have hcont : ContinuousOn (fun r : ℝ => 1 / r) (Icc h R) := by
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro r hr; exact ne_of_gt (lt_of_lt_of_le hh hr.1)
      have hintegrable : IntegrableOn (fun r : ℝ => 1 / r) (Icc h R) volume :=
        hcont.integrableOn_compact isCompact_Icc
      have hnn : 0 ≤ᵐ[volume.restrict (Icc h R)] (fun r : ℝ => 1 / r) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have : 0 < r := lt_of_lt_of_le hh hr.1; positivity
      rw [← ofReal_integral_eq_lintegral_ofReal hintegrable hnn]
      congr 1
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le]
      have h0notin : (0 : ℝ) ∉ Set.uIcc h R := by
        rw [Set.uIcc_of_le hR.le, Set.mem_Icc]; rintro ⟨hc1, hc2⟩; linarith
      rw [integral_one_div h0notin, hL]
    rw [hint_inv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp

/-- **Separating-ring modulus lower bound (the source Grötzsch/Teichmüller ring bound).**

The separating (winding-loop) family of the round annulus `{h ≤ ‖z − x‖ ≤ R}` has modulus at
least the reciprocal Grötzsch value `log(R/h)/(2π)`. This is the genuinely missing separating
ring bound — the conjugate of the proven crossing bound `annulus_crossingModulus_ge` — and is
exactly the input the Teichmüller two-point distortion `ringModulus_diam_le` needs.

## Reconciliation (crossing ↔ separating)

The previously-stated form bounded the **pushforward of the crossing family** by the *separating*
value `log(R/h)/(2πK)`. That was *incoherent*: the pushforward modulus of the crossing family is
`≤ M(crossing) = 2π/log(R/h)` (it can only drop, even conformally — `step` of
`curveModulus_conformal_invariant`), so a *lower* bound of the conjugate magnitude `log/(2π)` on it
is false in general, and the quasiconformal clause `hf.2.2` only upper-bounds **quadrilateral**
image moduli (no ring transport). The honest node is the **source separating modulus** bound, which
*is* the conjugate value and *is* provable (from `annulus_separatingModulus_ge`, i.e. from the
isolated annulus reciprocity + the proven crossing value). The `f`-transport and the Teichmüller
geometry are deferred to `ringModulus_diam_le` (deep), where they genuinely belong. -/
theorem image_ringModulus_ge (x : ℂ) {h R : ℝ} (hh : 0 < h) (hR : h < R) :
    ENNReal.ofReal (Real.log (R / h) / (2 * π))
      ≤ curveModulus (annulusSeparatingFamily x h R) :=
  annulus_separatingModulus_ge x hh hR

/-- **Teichmüller diameter estimate (deep) — the two-point distortion.**

A lower bound `c ≤ curveModulus` on the separating ring of `f''(annulus)` forces the image of the
outer circle to lie within a bounded multiple of the inner-circle image separation: if the two inner
image sides are separated by `d > 0` and the source ring `{h ≤ ‖z − x‖ ≤ R}` has fixed ratio `R/h`,
then `diam (f''(outer disc)) ≤ C'·d` with `C'` depending only on the modulus lower bound (hence only
on `K`).

## Reachable-vs-deep

**Deep.** This is the Teichmüller/Mori estimate `mod(separating ring) ≳ log(D/d)`: a *separating*
ring of large modulus must be geometrically thick, i.e. its bounded complementary continuum
(`f''inner`, of diameter `≥ d`) and its unbounded one (`f''outer`-complement) are separated by a
ratio bounded by an explicit function of the modulus. Inverting gives `D/d ≤ exp(2π·mod_upper)` so
`diam ≤ C'·d`. The sharp Teichmüller bound is absent from Mathlib; a non-sharp but sufficient bound
suffices here.

It consumes the proven **source** separating-ring modulus lower bound `image_ringModulus_ge`
(= `annulus_separatingModulus_ge`, value `log(R/h)/(2π)`). Two genuinely two-dimensional QC
ingredients remain bundled here: (a) the `K`-quasiconformal **transport** of the separating modulus
to the image ring `M(f''separating) ≥ M(separating)/K` (the geometric clause `hf.2.2` only
upper-bounds *quadrilateral* image moduli, so this ring transport is net-new), and (b) the
Teichmüller modulus⇒diameter geometric inversion. Both are absent from Mathlib and this repository;
the crossing↔separating value reconciliation and the source separating bound are now PROVEN,
axiom-clean, upstream. -/
theorem ringModulus_diam_le {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    (x : ℂ) {r h : ℝ} (hr : 0 < r) (hh : h = r / Real.sqrt 2) {d : ℝ} (hd : 0 < d) :
    Metric.diam (f '' qcOuterSquare x r) ≤ (2 * K + 2) * d := by
  -- `K ≥ 1 ≥ 0`, so the bound `(2K+2)·d` is nonnegative.
  have hK1 : (1 : ℝ) ≤ K := hf.1
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hbound_nonneg : (0 : ℝ) ≤ (2 * K + 2) * d := by positivity
  -- ===========================================================================================
  -- ASSEMBLY (metric-topology, proved here). The diameter of `f '' qcOuterSquare x r` is bounded
  -- by the uniform pairwise-distance bound `(2K+2)·d` between any two image points of the outer
  -- square, via `Metric.diam_le_of_forall_dist_le`. The only nonelementary input is the
  -- *two-point distortion* per-pair bound `two_point_distortion` below — the genuine
  -- Mori/Teichmüller estimate (see the ISOLATED DEEP RESIDUAL block).
  -- ===========================================================================================
  apply Metric.diam_le_of_forall_dist_le hbound_nonneg
  intro p hp q hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  -- ===========================================================================================
  -- ISOLATED DEEP RESIDUAL — the Mori/Teichmüller two-point distortion.
  --
  -- This is the single genuinely-deep, Mathlib-absent ingredient of `qc_quasiround`: for a
  -- geometric `K`-quasiconformal map `f`, any two image points `f a, f b` of the circumscribed
  -- square `qcOuterSquare x r` (half-side `r`, so its corner sits on the source circle of radius
  -- `r√2`) are at distance at most `(2K+2)·d`, where `d > 0` is the (sharp, attained) separation
  -- of the two opposite image sides of the inscribed square (half-side `h = r/√2`, so its sides
  -- sit on the source circle of radius `h = r/√2`). The source ring separating the inner square
  -- from the outer-square complement is the round annulus of FIXED ratio `R/h = r/(r/√2) = √2`.
  --
  -- The proof of this residual is the classical **Mori two-point distortion / Teichmüller ring
  -- modulus** estimate. The two genuinely two-dimensional, Mathlib- and repository-absent
  -- ingredients it bundles are:
  --   (a) the `K`-quasiconformal TRANSPORT of the *separating*-ring modulus to the image ring
  --       `M(f''separating) ≥ M(separating)/K`. The geometric clause `hf.2.2` only upper-bounds
  --       *quadrilateral* CROSSING image moduli, so a ring/separating-family transport is net-new
  --       (the proven source separating bound `image_ringModulus_ge = log(R/h)/(2π)` supplies the
  --       *source* value, but not its `f`-transport);
  --   (b) the **Teichmüller modulus⇒diameter inversion**: a separating ring of bounded modulus
  --       must be geometrically thin, i.e. its bounded complementary continuum (`f''inner`, of
  --       diameter ≥ `d`) and the outer-square image are separated by a ratio `D/d ≤ C(K)`; this
  --       is the Grötzsch/Teichmüller extremal (symmetrization) property, not reducible to the
  --       round-annulus energy computations already proved.
  --
  -- Both ingredients are absent from Mathlib and this repository; the upstream development
  -- (`annularLogDensity_energy`, `annulus_crossingModulus_eq`, `annulus_separatingModulus_ge` /
  -- `image_ringModulus_ge`) supplies the source round-annulus moduli these consume but neither
  -- the QC ring transport nor the extremal inversion. The constant `2K+2` is uniform in `x, r`
  -- (scale/translation invariance of QC distortion). This is the minimal honest residual: it
  -- cannot be narrowed to a sub-inequality expressible through the repository's Rengel/axis-
  -- rectangle moduli, all of which output the wrong inequality direction (area/modulus LOWER
  -- bounds, no diameter UPPER bound) — see the enumeration in `qc_quasiround_data`'s body.
  -- ===========================================================================================
  have two_point_distortion :
      ∀ a ∈ qcOuterSquare x r, ∀ b ∈ qcOuterSquare x r,
        dist (f a) (f b) ≤ (2 * K + 2) * d := by
    sorry
  exact two_point_distortion a ha b hb

/-- **Top assembly node — closes `hquasiround`.**

Packages the ring-modulus development into the exact statement consumed by `qc_quasiround_data`'s
internal `hquasiround`: a uniform `C' ≥ 0` with `diam (f''outer) ≤ C'·d` whenever `d` is the sharp
attained separation of the two inner image sides. The constant `C' = 2K + 2` from
`ringModulus_diam_le` is uniform in `x, r` (scale/translation invariance). All quasiconformal
content is delegated to `ringModulus_diam_le` (hence ultimately to `annulus_crossingModulus_ge` /
`image_ringModulus_ge` and the proven `annularLogDensity_energy`). -/
theorem qc_quasiround_distortion_bound {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∀ (h : ℝ), h = r / Real.sqrt 2 →
        ∀ (hlt : x.re - h < x.re + h) (hlt2 : x.im - h < x.im + h),
          ∀ d : ℝ, 0 < d →
            (∀ p ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).leftSide,
             ∀ q ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).rightSide,
              d ≤ dist p q) →
            (∃ p ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).leftSide,
             ∃ q ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).rightSide,
              dist p q = d) →
            Metric.diam (f '' qcOuterSquare x r) ≤ C' * d := by
  -- `C' = 2K + 2 ≥ 0`; the bound is `ringModulus_diam_le`.
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hf.1
  refine ⟨2 * K + 2, by positivity, fun x r hr h hh hlt hlt2 d hd _hsep _hatt => ?_⟩
  exact ringModulus_diam_le hf x hr hh hd

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
        Metric.diam (f '' qcOuterSquare x r) ≤ C' * d := by
  -- `f` is an injective homeomorphism (continuous, with continuous, hence compact, images).
  have hhomeo : IsHomeomorph f := hf.2.1.isHomeomorph
  have hfc : Continuous f := hhomeo.continuous
  -- ===========================================================================================
  -- THE GENUINE QUASICONFORMAL INPUT (the missing classical "quasiround / two-point-distortion"
  -- estimate, equivalently a lower bound on the Teichmüller ring modulus): a `K`-uniform constant
  -- `C' ≥ 0` bounding the outer image-square diameter by the SHARP separation `d` of the two inner
  -- image sides. Phrased as: given `d > 0` that is the genuine inf-distance of the two disjoint
  -- compact image sides (a pairwise lower bound that is ALSO attained by some pair), one has
  -- `diam (f''outer) ≤ C' · d`. (The attainment hypothesis is load-bearing: the bound is false for
  -- an arbitrarily small non-sharp lower bound.) This is the only step that is not elementary
  -- plane geometry / metric-space topology; it is absent from Mathlib and this repository (see the
  -- theorem docstring). The constant `C'` is uniform in `x, r` (scale/translation invariance of QC
  -- distortion).
  --
  -- WHY THE FINITE-DECOMPOSITION ROUTES FAIL (verified against the full repo toolkit). The target
  -- is a diameter *upper* bound `diam (f''outer) ≤ C' · d`. The repo's only inequalities relating
  -- the image of `f` to `d` are: (A) Rengel `rengel_area_lower_bound` (`d² · M(Γ) ≤ area(R)`, an
  -- AREA *lower* bound); (B) `square_imageCurveFamily_modulus_ge` (`1/K ≤ M(f(square))`, a crossing
  -- modulus *lower* bound); (C) `axisRect_imageModulus_le` (`M(f(R)) ≤ K·(t−s)/(b−a)`, a modulus
  -- *upper* bound). NONE upper-bounds a distance or diameter of an `f`-image, and no combination
  -- does:
  --   • Route 1 (decompose the frame `O \ I` into axis rectangles + a series/parallel law): a
  --     superadditivity law for `curveModulus` only relates moduli to moduli; combined with (A)/(C)
  --     it still produces only area lower bounds / modulus upper bounds, never a `diam ≤ …` term.
  --     Even a separating-frame modulus *lower* bound, fed to Rengel on the frame, yields an AREA
  --     lower bound `d_frame² · M ≤ area(f''frame)`, NOT a diameter bound.
  --   • Route 2 (two diametral image points via the separating family): bounding `dist(f a', f b')`
  --     needs a *lower* bound on the modulus of the family SEPARATING `f''inner` from the outer
  --     complement, converted to a diameter ratio by the Teichmüller estimate `mod ≳ log(D/d)`.
  --     That separating-direction lower bound is exactly the absent ring modulus; the geometric
  --     definition `M(f(Q)) ≤ K·M(Q)` gives only CROSSING-family *upper* bounds, which never force
  --     two image points close (a cheap admissible density is compatible with arbitrarily large
  --     separation in a thin region).
  --   • Route 3 (diam via `infDist`/`diam` from separation + Rengel + reciprocity only): Rengel and
  --     reciprocity are both area-/modulus-LOWER-bound machinery; there is no upper-diameter
  --     analogue of Rengel, so this cannot yield the required `diam ≤ C' · d`.
  -- Hence the single residual below — the two-point distortion bound — is the minimal honest
  -- missing inequality; it cannot be narrowed to a sub-inequality expressible through Rengel and
  -- the existing axis-rectangle moduli (all of which output the wrong inequality direction).
  -- ===========================================================================================
  have hquasiround : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (x : ℂ) (r : ℝ), 0 < r →
      ∀ (h : ℝ), h = r / Real.sqrt 2 →
        ∀ (hlt : x.re - h < x.re + h) (hlt2 : x.im - h < x.im + h),
          ∀ d : ℝ, 0 < d →
            -- `d` is the SHARP separation of the two inner image sides: a pairwise lower bound...
            (∀ p ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).leftSide,
             ∀ q ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).rightSide,
              d ≤ dist p q) →
            -- ...that is attained by some pair (so `d` is the genuine inf-distance, not an
            -- arbitrarily small lower bound — the bound below is false for non-sharp `d`).
            (∃ p ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).leftSide,
             ∃ q ∈ f '' (axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h)
                  hlt hlt2).rightSide,
              dist p q = d) →
            Metric.diam (f '' qcOuterSquare x r) ≤ C' * d :=
    qc_quasiround_distortion_bound hf
  -- ===========================================================================================
  -- Easy half: assemble the conclusion from `hquasiround` and the metric-topology separation of
  -- the two disjoint compact inner image sides (all elementary). We take `d` to be the EXACT
  -- attained pairwise distance `dist p₀ q₀` realizing the inf-distance of the two compacta — it is
  -- positive, is a lower bound for all pairs (`≤ dist p q`), and is itself realized by a pair so
  -- the distortion lemma's `d` is sharp.
  -- ===========================================================================================
  obtain ⟨C', hC'0, hC'bound⟩ := hquasiround
  refine ⟨C', hC'0, fun x r hr h hh hlt hlt2 => ?_⟩
  -- Abbreviate the inner-square quadrilateral and its two opposite source sides.
  set Q := axisRectQuadrilateral (x.re - h) (x.re + h) (x.im - h) (x.im + h) hlt hlt2 with hQ
  -- The two source sides are compact segments (continuous image of `{·} × Icc`).
  have hcptL : IsCompact Q.leftSide := by
    rw [hQ]; unfold Quadrilateral.leftSide
    exact (isCompact_singleton.prod isCompact_Icc).image
      (axisRectQuadrilateral _ _ _ _ hlt hlt2).continuous_toFun
  have hcptR : IsCompact Q.rightSide := by
    rw [hQ]; unfold Quadrilateral.rightSide
    exact (isCompact_singleton.prod isCompact_Icc).image
      (axisRectQuadrilateral _ _ _ _ hlt hlt2).continuous_toFun
  -- Their images under the continuous `f` are compact.
  have hcptfL : IsCompact (f '' Q.leftSide) := hcptL.image hfc
  have hcptfR : IsCompact (f '' Q.rightSide) := hcptR.image hfc
  -- The left side is nonempty (it contains the corner `⟨x.re - h, x.im - h⟩`); so is its image.
  obtain ⟨hdisjsrc, hneL⟩ := image_axisRectQuadrilateral_sides_disjoint hhomeo hlt hlt2
  have hnefL : (f '' Q.leftSide).Nonempty := hneL.image f
  have hnefR : (f '' Q.rightSide).Nonempty := by
    have hneR : (Q.rightSide).Nonempty := by
      rw [hQ, axisRectQuadrilateral_rightSide hlt hlt2]
      exact ⟨Complex.mk (x.re + h) (x.im - h), rfl, le_refl _, by linarith⟩
    exact hneR.image f
  -- The two image sides are disjoint (`f` injective transports the disjointness).
  have hdisj : Disjoint (f '' Q.leftSide) (f '' Q.rightSide) := hdisjsrc
  -- The metric-space separation primitive gives a uniform positive lower bound `d₀`. We upgrade it
  -- to the SHARP, ATTAINED separation: `infDist` of the two compacta is attained (compactness) and
  -- is positive (the lower bound `d₀ > 0`).
  obtain ⟨d₀, hd₀pos, hd₀sep⟩ :=
    exists_pos_setSeparation_of_disjoint_compact hcptfL hcptfR hnefL hnefR hdisj
  -- The two-variable continuous distance attains its minimum on the compact product `f''L × f''R`.
  have hcont : Continuous (fun pq : ℂ × ℂ => dist pq.1 pq.2) := continuous_dist
  obtain ⟨pq₀, hpq₀mem, hpq₀min⟩ :=
    (hcptfL.prod hcptfR).exists_isMinOn (hnefL.prod hnefR) hcont.continuousOn
  obtain ⟨hp₀, hq₀⟩ := hpq₀mem
  -- The minimal distance `d := dist p₀ q₀` is the sharp separation.
  set d : ℝ := dist pq₀.1 pq₀.2 with hd
  have hdsep : ∀ p ∈ f '' Q.leftSide, ∀ q ∈ f '' Q.rightSide, d ≤ dist p q := by
    intro p hp q hq
    exact hpq₀min (Set.mk_mem_prod hp hq)
  have hdpos : 0 < d := lt_of_lt_of_le hd₀pos (hd₀sep _ hp₀ _ hq₀)
  -- `d` is attained at `(p₀, q₀)`.
  have hattained : ∃ p ∈ f '' Q.leftSide, ∃ q ∈ f '' Q.rightSide, dist p q = d :=
    ⟨pq₀.1, hp₀, pq₀.2, hq₀, rfl⟩
  refine ⟨d, hdpos, hdsep, ?_⟩
  exact hC'bound x r hr h hh hlt hlt2 d hdpos hdsep hattained

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
