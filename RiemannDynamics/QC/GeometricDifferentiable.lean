/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.SensePreserving
import RiemannDynamics.QC.ReverseLengthAreaForward
import RiemannDynamics.QC.LoewnerReciprocity
import RiemannDynamics.QC.ModulusSymmetrization
import RiemannDynamics.Analysis.Sobolev.Stepanov
import RiemannDynamics.Analysis.Sobolev.Coarea.Assembly
import RiemannDynamics.Hyperbolic.WindingNumber.CircleRectangleWinding
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.CoveringNumbers

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
`conjugateImageModulus_reciprocity` (its docstring names the absent classical ingredient).

The swapped axis-rectangle quadrilateral itself and its structural lemmas
(`axisRectQuadrilateralSwap`, `*_{image,leftSide,rightSide,toFun}`) live in
`QC/ReverseLengthAreaForward.lean` so the planar Loewner-reciprocity workstream
(`QC/LoewnerReciprocity.lean`) can reference the swap without depending on this heavy
file. The admissibility / modulus upper-bound bricks
(`axisRectDensitySwap_admissible`, `axisRectSwap_modulus_upper_bound`) are kept here
because they consume `funcIncrement_le_arcLength` (above), which lives in this file. -/

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
    (hpair : ∀ ρ ∈ I, g ρ ≠ ⊤ → ∀ σ ∈ J, h σ ≠ ⊤ → 1 ≤ g ρ * h σ) :
    1 ≤ (⨅ ρ ∈ I, g ρ) * (⨅ σ ∈ J, h σ) := by
  obtain ⟨ρ₀, hρ₀I, hρ₀0, hρ₀top⟩ := hSfin
  obtain ⟨σt, hσtJ, hσttop⟩ := hTtop
  obtain ⟨σn, hσnJ⟩ := hTne
  set A := ⨅ ρ ∈ I, g ρ with hAdef
  set B := ⨅ σ ∈ J, h σ with hBdef
  have hBtop : B ≠ ⊤ := ne_top_of_le_ne_top hσttop (biInf_le _ hσtJ)
  -- The pairwise bound is only assumed for finite-energy densities; for an infinite-energy `σ`
  -- (`h σ = ⊤`) the inequality `(g ·)⁻¹ ≤ h σ` is automatic, so the infimum argument is unaffected.
  have hB0 : B ≠ 0 := by
    have hle : (g ρ₀)⁻¹ ≤ B := by
      apply le_iInf₂; intro σ hσ
      rcases eq_or_ne (h σ) ⊤ with hσtop | hσtop
      · rw [hσtop]; exact le_top
      · rw [ENNReal.inv_le_iff_le_mul (fun _ => hρ₀0) (fun hh => absurd hh hρ₀top)]
        exact hpair ρ₀ hρ₀I hρ₀top σ hσ hσtop
    exact (lt_of_lt_of_le (ENNReal.inv_pos.mpr hρ₀top) hle).ne'
  have hxB : ∀ ρ ∈ I, 1 ≤ g ρ * B := by
    intro ρ hρI
    rcases eq_or_ne (g ρ) ⊤ with hgtop | hgtop
    · rw [hgtop, ENNReal.top_mul hB0]; exact le_top
    · -- `g ρ` finite: derive `g ρ ≠ 0` from the pairwise bound against the finite witness `σt`.
      have hx0 : g ρ ≠ 0 := by
        rintro hh
        have := hpair ρ hρI hgtop σt hσtJ hσttop
        rw [hh, zero_mul] at this; simp at this
      have hxinv_le : (g ρ)⁻¹ ≤ B := by
        apply le_iInf₂; intro σ hσJ
        rcases eq_or_ne (h σ) ⊤ with hσtop | hσtop
        · rw [hσtop]; exact le_top
        · rw [ENNReal.inv_le_iff_le_mul (fun _ => hx0) (fun hh => absurd hh hgtop)]
          exact hpair ρ hρI hgtop σ hσJ hσtop
      calc (1:ℝ≥0∞) = g ρ * (g ρ)⁻¹ := (ENNReal.mul_inv_cancel hx0 hgtop).symm
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

/-! ### Reusable Hausdorff / co-area primitives

The geodesic ρ-potential route to the cross-bound `1 ≤ ∫∫ ρσ` was retired (its sharp eikonal
`‖∇u‖ ≤ ρ` is false for finite-energy `ρ` — planar Kakeya/Nikodym; see
`imageConjugate_lengthArea_pairwise`).  The Hausdorff-measure / projection / packing lemmas below
are kept as reusable primitives for the correct crossing-principle reciprocity proof. -/

open RiemannDynamics.Coarea in
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




/-! ### Reusable measure-theory / path-algebra primitives

Generic helpers for absolutely-continuous curves: disjoint-interval combinatorics under monotone
reparametrization, affine change-of-variables for arc-length integrals, and the path-algebra
(`segPath`, `glueCurve`, `reversePath`).  Kept as reusable primitives for the crossing-principle
reciprocity build. -/

/-- **A monotone map preserves pairwise disjointness of `uIoc` intervals.** If the intervals
`uIoc (I i).1 (I i).2`, `i < n`, are pairwise disjoint and `φ` is monotone, then so are the
intervals `uIoc (φ (I i).1) (φ (I i).2)`, `i < n`. This is the combinatorial core needed to split
an absolutely-continuous disjoint family across a midpoint by clipping its endpoints. -/
theorem pairwiseDisjoint_uIoc_comp_monotone {φ : ℝ → ℝ} (hφ : Monotone φ)
    {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hI : Set.PairwiseDisjoint (Finset.range n) (fun i => Set.uIoc (I i).1 (I i).2)) :
    Set.PairwiseDisjoint (Finset.range n)
      (fun i => Set.uIoc (φ (I i).1) (φ (I i).2)) := by
  intro i hi j hj hij
  have hdisj := hI hi hj hij
  -- Translate `Disjoint` of `uIoc` into the `min/max ≤` criterion, push `φ` through.
  simp only [Function.onFun, Set.uIoc, Set.disjoint_iff_inter_eq_empty] at hdisj ⊢
  rw [← Set.disjoint_iff_inter_eq_empty, Set.Ioc_disjoint_Ioc] at hdisj ⊢
  -- `min/max` of `φ`-values equal `φ` of `min/max` by monotonicity.
  rw [← hφ.map_min, ← hφ.map_min, ← hφ.map_max, ← hφ.map_max,
    ← hφ.map_max, ← hφ.map_min]
  exact hφ hdisj

/-- **Absolute continuity is preserved by composing on the left with a function that is Lipschitz
on a set containing the image.** If `l` is `K`-Lipschitz on `S`, `F` is absolutely continuous on
`uIcc a b`, and `F` maps `uIcc a b` into `S`, then `l ∘ F` is absolutely continuous on `uIcc a b`.
This is the `LipschitzOnWith` upgrade of the repository's `LipschitzWith`-composition pattern. -/
theorem absolutelyContinuousOnInterval_comp_lipschitzOnWith
    {Y : Type*} [PseudoMetricSpace Y] {l : ℂ → Y} {K : NNReal} {S : Set ℂ}
    (hl : LipschitzOnWith K l S) {F : ℝ → ℂ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hmaps : ∀ t ∈ Set.uIcc a b, F t ∈ S) :
    AbsolutelyContinuousOnInterval (fun t => l (F t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have key := hδ' E hE hlen
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  -- Each endpoint of the disjoint family lies in `uIcc a b`, hence its `F`-image lies in `S`.
  have hmem : ∀ i ∈ Finset.range E.1,
      F (E.2 i).1 ∈ S ∧ F (E.2 i).2 ∈ S := by
    intro i hi
    exact ⟨hmaps _ (hE.1 i hi).1, hmaps _ (hE.1 i hi).2⟩
  calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
        Finset.sum_le_sum (fun i hi => by
          have hd := hl.dist_le_mul _ (hmem i hi).1 _ (hmem i hi).2
          exact hd)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
    _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]

/-- **Two-piece concatenation of absolute continuity.** If `a ≤ m ≤ b` and `f` is absolutely
continuous on `[a, m]` and on `[m, b]`, then `f` is absolutely continuous on `[a, b]`. This is the
genuinely-missing finite-cover concatenation: a disjoint family of intervals inside `[a, b]` is
split at `m` by clipping each endpoint with `min m ·` (landing in `[a, m]`) and `max m ·` (landing
in `[m, b]`); clipping is `1`-Lipschitz and monotone, so the two clipped families are disjoint, of
total length no larger than the original, and the chord through `f m` dominates the original chord
by the triangle inequality. -/
theorem absolutelyContinuousOnInterval_concat {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {a m b : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b)
    (hL : AbsolutelyContinuousOnInterval f a m)
    (hR : AbsolutelyContinuousOnInterval f m b) :
    AbsolutelyContinuousOnInterval f a b := by
  have hab : a ≤ b := le_trans ham hmb
  rw [absolutelyContinuousOnInterval_iff] at hL hR ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hL (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hR (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hlen => ?_⟩
  obtain ⟨n, I⟩ := E
  -- Clip maps: `min m ·` retracts `[a, b]` onto `[a, m]`; `max m ·` onto `[m, b]`.
  have hMinMono : Monotone (fun x : ℝ => min m x) := fun _ _ h => min_le_min le_rfl h
  have hMaxMono : Monotone (fun x : ℝ => max m x) := fun _ _ h => max_le_max le_rfl h
  -- Endpoints of `E` lie in `[a, b]`.
  have hEmem : ∀ i ∈ Finset.range n, (I i).1 ∈ Set.Icc a b ∧ (I i).2 ∈ Set.Icc a b := by
    intro i hi
    have h := hE.1 i hi
    rw [Set.uIcc_of_le hab] at h
    exact h
  -- The left-clipped family.
  set IL : ℕ → ℝ × ℝ := fun i => (min m (I i).1, min m (I i).2) with hIL
  set IR : ℕ → ℝ × ℝ := fun i => (max m (I i).1, max m (I i).2) with hIR
  -- Membership of clipped endpoints in the sub-intervals.
  have hmemL : ∀ i ∈ Finset.range n,
      min m (I i).1 ∈ Set.uIcc a m ∧ min m (I i).2 ∈ Set.uIcc a m := by
    intro i hi
    obtain ⟨⟨hi1a, hi1b⟩, ⟨hi2a, hi2b⟩⟩ := hEmem i hi
    rw [Set.uIcc_of_le ham]
    exact ⟨⟨le_min ham hi1a, min_le_left _ _⟩, ⟨le_min ham hi2a, min_le_left _ _⟩⟩
  have hmemR : ∀ i ∈ Finset.range n,
      max m (I i).1 ∈ Set.uIcc m b ∧ max m (I i).2 ∈ Set.uIcc m b := by
    intro i hi
    obtain ⟨⟨hi1a, hi1b⟩, ⟨hi2a, hi2b⟩⟩ := hEmem i hi
    rw [Set.uIcc_of_le hmb]
    exact ⟨⟨le_max_left _ _, max_le hmb hi1b⟩, ⟨le_max_left _ _, max_le hmb hi2b⟩⟩
  -- Disjointness of clipped families (monotone images of disjoint `uIoc`).
  have hdisjL : Set.PairwiseDisjoint (Finset.range n)
      (fun i => Set.uIoc (IL i).1 (IL i).2) :=
    pairwiseDisjoint_uIoc_comp_monotone hMinMono hE.2
  have hdisjR : Set.PairwiseDisjoint (Finset.range n)
      (fun i => Set.uIoc (IR i).1 (IR i).2) :=
    pairwiseDisjoint_uIoc_comp_monotone hMaxMono hE.2
  have hEL : ((n, IL) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin a m := ⟨hmemL, hdisjL⟩
  have hER : ((n, IR) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin m b := ⟨hmemR, hdisjR⟩
  -- Total lengths of clipped families do not exceed the original total length.
  -- Clipping is `1`-Lipschitz, so per-interval clipped length ≤ original length.
  have hMinLip : LipschitzWith 1 (fun x : ℝ => min m x) := LipschitzWith.id.const_min m
  have hMaxLip : LipschitzWith 1 (fun x : ℝ => max m x) := LipschitzWith.id.const_max m
  have hlenL : ∑ i ∈ Finset.range n, dist (IL i).1 (IL i).2 ≤
      ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
    apply Finset.sum_le_sum
    intro i _
    have := hMinLip.dist_le_mul (I i).1 (I i).2
    simpa only [hIL, NNReal.coe_one, one_mul] using this
  have hlenR : ∑ i ∈ Finset.range n, dist (IR i).1 (IR i).2 ≤
      ∑ i ∈ Finset.range n, dist (I i).1 (I i).2 := by
    apply Finset.sum_le_sum
    intro i _
    have := hMaxLip.dist_le_mul (I i).1 (I i).2
    simpa only [hIR, NNReal.coe_one, one_mul] using this
  -- Per-interval chord domination: the original chord splits through `f m`.
  have hchord : ∀ i ∈ Finset.range n,
      dist (f (I i).1) (f (I i).2) ≤
        dist (f (IL i).1) (f (IL i).2) + dist (f (IR i).1) (f (IR i).2) := by
    intro i _
    simp only [hIL, hIR]
    set u := (I i).1
    set v := (I i).2
    rcases le_total u m with h1 | h1 <;> rcases le_total v m with h2 | h2
    · -- both ≤ m : right chord collapses to `dist (f m) (f m) = 0`.
      rw [min_eq_right h1, min_eq_right h2, max_eq_left h1, max_eq_left h2, dist_self, add_zero]
    · -- u ≤ m ≤ v : split through `f m`.
      rw [min_eq_right h1, min_eq_left h2, max_eq_left h1, max_eq_right h2]
      exact dist_triangle (f u) (f m) (f v)
    · -- v ≤ m ≤ u : split through `f m`.
      rw [min_eq_left h1, min_eq_right h2, max_eq_right h1, max_eq_left h2]
      calc dist (f u) (f v) ≤ dist (f u) (f m) + dist (f m) (f v) := dist_triangle _ _ _
        _ = dist (f m) (f v) + dist (f u) (f m) := by rw [add_comm]
    · -- both ≥ m : left chord collapses to `dist (f m) (f m) = 0`.
      rw [min_eq_left h1, min_eq_left h2, max_eq_right h1, max_eq_right h2, dist_self, zero_add]
  -- Apply per-side AC bounds.
  have hltL : ∑ i ∈ Finset.range n, dist (IL i).1 (IL i).2 < δ₁ :=
    lt_of_le_of_lt hlenL (lt_of_lt_of_le hlen (min_le_left _ _))
  have hltR : ∑ i ∈ Finset.range n, dist (IR i).1 (IR i).2 < δ₂ :=
    lt_of_le_of_lt hlenR (lt_of_lt_of_le hlen (min_le_right _ _))
  have hsumL := hδ₁' (n, IL) hEL hltL
  have hsumR := hδ₂' (n, IR) hER hltR
  calc ∑ i ∈ Finset.range n, dist (f (I i).1) (f (I i).2)
      ≤ ∑ i ∈ Finset.range n,
          (dist (f (IL i).1) (f (IL i).2) + dist (f (IR i).1) (f (IR i).2)) :=
        Finset.sum_le_sum hchord
    _ = (∑ i ∈ Finset.range n, dist (f (IL i).1) (f (IL i).2)) +
          ∑ i ∈ Finset.range n, dist (f (IR i).1) (f (IR i).2) := by
        rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add hsumL hsumR
    _ = ε := by ring

/-! ### Path-concatenation and affine-reparametrization machinery (reusable, axiom-clean)

Arc-length-additive gluing of absolutely-continuous curves (`glueCurve`), affine `lintegral`
change-of-variables, and the straight-segment / reversal path-algebra.  Kept as reusable primitives
for the crossing-principle reciprocity build. -/

/-- **Affine `lintegral` substitution on an interval.** For `c > 0`,
`∫⁻ t in Icc p q, G(c t + d) = c⁻¹ · ∫⁻ s in Icc (c p + d) (c q + d), G s`. The change of variables
`s = c t + d` (translation + scaling, both measure-(quasi)preserving) via `setLIntegral_map`. -/
theorem lintegral_Icc_comp_affine {c d : ℝ} (hc : 0 < c) (p q : ℝ) (G : ℝ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ t in Set.Icc p q, G (c * t + d)
      = ENNReal.ofReal c⁻¹ * ∫⁻ s in Set.Icc (c * p + d) (c * q + d), G s := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hmeas : Measurable (fun t : ℝ => c * t + d) := (measurable_const_mul c).add_const d
  have hpre : (fun t : ℝ => c * t + d) ⁻¹' Set.Icc (c * p + d) (c * q + d) = Set.Icc p q := by
    ext t; simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by nlinarith, by nlinarith⟩
  have hkey := setLIntegral_map (μ := volume) (f := G) (g := fun t : ℝ => c * t + d)
    (s := Set.Icc (c * p + d) (c * q + d)) measurableSet_Icc hG hmeas
  have hmapeq : Measure.map (fun t : ℝ => c * t + d) volume
      = ENNReal.ofReal |c⁻¹| • (volume : Measure ℝ) := by
    rw [show (fun t : ℝ => c * t + d) = (fun s => d + s) ∘ (fun t => c * t) by
      funext t; simp [add_comm],
      ← Measure.map_map (measurable_const_add d) (measurable_const_mul c)]
    rw [Real.map_volume_mul_left hcne, Measure.map_smul, map_add_left_eq_self]
  rw [hmapeq, hpre, setLIntegral_smul_measure, abs_of_pos (inv_pos.mpr hc)] at hkey
  exact hkey.symm

/-- **An affine map sends planar-null sets to null preimages.** For `c ≠ 0`, the preimage of a
null set `N ⊆ ℝ` under `t ↦ c t + d` is null. (Decompose into translation, then scaling.) -/
theorem affine_preimage_null {c d : ℝ} (hc : c ≠ 0) {N : Set ℝ} (hN : volume N = 0) :
    volume ((fun t : ℝ => c * t + d) ⁻¹' N) = 0 := by
  have hdecomp : (fun t : ℝ => c * t + d) ⁻¹' N
      = (fun t : ℝ => c * t) ⁻¹' ((fun s => d + s) ⁻¹' N) := by
    ext t; simp [Set.mem_preimage, add_comm]
  rw [hdecomp]
  have h1 : volume ((fun s : ℝ => d + s) ⁻¹' N) = 0 := by rw [measure_preimage_add]; exact hN
  rw [Real.volume_preimage_mul_left hc, h1, mul_zero]

/-- **A.e. differentiability transfers along an affine reparametrization.** If `δ` is absolutely
continuous on `[0, 1]` (hence differentiable a.e.) and `t ↦ c t + d` maps `Ioo p q` into `Ioo 0 1`
(with `c > 0`), then `δ` is differentiable at `c t + d` for a.e. `t ∈ Ioo p q`. -/
theorem ae_diff_comp_affine {δ : ℝ → ℂ} (hδac : AbsolutelyContinuousOnInterval δ 0 1)
    {c d : ℝ} (hc : 0 < c) (p q : ℝ)
    (hmaps : ∀ t ∈ Set.Ioo p q, c * t + d ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo p q)), DifferentiableAt ℝ δ (c * t + d) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hδdiff : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ s :=
    hδac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  set BadS : Set ℝ := {s | s ∈ Set.uIcc (0:ℝ) 1 ∧ ¬ DifferentiableAt ℝ δ s} with hBadS
  have hBadS_null : volume BadS = 0 := by
    rw [ae_iff] at hδdiff; refine measure_mono_null (fun s hs => ?_) hδdiff
    exact fun himp => hs.2 (himp hs.1)
  have hpre_null := affine_preimage_null hcne hBadS_null (d := d)
  rw [ae_restrict_iff' measurableSet_Ioo, ae_iff]
  refine measure_mono_null (fun t ht => ?_) hpre_null
  have htIoo : t ∈ Set.Ioo p q := by by_contra h; exact ht (fun hh => absurd hh h)
  have htbad : ¬ DifferentiableAt ℝ δ (c * t + d) := fun hh => ht (fun _ => hh)
  exact ⟨Set.mem_uIcc.mpr (Or.inl ⟨(hmaps t htIoo).1.le, (hmaps t htIoo).2.le⟩), htbad⟩

/-- **Affine reparametrization preserves the ρ-arc-length integrand (open-interval form).** With
`c > 0` and the affine substitution `s = c t + d` mapping `Ioo p q → Ioo 0 1`, the chain-rule factor
`c` exactly cancels the substitution Jacobian `c⁻¹`. -/
theorem arcLength_comp_affine_Ioo (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (hδcont : Continuous δ)
    {c d : ℝ} (hc : 0 < c) (p q : ℝ)
    (hmaps : ∀ t ∈ Set.Ioo p q, c * t + d ∈ Set.Ioo (0 : ℝ) 1) :
    ∫⁻ t in Set.Ioo p q, ρ (δ (c * t + d)) * (‖deriv (fun t => δ (c * t + d)) t‖₊ : ℝ≥0∞)
      = ∫⁻ s in Set.Ioo (c * p + d) (c * q + d), ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞) := by
  have hchain : (fun t => ρ (δ (c * t + d)) * (‖deriv (fun t => δ (c * t + d)) t‖₊ : ℝ≥0∞))
      =ᶠ[ae (volume.restrict (Set.Ioo p q))]
      (fun t => ENNReal.ofReal c * (ρ (δ (c * t + d)) * (‖deriv δ (c * t + d)‖₊ : ℝ≥0∞))) := by
    filter_upwards [ae_diff_comp_affine hδac hc p q hmaps] with t htd
    have haff : HasDerivAt (fun t : ℝ => c * t + d) c t := by
      simpa using ((hasDerivAt_id t).const_mul c).add_const d
    have hderiv : deriv (fun t => δ (c * t + d)) t = c • deriv δ (c * t + d) := by
      have := (htd.hasDerivAt.scomp t haff); simpa [Function.comp] using this.deriv
    rw [hderiv]
    have hnorm : (‖(c:ℝ) • deriv δ (c*t+d)‖₊ : ℝ≥0∞)
        = ENNReal.ofReal c * (‖deriv δ (c*t+d)‖₊ : ℝ≥0∞) := by
      rw [Complex.real_smul]
      have h1 : ‖(c:ℂ) * deriv δ (c*t+d)‖ = c * ‖deriv δ (c*t+d)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, h1, ENNReal.ofReal_mul hc.le,
        ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    rw [hnorm]; ring
  rw [lintegral_congr_ae hchain, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hIooIcc1 : ∫⁻ t in Set.Ioo p q, ρ (δ (c * t + d)) * (‖deriv δ (c*t+d)‖₊ : ℝ≥0∞)
      = ∫⁻ t in Set.Icc p q, ρ (δ (c * t + d)) * (‖deriv δ (c*t+d)‖₊ : ℝ≥0∞) :=
    setLIntegral_congr Ioo_ae_eq_Icc
  have hIooIcc2 : ∫⁻ s in Set.Ioo (c*p+d) (c*q+d), ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞)
      = ∫⁻ s in Set.Icc (c*p+d) (c*q+d), ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞) :=
    setLIntegral_congr Ioo_ae_eq_Icc
  rw [hIooIcc1, hIooIcc2]
  have hGmeas : Measurable (fun s => ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞)) :=
    Measurable.mul (hρ.comp hδcont.measurable) (measurable_deriv δ).nnnorm.coe_nnreal_ennreal
  have hsub := lintegral_Icc_comp_affine (d := d) hc p q
    (fun s => ρ (δ s) * (‖deriv δ s‖₊ : ℝ≥0∞)) hGmeas
  rw [hsub, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ (ne_of_gt hc),
    ENNReal.ofReal_one, one_mul]

/-- **Absolute continuity transfers along an affine reparametrization.** If `δ` is AC on
`[c p + d, c q + d]` (`c > 0`), then `t ↦ δ(c t + d)` is AC on `[p, q]`. The affine map is monotone
Lipschitz, so it sends a disjoint family in `[p, q]` to a disjoint family in `[c p + d, c q + d]`
with lengths scaled by `c`. -/
theorem ac_comp_affine {δ : ℝ → ℂ} {c d : ℝ} (hc : 0 < c) {p q : ℝ}
    (hδ : AbsolutelyContinuousOnInterval δ (c * p + d) (c * q + d)) :
    AbsolutelyContinuousOnInterval (fun t => δ (c * t + d)) p q := by
  rw [absolutelyContinuousOnInterval_iff] at hδ ⊢
  intro ε hε
  obtain ⟨D, hD, hD'⟩ := hδ ε hε
  refine ⟨D / c, by positivity, fun E hE hlen => ?_⟩
  set aff : ℝ → ℝ := fun x => c * x + d with haff
  have hmono : Monotone aff := fun x y hxy => by simp only [haff]; nlinarith
  set IL : ℕ → ℝ × ℝ := fun i => (aff (E.2 i).1, aff (E.2 i).2) with hIL
  have hEmem : ((E.1, IL) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (c*p+d) (c*q+d) := by
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hE.1 i hi
      have hmaps : ∀ x ∈ Set.uIcc p q, aff x ∈ Set.uIcc (c*p+d) (c*q+d) := by
        intro x hx
        rw [Set.mem_uIcc] at hx ⊢
        rcases hx with hx | hx
        · refine Or.inl ⟨?_, ?_⟩ <;>
            (simp only [haff]; nlinarith [hx.1])
        · refine Or.inr ⟨?_, ?_⟩ <;>
            (simp only [haff]; nlinarith [hx.1])
      exact ⟨hmaps _ h.1, hmaps _ h.2⟩
    · exact pairwiseDisjoint_uIoc_comp_monotone hmono hE.2
  have hlenscale : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2
      = c * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hIL, haff, Real.dist_eq]
    rw [show c * (E.2 i).1 + d - (c * (E.2 i).2 + d) = c * ((E.2 i).1 - (E.2 i).2) by ring,
      abs_mul, abs_of_pos hc]
  have hlen' : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2 < D := by
    rw [hlenscale]
    calc c * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2
        < c * (D / c) := mul_lt_mul_of_pos_left hlen hc
      _ = D := by field_simp
  have hkey := hD' (E.1, IL) hEmem hlen'
  convert hkey using 1

/-- **Absolute continuity is determined by the values on the interval.** If `f = g` on `uIcc a b`,
then `f` AC on `[a, b]` implies `g` AC on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_congr {f g : ℝ → ℂ} {a b : ℝ}
    (h : Set.EqOn f g (Set.uIcc a b)) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨d, hd, hd'⟩ := hf ε hε
  refine ⟨d, hd, fun E hE hlen => ?_⟩
  have hkey := hd' E hE hlen
  have heq : ∀ i ∈ Finset.range E.1,
      dist (g (E.2 i).1) (g (E.2 i).2) = dist (f (E.2 i).1) (f (E.2 i).2) := by
    intro i hi; rw [← h (hE.1 i hi).1, ← h (hE.1 i hi).2]
  rw [Finset.sum_congr rfl heq]; exact hkey

/-! #### The straight segment path and the geodesic glue -/

/-- The straight segment `t ↦ z + t (y − z)` from `z` to `y`, parametrized affinely on `[0, 1]`. -/
noncomputable def segPath (z y : ℂ) : ℝ → ℂ := fun t => z + (t : ℂ) * (y - z)

theorem segPath_zero (z y : ℂ) : segPath z y 0 = z := by simp [segPath]
theorem segPath_one (z y : ℂ) : segPath z y 1 = y := by simp [segPath]

theorem segPath_hasDerivAt (z y : ℂ) (t : ℝ) : HasDerivAt (segPath z y) (y - z) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (y - z)) (y - z) t := by
    have : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
    simpa using this.mul_const (y - z)
  have h2 : HasDerivAt (fun t : ℝ => z + (t : ℂ) * (y - z)) (y - z) t := by
    have := (hasDerivAt_const t z).add h1; rwa [zero_add] at this
  exact h2

theorem segPath_deriv (z y : ℂ) (t : ℝ) : deriv (segPath z y) t = y - z :=
  (segPath_hasDerivAt z y t).deriv

theorem segPath_continuous (z y : ℂ) : Continuous (segPath z y) := by
  unfold segPath
  exact continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)

theorem segPath_lipschitz (z y : ℂ) :
    LipschitzWith (Real.toNNReal ‖y - z‖) (segPath z y) := by
  refine LipschitzWith.of_dist_le_mul (fun t₁ t₂ => ?_)
  unfold segPath
  rw [Complex.dist_eq]
  have : (z + (t₁ : ℂ) * (y - z)) - (z + (t₂ : ℂ) * (y - z))
      = ((t₁ - t₂ : ℝ) : ℂ) * (y - z) := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.coe_toNNReal _ (norm_nonneg _), Real.dist_eq, mul_comm]

theorem segPath_ac (z y : ℂ) : AbsolutelyContinuousOnInterval (segPath z y) 0 1 :=
  ((segPath_lipschitz z y).lipschitzOnWith).absolutelyContinuousOnInterval

/-- The ρ-arc-length of the straight segment `[z, y]` is `∫₀¹ ρ(z + t(y−z)) · ‖y − z‖ dt`. -/
theorem arcLengthLineIntegral_segPath (ρ : ℂ → ℝ≥0∞) (z y : ℂ) :
    arcLengthLineIntegral ρ (segPath z y)
      = ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (segPath z y t) * (‖y - z‖₊ : ℝ≥0∞) := by
  unfold arcLengthLineIntegral
  refine setLIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
  simp only [segPath_deriv]

/-- The **glue** of two curves `δ` (covering `[0, 1/2]` via `t ↦ δ(2t)`) and `δp` (covering
`[1/2, 1]` via `t ↦ δp(2t − 1)`). When `δ 1 = δp 0` this is the concatenation `δ` then `δp`,
reparametrized to `[0, 1]`. -/
noncomputable def glueCurve (δ δp : ℝ → ℂ) : ℝ → ℂ :=
  fun t => if t ≤ 1/2 then δ (2 * t) else δp (2 * t - 1)

theorem glueCurve_continuous {δ δp : ℝ → ℂ} (hδc : Continuous δ) (hδpc : Continuous δp)
    (hmatch : δ 1 = δp 0) : Continuous (glueCurve δ δp) := by
  unfold glueCurve
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  · exact hδc.comp (by fun_prop)
  · exact hδpc.comp (by fun_prop)
  · intro x hx; rw [hx]; norm_num; rw [hmatch]

theorem glueCurve_zero (δ δp : ℝ → ℂ) : glueCurve δ δp 0 = δ 0 := by simp [glueCurve]
theorem glueCurve_one (δ δp : ℝ → ℂ) : glueCurve δ δp 1 = δp 1 := by
  simp only [glueCurve]; rw [if_neg (by norm_num)]; norm_num

theorem glueCurve_eqOn_left (δ δp : ℝ → ℂ) :
    Set.EqOn (fun t => δ (2*t+0)) (glueCurve δ δp) (Set.uIcc 0 (1/2)) := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
  simp only [glueCurve, add_zero]; rw [if_pos (by linarith [ht.2])]

theorem glueCurve_eqOn_right {δ δp : ℝ → ℂ} (hmatch : δ 1 = δp 0) :
    Set.EqOn (fun t => δp (2*t+(-1))) (glueCurve δ δp) (Set.uIcc (1/2) 1) := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
  simp only [glueCurve]
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; norm_num [← hmatch]
  · rw [if_neg (by linarith)]; ring_nf

theorem glueCurve_mem {δ δp : ℝ → ℂ} {S : Set ℂ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ S) (hδp : ∀ t ∈ Set.Icc (0 : ℝ) 1, δp t ∈ S) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, glueCurve δ δp t ∈ S := by
  intro t ht
  rw [Set.mem_Icc] at ht
  simp only [glueCurve]
  by_cases h : t ≤ 1/2
  · rw [if_pos h]; exact hδ _ (Set.mem_Icc.mpr ⟨by linarith [ht.1], by linarith⟩)
  · rw [if_neg h]; exact hδp _ (Set.mem_Icc.mpr ⟨by linarith, by linarith [ht.2]⟩)

theorem glueCurve_ac {δ δp : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1)
    (hδpac : AbsolutelyContinuousOnInterval δp 0 1) (hmatch : δ 1 = δp 0) :
    AbsolutelyContinuousOnInterval (glueCurve δ δp) 0 1 := by
  refine absolutelyContinuousOnInterval_concat (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) ≤ 1) ?_ ?_
  · have hpiece : AbsolutelyContinuousOnInterval (fun t => δ (2*t+0)) 0 (1/2) := by
      apply ac_comp_affine (c := 2) (d := 0) (by norm_num) (p := 0) (q := 1/2)
      have he1 : (2:ℝ)*0+0 = 0 := by norm_num
      have he2 : (2:ℝ)*(1/2)+0 = 1 := by norm_num
      rw [he1, he2]; exact hδac
    exact absolutelyContinuousOnInterval_congr (glueCurve_eqOn_left δ δp) hpiece
  · have hpiece : AbsolutelyContinuousOnInterval (fun t => δp (2*t+(-1))) (1/2) 1 := by
      apply ac_comp_affine (c := 2) (d := -1) (by norm_num) (p := 1/2) (q := 1)
      have he1 : (2:ℝ)*(1/2)+(-1) = 0 := by norm_num
      have he2 : (2:ℝ)*1+(-1) = 1 := by norm_num
      rw [he1, he2]; exact hδpac
    exact absolutelyContinuousOnInterval_congr (glueCurve_eqOn_right hmatch) hpiece

/-- **Arc-length of the glue is additive.** `arcLength(glue δ δp) = arcLength δ + arcLength δp`,
from the affine-reparametrization arc-length invariance on each half. -/
theorem arcLengthLineIntegral_glueCurve (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) {δ δp : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (hδcont : Continuous δ)
    (hδpac : AbsolutelyContinuousOnInterval δp 0 1) (hδpcont : Continuous δp) :
    arcLengthLineIntegral ρ (glueCurve δ δp)
      = arcLengthLineIntegral ρ δ + arcLengthLineIntegral ρ δp := by
  have hglue_split : arcLengthLineIntegral ρ (glueCurve δ δp)
      = (∫⁻ t in Set.Icc (0:ℝ) (1/2), ρ (glueCurve δ δp t) * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞))
        + ∫⁻ t in Set.Ioc (1/2:ℝ) 1, ρ (glueCurve δ δp t)
            * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞) := by
    unfold arcLengthLineIntegral
    have hun : Set.Icc (0:ℝ) 1 = Set.Icc (0:ℝ) (1/2) ∪ Set.Ioc (1/2:ℝ) 1 := by
      rw [Set.Icc_union_Ioc_eq_Icc (by norm_num) (by norm_num)]
    rw [hun, lintegral_union measurableSet_Ioc
      (Set.disjoint_left.mpr (fun x hx hx' => by
        simp only [Set.mem_Icc, Set.mem_Ioc] at hx hx'; linarith [hx.2, hx'.1]))]
  rw [hglue_split]
  congr 1
  · unfold arcLengthLineIntegral
    rw [← setLIntegral_congr Ioo_ae_eq_Icc]
    have hpt : ∀ t ∈ Set.Ioo (0:ℝ) (1/2),
        ρ (glueCurve δ δp t) * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞)
          = ρ (δ (2*t+0)) * (‖deriv (fun t => δ (2*t+0)) t‖₊ : ℝ≥0∞) := by
      intro t ht
      have hval : glueCurve δ δp t = δ (2*t+0) := by
        simp only [glueCurve, add_zero]; rw [if_pos (by linarith [ht.2])]
      have hderiv : deriv (glueCurve δ δp) t = deriv (fun t => δ (2*t+0)) t := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        simp only [glueCurve, Set.mem_Ioo, add_zero] at hs ⊢; rw [if_pos hs.2.le]
      rw [hval, hderiv]
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt]
    have hkey := arcLength_comp_affine_Ioo ρ hρ hδac hδcont (c := 2) (d := 0) (by norm_num) 0 (1/2)
      (fun t ht => by constructor <;> [linarith [ht.1]; (simp only [add_zero]; linarith [ht.2])])
    rw [hkey]
    have hb1 : (2:ℝ)*0+0 = 0 := by norm_num
    have hb2 : (2:ℝ)*(1/2)+0 = 1 := by norm_num
    rw [hb1, hb2, setLIntegral_congr (Ioo_ae_eq_Icc (a := (0:ℝ)) (b := 1))]
  · unfold arcLengthLineIntegral
    rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
    have hpt : ∀ t ∈ Set.Ioo (1/2:ℝ) 1,
        ρ (glueCurve δ δp t) * (‖deriv (glueCurve δ δp) t‖₊ : ℝ≥0∞)
          = ρ (δp (2*t+(-1))) * (‖deriv (fun t => δp (2*t+(-1))) t‖₊ : ℝ≥0∞) := by
      intro t ht
      have hval : glueCurve δ δp t = δp (2*t+(-1)) := by
        simp only [glueCurve]; rw [if_neg (by linarith [ht.1])]; ring_nf
      have hderiv : deriv (glueCurve δ δp) t = deriv (fun t => δp (2*t+(-1))) t := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        simp only [glueCurve, Set.mem_Ioo] at hs ⊢
        rw [if_neg (by linarith [hs.1])]; ring_nf
      rw [hval, hderiv]
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt]
    have hkey := arcLength_comp_affine_Ioo ρ hρ hδpac hδpcont (c := 2) (d := -1) (by norm_num)
      (1/2) 1 (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    rw [hkey]
    have hb1 : (2:ℝ)*(1/2)+(-1) = 0 := by norm_num
    have hb2 : (2:ℝ)*1+(-1) = 1 := by norm_num
    rw [hb1, hb2, setLIntegral_congr (Ioo_ae_eq_Icc (a := (0:ℝ)) (b := 1))]



section RhoPotentialWitness

variable {f : ℂ → ℂ} {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}







/-! #### Path-reversal helpers and a.e. differentiability of AC curves

For the two-sided cheap-connector statement we need to turn a cheap route `z ⤳ y` into a cheap
route `y ⤳ z`. The reversal `reversePath δ t = δ (1 − t)` keeps continuity, absolute continuity,
image-membership, swaps the endpoints, and — crucially — has the **same** `ρ`-arc-length
(`arcLengthLineIntegral_reversePath`), because its derivative is the negative of `δ'(1 − t)` (so
the integrand is unchanged after the measure-preserving reflection `t ↦ 1 − t` of the unit
interval). -/

/-- The **reversal** of a path `δ : ℝ → ℂ`, parametrized on `[0, 1]`: `reversePath δ t = δ (1 − t)`.
It traverses `δ` backwards, swapping the endpoints. -/
noncomputable def reversePath (δ : ℝ → ℂ) : ℝ → ℂ := fun t => δ (1 - t)

@[simp] theorem reversePath_zero (δ : ℝ → ℂ) : reversePath δ 0 = δ 1 := by simp [reversePath]
@[simp] theorem reversePath_one (δ : ℝ → ℂ) : reversePath δ 1 = δ 0 := by simp [reversePath]

theorem reversePath_continuous {δ : ℝ → ℂ} (hδ : Continuous δ) : Continuous (reversePath δ) :=
  hδ.comp (by fun_prop)

theorem reversePath_mem {δ : ℝ → ℂ} {S : Set ℂ}
    (hδ : ∀ t ∈ Set.Icc (0 : ℝ) 1, δ t ∈ S) : ∀ t ∈ Set.Icc (0 : ℝ) 1, reversePath δ t ∈ S := by
  intro t ht; rw [Set.mem_Icc] at ht
  exact hδ _ (Set.mem_Icc.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩)

/-- **Absolute continuity is preserved under path reversal.** The reflection `x ↦ 1 − x` is a
length-preserving, disjointness-preserving bijection of `[0, 1]`, so the `ε`-`δ` total-variation
criterion transfers verbatim. -/
theorem reversePath_ac {δ : ℝ → ℂ} (hδ : AbsolutelyContinuousOnInterval δ 0 1) :
    AbsolutelyContinuousOnInterval (reversePath δ) 0 1 := by
  have hmin : ∀ p q : ℝ, min (1 - p) (1 - q) = 1 - max p q := by
    intro p q; rw [max_def]; split_ifs with h
    · rw [min_eq_right (by linarith)]
    · rw [min_eq_left (by linarith)]
  have hmax : ∀ p q : ℝ, max (1 - p) (1 - q) = 1 - min p q := by
    intro p q; rw [min_def]; split_ifs with h
    · rw [max_eq_left (by linarith)]
    · rw [max_eq_right (by linarith)]
  rw [absolutelyContinuousOnInterval_iff] at hδ ⊢
  intro ε hε
  obtain ⟨D, hD, hD'⟩ := hδ ε hε
  refine ⟨D, hD, fun E hE hlen => ?_⟩
  set IL : ℕ → ℝ × ℝ := fun i => (1 - (E.2 i).1, 1 - (E.2 i).2) with hIL
  have hEmem : ((E.1, IL) : ℕ × (ℕ → ℝ × ℝ)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (0:ℝ) 1 := by
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hE.1 i hi
      have hmaps : ∀ x ∈ Set.uIcc (0:ℝ) 1, (1 - x) ∈ Set.uIcc (0:ℝ) 1 := by
        intro x hx
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at hx
        rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc]
        exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
      exact ⟨hmaps _ h.1, hmaps _ h.2⟩
    · intro i hi j hj hij
      have hdisj := hE.2 hi hj hij
      simp only [Function.onFun, hIL, Set.uIoc, Set.disjoint_iff_inter_eq_empty] at hdisj ⊢
      rw [← Set.disjoint_iff_inter_eq_empty, Set.Ioc_disjoint_Ioc] at hdisj ⊢
      rw [hmin, hmin, hmax, hmax, hmin, hmax]
      linarith [hdisj]
  have hlenscale : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2
      = ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hIL, Real.dist_eq]
    rw [show (1 - (E.2 i).1) - (1 - (E.2 i).2) = -((E.2 i).1 - (E.2 i).2) by ring, abs_neg]
  have hlen' : ∑ i ∈ Finset.range E.1, dist (IL i).1 (IL i).2 < D := by
    rw [hlenscale]; exact hlen
  have hkey := hD' (E.1, IL) hEmem hlen'
  convert hkey using 2 with i hi

/-- **A.e. differentiability of an absolutely continuous `ℂ`-valued curve.** Its real and imaginary
parts are absolutely continuous (compose with the `1`-Lipschitz coordinate projections), hence
differentiable a.e. by Mathlib's `AbsolutelyContinuousOnInterval.ae_differentiableAt`; a function
`ℝ → ℂ` is `ℝ`-differentiable wherever both parts are. -/
theorem ac_complex_ae_differentiableAt {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) :
    ∀ᵐ x, x ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ x := by
  have hreL : LipschitzWith 1 (fun z : ℂ => z.re) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_re]
    rw [dist_eq_norm]; exact Complex.abs_re_le_norm _
  have himL : LipschitzWith 1 (fun z : ℂ => z.im) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, ← Complex.sub_im]
    rw [dist_eq_norm]; exact Complex.abs_im_le_norm _
  have hre : AbsolutelyContinuousOnInterval (fun t => (δ t).re) 0 1 :=
    absolutelyContinuousOnInterval_comp_lipschitzOnWith (S := Set.univ)
      hreL.lipschitzOnWith hδac (fun t _ => Set.mem_univ _)
  have him : AbsolutelyContinuousOnInterval (fun t => (δ t).im) 0 1 :=
    absolutelyContinuousOnInterval_comp_lipschitzOnWith (S := Set.univ)
      himL.lipschitzOnWith hδac (fun t _ => Set.mem_univ _)
  filter_upwards [hre.ae_differentiableAt, him.ae_differentiableAt] with x hxr hxi hmem
  have hr := hxr hmem
  have hi := hxi hmem
  have heq : δ = fun t => Complex.equivRealProdCLM.symm ((δ t).re, (δ t).im) := by
    ext t; simp [Complex.equivRealProdCLM_symm_apply]
  rw [heq]
  exact (Complex.equivRealProdCLM.symm.differentiableAt).comp x (hr.prodMk hi)

/-- **Path reversal preserves the `ρ`-arc-length.** Since `deriv (reversePath δ) t = −δ'(1 − t)`
a.e. (`δ` is differentiable a.e. by `ac_complex_ae_differentiableAt`), the integrand is unchanged in
norm, and the measure-preserving reflection `t ↦ 1 − t` of the unit interval leaves the integral
fixed. -/
theorem arcLengthLineIntegral_reversePath (ρ : ℂ → ℝ≥0∞) (hρ : Measurable ρ) {δ : ℝ → ℂ}
    (hδac : AbsolutelyContinuousOnInterval δ 0 1) (hδcont : Continuous δ) :
    arcLengthLineIntegral ρ (reversePath δ) = arcLengthLineIntegral ρ δ := by
  have hδac_diff := ac_complex_ae_differentiableAt hδac
  unfold arcLengthLineIntegral
  have hmp : MeasurePreserving (fun x : ℝ => 1 - x) volume volume :=
    volume.measurePreserving_sub_left 1
  have hbad : ∀ᵐ t, (1 - t) ∈ Set.uIcc (0:ℝ) 1 → DifferentiableAt ℝ δ (1 - t) :=
    hmp.quasiMeasurePreserving.ae hδac_diff
  have hcong : ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (reversePath δ t) * (‖deriv (reversePath δ) t‖₊ : ℝ≥0∞)
      = ∫⁻ t in Set.Icc (0:ℝ) 1, ρ (δ (1 - t)) * (‖deriv δ (1 - t)‖₊ : ℝ≥0∞) := by
    refine lintegral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hbad] with t hbt ht
    have hmem : (1 - t) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.mem_Icc] at ht
      rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc]
      exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
    have hdiff := hbt hmem
    have haff : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      simpa using (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    have hHD : HasDerivAt (reversePath δ) (-1 • deriv δ (1 - t)) t := by
      simpa [reversePath, Function.comp] using (hdiff.hasDerivAt.scomp t haff)
    change ρ (δ (1 - t)) * (‖deriv (reversePath δ) t‖₊ : ℝ≥0∞)
        = ρ (δ (1 - t)) * (‖deriv δ (1 - t)‖₊ : ℝ≥0∞)
    rw [hHD.deriv]
    congr 2
    simp
  rw [hcong]
  have hG : Measurable (fun u => ρ (δ u) * (‖deriv δ u‖₊ : ℝ≥0∞)) :=
    Measurable.mul (hρ.comp hδcont.measurable) (measurable_deriv δ).nnnorm.coe_nnreal_ennreal
  have hset : (fun x : ℝ => 1 - x) ⁻¹' (Set.Icc (0:ℝ) 1) = Set.Icc (0:ℝ) 1 := by
    ext x; simp only [Set.mem_preimage, Set.mem_Icc]
    exact ⟨fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩,
           fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩⟩
  have hkey := hmp.setLIntegral_comp_preimage (s := Set.Icc (0:ℝ) 1) measurableSet_Icc hG
  rw [hset] at hkey
  exact hkey

/-! ### Point-set topology of the plane-separation core (fully proven, Brouwer-free)

The lemmas in this section establish the abstract level-continuum existence statement
`rect_level_continuum` via the genuinely two-dimensional boundary-bumping crux `rectLevel_no_split`
(the corrected, **true** `hsep`-form — see its docstring for the FALSE earlier version it replaces).
**The entire section is proven and axiom-clean**: the rectangle geometry
(`rectLevel_isCompact_rect`, `rectLevel_isConnected_rect`), the **Šura–Bura quasi-component
separation** (`rectLevel_exists_isClopen_separating`) and component-extraction
(`rectLevel_split_of_no_continuum`), the continuous-argument confinement lemmas
(`confined_{cos,sin}_{pos,neg}_branch`) and the winding contradiction
(`square_crossing_contradiction`), assembled in `rectLevel_no_split` by the gap-threading route.
The sole non-elementary input is the continuous logarithm of a nonvanishing map on the contractible
rectangle (`continuous_log_lift_param_of_continuous_ne_zero`), which is strictly weaker than
Brouwer and already proven axiom-clean in the repository. -/

/-- The closed coordinate rectangle `[a,b] × [s,t]` in `ℂ` (used only in this section). -/
private def rectLevelRect (a b s t : ℝ) : Set ℂ :=
  {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ (s ≤ z.im ∧ z.im ≤ t)}

private theorem rectLevel_continuous_mk_left (s : ℝ) :
    Continuous (fun x : ℝ => Complex.mk x s) := by
  have : (fun x : ℝ => Complex.mk x s) = (fun x : ℝ => (x : ℂ) + s * Complex.I) := by
    funext x; apply Complex.ext <;> simp
  rw [this]; fun_prop

/-- A single clopen neighbourhood of `x` disjoint from a closed `Q`, given that the connected
component of `x` is disjoint from `Q`. (Compact Hausdorff quasi-component step.) -/
private theorem rectLevel_exists_clopen_nbhd_disjoint {K : Type*} [TopologicalSpace K] [T2Space K]
    [CompactSpace K] {Q : Set K} (hQc : IsClosed Q) {x : K}
    (hxQ : Disjoint (connectedComponent x) Q) :
    ∃ C : Set K, IsClopen C ∧ x ∈ C ∧ Disjoint C Q := by
  rw [connectedComponent_eq_iInter_isClopen x] at hxQ
  have hQcompact : IsCompact Q := hQc.isCompact
  rw [disjoint_iff_inter_eq_empty] at hxQ
  have hempty : (Q ∩ ⋂ s : { s : Set K // IsClopen s ∧ x ∈ s }, (s : Set K)) = ∅ := by
    rw [inter_comm]; exact hxQ
  by_contra hcon
  push Not at hcon
  have hne : (Q ∩ ⋂ s : { s : Set K // IsClopen s ∧ x ∈ s }, (s : Set K)).Nonempty := by
    apply hQcompact.inter_iInter_nonempty
    · intro i; exact i.2.1.1
    · intro u
      set C : Set K := ⋂ i ∈ u, (i : Set K) with hC
      have hCclopen : IsClopen C := by rw [hC]; exact isClopen_biInter_finset (fun i _ => i.2.1)
      have hxC : x ∈ C := by rw [hC]; exact mem_biInter (fun i _ => i.2.2)
      have := hcon C hCclopen hxC
      rw [not_disjoint_iff] at this
      obtain ⟨z, hzC, hzQ⟩ := this
      exact ⟨z, hzQ, hzC⟩
  rw [hempty] at hne
  exact absurd hne (by simp)

/-- **Šura–Bura separation.** In a compact Hausdorff space, if `P` and `Q` are closed and no
preconnected subset meets both, then a clopen set contains `P` and is disjoint from `Q`.

This is the genuinely-missing-from-Mathlib continuum-theory primitive; it is **proven** here
(axiom-clean) from `connectedComponent_eq_iInter_isClopen` plus compactness. -/
private theorem rectLevel_exists_isClopen_separating {K : Type*} [TopologicalSpace K] [T2Space K]
    [CompactSpace K] {P Q : Set K} (hPc : IsClosed P) (hQc : IsClosed Q)
    (hsep : ∀ S : Set K, IsPreconnected S → (S ∩ P).Nonempty → (S ∩ Q).Nonempty → False) :
    ∃ U : Set K, IsClopen U ∧ P ⊆ U ∧ Disjoint U Q := by
  have hcomp : ∀ x ∈ P, Disjoint (connectedComponent x) Q := by
    intro x hxP
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne
    rw [← Ne, ← nonempty_iff_ne_empty] at hne
    exact hsep (connectedComponent x) isConnected_connectedComponent.isPreconnected
      ⟨x, mem_connectedComponent, hxP⟩ hne
  choose! C hCclopen hxC hCQ using fun x (hx : x ∈ P) =>
    rectLevel_exists_clopen_nbhd_disjoint hQc (hcomp x hx)
  have hPcompact : IsCompact P := hPc.isCompact
  obtain ⟨u, husub, hufin, hucover⟩ := hPcompact.elim_finite_subcover_image
    (b := P) (c := C) (fun x hx => (hCclopen x hx).isOpen)
    (fun x hx => mem_biUnion hx (hxC x hx))
  refine ⟨⋃ x ∈ u, C x, ?_, hucover, ?_⟩
  · exact Set.Finite.isClopen_biUnion hufin (fun x hx => hCclopen x (husub hx))
  · rw [Set.disjoint_left]
    rintro z hz hzQ
    rw [mem_iUnion₂] at hz
    obtain ⟨x, hxu, hzCx⟩ := hz
    exact (hCQ x (husub hxu)).le_bot ⟨hzCx, hzQ⟩

private theorem rectLevel_rect_eq_reProdIm (a b s t : ℝ) :
    rectLevelRect a b s t = Set.Icc a b ×ℂ Set.Icc s t := by
  ext z; simp only [rectLevelRect, mem_setOf_eq, Complex.mem_reProdIm, Set.mem_Icc]

private theorem rectLevel_isCompact_rect (a b s t : ℝ) : IsCompact (rectLevelRect a b s t) := by
  rw [rectLevel_rect_eq_reProdIm]; exact (isCompact_Icc).reProdIm (isCompact_Icc)

private theorem rectLevel_isClosed_rect (a b s t : ℝ) : IsClosed (rectLevelRect a b s t) :=
  (rectLevel_isCompact_rect a b s t).isClosed

private theorem rectLevel_isConnected_rect {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t) :
    IsConnected (rectLevelRect a b s t) := by
  have hpre : rectLevelRect a b s t = Complex.equivRealProdCLM.toHomeomorph ⁻¹'
      (Set.Icc a b ×ˢ Set.Icc s t) := by
    ext z
    constructor
    · intro h
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
        ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_apply]
      exact ⟨⟨h.1.1, h.1.2⟩, ⟨h.2.1, h.2.2⟩⟩
    · intro h
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc,
        ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_apply] at h
      exact ⟨⟨h.1.1, h.1.2⟩, ⟨h.2.1, h.2.2⟩⟩
  rw [hpre, Homeomorph.isConnected_preimage]
  exact (isConnected_Icc hab).prod (isConnected_Icc hst)

/-- On the horizontal segment at height `lvl`, the continuous `v` takes every value between its
endpoint values; in particular it attains `c ∈ (0,1)` when the endpoints are `0`, `1` (1-D IVT). -/
private theorem rectLevel_exists_mem_level_on_edge {a b lvl : ℝ} (hab : a ≤ b) {v : ℂ → ℝ}
    (hvcont : Continuous v) (hv0 : v (Complex.mk a lvl) = 0) (hv1 : v (Complex.mk b lvl) = 1)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc a b, v (Complex.mk x lvl) = c := by
  have hcont : ContinuousOn (fun x : ℝ => v (Complex.mk x lvl)) (Set.Icc a b) :=
    (hvcont.comp (rectLevel_continuous_mk_left lvl)).continuousOn
  have hsub : Set.Icc (v (Complex.mk a lvl)) (v (Complex.mk b lvl)) ⊆
      (fun x : ℝ => v (Complex.mk x lvl)) '' Set.Icc a b := intermediate_value_Icc hab hcont
  have hcmem : c ∈ Set.Icc (v (Complex.mk a lvl)) (v (Complex.mk b lvl)) := by
    rw [hv0, hv1]; exact ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  obtain ⟨x, hx, hvx⟩ := hsub hcmem
  exact ⟨x, hx, hvx⟩

/-- If a compact `K ⊆ ℂ` has nonempty closed subsets `Bot, Top` not joined by any preconnected
subset of `K`, then `K` splits into two disjoint compacta `K₁ ⊇ Bot`, `K₂ ⊇ Top` with union `K`.
(Šura–Bura in the subtype, pushed to ambient `ℂ`.) -/
private theorem rectLevel_split_of_no_continuum {K Bot Top : Set ℂ} (hK : IsCompact K)
    (hBot : Bot ⊆ K) (hTop : Top ⊆ K) (hBotcl : IsClosed Bot) (hTopcl : IsClosed Top)
    (hsep : ∀ S : Set ℂ, IsPreconnected S → S ⊆ K →
      (S ∩ Bot).Nonempty → (S ∩ Top).Nonempty → False) :
    ∃ K₁ K₂ : Set ℂ, IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧
      K₁ ∪ K₂ = K ∧ Bot ⊆ K₁ ∧ Top ⊆ K₂ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set P : Set K := Subtype.val ⁻¹' Bot with hP
  set Q : Set K := Subtype.val ⁻¹' Top with hQ
  have hPc : IsClosed P := hBotcl.preimage continuous_subtype_val
  have hQc : IsClosed Q := hTopcl.preimage continuous_subtype_val
  have hsep' : ∀ S : Set K, IsPreconnected S → (S ∩ P).Nonempty → (S ∩ Q).Nonempty → False := by
    intro S hScon hSP hSQ
    refine hsep (Subtype.val '' S) (hScon.image _ continuous_subtype_val.continuousOn)
      (Subtype.coe_image_subset _ _) ?_ ?_
    · obtain ⟨z, hzS, hzP⟩ := hSP
      exact ⟨z.1, ⟨z, hzS, rfl⟩, hzP⟩
    · obtain ⟨z, hzS, hzQ⟩ := hSQ
      exact ⟨z.1, ⟨z, hzS, rfl⟩, hzQ⟩
  obtain ⟨U, hUclopen, hPU, hUQ⟩ := rectLevel_exists_isClopen_separating hPc hQc hsep'
  refine ⟨Subtype.val '' U, Subtype.val '' Uᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hUclopen.1.isCompact).image continuous_subtype_val
  · exact (hUclopen.compl.1.isCompact).image continuous_subtype_val
  · rw [Set.disjoint_left]
    rintro z ⟨x, hxU, rfl⟩ ⟨y, hyU, hxy⟩
    have : y = x := Subtype.val_injective hxy
    rw [this] at hyU; exact hyU hxU
  · rw [← Set.image_union, Set.union_compl_self, Set.image_univ, Subtype.range_coe]
  · intro z hz
    have hzK : z ∈ K := hBot hz
    refine ⟨⟨z, hzK⟩, hPU ?_, rfl⟩; simpa [hP] using hz
  · intro z hz
    have hzK : z ∈ K := hTop hz
    refine ⟨⟨z, hzK⟩, ?_, rfl⟩
    have hzQ : (⟨z, hzK⟩ : K) ∈ Q := by simpa [hQ] using hz
    rw [Set.mem_compl_iff]
    intro hzU; exact (Set.disjoint_left.mp hUQ hzU) hzQ

/-! ### Continuous-argument confinement and the square-crossing winding contradiction

The lemmas below provide the genuinely two-dimensional ingredient of the boundary-bumping crux,
**Brouwer-free**: a single-valued continuous argument `θ` on the rectangle whose cosine/sine are
sign-constrained on the four edges (`Im φ > 0` on the bottom, `Re φ > 0` on the right, `Im φ < 0`
on the top, `Re φ < 0` on the left) is impossible, because the four half-plane confinements force a
net winding of `±2π` while single-valuedness forces winding `0`. The only non-elementary input is
the **continuous logarithm** of a nonvanishing map on the (simply connected) rectangle, which is the
already-proven, axiom-clean `continuous_log_lift_param_of_continuous_ne_zero`; the confinement
lemmas themselves are pure 1-D intermediate-value arguments. -/

/-- A continuous real function on `[p, q]` whose cosine is everywhere positive cannot move by `π`
or more between the endpoints (its image stays in a single `cos`-positive open branch). -/
private theorem confined_cos_pos {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, 0 < Real.cos (f u)) :
    |f q - f p| < π := by
  by_contra hcon
  rw [not_lt] at hcon  -- π ≤ |f q - f p|
  set lo := min (f p) (f q) with hlo
  set hi := max (f p) (f q) with hhi
  have hlen : π ≤ hi - lo := by
    rw [hlo, hhi]
    rcases le_total (f p) (f q) with h | h
    · rw [max_eq_right h, min_eq_left h]
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ f q - f p)] at hcon; linarith
    · rw [max_eq_left h, min_eq_right h]
      rw [abs_of_nonpos (by linarith : f q - f p ≤ 0)] at hcon; linarith
  set k : ℤ := ⌈ lo / π - 1/2 ⌉ with hk
  set c : ℝ := (2 * (k:ℝ) + 1) * π / 2 with hc
  have hpi : 0 < π := Real.pi_pos
  have hc_ge_lo : lo ≤ c := by
    have h1 : lo / π - 1/2 ≤ (k:ℝ) := Int.le_ceil _
    have : lo / π ≤ (k:ℝ) + 1/2 := by linarith
    have h2 : lo ≤ ((k:ℝ) + 1/2) * π := by
      rw [div_le_iff₀ hpi] at this; linarith
    rw [hc]; nlinarith
  have hc_le_hi : c ≤ hi := by
    have h1 : (k:ℝ) < lo / π - 1/2 + 1 := Int.ceil_lt_add_one _
    have h2 : (k:ℝ) + 1/2 < lo / π + 1 := by linarith
    have h3 : ((k:ℝ) + 1/2) * π < (lo / π + 1) * π :=
      mul_lt_mul_of_pos_right h2 hpi
    have h4 : (lo / π + 1) * π = lo + π := by field_simp
    have hclt : c < lo + π := by rw [hc]; nlinarith [h3, h4]
    linarith [hlen]
  have hcos_c : Real.cos c = 0 := by
    rw [Real.cos_eq_zero_iff]; exact ⟨k, by rw [hc]⟩
  have hc_mem : c ∈ Set.uIcc (f p) (f q) := by
    rw [Set.mem_uIcc]
    rcases le_total (f p) (f q) with h | h
    · left; refine ⟨?_, ?_⟩
      · have : lo = f p := min_eq_left h; rw [← this]; exact hc_ge_lo
      · have : hi = f q := max_eq_right h; rw [← this]; exact hc_le_hi
    · right; refine ⟨?_, ?_⟩
      · have : lo = f q := min_eq_right h; rw [← this]; exact hc_ge_lo
      · have : hi = f p := max_eq_left h; rw [← this]; exact hc_le_hi
  have huIcc : Set.uIcc p q = Set.Icc p q := Set.uIcc_of_le hpq
  have hf' : ContinuousOn f (Set.uIcc p q) := by rw [huIcc]; exact hf
  obtain ⟨u, hu_mem, hu_eq⟩ := intermediate_value_uIcc hf' hc_mem
  rw [huIcc] at hu_mem
  have : 0 < Real.cos c := hu_eq ▸ hcos u hu_mem
  rw [hcos_c] at this
  exact lt_irrefl 0 this

/-- `sin > 0` confinement (bottom edge): obtained from `confined_cos_pos` by a `π/2` phase shift. -/
private theorem confined_sin_pos {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, 0 < Real.sin (f u)) :
    |f q - f p| < π := by
  have key := confined_cos_pos hpq (f := fun u => f u - π/2)
    ((hf.sub continuousOn_const)) ?_
  · have : (f q - π/2) - (f p - π/2) = f q - f p := by ring
    rwa [this] at key
  · intro u hu
    have : Real.cos (f u - π/2) = Real.sin (f u) := by
      rw [show f u - π/2 = -(π/2 - f u) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]
    rw [this]; exact hsin u hu

/-- `sin < 0` confinement (top edge). -/
private theorem confined_sin_neg {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, Real.sin (f u) < 0) :
    |f q - f p| < π := by
  have key := confined_cos_pos hpq (f := fun u => f u + π/2)
    ((hf.add continuousOn_const)) ?_
  · have : (f q + π/2) - (f p + π/2) = f q - f p := by ring
    rwa [this] at key
  · intro u hu
    have : Real.cos (f u + π/2) = -Real.sin (f u) := Real.cos_add_pi_div_two (f u)
    rw [this]; linarith [hsin u hu]

/-- `cos < 0` confinement (left edge). -/
private theorem confined_cos_neg {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, Real.cos (f u) < 0) :
    |f q - f p| < π := by
  have key := confined_cos_pos hpq (f := fun u => f u + π)
    ((hf.add continuousOn_const)) ?_
  · have : (f q + π) - (f p + π) = f q - f p := by ring
    rwa [this] at key
  · intro u hu
    have : Real.cos (f u + π) = -Real.cos (f u) := Real.cos_add_pi (f u)
    rw [this]; linarith [hcos u hu]

/-- Branch characterization of `cos x > 0`: `x` lies in a unique open interval
`(2πk - π/2, 2πk + π/2)`. -/
private theorem cos_pos_branch {x : ℝ} (hx : 0 < Real.cos x) :
    ∃ k : ℤ, x ∈ Set.Ioo (2 * π * k - π/2) (2 * π * k + π/2) := by
  have hpi : 0 < π := Real.pi_pos
  set n : ℤ := ⌊ x/π + 1/2 ⌋ with hn
  have hfloor_le : (n:ℝ) ≤ x/π + 1/2 := Int.floor_le _
  have hlt_floor : x/π + 1/2 < n + 1 := Int.lt_floor_add_one _
  have hdiv : x / π * π = x := div_mul_cancel₀ x (ne_of_gt hpi)
  have hxlo : (n:ℝ) * π - π/2 ≤ x := by
    have := mul_le_mul_of_nonneg_right hfloor_le (le_of_lt hpi)
    rw [add_mul, hdiv] at this; nlinarith [this]
  have hxhi : x < (n:ℝ) * π + π/2 := by
    have := mul_lt_mul_of_pos_right hlt_floor hpi
    rw [add_mul, hdiv] at this; nlinarith [this]
  have hcosfac : Real.cos x = (-1)^n * Real.cos (x - n * π) := by
    have : x = (x - n*π) + n*π := by ring
    rw [this, Real.cos_add_int_mul_pi]; ring_nf
  have hxlo' : (n:ℝ) * π - π/2 < x := by
    rcases lt_or_eq_of_le hxlo with h | h
    · exact h
    · exfalso
      have hcosx0 : Real.cos x = 0 := by
        rw [← h, Real.cos_eq_zero_iff]; exact ⟨n - 1, by push_cast; ring⟩
      rw [hcosx0] at hx; exact lt_irrefl 0 hx
  have hcos_t : 0 < Real.cos (x - n*π) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · nlinarith [hxlo']
    · nlinarith [hxhi]
  have hsign : (0:ℝ) < (-1:ℝ)^n := by
    rcases lt_trichotomy ((-1:ℝ)^n) 0 with h | h | h
    · exfalso; nlinarith [hcosfac, hx, hcos_t, mul_neg_of_neg_of_pos h hcos_t]
    · exfalso; rw [hcosfac, h, zero_mul] at hx; exact lt_irrefl 0 hx
    · exact h
  have hneven : Even n := by
    rcases Int.even_or_odd n with he | ho
    · exact he
    · exfalso; rw [ho.neg_one_zpow] at hsign; norm_num at hsign
  obtain ⟨k, hk⟩ := hneven
  have hnk : (n:ℝ) = 2 * k := by rw [hk]; push_cast; ring
  refine ⟨k, ?_, ?_⟩
  · rw [hnk] at hxlo'; nlinarith [hxlo']
  · rw [hnk] at hxhi; nlinarith [hxhi]

/-- A continuous `f` on `[p, q]` with `cos∘f > 0` everywhere lies in a single open
`cos`-positive branch `(2πk - π/2, 2πk + π/2)`. -/
private theorem confined_cos_pos_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, 0 < Real.cos (f u)) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k - π/2) (2 * π * k + π/2) := by
  have hpi : 0 < π := Real.pi_pos
  have hp_mem : p ∈ Set.Icc p q := Set.left_mem_Icc.mpr hpq
  obtain ⟨k, hk⟩ := cos_pos_branch (hcos p hp_mem)
  refine ⟨k, fun u hu => ?_⟩
  obtain ⟨k', hk'⟩ := cos_pos_branch (hcos u hu)
  have hpu : p ≤ u := hu.1
  have hsub : Set.Icc p u ⊆ Set.Icc p q := Set.Icc_subset_Icc le_rfl hu.2
  have hbnd : |f u - f p| < π :=
    confined_cos_pos hpu (hf.mono hsub) (fun w hw => hcos w (hsub hw))
  rw [abs_lt] at hbnd
  have hkeq : k' = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk'le : (k':ℝ) ≤ (k:ℝ) - 1 := by
        have : k' ≤ k - 1 := by omega
        exact_mod_cast this
      have h1 : f u < 2 * π * k' + π/2 := hk'.2
      have h2 : 2 * π * k - π/2 < f p := hk.1
      nlinarith [hbnd.1, h1, h2, hk'le, hpi]
    · have hkle : (k:ℝ) ≤ (k':ℝ) - 1 := by
        have : k ≤ k' - 1 := by omega
        exact_mod_cast this
      have h1 : 2 * π * k' - π/2 < f u := hk'.1
      have h2 : f p < 2 * π * k + π/2 := hk.2
      nlinarith [hbnd.2, h1, h2, hkle, hpi]
  rw [← hkeq]; exact hk'

/-- Branch confinement `sin > 0`: branch `(2πk, 2πk + π)`. -/
private theorem confined_sin_pos_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, 0 < Real.sin (f u)) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k) (2 * π * k + π) := by
  obtain ⟨k, hk⟩ := confined_cos_pos_branch hpq (f := fun u => f u - π/2)
    (hf.sub continuousOn_const)
    (fun u hu => by
      have : Real.cos (f u - π/2) = Real.sin (f u) := by
        rw [show f u - π/2 = -(π/2 - f u) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]
      rw [this]; exact hsin u hu)
  refine ⟨k, fun u hu => ?_⟩
  have := hk u hu
  rw [Set.mem_Ioo] at this ⊢
  constructor <;> [nlinarith [this.1]; nlinarith [this.2]]

/-- Branch confinement `sin < 0`: branch `(2πk - π, 2πk)`. -/
private theorem confined_sin_neg_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hsin : ∀ u ∈ Set.Icc p q, Real.sin (f u) < 0) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k - π) (2 * π * k) := by
  obtain ⟨k, hk⟩ := confined_cos_pos_branch hpq (f := fun u => f u + π/2)
    (hf.add continuousOn_const)
    (fun u hu => by
      have : Real.cos (f u + π/2) = -Real.sin (f u) := Real.cos_add_pi_div_two (f u)
      rw [this]; linarith [hsin u hu])
  refine ⟨k, fun u hu => ?_⟩
  have := hk u hu
  rw [Set.mem_Ioo] at this ⊢
  constructor <;> [nlinarith [this.1]; nlinarith [this.2]]

/-- Branch confinement `cos < 0`: branch `(2πk + π/2, 2πk + 3π/2)`. -/
private theorem confined_cos_neg_branch {p q : ℝ} (hpq : p ≤ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc p q))
    (hcos : ∀ u ∈ Set.Icc p q, Real.cos (f u) < 0) :
    ∃ k : ℤ, ∀ u ∈ Set.Icc p q, f u ∈ Set.Ioo (2 * π * k + π/2) (2 * π * k + 3*π/2) := by
  obtain ⟨k, hk⟩ := confined_cos_pos_branch hpq (f := fun u => f u - π)
    (hf.sub continuousOn_const)
    (fun u hu => by
      have : Real.cos (f u - π) = -Real.cos (f u) := by
        rw [show f u - π = -(π - f u) by ring, Real.cos_neg, Real.cos_pi_sub]
      rw [this]; linarith [hcos u hu])
  refine ⟨k, fun u hu => ?_⟩
  have := hk u hu
  rw [Set.mem_Ioo] at this ⊢
  constructor <;> [nlinarith [this.1]; nlinarith [this.2]]

/-- **Square-crossing winding contradiction.** A single-valued continuous argument `θ` on the
rectangle `[a,b] × [s,t]` (`a ≤ b`, `s ≤ t`) whose `sin/cos` are sign-constrained on the four
edges — `sin (θ · s) > 0` on the bottom, `cos (θ b ·) > 0` on the right, `sin (θ · t) < 0` on the
top, `cos (θ a ·) < 0` on the left — is impossible: the four half-plane confinements force a winding
of `2π`, contradicting single-valuedness. (No Brouwer; pure 1-D intermediate-value argument.) -/
private theorem square_crossing_contradiction {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t)
    (θ : ℝ → ℝ → ℝ)
    (hbot : ContinuousOn (fun x => θ x s) (Set.Icc a b))
    (hrgt : ContinuousOn (fun y => θ b y) (Set.Icc s t))
    (htop : ContinuousOn (fun x => θ x t) (Set.Icc a b))
    (hlft : ContinuousOn (fun y => θ a y) (Set.Icc s t))
    (Hbot : ∀ x ∈ Set.Icc a b, 0 < Real.sin (θ x s))
    (Hrgt : ∀ y ∈ Set.Icc s t, 0 < Real.cos (θ b y))
    (Htop : ∀ x ∈ Set.Icc a b, Real.sin (θ x t) < 0)
    (Hlft : ∀ y ∈ Set.Icc s t, Real.cos (θ a y) < 0) :
    False := by
  have hpi : 0 < π := Real.pi_pos
  set A := θ a s with hA
  set B := θ b s with hB
  set C := θ b t with hC
  set D := θ a t with hD
  have ha_mem_ab : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb_mem_ab : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hs_mem_st : s ∈ Set.Icc s t := Set.left_mem_Icc.mpr hst
  have ht_mem_st : t ∈ Set.Icc s t := Set.right_mem_Icc.mpr hst
  obtain ⟨kb, hkb⟩ := confined_sin_pos_branch hab hbot Hbot
  obtain ⟨kr, hkr⟩ := confined_cos_pos_branch hst hrgt Hrgt
  obtain ⟨kt, hkt⟩ := confined_sin_neg_branch hab htop Htop
  obtain ⟨kl, hkl⟩ := confined_cos_neg_branch hst hlft Hlft
  have hA_bot : A ∈ Set.Ioo (2*π*kb) (2*π*kb + π) := hkb a ha_mem_ab
  have hA_lft : A ∈ Set.Ioo (2*π*kl + π/2) (2*π*kl + 3*π/2) := hkl s hs_mem_st
  have hB_bot : B ∈ Set.Ioo (2*π*kb) (2*π*kb + π) := hkb b hb_mem_ab
  have hB_rgt : B ∈ Set.Ioo (2*π*kr - π/2) (2*π*kr + π/2) := hkr s hs_mem_st
  have hC_rgt : C ∈ Set.Ioo (2*π*kr - π/2) (2*π*kr + π/2) := hkr t ht_mem_st
  have hC_top : C ∈ Set.Ioo (2*π*kt - π) (2*π*kt) := hkt b hb_mem_ab
  have hD_top : D ∈ Set.Ioo (2*π*kt - π) (2*π*kt) := hkt a ha_mem_ab
  have hD_lft : D ∈ Set.Ioo (2*π*kl + π/2) (2*π*kl + 3*π/2) := hkl t ht_mem_st
  rw [Set.mem_Ioo] at hA_bot hA_lft hB_bot hB_rgt hC_rgt hC_top hD_top hD_lft
  have int_le : ∀ i j : ℤ, (i:ℝ) < (j:ℝ) + 1 → i ≤ j := by
    intro i j h
    have : i < j + 1 := by exact_mod_cast h
    omega
  have e_kb_le_kr : kb ≤ kr := by
    apply int_le; nlinarith [hB_bot.1, hB_rgt.2, hpi]
  have e_kr_le_kb : kr ≤ kb := by
    apply int_le; nlinarith [hB_rgt.1, hB_bot.2, hpi]
  have hkr' : (kr:ℝ) = (kb:ℝ) := by
    have : kr = kb := le_antisymm e_kr_le_kb e_kb_le_kr; exact_mod_cast this
  have e_kb_le_kt : kb ≤ kt := by
    apply int_le; nlinarith [hC_rgt.1, hC_top.2, hpi, hkr']
  have e_kt_le_kb : kt ≤ kb := by
    apply int_le; nlinarith [hC_top.1, hC_rgt.2, hpi, hkr']
  have hkt' : (kt:ℝ) = (kb:ℝ) := by
    have : kt = kb := le_antisymm e_kt_le_kb e_kb_le_kt; exact_mod_cast this
  have e_kl_le : kl ≤ kb - 1 := by
    apply int_le
    have hlt : (kl:ℝ) < kb := by nlinarith [hD_lft.1, hD_top.2, hpi, hkt']
    push_cast; linarith
  have e_kl_ge : kb - 1 ≤ kl := by
    apply int_le
    have hlt : (kb:ℝ) < kl + 2 := by nlinarith [hD_top.1, hD_lft.2, hpi, hkt']
    push_cast; linarith
  have hkl' : (kl:ℝ) = (kb:ℝ) - 1 := by
    have : kl = kb - 1 := le_antisymm e_kl_le e_kl_ge; rw [this]; push_cast; ring
  have hAlo : 2*π*(kb:ℝ) < A := hA_bot.1
  have hAhi : A < 2*π*(kl:ℝ) + 3*π/2 := hA_lft.2
  nlinarith [hAlo, hAhi, hpi, hkl']

/-- **The boundary-bumping crux (the genuinely two-dimensional plane-separation core).**

With `Rect = [a,b]×[s,t]`, continuous `v` with `v = 0` on the left edge `{re = a}` and `v = 1` on
the right edge `{re = b}`, and `c ∈ (0,1)`, the level set `K = Rect ∩ {v = c}` **cannot** have its
bottom points `{im = s} ∩ K` topologically separated from its top points `{im = t} ∩ K`: there is
*always* a preconnected subset of `K` meeting both the bottom and the top edge. Equivalently
(contrapositive, the form proven here): if **no** preconnected `S ⊆ K` meets both the bottom edge
`{im = s}` and the top edge `{im = t}`, that is a contradiction.

## History — a previously FALSE statement, now corrected

The earlier formalization of this crux took the much weaker hypotheses *"`K` splits as disjoint
compacta `K₁ ⊔ K₂` with `K₁` meeting the bottom edge and `K₂` meeting the top edge"* and concluded
`False`. **That statement is FALSE**: take `Rect = [0,3]×[0,1]` and `v` depending only on `re` with
`v(0) = 0`, `v` rising to `c = ½` at `re = 1`, bulging `> ½` on `(1,2)`, returning to `½` at
`re = 2`, then rising to `v(3) = 1`. Its level set `K = ({re = 1} ∪ {re = 2}) × [0,1]` is **two
disjoint full-height segments**; `K₁ = {re = 1} × [0,1]`, `K₂ = {re = 2} × [0,1]` are disjoint
compacta with `K₁ ∋ (1,0)` (bottom) and `K₂ ∋ (2,1)` (top), satisfying *every* hypothesis of the
old statement, yet the conclusion `False` is unwarranted — both segments individually join bottom to
top, so there is no contradiction. The old weak hypotheses dropped the load-bearing separation
structure (*no preconnected subset of `K` joins bottom to top*) and were satisfiable, making the
lemma a latent false `sorry`. It is restated here with the correct, **true** hypothesis `hsep`.

## Proof (Brouwer-free, axiom-clean)

This is the classical Steinhaus-chessboard / Šura–Bura plane-separation core. It is proven here
**without** any Brouwer / Jordan / topological-degree input, by the *gap-threading winding* route:

1. **Šura–Bura split** (`rectLevel_split_of_no_continuum`): the contradiction hypothesis `hsep`
   gives a clopen-in-`K` decomposition `K = K₁ ⊔ K₂` with `Bot ⊆ K₁`, `Top ⊆ K₂`.
2. **Urysohn separator** (`exists_continuous_zero_one_of_isClosed`, `ℂ` normal): the disjoint
   closed sets `P = K₁ ∪ (full bottom edge)` and `Q = K₂ ∪ (full top edge)` (disjointness uses the
   split inclusions and `s < t`) carry a continuous `η : ℂ → ℝ` with `η = +1` on `P`, `η = −1`
   on `Q`.
3. **Nonvanishing field**: `φ z = (v z − c) + i·η z` is nonvanishing on `Rect` (if `v z = c` then
   `z ∈ K = K₁ ∪ K₂`, where `η = ±1 ≠ 0`), with the four-edge sign pattern `Re φ < 0` (left,
   `v = 0`), `Re φ > 0` (right, `v = 1`), `Im φ > 0` (bottom, `η = +1`), `Im φ < 0` (top, `η = −1`).
4. **Continuous logarithm**: since `Rect` is contractible, `φ` admits a global continuous log
   (`continuous_log_lift_param_of_continuous_ne_zero`, the repository's axiom-clean
   covering-space lift), so `θ := Im(L)` is a single-valued continuous argument of `φ`.
5. **Winding contradiction** (`square_crossing_contradiction`): the four-edge sign pattern confines
   `θ` to consecutive half-plane branches whose corner-matching forces a net winding of `2π`,
   contradicting that `θ` is single-valued. Each confinement is a pure 1-D intermediate-value
   argument (`confined_{cos,sin}_{pos,neg}_branch`).

The only non-elementary ingredient is the continuous logarithm of step 4, which is strictly weaker
than Brouwer (it is the *absence* of a degree obstruction on the contractible square) and is already
proven axiom-clean in the repository. -/
private theorem rectLevel_no_split {a b s t : ℝ} (hab : a ≤ b) (hst : s ≤ t)
    {v : ℂ → ℝ} (hvcont : Continuous v)
    (hv0 : ∀ z : ℂ, z.re = a → s ≤ z.im → z.im ≤ t → v z = 0)
    (hv1 : ∀ z : ℂ, z.re = b → s ≤ z.im → z.im ≤ t → v z = 1)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hsep : ∀ S : Set ℂ, IsPreconnected S → S ⊆ rectLevelRect a b s t ∩ v ⁻¹' {c} →
      (∃ p ∈ S, p.im = s) → (∃ q ∈ S, q.im = t) → False) :
    False := by
  have hpi : 0 < π := Real.pi_pos
  set R : Set ℂ := rectLevelRect a b s t with hR
  set K : Set ℂ := R ∩ v ⁻¹' {c} with hKdef
  -- The full bottom/top edges of the rectangle (closed segments at heights `s`, `t`).
  set botEdge : Set ℂ := {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ z.im = s} with hbotEdge
  set topEdge : Set ℂ := {z : ℂ | (a ≤ z.re ∧ z.re ≤ b) ∧ z.im = t} with htopEdge
  -- Membership helpers in `mk` coordinates.
  have hmk_re : ∀ x y : ℝ, (Complex.mk x y).re = x := fun _ _ => rfl
  have hmk_im : ∀ x y : ℝ, (Complex.mk x y).im = y := fun _ _ => rfl
  -- `v` restricted to a horizontal segment.
  -- Degenerate case `s = t`: the rectangle is a single segment; 1-D IVT finds a level point and
  -- a one-point preconnected `S` violates `hsep`.
  rcases eq_or_lt_of_le hst with hst_eq | hst_lt
  · obtain ⟨x, hx_mem, hvx⟩ := rectLevel_exists_mem_level_on_edge hab hvcont
      (hv0 (Complex.mk a s) rfl (le_refl s) hst) (hv1 (Complex.mk b s) rfl (le_refl s) hst) hc
    refine hsep {Complex.mk x s} isPreconnected_singleton ?_ ⟨_, rfl, rfl⟩
      ⟨_, rfl, hst_eq⟩
    rintro z hz; rw [Set.mem_singleton_iff] at hz; subst hz
    refine ⟨⟨⟨hx_mem.1, hx_mem.2⟩, le_refl s, hst⟩, ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hvx
  -- Main case `s < t`. Set up the bottom/top level point sets.
  set Bot : Set ℂ := {z ∈ K | z.im = s} with hBotdef
  set Top : Set ℂ := {z ∈ K | z.im = t} with hTopdef
  have hRcompact : IsCompact R := rectLevel_isCompact_rect a b s t
  have hvc_closed : IsClosed (v ⁻¹' {c}) := (isClosed_singleton).preimage hvcont
  have hKcompact : IsCompact K := hRcompact.inter_right hvc_closed
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hBot_sub : Bot ⊆ K := fun z hz => hz.1
  have hTop_sub : Top ⊆ K := fun z hz => hz.1
  have hBot_closed : IsClosed Bot := by
    have : Bot = K ∩ {z : ℂ | z.im = s} :=
      Set.ext fun z => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [this]; exact hKclosed.inter (isClosed_eq Complex.continuous_im continuous_const)
  have hTop_closed : IsClosed Top := by
    have : Top = K ∩ {z : ℂ | z.im = t} :=
      Set.ext fun z => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [this]; exact hKclosed.inter (isClosed_eq Complex.continuous_im continuous_const)
  -- Šura–Bura split: `K = K₁ ⊔ K₂` with `Bot ⊆ K₁`, `Top ⊆ K₂`.
  have hsep_split : ∀ S : Set ℂ, IsPreconnected S → S ⊆ K →
      (S ∩ Bot).Nonempty → (S ∩ Top).Nonempty → False := by
    intro S hScon hSK hSB hST
    refine hsep S hScon hSK ?_ ?_
    · obtain ⟨p, hpS, hpBot⟩ := hSB; exact ⟨p, hpS, hpBot.2⟩
    · obtain ⟨q, hqS, hqTop⟩ := hST; exact ⟨q, hqS, hqTop.2⟩
  obtain ⟨K₁, K₂, hK₁cpt, hK₂cpt, hK₁₂disj, hK₁₂union, hBotK₁, hTopK₂⟩ :=
    rectLevel_split_of_no_continuum hKcompact hBot_sub hTop_sub hBot_closed hTop_closed hsep_split
  have hK₁closed : IsClosed K₁ := hK₁cpt.isClosed
  have hK₂closed : IsClosed K₂ := hK₂cpt.isClosed
  -- Edge closedness.
  have hbotEdge_closed : IsClosed botEdge := by
    have : botEdge = {z : ℂ | a ≤ z.re} ∩ {z : ℂ | z.re ≤ b} ∩ {z : ℂ | z.im = s} := by
      ext z; simp only [hbotEdge, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  have htopEdge_closed : IsClosed topEdge := by
    have : topEdge = {z : ℂ | a ≤ z.re} ∩ {z : ℂ | z.re ≤ b} ∩ {z : ℂ | z.im = t} := by
      ext z; simp only [htopEdge, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  -- The two Urysohn sets `P = K₁ ∪ botEdge`, `Q = K₂ ∪ topEdge`.
  set P : Set ℂ := K₁ ∪ botEdge with hPdef
  set Q : Set ℂ := K₂ ∪ topEdge with hQdef
  have hP_closed : IsClosed P := hK₁closed.union hbotEdge_closed
  have hQ_closed : IsClosed Q := hK₂closed.union htopEdge_closed
  -- `K ⊆ K₁ ∪ K₂` (from the union equality) and the edge ⊆ K facts via level membership.
  have hbotEdge_K : ∀ z ∈ botEdge, z ∈ K → z ∈ K₁ := by
    intro z hz hzK; exact hBotK₁ ⟨hzK, hz.2⟩
  have htopEdge_K : ∀ z ∈ topEdge, z ∈ K → z ∈ K₂ := by
    intro z hz hzK; exact hTopK₂ ⟨hzK, hz.2⟩
  -- `P` and `Q` are disjoint.
  have hPQ_disj : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro z hzP hzQ
    rcases hzP with hzK₁ | hzbot <;> rcases hzQ with hzK₂ | hztop
    · exact (Set.disjoint_left.mp hK₁₂disj hzK₁) hzK₂
    · -- z ∈ K₁ and z ∈ topEdge: z.im = t and z ∈ K₁ ⊆ K, so z ∈ Top ⊆ K₂; contradiction.
      have hzK : z ∈ K := hK₁₂union ▸ Set.mem_union_left _ hzK₁
      exact (Set.disjoint_left.mp hK₁₂disj hzK₁) (htopEdge_K z hztop hzK)
    · -- z ∈ botEdge and z ∈ K₂: z.im = s and z ∈ K₂ ⊆ K, so z ∈ Bot ⊆ K₁; contradiction.
      have hzK : z ∈ K := hK₁₂union ▸ Set.mem_union_right _ hzK₂
      exact (Set.disjoint_left.mp hK₁₂disj (hbotEdge_K z hzbot hzK)) hzK₂
    · -- z ∈ botEdge ∩ topEdge: z.im = s and z.im = t with s < t.
      rw [hbotEdge, Set.mem_setOf_eq] at hzbot
      rw [htopEdge, Set.mem_setOf_eq] at hztop
      exact absurd (hzbot.2.symm.trans hztop.2) (ne_of_lt hst_lt)
  -- Urysohn function: `g = 0` on `P`, `g = 1` on `Q`, `g ∈ [0,1]`.
  obtain ⟨g, hgP, hgQ, hg01⟩ := exists_continuous_zero_one_of_isClosed hP_closed hQ_closed hPQ_disj
  -- `η = 1 - 2 g`: `η = 1` on `P`, `η = -1` on `Q`.
  set η : ℂ → ℝ := fun z => 1 - 2 * g z with hηdef
  have hη_cont : Continuous η := by fun_prop
  have hηP : ∀ z ∈ P, η z = 1 := by
    intro z hz
    have : g z = 0 := by have := hgP hz; simpa using this
    simp only [hηdef]; rw [this]; ring
  have hηQ : ∀ z ∈ Q, η z = -1 := by
    intro z hz
    have : g z = 1 := by have := hgQ hz; simpa using this
    simp only [hηdef]; rw [this]; ring
  -- The nonvanishing map `φ z = (v z - c) + i η z`.
  set φ : ℂ → ℂ := fun z => Complex.mk (v z - c) (η z) with hφdef
  have hφ_cont : Continuous φ := by
    have : φ = fun z => ((v z - c : ℝ) : ℂ) + (η z : ℝ) * Complex.I := by
      funext z; apply Complex.ext <;> simp [hφdef]
    rw [this]; fun_prop
  -- `φ z ≠ 0` for `z ∈ R`.
  have hφ_ne : ∀ z ∈ R, φ z ≠ 0 := by
    intro z hzR hφ0
    have hre0 : (φ z).re = 0 := by rw [hφ0]; rfl
    have him0 : (φ z).im = 0 := by rw [hφ0]; rfl
    have hvz : v z = c := by
      have : v z - c = 0 := by simpa [hφdef, hmk_re] using hre0
      linarith
    have hzK : z ∈ K := ⟨hzR, by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hvz⟩
    have hηz0 : η z = 0 := by simpa [hφdef, hmk_im] using him0
    rcases (hK₁₂union ▸ hzK : z ∈ K₁ ∪ K₂) with hzK₁ | hzK₂
    · have : η z = 1 := hηP z (Set.mem_union_left _ hzK₁)
      rw [hηz0] at this; norm_num at this
    · have : η z = -1 := hηQ z (Set.mem_union_left _ hzK₂)
      rw [hηz0] at this; norm_num at this
  -- The parametrized nonvanishing map and its continuous logarithm.
  set u : ℝ → ℝ → ℂ := fun x y => φ (Complex.mk x y) with hudef
  have hmk2_cont : Continuous (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
    have : (fun p : ℝ × ℝ => Complex.mk p.1 p.2)
        = fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) + (p.2 : ℝ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    rw [this]; fun_prop
  have hu_cont : ContinuousOn (Function.uncurry u) (Set.Icc a b ×ˢ Set.Icc s t) := by
    have : Function.uncurry u = fun p : ℝ × ℝ => φ (Complex.mk p.1 p.2) := by
      funext p; simp [Function.uncurry, hudef]
    rw [this]; exact (hφ_cont.comp hmk2_cont).continuousOn
  -- A point of the box lies in `R`.
  have hmk_mem_R : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc s t, Complex.mk x y ∈ R := by
    intro x hx y hy
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hmk_re]; exact hx.1
    · rw [hmk_re]; exact hx.2
    · rw [hmk_im]; exact hy.1
    · rw [hmk_im]; exact hy.2
  have hu_ne : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc s t, u x y ≠ 0 := by
    intro x hx y hy; exact hφ_ne _ (hmk_mem_R x hx y hy)
  obtain ⟨L, hL_cont, hL_exp⟩ :=
    continuous_log_lift_param_of_continuous_ne_zero hab hst u hu_cont hu_ne
  -- The single-valued argument `θ x y = (L x y).im`.
  set θ : ℝ → ℝ → ℝ := fun x y => (L x y).im with hθdef
  -- Sign of `Re/Im (φ (mk x y)) = exp((L x y).re) · cos/sin (θ x y)`.
  have hsign : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc s t,
      (v (Complex.mk x y) - c = Real.exp ((L x y).re) * Real.cos (θ x y)) ∧
      (η (Complex.mk x y) = Real.exp ((L x y).re) * Real.sin (θ x y)) := by
    intro x hx y hy
    have hexp : Complex.exp (L x y) = u x y := hL_exp x hx y hy
    have hre : (u x y).re = Real.exp ((L x y).re) * Real.cos (θ x y) := by
      rw [← hexp, Complex.exp_re]
    have him : (u x y).im = Real.exp ((L x y).re) * Real.sin (θ x y) := by
      rw [← hexp, Complex.exp_im]
    refine ⟨?_, ?_⟩
    · have : (u x y).re = v (Complex.mk x y) - c := by simp [hudef, hφdef, hmk_re]
      rw [this] at hre; exact hre
    · have : (u x y).im = η (Complex.mk x y) := by simp [hudef, hφdef, hmk_im]
      rw [this] at him; exact him
  -- Continuity of `θ` along the four edges.
  have hLuncurry : Continuous (Function.uncurry L) := hL_cont
  have hθ_cont_uncurry : Continuous (Function.uncurry θ) := by
    have : Function.uncurry θ = fun p : ℝ × ℝ => (Function.uncurry L p).im := by
      funext p; simp [hθdef, Function.uncurry]
    rw [this]; exact Complex.continuous_im.comp hLuncurry
  have hbot_cont : ContinuousOn (fun x => θ x s) (Set.Icc a b) := by
    have : (fun x => θ x s) = (Function.uncurry θ) ∘ (fun x : ℝ => (x, s)) := by
      funext x; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  have hrgt_cont : ContinuousOn (fun y => θ b y) (Set.Icc s t) := by
    have : (fun y => θ b y) = (Function.uncurry θ) ∘ (fun y : ℝ => (b, y)) := by
      funext y; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  have htop_cont : ContinuousOn (fun x => θ x t) (Set.Icc a b) := by
    have : (fun x => θ x t) = (Function.uncurry θ) ∘ (fun x : ℝ => (x, t)) := by
      funext x; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  have hlft_cont : ContinuousOn (fun y => θ a y) (Set.Icc s t) := by
    have : (fun y => θ a y) = (Function.uncurry θ) ∘ (fun y : ℝ => (a, y)) := by
      funext y; simp [Function.uncurry]
    rw [this]; exact (hθ_cont_uncurry.comp (by fun_prop)).continuousOn
  -- The four edge sign conditions.
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hs_mem : s ∈ Set.Icc s t := Set.left_mem_Icc.mpr hst
  have ht_mem : t ∈ Set.Icc s t := Set.right_mem_Icc.mpr hst
  -- Bottom edge: `η = 1 > 0` ⟹ `exp · sin > 0` ⟹ `sin > 0`.
  have Hbot : ∀ x ∈ Set.Icc a b, 0 < Real.sin (θ x s) := by
    intro x hx
    have hηeq : η (Complex.mk x s) = 1 := by
      refine hηP _ (Set.mem_union_right _ ?_)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hmk_re]; exact hx.1
      · rw [hmk_re]; exact hx.2
      · rw [hmk_im]
    have := (hsign x hx s hs_mem).2
    rw [hηeq] at this
    have hexp_pos := Real.exp_pos ((L x s).re)
    nlinarith [this, hexp_pos, Real.exp_pos ((L x s).re)]
  -- Top edge: `η = -1 < 0` ⟹ `sin < 0`.
  have Htop : ∀ x ∈ Set.Icc a b, Real.sin (θ x t) < 0 := by
    intro x hx
    have hηeq : η (Complex.mk x t) = -1 := by
      refine hηQ _ (Set.mem_union_right _ ?_)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hmk_re]; exact hx.1
      · rw [hmk_re]; exact hx.2
      · rw [hmk_im]
    have := (hsign x hx t ht_mem).2
    rw [hηeq] at this
    have hexp_pos := Real.exp_pos ((L x t).re)
    nlinarith [this, hexp_pos]
  -- Right edge: `v = 1` ⟹ `v - c = 1 - c > 0` ⟹ `cos > 0`.
  have Hrgt : ∀ y ∈ Set.Icc s t, 0 < Real.cos (θ b y) := by
    intro y hy
    have hv1' : v (Complex.mk b y) = 1 := by
      refine hv1 _ ?_ ?_ ?_
      · rw [hmk_re]
      · rw [hmk_im]; exact hy.1
      · rw [hmk_im]; exact hy.2
    have hpos : 0 < v (Complex.mk b y) - c := by rw [hv1']; linarith [hc.2]
    have := (hsign b hb_mem y hy).1
    rw [this] at hpos
    have hexp_pos := Real.exp_pos ((L b y).re)
    nlinarith [hpos, hexp_pos]
  -- Left edge: `v = 0` ⟹ `v - c = -c < 0` ⟹ `cos < 0`.
  have Hlft : ∀ y ∈ Set.Icc s t, Real.cos (θ a y) < 0 := by
    intro y hy
    have hv0' : v (Complex.mk a y) = 0 := by
      refine hv0 _ ?_ ?_ ?_
      · rw [hmk_re]
      · rw [hmk_im]; exact hy.1
      · rw [hmk_im]; exact hy.2
    have hneg : v (Complex.mk a y) - c < 0 := by rw [hv0']; linarith [hc.1]
    have := (hsign a ha_mem y hy).1
    rw [this] at hneg
    have hexp_pos := Real.exp_pos ((L a y).re)
    nlinarith [hneg, hexp_pos]
  -- Conclude via the winding contradiction.
  exact square_crossing_contradiction hab hst θ hbot_cont hrgt_cont htop_cont hlft_cont
    Hbot Hrgt Htop Hlft



/-! ### Arc-length Lipschitz reparametrization of a simple rectifiable arc

The decomposition of the rectifiable-continuum theorem `rectifiable_continuum_simple_arc` separates
its two ingredients:

* the **topological core** (Eilenberg–Harrold / Hahn–Mazurkiewicz, Mathlib-absent): a rectifiable
  continuum contains a *simple* (injective) **finite-variation** arc joining any two points —
  isolated as the residual `simpleRectifiableArc_of_compact_connected_finite_hausdorff`; and
* the **arc-length reparametrization** (proven here): a simple finite-variation arc can be
  reparametrized to a globally Lipschitz simple arc on `[0,1]` — the genuine analytic content for
  which Mathlib does have machinery (`variationOnFromTo`, `Mathlib.Analysis.ConstantSpeed`).

The reparametrization uses the cumulative variation `S = variationOnFromTo γ [0,1] 0` as a
*continuous strictly monotone* bijection `[0,1] → [0, L]` (`L =` total length), reparametrizing by
its inverse so the new curve has constant speed `L`, hence is `L`-Lipschitz. -/

/-- Continuity of the cumulative variation `variationOnFromTo γ s a` on `s`, from continuity of the
curve `γ` (and bounded variation on `s`). This packages Mathlib's one-sided
`tendsto_eVariationOn_Icc_zero_left/right` into honest `ContinuousOn`. -/
theorem continuousOn_variationOnFromTo {γ : ℝ → ℂ} {s : Set ℝ}
    (hγ : Continuous γ) (hbv : BoundedVariationOn γ s) {a : ℝ} (ha : a ∈ s) :
    ContinuousOn (variationOnFromTo γ s a) s := by
  have hloc : LocallyBoundedVariationOn γ s := hbv.locallyBoundedVariationOn
  intro x hx
  have key : Filter.Tendsto (fun y => variationOnFromTo γ s x y) (𝓝[s] x) (𝓝 (0 : ℝ)) := by
    have hcL : ContinuousWithinAt γ (s ∩ Iic x) x := (hγ.continuousWithinAt).mono inter_subset_left
    have hcR : ContinuousWithinAt γ (s ∩ Ici x) x := (hγ.continuousWithinAt).mono inter_subset_left
    have hL := (BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left hbv hcL)
    have hR := (BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right hbv x hcR)
    have hLr : Filter.Tendsto (fun y => (eVariationOn γ (s ∩ Icc y x)).toReal) (𝓝[s] x) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hL
      simpa using this
    have hRr : Filter.Tendsto (fun y => (eVariationOn γ (s ∩ Icc x y)).toReal) (𝓝[s] x) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hR
      simpa using this
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hLr.eventually (Metric.ball_mem_nhds 0 hε),
      hRr.eventually (Metric.ball_mem_nhds 0 hε)] with y hyL hyR
    rw [Real.dist_eq] at hyL hyR ⊢
    simp only [sub_zero] at hyL hyR ⊢
    rcases le_total y x with hyx | hxy
    · rw [variationOnFromTo.eq_of_ge γ s hyx, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg ENNReal.toReal_nonneg] at hyL
      exact hyL
    · rw [variationOnFromTo.eq_of_le γ s hxy, abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg ENNReal.toReal_nonneg] at hyR
      exact hyR
  have hcongr : (fun y => variationOnFromTo γ s a y)
      =ᶠ[𝓝[s] x] (fun y => variationOnFromTo γ s a x + variationOnFromTo γ s x y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [variationOnFromTo.add hloc ha hx hy]
  rw [ContinuousWithinAt, Filter.tendsto_congr' hcongr]
  have heq : (𝓝 (variationOnFromTo γ s a x)) = 𝓝 (variationOnFromTo γ s a x + 0) := by rw [add_zero]
  rw [heq]
  exact tendsto_const_nhds.add key

/-- The clamp of a real number into `[0,1]`. Continuous, `1`-Lipschitz, fixes `[0,1]` pointwise,
and always lands in `[0,1]`; used to make the reparametrized arc *globally* Lipschitz. -/
private noncomputable def clamp01 (τ : ℝ) : ℝ := max 0 (min 1 τ)

private theorem clamp01_mem (τ : ℝ) : clamp01 τ ∈ Icc (0 : ℝ) 1 := by
  unfold clamp01
  refine ⟨le_max_left _ _, ?_⟩
  rcases le_total 1 τ with h | h
  · simp [h]
  · rw [min_eq_right h, max_le_iff]; exact ⟨by norm_num, h⟩

private theorem clamp01_eq_self {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : clamp01 τ = τ := by
  unfold clamp01
  obtain ⟨h0, h1⟩ := hτ
  rw [min_eq_right h1, max_eq_right h0]

private theorem lipschitzWith_clamp01 : LipschitzWith 1 clamp01 := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro τ τ'
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  unfold clamp01
  have hmin : |min 1 τ - min 1 τ'| ≤ |τ - τ'| := by
    refine (abs_min_sub_min_le_max 1 τ 1 τ').trans ?_
    simp only [sub_self, abs_zero]
    exact max_le (abs_nonneg _) le_rfl
  refine (abs_max_sub_max_le_max 0 (min 1 τ) 0 (min 1 τ')).trans ?_
  simp only [sub_self, abs_zero]
  exact max_le (abs_nonneg _) hmin

/-- **Arc-length Lipschitz reparametrization** (the proven half of
`rectifiable_continuum_simple_arc`).

Given a continuous curve `γ` that is *injective* on `[0,1]` and of *finite total variation*
`eVariationOn γ [0,1] ≠ ∞`, there is a curve `δ` parametrized on `[0,1]` with the **same
endpoints**,
**globally Lipschitz** (hence continuous), **injective** on `[0,1]`, with trace inside `γ '' [0,1]`.

Reparametrize by cumulative arc length: `S t = variationOnFromTo γ [0,1] 0 t` is continuous
(`continuousOn_variationOnFromTo`) and *strictly* monotone (injectivity ⟹ positive variation over
each nondegenerate subinterval, via `eVariationOn.edist_le`), so it is a homeomorphism
`[0,1] ≃ [0, L]` with `L = (eVariationOn γ [0,1]).toReal > 0`. Composing `γ` with the (scaled,
clamped) inverse gives a constant-speed-`L` curve, which is `L`-Lipschitz by `eVariationOn.edist_le`
applied on subintervals. Clamping makes the Lipschitz bound global. -/
theorem lipschitz_simpleArc_of_finiteVariation {γ : ℝ → ℂ}
    (hγcont : Continuous γ) (hγinj : InjOn γ (Icc (0 : ℝ) 1))
    (hγbv : eVariationOn γ (Icc (0 : ℝ) 1) ≠ ∞) :
    ∃ δ : ℝ → ℂ, δ 0 = γ 0 ∧ δ 1 = γ 1 ∧ Continuous δ ∧
      (∃ K : ℝ≥0, LipschitzOnWith K δ (Set.uIcc 0 1)) ∧
      Set.InjOn δ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, δ τ ∈ γ '' (Icc (0 : ℝ) 1) := by
  set s : Set ℝ := Icc (0 : ℝ) 1 with hs
  have h0s : (0 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have h1s : (1 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have hbv : BoundedVariationOn γ s := hγbv
  have hloc : LocallyBoundedVariationOn γ s := hbv.locallyBoundedVariationOn
  set S : ℝ → ℝ := variationOnFromTo γ s 0 with hSdef
  set L : ℝ := (eVariationOn γ s).toReal with hLdef
  have hS0 : S 0 = 0 := by rw [hSdef]; exact variationOnFromTo.self γ s 0
  have hsIcc : s ∩ Icc (0 : ℝ) 1 = s := by rw [hs]; simp [Set.inter_self]
  have hS1 : S 1 = L := by
    rw [hSdef, hLdef, variationOnFromTo.eq_of_le γ s (by norm_num : (0 : ℝ) ≤ 1), hsIcc]
  have hSmono : MonotoneOn S s := variationOnFromTo.monotoneOn hloc h0s
  have hScont : ContinuousOn S s := continuousOn_variationOnFromTo hγcont hbv h0s
  -- strict mono: `S b < S c` for `b < c` in `s`, using injectivity ⟹ positive variation
  have hSstrict : ∀ b ∈ s, ∀ c ∈ s, b < c → S b < S c := by
    intro b hb c hc hbc
    have hadd : S b + variationOnFromTo γ s b c = S c := by
      rw [hSdef]; exact variationOnFromTo.add hloc h0s hb hc
    have hpos : 0 < variationOnFromTo γ s b c := by
      rw [variationOnFromTo.eq_of_le γ s hbc.le]
      have hbc' : b ∈ s ∩ Icc b c := ⟨hb, le_rfl, hbc.le⟩
      have hcc' : c ∈ s ∩ Icc b c := ⟨hc, hbc.le, le_rfl⟩
      have hne : γ b ≠ γ c := fun h => (hbc.ne) (hγinj hb hc h)
      have hedpos : 0 < edist (γ b) (γ c) := by rw [edist_pos]; exact hne
      have hsub : eVariationOn γ (s ∩ Icc b c) ≠ ∞ :=
        ne_top_of_le_ne_top hbv (eVariationOn.mono γ inter_subset_left)
      have hle : edist (γ b) (γ c) ≤ eVariationOn γ (s ∩ Icc b c) :=
        eVariationOn.edist_le γ hbc' hcc'
      have : (0 : ℝ≥0∞) < eVariationOn γ (s ∩ Icc b c) := lt_of_lt_of_le hedpos hle
      exact ENNReal.toReal_pos (ne_of_gt this) hsub
    linarith [hadd]
  have hLpos : 0 < L := by
    have := hSstrict 0 h0s 1 h1s (by norm_num)
    rw [hS0, hS1] at this; exact this
  have hLnn : 0 ≤ L := hLpos.le
  -- image of `S` is `Icc 0 L`
  have hSimage : S '' s = Icc 0 L := by
    have hcont' : ContinuousOn S (Icc (0 : ℝ) 1) := hScont
    have hmono' : MonotoneOn S (Icc (0 : ℝ) 1) := hSmono
    have himg := ContinuousOn.image_Icc_of_monotoneOn (a := (0 : ℝ)) (b := (1 : ℝ)) (f := S)
      (by norm_num) hcont' hmono'
    rw [hs, himg, hS0, hS1]
  -- the (generalized) inverse of `S` restricted to `s`
  set T : ℝ → ℝ := Function.invFunOn S s with hTdef
  have hTspec : ∀ v ∈ Icc (0 : ℝ) L, T v ∈ s ∧ S (T v) = v := by
    intro v hv
    have hex : ∃ a ∈ s, S a = v := by
      have : v ∈ S '' s := by rw [hSimage]; exact hv
      obtain ⟨a, ha, hav⟩ := this; exact ⟨a, ha, hav⟩
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  set δ : ℝ → ℂ := fun τ => γ (T (L * clamp01 τ)) with hδdef
  have hmulmem : ∀ τ, L * clamp01 τ ∈ Icc (0 : ℝ) L := by
    intro τ
    obtain ⟨hc0, hc1⟩ := clamp01_mem τ
    refine ⟨by positivity, ?_⟩
    nlinarith [hLnn]
  have hTmem : ∀ τ, T (L * clamp01 τ) ∈ s := fun τ => (hTspec _ (hmulmem τ)).1
  have hST : ∀ τ, S (T (L * clamp01 τ)) = L * clamp01 τ := fun τ => (hTspec _ (hmulmem τ)).2
  -- endpoints
  have hT0 : T 0 = 0 := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hLnn⟩
    have hm := (hTspec 0 h0mem).1
    have he := (hTspec 0 h0mem).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hSstrict (T 0) hm 0 h0s h; rw [he, hS0] at this; exact lt_irrefl _ this
    · have := hSstrict 0 h0s (T 0) hm h; rw [he, hS0] at this; exact lt_irrefl _ this
  have hTL : T L = 1 := by
    have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hLnn, le_rfl⟩
    have hm := (hTspec L hLmem).1
    have he := (hTspec L hLmem).2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hSstrict (T L) hm 1 h1s h; rw [he, hS1] at this; exact lt_irrefl _ this
    · have := hSstrict 1 h1s (T L) hm h; rw [he, hS1] at this; exact lt_irrefl _ this
  have hδ0 : δ 0 = γ 0 := by
    rw [hδdef]; simp only
    rw [show clamp01 0 = 0 from clamp01_eq_self (by constructor <;> norm_num), mul_zero, hT0]
  have hδ1 : δ 1 = γ 1 := by
    rw [hδdef]; simp only
    rw [show clamp01 1 = 1 from clamp01_eq_self (by constructor <;> norm_num), mul_one, hTL]
  -- global Lipschitz bound with constant `L`
  have hLip : LipschitzWith L.toNNReal δ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro τ τ'
    set u := T (L * clamp01 τ) with hu
    set u' := T (L * clamp01 τ') with hu'
    have hus : u ∈ s := hTmem τ
    have hu's : u' ∈ s := hTmem τ'
    have hSu : S u = L * clamp01 τ := hST τ
    have hSu' : S u' = L * clamp01 τ' := hST τ'
    have hvar : variationOnFromTo γ s u u' = S u' - S u := by
      rw [hSdef]
      have := variationOnFromTo.add hloc h0s hus hu's
      linarith [this]
    have hdist_le : dist (γ u) (γ u') ≤ |S u' - S u| := by
      rw [dist_edist]
      have hmemuu : u ∈ s ∩ uIcc u u' := ⟨hus, left_mem_uIcc⟩
      have hmemuu' : u' ∈ s ∩ uIcc u u' := ⟨hu's, right_mem_uIcc⟩
      have hle : edist (γ u) (γ u') ≤ eVariationOn γ (s ∩ uIcc u u') :=
        eVariationOn.edist_le γ hmemuu hmemuu'
      have hsubne : eVariationOn γ (s ∩ uIcc u u') ≠ ∞ :=
        ne_top_of_le_ne_top hbv (eVariationOn.mono γ inter_subset_left)
      have hreal : (edist (γ u) (γ u')).toReal ≤ (eVariationOn γ (s ∩ uIcc u u')).toReal :=
        ENNReal.toReal_mono hsubne hle
      have hvareq : (eVariationOn γ (s ∩ uIcc u u')).toReal = |variationOnFromTo γ s u u'| := by
        rcases le_total u u' with h | h
        · rw [variationOnFromTo.eq_of_le γ s h, abs_of_nonneg ENNReal.toReal_nonneg, uIcc_of_le h]
        · rw [variationOnFromTo.eq_of_ge γ s h, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
            uIcc_of_ge h]
      rw [hvareq, hvar] at hreal
      exact hreal
    calc dist (δ τ) (δ τ') = dist (γ u) (γ u') := by rw [hδdef]
      _ ≤ |S u' - S u| := hdist_le
      _ = |L * clamp01 τ' - L * clamp01 τ| := by rw [hSu, hSu']
      _ = L * |clamp01 τ' - clamp01 τ| := by rw [← mul_sub, abs_mul, abs_of_nonneg hLnn]
      _ = L * dist (clamp01 τ') (clamp01 τ) := by rw [Real.dist_eq]
      _ ≤ L * dist τ' τ := by
            apply mul_le_mul_of_nonneg_left _ hLnn
            have := lipschitzWith_clamp01.dist_le_mul τ' τ; simpa using this
      _ = L * dist τ τ' := by rw [dist_comm]
      _ = (L.toNNReal : ℝ) * dist τ τ' := by rw [Real.coe_toNNReal L hLnn]
  refine ⟨δ, hδ0, hδ1, hLip.continuous,
    ⟨L.toNNReal, hLip.lipschitzOnWith.mono (subset_univ _)⟩, ?_, ?_⟩
  · -- injectivity on `[0,1]`
    intro τ hτ τ' hτ' heq
    rw [hδdef] at heq; simp only at heq
    have hinj := hγinj (hTmem τ) (hTmem τ') heq
    have hSeq : S (T (L * clamp01 τ)) = S (T (L * clamp01 τ')) := by rw [hinj]
    rw [hST, hST] at hSeq
    rw [clamp01_eq_self hτ, clamp01_eq_self hτ'] at hSeq
    exact mul_left_cancel₀ (ne_of_gt hLpos) hSeq
  · -- the trace lies in `γ '' [0,1]`
    intro τ hτ
    rw [hδdef]; simp only
    exact ⟨T (L * clamp01 τ), hTmem τ, rfl⟩

/-- **Constant-speed (arc-length) reparametrization of a continuous finite-variation path —
without assuming injectivity.**

Given any continuous curve `γ` of finite total variation on `[0,1]`, the cumulative-variation
reparametrization produces a curve `δ` on `[0,1]` with the **same endpoints**, **globally
`L`-Lipschitz** (`L =` total length), trace inside `γ '' [0,1]`, total variation `eVariationOn δ
[0,1] ≤ eVariationOn γ [0,1]`, and the crucial **constant-speed identity**

`variationOnFromTo δ [0,1] 0 τ = L * τ`  for `τ ∈ [0,1]`,

i.e. the cumulative variation of `δ` is exactly linear. This is the injectivity-free version of
`lipschitz_simpleArc_of_finiteVariation`; the constant-speed identity is what later forces a
length-*minimizing* `γ` to have an *injective* reparametrization (a positive arc-length gap forces a
positive-variation sub-loop, whose excision would shorten the path). -/
theorem constantSpeedReparam_of_finiteVariation {γ : ℝ → ℂ}
    (hγcont : Continuous γ) (hγbv : eVariationOn γ (Icc (0 : ℝ) 1) ≠ ∞) :
    ∃ δ : ℝ → ℂ, δ 0 = γ 0 ∧ δ 1 = γ 1 ∧ Continuous δ ∧
      LipschitzWith (eVariationOn γ (Icc (0 : ℝ) 1)).toReal.toNNReal δ ∧
      eVariationOn δ (Icc (0 : ℝ) 1) ≤ eVariationOn γ (Icc (0 : ℝ) 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, δ τ ∈ γ '' (Icc (0 : ℝ) 1)) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1,
        variationOnFromTo δ (Icc (0 : ℝ) 1) 0 τ
          = (eVariationOn γ (Icc (0 : ℝ) 1)).toReal * τ) := by
  set s : Set ℝ := Icc (0 : ℝ) 1 with hs
  have h0s : (0 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have h1s : (1 : ℝ) ∈ s := by rw [hs]; constructor <;> norm_num
  have hbv : BoundedVariationOn γ s := hγbv
  have hloc : LocallyBoundedVariationOn γ s := hbv.locallyBoundedVariationOn
  set S : ℝ → ℝ := variationOnFromTo γ s 0 with hSdef
  set L : ℝ := (eVariationOn γ s).toReal with hLdef
  have hLnn : 0 ≤ L := ENNReal.toReal_nonneg
  have hS0 : S 0 = 0 := by rw [hSdef]; exact variationOnFromTo.self γ s 0
  have hsIcc : s ∩ Icc (0 : ℝ) 1 = s := by rw [hs]; simp [Set.inter_self]
  have hS1 : S 1 = L := by
    rw [hSdef, hLdef, variationOnFromTo.eq_of_le γ s (by norm_num : (0 : ℝ) ≤ 1), hsIcc]
  have hSmono : MonotoneOn S s := variationOnFromTo.monotoneOn hloc h0s
  have hScont : ContinuousOn S s := continuousOn_variationOnFromTo hγcont hbv h0s
  -- image of `S` is `Icc 0 L`
  have hSimage : S '' s = Icc 0 L := by
    have himg := ContinuousOn.image_Icc_of_monotoneOn (a := (0 : ℝ)) (b := (1 : ℝ)) (f := S)
      (by norm_num) hScont hSmono
    rw [hs, himg, hS0, hS1]
  -- the (generalized) inverse of `S` restricted to `s`
  set T : ℝ → ℝ := Function.invFunOn S s with hTdef
  have hTspec : ∀ v ∈ Icc (0 : ℝ) L, T v ∈ s ∧ S (T v) = v := by
    intro v hv
    have hex : ∃ a ∈ s, S a = v := by
      have : v ∈ S '' s := by rw [hSimage]; exact hv
      obtain ⟨a, ha, hav⟩ := this; exact ⟨a, ha, hav⟩
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  set δ : ℝ → ℂ := fun τ => γ (T (L * clamp01 τ)) with hδdef
  have hmulmem : ∀ τ, L * clamp01 τ ∈ Icc (0 : ℝ) L := by
    intro τ
    obtain ⟨hc0, hc1⟩ := clamp01_mem τ
    refine ⟨by positivity, ?_⟩
    nlinarith [hLnn]
  have hTmem : ∀ τ, T (L * clamp01 τ) ∈ s := fun τ => (hTspec _ (hmulmem τ)).1
  have hST : ∀ τ, S (T (L * clamp01 τ)) = L * clamp01 τ := fun τ => (hTspec _ (hmulmem τ)).2
  -- endpoints (S is monotone; need `S (T 0) = 0` and `S (T L) = L`, plus reach `0` and `1`)
  have hT0eq : S (T 0) = 0 := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) L := ⟨le_rfl, hLnn⟩
    exact (hTspec 0 h0mem).2
  have hTLeq : S (T L) = L := by
    have hLmem : L ∈ Icc (0 : ℝ) L := ⟨hLnn, le_rfl⟩
    exact (hTspec L hLmem).2
  -- `γ` agrees at points of equal cumulative variation `S`.
  have hγeq_of_Seq : ∀ a ∈ s, ∀ b ∈ s, S a = S b → γ a = γ b := by
    intro a ha b hb hab
    have h0 : variationOnFromTo γ s a b = 0 := by
      have hadd := variationOnFromTo.add hloc h0s ha hb
      simp only [← hSdef] at hadd
      linarith [hadd, hab]
    exact edist_eq_zero.mp (variationOnFromTo.edist_zero_of_eq_zero hloc ha hb h0)
  have hcl0 : L * clamp01 0 = 0 := by
    rw [show clamp01 0 = 0 from clamp01_eq_self (by constructor <;> norm_num), mul_zero]
  have hcl1 : L * clamp01 1 = L := by
    rw [show clamp01 1 = 1 from clamp01_eq_self (by constructor <;> norm_num), mul_one]
  have hδ0 : δ 0 = γ 0 := by
    change γ (T (L * clamp01 0)) = γ 0
    refine hγeq_of_Seq _ (hTmem 0) 0 h0s ?_
    rw [hcl0] at *
    rw [hT0eq, hS0]
  have hδ1 : δ 1 = γ 1 := by
    change γ (T (L * clamp01 1)) = γ 1
    refine hγeq_of_Seq _ (hTmem 1) 1 h1s ?_
    rw [hcl1] at *
    rw [hTLeq, hS1]
  -- global Lipschitz bound with constant `L` (same computation as the injective version)
  have hLip : LipschitzWith L.toNNReal δ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro τ τ'
    set u := T (L * clamp01 τ) with hu
    set u' := T (L * clamp01 τ') with hu'
    have hus : u ∈ s := hTmem τ
    have hu's : u' ∈ s := hTmem τ'
    have hSu : S u = L * clamp01 τ := hST τ
    have hSu' : S u' = L * clamp01 τ' := hST τ'
    have hvar : variationOnFromTo γ s u u' = S u' - S u := by
      have hadd := variationOnFromTo.add hloc h0s hus hu's
      simp only [← hSdef] at hadd
      linarith [hadd]
    have hdist_le : dist (γ u) (γ u') ≤ |S u' - S u| := by
      rw [dist_edist]
      have hmemuu : u ∈ s ∩ uIcc u u' := ⟨hus, left_mem_uIcc⟩
      have hmemuu' : u' ∈ s ∩ uIcc u u' := ⟨hu's, right_mem_uIcc⟩
      have hle : edist (γ u) (γ u') ≤ eVariationOn γ (s ∩ uIcc u u') :=
        eVariationOn.edist_le γ hmemuu hmemuu'
      have hsubne : eVariationOn γ (s ∩ uIcc u u') ≠ ∞ :=
        ne_top_of_le_ne_top hbv (eVariationOn.mono γ inter_subset_left)
      have hreal : (edist (γ u) (γ u')).toReal ≤ (eVariationOn γ (s ∩ uIcc u u')).toReal :=
        ENNReal.toReal_mono hsubne hle
      have hvareq : (eVariationOn γ (s ∩ uIcc u u')).toReal = |variationOnFromTo γ s u u'| := by
        rcases le_total u u' with h | h
        · rw [variationOnFromTo.eq_of_le γ s h, abs_of_nonneg ENNReal.toReal_nonneg, uIcc_of_le h]
        · rw [variationOnFromTo.eq_of_ge γ s h, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
            uIcc_of_ge h]
      rw [hvareq, hvar] at hreal
      exact hreal
    calc dist (δ τ) (δ τ') = dist (γ u) (γ u') := by rw [hδdef]
      _ ≤ |S u' - S u| := hdist_le
      _ = |L * clamp01 τ' - L * clamp01 τ| := by rw [hSu, hSu']
      _ = L * |clamp01 τ' - clamp01 τ| := by rw [← mul_sub, abs_mul, abs_of_nonneg hLnn]
      _ = L * dist (clamp01 τ') (clamp01 τ) := by rw [Real.dist_eq]
      _ ≤ L * dist τ' τ := by
            apply mul_le_mul_of_nonneg_left _ hLnn
            have := lipschitzWith_clamp01.dist_le_mul τ' τ; simpa using this
      _ = L * dist τ τ' := by rw [dist_comm]
      _ = (L.toNNReal : ℝ) * dist τ τ' := by rw [Real.coe_toNNReal L hLnn]
  -- trace inside `γ '' [0,1]`
  have htrace : ∀ τ ∈ Icc (0 : ℝ) 1, δ τ ∈ γ '' (Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact ⟨T (L * clamp01 τ), hTmem τ, rfl⟩
  -- variation bound: `eVariationOn δ ≤ eVariationOn γ`, since `δ = γ ∘ (T ∘ (L • clamp01))` and the
  -- reparam `T ∘ (L • clamp01)` maps `[0,1]` monotonically into `s`.
  have hreparmono : MonotoneOn (fun τ => T (L * clamp01 τ)) (Icc (0 : ℝ) 1) := by
    intro τ hτ τ' hτ' hττ'
    -- `S` is monotone and injective-up-to-γ; use that `S (T v) = v` to compare `T v` values
    have hSv : S (T (L * clamp01 τ)) = L * clamp01 τ := hST τ
    have hSv' : S (T (L * clamp01 τ')) = L * clamp01 τ' := hST τ'
    have hclamp : clamp01 τ ≤ clamp01 τ' := by
      have := lipschitzWith_clamp01.dist_le_mul τ τ'
      -- clamp01 is monotone on ℝ
      unfold clamp01
      exact max_le_max le_rfl (min_le_min le_rfl hττ')
    have hvle : L * clamp01 τ ≤ L * clamp01 τ' := by nlinarith [hLnn]
    by_contra hlt
    push Not at hlt
    have hmono := hSmono (hTmem τ') (hTmem τ) hlt.le
    rw [hSv, hSv'] at hmono
    -- `L * clamp01 τ' ≤ L * clamp01 τ` and `L * clamp01 τ ≤ L * clamp01 τ'` ⟹ equal ⟹ `T` equal
    have heqv : L * clamp01 τ = L * clamp01 τ' := le_antisymm hvle hmono
    exact absurd (congrArg T heqv) (ne_of_gt hlt)
  have hvarle : eVariationOn δ s ≤ eVariationOn γ s := by
    have hmaps : MapsTo (fun τ => T (L * clamp01 τ)) s s := fun τ _ => hTmem τ
    have := eVariationOn.comp_le_of_monotoneOn γ (s := s) (t := s)
      (fun τ => T (L * clamp01 τ)) (hs ▸ hreparmono) hmaps
    simpa [hδdef, Function.comp] using this
  -- constant-speed identity: `variationOnFromTo δ s 0 τ = L * τ` for `τ ∈ [0,1]`.
  -- On `s = [0,1]`, `δ = δ₀ ∘ φ` where `δ₀ = naturalParameterization γ s 0` has *unit* speed on
  -- `S '' s = Icc 0 L`, and `φ τ = L * τ` is the affine scaling onto `Icc 0 L`.
  set δ₀ : ℝ → ℂ := naturalParameterization γ s 0 with hδ₀def
  have hδ₀eq : ∀ v, δ₀ v = γ (T v) := fun v => by
    simp only [hδ₀def, naturalParameterization, Function.comp_apply, hTdef, hSdef]
  have hunit : HasUnitSpeedOn δ₀ (S '' s) := by
    have := has_unit_speed_naturalParameterization γ hloc h0s
    simpa only [hδ₀def, hSdef] using this
  rw [hSimage] at hunit
  -- `φ τ = L * τ`; on `s`, `δ τ = δ₀ (φ τ)`.
  set φ : ℝ → ℝ := fun τ => L * τ with hφdef
  have hδφ : ∀ τ ∈ s, δ τ = δ₀ (φ τ) := by
    intro τ hτ
    rw [hδ₀eq, hδdef]; simp only
    rw [clamp01_eq_self (by rw [← hs]; exact hτ)]
  have hφmono : MonotoneOn φ s := fun x _ y _ hxy => by
    simp only [hφdef]; exact mul_le_mul_of_nonneg_left hxy hLnn
  have hφimage : φ '' s = Icc 0 L := by
    rw [hs]; ext v; simp only [hφdef, mem_image, mem_Icc]
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩; exact ⟨by positivity, by nlinarith [hLnn]⟩
    · rintro ⟨hv0, hvL⟩
      rcases eq_or_lt_of_le hLnn with hL0 | hLpos
      · refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
        have : v = 0 := le_antisymm (hvL.trans hL0.symm.le) hv0
        rw [this, mul_zero]
      · refine ⟨v / L, ⟨by positivity, by rw [div_le_one hLpos]; exact hvL⟩, ?_⟩
        field_simp
  -- constant speed `L` of `δ` on `s`, via composition of unit-speed `δ₀` with the scaling `φ`.
  have hspeedConst : ∀ x ∈ s, ∀ y ∈ s, x ≤ y →
      eVariationOn δ (s ∩ Icc x y) = ENNReal.ofReal (L * (y - x)) := by
    intro x hx y hy hxy
    have hcongr : eVariationOn δ (s ∩ Icc x y) = eVariationOn (δ₀ ∘ φ) (s ∩ Icc x y) := by
      apply eVariationOn.congr
      intro τ hτ; exact hδφ τ hτ.1
    rw [hcongr, eVariationOn.comp_inter_Icc_eq_of_monotoneOn δ₀ φ hφmono hx hy, hφimage]
    -- `δ₀` unit speed on `Icc 0 L`:
    -- `eVariationOn δ₀ (Icc 0 L ∩ Icc (φ x)(φ y)) = ofReal(φ y - φ x)`
    have hφx : φ x ∈ Icc (0 : ℝ) L := by rw [← hφimage]; exact ⟨x, hx, rfl⟩
    have hφy : φ y ∈ Icc (0 : ℝ) L := by rw [← hφimage]; exact ⟨y, hy, rfl⟩
    have := hunit hφx hφy
    simp only [NNReal.coe_one, one_mul] at this
    rw [this]
    congr 1
    simp only [hφdef]; ring
  -- package as `variationOnFromTo δ s 0 τ = L * τ`.
  have hδloc : LocallyBoundedVariationOn δ s := by
    have : HasConstantSpeedOnWith δ s L.toNNReal := by
      rw [hasConstantSpeedOnWith_iff_ordered]
      intro x hx y hy hxy
      rw [hspeedConst x hx y hy hxy]; congr 1; simp [Real.coe_toNNReal L hLnn]
    exact this.hasLocallyBoundedVariationOn
  have hspeed : ∀ τ ∈ Icc (0 : ℝ) 1, variationOnFromTo δ s 0 τ = L * τ := by
    intro τ hτ
    have hτs : τ ∈ s := hτ
    rw [variationOnFromTo.eq_of_le δ s hτ.1, hspeedConst 0 h0s τ hτs hτ.1]
    rw [ENNReal.toReal_ofReal (by nlinarith [hLnn, hτ.1] : 0 ≤ L * (τ - 0))]
    ring
  exact ⟨δ, hδ0, hδ1, hLip.continuous, hLip, hvarle, htrace, hspeed⟩

/-- **A connected continuum's diameter is bounded by its `μH[1]`-length.**

For a (pre)connected subset `Γ ⊆ ℂ`, the Euclidean diameter is at most the one-dimensional Hausdorff
measure: `diam Γ ≤ μH[1] Γ`. The proof is the classical projection argument: for any two points
`p, q ∈ Γ`, project `Γ` orthogonally onto the real line through the direction `p - q` via a
`1`-Lipschitz `ℝ`-linear map `π : ℂ → ℝ`. Then `μH[1] (π '' Γ) ≤ μH[1] Γ`
(`LipschitzWith.hausdorffMeasure_image_le`), and `π '' Γ` is connected (continuous image of a
connected set) hence order-connected in `ℝ`, so it contains the whole interval between `π p` and
`π q`; therefore `μH[1] Γ ≥ μH[1] (π '' Γ) ≥ |π p − π q| = ‖p − q‖` for the chosen direction. Taking
the supremum over `p, q` gives `diam Γ ≤ μH[1] Γ` in the `ℝ≥0∞` (extended) sense `ediam`. -/
theorem ediam_le_hausdorffMeasure_one_of_isPreconnected {Γ : Set ℂ} (hΓ : IsPreconnected Γ) :
    Metric.ediam Γ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ := by
  -- It suffices to bound `edist x y` by `μH[1] Γ` for all `x, y ∈ Γ`.
  apply Metric.ediam_le
  intro x hx y hy
  set H : ℝ≥0∞ := (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ with hHdef
  -- Reduce to the real distance `d = ‖x - y‖`.
  set d : ℝ := ‖x - y‖ with hddef
  have hd0 : 0 ≤ d := norm_nonneg _
  have hedist : edist x y = ENNReal.ofReal d := by rw [edist_dist, dist_eq_norm]
  rw [hedist]
  rcases eq_or_lt_of_le hd0 with hd | hdpos
  · -- `d = 0`: trivial.
    rw [← hd, ENNReal.ofReal_zero]; exact zero_le _
  · -- `d > 0`: project along `w = x - y` by the real inner product `pr z = ⟪z, w⟫_ℝ`.
    set w : ℂ := x - y with hwdef
    have hwnorm : ‖w‖ = d := rfl
    set pr : ℂ → ℝ := fun z => @inner ℝ ℂ _ z w with hprdef
    -- `pr` is `‖w‖`-Lipschitz.
    have hlip : LipschitzWith ‖w‖.toNNReal pr := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      rw [Real.dist_eq, hprdef]
      change |@inner ℝ ℂ _ a w - @inner ℝ ℂ _ b w| ≤ _
      rw [← inner_sub_left]
      calc |@inner ℝ ℂ _ (a - b) w| ≤ ‖a - b‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ‖w‖.toNNReal * dist a b := by
            rw [Real.coe_toNNReal _ (norm_nonneg _), dist_eq_norm]; ring
    -- the difference of projected endpoints is `d²`.
    have hdiff : pr x - pr y = d * d := by
      change @inner ℝ ℂ _ x w - @inner ℝ ℂ _ y w = d * d
      rw [← inner_sub_left, ← hwdef, ← hwnorm, ← real_inner_self_eq_norm_mul_norm w]
    have hyx : pr y ≤ pr x := by linarith [hdiff, mul_nonneg hd0 hd0]
    -- `pr '' Γ` is preconnected hence order-connected; contains the interval `[pr y, pr x]`.
    have hcontpr : Continuous pr := hlip.continuous
    have hsub : Set.Icc (pr y) (pr x) ⊆ pr '' Γ :=
      (hΓ.image pr hcontpr.continuousOn).ordConnected.out ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩
    -- `μH[1]([pr y, pr x]) = ofReal (pr x - pr y) = ofReal (d²)`.
    have hIcc : (μH[1] : Measure ℝ) (Set.Icc (pr y) (pr x)) = ENNReal.ofReal (d * d) := by
      rw [hausdorffMeasure_real, Real.volume_Icc, hdiff]
    -- lower bound on `μH[1] (pr '' Γ)`.
    have hlow : ENNReal.ofReal (d * d) ≤ (μH[1] : Measure ℝ) (pr '' Γ) := by
      rw [← hIcc]; exact measure_mono hsub
    -- upper bound on `μH[1] (pr '' Γ)`.
    have hup : (μH[1] : Measure ℝ) (pr '' Γ) ≤ ‖w‖.toNNReal * H := by
      have := hlip.hausdorffMeasure_image_le (zero_le_one) Γ
      simpa using this
    -- combine: `ofReal (d²) ≤ ofReal d * H`.
    have hcomb : ENNReal.ofReal (d * d) ≤ ENNReal.ofReal d * H := by
      refine hlow.trans (hup.trans ?_)
      rw [hwnorm, show (d.toNNReal : ℝ≥0∞) = ENNReal.ofReal d from rfl]
    -- cancel the positive finite factor `ofReal d`.
    have hofd0 : ENNReal.ofReal d ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr hdpos
    have hofdtop : ENNReal.ofReal d ≠ ∞ := ENNReal.ofReal_ne_top
    have hsq : ENNReal.ofReal (d * d) = ENNReal.ofReal d * ENNReal.ofReal d :=
      ENNReal.ofReal_mul hd0
    rw [hsq] at hcomb
    exact (ENNReal.mul_le_mul_iff_right hofd0 hofdtop).mp hcomb

/-- **Localized continuum length lower bound (the per-ball packing estimate).**

For a connected set `Γ ⊆ ℂ`, a center `z ∈ Γ`, a radius `r > 0`, and a point `w ∈ Γ` with
`r ≤ dist z w`, the local `μH[1]`-length inside the closed ball of radius `r` about `z` is at least
`r`:
`ofReal r ≤ μH[1] (Γ ∩ closedBall z r)`.

The proof is the *localized* projection argument that **avoids any boundary-bumping / sub-continuum
construction**. Consider the `1`-Lipschitz "clamped distance" `f x = min (dist z x) r`. It is
constant `= r` outside the open ball, so `f '' Γ = f '' (Γ ∩ closedBall z r)` away from the single
value `r`; on `Γ ∩ closedBall z r` one has `f x = dist z x`. The continuous image `f '' Γ` is
connected, contains `f z = 0` and `f w = r` (since `r ≤ dist z w`), hence by the intermediate value
theorem contains the whole interval `[0, r]`, and `[0, r) ⊆ f '' (Γ ∩ closedBall z r)`. Therefore
`μH[1] (Γ ∩ closedBall z r) ≥ μH[1] (f '' (Γ ∩ closedBall z r)) ≥ μH[1] [0, r) = r`, using that the
`1`-Lipschitz `f` does not increase `μH[1]` (`LipschitzWith.hausdorffMeasure_image_le`) and
`hausdorffMeasure_real`. -/
theorem ofReal_le_hausdorffMeasure_one_inter_closedBall {Γ : Set ℂ} (hΓconn : IsConnected Γ)
    {z : ℂ} (hz : z ∈ Γ) {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ Γ) (hrw : r ≤ dist z w) :
    ENNReal.ofReal r ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (Γ ∩ Metric.closedBall z r) := by
  classical
  -- The clamped distance `f x = min (dist z x) r`, `1`-Lipschitz.
  set f : ℂ → ℝ := fun x => min (dist z x) r with hfdef
  have hflip : LipschitzWith 1 f := (LipschitzWith.dist_right z).min_const r
  have hfcont : Continuous f := hflip.continuous
  -- `f z = 0` and `f w = r`.
  have hfz : f z = 0 := by simp [hfdef, dist_self, le_of_lt hr]
  have hfw : f w = r := by simp [hfdef, min_eq_right hrw]
  -- `[0, r] ⊆ f '' Γ` by the intermediate value theorem on the connected `Γ`.
  have hIVT : Set.Icc (0 : ℝ) r ⊆ f '' Γ := by
    have h := hΓconn.isPreconnected.intermediate_value hz hw hfcont.continuousOn
    rwa [hfz, hfw] at h
  -- `f '' (Γ ∩ closedBall z r)` contains `[0, r)`.
  set B : Set ℂ := Γ ∩ Metric.closedBall z r with hBdef
  have hcover : Set.Ico (0 : ℝ) r ⊆ f '' B := by
    intro t ht
    obtain ⟨ht0, htr⟩ := ht
    obtain ⟨x, hxΓ, hfx⟩ := hIVT ⟨ht0, le_of_lt htr⟩
    -- `f x = t < r` forces `min (dist z x) r = t`, so `dist z x = t ≤ r`, i.e. `x ∈ closedBall`.
    have hdzx : dist z x = t := by
      have : min (dist z x) r = t := hfx
      rcases le_or_gt (dist z x) r with hle | hlt
      · rwa [min_eq_left hle] at this
      · rw [min_eq_right (le_of_lt hlt)] at this; exact absurd this.symm (ne_of_lt htr)
    refine ⟨x, ⟨hxΓ, ?_⟩, hfx⟩
    rw [Metric.mem_closedBall, dist_comm]; rw [hdzx]; exact le_of_lt htr
  -- length lower bound: `r = μH[1] [0, r) ≤ μH[1] (f '' B) ≤ μH[1] B`.
  have h1 : (μH[1] : Measure ℝ) (Set.Ico (0 : ℝ) r) = ENNReal.ofReal r := by
    rw [hausdorffMeasure_real, Real.volume_Ico, sub_zero]
  have h2 : (μH[1] : Measure ℝ) (Set.Ico (0 : ℝ) r) ≤ (μH[1] : Measure ℝ) (f '' B) :=
    measure_mono hcover
  have h3 : (μH[1] : Measure ℝ) (f '' B) ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) B := by
    have := hflip.hausdorffMeasure_image_le (zero_le_one) B
    simpa using this
  calc ENNReal.ofReal r = (μH[1] : Measure ℝ) (Set.Ico (0 : ℝ) r) := h1.symm
    _ ≤ (μH[1] : Measure ℝ) (f '' B) := h2
    _ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) B := h3

/-- **Far-point existence in a set of diameter `> 2r`.** If `z ∈ Γ` and
`ofReal (2 * r) < ediam Γ`, there is `w ∈ Γ` with `r ≤ dist z w`. Indeed the strict diameter excess
provides a pair `a, b ∈ Γ` with `2r < dist a b ≤ dist a z + dist z b`, so one of `dist z a`,
`dist z b` is `> r`. -/
theorem exists_far_point_of_lt_ediam {Γ : Set ℂ} {z : ℂ} {r : ℝ}
    (hdiam : ENNReal.ofReal (2 * r) < Metric.ediam Γ) :
    ∃ w ∈ Γ, r ≤ dist z w := by
  -- The strict bound `ofReal (2r) < ediam Γ` yields a pair `a, b ∈ Γ`
  -- with `ofReal (2r) < edist a b`.
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ Γ, ∃ b ∈ Γ, ENNReal.ofReal (2 * r) < edist a b := by
    by_contra hcon
    push Not at hcon
    exact absurd (Metric.ediam_le (fun a ha b hb => hcon a ha b hb)) (not_le.mpr hdiam)
  -- Translate to real distances: `2r < dist a b ≤ dist a z + dist z b`.
  have hdab : 2 * r < dist a b := by
    have hd : edist a b = ENNReal.ofReal (dist a b) := by rw [edist_dist]
    rw [hd] at hab
    by_contra hcon
    push Not at hcon
    exact absurd hab (not_lt.mpr (ENNReal.ofReal_le_ofReal hcon))
  have htri : dist a b ≤ dist a z + dist z b := dist_triangle a z b
  -- One of the legs is `≥ r`.
  rcases le_or_gt r (dist z a) with hza | hza
  · exact ⟨a, ha, hza⟩
  · refine ⟨b, hb, ?_⟩
    have hza' : dist a z < r := by rw [dist_comm]; exact hza
    linarith

/-- **The packing bound (lower-content estimate).**

Let `Γ ⊆ ℂ` be connected with `ofReal ε < ediam Γ` (`ε > 0`), and let `C` be a **finite**
`ε`-separated subset of `Γ` (distinct centers more than `ε` apart). The closed balls
`closedBall z (ε/2)` for `z ∈ C` are pairwise disjoint, and each captures local `μH[1]`-length
`≥ ε/2` (by `ofReal_le_hausdorffMeasure_one_inter_closedBall`, since the strict diameter excess
`ofReal ε < ediam Γ` provides for every center a point of `Γ` at distance `≥ ε/2`). Summing the
disjoint contributions gives `#C · (ε/2) ≤ μH[1] Γ`.

This is the genuinely two-dimensional, classically Mathlib-absent **lower-content / packing**
estimate at the heart of the Eilenberg–Harrold ε-chain length bound — proved here from the
localized continuum length estimate, with no boundary-bumping. -/
theorem packing_card_mul_le_hausdorffMeasure_one {Γ : Set ℂ} (hΓconn : IsConnected Γ)
    (hΓmeas : MeasurableSet Γ) {ε : ℝ} (hε : 0 < ε) (hdiam : ENNReal.ofReal ε < Metric.ediam Γ)
    {C : Finset ℂ} (hCΓ : ↑C ⊆ Γ) (hCsep : ∀ z ∈ C, ∀ w ∈ C, z ≠ w → ε < dist z w) :
    (C.card : ℝ≥0∞) * ENNReal.ofReal (ε / 2) ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ := by
  classical
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  -- The disjoint closed balls indexed by `C`.
  set B : ℂ → Set ℂ := fun z => Γ ∩ Metric.closedBall z r with hBdef
  -- Pairwise disjoint.
  have hdisj : (↑C : Set ℂ).PairwiseDisjoint B := by
    intro z hz w hw hzw
    have hsep : ε < dist z w := hCsep z hz w hw hzw
    have hball : Disjoint (Metric.closedBall z r) (Metric.closedBall w r) := by
      apply Metric.closedBall_disjoint_closedBall
      rw [hrdef]; linarith
    exact (hball.mono inter_subset_right inter_subset_right)
  -- Each ball is measurable.
  have hmeas : ∀ z ∈ C, MeasurableSet (B z) := fun z _ =>
    hΓmeas.inter measurableSet_closedBall
  -- Per-ball lower bound `ofReal r ≤ μH[1] (B z)`.
  have hperball : ∀ z ∈ C, ENNReal.ofReal r ≤
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (B z) := by
    intro z hz
    have hzΓ : z ∈ Γ := hCΓ hz
    -- far point: `ofReal (2r) = ofReal ε < ediam Γ`.
    have h2r : ENNReal.ofReal (2 * r) = ENNReal.ofReal ε := by rw [hrdef]; ring_nf
    have hfar : ENNReal.ofReal (2 * r) < Metric.ediam Γ := by rw [h2r]; exact hdiam
    obtain ⟨w, hwΓ, hrw⟩ := exists_far_point_of_lt_ediam (z := z) (r := r) hfar
    exact ofReal_le_hausdorffMeasure_one_inter_closedBall hΓconn hzΓ hr hwΓ hrw
  -- Disjoint additivity: `∑ μH[1] (B z) = μH[1] (⋃ B z) ≤ μH[1] Γ`.
  have hsum : ∑ z ∈ C, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (B z) =
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (⋃ z ∈ C, B z) :=
    (measure_biUnion_finset hdisj hmeas).symm
  have hunionsub : (⋃ z ∈ C, B z) ⊆ Γ := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, _, hxz⟩ := hx
    exact hxz.1
  -- Assemble: `card · ofReal r ≤ ∑ μH[1] (B z) = μH[1] (⋃) ≤ μH[1] Γ`.
  calc (C.card : ℝ≥0∞) * ENNReal.ofReal (ε / 2)
      = ∑ _z ∈ C, ENNReal.ofReal r := by
        rw [Finset.sum_const, nsmul_eq_mul, hrdef]
    _ ≤ ∑ z ∈ C, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (B z) :=
        Finset.sum_le_sum hperball
    _ = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) (⋃ z ∈ C, B z) := hsum
    _ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ := measure_mono hunionsub

section RectifiablePathHelpers

set_option linter.unusedDecidableInType false

/-! ## Eilenberg-Harrold rectifiable-path construction (polygon + chain helpers, inlined) -/


/-- Clamp a real number into `[0,1]`. -/
noncomputable def clmp (τ : ℝ) : ℝ := max 0 (min 1 τ)

theorem clmp_mem (τ : ℝ) : clmp τ ∈ Icc (0 : ℝ) 1 := by
  unfold clmp
  refine ⟨le_max_left _ _, ?_⟩
  rw [max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩

theorem clmp_eq_self {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : clmp τ = τ := by
  unfold clmp
  rw [min_eq_right hτ.2, max_eq_right hτ.1]

/-- Segment index for the parameter `τ` (with `n` segments): the index of the subinterval
`[k/n, (k+1)/n]` containing `clmp τ`, clamped to `{0, …, n-1}`. -/
noncomputable def polyIdx (n : ℕ) (τ : ℝ) : ℕ :=
  min (n - 1) ⌊(n : ℝ) * clmp τ⌋₊

theorem polyIdx_le_sub (n : ℕ) (τ : ℝ) : polyIdx n τ ≤ n - 1 := by
  unfold polyIdx; exact min_le_left _ _

theorem polyIdx_lt (n : ℕ) (hn : 1 ≤ n) (τ : ℝ) : polyIdx n τ < n := by
  have h := polyIdx_le_sub n τ; omega

/-- The polygonal path with `n` segments through the points `z 0, …, z n`. On the `i`-th
subinterval `[i/n, (i+1)/n]` it is the straight segment from `z i` to `z (i+1)`, and it is
clamped to be constant (`z 0` for `τ ≤ 0`, `z (last)` for `τ ≥ 1`) outside `[0,1]`. The successor
index is capped at `n` so that the definition typechecks unconditionally; for `n ≥ 1` (the only
case of interest) this cap is never active. -/
noncomputable def polyPath (n : ℕ) (z : Fin (n + 1) → ℂ) : ℝ → ℂ := fun τ =>
  AffineMap.lineMap (z ⟨polyIdx n τ, by
      have h := polyIdx_le_sub n τ; omega⟩)
    (z ⟨min n (polyIdx n τ + 1), by
      have h := polyIdx_le_sub n τ; omega⟩)
    ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ))

/-- Generic congruence for `lineMap` on `ℂ`: equal endpoints (as `Fin`-values into `z`) and equal
scalar give equal value. This avoids dependent-`rw` motive issues. -/
theorem lineMap_z_congr {n : ℕ} (z : Fin (n + 1) → ℂ) {a b a' b' : ℕ}
    (ha : a < n + 1) (hb : b < n + 1) (ha' : a' < n + 1) (hb' : b' < n + 1)
    (haa : a = a') (hbb : b = b') {c c' : ℝ} (hc : c = c') :
    AffineMap.lineMap (z ⟨a, ha⟩) (z ⟨b, hb⟩) c
      = AffineMap.lineMap (z ⟨a', ha'⟩) (z ⟨b', hb'⟩) c' := by
  subst haa; subst hbb; subst hc; rfl

/-- On the `i`-th subinterval `[i/n, (i+1)/n]`, the polygonal path equals the straight segment
from `z i.castSucc` to `z i.succ`, reparametrized affinely. -/
theorem polyPath_eq_lineMap (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) (i : Fin n)
    {τ : ℝ} (hτ : τ ∈ Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :
    polyPath n z τ = AffineMap.lineMap (z i.castSucc) (z i.succ)
      ((n : ℝ) * τ - (i : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hτ1, hτ2⟩ := hτ
  have hiltn : (i : ℕ) < n := i.2
  have hi_le : (i : ℝ) + 1 ≤ n := by
    have : (i : ℕ) + 1 ≤ n := hiltn
    exact_mod_cast this
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := by
    refine ⟨le_trans ?_ hτ1, le_trans hτ2 ?_⟩
    · positivity
    · rw [div_le_one hnpos]; exact hi_le
  have hclmp : clmp τ = τ := clmp_eq_self hτ01
  have hlow : (i : ℝ) ≤ (n : ℝ) * τ := by
    have := (div_le_iff₀ hnpos).mp hτ1; linarith [this]
  have hhigh : (n : ℝ) * τ ≤ (i : ℝ) + 1 := by
    have := (le_div_iff₀ hnpos).mp hτ2; linarith [this]
  -- The two `Fin` endpoints of `z i.castSucc`, `z i.succ` as plain values:
  have hcs : (i.castSucc : ℕ) = (i : ℕ) := rfl
  have hsu : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
  -- The target rewritten with explicit `Fin.mk` endpoints.
  have htarget : AffineMap.lineMap (z i.castSucc) (z i.succ) ((n : ℝ) * τ - (i : ℝ))
      = AffineMap.lineMap (z ⟨(i : ℕ), by omega⟩) (z ⟨(i : ℕ) + 1, by omega⟩)
          ((n : ℝ) * τ - (i : ℝ)) := by
    apply lineMap_z_congr <;> simp
  rw [htarget]
  by_cases hend : (n : ℝ) * τ = (i : ℝ) + 1
  · -- right endpoint
    have hfloor : ⌊(n : ℝ) * clmp τ⌋₊ = (i : ℕ) + 1 := by
      rw [hclmp, hend, show ((i : ℝ) + 1) = (((i : ℕ) + 1 : ℕ) : ℝ) by push_cast; ring]
      exact Nat.floor_natCast _
    have hidxval : polyIdx n τ = min (n - 1) ((i : ℕ) + 1) := by
      unfold polyIdx; rw [hfloor]
    change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
          ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = _
    rcases Nat.lt_or_ge ((i : ℕ) + 1) n with hcase | hcase
    · -- i+1 < n : index = i+1, param 0; both equal z (i+1)
      have hidx : polyIdx n τ = (i : ℕ) + 1 := by rw [hidxval]; omega
      have hp0 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 0 := by
        rw [hclmp, hidx, hend]; push_cast; ring
      have hp1 : (n : ℝ) * τ - (i : ℝ) = 1 := by rw [hend]; ring
      rw [hp1, AffineMap.lineMap_apply_one]
      rw [hp0, AffineMap.lineMap_apply_zero]
      exact congrArg z (Fin.ext (by simp [hidx]))
    · -- i is last: index = n-1 = i, param 1
      have hin : (i : ℕ) + 1 = n := by omega
      have hidx : polyIdx n τ = (i : ℕ) := by rw [hidxval]; omega
      have hp1 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 1 := by
        rw [hclmp, hidx, hend]; ring
      have hp1' : (n : ℝ) * τ - (i : ℝ) = 1 := by rw [hend]; ring
      rw [hp1', AffineMap.lineMap_apply_one]
      rw [hp1, AffineMap.lineMap_apply_one]
      exact congrArg z (Fin.ext (by simp [hidx, hin]))
  · -- interior: n*τ < i+1, floor = i
    have hlt : (n : ℝ) * τ < (i : ℝ) + 1 := lt_of_le_of_ne hhigh hend
    have hfloor : ⌊(n : ℝ) * clmp τ⌋₊ = (i : ℕ) := by
      rw [hclmp, Nat.floor_eq_iff (le_trans (by positivity) hlow)]
      exact ⟨hlow, hlt⟩
    have hidx : polyIdx n τ = (i : ℕ) := by
      unfold polyIdx; rw [hfloor]; omega
    change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
          ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = _
    apply lineMap_z_congr
    · exact hidx
    · rw [hidx]; omega
    · rw [hclmp, hidx]

/-- Continuity of the polygonal path on the `i`-th subinterval. -/
theorem polyPath_continuousOn_seg (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) (i : Fin n) :
    ContinuousOn (polyPath n z) (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
  apply ContinuousOn.congr (f := fun τ => AffineMap.lineMap (z i.castSucc) (z i.succ)
      ((n : ℝ) * τ - (i : ℝ)))
  · apply Continuous.continuousOn
    exact (AffineMap.lineMap_continuous).comp (by fun_prop)
  · intro τ hτ
    exact polyPath_eq_lineMap n hn z i hτ

/-- Continuity of the polygonal path on `Icc 0 (m/n)`, by induction on `m ≤ n`. -/
theorem polyPath_continuousOn_initial (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    ∀ m : ℕ, m ≤ n → ContinuousOn (polyPath n z) (Icc (0 : ℝ) ((m : ℝ) / n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  intro m
  induction m with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_div]
    exact (Set.subsingleton_Icc_of_ge le_rfl).continuousOn _
  | succ k ih =>
    intro hk
    have hk' : k ≤ n := by omega
    have hkn : (k : ℕ) < n := by omega
    have hsplit : Icc (0 : ℝ) (((k : ℝ) + 1) / n)
        = Icc (0 : ℝ) ((k : ℝ) / n) ∪ Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) := by
      rw [Set.Icc_union_Icc_eq_Icc]
      · positivity
      · gcongr; linarith
    have hpush : ((↑(k + 1) : ℝ)) / n = ((k : ℝ) + 1) / n := by push_cast; ring
    rw [hpush, hsplit]
    refine ContinuousOn.union_of_isClosed (ih hk') ?_ isClosed_Icc isClosed_Icc
    -- second piece is segment i = k
    have := polyPath_continuousOn_seg n hn z ⟨k, hkn⟩
    simpa only [Fin.val_mk] using this

/-- The polygonal path is continuous on `Icc 0 1`. -/
theorem polyPath_continuousOn_unit (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    ContinuousOn (polyPath n z) (Icc (0 : ℝ) 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have := polyPath_continuousOn_initial n hn z n le_rfl
  rwa [div_self (ne_of_gt hnpos)] at this

/-- For `τ ≤ 0` the polygonal path is the constant `z 0`. -/
theorem polyPath_of_nonpos (n : ℕ) (_hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {τ : ℝ} (hτ : τ ≤ 0) :
    polyPath n z τ = z 0 := by
  have hclmp : clmp τ = 0 := by
    unfold clmp; rw [min_eq_right (by linarith), max_eq_left hτ]
  have hidx : polyIdx n τ = 0 := by
    unfold polyIdx; rw [hclmp, mul_zero, Nat.floor_zero, Nat.min_zero]
  change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
      ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = z 0
  have hp0 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 0 := by rw [hclmp, hidx]; simp
  rw [hp0, AffineMap.lineMap_apply_zero]
  exact congrArg z (Fin.ext (by simp [hidx]))

/-- For `τ ≥ 1` the polygonal path is the constant `z (Fin.last n)`. -/
theorem polyPath_of_one_le (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {τ : ℝ} (hτ : 1 ≤ τ) :
    polyPath n z τ = z (Fin.last n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hclmp : clmp τ = 1 := by
    unfold clmp; rw [min_eq_left hτ, max_eq_right (by norm_num)]
  have hfloor : ⌊(n : ℝ) * clmp τ⌋₊ = n := by
    rw [hclmp, mul_one, Nat.floor_natCast]
  have hidx : polyIdx n τ = n - 1 := by
    unfold polyIdx; rw [hfloor]; omega
  change AffineMap.lineMap (z ⟨polyIdx n τ, _⟩) (z ⟨min n (polyIdx n τ + 1), _⟩)
      ((n : ℝ) * clmp τ - (polyIdx n τ : ℝ)) = z (Fin.last n)
  have hp1 : (n : ℝ) * clmp τ - (polyIdx n τ : ℝ) = 1 := by
    rw [hclmp, hidx, mul_one]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
    rw [this]; ring
  rw [hp1, AffineMap.lineMap_apply_one]
  exact congrArg z (Fin.ext (by simp only [Fin.val_last]; omega))

/-- `polyPath n z 0 = z 0`. -/
theorem polyPath_zero (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    polyPath n z 0 = z 0 :=
  polyPath_of_nonpos n hn z le_rfl

/-- `polyPath n z 1 = z (Fin.last n)`. -/
theorem polyPath_one (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    polyPath n z 1 = z (Fin.last n) :=
  polyPath_of_one_le n hn z le_rfl

/-- The polygonal path is continuous on all of `ℝ`. -/
theorem polyPath_continuous (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    Continuous (polyPath n z) := by
  rw [← continuousOn_univ]
  have hcov : (univ : Set ℝ) = Iic 0 ∪ Icc (0 : ℝ) 1 ∪ Ici 1 := by
    ext x; simp only [mem_univ, mem_union, mem_Iic, mem_Icc, mem_Ici, true_iff]
    rcases le_or_gt x 0 with h | h
    · exact Or.inl (Or.inl h)
    · rcases le_or_gt x 1 with h1 | h1
      · exact Or.inl (Or.inr ⟨le_of_lt h, h1⟩)
      · exact Or.inr (le_of_lt h1)
  rw [hcov]
  refine ContinuousOn.union_of_isClosed (ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Iic
    isClosed_Icc) ?_ (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  · -- on Iic 0 : constant z 0
    refine (continuousOn_const (c := z 0)).congr ?_
    intro x hx; exact polyPath_of_nonpos n hn z hx
  · exact polyPath_continuousOn_unit n hn z
  · -- on Ici 1 : constant z (last)
    refine (continuousOn_const (c := z (Fin.last n))).congr ?_
    intro x hx; exact polyPath_of_one_le n hn z hx

/-- The `eVariationOn` of a straight segment `lineMap a b` over `[0,1]` is exactly `edist a b`. -/
theorem eVariationOn_lineMap (a b : ℂ) :
    eVariationOn (AffineMap.lineMap a b : ℝ → ℂ) (Icc (0 : ℝ) 1) = edist a b := by
  apply le_antisymm
  · -- ≤ : lineMap is `nndist a b`-Lipschitz, variation of identity on [0,1] is `edist 0 1`.
    have hlip : LipschitzOnWith (nndist a b) (AffineMap.lineMap a b : ℝ → ℂ) (Icc (0 : ℝ) 1) :=
      (lipschitzWith_lineMap a b).lipschitzOnWith
    have hcomp : eVariationOn ((AffineMap.lineMap a b : ℝ → ℂ) ∘ (id : ℝ → ℝ)) (Icc (0 : ℝ) 1)
        ≤ (nndist a b : ℝ≥0∞) * eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) :=
      hlip.comp_eVariationOn_le (Set.mapsTo_id _)
    simp only [Function.comp_id] at hcomp
    refine hcomp.trans ?_
    -- eVariationOn id (Icc 0 1) = edist 0 1 = 1
    have hidvar : eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) = 1 := by
      apply le_antisymm
      · -- id monotone: variation ≤ ofReal (id 1 - id 0) = 1
        have hmono : MonotoneOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) := fun _ _ _ _ h => h
        have := hmono.eVariationOn_le (a := 0) (b := 1) (by simp) (by simp)
        rw [show (Icc (0:ℝ) 1) ∩ Icc (0:ℝ) 1 = Icc (0:ℝ) 1 from by rw [Set.inter_self]] at this
        simpa using this
      · have := eVariationOn.edist_le (id : ℝ → ℝ) (s := Icc (0:ℝ) 1)
          (x := 1) (y := 0) (by simp) (by simp)
        simpa [edist_dist, Real.dist_eq] using this
    rw [hidvar, mul_one]
    rw [edist_nndist]
  · -- ≥ : edist of the two endpoints lineMap 0 = a, lineMap 1 = b is ≤ variation.
    have h := eVariationOn.edist_le (AffineMap.lineMap a b : ℝ → ℂ)
      (s := Icc (0:ℝ) 1) (x := 0) (y := 1) (by simp) (by simp)
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using h

/-- The variation of the polygonal path over the `i`-th subinterval equals the length of the
`i`-th edge. -/
theorem eVariationOn_polyPath_seg (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) (i : Fin n) :
    eVariationOn (polyPath n z) (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n))
      = edist (z i.castSucc) (z i.succ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set φ : ℝ → ℝ := fun τ => (n : ℝ) * τ - (i : ℝ) with hφdef
  -- polyPath = (lineMap (z cs) (z su)) ∘ φ on the subinterval.
  have hEq : EqOn (polyPath n z)
      ((AffineMap.lineMap (z i.castSucc) (z i.succ) : ℝ → ℂ) ∘ φ)
      (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    intro τ hτ
    simpa only [Function.comp_apply, hφdef] using polyPath_eq_lineMap n hn z i hτ
  rw [eVariationOn.congr hEq]
  -- φ is monotone on the subinterval.
  have hφmono : MonotoneOn φ (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    intro x _ y _ hxy
    simp only [hφdef]
    have := mul_le_mul_of_nonneg_left hxy (le_of_lt hnpos)
    linarith
  rw [eVariationOn.comp_eq_of_monotoneOn _ φ hφmono]
  -- image of φ over the subinterval is Icc 0 1.
  have hφcont : ContinuousOn φ (Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) := by
    apply Continuous.continuousOn; simp only [hφdef]; fun_prop
  have hle : (i : ℝ) / n ≤ ((i : ℝ) + 1) / n := by gcongr; linarith
  have himg : φ '' Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n) = Icc (0 : ℝ) 1 := by
    rw [hφcont.image_Icc_of_monotoneOn hle hφmono]
    have hndvd : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hl : φ ((i : ℝ) / n) = 0 := by
      simp only [hφdef]; field_simp; ring
    have hr : φ (((i : ℝ) + 1) / n) = 1 := by
      simp only [hφdef]; field_simp; ring
    rw [hl, hr]
  rw [himg, eVariationOn_lineMap]

/-- **The key variation bound.** The total variation of the polygonal path over `[0,1]` is
bounded by the sum of the lengths of its edges. -/
theorem eVariationOn_polyPath_le (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) :
    eVariationOn (polyPath n z) (Icc (0 : ℝ) 1)
      ≤ ∑ i : Fin n, edist (z i.castSucc) (z i.succ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set I : ℕ → ℝ := fun k => (k : ℝ) / n with hIdef
  have hImono : Monotone I := by
    intro a b hab
    simp only [hIdef]
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    gcongr
  -- `eVariationOn.sum'` : ∑ over subintervals = variation over [I 0, I n] = [0,1].
  have hsum := eVariationOn.sum' (polyPath n z) hImono (n := n)
  have hI0 : I 0 = 0 := by simp [hIdef]
  have hIn : I n = 1 := by simp only [hIdef]; rw [div_self (ne_of_gt hnpos)]
  rw [hI0, hIn] at hsum
  rw [← hsum]
  -- Each subinterval variation equals the corresponding edge length; reindex Fin n ↔ range n.
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => eVariationOn (polyPath n z) (Icc (I k) (I (k + 1))))]
  apply Finset.sum_le_sum
  intro i _
  have hIi : I (i : ℕ) = (i : ℝ) / n := rfl
  have hIi1 : I ((i : ℕ) + 1) = ((i : ℝ) + 1) / n := by
    simp only [hIdef]; push_cast; ring_nf
  rw [hIi, hIi1]
  exact le_of_eq (eVariationOn_polyPath_seg n hn z i)

/-- For `τ ∈ [0,1]`, the parameter lies in the subinterval indexed by `polyIdx n τ`. -/
theorem mem_seg_of_mem_unit (n : ℕ) (hn : 1 ≤ n) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    τ ∈ Icc ((polyIdx n τ : ℝ) / n) (((polyIdx n τ : ℝ) + 1) / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hclmp : clmp τ = τ := clmp_eq_self hτ
  have hnτnn : (0 : ℝ) ≤ (n : ℝ) * τ := by
    have := hτ.1; positivity
  set k := polyIdx n τ with hk
  -- lower bound : k ≤ n·τ
  have hlow : (k : ℝ) ≤ (n : ℝ) * τ := by
    have hkle : k ≤ ⌊(n : ℝ) * τ⌋₊ := by
      rw [hk]; unfold polyIdx; rw [hclmp]; exact min_le_right _ _
    calc (k : ℝ) ≤ (⌊(n : ℝ) * τ⌋₊ : ℝ) := by exact_mod_cast hkle
      _ ≤ (n : ℝ) * τ := Nat.floor_le hnτnn
  -- upper bound (non-strict) : n·τ ≤ k+1
  have hhigh : (n : ℝ) * τ ≤ (k : ℝ) + 1 := by
    by_cases hcase : ⌊(n : ℝ) * τ⌋₊ ≤ n - 1
    · -- then k = ⌊n·τ⌋₊, use floor upper bound (strict, hence ≤)
      have hkeq : k = ⌊(n : ℝ) * τ⌋₊ := by
        rw [hk]; unfold polyIdx; rw [hclmp]; omega
      rw [hkeq]
      calc (n : ℝ) * τ ≤ (⌊(n : ℝ) * τ⌋₊ : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one _)
        _ = (⌊(n : ℝ) * τ⌋₊ : ℝ) + 1 := rfl
    · -- then k = n-1, and n·τ ≤ n = k+1 (since τ ≤ 1)
      have hkeq : k = n - 1 := by
        rw [hk]; unfold polyIdx; rw [hclmp]; omega
      have hk1 : (k : ℝ) + 1 = n := by
        rw [hkeq]
        have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
        rw [this]; ring
      rw [hk1]
      nlinarith [hτ.2, hnpos]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hnpos]; linarith [hlow]
  · rw [le_div_iff₀ hnpos]; linarith [hhigh]

/-- The trace of the polygonal path lies on one of its edges: for `τ ∈ [0,1]` there is a segment
index `i : Fin n` with `polyPath n z τ ∈ segment ℝ (z i.castSucc) (z i.succ)`. -/
theorem polyPath_mem_segment (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin n, polyPath n z τ ∈ segment ℝ (z i.castSucc) (z i.succ) := by
  refine ⟨⟨polyIdx n τ, polyIdx_lt n hn τ⟩, ?_⟩
  have hmem := mem_seg_of_mem_unit n hn hτ
  rw [polyPath_eq_lineMap n hn z ⟨polyIdx n τ, polyIdx_lt n hn τ⟩ (by simpa using hmem)]
  -- the parameter lies in [0,1], so the point is on the segment.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := hmem
  rw [div_le_iff₀ hnpos] at h1
  rw [le_div_iff₀ hnpos] at h2
  have hparam : (n : ℝ) * τ - ((⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n) : ℝ)
      ∈ Icc (0 : ℝ) 1 := by
    rw [Set.mem_Icc, Fin.val_mk]; constructor <;> linarith
  rw [show segment ℝ (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).castSucc)
        (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).succ)
      = AffineMap.lineMap (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).castSucc)
        (z (⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).succ) '' Icc (0 : ℝ) 1
      from segment_eq_image_lineMap ℝ _ _]
  exact mem_image_of_mem _ hparam

/-- **Distance to a vertex.** Given an upper bound `D` on all edge lengths, every point of the
polygon trace (for `τ ∈ [0,1]`) is within `D` of some vertex `z i`. -/
theorem polyPath_dist_vertex (n : ℕ) (hn : 1 ≤ n) (z : Fin (n + 1) → ℂ) {D : ℝ}
    (hD : ∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ D) :
    ∀ τ ∈ Icc (0 : ℝ) 1, ∃ i : Fin (n + 1), dist (polyPath n z τ) (z i) ≤ D := by
  intro τ hτ
  refine ⟨(⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n).castSucc, ?_⟩
  have hmem := mem_seg_of_mem_unit n hn hτ
  have hidxmem : τ ∈ Icc (((⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n) : ℝ) / n)
      ((((⟨polyIdx n τ, polyIdx_lt n hn τ⟩ : Fin n) : ℝ) + 1) / n) := by simpa using hmem
  rw [polyPath_eq_lineMap n hn z ⟨polyIdx n τ, polyIdx_lt n hn τ⟩ hidxmem]
  -- distance from `lineMap a b t` to `a` is `‖t‖ * dist a b ≤ dist a b ≤ D`.
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := hmem
  rw [div_le_iff₀ hnpos] at h1
  rw [le_div_iff₀ hnpos] at h2
  set i : Fin n := ⟨polyIdx n τ, polyIdx_lt n hn τ⟩ with hi
  have ht0 : 0 ≤ (n : ℝ) * τ - ((i : ℕ) : ℝ) := by simp only [hi, Fin.val_mk]; linarith
  have ht1 : (n : ℝ) * τ - ((i : ℕ) : ℝ) ≤ 1 := by simp only [hi, Fin.val_mk]; linarith
  rw [dist_lineMap_left]
  have hnorm : ‖(n : ℝ) * τ - ((i : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  calc ‖(n : ℝ) * τ - ((i : ℕ) : ℝ)‖ * dist (z i.castSucc) (z i.succ)
      ≤ 1 * dist (z i.castSucc) (z i.succ) :=
        mul_le_mul_of_nonneg_right hnorm dist_nonneg
    _ = dist (z i.castSucc) (z i.succ) := one_mul _
    _ ≤ D := hD i



/-- **ε-chain reachability from connectedness.**
`C` is a finite `ε`-cover of a preconnected `Γ` (every point of `Γ` within `ε` of some center),
with `C ⊆ Γ`. Then any two centers `a, b ∈ C` are joined by a chain of centers with consecutive
gaps `≤ 2ε` — i.e. they are related by the reflexive-transitive closure of the "edge" relation
`step z w := z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2ε`. -/
theorem reachable_of_isCover_preconnected {Γ : Set ℂ} (hΓconn : IsPreconnected Γ)
    {ε : ℝ} (hε : 0 < ε) {C : Finset ℂ} (hCΓ : ↑C ⊆ Γ)
    (hcover : ∀ x ∈ Γ, ∃ z ∈ C, dist x z ≤ ε)
    {a b : ℂ} (ha : a ∈ C) (hb : b ∈ C) :
    Relation.ReflTransGen (fun z w => z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2 * ε) a b := by
  classical
  set step : ℂ → ℂ → Prop := fun z w => z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2 * ε with hstepdef
  -- Reachable set from `a` within `C`.
  set R : Finset ℂ := C.filter (fun w => Relation.ReflTransGen step a w) with hRdef
  -- `a ∈ R`.
  have haR : a ∈ R := by
    rw [hRdef, Finset.mem_filter]
    exact ⟨ha, Relation.ReflTransGen.refl⟩
  -- Reachable centers are in `C`.
  have hRsub : R ⊆ C := Finset.filter_subset _ _
  -- The two closed cover pieces.
  set t : Set ℂ := ⋃ z ∈ R, Metric.closedBall z ε with htdef
  set t' : Set ℂ := ⋃ z ∈ (C \ R), Metric.closedBall z ε with ht'def
  have htclosed : IsClosed t := by
    rw [htdef]
    exact Set.Finite.isClosed_biUnion R.finite_toSet (fun z _ => Metric.isClosed_closedBall)
  have ht'closed : IsClosed t' := by
    rw [ht'def]
    exact Set.Finite.isClosed_biUnion (C \ R).finite_toSet
      (fun z _ => Metric.isClosed_closedBall)
  -- Γ ⊆ t ∪ t'.
  have hcoveruni : Γ ⊆ t ∪ t' := by
    intro x hx
    obtain ⟨z, hzC, hxz⟩ := hcover x hx
    by_cases hzR : z ∈ R
    · left; rw [htdef]; simp only [Set.mem_iUnion]
      exact ⟨z, hzR, by rw [Metric.mem_closedBall]; exact hxz⟩
    · right; rw [ht'def]; simp only [Set.mem_iUnion]
      refine ⟨z, ?_, by rw [Metric.mem_closedBall]; exact hxz⟩
      rw [Finset.mem_sdiff]; exact ⟨hzC, hzR⟩
  -- Γ ∩ t nonempty (a ∈ Γ ∩ t).
  have hat : a ∈ Γ ∩ t := by
    refine ⟨hCΓ ha, ?_⟩
    rw [htdef]; simp only [Set.mem_iUnion]
    exact ⟨a, haR, by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hε⟩
  -- Main claim: `b ∈ R`.
  have hbR : b ∈ R := by
    by_contra hbR
    -- then `b ∈ Γ ∩ t'`.
    have hbt' : b ∈ Γ ∩ t' := by
      refine ⟨hCΓ hb, ?_⟩
      rw [ht'def]; simp only [Set.mem_iUnion]
      refine ⟨b, ?_, by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hε⟩
      rw [Finset.mem_sdiff]; exact ⟨hb, hbR⟩
    -- preconnectedness forces Γ ∩ (t ∩ t') nonempty.
    obtain ⟨x, hxΓ, hxt, hxt'⟩ :=
      (isPreconnected_closed_iff.mp hΓconn) t t' htclosed ht'closed hcoveruni ⟨a, hat⟩ ⟨b, hbt'⟩
    -- extract the two covering centers.
    rw [htdef] at hxt; simp only [Set.mem_iUnion] at hxt
    obtain ⟨z, hzR, hxz⟩ := hxt
    rw [ht'def] at hxt'; simp only [Set.mem_iUnion] at hxt'
    obtain ⟨w, hwCR, hxw⟩ := hxt'
    rw [Metric.mem_closedBall] at hxz hxw
    rw [Finset.mem_sdiff] at hwCR
    obtain ⟨hwC, hwR⟩ := hwCR
    -- `dist z w ≤ 2ε`, so there is an edge `z → w`, contradicting `w ∉ R`.
    have hzC : z ∈ C := hRsub hzR
    have hzw : dist z w ≤ 2 * ε := by
      calc dist z w ≤ dist z x + dist x w := dist_triangle z x w
        _ = dist x z + dist x w := by rw [dist_comm z x]
        _ ≤ ε + ε := add_le_add hxz hxw
        _ = 2 * ε := by ring
    -- `z ∈ R` means `ReflTransGen step a z`; extend by the edge to `w`.
    have hzreach : Relation.ReflTransGen step a z := by
      rw [hRdef, Finset.mem_filter] at hzR; exact hzR.2
    have hwreach : Relation.ReflTransGen step a w :=
      hzreach.tail ⟨hzC, hwC, hzw⟩
    have : w ∈ R := by rw [hRdef, Finset.mem_filter]; exact ⟨hwC, hwreach⟩
    exact hwR this
  rw [hRdef, Finset.mem_filter] at hbR
  exact hbR.2



/-- Loop-excision helper, phrased with a length bound `n` to enable strong induction.
Any `r`-chain `l` with `l.length ≤ n` can be replaced by a `Nodup` `r`-chain with the same
endpoints (head and last). Whenever the chain is not already duplicate-free, we excise a loop
`l[i] … l[j]` (with `i < j` and `l[i] = l[j]`), yielding a strictly shorter chain, and recurse. -/
theorem exists_nodup_isChain_of_isChain_aux {α : Type*}
    {r : α → α → Prop} :
    ∀ (n : ℕ) (l : List α) (hne : l ≠ []) (_hlen : l.length ≤ n) (_hc : l.IsChain r),
      ∃ l' : List α, ∃ (hne' : l' ≠ []),
        l'.head hne' = l.head hne ∧ l'.getLast hne' = l.getLast hne ∧
        l'.IsChain r ∧ l'.Nodup := by
  intro n
  induction n with
  | zero =>
    intro l hne hlen _hc
    exact absurd (Nat.le_zero.mp hlen) (by simpa [List.length_eq_zero_iff] using hne)
  | succ n ih =>
    intro l hne hlen hc
    by_cases hnodup : l.Nodup
    · exact ⟨l, hne, rfl, rfl, hc, hnodup⟩
    · -- extract a duplicate: indices `i < j`, `j < l.length`, `l[i] = l[j]`
      rw [List.nodup_iff_getElem?_ne_getElem?] at hnodup
      push Not at hnodup
      obtain ⟨i, j, hij, hjlen, hdup⟩ := hnodup
      have hilen : i < l.length := lt_trans hij hjlen
      -- turn the `getElem?` equality into a `getElem` equality
      have hdup' : l[i] = l[j] := by
        have := hdup
        rw [List.getElem?_eq_getElem hilen, List.getElem?_eq_getElem hjlen] at this
        exact Option.some.inj this
      -- the spliced list: keep `take (i+1)` then `drop (j+1)`
      set l' : List α := l.take (i + 1) ++ l.drop (j + 1) with hl'def
      -- `take (i+1)` is nonempty
      have htake_ne : l.take (i + 1) ≠ [] := by
        rw [← List.length_pos_iff_ne_nil, List.length_take]
        omega
      have hl'_ne : l' ≠ [] := by
        rw [hl'def]
        simp [htake_ne]
      -- `l'` is a chain via append-overlap at the duplicated element `l[i] = l[j]`
      have hchain' : l'.IsChain r := by
        have h1 : (l.take i ++ [l[i]]).IsChain r := by
          rw [← List.take_succ_eq_append_getElem hilen]
          exact hc.take (i + 1)
        have h2 : ([l[i]] ++ l.drop (j + 1)).IsChain r := by
          have : l.drop j = l[i] :: l.drop (j + 1) := by
            rw [List.drop_eq_getElem_cons hjlen, hdup']
          have hdj : (l.drop j).IsChain r := hc.drop j
          rw [this] at hdj
          simpa using hdj
        have hover := List.IsChain.append_overlap (l₁ := l.take i) (l₂ := [l[i]])
          (l₃ := l.drop (j + 1)) h1 h2 (by simp)
        rw [hl'def, List.take_succ_eq_append_getElem hilen]
        simpa using hover
      -- `l'` is strictly shorter than `l`
      have hlen' : l'.length < l.length := by
        rw [hl'def, List.length_append, List.length_take, List.length_drop]
        rw [Nat.min_eq_left (by omega)]
        omega
      have hlen'' : l'.length ≤ n := by omega
      -- head of `l'` equals head of `l`
      have hhead : l'.head hl'_ne = l.head hne := by
        have hstep : l'.head hl'_ne = (l.take (i + 1)).head htake_ne := by
          apply List.head_append_left
        rw [hstep, List.head_eq_getElem htake_ne, List.getElem_take, List.head_eq_getElem hne]
      -- getLast of `l'` equals getLast of `l`
      have hlast : l'.getLast hl'_ne = l.getLast hne := by
        by_cases hd : l.drop (j + 1) = []
        · -- drop is empty: `j + 1 = l.length`, so `l[j]` is the last element
          have hjlast : j + 1 = l.length := by
            have := List.drop_eq_nil_iff.mp hd
            omega
          have hstep : l'.getLast hl'_ne = (l.take (i + 1)).getLast htake_ne := by
            apply List.getLast_append_left (l' := l.drop (j + 1))
            exact hd
          -- the last element of `take (i+1) l` is `l[i] = l[j]`, which is `l.getLast`
          have htlen : (l.take (i + 1)).length = i + 1 := by
            rw [List.length_take]; omega
          rw [hstep, List.getLast_eq_getElem htake_ne, List.getElem_take,
            List.getLast_eq_getElem hne]
          have e1 : (l.take (i + 1)).length - 1 = i := by omega
          have e2 : l.length - 1 = j := by omega
          simp only [e1, e2]; exact hdup'
        · have hstep : l'.getLast hl'_ne = (l.drop (j + 1)).getLast hd := by
            apply List.getLast_append_of_ne_nil
          rw [hstep, List.getLast_drop, List.getLast_eq_getElem hne]
      -- recurse on the strictly shorter chain
      obtain ⟨l'', hne'', hh'', hl'', hc'', hnd''⟩ := ih l' hl'_ne hlen'' hchain'
      exact ⟨l'', hne'', by rw [hh'', hhead], by rw [hl'', hlast], hc'', hnd''⟩

/-- **Main theorem.** If `a` and `b` are related by the reflexive transitive closure of `r`,
then there is a *duplicate-free* `r`-chain from `a` to `b`. -/
theorem exists_nodup_isChain_of_reflTransGen {α : Type*} [DecidableEq α]
    {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, ∃ (hl : l ≠ []), l.head hl = a ∧ l.getLast hl = b ∧
      l.IsChain r ∧ l.Nodup := by
  -- start from some (possibly looping) chain provided by Mathlib
  obtain ⟨l, hne, hc, hhead, hlast⟩ :=
    List.exists_isChain_ne_nil_of_relationReflTransGen h
  -- excise loops to obtain a `Nodup` chain with the same endpoints
  obtain ⟨l', hne', hh', hl', hc', hnd'⟩ :=
    exists_nodup_isChain_of_isChain_aux l.length l hne le_rfl hc
  exact ⟨l', hne', by rw [hh', hhead], by rw [hl', hlast], hc', hnd'⟩

/-- **Corollary.** If every `r`-step lands inside a finite set `C` containing `a` and `b`, and
`a` reaches `b` under `ReflTransGen r`, then there is a `Nodup`-free (hence length `≤ C.card`)
`r`-chain from `a` to `b` all of whose vertices lie in `C`. -/
theorem exists_nodup_isChain_subset_card {α : Type*} [DecidableEq α]
    {r : α → α → Prop} {C : Finset α} {a b : α} (ha : a ∈ C) (_hb : b ∈ C)
    (hr : ∀ x y, r x y → y ∈ C)
    (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, ∃ (hl : l ≠ []), l.head hl = a ∧ l.getLast hl = b ∧
      l.IsChain r ∧ (∀ x ∈ l, x ∈ C) ∧ l.length ≤ C.card := by
  obtain ⟨l, hl, hhead, hlast, hc, hnd⟩ := exists_nodup_isChain_of_reflTransGen h
  -- every element of `l` is in `C`: the head is `a ∈ C`, every other is an `r`-target
  have hmem : ∀ x ∈ l, x ∈ C := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · -- head element equals `a`
      subst hi0
      rw [List.head_eq_getElem hl] at hhead
      rw [hhead]; exact ha
    · -- `x = l[i]` with `i ≥ 1` is the `r`-target of `l[i-1]`
      have hidx : i - 1 + 1 = i := by omega
      have hstep : r l[i - 1] l[i] := by
        have h0 := hc.getElem (i - 1) (by omega)
        simp only [hidx] at h0
        exact h0
      exact hr _ _ hstep
  refine ⟨l, hl, hhead, hlast, hc, hmem, ?_⟩
  -- length bound: `Nodup` + all elements in `C` gives `l.toFinset ⊆ C`
  have hsub : l.toFinset ⊆ C := by
    intro x hx
    exact hmem x (List.mem_toFinset.mp hx)
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ C.card := Finset.card_le_card hsub



/-- **List → vertex sequence.** Given a nonempty list `L` of complex numbers that is a chain for
the relation `dist · · ≤ 2ε`, with all elements in `Γ`, with head `p` and last `q`, and with
length `≥ 2`, produce a `Fin (n+1) → ℂ` vertex sequence with all the bounds transferred. The number
of segments `n = L.length - 1`. -/
theorem exists_vertices_of_list {Γ : Set ℂ} {ε : ℝ} {p q : ℂ} (L : List ℂ)
    (hlen : 2 ≤ L.length)
    (hmem : ∀ x ∈ L, x ∈ Γ)
    (hchain : L.IsChain (fun z w => dist z w ≤ 2 * ε))
    (hhead : L.head? = some p)
    (hlast : L.getLast? = some q) :
    ∃ (n : ℕ) (z : Fin (n+1) → ℂ), 1 ≤ n ∧ n + 1 = L.length ∧ z 0 = p ∧ z (Fin.last n) = q ∧
      (∀ i : Fin (n+1), z i ∈ Γ) ∧
      (∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ 2 * ε) := by
  -- `n := L.length - 1`, so `L.length = n + 1`.
  have hLne : L ≠ [] := by rintro rfl; simp at hlen
  set n : ℕ := L.length - 1 with hn
  have hLlen : L.length = n + 1 := by omega
  have hn1 : 1 ≤ n := by omega
  -- The vertex function: `z i := L[i]` (with the length cast).
  refine ⟨n, fun i => L[(i : ℕ)]'(by omega), hn1, by omega, ?_, ?_, ?_, ?_⟩
  · -- `z 0 = p`
    have : L[0]'(by omega) = p := by
      have hh : L.head? = some (L[0]'(by omega)) := by
        rw [List.head?_eq_getElem?]
        rw [List.getElem?_eq_getElem (by omega : 0 < L.length)]
      rw [hhead] at hh
      exact ((Option.some.injEq _ _).mp hh).symm
    simpa using this
  · -- `z (Fin.last n) = q`
    have : L[n]'(by omega) = q := by
      have hq' : L.getLast? = some (L[n]'(by omega)) := by
        rw [List.getLast?_eq_getLast_of_ne_nil hLne, List.getLast_eq_getElem hLne]
      rw [hlast] at hq'
      exact ((Option.some.injEq _ _).mp hq').symm
    simpa [Fin.val_last] using this
  · -- membership
    intro i
    exact hmem _ (List.getElem_mem _)
  · -- edge bound
    intro i
    have hbound : (fun j : Fin (n+1) => L[(j : ℕ)]'(by omega)) i.castSucc
        = L[(i : ℕ)]'(by omega) := by simp
    have hbound2 : (fun j : Fin (n+1) => L[(j : ℕ)]'(by omega)) i.succ
        = L[(i : ℕ) + 1]'(by omega) := by simp
    rw [hbound, hbound2]
    have hi1 : (i : ℕ) + 1 < L.length := by have := i.2; omega
    exact hchain.getElem (i : ℕ) hi1

theorem exists_polygon_in_thickening
    {Γ : Set ℂ} (hΓconn : IsPreconnected Γ) {ε : ℝ} (hε : 0 < ε)
    {C : Finset ℂ} (hCΓ : ↑C ⊆ Γ)
    (hcover : ∀ x ∈ Γ, ∃ z ∈ C, dist x z ≤ ε)
    {p q : ℂ} (hp : p ∈ Γ) (hq : q ∈ Γ)
    {zp zq : ℂ} (hzp : zp ∈ C) (hzq : zq ∈ C) (hpzp : dist p zp ≤ ε) (hqzq : dist q zq ≤ ε) :
    ∃ (n : ℕ) (z : Fin (n+1) → ℂ), 1 ≤ n ∧ n ≤ C.card + 1 ∧ z 0 = p ∧ z (Fin.last n) = q ∧
      (∀ i : Fin (n+1), z i ∈ Γ) ∧
      (∀ i : Fin n, dist (z i.castSucc) (z i.succ) ≤ 2 * ε) := by
  classical
  set step : ℂ → ℂ → Prop := fun z w => z ∈ C ∧ w ∈ C ∧ dist z w ≤ 2 * ε with hstepdef
  -- every `step` lands in `C`.
  have hstepC : ∀ x y, step x y → y ∈ C := fun x y h => h.2.1
  -- 1. reachability `zp ⇝ zq`.
  have hreach : Relation.ReflTransGen step zp zq :=
    reachable_of_isCover_preconnected hΓconn hε hCΓ hcover hzp hzq
  -- 2. extract a *Nodup* chain `mid` from `zp` to `zq`, with length `≤ C.card`.
  obtain ⟨mid, hmidne, hmidhead, hmidlast, hmidchain, hmidC, hmidcard⟩ :=
    exists_nodup_isChain_subset_card hzp hzq hstepC hreach
  -- The full vertex list.
  set vlist : List ℂ := p :: (mid ++ [q]) with hvdef
  have hvne : vlist ≠ [] := by simp [hvdef]
  -- length ≥ 2 and `vlist.length = mid.length + 2`.
  have hmidlenpos : 1 ≤ mid.length := List.length_pos_iff.mpr hmidne
  have hvlencalc : vlist.length = mid.length + 2 := by
    rw [hvdef]; simp
  have hvlen : 2 ≤ vlist.length := by omega
  -- membership : every element of `vlist` is in `Γ`.
  have hvmem : ∀ x ∈ vlist, x ∈ Γ := by
    intro x hx
    rw [hvdef, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hp
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hCΓ (hmidC x hx)
    · rw [List.mem_singleton] at hx; subst hx; exact hq
  -- chain for the metric relation `dist · · ≤ 2ε`.
  have hvchain : vlist.IsChain (fun z w => dist z w ≤ 2 * ε) := by
    -- chain on `mid` for the metric relation.
    have hmidmetric : mid.IsChain (fun z w => dist z w ≤ 2 * ε) :=
      hmidchain.imp (fun a b hab => hab.2.2)
    -- append `[q]` : need last of `mid` (= `zq`) within `2ε` of `q`.
    have happ : (mid ++ [q]).IsChain (fun z w => dist z w ≤ 2 * ε) := by
      rw [List.isChain_append]
      refine ⟨hmidmetric, List.isChain_singleton _, ?_⟩
      intro x hx y hy
      rw [List.getLast?_eq_getLast_of_ne_nil hmidne, Option.mem_some_iff] at hx
      rw [List.head?_singleton, Option.mem_some_iff] at hy
      rw [hmidlast] at hx
      subst hx; subst hy
      calc dist zq q = dist q zq := dist_comm zq q
        _ ≤ ε := hqzq
        _ ≤ 2 * ε := by linarith
    -- prepend `p` : `dist p zp ≤ ε ≤ 2ε`, head of `mid ++ [q]` is `zp`.
    refine happ.cons ?_
    intro y hy
    rw [List.head?_append_of_ne_nil _ hmidne] at hy
    rw [List.head?_eq_some_head hmidne, hmidhead, Option.mem_some_iff] at hy
    subst hy
    calc dist p zp ≤ ε := hpzp
      _ ≤ 2 * ε := by linarith
  -- head of `vlist` is `p`.
  have hvhead : vlist.head? = some p := by rw [hvdef, List.head?_cons]
  -- last of `vlist` is `q`.
  have hvlast : vlist.getLast? = some q := by
    rw [hvdef, List.getLast?_cons, List.getLast?_append_cons]
    rfl
  obtain ⟨n, z, hn1, hnlen, hz0, hzlast, hzmem, hzedge⟩ :=
    exists_vertices_of_list (Γ := Γ) (ε := ε) (p := p) (q := q) vlist
      hvlen hvmem hvchain hvhead hvlast
  refine ⟨n, z, hn1, ?_, hz0, hzlast, hzmem, hzedge⟩
  -- `n + 1 = vlist.length = mid.length + 2 ≤ C.card + 2`, so `n ≤ C.card + 1`.
  omega


end RectifiablePathHelpers

/-- **The Eilenberg–Harrold rectifiable-connectedness theorem (PROVEN, no residual).**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length (a *rectifiable continuum*) is
*rectifiably path-connected*: any two of its points `p, q` are joined by a continuous,
**finite-total-variation** path lying entirely in `Γ`.

## Proof (the Eilenberg–Harrold / Wazewski ε-chain construction, fully formalized)

For each `k` take `ε ↓ 0` and a maximal `ε`-separated set `C = maximalSeparatedSet ε Γ` (Mathlib's
covering-number API), which is also an `ε`-cover. Connectedness threads an `ε`-chain
`p ≈ z₀ — z₁ — … — z_m ≈ q` through `C` with each hop `≤ 2ε`
(`reachable_of_isCover_preconnected`, via the two-coloring `isPreconnected_closed_iff`), and the
chain may be taken *duplicate-free* of length `≤ #C` (`exists_nodup_isChain_subset_card`, loop
excision). The **lower-content / packing bound** `#C · (ε/2) ≤ μH[1] Γ`
(`packing_card_mul_le_hausdorffMeasure_one`) — proved here from the *localized* continuum length
estimate `ofReal_le_hausdorffMeasure_one_inter_closedBall` with **no boundary-bumping**, the
genuinely two-dimensional ingredient classically absent from Mathlib — bounds the total polygonal
length `≤ #C · 2ε + …` uniformly by `6 · μH[1] Γ`. The polygons `γ_k` (`polyPath`) have traces
within `2ε` of `Γ`; constant-speed reparametrization (`constantSpeedReparam_of_finiteVariation`)
makes them equi-Lipschitz, and Arzelà–Ascoli on the fixed compact `cthickening 1 Γ` extracts a
uniform limit `γ*`, which lies in `Γ` because `infDist (γ* τ) Γ ≤ 2ε → 0` and `Γ` is closed; lower
semicontinuity of `eVariationOn` keeps the limit's variation finite. -/
theorem exists_finiteVariation_path_of_connected_finite_hausdorff {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) :
    ∃ γ : ℝ → ℂ, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 1) ≠ ∞ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ Γ) := by
  classical
  set I : Set ℝ := Icc (0 : ℝ) 1 with hI
  -- Degenerate case `p = q`: use the constant path.
  by_cases hpq : p = q
  · refine ⟨fun _ => p, rfl, by rw [hpq], continuous_const, ?_, ?_⟩
    · have hsub : ((fun _ : ℝ => p) '' I).Subsingleton := by
        rintro a ⟨_, _, rfl⟩ b ⟨_, _, rfl⟩; rfl
      rw [eVariationOn.constant_on hsub]
      exact ENNReal.zero_ne_top
    · intro τ _; exact hpΓ
  -- Nontrivial case. Basic constants.
  have hΓne : Γ.Nonempty := ⟨p, hpΓ⟩
  have hΓmeas : MeasurableSet Γ := hΓcpt.isClosed.measurableSet
  have hΓpre : IsPreconnected Γ := hΓconn.isPreconnected
  set D : ℝ := ((MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ).toReal with hDdef
  -- ediam finiteness.
  have hediam_ne : Metric.ediam Γ ≠ ∞ := hΓcpt.isBounded.ediam_ne_top
  set E : ℝ := (Metric.ediam Γ).toReal with hEdef
  -- p ≠ q ⟹ 0 < dist p q ≤ ediam Γ ⟹ ediam Γ > 0, E > 0.
  have hpqdist : 0 < dist p q := dist_pos.mpr hpq
  have hdist_le_ediam : ENNReal.ofReal (dist p q) ≤ Metric.ediam Γ := by
    rw [Metric.ediam]
    exact le_trans (le_of_eq (by rw [edist_dist])) (Metric.edist_le_ediam_of_mem hpΓ hqΓ)
  have hediam_pos : 0 < Metric.ediam Γ := by
    refine lt_of_lt_of_le ?_ hdist_le_ediam
    rwa [ENNReal.ofReal_pos]
  have hediam_eq : ENNReal.ofReal E = Metric.ediam Γ := by
    rw [hEdef, ENNReal.ofReal_toReal hediam_ne]
  have hEpos : 0 < E := by
    rw [hEdef]; exact ENNReal.toReal_pos hediam_pos.ne' hediam_ne
  -- ediam ≤ μH[1] Γ, so E ≤ D, and D > 0.
  have hediam_le_H : Metric.ediam Γ ≤ (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ :=
    ediam_le_hausdorffMeasure_one_of_isPreconnected hΓpre
  have hE_le_D : E ≤ D := by
    rw [hEdef, hDdef]; exact ENNReal.toReal_mono hΓfin hediam_le_H
  have hDpos : 0 < D := lt_of_lt_of_le hEpos hE_le_D
  -- STEP 1+2: for each `k`, build a polygon path `γ k` with uniform variation bound and trace
  -- within `2 (ε k)` of Γ, where `ε k := min (E/(k+2)) (1/2)`.
  set ε : ℕ → ℝ := fun k => min (E / (k + 2)) (1 / 2) with hεdef
  have hεpos : ∀ k, 0 < ε k := by
    intro k; rw [hεdef]; simp only [lt_min_iff]
    refine ⟨?_, by norm_num⟩
    apply div_pos hEpos; positivity
  have hε_le_half : ∀ k, ε k ≤ 1 / 2 := fun k => by rw [hεdef]; exact min_le_right _ _
  have hε_lt_E : ∀ k, ε k < E := by
    intro k
    have h1 : ε k ≤ E / (k + 2) := by rw [hεdef]; exact min_le_left _ _
    refine lt_of_le_of_lt h1 ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hEpos]
  have hε_le_E : ∀ k, ε k ≤ E := fun k => le_of_lt (hε_lt_E k)
  -- `ofReal (ε k) < ediam Γ`.
  have hofReal_lt : ∀ k, ENNReal.ofReal (ε k) < Metric.ediam Γ := by
    intro k
    rw [← hediam_eq]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt (hεpos k)) |>.mpr (hε_lt_E k)
  -- The per-k polygon construction.
  have hpoly : ∀ k, ∃ (n : ℕ) (z : Fin (n + 1) → ℂ), 1 ≤ n ∧
      polyPath n z 0 = p ∧ polyPath n z 1 = q ∧ Continuous (polyPath n z) ∧
      eVariationOn (polyPath n z) I ≤ ENNReal.ofReal (6 * D) ∧
      (∀ τ ∈ I, ∃ w ∈ Γ, dist (polyPath n z τ) w ≤ 2 * ε k) := by
    intro k
    have hεk : 0 < ε k := hεpos k
    -- NNReal radius and its coercions.
    set rk : ℝ≥0 := (ε k).toNNReal with hrkdef
    have hrk_coe : (rk : ℝ) = ε k := by rw [hrkdef]; exact Real.coe_toNNReal _ (le_of_lt hεk)
    have hrk_enn : (rk : ℝ≥0∞) = ENNReal.ofReal (ε k) := by
      rw [ENNReal.coe_nnreal_eq, hrk_coe]
    set rk2 : ℝ≥0 := (ε k / 2).toNNReal with hrk2def
    have hrk2_coe : (rk2 : ℝ) = ε k / 2 := by
      rw [hrk2def]; exact Real.coe_toNNReal _ (by positivity)
    -- packing number finiteness via a finite cover.
    have hpackne : Metric.packingNumber rk Γ ≠ ⊤ := by
      obtain ⟨N, hNΓ, hNfin, hNcov⟩ :=
        Metric.exists_finite_isCover_of_isCompact (ε := rk2)
          (by rw [hrk2def, ne_eq, Real.toNNReal_eq_zero, not_le]; positivity) hΓcpt
      have hle : Metric.packingNumber rk Γ ≤ Metric.externalCoveringNumber rk2 Γ := by
        have h2 := Metric.packingNumber_two_mul_le_externalCoveringNumber rk2 Γ
        have hcoe : (2 * rk2 : ℝ≥0) = rk := by
          apply NNReal.coe_injective; rw [NNReal.coe_mul, hrk2_coe, hrk_coe]; push_cast; ring
        rwa [hcoe] at h2
      have hext_le : Metric.externalCoveringNumber rk2 Γ ≤ N.encard :=
        hNcov.externalCoveringNumber_le_encard
      exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin) (le_trans hle hext_le)
    -- the maximal separated set: finite, separated, covering.
    set Cset : Set ℂ := Metric.maximalSeparatedSet rk Γ with hCsetdef
    have hCsetfin : Cset.Finite := by
      have hencardle : Cset.encard ≤ Metric.packingNumber rk Γ := by
        rw [hCsetdef, Metric.encard_maximalSeparatedSet hpackne]
      exact Set.encard_ne_top_iff.mp (ne_top_of_le_ne_top hpackne hencardle)
    set C : Finset ℂ := hCsetfin.toFinset with hCfinDef
    have hC_eq : (↑C : Set ℂ) = Cset := hCsetfin.coe_toFinset
    have hCΓ : (↑C : Set ℂ) ⊆ Γ := by rw [hC_eq, hCsetdef]; exact Metric.maximalSeparatedSet_subset
    -- separated: distinct centers have `dist > ε k`.
    have hCsep : ∀ z ∈ C, ∀ w ∈ C, z ≠ w → ε k < dist z w := by
      intro z hz w hw hzw
      have hsep := Metric.isSeparated_maximalSeparatedSet (ε := rk) (A := Γ)
      have hzC : z ∈ Cset := by rw [← hC_eq]; exact hz
      have hwC : w ∈ Cset := by rw [← hC_eq]; exact hw
      have hedist : (rk : ℝ≥0∞) < edist z w := hsep hzC hwC hzw
      rw [edist_dist, hrk_enn] at hedist
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hεk)).mp hedist
    -- covering: every Γ-point is within `ε k` of some center.
    have hcover : ∀ x ∈ Γ, ∃ z ∈ C, dist x z ≤ ε k := by
      intro x hx
      have hcov := Metric.isCover_maximalSeparatedSet (ε := rk) hpackne
      obtain ⟨z, hzCset, hxz⟩ := hcov hx
      refine ⟨z, by rw [hCfinDef, Set.Finite.mem_toFinset]; exact hzCset, ?_⟩
      have hxz' : edist x z ≤ (rk : ℝ≥0∞) := hxz
      rw [edist_dist, hrk_enn] at hxz'
      exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hεk)).mp hxz'
    -- centers for `p` and `q`.
    obtain ⟨zp, hzpC, hpzp⟩ := hcover p hpΓ
    obtain ⟨zq, hzqC, hqzq⟩ := hcover q hqΓ
    -- build the polygon.
    obtain ⟨n, z, hn1, hncard, hz0, hzlast, hzmem, hzedge⟩ :=
      exists_polygon_in_thickening hΓpre hεk hCΓ hcover hpΓ hqΓ hzpC hzqC hpzp hqzq
    -- packing bound in ℝ: `C.card * ε k ≤ 2 D`.
    have hcard_bound : (C.card : ℝ) * ε k ≤ 2 * D := by
      have hpack := packing_card_mul_le_hausdorffMeasure_one hΓconn hΓmeas hεk
        (hofReal_lt k) hCΓ hCsep
      -- take toReal of `C.card * ofReal (ε k / 2) ≤ μH[1] Γ`.
      have hfin : (C.card : ℝ≥0∞) * ENNReal.ofReal (ε k / 2) ≠ ∞ :=
        ne_top_of_le_ne_top hΓfin hpack
      have htoreal := ENNReal.toReal_mono hΓfin hpack
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
        at htoreal
      -- `C.card * (ε k / 2) ≤ D` ⟹ `C.card * ε k ≤ 2 D`.
      nlinarith [htoreal]
    refine ⟨n, z, hn1, polyPath_zero n hn1 z ▸ hz0, ?_, polyPath_continuous n hn1 z, ?_, ?_⟩
    · rw [polyPath_one n hn1 z]; exact hzlast
    · -- variation bound.
      rw [hI]
      refine le_trans (eVariationOn_polyPath_le n hn1 z) ?_
      -- each edge length ≤ ofReal (2 ε k), so the sum ≤ n • ofReal (2 ε k).
      have hedge_enn : ∀ i : Fin n, edist (z i.castSucc) (z i.succ) ≤ ENNReal.ofReal (2 * ε k) := by
        intro i
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hzedge i)
      have hsum_le : (∑ i : Fin n, edist (z i.castSucc) (z i.succ))
          ≤ (n : ℕ) • ENNReal.ofReal (2 * ε k) := by
        refine le_trans (Finset.sum_le_sum (fun i _ => hedge_enn i)) ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      refine le_trans hsum_le ?_
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      -- `n * (2 ε k) ≤ 6 D`.
      have hn_le : (n : ℝ) ≤ (C.card : ℝ) + 1 := by exact_mod_cast hncard
      have hεE : ε k ≤ E := hε_le_E k
      nlinarith [hcard_bound, hn_le, hεpos k, hE_le_D, hDpos]
    · -- trace within `2 ε k` of Γ.
      intro τ hτ
      obtain ⟨i, hi⟩ := polyPath_dist_vertex n hn1 z hzedge τ hτ
      exact ⟨z i, hzmem i, hi⟩
  -- Extract the polygon family.
  choose n z hn1 hpoly0 hpoly1 hpolycont hpolyvar hpolytrace using hpoly
  set γpoly : ℕ → ℝ → ℂ := fun k => polyPath (n k) (z k) with hγpolydef
  -- STEP 3: constant-speed reparametrize each `γpoly k` to `δ k`.
  have hδexists : ∀ k, ∃ δ : ℝ → ℂ, δ 0 = p ∧ δ 1 = q ∧ Continuous δ ∧
      LipschitzWith (ENNReal.ofReal (6 * D)).toReal.toNNReal δ ∧
      eVariationOn δ I ≤ ENNReal.ofReal (6 * D) ∧
      (∀ τ ∈ I, ∃ w ∈ Γ, dist (δ τ) w ≤ 2 * ε k) := by
    intro k
    have hγcont : Continuous (γpoly k) := hpolycont k
    have hγvar : eVariationOn (γpoly k) I ≤ ENNReal.ofReal (6 * D) := hpolyvar k
    have hγfin : eVariationOn (γpoly k) (Icc (0 : ℝ) 1) ≠ ∞ := by
      rw [← hI]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hγvar
    obtain ⟨δ, hδ0, hδ1, hδcont, hδLip, hδvarle, hδtrace, _⟩ :=
      constantSpeedReparam_of_finiteVariation hγcont hγfin
    refine ⟨δ, ?_, ?_, hδcont, ?_, ?_, ?_⟩
    · rw [hδ0]; exact hpoly0 k
    · rw [hδ1]; exact hpoly1 k
    · -- weaken Lipschitz constant to the uniform `ofReal (6D)`-bound.
      refine hδLip.weaken ?_
      apply Real.toNNReal_mono
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      rw [← hI]; exact (le_of_eq rfl).trans (hγvar.trans_eq' (by rw [hI]))
    · -- variation bound carries through.
      exact le_trans hδvarle hγvar
    · -- trace: `δ τ = γpoly k σ` and `γpoly k σ` is within `2 ε k` of Γ.
      intro τ hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := by rw [← hI]; exact hτ
      obtain ⟨σ, hσmem, hσeq⟩ := hδtrace τ hτ'
      rw [← hσeq]
      have hσI : σ ∈ I := by rw [hI]; exact hσmem
      exact hpolytrace k σ hσI
  choose δ hδ0 hδ1 hδcont hδLipK hδvarle hδtrace using hδexists
  -- The uniform Lipschitz constant.
  set K : ℝ≥0 := (ENNReal.ofReal (6 * D)).toReal.toNNReal with hKdef
  have hδLip : ∀ k, LipschitzWith K (δ k) := hδLipK
  -- STEP 4: Arzela-Ascoli on the fixed compact `K0 := cthickening 1 Γ`.
  set K0 : Set ℂ := Metric.cthickening 1 Γ with hK0def
  have hK0cpt : IsCompact K0 := hΓcpt.cthickening
  -- each `δ k τ ∈ K0` for `τ ∈ I`.
  have hδmemK0 : ∀ k, ∀ τ ∈ I, δ k τ ∈ K0 := by
    intro k τ hτ
    obtain ⟨w, hwΓ, hwdist⟩ := hδtrace k τ hτ
    have h2εle : (2 : ℝ) * ε k ≤ 1 := by nlinarith [hε_le_half k]
    rw [hK0def]
    exact Metric.cthickening_mono h2εle Γ
      (Metric.mem_cthickening_of_dist_le _ w (2 * ε k) Γ hwΓ hwdist)
  -- Lift each `δ k` (restricted to the compact `[0,1]`) to a bounded continuous function.
  haveI hcs : CompactSpace (↥I) := by rw [hI]; exact isCompact_iff_compactSpace.mp isCompact_Icc
  set F : ℕ → BoundedContinuousFunction (↥I) ℂ :=
    fun k => BoundedContinuousFunction.mkOfCompact
      ⟨fun x => δ k x.1, ((hδcont k).comp continuous_subtype_val)⟩ with hFdef
  set A : Set (BoundedContinuousFunction (↥I) ℂ) := Set.range F with hAdef
  have hFmem : ∀ (f : BoundedContinuousFunction (↥I) ℂ) (x : ↥I),
      f ∈ A → f x ∈ K0 := by
    rintro f x ⟨k, rfl⟩
    exact hδmemK0 k x.1 x.2
  have hequi : Equicontinuous
      (fun (x : ↥A) => ⇑(↑x : BoundedContinuousFunction (↥I) ℂ)) := by
    have hlipA : ∀ (c : ↥A),
        LipschitzWith K (fun (x : ↥I) => ((↑c : BoundedContinuousFunction (↥I) ℂ)) x) := by
      rintro ⟨f, k, rfl⟩
      intro a b
      simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using (hδLip k) (a : ℝ) (b : ℝ)
    exact (LipschitzWith.uniformEquicontinuous _ K hlipA).equicontinuous
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli K0 hK0cpt A hFmem hequi
  obtain ⟨Glim, _, φ, hφmono, hφtend⟩ :=
    hcompact.tendsto_subseq (fun k => subset_closure ⟨k, rfl⟩)
  -- pointwise convergence of the subsequence at each `x : ↥I`.
  have hptsub : ∀ x : ↥I, Tendsto (fun k => F (φ k) x) atTop (𝓝 (Glim x)) := by
    intro x
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtend).tendsto_at x
  -- The limit path, extended off `[0,1]` by clamping (using `clmp` from ScratchPolygon).
  set γstar : ℝ → ℂ := fun τ => Glim ⟨clmp τ, clmp_mem τ⟩ with hγstardef
  have hγstarcont : Continuous γstar := by
    apply Glim.continuous.comp
    apply Continuous.subtype_mk
    unfold clmp; fun_prop
  have hγstarval : ∀ τ (hτ : τ ∈ I), γstar τ = Glim ⟨τ, hτ⟩ := by
    intro τ hτ
    simp only [hγstardef]
    congr 1
    exact Subtype.ext (clmp_eq_self (by rw [← hI]; exact hτ))
  have hptconv : ∀ τ ∈ I, Tendsto (fun k => δ (φ k) τ) atTop (𝓝 (γstar τ)) := by
    intro τ hτ
    have := hptsub ⟨τ, hτ⟩
    rw [hγstarval τ hτ]
    simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using this
  -- endpoints.
  have h0I : (0 : ℝ) ∈ I := by rw [hI]; exact ⟨le_rfl, by norm_num⟩
  have h1I : (1 : ℝ) ∈ I := by rw [hI]; exact ⟨by norm_num, le_rfl⟩
  have hγstar0 : γstar 0 = p := by
    have htend := hptconv 0 h0I
    have hconst : (fun k => δ (φ k) (0:ℝ)) = fun _ => p := by funext k; exact hδ0 (φ k)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := p))
  have hγstar1 : γstar 1 = q := by
    have htend := hptconv 1 h1I
    have hconst : (fun k => δ (φ k) (1:ℝ)) = fun _ => q := by funext k; exact hδ1 (φ k)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := q))
  -- `ε k → 0`, hence `ε (φ k) → 0` (subsequence).
  have hεtend : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    have htend1 : Tendsto (fun k : ℕ => E / (k + 2)) atTop (𝓝 (0 : ℝ)) := by
      have := tendsto_const_div_atTop_nhds_zero_nat E
      have hcomp := this.comp (tendsto_add_atTop_nat 2)
      refine hcomp.congr ?_
      intro k; simp only [Function.comp_apply]; push_cast; ring_nf
    refine squeeze_zero (fun k => le_of_lt (hεpos k)) (fun k => ?_) htend1
    rw [hεdef]; exact min_le_left _ _
  have hεφtend : Tendsto (fun k => ε (φ k)) atTop (𝓝 (0 : ℝ)) :=
    hεtend.comp hφmono.tendsto_atTop
  -- trace `γstar τ ∈ Γ` via `infDist (γstar τ) Γ = 0` (Γ closed).
  have hγstarmem : ∀ τ ∈ I, γstar τ ∈ Γ := by
    intro τ hτ
    rw [hΓcpt.isClosed.mem_iff_infDist_zero hΓne]
    refine le_antisymm ?_ Metric.infDist_nonneg
    -- `infDist (γstar τ) Γ ≤ dist (γstar τ) (δ (φ k) τ) + 2 ε (φ k) → 0`.
    have hbound : ∀ k, Metric.infDist (γstar τ) Γ
        ≤ dist (γstar τ) (δ (φ k) τ) + 2 * ε (φ k) := by
      intro k
      obtain ⟨w, hwΓ, hwdist⟩ := hδtrace (φ k) τ hτ
      calc Metric.infDist (γstar τ) Γ
          ≤ dist (γstar τ) w := Metric.infDist_le_dist_of_mem hwΓ
        _ ≤ dist (γstar τ) (δ (φ k) τ) + dist (δ (φ k) τ) w := dist_triangle _ _ _
        _ ≤ dist (γstar τ) (δ (φ k) τ) + 2 * ε (φ k) := by gcongr
    -- the right-hand side tends to 0.
    have hrhs_tend : Tendsto (fun k => dist (γstar τ) (δ (φ k) τ) + 2 * ε (φ k))
        atTop (𝓝 (0 : ℝ)) := by
      have hd : Tendsto (fun k => dist (γstar τ) (δ (φ k) τ)) atTop (𝓝 (0 : ℝ)) := by
        have := (hptconv τ hτ).dist (tendsto_const_nhds (x := γstar τ))
        simpa [dist_comm] using this
      have he : Tendsto (fun k => 2 * ε (φ k)) atTop (𝓝 (0 : ℝ)) := by
        have := hεφtend.const_mul (2 : ℝ); simpa using this
      have := hd.add he; simpa using this
    -- pass the inequality to the limit.
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_tend hbound
  -- variation finiteness via lower semicontinuity.
  have hvarstar_le : eVariationOn γstar I ≤ ENNReal.ofReal (6 * D) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hmv, hvvar⟩ := exists_between hlt
    have hev := eVariationOn.lowerSemicontinuous_aux hptconv hvvar
    -- but each `eVariationOn (δ (φ k)) I ≤ ofReal(6D) < v`, contradiction.
    have hev2 : ∀ k, eVariationOn (δ (φ k)) I < v :=
      fun k => lt_of_le_of_lt (hδvarle (φ k)) hmv
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (le_of_lt (hev2 k)))
  have hvarstar_fin : eVariationOn γstar I ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvarstar_le
  -- Assemble.
  refine ⟨γstar, hγstar0, hγstar1, hγstarcont, ?_, ?_⟩
  · rw [hI] at hvarstar_fin ⊢; exact hvarstar_fin
  · intro τ hτ; rw [hI] at hτ; exact hγstarmem τ hτ


/-- **The Eilenberg–Harrold geodesic existence theorem: a length-minimizing arc exists.**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length (a *rectifiable continuum*) is
*rectifiably path-connected* and the path metric is *geodesic*: any two of its points `p ≠ q` are
joined by a continuous, **finite-total-variation** path lying in `Γ` whose length **minimizes** the
total variation over *all* continuous paths from `p` to `q` in `Γ`.

## Proof

The **geodesic-existence** half is proved here from a single residual. Take one finite-variation
competitor from `exists_finiteVariation_path_of_connected_finite_hausdorff` (the rectifiable
path-connectedness residual), so the infimum `m` of competitor lengths is finite. Choose a
minimizing sequence of competitor lengths `≤ V₀` (the first competitor's length), realize each by a
competitor, and constant-speed reparametrize (`constantSpeedReparam_of_finiteVariation`) to obtain
paths `gₙ` that are uniformly `K`-Lipschitz on `[0,1]` (with `K = V₀.toReal`), have the same
endpoints and trace in `Γ`, and length `→ m`. Lift the `gₙ` (restricted to the compact `[0,1]`) to
bounded continuous functions valued in the compact `Γ`; equi-Lipschitz gives equicontinuity, so
**Arzelà–Ascoli** yields a uniformly convergent subsequence with limit `γ*`. Continuity, the
endpoints, and the trace in `Γ` (closedness) pass to the limit, and **lower semicontinuity of
`eVariationOn`** under pointwise convergence (`eVariationOn.lowerSemicontinuous_aux`) bounds
`eVariationOn γ* [0,1] ≤ m`. Since `γ*` is a competitor its length is `≥ m`, so it equals `m` and is
minimal.

The single remaining ingredient is the **rectifiable path-connectedness residual**
`exists_finiteVariation_path_of_connected_finite_hausdorff` (the Eilenberg–Harrold ε-chain /
covering-number content, absent from Mathlib): the existence of *one* finite-variation competitor.

The hypothesis `p ≠ q` is part of the consumer's interface (it makes the minimal length positive for
the downstream loop-excision in `simpleRectifiableArc_of_compact_connected_finite_hausdorff`); the
minimizer construction itself does not consume it. -/
theorem geodesicMinimizer_of_connected_finite_hausdorff {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (_hpq : p ≠ q) :
    ∃ γ : ℝ → ℂ, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 1) ≠ ∞ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ Γ) ∧
      (∀ η : ℝ → ℂ, Continuous η → η 0 = p → η 1 = q →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, η τ ∈ Γ) →
          eVariationOn γ (Set.Icc (0 : ℝ) 1) ≤ eVariationOn η (Set.Icc (0 : ℝ) 1)) := by
  classical
  set I : Set ℝ := Icc (0 : ℝ) 1 with hI
  -- The competitor class: continuous paths `p → q` lying in `Γ` (no finiteness required).
  set Comp : (ℝ → ℂ) → Prop :=
    fun η => Continuous η ∧ η 0 = p ∧ η 1 = q ∧ (∀ τ ∈ I, η τ ∈ Γ) with hCompdef
  -- The set of competitor lengths in `ℝ≥0∞`, and its infimum `m`.
  set S : Set ℝ≥0∞ := {v | ∃ η, Comp η ∧ eVariationOn η I = v} with hSdef
  set m : ℝ≥0∞ := sInf S with hmdef
  -- From the rectifiable-connectedness residual: at least one finite-length competitor exists.
  obtain ⟨γ₀, hγ₀0, hγ₀1, hγ₀cont, hγ₀fin, hγ₀mem⟩ :=
    exists_finiteVariation_path_of_connected_finite_hausdorff hΓcpt hΓconn hΓfin hpΓ hqΓ
  have hγ₀comp : Comp γ₀ := ⟨hγ₀cont, hγ₀0, hγ₀1, hγ₀mem⟩
  set V₀ : ℝ≥0∞ := eVariationOn γ₀ I with hV₀def
  have hV₀S : V₀ ∈ S := ⟨γ₀, hγ₀comp, rfl⟩
  -- `m ≤ V₀ < ∞`.
  have hmleV₀ : m ≤ V₀ := sInf_le hV₀S
  have hmne : m ≠ ∞ := ne_top_of_le_ne_top hγ₀fin hmleV₀
  -- Restrict to competitor lengths `≤ V₀`; the infimum is unchanged but now uniformly finite.
  set S' : Set ℝ≥0∞ := S ∩ Set.Iic V₀ with hS'def
  have hV₀S' : V₀ ∈ S' := ⟨hV₀S, Set.mem_Iic.mpr le_rfl⟩
  -- `sInf S' = m`.
  have hSinf' : sInf S' = m := by
    apply le_antisymm
    · -- `sInf S' ≤ m = sInf S`: any `s ∈ S` dominates an element of `S'`.
      refine le_sInf ?_
      intro s hs
      by_cases hsle : s ≤ V₀
      · exact sInf_le ⟨hs, hsle⟩
      · exact (sInf_le hV₀S').trans (le_of_lt (not_le.mp hsle))
    · -- `m = sInf S ≤ sInf S'` since `S' ⊆ S`.
      exact le_sInf (fun s hs => sInf_le hs.1)
  -- A minimizing antitone sequence of competitor lengths `≤ V₀`, tending to `m`.
  obtain ⟨u, humono, hutend, humem'⟩ :=
    exists_seq_tendsto_sInf ⟨V₀, hV₀S'⟩ (OrderBot.bddBelow S')
  rw [hSinf'] at hutend
  -- each `u n` is a competitor length `≤ V₀ < ∞`.
  have hule : ∀ n, u n ≤ V₀ := fun n => (humem' n).2
  have hune : ∀ n, u n ≠ ∞ := fun n => ne_top_of_le_ne_top hγ₀fin (hule n)
  have humem : ∀ n, u n ∈ S := fun n => (humem' n).1
  -- choose a competitor `η n` realizing each length `u n`.
  have hηchoice : ∀ n, ∃ ζ, Comp ζ ∧ eVariationOn ζ I = u n := fun n => humem n
  choose ζ hζcomp hζlen using hηchoice
  -- constant-speed reparametrization `g n` of `ζ n`: globally Lipschitz with constant
  -- `(u n).toReal`, same endpoints, trace in `Γ`, variation `≤ u n`.
  have hgexists : ∀ n, ∃ g : ℝ → ℂ, g 0 = p ∧ g 1 = q ∧ Continuous g ∧
      LipschitzWith (u n).toReal.toNNReal g ∧
      eVariationOn g I ≤ u n ∧ (∀ τ ∈ I, g τ ∈ Γ) := by
    intro n
    obtain ⟨hζcont, hζ0, hζ1, hζmem⟩ := hζcomp n
    have hζfin : eVariationOn (ζ n) I ≠ ∞ := by rw [hζlen]; exact hune n
    obtain ⟨g, hg0, hg1, hgcont, hgLip, hgvarle, hgtrace, _⟩ :=
      constantSpeedReparam_of_finiteVariation hζcont hζfin
    refine ⟨g, ?_, ?_, hgcont, ?_, ?_, ?_⟩
    · rw [hg0, hζ0]
    · rw [hg1, hζ1]
    · rw [hζlen] at hgLip; exact hgLip
    · rw [hζlen] at hgvarle; exact hgvarle
    · intro τ hτ
      obtain ⟨σ, hσmem, hσeq⟩ := hgtrace τ hτ
      rw [← hσeq]; exact hζmem σ hσmem
  choose g hg0 hg1 hgcont hgLip hgvarle hgtrace using hgexists
  -- uniform Lipschitz bound `K := (V₀).toReal.toNNReal` for all `g n`.
  set K : ℝ≥0 := V₀.toReal.toNNReal with hKdef
  have hgLipK : ∀ n, LipschitzWith K (g n) := by
    intro n
    refine (hgLip n).weaken ?_
    exact Real.toNNReal_mono ((ENNReal.toReal_le_toReal (hune n) hγ₀fin).mpr (hule n))
  -- variation of `g n` is squeezed `m ≤ eVariationOn (g n) I ≤ u n → m`.
  have hgvar_ge : ∀ n, m ≤ eVariationOn (g n) I := by
    intro n
    refine sInf_le ⟨g n, ⟨hgcont n, hg0 n, hg1 n, hgtrace n⟩, rfl⟩
  have hgvar_tend : Tendsto (fun n => eVariationOn (g n) I) atTop (𝓝 m) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hutend hgvar_ge hgvarle
  -- **Arzelà–Ascoli extraction.** Lift each `g n` (restricted to the compact `[0,1]`) to a
  -- bounded continuous function; the family is valued in the compact `Γ` and is equi-`K`-Lipschitz,
  -- hence equicontinuous. Arzelà–Ascoli gives a uniformly convergent subsequence.
  haveI hcs : CompactSpace (↥I) := by rw [hI]; exact isCompact_iff_compactSpace.mp isCompact_Icc
  set F : ℕ → BoundedContinuousFunction (↥I) ℂ :=
    fun n => BoundedContinuousFunction.mkOfCompact
      ⟨fun x => g n x.1, ((hgcont n).comp continuous_subtype_val)⟩ with hFdef
  set A : Set (BoundedContinuousFunction (↥I) ℂ) := Set.range F with hAdef
  have hFmem : ∀ (f : BoundedContinuousFunction (↥I) ℂ) (x : ↥I),
      f ∈ A → f x ∈ Γ := by
    rintro f x ⟨n, rfl⟩
    exact hgtrace n x.1 x.2
  have hequi : Equicontinuous
      (fun (x : ↥A) => ⇑(↑x : BoundedContinuousFunction (↥I) ℂ)) := by
    have hlipA : ∀ (c : ↥A),
        LipschitzWith K (fun (x : ↥I) => ((↑c : BoundedContinuousFunction (↥I) ℂ)) x) := by
      rintro ⟨f, n, rfl⟩
      intro a b
      simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using (hgLipK n) (a : ℝ) (b : ℝ)
    exact (LipschitzWith.uniformEquicontinuous _ K hlipA).equicontinuous
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli Γ hΓcpt A hFmem hequi
  obtain ⟨Glim, _, φ, hφmono, hφtend⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  -- pointwise convergence of the subsequence at each `x : ↥I`.
  have hptsub : ∀ x : ↥I, Tendsto (fun n => F (φ n) x) atTop (𝓝 (Glim x)) := by
    intro x
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtend).tendsto_at x
  -- **The limit path** `γstar`, extended off `[0,1]` by clamping.
  set γstar : ℝ → ℂ := fun τ => Glim ⟨clamp01 τ, clamp01_mem τ⟩ with hγstardef
  -- continuity of `γstar`.
  have hγstarcont : Continuous γstar := by
    apply Glim.continuous.comp
    apply Continuous.subtype_mk
    unfold clamp01; fun_prop
  -- on `[0,1]`, `γstar τ = Glim ⟨τ, _⟩`, and `g (φ n) τ → γstar τ`.
  have hγstarval : ∀ τ (hτ : τ ∈ I), γstar τ = Glim ⟨τ, hτ⟩ := by
    intro τ hτ
    simp only [hγstardef]
    congr 1
    exact Subtype.ext (clamp01_eq_self hτ)
  have hptconv : ∀ τ ∈ I, Tendsto (fun n => g (φ n) τ) atTop (𝓝 (γstar τ)) := by
    intro τ hτ
    have := hptsub ⟨τ, hτ⟩
    rw [hγstarval τ hτ]
    simpa [hFdef, BoundedContinuousFunction.mkOfCompact] using this
  -- endpoints: `γstar 0 = p`, `γstar 1 = q`.
  have h0I : (0 : ℝ) ∈ I := by rw [hI]; exact ⟨le_rfl, by norm_num⟩
  have h1I : (1 : ℝ) ∈ I := by rw [hI]; exact ⟨by norm_num, le_rfl⟩
  have hγstar0 : γstar 0 = p := by
    have htend := hptconv 0 h0I
    have hconst : (fun n => g (φ n) (0:ℝ)) = fun _ => p := by funext n; exact hg0 (φ n)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := p))
  have hγstar1 : γstar 1 = q := by
    have htend := hptconv 1 h1I
    have hconst : (fun n => g (φ n) (1:ℝ)) = fun _ => q := by funext n; exact hg1 (φ n)
    rw [hconst] at htend
    exact tendsto_nhds_unique htend (tendsto_const_nhds (x := q))
  -- trace: `γstar τ ∈ Γ` for `τ ∈ [0,1]` (`Γ` is closed and each `g (φ n) τ ∈ Γ`).
  have hγstarmem : ∀ τ ∈ I, γstar τ ∈ Γ := by
    intro τ hτ
    refine hΓcpt.isClosed.mem_of_tendsto (hptconv τ hτ) (Eventually.of_forall ?_)
    intro n; exact hgtrace (φ n) τ hτ
  -- **Lower semicontinuity:** `eVariationOn γstar I ≤ m`.
  have hvarstar_le : eVariationOn γstar I ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hmv, hvvar⟩ := exists_between hlt
    have hev := eVariationOn.lowerSemicontinuous_aux hptconv hvvar
    -- `eVariationOn (g (φ n)) I → m < v`, so eventually `< v`.
    have hsubtend : Tendsto (fun n => eVariationOn (g (φ n)) I) atTop (𝓝 m) :=
      hgvar_tend.comp hφmono.tendsto_atTop
    have hev2 : ∀ᶠ n in atTop, eVariationOn (g (φ n)) I < v := hsubtend.eventually_lt_const hmv
    obtain ⟨n, h1, h2⟩ := (hev.and hev2).exists
    exact absurd h1 (not_lt.mpr h2.le)
  -- `γstar` is a competitor, so its length is `≥ m`; hence `= m`, and it is finite.
  have hvarstar_ge : m ≤ eVariationOn γstar I :=
    sInf_le ⟨γstar, ⟨hγstarcont, hγstar0, hγstar1, hγstarmem⟩, rfl⟩
  have hvarstar_eq : eVariationOn γstar I = m := le_antisymm hvarstar_le hvarstar_ge
  have hvarstar_fin : eVariationOn γstar I ≠ ∞ := by rw [hvarstar_eq]; exact hmne
  -- **Assemble the minimizer.** Any competitor `η` has length `≥ m = eVariationOn γstar I`.
  refine ⟨γstar, hγstar0, hγstar1, hγstarcont, hvarstar_fin, hγstarmem, ?_⟩
  intro η hηcont hη0 hη1 hηmem
  rw [hvarstar_eq]
  exact sInf_le ⟨η, ⟨hηcont, hη0, hη1, hηmem⟩, rfl⟩

/-- **The Eilenberg–Harrold / Hahn–Mazurkiewicz topological core (now reduced to the geodesic
existence residual `geodesicMinimizer_of_connected_finite_hausdorff`).**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length is arcwise connected by a
**simple** (injective on `[0,1]`) arc of **finite total variation** lying entirely in `Γ`.

The proof is now **honest analytic content** modulo the single geodesic-existence residual: take a
length-minimizing path `γ` (from `geodesicMinimizer_of_connected_finite_hausdorff`), pass to its
constant-speed reparametrization `δ` (`constantSpeedReparam_of_finiteVariation`), and show `δ` is
**injective** by *loop excision*: if `δ s = δ t` with `s < t`, the constant-speed identity gives the
sub-loop positive length `L·(t−s) > 0`, so excising it (re-routing over `[0,s] ∪ [t,1]`, which is
continuous precisely because `δ s = δ t`) produces a strictly shorter competitor, contradicting the
minimality of `γ`. -/
theorem simpleRectifiableArc_of_compact_connected_finite_hausdorff {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (hpq : p ≠ q) :
    ∃ γ : ℝ → ℂ, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 1) ≠ ∞ ∧
      Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, γ τ ∈ Γ := by
  classical
  -- Geodesic minimizer `γ₀` from the isolated EH/Arzelà–Ascoli residual.
  obtain ⟨γ₀, hγ₀0, hγ₀1, hγ₀cont, hγ₀bv, hγ₀mem, hmin⟩ :=
    geodesicMinimizer_of_connected_finite_hausdorff hΓcpt hΓconn hΓfin hpΓ hqΓ hpq
  -- Constant-speed reparametrization `δ` of `γ₀`.
  obtain ⟨δ, hδ0, hδ1, hδcont, hδLip, hδvarle, hδtrace, hδspeed⟩ :=
    constantSpeedReparam_of_finiteVariation hγ₀cont hγ₀bv
  set L : ℝ := (eVariationOn γ₀ (Icc (0 : ℝ) 1)).toReal with hLdef
  have hδ0p : δ 0 = p := by rw [hδ0, hγ₀0]
  have hδ1q : δ 1 = q := by rw [hδ1, hγ₀1]
  -- `δ` lands in `Γ` (its trace is inside `γ₀ '' [0,1] ⊆ Γ`).
  have hδmem : ∀ τ ∈ Icc (0 : ℝ) 1, δ τ ∈ Γ := by
    intro τ hτ
    obtain ⟨σ, hσmem, hσeq⟩ := hδtrace τ hτ
    rw [← hσeq]; exact hγ₀mem σ hσmem
  -- `δ` is itself a competitor, so its length is `≥` the minimal length; hence `= L`.
  have hδlen_ge : eVariationOn γ₀ (Icc (0 : ℝ) 1) ≤ eVariationOn δ (Icc (0 : ℝ) 1) :=
    hmin δ hδcont hδ0p hδ1q hδmem
  have hδlen : eVariationOn δ (Icc (0 : ℝ) 1) = eVariationOn γ₀ (Icc (0 : ℝ) 1) :=
    le_antisymm hδvarle hδlen_ge
  -- minimal length is finite and positive: `L = eVariationOn γ₀ [0,1] ∈ (0, ∞)`.
  have hγ₀ne : eVariationOn γ₀ (Icc (0 : ℝ) 1) ≠ ∞ := hγ₀bv
  have hδne : eVariationOn δ (Icc (0 : ℝ) 1) ≠ ∞ := by rw [hδlen]; exact hγ₀ne
  have hpos : 0 < eVariationOn δ (Icc (0 : ℝ) 1) := by
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
    have hle : edist (δ 0) (δ 1) ≤ eVariationOn δ (Icc (0 : ℝ) 1) :=
      eVariationOn.edist_le δ h0mem h1mem
    have hedpos : 0 < edist (δ 0) (δ 1) := by
      rw [edist_pos, hδ0p, hδ1q]; exact hpq
    exact lt_of_lt_of_le hedpos hle
  have hLpos : 0 < L := by
    rw [hLdef, ← hδlen]
    exact ENNReal.toReal_pos (ne_of_gt hpos) hδne
  -- constant-speed identity in `ℝ≥0∞` form is what `hδspeed` gives in `ℝ` form; record both.
  -- `variationOnFromTo δ [0,1] x y = L * (y - x)` for `x ≤ y` in `[0,1]`.
  have hδloc : LocallyBoundedVariationOn δ (Icc (0 : ℝ) 1) :=
    (BoundedVariationOn.locallyBoundedVariationOn (hδne))
  have hvarft : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      variationOnFromTo δ (Icc (0 : ℝ) 1) x y = L * (y - x) := by
    intro x hx y hy
    have hadd := variationOnFromTo.add hδloc (⟨le_rfl, by norm_num⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1) hx hy
    have hsx := hδspeed x hx
    have hsy := hδspeed y hy
    -- `variationOnFromTo δ s 0 y = variationOnFromTo δ s 0 x + variationOnFromTo δ s x y`
    have : variationOnFromTo δ (Icc (0 : ℝ) 1) x y
        = variationOnFromTo δ (Icc (0:ℝ) 1) 0 y - variationOnFromTo δ (Icc (0:ℝ) 1) 0 x := by
      linarith [hadd]
    rw [this, hsx, hsy]; ring
  -- **Injectivity of `δ` via loop excision.**
  -- Core: if `δ s = δ t` with `s < t` (both in `[0,1]`), we reach a contradiction.
  have hexcise : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s < t → δ s = δ t → False := by
    intro s hs t ht hslt hst
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    have hsm : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
    have htm : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
    -- positive sub-loop length on `[s,t]`.
    have hloopvar : variationOnFromTo δ (Icc (0 : ℝ) 1) s t = L * (t - s) :=
      hvarft s hsm t htm
    have hlooppos : 0 < L * (t - s) := by
      apply mul_pos hLpos; linarith
    -- The loop endpoints cannot be `(0,1)`: else `δ 0 = δ 1`, i.e. `p = q`, contradicting `p ≠ q`.
    have hnot01 : ¬ (s = 0 ∧ t = 1) := by
      rintro ⟨rfl, rfl⟩
      rw [hδ0p, hδ1q] at hst; exact hpq hst
    have htms : t - s < 1 := by
      rcases lt_or_eq_of_le hs0 with hs0' | hs0'
      · linarith
      · rcases lt_or_eq_of_le ht1 with ht1' | ht1'
        · linarith
        · exact absurd ⟨hs0'.symm, ht1'⟩ hnot01
    -- Build the excised competitor `η` on `[0,1]`, skipping the loop `(s,t)`.
    set m : ℝ := 1 - (t - s) with hmdef
    have hmpos : 0 < m := by rw [hmdef]; linarith
    set c : ℝ := s / m with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    have hcm : m * c = s := by rw [hcdef]; field_simp
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hmpos, hmdef]; linarith
    set η : ℝ → ℂ := fun τ => if τ ≤ c then δ (m * τ) else δ (m * τ + (t - s)) with hηdef
    -- continuity of `η`: each branch continuous; they agree at `τ = c` since `δ s = δ t`.
    have hηcont : Continuous η := by
      have hcont1 : Continuous (fun τ : ℝ => δ (m * τ)) :=
        hδcont.comp (continuous_const.mul continuous_id)
      have hcont2 : Continuous (fun τ : ℝ => δ (m * τ + (t - s))) :=
        hδcont.comp ((continuous_const.mul continuous_id).add continuous_const)
      have hagree : (fun τ : ℝ => δ (m * τ)) c = (fun τ : ℝ => δ (m * τ + (t - s))) c := by
        simp only
        have e1 : m * c = s := hcm
        have e2 : m * c + (t - s) = t := by rw [hcm]; ring
        rw [e1] at e2 ⊢
        rw [e2]; exact hst
      simpa only [hηdef] using
        (Continuous.if_le hcont1 hcont2 continuous_id continuous_const (fun x hx => by
          subst hx; exact hagree))
    -- `η 0 = p`, `η 1 = q`.
    have hη0 : η 0 = p := by
      simp only [hηdef]
      rw [if_pos hc0, mul_zero, hδ0p]
    have hη1 : η 1 = q := by
      simp only [hηdef]
      by_cases hcge : (1 : ℝ) ≤ c
      · -- `c ≥ 1` forces `c = 1` (we have `c ≤ 1`), so `m = s`, hence `t = 1` and `δ (m·1) = δ 1`.
        rw [if_pos hcge]
        have hceq : c = 1 := le_antisymm hc1 hcge
        -- `m * c = s` with `c = 1` gives `m = s`; and `m = 1-(t-s)` gives `t = 1`.
        have hms : m = s := by rw [← hcm, hceq, mul_one]
        have ht1' : t = 1 := by rw [hmdef] at hms; linarith
        rw [show m * 1 = s by rw [mul_one, hms]]
        rw [hst, ht1', hδ1q]
      · rw [if_neg hcge]
        rw [show m * 1 + (t - s) = 1 by rw [hmdef]; ring, hδ1q]
    -- trace of `η` in `Γ`.
    have hηmem : ∀ τ ∈ Icc (0 : ℝ) 1, η τ ∈ Γ := by
      intro τ hτ
      obtain ⟨hτ0, hτ1⟩ := hτ
      simp only [hηdef]
      split_ifs with h
      · apply hδmem; constructor
        · positivity
        · -- `m * τ ≤ m * c = s ≤ 1`.
          have h1 : m * τ ≤ m * c := mul_le_mul_of_nonneg_left h hmpos.le
          rw [hcm] at h1; linarith
      · apply hδmem; constructor
        · push Not at h
          have : 0 ≤ m * τ := by positivity
          linarith
        · -- `m * τ + (t - s) ≤ 1`: since `τ ≤ 1`, `m*τ ≤ m`, so `m*τ + (t-s) ≤ m + (t-s) = 1`.
          have hmt : m * τ ≤ m := by nlinarith [hmpos, hτ1]
          rw [hmdef] at hmt; linarith
    -- variation of `η`: split `[0,1]` at `c`; each piece is a monotone reparam of `δ`.
    have hηvar : eVariationOn η (Icc (0 : ℝ) 1) < eVariationOn δ (Icc (0 : ℝ) 1) := by
      -- sub-interval variation of `δ` in `ℝ≥0∞` form: `eVar δ ([0,1] ∩ [x,y]) = ofReal (L (y-x))`.
      have hδsub : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x ≤ y →
          eVariationOn δ (Icc (0 : ℝ) 1 ∩ Icc x y) = ENNReal.ofReal (L * (y - x)) := by
        intro x hx y hy hxy
        have hft := hvarft x hx y hy
        rw [variationOnFromTo.eq_of_le δ (Icc (0 : ℝ) 1) hxy] at hft
        have hsubne : eVariationOn δ (Icc (0 : ℝ) 1 ∩ Icc x y) ≠ ∞ :=
          ne_top_of_le_ne_top hδne (eVariationOn.mono δ inter_subset_left)
        rw [← hft, ENNReal.ofReal_toReal hsubne]
      -- pieces: `0 ≤ c ≤ 1`, split `[0,1]` at `c`.
      have hcmem : c ∈ Icc (0 : ℝ) 1 := ⟨hc0, hc1⟩
      have hsplit := eVariationOn.Icc_add_Icc η (a := (0:ℝ)) (b := c) (c := (1:ℝ))
        (s := Icc (0:ℝ) 1) hc0 hc1 hcmem
      -- `[0,1] ∩ [0,c] = [0,c]`, `[0,1] ∩ [c,1] = [c,1]`, `[0,1] ∩ [0,1] = [0,1]`.
      have hI1 : Icc (0:ℝ) 1 ∩ Icc 0 c = Icc 0 c := by
        rw [inter_eq_right]; exact Icc_subset_Icc le_rfl hc1
      have hI2 : Icc (0:ℝ) 1 ∩ Icc c 1 = Icc c 1 := by
        rw [inter_eq_right]; exact Icc_subset_Icc hc0 le_rfl
      have hI3 : Icc (0:ℝ) 1 ∩ Icc 0 1 = Icc (0:ℝ) 1 := by rw [inter_self]
      rw [hI1, hI2, hI3] at hsplit
      -- piece 1: `η = δ ∘ (m·)` on `[0,c]`; variation `= eVar δ [0, m·c] = eVar δ [0, s]`.
      have hpiece1 : eVariationOn η (Icc 0 c) = eVariationOn δ (Icc (0:ℝ) 1 ∩ Icc 0 s) := by
        have hcongr : eVariationOn η (Icc 0 c) = eVariationOn (fun τ => δ (m * τ)) (Icc 0 c) := by
          apply eVariationOn.congr
          intro τ hτ; simp only [hηdef]; rw [if_pos hτ.2]
        rw [hcongr]
        have hmono : MonotoneOn (fun τ => m * τ) (Icc (0:ℝ) c) := fun a _ b _ hab =>
          mul_le_mul_of_nonneg_left hab hmpos.le
        rw [show (fun τ => δ (m * τ)) = δ ∘ (fun τ => m * τ) from rfl,
          eVariationOn.comp_eq_of_monotoneOn δ (fun τ => m * τ) hmono]
        congr 1
        -- `(m·) '' [0,c] = [0,1] ∩ [0, s]`
        have hssub : Icc (0:ℝ) s ⊆ Icc (0:ℝ) 1 :=
          Icc_subset_Icc le_rfl (by rw [← hcm]; nlinarith [hmpos, hc1])
        rw [inter_eq_right.mpr hssub]
        ext v; simp only [mem_image, mem_Icc]
        constructor
        · rintro ⟨w, ⟨hw0, hwc⟩, rfl⟩
          refine ⟨by positivity, ?_⟩
          rw [← hcm]; exact mul_le_mul_of_nonneg_left hwc hmpos.le
        · rintro ⟨hv0, hvs⟩
          refine ⟨v / m, ⟨by positivity, ?_⟩, by field_simp⟩
          rw [div_le_iff₀ hmpos, mul_comm]
          rw [← hcm] at hvs; exact hvs
      -- piece 2: `η = δ ∘ (m·+(t-s))` on `[c,1]`; variation `= eVar δ [t, 1]`.
      have hpiece2 : eVariationOn η (Icc c 1) = eVariationOn δ (Icc (0:ℝ) 1 ∩ Icc t 1) := by
        have hcongr : eVariationOn η (Icc c 1)
            = eVariationOn (fun τ => δ (m * τ + (t - s))) (Icc c 1) := by
          apply eVariationOn.congr
          intro τ hτ; simp only [hηdef]
          rcases eq_or_lt_of_le hτ.1 with hc | hc
          · -- at `τ = c`, both branches agree (`δ s = δ t`).
            rw [← hc, if_pos le_rfl]
            have e2 : m * c + (t - s) = t := by rw [hcm]; ring
            rw [e2, show m * c = s from hcm, hst]
          · rw [if_neg (not_le.mpr hc)]
        rw [hcongr]
        have hmono : MonotoneOn (fun τ => m * τ + (t - s)) (Icc c (1:ℝ)) := fun a _ b _ hab => by
          simp only; nlinarith [mul_le_mul_of_nonneg_left hab hmpos.le]
        rw [show (fun τ => δ (m * τ + (t - s))) = δ ∘ (fun τ => m * τ + (t - s)) from rfl,
          eVariationOn.comp_eq_of_monotoneOn δ (fun τ => m * τ + (t - s)) hmono]
        congr 1
        -- `(m·+(t-s)) '' [c,1] = [0,1] ∩ [t, 1]`
        rw [inter_eq_right.mpr (Icc_subset_Icc (by linarith) le_rfl)]
        ext v; simp only [mem_image, mem_Icc]
        constructor
        · rintro ⟨w, ⟨hcw, hw1⟩, rfl⟩
          refine ⟨?_, ?_⟩
          · -- `m*w+(t-s) ≥ m*c+(t-s) = s+(t-s) = t`
            have : m * c + (t - s) ≤ m * w + (t - s) := by
              have := mul_le_mul_of_nonneg_left hcw hmpos.le; linarith
            rw [hcm] at this; linarith
          · -- `m*w+(t-s) ≤ m*1+(t-s) = m+(t-s) = 1`
            have : m * w + (t - s) ≤ m * 1 + (t - s) := by
              have := mul_le_mul_of_nonneg_left hw1 hmpos.le; linarith
            rw [hmdef] at this; linarith
        · rintro ⟨hvt, hv1⟩
          refine ⟨(v - (t - s)) / m, ⟨?_, ?_⟩, ?_⟩
          · rw [le_div_iff₀ hmpos]
            have hh : m * c = s := hcm
            nlinarith [hh, hvt]
          · rw [div_le_one hmpos, hmdef]; linarith
          · rw [mul_div_cancel₀ _ (ne_of_gt hmpos)]; ring
      -- assemble: `eVar η [0,1] = L·s + L·(1-t) = L·m`, and `L·m < L = eVar δ [0,1]`.
      rw [← hsplit, hpiece1, hpiece2]
      rw [hδsub 0 ⟨le_rfl, by norm_num⟩ s hsm hs0, hδsub t htm 1 ⟨by norm_num, le_rfl⟩ ht1]
      -- `eVar δ [0,1] = ofReal L`
      have hδtot : eVariationOn δ (Icc (0:ℝ) 1) = ENNReal.ofReal L := by
        have := hδsub 0 ⟨le_rfl, by norm_num⟩ 1 ⟨by norm_num, le_rfl⟩ (by norm_num)
        rw [hI3] at this; rw [this]; congr 1; ring
      have hnn1 : 0 ≤ L * (s - 0) := by nlinarith [hLpos, hs0]
      have hnn2 : 0 ≤ L * (1 - t) := by nlinarith [hLpos, ht1]
      rw [hδtot, ← ENNReal.ofReal_add hnn1 hnn2]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by nlinarith [hnn1, hnn2])).mpr
      nlinarith [hLpos, hslt, hs0, ht1]
    -- contradiction with minimality.
    have hcontra : eVariationOn γ₀ (Icc (0 : ℝ) 1) ≤ eVariationOn η (Icc (0 : ℝ) 1) :=
      hmin η hηcont hη0 hη1 hηmem
    rw [hδlen] at hηvar
    exact absurd hcontra (not_le.mpr hηvar)
  have hδinj : InjOn δ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    by_contra hne
    rcases lt_trichotomy s t with h | h | h
    · exact hexcise s hs t ht h hst
    · exact hne h
    · exact hexcise t ht s hs h hst.symm
  -- Final assembly: `δ` is the simple finite-variation arc.
  exact ⟨δ, hδ0p, hδ1q, hδcont, hδne, hδinj, hδmem⟩

/-- **(B) — A rectifiable continuum is arcwise connected by a simple absolutely continuous arc.**

A **compact connected** set `Γ ⊆ ℂ` of **finite** `μH[1]`-length (a *rectifiable continuum*) is a
Peano continuum, hence arcwise connected; any two of its points `p, q` are joined by a **simple**
(injective) Lipschitz — and therefore absolutely continuous — arc `δ : [0,1] → ℂ` lying entirely in
`Γ`, with `δ 0 = p`, `δ 1 = q`.

## Truth and the missing classical ingredient

**TRUE** — this is the **Eilenberg–Harrold / Wazewski** theorem (a continuum of finite linear
measure is a Peano continuum, so **Hahn–Mazurkiewicz** gives arcwise connectedness; loops are
removed to get a simple arc, and arc-length parametrization makes it Lipschitz hence absolutely
continuous).

## Decomposition

The proof now **separates** the two ingredients, proving the analytic half outright:

* the **topological core** — existence of a simple (injective) *finite-variation* arc joining `p`
  and `q` inside `Γ` — is the Mathlib-absent Eilenberg–Harrold / Hahn–Mazurkiewicz content,
  isolated as the single residual `simpleRectifiableArc_of_compact_connected_finite_hausdorff`;
* the **arc-length Lipschitz reparametrization** — turning a simple finite-variation arc into a
  globally Lipschitz simple arc on `[0,1]` with the same endpoints, trace, and injectivity — is
  proved unconditionally in `lipschitz_simpleArc_of_finiteVariation`, using Mathlib's
  `variationOnFromTo` cumulative-variation machinery.

Only the topological core remains a `sorry`. -/
theorem rectifiable_continuum_simple_arc {Γ : Set ℂ}
    (hΓcpt : IsCompact Γ) (hΓconn : IsConnected Γ)
    (hΓfin : (MeasureTheory.Measure.hausdorffMeasure 1 : Measure ℂ) Γ ≠ ∞)
    {p q : ℂ} (hpΓ : p ∈ Γ) (hqΓ : q ∈ Γ) (hpq : p ≠ q) :
    ∃ δ : ℝ → ℂ, δ 0 = p ∧ δ 1 = q ∧ Continuous δ ∧
      (∃ K : ℝ≥0, LipschitzOnWith K δ (Set.uIcc 0 1)) ∧
      Set.InjOn δ (Set.Icc (0 : ℝ) 1) ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, δ τ ∈ Γ := by
  -- Topological core: a simple finite-variation arc `γ : [0,1] → Γ` joining `p` and `q`.
  obtain ⟨γ, hγ0, hγ1, hγcont, hγbv, hγinj, hγmem⟩ :=
    simpleRectifiableArc_of_compact_connected_finite_hausdorff hΓcpt hΓconn hΓfin hpΓ hqΓ hpq
  -- Analytic half: reparametrize `γ` by arc length to a globally Lipschitz simple arc.
  obtain ⟨δ, hδ0, hδ1, hδcont, hδLip, hδinj, hδmem⟩ :=
    lipschitz_simpleArc_of_finiteVariation hγcont hγinj hγbv
  refine ⟨δ, ?_, ?_, hδcont, hδLip, hδinj, ?_⟩
  · rw [hδ0, hγ0]
  · rw [hδ1, hγ1]
  · -- `δ τ ∈ γ '' [0,1] ⊆ Γ`.
    intro τ hτ
    obtain ⟨σ, hσmem, hσeq⟩ := hδmem τ hτ
    rw [← hσeq]; exact hγmem σ hσmem



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


end RhoPotentialWitness

/-! ### The per-density length–area inequality and its atomic cross-bound

For a homeomorphism `f` and an axis rectangle `(a, b) × (s, t)`, every `ρ` admissible for the image
crossing family `Γ` and every `σ` admissible for the image separating family `Γ*` satisfy
`1 ≤ (∫∫ ρ²) · (∫∫ σ²)` (`imageConjugate_lengthArea_pairwise`, **proven** below).  Taking the
infimum over `ρ` then `σ`, this per-pair bound is exactly the conjugate-image reciprocity
`1 ≤ M(Γ) · M(Γ*)` (via the proven `one_le_biInf_mul_biInf'` and the finiteness witnesses
`imageCurveFamily_finiteWitness`).  This is the **easy** direction (Ahlfors, *Conformal Invariants*
Ch. 4; Väisälä §II; Lehto–Virtanen); no conformality or differentiability of `f` is used.

The reduction is fully discharged down to **one** atomic residual, the crossing-principle
cross-bound `1 ≤ ∫∫ ρσ` (`imageConjugate_cross_bound`):

* the final Cauchy–Schwarz step `(∫∫ ρσ ≥ 1) ⟹ (∫∫ ρ²)(∫∫ σ²) ≥ 1` is **proven, axiom-clean**
  (`one_le_energy_mul_energy_of_one_le_lintegral_mul`, Hölder at the conjugate pair `(2, 2)`);
* the cross-bound `1 ≤ ∫∫ ρσ` is **true for every admissible pair** (it genuinely uses *full*
  admissibility against all connecting curves — the weak row/column condition alone is insufficient)
  and is the irreducible content: every crossing curve meets every separating curve in a topological
  square, paired by a planar co-area argument.  Mathlib-absent (no Jordan-separation / topological
  crossing lemma; no co-area for the curved image foliation of a mere homeomorphism — the only
  change-of-variables tool, `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, needs an injective
  differentiable map with a known differential).  A geodesic-ρ-potential route was attempted and
  retired (its sharp eikonal `‖∇u‖ ≤ ρ` is false for finite-energy `ρ`; planar Kakeya/Nikodym —
  see `imageConjugate_cross_bound`).  The kept Sperner / Poincaré–Miranda crossing machinery
  (`RectangleCrossing`), Eilenberg–Harrold simple-arc, and the proven `eilenberg_coarea_grad_le`
  are the building blocks for the next phase. -/

/-- **The crossing-principle cross-bound (the atomic reciprocity residual).**

For a homeomorphism `f`, an admissible `ρ` for the image **crossing** family of an axis rectangle
and an admissible `σ` for the conjugate image **separating** family,

  `1 ≤ ∫∫ ρ · σ`.

This is the genuine topological/measure content of conformal-modulus reciprocity (Beurling; Ahlfors,
*Conformal Invariants* Ch. 4; Väisälä §II): every crossing curve meets every separating curve in a
topological square, and the co-area/Fubini pairing over the image foliation delivers the bound.

**Status.** **Discharged by reduction** to the planar Loewner reciprocity workstream
(`QC/LoewnerReciprocity.lean`). The body is a one-line call into
`loewner_image_cross_bound_axisRect`, whose signature matches this theorem exactly. The
genuine Beurling–Ahlfors content has been factored into two named architectural sorries
in `LoewnerReciprocity.lean`: the affine atom `loewner_affine_cross_bound_full`
(`f = id`, axis rectangle, full AC-curve-family admissibility — closeable via the
truncation + Beurling-ρ-potential + L²-limit Lipschitz-eikonal pipeline using the proved
Sobolev co-area engine `eilenberg_coarea_grad_le`) and the source ↔ image reduction
`loewner_image_cross_bound_axisRect` itself (using `rectangle_crossing` + the
`IsQCGeometric f K` modulus bound). Filling those two sorries is multi-session
research engineering; closure of *this* theorem now bottoms out at the named Loewner
residuals rather than at a one-off sorry in this file.

The classical mathematics: there is no Jordan-separation / topological-square crossing
lemma in Mathlib, and no planar co-area for the curved image foliation of a *mere*
homeomorphism (the only Mathlib change-of-variables tool needs an injective differentiable
map with a known differential, not a level-set foliation). The kept Sperner /
Poincaré–Miranda crossing machinery (`Analysis/RectangleCrossing.lean`'s
`rectangle_crossing`), the Eilenberg–Harrold simple-arc, and the proved
`eilenberg_coarea_grad_le` (`Analysis/Sobolev/Coarea/Assembly.lean`) are the building
blocks the Loewner workstream uses.

A *geodesic ρ-potential* route to this bound was attempted and **retired as unsound for
the sharp eikonal**: the cheap-connector `‖∇u‖ ≤ ρ(z)` is FALSE for finite-energy `ρ`
(planar Kakeya/Nikodym — a thin heavy transversal "wall", invisible to small
ball-averages at `z` yet crossed by every fan/detour path at the macroscopic scale
`d = ‖y − z‖`, forcing cost `(ρ(z) + Θ(1)·ε)·d` with a dimensional dilution factor
`≥ 9π/8 > 1`). The conclusion still holds (such a wall makes `∫∫ ρ²` large), but only via
the energy/crossing duality, not a potential. The Beurling potential approach in
`loewner_affine_cross_bound_full` is constrained to *bounded* `ρ_n = min(ρ, n)` (where
the eikonal holds) plus an admissibility-preserving renormalization and an L² limit
passage — this finesses the Kakeya counterexample. -/
theorem imageConjugate_cross_bound {f : ℂ → ℂ} {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    1 ≤ ∫⁻ z, ρ z * σ z :=
  -- Discharged by the planar Loewner reciprocity workstream
  -- (`QC/LoewnerReciprocity.lean`); the genuine Beurling–Ahlfors content lives in
  -- `loewner_affine_cross_bound_full` (the affine atom) and the source ↔ image
  -- reduction is `loewner_image_cross_bound_axisRect`. The signatures match exactly
  -- and the call is one-to-one.
  loewner_image_cross_bound_axisRect hf hfqc hab hst hρ hσ

/-- **The length–area cross-inequality (conformal-modulus reciprocity, energy form).**

`1 ≤ (∫∫ ρ²) · (∫∫ σ²)` for an admissible crossing `ρ` and separating `σ` of the conjugate image
families.  **Proven** from the crossing-principle cross-bound `imageConjugate_cross_bound`
(`1 ≤ ∫∫ ρσ`) via the Cauchy–Schwarz step `one_le_energy_mul_energy_of_one_le_lintegral_mul`. -/
theorem imageConjugate_lengthArea_pairwise {f : ℂ → ℂ} {Kqc : ℝ} (hf : IsHomeomorph f)
    (hfqc : IsQCGeometric f Kqc)
    {a b s t : ℝ} (hab : a < b) (hst : s < t) {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) :=
  one_le_energy_mul_energy_of_one_le_lintegral_mul hρ.1 hσ.1
    (imageConjugate_cross_bound hf hfqc hab hst hρ hσ)

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
  -- The pairwise length–area bound is needed only for finite-energy densities; the finite-energy
  -- guard `∫⁻ ρ² ≠ ⊤` is exactly the hypothesis `imageConjugate_lengthArea_pairwise` consumes.
  have hpair : ∀ ρ ∈ {ρ : ℂ → ℝ≥0∞ |
        IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f)},
      (∫⁻ z, (ρ z) ^ 2) ≠ ⊤ → ∀ σ ∈ {σ : ℂ → ℝ≥0∞ |
        IsAdmissibleDensity σ ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)},
      (∫⁻ z, (σ z) ^ 2) ≠ ⊤ → 1 ≤ (∫⁻ z, (ρ z) ^ 2) * (∫⁻ z, (σ z) ^ 2) :=
    fun ρ hρ _ σ hσ _ => imageConjugate_lengthArea_pairwise hf hfqc hab hst hρ hσ
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

end RiemannDynamics
