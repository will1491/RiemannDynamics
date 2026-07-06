/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.MRMT.NeumannSeries

/-!
# The smooth-case principal solution and the Ahlfors–Bers endgame

The measurable Riemann mapping theorem is proved by first solving the Beltrami
equation for a **smooth, compactly supported** coefficient — where the principal
solution can be exhibited as an explicit `C¹` diffeomorphism through the
exponential representation `F = id + P(μ·e^σ)`, `∂F = e^σ` — and then passing to
a measurable coefficient by mollification, using the Ahlfors–Bers stability and
two-sided Hölder estimates to carry injectivity and surjectivity to the limit
(Astala–Iwaniec–Martin §§5.2–5.3, Ahlfors–Bers 1960).

This file records the statements of that route; the proofs are the later wave.

* **Smooth Calderón–Zygmund calculus** — on `C∞₀` data the Beurling transform is
  `S u = P(∂u)` (`beurling_eq_cauchyTransform_dz`, the companion of the proved
  bridge `T = ∂ ∘ P`), and both `P` and `S` preserve smoothness
  (`contDiff_cauchyTransform`, `contDiff_beurling`).
* **`C¹` criterion** — a continuous function with continuous weak gradient is
  genuinely `C¹` with the weak gradient as its differential
  (`contDiffOne_of_continuous_hasWeakGradient`).
* **Smooth fixed point** — for smooth data the `Lᵖ` fixed point of
  `φ ↦ μ·Sφ + g` is continuous with continuous Beurling image and satisfies the
  equation pointwise (`exists_continuous_fixedPoint_beltrami_of_contDiff`,
  the regularity content of AIM Lemma 5.2.1/Theorem 5.2.2).
* **The smooth principal solution** — for a smooth compactly supported
  coefficient the principal solution is `C¹` with everywhere-positive Jacobian
  and nonvanishing `∂f` (`exists_contDiffOne_principalSolution`, AIM
  Theorem 5.2.3), and is a homeomorphism of the plane
  (`isHomeomorph_of_contDiffOne_principalSolution`, AIM Theorem 5.2.4).
* **The inverse solution** — the inverse of the smooth-case principal solution
  is the principal solution of the explicit coefficient
  `ν = −(μ∘g)·(∂f∘g)/conj(∂f∘g)`, of no larger dilatation and compactly
  supported in the image of `supp μ`
  (`IsPrincipalSolution.inverse_principalSolution_of_contDiff`, Ahlfors–Bers
  Lemma 11).
* **The Ahlfors–Bers endgame** — the uniform potential estimates
  (`norm_cauchyTransform_le_of_memLp_support`,
  `cauchyTransform_sub_le_holder_uniform`, `isPrincipalSolution_uniform_image_bound`),
  the resolvent stability of the fixed-point field
  (`lp_fixedPoint_beltrami_stability`, AIM Lemma 5.3.1), locally uniform
  convergence of principal solutions under a.e. convergence of coefficients
  (`isPrincipalSolution_tendstoUniformly_of_ae_tendsto`, AIM Theorem 5.3.2),
  the two-sided Hölder inequality with constants uniform over the smooth family
  (`isPrincipalSolution_two_sided_holder`, Ahlfors–Bers Lemma 8 — the estimate
  that forces injectivity of the measurable-case limit), and mollification of a
  Beltrami coefficient (`exists_contDiff_mollification_beltrami`).
-/

open MeasureTheory Complex Filter
open scoped ContDiff ENNReal NNReal Topology

namespace RiemannDynamics

/-! ## Smooth Calderón–Zygmund calculus -/

/-- **`S = P ∘ ∂` on smooth data.** For a smooth compactly supported `u` the
Beurling transform is the Cauchy transform of the holomorphic Wirtinger
derivative: `S u = P(∂u)`. Companion of the proved bridge
`beurling_eq_dz_cauchyTransform` (`S u = ∂(P u)`): both sides are continuous,
vanish at infinity, and have the same `∂̄` (namely `∂u`, by Cauchy–Pompeiu and
the commutation of `∂̄` with `P`), so the difference is entire and vanishes by
Liouville. -/
theorem beurling_eq_cauchyTransform_dz {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (z : ℂ) :
    beurling u z = cauchyTransform (fun ζ => dz u ζ) z := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast le_top)
  -- Both sides are `-(1/π)` times an integral: the Beurling side is the
  -- principal-value limit of the truncated singular integrals, and the
  -- extracted Tendsto `czOperator_beurling_tendsto_smooth` identifies that
  -- limit with the Cauchy-transform integral of `∂u`.
  rw [beurling, cauchyTransform]
  congr 1
  refine Filter.Tendsto.limUnder_eq ?_
  have hcz : ∀ r : ℝ, czOperator (fun a b => (a - b) ^ (-2 : ℤ)) r u z
      = czOperator beurlingKernel r u z := fun r => rfl
  simpa only [hcz] using czOperator_beurling_tendsto_smooth hu1 huc z

/-- **The Cauchy transform preserves smoothness.** For smooth compactly
supported `u` the potential `P u` is smooth: `P u` is the convolution of `u`
with the locally integrable kernel `-1/(π·)`, so all derivatives fall on `u`
(`HasCompactSupport.hasFDerivAt_convolution_left`, iterated). -/
theorem contDiff_cauchyTransform {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    ContDiff ℝ ∞ (cauchyTransform u) := by
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ with hL
  set k : ℂ → ℂ := fun w => -w⁻¹ with hk
  -- The kernel `-w⁻¹` is locally integrable: in polar coordinates the Jacobian
  -- factor `r` cancels the singularity `r⁻¹`, leaving a finite box integral.
  have hk_loc : LocallyIntegrable k volume := by
    rw [hk]
    apply LocallyIntegrable.neg
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
    apply MeasureTheory.IntegrableOn.mono_set _ hR₀
    rw [IntegrableOn]
    refine ⟨measurable_inv.aestronglyMeasurable.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_indicator measurableSet_closedBall,
      ← Complex.lintegral_comp_polarCoord_symm]
    set box : ℝ × ℝ → ENNReal :=
      (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun _ => (1 : ENNReal)) with hbox
    have hbound : ∀ q ∈ polarCoord.target,
        ENNReal.ofReal q.1 • (Metric.closedBall (0 : ℂ) R₀).indicator
          (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q) ≤ box q := by
      intro q hq
      simp only [hbox]
      rw [polarCoord_target, Set.mem_prod] at hq
      obtain ⟨hq1, hq2⟩ := hq
      simp only [Set.mem_Ioi] at hq1
      by_cases hmem : Complex.polarCoord.symm q ∈ Metric.closedBall (0 : ℂ) R₀
      · rw [Set.indicator_of_mem hmem]
        have hnorm : ‖Complex.polarCoord.symm q‖ = q.1 := by
          rw [Complex.norm_polarCoord_symm, abs_of_pos hq1]
        have hsymm_ne : Complex.polarCoord.symm q ≠ 0 := by
          rw [← norm_ne_zero_iff, hnorm]; exact ne_of_gt hq1
        rw [enorm_inv hsymm_ne]
        have henorm : ‖Complex.polarCoord.symm q‖ₑ = ENNReal.ofReal q.1 := by
          rw [← ofReal_norm_eq_enorm, hnorm]
        rw [henorm, smul_eq_mul,
          ENNReal.mul_inv_cancel
            (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq1)
            ENNReal.ofReal_lt_top.ne]
        have hqR : q.1 ≤ R₀ := by
          rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hmem; exact hmem
        rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hq1, hqR⟩, hq2⟩)]
      · rw [Set.indicator_of_notMem hmem]; simp
    calc
      ∫⁻ q in polarCoord.target, ENNReal.ofReal q.1 •
          (Metric.closedBall (0 : ℂ) R₀).indicator
            (fun w : ℂ => ‖w⁻¹‖ₑ) (Complex.polarCoord.symm q)
          ≤ ∫⁻ q in polarCoord.target, box q :=
            setLIntegral_mono (measurable_const.indicator
              (measurableSet_Ioc.prod measurableSet_Ioo)) hbound
      _ ≤ ∫⁻ q, box q := setLIntegral_le_lintegral _ _
      _ = volume (Set.Ioc (0 : ℝ) R₀ ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
            rw [hbox, lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
            simp
      _ < ⊤ := by
            rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_Ioc,
              Real.volume_Ioo]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- `P u` is `-(1/π)` times the convolution of `u` with the kernel.
  have hCT : cauchyTransform u
      = fun w => (-(1 / (Real.pi : ℂ))) • (MeasureTheory.convolution u k L volume) w := by
    funext w
    rw [cauchyTransform, MeasureTheory.convolution_def, smul_eq_mul]
    congr 1
    apply integral_congr_ae (ae_of_all _ fun ζ => ?_)
    rw [hL, ContinuousLinearMap.mul_apply']
    change u ζ / (ζ - w) = u ζ * -(w - ζ)⁻¹
    have hflip : -(w - ζ)⁻¹ = (ζ - w)⁻¹ := by rw [← neg_sub ζ w, inv_neg, neg_neg]
    rw [hflip, div_eq_mul_inv]
  rw [hCT]
  exact (huc.contDiff_convolution_left L hu hk_loc).const_smul _

/-- **The Beurling transform preserves smoothness.** For smooth compactly
supported `u` the singular integral `S u` is smooth: by
`beurling_eq_cauchyTransform_dz`, `S u = P(∂u)` with `∂u` smooth and compactly
supported, and `P` preserves smoothness (`contDiff_cauchyTransform`). -/
theorem contDiff_beurling {u : ℂ → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    ContDiff ℝ ∞ (beurling u) := by
  -- `S u = P(∂u)` pointwise.
  have hbeq : beurling u = cauchyTransform (fun ζ => dz u ζ) := by
    funext z; exact beurling_eq_cauchyTransform_dz hu huc z
  -- `∂u` is a fixed continuous-linear expression in `fderiv ℝ u`.
  have hcomp : (fun ζ => dz u ζ)
      = (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
        ∘ (fun ζ => fderiv ℝ u ζ) := by
    funext ζ; rfl
  -- Smoothness of `∂u`.
  have hfderiv_cinf : ContDiff ℝ ∞ (fun ζ => fderiv ℝ u ζ) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hΦ_cd : ContDiff ℝ ∞
      (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I)) := by
    have hΦ_lin : (fun D : ℂ →L[ℝ] ℂ => (1 / 2 : ℂ) * (D 1 - Complex.I * D Complex.I))
        = (fun D : ℂ →L[ℝ] ℂ =>
            (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) D
              - Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I D)) := by
      funext D; simp [ContinuousLinearMap.apply_apply, smul_eq_mul]
    rw [hΦ_lin]
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff).sub
      ((ContinuousLinearMap.apply ℝ ℂ Complex.I).contDiff.const_smul Complex.I)).const_smul _
  have hdzu_cinf : ContDiff ℝ ∞ (fun ζ => dz u ζ) := by
    rw [hcomp]; exact hΦ_cd.comp hfderiv_cinf
  -- Compact support of `∂u`.
  have hdzu_cs : HasCompactSupport (fun ζ => dz u ζ) := by
    have hfderiv_cs : HasCompactSupport (fun ζ => fderiv ℝ u ζ) := huc.fderiv (𝕜 := ℝ)
    rw [hcomp]; exact hfderiv_cs.comp_left (by simp)
  -- Conclude via the smoothness of the Cauchy transform.
  rw [hbeq]
  exact contDiff_cauchyTransform hdzu_cinf hdzu_cs

/-! ## The `C¹` criterion from continuous weak gradients -/

/-- **Continuous weak gradient ⇒ `C¹`.** A continuous function on `ℂ` whose
weak gradient components are continuous is continuously differentiable, and the
weak partials are the genuine directional derivatives everywhere. Classical
mollification argument: `f ∗ φ_ε → f` locally uniformly and
`∂(f ∗ φ_ε) = gx ∗ φ_ε → gx` locally uniformly, so the limit `f` is `C¹` with
the asserted differential. -/
theorem contDiffOne_of_continuous_hasWeakGradient {f gx gy : ℂ → ℂ}
    (hf : Continuous f) (hgrad : HasWeakGradient gx gy f Set.univ)
    (hgx : Continuous gx) (hgy : Continuous gy) :
    ContDiff ℝ 1 f ∧
      ∀ z : ℂ, (fderiv ℝ f z) 1 = gx z ∧ (fderiv ℝ f z) Complex.I = gy z := by
  sorry

/-! ## The smooth fixed point -/

/-- **Regularity of the Beltrami fixed point for smooth data** (AIM
Lemma 5.2.1 / Theorem 5.2.2, the regularity content). For a smooth compactly
supported multiplier `μ` and datum `g`, and contraction data at an exponent
`p > 2`, the fixed-point equation `φ = μ·Sφ + g` has a solution `φ ∈ Lᵖ`,
vanishing outside the common support ball, which is **continuous with
continuous Beurling transform** and satisfies the equation **pointwise**.
Internally: the `Lᵖ` fixed point of the proved `exists_lp_fixedPoint_beltrami`
is `W^{1,p}` (differentiate the equation: `∂φ` solves the same-multiplier
equation with datum `∂μ·Sφ + ∂g`), hence Hölder continuous by the Morrey
embedding (`Analysis/Sobolev/Morrey/OscillationBound.lean`), and `S` preserves
the Hölder class of compactly supported fields; continuity of both sides
upgrades the a.e. equation to a pointwise one. -/
theorem exists_continuous_fixedPoint_beltrami_of_contDiff {μ g : ℂ → ℂ}
    {p : ℝ≥0∞} {C R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hμs : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hcontr : (eLpNormEssSup μ volume).toReal * C < 1)
    (hsupp : ∀ z : ℂ, R < ‖z‖ → μ z = 0 ∧ g z = 0) :
    ∃ φ : ℂ → ℂ, MemLp φ p volume ∧ (∀ z : ℂ, R < ‖z‖ → φ z = 0) ∧
      Continuous φ ∧ Continuous (beurling φ) ∧
      ∀ z : ℂ, φ z = μ z * beurling φ z + g z := by
  sorry

/-! ## The smooth principal solution -/

/-- **The smooth-case principal solution is a nondegenerate `C¹` map** (AIM
Theorem 5.2.3). For a Beltrami coefficient with smooth compactly supported `μ`
there is a principal solution `f` of class `C¹` whose Jacobian is positive at
**every** point and whose `∂`-derivative never vanishes. Exponential
representation: solve the auxiliary equation `ω = μ·Sω + ∂μ` (the fixed point
of `exists_continuous_fixedPoint_beltrami_of_contDiff` with datum `∂μ`), set
`σ = P ω` and `F = id + P(μ·e^σ)`; the identity `e^σ − 1 = S(μ·e^σ)` gives
`∂F = e^σ ≠ 0`, `∂̄F = μ·e^σ`, hence `J(z, F) = |e^σ|²·(1 − |μ|²) > 0`, and
`F` is itself a principal solution with field `h = μ·e^σ`. -/
theorem exists_contDiffOne_principalSolution (b : BeltramiCoeff)
    (hμs : ContDiff ℝ ∞ b.μ) (hμc : HasCompactSupport b.μ) :
    ∃ f : ℂ → ℂ, IsPrincipalSolution b f ∧ ContDiff ℝ 1 f ∧
      (∀ z : ℂ, 0 < (fderiv ℝ f z).det) ∧ ∀ z : ℂ, dz f z ≠ 0 := by
  sorry

/-- **A nondegenerate `C¹` principal solution is a homeomorphism of the plane**
(AIM Theorem 5.2.4). Everywhere-positive Jacobian makes `f` a local
homeomorphism (inverse function theorem); the principal normalization makes it
proper (`f − id → 0` at infinity) and holomorphic and injective near infinity
(off the support ball of its field, `f = id + P h` is holomorphic with Laurent
expansion `z + O(1/z)`); the fiber-count function of a proper local
homeomorphism of the plane is locally constant, and it equals `1` near
infinity, so `f` is a global homeomorphism. -/
theorem isHomeomorph_of_contDiffOne_principalSolution {b : BeltramiCoeff}
    {f : ℂ → ℂ} (hf : IsPrincipalSolution b f) (hf1 : ContDiff ℝ 1 f)
    (hdet : ∀ z : ℂ, 0 < (fderiv ℝ f z).det) :
    IsHomeomorph f := by
  sorry

/-- **The inverse of the smooth-case principal solution is a principal
solution** (Ahlfors–Bers Lemma 11). If `f` is a `C¹` homeomorphic principal
solution for a smooth compactly supported coefficient, its inverse
`g = f⁻¹` is the principal solution of the explicit coefficient

`ν(w) = −μ(g w)·∂f(g w) / conj (∂f(g w))`

(chain rule for `C¹` diffeomorphisms: `∂g = conj(∂f)/J ∘ g`,
`∂̄g = −∂̄f/J ∘ g`). Since `|ν| = |μ ∘ g|` pointwise, the dilatation does not
grow, and `ν` is supported in the compact image `f '' supp μ` — the two
uniformities the measurable-case endgame consumes. -/
theorem IsPrincipalSolution.inverse_principalSolution_of_contDiff
    {b : BeltramiCoeff} {f : ℂ → ℂ} (hf : IsPrincipalSolution b f)
    (hμs : ContDiff ℝ ∞ b.μ) (hμc : HasCompactSupport b.μ)
    (hf1 : ContDiff ℝ 1 f) (hdet : ∀ z : ℂ, 0 < (fderiv ℝ f z).det)
    (hhom : IsHomeomorph f) :
    ∃ ν : BeltramiCoeff,
      (∀ w : ℂ, ν.μ w = -(b.μ ((hhom.homeomorph f).symm w)
          * dz f ((hhom.homeomorph f).symm w)
          / (starRingEnd ℂ) (dz f ((hhom.homeomorph f).symm w)))) ∧
      eLpNormEssSup ν.μ volume ≤ eLpNormEssSup b.μ volume ∧
      HasCompactSupport ν.μ ∧
      (∀ w : ℂ, ν.μ w ≠ 0 → w ∈ f '' tsupport b.μ) ∧
      IsPrincipalSolution ν ⇑(hhom.homeomorph f).symm := by
  sorry

/-! ## Uniform potential estimates -/

/-- **Uniform sup bound for the Cauchy transform of compactly vanishing `Lᵖ`
fields** (`p > 2`): a constant `C = C(p, R)` with
`‖P h‖_∞ ≤ C·‖h‖ₚ` for every field `h ∈ Lᵖ` vanishing outside the ball of
radius `R`. Hölder's inequality against the kernel: the conjugate exponent
satisfies `q < 2`, so `sup_z ∫_{B_R} |ζ − z|^{-q} dA < ∞`. The constant is
uniform over the family — the source of every uniformity in the
Ahlfors–Bers limit argument. -/
theorem norm_cauchyTransform_le_of_memLp_support {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ → ℂ, MemLp h p volume →
      (∀ z : ℂ, R < ‖z‖ → h z = 0) →
      ∀ z : ℂ, ‖cauchyTransform h z‖ ≤ C * (eLpNorm h p volume).toReal := by
  sorry

/-- **Uniform Hölder bound for the Cauchy transform** — the family-uniform form
of the proved `cauchyTransform_sub_le_holder`: a constant `C = C(p, R)` with

`‖P h z₁ − P h z₂‖ ≤ C·‖h‖ₚ·‖z₁ − z₂‖^(1−2/p)`

for **every** field `h ∈ Lᵖ` (`p > 2`) vanishing outside the ball of radius
`R`. The difference kernel scales: `∫ |1/(ζ−z₁) − 1/(ζ−z₂)|^q dA =
c(q)·‖z₁ − z₂‖^(2−q)`, so the constant depends only on the exponent data. -/
theorem cauchyTransform_sub_le_holder_uniform {p : ℝ≥0∞} {R : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ → ℂ, MemLp h p volume →
      (∀ z : ℂ, R < ‖z‖ → h z = 0) →
      ∀ z₁ z₂ : ℂ, ‖cauchyTransform h z₁ - cauchyTransform h z₂‖
        ≤ C * (eLpNorm h p volume).toReal * ‖z₁ - z₂‖ ^ (1 - 2 / p.toReal) := by
  sorry

/-- **Uniform image bound for principal solutions.** Over all coefficients of
dilatation at most `k < 1` supported in the ball of radius `R`, the principal
solutions displace points by a bounded amount: there is `R' = R'(k, R)` with
`‖f z‖ ≤ R'` whenever `‖z‖ ≤ R`. Choose `p = p(k) > 2` with the Neumann
contraction (`exists_p_gt_two_beurling_contraction`); the canonical field has
`‖h‖ₚ ≤ (1 − kC)⁻¹·‖μ‖ₚ ≤ (1 − kC)⁻¹·k·|B_R|^{1/p}`, and
`norm_cauchyTransform_le_of_memLp_support` bounds the displacement `‖P h‖_∞`.
Needed to place the supports of the inverse coefficients
(`IsPrincipalSolution.inverse_principalSolution_of_contDiff`) in a uniform
ball. -/
theorem isPrincipalSolution_uniform_image_bound {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ R' : ℝ, R ≤ R' ∧ ∀ (b : BeltramiCoeff) (f : ℂ → ℂ),
      eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      IsPrincipalSolution b f →
      ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ R' := by
  sorry

/-! ## The Ahlfors–Bers endgame: stability, convergence, injectivity -/

/-- **Resolvent stability of the Beltrami fixed point** (AIM Lemma 5.3.1). Two
fixed points `hᵢ = μᵢ·S hᵢ + μᵢ` with common contraction data satisfy the
resolvent identity `h₁ − h₂ = μ₁·S(h₁ − h₂) + (μ₁ − μ₂)·(1 + S h₂)`, so the
Neumann bound controls their distance by the coefficient difference:

`‖h₁ − h₂‖ₚ ≤ (1 − kC)⁻¹·‖(μ₁ − μ₂)·(1 + S h₂)‖ₚ`.

With `μₙ → μ` a.e., uniformly bounded and commonly supported, dominated
convergence sends the right side to `0` — the quantitative engine of the
mollification limit. -/
theorem lp_fixedPoint_beltrami_stability {μ₁ μ₂ h₁ h₂ : ℂ → ℂ}
    {p : ℝ≥0∞} {C k : ℝ}
    (hp : 2 < p) (hp' : p ≠ ⊤)
    (hμ₁ : Measurable μ₁) (hμ₂ : Measurable μ₂)
    (hk₁ : eLpNormEssSup μ₁ volume ≤ ENNReal.ofReal k)
    (hk₂ : eLpNormEssSup μ₂ volume ≤ ENNReal.ofReal k)
    (hCb : IsCalderonZygmundBound beurling p C)
    (hk0 : 0 ≤ k) (hcontr : k * C < 1)
    (hh₁ : MemLp h₁ p volume) (hh₂ : MemLp h₂ p volume)
    (heq₁ : h₁ =ᵐ[volume] fun z => μ₁ z * beurling h₁ z + μ₁ z)
    (heq₂ : h₂ =ᵐ[volume] fun z => μ₂ z * beurling h₂ z + μ₂ z) :
    eLpNorm (fun z => h₁ z - h₂ z) p volume
      ≤ ENNReal.ofReal ((1 - k * C)⁻¹)
        * eLpNorm (fun z => (μ₁ z - μ₂ z) * (1 + beurling h₂ z)) p volume := by
  sorry

/-- **Principal solutions converge uniformly under a.e. convergence of the
coefficients** (AIM Theorem 5.3.2, convergence half). For coefficients of
dilatation at most `k < 1` supported in a common ball, a.e. convergence
`μₙ → μ` forces the principal solutions to converge uniformly on all of `ℂ`:
the fixed-point fields converge in `Lᵖ` (`lp_fixedPoint_beltrami_stability` +
dominated convergence), and `fₙ − f = P(hₙ − h)` is controlled in sup norm by
`norm_cauchyTransform_le_of_memLp_support`. -/
theorem isPrincipalSolution_tendstoUniformly_of_ae_tendsto
    {bs : ℕ → BeltramiCoeff} {b : BeltramiCoeff}
    {fs : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1)
    (hbound : ∀ n, eLpNormEssSup (bs n).μ volume ≤ ENNReal.ofReal k)
    (hbound' : eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k)
    (hsupp : ∀ n, ∀ z : ℂ, R < ‖z‖ → (bs n).μ z = 0)
    (hsupp' : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0)
    (htend : ∀ᵐ z, Tendsto (fun n => (bs n).μ z) atTop (𝓝 (b.μ z)))
    (hfs : ∀ n, IsPrincipalSolution (bs n) (fs n))
    (hf : IsPrincipalSolution b f) :
    TendstoUniformly fs f atTop := by
  sorry

/-- **The two-sided Hölder inequality, uniformly over the smooth family**
(Ahlfors–Bers Lemma 8). For every dilatation bound `k < 1` and support radius
`R` there are constants `c` and `α > 0` such that **every** principal solution
of a smooth compactly supported coefficient within those bounds satisfies

`‖z₁ − z₂‖ ≤ ‖f z₁ − f z₂‖ + c·‖f z₁ − f z₂‖^α` for all `z₁ z₂`.

Apply the inverse-solution package
(`IsPrincipalSolution.inverse_principalSolution_of_contDiff`): the inverse
`g = id + P h'` has field norm `‖h'‖ₚ` bounded by `k`, the uniform image ball
(`isPrincipalSolution_uniform_image_bound`), and the Neumann bound, so the
uniform Hölder estimate `cauchyTransform_sub_le_holder_uniform` at
`wᵢ = f zᵢ` gives `‖z₁ − z₂‖ − ‖w₁ − w₂‖ ≤ ‖P h' w₁ − P h' w₂‖ ≤
c·‖w₁ − w₂‖^α`. Since the constants survive the mollification limit, this
inequality is what forces the measurable-case principal solution to be
injective. -/
theorem isPrincipalSolution_two_sided_holder {k R : ℝ}
    (hk0 : 0 ≤ k) (hk : k < 1) :
    ∃ c α : ℝ, 0 ≤ c ∧ 0 < α ∧ ∀ (b : BeltramiCoeff) (f : ℂ → ℂ),
      ContDiff ℝ ∞ b.μ → HasCompactSupport b.μ →
      eLpNormEssSup b.μ volume ≤ ENNReal.ofReal k →
      (∀ z : ℂ, R < ‖z‖ → b.μ z = 0) →
      IsPrincipalSolution b f →
      ∀ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤ ‖f z₁ - f z₂‖ + c * ‖f z₁ - f z₂‖ ^ α := by
  sorry

/-- **Mollification of a Beltrami coefficient.** Every compactly vanishing
Beltrami coefficient is the a.e. limit of smooth compactly supported
coefficients of no larger dilatation, supported in a slightly larger ball:
convolve with a mollifier at scales `εₙ → 0` — the convolution is smooth, its
modulus is bounded by the essential supremum of `|μ|` everywhere, its support
lies in `supp μ + B(εₙ)`, and it converges at every Lebesgue point of `μ`. -/
theorem exists_contDiff_mollification_beltrami (b : BeltramiCoeff) {R : ℝ}
    (hsupp : ∀ z : ℂ, R < ‖z‖ → b.μ z = 0) :
    ∃ bs : ℕ → BeltramiCoeff,
      (∀ n, ContDiff ℝ ∞ (bs n).μ) ∧ (∀ n, HasCompactSupport (bs n).μ) ∧
      (∀ n, eLpNormEssSup (bs n).μ volume ≤ eLpNormEssSup b.μ volume) ∧
      (∀ n, ∀ z : ℂ, R + 1 < ‖z‖ → (bs n).μ z = 0) ∧
      ∀ᵐ z, Tendsto (fun n => (bs n).μ z) atTop (𝓝 (b.μ z)) := by
  sorry

end RiemannDynamics
