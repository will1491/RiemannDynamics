import RiemannDynamics.Teichmuller.QuadraticDifferential.FlatMetric

/-!
# The horizontal flow and the Reich–Strebel main inequality

Away from its zeros a quadratic differential admits local natural charts: a holomorphic
primitive of a local branch of `√q`, in which `q` is the constant `1` and the horizontal
foliation is the family of horizontal lines. Translation in natural-chart time defines the
horizontal flow almost everywhere; its leaves avoid the zeros and the boundary for almost
every start point, and the flow preserves the area measure `|q| dA`.

Averaging over the flow yields the **Reich–Strebel main inequality**: for a boundary-trivial
equivariant quasiconformal self-map `h` of the upper half plane, each horizontal leaf
segment of time `T` is displaced by a uniformly bounded flat distance, so the image curve
deposits horizontal variation at least `T − 2C`; integrating over a fundamental domain,
applying Cauchy–Schwarz per leaf, and changing variables through `h` produces the
quadratic-form bound on `‖q‖₁` and lets `T → ∞`.

* `exists_natural_chart` — local natural charts at nonzero points.
* `reich_strebel_main_inequality` — the main inequality.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Local natural charts**: at a point where a holomorphic function does not vanish
there is a disc on which some holomorphic injective `Φ` satisfies `(Φ')² = q`; in the
chart `Φ` the differential is the constant `1`. -/
theorem exists_natural_chart {q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hq : DifferentiableOn ℂ q U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hq0 : q z₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ U ∧ ∃ Φ : ℂ → ℂ,
      DifferentiableOn ℂ Φ (Metric.ball z₀ r) ∧ Set.InjOn Φ (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, deriv Φ z ^ 2 = q z := by
  have hpos : (0 : ℝ) < ‖q z₀‖ := norm_pos_iff.mpr hq0
  have hqc : ContinuousAt q z₀ := hq.continuousOn.continuousAt (hU.mem_nhds hz₀)
  have hmem : q ⁻¹' Metric.ball (q z₀) ‖q z₀‖ ∩ U ∈ 𝓝 z₀ :=
    Filter.inter_mem (hqc (Metric.ball_mem_nhds _ hpos)) (hU.mem_nhds hz₀)
  obtain ⟨r₁, hr₁, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hsubU : Metric.ball z₀ r₁ ⊆ U := fun z hz => (hsub hz).2
  -- on the ball, `q` does not vanish and `q z / q z₀` lies in the slit plane
  have hne : ∀ z ∈ Metric.ball z₀ r₁, q z ≠ 0 := by
    intro z hz h0
    have hlt : dist (q z) (q z₀) < ‖q z₀‖ := Metric.mem_ball.mp (hsub hz).1
    rw [h0, dist_zero_left] at hlt
    exact lt_irrefl _ hlt
  have hslit : ∀ z ∈ Metric.ball z₀ r₁, q z / q z₀ ∈ Complex.slitPlane := by
    intro z hz
    refine Complex.ball_one_subset_slitPlane (mem_ball_iff_norm.mpr ?_)
    rw [div_sub_one hq0, norm_div, div_lt_one hpos, ← dist_eq_norm]
    exact Metric.mem_ball.mp (hsub hz).1
  -- the local square-root branch
  set g : ℂ → ℂ :=
    fun z => Complex.exp (Complex.log (q z₀) / 2 + Complex.log (q z / q z₀) / 2) with hgdef
  have hg2 : ∀ z ∈ Metric.ball z₀ r₁, g z ^ 2 = q z := by
    intro z hz
    have hd : q z / q z₀ ≠ 0 := div_ne_zero (hne z hz) hq0
    have harith : Complex.log (q z₀) / 2 + Complex.log (q z / q z₀) / 2
        + (Complex.log (q z₀) / 2 + Complex.log (q z / q z₀) / 2)
        = Complex.log (q z₀) + Complex.log (q z / q z₀) := by ring
    rw [hgdef, sq, ← Complex.exp_add, harith, Complex.exp_add, Complex.exp_log hq0,
      Complex.exp_log hd, mul_comm, div_mul_cancel₀ _ hq0]
  have hgd : DifferentiableOn ℂ g (Metric.ball z₀ r₁) := by
    intro z hz
    have hqz : DifferentiableAt ℂ q z := hq.differentiableAt (hU.mem_nhds (hsubU hz))
    exact ((((hqz.div_const _).clog (hslit z hz)).div_const 2).const_add
      _).cexp.differentiableWithinAt
  -- a holomorphic primitive `Φ₀` of `g` on the ball
  obtain ⟨Φ₀, hΦ₀⟩ :=
    (hgd.isExactOn_ball : ∃ F, ∀ z ∈ Metric.ball z₀ r₁, HasDerivAt F (g z) z)
  have hΦd : DifferentiableOn ℂ Φ₀ (Metric.ball z₀ r₁) :=
    fun z hz => (hΦ₀ z hz).differentiableAt.differentiableWithinAt
  have hz₀b : z₀ ∈ Metric.ball z₀ r₁ := Metric.mem_ball_self hr₁
  -- strict differentiability at the center with nonzero derivative
  have han : AnalyticAt ℂ Φ₀ z₀ := hΦd.analyticOnNhd Metric.isOpen_ball z₀ hz₀b
  have hstrict : HasStrictDerivAt Φ₀ (deriv Φ₀ z₀) z₀ :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  have hne0 : deriv Φ₀ z₀ ≠ 0 := by
    rw [(hΦ₀ z₀ hz₀b).deriv]
    exact Complex.exp_ne_zero _
  -- local injectivity via the inverse function theorem
  obtain ⟨ε, hε, hinv⟩ :=
    Metric.eventually_nhds_iff.mp (hstrict.eventually_left_inverse hne0)
  refine ⟨min r₁ ε, lt_min hr₁ hε,
    (Metric.ball_subset_ball (min_le_left _ _)).trans hsubU, Φ₀,
    hΦd.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_, ?_⟩
  · intro x hx y hy hxy
    have hx' : dist x z₀ < ε := (Metric.mem_ball.mp hx).trans_le (min_le_right _ _)
    have hy' : dist y z₀ < ε := (Metric.mem_ball.mp hy).trans_le (min_le_right _ _)
    have hkey := hinv hx'
    rw [hxy, hinv hy'] at hkey
    exact hkey.symm
  · intro z hz
    have hzb : z ∈ Metric.ball z₀ r₁ := Metric.ball_subset_ball (min_le_left _ _) hz
    rw [(hΦ₀ z hzb).deriv]
    exact hg2 z hzb

/-- **The Reich–Strebel main inequality.** Let `Γ` be a cocompact free Fuchsian group,
`q` an automorphic quadratic differential, and `h` an upper-half-plane quasiconformal map
commuting with `Γ` elementwise whose boundary limits are the identity on `ℝ`. Then the
`L¹` mass of `q` is dominated by the integral, over the Dirichlet domain, of
`|q| · ‖1 − μ_h q/|q|‖²/(1 − ‖μ_h‖²)` formed from the Wirtinger quotient of `h`. -/
theorem reich_strebel_main_inequality
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (hbd : ∀ t : ℝ, Filter.Tendsto h (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
      (nhds (t : ℂ)))
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z)) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  sorry

/-- The **Reich–Strebel weight** of `h` against `q` at `z`: the pointwise factor
`‖1 − μ q/|q|‖² / (1 − ‖μ‖²)` formed from the Wirtinger quotient `μ` of `h`. -/
noncomputable def rsWeight (q : ℂ → ℂ) (h : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
      / (1 - ‖wirtingerQuotient h z‖ ^ 2))

/-- The Reich–Strebel weight floored at `(1 − κ)²`: equal to the weight almost
everywhere for a `κ`-quasiconformal `h`, but everywhere positive and finite, so that
it may serve as a Cauchy–Schwarz weight without null-set bookkeeping. -/
noncomputable def rsWeightM (q : ℂ → ℂ) (h : ℂ → ℂ) (κ : ℝ) (z : ℂ) : ℝ≥0∞ :=
  max (rsWeight q h z) (ENNReal.ofReal ((1 - κ) ^ 2))

/-- The branch-free **image pullback** of `q` under `h` in the unit vertical direction
of `q`: with `v² = −1/q` the square of the image of `v` under the real derivative of
`h` carries `q(h z) (Dh v)² = −q(h z) (∂h)² (1 − μ q/|q|)² / q`. -/
noncomputable def rsQ (q : ℂ → ℂ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(q (h z) * dz h z ^ 2 * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2) / q z

/-- The **image vertical-leaf density**: the branch-free horizontal transverse density
`√((|Q| − Re Q)/2)` of the image under `h` of a unit-speed vertical leaf of `q`. -/
noncomputable def rsDensity (q : ℂ → ℂ) (h : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt ((‖rsQ q h z‖ - (rsQ q h z).re) / 2))

/-- The first Cauchy–Schwarz factor: the squared image density divided by the floored
weight. -/
noncomputable def rsU (q : ℂ → ℂ) (h : ℂ → ℂ) (κ : ℝ) (z : ℂ) : ℝ≥0∞ :=
  rsDensity q h z ^ 2 * (rsWeightM q h κ z)⁻¹

/-- Measurability of the Reich–Strebel weight. -/
theorem measurable_rsWeight {q : ℂ → ℂ} (hq : Measurable q) (h : ℂ → ℂ) :
    Measurable (rsWeight q h) := by
  have h1 : Measurable fun z => (fderiv ℝ h z) 1 :=
    (measurable_fderiv ℝ h).apply_continuousLinearMap 1
  have hI : Measurable fun z => (fderiv ℝ h z) Complex.I :=
    (measurable_fderiv ℝ h).apply_continuousLinearMap Complex.I
  have hdz : Measurable (dz h) := by
    unfold dz; exact (measurable_const.mul (h1.sub (measurable_const.mul hI)))
  have hdzbar : Measurable (dzbar h) := by
    unfold dzbar; exact (measurable_const.mul (h1.add (measurable_const.mul hI)))
  have hwq : Measurable (wirtingerQuotient h) := hdzbar.div hdz
  have hθ : Measurable fun z => (q z / (‖q z‖ : ℂ)) :=
    hq.div (Complex.measurable_ofReal.comp hq.norm)
  have hnum : Measurable fun z =>
      ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2 :=
    ((measurable_const.sub (hwq.mul hθ)).norm.pow_const 2)
  have hden : Measurable fun z => 1 - ‖wirtingerQuotient h z‖ ^ 2 :=
    measurable_const.sub (hwq.norm.pow_const 2)
  exact (hnum.div hden).ennreal_ofReal

/-- Measurability of the floored weight. -/
theorem measurable_rsWeightM {q : ℂ → ℂ} (hq : Measurable q) (h : ℂ → ℂ) (κ : ℝ) :
    Measurable (rsWeightM q h κ) :=
  (measurable_rsWeight hq h).max measurable_const

/-- Measurability of the image vertical-leaf density. -/
theorem measurable_rsDensity {q : ℂ → ℂ} (hq : Measurable q) {h : ℂ → ℂ}
    (hh : Measurable h) : Measurable (rsDensity q h) := by
  have h1 : Measurable fun z => (fderiv ℝ h z) 1 :=
    (measurable_fderiv ℝ h).apply_continuousLinearMap 1
  have hI : Measurable fun z => (fderiv ℝ h z) Complex.I :=
    (measurable_fderiv ℝ h).apply_continuousLinearMap Complex.I
  have hdz : Measurable (dz h) := by
    unfold dz; exact (measurable_const.mul (h1.sub (measurable_const.mul hI)))
  have hdzbar : Measurable (dzbar h) := by
    unfold dzbar; exact (measurable_const.mul (h1.add (measurable_const.mul hI)))
  have hwq : Measurable (wirtingerQuotient h) := hdzbar.div hdz
  have hθ : Measurable fun z => (q z / (‖q z‖ : ℂ)) :=
    hq.div (Complex.measurable_ofReal.comp hq.norm)
  have hQ : Measurable (rsQ q h) := by
    unfold rsQ
    exact ((((hq.comp hh).mul (hdz.pow_const 2)).mul
      ((measurable_const.sub (hwq.mul hθ)).pow_const 2)).neg).div hq
  exact (((hQ.norm.sub (Complex.measurable_re.comp hQ)).div_const 2).sqrt).ennreal_ofReal

/-- Measurability of the first Cauchy–Schwarz factor. -/
theorem measurable_rsU {q : ℂ → ℂ} (hq : Measurable q) {h : ℂ → ℂ}
    (hh : Measurable h) (κ : ℝ) : Measurable (rsU q h κ) :=
  ((measurable_rsDensity hq hh).pow_const 2).mul
    (measurable_rsWeightM hq h κ).inv

/-- **Cauchy–Schwarz for square roots**: the integral of the pointwise geometric mean is
dominated by the geometric mean of the integrals. -/
theorem lintegral_sqrt_mul_sqrt_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, f x ^ (1 / 2 : ℝ) * g x ^ (1 / 2 : ℝ) ∂μ
      ≤ (∫⁻ x, f x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ∂μ) ^ (1 / 2 : ℝ) := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (f := fun x => f x ^ (1 / 2 : ℝ)) (g := fun x => g x ^ (1 / 2 : ℝ))
    (hf.pow_const _) (hg.pow_const _)
  simp only [Pi.mul_apply] at hcs
  calc ∫⁻ x, f x ^ (1 / 2 : ℝ) * g x ^ (1 / 2 : ℝ) ∂μ
      ≤ (∫⁻ x, (f x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        * (∫⁻ x, (g x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hcs
    _ = (∫⁻ x, f x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, g x ∂μ) ^ (1 / 2 : ℝ) := by
        congr 2 <;> refine lintegral_congr fun x => ?_ <;>
          rw [← ENNReal.rpow_mul] <;> norm_num

/-- **Weighted Cauchy–Schwarz**: for an everywhere positive finite weight `w`,
`(∫ f)² ≤ (∫ f²/w) (∫ w)`. -/
theorem lintegral_sq_le_weighted {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f w : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hw : AEMeasurable w μ)
    (hw0 : ∀ x, w x ≠ 0) (hwt : ∀ x, w x ≠ ⊤) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 * (w x)⁻¹ ∂μ) * ∫⁻ x, w x ∂μ := by
  have hpt : ∀ x, f x = (f x ^ 2 * (w x)⁻¹) ^ (1 / 2 : ℝ) * w x ^ (1 / 2 : ℝ) := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_natCast (f x) 2, ← ENNReal.rpow_mul, mul_assoc,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.inv_mul_cancel (hw0 x) (hwt x), ENNReal.one_rpow, mul_one]
    norm_num
  have hkey : ∫⁻ x, f x ∂μ
      ≤ (∫⁻ x, f x ^ 2 * (w x)⁻¹ ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, w x ∂μ) ^ (1 / 2 : ℝ) := by
    calc ∫⁻ x, f x ∂μ
        = ∫⁻ x, (f x ^ 2 * (w x)⁻¹) ^ (1 / 2 : ℝ) * w x ^ (1 / 2 : ℝ) ∂μ :=
          lintegral_congr fun x => hpt x
      _ ≤ _ := lintegral_sqrt_mul_sqrt_le ((hf.pow_const _).mul hw.inv) hw
  have hsq := ENNReal.rpow_le_rpow hkey (by norm_num : (0 : ℝ) ≤ 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hsq
  norm_num at hsq
  exact hsq

/-- Division endgame: if `T N ≤ T S + K` for every positive time `T`, with `K` finite,
then `N ≤ S`. -/
theorem le_of_forall_ofReal_mul_le {N S K : ℝ≥0∞} (hK : K ≠ ⊤)
    (h : ∀ T : ℝ, 0 < T → ENNReal.ofReal T * N ≤ ENNReal.ofReal T * S + K) : N ≤ S := by
  rcases eq_top_or_lt_top S with hS | hS
  · exact hS ▸ le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hSt => ?_
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  set T : ℝ := K.toReal / (ε : ℝ) + 1 with hTdef
  have hT : 0 < T := by positivity
  have hT0 : ENNReal.ofReal T ≠ 0 := (ENNReal.ofReal_pos.mpr hT).ne'
  have hdiv : K / ENNReal.ofReal T ≤ (ε : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hT0) (Or.inl ENNReal.ofReal_ne_top)]
    calc K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
      _ ≤ ENNReal.ofReal ((ε : ℝ) * T) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hKT : (ε : ℝ) * T = K.toReal + (ε : ℝ) := by
            rw [hTdef, mul_add, mul_one, mul_div_cancel₀ _ hε'.ne']
          linarith
      _ = (ε : ℝ≥0∞) * ENNReal.ofReal T := by
          rw [ENNReal.ofReal_mul hε'.le, ENNReal.ofReal_coe_nnreal]
  have hstep := h T hT
  have hdivle : N ≤ S + K / ENNReal.ofReal T := by
    rw [← ENNReal.mul_le_mul_iff_right hT0 ENNReal.ofReal_ne_top, mul_add,
      ENNReal.mul_div_cancel hT0 ENNReal.ofReal_ne_top]
    exact hstep
  exact hdivle.trans (add_le_add le_rfl hdiv)

/-- Square-root endgame: `N ≤ √(N I)` with `N` finite forces `N ≤ I`. -/
theorem le_of_le_sqrt_mul {N I : ℝ≥0∞} (hN : N ≠ ⊤)
    (h : N ≤ (N * I) ^ (1 / 2 : ℝ)) : N ≤ I := by
  rcases eq_or_ne N 0 with hN0 | hN0
  · exact hN0 ▸ zero_le I
  have hsq := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at hsq
  norm_num at hsq
  rw [pow_two] at hsq
  exact (ENNReal.mul_le_mul_iff_right hN0 hN).mp hsq

/-- The squared image density is dominated by the full pullback modulus. -/
theorem rsDensity_sq_le (q h : ℂ → ℂ) (z : ℂ) :
    rsDensity q h z ^ 2 ≤ ‖rsQ q h z‖ₑ := by
  have h1 := norm_sub_re_div_two_nonneg (rsQ q h z)
  have habs := abs_le.mp (Complex.abs_re_le_norm (rsQ q h z))
  unfold rsDensity
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt h1, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (by linarith [habs.1])

/-- Norm factorization of the pullback modulus. -/
theorem norm_rsQ (q h : ℂ → ℂ) (z : ℂ) :
    ‖rsQ q h z‖ = ‖q (h z)‖ * ‖dz h z‖ ^ 2
      * ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2 / ‖q z‖ := by
  unfold rsQ
  rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, norm_pow]

/-- The unimodular direction `q/|q|` has norm at most one. -/
theorem norm_theta_le_one (q : ℂ → ℂ) (z : ℂ) : ‖q z / (‖q z‖ : ℂ)‖ ≤ 1 := by
  rcases eq_or_ne (q z) 0 with h0 | h0
  · simp [h0]
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _

/-- Pointwise lower bound `1 − κ ≤ ‖1 − μ q/|q|‖` under the Beltrami bound. -/
theorem one_sub_kappa_le {q h : ℂ → ℂ} {κ : ℝ} {z : ℂ}
    (hμ : ‖wirtingerQuotient h z‖ ≤ κ) :
    1 - κ ≤ ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ := by
  have hθ := norm_theta_le_one q z
  have h1 : ‖wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ≤ κ := by
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) hθ) hμ
  calc 1 - κ ≤ ‖(1 : ℂ)‖ - ‖wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ := by
        rw [norm_one]; linarith
    _ ≤ ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ := norm_sub_norm_le _ _

/-- Pointwise weight floor: under the Beltrami bound the Reich–Strebel weight is at
least `(1 − κ)²`, so the floored weight agrees with the weight. -/
theorem rsWeightM_eq {q h : ℂ → ℂ} {κ : ℝ} {z : ℂ} (hκ : κ < 1)
    (hμ : ‖wirtingerQuotient h z‖ ≤ κ) :
    rsWeightM q h κ z = rsWeight q h z := by
  have hμ0 : 0 ≤ ‖wirtingerQuotient h z‖ := norm_nonneg _
  have hμ1 : ‖wirtingerQuotient h z‖ < 1 := lt_of_le_of_lt hμ hκ
  have hden : 0 < 1 - ‖wirtingerQuotient h z‖ ^ 2 := by nlinarith
  have hnum := one_sub_kappa_le (q := q) hμ
  refine max_eq_left (ENNReal.ofReal_le_ofReal ?_)
  have hd1 : 1 - ‖wirtingerQuotient h z‖ ^ 2 ≤ 1 := by nlinarith
  have hsq : (1 - κ) ^ 2 ≤ ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2 := by
    have h1κ : 0 ≤ 1 - κ := by linarith
    nlinarith [norm_nonneg (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ)))]
  calc (1 - κ) ^ 2 ≤ ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2 := hsq
    _ ≤ ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2) := by
        rw [le_div_iff₀ hden]; nlinarith [norm_nonneg
          (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ)))]

/-- **The pointwise key bound**: under the Beltrami bound with nonvanishing `∂h`, the
first Cauchy–Schwarz factor weighted by `|q|` is dominated by the image density
`|q(h z)|` times the Jacobian of `h` — the integrand of the change of variables. -/
theorem rsU_mul_le {q h : ℂ → ℂ} {κ : ℝ} {z : ℂ} (hκ : κ < 1)
    (hdz : dz h z ≠ 0) (hμ : ‖wirtingerQuotient h z‖ ≤ κ) :
    rsU q h κ z * ‖q z‖ₑ
      ≤ ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) := by
  rcases eq_or_ne (q z) 0 with h0 | h0
  · rw [h0, enorm_zero, mul_zero]; exact zero_le _
  set m : ℝ := ‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ with hmdef
  set u : ℝ := ‖wirtingerQuotient h z‖ with hudef
  set d : ℝ := ‖dz h z‖ with hddef
  set a : ℝ := ‖q (h z)‖ with hadef
  set Q : ℝ := ‖q z‖ with hQdef
  have hQ0 : 0 < Q := norm_pos_iff.mpr h0
  have hd0 : 0 < d := norm_pos_iff.mpr hdz
  have hu0 : 0 ≤ u := norm_nonneg _
  have hu1 : u < 1 := lt_of_le_of_lt hμ hκ
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have hm0 : 0 < m := lt_of_lt_of_le (by linarith) (one_sub_kappa_le hμ)
  have hdzbar : ‖dzbar h z‖ = u * d := by
    rw [hudef, wirtingerQuotient, norm_div, div_mul_cancel₀ _ hd0.ne']
  have hdet : (fderiv ℝ h z).det = d ^ 2 * (1 - u ^ 2) := by
    rw [det_fderiv_eq_wirtinger, hdzbar]; ring
  have hWinv : (rsWeightM q h κ z)⁻¹
      = ENNReal.ofReal ((1 - u ^ 2) / m ^ 2) := by
    rw [rsWeightM_eq hκ hμ, rsWeight, ← hmdef, ← hudef,
      ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  have hQf : ‖rsQ q h z‖ₑ = ENNReal.ofReal (a * d ^ 2 * m ^ 2 / Q) := by
    rw [← ofReal_norm_eq_enorm, norm_rsQ, ← hmdef, ← hddef, ← hadef, ← hQdef]
  calc rsU q h κ z * ‖q z‖ₑ
      = rsDensity q h z ^ 2 * (rsWeightM q h κ z)⁻¹ * ‖q z‖ₑ := rfl
    _ ≤ ‖rsQ q h z‖ₑ * (rsWeightM q h κ z)⁻¹ * ‖q z‖ₑ := by
        gcongr
        exact rsDensity_sq_le q h z
    _ = ENNReal.ofReal (a * d ^ 2 * m ^ 2 / Q * ((1 - u ^ 2) / m ^ 2) * Q) := by
        rw [hQf, hWinv, ← ofReal_norm_eq_enorm, ← hQdef,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal a * ENNReal.ofReal (d ^ 2 * (1 - u ^ 2)) := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        field_simp
        ring
    _ = ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) := by
        rw [hdet, ofReal_norm_eq_enorm]

/-- Almost everywhere on the upper half plane a quasiconformal map has nonvanishing
`∂h` and Wirtinger quotient bounded by `κ`. -/
theorem ae_qc_facts {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dz h z ≠ 0 ∧ ‖wirtingerQuotient h z‖ ≤ κ := by
  filter_upwards [hqc.jac, hqc.belt] with z hj hb
  rw [det_fderiv_eq_wirtinger] at hj
  have hdz : dz h z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hj
    nlinarith [sq_nonneg ‖dzbar h z‖]
  have hd0 : 0 < ‖dz h z‖ := norm_pos_iff.mpr hdz
  refine ⟨hdz, ?_⟩
  rw [wirtingerQuotient, norm_div, div_le_iff₀ hd0]
  exact hb

/-- Almost everywhere on the upper half plane the floored weight agrees with the
Reich–Strebel weight. -/
theorem ae_rsWeightM_eq {q h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hκ : κ < 1) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsWeightM q h κ z = rsWeight q h z := by
  filter_upwards [ae_qc_facts hqc] with z hz using rsWeightM_eq hκ hz.2

/-- Almost everywhere on the upper half plane the weighted first Cauchy–Schwarz factor
is dominated by the change-of-variables integrand. -/
theorem ae_rsU_mul_le {q h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hκ : κ < 1) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsU q h κ z * ‖q z‖ₑ
        ≤ ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) := by
  filter_upwards [ae_qc_facts hqc] with z hz using rsU_mul_le hκ hz.1 hz.2

/-- The floored weight is everywhere positive and finite. -/
theorem rsWeightM_pos_ne_top (q h : ℂ → ℂ) {κ : ℝ} (hκ : κ < 1) (z : ℂ) :
    rsWeightM q h κ z ≠ 0 ∧ rsWeightM q h κ z ≠ ⊤ := by
  constructor
  · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 - κ) ^ 2) :=
      ENNReal.ofReal_pos.mpr (by nlinarith)
    exact (lt_of_lt_of_le hpos (le_max_right _ _)).ne'
  · exact (max_lt ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne

/-- The canonical Dirichlet domain, viewed in the plane, is compact for a cocompact
free Fuchsian group. -/
theorem isCompact_domain {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    IsCompact (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I) := by
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  exact (isCompact_dirichletDomain hdense).image UpperHalfPlane.continuous_coe

/-- A differential vanishing on the upper half plane has zero mass. -/
theorem l1Norm_eq_zero {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ)
    (hmeas : MeasurableSet (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I))
    (hq : ∀ z : ℂ, 0 < z.im → q z = 0) :
    q.l1Norm = 0 := by
  have hzero : ∀ z ∈ UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ = (0 : ℝ≥0∞) := by
    rintro w ⟨τ, -, rfl⟩
    rw [hq _ (by simpa using τ.im_pos), enorm_zero]
  calc q.l1Norm = ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        ‖q z‖ₑ := rfl
    _ = ∫⁻ _ in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I, (0 : ℝ≥0∞) :=
        setLIntegral_congr_fun hmeas fun z hz => hzero z hz
    _ = 0 := lintegral_zero

/-- **The vertical-flow interface** for the Reich–Strebel argument: an almost-everywhere
defined unit-speed flow along the vertical foliation of `q`, packaged through its three
consumable properties — the leafwise lower bound on the deposited horizontal variation of
the image curves under `h` (endpoint displacement absorbed in the finite constant `C`),
and invariance of the two Cauchy–Schwarz factor integrals against the `|q|`-area of the
Dirichlet domain — together with joint measurability of the composed integrands. -/
structure VerticalFlowData (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (q : QuadraticDifferential Γ) (h : ℂ → ℂ) (κ : ℝ) where
  /-- The uniform displacement constant. -/
  C : ℝ≥0∞
  /-- Finiteness of the displacement constant. -/
  hC : C ≠ ⊤
  /-- The flow map: time, then start point. -/
  flow : ℝ → ℂ → ℂ
  /-- The invariant full-measure set of regular start points. -/
  good : Set ℂ
  /-- Almost every point of the upper half plane is regular. -/
  good_ae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good
  /-- Joint measurability of the composed image density. -/
  meas_D : Measurable fun p : ℝ × ℂ => rsDensity q h (flow p.1 p.2)
  /-- Joint measurability of the composed first Cauchy–Schwarz factor. -/
  meas_U : Measurable fun p : ℝ × ℂ => rsU q h κ (flow p.1 p.2)
  /-- Joint measurability of the composed floored weight. -/
  meas_W : Measurable fun p : ℝ × ℂ => rsWeightM q h κ (flow p.1 p.2)
  /-- **The leafwise estimate**: on a regular leaf the image curve under `h` deposits
  horizontal variation at least the elapsed time minus twice the displacement bound. -/
  leaf_lb : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
    ENNReal.ofReal T ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow t z)) + 2 * C
  /-- **Flow invariance** of the first factor against the `|q|` area measure. -/
  invar_U : ∀ t : ℝ,
    ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      rsU q h κ (flow t z) * ‖q z‖ₑ
      = ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        rsU q h κ z * ‖q z‖ₑ
  /-- **Flow invariance** of the floored weight against the `|q|` area measure. -/
  invar_W : ∀ t : ℝ,
    ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      rsWeightM q h κ (flow t z) * ‖q z‖ₑ
      = ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        rsWeightM q h κ z * ‖q z‖ₑ

/-- Half powers of a finite quantity multiply back to it. -/
theorem rpow_half_self {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c := by
  rcases eq_or_ne c 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]
  · rw [← ENNReal.rpow_add _ _ h0 hc]
    norm_num

/-- Distribution of a finite common factor out of a product of half powers. -/
theorem mul_rpow_half_mul {c A B : ℝ≥0∞} (hc : c ≠ ⊤) :
    (c * A) ^ (1 / 2 : ℝ) * ((c * B) ^ (1 / 2 : ℝ))
      = c * ((A * B) ^ (1 / 2 : ℝ)) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc c ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) * (c ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ))
      = c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) * (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) := by
        ring
    _ = c * (A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) := by rw [rpow_half_self hc]

/-- A quantity is dominated by the geometric mean of two majorants of its square. -/
theorem le_sqrt_mul_sqrt {x y z : ℝ≥0∞} (h : x ^ 2 ≤ y * z) :
    x ≤ y ^ (1 / 2 : ℝ) * z ^ (1 / 2 : ℝ) := by
  have hx : x = (x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hx, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

-- The assembly tier below never unfolds the integrand definitions; sealing them keeps
-- unification from descending into the Wirtinger terms.
attribute [irreducible] rsQ rsDensity rsWeight rsWeightM rsU

/-- **The leafwise weighted Cauchy–Schwarz estimate**: on a regular leaf, the elapsed
time is controlled by the geometric mean of the two Cauchy–Schwarz factors plus the
displacement defect. -/
theorem leaf_pointwise {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {q : QuadraticDifferential Γ} {h : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (fd : VerticalFlowData Γ q h κ) {z : ℂ} (hz : z ∈ fd.good)
    {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal T
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsU q h κ (fd.flow t z)) ^ (1 / 2 : ℝ)
        * (∫⁻ t in Set.Icc (0 : ℝ) T, rsWeightM q h κ (fd.flow t z)) ^ (1 / 2 : ℝ)
        + 2 * fd.C := by
  have hf : Measurable fun t => rsDensity q h (fd.flow t z) :=
    fd.meas_D.comp (measurable_id.prodMk measurable_const)
  have hw : Measurable fun t => rsWeightM q h κ (fd.flow t z) :=
    fd.meas_W.comp (measurable_id.prodMk measurable_const)
  have hcs := lintegral_sq_le_weighted (μ := volume.restrict (Set.Icc (0 : ℝ) T))
    hf.aemeasurable hw.aemeasurable
    (fun t => (rsWeightM_pos_ne_top q h hκ _).1)
    (fun t => (rsWeightM_pos_ne_top q h hκ _).2)
  simp only [rsU]
  exact (fd.leaf_lb z hz T hT).trans (add_le_add (le_sqrt_mul_sqrt hcs) le_rfl)

/-- **Fubini and flow invariance**: the space integral of a leafwise time integral of an
invariant composed integrand is the elapsed time times the invariant value. -/
theorem fubini_invar {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ)
    {F : ℝ × ℂ → ℝ≥0∞} (hF : Measurable F) {c : ℝ≥0∞}
    (hinv : ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        F (t, z) * ‖q z‖ₑ = c) (T : ℝ) :
    ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      (∫⁻ t in Set.Icc (0 : ℝ) T, F (t, z)) * ‖q z‖ₑ = ENNReal.ofReal T * c := by
  set ω := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hω
  have hswapmeas : AEMeasurable (Function.uncurry fun z t => F (t, z) * ‖q z‖ₑ)
      ((volume.restrict ω).prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    refine Measurable.aemeasurable ?_
    have h1 : Measurable fun p : ℂ × ℝ => F (p.2, p.1) := hF.comp measurable_swap
    exact h1.mul ((q.measurable.enorm).comp measurable_fst)
  calc ∫⁻ z in ω, (∫⁻ t in Set.Icc (0 : ℝ) T, F (t, z)) * ‖q z‖ₑ
      = ∫⁻ z in ω, ∫⁻ t in Set.Icc (0 : ℝ) T, F (t, z) * ‖q z‖ₑ := by
        refine lintegral_congr fun z => ?_
        rw [lintegral_mul_const' _ _ (enorm_ne_top)]
    _ = ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ z in ω, F (t, z) * ‖q z‖ₑ :=
        lintegral_lintegral_swap hswapmeas
    _ = ∫⁻ _ in Set.Icc (0 : ℝ) T, c := lintegral_congr fun t => hinv t
    _ = ENNReal.ofReal T * c := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

/-- Geometric means against a common finite factor. -/
theorem geom_mean_mul {a b c : ℝ≥0∞} (hc : c ≠ ⊤) :
    (a * c) ^ (1 / 2 : ℝ) * (b * c) ^ (1 / 2 : ℝ)
      = a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) * c := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_mul_mul_comm, rpow_half_self hc]

/-- **The Reich–Strebel main inequality, reduced to the vertical-flow interface**: given
the flow data and the change-of-variables bound, the `L¹` mass of `q` is dominated by the
Reich–Strebel integral of `h` over the Dirichlet domain. -/
theorem reich_strebel_of_flowData
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (fd : VerticalFlowData Γ q h κ)
    (hcov : ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) ≤ q.l1Norm) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  set ω : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hωdef
  have hsubH : ω ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  set N : ℝ≥0∞ := q.l1Norm with hNdef
  have hNint : N = ∫⁻ z in ω, ‖q z‖ₑ := rfl
  have hN : N ≠ ⊤ := q.l1Norm_ne_top hΓ hfree hcc
  set A : ℝ≥0∞ := ∫⁻ z in ω, rsU q h κ z * ‖q z‖ₑ with hAdef
  set B : ℝ≥0∞ := ∫⁻ z in ω, rsWeightM q h κ z * ‖q z‖ₑ with hBdef
  have haegood : ∀ᵐ z ∂(volume.restrict ω), z ∈ fd.good :=
    ae_restrict_of_ae_restrict_of_subset hsubH fd.good_ae
  have haeW : ∀ᵐ z ∂(volume.restrict ω),
      rsWeightM q h κ z = rsWeight q h z :=
    ae_restrict_of_ae_restrict_of_subset hsubH (ae_rsWeightM_eq hqc hκ)
  have haeU : ∀ᵐ z ∂(volume.restrict ω),
      rsU q h κ z * ‖q z‖ₑ
        ≤ ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) :=
    ae_restrict_of_ae_restrict_of_subset hsubH (ae_rsU_mul_le hqc hκ)
  have hBI : B = ∫⁻ z in ω, ‖q z‖ₑ * ENNReal.ofReal
      (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
        / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
    calc B = ∫⁻ z in ω, rsWeight q h z * ‖q z‖ₑ :=
          lintegral_congr_ae (haeW.mono fun z hz => by
            show rsWeightM q h κ z * ‖q z‖ₑ = rsWeight q h z * ‖q z‖ₑ
            rw [hz])
      _ = _ := lintegral_congr fun z => by
          show rsWeight q h z * ‖q z‖ₑ = _
          rw [rsWeight, mul_comm]
  have hAN : A ≤ N := (lintegral_mono_ae haeU).trans hcov
  have hqe : Measurable fun z : ℂ => ‖q z‖ₑ := q.measurable.enorm
  have key : ∀ T : ℝ, 0 < T → ENNReal.ofReal T * N
      ≤ ENNReal.ofReal T * ((A * B) ^ (1 / 2 : ℝ)) + 2 * fd.C * N := by
    intro T hT
    set aT : ℂ → ℝ≥0∞ :=
      fun z => ∫⁻ t in Set.Icc (0 : ℝ) T, rsU q h κ (fd.flow t z) with haTdef
    set bT : ℂ → ℝ≥0∞ :=
      fun z => ∫⁻ t in Set.Icc (0 : ℝ) T, rsWeightM q h κ (fd.flow t z) with hbTdef
    have haTmeas : Measurable aT :=
      (fd.meas_U.comp measurable_swap).lintegral_prod_right'
    have hbTmeas : Measurable bT :=
      (fd.meas_W.comp measurable_swap).lintegral_prod_right'
    have hXmeas : Measurable fun z => aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) :=
      (ENNReal.continuous_rpow_const.measurable.comp haTmeas).mul
        (ENNReal.continuous_rpow_const.measurable.comp hbTmeas)
    have hstep1 : ENNReal.ofReal T * N
        ≤ ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) + 2 * fd.C) * ‖q z‖ₑ := by
      rw [hNint, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [haegood] with z hz
      exact mul_le_mul_left (leaf_pointwise hκ fd hz hT) _
    have hstep2 : ∫⁻ z in ω,
        (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) + 2 * fd.C) * ‖q z‖ₑ
        = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
          + 2 * fd.C * N := by
      calc ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) + 2 * fd.C) * ‖q z‖ₑ
          = ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ
              + 2 * fd.C * ‖q z‖ₑ) := lintegral_congr fun z => add_mul _ _ _
        _ = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
              + ∫⁻ z in ω, 2 * fd.C * ‖q z‖ₑ :=
            lintegral_add_left (hXmeas.mul hqe) _
        _ = _ := by
            rw [lintegral_const_mul' _ _
              (ENNReal.mul_ne_top ENNReal.ofNat_ne_top fd.hC), ← hNint]
    have hstep3 : ∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ
        = ∫⁻ z in ω, (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) :=
      lintegral_congr fun z => (geom_mean_mul enorm_ne_top).symm
    have hstep4 : ∫⁻ z in ω,
        (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ z in ω, aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
          * (∫⁻ z in ω, bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) :=
      lintegral_sqrt_mul_sqrt_le ((haTmeas.mul hqe).aemeasurable)
        ((hbTmeas.mul hqe).aemeasurable)
    have hstep5 : ∫⁻ z in ω, aT z * ‖q z‖ₑ = ENNReal.ofReal T * A :=
      fubini_invar q fd.meas_U (fun t => (fd.invar_U t).trans hAdef.symm) T
    have hstep6 : ∫⁻ z in ω, bT z * ‖q z‖ₑ = ENNReal.ofReal T * B :=
      fubini_invar q fd.meas_W (fun t => (fd.invar_W t).trans hBdef.symm) T
    calc ENNReal.ofReal T * N
        ≤ ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) + 2 * fd.C) * ‖q z‖ₑ :=
          hstep1
      _ = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
            + 2 * fd.C * N := hstep2
      _ = (∫⁻ z in ω, (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ))
            + 2 * fd.C * N := by rw [hstep3]
      _ ≤ (∫⁻ z in ω, aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
            * (∫⁻ z in ω, bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) + 2 * fd.C * N :=
          add_le_add hstep4 le_rfl
      _ = (ENNReal.ofReal T * A) ^ (1 / 2 : ℝ) * (ENNReal.ofReal T * B) ^ (1 / 2 : ℝ)
            + 2 * fd.C * N := by rw [hstep5, hstep6]
      _ = ENNReal.ofReal T * ((A * B) ^ (1 / 2 : ℝ)) + 2 * fd.C * N := by
          rw [mul_rpow_half_mul ENNReal.ofReal_ne_top]
  have hK2 : 2 * fd.C * N ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top fd.hC) hN
  have hNS : N ≤ (A * B) ^ (1 / 2 : ℝ) := le_of_forall_ofReal_mul_le hK2 key
  have hfin : N ≤ (N * (∫⁻ z in ω, ‖q z‖ₑ * ENNReal.ofReal
      (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
        / (1 - ‖wirtingerQuotient h z‖ ^ 2)))) ^ (1 / 2 : ℝ) :=
    hNS.trans (ENNReal.rpow_le_rpow (mul_le_mul' hAN hBI.le) (by norm_num))
  exact le_of_le_sqrt_mul hN hfin

/-- A quasiconformal map of the upper half plane is differentiable almost everywhere on
the upper half plane: nondifferentiability forces the junk zero derivative, whose
Jacobian cannot be positive. -/
theorem ae_differentiableAt {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), DifferentiableAt ℝ h z := by
  filter_upwards [hqc.jac] with z hj
  by_contra hnd
  have h0 : fderiv ℝ h z = 0 := fderiv_zero_of_not_differentiableAt hnd
  rw [det_fderiv_eq_wirtinger] at hj
  simp only [dz, dzbar, h0, ContinuousLinearMap.zero_apply, mul_zero, sub_zero, add_zero,
    norm_zero] at hj
  norm_num at hj

set_option maxHeartbeats 400000 in
-- Heartbeats: the area-formula rewrite unifies through the image-set lintegrals.
/-- **The change-of-variables half of the Jacobian bound**: the Dirichlet-domain integral
of `|q(h z)|` against the Jacobian of `h` is dominated by the `|q|` mass of the image of
the domain under `h`. The remaining half is the tiling exchange
`∫⁻_{h(ω ∩ D)} ‖q‖ₑ ≤ q.l1Norm` for the injective equivariant image of the fundamental
domain. -/
theorem lintegral_cov_le {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hKmeas : MeasurableSet (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)) :
    (∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det))
    ≤ ∫⁻ z in h '' ((UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)
        ∩ {z : ℂ | DifferentiableAt ℝ h z}), ‖q z‖ₑ := by
  set ω : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hωdef
  have hsubH : ω ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  set s : Set ℂ := ω ∩ {z : ℂ | DifferentiableAt ℝ h z} with hsdef
  have hsmeas : MeasurableSet s := hKmeas.inter (measurableSet_of_differentiableAt ℝ h)
  have hinj : Set.InjOn h s := by
    intro x hx y hy hxy
    have hx' : 0 < x.im := hsubH hx.1
    have hy' : 0 < y.im := hsubH hy.1
    rw [← hqc.left_inv x hx', hxy, hqc.left_inv y hy']
  have hf' : ∀ x ∈ s, HasFDerivWithinAt h (fderiv ℝ h x) s x :=
    fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt
  have hAF := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsmeas hf' hinj
    fun z => ‖q z‖ₑ
  have haes : s =ᵐ[volume] ω := by
    have hae : ∀ᵐ z ∂(volume.restrict ω), DifferentiableAt ℝ h z :=
      ae_restrict_of_ae_restrict_of_subset hsubH (ae_differentiableAt hqc)
    have hae' : ∀ᵐ z ∂volume, z ∈ ω → DifferentiableAt ℝ h z :=
      (ae_restrict_iff' hKmeas).mp hae
    filter_upwards [hae'] with z hz
    change (z ∈ s) = (z ∈ ω)
    simp only [hsdef, Set.mem_inter_iff, Set.mem_setOf_eq, eq_iff_iff, and_iff_left_iff_imp]
    exact hz
  calc ∫⁻ z in ω, ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det)
      = ∫⁻ z in s, ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) :=
        (setLIntegral_congr haes.symm).symm.symm
    _ ≤ ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ h z).det| * ‖q (h z)‖ₑ := by
        refine setLIntegral_mono_ae' hsmeas ?_
        filter_upwards with z hz
        rw [mul_comm]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_abs_self _)) _
    _ = ∫⁻ z in h '' s, ‖q z‖ₑ := hAF.symm


/-- The branch-free horizontal density form of `−W²` is `|Re W|`: the developed-frame
identity behind the vertical flow. -/
theorem sqrt_norm_neg_sq (W : ℂ) :
    Real.sqrt ((‖-W ^ 2‖ - (-W ^ 2).re) / 2) = |W.re| := by
  have h1 : ‖-W ^ 2‖ = W.re ^ 2 + W.im ^ 2 := by
    rw [norm_neg, norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h2 : (-W ^ 2).re = W.im ^ 2 - W.re ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [h1, h2, show (W.re ^ 2 + W.im ^ 2 - (W.im ^ 2 - W.re ^ 2)) / 2 = W.re ^ 2 by ring,
    Real.sqrt_sq_eq_abs]

/-- Along a curve, at a point where a local `−q`-natural chart exists, the horizontal
density of `q` is the modulus of the real part of the developed velocity. -/
theorem horizontalDensity_eq_re_developed {q : ℂ → ℂ} {Φ : ℂ → ℂ} {σ : ℝ → ℂ}
    {t : ℝ} (hsq : deriv Φ (σ t) ^ 2 = -q (σ t))
    (hchain : deriv (Φ ∘ σ) t = deriv Φ (σ t) * deriv σ t) :
    horizontalDensity q σ t = ENNReal.ofReal |(deriv (Φ ∘ σ) t).re| := by
  have hQ : q (σ t) * deriv σ t ^ 2 = -(deriv Φ (σ t) * deriv σ t) ^ 2 := by
    have h := congrArg (fun x => x * deriv σ t ^ 2) hsq
    simp only at h
    calc q (σ t) * deriv σ t ^ 2 = -(deriv Φ (σ t) ^ 2) * deriv σ t ^ 2 := by
          rw [← neg_neg (q (σ t)), ← hsq]
      _ = -(deriv Φ (σ t) * deriv σ t) ^ 2 := by ring
  unfold horizontalDensity
  rw [hQ, hchain, sqrt_norm_neg_sq]


/-- **Order factorization at a point**: a holomorphic function that does not vanish
identically near `z₀` factors as `(z − z₀)^m g z` with `g` analytic and nonvanishing at
`z₀`; the exponent is positive when `z₀` is a zero. -/
theorem exists_order_factorization {q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hq : DifferentiableOn ℂ q U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hnc : ¬ ∀ᶠ z in 𝓝 z₀, q z = 0) :
    ∃ m : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      (∀ᶠ z in 𝓝 z₀, q z = (z - z₀) ^ m * g z) ∧ (q z₀ = 0 → 1 ≤ m) := by
  have hA : AnalyticAt ℂ q z₀ :=
    (hq.analyticOnNhd hU) z₀ hz₀
  have htop : analyticOrderAt q z₀ ≠ ⊤ := fun h => hnc (analyticOrderAt_eq_top.mp h)
  set m : ℕ := analyticOrderNatAt q z₀ with hmdef
  have hcast : analyticOrderAt q z₀ = (m : ℕ∞) := (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨g, hg, hg0, hev⟩ := hA.analyticOrderAt_eq_natCast.mp hcast
  refine ⟨m, g, hg, hg0, ?_, ?_⟩
  · filter_upwards [hev] with z hz
    rw [hz, smul_eq_mul]
  · intro hq0
    by_contra hm
    have hm0 : m = 0 := by omega
    have hself := hev.self_of_nhds
    rw [hm0, pow_zero, one_smul, hq0] at hself
    exact hg0 hself.symm


/-- **Even zeros are transparent**: if `q = (z − z₀)^{2k} g` near `z₀` with `g` analytic
and nonvanishing at `z₀`, then on some disc around `z₀` inside `U` there is a holomorphic
`Φ` with `(Φ')² = −q` — a natural parameter of `−q` through the zero. -/
theorem even_zero_transparent_chart {q g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (k : ℕ) (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 z₀, q z = (z - z₀) ^ (2 * k) * g z) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ U ∧ ∃ Φ : ℂ → ℂ,
      DifferentiableOn ℂ Φ (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, deriv Φ z ^ 2 = -q z := by
  have hpos : (0 : ℝ) < ‖-g z₀‖ := by rw [norm_neg]; exact norm_pos_iff.mpr hg0
  have hgc : ContinuousAt g z₀ := hg.continuousAt
  have hnear : ∀ᶠ z in 𝓝 z₀, -g z ∈ Metric.ball (-g z₀) ‖-g z₀‖ := by
    have hc : ContinuousAt (fun z => -g z) z₀ := hgc.neg
    exact hc (Metric.ball_mem_nhds _ hpos)
  have hdiff : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hmem : {z | -g z ∈ Metric.ball (-g z₀) ‖-g z₀‖}
      ∩ ({z | AnalyticAt ℂ g z} ∩ ({z | q z = (z - z₀) ^ (2 * k) * g z} ∩ U)) ∈ 𝓝 z₀ :=
    Filter.inter_mem hnear (Filter.inter_mem hdiff
      (Filter.inter_mem hfac (hU.mem_nhds hz₀)))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hsubU : Metric.ball z₀ r ⊆ U := fun z hz => (hsub hz).2.2.2
  have hball : ∀ z ∈ Metric.ball z₀ r, -g z ∈ Metric.ball (-g z₀) ‖-g z₀‖ :=
    fun z hz => (hsub hz).1
  have hne : ∀ z ∈ Metric.ball z₀ r, -g z ≠ 0 := by
    intro z hz h0
    have hlt : dist (-g z) (-g z₀) < ‖-g z₀‖ := Metric.mem_ball.mp (hball z hz)
    rw [h0, dist_zero_left] at hlt
    exact lt_irrefl _ hlt
  have hslit : ∀ z ∈ Metric.ball z₀ r, -g z / -g z₀ ∈ Complex.slitPlane := by
    intro z hz
    refine Complex.ball_one_subset_slitPlane (mem_ball_iff_norm.mpr ?_)
    have hne0 : -g z₀ ≠ 0 := neg_ne_zero.mpr hg0
    rw [div_sub_one hne0, norm_div, div_lt_one hpos, ← dist_eq_norm]
    exact Metric.mem_ball.mp (hball z hz)
  set s : ℂ → ℂ :=
    fun z => Complex.exp (Complex.log (-g z₀) / 2 + Complex.log (-g z / -g z₀) / 2)
    with hsdef
  have hgne0 : -g z₀ ≠ 0 := neg_ne_zero.mpr hg0
  have hs2 : ∀ z ∈ Metric.ball z₀ r, s z ^ 2 = -g z := by
    intro z hz
    have hd : -g z / -g z₀ ≠ 0 := div_ne_zero (hne z hz) hgne0
    have harith : Complex.log (-g z₀) / 2 + Complex.log (-g z / -g z₀) / 2
        + (Complex.log (-g z₀) / 2 + Complex.log (-g z / -g z₀) / 2)
        = Complex.log (-g z₀) + Complex.log (-g z / -g z₀) := by ring
    rw [hsdef, sq, ← Complex.exp_add, harith, Complex.exp_add, Complex.exp_log hgne0,
      Complex.exp_log hd, mul_comm, div_mul_cancel₀ _ hgne0]
  have hsd : DifferentiableOn ℂ s (Metric.ball z₀ r) := by
    intro z hz
    have hgz : DifferentiableAt ℂ g z := ((hsub hz).2.1).differentiableAt
    exact ((((hgz.neg.div_const _).clog (hslit z hz)).div_const 2).const_add
      _).cexp.differentiableWithinAt
  set F : ℂ → ℂ := fun z => (z - z₀) ^ k * s z with hFdef
  have hFd : DifferentiableOn ℂ F (Metric.ball z₀ r) :=
    (((differentiable_id.sub_const z₀).pow k).differentiableOn).mul hsd
  obtain ⟨Φ, hΦ⟩ :=
    (hFd.isExactOn_ball : ∃ P, ∀ z ∈ Metric.ball z₀ r, HasDerivAt P (F z) z)
  refine ⟨r, hr, hsubU, Φ,
    fun z hz => (hΦ z hz).differentiableAt.differentiableWithinAt, ?_⟩
  intro z hz
  have hq : q z = (z - z₀) ^ (2 * k) * g z := (hsub hz).2.2.1
  rw [(hΦ z hz).deriv, hFdef]
  have hs2' := hs2 z hz
  calc ((z - z₀) ^ k * s z) ^ 2 = (z - z₀) ^ (2 * k) * s z ^ 2 := by ring
    _ = (z - z₀) ^ (2 * k) * -g z := by rw [hs2']
    _ = -q z := by rw [hq]; ring

/-- Rays leaving the slit ball avoid it: the complement of a slit ball has only
unbounded components. -/
theorem slitBall_compl_unbounded {z₀ : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ z ∉ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane},
      ¬Bornology.IsBounded (connectedComponentIn
        {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane}ᶜ z) := by
  set T : Set ℂ := {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} with hT
  intro z hz hbdd
  have hray : ∃ R : Set ℂ, z ∈ R ∧ IsPreconnected R ∧ R ⊆ Tᶜ ∧
      ∀ M : ℝ, ∃ w ∈ R, M ≤ ‖w‖ := by
    by_cases hzb : z ∈ Metric.ball z₀ r
    · -- on the slit: march further along the negative-real direction
      have hslit : z - z₀ ∉ Complex.slitPlane := fun hs => hz ⟨hzb, hs⟩
      have hno : ¬(0 < (z - z₀).re ∨ (z - z₀).im ≠ 0) :=
        fun hc => hslit (Complex.mem_slitPlane_iff.mpr hc)
      push Not at hno
      refine ⟨(fun t : ℝ => z - (t : ℂ)) '' Set.Ici 0, ⟨0, Set.self_mem_Ici, by simp⟩,
        isPreconnected_Ici.image _
          (continuous_const.sub Complex.continuous_ofReal).continuousOn, ?_, ?_⟩
      · rintro w ⟨t, ht, rfl⟩ hw
        have hre : (z - (t : ℂ) - z₀).re = (z - z₀).re - t := by
          simp [Complex.sub_re]
          ring
        have him : (z - (t : ℂ) - z₀).im = (z - z₀).im := by
          simp [Complex.sub_im]
        simp only [Set.mem_Ici] at ht
        rcases Complex.mem_slitPlane_iff.mp hw.2 with hpos | him0
        · rw [hre] at hpos; linarith [hno.1]
        · rw [him] at him0; exact him0 hno.2
      · intro M
        refine ⟨z - ((|M| + ‖z‖ + 1 : ℝ) : ℂ),
          ⟨|M| + ‖z‖ + 1, by simp only [Set.mem_Ici]; positivity, rfl⟩, ?_⟩
        have h1 : ‖((|M| + ‖z‖ + 1 : ℝ) : ℂ)‖ ≤ ‖z - ((|M| + ‖z‖ + 1 : ℝ) : ℂ)‖ + ‖z‖ := by
          calc ‖((|M| + ‖z‖ + 1 : ℝ) : ℂ)‖ = ‖z - (z - ((|M| + ‖z‖ + 1 : ℝ) : ℂ))‖ := by
                ring_nf
            _ ≤ ‖z‖ + ‖z - ((|M| + ‖z‖ + 1 : ℝ) : ℂ)‖ := norm_sub_le _ _
            _ = _ := by ring
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
        linarith [le_abs_self M]
    · -- outside the ball: the outward radial ray from the center
      have hzne : z - z₀ ≠ 0 := by
        intro h0
        exact hzb (by simp [sub_eq_zero.mp h0, Metric.mem_ball, hr])
      have hnz : (0 : ℝ) < ‖z - z₀‖ := norm_pos_iff.mpr hzne
      set u : ℂ := (z - z₀) / (‖z - z₀‖ : ℂ) with hudef
      have hcast : ((‖z - z₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnz.ne'
      have hru : r ≤ ‖z - z₀‖ := by
        by_contra hlt
        exact hzb (Metric.mem_ball.mpr (by rw [dist_eq_norm]; linarith [not_le.mp hlt]))
      have hu1 : ‖u‖ = 1 := by
        rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg _), div_self hnz.ne']
      have hnormpt : ∀ s : ℝ, 0 ≤ s → ‖z₀ + (s : ℂ) * u - z₀‖ = s := by
        intro s hs
        rw [add_sub_cancel_left, norm_mul, Complex.norm_real, hu1, mul_one,
          Real.norm_eq_abs, abs_of_nonneg hs]
      refine ⟨(fun s : ℝ => z₀ + (s : ℂ) * u) '' Set.Ici ‖z - z₀‖, ?_,
        isPreconnected_Ici.image _
          (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn,
        ?_, ?_⟩
      · refine ⟨‖z - z₀‖, Set.self_mem_Ici, ?_⟩
        rw [hudef]
        field_simp
        ring
      · rintro w ⟨s, hs, rfl⟩ hw
        simp only [Set.mem_Ici] at hs
        have hout : r ≤ ‖z₀ + (s : ℂ) * u - z₀‖ := by
          rw [hnormpt s (le_trans hnz.le hs)]; linarith
        rw [← dist_eq_norm] at hout
        exact absurd (Metric.mem_ball.mp hw.1) (not_lt.mpr hout)
      · intro M
        set s : ℝ := max ‖z - z₀‖ (M + ‖z₀‖) with hsdef
        have hs0 : (0 : ℝ) ≤ s := le_trans hnz.le (le_max_left _ _)
        refine ⟨z₀ + (s : ℂ) * u, ⟨s, Set.mem_Ici.mpr (le_max_left _ _), rfl⟩, ?_⟩
        have h2 : ‖z₀ + (s : ℂ) * u - z₀‖ = s := hnormpt s hs0
        have h1 : ‖z₀ + (s : ℂ) * u - z₀‖ ≤ ‖z₀ + (s : ℂ) * u‖ + ‖z₀‖ := norm_sub_le _ _
        rw [h2] at h1
        have := le_max_right ‖z - z₀‖ (M + ‖z₀‖)
        linarith
  obtain ⟨R, hzR, hRconn, hRsub, hRunb⟩ := hray
  have hRcomp : R ⊆ connectedComponentIn Tᶜ z :=
    hRconn.subset_connectedComponentIn hzR hRsub
  obtain ⟨C, hC⟩ := (hbdd.subset hRcomp).exists_norm_le
  obtain ⟨w, hwR, hwn⟩ := hRunb (C + 1)
  linarith [hC w hwR]

/-- **The slit chart at an odd zero**: if `q = (z − z₀)^{2k+1} g` near `z₀` with `g`
analytic and nonvanishing at `z₀`, then on a slit disc around `z₀` — the disc minus the
leftward horizontal ray — there is a holomorphic `Ψ` with `(Ψ')² = −q`: one branch of
the natural parameter of `−q` at the odd zero. -/
theorem odd_zero_slit_chart {q g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (k : ℕ) (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ ≠ 0)
    (hfac : ∀ᶠ z in 𝓝 z₀, q z = (z - z₀) ^ (2 * k + 1) * g z) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z₀ r ⊆ U ∧ ∃ Ψ : ℂ → ℂ,
      DifferentiableOn ℂ Ψ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} ∧
      ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → deriv Ψ z ^ 2 = -q z := by
  have hpos : (0 : ℝ) < ‖-g z₀‖ := by rw [norm_neg]; exact norm_pos_iff.mpr hg0
  have hnear : ∀ᶠ z in 𝓝 z₀, -g z ∈ Metric.ball (-g z₀) ‖-g z₀‖ :=
    hg.continuousAt.neg (Metric.ball_mem_nhds _ hpos)
  have hmem : {z | -g z ∈ Metric.ball (-g z₀) ‖-g z₀‖}
      ∩ ({z | AnalyticAt ℂ g z} ∩ ({z | q z = (z - z₀) ^ (2 * k + 1) * g z} ∩ U)) ∈ 𝓝 z₀ :=
    Filter.inter_mem hnear (Filter.inter_mem hg.eventually_analyticAt
      (Filter.inter_mem hfac (hU.mem_nhds hz₀)))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hgne0 : -g z₀ ≠ 0 := neg_ne_zero.mpr hg0
  have hne : ∀ z ∈ Metric.ball z₀ r, -g z ≠ 0 := by
    intro z hz h0
    have hlt : dist (-g z) (-g z₀) < ‖-g z₀‖ := Metric.mem_ball.mp (hsub hz).1
    rw [h0, dist_zero_left] at hlt
    exact lt_irrefl _ hlt
  have hslit : ∀ z ∈ Metric.ball z₀ r, -g z / -g z₀ ∈ Complex.slitPlane := by
    intro z hz
    refine Complex.ball_one_subset_slitPlane (mem_ball_iff_norm.mpr ?_)
    rw [div_sub_one hgne0, norm_div, div_lt_one hpos, ← dist_eq_norm]
    exact Metric.mem_ball.mp (hsub hz).1
  set s : ℂ → ℂ :=
    fun z => Complex.exp (Complex.log (-g z₀) / 2 + Complex.log (-g z / -g z₀) / 2)
    with hsdef
  have hs2 : ∀ z ∈ Metric.ball z₀ r, s z ^ 2 = -g z := by
    intro z hz
    have hd : -g z / -g z₀ ≠ 0 := div_ne_zero (hne z hz) hgne0
    have harith : Complex.log (-g z₀) / 2 + Complex.log (-g z / -g z₀) / 2
        + (Complex.log (-g z₀) / 2 + Complex.log (-g z / -g z₀) / 2)
        = Complex.log (-g z₀) + Complex.log (-g z / -g z₀) := by ring
    rw [hsdef, sq, ← Complex.exp_add, harith, Complex.exp_add, Complex.exp_log hgne0,
      Complex.exp_log hd, mul_comm, div_mul_cancel₀ _ hgne0]
  set T : Set ℂ := {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} with hTdef
  have hTopen : IsOpen T := Metric.isOpen_ball.inter
    (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const))
  set F : ℂ → ℂ :=
    fun z => (z - z₀) ^ k * Complex.exp (Complex.log (z - z₀) / 2) * s z with hFdef
  have hFd : DifferentiableOn ℂ F T := by
    intro z hz
    have hgz : DifferentiableAt ℂ g z := ((hsub hz.1).2.1).differentiableAt
    have hsz : DifferentiableAt ℂ s z :=
      ((((hgz.neg.div_const _).clog (hslit z hz.1)).div_const 2).const_add _).cexp
    have hmid : DifferentiableAt ℂ (fun z => Complex.exp (Complex.log (z - z₀) / 2)) z :=
      (((differentiableAt_id.sub_const z₀).clog hz.2).div_const 2).cexp
    exact ((((differentiableAt_id.sub_const z₀).pow k).mul hmid).mul hsz).differentiableWithinAt
  obtain ⟨Ψ, hΨd, hΨderiv⟩ :=
    has_primitives_of_unbounded_components hTopen (slitBall_compl_unbounded hr) F hFd
  refine ⟨r, hr, fun z hz => (hsub hz).2.2.2, Ψ, hΨd, ?_⟩
  intro z hzball hzslit
  have hzT : z ∈ T := ⟨hzball, hzslit⟩
  have hz0 : z - z₀ ≠ 0 := by
    intro h0
    rw [h0] at hzslit
    simp [Complex.mem_slitPlane_iff] at hzslit
  have hq : q z = (z - z₀) ^ (2 * k + 1) * g z := (hsub hzball).2.2.1
  rw [hΨderiv hzT, hFdef]
  have hexp : Complex.exp (Complex.log (z - z₀) / 2) ^ 2 = z - z₀ := by
    rw [sq, ← Complex.exp_add, show Complex.log (z - z₀) / 2 + Complex.log (z - z₀) / 2
      = Complex.log (z - z₀) by ring, Complex.exp_log hz0]
  calc ((z - z₀) ^ k * Complex.exp (Complex.log (z - z₀) / 2) * s z) ^ 2
      = (z - z₀) ^ (2 * k) * Complex.exp (Complex.log (z - z₀) / 2) ^ 2 * s z ^ 2 := by
        ring
    _ = (z - z₀) ^ (2 * k) * (z - z₀) * -g z := by rw [hexp, hs2 z hzball]
    _ = -q z := by rw [hq]; ring


/-- A plane Möbius map of `SL(2, ℝ)` is real-differentiable off the real axis. -/
theorem moebius_diffAt (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : DifferentiableAt ℝ (moebiusMap γ) z :=
  ((hasDerivAt_moebiusMap γ (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
    ).complexToReal_fderiv).differentiableAt

/-- Continuity of a plane Möbius map on the open upper half plane. -/
theorem moebius_contOn (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ContinuousOn (moebiusMap γ) {z : ℂ | 0 < z.im} :=
  fun _ hz => ((moebius_diffAt γ hz).continuousAt).continuousWithinAt

/-- The inverse Möbius map undoes the map on the upper half plane. -/
theorem moebius_cancel (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : moebiusMap γ⁻¹ (moebiusMap γ z) = z := by
  rw [moebiusMap_mul γ⁻¹ γ z (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'),
    inv_mul_cancel, moebiusMap_one]

/-- The Möbius map undoes its inverse on the upper half plane. -/
theorem moebius_cancel' (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : moebiusMap γ (moebiusMap γ⁻¹ z) = z := by
  have h := moebius_cancel γ⁻¹ hz
  rwa [inv_inv] at h

/-- Injectivity of a plane Möbius map on the open upper half plane. -/
theorem moebius_injOn (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Set.InjOn (moebiusMap γ) {z : ℂ | 0 < z.im} := by
  intro x hx y hy hxy
  have h1 := moebius_cancel γ (hx : 0 < x.im)
  rw [hxy, moebius_cancel γ (hy : 0 < y.im)] at h1
  exact h1.symm

/-- The subgroup action on the upper half plane coincides with the plane Möbius map. -/
theorem coe_smul_moebius {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (γ : ↥Γ)
    (τ : UpperHalfPlane) : ((γ • τ : UpperHalfPlane) : ℂ) = moebiusMap ↑γ ↑τ :=
  coe_smul_eq_moebiusMap ↑γ τ

/-- The image of a measurable null set under an injective everywhere-differentiable map
is null: by the area formula its measure is the integral of the Jacobian over a null set. -/
theorem image_null {f : ℂ → ℂ} {N : Set ℂ} (hN : MeasurableSet N)
    (h0 : volume N = 0) (hd : ∀ z ∈ N, DifferentiableAt ℝ f z)
    (hinj : Set.InjOn f N) : volume (f '' N) = 0 := by
  have hAF := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hN
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) hinj (fun _ => (1 : ℝ≥0∞))
  calc volume (f '' N) = ∫⁻ _ in f '' N, 1 := (setLIntegral_one _).symm
    _ = ∫⁻ x in N, ENNReal.ofReal |(fderiv ℝ f x).det| * 1 := hAF
    _ = 0 := setLIntegral_measure_zero _ _ h0

/-- The Möbius image of an open subset of the upper half plane is open. -/
theorem isOpen_moebius_image (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ {z : ℂ | 0 < z.im}) :
    IsOpen (moebiusMap γ '' V) := by
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have himg : moebiusMap γ '' V = {z : ℂ | 0 < z.im} ∩ moebiusMap γ⁻¹ ⁻¹' V := by
    ext w
    constructor
    · rintro ⟨v, hvV, rfl⟩
      have hv : 0 < v.im := hVU hvV
      refine ⟨moebiusMap_im_pos γ hv, ?_⟩
      show moebiusMap γ⁻¹ (moebiusMap γ v) ∈ V
      rw [moebius_cancel γ hv]
      exact hvV
    · rintro ⟨hw, hwV⟩
      exact ⟨moebiusMap γ⁻¹ w, hwV, moebius_cancel' γ (hw : 0 < w.im)⟩
  rw [himg]
  exact (moebius_contOn γ⁻¹).isOpen_inter_preimage hUopen hV

/-- The planar image of the frontier of the Dirichlet domain is Lebesgue-null: it lies in
the finitely many active bisectors, each carried by a null line or circle. -/
theorem frontier_image_null {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) {τ₀ : UpperHalfPlane} {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    volume (UpperHalfPlane.coe '' frontier (dirichletDomain Γ τ₀)) = 0 := by
  refine measure_mono_null (t := ⋃ γ ∈ activeSides Γ τ₀ R,
    UpperHalfPlane.coe '' {τ : UpperHalfPlane | dist τ τ₀ = dist τ (γ • τ₀)}) ?_ ?_
  · rintro w ⟨τ, hτ, rfl⟩
    obtain ⟨γ, hγ, hmem⟩ := Set.mem_iUnion₂.mp (frontier_dirichletDomain_subset hΓ hdense hτ)
    exact Set.mem_iUnion₂.mpr ⟨γ, hγ, Set.mem_image_of_mem _ hmem⟩
  · rw [measure_biUnion_null_iff (finite_activeSides hΓ τ₀ R).countable]
    intro γ hγ
    obtain ⟨S, hS0, hSsub⟩ := exists_null_carrier_bisector τ₀ (γ • τ₀) (Ne.symm hγ.2)
    refine measure_mono_null ?_ hS0
    rintro w ⟨τ, hτ, rfl⟩
    exact hSsub τ hτ

/-- An element of a free Fuchsian group fixing the base point acts as the identity Möbius
map on the upper half plane. -/
theorem stab_moebius_id {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {δ : ↥Γ} (hδ : δ • UpperHalfPlane.I = UpperHalfPlane.I)
    {z : ℂ} (hz : 0 < z.im) : moebiusMap ↑δ z = z := by
  have htriv := hfree δ ⟨UpperHalfPlane.I, hδ⟩ ⟨z, hz⟩
  have h := congrArg UpperHalfPlane.coe htriv
  rwa [coe_smul_moebius δ ⟨z, hz⟩] at h

/-- **Plane tiling cover**: a point of the upper half plane outside the `Γ`-orbit of the
planar frontier image lies in a Möbius translate of the open Dirichlet tile. -/
theorem cover {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) {w : ℂ} (hw : 0 < w.im)
    (hnb : w ∉ ⋃ γ : ↥Γ, moebiusMap ↑γ ''
      (UpperHalfPlane.coe '' frontier (dirichletDomain Γ UpperHalfPlane.I))) :
    ∃ γ : ↥Γ, w ∈ moebiusMap ↑γ ''
      (UpperHalfPlane.coe '' interior (dirichletDomain Γ UpperHalfPlane.I)) := by
  obtain ⟨γ', hγ'⟩ := exists_smul_mem_dirichletDomain hΓ UpperHalfPlane.I ⟨w, hw⟩
  have hback : moebiusMap ↑(γ'⁻¹) ((γ' • (⟨w, hw⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
      = w := by
    rw [coe_smul_moebius γ' ⟨w, hw⟩]
    exact moebius_cancel (↑γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ) hw
  by_cases hint : γ' • (⟨w, hw⟩ : UpperHalfPlane) ∈ interior (dirichletDomain Γ
      UpperHalfPlane.I)
  · exact ⟨γ'⁻¹, _, Set.mem_image_of_mem _ hint, hback⟩
  · exfalso
    apply hnb
    have hfr : γ' • (⟨w, hw⟩ : UpperHalfPlane) ∈ frontier (dirichletDomain Γ
        UpperHalfPlane.I) := by
      rw [(isClosed_dirichletDomain Γ UpperHalfPlane.I).frontier_eq]
      exact ⟨hγ', hint⟩
    exact Set.mem_iUnion.mpr ⟨γ'⁻¹, _, Set.mem_image_of_mem _ hfr, hback⟩

set_option maxHeartbeats 400000 in
-- Heartbeats: the tiling exchange elaborates the area formula, the Lusin–Souslin image
-- measurability, and the quotient-indexed tsum rewrites in a single proof.
/-- **The Reich–Strebel tiling bound**: for an equivariant quasiconformal self-map of the
upper half plane, the Dirichlet-domain integral of `|q ∘ h|` against the Jacobian of `h`
is dominated by the `L¹` mass of `q` — the image of the fundamental piece re-tiles into
the `Γ`-translates of the Dirichlet domain and `|q| dA` is `Γ`-invariant. -/
theorem reich_strebel_tiling_bound
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (_hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z)) :
    ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) ≤ q.l1Norm := by
  classical
  haveI : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  haveI : Countable (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) :=
    QuotientGroup.mk_surjective.countable
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  set D : Set UpperHalfPlane := dirichletDomain Γ UpperHalfPlane.I with hDdef
  set ω : Set ℂ := UpperHalfPlane.coe '' D with hωdef
  have hωmeas : MeasurableSet ω := (isCompact_domain hΓ hfree hcc).measurableSet
  have hωU : ω ⊆ {z : ℂ | 0 < z.im} := by rintro w ⟨τ, -, rfl⟩; simpa using τ.im_pos
  set ωo : Set ℂ := UpperHalfPlane.coe '' interior D with hωodef
  have hωoopen : IsOpen ωo := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_interior
  have hωoU : ωo ⊆ {z : ℂ | 0 < z.im} := by rintro w ⟨τ, -, rfl⟩; simpa using τ.im_pos
  have hωoω : ωo ⊆ ω := Set.image_mono interior_subset
  have hInjU : Set.InjOn h {z : ℂ | 0 < z.im} := by
    intro x hx y hy hxy
    rw [← hqc.left_inv x hx, hxy, hqc.left_inv y hy]
  set s : Set ℂ := ω ∩ {z : ℂ | DifferentiableAt ℝ h z} with hsdef
  have hsmeas : MeasurableSet s := hωmeas.inter (measurableSet_of_differentiableAt ℝ h)
  have hsU : s ⊆ {z : ℂ | 0 < z.im} := fun z hz => hωU hz.1
  set E : Set ℂ := h '' s with hEdef
  have hEU : E ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨z, hz, rfl⟩
    exact hqc.mapsTo z (hsU hz)
  have hEmeas : MeasurableSet E :=
    hsmeas.image_of_continuousOn_injOn (hqc.cont.mono hsU) (hInjU.mono hsU)
  set F : Set ℂ := UpperHalfPlane.coe '' frontier D with hFdef
  have hFU : F ⊆ {z : ℂ | 0 < z.im} := by rintro w ⟨τ, -, rfl⟩; simpa using τ.im_pos
  have hFcomp : IsCompact F :=
    ((isCompact_dirichletDomain hdense).of_isClosed_subset isClosed_frontier
      (isClosed_dirichletDomain Γ UpperHalfPlane.I).frontier_subset).image
      UpperHalfPlane.continuous_coe
  have hFmeas : MeasurableSet F := hFcomp.measurableSet
  have hFnull : volume F = 0 := frontier_image_null hΓ hdense
  set Bad : Set ℂ := ⋃ γ : ↥Γ, moebiusMap ↑γ '' F with hBaddef
  have hBadU : Bad ⊆ {z : ℂ | 0 < z.im} := by
    intro w hw
    obtain ⟨γ, v, hvF, rfl⟩ := Set.mem_iUnion.mp hw
    exact moebiusMap_im_pos ↑γ (hFU hvF)
  have hBadmeas : MeasurableSet Bad := MeasurableSet.iUnion fun γ =>
    (hFcomp.image_of_continuousOn ((moebius_contOn ↑γ).mono hFU)).measurableSet
  have hBadnull : volume Bad = 0 := by
    rw [hBaddef, measure_iUnion_null_iff]
    intro γ
    exact image_null hFmeas hFnull (fun z hz => moebius_diffAt ↑γ (hFU hz))
      ((moebius_injOn ↑γ).mono hFU)
  set T : (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) → Set ℂ :=
    fun c => moebiusMap ↑(Quotient.out c) '' ωo with hTdef
  have hTU : ∀ c, T c ⊆ {z : ℂ | 0 < z.im} := by
    rintro c w ⟨v, hv, rfl⟩
    exact moebiusMap_im_pos _ (hωoU hv)
  have hTopen : ∀ c, IsOpen (T c) := fun c =>
    isOpen_moebius_image _ hωoopen hωoU
  have hrep : ∀ γ : ↥Γ, ∀ z : ℂ, 0 < z.im →
      moebiusMap ↑(Quotient.out (QuotientGroup.mk γ : ↥Γ ⧸ MulAction.stabilizer ↥Γ
        UpperHalfPlane.I)) z = moebiusMap ↑γ z := by
    intro γ z hz
    set γ' : ↥Γ := Quotient.out (QuotientGroup.mk γ : ↥Γ ⧸ MulAction.stabilizer ↥Γ
      UpperHalfPlane.I) with hγ'def
    have hδ : γ⁻¹ * γ' ∈ MulAction.stabilizer ↥Γ UpperHalfPlane.I := by
      rw [← QuotientGroup.eq]
      exact (QuotientGroup.out_eq' _).symm
    have hfact : γ' = γ * (γ⁻¹ * γ') := by group
    have hid : moebiusMap ↑(γ⁻¹ * γ') z = z :=
      stab_moebius_id hfree (MulAction.mem_stabilizer_iff.mp hδ) hz
    conv_lhs => rw [hfact]
    have hcoe : ((↑(γ * (γ⁻¹ * γ')) : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        = ↑γ * ↑(γ⁻¹ * γ') := rfl
    rw [hcoe, ← moebiusMap_mul ↑γ ↑(γ⁻¹ * γ') z
      (moebiusDenom_ne_zero_of_im_ne_zero _ hz.ne'), hid]
  have hEcover : E ⊆ Bad ∪ ⋃ c, (T c ∩ E) := by
    intro w hwE
    by_cases hb : w ∈ Bad
    · exact Or.inl hb
    · have hwU : (0 : ℝ) < w.im := hEU hwE
      obtain ⟨γ, hγmem⟩ := cover hΓ hwU hb
      have himeq : T (QuotientGroup.mk γ) = moebiusMap ↑γ '' ωo :=
        Set.image_congr fun z hz => hrep γ z (hωoU hz)
      refine Or.inr (Set.mem_iUnion.mpr ⟨QuotientGroup.mk γ, ?_, hwE⟩)
      rw [himeq]
      exact hγmem
  refine le_trans (lintegral_cov_le q hqc hωmeas) ?_
  show ∫⁻ z in E, ‖q z‖ₑ ≤ q.l1Norm
  have hsplit : ∫⁻ z in E, ‖q z‖ₑ ≤ ∑' c, ∫⁻ z in T c ∩ E, ‖q z‖ₑ := by
    calc ∫⁻ z in E, ‖q z‖ₑ ≤ ∫⁻ z in Bad ∪ ⋃ c, (T c ∩ E), ‖q z‖ₑ :=
          lintegral_mono_set hEcover
      _ ≤ (∫⁻ z in Bad, ‖q z‖ₑ) + ∫⁻ z in ⋃ c, (T c ∩ E), ‖q z‖ₑ :=
          lintegral_union_le _ _ _
      _ ≤ 0 + ∑' c, ∫⁻ z in T c ∩ E, ‖q z‖ₑ :=
          add_le_add (le_of_eq (setLIntegral_measure_zero _ _ hBadnull))
            (lintegral_iUnion_le _ _)
      _ = ∑' c, ∫⁻ z in T c ∩ E, ‖q z‖ₑ := zero_add _
  set B : (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) → Set ℂ :=
    fun c => moebiusMap (↑(Quotient.out c))⁻¹ '' (T c ∩ E) with hBdef
  have hTEU : ∀ c, T c ∩ E ⊆ {z : ℂ | 0 < z.im} := fun c =>
    Set.inter_subset_left.trans (hTU c)
  have hBmeas : ∀ c, MeasurableSet (B c) := fun c =>
    ((hTopen c).measurableSet.inter hEmeas).image_of_continuousOn_injOn
      ((moebius_contOn _).mono (hTEU c)) ((moebius_injOn _).mono (hTEU c))
  have hBsub : ∀ c, B c ⊆ ωo := by
    rintro c z₀ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hw.1
    rw [moebius_cancel _ (hωoU hv)]
    exact hv
  have himgB : ∀ c : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I,
      moebiusMap ↑(Quotient.out c) '' B c = T c ∩ E := by
    intro c
    ext w
    constructor
    · rintro ⟨z₀, ⟨w', hw', rfl⟩, rfl⟩
      rwa [moebius_cancel' _ (hTEU c hw')]
    · intro hw
      exact ⟨moebiusMap (↑(Quotient.out c))⁻¹ w, Set.mem_image_of_mem _ hw,
        moebius_cancel' _ (hTEU c hw)⟩
  have hint : ∀ c, ∫⁻ z in T c ∩ E, ‖q z‖ₑ = ∫⁻ z in B c, ‖q z‖ₑ := by
    intro c
    conv_lhs => rw [← himgB c]
    exact q.lintegral_enorm_image (Quotient.out c).2 (hBmeas c) ((hBsub c).trans hωoU)
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hBadDmeas : MeasurableSet (Bad ∩ {z : ℂ | DifferentiableAt ℝ h z}) :=
    hBadmeas.inter (measurableSet_of_differentiableAt ℝ h)
  have hHBadnull : volume (h '' (Bad ∩ {z : ℂ | DifferentiableAt ℝ h z})) = 0 :=
    image_null hBadDmeas (measure_mono_null Set.inter_subset_left hBadnull)
      (fun z hz => hz.2) (hInjU.mono fun z hz => hBadU hz.1)
  have hpull : ∀ c : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I, ∀ z₀ ∈ B c,
      ∃ z₁ ∈ s, h (moebiusMap (↑(Quotient.out c))⁻¹ z₁) = z₀ ∧
        DifferentiableAt ℝ h (moebiusMap (↑(Quotient.out c))⁻¹ z₁) := by
    intro c z₀ hz₀
    obtain ⟨w, hw, rfl⟩ := hz₀
    obtain ⟨z₁, hz₁, hz₁w⟩ := hw.2
    refine ⟨z₁, hz₁, ?_, ?_⟩
    · rw [hcomm (↑(Quotient.out c))⁻¹ (inv_mem (Quotient.out c).2) z₁ (hsU hz₁), hz₁w]
    · set g : ↥Γ := Quotient.out c with hgdef
      have huU : 0 < (moebiusMap (↑g)⁻¹ z₁).im := moebiusMap_im_pos _ (hsU hz₁)
      have hveq : ∀ ζ ∈ {z : ℂ | 0 < z.im},
          h ζ = moebiusMap (↑g)⁻¹ (h (moebiusMap ↑g ζ)) := by
        intro ζ hζ
        rw [hcomm ↑g g.2 ζ hζ, moebius_cancel _ (hqc.mapsTo ζ hζ)]
      have hev : h =ᶠ[nhds (moebiusMap (↑g)⁻¹ z₁)]
          fun ζ => moebiusMap (↑g)⁻¹ (h (moebiusMap ↑g ζ)) :=
        Filter.eventuallyEq_of_mem (hUopen.mem_nhds huU) hveq
      have hmu : moebiusMap ↑g (moebiusMap (↑g)⁻¹ z₁) = z₁ :=
        moebius_cancel' _ (hsU hz₁)
      have h1 : DifferentiableAt ℝ (moebiusMap ↑g) (moebiusMap (↑g)⁻¹ z₁) :=
        moebius_diffAt _ huU
      have h2 : DifferentiableAt ℝ h (moebiusMap ↑g (moebiusMap (↑g)⁻¹ z₁)) := by
        rw [hmu]
        exact hz₁.2
      have h3 : DifferentiableAt ℝ (moebiusMap (↑g)⁻¹)
          (h (moebiusMap ↑g (moebiusMap (↑g)⁻¹ z₁))) := by
        rw [hmu]
        exact moebius_diffAt _ (hqc.mapsTo z₁ (hsU hz₁))
      have hcomp : DifferentiableAt ℝ (moebiusMap (↑g)⁻¹ ∘ h ∘ moebiusMap ↑g)
          (moebiusMap (↑g)⁻¹ z₁) :=
        h3.comp (moebiusMap (↑g)⁻¹ z₁) (h2.comp (moebiusMap (↑g)⁻¹ z₁) h1)
      exact hev.differentiableAt_iff.mpr hcomp
  have hmult : ∀ c c' : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I, c ≠ c' →
      B c ∩ B c' ⊆ h '' (Bad ∩ {z : ℂ | DifferentiableAt ℝ h z}) := by
    intro c c' hne z₀ hz₀
    obtain ⟨z₁, hz₁, hh₁, hd₁⟩ := hpull c z₀ hz₀.1
    obtain ⟨z₂, hz₂, hh₂, hd₂⟩ := hpull c' z₀ hz₀.2
    set g₁ : ↥Γ := Quotient.out c with hg₁def
    set g₂ : ↥Γ := Quotient.out c' with hg₂def
    have hu₁U : 0 < (moebiusMap (↑g₁)⁻¹ z₁).im := moebiusMap_im_pos _ (hsU hz₁)
    have hu₂U : 0 < (moebiusMap (↑g₂)⁻¹ z₂).im := moebiusMap_im_pos _ (hsU hz₂)
    have huu : moebiusMap (↑g₁)⁻¹ z₁ = moebiusMap (↑g₂)⁻¹ z₂ :=
      hInjU hu₁U hu₂U (hh₁.trans hh₂.symm)
    obtain ⟨σ₁, hσ₁D, hσ₁⟩ := hz₁.1
    obtain ⟨σ₂, hσ₂D, hσ₂⟩ := hz₂.1
    have hcoe₁ : ((g₁⁻¹ • σ₁ : UpperHalfPlane) : ℂ) = moebiusMap (↑g₁)⁻¹ z₁ := by
      rw [coe_smul_moebius g₁⁻¹ σ₁, hσ₁]
      rfl
    have hcoe₂ : ((g₂⁻¹ • σ₂ : UpperHalfPlane) : ℂ) = moebiusMap (↑g₂)⁻¹ z₂ := by
      rw [coe_smul_moebius g₂⁻¹ σ₂, hσ₂]
      rfl
    have hττ : g₁⁻¹ • σ₁ = g₂⁻¹ • σ₂ :=
      UpperHalfPlane.coe_injective (by rw [hcoe₁, hcoe₂]; exact huu)
    have hδσ : (g₂ * g₁⁻¹) • σ₁ = σ₂ := by
      rw [mul_smul, hττ, smul_inv_smul]
    have hmove : (g₂ * g₁⁻¹) • UpperHalfPlane.I ≠ UpperHalfPlane.I := by
      intro hfix
      apply hne
      have htriv := hfree (g₂ * g₁⁻¹) ⟨UpperHalfPlane.I, hfix⟩
      have hK : g₁⁻¹ * g₂ ∈ MulAction.stabilizer ↥Γ UpperHalfPlane.I := by
        refine MulAction.mem_stabilizer_iff.mpr ?_
        have hconj : g₁⁻¹ * g₂ = g₁⁻¹ * ((g₂ * g₁⁻¹) * g₁) := by group
        rw [hconj, mul_smul, mul_smul, htriv, inv_smul_smul]
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      exact QuotientGroup.eq.mpr hK
    have hDσ₂ : (g₂ * g₁⁻¹) • σ₁ ∈ D := by
      rw [hδσ]
      exact hσ₂D
    have hfr : σ₁ ∈ frontier D ∨ (g₂ * g₁⁻¹) • σ₁ ∈ frontier D := by
      by_cases h₁ : σ₁ ∈ interior D
      · by_cases h₂ : (g₂ * g₁⁻¹) • σ₁ ∈ interior D
        · exact absurd ⟨σ₁, h₁, rfl⟩ (Set.disjoint_left.mp
            (disjoint_smul_interior_dirichletDomain hΓ hdense hmove) h₂)
        · right
          rw [hDdef, (isClosed_dirichletDomain Γ UpperHalfPlane.I).frontier_eq]
          exact ⟨hDσ₂, h₂⟩
      · left
        rw [hDdef, (isClosed_dirichletDomain Γ UpperHalfPlane.I).frontier_eq]
        exact ⟨hσ₁D, h₁⟩
    have huBad : moebiusMap (↑g₁)⁻¹ z₁ ∈ Bad := by
      rcases hfr with hfr₁ | hfr₂
      · refine Set.mem_iUnion.mpr ⟨g₁⁻¹, (σ₁ : ℂ), Set.mem_image_of_mem _ hfr₁, ?_⟩
        exact (coe_smul_moebius g₁⁻¹ σ₁).symm.trans hcoe₁
      · refine Set.mem_iUnion.mpr ⟨g₁⁻¹ * (g₂ * g₁⁻¹)⁻¹,
          (((g₂ * g₁⁻¹) • σ₁ : UpperHalfPlane) : ℂ), Set.mem_image_of_mem _ hfr₂, ?_⟩
        have hkey : (g₁⁻¹ * (g₂ * g₁⁻¹)⁻¹) • ((g₂ * g₁⁻¹) • σ₁) = g₁⁻¹ • σ₁ := by
          rw [mul_smul, inv_smul_smul]
        calc moebiusMap ↑(g₁⁻¹ * (g₂ * g₁⁻¹)⁻¹) (((g₂ * g₁⁻¹) • σ₁ : UpperHalfPlane) : ℂ)
            = (((g₁⁻¹ * (g₂ * g₁⁻¹)⁻¹) • ((g₂ * g₁⁻¹) • σ₁) : UpperHalfPlane) : ℂ) :=
              (coe_smul_moebius _ _).symm
          _ = ((g₁⁻¹ • σ₁ : UpperHalfPlane) : ℂ) := by rw [hkey]
          _ = moebiusMap (↑g₁)⁻¹ z₁ := hcoe₁
    exact ⟨moebiusMap (↑g₁)⁻¹ z₁, ⟨huBad, hd₁⟩, hh₁⟩
  have hdisj : Pairwise (Function.onFun (MeasureTheory.AEDisjoint volume) B) :=
    fun c c' hne => measure_mono_null (hmult c c' hne) hHBadnull
  calc ∫⁻ z in E, ‖q z‖ₑ ≤ ∑' c, ∫⁻ z in T c ∩ E, ‖q z‖ₑ := hsplit
    _ = ∑' c, ∫⁻ z in B c, ‖q z‖ₑ := tsum_congr hint
    _ = ∫⁻ z in ⋃ c, B c, ‖q z‖ₑ :=
        (lintegral_iUnion₀ (fun c => (hBmeas c).nullMeasurableSet) hdisj _).symm
    _ ≤ ∫⁻ z in ω, ‖q z‖ₑ :=
        lintegral_mono_set (Set.iUnion_subset fun c => (hBsub c).trans hωoω)
    _ = q.l1Norm := rfl

/-- The slit disc is star-shaped about its positive-radius points: the segment from any
point of the slit disc to `z₀ + c` with `0 < c < r` stays in the slit disc. -/
theorem slit_segment_subset {z₀ : ℂ} {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    {a : ℂ} (ha : a ∈ Metric.ball z₀ r) (has : a - z₀ ∈ Complex.slitPlane) :
    segment ℝ a (z₀ + (c : ℂ))
      ⊆ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} := by
  intro w hw
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hw
  have hw0 : s • a + t • (z₀ + (c : ℂ)) - z₀ = s • (a - z₀) + t • (c : ℂ) := by
    have hz : (s : ℂ) + (t : ℂ) = 1 := by
      push_cast
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hst
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul]
    linear_combination z₀ * hz
  constructor
  · rw [Metric.mem_ball, dist_eq_norm, hw0]
    have h1 : ‖s • (a - z₀) + t • (c : ℂ)‖ ≤ s * ‖a - z₀‖ + t * c := by
      calc ‖s • (a - z₀) + t • (c : ℂ)‖ ≤ ‖s • (a - z₀)‖ + ‖t • (c : ℂ)‖ := norm_add_le _ _
        _ = s * ‖a - z₀‖ + t * c := by
            rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hs, abs_of_nonneg ht, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hc.le]
    have h2 : ‖a - z₀‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at ha
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · have ht1 : t = 1 := by linarith
      subst ht1
      rw [← hs0]
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.le] using hcr
    · have h3 : s * ‖a - z₀‖ < s * r := mul_lt_mul_of_pos_left h2 hs0
      have h4 : t * c ≤ t * r := mul_le_mul_of_nonneg_left hcr.le ht
      nlinarith
  · rw [hw0]
    rcases Complex.mem_slitPlane_iff.mp has with hre | him
    · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      have hres : (s • (a - z₀) + t • (c : ℂ)).re = s * (a - z₀).re + t * c := by
        rw [Complex.real_smul, Complex.real_smul]
        simp [Complex.add_re, Complex.mul_re]
      rw [hres]
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · have ht1 : t = 1 := by linarith
        rw [← hs0, ht1]; simpa using hc
      · nlinarith
    · have hims : (s • (a - z₀) + t • (c : ℂ)).im = s * (a - z₀).im := by
        rw [Complex.real_smul, Complex.real_smul]
        simp [Complex.add_im, Complex.mul_im]
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · have ht1 : t = 1 := by linarith
        refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
        rw [Complex.add_re, Complex.real_smul, Complex.real_smul, ← hs0, ht1]
        simpa using hc
      · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
        rw [hims]
        exact mul_ne_zero hs0.ne' him

/-- Lipschitz control against the star center: on the slit disc a holomorphic function
with derivative bounded by `M` moves by at most `M` times the distance along the segment
to a positive-radius point. -/
theorem slit_lipschitz_to_center {Ψ : ℂ → ℂ} {z₀ : ℂ} {r M c : ℝ} (hM : 0 ≤ M)
    (hc : 0 < c) (hcr : c < r)
    (hΨ : DifferentiableOn ℂ Ψ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hbd : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → ‖deriv Ψ z‖ ≤ M)
    {a : ℂ} (ha : a ∈ Metric.ball z₀ r) (has : a - z₀ ∈ Complex.slitPlane) :
    dist (Ψ a) (Ψ (z₀ + (c : ℂ))) ≤ M * dist a (z₀ + (c : ℂ)) := by
  set T : Set ℂ := {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} with hT
  have hTopen : IsOpen T := Metric.isOpen_ball.inter
    (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const))
  have hseg : segment ℝ a (z₀ + (c : ℂ)) ⊆ T := slit_segment_subset hc hcr ha has
  have hf : ∀ z ∈ segment ℝ a (z₀ + (c : ℂ)),
      HasDerivWithinAt Ψ (deriv Ψ z) (segment ℝ a (z₀ + (c : ℂ))) z := fun z hz =>
    ((hΨ.differentiableAt (hTopen.mem_nhds (hseg hz))).hasDerivAt).hasDerivWithinAt
  have hlip : LipschitzOnWith M.toNNReal Ψ (segment ℝ a (z₀ + (c : ℂ))) := by
    refine (convex_segment _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hf fun z hz => ?_
    rw [← norm_toNNReal]
    exact Real.toNNReal_mono (hbd z (hseg hz).1 (hseg hz).2)
  have hmem_a : a ∈ segment ℝ a (z₀ + (c : ℂ)) := left_mem_segment _ _ _
  have hmem_p : z₀ + (c : ℂ) ∈ segment ℝ a (z₀ + (c : ℂ)) := right_mem_segment _ _ _
  have := hlip.dist_le_mul a hmem_a (z₀ + (c : ℂ)) hmem_p
  rwa [Real.coe_toNNReal M hM] at this

/-- **Continuous extension of a slit chart to the puncture**: a holomorphic function on
the slit disc with uniformly bounded derivative has a limit at the center. -/
theorem slit_chart_limit {Ψ : ℂ → ℂ} {z₀ : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hΨ : DifferentiableOn ℂ Ψ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hbd : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → ‖deriv Ψ z‖ ≤ M) :
    ∃ L : ℂ, Filter.Tendsto Ψ
      (nhdsWithin z₀ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
      (nhds L) := by
  set T : Set ℂ := {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} with hT
  have hmemT : ∀ c : ℝ, 0 < c → c < r → z₀ + (c : ℂ) ∈ T := by
    intro c hc hcr
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hc.le]
      exact hcr
    · rw [add_sub_cancel_left]
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hc))
  have hclos : z₀ ∈ closure T := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨z₀ + ((min (r / 2) (ε / 2) : ℝ) : ℂ),
      hmemT _ (by positivity) (by rw [min_lt_iff]; left; linarith), ?_⟩
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    calc min (r / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
      _ < ε := by linarith
  have hne : (nhdsWithin z₀ T).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclos
  have hkey : ∀ δ : ℝ, 0 < δ → δ < r → ∀ a ∈ T ∩ Metric.ball z₀ δ,
      ∀ b ∈ T ∩ Metric.ball z₀ δ, dist (Ψ a) (Ψ b) ≤ M * (3 * δ) := by
    intro δ hδ hδr a ha b hb
    have hc2 : (0 : ℝ) < δ / 2 := by positivity
    have hc2r : δ / 2 < r := by linarith
    have hda := slit_lipschitz_to_center hM hc2 hc2r hΨ hbd ha.1.1 ha.1.2
    have hdb := slit_lipschitz_to_center hM hc2 hc2r hΨ hbd hb.1.1 hb.1.2
    have hdista : dist a (z₀ + ((δ / 2 : ℝ) : ℂ)) ≤ 3 / 2 * δ := by
      calc dist a (z₀ + ((δ / 2 : ℝ) : ℂ)) ≤ dist a z₀ + dist z₀ (z₀ + ((δ / 2 : ℝ) : ℂ)) :=
            dist_triangle _ _ _
        _ ≤ 3 / 2 * δ := by
            have h1 : dist a z₀ < δ := Metric.mem_ball.mp ha.2
            have h2 : dist z₀ (z₀ + ((δ / 2 : ℝ) : ℂ)) = δ / 2 := by
              rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg hc2.le]
            linarith
    have hdistb : dist b (z₀ + ((δ / 2 : ℝ) : ℂ)) ≤ 3 / 2 * δ := by
      calc dist b (z₀ + ((δ / 2 : ℝ) : ℂ)) ≤ dist b z₀ + dist z₀ (z₀ + ((δ / 2 : ℝ) : ℂ)) :=
            dist_triangle _ _ _
        _ ≤ 3 / 2 * δ := by
            have h1 : dist b z₀ < δ := Metric.mem_ball.mp hb.2
            have h2 : dist z₀ (z₀ + ((δ / 2 : ℝ) : ℂ)) = δ / 2 := by
              rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real,
                Real.norm_eq_abs, abs_of_nonneg hc2.le]
            linarith
    calc dist (Ψ a) (Ψ b)
        ≤ dist (Ψ a) (Ψ (z₀ + ((δ / 2 : ℝ) : ℂ))) + dist (Ψ (z₀ + ((δ / 2 : ℝ) : ℂ))) (Ψ b) :=
          dist_triangle _ _ _
      _ ≤ M * (3 / 2 * δ) + M * (3 / 2 * δ) := by
          have ha' : dist (Ψ a) (Ψ (z₀ + ((δ / 2 : ℝ) : ℂ))) ≤ M * (3 / 2 * δ) :=
            hda.trans (mul_le_mul_of_nonneg_left hdista hM)
          have hb' : dist (Ψ (z₀ + ((δ / 2 : ℝ) : ℂ))) (Ψ b) ≤ M * (3 / 2 * δ) := by
            rw [dist_comm]
            exact hdb.trans (mul_le_mul_of_nonneg_left hdistb hM)
          linarith
      _ = M * (3 * δ) := by ring
  have hcauchy : Cauchy (Filter.map Ψ (nhdsWithin z₀ T)) := by
    refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, fun ε hε => ?_⟩
    set δ : ℝ := min (r / 2) (ε / (3 * M + 1)) with hδdef
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨Ψ '' (T ∩ Metric.ball z₀ δ), Filter.image_mem_map ?_, ?_⟩
    · exact inter_mem_nhdsWithin T (Metric.ball_mem_nhds z₀ hδ0)
    · rintro x ⟨a, haT, rfl⟩ y ⟨b, hbT, rfl⟩
      have := hkey δ hδ0 hδr a haT b hbT
      have hδε : M * (3 * δ) < ε := by
        have h1 : δ ≤ ε / (3 * M + 1) := min_le_right _ _
        have h2 : M * (3 * δ) ≤ M * (3 * (ε / (3 * M + 1))) := by gcongr
        have h3 : M * (3 * (ε / (3 * M + 1))) < ε := by
          have heq : M * (3 * (ε / (3 * M + 1))) = 3 * M * ε / (3 * M + 1) := by
            field_simp
          rw [heq, div_lt_iff₀ (by positivity : (0:ℝ) < 3 * M + 1)]
          nlinarith
        linarith
      exact lt_of_le_of_lt this hδε
  obtain ⟨L, hL⟩ := CompleteSpace.complete hcauchy
  exact ⟨L, hL⟩

/-- The slit disc is preconnected: it is star-shaped about its positive-radius points. -/
theorem slit_isPreconnected {z₀ : ℂ} {r : ℝ} (hr : 0 < r) :
    IsPreconnected {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} := by
  have hp : z₀ + ((r / 2 : ℝ) : ℂ)
      ∈ {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
    · rw [add_sub_cancel_left]
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using by positivity))
  have hstar : StarConvex ℝ (z₀ + ((r / 2 : ℝ) : ℂ))
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} := by
    rw [starConvex_iff_segment_subset]
    intro a ha
    rw [segment_symm]
    exact slit_segment_subset (by positivity) (by linarith) ha.1 ha.2
  exact (hstar.isPathConnected hp).isConnected.isPreconnected

/-- A holomorphic function with vanishing derivative on the slit disc is constant
there. -/
theorem slit_eq_of_deriv_zero {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hf0 : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → deriv f z = 0)
    {a b : ℂ} (ha : a ∈ Metric.ball z₀ r) (has : a - z₀ ∈ Complex.slitPlane)
    (hb : b ∈ Metric.ball z₀ r) (hbs : b - z₀ ∈ Complex.slitPlane) : f a = f b := by
  have hc : (0 : ℝ) < r / 2 := by positivity
  have hcr : r / 2 < r := by linarith
  have hbd : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → ‖deriv f z‖ ≤ 0 :=
    fun z hz hzs => by rw [hf0 z hz hzs, norm_zero]
  have h1 := slit_lipschitz_to_center le_rfl hc hcr hf hbd ha has
  have h2 := slit_lipschitz_to_center le_rfl hc hcr hf hbd hb hbs
  rw [zero_mul] at h1 h2
  have h1' : f a = f (z₀ + ((r / 2 : ℝ) : ℂ)) := by
    rwa [← dist_le_zero]
  have h2' : f b = f (z₀ + ((r / 2 : ℝ) : ℂ)) := by
    rwa [← dist_le_zero]
  rw [h1', h2']

/-- **Branch classification on the slit disc**: two holomorphic square-root primitives of
`−q` on the slit disc agree up to sign and an additive constant — the two branches of the
natural parameter. -/
theorem slit_chart_branch_classification {q Ψ Φ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hΨ : DifferentiableOn ℂ Ψ
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hΦ : DifferentiableOn ℂ Φ
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hΨq : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → deriv Ψ z ^ 2 = -q z)
    (hΦq : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → deriv Φ z ^ 2 = -q z)
    (hq0 : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → q z ≠ 0) :
    (∃ b : ℂ, ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → Φ z = Ψ z + b) ∨
    (∃ b : ℂ, ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → Φ z = b - Ψ z) := by
  set T : Set ℂ := {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane} with hT
  have hTopen : IsOpen T := Metric.isOpen_ball.inter
    (Complex.isOpen_slitPlane.preimage (continuous_id.sub continuous_const))
  have hTconn : IsPreconnected T := slit_isPreconnected hr
  set u : ℂ → ℂ := fun z => deriv Φ z - deriv Ψ z with hu
  set v : ℂ → ℂ := fun z => deriv Φ z + deriv Ψ z with hv
  have hΨan : AnalyticOnNhd ℂ (deriv Ψ) T := (hΨ.analyticOnNhd hTopen).deriv
  have hΦan : AnalyticOnNhd ℂ (deriv Φ) T := (hΦ.analyticOnNhd hTopen).deriv
  have huan : AnalyticOnNhd ℂ u T := hΦan.sub hΨan
  have hvan : AnalyticOnNhd ℂ v T := hΦan.add hΨan
  have huv : ∀ z ∈ T, u z * v z = 0 := fun z hz => by
    have h1 := hΨq z hz.1 hz.2
    have h2 := hΦq z hz.1 hz.2
    simp only [hu, hv]
    linear_combination h2 - h1
  have hΨne : ∀ z ∈ T, deriv Ψ z ≠ 0 := by
    intro z hz h0
    have := hΨq z hz.1 hz.2
    rw [h0] at this
    exact hq0 z hz.1 hz.2 (by simpa using this.symm)
  set U : Set ℂ := {z : ℂ | ∀ᶠ w in nhds z, u w = 0} ∩ T with hU
  set V : Set ℂ := {z : ℂ | ∀ᶠ w in nhds z, v w = 0} ∩ T with hV
  have hUopen : IsOpen U := isOpen_setOf_eventually_nhds.inter hTopen
  have hVopen : IsOpen V := isOpen_setOf_eventually_nhds.inter hTopen
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro z ⟨hu0, hzT⟩ ⟨hv0, -⟩
    have h1 : u z = 0 := hu0.self_of_nhds
    have h2 : v z = 0 := hv0.self_of_nhds
    apply hΨne z hzT
    simp only [hu, hv] at h1 h2
    linear_combination (h2 - h1) / 2
  have hcover : T ⊆ U ∪ V := by
    intro z hz
    have hTz : T ∈ nhds z := hTopen.mem_nhds hz
    rcases (huan z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exact Or.inl ⟨h0, hz⟩
    · refine Or.inr ⟨?_, hz⟩
      have hpunc : ∀ᶠ w in nhds z, w ≠ z → u w ≠ 0 := eventually_nhdsWithin_iff.mp hne
      have hvz : v z = 0 := by
        have hvc : Filter.Tendsto v (nhdsWithin z {z}ᶜ) (nhds (v z)) :=
          ((hvan z hz).continuousAt).continuousWithinAt
        have hvev : v =ᶠ[nhdsWithin z {z}ᶜ] fun _ => (0 : ℂ) := by
          rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
          filter_upwards [hpunc, hTz] with w hw1 hw2 hwne
          rcases mul_eq_zero.mp (huv w hw2) with h | h
          · exact absurd h (hw1 (by simpa using hwne))
          · exact h
        exact tendsto_nhds_unique (hvc.congr' hvev) tendsto_const_nhds
      filter_upwards [hpunc, hTz] with w hw1 hw2
      by_cases hwz : w = z
      · rw [hwz, hvz]
      · rcases mul_eq_zero.mp (huv w hw2) with h | h
        · exact absurd h (hw1 hwz)
        · exact h
  rcases hTconn.subset_or_subset hUopen hVopen hdisj hcover with hsub | hsub
  · left
    have hfd : DifferentiableOn ℂ (fun z => Φ z - Ψ z) T := hΦ.sub hΨ
    have hderiv0 : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane →
        deriv (fun z => Φ z - Ψ z) z = 0 := by
      intro z hz hzs
      have hΦd : DifferentiableAt ℂ Φ z := hΦ.differentiableAt (hTopen.mem_nhds ⟨hz, hzs⟩)
      have hΨd : DifferentiableAt ℂ Ψ z := hΨ.differentiableAt (hTopen.mem_nhds ⟨hz, hzs⟩)
      show deriv (Φ - Ψ) z = 0
      rw [(hΦd.hasDerivAt.sub hΨd.hasDerivAt).deriv]
      have := ((hsub ⟨hz, hzs⟩).1).self_of_nhds
      simpa [hu] using this
    have hp : z₀ + ((r / 2 : ℝ) : ℂ) ∈ T := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        linarith
      · rw [add_sub_cancel_left]
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using by positivity))
    refine ⟨Φ (z₀ + ((r / 2 : ℝ) : ℂ)) - Ψ (z₀ + ((r / 2 : ℝ) : ℂ)), fun z hz hzs => ?_⟩
    have := slit_eq_of_deriv_zero hr hfd hderiv0 hz hzs hp.1 hp.2
    linear_combination this
  · right
    have hfd : DifferentiableOn ℂ (fun z => Φ z + Ψ z) T := hΦ.add hΨ
    have hderiv0 : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane →
        deriv (fun z => Φ z + Ψ z) z = 0 := by
      intro z hz hzs
      have hΦd : DifferentiableAt ℂ Φ z := hΦ.differentiableAt (hTopen.mem_nhds ⟨hz, hzs⟩)
      have hΨd : DifferentiableAt ℂ Ψ z := hΨ.differentiableAt (hTopen.mem_nhds ⟨hz, hzs⟩)
      show deriv (Φ + Ψ) z = 0
      rw [(hΦd.hasDerivAt.add hΨd.hasDerivAt).deriv]
      have := ((hsub ⟨hz, hzs⟩).1).self_of_nhds
      simpa [hv] using this
    have hp : z₀ + ((r / 2 : ℝ) : ℂ) ∈ T := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        linarith
      · rw [add_sub_cancel_left]
        exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using by positivity))
    refine ⟨Φ (z₀ + ((r / 2 : ℝ) : ℂ)) + Ψ (z₀ + ((r / 2 : ℝ) : ℂ)), fun z hz hzs => ?_⟩
    have := slit_eq_of_deriv_zero hr hfd hderiv0 hz hzs hp.1 hp.2
    linear_combination this

/-- The puncture filter of the slit disc is nontrivial. -/
theorem slit_nhdsWithin_neBot {z₀ : ℂ} {r : ℝ} (hr : 0 < r) :
    (nhdsWithin z₀
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane}).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨z₀ + ((min (r / 2) (ε / 2) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc min (r / 2) (ε / 2) ≤ r / 2 := min_le_left _ _
      _ < r := by linarith
  · rw [add_sub_cancel_left]
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.ofReal_re]
    exact lt_min (by linarith) (by linarith)
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_min (by linarith) (by linarith))]
    calc min (r / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
      _ < ε := by linarith

/-- **Branch limits transform with the branch relation**: two slit charts of `−q` with
puncture limits either differ by the constant matching the limits, or are related by the
point reflection determined by the limit sum; equal limits give `Φ = 2c − Ψ`. -/
theorem slit_branch_limit_relation {q Ψ Φ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} {LΨ LΦ : ℂ}
    (hr : 0 < r)
    (hΨ : DifferentiableOn ℂ Ψ
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hΦ : DifferentiableOn ℂ Φ
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
    (hΨq : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → deriv Ψ z ^ 2 = -q z)
    (hΦq : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → deriv Φ z ^ 2 = -q z)
    (hq0 : ∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → q z ≠ 0)
    (hLΨ : Filter.Tendsto Ψ (nhdsWithin z₀
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane}) (nhds LΨ))
    (hLΦ : Filter.Tendsto Φ (nhdsWithin z₀
      {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane}) (nhds LΦ)) :
    (∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane → Φ z = Ψ z + (LΦ - LΨ)) ∨
    (∀ z ∈ Metric.ball z₀ r, z - z₀ ∈ Complex.slitPlane →
      Φ z = (LΦ + LΨ) - Ψ z) := by
  have hne := slit_nhdsWithin_neBot (z₀ := z₀) hr
  rcases slit_chart_branch_classification hr hΨ hΦ hΨq hΦq hq0 with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    have hev : Φ =ᶠ[nhdsWithin z₀
        {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane}]
        fun z => Ψ z + b := by
      filter_upwards [self_mem_nhdsWithin] with w hw using hb w hw.1 hw.2
    have h2 : Filter.Tendsto (fun z => Ψ z + b) (nhdsWithin z₀
        {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
        (nhds (LΨ + b)) := hLΨ.add_const b
    have hbeq : LΦ = LΨ + b := tendsto_nhds_unique (hLΦ.congr' hev) h2
    intro z hz hzs
    rw [hb z hz hzs]
    linear_combination hbeq.symm
  · right
    have hev : Φ =ᶠ[nhdsWithin z₀
        {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane}]
        fun z => b - Ψ z := by
      filter_upwards [self_mem_nhdsWithin] with w hw using hb w hw.1 hw.2
    have h2 : Filter.Tendsto (fun z => b - Ψ z) (nhdsWithin z₀
        {z : ℂ | z ∈ Metric.ball z₀ r ∧ z - z₀ ∈ Complex.slitPlane})
        (nhds (b - LΨ)) := tendsto_const_nhds.sub hLΨ
    have hbeq : LΦ = b - LΨ := tendsto_nhds_unique (hLΦ.congr' hev) h2
    intro z hz hzs
    rw [hb z hz hzs]
    linear_combination hbeq.symm

/-- The reflected-target accumulator: each crossing at position `c` replaces the target
`τ` by its point reflection `2c − τ`. -/
def reflTarget : ℝ → List ℝ → ℝ
  | τ, [] => τ
  | τ, c :: cs => reflTarget (2 * c - τ) cs

/-- The crossing cost of a chain: the sum of the successive distances from the start
through the crossing positions to the final position. -/
def reflCost : ℝ → List ℝ → ℝ → ℝ
  | u, [], f => |f - u|
  | u, c :: cs, f => |c - u| + reflCost c cs f

/-- **The telescoping induction**: a chain that starts at `u₀` and ends on the fully
reflected target pays at least the distance from `u₀` to the original target — each
reflection preserves the remaining distance, and the triangle inequality telescopes. -/
theorem reflect_telescoping :
    ∀ (cs : List ℝ) (u₀ τ f : ℝ), f = reflTarget τ cs →
      |τ - u₀| ≤ reflCost u₀ cs f := by
  intro cs
  induction cs with
  | nil =>
    intro u₀ τ f hf
    rw [reflCost, hf, reflTarget]
  | cons c cs ih =>
    intro u₀ τ f hf
    rw [reflCost]
    have h1 : |2 * c - τ - c| ≤ reflCost c cs f := ih c (2 * c - τ) f hf
    have h2 : |2 * c - τ - c| = |c - τ| := by
      rw [show 2 * c - τ - c = c - τ by ring]
    calc |τ - u₀| ≤ |c - u₀| + |c - τ| := by
          have h4 : |τ - u₀| ≤ |τ - c| + |c - u₀| := abs_sub_le τ c u₀
          have h5 : |τ - c| = |c - τ| := abs_sub_comm τ c
          linarith
      _ ≤ |c - u₀| + reflCost c cs f := by
          rw [← h2] at *
          linarith


/-- **Single-chart variation lower bound**: if along `[a, b]` the horizontal density of
`q` along `σ` is the modulus of the real part of the developed velocity, and the
developed real part is absolutely continuous with matching derivative, then the deposited
horizontal variation dominates the developed real displacement. -/
theorem single_chart_variation_lb {q Φ : ℂ → ℂ} {σ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : AbsolutelyContinuousOnInterval (fun t => (Φ (σ t)).re) a b)
    (hden : ∀ t ∈ Set.Icc a b,
      horizontalDensity q σ t = ENNReal.ofReal |(deriv (Φ ∘ σ) t).re|)
    (hd : ∀ t ∈ Set.Icc a b,
      deriv (fun s => (Φ (σ s)).re) t = (deriv (Φ ∘ σ) t).re) :
    ENNReal.ofReal |(Φ (σ b)).re - (Φ (σ a)).re|
      ≤ ∫⁻ t in Set.Icc a b, horizontalDensity q σ t := by
  set u : ℝ → ℝ := fun t => (Φ (σ t)).re with hudef
  have hmem_a : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hmem_b : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have h1 : ENNReal.ofReal |u b - u a| ≤ eVariationOn u (Set.Icc a b) := by
    have := eVariationOn.edist_le u hmem_b hmem_a
    rwa [edist_dist, Real.dist_eq] at this
  have h2 : eVariationOn u (Set.Icc a b) ≤ ∫⁻ t in Set.Icc a b, ‖deriv u t‖₊ :=
    hu.eVariationOn_le_lintegral_deriv hab
  have h3 : ∫⁻ t in Set.Icc a b, (‖deriv u t‖₊ : ℝ≥0∞)
      = ∫⁻ t in Set.Icc a b, horizontalDensity q σ t := by
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [hden t ht, ← enorm_eq_nnnorm, hd t ht, Real.enorm_eq_ofReal_abs]
  exact h1.trans (h2.trans_eq h3)


/-- **A development chain** for `q` along `σ` with `n` pieces: partition points, chart
developments per piece, and affine `±`-matching data at the junctions, carrying the
density identity, absolute continuity, and the chain rule on every piece. -/
structure DevChain (q : ℂ → ℂ) (σ : ℝ → ℂ) (n : ℕ) where
  /-- The partition points. -/
  t : ℕ → ℝ
  /-- The chart development on each piece. -/
  Φ : ℕ → ℂ → ℂ
  /-- The junction signs. -/
  ε : ℕ → ℝ
  /-- The junction constants. -/
  c : ℕ → ℝ
  /-- The partition is monotone. -/
  hmono : ∀ i < n, t i ≤ t (i + 1)
  /-- The density identity almost everywhere on each piece. -/
  hden : ∀ i < n, ∀ᵐ s ∂(volume.restrict (Set.Icc (t i) (t (i + 1)))),
    horizontalDensity q σ s = ENNReal.ofReal |(deriv (Φ i ∘ σ) s).re|
  /-- Absolute continuity of the developed real part on each piece. -/
  hAC : ∀ i < n, AbsolutelyContinuousOnInterval
    (fun s => (Φ i (σ s)).re) (t i) (t (i + 1))
  /-- The chain rule almost everywhere on each piece. -/
  hchain : ∀ i < n, ∀ᵐ s ∂(volume.restrict (Set.Icc (t i) (t (i + 1)))),
    deriv (fun s' => (Φ i (σ s')).re) s = (deriv (Φ i ∘ σ) s).re
  /-- Each junction sign is `±1`. -/
  hsign : ∀ i, ε i = 1 ∨ ε i = -1
  /-- The branch matching at each interior junction. -/
  hmatch : ∀ i, i + 1 < n →
    (Φ (i + 1) (σ (t (i + 1)))).re = ε i * (Φ i (σ (t (i + 1)))).re + c i

/-- Pulling a developed value from frame `i` back to frame `0` through the junction
isometries `v ↦ ε (v − c)`. -/
def chainPull (ε c : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, v => v
  | i + 1, v => chainPull ε c i (ε i * (v - c i))

/-- Each pullback is an isometry of the line. -/
theorem chainPull_isometry {ε c : ℕ → ℝ} (hsign : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∀ i, ∀ x y : ℝ, |chainPull ε c i x - chainPull ε c i y| = |x - y| := by
  intro i
  induction i with
  | zero => intro x y; rfl
  | succ i ih =>
    intro x y
    rw [chainPull, chainPull, ih]
    have hfac : ε i * (x - c i) - ε i * (y - c i) = ε i * (x - y) := by ring
    rw [hfac, abs_mul]
    rcases hsign i with h | h <;> rw [h] <;> simp

/-- Almost-everywhere variant of the single-chart variation lower bound. -/
theorem single_chart_variation_lb_ae {q Φ : ℂ → ℂ} {σ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hu : AbsolutelyContinuousOnInterval (fun t => (Φ (σ t)).re) a b)
    (hden : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      horizontalDensity q σ t = ENNReal.ofReal |(deriv (Φ ∘ σ) t).re|)
    (hd : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      deriv (fun s => (Φ (σ s)).re) t = (deriv (Φ ∘ σ) t).re) :
    ENNReal.ofReal |(Φ (σ b)).re - (Φ (σ a)).re|
      ≤ ∫⁻ t in Set.Icc a b, horizontalDensity q σ t := by
  set u : ℝ → ℝ := fun t => (Φ (σ t)).re with hudef
  have h1 : ENNReal.ofReal |u b - u a| ≤ eVariationOn u (Set.Icc a b) := by
    have := eVariationOn.edist_le u (Set.right_mem_Icc.mpr hab) (Set.left_mem_Icc.mpr hab)
    rwa [edist_dist, Real.dist_eq] at this
  have h2 : eVariationOn u (Set.Icc a b) ≤ ∫⁻ t in Set.Icc a b, ‖deriv u t‖₊ :=
    hu.eVariationOn_le_lintegral_deriv hab
  have h3 : ∫⁻ t in Set.Icc a b, (‖deriv u t‖₊ : ℝ≥0∞)
      = ∫⁻ t in Set.Icc a b, horizontalDensity q σ t := by
    refine lintegral_congr_ae ?_
    filter_upwards [hden, hd] with t ht1 ht2
    rw [ht1, ← enorm_eq_nnnorm, ht2, Real.enorm_eq_ofReal_abs]
  exact h1.trans (h2.trans_eq h3)

/-- Partition points of a chain increase from the left endpoint. -/
theorem devChain_t_le {q : ℂ → ℂ} {σ : ℝ → ℂ} {n : ℕ} (D : DevChain q σ n) :
    ∀ m, m ≤ n → D.t 0 ≤ D.t m := by
  intro m
  induction m with
  | zero => intro _; exact le_rfl
  | succ m ih =>
    intro hm
    exact (ih (by omega)).trans (D.hmono m (by omega))

/-- **The chain variation lower bound**: the developed displacement of the final frame,
pulled back to the initial frame through the junction isometries, is dominated by the
total deposited horizontal variation. -/
theorem devChain_variation_lb {q : ℂ → ℂ} {σ : ℝ → ℂ} :
    ∀ n : ℕ, ∀ D : DevChain q σ (n + 1),
    ENNReal.ofReal |chainPull D.ε D.c n ((D.Φ n (σ (D.t (n + 1)))).re)
        - (D.Φ 0 (σ (D.t 0))).re|
      ≤ ∫⁻ s in Set.Icc (D.t 0) (D.t (n + 1)), horizontalDensity q σ s := by
  intro n
  induction n with
  | zero =>
    intro D
    exact single_chart_variation_lb_ae (q := q) (Φ := D.Φ 0) (σ := σ)
      (D.hmono 0 (by omega)) (D.hAC 0 (by omega)) (D.hden 0 (by omega))
      (D.hchain 0 (by omega))
  | succ n ih =>
    intro D
    set D' : DevChain q σ (n + 1) :=
      ⟨D.t, D.Φ, D.ε, D.c, fun i hi => D.hmono i (by omega),
        fun i hi => D.hden i (by omega), fun i hi => D.hAC i (by omega),
        fun i hi => D.hchain i (by omega), D.hsign,
        fun i hi => D.hmatch i (by omega)⟩ with hD'
    have hIH := ih D'
    have hlast := single_chart_variation_lb_ae (q := q) (Φ := D.Φ (n + 1)) (σ := σ)
      (D.hmono (n + 1) (by omega)) (D.hAC (n + 1) (by omega))
      (D.hden (n + 1) (by omega)) (D.hchain (n + 1) (by omega))
    set vfin : ℝ := (D.Φ (n + 1) (σ (D.t (n + 2)))).re with hvfin
    set vmid : ℝ := (D.Φ (n + 1) (σ (D.t (n + 1)))).re with hvmid
    set umid : ℝ := (D.Φ n (σ (D.t (n + 1)))).re with humid
    have hjunc : vmid = D.ε n * umid + D.c n := D.hmatch n (by omega)
    have hstep : D.ε n * (vmid - D.c n) = umid := by
      rcases D.hsign n with h | h <;> rw [hjunc, h] <;> ring
    have hpull : chainPull D.ε D.c (n + 1) vmid = chainPull D.ε D.c n umid := by
      rw [chainPull, hstep]
    have htri : |chainPull D.ε D.c (n + 1) vfin - (D.Φ 0 (σ (D.t 0))).re|
        ≤ |vfin - vmid| + |chainPull D.ε D.c n umid - (D.Φ 0 (σ (D.t 0))).re| := by
      have h1 := abs_sub_le (chainPull D.ε D.c (n + 1) vfin)
        (chainPull D.ε D.c (n + 1) vmid) ((D.Φ 0 (σ (D.t 0))).re)
      rw [chainPull_isometry D.hsign (n + 1) vfin vmid, hpull] at h1
      exact h1
    have hsplit : ∫⁻ s in Set.Icc (D.t 0) (D.t (n + 2)), horizontalDensity q σ s
        = (∫⁻ s in Set.Icc (D.t 0) (D.t (n + 1)), horizontalDensity q σ s)
          + ∫⁻ s in Set.Icc (D.t (n + 1)) (D.t (n + 2)), horizontalDensity q σ s := by
      have h01 : D.t 0 ≤ D.t (n + 1) := devChain_t_le D _ (by omega)
      have h12 : D.t (n + 1) ≤ D.t (n + 2) := D.hmono (n + 1) (by omega)
      rw [← Set.Icc_union_Ioc_eq_Icc h01 h12,
        lintegral_union measurableSet_Ioc
          ((Set.Iic_disjoint_Ioc le_rfl).mono Set.Icc_subset_Iic_self le_rfl)]
      congr 1
      exact (setLIntegral_congr Ioc_ae_eq_Icc)
    calc ENNReal.ofReal |chainPull D.ε D.c (n + 1) vfin - (D.Φ 0 (σ (D.t 0))).re|
        ≤ ENNReal.ofReal (|vfin - vmid|
            + |chainPull D.ε D.c n umid - (D.Φ 0 (σ (D.t 0))).re|) :=
          ENNReal.ofReal_le_ofReal htri
      _ = ENNReal.ofReal |vfin - vmid|
            + ENNReal.ofReal |chainPull D.ε D.c n umid - (D.Φ 0 (σ (D.t 0))).re| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ (∫⁻ s in Set.Icc (D.t (n + 1)) (D.t (n + 2)), horizontalDensity q σ s)
            + ∫⁻ s in Set.Icc (D.t 0) (D.t (n + 1)), horizontalDensity q σ s := by
          rw [abs_sub_comm] at hlast ⊢
          exact add_le_add hlast hIH
      _ = ∫⁻ s in Set.Icc (D.t 0) (D.t (n + 2)), horizontalDensity q σ s := by
          rw [hsplit, add_comm]

/-- **Branch classification on any preconnected open set**: two holomorphic functions
with equal squared derivatives differ by a sign and an additive constant. -/
theorem open_branch_classification {Φ₁ Φ₂ : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {p : ℂ} (hp : p ∈ Ω)
    (h₁ : DifferentiableOn ℂ Φ₁ Ω) (h₂ : DifferentiableOn ℂ Φ₂ Ω)
    (hsq : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2) :
    (∀ z ∈ Ω, Φ₂ z = Φ₁ z + (Φ₂ p - Φ₁ p)) ∨
    (∀ z ∈ Ω, Φ₂ z = (Φ₂ p + Φ₁ p) - Φ₁ z) := by
  have h₁an : AnalyticOnNhd ℂ (deriv Φ₁) Ω := (h₁.analyticOnNhd hΩ).deriv
  have h₂an : AnalyticOnNhd ℂ (deriv Φ₂) Ω := (h₂.analyticOnNhd hΩ).deriv
  have hprod : ∀ z ∈ Ω, (deriv Φ₂ z - deriv Φ₁ z) * (deriv Φ₂ z + deriv Φ₁ z) = 0 :=
    fun z hz => by linear_combination hsq z hz
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (h₂an.sub h₁an) (h₂an.add h₁an)
    hprod hconn with h0 | h0
  · left
    have hzero := EqOn_zero_of_deriv_eq_zero hΩ hconn
      (f := fun z => Φ₂ z - Φ₁ z - (Φ₂ p - Φ₁ p)) ((h₂.sub h₁).sub_const _) ?_ hp (by ring)
    · intro z hz
      have := hzero hz
      simp only [Pi.zero_apply] at this
      linear_combination this
    · intro z hz
      have hd₂ : DifferentiableAt ℂ Φ₂ z := h₂.differentiableAt (hΩ.mem_nhds hz)
      have hd₁ : DifferentiableAt ℂ Φ₁ z := h₁.differentiableAt (hΩ.mem_nhds hz)
      show deriv (fun w => (Φ₂ - Φ₁) w - (Φ₂ p - Φ₁ p)) z = 0
      rw [((hd₂.hasDerivAt.sub hd₁.hasDerivAt).sub_const _).deriv]
      have := h0 z hz
      simpa using this
  · right
    have hzero := EqOn_zero_of_deriv_eq_zero hΩ hconn
      (f := fun z => Φ₂ z + Φ₁ z - (Φ₂ p + Φ₁ p)) ((h₂.add h₁).sub_const _) ?_ hp (by ring)
    · intro z hz
      have := hzero hz
      simp only [Pi.zero_apply] at this
      linear_combination this
    · intro z hz
      have hd₂ : DifferentiableAt ℂ Φ₂ z := h₂.differentiableAt (hΩ.mem_nhds hz)
      have hd₁ : DifferentiableAt ℂ Φ₁ z := h₁.differentiableAt (hΩ.mem_nhds hz)
      show deriv (fun w => (Φ₂ + Φ₁) w - (Φ₂ p + Φ₁ p)) z = 0
      rw [((hd₂.hasDerivAt.add hd₁.hasDerivAt).sub_const _).deriv]
      have := h0 z hz
      simpa using this

/-- **Junction data extraction**: on a preconnected open overlap of two chart domains,
the branch classification yields the sign and real constant of the affine relation
between the developed real parts — the matching data of a development chain. -/
theorem junction_data {Φ₁ Φ₂ : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {p : ℂ} (hp : p ∈ Ω)
    (h₁ : DifferentiableOn ℂ Φ₁ Ω) (h₂ : DifferentiableOn ℂ Φ₂ Ω)
    (hsq : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2) :
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ z ∈ Ω, (Φ₂ z).re = ε * (Φ₁ z).re + c := by
  rcases open_branch_classification hΩ hconn hp h₁ h₂ hsq with h | h
  · refine ⟨1, (Φ₂ p - Φ₁ p).re, Or.inl rfl, fun z hz => ?_⟩
    rw [h z hz]
    simp [Complex.add_re, Complex.sub_re]
  · refine ⟨-1, (Φ₂ p + Φ₁ p).re, Or.inr rfl, fun z hz => ?_⟩
    rw [h z hz]
    simp [Complex.add_re, Complex.sub_re]
    ring


/-- Postcomposition with a map Lipschitz on a set containing the track preserves
absolute continuity on a general interval, for any metric target. -/
theorem lipschitzOnWith_comp_ac_interval {X : Type*} [PseudoMetricSpace X]
    {l : ℂ → X} {S : Set ℂ} {K : ℝ≥0} (hl : LipschitzOnWith K l S) {γ : ℝ → ℂ}
    {a b : ℝ} (hac : AbsolutelyContinuousOnInterval γ a b)
    (htr : ∀ t ∈ Set.uIcc a b, γ t ∈ S) :
    AbsolutelyContinuousOnInterval (l ∘ γ) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hac ⊢
  intro ε hε
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hac (ε / ((K : ℝ) + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hkey := hδ' E hE hlen
  have hmem : ∀ i ∈ Finset.range E.1, γ (E.2 i).1 ∈ S ∧ γ (E.2 i).2 ∈ S := fun i hi =>
    ⟨htr _ (hE.1 i hi).1, htr _ (hE.1 i hi).2⟩
  simp only [Function.comp_apply]
  calc ∑ i ∈ Finset.range E.1, dist (l (γ (E.2 i).1)) (l (γ (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (γ (E.2 i).1) (γ (E.2 i).2) :=
        Finset.sum_le_sum fun i hi => hl.dist_le_mul _ (hmem i hi).1 _ (hmem i hi).2
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (γ (E.2 i).1) (γ (E.2 i).2) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * (ε / ((K : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hkey.le K.coe_nonneg
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
    _ = ε := by field_simp

/-- **Piece data from a chart**: a chart ball containing the compact track of an
absolutely continuous piece yields the three development-chain piece fields — absolute
continuity of the developed real part, the almost-everywhere density identity, and the
almost-everywhere chain rule. -/
theorem piece_data {q Φ : ℂ → ℂ} {σ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {r : ℝ}
    (hab : a ≤ b) (hΦd : DifferentiableOn ℂ Φ (Metric.ball z₀ r))
    (hΦq : ∀ z ∈ Metric.ball z₀ r, deriv Φ z ^ 2 = -q z)
    (hσc : ContinuousOn σ (Set.Icc a b))
    (hσac : AbsolutelyContinuousOnInterval σ a b)
    (htr : ∀ s ∈ Set.Icc a b, σ s ∈ Metric.ball z₀ r) :
    AbsolutelyContinuousOnInterval (fun s => (Φ (σ s)).re) a b ∧
    (∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      horizontalDensity q σ s = ENNReal.ofReal |(deriv (Φ ∘ σ) s).re|) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      deriv (fun s' => (Φ (σ s')).re) s = (deriv (Φ ∘ σ) s).re) := by
  -- shrink the track into a compact convex sub-ball
  have hKc : IsCompact (σ '' Set.Icc a b) := (isCompact_Icc.image_of_continuousOn hσc)
  have hKne : (σ '' Set.Icc a b).Nonempty :=
    ⟨σ a, Set.mem_image_of_mem σ (Set.left_mem_Icc.mpr hab)⟩
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hKc.exists_isMaxOn hKne
    ((continuous_id.dist continuous_const).continuousOn)
  set r' : ℝ := (dist x₀ z₀ + r) / 2 with hr'def
  have hd₀ : dist x₀ z₀ < r := Metric.mem_ball.mp (by
    obtain ⟨s, hs, rfl⟩ := hx₀K
    exact htr s hs)
  have hr'r : r' < r := by rw [hr'def]; linarith
  have hKsub : σ '' Set.Icc a b ⊆ Metric.closedBall z₀ r' := by
    rintro x ⟨s, hs, rfl⟩
    have h2 : dist (σ s) z₀ ≤ dist x₀ z₀ := hx₀max (Set.mem_image_of_mem σ hs)
    exact Metric.mem_closedBall.mpr (by rw [hr'def]; linarith)
  have hsubball : Metric.closedBall z₀ r' ⊆ Metric.ball z₀ r :=
    Metric.closedBall_subset_ball hr'r
  -- Lipschitz bound for the chart on the sub-ball
  have hderivcont : ContinuousOn (deriv Φ) (Metric.ball z₀ r) :=
    ((hΦd.analyticOnNhd Metric.isOpen_ball).deriv).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ r').exists_bound_of_continuousOn
    (hderivcont.mono hsubball)
  have hlip : LipschitzOnWith C.toNNReal Φ (Metric.closedBall z₀ r') := by
    refine (convex_closedBall z₀ r').lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => ((hΦd.differentiableAt
        (Metric.isOpen_ball.mem_nhds (hsubball hz))).hasDerivAt).hasDerivWithinAt)
      fun z hz => ?_
    rw [← norm_toNNReal]
    exact Real.toNNReal_mono (hC z hz)
  have hAC : AbsolutelyContinuousOnInterval (fun s => (Φ (σ s)).re) a b := by
    have hrelip : LipschitzOnWith (‖Complex.reCLM‖₊ * C.toNNReal)
        (fun z => (Φ z).re) (Metric.closedBall z₀ r') :=
      Complex.reCLM.lipschitz.comp_lipschitzOnWith hlip
    exact lipschitzOnWith_comp_ac_interval hrelip hσac fun s hs =>
      hKsub (Set.mem_image_of_mem σ ((Set.uIcc_of_le hab) ▸ hs))
  -- almost-everywhere differentiability of the piece
  have hdiffae : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), DifferentiableAt ℝ σ s := by
    have h := hσac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    rw [Set.uIcc_of_le hab] at h
    exact (ae_restrict_iff' measurableSet_Icc).mpr h
  have hmemae : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), s ∈ Set.Icc a b :=
    ae_restrict_mem measurableSet_Icc
  refine ⟨hAC, ?_, ?_⟩
  · filter_upwards [hdiffae, hmemae] with s hdiff hmem
    have hball := htr s hmem
    have hΦat : HasDerivAt Φ (deriv Φ (σ s)) (σ s) :=
      (hΦd.differentiableAt (Metric.isOpen_ball.mem_nhds hball)).hasDerivAt
    have hcomp := HasDerivAt.comp (h := σ) s hΦat hdiff.hasDerivAt
    exact horizontalDensity_eq_re_developed (hΦq _ hball) hcomp.deriv
  · filter_upwards [hdiffae, hmemae] with s hdiff hmem
    have hball := htr s hmem
    have hΦat : HasDerivAt Φ (deriv Φ (σ s)) (σ s) :=
      (hΦd.differentiableAt (Metric.isOpen_ball.mem_nhds hball)).hasDerivAt
    have hcomp := HasDerivAt.comp (h := σ) s hΦat hdiff.hasDerivAt
    have hre : HasDerivAt (fun s' => (Φ (σ s')).re)
        ((deriv Φ (σ s) * deriv σ s).re) s := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hcomp
      simpa using this
    rw [hre.deriv, hcomp.deriv]

/-- Degenerate intervals carry every almost-everywhere property. -/
theorem ae_degenerate (P : ℝ → Prop) (c : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc c c)), P s := by
  have h0 : volume.restrict (Set.Icc c c) = 0 := by
    rw [Set.Icc_self, Measure.restrict_eq_zero]
    exact measure_singleton c
  rw [h0]
  simp

/-- Absolute continuity on a degenerate interval. -/
theorem ac_degenerate (f : ℝ → ℂ → ℝ) (g : ℝ → ℝ) (c : ℝ) :
    AbsolutelyContinuousOnInterval g c c := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨1, one_pos, fun E hE _ => ?_⟩
  have hpt : ∀ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) = 0 := by
    intro i hi
    have h1 := (hE.1 i hi).1
    have h2 := (hE.1 i hi).2
    rw [Set.uIcc_self, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2, dist_self]
  rw [Finset.sum_congr rfl hpt]
  simpa using hε

/-- A convex open overlap of two chart balls carries junction data at any common
point. -/
theorem ball_junction {q Φ₁ Φ₂ : ℂ → ℂ} {x₁ x₂ : ℂ} {r₁ r₂ : ℝ}
    (h₁ : DifferentiableOn ℂ Φ₁ (Metric.ball x₁ r₁))
    (h₂ : DifferentiableOn ℂ Φ₂ (Metric.ball x₂ r₂))
    (hq₁ : ∀ z ∈ Metric.ball x₁ r₁, deriv Φ₁ z ^ 2 = -q z)
    (hq₂ : ∀ z ∈ Metric.ball x₂ r₂, deriv Φ₂ z ^ 2 = -q z)
    {p : ℂ} (hp₁ : p ∈ Metric.ball x₁ r₁) (hp₂ : p ∈ Metric.ball x₂ r₂) :
    ∃ ε c : ℝ, (ε = 1 ∨ ε = -1) ∧ (Φ₂ p).re = ε * (Φ₁ p).re + c := by
  set Ω : Set ℂ := Metric.ball x₁ r₁ ∩ Metric.ball x₂ r₂ with hΩdef
  have hΩopen : IsOpen Ω := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hΩconn : IsPreconnected Ω :=
    ((convex_ball x₁ r₁).inter (convex_ball x₂ r₂)).isPreconnected
  have hpΩ : p ∈ Ω := ⟨hp₁, hp₂⟩
  have hsq : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2 := fun z hz => by
    rw [hq₂ z hz.2, hq₁ z hz.1]
  obtain ⟨ε, c, hε, hrel⟩ := junction_data hΩopen hΩconn hpΩ
    (h₁.mono Set.inter_subset_left) (h₂.mono Set.inter_subset_right) hsq
  exact ⟨ε, c, hε, hrel p hpΩ⟩

set_option maxHeartbeats 400000 in
-- Heartbeats: the partition arithmetic and chart-choice assembly elaborate large terms.
/-- **Chain existence**: an absolutely continuous path whose compact track carries
full-disc natural charts of `−q`, with prescribed charts at the two endpoints, admits a
development chain from `0` to `1` whose first and last frames are the prescribed ones. -/
theorem exists_devChain {q : ℂ → ℂ} {σ : ℝ → ℂ} {Φs Φe : ℂ → ℂ} {rs re : ℝ}
    (hσc : ContinuousOn σ (Set.Icc 0 1))
    (hσac : AbsolutelyContinuousOnInterval σ 0 1)
    (hatlas : ∀ x ∈ σ '' Set.Icc 0 1, ∃ r > 0, ∃ Φ : ℂ → ℂ,
      DifferentiableOn ℂ Φ (Metric.ball x r) ∧
      ∀ z ∈ Metric.ball x r, deriv Φ z ^ 2 = -q z)
    (hrs : 0 < rs) (hre : 0 < re)
    (hΦs : DifferentiableOn ℂ Φs (Metric.ball (σ 0) rs))
    (hΦsq : ∀ z ∈ Metric.ball (σ 0) rs, deriv Φs z ^ 2 = -q z)
    (hΦe : DifferentiableOn ℂ Φe (Metric.ball (σ 1) re))
    (hΦeq : ∀ z ∈ Metric.ball (σ 1) re, deriv Φe z ^ 2 = -q z) :
    ∃ n : ℕ, ∃ D : DevChain q σ (n + 1),
      D.t 0 = 0 ∧ D.t (n + 1) = 1 ∧ D.Φ 0 = Φs ∧ D.Φ n = Φe := by
  classical
  set K : Set ℂ := σ '' Set.Icc 0 1 with hKdef
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hσc
  -- choose an atlas chart at every track point
  choose! rx hrx Φx hΦx hΦxq using hatlas
  -- Lebesgue number for the chart cover
  obtain ⟨δe, hδe, hleb⟩ := lebesgue_number_lemma_of_emetric (s := K)
    (c := fun x : K => Metric.ball (x : ℂ) (rx x)) hKc
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrx x hx)⟩)
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδe
  have hδ'pos : (0 : ℝ) < δ' := by exact_mod_cast hδ'0
  have hballs : ∀ x ∈ K, ∃ y : K, Metric.ball x (δ' : ℝ) ⊆ Metric.ball (y : ℂ) (rx y) := by
    intro x hx
    obtain ⟨y, hy⟩ := hleb x hx
    refine ⟨y, ?_⟩
    intro w hw
    apply hy
    rw [Metric.mem_eball]
    exact lt_trans (edist_lt_coe.mpr (Metric.mem_ball.mp hw)) hδ'
  -- uniform continuity modulus against the Lebesgue number
  have hunif : UniformContinuousOn σ (Set.Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hσc
  obtain ⟨Δ, hΔ0, hΔ⟩ := Metric.uniformContinuousOn_iff.mp hunif (δ' : ℝ) hδ'pos
  -- the partition
  set m : ℕ := ⌈2 / Δ⌉₊ + 1 with hmdef
  set n : ℕ := m + 1 with hndef
  set t : ℕ → ℝ := fun i => if i = 0 then 0 else min ((i - 1 : ℕ) * (Δ / 2)) 1 with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have ht1 : t 1 = 0 := by simp [htdef]
  have htmem : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    by_cases h : i = 0
    · simp [htdef, h]
    · simp only [htdef, if_neg h]
      constructor
      · exact le_min (by positivity) zero_le_one
      · exact min_le_right _ _
  have htlast : ∀ i, m + 1 ≤ i → t i = 1 := by
    intro i hi
    have hne : i ≠ 0 := by omega
    simp only [htdef, if_neg hne]
    rw [min_eq_right]
    have h2 : (2 : ℝ) / Δ ≤ ⌈2 / Δ⌉₊ := Nat.le_ceil _
    have hm : (m : ℝ) ≤ (i - 1 : ℕ) := by
      have : m ≤ i - 1 := by omega
      exact_mod_cast this
    have hmΔ : (2 : ℝ) / Δ * (Δ / 2) ≤ (i - 1 : ℕ) * (Δ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc (2 : ℝ) / Δ ≤ ⌈2 / Δ⌉₊ := h2
        _ ≤ (m : ℝ) := by exact_mod_cast Nat.le_succ _
        _ ≤ _ := hm
    calc (1 : ℝ) = 2 / Δ * (Δ / 2) := by field_simp
      _ ≤ _ := hmΔ
  have htmono : ∀ i, t i ≤ t (i + 1) := by
    intro i
    by_cases h : i = 0
    · rw [h, ht0]; exact (htmem 1).1
    · simp only [htdef, if_neg h, if_neg (Nat.succ_ne_zero i)]
      have : ((i - 1 : ℕ) : ℝ) ≤ ((i + 1 - 1 : ℕ) : ℝ) := by
        have : i - 1 ≤ i + 1 - 1 := by omega
        exact_mod_cast this
      exact min_le_min (mul_le_mul_of_nonneg_right this (by positivity)) le_rfl
  have htmesh : ∀ i, t (i + 1) - t i ≤ Δ / 2 := by
    intro i
    by_cases h : i = 0
    · rw [h, ht0, ht1]; simp; positivity
    · simp only [htdef, if_neg h, if_neg (Nat.succ_ne_zero i)]
      have hstep : ((i + 1 - 1 : ℕ) : ℝ) * (Δ / 2) = ((i - 1 : ℕ) : ℝ) * (Δ / 2) + Δ / 2 := by
        have : (i + 1 - 1 : ℕ) = (i - 1) + 1 := by omega
        rw [this]
        push_cast
        ring
      have h1 : min (((i + 1 - 1 : ℕ) : ℝ) * (Δ / 2)) 1
          ≤ min (((i - 1 : ℕ) : ℝ) * (Δ / 2)) 1 + Δ / 2 := by
        rw [hstep]
        rcases le_or_gt (((i - 1 : ℕ) : ℝ) * (Δ / 2)) 1 with hc | hc
        · rw [min_eq_left hc]
          exact le_trans (min_le_left _ _) (by linarith)
        · rw [min_eq_right hc.le]
          have : min (((i - 1 : ℕ) : ℝ) * (Δ / 2) + Δ / 2) 1 ≤ 1 := min_le_right _ _
          linarith
      linarith
  -- chart data for every piece
  have hpieces : ∀ i : ℕ, ∃ x : ℂ, ∃ ρ : ℝ, ∃ Φ : ℂ → ℂ,
      0 < ρ ∧ DifferentiableOn ℂ Φ (Metric.ball x ρ) ∧
      (∀ z ∈ Metric.ball x ρ, deriv Φ z ^ 2 = -q z) ∧
      (∀ s ∈ Set.Icc (t i) (t (i + 1)), σ s ∈ Metric.ball x ρ) ∧
      (i = 0 → Φ = Φs) ∧ (i = m + 1 → Φ = Φe) := by
    intro i
    rcases eq_or_ne i 0 with h0 | h0
    · subst h0
      refine ⟨σ 0, rs, Φs, hrs, hΦs, hΦsq, ?_, fun _ => rfl,
        fun hc => absurd hc (by omega)⟩
      intro s hs
      rw [ht0, ht1] at hs
      rw [le_antisymm hs.2 hs.1]
      exact Metric.mem_ball_self hrs
    rcases le_or_gt (m + 1) i with hge | hlt
    · have hti : t i = 1 := htlast i hge
      have hti1 : t (i + 1) = 1 := htlast _ (by omega)
      refine ⟨σ 1, re, Φe, hre, hΦe, hΦeq, ?_, fun hc => absurd hc h0, fun _ => rfl⟩
      intro s hs
      rw [hti, hti1] at hs
      rw [le_antisymm hs.2 hs.1]
      exact Metric.mem_ball_self hre
    · have htiK : σ (t i) ∈ K := Set.mem_image_of_mem σ (htmem i)
      obtain ⟨y, hy⟩ := hballs (σ (t i)) htiK
      refine ⟨(y : ℂ), rx y, Φx y, hrx y y.2, hΦx y y.2, hΦxq y y.2, ?_,
        fun hc => absurd hc h0, fun hc => absurd hc (by omega)⟩
      intro s hs
      apply hy
      rw [Metric.mem_ball]
      have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_trans (htmem i).1 hs.1, le_trans hs.2 (htmem (i + 1)).2⟩
      have hd : dist s (t i) < Δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        have h1 := htmesh i
        have h2 := hs.2
        linarith
      exact hΔ s hs01 (t i) (htmem i) hd
  choose xf ρf Φf hρf hΦfd hΦfq htrf hguard0 hguardn using hpieces
  -- junction data
  have hjunc : ∀ i : ℕ, ∃ e c : ℝ, (e = 1 ∨ e = -1) ∧
      (i + 1 < m + 2 →
        (Φf (i + 1) (σ (t (i + 1)))).re = e * (Φf i (σ (t (i + 1)))).re + c) := by
    intro i
    rcases lt_or_ge (i + 1) (m + 2) with hlt | hge
    · have hp1 : σ (t (i + 1)) ∈ Metric.ball (xf i) (ρf i) :=
        htrf i _ (Set.right_mem_Icc.mpr (htmono i))
      have hp2 : σ (t (i + 1)) ∈ Metric.ball (xf (i + 1)) (ρf (i + 1)) :=
        htrf (i + 1) _ (Set.left_mem_Icc.mpr (htmono (i + 1)))
      obtain ⟨e, c, hsgn, hrel⟩ := ball_junction (hΦfd i) (hΦfd (i + 1))
        (hΦfq i) (hΦfq (i + 1)) hp1 hp2
      exact ⟨e, c, hsgn, fun _ => hrel⟩
    · exact ⟨1, 0, Or.inl rfl, fun hc => absurd hc (by omega)⟩
  choose εf cf hsgnf hmatchf using hjunc
  have hsub : ∀ i : ℕ, Set.Icc (t i) (t (i + 1)) ⊆ Set.Icc (0 : ℝ) 1 :=
    fun i => Set.Icc_subset_Icc (htmem i).1 (htmem (i + 1)).2
  have hsubu : ∀ i : ℕ, Set.uIcc (t i) (t (i + 1)) ⊆ Set.uIcc (0 : ℝ) 1 := by
    intro i
    rw [Set.uIcc_of_le (htmono i), Set.uIcc_of_le zero_le_one]
    exact hsub i
  refine ⟨m + 1, ⟨t, Φf, εf, cf, fun i _ => htmono i, ?_, ?_, ?_, hsgnf,
    fun i hi => hmatchf i hi⟩, ht0, htlast (m + 1 + 1) (by omega), hguard0 0 rfl,
    hguardn (m + 1) rfl⟩
  · intro i _
    exact (piece_data (htmono i) (hΦfd i) (hΦfq i) (hσc.mono (hsub i))
      (hσac.mono (hsubu i)) (htrf i)).2.1
  · intro i _
    exact (piece_data (htmono i) (hΦfd i) (hΦfq i) (hσc.mono (hsub i))
      (hσac.mono (hsubu i)) (htrf i)).1
  · intro i _
    exact (piece_data (htmono i) (hΦfd i) (hΦfq i) (hσc.mono (hsub i))
      (hσac.mono (hsubu i)) (htrf i)).2.2

/-- **The minimal-variation estimate in chain form**: for an absolutely continuous path
whose compact track carries natural charts of `−q`, with prescribed charts at the two
endpoints, the horizontal variation deposited along the path dominates the developed
displacement between the prescribed end frames, pulled back through some junction
chain. -/
theorem mv_lower_bound {q : ℂ → ℂ} {σ : ℝ → ℂ} {Φs Φe : ℂ → ℂ} {rs re : ℝ}
    (hσc : ContinuousOn σ (Set.Icc 0 1))
    (hσac : AbsolutelyContinuousOnInterval σ 0 1)
    (hatlas : ∀ x ∈ σ '' Set.Icc 0 1, ∃ r > 0, ∃ Φ : ℂ → ℂ,
      DifferentiableOn ℂ Φ (Metric.ball x r) ∧
      ∀ z ∈ Metric.ball x r, deriv Φ z ^ 2 = -q z)
    (hrs : 0 < rs) (hre : 0 < re)
    (hΦs : DifferentiableOn ℂ Φs (Metric.ball (σ 0) rs))
    (hΦsq : ∀ z ∈ Metric.ball (σ 0) rs, deriv Φs z ^ 2 = -q z)
    (hΦe : DifferentiableOn ℂ Φe (Metric.ball (σ 1) re))
    (hΦeq : ∀ z ∈ Metric.ball (σ 1) re, deriv Φe z ^ 2 = -q z) :
    ∃ n : ℕ, ∃ D : DevChain q σ (n + 1),
      ENNReal.ofReal |chainPull D.ε D.c n ((Φe (σ 1)).re) - (Φs (σ 0)).re|
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1, horizontalDensity q σ s := by
  obtain ⟨n, D, ht0, htn, hΦ0, hΦn⟩ :=
    exists_devChain hσc hσac hatlas hrs hre hΦs hΦsq hΦe hΦeq
  refine ⟨n, D, ?_⟩
  have h := devChain_variation_lb n D
  rw [ht0, htn, hΦ0, hΦn] at h
  exact h


/-- **The symmetrized vertical-flow interface**: an almost-everywhere defined unit-speed
motion along the vertical foliation of `q`, consumed through both leaf orientations at
once. The leafwise lower bound holds separately for each orientation, while the two
Cauchy–Schwarz factor integrals are invariant only after summing the two orientations —
the deck transformations of a nonorientable vertical foliation exchange the two leaf
orientations, so only the symmetrized integrals descend from the orientation double
cover. -/
structure VerticalFlowDataSym (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (q : QuadraticDifferential Γ) (h : ℂ → ℂ) (κ : ℝ) where
  /-- The uniform displacement constant. -/
  C : ℝ≥0∞
  /-- Finiteness of the displacement constant. -/
  hC : C ≠ ⊤
  /-- The flow map: time, then start point. -/
  flow : ℝ → ℂ → ℂ
  /-- The invariant full-measure set of regular start points. -/
  good : Set ℂ
  /-- Almost every point of the upper half plane is regular. -/
  good_ae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good
  /-- Joint measurability of the composed image density. -/
  meas_D : Measurable fun p : ℝ × ℂ => rsDensity q h (flow p.1 p.2)
  /-- Joint measurability of the composed first Cauchy–Schwarz factor. -/
  meas_U : Measurable fun p : ℝ × ℂ => rsU q h κ (flow p.1 p.2)
  /-- Joint measurability of the composed floored weight. -/
  meas_W : Measurable fun p : ℝ × ℂ => rsWeightM q h κ (flow p.1 p.2)
  /-- **The leafwise estimate**, forward orientation. -/
  leaf_lb : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
    ENNReal.ofReal T ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow t z)) + 2 * C
  /-- **The leafwise estimate**, backward orientation. -/
  leaf_lb_neg : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
    ENNReal.ofReal T ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow (-t) z)) + 2 * C
  /-- **Symmetrized flow invariance** of the first factor against the `|q|` area. -/
  invar_U : ∀ t : ℝ,
    ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      (rsU q h κ (flow t z) + rsU q h κ (flow (-t) z)) * ‖q z‖ₑ
      = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        rsU q h κ z * ‖q z‖ₑ
  /-- **Symmetrized flow invariance** of the floored weight against the `|q|` area. -/
  invar_W : ∀ t : ℝ,
    ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      (rsWeightM q h κ (flow t z) + rsWeightM q h κ (flow (-t) z)) * ‖q z‖ₑ
      = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        rsWeightM q h κ z * ‖q z‖ₑ

/-- Two-term arithmetic–geometric mean inequality in `ℝ≥0∞`. -/
theorem rpow_half_mul_le_add {u v : ℝ≥0∞} : (u * v) ^ (1 / 2 : ℝ) * 2 ≤ u + v := by
  rcases eq_or_ne u ⊤ with hu | hu
  · rcases eq_or_ne v 0 with hv | hv
    · simp [hu, hv]
    · rw [hu, top_add]; exact le_top
  rcases eq_or_ne v ⊤ with hv | hv
  · rcases eq_or_ne u 0 with hu0 | hu0
    · simp [hv, hu0]
    · rw [hv, add_top]; exact le_top
  lift u to ℝ≥0 using hu
  lift v to ℝ≥0 using hv
  rw [← ENNReal.coe_mul, ← ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0:ℝ) ≤ 1 / 2),
    ← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  have hgm := NNReal.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 2) (w₂ := 1 / 2)
    (p₁ := u) (p₂ := v) (by norm_num)
  have hco : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hco] at hgm
  rw [NNReal.mul_rpow]
  calc u ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) * 2 ≤ (1 / 2 * u + 1 / 2 * v) * 2 :=
        mul_le_mul_left hgm 2
    _ = u + v := by
        rw [add_mul, mul_comm (1 / 2 * u) 2, mul_comm (1 / 2 * v) 2, ← mul_assoc,
          ← mul_assoc]
        norm_num

/-- Two-term Cauchy–Schwarz for square roots in `ℝ≥0∞`: the sum of geometric means is
dominated by the geometric mean of the sums. -/
theorem sqrt_add_sqrt_le {p₁ q₁ p₂ q₂ : ℝ≥0∞} :
    (p₁ * q₁) ^ (1 / 2 : ℝ) + (p₂ * q₂) ^ (1 / 2 : ℝ)
      ≤ (p₁ + p₂) ^ (1 / 2 : ℝ) * (q₁ + q₂) ^ (1 / 2 : ℝ) := by
  refine le_sqrt_mul_sqrt (x := (p₁ * q₁) ^ (1 / 2 : ℝ) + (p₂ * q₂) ^ (1 / 2 : ℝ))
    (y := p₁ + p₂) (z := q₁ + q₂) ?_
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
    norm_num
  have hcross : (p₁ * q₁) ^ (1 / 2 : ℝ) * (p₂ * q₂) ^ (1 / 2 : ℝ) * 2
      ≤ p₁ * q₂ + p₂ * q₁ := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
      show p₁ * q₁ * (p₂ * q₂) = p₁ * q₂ * (p₂ * q₁) by ring]
    exact rpow_half_mul_le_add
  calc ((p₁ * q₁) ^ (1 / 2 : ℝ) + (p₂ * q₂) ^ (1 / 2 : ℝ)) ^ 2
      = (p₁ * q₁) ^ (1 / 2 : ℝ) * (p₂ * q₂) ^ (1 / 2 : ℝ) * 2
        + ((p₁ * q₁) ^ (1 / 2 : ℝ)) ^ 2 + ((p₂ * q₂) ^ (1 / 2 : ℝ)) ^ 2 := by ring
    _ ≤ (p₁ * q₂ + p₂ * q₁) + (p₁ * q₁) + (p₂ * q₂) := by
        rw [hsq, hsq]
        exact add_le_add (add_le_add hcross le_rfl) le_rfl
    _ = (p₁ + p₂) * (q₁ + q₂) := by ring

/-- **The symmetrized leafwise weighted Cauchy–Schwarz estimate**: on a regular leaf the
doubled elapsed time is controlled by the geometric mean of the two orientation-summed
Cauchy–Schwarz factors plus the doubled displacement defect. -/
theorem leaf_pointwise_sym {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {q : QuadraticDifferential Γ} {h : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (fd : VerticalFlowDataSym Γ q h κ) {z : ℂ} (hz : z ∈ fd.good)
    {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal T + ENNReal.ofReal T
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) T,
            (rsU q h κ (fd.flow t z) + rsU q h κ (fd.flow (-t) z))) ^ (1 / 2 : ℝ)
        * (∫⁻ t in Set.Icc (0 : ℝ) T,
            (rsWeightM q h κ (fd.flow t z) + rsWeightM q h κ (fd.flow (-t) z)))
          ^ (1 / 2 : ℝ)
        + (2 * fd.C + 2 * fd.C) := by
  have hfp : Measurable fun t => rsDensity q h (fd.flow t z) :=
    fd.meas_D.comp (measurable_id.prodMk measurable_const)
  have hfm : Measurable fun t => rsDensity q h (fd.flow (-t) z) :=
    fd.meas_D.comp (measurable_neg.prodMk measurable_const)
  have hwp : Measurable fun t => rsWeightM q h κ (fd.flow t z) :=
    fd.meas_W.comp (measurable_id.prodMk measurable_const)
  have hwm : Measurable fun t => rsWeightM q h κ (fd.flow (-t) z) :=
    fd.meas_W.comp (measurable_neg.prodMk measurable_const)
  have hcsp := lintegral_sq_le_weighted (μ := volume.restrict (Set.Icc (0 : ℝ) T))
    hfp.aemeasurable hwp.aemeasurable
    (fun t => (rsWeightM_pos_ne_top q h hκ _).1)
    (fun t => (rsWeightM_pos_ne_top q h hκ _).2)
  have hcsm := lintegral_sq_le_weighted (μ := volume.restrict (Set.Icc (0 : ℝ) T))
    hfm.aemeasurable hwm.aemeasurable
    (fun t => (rsWeightM_pos_ne_top q h hκ _).1)
    (fun t => (rsWeightM_pos_ne_top q h hκ _).2)
  simp only [rsU]
  rw [lintegral_add_left ((hfp.pow_const 2).mul hwp.inv), lintegral_add_left hwp]
  have hbp : ENNReal.ofReal T
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (fd.flow t z) ^ 2
            * (rsWeightM q h κ (fd.flow t z))⁻¹) ^ (1 / 2 : ℝ)
        * (∫⁻ t in Set.Icc (0 : ℝ) T, rsWeightM q h κ (fd.flow t z)) ^ (1 / 2 : ℝ)
        + 2 * fd.C :=
    (fd.leaf_lb z hz T hT).trans (add_le_add (le_sqrt_mul_sqrt hcsp) le_rfl)
  have hbm : ENNReal.ofReal T
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (fd.flow (-t) z) ^ 2
            * (rsWeightM q h κ (fd.flow (-t) z))⁻¹) ^ (1 / 2 : ℝ)
        * (∫⁻ t in Set.Icc (0 : ℝ) T, rsWeightM q h κ (fd.flow (-t) z)) ^ (1 / 2 : ℝ)
        + 2 * fd.C :=
    (fd.leaf_lb_neg z hz T hT).trans (add_le_add (le_sqrt_mul_sqrt hcsm) le_rfl)
  set aP := ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (fd.flow t z) ^ 2
    * (rsWeightM q h κ (fd.flow t z))⁻¹ with haP
  set aM := ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (fd.flow (-t) z) ^ 2
    * (rsWeightM q h κ (fd.flow (-t) z))⁻¹ with haM
  set bP := ∫⁻ t in Set.Icc (0 : ℝ) T, rsWeightM q h κ (fd.flow t z) with hbP
  set bM := ∫⁻ t in Set.Icc (0 : ℝ) T, rsWeightM q h κ (fd.flow (-t) z) with hbM
  have hstep : aP ^ (1 / 2 : ℝ) * bP ^ (1 / 2 : ℝ) + aM ^ (1 / 2 : ℝ) * bM ^ (1 / 2 : ℝ)
      ≤ (aP + aM) ^ (1 / 2 : ℝ) * (bP + bM) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2),
      ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
    exact sqrt_add_sqrt_le
  calc ENNReal.ofReal T + ENNReal.ofReal T
      ≤ (aP ^ (1 / 2 : ℝ) * bP ^ (1 / 2 : ℝ) + 2 * fd.C)
        + (aM ^ (1 / 2 : ℝ) * bM ^ (1 / 2 : ℝ) + 2 * fd.C) := add_le_add hbp hbm
    _ = (aP ^ (1 / 2 : ℝ) * bP ^ (1 / 2 : ℝ) + aM ^ (1 / 2 : ℝ) * bM ^ (1 / 2 : ℝ))
        + (2 * fd.C + 2 * fd.C) := by ring
    _ ≤ (aP + aM) ^ (1 / 2 : ℝ) * (bP + bM) ^ (1 / 2 : ℝ) + (2 * fd.C + 2 * fd.C) :=
        add_le_add hstep le_rfl

/-- Square root of a doubled product pair: `√((2A)(2B)) = 2√(AB)` in `ℝ≥0∞`. -/
theorem four_rpow_half {A B : ℝ≥0∞} :
    (2 * A * (2 * B)) ^ (1 / 2 : ℝ) = 2 * (A * B) ^ (1 / 2 : ℝ) := by
  rw [show 2 * A * (2 * B) = 4 * (A * B) by ring,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  congr 1
  rw [show (4 : ℝ≥0∞) = 2 ^ (2 : ℕ) by norm_num, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The Reich–Strebel main inequality from symmetrized flow data**: the two-orientation
flow interface still produces the Reich–Strebel bound — each orientation contributes its
leafwise estimate, and only the orientation-symmetrized invariances are consumed. -/
theorem reich_strebel_of_flowDataSym
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (fd : VerticalFlowDataSym Γ q h κ)
    (hcov : ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) ≤ q.l1Norm) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  set ω : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hωdef
  have hsubH : ω ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  set N : ℝ≥0∞ := q.l1Norm with hNdef
  have hNint : N = ∫⁻ z in ω, ‖q z‖ₑ := rfl
  have hN : N ≠ ⊤ := q.l1Norm_ne_top hΓ hfree hcc
  set A : ℝ≥0∞ := ∫⁻ z in ω, rsU q h κ z * ‖q z‖ₑ with hAdef
  set B : ℝ≥0∞ := ∫⁻ z in ω, rsWeightM q h κ z * ‖q z‖ₑ with hBdef
  have haegood : ∀ᵐ z ∂(volume.restrict ω), z ∈ fd.good :=
    ae_restrict_of_ae_restrict_of_subset hsubH fd.good_ae
  have haeW : ∀ᵐ z ∂(volume.restrict ω),
      rsWeightM q h κ z = rsWeight q h z :=
    ae_restrict_of_ae_restrict_of_subset hsubH (ae_rsWeightM_eq hqc hκ)
  have haeU : ∀ᵐ z ∂(volume.restrict ω),
      rsU q h κ z * ‖q z‖ₑ
        ≤ ‖q (h z)‖ₑ * ENNReal.ofReal ((fderiv ℝ h z).det) :=
    ae_restrict_of_ae_restrict_of_subset hsubH (ae_rsU_mul_le hqc hκ)
  have hBI : B = ∫⁻ z in ω, ‖q z‖ₑ * ENNReal.ofReal
      (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
        / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
    calc B = ∫⁻ z in ω, rsWeight q h z * ‖q z‖ₑ :=
          lintegral_congr_ae (haeW.mono fun z hz => by
            show rsWeightM q h κ z * ‖q z‖ₑ = rsWeight q h z * ‖q z‖ₑ
            rw [hz])
      _ = _ := lintegral_congr fun z => by
          show rsWeight q h z * ‖q z‖ₑ = _
          rw [rsWeight, mul_comm]
  have hAN : A ≤ N := (lintegral_mono_ae haeU).trans hcov
  have hqe : Measurable fun z : ℂ => ‖q z‖ₑ := q.measurable.enorm
  have hFU : Measurable fun p : ℝ × ℂ =>
      rsU q h κ (fd.flow p.1 p.2) + rsU q h κ (fd.flow (-p.1) p.2) :=
    fd.meas_U.add (fd.meas_U.comp ((measurable_fst.neg).prodMk measurable_snd))
  have hFW : Measurable fun p : ℝ × ℂ =>
      rsWeightM q h κ (fd.flow p.1 p.2) + rsWeightM q h κ (fd.flow (-p.1) p.2) :=
    fd.meas_W.add (fd.meas_W.comp ((measurable_fst.neg).prodMk measurable_snd))
  have hCC : (2 * fd.C + 2 * fd.C) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top fd.hC,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top fd.hC⟩
  have key : ∀ T : ℝ, 0 < T →
      (ENNReal.ofReal T + ENNReal.ofReal T) * N
        ≤ ENNReal.ofReal T * (2 * ((A * B) ^ (1 / 2 : ℝ)))
          + (2 * fd.C + 2 * fd.C) * N := by
    intro T hT
    set aT : ℂ → ℝ≥0∞ := fun z => ∫⁻ t in Set.Icc (0 : ℝ) T,
      (rsU q h κ (fd.flow t z) + rsU q h κ (fd.flow (-t) z)) with haTdef
    set bT : ℂ → ℝ≥0∞ := fun z => ∫⁻ t in Set.Icc (0 : ℝ) T,
      (rsWeightM q h κ (fd.flow t z) + rsWeightM q h κ (fd.flow (-t) z)) with hbTdef
    have haTmeas : Measurable aT := (hFU.comp measurable_swap).lintegral_prod_right'
    have hbTmeas : Measurable bT := (hFW.comp measurable_swap).lintegral_prod_right'
    have hXmeas : Measurable fun z => aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) :=
      (ENNReal.continuous_rpow_const.measurable.comp haTmeas).mul
        (ENNReal.continuous_rpow_const.measurable.comp hbTmeas)
    have hstep1 : (ENNReal.ofReal T + ENNReal.ofReal T) * N
        ≤ ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ := by
      rw [hNint, ← lintegral_const_mul' _ _
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)]
      refine lintegral_mono_ae ?_
      filter_upwards [haegood] with z hz
      exact mul_le_mul_left (leaf_pointwise_sym hκ fd hz hT) _
    have hstep2 : ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
          + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ
        = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
          + (2 * fd.C + 2 * fd.C) * N := by
      calc ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
              + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ
          = ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ
              + (2 * fd.C + 2 * fd.C) * ‖q z‖ₑ) := lintegral_congr fun z => add_mul _ _ _
        _ = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
              + ∫⁻ z in ω, (2 * fd.C + 2 * fd.C) * ‖q z‖ₑ :=
            lintegral_add_left (hXmeas.mul hqe) _
        _ = _ := by rw [lintegral_const_mul' _ _ hCC, ← hNint]
    have hstep3 : ∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ
        = ∫⁻ z in ω, (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) :=
      lintegral_congr fun z => (geom_mean_mul enorm_ne_top).symm
    have hstep4 : ∫⁻ z in ω,
        (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
        ≤ (∫⁻ z in ω, aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
          * (∫⁻ z in ω, bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) :=
      lintegral_sqrt_mul_sqrt_le ((haTmeas.mul hqe).aemeasurable)
        ((hbTmeas.mul hqe).aemeasurable)
    have hstep5 : ∫⁻ z in ω, aT z * ‖q z‖ₑ = ENNReal.ofReal T * (2 * A) :=
      fubini_invar q hFU (fun t => (fd.invar_U t).trans (by rw [← hAdef])) T
    have hstep6 : ∫⁻ z in ω, bT z * ‖q z‖ₑ = ENNReal.ofReal T * (2 * B) :=
      fubini_invar q hFW (fun t => (fd.invar_W t).trans (by rw [← hBdef])) T
    calc (ENNReal.ofReal T + ENNReal.ofReal T) * N
        ≤ ∫⁻ z in ω, (aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C)) * ‖q z‖ₑ := hstep1
      _ = (∫⁻ z in ω, aT z ^ (1 / 2 : ℝ) * bT z ^ (1 / 2 : ℝ) * ‖q z‖ₑ)
            + (2 * fd.C + 2 * fd.C) * N := hstep2
      _ = (∫⁻ z in ω, (aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ) * (bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ))
            + (2 * fd.C + 2 * fd.C) * N := by rw [hstep3]
      _ ≤ (∫⁻ z in ω, aT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
            * (∫⁻ z in ω, bT z * ‖q z‖ₑ) ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C) * N := add_le_add hstep4 le_rfl
      _ = (ENNReal.ofReal T * (2 * A)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal T * (2 * B)) ^ (1 / 2 : ℝ)
            + (2 * fd.C + 2 * fd.C) * N := by rw [hstep5, hstep6]
      _ = ENNReal.ofReal T * ((2 * A * (2 * B)) ^ (1 / 2 : ℝ))
            + (2 * fd.C + 2 * fd.C) * N := by
          rw [mul_rpow_half_mul ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal T * (2 * ((A * B) ^ (1 / 2 : ℝ)))
            + (2 * fd.C + 2 * fd.C) * N := by rw [four_rpow_half]
  have hK2 : (2 * fd.C + 2 * fd.C) * N ≠ ⊤ := ENNReal.mul_ne_top hCC hN
  have key2 : ∀ T : ℝ, 0 < T → ENNReal.ofReal T * (2 * N)
      ≤ ENNReal.ofReal T * (2 * ((A * B) ^ (1 / 2 : ℝ)))
        + (2 * fd.C + 2 * fd.C) * N := by
    intro T hT
    calc ENNReal.ofReal T * (2 * N)
        = (ENNReal.ofReal T + ENNReal.ofReal T) * N := by ring
      _ ≤ _ := key T hT
  have hNS2 : 2 * N ≤ 2 * ((A * B) ^ (1 / 2 : ℝ)) :=
    le_of_forall_ofReal_mul_le hK2 key2
  have hNS : N ≤ (A * B) ^ (1 / 2 : ℝ) :=
    (ENNReal.mul_le_mul_iff_right (by norm_num : (2:ℝ≥0∞) ≠ 0)
      ENNReal.ofNat_ne_top).mp hNS2
  have hfin : N ≤ (N * (∫⁻ z in ω, ‖q z‖ₑ * ENNReal.ofReal
      (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
        / (1 - ‖wirtingerQuotient h z‖ ^ 2)))) ^ (1 / 2 : ℝ) :=
    hNS.trans (ENNReal.rpow_le_rpow (mul_le_mul' hAN hBI.le) (by norm_num))
  exact le_of_le_sqrt_mul hN hfin

/-- **Wirtinger derivatives under a deck transformation**: for `h` commuting with the
Möbius map of `γ` near `z`, `∂h(γz) = e⁻² d² ∂h(z)` and `∂̄h(γz) = e⁻² conj(d²) ∂̄h(z)`,
where `d, e` are the Möbius denominators at `z` and at `h z`. -/
theorem wirtinger_moebius {h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    dz h (moebiusMap γ z)
        = (moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ z ^ 2 * dz h z
      ∧ dzbar h (moebiusMap γ z)
        = (moebiusDenom γ (h z) ^ 2)⁻¹ * conj (moebiusDenom γ z ^ 2) * dzbar h z := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hdM : HasDerivAt (moebiusMap γ) ((moebiusDenom γ z ^ 2)⁻¹) z :=
    hasDerivAt_moebiusMap_of_im_pos γ hz
  have hdMh : HasDerivAt (moebiusMap γ) ((moebiusDenom γ (h z) ^ 2)⁻¹) (h z) :=
    hasDerivAt_moebiusMap_of_im_pos γ hhz
  have hγC : DifferentiableAt ℂ (moebiusMap γ) z := hdM.differentiableAt
  have hγCh : DifferentiableAt ℂ (moebiusMap γ) (h z) := hdMh.differentiableAt
  have hγR : DifferentiableAt ℝ (moebiusMap γ) z := moebius_diffAt γ hz
  have hγRh : DifferentiableAt ℝ (moebiusMap γ) (h z) := moebius_diffAt γ hhz
  have hdzγ : dz (moebiusMap γ) z = (moebiusDenom γ z ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hγC, hdM.deriv]
  have hdzbarγ : dzbar (moebiusMap γ) z = 0 := dzbar_eq_zero_of_differentiableAt hγC
  have hdzγh : dz (moebiusMap γ) (h z) = (moebiusDenom γ (h z) ^ 2)⁻¹ := by
    rw [dz_eq_deriv_of_differentiableAt hγCh, hdMh.deriv]
  have hdzbarγh : dzbar (moebiusMap γ) (h z) = 0 :=
    dzbar_eq_zero_of_differentiableAt hγCh
  have hev : (fun w => h (moebiusMap γ w)) =ᶠ[nhds z] fun w => moebiusMap γ (h w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz]
      with w hw
    exact hcomm w hw
  have hfeq : fderiv ℝ (fun w => h (moebiusMap γ w)) z
      = fderiv ℝ (fun w => moebiusMap γ (h w)) z := hev.fderiv_eq
  have hE1 : dz h (moebiusMap γ z) * (moebiusDenom γ z ^ 2)⁻¹
      = (moebiusDenom γ (h z) ^ 2)⁻¹ * dz h z := by
    have hL := dz_comp (f := moebiusMap γ) (g := h) hγR hdiffγ
    have hR := dz_comp (f := h) (g := moebiusMap γ) hdiff hγRh
    have hLR : dz (fun w => h (moebiusMap γ w)) z
        = dz (fun w => moebiusMap γ (h w)) z := by simp only [dz, hfeq]
    rw [hL, hR, hdzγ, hdzbarγ, hdzγh, hdzbarγh] at hLR
    simpa using hLR
  have hE2 : dzbar h (moebiusMap γ z) * conj ((moebiusDenom γ z ^ 2)⁻¹)
      = (moebiusDenom γ (h z) ^ 2)⁻¹ * dzbar h z := by
    have hL := dzbar_comp (f := moebiusMap γ) (g := h) hγR hdiffγ
    have hR := dzbar_comp (f := h) (g := moebiusMap γ) hdiff hγRh
    have hLR : dzbar (fun w => h (moebiusMap γ w)) z
        = dzbar (fun w => moebiusMap γ (h w)) z := by simp only [dzbar, hfeq]
    rw [hL, hR, hdzγ, hdzbarγ, hdzγh, hdzbarγh] at hLR
    simpa using hLR
  have hd2 : (moebiusDenom γ z ^ 2) ≠ 0 := pow_ne_zero 2 hd
  constructor
  · calc dz h (moebiusMap γ z)
        = dz h (moebiusMap γ z) * (moebiusDenom γ z ^ 2)⁻¹ * moebiusDenom γ z ^ 2 := by
          field_simp
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * dz h z * moebiusDenom γ z ^ 2 := by rw [hE1]
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ z ^ 2 * dz h z := by ring
  · have hcinv : conj ((moebiusDenom γ z ^ 2)⁻¹) * conj (moebiusDenom γ z ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hd2, map_one]
    calc dzbar h (moebiusMap γ z)
        = dzbar h (moebiusMap γ z) * conj ((moebiusDenom γ z ^ 2)⁻¹)
          * conj (moebiusDenom γ z ^ 2) := by rw [mul_assoc, hcinv, mul_one]
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * dzbar h z * conj (moebiusDenom γ z ^ 2) := by
          rw [hE2]
      _ = (moebiusDenom γ (h z) ^ 2)⁻¹ * conj (moebiusDenom γ z ^ 2) * dzbar h z := by
          ring

/-- The Wirtinger quotient transforms by the unimodular phase `conj(d²)/d²` under a deck
transformation. -/
theorem wq_moebius {h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    wirtingerQuotient h (moebiusMap γ z)
      = conj (moebiusDenom γ z ^ 2) / moebiusDenom γ z ^ 2 * wirtingerQuotient h z := by
  obtain ⟨h1, h2⟩ := wirtinger_moebius γ hz hhz hcomm hdiff hdiffγ
  have hd2 : moebiusDenom γ z ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have he2 : moebiusDenom γ (h z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hhz.ne')
  have he : moebiusDenom γ (h z) ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hhz.ne'
  rcases eq_or_ne (dz h z) 0 with h0 | h0
  · rw [wirtingerQuotient, wirtingerQuotient, h1, h0]
    simp
  · rw [wirtingerQuotient, wirtingerQuotient, h1, h2]
    field_simp

/-- The unimodular direction `q/|q|` transforms by the opposite phase `d²/conj(d²)`. -/
theorem theta_moebius {q : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z) :
    q (moebiusMap γ z) / (‖q (moebiusMap γ z)‖ : ℂ)
      = moebiusDenom γ z ^ 2 / conj (moebiusDenom γ z ^ 2) * (q z / (‖q z‖ : ℂ)) := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hc2 : moebiusDenom γ z * conj (moebiusDenom γ z)
      = ((‖moebiusDenom γ z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hnorm4 : ((‖moebiusDenom γ z‖ ^ 4 : ℝ) : ℂ)
      = conj (moebiusDenom γ z ^ 2) * moebiusDenom γ z ^ 2 := by
    have h4 : ((‖moebiusDenom γ z‖ ^ 4 : ℝ) : ℂ)
        = ((‖moebiusDenom γ z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
      push_cast
      ring
    rw [h4, ← hc2, map_pow]
    ring
  rcases eq_or_ne (q z) 0 with h0 | h0
  · rw [hqz, h0, mul_zero, zero_div, mul_zero]
  · have hcne : conj (moebiusDenom γ z ^ 2) ≠ 0 := by
      intro hcc
      have : moebiusDenom γ z ^ 2 = 0 := by
        have := congrArg conj hcc
        rwa [Complex.conj_conj, map_zero] at this
      exact pow_ne_zero 2 hd this
    have hnq : (‖q z‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
    rw [hqz, norm_mul, norm_pow, Complex.ofReal_mul, hnorm4]
    field_simp

/-- **Exact deck invariance of the Beltrami phase product** `μ · q/|q|`. -/
theorem wq_theta_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    wirtingerQuotient h (moebiusMap γ z)
        * (q (moebiusMap γ z) / (‖q (moebiusMap γ z)‖ : ℂ))
      = wirtingerQuotient h z * (q z / (‖q z‖ : ℂ)) := by
  have hd2 : moebiusDenom γ z ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have hcne : conj (moebiusDenom γ z ^ 2) ≠ 0 := by
    intro hcc
    have h' := congrArg conj hcc
    rw [Complex.conj_conj, map_zero] at h'
    exact hd2 h'
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  rw [wq_moebius γ hz hhz hcomm hdiff hdiffγ, theta_moebius γ hz hqz]
  field_simp

/-- **Exact deck invariance of the Reich–Strebel pullback** `rsQ`: the weight-4
automorphy of `q`, the equivariance of `h`, and the Möbius chain rule cancel all
denominator phases. -/
theorem rsQ_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hqhz : q (moebiusMap γ (h z)) = moebiusDenom γ (h z) ^ 4 * q (h z))
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsQ q h (moebiusMap γ z) = rsQ q h z := by
  obtain ⟨h1, -⟩ := wirtinger_moebius γ hz hhz hcomm hdiff hdiffγ
  have hwqθ := wq_theta_moebius γ hz hhz hqz hcomm hdiff hdiffγ
  have hd4 : moebiusDenom γ z ^ 4 ≠ 0 :=
    pow_ne_zero 4 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne')
  have he2 : moebiusDenom γ (h z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hhz.ne')
  rw [rsQ, rsQ, hcomm z hz, hqhz, h1, hwqθ, hqz]
  have hnum : moebiusDenom γ (h z) ^ 4 * q (h z)
        * ((moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ z ^ 2 * dz h z) ^ 2
        * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2
      = moebiusDenom γ z ^ 4
        * (q (h z) * dz h z ^ 2
            * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2) := by
    have heq : moebiusDenom γ (h z) ^ 2 * (moebiusDenom γ (h z) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ he2
    linear_combination (q (h z) * moebiusDenom γ z ^ 4 * dz h z ^ 2
      * (1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))) ^ 2
      * ((moebiusDenom γ (h z) ^ 2)⁻¹ * moebiusDenom γ (h z) ^ 2 + 1)) * heq
  rw [hnum, neg_div, neg_div, mul_div_mul_left _ _ hd4]

/-- The norm of the Wirtinger quotient is deck-invariant. -/
theorem norm_wq_moebius {h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    ‖wirtingerQuotient h (moebiusMap γ z)‖ = ‖wirtingerQuotient h z‖ := by
  have hd2 : ‖moebiusDenom γ z ^ 2‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (pow_ne_zero 2 (moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'))
  rw [wq_moebius γ hz hhz hcomm hdiff hdiffγ, norm_mul, norm_div,
    RCLike.norm_conj, div_self hd2, one_mul]

/-- Deck invariance of the image vertical-leaf density. -/
theorem rsDensity_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hqhz : q (moebiusMap γ (h z)) = moebiusDenom γ (h z) ^ 4 * q (h z))
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsDensity q h (moebiusMap γ z) = rsDensity q h z := by
  rw [rsDensity, rsDensity, rsQ_moebius γ hz hhz hqz hqhz hcomm hdiff hdiffγ]

/-- Deck invariance of the Reich–Strebel weight. -/
theorem rsWeight_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsWeight q h (moebiusMap γ z) = rsWeight q h z := by
  rw [rsWeight, rsWeight, wq_theta_moebius γ hz hhz hqz hcomm hdiff hdiffγ,
    norm_wq_moebius γ hz hhz hcomm hdiff hdiffγ]

/-- Deck invariance of the floored Reich–Strebel weight. -/
theorem rsWeightM_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (κ : ℝ) {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsWeightM q h κ (moebiusMap γ z) = rsWeightM q h κ z := by
  rw [rsWeightM, rsWeightM, rsWeight_moebius γ hz hhz hqz hcomm hdiff hdiffγ]

/-- Deck invariance of the first Cauchy–Schwarz factor. -/
theorem rsU_moebius {q h : ℂ → ℂ} (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (κ : ℝ) {z : ℂ} (hz : 0 < z.im) (hhz : 0 < (h z).im)
    (hqz : q (moebiusMap γ z) = moebiusDenom γ z ^ 4 * q z)
    (hqhz : q (moebiusMap γ (h z)) = moebiusDenom γ (h z) ^ 4 * q (h z))
    (hcomm : ∀ w : ℂ, 0 < w.im → h (moebiusMap γ w) = moebiusMap γ (h w))
    (hdiff : DifferentiableAt ℝ h z) (hdiffγ : DifferentiableAt ℝ h (moebiusMap γ z)) :
    rsU q h κ (moebiusMap γ z) = rsU q h κ z := by
  rw [rsU, rsU, rsDensity_moebius γ hz hhz hqz hqhz hcomm hdiff hdiffγ,
    rsWeightM_moebius γ κ hz hhz hqz hcomm hdiff hdiffγ]

/-- **Packaging of the symmetrized flow data**: given the flow, its regular set, the two
leafwise minimal-variation bounds, and the two symmetrized invariance identities, the
composed measurability fields are discharged from joint measurability of the flow, and
the interface theorem `reich_strebel_of_flowDataSym` becomes consumable. -/
noncomputable def verticalFlowDataSym_of_leafLb
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (h : ℂ → ℂ) (κ : ℝ) (hh : Measurable h)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (flow : ℝ → ℂ → ℂ)
    (hflow : Measurable fun p : ℝ × ℂ => flow p.1 p.2)
    (good : Set ℂ)
    (good_ae : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good)
    (leaf_lb : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
      ENNReal.ofReal T
        ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow t z)) + 2 * C)
    (leaf_lb_neg : ∀ z ∈ good, ∀ T : ℝ, 0 < T →
      ENNReal.ofReal T
        ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (flow (-t) z)) + 2 * C)
    (invar_U : ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsU q h κ (flow t z) + rsU q h κ (flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsU q h κ z * ‖q z‖ₑ)
    (invar_W : ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsWeightM q h κ (flow t z) + rsWeightM q h κ (flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsWeightM q h κ z * ‖q z‖ₑ) :
    VerticalFlowDataSym Γ q h κ where
  C := C
  hC := hC
  flow := flow
  good := good
  good_ae := good_ae
  meas_D := (measurable_rsDensity q.measurable hh).comp hflow
  meas_U := (measurable_rsU q.measurable hh κ).comp hflow
  meas_W := (measurable_rsWeightM q.measurable h κ).comp hflow
  leaf_lb := leaf_lb
  leaf_lb_neg := leaf_lb_neg
  invar_U := invar_U
  invar_W := invar_W

/-- The **chart-translation local flow**: transport by time `t` in the natural chart `Φ`
over the chart domain `S` — the inverse-chart image of the translated development. -/
noncomputable def localFlow (Φ : ℂ → ℂ) (S : Set ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  Function.invFunOn Φ S (Φ w + t)

/-- The local flow stays in the chart domain while the development stays in the
developed image. -/
theorem localFlow_mem {Φ : ℂ → ℂ} {S : Set ℂ} {t : ℝ} {w : ℂ}
    (h : Φ w + (t : ℂ) ∈ Φ '' S) : localFlow Φ S t w ∈ S := by
  obtain ⟨a, ha, hfa⟩ := h
  exact Function.invFunOn_mem ⟨a, ha, hfa⟩

/-- The defining development identity of the local flow: `Φ` of the flow is the
translated development. -/
theorem localFlow_dev {Φ : ℂ → ℂ} {S : Set ℂ} {t : ℝ} {w : ℂ}
    (h : Φ w + (t : ℂ) ∈ Φ '' S) : Φ (localFlow Φ S t w) = Φ w + t := by
  obtain ⟨a, ha, hfa⟩ := h
  exact Function.invFunOn_eq ⟨a, ha, hfa⟩

/-- The local flow at time zero is the identity on the chart domain. -/
theorem localFlow_zero {Φ : ℂ → ℂ} {S : Set ℂ} (hinj : Set.InjOn Φ S) {w : ℂ}
    (hw : w ∈ S) : localFlow Φ S 0 w = w := by
  have h0 : Φ w + ((0 : ℝ) : ℂ) = Φ w := by simp
  have hex : ∃ a ∈ S, Φ a = Φ w + ((0 : ℝ) : ℂ) := ⟨w, hw, h0.symm⟩
  exact hinj (Function.invFunOn_mem hex) hw (by rw [Function.invFunOn_eq hex, h0])

/-- The cocycle law of the local flow inside a single chart. -/
theorem localFlow_add {Φ : ℂ → ℂ} {S : Set ℂ} {s t : ℝ} {w : ℂ}
    (hs : Φ w + (s : ℂ) ∈ Φ '' S) :
    localFlow Φ S t (localFlow Φ S s w) = localFlow Φ S (s + t) w := by
  show Function.invFunOn Φ S (Φ (localFlow Φ S s w) + (t : ℂ)) = _
  rw [localFlow_dev hs]
  unfold localFlow
  congr 1
  push_cast
  ring

/-- **Unit developed velocity of the local flow line**: where the chart derivative does
not vanish, the flow line is differentiable in time with velocity `1/Φ'` — in the chart
the motion is the unit horizontal translation. -/
theorem localFlow_hasDerivAt {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S) {w : ℂ} {t : ℝ}
    (hp : Φ w + (t : ℂ) ∈ Φ '' S)
    (hder : deriv Φ (localFlow Φ S t w) ≠ 0) :
    HasDerivAt (fun u : ℝ => localFlow Φ S u w)
      ((deriv Φ (localFlow Φ S t w))⁻¹) t := by
  set p := localFlow Φ S t w with hpdef
  have hpS : p ∈ S := localFlow_mem hp
  have hΦp : Φ p = Φ w + t := localFlow_dev hp
  have han : AnalyticAt ℂ Φ p := (hΦ.analyticOnNhd hS) p hpS
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set g := hstrict.localInverse Φ (deriv Φ p) p hder with hgdef
  have himg : Φ '' S ∈ nhds (Φ p) := by
    rw [← hstrict.map_nhds_eq hder]
    exact Filter.image_mem_map (hS.mem_nhds hpS)
  have hι : Filter.Tendsto (fun u : ℝ => Φ w + (u : ℂ)) (nhds t) (nhds (Φ p)) :=
    (continuous_const.add Complex.continuous_ofReal).tendsto' t (Φ p) hΦp.symm
  have hgleft : g (Φ p) = p := (hstrict.eventually_left_inverse hder).self_of_nhds
  have hgcont : ContinuousAt g (Φ p) :=
    (hstrict.to_localInverse hder).hasDerivAt.continuousAt
  have hgS : ∀ᶠ y in nhds (Φ p), g y ∈ S := by
    rw [ContinuousAt, hgleft] at hgcont
    exact hgcont (hS.mem_nhds hpS)
  have hgright : ∀ᶠ y in nhds (Φ p), Φ (g y) = y :=
    hstrict.eventually_right_inverse hder
  have heq : (fun u : ℝ => localFlow Φ S u w)
      =ᶠ[nhds t] fun u : ℝ => g (Φ w + (u : ℂ)) := by
    filter_upwards [hι himg, hι hgS, hι hgright] with u hu h1u h2u
    exact hinj (localFlow_mem hu) h1u (by rw [localFlow_dev hu, h2u])
  have hg' : HasDerivAt g ((deriv Φ p)⁻¹) (Φ w + (t : ℂ)) :=
    hΦp ▸ (hstrict.to_localInverse hder).hasDerivAt
  have hG : HasDerivAt (fun ζ : ℂ => g (Φ w + ζ)) ((deriv Φ p)⁻¹) ((t : ℝ) : ℂ) :=
    HasDerivAt.comp_const_add (Φ w) ((t : ℝ) : ℂ) hg'
  have hcomp : HasDerivAt (fun u : ℝ => g (Φ w + (u : ℂ))) ((deriv Φ p)⁻¹) t :=
    hG.comp_ofReal
  exact hcomp.congr_of_eventuallyEq heq

/-- **Chart-level `|q|` area identity**: in a natural chart of `−q` the `|q|` area of a
measurable chart subset equals the Lebesgue area of its development. -/
theorem chart_lintegral {q Φ : ℂ → ℂ} {S A : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    (hA : MeasurableSet A) (hAS : A ⊆ S) :
    volume (Φ '' A) = ∫⁻ z in A, ‖q z‖ₑ := by
  have hdiff : ∀ x ∈ A, DifferentiableAt ℂ Φ x := fun x hx =>
    hΦ.differentiableAt (hS.mem_nhds (hAS hx))
  have hf' : ∀ x ∈ A, HasFDerivWithinAt Φ (fderiv ℝ Φ x) A x := by
    intro x hx
    have hR : DifferentiableAt ℝ Φ x :=
      (differentiableAt_complex_iff_differentiableAt_real.mp (hdiff x hx)).1
    exact hR.hasFDerivAt.hasFDerivWithinAt
  have hAF := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hf'
    (hinj.mono hAS) (fun _ => (1 : ℝ≥0∞))
  calc volume (Φ '' A) = ∫⁻ _ in Φ '' A, 1 := (setLIntegral_one _).symm
    _ = ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ Φ x).det| * 1 := hAF
    _ = ∫⁻ z in A, ‖q z‖ₑ := by
        refine setLIntegral_congr_fun hA (fun x hx => ?_)
        have hdet : (fderiv ℝ Φ x).det = ‖deriv Φ x‖ ^ 2 := by
          rw [det_fderiv_eq_wirtinger, dzbar_eq_zero_of_differentiableAt (hdiff x hx),
            dz_eq_deriv_of_differentiableAt (hdiff x hx), norm_zero]
          ring
        have hq : ‖deriv Φ x‖ ^ 2 = ‖q x‖ := by
          rw [← norm_pow, hsq x (hAS hx), norm_neg]
        rw [mul_one, hdet, hq, abs_of_nonneg (norm_nonneg _), ofReal_norm_eq_enorm]

/-- The development of the local-flow image is the translated development. -/
theorem localFlow_image {Φ : ℂ → ℂ} {S A : Set ℂ} {t : ℝ}
    (hA : ∀ w ∈ A, Φ w + (t : ℂ) ∈ Φ '' S) :
    Φ '' (localFlow Φ S t '' A) = (fun ζ => ζ + (t : ℂ)) '' (Φ '' A) := by
  ext y
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨Φ w, ⟨w, hw, rfl⟩, (localFlow_dev (hA w hw)).symm⟩
  · rintro ⟨y', ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨localFlow Φ S t w, ⟨w, hw, rfl⟩, localFlow_dev (hA w hw)⟩

/-- **Chart-level flow invariance of the `|q|` area**: transporting a chart subset by the
local flow preserves the `|q|` mass — in the development it is translation invariance of
the planar Lebesgue measure. -/
theorem chart_flow_lintegral {q Φ : ℂ → ℂ} {S A : Set ℂ} {t : ℝ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hmove : ∀ w ∈ A, Φ w + (t : ℂ) ∈ Φ '' S)
    (hB : MeasurableSet (localFlow Φ S t '' A)) :
    ∫⁻ z in localFlow Φ S t '' A, ‖q z‖ₑ = ∫⁻ z in A, ‖q z‖ₑ := by
  have hBS : localFlow Φ S t '' A ⊆ S := by
    rintro x ⟨w, hw, rfl⟩
    exact localFlow_mem (hmove w hw)
  rw [← chart_lintegral hS hΦ hinj hsq hA hAS,
    ← chart_lintegral hS hΦ hinj hsq hB hBS, localFlow_image hmove]
  have himg : (fun ζ : ℂ => ζ + (t : ℂ)) '' (Φ '' A)
      = (fun ζ : ℂ => ζ + -(t : ℂ)) ⁻¹' (Φ '' A) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + -(t : ℂ), hy, by ring⟩
  rw [himg, measure_preimage_add_right]

/-- A horizontal line in the plane is Lebesgue-null: the rotation by `I` of a vertical
line. -/
theorem volume_im_line_eq_zero (c : ℝ) : volume {w : ℂ | w.im = c} = 0 := by
  have h1 : {w : ℂ | w.im = c} = (fun w => Complex.I * w) '' {w : ℂ | w.re = c} := by
    ext w'
    constructor
    · intro hw'
      refine ⟨-Complex.I * w', ?_, ?_⟩
      · show (-Complex.I * w').re = c
        simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
          one_mul, zero_sub, neg_mul, neg_neg]
        simpa using hw'
      · show Complex.I * (-Complex.I * w') = w'
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
    · rintro ⟨w, hw, rfl⟩
      show (Complex.I * w).im = c
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul]
      simpa using hw
  have hmeas : MeasurableSet {w : ℂ | w.re = c} :=
    Complex.measurable_re (measurableSet_singleton c)
  rw [h1]
  refine image_null hmeas (volume_re_line_eq_zero c) (fun z _ => ?_) ?_
  · exact ((differentiable_const _).mul differentiable_id).differentiableAt
  · intro x _ y _ hxy
    have h2 := congrArg (fun w => -Complex.I * w) hxy
    simpa [← mul_assoc, mul_neg, Complex.I_mul_I] using h2

/-- **Chart-leaf nullity off the zeros**: the part of a chart domain developing into a
single horizontal line carries no `|q|` mass — the vertical leaf through a chart point
is `|q| dA`-null. -/
theorem chart_leaf_null {q Φ : ℂ → ℂ} {S A : Set ℂ} {c : ℝ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    (hA : MeasurableSet A) (hAS : A ⊆ S) (hline : ∀ z ∈ A, (Φ z).im = c) :
    ∫⁻ z in A, ‖q z‖ₑ = 0 := by
  rw [← chart_lintegral hS hΦ hinj hsq hA hAS]
  refine measure_mono_null ?_ (volume_im_line_eq_zero c)
  rintro w ⟨z, hz, rfl⟩
  exact hline z hz


/-- A **vertical trajectory** of `q` on a set of times: a continuous curve carried by
`−q`-natural charts avoiding the zeros, in which the development is the unit-speed
horizontal translation. -/
structure IsTrajOn (q : ℂ → ℂ) (σ : ℝ → ℂ) (s : Set ℝ) : Prop where
  cont : ContinuousOn σ s
  chart : ∀ t ∈ s, ∃ U : Set ℂ, IsOpen U ∧ σ t ∈ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ w ∈ U, q w ≠ 0) ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ U ∧ Set.InjOn Φ U ∧
    (∀ w ∈ U, deriv Φ w ^ 2 = -q w) ∧
    ∀ᶠ u in nhdsWithin t s, σ u ∈ U ∧ Φ (σ u) = Φ (σ t) + ((u - t : ℝ) : ℂ)

/-- **Trajectory seed**: through every regular point of the upper half plane there is a
vertical trajectory on a symmetric time interval, built from one natural chart by the
local translation flow. -/
theorem exists_traj_seed {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (hq0 : q z ≠ 0) :
    ∃ δ > 0, ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc (-δ) δ) := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨r, hr, hsubH, Φ, hΦd, hΦinj, hΦsq⟩ :=
    exists_natural_chart (q := fun w => -q w) hH hq.neg hz (neg_ne_zero.mpr hq0)
  have hqc : ContinuousAt q z := hq.continuousOn.continuousAt (hH.mem_nhds hz)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hqc (isOpen_ne.mem_nhds hq0) : q ⁻¹' {w | w ≠ 0} ∈ nhds z)
      (Metric.ball_mem_nhds z hr))
  set S : Set ℂ := Metric.ball z r₁ with hSdef
  have hSr : S ⊆ Metric.ball z r := fun w hw => (hball hw).2
  have hSne : ∀ w ∈ S, q w ≠ 0 := fun w hw => (hball hw).1
  have hSopen : IsOpen S := Metric.isOpen_ball
  have hSH : S ⊆ {z : ℂ | 0 < z.im} := hSr.trans hsubH
  have hzS : z ∈ S := Metric.mem_ball_self hr₁
  have hΦdS : DifferentiableOn ℂ Φ S := hΦd.mono hSr
  have hΦinjS : Set.InjOn Φ S := hΦinj.mono hSr
  have hΦsqS : ∀ w ∈ S, deriv Φ w ^ 2 = -q w := fun w hw => hΦsq w (hSr hw)
  have hder : ∀ w ∈ S, deriv Φ w ≠ 0 := by
    intro w hw h0
    exact hSne w hw (by have := hΦsqS w hw; rw [h0] at this; simpa using this.symm)
  -- the developed image is a neighborhood of the developed center
  have han : AnalyticAt ℂ Φ z := (hΦdS.analyticOnNhd hSopen) z hzS
  have hstrict : HasStrictDerivAt Φ (deriv Φ z) z :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  have himg : Φ '' S ∈ nhds (Φ z) := by
    rw [← hstrict.map_nhds_eq (hder z hzS)]
    exact Filter.image_mem_map (hSopen.mem_nhds hzS)
  obtain ⟨δ₂, hδ₂, hδball⟩ := Metric.mem_nhds_iff.mp himg
  set δ : ℝ := δ₂ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hmove : ∀ u : ℝ, |u| ≤ δ → Φ z + (u : ℂ) ∈ Φ '' S := by
    intro u hu
    refine hδball (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    linarith
  set σ : ℝ → ℂ := fun u => localFlow Φ S u z with hσdef
  have hmem : ∀ u ∈ Set.Icc (-δ) δ, Φ z + (u : ℂ) ∈ Φ '' S := fun u hu =>
    hmove u (abs_le.mpr ⟨hu.1, hu.2⟩)
  have hσdev : ∀ u ∈ Set.Icc (-δ) δ, Φ (σ u) = Φ z + u := fun u hu =>
    localFlow_dev (hmem u hu)
  have hσS : ∀ u ∈ Set.Icc (-δ) δ, σ u ∈ S := fun u hu => localFlow_mem (hmem u hu)
  have hσcont : ContinuousOn σ (Set.Icc (-δ) δ) := by
    intro u hu
    exact (localFlow_hasDerivAt hSopen hΦdS hΦinjS (hmem u hu)
      (hder _ (hσS u hu))).continuousAt.continuousWithinAt
  refine ⟨δ, hδ, σ, localFlow_zero hΦinjS hzS, hσcont, ?_⟩
  intro t ht
  refine ⟨S, hSopen, hσS t ht, hSH, hSne, Φ, hΦdS, hΦinjS, hΦsqS, ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with u hu
  refine ⟨hσS u hu, ?_⟩
  rw [hσdev u hu, hσdev t ht]
  push_cast
  ring

/-- **Forward germ propagation**: two vertical trajectories that agree strictly before a
time `c` and at `c` agree near `c` within the time interval — the chart branch
classification pins the sign by the backward overlap. -/
theorem traj_germ {q : ℂ → ℂ} {σ₁ σ₂ : ℝ → ℂ} {a b c : ℝ}
    (h₁ : IsTrajOn q σ₁ (Set.Icc a b)) (h₂ : IsTrajOn q σ₂ (Set.Icc a b))
    (hc : c ∈ Set.Icc a b) (hac : a < c)
    (hup : ∀ u ∈ Set.Ico a c, σ₁ u = σ₂ u) (hcc : σ₁ c = σ₂ c) :
    ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₁ u = σ₂ u := by
  obtain ⟨U₁, hU₁o, hpU₁, -, -, Φ₁, hΦ₁d, hΦ₁inj, hΦ₁sq, hev₁⟩ := h₁.chart c hc
  obtain ⟨U₂, hU₂o, hpU₂', -, -, Φ₂, hΦ₂d, hΦ₂inj, hΦ₂sq, hev₂⟩ := h₂.chart c hc
  set p : ℂ := σ₁ c with hpdef
  have hpU₂ : p ∈ U₂ := by rw [hcc]; exact hpU₂'
  set Ω : Set ℂ := connectedComponentIn (U₁ ∩ U₂) p with hΩdef
  have hΩo : IsOpen Ω := (hU₁o.inter hU₂o).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hpΩ : p ∈ Ω := mem_connectedComponentIn ⟨hpU₁, hpU₂⟩
  have hΩsub : Ω ⊆ U₁ ∩ U₂ := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2 := fun z hz => by
    rw [hΦ₂sq z (hΩsub hz).2, hΦ₁sq z (hΩsub hz).1]
  have hσ₁Ω : ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₁ u ∈ Ω :=
    (h₁.cont c hc) (hΩo.mem_nhds hpΩ)
  have hσ₂Ω : ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₂ u ∈ Ω := by
    have h2c : ContinuousWithinAt σ₂ (Set.Icc a b) c := h₂.cont c hc
    exact h2c (hcc ▸ hΩo.mem_nhds hpΩ)
  have hΦ₂p : Φ₂ (σ₂ c) = Φ₂ p := by rw [hcc]
  rcases open_branch_classification hΩo hΩconn hpΩ
      (hΦ₁d.mono (hΩsub.trans Set.inter_subset_left))
      (hΦ₂d.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · filter_upwards [hev₁, hev₂, hσ₁Ω, hσ₂Ω] with u h1u h2u hΩ1 hΩ2
    have hval : Φ₁ (σ₂ u) = Φ₁ p + ((u - c : ℝ) : ℂ) := by
      have h := hplus (σ₂ u) hΩ2
      have h2 := h2u.2
      rw [hΦ₂p] at h2
      rw [h2] at h
      linear_combination -h
    exact hΦ₁inj (hΩsub hΩ1).1 (hΩsub hΩ2).1 (by rw [h1u.2, hval])
  · exfalso
    have hsubIco : Set.Ico a c ⊆ Set.Icc a b := fun u hu =>
      ⟨hu.1, le_trans hu.2.le hc.2⟩
    have hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.mp ?_
      rw [closure_Ico hac.ne]
      exact ⟨hac.le, le_refl c⟩
    have hmono : nhdsWithin c (Set.Ico a c) ≤ nhdsWithin c (Set.Icc a b) :=
      nhdsWithin_mono c hsubIco
    have hbig := (hev₁.and (hev₂.and hσ₂Ω)).filter_mono hmono
    obtain ⟨u, huIco, h1u, h2u, hΩ2⟩ := (eventually_mem_nhdsWithin.and hbig).exists
    have hval : Φ₁ (σ₂ u) = Φ₁ p - ((u - c : ℝ) : ℂ) := by
      have h := hminus (σ₂ u) hΩ2
      have h2 := h2u.2
      rw [hΦ₂p] at h2
      rw [h2] at h
      linear_combination h
    have hval1 : Φ₁ (σ₁ u) = Φ₁ p + ((u - c : ℝ) : ℂ) := h1u.2
    have hueq : σ₁ u = σ₂ u := hup u huIco
    have hzero : ((u - c : ℝ) : ℂ) = 0 := by
      have := hval1.symm.trans (by rw [hueq, hval])
      linear_combination this / 2
    have : u = c := by
      have h0 : (u - c : ℝ) = 0 := by exact_mod_cast hzero
      linarith
    exact absurd this (ne_of_lt huIco.2)

/-- **Uniqueness of vertical trajectories**: two trajectories on `[a, b]` with the same
germ at `a` coincide on all of `[a, b]`. -/
theorem traj_unique {q : ℂ → ℂ} {σ₁ σ₂ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (h₁ : IsTrajOn q σ₁ (Set.Icc a b)) (h₂ : IsTrajOn q σ₂ (Set.Icc a b))
    (hgerm : ∀ᶠ u in nhdsWithin a (Set.Icc a b), σ₁ u = σ₂ u) :
    Set.EqOn σ₁ σ₂ (Set.Icc a b) := by
  set A : Set ℝ := {t | t ∈ Set.Icc a b ∧ ∀ u ∈ Set.Icc a t, σ₁ u = σ₂ u} with hAdef
  have haa : σ₁ a = σ₂ a := hgerm.self_of_nhdsWithin (Set.left_mem_Icc.mpr hab)
  have haA : a ∈ A := by
    refine ⟨Set.left_mem_Icc.mpr hab, fun u hu => ?_⟩
    have hua : u = a := le_antisymm hu.2 hu.1
    rw [hua]
    exact haa
  have hbdd : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  set c : ℝ := sSup A with hcdef
  have hcA : a ≤ c := le_csSup hbdd haA
  have hcb : c ≤ b := csSup_le ⟨a, haA⟩ (fun t ht => ht.1.2)
  have hc : c ∈ Set.Icc a b := ⟨hcA, hcb⟩
  have hup : ∀ u ∈ Set.Ico a c, σ₁ u = σ₂ u := by
    intro u hu
    obtain ⟨t, htA, hut⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ hu.2
    exact htA.2 u ⟨hu.1, hut.le⟩
  have hsubIco : Set.Ico a c ⊆ Set.Icc a b := fun u hu =>
    ⟨hu.1, le_trans hu.2.le hcb⟩
  have hcc : σ₁ c = σ₂ c := by
    rcases eq_or_lt_of_le hcA with heq | hac
    · rw [← heq]
      exact haa
    · haveI hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
        refine mem_closure_iff_nhdsWithin_neBot.mp ?_
        rw [closure_Ico hac.ne]
        exact ⟨hac.le, le_refl c⟩
      have hlim₁ : Filter.Tendsto σ₁ (nhdsWithin c (Set.Ico a c)) (nhds (σ₁ c)) :=
        (h₁.cont c hc).mono_left (nhdsWithin_mono c hsubIco)
      have hlim₂ : Filter.Tendsto σ₂ (nhdsWithin c (Set.Ico a c)) (nhds (σ₂ c)) :=
        (h₂.cont c hc).mono_left (nhdsWithin_mono c hsubIco)
      have heqf : σ₂ =ᶠ[nhdsWithin c (Set.Ico a c)] σ₁ :=
        eventually_mem_nhdsWithin.mono fun u hu => (hup u hu).symm
      exact tendsto_nhds_unique hlim₁ (hlim₂.congr' heqf)
  rcases eq_or_lt_of_le hcb with heqb | hclt
  · intro u hu
    rcases eq_or_lt_of_le hu.2 with hub | hub
    · rw [hub, ← heqb]
      exact hcc
    · exact hup u ⟨hu.1, by rw [heqb]; exact hub⟩
  · exfalso
    have hgermc : ∀ᶠ u in nhdsWithin c (Set.Icc a b), σ₁ u = σ₂ u := by
      rcases eq_or_lt_of_le hcA with heq | hac
      · rw [← heq]
        exact hgerm
      · exact traj_germ h₁ h₂ hc hac hup hcc
    obtain ⟨V, hVopen, hcV, hVsub⟩ := mem_nhdsWithin.mp hgermc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen c hcV
    set t' : ℝ := min b (c + ε / 2) with ht'def
    have ht'c : c < t' := lt_min hclt (by linarith)
    have ht'A : t' ∈ A := by
      refine ⟨⟨le_trans hcA ht'c.le, min_le_left _ _⟩, ?_⟩
      intro u hu
      rcases lt_or_ge u c with huc | huc
      · exact hup u ⟨hu.1, huc⟩
      · rcases eq_or_lt_of_le huc with hueq | hult
        · rw [← hueq]
          exact hcc
        · refine hVsub ⟨hball ?_, ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
          have hu2 := le_trans hu.2 (min_le_right _ _)
          linarith
    have := le_csSup hbdd ht'A
    linarith
/-- **Time reversal** of a vertical trajectory: reversing time and negating the chart
gives a vertical trajectory on the reflected time set. -/
theorem traj_reverse {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ}
    (h : IsTrajOn q σ s) :
    IsTrajOn q (fun u => σ (-u)) ((fun u : ℝ => -u) ⁻¹' s) := by
  have hmap : ∀ t : ℝ, t ∈ (fun u : ℝ => -u) ⁻¹' s →
      Filter.Tendsto (fun u : ℝ => -u) (nhdsWithin t ((fun u : ℝ => -u) ⁻¹' s))
        (nhdsWithin (-t) s) := by
    intro t _
    refine Filter.Tendsto.inf (continuous_neg.tendsto t) ?_
    exact Filter.tendsto_principal_principal.mpr fun u hu => hu
  constructor
  · intro t ht
    exact ContinuousWithinAt.comp (h.cont (-t) ht)
      (continuous_neg.continuousWithinAt) (fun u hu => hu)
  · intro t ht
    obtain ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := h.chart (-t) ht
    refine ⟨U, hUo, hmem, hUH, hUne, fun z => -Φ z, hΦd.neg, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hΦinj hx hy (neg_injective hxy)
    · intro w hw
      have hd : deriv (fun z => -Φ z) w = -deriv Φ w := by
        simp [deriv.fun_neg]
      rw [hd]
      rw [show (-deriv Φ w) ^ 2 = deriv Φ w ^ 2 by ring]
      exact hΦsq w hw
    · have := (hmap t ht).eventually hev
      filter_upwards [this] with u hu
      refine ⟨hu.1, ?_⟩
      have h2 := hu.2
      rw [h2]
      push_cast
      ring

/-- Reflection symmetry of the symmetric interval under negation. -/
theorem neg_preimage_Icc (δ : ℝ) :
    (fun u : ℝ => -u) ⁻¹' Set.Icc (-δ) δ = Set.Icc (-δ) δ := by
  ext u
  simp only [Set.mem_preimage, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **Branch alignment of a seed at the endpoint of a trajectory**: a seed through the
endpoint may be reoriented so that, in the endpoint chart of the incoming trajectory,
its development continues the incoming development with unit speed. -/
theorem traj_align {q : ℂ → ℂ} {σ τ : ℝ → ℂ} {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ)
    (hσ : IsTrajOn q σ (Set.Icc 0 b)) (hτ : IsTrajOn q τ (Set.Icc (-δ) δ))
    (hmatch : τ 0 = σ b) :
    ∃ υ : ℝ → ℂ, υ 0 = σ b ∧ IsTrajOn q υ (Set.Icc (-δ) δ) ∧
      ∃ U : Set ℂ, IsOpen U ∧ σ b ∈ U ∧ U ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ w ∈ U, q w ≠ 0) ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ U ∧ Set.InjOn Φ U ∧
        (∀ w ∈ U, deriv Φ w ^ 2 = -q w) ∧
        (∀ᶠ u in nhdsWithin b (Set.Icc 0 b),
          σ u ∈ U ∧ Φ (σ u) = Φ (σ b) + ((u - b : ℝ) : ℂ)) ∧
        (∀ᶠ v in nhdsWithin 0 (Set.Icc (-δ) δ), υ v ∈ U ∧ Φ (υ v) = Φ (σ b) + (v : ℂ)) := by
  have hbmem : b ∈ Set.Icc (0 : ℝ) b := Set.right_mem_Icc.mpr hb
  have h0mem : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevσ⟩ := hσ.chart b hbmem
  obtain ⟨Uτ, hUτo, hpUτ', -, -, Φτ, hΦτd, hΦτinj, hΦτsq, hevτ⟩ := hτ.chart 0 h0mem
  set p : ℂ := σ b with hpdef
  have hτ0 : τ 0 = p := hmatch
  have hpUτ : p ∈ Uτ := hτ0 ▸ hpUτ'
  set Ω : Set ℂ := connectedComponentIn (U ∩ Uτ) p with hΩdef
  have hΩo : IsOpen Ω := (hUo.inter hUτo).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hpΩ : p ∈ Ω := mem_connectedComponentIn ⟨hpU, hpUτ⟩
  have hΩsub : Ω ⊆ U ∩ Uτ := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φτ z ^ 2 = deriv Φ z ^ 2 := fun z hz => by
    rw [hΦτsq z (hΩsub hz).2, hΦsq z (hΩsub hz).1]
  have hτΩ : ∀ᶠ v in nhdsWithin 0 (Set.Icc (-δ) δ), τ v ∈ Ω :=
    (hτ.cont 0 h0mem) (hτ0 ▸ hΩo.mem_nhds hpΩ)
  have hΦτ0 : Φτ (τ 0) = Φτ p := by rw [hτ0]
  rcases open_branch_classification hΩo hΩconn hpΩ
      (hΦd.mono (hΩsub.trans Set.inter_subset_left))
      (hΦτd.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · refine ⟨τ, hτ0, hτ, U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevσ, ?_⟩
    filter_upwards [hevτ, hτΩ] with v hv hvΩ
    refine ⟨(hΩsub hvΩ).1, ?_⟩
    have h := hplus (τ v) hvΩ
    have h2 := hv.2
    rw [hΦτ0] at h2
    rw [h2] at h
    rw [show ((v - 0 : ℝ) : ℂ) = (v : ℂ) by push_cast; ring] at h
    linear_combination -h
  · have hneg : Filter.Tendsto (fun v : ℝ => -v)
        (nhdsWithin 0 (Set.Icc (-δ) δ)) (nhdsWithin 0 (Set.Icc (-δ) δ)) := by
      refine Filter.Tendsto.inf ?_ ?_
      · have hn := (continuous_neg : Continuous fun v : ℝ => -v).tendsto 0
        rwa [neg_zero] at hn
      · refine Filter.tendsto_principal_principal.mpr fun v hv => ?_
        rw [Set.mem_Icc] at hv ⊢
        constructor <;> linarith [hv.1, hv.2]
    have hrev := traj_reverse hτ
    rw [neg_preimage_Icc δ] at hrev
    refine ⟨fun v => τ (-v), by show τ (-0) = _; rw [neg_zero]; exact hτ0, hrev,
      U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevσ, ?_⟩
    filter_upwards [hneg.eventually hevτ, hneg.eventually hτΩ] with v hv hvΩ
    refine ⟨(hΩsub hvΩ).1, ?_⟩
    have h := hminus (τ (-v)) hvΩ
    have h2 := hv.2
    rw [hΦτ0] at h2
    rw [h2] at h
    rw [show ((-v - 0 : ℝ) : ℂ) = -(v : ℂ) by push_cast; ring] at h
    linear_combination h

/-- Below the junction the extended time interval induces the same within-filter. -/
theorem nhdsWithin_left {b b' t : ℝ} (hbb : b ≤ b') (ht : t < b) :
    nhdsWithin t (Set.Icc 0 b') = nhdsWithin t (Set.Icc 0 b) := by
  have hio : Set.Iio b ∈ nhds t := Iio_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Icc 0 b) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by linarith⟩, h3⟩

/-- Above the junction the full time interval induces the same within-filter as the
right piece. -/
theorem nhdsWithin_right {b δ t : ℝ} (h0 : 0 ≤ b) (ht : b < t) :
    nhdsWithin t (Set.Icc 0 (b + δ)) = nhdsWithin t (Set.Icc b (b + δ)) := by
  have hio : Set.Ioi b ∈ nhds t := Ioi_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Icc b (b + δ)) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, h2⟩, h3⟩

/-- The within-filter of the glued interval at any point splits over the two pieces. -/
theorem nhdsWithin_split {b δ t : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) :
    nhdsWithin t (Set.Icc 0 (b + δ))
      = nhdsWithin t (Set.Icc 0 b) ⊔ nhdsWithin t (Set.Icc b (b + δ)) := by
  rw [← nhdsWithin_union, Set.Icc_union_Icc_eq_Icc hb (by linarith)]

/-- The time shift carries the right-piece within-filter to the seed interval filter. -/
theorem tendsto_shift {b δ t : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun u : ℝ => u - b) (nhdsWithin t (Set.Icc b (b + δ)))
      (nhdsWithin (t - b) (Set.Icc (-δ) δ)) := by
  refine Filter.Tendsto.inf ((continuous_sub_right b).tendsto t) ?_
  refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
  rw [Set.mem_Icc] at hu ⊢
  constructor <;> linarith [hu.1, hu.2]

/-- **Trajectory extension**: a vertical trajectory on `[0, b]` extends beyond `b` — the
aligned seed at the endpoint continues the development with unit speed. -/
theorem traj_extend {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) {σ : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hσ : IsTrajOn q σ (Set.Icc 0 b)) :
    ∃ δ > 0, ∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Icc 0 b) ∧
      IsTrajOn q σ' (Set.Icc 0 (b + δ)) := by
  have hbmem : b ∈ Set.Icc (0 : ℝ) b := Set.right_mem_Icc.mpr hb
  obtain ⟨U₀, -, hpU₀, hU₀H, hU₀ne, -⟩ := hσ.chart b hbmem
  obtain ⟨δ, hδ, τ, hτ0, hτ⟩ := exists_traj_seed hq (hU₀H hpU₀) (hU₀ne _ hpU₀)
  obtain ⟨υ, hυ0, hυ, U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hevL, hevR⟩ :=
    traj_align hb hδ hσ hτ hτ0
  set σ' : ℝ → ℂ := fun u => if u ≤ b then σ u else υ (u - b) with hσ'def
  have hEq : Set.EqOn σ' σ (Set.Icc 0 b) := fun u hu => if_pos hu.2
  have hσ'b : σ' b = σ b := if_pos le_rfl
  have hEqR : ∀ u ∈ Set.Icc b (b + δ), σ' u = υ (u - b) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with heq | hlt
    · rw [← heq, hσ'b, show b - b = (0 : ℝ) by ring, hυ0]
    · exact if_neg (not_le.mpr hlt)
  have hshift0 : Filter.Tendsto (fun u : ℝ => u - b)
      (nhdsWithin b (Set.Icc b (b + δ))) (nhdsWithin 0 (Set.Icc (-δ) δ)) := by
    have h := tendsto_shift (t := b) (b := b) hδ
    rwa [show b - b = (0 : ℝ) by ring] at h
  have h0mem : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  refine ⟨δ, hδ, σ', hEq, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · show Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (b + δ))) (nhds (σ' t))
      rw [nhdsWithin_left (by linarith) htb, hEq ⟨ht.1, htb.le⟩]
      exact Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
        (hσ.cont t ⟨ht.1, htb.le⟩)
    · subst heq
      show Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (t + δ))) (nhds (σ' t))
      rw [nhdsWithin_split hb hδ.le, Filter.tendsto_sup]
      constructor
      · rw [hσ'b]
        exact Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
          (hσ.cont t hbmem)
      · rw [hσ'b, ← hυ0]
        refine Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEqR u hu).symm) ?_
        exact Filter.Tendsto.comp (hυ.cont 0 h0mem) hshift0
    · show Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (b + δ))) (nhds (σ' t))
      have htmem : t - b ∈ Set.Icc (-δ) δ := ⟨by linarith, by linarith [ht.2]⟩
      rw [nhdsWithin_right hb htb, hEqR t ⟨htb.le, ht.2⟩]
      refine Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEqR u hu).symm) ?_
      exact Filter.Tendsto.comp (hυ.cont (t - b) htmem) (tendsto_shift hδ)
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hσ.chart t ⟨ht.1, htb.le⟩
      refine ⟨Ut, hUto, by rw [hEq ⟨ht.1, htb.le⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_left (by linarith) htb]
      filter_upwards [hevt, eventually_mem_nhdsWithin] with u hu huIcc
      rw [hEq huIcc, hEq ⟨ht.1, htb.le⟩]
      exact hu
    · subst heq
      refine ⟨U, hUo, by rw [hσ'b]; exact hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
      rw [nhdsWithin_split hb hδ.le, Filter.eventually_sup]
      constructor
      · filter_upwards [hevL, eventually_mem_nhdsWithin] with u hu huIcc
        rw [hEq huIcc, hσ'b]
        refine ⟨hu.1, ?_⟩
        rw [hu.2]
      · filter_upwards [hshift0.eventually hevR, eventually_mem_nhdsWithin]
          with u hu huIcc
        rw [hEqR u huIcc, hσ'b]
        exact hu
    · have htmem : t - b ∈ Set.Icc (-δ) δ := ⟨by linarith, by linarith [ht.2]⟩
      obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hυ.chart (t - b) htmem
      refine ⟨Ut, hUto, by rw [hEqR t ⟨htb.le, ht.2⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_right hb htb]
      filter_upwards [(tendsto_shift hδ).eventually hevt,
        eventually_mem_nhdsWithin] with u hu huIcc
      rw [hEqR u huIcc, hEqR t ⟨htb.le, ht.2⟩]
      refine ⟨hu.1, ?_⟩
      rw [hu.2]
      congr 1
      push_cast
      ring


/-- **Interior derivative of a vertical trajectory**: at an interior time the trajectory
is differentiable, with speed of squared norm `1/|q|` — unit flat speed. -/
theorem traj_hasDerivAt {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ} {t : ℝ}
    (hσ : IsTrajOn q σ s) (ht : t ∈ s) (hnhds : s ∈ nhds t) :
    ∃ d : ℂ, HasDerivAt σ d t ∧ ‖d‖ ^ 2 * ‖q (σ t)‖ = 1 := by
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t ht
  rw [nhdsWithin_eq_nhds.mpr hnhds] at hev
  set p : ℂ := σ t with hpdef
  have hq0 : q p ≠ 0 := hUne p hpU
  have hder : deriv Φ p ≠ 0 := by
    intro h0
    apply hq0
    have := hΦsq p hpU
    rw [h0] at this
    simpa using this.symm
  have han : AnalyticAt ℂ Φ p := (hΦd.analyticOnNhd hUo) p hpU
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set g : ℂ → ℂ := hstrict.localInverse Φ (deriv Φ p) p hder with hgdef
  have hgleft : ∀ᶠ x in nhds p, g (Φ x) = x := hstrict.eventually_left_inverse hder
  have hcont : ContinuousAt σ t := by
    have := hσ.cont t ht
    rwa [ContinuousWithinAt, nhdsWithin_eq_nhds.mpr hnhds] at this
  have hσp : ∀ᶠ v in nhds t, g (Φ (σ v)) = σ v := hcont hgleft
  have heq : σ =ᶠ[nhds t] fun v : ℝ => g (Φ p + ((v - t : ℝ) : ℂ)) := by
    filter_upwards [hσp, hev] with v hv hv2
    rw [← hv, hv2.2]
  have hg' : HasDerivAt g ((deriv Φ p)⁻¹) (Φ p) :=
    (hstrict.to_localInverse hder).hasDerivAt
  have hG : HasDerivAt (fun ζ : ℂ => g (Φ p + ζ)) ((deriv Φ p)⁻¹)
      (((t - t : ℝ) : ℂ)) := by
    refine HasDerivAt.comp_const_add (Φ p) _ ?_
    rw [show Φ p + ((t - t : ℝ) : ℂ) = Φ p by push_cast; ring]
    exact hg'
  have hF : HasDerivAt (fun v : ℝ => g (Φ p + ((v - t : ℝ) : ℂ)))
      ((deriv Φ p)⁻¹) t := by
    have h1 : HasDerivAt (fun v : ℝ => g (Φ p + ((v : ℝ) : ℂ))) ((deriv Φ p)⁻¹)
        (t - t) := by
      have := hG.comp_ofReal (z := t - t)
      simpa using this
    have h2 := HasDerivAt.comp_sub_const (x := t) (a := t) h1
    simpa using h2
  have hd : HasDerivAt σ ((deriv Φ p)⁻¹) t := hF.congr_of_eventuallyEq heq
  refine ⟨(deriv Φ p)⁻¹, hd, ?_⟩
  have hnorm : ‖deriv Φ p‖ ^ 2 = ‖q p‖ := by
    rw [← norm_pow, hΦsq p hpU, norm_neg]
  rw [norm_inv, inv_pow, hnorm]
  exact inv_mul_cancel₀ (by simpa using hq0)

/-- **Flat-speed Lipschitz bound**: a trajectory whose track satisfies a lower bound on
`|q|` is Lipschitz with constant `√(1/m)` on interior closed subintervals. -/
theorem traj_dist_le {q : ℂ → ℂ} {σ : ℝ → ℂ} {c : ℝ}
    (hσ : IsTrajOn q σ (Set.Ico 0 c)) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ t ∈ Set.Ico 0 c, m ≤ ‖q (σ t)‖)
    {s u : ℝ} (hs : 0 < s) (hsu : s ≤ u) (hu : u < c) :
    ‖σ u - σ s‖ ≤ Real.sqrt m⁻¹ * (u - s) := by
  have hex : ∀ x ∈ Set.Icc s u, ∃ d : ℂ, HasDerivAt σ d x ∧ ‖d‖ ^ 2 * ‖q (σ x)‖ = 1 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
    have hxc : x < c := lt_of_le_of_lt hx.2 hu
    exact traj_hasDerivAt hσ ⟨hx0.le, hxc⟩ (Ico_mem_nhds hx0 hxc)
  choose! d hd1 hd2 using hex
  have hf : ∀ x ∈ Set.Icc s u, HasDerivWithinAt σ (d x) (Set.Icc s u) x := fun x hx =>
    (hd1 x hx).hasDerivWithinAt
  have hboundd : ∀ x ∈ Set.Ico s u, ‖d x‖ ≤ Real.sqrt m⁻¹ := by
    intro x hx
    have hxI : x ∈ Set.Icc s u := ⟨hx.1, hx.2.le⟩
    have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
    have hxc : x < c := lt_of_lt_of_le hx.2 hu.le
    have hq : m ≤ ‖q (σ x)‖ := hbound x ⟨hx0.le, hxc⟩
    have hqpos : 0 < ‖q (σ x)‖ := lt_of_lt_of_le hm hq
    have hsq : ‖d x‖ ^ 2 = ‖q (σ x)‖⁻¹ := by
      have h := hd2 x hxI
      field_simp
      linarith [h]
    have hle : ‖d x‖ ^ 2 ≤ m⁻¹ := by
      rw [hsq]
      exact inv_anti₀ hm hq
    calc ‖d x‖ = Real.sqrt (‖d x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt m⁻¹ := Real.sqrt_le_sqrt hle
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf hboundd u
    (Set.right_mem_Icc.mpr hsu)
  linarith [this]

/-- **Limit at a finite escape time**: a trajectory on `[0, c)` whose track keeps `|q|`
bounded below converges at `c`. -/
theorem traj_limit {q : ℂ → ℂ} {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hσ : IsTrajOn q σ (Set.Ico 0 c)) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ t ∈ Set.Ico 0 c, m ≤ ‖q (σ t)‖) :
    ∃ w : ℂ, Filter.Tendsto σ (nhdsWithin c (Set.Ico 0 c)) (nhds w) := by
  haveI hne : (nhdsWithin c (Set.Ico 0 c)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico hc.ne]
    exact ⟨hc.le, le_refl c⟩
  have hcauchy : Cauchy (Filter.map σ (nhdsWithin c (Set.Ico 0 c))) := by
    refine Metric.cauchy_iff.mpr ⟨Filter.map_neBot, ?_⟩
    intro ε hε
    set M : ℝ := Real.sqrt m⁻¹ with hMdef
    have hM0 : 0 ≤ M := Real.sqrt_nonneg _
    set δ : ℝ := min (ε / (2 * (M + 1))) (c / 2) with hδdef
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδc : c - δ ≥ c / 2 := by
      have := min_le_right (ε / (2 * (M + 1))) (c / 2)
      simp only [← hδdef] at this
      linarith
    refine ⟨σ '' (Set.Ico (c - δ) c ∩ Set.Ico 0 c), ?_, ?_⟩
    · refine Filter.image_mem_map (mem_nhdsWithin.mpr ⟨Set.Ioo (c - δ) (c + 1),
        isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩)
      rintro x ⟨hx1, hx2⟩
      exact ⟨⟨hx1.1.le, hx2.2⟩, hx2⟩
    · rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
      have hgap : ∀ v w : ℝ, v ∈ Set.Ico (c - δ) c ∩ Set.Ico 0 c →
          w ∈ Set.Ico (c - δ) c ∩ Set.Ico 0 c → v ≤ w → dist (σ w) (σ v) < ε := by
        intro v w hv hw hvw
        have hv0 : 0 < v := lt_of_lt_of_le (by linarith) hv.1.1
        rw [dist_eq_norm]
        calc ‖σ w - σ v‖ ≤ M * (w - v) :=
              traj_dist_le hσ hm hbound hv0 hvw hw.1.2
          _ ≤ M * δ := by
              have h1 : w - v ≤ δ := by
                have := hv.1.1
                have := hw.1.2
                linarith
              exact mul_le_mul_of_nonneg_left h1 hM0
          _ ≤ M * (ε / (2 * (M + 1))) :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) hM0
          _ < ε := by
              rw [div_eq_mul_inv]
              have hM1 : 0 < M + 1 := by linarith
              have h2 : M * (ε * (2 * (M + 1))⁻¹) = ε * (M / (2 * (M + 1))) := by
                field_simp
              rw [h2]
              have h3 : M / (2 * (M + 1)) < 1 := by
                rw [div_lt_one (by positivity)]
                linarith
              calc ε * (M / (2 * (M + 1))) < ε * 1 :=
                    mul_lt_mul_of_pos_left h3 hε
                _ = ε := mul_one ε
      rcases le_total a b with hab | hab
      · rw [dist_comm]
        exact hgap a b ha hb hab
      · exact hgap b a hb ha hab
  obtain ⟨w, hw⟩ := CompleteSpace.complete hcauchy
  exact ⟨w, hw⟩

/-- Local step for the ambient development: at each tracked time the ambient chart
develops the trajectory affinely with a local sign. -/
theorem traj_ambient_local {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {I : Set ℝ} (hσ : IsTrajOn q σ I)
    {a b : ℝ} (hI : Set.Icc a b ⊆ I) {t : ℝ} (ht : t ∈ Set.Icc a b)
    (htS : σ t ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ᶠ u in nhdsWithin t (Set.Icc a b),
        Φ (σ u) = Φ (σ t) + ε * ((u - t : ℝ) : ℂ) := by
  obtain ⟨U, hUo, hpU, -, -, Φt, hΦtd, hΦtinj, hΦtsq, hev⟩ := hσ.chart t (hI ht)
  set p : ℂ := σ t with hpdef
  set Ω : Set ℂ := connectedComponentIn (U ∩ S) p with hΩdef
  have hΩo : IsOpen Ω := (hUo.inter hS).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hpΩ : p ∈ Ω := mem_connectedComponentIn ⟨hpU, htS⟩
  have hΩsub : Ω ⊆ U ∩ S := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φ z ^ 2 = deriv Φt z ^ 2 := fun z hz => by
    rw [hΦsq z (hΩsub hz).2, hΦtsq z (hΩsub hz).1]
  have hmono : nhdsWithin t (Set.Icc a b) ≤ nhdsWithin t I := nhdsWithin_mono t hI
  have hσΩ' : ∀ᶠ u in nhdsWithin t I, σ u ∈ Ω :=
    (hσ.cont t (hI ht)) (hΩo.mem_nhds hpΩ)
  have hσΩ : ∀ᶠ u in nhdsWithin t (Set.Icc a b), σ u ∈ Ω := hσΩ'.filter_mono hmono
  have hev' := hev.filter_mono hmono
  rcases open_branch_classification hΩo hΩconn hpΩ
      (hΦtd.mono (hΩsub.trans Set.inter_subset_left))
      (hΦd.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · refine ⟨1, Or.inl rfl, ?_⟩
    filter_upwards [hev', hσΩ] with u hu hΩu
    have h := hplus (σ u) hΩu
    rw [hu.2] at h
    rw [h, hplus p hpΩ]
    push_cast
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    filter_upwards [hev', hσΩ] with u hu hΩu
    have h := hminus (σ u) hΩu
    rw [hu.2] at h
    rw [h, hminus p hpΩ]
    push_cast
    ring

/-- **Coherent affine development in an ambient chart**: while a trajectory stays in the
domain of a natural chart, its development there is globally affine of one slope `±1`. -/
theorem traj_ambient_affine {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {I : Set ℝ} (hσ : IsTrajOn q σ I)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I)
    (htrack : ∀ t ∈ Set.Icc a b, σ t ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ t ∈ Set.Icc a b, Φ (σ t) = Φ (σ a) + ε * ((t - a : ℝ) : ℂ) := by
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  obtain ⟨ε, hε, heva⟩ := traj_ambient_local hS hΦd hΦsq hσ hI hamem (htrack a hamem)
  refine ⟨ε, hε, ?_⟩
  set A : Set ℝ := {t | t ∈ Set.Icc a b ∧
    ∀ u ∈ Set.Icc a t, Φ (σ u) = Φ (σ a) + ε * ((u - a : ℝ) : ℂ)} with hAdef
  have haA : a ∈ A := by
    refine ⟨hamem, fun u hu => ?_⟩
    have hua : u = a := le_antisymm hu.2 hu.1
    rw [hua]
    push_cast
    ring
  have hbdd : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  set c : ℝ := sSup A with hcdef
  have hcA : a ≤ c := le_csSup hbdd haA
  have hcb : c ≤ b := csSup_le ⟨a, haA⟩ (fun t ht => ht.1.2)
  have hc : c ∈ Set.Icc a b := ⟨hcA, hcb⟩
  have hup : ∀ u ∈ Set.Ico a c, Φ (σ u) = Φ (σ a) + ε * ((u - a : ℝ) : ℂ) := by
    intro u hu
    obtain ⟨t, htA, hut⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ hu.2
    exact htA.2 u ⟨hu.1, hut.le⟩
  have hsubIco : Set.Ico a c ⊆ Set.Icc a b := fun u hu => ⟨hu.1, le_trans hu.2.le hcb⟩
  have hΦcont : ContinuousWithinAt (fun u => Φ (σ u)) (Set.Icc a b) c := by
    have hΦca : ContinuousAt Φ (σ c) :=
      (hΦd.differentiableAt (hS.mem_nhds (htrack c hc))).continuousAt
    exact hΦca.comp_continuousWithinAt ((hσ.cont c (hI hc)).mono hI)
  have hcc : Φ (σ c) = Φ (σ a) + ε * ((c - a : ℝ) : ℂ) := by
    rcases eq_or_lt_of_le hcA with heq | hac
    · rw [← heq]
      push_cast
      ring
    · haveI hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
        refine mem_closure_iff_nhdsWithin_neBot.mp ?_
        rw [closure_Ico hac.ne]
        exact ⟨hac.le, le_refl c⟩
      have hlim : Filter.Tendsto (fun u => Φ (σ u)) (nhdsWithin c (Set.Ico a c))
          (nhds (Φ (σ c))) := hΦcont.mono_left (nhdsWithin_mono c hsubIco)
      have hlim2 : Filter.Tendsto (fun u : ℝ => Φ (σ a) + ε * ((u - a : ℝ) : ℂ))
          (nhdsWithin c (Set.Ico a c)) (nhds (Φ (σ a) + ε * ((c - a : ℝ) : ℂ))) := by
        refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
        exact (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_sub_right a)))).tendsto c
      have heqf : (fun u : ℝ => Φ (σ a) + ε * ((u - a : ℝ) : ℂ))
          =ᶠ[nhdsWithin c (Set.Ico a c)] fun u => Φ (σ u) :=
        eventually_mem_nhdsWithin.mono fun u hu => (hup u hu).symm
      exact tendsto_nhds_unique hlim (hlim2.congr' heqf)
  obtain ⟨εc, hεc, hevc⟩ := traj_ambient_local hS hΦd hΦsq hσ hI hc (htrack c hc)
  rcases eq_or_lt_of_le hcb with heqb | hclt
  · intro t htmem
    rcases eq_or_lt_of_le htmem.2 with htb | htb
    · rw [htb, ← heqb]
      exact hcc
    · exact hup t ⟨htmem.1, by rw [heqb]; exact htb⟩
  · exfalso
    have hab' : a < b := lt_of_le_of_lt hcA hclt
    have hεceq : εc = ε := by
      rcases eq_or_lt_of_le hcA with heq | hac
      · have hevc' : ∀ᶠ u in nhdsWithin a (Set.Icc a b),
            Φ (σ u) = Φ (σ a) + εc * ((u - a : ℝ) : ℂ) := by
          rw [← heq] at hevc
          exact hevc
        haveI hne : (nhdsWithin a (Set.Ioc a b)).NeBot := by
          refine mem_closure_iff_nhdsWithin_neBot.mp ?_
          rw [closure_Ioc hab'.ne]
          exact ⟨le_refl a, hab'.le⟩
        have hmono2 : nhdsWithin a (Set.Ioc a b) ≤ nhdsWithin a (Set.Icc a b) :=
          nhdsWithin_mono a (fun u hu => ⟨hu.1.le, hu.2⟩)
        obtain ⟨u, huIoc, h1, h2⟩ := (eventually_mem_nhdsWithin.and
          ((heva.filter_mono hmono2).and (hevc'.filter_mono hmono2))).exists
        have hune : ((u - a : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt huIoc.1))
        have := h1.symm.trans h2
        have hmul : ε * ((u - a : ℝ) : ℂ) = εc * ((u - a : ℝ) : ℂ) := by
          linear_combination this
        have : (ε : ℂ) = (εc : ℂ) := mul_right_cancel₀ hune hmul
        exact_mod_cast this.symm
      · haveI hne : (nhdsWithin c (Set.Ico a c)).NeBot := by
          refine mem_closure_iff_nhdsWithin_neBot.mp ?_
          rw [closure_Ico hac.ne]
          exact ⟨hac.le, le_refl c⟩
        have hmono2 : nhdsWithin c (Set.Ico a c) ≤ nhdsWithin c (Set.Icc a b) :=
          nhdsWithin_mono c hsubIco
        obtain ⟨u, huIco, h1⟩ := (eventually_mem_nhdsWithin.and
          (hevc.filter_mono hmono2)).exists
        have hune : ((u - c : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt huIco.2))
        have h2 := hup u huIco
        have hmul : εc * ((u - c : ℝ) : ℂ) = ε * ((u - c : ℝ) : ℂ) := by
          have h3 := hcc
          have h4 := h1
          rw [h2] at h4
          push_cast at h3 h4 ⊢
          linear_combination -h4 - h3
        have : (εc : ℂ) = (ε : ℂ) := mul_right_cancel₀ hune hmul
        exact_mod_cast this
    rw [hεceq] at hevc
    obtain ⟨V, hVo, hcV, hVsub⟩ := mem_nhdsWithin.mp hevc
    obtain ⟨δ', hδ', hballV⟩ := Metric.isOpen_iff.mp hVo c hcV
    set t' : ℝ := min b (c + δ' / 2) with ht'def
    have ht'c : c < t' := lt_min hclt (by linarith)
    have ht'A : t' ∈ A := by
      refine ⟨⟨le_trans hcA ht'c.le, min_le_left _ _⟩, ?_⟩
      intro u hu
      rcases le_or_gt u c with huc | huc
      · rcases eq_or_lt_of_le huc with hueq | hult
        · rw [hueq]
          exact hcc
        · exact hup u ⟨hu.1, hult⟩
      · have huV : Φ (σ u) = Φ (σ c) + ε * ((u - c : ℝ) : ℂ) := by
          refine hVsub ⟨hballV ?_, ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
          have := le_trans hu.2 (min_le_right _ _)
          linarith
        rw [huV, hcc]
        push_cast
        ring
    linarith [le_csSup hbdd ht'A]

/-- **Tail development at the limit time**: a trajectory converging at `c` inside one
natural chart develops affinely with a single sign up to the limit value. -/
theorem traj_tail_affine {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hσ : IsTrajOn q σ (Set.Ico 0 c))
    {w : ℂ} (hwS : w ∈ S)
    (hlim : Filter.Tendsto σ (nhdsWithin c (Set.Ico 0 c)) (nhds w))
    (htail : ∀ᶠ u in nhdsWithin c (Set.Ico 0 c), σ u ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ᶠ u in nhdsWithin c (Set.Ico 0 c),
        Φ (σ u) = Φ w + ε * ((u - c : ℝ) : ℂ) := by
  obtain ⟨V, hVo, hcV, hVsub⟩ := mem_nhdsWithin.mp htail
  obtain ⟨η₀, hη₀, hball⟩ := Metric.isOpen_iff.mp hVo c hcV
  set η : ℝ := min η₀ c with hηdef
  have hη : 0 < η := lt_min hη₀ hc
  have hηc : η ≤ c := min_le_right _ _
  set a₀ : ℝ := c - η / 2 with ha₀def
  set m₀ : ℝ := c - η / 4 with hm₀def
  have ha₀0 : 0 < a₀ := by
    have : η / 2 < c := by linarith
    linarith
  have ha₀m : a₀ < m₀ := by linarith
  have hm₀c : m₀ < c := by linarith
  have htrackIco : ∀ u ∈ Set.Ico a₀ c, σ u ∈ S := by
    intro u hu
    refine hVsub ⟨hball ?_, ⟨by linarith [hu.1], hu.2⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hu.2]), neg_sub]
    have := hu.1
    have := min_le_left η₀ c
    linarith
  have hsubI : ∀ b₀ : ℝ, b₀ < c → Set.Icc a₀ b₀ ⊆ Set.Ico 0 c := fun b₀ hb₀ u hu =>
    ⟨by linarith [hu.1], lt_of_le_of_lt hu.2 hb₀⟩
  obtain ⟨ε, hε, haff⟩ := traj_ambient_affine hS hΦd hΦsq hσ ha₀m.le
    (hsubI m₀ hm₀c) (fun t ht => htrackIco t ⟨ht.1, lt_of_le_of_lt ht.2 hm₀c⟩)
  have hall : ∀ u ∈ Set.Ico a₀ c, Φ (σ u) = Φ (σ a₀) + ε * ((u - a₀ : ℝ) : ℂ) := by
    intro u hu
    rcases le_total u m₀ with hum | hum
    · exact haff u ⟨hu.1, hum⟩
    · obtain ⟨ε', hε', haff'⟩ := traj_ambient_affine hS hΦd hΦsq hσ
        (le_trans ha₀m.le hum) (hsubI u hu.2)
        (fun t ht => htrackIco t ⟨ht.1, lt_of_le_of_lt ht.2 hu.2⟩)
      have hpin : ε' = ε := by
        have h1 := haff' m₀ ⟨ha₀m.le, hum⟩
        have h2 := haff m₀ (Set.right_mem_Icc.mpr ha₀m.le)
        have hne : ((m₀ - a₀ : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ha₀m.ne')
        have hmul : (ε' : ℂ) * ((m₀ - a₀ : ℝ) : ℂ) = ε * ((m₀ - a₀ : ℝ) : ℂ) := by
          rw [h2] at h1
          linear_combination -h1
        exact_mod_cast mul_right_cancel₀ hne hmul
      rw [← hpin]
      exact haff' u (Set.right_mem_Icc.mpr (le_trans ha₀m.le hum))
  haveI hne : (nhdsWithin c (Set.Ico 0 c)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico hc.ne]
    exact ⟨hc.le, le_refl c⟩
  have hevIco : ∀ᶠ u in nhdsWithin c (Set.Ico 0 c), u ∈ Set.Ico a₀ c := by
    refine mem_nhdsWithin.mpr ⟨Set.Ioo a₀ (c + 1), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, ?_⟩
    rintro u ⟨hu1, hu2⟩
    exact ⟨hu1.1.le, hu2.2⟩
  have hΦw : Φ w = Φ (σ a₀) + ε * ((c - a₀ : ℝ) : ℂ) := by
    have hΦca : ContinuousAt Φ w :=
      (hΦd.differentiableAt (hS.mem_nhds hwS)).continuousAt
    have h1 : Filter.Tendsto (fun u => Φ (σ u)) (nhdsWithin c (Set.Ico 0 c))
        (nhds (Φ w)) := hΦca.tendsto.comp hlim
    have h2 : Filter.Tendsto (fun u : ℝ => Φ (σ a₀) + ε * ((u - a₀ : ℝ) : ℂ))
        (nhdsWithin c (Set.Ico 0 c))
        (nhds (Φ (σ a₀) + ε * ((c - a₀ : ℝ) : ℂ))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_sub_right a₀)))).tendsto c
    have heqf : (fun u : ℝ => Φ (σ a₀) + ε * ((u - a₀ : ℝ) : ℂ))
        =ᶠ[nhdsWithin c (Set.Ico 0 c)] fun u => Φ (σ u) :=
      hevIco.mono fun u hu => (hall u hu).symm
    exact tendsto_nhds_unique h1 (h2.congr' heqf)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hevIco] with u hu
  rw [hall u hu, hΦw]
  push_cast
  ring

/-- Below the limit time the closed and half-open time intervals induce the same
within-filter. -/
theorem nhdsWithin_Ico {c t : ℝ} (ht : t < c) :
    nhdsWithin t (Set.Icc 0 c) = nhdsWithin t (Set.Ico 0 c) := by
  have hio : Set.Iio c ∈ nhds t := Iio_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Ico 0 c) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.le⟩, h3⟩

/-- **Limit closure**: a trajectory on `[0, c)` converging at `c` to a regular point of
the upper half plane closes to a trajectory on `[0, c]`. -/
theorem traj_close {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {σ : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hσ : IsTrajOn q σ (Set.Ico 0 c))
    {w : ℂ} (hw : 0 < w.im) (hqw : q w ≠ 0)
    (hlim : Filter.Tendsto σ (nhdsWithin c (Set.Ico 0 c)) (nhds w)) :
    ∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Ico 0 c) ∧ σ' c = w ∧
      IsTrajOn q σ' (Set.Icc 0 c) := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨r, hr, hsubH, Φ, hΦd0, hΦinj0, hΦsq0⟩ :=
    exists_natural_chart (q := fun z => -q z) hH hq.neg hw (neg_ne_zero.mpr hqw)
  have hqc : ContinuousAt q w := hq.continuousOn.continuousAt (hH.mem_nhds hw)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hqc (isOpen_ne.mem_nhds hqw) : q ⁻¹' {x | x ≠ 0} ∈ nhds w)
      (Metric.ball_mem_nhds w hr))
  set S : Set ℂ := Metric.ball w r₁ with hSdef
  have hSr : S ⊆ Metric.ball w r := fun x hx => (hball hx).2
  have hSne : ∀ x ∈ S, q x ≠ 0 := fun x hx => (hball hx).1
  have hSo : IsOpen S := Metric.isOpen_ball
  have hSH : S ⊆ {z : ℂ | 0 < z.im} := hSr.trans hsubH
  have hwS : w ∈ S := Metric.mem_ball_self hr₁
  have hΦd : DifferentiableOn ℂ Φ S := hΦd0.mono hSr
  have hΦinj : Set.InjOn Φ S := hΦinj0.mono hSr
  have hΦsq : ∀ x ∈ S, deriv Φ x ^ 2 = -q x := fun x hx => hΦsq0 x (hSr hx)
  have htail : ∀ᶠ u in nhdsWithin c (Set.Ico 0 c), σ u ∈ S := hlim (hSo.mem_nhds hwS)
  obtain ⟨ε, hε, hgerm⟩ := traj_tail_affine hSo hΦd hΦsq hc hσ hwS hlim htail
  have hε2 : ((ε : ℝ) : ℂ) ^ 2 = 1 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  have hεne : ((ε : ℝ) : ℂ) ≠ 0 := by
    rcases hε with h | h <;> rw [h] <;> norm_num
  set σ' : ℝ → ℂ := fun t => if t < c then σ t else w with hσ'def
  have hEq : Set.EqOn σ' σ (Set.Ico 0 c) := fun u hu => if_pos hu.2
  have hσ'c : σ' c = w := if_neg (lt_irrefl c)
  have hsplit : ∀ t : ℝ, nhdsWithin t (Set.Icc 0 c)
      = nhdsWithin t (Set.Ico 0 c) ⊔ nhdsWithin t {c} := by
    intro t
    rw [← nhdsWithin_union, Set.Ico_union_right hc.le]
  refine ⟨σ', hEq, hσ'c, ?_, ?_⟩
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with htc | htc
    · show Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 c)) (nhds (σ' t))
      rw [nhdsWithin_Ico htc, hEq ⟨ht.1, htc⟩]
      exact Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
        (hσ.cont t ⟨ht.1, htc⟩)
    · show Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 c)) (nhds (σ' t))
      rw [htc, hsplit c, Filter.tendsto_sup, hσ'c]
      constructor
      · exact Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm) hlim
      · rw [nhdsWithin_singleton]
        have : Filter.Tendsto σ' (pure c) (nhds (σ' c)) := tendsto_pure_nhds σ' c
        rwa [hσ'c] at this
  · intro t ht
    rcases lt_or_eq_of_le ht.2 with htc | htc
    · obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hσ.chart t ⟨ht.1, htc⟩
      refine ⟨Ut, hUto, by rw [hEq ⟨ht.1, htc⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_Ico htc]
      filter_upwards [hevt, eventually_mem_nhdsWithin] with u hu huIco
      rw [hEq huIco, hEq ⟨ht.1, htc⟩]
      exact hu
    · subst htc
      refine ⟨S, hSo, by rw [hσ'c]; exact hwS, hSH, hSne,
        fun z => ((ε : ℝ) : ℂ) * Φ z,
        fun x hx => ((hΦd x hx).const_mul _), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        exact hΦinj hx hy (mul_left_cancel₀ hεne hxy)
      · intro x hx
        have hdiff : DifferentiableAt ℂ Φ x := hΦd.differentiableAt (hSo.mem_nhds hx)
        have hd : deriv (fun z => ((ε : ℝ) : ℂ) * Φ z) x = ((ε : ℝ) : ℂ) * deriv Φ x :=
          deriv_const_mul _ hdiff
        rw [hd, mul_pow, hε2, one_mul]
        exact hΦsq x hx
      · rw [hsplit t, Filter.eventually_sup]
        constructor
        · filter_upwards [hgerm, htail, eventually_mem_nhdsWithin] with u hg hSu hu
          rw [hEq hu, hσ'c]
          refine ⟨hSu, ?_⟩
          rw [hg]
          linear_combination ((u - t : ℝ) : ℂ) * hε2
        · rw [nhdsWithin_singleton]
          rw [Filter.eventually_pure]
          rw [hσ'c]
          refine ⟨hwS, ?_⟩
          rw [sub_self]
          push_cast
          ring

/-- Restriction of a vertical trajectory to a smaller time set. -/
theorem traj_mono {q : ℂ → ℂ} {σ : ℝ → ℂ} {s s' : Set ℝ}
    (h : IsTrajOn q σ s) (hsub : s' ⊆ s) : IsTrajOn q σ s' := by
  constructor
  · exact h.cont.mono hsub
  · intro t ht
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := h.chart t (hsub ht)
    exact ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq,
      hev.filter_mono (nhdsWithin_mono t hsub)⟩

/-- Two trajectories sharing the seed coincide on the common time interval. -/
theorem traj_coherent {q : ℂ → ℂ} {σ₀ σ₁ σ₂ : ℝ → ℂ} {δ₀ b₁ b₂ : ℝ}
    (hδ₀ : 0 < δ₀) (hδb : δ₀ ≤ b₁) (hb : b₁ ≤ b₂)
    (h₁ : IsTrajOn q σ₁ (Set.Icc 0 b₁)) (h₂ : IsTrajOn q σ₂ (Set.Icc 0 b₂))
    (hE₁ : Set.EqOn σ₁ σ₀ (Set.Icc 0 δ₀)) (hE₂ : Set.EqOn σ₂ σ₀ (Set.Icc 0 δ₀)) :
    Set.EqOn σ₁ σ₂ (Set.Icc 0 b₁) := by
  have h0b : (0 : ℝ) ≤ b₁ := le_trans hδ₀.le hδb
  refine traj_unique h0b h₁ (traj_mono h₂ (Set.Icc_subset_Icc le_rfl hb)) ?_
  refine mem_nhdsWithin.mpr ⟨Set.Iio δ₀, isOpen_Iio, hδ₀, ?_⟩
  rintro u ⟨hu1, hu2⟩
  have huδ : u ∈ Set.Icc 0 δ₀ := ⟨hu2.1, le_of_lt hu1⟩
  show σ₁ u = σ₂ u
  rw [hE₁ huδ, hE₂ huδ]

/-- Below an inner cutoff the long half-open and short closed time intervals induce the
same within-filter. -/
theorem nhdsWithin_agree {b c t : ℝ} (ht : t < b) (hbc : b ≤ c) :
    nhdsWithin t (Set.Ico 0 c) = nhdsWithin t (Set.Icc 0 b) := by
  have hio : Set.Iio b ∈ nhds t := Iio_mem_nhds ht
  rw [nhdsWithin_restrict' _ hio, nhdsWithin_restrict' (Set.Icc 0 b) hio]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ico, Set.mem_Iio]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h3.le⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, lt_of_lt_of_le h3 hbc⟩, h3⟩

/-- **The coherent family below the supremum**: coherent trajectories on every closed
interval strictly below `c` assemble into one trajectory on `[0, c)`. -/
theorem traj_family {q : ℂ → ℂ} {σ₀ : ℝ → ℂ} {δ₀ c : ℝ}
    (hδ₀ : 0 < δ₀) (hδc : δ₀ < c)
    (hA : ∀ b ∈ Set.Ico δ₀ c, ∃ σ : ℝ → ℂ,
      Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧ IsTrajOn q σ (Set.Icc 0 b)) :
    ∃ σ : ℝ → ℂ, Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧ IsTrajOn q σ (Set.Ico 0 c) := by
  choose! F hF1 hF2 using hA
  set pick : ℝ → ℝ := fun t => if t < c then max δ₀ ((t + c) / 2) else δ₀ with hpickdef
  have hpick_mem : ∀ t, pick t ∈ Set.Ico δ₀ c := by
    intro t
    by_cases h : t < c
    · rw [hpickdef]
      simp only [if_pos h]
      exact ⟨le_max_left _ _, max_lt hδc (by linarith)⟩
    · rw [hpickdef]
      simp only [if_neg h]
      exact ⟨le_refl _, hδc⟩
  have hpick_gt : ∀ t, 0 ≤ t → t < c → t < pick t := by
    intro t ht htc
    rw [hpickdef]
    simp only [if_pos htc]
    exact lt_max_of_lt_right (by linarith)
  set σ : ℝ → ℂ := fun t => F (pick t) t with hσdef
  have hcoh : ∀ b ∈ Set.Ico δ₀ c, ∀ u ∈ Set.Icc 0 b, σ u = F b u := by
    intro b hb u hu
    have huc : u < c := lt_of_le_of_lt hu.2 hb.2
    have hup : u < pick u := hpick_gt u hu.1 huc
    have hpu := hpick_mem u
    rcases le_total (pick u) b with hpb | hpb
    · exact traj_coherent hδ₀ hpu.1 hpb (hF2 (pick u) hpu) (hF2 b hb)
        (hF1 (pick u) hpu) (hF1 b hb) ⟨hu.1, hup.le⟩
    · exact (traj_coherent hδ₀ hb.1 hpb (hF2 b hb) (hF2 (pick u) hpu)
        (hF1 b hb) (hF1 (pick u) hpu) hu).symm
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro u hu
    have hδmem : δ₀ ∈ Set.Ico δ₀ c := ⟨le_refl _, hδc⟩
    rw [hcoh δ₀ hδmem u hu]
    exact hF1 δ₀ hδmem hu
  · intro t ht
    have hb := hpick_mem t
    have htb : t < pick t := hpick_gt t ht.1 ht.2
    have hσt : σ t = F (pick t) t := hcoh (pick t) hb t ⟨ht.1, htb.le⟩
    show Filter.Tendsto σ (nhdsWithin t (Set.Ico 0 c)) (nhds (σ t))
    rw [nhdsWithin_agree htb hb.2.le, hσt]
    refine Filter.Tendsto.congr' ?_ ((hF2 (pick t) hb).cont t ⟨ht.1, htb.le⟩)
    exact eventually_mem_nhdsWithin.mono fun u hu => (hcoh (pick t) hb u hu).symm
  · intro t ht
    have hb := hpick_mem t
    have htb : t < pick t := hpick_gt t ht.1 ht.2
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ :=
      (hF2 (pick t) hb).chart t ⟨ht.1, htb.le⟩
    have hσt : σ t = F (pick t) t := hcoh (pick t) hb t ⟨ht.1, htb.le⟩
    refine ⟨U, hUo, by rw [hσt]; exact hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
    rw [nhdsWithin_agree htb hb.2.le]
    filter_upwards [hev, eventually_mem_nhdsWithin] with u hu huI
    rw [hcoh (pick t) hb u huI, hσt]
    exact hu

/-- **All-time-or-escape dichotomy**: a seed trajectory either continues coherently to
every time, or some coherent continuation leaves any prescribed compact set of regular
points. -/
theorem traj_dichotomy {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {σ₀ : ℝ → ℂ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hσ₀ : IsTrajOn q σ₀ (Set.Icc 0 δ₀))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im})
    (hKne : ∀ x ∈ K, q x ≠ 0) :
    (∀ T, δ₀ ≤ T → ∃ σ : ℝ → ℂ, Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧
      IsTrajOn q σ (Set.Icc 0 T)) ∨
    (∃ b, δ₀ ≤ b ∧ ∃ σ : ℝ → ℂ, Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧
      IsTrajOn q σ (Set.Icc 0 b) ∧ ∃ t ∈ Set.Icc 0 b, σ t ∉ K) := by
  by_cases hall : ∀ T, δ₀ ≤ T → ∃ σ : ℝ → ℂ, Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧
      IsTrajOn q σ (Set.Icc 0 T)
  · exact Or.inl hall
  right
  by_contra hnoexit
  rcases not_forall.mp hall with ⟨T₀, hT₀⟩
  rw [Classical.not_imp] at hT₀
  set A : Set ℝ := {b | δ₀ ≤ b ∧ ∃ σ : ℝ → ℂ, Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧
    IsTrajOn q σ (Set.Icc 0 b)} with hAdef
  have hδA : δ₀ ∈ A := ⟨le_rfl, σ₀, fun u _ => rfl, hσ₀⟩
  have hbdd : BddAbove A := by
    refine ⟨T₀, fun b hb => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨hδb, σb, hEb, hTb⟩ := hb
    exact hT₀.2 ⟨σb, hEb, traj_mono hTb (Set.Icc_subset_Icc le_rfl hlt.le)⟩
  set c : ℝ := sSup A with hcdef
  have hδc : δ₀ ≤ c := le_csSup hbdd hδA
  have hc0 : 0 < c := lt_of_lt_of_le hδ₀ hδc
  have hcnA : c ∉ A := by
    rintro ⟨hδc', σc, hEqc, hTrajc⟩
    obtain ⟨δ', hδ', σ'', hE'', hT''⟩ := traj_extend hq hc0.le hTrajc
    have hcA : c + δ' ∈ A := by
      refine ⟨by linarith, σ'', fun u hu => ?_, hT''⟩
      rw [hE'' ⟨hu.1, le_trans hu.2 hδc⟩]
      exact hEqc hu
    have := le_csSup hbdd hcA
    linarith
  have hδc_lt : δ₀ < c := lt_of_le_of_ne hδc (fun h => hcnA (h ▸ hδA))
  have hint : ∀ b ∈ Set.Ico δ₀ c, ∃ σ : ℝ → ℂ,
      Set.EqOn σ σ₀ (Set.Icc 0 δ₀) ∧ IsTrajOn q σ (Set.Icc 0 b) := by
    intro b hb
    obtain ⟨b', hb'A, hbb'⟩ := exists_lt_of_lt_csSup ⟨δ₀, hδA⟩ hb.2
    obtain ⟨hδb', σb, hEb, hTb⟩ := hb'A
    exact ⟨σb, hEb, traj_mono hTb (Set.Icc_subset_Icc le_rfl hbb'.le)⟩
  obtain ⟨σi, hEi, hTi⟩ := traj_family hδ₀ hδc_lt hint
  have htrack : ∀ t ∈ Set.Ico 0 c, σi t ∈ K := by
    intro t ht
    set b : ℝ := max δ₀ ((t + c) / 2) with hbdef
    have hbc : b < c := max_lt hδc_lt (by linarith [ht.2])
    have htb : t ≤ b := le_trans (by linarith [ht.2]) (le_max_right _ _)
    have hsub : Set.Icc 0 b ⊆ Set.Ico 0 c := fun u hu =>
      ⟨hu.1, lt_of_le_of_lt hu.2 hbc⟩
    by_contra hout
    exact hnoexit ⟨b, le_max_left _ _, σi, hEi, traj_mono hTi hsub,
      t, ⟨ht.1, htb⟩, hout⟩
  have hKnonempty : K.Nonempty := ⟨σi 0, htrack 0 ⟨le_refl 0, hc0⟩⟩
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKnonempty
    ((hq.continuousOn.mono hKH).norm)
  have hm : 0 < ‖q x₀‖ := norm_pos_iff.mpr (hKne x₀ hx₀K)
  have hbound : ∀ t ∈ Set.Ico 0 c, ‖q x₀‖ ≤ ‖q (σi t)‖ := fun t ht =>
    hx₀min (htrack t ht)
  obtain ⟨w, hlim⟩ := traj_limit hc0 hTi hm hbound
  haveI hne : (nhdsWithin c (Set.Ico 0 c)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico hc0.ne]
    exact ⟨hc0.le, le_refl c⟩
  have hwK : w ∈ K := hK.isClosed.mem_of_tendsto hlim
    (eventually_mem_nhdsWithin.mono fun u hu => htrack u hu)
  obtain ⟨σ', hE', hσ'c, hT'⟩ := traj_close hq hc0 hTi (hKH hwK)
    (hKne w hwK) hlim
  refine hcnA ⟨hδc, σ', fun u hu => ?_, hT'⟩
  rw [hE' ⟨hu.1, lt_of_le_of_lt hu.2 hδc_lt⟩]
  exact hEi hu


/-- A rational complex point within any prescribed distance of a given point. -/
theorem exists_rat_near_complex (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℚ × ℚ, ‖z - (((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I)‖ < δ := by
  obtain ⟨q₁, hq₁⟩ := exists_rat_near z.re (by positivity : (0 : ℝ) < δ / 2)
  obtain ⟨q₂, hq₂⟩ := exists_rat_near z.im (by positivity : (0 : ℝ) < δ / 2)
  refine ⟨(q₁, q₂), ?_⟩
  set w : ℂ := z - (((q₁ : ℝ) : ℂ) + ((q₂ : ℝ) : ℂ) * Complex.I) with hwdef
  have hre : w.re = z.re - (q₁ : ℝ) := by
    simp [hwdef, Complex.sub_re, Complex.add_re, Complex.mul_re]
  have him : w.im = z.im - (q₂ : ℝ) := by
    simp [hwdef, Complex.sub_im, Complex.add_im, Complex.mul_im]
  have h1 : |w.re| < δ / 2 := by rw [hre]; exact hq₁
  have h2 : |w.im| < δ / 2 := by rw [him]; exact hq₂
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ < δ := by linarith

/-- **A countable atlas of natural charts with margins**: countably many chart balls,
each with doubled radius inside the regular part of the upper half plane, whose unit
radii cover every regular point. -/
theorem exists_countable_atlas {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) :
    ∃ (c : ℕ → ℂ) (r : ℕ → ℝ) (Φ : ℕ → ℂ → ℂ) (active : ℕ → Prop),
      (∀ j, active j → 0 < r j) ∧
      (∀ j, active j → Metric.ball (c j) (2 * r j) ⊆ {z : ℂ | 0 < z.im}) ∧
      (∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), q w ≠ 0) ∧
      (∀ j, active j → DifferentiableOn ℂ (Φ j) (Metric.ball (c j) (2 * r j))) ∧
      (∀ j, active j → Set.InjOn (Φ j) (Metric.ball (c j) (2 * r j))) ∧
      (∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), deriv (Φ j) w ^ 2 = -q w) ∧
      (∀ z, 0 < z.im → q z ≠ 0 → ∃ j, active j ∧ z ∈ Metric.ball (c j) (r j)) ∧
      (∀ j, ¬ active j → Φ j = id) := by
  classical
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  -- the chartability predicate on rational data
  set embed : (ℚ × ℚ) × ℚ → ℂ × ℝ := fun p =>
    ((((p.1.1 : ℝ) : ℂ) + ((p.1.2 : ℝ) : ℂ) * Complex.I), (p.2 : ℝ)) with hembdef
  set P : (ℚ × ℚ) × ℚ → Prop := fun p =>
    0 < (embed p).2 ∧ Metric.ball (embed p).1 (2 * (embed p).2) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ w ∈ Metric.ball (embed p).1 (2 * (embed p).2), q w ≠ 0) ∧
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (Metric.ball (embed p).1 (2 * (embed p).2)) ∧
      Set.InjOn Ψ (Metric.ball (embed p).1 (2 * (embed p).2)) ∧
      ∀ w ∈ Metric.ball (embed p).1 (2 * (embed p).2), deriv Ψ w ^ 2 = -q w with hPdef
  obtain ⟨e, he⟩ := exists_surjective_nat ((ℚ × ℚ) × ℚ)
  refine ⟨fun j => (embed (e j)).1, fun j => (embed (e j)).2,
    fun j => if h : P (e j) then h.2.2.2.choose else id, fun j => P (e j),
    fun j hj => hj.1, fun j hj => hj.2.1, fun j hj => hj.2.2.1, ?_, ?_, ?_, ?_,
    fun j hj => dif_neg hj⟩
  · intro j hj
    simp only [dif_pos hj]
    exact hj.2.2.2.choose_spec.1
  · intro j hj
    simp only [dif_pos hj]
    exact hj.2.2.2.choose_spec.2.1
  · intro j hj
    simp only [dif_pos hj]
    exact hj.2.2.2.choose_spec.2.2
  · intro z hz hq0
    -- a chart ball around `z` avoiding the zeros
    obtain ⟨R₀, hR₀, hsubH, Ψ, hΨd, hΨinj, hΨsq⟩ :=
      exists_natural_chart (q := fun w => -q w) hH hq.neg hz (neg_ne_zero.mpr hq0)
    have hqc : ContinuousAt q z := hq.continuousOn.continuousAt (hH.mem_nhds hz)
    obtain ⟨R₁, hR₁, hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hqc (isOpen_ne.mem_nhds hq0) : q ⁻¹' {x | x ≠ 0} ∈ nhds z)
        (Metric.ball_mem_nhds z hR₀))
    set R : ℝ := min R₁ R₀ with hRdef
    have hR : 0 < R := lt_min hR₁ hR₀
    obtain ⟨a, ha⟩ := exists_rat_near_complex z (by positivity : (0 : ℝ) < R / 8)
    obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (by linarith : R / 8 < R / 4)
    obtain ⟨j, hj⟩ := he (a, ρ)
    set A : ℂ := ((a.1 : ℝ) : ℂ) + ((a.2 : ℝ) : ℂ) * Complex.I with hAdef
    have hsub2 : Metric.ball A (2 * (ρ : ℝ)) ⊆ Metric.ball z R := by
      intro w hw
      rw [Metric.mem_ball] at hw ⊢
      have hzA : dist z A < R / 8 := by rw [dist_eq_norm]; exact ha
      calc dist w z ≤ dist w A + dist A z := dist_triangle _ _ _
        _ < 2 * (ρ : ℝ) + R / 8 := by
            rw [dist_comm A z]
            linarith
        _ < R := by linarith
    have hsubR : Metric.ball z R ⊆ Metric.ball z R₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hPa : P (a, ρ) := by
      refine ⟨by exact_mod_cast lt_trans (by linarith) hρ1, ?_, ?_, Ψ, ?_, ?_, ?_⟩
      · exact (hsub2.trans hsubR).trans hsubH
      · intro w hw
        exact (hball (Metric.ball_subset_ball (min_le_left _ _) (hsub2 hw))).1
      · exact hΨd.mono (hsub2.trans hsubR)
      · exact hΨinj.mono (hsub2.trans hsubR)
      · exact fun w hw => hΨsq w (hsubR (hsub2 hw))
    refine ⟨j, ?_, ?_⟩
    · show P (e j)
      rw [hj]
      exact hPa
    · show z ∈ Metric.ball (embed (e j)).1 (embed (e j)).2
      rw [hj]
      show z ∈ Metric.ball A ((ρ : ℚ) : ℝ)
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖z - A‖ < R / 8 := ha
        _ < (ρ : ℝ) := hρ1

/-- **Chart-branch ratio**: on the connected component of a chart overlap two natural
charts differ by an affine map `z ↦ ε z + k`, and the sign is read off the derivative
ratio at the base point. -/
theorem chart_ratio {q Φ₁ Φ₂ : ℂ → ℂ} {S₁ S₂ : Set ℂ}
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂)
    (h₁d : DifferentiableOn ℂ Φ₁ S₁) (h₂d : DifferentiableOn ℂ Φ₂ S₂)
    (h₁sq : ∀ w ∈ S₁, deriv Φ₁ w ^ 2 = -q w) (h₂sq : ∀ w ∈ S₂, deriv Φ₂ w ^ 2 = -q w)
    {x : ℂ} (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ deriv Φ₂ x = ε * deriv Φ₁ x ∧
      ∀ z ∈ connectedComponentIn (S₁ ∩ S₂) x,
        Φ₂ z = ε * Φ₁ z + (Φ₂ x - ε * Φ₁ x) := by
  set Ω : Set ℂ := connectedComponentIn (S₁ ∩ S₂) x with hΩdef
  have hΩo : IsOpen Ω := (hS₁.inter hS₂).connectedComponentIn
  have hΩconn : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hxΩ : x ∈ Ω := mem_connectedComponentIn ⟨hx₁, hx₂⟩
  have hΩsub : Ω ⊆ S₁ ∩ S₂ := connectedComponentIn_subset _ _
  have hsq' : ∀ z ∈ Ω, deriv Φ₂ z ^ 2 = deriv Φ₁ z ^ 2 := fun z hz => by
    rw [h₂sq z (hΩsub hz).2, h₁sq z (hΩsub hz).1]
  have hΩnhds : Ω ∈ nhds x := hΩo.mem_nhds hxΩ
  rcases open_branch_classification hΩo hΩconn hxΩ
      (h₁d.mono (hΩsub.trans Set.inter_subset_left))
      (h₂d.mono (hΩsub.trans Set.inter_subset_right)) hsq' with hplus | hminus
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · have hev : Φ₂ =ᶠ[nhds x] fun z => Φ₁ z + (Φ₂ x - Φ₁ x) := by
        filter_upwards [hΩnhds] with z hz
        exact hplus z hz
      rw [hev.deriv_eq]
      have hd₁ : DifferentiableAt ℂ Φ₁ x := h₁d.differentiableAt (hS₁.mem_nhds hx₁)
      rw [deriv_add_const]
      push_cast
      ring
    · intro z hz
      rw [hplus z hz]
      push_cast
      ring
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · have hev : Φ₂ =ᶠ[nhds x] fun z => (Φ₂ x + Φ₁ x) - Φ₁ z := by
        filter_upwards [hΩnhds] with z hz
        exact hminus z hz
      rw [hev.deriv_eq, deriv_const_sub]
      push_cast
      ring
    · intro z hz
      rw [hminus z hz]
      push_cast
      ring

/-- A **countable natural-chart atlas with margins** for `q`: chart balls with doubled
radius inside the regular upper half plane whose unit radii cover every regular point. -/
structure Atlas (q : ℂ → ℂ) where
  c : ℕ → ℂ
  r : ℕ → ℝ
  Φ : ℕ → ℂ → ℂ
  active : ℕ → Prop
  hr : ∀ j, active j → 0 < r j
  hH : ∀ j, active j → Metric.ball (c j) (2 * r j) ⊆ {z : ℂ | 0 < z.im}
  hne : ∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), q w ≠ 0
  hd : ∀ j, active j → DifferentiableOn ℂ (Φ j) (Metric.ball (c j) (2 * r j))
  hinj : ∀ j, active j → Set.InjOn (Φ j) (Metric.ball (c j) (2 * r j))
  hsq : ∀ j, active j → ∀ w ∈ Metric.ball (c j) (2 * r j), deriv (Φ j) w ^ 2 = -q w
  hcover : ∀ z, 0 < z.im → q z ≠ 0 → ∃ j, active j ∧ z ∈ Metric.ball (c j) (r j)
  hjunk : ∀ j, ¬ active j → Φ j = id

/-- Every holomorphic `q` admits a countable margin atlas. -/
theorem exists_atlas {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) : Nonempty (Atlas q) := by
  obtain ⟨c, r, Φ, active, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_countable_atlas hq
  exact ⟨⟨c, r, Φ, active, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

open Classical in
/-- The measurable chart selector: the least active atlas index whose unit ball contains
the point. -/
noncomputable def Atlas.sel {q : ℂ → ℂ} (A : Atlas q) (z : ℂ) : ℕ :=
  if h : ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j) then Nat.find h else 0

theorem Atlas.sel_spec {q : ℂ → ℂ} (A : Atlas q) {z : ℂ}
    (hz : 0 < z.im) (hq0 : q z ≠ 0) :
    A.active (A.sel z) ∧ z ∈ Metric.ball (A.c (A.sel z)) (A.r (A.sel z)) := by
  classical
  have h : ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j) := A.hcover z hz hq0
  rw [Atlas.sel, dif_pos h]
  exact Nat.find_spec h

/-- Measurability of the chart selector. -/
theorem Atlas.measurable_sel {q : ℂ → ℂ} (A : Atlas q) :
    Measurable A.sel := by
  classical
  have hpset : ∀ i, MeasurableSet {z : ℂ | A.active i ∧
      z ∈ Metric.ball (A.c i) (A.r i)} := by
    intro i
    by_cases hi : A.active i
    · have : {z : ℂ | A.active i ∧ z ∈ Metric.ball (A.c i) (A.r i)}
          = Metric.ball (A.c i) (A.r i) := by
        ext z
        simp [hi]
      rw [this]
      exact measurableSet_ball
    · have : {z : ℂ | A.active i ∧ z ∈ Metric.ball (A.c i) (A.r i)} = ∅ := by
        ext z
        simp [hi]
      rw [this]
      exact MeasurableSet.empty
  have hE : MeasurableSet {z : ℂ | ∃ j, A.active j ∧
      z ∈ Metric.ball (A.c j) (A.r j)} := by
    have : {z : ℂ | ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)}
        = ⋃ j, {z : ℂ | A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)} := by
      ext z
      simp
    rw [this]
    exact MeasurableSet.iUnion hpset
  refine measurable_to_countable' fun n => ?_
  have hfib : A.sel ⁻¹' {n} = ({z : ℂ | ∃ j, A.active j ∧
        z ∈ Metric.ball (A.c j) (A.r j)} ∩ ({z : ℂ | A.active n ∧
        z ∈ Metric.ball (A.c n) (A.r n)} ∩ ⋂ i ∈ Set.Iio n, {z : ℂ | A.active i ∧
        z ∈ Metric.ball (A.c i) (A.r i)}ᶜ))
      ∪ ({z : ℂ | ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)}ᶜ
        ∩ (if n = 0 then Set.univ else ∅)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iInter, Set.mem_Iio]
    constructor
    · intro hsel
      by_cases h : ∃ j, A.active j ∧ z ∈ Metric.ball (A.c j) (A.r j)
      · rw [Atlas.sel, dif_pos h] at hsel
        refine Or.inl ⟨h, ?_, ?_⟩
        · rw [← hsel]
          exact Nat.find_spec h
        · intro i hi
          rw [← hsel] at hi
          exact Nat.find_min h hi
      · rw [Atlas.sel, dif_neg h] at hsel
        refine Or.inr ⟨h, ?_⟩
        rw [← hsel]
        simp
    · rintro (⟨h, hn, hmin⟩ | ⟨h, hn⟩)
      · rw [Atlas.sel, dif_pos h]
        exact (Nat.find_eq_iff h).mpr ⟨hn, fun i hi => hmin i hi⟩
      · rw [Atlas.sel, dif_neg h]
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exact h0.symm
        · rw [if_neg h0.ne'] at hn
          exact absurd hn (Set.notMem_empty z)
  rw [hfib]
  refine (hE.inter ((hpset n).inter ?_)).union (hE.compl.inter ?_)
  · exact MeasurableSet.biInter ((Set.finite_Iio n).countable) fun i _ => (hpset i).compl
  · by_cases h0 : n = 0
    · rw [if_pos h0]
      exact MeasurableSet.univ
    · rw [if_neg h0]
      exact MeasurableSet.empty

/-- The developed image of a zero-free natural chart domain is open. -/
theorem chart_image_open {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hd : DifferentiableOn ℂ Φ S) (hne : ∀ w ∈ S, q w ≠ 0)
    (hsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w) : IsOpen (Φ '' S) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨p, hpS, rfl⟩
  have hder : deriv Φ p ≠ 0 := by
    intro h0
    apply hne p hpS
    have := hsq p hpS
    rw [h0] at this
    simpa using this.symm
  have han : AnalyticAt ℂ Φ p := (hd.analyticOnNhd hS) p hpS
  have hstrict : HasStrictDerivAt Φ (deriv Φ p) p :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  rw [← hstrict.map_nhds_eq hder]
  exact Filter.image_mem_map (hS.mem_nhds hpS)

/-- **Measurability of the chart inverse**: the set inverse of an injective map with open
image, continuous inverse on the image, and constant junk off the image. -/
theorem invFunOn_measurable {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (himg : IsOpen (Φ '' S)) (hinj : Set.InjOn Φ S)
    (hopenmap : ∀ U : Set ℂ, IsOpen U → IsOpen (Φ '' (U ∩ S))) :
    Measurable (Function.invFunOn Φ S) := by
  classical
  refine measurable_of_isOpen fun U hU => ?_
  have hsplit : Function.invFunOn Φ S ⁻¹' U
      = (Φ '' S ∩ Function.invFunOn Φ S ⁻¹' U)
        ∪ ((Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U) := by
    ext b
    by_cases hb : b ∈ Φ '' S <;> simp [hb]
  have hin : Φ '' S ∩ Function.invFunOn Φ S ⁻¹' U = Φ '' (U ∩ S) := by
    ext b
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hbU⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, ha, rfl⟩
      have hmem := Function.invFunOn_mem hex
      have heq := Function.invFunOn_eq hex
      have hval : Function.invFunOn Φ S (Φ a) = a := hinj hmem ha heq
      exact ⟨a, ⟨by rwa [← hval], ha⟩, rfl⟩
    · rintro ⟨a, ⟨haU, haS⟩, rfl⟩
      have hex : ∃ x ∈ S, Φ x = Φ a := ⟨a, haS, rfl⟩
      have hval : Function.invFunOn Φ S (Φ a) = a :=
        hinj (Function.invFunOn_mem hex) haS (Function.invFunOn_eq hex)
      exact ⟨⟨a, haS, rfl⟩, by rw [Set.mem_preimage, hval]; exact haU⟩
  have hconst : ∀ b ∉ Φ '' S, ∀ b' ∉ Φ '' S,
      Function.invFunOn Φ S b = Function.invFunOn Φ S b' := by
    intro b hb b' hb'
    have h1 : ¬∃ x ∈ S, Φ x = b := fun ⟨x, hx, he⟩ => hb ⟨x, hx, he⟩
    have h2 : ¬∃ x ∈ S, Φ x = b' := fun ⟨x, hx, he⟩ => hb' ⟨x, hx, he⟩
    rw [Function.invFunOn_neg h1, Function.invFunOn_neg h2]
  have hout : MeasurableSet ((Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U) := by
    by_cases hex : ∃ b, b ∉ Φ '' S ∧ Function.invFunOn Φ S b ∈ U
    · obtain ⟨b₀, hb₀, hb₀U⟩ := hex
      have : (Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U = (Φ '' S)ᶜ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
          and_iff_left_iff_imp]
        intro hb
        rwa [hconst b hb b₀ hb₀]
      rw [this]
      exact himg.measurableSet.compl
    · push Not at hex
      have : (Φ '' S)ᶜ ∩ Function.invFunOn Φ S ⁻¹' U = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨hb, hbU⟩
        exact hex b hb hbU
      rw [this]
      exact MeasurableSet.empty
  rw [hsplit, hin]
  exact (hopenmap U hU).measurableSet.union hout

/-- Measurability of the inverse of an atlas chart. -/
theorem Atlas.measurable_inv {q : ℂ → ℂ} (A : Atlas q) (j : ℕ) :
    Measurable (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))) := by
  classical
  by_cases hj : A.active j
  · refine invFunOn_measurable Metric.isOpen_ball
      (chart_image_open Metric.isOpen_ball (A.hd j hj) (A.hne j hj) (A.hsq j hj))
      (A.hinj j hj) (fun U hU => ?_)
    have hopen : IsOpen (U ∩ Metric.ball (A.c j) (2 * A.r j)) :=
      hU.inter Metric.isOpen_ball
    have himg := chart_image_open (q := q) hopen
      ((A.hd j hj).mono Set.inter_subset_right)
      (fun w hw => A.hne j hj w hw.2)
      (fun w hw => A.hsq j hj w hw.2)
    exact himg
  · rw [A.hjunk j hj]
    refine invFunOn_measurable Metric.isOpen_ball ?_ ?_ (fun U hU => ?_)
    · rw [Set.image_id]
      exact Metric.isOpen_ball
    · exact Function.injective_id.injOn
    · rw [Set.image_id]
      exact hU.inter Metric.isOpen_ball

open Classical in
/-- A function continuous on an open set and constant outside is measurable. -/
theorem measurable_piecewise_open {f : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hf : ContinuousOn f S) (k : ℂ) :
    Measurable (S.piecewise f fun _ => k) := by
  classical
  refine measurable_of_isOpen fun U hU => ?_
  have hsplit : (S.piecewise f fun _ => k) ⁻¹' U
      = (S ∩ f ⁻¹' U) ∪ (Sᶜ ∩ (if k ∈ U then Set.univ else ∅)) := by
    ext x
    by_cases hx : x ∈ S
    · simp only [Set.mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx, Set.mem_union,
        Set.mem_inter_iff, Set.mem_compl_iff, hx, not_true, false_and, or_false,
        true_and]
    · simp only [Set.mem_preimage, Set.piecewise_eq_of_notMem _ _ _ hx, Set.mem_union,
        Set.mem_inter_iff, hx, false_and, false_or, Set.mem_compl_iff, not_false_iff,
        true_and]
      split_ifs with hk
      · simp [hk]
      · simp [hk]
  rw [hsplit]
  refine (hf.isOpen_inter_preimage hS hU).measurableSet.union
    (hS.measurableSet.compl.inter ?_)
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

open Classical in
/-- The masked atlas chart: the chart on its doubled ball, zero elsewhere and for
inactive indices. -/
noncomputable def Atlas.mchart {q : ℂ → ℂ} (A : Atlas q) (j : ℕ) : ℂ → ℂ :=
  if h : A.active j then
    (Metric.ball (A.c j) (2 * A.r j)).piecewise (A.Φ j) fun _ => 0
  else fun _ => 0

theorem Atlas.measurable_mchart {q : ℂ → ℂ} (A : Atlas q) (j : ℕ) :
    Measurable (A.mchart j) := by
  classical
  rw [Atlas.mchart]
  split_ifs with hj
  · exact measurable_piecewise_open Metric.isOpen_ball
      ((A.hd j hj).continuousOn) 0
  · exact measurable_const

/-- The masked chart agrees with the chart on the doubled ball of an active index. -/
theorem Atlas.mchart_eq {q : ℂ → ℂ} (A : Atlas q) {j : ℕ} (hj : A.active j)
    {z : ℂ} (hz : z ∈ Metric.ball (A.c j) (2 * A.r j)) : A.mchart j z = A.Φ j z := by
  classical
  rw [Atlas.mchart, dif_pos hj, Set.piecewise_eq_of_mem _ _ _ hz]

/-- The chart derivative in the selected chart, as one measurable function. -/
theorem Atlas.measurable_derivSel {q : ℂ → ℂ} (A : Atlas q) :
    Measurable (fun y : ℂ => deriv (A.Φ (A.sel y)) y) := by
  have hG : Measurable (fun jy : ℕ × ℂ => deriv (A.Φ jy.1) jy.2) :=
    measurable_from_prod_countable_right fun j => measurable_deriv (A.Φ j)
  exact hG.comp (A.measurable_sel.prodMk measurable_id)

open Classical in
/-- **One stepper move**: transport by the signed step in the selected chart and update
the sign by the chart-branch derivative ratio at the new position. -/
noncomputable def Atlas.step {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) (p : ℂ × ℝ) :
    ℂ × ℝ :=
  let j := A.sel p.1
  let x' := Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
    (A.mchart j p.1 + ((p.2 * h : ℝ) : ℂ))
  (x', p.2 * ((deriv (A.Φ (A.sel x')) x') * (deriv (A.Φ j) x')⁻¹).re)

/-- Joint measurability of the stepper move. -/
theorem Atlas.measurable_step {q : ℂ → ℂ} (A : Atlas q) (h : ℝ) :
    Measurable (A.step h) := by
  have hX : ∀ j : ℕ, Measurable (fun p : ℂ × ℝ =>
      Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j p.1 + ((p.2 * h : ℝ) : ℂ))) := by
    intro j
    exact (A.measurable_inv j).comp
      (((A.measurable_mchart j).comp measurable_fst).add
        (Complex.measurable_ofReal.comp (measurable_snd.mul_const h)))
  have hcomp : A.step h = (fun jp : ℕ × (ℂ × ℝ) =>
      (Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
          (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ)),
        jp.2.2 * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ)))))
            (Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ))))
          * (deriv (A.Φ jp.1) (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.1 + ((jp.2.2 * h : ℝ) : ℂ))))⁻¹).re))
      ∘ (fun p : ℂ × ℝ => (A.sel p.1, p)) := rfl
  rw [hcomp]
  refine Measurable.comp ?_
    ((A.measurable_sel.comp measurable_fst).prodMk measurable_id)
  refine measurable_from_prod_countable_right fun j => ?_
  refine Measurable.prodMk (hX j) ?_
  refine measurable_snd.mul ?_
  refine (Complex.measurable_re).comp ?_
  exact (A.measurable_derivSel.comp (hX j)).mul
    (((measurable_deriv (A.Φ j)).comp (hX j)).inv)

open Classical in
/-- The stepper move carrying its step size: jointly measurable in size and state. -/
noncomputable def Atlas.step2 {q : ℂ → ℂ} (A : Atlas q)
    (p : ℝ × ℂ × ℝ) : ℝ × ℂ × ℝ :=
  let j := A.sel p.2.1
  let x' := Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
    (A.mchart j p.2.1 + ((p.2.2 * p.1 : ℝ) : ℂ))
  (p.1, x', p.2.2 * ((deriv (A.Φ (A.sel x')) x') * (deriv (A.Φ j) x')⁻¹).re)

/-- Joint measurability of the size-carrying stepper move. -/
theorem Atlas.measurable_step2 {q : ℂ → ℂ} (A : Atlas q) :
    Measurable A.step2 := by
  have hX : ∀ j : ℕ, Measurable (fun p : ℝ × ℂ × ℝ =>
      Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j p.2.1 + ((p.2.2 * p.1 : ℝ) : ℂ))) := by
    intro j
    exact (A.measurable_inv j).comp
      (((A.measurable_mchart j).comp (measurable_fst.comp measurable_snd)).add
        (Complex.measurable_ofReal.comp
          ((measurable_snd.comp measurable_snd).mul measurable_fst)))
  have hcomp : A.step2 = (fun jp : ℕ × (ℝ × ℂ × ℝ) =>
      (jp.2.1, Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
          (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ)),
        jp.2.2.2 * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ)))))
            (Function.invFunOn (A.Φ jp.1) (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ))))
          * (deriv (A.Φ jp.1) (Function.invFunOn (A.Φ jp.1)
            (Metric.ball (A.c jp.1) (2 * A.r jp.1))
            (A.mchart jp.1 jp.2.2.1 + ((jp.2.2.2 * jp.2.1 : ℝ) : ℂ))))⁻¹).re))
      ∘ (fun p : ℝ × ℂ × ℝ => (A.sel p.2.1, p)) := rfl
  rw [hcomp]
  refine Measurable.comp ?_
    ((A.measurable_sel.comp (measurable_fst.comp measurable_snd)).prodMk measurable_id)
  refine measurable_from_prod_countable_right fun j => ?_
  refine Measurable.prodMk measurable_fst (Measurable.prodMk (hX j) ?_)
  refine (measurable_snd.comp measurable_snd).mul ?_
  refine (Complex.measurable_re).comp ?_
  exact (A.measurable_derivSel.comp (hX j)).mul
    (((measurable_deriv (A.Φ j)).comp (hX j)).inv)

/-- The `n`-th stepper approximant of the flow: `n + 1` exact chart steps of size
`t/(n+1)` started with unit sign. -/
noncomputable def Atlas.flowApprox {q : ℂ → ℂ} (A : Atlas q) (n : ℕ)
    (p : ℝ × ℂ) : ℂ :=
  ((A.step2)^[n + 1] (p.1 / (n + 1), p.2, 1)).2.1

theorem Atlas.measurable_flowApprox {q : ℂ → ℂ} (A : Atlas q) (n : ℕ) :
    Measurable (A.flowApprox n) := by
  have h1 : Measurable (fun p : ℝ × ℂ => (p.1 / (n + 1), p.2, (1 : ℝ))) :=
    (measurable_fst.div_const _).prodMk (measurable_snd.prodMk measurable_const)
  exact (measurable_fst.comp measurable_snd).comp
    ((A.measurable_step2.iterate (n + 1)).comp h1)

open Classical in
/-- **The measurable flow candidate**: the stabilized limit of the stepper approximants,
with junk value the start point. -/
noncomputable def Atlas.flow {q : ℂ → ℂ} (A : Atlas q) (t : ℝ) (z : ℂ) : ℂ :=
  if h : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (t, z)) Filter.atTop (nhds L)
  then h.choose else z

/-- Joint measurability of the flow candidate. -/
theorem Atlas.measurable_flow {q : ℂ → ℂ} (A : Atlas q) :
    Measurable (fun p : ℝ × ℂ => A.flow p.1 p.2) := by
  classical
  set E : Set (ℝ × ℂ) := {p | ∃ L, Filter.Tendsto (fun n => A.flowApprox n p)
    Filter.atTop (nhds L)} with hEdef
  have hE : MeasurableSet E :=
    MeasureTheory.measurableSet_exists_tendsto fun n => A.measurable_flowApprox n
  set g : ℕ → ℝ × ℂ → ℂ := fun n => E.piecewise (A.flowApprox n) Prod.snd with hgdef
  have hgmeas : ∀ n, Measurable (g n) := fun n =>
    Measurable.piecewise hE (A.measurable_flowApprox n) measurable_snd
  have hglim : ∀ p : ℝ × ℂ, Filter.Tendsto (fun n => g n p) Filter.atTop
      (nhds (A.flow p.1 p.2)) := by
    intro p
    by_cases hp : p ∈ E
    · have hg' : (fun n => g n p) = fun n => A.flowApprox n p := by
        funext n
        exact Set.piecewise_eq_of_mem _ _ _ hp
      have hp' : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (p.1, p.2))
          Filter.atTop (nhds L) := hp
      rw [hg', Atlas.flow, dif_pos hp']
      exact hp'.choose_spec
    · have hg' : (fun n => g n p) = fun _ => p.2 := by
        funext n
        exact Set.piecewise_eq_of_notMem _ _ _ hp
      have hp' : ¬∃ L, Filter.Tendsto (fun n => A.flowApprox n (p.1, p.2))
          Filter.atTop (nhds L) := hp
      rw [hg', Atlas.flow, dif_neg hp']
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable' Filter.atTop hgmeas
    (tendsto_pi_nhds.mpr hglim)


/-- Points on a vertical trajectory are regular. -/
theorem traj_regular {q : ℂ → ℂ} {σ : ℝ → ℂ} {s : Set ℝ}
    (hσ : IsTrajOn q σ s) {u : ℝ} (hu : u ∈ s) : 0 < (σ u).im ∧ q (σ u) ≠ 0 := by
  obtain ⟨U, -, hpU, hUH, hUne, -, -, -, -, -⟩ := hσ.chart u hu
  exact ⟨hUH hpU, hUne _ hpU⟩

/-- The flat-speed Lipschitz bound on the closed time interval, endpoints included. -/
theorem traj_dist_le_Icc {q : ℂ → ℂ} {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) {m : ℝ} (hm : 0 < m)
    (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u ≤ T) :
    ‖σ u - σ s‖ ≤ Real.sqrt m⁻¹ * (u - s) := by
  rcases eq_or_lt_of_le hsu with heq | hlt
  · rw [← heq]
    simp
  have hσ' : IsTrajOn q σ (Set.Ico 0 T) := traj_mono hσ Set.Ico_subset_Icc_self
  have hbound' : ∀ v ∈ Set.Ico 0 T, m ≤ ‖q (σ v)‖ := fun v hv =>
    hbound v ⟨hv.1, hv.2.le⟩
  set δ : ℝ := (u - s) / 3 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    linarith
  set sn : ℕ → ℝ := fun n => s + δ / (n + 1) with hsndef
  set un : ℕ → ℝ := fun n => u - δ / (n + 1) with hundef
  have hstep : ∀ n : ℕ, ‖σ (un n) - σ (sn n)‖ ≤ Real.sqrt m⁻¹ * (un n - sn n) := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have h1 : 0 < sn n := by
      rw [hsndef]
      simp only
      linarith
    have h2 : sn n ≤ un n := by
      rw [hsndef, hundef]
      simp only
      have : δ / (n + 1) ≤ δ := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
        nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
      rw [hδdef] at this ⊢
      linarith
    have h3 : un n < T := by
      rw [hundef]
      simp only
      linarith
    exact traj_dist_le hσ' hm hbound' h1 h2 h3
  have hsn_mem : ∀ n, sn n ∈ Set.Icc 0 T := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    constructor
    · rw [hsndef]; simp only; linarith
    · rw [hsndef]; simp only; rw [hδdef] at this ⊢; linarith
  have hun_mem : ∀ n, un n ∈ Set.Icc 0 T := by
    intro n
    have hpos : 0 < δ / (n + 1) := by positivity
    have : δ / (n + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
      nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) n]
    constructor
    · rw [hundef]; simp only; rw [hδdef] at this ⊢; linarith
    · rw [hundef]; simp only; linarith
  have htend : Filter.Tendsto (fun n : ℕ => δ / (n + 1)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => δ * (1 / ((n : ℝ) + 1))) Filter.atTop
        (nhds (δ * 0)) := h0.const_mul δ
    simpa [div_eq_mul_inv, mul_zero] using h2
  have hsn_tend : Filter.Tendsto sn Filter.atTop (nhds s) := by
    have := htend.const_add s
    simpa [hsndef] using this
  have hun_tend : Filter.Tendsto un Filter.atTop (nhds u) := by
    have h2 := (htend.const_mul (-1 : ℝ)).const_add u
    have h3 : (fun n : ℕ => u + (-1) * (δ / (n + 1))) = un := by
      funext n
      rw [hundef]
      ring
    rw [h3] at h2
    simpa using h2
  have hσs : Filter.Tendsto (fun n => σ (sn n)) Filter.atTop (nhds (σ s)) := by
    refine (hσ.cont s ⟨hs, le_trans hsu hu⟩).tendsto.comp ?_
    rw [Filter.tendsto_iff_comap, ← Filter.tendsto_iff_comap]
    exact tendsto_nhdsWithin_iff.mpr ⟨hsn_tend, Filter.Eventually.of_forall hsn_mem⟩
  have hσu : Filter.Tendsto (fun n => σ (un n)) Filter.atTop (nhds (σ u)) := by
    refine (hσ.cont u ⟨le_trans hs hsu, hu⟩).tendsto.comp ?_
    rw [Filter.tendsto_iff_comap, ← Filter.tendsto_iff_comap]
    exact tendsto_nhdsWithin_iff.mpr ⟨hun_tend, Filter.Eventually.of_forall hun_mem⟩
  refine le_of_tendsto_of_tendsto' ((hσu.sub hσs).norm) ?_ hstep
  exact (hun_tend.sub hsn_tend).const_mul (Real.sqrt m⁻¹)

/-- A point in an active atlas unit ball bounds the selector from above. -/
theorem sel_le {q : ℂ → ℂ} (A : Atlas q) {z : ℂ} {j : ℕ}
    (hj : A.active j) (hz : z ∈ Metric.ball (A.c j) (A.r j)) : A.sel z ≤ j := by
  classical
  have h : ∃ i, A.active i ∧ z ∈ Metric.ball (A.c i) (A.r i) := ⟨j, hj, hz⟩
  rw [Atlas.sel, dif_pos h]
  exact Nat.find_min' h ⟨hj, hz⟩

/-- The selector is bounded along a compact track of regular points. -/
theorem sel_bound {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσc : ContinuousOn σ (Set.Icc 0 T))
    (hreg : ∀ u ∈ Set.Icc 0 T, 0 < (σ u).im ∧ q (σ u) ≠ 0) :
    ∃ J : ℕ, ∀ u ∈ Set.Icc 0 T, A.sel (σ u) ≤ J := by
  have hloc : ∀ u : Set.Icc (0 : ℝ) T, ∃ V : Set ℝ, IsOpen V ∧ (u : ℝ) ∈ V ∧
      ∀ v ∈ V ∩ Set.Icc 0 T, A.sel (σ v) ≤ A.sel (σ (u : ℝ)) := by
    intro u
    obtain ⟨hact, hmem⟩ := A.sel_spec (hreg u u.2).1 (hreg u u.2).2
    have hpre : σ ⁻¹' Metric.ball (A.c (A.sel (σ u))) (A.r (A.sel (σ u)))
        ∈ nhdsWithin (u : ℝ) (Set.Icc 0 T) :=
      (hσc (u : ℝ) u.2) (Metric.isOpen_ball.mem_nhds hmem)
    obtain ⟨V, hVo, hVmem, hVsub⟩ := mem_nhdsWithin.mp hpre
    exact ⟨V, hVo, hVmem, fun v hv => sel_le A hact (hVsub ⟨hv.1, hv.2⟩)⟩
  choose V hVo hVmem hVsel using hloc
  obtain ⟨F, hF⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).elim_finite_subcover V hVo
    (fun v hv => Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hVmem ⟨v, hv⟩⟩)
  refine ⟨F.sup (fun u => A.sel (σ (u : ℝ))), ?_⟩
  intro v hv
  obtain ⟨u, huF, hvV⟩ := Set.mem_iUnion₂.mp (hF hv)
  have hsup : A.sel (σ (u : ℝ)) ≤ F.sup (fun u => A.sel (σ (u : ℝ))) :=
    Finset.le_sup (f := fun u : Set.Icc (0 : ℝ) T => A.sel (σ (u : ℝ))) huF
  exact le_trans (hVsel u v ⟨hvV, hv⟩) hsup

/-- A uniform positive lower bound on the radii of the first `J` active charts. -/
theorem atlas_radius_min {q : ℂ → ℂ} (A : Atlas q) (J : ℕ) :
    ∃ ρ > 0, ∀ j ≤ J, A.active j → ρ ≤ A.r j := by
  induction J with
  | zero =>
    by_cases h : A.active 0
    · refine ⟨A.r 0, A.hr 0 h, fun j hj hact => ?_⟩
      rw [Nat.le_zero.mp hj]
    · refine ⟨1, one_pos, fun j hj hact => ?_⟩
      rw [Nat.le_zero.mp hj] at hact
      exact absurd hact h
  | succ n ih =>
    obtain ⟨ρ, hρ, hle⟩ := ih
    by_cases h : A.active (n + 1)
    · refine ⟨min ρ (A.r (n + 1)), lt_min hρ (A.hr _ h), fun j hj hact => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · exact le_trans (min_le_left _ _) (hle j (Nat.lt_succ_iff.mp hlt) hact)
      · rw [heq]
        exact min_le_right _ _
    · refine ⟨ρ, hρ, fun j hj hact => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hlt | heq
      · exact hle j (Nat.lt_succ_iff.mp hlt) hact
      · rw [heq] at hact
        exact absurd hact h

/-- The trajectory develops in the chart `Φ` with slope `s` at time `u`. -/
def SlopeAt (Φ : ℂ → ℂ) (σ : ℝ → ℂ) (I : Set ℝ) (u : ℝ) (s : ℝ) : Prop :=
  ∀ᶠ v in nhdsWithin u I, Φ (σ v) = Φ (σ u) + s * ((v - u : ℝ) : ℂ)

/-- **Forward pinning**: an affine identity on a nondegenerate forward interval forces
its slope to agree with the germ slope. -/
theorem slope_pin_forward {Φ : ℂ → ℂ} {σ : ℝ → ℂ} {T u u' s ε : ℝ}
    (hsub : Set.Icc u u' ⊆ Set.Icc 0 T) (huu' : u < u')
    (hslope : SlopeAt Φ σ (Set.Icc 0 T) u s)
    (haff : ∀ v ∈ Set.Icc u u', Φ (σ v) = Φ (σ u) + ε * ((v - u : ℝ) : ℂ)) :
    ε = s := by
  haveI hne : (nhdsWithin u (Set.Ioc u u')).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioc huu'.ne]
    exact ⟨le_refl u, huu'.le⟩
  have hmono : nhdsWithin u (Set.Ioc u u') ≤ nhdsWithin u (Set.Icc 0 T) :=
    nhdsWithin_mono u (fun v hv => hsub ⟨hv.1.le, hv.2⟩)
  obtain ⟨v, hv, e₁⟩ := (eventually_mem_nhdsWithin.and
    (hslope.filter_mono hmono)).exists
  have e₂ := haff v ⟨hv.1.le, hv.2⟩
  have hvne : ((v - u : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hv.1))
  have hmul : (ε : ℂ) * ((v - u : ℝ) : ℂ) = s * ((v - u : ℝ) : ℂ) := by
    rw [e₁] at e₂
    linear_combination -e₂
  exact_mod_cast mul_right_cancel₀ hvne hmul

/-- **Slope transport to the segment endpoint**: an affine development on `[u, u']`
extends to a two-sided germ of the same slope at `u'`. -/
theorem slope_transport {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {T : ℝ} (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {u u' s : ℝ} (hu0 : 0 ≤ u) (huu' : u < u') (hu'T : u' ≤ T)
    (hxS : σ u' ∈ S)
    (haff : ∀ v ∈ Set.Icc u u', Φ (σ v) = Φ (σ u) + s * ((v - u : ℝ) : ℂ)) :
    SlopeAt Φ σ (Set.Icc 0 T) u' s := by
  have hu'mem : u' ∈ Set.Icc 0 T := ⟨le_trans hu0 huu'.le, hu'T⟩
  obtain ⟨ε, hε, hgerm⟩ := traj_ambient_local hS hΦd hΦsq hσ
    (Set.Subset.refl _) hu'mem hxS
  haveI hne : (nhdsWithin u' (Set.Ico u u')).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ico huu'.ne]
    exact ⟨huu'.le, le_refl u'⟩
  have hmono : nhdsWithin u' (Set.Ico u u') ≤ nhdsWithin u' (Set.Icc 0 T) :=
    nhdsWithin_mono u' (fun v hv => ⟨le_trans hu0 hv.1, le_trans hv.2.le hu'T⟩)
  obtain ⟨v, hv, e₁⟩ := (eventually_mem_nhdsWithin.and
    (hgerm.filter_mono hmono)).exists
  have e₂ := haff v ⟨hv.1, hv.2.le⟩
  have e₃ := haff u' (Set.right_mem_Icc.mpr huu'.le)
  have hvne : ((v - u' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt hv.2))
  have hεs : (ε : ℂ) = (s : ℂ) := by
    have hmul : (ε : ℂ) * ((v - u' : ℝ) : ℂ) = s * ((v - u' : ℝ) : ℂ) := by
      rw [e₂, e₃] at e₁
      push_cast at e₁ ⊢
      linear_combination -e₁
    exact mul_right_cancel₀ hvne hmul
  have hεs' : ε = s := by exact_mod_cast hεs
  rw [← hεs']
  exact hgerm

/-- **Chart change of the slope**: through an affine branch relation the slope
multiplies by the branch sign. -/
theorem slope_ratio {Φ₁ Φ₂ : ℂ → ℂ} {Ω : Set ℂ} (hΩo : IsOpen Ω)
    {σ : ℝ → ℂ} {T u s ε : ℝ} {k : ℂ} (hu : u ∈ Set.Icc 0 T)
    (hcont : ContinuousWithinAt σ (Set.Icc 0 T) u) (hxΩ : σ u ∈ Ω)
    (hrel : ∀ z ∈ Ω, Φ₂ z = (ε : ℂ) * Φ₁ z + k)
    (hslope : SlopeAt Φ₁ σ (Set.Icc 0 T) u s) :
    SlopeAt Φ₂ σ (Set.Icc 0 T) u (ε * s) := by
  have hev : ∀ᶠ v in nhdsWithin u (Set.Icc 0 T), σ v ∈ Ω :=
    hcont (hΩo.mem_nhds hxΩ)
  filter_upwards [hslope, hev] with v hv hvΩ
  rw [hrel _ hvΩ, hrel _ hxΩ, hv]
  push_cast
  ring

/-- **The stepper move lands on the trajectory**: within the margin threshold, the
selected chart contains the coming segment, the development is affine with the germ
slope, and the chart inverse of the stepped development is the trajectory point. -/
theorem step_position {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ)
    {u : ℝ} (hu0 : 0 ≤ u) (huh : u + h ≤ T) {sgn : ℝ}
    (hslope : SlopeAt (A.Φ (A.sel (σ u))) σ (Set.Icc 0 T) u sgn) :
    (∀ v ∈ Set.Icc u (u + h), σ v ∈ Metric.ball (A.c (A.sel (σ u)))
      (2 * A.r (A.sel (σ u)))) ∧
    (∀ v ∈ Set.Icc u (u + h), A.Φ (A.sel (σ u)) (σ v)
      = A.Φ (A.sel (σ u)) (σ u) + sgn * ((v - u : ℝ) : ℂ)) ∧
    Function.invFunOn (A.Φ (A.sel (σ u)))
      (Metric.ball (A.c (A.sel (σ u))) (2 * A.r (A.sel (σ u))))
      (A.mchart (A.sel (σ u)) (σ u) + ((sgn * h : ℝ) : ℂ)) = σ (u + h) := by
  have humem : u ∈ Set.Icc 0 T := ⟨hu0, by linarith⟩
  obtain ⟨him, hq0⟩ := traj_regular hσ humem
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  set j : ℕ := A.sel (σ u) with hjdef
  have hsubI : Set.Icc u (u + h) ⊆ Set.Icc 0 T := fun v hv =>
    ⟨le_trans hu0 hv.1, le_trans hv.2 huh⟩
  have htrack : ∀ v ∈ Set.Icc u (u + h), σ v ∈ Metric.ball (A.c j) (2 * A.r j) := by
    intro v hv
    have hd1 : ‖σ v - σ u‖ ≤ Real.sqrt m⁻¹ * (v - u) :=
      traj_dist_le_Icc hσ hm hbound hu0 hv.1 (le_trans hv.2 huh)
    have hd2 : Real.sqrt m⁻¹ * (v - u) ≤ Real.sqrt m⁻¹ * h := by
      have := hv.2
      have hM : 0 ≤ Real.sqrt m⁻¹ := Real.sqrt_nonneg _
      nlinarith [hv.1]
    have hd3 : ‖σ v - σ u‖ < ρ := lt_of_le_of_lt (le_trans hd1 hd2) hsmall
    have hd4 : ρ ≤ A.r j := hrad u humem
    rw [Metric.mem_ball] at hmem ⊢
    calc dist (σ v) (A.c j) ≤ dist (σ v) (σ u) + dist (σ u) (A.c j) :=
          dist_triangle _ _ _
      _ < A.r j + A.r j := by
          rw [dist_eq_norm]
          exact add_lt_add (lt_of_lt_of_le hd3 hd4) hmem
      _ = 2 * A.r j := by ring
  obtain ⟨ε₀, hε₀, haff₀⟩ := traj_ambient_affine Metric.isOpen_ball (A.hd j hact)
    (A.hsq j hact) hσ (by linarith : u ≤ u + h) hsubI htrack
  have hε₀sgn : ε₀ = sgn :=
    slope_pin_forward hsubI (by linarith) hslope haff₀
  have haff : ∀ v ∈ Set.Icc u (u + h), A.Φ j (σ v)
      = A.Φ j (σ u) + sgn * ((v - u : ℝ) : ℂ) := by
    intro v hv
    rw [← hε₀sgn]
    exact haff₀ v hv
  refine ⟨htrack, haff, ?_⟩
  have hmem2 : σ u ∈ Metric.ball (A.c j) (2 * A.r j) :=
    Metric.ball_subset_ball (by linarith [A.hr j hact]) hmem
  have htarget : A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ)
      = A.Φ j (σ (u + h)) := by
    rw [A.mchart_eq hact hmem2, haff (u + h) (Set.right_mem_Icc.mpr (by linarith))]
    push_cast
    ring
  rw [htarget]
  have hex : ∃ a ∈ Metric.ball (A.c j) (2 * A.r j), A.Φ j a = A.Φ j (σ (u + h)) :=
    ⟨σ (u + h), htrack (u + h) (Set.right_mem_Icc.mpr (by linarith)), rfl⟩
  exact (A.hinj j hact) (Function.invFunOn_mem hex)
    (htrack (u + h) (Set.right_mem_Icc.mpr (by linarith)))
    (Function.invFunOn_eq hex)

/-- **One stepper move follows the trajectory** and carries the slope into the newly
selected chart. -/
theorem step_follows {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ)
    {u : ℝ} (hu0 : 0 ≤ u) (huh : u + h ≤ T) {sgn : ℝ}
    (hslope : SlopeAt (A.Φ (A.sel (σ u))) σ (Set.Icc 0 T) u sgn) :
    (A.step2 (h, σ u, sgn)).1 = h ∧
    (A.step2 (h, σ u, sgn)).2.1 = σ (u + h) ∧
    SlopeAt (A.Φ (A.sel (σ (u + h)))) σ (Set.Icc 0 T) (u + h)
      ((A.step2 (h, σ u, sgn)).2.2) := by
  obtain ⟨htrack, haff, hinv⟩ := step_position A hσ hm hbound hrad hh0 hsmall
    hu0 huh hslope
  set j : ℕ := A.sel (σ u) with hjdef
  have humem : u ∈ Set.Icc 0 T := ⟨hu0, by linarith⟩
  have huhmem : u + h ∈ Set.Icc 0 T := ⟨by linarith, huh⟩
  obtain ⟨him, hq0⟩ := traj_regular hσ humem
  obtain ⟨him', hq0'⟩ := traj_regular hσ huhmem
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  obtain ⟨hact', hmem'⟩ := A.sel_spec him' hq0'
  set j' : ℕ := A.sel (σ (u + h)) with hj'def
  have hx'S₁ : σ (u + h) ∈ Metric.ball (A.c j) (2 * A.r j) :=
    htrack (u + h) (Set.right_mem_Icc.mpr (by linarith))
  have hx'S₂ : σ (u + h) ∈ Metric.ball (A.c j') (2 * A.r j') :=
    Metric.ball_subset_ball (by linarith [A.hr j' hact']) hmem'
  have h21 : (A.step2 (h, σ u, sgn)).2.1 = σ (u + h) := hinv
  have h22 : (A.step2 (h, σ u, sgn)).2.2
      = sgn * ((deriv (A.Φ j') (σ (u + h)))
        * (deriv (A.Φ j) (σ (u + h)))⁻¹).re := by
    show sgn * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ)))))
        (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ))))
      * (deriv (A.Φ j) (Function.invFunOn (A.Φ j)
        (Metric.ball (A.c j) (2 * A.r j))
        (A.mchart j (σ u) + ((sgn * h : ℝ) : ℂ))))⁻¹).re = _
    rw [hinv]
  obtain ⟨ε', hε', hderiv', hrel'⟩ := chart_ratio (q := q) Metric.isOpen_ball
    Metric.isOpen_ball (A.hd j hact) (A.hd j' hact') (A.hsq j hact) (A.hsq j' hact')
    hx'S₁ hx'S₂
  have hd : deriv (A.Φ j) (σ (u + h)) ≠ 0 := by
    intro h0
    apply hq0'
    have hsq := A.hsq j hact _ hx'S₁
    rw [h0] at hsq
    simpa using hsq.symm
  have hratio : ((deriv (A.Φ j') (σ (u + h)))
      * (deriv (A.Φ j) (σ (u + h)))⁻¹).re = ε' := by
    rw [hderiv', mul_assoc, mul_inv_cancel₀ hd, mul_one, Complex.ofReal_re]
  have hslope₁ : SlopeAt (A.Φ j) σ (Set.Icc 0 T) (u + h) sgn :=
    slope_transport Metric.isOpen_ball (A.hd j hact) (A.hsq j hact) hσ hu0
      (by linarith) huh hx'S₁ haff
  have hslope₂ : SlopeAt (A.Φ j') σ (Set.Icc 0 T) (u + h) (ε' * sgn) :=
    slope_ratio ((Metric.isOpen_ball.inter Metric.isOpen_ball).connectedComponentIn)
      huhmem (hσ.cont _ huhmem) (mem_connectedComponentIn ⟨hx'S₁, hx'S₂⟩)
      hrel' hslope₁
  refine ⟨rfl, h21, ?_⟩
  rw [h22, hratio, mul_comm sgn ε']
  exact hslope₂

/-- **The stepper follows the trajectory for all steps** below the margin threshold. -/
theorem stepper_follows {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ)
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 T) 0 1) :
    ∀ k : ℕ, (k : ℝ) * h ≤ T →
      ((A.step2)^[k] (h, σ 0, 1)).1 = h ∧
      ((A.step2)^[k] (h, σ 0, 1)).2.1 = σ ((k : ℝ) * h) ∧
      SlopeAt (A.Φ (A.sel (σ ((k : ℝ) * h)))) σ (Set.Icc 0 T) ((k : ℝ) * h)
        (((A.step2)^[k] (h, σ 0, 1)).2.2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · show σ 0 = σ ((0 : ℕ) * h)
      norm_num
    · show SlopeAt (A.Φ (A.sel (σ ((0 : ℕ) * h)))) σ (Set.Icc 0 T)
        ((0 : ℕ) * h) (1 : ℝ)
      norm_num
      exact hslope0
  | succ k ih =>
    intro hkT
    have hkh : (k : ℝ) * h ≤ T := by
      push_cast at hkT
      nlinarith [hh0.le, Nat.cast_nonneg (α := ℝ) k]
    have hk0 : 0 ≤ (k : ℝ) * h := by positivity
    have hkh1 : (k : ℝ) * h + h ≤ T := by
      push_cast at hkT
      linarith
    obtain ⟨ih1, ih2, ih3⟩ := ih hkh
    have hstate : (A.step2)^[k] (h, σ 0, 1)
        = (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, 1)).2.2) := by
      refine Prod.ext ih1 (Prod.ext ih2 rfl)
    obtain ⟨hs1, hs2, hs3⟩ := step_follows A hσ hm hbound hrad hh0 hsmall
      hk0 hkh1 ih3
    have hiter : (A.step2)^[k + 1] (h, σ 0, 1)
        = A.step2 (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, 1)).2.2) := by
      rw [Function.iterate_succ_apply', hstate]
    have hcast : ((k : ℝ) + 1) * h = (k : ℝ) * h + h := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hiter]
      exact hs1
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs2
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs3

/-- **Stepper stabilization**: for a trajectory with unit initial chart slope, the
stepper approximants eventually equal the trajectory endpoint. -/
theorem flowApprox_eq {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (A : Atlas q) {σ : ℝ → ℂ} {t : ℝ} (ht : 0 < t)
    (hσ : IsTrajOn q σ (Set.Icc 0 t))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 t) 0 1) :
    ∃ N : ℕ, ∀ n ≥ N, A.flowApprox n (t, σ 0) = σ t := by
  have hreg : ∀ v ∈ Set.Icc 0 t, 0 < (σ v).im ∧ q (σ v) ≠ 0 := fun v hv =>
    traj_regular hσ hv
  have hqcont : ContinuousOn (fun v => ‖q (σ v)‖) (Set.Icc 0 t) := by
    refine ContinuousOn.norm (hq.continuousOn.comp hσ.cont ?_)
    exact fun v hv => (hreg v hv).1
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr ht.le⟩ hqcont
  set m : ℝ := ‖q (σ v₀)‖ with hmdef
  have hm : 0 < m := norm_pos_iff.mpr (hreg v₀ hv₀mem).2
  have hbound : ∀ v ∈ Set.Icc 0 t, m ≤ ‖q (σ v)‖ := fun v hv => hv₀min hv
  obtain ⟨J, hJ⟩ := sel_bound A hσ.cont hreg
  obtain ⟨ρ, hρ, hρle⟩ := atlas_radius_min A J
  have hrad : ∀ v ∈ Set.Icc 0 t, ρ ≤ A.r (A.sel (σ v)) := by
    intro v hv
    exact hρle _ (hJ v hv) (A.sel_spec (hreg v hv).1 (hreg v hv).2).1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt m⁻¹ * t / ρ)
  refine ⟨N, fun n hn => ?_⟩
  set h : ℝ := t / (n + 1) with hhdef
  have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by
    rw [hhdef]
    positivity
  have hsmall : Real.sqrt m⁻¹ * h < ρ := by
    have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : Real.sqrt m⁻¹ * t / ρ < (n : ℝ) + 1 := by linarith
    have h2 : Real.sqrt m⁻¹ * t < ρ * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hρ] at h1
      linarith
    rw [hhdef, ← mul_div_assoc, div_lt_iff₀ hnn]
    linarith
  have hth : ((n + 1 : ℕ) : ℝ) * h = t := by
    rw [hhdef]
    push_cast
    field_simp
  obtain ⟨-, hpos, -⟩ := stepper_follows A hσ hm hbound hrad hh0 hsmall hslope0
    (n + 1) (le_of_eq hth)
  rw [hth] at hpos
  exact hpos

/-- **The measurable flow candidate follows the trajectory**: at a positive time with a
trajectory of unit initial chart slope, the flow equals the trajectory endpoint. -/
theorem flow_eq_traj {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (A : Atlas q) {σ : ℝ → ℂ} {t : ℝ} (ht : 0 < t)
    (hσ : IsTrajOn q σ (Set.Icc 0 t))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 t) 0 1) :
    A.flow t (σ 0) = σ t := by
  classical
  obtain ⟨N, hN⟩ := flowApprox_eq hq A ht hσ hslope0
  have hconv : Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds (σ t)) := by
    refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
    exact fun n hn => hN n hn
  have hex : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds L) := ⟨σ t, hconv⟩
  rw [Atlas.flow, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hconv


/-- The stepper move conjugated by simultaneous time-and-sign reversal. -/
theorem step2_neg {q : ℂ → ℂ} (A : Atlas q) (p : ℝ × ℂ × ℝ) :
    A.step2 (-p.1, p.2.1, -p.2.2)
      = (-(A.step2 p).1, (A.step2 p).2.1, -(A.step2 p).2.2) := by
  have harg : ((-p.2.2 * -p.1 : ℝ) : ℂ) = ((p.2.2 * p.1 : ℝ) : ℂ) := by
    push_cast
    ring
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ))
      = Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((p.2.2 * p.1 : ℝ) : ℂ))
    rw [harg]
  · show (-p.2.2) * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ)))))
        (Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ))))
      * (deriv (A.Φ (A.sel p.2.1)) (Function.invFunOn (A.Φ (A.sel p.2.1))
        (Metric.ball (A.c (A.sel p.2.1)) (2 * A.r (A.sel p.2.1)))
        (A.mchart (A.sel p.2.1) p.2.1 + ((-p.2.2 * -p.1 : ℝ) : ℂ))))⁻¹).re = _
    rw [harg, neg_mul]
    rfl

/-- The stepper iterate conjugated by time-and-sign reversal. -/
theorem step2_iterate_neg {q : ℂ → ℂ} (A : Atlas q) (k : ℕ) :
    ∀ p : ℝ × ℂ × ℝ, (A.step2)^[k] (-p.1, p.2.1, -p.2.2)
      = (-((A.step2)^[k] p).1, ((A.step2)^[k] p).2.1, -((A.step2)^[k] p).2.2) := by
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step2_neg,
      ih (A.step2 p)]

/-- The stepper follows the trajectory for any initial chart slope. -/
theorem stepper_follows_gen {q : ℂ → ℂ} (A : Atlas q) {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    {m : ℝ} (hm : 0 < m) (hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖)
    {ρ : ℝ} (hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)))
    {h : ℝ} (hh0 : 0 < h) (hsmall : Real.sqrt m⁻¹ * h < ρ) {s₀ : ℝ}
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 T) 0 s₀) :
    ∀ k : ℕ, (k : ℝ) * h ≤ T →
      ((A.step2)^[k] (h, σ 0, s₀)).1 = h ∧
      ((A.step2)^[k] (h, σ 0, s₀)).2.1 = σ ((k : ℝ) * h) ∧
      SlopeAt (A.Φ (A.sel (σ ((k : ℝ) * h)))) σ (Set.Icc 0 T) ((k : ℝ) * h)
        (((A.step2)^[k] (h, σ 0, s₀)).2.2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · show σ 0 = σ ((0 : ℕ) * h)
      norm_num
    · show SlopeAt (A.Φ (A.sel (σ ((0 : ℕ) * h)))) σ (Set.Icc 0 T) ((0 : ℕ) * h) s₀
      norm_num
      exact hslope0
  | succ k ih =>
    intro hkT
    have hkh : (k : ℝ) * h ≤ T := by
      push_cast at hkT
      nlinarith [hh0.le, Nat.cast_nonneg (α := ℝ) k]
    have hk0 : 0 ≤ (k : ℝ) * h := by positivity
    have hkh1 : (k : ℝ) * h + h ≤ T := by
      push_cast at hkT
      linarith
    obtain ⟨ih1, ih2, ih3⟩ := ih hkh
    have hstate : (A.step2)^[k] (h, σ 0, s₀)
        = (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, s₀)).2.2) :=
      Prod.ext ih1 (Prod.ext ih2 rfl)
    obtain ⟨hs1, hs2, hs3⟩ := step_follows A hσ hm hbound hrad hh0 hsmall
      hk0 hkh1 ih3
    have hiter : (A.step2)^[k + 1] (h, σ 0, s₀)
        = A.step2 (h, σ ((k : ℝ) * h), ((A.step2)^[k] (h, σ 0, s₀)).2.2) := by
      rw [Function.iterate_succ_apply', hstate]
    have hcast : ((k : ℝ) + 1) * h = (k : ℝ) * h + h := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hiter]
      exact hs1
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs2
    · rw [hiter]
      push_cast
      rw [hcast]
      exact hs3

/-- **Negative-time stabilization**: for a backward trajectory with slope `−1` in its
initial chart the stepper approximants at negative time eventually equal its endpoint. -/
theorem flowApprox_eq_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {σ : ℝ → ℂ} {t : ℝ} (ht : t < 0) (hσ : IsTrajOn q σ (Set.Icc 0 (-t)))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (-t)) 0 (-1)) :
    ∃ N : ℕ, ∀ n ≥ N, A.flowApprox n (t, σ 0) = σ (-t) := by
  have ht' : 0 < -t := by linarith
  have hreg : ∀ v ∈ Set.Icc 0 (-t), 0 < (σ v).im ∧ q (σ v) ≠ 0 := fun v hv =>
    traj_regular hσ hv
  have hqcont : ContinuousOn (fun v => ‖q (σ v)‖) (Set.Icc 0 (-t)) := by
    refine ContinuousOn.norm (hq.continuousOn.comp hσ.cont ?_)
    exact fun v hv => (hreg v hv).1
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr ht'.le⟩ hqcont
  set m : ℝ := ‖q (σ v₀)‖ with hmdef
  have hm : 0 < m := norm_pos_iff.mpr (hreg v₀ hv₀mem).2
  have hbound : ∀ v ∈ Set.Icc 0 (-t), m ≤ ‖q (σ v)‖ := fun v hv => hv₀min hv
  obtain ⟨J, hJ⟩ := sel_bound A hσ.cont hreg
  obtain ⟨ρ, hρ, hρle⟩ := atlas_radius_min A J
  have hrad : ∀ v ∈ Set.Icc 0 (-t), ρ ≤ A.r (A.sel (σ v)) := fun v hv =>
    hρle _ (hJ v hv) (A.sel_spec (hreg v hv).1 (hreg v hv).2).1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt m⁻¹ * (-t) / ρ)
  refine ⟨N, fun n hn => ?_⟩
  set ĥ : ℝ := -t / (n + 1) with hhdef
  have hnn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < ĥ := by
    rw [hhdef]
    positivity
  have hsmall : Real.sqrt m⁻¹ * ĥ < ρ := by
    have hle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : Real.sqrt m⁻¹ * (-t) / ρ < (n : ℝ) + 1 := by linarith
    have h2 : Real.sqrt m⁻¹ * (-t) < ρ * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hρ] at h1
      linarith
    rw [hhdef, ← mul_div_assoc, div_lt_iff₀ hnn]
    linarith
  have hth : ((n + 1 : ℕ) : ℝ) * ĥ = -t := by
    rw [hhdef]
    push_cast
    field_simp
  obtain ⟨-, hpos, -⟩ := stepper_follows_gen A hσ hm hbound hrad hh0 hsmall
    hslope0 (n + 1) (le_of_eq hth)
  rw [hth] at hpos
  have hneg : (t / ((n : ℝ) + 1), σ 0, (1 : ℝ)) = (-ĥ, σ 0, -(-1 : ℝ)) := by
    rw [hhdef]
    refine Prod.ext (by ring) (Prod.ext rfl (by norm_num))
  calc A.flowApprox n (t, σ 0)
      = ((A.step2)^[n + 1] (t / ((n : ℝ) + 1), σ 0, (1 : ℝ))).2.1 := rfl
    _ = ((A.step2)^[n + 1] (-ĥ, σ 0, -(-1 : ℝ))).2.1 := by rw [hneg]
    _ = ((A.step2)^[n + 1] (ĥ, σ 0, (-1 : ℝ))).2.1 := by
        rw [show ((-ĥ : ℝ), σ 0, -(-1 : ℝ))
          = (-(ĥ, σ 0, (-1 : ℝ)).1, (ĥ, σ 0, (-1 : ℝ)).2.1,
            -(ĥ, σ 0, (-1 : ℝ)).2.2) from rfl,
          step2_iterate_neg A (n + 1) (ĥ, σ 0, (-1 : ℝ))]
    _ = σ (-t) := hpos

/-- The measurable flow follows the backward trajectory at negative times. -/
theorem flow_eq_traj_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {σ : ℝ → ℂ} {t : ℝ} (ht : t < 0) (hσ : IsTrajOn q σ (Set.Icc 0 (-t)))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (-t)) 0 (-1)) :
    A.flow t (σ 0) = σ (-t) := by
  classical
  obtain ⟨N, hN⟩ := flowApprox_eq_neg hq A ht hσ hslope0
  have hconv : Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds (σ (-t))) := by
    refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
    exact fun n hn => hN n hn
  have hex : ∃ L, Filter.Tendsto (fun n => A.flowApprox n (t, σ 0)) Filter.atTop
      (nhds L) := ⟨σ (-t), hconv⟩
  rw [Atlas.flow, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hconv

/-- The **two-sided regular set**: points with coherently oriented vertical trajectories
of both orientations for every time horizon, in the stepper's initial chart. -/
def good (q : ℂ → ℂ) (A : Atlas q) : Set ℂ :=
  {z | 0 < z.im ∧ q z ≠ 0 ∧
    (∀ T, 0 < T → ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1) ∧
    (∀ T, 0 < T → ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 (-1))}

/-- On the two-sided regular set the flow at positive times is realized by a coherently
oriented trajectory. -/
theorem flow_follows_pos {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 ∧ A.flow t z = σ t := by
  obtain ⟨σ, hz0, hσ, hslope⟩ := hz.2.2.1 t ht
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  have hslope' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 t) 0 1 := by
    rw [hz0]
    exact hslope
  rw [← hz0]
  exact flow_eq_traj hq A ht hσ hslope'

/-- On the two-sided regular set the flow at negative times is realized by a reversely
oriented trajectory. -/
theorem flow_follows_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : t < 0) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (-t)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (-t)) 0 (-1) ∧ A.flow t z = σ (-t) := by
  obtain ⟨σ, hz0, hσ, hslope⟩ := hz.2.2.2 (-t) (by linarith)
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  have hslope' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (-t)) 0 (-1) := by
    rw [hz0]
    exact hslope
  rw [← hz0]
  exact flow_eq_traj_neg hq A ht hσ hslope'

/-- The stepper move fixes regular points at step size zero. -/
theorem step2_zero {q : ℂ → ℂ} (A : Atlas q) {z : ℂ} (hz : 0 < z.im)
    (hq0 : q z ≠ 0) (s : ℝ) : A.step2 (0, z, s) = (0, z, s) := by
  obtain ⟨hact, hmem⟩ := A.sel_spec hz hq0
  set j : ℕ := A.sel z with hjdef
  have hmem2 : z ∈ Metric.ball (A.c j) (2 * A.r j) :=
    Metric.ball_subset_ball (by linarith [A.hr j hact]) hmem
  have harg : A.mchart j z + ((s * 0 : ℝ) : ℂ) = A.Φ j z := by
    rw [A.mchart_eq hact hmem2]
    push_cast
    ring
  have hex : ∃ a ∈ Metric.ball (A.c j) (2 * A.r j), A.Φ j a = A.Φ j z :=
    ⟨z, hmem2, rfl⟩
  have hinv : Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
      (A.mchart j z + ((s * 0 : ℝ) : ℂ)) = z := by
    rw [harg]
    exact (A.hinj j hact) (Function.invFunOn_mem hex) hmem2 (Function.invFunOn_eq hex)
  have hd : deriv (A.Φ j) z ≠ 0 := by
    intro h0
    apply hq0
    have hsq := A.hsq j hact z hmem2
    rw [h0] at hsq
    simpa using hsq.symm
  refine Prod.ext rfl (Prod.ext hinv ?_)
  show s * ((deriv (A.Φ (A.sel (Function.invFunOn (A.Φ j)
      (Metric.ball (A.c j) (2 * A.r j)) (A.mchart j z + ((s * 0 : ℝ) : ℂ)))))
      (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
      (A.mchart j z + ((s * 0 : ℝ) : ℂ))))
    * (deriv (A.Φ j) (Function.invFunOn (A.Φ j) (Metric.ball (A.c j) (2 * A.r j))
      (A.mchart j z + ((s * 0 : ℝ) : ℂ))))⁻¹).re = s
  rw [hinv, mul_inv_cancel₀ hd, Complex.one_re, mul_one]

/-- The flow fixes regular points at time zero. -/
theorem flow_zero {q : ℂ → ℂ} (A : Atlas q) {z : ℂ} (hz : 0 < z.im)
    (hq0 : q z ≠ 0) : A.flow 0 z = z := by
  classical
  have happrox : ∀ n : ℕ, A.flowApprox n ((0 : ℝ), z) = z := by
    intro n
    have hstep : ∀ k : ℕ, (A.step2)^[k] ((0 : ℝ) / (n + 1), z, 1)
        = ((0 : ℝ) / (n + 1), z, (1 : ℝ)) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih,
          show ((0 : ℝ) / (n + 1), z, (1 : ℝ)) = ((0 : ℝ), z, (1 : ℝ)) by norm_num,
          step2_zero A hz hq0 1]
    show ((A.step2)^[n + 1] ((0 : ℝ) / (n + 1), z, 1)).2.1 = z
    rw [hstep (n + 1)]
  have hconv : Filter.Tendsto (fun n => A.flowApprox n ((0 : ℝ), z)) Filter.atTop
      (nhds z) := by
    refine tendsto_atTop_of_eventually_const (i₀ := 0) ?_
    exact fun n _ => happrox n
  have hex : ∃ L, Filter.Tendsto (fun n => A.flowApprox n ((0 : ℝ), z)) Filter.atTop
      (nhds L) := ⟨z, hconv⟩
  rw [Atlas.flow, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec hconv

/-- **Flow evaluation along the whole forward window**: on the two-sided regular set the
flow restricted to `[0, t]` is a coherently oriented trajectory. -/
theorem flow_traj_eval_pos {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 ∧
      ∀ u ∈ Set.Icc 0 t, A.flow u z = σ u := by
  obtain ⟨σ, hz0, hσ, hslope, -⟩ := flow_follows_pos hq A hz ht
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, flow_zero A hz.1 hz.2.1, hz0]
  · have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
      traj_mono hσ (Set.Icc_subset_Icc le_rfl hu.2)
    have hslopeu : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 u) 0 1 := by
      rw [hz0]
      have h := hslope
      rw [SlopeAt] at h ⊢
      exact h.filter_mono (nhdsWithin_mono 0 (Set.Icc_subset_Icc le_rfl hu.2))
    rw [← hz0]
    exact flow_eq_traj hq A h0 hσu hslopeu

/-- **Flow evaluation along the whole backward window**: on the two-sided regular set
the flow at negative times is the reversely oriented trajectory. -/
theorem flow_traj_eval_neg {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {t : ℝ} (ht : 0 < t) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 t) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 (-1) ∧
      ∀ u ∈ Set.Icc 0 t, A.flow (-u) z = σ u := by
  obtain ⟨σ, hz0, hσ, hslope, -⟩ := flow_follows_neg hq A hz
    (show -t < 0 by linarith)
  rw [neg_neg] at hσ hslope
  refine ⟨σ, hz0, hσ, hslope, ?_⟩
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · rw [← h0, neg_zero, flow_zero A hz.1 hz.2.1, hz0]
  · have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
      traj_mono hσ (Set.Icc_subset_Icc le_rfl hu.2)
    have hslopeu : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 u) 0 (-1) := by
      rw [hz0]
      have h := hslope
      rw [SlopeAt] at h ⊢
      exact h.filter_mono (nhdsWithin_mono 0 (Set.Icc_subset_Icc le_rfl hu.2))
    have hnu : -u < 0 := by linarith
    have hσu' : IsTrajOn q σ (Set.Icc 0 (- -u)) := by
      rw [neg_neg]
      exact hσu
    have hslopeu' : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 (- -u)) 0 (-1) := by
      rw [neg_neg]
      exact hslopeu
    have := flow_eq_traj_neg hq A hnu hσu' hslopeu'
    rw [neg_neg] at this
    rw [← hz0]
    exact this


/-- The imaginary part transforms by the reciprocal square denominator norm. -/
theorem moebiusMap_im (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : 0 < z.im) : (moebiusMap γ z).im = z.im / ‖moebiusDenom γ z‖ ^ 2 := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hns : Complex.normSq (moebiusDenom γ z) = ‖moebiusDenom γ z‖ ^ 2 :=
    Complex.normSq_eq_norm_sq _
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  rw [moebiusMap, Complex.div_im, hns]
  have hNim : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)).im
      = (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.im := by
    simp [Complex.add_im, Complex.mul_im]
  have hNre : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)).re
      = (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.re
        + (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    simp [Complex.add_re, Complex.mul_re]
  have hDim : (moebiusDenom γ z).im = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * z.im := by
    simp [moebiusDenom, Complex.add_im, Complex.mul_im]
  have hDre : (moebiusDenom γ z).re
      = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * z.re
        + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    simp [moebiusDenom, Complex.add_re, Complex.mul_re]
  rw [hNim, hNre, hDim, hDre]
  have hpos : (0 : ℝ) < ‖moebiusDenom γ z‖ ^ 2 := by
    have := norm_pos_iff.mpr hd
    positivity
  field_simp
  ring_nf
  nlinarith [hdet, sq_nonneg z.im]

/-- The flat-to-hyperbolic density ratio `√‖q‖ · im` is `Γ`-invariant. -/
theorem ratio_invariant {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt ‖q (moebiusMap γ z)‖ * (moebiusMap γ z).im
      = Real.sqrt ‖q z‖ * z.im := by
  have hd : moebiusDenom γ z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero γ hz.ne'
  have hpos : (0 : ℝ) < ‖moebiusDenom γ z‖ ^ 2 := by
    have := norm_pos_iff.mpr hd
    positivity
  rw [q.automorphy γ hγ z hz, moebiusMap_im γ hz, norm_mul, norm_pow,
    Real.sqrt_mul (by positivity),
    show ‖moebiusDenom γ z‖ ^ 4 = (‖moebiusDenom γ z‖ ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  field_simp

set_option maxHeartbeats 400000 in
-- Heartbeats: the compact-quotient descent elaborates the coercion tower of the orbit
-- covering together with nested real norms in one declaration.
/-- **Uniform bound on the density ratio**: over a cocompact group the invariant ratio
`√‖q‖ · im` is bounded on the upper half plane. -/
theorem density_ratio_bound {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, 0 < z.im → Real.sqrt ‖q z‖ * z.im ≤ M := by
  have _ := hΓ
  obtain ⟨K, hK, hcov⟩ := exists_compact_covering Γ hcc
  set K' : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' K with hK'def
  have hK'c : IsCompact K' := hK.image UpperHalfPlane.continuous_coe
  have hK'H : ∀ x ∈ K', 0 < x.im := by
    rintro x ⟨τ, hτ, rfl⟩
    exact τ.2
  have hcont : ContinuousOn (fun z : ℂ => Real.sqrt ‖q z‖ * z.im) K' := by
    refine ContinuousOn.mul ?_ Complex.continuous_im.continuousOn
    exact ((q.continuousOn_upper.mono fun x hx => hK'H x hx).norm).sqrt
  obtain ⟨M, hM⟩ := hK'c.exists_bound_of_continuousOn hcont
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
  obtain ⟨γ, hγK⟩ := hcov ⟨z, hz⟩
  set w : ℂ := moebiusMap (↑γ) z with hwdef
  have hcoe : ((γ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = w :=
    coe_smul_eq_moebiusMap _ ⟨z, hz⟩
  have hwK' : w ∈ K' := ⟨γ • ⟨z, hz⟩, hγK, hcoe⟩
  have hinv : Real.sqrt ‖q w‖ * w.im = Real.sqrt ‖q z‖ * z.im :=
    ratio_invariant q γ.2 hz
  calc Real.sqrt ‖q z‖ * z.im = Real.sqrt ‖q w‖ * w.im := hinv.symm
    _ ≤ ‖Real.sqrt ‖q w‖ * w.im‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
    _ ≤ M := hM w hwK'
    _ ≤ max M 1 := le_max_left _ _

end RiemannDynamics
