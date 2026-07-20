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
open scoped ENNReal

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

end RiemannDynamics
