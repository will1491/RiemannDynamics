import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy

/-!
# Sequential integration-by-parts boundary term and the rough-ring flux FTC

For a function `f` on `[a, b]` that is differentiable on the open interval with
square-integrable derivative, continuous up to the closed interval, and vanishing
at an endpoint, the boundary product `f · f'` has a subsequence tending to the
endpoint along which the product tends to `0`.

This packages the estimate `|f(t)| ≤ √(b - t) · ‖f'‖_{L²(t, b)}`, obtained from the
fundamental theorem of calculus and the Cauchy-Schwarz inequality, together with the
divergence of `∫ (b - t)⁻¹` which forces the weighted quantity `(b - t) · f'(t)²` to
have a subsequence tending to `0`.

These sequential boundary bricks feed the **rough-ring flux** — the angle integral of the
potential against its scale-invariant radial derivative, restricted by the indicator of an open
set `U ⊆ ball 0 1`.  On the collar the indicator is trivial, so the rough flux agrees with the
round-annulus ring flux `RiemannDynamics.ringFlux`.  On a single angular arc `(a, b)` of a slice
`C_r ∩ U` whose endpoints escape `U` — where the potential vanishes — the two sequential
bricks kill the boundary term of the angular integration by parts, giving the exact per-arc identity
`∫_a^b u · Re (deriv (expGrad u)) = ∫_a^b (Im (expGrad u))²`.
-/

namespace RiemannDynamics

open MeasureTheory intervalIntegral Filter Set
open scoped Real ENNReal Topology

/-- A square-integrable function on a finite interval is integrable there:
the pointwise bound `|g| ≤ (1 + g²)/2` dominates `g` by an integrable function. -/
theorem integrableOn_of_sq_integrableOn {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmeas : Measurable g) (hg2 : IntegrableOn (fun t => (g t) ^ 2) (Ioo a b)) :
    IntegrableOn g (Ioo a b) := by
  have _hab := hab
  have hvol : volume (Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2) (Ioo a b) :=
    integrableOn_const hvol (by simp)
  have hgsq : IntegrableOn (fun t => (g t) ^ 2 / 2) (Ioo a b) := hg2.div_const 2
  have hdom : IntegrableOn (fun t => (1 + (g t) ^ 2) / 2) (Ioo a b) := by
    have hsum : IntegrableOn (fun t => (1 : ℝ) / 2 + (g t) ^ 2 / 2) (Ioo a b) :=
      hconst.add hgsq
    refine hsum.congr_fun ?_ measurableSet_Ioo
    intro t _
    ring
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|g t| - 1), abs_nonneg (g t), sq_abs (g t)]

/-- Elementary Cauchy-Schwarz on a finite interval, via the discriminant of the
nonnegative quadratic `x ↦ ∫ (x·|g| + 1)²`:
`(∫_{t}^{b} |g|)² ≤ (b - t) · ∫_{t}^{b} g²`. -/
theorem sq_integral_abs_le {g : ℝ → ℝ} {t b : ℝ} (htb : t ≤ b)
    (hg : IntervalIntegrable g volume t b)
    (hg2 : IntervalIntegrable (fun s => (g s) ^ 2) volume t b) :
    (∫ s in t..b, |g s|) ^ 2 ≤ (b - t) * ∫ s in t..b, (g s) ^ 2 := by
  set A := ∫ s in t..b, (g s) ^ 2 with hA
  set B := ∫ s in t..b, |g s| with hB
  have hQ : ∀ x : ℝ, 0 ≤ A * (x * x) + (2 * B) * x + (b - t) := by
    intro x
    have key : ∀ s, (x * |g s| + 1) ^ 2
        = x ^ 2 * (g s) ^ 2 + (2 * x) * |g s| + 1 := by
      intro s
      rw [← sq_abs (g s)]; ring
    have hi1 : IntervalIntegrable (fun s => x ^ 2 * (g s) ^ 2) volume t b :=
      hg2.const_mul (x ^ 2)
    have hi2 : IntervalIntegrable (fun s => (2 * x) * |g s|) volume t b :=
      hg.abs.const_mul (2 * x)
    have hi3 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume t b :=
      intervalIntegral.intervalIntegrable_const
    have hnn : (0 : ℝ) ≤ ∫ s in t..b, (x * |g s| + 1) ^ 2 := by
      apply intervalIntegral.integral_nonneg htb
      intro s _
      positivity
    have hexp : (∫ s in t..b, (x * |g s| + 1) ^ 2)
        = A * (x * x) + (2 * B) * x + (b - t) := by
      simp_rw [key]
      rw [intervalIntegral.integral_add (hi1.add hi2) hi3,
          intervalIntegral.integral_add hi1 hi2,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      rw [← hA, ← hB]
      ring
    rw [hexp] at hnn
    exact hnn
  have hdisc : discrim A (2 * B) (b - t) ≤ 0 := discrim_le_zero hQ
  have hdisc' : (2 * B) ^ 2 - 4 * A * (b - t) ≤ 0 := by
    have : discrim A (2 * B) (b - t) = (2 * B) ^ 2 - 4 * A * (b - t) := by
      unfold discrim; ring
    rwa [this] at hdisc
  nlinarith [hdisc']

/-- Fundamental-theorem-of-calculus boundary bound: if `f` vanishes at `b`, is
continuous on `[a, b]`, differentiable on `(a, b)` with square-integrable derivative,
then for `t ∈ (a, b)`, `|f t| ≤ √(b - t) · √(∫_{t}^{b} (deriv f)²)`. -/
theorem abs_le_sqrt_mul_sqrt_integral_sq {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt f (deriv f s) s)
    (hf2 : IntegrableOn (fun s => (deriv f s) ^ 2) (Ioo a b))
    (hcont : ContinuousOn f (Icc a b)) (hb0 : f b = 0) {t : ℝ} (ht : t ∈ Ioo a b) :
    |f t| ≤ Real.sqrt (b - t) * Real.sqrt (∫ s in t..b, (deriv f s) ^ 2) := by
  obtain ⟨hat, htb⟩ := ht
  have _hab := hab
  have hsub : Ioo t b ⊆ Ioo a b := Ioo_subset_Ioo hat.le le_rfl
  have hg2' : IntegrableOn (fun s => (deriv f s) ^ 2) (Ioo t b) := hf2.mono_set hsub
  have hg2i : IntervalIntegrable (fun s => (deriv f s) ^ 2) volume t b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le htb.le]; exact hg2'
  have hgi : IntervalIntegrable (deriv f) volume t b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le htb.le]
    exact integrableOn_of_sq_integrableOn htb.le (measurable_deriv f) hg2'
  have hftc : ∫ s in t..b, deriv f s = f b - f t := by
    apply integral_eq_sub_of_hasDerivAt_of_le htb.le
    · exact hcont.mono (Icc_subset_Icc hat.le le_rfl)
    · intro x hx
      exact hderiv x ⟨hat.trans hx.1, hx.2⟩
    · exact hgi
  have hft : f t = -∫ s in t..b, deriv f s := by rw [hftc, hb0]; ring
  have habs : |f t| ≤ ∫ s in t..b, |deriv f s| := by
    rw [hft, abs_neg]
    exact intervalIntegral.abs_integral_le_integral_abs htb.le
  have h0 : (0 : ℝ) ≤ ∫ s in t..b, |deriv f s| :=
    intervalIntegral.integral_nonneg htb.le fun s _ => abs_nonneg _
  have hcs := sq_integral_abs_le htb.le hgi hg2i
  have h2 : (∫ s in t..b, |deriv f s|)
      ≤ Real.sqrt ((b - t) * ∫ s in t..b, (deriv f s) ^ 2) := by
    rw [show (∫ s in t..b, |deriv f s|)
        = Real.sqrt ((∫ s in t..b, |deriv f s|) ^ 2) from (Real.sqrt_sq h0).symm]
    exact Real.sqrt_le_sqrt hcs
  calc |f t| ≤ ∫ s in t..b, |deriv f s| := habs
    _ ≤ Real.sqrt ((b - t) * ∫ s in t..b, (deriv f s) ^ 2) := h2
    _ = Real.sqrt (b - t) * Real.sqrt (∫ s in t..b, (deriv f s) ^ 2) :=
      Real.sqrt_mul (by linarith) _

/-- The divergence of `∫ (b - t)⁻¹` forces a sequence `t n → b` inside `(a, b)`
along which the weight `(b - t n) · (deriv f (t n))²` is smaller than `1 / (n + 1)`. -/
theorem exists_seq_weight_deriv_sq_lt {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf2 : IntegrableOn (fun s => (deriv f s) ^ 2) (Ioo a b)) :
    ∃ t : ℕ → ℝ, (∀ n, t n ∈ Ioo a b) ∧ Tendsto t atTop (nhds b) ∧
      (∀ n, (b - t n) * (deriv f (t n)) ^ 2 < 1 / (n + 1)) := by
  have key : ∀ n : ℕ, ∃ s : ℝ, s ∈ Ioo a b ∧ b - s < 1 / ((n : ℝ) + 1) ∧
      (b - s) * (deriv f s) ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    set δ : ℝ := min ((b - a) / 2) ε with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) hεpos
    have hδε : δ ≤ ε := min_le_right _ _
    have hδab : δ ≤ (b - a) / 2 := min_le_left _ _
    have hsub : Ioo (b - δ) b ⊆ Ioo a b := fun s hs =>
      ⟨by have := hs.1; linarith, hs.2⟩
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have hgint : IntegrableOn (fun s => (deriv f s) ^ 2) (Ioo (b - δ) b) :=
      hf2.mono_set hsub
    have hdom : IntegrableOn (fun s : ℝ => ε * (b - s)⁻¹) (Ioo (b - δ) b) := by
      apply hgint.mono'
        ((measurable_const.mul
          ((measurable_const.sub measurable_id').inv)).aestronglyMeasurable)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hbs : 0 < b - s := by have := hs.2; linarith
      have hsab : s ∈ Ioo a b := hsub hs
      have hlt : b - s < ε := lt_of_lt_of_le (by have := hs.1; linarith) hδε
      have hbound := hcon s hsab hlt
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hεpos.le (inv_nonneg.mpr hbs.le))]
      rw [← div_eq_mul_inv, div_le_iff₀ hbs]
      calc ε ≤ (b - s) * (deriv f s) ^ 2 := hbound
        _ = (deriv f s) ^ 2 * (b - s) := mul_comm _ _
    have hconstmul : IntegrableOn (fun s : ℝ => ε⁻¹ * (ε * (b - s)⁻¹)) (Ioo (b - δ) b) :=
      hdom.const_mul ε⁻¹
    have hinv : IntegrableOn (fun s : ℝ => (b - s)⁻¹) (Ioo (b - δ) b) := by
      apply hconstmul.congr_fun ?_ measurableSet_Ioo
      intro s _
      change ε⁻¹ * (ε * (b - s)⁻¹) = (b - s)⁻¹
      rw [← mul_assoc, inv_mul_cancel₀ hεpos.ne', one_mul]
    have hmp : MeasurePreserving (fun s : ℝ => b - s) volume volume :=
      Measure.measurePreserving_sub_left volume b
    have hemb : MeasurableEmbedding (fun s : ℝ => b - s) :=
      (Homeomorph.subLeft b).measurableEmbedding
    have hpre : (fun s : ℝ => b - s) ⁻¹' (Ioo 0 δ) = Ioo (b - δ) b := by
      ext s
      simp only [mem_preimage, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    have hiff := hmp.integrableOn_comp_preimage hemb
      (f := fun x : ℝ => x⁻¹) (s := Ioo 0 δ)
    rw [hpre] at hiff
    have hio : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo 0 δ) volume :=
      hiff.mp (hinv.congr_fun (fun s _ => rfl) measurableSet_Ioo)
    have hrpow : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 δ) volume := by
      apply hio.congr_fun ?_ measurableSet_Ioo
      intro x _
      change x⁻¹ = x ^ (-1 : ℝ)
      rw [show ((-1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg_one]
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hδpos] at hrpow
    linarith
  choose t ht using key
  refine ⟨t, fun n => (ht n).1, ?_, fun n => (ht n).2.2⟩
  have hlow : ∀ n : ℕ, b - 1 / ((n : ℝ) + 1) ≤ t n := fun n => by
    have := (ht n).2.1; linarith
  have hup : ∀ n : ℕ, t n ≤ b := fun n => ((ht n).1).2.le
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => b - 1 / ((n : ℝ) + 1)) atTop (nhds b) := by
    simpa using tendsto_const_nhds.sub h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h2 tendsto_const_nhds hlow hup

/-- Sequential boundary term vanishing at the right endpoint: there is a sequence
`t n → b` inside `(a, b)` along which `f (t n) · deriv f (t n) → 0`. -/
theorem boundary_term_liminf_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt f (deriv f t) t)
    (hf2 : MeasureTheory.IntegrableOn (fun t => (deriv f t) ^ 2) (Set.Ioo a b))
    (hcont : ContinuousOn f (Set.Icc a b)) (hb0 : f b = 0) :
    ∃ t : ℕ → ℝ, (∀ n, t n ∈ Set.Ioo a b) ∧ Filter.Tendsto t Filter.atTop (nhds b) ∧
      Filter.Tendsto (fun n => f (t n) * deriv f (t n)) Filter.atTop (nhds 0) := by
  obtain ⟨t, htmem, htto, hsmall⟩ := exists_seq_weight_deriv_sq_lt hab hf2
  refine ⟨t, htmem, htto, ?_⟩
  set M := ∫ s in Ioo a b, (deriv f s) ^ 2 with hM
  have hbound : ∀ n : ℕ, |f (t n) * deriv f (t n)|
      ≤ Real.sqrt (1 / ((n : ℝ) + 1)) * Real.sqrt M := by
    intro n
    obtain ⟨hat, htb⟩ := htmem n
    have h1 := abs_le_sqrt_mul_sqrt_integral_sq hab hderiv hf2 hcont hb0 (htmem n)
    have hIle : (∫ s in (t n)..b, (deriv f s) ^ 2) ≤ M := by
      rw [intervalIntegral.integral_of_le htb.le]
      apply setIntegral_mono_set hf2 (ae_of_all _ fun s => sq_nonneg _)
      rw [ae_le_set]
      apply measure_mono_null (fun x hx => ?_) (measure_singleton b)
      obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
      simp only [mem_Ioo, not_and, not_lt] at hx3
      have hbx := hx3 (hat.trans hx1)
      simp [le_antisymm hx2 hbx]
    have hsqle : Real.sqrt (∫ s in (t n)..b, (deriv f s) ^ 2) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt hIle
    rw [abs_mul]
    calc |f (t n)| * |deriv f (t n)|
        ≤ (Real.sqrt (b - t n) * Real.sqrt (∫ s in (t n)..b, (deriv f s) ^ 2))
            * |deriv f (t n)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = (Real.sqrt (b - t n) * |deriv f (t n)|)
            * Real.sqrt (∫ s in (t n)..b, (deriv f s) ^ 2) := by ring
      _ = Real.sqrt ((b - t n) * (deriv f (t n)) ^ 2)
            * Real.sqrt (∫ s in (t n)..b, (deriv f s) ^ 2) := by
          rw [Real.sqrt_mul (by linarith) ((deriv f (t n)) ^ 2), Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (1 / ((n : ℝ) + 1)) * Real.sqrt M :=
          mul_le_mul (Real.sqrt_le_sqrt (hsmall n).le) hsqle (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
  have hto : Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1)) * Real.sqrt M)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
      have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa only [Function.comp_def, Real.sqrt_zero] using h3
    simpa using h2.mul_const (Real.sqrt M)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _) hbound hto

/-- Sequential boundary term vanishing at the left endpoint: there is a sequence
`t n → a` inside `(a, b)` along which `f (t n) · deriv f (t n) → 0`. Obtained from the
right-endpoint version by the reflection `s ↦ a + b - s`. -/
theorem boundary_term_liminf_zero_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt f (deriv f t) t)
    (hf2 : MeasureTheory.IntegrableOn (fun t => (deriv f t) ^ 2) (Set.Ioo a b))
    (hcont : ContinuousOn f (Set.Icc a b)) (ha0 : f a = 0) :
    ∃ t : ℕ → ℝ, (∀ n, t n ∈ Set.Ioo a b) ∧ Filter.Tendsto t Filter.atTop (nhds a) ∧
      Filter.Tendsto (fun n => f (t n) * deriv f (t n)) Filter.atTop (nhds 0) := by
  set F : ℝ → ℝ := fun s => f (a + b - s) with hF
  have hrefl_mem : ∀ s ∈ Ioo a b, a + b - s ∈ Ioo a b := fun s hs =>
    ⟨by have := hs.2; linarith, by have := hs.1; linarith⟩
  have hFderiv : ∀ s ∈ Ioo a b, HasDerivAt F (-(deriv f (a + b - s))) s := by
    intro s hs
    have h1 : HasDerivAt (fun u : ℝ => a + b - u) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (a + b)
    have h2 : HasDerivAt f (deriv f (a + b - s)) (a + b - s) :=
      hderiv _ (hrefl_mem s hs)
    have h3 := h2.comp s h1
    simpa [hF, Function.comp_def] using h3
  have hFd : ∀ s ∈ Ioo a b, deriv F s = -(deriv f (a + b - s)) := fun s hs =>
    (hFderiv s hs).deriv
  have hFderiv' : ∀ s ∈ Ioo a b, HasDerivAt F (deriv F s) s := fun s hs => by
    rw [hFd s hs]; exact hFderiv s hs
  have hFcont : ContinuousOn F (Icc a b) := by
    apply hcont.comp ((continuous_const.sub continuous_id).continuousOn)
    intro s hs
    simp only [id_eq, mem_Icc] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  have hFb : F b = 0 := by
    have : a + b - b = a := by ring
    rw [hF]; simp only [this]; exact ha0
  have hFint : IntegrableOn (fun s => (deriv F s) ^ 2) (Ioo a b) := by
    have hmp : MeasurePreserving (fun s : ℝ => a + b - s) volume volume :=
      Measure.measurePreserving_sub_left volume (a + b)
    have hemb : MeasurableEmbedding (fun s : ℝ => a + b - s) :=
      (Homeomorph.subLeft (a + b)).measurableEmbedding
    have hpre : (fun s : ℝ => a + b - s) ⁻¹' (Ioo a b) = Ioo a b := by
      ext s
      simp only [mem_preimage, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    have hiff := hmp.integrableOn_comp_preimage hemb
      (f := fun s => (deriv f s) ^ 2) (s := Ioo a b)
    rw [hpre] at hiff
    have hcomp : IntegrableOn (fun s : ℝ => (deriv f (a + b - s)) ^ 2) (Ioo a b) := by
      have h4 := hiff.mpr hf2
      simpa [Function.comp_def] using h4
    apply hcomp.congr_fun ?_ measurableSet_Ioo
    intro s hs
    simp only [hFd s hs]
    ring
  obtain ⟨s, hsmem, hsto, hsprod⟩ := boundary_term_liminf_zero hab hFderiv' hFint hFcont hFb
  refine ⟨fun n => a + b - s n, fun n => hrefl_mem _ (hsmem n), ?_, ?_⟩
  · have h5 : Tendsto (fun n : ℕ => a + b - s n) atTop (nhds (a + b - b)) :=
      tendsto_const_nhds.sub hsto
    simpa using h5
  · have heq : ∀ n, f (a + b - s n) * deriv f (a + b - s n)
        = -(F (s n) * deriv F (s n)) := by
      intro n
      rw [hFd _ (hsmem n)]
      simp only [hF]
      ring
    have h6 := hsprod.neg
    rw [neg_zero] at h6
    exact Tendsto.congr (fun n => (heq n).symm) h6

/-- **Interval integral over a left-shrinking window converges to the full integral.** For `h`
integrable on `(a, c)` and a left-endpoint sequence `p n → a` inside `(a, c)`, the interval
integrals `∫_{p n}^{c} h` converge to `∫_{(a, c)} h`: the indicators of the shrinking windows
converge pointwise a.e. to the indicator of `(a, c)`, and dominated convergence applies on the
finite measure `volume.restrict (Ioo a c)`. -/
theorem tendsto_intervalIntegral_left_shrinking {h : ℝ → ℝ} {a c : ℝ} {p : ℕ → ℝ}
    (hint : IntegrableOn h (Ioo a c))
    (hpmem : ∀ᶠ n in atTop, p n ∈ Ioo a c) (hpto : Tendsto p atTop (nhds a)) :
    Tendsto (fun n => ∫ t in (p n)..c, h t) atTop (nhds (∫ t in Ioo a c, h t)) := by
  have hμfin : IsFiniteMeasure (volume.restrict (Ioo a c)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hstep : (fun n => ∫ t in (p n)..c, h t)
      =ᶠ[atTop] fun n => ∫ t in Ioo a c, (Ioo (p n) c).indicator h t := by
    filter_upwards [hpmem] with n hn
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_self_of_subset_right (Ioo_subset_Ioo hn.1.le le_rfl),
      intervalIntegral.integral_of_le hn.2.le, integral_Ioc_eq_integral_Ioo]
  refine Tendsto.congr' hstep.symm ?_
  rw [show (∫ t in Ioo a c, h t) = ∫ t in Ioo a c, (Ioo a c).indicator h t from
    (setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => (Set.indicator_of_mem ht h).symm))]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun t => ‖h t‖)
    (fun n => hint.aestronglyMeasurable.indicator measurableSet_Ioo)
    hint.norm ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t _
    rw [Set.indicator]
    split_ifs with hmem
    · exact le_refl _
    · rw [norm_zero]; exact norm_nonneg _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    -- eventually `p n < t`, so the shrinking indicator equals `h t`
    have hpt : ∀ᶠ n in atTop, p n < t := hpto.eventually_lt_const ht.1
    have hev : (fun n => (Ioo (p n) c).indicator h t)
        =ᶠ[atTop] fun _ => (Ioo a c).indicator h t := by
      filter_upwards [hpt] with n hn
      rw [Set.indicator_of_mem (show t ∈ Ioo (p n) c from ⟨hn, ht.2⟩),
        Set.indicator_of_mem ht]
    exact Tendsto.congr' hev.symm tendsto_const_nhds

/-- **Interval integral over a right-shrinking window converges to the full integral.** For `h`
integrable on `(c, b)` and a right-endpoint sequence `q n → b` inside `(c, b)`, the interval
integrals `∫_{c}^{q n} h` converge to `∫_{(c, b)} h`. -/
theorem tendsto_intervalIntegral_right_shrinking {h : ℝ → ℝ} {c b : ℝ} {q : ℕ → ℝ}
    (hint : IntegrableOn h (Ioo c b))
    (hqmem : ∀ᶠ n in atTop, q n ∈ Ioo c b) (hqto : Tendsto q atTop (nhds b)) :
    Tendsto (fun n => ∫ t in c..(q n), h t) atTop (nhds (∫ t in Ioo c b, h t)) := by
  have hμfin : IsFiniteMeasure (volume.restrict (Ioo c b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hstep : (fun n => ∫ t in c..(q n), h t)
      =ᶠ[atTop] fun n => ∫ t in Ioo c b, (Ioo c (q n)).indicator h t := by
    filter_upwards [hqmem] with n hn
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_self_of_subset_right (Ioo_subset_Ioo le_rfl hn.2.le),
      intervalIntegral.integral_of_le hn.1.le, integral_Ioc_eq_integral_Ioo]
  refine Tendsto.congr' hstep.symm ?_
  rw [show (∫ t in Ioo c b, h t) = ∫ t in Ioo c b, (Ioo c b).indicator h t from
    (setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => (Set.indicator_of_mem ht h).symm))]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun t => ‖h t‖)
    (fun n => hint.aestronglyMeasurable.indicator measurableSet_Ioo)
    hint.norm ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t _
    rw [Set.indicator]
    split_ifs with hmem
    · exact le_refl _
    · rw [norm_zero]; exact norm_nonneg _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hqt : ∀ᶠ n in atTop, t < q n := hqto.eventually_const_lt ht.2
    have hev : (fun n => (Ioo c (q n)).indicator h t)
        =ᶠ[atTop] fun _ => (Ioo c b).indicator h t := by
      filter_upwards [hqt] with n hn
      rw [Set.indicator_of_mem (show t ∈ Ioo c (q n) from ⟨ht.1, hn⟩),
        Set.indicator_of_mem ht]
    exact Tendsto.congr' hev.symm tendsto_const_nhds

/-! ### Sequential integration by parts on an open arc with vanishing endpoints -/

/-- **Sequential integration by parts on an open arc.** For `f`, `g` on `(a, b)` with `f`
continuous on the closed arc, `f` differentiable there with `deriv f = -g`, `g` differentiable
with derivative `g'`, `(deriv f)²` integrable, `g` and `g'` interval-integrable, and `f` vanishing
at both endpoints, the boundary term of the integration by parts is annihilated in the limit by the
two sequential bricks, giving `∫_a^b f · g' = ∫_a^b g²`. -/
theorem integral_mul_deriv_eq_integral_sq_of_endpoints_zero {f g g' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (deriv f t) t)
    (hfg : ∀ t ∈ Ioo a b, deriv f t = -g t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t)
    (hf2 : IntegrableOn (fun t => (deriv f t) ^ 2) (Ioo a b))
    (hcont : ContinuousOn f (Icc a b))
    (hgint : IntegrableOn g (Ioo a b)) (hg'int : IntegrableOn g' (Ioo a b))
    (ha0 : f a = 0) (hb0 : f b = 0) :
    ∫ t in a..b, f t * g' t = ∫ t in a..b, (g t) ^ 2 := by
  -- the two endpoint sequences, with the boundary products tending to `0`
  obtain ⟨sN, hsNmem, hsNto, hsNprod⟩ := boundary_term_liminf_zero hab hderiv hf2 hcont hb0
  obtain ⟨tN, htNmem, htNto, htNprod⟩ := boundary_term_liminf_zero_left hab hderiv hf2 hcont ha0
  -- integrability of the interior integrands on `(a, b)`
  have hg2int : IntegrableOn (fun t => (g t) ^ 2) (Ioo a b) := by
    refine hf2.congr_fun (fun t ht => ?_) measurableSet_Ioo
    rw [hfg t ht]; ring
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b)) :=
    ((hcont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
  have hfg'int : IntegrableOn (fun t => f t * g' t) (Ioo a b) := by
    -- `f · g'` is dominated: `f` is bounded (continuous on the compact `[a, b]`)
    obtain ⟨C, hC⟩ := (isCompact_Icc.exists_bound_of_continuousOn hcont)
    refine Integrable.mono' (hg'int.norm.const_mul C) ?_ ?_
    · exact hfmeas.mul hg'int.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC t (Ioo_subset_Icc_self ht)) (norm_nonneg _)
  -- the fixed midpoint
  set c : ℝ := (a + b) / 2 with hc
  have hac : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  -- interval integrability on any closed subinterval of `(a, b)`
  have hgii : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]; exact hgint
  have hg'ii : IntervalIntegrable g' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]; exact hg'int
  have hg2ii : IntervalIntegrable (fun t => (g t) ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]; exact hg2int
  have hfg'ii : IntervalIntegrable (fun t => f t * g' t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]; exact hfg'int
  -- interior integration by parts on `[p, q] ⊆ (a, b)`
  have hIBP : ∀ p q : ℝ, a < p → p ≤ q → q < b →
      ∫ t in p..q, f t * g' t
        = f q * g q - f p * g p + ∫ t in p..q, (g t) ^ 2 := by
    intro p q hap hpq hqb
    have hIcc : Icc p q ⊆ Ioo a b := fun t ht =>
      ⟨lt_of_lt_of_le hap ht.1, lt_of_le_of_lt ht.2 hqb⟩
    have hIoopq : Ioo (min p q) (max p q) ⊆ Ioo a b := by
      rw [min_eq_left hpq, max_eq_right hpq]
      exact fun t ht => ⟨lt_trans hap ht.1, lt_trans ht.2 hqb⟩
    have hfc : ContinuousOn f (uIcc p q) := by
      rw [uIcc_of_le hpq]; exact hcont.mono (hIcc.trans Ioo_subset_Icc_self)
    have hgc : ContinuousOn g (uIcc p q) := by
      rw [uIcc_of_le hpq]
      exact fun t ht => (hg t (hIcc ht)).continuousAt.continuousWithinAt
    -- interior derivatives on `(min p q, max p q)`
    have hf' : ∀ t ∈ Ioo (min p q) (max p q), HasDerivAt f (deriv f t) t :=
      fun t ht => hderiv t (hIoopq ht)
    have hg'' : ∀ t ∈ Ioo (min p q) (max p q), HasDerivAt g (g' t) t :=
      fun t ht => hg t (hIoopq ht)
    have hsubuIcc : uIcc p q ⊆ uIcc a b := by
      rw [uIcc_of_le hpq, uIcc_of_le hab.le]
      exact fun t ht => ⟨hap.le.trans ht.1, ht.2.trans hqb.le⟩
    have hg'pq : IntervalIntegrable g' volume p q := hg'ii.mono_set hsubuIcc
    have hdfpq : IntervalIntegrable (deriv f) volume p q := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hpq]
      exact integrableOn_of_sq_integrableOn hpq (measurable_deriv f)
        (hf2.mono_set (fun t ht => hIcc (Ioo_subset_Icc_self ht)))
    have hIBP0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hfc hgc hf' hg'' hdfpq hg'pq
    -- `∫ (deriv f) · g = - ∫ g²` since `deriv f = -g`
    have hconv : (∫ t in p..q, deriv f t * g t) = - ∫ t in p..q, (g t) ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le hpq] at ht
      rw [hfg t (hIcc ht)]; ring
    rw [hIBP0, hconv]; ring
  -- integrability on the two halves, for splitting the interval integrals
  have hIooac : Ioo a c ⊆ Ioo a b := Ioo_subset_Ioo le_rfl hcb.le
  have hIoocb : Ioo c b ⊆ Ioo a b := Ioo_subset_Ioo hac.le le_rfl
  have hfg'iiL : IntervalIntegrable (fun t => f t * g' t) volume a c := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le]
    exact hfg'int.mono_set hIooac
  have hfg'iiR : IntervalIntegrable (fun t => f t * g' t) volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le]
    exact hfg'int.mono_set hIoocb
  have hg2iiL : IntervalIntegrable (fun t => (g t) ^ 2) volume a c := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le]
    exact hg2int.mono_set hIooac
  have hg2iiR : IntervalIntegrable (fun t => (g t) ^ 2) volume c b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hcb.le]
    exact hg2int.mono_set hIoocb
  -- the boundary product tends to `0` along each endpoint sequence (using `deriv f = -g`)
  have htNprod' : Tendsto (fun n => f (tN n) * g (tN n)) atTop (nhds 0) := by
    have heq : (fun n => f (tN n) * deriv f (tN n))
        =ᶠ[atTop] fun n => -(f (tN n) * g (tN n)) := by
      filter_upwards with n
      rw [hfg _ (htNmem n)]; ring
    have := (Tendsto.congr' heq htNprod).neg
    simpa using this
  have hsNprod' : Tendsto (fun n => f (sN n) * g (sN n)) atTop (nhds 0) := by
    have heq : (fun n => f (sN n) * deriv f (sN n))
        =ᶠ[atTop] fun n => -(f (sN n) * g (sN n)) := by
      filter_upwards with n
      rw [hfg _ (hsNmem n)]; ring
    have := (Tendsto.congr' heq hsNprod).neg
    simpa using this
  -- eventual membership of the sequences in the half-arcs
  have htNac : ∀ᶠ n in atTop, tN n ∈ Ioo a c := by
    filter_upwards [htNto.eventually_lt_const hac] with n hn
    exact ⟨(htNmem n).1, hn⟩
  have hsNcb : ∀ᶠ n in atTop, sN n ∈ Ioo c b := by
    filter_upwards [hsNto.eventually_const_lt hcb] with n hn
    exact ⟨hn, (hsNmem n).2⟩
  -- left half: `∫_a^c f·g' = f(c)·g(c) + ∫_a^c g²`
  have hleftFTC : (fun n => ∫ t in (tN n)..c, f t * g' t)
      =ᶠ[atTop] fun n => f c * g c - f (tN n) * g (tN n) + ∫ t in (tN n)..c, (g t) ^ 2 := by
    filter_upwards [htNac] with n hn
    exact hIBP (tN n) c hn.1 hn.2.le hcb
  have hleftLHS : Tendsto (fun n => ∫ t in (tN n)..c, f t * g' t) atTop
      (nhds (∫ t in Ioo a c, f t * g' t)) :=
    tendsto_intervalIntegral_left_shrinking (hfg'int.mono_set hIooac) htNac htNto
  have hleftRHS : Tendsto (fun n =>
      f c * g c - f (tN n) * g (tN n) + ∫ t in (tN n)..c, (g t) ^ 2) atTop
      (nhds (f c * g c - 0 + ∫ t in Ioo a c, (g t) ^ 2)) :=
    ((tendsto_const_nhds.sub htNprod').add
      (tendsto_intervalIntegral_left_shrinking (hg2int.mono_set hIooac) htNac htNto))
  have hleft : ∫ t in Ioo a c, f t * g' t
      = f c * g c + ∫ t in Ioo a c, (g t) ^ 2 := by
    have := tendsto_nhds_unique hleftLHS (hleftRHS.congr' hleftFTC.symm)
    rw [this]; ring
  -- right half: `∫_c^b f·g' = -f(c)·g(c) + ∫_c^b g²`
  have hrightFTC : (fun n => ∫ t in c..(sN n), f t * g' t)
      =ᶠ[atTop] fun n => f (sN n) * g (sN n) - f c * g c + ∫ t in c..(sN n), (g t) ^ 2 := by
    filter_upwards [hsNcb] with n hn
    exact hIBP c (sN n) hac hn.1.le hn.2
  have hrightLHS : Tendsto (fun n => ∫ t in c..(sN n), f t * g' t) atTop
      (nhds (∫ t in Ioo c b, f t * g' t)) :=
    tendsto_intervalIntegral_right_shrinking (hfg'int.mono_set hIoocb) hsNcb hsNto
  have hrightRHS : Tendsto (fun n =>
      f (sN n) * g (sN n) - f c * g c + ∫ t in c..(sN n), (g t) ^ 2) atTop
      (nhds (0 - f c * g c + ∫ t in Ioo c b, (g t) ^ 2)) :=
    ((hsNprod'.sub tendsto_const_nhds).add
      (tendsto_intervalIntegral_right_shrinking (hg2int.mono_set hIoocb) hsNcb hsNto))
  have hright : ∫ t in Ioo c b, f t * g' t
      = -(f c * g c) + ∫ t in Ioo c b, (g t) ^ 2 := by
    have := tendsto_nhds_unique hrightLHS (hrightRHS.congr' hrightFTC.symm)
    rw [this]; ring
  -- assemble: split both interval integrals at `c`, the `f(c)·g(c)` terms cancel
  rw [← intervalIntegral.integral_add_adjacent_intervals hfg'iiL hfg'iiR,
    ← intervalIntegral.integral_add_adjacent_intervals hg2iiL hg2iiR,
    intervalIntegral.integral_of_le hac.le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hcb.le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hac.le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hcb.le, integral_Ioc_eq_integral_Ioo,
    hleft, hright]
  ring

/-! ### Per-arc flux identity for a harmonic potential on an open set -/

open Complex

/-- **Holomorphy of the log-polar gradient over an open set.** For `u` harmonic on an open set `U`,
`expGrad u` is complex-differentiable at every `w` whose exponential lies in `U`. -/
theorem expGrad_differentiableAt_open {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) {w : ℂ} (hw : Complex.exp w ∈ U) :
    DifferentiableAt ℂ (expGrad u) w := by
  have hg : DifferentiableAt ℂ (gradC u) (Complex.exp w) :=
    (gradC_differentiableOn hu).differentiableAt (hU.mem_nhds hw)
  exact ((hg.comp w (Complex.differentiable_exp w)).mul (Complex.differentiable_exp w))

/-- **Per-arc flux identity.** For `u` harmonic on an open set `U ⊆ ℂ` and a log-radius `ξ`, on
a closed angular arc `[a, b]` whose interior maps into `U` under `θ ↦ e^{ξ+θi}`, whose
endpoints map to points where `u` vanishes, with `u` continuous on the closed slice arc, the slice
squared-gradient integrable, and the slice radial-derivative integrand integrable, the angle
integral of `u(e^{ξ+θi}) · Re (deriv (expGrad u))` over the arc equals the integral of
`(Im (expGrad u))²`: the two sequential boundary bricks annihilate the integration-by-parts
boundary term at both ends. -/
theorem integral_uexp_re_deriv_expGrad_arc {u : ℂ → ℝ} {U : Set ℂ} {ξ a b : ℝ}
    (hU : IsOpen U) (hab : a < b)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (harc : ∀ θ ∈ Ioo a b, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hcont : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc a b))
    (hslice : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo a b))
    (hg'int : IntegrableOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b))
    (ha0 : u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I)) = 0)
    (hb0 : u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I)) = 0) :
    ∫ θ in a..b, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  set f : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with hf
  set g : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgdef
  set g' : ℝ → ℝ :=
    fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hg'def
  -- differentiability on the open arc
  have hdiffR : ∀ θ ∈ Ioo a b,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ hθ =>
    differentiableAt_of_harmonicOnNhd hu (harc θ hθ)
  have hdiffC : ∀ θ ∈ Ioo a b,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ hθ =>
    expGrad_differentiableAt_open hU hu (harc θ hθ)
  -- slice derivative facts (angular direction)
  have hfg : ∀ θ ∈ Ioo a b, deriv f θ = -g θ := fun θ hθ =>
    (hasDerivAt_uexp_angular (hdiffR θ hθ)).deriv
  have hfderiv : ∀ θ ∈ Ioo a b, HasDerivAt f (deriv f θ) θ := by
    intro θ hθ; rw [hfg θ hθ]; exact hasDerivAt_uexp_angular (hdiffR θ hθ)
  have hgderiv : ∀ θ ∈ Ioo a b, HasDerivAt g (g' θ) θ := by
    intro θ hθ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ hθ)
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [hgdef, hg'def, Function.comp, Complex.mul_im] using hcomp
  -- `g` is continuous, hence measurable, on the open arc
  have hgcont : ContinuousOn g (Ioo a b) := fun θ hθ =>
    (hgderiv θ hθ).continuousAt.continuousWithinAt
  -- `(deriv f)² = g² ≤ normSq (expGrad u)` gives square-integrability of `deriv f`
  have hf2 : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Ioo a b) := by
    have hg2meas : AEStronglyMeasurable (fun θ => (deriv f θ) ^ 2)
        (volume.restrict (Ioo a b)) := by
      refine ((hgcont.aestronglyMeasurable measurableSet_Ioo).pow 2).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hfg θ hθ]; simp [hgdef]
    refine Integrable.mono' hslice hg2meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [hfg θ hθ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        ≤ Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [Complex.normSq_apply]; nlinarith [sq_nonneg
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
    simpa [hgdef] using this
  -- `g` is integrable: `|g| ≤ (1 + g²)/2` dominates it by an integrable function
  have hg2int : IntegrableOn (fun θ => (g θ) ^ 2) (Ioo a b) :=
    hf2.congr_fun (fun θ hθ => by rw [hfg θ hθ]; simp [hgdef]) measurableSet_Ioo
  have hgint : IntegrableOn g (Ioo a b) := by
    have hvol : volume (Ioo a b) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2) (Ioo a b) :=
      integrableOn_const hvol (by simp)
    have hsum : IntegrableOn (fun θ => (1 : ℝ) / 2 + (g θ) ^ 2 / 2) (Ioo a b) :=
      hconst.add (hg2int.div_const 2)
    have hdom : IntegrableOn (fun θ => (1 + (g θ) ^ 2) / 2) (Ioo a b) :=
      hsum.congr_fun (fun θ _ => by ring) measurableSet_Ioo
    refine hdom.mono' (hgcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|g θ| - 1), abs_nonneg (g θ), sq_abs (g θ)]
  -- apply the abstract per-arc integration by parts
  exact integral_mul_deriv_eq_integral_sq_of_endpoints_zero hab hfderiv hfg hgderiv hf2
    hcont hgint hg'int ha0 hb0

/-! ### Countable open-interval decomposition of a bounded open subset of `ℝ` -/

/-- **A bounded open connected component is an open interval.** If `C = connectedComponentIn O ξ`
for `ξ` in an open set `O ⊆ Ioo c d`, then `C = Ioo (sInf C) (sSup C)` with both endpoints escaping
`O` and lying in `[c, d]`. -/
theorem connectedComponentIn_eq_Ioo {O : Set ℝ} {c d ξ : ℝ} (hO : IsOpen O)
    (hOsub : O ⊆ Ioo c d) (hξ : ξ ∈ O) :
    connectedComponentIn O ξ
        = Ioo (sInf (connectedComponentIn O ξ)) (sSup (connectedComponentIn O ξ))
      ∧ sInf (connectedComponentIn O ξ) ∉ O ∧ sSup (connectedComponentIn O ξ) ∉ O
      ∧ c ≤ sInf (connectedComponentIn O ξ) ∧ sSup (connectedComponentIn O ξ) ≤ d := by
  set C : Set ℝ := connectedComponentIn O ξ with hCdef
  have hξC : ξ ∈ C := mem_connectedComponentIn hξ
  have hCO : C ⊆ O := connectedComponentIn_subset O ξ
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hCord : OrdConnected C := hCpre.ordConnected
  have hCbdd : C ⊆ Ioo c d := hCO.trans hOsub
  have hbelow : BddBelow C := ⟨c, fun x hx => (hCbdd hx).1.le⟩
  have habove : BddAbove C := ⟨d, fun x hx => (hCbdd hx).2.le⟩
  set α : ℝ := sInf C with hαdef
  set β : ℝ := sSup C with hβdef
  have hαle : α ≤ ξ := csInf_le hbelow hξC
  have hleβ : ξ ≤ β := le_csSup habove hξC
  -- `Ioo α β ⊆ C` via ordConnectedness, approximating from both sides
  have hIooC : Ioo α β ⊆ C := by
    intro y hy
    obtain ⟨a, haC, hay⟩ := exists_lt_of_csInf_lt ⟨ξ, hξC⟩ hy.1
    obtain ⟨b, hbC, hyb⟩ := exists_lt_of_lt_csSup ⟨ξ, hξC⟩ hy.2
    exact hCord.out haC hbC ⟨hay.le, hyb.le⟩
  -- left endpoint escapes `O`: openness of `O` would extend the component below its infimum
  have hαnotO : α ∉ O := by
    intro hαO
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO α hαO
    obtain ⟨a, haC, haα⟩ := exists_lt_of_csInf_lt ⟨ξ, hξC⟩ (by linarith : α < α + ε)
    have hIball : Ioo (α - ε) (α + ε) ⊆ O := fun x hx => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have haInBall : a ∈ Ioo (α - ε) (α + ε) := ⟨by linarith [csInf_le hbelow haC], haα⟩
    have hsub : C ∪ Ioo (α - ε) (α + ε) ⊆ C :=
      (hCpre.union' ⟨a, haC, haInBall⟩ isPreconnected_Ioo).subset_connectedComponentIn
        (Or.inl hξC) (union_subset hCO hIball)
    have := csInf_le hbelow (hsub (Or.inr ⟨by linarith, by linarith⟩ : α - ε / 2 ∈ _))
    linarith
  -- right endpoint escapes `O`, symmetrically
  have hβnotO : β ∉ O := by
    intro hβO
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO β hβO
    obtain ⟨b, hbC, hbβ⟩ := exists_lt_of_lt_csSup ⟨ξ, hξC⟩ (by linarith : β - ε < β)
    have hIball : Ioo (β - ε) (β + ε) ⊆ O := fun x hx => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hbInBall : b ∈ Ioo (β - ε) (β + ε) := ⟨hbβ, by linarith [le_csSup habove hbC]⟩
    have hsub : C ∪ Ioo (β - ε) (β + ε) ⊆ C :=
      (hCpre.union' ⟨b, hbC, hbInBall⟩ isPreconnected_Ioo).subset_connectedComponentIn
        (Or.inl hξC) (union_subset hCO hIball)
    have := le_csSup habove (hsub (Or.inr ⟨by linarith, by linarith⟩ : β + ε / 2 ∈ _))
    linarith
  -- `C ⊆ Ioo α β`: `α, β ∉ C` (they escape `O ⊇ C`), so all of `C` is strictly interior
  have hCIoo : C ⊆ Ioo α β := by
    intro y hy
    refine ⟨lt_of_le_of_ne (csInf_le hbelow hy) (fun h => hαnotO (h ▸ hCO hy)),
      lt_of_le_of_ne (le_csSup habove hy) (fun h => hβnotO (h.symm ▸ hCO hy))⟩
  refine ⟨Subset.antisymm hCIoo hIooC, hαnotO, hβnotO,
    le_csInf ⟨ξ, hξC⟩ (fun x hx => (hCbdd hx).1.le),
    csSup_le ⟨ξ, hξC⟩ (fun x hx => (hCbdd hx).2.le)⟩

/-- **Countable open-interval decomposition of a bounded open subset of `ℝ`.** A bounded open set
`O ⊆ Ioo c d` is the union of the countably many pairwise-disjoint open intervals `Ioo p.1 p.2`
(`p` in a countable set `S`), each with endpoints escaping `O` and contained in `[c, d]`. -/
theorem isOpen_eq_iUnion_Ioo {O : Set ℝ} {c d : ℝ} (hO : IsOpen O) (hOsub : O ⊆ Ioo c d) :
    ∃ S : Set (ℝ × ℝ), S.Countable ∧
      S.PairwiseDisjoint (fun p => Ioo p.1 p.2) ∧
      O = ⋃ p ∈ S, Ioo p.1 p.2 ∧
      ∀ p ∈ S, p.1 ∉ O ∧ p.2 ∉ O ∧ c ≤ p.1 ∧ p.2 ≤ d := by
  classical
  -- the endpoint-pair of the component of a point
  set e : ℝ → ℝ × ℝ := fun x =>
    (sInf (connectedComponentIn O x), sSup (connectedComponentIn O x)) with he
  set S : Set (ℝ × ℝ) := e '' O with hS
  -- every pair in `S` has the properties of `connectedComponentIn_eq_Ioo`, and its `Ioo` is a
  -- component of `O`
  have hpair : ∀ x ∈ O, connectedComponentIn O x = Ioo (e x).1 (e x).2 ∧
      (e x).1 ∉ O ∧ (e x).2 ∉ O ∧ c ≤ (e x).1 ∧ (e x).2 ≤ d := fun x hx =>
    connectedComponentIn_eq_Ioo hO hOsub hx
  -- membership of a point in the `Ioo` of its own component
  have hmemself : ∀ x ∈ O, x ∈ Ioo (e x).1 (e x).2 := fun x hx =>
    (hpair x hx).1 ▸ mem_connectedComponentIn hx
  -- the union equals `O`
  have hunion : O = ⋃ p ∈ S, Ioo p.1 p.2 := by
    apply Subset.antisymm
    · intro x hx
      exact mem_iUnion₂.mpr ⟨e x, mem_image_of_mem e hx, hmemself x hx⟩
    · rintro x hx
      obtain ⟨p, ⟨y, hyO, rfl⟩, hxp⟩ := mem_iUnion₂.mp hx
      have : x ∈ connectedComponentIn O y := (hpair y hyO).1 ▸ hxp
      exact connectedComponentIn_subset O y this
  -- pairwise disjointness: distinct pairs come from distinct components
  have hdisj : S.PairwiseDisjoint (fun p => Ioo p.1 p.2) := by
    rintro p ⟨x, hxO, rfl⟩ q ⟨y, hyO, rfl⟩ hpq
    rw [Function.onFun, ← (hpair x hxO).1, ← (hpair y hyO).1]
    by_contra hnd
    obtain ⟨z, hz⟩ := Set.not_disjoint_iff.mp hnd
    have hxy : connectedComponentIn O x = connectedComponentIn O y := by
      rw [connectedComponentIn_eq hz.1, connectedComponentIn_eq hz.2]
    exact hpq (by simp only [he]; rw [hxy])
  -- countability: the `Ioo p.1 p.2` are nonempty open pairwise-disjoint sets
  have hcount : S.Countable := by
    refine (hdisj.countable_of_nonempty_interior ?_)
    rintro p ⟨x, hxO, rfl⟩
    rw [interior_Ioo]
    exact ⟨x, hmemself x hxO⟩
  exact ⟨S, hcount, hdisj, hunion, fun p ⟨x, hxO, hpe⟩ =>
    hpe ▸ ⟨(hpair x hxO).2.1, (hpair x hxO).2.2.1, (hpair x hxO).2.2.2.1,
      (hpair x hxO).2.2.2.2⟩⟩

/-- **Summed per-arc integration-by-parts identity over a bounded open set.** Let
`O = ⋃ p ∈ S, Ioo p.1 p.2` be the countable pairwise-disjoint open-interval decomposition of a
bounded open set. If on each arc `f`, `g`, `g'` satisfy the hypotheses of the single-arc integration
by parts (continuity, `deriv f = -g`, `HasDerivAt g g'`, `(deriv f)²` integrable, `g` integrable,
`f` vanishing at both endpoints), and `f · g'` and `g²` are integrable on all of `O`, then the
integral of `f · g'` over `O` equals the integral of `g²` over `O`: sum the exact per-arc
identities over the countable disjoint union. -/
theorem setIntegral_mul_deriv_eq_setIntegral_sq_of_arcs {f g g' : ℝ → ℝ} {O : Set ℝ}
    {S : Set (ℝ × ℝ)} (hcount : S.Countable)
    (hdisj : S.PairwiseDisjoint (fun p => Ioo p.1 p.2))
    (hunion : O = ⋃ p ∈ S, Ioo p.1 p.2)
    (harc : ∀ p ∈ S, p.1 < p.2 →
      (∀ t ∈ Ioo p.1 p.2, HasDerivAt f (deriv f t) t) ∧
      (∀ t ∈ Ioo p.1 p.2, deriv f t = -g t) ∧
      (∀ t ∈ Ioo p.1 p.2, HasDerivAt g (g' t) t) ∧
      IntegrableOn (fun t => (deriv f t) ^ 2) (Ioo p.1 p.2) ∧
      ContinuousOn f (Icc p.1 p.2) ∧
      IntegrableOn g (Ioo p.1 p.2) ∧ IntegrableOn g' (Ioo p.1 p.2) ∧
      f p.1 = 0 ∧ f p.2 = 0)
    (hfg'O : IntegrableOn (fun t => f t * g' t) O) (hg2O : IntegrableOn (fun t => (g t) ^ 2) O) :
    ∫ t in O, f t * g' t = ∫ t in O, (g t) ^ 2 := by
  classical
  have _ := hcount.to_subtype
  -- reindex the union over the countable subtype `↥S`
  set s : S → Set ℝ := fun p => Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hs
  have hsu : O = ⋃ p : S, s p := by rw [hunion, hs, iUnion_subtype]
  have hsmeas : ∀ p : S, MeasurableSet (s p) := fun _ => measurableSet_Ioo
  have hsdisj : Pairwise (Function.onFun Disjoint s) := by
    intro p q hpq
    exact hdisj p.2 q.2 (fun h => hpq (Subtype.ext h))
  -- per-arc identity: interval integrals equal the two sides of the single-arc IBP
  have hper : ∀ p : S, ∫ t in s p, f t * g' t = ∫ t in s p, (g t) ^ 2 := by
    intro p
    rcases lt_or_ge (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hlt | hle
    · obtain ⟨hderiv, hfg, hg, hf2, hcont, hgint, hg'int, ha0, hb0⟩ := harc p p.2 hlt
      have hid := integral_mul_deriv_eq_integral_sq_of_endpoints_zero hlt hderiv hfg hg hf2
        hcont hgint hg'int ha0 hb0
      rw [hs] at *
      rw [intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo] at hid
      exact hid
    · -- degenerate arc: both sides vanish
      rw [hs]
      simp only [Ioo_eq_empty (not_lt.mpr hle), setIntegral_empty]
  -- sum the per-arc identities over the countable disjoint union
  rw [hsu, integral_iUnion hsmeas hsdisj (hsu ▸ hfg'O),
    integral_iUnion hsmeas hsdisj (hsu ▸ hg2O)]
  exact tsum_congr hper

/-- **Summed per-slice flux identity for a harmonic potential on an open set.** Fix a log-radius
`ξ`. Let `O = {θ ∈ Ioo (-π) π | e^{ξ+iθ} ∈ U}` be the angular slice of an open set `U`, on which the
harmonic potential `u` vanishes off the slice and is continuous on the closed interval. If the slice
squared gradient and the slice radial-derivative integrand are integrable on `O`, then the angle
integral over the slice of `u(e^{ξ+iθ}) · Re (deriv (expGrad u))` equals the integral of
`(Im (expGrad u))²`: decompose `O` into its countable disjoint open arcs (each with endpoints
escaping the slice, where `u` vanishes) and sum the exact per-arc integration-by-parts
identities. -/
theorem setIntegral_slice_uexp_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcont : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc (-π) π))
    (hvanish : ∀ θ : ℝ,
      θ ∉ {θ' : ℝ | θ' ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = 0)
    (hsliceInt : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U})
    (hradInt : IntegrableOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U}) :
    ∫ θ in {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U},
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U},
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  classical
  set O : Set ℝ :=
    {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U} with hO
  -- the slice is open (preimage of `U` under the continuous angle map, meet the open interval)
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hOopen : IsOpen O := by
    have : O = Ioo (-π) π ∩ (fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ⁻¹' U := by
      ext θ; simp only [hO, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]; exact isOpen_Ioo.inter (hU.preimage hcontmap)
  have hOsub : O ⊆ Ioo (-π) π := fun θ hθ => hθ.1
  obtain ⟨S, hcount, hdisj, hunion, hSend⟩ := isOpen_eq_iUnion_Ioo hOopen hOsub
  have _ := hcount.to_subtype
  -- abbreviations for the two slice integrands
  set F : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
      * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 with hG
  -- reindex the disjoint union over the countable subtype `↥S`
  set s : S → Set ℝ := fun p => Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hs
  have hsu : O = ⋃ p : S, s p := by rw [hunion, hs, iUnion_subtype]
  have hsmeas : ∀ p : S, MeasurableSet (s p) := fun _ => measurableSet_Ioo
  have hsdisj : Pairwise (Function.onFun Disjoint s) := fun p q hpq =>
    hdisj p.2 q.2 (fun h => hpq (Subtype.ext h))
  -- points of an arc lie in the slice, hence map into `U`
  have harcU : ∀ p : S, ∀ θ ∈ s p, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro p θ hθ
    have : θ ∈ O := hsu ▸ mem_iUnion.mpr ⟨p, hθ⟩
    exact this.2
  -- endpoints escape the slice, so `u` vanishes there
  have harcEnd : ∀ p : S, u (Complex.exp ((ξ : ℂ) + ((p : ℝ × ℝ).1 : ℂ) * Complex.I)) = 0 ∧
      u (Complex.exp ((ξ : ℂ) + ((p : ℝ × ℝ).2 : ℂ) * Complex.I)) = 0 := fun p =>
    ⟨hvanish _ (hSend p p.2).1, hvanish _ (hSend p p.2).2.1⟩
  -- each arc is contained in `[-π, π]`, giving the closed-arc continuity
  have harcIcc : ∀ p : S, Icc (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 ⊆ Icc (-π) π := by
    intro p
    obtain ⟨_, _, hlo, hhi⟩ := hSend p p.2
    exact Icc_subset_Icc hlo hhi
  have harcmem : ∀ p : S, ∀ θ ∈ s p, θ ∈ O := fun p θ hθ => hsu ▸ mem_iUnion.mpr ⟨p, hθ⟩
  -- per-arc identity: the set integral over each arc, of both integrands, agree
  have hper : ∀ p : S, ∫ θ in s p, F θ = ∫ θ in s p, G θ := by
    intro p
    rcases lt_or_ge (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hlt | hle
    · have hid := integral_uexp_re_deriv_expGrad_arc hU hlt hu (fun θ hθ => harcU p θ hθ)
        (hcont.mono (harcIcc p)) (hsliceInt.mono_set (harcmem p)) (hradInt.mono_set (harcmem p))
        (harcEnd p).1 (harcEnd p).2
      rw [hF, hG, hs]
      rw [intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo] at hid
      exact hid
    · rw [hs]; simp only [Ioo_eq_empty (not_lt.mpr hle), setIntegral_empty]
  -- `u ∘ exp` is continuous on the slice (as a subset of the compact `[-π, π]`)
  have hcontO : ContinuousOn (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) O :=
    hcont.mono (hOsub.trans Ioo_subset_Icc_self)
  have hOmeas : MeasurableSet O := hOopen.measurableSet
  -- integrability of `F` on `O`: `u ∘ exp` bounded on the compact `[-π, π]`, `rad` integrable
  have hFint : IntegrableOn F O := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine Integrable.mono' (hradInt.norm.const_mul C) ?_ ?_
    · exact (hcontO.aestronglyMeasurable hOmeas).mul hradInt.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hOmeas] with θ hθ
      rw [hF, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hC _ (Ioo_subset_Icc_self (hOsub hθ))) (norm_nonneg _)
  -- `θ ↦ expGrad u (ξ+θI)` restricted to the angular slice is continuous
  have hexpGradO : ContinuousOn
      (fun θ : ℝ => expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) O := by
    intro θ hθ
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hθ.2
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    have := ContinuousAt.comp (g := expGrad u)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hdC.continuousAt hinner
    exact this.continuousWithinAt
  -- integrability of `G = (Im expGrad)²` on `O`: dominated by `normSq (expGrad u)`
  have hGint : IntegrableOn G O := by
    refine Integrable.mono' hsliceInt ?_ ?_
    · exact ((Complex.continuous_im.comp_continuousOn hexpGradO).pow 2).aestronglyMeasurable hOmeas
    · filter_upwards [ae_restrict_mem hOmeas] with θ _
      rw [hG, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.normSq_apply]
      nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
  -- sum the per-arc identities over the countable disjoint union
  rw [hsu, integral_iUnion hsmeas hsdisj (hsu ▸ hFint),
    integral_iUnion hsmeas hsdisj (hsu ▸ hGint)]
  exact tsum_congr hper

/-! ### The `ξ`-Fubini selector for slice integrability -/

/-- **Joint measurability of the log-polar squared gradient.** The map
`(ξ, θ) ↦ normSq (expGrad u (ξ + θ·I))` is measurable: `expGrad u` is a product of the measurable
`gradC u ∘ exp` and the continuous `exp`, and `normSq` is continuous. -/
theorem measurable_normSq_expGrad_logPolar (u : ℂ → ℝ) :
    Measurable fun p : ℝ × ℝ =>
      Complex.normSq (expGrad u ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
  have hw : Measurable fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    fun_prop
  have hexp : Measurable fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp hw
  have hgrad : Measurable fun p : ℝ × ℝ =>
      gradC u (Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) :=
    (measurable_gradC u).comp hexp
  have hprod : Measurable fun p : ℝ × ℝ => expGrad u ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    simp only [expGrad]
    exact hgrad.mul hexp
  exact Complex.continuous_normSq.measurable.comp hprod

/-- **The `ξ`-Fubini selector.** If the iterated log-polar integral of the energy density
`normSq (expGrad u)` over the box `Ioo ξ₁ ξ₂ ×ˢ Ioo (-π) π` is finite, then for a.e. log-radius
`ξ ∈ Ioo ξ₁ ξ₂` the angular slice `θ ↦ normSq (expGrad u (ξ + θ·I))` is integrable on `(-π, π)`:
the finiteness of the outer integral forces the inner slice integral to be finite a.e. by Markov,
and finiteness of `∫⁻ ofReal` of a nonnegative function is integrability. -/
theorem ae_integrableOn_slice_normSq_expGrad {u : ℂ → ℝ} {ξ₁ ξ₂ : ℝ}
    (hDfin : (∫⁻ ξ in Ioo ξ₁ ξ₂, ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))) ≠ ⊤) :
    ∀ᵐ ξ : ℝ ∂(volume.restrict (Ioo ξ₁ ξ₂)),
      IntegrableOn (fun θ : ℝ =>
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo (-π) π) := by
  have hmeasD : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (Complex.normSq (expGrad u ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) :=
    ENNReal.measurable_ofReal.comp (measurable_normSq_expGrad_logPolar u)
  -- the inner slice lintegral is measurable in `ξ`
  have hinner : Measurable fun ξ : ℝ => ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :=
    Measurable.lintegral_prod_right (ν := volume.restrict (Ioo (-π) π)) hmeasD
  -- Markov: the a.e.-finiteness of the outer integral gives a.e.-finiteness of the inner slice
  have hae := ae_lt_top hinner hDfin
  filter_upwards [hae] with ξ hξ
  -- finiteness of `∫⁻ ofReal` of a nonnegative slice function is slice integrability
  refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hξ.ne
  · exact ((measurable_normSq_expGrad_logPolar u).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun θ => Complex.normSq_nonneg _)

/-! ### The rough-ring flux -/

/-- The **rough-ring flux** of a potential `u` on an open set `U ⊆ ball 0 1` at log-radius `ξ`:
the angle integral over the full circle `(−π, π)`, restricted by the indicator of the angular
set `{θ | e^{ξ+iθ} ∈ U}`, of the potential against its scale-invariant radial derivative
`u(e^{ξ+iθ}) · (∇u(e^{ξ+iθ}) · e^{ξ+iθ})`.  When the whole circle lies in `U` the
indicator is `1` and the rough flux reduces to `RiemannDynamics.ringFlux`. -/
noncomputable def roughFlux (u : ℂ → ℝ) (U : Set ℂ) (ξ : ℝ) : ℝ :=
  ∫ θ in Ioo (-π) π,
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator
      (fun θ' : ℝ => u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
        * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
            (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ

/-- **Collar agreement of the rough flux.** If every point `e^{ξ+iθ}` of the circle of radius
`e^ξ` lies in `U`, the indicator in the rough flux is identically `1`, so the rough flux equals
the round-annulus ring flux `ringFlux u ξ`. -/
theorem roughFlux_eq_ringFlux {u : ℂ → ℝ} {U : Set ℂ} {ξ : ℝ}
    (hU : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    roughFlux u U ξ = ringFlux u ξ := by
  unfold roughFlux ringFlux
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
    Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hU θ)]

/-- **Collar agreement on a round annulus.** If the circle of radius `e^ξ` lies inside the round
collar `{r₀ < |z| < 1}` — that is, `log r₀ < ξ < 0` — then the rough flux over that collar
equals the ring flux `ringFlux u ξ`. -/
theorem roughFlux_eq_ringFlux_on_collar {u : ℂ → ℝ} {r₀ ξ : ℝ} (h0 : 0 < r₀)
    (hξ1 : Real.log r₀ < ξ) (hξ2 : ξ < 0) :
    roughFlux u (RoundAnnulus 0 r₀ 1) ξ = ringFlux u ξ :=
  roughFlux_eq_ringFlux (fun θ =>
    exp_mem_roundAnnulus h0 (by rw [re_logPolar]; exact hξ1) (by rw [re_logPolar]; exact hξ2))

/-- The **angular slice** of an open set `U` at log-radius `ξ`: the angles `θ ∈ (−π, π)` whose
log-polar image `e^{ξ+iθ}` lies in `U`.  It is the set integrated over by the flux–energy exchange
at that radius. -/
def angularSlice (U : Set ℂ) (ξ : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U}

/-- The **single-slice energy** of `u` over the angular slice `U ∩ C_{e^ξ}`: the angle integral of
the squared log-polar gradient `|expGrad u|²` over the slice `angularSlice U ξ`.  This is the
exchange target `d/dξ (roughFlux u U ξ)`. -/
noncomputable def sliceEnergyU (u : ℂ → ℝ) (U : Set ℂ) (ξ : ℝ) : ℝ :=
  ∫ θ in angularSlice U ξ, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- **The angular slice is open.** For `U` open, the slice `angularSlice U ξ` is the intersection of
the open interval `(−π, π)` with the preimage of `U` under the continuous angle map. -/
theorem isOpen_angularSlice {U : Set ℂ} (hU : IsOpen U) (ξ : ℝ) :
    IsOpen (angularSlice U ξ) := by
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hrw : angularSlice U ξ
      = Ioo (-π) π ∩ (fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ⁻¹' U := by
    ext θ; simp only [angularSlice, mem_setOf_eq, mem_inter_iff, mem_preimage]
  rw [hrw]; exact isOpen_Ioo.inter (hU.preimage hcontmap)

/-- The angular slice is contained in `(−π, π)`, hence measurable. -/
theorem angularSlice_subset (U : Set ℂ) (ξ : ℝ) : angularSlice U ξ ⊆ Ioo (-π) π :=
  fun _ hθ => hθ.1

/-- **The rough flux is the slice integral of `u · Re (expGrad u)`.** Rewriting the Fréchet
derivative `fderiv ℝ u (e^w) (e^w) = Re (gradC u (e^w) · e^w) = Re (expGrad u w)` turns the
indicator integral defining `roughFlux` into the set integral over the angular slice. -/
theorem roughFlux_eq_setIntegral_slice {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (ξ : ℝ) :
    roughFlux u U ξ = ∫ θ in angularSlice U ξ,
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hπ := Real.pi_pos
  unfold roughFlux
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hmeasset : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} :=
    hcontmap.measurable (hU.measurableSet)
  -- first rewrite the Fréchet derivative factor to `Re (expGrad u)` inside the indicator
  rw [show (∫ θ in Ioo (-π) π,
        {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator
          (fun θ' : ℝ => u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
            * fderiv ℝ u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
                (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ)
      = ∫ θ in Ioo (-π) π,
        {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator
          (fun θ' : ℝ => u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)).re) θ from by
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    unfold Set.indicator
    split_ifs with h
    · simp only []; rw [fderiv_eq_re_gradC_mul]; rfl
    · rfl]
  -- then convert the indicator integral over `(−π, π)` to the set integral over the slice
  rw [setIntegral_indicator hmeasset]
  refine setIntegral_congr_set ?_
  rw [angularSlice]
  refine (ae_eq_set.mpr ⟨?_, ?_⟩) <;>
    · refine measure_mono_null (fun θ hθ => ?_) (measure_empty)
      simp only [mem_diff, mem_inter_iff, mem_setOf_eq] at hθ
      tauto

/-! ### Fixed-window flux FTC for a general open set

For a general open `U` and a window `[a, b]` whose log-polar strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}`
maps into `U` under `exp`, the truncated flux `truncFlux u a b` obeys the flux–energy exchange
`d/dξ (truncFlux u a b) = boundary + ∫ |expGrad u|²` exactly (the fixed-domain heart of the
exchange), mirroring `RiemannDynamics.hasDerivAt_truncFlux` with the Grötzsch ring replaced by `U`.
-/

/-- Every point of the strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}` has its exponential in `U`, provided
the whole closed box of log-polar parameters maps into `U`. -/
theorem stripBox_exp_mem_of_mapsTo {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) {w : ℂ}
    (hw : w ∈ stripBox ξ₁ ξ₂ a b) :
    Complex.exp w ∈ U := by
  obtain ⟨hre1, hre2, him1, him2⟩ := hw
  have hwrepr : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hwrepr]
  exact hmaps w.re ⟨hre1.le, hre2.le⟩ w.im ⟨him1, him2⟩

/-- The pullback `w ↦ u(e^w)` is continuous on a strip box mapping into `U`. -/
theorem continuousOn_uexp_stripBox_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (fun w => u (Complex.exp w)) (stripBox ξ₁ ξ₂ a b) := by
  intro w hw
  have hmem := stripBox_exp_mem_of_mapsTo hmaps hw
  have hc : ContinuousAt u (Complex.exp w) := (hu _ hmem).1.continuousAt
  exact (hc.comp Complex.continuous_exp.continuousAt).continuousWithinAt

/-- `expGrad u` is continuous on a strip box mapping into the open set `U`. -/
theorem continuousOn_expGrad_stripBox_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (expGrad u) (stripBox ξ₁ ξ₂ a b) := fun _w hw =>
  (expGrad_differentiableAt_open hU hu
    (stripBox_exp_mem_of_mapsTo hmaps hw)).continuousAt.continuousWithinAt

/-- The derivative of `expGrad u` is continuous on a strip box whose *interior* maps into the open
set `U`: on the open log-strip `expGrad u` is holomorphic hence analytic, so its derivative is
continuous there.  The interior-mapping hypothesis is packaged as membership of an open strip box in
the preimage. -/
theorem continuousOn_deriv_expGrad_stripBox_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (deriv (expGrad u)) (stripBox ξ₁ ξ₂ a b) := by
  -- `expGrad u` is holomorphic on the open preimage of `U`, so its derivative is continuous there
  set O : Set ℂ := Complex.exp ⁻¹' U with hO
  have hOopen : IsOpen O := hU.preimage Complex.continuous_exp
  have hdiff : DifferentiableOn ℂ (expGrad u) O := fun w hw =>
    (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
  have hanalytic := hdiff.analyticOnNhd hOopen
  have hderivCont : ContinuousOn (deriv (expGrad u)) O :=
    (hanalytic.deriv_of_isOpen hOopen).continuousOn
  refine hderivCont.mono (fun w hw => ?_)
  exact stripBox_exp_mem_of_mapsTo hmaps hw

/-- **Angular integration by parts with boundary terms on a window mapping into `U`.** For `u`
harmonic on the open set `U` and a closed window `[a, b]` whose slice at log-radius `ξ` maps into
`U`, the angle integral of `u · Re (deriv (expGrad u))` equals the boundary term
`[u · Im (expGrad u)]_a^b` plus the integral of `(Im (expGrad u))²`.  Unlike the endpoint-vanishing
per-arc identity, the boundary term is kept explicit — this is the form consumed by the fixed-window
flux FTC. -/
theorem integral_uexp_re_deriv_expGrad_window_Icc {u : ℂ → ℝ} {U : Set ℂ} {ξ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ θ ∈ Icc a b, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ∫ θ in a..b, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  -- differentiability of `u` and holomorphy of `expGrad u` at each window point
  have hdiffR : ∀ θ ∈ Icc a b,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ hθ =>
    differentiableAt_of_harmonicOnNhd hu (hmaps θ hθ)
  have hdiffC : ∀ θ ∈ Icc a b,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ hθ =>
    expGrad_differentiableAt_open hU hu (hmaps θ hθ)
  -- continuity of the three slice factors on the window (from differentiability)
  have hcont_f : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun θ hθ => ((hasDerivAt_uexp_angular (hdiffR θ hθ)).continuousAt).continuousWithinAt
  have hcont_g : ContinuousOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) (uIcc a b) := by
    rw [uIcc_of_le hab]
    refine fun θ hθ => ?_
    have hD := hasDerivAt_expGrad_angular (hdiffC θ hθ)
    exact ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD).continuousAt).continuousWithinAt
  have hcont_g' : ContinuousOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (uIcc a b) := by
    -- `deriv (expGrad u)` is continuous on the open preimage of `U`, restricted to the slice
    set O : Set ℂ := Complex.exp ⁻¹' U with hO
    have hOopen : IsOpen O := hU.preimage Complex.continuous_exp
    have hdiff : DifferentiableOn ℂ (expGrad u) O := fun w hw =>
      (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
    have hderivCont : ContinuousOn (deriv (expGrad u)) O :=
      ((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn
    rw [uIcc_of_le hab]
    refine fun θ hθ => ?_
    have hmem : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ O := hmaps θ hθ
    have hcont : ContinuousAt (fun w : ℂ => (deriv (expGrad u) w).re)
        ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      (Complex.continuous_re.comp_continuousOn hderivCont).continuousAt (hOopen.mem_nhds hmem)
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    exact (ContinuousAt.comp (g := fun w : ℂ => (deriv (expGrad u) w).re)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hcont hinner).continuousWithinAt
  -- pointwise angular derivatives on the open window
  have hf' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)))
        (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact hasDerivAt_uexp_angular (hdiffR θ (Ioo_subset_Icc_self hθ))
  have hg' : ∀ θ ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).im)
        ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ := by
    intro θ hθ
    rw [min_eq_left hab, max_eq_right hab] at hθ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ (Ioo_subset_Icc_self hθ))
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [Function.comp, Complex.mul_im] using hcomp
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f hcont_g hf' hg' hcont_g.neg.intervalIntegrable hcont_g'.intervalIntegrable
  have halg : ∫ θ in a..b, (-(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im)
      * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im
      = - ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [hIBP, halg]; ring

/-- **Fixed-window flux FTC derivative for a general open set.** For `u` harmonic on the open set
`U` and a window `[a, b]` whose *closed* strip box `{ξ₁ < Re < ξ₂, a ≤ Im ≤ b}` maps into `U` under
`exp`, the truncated flux `truncFlux u a b` has, at every interior log-radius `ξ ∈ (ξ₁, ξ₂)`,
derivative the angular boundary term plus the window integral of `|expGrad u|²`.  Differentiation
under the integral sign gives `(Re expGrad)² + u · Re (deriv expGrad)`, and the angular integration
by parts converts the second term into the boundary term plus `(Im expGrad)²`; adding
`(Re expGrad)² + (Im expGrad)² = |expGrad|²` gives the window slice energy.  This mirrors
`RiemannDynamics.hasDerivAt_truncFlux` with the Grötzsch ring replaced by `U`. -/
theorem hasDerivAt_truncFlux_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hξ1 : ξ₁ < ξ) (hξ2 : ξ < ξ₂) :
    HasDerivAt (truncFlux u a b)
      (u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) ξ := by
  -- continuity of the integrand `G` and its radial derivative `G'` on the strip box
  have hUexp := continuousOn_uexp_stripBox_of_mapsTo hu hmaps
  have hEG := continuousOn_expGrad_stripBox_of_mapsTo hU hu hmaps
  have hDEG := continuousOn_deriv_expGrad_stripBox_of_mapsTo hU hu hmaps
  have hGcont : ContinuousOn (fun w => u (Complex.exp w) * (expGrad u w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    hUexp.mul (Complex.continuous_re.comp_continuousOn hEG)
  have hG'cont : ContinuousOn
      (fun w => (expGrad u w).re ^ 2 + u (Complex.exp w) * (deriv (expGrad u) w).re)
      (stripBox ξ₁ ξ₂ a b) :=
    ((Complex.continuous_re.comp_continuousOn hEG).pow 2).add
      (hUexp.mul (Complex.continuous_re.comp_continuousOn hDEG))
  -- radial product rule at each interior strip-box point
  have hd : ∀ x θ : ℝ, ξ₁ < x → x < ξ₂ → a < θ → θ < b →
      HasDerivAt (fun y : ℝ => u (Complex.exp ((y : ℂ) + (θ : ℂ) * Complex.I))
          * (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))
            * (deriv (expGrad u) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
    intro x θ hx1 hx2 hθ1 hθ2
    have hmem : Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U :=
      hmaps x ⟨hx1.le, hx2.le⟩ θ ⟨hθ1.le, hθ2.le⟩
    have hu' := hasDerivAt_uexp_radial (differentiableAt_of_harmonicOnNhd hu hmem)
    have hD := hasDerivAt_expGrad_radial (expGrad_differentiableAt_open hU hu hmem)
    have hDre : HasDerivAt (fun y : ℝ => (expGrad u ((y : ℂ) + (θ : ℂ) * Complex.I)).re)
        ((deriv (expGrad u) ((x : ℂ) + (θ : ℂ) * Complex.I)).re) x := by
      have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hD
      simpa [Function.comp] using hcomp
    exact (hu'.mul hDre).congr_deriv (by ring)
  have hDUI := hasDerivAt_integral_stripBox hab hGcont hG'cont hd hξ1 hξ2
  -- integrability of the three interior integrands on `(a, b)` via real-valued slice continuity
  have hsliceEGre : ContinuousOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox
      (Complex.continuous_re.comp_continuousOn hEG) hξ1 hξ2
  have hsliceEGim : ContinuousOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox
      (Complex.continuous_im.comp_continuousOn hEG) hξ1 hξ2
  have hsliceU : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox hUexp hξ1 hξ2
  have hsliceDEGre : ContinuousOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Icc a b) :=
    continuousOn_slice_of_continuousOn_stripBox
      (Complex.continuous_re.comp_continuousOn hDEG) hξ1 hξ2
  have hint1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2) (Ioo a b) :=
    ((hsliceEGre.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b) :=
    ((hsliceU.mul hsliceDEGre).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hint3 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) (Ioo a b) :=
    ((hsliceEGim.pow 2).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  -- convert the DUI derivative value via the window integration by parts
  have hval : (∫ θ in Ioo a b,
      ((expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re))
      = u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
          * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
        - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
        + ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    rw [integral_add hint1 hint2]
    have hIBP := integral_uexp_re_deriv_expGrad_window_Icc hU hu hab
      (fun θ hθ => hmaps ξ ⟨hξ1.le, hξ2.le⟩ θ hθ)
    have hIBP' : (∫ θ in Ioo a b, u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        = u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
            * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
          - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
              * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
          + ∫ θ in Ioo a b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
      rw [integral_Ioo_eq_intervalIntegral hab, hIBP, integral_Ioo_eq_intervalIntegral hab]
    rw [hIBP']
    have hnormeq : (∫ θ in Ioo a b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2)
          + ∫ θ in Ioo a b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        = ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [← integral_add hint1 hint3]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [Complex.normSq_apply]; ring
    linarith [hnormeq]
  rw [hval] at hDUI
  exact hDUI

/-- The derivative value of the fixed-window flux for a general open set: the angular boundary term
of the integration by parts plus the window integral of `|expGrad u|²`. -/
noncomputable def truncFluxDerivU (u : ℂ → ℝ) (a b ξ : ℝ) : ℝ :=
  u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I))
      * (expGrad u ((ξ : ℂ) + (b : ℂ) * Complex.I)).im
    - u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (a : ℂ) * Complex.I)).im
    + ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))

/-- **Continuity of the fixed-window flux derivative value.** Under the strip-box mapping
hypothesis, the derivative value `truncFluxDerivU u a b` is continuous on the open log-radius
interval `(ξ₁, ξ₂)`: the two boundary factors are continuous in `ξ` (fixed angle in `U`), and the
window integral of `|expGrad u|²` is continuous by dominated convergence with a strip-box bound. -/
theorem continuousOn_truncFluxDerivU {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    ContinuousOn (truncFluxDerivU u a b) (Ioo ξ₁ ξ₂) := by
  have hUexp := continuousOn_uexp_stripBox_of_mapsTo hu hmaps
  have hEG := continuousOn_expGrad_stripBox_of_mapsTo hU hu hmaps
  -- the boundary factors `ξ ↦ u(e^{ξ+ci}) · Im (expGrad u (ξ+ci))` are continuous on `(ξ₁, ξ₂)`
  have hbdry : ∀ c : ℝ, c ∈ Icc a b →
      ContinuousOn (fun ξ : ℝ => u (Complex.exp ((ξ : ℂ) + (c : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (c : ℂ) * Complex.I)).im) (Ioo ξ₁ ξ₂) := by
    intro c hc ξ hξ
    have hmem : Complex.exp ((ξ : ℂ) + (c : ℂ) * Complex.I) ∈ U :=
      hmaps ξ (Ioo_subset_Icc_self hξ) c hc
    have hcu : ContinuousAt (fun ξ : ℝ => u (Complex.exp ((ξ : ℂ) + (c : ℂ) * Complex.I))) ξ :=
      (hasDerivAt_uexp_radial (differentiableAt_of_harmonicOnNhd hu hmem)).continuousAt
    have hcg : ContinuousAt (fun ξ : ℝ => (expGrad u ((ξ : ℂ) + (c : ℂ) * Complex.I)).im) ξ :=
      Complex.continuous_im.continuousAt.comp
        (hasDerivAt_expGrad_radial (expGrad_differentiableAt_open hU hu hmem)).continuousAt
    exact (hcu.mul hcg).continuousWithinAt
  -- the window integral of `|expGrad u|²` is continuous on `(ξ₁, ξ₂)`
  have hint : ContinuousOn (fun ξ : ℝ =>
      ∫ θ in Ioo a b, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (Ioo ξ₁ ξ₂) := by
    intro ξ₀ hξ₀
    obtain ⟨δ, hδpos, hδsub⟩ := exists_closed_slab hξ₀.1 hξ₀.2
    have hcont : ContinuousOn (fun w => Complex.normSq (expGrad u w))
        (stripBox ξ₁ ξ₂ a b) :=
      Complex.continuous_normSq.comp_continuousOn hEG
    obtain ⟨C, hC⟩ := exists_bound_on_stripBox hcont hδsub
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_of_dominated (bound := fun _ => C)
    · filter_upwards [Ioo_mem_nhds hξ₀.1 hξ₀.2] with ξ hξ
      exact ((continuousOn_slice_of_continuousOn_stripBox hcont hξ.1 hξ.2).mono
        Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [Metric.ball_mem_nhds ξ₀ hδpos] with ξ hξ
      have hξ' : ξ ∈ Icc (ξ₀ - δ) (ξ₀ + δ) := by
        rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hξ
        exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      exact hC ξ hξ' θ (Ioo_subset_Icc_self hθ)
    · exact integrableOn_const (hs := measure_Ioo_lt_top.ne)
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => ?_)
      have hmem : Complex.exp ((ξ₀ : ℂ) + (θ : ℂ) * Complex.I) ∈ U :=
        hmaps ξ₀ (Ioo_subset_Icc_self hξ₀) θ (Ioo_subset_Icc_self hθ)
      exact Complex.continuous_normSq.continuousAt.comp
        (hasDerivAt_expGrad_radial (expGrad_differentiableAt_open hU hu hmem)).continuousAt
  exact ((hbdry b (right_mem_Icc.mpr hab)).sub (hbdry a (left_mem_Icc.mpr hab))).add hint

/-- **Fundamental theorem of calculus for the fixed-window flux (general open set).** Under the
strip-box mapping hypothesis, the increment of the truncated flux over `[ξ₁', ξ₂'] ⊆ (ξ₁, ξ₂)` is
the integral of its derivative value. -/
theorem truncFlux_sub_eq_integral_of_mapsTo {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ a b ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hab : a ≤ b)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc a b,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (h1 : ξ₁ < ζ₁) (h12 : ζ₁ ≤ ζ₂) (h2 : ζ₂ < ξ₂) :
    truncFlux u a b ζ₂ - truncFlux u a b ζ₁ = ∫ ξ in ζ₁..ζ₂, truncFluxDerivU u a b ξ := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_).symm
  · rw [uIcc_of_le h12] at hx
    exact hasDerivAt_truncFlux_of_mapsTo hU hu hab hmaps
      (lt_of_lt_of_le h1 hx.1) (lt_of_le_of_lt hx.2 h2)
  · refine ((continuousOn_truncFluxDerivU hU hu hab hmaps).mono ?_).intervalIntegrable
    rw [uIcc_of_le h12]
    exact fun x hx => ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h2⟩

/-! ### The full-circle collar flux–energy identity for a general open set

When the *whole* circle at log-radius `ξ` lies in `U`, the rough flux is the full-window flux
`truncFlux u (−π) π ξ` and its FTC derivative is the whole-circle slice energy — the `±π` boundary
terms cancel by `2π`-periodicity.  This yields an exact flux–energy identity on any full-circle
collar for a general open `U`, without needing the varying-domain radial FTC. -/

/-- On a full-circle collar (`exp(ξ+θi) ∈ U` for all `θ`), the rough flux equals the full-window
flux `truncFlux u (−π) π ξ`. -/
theorem roughFlux_eq_truncFlux_full {u : ℂ → ℝ} {U : Set ℂ} {ξ : ℝ} (hU : IsOpen U)
    (hfull : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U) :
    roughFlux u U ξ = truncFlux u (-π) π ξ := by
  rw [roughFlux_eq_setIntegral_slice hU, truncFlux]
  refine setIntegral_congr_set ?_
  have hsub : angularSlice U ξ = Ioo (-π) π := by
    ext θ; simp only [angularSlice, mem_setOf_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, hfull θ⟩⟩
  rw [hsub]

/-- On a full-circle collar, the fixed-window derivative value `truncFluxDerivU u (−π) π ξ` equals
the whole-circle slice energy: the `±π` boundary terms cancel by `2π`-periodicity of the log-polar
pullback and of `expGrad u`. -/
theorem truncFluxDerivU_full_eq_sliceEnergy {u : ℂ → ℝ} (ξ : ℝ) :
    truncFluxDerivU u (-π) π ξ
      = ∫ θ in Ioo (-π) π, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
  unfold truncFluxDerivU
  have hexp : Complex.exp ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    rw [show ((ξ : ℂ) + (π : ℂ) * Complex.I)
        = ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  have heg : expGrad u ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    simp only [expGrad, hexp]
  rw [show ((π : ℝ) : ℂ) = ((π : ℝ) : ℂ) from rfl, hexp, heg]
  push_cast
  ring

/-- **Full-circle collar flux–energy identity.** For `u` harmonic on the open set `U`, if the whole
strip box `{ξ₁ < Re < ξ₂, −π ≤ Im ≤ π}` maps into `U`, then the increment of the rough flux over
`[ζ₁, ζ₂] ⊆ (ξ₁, ξ₂)` equals the Dirichlet energy of the round sub-annulus
`{e^{ζ₁} < |z| < e^{ζ₂}}`.  The `±π` boundary terms cancel by periodicity, so the fixed-window FTC
integrates the whole-circle slice energy, which is the round-annulus energy by the log-polar change
of variables. -/
theorem roughFlux_sub_eq_dirichletEnergy_roundAnnulus {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (h1 : ξ₁ < ζ₁) (h12 : ζ₁ ≤ ζ₂) (h2 : ζ₂ < ξ₂) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁
      = (dirichletEnergy u (RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂))).toReal := by
  have hπ := Real.pi_pos
  -- each `ζ` in `[ζ₁, ζ₂]` is a full-circle collar radius
  have hfull : ∀ ζ : ℝ, ζ ∈ Icc ξ₁ ξ₂ → ∀ θ : ℝ,
      Complex.exp ((ζ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro ζ hζ θ
    -- reduce the angle to `(−π, π]` by periodicity; the strip box covers `[−π, π]`
    set α : ℝ := (Complex.exp ((θ : ℂ) * Complex.I)).arg with hα
    have hunit : Complex.exp ((α : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
      have hx := Complex.norm_mul_exp_arg_mul_I (Complex.exp ((θ : ℂ) * Complex.I))
      rw [Complex.norm_exp] at hx
      simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero,
        Complex.ofReal_one, one_mul] at hx
      rw [hα]; exact hx
    have hper : Complex.exp ((ζ : ℂ) + (θ : ℂ) * Complex.I)
        = Complex.exp ((ζ : ℂ) + (α : ℂ) * Complex.I) := by
      rw [Complex.exp_add, Complex.exp_add, hunit]
    rw [hper]
    exact hmaps ζ hζ α ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hζ₁mem : ζ₁ ∈ Icc ξ₁ ξ₂ := ⟨h1.le, le_trans h12 h2.le⟩
  have hζ₂mem : ζ₂ ∈ Icc ξ₁ ξ₂ := ⟨le_trans h1.le h12, h2.le⟩
  have hmaps' : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hmaps
  -- rough flux = full-window flux at both radii; the FTC integrates the derivative value
  rw [roughFlux_eq_truncFlux_full hU (hfull ζ₂ hζ₂mem),
    roughFlux_eq_truncFlux_full hU (hfull ζ₁ hζ₁mem),
    truncFlux_sub_eq_integral_of_mapsTo hU hu (by linarith : -π ≤ π) hmaps' h1 h12 h2]
  -- the derivative value is the whole-circle slice energy (boundary terms cancel)
  have hderiveq : (∫ ξ in ζ₁..ζ₂, truncFluxDerivU u (-π) π ξ)
      = ∫ ξ in ζ₁..ζ₂,
        ∫ θ in Ioo (-π) π, Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
    intervalIntegral.integral_congr (fun ξ _ => truncFluxDerivU_full_eq_sliceEnergy (u := u) ξ)
  rw [hderiveq]
  -- the round-annulus energy is the log-polar box lintegral of `normSq (expGrad u)`
  rw [dirichletEnergy_roundAnnulus_eq_lintegral u ζ₁ ζ₂]
  -- inner bridge: the `ofReal` of the whole-circle slice energy is the inner slice lintegral
  have hSnn : ∀ ξ : ℝ, 0 ≤ ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun ξ =>
    setIntegral_nonneg measurableSet_Ioo fun θ _ => Complex.normSq_nonneg _
  -- integrability of the whole-circle slice energy over `[ζ₁, ζ₂]` for the outer bridge
  have hScont : ContinuousOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc ζ₁ ζ₂) := by
    have hfulld : ContinuousOn (truncFluxDerivU u (-π) π) (Icc ζ₁ ζ₂) :=
      (continuousOn_truncFluxDerivU hU hu (by linarith : -π ≤ π) hmaps').mono
        (fun x hx => ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h2⟩)
    exact hfulld.congr (fun ξ _ => (truncFluxDerivU_full_eq_sliceEnergy (u := u) ξ).symm)
  have hSint : IntegrableOn (fun ξ : ℝ => ∫ θ in Ioo (-π) π,
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo ζ₁ ζ₂) :=
    (hScont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hinner : ∀ ξ ∈ Ioo ζ₁ ζ₂,
      (∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
      = ENNReal.ofReal (∫ θ in Ioo (-π) π,
          Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) := by
    intro ξ hξ
    have hmem : ξ ∈ Icc ξ₁ ξ₂ := ⟨le_trans hζ₁mem.1 hξ.1.le, le_trans hξ.2.le hζ₂mem.2⟩
    have hintNeg : IntegrableOn
        (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (Ioo (-π) π) :=
      (continuousOn_slice_of_continuousOn_stripBox
        (Complex.continuous_normSq.comp_continuousOn
          (continuousOn_expGrad_stripBox_of_mapsTo hU hu hmaps'))
        (lt_trans h1 hξ.1) (lt_trans hξ.2 h2)).integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hintNeg
      (ae_of_all _ fun θ => Complex.normSq_nonneg _)]
  rw [setLIntegral_congr_fun measurableSet_Ioo hinner,
    ← ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ fun ξ => hSnn ξ),
    integral_Ioo_eq_intervalIntegral h12]
  rw [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg h12 (fun ξ _ => hSnn ξ))]

/-- **Monotonicity of the Dirichlet energy in the domain.** The Dirichlet energy is monotone under
inclusion of the integration set: `E ⊆ F ⇒ D(u; E) ≤ D(u; F)`. -/
theorem dirichletEnergy_mono {u : ℂ → ℝ} {E F : Set ℂ} (hEF : E ⊆ F) :
    dirichletEnergy u E ≤ dirichletEnergy u F :=
  lintegral_mono_set hEF

/-- **The `ofReal` of a set integral is dominated by the set lower integral.** For a nonnegative `g`
on a measurable set `s`, `ofReal (∫_s g) ≤ ∫⁻_s ofReal (g)`: if `g` is integrable this is equality,
otherwise the Bochner integral is `0`. -/
theorem ofReal_setIntegral_le_setLIntegral_ofReal {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hgnn : ∀ t ∈ s, 0 ≤ g t) :
    ENNReal.ofReal (∫ t in s, g t) ≤ ∫⁻ t in s, ENNReal.ofReal (g t) := by
  by_cases hint : IntegrableOn g s
  · rw [ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' hs).mpr (ae_of_all _ hgnn))]
  · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le

/-- **Log-polar change of variables for the energy over an open set below a radius.** For any `u`
and log-radius `ξ₀`, the Dirichlet energy over `U ∩ {0 < |z| < e^{ξ₀}}` is the iterated log-polar
integral of `normSq (expGrad u)` restricted to the angular slice of `U`: the polar Jacobian combines
the squared gradient into `normSq (expGrad u)`, and the indicator of `U` becomes the slice
indicator. -/
theorem dirichletEnergy_inter_ball_eq_lintegral_slice (u : ℂ → ℝ) {U : Set ℂ} (hU : IsOpen U)
    (ξ₀ : ℝ) :
    dirichletEnergy u {z : ℂ | z ∈ U ∧ 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀}
      = ∫⁻ ξ in Iio ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
  classical
  set A : Set ℂ := {z : ℂ | z ∈ U ∧ 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀} with hA
  set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Complex.normSq (gradC u z)) with hG
  set R : Set (ℝ × ℝ) := Ioo (0 : ℝ) (Real.exp ξ₀) ×ˢ Ioo (-π) π with hR
  have hGmeas : Measurable G :=
    ENNReal.measurable_ofReal.comp (Complex.continuous_normSq.measurable.comp (measurable_gradC u))
  have hAMeas : MeasurableSet A := by
    have : A = U ∩ {z : ℂ | 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀} := by
      ext z; simp only [hA, mem_setOf_eq, mem_inter_iff]
    rw [this]
    refine hU.measurableSet.inter ?_
    exact (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const) |>.measurableSet
  have hRMeas : MeasurableSet R := measurableSet_Ioo.prod measurableSet_Ioo
  have hsymmMeas : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have heq : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [heq]; exact Continuous.measurable (by fun_prop)
  -- Step 1: polar change of variables, folding the indicator of `A` into the slice indicator
  have h2 : ∫⁻ z in A, G z
      = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
          * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := by
    have hcov := Complex.lintegral_comp_polarCoord_symm (fun z => A.indicator G z)
    rw [lintegral_indicator hAMeas] at hcov
    have hpt : ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • A.indicator G (Complex.polarCoord.symm p)
          = R.indicator (fun q : ℝ × ℝ =>
              (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm q))
                * (ENNReal.ofReal q.1 * G (Complex.polarCoord.symm q))) p := by
      intro p hp
      rw [polarCoord_target] at hp
      have hnorm : dist (Complex.polarCoord.symm p) 0 = p.1 := by
        rw [dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      by_cases hmemA : Complex.polarCoord.symm p ∈ A
      · have hUin : Complex.polarCoord.symm p ∈ U := hmemA.1
        have hlt : dist (Complex.polarCoord.symm p) 0 < Real.exp ξ₀ := hmemA.2.2
        have hpR : p ∈ R := ⟨⟨hp.1, by rwa [hnorm] at hlt⟩, hp.2⟩
        rw [Set.indicator_of_mem hmemA, Set.indicator_of_mem hpR,
          Set.indicator_of_mem hUin, smul_eq_mul, one_mul]
      · rw [Set.indicator_of_notMem hmemA, smul_zero]
        by_cases hpR : p ∈ R
        · rw [Set.indicator_of_mem hpR]
          rw [Set.indicator_of_notMem (fun hUin => hmemA
            ⟨hUin, by rw [hnorm]; exact hp.1, by rw [hnorm]; exact hpR.1.2⟩), zero_mul]
        · rw [Set.indicator_of_notMem hpR]
    have hRsub : R ⊆ polarCoord.target := by
      rintro p ⟨hp1, hp2⟩
      rw [polarCoord_target]; exact ⟨hp1.1, hp2⟩
    calc ∫⁻ z in A, G z
        = ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • A.indicator G (Complex.polarCoord.symm p) := hcov.symm
      _ = ∫⁻ p in polarCoord.target,
            R.indicator (fun q : ℝ × ℝ =>
              (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm q))
                * (ENNReal.ofReal q.1 * G (Complex.polarCoord.symm q))) p :=
          setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt
      _ = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
            * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p))
            ∂(volume.restrict polarCoord.target) := lintegral_indicator hRMeas _
      _ = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
            * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := by
          rw [Measure.restrict_restrict hRMeas, Set.inter_eq_self_of_subset_left hRsub]
  -- Step 2: Tonelli on the rectangle
  have hUindeq : (fun p : ℝ × ℝ => U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
      = ((fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    by_cases hp : Complex.polarCoord.symm p ∈ U
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ _ from hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ _ from hp)]
  have hintegrand_meas : Measurable fun p : ℝ × ℝ =>
      (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
        * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := by
    refine Measurable.mul ?_ ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hGmeas.comp hsymmMeas))
    rw [hUindeq]
    exact measurable_const.indicator (hU.measurableSet.preimage hsymmMeas)
  have h3 : ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
        * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p))
      = ∫⁻ r in Ioo (0 : ℝ) (Real.exp ξ₀), ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (r, θ)))
            * (ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict R
        = ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) (Real.exp ξ₀))).prod
            ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
      rw [hR, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hprod]; exact lintegral_prod _ hintegrand_meas.aemeasurable
  -- Step 3: radial substitution `r = e^ξ`, restricting to `Iio ξ₀`
  have h4 : ∫⁻ r in Ioo (0 : ℝ) (Real.exp ξ₀), ∫⁻ θ in Ioo (-π) π,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (r, θ)))
          * (ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)))
      = ∫⁻ ξ in Iio ξ₀, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (Real.exp ξ, θ)))
            * (ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ))) := by
    have himg : Real.exp '' Iio ξ₀ = Ioo (0 : ℝ) (Real.exp ξ₀) := by
      ext r; simp only [mem_image, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨Real.exp_pos x, Real.exp_lt_exp.mpr hx⟩
      · intro hr; exact ⟨Real.log r, (Real.log_lt_iff_lt_exp hr.1).mpr hr.2,
          Real.exp_log hr.1⟩
    rw [← himg]
    exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn _
  -- Step 4: absorb the Jacobian and fold the `U`-indicator into the slice indicator
  have h5 : ∀ ξ : ℝ, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
        (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (Real.exp ξ, θ)))
          * (ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ)))
      = ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
    intro ξ
    rw [abs_of_pos (Real.exp_pos ξ), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [polarCoord_symm_exp]
    by_cases hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show θ ∈ angularSlice U ξ from
        ⟨hθ, hmem⟩), one_mul, hG, normSq_expGrad_eq u ξ θ,
        ENNReal.ofReal_mul (Real.exp_pos ξ).le, ENNReal.ofReal_mul (Real.exp_pos ξ).le]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem
        (show θ ∉ angularSlice U ξ from fun h => hmem h.2), zero_mul, mul_zero]
  -- assemble the calc
  calc dirichletEnergy u A
      = ∫⁻ z in A, G z :=
        lintegral_congr fun z => nnnorm_fderiv_sq_eq_ofReal_normSq_gradC u z
    _ = ∫⁻ p in R, (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm p))
          * (ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)) := h2
    _ = ∫⁻ r in Ioo (0 : ℝ) (Real.exp ξ₀), ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (r, θ)))
            * (ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))) := h3
    _ = ∫⁻ ξ in Iio ξ₀, ENNReal.ofReal |Real.exp ξ| * ∫⁻ θ in Ioo (-π) π,
          (U.indicator (fun _ => (1 : ℝ≥0∞)) (Complex.polarCoord.symm (Real.exp ξ, θ)))
            * (ENNReal.ofReal (Real.exp ξ) * G (Complex.polarCoord.symm (Real.exp ξ, θ))) := h4
    _ = ∫⁻ ξ in Iio ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ :=
        lintegral_congr fun ξ => h5 ξ

/-- **The tail slice-energy lower integral is bounded by the total Dirichlet energy (`F2`).** For
`u` harmonic on the open set `U` with finite Dirichlet energy, the tail integral of the single-slice
energy `∫⁻_{Iic ξ₀} ofReal (sliceEnergyU u U ξ)` is at most `D(u; U)`: `ofReal` of the slice
integral is dominated by the slice lower integral, whose `ξ`-integral over `(-∞, ξ₀)` is — log-polar
change of variables — the energy over `U ∩ {|z| < e^{ξ₀}}`, monotone below `D(u; U)`. -/
theorem setLIntegral_tail_ofReal_sliceEnergyU_le {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (ξ₀ : ℝ) :
    (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ)) ≤ dirichletEnergy u U := by
  -- slice-wise: `ofReal` of the slice integral is dominated by the slice lower integral
  have hslice : ∀ ξ : ℝ, ENNReal.ofReal (sliceEnergyU u U ξ)
      ≤ ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
    intro ξ
    have hsub : angularSlice U ξ ⊆ Ioo (-π) π := angularSlice_subset U ξ
    have hsmeas : MeasurableSet (angularSlice U ξ) := (isOpen_angularSlice hU ξ).measurableSet
    calc ENNReal.ofReal (sliceEnergyU u U ξ)
        ≤ ∫⁻ θ in angularSlice U ξ,
            ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :=
          ofReal_setIntegral_le_setLIntegral_ofReal hsmeas
            (fun θ _ => Complex.normSq_nonneg _)
      _ = ∫⁻ θ in Ioo (-π) π,
            (angularSlice U ξ).indicator
              (fun θ' => ENNReal.ofReal
                (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ := by
          rw [lintegral_indicator hsmeas,
            Measure.restrict_restrict hsmeas, Set.inter_eq_self_of_subset_left hsub]
  -- integrate the slice bound in `ξ`; `Iic` and `Iio` agree up to the null endpoint
  calc (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ))
      ≤ ∫⁻ ξ in Iic ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ :=
        lintegral_mono hslice
    _ = ∫⁻ ξ in Iio ξ₀, ∫⁻ θ in Ioo (-π) π,
          (angularSlice U ξ).indicator
            (fun θ' => ENNReal.ofReal
              (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ :=
        (setLIntegral_congr Iio_ae_eq_Iic).symm
    _ = dirichletEnergy u {z : ℂ | z ∈ U ∧ 0 < dist z 0 ∧ dist z 0 < Real.exp ξ₀} :=
        (dirichletEnergy_inter_ball_eq_lintegral_slice u hU ξ₀).symm
    _ ≤ dirichletEnergy u U := dirichletEnergy_mono (fun z hz => hz.1)

/-- **The single-slice energy is measurable in the log-radius.** For `u` harmonic on the open set
`U`, the map `ξ ↦ sliceEnergyU u U ξ` is measurable: it is the `θ`-Bochner integral of the jointly
measurable integrand `(ξ, θ) ↦ (angularSlice U ξ).indicator (normSq (expGrad u)) θ`, whose
underlying set `{(ξ, θ) | θ ∈ (-π, π) ∧ e^{ξ+iθ} ∈ U}` is open. -/
theorem measurable_sliceEnergyU {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) :
    Measurable (sliceEnergyU u U) := by
  -- the joint slice set in `(ξ, θ)` is open, hence measurable
  set W : Set (ℝ × ℝ) :=
    {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π ∧ Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ U} with hW
  have hcontmap : Continuous fun p : ℝ × ℝ =>
      Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hWopen : IsOpen W := by
    have : W = (Prod.snd ⁻¹' Ioo (-π) π) ∩
        ((fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ⁻¹' U) := by
      ext p; simp only [hW, mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]
    exact (isOpen_Ioo.preimage continuous_snd).inter (hU.preimage hcontmap)
  -- the jointly measurable integrand, folded through the slice indicator
  have hjoint : Measurable fun p : ℝ × ℝ =>
      W.indicator (fun q : ℝ × ℝ =>
        ENNReal.ofReal (Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)))) p :=
    (ENNReal.measurable_ofReal.comp (measurable_normSq_expGrad_logPolar u)).indicator
      hWopen.measurableSet
  -- `sliceEnergyU` as a full `θ`-Bochner integral of the folded integrand
  have hrepr : ∀ ξ : ℝ, sliceEnergyU u U ξ
      = ∫ θ : ℝ, (angularSlice U ξ).indicator
          (fun θ' => Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ := by
    intro ξ
    rw [sliceEnergyU, ← MeasureTheory.integral_indicator (isOpen_angularSlice hU ξ).measurableSet]
  rw [show sliceEnergyU u U = fun ξ => ∫ θ : ℝ, (angularSlice U ξ).indicator
      (fun θ' => Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ from
    funext hrepr]
  -- reduce to strong measurability of the joint real integrand
  have hjointR : StronglyMeasurable fun p : ℝ × ℝ =>
      (angularSlice U p.1).indicator
        (fun θ' => Complex.normSq (expGrad u ((p.1 : ℂ) + (θ' : ℂ) * Complex.I))) p.2 := by
    have hmeasR : Measurable fun p : ℝ × ℝ =>
        W.indicator (fun q : ℝ × ℝ =>
          Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))) p :=
      (measurable_normSq_expGrad_logPolar u).indicator hWopen.measurableSet
    have hfeq : (fun p : ℝ × ℝ =>
          (angularSlice U p.1).indicator
            (fun θ' => Complex.normSq (expGrad u ((p.1 : ℂ) + (θ' : ℂ) * Complex.I))) p.2)
        = fun p : ℝ × ℝ => W.indicator (fun q : ℝ × ℝ =>
            Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))) p := by
      funext p
      by_cases hp : p ∈ W
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p.2 ∈ angularSlice U p.1 from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p.2 ∉ angularSlice U p.1 from hp)]
    rw [hfeq]; exact hmeasR.stronglyMeasurable
  exact (hjointR.integral_prod_right').measurable

/-- **Rough-flux increment bounded by the total energy (full-circle collar window).** For `u`
harmonic on the open set `U`, if the whole strip box over `[ξ₁, ξ₂] × [−π, π]` maps into `U` and the
round sub-annulus `{e^{ζ₁} < |z| < e^{ζ₂}}` is contained in `U`, then the rough-flux increment over
`[ζ₁, ζ₂] ⊆ (ξ₁, ξ₂)` is at most the total Dirichlet energy `D(u; U)`.  Combines the exact
full-circle collar identity with monotonicity of the energy in the domain. -/
theorem roughFlux_sub_le_dirichletEnergy {u : ℂ → ℝ} {U : Set ℂ} {ξ₁ ξ₂ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hsub : RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂) ⊆ U)
    (h1 : ξ₁ < ζ₁) (h12 : ζ₁ ≤ ζ₂) (h2 : ζ₂ < ξ₂)
    (hEfin : dirichletEnergy u U ≠ ⊤) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
  rw [roughFlux_sub_eq_dirichletEnergy_roundAnnulus hU hu hmaps h1 h12 h2]
  exact ENNReal.toReal_mono hEfin (dirichletEnergy_mono hsub)

/-! ### The level-set truncated rough flux and its `δ → 0` recovery

For `δ ∈ (0, 1)` the **superlevel set** `V_δ := {z ∈ U | δ < u z}` is open (`u` continuous on the
open `U`); its angular slice `angularSliceδ U u δ ξ` and the **δ-rough flux** `roughFluxδ` mirror
the angular slice and the rough flux with the indicator refined to the superlevel.  As `δ ↓ 0` the
superlevel slices increase to the slice of `U ∩ {u > 0}`, which — by the strong minimum principle
`u > 0` on a connected `U` where `u` is nonnegative and not identically `0` — is the full slice,
so `roughFluxδ u U · ξ → roughFlux u U ξ` by dominated convergence at any log-radius where the
slice radial-derivative integrand is slice-`L¹`. -/

/-- The **superlevel set** of a potential `u` above level `δ` inside an open set `U`: the points of
`U` where `u` strictly exceeds `δ`.  For continuous `u` on the open `U` it is open. -/
def superLevelU (U : Set ℂ) (u : ℂ → ℝ) (δ : ℝ) : Set ℂ := {z : ℂ | z ∈ U ∧ δ < u z}

/-- The **δ-angular slice**: the angles whose log-polar image lies in the superlevel set. -/
def angularSliceδ (U : Set ℂ) (u : ℂ → ℝ) (δ ξ : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Ioo (-π) π ∧ Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ}

/-- The **δ-rough flux**: the rough flux with the slice indicator refined to the superlevel set. -/
noncomputable def roughFluxδ (u : ℂ → ℝ) (U : Set ℂ) (δ ξ : ℝ) : ℝ :=
  ∫ θ in Ioo (-π) π,
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}.indicator
      (fun θ' : ℝ => u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)).re) θ

/-- The superlevel set is open, for `u` harmonic (hence continuous) on the open `U`. -/
theorem isOpen_superLevelU {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ : ℝ) : IsOpen (superLevelU U u δ) := by
  have hcont : ContinuousOn u U := hu.continuousOn
  have hrw : superLevelU U u δ = U ∩ (u ⁻¹' Ioi δ) := by
    ext z; simp only [superLevelU, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi]
  rw [hrw]
  exact hcont.isOpen_inter_preimage hU isOpen_Ioi

/-- The δ-angular slice is the angular slice of the superlevel set. -/
theorem angularSliceδ_eq {U : Set ℂ} {u : ℂ → ℝ} (δ ξ : ℝ) :
    angularSliceδ U u δ ξ = angularSlice (superLevelU U u δ) ξ := rfl

/-- The δ-angular slice is open, for `u` harmonic on the open `U`. -/
theorem isOpen_angularSliceδ {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    IsOpen (angularSliceδ U u δ ξ) :=
  isOpen_angularSlice (isOpen_superLevelU hU hu δ) ξ

/-- The δ-angular slice is contained in `(−π, π)`, hence measurable. -/
theorem angularSliceδ_subset {U : Set ℂ} {u : ℂ → ℝ} (δ ξ : ℝ) :
    angularSliceδ U u δ ξ ⊆ Ioo (-π) π := fun _ hθ => hθ.1

/-- The δ-angular slice sits inside the full angular slice: superlevel points lie in `U`. -/
theorem angularSliceδ_subset_angularSlice {U : Set ℂ} {u : ℂ → ℝ} (δ ξ : ℝ) :
    angularSliceδ U u δ ξ ⊆ angularSlice U ξ :=
  fun _ hθ => ⟨hθ.1, hθ.2.1⟩

/-- **The δ-rough flux is the set integral over the δ-angular slice.** The indicator integral
defining `roughFluxδ` unfolds, exactly as for `roughFlux`, to the set integral of
`u · Re (expGrad u)` over the open δ-angular slice. -/
theorem roughFluxδ_eq_setIntegral_slice {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    roughFluxδ u U δ ξ = ∫ θ in angularSliceδ U u δ ξ,
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hπ := Real.pi_pos
  have hVopen : IsOpen (superLevelU U u δ) := isOpen_superLevelU hU hu δ
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hmeasset :
      MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} :=
    hcontmap.measurable hVopen.measurableSet
  unfold roughFluxδ
  rw [setIntegral_indicator hmeasset]
  refine setIntegral_congr_set ?_
  rw [angularSliceδ, superLevelU]
  refine (ae_eq_set.mpr ⟨?_, ?_⟩) <;>
    · refine measure_mono_null (fun θ hθ => ?_) measure_empty
      simp only [mem_diff, mem_inter_iff, mem_setOf_eq] at hθ
      tauto

/-- **The δ-rough flux is the rough flux of the superlevel set.** The δ-rough flux restricts the
slice indicator to the superlevel set `V_δ = {u > δ} ∩ U`, which is exactly the rough flux of `u`
over the open set `V_δ`. -/
theorem roughFluxδ_eq_roughFlux_superLevelU {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    roughFluxδ u U δ ξ = roughFlux u (superLevelU U u δ) ξ := by
  rw [roughFluxδ_eq_setIntegral_slice hU hu,
    roughFlux_eq_setIntegral_slice (isOpen_superLevelU hU hu δ), angularSliceδ_eq]

/-- **Compact containment of a superlevel window.** For `u` continuous on `closure U` and vanishing
on the part of `frontier U` inside the unit disc, the closure of the intersection of the superlevel
set `{u > δ}` (`δ > 0`) with a window annulus `{e^{ζ₁} < |z| < e^{ζ₂}}` (`ζ₂ < 0`) is a compact
subset of `U`.  It is closed and bounded (the window sits in the disc of radius `e^{ζ₂} < 1`), and
each of its points `w` has `u w ≥ δ > 0` by continuity — a frontier point with `‖w‖ < 1` would force
`u w = 0`, so `w` is an interior point of `U`. -/
theorem closure_superLevel_window_subset {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hδ : 0 < δ) (hζ₂ : ζ₂ < 0) :
    IsCompact (closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂))) ∧
      closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) ⊆ U := by
  set W : Set ℂ := RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂) with hW
  set V : Set ℂ := superLevelU U u δ with hV
  set K : Set ℂ := closure (V ∩ W) with hK
  have hexp1 : Real.exp ζ₂ < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr hζ₂
  have hWsub : W ⊆ {z : ℂ | dist z 0 ≤ Real.exp ζ₂} := fun z hz => hz.2.le
  have hclW : closure W ⊆ {z : ℂ | dist z 0 ≤ Real.exp ζ₂} :=
    closure_minimal hWsub (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hKdisc : K ⊆ {z : ℂ | dist z 0 ≤ Real.exp ζ₂} :=
    (closure_mono inter_subset_right).trans hclW
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨Real.exp ζ₂, fun z hz => ?_⟩
    rw [Metric.mem_closedBall]; exact hKdisc hz
  have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_closure hKbdd
  refine ⟨hKcompact, ?_⟩
  intro w hw
  have hVWU : V ∩ W ⊆ U := inter_subset_left.trans (fun z hz => hz.1)
  have hwclU : w ∈ closure U := closure_mono hVWU hw
  have hwnorm : ‖w‖ < 1 := by
    have hle := hKdisc hw
    rw [mem_setOf_eq, dist_zero_right] at hle
    exact lt_of_le_of_lt hle hexp1
  have huwge : δ ≤ u w := by
    have hmap : MapsTo u (V ∩ W) (Ici δ) := fun z hz => le_of_lt hz.1.2
    have hclsub : closure (V ∩ W) ⊆ closure U := closure_mono hVWU
    have hcl : MapsTo u (closure (V ∩ W)) (closure (Ici δ)) :=
      hmap.closure_of_continuousOn (hucont.mono hclsub)
    have := hcl hw
    rwa [closure_Ici, mem_Ici] at this
  have hnotfront : w ∉ frontier U := by
    intro hfront
    have := hE0 w hfront hwnorm
    linarith
  rw [closure_eq_self_union_frontier] at hwclU
  exact hwclU.resolve_right hnotfront

/-- **Strict positivity of a nonnegative nonconstant harmonic potential.** For `u` harmonic on the
open preconnected set `U`, nonnegative on `U` and strictly positive at one point, the strong minimum
principle gives `0 < u` throughout `U`: a zero would force `u ≡ 0`, contradicting the positive
point. -/
theorem pos_of_harmonic_nonneg {U : Set ℂ} {u : ℂ → ℝ} (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hnn : ∀ z ∈ U, 0 ≤ u z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hpos : 0 < u z₀) : ∀ z ∈ U, 0 < u z := by
  intro z hz
  refine lt_of_le_of_ne (hnn z hz) (fun heq => ?_)
  have hzero := harmonic_eq_zero_of_nonneg_eq_zero hU hUconn hu hnn hz heq.symm
  exact absurd (hzero z₀ hz₀) hpos.ne'

/-- **`δ`-monotone pointwise recovery of the slice indicator.** For `u` strictly positive on `U`,
each angle `θ` of the full angular slice enters the δ-angular slice once `δ < u (e^{ξ+iθ})`; hence
along any positive null-sequence `δ n → 0`, the δ-slice indicator of the flux integrand converges
pointwise to the full-slice indicator. -/
theorem tendsto_indicator_angularSliceδ {u : ℂ → ℝ} {U : Set ℂ} {ξ : ℝ}
    (hpos : ∀ z ∈ U, 0 < u z) {d : ℕ → ℝ} (hdto : Tendsto d atTop (𝓝 0))
    (F : ℝ → ℝ) (θ : ℝ) :
    Tendsto (fun n => {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)}.indicator F θ)
      atTop (𝓝 ({θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator F θ)) := by
  by_cases hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
  · -- `θ` in the full slice: eventually `d n < u(e^{ξ+iθ})`, so the δ-indicator is `F θ`
    rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
    have hupos : 0 < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := hpos _ hmem
    have hev : ∀ᶠ n in atTop, d n < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      hdto.eventually_lt_const hupos
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with n hn
    rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
      superLevelU U u (d n)} from ⟨hmem, hn⟩)]
  · -- `θ` outside the full slice: both indicators are `0`
    rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
      superLevelU U u (d n)} from fun h => hmem h.1)]

/-- **`δ → 0` recovery of the rough flux.** For `u` harmonic and strictly positive on the open set
`U`, if at log-radius `ξ` the slice radial-derivative integrand `θ ↦ Re (expGrad u)` is integrable
on the angular slice, then along any positive null-sequence `δ n → 0` the δ-rough flux tends to the
rough flux: the δ-slice indicators of the integrand `u · Re (expGrad u)` increase pointwise to the
full-slice indicator, dominated by the slice-`L¹` bound `|u| · |Re (expGrad u)|`, so dominated
convergence applies on `(−π, π)`. -/
theorem tendsto_roughFluxδ_atZero {u : ℂ → ℝ} {U : Set ℂ} {ξ M : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z) (hMnn : 0 ≤ M)
    (hM : ∀ θ ∈ angularSlice U ξ, |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hReInt : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    {d : ℕ → ℝ} (hdto : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => roughFluxδ u U (d n) ξ) atTop (𝓝 (roughFlux u U ξ)) := by
  have hπ := Real.pi_pos
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hssub : s ⊆ Ioo (-π) π := angularSlice_subset U ξ
  set I : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hI
  -- the fixed dominating function: the full-slice indicator of `|I|`
  set B : ℝ → ℝ := s.indicator (fun θ => M * |(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|)
    with hB
  -- `I` is continuous on the full slice `s`
  have hcontI : ContinuousOn I s := by
    intro θ hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2
    have hcm : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
      fun_prop
    have hcu : ContinuousAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))) θ :=
      (ContinuousAt.comp (g := u)
        (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hcm)
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hmem
    have hcg : ContinuousAt
        (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      (ContinuousAt.comp (g := fun w : ℂ => (expGrad u w).re)
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (Complex.continuous_re.continuousAt.comp hdC.continuousAt) (by fun_prop))
    exact (hcu.mul hcg).continuousWithinAt
  have hBint : IntegrableOn B (Ioo (-π) π) := by
    have hsint : IntegrableOn
        (fun θ : ℝ => M * |(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|) s :=
      hReInt.abs.const_mul M
    rw [hB, integrableOn_indicator_iff hsmeas, Set.inter_eq_self_of_subset_left hssub]
    exact hsint
  -- indicator a.e.-strong-measurability of each δ-integrand on `(−π, π)`
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun θ => {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)}.indicator I θ) (volume.restrict (Ioo (-π) π)) := by
    intro n
    have hVmeas : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable
          (isOpen_superLevelU hU hu (d n)).measurableSet
    rw [aestronglyMeasurable_indicator_iff hVmeas]
    -- `I` on `(Ioo (-π) π) ∩ V`; since `V ∩ Ioo ⊆ s`, restrict `I`'s slice measurability
    have hIslice : AEStronglyMeasurable I (volume.restrict s) :=
      hcontI.aestronglyMeasurable hsmeas
    refine hIslice.mono_measure ?_
    rw [Measure.restrict_restrict hVmeas]
    refine Measure.restrict_mono (fun θ hθ => ?_) le_rfl
    exact (show θ ∈ s from ⟨hθ.2, hθ.1.1⟩)
  -- rewrite both sides as indicator integrals over the fixed `(−π, π)`
  have hδform : ∀ n, roughFluxδ u U (d n) ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
          superLevelU U u (d n)}.indicator I θ := fun n => rfl
  have hlimform : roughFlux u U ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator I θ := by
    rw [roughFlux_eq_setIntegral_slice hU, ← hs]
    rw [show (∫ θ in Ioo (-π) π, {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator I θ)
        = ∫ θ in Ioo (-π) π, s.indicator I θ from
      setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)]
    · rw [MeasureTheory.integral_indicator hsmeas, Measure.restrict_restrict hsmeas,
        Set.inter_eq_self_of_subset_left hssub]
    · by_cases hθU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
      · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hθU),
          Set.indicator_of_mem (show θ ∈ s from ⟨hθ, hθU⟩)]
      · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hθU),
          Set.indicator_of_notMem (show θ ∉ s from fun h => hθU h.2)]
  simp only [hδform]
  rw [hlimform]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence B hFmeas hBint ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    by_cases hθV : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u (d n)
    · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV)]
      have hθs : θ ∈ s := ⟨hθ, hθV.1⟩
      rw [hB, Set.indicator_of_mem hθs, hI, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM θ hθs) (abs_nonneg _)
    · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV),
        norm_zero, hB]
      by_cases hθs : θ ∈ s
      · rw [Set.indicator_of_mem hθs]; positivity
      · rw [Set.indicator_of_notMem hθs]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    exact tendsto_indicator_angularSliceδ hpos hdto I θ

/-- **Rough-flux increment from the level-set increment bound.** For `u` harmonic and strictly
positive on the open set `U`, uniformly bounded by `M` on both slices at `ζ₁` and `ζ₂` with the
slice radial-derivative integrand integrable there, if the δ-rough-flux increment is bounded by a
constant `D` for every `δ > 0`, then the rough-flux increment is bounded by `D`: pass to `δ → 0`
using the `δ`-recovery of the rough flux at each of the two log-radii. -/
theorem roughFlux_sub_le_of_roughFluxδ_sub_le {u : ℂ → ℝ} {U : Set ℂ} {ζ₁ ζ₂ M D : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hMnn : 0 ≤ M)
    (hM1 : ∀ θ ∈ angularSlice U ζ₁, |u (Complex.exp ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hM2 : ∀ θ ∈ angularSlice U ζ₂, |u (Complex.exp ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hRe1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₁))
    (hRe2 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₂))
    (hδbd : ∀ δ : ℝ, 0 < δ → roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ D) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ D := by
  -- a concrete positive null-sequence `δ n = 1/(n+1) → 0`
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hd
  have hdpos : ∀ n, 0 < d n := fun n => by positivity
  have hdto : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- `δ`-recovery at both log-radii
  have hlim1 : Tendsto (fun n => roughFluxδ u U (d n) ζ₁) atTop (𝓝 (roughFlux u U ζ₁)) :=
    tendsto_roughFluxδ_atZero hU hu hpos hMnn hM1 hRe1 hdto
  have hlim2 : Tendsto (fun n => roughFluxδ u U (d n) ζ₂) atTop (𝓝 (roughFlux u U ζ₂)) :=
    tendsto_roughFluxδ_atZero hU hu hpos hMnn hM2 hRe2 hdto
  have hlim : Tendsto (fun n => roughFluxδ u U (d n) ζ₂ - roughFluxδ u U (d n) ζ₁) atTop
      (𝓝 (roughFlux u U ζ₂ - roughFlux u U ζ₁)) := hlim2.sub hlim1
  refine le_of_tendsto hlim ?_
  filter_upwards with n
  exact hδbd (d n) (hdpos n)

/-- **The slope is bounded by the total energy.** Let `u` be harmonic on an open set `U` containing
the whole punctured collar `{0 < |z| < 1}` (every circle `e^{ξ+iθ}`, `ξ < 0`, lies in `U`), with
finite Dirichlet energy `D(u; U) < ∞`.  If the rough flux tends to the boundary slope `b` as the
log-radius rises to `0` and tends to `0` as it falls to `−∞` (the potential vanishing at the
origin), then the slope is bounded by the total energy: `b ≤ D(u; U)`.

The two flux limits are the boundary data of the flux–energy exchange: on every full-circle window
`[ζ₁, ζ₂] ⊆ (−∞, 0)` the rough-flux increment is the sub-annulus energy, bounded by `D(u; U)`;
letting `ζ₂ ↑ 0` and `ζ₁ ↓ −∞` sends the increment to `b − 0 = b`. -/
theorem slope_le_energy {u : ℂ → ℝ} {U : Set ℂ} {b : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hmaps : ∀ ξ : ℝ, ξ < 0 → ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hEfin : dirichletEnergy u U ≠ ⊤)
    (hTop : Tendsto (roughFlux u U) (𝓝[<] (0 : ℝ)) (𝓝 b))
    (hBot : Tendsto (roughFlux u U) atBot (𝓝 0)) :
    b ≤ (dirichletEnergy u U).toReal := by
  -- box-mapping over any slab strictly below `0`
  have hbox : ∀ ξ₁ ξ₂ : ℝ, ξ₂ < 0 → ∀ x ∈ Icc ξ₁ ξ₂, ∀ θ ∈ Icc (-π) π,
      Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U := by
    intro ξ₁ ξ₂ hξ₂ x hx θ _
    exact hmaps x (lt_of_le_of_lt hx.2 hξ₂) θ
  -- the whole round sub-annulus below `0` lies in `U`
  have hann : ∀ ζ₁ ζ₂ : ℝ, ζ₂ < 0 → RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂) ⊆ U := by
    intro ζ₁ ζ₂ hζ₂ z hz
    obtain ⟨hz1, hz2⟩ := hz
    -- write `z = e^{ξ+θi}` with `ξ = log|z| < ζ₂ < 0`
    set ξ : ℝ := Real.log (dist z 0) with hξ
    have hdpos : 0 < dist z 0 := lt_of_le_of_lt (Real.exp_pos _).le hz1
    have hznorm : dist z 0 = Real.exp ξ := by rw [hξ, Real.exp_log hdpos]
    have hξ0 : ξ < 0 := by
      have hlt : Real.exp ξ < Real.exp ζ₂ := by rw [← hznorm]; exact hz2
      exact lt_trans (Real.exp_lt_exp.mp hlt) hζ₂
    have hzrepr : z = Complex.exp ((ξ : ℂ) + ((z.arg : ℝ) : ℂ) * Complex.I) := by
      have hnz := Complex.norm_mul_exp_arg_mul_I z
      have hnorm : (‖z‖ : ℂ) = ((Real.exp ξ : ℝ) : ℂ) := by
        rw [← dist_zero_right, hznorm]
      rw [Complex.exp_add, ← Complex.ofReal_exp, ← hnorm, hnz]
    rw [hzrepr]; exact hmaps ξ hξ0 z.arg
  -- windowed increment inequality for any `ζ₁ ≤ ζ₂ < 0`
  have hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
    intro ζ₁ ζ₂ h12 hζ₂
    exact roughFlux_sub_le_dirichletEnergy hU hu
      (hbox (ζ₁ - 1) (ζ₂ + (-ζ₂) / 2) (by linarith))
      (hann ζ₁ ζ₂ hζ₂) (by linarith) h12 (by linarith) hEfin
  -- fix an inner radius `ζ₁` and let the outer radius rise to `0`: `b − roughFlux ζ₁ ≤ D`
  have hfix : ∀ ζ₁ : ℝ, ζ₁ < 0 → b - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
    intro ζ₁ hζ₁
    have hlim : Tendsto (fun ζ₂ : ℝ => roughFlux u U ζ₂ - roughFlux u U ζ₁)
        (𝓝[<] (0 : ℝ)) (𝓝 (b - roughFlux u U ζ₁)) := hTop.sub_const _
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hζ₁, self_mem_nhdsWithin] with ζ₂ hζ₂mem hζ₂neg
    exact hwin ζ₁ ζ₂ hζ₂mem.1.le hζ₂neg
  -- let the inner radius fall to `−∞`: `roughFlux ζ₁ → 0`, giving `b ≤ D`
  have hlim2 : Tendsto (fun ζ₁ : ℝ => b - roughFlux u U ζ₁) atBot (𝓝 (b - 0)) :=
    hBot.const_sub b
  rw [sub_zero] at hlim2
  refine le_of_tendsto hlim2 ?_
  filter_upwards [Iio_mem_atBot (0 : ℝ)] with ζ₁ hζ₁
  exact hfix ζ₁ hζ₁

/-! ### The keystone-shaped slope bound: discharging the two flux limits

For the keystone open set `U` (whose frontier contains a connected continuum `E ∋ 0` blocking small
circles) the full-circle hypothesis of `slope_le_energy` fails.  The lemmas below discharge the two
flux limits from ring-potential data on a *round collar* `{r₀ < |z| < 1}` whose full circles lie in
`U`, and package the slope bound consuming the windowed increment inequality over the genuine window
family (log-radii below `0`, where the collar circles are full). -/

/-- **Set-integral Cauchy–Schwarz.** For `g` with `g` and `g²` integrable on a finite-measure set
`s`, `(∫_s |g|)² ≤ (volume s).toReal · ∫_s g²`, via the discriminant of the nonnegative quadratic
`x ↦ ∫_s (x·|g| + 1)²`. -/
theorem sq_setIntegral_abs_le {g : ℝ → ℝ} {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hsfin : volume s ≠ ⊤) (hg : IntegrableOn g s)
    (hg2 : IntegrableOn (fun t => (g t) ^ 2) s) :
    (∫ t in s, |g t|) ^ 2 ≤ (volume s).toReal * ∫ t in s, (g t) ^ 2 := by
  set A := ∫ t in s, (g t) ^ 2 with hA
  set B := ∫ t in s, |g t| with hB
  set V := (volume s).toReal with hV
  have hQ : ∀ x : ℝ, 0 ≤ A * (x * x) + (2 * B) * x + V := by
    intro x
    have key : ∀ t, (x * |g t| + 1) ^ 2 = x ^ 2 * (g t) ^ 2 + (2 * x) * |g t| + 1 := by
      intro t; rw [← sq_abs (g t)]; ring
    have hi1 : IntegrableOn (fun t => x ^ 2 * (g t) ^ 2) s := hg2.const_mul (x ^ 2)
    have hi2 : IntegrableOn (fun t => (2 * x) * |g t|) s := hg.abs.const_mul (2 * x)
    have hi3 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s := integrableOn_const hsfin (by simp)
    have hnn : (0 : ℝ) ≤ ∫ t in s, (x * |g t| + 1) ^ 2 :=
      setIntegral_nonneg hsmeas fun t _ => by positivity
    have hexp : (∫ t in s, (x * |g t| + 1) ^ 2) = A * (x * x) + (2 * B) * x + V := by
      have hcong : (∫ t in s, (x * |g t| + 1) ^ 2)
          = ∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t| + 1) :=
        setIntegral_congr_fun hsmeas fun t _ => key t
      have hsplit1 : (∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t| + 1))
          = (∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t|)) + ∫ _t in s, (1 : ℝ) :=
        integral_add (hi1.add hi2) hi3
      have hsplit2 : (∫ t in s, (x ^ 2 * (g t) ^ 2 + (2 * x) * |g t|))
          = (∫ t in s, x ^ 2 * (g t) ^ 2) + ∫ t in s, (2 * x) * |g t| :=
        integral_add hi1 hi2
      rw [hcong, hsplit1, hsplit2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]
      rw [← hA, ← hB, hV, ← measureReal_def]
      ring
    rw [hexp] at hnn; exact hnn
  have hdisc : discrim A (2 * B) V ≤ 0 := discrim_le_zero hQ
  have hdisc' : (2 * B) ^ 2 - 4 * A * V ≤ 0 := by
    have : discrim A (2 * B) V = (2 * B) ^ 2 - 4 * A * V := by unfold discrim; ring
    rwa [this] at hdisc
  nlinarith [hdisc']

/-- **Per-slice Cauchy–Schwarz bound on the rough flux.** For `u` harmonic on the open set `U`, if
on the angular slice at log-radius `ξ` the potential is bounded by `M`, the slice radial-derivative
integrand is integrable and the slice squared gradient is integrable, then the rough flux is bounded
by `M · √(2π) · √(sliceEnergyU u U ξ)`: the flux is the slice integral of `u · Re (expGrad u)`,
bounded pointwise by `M · |Re (expGrad u)|`, whose slice `L¹` norm is Cauchy–Schwarz-dominated by
`√(2π) · √(∫ (Re expGrad)²) ≤ √(2π) · √(slice energy)`. -/
theorem abs_roughFlux_le_slice {u : ℂ → ℝ} {U : Set ℂ} {ξ M : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hMnn : 0 ≤ M)
    (hM : ∀ θ ∈ angularSlice U ξ, |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hReInt : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    (hEInt : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ)) :
    |roughFlux u U ξ| ≤ M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ)) := by
  have hπ := Real.pi_pos
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hsvol : volume s ≤ ENNReal.ofReal (2 * π) := by
    refine le_trans (measure_mono (angularSlice_subset U ξ)) ?_
    rw [Real.volume_Ioo]; exact le_of_eq (by rw [show π - -π = 2 * π by ring])
  have hsvol' : (volume s).toReal ≤ 2 * π := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsvol
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  set F : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hG
  -- `(Re expGrad)² ≤ normSq expGrad`, so `∫ G² ≤ sliceEnergyU`
  have hG2int : IntegrableOn (fun θ => (G θ) ^ 2) s := by
    refine (hEInt).mono' (hReInt.aestronglyMeasurable.pow 2) ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.normSq_apply]
    nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im]
  have hG2le : (∫ θ in s, (G θ) ^ 2) ≤ sliceEnergyU u U ξ := by
    rw [hs, sliceEnergyU]
    refine setIntegral_mono_on hG2int (hEInt.mono_set (by rw [hs])) ?_ (fun θ _ => ?_)
    · exact (isOpen_angularSlice hU ξ).measurableSet
    · rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im]
  -- `u ∘ exp` is continuous on the open slice, hence a.e.-strongly-measurable there
  have hFmeas : AEStronglyMeasurable F (volume.restrict s) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hsmeas
    intro θ hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2
    have hc : ContinuousAt u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
      (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt
    have hcm : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
      fun_prop
    exact (ContinuousAt.comp (g := u)
      (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) hc hcm).continuousWithinAt
  have hFGint : IntegrableOn (fun θ => F θ * G θ) s := by
    refine (hReInt.abs.const_mul M).mono' (hFmeas.mul hReInt.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM θ hθ) (abs_nonneg _)
  -- Cauchy–Schwarz: `∫_s |G| ≤ √(vol s) · √(∫_s G²) ≤ √(2π)·√(sliceEnergyU)`
  have hCS : (∫ θ in s, |G θ|) ≤ Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ) := by
    have hcs := sq_setIntegral_abs_le hsmeas (by
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsvol) hReInt hG2int
    have h0 : (0 : ℝ) ≤ ∫ θ in s, |G θ| := setIntegral_nonneg hsmeas fun θ _ => abs_nonneg _
    have hstep : (∫ θ in s, |G θ|) ≤ Real.sqrt ((volume s).toReal * ∫ θ in s, (G θ) ^ 2) := by
      rw [show (∫ θ in s, |G θ|) = Real.sqrt ((∫ θ in s, |G θ|) ^ 2) from (Real.sqrt_sq h0).symm]
      exact Real.sqrt_le_sqrt hcs
    calc (∫ θ in s, |G θ|)
        ≤ Real.sqrt ((volume s).toReal * ∫ θ in s, (G θ) ^ 2) := hstep
      _ = Real.sqrt ((volume s).toReal) * Real.sqrt (∫ θ in s, (G θ) ^ 2) :=
          Real.sqrt_mul ENNReal.toReal_nonneg _
      _ ≤ Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ) :=
          mul_le_mul (Real.sqrt_le_sqrt hsvol') (Real.sqrt_le_sqrt hG2le)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- assemble
  rw [roughFlux_eq_setIntegral_slice hU, ← hs]
  calc |∫ θ in s, F θ * G θ|
      ≤ ∫ θ in s, |F θ * G θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in s, M * |G θ| := by
        refine setIntegral_mono_on hFGint.abs ((hReInt.abs.const_mul M)) hsmeas fun θ hθ => ?_
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hM θ hθ) (abs_nonneg _)
    _ = M * ∫ θ in s, |G θ| := by rw [MeasureTheory.integral_const_mul]
    _ ≤ M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U ξ)) :=
        mul_le_mul_of_nonneg_left hCS hMnn

/-- **A finite tail integral has a null-sequence of small values escaping to `−∞`.** For a
nonnegative measurable `f` with finite integral over `Iic ξ₀`, there is a sequence `ξ n → −∞` inside
`Iic ξ₀` along which `f (ξ n) → 0`: for each `n`, the set `{ξ ≤ ξ₀ - n | f ξ < 1/(n+1)}` is
nonempty, since otherwise `f ≥ 1/(n+1)` on the infinite-measure set `Iic (ξ₀ - n)`, forcing an
infinite integral. -/
theorem exists_seq_tendsto_zero_atBot_of_lintegral_ne_top {f : ℝ → ℝ} {ξ₀ : ℝ}
    (hfmeas : Measurable f) (hfnn : ∀ ξ, 0 ≤ f ξ)
    (hfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (f ξ)) ≠ ⊤) :
    ∃ ξ : ℕ → ℝ, (∀ n, ξ n ≤ ξ₀) ∧ Tendsto ξ atTop atBot ∧
      Tendsto (fun n => f (ξ n)) atTop (𝓝 0) := by
  have hncast : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have key : ∀ n : ℕ, ∃ x : ℝ, x ≤ ξ₀ - n ∧ f x < 1 / ((n : ℝ) + 1) := by
    intro n
    by_contra hcon0
    have hcon : ∀ x : ℝ, x ≤ ξ₀ - (n : ℝ) → 1 / ((n : ℝ) + 1) ≤ f x := by
      intro x hx
      by_contra hlt
      exact hcon0 ⟨x, hx, lt_of_not_ge hlt⟩
    -- `f ≥ 1/(n+1)` on `Iic (ξ₀ - n)`, an infinite-measure set, forces an infinite integral
    have hsub : Iic (ξ₀ - (n : ℝ)) ⊆ Iic ξ₀ := Iic_subset_Iic.mpr (by linarith [hncast n])
    have hmono : (∫⁻ _ξ in Iic (ξ₀ - (n : ℝ)), ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        ≤ ∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (f ξ) := by
      refine le_trans ?_ (lintegral_mono_set hsub)
      refine setLIntegral_mono hfmeas.ennreal_ofReal (fun ξ hξ => ?_)
      exact ENNReal.ofReal_le_ofReal (hcon ξ (mem_Iic.mp hξ))
    rw [setLIntegral_const, Real.volume_Iic] at hmono
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    exact hfin (top_le_iff.mp (le_trans (by rw [ENNReal.mul_top hpos.ne']) hmono))
  choose ξ hξ using key
  refine ⟨ξ, fun n => le_trans (hξ n).1 (by linarith [hncast n]), ?_, ?_⟩
  · refine tendsto_atBot_mono (fun n => (hξ n).1) ?_
    exact tendsto_atBot_add_const_left _ ξ₀
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => hfnn _) (fun n => (hξ n).2.le) h1

/-- **A finite tail integral has a null-sequence of small values escaping to `−∞`, avoiding a null
set.** Strengthening of `exists_seq_tendsto_zero_atBot_of_lintegral_ne_top`: if additionally a
predicate `P` holds almost everywhere, the escaping sequence can be chosen inside `{ξ | P ξ}`.  For
each `n` the small-value tail set `{ξ ≤ ξ₀ - n | f ξ < 1/(n+1)}` has infinite measure (else the
integral diverges), so removing the null set `{¬P}` leaves it nonempty. -/
theorem exists_seq_tendsto_zero_atBot_of_lintegral_ne_top_ae {f : ℝ → ℝ} {ξ₀ : ℝ} {P : ℝ → Prop}
    (hfmeas : Measurable f) (hfnn : ∀ ξ, 0 ≤ f ξ)
    (hfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (f ξ)) ≠ ⊤)
    (hP : ∀ᵐ ξ : ℝ, P ξ) :
    ∃ ξ : ℕ → ℝ, (∀ n, ξ n ≤ ξ₀) ∧ (∀ n, P (ξ n)) ∧ Tendsto ξ atTop atBot ∧
      Tendsto (fun n => f (ξ n)) atTop (𝓝 0) := by
  have hncast : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  set N : Set ℝ := {ξ : ℝ | ¬ P ξ} with hN
  have hNnull : volume N = 0 := hP
  have key : ∀ n : ℕ, ∃ x : ℝ, x ≤ ξ₀ - n ∧ f x < 1 / ((n : ℝ) + 1) ∧ P x := by
    intro n
    set T : Set ℝ := {x : ℝ | x ≤ ξ₀ - (n : ℝ) ∧ f x < 1 / ((n : ℝ) + 1)} with hT
    have hTmeas : MeasurableSet T :=
      (measurableSet_Iic).inter (measurableSet_lt hfmeas measurable_const)
    -- `T` has infinite measure: else `Iic (ξ₀-n) ⊆ T ∪ Big` bounds `⊤` by finite mass
    set Big : Set ℝ := {x : ℝ | x ≤ ξ₀ - (n : ℝ) ∧ 1 / ((n : ℝ) + 1) ≤ f x} with hBig
    have hBigsub : Big ⊆ Iic ξ₀ := fun x hx => mem_Iic.mpr (by linarith [hx.1, hncast n])
    have hBigmeas : MeasurableSet Big :=
      measurableSet_Iic.inter (measurableSet_le measurable_const hfmeas)
    have hcompl : Iic (ξ₀ - (n : ℝ)) ⊆ T ∪ Big := by
      intro x hx
      by_cases hlt : f x < 1 / ((n : ℝ) + 1)
      · exact Or.inl ⟨mem_Iic.mp hx, hlt⟩
      · exact Or.inr ⟨mem_Iic.mp hx, le_of_not_gt hlt⟩
    have hIicinf : volume (Iic (ξ₀ - (n : ℝ))) = ⊤ := by rw [Real.volume_Iic]
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    -- the large-value tail set carries only finite measure (Markov, restricted to `Iic ξ₀`)
    have hgefin : volume Big ≠ ⊤ := by
      intro hgeinf
      have hbig : (∫⁻ ξ in Big, ENNReal.ofReal (f ξ)) = ⊤ := by
        refine top_le_iff.mp ?_
        calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) * volume Big := by
              rw [hgeinf, ENNReal.mul_top hpos.ne']
          _ = ∫⁻ _ξ in Big, ENNReal.ofReal (1 / ((n : ℝ) + 1)) := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ ξ in Big, ENNReal.ofReal (f ξ) := by
              refine setLIntegral_mono hfmeas.ennreal_ofReal (fun ξ hξ => ?_)
              exact ENNReal.ofReal_le_ofReal hξ.2
      exact hfin (top_le_iff.mp (hbig ▸ lintegral_mono_set hBigsub))
    have hTinf : volume T = ⊤ := by
      have hle : volume (Iic (ξ₀ - (n : ℝ))) ≤ volume T + volume Big :=
        (measure_mono hcompl).trans (measure_union_le T Big)
      rw [hIicinf] at hle
      by_contra hfinT
      exact (ENNReal.add_ne_top.mpr ⟨hfinT, hgefin⟩) (top_le_iff.mp hle)
    -- removing the null set `N` keeps `T` nonempty
    have hTN : volume (T \ N) = ⊤ := by
      rw [measure_diff_null hNnull]; exact hTinf
    obtain ⟨x, hxT, hxN⟩ := nonempty_of_measure_ne_zero (by rw [hTN]; exact ENNReal.top_ne_zero)
    exact ⟨x, hxT.1, hxT.2, not_not.mp hxN⟩
  choose ξ hξ using key
  refine ⟨ξ, fun n => le_trans (hξ n).1 (by linarith [hncast n]), fun n => (hξ n).2.2, ?_, ?_⟩
  · refine tendsto_atBot_mono (fun n => (hξ n).1) ?_
    exact tendsto_atBot_add_const_left _ ξ₀
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => hfnn _) (fun n => (hξ n).2.1.le) h1

/-- **Upper flux limit for a ring potential (discharging `hTop`).** If the full circles of every
collar radius `ξ ∈ (log r₀, 0)` lie in `U` and `u` is a ring potential on the round collar
`{r₀ < |z| < 1}` with affine circle mean `2π + b·ξ`, then the rough flux of `u` on `U` tends to the
boundary slope `b` as the log-radius rises to `0`: on the collar the indicator is trivial, so the
rough flux agrees with the round-annulus ring flux, whose boundary limit is `b`. -/
theorem roughFlux_tendsto_slope_ringPotential {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hu : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ) :
    Tendsto (roughFlux u U) (𝓝[<] (0 : ℝ)) (𝓝 b) := by
  have hring := ringFlux_tendsto_slope h0 h1 hu hcont hone hrange hslope
  refine hring.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (Real.log_neg h0 h1)] with ξ hξ
  exact (roughFlux_eq_ringFlux (fun θ => hcollar ξ hξ.1 hξ.2 θ)).symm

/-- **A.e. slice integrability of the squared gradient from finite total energy (`W1c`, a.e.).** For
`u` harmonic on the open set `U` with finite Dirichlet energy, at almost every log-radius `ξ ≤ ξ₀`
the squared log-polar gradient `θ ↦ normSq (expGrad u (ξ+iθ))` is integrable on the angular slice
`angularSlice U ξ`: the slice lower-integral is the `ξ`-integrand of a finite total, hence a.e.
finite by Markov, and finiteness of `∫⁻ ofReal` of a nonnegative function is integrability. -/
theorem ae_integrableOn_slice_normSq_of_energy_lt_top {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    {ξ₀ : ℝ} (hDfin : dirichletEnergy u U ≠ ⊤) :
    ∀ᵐ ξ : ℝ ∂(volume.restrict (Iic ξ₀)),
      IntegrableOn (fun θ : ℝ =>
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (angularSlice U ξ) := by
  -- the slice lower-integral is measurable in `ξ` and its `ξ`-integral is finite
  set g : ℝ → ℝ≥0∞ := fun ξ => ∫⁻ θ in Ioo (-π) π,
    (angularSlice U ξ).indicator
      (fun θ' => ENNReal.ofReal
        (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))) θ with hg
  have hWopen : IsOpen {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π ∧
      Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ U} := by
    have hcontmap : Continuous fun p : ℝ × ℝ =>
        Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
    have : {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π ∧
          Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ U}
        = (Prod.snd ⁻¹' Ioo (-π) π) ∩
          ((fun p : ℝ × ℝ => Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ⁻¹' U) := by
      ext p; simp only [mem_setOf_eq, mem_inter_iff, mem_preimage]
    rw [this]; exact (isOpen_Ioo.preimage continuous_snd).inter (hU.preimage hcontmap)
  have hgmeas : Measurable g := by
    refine Measurable.lintegral_prod_right (ν := volume.restrict (Ioo (-π) π)) ?_
    have hjoint : Measurable fun p : ℝ × ℝ =>
        {q : ℝ × ℝ | q.2 ∈ Ioo (-π) π ∧
          Complex.exp ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ U}.indicator
          (fun q : ℝ × ℝ => ENNReal.ofReal
            (Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)))) p :=
      (ENNReal.measurable_ofReal.comp (measurable_normSq_expGrad_logPolar u)).indicator
        hWopen.measurableSet
    have hfeq : (Function.uncurry fun ξ : ℝ => (angularSlice U ξ).indicator
          (fun θ' => ENNReal.ofReal
            (Complex.normSq (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)))))
        = fun p : ℝ × ℝ => {q : ℝ × ℝ | q.2 ∈ Ioo (-π) π ∧
            Complex.exp ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ U}.indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal
              (Complex.normSq (expGrad u ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)))) p := by
      funext p
      rw [Function.uncurry_apply_pair]
      by_cases hp : p ∈ {q : ℝ × ℝ | q.2 ∈ Ioo (-π) π ∧
          Complex.exp ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ∈ U}
      · rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem (show p.2 ∈ angularSlice U p.1 from hp)]
      · rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (show p.2 ∉ angularSlice U p.1 from hp)]
    rw [hfeq]; exact hjoint
  have hgfin : (∫⁻ ξ in Iic ξ₀, g ξ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hDfin ?_
    rw [(setLIntegral_congr Iio_ae_eq_Iic).symm,
      ← dirichletEnergy_inter_ball_eq_lintegral_slice u hU ξ₀]
    exact dirichletEnergy_mono (fun z hz => hz.1)
  -- Markov: a.e. `ξ` the slice lower-integral is finite, giving slice integrability
  filter_upwards [ae_lt_top hgmeas hgfin] with ξ hξ
  have hsmeas : MeasurableSet (angularSlice U ξ) := (isOpen_angularSlice hU ξ).measurableSet
  have hslicefin : (∫⁻ θ in angularSlice U ξ,
      ENNReal.ofReal (Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))) ≠ ⊤ := by
    simp only [hg] at hξ
    rw [lintegral_indicator hsmeas, Measure.restrict_restrict hsmeas,
      Set.inter_eq_self_of_subset_left (angularSlice_subset U ξ)] at hξ
    exact hξ.ne
  refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hslicefin
  · exact ((measurable_normSq_expGrad_logPolar u).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun θ => Complex.normSq_nonneg _)

/-- **Lower flux limit along a sequence (discharging `hBot`).** For `u` harmonic on the open set
`U`, suppose the potential admits a boundary modulus `Mbound ξ` dominating `|u|` on every angular
slice with `Mbound → 0` as `ξ → −∞` (the potential vanishing at the origin, `F1`), the slice
radial-derivative and squared gradient are integrable on the slice at each log-radius (`W1c`), and
the tail slice-energy integral `∫⁻_{Iic ξ₀} sliceEnergyU` is finite (`F2`, from `D(u; U) < ∞`).
Then there is a sequence `ξ n → −∞` along which the rough flux tends to `0`: pick the sequence of
the finite tail integral along which the slice energy vanishes, and squeeze the per-slice C.–S.
bound `|roughFlux| ≤ Mbound · √(2π) · √(sliceEnergyU)` by `Mbound → 0` and `sliceEnergyU → 0`. -/
theorem exists_seq_roughFlux_tendsto_zero_atBot {u : ℂ → ℝ} {U : Set ℂ} {Mbound : ℝ → ℝ} {ξ₀ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hMbnn : ∀ ξ, 0 ≤ Mbound ξ)
    (hMb : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ Mbound ξ)
    (hMbtop : Tendsto Mbound atBot (𝓝 0))
    (hReInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hEmeas : Measurable (sliceEnergyU u U))
    (hEfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ)) ≠ ⊤) :
    ∃ ξ : ℕ → ℝ, Tendsto ξ atTop atBot ∧
      Tendsto (fun n => roughFlux u U (ξ n)) atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hEnn : ∀ ξ, 0 ≤ sliceEnergyU u U ξ := fun ξ =>
    setIntegral_nonneg (isOpen_angularSlice hU ξ).measurableSet
      fun θ _ => Complex.normSq_nonneg _
  -- `F2`: the sequence escaping to `−∞` along which the slice energy vanishes
  obtain ⟨ξ, hξle, hξbot, hξE⟩ :=
    exists_seq_tendsto_zero_atBot_of_lintegral_ne_top hEmeas hEnn hEfin
  refine ⟨ξ, hξbot, ?_⟩
  -- the per-slice Cauchy–Schwarz bound, applied along the sequence
  have hbound : ∀ n, |roughFlux u U (ξ n)|
      ≤ Mbound (ξ n) * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n))) := fun n =>
    abs_roughFlux_le_slice hU hu (hMbnn (ξ n)) (hMb (ξ n)) (hReInt (ξ n)) (hEInt (ξ n))
  -- the bounding sequence tends to `0`: `Mbound (ξ n) → 0` and `√(sliceEnergyU (ξ n)) → 0`
  have hMto : Tendsto (fun n => Mbound (ξ n)) atTop (𝓝 0) := hMbtop.comp hξbot
  have hEto : Tendsto (fun n => Real.sqrt (sliceEnergyU u U (ξ n))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hξE
    simpa [Function.comp_def, Real.sqrt_zero] using this
  have hinner : Tendsto (fun n => Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n)))
      atTop (𝓝 (Real.sqrt (2 * π) * 0)) :=
    (tendsto_const_nhds (x := Real.sqrt (2 * π))).mul hEto
  rw [mul_zero] at hinner
  have hprod : Tendsto (fun n =>
      Mbound (ξ n) * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n))))
      atTop (𝓝 (0 * 0)) := hMto.mul hinner
  rw [mul_zero] at hprod
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _) hbound hprod

/-- **Slice integrability of the real part from the squared gradient.** On the finite-measure
angular slice, integrability of `θ ↦ normSq (expGrad u)` implies integrability of
`θ ↦ Re (expGrad u)`: `|Re| ≤ √(normSq)` is dominated by the integrable `(1 + normSq)/2`. -/
theorem integrableOn_slice_re_of_normSq {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (ξ : ℝ)
    (hE : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ)) :
    IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ) := by
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hsfin : volume s ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono (hs ▸ angularSlice_subset U ξ))
  -- `θ ↦ Re (expGrad u)` is continuous on the open slice, hence a.e.-strongly-measurable
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (volume.restrict s) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hsmeas
    intro θ hθ
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hθ.2
    have houter : ContinuousAt (fun w : ℂ => (expGrad u w).re)
        ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      Complex.continuous_re.continuousAt.comp hdC.continuousAt
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    exact (ContinuousAt.comp (g := fun w : ℂ => (expGrad u w).re)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) houter hinner).continuousWithinAt
  refine ((hE.add (integrableOn_const (C := (1 : ℝ)) hsfin (by simp))).const_mul
    (1 / 2)).mono' hmeas ?_
  filter_upwards [ae_restrict_mem hsmeas] with θ _
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [Complex.normSq_apply]
  nlinarith [abs_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re,
    sq_abs (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re,
    sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im,
    sq_nonneg (|(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| - 1)]

/-- **Lower flux limit along a sequence, from a uniform potential bound and finite energy.** For `u`
harmonic on the open set `U` with finite Dirichlet energy, if the potential is uniformly bounded by
a constant `M` on every angular slice, then there is a sequence `ξ n → −∞` along which the rough
flux tends to `0`.  The escaping sequence is chosen — via the co-null null-value selector — at radii
whose slice squared gradient is integrable (a.e. from finite energy) and whose slice energy
vanishes; the per-slice Cauchy–Schwarz bound `|roughFlux| ≤ M · √(2π) · √(sliceEnergyU)` squeezed by
`sliceEnergyU (ξ n) → 0`.  Unlike `exists_seq_roughFlux_tendsto_zero_atBot`, this needs neither
`Mbound → 0` nor slice integrability at every log-radius — only the uniform bound and `D(u; U) < ∞`,
which the keystone data (`0 ≤ u ≤ 1`) supplies directly. -/
theorem exists_seq_roughFlux_tendsto_zero_atBot' {u : ℂ → ℝ} {U : Set ℂ} {M : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hMnn : 0 ≤ M)
    (hbdd : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hDfin : dirichletEnergy u U ≠ ⊤) :
    ∃ ξ : ℕ → ℝ, Tendsto ξ atTop atBot ∧
      Tendsto (fun n => roughFlux u U (ξ n)) atTop (𝓝 0) := by
  have hπ := Real.pi_pos
  have hEnn : ∀ ξ, 0 ≤ sliceEnergyU u U ξ := fun ξ =>
    setIntegral_nonneg (isOpen_angularSlice hU ξ).measurableSet
      fun θ _ => Complex.normSq_nonneg _
  -- `F2`: the tail slice-energy integral is finite (from `D(u; U) < ∞`)
  have hEfin : (∫⁻ ξ in Iic (0 : ℝ), ENNReal.ofReal (sliceEnergyU u U ξ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (setLIntegral_tail_ofReal_sliceEnergyU_le hU 0)
  -- `W1c` a.e.: the slice squared gradient is integrable at a.e. log-radius below `0`
  have hae : ∀ᵐ ξ : ℝ ∂(volume.restrict (Iic (0 : ℝ))),
      IntegrableOn (fun θ : ℝ =>
        Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (angularSlice U ξ) :=
    ae_integrableOn_slice_normSq_of_energy_lt_top hU hDfin
  -- pick the escaping sequence at integrable, low-energy log-radii
  obtain ⟨ξ, hξle, hξInt, hξbot, hξE⟩ :=
    exists_seq_tendsto_zero_atBot_of_lintegral_ne_top_ae (measurable_sliceEnergyU hU) hEnn hEfin
      ((ae_restrict_iff' measurableSet_Iic).mp hae)
  refine ⟨ξ, hξbot, ?_⟩
  -- along the sequence, the log-radii lie in `Iic 0`, so the a.e.-selected integrability applies
  have hEInt : ∀ n, IntegrableOn (fun θ : ℝ =>
      Complex.normSq (expGrad u ((ξ n : ℂ) + (θ : ℂ) * Complex.I))) (angularSlice U (ξ n)) :=
    fun n => hξInt n (hξle n)
  have hReInt : ∀ n, IntegrableOn (fun θ : ℝ =>
      (expGrad u ((ξ n : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U (ξ n)) :=
    fun n => integrableOn_slice_re_of_normSq hU hu (ξ n) (hEInt n)
  -- the per-slice Cauchy–Schwarz bound, with the uniform constant `M`
  have hbound : ∀ n, |roughFlux u U (ξ n)|
      ≤ M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n))) := fun n =>
    abs_roughFlux_le_slice hU hu hMnn (hbdd (ξ n)) (hReInt n) (hEInt n)
  -- squeeze: `√(sliceEnergyU (ξ n)) → 0`
  have hEto : Tendsto (fun n => Real.sqrt (sliceEnergyU u U (ξ n))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hξE
    simpa [Function.comp_def, Real.sqrt_zero] using this
  have hinner : Tendsto (fun n => Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n)))
      atTop (𝓝 (Real.sqrt (2 * π) * 0)) :=
    (tendsto_const_nhds (x := Real.sqrt (2 * π))).mul hEto
  rw [mul_zero] at hinner
  have hprod : Tendsto (fun n =>
      M * (Real.sqrt (2 * π) * Real.sqrt (sliceEnergyU u U (ξ n)))) atTop (𝓝 (M * 0)) :=
    (tendsto_const_nhds (x := M)).mul hinner
  rw [mul_zero] at hprod
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun n => abs_nonneg _) hbound hprod

/-- **The slope is bounded by the total energy (sequential, windowed).** Given the upper flux limit
`hTop`, a sequence `ξ n → −∞` along which the rough flux tends to `0` (`hBotSeq`), and the windowed
increment inequality `roughFlux ζ₂ − roughFlux ζ₁ ≤ D` over the window family `ζ₁ ≤ ζ₂ < 0`, the
boundary slope is bounded by the total energy: fix an inner radius and let the outer radius rise to
`0` to get `b − roughFlux ζ₁ ≤ D`; then let `ζ₁` run along the null sequence to send
`roughFlux ζ₁ → 0`, giving `b ≤ D`.  This is the shape consumable by the keystone `U` (whose small
circles are blocked by the continuum on its frontier, so the full-circle hypothesis of
`slope_le_energy` fails): only the rough windows that genuinely exist are used. -/
theorem slope_le_energy_of_windowed_seq {u : ℂ → ℝ} {U : Set ℂ} {b D : ℝ} {ξ : ℕ → ℝ}
    (hTop : Tendsto (roughFlux u U) (𝓝[<] (0 : ℝ)) (𝓝 b))
    (hBotSeq : Tendsto ξ atTop atBot ∧ Tendsto (fun n => roughFlux u U (ξ n)) atTop (𝓝 0))
    (hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 → roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ D) :
    b ≤ D := by
  obtain ⟨hξbot, hξ0⟩ := hBotSeq
  -- fix an inner radius `ζ₁` and let the outer radius rise to `0`: `b − roughFlux ζ₁ ≤ D`
  have hfix : ∀ ζ₁ : ℝ, ζ₁ < 0 → b - roughFlux u U ζ₁ ≤ D := by
    intro ζ₁ hζ₁
    have hlim : Tendsto (fun ζ₂ : ℝ => roughFlux u U ζ₂ - roughFlux u U ζ₁)
        (𝓝[<] (0 : ℝ)) (𝓝 (b - roughFlux u U ζ₁)) := hTop.sub_const _
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hζ₁, self_mem_nhdsWithin] with ζ₂ hζ₂mem hζ₂neg
    exact hwin ζ₁ ζ₂ hζ₂mem.1.le hζ₂neg
  -- run `ζ₁` along the null sequence `ξ n → −∞`: `roughFlux (ξ n) → 0`, giving `b ≤ D`
  have hlim2 : Tendsto (fun n : ℕ => b - roughFlux u U (ξ n)) atTop (𝓝 (b - 0)) :=
    hξ0.const_sub b
  rw [sub_zero] at hlim2
  refine le_of_tendsto hlim2 ?_
  have hev : ∀ᶠ n in atTop, ξ n < 0 := hξbot.eventually (eventually_lt_atBot 0)
  filter_upwards [hev] with n hn
  exact hfix (ξ n) hn

/-- **Keystone slope bound for a ring potential.** Assemble the discharged flux limits into the
final consumable slope inequality `b ≤ D(u; U)`.  From the collar full-circle mapping and
ring-potential data the upper flux limit `hTop` is `roughFlux_tendsto_slope_ringPotential`; from the
boundary modulus (`F1`), the a.e.-slice integrabilities (`W1c`), and the finite tail slice-energy
integral (`F2`) the null-sequence flux limit is `exists_seq_roughFlux_tendsto_zero_atBot`; the
windowed increment inequality `hwin` — the rough-window flux–energy content over the window family
that genuinely exists for the keystone `U` — is supplied as a hypothesis, and
`slope_le_energy_of_windowed_seq` combines them. -/
theorem slope_le_energy_ringPotential {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ} {Mbound : ℝ → ℝ} {ξ₀ : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hMbnn : ∀ ξ, 0 ≤ Mbound ξ)
    (hMb : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ Mbound ξ)
    (hMbtop : Tendsto Mbound atBot (𝓝 0))
    (hReInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hEmeas : Measurable (sliceEnergyU u U))
    (hEfin : (∫⁻ ξ in Iic ξ₀, ENNReal.ofReal (sliceEnergyU u U ξ)) ≠ ⊤)
    (hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal) :
    b ≤ (dirichletEnergy u U).toReal := by
  have hTop := roughFlux_tendsto_slope_ringPotential h0 h1 hcollar hucollar hcont hone hrange hslope
  have hBotSeq := exists_seq_roughFlux_tendsto_zero_atBot hU hu hMbnn hMb hMbtop hReInt hEInt
    hEmeas hEfin
  obtain ⟨ξ, hξbot, hξ0⟩ := hBotSeq
  exact slope_le_energy_of_windowed_seq (ξ := ξ) hTop ⟨hξbot, hξ0⟩ hwin

/-- **Keystone slope bound for a ring potential (self-contained flux limits).** The keystone-shaped
version of `slope_le_energy_ringPotential`: from the collar full-circle mapping and ring-potential
data (giving the upper flux limit `hTop`), the uniform bound `0 ≤ u ≤ 1` on `U`, and finite
Dirichlet energy `D(u; U) < ∞`, the boundary slope is bounded by the total energy `b ≤ D(u; U)`.

All the auxiliary hypotheses of `slope_le_energy_ringPotential` are discharged here:
* the lower flux limit is `exists_seq_roughFlux_tendsto_zero_atBot'`, which needs only the uniform
  potential bound and `D(u; U) < ∞` — measurability of `sliceEnergyU`
  (`measurable_sliceEnergyU`), the finite tail slice-energy integral
  (`setLIntegral_tail_ofReal_sliceEnergyU_le`), and a.e. slice integrability of the squared
  gradient (`ae_integrableOn_slice_normSq_of_energy_lt_top`, threaded into the sequence) are
  internal;
* the windowed increment inequality `hwin` — the rough-window flux–energy content over the window
  family that genuinely exists for the keystone `U` — remains a hypothesis (its discharge is the
  varying-domain radial flux–energy exchange, not available for the keystone `U` whose small circles
  are blocked by the continuum on its frontier). -/
theorem slope_le_energy_ringPotential' {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hDfin : dirichletEnergy u U ≠ ⊤)
    (hwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal) :
    b ≤ (dirichletEnergy u U).toReal := by
  have hTop := roughFlux_tendsto_slope_ringPotential h0 h1 hcollar hucollar hcont hone hrange hslope
  -- the uniform slice bound `|u| ≤ 1` from `0 ≤ u ≤ 1` on `U`
  have hbdd : ∀ ξ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
    intro ξ θ hθ
    obtain ⟨hnn, hle⟩ := hrangeU _ hθ.2
    rw [abs_of_nonneg hnn]; exact hle
  obtain ⟨ξ, hξbot, hξ0⟩ :=
    exists_seq_roughFlux_tendsto_zero_atBot' hU hu (by norm_num : (0:ℝ) ≤ 1) hbdd hDfin
  exact slope_le_energy_of_windowed_seq (ξ := ξ) hTop ⟨hξbot, hξ0⟩ hwin

/-! ### The windowed increment inequality from the level-set exhaustion

The windowed increment inequality `hwin` — `roughFlux ζ₂ − roughFlux ζ₁ ≤ D(u; U)` for
`ζ₁ ≤ ζ₂ < 0` — is produced from the **level-set exhaustion**: writing `roughFluxδ u U δ`
(= the rough flux of the superlevel set `V_δ = {u > δ} ∩ U`, `roughFluxδ_eq_roughFlux_superLevelU`)
and letting `δ ↓ 0`, the rough flux is recovered (`tendsto_roughFluxδ_atZero`).  It therefore
suffices to bound the δ-increment `roughFluxδ ζ₂ − roughFluxδ ζ₁ ≤ D(u; U)` uniformly in `δ > 0`;
this is the per-level flux–energy content of the superlevel set (whose closure meets `U` compactly
inside any window `{e^{ζ₁} < |z| < e^{ζ₂}}`, `ζ₂ < 0`, so all slab bounds apply). -/

/-- **The windowed increment inequality from the level-set δ-increment bound.** For `u` harmonic and
strictly positive on the open set `U`, uniformly bounded by `1` on `U`, with the slice
radial-derivative integrand integrable on every slice, if for every window `ζ₁ ≤ ζ₂ < 0` and every
`δ > 0` the level-set δ-rough-flux increment is bounded by `D(u; U)`, then the rough-flux increment
is bounded by `D(u; U)` on every such window.  This packages the `δ → 0` recovery of the rough flux
into the windowed increment inequality `hwin` consumed by `slope_le_energy_ringPotential'`. -/
theorem roughFlux_sub_le_dirichletEnergy_rough {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hδwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 → ∀ δ : ℝ, 0 < δ →
      roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ (dirichletEnergy u U).toReal) :
    ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
  intro ζ₁ ζ₂ h12 hζ₂
  -- the uniform `|u| ≤ 1` slice bound
  have hbdd : ∀ ξ : ℝ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
    intro ξ θ hθ
    obtain ⟨hnn, hle⟩ := hrangeU _ hθ.2
    rw [abs_of_nonneg hnn]; exact hle
  -- slice radial-derivative integrand integrable at each of the two log-radii
  have hRe : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ) :=
    fun ξ => integrableOn_slice_re_of_normSq hU hu ξ (hEInt ξ)
  exact roughFlux_sub_le_of_roughFluxδ_sub_le hU hu hpos (by norm_num : (0:ℝ) ≤ 1)
    (hbdd ζ₁) (hbdd ζ₂) (hRe ζ₁) (hRe ζ₂) (hδwin ζ₁ ζ₂ h12 hζ₂)

/-- **Keystone slope bound for a ring potential (level-set δ-increment residual).** The
`slope_le_energy_ringPotential'` slope bound `b ≤ D(u; U)`, with the windowed increment hypothesis
`hwin` eliminated in favour of the strictly more local **level-set δ-increment bound** `hδwin`:
the flux–energy content of each superlevel set `{u > δ} ∩ U` (whose closure sits compactly inside
`U` on any window `{e^{ζ₁} < |z| < e^{ζ₂}}`, `ζ₂ < 0`).  The `δ → 0` recovery
(`roughFlux_sub_le_dirichletEnergy_rough`) turns `hδwin` into `hwin`. -/
theorem slope_le_energy_ringPotential'' {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤)
    (hδwin : ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 → ∀ δ : ℝ, 0 < δ →
      roughFluxδ u U δ ζ₂ - roughFluxδ u U δ ζ₁ ≤ (dirichletEnergy u U).toReal) :
    b ≤ (dirichletEnergy u U).toReal :=
  slope_le_energy_ringPotential' h0 h1 hU hu hcollar hucollar hcont hone hrange hslope hrangeU hDfin
    (roughFlux_sub_le_dirichletEnergy_rough hU hu hpos hrangeU hEInt hδwin)

/-! ### The truncated per-arc integration-by-parts identity for a superlevel arc

On a single angular arc `(a, b)` of the superlevel slice `V_δ ∩ C_{e^ξ}` — whose interior maps
into `{u > δ} ∩ U`, so `u > δ` throughout the open arc, and whose endpoints escape the superlevel
set, where `u = δ` — the truncated potential `(u − δ)⁺` vanishes at both endpoints and equals
`u − δ` on the interior.  The two sequential boundary bricks therefore annihilate the
integration-by-parts boundary term, giving the exact per-arc identity
`∫_a^b (u − δ)⁺ · Re (deriv (expGrad u)) = ∫_a^b (Im (expGrad u))²`. -/

/-- **Truncated per-arc flux identity.** For `u` harmonic on an open set `U`, a log-radius `ξ` and a
closed arc `[a, b]` whose interior maps under `θ ↦ e^{ξ+θi}` into `U` with `δ < u` throughout, and
whose endpoints map to superlevel-boundary points where `u = δ`, with the slice squared gradient and
slice radial-derivative integrand integrable, the angle integral over the arc of
`(u(e^{ξ+θi}) − δ)⁺ · Re (deriv (expGrad u))` equals the integral of `(Im (expGrad u))²`.  The
truncation `(u − δ)⁺` vanishes at both endpoints, so the two sequential boundary bricks kill the
integration-by-parts boundary term exactly as in `integral_uexp_re_deriv_expGrad_arc`. -/
theorem integral_posPart_re_deriv_expGrad_arc {u : ℂ → ℝ} {U : Set ℂ} {δ ξ a b : ℝ}
    (hU : IsOpen U) (hab : a < b)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (harc : ∀ θ ∈ Ioo a b, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hsup : ∀ θ ∈ Ioo a b, δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
    (hcont : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Icc a b))
    (hslice : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (Ioo a b))
    (hg'int : IntegrableOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (Ioo a b))
    (ha0 : u (Complex.exp ((ξ : ℂ) + (a : ℂ) * Complex.I)) = δ)
    (hb0 : u (Complex.exp ((ξ : ℂ) + (b : ℂ) * Complex.I)) = δ) :
    ∫ θ in a..b, (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in a..b, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  set uexp : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with huexp
  set f : ℝ → ℝ := fun θ => (uexp θ - δ)⁺ with hf
  set g : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgdef
  set g' : ℝ → ℝ :=
    fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hg'def
  -- differentiability on the open arc
  have hdiffR : ∀ θ ∈ Ioo a b,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ hθ =>
    differentiableAt_of_harmonicOnNhd hu (harc θ hθ)
  have hdiffC : ∀ θ ∈ Ioo a b,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ hθ =>
    expGrad_differentiableAt_open hU hu (harc θ hθ)
  -- `uexp` is continuous on the open arc, and on the interior `f = uexp - δ` (since `uexp > δ`)
  have huexpcont : ContinuousOn uexp (Ioo a b) := (hcont.mono Ioo_subset_Icc_self)
  -- `f = (uexp - δ)⁺` has, on the open arc, derivative `-Im (expGrad u)` (`= deriv uexp`)
  have hfderiv : ∀ θ ∈ Ioo a b, HasDerivAt f (deriv f θ) θ := by
    intro θ hθ
    -- near `θ`, `uexp > δ`, so `f =ᶠ uexp - δ` and shares its derivative
    have hgtθ : δ < uexp θ := hsup θ hθ
    have hnhd : ∀ᶠ t in nhds θ, δ < uexp t := by
      have hcθ : ContinuousAt uexp θ :=
        (huexpcont.continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
      exact hcθ.eventually_const_lt hgtθ
    have hnhdsub : ∀ᶠ t in nhds θ, t ∈ Ioo a b := Ioo_mem_nhds hθ.1 hθ.2
    have hfeq : f =ᶠ[nhds θ] fun t => uexp t - δ := by
      filter_upwards [hnhd] with t ht
      rw [hf]; simp only [posPart_eq_self.mpr (by linarith : (0:ℝ) ≤ uexp t - δ)]
    have huderiv : HasDerivAt uexp (-(g θ)) θ := hasDerivAt_uexp_angular (hdiffR θ hθ)
    have hshift : HasDerivAt (fun t => uexp t - δ) (-(g θ)) θ := by
      simpa using huderiv.sub_const δ
    have hfd : HasDerivAt f (-(g θ)) θ := hshift.congr_of_eventuallyEq hfeq
    rw [hfd.deriv]; exact hfd
  have hfg : ∀ θ ∈ Ioo a b, deriv f θ = -g θ := by
    intro θ hθ
    have hgtθ : δ < uexp θ := hsup θ hθ
    have hnhd : ∀ᶠ t in nhds θ, δ < uexp t := by
      have hcθ : ContinuousAt uexp θ := (huexpcont.continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
      exact hcθ.eventually_const_lt hgtθ
    have hfeq : f =ᶠ[nhds θ] fun t => uexp t - δ := by
      filter_upwards [hnhd] with t ht
      rw [hf]; simp only [posPart_eq_self.mpr (by linarith : (0:ℝ) ≤ uexp t - δ)]
    have huderiv : HasDerivAt uexp (-(g θ)) θ := hasDerivAt_uexp_angular (hdiffR θ hθ)
    have hshift : HasDerivAt (fun t => uexp t - δ) (-(g θ)) θ := by
      simpa using huderiv.sub_const δ
    exact (hshift.congr_of_eventuallyEq hfeq).deriv
  have hgderiv : ∀ θ ∈ Ioo a b, HasDerivAt g (g' θ) θ := by
    intro θ hθ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ hθ)
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [hgdef, hg'def, Function.comp, Complex.mul_im] using hcomp
  have hgcont : ContinuousOn g (Ioo a b) := fun θ hθ =>
    (hgderiv θ hθ).continuousAt.continuousWithinAt
  -- `(deriv f)² = g² ≤ normSq (expGrad u)` gives square-integrability of `deriv f`
  have hf2 : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Ioo a b) := by
    have hg2meas : AEStronglyMeasurable (fun θ => (deriv f θ) ^ 2)
        (volume.restrict (Ioo a b)) := by
      refine ((hgcont.aestronglyMeasurable measurableSet_Ioo).pow 2).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [hfg θ hθ]; simp [hgdef]
    refine Integrable.mono' hslice hg2meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [hfg θ hθ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2
        ≤ Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
      rw [Complex.normSq_apply]; nlinarith [sq_nonneg
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
    simpa [hgdef] using this
  have hg2int : IntegrableOn (fun θ => (g θ) ^ 2) (Ioo a b) :=
    hf2.congr_fun (fun θ hθ => by rw [hfg θ hθ]; simp [hgdef]) measurableSet_Ioo
  have hgint : IntegrableOn g (Ioo a b) := by
    have hvol : volume (Ioo a b) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ) / 2) (Ioo a b) :=
      integrableOn_const hvol (by simp)
    have hsum : IntegrableOn (fun θ => (1 : ℝ) / 2 + (g θ) ^ 2 / 2) (Ioo a b) :=
      hconst.add (hg2int.div_const 2)
    have hdom : IntegrableOn (fun θ => (1 + (g θ) ^ 2) / 2) (Ioo a b) :=
      hsum.congr_fun (fun θ _ => by ring) measurableSet_Ioo
    refine hdom.mono' (hgcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|g θ| - 1), abs_nonneg (g θ), sq_abs (g θ)]
  -- `f` is continuous on the closed arc (composition of the Lipschitz `posPart` with `uexp - δ`)
  have hfcont : ContinuousOn f (Icc a b) := by
    have : ContinuousOn (fun θ => uexp θ - δ) (Icc a b) := hcont.sub continuousOn_const
    exact (lipschitzWith_posPart.continuous.comp_continuousOn this)
  -- endpoint vanishing: `uexp = δ` there, so `(uexp - δ)⁺ = 0`
  have hfa : f a = 0 := by
    rw [hf]; simp only [huexp, ha0, sub_self, posPart_zero]
  have hfb : f b = 0 := by
    rw [hf]; simp only [huexp, hb0, sub_self, posPart_zero]
  exact integral_mul_deriv_eq_integral_sq_of_endpoints_zero hab hfderiv hfg hgderiv hf2
    hfcont hgint hg'int hfa hfb

/-- **Window-general summed truncated per-slice flux identity.** Fix a log-radius `ξ`, a level `δ`,
and a window `(lo, hi)`.  On the windowed superlevel slice
`O = {θ ∈ (lo, hi) | e^{ξ+θi} ∈ U ∧ u > δ}` — with `u` harmonic on `U`, continuous on the closure of
the slice, `u = δ` at every circle boundary point of the superlevel set, the window seams `lo`, `hi`
escaping the superlevel set, and the slice squared gradient and slice radial-derivative integrand
integrable — the angle integral over the slice of
`(u − δ)⁺ · Re (deriv (expGrad u))` equals the integral of `(Im (expGrad u))²`: decompose `O` into
its countable disjoint open arcs (each with endpoints where `u = δ`) and sum the exact truncated
per-arc identities. -/
theorem setIntegral_windowSlice_posPart_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {δ ξ lo hi : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcont : ContinuousOn
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (closure {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}))
    (hEsc : ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ closure (superLevelU U u δ) →
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∉ superLevelU U u δ →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ)
    (hloOut : Complex.exp ((ξ : ℂ) + (lo : ℂ) * Complex.I) ∉ superLevelU U u δ)
    (hhiOut : Complex.exp ((ξ : ℂ) + (hi : ℂ) * Complex.I) ∉ superLevelU U u δ)
    (hsliceInt : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ})
    (hradInt : IntegrableOn
      (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}) :
    ∫ θ in {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ},
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in {θ' : ℝ | θ' ∈ Ioo lo hi ∧
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ},
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  classical
  set O : Set ℝ := {θ' : ℝ | θ' ∈ Ioo lo hi ∧
    Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} with hO
  have hOopen : IsOpen O := by
    have h1 : IsOpen (Ioo lo hi) := isOpen_Ioo
    have h2 : IsOpen {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} :=
      (isOpen_superLevelU hU hu δ).preimage (by fun_prop)
    exact h1.inter h2
  have hOsub : O ⊆ Ioo lo hi := fun _ hθ => hθ.1
  obtain ⟨S, hcount, hdisj, hunion, hSend⟩ := isOpen_eq_iUnion_Ioo hOopen hOsub
  have _ := hcount.to_subtype
  set F : ℝ → ℝ := fun θ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
      * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 with hG
  set s : S → Set ℝ := fun p => Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hs
  have hsu : O = ⋃ p : S, s p := by rw [hunion, hs, iUnion_subtype]
  have hsmeas : ∀ p : S, MeasurableSet (s p) := fun _ => measurableSet_Ioo
  have hsdisj : Pairwise (Function.onFun Disjoint s) := fun p q hpq =>
    hdisj p.2 q.2 (fun h => hpq (Subtype.ext h))
  have harcmem : ∀ p : S, ∀ θ ∈ s p, θ ∈ O := fun p θ hθ => hsu ▸ mem_iUnion.mpr ⟨p, hθ⟩
  have harcU : ∀ p : S, ∀ θ ∈ s p, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := fun p θ hθ =>
    (harcmem p θ hθ).2.1
  have harcSup : ∀ p : S, ∀ θ ∈ s p,
      δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun p θ hθ => (harcmem p θ hθ).2.2
  -- each arc's closed interval lies in the closure of `O` (interior in `O`, endpoints are limits)
  have harcIcc : ∀ p : S, (p : ℝ × ℝ).1 < (p : ℝ × ℝ).2 →
      Icc (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 ⊆ closure O := by
    intro p hlt
    have hIooO : Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 ⊆ O := fun θ hθ => harcmem p θ hθ
    calc Icc (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 = closure (Ioo (p : ℝ × ℝ).1 (p : ℝ × ℝ).2) := by
          rw [closure_Ioo hlt.ne]
      _ ⊆ closure O := closure_mono hIooO
  -- membership of the exponential in the superlevel set as a set on the circle
  have hmemexp : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by fun_prop
  have hper : ∀ p : S, ∫ θ in s p, F θ = ∫ θ in s p, G θ := by
    intro p
    rcases lt_or_ge (p : ℝ × ℝ).1 (p : ℝ × ℝ).2 with hlt | hle
    · obtain ⟨hn1, hn2, hlo, hhi⟩ := hSend p p.2
      -- both endpoints are in `closure (super)` (limits of arc-interior super points)
      set p1 : ℝ := (p : ℝ × ℝ).1 with hp1
      set p2 : ℝ := (p : ℝ × ℝ).2 with hp2
      have hseq1 : Filter.Tendsto (fun n : ℕ => p1 + 1 / (n + 2 : ℝ) * (p2 - p1))
          Filter.atTop (nhds p1) := by
        have h0 : Filter.Tendsto (fun n : ℕ => p1 + 1 / (n + 2 : ℝ) * (p2 - p1))
            Filter.atTop (nhds (p1 + 0 * (p2 - p1))) :=
          Filter.Tendsto.const_add _ (Filter.Tendsto.mul_const _
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
              |>.congr (fun n => by simp only [Function.comp_apply]; push_cast; ring)))
        simpa using h0
      have hseq2 : Filter.Tendsto (fun n : ℕ => p2 - 1 / (n + 2 : ℝ) * (p2 - p1))
          Filter.atTop (nhds p2) := by
        have h0 : Filter.Tendsto (fun n : ℕ => p2 - 1 / (n + 2 : ℝ) * (p2 - p1))
            Filter.atTop (nhds (p2 - 0 * (p2 - p1))) :=
          Filter.Tendsto.const_sub _ (Filter.Tendsto.mul_const _
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
              |>.congr (fun n => by simp only [Function.comp_apply]; push_cast; ring)))
        simpa using h0
      have hnbelow : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 2 : ℝ) ∧ 1 / (n + 2 : ℝ) < 1 := by
        intro n
        refine ⟨by positivity, ?_⟩
        rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hclos1 : Complex.exp ((ξ : ℂ) + (p1 : ℂ) * Complex.I)
          ∈ closure (superLevelU U u δ) :=
        mem_closure_of_tendsto (hmemexp.continuousAt.tendsto.comp hseq1)
          (Filter.Eventually.of_forall fun n => (harcmem p _
            (Set.mem_Ioo.mpr ⟨by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2],
             by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2]⟩)).2)
      have hclos2 : Complex.exp ((ξ : ℂ) + (p2 : ℂ) * Complex.I)
          ∈ closure (superLevelU U u δ) :=
        mem_closure_of_tendsto (hmemexp.continuousAt.tendsto.comp hseq2)
          (Filter.Eventually.of_forall fun n => (harcmem p _
            (Set.mem_Ioo.mpr ⟨by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2],
             by nlinarith [hlt, (hnbelow n).1, (hnbelow n).2]⟩)).2)
      have hnot1 : Complex.exp ((ξ : ℂ) + (p1 : ℂ) * Complex.I)
          ∉ superLevelU U u δ := by
        rcases eq_or_lt_of_le hlo with heq | hlt'
        · rw [← heq]; exact hloOut
        · intro hsup; exact hn1 ⟨⟨hlt', lt_of_lt_of_le hlt hhi⟩, hsup⟩
      have hnot2 : Complex.exp ((ξ : ℂ) + (p2 : ℂ) * Complex.I)
          ∉ superLevelU U u δ := by
        rcases eq_or_lt_of_le hhi with heq | hlt'
        · rw [heq]; exact hhiOut
        · intro hsup; exact hn2 ⟨⟨lt_of_le_of_lt hlo hlt, hlt'⟩, hsup⟩
      have hEnd1 : u (Complex.exp ((ξ : ℂ) + ((p : ℝ × ℝ).1 : ℂ) * Complex.I)) = δ :=
        hEsc _ hclos1 hnot1
      have hEnd2 : u (Complex.exp ((ξ : ℂ) + ((p : ℝ × ℝ).2 : ℂ) * Complex.I)) = δ :=
        hEsc _ hclos2 hnot2
      have hid := integral_posPart_re_deriv_expGrad_arc hU hlt hu (fun θ hθ => harcU p θ hθ)
        (fun θ hθ => harcSup p θ hθ) (hcont.mono (harcIcc p hlt))
        (hsliceInt.mono_set (harcmem p)) (hradInt.mono_set (harcmem p))
        hEnd1 hEnd2
      rw [hF, hG, hs]
      rw [intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le hlt.le, integral_Ioc_eq_integral_Ioo] at hid
      exact hid
    · rw [hs]; simp only [Ioo_eq_empty (not_lt.mpr hle), setIntegral_empty]
  have hOmeas : MeasurableSet O := hOopen.measurableSet
  have hOclosCpt : IsCompact (closure O) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      ((Metric.isBounded_Ioo lo hi).subset hOsub).closure
  have hcontO : ContinuousOn (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) O :=
    hcont.mono subset_closure
  have hFint : IntegrableOn F O := by
    obtain ⟨C, hC⟩ := (hOclosCpt.exists_bound_of_continuousOn
      (lipschitzWith_posPart.continuous.comp_continuousOn (hcont.sub continuousOn_const)))
    refine Integrable.mono' (hradInt.norm.const_mul C) ?_ ?_
    · exact ((lipschitzWith_posPart.continuous.comp_continuousOn
        (hcontO.sub continuousOn_const)).aestronglyMeasurable hOmeas).mul
        hradInt.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hOmeas] with θ hθ
      rw [hF, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hC _ (subset_closure hθ)) (norm_nonneg _)
  have hexpGradO : ContinuousOn
      (fun θ : ℝ => expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) O := by
    intro θ hθ
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hθ.2.1
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    exact (ContinuousAt.comp (g := expGrad u)
      (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hdC.continuousAt
      hinner).continuousWithinAt
  have hGint : IntegrableOn G O := by
    refine Integrable.mono' hsliceInt ?_ ?_
    · exact ((Complex.continuous_im.comp_continuousOn hexpGradO).pow 2).aestronglyMeasurable hOmeas
    · filter_upwards [ae_restrict_mem hOmeas] with θ _
      rw [hG, Real.norm_eq_abs, abs_of_nonneg (by positivity), Complex.normSq_apply]
      nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
  rw [hsu, integral_iUnion hsmeas hsdisj (hsu ▸ hFint),
    integral_iUnion hsmeas hsdisj (hsu ▸ hGint)]
  exact tsum_congr hper

/-- **Full-circle truncated angular integration by parts.** Fix a log-radius `ξ` and level `δ`.
If the *whole* circle at log-radius `ξ` lies in `U` and `u > δ` everywhere on it, then the
truncation `(u − δ)⁺` coincides with the smooth `u − δ` on the circle, and the periodic angular
integration by parts (with `±π` boundary terms cancelling by `2π`-periodicity) gives
`∫_{(−π,π)} (u − δ)⁺ · Re (deriv (expGrad u)) = ∫_{(−π,π)} (Im (expGrad u))²`. -/
theorem integral_full_posPart_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {δ ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hfull : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hsup : ∀ θ : ℝ, δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) :
    ∫ θ in Ioo (-π) π,
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in Ioo (-π) π, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  -- on the whole circle the truncation is smooth: `(u − δ)⁺ = u − δ`
  have hpos : ∀ θ : ℝ, (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
      = u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ := fun θ =>
    posPart_eq_self.mpr (by linarith [hsup θ])
  -- rewrite the truncation factor to `u − δ`
  have hinteq : ∫ θ in Ioo (-π) π,
      (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
        * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in Ioo (-π) π,
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re :=
    setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by rw [hpos θ])
  rw [hinteq]
  set f : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ with hf
  set g : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgdef
  set g' : ℝ → ℝ :=
    fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hg'def
  have hdiffR : ∀ θ : ℝ,
      DifferentiableAt ℝ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := fun θ =>
    differentiableAt_of_harmonicOnNhd hu (hfull θ)
  have hdiffC : ∀ θ : ℝ,
      DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ =>
    expGrad_differentiableAt_open hU hu (hfull θ)
  -- `f` and `g` are continuous, and `f' = -g`, `g' = Re (deriv expGrad)`
  have hcont_f : Continuous f := by
    refine continuous_iff_continuousAt.mpr (fun θ => ?_)
    exact ((hasDerivAt_uexp_angular (hdiffR θ)).continuousAt.sub continuousAt_const)
  have hgderiv : ∀ θ : ℝ, HasDerivAt g (g' θ) θ := by
    intro θ
    have hD := hasDerivAt_expGrad_angular (hdiffC θ)
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hD
    simpa [hgdef, hg'def, Function.comp, Complex.mul_im] using hcomp
  have hcont_g : Continuous g :=
    continuous_iff_continuousAt.mpr (fun θ => (hgderiv θ).continuousAt)
  -- `deriv (expGrad u)` is continuous on the open preimage `O = exp ⁻¹' U`, which the circle enters
  have hOcont : ContinuousOn (deriv (expGrad u)) (Complex.exp ⁻¹' U) := by
    set O : Set ℂ := Complex.exp ⁻¹' U with hO
    have hOopen : IsOpen O := hU.preimage Complex.continuous_exp
    have hdiff : DifferentiableOn ℂ (expGrad u) O := fun w hw =>
      (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
    exact ((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn
  have hcont_g' : Continuous g' := by
    refine continuous_iff_continuousAt.mpr (fun θ => ?_)
    have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
    have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hfull θ
    have hOopen : IsOpen (Complex.exp ⁻¹' U) := hU.preimage Complex.continuous_exp
    have hderivC : ContinuousAt (deriv (expGrad u)) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      (hOcont.continuousAt (hOopen.mem_nhds hmemO))
    have hcomp : ContinuousAt
        (fun t : ℝ => deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := deriv (expGrad u))
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hderivC hinner
    exact Complex.continuous_re.continuousAt.comp hcomp
  have hf' : ∀ θ ∈ Ioo (min (-π) π) (max (-π) π), HasDerivAt f (-(g θ)) θ := fun θ _ => by
    simpa [hf, hgdef] using (hasDerivAt_uexp_angular (hdiffR θ)).sub_const δ
  have hg'' : ∀ θ ∈ Ioo (min (-π) π) (max (-π) π), HasDerivAt g (g' θ) θ := fun θ _ => hgderiv θ
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_f.continuousOn hcont_g.continuousOn hf' hg''
    (hcont_g.neg.intervalIntegrable _ _) (hcont_g'.intervalIntegrable _ _)
  have halg : ∫ θ in (-π)..π, (-(g θ)) * g θ = - ∫ θ in (-π)..π, (g θ) ^ 2 := by
    rw [show (fun θ : ℝ => (-(g θ)) * g θ) = fun θ : ℝ => -((g θ) ^ 2) from
      funext fun θ => by ring, intervalIntegral.integral_neg]
  -- boundary terms cancel by `2π`-periodicity
  have hexp : Complex.exp ((ξ : ℂ) + (π : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) := by
    rw [show ((ξ : ℂ) + (π : ℂ) * Complex.I)
        = ((ξ : ℂ) + ((-π : ℝ) : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  have hfper : f π = f (-π) := by simp only [hf]; rw [show ((π : ℝ) : ℂ) = ((π : ℝ) : ℂ) from rfl,
    hexp]
  have hgper : g π = g (-π) := by
    simp only [hgdef, expGrad]; rw [show ((π : ℝ) : ℂ) = ((π : ℝ) : ℂ) from rfl, hexp]
  rw [integral_Ioo_eq_intervalIntegral hπ, integral_Ioo_eq_intervalIntegral hπ, hIBP, halg,
    hfper, hgper]
  ring

/-- **Branch-cut-free truncated angular integration by parts.** Fix a log-radius `ξ` and level `δ`.
On the standard superlevel slice `angularSliceδ U u δ ξ = {θ ∈ (−π, π) | e^{ξ+θi} ∈ U ∧ u > δ}`,
with `u` harmonic on `U`, continuous on the closure of the slice, `u = δ` at every circle boundary
point of the superlevel set, and the slice squared gradient and slice radial-derivative integrand
integrable, the angle integral over the slice of `(u − δ)⁺ · Re (deriv (expGrad u))` equals the
integral of `(Im (expGrad u))²`.  Unlike the arc decomposition, this handles the case where the
superlevel set straddles the `±π` branch cut: if the whole circle is superlevel, the periodic
angular IBP applies (`integral_full_posPart_re_deriv_expGrad`); otherwise a rotation to a window
`(α, α+2π)` whose seam `α` escapes the superlevel set makes the arc decomposition valid
(`setIntegral_windowSlice_posPart_re_deriv_expGrad`), and the `2π`-periodicity of the integrands
transfers the identity back to the standard chart. -/
theorem setIntegral_slice_posPart_re_deriv_expGrad {u : ℂ → ℝ} {U : Set ℂ} {δ ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hcontR : Continuous
      (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEsc : ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ closure (superLevelU U u δ) →
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∉ superLevelU U u δ →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ)
    (hbdd : ∃ C : ℝ, ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ →
      Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≤ C
      ∧ |(deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ C) :
    ∫ θ in angularSliceδ U u δ ξ,
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re
      = ∫ θ in angularSliceδ U u δ ξ,
        (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
  classical
  have hπ : -π ≤ π := neg_le_self Real.pi_pos.le
  set V : Set ℂ := superLevelU U u δ with hVdef
  have hVopen : IsOpen V := isOpen_superLevelU hU hu δ
  set F : ℝ → ℝ := fun θ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
      * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hF
  set G : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 with hG
  set P : Set ℝ := {θ : ℝ | Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ V} with hP
  have hPmeas : MeasurableSet P := (hVopen.preimage (by fun_prop)).measurableSet
  -- both integrands, cut by the superlevel indicator, are `2π`-periodic in the angle
  have hexpper : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    intro θ
    rw [show ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
        = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_periodic _]
  have hloctwo : ∀ θ : ℝ, ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
    intro θ; push_cast; ring
  have hEGper : ∀ θ : ℝ, expGrad u ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    intro θ; simp only [expGrad, hexpper θ]
  -- `expGrad u` is `2π·I`-periodic on `ℂ`, hence so is its derivative
  have hExp2πI : Complex.exp (2 * (π : ℂ) * Complex.I) = 1 := by
    rw [show (2 * (π : ℂ) * Complex.I) = 2 * ↑π * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  have hEGperC : Function.Periodic (expGrad u) (2 * (π : ℂ) * Complex.I) := by
    intro w
    simp only [expGrad]
    rw [show w + 2 * (π : ℂ) * Complex.I = w + 2 * π * Complex.I by ring, Complex.exp_add,
      show Complex.exp (2 * ↑π * Complex.I) = 1 from hExp2πI, mul_one]
  have hshiftfun : (fun x : ℂ => expGrad u (x + 2 * (π : ℂ) * Complex.I)) = expGrad u :=
    funext fun x => hEGperC x
  have hDEGper : ∀ θ : ℝ, deriv (expGrad u) ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
      = deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    intro θ
    rw [hloctwo θ, ← deriv_comp_add_const (expGrad u) (2 * (π : ℂ) * Complex.I), hshiftfun]
  have hPper : Function.Periodic (P.indicator F) (2 * π) := by
    intro θ
    simp only [hP, Set.indicator_apply, hF, mem_setOf_eq, hexpper θ, hDEGper θ]
  have hQper : Function.Periodic (P.indicator G) (2 * π) := by
    intro θ
    simp only [hP, Set.indicator_apply, hG, mem_setOf_eq, hexpper θ, hEGper θ]
  -- `angularSliceδ = Ioo(-π)π ∩ P`, so its set integral is the indicator interval integral
  have hslicedef : angularSliceδ U u δ ξ = Ioo (-π) π ∩ P := by
    ext θ; simp only [angularSliceδ, hP, mem_inter_iff, mem_setOf_eq]; tauto
  have hindF : (∫ θ in angularSliceδ U u δ ξ, F θ) = ∫ θ in (-π)..π, P.indicator F θ := by
    rw [hslicedef, ← setIntegral_indicator hPmeas,
      ← integral_Ioo_eq_intervalIntegral hπ]
  have hindG : (∫ θ in angularSliceδ U u δ ξ, G θ) = ∫ θ in (-π)..π, P.indicator G θ := by
    rw [hslicedef, ← setIntegral_indicator hPmeas,
      ← integral_Ioo_eq_intervalIntegral hπ]
  -- integrands are continuous on the open slice and bounded on `V`, hence integrable on any
  -- bounded window slice
  obtain ⟨C, hC⟩ := hbdd
  have hwinInt : ∀ a b : ℝ,
      IntegrableOn (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        {θ' : ℝ | θ' ∈ Ioo a b ∧ Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V}
      ∧ IntegrableOn (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        {θ' : ℝ | θ' ∈ Ioo a b ∧ Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} := by
    intro a b
    set W : Set ℝ := {θ' : ℝ | θ' ∈ Ioo a b ∧
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} with hW
    have hWopen : IsOpen W := isOpen_Ioo.inter (hVopen.preimage (by fun_prop))
    have hWmeas : MeasurableSet W := hWopen.measurableSet
    have hWbdd : volume W ≠ ⊤ := by
      refine (measure_mono (fun θ hθ => hθ.1)).trans_lt ?_ |>.ne
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hDEGcont : ContinuousOn (deriv (expGrad u)) (Complex.exp ⁻¹' U) := by
      have hOopen : IsOpen (Complex.exp ⁻¹' U) := hU.preimage Complex.continuous_exp
      have hdiff : DifferentiableOn ℂ (expGrad u) (Complex.exp ⁻¹' U) := fun w hw =>
        (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
      exact ((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn
    have hEGmeas : AEStronglyMeasurable
        (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
        (volume.restrict W) := by
      refine (ContinuousOn.aestronglyMeasurable ?_ hWmeas)
      intro θ hθ
      have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
        expGrad_differentiableAt_open hU hu hθ.2.1
      have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
      have hcomp : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
        ContinuousAt.comp (g := expGrad u)
          (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) hdC.continuousAt hinner
      exact (Complex.continuous_normSq.continuousAt.comp hcomp).continuousWithinAt
    have hRDmeas : AEStronglyMeasurable
        (fun θ : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
        (volume.restrict W) := by
      refine (ContinuousOn.aestronglyMeasurable ?_ hWmeas)
      intro θ hθ
      have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hθ.2.1
      have hinner : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
      have hcomp : ContinuousAt
          (fun t : ℝ => deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
        ContinuousAt.comp (g := deriv (expGrad u))
          (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
          (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hinner
      exact (Complex.continuous_re.continuousAt.comp hcomp).continuousWithinAt
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' (integrableOn_const hWbdd (C := C)) hEGmeas ?_
      filter_upwards [ae_restrict_mem hWmeas] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]; exact (hC θ hθ.2).1
    · refine Integrable.mono' (integrableOn_const hWbdd (C := C)) hRDmeas ?_
      filter_upwards [ae_restrict_mem hWmeas] with θ hθ
      rw [Real.norm_eq_abs]; exact (hC θ hθ.2).2
  rw [hindF, hindG]
  -- CASE SPLIT: the whole circle is superlevel, or some angle escapes it
  by_cases hfull : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ V
  · -- FULL CASE: `P = ℝ`, so the indicator drops and the periodic IBP applies directly
    have hPeq : P = univ := by
      ext θ; simp only [hP, mem_setOf_eq, mem_univ, iff_true]; exact hfull θ
    have hFind : ∀ θ : ℝ, P.indicator F θ = F θ := fun θ => by rw [hPeq]; simp
    have hGind : ∀ θ : ℝ, P.indicator G θ = G θ := fun θ => by rw [hPeq]; simp
    simp only [hFind, hGind]
    rw [← integral_Ioo_eq_intervalIntegral hπ, ← integral_Ioo_eq_intervalIntegral hπ]
    exact integral_full_posPart_re_deriv_expGrad hU hu (fun θ => (hfull θ).1)
      (fun θ => (hfull θ).2)
  · -- PROPER CASE: pick a seam `α` escaping the superlevel set and rotate to `(α, α+2π)`
    push Not at hfull
    obtain ⟨α, hα⟩ := hfull
    set W : Set ℝ := {θ' : ℝ | θ' ∈ Ioo α (α + 2 * π) ∧
      Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} with hWdef
    have hWmeas : MeasurableSet W :=
      (isOpen_Ioo.inter (hVopen.preimage (by fun_prop))).measurableSet
    -- transfer the two `(−π, π)` indicator interval integrals to the window `(α, α+2π)`
    have haddπ : (-π) + 2 * π = π := by ring
    have hαle : α ≤ α + 2 * π := by linarith [Real.pi_pos]
    have hWeq : W = Ioo α (α + 2 * π) ∩ P := by
      ext θ; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
    have htransF : (∫ θ in (-π)..π, P.indicator F θ) = ∫ θ in W, F θ := by
      have hkey := hPper.intervalIntegral_add_eq (-π) α
      rw [haddπ] at hkey
      rw [hkey, ← integral_Ioo_eq_intervalIntegral hαle, hWeq, ← setIntegral_indicator hPmeas]
    have htransG : (∫ θ in (-π)..π, P.indicator G θ) = ∫ θ in W, G θ := by
      have hkey := hQper.intervalIntegral_add_eq (-π) α
      rw [haddπ] at hkey
      rw [hkey, ← integral_Ioo_eq_intervalIntegral hαle, hWeq, ← setIntegral_indicator hPmeas]
    rw [htransF, htransG]
    -- the window slice IBP: the seam `α` (and `α+2π`) escape the superlevel set
    have hαπOut : Complex.exp ((ξ : ℂ) + ((α + 2 * π : ℝ) : ℂ) * Complex.I) ∉ V := by
      rw [hexpper α]; exact hα
    have hcontClos : ContinuousOn
        (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) (closure W) :=
      hcontR.continuousOn
    exact setIntegral_windowSlice_posPart_re_deriv_expGrad hU hu hcontClos hEsc hα hαπOut
      (hwinInt α (α + 2 * π)).1 (hwinInt α (α + 2 * π)).2

/-! ### The truncated rough flux and its `δ → 0` recovery of `roughFlux`

The **truncated rough flux** `truncRoughFlux u U δ ξ` is the δ-rough flux with the potential factor
`u` replaced by its truncation `(u − δ)⁺`, integrated over the superlevel slice.  For `u` strictly
positive on `U`, `(u − δ)⁺ → u` pointwise as `δ ↓ 0` and the superlevel slices increase to the full
slice, so — dominated by the slice-`L¹` radial-derivative bound (`|(u − δ)⁺| ≤ |u| ≤ M` on the
slice) — the truncated rough flux converges to `roughFlux u U ξ`.  The convergence is even more
elementary than `tendsto_roughFluxδ_atZero`: on the superlevel slice `|(u − δ)⁺ − u| = δ` uniformly.
-/

/-- The **truncated rough flux**: the angle integral over the superlevel slice of the truncated
potential `(u − δ)⁺` against the radial-derivative factor `Re (expGrad u)`. -/
noncomputable def truncRoughFlux (u : ℂ → ℝ) (U : Set ℂ) (δ ξ : ℝ) : ℝ :=
  ∫ θ in Ioo (-π) π,
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}.indicator
      (fun θ' : ℝ => (u (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I)) - δ)⁺
        * (expGrad u ((ξ : ℂ) + (θ' : ℂ) * Complex.I)).re) θ

/-- **The truncated rough flux is the set integral over the superlevel slice.** The indicator
integral defining `truncRoughFlux` unfolds, exactly as for `roughFluxδ`, to the set integral of
`(u − δ)⁺ · Re (expGrad u)` over the open δ-angular slice. -/
theorem truncRoughFlux_eq_setIntegral_slice {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (δ ξ : ℝ) :
    truncRoughFlux u U δ ξ = ∫ θ in angularSliceδ U u δ ξ,
      (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
        * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
  have hπ := Real.pi_pos
  have hVopen : IsOpen (superLevelU U u δ) := isOpen_superLevelU hU hu δ
  have hcontmap : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
    fun_prop
  have hmeasset :
      MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ} :=
    hcontmap.measurable hVopen.measurableSet
  unfold truncRoughFlux
  rw [setIntegral_indicator hmeasset]
  refine setIntegral_congr_set ?_
  rw [angularSliceδ, superLevelU]
  refine (ae_eq_set.mpr ⟨?_, ?_⟩) <;>
    · refine measure_mono_null (fun θ hθ => ?_) measure_empty
      simp only [mem_diff, mem_inter_iff, mem_setOf_eq] at hθ
      tauto

/-- **`δ → 0` recovery of the rough flux via the truncated flux.** For `u` harmonic and strictly
positive on the open set `U`, uniformly bounded by `M` on the angular slice at log-radius `ξ` with
the slice radial-derivative integrand integrable, along any positive null-sequence `δ n → 0` the
truncated rough flux tends to the rough flux: the superlevel-slice indicators of the integrand
`(u − δ n)⁺ · Re (expGrad u)` converge pointwise to the full-slice `u · Re (expGrad u)` (both the
superlevel slices increase to the full slice and `(u − δ n)⁺ → u`), dominated by the slice-`L¹`
bound `M · |Re (expGrad u)|`, so dominated convergence applies on `(−π, π)`. -/
theorem tendsto_truncRoughFlux_atZero {u : ℂ → ℝ} {U : Set ℂ} {ξ M : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z) (hMnn : 0 ≤ M)
    (hM : ∀ θ ∈ angularSlice U ξ, |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hReInt : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ))
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hdto : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => truncRoughFlux u U (d n) ξ) atTop (𝓝 (roughFlux u U ξ)) := by
  have hπ := Real.pi_pos
  set s : Set ℝ := angularSlice U ξ with hs
  have hsmeas : MeasurableSet s := (isOpen_angularSlice hU ξ).measurableSet
  have hssub : s ⊆ Ioo (-π) π := angularSlice_subset U ξ
  set I : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hI
  set B : ℝ → ℝ := s.indicator (fun θ => M * |(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|)
    with hB
  -- `I` is continuous on the full slice `s`
  have hcontI : ContinuousOn I s := by
    intro θ hθ
    have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2
    have hcm : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by
      fun_prop
    have hcu : ContinuousAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))) θ :=
      (ContinuousAt.comp (g := u)
        (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hcm)
    have hdC : DifferentiableAt ℂ (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I) :=
      expGrad_differentiableAt_open hU hu hmem
    have hcg : ContinuousAt
        (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      (ContinuousAt.comp (g := fun w : ℂ => (expGrad u w).re)
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (Complex.continuous_re.continuousAt.comp hdC.continuousAt) (by fun_prop))
    exact (hcu.mul hcg).continuousWithinAt
  have hBint : IntegrableOn B (Ioo (-π) π) := by
    have hsint : IntegrableOn
        (fun θ : ℝ => M * |(expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re|) s :=
      hReInt.abs.const_mul M
    rw [hB, integrableOn_indicator_iff hsmeas, Set.inter_eq_self_of_subset_left hssub]
    exact hsint
  -- the truncated-flux integrand and its target, as indicator integrals over `(−π, π)`
  set J : ℝ → ℝ → ℝ := fun δ θ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
    * (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hJ
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun θ => {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)}.indicator (J (d n)) θ) (volume.restrict (Ioo (-π) π)) := by
    intro n
    have hVmeas : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
        superLevelU U u (d n)} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable
          (isOpen_superLevelU hU hu (d n)).measurableSet
    rw [aestronglyMeasurable_indicator_iff hVmeas]
    -- `J (d n)` on `(Ioo (-π) π) ∩ V`; since `V ∩ Ioo ⊆ s`, restrict its slice measurability
    have hucontS : ContinuousOn (fun θ : ℝ =>
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))) s := fun θ hθ =>
      (ContinuousAt.comp (g := u)
        (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hθ.2).continuousAt (by fun_prop)).continuousWithinAt
    have hposS : ContinuousOn (fun θ : ℝ =>
        (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n)⁺) s :=
      lipschitzWith_posPart.continuous.comp_continuousOn (hucontS.sub continuousOn_const)
    have hJslice : AEStronglyMeasurable (J (d n)) (volume.restrict s) :=
      (hposS.aestronglyMeasurable hsmeas).mul hReInt.aestronglyMeasurable
    refine hJslice.mono_measure ?_
    rw [Measure.restrict_restrict hVmeas]
    refine Measure.restrict_mono (fun θ hθ => ?_) le_rfl
    exact (show θ ∈ s from ⟨hθ.2, hθ.1.1⟩)
  have hδform : ∀ n, truncRoughFlux u U (d n) ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈
          superLevelU U u (d n)}.indicator (J (d n)) θ := fun n => rfl
  have hlimform : roughFlux u U ξ
      = ∫ θ in Ioo (-π) π, {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator I θ := by
    rw [roughFlux_eq_setIntegral_slice hU, ← hs]
    rw [show (∫ θ in Ioo (-π) π, {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U}.indicator I θ)
        = ∫ θ in Ioo (-π) π, s.indicator I θ from
      setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)]
    · rw [MeasureTheory.integral_indicator hsmeas, Measure.restrict_restrict hsmeas,
        Set.inter_eq_self_of_subset_left hssub]
    · by_cases hθU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
      · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hθU),
          Set.indicator_of_mem (show θ ∈ s from ⟨hθ, hθU⟩)]
      · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hθU),
          Set.indicator_of_notMem (show θ ∉ s from fun h => hθU h.2)]
  simp only [hδform]
  rw [hlimform]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence B hFmeas hBint ?_ ?_
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    by_cases hθV : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u (d n)
    · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV)]
      have hθs : θ ∈ s := ⟨hθ, hθV.1⟩
      rw [hB, Set.indicator_of_mem hθs, hJ, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      -- `|(u − δ)⁺| ≤ |u| ≤ M`
      have hule : |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M := hM θ hθs
      have hnn : 0 ≤ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := (hpos _ hθV.1).le
      rw [abs_of_nonneg (posPart_nonneg _)]
      calc (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n)⁺
          ≤ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
            rw [show (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n)⁺
              = max (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - d n) 0 from rfl]
            exact max_le (by linarith [(hdpos n)]) hnn
        _ ≤ M := le_trans (le_abs_self _) hule
    · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)} from hθV),
        norm_zero, hB]
      by_cases hθs : θ ∈ s
      · rw [Set.indicator_of_mem hθs]; positivity
      · rw [Set.indicator_of_notMem hθs]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
    -- pointwise convergence of the superlevel-slice truncated integrand to the full-slice `I θ`
    by_cases hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
    · rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
      have hupos : 0 < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := hpos _ hmem
      have hev : ∀ᶠ n in atTop, d n < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) :=
        hdto.eventually_lt_const hupos
      refine Tendsto.congr' ?_
        (show Tendsto (fun n : ℕ => J (d n) θ) atTop (𝓝 (I θ)) from ?_)
      · filter_upwards [hev] with n hn
        rw [Set.indicator_of_mem (show θ ∈ {θ' : ℝ |
          Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)}
          from ⟨hmem, hn⟩)]
      · have hJto : Tendsto (fun n : ℕ => (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
            - d n)⁺) atTop (𝓝 ((u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - 0)⁺)) := by
          exact (continuous_posPart.tendsto _).comp (tendsto_const_nhds.sub hdto)
        rw [hJ, hI, sub_zero, posPart_eq_self.mpr hupos.le] at *
        exact hJto.mul_const _
    · rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ U} from hmem)]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with n
      rw [Set.indicator_of_notMem (show θ ∉ {θ' : ℝ |
        Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u (d n)}
        from fun h => hmem h.1)]

/-- **Rough-flux increment from the truncated-flux increment bound.** For `u` harmonic and strictly
positive on the open set `U`, uniformly bounded by `M` on both slices at `ζ₁` and `ζ₂` with the
slice radial-derivative integrand integrable there, if the truncated-flux increment is bounded by a
constant `D` for every `δ > 0`, then the rough-flux increment is bounded by `D`: pass to `δ → 0`
using the truncated-flux recovery of the rough flux at each of the two log-radii. -/
theorem roughFlux_sub_le_of_truncRoughFlux_sub_le {u : ℂ → ℝ} {U : Set ℂ} {ζ₁ ζ₂ M D : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hMnn : 0 ≤ M)
    (hM1 : ∀ θ ∈ angularSlice U ζ₁, |u (Complex.exp ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hM2 : ∀ θ ∈ angularSlice U ζ₂, |u (Complex.exp ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I))| ≤ M)
    (hRe1 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₁ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₁))
    (hRe2 : IntegrableOn
      (fun θ : ℝ => (expGrad u ((ζ₂ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ζ₂))
    (hδbd : ∀ δ : ℝ, 0 < δ → truncRoughFlux u U δ ζ₂ - truncRoughFlux u U δ ζ₁ ≤ D) :
    roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ D := by
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hd
  have hdpos : ∀ n, 0 < d n := fun n => by positivity
  have hdto : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim1 : Tendsto (fun n => truncRoughFlux u U (d n) ζ₁) atTop (𝓝 (roughFlux u U ζ₁)) :=
    tendsto_truncRoughFlux_atZero hU hu hpos hMnn hM1 hRe1 hdpos hdto
  have hlim2 : Tendsto (fun n => truncRoughFlux u U (d n) ζ₂) atTop (𝓝 (roughFlux u U ζ₂)) :=
    tendsto_truncRoughFlux_atZero hU hu hpos hMnn hM2 hRe2 hdpos hdto
  have hlim : Tendsto (fun n => truncRoughFlux u U (d n) ζ₂ - truncRoughFlux u U (d n) ζ₁) atTop
      (𝓝 (roughFlux u U ζ₂ - roughFlux u U ζ₁)) := hlim2.sub hlim1
  refine le_of_tendsto hlim ?_
  filter_upwards with n
  exact hδbd (d n) (hdpos n)

/-! ### The truncated-flux increment inequality (fixed-window FTC on the superlevel set)

The truncated-flux increment `truncRoughFlux u U δ ζ₂ − truncRoughFlux u U δ ζ₁` is, on a window
`{e^{ζ₁} < |z| < e^{ζ₂}}` (`ζ₂ < 0`) whose superlevel intersection sits compactly inside `U`, the
Dirichlet energy of `{u > δ} ∩ U` over the window annulus, bounded above by the total energy
`D(u; U)`.  The truncated integrand is supported in the superlevel slice and — because `(u − δ)⁺`
vanishes continuously across the superlevel boundary while `Re (expGrad u)` stays bounded on the
compact containment `K = closure({u > δ} ∩ window) ⊆ U` — extends to a continuous integrand on the
whole fixed window box, so the fixed-window flux–energy FTC applies without a moving domain. -/

/-! ### The windowed truncated integrand and the moving-domain flux FTC

Fix a window annulus `W = {e^{ξ₁} < |z| < e^{ξ₂}}` whose superlevel intersection `V ∩ W` has compact
closure `K ⊆ U`.  On the log-strip box `stripBox ξ₁ ξ₂ (−π) π` the **windowed truncated integrand**
`H w = 1_{e^w ∈ U} · (u(e^w) − δ)⁺ · Re (expGrad u w)` is continuous: near a point whose exponential
lies in `U` the two smooth factors are continuous, while off `K` (in particular at any strip-box
point whose exponential escapes `U`) `H` vanishes on a whole neighbourhood since `{H ≠ 0}` maps into
`V ∩ W ⊆ K`.  The truncated rough flux is the `θ`-integral of `H` over the full circle, so the
strip-box Lipschitz differentiation under the integral sign gives its `ξ`-FTC with the superlevel
slice energy as derivative. -/

/-- The **windowed truncated integrand** `H w = 1_{e^w ∈ U} · (u(e^w) − δ)⁺ · Re (expGrad u w)`. -/
noncomputable def windowedTruncIntegrand (u : ℂ → ℝ) (U : Set ℂ) (δ : ℝ) (w : ℂ) : ℝ :=
  U.indicator (fun z => (u z - δ)⁺ * (gradC u z * z).re) (Complex.exp w)

/-- Off the compact containment `K ⊇ V ∩ W`, the windowed truncated integrand vanishes on any point
of the strip box (whose exponential lies in the window annulus). -/
theorem windowedTruncIntegrand_eq_zero_of_notMem {u : ℂ → ℝ} {U : Set ℂ} {δ ξ₁ ξ₂ : ℝ}
    {w : ℂ} (hw : w ∈ stripBox ξ₁ ξ₂ (-π) π)
    (hwK : Complex.exp w ∉ closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ξ₁)
      (Real.exp ξ₂))) :
    windowedTruncIntegrand u U δ w = 0 := by
  unfold windowedTruncIntegrand
  by_cases hU : Complex.exp w ∈ U
  · rw [Set.indicator_of_mem hU]
    by_cases hgt : δ < u (Complex.exp w)
    · exfalso
      apply hwK
      apply subset_closure
      refine ⟨⟨hU, hgt⟩, ?_⟩
      obtain ⟨hre1, hre2, _, _⟩ := hw
      have hdist : dist (Complex.exp w) 0 = Real.exp w.re := by
        rw [dist_zero_right, Complex.norm_exp]
      refine ⟨?_, ?_⟩
      · rw [hdist]; exact Real.exp_lt_exp.mpr hre1
      · rw [hdist]; exact Real.exp_lt_exp.mpr hre2
    · rw [posPart_eq_zero.mpr (by rw [not_lt] at hgt; linarith), zero_mul]
  · rw [Set.indicator_of_notMem hU]

/-- **Continuity of the windowed truncated integrand on the strip box.** For `u` harmonic on the
open set `U` with the superlevel window intersection compactly contained in `U`
(`hK : closure (V ∩ W) ⊆ U`), the windowed truncated integrand `H` is continuous on the log-strip
box `stripBox ξ₁ ξ₂ (−π) π`.  At a point whose exponential lies in `U` the two smooth factors are
continuous; off the compact containment `K` (in particular where the exponential escapes `U`), `H`
vanishes on a whole neighbourhood since `exp ⁻¹' Kᶜ` is open and `H` is supported in `exp ⁻¹' K`. -/
theorem continuousOn_windowedTruncIntegrand {u : ℂ → ℝ} {U : Set ℂ} {δ ξ₁ ξ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hK : closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂)) ⊆ U) :
    ContinuousOn (windowedTruncIntegrand u U δ) (stripBox ξ₁ ξ₂ (-π) π) := by
  set K : Set ℂ := closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ξ₁) (Real.exp ξ₂))
    with hKdef
  intro w hw
  by_cases hwU : Complex.exp w ∈ U
  · -- near a point whose exponential lies in `U`, both factors are continuous
    have hnhdU : (fun z : ℂ => Complex.exp z) ⁻¹' U ∈ nhds w :=
      (hU.preimage Complex.continuous_exp).mem_nhds hwU
    have hHeq : windowedTruncIntegrand u U δ
        =ᶠ[nhds w] fun z : ℂ => (u (Complex.exp z) - δ)⁺ * (expGrad u z).re := by
      filter_upwards [hnhdU] with z hz
      unfold windowedTruncIntegrand
      rw [Set.indicator_of_mem (show Complex.exp z ∈ U from hz), expGrad]
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (hHeq.filter_mono nhdsWithin_le_nhds)
      (hHeq.self_of_nhds)
    -- continuity of `(u∘exp − δ)⁺ · Re (expGrad u)` at `w`
    have hcu : ContinuousAt (fun z : ℂ => u (Complex.exp z)) w :=
      (differentiableAt_of_harmonicOnNhd hu hwU).continuousAt.comp
        Complex.continuous_exp.continuousAt
    have hpos : ContinuousAt (fun z : ℂ => (u (Complex.exp z) - δ)⁺) w :=
      (continuous_posPart.continuousAt).comp (hcu.sub continuousAt_const)
    have hre : ContinuousAt (fun z : ℂ => (expGrad u z).re) w :=
      Complex.continuous_re.continuousAt.comp
        (expGrad_differentiableAt_open hU hu hwU).continuousAt
    exact (hpos.mul hre).continuousWithinAt
  · -- off `U`, `exp w ∉ K` (since `K ⊆ U`), so `H` vanishes on a neighbourhood within the strip box
    have hwK : Complex.exp w ∉ K := fun h => hwU (hK h)
    have hnhd : (fun z : ℂ => Complex.exp z) ⁻¹' Kᶜ ∈ nhds w :=
      (isClosed_closure.isOpen_compl.preimage Complex.continuous_exp).mem_nhds hwK
    have hHeq : windowedTruncIntegrand u U δ
        =ᶠ[nhdsWithin w (stripBox ξ₁ ξ₂ (-π) π)] fun _ : ℂ => (0 : ℝ) := by
      have hnhdW : (fun z : ℂ => Complex.exp z) ⁻¹' Kᶜ
          ∈ nhdsWithin w (stripBox ξ₁ ξ₂ (-π) π) := nhdsWithin_le_nhds hnhd
      filter_upwards [hnhdW, self_mem_nhdsWithin] with z hz hzstrip
      exact windowedTruncIntegrand_eq_zero_of_notMem hzstrip hz
    refine ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hHeq ?_
    exact windowedTruncIntegrand_eq_zero_of_notMem hw hwK

/-- **The truncated rough flux is the full-circle integral of the windowed truncated integrand.**
For each log-radius `ξ`, `truncRoughFlux u U δ ξ` equals the `θ`-integral over `(−π, π)` of
`windowedTruncIntegrand u U δ (ξ + θi)`: pointwise the two integrands agree — on the superlevel
slice both are `(u − δ)⁺ · Re (expGrad u)`, and off it both vanish (either the exponential escapes
`U`, or `u ≤ δ` makes `(u − δ)⁺ = 0`). -/
theorem truncRoughFlux_eq_integral_windowedTruncIntegrand {u : ℂ → ℝ} {U : Set ℂ} (δ ξ : ℝ) :
    truncRoughFlux u U δ ξ
      = ∫ θ in Ioo (-π) π, windowedTruncIntegrand u U δ ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
  unfold truncRoughFlux windowedTruncIntegrand
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  by_cases hU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U
  · by_cases hgt : δ < u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
    · rw [Set.indicator_of_mem
          (show θ ∈ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
            from ⟨hU, hgt⟩), Set.indicator_of_mem hU, expGrad]
    · rw [Set.indicator_of_notMem
          (show θ ∉ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
            from fun h => hgt h.2), Set.indicator_of_mem hU,
        posPart_eq_zero.mpr (by rw [not_lt] at hgt; linarith), zero_mul]
  · rw [Set.indicator_of_notMem
        (show θ ∉ {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
          from fun h => hU h.1), Set.indicator_of_notMem hU]

/-! ### The planar level-set nullity of a nonconstant harmonic potential

For `u` harmonic on the open set `U`, its level set `{z ∈ U | u z = δ}` at any level `δ` has planar
measure zero, provided `u` is nowhere locally constant on `U` (equivalently, its holomorphic
gradient `gradC u` is nowhere locally identically zero).  The proof splits the level set at the
critical set `{gradC u = 0}`: the critical set is the zero set of the holomorphic `gradC u`, hence
discrete (its zeros are isolated by the identity principle) and countable, so null; off the critical
set one of the two partials is nonzero, so near each such point `u` is strictly monotone along a
coordinate axis and the level set meets each axis-parallel line in at most one point — a graph, null
by Fubini. -/

/-- **Nullity of the critical set of a nowhere-locally-constant harmonic potential.** For `u`
harmonic on the open set `U` with `gradC u` nowhere locally identically zero on `U`, the critical
set `{z ∈ U | gradC u z = 0}` has planar measure zero: it is the zero set of the holomorphic
`gradC u`, whose zeros are isolated (identity principle), so it is discrete, countable and null. -/
theorem gradC_zeroSet_null {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0)) :
    volume {z : ℂ | z ∈ U ∧ gradC u z = 0} = 0 := by
  set Z : Set ℂ := {z : ℂ | z ∈ U ∧ gradC u z = 0} with hZ
  have hanal : AnalyticOnNhd ℂ (gradC u) U := (gradC_differentiableOn hu).analyticOnNhd hU
  have hdisc : DiscreteTopology Z := by
    apply discreteTopology_of_noAccPts
    intro z hz hacc
    have hzU : z ∈ U := hz.1
    have hfreq : ∃ᶠ w in 𝓝[≠] z, gradC u w = 0 :=
      (accPt_iff_frequently_nhdsNE.mp hacc).mono (fun w hw => hw.2)
    rcases (hanal z hzU).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact hnc z hzU hzero
    · rcases (hne.and_frequently hfreq).exists with ⟨w, hw1, hw2⟩
      exact hw1 hw2
  have hcount : Z.Countable :=
    (HereditarilyLindelofSpace.isLindelof Z).countable hdisc
  exact hcount.measure_zero volume

/-- A measurable planar set all of whose vertical slices `{y | x + y·i ∈ S}` are subsingletons has
planar measure zero: transporting to `ℝ × ℝ` (`Complex.volume_preserving_equiv_real_prod`) and
applying `Measure.prod_apply`, each fibre has one-dimensional measure zero. -/
theorem volume_eq_zero_of_subsingleton_vertical_slice {S : Set ℂ} (hmeas : MeasurableSet S)
    (hslice : ∀ x : ℝ, {y : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S}.Subsingleton) :
    volume S = 0 := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  set S' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd '' S with hS'
  have hS'meas : MeasurableSet S' :=
    Complex.measurableEquivRealProd.measurableEmbedding.measurableSet_image.mpr hmeas
  have hvol : volume S = volume S' := by
    rw [hS', ← hmp.measure_preimage hS'meas.nullMeasurableSet,
      Set.preimage_image_eq _ Complex.measurableEquivRealProd.injective]
  rw [hvol, Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply hS'meas]
  have hz : ∀ x : ℝ, (volume : Measure ℝ) (Prod.mk x ⁻¹' S') = 0 := by
    intro x
    have hsub : (Prod.mk x ⁻¹' S') = {y : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S} := by
      ext y
      simp only [Set.mem_preimage, hS', Set.mem_image, mem_setOf_eq]
      constructor
      · rintro ⟨z, hzS, hz⟩
        have : z = (x : ℂ) + (y : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp_all [Complex.measurableEquivRealProd_apply, Prod.ext_iff]
        rwa [this] at hzS
      · intro hy
        exact ⟨(x : ℂ) + (y : ℂ) * Complex.I, hy, by simp [Complex.measurableEquivRealProd_apply]⟩
    rw [hsub]; exact (hslice x).measure_zero volume
  simp only [hz, lintegral_zero]

/-- A measurable planar set all of whose horizontal slices `{x | x + y·i ∈ S}` are subsingletons has
planar measure zero (the `Prod.swap` variant of `volume_eq_zero_of_subsingleton_vertical_slice`). -/
theorem volume_eq_zero_of_subsingleton_horizontal_slice {S : Set ℂ} (hmeas : MeasurableSet S)
    (hslice : ∀ y : ℝ, {x : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S}.Subsingleton) :
    volume S = 0 := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  set S' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd '' S with hS'
  have hS'meas : MeasurableSet S' :=
    Complex.measurableEquivRealProd.measurableEmbedding.measurableSet_image.mpr hmeas
  have hvol : volume S = volume S' := by
    rw [hS', ← hmp.measure_preimage hS'meas.nullMeasurableSet,
      Set.preimage_image_eq _ Complex.measurableEquivRealProd.injective]
  rw [hvol, Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply_symm hS'meas]
  have hz : ∀ y : ℝ, (volume : Measure ℝ) ((fun x => (x, y)) ⁻¹' S') = 0 := by
    intro y
    have hsub : ((fun x => (x, y)) ⁻¹' S') = {x : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S} := by
      ext x
      simp only [Set.mem_preimage, hS', Set.mem_image, mem_setOf_eq]
      constructor
      · rintro ⟨z, hzS, hz⟩
        have : z = (x : ℂ) + (y : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp_all [Complex.measurableEquivRealProd_apply, Prod.ext_iff]
        rwa [this] at hzS
      · intro hx
        exact ⟨(x : ℂ) + (y : ℂ) * Complex.I, hx, by simp [Complex.measurableEquivRealProd_apply]⟩
    rw [hsub]; exact (hslice y).measure_zero volume
  simp only [hz, lintegral_zero]

/-- On an open rectangle `{re ∈ (a₁, a₂), im ∈ (b₁, b₂)}` on which `u` is differentiable with
nonvanishing vertical partial `(fderiv ℝ u) I`, each vertical line meets the level set `{u = δ}` in
at most one point of the rectangle: two such points would, by Rolle's theorem, force the vertical
partial to vanish between them. -/
theorem subsingleton_vertical_slice_of_deriv_ne {u : ℂ → ℝ} {δ a₁ a₂ b₁ b₂ : ℝ}
    (hdiff : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → DifferentiableAt ℝ u z)
    (hne : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → (fderiv ℝ u z) Complex.I ≠ 0)
    (x : ℝ) :
    {y : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ ∧
      ((x : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ ∧
      u ((x : ℂ) + (y : ℂ) * Complex.I) = δ}.Subsingleton := by
  have hre : ∀ s : ℝ, ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by intro s; simp
  have him : ∀ s : ℝ, ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by intro s; simp
  have hcore : ∀ y1 y2 : ℝ, y1 < y2 →
      ((x : ℂ) + (y1 : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ →
      ((x : ℂ) + (y1 : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ →
      u ((x : ℂ) + (y1 : ℂ) * Complex.I) = δ →
      ((x : ℂ) + (y2 : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ →
      u ((x : ℂ) + (y2 : ℂ) * Complex.I) = δ → False := by
    intro y1 y2 hlt hx1 hy1i hgy1 hy2i hgy2
    set g : ℝ → ℝ := fun s => u ((x : ℂ) + (s : ℂ) * Complex.I) with hg
    have hIcc : Icc y1 y2 ⊆ Ioo b₁ b₂ := by
      rw [him] at hy1i hy2i
      exact fun s hs => ⟨lt_of_lt_of_le hy1i.1 hs.1, lt_of_le_of_lt hs.2 hy2i.2⟩
    have hdg : ∀ s ∈ Icc y1 y2,
        HasDerivAt g ((fderiv ℝ u ((x : ℂ) + (s : ℂ) * Complex.I)) Complex.I) s := by
      intro s hs
      have hsre : ((x : ℂ) + (s : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by
        rw [hre]; rw [hre] at hx1; exact hx1
      have hsim : ((x : ℂ) + (s : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by rw [him]; exact hIcc hs
      have hline : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
        have h := (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
        simpa using (h.const_add (x : ℂ))
      simpa using (hdiff _ hsre hsim).hasFDerivAt.comp_hasDerivAt s hline
    have hcont : ContinuousOn g (Icc y1 y2) :=
      fun s hs => (hdg s hs).continuousAt.continuousWithinAt
    have hends : g y1 = g y2 := by rw [hg]; simp only []; rw [hgy1, hgy2]
    obtain ⟨c, hc, hderiv⟩ :=
      exists_hasDerivAt_eq_zero hlt hcont hends (fun s hs => hdg s ⟨hs.1.le, hs.2.le⟩)
    have hcre : ((x : ℂ) + (c : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by
      rw [hre]; rw [hre] at hx1; exact hx1
    have hcim : ((x : ℂ) + (c : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by
      rw [him]; exact hIcc ⟨hc.1.le, hc.2.le⟩
    exact hne _ hcre hcim hderiv
  intro y1 hy1 y2 hy2
  obtain ⟨hx1, hy1i, hgy1⟩ := hy1
  obtain ⟨hx2, hy2i, hgy2⟩ := hy2
  rcases lt_trichotomy y1 y2 with hlt | heq | hgt
  · exact absurd (hcore y1 y2 hlt hx1 hy1i hgy1 hy2i hgy2) (by simp)
  · exact heq
  · exact absurd (hcore y2 y1 hgt hx2 hy2i hgy2 hy1i hgy1) (by simp)

/-- On an open rectangle `{re ∈ (a₁, a₂), im ∈ (b₁, b₂)}` on which `u` is differentiable with
nonvanishing horizontal partial `(fderiv ℝ u) 1`, each horizontal line meets the level set `{u = δ}`
in at most one point of the rectangle. -/
theorem subsingleton_horizontal_slice_of_deriv_ne {u : ℂ → ℝ} {δ a₁ a₂ b₁ b₂ : ℝ}
    (hdiff : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → DifferentiableAt ℝ u z)
    (hne : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → (fderiv ℝ u z) 1 ≠ 0)
    (y : ℝ) :
    {x : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ ∧
      ((x : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ ∧
      u ((x : ℂ) + (y : ℂ) * Complex.I) = δ}.Subsingleton := by
  have hre : ∀ s : ℝ, ((s : ℂ) + (y : ℂ) * Complex.I).re = s := by intro s; simp
  have him : ∀ s : ℝ, ((s : ℂ) + (y : ℂ) * Complex.I).im = y := by intro s; simp
  have hcore : ∀ x1 x2 : ℝ, x1 < x2 →
      ((x1 : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ →
      ((x1 : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ →
      u ((x1 : ℂ) + (y : ℂ) * Complex.I) = δ →
      ((x2 : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ →
      u ((x2 : ℂ) + (y : ℂ) * Complex.I) = δ → False := by
    intro x1 x2 hlt hx1i hyi hgx1 hx2i hgx2
    set g : ℝ → ℝ := fun s => u ((s : ℂ) + (y : ℂ) * Complex.I) with hg
    have hIcc : Icc x1 x2 ⊆ Ioo a₁ a₂ := by
      rw [hre] at hx1i hx2i
      exact fun s hs => ⟨lt_of_lt_of_le hx1i.1 hs.1, lt_of_le_of_lt hs.2 hx2i.2⟩
    have hdg : ∀ s ∈ Icc x1 x2,
        HasDerivAt g ((fderiv ℝ u ((s : ℂ) + (y : ℂ) * Complex.I)) 1) s := by
      intro s hs
      have hsre : ((s : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by rw [hre]; exact hIcc hs
      have hsim : ((s : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by
        rw [him]; rw [him] at hyi; exact hyi
      have hline : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) 1 s := by
        have h := Complex.ofRealCLM.hasDerivAt (x := s)
        simpa using (h.add_const ((y : ℂ) * Complex.I))
      simpa using (hdiff _ hsre hsim).hasFDerivAt.comp_hasDerivAt s hline
    have hcont : ContinuousOn g (Icc x1 x2) :=
      fun s hs => (hdg s hs).continuousAt.continuousWithinAt
    have hends : g x1 = g x2 := by rw [hg]; simp only []; rw [hgx1, hgx2]
    obtain ⟨c, hc, hderiv⟩ :=
      exists_hasDerivAt_eq_zero hlt hcont hends (fun s hs => hdg s ⟨hs.1.le, hs.2.le⟩)
    have hcre : ((c : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by
      rw [hre]; exact hIcc ⟨hc.1.le, hc.2.le⟩
    have hcim : ((c : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by
      rw [him]; rw [him] at hyi; exact hyi
    exact hne _ hcre hcim hderiv
  intro x1 hx1 x2 hx2
  obtain ⟨hx1i, hyi, hgx1⟩ := hx1
  obtain ⟨hx2i, _, hgx2⟩ := hx2
  rcases lt_trichotomy x1 x2 with hlt | heq | hgt
  · exact absurd (hcore x1 x2 hlt hx1i hyi hgx1 hx2i hgx2) (by simp)
  · exact heq
  · exact absurd (hcore x2 x1 hgt hx2i hyi hgx2 hx1i hgx1) (by simp)

/-- Every point of an open set has an open axis-parallel rectangle neighbourhood contained in it:
the rectangles `{re ∈ (a₁, a₂), im ∈ (b₁, b₂)}` form a neighbourhood basis of `ℂ`. -/
theorem exists_rect_subset_of_isOpen {W : Set ℂ} (hW : IsOpen W) {z0 : ℂ} (hz0 : z0 ∈ W) :
    ∃ a₁ a₂ b₁ b₂ : ℝ, z0.re ∈ Ioo a₁ a₂ ∧ z0.im ∈ Ioo b₁ b₂ ∧
      {z : ℂ | z.re ∈ Ioo a₁ a₂ ∧ z.im ∈ Ioo b₁ b₂} ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW z0 hz0
  refine ⟨z0.re - ε / 2, z0.re + ε / 2, z0.im - ε / 2, z0.im + ε / 2,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  intro z hz
  apply hball
  rw [Metric.mem_ball, Complex.dist_eq]
  obtain ⟨⟨hzr1, hzr2⟩, ⟨hzi1, hzi2⟩⟩ := hz
  have hre : |z.re - z0.re| < ε / 2 := by rw [abs_lt]; constructor <;> linarith
  have him : |z.im - z0.im| < ε / 2 := by rw [abs_lt]; constructor <;> linarith
  calc ‖z - z0‖ ≤ |(z - z0).re| + |(z - z0).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - z0.re| + |z.im - z0.im| := by simp [Complex.sub_re, Complex.sub_im]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Planar level-set nullity of a nowhere-locally-constant harmonic potential.** For `u` harmonic
on the open set `U` with `gradC u` nowhere locally identically zero on `U`, every level set
`{z ∈ U | u z = δ}` has planar measure zero.  Split it at the critical set `{gradC u = 0}` (null
by `gradC_zeroSet_null`); off the critical set one partial `∂_x u` or `∂_y u` is nonzero, so on an
open rectangle around each such point (`exists_rect_subset_of_isOpen`) the level set meets each
axis-parallel line in at most one point (`subsingleton_{vertical,horizontal}_slice_of_deriv_ne`),
hence is null by Fubini (`volume_eq_zero_of_subsingleton_{vertical,horizontal}_slice`).  A countable
subcover (`TopologicalSpace.isOpen_biUnion_countable`) of these rectangles covers the off-critical
part, so it too is null. -/
theorem levelSet_volume_zero {u : ℂ → ℝ} {U : Set ℂ} {δ : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0)) :
    volume {z : ℂ | z ∈ U ∧ u z = δ} = 0 := by
  classical
  set L : Set ℂ := {z : ℂ | z ∈ U ∧ u z = δ} with hL
  have hucont : ContinuousOn u U := hu.continuousOn
  -- L measurable
  have hLmeas : MeasurableSet L := by
    have hopen : IsOpen (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) :=
      hucont.isOpen_inter_preimage hU isOpen_ne
    have : L = U \ (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) := by
      ext z; simp only [hL, mem_setOf_eq, mem_diff, mem_inter_iff, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨hzU, hzδ⟩; exact ⟨hzU, fun h => h.2 hzδ⟩
      · rintro ⟨hzU, hne⟩; exact ⟨hzU, not_not.mp (fun h => hne ⟨hzU, h⟩)⟩
    rw [this]; exact hU.measurableSet.diff hopen.measurableSet
  -- split at critical set
  set Zc : Set ℂ := {z : ℂ | z ∈ U ∧ gradC u z = 0} with hZc
  set G : Set ℂ := {z : ℂ | z ∈ U ∧ u z = δ ∧ gradC u z ≠ 0} with hG
  have hLsplit : L ⊆ Zc ∪ G := by
    intro z hz
    obtain ⟨hzU, hzδ⟩ := hz
    by_cases hg : gradC u z = 0
    · exact Or.inl ⟨hzU, hg⟩
    · exact Or.inr ⟨hzU, hzδ, hg⟩
  have hZcnull : volume Zc = 0 := gradC_zeroSet_null hU hu hnc
  -- G is null: box cover
  have hGnull : volume G = 0 := by
    -- partials via gradC (continuous on U)
    have hgradcont : ContinuousOn (gradC u) U := (gradC_differentiableOn hu).continuousOn
    have hdiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
      fun z hz => differentiableAt_of_harmonicOnNhd hu hz
    have hIeq : ∀ z : ℂ, (fderiv ℝ u z) Complex.I = -(gradC u z).im := by
      intro z; rw [fderiv_eq_re_gradC_mul u z Complex.I, Complex.mul_I_re]
    have hOneEq : ∀ z : ℂ, (fderiv ℝ u z) 1 = (gradC u z).re := by
      intro z; rw [fderiv_eq_re_gradC_mul u z 1, mul_one]
    -- per point z0 ∈ G, choose a rectangle
    -- the open set where the vertical partial is nonzero (within U)
    have hOpenV : IsOpen (U ∩ {z : ℂ | (gradC u z).im ≠ 0}) :=
      hgradcont.isOpen_inter_preimage hU (isOpen_ne.preimage Complex.continuous_im)
    have hOpenH : IsOpen (U ∩ {z : ℂ | (gradC u z).re ≠ 0}) :=
      hgradcont.isOpen_inter_preimage hU (isOpen_ne.preimage Complex.continuous_re)
    -- rectangle-and-direction assignment
    set rect : ℝ → ℝ → ℝ → ℝ → Set ℂ :=
      fun a₁ a₂ b₁ b₂ => {z : ℂ | z.re ∈ Ioo a₁ a₂ ∧ z.im ∈ Ioo b₁ b₂} with hrect
    have hpick : ∀ z0 ∈ G, ∃ a₁ a₂ b₁ b₂ : ℝ, z0.re ∈ Ioo a₁ a₂ ∧ z0.im ∈ Ioo b₁ b₂ ∧
        ((rect a₁ a₂ b₁ b₂ ⊆ U ∧
            ∀ z ∈ rect a₁ a₂ b₁ b₂, (fderiv ℝ u z) Complex.I ≠ 0) ∨
          (rect a₁ a₂ b₁ b₂ ⊆ U ∧
            ∀ z ∈ rect a₁ a₂ b₁ b₂, (fderiv ℝ u z) 1 ≠ 0)) := by
      intro z0 hz0
      obtain ⟨hz0U, hz0δ, hz0g⟩ := hz0
      -- gradC ≠ 0 gives im ≠ 0 or re ≠ 0
      have hdir : (gradC u z0).im ≠ 0 ∨ (gradC u z0).re ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hz0g (Complex.ext hcon.2 hcon.1)
      rcases hdir with hv | hh
      · obtain ⟨a₁, a₂, b₁, b₂, hr, hi, hsub⟩ := exists_rect_subset_of_isOpen hOpenV
          (show z0 ∈ U ∩ {z : ℂ | (gradC u z).im ≠ 0} from ⟨hz0U, hv⟩)
        refine ⟨a₁, a₂, b₁, b₂, hr, hi, Or.inl ⟨fun z hz => (hsub hz).1, fun z hz => ?_⟩⟩
        rw [hIeq]; exact fun h => (hsub hz).2 (neg_eq_zero.mp h)
      · obtain ⟨a₁, a₂, b₁, b₂, hr, hi, hsub⟩ := exists_rect_subset_of_isOpen hOpenH
          (show z0 ∈ U ∩ {z : ℂ | (gradC u z).re ≠ 0} from ⟨hz0U, hh⟩)
        refine ⟨a₁, a₂, b₁, b₂, hr, hi, Or.inr ⟨fun z hz => (hsub hz).1, fun z hz => ?_⟩⟩
        rw [hOneEq]; exact (hsub hz).2
    choose! A1 A2 B1 B2 hAr hAi hAdir using hpick
    -- rectangle set for each point
    set R : ℂ → Set ℂ := fun z0 => rect (A1 z0) (A2 z0) (B1 z0) (B2 z0) with hR
    have hRopen : ∀ z0, IsOpen (R z0) := fun z0 =>
      (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
    -- countable subcover of the open cover of G
    obtain ⟨T, hTsub, hTcount, hTU⟩ :=
      TopologicalSpace.isOpen_biUnion_countable G R (fun z0 _ => hRopen z0)
    have hGcover : G ⊆ ⋃ z0 ∈ T, R z0 := by
      intro z hz
      rw [hTU]
      exact mem_biUnion hz ⟨hAr z hz, hAi z hz⟩
    -- each L ∩ R z0 (z0 ∈ T) is null
    have hpiece : ∀ z0 ∈ T, volume (L ∩ R z0) = 0 := by
      intro z0 hz0
      have hz0G : z0 ∈ G := hTsub hz0
      have hLRmeas : MeasurableSet (L ∩ R z0) := hLmeas.inter (hRopen z0).measurableSet
      -- L ∩ R z0 = {z | z ∈ R z0 ∧ u z = δ ∧ z ∈ U} ⊆ level set on the rectangle
      rcases hAdir z0 hz0G with ⟨hrsubU, hvne⟩ | ⟨hrsubU, hhne⟩
      · -- vertical subsingleton
        apply volume_eq_zero_of_subsingleton_vertical_slice hLRmeas
        intro x
        have hsub := subsingleton_vertical_slice_of_deriv_ne
          (u := u) (δ := δ) (a₁ := A1 z0) (a₂ := A2 z0) (b₁ := B1 z0) (b₂ := B2 z0)
          (fun z hzr hzi => hdiffU z (hrsubU ⟨hzr, hzi⟩))
          (fun z hzr hzi => hvne z ⟨hzr, hzi⟩) x
        intro y1 hy1 y2 hy2
        apply hsub
        · obtain ⟨hy1L, hy1R⟩ := hy1
          exact ⟨hy1R.1, hy1R.2, hy1L.2⟩
        · obtain ⟨hy2L, hy2R⟩ := hy2
          exact ⟨hy2R.1, hy2R.2, hy2L.2⟩
      · -- horizontal subsingleton
        apply volume_eq_zero_of_subsingleton_horizontal_slice hLRmeas
        intro y
        have hsub := subsingleton_horizontal_slice_of_deriv_ne
          (u := u) (δ := δ) (a₁ := A1 z0) (a₂ := A2 z0) (b₁ := B1 z0) (b₂ := B2 z0)
          (fun z hzr hzi => hdiffU z (hrsubU ⟨hzr, hzi⟩))
          (fun z hzr hzi => hhne z ⟨hzr, hzi⟩) y
        intro x1 hx1 x2 hx2
        apply hsub
        · obtain ⟨hx1L, hx1R⟩ := hx1
          exact ⟨hx1R.1, hx1R.2, hx1L.2⟩
        · obtain ⟨hx2L, hx2R⟩ := hx2
          exact ⟨hx2R.1, hx2R.2, hx2L.2⟩
    -- assemble
    have hGsub : G ⊆ ⋃ z0 ∈ T, (L ∩ R z0) := by
      intro z hz
      obtain ⟨i, hi, hiR⟩ := mem_iUnion₂.mp (hGcover hz)
      exact mem_biUnion hi ⟨(show z ∈ L from ⟨hz.1, hz.2.1⟩), hiR⟩
    refine le_antisymm ?_ (zero_le _)
    calc volume G ≤ volume (⋃ z0 ∈ T, (L ∩ R z0)) := measure_mono hGsub
      _ = 0 := (measure_biUnion_null_iff hTcount).2 hpiece
  refine le_antisymm ?_ (zero_le _)
  calc volume L ≤ volume (Zc ∪ G) := measure_mono hLsplit
    _ ≤ volume Zc + volume G := measure_union_le _ _
    _ = 0 := by rw [hZcnull, hGnull, add_zero]

/-- **A.e.-`ξ` angular slice nullity of a planar-null level set.** If the level set
`L = {z ∈ U | u z = δ}` (measurable) has planar measure zero, then for a.e. log-radius `ξ` the
angular slice `{θ ∈ (−π, π) | e^{ξ+θi} ∈ U ∧ u(e^{ξ+θi}) = δ}` has one-dimensional measure zero.
The log-polar change of variables (`Complex.lintegral_comp_polarCoord_symm`, then the radial
substitution `r = e^ξ` with positive Jacobian) writes the vanishing planar integral of `1_L` as an
iterated integral over `(ξ, θ)`, whose inner `θ`-integral is a.e.-`ξ` zero. -/
theorem ae_angularSlice_levelSet_null {u : ℂ → ℝ} {U : Set ℂ} {δ : ℝ}
    (hLmeas : MeasurableSet {z : ℂ | z ∈ U ∧ u z = δ})
    (hLnull : volume {z : ℂ | z ∈ U ∧ u z = δ} = 0) :
    ∀ᵐ ξ : ℝ, volume {θ : ℝ | θ ∈ Ioo (-π) π ∧
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ} = 0 := by
  classical
  set L : Set ℂ := {z : ℂ | z ∈ U ∧ u z = δ} with hLdef
  -- Slice indicator abbreviations
  set S : ℝ → Set ℝ := fun ξ => {θ : ℝ | θ ∈ Ioo (-π) π ∧
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ} with hSdef
  -- the (ξ, θ)-indicator of the pulled-back level set on the log-strip box
  set g : ℝ → ℝ → ℝ≥0∞ := fun ξ θ => (Ioo (-π) π).indicator
    (fun θ' => L.indicator (fun _ => (1 : ℝ≥0∞))
      (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ with hgdef
  -- the inner θ-integral of `g ξ` is the measure of the slice `S ξ`
  have hinner : ∀ ξ : ℝ, (∫⁻ θ, g ξ θ) = volume (S ξ) := by
    intro ξ
    have hmeasθ : MeasurableSet {θ : ℝ |
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable hLmeas
    have hSeq : S ξ = Ioo (-π) π ∩ {θ : ℝ |
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L} := by
      ext θ
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, ⟨h2, h3⟩⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    calc (∫⁻ θ, g ξ θ)
        = ∫⁻ θ, (Ioo (-π) π ∩ {θ'' : ℝ |
            Complex.exp ((ξ : ℂ) + (θ'' : ℂ) * Complex.I) ∈ L}).indicator
              (fun _ => (1 : ℝ≥0∞)) θ := by
          refine lintegral_congr fun θ => ?_
          simp only [hgdef, Set.indicator_apply, mem_inter_iff, mem_setOf_eq, mem_Ioo]
          by_cases h1 : -π < θ ∧ θ < π <;> by_cases h2 : Complex.exp
              ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L <;> simp [h1, h2]
      _ = volume (S ξ) := by
          rw [lintegral_indicator (measurableSet_Ioo.inter hmeasθ), setLIntegral_one, hSeq]
  -- log-polar change of variables: the weighted `ξ`-integral of the slice measure vanishes
  set G : ℂ → ℝ≥0∞ := L.indicator (fun _ => (1 : ℝ≥0∞)) with hGdef
  have hGmeas : Measurable G := measurable_const.indicator hLmeas
  set R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-π) π with hRdef
  have hRMeas : MeasurableSet R := measurableSet_Ioi.prod measurableSet_Ioo
  have hsymmMeas : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have heq : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [heq]; exact Continuous.measurable (by fun_prop)
  -- Step 1: the polar integral equals `volume L = 0`; the target is `R`
  have hRtarget : polarCoord.target = R := Complex.polarCoord_target
  have hpolar : ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) = 0 := by
    have hcov := Complex.lintegral_comp_polarCoord_symm G
    rw [← hRtarget]
    calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)
        = ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p) := by
          simp only [smul_eq_mul]
      _ = ∫⁻ z, G z := hcov
      _ = 0 := by rw [hGdef, lintegral_indicator hLmeas, setLIntegral_one, hLnull]
  -- Step 2: Tonelli on `R` and the radial substitution `r = e^ξ`
  have hintegrand_meas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hGmeas.comp hsymmMeas)
  have hTon : ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)
      = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict R
        = ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
            ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
      rw [hRdef, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hprod]; exact lintegral_prod _ hintegrand_meas.aemeasurable
  have hsub : ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))
      = ∫⁻ ξ : ℝ, ENNReal.ofReal (Real.exp ξ) * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Real.exp ξ) * G (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    have himg : Real.exp '' univ = Ioi (0 : ℝ) := by
      ext r; simp only [image_univ, mem_range, mem_Ioi]
      constructor
      · rintro ⟨x, rfl⟩; exact Real.exp_pos x
      · intro hr; exact ⟨Real.log r, Real.exp_log hr⟩
    rw [← himg,
      lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine lintegral_congr fun ξ => ?_
    rw [abs_of_pos (Real.exp_pos ξ)]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θ (_ : θ ∈ Ioo (-π) π) => ?_)
    rw [polarCoord_symm_exp]
  -- combine: `∫⁻ ξ, exp ξ · (exp ξ · (∫⁻ θ g ξ θ)) = 0`
  have hfinal : ∫⁻ ξ : ℝ, ENNReal.ofReal (Real.exp ξ)
      * (ENNReal.ofReal (Real.exp ξ) * (∫⁻ θ, g ξ θ)) = 0 := by
    rw [← hpolar, hTon, hsub]
    refine lintegral_congr fun ξ => ?_
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hθmeas : MeasurableSet {θ : ℝ |
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable hLmeas
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun θ => ?_
    simp only [hgdef, Set.indicator_apply, hGdef]
    by_cases h1 : θ ∈ Ioo (-π) π <;>
      by_cases h2 : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L <;> simp [h1, h2]
  -- measurability of the inner slice integral in `ξ`
  have hgjoint : Measurable (Function.uncurry g) := by
    have hexpmap : Measurable fun p : ℝ × ℝ =>
        Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).measurable
    have h1 : Measurable fun p : ℝ × ℝ => G (Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) :=
      hGmeas.comp hexpmap
    have h2 : Measurable fun p : ℝ × ℝ => (Ioo (-π) π).indicator
        (fun _ : ℝ => G (Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) p.2 := by
      have : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π} :=
        measurable_snd measurableSet_Ioo
      exact h1.indicator this
    simpa only [Function.uncurry, hgdef] using h2
  have hglint_meas : Measurable fun ξ : ℝ => ∫⁻ θ, g ξ θ := hgjoint.lintegral_prod_right
  -- conclude: a.e.-ξ the slice measure vanishes
  have hae : ∀ᵐ ξ : ℝ, ENNReal.ofReal (Real.exp ξ)
      * (ENNReal.ofReal (Real.exp ξ) * (∫⁻ θ, g ξ θ)) = 0 :=
    (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((ENNReal.measurable_ofReal.comp Real.measurable_exp).mul hglint_meas))).mp hfinal
  -- strip the positive `exp ξ` factors
  filter_upwards [hae] with ξ hξ
  rw [← hinner ξ]
  have hexp0 : ENNReal.ofReal (Real.exp ξ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos ξ)).ne'
  have := hξ
  rw [mul_eq_zero, mul_eq_zero] at this
  rcases this with h | h | h
  · exact absurd h hexp0
  · exact absurd h hexp0
  · exact h

/-- **Radial right-derivative of the windowed truncated integrand off the level set.** For `u`
harmonic on the open `U` with the superlevel window intersection compactly contained in `U`, at any
`(ξ, θ)` whose exponential does not lie on the level set `{u = δ}`, the radial line map
`x ↦ windowedTruncIntegrand u U δ (x + θi)` is differentiable at `ξ` with derivative the superlevel
indicator of `(Re expGrad)² + (u∘exp − δ)·Re (deriv expGrad)`.  Off the compact containment the map
is locally `0`; on the superlevel set the two smooth factors give the product rule; on the strict
sublevel set the map is locally `0` again. -/
theorem hasDerivAt_windowedTruncIntegrand_radial {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ ξ θ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hK : closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) ⊆ U)
    (hξ : ξ ∈ Ioo ζ₁ ζ₂) (hθmem : θ ∈ Icc (-π) π)
    (hne : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≠ δ) :
    HasDerivAt (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
      ({θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}.indicator
        (fun _ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
            * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ) ξ := by
  set w₀ : ℂ := (ξ : ℂ) + (θ : ℂ) * Complex.I with hw₀
  set z₀ : ℂ := Complex.exp w₀ with hz₀
  set P : Set ℝ := {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
    with hP
  have hexpline : ContinuousAt (fun x : ℝ => Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) ξ :=
    (Complex.continuous_exp.comp (by fun_prop :
      Continuous fun x : ℝ => (x : ℂ) + (θ : ℂ) * Complex.I)).continuousAt
  by_cases hzU : z₀ ∈ U
  · -- `exp w₀ ∈ U`: split on `u z₀ > δ` (superlevel) vs `u z₀ < δ` (sublevel)
    have hnhdU : {x : ℝ | Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U} ∈ nhds ξ :=
      hexpline.preimage_mem_nhds (hU.mem_nhds hzU)
    have hcu' : ContinuousAt (fun x : ℝ => u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ξ :=
      (hasDerivAt_uexp_radial (θ := θ) (differentiableAt_of_harmonicOnNhd hu hzU)).continuousAt
    rcases lt_or_gt_of_ne (hne hzU) with hlt | hgt
    · -- sublevel: `(u∘exp − δ)⁺ = 0` on a neighbourhood, so the integrand is locally `0`
      have hθP : θ ∉ P := by
        simp only [hP, mem_setOf_eq, superLevelU, mem_setOf_eq, not_and]
        exact fun _ => not_lt.mpr hlt.le
      rw [Set.indicator_of_notMem hθP]
      have hloc : (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
          =ᶠ[nhds ξ] fun _ => (0 : ℝ) := by
        have hsub : {x : ℝ | u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) < δ} ∈ nhds ξ :=
          hcu'.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
        filter_upwards [hsub, hnhdU] with x hx hxU
        unfold windowedTruncIntegrand
        rw [Set.indicator_of_mem hxU,
          posPart_eq_zero.mpr (by linarith [hx]), zero_mul]
      exact (hasDerivAt_const ξ (0 : ℝ)).congr_of_eventuallyEq hloc
    · -- superlevel: product rule for `(u∘exp − δ)·Re (expGrad)`
      have hθP : θ ∈ P := ⟨hzU, hgt⟩
      rw [Set.indicator_of_mem hθP]
      have hloc : (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
          =ᶠ[nhds ξ] fun x : ℝ => (u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) - δ)
            * (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re := by
        have hsup : {x : ℝ | δ < u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))} ∈ nhds ξ :=
          hcu'.preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)
        filter_upwards [hsup, hnhdU] with x hx hxU
        unfold windowedTruncIntegrand
        rw [Set.indicator_of_mem hxU,
          posPart_eq_self.mpr (by linarith [hx]), expGrad]
      have hu' := hasDerivAt_uexp_radial
        (θ := θ) (differentiableAt_of_harmonicOnNhd hu hzU)
      have hD := hasDerivAt_expGrad_radial (θ := θ) (expGrad_differentiableAt_open hU hu hzU)
      have hDre : HasDerivAt (fun x : ℝ => (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re)
          ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) ξ := by
        have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt ξ hD
        simpa [Function.comp] using hcomp
      have hprod := ((hu'.sub_const δ).mul hDre)
      refine (hprod.congr_deriv ?_).congr_of_eventuallyEq hloc
      ring
  · -- `exp w₀ ∉ U ⊆ᶜ K`: the integrand vanishes on a neighbourhood of `ξ`
    have hθP : θ ∉ P := by
      simp only [hP, mem_setOf_eq, superLevelU, mem_setOf_eq, not_and]
      exact fun h => absurd h hzU
    rw [Set.indicator_of_notMem hθP]
    have hwK : z₀ ∉ closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) :=
      fun h => hzU (hK h)
    have hnhd : {x : ℝ | Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∉
        closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂))} ∈ nhds ξ :=
      (Complex.continuous_exp.comp (by fun_prop :
        Continuous fun x : ℝ => (x : ℂ) + (θ : ℂ) * Complex.I)).continuousAt.preimage_mem_nhds
        (isClosed_closure.isOpen_compl.mem_nhds hwK)
    have hloc : (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
        =ᶠ[nhds ξ] fun _ => (0 : ℝ) := by
      have hstrip : {x : ℝ | ((x : ℂ) + (θ : ℂ) * Complex.I) ∈
          stripBox ζ₁ ζ₂ (-π) π} ∈ nhds ξ :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hξ) (fun x hx => by
          simp only [stripBox, mem_setOf_eq, re_logPolar, im_logPolar]
          exact ⟨hx.1, hx.2, hθmem.1, hθmem.2⟩)
      filter_upwards [hnhd, hstrip] with x hx hxstrip
      exact windowedTruncIntegrand_eq_zero_of_notMem hxstrip hx
    exact (hasDerivAt_const ξ (0 : ℝ)).congr_of_eventuallyEq hloc

/-- **The ring product of two bounded Lipschitz functions is Lipschitz.** On a set where `f` and
`g` are `Lipschitz` with constants `Kf, Kg` and bounded in norm by `Bf, Bg`, the pointwise product
`f · g` is Lipschitz with constant `Bf·Kg + Bg·Kf`. -/
theorem lipschitzOnWith_mul_of_bounded {α : Type*} [PseudoMetricSpace α] {s : Set α}
    {f g : α → ℝ} {Kf Kg Bf Bg : NNReal}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hBf : ∀ x ∈ s, ‖f x‖ ≤ Bf) (hBg : ∀ x ∈ s, ‖g x‖ ≤ Bg) :
    LipschitzOnWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hfd := (lipschitzOnWith_iff_dist_le_mul.mp hf) x hx y hy
  have hgd := (lipschitzOnWith_iff_dist_le_mul.mp hg) x hx y hy
  have hstep : dist (f x * g x) (f y * g y)
      ≤ ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := by
    simp only [Real.dist_eq]
    calc |f x * g x - f y * g y|
        = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
      _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
      _ = ‖f x‖ * |g x - g y| + ‖g y‖ * |f x - f y| := by
          rw [abs_mul, abs_mul]; simp only [Real.norm_eq_abs]; ring
  calc dist (f x * g x) (f y * g y)
      ≤ ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := hstep
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) + (Bg : ℝ) * ((Kf : ℝ) * dist x y) := by
        gcongr
        · exact hBf x hx
        · exact hBg y hy
    _ = ((Bf * Kg + Bg * Kf : NNReal) : ℝ) * dist x y := by push_cast; ring

/-- **Local Lipschitz continuity of the windowed truncated integrand.** For `u` harmonic on the open
`U` with the superlevel window intersection compactly contained in `U`, the integrand
`windowedTruncIntegrand u U δ` is locally Lipschitz on the log-strip box `stripBox ζ₁' ζ₂' (−π) π`:
off the compact containment it is locally `0`, and near a point whose exponential lies in `U` it is
the product of the locally-Lipschitz factors `(u∘exp − δ)⁺` (Lipschitz `posPart` of a `C²` map) and
`Re (expGrad u)` (real part of a holomorphic map), both locally bounded. -/
theorem locallyLipschitzOn_windowedTruncIntegrand {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hK : closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) ⊆ U) :
    LocallyLipschitzOn (stripBox ζ₁ ζ₂ (-π) π) (windowedTruncIntegrand u U δ) := by
  intro w₀ hw₀
  by_cases hzU : Complex.exp w₀ ∈ U
  · -- near a point whose exponential lies in `U`, the integrand is a bounded Lipschitz product
    set F : ℂ → ℝ := fun w : ℂ => (u (Complex.exp w) - δ)⁺ * (expGrad u w).re with hF
    have hnhdU : Complex.exp ⁻¹' U ∈ nhds w₀ :=
      (hU.preimage Complex.continuous_exp).mem_nhds hzU
    have hHeq : ∀ w ∈ Complex.exp ⁻¹' U, windowedTruncIntegrand u U δ w = F w := by
      intro w hw
      unfold windowedTruncIntegrand
      rw [Set.indicator_of_mem (show Complex.exp w ∈ U from hw)]
      simp only [hF, expGrad]
    -- factor 1: `(u∘exp − δ)⁺` is locally Lipschitz (posPart of a `C²` map)
    have hcexp : ContDiffAt ℝ 2 Complex.exp w₀ :=
      (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt
    have hcd : ContDiffAt ℝ 2 (fun w : ℂ => u (Complex.exp w)) w₀ :=
      (hu.contDiffOn.contDiffAt (hU.mem_nhds hzU)).comp w₀ hcexp
    obtain ⟨K1, s1, hs1, hL1⟩ :=
      ((hcd.hasStrictFDerivAt (by norm_num)).sub_const δ).exists_lipschitzOnWith
    have hLpos : LipschitzOnWith K1 (fun w : ℂ => (u (Complex.exp w) - δ)⁺) s1 := by
      have := lipschitzWith_posPart.comp_lipschitzOnWith hL1
      rwa [one_mul] at this
    -- factor 2: `Re (expGrad u) = (fderiv ℝ u ∘ exp) applied to exp` is `C¹`,
    -- hence locally Lipschitz
    have hueq : (fun w : ℂ => (expGrad u w).re)
        = fun w : ℂ => (fderiv ℝ u (Complex.exp w)) (Complex.exp w) := by
      funext w; rw [expGrad, fderiv_eq_re_gradC_mul]
    have hufd : ContDiffAt ℝ 1 (fun z : ℂ => fderiv ℝ u z) (Complex.exp w₀) :=
      (hu.contDiffOn.contDiffAt (hU.mem_nhds hzU)).fderiv_right (m := 1) (by norm_num)
    have hcd2 : ContDiffAt ℝ 1 (fun w : ℂ => (expGrad u w).re) w₀ := by
      rw [hueq]
      have hpair : ContDiffAt ℝ 1
          (fun w : ℂ => (fderiv ℝ u (Complex.exp w), Complex.exp w)) w₀ :=
        (hufd.comp w₀ (hcexp.of_le (by norm_num))).prodMk (hcexp.of_le (by norm_num))
      exact (isBoundedBilinearMap_apply.contDiff.contDiffAt).comp w₀ hpair
    obtain ⟨K2, s2, hs2, hL2⟩ :=
      (hcd2.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
    -- boundedness on a neighbourhood of `w₀` (continuity)
    have hc1 : ContinuousAt (fun w : ℂ => (u (Complex.exp w) - δ)⁺) w₀ :=
      (continuous_posPart.continuousAt).comp (hcd.continuousAt.sub continuousAt_const)
    have hc2 : ContinuousAt (fun w : ℂ => (expGrad u w).re) w₀ := hcd2.continuousAt
    have hb1 : {w : ℂ | ‖(u (Complex.exp w) - δ)⁺‖ ≤ ‖(u (Complex.exp w₀) - δ)⁺‖ + 1} ∈ nhds w₀ :=
      hc1.norm.eventually_le_const (by simp : ‖(u (Complex.exp w₀) - δ)⁺‖
        < ‖(u (Complex.exp w₀) - δ)⁺‖ + 1)
    have hb2 : {w : ℂ | ‖(expGrad u w).re‖ ≤ ‖(expGrad u w₀).re‖ + 1} ∈ nhds w₀ :=
      hc2.norm.eventually_le_const (by simp : ‖(expGrad u w₀).re‖ < ‖(expGrad u w₀).re‖ + 1)
    set B1 : NNReal := (‖(u (Complex.exp w₀) - δ)⁺‖ + 1).toNNReal with hB1def
    set B2 : NNReal := (‖(expGrad u w₀).re‖ + 1).toNNReal with hB2def
    set t : Set ℂ := (Complex.exp ⁻¹' U ∩ (s1 ∩ s2)) ∩
      ({w | ‖(u (Complex.exp w) - δ)⁺‖ ≤ ‖(u (Complex.exp w₀) - δ)⁺‖ + 1} ∩
        {w | ‖(expGrad u w).re‖ ≤ ‖(expGrad u w₀).re‖ + 1}) with htdef
    have htnhd : t ∈ nhds w₀ :=
      inter_mem (inter_mem hnhdU (inter_mem hs1 hs2)) (inter_mem hb1 hb2)
    refine ⟨B1 * K2 + B2 * K1, t, nhdsWithin_le_nhds htnhd, ?_⟩
    have hprodLip : LipschitzOnWith (B1 * K2 + B2 * K1) F t := by
      refine lipschitzOnWith_mul_of_bounded
        (hLpos.mono (fun w hw => hw.1.2.1)) (hL2.mono (fun w hw => hw.1.2.2))
        (fun w hw => le_trans hw.2.1 (Real.le_coe_toNNReal _))
        (fun w hw => le_trans hw.2.2 (Real.le_coe_toNNReal _))
    intro x hx y hy
    rw [hHeq x hx.1.1, hHeq y hy.1.1]
    exact hprodLip hx hy
  · -- off `U`, `exp w₀ ∉ K`, so the integrand vanishes on a strip-box neighbourhood
    have hwK : Complex.exp w₀ ∉ closure (superLevelU U u δ ∩
        RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) := fun h => hzU (hK h)
    have hnhd : Complex.exp ⁻¹' (closure (superLevelU U u δ ∩
        RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)))ᶜ ∈ nhds w₀ :=
      (isClosed_closure.isOpen_compl.preimage Complex.continuous_exp).mem_nhds hwK
    refine ⟨0, stripBox ζ₁ ζ₂ (-π) π ∩
      Complex.exp ⁻¹' (closure (superLevelU U u δ ∩
        RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)))ᶜ,
      inter_mem_nhdsWithin _ hnhd, ?_⟩
    intro x hx y hy
    rw [windowedTruncIntegrand_eq_zero_of_notMem hx.1 hx.2,
      windowedTruncIntegrand_eq_zero_of_notMem hy.1 hy.2]
    simp

/-- **Lipschitz continuity of the truncated rough flux.** For `u` harmonic on the open `U`,
continuous on `closure U` and vanishing on the inner frontier, the truncated rough flux
`truncRoughFlux u U δ` is Lipschitz on `[ζ₁, ζ₂]` (`ζ₂ < 0`, `δ > 0`): enlarging the window slightly
to `(ζ₁', ζ₂')` with `ζ₂' < 0`, its full-circle integrand `windowedTruncIntegrand u U δ` is globally
Lipschitz on the compact log-strip slab with constant `K₀` (local Lipschitz on a compact set), so
the `θ`-integral of the two-point radial difference is bounded by `2π·K₀·|ξ − ξ'|`. -/
theorem lipschitzOnWith_truncRoughFlux {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U)) (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hδ : 0 < δ) (h12 : ζ₁ ≤ ζ₂) (hζ₂ : ζ₂ < 0) :
    ∃ L : NNReal, LipschitzOnWith L (truncRoughFlux u U δ) (uIcc ζ₁ ζ₂) := by
  have hπ := Real.pi_pos
  -- enlarge the window: `ζ₁' < ζ₁ ≤ ζ₂ < ζ₂' < 0`
  set ζ₁' : ℝ := ζ₁ - 1 with hζ₁'
  set ζ₂' : ℝ := (ζ₂ + 0) / 2 with hζ₂'
  have hζ₂'0 : ζ₂' < 0 := by rw [hζ₂']; linarith
  have hζ₁'lt : ζ₁' < ζ₁ := by rw [hζ₁']; linarith
  have hζ₂lt : ζ₂ < ζ₂' := by rw [hζ₂']; linarith
  have hK := (closure_superLevel_window_subset (u := u) (U := U) (δ := δ)
    (ζ₁ := ζ₁') (ζ₂ := ζ₂') hucont hE0 hδ hζ₂'0).2
  -- the closed slab `[ζ₁, ζ₂] × [−π, π]` is compact and sits in the open strip `(ζ₁', ζ₂')`
  set C : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Icc ζ₁ ζ₂ ×ˢ Icc (-π) π) with hCdef
  have hCcompact : IsCompact C := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hCsub : C ⊆ stripBox ζ₁' ζ₂' (-π) π := by
    rintro w ⟨⟨x, θ⟩, ⟨hx, hθ⟩, rfl⟩
    simp only [stripBox, mem_setOf_eq, re_logPolar, im_logPolar]
    exact ⟨lt_of_lt_of_le hζ₁'lt hx.1, lt_of_le_of_lt hx.2 hζ₂lt, hθ.1, hθ.2⟩
  obtain ⟨K₀, hK₀⟩ :=
    ((locallyLipschitzOn_windowedTruncIntegrand hU hu hK).mono
      hCsub).exists_lipschitzOnWith_of_compact hCcompact
  -- per-`θ` radial two-point bound and integration over `(−π, π)`
  refine ⟨(2 * π).toNNReal * K₀, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro ξ hξ ξ' hξ'
  rw [uIcc_of_le h12] at hξ hξ'
  rw [truncRoughFlux_eq_integral_windowedTruncIntegrand,
    truncRoughFlux_eq_integral_windowedTruncIntegrand, Real.dist_eq]
  set H : ℂ → ℝ := windowedTruncIntegrand u U δ with hHdef
  -- membership of the slab
  have hmemC : ∀ x : ℝ, x ∈ Icc ζ₁ ζ₂ → ∀ θ : ℝ, θ ∈ Ioo (-π) π →
      ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ C := fun x hx θ hθ =>
    ⟨(x, θ), ⟨hx, ⟨hθ.1.le, hθ.2.le⟩⟩, by apply Complex.ext <;> simp⟩
  -- per-θ two-point Lipschitz bound from the slab Lipschitz constant
  have hptwise : ∀ θ ∈ Ioo (-π) π, ‖H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
      - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ (K₀ : ℝ) * |ξ - ξ'| := by
    intro θ hθ
    have hd := (lipschitzOnWith_iff_dist_le_mul.mp hK₀) _ (hmemC ξ hξ θ hθ) _ (hmemC ξ' hξ' θ hθ)
    rw [Real.dist_eq, Complex.dist_eq] at hd
    have hdiff : ((ξ : ℂ) + (θ : ℂ) * Complex.I) - ((ξ' : ℂ) + (θ : ℂ) * Complex.I)
        = (ξ - ξ' : ℝ) := by push_cast; ring
    rw [hdiff, Complex.norm_real] at hd
    exact hd
  -- integrability of both integrand slices (continuous on the compact slab, hence on `(−π, π)`)
  have hcontH : ContinuousOn H (stripBox ζ₁' ζ₂' (-π) π) :=
    continuousOn_windowedTruncIntegrand hU hu hK
  have hslice : ∀ x : ℝ, x ∈ Icc ζ₁ ζ₂ →
      IntegrableOn (fun θ : ℝ => H ((x : ℂ) + (θ : ℂ) * Complex.I)) (Ioo (-π) π) := by
    intro x hx
    have hxstrip : ζ₁' < x ∧ x < ζ₂' := ⟨lt_of_lt_of_le hζ₁'lt hx.1, lt_of_le_of_lt hx.2 hζ₂lt⟩
    exact (continuousOn_slice_of_continuousOn_stripBox hcontH hxstrip.1
      hxstrip.2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- the difference integral is bounded by the constant integrated over `(−π, π)`
  have hdiffint : IntegrableOn (fun θ : ℝ => H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
      - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)) (Ioo (-π) π) :=
    (hslice ξ hξ).sub (hslice ξ' hξ')
  calc |(∫ θ in Ioo (-π) π, H ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        - ∫ θ in Ioo (-π) π, H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)|
      = |∫ θ in Ioo (-π) π, (H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
          - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I))| := by
        rw [integral_sub (hslice ξ hξ) (hslice ξ' hξ')]
    _ ≤ ∫ θ in Ioo (-π) π, ‖H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
          - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ _θ in Ioo (-π) π, (K₀ : ℝ) * |ξ - ξ'| := by
        refine setIntegral_mono_on hdiffint.norm
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioo (fun θ hθ => hptwise θ hθ)
    _ = ((2 * π).toNNReal * K₀ : NNReal) * |ξ - ξ'| := by
        rw [setIntegral_const]
        have hvol : (volume (Ioo (-π) π)).toReal = 2 * π := by
          rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; ring
        rw [MeasureTheory.measureReal_def, hvol, smul_eq_mul]
        push_cast [Real.coe_toNNReal (2 * π) (by positivity)]
        ring

/-- **The `ξ`-derivative of the truncated rough flux is the superlevel-slice energy.** For `u`
harmonic on the open `U`, at any interior log-radius `ξ ∈ (ζ₁, ζ₂)` whose angular slice meets the
level set `{u = δ}` in a null set, the truncated rough flux `truncRoughFlux u U δ` has derivative
`sliceEnergyU u (superLevelU U u δ) ξ`.  Differentiation under the `θ`-integral of the
strip-box-Lipschitz windowed integrand (a.e.-`θ` radial product rule off the level set, dominated by
the slab Lipschitz constant) gives `∫_slice [(Re expGrad)² + (u−δ)·Re (deriv expGrad)]`, which the
branch-cut-free `θ`-IBP `setIntegral_slice_posPart_re_deriv_expGrad` rewrites to
`∫_slice |expGrad|²`. -/
theorem hasDerivAt_truncRoughFlux_of_slice_null {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U)) (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hcontR : Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEIntδ : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSliceδ U u δ ξ))
    (hδ : 0 < δ) (hζ₂ : ζ₂ < 0) (hξ : ξ ∈ Ioo ζ₁ ζ₂)
    (hnull : volume {θ : ℝ | θ ∈ Ioo (-π) π ∧
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ} = 0) :
    HasDerivAt (truncRoughFlux u U δ) (sliceEnergyU u (superLevelU U u δ) ξ) ξ := by
  have hπ := Real.pi_pos
  set V : Set ℂ := superLevelU U u δ with hVdef
  have hVopen : IsOpen V := isOpen_superLevelU hU hu δ
  -- enlarge the window and take the compact slab Lipschitz constant for the dominator
  set ζ₁' : ℝ := ζ₁ - 1 with hζ₁'
  set ζ₂' : ℝ := ζ₂ / 2 with hζ₂'
  have hζ₂'0 : ζ₂' < 0 := by rw [hζ₂']; linarith
  have hζ₁'lt : ζ₁' < ξ := by rw [hζ₁']; linarith [hξ.1]
  have hξlt2 : ξ < ζ₂' := by rw [hζ₂']; linarith [hξ.2]
  have hK := (closure_superLevel_window_subset (u := u) (U := U) (δ := δ)
    (ζ₁ := ζ₁') (ζ₂ := ζ₂') hucont hE0 hδ hζ₂'0).2
  -- a compact slab neighbourhood of `ξ` in the log-radius, inside the open strip `(ζ₁', ζ₂')`
  set r : ℝ := min (ξ - ζ₁') (ζ₂' - ξ) / 2 with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]; have h1 : 0 < ξ - ζ₁' := by linarith
    have h2 : 0 < ζ₂' - ξ := by linarith
    positivity
  have hrsub : Icc (ξ - r) (ξ + r) ⊆ Ioo ζ₁' ζ₂' := by
    intro y hy
    have hmin := min_le_left (ξ - ζ₁') (ζ₂' - ξ)
    have hmin' := min_le_right (ξ - ζ₁') (ζ₂' - ξ)
    exact ⟨by simp only [hrdef] at hy ⊢; linarith [hy.1],
      by simp only [hrdef] at hy ⊢; linarith [hy.2]⟩
  set C : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Icc (ξ - r) (ξ + r) ×ˢ Icc (-π) π) with hCdef
  have hCcompact : IsCompact C := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hCsub : C ⊆ stripBox ζ₁' ζ₂' (-π) π := by
    rintro w ⟨⟨x, θ⟩, ⟨hx, hθ⟩, rfl⟩
    have hxIoo := hrsub hx
    simp only [stripBox, mem_setOf_eq, re_logPolar, im_logPolar]
    exact ⟨hxIoo.1, hxIoo.2, hθ.1, hθ.2⟩
  obtain ⟨K₀, hK₀⟩ :=
    ((locallyLipschitzOn_windowedTruncIntegrand hU hu hK).mono
      hCsub).exists_lipschitzOnWith_of_compact hCcompact
  set H : ℂ → ℝ := windowedTruncIntegrand u U δ with hHdef
  -- the derivative-value slice integrand
  set F' : ℝ → ℝ := fun θ =>
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V}.indicator
      (fun _ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ with hF'def
  have hslabmem : ∀ x : ℝ, x ∈ Metric.ball ξ r → ∀ θ : ℝ, θ ∈ Icc (-π) π →
      ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ C := by
    intro x hx θ hθ
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
    exact ⟨(x, θ), ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, hθ⟩, by apply Complex.ext <;> simp⟩
  -- strip-box continuity of `H` for slice integrability/measurability
  have hcontH : ContinuousOn H (stripBox ζ₁' ζ₂' (-π) π) :=
    continuousOn_windowedTruncIntegrand hU hu hK
  have hsliceIcc : ∀ x : ℝ, x ∈ Ioo ζ₁' ζ₂' →
      IntegrableOn (fun θ : ℝ => H ((x : ℂ) + (θ : ℂ) * Complex.I)) (Ioc (-π) π) := fun x hx =>
    (continuousOn_slice_of_continuousOn_stripBox hcontH hx.1 hx.2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hslice : ∀ x : ℝ, x ∈ Ioo ζ₁' ζ₂' →
      IntegrableOn (fun θ : ℝ => H ((x : ℂ) + (θ : ℂ) * Complex.I)) (Ioo (-π) π) := fun x hx =>
    (continuousOn_slice_of_continuousOn_stripBox hcontH hx.1 hx.2).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  -- a.e.-θ (within `(−π, π)`) the level set is avoided (from the null slice hypothesis)
  have hae_ne : ∀ᵐ θ : ℝ, θ ∈ Ioo (-π) π →
      (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U →
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≠ δ) := by
    have hcompl : ∀ᵐ θ : ℝ, ¬ (θ ∈ Ioo (-π) π ∧
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ) :=
      MeasureTheory.ae_iff.mpr (by simp only [not_not]; exact hnull)
    filter_upwards [hcompl] with θ hθ hθIoo hθU hθδ
    exact hθ ⟨hθIoo, hθU, hθδ⟩
  -- measurability of the derivative-value integrand `F'` (continuous on the open superlevel slice)
  have hPmeas : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} :=
    (hVopen.preimage (by fun_prop)).measurableSet
  have hDEGcont : ContinuousOn (deriv (expGrad u)) (Complex.exp ⁻¹' U) := by
    have hOopen : IsOpen (Complex.exp ⁻¹' U) := hU.preimage Complex.continuous_exp
    have hdiff : DifferentiableOn ℂ (expGrad u) (Complex.exp ⁻¹' U) := fun w hw =>
      (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
    exact (((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn)
  have hlinecont : Continuous fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hF'contOn : ContinuousOn (fun θ : ℝ =>
      (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} := by
    intro θ hθ
    have hmemU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.1
    have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hmemU
    have hlineθ : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      hlinecont.continuousAt
    have hEGθ : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := expGrad u) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (expGrad_differentiableAt_open hU hu hmemU).continuousAt hlineθ
    have hEGre : ContinuousAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      Complex.continuous_re.continuousAt.comp hEGθ
    have hexpθ : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := Complex.exp) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        Complex.continuous_exp.continuousAt hlineθ
    have hufun : ContinuousAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))) θ :=
      ContinuousAt.comp (g := u) (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hmemU).continuousAt hexpθ
    have hDEGθ :
        ContinuousAt (fun t : ℝ => deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := deriv (expGrad u))
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hlineθ
    have hDEGre :
        ContinuousAt (fun t : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      Complex.continuous_re.continuousAt.comp hDEGθ
    exact ((hEGre.pow 2).add ((hufun.sub continuousAt_const).mul hDEGre)).continuousWithinAt
  have hF'meas : AEStronglyMeasurable F' (volume.restrict (Set.uIoc (-π) π)) :=
    ((aestronglyMeasurable_indicator_iff hPmeas).mpr
      (hF'contOn.aestronglyMeasurable hPmeas)).restrict
  -- apply the strip-box-Lipschitz DUI
  have hDUI := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (F := fun (x : ℝ) (θ : ℝ) => H ((x : ℂ) + (θ : ℂ) * Complex.I))
    (F' := F') (x₀ := ξ) (a := -π) (b := π) (bound := fun _ => (K₀ : ℝ))
    (s := Metric.ball ξ r) (Metric.ball_mem_nhds ξ hr0) ?_ ?_ ?_ ?_ ?_ ?_
  · -- rewrite both integrals: `∫_θ H = truncRoughFlux` and `∫_θ F' = sliceEnergyU`
    have hleft : (fun x : ℝ => ∫ θ in (-π)..π, H ((x : ℂ) + (θ : ℂ) * Complex.I))
        = truncRoughFlux u U δ := by
      funext x
      rw [truncRoughFlux_eq_integral_windowedTruncIntegrand,
        integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π)]
    have hright : (∫ θ in (-π)..π, F' θ) = sliceEnergyU u V ξ := by
      -- `∫_θ F' = ∫_slice[(Re expGrad)² + (u−δ)·Re(deriv expGrad)]`, then the branch-cut-free
      -- θ-IBP `setIntegral_slice_posPart_re_deriv_expGrad` turns the second term into
      -- `∫_slice(Im expGrad)²`, summing to `∫_slice |expGrad|² = sliceEnergyU`.  Its escape/bound
      -- hypotheses hold on the superlevel slice (u = δ on ∂V by continuity; expGrad, deriv bounded
      -- on the compact circle-arc `{θ | exp ∈ closure V}`, transported by 2π-periodicity).
      classical
      have hπ2 : (0 : ℝ) < 2 * π := by positivity
      set S : Set ℝ := angularSliceδ U u δ ξ with hSdef
      have hSopen : IsOpen S := isOpen_angularSliceδ hU hu δ ξ
      have hSmeas : MeasurableSet S := hSopen.measurableSet
      have hSsub : S ⊆ Ioo (-π) π := angularSliceδ_subset δ ξ
      have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono hSsub)
      set P : Set ℝ := {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} with hPdef
      have hSP : S = Ioo (-π) π ∩ P := by
        ext θ
        simp only [hSdef, angularSliceδ, hPdef, hVdef, mem_inter_iff, mem_setOf_eq]
      have hSsubP : S ⊆ P := fun θ hθ => (hSP ▸ hθ).2
      -- every log-polar point at radius `ξ` lies in the compact window annulus
      have hannmem : ∀ t : ℝ, Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)
          ∈ RoundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂') := by
        intro t
        have hdist : dist (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) 0 = Real.exp ξ := by
          rw [dist_zero_right, Complex.norm_exp, re_logPolar]
        simp only [RoundAnnulus, mem_setOf_eq, hdist]
        exact ⟨Real.exp_lt_exp.mpr hζ₁'lt, Real.exp_lt_exp.mpr hξlt2⟩
      set gRe : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hgReD
      set gU : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with hgUD
      set gDE : ℝ → ℝ := fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hgDED
      set gNS : ℝ → ℝ := fun θ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        with hgNSD
      set gIm : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgImD
      -- per-reading continuity on the open slice `S`
      have hcontReadings : ∀ θ ∈ S, ContinuousAt gRe θ ∧ ContinuousAt gU θ ∧ ContinuousAt gDE θ
          ∧ ContinuousAt gNS θ ∧ ContinuousAt gIm θ := by
        intro θ hθ
        have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2.1
        have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hmem
        have hline : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
        have hEG : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := expGrad u) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (expGrad_differentiableAt_open hU hu hmem).continuousAt hline
        have hexpθ : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := Complex.exp)
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            Complex.continuous_exp.continuousAt hline
        refine ⟨Complex.continuous_re.continuousAt.comp hEG,
          ContinuousAt.comp (g := u)
            (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hexpθ,
          Complex.continuous_re.continuousAt.comp (ContinuousAt.comp (g := deriv (expGrad u))
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hline),
          Complex.continuous_normSq.continuousAt.comp hEG,
          Complex.continuous_im.continuousAt.comp hEG⟩
      -- escape hypothesis
      have hEsc : ∀ θ : ℝ,
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ closure (superLevelU U u δ) →
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∉ superLevelU U u δ →
          u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ := by
        intro θ hcl hnot
        set w : ℂ := Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) with hwD
        have hclV : w ∈ closure V := by rw [hVdef]; exact hcl
        have hnotV : w ∉ V := by rw [hVdef]; exact hnot
        have hann : w ∈ RoundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂') := hannmem θ
        have hVsubU : V ⊆ U := fun z hz => hz.1
        have hwU : w ∈ U := by
          have hin := (isOpen_roundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂')).inter_closure
            (t := V) ⟨hann, hclV⟩
          rw [inter_comm] at hin
          exact hK hin
        have hge : δ ≤ u w := by
          have hmap : MapsTo u V (Ici δ) := fun z hz => le_of_lt hz.2
          have := (hmap.closure_of_continuousOn (hucont.mono (closure_mono hVsubU))) hclV
          rwa [closure_Ici, mem_Ici] at this
        exact le_antisymm (le_of_not_gt (fun h => hnotV ⟨hwU, h⟩)) hge
      -- compact-arc bound transported by 2π-periodicity
      have hgper : Function.Periodic (fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          (2 * π) := fun θ => by
        simp only
        rw [show ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
            = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_periodic _]
      -- the log-polar readings are `2π`-periodic in the angle
      have hExp2πI : Complex.exp (2 * (π : ℂ) * Complex.I) = 1 := by
        rw [show (2 * (π : ℂ) * Complex.I) = 2 * ↑π * Complex.I by ring]
        exact Complex.exp_two_pi_mul_I
      have hEGperC : Function.Periodic (expGrad u) (2 * (π : ℂ) * Complex.I) := by
        intro w
        simp only [expGrad]
        rw [show w + 2 * (π : ℂ) * Complex.I = w + 2 * π * Complex.I by ring, Complex.exp_add,
          hExp2πI, mul_one]
      have hloctwo : ∀ θ : ℝ, ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
          = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
        intro θ; push_cast; ring
      have hexpper : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ => hgper θ
      have hgNSper : Function.Periodic gNS (2 * π) := fun θ => by
        rw [hgNSD]; simp only; rw [hloctwo θ, hEGperC]
      have hgUper : Function.Periodic gU (2 * π) := fun θ => by
        rw [hgUD]; simp only; rw [hexpper θ]
      have hgDEper : Function.Periodic gDE (2 * π) := fun θ => by
        rw [hgDED]; simp only
        rw [hloctwo θ, ← deriv_comp_add_const (expGrad u) (2 * (π : ℂ) * Complex.I),
          (funext fun x => hEGperC x : (fun x : ℂ => expGrad u (x + 2 * (π : ℂ) * Complex.I))
            = expGrad u)]
      set K₁ : Set ℂ := closure (V ∩ RoundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂')) with hK₁D
      set A : Set ℝ := Icc (-π) π ∩
        (fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ⁻¹' K₁ with hAD
      have hcexp : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
        fun_prop
      have hAcompact : IsCompact A :=
        isCompact_Icc.inter_right (isClosed_closure.preimage hcexp)
      set bnd : ℝ → ℝ := fun θ => gNS θ + (|gDE θ| + |gU θ|) with hbndD
      have hbndcont : ContinuousOn bnd A := by
        intro θ hθ
        have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hK hθ.2
        have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hmem
        have hline : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
        have hEG : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := expGrad u) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (expGrad_differentiableAt_open hU hu hmem).continuousAt hline
        have hexpθ : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := Complex.exp)
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            Complex.continuous_exp.continuousAt hline
        have hNS : ContinuousAt gNS θ := Complex.continuous_normSq.continuousAt.comp hEG
        have hDE : ContinuousAt gDE θ :=
          Complex.continuous_re.continuousAt.comp (ContinuousAt.comp (g := deriv (expGrad u))
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hline)
        have hUc : ContinuousAt gU θ :=
          ContinuousAt.comp (g := u)
            (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hexpθ
        exact (hNS.add (hDE.abs.add hUc.abs)).continuousWithinAt
      have hbndper : Function.Periodic bnd (2 * π) := fun θ => by
        rw [hbndD]; simp only; rw [hgNSper θ, hgDEper θ, hgUper θ]
      obtain ⟨Cb, hCb⟩ := hAcompact.bddAbove_image hbndcont
      -- transport the arc bound to every superlevel angle (combined exp + bnd periodicity)
      have hHper : Function.Periodic
          (fun θ : ℝ => (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I), bnd θ)) (2 * π) := fun θ => by
        simp only [Prod.mk.injEq]; exact ⟨hgper θ, hbndper θ⟩
      have hAllBdd : ∀ θ : ℝ,
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ →
          gNS θ ≤ Cb ∧ |gDE θ| ≤ Cb ∧ |gU θ| ≤ Cb := by
        intro θ hθV
        obtain ⟨y, hyIco, hyeq⟩ := hHper.exists_mem_Ico hπ2 θ (-π)
        rw [Prod.mk.injEq] at hyeq
        have hyIcc : y ∈ Icc (-π) π := ⟨hyIco.1, le_of_lt (by have := hyIco.2; linarith)⟩
        have hyV : Complex.exp ((ξ : ℂ) + (y : ℂ) * Complex.I) ∈ V := by
          rw [hVdef, ← hyeq.1]; exact hθV
        have hyA : y ∈ A := ⟨hyIcc, subset_closure ⟨hyV, hannmem y⟩⟩
        have hbnd_le : bnd y ≤ Cb := hCb ⟨y, hyA, rfl⟩
        have hbndθ : bnd θ ≤ Cb := hyeq.2 ▸ hbnd_le
        rw [hbndD] at hbndθ; simp only at hbndθ
        refine ⟨?_, ?_, ?_⟩
        · nlinarith [abs_nonneg (gDE θ), abs_nonneg (gU θ)]
        · nlinarith [Complex.normSq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)),
            abs_nonneg (gU θ)]
        · nlinarith [Complex.normSq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)),
            abs_nonneg (gDE θ)]
      have hbdd : ∃ C : ℝ, ∀ θ : ℝ,
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ →
          Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≤ C
          ∧ |(deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ C :=
        ⟨Cb, fun θ hθV => ⟨(hAllBdd θ hθV).1, (hAllBdd θ hθV).2.1⟩⟩
      -- integrabilities on the slice `S`
      have hIntNS : IntegrableOn gNS S := hEIntδ
      have hIntRe2 : IntegrableOn (fun θ => gRe θ ^ 2) S := by
        refine Integrable.mono' hIntNS
          ((ContinuousOn.aestronglyMeasurable (fun θ hθ =>
            ((hcontReadings θ hθ).1.pow 2).continuousWithinAt) hSmeas)) ?_
        filter_upwards [ae_restrict_mem hSmeas] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hgReD, hgNSD]; simp only
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im]
      have hIntIm2 : IntegrableOn
          (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) S := by
        refine Integrable.mono' hIntNS
          ((ContinuousOn.aestronglyMeasurable (fun θ hθ =>
            ((hcontReadings θ hθ).2.2.2.2.pow 2).continuousWithinAt) hSmeas)) ?_
        filter_upwards [ae_restrict_mem hSmeas] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hgNSD]; simp only
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
      have hIntProd : IntegrableOn (fun θ => (gU θ - δ) * gDE θ) S := by
        refine (integrableOn_const hSfin (C := (Cb + δ) * Cb)).mono'
          ((ContinuousOn.aestronglyMeasurable (fun θ hθ =>
            (((hcontReadings θ hθ).2.1.sub continuousAt_const).mul
              (hcontReadings θ hθ).2.2.1).continuousWithinAt) hSmeas)) ?_
        filter_upwards [ae_restrict_mem hSmeas] with θ hθ
        have hb := hAllBdd θ hθ.2
        rw [Real.norm_eq_abs, abs_mul]
        have hU1 : |gU θ - δ| ≤ Cb + δ := by
          rw [hgUD] at hb ⊢
          have := hb.2.2
          rw [abs_le] at this ⊢
          constructor <;> [linarith [this.1, hδ.le]; linarith [this.2]]
        have hD1 : |gDE θ| ≤ Cb := hb.2.1
        have hCbnn : (0 : ℝ) ≤ Cb := le_trans (abs_nonneg _) hb.2.1
        exact mul_le_mul hU1 hD1 (abs_nonneg _) (by linarith [hCbnn, hδ.le])
      -- assemble
      have hPmeas' : MeasurableSet P := (hVopen.preimage (by fun_prop)).measurableSet
      have hLHS : (∫ θ in (-π)..π, F' θ)
          = ∫ θ in S, (gRe θ ^ 2 + (gU θ - δ) * gDE θ) := by
        have hF'eq : F' = P.indicator (fun θ => gRe θ ^ 2 + (gU θ - δ) * gDE θ) := by
          funext θ; rw [hF'def]; rfl
        rw [hF'eq, ← integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π),
          setIntegral_indicator hPmeas', ← hSP]
      have hsplit : (∫ θ in S, (gRe θ ^ 2 + (gU θ - δ) * gDE θ))
          = (∫ θ in S, gRe θ ^ 2) + ∫ θ in S, (gU θ - δ) * gDE θ := by
        exact MeasureTheory.integral_add hIntRe2 hIntProd
      have hposEq : (∫ θ in S, (gU θ - δ) * gDE θ)
          = ∫ θ in angularSliceδ U u δ ξ,
            (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
              * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
        rw [hSdef]
        refine setIntegral_congr_fun (isOpen_angularSliceδ hU hu δ ξ).measurableSet
          (fun θ hθ => ?_)
        rw [hgUD, hgDED]; simp only
        rw [posPart_eq_self.mpr (by linarith [hθ.2.2] : (0:ℝ)
          ≤ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)]
      have hIBP :
          (∫ θ in angularSliceδ U u δ ξ,
              (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
                * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
            = ∫ θ in angularSliceδ U u δ ξ,
              (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 :=
        setIntegral_slice_posPart_re_deriv_expGrad hU hu hcontR hEsc hbdd
      have hcomb : (∫ θ in S, gNS θ)
          = (∫ θ in S, gRe θ ^ 2)
            + ∫ θ in S, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
        rw [← MeasureTheory.integral_add hIntRe2 hIntIm2]
        refine setIntegral_congr_fun hSmeas (fun θ _ => ?_)
        rw [hgNSD, hgReD]; simp only
        rw [Complex.normSq_apply]; ring
      rw [hLHS, hsplit, hposEq, hIBP, ← hSdef, ← hcomb, sliceEnergyU, hSdef,
        angularSliceδ_eq, hVdef]
    rw [hleft, hright] at hDUI
    exact hDUI.2
  · -- `hF_meas`
    filter_upwards [Metric.ball_mem_nhds ξ hr0] with x hx
    have hxIoo : x ∈ Ioo ζ₁' ζ₂' := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
      exact hrsub ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [Set.uIoc_of_le (by linarith : -π ≤ π)]
    exact ((continuousOn_slice_of_continuousOn_stripBox hcontH hxIoo.1 hxIoo.2).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · -- `hF_int` at `ξ`
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith : -π ≤ π)]
    exact hsliceIcc ξ ⟨hζ₁'lt, hξlt2⟩
  · -- `hF'_meas`
    exact hF'meas
  · -- `h_lipsch`: per-θ Lipschitz in `x` on the ball, uniform in θ (from the slab constant)
    refine Eventually.of_forall (fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by linarith : -π ≤ π)] at hθ
    have hθIcc : θ ∈ Icc (-π) π := Ioc_subset_Icc_self hθ
    rw [show Real.nnabs (K₀ : ℝ) = K₀ from by
      rw [Real.nnabs_of_nonneg (NNReal.coe_nonneg K₀), Real.toNNReal_coe]]
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hd := (lipschitzOnWith_iff_dist_le_mul.mp hK₀)
      _ (hslabmem x hx θ hθIcc) _ (hslabmem y hy θ hθIcc)
    rw [Real.dist_eq, Complex.dist_eq,
      show ((x : ℂ) + (θ : ℂ) * Complex.I) - ((y : ℂ) + (θ : ℂ) * Complex.I) = (x - y : ℝ) by
        push_cast; ring, Complex.norm_real, ← Real.dist_eq] at hd
    exact hd
  · -- `bound_integrable`
    exact _root_.intervalIntegrable_const
  · -- `h_diff`: a.e.-θ radial derivative off the level set (helper 1)
    have haeπ : ∀ᵐ θ : ℝ, θ ≠ π :=
      MeasureTheory.ae_iff.mpr (by simp only [not_ne_iff, setOf_eq_eq_singleton,
        MeasureTheory.measure_singleton])
    filter_upwards [hae_ne, haeπ] with θ hθne hθπ hθΙ
    rw [Set.uIoc_of_le (by linarith : -π ≤ π)] at hθΙ
    have hθIoo : θ ∈ Ioo (-π) π := ⟨hθΙ.1, lt_of_le_of_ne hθΙ.2 hθπ⟩
    exact hasDerivAt_windowedTruncIntegrand_radial hU hu hK ⟨hζ₁'lt, hξlt2⟩
      (Ioc_subset_Icc_self hθΙ) (hθne hθIoo)

/-- **Truncated-flux increment bounded by the total energy.** For `u` harmonic and strictly positive
on the open set `U`, continuous on `closure U` and vanishing on the part of `frontier U` inside the
unit disc, with the slice squared gradient integrable on every superlevel slice, if the window
`{e^{ζ₁} < |z| < e^{ζ₂}}` (`ζ₁ ≤ ζ₂ < 0`) has its superlevel intersection compactly contained in
`U` (`closure_superLevel_window_subset`), then for every `δ > 0` the truncated-flux increment is at
most the total Dirichlet energy `D(u; U)`.  The truncated flux is the fixed-window flux of the
continuous truncated integrand; its `ξ`-FTC integrates the superlevel-slice energy, which is the
window energy of `{u > δ} ∩ U`, monotone below `D(u; U)`. -/
theorem truncRoughFlux_sub_le_dirichletEnergy {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSliceδ U u δ ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤)
    (hδ : 0 < δ) (h12 : ζ₁ ≤ ζ₂) (hζ₂ : ζ₂ < 0) :
    truncRoughFlux u U δ ζ₂ - truncRoughFlux u U δ ζ₁ ≤ (dirichletEnergy u U).toReal := by
  set V : Set ℂ := superLevelU U u δ with hV
  have hVopen : IsOpen V := isOpen_superLevelU hU hu δ
  -- the superlevel-slice energy is the fixed-window flux derivative value
  set E : ℝ → ℝ := fun ξ => sliceEnergyU u V ξ with hE
  have hEnn : ∀ ξ, 0 ≤ E ξ := fun ξ =>
    setIntegral_nonneg (isOpen_angularSlice hVopen ξ).measurableSet
      fun θ _ => Complex.normSq_nonneg _
  -- The moving-domain flux-energy FTC for the truncated flux.
  -- Route (absolute-continuity FTC, avoiding an every-point radial derivative):
  --   (1) truncRoughFlux u U d . = the theta-integral of windowedTruncIntegrand (.+theta i) on the
  --       window (windowedTruncIntegrand is continuous on the strip box, by
  --       continuousOn_windowedTruncIntegrand, and its radial (u-d)^+ / Re expGrad factors are
  --       Lipschitz on the compact slab K = closure(V cap window) subset U), so truncRoughFlux u U
  --       d is Lipschitz, hence absolutely continuous on [z1, z2]
  --       (LipschitzOnWith.absolutelyContinuousOnInterval);
  --   (2) AbsolutelyContinuousOnInterval.integral_deriv_eq_sub gives
  --       (integral of deriv (truncRoughFlux u U d)) = truncRoughFlux .. z2 - truncRoughFlux .. z1;
  --   (3) for a.e. xi, the strip-box Lipschitz DUI
  --       (hasDerivAt_integral_of_dominated_loc_of_lip) yields
  --       HasDerivAt (truncRoughFlux u U d) (E xi) xi: its radial product rule gives
  --       (Re expGrad)^2 + (u-d)^+ * Re (deriv expGrad) on the slice and 0 off it, whose slice
  --       integral is E xi after setIntegral_slice_posPart_re_deriv_expGrad; therefore
  --       deriv (truncRoughFlux u U d) = E a.e. and (integral of deriv) = (integral of E).
  -- STEP A (LANDED): a.e.-xi angular slice nullity (`levelSet_volume_zero` +
  -- `ae_angularSlice_levelSet_null`), which needs `u` nowhere locally gradient-constant on `U`.
  -- STEP B (LANDED): `truncRoughFlux_eq_integral_windowedTruncIntegrand`.
  -- STEP C (LANDED): the branch-cut-free theta-IBP
  -- `setIntegral_slice_posPart_re_deriv_expGrad`:
  --   `int_slice (u-d)^+ Re(deriv expGrad) = int_slice (Im expGrad)^2`, valid even when `{u>d}`
  -- straddles the +-pi cut (full-circle case = periodic IBP
  -- `integral_full_posPart_re_deriv_expGrad`; proper case = rotate to a window `(a, a+2pi)` whose
  -- seam escapes `{u>d}`, arc-decompose via `setIntegral_windowSlice_posPart_re_deriv_expGrad`,
  -- transfer back by 2pi-periodicity).
  --
  -- REMAINING (DUI + AC-FTC assembly, still to be built):
  --   (i) `truncRoughFlux u U d` is Lipschitz on `[z1, z2]` (strip-box bound of the xi-partial of
  --       `windowedTruncIntegrand` on the compact slab K = closure(V cap window) subset U), hence
  --       AC (`LipschitzOnWith.absolutelyContinuousOnInterval`);
  --   (ii) at a.e. xi the strip-box Lipschitz DUI
  --       (`hasDerivAt_integral_of_dominated_loc_of_lip`) gives `HasDerivAt (truncRoughFlux u U d)`
  --       with value `int_theta [1_{u>d}(Re expGrad)^2 + (u-d)^+ Re(deriv expGrad)]` (off the null
  --       level slice from STEP A the posPart is locally smooth), which STEP C rewrites to `E xi`;
  --   (iii) so `deriv (truncRoughFlux u U d) = E` a.e., and
  --       `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` closes the FTC.
  -- STEP A needs `u` nowhere locally gradient-constant on `U`, a hypothesis absent from this
  -- theorem (it must be threaded from the ring data of `slope_le_energy_ringPotential'''`).
  have hFTC : truncRoughFlux u U δ ζ₂ - truncRoughFlux u U δ ζ₁ = ∫ ξ in ζ₁..ζ₂, E ξ := by
    -- level-set nullity: a.e.-ξ the angular slice meets `{u = δ}` in a null set
    have hLmeas : MeasurableSet {z : ℂ | z ∈ U ∧ u z = δ} := by
      have hopen : IsOpen (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) :=
        hu.continuousOn.isOpen_inter_preimage hU isOpen_ne
      have : {z : ℂ | z ∈ U ∧ u z = δ} = U \ (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) := by
        ext z; simp only [mem_setOf_eq, mem_diff, mem_inter_iff, mem_preimage, mem_setOf_eq]
        constructor
        · rintro ⟨hzU, hzδ⟩; exact ⟨hzU, fun h => h.2 hzδ⟩
        · rintro ⟨hzU, hne⟩; exact ⟨hzU, not_not.mp (fun h => hne ⟨hzU, h⟩)⟩
      rw [this]; exact hU.measurableSet.diff hopen.measurableSet
    have haeslice := ae_angularSlice_levelSet_null hLmeas (levelSet_volume_zero hU hu hnc)
    -- absolute continuity of the truncated flux on `[ζ₁, ζ₂]`
    obtain ⟨L, hL⟩ := lipschitzOnWith_truncRoughFlux hU hu hucont hE0 hδ h12 hζ₂
    have hAC : AbsolutelyContinuousOnInterval (truncRoughFlux u U δ) ζ₁ ζ₂ :=
      hL.absolutelyContinuousOnInterval
    -- a.e.-ξ (within `(ζ₁, ζ₂)`) the flux derivative is `E`
    have hderiv : ∀ᵐ ξ : ℝ, ξ ∈ Ioo ζ₁ ζ₂ →
        deriv (truncRoughFlux u U δ) ξ = E ξ := by
      filter_upwards [haeslice] with ξ hξnull hξIoo
      exact (hasDerivAt_truncRoughFlux_of_slice_null hU hu hucont hE0 (hcontR ξ) (hEInt ξ)
        hδ hζ₂ hξIoo hξnull).deriv
    -- FTC + a.e. derivative identification
    have haeζ₂ : ∀ᵐ ξ : ℝ, ξ ≠ ζ₂ :=
      MeasureTheory.ae_iff.mpr (by
        simp only [not_ne_iff, setOf_eq_eq_singleton, MeasureTheory.measure_singleton])
    rw [← hAC.integral_deriv_eq_sub]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le h12]
    filter_upwards [hderiv, haeζ₂] with ξ hξderiv hξne hξIoc
    exact hξderiv ⟨hξIoc.1, lt_of_le_of_ne hξIoc.2 hξne⟩
  rw [hFTC]
  -- the window integral of the superlevel-slice energy is bounded by the total energy
  have hIooeq : (∫ ξ in ζ₁..ζ₂, E ξ) = ∫ ξ in Ioo ζ₁ ζ₂, E ξ :=
    (integral_Ioo_eq_intervalIntegral h12 E).symm
  rw [hIooeq]
  -- `ofReal (∫_{Ioo} E) ≤ ∫⁻_{Ioo} ofReal E ≤ ∫⁻_{Iic ζ₂} ofReal E ≤ D(V) ≤ D(U)`
  have hVU : dirichletEnergy u V ≤ dirichletEnergy u U := dirichletEnergy_mono (fun z hz => hz.1)
  have htail : (∫⁻ ξ in Iic ζ₂, ENNReal.ofReal (E ξ)) ≤ dirichletEnergy u U :=
    le_trans (setLIntegral_tail_ofReal_sliceEnergyU_le hVopen ζ₂) hVU
  have hIoosub : Ioo ζ₁ ζ₂ ⊆ Iic ζ₂ := fun ξ hξ => hξ.2.le
  have hofReal : ENNReal.ofReal (∫ ξ in Ioo ζ₁ ζ₂, E ξ) ≤ dirichletEnergy u U := by
    calc ENNReal.ofReal (∫ ξ in Ioo ζ₁ ζ₂, E ξ)
        ≤ ∫⁻ ξ in Ioo ζ₁ ζ₂, ENNReal.ofReal (E ξ) :=
          ofReal_setIntegral_le_setLIntegral_ofReal measurableSet_Ioo (fun ξ _ => hEnn ξ)
      _ ≤ ∫⁻ ξ in Iic ζ₂, ENNReal.ofReal (E ξ) := lintegral_mono_set hIoosub
      _ ≤ dirichletEnergy u U := htail
  -- pull `.toReal` through the `ofReal` bound (both sides nonnegative)
  have hEint_nonneg : 0 ≤ ∫ ξ in Ioo ζ₁ ζ₂, E ξ :=
    setIntegral_nonneg measurableSet_Ioo (fun ξ _ => hEnn ξ)
  have := ENNReal.toReal_mono hDfin hofReal
  rwa [ENNReal.toReal_ofReal hEint_nonneg] at this

/-- **The windowed increment inequality from the truncated-flux increment bound.** For `u` harmonic
and strictly positive on the open set `U`, uniformly bounded by `1` on `U`, continuous on
`closure U`, vanishing on the part of `frontier U` inside the unit disc, with the slice squared
gradient integrable on every superlevel slice and finite total Dirichlet energy, the rough-flux
increment is bounded by `D(u; U)` on every window `ζ₁ ≤ ζ₂ < 0`.  The truncated-flux increment is
bounded by `D(u; U)` on each window (`truncRoughFlux_sub_le_dirichletEnergy`), and the
truncated-flux recovery of the rough flux (`roughFlux_sub_le_of_truncRoughFlux_sub_le`) passes to
`δ → 0`.  This is
the windowed increment inequality `hwin` consumed by `slope_le_energy_ringPotential'`, discharged
without the level-set δ-increment residual `hδwin`. -/
theorem roughFlux_sub_le_dirichletEnergy_trunc {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤) :
    ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
  intro ζ₁ ζ₂ h12 hζ₂
  -- the uniform `|u| ≤ 1` slice bound
  have hbdd : ∀ ξ : ℝ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
    intro ξ θ hθ
    obtain ⟨hnn, hle⟩ := hrangeU _ hθ.2
    rw [abs_of_nonneg hnn]; exact hle
  -- slice radial-derivative integrand integrable at each of the two log-radii
  have hRe : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ) :=
    fun ξ => integrableOn_slice_re_of_normSq hU hu ξ (hEInt ξ)
  -- the superlevel-slice squared gradient integrability (restrict the full-slice one)
  have hEIntδ : ∀ δ : ℝ, ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSliceδ U u δ ξ) :=
    fun δ ξ => (hEInt ξ).mono_set (angularSliceδ_subset_angularSlice δ ξ)
  refine roughFlux_sub_le_of_truncRoughFlux_sub_le hU hu hpos (by norm_num : (0:ℝ) ≤ 1)
    (hbdd ζ₁) (hbdd ζ₂) (hRe ζ₁) (hRe ζ₂) (fun δ hδ => ?_)
  exact truncRoughFlux_sub_le_dirichletEnergy hU hu hnc hcontR hucont hE0 (hEIntδ δ) hDfin hδ h12
    hζ₂

/-- **Keystone slope bound for a ring potential (windowed increment discharged via the truncated
flux).** The `slope_le_energy_ringPotential'` slope bound `b ≤ D(u; U)` with the windowed increment
hypothesis `hwin` eliminated entirely: it is produced from the truncated-flux increment inequality
`roughFlux_sub_le_dirichletEnergy_trunc` (the fixed-window flux–energy FTC of the truncated
integrand, passed to `δ → 0`).  The remaining hypotheses are the ring-potential data together with
`u > 0` on `U`, continuity on `closure U`, and vanishing on the inner frontier. -/
theorem slope_le_energy_ringPotential''' {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤) :
    b ≤ (dirichletEnergy u U).toReal :=
  slope_le_energy_ringPotential' h0 h1 hU hu hcollar hucollar hcont hone hrange hslope hrangeU hDfin
    (roughFlux_sub_le_dirichletEnergy_trunc hU hu hpos hnc hcontR hrangeU hucont hE0 hEInt hDfin)

end RiemannDynamics
