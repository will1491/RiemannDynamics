/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.FluxEnergy.SlitFlux

/-!
# Sequential integration-by-parts bricks and the rough-ring flux

This is the base file of the `SequentialIBP` group.  It gathers the square-integrability and
Cauchy-Schwarz estimates that force a boundary term `f · f'` to vanish along a sequence approaching
an endpoint, the integration by parts on an open interval that those estimates unlock when `f`
vanishes at both endpoints, the countable open-interval decomposition of a bounded open subset of
`ℝ` that lifts the one-interval identity to a whole angular slice, and a Fubini selector turning
finiteness of the log-polar energy over a box into a.e. slice integrability.  It also introduces
the objects the rest of the group is written in: the rough-ring flux `roughFlux`, the angular slice
`angularSlice U ξ`, and the slice energy `sliceEnergyU`.  `FluxFTC` imports this file,
`TruncatedFlux` imports `FluxFTC`, `LevelSetNullity` imports `TruncatedFlux`, and all three are
stated in terms of these three definitions.

## Main definitions

* `RiemannDynamics.roughFlux` — the **rough-ring flux** `roughFlux u U ξ`: the angle integral over
  `(-π, π)` of the potential against its scale-invariant radial derivative
  `u (e^{ξ+iθ}) * fderiv ℝ u (e^{ξ+iθ}) (e^{ξ+iθ})`, cut off by the indicator of
  `{θ | e^{ξ+iθ} ∈ U}`.  No hypotheses on `u` or `U` enter the definition.
* `RiemannDynamics.angularSlice` — the **angular slice** `{θ | θ ∈ Ioo (-π) π ∧ e^{ξ+iθ} ∈ U}`.
  The cutoff `θ ∈ (-π, π)` is part of the definition; for a general `U` the slice is an arbitrary
  subset of `(-π, π)`, not an arc.
* `RiemannDynamics.sliceEnergyU` — the **single-slice energy**
  `∫ θ in angularSlice U ξ, normSq (expGrad u (ξ + θ·I))`, the angular integral of the log-polar
  energy density over the slice at log-radius `ξ`.

## Main results

* `RiemannDynamics.integral_mul_deriv_eq_integral_sq_of_endpoints_zero` — **sequential integration
  by parts.**  For `a < b`, `f` continuous on `[a, b]` and differentiable on `(a, b)` with
  `deriv f = -g` there and `(deriv f)²` integrable on `(a, b)`, `g` differentiable on `(a, b)` with
  derivative `g'`, both `g` and `g'` integrable there, and `f a = f b = 0`, one has
  `∫_a^b f · g' = ∫_a^b g²`.  Vanishing at *both* endpoints is what annihilates the boundary term.
* `RiemannDynamics.expGrad_differentiableAt_open` — for `U` open and `u` harmonic on a
  neighbourhood of every point of `U`, the log-polar gradient `expGrad u` is complex-differentiable
  at every `w` with `Complex.exp w ∈ U`.  Openness turns `e^w ∈ U` into a neighbourhood of `e^w`.
* `RiemannDynamics.isOpen_eq_iUnion_Ioo` — an open set `O` contained in `Ioo c d` is the union of a
  countable pairwise-disjoint family of intervals `Ioo p.1 p.2` whose endpoints all lie outside `O`
  and inside `[c, d]`.  The containment `O ⊆ Ioo c d` is load-bearing: it is what bounds the
  components and hence their endpoints.
* `RiemannDynamics.measurable_normSq_expGrad_logPolar` — for an arbitrary `u : ℂ → ℝ`, with no
  regularity assumed, the log-polar energy density `(ξ, θ) ↦ normSq (expGrad u (ξ + θ·I))` is
  jointly measurable on `ℝ × ℝ`.
* `RiemannDynamics.isOpen_angularSlice` — for `U` open, `angularSlice U ξ` is open, being the
  intersection of `(-π, π)` with the preimage of `U` under the continuous `θ ↦ e^{ξ+iθ}`.  This is
  the source of the measurability of the slice used throughout the group.
* `RiemannDynamics.roughFlux_eq_setIntegral_slice` — for `U` open, `roughFlux u U ξ` equals the set
  integral over `angularSlice U ξ` of `u (e^{ξ+iθ}) * Re (expGrad u (ξ + θ·I))`, the Fréchet
  derivative factor having been rewritten as the real part of the log-polar gradient.  Openness of
  `U` supplies measurability of the indicator set.
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
      intervalIntegrable_const
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
      change ‖ε * (b - s)⁻¹‖ ≤ (deriv f s) ^ 2
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
    simp only [Pi.sub_apply, id_eq, mem_Icc] at hs ⊢
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
    simp only [hfg t ht]; ring
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
    simpa [hgdef, hg'def, Function.comp, Complex.mul_im] using! hcomp
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
    hf2.congr_fun (fun θ hθ => by simp only [hfg θ hθ]; simp [hgdef]) measurableSet_Ioo
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
      ext θ; simp only [hO, mem_ofPred_eq, mem_inter_iff, mem_preimage]
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
    ext θ; simp only [angularSlice, mem_ofPred_eq, mem_inter_iff, mem_preimage]
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
      simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq] at hθ
      tauto

end RiemannDynamics
