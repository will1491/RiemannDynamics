/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.AbsolutelyContinuousLines
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Arc length equals total variation for absolutely continuous curves

For an absolutely continuous curve `γ : ℝ → ℂ` on `[a, b]`, the total variation `eVariationOn γ`
equals the integral of the speed `∫⁻ ‖deriv γ‖`. The deep direction `∫⁻ ‖deriv γ‖ ≤ eVariationOn γ`
(equivalently, the running-variation function differentiates almost everywhere to the speed
`‖deriv γ‖`) is the conformal/arc-length input absent from Mathlib; the reverse direction
`eVariationOn γ ≤ ∫⁻ ‖deriv γ‖` is the elementary "chord ≤ subarc" estimate.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- **Arc length equals total variation for an absolutely continuous curve.** For
`γ : ℝ → ℂ` absolutely continuous on `[a, b]`, the total variation equals the integral of the
speed:

`eVariationOn γ (Set.Icc a b) = ∫⁻ t in Set.Icc a b, ‖deriv γ t‖₊`.

The reverse inequality `eVariationOn ≤ ∫⁻ ‖deriv γ‖` is the chord-≤-subarc estimate
`dist (γ x) (γ y) = ‖∫ₓʸ deriv γ‖ ≤ ∫ₓʸ ‖deriv γ‖` summed over a partition. The forward inequality
`∫⁻ ‖deriv γ‖ ≤ eVariationOn` follows from the running-variation function `s ↦ variationOnFromTo γ`
having derivative `‖deriv γ‖` almost everywhere (squeeze between `‖γ(t+h) - γ t‖ / h` and the
Lebesgue-differentiation limit of `∫ ‖deriv γ‖`), integrated against the monotone fundamental
theorem of calculus. -/
theorem eVariationOn_eq_lintegral_norm_deriv {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    eVariationOn γ (Set.Icc a b) = ∫⁻ t in Set.Icc a b, (‖deriv γ t‖₊ : ℝ≥0∞) := by
  classical
  -- `uIcc a b = Icc a b` under `a ≤ b`.
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  -- **Lipschitz ∘ AC is AC** (real/imaginary parts stay AC).
  have hLipComp : ∀ {F : ℝ → ℂ} {Y : Type} [PseudoMetricSpace Y] (l : ℂ → Y) (K : NNReal),
      LipschitzWith K l → ∀ {x y : ℝ}, AbsolutelyContinuousOnInterval F x y →
      AbsolutelyContinuousOnInterval (fun t => l (F t)) x y := by
    intro F Y _ l K hl x y hF
    rw [absolutelyContinuousOnInterval_iff] at hF ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hF (ε / (K + 1)) (by positivity)
    refine ⟨δ, hδ, fun E hE hlen => ?_⟩
    have key := hδ' E hE hlen
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    calc ∑ i ∈ Finset.range E.1, dist (l (F (E.2 i).1)) (l (F (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (F (E.2 i).1) (F (E.2 i).2) :=
          Finset.sum_le_sum (fun i _ => hl.dist_le_mul _ _)
      _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
          rw [Finset.mul_sum]
      _ ≤ (K : ℝ) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left key.le hKnn
      _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [hε.le, hKnn]
  -- **AC on every subinterval of `[a, b]`.**
  have hγsub : ∀ x y : ℝ, Set.uIcc x y ⊆ Set.Icc a b → AbsolutelyContinuousOnInterval γ x y :=
    fun x y hxy => hγ.mono (by rw [huIcc]; exact hxy)
  -- **(ℂ-valued FTC on a subinterval.)** `γ y - γ x = ∫ t in x..y, deriv γ t`.
  have ftc : ∀ x y : ℝ, Set.uIcc x y ⊆ Set.Icc a b →
      γ y - γ x = ∫ t in x..y, deriv γ t := by
    intro x y hxy
    have hxyAC : AbsolutelyContinuousOnInterval γ x y := hγsub x y hxy
    -- a.e. differentiability of `γ` on `uIcc x y`.
    have hγ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc x y → DifferentiableAt ℝ γ t :=
      hxyAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hderiv : ∀ᵐ t : ℝ ∂(volume.restrict (Set.uIoc x y)), HasDerivAt γ (deriv γ t) t := by
      rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hγ_diff] with t ht ht'
      exact (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
    -- interval-integrability of `deriv γ` (componentwise).
    have hre_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).re) x y :=
      hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz hxyAC
    have him_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).im) x y :=
      hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz hxyAC
    have hre_int : IntervalIntegrable (deriv (fun t => (γ t).re)) volume x y :=
      hre_ac.intervalIntegrable_deriv
    have him_int : IntervalIntegrable (deriv (fun t => (γ t).im)) volume x y :=
      him_ac.intervalIntegrable_deriv
    have hre_eq : (deriv (fun t => (γ t).re)) =ᵐ[volume.restrict (Set.uIoc x y)]
        (fun t => (deriv γ t).re) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hγ_diff] with t ht ht'
      have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
      simpa using this.deriv
    have him_eq : (deriv (fun t => (γ t).im)) =ᵐ[volume.restrict (Set.uIoc x y)]
        (fun t => (deriv γ t).im) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hγ_diff] with t ht ht'
      have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
      simpa using this.deriv
    have hre_int' : IntervalIntegrable (fun t => (deriv γ t).re) volume x y := by
      rw [intervalIntegrable_iff]; exact (hre_int.def'.congr hre_eq)
    have him_int' : IntervalIntegrable (fun t => (deriv γ t).im) volume x y := by
      rw [intervalIntegrable_iff]; exact (him_int.def'.congr him_eq)
    have hre_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).re : ℂ)) volume x y :=
      ⟨Complex.ofRealCLM.integrable_comp hre_int'.1,
        Complex.ofRealCLM.integrable_comp hre_int'.2⟩
    have him_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).im : ℂ)) volume x y :=
      ⟨Complex.ofRealCLM.integrable_comp him_int'.1,
        Complex.ofRealCLM.integrable_comp him_int'.2⟩
    have hint : IntervalIntegrable (deriv γ) volume x y := by
      have hrecomb : deriv γ =
          fun t => (↑(deriv γ t).re : ℂ) + (↑(deriv γ t).im : ℂ) * Complex.I := by
        funext t; exact (Complex.re_add_im (deriv γ t)).symm
      rw [hrecomb]; exact hre_intℂ.add (him_intℂ.mul_const Complex.I)
    -- componentwise real FTC.
    have hre_deriv : ∀ᵐ t : ℝ ∂(volume.restrict (Set.uIoc x y)),
        HasDerivAt (fun s => (γ s).re) (deriv γ t).re t := by
      filter_upwards [hderiv] with t ht
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht; simpa using this
    have him_deriv : ∀ᵐ t : ℝ ∂(volume.restrict (Set.uIoc x y)),
        HasDerivAt (fun s => (γ s).im) (deriv γ t).im t := by
      filter_upwards [hderiv] with t ht
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ht; simpa using this
    have hre_deriv_eq : ∀ᵐ t : ℝ ∂(volume.restrict (Set.uIoc x y)),
        deriv (fun s => (γ s).re) t = (deriv γ t).re := by
      filter_upwards [hre_deriv] with t ht using ht.deriv
    have him_deriv_eq : ∀ᵐ t : ℝ ∂(volume.restrict (Set.uIoc x y)),
        deriv (fun s => (γ s).im) t = (deriv γ t).im := by
      filter_upwards [him_deriv] with t ht using ht.deriv
    have hre_ftc : ∫ t in x..y, deriv (fun s => (γ s).re) t = (γ y).re - (γ x).re :=
      hre_ac.integral_deriv_eq_sub
    have him_ftc : ∫ t in x..y, deriv (fun s => (γ s).im) t = (γ y).im - (γ x).im :=
      him_ac.integral_deriv_eq_sub
    have hre_congr : (∫ t in x..y, deriv (fun s => (γ s).re) t) = ∫ t in x..y, (deriv γ t).re :=
      intervalIntegral.integral_congr_ae (by
        filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp hre_deriv_eq]
          with t ht hmem using ht hmem)
    have him_congr : (∫ t in x..y, deriv (fun s => (γ s).im) t) = ∫ t in x..y, (deriv γ t).im :=
      intervalIntegral.integral_congr_ae (by
        filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp him_deriv_eq]
          with t ht hmem using ht hmem)
    have hre_int_eq : ∫ t in x..y, (deriv γ t).re = (γ y).re - (γ x).re := by
      rw [← hre_congr, hre_ftc]
    have him_int_eq : ∫ t in x..y, (deriv γ t).im = (γ y).im - (γ x).im := by
      rw [← him_congr, him_ftc]
    have hintre : (∫ t in x..y, deriv γ t).re = ∫ t in x..y, (deriv γ t).re := by
      have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
      simpa using this.symm
    have hintim : (∫ t in x..y, deriv γ t).im = ∫ t in x..y, (deriv γ t).im := by
      have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.imCLM hint
      simpa using this.symm
    apply Complex.ext
    · rw [Complex.sub_re, hintre, hre_int_eq]
    · rw [Complex.sub_im, hintim, him_int_eq]
  -- **(Chord ≤ subarc.)** For `x ≤ y` inside `[a, b]`, the chord length is bounded by the
  -- integral of the speed on `Ioc x y`.
  have chord : ∀ x y : ℝ, Set.uIcc x y ⊆ Set.Icc a b → x ≤ y →
      edist (γ x) (γ y) ≤ ∫⁻ t in Set.Ioc x y, (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro x y hxy hxyle
    have hint : IntervalIntegrable (deriv γ) volume x y := by
      -- reuse the integrability established inside `ftc`.
      have hxyAC : AbsolutelyContinuousOnInterval γ x y := hγsub x y hxy
      have hγ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc x y → DifferentiableAt ℝ γ t :=
        hxyAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
      have hre_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).re) x y :=
        hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz hxyAC
      have him_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).im) x y :=
        hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz hxyAC
      have hre_int : IntervalIntegrable (deriv (fun t => (γ t).re)) volume x y :=
        hre_ac.intervalIntegrable_deriv
      have him_int : IntervalIntegrable (deriv (fun t => (γ t).im)) volume x y :=
        him_ac.intervalIntegrable_deriv
      have hre_eq : (deriv (fun t => (γ t).re)) =ᵐ[volume.restrict (Set.uIoc x y)]
          (fun t => (deriv γ t).re) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hγ_diff] with t ht ht'
        have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
        have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
        simpa using this.deriv
      have him_eq : (deriv (fun t => (γ t).im)) =ᵐ[volume.restrict (Set.uIoc x y)]
          (fun t => (deriv γ t).im) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hγ_diff] with t ht ht'
        have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
        have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
        simpa using this.deriv
      have hre_int' : IntervalIntegrable (fun t => (deriv γ t).re) volume x y := by
        rw [intervalIntegrable_iff]; exact (hre_int.def'.congr hre_eq)
      have him_int' : IntervalIntegrable (fun t => (deriv γ t).im) volume x y := by
        rw [intervalIntegrable_iff]; exact (him_int.def'.congr him_eq)
      have hre_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).re : ℂ)) volume x y :=
        ⟨Complex.ofRealCLM.integrable_comp hre_int'.1,
          Complex.ofRealCLM.integrable_comp hre_int'.2⟩
      have him_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).im : ℂ)) volume x y :=
        ⟨Complex.ofRealCLM.integrable_comp him_int'.1,
          Complex.ofRealCLM.integrable_comp him_int'.2⟩
      have hrecomb : deriv γ =
          fun t => (↑(deriv γ t).re : ℂ) + (↑(deriv γ t).im : ℂ) * Complex.I := by
        funext t; exact (Complex.re_add_im (deriv γ t)).symm
      rw [hrecomb]; exact hre_intℂ.add (him_intℂ.mul_const Complex.I)
    have hftc : γ y - γ x = ∫ t in x..y, deriv γ t := ftc x y hxy
    have hset : (∫ t in x..y, deriv γ t) = ∫ t, deriv γ t ∂(volume.restrict (Set.Ioc x y)) := by
      rw [intervalIntegral.integral_of_le hxyle]
    have hbound : ‖∫ t, deriv γ t ∂(volume.restrict (Set.Ioc x y))‖ₑ ≤
        ∫⁻ t, ‖deriv γ t‖ₑ ∂(volume.restrict (Set.Ioc x y)) :=
      enorm_integral_le_lintegral_enorm _
    calc edist (γ x) (γ y) = ‖γ y - γ x‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]
      _ = ‖∫ t, deriv γ t ∂(volume.restrict (Set.Ioc x y))‖ₑ := by rw [hftc, hset]
      _ ≤ ∫⁻ t, ‖deriv γ t‖ₑ ∂(volume.restrict (Set.Ioc x y)) := hbound
      _ = ∫⁻ t in Set.Ioc x y, (‖deriv γ t‖₊ : ℝ≥0∞) := by
          simp only [enorm_eq_nnnorm]
  -- **Reverse inequality on a subinterval: `eVariationOn γ (Icc x y) ≤ ∫⁻ Icc x y, ‖deriv γ‖`.**
  have revSub : ∀ x y : ℝ, Set.Icc x y ⊆ Set.Icc a b →
      eVariationOn γ (Set.Icc x y) ≤ ∫⁻ t in Set.Icc x y, (‖deriv γ t‖₊ : ℝ≥0∞) := by
    intro x y hxysub
    rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, ⟨u, humono, umem⟩⟩
    -- Per-edge: `edist (γ (u (i+1))) (γ (u i)) ≤ ∫⁻ Ioc (u i) (u (i+1))`.
    have hedge : ∀ i, edist (γ (u (i + 1))) (γ (u i)) ≤
        ∫⁻ t in Set.Ioc (u i) (u (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞) := by
      intro i
      have hle : u i ≤ u (i + 1) := humono (Nat.le_succ i)
      have hsub : Set.uIcc (u i) (u (i + 1)) ⊆ Set.Icc a b := by
        rw [Set.uIcc_of_le hle]
        intro z hz
        exact hxysub ⟨le_trans (umem i).1 hz.1, le_trans hz.2 (umem (i + 1)).2⟩
      rw [edist_comm]
      exact chord (u i) (u (i + 1)) hsub hle
    -- Sum of edge bounds is a sum of lintegrals over disjoint `Ioc`s.
    have hsumbound : ∑ i ∈ Finset.range n,
        (∫⁻ t in Set.Ioc (u i) (u (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞)) =
        ∫⁻ t in ⋃ i ∈ Finset.range n, Set.Ioc (u i) (u (i + 1)),
          (‖deriv γ t‖₊ : ℝ≥0∞) := by
      rw [lintegral_biUnion_finset]
      · exact (humono.pairwise_disjoint_on_Ioc_succ).set_pairwise _
      · exact fun i _ => measurableSet_Ioc
    have hunion_sub : (⋃ i ∈ Finset.range n, Set.Ioc (u i) (u (i + 1))) ⊆ Set.Icc x y := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, _, hi⟩ := hz
      exact ⟨le_trans (umem i).1 (le_of_lt hi.1), le_trans hi.2 (umem (i + 1)).2⟩
    calc ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))
        ≤ ∑ i ∈ Finset.range n,
            (∫⁻ t in Set.Ioc (u i) (u (i + 1)), (‖deriv γ t‖₊ : ℝ≥0∞)) :=
          Finset.sum_le_sum (fun i _ => hedge i)
      _ = ∫⁻ t in ⋃ i ∈ Finset.range n, Set.Ioc (u i) (u (i + 1)),
            (‖deriv γ t‖₊ : ℝ≥0∞) := hsumbound
      _ ≤ ∫⁻ t in Set.Icc x y, (‖deriv γ t‖₊ : ℝ≥0∞) := lintegral_mono_set hunion_sub
  have hreverse : eVariationOn γ (Set.Icc a b) ≤ ∫⁻ t in Set.Icc a b, (‖deriv γ t‖₊ : ℝ≥0∞) :=
    revSub a b (subset_refl _)
  -- **Forward inequality: `∫⁻ ‖deriv γ‖ ≤ eVariationOn γ (Icc a b)`.**
  -- Bounded variation and running-variation set-up.
  have hbv : BoundedVariationOn γ (Set.Icc a b) := by
    have := hγ.boundedVariationOn; rwa [huIcc] at this
  have hlbv : LocallyBoundedVariationOn γ (Set.Icc a b) := hbv.locallyBoundedVariationOn
  set s : Set ℝ := Set.Icc a b with hs
  have hains : a ∈ s := ⟨le_refl a, hab⟩
  have hbins : b ∈ s := ⟨hab, le_refl b⟩
  set V : ℝ → ℝ := fun r => variationOnFromTo γ s a r with hV
  -- `deriv γ` is interval integrable on `a..b`, hence so is its norm.
  have hint_ab : IntervalIntegrable (deriv γ) volume a b := by
    have hxy : Set.uIcc a b ⊆ Set.Icc a b := by rw [huIcc]
    -- reconstruct from `ftc`'s integrability proof (componentwise).
    have hxyAC : AbsolutelyContinuousOnInterval γ a b := hγsub a b hxy
    have hγ_diff : ∀ᵐ t : ℝ, t ∈ Set.uIcc a b → DifferentiableAt ℝ γ t :=
      hxyAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    have hre_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).re) a b :=
      hLipComp Complex.reCLM ‖Complex.reCLM‖₊ Complex.reCLM.lipschitz hxyAC
    have him_ac : AbsolutelyContinuousOnInterval (fun t => (γ t).im) a b :=
      hLipComp Complex.imCLM ‖Complex.imCLM‖₊ Complex.imCLM.lipschitz hxyAC
    have hre_int : IntervalIntegrable (deriv (fun t => (γ t).re)) volume a b :=
      hre_ac.intervalIntegrable_deriv
    have him_int : IntervalIntegrable (deriv (fun t => (γ t).im)) volume a b :=
      him_ac.intervalIntegrable_deriv
    have hre_eq : (deriv (fun t => (γ t).re)) =ᵐ[volume.restrict (Set.uIoc a b)]
        (fun t => (deriv γ t).re) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hγ_diff] with t ht ht'
      have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
      simpa using this.deriv
    have him_eq : (deriv (fun t => (γ t).im)) =ᵐ[volume.restrict (Set.uIoc a b)]
        (fun t => (deriv γ t).im) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hγ_diff] with t ht ht'
      have hd : HasDerivAt γ (deriv γ t) t := (ht (Set.uIoc_subset_uIcc ht')).hasDerivAt
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
      simpa using this.deriv
    have hre_int' : IntervalIntegrable (fun t => (deriv γ t).re) volume a b := by
      rw [intervalIntegrable_iff]; exact (hre_int.def'.congr hre_eq)
    have him_int' : IntervalIntegrable (fun t => (deriv γ t).im) volume a b := by
      rw [intervalIntegrable_iff]; exact (him_int.def'.congr him_eq)
    have hre_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).re : ℂ)) volume a b :=
      ⟨Complex.ofRealCLM.integrable_comp hre_int'.1, Complex.ofRealCLM.integrable_comp hre_int'.2⟩
    have him_intℂ : IntervalIntegrable (fun t => (↑(deriv γ t).im : ℂ)) volume a b :=
      ⟨Complex.ofRealCLM.integrable_comp him_int'.1, Complex.ofRealCLM.integrable_comp him_int'.2⟩
    have hrecomb : deriv γ =
        fun t => (↑(deriv γ t).re : ℂ) + (↑(deriv γ t).im : ℂ) * Complex.I := by
      funext t; exact (Complex.re_add_im (deriv γ t)).symm
    rw [hrecomb]; exact hre_intℂ.add (him_intℂ.mul_const Complex.I)
  have hnorm_ii : IntervalIntegrable (fun τ => ‖deriv γ τ‖) volume a b := hint_ab.norm
  set W : ℝ → ℝ := fun r => ∫ τ in a..r, ‖deriv γ τ‖ with hW
  -- `V r - V t = variationOnFromTo γ s t r` for `t, r ∈ s` (additivity).
  have hVincr : ∀ t r : ℝ, t ∈ s → r ∈ s → V r - V t = variationOnFromTo γ s t r := by
    intro t r hts hrs
    have := variationOnFromTo.add hlbv hains hts hrs
    simp only [hV]; linarith [this]
  -- `V` is monotone on `s`.
  have hVmono : MonotoneOn V s := variationOnFromTo.monotoneOn hlbv hains
  -- Subinterval interval-integrability of `deriv γ` and of `‖deriv γ‖`.
  have hdsub : ∀ x y : ℝ, x ∈ s → y ∈ s →
      IntervalIntegrable (deriv γ) volume x y := by
    intro x y hxs hys
    refine hint_ab.mono_set ?_
    rw [huIcc]
    exact (Set.uIcc_subset_uIcc (huIcc ▸ hxs) (huIcc ▸ hys)).trans_eq huIcc
  have hnsub : ∀ x y : ℝ, x ∈ s → y ∈ s →
      IntervalIntegrable (fun τ => ‖deriv γ τ‖) volume x y :=
    fun x y hxs hys => (hdsub x y hxs hys).norm
  -- `W r - W t = ∫ τ in t..r, ‖deriv γ‖` for `t, r ∈ s`.
  have hWincr : ∀ t r : ℝ, t ∈ s → r ∈ s → W r - W t = ∫ τ in t..r, ‖deriv γ τ‖ := by
    intro t r hts hrs
    have hat : IntervalIntegrable (fun τ => ‖deriv γ τ‖) volume a t := hnsub a t hains hts
    have htr : IntervalIntegrable (fun τ => ‖deriv γ τ‖) volume t r := hnsub t r hts hrs
    have := intervalIntegral.integral_add_adjacent_intervals hat htr
    simp only [hW]; linarith [this]
  -- **Chord bound on `V`:** `‖γ r - γ t‖ ≤ V r - V t` for `t ≤ r` in `s`.
  have hchordV : ∀ t r : ℝ, t ∈ s → r ∈ s → t ≤ r → ‖γ r - γ t‖ ≤ V r - V t := by
    intro t r hts hrs htr
    rw [hVincr t r hts hrs, variationOnFromTo.eq_of_le γ s htr, ← Complex.dist_eq, dist_comm]
    rw [dist_edist]
    apply ENNReal.toReal_mono (hlbv t r hts hrs)
    exact eVariationOn.edist_le γ ⟨hts, le_rfl, htr⟩ ⟨hrs, htr, le_rfl⟩
  -- **`W`-increment bound on `V`:** `V r - V t ≤ W r - W t` for `t ≤ r` in `s`.
  have hVWincr : ∀ t r : ℝ, t ∈ s → r ∈ s → t ≤ r → V r - V t ≤ W r - W t := by
    intro t r hts hrs htr
    rw [hVincr t r hts hrs, variationOnFromTo.eq_of_le γ s htr, hWincr t r hts hrs]
    have hsub : Set.Icc t r ⊆ Set.Icc a b := Set.Icc_subset_Icc hts.1 hrs.2
    -- `s ∩ Icc t r = Icc t r`.
    have hcap : s ∩ Set.Icc t r = Set.Icc t r := by rw [hs, Set.inter_eq_right.mpr hsub]
    rw [hcap]
    have hrev : eVariationOn γ (Set.Icc t r) ≤ ∫⁻ τ in Set.Icc t r, (‖deriv γ τ‖₊ : ℝ≥0∞) :=
      revSub t r hsub
    -- `∫ τ in t..r, ‖deriv γ‖ = (∫⁻ Ioc t r ‖deriv γ‖ₑ).toReal = (∫⁻ Icc t r ‖deriv γ‖₊).toReal`.
    have hdint : IntegrableOn (deriv γ) (Set.Ioc t r) volume := by
      have := (hdsub t r hts hrs).def'; rwa [Set.uIoc_of_le htr] at this
    -- `∫⁻ Icc t r = ∫⁻ Ioc t r` (endpoint has measure zero).
    have hIccIoc : (∫⁻ τ in Set.Icc t r, (‖deriv γ τ‖₊ : ℝ≥0∞)) =
        ∫⁻ τ in Set.Ioc t r, (‖deriv γ τ‖₊ : ℝ≥0∞) :=
      setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
    have henorm : ∀ τ, ‖deriv γ τ‖ₑ = (‖deriv γ τ‖₊ : ℝ≥0∞) := fun _ => rfl
    have hconv : ∫ τ in t..r, ‖deriv γ τ‖ =
        (∫⁻ τ in Set.Icc t r, (‖deriv γ τ‖₊ : ℝ≥0∞)).toReal := by
      rw [hIccIoc, intervalIntegral.integral_of_le htr,
        integral_norm_eq_lintegral_enorm hdint.aestronglyMeasurable]
      simp_rw [henorm]
    have hfin : (∫⁻ τ in Set.Icc t r, (‖deriv γ τ‖₊ : ℝ≥0∞)) ≠ ⊤ := by
      rw [hIccIoc]
      have hlt : ∫⁻ τ in Set.Ioc t r, ‖deriv γ τ‖ₑ < ⊤ :=
        hasFiniteIntegral_iff_enorm.mp hdint.2
      simp_rw [henorm] at hlt
      exact hlt.ne
    rw [hconv]
    exact ENNReal.toReal_mono hfin hrev
  -- **The squeeze (pointwise): at a point `t ∈ (a, b)` where `W` differentiates to `‖deriv γ t‖`
  -- and `γ` is differentiable, `V` differentiates to `‖deriv γ t‖`.**
  have hVderiv_pt : ∀ t : ℝ, t ∈ Set.Ioo a b → HasDerivAt W (‖deriv γ t‖) t →
      HasDerivAt γ (deriv γ t) t → HasDerivAt V (‖deriv γ t‖) t := by
    intro t htIoo hWt hγt
    have htmem : t ∈ s := ⟨htIoo.1.le, htIoo.2.le⟩
    rw [hasDerivAt_iff_tendsto_slope]
    -- lower function: `‖slope γ t‖`; upper function: `slope W t`.
    have hlow : Filter.Tendsto (fun u => ‖slope γ t u‖) (nhdsWithin t {t}ᶜ)
        (nhds (‖deriv γ t‖)) :=
      (hasDerivAt_iff_tendsto_slope.mp hγt).norm
    have hupp : Filter.Tendsto (slope W t) (nhdsWithin t {t}ᶜ) (nhds (‖deriv γ t‖)) :=
      hasDerivAt_iff_tendsto_slope.mp hWt
    -- eventually `u ∈ Icc a b` and `u ≠ t`.
    have hev : ∀ᶠ u in nhdsWithin t {t}ᶜ, u ∈ s ∧ u ≠ t := by
      have h1 : ∀ᶠ u in nhdsWithin t {t}ᶜ, u ∈ Set.Ioo a b :=
        Filter.eventually_inf_principal.mpr
          (Filter.eventually_of_mem (Ioo_mem_nhds htIoo.1 htIoo.2) (fun u hu _ => hu))
      have h2 : ∀ᶠ u in nhdsWithin t {t}ᶜ, u ≠ t :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun u hu => hu)
      filter_upwards [h1, h2] with u hu hut
      exact ⟨⟨hu.1.le, hu.2.le⟩, hut⟩
    -- slope bounds for `u ∈ s, u ≠ t`.
    have hbnd : ∀ u : ℝ, u ∈ s → u ≠ t →
        ‖slope γ t u‖ ≤ slope V t u ∧ slope V t u ≤ slope W t u := by
      intro u hus hut
      have hns : ‖slope γ t u‖ = ‖γ u - γ t‖ / |u - t| := by
        rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs, div_eq_inv_mul]
      have hsV : slope V t u = (V u - V t) / (u - t) := slope_def_field V t u
      have hsW : slope W t u = (W u - W t) / (u - t) := slope_def_field W t u
      rcases lt_or_gt_of_ne hut with hlt | hgt
      · -- `u < t`: rewrite each ratio with the positive denominator `t - u`.
        have htu0 : (0 : ℝ) < t - u := by linarith
        have habs : |u - t| = t - u := by rw [abs_sub_comm, abs_of_pos htu0]
        have hchord : ‖γ t - γ u‖ ≤ V t - V u := hchordV u t hus htmem hlt.le
        have hVW : V t - V u ≤ W t - W u := hVWincr u t hus htmem hlt.le
        have hrV : (V u - V t) / (u - t) = (V t - V u) / (t - u) := by
          rw [← neg_sub t u, ← neg_sub (V t) (V u), neg_div_neg_eq]
        have hrW : (W u - W t) / (u - t) = (W t - W u) / (t - u) := by
          rw [← neg_sub t u, ← neg_sub (W t) (W u), neg_div_neg_eq]
        constructor
        · rw [hns, hsV, habs, norm_sub_rev, hrV]
          exact (div_le_div_iff_of_pos_right htu0).mpr hchord
        · rw [hsV, hsW, hrV, hrW]
          exact (div_le_div_iff_of_pos_right htu0).mpr hVW
      · -- `t < u`: denominator `u - t` is positive.
        have hut0 : (0 : ℝ) < u - t := by linarith
        have habs : |u - t| = u - t := abs_of_pos hut0
        have hchord : ‖γ u - γ t‖ ≤ V u - V t := hchordV t u htmem hus hgt.le
        have hVW : V u - V t ≤ W u - W t := hVWincr t u htmem hus hgt.le
        constructor
        · rw [hns, hsV, habs]
          exact (div_le_div_iff_of_pos_right hut0).mpr hchord
        · rw [hsV, hsW]
          exact (div_le_div_iff_of_pos_right hut0).mpr hVW
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
    · filter_upwards [hev] with u hu using (hbnd u hu.1 hu.2).1
    · filter_upwards [hev] with u hu using (hbnd u hu.1 hu.2).2
  -- **a.e. on the interval, `deriv V = ‖deriv γ‖`.**
  have hWderiv : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → ∀ c ∈ Set.uIcc a b,
      HasDerivAt (fun y => ∫ τ in c..y, ‖deriv γ τ‖) (‖deriv γ x‖) x :=
    hnorm_ii.ae_hasDerivAt_integral
  have hγderiv : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → DifferentiableAt ℝ γ x :=
    (huIcc ▸ hbv : BoundedVariationOn γ (Set.uIcc a b)).ae_differentiableAt_of_mem_uIcc
  have hIooIcc : ∀ᵐ x : ℝ, x ∈ Set.Icc a b → x ∈ Set.Ioo a b := by
    have h := MeasureTheory.Ioo_ae_eq_Icc (a := a) (b := b) (μ := volume)
    filter_upwards [h.mem_iff] with x hx hxIcc
    exact (hx.mpr hxIcc)
  have hVderiv : ∀ᵐ x : ℝ, x ∈ Set.uIcc a b → deriv V x = ‖deriv γ x‖ := by
    rw [huIcc]
    filter_upwards [hWderiv, hγderiv, hIooIcc] with x hWx hγx hIox hxIcc
    have hxIoo : x ∈ Set.Ioo a b := hIox hxIcc
    have hWx' : HasDerivAt W (‖deriv γ x‖) x := by
      have := hWx (huIcc ▸ hxIcc) a (huIcc ▸ hains); exact this
    have hγx' : HasDerivAt γ (deriv γ x) x := (hγx (huIcc ▸ hxIcc)).hasDerivAt
    exact (hVderiv_pt x hxIoo hWx' hγx').deriv
  -- **Monotone fundamental theorem of calculus for `V`.**
  have hVmono' : MonotoneOn V (Set.uIcc a b) := by rw [huIcc]; exact hVmono
  have hFTC : ∫ x in a..b, deriv V x ∈ Set.uIcc 0 (V b - V a) :=
    hVmono'.intervalIntegral_deriv_mem_uIcc
  -- `V a = 0`, `V b = (eVariationOn γ (Icc a b)).toReal`.
  have hVa : V a = 0 := by simp only [hV]; exact variationOnFromTo.self γ s a
  have hVb : V b = (eVariationOn γ (Set.Icc a b)).toReal := by
    simp only [hV]
    rw [variationOnFromTo.eq_of_le γ s hab, hs, Set.inter_eq_right.mpr (subset_refl _)]
  -- `∫ deriv V = ∫ ‖deriv γ‖` over `a..b`.
  have hinteq : ∫ x in a..b, deriv V x = ∫ x in a..b, ‖deriv γ x‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hVderiv] with x hVx hxIoc
    exact hVx (Set.uIoc_subset_uIcc hxIoc)
  -- Combine: `∫ ‖deriv γ‖ over a..b ≤ V b - V a = (eVariationOn).toReal`.
  have hWb_le : ∫ x in a..b, ‖deriv γ x‖ ≤ (eVariationOn γ (Set.Icc a b)).toReal := by
    rw [← hinteq]
    have hVba_nonneg : (0 : ℝ) ≤ V b - V a := by
      rw [hVa, sub_zero, hV]; exact variationOnFromTo.nonneg_of_le γ s hab
    have := hFTC
    rw [Set.uIcc_of_le hVba_nonneg, Set.mem_Icc] at this
    rw [hVa, sub_zero, hVb] at this
    exact this.2
  -- **Convert to the `ℝ≥0∞` statement.**
  have hfwd : ∫⁻ t in Set.Icc a b, (‖deriv γ t‖₊ : ℝ≥0∞) ≤ eVariationOn γ (Set.Icc a b) := by
    -- `∫⁻ Icc a b ‖deriv γ‖₊ = ENNReal.ofReal (∫ a..b ‖deriv γ‖)`.
    have hdint_ab : IntegrableOn (deriv γ) (Set.Ioc a b) volume := by
      have := hint_ab.def'; rwa [Set.uIoc_of_le hab] at this
    have henorm : ∀ τ, ‖deriv γ τ‖ₑ = (‖deriv γ τ‖₊ : ℝ≥0∞) := fun _ => rfl
    have hIccIoc : (∫⁻ τ in Set.Icc a b, (‖deriv γ τ‖₊ : ℝ≥0∞)) =
        ∫⁻ τ in Set.Ioc a b, (‖deriv γ τ‖₊ : ℝ≥0∞) :=
      setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc (μ := volume)).symm
    have hofReal : (∫⁻ t in Set.Icc a b, (‖deriv γ t‖₊ : ℝ≥0∞)) =
        ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
      rw [hIccIoc, intervalIntegral.integral_of_le hab,
        ofReal_integral_norm_eq_lintegral_enorm hdint_ab]
      exact lintegral_congr fun τ => (henorm τ)
    rw [hofReal]
    have hevar_ne : eVariationOn γ (Set.Icc a b) ≠ ⊤ := hbv
    calc ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖)
        ≤ ENNReal.ofReal ((eVariationOn γ (Set.Icc a b)).toReal) :=
          ENNReal.ofReal_le_ofReal hWb_le
      _ = eVariationOn γ (Set.Icc a b) := ENNReal.ofReal_toReal hevar_ne
  -- **Conclude by antisymmetry.**
  exact le_antisymm hreverse hfwd

end RiemannDynamics
