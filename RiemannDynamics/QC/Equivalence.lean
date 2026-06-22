/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.InverseQC
import RiemannDynamics.QC.LengthArea

/-!
# The analytic ⇔ geometric quasiconformal equivalence (clean endpoints)

This file states the Milestone 9.2 headline theorems in their clean, hypothesis-free form:

* `isQCGeometric_of_isQCAnalytic` — analytic ⇒ geometric;
* `qc_analytic_iff_geometric` — the full equivalence.

The analytic ⇒ geometric direction is necessarily proved **here**, downstream of
`QC/InverseQC.lean`, rather than in `QC/Equivalence.lean`: its image-side modulus argument
needs both the inverse-is-quasiconformal fact `IsQCAnalytic.inverse_isQCAnalytic` and the
planar Lusin-(N) fact `IsQCAnalytic.image_lusinN` (which rests on the higher-integrability
machinery in `Beltrami.lean`, importing `QC/LengthArea.lean`) — both of which sit strictly
below the `Equivalence` file. The original upstream scaffold, which threaded the Lusin-(N)
fact as an explicit hypothesis, has been removed in favour of this self-contained downstream
proof.
-/

open MeasureTheory Complex Set
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- The planar Lusin-(N) fact in the shape required by the downstream
`isQCGeometric_of_isQCAnalytic` proof (the degeneracy set `{¬(diff ∧ 0<det)}`), obtained from
`IsQCAnalytic.image_lusinN` (stated on `{¬diff ∨ ¬0<det}`) by De Morgan. -/
private theorem lusinN_degeneracy {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b) :
    volume (f '' {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}) = 0 := by
  have hset : {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}
      = {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det} := by
    ext z; exact not_and_or
  rw [hset]; exact hf.image_lusinN

/-- **(Pointwise a.e. upper-gradient bound from the interval bound.)** If `h : ℝ → ℂ`
is a curve and `ρ : ℝ → ℝ` is a nonnegative, locally integrable density such that the
distance moved by `h` across every subinterval `[x, y] ⊆ [0,1]` is bounded by the
interval integral `|∫ₓʸ ρ|`, then at almost every `t ∈ (0,1)` the derivative `deriv h t`
satisfies `‖deriv h t‖ ≤ ρ t`.

The proof is the standard Lebesgue-differentiation argument.  Write
`R x := ∫₀ˣ ρ`.  Then `∫ₓʸ ρ = R y - R x`, so the bound reads
`dist (h x) (h y) ≤ |R y − R x|`, i.e. `‖slope h t s‖ ≤ ‖slope R t s‖` for `s` near `t`.
By the Lebesgue differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`),
for a.e. `t` we have `HasDerivAt R (ρ t) t`, so `‖slope R t ·‖ → |ρ t| = ρ t`.  At an
`a.e.` `t`, either `h` is non-differentiable (then `deriv h t = 0 ≤ ρ t` since `ρ ≥ 0`),
or `HasDerivAt h (deriv h t) t`, whence `‖slope h t ·‖ → ‖deriv h t‖`; comparing the two
limits over `𝓝[≠] t` gives `‖deriv h t‖ ≤ ρ t`. -/
private theorem norm_deriv_le_of_dist_le_intervalIntegral {h : ℝ → ℂ} {ρ : ℝ → ℝ}
    (hρnn : ∀ t, 0 ≤ ρ t) (hρint : IntegrableOn ρ (Set.Icc (0 : ℝ) 1) volume)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      dist (h x) (h y) ≤ |∫ u in x..y, ρ u|) :
    ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ‖deriv h t‖ ≤ ρ t := by
  classical
  -- Truncate `ρ` to `[0,1]` so it is globally integrable (hence locally integrable).
  set ρ' : ℝ → ℝ := (Set.Icc (0 : ℝ) 1).indicator ρ with hρ'
  have hρ'nn : ∀ t, 0 ≤ ρ' t := by
    intro t; rw [hρ']; exact Set.indicator_nonneg (fun s _ => hρnn s) t
  have hρ'int : Integrable ρ' volume := by
    rw [hρ', ← integrable_indicator_iff measurableSet_Icc] at *
    exact hρint
  have hρ'loc : LocallyIntegrable ρ' volume := hρ'int.locallyIntegrable
  -- On `[0,1]`, the interval integrals of `ρ'` and `ρ` agree.
  have hII' : ∀ a b : ℝ, IntervalIntegrable ρ' volume a b := fun a b =>
    (hρ'loc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hintcongr : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (∫ u in x..y, ρ' u) = ∫ u in x..y, ρ u := by
    intro x hx y hy
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have hu01 : u ∈ Set.Icc (0 : ℝ) 1 :=
      (Set.uIcc_subset_Icc hx hy) hu
    rw [hρ', Set.indicator_of_mem hu01]
  -- The primitive `R x = ∫₀ˣ ρ'`; its a.e. derivative is `ρ'` by Lebesgue differentiation.
  set R : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, ρ' u with hR
  have hLDT : ∀ᵐ x : ℝ, HasDerivAt R (ρ' x) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hρ'loc] with x hx
    exact hx 0
  -- Work on the open interval; pull the a.e. statement to the restricted measure.
  refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
  filter_upwards [hLDT] with t htR
  intro htIoo
  -- On `Ioo 0 1`, `ρ' t = ρ t`.
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self htIoo
  have hρ'eq : ρ' t = ρ t := by rw [hρ', Set.indicator_of_mem ht01]
  rw [hρ'eq] at htR
  -- `Ioo 0 1` is a neighbourhood of `t`, and the bound transfers to a slope bound there.
  have hIoo_nhds : Set.Ioo (0 : ℝ) 1 ∈ nhds t := isOpen_Ioo.mem_nhds htIoo
  -- On `Ioo 0 1`, the interval integral equals `R · − R ·`, so the distance bound becomes
  -- the slope comparison `‖slope h t s‖ ≤ ‖slope R t s‖`.
  have hslopeBound : ∀ᶠ s in nhdsWithin t ({t}ᶜ),
      ‖slope h t s‖ ≤ ‖slope R t s‖ := by
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin t ({t}ᶜ) := nhdsWithin_le_nhds hIoo_nhds
    filter_upwards [hmem] with s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hs
    -- `R s − R t = ∫ₜˢ ρ'`, and the distance bound gives `dist (h t) (h s) ≤ |∫ₜˢ ρ|`.
    have hRsub : R s - R t = ∫ u in t..s, ρ' u :=
      intervalIntegral.integral_interval_sub_left (hII' 0 s) (hII' 0 t)
    have hdist : ‖h s - h t‖ ≤ ‖R s - R t‖ := by
      rw [Real.norm_eq_abs, hRsub, hintcongr t ht01 s hs01, ← dist_eq_norm, dist_comm]
      exact hbound t ht01 s hs01
    -- Slope norms: `‖slope h t s‖ = ‖s−t‖⁻¹·‖h s − h t‖`, similarly for `R`.
    rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
    gcongr
  -- Compare the two slope limits over `𝓝[≠] t`, splitting on differentiability of `h`.
  by_cases hd : DifferentiableAt ℝ h t
  · have hh : HasDerivAt h (deriv h t) t := hd.hasDerivAt
    have hlimh : Filter.Tendsto (fun s => ‖slope h t s‖) (nhdsWithin t ({t}ᶜ))
        (nhds ‖deriv h t‖) := (hh.tendsto_slope).norm
    have hlimR : Filter.Tendsto (fun s => ‖slope R t s‖) (nhdsWithin t ({t}ᶜ))
        (nhds ‖ρ t‖) := (htR.tendsto_slope).norm
    have hle : ‖deriv h t‖ ≤ ‖ρ t‖ :=
      le_of_tendsto_of_tendsto hlimh hlimR hslopeBound
    rw [Real.norm_eq_abs, abs_of_nonneg (hρnn t)] at hle
    exact hle
  · rw [deriv_zero_of_not_differentiableAt hd]
    simpa using hρnn t

/-- **The image-stationary Fuglede node (the single genuine residual).**  For an
`IsQCAnalytic` map `f` with inverse `g = f⁻¹` and the (Lebesgue-null) image
`M = f '' Nf` of the `f`-degeneracy set, the family of absolutely continuous image curves
`δ` for which the **image-stationary contact**
`{t ∈ [0,1] | δ t ∈ M ∧ deriv δ t = 0 ∧ deriv (g ∘ δ) t ≠ 0}` (the pull-back `γ = g ∘ δ`
moves through `f`'s degeneracy set while `δ` itself is stationary) has positive Lebesgue
measure, has zero modulus.

This is the irreducible image-stationary node.  The contact carries **zero `δ`-arc
length** (`deriv δ = 0`), so it is *invisible* to every admissible image-side density
`ρ` (`ρ(δ t) · ‖deriv δ t‖ = ρ(δ t) · 0 = 0`, regardless of `ρ`): one cannot witness it
by a density on `M`, even with `ρ = ∞ · 𝟙_M`.  Its nullity is the genuine
modulus–area/Fuglede content for the `W^{1,2}_loc` inverse `g`
(`IsQCAnalytic.inverse_memW12loc` / `inverse_hasWeakGradient`): for `g ∈ W^{1,2}` and
modulus-almost-every `δ`, `g` is differentiable along `δ` with the chain rule
`deriv (g ∘ δ) t = (D g)(δ t) · deriv δ t` holding a.e. **including at the stationary
points `deriv δ t = 0`** (where it forces `deriv (g ∘ δ) t = 0`).  The singular shear
`g(x + iy) = x + i(y + s x)` (s monotone singular) shows this is *false* without the
genuine Sobolev/ACL structure of `g`, so `hf` (through `inverse_memW12loc`) is
load-bearing.  This is exactly the planar borderline (`p = n = 2`) Fuglede theorem
(Väisälä, *Lectures on n-dimensional QC mappings*, §28), absent from Mathlib. -/
private theorem imageStationary_fugledeNode_modulus_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Δ : Set (ℝ → ℂ))
    (_hΔcont : ∀ δ ∈ Δ, Continuous δ)
    (_hΔac : ∀ δ ∈ Δ, AbsolutelyContinuousOnInterval δ 0 1) :
    curveModulus {δ ∈ Δ | 0 < volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      δ t ∈ f '' {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} ∧
      deriv δ t = 0 ∧ deriv (⇑(hf.1.1.homeomorph f).symm ∘ δ) t ≠ 0}} = 0 := by
  classical
  -- The inverse `g = f⁻¹` is itself `IsQCAnalytic`, so every `f`-level length–area lemma
  -- applies to `g`.  This is the load-bearing Sobolev structure.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  obtain ⟨b', hgQC⟩ := hf.inverse_isQCAnalytic
  -- The `f`-degeneracy set and its image.
  set Nf : Set ℂ := {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hNf
  set M : Set ℂ := f '' Nf with hM
  -- The two zero-modulus families: non-good curves of `g`, and infinite `g`-gradient curves.
  set P : Set (ℝ → ℂ) := {δ ∈ Δ | ¬ GoodCurve g δ} with hP
  set Q : Set (ℝ → ℂ) :=
    {δ ∈ Δ | arcLengthLineIntegral (fun z => (‖fderiv ℝ g z‖₊ : ℝ≥0∞)) δ = ∞} with hQ
  have hPzero : curveModulus P = 0 :=
    IsQCAnalytic.curveModulus_notGoodCurve_zero hgQC Δ _hΔcont
  have hQzero : curveModulus Q = 0 :=
    curveModulus_lineIntegral_top_zero hgQC Δ _hΔcont
  -- The node family embeds in `P ∪ Q`; finish by subadditivity and monotonicity.
  refine le_antisymm ?_ (zero_le _)
  rw [← curveModulus_union_zero hPzero hQzero]
  refine curveModulus_mono ?_
  rintro δ ⟨hδΔ, hδpos⟩
  -- Notation: the node set of `δ`.
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ δ t ∈ M ∧
    deriv δ t = 0 ∧ deriv (g ∘ δ) t ≠ 0} with hS
  -- Suppose `δ ∉ P ∪ Q`: then `δ` is `g`-good with finite `g`-gradient line integral.
  by_contra hnotin
  rw [Set.mem_union, not_or] at hnotin
  obtain ⟨hnP, hnQ⟩ := hnotin
  have hgood : GoodCurve g δ := by by_contra hng; exact hnP ⟨hδΔ, hng⟩
  have hfin : arcLengthLineIntegral (fun z => (‖fderiv ℝ g z‖₊ : ℝ≥0∞)) δ ≠ ∞ := by
    intro htop; exact hnQ ⟨hδΔ, htop⟩
  have hδcont : Continuous δ := _hΔcont δ hδΔ
  have hδac : AbsolutelyContinuousOnInterval δ 0 1 := _hΔac δ hδΔ
  -- The density `ρ t := ‖fderiv ℝ g (δ t)‖ · ‖deriv δ t‖` (the `g`-gradient density along `δ`).
  set ρ : ℝ → ℝ := fun t => ‖fderiv ℝ g (δ t)‖ * ‖deriv δ t‖ with hρ
  have hρnn : ∀ t, 0 ≤ ρ t := fun t => by rw [hρ]; positivity
  -- `ρ` is integrable on `[0,1]` (the `ℝ`-valued content of `hfin`).
  have hρint : IntegrableOn ρ (Set.Icc (0 : ℝ) 1) volume := by
    have := integrableOn_fderiv_norm_mul_deriv_uIcc hgQC hδcont hfin 0 1
      (by rw [Set.uIcc_of_le (by norm_num)])
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at this
  -- The upper-gradient bound from the Fuglede inequality applied to `g`.
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      dist ((g ∘ δ) x) ((g ∘ δ) y) ≤ |∫ u in x..y, ρ u| := by
    intro x hx y hy
    have hxy : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc hx hy
    have hub := fugledeUpperGradient hgQC hδcont hδac hfin x y hxy hgood
    -- `∫ uIoc x y, ρ = |∫ x..y, ρ|` since `ρ ≥ 0`.
    have habs : |∫ u in x..y, ρ u| = ∫ u in Set.uIoc x y, ρ u := by
      rw [intervalIntegral.abs_intervalIntegral_eq]
      rw [abs_of_nonneg (integral_nonneg_of_ae (Filter.Eventually.of_forall hρnn))]
    rw [habs]
    exact hub
  -- The helper: a.e. on `Ioo 0 1`, `‖deriv (g ∘ δ) t‖ ≤ ρ t`.
  have hae := norm_deriv_le_of_dist_le_intervalIntegral hρnn hρint hbound
  -- The node set is null: on it `deriv δ t = 0` forces `ρ t = 0`, hence `deriv (g∘δ) t = 0`,
  -- contradicting `deriv (g∘δ) t ≠ 0`.
  have hSnull : volume S = 0 := by
    -- The a.e.-bound set `bad = {t | ¬(‖deriv (g∘δ) t‖ ≤ ρ t)}` is null for `volume|Ioo`.
    set bad : Set ℝ := {t : ℝ | ¬ (‖deriv (g ∘ δ) t‖ ≤ ρ t)} with hbad
    have hbadnull : volume (bad ∩ Set.Ioo (0 : ℝ) 1) = 0 := by
      have := ae_iff.mp hae
      rwa [Measure.restrict_apply' measurableSet_Ioo] at this
    -- `S ∩ Ioo 0 1 ⊆ bad`: on `S`, `deriv δ t = 0 ⟹ ρ t = 0`, but `deriv (g∘δ) t ≠ 0`.
    have hSIoo_null : volume (S ∩ Set.Ioo (0 : ℝ) 1) = 0 := by
      refine measure_mono_null (fun t ht => ?_) hbadnull
      obtain ⟨htS, htIoo⟩ := ht
      obtain ⟨_, _, hδ0, hgd⟩ := htS
      have hρ0 : ρ t = 0 := by rw [hρ]; simp [hδ0]
      refine ⟨?_, htIoo⟩
      rw [hbad, Set.mem_setOf_eq, hρ0]
      intro hle
      exact hgd (norm_le_zero_iff.mp hle)
    -- `S \ Ioo 0 1 ⊆ {0,1}` (since `S ⊆ Icc 0 1`), a null set.
    have hSdiff_null : volume (S \ Set.Ioo (0 : ℝ) 1) = 0 := by
      refine measure_mono_null (fun t ht => ?_)
        (measure_union_null (measure_singleton 0) (measure_singleton 1))
      obtain ⟨⟨ht01, _⟩, htn⟩ := ht
      rcases eq_or_lt_of_le ht01.1 with h0 | h0
      · exact Or.inl h0.symm
      · rcases eq_or_lt_of_le ht01.2 with h1 | h1
        · exact Or.inr h1
        · exact absurd ⟨h0, h1⟩ htn
    -- `volume S ≤ volume (S ∩ Ioo) + volume (S \ Ioo) = 0`.
    refine nonpos_iff_eq_zero.mp ?_
    calc volume S
        ≤ volume ((S ∩ Set.Ioo (0:ℝ) 1) ∪ (S \ Set.Ioo (0:ℝ) 1)) := by
          refine measure_mono (fun t ht => ?_)
          by_cases h : t ∈ Set.Ioo (0:ℝ) 1
          · exact Or.inl ⟨ht, h⟩
          · exact Or.inr ⟨ht, h⟩
      _ ≤ volume (S ∩ Set.Ioo (0:ℝ) 1) + volume (S \ Set.Ioo (0:ℝ) 1) := measure_union_le _ _
      _ = 0 := by rw [hSIoo_null, hSdiff_null, add_zero]
  rw [hSnull] at hδpos
  exact absurd hδpos (not_lt.mpr (zero_le _))

/-- **The image-stationary residual is modulus-null.**  For an `IsQCAnalytic` map `f` with
inverse homeomorphism `g = f⁻¹` and the `f`-degeneracy set
`Nf = {z | ¬(DifferentiableAt ℝ f z ∧ 0 < det (fderiv ℝ f z))}` (Lebesgue-null), the family
of absolutely continuous **image** curves `δ` (joining the image sides of some quadrilateral,
hence in `Δ`) whose source preimage `γ := g ∘ δ` meets `Nf` with **positive `γ`-arc length**
has zero modulus.

This is the single genuine residual of the analytic ⇒ geometric direction — the
*image-stationary* phenomenon.  The contact set `C = {t | γ t ∈ Nf ∧ deriv γ t ≠ 0}` (of
positive measure, by membership in the family) splits along whether `δ` itself moves:

* **`C₁ = {t ∈ C | deriv δ t ≠ 0}`** — there `δ t = f (γ t) ∈ f '' Nf` and `δ` *moves*, so
  `δ` meets the null set `f '' Nf` with positive `δ`-arc length; this sub-family has zero
  modulus by `curveModulus_meetsNullSet_zero` (`f '' Nf` is null by planar Lusin-(N),
  `lusinN_degeneracy`).
* **`C₂ = {t ∈ C | deriv δ t = 0}`** — the *image-stationary* part: `δ` is stationary while
  `γ = g ∘ δ` moves through `Nf` (`deriv γ t ≠ 0`).  Its nullity for modulus-a.e. `δ` is the
  irreducible `W^{1,2}` Fuglede node `imageStationary_fugledeNode_modulus_zero`.

`C` positive forces one of `C₁`, `C₂` positive, so the family embeds in the union of the two
zero-modulus families; `curveModulus_union_zero`/`curveModulus_mono` finish. -/
theorem isQCGeometric_imageStationary_residual_modulus_zero {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) (Δ : Set (ℝ → ℂ))
    (_hΔcont : ∀ δ ∈ Δ, Continuous δ)
    (_hΔac : ∀ δ ∈ Δ, AbsolutelyContinuousOnInterval δ 0 1) :
    curveModulus {δ ∈ Δ | 1 ≤ arcLengthLineIntegral
      ({z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)}.indicator (fun _ => ∞))
      (⇑(hf.1.1.homeomorph f).symm ∘ δ)} = 0 := by
  classical
  -- Notation: the inverse `g = f⁻¹`, the `f`-degeneracy set `Nf`, its image `M = f '' Nf`.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hfg : ∀ w, f (g w) = w := (hf.1.1.homeomorph f).apply_symm_apply
  set Nf : Set ℂ := {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hNf
  set M : Set ℂ := f '' Nf with hM
  have hMnull : volume M = 0 := lusinN_degeneracy hf
  have hNfmeas : MeasurableSet Nf := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have hrw : Nf = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hNf, Set.mem_compl_iff, not_and]
    rw [hrw]; exact (hd.inter hdet).compl
  have hMmeas : MeasurableSet M := by
    -- `M = f '' Nf = g ⁻¹' Nf` (since `g` is a bijection with inverse `f`).
    have himg : M = g ⁻¹' Nf := by
      ext w; constructor
      · rintro ⟨z, hz, rfl⟩
        have hgz : g (f z) = z := (hf.1.1.homeomorph f).symm_apply_apply z
        rw [Set.mem_preimage, hg, ← hg, hgz]; exact hz
      · intro hw
        exact ⟨g w, hw, hfg w⟩
    rw [himg]
    exact hNfmeas.preimage (hf.1.1.homeomorph f).symm.continuous.measurable
  -- The two zero-modulus families.
  -- (A) the curves meeting the null image `M` with positive `δ`-arc length (the `C₁` part).
  set A : Set (ℝ → ℂ) :=
    {δ ∈ Δ | 1 ≤ arcLengthLineIntegral (M.indicator (fun _ => (∞ : ℝ≥0∞))) δ} with hA
  have hAzero : curveModulus A = 0 := curveModulus_meetsNullSet_zero hMmeas hMnull Δ
  -- (B) the image-stationary Fuglede node (the `C₂` part).
  set B : Set (ℝ → ℂ) :=
    {δ ∈ Δ | 0 < volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ δ t ∈ M ∧
      deriv δ t = 0 ∧ deriv (g ∘ δ) t ≠ 0}} with hB
  have hBzero : curveModulus B = 0 :=
    imageStationary_fugledeNode_modulus_zero hf Δ _hΔcont _hΔac
  -- The residual family embeds in `A ∪ B`.
  refine le_antisymm ?_ (zero_le _)
  rw [← curveModulus_union_zero hAzero hBzero]
  refine curveModulus_mono ?_
  -- Take a member `δ` of the residual family; show `δ ∈ A ∪ B`.
  rintro δ ⟨hδΔ, hδmeet⟩
  set γ : ℝ → ℂ := g ∘ δ with hγ
  have hδcont : Continuous δ := _hΔcont δ hδΔ
  have hγcont : Continuous γ := ((hf.1.1.homeomorph f).symm.continuous).comp hδcont
  -- The `γ`-contact footprint `C = {t ∈ [0,1] | γ t ∈ Nf ∧ deriv γ t ≠ 0}` has positive
  -- measure, since `1 ≤ ∫ (∞·𝟙_Nf)(γ t) ‖γ' t‖ dt`.
  set C : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ γ t ∈ Nf ∧ deriv γ t ≠ 0} with hC
  have hCmeas : MeasurableSet C := by
    have h01 : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
    have hpreNf : MeasurableSet {t : ℝ | γ t ∈ Nf} := hNfmeas.preimage hγcont.measurable
    have hderiv : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
      ((measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv γ)).compl
    have hrw : C = Set.Icc (0 : ℝ) 1 ∩ {t : ℝ | γ t ∈ Nf} ∩ {t : ℝ | deriv γ t ≠ 0} := by
      ext t; simp only [hC, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hrw]; exact (h01.inter hpreNf).inter hderiv
  have hCpos : 0 < volume C := by
    -- The line integral equals `∞ * volume C`; if `volume C = 0` it would be `0 < 1`.
    have hintegrand : ∀ t, (Nf.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
        (‖deriv γ t‖₊ : ℝ≥0∞)
          = ({t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0}.indicator (fun _ => (∞ : ℝ≥0∞))) t := by
      intro t
      by_cases hd : deriv γ t = 0
      · have htB : t ∉ {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0} := fun h => h.2 hd
        rw [Set.indicator_of_notMem htB]; simp [hd]
      · by_cases hγN : γ t ∈ Nf
        · have htB : t ∈ {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0} := ⟨hγN, hd⟩
          have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
            simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]; exact hd
          rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
        · have htB : t ∉ {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0} := fun h => hγN h.1
          rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
    have hBmeas2 : MeasurableSet {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0} := by
      have hpreNf : MeasurableSet {t : ℝ | γ t ∈ Nf} := hNfmeas.preimage hγcont.measurable
      have hderiv : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
        ((measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv γ)).compl
      have : {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0}
          = {t : ℝ | γ t ∈ Nf} ∩ {t : ℝ | deriv γ t ≠ 0} := by
        ext t; simp [Set.mem_inter_iff]
      rw [this]; exact hpreNf.inter hderiv
    have hLI : arcLengthLineIntegral (Nf.indicator (fun _ => (∞ : ℝ≥0∞))) γ
        = (∞ : ℝ≥0∞) * volume C := by
      unfold arcLengthLineIntegral
      rw [show (fun t => (Nf.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) * (‖deriv γ t‖₊ : ℝ≥0∞))
          = {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0}.indicator (fun _ => (∞ : ℝ≥0∞)) from
        funext hintegrand]
      rw [lintegral_indicator hBmeas2, setLIntegral_const,
        Measure.restrict_apply hBmeas2]
      have hseteq : {t : ℝ | γ t ∈ Nf ∧ deriv γ t ≠ 0} ∩ Set.Icc (0 : ℝ) 1 = C := by
        rw [hC]; ext t; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
      rw [hseteq]
    by_contra hle
    rw [not_lt, nonpos_iff_eq_zero] at hle
    rw [hLI, hle, mul_zero] at hδmeet
    exact absurd hδmeet (by norm_num)
  -- Split `C = C₂ ∪ (C \ C₂)`, where `C₂ = {t ∈ C | deriv δ t = 0}`.
  set C₂ : Set ℝ := {t ∈ C | deriv δ t = 0} with hC₂
  by_cases hC₂pos : 0 < volume C₂
  · -- `C₂` positive: `δ ∈ B` (image-stationary contact).
    right
    refine ⟨hδΔ, lt_of_lt_of_le hC₂pos (measure_mono ?_)⟩
    -- `C₂ ⊆ {t ∈ [0,1] | δ t ∈ M ∧ deriv δ t = 0 ∧ deriv γ t ≠ 0}`.
    rintro t ⟨⟨ht01, hγNf, hγderiv⟩, hδ0⟩
    refine ⟨ht01, ?_, hδ0, hγderiv⟩
    -- `δ t = f (γ t) ∈ f '' Nf = M`, since `γ t = g (δ t)` and `γ t ∈ Nf`.
    have hδeq : δ t = f (γ t) := by rw [hγ]; simp only [Function.comp_apply, hfg (δ t)]
    rw [hδeq]; exact ⟨γ t, hγNf, rfl⟩
  · -- `C₂` null: `C₁ = C \ C₂` (where `deriv δ ≠ 0`) carries the positive measure ⟹ `δ ∈ A`.
    left
    -- `C₁ := {t ∈ C | deriv δ t ≠ 0}` has positive measure.
    have hC₂null : volume C₂ = 0 := by rw [not_lt, nonpos_iff_eq_zero] at hC₂pos; exact hC₂pos
    set C₁ : Set ℝ := {t ∈ C | deriv δ t ≠ 0} with hC₁
    have hC₁meas : MeasurableSet C₁ := by
      have hderiv : MeasurableSet {t : ℝ | deriv δ t ≠ 0} :=
        ((measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv δ)).compl
      have hrw : C₁ = C ∩ {t : ℝ | deriv δ t ≠ 0} := by
        ext t; simp [hC₁, Set.mem_inter_iff]
      rw [hrw]; exact hCmeas.inter hderiv
    have hC₁pos : 0 < volume C₁ := by
      -- `C = C₁ ∪ C₂`, so `volume C ≤ volume C₁ + volume C₂ = volume C₁`.
      have hCsub : C ⊆ C₁ ∪ C₂ := by
        intro t htC
        by_cases hd : deriv δ t = 0
        · exact Or.inr ⟨htC, hd⟩
        · exact Or.inl ⟨htC, hd⟩
      have hle : volume C ≤ volume C₁ + volume C₂ :=
        le_trans (measure_mono hCsub) (measure_union_le _ _)
      rw [hC₂null, add_zero] at hle
      exact lt_of_lt_of_le hCpos hle
    -- On `C₁`, `δ t = f (γ t) ∈ M` and `deriv δ t ≠ 0`, so `δ` meets `M` positively.
    refine ⟨hδΔ, ?_⟩
    -- Show `1 ≤ ∫ (∞·𝟙_M)(δ t) ‖δ' t‖ dt` by showing the integrand is `∞` on `C₁ ⊆ [0,1]`.
    have hδMpos : 0 < volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ δ t ∈ M ∧ deriv δ t ≠ 0} := by
      refine lt_of_lt_of_le hC₁pos (measure_mono ?_)
      rintro t ⟨⟨ht01, hγNf, _⟩, hδd⟩
      have hδeq : δ t = f (γ t) := by rw [hγ]; simp only [Function.comp_apply, hfg (δ t)]
      exact ⟨ht01, by rw [hδeq]; exact ⟨γ t, hγNf, rfl⟩, hδd⟩
    -- Convert positive-measure contact into `arcLengthLineIntegral ≥ 1 = ∞`.
    set D : Set ℝ := {t : ℝ | δ t ∈ M ∧ deriv δ t ≠ 0} with hD
    have hDmeas : MeasurableSet D := by
      have hpreM : MeasurableSet {t : ℝ | δ t ∈ M} := hMmeas.preimage hδcont.measurable
      have hderiv : MeasurableSet {t : ℝ | deriv δ t ≠ 0} :=
        ((measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv δ)).compl
      have : D = {t : ℝ | δ t ∈ M} ∩ {t : ℝ | deriv δ t ≠ 0} := by
        ext t; simp [hD, Set.mem_inter_iff]
      rw [this]; exact hpreM.inter hderiv
    have hintegrand : ∀ t, (M.indicator (fun _ => (∞ : ℝ≥0∞)) (δ t)) *
        (‖deriv δ t‖₊ : ℝ≥0∞) = D.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
      intro t
      by_cases hd : deriv δ t = 0
      · have htD : t ∉ D := fun h => h.2 hd
        rw [Set.indicator_of_notMem htD]; simp [hd]
      · by_cases hδM : δ t ∈ M
        · have htD : t ∈ D := ⟨hδM, hd⟩
          have hnz : (‖deriv δ t‖₊ : ℝ≥0∞) ≠ 0 := by
            simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]; exact hd
          rw [Set.indicator_of_mem hδM, Set.indicator_of_mem htD, ENNReal.top_mul hnz]
        · have htD : t ∉ D := fun h => hδM h.1
          rw [Set.indicator_of_notMem hδM, Set.indicator_of_notMem htD, zero_mul]
    have hLI : arcLengthLineIntegral (M.indicator (fun _ => (∞ : ℝ≥0∞))) δ
        = (∞ : ℝ≥0∞) * volume (D ∩ Set.Icc (0 : ℝ) 1) := by
      unfold arcLengthLineIntegral
      rw [show (fun t => (M.indicator (fun _ => (∞ : ℝ≥0∞)) (δ t)) * (‖deriv δ t‖₊ : ℝ≥0∞))
          = D.indicator (fun _ => (∞ : ℝ≥0∞)) from funext hintegrand]
      rw [lintegral_indicator hDmeas, setLIntegral_const, Measure.restrict_apply hDmeas,
        Set.inter_comm]
    -- `{t ∈ [0,1] | δ t ∈ M ∧ deriv δ t ≠ 0} = D ∩ [0,1]`, so its measure is positive.
    have hDIcc_pos : 0 < volume (D ∩ Set.Icc (0 : ℝ) 1) := by
      refine lt_of_lt_of_le hδMpos (measure_mono ?_)
      rintro t ⟨ht01, hδM, hδd⟩
      exact ⟨⟨hδM, hδd⟩, ht01⟩
    rw [hLI, ENNReal.top_mul (ne_of_gt hDIcc_pos)]
    exact le_top

/-- **The pushforward of the chain-rule-good subfamily is `K`-quasiconformally bounded.**
For an `IsQCAnalytic` map `f` with Beltrami norm at most `(K − 1)/(K + 1)` and a family `Γ`
of continuous, absolutely continuous curves, the image under `f` of the chain-rule **good**
subfamily `{γ ∈ Γ | P_f(γ)}` (those `γ` for which `f ∘ γ` is absolutely continuous with the
a.e. chain rule and positive Jacobian) has modulus at most `K · curveModulus Γ`.

This is the *clean* (length–area energy-transfer) bound on the chain-rule-good image part; it
is consumed by the main `isQCGeometric_of_isQCAnalytic` proof for the good source curves. The
argument is the dilatation-controlled change of variables: from the a.e. bound
`‖(Df)⁻¹‖² · det (Df) ≤ K`, the transferred density `σ(w) = ρ(g w)·‖(Df(g w))⁻¹‖`
(`g = f⁻¹`) is admissible for the good image with energy at most `K · ∫ ρ²`. -/
private theorem pushforwardGood_modulus_le {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    {b : BeltramiCoeff} (hb : b.normInf ≤ (K - 1) / (K + 1)) (hf : IsQCAnalytic f b)
    (Γ : Set (ℝ → ℂ)) (_hΓcont : ∀ γ ∈ Γ, Continuous γ)
    (_hΓac : ∀ γ ∈ Γ, AbsolutelyContinuousOnInterval γ 0 1) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) ''
      (Γ \ {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
            AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
          (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
              deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
            HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)}))
      ≤ ENNReal.ofReal K * curveModulus Γ := by
  classical
  -- Notation.
  set hhom : IsHomeomorph f := hf.1.1 with hhom_def
  -- The almost-everywhere essential-sup bound on the Beltrami coefficient.
  have hμae : ∀ᵐ z : ℂ, ‖b.μ z‖ ≤ b.normInf := by
    filter_upwards [ae_le_eLpNormEssSup (f := b.μ) (μ := volume)] with z hz
    have hfin : eLpNormEssSup b.μ volume ≠ ⊤ := ne_top_of_lt b.bound
    have hz' : (‖b.μ z‖₊ : ℝ≥0∞) ≤ eLpNormEssSup b.μ volume := by
      simpa [enorm_eq_nnnorm] using hz
    have := (ENNReal.toReal_le_toReal (by simp) hfin).mpr hz'
    simpa [BeltramiCoeff.normInf, coe_nnnorm] using this
  -- STEP 1.  Almost-everywhere dilatation bound: ‖(Df z)⁻¹‖² · det (Df z) ≤ K.
  have hkbound : b.normInf < 1 := b.normInf_lt_one
  have hKkey : (1 + b.normInf) / (1 - b.normInf) ≤ K := by
    have hknn : (0 : ℝ) ≤ b.normInf := b.normInf_nonneg
    have hKpos : (0 : ℝ) < K + 1 := by linarith
    have hk_le : b.normInf ≤ (K - 1) / (K + 1) := hb
    have hKm1 : (K - 1) / (K + 1) < 1 := by
      rw [div_lt_one hKpos]; linarith
    have h1mk : (0 : ℝ) < 1 - b.normInf := by linarith
    rw [div_le_iff₀ h1mk]
    have hk_mul : b.normInf * (K + 1) ≤ K - 1 := by
      rw [← le_div_iff₀ hKpos]; exact hk_le
    nlinarith [hk_mul]
  have hdil : ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
    filter_upwards [hf.1.2, hf.2.2, hμae] with z hdet hbel hμz
    set p : ℂ := dz f z with hp
    set q : ℂ := dzbar f z with hq
    set d : ℝ := (fderiv ℝ f z).det with hd
    have hdval : d = ‖p‖ ^ 2 - ‖q‖ ^ 2 := det_fderiv_eq_wirtinger f z
    have hinvval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ = (‖p‖ + ‖q‖) / d :=
      opNorm_inverse_eq_wirtinger f z hdet
    have hqeq : ‖q‖ = ‖b.μ z‖ * ‖p‖ := by rw [hq, ← hq, hbel, norm_mul]
    have hqp : ‖q‖ ≤ b.normInf * ‖p‖ := by
      rw [hqeq]; gcongr
    have hdpos : 0 < d := hdet
    have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg q, norm_nonneg p, hdval, hdpos]
    have hqnn : 0 ≤ ‖q‖ := norm_nonneg q
    have hpqlt : ‖q‖ < ‖p‖ := by nlinarith [hdval, hdpos, norm_nonneg p]
    have hpmq : 0 < ‖p‖ - ‖q‖ := by linarith
    have hfactor : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * d
        = (‖p‖ + ‖q‖) / (‖p‖ - ‖q‖) := by
      rw [hinvval, div_pow, hdval]
      have hsplit : ‖p‖ ^ 2 - ‖q‖ ^ 2 = (‖p‖ + ‖q‖) * (‖p‖ - ‖q‖) := by ring
      rw [hsplit]
      have hsum_ne : ‖p‖ + ‖q‖ ≠ 0 := by positivity
      have hpmq_ne : ‖p‖ - ‖q‖ ≠ 0 := ne_of_gt hpmq
      field_simp
    rw [hfactor]
    refine le_trans ?_ hKkey
    rw [div_le_div_iff₀ hpmq (by linarith : (0:ℝ) < 1 - b.normInf)]
    nlinarith [hqp, hppos]
  -- Global infrastructure: the differentiability set and the inverse map.
  set S : Set ℂ := {z : ℂ | DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det} with hSdef
  have hSmeas : MeasurableSet S := by
    apply MeasurableSet.inter (measurableSet_of_differentiableAt ℝ f)
    exact measurableSet_lt measurable_const
      ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
  have hSae : ∀ᵐ z : ℂ, z ∈ S := by
    filter_upwards [hf.1.2, IsQCAnalytic.ae_differentiableAt hf] with z hz hzd
    exact ⟨hzd, hz⟩
  have hScompl_null : volume (Sᶜ : Set ℂ) = 0 := by
    have : {z : ℂ | ¬ z ∈ S} = (Sᶜ : Set ℂ) := rfl
    rw [← this, ← ae_iff]
    filter_upwards [hSae] with z hz using hz
  set g : ℂ → ℂ := ⇑(hhom.homeomorph f).symm with hg_def
  have hgf : ∀ z, g (f z) = z := (hhom.homeomorph f).symm_apply_apply
  have hfg : ∀ w, f (g w) = w := (hhom.homeomorph f).apply_symm_apply
  have hg_cont : Continuous g := (hhom.homeomorph f).symm.continuous
  have hfderiv_S : ∀ z ∈ S, HasFDerivWithinAt f (fderiv ℝ f z) S z := fun z hz =>
    (hz.1.hasFDerivAt).hasFDerivWithinAt
  have hfinj_S : Set.InjOn f S := hhom.injective.injOn
  have hfSmeas : MeasurableSet (f '' S) :=
    measurable_image_of_fderivWithin hSmeas hfderiv_S hfinj_S
  -- The exceptional (bad) and good subfamilies of `Γ`.
  set badProp : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hbadProp
  set Γbad : Set (ℝ → ℂ) := {γ ∈ Γ | badProp γ} with hΓbad
  set Γgood : Set (ℝ → ℂ) := Γ \ Γbad with hΓgood
  -- KEY: for every density `ρ` admissible for `Γ`,
  --   curveModulus ((f∘·)''Γgood) ≤ ofReal K * ∫⁻ ρ².
  have key : ∀ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ Γ →
      curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
        ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
    intro ρ ⟨hρmeas, hρadm⟩
    set wt : ℂ → ℝ≥0∞ := fun z =>
      ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (fderiv ℝ f z).det) with hwt_def
    have hwt_eq : ∀ z ∈ S, wt z =
        ENNReal.ofReal ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ := by
      intro z hz
      rw [hwt_def, opNorm_inverse_eq_wirtinger f z hz.2]
    set σ : ℂ → ℝ≥0∞ := fun w =>
      (f '' S).indicator (fun w => ρ (g w) * wt (g w)) w with hσ_def
    have hfderivmeas : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    have hdzmeas : Measurable (fun z : ℂ => dz f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dz] using (measurable_const.mul ((h1.sub (measurable_const.mul h2))))
    have hdzbarmeas : Measurable (fun z : ℂ => dzbar f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dzbar] using (measurable_const.mul ((h1.add (measurable_const.mul h2))))
    have hdetmeas : Measurable (fun z : ℂ => (fderiv ℝ f z).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp hfderivmeas
    have hwtmeas : Measurable wt := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact ((hdzmeas.norm.add hdzbarmeas.norm).div hdetmeas)
    have hσmeas : Measurable σ := by
      refine (Measurable.indicator ?_ hfSmeas)
      exact (hρmeas.comp hg_cont.measurable).mul (hwtmeas.comp hg_cont.measurable)
    -- STEP 2.  Energy bound: ∫⁻ σ² ≤ ofReal K * ∫⁻ ρ².
    have henergy : ∫⁻ w, (σ w) ^ 2 ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
      have hσsq_ind : (fun w => (σ w) ^ 2)
          = (f '' S).indicator (fun w => (ρ (g w) * wt (g w)) ^ 2) := by
        funext w
        simp only [hσ_def]
        by_cases hw : w ∈ f '' S
        · simp only [Set.indicator_of_mem hw]
        · simp only [Set.indicator_of_notMem hw]; ring
      rw [hσsq_ind, lintegral_indicator hfSmeas]
      have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (volume : Measure ℂ) hSmeas hfderiv_S hfinj_S
        (fun w => (ρ (g w) * wt (g w)) ^ 2)
      rw [hcov]
      have hmono : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := by
        refine setLIntegral_mono_ae' hSmeas ?_
        filter_upwards [hdil] with z hzdil hzS
        rw [hgf z, hwt_eq z hzS]
        have hdetpos : 0 < (fderiv ℝ f z).det := hzS.2
        rw [abs_of_pos hdetpos, mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [show ENNReal.ofReal (fderiv ℝ f z).det *
              ((ρ z) ^ 2 * ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2))
            = (ρ z) ^ 2 * (ENNReal.ofReal (fderiv ℝ f z).det *
                ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2)) by ring]
        rw [← ENNReal.ofReal_mul hdetpos.le, mul_comm (ENNReal.ofReal K) ((ρ z) ^ 2)]
        gcongr
        rw [mul_comm]; exact hzdil
      calc ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := hmono
        _ = ENNReal.ofReal K * ∫⁻ z in S, (ρ z) ^ 2 := by
            rw [lintegral_const_mul _ (hρmeas.pow_const 2)]
        _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    -- STEP 3.  `σ` is admissible for `(f∘·)''Γgood`.
    have hσadm : IsAdmissibleDensity σ ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood) := by
      refine ⟨hσmeas, ?_⟩
      rintro δ ⟨γ, hγgood, rfl⟩
      have hγΓ : γ ∈ Γ := hγgood.1
      have hnotbad : ¬ badProp γ := by
        intro hbad; exact hγgood.2 ⟨hγΓ, hbad⟩
      rw [hbadProp] at hnotbad
      obtain ⟨hAC, hdetγ, hchainγ⟩ := not_not.mp hnotbad
      have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ σ ((f ∘ γ) t) * (‖deriv (f ∘ γ) t‖₊ : ℝ≥0∞) := by
        filter_upwards [hdetγ, hchainγ] with t hdett₀ hchaint₀
        rcases eq_or_ne (deriv γ t) 0 with hd0 | hd0
        · simp [hd0]
        have hdett : 0 < (fderiv ℝ f (γ t)).det := hdett₀ hd0
        have hchaint : HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t :=
          hchaint₀ hd0
        set A : ℂ →L[ℝ] ℂ := fderiv ℝ f (γ t) with hA
        have hdett' : 0 < (fderiv ℝ f (γ t)).det := hdett
        have hγtS : γ t ∈ S := by
          refine ⟨?_, hdett'⟩
          by_contra hnd
          rw [fderiv_zero_of_not_differentiableAt hnd] at hdett'
          simp [ContinuousLinearMap.det] at hdett'
        have hAinv : A.IsInvertible :=
          ⟨A.toContinuousLinearEquivOfDetNeZero hdett.ne',
            A.coe_toContinuousLinearEquivOfDetNeZero hdett.ne'⟩
        have hderiv : deriv (f ∘ γ) t = A (deriv γ t) := hchaint.deriv
        have hfγtS : f (γ t) ∈ f '' S := ⟨γ t, hγtS, rfl⟩
        have hσval : σ ((f ∘ γ) t) = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ := by
          simp only [Function.comp_apply, hσ_def]
          rw [Set.indicator_of_mem hfγtS, hgf, hwt_eq (γ t) hγtS]
        rw [hσval, hderiv]
        have hkey : (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by
          have hself : A.inverse (A (deriv γ t)) = deriv γ t :=
            ContinuousLinearMap.IsInvertible.inverse_apply_self hAinv (deriv γ t)
          have hop : ‖deriv γ t‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ := by
            have hle : ‖A.inverse (A (deriv γ t))‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ :=
              A.inverse.le_opNNNorm _
            rwa [hself] at hle
          have hcoe : ENNReal.ofReal ‖A.inverse‖ = (‖A.inverse‖₊ : ℝ≥0∞) := by
            rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]
          rw [hcoe, ← ENNReal.coe_mul]
          exact_mod_cast hop
        calc ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ρ (γ t) * (ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞)) := by
              gcongr
          _ = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by ring
      have hint : arcLengthLineIntegral ρ γ ≤ arcLengthLineIntegral σ (f ∘ γ) := by
        unfold arcLengthLineIntegral
        exact lintegral_mono_ae hpoint
      exact le_trans (hρadm γ hγΓ) hint
    calc curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
        ≤ ∫⁻ w, (σ w) ^ 2 := iInf₂_le σ hσadm
      _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := henergy
  -- Conclude: `curveModulus ((f∘·)''Γgood) ≤ ofReal K * curveModulus Γ` from `key`.
  have hKne0 : ENNReal.ofReal K ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hKnetop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  change curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood) ≤ ENNReal.ofReal K * curveModulus Γ
  conv_rhs => rw [curveModulus, ENNReal.mul_iInf_of_ne hKne0 hKnetop]
  refine le_iInf fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne hKne0 hKnetop]
  refine le_iInf fun hρ => ?_
  exact key ρ hρ

/-- **Analytic ⇒ geometric** (clean endpoint). A map carrying an analytic-quasiconformal
structure with Beltrami norm `≤ (K − 1)/(K + 1)` is `K`-quasiconformal in the geometric
(modulus) sense.

The proof is the genuine image-side argument, available downstream of `QC/InverseQC.lean`
where the inverse map `g = f⁻¹` is known to be analytic-quasiconformal
(`IsQCAnalytic.inverse_isQCAnalytic`). For each quadrilateral `Q`, the genuine image family
`Q.imageCurveFamily f` (all absolutely continuous curves joining the image sides) is split
through the predicate "`δ` is `g`-chain-rule-good":

* the **good** curves `δ` have `g ∘ δ` absolutely continuous, so `γ := g ∘ δ ∈ Q.curveFamily`
  (it joins the back-image sides and stays in the back-image region, via `g (f p) = p`) and
  `δ = f ∘ γ` (via `f (g w) = w`); hence the good part embeds in the pushforward
  `(f ∘ ·) '' Q.curveFamily`, whose good part has modulus at most `K · M(Q)` by the
  length–area energy transfer `pushforwardGood_modulus_le`;
* the **complementary** curves form the `g`-chain-rule exceptional subfamily of
  `Q.imageCurveFamily f`, of zero modulus by `IsQCAnalytic.chainRule_exceptional_modulus_zero`
  applied to the (analytic-quasiconformal) inverse `g` — this is the new inverse-is-QC ingredient
  that the upstream layer could not reach.

Removing the zero-modulus piece (`curveModulus_sdiff_modulus_zero`) and bounding the good part
by the energy transfer `pushforwardGood_modulus_le` gives `M(f(Q)) ≤ K · M(Q)`.

The one delicate sub-case — image curves stationary along the degeneracy image `f '' Nf` while
their `g`-preimages move through `Nf` — is handled by
`isQCGeometric_imageStationary_residual_modulus_zero`, whose Fuglede node closes via
`fugledeUpperGradient` applied to the analytic-quasiconformal inverse `g`
(`IsQCAnalytic.inverse_isQCAnalytic`): for `g`-good curves the upper-gradient bound forces
`g ∘ δ` to be stationary wherever `δ` is, so those curves carry no modulus. This is the
inverse-is-QC ingredient that the original upstream layer could not reach. -/
theorem isQCGeometric_of_isQCAnalytic {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    {b : BeltramiCoeff} (hb : b.normInf ≤ (K - 1) / (K + 1)) (hf : IsQCAnalytic f b) :
    IsQCGeometric f K := by
  classical
  -- The inverse homeomorphism `g = f⁻¹` and the two inversion identities.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hf.1.1.homeomorph f).symm_apply_apply z
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
  -- The inverse is itself analytic-quasiconformal.
  obtain ⟨b', hg_qc⟩ : ∃ b' : BeltramiCoeff, IsQCAnalytic g b' := hf.inverse_isQCAnalytic
  -- The `f`-degeneracy set `Nf` in the source, and its image `M = f '' Nf = {w | g w ∈ Nf}`
  -- in the target.  `M` is measurable and Lebesgue-null (planar Lusin-(N), `image_lusinN`).
  set Nf : Set ℂ := {z : ℂ | ¬ (DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det)} with hNf
  have hNfmeas : MeasurableSet Nf := by
    have hd : MeasurableSet {z : ℂ | DifferentiableAt ℝ f z} :=
      measurableSet_of_differentiableAt ℝ f
    have hdet : MeasurableSet {z : ℂ | 0 < (fderiv ℝ f z).det} :=
      measurableSet_lt measurable_const
        ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
    have hrw : Nf = ({z : ℂ | DifferentiableAt ℝ f z} ∩ {z : ℂ | 0 < (fderiv ℝ f z).det})ᶜ := by
      ext z; simp [hNf, Set.mem_compl_iff, not_and]
    rw [hrw]; exact (hd.inter hdet).compl
  have hNfnull : volume Nf = 0 := by
    rw [hNf, ← ae_iff]
    filter_upwards [hf.1.2, IsQCAnalytic.ae_differentiableAt hf] with z hz hzd
    exact ⟨hzd, hz⟩
  -- Assemble the geometric definition.
  refine ⟨hK, SensePreserving.of_orientationPreservingHomeo hf.1, fun Q => ?_⟩
  -- The genuine image family and its `g`-chain-rule exceptional ("bad") subfamily.
  set Δ : Set (ℝ → ℂ) := Q.imageCurveFamily f with hΔ
  set Δbad : Set (ℝ → ℂ) :=
    {δ ∈ Δ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (g ∘ δ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv δ t ≠ 0 → 0 < (fderiv ℝ g (δ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv δ t ≠ 0 →
          HasDerivAt (g ∘ δ) ((fderiv ℝ g (δ t)) (deriv δ t)) t)} with hΔbad
  -- The image-stationary subfamily: image curves `δ` whose source preimage `γ := g ∘ δ`
  -- meets `f`'s degeneracy set `Nf` with positive **`γ`-arc length** (the `Nf`-contact may be
  -- carried entirely by image-stationary points `deriv δ = 0`, so this is a finer condition
  -- than `δ` meeting `f '' Nf` with positive `δ`-arc length).
  set Δmeet : Set (ℝ → ℂ) :=
    {δ ∈ Δ | 1 ≤ arcLengthLineIntegral (Nf.indicator (fun _ => ∞)) (g ∘ δ)} with hΔmeet
  -- The combined exceptional ("bad") image family.
  set Δexc : Set (ℝ → ℂ) := Δbad ∪ Δmeet with hΔexc
  -- The members of `Δ` are continuous and absolutely continuous (by definition).
  have hΔcont : ∀ δ ∈ Δ, Continuous δ := fun δ hδ => hδ.1
  have hΔac : ∀ δ ∈ Δ, AbsolutelyContinuousOnInterval δ 0 1 := fun δ hδ => hδ.2.1
  -- (i)  The `g`-exceptional subfamily has zero modulus: it is the `g`-chain-rule exceptional
  -- family of the (analytic-quasiconformal) inverse `g`, swept over the AC family `Δ`.
  have hbad0 : curveModulus Δbad = 0 :=
    IsQCAnalytic.chainRule_exceptional_modulus_zero hg_qc Δ hΔcont hΔac
  -- (ii)  The image-stationary subfamily has zero modulus — the single genuine residual,
  -- isolated as `isQCGeometric_imageStationary_residual_modulus_zero`.
  have hmeet0 : curveModulus Δmeet = 0 :=
    isQCGeometric_imageStationary_residual_modulus_zero hf Δ hΔcont hΔac
  -- Hence the combined exceptional image family has zero modulus.
  have hexc0 : curveModulus Δexc = 0 := curveModulus_union_zero hbad0 hmeet0
  -- The non-exceptional good part embeds in `(f ∘ ·) '' (Q.curveFamily \ Γfbad)`, where
  -- `Γfbad` is the `f`-chain-rule exceptional subfamily of the source family.  A non-exceptional
  -- image curve `δ` has `γ := g ∘ δ ∈ Q.curveFamily`, is `f`-chain-rule **good** (its preimage
  -- `γ` meets `f`'s degeneracy set `Nf` negligibly in `γ`-arc length, so the chain rule for `f`
  -- along `γ` holds), and `δ = f ∘ γ`.
  set Γfbadprop : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hΓfbadprop
  have hgood_sub :
      Δ \ Δexc ⊆ (fun γ : ℝ → ℂ => f ∘ γ) '' (Q.curveFamily \ {γ ∈ Q.curveFamily | Γfbadprop γ}) := by
    rintro δ ⟨hδΔ, hδnotexc⟩
    -- `δ` is neither `g`-exceptional nor image-stationary.
    have hδnotbad : δ ∉ Δbad := fun h => hδnotexc (Or.inl h)
    have hδnotmeet : δ ∉ Δmeet := fun h => hδnotexc (Or.inr h)
    -- `g`-goodness of `δ` (membership in `Δ \ Δbad`).
    have hδgood : (∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (g ∘ δ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv δ t ≠ 0 → 0 < (fderiv ℝ g (δ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv δ t ≠ 0 →
          HasDerivAt (g ∘ δ) ((fderiv ℝ g (δ t)) (deriv δ t)) t := by
      by_contra hc; exact hδnotbad ⟨hδΔ, hc⟩
    obtain ⟨hgAC, _hgdet, _hgchain⟩ := hδgood
    have hδmemΔ : δ ∈ Δ := hδΔ
    obtain ⟨hδcont, hδac, hδ0, hδ1, hδimg⟩ := hδΔ
    have h01 : Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (zero_le_one)]
    set γ : ℝ → ℂ := g ∘ δ with hγ
    have hγcont : Continuous γ := hgcont.comp hδcont
    have hγac : AbsolutelyContinuousOnInterval γ 0 1 := hgAC 0 1 h01
    -- `δ ∉ Δmeet` ⟹ `γ = g ∘ δ` meets `Nf` negligibly in `γ`-arc length.
    have hmeet : ¬ 1 ≤ arcLengthLineIntegral (Nf.indicator (fun _ => (∞ : ℝ≥0∞))) γ := by
      intro hge; exact hδnotmeet ⟨hδmemΔ, hge⟩
    -- The `f`-chain-rule good clauses for `γ = g ∘ δ`.
    have hfgood : (∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
          HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t := by
      -- `f ∘ γ = δ` (since `f ∘ g = id`), which is AC by membership in `Δ`.
      have hfγeq : f ∘ γ = δ := by funext t; simp only [hγ, Function.comp_apply, hfg (δ t)]
      -- The `γ`-contact parameter footprint of `Nf` is Lebesgue-null on `[0,1]` (from `hmeet`).
      set B : Set ℝ := {t : ℝ | deriv γ t ≠ 0 ∧ γ t ∈ Nf} with hB
      have hBmeas : MeasurableSet B := by
        have hd : MeasurableSet {t : ℝ | deriv γ t ≠ 0} :=
          (measurableSet_singleton (0 : ℂ)).preimage (measurable_deriv γ) |>.compl
        have hpre : MeasurableSet {t : ℝ | γ t ∈ Nf} := hNfmeas.preimage hγcont.measurable
        have hrw : B = {t : ℝ | deriv γ t ≠ 0} ∩ {t : ℝ | γ t ∈ Nf} := by
          ext t; simp [hB, Set.mem_inter_iff]
        rw [hrw]; exact hd.inter hpre
      have hintegrand : ∀ t, (Nf.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
          (‖deriv γ t‖₊ : ℝ≥0∞) = B.indicator (fun _ => (∞ : ℝ≥0∞)) t := by
        intro t
        by_cases hd : deriv γ t = 0
        · have htB : t ∉ B := fun h => h.1 hd
          rw [Set.indicator_of_notMem htB]; simp [hd]
        · by_cases hγN : γ t ∈ Nf
          · have htB : t ∈ B := ⟨hd, hγN⟩
            have hnz : (‖deriv γ t‖₊ : ℝ≥0∞) ≠ 0 := by
              simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero]; exact hd
            rw [Set.indicator_of_mem hγN, Set.indicator_of_mem htB, ENNReal.top_mul hnz]
          · have htB : t ∉ B := fun h => hγN h.2
            rw [Set.indicator_of_notMem hγN, Set.indicator_of_notMem htB, zero_mul]
      have hLI : arcLengthLineIntegral (Nf.indicator (fun _ => (∞ : ℝ≥0∞))) γ
          = (∞ : ℝ≥0∞) * volume (B ∩ Set.Icc (0 : ℝ) 1) := by
        unfold arcLengthLineIntegral
        rw [show (fun t => (Nf.indicator (fun _ => (∞ : ℝ≥0∞)) (γ t)) *
            (‖deriv γ t‖₊ : ℝ≥0∞)) = B.indicator (fun _ => (∞ : ℝ≥0∞)) from funext hintegrand]
        rw [lintegral_indicator hBmeas, setLIntegral_const,
          Measure.restrict_apply hBmeas, Set.inter_comm]
      have hBnull : volume (B ∩ Set.Icc (0 : ℝ) 1) = 0 := by
        by_contra hpos
        apply hmeet; rw [hLI, ENNReal.top_mul hpos]; exact le_top
      -- a.e.-`t ∈ [0,1]`: `deriv γ t ≠ 0 → γ t ∉ Nf`, i.e. `f` differentiable with `0 < det`.
      have hγNnegl : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → (DifferentiableAt ℝ f (γ t) ∧ 0 < (fderiv ℝ f (γ t)).det) := by
        rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
        apply measure_mono_null _ hBnull
        intro t ht
        simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
        obtain ⟨hmem, hd, hnotgood⟩ := ht
        refine ⟨⟨hd, ?_⟩, hmem⟩
        simp only [hNf, Set.mem_setOf_eq]; exact hnotgood
      -- `γ` is differentiable a.e. on `[0,1]` (it is absolutely continuous).
      have hdiffγ : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          DifferentiableAt ℝ γ t := by
        rw [ae_restrict_iff' measurableSet_Icc]
        have hbv : BoundedVariationOn γ (Set.uIcc (0 : ℝ) 1) := hγac.boundedVariationOn
        filter_upwards [hbv.ae_differentiableAt_of_mem_uIcc] with t ht htmem
        exact ht (by rw [Set.uIcc_of_le (by norm_num)]; exact htmem)
      refine ⟨?_, ?_, ?_⟩
      · -- Clause 1: `f ∘ γ = δ` is AC on every subinterval of `[0,1]`.
        intro a c hac
        rw [hfγeq]
        exact hδac.mono_subinterval hac
      · -- Clause 2: a.e.-`t`, `deriv γ t ≠ 0 → 0 < det Df(γ t)`.
        filter_upwards [hγNnegl] with t hgoodt hγderiv
        exact (hgoodt hγderiv).2
      · -- Clause 3: a.e.-`t`, `deriv γ t ≠ 0 → HasDerivAt (f ∘ γ) (Df(γ t)·γ' t) t`.
        filter_upwards [hγNnegl, hdiffγ] with t hgoodt hdiffγt hγderiv
        have hfd : HasFDerivAt f (fderiv ℝ f (γ t)) (γ t) := (hgoodt hγderiv).1.hasFDerivAt
        have hγd : HasDerivAt γ (deriv γ t) t := hdiffγt.hasDerivAt
        exact hfd.comp_hasDerivAt t hγd
    -- Hence `γ ∈ Q.curveFamily` and `γ` is `f`-good, and `δ = f ∘ γ`.
    refine ⟨γ, ⟨⟨hγcont, hγac, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · obtain ⟨p, hp, hpeq⟩ := hδ0
      simp only [hγ, Function.comp_apply]; rw [← hpeq, hgf p]; exact hp
    · obtain ⟨p, hp, hpeq⟩ := hδ1
      simp only [hγ, Function.comp_apply]; rw [← hpeq, hgf p]; exact hp
    · intro t ht
      obtain ⟨p, hp, hpeq⟩ := hδimg t ht
      simp only [hγ, Function.comp_apply]; rw [← hpeq, hgf p]; exact hp
    · -- `γ ∉ {γ ∈ Q.curveFamily | Γfbadprop γ}`: `γ` is `f`-good.
      intro hmem; exact (not_not.mpr hfgood) hmem.2
    · funext t; simp only [hγ, Function.comp_apply, hfg (δ t)]
  -- Bound the good part by the clean pushforward energy transfer for the `f`-good source
  -- curves (`pushforwardGood_modulus_le`).
  have hQcont : ∀ γ ∈ Q.curveFamily, Continuous γ := fun γ hγ => hγ.1
  have hQac : ∀ γ ∈ Q.curveFamily, AbsolutelyContinuousOnInterval γ 0 1 := fun γ hγ => hγ.2.1
  have hpush := pushforwardGood_modulus_le hK hb hf Q.curveFamily hQcont hQac
  -- The pushforward set is defeq to `(f ∘ ·) '' (Q.curveFamily \ Γfbad)`.
  have hgood_le : curveModulus (Δ \ Δexc) ≤ ENNReal.ofReal K * Q.modulus := by
    refine le_trans (curveModulus_mono hgood_sub) ?_
    exact hpush
  -- Remove the zero-modulus exceptional part: `curveModulus (Δ \ Δexc) = curveModulus Δ`.
  have hexcsub : Δexc ⊆ Δ := by
    rw [hΔexc]; exact Set.union_subset (Set.sep_subset _ _) (Set.sep_subset _ _)
  have hsdiff : curveModulus (Δ \ Δexc) = curveModulus Δ :=
    curveModulus_sdiff_modulus_zero hexcsub hexc0
  rw [hΔ] at hsdiff ⊢
  rw [← hsdiff]; exact hgood_le

/-- **Geometric ⇒ analytic** (the hard direction). A `K`-quasiconformal map in the
geometric (modulus) sense is absolutely continuous on lines, hence lies in
`W^{1,2}_loc`, and satisfies the Beltrami equation with a coefficient of norm at
most `(K − 1)/(K + 1)`. The proof assembles the Gehring–Lehto stages of
`QC/GeometricToAnalytic.lean` (`exists_acl_weakGradient`, `ae_differentiableAt`,
`exists_beltrami`); these remain the open research-scale residual of Milestone 9.2. -/
theorem isQCAnalytic_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (hf : IsQCGeometric f K) :
    ∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧ IsQCAnalytic f b := by
  sorry

/-- **Equivalence of the analytic and geometric quasiconformal definitions.** For `1 ≤ K`, a
map admits an analytic-quasiconformal structure with Beltrami norm at most `(K − 1)/(K + 1)`
if and only if it is `K`-quasiconformal in the geometric (modulus) sense. -/
theorem qc_analytic_iff_geometric {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K) :
    (∃ b : BeltramiCoeff, b.normInf ≤ (K - 1) / (K + 1) ∧ IsQCAnalytic f b) ↔
      IsQCGeometric f K :=
  ⟨fun ⟨_, hb, hf⟩ => isQCGeometric_of_isQCAnalytic hK hb hf,
    isQCAnalytic_of_isQCGeometric hK⟩

end RiemannDynamics
