/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Extremal

/-!
# Symmetrization of marked candidates

A marked candidate is pinned on the closed upper half plane by its boundary transition, so
replacing its lower-half-plane behavior by the conjugate reflection of its upper half
produces another candidate for the same pair: the glued map is again quasiconformal (the
real line is removable), its Beltrami coefficient is the reflection-symmetric extension of
the upper coefficient, and the plane dilatation drops to the upper one. Applying this to
an extremal marked candidate yields a symmetric extremal representative whose maximal
dilatation is exactly the equivariant infimum — the normal form the Hamilton–Krushkal
necessity argument runs on.

* `isMarkedCandidate_congr_upper` — candidacy only reads the closed upper half plane.
* `exists_reflectGlue` — the conjugate-reflection glue of an upper-preserving
  quasiconformal map.
* `exists_symmetric_extremal` — the symmetric extremal marked candidate of a pair.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Candidacy reads only the closed upper half plane**: a map agreeing with a marked
candidate on `{0 ≤ im}` is a marked candidate for the same pair. -/
theorem isMarkedCandidate_congr_upper {x y : TeichRep Γ₀} {F F' : ℂ → ℂ}
    (hmc : IsMarkedCandidate x y F) (heq : ∀ z : ℂ, 0 ≤ z.im → F' z = F z) :
    IsMarkedCandidate x y F' := by
  obtain ⟨h1, h2, h3⟩ := hmc
  refine ⟨fun t => ?_, fun W hW => ?_, fun W' hW' => ?_⟩
  · rw [heq (y.w t) (le_of_eq (y.w_real t).symm)]
    exact h1 t
  · obtain ⟨W', hW', hc⟩ := h2 W hW
    refine ⟨W', hW', fun z hz => ?_⟩
    rw [heq (moebiusMap W z) (moebiusMap_im_pos W hz).le, heq z hz.le]
    exact hc z hz
  · obtain ⟨W, hW, hc⟩ := h3 W' hW'
    refine ⟨W, hW, fun z hz => ?_⟩
    rw [heq (moebiusMap W z) (moebiusMap_im_pos W hz).le, heq z hz.le]
    exact hc z hz

/-- **The conjugate-reflection glue**: a quasiconformal map preserving the open upper half
plane and the real line agrees on `{0 ≤ im}` with a quasiconformal map commuting with
conjugation, whose Beltrami coefficient is the reflection-symmetric extension of the upper
coefficient. -/
theorem exists_reflectGlue {F : ℂ → ℂ} {b : BeltramiCoeff} (hF : IsQCAnalytic F b)
    (hreal : ∀ t : ℝ, (F (t : ℂ)).im = 0)
    (hupper : ∀ z : ℂ, 0 < z.im → 0 < (F z).im) :
    ∃ (F' : ℂ → ℂ) (b' : BeltramiCoeff), IsQCAnalytic F' b' ∧
      (∀ z : ℂ, 0 ≤ z.im → F' z = F z) ∧
      (∀ z : ℂ, F' (starRingEnd ℂ z) = starRingEnd ℂ (F' z)) ∧
      b'.μ = symmExtension b.μ := by
  classical
  -- ===== The reflected companion map and its quasiconformal package. =====
  have hG : IsQCAnalytic (fun z => starRingEnd ℂ (F (starRingEnd ℂ z))) b.reflect :=
    isQCAnalytic_conj_conj hF
  set G : ℂ → ℂ := fun z => starRingEnd ℂ (F (starRingEnd ℂ z)) with hGdef
  have hGval : ∀ w : ℂ, G w = starRingEnd ℂ (F (starRingEnd ℂ w)) := fun _ => rfl
  obtain ⟨⟨hFhomeo, hFdet⟩, hFW12, hFbelt⟩ := hF
  obtain ⟨⟨hGhomeo, hGdet⟩, hGW12, hGbelt⟩ := hG
  have hFcont : Continuous F := hFhomeo.continuous
  have hFinj : Function.Injective F := hFhomeo.injective
  have hFsurj : Function.Surjective F := hFhomeo.bijective.surjective
  have hGcont : Continuous G := hGhomeo.continuous
  -- ===== Trichotomy: real points stay real, the halves stay in their halves. =====
  have himzero : ∀ z : ℂ, z.im = 0 → (F z).im = 0 := by
    intro z hz
    rw [eq_ofReal_of_im_eq_zero hz]
    exact hreal z.re
  have hFG : ∀ z : ℂ, z.im = 0 → F z = G z := by
    intro z hz
    have hconjz : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr hz
    rw [hGval, hconjz, Complex.conj_eq_iff_im.mpr (himzero z hz)]
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hVopen : IsOpen (F '' {z : ℂ | 0 < z.im}) := hFhomeo.isOpenMap _ hUopen
  have hWopen : IsOpen (F '' {z : ℂ | z.im < 0}) := hFhomeo.isOpenMap _ hLopen
  have hdisjVW : Disjoint (F '' {z : ℂ | 0 < z.im}) (F '' {z : ℂ | z.im < 0}) := by
    rw [Set.disjoint_left]
    rintro w ⟨z1, hz1, rfl⟩ ⟨z2, hz2, heq⟩
    have hz12 : z2 = z1 := hFinj heq
    rw [hz12] at hz2
    have h1 : 0 < z1.im := hz1
    have h2 : z1.im < 0 := hz2
    linarith
  have hVeq : F '' {z : ℂ | 0 < z.im} = {z : ℂ | 0 < z.im} := by
    have hVsub : F '' {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 < z.im} := by
      rintro w ⟨z, hz, rfl⟩
      exact hupper z hz
    refine Set.Subset.antisymm hVsub ?_
    have hcover : {z : ℂ | 0 < z.im} ⊆
        F '' {z : ℂ | 0 < z.im} ∪ F '' {z : ℂ | z.im < 0} := by
      intro w hw
      obtain ⟨z, rfl⟩ := hFsurj w
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · exact Or.inr ⟨z, hneg, rfl⟩
      · exact absurd (himzero z hzero) (ne_of_gt hw)
      · exact Or.inl ⟨z, hpos, rfl⟩
    have hpre : IsPreconnected {z : ℂ | 0 < z.im} :=
      (convex_halfSpace_im_gt 0).isPreconnected
    rcases hpre.subset_or_subset hVopen hWopen hdisjVW hcover with h | h
    · exact h
    · exfalso
      have hIim : (0 : ℝ) < Complex.I.im := by simp
      have hIV : F Complex.I ∈ F '' {z : ℂ | 0 < z.im} := ⟨Complex.I, hIim, rfl⟩
      have hIU : F Complex.I ∈ {z : ℂ | 0 < z.im} := hupper Complex.I hIim
      exact Set.disjoint_left.mp hdisjVW hIV (h hIU)
  have hlower : ∀ z : ℂ, z.im < 0 → (F z).im < 0 := by
    intro z hz
    have hne_upper : ¬0 < (F z).im := by
      intro hpos
      have h1 : F z ∈ F '' {z : ℂ | 0 < z.im} := by
        rw [hVeq]
        exact hpos
      exact Set.disjoint_left.mp hdisjVW h1 ⟨z, hz, rfl⟩
    have hne_zero : (F z).im ≠ 0 := by
      intro h0
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen (F z) ⟨z, hz, rfl⟩
      have hmem : F z + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ Metric.ball (F z) ε := by
        rw [Metric.mem_ball, Complex.dist_eq]
        have heq : F z + ((ε / 2 : ℝ) : ℂ) * Complex.I - F z
            = ((ε / 2 : ℝ) : ℂ) * Complex.I := by ring
        rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (half_pos hε)]
        linarith
      have hup : F z + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ {z : ℂ | 0 < z.im} := by
        have him : (F z + ((ε / 2 : ℝ) : ℂ) * Complex.I).im = ε / 2 := by
          simp [Complex.add_im, Complex.mul_im, h0]
        simp only [Set.mem_ofPred_eq, him]
        linarith
      have h1 : F z + ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ F '' {z : ℂ | 0 < z.im} := by
        rw [hVeq]
        exact hup
      exact Set.disjoint_left.mp hdisjVW h1 (hball hmem)
    rcases lt_trichotomy (F z).im 0 with h | h | h
    · exact h
    · exact absurd h hne_zero
    · exact absurd h hne_upper
  -- ===== The packaged inverse and its half-plane behavior. =====
  set W : ℂ ≃ₜ ℂ := IsHomeomorph.homeomorph F hFhomeo with hWdef
  set Finv : ℂ → ℂ := ⇑W.symm with hFinvdef
  have hWF : ∀ z : ℂ, W z = F z := IsHomeomorph.homeomorph_apply F hFhomeo
  have hFinvF : ∀ z : ℂ, Finv (F z) = z := by
    intro z
    change W.symm (F z) = z
    rw [← hWF]
    exact W.symm_apply_apply z
  have hFFinv : ∀ w : ℂ, F (Finv w) = w := by
    intro w
    change F (W.symm w) = w
    rw [← hWF]
    exact W.apply_symm_apply w
  have hFinv_pos : ∀ w : ℂ, 0 < w.im → 0 < (Finv w).im := by
    intro w hw
    rcases lt_trichotomy (Finv w).im 0 with h | h | h
    · have := hlower _ h
      rw [hFFinv] at this
      linarith
    · have := himzero _ h
      rw [hFFinv] at this
      linarith
    · exact h
  have hFinv_zero : ∀ w : ℂ, w.im = 0 → (Finv w).im = 0 := by
    intro w hw
    rcases lt_trichotomy (Finv w).im 0 with h | h | h
    · have := hlower _ h
      rw [hFFinv] at this
      linarith
    · exact h
    · have := hupper _ h
      rw [hFFinv] at this
      linarith
  have hFinv_neg : ∀ w : ℂ, w.im < 0 → (Finv w).im < 0 := by
    intro w hw
    rcases lt_trichotomy (Finv w).im 0 with h | h | h
    · exact h
    · have := himzero _ h
      rw [hFFinv] at this
      linarith
    · have := hupper _ h
      rw [hFFinv] at this
      linarith
  -- ===== The glued map and its inverse. =====
  set F' : ℂ → ℂ := fun z => if 0 ≤ z.im then F z else G z with hF'def
  set F'inv : ℂ → ℂ := fun w => if 0 ≤ w.im then Finv w
    else starRingEnd ℂ (Finv (starRingEnd ℂ w)) with hF'invdef
  have hF'cont : Continuous F' := by
    simp only [hF'def]
    exact Continuous.if_le hFcont hGcont continuous_const Complex.continuous_im
      (fun z hz => hFG z hz.symm)
  have hF'inv_cont : Continuous F'inv := by
    simp only [hF'invdef]
    refine Continuous.if_le W.symm.continuous
      (Complex.continuous_conj.comp (W.symm.continuous.comp Complex.continuous_conj))
      continuous_const Complex.continuous_im (fun w hw => ?_)
    have hconjw : starRingEnd ℂ w = w := Complex.conj_eq_iff_im.mpr hw.symm
    change Finv w = starRingEnd ℂ (Finv (starRingEnd ℂ w))
    rw [hconjw]
    exact (Complex.conj_eq_iff_im.mpr (hFinv_zero w hw.symm)).symm
  have hleft : Function.LeftInverse F'inv F' := by
    intro z
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · have hcim : 0 < (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have hFcim : 0 < (F (starRingEnd ℂ z)).im := hupper _ hcim
      have h1 : F' z = G z := by
        simp only [hF'def]
        rw [if_neg (not_le.mpr hneg)]
      have h3 : (G z).im < 0 := by
        rw [hGval, Complex.conj_im]
        linarith
      rw [h1]
      simp only [hF'invdef]
      rw [if_neg (not_le.mpr h3), hGval, Complex.conj_conj, hFinvF, Complex.conj_conj]
    · have h1 : F' z = F z := by
        simp only [hF'def]
        rw [if_pos (le_of_eq hzero.symm)]
      have h2 : (0 : ℝ) ≤ (F z).im := le_of_eq (himzero z hzero).symm
      rw [h1]
      simp only [hF'invdef]
      rw [if_pos h2]
      exact hFinvF z
    · have h1 : F' z = F z := by
        simp only [hF'def]
        rw [if_pos hpos.le]
      have h2 : (0 : ℝ) ≤ (F z).im := (hupper z hpos).le
      rw [h1]
      simp only [hF'invdef]
      rw [if_pos h2]
      exact hFinvF z
  have hright : Function.RightInverse F'inv F' := by
    intro w
    rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
    · have hcim : 0 < (starRingEnd ℂ w).im := by
        rw [Complex.conj_im]
        linarith
      have h3 : 0 < (Finv (starRingEnd ℂ w)).im := hFinv_pos _ hcim
      have h4 : F'inv w = starRingEnd ℂ (Finv (starRingEnd ℂ w)) := by
        simp only [hF'invdef]
        rw [if_neg (not_le.mpr hneg)]
      have h6 : ¬(0 : ℝ) ≤ (starRingEnd ℂ (Finv (starRingEnd ℂ w))).im := by
        rw [Complex.conj_im]
        linarith
      rw [h4]
      simp only [hF'def]
      rw [if_neg h6, hGval, Complex.conj_conj, hFFinv, Complex.conj_conj]
    · have h2 : (0 : ℝ) ≤ (Finv w).im := le_of_eq (hFinv_zero w hzero).symm
      have h4 : F'inv w = Finv w := by
        simp only [hF'invdef]
        rw [if_pos (le_of_eq hzero.symm)]
      rw [h4]
      simp only [hF'def]
      rw [if_pos h2]
      exact hFFinv w
    · have h2 : (0 : ℝ) ≤ (Finv w).im := (hFinv_pos w hpos).le
      have h4 : F'inv w = Finv w := by
        simp only [hF'invdef]
        rw [if_pos hpos.le]
      rw [h4]
      simp only [hF'def]
      rw [if_pos h2]
      exact hFFinv w
  have hF'homeo : IsHomeomorph F' :=
    Homeomorph.isHomeomorph (⟨⟨F', F'inv, hleft, hright⟩, hF'cont, hF'inv_cont⟩ : ℂ ≃ₜ ℂ)
  -- ===== The conjugation-commutation clause. =====
  have hF'conj : ∀ z : ℂ, F' (starRingEnd ℂ z) = starRingEnd ℂ (F' z) := by
    intro z
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · have h1 : (0 : ℝ) ≤ (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        linarith
      have h2 : ¬(0 : ℝ) ≤ z.im := not_le.mpr hneg
      simp only [hF'def]
      rw [if_pos h1, if_neg h2, hGval, Complex.conj_conj]
    · have hconjz : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr hzero
      rw [hconjz]
      have h1 : (0 : ℝ) ≤ z.im := le_of_eq hzero.symm
      simp only [hF'def]
      rw [if_pos h1]
      exact (Complex.conj_eq_iff_im.mpr (himzero z hzero)).symm
    · have h1 : ¬(0 : ℝ) ≤ (starRingEnd ℂ z).im := by
        rw [Complex.conj_im]
        push Not
        linarith
      have h2 : (0 : ℝ) ≤ z.im := hpos.le
      simp only [hF'def]
      rw [if_neg h1, if_pos h2, hGval, Complex.conj_conj]
  -- ===== Sobolev membership of the glued map, via absolute continuity on lines. =====
  obtain ⟨hFL2, gx, gy, hFgrad, hgxL2, hgyL2⟩ := hFW12
  obtain ⟨hGL2, Gx, Gy, hGgrad, hGxL2, hGyL2⟩ := hGW12
  obtain ⟨haclFx, haclFy⟩ :=
    acl_weakGradient_of_conditionNPlus hFcont gx gy hgxL2 hgyL2 hFgrad.1 hFgrad.2
  obtain ⟨haclGx, haclGy⟩ :=
    acl_weakGradient_of_conditionNPlus hGcont Gx Gy hGxL2 hGyL2 hGgrad.1 hGgrad.2
  set gx' : ℂ → ℂ := fun z => if 0 < z.im then gx z else Gx z with hgx'def
  set gy' : ℂ → ℂ := fun z => if 0 < z.im then gy z else Gy z with hgy'def
  have hUmeas : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  -- a piecewise combination of two locally square-integrable functions is again `L²_loc`
  have hpieceL2 : ∀ u v : ℂ → ℂ, MemLpLocOn u 2 Set.univ → MemLpLocOn v 2 Set.univ →
      MemLpLocOn (fun z => if 0 < z.im then u z else v z) 2 Set.univ := by
    intro u v hu hv K hKsub hK
    have huK := hu K hKsub hK
    have hvK := hv K hKsub hK
    have heq : (fun z => if 0 < z.im then u z else v z)
        = fun z => {z : ℂ | 0 < z.im}.indicator u z
            + {z : ℂ | 0 < z.im}ᶜ.indicator v z := by
      funext z
      by_cases h : 0 < z.im
      · rw [if_pos h, Set.indicator_of_mem (show z ∈ {z : ℂ | 0 < z.im} from h) u,
          Set.indicator_of_notMem (show z ∉ {z : ℂ | 0 < z.im}ᶜ by simpa using h) v,
          add_zero]
      · rw [if_neg h, Set.indicator_of_notMem (show z ∉ {z : ℂ | 0 < z.im} from h) u,
          Set.indicator_of_mem (show z ∈ {z : ℂ | 0 < z.im}ᶜ by simpa using h) v,
          zero_add]
    rw [heq]
    exact (huK.indicator hUmeas).add (hvK.indicator hUmeas.compl)
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict K) := hh K (Set.subset_univ _) hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hgx'L2 : MemLpLocOn gx' 2 Set.univ := hpieceL2 gx Gx hgxL2 hGxL2
  have hgy'L2 : MemLpLocOn gy' 2 Set.univ := hpieceL2 gy Gy hgyL2 hGyL2
  have hF'L2 : MemLpLocOn F' 2 Set.univ := by
    intro K _ hK
    have hfin : IsFiniteMeasure (volume.restrict K) := by
      constructor
      rw [Measure.restrict_apply_univ]
      exact hK.measure_lt_top
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'cont.continuousOn
    have hbound : ∀ᵐ z ∂(volume.restrict K), ‖F' z‖ ≤ C := by
      rw [ae_restrict_iff' hK.measurableSet]
      exact Filter.Eventually.of_forall hC
    exact (memLp_top_of_bound hF'cont.aestronglyMeasurable C hbound).mono_exponent le_top
  have hy0ae : ∀ᵐ y : ℝ, y ≠ 0 := by
    rw [ae_iff]
    have hset : {y : ℝ | ¬y ≠ 0} = {(0 : ℝ)} := by
      ext t
      simp
    rw [hset]
    exact measure_singleton 0
  -- absolute continuity on almost every horizontal line
  have haclx' : ACLHorizontal F' gx' := by
    filter_upwards [haclFx, haclGx, hy0ae] with y hyF hyG hy0
    rcases lt_or_gt_of_ne hy0 with hneg | hpos
    · have hfun : (fun x : ℝ => F' ⟨x, y⟩) = fun x : ℝ => G ⟨x, y⟩ := by
        funext u
        have h : ¬(0 : ℝ) ≤ (⟨u, y⟩ : ℂ).im := not_le.mpr hneg
        simp only [hF'def]
        rw [if_neg h]
      refine ⟨fun a b => ?_, ?_⟩
      · rw [hfun]
        exact hyG.1 a b
      · filter_upwards [hyG.2] with u hu
        have hval : gx' ⟨u, y⟩ = Gx ⟨u, y⟩ := by
          have h : ¬(0 : ℝ) < (⟨u, y⟩ : ℂ).im := not_lt.mpr hneg.le
          simp only [hgx'def]
          rw [if_neg h]
        rw [hfun, hval]
        exact hu
    · have hfun : (fun x : ℝ => F' ⟨x, y⟩) = fun x : ℝ => F ⟨x, y⟩ := by
        funext u
        have h : (0 : ℝ) ≤ (⟨u, y⟩ : ℂ).im := hpos.le
        simp only [hF'def]
        rw [if_pos h]
      refine ⟨fun a b => ?_, ?_⟩
      · rw [hfun]
        exact hyF.1 a b
      · filter_upwards [hyF.2] with u hu
        have hval : gx' ⟨u, y⟩ = gx ⟨u, y⟩ := by
          have h : (0 : ℝ) < (⟨u, y⟩ : ℂ).im := hpos
          simp only [hgx'def]
          rw [if_pos h]
        rw [hfun, hval]
        exact hu
  -- absolute continuity on almost every vertical line: glue across the real axis
  have hacly' : ACLVertical F' gy' := by
    filter_upwards [haclFy, haclGy] with x hxF hxG
    have hvalF : ∀ t : ℝ, 0 ≤ t → F' ⟨x, t⟩ = F ⟨x, t⟩ := by
      intro t ht
      have h : (0 : ℝ) ≤ (⟨x, t⟩ : ℂ).im := ht
      simp only [hF'def]
      rw [if_pos h]
    have hvalG : ∀ t : ℝ, t ≤ 0 → F' ⟨x, t⟩ = G ⟨x, t⟩ := by
      intro t ht
      rcases lt_or_eq_of_le ht with hlt | heq
      · have h : ¬(0 : ℝ) ≤ (⟨x, t⟩ : ℂ).im := not_le.mpr hlt
        simp only [hF'def]
        rw [if_neg h]
      · have h0 : ((⟨x, t⟩ : ℂ)).im = 0 := heq
        rw [hvalF t heq.ge]
        exact hFG _ h0
    have hkey : ∀ a b : ℝ, a ≤ b →
        AbsolutelyContinuousOnInterval (fun t : ℝ => F' ⟨x, t⟩) a b := by
      intro a b hab
      rcases le_total b 0 with hb0 | hb0
      · refine AbsolutelyContinuousOnInterval.congr (hxG.1 a b) ?_
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        exact (hvalG t (ht.2.trans hb0)).symm
      · rcases le_total 0 a with ha0 | ha0
        · refine AbsolutelyContinuousOnInterval.congr (hxF.1 a b) ?_
          intro t ht
          rw [Set.uIcc_of_le hab] at ht
          exact (hvalF t (ha0.trans ht.1)).symm
        · refine AbsolutelyContinuousOnInterval.union_of_split ha0 hb0 ?_ ?_
          · refine AbsolutelyContinuousOnInterval.congr (hxG.1 a 0) ?_
            intro t ht
            rw [Set.uIcc_of_le ha0] at ht
            exact (hvalG t ht.2).symm
          · refine AbsolutelyContinuousOnInterval.congr (hxF.1 0 b) ?_
            intro t ht
            rw [Set.uIcc_of_le hb0] at ht
            exact (hvalF t ht.1).symm
    refine ⟨fun a b => ?_, ?_⟩
    · rcases le_total a b with h | h
      · exact hkey a b h
      · exact (hkey b a h).symm
    · have hderivneg : ∀ᵐ t : ℝ, t < 0 →
          HasDerivAt (fun s : ℝ => F' ⟨x, s⟩) (gy' ⟨x, t⟩) t := by
        filter_upwards [hxG.2] with t htG htneg
        have hval : gy' ⟨x, t⟩ = Gy ⟨x, t⟩ := by
          have h : ¬(0 : ℝ) < (⟨x, t⟩ : ℂ).im := not_lt.mpr htneg.le
          simp only [hgy'def]
          rw [if_neg h]
        rw [hval]
        refine htG.congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds htneg] with s hs
        exact hvalG s (le_of_lt hs)
      have hderivpos : ∀ᵐ t : ℝ, 0 < t →
          HasDerivAt (fun s : ℝ => F' ⟨x, s⟩) (gy' ⟨x, t⟩) t := by
        filter_upwards [hxF.2] with t htF htpos
        have hval : gy' ⟨x, t⟩ = gy ⟨x, t⟩ := by
          have h : (0 : ℝ) < (⟨x, t⟩ : ℂ).im := htpos
          simp only [hgy'def]
          rw [if_pos h]
        rw [hval]
        refine htF.congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds htpos] with s hs
        exact hvalF s (le_of_lt hs)
      filter_upwards [hderivneg, hderivpos, hy0ae] with t h1 h2 ht0
      rcases lt_or_gt_of_ne ht0 with h | h
      · exact h1 h
      · exact h2 h
  have hW12' : MemW12loc F' :=
    memWklocP_one_of_acl hF'L2 hgx'L2 hgy'L2 hF'cont.locallyIntegrable
      (hLIofL2 hgx'L2) (hLIofL2 hgy'L2) haclx' hacly'
  -- ===== Orientation and the Beltrami equation, off the null real axis. =====
  have haxis : ∀ᵐ z : ℂ, z.im ≠ 0 := by
    rw [ae_iff]
    have hset : {a : ℂ | ¬a.im ≠ 0} = {z : ℂ | z.im = 0} := by
      ext a
      simp
    rw [hset]
    exact volume_imZero
  have hFnhds : ∀ z : ℂ, 0 < z.im → F' =ᶠ[nhds z] F := by
    intro z hz
    filter_upwards [hUopen.mem_nhds hz] with w hw
    simp only [hF'def]
    rw [if_pos (le_of_lt hw)]
  have hGnhds : ∀ z : ℂ, z.im < 0 → F' =ᶠ[nhds z] G := by
    intro z hz
    filter_upwards [hLopen.mem_nhds hz] with w hw
    simp only [hF'def]
    rw [if_neg (not_le.mpr hw)]
  have hdet' : ∀ᵐ z : ℂ, 0 < (fderiv ℝ F' z).det := by
    filter_upwards [hFdet, hGdet, haxis] with z hzF hzG hz0
    rcases lt_or_gt_of_ne hz0 with hneg | hpos
    · rw [(hGnhds z hneg).fderiv_eq]
      exact hzG
    · rw [(hFnhds z hpos).fderiv_eq]
      exact hzF
  -- ===== The symmetric-extension coefficient. =====
  have hb'bound : eLpNormEssSup (symmExtension b.μ) volume < 1 := by
    refine symmExtension_bound (lt_of_le_of_lt ?_ b.bound)
    exact eLpNormEssSup_mono_measure _
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  set b' : BeltramiCoeff :=
    ⟨symmExtension b.μ, symmExtension_measurable b.measurable, hb'bound⟩ with hb'def
  have hbelt' : ∀ᵐ z : ℂ, dzbar F' z = b'.μ z * dz F' z := by
    filter_upwards [hFbelt, hGbelt, haxis] with z hzF hzG hz0
    rcases lt_or_gt_of_ne hz0 with hneg | hpos
    · have hfd : fderiv ℝ F' z = fderiv ℝ G z := (hGnhds z hneg).fderiv_eq
      have h1 : dzbar F' z = dzbar G z := by
        simp only [dzbar, hfd]
      have h2 : dz F' z = dz G z := by
        simp only [dz, hfd]
      have h3 : b'.μ z = b.reflect.μ z := by
        change symmExtension b.μ z = b.reflect.μ z
        simp only [symmExtension]
        rw [if_neg (not_lt.mpr hneg.le)]
        rfl
      rw [h1, h2, h3]
      exact hzG
    · have hfd : fderiv ℝ F' z = fderiv ℝ F z := (hFnhds z hpos).fderiv_eq
      have h1 : dzbar F' z = dzbar F z := by
        simp only [dzbar, hfd]
      have h2 : dz F' z = dz F z := by
        simp only [dz, hfd]
      have h3 : b'.μ z = b.μ z := by
        change symmExtension b.μ z = b.μ z
        simp only [symmExtension]
        rw [if_pos hpos]
      rw [h1, h2, h3]
      exact hzF
  -- ===== Assembly. =====
  refine ⟨F', b', ⟨⟨hF'homeo, hdet'⟩, hW12', hbelt'⟩, fun z hz => ?_, hF'conj, rfl⟩
  simp only [hF'def]
  rw [if_pos hz]

/-- **The symmetric extremal marked candidate**: every pair over a cocompact free Fuchsian
base admits a marked candidate commuting with conjugation whose Beltrami coefficient is
reflection-symmetric and whose maximal dilatation is exactly the equivariant infimum. -/
theorem exists_symmetric_extremal (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x y : TeichRep Γ₀) :
    ∃ (F : ℂ → ℂ) (b : BeltramiCoeff), IsMarkedCandidate x y F ∧ IsQCAnalytic F b ∧
      b.μ = symmExtension b.μ ∧
      (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) ∧
      b.K = sInf (gDilatationSet x y) := by
  classical
  set K₀ : ℝ := sInf (gDilatationSet x y) with hK₀def
  obtain ⟨F₀, hgeo₀, hmc₀⟩ := exists_extremal_marked hΓ₀ hfree hcc x y
  have h1K₀ : 1 ≤ K₀ := one_le_of_mem_gDilatationSet ⟨F₀, hgeo₀, hmc₀⟩
  obtain ⟨b₀, hb₀n, hqa₀⟩ := isQCAnalytic_of_isQCGeometric h1K₀ hgeo₀
  have hupper : ∀ z : ℂ, 0 < z.im → 0 < (F₀ z).im :=
    isMarkedCandidate_mapsTo_upper hgeo₀ hmc₀.1
  have hreal : ∀ t : ℝ, (F₀ (t : ℂ)).im = 0 := by
    intro t
    obtain ⟨s, hs⟩ := y.boundary_surjective t
    have hws : y.w (s : ℂ) = (t : ℂ) := by rw [y.w_ofReal s, hs]
    rw [← hws, hmc₀.1 s]
    exact x.w_real s
  obtain ⟨F', b', hqa', hagree, hconj, hb'μ⟩ := exists_reflectGlue hqa₀ hreal hupper
  have hmc' : IsMarkedCandidate x y F' := isMarkedCandidate_congr_upper hmc₀ hagree
  -- the essential supremum of the glued coefficient is at most that of `b₀`
  set N₀ : ℝ≥0∞ := eLpNormEssSup b₀.μ volume with hN₀def
  have hreflN : eLpNormEssSup b₀.reflect.μ volume = N₀ := by
    have h := b₀.normInf_reflect
    simp only [BeltramiCoeff.normInf] at h
    exact (ENNReal.toReal_eq_toReal_iff' (ne_top_of_lt b₀.reflect.bound)
      (ne_top_of_lt b₀.bound)).mp h
  have hess' : eLpNormEssSup b'.μ volume ≤ N₀ := by
    have h2 : ∀ᵐ z : ℂ, ‖b₀.reflect.μ z‖ₑ ≤ N₀ := by
      have h := enorm_ae_le_eLpNormEssSup b₀.reflect.μ volume
      rw [hreflN] at h
      exact h
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards [enorm_ae_le_eLpNormEssSup b₀.μ volume, h2] with z hz1 hz2
    rw [hb'μ]
    by_cases h : 0 < z.im
    · simp only [symmExtension]
      rw [if_pos h]
      exact hz1
    · simp only [symmExtension]
      rw [if_neg h]
      exact hz2
  have hn' : b'.normInf ≤ b₀.normInf :=
    ENNReal.toReal_mono (ne_top_of_lt b₀.bound) hess'
  -- adjust the coefficient on the null real line to make symmetry exact
  set μt : ℂ → ℂ := fun z => if z.im = 0 then 0 else symmExtension b₀.μ z with hμtdef
  have hset0 : MeasurableSet {z : ℂ | z.im = 0} :=
    Complex.measurable_im (measurableSet_singleton 0)
  have hμt_meas : Measurable μt :=
    Measurable.ite hset0 measurable_const (symmExtension_measurable b₀.measurable)
  have hμt_ae : μt =ᵐ[volume] b'.μ := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ volume_imZero
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    by_contra him
    apply hz
    rw [hb'μ, hμtdef]
    simp only [if_neg him]
  have hbt : eLpNormEssSup μt volume < 1 := by
    rw [eLpNormEssSup_congr_ae hμt_ae]
    exact b'.bound
  set bt : BeltramiCoeff := ⟨μt, hμt_meas, hbt⟩ with hbtdef
  have hqat : IsQCAnalytic F' bt := hqa'.congr_coeff hμt_ae.symm
  -- exact reflection symmetry of the adjusted coefficient
  have hsymt : bt.μ = symmExtension bt.μ := by
    funext z
    change μt z = symmExtension μt z
    by_cases him : z.im = 0
    · have hconjz : starRingEnd ℂ z = z := Complex.conj_eq_iff_im.mpr him
      have hnlt : ¬0 < z.im := by rw [him]; exact lt_irrefl 0
      have hL : μt z = 0 := by simp only [hμtdef]; rw [if_pos him]
      have hR : symmExtension μt z = 0 := by
        simp only [symmExtension]
        rw [if_neg hnlt, hconjz, hL, map_zero]
      rw [hL, hR]
    · by_cases hpos : 0 < z.im
      · simp only [symmExtension]
        rw [if_pos hpos]
      · have hneg : z.im < 0 := lt_of_le_of_ne (not_lt.mp hpos) him
        have hconjim : 0 < (starRingEnd ℂ z).im := by
          rw [Complex.conj_im]
          linarith
        have hne : ¬(starRingEnd ℂ z).im = 0 := ne_of_gt hconjim
        have h1 : μt (starRingEnd ℂ z) = b₀.μ (starRingEnd ℂ z) := by
          simp only [hμtdef, symmExtension]
          rw [if_neg hne, if_pos hconjim]
        have hL : μt z = starRingEnd ℂ (b₀.μ (starRingEnd ℂ z)) := by
          simp only [hμtdef, symmExtension]
          rw [if_neg him, if_neg hpos]
        have hR : symmExtension μt z = starRingEnd ℂ (μt (starRingEnd ℂ z)) := by
          simp only [symmExtension]
          rw [if_neg hpos]
        rw [hL, hR, h1]
  -- the maximal dilatation of the adjusted coefficient is the infimum
  have hntb : bt.normInf = b'.normInf := by
    simp only [BeltramiCoeff.normInf]
    rw [eLpNormEssSup_congr_ae hμt_ae]
  have hnle : bt.normInf ≤ (K₀ - 1) / (K₀ + 1) := by
    rw [hntb]
    exact hn'.trans hb₀n
  have hn0 : 0 ≤ bt.normInf := bt.normInf_nonneg
  have hn1 : bt.normInf < 1 := bt.normInf_lt_one
  have hKle : bt.K ≤ K₀ := by
    have hK₀pos : (0 : ℝ) < K₀ + 1 := by linarith
    have hmul : bt.normInf * (K₀ + 1) ≤ K₀ - 1 := by
      rw [← le_div_iff₀ hK₀pos]
      exact hnle
    rw [BeltramiCoeff.K, div_le_iff₀ (by linarith)]
    nlinarith [hmul]
  have hKge : K₀ ≤ bt.K := by
    have hKmem : bt.K ∈ gDilatationSet x y := ⟨F', hqat.isQCGeometric_K, hmc'⟩
    rw [hK₀def]
    exact csInf_le (bddBelow_gDilatationSet x y) hKmem
  exact ⟨F', bt, hmc', hqat, hsymt, hconj, le_antisymm hKle hKge⟩

end RiemannDynamics
