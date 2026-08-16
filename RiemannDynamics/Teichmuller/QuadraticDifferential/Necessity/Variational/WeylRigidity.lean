/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Variational.Schwarzian
import RiemannDynamics.Teichmuller.QuadraticDifferential.Necessity.Symmetrize

/-!
# Weyl rigidity of zero-extension solutions

A Beltrami coefficient supported in the closed upper half plane has its normalized
solution conformal on the open lower half plane, where the Schwarzian derivative reads
the deformation. A solution whose Schwarzian vanishes on the lower half plane is the
identity there, and therefore commutes with every real Möbius map whose coefficient law
it inherits.

* `differentiableOn_of_beltrami_ae_zero` — conformality where the coefficient vanishes.
* `eq_id_on_lower_of_schwarzian_eq_zero` — vanishing Schwarzian forces the identity.
* `moebiusMap_comm_of_eq_id_lower` — identity below plus invariance above forces
  commutation with the group.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Conformality off the support**: a quasiconformal map whose coefficient vanishes
almost everywhere on an open set is holomorphic there. -/
theorem differentiableOn_of_beltrami_ae_zero {w : ℂ → ℂ} {b : BeltramiCoeff}
    (hw : IsQCAnalytic w b) {U : Set ℂ} (hU : IsOpen U)
    (hb : ∀ᵐ z ∂(volume.restrict U), b.μ z = 0) :
    DifferentiableOn ℂ w U := by
  have hwcont : Continuous w := hw.1.1.continuous
  have hwloc : LocallyIntegrable w := hwcont.locallyIntegrable
  have hdiff : ∀ᵐ z, DifferentiableAt ℝ w z := hw.ae_differentiableAt
  obtain ⟨_hLp, gx, gy, ⟨hwgx, hwgy⟩, hmgx, hmgy⟩ := hw.2.1
  have hLpgx : MemLpLocOn gx 2 Set.univ := hmgx
  have hLpgy : MemLpLocOn gy 2 Set.univ := hmgy
  -- `L²_loc ⟹ L¹_loc ⟹ LocallyIntegrable`.
  have memLpLoc_to_loc : ∀ {g : ℂ → ℂ}, MemLpLocOn g 2 Set.univ →
      LocallyIntegrable g := by
    intro g hg
    rw [← locallyIntegrableOn_univ, locallyIntegrableOn_univ, locallyIntegrable_iff]
    intro k hk
    have : IsFiniteMeasure (volume.restrict k) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
    have hmem1 : MemLp g 1 (volume.restrict k) :=
      (hg k (Set.subset_univ _) hk).mono_exponent (by norm_num)
    exact memLp_one_iff_integrable.mp hmem1
  have hgxLI : LocallyIntegrable gx := memLpLoc_to_loc hLpgx
  have hgyLI : LocallyIntegrable gy := memLpLoc_to_loc hLpgy
  -- a.e.: the pointwise partials agree with the weak partials.
  have haex : ∀ᵐ z, (fderiv ℝ w z) (1 : ℂ) = gx z :=
    fderiv_ae_eq_weakDirDeriv hwgx (locallyIntegrableOn_univ.mpr hgxLI) hdiff
      (Or.inl rfl) hwloc
  have haey : ∀ᵐ z, (fderiv ℝ w z) Complex.I = gy z :=
    fderiv_ae_eq_weakDirDeriv hwgy (locallyIntegrableOn_univ.mpr hgyLI) hdiff
      (Or.inr rfl) hwloc
  -- the coefficient vanishes a.e. on `U`, so the `∂̄`-combination vanishes a.e. on `U`.
  have hbU : ∀ᵐ z, z ∈ U → b.μ z = 0 := (ae_restrict_iff' hU.measurableSet).mp hb
  have hcomb : ∀ᵐ z, z ∈ U → gx z + Complex.I * gy z = 0 := by
    filter_upwards [hw.2.2, hbU, haex, haey] with z hbel hbz hx hy hzU
    have h0 : dzbar w z = 0 := by rw [hbel, hbz hzU, zero_mul]
    have hval : dzbar w z = (1 / 2 : ℂ) * (gx z + Complex.I * gy z) := by
      rw [dzbar, hx, hy]
    rw [hval] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (by norm_num)
    · exact h
  exact weyl_lemma_on hU hwcont.continuousOn
    ⟨hwgx.mono (Set.subset_univ U), hwgy.mono (Set.subset_univ U)⟩
    (hgxLI.locallyIntegrableOn U) (hgyLI.locallyIntegrableOn U) hcomb

/-- **Identity from vanishing Schwarzian**: a normalized solution of an upper-supported
coefficient whose Schwarzian vanishes on the lower half plane is the identity on the
closed lower half plane. -/
theorem eq_id_on_lower_of_schwarzian_eq_zero {w : ℂ → ℂ} {b : BeltramiCoeff}
    (hw : IsQCAnalytic w b) (hb : ∀ z : ℂ, z.im ≤ 0 → b.μ z = 0)
    (h0 : w 0 = 0) (h1 : w 1 = 1)
    (hS : ∀ z : ℂ, z.im < 0 → schwarzian w z = 0) :
    ∀ z : ℂ, z.im ≤ 0 → w z = z := by
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  -- the coefficient vanishes a.e. on the open lower half plane, so `w` is holomorphic there
  have hbae : ∀ᵐ z ∂(volume.restrict {z : ℂ | z.im < 0}), b.μ z = 0 :=
    (ae_restrict_iff' hLopen.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => hb z (le_of_lt hz))
  have hol : DifferentiableOn ℂ w {z : ℂ | z.im < 0} :=
    differentiableOn_of_beltrami_ae_zero hw hLopen hbae
  have hinj : Set.InjOn w {z : ℂ | z.im < 0} := fun x _ y _ h => hw.injective h
  -- rigidity of the vanishing Schwarzian: `w` is a single ratio on the lower half plane
  obtain ⟨a, p, c, d, hdet, hratio⟩ :=
    exists_ratio_of_schwarzian_eq_zero hLopen ((convex_halfSpace_im_lt 0).isPreconnected)
      ⟨-Complex.I, by simp⟩ hol
      (fun z hz => deriv_ne_zero_of_injOn hLopen hol hinj hz) (fun z hz => hS z hz)
  -- the vertical test ray
  have humem : ∀ n : ℕ, -((n : ℂ) + 1) * Complex.I ∈ {z : ℂ | z.im < 0} := by
    intro n
    have him : (-((n : ℂ) + 1) * Complex.I).im = -((n : ℝ) + 1) := by
      simp [Complex.mul_im]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [Set.mem_ofPred_eq, him]
    linarith
  have hnorm_u : ∀ n : ℕ, ‖-((n : ℂ) + 1) * Complex.I‖ = (n : ℝ) + 1 := by
    intro n
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    push_cast
    ring
  -- properness of the plane homeomorphism `w` forces `c = 0`
  have hc0 : c = 0 := by
    by_contra hc
    set u : ℕ → ℂ := fun n => -((n : ℂ) + 1) * Complex.I with hu
    -- the ratio value along the ray, in pole-free form
    have hdecomp : ∀ n : ℕ, w (u n) = a / c + (p - a * d / c) * (c * u n + d)⁻¹ := by
      intro n
      rw [(hratio (u n) (humem n)).2]
      have hden := (hratio (u n) (humem n)).1
      rw [div_eq_iff hden, add_mul, mul_assoc, inv_mul_cancel₀ hden, mul_one]
      field_simp [hc]
      ring
    -- the denominator norm tends to infinity along the ray
    have hnormden : Filter.Tendsto (fun n : ℕ => ‖c * u n + d‖) Filter.atTop Filter.atTop := by
      have hlow : ∀ n : ℕ, ‖c‖ * ((n : ℝ) + 1) - ‖d‖ ≤ ‖c * u n + d‖ := by
        intro n
        have h1 : ‖c * u n‖ ≤ ‖c * u n + d‖ + ‖d‖ := by
          calc ‖c * u n‖ = ‖c * u n + d - d‖ := by ring_nf
            _ ≤ ‖c * u n + d‖ + ‖d‖ := norm_sub_le _ _
        have h2 : ‖c * u n‖ = ‖c‖ * ((n : ℝ) + 1) := by rw [norm_mul, hnorm_u n]
        linarith
      have hbase : Filter.Tendsto (fun n : ℕ => ‖c‖ * ((n : ℝ) + 1) - ‖d‖)
          Filter.atTop Filter.atTop := by
        have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        have h2 := h1.const_mul_atTop (norm_pos_iff.mpr hc)
        simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-‖d‖) h2
      exact Filter.tendsto_atTop_mono hlow hbase
    -- hence the inverses tend to zero and the ratio values converge
    have hinvzero : Filter.Tendsto (fun n : ℕ => (c * u n + d)⁻¹) Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa [norm_inv] using! hnormden.inv_tendsto_atTop
    have hlim : Filter.Tendsto (fun n : ℕ => w (u n)) Filter.atTop (nhds (a / c)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => a / c + (p - a * d / c) * (c * u n + d)⁻¹)
          Filter.atTop (nhds (a / c + (p - a * d / c) * 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.mul hinvzero)
      rw [mul_zero, add_zero] at h1
      exact h1.congr fun n => (hdecomp n).symm
    -- but the preimage of a compact ball under the homeomorphism is bounded
    have hK : IsCompact ((IsHomeomorph.homeomorph w hw.1.1).symm ''
        Metric.closedBall (a / c) 1) :=
      (isCompact_closedBall _ _).image (IsHomeomorph.homeomorph w hw.1.1).symm.continuous
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    have hev : ∀ᶠ n : ℕ in Filter.atTop, w (u n) ∈ Metric.closedBall (a / c) 1 :=
      hlim.eventually_mem (Metric.closedBall_mem_nhds _ one_pos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hmem := hN (max N (Nat.ceil R)) (le_max_left _ _)
    have humem2 : u (max N (Nat.ceil R)) ∈ (IsHomeomorph.homeomorph w hw.1.1).symm ''
        Metric.closedBall (a / c) 1 := by
      refine ⟨w (u (max N (Nat.ceil R))), hmem, ?_⟩
      rw [← IsHomeomorph.homeomorph_apply w hw.1.1, Homeomorph.symm_apply_apply]
    have hle := hR humem2
    rw [Metric.mem_closedBall, dist_zero_right, hnorm_u] at hle
    have hceil : R ≤ ((max N (Nat.ceil R) : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil R) (by exact_mod_cast le_max_right N (Nat.ceil R))
    linarith
  -- with `c = 0` the ratio is affine and extends by continuity to the closed half plane
  have hdne : d ≠ 0 := fun h => hdet (by rw [hc0, h]; ring)
  have hEq : Set.EqOn w (fun z => (a * z + p) / d) {z : ℂ | z.im < 0} := by
    intro z hz
    have h := (hratio z hz).2
    rwa [hc0, zero_mul, zero_add] at h
  have hcontg : Continuous fun z : ℂ => (a * z + p) / d :=
    ((continuous_const.mul continuous_id).add continuous_const).div_const d
  have hclose : Set.EqOn w (fun z => (a * z + p) / d) {z : ℂ | z.im ≤ 0} := by
    have h := hEq.closure hw.1.1.continuous hcontg
    rwa [Complex.closure_setOfPred_im_lt] at h
  -- normalization pins the affine map to the identity
  have hp0 : p = 0 := by
    have h := hclose (show (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)
    rw [h0] at h
    have h' : p / d = 0 := by simpa using h.symm
    rcases div_eq_zero_iff.mp h' with h'' | h''
    · exact h''
    · exact absurd h'' hdne
  have had : a = d := by
    have h := hclose (show (1 : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)
    rw [h1] at h
    have h' : (a + p) / d = 1 := by simpa using h.symm
    rw [hp0, add_zero] at h'
    exact (div_eq_one_iff_eq hdne).mp h'
  intro z hz
  have h := hclose hz
  simp only [hp0, had, add_zero] at h
  rw [h, mul_comm d z, mul_div_assoc, div_self hdne, mul_one]

/-- **Group commutation from boundary triviality**: a normalized solution of an
upper-supported coefficient obeying the invariance law of `Γ` on the upper half plane
and equal to the identity on the closed lower half plane commutes with every Möbius map
of `Γ` off its pole. -/
theorem moebiusMap_comm_of_eq_id_lower {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {w : ℂ → ℂ} {b : BeltramiCoeff} (hw : IsQCAnalytic w b)
    (hb : ∀ z : ℂ, z.im ≤ 0 → b.μ z = 0)
    (hinv : ∀ W ∈ Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      b.μ (moebiusMap W z) * (moebiusDenom W z) ^ 2
        = b.μ z * (starRingEnd ℂ (moebiusDenom W z)) ^ 2)
    (hid : ∀ z : ℂ, z.im ≤ 0 → w z = z) :
    ∀ γ ∈ Γ, ∀ z : ℂ, moebiusDenom γ z ≠ 0 →
      w (moebiusMap γ z) = moebiusMap γ (w z) := by
  -- the support hypothesis is subsumed: the identity below already forces the
  -- coefficient to vanish there, and the reflection glue does not consult it
  have _ := hb
  -- `w` fixes the real line pointwise and preserves the open upper half plane
  have hreal : ∀ t : ℝ, (w (t : ℂ)).im = 0 := by
    intro t
    rw [hid (t : ℂ) (le_of_eq (Complex.ofReal_im t))]
    exact Complex.ofReal_im t
  have hupper : ∀ z : ℂ, 0 < z.im → 0 < (w z).im := by
    intro z hz
    by_contra hle
    push Not at hle
    have h2 : w z = z := hw.injective (hid (w z) hle)
    rw [h2] at hle
    linarith
  -- the conjugate-reflection glue: a symmetric solution agreeing with `w` above
  obtain ⟨F, bF, hFqc, hagree, hsym, hbF⟩ := exists_reflectGlue hw hreal hupper
  have hF0 : F 0 = 0 := by
    rw [hagree 0 (le_of_eq Complex.zero_im.symm)]
    exact hid 0 (le_of_eq Complex.zero_im)
  have hF1 : F 1 = 1 := by
    rw [hagree 1 (le_of_eq Complex.one_im.symm)]
    exact hid 1 (le_of_eq Complex.one_im)
  intro γ hγ
  -- the glued coefficient obeys the invariance law globally
  have hlaw : ∀ᵐ z : ℂ, bF.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = bF.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
    rw [hbF]
    exact symmExtension_invariant Γ hinv γ hγ
  obtain ⟨W, hWeq⟩ := exists_sl2_equivariant hFqc hF0 hF1 hsym γ hlaw
  -- a real Möbius map has at most one real pole
  have huniq : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s t : ℝ),
      moebiusDenom V (s : ℂ) = 0 → moebiusDenom V (t : ℂ) = 0 → s = t := by
    intro V s t hs ht
    have hs' : (V 1 0 : ℂ) * (s : ℂ) + (V 1 1 : ℂ) = 0 := hs
    have ht' : (V 1 0 : ℂ) * (t : ℂ) + (V 1 1 : ℂ) = 0 := ht
    have hfac : (V 1 0 : ℂ) * ((s : ℂ) - (t : ℂ)) = 0 := by linear_combination hs' - ht'
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso
      have hc0 : V 1 0 = 0 := by exact_mod_cast h
      have h11 : (V 1 1 : ℂ) = 0 := by rw [h, zero_mul, zero_add] at hs'; exact hs'
      have h11' : V 1 1 = 0 := by exact_mod_cast h11
      have hdet : V 0 0 * V 1 1 - V 0 1 * V 1 0 = 1 := by
        have hD := Matrix.SpecialLinearGroup.det_coe V
        rwa [Matrix.det_fin_two] at hD
      rw [hc0, h11'] at hdet
      norm_num at hdet
    · have hst : (s : ℂ) = (t : ℂ) := sub_eq_zero.mp h
      exact_mod_cast hst
  -- each of the two matrices has at most one real pole
  have hpoles : ∀ V : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ q : ℝ,
      ∀ t : ℝ, moebiusDenom V (t : ℂ) = 0 → t = q := by
    intro V
    by_cases hex : ∃ t : ℝ, moebiusDenom V (t : ℂ) = 0
    · obtain ⟨q, hq⟩ := hex
      exact ⟨q, fun t ht => huniq V t q ht hq⟩
    · exact ⟨0, fun t ht => absurd ⟨t, ht⟩ hex⟩
  obtain ⟨qγ, hqγ⟩ := hpoles γ
  obtain ⟨qW, hqW⟩ := hpoles W
  set T : ℝ := |qγ| + |qW| + 1 with hT
  -- large real points avoid both poles
  have hgood : ∀ s : ℝ, T ≤ s →
      moebiusDenom γ (s : ℂ) ≠ 0 ∧ moebiusDenom W (s : ℂ) ≠ 0 := by
    intro s hs
    rw [hT] at hs
    have h1 : qγ ≤ |qγ| := le_abs_self qγ
    have h2 : qW ≤ |qW| := le_abs_self qW
    have h3 : (0 : ℝ) ≤ |qγ| := abs_nonneg qγ
    have h4 : (0 : ℝ) ≤ |qW| := abs_nonneg qW
    constructor
    · intro h
      have he := hqγ s h
      rw [he] at hs
      linarith
    · intro h
      have he := hqW s h
      rw [he] at hs
      linarith
  -- at large real points the equivariance identity reads `γ = W` on values
  have hpin : ∀ s : ℝ, T ≤ s → moebiusMap γ (s : ℂ) = moebiusMap W (s : ℂ) := by
    intro s hs
    obtain ⟨hdγ, _⟩ := hgood s hs
    have h1 := hWeq (s : ℂ) hdγ
    have hims : ((s : ℝ) : ℂ).im = 0 := Complex.ofReal_im s
    have h2 : F (s : ℂ) = (s : ℂ) := by
      rw [hagree _ (le_of_eq hims.symm)]
      exact hid _ (le_of_eq hims)
    have him2 : (moebiusMap γ (s : ℂ)).im = 0 := moebiusMap_im_eq_zero γ hims hdγ
    have h3 : F (moebiusMap γ (s : ℂ)) = moebiusMap γ (s : ℂ) := by
      rw [hagree _ (le_of_eq him2.symm)]
      exact hid _ (le_of_eq him2)
    rw [h3, h2] at h1
    exact h1
  -- three distinct such points pin the matrix up to sign, hence the map exactly
  have hne12 : ((T : ℝ) : ℂ) ≠ ((T + 1 : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    linarith
  have hne13 : ((T : ℝ) : ℂ) ≠ ((T + 2 : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    linarith
  have hne23 : ((T + 1 : ℝ) : ℂ) ≠ ((T + 2 : ℝ) : ℂ) := by
    rw [Ne, Complex.ofReal_inj]
    intro h
    linarith
  have hVden : ∀ ζ ∈ ({((T : ℝ) : ℂ), ((T + 1 : ℝ) : ℂ), ((T + 2 : ℝ) : ℂ)} : Set ℂ),
      moebiusDenom γ ζ ≠ 0 := by
    intro ζ hζ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
    rcases hζ with rfl | rfl | rfl
    · exact (hgood T le_rfl).1
    · exact (hgood (T + 1) (by linarith)).1
    · exact (hgood (T + 2) (by linarith)).1
  have hWden : ∀ ζ ∈ ({((T : ℝ) : ℂ), ((T + 1 : ℝ) : ℂ), ((T + 2 : ℝ) : ℂ)} : Set ℂ),
      moebiusDenom W ζ ≠ 0 := by
    intro ζ hζ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
    rcases hζ with rfl | rfl | rfl
    · exact (hgood T le_rfl).2
    · exact (hgood (T + 1) (by linarith)).2
    · exact (hgood (T + 2) (by linarith)).2
  have hpts : ∀ ζ ∈ ({((T : ℝ) : ℂ), ((T + 1 : ℝ) : ℂ), ((T + 2 : ℝ) : ℂ)} : Set ℂ),
      moebiusMap γ ζ = moebiusMap W ζ := by
    intro ζ hζ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hζ
    rcases hζ with rfl | rfl | rfl
    · exact hpin T le_rfl
    · exact hpin (T + 1) (by linarith)
    · exact hpin (T + 2) (by linarith)
  have hMW : ∀ ζ : ℂ, moebiusMap W ζ = moebiusMap γ ζ := by
    rcases moebius_ext_three hne12 hne13 hne23 hVden hWden hpts with h | h
    · intro ζ
      rw [Subtype.coe_injective h]
    · intro ζ
      exact (moebiusMap_neg_matrix h ζ).symm
  -- assemble: above the axis through the glue, below it directly
  intro z hden
  rcases le_or_gt z.im 0 with hz | hz
  swap
  · have h1 := hWeq z hden
    rw [hagree z hz.le, hagree (moebiusMap γ z) (moebiusMap_im_pos γ hz).le, hMW] at h1
    exact h1
  · have hγz : (moebiusMap γ z).im ≤ 0 := by
      rcases lt_or_eq_of_le hz with h | h
      · exact (moebiusMap_im_neg γ h).le
      · exact le_of_eq (moebiusMap_im_eq_zero γ h hden)
    rw [hid z hz, hid (moebiusMap γ z) hγz]

end RiemannDynamics
