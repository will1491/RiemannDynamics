/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Winding.Separation

/-!
# Leaves, boxes, and the crossing of a competitor

Following a leaf through a chart box, the connecting vertical arcs, the leaf loop and
its cases, and the theorem that a competitor path crosses every leaf it separates.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- The modified competitor of an upper quasiconformal map is upper quasiconformal with
the same inverse and dilatation bound. -/
theorem hMod_qc {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) :
    IsQCUpper (hMod h) hinv κ := by
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  refine ⟨?_, hqc.mapsTo', ?_, ?_, ?_, hqc.cont', ?_, ?_, ?_⟩
  · intro z hz
    rw [hMod_eq hz]
    exact hqc.mapsTo z hz
  · intro z hz
    rw [hMod_eq hz]
    exact hqc.left_inv z hz
  · intro z hz
    rw [hMod_eq (hqc.mapsTo' z hz)]
    exact hqc.right_inv z hz
  · refine hqc.cont.congr fun z hz => ?_
    exact hMod_eq hz
  · obtain ⟨hL2, gx, gy, hgrad, hgx, hgy⟩ := hqc.sobolev
    refine ⟨?_, gx, gy, ⟨hMod_weak hgrad.1, hMod_weak hgrad.2⟩,
      hgx, hgy⟩
    intro K hK hKc
    refine (hL2 K hK hKc).ae_eq ?_
    filter_upwards [ae_restrict_mem hKc.measurableSet] with z hzK
    exact (hMod_eq (hK hzK)).symm
  · filter_upwards [hqc.jac, ae_restrict_mem hUm] with z hj hzU
    rw [(hMod_eventuallyEq hzU).fderiv_eq]
    exact hj
  · filter_upwards [hqc.belt, ae_restrict_mem hUm] with z hb hzU
    have hfeq : fderiv ℝ (hMod h) z = fderiv ℝ h z :=
      (hMod_eventuallyEq hzU).fderiv_eq
    rw [dz, dzbar, hfeq, ← dz, ← dzbar]
    exact hb

/-- The modified competitor inherits the elementwise group equivariance of the
competitor. -/
theorem hMod_comm {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {h : ℂ → ℂ}
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z)) :
    ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      hMod h (moebiusMap γ z) = moebiusMap γ (hMod h z) := by
  intro γ hγ z hz
  rw [hMod_eq (moebiusMap_im_pos γ hz), hMod_eq hz]
  exact hcomm γ hγ z hz

/-- The Wirtinger quotient is unchanged by the modification on the upper half plane. -/
theorem wirtingerQuotient_hMod {h : ℂ → ℂ} {z : ℂ} (hz : 0 < z.im) :
    wirtingerQuotient (hMod h) z = wirtingerQuotient h z := by
  have hfeq : fderiv ℝ (hMod h) z = fderiv ℝ h z :=
    (hMod_eventuallyEq hz).fderiv_eq
  change dzbar (hMod h) z / dz (hMod h) z = dzbar h z / dz h z
  rw [dz, dzbar, dz, dzbar, hfeq]

/-- **Pointwise leafwise bound**: the forward leaf field shape at a regular point with
the separation, admissibility, and reparametrization properties. -/
theorem sym_leaf_lb_pt {q h : ℂ → ℂ} {A : Atlas q} {C : ℝ≥0∞}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (hqm : Measurable q)
    (hCbd : ∀ w : ℂ, 0 < w.im → qdDist q w (h w) ≤ C)
    {z : ℂ} (hzg : z ∈ good q A)
    (hsep : ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, σ 0 = z → IsTrajOn q σ (Set.Icc 0 T) →
      ENNReal.ofReal T ≤ horizontalDist q (σ 0) (σ T))
    (hpath : ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn q σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)))
    (hrepar : ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn q σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      horizontalVariation q (fun s => h (σ (s * T)))
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (A.flow t z))
    {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal T
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (A.flow t z)) + 2 * C := by
  obtain ⟨σ, hσ0, hσtraj, hσS, hσev⟩ := flow_traj_eval_pos hq A hzg hT
  have hsep' := hsep T hT σ hσ0 hσtraj
  have hpath' := hpath T hT σ hσtraj hσev
  have hrepar' := hrepar T hT σ hσtraj hσev
  have him0 : 0 < (σ 0).im := by
    rw [hσ0]
    exact hzg.1
  have himT : 0 < (σ T).im :=
    (traj_regular hσtraj (Set.right_mem_Icc.mpr hT.le)).1
  have hC0 : qdDist q (σ 0) ((fun s => h (σ (s * T))) 0) ≤ C := by
    change qdDist q (σ 0) (h (σ (0 * T))) ≤ C
    rw [zero_mul]
    exact hCbd (σ 0) him0
  have hC1 : qdDist q ((fun s => h (σ (s * T))) 1) (σ T) ≤ C := by
    change qdDist q (h (σ (1 * T))) (σ T) ≤ C
    rw [one_mul]
    exact le_trans (qdDist_symm_le hqm _ _) (hCbd (σ T) himT)
  exact leaf_lb_of_dH hsep'
    ⟨rfl, rfl, hpath'.cont, hpath'.ac, hpath'.upper⟩ hC0 hC1 hrepar'

/-- **Pointwise backward leafwise bound**: the reverse orientation. -/
theorem sym_leaf_lb_neg_pt {q h : ℂ → ℂ} {A : Atlas q} {C : ℝ≥0∞}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (hqm : Measurable q)
    (hCbd : ∀ w : ℂ, 0 < w.im → qdDist q w (h w) ≤ C)
    {z : ℂ} (hzg : z ∈ good q A)
    (hsep : ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, σ 0 = z → IsTrajOn q σ (Set.Icc 0 T) →
      ENNReal.ofReal T ≤ horizontalDist q (σ 0) (σ T))
    (hpath : ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn q σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
      IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)))
    (hrepar : ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn q σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
      horizontalVariation q (fun s => h (σ (s * T)))
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (A.flow (-t) z))
    {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal T
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity q h (A.flow (-t) z)) + 2 * C := by
  obtain ⟨σ, hσ0, hσtraj, hσS, hσev⟩ := flow_traj_eval_neg hq A hzg hT
  have hsep' := hsep T hT σ hσ0 hσtraj
  have hpath' := hpath T hT σ hσtraj hσev
  have hrepar' := hrepar T hT σ hσtraj hσev
  have him0 : 0 < (σ 0).im := by
    rw [hσ0]
    exact hzg.1
  have himT : 0 < (σ T).im :=
    (traj_regular hσtraj (Set.right_mem_Icc.mpr hT.le)).1
  have hC0 : qdDist q (σ 0) ((fun s => h (σ (s * T))) 0) ≤ C := by
    change qdDist q (σ 0) (h (σ (0 * T))) ≤ C
    rw [zero_mul]
    exact hCbd (σ 0) him0
  have hC1 : qdDist q ((fun s => h (σ (s * T))) 1) (σ T) ≤ C := by
    change qdDist q (h (σ (1 * T))) (σ T) ≤ C
    rw [one_mul]
    exact le_trans (qdDist_symm_le hqm _ _) (hCbd (σ T) himT)
  exact leaf_lb_of_dH hsep'
    ⟨rfl, rfl, hpath'.cont, hpath'.ac, hpath'.upper⟩ hC0 hC1 hrepar'

/-- **The symmetrized flow interface from the separation input**: the full
`VerticalFlowDataSym` instance, conditional only on the leafwise no-shortcut bound. -/
noncomputable def flowDataSym_of_hsep {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hqc : IsQCUpper h hinv κ)
    (hh : Measurable h)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ))
    (hsep : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, σ 0 = z →
      IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      ENNReal.ofReal T ≤ horizontalDist (q : ℂ → ℂ) (σ 0) (σ T))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hCbd : ∀ w : ℂ, 0 < w.im → qdDist (q : ℂ → ℂ) w (h w) ≤ C) :
    VerticalFlowDataSym Γ q h κ :=
  verticalFlowDataSym_of_leafLb q h κ hh C hC A.flow A.measurable_flow
    {z : ℂ | z ∈ good (q : ℂ → ℂ) A
      ∧ (∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, σ 0 = z →
          IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
          ENNReal.ofReal T ≤ horizontalDist (q : ℂ → ℂ) (σ 0) (σ T))
      ∧ (∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
          (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
          IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)))
      ∧ (∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
          (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
          IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)))
      ∧ (∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
          (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
          horizontalVariation (q : ℂ → ℂ) (fun s => h (σ (s * T)))
            ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity (q : ℂ → ℂ) h (A.flow t z))
      ∧ (∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
          (∀ u ∈ Set.Icc 0 T, A.flow (-u) z = σ u) →
          horizontalVariation (q : ℂ → ℂ) (fun s => h (σ (s * T)))
            ≤ ∫⁻ t in Set.Icc (0 : ℝ) T,
                rsDensity (q : ℂ → ℂ) h (A.flow (-t) z))}
    (by
      filter_upwards [good_ae hΓ hcc q hq0 A, hsep, sym_hpath_full q hq0 hqc A,
        sym_hpath_neg q hq0 hqc A, sym_hrepar hΓ hcc q hq0 hqc A,
        sym_hrepar_neg hΓ hcc q hq0 hqc A] with z h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2 h1, h3 h1, h4 h1, h5 h1, h6 h1⟩)
    (fun z hz T hT => sym_leaf_lb_pt q.holo q.measurable hCbd hz.1 hz.2.1
      hz.2.2.1 hz.2.2.2.2.1 hT)
    (fun z hz T hT => sym_leaf_lb_neg_pt q.holo q.measurable hCbd hz.1 hz.2.1
      hz.2.2.2.1 hz.2.2.2.2.2 hT)
    (sym_invar_U_full hΓ hfree hcc q hq0 hκ hqc hh hcomm A)
    (sym_invar_W_full hΓ hfree hcc q hq0 hκ hqc hcomm A)

/-- **The Reich–Strebel main inequality from the leafwise separation bound**: the
exact main-inequality statement, conditional only on the no-shortcut property of the
leaves of `q`. -/
theorem reich_strebel_of_hsep
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (_hbd : ∀ t : ℝ, Filter.Tendsto h (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
      (nhds (t : ℂ)))
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (hsep : ∀ A : Atlas (q : ℂ → ℂ),
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, σ 0 = z →
      IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      ENNReal.ofReal T ≤ horizontalDist (q : ℂ → ℂ) (σ 0) (σ T)) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  have hmeas : MeasurableSet
      (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I) :=
    (isCompact_domain hΓ hfree hcc).measurableSet
  by_cases hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0
  · have hqc' := hMod_qc hqc
    have hh' := hMod_meas hqc
    have hcomm' := hMod_comm (Γ := Γ) hcomm
    obtain ⟨A⟩ := exists_atlas q.holo
    obtain ⟨C, hC, hCbd⟩ :=
      exists_qdDist_displacement_bound hΓ hfree hcc q hqc' hcomm'
    have fd := flowDataSym_of_hsep hΓ hfree hcc q hq0 hκ hqc' hh' hcomm' A
      (hsep A) hC hCbd
    have hcov := reich_strebel_tiling_bound hΓ hfree hcc q hκ hqc' hcomm'
    have hmain := reich_strebel_of_flowDataSym hΓ hfree hcc q hκ hqc' fd hcov
    refine le_trans hmain (le_of_eq ?_)
    refine setLIntegral_congr_fun hmeas fun z hz => ?_
    have hzU : 0 < z.im := by
      obtain ⟨τ, -, rfl⟩ := hz
      simpa using τ.im_pos
    rw [wirtingerQuotient_hMod hzU]
  · push Not at hq0
    rw [l1Norm_eq_zero q hmeas hq0]
    exact zero_le _

/-- **Uniqueness of continuous logarithm lifts on an interval**: two continuous lifts of
the same nonvanishing function agreeing at the left endpoint agree throughout. -/
theorem loglift_unique {f L₁ L₂ : ℝ → ℂ} {c d : ℝ}
    (h₁c : ContinuousOn L₁ (Set.Icc c d)) (h₂c : ContinuousOn L₂ (Set.Icc c d))
    (h₁ : ∀ t ∈ Set.Icc c d, Complex.exp (L₁ t) = f t)
    (h₂ : ∀ t ∈ Set.Icc c d, Complex.exp (L₂ t) = f t)
    (h0 : L₁ c = L₂ c) : Set.EqOn L₁ L₂ (Set.Icc c d) := by
  have hmem : ∀ t ∈ Set.Icc c d, ∃ n : ℤ,
      L₁ t - L₂ t = n * (2 * Real.pi * Complex.I) := by
    intro t ht
    refine Complex.exp_eq_one_iff.mp ?_
    have hf : f t ≠ 0 := by rw [← h₁ t ht]; exact Complex.exp_ne_zero _
    rw [Complex.exp_sub, h₁ t ht, h₂ t ht, div_self hf]
  set g : ℝ → ℝ := fun t => (L₁ t - L₂ t).im with hgdef
  have hgc : ContinuousOn g (Set.Icc c d) :=
    Complex.continuous_im.comp_continuousOn (h₁c.sub h₂c)
  have hg0 : g c = 0 := by rw [hgdef]; simp [h0]
  have him : ∀ t ∈ Set.Icc c d, ∃ n : ℤ, g t = n * (2 * Real.pi) := by
    intro t ht
    obtain ⟨n, hn⟩ := hmem t ht
    refine ⟨n, ?_⟩
    rw [hgdef]
    simp only [hn]
    rw [show ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      Complex.I * ((n : ℝ) * (2 * Real.pi) : ℝ) by push_cast; ring]
    simp
  intro t ht
  obtain ⟨n, hn⟩ := hmem t ht
  have hn0 : n = 0 := by
    by_contra hne
    have hgt : g t = n * (2 * Real.pi) := by
      rw [hgdef]
      simp only [hn]
      rw [show ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
        Complex.I * ((n : ℝ) * (2 * Real.pi) : ℝ) by push_cast; ring]
      simp
    set v : ℝ := if 0 < (n : ℝ) then Real.pi else -Real.pi with hvdef
    have hvmem : v ∈ Set.uIcc (g c) (g t) := by
      rw [hg0, hgt, Set.mem_uIcc]
      rcases lt_or_gt_of_ne (fun h : (n : ℝ) = 0 => hne (by exact_mod_cast h)) with hlt | hgt'
      · right
        have hnz : n < 0 := by exact_mod_cast hlt
        have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_of_lt_add_one (by omega)
        have hv : v = -Real.pi := by rw [hvdef, if_neg (by linarith)]
        rw [hv]
        constructor <;> nlinarith [Real.pi_pos]
      · left
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hgt'
        have hv : v = Real.pi := by rw [hvdef, if_pos (by linarith)]
        rw [hv]
        constructor <;> nlinarith [Real.pi_pos]
    have hsub : Set.uIcc c t ⊆ Set.Icc c d := by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2
    obtain ⟨s, hs, hgs⟩ := intermediate_value_uIcc (hgc.mono hsub) hvmem
    obtain ⟨m, hm⟩ := him s (hsub hs)
    rw [hgs] at hm
    have hpi := Real.pi_pos
    rcases lt_trichotomy (0 : ℝ) (n : ℝ) with h | h | h
    · rw [hvdef, if_pos h] at hm
      rcases lt_trichotomy m 0 with hm' | hm' | hm'
      · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_of_lt_add_one (by omega)
        nlinarith
      · rw [hm', Int.cast_zero, zero_mul] at hm; linarith
      · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm'
        nlinarith
    · exact hne (by exact_mod_cast h.symm)
    · rw [hvdef, if_neg (by linarith)] at hm
      rcases lt_trichotomy m 0 with hm' | hm' | hm'
      · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_of_lt_add_one (by omega)
        nlinarith
      · rw [hm', Int.cast_zero, zero_mul] at hm; linarith
      · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm'
        nlinarith
  rw [hn0, Int.cast_zero, zero_mul] at hn
  exact sub_eq_zero.mp hn

/-- **Tail logarithm lift**: a continuous curve on `[b, ∞)` avoiding a point admits a
continuous logarithm lift of its displacement from that point. -/
theorem exists_loglift_tail {σ : ℝ → ℂ} {z₀ : ℂ} {b : ℝ}
    (hσc : ContinuousOn σ (Set.Ici b)) (hne : ∀ t ∈ Set.Ici b, σ t ≠ z₀) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Set.Ici b) ∧
      ∀ t ∈ Set.Ici b, Complex.exp (L t) = σ t - z₀ := by
  have hb : (b : ℝ) ∈ Set.Ici b := Set.self_mem_Ici
  have hσb : σ b - z₀ ≠ 0 := sub_ne_zero.mpr (hne b hb)
  have hseg : ∀ n : ℕ, ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ t ∈ Set.Icc b (b + n + 1), Complex.exp (L t) = σ t - z₀) ∧
      L b = Complex.log (σ b - z₀) := by
    intro n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set e : ℝ → ℝ := fun s => b + s * ((n : ℝ) + 1) with hedef
    have hmap : ∀ s : unitInterval, e s ∈ Set.Ici b := by
      intro s
      have := s.2.1
      have h2 : 0 ≤ (s : ℝ) * ((n : ℝ) + 1) := by positivity
      simp only [hedef, Set.mem_Ici]
      linarith
    have hγc : Continuous fun s : unitInterval => σ (e s) - z₀ := by
      refine Continuous.sub ?_ continuous_const
      refine hσc.comp_continuous ?_ hmap
      exact continuous_const.add (continuous_subtype_val.mul continuous_const)
    set γ : C(unitInterval, ℂ) := ⟨fun s => σ (e s) - z₀, hγc⟩ with hγdef
    have hγne : ∀ s : unitInterval, γ s ≠ 0 := fun s =>
      sub_ne_zero.mpr (hne _ (hmap s))
    obtain ⟨L₀, hL₀⟩ := exists_isLogLiftOf γ hγne
    set L : ℝ → ℂ := fun t =>
      L₀ (Set.projIcc 0 1 zero_le_one ((t - b) / ((n : ℝ) + 1)))
        + (Complex.log (σ b - z₀) - L₀ 0) with hLdef
    have hLc : Continuous L := by
      refine Continuous.add ?_ continuous_const
      exact L₀.continuous.comp (continuous_projIcc.comp (by fun_prop))
    have hproj0 : Set.projIcc 0 1 zero_le_one ((b - b) / ((n : ℝ) + 1))
        = (0 : unitInterval) := by
      rw [sub_self, zero_div]
      exact Set.projIcc_left zero_le_one
    have hL0exp : Complex.exp (L₀ 0) = σ b - z₀ := by
      have := hL₀ 0
      rw [hγdef] at this
      simpa [hedef] using this
    refine ⟨L, hLc, ?_, ?_⟩
    · intro t ht
      have hs01 : (t - b) / ((n : ℝ) + 1) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [ht.1]) hn1.le
        · rw [div_le_one hn1]; have := ht.2; linarith
      have hproj : Set.projIcc 0 1 zero_le_one ((t - b) / ((n : ℝ) + 1))
          = ⟨(t - b) / ((n : ℝ) + 1), hs01⟩ := Set.projIcc_of_mem zero_le_one hs01
      have het : e ((t - b) / ((n : ℝ) + 1)) = t := by
        rw [hedef]
        field_simp
        ring
      have hlift := hL₀ ⟨(t - b) / ((n : ℝ) + 1), hs01⟩
      rw [hγdef] at hlift
      simp only [ContinuousMap.coe_mk] at hlift
      rw [hLdef]
      simp only
      rw [hproj, Complex.exp_add, hlift, het, Complex.exp_sub,
        Complex.exp_log hσb, hL0exp]
      field_simp
    · rw [hLdef]
      simp only
      rw [hproj0]
      ring
  choose Ln hLnc hLnexp hLnb using hseg
  have hagree : ∀ n m : ℕ, ∀ t, t ∈ Set.Icc b (b + n + 1) →
      t ∈ Set.Icc b (b + m + 1) → Ln n t = Ln m t := by
    intro n m t htn htm
    set d : ℝ := b + (min n m : ℕ) + 1 with hddef
    have hsubn : Set.Icc b d ⊆ Set.Icc b (b + n + 1) := by
      refine Set.Icc_subset_Icc le_rfl ?_
      have : ((min n m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.min_le_left n m
      rw [hddef]; linarith
    have hsubm : Set.Icc b d ⊆ Set.Icc b (b + m + 1) := by
      refine Set.Icc_subset_Icc le_rfl ?_
      have : ((min n m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.min_le_right n m
      rw [hddef]; linarith
    have htd : t ∈ Set.Icc b d := by
      refine ⟨htn.1, ?_⟩
      have h1 : t - b ≤ (n : ℝ) + 1 := by have := htn.2; linarith
      have h2 : t - b ≤ (m : ℝ) + 1 := by have := htm.2; linarith
      have h3 : ((min n m : ℕ) : ℝ) = min (n : ℝ) (m : ℝ) := by
        push_cast; rfl
      rw [hddef, h3]
      rcases min_cases (n : ℝ) (m : ℝ) with ⟨heq, -⟩ | ⟨heq, -⟩ <;> rw [heq] <;> linarith
    exact loglift_unique (f := fun t => σ t - z₀)
      (hLnc n).continuousOn (hLnc m).continuousOn
      (fun u hu => hLnexp n u (hsubn hu)) (fun u hu => hLnexp m u (hsubm hu))
      ((hLnb n).trans (hLnb m).symm) htd
  refine ⟨fun t => Ln (Nat.floor (t - b)) t, ?_, ?_⟩
  · intro t₀ ht₀
    set N : ℕ := Nat.floor (t₀ - b) + 1 with hNdef
    have hmemN : ∀ u, u ∈ Set.Ici b → u < b + N + 1 →
        Ln (Nat.floor (u - b)) u = Ln N u := by
      intro u hu huN
      refine hagree _ N u ⟨hu, ?_⟩ ⟨hu, by linarith⟩
      have := Nat.lt_floor_add_one (u - b)
      linarith
    have hev : (fun t => Ln (Nat.floor (t - b)) t) =ᶠ[nhdsWithin t₀ (Set.Ici b)]
        Ln N := by
      have hIio : Set.Iio (b + N + 1) ∈ nhdsWithin t₀ (Set.Ici b) := by
        refine mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ?_)
        have h1 : t₀ - b < Nat.floor (t₀ - b) + 1 := Nat.lt_floor_add_one (t₀ - b)
        rw [hNdef]; push_cast; linarith
      filter_upwards [hIio, eventually_mem_nhdsWithin] with u hu1 hu2
      exact hmemN u hu2 hu1
    have hbase : ContinuousWithinAt (Ln N) (Set.Ici b) t₀ :=
      (hLnc N).continuousAt.continuousWithinAt
    refine hbase.congr_of_eventuallyEq hev ?_
    refine hmemN t₀ ht₀ ?_
    have := Nat.lt_floor_add_one (t₀ - b)
    rw [hNdef]; push_cast; linarith
  · intro t ht
    refine hLnexp _ t ⟨ht, ?_⟩
    have := (Nat.lt_floor_add_one (t - b)).le
    linarith

/-- **Branched double-cover lift of a trajectory**: a continuous square root of the
displacement from a point, kept small and shifted to the unit-height horizontal, is a
vertical trajectory of the pulled-back differential `4 (v − i)² q (z₀ + (v − i)²)`. -/
theorem traj_double_cover {q : ℂ → ℂ} {z₀ : ℂ} {σ w : ℝ → ℂ} {b : ℝ}
    (hσ : IsTrajOn q σ (Set.Ici b)) (hwc : ContinuousOn w (Set.Ici b))
    (hw0 : ∀ t ∈ Set.Ici b, w t ≠ 0)
    (hwsq : ∀ t ∈ Set.Ici b, w t ^ 2 = σ t - z₀)
    (hwsmall : ∀ t ∈ Set.Ici b, ‖w t‖ < 1 / 2) :
    IsTrajOn (fun v => 4 * (v - Complex.I) ^ 2 * q (z₀ + (v - Complex.I) ^ 2))
      (fun t => w t + Complex.I) (Set.Ici b) := by
  set p : ℂ → ℂ := fun v => z₀ + (v - Complex.I) ^ 2 with hpdef
  have hpc : Continuous p := by fun_prop
  have hpτ : ∀ u ∈ Set.Ici b, p (w u + Complex.I) = σ u := by
    intro u hu
    rw [hpdef]
    simp only [add_sub_cancel_right]
    rw [hwsq u hu]
    ring
  constructor
  · exact hwc.add continuousOn_const
  · intro t ht
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t ht
    have hτU : p (w t + Complex.I) ∈ U := by rw [hpτ t ht]; exact hpU
    obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp
      (hpc.continuousAt (hUo.mem_nhds hτU) : p ⁻¹' U ∈ 𝓝 (w t + Complex.I))
    have hwt : (0 : ℝ) < ‖w t‖ := norm_pos_iff.mpr (hw0 t ht)
    set δ : ℝ := min δ₁ (‖w t‖ / 2) with hδdef
    have hδ : 0 < δ := lt_min hδ₁ (by linarith)
    set V : Set ℂ := Metric.ball (w t + Complex.I) δ with hVdef
    have hVsubU : ∀ v ∈ V, p v ∈ U := fun v hv =>
      hball₁ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hv)
        (min_le_left _ _)))
    have hVnear : ∀ v ∈ V, ‖v - Complex.I - w t‖ < ‖w t‖ / 2 := by
      intro v hv
      have h1 : ‖v - (w t + Complex.I)‖ < δ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hv
      have h2 : v - Complex.I - w t = v - (w t + Complex.I) := by ring
      rw [h2]
      exact lt_of_lt_of_le h1 (min_le_right _ _)
    have hVne : ∀ v ∈ V, v - Complex.I ≠ 0 := by
      intro v hv h0
      have h1 := hVnear v hv
      rw [h0, zero_sub, norm_neg] at h1
      linarith
    refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_, ?_, Φ ∘ p, ?_, ?_, ?_, ?_⟩
    · intro v hv
      have h1 := hVnear v hv
      have h2 : |(v - Complex.I - w t).im| ≤ ‖v - Complex.I - w t‖ :=
        Complex.abs_im_le_norm _
      have h3 : |(w t).im| ≤ ‖w t‖ := Complex.abs_im_le_norm _
      have h4 : (v - Complex.I - w t).im = v.im - 1 - (w t).im := by simp
      have h5 := hwsmall t ht
      simp only [Set.mem_setOf_eq]
      have h6 : |v.im - 1 - (w t).im| < ‖w t‖ / 2 := h4 ▸ lt_of_le_of_lt h2 h1
      have h7 := abs_lt.mp h6
      have h8 := abs_le.mp h3
      linarith [h7.1, h8.1]
    · intro v hv
      refine mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (hVne v hv))) ?_
      exact hUne _ (hVsubU v hv)
    · have hpd : Differentiable ℂ p := by
        rw [hpdef]
        exact (((differentiable_id.sub_const Complex.I).pow 2).const_add z₀)
      exact hΦd.comp hpd.differentiableOn (fun v hv => hVsubU v hv)
    · intro v₁ h₁ v₂ h₂ heq
      have hpeq : p v₁ = p v₂ := hΦinj (hVsubU v₁ h₁) (hVsubU v₂ h₂) heq
      have hsq : (v₁ - Complex.I) ^ 2 = (v₂ - Complex.I) ^ 2 := by
        have := hpeq
        rw [hpdef] at this
        simpa using this
      have hfac : ((v₁ - Complex.I) - (v₂ - Complex.I))
          * ((v₁ - Complex.I) + (v₂ - Complex.I)) = 0 := by
        linear_combination hsq
      rcases mul_eq_zero.mp hfac with h | h
      · have : v₁ = v₂ := by linear_combination h
        exact this
      · exfalso
        have h1 := hVnear v₁ h₁
        have h2 := hVnear v₂ h₂
        have h3 : ‖(2 : ℂ) * w t‖ = 2 * ‖w t‖ := by
          rw [norm_mul]; norm_num
        have h4 : (2 : ℂ) * w t
            = (w t - (v₁ - Complex.I)) + (w t - (v₂ - Complex.I)) := by
          linear_combination h
        have h5 : ‖(2 : ℂ) * w t‖ ≤ ‖w t - (v₁ - Complex.I)‖
            + ‖w t - (v₂ - Complex.I)‖ := h4 ▸ norm_add_le _ _
        rw [norm_sub_rev] at h5
        nth_rewrite 2 [norm_sub_rev] at h5
        rw [h3] at h5
        linarith
    · intro v hv
      have hp' : HasDerivAt p (2 * (v - Complex.I)) v := by
        have h1 : HasDerivAt (fun x : ℂ => (x - Complex.I) ^ 2)
            (2 * (v - Complex.I)) v := by
          have h0 : HasDerivAt (fun x : ℂ => x - Complex.I) 1 v :=
            (hasDerivAt_id v).sub_const Complex.I
          have := h0.pow 2
          simpa using this
        rw [hpdef]
        simpa using h1.const_add z₀
      have hΦ' : HasDerivAt Φ (deriv Φ (p v)) (p v) :=
        (hΦd.differentiableAt (hUo.mem_nhds (hVsubU v hv))).hasDerivAt
      have hcomp : HasDerivAt (Φ ∘ p) (deriv Φ (p v) * (2 * (v - Complex.I))) v :=
        hΦ'.comp v hp'
      rw [hcomp.deriv]
      have hsq := hΦsq (p v) (hVsubU v hv)
      calc (deriv Φ (p v) * (2 * (v - Complex.I))) ^ 2
          = deriv Φ (p v) ^ 2 * (4 * (v - Complex.I) ^ 2) := by ring
        _ = -q (p v) * (4 * (v - Complex.I) ^ 2) := by rw [hsq]
        _ = -(4 * (v - Complex.I) ^ 2 * q (z₀ + (v - Complex.I) ^ 2)) := by
            rw [hpdef]; ring
    · have hτcont : ContinuousWithinAt (fun u => w u + Complex.I) (Set.Ici b) t :=
        ((hwc.add continuousOn_const) t ht)
      have hVmem : V ∈ 𝓝 (w t + Complex.I) := Metric.ball_mem_nhds _ hδ
      filter_upwards [hev, hτcont.tendsto.eventually_mem hVmem,
        eventually_mem_nhdsWithin] with u hu hVu huI
      refine ⟨hVu, ?_⟩
      change Φ (p (w u + Complex.I)) = Φ (p (w t + Complex.I)) + _
      rw [hpτ u huI, hpτ t ht]
      exact hu.2

/-- **No all-time trajectory falls into a zero**: a vertical trajectory defined for all
future times cannot converge to a zero of the differential — through the branched double
cover the zero has even order, so a transparent chart develops the lifted trajectory
affinely with unbounded advance while remaining bounded near the puncture. -/
theorem no_alltime_traj_to_zero {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a))
    {z₀ : ℂ} (hz₀im : 0 < z₀.im) (hz₀ : q z₀ = 0)
    (hlim : Filter.Tendsto σ Filter.atTop (𝓝 z₀)) : False := by
  have hH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hnc : ¬ ∀ᶠ z in 𝓝 z₀, q z = 0 := by
    intro hc
    obtain ⟨t, ht0, hta⟩ := ((hlim.eventually hc).and (eventually_ge_atTop a)).exists
    exact (traj_regular hσ hta).2 ht0
  obtain ⟨m, g, hg, hg0, hfac, -⟩ := exists_order_factorization hH hq hz₀im hnc
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (1 / 4) (by norm_num)
  set b : ℝ := max a N with hbdef
  have hσb : IsTrajOn q σ (Set.Ici b) :=
    traj_mono hσ (Set.Ici_subset_Ici.mpr (le_max_left a N))
  have hsmall : ∀ t ∈ Set.Ici b, ‖σ t - z₀‖ < 1 / 4 := by
    intro t ht
    rw [← dist_eq_norm]
    exact hN t (le_trans (le_max_right a N) ht)
  have hnez : ∀ t ∈ Set.Ici b, σ t ≠ z₀ := by
    intro t ht h
    exact (traj_regular hσb ht).2 (by rw [h]; exact hz₀)
  obtain ⟨L, hLc, hLexp⟩ := exists_loglift_tail hσb.cont hnez
  set w : ℝ → ℂ := fun t => Complex.exp (L t / 2) with hwdef
  have hwc : ContinuousOn w (Set.Ici b) :=
    Complex.continuous_exp.comp_continuousOn (hLc.div_const 2)
  have hw0 : ∀ t ∈ Set.Ici b, w t ≠ 0 := fun t _ => Complex.exp_ne_zero _
  have hwsq : ∀ t ∈ Set.Ici b, w t ^ 2 = σ t - z₀ := by
    intro t ht
    have h1 : L t / 2 + L t / 2 = L t := by ring
    rw [hwdef]
    simp only
    rw [sq, ← Complex.exp_add, h1]
    exact hLexp t ht
  have hwnorm : ∀ t ∈ Set.Ici b, ‖w t‖ ^ 2 = ‖σ t - z₀‖ := by
    intro t ht
    rw [← norm_pow, hwsq t ht]
  have hwsmall : ∀ t ∈ Set.Ici b, ‖w t‖ < 1 / 2 := by
    intro t ht
    by_contra hcon
    push Not at hcon
    have h1 := hwnorm t ht
    have h2 := hsmall t ht
    nlinarith
  have hτ := traj_double_cover hσb hwc hw0 hwsq hwsmall
  have hwlim : Filter.Tendsto w Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn0 : Filter.Tendsto (fun t => σ t - z₀) Filter.atTop (𝓝 0) := by
      simpa using hlim.sub_const z₀
    have hn1 : Filter.Tendsto (fun t => ‖σ t - z₀‖) Filter.atTop (𝓝 0) := by
      simpa using hn0.norm
    have hn2 : Filter.Tendsto (fun t => Real.sqrt ‖σ t - z₀‖) Filter.atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn1
      simpa using this
    refine hn2.congr' ?_
    filter_upwards [eventually_ge_atTop b] with t ht
    rw [← hwnorm t ht, Real.sqrt_sq (norm_nonneg _)]
  have hτlim : Filter.Tendsto (fun t => w t + Complex.I) Filter.atTop
      (𝓝 Complex.I) := by
    simpa using hwlim.add_const Complex.I
  set p : ℂ → ℂ := fun v => z₀ + (v - Complex.I) ^ 2 with hpdef
  have hpI : p Complex.I = z₀ := by rw [hpdef]; simp
  have hpan : AnalyticAt ℂ p Complex.I := by
    rw [hpdef]
    exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).pow 2)
  set ĝ : ℂ → ℂ := fun v => 4 * g (p v) with hĝdef
  have hĝan : AnalyticAt ℂ ĝ Complex.I := by
    refine analyticAt_const.mul ?_
    exact (hpI.symm ▸ hg : AnalyticAt ℂ g (p Complex.I)).comp hpan
  have hĝ0 : ĝ Complex.I ≠ 0 := by
    rw [hĝdef]
    simp only [hpI]
    exact mul_ne_zero (by norm_num) hg0
  have hfacup : ∀ᶠ v in 𝓝 Complex.I,
      4 * (v - Complex.I) ^ 2 * q (z₀ + (v - Complex.I) ^ 2)
        = (v - Complex.I) ^ (2 * (m + 1)) * ĝ v := by
    have hpt : Filter.Tendsto p (𝓝 Complex.I) (𝓝 z₀) := by
      rw [← hpI]
      exact hpan.continuousAt.tendsto
    filter_upwards [hpt.eventually hfac] with v hv
    have hpz : p v - z₀ = (v - Complex.I) ^ 2 := by rw [hpdef]; ring
    have hpow : (v - Complex.I) ^ (2 * (m + 1))
        = ((v - Complex.I) ^ 2) ^ m * (v - Complex.I) ^ 2 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, pow_mul]
    change 4 * (v - Complex.I) ^ 2 * q (p v) = _
    rw [hv, hpz, hpow, hĝdef]
    ring
  obtain ⟨rE, hrE, -, Φ, hΦd, hΦsq⟩ := even_zero_transparent_chart isOpen_univ
    (Set.mem_univ Complex.I) (m + 1) hĝan hĝ0 hfacup
  have hΦI : ContinuousAt Φ Complex.I :=
    (hΦd.differentiableAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self hrE))).continuousAt
  obtain ⟨b₁₀, hb₁₀⟩ := eventually_atTop.mp
    (hτlim.eventually_mem (Metric.ball_mem_nhds _ hrE))
  set b₁ : ℝ := max b b₁₀ with hb₁def
  have hΦτ : Filter.Tendsto (fun t => Φ (w t + Complex.I)) Filter.atTop
      (𝓝 (Φ Complex.I)) := hΦI.tendsto.comp hτlim
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (hΦτ.eventually_mem (Metric.ball_mem_nhds _ one_pos))
  set C : ℝ := ‖Φ (w b₁ + Complex.I) - Φ Complex.I‖ with hCdef
  set tf : ℝ := max T₁ (b₁ + C + 2) with htfdef
  have hCnn : 0 ≤ C := norm_nonneg _
  have hb₁tf : b₁ ≤ tf := le_trans (by linarith) (le_max_right _ _)
  obtain ⟨ε, hε, haff⟩ := traj_ambient_affine Metric.isOpen_ball hΦd hΦsq hτ hb₁tf
    (fun u hu => le_trans (le_max_left b b₁₀) hu.1)
    (fun u hu => hb₁₀ u (le_trans (le_max_right b b₁₀) hu.1))
  have heq := haff tf ⟨hb₁tf, le_rfl⟩
  have h1 : Φ (w tf + Complex.I) - Φ (w b₁ + Complex.I)
      = (ε : ℂ) * ((tf - b₁ : ℝ) : ℂ) := by rw [heq]; ring
  have hnε : ‖(ε : ℂ)‖ = 1 := by
    rcases hε with h | h <;> rw [h] <;> simp
  have h2 : ‖Φ (w tf + Complex.I) - Φ (w b₁ + Complex.I)‖ = tf - b₁ := by
    rw [h1, norm_mul, hnε, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have h3 : dist (Φ (w tf + Complex.I)) (Φ (w b₁ + Complex.I))
      ≤ dist (Φ (w tf + Complex.I)) (Φ Complex.I)
        + dist (Φ Complex.I) (Φ (w b₁ + Complex.I)) := dist_triangle _ _ _
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, h2] at h3
  have h4 : ‖Φ (w tf + Complex.I) - Φ Complex.I‖ < 1 := by
    have := hT₁ tf (le_max_left _ _)
    rwa [Metric.mem_ball, dist_eq_norm] at this
  have h5 : ‖Φ Complex.I - Φ (w b₁ + Complex.I)‖ = C := by
    rw [norm_sub_rev]
  have h6 : b₁ + C + 2 ≤ tf := le_max_right _ _
  rw [h5] at h3
  linarith

/-- **Regular accumulation of a confined forward tail**: a vertical trajectory defined
for all future times whose tail stays in a compact subset of the upper half plane
accumulates at a point of the compact where the differential does not vanish. -/
theorem tail_regular_accum {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im})
    {T₀ : ℝ} (hconf : ∀ t, T₀ ≤ t → σ t ∈ K) :
    ∃ w ∈ K, 0 < w.im ∧ q w ≠ 0 ∧ MapClusterPt w Filter.atTop σ := by
  by_contra hno
  push Not at hno
  set b : ℝ := max a T₀ with hbdef
  have hσb : IsTrajOn q σ (Set.Ici b) :=
    traj_mono hσ (Set.Ici_subset_Ici.mpr (le_max_left a T₀))
  have hbK : ∀ t ∈ Set.Ici b, σ t ∈ K := fun t ht =>
    hconf t (le_trans (le_max_right a T₀) ht)
  have hmapK : Filter.map σ Filter.atTop ≤ Filter.principal K := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Filter.mem_of_superset (Filter.Ici_mem_atTop b) (fun t ht => hbK t ht)
  haveI : (Filter.map σ Filter.atTop).NeBot := Filter.map_neBot
  obtain ⟨z₀, hz₀K, hz₀cl⟩ := hK hmapK
  have hz₀im : 0 < z₀.im := hKH hz₀K
  have hz₀MCP : MapClusterPt z₀ Filter.atTop σ := hz₀cl
  have hz₀0 : q z₀ = 0 := by
    by_contra h
    exact hno z₀ hz₀K hz₀im h hz₀MCP
  have hq0ex : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0 := by
    obtain ⟨h1, h2⟩ := traj_regular hσb Set.self_mem_Ici
    exact ⟨σ b, h1, h2⟩
  have hZfin : Set.Finite {z ∈ K | q z = 0} := zeros_finite hq hq0ex hK hKH
  have htend : Filter.Tendsto σ Filter.atTop (𝓝 z₀) := by
    by_contra hnt
    rw [Metric.tendsto_atTop] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hdiv⟩ := hnt
    have hDfin : Set.Finite ((fun v => dist v z₀) '' ({z ∈ K | q z = 0} \ {z₀})) :=
      (hZfin.subset Set.diff_subset).image _
    have hrex : ∃ r : ℝ, 0 < r ∧ r < ε ∧
        ∀ v ∈ K, q v = 0 → v ≠ z₀ → r < dist v z₀ := by
      by_cases hne : ({z ∈ K | q z = 0} \ {z₀}).Nonempty
      · have hFne : hDfin.toFinset.Nonempty := by
          obtain ⟨v, hv⟩ := hne
          exact ⟨dist v z₀, (Set.Finite.mem_toFinset _).mpr ⟨v, hv, rfl⟩⟩
        set dmin : ℝ := hDfin.toFinset.min' hFne with hdmindef
        have hdmin0 : 0 < dmin := by
          have hmem := hDfin.toFinset.min'_mem hFne
          rw [Set.Finite.mem_toFinset] at hmem
          obtain ⟨v, ⟨⟨-, -⟩, hvne⟩, hveq⟩ := hmem
          rw [hdmindef, ← hveq]
          exact dist_pos.mpr (by simpa using hvne)
        refine ⟨min (ε / 2) (dmin / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
        · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        · intro v hvK hv0 hvne
          have hmemF : dist v z₀ ∈ hDfin.toFinset := by
            rw [Set.Finite.mem_toFinset]
            exact ⟨v, ⟨⟨hvK, hv0⟩, by simpa using hvne⟩, rfl⟩
          have h1 := hDfin.toFinset.min'_le _ hmemF
          have h2 : min (ε / 2) (dmin / 2) ≤ dmin / 2 := min_le_right _ _
          rw [← hdmindef] at h1
          linarith
      · refine ⟨ε / 2, by linarith, by linarith, ?_⟩
        intro v hvK hv0 hvne
        exact absurd ⟨⟨hvK, hv0⟩, by simpa using hvne⟩ (fun h => hne ⟨v, h⟩)
    obtain ⟨r, hr0, hrε, hravoid⟩ := hrex
    have hcross : ∀ T : ℝ, ∃ t, T ≤ t ∧ b ≤ t ∧ dist (σ t) z₀ = r := by
      intro T
      have hfreq : ∃ᶠ t in Filter.atTop, σ t ∈ Metric.ball z₀ r :=
        mapClusterPt_iff_frequently.mp hz₀MCP _ (Metric.ball_mem_nhds _ hr0)
      obtain ⟨t₁, ht₁T, ht₁mem⟩ := Filter.frequently_atTop.mp hfreq (max T b)
      obtain ⟨t₂, ht₂t₁, ht₂d⟩ := hdiv t₁
      have hsub : Set.Icc t₁ t₂ ⊆ Set.Ici b := fun u hu =>
        le_trans (le_max_right T b) (le_trans ht₁T hu.1)
      have hgc : ContinuousOn (fun t => dist (σ t) z₀) (Set.Icc t₁ t₂) :=
        (continuous_id.dist continuous_const).comp_continuousOn
          (hσb.cont.mono hsub)
      have hmem : r ∈ Set.Icc (dist (σ t₁) z₀) (dist (σ t₂) z₀) :=
        ⟨(Metric.mem_ball.mp ht₁mem).le, le_trans hrε.le ht₂d⟩
      obtain ⟨ts, htsI, hts⟩ := intermediate_value_Icc ht₂t₁ hgc hmem
      exact ⟨ts, le_trans (le_max_left T b) (le_trans ht₁T htsI.1),
        le_trans (le_max_right T b) (le_trans ht₁T htsI.1), hts⟩
    set S : Set ℝ := {t | b ≤ t ∧ dist (σ t) z₀ = r} with hSdef
    have hSfreq : ∃ᶠ t in Filter.atTop, t ∈ S := by
      refine Filter.frequently_atTop.mpr fun T => ?_
      obtain ⟨t, h1, h2, h3⟩ := hcross T
      exact ⟨t, h1, h2, h3⟩
    haveI hSne : (Filter.atTop ⊓ Filter.principal S).NeBot :=
      frequently_iff_neBot.mp hSfreq
    have hK'c : IsCompact (K ∩ {v | dist v z₀ = r}) :=
      hK.inter_right (isClosed_eq (continuous_id.dist continuous_const)
        continuous_const)
    have hle2 : Filter.map σ (Filter.atTop ⊓ Filter.principal S)
        ≤ Filter.principal (K ∩ {v | dist v z₀ = r}) := by
      rw [Filter.le_principal_iff, Filter.mem_map]
      refine Filter.mem_of_superset
        (Filter.mem_inf_of_right (Filter.mem_principal_self S)) ?_
      rintro t ⟨htb, htd⟩
      exact ⟨hbK t htb, htd⟩
    haveI : (Filter.map σ (Filter.atTop ⊓ Filter.principal S)).NeBot :=
      Filter.map_neBot
    obtain ⟨v, hvK', hvcl⟩ := hK'c hle2
    have hvMCP : MapClusterPt v Filter.atTop σ :=
      hvcl.mono (Filter.map_mono inf_le_left)
    have hvq : q v = 0 := by
      by_contra h
      exact hno v hvK'.1 (hKH hvK'.1) h hvMCP
    have hvne : v ≠ z₀ := by
      intro h
      have h2 := hvK'.2
      rw [h] at h2
      simp only [Set.mem_setOf_eq, dist_self] at h2
      exact hr0.ne h2
    exact lt_irrefl r (hvK'.2 ▸ hravoid v hvK'.1 hvq hvne)
  exact no_alltime_traj_to_zero hq hσ hz₀im hz₀0 htend

/-- **The trajectory follows the chart flow line two-sidedly**: around any time whose
point lies in a natural chart whose development contains the full symmetric horizontal
segment, the trajectory coincides with the local flow line, with a single sign. -/
theorem leaf_follow {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ w ∈ S, q w ≠ 0)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a))
    {t h : ℝ} (hh : 0 < h) (hta : a ≤ t - h) (htS : σ t ∈ S)
    (hdev : ∀ x : ℝ, |x| ≤ h → Φ (σ t) + (x : ℂ) ∈ Φ '' S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ u : ℝ, |u| ≤ h → σ (t + u) = localFlow Φ S (ε * u) (σ t) := by
  have hIcc : Set.Icc (t - h) (t + h) ⊆ Set.Ici a := fun u hu => by
    have := hu.1
    simp only [Set.mem_Ici]
    linarith
  obtain ⟨ε, hε, hev⟩ := traj_ambient_local hS hΦd hΦsq hσ hIcc
    (⟨by linarith, by linarith⟩ : t ∈ Set.Icc (t - h) (t + h)) htS
  have hevn : ∀ᶠ u in 𝓝 t, Φ (σ u) = Φ (σ t) + ε * ((u - t : ℝ) : ℂ) := by
    rwa [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by linarith) (by linarith))] at hev
  have hεsq : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  have habs : ∀ u : ℝ, |ε * u| = |u| := by
    intro u
    rw [abs_mul]
    rcases hε with h1 | h1 <;> rw [h1] <;> simp
  -- one-sided matching engine
  have hside : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      (∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
        Φ (σ (t + sgn * u)) = Φ (σ t) + (ε * sgn) * (u : ℂ)) →
      IsTrajOn q (fun u => σ (t + sgn * u)) (Set.Icc 0 h) →
      ∀ u ∈ Set.Icc (0 : ℝ) h, σ (t + sgn * u)
        = localFlow Φ S ((ε * sgn) * u) (σ t) := by
    intro sgn hsgn hdevε hτ
    have hεs : ε * sgn = 1 ∨ ε * sgn = -1 := by
      rcases hε with h1 | h1 <;> rcases hsgn with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
    have hsegm : ∀ u ∈ Set.Icc (0 : ℝ) h,
        Φ (σ t) + (((ε * sgn) * u : ℝ) : ℂ) ∈ Φ '' S := by
      intro u hu
      refine hdev _ ?_
      have : |(ε * sgn) * u| = |u| := by
        rw [abs_mul, abs_mul]
        rcases hε with h1 | h1 <;> rcases hsgn with h2 | h2 <;>
          rw [h1, h2] <;> simp
      rw [this, abs_of_nonneg hu.1]
      exact hu.2
    obtain ⟨hflow0, hflowτ, -⟩ := seg_traj hS hΦd hΦinj hSH hSne hΦsq htS
      hεs hh hsegm
    have hgerm : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
        σ (t + sgn * u) = localFlow Φ S ((ε * sgn) * u) (σ t) := by
      have hcS : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h), σ (t + sgn * u) ∈ S := by
        have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) h := Set.left_mem_Icc.mpr hh.le
        have hc := hτ.cont 0 h0m
        have := hc (hS.mem_nhds (by simpa using htS))
        simpa using this
      filter_upwards [hdevε, hcS, eventually_mem_nhdsWithin] with u hd hcSu hum
      refine hΦinj hcSu (localFlow_mem (hsegm u hum)) ?_
      rw [hd, localFlow_dev (hsegm u hum)]
      push_cast
      ring
    have := traj_unique hh.le hτ hflowτ hgerm
    intro u hu
    exact this hu
  -- forward branch
  have hτfwd : IsTrajOn q (fun u => σ (t + 1 * u)) (Set.Icc 0 h) := by
    have h1 := traj_shift t hσ
    have h2 : Set.Icc (0 : ℝ) h ⊆ (fun u : ℝ => u + t) ⁻¹' Set.Ici a := by
      intro u hu
      simp only [Set.mem_preimage, Set.mem_Ici]
      linarith [hu.1]
    have h3 := traj_mono h1 h2
    have hfun : (fun u => σ (u + t)) = fun u => σ (t + 1 * u) := by
      funext u
      ring_nf
    rwa [hfun] at h3
  have hdevfwd : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
      Φ (σ (t + 1 * u)) = Φ (σ t) + (ε * 1) * (u : ℂ) := by
    have hmap : Filter.Tendsto (fun u : ℝ => t + 1 * u)
        (nhdsWithin 0 (Set.Icc 0 h)) (𝓝 t) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have : Continuous fun u : ℝ => t + 1 * u := by continuity
      simpa using this.tendsto 0
    filter_upwards [hmap.eventually hevn] with u hu
    rw [hu]
    push_cast
    ring
  have hfwd := hside 1 (Or.inl rfl) hdevfwd hτfwd
  -- backward branch
  have hτbwd : IsTrajOn q (fun u => σ (t + (-1) * u)) (Set.Icc 0 h) := by
    have hshift := traj_shift (t - h) hσ
    have hsub : Set.Icc (0 : ℝ) h ⊆ (fun u : ℝ => u + (t - h)) ⁻¹' Set.Ici a := by
      intro u hu
      simp only [Set.mem_preimage, Set.mem_Ici]
      linarith [hu.1]
    have hbase := traj_mono hshift hsub
    have hrev := traj_reverse hbase
    have hset : (fun u : ℝ => -u) ⁻¹' Set.Icc (0 : ℝ) h = Set.Icc (-h) 0 := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hset] at hrev
    have hshift2 := traj_shift (-h) hrev
    have hset2 : (fun u : ℝ => u + -h) ⁻¹' Set.Icc (-h) (0 : ℝ) = Set.Icc 0 h := by
      ext u
      simp only [Set.mem_preimage, Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hset2] at hshift2
    have hfun : (fun u : ℝ => (fun v : ℝ =>
        (fun y : ℝ => σ (y + (t - h))) (-v)) (u + -h))
        = fun u => σ (t + (-1) * u) := by
      funext u
      change σ (-(u + -h) + (t - h)) = σ (t + (-1) * u)
      ring_nf
    rwa [hfun] at hshift2
  have hdevbwd : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 h),
      Φ (σ (t + (-1) * u)) = Φ (σ t) + (ε : ℂ) * ((-1 : ℝ) : ℂ) * (u : ℂ) := by
    have hmap : Filter.Tendsto (fun u : ℝ => t + (-1) * u)
        (nhdsWithin 0 (Set.Icc 0 h)) (𝓝 t) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have : Continuous fun u : ℝ => t + (-1) * u := by continuity
      simpa using this.tendsto 0
    filter_upwards [hmap.eventually hevn] with u hu
    rw [hu]
    push_cast
    ring
  have hbwd := hside (-1) (Or.inr rfl) hdevbwd hτbwd
  refine ⟨ε, hε, ?_⟩
  intro u hu
  rcases le_or_gt 0 u with h0 | h0
  · have := hfwd u ⟨h0, by rwa [abs_of_nonneg h0] at hu⟩
    simpa using this
  · have hmem : -u ∈ Set.Icc (0 : ℝ) h :=
      ⟨by linarith, by rwa [abs_of_neg h0] at hu⟩
    have := hbwd (-u) hmem
    have hl : t + (-1) * (-u) = t + u := by ring
    have hr : (ε * (-1)) * (-u) = ε * u := by ring
    rwa [hl, hr] at this

/-- **Natural chart box at a regular point**: an injective `−q`-natural chart on an open
set of regular points of the upper half plane whose development contains a ball. -/
theorem box_data {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    {w : ℂ} (hw : 0 < w.im) (hq0 : q w ≠ 0) :
    ∃ S : Set ℂ, ∃ Φ : ℂ → ℂ, ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ IsOpen S ∧ w ∈ S ∧
      S ⊆ {z : ℂ | 0 < z.im} ∧ (∀ z ∈ S, q z ≠ 0) ∧
      DifferentiableOn ℂ Φ S ∧ Set.InjOn Φ S ∧
      (∀ z ∈ S, deriv Φ z ^ 2 = -q z) ∧
      Metric.ball (Φ w) ρ₀ ⊆ Φ '' S := by
  have hH : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨r, hr, hsubH, Φ, hΦd, hΦinj, hΦsq⟩ :=
    exists_natural_chart (q := fun z => -q z) hH hq.neg hw (neg_ne_zero.mpr hq0)
  have hqc : ContinuousAt q w := hq.continuousOn.continuousAt (hH.mem_nhds hw)
  obtain ⟨r₁, hr₁, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem
      (hqc (isOpen_ne.mem_nhds hq0) : q ⁻¹' {u | u ≠ 0} ∈ 𝓝 w)
      (Metric.ball_mem_nhds w hr))
  set S : Set ℂ := Metric.ball w r₁ with hSdef
  have hSr : S ⊆ Metric.ball w r := fun z hz => (hball hz).2
  have hSne : ∀ z ∈ S, q z ≠ 0 := fun z hz => (hball hz).1
  have hSopen : IsOpen S := Metric.isOpen_ball
  have hSH : S ⊆ {z : ℂ | 0 < z.im} := hSr.trans hsubH
  have hwS : w ∈ S := Metric.mem_ball_self hr₁
  have hΦdS : DifferentiableOn ℂ Φ S := hΦd.mono hSr
  have hΦinjS : Set.InjOn Φ S := hΦinj.mono hSr
  have hΦsqS : ∀ z ∈ S, deriv Φ z ^ 2 = -q z := fun z hz => hΦsq z (hSr hz)
  have hder : deriv Φ w ≠ 0 := by
    intro h0
    refine hSne w hwS ?_
    have := hΦsqS w hwS
    rw [h0] at this
    simpa using this.symm
  have han : AnalyticAt ℂ Φ w := (hΦdS.analyticOnNhd hSopen) w hwS
  have hstrict : HasStrictDerivAt Φ (deriv Φ w) w :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  have himg : Φ '' S ∈ 𝓝 (Φ w) := by
    rw [← hstrict.map_nhds_eq hder]
    exact Filter.image_mem_map (hSopen.mem_nhds hwS)
  obtain ⟨ρ₀, hρ₀, hρball⟩ := Metric.mem_nhds_iff.mp himg
  exact ⟨S, Φ, ρ₀, hρ₀, hSopen, hwS, hSH, hSne, hΦdS, hΦinjS, hΦsqS, hρball⟩

/-- **Central-transversal crossing of a box passage**: an all-time trajectory visiting
the quarter-ball of a chart box crosses the central vertical chart line at a nearby
time, at a height within the quarter radius. -/
theorem box_crossing {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ z ∈ S, q z ≠ 0)
    (hΦsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    {W₀ : ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (himg : Metric.ball W₀ ρ₀ ⊆ Φ '' S)
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a))
    {t : ℝ} (hta : a ≤ t - ρ₀ / 2) (htS : σ t ∈ S)
    (htβ : Φ (σ t) ∈ Metric.ball W₀ (ρ₀ / 4)) :
    ∃ ts : ℝ, |ts - t| < ρ₀ / 4 ∧ σ ts ∈ S ∧
      (Φ (σ ts)).re = W₀.re ∧ |(Φ (σ ts)).im - W₀.im| < ρ₀ / 4 := by
  have htβ' : ‖Φ (σ t) - W₀‖ < ρ₀ / 4 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp htβ
  have hdev : ∀ x : ℝ, |x| ≤ ρ₀ / 2 → Φ (σ t) + (x : ℂ) ∈ Φ '' S := by
    intro x hx
    refine himg (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm]
    calc ‖Φ (σ t) + (x : ℂ) - W₀‖ ≤ ‖Φ (σ t) - W₀‖ + ‖(x : ℂ)‖ := by
          rw [show Φ (σ t) + (x : ℂ) - W₀ = (Φ (σ t) - W₀) + (x : ℂ) by ring]
          exact norm_add_le _ _
      _ < ρ₀ / 4 + ρ₀ / 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_lt_add_of_lt_of_le htβ' hx
      _ < ρ₀ := by linarith
  obtain ⟨ε, hε, hfollow⟩ := leaf_follow hS hΦd hΦinj hSH hSne hΦsq hσ
    (by linarith : (0:ℝ) < ρ₀ / 2) hta htS hdev
  set δ : ℝ := W₀.re - (Φ (σ t)).re with hδdef
  have hδsmall : |δ| < ρ₀ / 4 := by
    have h1 : |δ| = |(Φ (σ t) - W₀).re| := by
      rw [hδdef, Complex.sub_re, abs_sub_comm]
    rw [h1]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) htβ'
  have hεδ : |ε * δ| ≤ ρ₀ / 2 := by
    have : |ε * δ| = |δ| := by
      rw [abs_mul]
      rcases hε with h1 | h1 <;> rw [h1] <;> simp
    rw [this]
    linarith
  have hval := hfollow (ε * δ) hεδ
  have hεε : ε * (ε * δ) = δ := by
    rcases hε with h1 | h1 <;> rw [h1] <;> ring
  rw [hεε] at hval
  have hmem : Φ (σ t) + (δ : ℂ) ∈ Φ '' S := hdev δ (by linarith)
  have habsεδ : |ε * δ| = |δ| := by
    rw [abs_mul]
    rcases hε with h1 | h1 <;> rw [h1] <;> simp
  refine ⟨t + ε * δ, ?_, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left, habsεδ]
    exact hδsmall
  · rw [hval]
    exact localFlow_mem hmem
  · rw [hval, localFlow_dev hmem]
    simp [hδdef]
  · rw [hval, localFlow_dev hmem]
    have h2 : (Φ (σ t) + (δ : ℂ)).im = (Φ (σ t)).im := by simp
    rw [h2]
    have h3 : (Φ (σ t)).im - W₀.im = (Φ (σ t) - W₀).im := by simp
    rw [h3]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm _) htβ'

/-- **Vertical chart connection**: two points of a chart box on the central vertical
line at distinct quarter-radius heights are joined by a horizontal trajectory of `−q`
running down the transversal, with interior margin on both sides. -/
theorem vertical_connect {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ z ∈ S, q z ≠ 0)
    (hΦsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z)
    {W₀ : ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (himg : Metric.ball W₀ ρ₀ ⊆ Φ '' S)
    {z₁ z₂ : ℂ} (hz₁S : z₁ ∈ S) (hz₂S : z₂ ∈ S)
    {h₁ h₂ : ℝ} (hΦ₁ : Φ z₁ = (W₀.re : ℂ) + (h₁ : ℂ) * Complex.I)
    (hΦ₂ : Φ z₂ = (W₀.re : ℂ) + (h₂ : ℂ) * Complex.I)
    (hh₁ : |h₁ - W₀.im| < ρ₀ / 4) (hh₂ : |h₂ - W₀.im| < ρ₀ / 4)
    (hne : h₁ ≠ h₂) :
    ∃ τ : ℝ → ℂ, IsTrajOn (fun z => -q z) τ (Set.Icc (-(ρ₀ / 4)) (|h₁ - h₂| + ρ₀ / 4))
      ∧ τ 0 = z₂ ∧ τ |h₁ - h₂| = z₁ := by
  set μ : ℝ := ρ₀ / 4 with hμdef
  have hμ : 0 < μ := by positivity
  set ℓ : ℝ := |h₁ - h₂| with hℓdef
  have hℓ : 0 < ℓ := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hℓle : ℓ < ρ₀ / 2 := by
    have : |h₁ - h₂| ≤ |h₁ - W₀.im| + |W₀.im - h₂| := abs_sub_le _ _ _
    rw [abs_sub_comm W₀.im h₂] at this
    rw [hℓdef]
    linarith
  set Ψ : ℂ → ℂ := fun z => Complex.I * Φ z with hΨdef
  have hΨd : DifferentiableOn ℂ Ψ S := hΦd.const_mul _
  have hΨinj : Set.InjOn Ψ S := by
    intro x hx y hy hxy
    exact hΦinj hx hy (mul_left_cancel₀ Complex.I_ne_zero hxy)
  have hΨsq : ∀ z ∈ S, deriv Ψ z ^ 2 = -(fun z => -q z) z := by
    intro z hz
    have hΦat : DifferentiableAt ℂ Φ z := hΦd.differentiableAt (hS.mem_nhds hz)
    rw [hΨdef]
    simp only
    rw [deriv_const_mul _ hΦat, mul_pow, Complex.I_sq, hΦsq z hz]
    ring
  have hSneN : ∀ z ∈ S, (fun z => -q z) z ≠ 0 := fun z hz =>
    neg_ne_zero.mpr (hSne z hz)
  -- vertical developed points lie in the ball
  have hvert : ∀ c : ℝ, |c| ≤ ℓ + μ → Φ z₂ - Complex.I * (c : ℂ) ∈ Φ '' S := by
    intro c hc
    refine himg (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm]
    have hpt : Φ z₂ - Complex.I * (c : ℂ) - W₀
        = ((h₂ - c - W₀.im : ℝ) : ℂ) * Complex.I := by
      rw [hΦ₂]
      push_cast
      linear_combination Complex.re_add_im W₀
    rw [hpt, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    have h1 : |h₂ - c - W₀.im| ≤ |h₂ - W₀.im| + |c| := by
      rw [show h₂ - c - W₀.im = h₂ - W₀.im - c from by ring]
      exact abs_sub _ _
    calc |h₂ - c - W₀.im| ≤ |h₂ - W₀.im| + |c| := h1
      _ < ρ₀ / 4 + (ℓ + μ) := add_lt_add_of_lt_of_le hh₂ hc
      _ < ρ₀ := by rw [hμdef]; linarith
  have hΨmem : ∀ c : ℝ, |c| ≤ ℓ + μ → Ψ z₂ + ((c : ℝ) : ℂ) ∈ Ψ '' S := by
    intro c hc
    obtain ⟨y, hyS, hy⟩ := hvert c hc
    refine ⟨y, hyS, ?_⟩
    rw [hΨdef]
    simp only
    rw [hy, mul_sub, ← mul_assoc, Complex.I_mul_I]
    ring
  set sgn : ℝ := if h₂ < h₁ then (-1 : ℝ) else 1 with hsgndef
  have hsgn : sgn = 1 ∨ sgn = -1 := by
    rw [hsgndef]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hsgnabs : ∀ x : ℝ, |sgn * x| = |x| := by
    intro x
    rw [abs_mul]
    rcases hsgn with h | h <;> rw [h] <;> simp
  have hsgnℓ : sgn * ℓ = h₂ - h₁ := by
    rw [hsgndef, hℓdef]
    split_ifs with hc
    · rw [abs_of_pos (by linarith : (0:ℝ) < h₁ - h₂)]
      ring
    · have hlt : h₁ < h₂ := lt_of_le_of_ne (not_lt.mp hc) hne
      rw [abs_of_neg (by linarith : h₁ - h₂ < 0)]
      ring
  have hmem0 : Ψ z₂ + ((-(sgn * μ) : ℝ) : ℂ) ∈ Ψ '' S := by
    refine hΨmem _ ?_
    rw [abs_neg, hsgnabs, abs_of_pos hμ]
    linarith
  set zst : ℂ := localFlow Ψ S (-(sgn * μ)) z₂ with hzstdef
  have hzstS : zst ∈ S := localFlow_mem hmem0
  have hzstdev : Ψ zst = Ψ z₂ + ((-(sgn * μ) : ℝ) : ℂ) := localFlow_dev hmem0
  have hL : (0 : ℝ) < ℓ + 2 * μ := by linarith
  have hseg : ∀ u ∈ Set.Icc (0 : ℝ) (ℓ + 2 * μ),
      Ψ zst + ((sgn * u : ℝ) : ℂ) ∈ Ψ '' S := by
    intro u hu
    have hval : Ψ zst + ((sgn * u : ℝ) : ℂ)
        = Ψ z₂ + ((sgn * (u - μ) : ℝ) : ℂ) := by
      rw [hzstdev]
      push_cast
      ring
    rw [hval]
    refine hΨmem _ ?_
    rw [hsgnabs]
    refine abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨-, hτhat, -⟩ := seg_traj (q := fun z => -q z) hS hΨd hΨinj hSH hSneN
    hΨsq hzstS hsgn hL hseg
  have hshift := traj_shift μ hτhat
  have hsetid : (fun u : ℝ => u + μ) ⁻¹' Set.Icc 0 (ℓ + 2 * μ)
      = Set.Icc (-μ) (ℓ + μ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hsetid] at hshift
  have hτeq : ∀ u : ℝ, localFlow Ψ S (sgn * (u + μ)) zst
      = localFlow Ψ S (sgn * u) z₂ := by
    intro u
    rw [hzstdef, localFlow_add hmem0,
      show -(sgn * μ) + sgn * (u + μ) = sgn * u from by ring]
  have hτℓmem : Ψ z₂ + ((sgn * ℓ : ℝ) : ℂ) ∈ Ψ '' S := by
    refine hΨmem _ ?_
    rw [hsgnabs, abs_of_pos hℓ]
    linarith
  refine ⟨fun u => localFlow Ψ S (sgn * (u + μ)) zst, hshift, ?_, ?_⟩
  · change localFlow Ψ S (sgn * (0 + μ)) zst = z₂
    rw [hτeq 0, mul_zero]
    exact localFlow_zero hΨinj hz₂S
  · change localFlow Ψ S (sgn * (ℓ + μ)) zst = z₁
    rw [hτeq ℓ]
    refine hΨinj (localFlow_mem hτℓmem) hz₁S ?_
    rw [localFlow_dev hτℓmem, hΨdef]
    simp only
    rw [hΦ₁, hΦ₂]
    have h5 : ((sgn * ℓ : ℝ) : ℂ) = (h₂ : ℂ) - (h₁ : ℂ) := by
      rw [hsgnℓ]
      push_cast
      ring
    rw [h5]
    linear_combination ((h₂ : ℂ) - (h₁ : ℂ)) * Complex.I_mul_I

/-- **Confined-end exclusion, forward**: under the no-bigon principle — no vertical
trajectory arc and horizontal trajectory arc share both endpoints — an all-time vertical
trajectory cannot keep its forward tail in a compact subset of the upper half plane. -/
theorem confined_tail_false {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im})
    {T₀ : ℝ} (hconf : ∀ t, T₀ ≤ t → σ t ∈ K) : False := by
  obtain ⟨w, hwK, hwim, hwq, hwMCP⟩ := tail_regular_accum hq hσ hK hKH hconf
  obtain ⟨S, Φ, ρ₀, hρ₀, hSopen, hwS, hSH, hSne, hΦd, hΦinj, hΦsq, himg⟩ :=
    box_data hq hwim hwq
  set W₀ : ℂ := Φ w with hW₀def
  set B : Set ℂ := S ∩ Φ ⁻¹' Metric.ball W₀ (ρ₀ / 4) with hBdef
  have hBopen : IsOpen B :=
    hΦd.continuousOn.isOpen_inter_preimage hSopen Metric.isOpen_ball
  have hwB : w ∈ B := ⟨hwS, Metric.mem_ball_self (by positivity)⟩
  have hfreq : ∃ᶠ t in Filter.atTop, σ t ∈ B :=
    mapClusterPt_iff_frequently.mp hwMCP B (hBopen.mem_nhds hwB)
  obtain ⟨t₁, ht₁ge, ht₁B⟩ := Filter.frequently_atTop.mp hfreq (a + ρ₀ + 1)
  obtain ⟨t₂, ht₂ge, ht₂B⟩ := Filter.frequently_atTop.mp hfreq (t₁ + ρ₀ + 1)
  obtain ⟨s₁, hs₁close, hs₁S, hs₁re, hs₁im⟩ := box_crossing hSopen hΦd hΦinj
    hSH hSne hΦsq hρ₀ himg hσ (by linarith) ht₁B.1 ht₁B.2
  obtain ⟨s₂, hs₂close, hs₂S, hs₂re, hs₂im⟩ := box_crossing hSopen hΦd hΦinj
    hSH hSne hΦsq hρ₀ himg hσ (by linarith) ht₂B.1 ht₂B.2
  have hs₁a : a + ρ₀ / 2 < s₁ := by
    have := abs_lt.mp hs₁close
    linarith [this.1]
  have hs₁s₂ : s₁ < s₂ := by
    have h1 := abs_lt.mp hs₁close
    have h2 := abs_lt.mp hs₂close
    linarith [h1.2, h2.1]
  set h₁ : ℝ := (Φ (σ s₁)).im with hh₁def
  set h₂ : ℝ := (Φ (σ s₂)).im with hh₂def
  have hΦs₁ : Φ (σ s₁) = (W₀.re : ℂ) + (h₁ : ℂ) * Complex.I := by
    rw [hh₁def, ← hs₁re]
    exact (Complex.re_add_im _).symm
  have hΦs₂ : Φ (σ s₂) = (W₀.re : ℂ) + (h₂ : ℂ) * Complex.I := by
    rw [hh₂def, ← hs₂re]
    exact (Complex.re_add_im _).symm
  set T : ℝ := s₂ - s₁ with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hσv : ∀ μ : ℝ, 0 < μ → μ ≤ ρ₀ / 4 →
      IsTrajOn q (fun u => σ (u + s₁)) (Set.Icc (-μ) (T + μ)) := by
    intro μ hμ hμle
    refine traj_mono (traj_shift s₁ hσ) ?_
    intro u hu
    simp only [Set.mem_preimage, Set.mem_Ici]
    have := hu.1
    linarith
  by_cases hcase : h₁ = h₂
  · -- coincident crossings: closed vertical loop, degenerate bigon
    have hΦeq : Φ (σ s₁) = Φ (σ s₂) := by rw [hΦs₁, hΦs₂, hcase]
    have hpt : σ s₁ = σ s₂ := hΦinj hs₁S hs₂S hΦeq
    obtain ⟨δs, hδs, τ₀, hτ₀0, hτ₀⟩ := exists_traj_seed (q := fun z => -q z)
      hq.neg (hSH hs₁S) (neg_ne_zero.mpr (hSne _ hs₁S))
    set μ : ℝ := min δs (ρ₀ / 4) with hμdef
    have hμ : 0 < μ := lt_min hδs (by positivity)
    have hμle : μ ≤ ρ₀ / 4 := min_le_right _ _
    have hτh : IsTrajOn (fun z => -q z) τ₀ (Set.Icc (-μ) (0 + μ)) := by
      refine traj_mono hτ₀ ?_
      intro u hu
      have h1 := hu.1
      have h2 := hu.2
      have h3 : μ ≤ δs := min_le_left _ _
      exact ⟨by linarith, by linarith⟩
    refine hbigon (fun u => σ (u + s₁)) τ₀ T 0 μ hT le_rfl hμ
      (hσv μ hμ hμle) hτh ?_ ?_
    · change τ₀ 0 = σ (T + s₁)
      rw [hτ₀0, hTdef, sub_add_cancel, hpt]
    · change τ₀ 0 = σ (0 + s₁)
      rw [hτ₀0, zero_add]
  · -- distinct heights: vertical chart connection, genuine bigon
    obtain ⟨τ, hτtraj, hτ0, hτℓ⟩ := vertical_connect hSopen hΦd hΦinj hSH
      hSne hΦsq hρ₀ himg hs₁S hs₂S hΦs₁ hΦs₂ hs₁im hs₂im hcase
    have hμ : (0 : ℝ) < ρ₀ / 4 := by positivity
    refine hbigon (fun u => σ (u + s₁)) τ T |h₁ - h₂| (ρ₀ / 4) hT (abs_nonneg _)
      hμ (hσv _ hμ le_rfl) hτtraj ?_ ?_
    · change τ 0 = σ (T + s₁)
      rw [hτ0, hTdef, sub_add_cancel]
    · change τ |h₁ - h₂| = σ (0 + s₁)
      rw [hτℓ, zero_add]

/-- **Confined-end exclusion, backward**: under the same no-bigon principle, an all-time
vertical trajectory cannot keep its backward tail in a compact subset of the upper half
plane. -/
theorem confined_tail_false_bwd {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Iic a))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im})
    {T₀ : ℝ} (hconf : ∀ t, t ≤ T₀ → σ t ∈ K) : False := by
  have hpre : (fun u : ℝ => -u) ⁻¹' Set.Iic a = Set.Ici (-a) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  have hσ' : IsTrajOn q (fun u => σ (-u)) (Set.Ici (-a)) := by
    have := traj_reverse hσ
    rwa [hpre] at this
  exact confined_tail_false hq hbigon hσ' hK hKH
    (T₀ := -T₀) (fun t ht => hconf (-t) (by linarith))

/-- The competitor–trajectory loop: the competitor on the first half, the reversed and
clamped trajectory arc on the second half. -/
noncomputable def leafLoop (p : C(unitInterval, ℂ)) (f : ℝ → ℂ) (T : ℝ) : ℝ → ℂ := fun s =>
  if s ≤ 1 / 2 then p (Set.projIcc 0 1 zero_le_one (2 * s))
  else f (min 1 (2 - 2 * s) * T)

/-- The bundled loop, continuous once the junction values agree. -/
noncomputable def leafLoopC (p : C(unitInterval, ℂ)) (f : ℝ → ℂ) (T : ℝ)
    (hfc : ContinuousOn f (Set.Icc 0 T)) (hT : 0 ≤ T) (hm : p 1 = f T) :
    C(unitInterval, ℂ) := by
  refine ⟨fun s : unitInterval => leafLoop p f T s, ?_⟩
  have hf' : Continuous fun s : unitInterval => p (Set.projIcc 0 1 zero_le_one (2 * (s : ℝ))) :=
    p.continuous.comp (continuous_projIcc.comp (by fun_prop))
  have hmaps : ∀ s : unitInterval, min 1 (2 - 2 * (s : ℝ)) * T ∈ Set.Icc 0 T := by
    intro s
    have h1 := s.2.1
    have h2 := s.2.2
    constructor
    · have : (0 : ℝ) ≤ min 1 (2 - 2 * (s : ℝ)) := le_min (by linarith) (by linarith)
      positivity
    · have : min 1 (2 - 2 * (s : ℝ)) ≤ 1 := min_le_left _ _
      nlinarith
  have hg' : Continuous fun s : unitInterval => f (min 1 (2 - 2 * (s : ℝ)) * T) := by
    refine hfc.comp_continuous ?_ hmaps
    fun_prop
  refine Continuous.if_le hf' hg' continuous_subtype_val continuous_const ?_
  intro s hs
  have h2s : 2 * (s : ℝ) = 1 := by rw [hs]; ring
  rw [h2s]
  norm_num
  exact hm

/-- Values of the loop: each point is a competitor value or a trajectory value at a
time in `[0, T]`. -/
theorem leafLoop_cases (p : C(unitInterval, ℂ)) (f : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (s : unitInterval) :
    (∃ s' : unitInterval, leafLoop p f T s = p s') ∨
    (∃ v : ℝ, v ∈ Set.Icc 0 T ∧ leafLoop p f T s = f v) := by
  rw [leafLoop]
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · refine Or.inr ⟨min 1 (2 - 2 * (s : ℝ)) * T, ⟨?_, ?_⟩, rfl⟩
    · have h1 := s.2.2
      have : (0 : ℝ) ≤ min 1 (2 - 2 * (s : ℝ)) := le_min (by linarith) (by linarith)
      positivity
    · have : min 1 (2 - 2 * (s : ℝ)) ≤ 1 := min_le_left _ _
      nlinarith [s.2.1]

/-- The loop closes at the trajectory start. -/
theorem leafLoop_closed (p : C(unitInterval, ℂ)) (f : ℝ → ℂ) (T : ℝ)
    (hfc : ContinuousOn f (Set.Icc 0 T)) (hT : 0 ≤ T) (hm : p 1 = f T)
    (h0 : p 0 = f 0) :
    leafLoopC p f T hfc hT hm 0 = leafLoopC p f T hfc hT hm 1 := by
  change leafLoop p f T ((0 : unitInterval) : ℝ)
    = leafLoop p f T ((1 : unitInterval) : ℝ)
  rw [leafLoop, leafLoop]
  norm_num
  exact h0

/-- **Global crossing uniqueness**: under the no-bigon principle in both chiralities, a
vertical trajectory and an all-time transverse leaf meet in at most one parameter
pair — two crossings would close a vertical-horizontal bigon, and a repeated leaf
parameter would close a horizontal loop against a vertical seed. -/
theorem leaf_cross_once {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn q σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -q z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -q z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn q τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    {σ : ℝ → ℂ} {a : ℝ} (hσ : IsTrajOn q σ (Set.Ici a))
    {τ : ℝ → ℂ} (hτ : IsTrajOn (fun z => -q z) τ Set.univ)
    {t₁ t₂ u₁ u₂ : ℝ} (ht₁ : a < t₁) (ht₂ : a < t₂)
    (h₁ : σ t₁ = τ u₁) (h₂ : σ t₂ = τ u₂) : t₁ = t₂ ∧ u₁ = u₂ := by
  have hτshift : ∀ c : ℝ, IsTrajOn (fun z => -q z) (fun v => τ (v + c)) Set.univ := by
    intro c
    have := traj_shift c hτ
    rwa [Set.preimage_univ] at this
  have hτrevs : ∀ c : ℝ, IsTrajOn (fun z => -q z) (fun v => τ (c - v)) Set.univ := by
    intro c
    have h1 := traj_shift (-c) (traj_reverse hτ)
    rw [Set.preimage_univ, Set.preimage_univ] at h1
    have hfun : (fun v : ℝ => (fun w : ℝ => τ (-w)) (v + -c)) = fun v => τ (c - v) := by
      funext v
      change τ (-(v + -c)) = τ (c - v)
      congr 1
      ring
    rwa [hfun] at h1
  have key : ∀ tl tr ul ur : ℝ, a < tl → tl < tr →
      σ tl = τ ul → σ tr = τ ur → False := by
    intro tl tr ul ur htl htlr hl hr
    set T' : ℝ := tr - tl with hT'def
    have hT' : 0 < T' := by rw [hT'def]; linarith
    set μ : ℝ := min 1 (tl - a) with hμdef
    have hμ : 0 < μ := lt_min one_pos (by linarith)
    have hσv : IsTrajOn q (fun v => σ (v + tl)) (Set.Icc (-μ) (T' + μ)) := by
      refine traj_mono (traj_shift tl hσ) ?_
      intro v hv
      simp only [Set.mem_preimage, Set.mem_Ici]
      have h3 : μ ≤ tl - a := min_le_right _ _
      have := hv.1
      linarith
    have hσvT : σ (T' + tl) = τ ur := by
      rw [hT'def, sub_add_cancel]
      exact hr
    have hσv0 : σ (0 + tl) = τ ul := by
      rw [zero_add]
      exact hl
    rcases le_total ur ul with hu | hu
    · refine hbigon _ (fun v => τ (v + ur)) T' (ul - ur) μ hT'
        (by linarith) hμ hσv (traj_mono (hτshift ur) (Set.subset_univ _)) ?_ ?_
      · change τ (0 + ur) = σ (T' + tl)
        rw [zero_add]
        exact hσvT.symm
      · change τ (ul - ur + ur) = σ (0 + tl)
        rw [sub_add_cancel]
        exact hσv0.symm
    · refine hbigon _ (fun v => τ (ur - v)) T' (ur - ul) μ hT'
        (by linarith) hμ hσv (traj_mono (hτrevs ur) (Set.subset_univ _)) ?_ ?_
      · change τ (ur - 0) = σ (T' + tl)
        rw [sub_zero]
        exact hσvT.symm
      · change τ (ur - (ur - ul)) = σ (0 + tl)
        rw [show ur - (ur - ul) = ul from by ring]
        exact hσv0.symm
  have key2 : ∀ t ul ur : ℝ, a < t → ul < ur →
      σ t = τ ul → σ t = τ ur → False := by
    intro t ul ur ht hu hl hr
    obtain ⟨him, hqne⟩ := traj_regular hσ (Set.mem_Ici.mpr ht.le)
    obtain ⟨δ, hδ, τ₀, hτ₀0, hτ₀⟩ := exists_traj_seed hq him hqne
    set T' : ℝ := ur - ul with hT'def
    have hT' : 0 < T' := by rw [hT'def]; linarith
    have hσv : IsTrajOn (fun z => -q z) (fun v => τ (v + ul))
        (Set.Icc (-δ) (T' + δ)) := traj_mono (hτshift ul) (Set.subset_univ _)
    have hτh : IsTrajOn q τ₀ (Set.Icc (-δ) (0 + δ)) := by
      refine traj_mono hτ₀ ?_
      intro v hv
      exact ⟨hv.1, by linarith [hv.2]⟩
    refine hbigonH _ τ₀ T' 0 δ hT' le_rfl hδ hσv hτh ?_ ?_
    · show τ₀ 0 = τ (T' + ul)
      rw [hτ₀0, hT'def, sub_add_cancel]
      exact hr
    · show τ₀ 0 = τ (0 + ul)
      rw [hτ₀0, zero_add]
      exact hl
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · exact absurd (key t₁ t₂ u₁ u₂ ht₁ hlt h₁ h₂) (fun h => h)
  · subst heq
    refine ⟨rfl, ?_⟩
    rcases lt_trichotomy u₁ u₂ with hu | hu | hu
    · exact absurd (key2 t₁ u₁ u₂ ht₁ hu h₁ h₂) (fun h => h)
    · exact hu
    · exact absurd (key2 t₁ u₂ u₁ ht₁ hu h₂ h₁) (fun h => h)
  · exact absurd (key t₂ t₁ u₂ u₁ ht₂ hgt h₂ h₁) (fun h => h)

end RiemannDynamics
