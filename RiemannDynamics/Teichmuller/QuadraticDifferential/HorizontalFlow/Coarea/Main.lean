/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Coarea.Discharge

/-!
# The Reich-Strebel main inequality

The nearest-point reach and the two-value dichotomy complete the nonnegative-winding
principle; composing it with the conditional form yields the Reich-Strebel main
inequality, together with the weight-algebra bricks consumed by the extremality tier.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **The separation inequality from the atlas-threaded displacement estimate**. -/
theorem hsep_of_displacement {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (q : ℂ → ℂ) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (q : ℂ → ℂ) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hjump : ∀ (ϑ : ℝ → ℂ) (a : ℝ) (hϑ : IsTrajOn (q : ℂ → ℂ) ϑ (Set.Ici a))
      (ha : a < 0) (T : ℝ) (hT : 0 < T) (τ : ℝ → ℂ),
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ Set.univ →
      ∀ tstar : ℝ, tstar ∈ Set.Ioo 0 T → τ 0 = ϑ tstar →
      ∀ (p : C(unitInterval, ℂ)), p 0 = ϑ 0 → ∀ hp1 : p 1 = ϑ T,
      (∀ s : unitInterval, 0 < (p s).im) →
      (∀ (s : unitInterval) (u : ℝ), p s ≠ τ u) →
      ∃ η : ℝ, 0 < η ∧
        (windingNumber (leafLoopC p ϑ T
            (hϑ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1) (τ η) ≠ 0 ∨
         windingNumber (leafLoopC p ϑ T
            (hϑ.cont.mono fun _ hx => le_trans ha.le hx.1) hT.le hp1)
              (τ (-η)) ≠ 0))
    (hcoarea₄ : ∀ ϑ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) ϑ Set.univ →
      ∀ B : Atlas (qdNeg q : ℂ → ℂ),
      (∀ᵐ t ∂(volume : Measure ℝ), ϑ t ∈ good (qdNeg q : ℂ → ℂ) B) →
      ∀ T : ℝ, 0 < T → Set.InjOn ϑ (Set.Icc 0 T) →
      ∀ p : ℝ → ℂ, IsFlatPath p (ϑ 0) (ϑ T) →
      ∀ (t₀ t₁ s₀ s₁ : ℝ) (τ₀ τ₁ : ℝ → ℂ),
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ₀ Set.univ →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ₁ Set.univ →
      τ₀ 0 = ϑ t₀ → τ₁ 0 = ϑ t₁ →
      t₀ ∈ Set.Ioo 0 T → t₁ ∈ Set.Ioo 0 T →
      s₀ ∈ Set.Icc (0 : ℝ) 1 → s₁ ∈ Set.Icc (0 : ℝ) 1 →
      (∃ u, p s₀ = τ₀ u) → (∃ u, p s₁ = τ₁ u) →
      ENNReal.ofReal |t₁ - t₀| ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1,
        horizontalDensity (q : ℂ → ℂ) p s) :
    ∀ A : Atlas (q : ℂ → ℂ),
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, σ 0 = z →
      IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      ENNReal.ofReal T ≤ horizontalDist (q : ℂ → ℂ) (σ 0) (σ T) := by
  intro A
  obtain ⟨B⟩ := exists_atlas (qdNeg q).holo
  filter_upwards [flow_good_neg_ae hΓ hcc q hq0 A B] with z hzimp
  intro hzg T hT σ hσ0 hσtr
  have hzim : 0 < z.im := hzg.1
  have hz0 : (q : ℂ → ℂ) z ≠ 0 := hzg.2.1
  have hflowae := hzimp hzg
  have hϑuniv : IsTrajOn (q : ℂ → ℂ) (fun u => A.flow u z) Set.univ :=
    flow_alltime q.holo A hzg
  have key : ∀ ϑ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) ϑ Set.univ →
      (∀ u ∈ Set.Icc 0 T, ϑ u = σ u) →
      (∀ᵐ t ∂(volume : Measure ℝ), ϑ t ∈ good (qdNeg q : ℂ → ℂ) B) →
      ENNReal.ofReal T ≤ horizontalDist (q : ℂ → ℂ) (σ 0) (σ T) := by
    intro ϑ hϑ hagree hae
    have h00 : ϑ 0 = σ 0 := hagree 0 ⟨le_rfl, hT.le⟩
    have hTT : ϑ T = σ T := hagree T ⟨hT.le, le_rfl⟩
    rw [← h00, ← hTT]
    have hinj : Set.InjOn ϑ (Set.Icc 0 T) := by
      refine traj_injOn q.holo hbigon (m := 1) one_pos ?_
      exact traj_mono hϑ (Set.subset_univ _)
    set D : Set ℝ := Set.Ioo 0 T ∩ {t | ϑ t ∈ good (qdNeg q : ℂ → ℂ) B}
      with hDdef
    have hDsub : D ⊆ Set.Ioo 0 T := Set.inter_subset_left
    have hDae : volume ({t | ¬ ϑ t ∈ good (qdNeg q : ℂ → ℂ) B}) = 0 :=
      ae_iff.mp hae
    have hDmeet : ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ T →
        (D ∩ Set.Ioo α β).Nonempty := by
      intro α β hα hαβ hβT
      by_contra hemp
      push Not at hemp
      have hsub : Set.Ioo α β ⊆ {t | ¬ ϑ t ∈ good (qdNeg q : ℂ → ℂ) B} := by
        intro t ht hg
        have hmem : t ∈ D ∩ Set.Ioo α β :=
          ⟨⟨⟨lt_of_le_of_lt hα ht.1, lt_of_lt_of_le ht.2 hβT⟩, hg⟩, ht⟩
        rw [hemp] at hmem
        exact hmem
      have h1 : volume (Set.Ioo α β) = 0 :=
        measure_mono_null hsub hDae
      rw [Real.volume_Ioo] at h1
      have h2 : (0 : ℝ) < β - α := by linarith
      rw [ENNReal.ofReal_eq_zero] at h1
      linarith
    set τfam : ℝ → ℝ → ℂ := fun t u => B.flow u (ϑ t) with hτfamdef
    have hτfam : ∀ t ∈ D, IsTrajOn (fun w => -(q : ℂ → ℂ) w) (τfam t) Set.univ ∧
        τfam t 0 = ϑ t := by
      intro t ht
      have hgood : ϑ t ∈ good (qdNeg q : ℂ → ℂ) B := ht.2
      exact ⟨isTrajOn_congr (fun w => qdNeg_apply q w)
        (flow_alltime (qdNeg q).holo B hgood), flow_zero B hgood.1 hgood.2.1⟩
    rw [horizontalDist]
    refine le_iInf₂ fun p hp => ?_
    have hcross : ∀ t ∈ D, ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ u : ℝ,
        p s = τfam t u := by
      intro t ht
      set pC : C(unitInterval, ℂ) := ⟨fun s => p s,
        hp.cont.comp_continuous continuous_subtype_val (fun s => s.2)⟩ with hpCdef
      have hϑIci : IsTrajOn (q : ℂ → ℂ) ϑ (Set.Ici (-1 : ℝ)) :=
        traj_mono hϑ (Set.subset_univ _)
      have hp0' : pC 0 = ϑ 0 := hp.init
      have hp1' : pC 1 = ϑ T := hp.final
      have hpim' : ∀ s : unitInterval, 0 < (pC s).im := fun s =>
        hp.upper s s.2
      obtain ⟨s, u, hsu⟩ := competitor_crosses_leaf q.holo hbigon hbigonH hϑIci
        (by norm_num) hT (hτfam t ht).1 (hDsub ht) (hτfam t ht).2 pC hp0' hp1'
        hpim' (hjump ϑ (-1) hϑIci (by norm_num) T hT (τfam t) (hτfam t ht).1 t
          (hDsub ht) (hτfam t ht).2 pC hp0' hp1' hpim')
      exact ⟨(s : ℝ), s.2, u, hsu⟩
    -- the squeeze over levels near the window ends
    have hstep : ∀ n : ℕ, ENNReal.ofReal (T - 2 * (T / (2 * ((n : ℝ) + 2))))
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1, horizontalDensity (q : ℂ → ℂ) p s := by
      intro n
      set εn : ℝ := T / (2 * ((n : ℝ) + 2)) with hεndef
      have hεn : 0 < εn := by positivity
      have hεnT : εn < T / 2 := by
        rw [hεndef]
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      obtain ⟨t₀, ht₀D, ht₀I⟩ := hDmeet 0 εn le_rfl hεn (by linarith)
      obtain ⟨t₁, ht₁D, ht₁I⟩ := hDmeet (T - εn) T (by linarith) (by linarith)
        le_rfl
      obtain ⟨s₀, hs₀I, u₀, hu₀⟩ := hcross t₀ ht₀D
      obtain ⟨s₁, hs₁I, u₁, hu₁⟩ := hcross t₁ ht₁D
      have hbound := hcoarea₄ ϑ hϑ B hae T hT hinj p hp t₀ t₁ s₀ s₁ (τfam t₀)
        (τfam t₁) (hτfam t₀ ht₀D).1 (hτfam t₁ ht₁D).1 (hτfam t₀ ht₀D).2
        (hτfam t₁ ht₁D).2 (hDsub ht₀D) (hDsub ht₁D) hs₀I hs₁I ⟨u₀, hu₀⟩
        ⟨u₁, hu₁⟩
      have hgap : T - 2 * εn ≤ |t₁ - t₀| := by
        have h1 : t₀ < εn := ht₀I.2
        have h2 : T - εn < t₁ := ht₁I.1
        have h3 : T - 2 * εn ≤ t₁ - t₀ := by linarith
        exact le_trans h3 (le_abs_self _)
      exact le_trans (ENNReal.ofReal_le_ofReal hgap) hbound
    have htend : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (T - 2 * (T / (2 * ((n : ℝ) + 2)))))
        Filter.atTop (𝓝 (ENNReal.ofReal T)) := by
      refine (ENNReal.continuous_ofReal.tendsto T).comp ?_
      have h1 : Filter.Tendsto (fun n : ℕ => T / (2 * ((n : ℝ) + 2)))
          Filter.atTop (𝓝 0) := by
        refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
        have h2 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop
            Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        exact h2.const_mul_atTop (by norm_num)
      have h3 := h1.const_mul (2 : ℝ)
      have h4 := (tendsto_const_nhds (x := T)
        (f := Filter.atTop (α := ℕ))).sub h3
      simpa using h4
    exact le_of_tendsto' htend hstep
  rcases traj_flow_eval q.holo A hzim hz0 hT hσ0 hσtr with hor | hor
  · exact key (fun u => A.flow u z) hϑuniv (fun u hu => hor u hu) hflowae
  · have hrev := traj_reverse hϑuniv
    rw [Set.preimage_univ] at hrev
    exact key (fun u => A.flow (-u) z) hrev (fun u hu => hor u hu)
      (ae_neg_volume hflowae)

/-- **The Reich–Strebel main inequality from the exclusion principles**: the bigon exclusions in
both chiralities and the atlas-threaded two-point leaf-displacement estimate imply the
main inequality; the winding jump is supplied by the proven crossing theorem. -/
theorem reich_strebel_of_principles {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (hbd : ∀ t : ℝ, Filter.Tendsto h (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
      (nhds (t : ℂ)))
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (hbigon : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (q : ℂ → ℂ) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hbigonH : ∀ (σv τh : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) σv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (q : ℂ → ℂ) τh (Set.Icc (-μ) (s + μ)) →
      τh 0 = σv T → τh s = σv 0 → False)
    (hcoarea₄ : ∀ ϑ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) ϑ Set.univ →
      ∀ B : Atlas (qdNeg q : ℂ → ℂ),
      (∀ᵐ t ∂(volume : Measure ℝ), ϑ t ∈ good (qdNeg q : ℂ → ℂ) B) →
      ∀ T : ℝ, 0 < T → Set.InjOn ϑ (Set.Icc 0 T) →
      ∀ p : ℝ → ℂ, IsFlatPath p (ϑ 0) (ϑ T) →
      ∀ (t₀ t₁ s₀ s₁ : ℝ) (τ₀ τ₁ : ℝ → ℂ),
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ₀ Set.univ →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) τ₁ Set.univ →
      τ₀ 0 = ϑ t₀ → τ₁ 0 = ϑ t₁ →
      t₀ ∈ Set.Ioo 0 T → t₁ ∈ Set.Ioo 0 T →
      s₀ ∈ Set.Icc (0 : ℝ) 1 → s₁ ∈ Set.Icc (0 : ℝ) 1 →
      (∃ u, p s₀ = τ₀ u) → (∃ u, p s₁ = τ₁ u) →
      ENNReal.ofReal |t₁ - t₀| ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1,
        horizontalDensity (q : ℂ → ℂ) p s) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  by_cases hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ (q : ℂ → ℂ) z₀ ≠ 0
  · exact reich_strebel_of_hsep hΓ hfree hcc q hκ hqc hbd hcomm
      (hsep_of_displacement hΓ hcc q hq0 hbigon hbigonH
        (hjump_of_bigons q.holo hbigon hbigonH) hcoarea₄)
  · push Not at hq0
    have hmeas : MeasurableSet
        (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I) :=
      (isCompact_domain hΓ hfree hcc).measurableSet
    rw [l1Norm_eq_zero q hmeas hq0]
    exact zero_le

/-- **The Reich–Strebel main inequality from the nonnegative-winding principle.** Let
`Γ` be a cocompact free Fuchsian group, `q` an automorphic quadratic differential, and
`h` an upper-half-plane quasiconformal map commuting with `Γ` elementwise whose
boundary limits are the identity on `ℝ`. Then the `L¹` mass of `q` is dominated by the
integral, over the Dirichlet domain, of `|q| · ‖1 − μ_h q/|q|‖²/(1 − ‖μ_h‖²)` formed
from the Wirtinger quotient of `h`. -/
theorem rs_main_of_principle
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (hbd : ∀ t : ℝ, Filter.Tendsto h (nhdsWithin (t : ℂ) {z : ℂ | 0 < z.im})
      (nhds (t : ℂ)))
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (hW : NonnegWindingPrinciple₂) :
    q.l1Norm ≤ ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
      ‖q z‖ₑ * ENNReal.ofReal
        (‖1 - wirtingerQuotient h z * (q z / (‖q z‖ : ℂ))‖ ^ 2
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) := by
  have hbigon : ∀ (sv th : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (q : ℂ → ℂ) sv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) th (Set.Icc (-μ) (s + μ)) →
      th 0 = sv T → th s = sv 0 → False := by
    intro sv th T s μ hT hs hμ hσ hτ hc1 hc2
    have hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ (q : ℂ → ℂ) z₀ ≠ 0 := by
      obtain ⟨U, -, hpU, hUH, hUne, -⟩ :=
        hσ.chart 0 ⟨by linarith, by linarith⟩
      exact ⟨sv 0, hUH hpU, hUne _ hpU⟩
    exact bigon_principle₂ q.holo hq0 hW sv th T s μ hT hs hμ hσ hτ hc1 hc2
  have hbigonH : ∀ (sv th : ℝ → ℂ) (T s μ : ℝ), 0 < T → 0 ≤ s → 0 < μ →
      IsTrajOn (fun z => -(q : ℂ → ℂ) z) sv (Set.Icc (-μ) (T + μ)) →
      IsTrajOn (q : ℂ → ℂ) th (Set.Icc (-μ) (s + μ)) →
      th 0 = sv T → th s = sv 0 → False := by
    intro sv th T s μ hT hs hμ hσ hτ hc1 hc2
    have hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ (q : ℂ → ℂ) z₀ ≠ 0 := by
      obtain ⟨U, -, hpU, hUH, hUne, -⟩ :=
        hτ.chart 0 ⟨by linarith, by linarith⟩
      exact ⟨th 0, hUH hpU, hUne _ hpU⟩
    exact bigon_principleH₂ q.holo hq0 hW sv th T s μ hT hs hμ hσ hτ hc1 hc2
  exact reich_strebel_of_principles hΓ hfree hcc q hκ hqc hbd hcomm hbigon hbigonH
    (hcoarea_of_bigons q hbigon hbigonH)

section PinDischarge

open unitInterval

/-- **First variation at a periodic minimum**: a function with wrap-matched values and
derivatives on the period has vanishing derivative at any minimum over the period. -/
theorem loop_min_deriv_zero {φ ψ : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (ψ t) t)
    (hφcl : φ 0 = φ 1) (hψcl : ψ 1 = ψ 0) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t₀ ≤ φ t) :
    ψ t₀ = 0 := by
  rcases lt_or_eq_of_le ht₀.1 with h0 | h0
  · rcases lt_or_eq_of_le ht₀.2 with h1 | h1
    · -- interior minimum
      have hloc : IsLocalMin φ t₀ := by
        have hmem : Set.Icc (0 : ℝ) 1 ∈ nhds t₀ := Icc_mem_nhds h0 h1
        exact Filter.eventually_iff_exists_mem.mpr ⟨_, hmem, fun t ht => hmin t ht⟩
      exact hloc.hasDerivAt_eq_zero (hd t₀ ht₀)
    · -- minimum at the right endpoint: both endpoints are minima
      have hm0 : φ 0 = φ t₀ := by rw [hφcl, h1]
      have hge : 0 ≤ ψ 0 := by
        have h1' : HasDerivWithinAt φ (ψ 0) (Set.Ioc 0 1) 0 :=
          (hd 0 (by norm_num)).hasDerivWithinAt
        rw [hasDerivWithinAt_iff_tendsto_slope] at h1'
        have h2 : Set.Ioc (0 : ℝ) 1 \ {0} = Set.Ioc 0 1 := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_singleton_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, by linarith [h.1]⟩⟩
        rw [h2] at h1'
        have := left_nhdsWithin_Ioc_neBot (by norm_num : (0 : ℝ) < 1)
        refine ge_of_tendsto h1' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [slope_def_field]
        have h3 : φ 0 ≤ φ t := by rw [hm0]; exact hmin t ⟨ht.1.le, ht.2⟩
        have h4 : 0 < t - 0 := by linarith [ht.1]
        exact div_nonneg (by linarith) (by linarith)
      have hle : ψ 1 ≤ 0 := by
        have h1' : HasDerivWithinAt φ (ψ 1) (Set.Ico 0 1) 1 :=
          (hd 1 (by norm_num)).hasDerivWithinAt
        rw [hasDerivWithinAt_iff_tendsto_slope] at h1'
        have h2 : Set.Ico (0 : ℝ) 1 \ {1} = Set.Ico 0 1 := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_singleton_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, by linarith [h.2]⟩⟩
        rw [h2] at h1'
        have := right_nhdsWithin_Ico_neBot (by norm_num : (0 : ℝ) < 1)
        refine le_of_tendsto h1' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [slope_def_field]
        have h3 : φ 1 ≤ φ t := by rw [← h1]; exact hmin t ⟨ht.1, ht.2.le⟩
        have h4 : t - 1 < 0 := by linarith [ht.2]
        exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      rw [hψcl] at hle
      have : ψ 0 = 0 := le_antisymm hle hge
      rw [h1, hψcl]
      exact this
  · -- minimum at the left endpoint: symmetric squeeze
    have hm1 : φ 1 = φ t₀ := by rw [← hφcl, h0]
    have hge : 0 ≤ ψ 0 := by
      have h1' : HasDerivWithinAt φ (ψ 0) (Set.Ioc 0 1) 0 :=
        (hd 0 (by norm_num)).hasDerivWithinAt
      rw [hasDerivWithinAt_iff_tendsto_slope] at h1'
      have h2 : Set.Ioc (0 : ℝ) 1 \ {0} = Set.Ioc 0 1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ioc, Set.mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, by linarith [h.1]⟩⟩
      rw [h2] at h1'
      have := left_nhdsWithin_Ioc_neBot (by norm_num : (0 : ℝ) < 1)
      refine ge_of_tendsto h1' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field]
      have h3 : φ 0 ≤ φ t := by rw [h0]; exact hmin t ⟨ht.1.le, ht.2⟩
      have h4 : 0 < t - 0 := by linarith [ht.1]
      exact div_nonneg (by linarith) (by linarith)
    have hle : ψ 1 ≤ 0 := by
      have h1' : HasDerivWithinAt φ (ψ 1) (Set.Ico 0 1) 1 :=
        (hd 1 (by norm_num)).hasDerivWithinAt
      rw [hasDerivWithinAt_iff_tendsto_slope] at h1'
      have h2 : Set.Ico (0 : ℝ) 1 \ {1} = Set.Ico 0 1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, by linarith [h.2]⟩⟩
      rw [h2] at h1'
      have := right_nhdsWithin_Ico_neBot (by norm_num : (0 : ℝ) < 1)
      refine le_of_tendsto h1' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [slope_def_field]
      have h3 : φ 1 ≤ φ t := by rw [hm1]; exact hmin t ⟨ht.1, ht.2.le⟩
      have h4 : t - 1 < 0 := by linarith [ht.2]
      exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    rw [hψcl] at hle
    rw [← h0, le_antisymm hle hge]

/-- **Winding under recentering**: the winding of a closed curve about a point equals the
winding of the recentered curve about the origin. -/
theorem winding_shift {γ : C(I, ℂ)} {p : ℂ} (hcl : γ 0 = γ 1)
    (hne : ∀ t : I, γ t ≠ p) (A : C(I, ℂ)) (hA : ∀ t : I, A t = γ t - p) :
    windingNumber A 0 = windingNumber γ p := by
  have hclA : A 0 = A 1 := by rw [hA 0, hA 1, hcl]
  have hneA : ∀ t : I, A t ≠ 0 := fun t => by
    rw [hA t]
    exact sub_ne_zero.mpr (hne t)
  have hs : shiftedCurve γ p = shiftedCurve A 0 := by
    apply ContinuousMap.ext
    intro t
    have h1 : shiftedCurve A 0 t = A t - 0 := by simp [shiftedCurve]
    have h2 : shiftedCurve γ p t = γ t - p := by simp [shiftedCurve]
    rw [h1, h2, hA t, sub_zero]
  have hsne : ∀ t : I, shiftedCurve γ p t ≠ 0 := by
    intro t
    have h2 : shiftedCurve γ p t = γ t - p := by simp [shiftedCurve]
    rw [h2]
    exact sub_ne_zero.mpr (hne t)
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ p) hsne
  have hspec1 := windingNumber_spec hcl hne hL
  have hL' : IsLogLiftOf L (shiftedCurve A 0) := by
    rw [← hs]
    exact hL
  have hspec2 := windingNumber_spec hclA hneA hL'
  rw [hspec1] at hspec2
  have h2πi : (2 * (Real.pi : ℂ) * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hcan := mul_left_cancel₀ h2πi hspec2
  exact_mod_cast hcan.symm

/-- **Normal decomposition**: a vector orthogonal to a nonzero vector is a real multiple
of its quarter-turn rotation. -/
theorem normal_decomp {w v : ℂ} (hv : v ≠ 0)
    (h : w.re * v.re + w.im * v.im = 0) :
    ∃ s : ℝ, w = (s : ℂ) * (Complex.I * v) := by
  have hns : (0 : ℝ) < Complex.normSq v := Complex.normSq_pos.mpr hv
  have hns' : Complex.normSq v ≠ 0 := ne_of_gt hns
  set s := (w.im * v.re - w.re * v.im) / Complex.normSq v with hsdef
  refine ⟨s, ?_⟩
  have hIv : (Complex.I * v).re = -v.im := by simp [Complex.mul_re]
  have hIv' : (Complex.I * v).im = v.re := by simp [Complex.mul_im]
  apply Complex.ext
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hIv, hIv', zero_mul,
      sub_zero, hsdef, div_mul_eq_mul_div, eq_div_iff hns', Complex.normSq_apply]
    linear_combination (v.re : ℝ) * h
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hIv, hIv', zero_mul,
      add_zero, hsdef, div_mul_eq_mul_div, eq_div_iff hns', Complex.normSq_apply]
    linear_combination (v.im : ℝ) * h

/-- **Derivative gluing at a seam**: two functions with equal value and equal derivative
at a point glue along it to a differentiable piecewise function. -/
theorem glue_deriv {F₁ F₂ : ℝ → ℂ} {d : ℂ} {a : ℝ}
    (h1 : HasDerivAt F₁ d a) (h2 : HasDerivAt F₂ d a) (heq : F₁ a = F₂ a) :
    HasDerivAt (fun t => if t ≤ a then F₁ t else F₂ t) d a := by
  have hIic : HasDerivWithinAt (fun t => if t ≤ a then F₁ t else F₂ t) d (Set.Iic a) a := by
    refine (h1.hasDerivWithinAt).congr ?_ ?_
    · intro y hy
      rw [if_pos (Set.mem_Iic.mp hy)]
    · rw [if_pos le_rfl]
  have hIci : HasDerivWithinAt (fun t => if t ≤ a then F₁ t else F₂ t) d (Set.Ici a) a := by
    refine (h2.hasDerivWithinAt).congr ?_ ?_
    · intro y hy
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with h | h
      · rw [if_pos h.symm.le, ← h, heq]
      · rw [if_neg (not_le.mpr h)]
    · rw [if_pos le_rfl, heq]
  have hu := hIic.union hIci
  rw [Set.Iic_union_Ici] at hu
  exact hasDerivWithinAt_univ.mp hu

/-- **Rebased derivative**: the wrap-shift of a closed curve with wrap-matched derivative
differentiates to the wrap-shift of the derivative throughout the period. -/
theorem rebase_deriv {ρ g : ℝ → ℂ} {c : ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ρ (g t) t)
    (hcl : ρ 0 = ρ 1) (hgcl : g 1 = g 0) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun u => if u + c ≤ 1 then ρ (u + c) else ρ (u + c - 1))
        (if t + c ≤ 1 then g (t + c) else g (t + c - 1)) t := by
  intro t ht
  have hfun2 : (fun x : ℝ => ρ (x + (c - 1))) = fun x => ρ (x + c - 1) := by
    funext x
    congr 1
    ring
  rcases lt_trichotomy (t + c) 1 with hlt | heq | hgt
  · have hd1 : HasDerivAt (fun u => ρ (u + c)) (g (t + c)) t :=
      HasDerivAt.comp_add_const t c
        (hd (t + c) ⟨by linarith [ht.1, hc.1], le_of_lt hlt⟩)
    rw [if_pos (le_of_lt hlt)]
    refine hd1.congr_of_eventuallyEq ?_
    have hmem : Set.Iio (1 - c) ∈ nhds t := Iio_mem_nhds (by linarith)
    filter_upwards [hmem] with u hu
    rw [if_pos (by linarith [Set.mem_Iio.mp hu])]
  · have hF1 : HasDerivAt (fun u => ρ (u + c)) (g 1) t := by
      have h0' : HasDerivAt ρ (g 1) (t + c) := by
        rw [heq]
        exact hd 1 ⟨zero_le_one, le_refl 1⟩
      exact HasDerivAt.comp_add_const t c h0'
    have hF2 : HasDerivAt (fun u => ρ (u + c - 1)) (g 1) t := by
      have h0' : HasDerivAt ρ (g 0) (t + (c - 1)) := by
        rw [show t + (c - 1) = 0 by linarith]
        exact hd 0 ⟨le_refl 0, zero_le_one⟩
      have h1' := HasDerivAt.comp_add_const t (c - 1) h0'
      rw [hfun2] at h1'
      rw [hgcl]
      exact h1'
    have heqv : (fun u => ρ (u + c)) t = (fun u => ρ (u + c - 1)) t := by
      have h1 : t + c = 1 := heq
      have h2 : t + c - 1 = 0 := by linarith
      change ρ (t + c) = ρ (t + c - 1)
      rw [h2, h1]
      exact hcl.symm
    have hglue := glue_deriv hF1 hF2 heqv
    have hfun : (fun u : ℝ => if u + c ≤ 1 then ρ (u + c) else ρ (u + c - 1))
        = fun u => if u ≤ t then ρ (u + c) else ρ (u + c - 1) := by
      funext u
      by_cases hu : u + c ≤ 1
      · rw [if_pos hu, if_pos (by linarith)]
      · rw [if_neg hu, if_neg (by intro hle; exact hu (by linarith))]
    rw [hfun, if_pos (le_of_eq heq), heq]
    exact hglue
  · have hd2 : HasDerivAt (fun u => ρ (u + c - 1)) (g (t + c - 1)) t := by
      have h0' : HasDerivAt ρ (g (t + c - 1)) (t + (c - 1)) := by
        rw [show t + (c - 1) = t + c - 1 by ring]
        exact hd (t + c - 1) ⟨by linarith, by linarith [ht.2, hc.2]⟩
      have h1' := HasDerivAt.comp_add_const t (c - 1) h0'
      rw [hfun2] at h1'
      exact h1'
    rw [if_neg (not_le.mpr hgt)]
    refine hd2.congr_of_eventuallyEq ?_
    have hmem : Set.Ioi (1 - c) ∈ nhds t := Ioi_mem_nhds (by linarith)
    filter_upwards [hmem] with u hu
    rw [if_neg (by intro hle; linarith [Set.mem_Ioi.mp hu])]

/-- The wrapped shift keeps the period. -/
theorem wrap_mem {t c : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (if t + c ≤ 1 then t + c else t + c - 1) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : t + c ≤ 1
  · rw [if_pos h]
    exact ⟨by linarith [ht.1, hc.1], h⟩
  · rw [if_neg h]
    rw [not_le] at h
    exact ⟨by linarith, by linarith [ht.2, hc.2]⟩

/-- The wrap-shift of a function is the function at the wrapped time. -/
theorem rebase_val (ρ : ℝ → ℂ) {t c : ℝ} :
    (if t + c ≤ 1 then ρ (t + c) else ρ (t + c - 1))
      = ρ (if t + c ≤ 1 then t + c else t + c - 1) := by
  by_cases h : t + c ≤ 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The wrap-shift of a closed loop is closed. -/
theorem rebase_closure {ρ : ℝ → ℂ} {c : ℝ} (hcl : ρ 0 = ρ 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (if (0 : ℝ) + c ≤ 1 then ρ (0 + c) else ρ (0 + c - 1))
      = (if (1 : ℝ) + c ≤ 1 then ρ (1 + c) else ρ (1 + c - 1)) := by
  rw [if_pos (by linarith [hc.2] : (0 : ℝ) + c ≤ 1)]
  by_cases h : (1 : ℝ) + c ≤ 1
  · have hc0 : c = 0 := le_antisymm (by linarith) hc.1
    rw [if_pos h, hc0]
    norm_num
    exact hcl
  · rw [if_neg h, show (1 : ℝ) + c - 1 = 0 + c by ring]

/-- The wrap-shift matches at the endpoints in the reversed order as well. -/
theorem rebase_gclosure {g : ℝ → ℂ} {c : ℝ} (hgcl : g 1 = g 0)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (if (1 : ℝ) + c ≤ 1 then g (1 + c) else g (1 + c - 1))
      = (if (0 : ℝ) + c ≤ 1 then g (0 + c) else g (0 + c - 1)) := by
  rw [if_pos (by linarith [hc.2] : (0 : ℝ) + c ≤ 1)]
  by_cases h : (1 : ℝ) + c ≤ 1
  · have hc0 : c = 0 := le_antisymm (by linarith) hc.1
    rw [if_pos h, hc0]
    norm_num
    exact hgcl
  · rw [if_neg h, show (1 : ℝ) + c - 1 = 0 + c by ring]

/-- **Rebased continuity**: the wrap-shift of a continuous loop with matched endpoint
values is continuous on the period. -/
theorem rebase_gcont {g : ℝ → ℂ} {c : ℝ} (hgc : ContinuousOn g (Set.Icc 0 1))
    (hgcl : g 1 = g 0) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun u => if u + c ≤ 1 then g (u + c) else g (u + c - 1))
      (Set.Icc 0 1) := by
  set G : ℝ → ℂ := fun x => g (min 1 (max 0 x)) with hGdef
  have hGid : ∀ x ∈ Set.Icc (0 : ℝ) 1, G x = g x := by
    intro x hx
    change g (min 1 (max 0 x)) = g x
    rw [max_eq_right hx.1, min_eq_right hx.2]
  have hGc : Continuous G := by
    refine hgc.comp_continuous (continuous_const.min (continuous_const.max continuous_id))
      fun x => ?_
    exact ⟨le_min zero_le_one (le_max_left 0 x), min_le_left 1 _⟩
  have hcont : Continuous fun u => if u + c ≤ 1 then G (u + c) else G (u + c - 1) := by
    refine Continuous.if_le (hGc.comp (continuous_id.add continuous_const))
      (hGc.comp ((continuous_id.add continuous_const).sub continuous_const))
      (continuous_id.add continuous_const) continuous_const fun x hx => ?_
    rw [hx, show (1 : ℝ) - 1 = 0 by norm_num]
    have h1 : G 1 = g 1 := hGid 1 ⟨zero_le_one, le_refl 1⟩
    have h0 : G 0 = g 0 := hGid 0 ⟨le_refl 0, zero_le_one⟩
    rw [h1, h0, hgcl]
  refine hcont.continuousOn.congr fun u hu => ?_
  by_cases h : u + c ≤ 1
  · simp only [if_pos h]
    rw [hGid (u + c) ⟨by linarith [hu.1, hc.1], h⟩]
  · simp only [if_neg h]
    rw [not_le] at h
    rw [hGid (u + c - 1) ⟨by linarith, by linarith [hu.2, hc.2]⟩]

/-- **Rebased injectivity**: the wrap-shift of a loop injective on the fundamental
half-open period is injective there as well. -/
theorem rebase_inj {ρ : ℝ → ℂ} {c : ℝ} (hcl : ρ 0 = ρ 1)
    (hinj : Set.InjOn ρ (Set.Ico 0 1)) (hc : c ∈ Set.Ico (0 : ℝ) 1) :
    Set.InjOn (fun u => if u + c ≤ 1 then ρ (u + c) else ρ (u + c - 1))
      (Set.Ico 0 1) := by
  have hval : ∀ z ∈ Set.Ico (0 : ℝ) 1,
      (if z + c ≤ 1 then ρ (z + c) else ρ (z + c - 1))
        = ρ (if z + c < 1 then z + c else z + c - 1) := by
    intro z hz
    by_cases h1 : z + c < 1
    · rw [if_pos (le_of_lt h1), if_pos h1]
    · rw [if_neg h1]
      rw [not_lt] at h1
      by_cases h2 : z + c ≤ 1
      · have he : z + c = 1 := le_antisymm h2 h1
        rw [if_pos h2, he, show (1 : ℝ) - 1 = 0 by norm_num]
        exact hcl.symm
      · rw [if_neg h2]
  have hmem : ∀ z ∈ Set.Ico (0 : ℝ) 1,
      (if z + c < 1 then z + c else z + c - 1) ∈ Set.Ico (0 : ℝ) 1 := by
    intro z hz
    by_cases h : z + c < 1
    · rw [if_pos h]
      exact ⟨by linarith [hz.1, hc.1], h⟩
    · rw [if_neg h]
      rw [not_lt] at h
      exact ⟨by linarith, by linarith [hz.2, hc.2]⟩
  intro x hx y hy hxy
  have hxy' : ρ (if x + c < 1 then x + c else x + c - 1)
      = ρ (if y + c < 1 then y + c else y + c - 1) := by
    rw [← hval x hx, ← hval y hy]
    exact hxy
  have hww := hinj (hmem x hx) (hmem y hy) hxy'
  by_cases h1 : x + c < 1 <;> by_cases h2 : y + c < 1
  · rw [if_pos h1, if_pos h2] at hww
    linarith
  · rw [if_pos h1, if_neg h2] at hww
    rw [not_lt] at h2
    linarith [hx.1, hy.2]
  · rw [if_neg h1, if_pos h2] at hww
    rw [not_lt] at h1
    linarith [hy.1, hx.2]
  · rw [if_neg h1, if_neg h2] at hww
    linarith

/-- **Rebased winding**: the wrap-shift of a closed loop winds about any off-track point
exactly as the loop does. -/
theorem rebase_winding {ρ : ℝ → ℂ} {c : ℝ} {ζ : ℂ}
    (hc' : Continuous fun t : I => ρ ((t : ℝ)))
    (hcl : ρ 0 = ρ 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hne : ∀ t : I, ρ ((t : ℝ)) ≠ ζ)
    (hw : Continuous fun t : I =>
      if ((t : ℝ)) + c ≤ 1 then ρ (((t : ℝ)) + c) else ρ (((t : ℝ)) + c - 1)) :
    windingNumber (⟨fun t : I =>
        if ((t : ℝ)) + c ≤ 1 then ρ (((t : ℝ)) + c) else ρ (((t : ℝ)) + c - 1), hw⟩ : C(I, ℂ)) ζ
      = windingNumber (⟨fun t : I => ρ ((t : ℝ)), hc'⟩ : C(I, ℂ)) ζ := by
  set γρ : C(I, ℂ) := ⟨fun t : I => ρ ((t : ℝ)), hc'⟩ with hγdef
  have hclγ : γρ 0 = γρ 1 := by
    change ρ (((0:I) : ℝ)) = ρ (((1:I) : ℝ))
    rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
    exact hcl
  have hkey : (⟨fun t : I =>
      if ((t : ℝ)) + c ≤ 1 then ρ (((t : ℝ)) + c) else ρ (((t : ℝ)) + c - 1), hw⟩ : C(I, ℂ))
      = ⟨fun t : I => rotateLoop γρ c ((t : ℝ)),
          (rotateLoop_continuous γρ hclγ).comp continuous_subtype_val⟩ := by
    apply ContinuousMap.ext
    intro t
    change (if ((t : ℝ)) + c ≤ 1 then ρ (((t : ℝ)) + c) else ρ (((t : ℝ)) + c - 1))
      = rotateLoop γρ c ((t : ℝ))
    by_cases h : ((t : ℝ)) + c ≤ 1
    · rw [if_pos h, rotateLoop_apply_le γρ h]
      have hmem : ((t : ℝ)) + c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [t.2.1, hc.1], h⟩
      change _ = ρ ((Set.projIcc 0 1 zero_le_one (((t : ℝ)) + c) : I) : ℝ)
      rw [Set.projIcc_of_mem zero_le_one hmem]
    · rw [if_neg h, rotateLoop_apply_gt γρ h]
      rw [not_le] at h
      have hmem : ((t : ℝ)) + c - 1 ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith, by linarith [t.2.2, hc.2]⟩
      change _ = ρ ((Set.projIcc 0 1 zero_le_one (((t : ℝ)) + c - 1) : I) : ℝ)
      rw [Set.projIcc_of_mem zero_le_one hmem]
  rw [hkey]
  exact winding_rotate hclγ hne hc

/-- **Nearest-point orthogonality**: at a parameter of minimal squared distance from a
point to a closed curve with wrap-matched derivative, the joining vector is orthogonal
to the velocity. -/
theorem nearest_orth {ρ g : ℝ → ℂ} {ζ : ℂ} {t₀ : ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ρ (g t) t)
    (hcl : ρ 0 = ρ 1) (hgcl : g 1 = g 0)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Complex.normSq (ρ t₀ - ζ) ≤ Complex.normSq (ρ t - ζ)) :
    (ρ t₀ - ζ).re * (g t₀).re + (ρ t₀ - ζ).im * (g t₀).im = 0 := by
  set φ : ℝ → ℝ := fun t => Complex.normSq (ρ t - ζ) with hφdef
  set ψ : ℝ → ℝ := fun t =>
    2 * ((ρ t - ζ).re * (g t).re + (ρ t - ζ).im * (g t).im) with hψdef
  have hdφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have hsub : HasDerivAt (fun u => ρ u - ζ) (g t) t := (hd t ht).sub_const ζ
    have hre : HasDerivAt (fun u => (ρ u - ζ).re) ((g t).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hsub
    have him : HasDerivAt (fun u => (ρ u - ζ).im) ((g t).im) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hsub
    have hpoly : HasDerivAt (fun u => (ρ u - ζ).re ^ 2 + (ρ u - ζ).im ^ 2)
        (2 * (ρ t - ζ).re ^ 1 * (g t).re + 2 * (ρ t - ζ).im ^ 1 * (g t).im) t :=
      (hre.pow 2).add (him.pow 2)
    have hfun : φ = fun u => (ρ u - ζ).re ^ 2 + (ρ u - ζ).im ^ 2 := by
      funext u
      change Complex.normSq (ρ u - ζ) = _
      rw [Complex.normSq_apply]
      ring
    have hval : ψ t = 2 * (ρ t - ζ).re ^ 1 * (g t).re
        + 2 * (ρ t - ζ).im ^ 1 * (g t).im := by
      change 2 * ((ρ t - ζ).re * (g t).re + (ρ t - ζ).im * (g t).im) = _
      ring
    rw [hfun, hval]
    exact hpoly
  have hφcl : φ 0 = φ 1 := by
    change Complex.normSq (ρ 0 - ζ) = Complex.normSq (ρ 1 - ζ)
    rw [hcl]
  have hψcl : ψ 1 = ψ 0 := by
    change 2 * ((ρ 1 - ζ).re * (g 1).re + (ρ 1 - ζ).im * (g 1).im)
      = 2 * ((ρ 0 - ζ).re * (g 0).re + (ρ 0 - ζ).im * (g 0).im)
    rw [← hcl, hgcl]
  have hz := loop_min_deriv_zero hdφ hφcl hψcl ht₀ hmin
  have hz' : 2 * ((ρ t₀ - ζ).re * (g t₀).re + (ρ t₀ - ζ).im * (g t₀).im) = 0 := hz
  linarith

/-- **Segment reach**: the winding of a loop about an off-track point transports along
the nearest-point normal segment and then along the offset track to the winding about
some admissibly small basepoint offset. -/
theorem reach {ρ g : ℝ → ℂ} {ζ : ℂ} {ε₁ : ℝ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ρ (g t) t)
    (hgc : ContinuousOn g (Set.Icc 0 1))
    (hcl : ρ 0 = ρ 1) (hgcl : g 1 = g 0)
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0)
    (hc' : Continuous fun t : I => ρ ((t : ℝ)))
    (hζ : ∀ t : I, ρ ((t : ℝ)) ≠ ζ) (hε₁ : 0 < ε₁)
    (hdisj : ∀ ε' : ℝ, 0 < |ε'| → |ε'| ≤ ε₁ →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ρ t ≠ ρ s - (ε' : ℂ) * (Complex.I * g s)) :
    ∃ ε' : ℝ, 0 < |ε'| ∧ |ε'| ≤ ε₁ ∧
      windingNumber (⟨fun t : I => ρ ((t : ℝ)), hc'⟩ : C(I, ℂ)) ζ
        = windingNumber (⟨fun t : I => ρ ((t : ℝ)), hc'⟩ : C(I, ℂ))
            (ρ 0 - (ε' : ℂ) * (Complex.I * g 0)) := by
  have hρc : ContinuousOn ρ (Set.Icc 0 1) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hφc : ContinuousOn (fun t => Complex.normSq (ρ t - ζ)) (Set.Icc 0 1) :=
    Complex.continuous_normSq.comp_continuousOn (hρc.sub continuousOn_const)
  obtain ⟨t₀, ht₀, hminOn⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) hφc
  have hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Complex.normSq (ρ t₀ - ζ) ≤ Complex.normSq (ρ t - ζ) := fun t ht => hminOn ht
  have horth := nearest_orth hd hcl hgcl ht₀ hmin
  have horth' : (ζ - ρ t₀).re * (g t₀).re + (ζ - ρ t₀).im * (g t₀).im = 0 := by
    simp only [Complex.sub_re, Complex.sub_im] at horth ⊢
    linarith
  obtain ⟨s, hs⟩ := normal_decomp (hgne t₀ ht₀) horth'
  have hζne : ζ - ρ t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm (hζ ⟨t₀, ht₀⟩))
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, zero_mul] at hs
    exact hζne hs
  set W : ℂ := ζ - ρ t₀ with hWdef
  set ε : ℝ := min ε₁ |s| with hεdef
  have habs : 0 < |s| := abs_pos.mpr hsne
  have hε : 0 < ε := lt_min hε₁ habs
  set θ : ℝ := ε / |s| with hθdef
  have hθ0 : 0 < θ := div_pos hε habs
  have hθ1 : θ ≤ 1 := (div_le_one habs).mpr (min_le_right _ _)
  set ε' : ℝ := -(θ * s) with hε'def
  have hε'abs : |ε'| = ε := by
    rw [hε'def, abs_neg, abs_mul, abs_of_pos hθ0, hθdef]
    field_simp
  have hε'pos : 0 < |ε'| := by rw [hε'abs]; exact hε
  have hε'le : |ε'| ≤ ε₁ := by rw [hε'abs]; exact min_le_left _ _
  refine ⟨ε', hε'pos, hε'le, ?_⟩
  set sg : ℝ → ℂ := fun u => ρ t₀ + ((θ + u * (1 - θ) : ℝ) : ℂ) * W with hsgdef
  have hsgc : ContinuousOn sg (Set.Icc 0 1) := by
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.mul ?_ continuousOn_const
    exact (Complex.continuous_ofReal.comp
      (continuous_const.add (continuous_id.mul continuous_const))).continuousOn
  have hsgavoid : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ρ t ≠ sg u := by
    intro u hu t ht heq'
    set lam : ℝ := θ + u * (1 - θ) with hlam
    have hlam0 : 0 < lam := by nlinarith only [hu.1, hu.2, hθ0, hθ1]
    have hlam1 : lam ≤ 1 := by nlinarith only [hu.1, hu.2, hθ0, hθ1]
    have h2 : sg u - ζ = ((lam - 1 : ℝ) : ℂ) * W := by
      change ρ t₀ + ((lam : ℝ) : ℂ) * W - ζ = _
      rw [hWdef]
      push_cast
      ring
    have h2' : ρ t - ζ = ((lam - 1 : ℝ) : ℂ) * W := by rw [heq']; exact h2
    have hWpos : 0 < Complex.normSq W := Complex.normSq_pos.mpr hζne
    have h3 : Complex.normSq (ρ t - ζ) = (lam - 1) * (lam - 1) * Complex.normSq W := by
      rw [h2', Complex.normSq_mul, Complex.normSq_ofReal]
    have h4 : ρ t₀ - ζ = -W := by
      rw [hWdef]
      ring
    have h5 : Complex.normSq (ρ t₀ - ζ) = Complex.normSq W := by
      rw [h4, Complex.normSq_neg]
    have h6 := hmin t ht
    rw [h3, h5] at h6
    nlinarith only [h6, hlam0, hlam1, hWpos,
      mul_pos (mul_pos hlam0 (show (0 : ℝ) < 2 - lam by linarith)) hWpos]
  have hsg1 : sg 1 = ζ := by
    change ρ t₀ + ((θ + 1 * (1 - θ) : ℝ) : ℂ) * W = ζ
    rw [show θ + 1 * (1 - θ) = 1 by ring, hWdef]
    push_cast
    ring
  have hsg0 : sg 0 = ρ t₀ - (ε' : ℂ) * (Complex.I * g t₀) := by
    change ρ t₀ + ((θ + 0 * (1 - θ) : ℝ) : ℂ) * W = _
    rw [show θ + 0 * (1 - θ) = θ by ring, hs, hε'def]
    push_cast
    ring
  have htr1 := offset_transport hsgc hcl hsgavoid hc'
    (s₀ := 1) (s₁ := 0) ⟨zero_le_one, le_refl 1⟩ ⟨le_refl 0, zero_le_one⟩
  set τ : ℝ → ℂ := fun u => ρ u - (ε' : ℂ) * (Complex.I * g u) with hτdef
  have hτc : ContinuousOn τ (Set.Icc 0 1) :=
    hρc.sub (continuousOn_const.mul (continuousOn_const.mul hgc))
  have hτavoid : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ρ t ≠ τ u := by
    intro u hu t ht
    exact hdisj ε' hε'pos hε'le u hu t ht
  have htr2 := offset_transport hτc hcl hτavoid hc'
    (s₀ := t₀) (s₁ := 0) ht₀ ⟨le_refl 0, zero_le_one⟩
  have hτt₀ : τ t₀ = sg 0 := by
    rw [hsg0]
  have hτ0 : τ 0 = ρ 0 - (ε' : ℂ) * (Complex.I * g 0) := rfl
  rw [← hsg1, htr1, ← hτ0, ← htr2, hτt₀]

/-- **Two values at the offset basepoint**: for a loop based at its imaginary minimum
with sign-adapted window data, the winding about the offset basepoint is the tangent
degree on the inward side and zero on the outward side, hence nonnegative. -/
theorem two_values {P G : ℝ → ℂ} {ς εA M ε' : ℝ}
    (hPc : ContinuousOn P (Set.Icc 0 1)) (hclP : P 0 = P 1) (hGcl : G 1 = G 0)
    (hGc : ContinuousOn G (Set.Icc 0 1))
    (hGne : ∀ u ∈ Set.Icc (0 : ℝ) 1, G u ≠ 0)
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖G u‖ ≤ M)
    (hminP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (P 0).im ≤ (P t).im)
    (hwin : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t ∈ Metric.closedBall (P 0) εA →
      (Complex.I * (((ς : ℝ) : ℂ) * G t)).im < 0)
    (hς : ς = 1 ∨ ς = -1)
    (hneg : (Complex.I * (((ς : ℝ) : ℂ) * G 0)).im < 0)
    (hε'pos : 0 < |ε'|) (hεAM : |ε'| * M ≤ εA)
    (hdisjε' : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      P t ≠ P s - (ε' : ℂ) * (Complex.I * G s))
    (hcP' : Continuous fun t : I => P ((t : ℝ)))
    (hGw : Continuous fun t : I => G ((t : ℝ)))
    (hdeg1 : windingNumber (⟨fun t : I => G ((t : ℝ)), hGw⟩ : C(I, ℂ)) 0 = 1) :
    0 ≤ windingNumber (⟨fun t : I => P ((t : ℝ)), hcP'⟩ : C(I, ℂ))
        (P 0 - (ε' : ℂ) * (Complex.I * G 0)) := by
  have hclP' : (⟨fun t : I => P ((t : ℝ)), hcP'⟩ : C(I, ℂ)) 0
      = (⟨fun t : I => P ((t : ℝ)), hcP'⟩ : C(I, ℂ)) 1 := by
    change P (((0:I) : ℝ)) = P (((1:I) : ℝ))
    rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
    exact hclP
  have hnegG : ς * (G 0).re < 0 := by
    have h1 : (Complex.I * (((ς:ℝ):ℂ) * G 0)).im = ς * (G 0).re := by
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h1] at hneg
    exact hneg
  by_cases hsign : ε' = ς * |ε'|
  · -- inward side: the winding is the tangent degree
    have hdisj2 : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        P t ≠ P s - ((ς * |ε'| : ℝ) : ℂ) * (Complex.I * G s) := by
      rw [← hsign]
      exact hdisjε'
    have hAc : Continuous fun u : I =>
        P ((u : ℝ)) - (P 0 - ((ς * |ε'| : ℝ) : ℂ) * (Complex.I * G 0)) :=
      hcP'.sub continuous_const
    have happ := inner_degree hPc hclP hGcl hε'pos hς hGc hGne hM hminP hwin hεAM hdisj2
      (⟨fun u : I => P ((u : ℝ)) - (P 0 - ((ς * |ε'| : ℝ) : ℂ) * (Complex.I * G 0)),
        hAc⟩ : C(I, ℂ)) (fun u => rfl) hGw
    have hne : ∀ t : I, (⟨fun t : I => P ((t : ℝ)), hcP'⟩ : C(I, ℂ)) t
        ≠ P 0 - ((ς * |ε'| : ℝ) : ℂ) * (Complex.I * G 0) :=
      fun t => hdisj2 0 ⟨le_refl 0, zero_le_one⟩ ((t : ℝ)) t.2
    have hshift := winding_shift hclP' hne
      (⟨fun u : I => P ((u : ℝ)) - (P 0 - ((ς * |ε'| : ℝ) : ℂ) * (Complex.I * G 0)),
        hAc⟩ : C(I, ℂ)) (fun u => rfl)
    rw [show ((ε' : ℝ) : ℂ) = ((ς * |ε'| : ℝ) : ℂ) by rw [← hsign]]
    rw [← hshift, happ, hdeg1]
    norm_num
  · -- outward side: the offset point lies strictly below the loop
    have heq2 : ε' = -(ς * |ε'|) := by
      rcases hς with hh | hh <;> rcases abs_cases ε' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exfalso
        rw [hh, ha, one_mul] at hsign
        exact hsign rfl
      · rw [hh, ha]
        ring
      · rw [hh, ha]
        ring
      · exfalso
        rw [hh, ha] at hsign
        apply hsign
        ring
    have hkey : 0 < ε' * (Complex.I * G 0).im := by
      have hIm : (Complex.I * G 0).im = (G 0).re := by
        rw [Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      rw [heq2, hIm]
      rcases hς with hh | hh <;> rw [hh] at hnegG ⊢
      · nlinarith only [mul_pos hε'pos (show (0 : ℝ) < -(G 0).re by linarith [hnegG])]
      · nlinarith only [mul_pos hε'pos (show (0 : ℝ) < (G 0).re by linarith [hnegG])]
    have hpim : (P 0 - (ε' : ℂ) * (Complex.I * G 0)).im
        = (P 0).im - ε' * (Complex.I * G 0).im := by
      rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hoff : ∀ t : I, ((⟨fun t : I => P ((t : ℝ)), hcP'⟩ : C(I, ℂ)) t).im
        ≠ (P 0 - (ε' : ℂ) * (Complex.I * G 0)).im := by
      intro t
      have hlt : (P 0 - (ε' : ℂ) * (Complex.I * G 0)).im < (P ((t : ℝ))).im := by
        rw [hpim]
        have := hminP ((t : ℝ)) t.2
        linarith [hkey]
      exact ne_of_gt hlt
    rw [winding_offline_zero hclP' hoff]

/-- **The nonnegative-winding principle**: a positively-oriented simple smooth loop has
nonnegative winding about every off-track point. -/
theorem nonnegWindingPrinciple₂_holds : NonnegWindingPrinciple₂ := by
  intro ρ g hd hgc hcl hgcl hinj hgne hgw hdeg hc' ζ hζ
  have hρc : ContinuousOn ρ (Set.Icc 0 1) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  obtain ⟨c₀, hc₀, hminOn⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one) (Complex.continuous_im.comp_continuousOn hρc)
  have hminIm : ∀ t ∈ Set.Icc (0 : ℝ) 1, (ρ c₀).im ≤ (ρ t).im := fun t ht => hminOn ht
  set c : ℝ := if c₀ = 1 then 0 else c₀ with hcdef
  have hcIco : c ∈ Set.Ico (0 : ℝ) 1 := by
    by_cases h : c₀ = 1
    · rw [hcdef, if_pos h]
      exact ⟨le_refl 0, zero_lt_one⟩
    · rw [hcdef, if_neg h]
      exact ⟨hc₀.1, lt_of_le_of_ne hc₀.2 h⟩
  have hcIcc : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hcIco.1, hcIco.2.le⟩
  have hcmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, (ρ c).im ≤ (ρ t).im := by
    intro t ht
    by_cases h : c₀ = 1
    · rw [hcdef, if_pos h, hcl]
      have h1 := hminIm t ht
      rw [h] at h1
      exact h1
    · rw [hcdef, if_neg h]
      exact hminIm t ht
  set P : ℝ → ℂ := fun u => if u + c ≤ 1 then ρ (u + c) else ρ (u + c - 1) with hPdef
  set G : ℝ → ℂ := fun u => if u + c ≤ 1 then g (u + c) else g (u + c - 1) with hGdef
  have hdP : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt P (G t) t := fun t ht =>
    rebase_deriv hd hcl hgcl hcIcc t ht
  have hGc : ContinuousOn G (Set.Icc 0 1) := rebase_gcont hgc hgcl hcIcc
  have hclP : P 0 = P 1 := rebase_closure hcl hcIcc
  have hGcl : G 1 = G 0 := rebase_gclosure hgcl hcIcc
  have hinjP : Set.InjOn P (Set.Ico 0 1) := rebase_inj hcl hinj hcIco
  have hGne : ∀ u ∈ Set.Icc (0 : ℝ) 1, G u ≠ 0 := by
    intro u hu
    have hv : G u = g (if u + c ≤ 1 then u + c else u + c - 1) := rebase_val g
    rw [hv]
    exact hgne _ (wrap_mem hu hcIcc)
  have hPc : ContinuousOn P (Set.Icc 0 1) := fun t ht =>
    (hdP t ht).continuousAt.continuousWithinAt
  have hP0 : P 0 = ρ c := by
    change (if (0 : ℝ) + c ≤ 1 then ρ (0 + c) else ρ (0 + c - 1)) = ρ c
    rw [if_pos (by linarith [hcIco.2.le] : (0 : ℝ) + c ≤ 1), zero_add]
  have hminP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (P 0).im ≤ (P t).im := by
    intro t ht
    rw [hP0]
    have hv : P t = ρ (if t + c ≤ 1 then t + c else t + c - 1) := rebase_val ρ
    rw [hv]
    exact hcmin _ (wrap_mem ht hcIcc)
  have hcP' : Continuous fun t : I => P ((t : ℝ)) :=
    hPc.comp_continuous continuous_subtype_val fun u => u.2
  have hGw : Continuous fun t : I => G ((t : ℝ)) :=
    hGc.comp_continuous continuous_subtype_val fun u => u.2
  have hζP : ∀ t : I, P ((t : ℝ)) ≠ ζ := by
    intro t
    have hv : P ((t : ℝ)) = ρ (if (t:ℝ) + c ≤ 1 then (t:ℝ) + c else (t:ℝ) + c - 1) :=
      rebase_val ρ
    rw [hv]
    exact hζ ⟨_, wrap_mem t.2 hcIcc⟩
  have hGim : (G 0).im = 0 := min_im_deriv_zero hdP hclP hGcl hminP
  have hG0ne : G 0 ≠ 0 := hGne 0 ⟨le_refl 0, zero_le_one⟩
  have hGre : (G 0).re ≠ 0 := by
    intro h0
    apply hG0ne
    apply Complex.ext
    · rw [h0, Complex.zero_re]
    · rw [hGim, Complex.zero_im]
  set ς : ℝ := if 0 < (G 0).re then -1 else 1 with hςdef
  have hς : ς = 1 ∨ ς = -1 := by
    by_cases h : 0 < (G 0).re
    · right
      rw [hςdef, if_pos h]
    · left
      rw [hςdef, if_neg h]
  have hneg : (Complex.I * (((ς : ℝ) : ℂ) * G 0)).im < 0 := by
    have h1 : (Complex.I * (((ς:ℝ):ℂ) * G 0)).im = ς * (G 0).re := by
      rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h1]
    by_cases h : 0 < (G 0).re
    · rw [hςdef, if_pos h]
      nlinarith only [h]
    · rw [hςdef, if_neg h]
      rw [not_lt] at h
      nlinarith only [lt_of_le_of_ne h hGre]
  obtain ⟨εA, hεA0, hwin⟩ := assertion_ii (g := fun t => ((ς : ℝ) : ℂ) * G t) hPc
    (continuousOn_const.mul hGc)
    (by rw [hGcl]) hinjP hneg
  obtain ⟨u₁, hu₁, hmaxOn⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) hGc.norm
  set M : ℝ := ‖G u₁‖ with hMdef
  have hM : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖G u‖ ≤ M := fun u hu => hmaxOn hu
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.mpr hG0ne)
    (hM 0 ⟨le_refl 0, zero_le_one⟩)
  obtain ⟨ε₀, hε₀, hoffd⟩ := offset_disjoint hdP hGc hclP hGcl hinjP hGne
  set ε₁ : ℝ := min ε₀ (εA / M) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε₀ (div_pos hεA0 hMpos)
  have hdisj₁ : ∀ ε' : ℝ, 0 < |ε'| → |ε'| ≤ ε₁ →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        P t ≠ P s - (ε' : ℂ) * (Complex.I * G s) :=
    fun ε' h1 h2 => hoffd ε' h1 (le_trans h2 (min_le_left _ _))
  obtain ⟨ε', hε'pos, hε'le, hreach⟩ :=
    reach hdP hGc hclP hGcl hGne hcP' hζP hε₁ hdisj₁
  have hεAM : |ε'| * M ≤ εA := by
    have h1 : |ε'| ≤ εA / M := le_trans hε'le (min_le_right _ _)
    calc |ε'| * M ≤ (εA / M) * M := by nlinarith only [h1, hMpos]
      _ = εA := by field_simp
  have hdegG : windingNumber (⟨fun t : I => G ((t : ℝ)), hGw⟩ : C(I, ℂ)) 0 = 1 := by
    have htr := rebase_winding (ρ := g) (c := c) (ζ := 0) hgw hgcl.symm hcIcc
      (fun t => hgne _ t.2) hGw
    rw [← hdeg]
    exact htr
  have hwζ : windingNumber (⟨fun t : I => P ((t:ℝ)), hcP'⟩ : C(I,ℂ)) ζ
      = windingNumber (⟨fun t : I => ρ ((t:ℝ)), hc'⟩ : C(I,ℂ)) ζ :=
    rebase_winding hc' hcl hcIcc hζ hcP'
  have h2v := two_values hPc hclP hGcl hGc hGne hM hminP hwin hς hneg hε'pos hεAM
    (fun s hs t ht => hdisj₁ ε' hε'pos hε'le s hs t ht) hcP' hGw hdegG
  rw [← hwζ, hreach]
  exact h2v

end PinDischarge

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
          / (1 - ‖wirtingerQuotient h z‖ ^ 2)) :=
  rs_main_of_principle hΓ hfree hcc q hκ hqc hbd hcomm nonnegWindingPrinciple₂_holds

/-- **Lusin (N) for quasiconformal maps**: the image of a Lebesgue-null set under an
analytically quasiconformal plane map is Lebesgue-null. -/
theorem qc_image_null {f : ℂ → ℂ} {b : BeltramiCoeff} (hf : IsQCAnalytic f b)
    {N : Set ℂ} (hN : volume N = 0) : volume (f '' N) = 0 := by
  obtain ⟨p, gx, gy, hp2, hgrad, hgxp, hgyp⟩ :=
    hf.exists_weakGradient_memLpLocOn_gt_two
  exact lusinN_image_null_of_weakGradient hp2 hf.1.1.continuous hgrad hgxp hgyp hN

/-- **Quasiconformal pullback of a co-null set**: a geometrically quasiconformal plane
map sends almost every point outside any given null set. -/
theorem preimage_conull {H : ℂ → ℂ} {K : ℝ} (hH : IsQCGeometric H K)
    {N : Set ℂ} (hN : volume N = 0) : ∀ᵐ z : ℂ, H z ∉ N := by
  have hHinvqc := isQCGeometric_inv_of_isQCGeometric hH
  obtain ⟨b, -, hQCA⟩ := isQCAnalytic_of_isQCGeometric hHinvqc.1 hHinvqc
  have himg : volume (⇑(hH.2.1.isHomeomorph.homeomorph H).symm '' N) = 0 :=
    qc_image_null hQCA hN
  rw [ae_iff]
  have happ : ∀ z : ℂ, (hH.2.1.isHomeomorph.homeomorph H) z = H z := fun z =>
    IsHomeomorph.homeomorph_apply H hH.2.1.isHomeomorph z
  have hset : {z : ℂ | ¬ H z ∉ N}
      = ⇑(hH.2.1.isHomeomorph.homeomorph H).symm '' N := by
    ext z
    simp only [Set.mem_ofPred_eq, not_not]
    constructor
    · intro hz
      exact ⟨H z, hz, by rw [← happ z, Homeomorph.symm_apply_apply]⟩
    · rintro ⟨w, hw, rfl⟩
      have h2 : H ((hH.2.1.isHomeomorph.homeomorph H).symm w) = w := by
        rw [← happ, Homeomorph.apply_symm_apply]
      rwa [h2]
  rw [hset]
  exact himg

/-- **The conjugate-pair real part**: for a unimodular direction `θ` the product
`(u − θv) conj (u + θv)` has real part `|u|² − |v|²`. -/
theorem conj_pair_re (u v θ : ℂ) (hθ : θ * starRingEnd ℂ θ = 1) :
    ((u - θ * v) * starRingEnd ℂ (u + θ * v)).re
      = Complex.normSq u - Complex.normSq v := by
  have h1 : (u - θ * v) * starRingEnd ℂ (u + θ * v)
      = ((Complex.normSq u - Complex.normSq v : ℝ) : ℂ)
        + (u * starRingEnd ℂ θ * starRingEnd ℂ v
            - starRingEnd ℂ u * θ * v) := by
    simp only [map_add, map_mul, Complex.ofReal_sub]
    linear_combination Complex.mul_conj u - Complex.mul_conj v
      - (v * starRingEnd ℂ v) * hθ
  rw [h1]
  have h2 : (u * starRingEnd ℂ θ * starRingEnd ℂ v - starRingEnd ℂ u * θ * v).re
      = 0 := by
    have h3 : starRingEnd ℂ u * θ * v
        = starRingEnd ℂ (u * starRingEnd ℂ θ * starRingEnd ℂ v) := by
      simp only [map_mul, Complex.conj_conj]
    rw [h3, Complex.sub_re, Complex.conj_re, sub_self]
  rw [Complex.add_re, h2, add_zero, Complex.ofReal_re]

/-- **The pointwise Reich–Strebel weight bound in the Teichmüller frame**: if the chain
identity `p (β − k θ̄ α) = −b conj (α − k θ β)` holds with unimodular `θ`, positive
Jacobian `|β| < |α|`, and coefficient bound `|b| ≤ c₀ |p|` with `p ≠ 0`, then the weight
`|α − θβ|²/(|α|² − |β|²)` is at most `(1 − k)/(1 + k) · (1 + c₀)/(1 − c₀)`. -/
theorem rs_weight_pointwise {θ α β p b : ℂ} {k c₀ : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hc₀0 : 0 ≤ c₀) (hc₀1 : c₀ < 1)
    (hθ : θ * starRingEnd ℂ θ = 1)
    (hjac : ‖β‖ < ‖α‖) (hp : p ≠ 0) (hb : ‖b‖ ≤ c₀ * ‖p‖)
    (hchain : p * (β - (k : ℂ) * starRingEnd ℂ θ * α)
      = -(b * starRingEnd ℂ (α - (k : ℂ) * θ * β))) :
    ‖α - θ * β‖ ^ 2 / (‖α‖ ^ 2 - ‖β‖ ^ 2)
      ≤ (1 - k) / (1 + k) * ((1 + c₀) / (1 - c₀)) := by
  set X : ℂ := α - (k : ℂ) * θ * β with hXdef
  set Y : ℂ := β - (k : ℂ) * starRingEnd ℂ θ * α with hYdef
  -- the two linear identities of the frame
  have hX1 : X - θ * Y = (1 + (k : ℂ)) * (α - θ * β) := by
    rw [hXdef, hYdef]
    linear_combination ((k : ℂ) * α) * hθ
  have hX2 : X + θ * Y = (1 - (k : ℂ)) * (α + θ * β) := by
    rw [hXdef, hYdef]
    linear_combination (-(k : ℂ) * α) * hθ
  -- the norm transfer along the chain identity
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hYX : ‖Y‖ ≤ c₀ * ‖X‖ := by
    have h1 : ‖p‖ * ‖Y‖ = ‖b‖ * ‖X‖ := by
      have h2 := congrArg norm hchain
      rwa [norm_mul, norm_neg, norm_mul, RCLike.norm_conj] at h2
    have h2 : ‖b‖ * ‖X‖ ≤ c₀ * ‖p‖ * ‖X‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    nlinarith [h1, h2, hpn]
  -- the Jacobian transfer
  have hnθY : ∀ w : ℂ, ‖θ * w‖ = ‖w‖ := by
    intro w
    have hθ1 : ‖θ‖ = 1 := by
      have h1 := congrArg norm hθ
      rw [norm_mul, RCLike.norm_conj, norm_one] at h1
      nlinarith [norm_nonneg θ]
    rw [norm_mul, hθ1, one_mul]
  have hXY2 : Complex.normSq X - Complex.normSq Y
      = (1 - k ^ 2) * (Complex.normSq α - Complex.normSq β) := by
    have h1 := conj_pair_re X Y θ hθ
    rw [hX1, hX2] at h1
    have h2 : ((1 + (k : ℂ)) * (α - θ * β)
        * starRingEnd ℂ ((1 - (k : ℂ)) * (α + θ * β)))
        = ((1 - k ^ 2 : ℝ) : ℂ) * ((α - θ * β) * starRingEnd ℂ (α + θ * β)) := by
      simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
      push_cast
      ring
    rw [h2] at h1
    rw [← h1, Complex.re_ofReal_mul, conj_pair_re α β θ hθ]
  -- positivity of the frame
  have hJ : 0 < ‖α‖ ^ 2 - ‖β‖ ^ 2 := by
    nlinarith [norm_nonneg β]
  have hX0 : 0 < ‖X‖ := by
    rcases eq_or_ne X 0 with hXz | hXz
    · exfalso
      have hYz : Y = 0 := by
        have h5 : ‖Y‖ ≤ 0 := by
          have h6 := hYX
          rw [hXz, norm_zero, mul_zero] at h6
          exact h6
        exact norm_eq_zero.mp (le_antisymm h5 (norm_nonneg _))
      have hαe : α - (k : ℂ) * θ * β = 0 := by rw [← hXdef]; exact hXz
      have hβe : β - (k : ℂ) * starRingEnd ℂ θ * α = 0 := by rw [← hYdef]; exact hYz
      have h6 : (1 - (k : ℂ) ^ 2) * α = 0 := by
        linear_combination hαe + (k : ℂ) * θ * hβe + ((k : ℂ) ^ 2 * α) * hθ
      have h7 : (1 - (k : ℂ) ^ 2) ≠ 0 := by
        intro h8
        have h9 : ((k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination -h8
        have h10 : (k : ℝ) ^ 2 = 1 := by exact_mod_cast h9
        nlinarith
      have hαz : α = 0 := (mul_eq_zero.mp h6).resolve_left h7
      rw [hαz, norm_zero] at hjac
      exact absurd hjac (not_lt.mpr (norm_nonneg β))
    · exact norm_pos_iff.mpr hXz
  -- the endgame chain
  have hnum : ‖α - θ * β‖ * (1 + k) = ‖X - θ * Y‖ := by
    rw [hX1, norm_mul]
    have h1 : ‖(1 + (k : ℂ))‖ = 1 + k := by
      rw [show (1 + (k : ℂ)) = ((1 + k : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [h1]
    ring
  have hA : (‖α - θ * β‖ * (1 + k)) ^ 2 = ‖X - θ * Y‖ ^ 2 := by rw [hnum]
  have hB0 : ‖X - θ * Y‖ ≤ (1 + c₀) * ‖X‖ := by
    calc ‖X - θ * Y‖ ≤ ‖X‖ + ‖θ * Y‖ := norm_sub_le _ _
      _ = ‖X‖ + ‖Y‖ := by rw [hnθY]
      _ ≤ ‖X‖ + c₀ * ‖X‖ := by linarith [hYX]
      _ = (1 + c₀) * ‖X‖ := by ring
  have hB : ‖X - θ * Y‖ ^ 2 ≤ ((1 + c₀) * ‖X‖) ^ 2 := by
    nlinarith [hB0, norm_nonneg (X - θ * Y)]
  have hden_ge : (1 - c₀ ^ 2) * ‖X‖ ^ 2 ≤ (1 - k ^ 2) * (‖α‖ ^ 2 - ‖β‖ ^ 2) := by
    have h1 : ‖X‖ ^ 2 - c₀ ^ 2 * ‖X‖ ^ 2 ≤ Complex.normSq X - Complex.normSq Y := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      nlinarith [hYX, norm_nonneg Y, norm_nonneg X]
    rw [hXY2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h1
    nlinarith [h1]
  have hgoal2 : ‖α - θ * β‖ ^ 2 * ((1 + k) * (1 - c₀)) * (1 + k)
      ≤ (1 - k) * (1 + c₀) * (‖α‖ ^ 2 - ‖β‖ ^ 2) * (1 + k) := by
    nlinarith [hA, hB, hden_ge, hX0, hJ, sq_nonneg ‖X‖, sq_nonneg (‖α - θ * β‖)]
  have hgoal3 : ‖α - θ * β‖ ^ 2 * ((1 + k) * (1 - c₀))
      ≤ (1 - k) * (1 + c₀) * (‖α‖ ^ 2 - ‖β‖ ^ 2) :=
    le_of_mul_le_mul_right hgoal2 (by linarith)
  rw [div_le_iff₀ hJ, div_mul_div_comm, div_mul_eq_mul_div,
    le_div_iff₀ (by nlinarith : (0 : ℝ) < (1 + k) * (1 - c₀))]
  nlinarith [hgoal3]

/-- **Positivity of the `L¹` mass**: a somewhere-nonzero automorphic quadratic
differential over a cocompact free Fuchsian base has positive `L¹` mass. -/
theorem l1Norm_pos {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z : ℂ, 0 < z.im ∧ q z ≠ 0) :
    0 < q.l1Norm := by
  set K : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hKdef
  have hsub : K ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  -- the domain image has positive volume
  obtain ⟨ε, hε, hgap⟩ := exists_translation_gap hΓ hfree hcc
  have hball : Metric.ball UpperHalfPlane.I (ε / 2) ⊆ dirichletDomain Γ UpperHalfPlane.I :=
    ball_subset_dirichletDomain hε hgap
  have hopen : IsOpen (UpperHalfPlane.coe '' Metric.ball UpperHalfPlane.I (ε / 2)) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ Metric.isOpen_ball
  have hne : (UpperHalfPlane.coe '' Metric.ball UpperHalfPlane.I (ε / 2)).Nonempty :=
    ⟨UpperHalfPlane.coe UpperHalfPlane.I,
      ⟨UpperHalfPlane.I, Metric.mem_ball_self (by linarith), rfl⟩⟩
  have hvol : 0 < volume K := by
    refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono ?_)
    exact Set.image_mono hball
  -- if the mass vanished, the differential would vanish almost everywhere on the image
  rw [pos_iff_ne_zero]
  intro h0
  have hmeas : Measurable fun z : ℂ => ‖q z‖ₑ := q.measurable.enorm
  have h1 : ∀ᵐ z ∂(volume.restrict K), ‖q z‖ₑ = 0 := by
    have h2 : ∫⁻ z in K, ‖q z‖ₑ = 0 := h0
    rw [lintegral_eq_zero_iff hmeas] at h2
    exact h2
  have h3 : ∀ᵐ z ∂(volume.restrict K), q z ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub (q.ae_ne_zero hq0)
  have h4 : ∀ᵐ z ∂(volume.restrict K), False := by
    filter_upwards [h1, h3] with z hz1 hz3
    exact hz3 (by rwa [enorm_eq_zero] at hz1)
  have h5 : (volume.restrict K) Set.univ = 0 := by
    have h6 := ae_iff.mp h4
    simpa using h6
  rw [Measure.restrict_apply_univ] at h5
  rw [h5] at hvol
  exact lt_irrefl 0 hvol

set_option maxHeartbeats 400000 in
-- Heartbeats: the deep local-definition tower needs an enlarged elaboration budget.
-- The equality analysis chains a dozen nonlinear norm identities; the elaboration
-- needs an enlarged budget.
/-- **The equality case of the pointwise weight bound**: with exactly aligned coefficient
of modulus `k`, competitor coefficient bound `k` at the image, and weight exactly one,
the antiholomorphic derivative vanishes. -/
theorem rs_weight_equality {θ α β p b : ℂ} {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hθ : θ * starRingEnd ℂ θ = 1)
    (hjac : ‖β‖ < ‖α‖) (hp : p ≠ 0) (hb : ‖b‖ ≤ k * ‖p‖)
    (hchain : p * (β - (k : ℂ) * starRingEnd ℂ θ * α)
      = -(b * starRingEnd ℂ (α - (k : ℂ) * θ * β)))
    (hEq : ‖α - θ * β‖ ^ 2 / (‖α‖ ^ 2 - ‖β‖ ^ 2) = 1) :
    β = 0 := by
  set X : ℂ := α - (k : ℂ) * θ * β with hXdef
  set Y : ℂ := β - (k : ℂ) * starRingEnd ℂ θ * α with hYdef
  have hX1 : X - θ * Y = (1 + (k : ℂ)) * (α - θ * β) := by
    rw [hXdef, hYdef]
    linear_combination ((k : ℂ) * α) * hθ
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hYX : ‖Y‖ ≤ k * ‖X‖ := by
    have h1 : ‖p‖ * ‖Y‖ = ‖b‖ * ‖X‖ := by
      have h2 := congrArg norm hchain
      rwa [norm_mul, norm_neg, norm_mul, RCLike.norm_conj] at h2
    have h2 : ‖b‖ * ‖X‖ ≤ k * ‖p‖ * ‖X‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    nlinarith [h1, h2, hpn]
  have hnθ : ∀ w : ℂ, ‖θ * w‖ = ‖w‖ := by
    intro w
    have hθ1 : ‖θ‖ = 1 := by
      have h1 := congrArg norm hθ
      rw [norm_mul, RCLike.norm_conj, norm_one] at h1
      nlinarith [norm_nonneg θ]
    rw [norm_mul, hθ1, one_mul]
  have hJ : 0 < ‖α‖ ^ 2 - ‖β‖ ^ 2 := by nlinarith [norm_nonneg β]
  have hk2 : (1 - (k : ℂ) ^ 2) ≠ 0 := by
    intro h8
    have h9 : ((k ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination -h8
    have h10 : (k : ℝ) ^ 2 = 1 := by exact_mod_cast h9
    nlinarith
  have hX0 : 0 < ‖X‖ := by
    rcases eq_or_ne X 0 with hXz | hXz
    · exfalso
      have hYz : Y = 0 := by
        have h5 : ‖Y‖ ≤ 0 := by
          have h6 := hYX
          rw [hXz, norm_zero, mul_zero] at h6
          exact h6
        exact norm_eq_zero.mp (le_antisymm h5 (norm_nonneg _))
      have hαe : α - (k : ℂ) * θ * β = 0 := by rw [← hXdef]; exact hXz
      have hβe : β - (k : ℂ) * starRingEnd ℂ θ * α = 0 := by rw [← hYdef]; exact hYz
      have h6 : (1 - (k : ℂ) ^ 2) * α = 0 := by
        linear_combination hαe + (k : ℂ) * θ * hβe + ((k : ℂ) ^ 2 * α) * hθ
      have hαz : α = 0 := (mul_eq_zero.mp h6).resolve_left hk2
      rw [hαz, norm_zero] at hjac
      exact absurd hjac (not_lt.mpr (norm_nonneg β))
    · exact norm_pos_iff.mpr hXz
  -- the norm-square transfer of the frame
  have hXY2 : Complex.normSq X - Complex.normSq Y
      = (1 - k ^ 2) * (Complex.normSq α - Complex.normSq β) := by
    have hX2 : X + θ * Y = (1 - (k : ℂ)) * (α + θ * β) := by
      rw [hXdef, hYdef]
      linear_combination (-(k : ℂ) * α) * hθ
    have h1 := conj_pair_re X Y θ hθ
    rw [hX1, hX2] at h1
    have h2 : ((1 + (k : ℂ)) * (α - θ * β)
        * starRingEnd ℂ ((1 - (k : ℂ)) * (α + θ * β)))
        = ((1 - k ^ 2 : ℝ) : ℂ) * ((α - θ * β) * starRingEnd ℂ (α + θ * β)) := by
      simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
      push_cast
      ring
    rw [h2] at h1
    rw [← h1, Complex.re_ofReal_mul, conj_pair_re α β θ hθ]
  -- the equality extraction
  have hEq2 : ‖α - θ * β‖ ^ 2 = ‖α‖ ^ 2 - ‖β‖ ^ 2 := by
    rw [div_eq_one_iff_eq hJ.ne'] at hEq
    exact hEq
  have hnum : ‖α - θ * β‖ * (1 + k) = ‖X - θ * Y‖ := by
    rw [hX1, norm_mul]
    have h1 : ‖(1 + (k : ℂ))‖ = 1 + k := by
      rw [show (1 + (k : ℂ)) = ((1 + k : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [h1]
    ring
  have hkey1 : (1 - k) * ‖X - θ * Y‖ ^ 2 = (1 + k) * (‖X‖ ^ 2 - ‖Y‖ ^ 2) := by
    have h1 : ‖X - θ * Y‖ ^ 2 = (1 + k) ^ 2 * ‖α - θ * β‖ ^ 2 := by
      rw [← hnum, mul_pow]
      ring
    have h2 : ‖X‖ ^ 2 - ‖Y‖ ^ 2 = (1 - k ^ 2) * (‖α‖ ^ 2 - ‖β‖ ^ 2) := by
      have h3 := hXY2
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h3
      exact h3
    rw [h1, hEq2, h2]
    ring
  have hTri : ‖X - θ * Y‖ ≤ ‖X‖ + ‖Y‖ := by
    calc ‖X - θ * Y‖ ≤ ‖X‖ + ‖θ * Y‖ := norm_sub_le _ _
      _ = ‖X‖ + ‖Y‖ := by rw [hnθ]
  have hTri2 : ‖X - θ * Y‖ ^ 2 ≤ (‖X‖ + ‖Y‖) ^ 2 := by
    nlinarith [hTri, norm_nonneg (X - θ * Y)]
  have hYge : k * ‖X‖ ≤ ‖Y‖ := by
    nlinarith [hkey1, hTri2, hX0, norm_nonneg Y, hYX]
  have hYeq : ‖Y‖ = k * ‖X‖ := le_antisymm hYX hYge
  -- the positive alignment
  have hAl2 : ‖X - θ * Y‖ ^ 2 = (‖X‖ + ‖Y‖) ^ 2 := by
    have h4 : (1 - k) * ‖X - θ * Y‖ ^ 2 = (1 - k) * (‖X‖ + ‖Y‖) ^ 2 := by
      rw [hkey1, hYeq]
      ring
    exact mul_left_cancel₀ (by linarith : (1 : ℝ) - k ≠ 0) h4
  have hRe : (X * starRingEnd ℂ (θ * Y)).re = -(‖X‖ * ‖Y‖) := by
    have h6 : Complex.normSq (X - θ * Y) = Complex.normSq X + Complex.normSq (θ * Y)
        - 2 * (X * starRingEnd ℂ (θ * Y)).re := Complex.normSq_sub _ _
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hnθ] at h6
    have h7 : (‖X‖ + ‖Y‖) ^ 2 = ‖X‖ ^ 2 + 2 * (‖X‖ * ‖Y‖) + ‖Y‖ ^ 2 := by ring
    linarith [h6, hAl2, h7]
  set w : ℂ := X * starRingEnd ℂ (θ * Y) with hwdef
  have hwnorm : ‖w‖ = ‖X‖ * ‖Y‖ := by
    rw [hwdef, norm_mul, RCLike.norm_conj, hnθ]
  have hwre : w.re = -(‖w‖) := by
    rw [hwnorm]
    exact hRe
  have hwim : w.im = 0 := by
    have h8 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h9 : w.re ^ 2 = ‖w‖ ^ 2 := by
      rw [hwre]
      ring
    have h10 : w.im ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp h10
  have hwval : w = -((‖X‖ * ‖Y‖ : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.neg_re, Complex.ofReal_re, hwre, hwnorm]
    · rw [hwim, Complex.neg_im, Complex.ofReal_im, neg_zero]
  -- cancellation to the exact ray
  have hconjw : starRingEnd ℂ X * (θ * Y) = -((‖X‖ * ‖Y‖ : ℝ) : ℂ) := by
    have h11 := congrArg (starRingEnd ℂ) hwval
    rw [hwdef, map_mul, Complex.conj_conj, map_neg, Complex.conj_ofReal] at h11
    rw [← h11]
  have hXc0 : starRingEnd ℂ X ≠ 0 := by
    rw [map_ne_zero]
    exact norm_pos_iff.mp hX0
  have hgoal : starRingEnd ℂ X * (θ * Y) = starRingEnd ℂ X * (-(k : ℂ) * X) := by
    rw [hconjw, show starRingEnd ℂ X * (-(k : ℂ) * X)
        = -((k : ℂ) * (X * starRingEnd ℂ X)) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, hYeq]
    push_cast
    ring
  have hθY : θ * Y = -(k : ℂ) * X := mul_left_cancel₀ hXc0 hgoal
  -- the vanishing conclusion
  have hfin : (1 - (k : ℂ) ^ 2) * (θ * β) = 0 := by
    rw [hYdef, hXdef] at hθY
    linear_combination hθY + ((k : ℂ) * α) * hθ
  have hθβ : θ * β = 0 := (mul_eq_zero.mp hfin).resolve_left hk2
  have hθ0 : θ ≠ 0 := by
    intro h13
    rw [h13, zero_mul] at hθ
    exact zero_ne_one hθ
  exact (mul_eq_zero.mp hθβ).resolve_left hθ0

/-- **Fundamental-domain unfolding of `∂̄ = 0`**: for an equivariant upper-half-plane
quasiconformal map over a cocompact free Fuchsian base, vanishing of the antiholomorphic
derivative almost everywhere on the Dirichlet domain propagates to the whole upper half
plane along the countable family of group translates. -/
theorem dzbar_zero_unfold {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {H Hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper H Hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      H (moebiusMap γ z) = moebiusMap γ (H z))
    (hD0 : ∀ᵐ z ∂(volume.restrict
      (UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I)), dzbar H z = 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), dzbar H z = 0 := by
  have hcnt : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  set D : Set ℂ := UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I with hDdef
  have hDsub : D ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have hDmeas : MeasurableSet D := (isCompact_domain hΓ hfree hcc).measurableSet
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.continuous_im.measurable
  -- per-translate nullity on the domain
  have hTγ : ∀ γ : Γ, volume
      ({w : ℂ | ¬ dzbar H (moebiusMap ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) w)
        = 0} ∩ D) = 0 := by
    intro γ
    have hγinv : ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ Γ := (γ⁻¹ : Γ).2
    have hae : ∀ᵐ w ∂(volume.restrict D),
        dzbar H (moebiusMap ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) w) = 0 := by
      filter_upwards [hD0,
        ae_restrict_of_ae_restrict_of_subset hDsub (ae_differentiableAt hqc),
        ae_restrict_of_ae_restrict_of_subset hDsub (ae_diffAt_moebius hqc
          ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)),
        ae_restrict_mem hDmeas] with w h0 hdiff hdiffγ hwD
      have hwU : 0 < w.im := hDsub hwD
      have h1 := (wirtinger_moebius ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) hwU
        (hqc.mapsTo w hwU) (fun ζ hζ => hcomm _ hγinv ζ hζ) hdiff hdiffγ).2
      rw [h1, h0, mul_zero]
    have h2 := ae_iff.mp hae
    rwa [Measure.restrict_apply' hDmeas] at h2
  -- the exceptional set is covered by the translates of the domain bad sets
  set E : Set ℂ := {z : ℂ | 0 < z.im ∧ dzbar H z ≠ 0} with hEdef
  have hEcover : E ⊆ ⋃ γ : Γ,
      moebiusMap ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) ''
      ({w : ℂ | ¬ dzbar H (moebiusMap ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) w)
        = 0} ∩ D) := by
    rintro z ⟨hzU, hzne⟩
    set τ : UpperHalfPlane := ⟨z, hzU⟩ with hτdef
    obtain ⟨γ, hγD⟩ := exists_smul_mem_dirichletDomain hΓ UpperHalfPlane.I τ
    have hback : moebiusMap ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        (UpperHalfPlane.coe (γ • τ)) = z := by
      rw [← coe_smul_eq_moebiusMap]
      have h3 : ((γ⁻¹ : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (γ • τ) = τ := by
        have h4 : γ • τ = ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) • τ := rfl
        rw [h4, smul_smul]
        simp
      rw [h3]
    refine Set.mem_iUnion.mpr ⟨γ, ⟨UpperHalfPlane.coe (γ • τ), ⟨?_, ⟨γ • τ, hγD, rfl⟩⟩, hback⟩⟩
    simp only [Set.mem_ofPred_eq]
    rw [hback]
    exact hzne
  -- countable union of null translated images
  have hEnull : volume E = 0 := by
    refine measure_mono_null hEcover (measure_iUnion_null fun γ => ?_)
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume)
      ?_ (hTγ γ)
    intro w hw
    have hwU : 0 < w.im := hDsub hw.2
    exact (moebius_diffAt _ hwU).differentiableWithinAt
  -- conclusion
  rw [ae_iff, Measure.restrict_apply' hUm]
  refine measure_mono_null ?_ hEnull
  intro z hz
  exact ⟨hz.2, hz.1⟩

end RiemannDynamics
