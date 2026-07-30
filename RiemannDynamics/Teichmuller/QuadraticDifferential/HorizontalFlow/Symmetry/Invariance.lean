/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Symmetry.Symmetrization

/-!
# The unconditional symmetrized invariances

The full invariance identities of the symmetrized flow, the track separation estimates,
and the image-density identity along a leaf.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Two-step dichotomy along one trajectory window**: at the midpoint of a duration-`2s`
trajectory the two flow orientations reach the window endpoints, in one of the two
orientation pairings. -/
theorem two_step_core {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {s : ℝ} (hs : 0 < s) {σ : ℝ → ℂ} (hσ : IsTrajOn q σ (Set.Icc 0 (2 * s))) :
    (A.flow s (σ s) = σ (2 * s) ∧ A.flow (-s) (σ s) = σ 0) ∨
    (A.flow s (σ s) = σ 0 ∧ A.flow (-s) (σ s) = σ (2 * s)) := by
  have hsmem : s ∈ Set.Icc (0 : ℝ) (2 * s) := ⟨hs.le, by linarith⟩
  have hreg := traj_regular hσ hsmem
  have hact : A.active (A.sel (σ s)) := (A.sel_spec hreg.1 hreg.2).1
  have hrpos : 0 < A.r (A.sel (σ s)) := A.hr _ hact
  have hSmem : σ s ∈ Metric.ball (A.c (A.sel (σ s))) (2 * A.r (A.sel (σ s))) :=
    Metric.ball_subset_ball (by linarith) (A.sel_spec hreg.1 hreg.2).2
  obtain ⟨ε, hεpm, hev⟩ := traj_ambient_local Metric.isOpen_ball (A.hd _ hact)
    (A.hsq _ hact) hσ Set.Subset.rfl hsmem hSmem
  have hτp : IsTrajOn q (fun u => σ (u + s)) (Set.Icc 0 s) := by
    refine traj_mono (traj_shift s hσ) fun u hu => ?_
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hτm : IsTrajOn q (fun u => σ (s - u)) (Set.Icc 0 s) :=
    traj_reverse_at (traj_mono hσ (Set.Icc_subset_Icc le_rfl (by linarith)))
  have hmapp : Filter.Tendsto (fun u : ℝ => u + s)
      (nhdsWithin 0 (Set.Icc 0 s)) (nhdsWithin s (Set.Icc 0 (2 * s))) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h := (continuous_add_const s).tendsto (0 : ℝ)
      simpa using h
    · exact Filter.tendsto_principal_principal.mpr fun u hu =>
        ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hmapm : Filter.Tendsto (fun u : ℝ => s - u)
      (nhdsWithin 0 (Set.Icc 0 s)) (nhdsWithin s (Set.Icc 0 (2 * s))) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h := (continuous_sub_left s).tendsto (0 : ℝ)
      simpa using h
    · exact Filter.tendsto_principal_principal.mpr fun u hu =>
        ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩
  have hSp : SlopeAt (A.Φ (A.sel (σ s))) (fun u => σ (u + s))
      (Set.Icc 0 s) 0 ε := by
    change ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 s),
      A.Φ (A.sel (σ s)) (σ (u + s))
        = A.Φ (A.sel (σ s)) (σ (0 + s)) + (ε : ℂ) * ((u - 0 : ℝ) : ℂ)
    filter_upwards [hmapp.eventually hev] with u hu
    rw [zero_add]
    push_cast at hu ⊢
    linear_combination hu
  have hSm : SlopeAt (A.Φ (A.sel (σ s))) (fun u => σ (s - u))
      (Set.Icc 0 s) 0 (-ε) := by
    change ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 s),
      A.Φ (A.sel (σ s)) (σ (s - u))
        = A.Φ (A.sel (σ s)) (σ (s - 0)) + ((-ε : ℝ) : ℂ) * ((u - 0 : ℝ) : ℂ)
    filter_upwards [hmapm.eventually hev] with u hu
    rw [sub_zero]
    push_cast at hu ⊢
    linear_combination hu
  have hτp0 : (fun u => σ (u + s)) 0 = σ s := by
    change σ (0 + s) = σ s
    rw [zero_add]
  have hτps : (fun u => σ (u + s)) s = σ (2 * s) := by
    change σ (s + s) = σ (2 * s)
    rw [two_mul]
  have hτm0 : (fun u => σ (s - u)) 0 = σ s := by
    change σ (s - 0) = σ s
    rw [sub_zero]
  have hτms : (fun u => σ (s - u)) s = σ 0 := by
    change σ (s - s) = σ 0
    rw [sub_self]
  have hτp' : IsTrajOn q (fun u => σ (u + s)) (Set.Icc 0 (- -s)) := by
    rw [neg_neg]
    exact hτp
  have hτm' : IsTrajOn q (fun u => σ (s - u)) (Set.Icc 0 (- -s)) := by
    rw [neg_neg]
    exact hτm
  rcases hεpm with hε1 | hε1
  · left
    constructor
    · have hSp1 : SlopeAt (A.Φ (A.sel ((fun u => σ (u + s)) 0)))
          (fun u => σ (u + s)) (Set.Icc 0 s) 0 1 := by
        rw [hτp0, ← hε1]
        exact hSp
      have h1 := flow_eq_traj hq A hs hτp hSp1
      rw [zero_add] at h1
      rwa [← two_mul] at h1
    · have hSm1 : SlopeAt (A.Φ (A.sel ((fun u => σ (s - u)) 0)))
          (fun u => σ (s - u)) (Set.Icc 0 (- -s)) 0 (-1) := by
        rw [hτm0, neg_neg, ← hε1]
        exact hSm
      have h1 := flow_eq_traj_neg hq A (by linarith : -s < 0) hτm' hSm1
      rw [neg_neg] at h1
      rwa [sub_zero, sub_self] at h1
  · right
    constructor
    · have hSm1 : SlopeAt (A.Φ (A.sel ((fun u => σ (s - u)) 0)))
          (fun u => σ (s - u)) (Set.Icc 0 s) 0 1 := by
        rw [hτm0]
        have h := hSm
        rw [hε1] at h
        simpa using h
      have h1 := flow_eq_traj hq A hs hτm hSm1
      rwa [sub_zero, sub_self] at h1
    · have hSp1 : SlopeAt (A.Φ (A.sel ((fun u => σ (u + s)) 0)))
          (fun u => σ (u + s)) (Set.Icc 0 (- -s)) 0 (-1) := by
        rw [hτp0, neg_neg, ← hε1]
        exact hSp
      have h1 := flow_eq_traj_neg hq A (by linarith : -s < 0) hτp' hSp1
      rw [neg_neg] at h1
      rw [zero_add] at h1
      rwa [← two_mul] at h1

/-- **The dyadic two-step law on the regular set**: the `htwo` hypothesis of
`sym_invar_U` and `sym_invar_W`. -/
theorem htwo_flow {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (A : Atlas (q : ℂ → ℂ)) :
    ∀ z ∈ good (q : ℂ → ℂ) A, ∀ s : ℝ, 0 < s →
      ((A.flow s (A.flow s z) = A.flow (2 * s) z
          ∧ A.flow (-s) (A.flow s z) = z) ∨
        (A.flow s (A.flow s z) = z
          ∧ A.flow (-s) (A.flow s z) = A.flow (2 * s) z)) ∧
      ((A.flow s (A.flow (-s) z) = A.flow (-(2 * s)) z
          ∧ A.flow (-s) (A.flow (-s) z) = z) ∨
        (A.flow s (A.flow (-s) z) = z
          ∧ A.flow (-s) (A.flow (-s) z) = A.flow (-(2 * s)) z)) := by
  intro z hz s hs
  have h2s : (0 : ℝ) < 2 * s := by linarith
  constructor
  · obtain ⟨σ, hσ0, hσtraj, -, hσev⟩ := flow_traj_eval_pos q.holo A hz h2s
    have e1 : A.flow s z = σ s := hσev s ⟨hs.le, by linarith⟩
    have e2 : A.flow (2 * s) z = σ (2 * s) := hσev (2 * s) ⟨h2s.le, le_refl _⟩
    have hcore := two_step_core q.holo A hs hσtraj
    rw [← e1, ← e2, hσ0] at hcore
    exact hcore
  · obtain ⟨σ, hσ0, hσtraj, -, hσev⟩ := flow_traj_eval_neg q.holo A hz h2s
    have e1 : A.flow (-s) z = σ s := hσev s ⟨hs.le, by linarith⟩
    have e2 : A.flow (-(2 * s)) z = σ (2 * s) := hσev (2 * s) ⟨h2s.le, le_refl _⟩
    have hcore := two_step_core q.holo A hs hσtraj
    rw [← e1, ← e2, hσ0] at hcore
    exact hcore

/-- **Flow deck dichotomy**: at a regular point the deck translate of the flow pair is
the flow pair of the deck translate, in one of the two orientation pairings. -/
theorem flow_deck_swap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (A : Atlas (q : ℂ → ℂ))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    {z : ℂ} (hz : z ∈ good (q : ℂ → ℂ) A) {s : ℝ} (hs : 0 < s) :
    (A.flow s (moebiusMap γ z) = moebiusMap γ (A.flow s z)
      ∧ A.flow (-s) (moebiusMap γ z) = moebiusMap γ (A.flow (-s) z)) ∨
    (A.flow s (moebiusMap γ z) = moebiusMap γ (A.flow (-s) z)
      ∧ A.flow (-s) (moebiusMap γ z) = moebiusMap γ (A.flow s z)) := by
  obtain ⟨σ, hσ0, hσtraj, hσS, hσev⟩ := flow_traj_eval_pos q.holo A hz hs
  obtain ⟨σ', hσ'0, hσ'traj, hσ'S, hσ'ev⟩ := flow_traj_eval_neg q.holo A hz hs
  have hauto : ∀ w : ℂ, 0 < w.im →
      (q : ℂ → ℂ) (moebiusMap γ w) = moebiusDenom γ w ^ 4 * q w :=
    fun w hw => q.automorphy γ hγ w hw
  set τ : ℝ → ℂ := fun u => moebiusMap γ (σ u) with hτdef
  set τ' : ℝ → ℂ := fun u => moebiusMap γ (σ' u) with hτ'def
  have hτtraj : IsTrajOn (q : ℂ → ℂ) τ (Set.Icc 0 s) := traj_deck γ hauto hσtraj
  have hτ'traj : IsTrajOn (q : ℂ → ℂ) τ' (Set.Icc 0 s) := traj_deck γ hauto hσ'traj
  have hzim : 0 < z.im := hz.1
  have hγzim : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hzim
  have hγzq : (q : ℂ → ℂ) (moebiusMap γ z) ≠ 0 := by
    rw [hauto z hzim]
    exact mul_ne_zero (pow_ne_zero 4
      (moebiusDenom_ne_zero_of_im_ne_zero γ hzim.ne')) hz.2.1
  have hact : A.active (A.sel (moebiusMap γ z)) := (A.sel_spec hγzim hγzq).1
  have hrpos : 0 < A.r (A.sel (moebiusMap γ z)) := A.hr _ hact
  have hball : moebiusMap γ z ∈ Metric.ball (A.c (A.sel (moebiusMap γ z)))
      (2 * A.r (A.sel (moebiusMap γ z))) :=
    Metric.ball_subset_ball (by linarith) (A.sel_spec hγzim hγzq).2
  have hτ0 : τ 0 = moebiusMap γ z := by
    change moebiusMap γ (σ 0) = _
    rw [hσ0]
  have hτ'0 : τ' 0 = moebiusMap γ z := by
    change moebiusMap γ (σ' 0) = _
    rw [hσ'0]
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) s := Set.left_mem_Icc.mpr hs.le
  obtain ⟨ε, hεpm, hev⟩ := traj_ambient_local Metric.isOpen_ball (A.hd _ hact)
    (A.hsq _ hact) hτtraj Set.Subset.rfl h0mem (by rw [hτ0]; exact hball)
  obtain ⟨ε', hε'pm, hev'⟩ := traj_ambient_local Metric.isOpen_ball (A.hd _ hact)
    (A.hsq _ hact) hτ'traj Set.Subset.rfl h0mem (by rw [hτ'0]; exact hball)
  have key : ε' ≠ ε := by
    intro heq
    have hev'' : SlopeAt (A.Φ (A.sel (moebiusMap γ z))) τ' (Set.Icc 0 s) 0 ε := by
      rw [← heq]
      exact hev'
    have hEq := seed_unique Metric.isOpen_ball (A.hinj _ hact) hs.le hτtraj
      hτ'traj (hτ0.trans hτ'0.symm) (by rw [hτ0]; exact hball) hev hev''
    have hEqσ : Set.EqOn σ σ' (Set.Icc 0 s) := fun u hu =>
      moebius_injOn γ (traj_regular hσtraj hu).1 (traj_regular hσ'traj hu).1
        (hEq hu)
    have hσ'S2 := slope_congr hEqσ.symm h0mem hσ'S
    haveI := nebot_left hs
    have hclash := slope_eq hσS hσ'S2
    norm_num at hclash
  have hne : ε' = -ε := by
    rcases hεpm with h1 | h1 <;> rcases hε'pm with h2 | h2
    · exact absurd (h2.trans h1.symm) key
    · rw [h2, h1]
    · rw [h2, h1]
      norm_num
    · exact absurd (h2.trans h1.symm) key
  have hτs : τ s = moebiusMap γ (A.flow s z) := by
    change moebiusMap γ (σ s) = _
    rw [hσev s (Set.right_mem_Icc.mpr hs.le)]
  have hτ's : τ' s = moebiusMap γ (A.flow (-s) z) := by
    change moebiusMap γ (σ' s) = _
    rw [hσ'ev s (Set.right_mem_Icc.mpr hs.le)]
  rcases hεpm with h1 | h1
  · left
    have hε'1 : ε' = -1 := by rw [hne, h1]
    constructor
    · have hevS : SlopeAt (A.Φ (A.sel (τ 0))) τ (Set.Icc 0 s) 0 1 := by
        rw [hτ0, ← h1]
        exact hev
      have h2 := flow_eq_traj q.holo A hs hτtraj hevS
      rw [hτ0] at h2
      rw [h2, hτs]
    · have hτ'traj2 : IsTrajOn (q : ℂ → ℂ) τ' (Set.Icc 0 (- -s)) := by
        rw [neg_neg]
        exact hτ'traj
      have hevS' : SlopeAt (A.Φ (A.sel (τ' 0))) τ' (Set.Icc 0 (- -s)) 0 (-1) := by
        rw [hτ'0, neg_neg, ← hε'1]
        exact hev'
      have h2 := flow_eq_traj_neg q.holo A (by linarith : -s < 0) hτ'traj2 hevS'
      rw [neg_neg, hτ'0] at h2
      rw [h2, hτ's]
  · right
    have hε'1 : ε' = 1 := by
      rw [hne, h1]
      norm_num
    constructor
    · have hevS' : SlopeAt (A.Φ (A.sel (τ' 0))) τ' (Set.Icc 0 s) 0 1 := by
        rw [hτ'0, ← hε'1]
        exact hev'
      have h2 := flow_eq_traj q.holo A hs hτ'traj hevS'
      rw [hτ'0] at h2
      rw [h2, hτ's]
    · have hτtraj2 : IsTrajOn (q : ℂ → ℂ) τ (Set.Icc 0 (- -s)) := by
        rw [neg_neg]
        exact hτtraj
      have hevS : SlopeAt (A.Φ (A.sel (τ 0))) τ (Set.Icc 0 (- -s)) 0 (-1) := by
        rw [hτ0, neg_neg, ← h1]
        exact hev
      have h2 := flow_eq_traj_neg q.holo A (by linarith : -s < 0) hτtraj2 hevS
      rw [neg_neg, hτ0] at h2
      rw [h2, hτs]

/-- **Stepper preimage of a null set is null**: on a strong-legal layer the arrival map
pulls Lebesgue-null sets back to Lebesgue-null sets. -/
theorem pos_preimage_null {q : ℂ → ℂ} (hqm : Measurable q) (B : Atlas q)
    {h : ℝ} (hh : 0 < h) (Nn : ℕ) {N : Set ℂ} (hNm : MeasurableSet N)
    (hN0 : volume N = 0) :
    volume {z : ℂ | z ∈ slegal B h Nn ∧ pos B h (Nn + 1) z ∈ N} = 0 := by
  classical
  set S : Set ℂ := {z | z ∈ slegal B h Nn ∧ pos B h (Nn + 1) z ∈ N} with hSdef
  have hSm : MeasurableSet S := by
    have hset : S = slegal B h Nn ∩ (pos B h (Nn + 1)) ⁻¹' N := rfl
    rw [hset]
    exact (slegal_measurable B hh Nn).inter ((measurable_pos B h (Nn + 1)) hNm)
  have hEL : S ⊆ legal B h Nn := fun z hz => slegal_legal B hh.le Nn hz.1
  have hcov : S = ⋃ c : Fin (Nn + 1) → ℕ × Bool, itinPiece B h Nn S c := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · intro hz
      refine ⟨itin B h Nn z, hz, fun k => ⟨rfl, ?_⟩⟩
      have hpm := ((hEL hz) (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)).2.2.1
      change sgn B h (k : ℕ) z
        = (if (if sgn B h (k : ℕ) z = 1 then true else false)
          then (1 : ℝ) else -1)
      rcases hpm with h1 | h1
      · rw [if_pos h1]
        simp [h1]
      · rw [if_neg (by rw [h1]; norm_num)]
        simp [h1]
    · rintro ⟨c, hz⟩
      exact hz.1
  rw [hcov]
  refine measure_iUnion_null fun c => ?_
  have hPm : MeasurableSet (itinPiece B h Nn S c) := piece_measurable B h Nn hSm c
  have hPs : itinPiece B h Nn S c ⊆ slegal B h Nn := fun z hz => hz.1.1
  have hPc : ∀ z ∈ itinPiece B h Nn S c, ∀ k : Fin (Nn + 1),
      B.sel (pos B h (k : ℕ) z) = (c k).1 ∧
      sgn B h (k : ℕ) z = (if (c k).2 then (1 : ℝ) else -1) :=
    fun z hz k => hz.2 k
  obtain ⟨-, heq⟩ := piece_cov hqm B hh hPm hPs c hPc
    (measurable_const : Measurable fun _ : ℂ => (1 : ℝ≥0∞))
  have hsub : pos B h (Nn + 1) '' itinPiece B h Nn S c ⊆ N := by
    rintro w ⟨z, hz, rfl⟩
    exact hz.1.2
  have hzero' : ∫⁻ z in itinPiece B h Nn S c, ‖q z‖ₑ = 0 := by
    have hzero : ∫⁻ z in itinPiece B h Nn S c, (1 : ℝ≥0∞) * ‖q z‖ₑ = 0 := by
      rw [← heq]
      refine le_antisymm (le_trans (lintegral_mono_set hsub) ?_) (zero_le _)
      exact le_of_eq (setLIntegral_measure_zero _ _ hN0)
    rw [← hzero]
    exact lintegral_congr fun z => (one_mul _).symm
  have hae := (lintegral_eq_zero_iff hqm.enorm).mp hzero'
  have hfalse : ∀ᵐ z ∂(volume.restrict (itinPiece B h Nn S c)), False := by
    filter_upwards [hae, ae_restrict_mem hPm] with z h0 hzP
    exact (slegal_regular0 B (hPs hzP)).2 (enorm_eq_zero.mp h0)
  have huniv : (volume.restrict (itinPiece B h Nn S c)) Set.univ = 0 := by
    have h5 := ae_iff.mp hfalse
    simpa using h5
  rwa [Measure.restrict_apply_univ] at huniv

/-- **Flow preimage of a null set is almost nowhere met on the regular set.** -/
theorem flow_preimage_ae {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (A B : Atlas (q : ℂ → ℂ)) (f : ℂ → ℂ)
    {s : ℝ} (hs : 0 < s)
    (hflow : ∀ n : ℕ, ∀ z ∈ slegal B (s / (n + 1)) n,
      f z = pos B (s / (n + 1)) (n + 1) z)
    (hcov : ∀ z ∈ good (q : ℂ → ℂ) A, ∃ n : ℕ, z ∈ slegal B (s / (n + 1)) n)
    {N : Set ℂ} (hNm : MeasurableSet N) (hN0 : volume N = 0) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      z ∈ good (q : ℂ → ℂ) A → f z ∉ N := by
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hgrid : ∀ n : ℕ, (0 : ℝ) < s / (n + 1) := fun n => by positivity
  have hnull : volume {z : ℂ | z ∈ good (q : ℂ → ℂ) A ∧ f z ∈ N} = 0 := by
    refine measure_mono_null (fun z hz => ?_) (measure_iUnion_null (ι := ℕ)
      fun n => pos_preimage_null q.measurable B (hgrid n) n hNm hN0)
    obtain ⟨n, hn⟩ := hcov z hz.1
    refine Set.mem_iUnion.mpr ⟨n, hn, ?_⟩
    rw [← hflow n z hn]
    exact hz.2
  refine ae_iff.mpr ?_
  rw [Measure.restrict_apply' hUm]
  refine measure_mono_null (fun z hz => ?_) hnull
  have h1 := hz.1
  push Not at h1
  exact ⟨h1.1, h1.2⟩

/-- The flow of a regular point stays in the upper half plane at both orientations. -/
theorem flow_good_regular {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q)
    {z : ℂ} (hz : z ∈ good q A) {s : ℝ} (hs : 0 < s) :
    0 < (A.flow s z).im ∧ 0 < (A.flow (-s) z).im := by
  constructor
  · obtain ⟨σ, hσ0, hσtraj, -, hσev⟩ := flow_traj_eval_pos hq A hz hs
    rw [hσev s (Set.right_mem_Icc.mpr hs.le)]
    exact (traj_regular hσtraj (Set.right_mem_Icc.mpr hs.le)).1
  · obtain ⟨σ, hσ0, hσtraj, -, hσev⟩ := flow_traj_eval_neg hq A hz hs
    rw [hσev s (Set.right_mem_Icc.mpr hs.le)]
    exact (traj_regular hσtraj (Set.right_mem_Icc.mpr hs.le)).1

/-- **Deck compatibility engine**: an almost-everywhere `Γ`-invariant measurable weight
is almost everywhere compatible with the flow deck action at every fixed positive time. -/
theorem hdeck_engine {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (q : ℂ → ℂ)) {F : ℂ → ℝ≥0∞}
    (hFinv : ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      F (moebiusMap ↑γ z) = F z) :
    ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      F (A.flow s (moebiusMap ↑γ z)) + F (A.flow (-s) (moebiusMap ↑γ z))
        = F (A.flow s z) + F (A.flow (-s) z) := by
  intro s hs γ
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hN0' : volume ({w : ℂ | ¬ F (moebiusMap ↑γ w) = F w}
      ∩ {w : ℂ | 0 < w.im}) = 0 := by
    have h0 := ae_iff.mp (hFinv γ)
    rwa [Measure.restrict_apply' hUm] at h0
  set N : Set ℂ := toMeasurable volume
    ({w : ℂ | ¬ F (moebiusMap ↑γ w) = F w} ∩ {w : ℂ | 0 < w.im}) with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact hN0'
  have hsub := subset_toMeasurable volume
    ({w : ℂ | ¬ F (moebiusMap ↑γ w) = F w} ∩ {w : ℂ | 0 < w.im})
  have hfwd := flow_preimage_ae q A A (fun z => A.flow s z) hs
    (fun n z hz => flow_eq_pos_fwd q.holo A hs hz)
    (fun z hz => good_slegal_fwd q.holo A hs hz) hNm hN0
  have hbwd := flow_preimage_ae q A (mirrorAtlas A) (fun z => A.flow (-s) z)
    hs (fun n z hz => flow_eq_pos_bwd q.holo A hs hz)
    (fun z hz => good_slegal_bwd q.holo A hs hz) hNm hN0
  filter_upwards [good_ae hΓ hcc q hq0 A, hfwd, hbwd] with z hzg hf1 hf2
  have hreg := flow_good_regular q.holo A hzg hs
  have hw1 : F (moebiusMap ↑γ (A.flow s z)) = F (A.flow s z) := by
    by_contra hne
    exact hf1 hzg (hsub ⟨hne, hreg.1⟩)
  have hw2 : F (moebiusMap ↑γ (A.flow (-s) z)) = F (A.flow (-s) z) := by
    by_contra hne
    exact hf2 hzg (hsub ⟨hne, hreg.2⟩)
  rcases flow_deck_swap q A γ.2 hzg hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, hw1, hw2]
  · rw [e1, e2, hw2, hw1]
    exact add_comm _ _

/-- **Deck compatibility of the symmetrized first factor**: the `hdeckU` hypothesis of
`sym_invar_U`. -/
theorem sym_hdeckU {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsU (q : ℂ → ℂ) h κ (A.flow s (moebiusMap ↑γ z))
          + rsU (q : ℂ → ℂ) h κ (A.flow (-s) (moebiusMap ↑γ z))
        = rsU (q : ℂ → ℂ) h κ (A.flow s z)
          + rsU (q : ℂ → ℂ) h κ (A.flow (-s) z) :=
  hdeck_engine hΓ hcc q hq0 A (rsU_ae_inv q hqc hcomm)

/-- **Deck compatibility of the symmetrized floored weight**: the `hdeckW` hypothesis of
`sym_invar_W`. -/
theorem sym_hdeckW {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsWeightM (q : ℂ → ℂ) h κ (A.flow s (moebiusMap ↑γ z))
          + rsWeightM (q : ℂ → ℂ) h κ (A.flow (-s) (moebiusMap ↑γ z))
        = rsWeightM (q : ℂ → ℂ) h κ (A.flow s z)
          + rsWeightM (q : ℂ → ℂ) h κ (A.flow (-s) z) :=
  hdeck_engine hΓ hcc q hq0 A (rsWeightM_ae_inv q hqc hcomm)

/-- **Unconditional symmetrized flow invariance of the first factor**: the `invar_U`
field of `VerticalFlowDataSym` for the atlas flow, from the Reich–Strebel hypotheses. -/
theorem sym_invar_U_full {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hqc : IsQCUpper h hinv κ)
    (hh : Measurable h)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsU q h κ (A.flow t z) + rsU q h κ (A.flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsU q h κ z * ‖q z‖ₑ :=
  sym_invar_U hΓ hfree hcc q hq0 hκ hqc hh hcomm A (htwo_flow q A)
    (sym_hdeckU hΓ hcc q hq0 hqc hcomm A)

/-- **Unconditional symmetrized flow invariance of the floored weight**: the `invar_W`
field of `VerticalFlowDataSym` for the atlas flow, from the Reich–Strebel hypotheses. -/
theorem sym_invar_W_full {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ)) :
    ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsWeightM q h κ (A.flow t z) + rsWeightM q h κ (A.flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsWeightM q h κ z * ‖q z‖ₑ :=
  sym_invar_W hΓ hfree hcc q hq0 hκ hqc hcomm A (htwo_flow q A)
    (sym_hdeckW hΓ hcc q hq0 hqc hcomm A)

/-- **Uniform self-separation** of an injective compact track: points at parameter
distance at least `mesh` keep a positive spatial distance. -/
theorem track_separation {σ : ℝ → ℂ} {T : ℝ}
    (hc : ContinuousOn σ (Set.Icc 0 T)) (hinj : Set.InjOn σ (Set.Icc 0 T))
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ sep > 0, ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T,
      mesh ≤ |t - t'| → sep ≤ ‖σ t - σ t'‖ := by
  set P : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc 0 T ∧ p.2 ∈ Set.Icc 0 T ∧
    mesh ≤ |p.1 - p.2|} with hPdef
  by_cases hPne : P.Nonempty
  case neg =>
    refine ⟨1, one_pos, fun t ht t' ht' hd => ?_⟩
    exact absurd ⟨(t, t'), ht, ht', hd⟩ hPne
  case pos =>
  have hPclosed : IsClosed P := by
    have h1 : IsClosed {p : ℝ × ℝ | p.1 ∈ Set.Icc 0 T} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {p : ℝ × ℝ | p.2 ∈ Set.Icc 0 T} :=
      isClosed_Icc.preimage continuous_snd
    have h3 : IsClosed {p : ℝ × ℝ | mesh ≤ |p.1 - p.2|} :=
      isClosed_le continuous_const ((continuous_fst.sub continuous_snd).abs)
    exact h1.inter (h2.inter h3)
  have hPc : IsCompact P :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hPclosed
      fun p hp => ⟨hp.1, hp.2.1⟩
  have hfc : ContinuousOn (fun p : ℝ × ℝ => ‖σ p.1 - σ p.2‖) P := by
    refine ContinuousOn.norm (ContinuousOn.sub ?_ ?_)
    · exact hc.comp continuous_fst.continuousOn fun p hp => hp.1
    · exact hc.comp continuous_snd.continuousOn fun p hp => hp.2.1
  obtain ⟨p₀, hp₀, hmin⟩ := hPc.exists_isMinOn hPne hfc
  refine ⟨‖σ p₀.1 - σ p₀.2‖, ?_, ?_⟩
  · change 0 < ‖σ p₀.1 - σ p₀.2‖
    rw [norm_pos_iff, sub_ne_zero]
    intro heq
    have h4 := hinj hp₀.1 hp₀.2.1 heq
    have h5 := hp₀.2.2
    rw [h4] at h5
    simp at h5
    linarith
  · intro t ht t' ht' hd
    exact hmin (⟨ht, ht', hd⟩ : (t, t') ∈ P)

/-- **Near-diagonal lower separation**: inside a natural-chart ball with derivative
bound `C`, the parameter distance of two trajectory times is at most `C` times the
spatial distance of the track points. -/
theorem traj_lower_sep {q Φ : ℂ → ℂ} {x₀ : ℂ} {r C : ℝ}
    (hΦd : DifferentiableOn ℂ Φ (Metric.ball x₀ r))
    (hΦsq : ∀ w ∈ Metric.ball x₀ r, deriv Φ w ^ 2 = -q w)
    (hC : ∀ w ∈ Metric.ball x₀ r, ‖deriv Φ w‖ ≤ C)
    {σ : ℝ → ℂ} {I : Set ℝ} (hσ : IsTrajOn q σ I)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I)
    (htrack : ∀ t ∈ Set.Icc a b, σ t ∈ Metric.ball x₀ r) :
    ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, |t - t'| ≤ C * ‖σ t - σ t'‖ := by
  obtain ⟨ε, hε, haff⟩ := traj_ambient_affine Metric.isOpen_ball hΦd hΦsq hσ
    hab hI htrack
  have hmv : ∀ x ∈ Metric.ball x₀ r, ∀ y ∈ Metric.ball x₀ r,
      ‖Φ y - Φ x‖ ≤ C * ‖y - x‖ := by
    intro x hx y hy
    refine (convex_ball x₀ r).norm_image_sub_le_of_norm_fderivWithin_le hΦd ?_
      hx hy
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw]
    have hΦat : DifferentiableAt ℂ Φ w :=
      hΦd.differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    rw [hΦat.hasDerivAt.hasFDerivAt.fderiv]
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact hC w hw
  intro t ht t' ht'
  have h1 : Φ (σ t) - Φ (σ t') = (ε : ℂ) * ((t - t' : ℝ) : ℂ) := by
    rw [haff t ht, haff t' ht']
    push_cast
    ring
  have h2 : ‖Φ (σ t) - Φ (σ t')‖ = |t - t'| := by
    rw [h1, norm_mul]
    have hε1 : ‖(ε : ℂ)‖ = 1 := by
      rcases hε with h | h <;> rw [h] <;> norm_num
    rw [hε1, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |t - t'| = ‖Φ (σ t) - Φ (σ t')‖ := h2.symm
    _ ≤ C * ‖σ t - σ t'‖ := hmv _ (htrack t' ht') _ (htrack t ht)

/-- The real Fréchet derivative acts through the Wirtinger derivatives. -/
theorem fderiv_wirtinger_apply (f : ℂ → ℂ) (z u : ℂ) :
    (fderiv ℝ f z) u = dz f z * u + dzbar f z * (starRingEnd ℂ) u := by
  have hu' : u = (u.re : ℂ) + (u.im : ℂ) * Complex.I := (Complex.re_add_im u).symm
  have hu : u = u.re • (1 : ℂ) + u.im • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact hu'
  have happ : (fderiv ℝ f z) u
      = u.re • (fderiv ℝ f z) 1 + u.im • (fderiv ℝ f z) Complex.I := by
    conv_lhs => rw [hu]
    rw [map_add, map_smul, map_smul]
  have hconj : (starRingEnd ℂ) u = (u.re : ℂ) - u.im * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im u]
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [happ, dz, dzbar, hconj, Complex.real_smul, Complex.real_smul]
  have hI := Complex.I_mul_I
  linear_combination (-(1 / 2 : ℂ) * ((fderiv ℝ f z) 1
      - Complex.I * (fderiv ℝ f z) Complex.I)) * hu'
    + ((u.im : ℂ) * (fderiv ℝ f z) Complex.I) * hI

/-- **The flat-path structure of the image leaf**: the image under the quasiconformal
map of the unit-time reparametrized trajectory is a flat path once its absolute
continuity is known. -/
theorem image_flatPath {q : ℂ → ℂ} {h hinv : ℂ → ℂ} {κ : ℝ}
    (hqc : IsQCUpper h hinv κ) {σ : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hσ : IsTrajOn q σ (Set.Icc 0 T))
    (hac : AbsolutelyContinuousOnInterval (fun s => h (σ (s * T))) 0 1) :
    IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)) := by
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, s * T ∈ Set.Icc 0 T := by
    intro s hs
    exact ⟨mul_nonneg hs.1 hT.le, by nlinarith [hs.2]⟩
  have him : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < (σ (s * T)).im := fun s hs =>
    (traj_regular hσ (hmem s hs)).1
  refine ⟨?_, ?_, ?_, hac, ?_⟩
  · show h (σ (0 * T)) = h (σ 0)
    rw [zero_mul]
  · show h (σ (1 * T)) = h (σ T)
    rw [one_mul]
  · have hpc : ContinuousOn (fun s => σ (s * T)) (Set.Icc 0 1) := by
      refine ContinuousOn.comp hσ.cont ?_ hmem
      exact (continuous_mul_const T).continuousOn
    refine ContinuousOn.comp hqc.cont hpc fun s hs => him s hs
  · intro s hs
    exact hqc.mapsTo _ (him s hs)

/-- **Interior differentiability of trajectories**: at interior times a vertical
trajectory has a derivative whose square is `-q⁻¹`, through the analytic local inverse
of a defining natural chart. -/
theorem traj_hasDerivAt_interior {q : ℂ → ℂ} {σ : ℝ → ℂ} {a b : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc a b)) {v : ℝ} (hv : v ∈ Set.Ioo a b) :
    ∃ d : ℂ, HasDerivAt σ d v ∧ d ^ 2 = -(q (σ v))⁻¹ := by
  obtain ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ :=
    hσ.chart v ⟨hv.1.le, hv.2.le⟩
  have hnhds : nhdsWithin v (Set.Icc a b) = nhds v := by
    rw [nhdsWithin_eq_nhds]
    exact Icc_mem_nhds hv.1 hv.2
  rw [hnhds] at hev
  have hΦan : AnalyticAt ℂ Φ (σ v) := (hΦd.analyticOnNhd hUo) (σ v) hmem
  have hΦ' : deriv Φ (σ v) ≠ 0 := by
    intro h0
    have hsq := hΦsq (σ v) hmem
    rw [h0] at hsq
    exact hUne (σ v) hmem (by simpa using hsq.symm)
  have hstrict : HasStrictDerivAt Φ (deriv Φ (σ v)) (σ v) :=
    (hΦan.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  set ψ : ℂ → ℂ := hstrict.localInverse Φ (deriv Φ (σ v)) (σ v) hΦ' with hψdef
  have hψd : HasStrictDerivAt ψ (deriv Φ (σ v))⁻¹ (Φ (σ v)) :=
    hstrict.to_localInverse hΦ'
  have hleft : ∀ᶠ w in nhds (σ v), ψ (Φ w) = w :=
    hstrict.eventually_left_inverse hΦ'
  have hσcont : ContinuousAt σ v :=
    (hσ.cont v ⟨hv.1.le, hv.2.le⟩).continuousAt (Icc_mem_nhds hv.1 hv.2)
  have hgerm : ∀ᶠ u in nhds v,
      σ u = ψ (Φ (σ v) + ((u - v : ℝ) : ℂ)) := by
    filter_upwards [hev, hσcont.eventually hleft] with u hu hlu
    rw [← hu.2, hlu]
  have hinner : HasDerivAt (fun u : ℝ => Φ (σ v) + ((u - v : ℝ) : ℂ)) 1 v := by
    have h1 : HasDerivAt (fun u : ℝ => ((u - v : ℝ) : ℂ)) 1 v := by
      have h2 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 v := by
        simpa using Complex.ofRealCLM.hasDerivAt (x := v)
      have h3 : HasDerivAt (fun u : ℝ => (u : ℂ) - (v : ℂ)) 1 v := h2.sub_const _
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards with u
      push_cast
      ring
    simpa using h1.const_add (Φ (σ v))
  have hψat : HasDerivAt ψ (deriv Φ (σ v))⁻¹ (Φ (σ v) + ((v - v : ℝ) : ℂ)) := by
    have h0 : (Φ (σ v) + ((v - v : ℝ) : ℂ)) = Φ (σ v) := by
      push_cast
      ring
    rw [h0]
    exact hψd.hasDerivAt
  have hmodel : HasDerivAt (fun u : ℝ => ψ (Φ (σ v) + ((u - v : ℝ) : ℂ)))
      ((deriv Φ (σ v))⁻¹) v := by
    have := hψat.comp v hinner
    simpa using this
  refine ⟨(deriv Φ (σ v))⁻¹, hmodel.congr_of_eventuallyEq hgerm, ?_⟩
  rw [inv_pow, hΦsq (σ v) hmem, ← inv_neg]

/-- **The image-density identity**: along a unit-speed vertical leaf the
horizontal transverse density of the image curve is the flat-time multiple of the
sealed image density, wherever the chain-rule derivative and the Beltrami bound hold. -/
theorem image_density_eq {q h : ℂ → ℂ} {κ : ℝ} {w d : ℂ} {T : ℝ}
    (hT : 0 < T) (hq0 : q w ≠ 0) (hd2 : d ^ 2 = -(q w)⁻¹)
    (hbelt : ‖dzbar h w‖ ≤ κ * ‖dz h w‖)
    {γ : ℝ → ℂ} {s : ℝ} (hγs : γ s = h w)
    (hγd : deriv γ s = (fderiv ℝ h w) (((T : ℝ) : ℂ) * d)) :
    horizontalDensity q γ s = ENNReal.ofReal T * rsDensity q h w := by
  have hdne : d ≠ 0 := by
    intro h0
    rw [h0] at hd2
    have h2 := hd2.symm
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h2
    exact hq0 (inv_eq_zero.mp (neg_eq_zero.mp h2))
  have hnq : ((‖q w‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq0)
  have hdd : d * (starRingEnd ℂ) d = ((‖q w‖⁻¹ : ℝ) : ℂ) := by
    have h2 : ‖d‖ ^ 2 = ‖q w‖⁻¹ := by
      rw [← norm_pow, hd2, norm_neg, norm_inv]
    rw [Complex.mul_conj, ← h2, Complex.normSq_eq_norm_sq]
  have hconj : (starRingEnd ℂ) d = -(q w / ((‖q w‖ : ℝ) : ℂ)) * d := by
    refine mul_right_cancel₀ hdne ?_
    have hnr : ‖q w‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
    rw [mul_comm ((starRingEnd ℂ) d) d, hdd, mul_assoc,
      mul_comm d d, ← sq, hd2]
    push_cast
    field_simp
  have hkey : q (γ s) * deriv γ s ^ 2 = ((T : ℝ) : ℂ) ^ 2 * rsQ q h w := by
    rw [hγs, hγd, fderiv_wirtinger_apply, rsQ]
    have hconjT : (starRingEnd ℂ) (((T : ℝ) : ℂ) * d)
        = ((T : ℝ) : ℂ) * (starRingEnd ℂ) d := by
      rw [map_mul, Complex.conj_ofReal]
    rw [hconjT, hconj]
    by_cases hdz : dz h w = 0
    · have hdzb : dzbar h w = 0 := by
        have hb := hbelt
        rw [hdz, norm_zero, mul_zero] at hb
        exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      rw [hdz, hdzb]
      ring
    · have hwq : wirtingerQuotient h w = dzbar h w / dz h w := rfl
      have hfac : dz h w * (1 - dzbar h w / dz h w * (q w / ((‖q w‖ : ℝ) : ℂ)))
          = dz h w - dzbar h w * (q w / ((‖q w‖ : ℝ) : ℂ)) := by
        field_simp
      have hL : q (h w) * (dz h w * (((T : ℝ) : ℂ) * d)
            + dzbar h w * (((T : ℝ) : ℂ) * (-(q w / ((‖q w‖ : ℝ) : ℂ)) * d))) ^ 2
          = q (h w) * ((T : ℝ) : ℂ) ^ 2 * d ^ 2
            * (dz h w - dzbar h w * (q w / ((‖q w‖ : ℝ) : ℂ))) ^ 2 := by
        ring
      have hR : ((T : ℝ) : ℂ) ^ 2
            * (-(q (h w) * dz h w ^ 2
              * (1 - wirtingerQuotient h w * (q w / ((‖q w‖ : ℝ) : ℂ))) ^ 2) / q w)
          = q (h w) * ((T : ℝ) : ℂ) ^ 2 * (-(q w)⁻¹)
            * (dz h w - dzbar h w * (q w / ((‖q w‖ : ℝ) : ℂ))) ^ 2 := by
        rw [hwq, ← hfac]
        field_simp
      calc q (h w) * (dz h w * (((T : ℝ) : ℂ) * d)
            + dzbar h w * (((T : ℝ) : ℂ) * (-(q w / ((‖q w‖ : ℝ) : ℂ)) * d))) ^ 2
          = q (h w) * ((T : ℝ) : ℂ) ^ 2 * d ^ 2
            * (dz h w - dzbar h w * (q w / ((‖q w‖ : ℝ) : ℂ))) ^ 2 := hL
        _ = q (h w) * ((T : ℝ) : ℂ) ^ 2 * (-(q w)⁻¹)
            * (dz h w - dzbar h w * (q w / ((‖q w‖ : ℝ) : ℂ))) ^ 2 := by
            rw [hd2]
        _ = ((T : ℝ) : ℂ) ^ 2
            * (-(q (h w) * dz h w ^ 2
              * (1 - wirtingerQuotient h w * (q w / ((‖q w‖ : ℝ) : ℂ))) ^ 2) / q w) :=
            hR.symm
  unfold horizontalDensity
  rw [hkey, rsDensity]
  have hT2 : ((T : ℝ) : ℂ) ^ 2 = ((T ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hT2, norm_mul, Complex.re_ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T)]
  have harg : (T ^ 2 * ‖rsQ q h w‖ - T ^ 2 * (rsQ q h w).re) / 2
      = T ^ 2 * ((‖rsQ q h w‖ - (rsQ q h w).re) / 2) := by
    ring
  rw [harg, Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT.le,
    ENNReal.ofReal_mul hT.le]

/-- **Foliated Fubini regularity**: for almost every regular start point, at almost
every time the flow point carries the differentiability and Beltrami bound of the
quasiconformal map, and lies in the upper half plane. -/
theorem flow_diff_ae {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ᵐ t ∂(volume : Measure ℝ),
        DifferentiableAt ℝ h (A.flow t z)
          ∧ ‖dzbar h (A.flow t z)‖ ≤ κ * ‖dz h (A.flow t z)‖
          ∧ 0 < (A.flow t z).im := by
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hN0' : volume ({w : ℂ | ¬ (DifferentiableAt ℝ h w
      ∧ ‖dzbar h w‖ ≤ κ * ‖dz h w‖)} ∩ {w : ℂ | 0 < w.im}) = 0 := by
    have hae := (ae_differentiableAt hqc).and hqc.belt
    have h0 := ae_iff.mp hae
    rwa [Measure.restrict_apply' hUm] at h0
  set N : Set ℂ := toMeasurable volume
    ({w : ℂ | ¬ (DifferentiableAt ℝ h w ∧ ‖dzbar h w‖ ≤ κ * ‖dz h w‖)}
      ∩ {w : ℂ | 0 < w.im}) with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact hN0'
  have hsub := subset_toMeasurable volume
    ({w : ℂ | ¬ (DifferentiableAt ℝ h w ∧ ‖dzbar h w‖ ≤ κ * ‖dz h w‖)}
      ∩ {w : ℂ | 0 < w.im})
  have hsec : ∀ t : ℝ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      A.flow t z ∉ N := by
    intro t
    rcases lt_trichotomy t 0 with htn | ht0 | htp
    · have hminus : (0 : ℝ) < -t := by linarith
      have hb := flow_preimage_ae q A (mirrorAtlas A)
        (fun z => A.flow (-(-t)) z) hminus
        (fun n z hz => flow_eq_pos_bwd q.holo A hminus hz)
        (fun z hz => good_slegal_bwd q.holo A hminus hz) hNm hN0
      simp only [neg_neg] at hb
      filter_upwards [good_ae hΓ hcc q hq0 A, hb] with z hzg hzb
      exact hzb hzg
    · subst ht0
      have hnotN : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∉ N := by
        refine ae_iff.mpr ?_
        have hset : {a : ℂ | ¬ a ∉ N} = N := by
          ext a
          simp [not_not]
        rw [hset, Measure.restrict_apply' hUm]
        exact measure_mono_null Set.inter_subset_left hN0
      filter_upwards [hnotN, q.ae_ne_zero hq0, ae_restrict_mem hUm]
        with z hzN hqz hzU
      intro hflowN
      rw [flow_zero A hzU hqz] at hflowN
      exact hzN hflowN
    · have hb := flow_preimage_ae q A A (fun z => A.flow t z) htp
        (fun n z hz => flow_eq_pos_fwd q.holo A htp hz)
        (fun z hz => good_slegal_fwd q.holo A htp hz) hNm hN0
      filter_upwards [good_ae hΓ hcc q hq0 A, hb] with z hzg hzb
      exact hzb hzg
  have hsec0 : ∀ t : ℝ, (volume.restrict {z : ℂ | 0 < z.im})
      {z : ℂ | A.flow t z ∈ N} = 0 := by
    intro t
    have h1 := ae_iff.mp (hsec t)
    have hset : {a : ℂ | ¬ A.flow t a ∉ N} = {a : ℂ | A.flow t a ∈ N} := by
      ext a
      simp [not_not]
    rwa [hset] at h1
  set S : Set (ℝ × ℂ) := (fun p : ℝ × ℂ => A.flow p.1 p.2) ⁻¹' N with hSdef
  have hSm : MeasurableSet S := A.measurable_flow hNm
  have hprod : ((volume : Measure ℝ).prod
      (volume.restrict {z : ℂ | 0 < z.im})) S = 0 := by
    rw [Measure.prod_apply hSm]
    have hpt : ∀ t : ℝ, (volume.restrict {z : ℂ | 0 < z.im})
        (Prod.mk t ⁻¹' S) = 0 := fun t => hsec0 t
    simp [hpt]
  have hswap : ((volume.restrict {z : ℂ | 0 < z.im}).prod (volume : Measure ℝ))
      {p : ℂ × ℝ | A.flow p.2 p.1 ∈ N} = 0 := by
    have hXm : MeasurableSet {p : ℂ × ℝ | A.flow p.2 p.1 ∈ N} :=
      (A.measurable_flow.comp (measurable_snd.prodMk measurable_fst)) hNm
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap hXm]
    exact hprod
  have hae2 : ∀ᵐ p ∂((volume.restrict {z : ℂ | 0 < z.im}).prod
      (volume : Measure ℝ)), A.flow p.2 p.1 ∉ N := by
    refine ae_iff.mpr ?_
    have hset : {p : ℂ × ℝ | ¬ A.flow p.2 p.1 ∉ N}
        = {p : ℂ × ℝ | A.flow p.2 p.1 ∈ N} := by
      ext p
      simp [not_not]
    rw [hset]
    exact hswap
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  filter_upwards [hae3] with z hz
  intro hzg
  have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    refine ae_iff.mpr ?_
    have hset : {t : ℝ | ¬ t ≠ 0} = {(0 : ℝ)} := by
      ext t
      simp
    rw [hset]
    exact Real.volume_singleton
  filter_upwards [hz, hne0] with t htN htne
  have him : 0 < (A.flow t z).im := by
    rcases lt_or_gt_of_ne htne with hlt | hgt
    · have h2 := (flow_good_regular q.holo A hzg (by linarith : (0 : ℝ) < -t)).2
      simpa using h2
    · exact (flow_good_regular q.holo A hzg hgt).1
  have hprop : DifferentiableAt ℝ h (A.flow t z)
      ∧ ‖dzbar h (A.flow t z)‖ ≤ κ * ‖dz h (A.flow t z)‖ := by
    by_contra hcon
    exact htN (hsub ⟨hcon, him⟩)
  exact ⟨hprop.1, hprop.2, him⟩

/-- Almost-everywhere properties pull back along positive time scalings. -/
theorem ae_scale_pos {P : ℝ → Prop} (hP : ∀ᵐ t ∂(volume : Measure ℝ), P t)
    {T : ℝ} (hT : 0 < T) : ∀ᵐ s ∂(volume : Measure ℝ), P (s * T) := by
  have hE0 : volume {t : ℝ | ¬ P t} = 0 := ae_iff.mp hP
  set E : Set ℝ := toMeasurable volume {t : ℝ | ¬ P t} with hEdef
  have hEm : MeasurableSet E := measurableSet_toMeasurable _ _
  have hE : volume E = 0 := by
    rw [hEdef, measure_toMeasurable]
    exact hE0
  have hEsub := subset_toMeasurable volume {t : ℝ | ¬ P t}
  refine ae_iff.mpr
    (measure_mono_null (t := (fun s : ℝ => T * s) ⁻¹' E) (fun s hs => ?_) ?_)
  · have hs2 : ¬ P (T * s) := by
      rw [mul_comm]
      exact hs
    exact hEsub hs2
  · rw [← Measure.map_apply (measurable_const_mul T) hEm,
      Real.map_volume_mul_left hT.ne']
    simp [Measure.smul_apply, hE]

/-- Almost every point of the closed unit interval is interior. -/
theorem ae_mem_Ioo01 :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), s ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ae_iff.mpr ?_
  rw [Measure.restrict_apply' measurableSet_Icc]
  refine measure_mono_null (t := {(0 : ℝ)} ∪ {(1 : ℝ)}) (fun s hs => ?_)
    (measure_union_null Real.volume_singleton Real.volume_singleton)
  obtain ⟨hs1, hs2⟩ := hs
  rw [Set.mem_setOf_eq, Set.mem_Ioo] at hs1
  push Not at hs1
  by_cases hs0 : s = 0
  · exact Or.inl hs0
  · have hpos : 0 < s := lt_of_le_of_ne hs2.1 (Ne.symm hs0)
    exact Or.inr (le_antisymm hs2.2 (hs1 hpos))

/-- **The reparametrization bound**: for almost every regular start point and every
horizon, the horizontal variation of the image of the unit-time reparametrized flow
trajectory is dominated by the flow integral of the sealed image density — with
equality of the underlying densities almost everywhere. -/
theorem sym_hrepar {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ) (A : Atlas (q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      horizontalVariation (q : ℂ → ℂ) (fun s => h (σ (s * T)))
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity (q : ℂ → ℂ) h (A.flow t z) := by
  filter_upwards [flow_diff_ae hΓ hcc q hq0 hqc A] with z hz
  intro hzg T hT σ hσtraj hσev
  have hpull := ae_scale_pos (hz hzg) hT
  have haes : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      horizontalDensity (q : ℂ → ℂ) (fun s' => h (σ (s' * T))) s
        = ENNReal.ofReal T * rsDensity (q : ℂ → ℂ) h (A.flow (s * T) z) := by
    filter_upwards [ae_restrict_of_ae hpull, ae_mem_Ioo01] with s hs hsIoo
    have hvIoo : s * T ∈ Set.Ioo 0 T :=
      ⟨mul_pos hsIoo.1 hT, by nlinarith [hsIoo.2]⟩
    have hvIcc : s * T ∈ Set.Icc 0 T := ⟨hvIoo.1.le, hvIoo.2.le⟩
    have hflowe : A.flow (s * T) z = σ (s * T) := hσev _ hvIcc
    rw [hflowe] at hs
    obtain ⟨hdh, hbelt, him⟩ := hs
    obtain ⟨d, hdAt, hd2⟩ := traj_hasDerivAt_interior hσtraj hvIoo
    have hqw0 : (q : ℂ → ℂ) (σ (s * T)) ≠ 0 := (traj_regular hσtraj hvIcc).2
    have hmulT : HasDerivAt (fun x : ℝ => x * T) T s := hasDerivAt_mul_const T
    have hp : HasDerivAt (fun s' : ℝ => σ (s' * T)) (T • d) s :=
      hdAt.scomp s hmulT
    have hγ : HasDerivAt (fun s' : ℝ => h (σ (s' * T)))
        ((fderiv ℝ h (σ (s * T))) (T • d)) s :=
      hdh.hasFDerivAt.comp_hasDerivAt s hp
    have hγd : deriv (fun s' : ℝ => h (σ (s' * T))) s
        = (fderiv ℝ h (σ (s * T))) (((T : ℝ) : ℂ) * d) := by
      rw [hγ.deriv]
      congr 1
    rw [hflowe]
    exact image_density_eq hT hqw0 hd2 hbelt rfl hγd
  change (∫⁻ s in Set.Icc (0 : ℝ) 1,
      horizontalDensity (q : ℂ → ℂ) (fun s' => h (σ (s' * T))) s)
    ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, rsDensity (q : ℂ → ℂ) h (A.flow t z)
  rw [lintegral_congr_ae haes,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hcov := setLIntegral_affine
    (fun t => rsDensity (q : ℂ → ℂ) h (A.flow t z)) hT 0 (Set.Icc 0 1)
  have himg : (fun s : ℝ => T * s + 0) '' Set.Icc 0 1 = Set.Icc (0 : ℝ) T := by
    rw [image_affine_Icc hT 0 0 1]
    norm_num
  rw [himg] at hcov
  have hcomm : ∫⁻ s in Set.Icc (0 : ℝ) 1,
      rsDensity (q : ℂ → ℂ) h (A.flow (s * T) z)
      = ∫⁻ s in Set.Icc (0 : ℝ) 1,
        rsDensity (q : ℂ → ℂ) h (A.flow (T * s + 0) z) := by
    refine lintegral_congr fun s => ?_
    rw [add_zero, mul_comm]
  rw [hcomm, hcov, ← mul_assoc, ← ENNReal.ofReal_mul hT.le,
    mul_inv_cancel₀ hT.ne', ENNReal.ofReal_one, one_mul]

/-- **The flat-path field in consumable form**: conditional on leafwise absolute
continuity of the image reparametrization, almost every regular start point yields the
flat-path structure for every horizon along the flow trajectory. -/
theorem sym_hpath_of_acl {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (A : Atlas (q : ℂ → ℂ))
    {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (hacl : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      AbsolutelyContinuousOnInterval (fun s => h (σ (s * T))) 0 1) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), z ∈ good (q : ℂ → ℂ) A →
      ∀ T : ℝ, 0 < T → ∀ σ : ℝ → ℂ, IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 T) →
      (∀ u ∈ Set.Icc 0 T, A.flow u z = σ u) →
      IsFlatPath (fun s => h (σ (s * T))) (h (σ 0)) (h (σ T)) := by
  filter_upwards [hacl] with z hz
  intro hzg T hT σ hσ hσev
  exact image_flatPath hqc hT hσ (hz hzg T hT σ hσ hσev)

/-- **Segment variation bound**: on a parameter subinterval whose track lies in an open
set carrying a global natural chart, the horizontal variation of the subinterval
dominates the developed real displacement of its endpoints. -/
theorem segment_variation_lb {q Φg : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΦgd : DifferentiableOn ℂ Φg U)
    (hΦgsq : ∀ w ∈ U, deriv Φg w ^ 2 = -q w)
    {p : ℝ → ℂ} {α β : ℝ} (hαβ : α < β)
    (hpc : ContinuousOn p (Set.Icc α β))
    (hpac : AbsolutelyContinuousOnInterval p α β)
    (htr : ∀ s ∈ Set.Icc α β, p s ∈ U) :
    ENNReal.ofReal |(Φg (p β)).re - (Φg (p α)).re|
      ≤ ∫⁻ s in Set.Icc α β, horizontalDensity q p s := by
  set c : ℝ := β - α with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set r : ℝ → ℂ := fun s => p (c * s + α) with hrdef
  have haff : ∀ s ∈ Set.Icc (0 : ℝ) 1, c * s + α ∈ Set.Icc α β := by
    intro s hs
    constructor
    · nlinarith [hs.1]
    · nlinarith [hs.2]
  have hrc : ContinuousOn r (Set.Icc 0 1) := by
    refine hpc.comp ((continuous_const.mul continuous_id).add
      continuous_const).continuousOn haff
  have hrac : AbsolutelyContinuousOnInterval r 0 1 := by
    have h0 : AbsolutelyContinuousOnInterval p (c * 0 + α) (c * 1 + α) := by
      have h1 : c * 0 + α = α := by ring
      have h2 : c * 1 + α = β := by rw [hcdef]; ring
      rw [h1, h2]
      exact hpac
    exact acOn_comp_affine hc h0
  have hrtr : ∀ s ∈ Set.Icc (0 : ℝ) 1, r s ∈ U := fun s hs =>
    htr _ (haff s hs)
  have hmain := global_chart_variation_lb hU hΦgd hΦgsq hrc hrac hrtr
  have hr0 : r 0 = p α := by
    rw [hrdef]
    change p (c * 0 + α) = p α
    rw [show c * 0 + α = α by ring]
  have hr1 : r 1 = p β := by
    rw [hrdef]
    change p (c * 1 + α) = p β
    rw [show c * 1 + α = β by rw [hcdef]; ring]
  rw [hr0, hr1] at hmain
  refine le_trans hmain ?_
  -- CoV back: ∫_{[0,1]} d_r = ∫_{[α,β]} d_p
  have hden : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      horizontalDensity q r s
        = ENNReal.ofReal c * horizontalDensity q p (c * s + α) := by
    refine Filter.Eventually.of_forall fun s => ?_
    exact horizontalDensity_affine q p α s hc
  rw [lintegral_congr_ae hden,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_affine (horizontalDensity q p) hc α (Set.Icc 0 1),
    image_affine_Icc hc α 0 1]
  rw [show c * 0 + α = α by ring, show c * 1 + α = β by rw [hcdef]; ring]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le]
  rw [show c * c⁻¹ = 1 by field_simp]
  simp

/-- **The negated automorphic differential**: the carrier of the transverse foliation.
-/
noncomputable def qdNeg (q : QuadraticDifferential Γ) :
    QuadraticDifferential Γ where
  toFun := fun z => -(q z)
  measurable := q.measurable.neg
  holo := q.holo.neg
  automorphy := by
    intro γ hγ z hz
    rw [q.automorphy γ hγ z hz]
    ring

/-- The negated differential evaluates pointwise to the negation. -/
@[simp]
theorem qdNeg_apply (q : QuadraticDifferential Γ) (z : ℂ) :
    qdNeg q z = -(q z) := rfl

/-- The negated differential is somewhere nonzero when the original is. -/
theorem qdNeg_ne_zero (q : QuadraticDifferential Γ)
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) :
    ∃ z₀ : ℂ, 0 < z₀.im ∧ qdNeg q z₀ ≠ 0 := by
  obtain ⟨z₀, hz, h0⟩ := hq0
  exact ⟨z₀, hz, by simpa using h0⟩

/-- **Almost every point is transversely regular**: the two-sided regular set of the
negated differential has full measure. -/
theorem good_ae_neg (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (qdNeg q : ℂ → ℂ)) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      z ∈ good (qdNeg q : ℂ → ℂ) A :=
  good_ae hΓ hcc (qdNeg q) (qdNeg_ne_zero q hq0) A

/-- The union of the horizontal lines over a null set of heights is null. -/
theorem line_heights_null {E : Set ℝ} (hE : volume E = 0) :
    volume {w : ℂ | w.im ∈ E} = 0 := by
  set E' : Set ℝ := toMeasurable volume E with hE'def
  have hE'm : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hE'0 : volume E' = 0 := by
    rw [hE'def, measure_toMeasurable]
    exact hE
  have hE'null : volume {w : ℂ | w.im ∈ E'} = 0 := by
    have hpre : {w : ℂ | w.im ∈ E'}
        = Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ E') := by
      ext w
      simp [Complex.measurableEquivRealProd_apply]
    rw [hpre,
      Complex.volume_preserving_equiv_real_prod.measure_preimage
        (MeasurableSet.univ.prod hE'm).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, hE'0, mul_zero]
  exact measure_mono_null
    (fun w hw => (subset_toMeasurable volume E hw : w.im ∈ E')) hE'null

/-- **Transverse nullity in a natural chart**: the chart preimage of a null set of
developed heights is null, since the chart Jacobian is the `|q|` density. -/
theorem chartline_heights_null {q : ℂ → ℂ} (hqm : Measurable q) (A : Atlas q)
    {j : ℕ} (hj : A.active j) {E : Set ℝ} (hE : volume E = 0) :
    volume {z : ℂ | z ∈ Metric.ball (A.c j) (2 * A.r j) ∧ (A.Φ j z).im ∈ E} = 0 := by
  set B : Set ℂ := toMeasurable volume {w : ℂ | w.im ∈ E} with hBdef
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : volume B = 0 := by
    rw [hBdef, measure_toMeasurable]
    exact line_heights_null hE
  have hBsub := subset_toMeasurable volume {w : ℂ | w.im ∈ E}
  set X : Set ℂ := Metric.ball (A.c j) (2 * A.r j) ∩ A.mchart j ⁻¹' B with hXdef
  have hXm : MeasurableSet X :=
    measurableSet_ball.inter ((A.measurable_mchart j) hBm)
  refine measure_mono_null (t := X) (fun z hz => ?_) ?_
  · refine ⟨hz.1, ?_⟩
    change A.mchart j z ∈ B
    rw [A.mchart_eq hj hz.1]
    exact hBsub hz.2
  · have hXball : X ⊆ Metric.ball (A.c j) (2 * A.r j) := Set.inter_subset_left
    have hfd : ∀ z ∈ X, HasFDerivWithinAt (A.Φ j) (fderiv ℝ (A.Φ j) z) X z := by
      intro z hz
      have hdC : DifferentiableAt ℂ (A.Φ j) z :=
        (A.hd j hj).differentiableAt (Metric.isOpen_ball.mem_nhds (hXball hz))
      have hd : DifferentiableAt ℝ (A.Φ j) z :=
        (hdC.hasDerivAt.complexToReal_fderiv).differentiableAt
      exact hd.hasFDerivAt.hasFDerivWithinAt
    have hinj : Set.InjOn (A.Φ j) X := (A.hinj j hj).mono hXball
    have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hXm hfd
      hinj (fun _ => (1 : ℝ≥0∞))
    have himgB : A.Φ j '' X ⊆ B := by
      rintro w ⟨z, hz, rfl⟩
      have h1 : A.mchart j z ∈ B := hz.2
      rwa [A.mchart_eq hj (hXball hz)] at h1
    have hdet : ∀ z ∈ X, ENNReal.ofReal |(fderiv ℝ (A.Φ j) z).det| = ‖q z‖ₑ := by
      intro z hz
      have hzball := hXball hz
      have hdC : DifferentiableAt ℂ (A.Φ j) z :=
        (A.hd j hj).differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
      have hdet1 : (fderiv ℝ (A.Φ j) z).det = ‖deriv (A.Φ j) z‖ ^ 2 := by
        rw [det_fderiv_eq_wirtinger, dzbar_eq_zero_of_differentiableAt hdC,
          dz_eq_deriv_of_differentiableAt hdC, norm_zero]
        ring
      have hdet2 : ‖deriv (A.Φ j) z‖ ^ 2 = ‖q z‖ := by
        rw [← norm_pow, A.hsq j hj z hzball, norm_neg]
      rw [hdet1, hdet2, abs_of_nonneg (norm_nonneg _), ofReal_norm_eq_enorm]
    have hzero : ∫⁻ z in X, ‖q z‖ₑ = 0 := by
      have h1 : ∫⁻ z in X, ENNReal.ofReal |(fderiv ℝ (A.Φ j) z).det| = 0 := by
        have h2 : ∫⁻ z in X, ENNReal.ofReal |(fderiv ℝ (A.Φ j) z).det|
            = ∫⁻ z in X, ENNReal.ofReal |(fderiv ℝ (A.Φ j) z).det| * 1 := by
          refine lintegral_congr fun z => (mul_one _).symm
        rw [h2, ← hcov]
        refine le_antisymm ?_ (zero_le _)
        refine le_trans (lintegral_mono_set himgB) ?_
        exact le_of_eq (setLIntegral_measure_zero _ _ hB0)
      rw [← h1]
      exact setLIntegral_congr_fun hXm fun z hz => (hdet z hz).symm
    have hae := (lintegral_eq_zero_iff hqm.enorm).mp hzero
    have hfalse : ∀ᵐ z ∂(volume.restrict X), False := by
      filter_upwards [hae, ae_restrict_mem hXm] with z h0 hzX
      exact A.hne j hj z (hXball hzX) (enorm_eq_zero.mp h0)
    have huniv : (volume.restrict X) Set.univ = 0 := by
      have h5 := ae_iff.mp hfalse
      simpa using h5
    rwa [Measure.restrict_apply_univ] at huniv

/-- Absolute continuity is preserved by time reflection. -/
theorem acOn_reflect {X : Type*} [PseudoMetricSpace X] {η : ℝ → X} {c d : ℝ}
    (hη : AbsolutelyContinuousOnInterval η c d) :
    AbsolutelyContinuousOnInterval (fun t => η (-t)) (-d) (-c) := by
  rw [absolutelyContinuousOnInterval_iff] at hη ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hη ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  set F : ℕ → ℝ × ℝ := fun i => (-(E.2 i).1, -(E.2 i).2) with hF
  have hdistF : ∀ i, dist (F i).1 (F i).2 = dist (E.2 i).1 (E.2 i).2 := by
    intro i
    simp only [hF, Real.dist_eq]
    rw [show -(E.2 i).1 - -(E.2 i).2 = -((E.2 i).1 - (E.2 i).2) from by ring,
      abs_neg]
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Finset.mem_range,
    Set.mem_setOf_eq] at hE
  obtain ⟨hEicc, hEdisj⟩ := hE
  have hmemF : (E.1, F) ∈ AbsolutelyContinuousOnInterval.disjWithin c d := by
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 := hEicc i (Finset.mem_range.mp hi)
      constructor
      · simp only [hF]
        rcases Set.mem_uIcc.mp h1.1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
        · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
      · simp only [hF]
        rcases Set.mem_uIcc.mp h1.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
        · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    · intro i hi j hj hij
      have hd := hEdisj hi hj hij
      rw [Function.onFun, Set.disjoint_left] at hd ⊢
      intro z hzi hzj
      simp only [hF, Set.mem_uIoc] at hzi hzj
      have hzi' : (E.2 i).1 ⊓ (E.2 i).2 ≤ -z ∧ -z < (E.2 i).1 ⊔ (E.2 i).2 := by
        rcases hzi with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans inf_le_right (by linarith),
            lt_of_lt_of_le (by linarith) le_sup_left⟩
        · exact ⟨le_trans inf_le_left (by linarith),
            lt_of_lt_of_le (by linarith) le_sup_right⟩
      have hzj' : (E.2 j).1 ⊓ (E.2 j).2 ≤ -z ∧ -z < (E.2 j).1 ⊔ (E.2 j).2 := by
        rcases hzj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans inf_le_right (by linarith),
            lt_of_lt_of_le (by linarith) le_sup_left⟩
        · exact ⟨le_trans inf_le_left (by linarith),
            lt_of_lt_of_le (by linarith) le_sup_right⟩
      obtain ⟨w, hw1, hw2⟩ := exists_between (lt_min hzi'.2 hzj'.2)
      have hwi : w ∈ Set.uIoc (E.2 i).1 (E.2 i).2 := by
        rw [Set.uIoc, Set.mem_Ioc]
        exact ⟨lt_of_le_of_lt hzi'.1 hw1, le_of_lt (lt_of_lt_of_le hw2 (min_le_left _ _))⟩
      have hwj : w ∈ Set.uIoc (E.2 j).1 (E.2 j).2 := by
        rw [Set.uIoc, Set.mem_Ioc]
        exact ⟨lt_of_le_of_lt hzj'.1 hw1, le_of_lt (lt_of_lt_of_le hw2 (min_le_right _ _))⟩
      exact hd hwi hwj
  have hlenF : ∑ i ∈ Finset.range (E.1, F).1, dist (F i).1 (F i).2 < δ := by
    simp only
    calc ∑ i ∈ Finset.range E.1, dist (F i).1 (F i).2
        = ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 :=
          Finset.sum_congr rfl fun i _ => hdistF i
      _ < δ := by simpa using hlen
  simpa [hF] using hδ' (E.1, F) hmemF hlenF

/-- **Rational-time detection of a chart height**: a leaf point in a natural-chart
domain is accompanied by a rational-time leaf point in the same domain at the same
developed height. -/
theorem leaf_height_hit_rational {q : ℂ → ℂ} {σ : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) {v : ℝ} (hv : v ∈ Set.Icc 0 T)
    {S : Set ℂ} (hS : IsOpen S) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    (hin : σ v ∈ S) :
    ∃ r : ℚ, (r : ℝ) ∈ Set.Icc 0 T ∧ σ (r : ℝ) ∈ S
      ∧ (Φ (σ (r : ℝ))).im = (Φ (σ v)).im := by
  obtain ⟨ε, hεpm, hev⟩ := traj_ambient_local hS hΦd hΦsq hσ Set.Subset.rfl hv hin
  have hmemS : ∀ᶠ u in nhdsWithin v (Set.Icc 0 T), σ u ∈ S :=
    (hσ.cont v hv) (hS.mem_nhds hin)
  have hcomb := hmemS.and hev
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hcomb
  obtain ⟨u₁, u₂, hu12, hsub⟩ : ∃ u₁ u₂ : ℝ, u₁ < u₂ ∧
      Set.Ioo u₁ u₂ ⊆ Metric.ball v δ ∩ Set.Icc 0 T := by
    rcases lt_or_ge v T with hvT | hvT
    · refine ⟨v, min T (v + δ), lt_min hvT (by linarith), fun u hu => ?_⟩
      have h1 : u < v + δ := lt_of_lt_of_le hu.2 (min_le_right _ _)
      have h2 : u < T := lt_of_lt_of_le hu.2 (min_le_left _ _)
      refine ⟨?_, ⟨by linarith [hv.1, hu.1], h2.le⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1]
    · have hvT' : v = T := le_antisymm hv.2 hvT
      refine ⟨max 0 (T - δ), T, ?_, fun u hu => ?_⟩
      · rcases le_or_gt 0 (T - δ) with h1 | h1
        · rw [max_eq_right h1]
          linarith
        · rw [max_eq_left h1.le]
          exact hT
      · have h1 : T - δ < u := lt_of_le_of_lt (le_max_right _ _) hu.1
        have h0 : 0 < u := lt_of_le_of_lt (le_max_left _ _) hu.1
        refine ⟨?_, ⟨h0.le, hu.2.le⟩⟩
        rw [Metric.mem_ball, Real.dist_eq, hvT', abs_lt]
        constructor <;> linarith [hu.2]
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hu12
  have hrmem : (r : ℝ) ∈ Metric.ball v δ ∩ Set.Icc 0 T := hsub ⟨hr1, hr2⟩
  have hrprop := hδsub ⟨hrmem.1, hrmem.2⟩
  refine ⟨r, hrmem.2, hrprop.1, ?_⟩
  rw [hrprop.2]
  have him : ((ε : ℂ) * (((r : ℝ) - v : ℝ) : ℂ)).im = 0 := by
    have hcast : (ε : ℂ) * (((r : ℝ) - v : ℝ) : ℂ)
        = (((ε * ((r : ℝ) - v)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_im]
  rw [Complex.add_im, him, add_zero]

/-- **Window absolute continuity**: near any leaf time, absolute continuity of the
image of the developed height line yields absolute continuity of the image leaf. -/
theorem leaf_window_ac {q h : ℂ → ℂ} {σ : ℝ → ℂ} {T : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 T)) {v : ℝ} (hv : v ∈ Set.Icc 0 T)
    {S : Set ℂ} (hS : IsOpen S) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w) (hin : σ v ∈ S)
    (hACy : ∀ a b : ℝ,
      (∀ x ∈ Set.uIcc a b,
        (x : ℂ) + ((Φ (σ v)).im : ℝ) * Complex.I ∈ Φ '' S) →
      AbsolutelyContinuousOnInterval
        (fun x => h (Function.invFunOn Φ S
          ((x : ℂ) + ((Φ (σ v)).im : ℝ) * Complex.I))) a b) :
    ∃ δ > 0, AbsolutelyContinuousOnInterval (fun u => h (σ u))
      (max 0 (v - δ)) (min T (v + δ)) := by
  obtain ⟨ε, hεpm, hev⟩ := traj_ambient_local hS hΦd hΦsq hσ Set.Subset.rfl hv hin
  have hmemS : ∀ᶠ u in nhdsWithin v (Set.Icc 0 T), σ u ∈ S :=
    (hσ.cont v hv) (hS.mem_nhds hin)
  obtain ⟨δ₀, hδ₀, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp (hmemS.and hev)
  refine ⟨δ₀ / 2, by positivity, ?_⟩
  set w₁ : ℝ := max 0 (v - δ₀ / 2) with hw₁def
  set w₂ : ℝ := min T (v + δ₀ / 2) with hw₂def
  have hw₁v : w₁ ≤ v := max_le hv.1 (by linarith)
  have hvw₂ : v ≤ w₂ := le_min hv.2 (by linarith)
  have hw12 : w₁ ≤ w₂ := le_trans hw₁v hvw₂
  have hJprop : ∀ u ∈ Set.uIcc w₁ w₂, σ u ∈ S
      ∧ Φ (σ u) = Φ (σ v) + (ε : ℂ) * ((u - v : ℝ) : ℂ) := by
    intro u hu
    rw [Set.uIcc_of_le hw12] at hu
    refine hδsub ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have := le_trans (le_max_right 0 (v - δ₀ / 2)) hu.1
        linarith
      · have := le_trans hu.2 (min_le_right T (v + δ₀ / 2))
        linarith
    · exact ⟨le_trans (le_max_left 0 _) hu.1,
        le_trans hu.2 (min_le_left T _)⟩
  set xv : ℝ := (Φ (σ v)).re with hxvdef
  set yv : ℝ := (Φ (σ v)).im with hyvdef
  set g : ℝ → ℂ := fun x => h (Function.invFunOn Φ S
    ((x : ℂ) + (yv : ℝ) * Complex.I)) with hgdef
  have hline : ∀ u ∈ Set.uIcc w₁ w₂,
      ((xv + ε * (u - v) : ℝ) : ℂ) + (yv : ℝ) * Complex.I = Φ (σ u) := by
    intro u hu
    rw [(hJprop u hu).2]
    have hre := Complex.re_add_im (Φ (σ v))
    push_cast
    linear_combination hre
  have hval : ∀ u ∈ Set.uIcc w₁ w₂, g (xv + ε * (u - v)) = h (σ u) := by
    intro u hu
    have huS := (hJprop u hu).1
    have hex : ∃ x ∈ S, Φ x = Φ (σ u) := ⟨σ u, huS, rfl⟩
    have hinv : Function.invFunOn Φ S (Φ (σ u)) = σ u :=
      hΦinj (Function.invFunOn_mem hex) huS (Function.invFunOn_eq hex)
    change h (Function.invFunOn Φ S _) = h (σ u)
    rw [hline u hu, hinv]
  rcases hεpm with hε1 | hε1
  · have hmaps : ∀ t ∈ Set.uIcc w₁ w₂,
        (1 : ℝ) * t + (xv - v) ∈ Set.uIcc (w₁ + (xv - v)) (w₂ + (xv - v)) := by
      intro t ht
      rw [Set.uIcc_of_le hw12] at ht
      rw [Set.uIcc_of_le (by linarith : w₁ + (xv - v) ≤ w₂ + (xv - v))]
      constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have hcond : ∀ x ∈ Set.uIcc (w₁ + (xv - v)) (w₂ + (xv - v)),
        (x : ℂ) + (yv : ℝ) * Complex.I ∈ Φ '' S := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : w₁ + (xv - v) ≤ w₂ + (xv - v))] at hx
      have hu : x - (xv - v) ∈ Set.uIcc w₁ w₂ := by
        rw [Set.uIcc_of_le hw12]
        constructor <;> [linarith [hx.1]; linarith [hx.2]]
      have h1 := hline (x - (xv - v)) hu
      rw [hε1] at h1
      have h2 : xv + 1 * (x - (xv - v) - v) = x := by ring
      rw [h2] at h1
      rw [h1]
      exact ⟨σ (x - (xv - v)), (hJprop _ hu).1, rfl⟩
    have hAC := AbsolutelyContinuousOnInterval.comp_affine one_pos
      (hACy _ _ hcond) hmaps
    refine AbsolutelyContinuousOnInterval.congr hAC fun t ht => ?_
    have h1 := hval t ht
    rw [hε1] at h1
    change g (1 * t + (xv - v)) = h (σ t)
    have h2 : 1 * t + (xv - v) = xv + 1 * (t - v) := by ring
    rw [h2]
    exact h1
  · have hcd : xv - (w₂ - v) ≤ xv - (w₁ - v) := by linarith
    have hcond : ∀ x ∈ Set.uIcc (xv - (w₂ - v)) (xv - (w₁ - v)),
        (x : ℂ) + (yv : ℝ) * Complex.I ∈ Φ '' S := by
      intro x hx
      rw [Set.uIcc_of_le hcd] at hx
      have hu : xv + v - x ∈ Set.uIcc w₁ w₂ := by
        rw [Set.uIcc_of_le hw12]
        constructor <;> [linarith [hx.2]; linarith [hx.1]]
      have h1 := hline (xv + v - x) hu
      rw [hε1] at h1
      have h2 : xv + -1 * (xv + v - x - v) = x := by ring
      rw [h2] at h1
      rw [h1]
      exact ⟨σ (xv + v - x), (hJprop _ hu).1, rfl⟩
    have hrefl := acOn_reflect (hACy _ _ hcond)
    have hmaps : ∀ t ∈ Set.uIcc w₁ w₂,
        (1 : ℝ) * t + (-(xv + v))
          ∈ Set.uIcc (-(xv - (w₁ - v))) (-(xv - (w₂ - v))) := by
      intro t ht
      rw [Set.uIcc_of_le hw12] at ht
      rw [Set.uIcc_of_le (by linarith : -(xv - (w₁ - v)) ≤ -(xv - (w₂ - v)))]
      constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have hAC := AbsolutelyContinuousOnInterval.comp_affine one_pos hrefl hmaps
    refine AbsolutelyContinuousOnInterval.congr hAC fun t ht => ?_
    have h1 := hval t ht
    rw [hε1] at h1
    change g (-(1 * t + -(xv + v))) = h (σ t)
    have h2 : -(1 * t + -(xv + v)) = xv + -1 * (t - v) := by ring
    rw [h2]
    exact h1

/-- Absolute continuity on a degenerate interval. -/
theorem acOn_self {X : Type*} [PseudoMetricSpace X] (f : ℝ → X) (a : ℝ) :
    AbsolutelyContinuousOnInterval f a a := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨1, one_pos, fun E hE _ => ?_⟩
  obtain ⟨hEicc, -⟩ := hE
  have hzero : ∀ i ∈ Finset.range E.1,
      dist (f (E.2 i).1) (f (E.2 i).2) = 0 := by
    intro i hi
    have h1 := (hEicc i hi).1
    have h2 := (hEicc i hi).2
    rw [Set.uIcc_self, Set.mem_singleton_iff] at h1 h2
    rw [h1, h2, dist_self]
  rw [Finset.sum_congr rfl hzero]
  simpa using hε

/-- **Local-to-global absolute continuity**: window absolute continuity around every
time of a compact horizon glues to absolute continuity on the horizon. -/
theorem ac_of_local_windows {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {T : ℝ}
    (hT : 0 < T)
    (hloc : ∀ v ∈ Set.Icc (0 : ℝ) T, ∃ δ > 0,
      AbsolutelyContinuousOnInterval f (max 0 (v - δ)) (min T (v + δ))) :
    AbsolutelyContinuousOnInterval f 0 T := by
  classical
  choose! δf hδf hACf using hloc
  have hcov : Set.Icc (0 : ℝ) T ⊆ ⋃ v : Set.Icc (0 : ℝ) T,
      Set.Ioo ((v : ℝ) - δf v) ((v : ℝ) + δf v) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    have hpos := hδf x hx
    exact ⟨by linarith, by linarith⟩
  obtain ⟨δL, hδL, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun v : Set.Icc (0 : ℝ) T => isOpen_Ioo) hcov
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δL)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmesh : T / ((n : ℝ) + 1) < δL := by
    rw [div_lt_iff₀ hnpos]
    have h1 : T / δL < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hδL] at h1
    linarith
  have hmesh0 : 0 < T / ((n : ℝ) + 1) := by positivity
  have hfull : ((n : ℝ) + 1) * (T / ((n : ℝ) + 1)) = T := by
    field_simp
  have hle : ∀ k : ℕ, k ≤ n + 1 → (k : ℝ) * (T / ((n : ℝ) + 1)) ≤ T := by
    intro k hk
    have h1 : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk
    calc (k : ℝ) * (T / ((n : ℝ) + 1))
        ≤ ((n : ℝ) + 1) * (T / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right h1 hmesh0.le
      _ = T := hfull
  have hstep : ∀ k : ℕ, k ≤ n + 1 →
      AbsolutelyContinuousOnInterval f 0 ((k : ℝ) * (T / ((n : ℝ) + 1))) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using acOn_self f 0
    | succ k ih =>
      intro hk1
      have hk : k ≤ n + 1 := by omega
      set m : ℝ := T / ((n : ℝ) + 1) with hmdef
      have htk0 : (0 : ℝ) ≤ (k : ℝ) * m := by positivity
      have hstep1 : (k : ℝ) * m ≤ ((k : ℕ) + 1 : ℕ) * m := by
        push_cast
        nlinarith [hmesh0]
      have htkIcc : (k : ℝ) * m ∈ Set.Icc (0 : ℝ) T := ⟨htk0, hle k hk⟩
      obtain ⟨v, hball⟩ := hleb ((k : ℝ) * m) htkIcc
      have hvwin : max 0 ((v : ℝ) - δf v) ≤ (k : ℝ) * m
          ∧ (k : ℝ) * m ≤ min T ((v : ℝ) + δf v) := by
        have h1 : (k : ℝ) * m ∈ Set.Ioo ((v : ℝ) - δf v) ((v : ℝ) + δf v) :=
          hball (Metric.mem_ball_self hδL)
        exact ⟨max_le htk0 h1.1.le, le_min (hle k hk) h1.2.le⟩
      have hsub : Set.uIcc ((k : ℝ) * m) (((k : ℕ) + 1 : ℕ) * m)
          ⊆ Set.uIcc (max 0 ((v : ℝ) - δf v)) (min T ((v : ℝ) + δf v)) := by
        intro u hu
        rw [Set.uIcc_of_le hstep1] at hu
        have hu1 : (k : ℝ) * m ≤ u := hu.1
        have hu2 : u ≤ (k : ℝ) * m + m := by
          have := hu.2
          push_cast at this
          nlinarith [this]
        have huIoo : u ∈ Set.Ioo ((v : ℝ) - δf v) ((v : ℝ) + δf v) := by
          refine hball ?_
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> [linarith [hmesh]; linarith [hmesh]]
        have huT : u ≤ T := by
          have := hle (k + 1) hk1
          push_cast at this
          nlinarith [this]
        rw [Set.uIcc_of_le (le_trans hvwin.1 hvwin.2)]
        exact ⟨max_le (by linarith) huIoo.1.le, le_min huT huIoo.2.le⟩
      have hACwin := AbsolutelyContinuousOnInterval.mono (hACf v v.2) hsub
      have hglue := AbsolutelyContinuousOnInterval.union_of_split htk0 hstep1
        (ih hk) hACwin
      have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) * m = ((k + 1 : ℕ) : ℝ) * m := by
        push_cast
        ring
      rwa [hcast] at hglue
  have hfin := hstep (n + 1) le_rfl
  have hcast : (((n : ℕ) + 1 : ℕ) : ℝ) * (T / ((n : ℝ) + 1)) = T := by
    push_cast
    exact hfull
  rwa [hcast] at hfin

end RiemannDynamics
