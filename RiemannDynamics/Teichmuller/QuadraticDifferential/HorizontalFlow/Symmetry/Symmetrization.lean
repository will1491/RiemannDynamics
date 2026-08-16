/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Flow.GoodSet

/-!
# The symmetrized flow and its invariance engine

The symmetrized labels, the total flow on the tiling, and the engine producing the
invariance identities of the weight functionals under the symmetrized flow.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Label decomposition**: the weighted `|q|` integral of a flow section over the
fundamental tile is the sum, over itinerary pieces and cosets, of the retiled arrival
integrals. -/
theorem label_decomp {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (A B : Atlas (q : ℂ → ℂ)) (f : ℂ → ℂ) {t : ℝ} (ht : 0 < t)
    (hflow : ∀ N : ℕ, ∀ z ∈ slegal B (t / (N + 1)) N,
      f z = pos B (t / (N + 1)) (N + 1) z)
    (hcov : ∀ z ∈ good (q : ℂ → ℂ) A, ∃ N : ℕ, z ∈ slegal B (t / (N + 1)) N)
    {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    (hGinv : ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      G (moebiusMap ↑γ z) = G z) :
    ∫⁻ z in symOmega Γ, G (f z) * ‖q z‖ₑ
      = ∑' i : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
          × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I),
          ∫⁻ w in symRet Γ B t i, G w * ‖q w‖ₑ := by
  classical
  have : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  have : Countable (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) :=
    QuotientGroup.mk_surjective.countable
  obtain ⟨hBadm, hBadnull⟩ := symBad_facts hΓ hdense
  have hωm : MeasurableSet (symOmega Γ) :=
    (isCompact_domain hΓ hfree hcc).measurableSet
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hgrid : ∀ N : ℕ, (0 : ℝ) < t / (N + 1) := fun N => by positivity
  have hseedm : ∀ N, MeasurableSet (symSeed Γ B t N) := fun N =>
    (hωm.diff hBadm).inter ((slegal_measurable B (hgrid N) N).diff
      (MeasurableSet.iUnion fun M =>
        MeasurableSet.iUnion fun _ => slegal_measurable B (hgrid M) M))
  have hseedsub : ∀ N, symSeed Γ B t N ⊆ slegal B (t / (N + 1)) N :=
    fun N z hz => hz.2.1
  have hseedω : ∀ N, symSeed Γ B t N ⊆ symOmega Γ := fun N z hz => hz.1.1
  have hgood := good_ae hΓ hcc q hq0 A
  have hnullgood : volume ({z : ℂ | ¬ z ∈ good (q : ℂ → ℂ) A}
      ∩ {z : ℂ | 0 < z.im}) = 0 := by
    have h0 := ae_iff.mp hgood
    rwa [Measure.restrict_apply' hUm] at h0
  have hcovseed : symOmega Γ \ ⋃ N, symSeed Γ B t N ⊆
      symBad Γ ∪ ({z : ℂ | ¬ z ∈ good (q : ℂ → ℂ) A} ∩ {z : ℂ | 0 < z.im}) := by
    rintro z ⟨hzω, hzU⟩
    by_cases hb : z ∈ symBad Γ
    · exact Or.inl hb
    by_cases hg : z ∈ good (q : ℂ → ℂ) A
    · exfalso
      apply hzU
      obtain ⟨N₀, hN₀⟩ := hcov z hg
      have hex : ∃ N : ℕ, z ∈ slegal B (t / (N + 1)) N := ⟨N₀, hN₀⟩
      refine Set.mem_iUnion.mpr ⟨Nat.find hex, ⟨hzω, hb⟩, Nat.find_spec hex, ?_⟩
      intro hc
      obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hc
      obtain ⟨hMlt, hMs⟩ := Set.mem_iUnion.mp hM
      exact Nat.find_min hex hMlt hMs
    · exact Or.inr ⟨hg, symOmega_upper hzω⟩
  have hA : ∫⁻ z in symOmega Γ, G (f z) * ‖q z‖ₑ
      = ∫⁻ z in ⋃ N, symSeed Γ B t N, G (f z) * ‖q z‖ₑ := by
    refine setLIntegral_congr (MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null hcovseed
        (measure_union_null hBadnull hnullgood)
    · refine measure_mono_null (fun w hw => (hw.2 ?_).elim)
        (measure_empty (μ := volume))
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hw.1
      exact hseedω N hN
  set P : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool) → Set ℂ :=
    fun j => symPiece Γ B t j.1 j.2 with hPdef
  have hPm : ∀ j, MeasurableSet (P j) := fun j =>
    piece_measurable B _ _ (hseedm j.1) j.2
  have hEL : ∀ N, symSeed Γ B t N ⊆ legal B (t / (N + 1)) N := fun N =>
    (hseedsub N).trans (slegal_legal B (hgrid N).le N)
  have hseedd : Pairwise (Function.onFun Disjoint fun N => symSeed Γ B t N) := by
    intro N N' hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hz'.2.2 (Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨hlt, hz.2.1⟩⟩)
    · exact hz.2.2 (Set.mem_iUnion.mpr ⟨N', Set.mem_iUnion.mpr ⟨hlt, hz'.2.1⟩⟩)
  have hcovP : ⋃ N, symSeed Γ B t N = ⋃ j, P j := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hz⟩
      refine ⟨⟨N, itin B (t / (N + 1)) N z⟩, hz, fun k => ⟨rfl, ?_⟩⟩
      have hpm := ((hEL N hz) (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)).2.2.1
      change sgn B (t / (N + 1)) (k : ℕ) z
        = (if (if sgn B (t / (N + 1)) (k : ℕ) z = 1 then true else false)
          then (1 : ℝ) else -1)
      rcases hpm with h1 | h1
      · rw [if_pos h1]
        simp [h1]
      · rw [if_neg (by rw [h1]; norm_num)]
        simp [h1]
    · rintro ⟨j, hz⟩
      exact ⟨j.1, hz.1⟩
  have hdisjP : Pairwise (Function.onFun Disjoint P) := by
    rintro ⟨N, c⟩ ⟨N', c'⟩ hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    by_cases hN : N = N'
    · subst hN
      have h1 := itin_eq B (hEL N) hzi
      have h2 := itin_eq B (hEL N) hzj
      exact hij (by rw [Sigma.mk.injEq]; exact ⟨rfl, heq_of_eq (h1.trans h2.symm)⟩)
    · exact Set.disjoint_left.mp (hseedd hN) hzi.1 hzj.1
  have hB : ∫⁻ z in ⋃ N, symSeed Γ B t N, G (f z) * ‖q z‖ₑ
      = ∑' j, ∫⁻ z in P j, G (f z) * ‖q z‖ₑ := by
    conv_lhs => rw [hcovP]
    exact lintegral_iUnion hPm hdisjP _
  have hC : ∀ j, ∫⁻ z in P j, G (f z) * ‖q z‖ₑ
      = ∑' cq, ∫⁻ w in symRet Γ B t (j, cq), G w * ‖q w‖ₑ := by
    intro j
    have hPs : P j ⊆ slegal B (t / (j.1 + 1)) j.1 := fun z hz => hseedsub j.1 hz.1
    have hPc : ∀ z ∈ P j, ∀ k : Fin (j.1 + 1),
        B.sel (pos B (t / (j.1 + 1)) (k : ℕ) z) = (j.2 k).1 ∧
        sgn B (t / (j.1 + 1)) (k : ℕ) z
          = (if (j.2 k).2 then (1 : ℝ) else -1) := fun z hz k => hz.2 k
    have step1 : ∫⁻ z in P j, G (f z) * ‖q z‖ₑ
        = ∫⁻ z in P j, G (pos B (t / (j.1 + 1)) (j.1 + 1) z) * ‖q z‖ₑ :=
      setLIntegral_congr_fun (hPm j)
        (fun z hz => by rw [hflow j.1 z (hPs hz)])
    obtain ⟨harrm, htrans⟩ := piece_cov q.measurable B (hgrid j.1)
      (hPm j) hPs j.2 hPc hG
    have harrU : ∀ w ∈ symArr Γ B t j, 0 < w.im := by
      rintro w ⟨z, hz, rfl⟩
      exact (pos_regular B (hgrid j.1) (hPs hz)).1
    rw [step1, ← htrans]
    exact symArr_retile hΓ hfree hdense q B j harrm harrU hGinv
  rw [hA, hB, ENNReal.tsum_prod']
  exact tsum_congr hC

/-- A strong-legal seed is a regular point. -/
theorem slegal_regular0 {q : ℂ → ℂ} (B : Atlas q) {h : ℝ} {N : ℕ} {z : ℂ}
    (hz : z ∈ slegal B h N) : 0 < z.im ∧ q z ≠ 0 := by
  obtain ⟨hact, hball, -, -⟩ := hz 0 (Nat.zero_le N)
  refine ⟨?_, ?_⟩
  · exact B.hH _ hact
      (Metric.ball_subset_ball (by linarith [B.hr _ hact]) hball)
  · exact B.hne _ hact _
      (Metric.ball_subset_ball (by linarith [B.hr _ hact]) hball)

/-- Time reversal of a trajectory on a compact window. -/
theorem traj_reverse_at {q : ℂ → ℂ} {σ : ℝ → ℂ} {a : ℝ}
    (hσ : IsTrajOn q σ (Set.Icc 0 a)) :
    IsTrajOn q (fun u => σ (a - u)) (Set.Icc 0 a) := by
  have h1 := traj_reverse (traj_shift a hσ)
  have hset : (fun u : ℝ => -u) ⁻¹' ((fun u : ℝ => u + a) ⁻¹' Set.Icc 0 a)
      = Set.Icc 0 a := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hh1, hh2⟩
      constructor <;> linarith
    · rintro ⟨hh1, hh2⟩
      constructor <;> linarith
  rw [hset] at h1
  have hfun : (fun u : ℝ => (fun v : ℝ => σ (v + a)) (-u)) = fun u => σ (a - u) := by
    funext u
    change σ (-u + a) = σ (a - u)
    rw [neg_add_eq_sub]
  rwa [hfun] at h1

/-- Time reversal negates the arrival chart slope. -/
theorem slope_reverse {Φ : ℂ → ℂ} {σ : ℝ → ℂ} {t ε : ℝ}
    (hev : SlopeAt Φ σ (Set.Icc 0 t) t ε) :
    SlopeAt Φ (fun u => σ (t - u)) (Set.Icc 0 t) 0 (-ε) := by
  have hmap : Filter.Tendsto (fun u : ℝ => t - u)
      (nhdsWithin 0 (Set.Icc 0 t)) (nhdsWithin t (Set.Icc 0 t)) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h := (continuous_sub_left t).tendsto (0 : ℝ)
      simpa using h
    · exact Filter.tendsto_principal_principal.mpr fun u hu =>
        ⟨by linarith [hu.2], by linarith [hu.1]⟩
  change ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 t),
    Φ (σ (t - v)) = Φ (σ (t - 0)) + ((-ε : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
  filter_upwards [hmap.eventually hev] with v hv
  rw [sub_zero]
  push_cast at hv ⊢
  linear_combination hv

/-- Chart slopes transfer along pointwise equal curves. -/
theorem slope_congr {Φ : ℂ → ℂ} {σ σ' : ℝ → ℂ} {I : Set ℝ} {u s : ℝ}
    (hEq : Set.EqOn σ σ' I) (hu : u ∈ I) (h : SlopeAt Φ σ I u s) :
    SlopeAt Φ σ' I u s := by
  change ∀ᶠ v in nhdsWithin u I, Φ (σ' v) = Φ (σ' u) + s * ((v - u : ℝ) : ℂ)
  filter_upwards [h, eventually_mem_nhdsWithin] with v hv hvI
  rw [← hEq hvI, ← hEq hu]
  exact hv

/-- The punctured left-endpoint neighborhood filter of a nondegenerate window. -/
theorem nebot_left {t : ℝ} (ht : 0 < t) :
    (nhdsWithin 0 (Set.Icc 0 t \ {0})).NeBot := by
  have h1 : (nhdsWithin (0 : ℝ) (Set.Ioc 0 t)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioc ht.ne]
    exact ⟨le_refl 0, ht.le⟩
  exact h1.mono (nhdsWithin_mono 0 fun u hu => ⟨⟨hu.1.le, hu.2⟩, hu.1.ne'⟩)

/-- **Retiled membership data**: a point of a retiled arrival set is the decked endpoint
of a strong-legal trajectory from a seed of the piece. -/
theorem symRet_data {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (B : Atlas (q : ℂ → ℂ)) {t : ℝ} (ht : 0 < t)
    {j : Σ N : ℕ, Fin (N + 1) → ℕ × Bool}
    {cq : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I} {y : ℂ}
    (hy : y ∈ symRet Γ B t (j, cq)) :
    ∃ (z : ℂ) (σ : ℝ → ℂ), z ∈ symPiece Γ B t j.1 j.2 ∧ σ 0 = z ∧
      IsTrajOn (q : ℂ → ℂ) σ (Set.Icc 0 t) ∧
      SlopeAt (B.Φ (B.sel z)) σ (Set.Icc 0 t) 0 1 ∧
      σ t = moebiusMap ↑(Quotient.out cq) y := by
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨z, hz, hzw⟩ := hw.1.1
  have hzs : z ∈ slegal B (t / (j.1 + 1)) j.1 := hz.1.2.1
  obtain ⟨σ, h0, htraj, hS0, hend⟩ := slegal_traj_t B ht hzs
  have hh : (0 : ℝ) < t / (j.1 + 1) := by positivity
  have hwim : 0 < w.im := by
    rw [← hzw]
    exact (pos_regular B hh hzs).1
  refine ⟨z, σ, hz, h0, htraj, hS0, ?_⟩
  rw [moebius_cancel' _ hwim]
  exact hend.trans hzw

/-- **Seed coset rigidity**: two trimmed-tile seeds decked to the same base point share
their coset and coincide. -/
theorem seed_coset_eq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    {z z' : ℂ}
    (hz : z ∈ symOmega Γ \ symBad Γ) (hz' : z' ∈ symOmega Γ \ symBad Γ)
    {cq cq' : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I}
    (hw : moebiusMap (↑(Quotient.out cq))⁻¹ z
      = moebiusMap (↑(Quotient.out cq'))⁻¹ z') :
    cq = cq' ∧ z = z' := by
  obtain ⟨ρz, hρz, hρzeq⟩ := notBad_interior hz.1 hz.2
  obtain ⟨ρz', hρz', hρz'eq⟩ := notBad_interior hz'.1 hz'.2
  have hw0 : (((Quotient.out cq)⁻¹ • ρz : UpperHalfPlane) : ℂ)
      = moebiusMap (↑(Quotient.out cq))⁻¹ z := by
    rw [coe_smul_moebius (Quotient.out cq)⁻¹ ρz, hρzeq]
    rfl
  have hw0' : (((Quotient.out cq')⁻¹ • ρz' : UpperHalfPlane) : ℂ)
      = moebiusMap (↑(Quotient.out cq'))⁻¹ z' := by
    rw [coe_smul_moebius (Quotient.out cq')⁻¹ ρz', hρz'eq]
    rfl
  have hww : ((Quotient.out cq)⁻¹ • ρz : UpperHalfPlane)
      = (Quotient.out cq')⁻¹ • ρz' :=
    UpperHalfPlane.coe_injective (by rw [hw0, hw0']; exact hw)
  have hρδ : ((Quotient.out cq') * (Quotient.out cq)⁻¹) • ρz = ρz' := by
    rw [mul_smul, hww, smul_inv_smul]
  have hcq : cq = cq' := by
    by_cases hfix : ((Quotient.out cq') * (Quotient.out cq)⁻¹) • UpperHalfPlane.I
        = UpperHalfPlane.I
    · have htriv := hfree _ ⟨UpperHalfPlane.I, hfix⟩
      have hK : (Quotient.out cq)⁻¹ * Quotient.out cq'
          ∈ MulAction.stabilizer ↥Γ UpperHalfPlane.I := by
        refine MulAction.mem_stabilizer_iff.mpr ?_
        have hconj : (Quotient.out cq)⁻¹ * Quotient.out cq'
            = (Quotient.out cq)⁻¹
              * ((Quotient.out cq' * (Quotient.out cq)⁻¹) * Quotient.out cq) := by
          group
        rw [hconj, mul_smul, mul_smul, htriv, inv_smul_smul]
      rw [← QuotientGroup.out_eq' cq, ← QuotientGroup.out_eq' cq']
      exact QuotientGroup.eq.mpr hK
    · exfalso
      have hd := disjoint_smul_interior_dirichletDomain hΓ hdense
        (γ := (Quotient.out cq') * (Quotient.out cq)⁻¹) hfix
      have hρz'' : ((Quotient.out cq') * (Quotient.out cq)⁻¹) • ρz
          ∈ interior (dirichletDomain Γ UpperHalfPlane.I) := by
        rw [hρδ]
        exact hρz'
      exact absurd ⟨ρz, hρz, rfl⟩ (Set.disjoint_left.mp hd hρz'')
  refine ⟨hcq, ?_⟩
  rw [hcq] at hw
  have him : 0 < (moebiusMap (↑(Quotient.out cq'))⁻¹ z').im := by
    refine moebiusMap_im_pos _ ?_
    have := symOmega_upper hz'.1
    exact this
  have h1 := congrArg (moebiusMap ↑(Quotient.out cq')) hw
  rwa [moebius_cancel' _ (symOmega_upper hz.1),
    moebius_cancel' _ (symOmega_upper hz'.1)] at h1

/-- The two-label atlas family: the base atlas and its mirror. -/
noncomputable def symLab {q : ℂ → ℂ} (A : Atlas q) : Bool → Atlas q := fun b =>
  bif b then A else mirrorAtlas A

/-- **Arrival disambiguation**: two retiled arrival data at one regular point with equal
arrival slopes share the label, the itinerary piece, and the coset. -/
theorem main_disamb {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    {q : ℂ → ℂ} (A : Atlas q) {t : ℝ} (ht : 0 < t)
    {y : ℂ} (hyim : 0 < y.im) (hyq : q y ≠ 0)
    {b b' : Bool} {j j' : Σ N : ℕ, Fin (N + 1) → ℕ × Bool}
    {cq cq' : ↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I}
    {z z' : ℂ} {τ τ' : ℝ → ℂ} {ε : ℝ}
    (hz : z ∈ symPiece Γ (symLab A b) t j.1 j.2)
    (hz' : z' ∈ symPiece Γ (symLab A b') t j'.1 j'.2)
    (hτ : IsTrajOn q τ (Set.Icc 0 t)) (hτ' : IsTrajOn q τ' (Set.Icc 0 t))
    (hτ0 : τ 0 = moebiusMap (↑(Quotient.out cq))⁻¹ z)
    (hτ'0 : τ' 0 = moebiusMap (↑(Quotient.out cq'))⁻¹ z')
    (hτt : τ t = y) (hτ't : τ' t = y)
    (harr : SlopeAt (A.Φ (A.sel y)) τ (Set.Icc 0 t) t ε)
    (harr' : SlopeAt (A.Φ (A.sel y)) τ' (Set.Icc 0 t) t ε)
    (hund : SlopeAt (A.Φ (A.sel z))
      (fun u => moebiusMap ↑(Quotient.out cq) (τ u)) (Set.Icc 0 t) 0
      (cond b 1 (-1)))
    (hund' : SlopeAt (A.Φ (A.sel z'))
      (fun u => moebiusMap ↑(Quotient.out cq') (τ' u)) (Set.Icc 0 t) 0
      (cond b' 1 (-1))) :
    b = b' ∧ j = j' ∧ cq = cq' := by
  have hact : A.active (A.sel y) := (A.sel_spec hyim hyq).1
  have hrpos : 0 < A.r (A.sel y) := A.hr _ hact
  have hyS : y ∈ Metric.ball (A.c (A.sel y)) (2 * A.r (A.sel y)) :=
    Metric.ball_subset_ball (by linarith) (A.sel_spec hyim hyq).2
  have h0eq : τ 0 = τ' 0 :=
    arrival_unique Metric.isOpen_ball (A.hinj _ hact) ht.le hτ hτ'
      (hτt.trans hτ't.symm) (by rw [hτt]; exact hyS) harr harr'
  have hEqρ : Set.EqOn (fun u => τ (t - u)) (fun u => τ' (t - u))
      (Set.Icc 0 t) := by
    refine seed_unique Metric.isOpen_ball (A.hinj _ hact) ht.le
      (traj_reverse_at hτ) (traj_reverse_at hτ') ?_ ?_
      (slope_reverse harr) (slope_reverse harr')
    · show τ (t - 0) = τ' (t - 0)
      rw [sub_zero, hτt, hτ't]
    · show τ (t - 0) ∈ Metric.ball (A.c (A.sel y)) (2 * A.r (A.sel y))
      rw [sub_zero, hτt]
      exact hyS
  have hEqτ : Set.EqOn τ τ' (Set.Icc 0 t) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hmem : t - u ∈ Set.Icc 0 t := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h1 := hEqρ hmem
    simpa [sub_sub_cancel] using h1
  have hw : moebiusMap (↑(Quotient.out cq))⁻¹ z
      = moebiusMap (↑(Quotient.out cq'))⁻¹ z' := by
    rw [← hτ0, ← hτ'0, h0eq]
  obtain ⟨hcq, hzz⟩ := seed_coset_eq hΓ hfree hdense hz.1.1 hz'.1.1 hw
  subst hcq
  subst hzz
  have hbb : b = b' := by
    by_contra hbne
    have hEqc : Set.EqOn (fun u => moebiusMap ↑(Quotient.out cq) (τ u))
        (fun u => moebiusMap ↑(Quotient.out cq) (τ' u)) (Set.Icc 0 t) :=
      fun u hu => congrArg (moebiusMap ↑(Quotient.out cq)) (hEqτ hu)
    have hslope2 := slope_congr hEqc (Set.left_mem_Icc.mpr ht.le) hund
    have := nebot_left ht
    have hcond := slope_eq hslope2 hund'
    cases b <;> cases b'
    · exact hbne rfl
    · simp only [Bool.cond_false, Bool.cond_true] at hcond
      norm_num at hcond
    · simp only [Bool.cond_false, Bool.cond_true] at hcond
      norm_num at hcond
    · exact hbne rfl
  subst hbb
  refine ⟨rfl, ?_, rfl⟩
  have hN : j.1 = j'.1 := by
    by_contra hNe
    have hs1 : z ∈ symSeed Γ (symLab A b) t j.1 := hz.1
    have hs2 : z ∈ symSeed Γ (symLab A b) t j'.1 := hz'.1
    rcases lt_or_gt_of_ne hNe with hlt | hlt
    · exact hs2.2.2 (Set.mem_iUnion.mpr ⟨j.1, Set.mem_iUnion.mpr ⟨hlt, hs1.2.1⟩⟩)
    · exact hs1.2.2 (Set.mem_iUnion.mpr ⟨j'.1, Set.mem_iUnion.mpr ⟨hlt, hs2.2.1⟩⟩)
  obtain ⟨N, c⟩ := j
  obtain ⟨N', c'⟩ := j'
  have hN' : N = N' := hN
  subst hN'
  have hgrid : (0 : ℝ) < t / (N + 1) := by positivity
  have hEL : symSeed Γ (symLab A b) t N
      ⊆ legal (symLab A b) (t / (N + 1)) N :=
    fun w hw' => slegal_legal _ hgrid.le N hw'.2.1
  have h1 := itin_eq (symLab A b) hEL hz
  have h2 := itin_eq (symLab A b) hEL hz'
  exact congrArg (Sigma.mk N) (h1.trans h2.symm)

/-- **Two-point arrival multiplicity**: at a regular point, all retiled arrival sets
through both labels, all grids, and all cosets pass through at most two indices. -/
theorem mult_pair {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (q : QuadraticDifferential Γ) (A : Atlas (q : ℂ → ℂ)) {t : ℝ} (ht : 0 < t)
    {y : ℂ} (hyim : 0 < y.im) (hyq : (q : ℂ → ℂ) y ≠ 0) :
    ∃ i₁ i₂ : Bool × ((Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
        × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I)),
      ∀ i, y ∈ symRet Γ (symLab A i.1) t i.2 → i = i₁ ∨ i = i₂ := by
  classical
  have hact : A.active (A.sel y) := (A.sel_spec hyim hyq).1
  have hrpos : 0 < A.r (A.sel y) := A.hr _ hact
  have hyS : y ∈ Metric.ball (A.c (A.sel y)) (2 * A.r (A.sel y)) :=
    Metric.ball_subset_ball (by linarith) (A.sel_spec hyim hyq).2
  have hlab : ∀ (b : Bool) (z : ℂ), 0 < z.im → (q : ℂ → ℂ) z ≠ 0 →
      ∀ σ : ℝ → ℂ,
      SlopeAt ((symLab A b).Φ ((symLab A b).sel z)) σ (Set.Icc 0 t) 0 1 →
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 t) 0 (cond b 1 (-1)) := by
    intro b z hzim hzq σ hS
    have hactz : A.active (A.sel z) := (A.sel_spec hzim hzq).1
    cases b
    · have h1 : SlopeAt ((mirrorAtlas A).Φ (A.sel z)) σ (Set.Icc 0 t) 0 1 := hS
      rw [mirror_Φ A hactz] at h1
      change ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 t),
        A.Φ (A.sel z) (σ v)
          = A.Φ (A.sel z) (σ 0) + ((-1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
      filter_upwards [h1] with v hv
      have hv' : -(A.Φ (A.sel z) (σ v))
          = -(A.Φ (A.sel z) (σ 0)) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hv
      push_cast at hv' ⊢
      linear_combination -hv'
    · exact hS
  have hdat : ∀ i : Bool × ((Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
      × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I)),
      y ∈ symRet Γ (symLab A i.1) t i.2 →
      ∃ (z : ℂ) (τ : ℝ → ℂ) (ε : ℝ),
        z ∈ symPiece Γ (symLab A i.1) t i.2.1.1 i.2.1.2 ∧
        (ε = 1 ∨ ε = -1) ∧
        IsTrajOn (q : ℂ → ℂ) τ (Set.Icc 0 t) ∧
        τ 0 = moebiusMap (↑(Quotient.out i.2.2))⁻¹ z ∧
        τ t = y ∧
        SlopeAt (A.Φ (A.sel y)) τ (Set.Icc 0 t) t ε ∧
        SlopeAt (A.Φ (A.sel z))
          (fun u => moebiusMap ↑(Quotient.out i.2.2) (τ u)) (Set.Icc 0 t) 0
          (cond i.1 1 (-1)) := by
    rintro ⟨b, j, cq⟩ hy
    obtain ⟨z, σ, hzp, hσ0, hσtraj, hσS, hσend⟩ :=
      symRet_data q (symLab A b) ht hy
    have hzreg := slegal_regular0 (symLab A b) hzp.1.2.1
    have hauto : ∀ w : ℂ, 0 < w.im →
        (q : ℂ → ℂ) (moebiusMap (↑(Quotient.out cq))⁻¹ w)
          = moebiusDenom (↑(Quotient.out cq))⁻¹ w ^ 4 * (q : ℂ → ℂ) w :=
      fun w hw =>
        q.automorphy ↑((Quotient.out cq)⁻¹) ((Quotient.out cq)⁻¹).2 w hw
    set τ : ℝ → ℂ := fun u => moebiusMap (↑(Quotient.out cq))⁻¹ (σ u) with hτdef
    have hτtraj : IsTrajOn (q : ℂ → ℂ) τ (Set.Icc 0 t) :=
      traj_deck _ hauto hσtraj
    have hτt : τ t = y := by
      change moebiusMap (↑(Quotient.out cq))⁻¹ (σ t) = y
      rw [hσend]
      exact moebius_cancel _ hyim
    obtain ⟨ε, hεpm, hev⟩ := traj_ambient_local Metric.isOpen_ball (A.hd _ hact)
      (A.hsq _ hact) hτtraj Set.Subset.rfl (Set.right_mem_Icc.mpr ht.le)
      (by rw [hτt]; exact hyS)
    have hEqγ : Set.EqOn σ
        (fun u => moebiusMap ↑(Quotient.out cq) (τ u)) (Set.Icc 0 t) := by
      intro u hu
      have him : 0 < (σ u).im := (traj_regular hσtraj hu).1
      exact (moebius_cancel' _ him).symm
    refine ⟨z, τ, ε, hzp, hεpm, hτtraj, ?_, hτt, hev, ?_⟩
    · change moebiusMap (↑(Quotient.out cq))⁻¹ (σ 0) = _
      rw [hσ0]
    · exact slope_congr hEqγ (Set.left_mem_Icc.mpr ht.le)
        (hlab b z hzreg.1 hzreg.2 σ hσS)
  choose! zf τf εf hp1 hp2 hp3 hp4 hp5 hp6 hp7 using hdat
  have main : ∀ i, y ∈ symRet Γ (symLab A i.1) t i.2 →
      ∀ i', y ∈ symRet Γ (symLab A i'.1) t i'.2 → εf i = εf i' → i = i' := by
    rintro ⟨b, j, cq⟩ hm ⟨b', j', cq'⟩ hm' hεeq
    have harr' := hp6 (b', j', cq') hm'
    rw [← hεeq] at harr'
    obtain ⟨hb, hj, hcq⟩ := main_disamb hΓ hfree hdense A ht hyim hyq
      (hp1 (b, j, cq) hm) (hp1 (b', j', cq') hm')
      (hp3 (b, j, cq) hm) (hp3 (b', j', cq') hm')
      (hp4 (b, j, cq) hm) (hp4 (b', j', cq') hm')
      (hp5 (b, j, cq) hm) (hp5 (b', j', cq') hm')
      (hp6 (b, j, cq) hm) harr'
      (hp7 (b, j, cq) hm) (hp7 (b', j', cq') hm')
    simp only [Prod.mk.injEq]
    exact ⟨hb, hj, hcq⟩
  by_cases h1 : ∃ i, (y ∈ symRet Γ (symLab A i.1) t i.2) ∧ εf i = 1
  · by_cases h2 : ∃ i, (y ∈ symRet Γ (symLab A i.1) t i.2) ∧ εf i = -1
    · obtain ⟨i₁, hm₁, hε₁⟩ := h1
      obtain ⟨i₂, hm₂, hε₂⟩ := h2
      refine ⟨i₁, i₂, fun i hi => ?_⟩
      rcases hp2 i hi with hs | hs
      · exact Or.inl (main i hi i₁ hm₁ (by rw [hs, hε₁]))
      · exact Or.inr (main i hi i₂ hm₂ (by rw [hs, hε₂]))
    · obtain ⟨i₁, hm₁, hε₁⟩ := h1
      refine ⟨i₁, i₁, fun i hi => ?_⟩
      rcases hp2 i hi with hs | hs
      · exact Or.inl (main i hi i₁ hm₁ (by rw [hs, hε₁]))
      · exact absurd ⟨i, hi, hs⟩ h2
  · by_cases h2 : ∃ i, (y ∈ symRet Γ (symLab A i.1) t i.2) ∧ εf i = -1
    · obtain ⟨i₂, hm₂, hε₂⟩ := h2
      refine ⟨i₂, i₂, fun i hi => ?_⟩
      rcases hp2 i hi with hs | hs
      · exact absurd ⟨i, hi, hs⟩ h1
      · exact Or.inl (main i hi i₂ hm₂ (by rw [hs, hε₂]))
    · refine ⟨(true, ⟨⟨0, fun _ => (0, true)⟩, QuotientGroup.mk 1⟩),
        (true, ⟨⟨0, fun _ => (0, true)⟩, QuotientGroup.mk 1⟩), fun i hi => ?_⟩
      rcases hp2 i hi with hs | hs
      · exact absurd ⟨i, hi, hs⟩ h1
      · exact absurd ⟨i, hi, hs⟩ h2

/-- Retiled arrival sets are measurable and lie in the fundamental tile. -/
theorem symRet_meas {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (q : QuadraticDifferential Γ) (B : Atlas (q : ℂ → ℂ)) {t : ℝ} (ht : 0 < t)
    (i : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
      × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I)) :
    MeasurableSet (symRet Γ B t i) ∧ symRet Γ B t i ⊆ symOmega Γ := by
  obtain ⟨j, cq⟩ := i
  obtain ⟨hBadm, hBadnull⟩ := symBad_facts hΓ hdense
  have hωm : MeasurableSet (symOmega Γ) :=
    (isCompact_domain hΓ hfree hcc).measurableSet
  have hgrid : ∀ N : ℕ, (0 : ℝ) < t / (N + 1) := fun N => by positivity
  have hseedm : MeasurableSet (symSeed Γ B t j.1) :=
    (hωm.diff hBadm).inter ((slegal_measurable B (hgrid j.1) j.1).diff
      (MeasurableSet.iUnion fun M =>
        MeasurableSet.iUnion fun _ => slegal_measurable B (hgrid M) M))
  have hPs : symPiece Γ B t j.1 j.2 ⊆ slegal B (t / (j.1 + 1)) j.1 :=
    fun z hz => hz.1.2.1
  have hPc : ∀ z ∈ symPiece Γ B t j.1 j.2, ∀ k : Fin (j.1 + 1),
      B.sel (pos B (t / (j.1 + 1)) (k : ℕ) z) = (j.2 k).1 ∧
      sgn B (t / (j.1 + 1)) (k : ℕ) z = (if (j.2 k).2 then (1 : ℝ) else -1) :=
    fun z hz k => hz.2 k
  obtain ⟨harrm, -⟩ := piece_cov q.measurable B (hgrid j.1)
    (piece_measurable B _ _ hseedm j.2) hPs j.2 hPc
    (measurable_const : Measurable fun _ : ℂ => (1 : ℝ≥0∞))
  have hIntU : UpperHalfPlane.coe ''
      interior (dirichletDomain Γ UpperHalfPlane.I) ⊆ {z : ℂ | 0 < z.im} := by
    rintro w ⟨τ, -, rfl⟩
    simpa using τ.im_pos
  have htile : IsOpen (symTile Γ cq) := isOpen_moebius_image _
    (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_interior) hIntU
  have hXm : MeasurableSet ((symArr Γ B t j \ symBad Γ) ∩ symTile Γ cq) :=
    (harrm.diff hBadm).inter htile.measurableSet
  have hXU : (symArr Γ B t j \ symBad Γ) ∩ symTile Γ cq
      ⊆ {z : ℂ | 0 < z.im} :=
    Set.inter_subset_right.trans (symTile_upper cq)
  constructor
  · exact hXm.image_of_continuousOn_injOn ((moebius_contOn _).mono hXU)
      ((moebius_injOn _).mono hXU)
  · rintro v ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hw.2
    rw [moebius_cancel _ (hIntU hu)]
    obtain ⟨τ, hτ, rfl⟩ := hu
    exact ⟨τ, interior_subset hτ, rfl⟩

/-- The combined label-piece-coset index of the symmetrized retiling. -/
abbrev symIdx (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
  Bool × ((Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
    × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I))

set_option maxHeartbeats 400000 in
-- Heartbeats: rewriting both label decompositions inside the doubly indexed tsum goal
-- exceeds the default elaboration budget.
/-- **Symmetrized retiling identity**: the two-orientation flow average over the
fundamental tile is the total mass of the doubly indexed retiled arrival family. -/
theorem sym_total {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (A : Atlas (q : ℂ → ℂ)) {t : ℝ} (ht : 0 < t)
    {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    (hGinv : ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      G (moebiusMap ↑γ z) = G z) :
    ∫⁻ z in symOmega Γ, (G (A.flow t z) + G (A.flow (-t) z)) * ‖q z‖ₑ
      = ∑' i : symIdx Γ,
          ∫⁻ w in symRet Γ (symLab A i.1) t i.2, G w * ‖q w‖ₑ := by
  have hdec1 := label_decomp hΓ hfree hcc q hq0 hdense A (symLab A true)
    (fun z => A.flow t z) ht
    (fun N z hz => flow_eq_pos_fwd q.holo A ht hz)
    (fun z hz => good_slegal_fwd q.holo A ht hz) hG hGinv
  have hdec2 := label_decomp hΓ hfree hcc q hq0 hdense A (symLab A false)
    (fun z => A.flow (-t) z) ht
    (fun N z hz => flow_eq_pos_bwd q.holo A ht hz)
    (fun z hz => good_slegal_bwd q.holo A ht hz) hG hGinv
  have hpair : Measurable fun z : ℂ => ((t, z) : ℝ × ℂ) :=
    measurable_const.prodMk measurable_id
  have hflowt : Measurable fun z : ℂ => A.flow t z := by
    have h0 := A.measurable_flow.comp hpair
    simpa [Function.comp_def] using h0
  have hGm1 : Measurable fun z : ℂ => G (A.flow t z) := by
    have h0 := hG.comp hflowt
    simpa [Function.comp_def] using h0
  have hsplit : ∫⁻ z in symOmega Γ,
      (G (A.flow t z) + G (A.flow (-t) z)) * ‖q z‖ₑ
      = (∫⁻ z in symOmega Γ, G (A.flow t z) * ‖q z‖ₑ)
        + ∫⁻ z in symOmega Γ, G (A.flow (-t) z) * ‖q z‖ₑ := by
    rw [← lintegral_add_left (hGm1.fun_mul q.measurable.enorm)]
    exact lintegral_congr fun z => add_mul _ _ _
  have h1 : (∑' i : symIdx Γ,
        ∫⁻ w in symRet Γ (symLab A i.1) t i.2, G w * ‖q w‖ₑ)
      = ∑' b : Bool, ∑' k : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
          × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I),
          ∫⁻ w in symRet Γ (symLab A b) t k, G w * ‖q w‖ₑ :=
    ENNReal.tsum_prod'
  have h2 : (∑' b : Bool, ∑' k : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
          × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I),
          ∫⁻ w in symRet Γ (symLab A b) t k, G w * ‖q w‖ₑ)
      = (∑' k : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
          × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I),
          ∫⁻ w in symRet Γ (symLab A false) t k, G w * ‖q w‖ₑ)
        + ∑' k : (Σ N : ℕ, Fin (N + 1) → ℕ × Bool)
          × (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I),
          ∫⁻ w in symRet Γ (symLab A true) t k, G w * ‖q w‖ₑ :=
    tsum_bool _
  rw [hsplit, hdec1, hdec2, h1, h2, add_comm]

/-- **Symmetrized push bound**: for a measurable almost-everywhere `Γ`-invariant weight,
the two-orientation flow average over the fundamental tile is at most twice the mass. -/
theorem sym_upper {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (A : Atlas (q : ℂ → ℂ)) {t : ℝ} (ht : 0 < t)
    {G : ℂ → ℝ≥0∞} (hG : Measurable G)
    (hGinv : ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      G (moebiusMap ↑γ z) = G z) :
    ∫⁻ z in symOmega Γ, (G (A.flow t z) + G (A.flow (-t) z)) * ‖q z‖ₑ
      ≤ 2 * ∫⁻ z in symOmega Γ, G z * ‖q z‖ₑ := by
  classical
  have : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  have : Countable (↥Γ ⧸ MulAction.stabilizer ↥Γ UpperHalfPlane.I) :=
    QuotientGroup.mk_surjective.countable
  obtain ⟨hBadm, hBadnull⟩ := symBad_facts hΓ hdense
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hqnull : volume ({z : ℂ | (q : ℂ → ℂ) z = 0} ∩ {z : ℂ | 0 < z.im}) = 0 := by
    have h0 := ae_iff.mp (q.ae_ne_zero hq0)
    rw [Measure.restrict_apply' hUm] at h0
    refine measure_mono_null (fun z hz => ?_) h0
    exact ⟨by simpa using hz.1, hz.2⟩
  set Z : Set ℂ := symBad Γ ∪ ({z : ℂ | (q : ℂ → ℂ) z = 0} ∩ {z : ℂ | 0 < z.im})
    with hZdef
  have hZm : MeasurableSet Z := hBadm.union
    ((q.measurable (measurableSet_singleton 0)).inter hUm)
  have hZnull : volume Z = 0 := measure_union_null hBadnull hqnull
  have hretm := fun i : symIdx Γ =>
    symRet_meas hΓ hfree hcc hdense q (symLab A i.1) ht i.2
  have htrim : ∀ i : symIdx Γ,
      ∫⁻ w in symRet Γ (symLab A i.1) t i.2, G w * ‖q w‖ₑ
        = ∫⁻ w in symRet Γ (symLab A i.1) t i.2 \ Z, G w * ‖q w‖ₑ := by
    intro i
    refine setLIntegral_congr (MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩)
    · refine measure_mono_null (fun w hw => ?_) hZnull
      by_contra hb
      exact hw.2 ⟨hw.1, hb⟩
    · exact measure_mono_null (fun w hw => (hw.2 hw.1.1).elim)
        (measure_empty (μ := volume))
  have hmult : ∀ x : ℂ,
      (∑' i : symIdx Γ,
        (symRet Γ (symLab A i.1) t i.2 \ Z).indicator
          (fun _ => (1 : ℝ≥0∞)) x) ≤ 2 := by
    intro x
    by_cases hx : ∃ i : symIdx Γ, x ∈ symRet Γ (symLab A i.1) t i.2 \ Z
    · obtain ⟨i₀, hi₀⟩ := hx
      have hxω : x ∈ symOmega Γ := (hretm i₀).2 hi₀.1
      have hxim : 0 < x.im := symOmega_upper hxω
      have hxq : (q : ℂ → ℂ) x ≠ 0 := by
        intro h0
        exact hi₀.2 (Or.inr ⟨h0, hxim⟩)
      obtain ⟨i₁, i₂, hpair⟩ := mult_pair hΓ hfree hdense q A ht hxim hxq
      exact tsum_indicator_pair fun i hi => hpair i hi.1
    · push Not at hx
      have hzero : ∀ i : symIdx Γ,
          (symRet Γ (symLab A i.1) t i.2 \ Z).indicator
            (fun _ => (1 : ℝ≥0∞)) x = 0 :=
        fun i => Set.indicator_of_notMem (hx i) _
      rw [tsum_congr hzero]
      simp
  have hbound := lintegral_mult_le'
    (fun i : symIdx Γ => (hretm i).1.diff hZm) (hG.mul q.measurable.enorm) hmult
  rw [sym_total hΓ hfree hcc q hq0 hdense A ht hG hGinv, tsum_congr htrim]
  refine le_trans hbound (mul_le_mul_right (lintegral_mono_set ?_) 2)
  exact Set.iUnion_subset fun i => Set.sdiff_subset.trans (hretm i).2

/-- The quasiconformal map is almost everywhere differentiable along a Möbius shift. -/
theorem ae_diffAt_moebius {h hinv : ℂ → ℂ} {κ : ℝ} (hqc : IsQCUpper h hinv κ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      DifferentiableAt ℝ h (moebiusMap γ z) := by
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hNd : volume ({z : ℂ | ¬ DifferentiableAt ℝ h z} ∩ {z : ℂ | 0 < z.im})
      = 0 := by
    have h0 := ae_iff.mp (ae_differentiableAt hqc)
    rwa [Measure.restrict_apply' hUm] at h0
  have hNdm : MeasurableSet
      ({z : ℂ | ¬ DifferentiableAt ℝ h z} ∩ {z : ℂ | 0 < z.im}) :=
    (measurableSet_of_differentiableAt ℝ h).compl.inter hUm
  have himnull : volume (moebiusMap γ⁻¹ ''
      ({z : ℂ | ¬ DifferentiableAt ℝ h z} ∩ {z : ℂ | 0 < z.im})) = 0 :=
    image_null hNdm hNd (fun z hz => moebius_diffAt _ hz.2)
      ((moebius_injOn _).mono fun z hz => hz.2)
  rw [ae_restrict_iff' hUm, ae_iff]
  refine measure_mono_null (fun z hz => ?_) himnull
  push Not at hz
  obtain ⟨hzU, hznd⟩ := hz
  exact ⟨moebiusMap γ z, ⟨hznd, moebiusMap_im_pos _ hzU⟩, moebius_cancel _ hzU⟩

/-- Almost-everywhere `Γ`-invariance of the first Cauchy–Schwarz factor. -/
theorem rsU_ae_inv {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ}
    (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z)) :
    ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsU (q : ℂ → ℂ) h κ (moebiusMap ↑γ z) = rsU (q : ℂ → ℂ) h κ z := by
  intro γ
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  filter_upwards [ae_differentiableAt hqc, ae_diffAt_moebius hqc ↑γ,
    ae_restrict_mem hUm] with z hdz hdγz hzU
  exact rsU_moebius ↑γ κ hzU (hqc.mapsTo z hzU) (q.automorphy ↑γ γ.2 z hzU)
    (q.automorphy ↑γ γ.2 (h z) (hqc.mapsTo z hzU))
    (fun w hw => hcomm ↑γ γ.2 w hw) hdz hdγz

/-- Almost-everywhere `Γ`-invariance of the floored weight. -/
theorem rsWeightM_ae_inv {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) {h hinv : ℂ → ℂ} {κ : ℝ}
    (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z)) :
    ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsWeightM (q : ℂ → ℂ) h κ (moebiusMap ↑γ z)
        = rsWeightM (q : ℂ → ℂ) h κ z := by
  intro γ
  have hUm : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  filter_upwards [ae_differentiableAt hqc, ae_diffAt_moebius hqc ↑γ,
    ae_restrict_mem hUm] with z hdz hdγz hzU
  exact rsWeightM_moebius ↑γ κ hzU (hqc.mapsTo z hzU) (q.automorphy ↑γ γ.2 z hzU)
    (fun w hw => hcomm ↑γ γ.2 w hw) hdz hdγz

/-- Fixed-time measurability of a weight composed with the flow. -/
theorem meas_F_flow {q : ℂ → ℂ} (A : Atlas q) {F : ℂ → ℝ≥0∞}
    (hF : Measurable F) (u : ℝ) :
    Measurable fun z : ℂ => F (A.flow u z) := by
  have hpair : Measurable fun z : ℂ => ((u, z) : ℝ × ℂ) :=
    measurable_const.prodMk measurable_id
  have h0 := A.measurable_flow.comp hpair
  have h1 : Measurable fun z : ℂ => A.flow u z := by
    simpa [Function.comp_def] using h0
  have h2 := hF.comp h1
  simpa [Function.comp_def] using h2

/-- **Dyadic minoration**: a halving functional inequality forces the double mass as a
lower bound. -/
theorem sym_iter {a : ℝ → ℝ≥0∞} {Fb : ℝ≥0∞}
    (hkey : ∀ s : ℝ, 0 < s → 2 * Fb + a (2 * s) ≤ 2 * a s) {t : ℝ} (ht : 0 < t) :
    2 * Fb ≤ a t := by
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  by_cases hFbtop : Fb = ⊤
  · have h1 := hkey t ht
    rw [hFbtop] at h1 ⊢
    have h2 : (⊤ : ℝ≥0∞) ≤ 2 * a t := le_trans (by simp) h1
    have h3 : a t = ⊤ := by
      by_contra hne
      exact ENNReal.mul_ne_top h2top hne (top_le_iff.mp h2)
    rw [h3]
    exact le_top
  · have h2Fb : 2 * Fb ≠ ⊤ := ENNReal.mul_ne_top h2top hFbtop
    have hlow : ∀ n : ℕ, ∀ s : ℝ, 0 < s →
        2 * Fb ≤ a s + (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb) := by
      intro n
      induction n with
      | zero =>
        intro s hs
        simp
      | succ n ih =>
        intro s hs
        have h1 := hkey s hs
        have h2 := ih (2 * s) (by positivity)
        have h3 : 2 * (2 * Fb) ≤ 2 * a s + (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb) := by
          calc 2 * (2 * Fb) = 2 * Fb + 2 * Fb := two_mul _
            _ ≤ 2 * Fb + (a (2 * s) + (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb)) :=
                add_le_add le_rfl h2
            _ = (2 * Fb + a (2 * s)) + (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb) :=
                (add_assoc _ _ _).symm
            _ ≤ 2 * a s + (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb) := add_le_add h1 le_rfl
        have h4 : 2 * a s + (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb)
            = 2 * (a s + (2 : ℝ≥0∞)⁻¹ ^ (n + 1) * (2 * Fb)) := by
          rw [mul_add]
          congr 1
          rw [pow_succ, mul_comm ((2 : ℝ≥0∞)⁻¹ ^ n) (2 : ℝ≥0∞)⁻¹, mul_assoc,
            ← mul_assoc (2 : ℝ≥0∞) (2 : ℝ≥0∞)⁻¹,
            ENNReal.mul_inv_cancel two_ne_zero h2top, one_mul]
        rw [h4] at h3
        exact (ENNReal.mul_le_mul_iff_right two_ne_zero h2top).mp h3
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    by_cases hc0 : 2 * Fb = 0
    · rw [hc0]
      exact zero_le
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt
      (a := (ε : ℝ≥0∞) / (2 * Fb))
      (ENNReal.div_pos (ENNReal.coe_ne_zero.mpr hε.ne') h2Fb).ne'
    have hle : (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb) ≤ ε := by
      calc (2 : ℝ≥0∞)⁻¹ ^ n * (2 * Fb)
          ≤ ((ε : ℝ≥0∞) / (2 * Fb)) * (2 * Fb) := mul_le_mul_left hn.le _
        _ = ε := ENNReal.div_mul_cancel hc0 h2Fb
    exact le_trans (hlow n t ht) (add_le_add le_rfl hle)

/-- **Dyadic pair step**: the doubled mass plus the doubled-time pair integral is
dominated by twice the single-time pair integral. -/
theorem pair_step {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane,
      Metric.infDist σ (MulAction.orbit Γ UpperHalfPlane.I) ≤ R)
    (A : Atlas (q : ℂ → ℂ)) {F : ℂ → ℝ≥0∞} (hF : Measurable F)
    (htwo : ∀ z ∈ good (q : ℂ → ℂ) A, ∀ s : ℝ, 0 < s →
      ((A.flow s (A.flow s z) = A.flow (2 * s) z
          ∧ A.flow (-s) (A.flow s z) = z) ∨
        (A.flow s (A.flow s z) = z
          ∧ A.flow (-s) (A.flow s z) = A.flow (2 * s) z)) ∧
      ((A.flow s (A.flow (-s) z) = A.flow (-(2 * s)) z
          ∧ A.flow (-s) (A.flow (-s) z) = z) ∨
        (A.flow s (A.flow (-s) z) = z
          ∧ A.flow (-s) (A.flow (-s) z) = A.flow (-(2 * s)) z)))
    (hdeck : ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      F (A.flow s (moebiusMap ↑γ z)) + F (A.flow (-s) (moebiusMap ↑γ z))
        = F (A.flow s z) + F (A.flow (-s) z))
    {s : ℝ} (hs : 0 < s) :
    2 * (∫⁻ z in symOmega Γ, F z * ‖q z‖ₑ)
        + ∫⁻ z in symOmega Γ,
            (F (A.flow (2 * s) z) + F (A.flow (-(2 * s)) z)) * ‖q z‖ₑ
      ≤ 2 * ∫⁻ z in symOmega Γ,
            (F (A.flow s z) + F (A.flow (-s) z)) * ‖q z‖ₑ := by
  have hωU : symOmega Γ ⊆ {z : ℂ | 0 < z.im} := symOmega_upper
  have hGm : Measurable fun z : ℂ => F (A.flow s z) + F (A.flow (-s) z) :=
    (meas_F_flow A hF s).add (meas_F_flow A hF (-s))
  have hup := sym_upper hΓ hfree hcc q hq0 hdense A hs hGm (hdeck s hs)
  beta_reduce at hup
  have hBid : ∀ᵐ z ∂(volume.restrict (symOmega Γ)),
      (F (A.flow s (A.flow s z)) + F (A.flow (-s) (A.flow s z))
        + (F (A.flow s (A.flow (-s) z)) + F (A.flow (-s) (A.flow (-s) z))))
          * ‖q z‖ₑ
      = (2 * F z + (F (A.flow (2 * s) z) + F (A.flow (-(2 * s)) z)))
          * ‖q z‖ₑ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hωU
      (good_ae hΓ hcc q hq0 A)] with z hzg
    obtain ⟨hpos, hneg⟩ := htwo z hzg s hs
    have e1 : F (A.flow s (A.flow s z)) + F (A.flow (-s) (A.flow s z))
        = F (A.flow (2 * s) z) + F z := by
      rcases hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]
        exact add_comm _ _
    have e2 : F (A.flow s (A.flow (-s) z)) + F (A.flow (-s) (A.flow (-s) z))
        = F (A.flow (-(2 * s)) z) + F z := by
      rcases hneg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2]
        exact add_comm _ _
    rw [e1, e2]
    ring
  have hL := lintegral_congr_ae hBid
  have hsplit : ∫⁻ z in symOmega Γ,
      (2 * F z + (F (A.flow (2 * s) z) + F (A.flow (-(2 * s)) z))) * ‖q z‖ₑ
      = 2 * (∫⁻ z in symOmega Γ, F z * ‖q z‖ₑ)
        + ∫⁻ z in symOmega Γ,
            (F (A.flow (2 * s) z) + F (A.flow (-(2 * s)) z)) * ‖q z‖ₑ := by
    have hm2 : Measurable fun z : ℂ => 2 * (F z * ‖q z‖ₑ) :=
      (hF.mul q.measurable.enorm).const_mul 2
    rw [← lintegral_const_mul 2 (hF.fun_mul q.measurable.enorm),
      ← lintegral_add_left hm2]
    exact lintegral_congr fun z => by ring
  calc 2 * (∫⁻ z in symOmega Γ, F z * ‖q z‖ₑ)
        + ∫⁻ z in symOmega Γ,
            (F (A.flow (2 * s) z) + F (A.flow (-(2 * s)) z)) * ‖q z‖ₑ
      = ∫⁻ z in symOmega Γ,
          (2 * F z + (F (A.flow (2 * s) z) + F (A.flow (-(2 * s)) z)))
            * ‖q z‖ₑ := hsplit.symm
    _ = ∫⁻ z in symOmega Γ,
          (F (A.flow s (A.flow s z)) + F (A.flow (-s) (A.flow s z))
            + (F (A.flow s (A.flow (-s) z)) + F (A.flow (-s) (A.flow (-s) z))))
              * ‖q z‖ₑ := hL.symm
    _ ≤ 2 * ∫⁻ z in symOmega Γ,
          (F (A.flow s z) + F (A.flow (-s) z)) * ‖q z‖ₑ := hup

/-- **Symmetrized invariance engine**: for a measurable, almost-everywhere
`Γ`-invariant weight compatible with the flow deck action and the dyadic two-step law,
the two-orientation flow average of the weight against `|q| dA` over the fundamental
tile equals twice its mass, at every time. -/
theorem sym_invar_engine {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (q : ℂ → ℂ)) {F : ℂ → ℝ≥0∞} (hF : Measurable F)
    (hFinv : ∀ γ : ↥Γ, ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      F (moebiusMap ↑γ z) = F z)
    (htwo : ∀ z ∈ good (q : ℂ → ℂ) A, ∀ s : ℝ, 0 < s →
      ((A.flow s (A.flow s z) = A.flow (2 * s) z
          ∧ A.flow (-s) (A.flow s z) = z) ∨
        (A.flow s (A.flow s z) = z
          ∧ A.flow (-s) (A.flow s z) = A.flow (2 * s) z)) ∧
      ((A.flow s (A.flow (-s) z) = A.flow (-(2 * s)) z
          ∧ A.flow (-s) (A.flow (-s) z) = z) ∨
        (A.flow s (A.flow (-s) z) = z
          ∧ A.flow (-s) (A.flow (-s) z) = A.flow (-(2 * s)) z)))
    (hdeck : ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      F (A.flow s (moebiusMap ↑γ z)) + F (A.flow (-s) (moebiusMap ↑γ z))
        = F (A.flow s z) + F (A.flow (-s) z)) :
    ∀ t : ℝ,
      ∫⁻ z in symOmega Γ, (F (A.flow t z) + F (A.flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in symOmega Γ, F z * ‖q z‖ₑ := by
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc
    UpperHalfPlane.I
  have hωm : MeasurableSet (symOmega Γ) :=
    (isCompact_domain hΓ hfree hcc).measurableSet
  have hωU : symOmega Γ ⊆ {z : ℂ | 0 < z.im} := symOmega_upper
  have hpos : ∀ t : ℝ, 0 < t →
      ∫⁻ z in symOmega Γ, (F (A.flow t z) + F (A.flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in symOmega Γ, F z * ‖q z‖ₑ := by
    intro t ht
    refine le_antisymm
      (sym_upper hΓ hfree hcc q hq0 hdense A ht hF hFinv) ?_
    exact sym_iter
      (a := fun s => ∫⁻ z in symOmega Γ,
        (F (A.flow s z) + F (A.flow (-s) z)) * ‖q z‖ₑ)
      (fun s hs => pair_step hΓ hfree hcc q hq0 hdense A hF htwo hdeck hs)
      ht
  intro t
  rcases lt_trichotomy t 0 with htn | ht0 | htp
  · have h1 : ∫⁻ z in symOmega Γ,
        (F (A.flow t z) + F (A.flow (-t) z)) * ‖q z‖ₑ
        = ∫⁻ z in symOmega Γ,
          (F (A.flow (-t) z) + F (A.flow (- -t) z)) * ‖q z‖ₑ := by
      refine lintegral_congr fun z => ?_
      rw [neg_neg]
      ring
    rw [h1]
    exact hpos (-t) (by linarith)
  · subst ht0
    have hcongr : ∀ᵐ z ∂(volume.restrict (symOmega Γ)),
        (F (A.flow 0 z) + F (A.flow (-0) z)) * ‖q z‖ₑ = 2 * (F z * ‖q z‖ₑ) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hωU
        (q.ae_ne_zero hq0), ae_restrict_mem hωm] with z hqz hzω
      rw [neg_zero, flow_zero A (symOmega_upper hzω) hqz]
      ring
    rw [lintegral_congr_ae hcongr,
      lintegral_const_mul 2 (hF.fun_mul q.measurable.enorm)]
  · exact hpos t htp

/-- **Symmetrized flow invariance of the first Cauchy–Schwarz factor** against the
`|q|` area: the `invar_U` field of `VerticalFlowDataSym` for the atlas flow, from the
Reich–Strebel hypotheses, the dyadic two-step law of the flow on the regular set, and the
almost-everywhere deck compatibility of the symmetrized factor. -/
theorem sym_invar_U {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (_hκ : κ < 1) (hqc : IsQCUpper h hinv κ)
    (hh : Measurable h)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ))
    (htwo : ∀ z ∈ good (q : ℂ → ℂ) A, ∀ s : ℝ, 0 < s →
      ((A.flow s (A.flow s z) = A.flow (2 * s) z
          ∧ A.flow (-s) (A.flow s z) = z) ∨
        (A.flow s (A.flow s z) = z
          ∧ A.flow (-s) (A.flow s z) = A.flow (2 * s) z)) ∧
      ((A.flow s (A.flow (-s) z) = A.flow (-(2 * s)) z
          ∧ A.flow (-s) (A.flow (-s) z) = z) ∨
        (A.flow s (A.flow (-s) z) = z
          ∧ A.flow (-s) (A.flow (-s) z) = A.flow (-(2 * s)) z)))
    (hdeckU : ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsU (q : ℂ → ℂ) h κ (A.flow s (moebiusMap ↑γ z))
          + rsU (q : ℂ → ℂ) h κ (A.flow (-s) (moebiusMap ↑γ z))
        = rsU (q : ℂ → ℂ) h κ (A.flow s z)
          + rsU (q : ℂ → ℂ) h κ (A.flow (-s) z)) :
    ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsU q h κ (A.flow t z) + rsU q h κ (A.flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsU q h κ z * ‖q z‖ₑ :=
  sym_invar_engine hΓ hfree hcc q hq0 A
    (measurable_rsU q.measurable hh κ) (rsU_ae_inv q hqc hcomm) htwo hdeckU

/-- **Symmetrized flow invariance of the floored weight** against the `|q|` area: the
`invar_W` field of `VerticalFlowDataSym` for the atlas flow, from the Reich–Strebel
standing hypotheses, the dyadic two-step law of the flow on the regular set, and the
almost-everywhere
deck compatibility of the symmetrized weight. -/
theorem sym_invar_W {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {h hinv : ℂ → ℂ} {κ : ℝ} (_hκ : κ < 1) (hqc : IsQCUpper h hinv κ)
    (hcomm : ∀ γ ∈ Γ, ∀ z : ℂ, 0 < z.im →
      h (moebiusMap γ z) = moebiusMap γ (h z))
    (A : Atlas (q : ℂ → ℂ))
    (htwo : ∀ z ∈ good (q : ℂ → ℂ) A, ∀ s : ℝ, 0 < s →
      ((A.flow s (A.flow s z) = A.flow (2 * s) z
          ∧ A.flow (-s) (A.flow s z) = z) ∨
        (A.flow s (A.flow s z) = z
          ∧ A.flow (-s) (A.flow s z) = A.flow (2 * s) z)) ∧
      ((A.flow s (A.flow (-s) z) = A.flow (-(2 * s)) z
          ∧ A.flow (-s) (A.flow (-s) z) = z) ∨
        (A.flow s (A.flow (-s) z) = z
          ∧ A.flow (-s) (A.flow (-s) z) = A.flow (-(2 * s)) z)))
    (hdeckW : ∀ s : ℝ, 0 < s → ∀ γ : ↥Γ,
      ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      rsWeightM (q : ℂ → ℂ) h κ (A.flow s (moebiusMap ↑γ z))
          + rsWeightM (q : ℂ → ℂ) h κ (A.flow (-s) (moebiusMap ↑γ z))
        = rsWeightM (q : ℂ → ℂ) h κ (A.flow s z)
          + rsWeightM (q : ℂ → ℂ) h κ (A.flow (-s) z)) :
    ∀ t : ℝ,
      ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
        (rsWeightM q h κ (A.flow t z) + rsWeightM q h κ (A.flow (-t) z)) * ‖q z‖ₑ
        = 2 * ∫⁻ z in UpperHalfPlane.coe '' dirichletDomain Γ UpperHalfPlane.I,
          rsWeightM q h κ z * ‖q z‖ₑ :=
  sym_invar_engine hΓ hfree hcc q hq0 A
    (measurable_rsWeightM q.measurable h κ) (rsWeightM_ae_inv q hqc hcomm)
    htwo hdeckW

/-- The image of a closed interval under a positively sloped affine map. -/
theorem image_affine_Icc {c : ℝ} (hc : 0 < c) (d u v : ℝ) :
    (fun s => c * s + d) '' Set.Icc u v = Set.Icc (c * u + d) (c * v + d) := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  · intro hx
    refine ⟨(x - d) / c, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hc]
      nlinarith [hx.1]
    · rw [div_le_iff₀ hc]
      nlinarith [hx.2]
    · field_simp
      ring

/-- **Affine change of variables** for the lower integral over a set. -/
theorem setLIntegral_affine (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) (d : ℝ)
    (A : Set ℝ) :
    ∫⁻ s in A, f (c * s + d)
      = ENNReal.ofReal c⁻¹ * ∫⁻ u in (fun s => c * s + d) '' A, f u := by
  have hemb : MeasurableEmbedding (fun s : ℝ => c * s + d) := by
    have h1 : (fun s : ℝ => c * s + d)
        = (Homeomorph.addRight d) ∘ (Homeomorph.mulLeft₀ c hc.ne') := rfl
    rw [h1]
    exact (Homeomorph.addRight d).measurableEmbedding.comp
      (Homeomorph.mulLeft₀ c hc.ne').measurableEmbedding
  have hmp : MeasurePreserving (fun s : ℝ => c * s + d) volume
      (ENNReal.ofReal c⁻¹ • volume) := by
    refine ⟨hemb.measurable, ?_⟩
    have h1 : (fun s : ℝ => c * s + d) = (fun x => x + d) ∘ (fun x => c * x) :=
      rfl
    rw [h1, ← Measure.map_map (measurable_add_const d) (measurable_const_mul c)]
    rw [Real.map_volume_mul_left hc.ne', Measure.map_smul,
      map_add_right_eq_self volume d]
    congr 1
    rw [abs_of_pos (by positivity)]
  rw [hmp.setLIntegral_comp_emb hemb f A, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul]

/-- **Subadditivity of the horizontal variation under concatenation**. -/
theorem pathJoin_horVar_le (q : ℂ → ℂ) (γ₁ γ₂ : ℝ → ℂ) :
    horizontalVariation q (pathJoin γ₁ γ₂)
      ≤ horizontalVariation q γ₁ + horizontalVariation q γ₂ := by
  have hpt : ∀ (c : ℝ) (A : Set ℝ), volume.restrict A {c} = 0 := by
    intro c A
    rw [Measure.restrict_apply (measurableSet_singleton c)]
    refine le_antisymm
      (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le)
    simp
  have h1 : ∫⁻ s in Set.Icc (0 : ℝ) (1 / 2),
      horizontalDensity q (pathJoin γ₁ γ₂) s = horizontalVariation q γ₁ := by
    have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) (1 / 2))),
        horizontalDensity q (pathJoin γ₁ γ₂) s
          = ENNReal.ofReal 2 * horizontalDensity q γ₁ (2 * s + 0) := by
      have hne : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) (1 / 2))),
          s ≠ 1 / 2 := by
        rw [ae_iff]
        refine measure_mono_null (t := {(1 / 2 : ℝ)}) (fun s hs =>
          Set.mem_singleton_iff.mpr (not_not.mp hs)) (hpt _ _)
      have hmem : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) (1 / 2))),
          s ∈ Set.Icc (0 : ℝ) (1 / 2) := ae_restrict_mem measurableSet_Icc
      filter_upwards [hmem, hne] with s hs hs12
      have hslt : s < 1 / 2 := lt_of_le_of_ne hs.2 hs12
      have hval : pathJoin γ₁ γ₂ s = (fun t => γ₁ (2 * t + 0)) s := by
        change (if s ≤ 1 / 2 then γ₁ (2 * s) else γ₂ (2 * s - 1)) = γ₁ (2 * s + 0)
        rw [if_pos hslt.le, add_zero]
      have hder : deriv (pathJoin γ₁ γ₂) s
          = deriv (fun t => γ₁ (2 * t + 0)) s := by
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [Iio_mem_nhds hslt] with u hu
        change (if u ≤ 1 / 2 then γ₁ (2 * u) else γ₂ (2 * u - 1)) = γ₁ (2 * u + 0)
        rw [if_pos (le_of_lt hu), add_zero]
      have hden : horizontalDensity q (pathJoin γ₁ γ₂) s
          = horizontalDensity q (fun t => γ₁ (2 * t + 0)) s := by
        unfold horizontalDensity
        rw [hval, hder]
      rw [hden, horizontalDensity_affine q γ₁ 0 s two_pos]
    rw [lintegral_congr_ae hae,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_affine (horizontalDensity q γ₁) two_pos 0
        (Set.Icc 0 (1 / 2)),
      image_affine_Icc two_pos 0 0 (1 / 2),
      show (2 : ℝ) * 0 + 0 = 0 by norm_num,
      show (2 : ℝ) * (1 / 2) + 0 = 1 by norm_num,
      ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    rfl
  have h2 : ∫⁻ s in Set.Icc (1 / 2 : ℝ) 1,
      horizontalDensity q (pathJoin γ₁ γ₂) s = horizontalVariation q γ₂ := by
    have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (1 / 2 : ℝ) 1)),
        horizontalDensity q (pathJoin γ₁ γ₂) s
          = ENNReal.ofReal 2 * horizontalDensity q γ₂ (2 * s + -1) := by
      have hne : ∀ᵐ s ∂(volume.restrict (Set.Icc (1 / 2 : ℝ) 1)),
          s ≠ 1 / 2 := by
        rw [ae_iff]
        refine measure_mono_null (t := {(1 / 2 : ℝ)}) (fun s hs =>
          Set.mem_singleton_iff.mpr (not_not.mp hs)) (hpt _ _)
      have hmem : ∀ᵐ s ∂(volume.restrict (Set.Icc (1 / 2 : ℝ) 1)),
          s ∈ Set.Icc (1 / 2 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
      filter_upwards [hmem, hne] with s hs hs12
      have hslt : 1 / 2 < s := lt_of_le_of_ne hs.1 (Ne.symm hs12)
      have hval : pathJoin γ₁ γ₂ s = (fun t => γ₂ (2 * t + -1)) s := by
        change (if s ≤ 1 / 2 then γ₁ (2 * s) else γ₂ (2 * s - 1)) = γ₂ (2 * s + -1)
        rw [if_neg (not_le.mpr hslt)]
        ring_nf
      have hder : deriv (pathJoin γ₁ γ₂) s
          = deriv (fun t => γ₂ (2 * t + -1)) s := by
        refine Filter.EventuallyEq.deriv_eq ?_
        filter_upwards [Ioi_mem_nhds hslt] with u hu
        change (if u ≤ 1 / 2 then γ₁ (2 * u) else γ₂ (2 * u - 1)) = γ₂ (2 * u + -1)
        rw [if_neg (not_le.mpr hu)]
        ring_nf
      have hden : horizontalDensity q (pathJoin γ₁ γ₂) s
          = horizontalDensity q (fun t => γ₂ (2 * t + -1)) s := by
        unfold horizontalDensity
        rw [hval, hder]
      rw [hden, horizontalDensity_affine q γ₂ (-1) s two_pos]
    rw [lintegral_congr_ae hae,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_affine (horizontalDensity q γ₂) two_pos (-1)
        (Set.Icc (1 / 2) 1),
      image_affine_Icc two_pos (-1) (1 / 2) 1,
      show (2 : ℝ) * (1 / 2) + -1 = 0 by norm_num,
      show (2 : ℝ) * 1 + -1 = 1 by norm_num,
      ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    rfl
  have hsplit : Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1 :=
    (Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
  calc horizontalVariation q (pathJoin γ₁ γ₂)
      = ∫⁻ s in Set.Icc 0 (1 / 2) ∪ Set.Icc (1 / 2) 1,
        horizontalDensity q (pathJoin γ₁ γ₂) s := by
        rw [horizontalVariation, hsplit]
    _ ≤ (∫⁻ s in Set.Icc (0 : ℝ) (1 / 2),
          horizontalDensity q (pathJoin γ₁ γ₂) s)
        + ∫⁻ s in Set.Icc (1 / 2 : ℝ) 1,
          horizontalDensity q (pathJoin γ₁ γ₂) s := lintegral_union_le _ _ _
    _ = horizontalVariation q γ₁ + horizontalVariation q γ₂ := by rw [h1, h2]

/-- **Triangle inequality** for the horizontal pseudodistance. -/
theorem horizontalDist_triangle (q : ℂ → ℂ) (a b c : ℂ) :
    horizontalDist q a c ≤ horizontalDist q a b + horizontalDist q b c := by
  have key : ∀ γ₁, IsFlatPath γ₁ a b → ∀ γ₂, IsFlatPath γ₂ b c →
      horizontalDist q a c
        ≤ horizontalVariation q γ₁ + horizontalVariation q γ₂ :=
    fun γ₁ h₁ γ₂ h₂ => le_trans (horizontalDist_le (pathJoin_isFlatPath h₁ h₂))
      (pathJoin_horVar_le q γ₁ γ₂)
  by_cases h1 : horizontalDist q a b = ⊤
  · rw [h1, top_add]
    exact le_top
  by_cases h2 : horizontalDist q b c = ⊤
  · rw [h2, add_top]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_pos_iff]
    exact ⟨by exact_mod_cast hε.ne', by norm_num⟩
  have hlt₁ : horizontalDist q a b < horizontalDist q a b + (ε : ℝ≥0∞) / 2 :=
    ENNReal.lt_add_right h1 hε2.ne'
  have hlt₂ : horizontalDist q b c < horizontalDist q b c + (ε : ℝ≥0∞) / 2 :=
    ENNReal.lt_add_right h2 hε2.ne'
  obtain ⟨γ₁, hγ₁⟩ := iInf_lt_iff.mp hlt₁
  obtain ⟨hp₁, hv₁⟩ := iInf_lt_iff.mp hγ₁
  obtain ⟨γ₂, hγ₂⟩ := iInf_lt_iff.mp hlt₂
  obtain ⟨hp₂, hv₂⟩ := iInf_lt_iff.mp hγ₂
  calc horizontalDist q a c
      ≤ horizontalVariation q γ₁ + horizontalVariation q γ₂ :=
        key γ₁ hp₁ γ₂ hp₂
    _ ≤ (horizontalDist q a b + (ε : ℝ≥0∞) / 2)
        + (horizontalDist q b c + (ε : ℝ≥0∞) / 2) :=
        add_le_add hv₁.le hv₂.le
    _ = horizontalDist q a b + horizontalDist q b c
        + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := by ring
    _ = horizontalDist q a b + horizontalDist q b c + (ε : ℝ≥0∞) := by
        rw [ENNReal.add_halves]

/-- **The pseudodistance form of the leafwise lower bound**: the no-shortcut inequality
for the leaf, flat-distance connector bounds, and admissibility with a reparametrization
bound for the image curve close the leafwise field shape. -/
theorem leaf_lb_of_dH {q : ℂ → ℂ} {γ : ℝ → ℂ} {z w : ℂ}
    {T : ℝ} {C : ℝ≥0∞} {ρ : ℝ → ℝ≥0∞}
    (hshort : ENNReal.ofReal T ≤ horizontalDist q z w)
    (hpath : IsFlatPath γ (γ 0) (γ 1))
    (hC0 : qdDist q z (γ 0) ≤ C) (hC1 : qdDist q (γ 1) w ≤ C)
    (hrepar : horizontalVariation q γ ≤ ∫⁻ t in Set.Icc (0 : ℝ) T, ρ t) :
    ENNReal.ofReal T ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, ρ t) + 2 * C := by
  calc ENNReal.ofReal T
      ≤ horizontalDist q z w := hshort
    _ ≤ horizontalDist q z (γ 1) + horizontalDist q (γ 1) w :=
        horizontalDist_triangle q z (γ 1) w
    _ ≤ (horizontalDist q z (γ 0) + horizontalDist q (γ 0) (γ 1))
        + horizontalDist q (γ 1) w :=
        add_le_add (horizontalDist_triangle q z (γ 0) (γ 1)) le_rfl
    _ ≤ (C + ∫⁻ t in Set.Icc (0 : ℝ) T, ρ t) + C := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact le_trans (horizontalDist_le_qdDist q _ _) hC0
        · exact le_trans (horizontalDist_le hpath) hrepar
        · exact le_trans (horizontalDist_le_qdDist q _ _) hC1
    _ = (∫⁻ t in Set.Icc (0 : ℝ) T, ρ t) + 2 * C := by ring

/-- The trivial junction pull is the identity. -/
theorem chainPull_id : ∀ (n : ℕ) (v : ℝ),
    chainPull (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) n v = v := by
  intro n
  induction n with
  | zero =>
    intro v
    rfl
  | succ n ih =>
    intro v
    change chainPull (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) n (1 * (v - 0)) = v
    rw [one_mul, sub_zero]
    exact ih v

/-- **The local no-shortcut bound**: along an absolutely continuous curve inside an
open set carrying a global natural chart, the horizontal variation dominates the
developed real displacement. -/
theorem global_chart_variation_lb {q Φg : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΦgd : DifferentiableOn ℂ Φg U)
    (hΦgsq : ∀ w ∈ U, deriv Φg w ^ 2 = -q w)
    {p : ℝ → ℂ} (hpc : ContinuousOn p (Set.Icc 0 1))
    (hpac : AbsolutelyContinuousOnInterval p 0 1)
    (htr : ∀ s ∈ Set.Icc (0 : ℝ) 1, p s ∈ U) :
    ENNReal.ofReal |(Φg (p 1)).re - (Φg (p 0)).re|
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) 1, horizontalDensity q p s := by
  classical
  set K : Set ℂ := p '' Set.Icc 0 1 with hKdef
  have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn hpc
  have hKU : ∀ x ∈ K, x ∈ U := by
    rintro x ⟨s, hs, rfl⟩
    exact htr s hs
  have hrad : ∀ x : K, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : ℂ) r ⊆ U := by
    intro x
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU (x : ℂ) (hKU x x.2)
    exact ⟨r, hr, hsub⟩
  choose rx hrx hrxU using hrad
  obtain ⟨δe, hδe, hleb⟩ := lebesgue_number_lemma_of_emetric (s := K)
    (c := fun x : K => Metric.ball (x : ℂ) (rx x)) hKc
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrx ⟨x, hx⟩)⟩)
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδe
  have hδ'pos : (0 : ℝ) < δ' := by exact_mod_cast hδ'0
  have hballs : ∀ x ∈ K, ∃ y : K,
      Metric.ball x (δ' : ℝ) ⊆ Metric.ball (y : ℂ) (rx y) := by
    intro x hx
    obtain ⟨y, hy⟩ := hleb x hx
    refine ⟨y, ?_⟩
    intro w hw
    apply hy
    rw [Metric.mem_eball]
    exact lt_trans (edist_lt_coe.mpr (Metric.mem_ball.mp hw)) hδ'
  have hunif : UniformContinuousOn p (Set.Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hpc
  obtain ⟨Δ, hΔ0, hΔ⟩ := Metric.uniformContinuousOn_iff.mp hunif (δ' : ℝ) hδ'pos
  set m : ℕ := ⌈2 / Δ⌉₊ + 1 with hmdef
  set t : ℕ → ℝ := fun i => if i = 0 then 0
    else min ((i - 1 : ℕ) * (Δ / 2)) 1 with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have ht1 : t 1 = 0 := by simp [htdef]
  have htmem : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    by_cases h : i = 0
    · simp [htdef, h]
    · simp only [htdef, if_neg h]
      constructor
      · exact le_min (by positivity) zero_le_one
      · exact min_le_right _ _
  have htlast : ∀ i, m + 1 ≤ i → t i = 1 := by
    intro i hi
    have hne : i ≠ 0 := by omega
    simp only [htdef, if_neg hne]
    rw [min_eq_right]
    have h2 : (2 : ℝ) / Δ ≤ ⌈2 / Δ⌉₊ := Nat.le_ceil _
    have hm : (m : ℝ) ≤ (i - 1 : ℕ) := by
      have : m ≤ i - 1 := by omega
      exact_mod_cast this
    have hmΔ : (2 : ℝ) / Δ * (Δ / 2) ≤ (i - 1 : ℕ) * (Δ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc (2 : ℝ) / Δ ≤ ⌈2 / Δ⌉₊ := h2
        _ ≤ (m : ℝ) := by exact_mod_cast Nat.le_succ _
        _ ≤ _ := hm
    calc (1 : ℝ) = 2 / Δ * (Δ / 2) := by field_simp
      _ ≤ _ := hmΔ
  have htmono : ∀ i, t i ≤ t (i + 1) := by
    intro i
    by_cases h : i = 0
    · rw [h, ht0]
      exact (htmem 1).1
    · simp only [htdef, if_neg h, if_neg (Nat.succ_ne_zero i)]
      have : ((i - 1 : ℕ) : ℝ) ≤ ((i + 1 - 1 : ℕ) : ℝ) := by
        have : i - 1 ≤ i + 1 - 1 := by omega
        exact_mod_cast this
      exact min_le_min (mul_le_mul_of_nonneg_right this (by positivity)) le_rfl
  have htmesh : ∀ i, t (i + 1) - t i ≤ Δ / 2 := by
    intro i
    by_cases h : i = 0
    · rw [h, ht0, ht1]
      simp only [sub_self]
      positivity
    · simp only [htdef, if_neg h, if_neg (Nat.succ_ne_zero i)]
      have hstep : ((i + 1 - 1 : ℕ) : ℝ) * (Δ / 2)
          = ((i - 1 : ℕ) : ℝ) * (Δ / 2) + Δ / 2 := by
        have : (i + 1 - 1 : ℕ) = (i - 1) + 1 := by omega
        rw [this]
        push_cast
        ring
      have h1 : min (((i + 1 - 1 : ℕ) : ℝ) * (Δ / 2)) 1
          ≤ min (((i - 1 : ℕ) : ℝ) * (Δ / 2)) 1 + Δ / 2 := by
        rw [hstep]
        rcases le_or_gt (((i - 1 : ℕ) : ℝ) * (Δ / 2)) 1 with hc | hc
        · rw [min_eq_left hc]
          exact le_trans (min_le_left _ _) (by linarith)
        · rw [min_eq_right hc.le]
          have : min (((i - 1 : ℕ) : ℝ) * (Δ / 2) + Δ / 2) 1 ≤ 1 :=
            min_le_right _ _
          linarith
      linarith
  have hpieces : ∀ i : ℕ, ∃ x : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball x ρ ⊆ U ∧
      ∀ s ∈ Set.Icc (t i) (t (i + 1)), p s ∈ Metric.ball x ρ := by
    intro i
    have htiK : p (t i) ∈ K := Set.mem_image_of_mem p (htmem i)
    obtain ⟨y, hy⟩ := hballs (p (t i)) htiK
    refine ⟨(y : ℂ), rx y, hrx y, hrxU y, ?_⟩
    intro s hs
    apply hy
    rw [Metric.mem_ball]
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (htmem i).1 hs.1, le_trans hs.2 (htmem (i + 1)).2⟩
    have hd : dist s (t i) < Δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
      have h1 := htmesh i
      have h2 := hs.2
      linarith
    exact hΔ s hs01 (t i) (htmem i) hd
  choose xf ρf hρf hρU htrf using hpieces
  have hsub : ∀ i : ℕ, Set.Icc (t i) (t (i + 1)) ⊆ Set.Icc (0 : ℝ) 1 :=
    fun i => Set.Icc_subset_Icc (htmem i).1 (htmem (i + 1)).2
  have hsubu : ∀ i : ℕ, Set.uIcc (t i) (t (i + 1)) ⊆ Set.uIcc (0 : ℝ) 1 := by
    intro i
    rw [Set.uIcc_of_le (htmono i), Set.uIcc_of_le zero_le_one]
    exact hsub i
  have hdata : ∀ i : ℕ,
      AbsolutelyContinuousOnInterval (fun s => (Φg (p s)).re) (t i) (t (i + 1)) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Icc (t i) (t (i + 1)))),
        horizontalDensity q p s = ENNReal.ofReal |(deriv (Φg ∘ p) s).re|) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Icc (t i) (t (i + 1)))),
        deriv (fun s' => (Φg (p s')).re) s = (deriv (Φg ∘ p) s).re) :=
    fun i => piece_data (htmono i) (hΦgd.mono (hρU i))
      (fun z hz => hΦgsq z (hρU i hz)) (hpc.mono (hsub i))
      (hpac.mono (hsubu i)) (htrf i)
  set D : DevChain q p (m + 1 + 1) :=
    ⟨t, fun _ => Φg, fun _ => 1, fun _ => 0, fun i _ => htmono i,
      fun i _ => (hdata i).2.1, fun i _ => (hdata i).1,
      fun i _ => (hdata i).2.2, fun _ => Or.inl rfl,
      fun i _ => by ring⟩ with hDdef
  have hvar := devChain_variation_lb (m + 1) D
  have hDt0 : D.t 0 = 0 := ht0
  have hDtn : D.t (m + 1 + 1) = 1 := htlast (m + 1 + 1) (by omega)
  rw [hDt0, hDtn] at hvar
  have hpull : chainPull D.ε D.c (m + 1) ((D.Φ (m + 1) (p 1)).re) = (Φg (p 1)).re :=
    chainPull_id (m + 1) _
  rw [hpull] at hvar
  exact hvar

/-- **The level-set law of transverse leaves**: a `-q`-trajectory develops in a natural
chart of `q` along a vertical line, with one imaginary orientation. -/
theorem horizontal_level {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {τ : ℝ → ℂ} {I : Set ℝ} (hτ : IsTrajOn (fun w => -q w) τ I)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I)
    (htrack : ∀ t ∈ Set.Icc a b, τ t ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ t ∈ Set.Icc a b,
      Φ (τ t) = Φ (τ a) - Complex.I * ε * ((t - a : ℝ) : ℂ) := by
  set Ψ : ℂ → ℂ := fun w => Complex.I * Φ w with hΨdef
  have hΨd : DifferentiableOn ℂ Ψ S := hΦd.const_mul _
  have hΨsq : ∀ w ∈ S, deriv Ψ w ^ 2 = -(-q w) := by
    intro w hw
    have hΦat : DifferentiableAt ℂ Φ w := hΦd.differentiableAt (hS.mem_nhds hw)
    rw [hΨdef]
    rw [deriv_const_mul _ hΦat, mul_pow, Complex.I_sq, hΦsq w hw]
    ring
  obtain ⟨ε, hε, haff⟩ := traj_ambient_affine hS hΨd hΨsq hτ hab hI htrack
  refine ⟨ε, hε, fun t ht => ?_⟩
  have h1 := haff t ht
  rw [hΨdef] at h1
  have h2 : Complex.I * Φ (τ t)
      = Complex.I * Φ (τ a) + ε * ((t - a : ℝ) : ℂ) := h1
  have h3 : Complex.I * (Complex.I * Φ (τ t))
      = Complex.I * (Complex.I * Φ (τ a) + ε * ((t - a : ℝ) : ℂ)) := by
    rw [h2]
  rw [show Complex.I * (Complex.I * Φ (τ t)) = -Φ (τ t) by
      rw [← mul_assoc, Complex.I_mul_I]; ring,
    show Complex.I * (Complex.I * Φ (τ a) + ε * ((t - a : ℝ) : ℂ))
      = -Φ (τ a) + Complex.I * ε * ((t - a : ℝ) : ℂ) by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I]; ring] at h3
  linear_combination -h3

/-- Along a transverse leaf the developed real part is constant. -/
theorem horizontal_re_const {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {τ : ℝ → ℂ} {I : Set ℝ} (hτ : IsTrajOn (fun w => -q w) τ I)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I)
    (htrack : ∀ t ∈ Set.Icc a b, τ t ∈ S) :
    ∀ t ∈ Set.Icc a b, (Φ (τ t)).re = (Φ (τ a)).re := by
  obtain ⟨ε, hε, haff⟩ := horizontal_level hS hΦd hΦsq hτ hab hI htrack
  intro t ht
  rw [haff t ht, Complex.sub_re]
  have h1 : (Complex.I * ε * ((t - a : ℝ) : ℂ)).re = 0 := by
    rw [mul_assoc, Complex.I_mul_re]
    have : ((ε : ℂ) * ((t - a : ℝ) : ℂ)).im = 0 := by
      rw [← Complex.ofReal_mul]
      exact Complex.ofReal_im _
    rw [this]
    ring
  rw [h1]
  ring

/-- Along a transverse leaf the developed imaginary part moves at unit speed. -/
theorem horizontal_im_advance {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {τ : ℝ → ℂ} {I : Set ℝ} (hτ : IsTrajOn (fun w => -q w) τ I)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ I)
    (htrack : ∀ t ∈ Set.Icc a b, τ t ∈ S) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ t ∈ Set.Icc a b,
      (Φ (τ t)).im = (Φ (τ a)).im - ε * (t - a) := by
  obtain ⟨ε, hε, haff⟩ := horizontal_level hS hΦd hΦsq hτ hab hI htrack
  refine ⟨ε, hε, fun t ht => ?_⟩
  rw [haff t ht, Complex.sub_im]
  have h1 : (Complex.I * ε * ((t - a : ℝ) : ℂ)).im = ε * (t - a) := by
    rw [mul_assoc, Complex.I_mul_im]
    rw [← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  rw [h1]

end RiemannDynamics
