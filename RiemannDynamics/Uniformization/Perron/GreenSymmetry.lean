/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction
import RiemannDynamics.Analysis.Winding.GridPrimitives.Primitives
import RMT4.Main

/-!
# Green's function symmetry: the disc and simply connected surfaces

The explicit Green's function of the unit disc and the symmetry of the Green's
envelope on simply connected hyperbolic surfaces, together with two general
maximum-principle utilities consumed by the covering-space symmetry transfer:
a finitely-punctured maximum principle and the identity theorem for harmonic
functions.

Main results:
* `greenEnvelope_unitDisc_eq` — the Perron Green's envelope of the unit disc
  is the classical Möbius-invariant kernel `-log |(b - a)/(1 - āb)|`;
* `greenEnvelope_comp_diffeomorph` — conformal invariance of the envelope;
* `not_hasGreenFunction_complex` — the plane carries no Green's function;
* `greenEnvelope_symm_of_simplyConnected` — symmetry on simply connected
  hyperbolic surfaces, via the biholomorphism onto a plane domain and the
  Riemann map to the disc;
* `msubharmonic_le_zero_of_finite_punctures` — the puncture-tolerant maximum
  principle with finitely many punctures;
* `MHarmonicOn.eqOn_of_eqOn` — harmonic functions agreeing on a nonempty open
  subset of a connected open set agree on all of it.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-! ## From simple connectivity to holomorphic primitives -/

/-- In a simply connected open plane set, every connected component of the
complement is unbounded: a bounded complementary component would be enclosed
by an essential loop of the domain. -/
theorem unbounded_connectedComponentIn_compl_of_simplyConnectedSpace
    {U : Set ℂ} (hU : IsOpen U) (hsc : SimplyConnectedSpace ↥U) :
    ∀ z ∉ U, ¬Bornology.IsBounded (connectedComponentIn Uᶜ z) := by
  classical
  intro z hzU hbdd
  -- ## Stage 1: an essential grid loop in `U` about `z`.  The bounded
  -- component of `z` in the closed complement has a compact relatively
  -- clopen piece `A` (Šura-Bura in a compact truncation), metrically
  -- separated from the rest of the complement; the grid boundary of the
  -- union of small squares meeting `A` is a loop in `U` with nonzero
  -- winding about `z`.
  obtain ⟨γ, hγcl, hγmem, hγwind⟩ : ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧
      (∀ t : unitInterval, γ t ∈ U) ∧ windingNumber γ z ≠ 0 := by
    set F : Set ℂ := Uᶜ
    have hFclosed : IsClosed F := hU.isClosed_compl
    have hzF : z ∈ F := hzU
    set C : Set ℂ := connectedComponentIn F z
    have hzC : z ∈ C := mem_connectedComponentIn hzF
    have hCsub : C ⊆ F := connectedComponentIn_subset _ _
    obtain ⟨R, hRC⟩ := hbdd.subset_closedBall 0
    set K : Set ℂ := F ∩ Metric.closedBall 0 (R + 1)
    have hKcpt : IsCompact K :=
      (isCompact_closedBall 0 (R + 1)).inter_left hFclosed
    have hCK : C ⊆ K := fun x hx =>
      ⟨hCsub hx, Metric.closedBall_subset_closedBall (by linarith) (hRC hx)⟩
    have hzK : z ∈ K := hCK hzC
    -- the component in the truncation agrees with the component in `F`
    have hCKeq : connectedComponentIn K z = C := by
      apply Set.Subset.antisymm
      · exact connectedComponentIn_mono _ Set.inter_subset_left
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hzC hCK
    -- the boundary shell of the truncation, compact and missed by `C`
    set W : Set ℂ := K \ Metric.ball 0 (R + 1)
    have hCW : C ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxC hxW
      apply hxW.2
      have hx := hRC hxC
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    -- pass to the compact subspace `K`
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    set z' : K := ⟨z, hzK⟩
    have hccinter := connectedComponent_eq_iInter_isClopen z'
    have hWclosed : IsClosed W := hKcpt.isClosed.sdiff Metric.isOpen_ball
    have hW'cpt : IsCompact (Subtype.val ⁻¹' W : Set K) :=
      (hWclosed.preimage continuous_subtype_val).isCompact
    -- the shell misses every point of the component of `z` in `K`
    have hdisj : (Subtype.val ⁻¹' W : Set K) ∩
        (⋂ Z : {Z : Set K // IsClopen Z ∧ z' ∈ Z}, (Z : Set K)) = ∅ := by
      rw [← hccinter]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxW hxcc
      have hximg : (x : ℂ) ∈ connectedComponentIn K z := by
        rw [connectedComponentIn_eq_image hzK]
        exact ⟨x, hxcc, rfl⟩
      rw [hCKeq] at hximg
      have hmem : (x : ℂ) ∈ C ∩ W := ⟨hximg, hxW⟩
      rw [hCW] at hmem
      exact hmem
    -- compactness of the shell extracts a single clopen neighborhood
    obtain ⟨u, hu⟩ := hW'cpt.elim_finite_subfamily_closed
      (fun Z : {Z : Set K // IsClopen Z ∧ z' ∈ Z} => (Z : Set K))
      (fun Z => Z.2.1.isClosed) hdisj
    set A'' : Set K := ⋂ Z ∈ u, (Z : Set K) with hA''def
    have hA''clopen : IsClopen A'' := by
      apply Set.Finite.isClopen_biInter u.finite_toSet
      intro Z _
      exact Z.2.1
    have hzA'' : z' ∈ A'' := by
      rw [hA''def]
      exact Set.mem_biInter fun Z _ => Z.2.2
    -- the piece downstairs: compact, clopen in `F`, containing `z`, off the shell
    set A : Set ℂ := Subtype.val '' A''
    have hA''cpt : IsCompact A'' := hA''clopen.isClosed.isCompact
    have hAcpt : IsCompact A := hA''cpt.image continuous_subtype_val
    have hzA : z ∈ A := ⟨z', hzA'', rfl⟩
    have hAK : A ⊆ K := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have hAF : A ⊆ F := fun x hx => (hAK hx).1
    have hAW : A ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨y, hyA'', rfl⟩ hxW
      have hmem : y ∈ (Subtype.val ⁻¹' W : Set K) ∩ ⋂ Z ∈ u, (Z : Set K) :=
        ⟨hxW, hyA''⟩
      rw [hu] at hmem
      exact hmem
    -- `A` is relatively open in `F`
    obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hA''clopen.isOpen
    have hAeq : A = F ∩ (V ∩ Metric.ball 0 (R + 1)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hyA'', rfl⟩
        refine ⟨y.2.1, ?_, ?_⟩
        · rw [← hVeq] at hyA''
          exact hyA''
        · by_contra hball
          have hmem : (y : ℂ) ∈ A ∩ W := ⟨⟨y, hyA'', rfl⟩, ⟨y.2, hball⟩⟩
          rw [hAW] at hmem
          exact hmem
      · rintro x ⟨hxF, hxV, hxball⟩
        have hxK : x ∈ K := ⟨hxF, Metric.ball_subset_closedBall hxball⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        rw [← hVeq]
        exact hxV
    have hFAclosed : IsClosed (F \ A) := by
      rw [hAeq, Set.diff_self_inter]
      exact hFclosed.sdiff (hVopen.inter Metric.isOpen_ball)
    -- metric separation of the compact clopen piece from the rest
    have hdisjAB : Disjoint A (F \ A) := disjoint_sdiff_self_right
    obtain ⟨ε, hε, hthick⟩ := hdisjAB.exists_thickenings hAcpt hFAclosed
    have hsep : ∀ w ∈ Uᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a := by
      intro w hwF hwA a haA
      by_contra hlt
      push Not at hlt
      have hw₁ : w ∈ Metric.thickening ε A :=
        Metric.mem_thickening_iff.mpr ⟨a, haA, hlt⟩
      have hw₂ : w ∈ Metric.thickening ε (F \ A) :=
        Metric.self_subset_thickening hε _ ⟨hwF, hwA⟩
      exact (Set.disjoint_left.mp hthick hw₁) hw₂
    exact exists_gridLoop_winding_ne_zero hU A ε hε hAcpt hzA hAF hsep
  -- ## Stage 2: simple connectivity null-homotopes the subtype lift of the loop.
  have hγ0z : γ 0 ≠ z := fun heq => hzU (heq ▸ hγmem 0)
  let x₀ : ↥U := ⟨γ 0, hγmem 0⟩
  let pγ : Path x₀ x₀ :=
    { toFun := fun s => ⟨γ s, hγmem s⟩
      continuous_toFun := γ.continuous.subtype_mk hγmem
      source' := rfl
      target' := Subtype.ext hγcl.symm }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic pγ (Path.refl x₀)
  -- ## Stage 3: push the homotopy through `↥U ↪ ℂ` and kill the winding number.
  let Hrel : ContinuousMap.HomotopyRel γ
      (ContinuousMap.const unitInterval (γ 0)) {0, 1} :=
    { toFun := fun q => ((F q : ↥U) : ℂ)
      continuous_toFun := continuous_subtype_val.comp F.continuous
      map_zero_left := fun s => congrArg Subtype.val (F.apply_zero s)
      map_one_left := fun s => congrArg Subtype.val (F.apply_one s)
      prop' := by
        intro t s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact congrArg Subtype.val (Path.Homotopy.source F t)
        · exact (congrArg Subtype.val (Path.Homotopy.target F t)).trans hγcl }
  have havoid : ∀ (t s : unitInterval), Hrel (t, s) ≠ z := by
    intro t s heq
    have heq' : ((F (t, s) : ↥U) : ℂ) = z := heq
    have h1 : ((F (t, s) : ↥U) : ℂ) ∈ U := (F (t, s)).2
    rw [heq'] at h1
    exact hzU h1
  have h0 : windingNumber γ z =
      windingNumber (ContinuousMap.const unitInterval (γ 0)) z :=
    windingNumber_eq_of_homotopicRel hγcl Hrel havoid
  rw [windingNumber_const (γ 0) z hγ0z] at h0
  exact hγwind h0

/-- A simply connected open plane set admits holomorphic primitives for all
holomorphic functions. -/
theorem has_primitives_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    (hsc : SimplyConnectedSpace ↥U) : has_primitives U := by
  exact has_primitives_of_unbounded_components hU
    (unbounded_connectedComponentIn_compl_of_simplyConnectedSpace hU hsc)

/-- **The Riemann mapping theorem** for simply connected plane domains: a
simply connected (hence nonempty and connected) open proper subset of `ℂ`
maps holomorphically and injectively onto the unit disc. -/
theorem exists_riemannMap_of_simplyConnectedSpace {U : Set ℂ} (hU : IsOpen U)
    (hne : U ≠ Set.univ) (hsc : SimplyConnectedSpace ↥U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧
      f '' U = Metric.ball 0 1 := by
  haveI := hsc
  have hUc : IsConnected U := isConnected_iff_connectedSpace.mpr inferInstance
  exact RMT hU hUc hne (has_primitives_of_simplyConnectedSpace hU hsc)

/-- The open unit disc, as an open set of the plane carrying the charted-space
structure of an open submanifold. -/
def discOpens : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- **The Green's function of the unit disc**: the Perron Green's envelope of
the disc equals the classical Möbius-invariant kernel. -/
theorem greenEnvelope_unitDisc_eq {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hab : b ≠ a) :
    greenEnvelope (⟨a, mem_ball_zero_iff.mpr ha⟩ : ↥discOpens)
        ⟨b, mem_ball_zero_iff.mpr hb⟩ =
      -Real.log ‖(b - a) / (1 - (starRingEnd ℂ) a * b)‖ := by
  classical
  set T : ℂ → ℂ := fun z => (z - a) / (1 - (starRingEnd ℂ) a * z) with hT
  set p₀ : ↥discOpens := ⟨a, mem_ball_zero_iff.mpr ha⟩ with hp₀def
  set xb : ↥discOpens := ⟨b, mem_ball_zero_iff.mpr hb⟩ with hxbdef
  -- Points of the disc have norm below one.
  have hmem : ∀ y : ↥discOpens, ‖(↑y : ℂ)‖ < 1 := fun y => mem_ball_zero_iff.mp y.2
  -- Instances on the disc subtype.
  haveI hne : Nonempty ↥discOpens := ⟨p₀⟩
  haveI : ConnectedSpace ↥discOpens :=
    Subtype.connectedSpace ((convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩)
  haveI : NoncompactSpace ↥discOpens := by
    rw [← not_compactSpace_iff]
    intro hcomp
    have hK : IsCompact (ball (0 : ℂ) 1) := by
      rw [isCompact_iff_compactSpace]
      exact hcomp
    have h1 : closedBall (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
      rw [← closure_ball (0 : ℂ) one_ne_zero]
      exact hK.isClosed.closure_eq
    have h2 : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (by norm_num)
    rw [h1, mem_ball_zero_iff] at h2
    norm_num at h2
  -- Denominator estimates for the Möbius kernel.
  have hdenlb : ∀ z : ℂ, ‖z‖ < 1 → 1 - ‖a‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ := by
    intro z hz
    have e2 : ‖(1 : ℂ)‖ - ‖(starRingEnd ℂ) a * z‖ ≤ ‖1 - (starRingEnd ℂ) a * z‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, norm_mul, Complex.norm_conj] at e2
    have e3 : ‖a‖ * ‖z‖ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg a) hz.le
    linarith
  have hden : ∀ z : ℂ, ‖z‖ < 1 → 1 - (starRingEnd ℂ) a * z ≠ 0 := by
    intro z hz hcon
    have h1 := hdenlb z hz
    rw [hcon, norm_zero] at h1
    linarith
  have hdenpos : ∀ z : ℂ, ‖z‖ < 1 → 0 < ‖1 - (starRingEnd ℂ) a * z‖ :=
    fun z hz => norm_pos_iff.mpr (hden z hz)
  have hdenub : ∀ z : ℂ, ‖z‖ < 1 → ‖1 - (starRingEnd ℂ) a * z‖ ≤ 2 := by
    intro z hz
    have e1 : ‖1 - (starRingEnd ℂ) a * z‖ ≤ ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) a * z‖ :=
      norm_sub_le _ _
    rw [norm_one, norm_mul, Complex.norm_conj] at e1
    have e3 : ‖a‖ * ‖z‖ ≤ ‖a‖ := mul_le_of_le_one_right (norm_nonneg a) hz.le
    linarith
  -- The Möbius identity `|1 - āz|² - |z - a|² = (1 - |a|²)(1 - |z|²)`.
  have hkey : ∀ z : ℂ, ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 - ‖z - a‖ ^ 2
      = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    intro z
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    ring
  -- Norm formula, nonvanishing, and the strict disc bound for `T`.
  have hTnorm : ∀ z : ℂ, ‖T z‖ = ‖z - a‖ / ‖1 - (starRingEnd ℂ) a * z‖ := by
    intro z
    rw [hT]
    exact norm_div _ _
  have hTne : ∀ z : ℂ, ‖z‖ < 1 → z ≠ a → T z ≠ 0 := by
    intro z hz hza
    rw [hT]
    exact div_ne_zero (sub_ne_zero_of_ne hza) (hden z hz)
  have hT1 : ∀ z : ℂ, ‖z‖ < 1 → ‖T z‖ < 1 := by
    intro z hz
    have h1 := hkey z
    have h2 := hdenpos z hz
    have hpa : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    have hpz : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h3 : ‖z - a‖ ^ 2 < ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
      nlinarith [mul_pos hpa hpz]
    have h4 : ‖z - a‖ < ‖1 - (starRingEnd ℂ) a * z‖ := by
      nlinarith [norm_nonneg (z - a)]
    rw [hTnorm z, div_lt_one h2]
    exact h4
  have hlogT : ∀ z : ℂ, ‖z‖ < 1 → z ≠ a →
      Real.log ‖T z‖ = Real.log ‖z - a‖ - Real.log ‖1 - (starRingEnd ℂ) a * z‖ := by
    intro z hz hza
    rw [hTnorm z]
    exact Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hza))
      (norm_ne_zero_iff.mpr (hden z hz))
  -- Harmonicity of `log ‖T‖` off the pole, in the plane.
  have hHlog : ∀ z : ℂ, ‖z‖ < 1 → z ≠ a → HarmonicAt (fun w => Real.log ‖T w‖) z := by
    intro z hz hza
    have h1 : AnalyticAt ℂ T z := by
      rw [hT]
      exact AnalyticAt.div (analyticAt_id.sub analyticAt_const)
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (hden z hz)
    exact h1.harmonicAt_log_norm (hTne z hz hza)
  -- Plane harmonicity transfers to the disc subtype through the identity chart.
  have mharmVal : ∀ (G : ℂ → ℝ) (y : ↥discOpens), HarmonicAt G (↑y : ℂ) →
      MHarmonicAt (fun w : ↥discOpens => G ↑w) y := by
    intro G y hG
    have hev : ⇑(chartAt ℂ (↑y : ℂ)).symm =ᶠ[𝓝 (↑y : ℂ)]
        Subtype.val ∘ ⇑(chartAt ℂ y).symm :=
      Opens.chartAt_subtype_val_symm_eventuallyEq discOpens (x := y)
    have hev2 : ((fun w : ↥discOpens => G ↑w) ∘ ⇑(chartAt ℂ y).symm) =ᶠ[𝓝 (↑y : ℂ)] G := by
      filter_upwards [hev] with w hw
      have h2 : (chartAt ℂ (↑y : ℂ)).symm w = w := rfl
      simp only [Function.comp_apply] at hw ⊢
      rw [← hw, h2]
    exact (harmonicAt_congr_nhds hev2).mpr hG
  -- Punctured points have coordinate different from the pole coordinate.
  have hval_ne : ∀ y : ↥discOpens, y ≠ p₀ → (↑y : ℂ) ≠ a := by
    intro y hy hcon
    exact hy (Subtype.ext hcon)
  have hpc : ∀ x : ↥discOpens, poleCoord p₀ x = (↑x : ℂ) - a := fun _ => rfl
  -- ## Upper bound: every member of the family lies below the Möbius kernel.
  have hle_all : ∀ v ∈ greenFamily p₀, v xb ≤ -Real.log ‖T b‖ := by
    intro v hv
    obtain ⟨hsub, -, ⟨K, hKcpt, -, hKv⟩, C, hC⟩ := hv
    have hwsub : MSubharmonicOn (fun y : ↥discOpens => v y + Real.log ‖T ↑y‖) {p₀}ᶜ := by
      intro y hy
      have hyne : (↑y : ℂ) ≠ a := hval_ne y (Set.mem_compl_singleton_iff.mp hy)
      have hH : MHarmonicAt (fun q : ↥discOpens => -Real.log ‖T ↑q‖) y := by
        refine mharmVal (fun z => -Real.log ‖T z‖) y ?_
        exact (hHlog ↑y (hmem y) hyne).neg
      have h1 := (hsub y hy).sub_mharmonicAt hH
      simp only [sub_neg_eq_add] at h1
      exact h1
    have hwsupp : ∃ Kc : Set ↥discOpens, IsCompact Kc ∧
        ∀ x ∉ Kc, (fun y : ↥discOpens => v y + Real.log ‖T ↑y‖) x ≤ 0 := by
      refine ⟨K, hKcpt, fun x hx => ?_⟩
      change v x + Real.log ‖T ↑x‖ ≤ 0
      rw [hKv x hx, zero_add]
      exact Real.log_nonpos (norm_nonneg _) (hT1 ↑x (hmem x)).le
    have hwpole : ∃ C', ∀ᶠ x in 𝓝[≠] p₀,
        (fun y : ↥discOpens => v y + Real.log ‖T ↑y‖) x ≤ C' := by
      refine ⟨C - Real.log (1 - ‖a‖), ?_⟩
      filter_upwards [hC, self_mem_nhdsWithin] with x hx1 hx2
      have hxne : (↑x : ℂ) ≠ a := hval_ne x (Set.mem_compl_singleton_iff.mp hx2)
      change v x + Real.log ‖T ↑x‖ ≤ C - Real.log (1 - ‖a‖)
      rw [hpc x] at hx1
      have h1 := hlogT ↑x (hmem x) hxne
      have h2 : Real.log (1 - ‖a‖) ≤ Real.log ‖1 - (starRingEnd ℂ) a * ↑x‖ :=
        Real.log_le_log (by linarith) (hdenlb ↑x (hmem x))
      linarith
    have hzero := msubharmonic_le_zero_of_puncture hwsub hwsupp hwpole
    have hxbne : xb ≠ p₀ := by
      intro h
      exact hab (congrArg Subtype.val h)
    have h3 : v xb + Real.log ‖T b‖ ≤ 0 := hzero xb hxbne
    linarith
  -- ## The zero function is a family member.
  have hzero_mem : (fun _ : ↥discOpens => (0 : ℝ)) ∈ greenFamily p₀ := by
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, Real.log 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : (↑x : ℂ) ≠ a := hval_ne x (Set.mem_compl_singleton_iff.mp hx)
    change (0 : ℝ) + Real.log ‖poleCoord p₀ x‖ ≤ Real.log 2
    rw [hpc x, zero_add]
    have h1 : 0 < ‖(↑x : ℂ) - a‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hxne)
    have h2 : ‖(↑x : ℂ) - a‖ ≤ 2 := by
      have h3 := norm_sub_le (↑x : ℂ) a
      have h4 := hmem x
      linarith
    exact Real.log_le_log h1 h2
  -- ## The evaluation image is bounded above by the kernel value.
  have hbdd : BddAbove ((fun v => v xb) '' greenFamily p₀) := by
    refine ⟨-Real.log ‖T b‖, ?_⟩
    rintro q ⟨v, hv, rfl⟩
    exact hle_all v hv
  -- ## Lower bound: the truncated kernels are family members.
  have heps_mem : ∀ ε : ℝ, 0 < ε →
      (fun y : ↥discOpens => max (-Real.log ‖T ↑y‖ - ε) 0) ∈ greenFamily p₀ := by
    intro ε hε
    refine ⟨?_, ?_, ?_, Real.log 2, ?_⟩
    · -- Subharmonic off the pole: max of a harmonic function and zero.
      intro y hy
      have hyne : (↑y : ℂ) ≠ a := hval_ne y (Set.mem_compl_singleton_iff.mp hy)
      have hH : MHarmonicAt (fun q : ↥discOpens => -Real.log ‖T ↑q‖ - ε) y := by
        refine mharmVal (fun z => -Real.log ‖T z‖ - ε) y ?_
        exact ((hHlog ↑y (hmem y) hyne).neg).sub (harmonicAt_const ε)
      have h0 : MSubharmonicAt (fun _ : ↥discOpens => (0 : ℝ)) y :=
        mharmonicAt_const.msubharmonicAt
      exact hH.msubharmonicAt.max h0
    · -- Continuity off the pole.
      intro y hy
      have hyne : (↑y : ℂ) ≠ a := hval_ne y (Set.mem_compl_singleton_iff.mp hy)
      have hnum : ContinuousAt T (↑y : ℂ) := by
        rw [hT]
        exact ContinuousAt.div (continuousAt_id.sub continuousAt_const)
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
          (hden ↑y (hmem y))
      have hne0 : ‖T (↑y : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (hTne ↑y (hmem y) hyne)
      have hc1 : ContinuousAt (fun q : ↥discOpens => -Real.log ‖T ↑q‖ - ε) y := by
        have h2 : ContinuousAt (fun q : ↥discOpens => T ↑q) y :=
          hnum.comp continuous_subtype_val.continuousAt
        exact ((h2.norm.log hne0).neg).sub continuousAt_const
      have hc2 : ContinuousAt (fun q : ↥discOpens => max (-Real.log ‖T ↑q‖ - ε) 0) y :=
        hc1.max continuousAt_const
      exact hc2.continuousWithinAt
    · -- Compact support: the closed pseudohyperbolic ball.
      have hr0 : (0 : ℝ) < Real.exp (-ε) := Real.exp_pos _
      have hr1 : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      set S : Set ℂ :=
        {z : ℂ | ‖z - a‖ ≤ Real.exp (-ε) * ‖1 - (starRingEnd ℂ) a * z‖} with hS
      have hSclosed : IsClosed S := by
        rw [hS]
        exact isClosed_le (by fun_prop) (by fun_prop)
      set c0 : ℝ := (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) / (1 + ‖a‖) with hc0
      have hc0pos : 0 < c0 := by
        rw [hc0]
        have h1 : 0 < 1 - Real.exp (-ε) ^ 2 := by nlinarith
        have h2 : 0 < 1 - ‖a‖ := by linarith
        have h3 : 0 < 1 + ‖a‖ := by linarith [norm_nonneg a]
        positivity
      have hc0le : c0 ≤ 1 := by
        rw [hc0, div_le_one (by linarith [norm_nonneg a])]
        nlinarith [norm_nonneg a, hr0]
      have hρnn : (0 : ℝ) ≤ 1 - c0 := by linarith
      have hρ1 : Real.sqrt (1 - c0) < 1 := by
        rw [Real.sqrt_lt' one_pos]
        nlinarith
      have hρ0 : (0 : ℝ) ≤ Real.sqrt (1 - c0) := Real.sqrt_nonneg _
      -- Points of the sublevel set inside the disc stay in a compact sub-disc.
      have hbound : ∀ z : ℂ, ‖z‖ < 1 → z ∈ S → ‖z‖ ≤ Real.sqrt (1 - c0) := by
        intro z hz hzS
        have h1 : ‖z - a‖ ≤ Real.exp (-ε) * ‖1 - (starRingEnd ℂ) a * z‖ := hzS
        have h2 : ‖z - a‖ ^ 2 ≤ Real.exp (-ε) ^ 2 * ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
          nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]
        have h3 := hkey z
        have h4 : (1 - ‖a‖) ^ 2 ≤ ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 := by
          nlinarith [hdenlb z hz, ha]
        have hr2 : 0 ≤ 1 - Real.exp (-ε) ^ 2 := by nlinarith [hr0, hr1]
        have h5a : (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) ^ 2
            ≤ (1 - Real.exp (-ε) ^ 2) * ‖1 - (starRingEnd ℂ) a * z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h4 hr2
        have h5 : (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) ^ 2
            ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
          nlinarith [h5a, h2, h3]
        have h6 : ((1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖)) * (1 - ‖a‖)
            ≤ ((1 + ‖a‖) * (1 - ‖z‖ ^ 2)) * (1 - ‖a‖) := by nlinarith [h5]
        have h7 : (1 - Real.exp (-ε) ^ 2) * (1 - ‖a‖) ≤ (1 + ‖a‖) * (1 - ‖z‖ ^ 2) :=
          le_of_mul_le_mul_right h6 (by linarith)
        have h8 : c0 ≤ 1 - ‖z‖ ^ 2 := by
          rw [hc0, div_le_iff₀ (by linarith [norm_nonneg a])]
          nlinarith [h7]
        have h9 : ‖z‖ ^ 2 ≤ Real.sqrt (1 - c0) ^ 2 := by
          rw [Real.sq_sqrt hρnn]
          linarith
        calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
          _ ≤ Real.sqrt (Real.sqrt (1 - c0) ^ 2) := Real.sqrt_le_sqrt h9
          _ = Real.sqrt (1 - c0) := Real.sqrt_sq hρ0
      have hKcpt : IsCompact (Subtype.val ⁻¹' S : Set ↥discOpens) := by
        rw [Subtype.isCompact_iff]
        have himg2 : Subtype.val '' (Subtype.val ⁻¹' S : Set ↥discOpens)
            = S ∩ closedBall 0 (Real.sqrt (1 - c0)) := by
          ext z
          constructor
          · rintro ⟨y, hyS, rfl⟩
            exact ⟨hyS, mem_closedBall_zero_iff.mpr (hbound ↑y (hmem y) hyS)⟩
          · rintro ⟨hzS, hzB⟩
            refine ⟨⟨z, ?_⟩, hzS, rfl⟩
            exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hzB) hρ1)
        rw [himg2]
        exact (isCompact_closedBall 0 _).inter_left hSclosed
      refine ⟨Subtype.val ⁻¹' S, hKcpt, ?_, ?_⟩
      · intro hcon
        rw [hcon] at hKcpt
        exact NoncompactSpace.noncompact_univ (X := ↥discOpens) hKcpt
      · intro x hx
        have h1 : ¬ ‖(↑x : ℂ) - a‖ ≤ Real.exp (-ε) * ‖1 - (starRingEnd ℂ) a * ↑x‖ := hx
        have h2 : Real.exp (-ε) < ‖T ↑x‖ := by
          rw [hTnorm ↑x, lt_div_iff₀ (hdenpos ↑x (hmem x))]
          exact not_le.mp h1
        have h4 : -ε < Real.log ‖T ↑x‖ := by
          have h5 := Real.log_lt_log hr0 h2
          rwa [Real.log_exp] at h5
        change max (-Real.log ‖T ↑x‖ - ε) 0 = 0
        exact max_eq_right (by linarith)
    · -- Pole bound: near the pole the truncation is dominated by the kernel.
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxne : (↑x : ℂ) ≠ a := hval_ne x (Set.mem_compl_singleton_iff.mp hx)
      change max (-Real.log ‖T ↑x‖ - ε) 0 + Real.log ‖poleCoord p₀ x‖ ≤ Real.log 2
      rw [hpc x]
      have h1 := hlogT ↑x (hmem x) hxne
      have hTle : Real.log ‖T ↑x‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) (hT1 ↑x (hmem x)).le
      have hmax2 : max (-Real.log ‖T ↑x‖ - ε) 0 ≤ -Real.log ‖T ↑x‖ :=
        max_le (by linarith) (by linarith)
      have hlog2 : Real.log ‖1 - (starRingEnd ℂ) a * ↑x‖ ≤ Real.log 2 :=
        Real.log_le_log (hdenpos ↑x (hmem x)) (hdenub ↑x (hmem x))
      linarith
  -- ## Assembly of the supremum.
  have hgoal : -Real.log ‖(b - a) / (1 - (starRingEnd ℂ) a * b)‖ = -Real.log ‖T b‖ := by
    rw [hT]
  rw [hgoal]
  have henv : greenEnvelope p₀ xb = sSup ((fun v => v xb) '' greenFamily p₀) := rfl
  rw [henv]
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨0, ⟨fun _ => 0, hzero_mem, rfl⟩⟩ ?_
    rintro q ⟨v, hv, rfl⟩
    exact hle_all v hv
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    rcases lt_or_ge ε (-Real.log ‖T b‖) with hlt | hge
    · have hmem2 := heps_mem ε hε
      have h1 : (fun y : ↥discOpens => max (-Real.log ‖T ↑y‖ - ε) 0) xb
          ≤ sSup ((fun v => v xb) '' greenFamily p₀) :=
        le_csSup hbdd ⟨_, hmem2, rfl⟩
      have hval : (fun y : ↥discOpens => max (-Real.log ‖T ↑y‖ - ε) 0) xb
          = -Real.log ‖T b‖ - ε := by
        change max (-Real.log ‖T b‖ - ε) 0 = -Real.log ‖T b‖ - ε
        exact max_eq_left (by linarith)
      rw [hval] at h1
      linarith
    · have h0 : (0 : ℝ) ≤ sSup ((fun v => v xb) '' greenFamily p₀) :=
        le_csSup hbdd ⟨fun _ => 0, hzero_mem, rfl⟩
      linarith

/-- **Conformal invariance of the Green's envelope**: a biholomorphism carries
the Perron Green's family at a pole bijectively onto the family at the image
pole, so the envelopes agree. -/
theorem greenEnvelope_comp_diffeomorph {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]
    (e : M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ N) (p₀ x : M) :
    greenEnvelope (e p₀) (e x) = greenEnvelope p₀ x := by
  -- Forward transfer: pulling back a family member along `e` gives a family member.
  have hfwd : ∀ (q : M) (v : N → ℝ), v ∈ greenFamily (e q) → v ∘ ⇑e ∈ greenFamily q := by
    obtain ⟨f, g, hfeq, hgf, hfg, hfc, hgc⟩ :
        ∃ (f : M → N) (g : N → M), f = ⇑e ∧ (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b) ∧
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g :=
      ⟨⇑e, ⇑e.symm, rfl, e.symm_apply_apply, e.apply_symm_apply, e.contMDiff, e.symm.contMDiff⟩
    intro q v hv
    rw [← hfeq] at hv ⊢
    obtain ⟨hsub, hcont, ⟨K, hKc, hKuniv, hKzero⟩, C, hC⟩ := hv
    have hfinj : Function.Injective f := Function.LeftInverse.injective hgf
    have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
        Set.EqOn F G W → SubharmonicOn G W := by
      intro F G U W hF hWU hFG
      refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
      intro a ha ρ hρ hb
      have h1 : G a = F a := (hFG ha).symm
      have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        rw [abs_of_pos hρ] at hz
        exact hFG (hb (sphere_subset_closedBall hz))
      rw [h1, ← h2]
      exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Subharmonicity of the pullback on the punctured surface.
      intro x' hx'
      have hfx' : f x' ∈ ({f q}ᶜ : Set _) :=
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      obtain ⟨s, hs0, -, hsubOn⟩ := hsub (f x') hfx'
      obtain ⟨fH, hfH1, hfH2⟩ : ∃ fH : _ ≃ₜ _, ⇑fH = f ∧ ⇑fH.symm = g :=
        ⟨{ toEquiv := ⟨f, g, hgf, hfg⟩
           continuous_toFun := hfc.continuous
           continuous_invFun := hgc.continuous }, rfl, rfl⟩
      set T := ((chartAt ℂ x').symm ≫ₕ fH.toOpenPartialHomeomorph) ≫ₕ chartAt ℂ (f x') with hT
      have hTcoe : ⇑T = ⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
          hfH1]
      have hTsymmcoe : ⇑T.symm = ⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Function.comp_assoc]
      have hTsrc_iff : ∀ z, z ∈ T.source ↔
          z ∈ (chartAt ℂ x').target ∧ f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source := by
        intro z
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.coe_trans,
          Homeomorph.toOpenPartialHomeomorph_apply, hfH1, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_univ, and_true, Function.comp_apply]
      have hTtgt_iff : ∀ w, w ∈ T.target ↔
          w ∈ (chartAt ℂ (f x')).target ∧
            g ((chartAt ℂ (f x')).symm w) ∈ (chartAt ℂ x').source := by
        intro w
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
          Homeomorph.toOpenPartialHomeomorph_target,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_univ, true_and]
      have hTdiff : DifferentiableOn ℂ (⇑T) T.source := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := (hTsrc_iff z).mp hz
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x').symm) z :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x').open_target.mem_nhds hz1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ x').symm z) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x'))) (f ((chartAt ℂ x').symm z)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ (f x')).open_source.mem_nhds hz2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm)) z :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp z (h2.comp z h1))).analyticAt
        rw [hTcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hTsymmdiff : DifferentiableOn ℂ (⇑T.symm) T.target := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := (hTtgt_iff w).mp hw
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x')).symm) w :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ (f x')).open_target.mem_nhds hw1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f x')).symm w) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x')) (g ((chartAt ℂ (f x')).symm w)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ x').open_source.mem_nhds hw2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm)) w :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp w (h2.comp w h1))).analyticAt
        rw [hTsymmcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hu2 : SubharmonicOn (v ∘ ⇑(chartAt ℂ (f x')).symm)
          (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) :=
        transfer _ _ _ _ hsubOn Set.inter_subset_left fun _ _ => rfl
      have hcomp := subharmonicOn_comp_biholo T hTdiff hTsymmdiff hu2 Set.inter_subset_right
      have hopenS : IsOpen (T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target)) :=
        T.isOpen_inter_preimage (isOpen_ball.inter T.open_target)
      have hz₀src : chartAt ℂ x' x' ∈ T.source := by
        refine (hTsrc_iff _).mpr ⟨mem_chart_target ℂ x', ?_⟩
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
        exact mem_chart_source ℂ (f x')
      have hTz₀ : T (chartAt ℂ x' x') = chartAt ℂ (f x') (f x') := by
        rw [hTcoe]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
      have hz₀mem : chartAt ℂ x' x' ∈
          T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) := by
        refine ⟨hz₀src, ?_⟩
        have h7 : T (chartAt ℂ x' x') ∈ T.target := T.map_source hz₀src
        rw [hTz₀] at h7
        rw [Set.mem_preimage, hTz₀]
        exact ⟨mem_ball_self hs0, h7⟩
      obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hopenS _ hz₀mem
      change ∃ r > 0, ball (chartAt ℂ x' x') r ⊆ (chartAt ℂ x').target ∧
        SubharmonicOn ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) (ball (chartAt ℂ x' x') r)
      refine ⟨r, hr0, ?_, ?_⟩
      · intro z hz
        exact ((hTsrc_iff z).mp (hrsub hz).1).1
      · refine transfer _ _ _ _ hcomp hrsub ?_
        intro z hz
        have hzn : f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source :=
          ((hTsrc_iff z).mp (hrsub hz).1).2
        calc ((v ∘ ⇑(chartAt ℂ (f x')).symm) ∘ ⇑T) z
            = v ((chartAt ℂ (f x')).symm (T z)) := rfl
          _ = v ((chartAt ℂ (f x')).symm (chartAt ℂ (f x') (f ((chartAt ℂ x').symm z)))) := by
              rw [hTcoe]
              simp only [Function.comp_apply]
          _ = ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) z := by
              rw [(chartAt ℂ (f x')).left_inv hzn]
              simp only [Function.comp_apply]
    · -- Continuity of the pullback on the punctured surface.
      exact hcont.comp hfc.continuous.continuousOn fun x' hx' =>
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
    · -- Compact support of the pullback.
      refine ⟨g '' K, hKc.image hgc.continuous, ?_, ?_⟩
      · intro hgKuniv
        obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem K).mp hKuniv
        have hmem : g y ∈ g '' K := by rw [hgKuniv]; exact Set.mem_univ _
        obtain ⟨k, hk, hgk⟩ := hmem
        have hky : k = y := by
          have h := congrArg f hgk
          rwa [hfg, hfg] at h
        exact hy (hky ▸ hk)
      · intro x' hx'
        have hfx' : f x' ∉ K := fun hfK => hx' ⟨f x', hfK, hgf x'⟩
        exact hKzero _ hfx'
    · -- Logarithmic pole bound for the pullback.
      set z₀ := chartAt ℂ q q with hz₀def
      set w₀ := chartAt ℂ (f q) (f q) with hw₀def
      set hfun := ⇑(chartAt ℂ (f q)) ∘ (f ∘ ⇑(chartAt ℂ q).symm) with hfundef
      set ψ := ⇑(chartAt ℂ q) ∘ (g ∘ ⇑(chartAt ℂ (f q)).symm) with hψdef
      have hqz : (chartAt ℂ q).symm z₀ = q := by
        rw [hz₀def]; exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
      have hpz : (chartAt ℂ (f q)).symm w₀ = f q := by
        rw [hw₀def]; exact (chartAt ℂ (f q)).left_inv (mem_chart_source ℂ (f q))
      have hh0 : hfun z₀ = w₀ := by
        rw [hfundef, hw₀def]
        simp only [Function.comp_apply]
        rw [hqz]
      have hfa : AnalyticAt ℂ hfun z₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q).symm) z₀ := by
          rw [hz₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ q).open_target.mem_nhds (mem_chart_target ℂ q))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ q).symm z₀) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q))) (f ((chartAt ℂ q).symm z₀)) := by
          rw [hqz]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ (f q)).open_source.mem_nhds (mem_chart_source ℂ (f q)))
        rw [hfundef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp z₀ (h2.comp z₀ h1))).analyticAt
      have hψa : AnalyticAt ℂ ψ w₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q)).symm) w₀ := by
          rw [hw₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ (f q)).open_target.mem_nhds (mem_chart_target ℂ (f q)))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f q)).symm w₀) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q)) (g ((chartAt ℂ (f q)).symm w₀)) := by
          rw [hpz, hgf]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))
        rw [hψdef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp w₀ (h2.comp w₀ h1))).analyticAt
      have hΩopen : IsOpen ((chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source)) :=
        (chartAt ℂ q).isOpen_inter_preimage_symm
          ((chartAt ℂ (f q)).open_source.preimage hfc.continuous)
      have hz₀Ω : z₀ ∈ (chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source) := by
        refine ⟨?_, ?_⟩
        · rw [hz₀def]; exact mem_chart_target ℂ q
        · rw [Set.mem_preimage, Set.mem_preimage, hqz]
          exact mem_chart_source ℂ (f q)
      have hid : ψ ∘ hfun =ᶠ[𝓝 z₀] id := by
        filter_upwards [hΩopen.mem_nhds hz₀Ω] with z hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [Set.mem_preimage, Set.mem_preimage] at hz2
        rw [hfundef, hψdef]
        simp only [Function.comp_apply, id_eq]
        rw [(chartAt ℂ (f q)).left_inv hz2, hgf, (chartAt ℂ q).right_inv hz1]
      have hfd : DifferentiableAt ℂ hfun z₀ := hfa.differentiableAt
      have hψd : DifferentiableAt ℂ ψ (hfun z₀) := by
        rw [hh0]; exact hψa.differentiableAt
      have hd1 : deriv (ψ ∘ hfun) z₀ = 1 := by
        rw [hid.deriv_eq, deriv_id]
      have hd2 : deriv (ψ ∘ hfun) z₀ = deriv ψ (hfun z₀) * deriv hfun z₀ :=
        deriv_comp z₀ hψd hfd
      have hd0 : deriv hfun z₀ ≠ 0 := by
        intro h0
        rw [hd2, h0, mul_zero] at hd1
        exact zero_ne_one hd1
      have hdpos : 0 < ‖deriv hfun z₀‖ := norm_pos_iff.mpr hd0
      have hhalf : 0 < ‖deriv hfun z₀‖ / 2 := half_pos hdpos
      have hslope : Tendsto (fun z => ‖slope hfun z₀ z‖) (𝓝[≠] z₀) (𝓝 ‖deriv hfun z₀‖) :=
        (hasDerivAt_iff_tendsto_slope.mp hfd.hasDerivAt).norm
      have hev : ∀ᶠ z in 𝓝[≠] z₀, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ z‖ :=
        hslope.eventually_const_lt (half_lt_self hdpos)
      have htends : Tendsto f (𝓝[≠] q) (𝓝[≠] (f q)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hfc.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [eventually_mem_nhdsWithin] with x' hx'
        exact Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      have hct : Tendsto (⇑(chartAt ℂ q)) (𝓝[≠] q) (𝓝[≠] z₀) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · rw [hz₀def]
          exact ((chartAt ℂ q).continuousAt (mem_chart_source ℂ q)).mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
            eventually_mem_nhdsWithin] with x' hx'src hx'ne
          refine Set.mem_compl_singleton_iff.mpr fun hzz => ?_
          rw [hz₀def] at hzz
          exact Set.mem_compl_singleton_iff.mp hx'ne
            ((chartAt ℂ q).injOn hx'src (mem_chart_source ℂ q) hzz)
      have hCk : ∀ᶠ x' in 𝓝[≠] q, v (f x') + Real.log ‖poleCoord (f q) (f x')‖ ≤ C :=
        htends.eventually hC
      have hsl' : ∀ᶠ x' in 𝓝[≠] q, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ (chartAt ℂ q x')‖ :=
        hct.eventually hev
      refine ⟨C - Real.log (‖deriv hfun z₀‖ / 2), ?_⟩
      filter_upwards [hCk, hsl', nhdsWithin_le_nhds
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
        eventually_mem_nhdsWithin] with x' h1 h2 h3 h5
      have hx'q : x' ≠ q := Set.mem_compl_singleton_iff.mp h5
      have hzz : chartAt ℂ q x' ≠ z₀ := by
        intro hzz
        rw [hz₀def] at hzz
        exact hx'q ((chartAt ℂ q).injOn h3 (mem_chart_source ℂ q) hzz)
      have hnp : 0 < ‖chartAt ℂ q x' - z₀‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzz)
      have hval : hfun (chartAt ℂ q x') = chartAt ℂ (f q) (f x') := by
        rw [hfundef]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ q).left_inv h3]
      have hslope_val : ‖slope hfun z₀ (chartAt ℂ q x')‖
          = ‖hfun (chartAt ℂ q x') - w₀‖ / ‖chartAt ℂ q x' - z₀‖ := by
        rw [slope_def_field, hh0, norm_div]
      rw [hslope_val] at h2
      have hprod : ‖deriv hfun z₀‖ / 2 * ‖chartAt ℂ q x' - z₀‖
          < ‖hfun (chartAt ℂ q x') - w₀‖ := (lt_div_iff₀ hnp).mp h2
      have hlog : Real.log (‖deriv hfun z₀‖ / 2) + Real.log ‖chartAt ℂ q x' - z₀‖
          ≤ Real.log ‖hfun (chartAt ℂ q x') - w₀‖ := by
        rw [← Real.log_mul (ne_of_gt hhalf) (ne_of_gt hnp)]
        exact Real.log_le_log (mul_pos hhalf hnp) hprod.le
      have hpole_src : poleCoord q x' = chartAt ℂ q x' - z₀ := by
        rw [hz₀def]
        simp only [poleCoord]
      have hpole_tgt : poleCoord (f q) (f x') = hfun (chartAt ℂ q x') - w₀ := by
        rw [hval, hw₀def]
        simp only [poleCoord]
      rw [hpole_tgt] at h1
      simp only [Function.comp_apply]
      rw [hpole_src]
      linarith
  -- Backward transfer: pulling back along `e.symm`.
  have hbwd : ∀ (q : N) (v : M → ℝ),
      v ∈ greenFamily (e.symm q) → v ∘ ⇑e.symm ∈ greenFamily q := by
    obtain ⟨f, g, hfeq, hgf, hfg, hfc, hgc⟩ :
        ∃ (f : N → M) (g : M → N), f = ⇑e.symm ∧ (∀ a, g (f a) = a) ∧ (∀ b, f (g b) = b) ∧
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g :=
      ⟨⇑e.symm, ⇑e, rfl, e.apply_symm_apply, e.symm_apply_apply, e.symm.contMDiff, e.contMDiff⟩
    intro q v hv
    rw [← hfeq] at hv ⊢
    obtain ⟨hsub, hcont, ⟨K, hKc, hKuniv, hKzero⟩, C, hC⟩ := hv
    have hfinj : Function.Injective f := Function.LeftInverse.injective hgf
    have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
        Set.EqOn F G W → SubharmonicOn G W := by
      intro F G U W hF hWU hFG
      refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
      intro a ha ρ hρ hb
      have h1 : G a = F a := (hFG ha).symm
      have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        rw [abs_of_pos hρ] at hz
        exact hFG (hb (sphere_subset_closedBall hz))
      rw [h1, ← h2]
      exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Subharmonicity of the pullback on the punctured surface.
      intro x' hx'
      have hfx' : f x' ∈ ({f q}ᶜ : Set _) :=
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      obtain ⟨s, hs0, -, hsubOn⟩ := hsub (f x') hfx'
      obtain ⟨fH, hfH1, hfH2⟩ : ∃ fH : _ ≃ₜ _, ⇑fH = f ∧ ⇑fH.symm = g :=
        ⟨{ toEquiv := ⟨f, g, hgf, hfg⟩
           continuous_toFun := hfc.continuous
           continuous_invFun := hgc.continuous }, rfl, rfl⟩
      set T := ((chartAt ℂ x').symm ≫ₕ fH.toOpenPartialHomeomorph) ≫ₕ chartAt ℂ (f x') with hT
      have hTcoe : ⇑T = ⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
          hfH1]
      have hTsymmcoe : ⇑T.symm = ⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm) := by
        rw [hT]
        simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Function.comp_assoc]
      have hTsrc_iff : ∀ z, z ∈ T.source ↔
          z ∈ (chartAt ℂ x').target ∧ f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source := by
        intro z
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
          Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.coe_trans,
          Homeomorph.toOpenPartialHomeomorph_apply, hfH1, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_univ, and_true, Function.comp_apply]
      have hTtgt_iff : ∀ w, w ∈ T.target ↔
          w ∈ (chartAt ℂ (f x')).target ∧
            g ((chartAt ℂ (f x')).symm w) ∈ (chartAt ℂ x').source := by
        intro w
        rw [hT]
        simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
          Homeomorph.toOpenPartialHomeomorph_target,
          Homeomorph.toOpenPartialHomeomorph_symm_apply, hfH2, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_univ, true_and]
      have hTdiff : DifferentiableOn ℂ (⇑T) T.source := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := (hTsrc_iff z).mp hz
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x').symm) z :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x').open_target.mem_nhds hz1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ x').symm z) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x'))) (f ((chartAt ℂ x').symm z)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ (f x')).open_source.mem_nhds hz2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ (f x')) ∘ (f ∘ ⇑(chartAt ℂ x').symm)) z :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp z (h2.comp z h1))).analyticAt
        rw [hTcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hTsymmdiff : DifferentiableOn ℂ (⇑T.symm) T.target := by
        intro w hw
        obtain ⟨hw1, hw2⟩ := (hTtgt_iff w).mp hw
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f x')).symm) w :=
          contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ (f x')).open_target.mem_nhds hw1)
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f x')).symm w) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x')) (g ((chartAt ℂ (f x')).symm w)) :=
          contMDiffOn_chart.contMDiffAt ((chartAt ℂ x').open_source.mem_nhds hw2)
        have h4 : AnalyticAt ℂ (⇑(chartAt ℂ x') ∘ (g ∘ ⇑(chartAt ℂ (f x')).symm)) w :=
          (contMDiffAt_iff_contDiffAt.mp (h3.comp w (h2.comp w h1))).analyticAt
        rw [hTsymmcoe]
        exact h4.differentiableAt.differentiableWithinAt
      have hu2 : SubharmonicOn (v ∘ ⇑(chartAt ℂ (f x')).symm)
          (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) :=
        transfer _ _ _ _ hsubOn Set.inter_subset_left fun _ _ => rfl
      have hcomp := subharmonicOn_comp_biholo T hTdiff hTsymmdiff hu2 Set.inter_subset_right
      have hopenS : IsOpen (T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target)) :=
        T.isOpen_inter_preimage (isOpen_ball.inter T.open_target)
      have hz₀src : chartAt ℂ x' x' ∈ T.source := by
        refine (hTsrc_iff _).mpr ⟨mem_chart_target ℂ x', ?_⟩
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
        exact mem_chart_source ℂ (f x')
      have hTz₀ : T (chartAt ℂ x' x') = chartAt ℂ (f x') (f x') := by
        rw [hTcoe]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x').left_inv (mem_chart_source ℂ x')]
      have hz₀mem : chartAt ℂ x' x' ∈
          T.source ∩ ⇑T ⁻¹' (ball (chartAt ℂ (f x') (f x')) s ∩ T.target) := by
        refine ⟨hz₀src, ?_⟩
        have h7 : T (chartAt ℂ x' x') ∈ T.target := T.map_source hz₀src
        rw [hTz₀] at h7
        rw [Set.mem_preimage, hTz₀]
        exact ⟨mem_ball_self hs0, h7⟩
      obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hopenS _ hz₀mem
      change ∃ r > 0, ball (chartAt ℂ x' x') r ⊆ (chartAt ℂ x').target ∧
        SubharmonicOn ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) (ball (chartAt ℂ x' x') r)
      refine ⟨r, hr0, ?_, ?_⟩
      · intro z hz
        exact ((hTsrc_iff z).mp (hrsub hz).1).1
      · refine transfer _ _ _ _ hcomp hrsub ?_
        intro z hz
        have hzn : f ((chartAt ℂ x').symm z) ∈ (chartAt ℂ (f x')).source :=
          ((hTsrc_iff z).mp (hrsub hz).1).2
        calc ((v ∘ ⇑(chartAt ℂ (f x')).symm) ∘ ⇑T) z
            = v ((chartAt ℂ (f x')).symm (T z)) := rfl
          _ = v ((chartAt ℂ (f x')).symm (chartAt ℂ (f x') (f ((chartAt ℂ x').symm z)))) := by
              rw [hTcoe]
              simp only [Function.comp_apply]
          _ = ((v ∘ f) ∘ ⇑(chartAt ℂ x').symm) z := by
              rw [(chartAt ℂ (f x')).left_inv hzn]
              simp only [Function.comp_apply]
    · -- Continuity of the pullback on the punctured surface.
      exact hcont.comp hfc.continuous.continuousOn fun x' hx' =>
        Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
    · -- Compact support of the pullback.
      refine ⟨g '' K, hKc.image hgc.continuous, ?_, ?_⟩
      · intro hgKuniv
        obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem K).mp hKuniv
        have hmem : g y ∈ g '' K := by rw [hgKuniv]; exact Set.mem_univ _
        obtain ⟨k, hk, hgk⟩ := hmem
        have hky : k = y := by
          have h := congrArg f hgk
          rwa [hfg, hfg] at h
        exact hy (hky ▸ hk)
      · intro x' hx'
        have hfx' : f x' ∉ K := fun hfK => hx' ⟨f x', hfK, hgf x'⟩
        exact hKzero _ hfx'
    · -- Logarithmic pole bound for the pullback.
      set z₀ := chartAt ℂ q q with hz₀def
      set w₀ := chartAt ℂ (f q) (f q) with hw₀def
      set hfun := ⇑(chartAt ℂ (f q)) ∘ (f ∘ ⇑(chartAt ℂ q).symm) with hfundef
      set ψ := ⇑(chartAt ℂ q) ∘ (g ∘ ⇑(chartAt ℂ (f q)).symm) with hψdef
      have hqz : (chartAt ℂ q).symm z₀ = q := by
        rw [hz₀def]; exact (chartAt ℂ q).left_inv (mem_chart_source ℂ q)
      have hpz : (chartAt ℂ (f q)).symm w₀ = f q := by
        rw [hw₀def]; exact (chartAt ℂ (f q)).left_inv (mem_chart_source ℂ (f q))
      have hh0 : hfun z₀ = w₀ := by
        rw [hfundef, hw₀def]
        simp only [Function.comp_apply]
        rw [hqz]
      have hfa : AnalyticAt ℂ hfun z₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q).symm) z₀ := by
          rw [hz₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ q).open_target.mem_nhds (mem_chart_target ℂ q))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f ((chartAt ℂ q).symm z₀) := hfc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q))) (f ((chartAt ℂ q).symm z₀)) := by
          rw [hqz]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ (f q)).open_source.mem_nhds (mem_chart_source ℂ (f q)))
        rw [hfundef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp z₀ (h2.comp z₀ h1))).analyticAt
      have hψa : AnalyticAt ℂ ψ w₀ := by
        have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ (f q)).symm) w₀ := by
          rw [hw₀def]
          exact contMDiffOn_chart_symm.contMDiffAt
            ((chartAt ℂ (f q)).open_target.mem_nhds (mem_chart_target ℂ (f q)))
        have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g ((chartAt ℂ (f q)).symm w₀) := hgc.contMDiffAt
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ q)) (g ((chartAt ℂ (f q)).symm w₀)) := by
          rw [hpz, hgf]
          exact contMDiffOn_chart.contMDiffAt
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q))
        rw [hψdef]
        exact (contMDiffAt_iff_contDiffAt.mp (h3.comp w₀ (h2.comp w₀ h1))).analyticAt
      have hΩopen : IsOpen ((chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source)) :=
        (chartAt ℂ q).isOpen_inter_preimage_symm
          ((chartAt ℂ (f q)).open_source.preimage hfc.continuous)
      have hz₀Ω : z₀ ∈ (chartAt ℂ q).target ∩
          ⇑(chartAt ℂ q).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f q)).source) := by
        refine ⟨?_, ?_⟩
        · rw [hz₀def]; exact mem_chart_target ℂ q
        · rw [Set.mem_preimage, Set.mem_preimage, hqz]
          exact mem_chart_source ℂ (f q)
      have hid : ψ ∘ hfun =ᶠ[𝓝 z₀] id := by
        filter_upwards [hΩopen.mem_nhds hz₀Ω] with z hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [Set.mem_preimage, Set.mem_preimage] at hz2
        rw [hfundef, hψdef]
        simp only [Function.comp_apply, id_eq]
        rw [(chartAt ℂ (f q)).left_inv hz2, hgf, (chartAt ℂ q).right_inv hz1]
      have hfd : DifferentiableAt ℂ hfun z₀ := hfa.differentiableAt
      have hψd : DifferentiableAt ℂ ψ (hfun z₀) := by
        rw [hh0]; exact hψa.differentiableAt
      have hd1 : deriv (ψ ∘ hfun) z₀ = 1 := by
        rw [hid.deriv_eq, deriv_id]
      have hd2 : deriv (ψ ∘ hfun) z₀ = deriv ψ (hfun z₀) * deriv hfun z₀ :=
        deriv_comp z₀ hψd hfd
      have hd0 : deriv hfun z₀ ≠ 0 := by
        intro h0
        rw [hd2, h0, mul_zero] at hd1
        exact zero_ne_one hd1
      have hdpos : 0 < ‖deriv hfun z₀‖ := norm_pos_iff.mpr hd0
      have hhalf : 0 < ‖deriv hfun z₀‖ / 2 := half_pos hdpos
      have hslope : Tendsto (fun z => ‖slope hfun z₀ z‖) (𝓝[≠] z₀) (𝓝 ‖deriv hfun z₀‖) :=
        (hasDerivAt_iff_tendsto_slope.mp hfd.hasDerivAt).norm
      have hev : ∀ᶠ z in 𝓝[≠] z₀, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ z‖ :=
        hslope.eventually_const_lt (half_lt_self hdpos)
      have htends : Tendsto f (𝓝[≠] q) (𝓝[≠] (f q)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hfc.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [eventually_mem_nhdsWithin] with x' hx'
        exact Set.mem_compl_singleton_iff.mpr fun h =>
          Set.mem_compl_singleton_iff.mp hx' (hfinj h)
      have hct : Tendsto (⇑(chartAt ℂ q)) (𝓝[≠] q) (𝓝[≠] z₀) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · rw [hz₀def]
          exact ((chartAt ℂ q).continuousAt (mem_chart_source ℂ q)).mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds
            ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
            eventually_mem_nhdsWithin] with x' hx'src hx'ne
          refine Set.mem_compl_singleton_iff.mpr fun hzz => ?_
          rw [hz₀def] at hzz
          exact Set.mem_compl_singleton_iff.mp hx'ne
            ((chartAt ℂ q).injOn hx'src (mem_chart_source ℂ q) hzz)
      have hCk : ∀ᶠ x' in 𝓝[≠] q, v (f x') + Real.log ‖poleCoord (f q) (f x')‖ ≤ C :=
        htends.eventually hC
      have hsl' : ∀ᶠ x' in 𝓝[≠] q, ‖deriv hfun z₀‖ / 2 < ‖slope hfun z₀ (chartAt ℂ q x')‖ :=
        hct.eventually hev
      refine ⟨C - Real.log (‖deriv hfun z₀‖ / 2), ?_⟩
      filter_upwards [hCk, hsl', nhdsWithin_le_nhds
        ((chartAt ℂ q).open_source.mem_nhds (mem_chart_source ℂ q)),
        eventually_mem_nhdsWithin] with x' h1 h2 h3 h5
      have hx'q : x' ≠ q := Set.mem_compl_singleton_iff.mp h5
      have hzz : chartAt ℂ q x' ≠ z₀ := by
        intro hzz
        rw [hz₀def] at hzz
        exact hx'q ((chartAt ℂ q).injOn h3 (mem_chart_source ℂ q) hzz)
      have hnp : 0 < ‖chartAt ℂ q x' - z₀‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzz)
      have hval : hfun (chartAt ℂ q x') = chartAt ℂ (f q) (f x') := by
        rw [hfundef]
        simp only [Function.comp_apply]
        rw [(chartAt ℂ q).left_inv h3]
      have hslope_val : ‖slope hfun z₀ (chartAt ℂ q x')‖
          = ‖hfun (chartAt ℂ q x') - w₀‖ / ‖chartAt ℂ q x' - z₀‖ := by
        rw [slope_def_field, hh0, norm_div]
      rw [hslope_val] at h2
      have hprod : ‖deriv hfun z₀‖ / 2 * ‖chartAt ℂ q x' - z₀‖
          < ‖hfun (chartAt ℂ q x') - w₀‖ := (lt_div_iff₀ hnp).mp h2
      have hlog : Real.log (‖deriv hfun z₀‖ / 2) + Real.log ‖chartAt ℂ q x' - z₀‖
          ≤ Real.log ‖hfun (chartAt ℂ q x') - w₀‖ := by
        rw [← Real.log_mul (ne_of_gt hhalf) (ne_of_gt hnp)]
        exact Real.log_le_log (mul_pos hhalf hnp) hprod.le
      have hpole_src : poleCoord q x' = chartAt ℂ q x' - z₀ := by
        rw [hz₀def]
        simp only [poleCoord]
      have hpole_tgt : poleCoord (f q) (f x') = hfun (chartAt ℂ q x') - w₀ := by
        rw [hval, hw₀def]
        simp only [poleCoord]
      rw [hpole_tgt] at h1
      simp only [Function.comp_apply]
      rw [hpole_src]
      linarith
  -- The evaluation images coincide, hence the envelopes agree.
  have himg : (fun v : N → ℝ => v (e x)) '' greenFamily (e p₀) =
      (fun w : M → ℝ => w x) '' greenFamily p₀ := by
    apply Set.Subset.antisymm
    · rintro a ⟨v, hv, rfl⟩
      exact ⟨v ∘ ⇑e, hfwd p₀ v hv, rfl⟩
    · rintro a ⟨w, hw, rfl⟩
      have hw' : w ∈ greenFamily (e.symm (e p₀)) := by
        rw [e.symm_apply_apply]; exact hw
      refine ⟨w ∘ ⇑e.symm, hbwd (e p₀) w hw', ?_⟩
      change w (e.symm (e x)) = w x
      rw [e.symm_apply_apply]
  change sSup ((fun v : N → ℝ => v (e x)) '' greenFamily (e p₀)) =
    sSup ((fun w : M → ℝ => w x) '' greenFamily p₀)
  rw [himg]

/-- **The plane carries no Green's function**: the truncated logarithms
`max (log (R/‖z - p₀‖)) 0` are members of the Perron Green's family with
unbounded evaluations. -/
theorem not_hasGreenFunction_complex (p₀ : ℂ) : ¬ HasGreenFunction p₀ := by
  rintro ⟨x, hx, B, hB⟩
  -- The truncation radius, chosen so the family member exceeds the bound at `x`.
  set R : ℝ := Real.exp (B + 1 + Real.log ‖x - p₀‖) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hlogR : Real.log R = B + 1 + Real.log ‖x - p₀‖ := by
    rw [hR]; exact Real.log_exp _
  -- The truncated logarithm.
  set v : ℂ → ℝ := fun z => max (Real.log R - Real.log ‖z - p₀‖) 0 with hv
  -- Charts on the plane are the identity, so the pole coordinate is `z - p₀`.
  have hpole_eq : ∀ y : ℂ, poleCoord p₀ y = y - p₀ := fun y => rfl
  -- The logarithmic kernel is harmonic off the pole.
  have hharm : HarmonicOnNhd (fun z : ℂ => Real.log R - Real.log ‖z - p₀‖) {p₀}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun t : ℂ => t - p₀) z := by
      exact analyticAt_id.sub analyticAt_const
    have hne : z - p₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log R)).sub (hana.harmonicAt_log_norm hne)
  have hvsub : SubharmonicOn v {p₀}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {p₀}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hharm) h0
  -- Restriction of plane subharmonicity to subsets of the punctured plane.
  have hmono : ∀ W : Set ℂ, W ⊆ {p₀}ᶜ → SubharmonicOn v W := by
    intro W hW
    refine ⟨hvsub.1.mono hW, ?_⟩
    intro c hc ρ hρ hb
    exact hvsub.2 c (hW hc) ρ hρ (hb.trans hW)
  -- The member vanishes off the closed ball of radius `R`.
  have hvzero : ∀ z : ℂ, z ∉ closedBall p₀ R → v z = 0 := by
    intro z hz
    have hzr : R < ‖z - p₀‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hz
      exact hz
    have hle : Real.log R ≤ Real.log ‖z - p₀‖ := Real.log_le_log hR0 hzr.le
    simp only [hv]
    exact max_eq_right (by linarith)
  -- Membership in the Perron family.
  have hmem : v ∈ greenFamily p₀ := by
    refine ⟨?_, hvsub.1, ⟨closedBall p₀ R, isCompact_closedBall _ _, ?_, hvzero⟩,
      Real.log R, ?_⟩
    · -- Subharmonicity, read in the identity charts of the plane.
      intro z hz
      have hzp : z ≠ p₀ := Set.mem_compl_singleton_iff.mp hz
      have hr0 : 0 < ‖z - p₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
      have hballsub : ball z ‖z - p₀‖ ⊆ ({p₀}ᶜ : Set ℂ) := by
        intro w hw
        rw [Set.mem_compl_singleton_iff]
        intro hwp
        rw [mem_ball, hwp, dist_eq_norm, norm_sub_rev] at hw
        exact lt_irrefl _ hw
      exact ⟨‖z - p₀‖, hr0, fun w _ => Set.mem_univ w, hmono _ hballsub⟩
    · -- The closed ball is not the whole plane.
      exact (isCompact_closedBall p₀ R).ne_univ
    · -- Logarithmic pole growth with constant `log R`.
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds p₀ hR0),
        eventually_mem_nhdsWithin] with y hy hyp
      have hyne : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hyp
      have hypos : 0 < ‖y - p₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
      have hlt : ‖y - p₀‖ < R := by
        rw [mem_ball, dist_eq_norm] at hy
        exact hy
      have hlog : Real.log ‖y - p₀‖ < Real.log R := Real.log_lt_log hypos hlt
      rw [hpole_eq]
      simp only [hv]
      rw [max_eq_left (by linarith)]
      linarith
  -- The member exceeds the upper bound at the witness point.
  have hvx : v x ≤ B := hB ⟨v, hmem, rfl⟩
  have hgt : B + 1 ≤ v x := by
    have heq : Real.log R - Real.log ‖x - p₀‖ = B + 1 := by
      rw [hlogR]; ring
    calc B + 1 = Real.log R - Real.log ‖x - p₀‖ := heq.symm
      _ ≤ v x := le_max_left _ _
  linarith

/-- **Symmetry of the Green's function on simply connected surfaces**: a
simply connected hyperbolic surface is biholomorphic to a plane domain, the
Riemann map takes the domain to the unit disc, and the disc kernel is
symmetric. -/
theorem greenEnvelope_symm_of_simplyConnected [T2Space M] [ConnectedSpace M]
    [SimplyConnectedSpace M] [NoncompactSpace M] {p q : M}
    (hG : HasGreenFunction p) (hpq : p ≠ q) :
    greenEnvelope p q = greenEnvelope q p := by
  classical
  -- ## The biholomorphism onto a plane domain, from the Green's map.
  obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hG
  have hinj : Function.Injective φ := injective_green_map hG hφ h0 habs
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
  by_cases hne : (U : Set ℂ) = Set.univ
  · -- ## The full-plane case contradicts hyperbolicity.
    exfalso
    have hU : U = ⊤ := Opens.ext (by simpa using hne)
    subst hU
    obtain ⟨etop⟩ := nonempty_diffeomorph_top ℂ
    obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := ⟨e.trans etop⟩
    have hpos := greenEnvelope_pos hG q (Ne.symm hpq)
    have htrans := greenEnvelope_comp_diffeomorph E p q
    have hnb : ¬ BddAbove ((fun v => v (E q)) '' greenFamily (E p)) := fun hb =>
      not_hasGreenFunction_complex (E p)
        ⟨E q, fun h => Ne.symm hpq (E.toEquiv.injective h), hb⟩
    have hzero : greenEnvelope (E p) (E q) = 0 := Real.sSup_of_not_bddAbove hnb
    rw [htrans] at hzero
    linarith
  · -- ## The Riemann map to the disc; transfer and the explicit kernel.
    have hscU : SimplyConnectedSpace ↥U :=
      simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
    obtain ⟨f, hf, hfinj, hfimg⟩ :=
      exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hscU
    obtain ⟨e₂⟩ := nonempty_diffeomorph_of_injOn_differentiableOn U discOpens f hf
      hfinj hfimg
    obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥discOpens) := ⟨e.trans e₂⟩
    have ha : ‖(E p : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E p).2
    have hb : ‖(E q : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E q).2
    have hba : (E q : ℂ) ≠ (E p : ℂ) := fun h =>
      hpq (E.toEquiv.injective (Subtype.ext h)).symm
    have hab : (E p : ℂ) ≠ (E q : ℂ) := hba.symm
    -- The two explicit disc values, with the two poles.
    have key1 : greenEnvelope (E p) (E q) =
        -Real.log ‖((E q : ℂ) - (E p : ℂ)) /
          (1 - (starRingEnd ℂ) (E p : ℂ) * (E q : ℂ))‖ :=
      greenEnvelope_unitDisc_eq ha hb hba
    have key2 : greenEnvelope (E q) (E p) =
        -Real.log ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ :=
      greenEnvelope_unitDisc_eq hb ha hab
    -- Symmetry of the Möbius kernel: conjugate the denominator.
    have hden : ‖(1 : ℂ) - (starRingEnd ℂ) (E p : ℂ) * (E q : ℂ)‖ =
        ‖(1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)‖ := by
      rw [← Complex.norm_conj ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)),
        map_sub, map_one, map_mul, Complex.conj_conj]
      congr 1
      ring
    have hker : ‖((E q : ℂ) - (E p : ℂ)) /
          (1 - (starRingEnd ℂ) (E p : ℂ) * (E q : ℂ))‖ =
        ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ := by
      rw [norm_div, norm_div, norm_sub_rev ((E q : ℂ)) ((E p : ℂ)), hden]
    -- Conformal transfer at both pole/point pairs.
    have t1 : greenEnvelope (E p) (E q) = greenEnvelope p q :=
      greenEnvelope_comp_diffeomorph E p q
    have t2 : greenEnvelope (E q) (E p) = greenEnvelope q p :=
      greenEnvelope_comp_diffeomorph E q p
    rw [← t1, ← t2, key1, key2, hker]

/-- **Pole independence on simply connected surfaces**: a simply connected
hyperbolic surface is hyperbolic at every pole, via the biholomorphism onto a
plane domain and the disc kernel. -/
theorem hasGreenFunction_of_simplyConnected [T2Space M] [ConnectedSpace M]
    [SimplyConnectedSpace M] [NoncompactSpace M] {p q : M}
    (hG : HasGreenFunction p) : HasGreenFunction q := by
  classical
  by_cases hqp : q = p
  · subst hqp
    exact hG
  · -- ## The biholomorphism onto a plane domain, from the Green's map.
    obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hG
    have hinj : Function.Injective φ := injective_green_map hG hφ h0 habs
    obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
    by_cases hne : (U : Set ℂ) = Set.univ
    · -- ## The full-plane case contradicts hyperbolicity.
      exfalso
      have hU : U = ⊤ := Opens.ext (by simpa using hne)
      subst hU
      obtain ⟨etop⟩ := nonempty_diffeomorph_top ℂ
      obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := ⟨e.trans etop⟩
      have hpos := greenEnvelope_pos hG q hqp
      have htrans := greenEnvelope_comp_diffeomorph E p q
      have hnb : ¬ BddAbove ((fun v => v (E q)) '' greenFamily (E p)) := fun hb =>
        not_hasGreenFunction_complex (E p)
          ⟨E q, fun h => hqp (E.toEquiv.injective h), hb⟩
      have hzero : greenEnvelope (E p) (E q) = 0 := Real.sSup_of_not_bddAbove hnb
      rw [htrans] at hzero
      linarith
    · -- ## The disc case: positivity of the kernel forces boundedness.
      have hscU : SimplyConnectedSpace ↥U :=
        simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
      obtain ⟨f, hf, hfinj, hfimg⟩ :=
        exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hscU
      obtain ⟨e₂⟩ := nonempty_diffeomorph_of_injOn_differentiableOn U discOpens f hf
        hfinj hfimg
      obtain ⟨E⟩ : Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥discOpens) := ⟨e.trans e₂⟩
      have ha : ‖(E q : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E q).2
      have hb : ‖(E p : ℂ)‖ < 1 := mem_ball_zero_iff.mp (E p).2
      have hab : (E p : ℂ) ≠ (E q : ℂ) := fun h =>
        hqp (E.toEquiv.injective (Subtype.ext h)).symm
      have hval : greenEnvelope (E q) (E p) =
          -Real.log ‖((E p : ℂ) - (E q : ℂ)) /
            (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ :=
        greenEnvelope_unitDisc_eq ha hb hab
      -- ### Positivity: the pseudohyperbolic distance lies strictly in `(0, 1)`.
      have hnum : (E p : ℂ) - (E q : ℂ) ≠ 0 := sub_ne_zero_of_ne hab
      have hdenne : (1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ) ≠ 0 := by
        intro h
        have h1 : (1 : ℂ) = (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ) := sub_eq_zero.mp h
        have h2 : (1 : ℝ) = ‖(E q : ℂ)‖ * ‖(E p : ℂ)‖ := by
          calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
            _ = ‖(starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)‖ := by rw [← h1]
            _ = ‖(E q : ℂ)‖ * ‖(E p : ℂ)‖ := by rw [norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg ((E q : ℂ)), norm_nonneg ((E p : ℂ))]
      have htpos : 0 < ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ :=
        norm_pos_iff.mpr (div_ne_zero hnum hdenne)
      have htlt : ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.mpr hdenne)]
        have hA2 : Complex.normSq (E q : ℂ) < 1 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg ((E q : ℂ))]
        have hB2 : Complex.normSq (E p : ℂ) < 1 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg ((E p : ℂ))]
        have hkey : Complex.normSq ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)) -
            Complex.normSq ((E p : ℂ) - (E q : ℂ)) =
            (1 - Complex.normSq (E q : ℂ)) * (1 - Complex.normSq (E p : ℂ)) := by
          simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
            Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
          ring
        have hsq : Complex.normSq ((E p : ℂ) - (E q : ℂ)) <
            Complex.normSq ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ)) := by
          nlinarith [hkey, hA2, hB2]
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
        nlinarith [norm_nonneg ((E p : ℂ) - (E q : ℂ)),
          norm_nonneg ((1 : ℂ) - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))]
      have hlog : Real.log ‖((E p : ℂ) - (E q : ℂ)) /
          (1 - (starRingEnd ℂ) (E q : ℂ) * (E p : ℂ))‖ < 0 := Real.log_neg htpos htlt
      have hpos : 0 < greenEnvelope (E q) (E p) := by
        rw [hval]
        linarith
      -- ### From the positive value to boundedness of the family at `p`.
      have htrans : greenEnvelope (E q) (E p) = greenEnvelope q p :=
        greenEnvelope_comp_diffeomorph E q p
      refine ⟨p, Ne.symm hqp, ?_⟩
      by_contra hnb
      have hzero : greenEnvelope q p = 0 := Real.sSup_of_not_bddAbove hnb
      rw [htrans, hzero] at hpos
      exact lt_irrefl 0 hpos

/-- **The finitely-punctured maximum principle**: a subharmonic function on
the complement of a finite set that vanishes off a compact set and is bounded
above near each puncture is nonpositive away from the punctures. -/
theorem msubharmonic_le_zero_of_finite_punctures [ConnectedSpace M]
    [NoncompactSpace M] [T2Space M] {F : Finset M} {v : M → ℝ}
    (hv : MSubharmonicOn v (↑F : Set M)ᶜ)
    (hsupp : ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, v x ≤ 0)
    (hpole : ∀ p ∈ F, ∃ C, ∀ᶠ x in 𝓝[≠] p, v x ≤ C) :
    ∀ x ∉ F, v x ≤ 0 := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  haveI : Infinite M := by
    by_contra hcon
    rw [not_infinite_iff_finite] at hcon
    haveI : CompactSpace M := Finite.compactSpace
    exact NoncompactSpace.noncompact_univ (X := M) isCompact_univ
  obtain ⟨K, hK, hKv⟩ := hsupp
  -- Continuity of `v` off the punctures.
  have hvcont : ∀ y : M, y ∉ (↑F : Set M) → ContinuousAt v y :=
    fun y hy => (hv y hy).continuousAt
  /- ## Connectivity of finite complements, by induction on the puncture set. -/
  have hconnF : ∀ G : Finset M, IsConnected ((↑G : Set M)ᶜ) := by
    intro G
    induction G using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, Set.compl_empty]
      exact isConnected_univ
    | insert p G' hpG' IH =>
      have hG'cl : IsClosed (↑G' : Set M) := G'.finite_toSet.isClosed
      set S : Opens M := ⟨(↑G' : Set M)ᶜ, hG'cl.isOpen_compl⟩ with hSdef
      haveI : ConnectedSpace ↥S := Subtype.connectedSpace IH
      have hpS : p ∈ S := by
        change p ∉ (↑G' : Set M)
        exact fun hcon => hpG' (Finset.mem_coe.mp hcon)
      have hinfc : ((↑G' : Set M)ᶜ).Infinite := G'.finite_toSet.infinite_compl
      obtain ⟨a, haS, b, hbS, hab⟩ := hinfc.nontrivial
      have hnt' : ∃ u w : ↥S, u ≠ w :=
        ⟨⟨a, haS⟩, ⟨b, hbS⟩, fun h => hab (congrArg Subtype.val h)⟩
      have hc := isConnected_compl_singleton_of_connected (M := ↥S) hnt' ⟨p, hpS⟩
      have himgc := hc.image Subtype.val continuous_subtype_val.continuousOn
      have heq : Subtype.val '' ({(⟨p, hpS⟩ : ↥S)}ᶜ : Set ↥S) =
          (↑(insert p G') : Set M)ᶜ := by
        ext w
        constructor
        · rintro ⟨⟨a', ha'⟩, hane, rfl⟩
          intro hw
          rw [Finset.coe_insert, Set.mem_insert_iff] at hw
          rcases hw with hw | hw
          · exact hane (Set.mem_singleton_iff.mpr (Subtype.ext hw))
          · exact ha' hw
        · intro hw
          have hw' : w ∉ insert p G' := hw
          have hwp : w ≠ p := fun h => hw' (h ▸ Finset.mem_insert_self p G')
          have hwG' : w ∉ (↑G' : Set M) :=
            fun h => hw' (Finset.mem_insert_of_mem (Finset.mem_coe.mp h))
          refine ⟨⟨w, hwG'⟩, ?_, rfl⟩
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hwp (congrArg Subtype.val hcon)
      rwa [heq] at himgc
  rcases F.eq_empty_or_nonempty with rfl | hFne
  /- ## No punctures: reduce to the single-puncture principle at an artificial pole. -/
  · intro x _
    obtain ⟨p₀, hp₀⟩ := exists_ne x
    have hv' : MSubharmonicOn v {p₀}ᶜ := fun q _ => hv q (by simp)
    have hpole' : ∃ C, ∀ᶠ y in 𝓝[≠] p₀, v y ≤ C := by
      have hcont : ContinuousAt v p₀ := hvcont p₀ (by simp)
      refine ⟨v p₀ + 1, ?_⟩
      have h1 : ∀ᶠ y in 𝓝 p₀, v y < v p₀ + 1 := hcont.eventually_lt_const (lt_add_one _)
      exact (h1.filter_mono nhdsWithin_le_nhds).mono fun y hy => hy.le
    exact msubharmonic_le_zero_of_puncture hv' ⟨K, hK, hKv⟩ hpole' x hp₀.symm
  /- ## Per-puncture data: pole constants and chart radii avoiding other punctures. -/
  have hpoleC : ∀ p : M, ∃ C : ℝ, p ∈ F → ∀ᶠ x in 𝓝[≠] p, v x ≤ C := by
    intro p
    by_cases hp : p ∈ F
    · obtain ⟨C, hC⟩ := hpole p hp
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose C hC using hpoleC
  -- Images under `(chartAt ℂ p).symm` of subsets of the target, in preimage form.
  have himg : ∀ (p : M) (s : Set ℂ), s ⊆ (chartAt ℂ p).target →
      (chartAt ℂ p).symm '' s = (chartAt ℂ p).source ∩ chartAt ℂ p ⁻¹' s := by
    intro p s hs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(chartAt ℂ p).map_target (hs hz), ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ p).right_inv (hs hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨chartAt ℂ p y, hy2, (chartAt ℂ p).left_inv hy⟩
  -- Chart radii on which the pole bound holds and no other puncture appears.
  have hrad : ∀ p : M, ∃ r : ℝ, 0 < r ∧ (p ∈ F →
      closedBall (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧
      (∀ y ∈ (chartAt ℂ p).source,
        chartAt ℂ p y ∈ closedBall (chartAt ℂ p p) r → y ≠ p → v y ≤ C p) ∧
      ∀ y ∈ (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) r,
        y ∈ (↑F : Set M) → y = p) := by
    intro p
    by_cases hp : p ∈ F
    swap
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
    set e := chartAt ℂ p with he
    have hps : p ∈ e.source := mem_chart_source ℂ p
    set z₀ := e p with hz₀
    have hz₀t : z₀ ∈ e.target := e.map_source hps
    obtain ⟨N, hNnhds, hN⟩ := (eventually_nhdsWithin_iff.mp (hC p hp)).exists_mem
    have hFcl : IsClosed (↑(F.erase p) : Set M) := (F.erase p).finite_toSet.isClosed
    have hpav : p ∈ ((↑(F.erase p) : Set M)ᶜ) := by simp
    have hpre : e.target ∩ e.symm ⁻¹' (N ∩ (↑(F.erase p) : Set M)ᶜ) ∈ 𝓝 z₀ := by
      have h1 : ContinuousAt e.symm z₀ := e.continuousAt_symm hz₀t
      have hsymz₀ : e.symm z₀ = p := e.left_inv hps
      have h2 : N ∩ (↑(F.erase p) : Set M)ᶜ ∈ 𝓝 p :=
        Filter.inter_mem hNnhds (hFcl.isOpen_compl.mem_nhds hpav)
      have h3 : e.symm ⁻¹' (N ∩ (↑(F.erase p) : Set M)ᶜ) ∈ 𝓝 z₀ :=
        h1.preimage_mem_nhds (hsymz₀ ▸ h2)
      exact Filter.inter_mem (e.open_target.mem_nhds hz₀t) h3
    obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall.mem_iff).1 hpre
    refine ⟨r, hr, fun _ => ⟨fun z hz => (hrsub hz).1, ?_, ?_⟩⟩
    · intro y hys hyball hyne
      have h3 : e y ∈ e.symm ⁻¹' (N ∩ (↑(F.erase p) : Set M)ᶜ) := (hrsub hyball).2
      rw [Set.mem_preimage, e.left_inv hys] at h3
      exact hN y h3.1 (Set.mem_compl_singleton_iff.mpr hyne)
    · intro y hy hyF
      obtain ⟨z, hz, rfl⟩ := hy
      have h4 : e.symm z ∈ N ∩ (↑(F.erase p) : Set M)ᶜ := (hrsub hz).2
      by_contra hne
      exact h4.2 (Finset.mem_coe.mpr
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hyF⟩))
  choose r hr0 hrP using hrad
  /- ## The coordinate disks, circles, and their unions. -/
  set D : M → Set M :=
    fun p => (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (r p) with hDdef
  set Γ : M → Set M :=
    fun p => (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (r p) with hΓdef
  have hpD : ∀ p : M, p ∈ D p := by
    intro p
    simp only [hDdef]
    exact ⟨chartAt ℂ p p, mem_closedBall_self (hr0 p).le,
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)⟩
  have hDcomp : ∀ p ∈ (↑F : Set M), IsCompact (D p) := by
    intro p hp
    simp only [hDdef]
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt ℂ p).continuousOn_symm.mono (hrP p (Finset.mem_coe.mp hp)).1)
  have hΓcomp : ∀ p ∈ (↑F : Set M), IsCompact (Γ p) := by
    intro p hp
    simp only [hΓdef]
    exact (isCompact_sphere _ _).image_of_continuousOn
      ((chartAt ℂ p).continuousOn_symm.mono
        (sphere_subset_closedBall.trans (hrP p (Finset.mem_coe.mp hp)).1))
  have hΓmem : ∀ (p : M), ∀ y ∈ (chartAt ℂ p).source,
      dist (chartAt ℂ p y) (chartAt ℂ p p) = r p → y ∈ Γ p := by
    intro p y hys hyd
    simp only [hΓdef]
    exact ⟨chartAt ℂ p y, by rwa [mem_sphere], (chartAt ℂ p).left_inv hys⟩
  -- Circles avoid all punctures.
  have hΓF : ∀ p ∈ (↑F : Set M), ∀ y ∈ Γ p, y ∉ (↑F : Set M) := by
    intro p hp y hyΓ hyF
    obtain ⟨hrtp, -, havoidp⟩ := hrP p (Finset.mem_coe.mp hp)
    have hyD : y ∈ D p := by
      simp only [hDdef]
      simp only [hΓdef] at hyΓ
      exact Set.image_mono sphere_subset_closedBall hyΓ
    have hyp : y = p := havoidp y (by simpa only [hDdef] using hyD) hyF
    simp only [hΓdef] at hyΓ
    obtain ⟨z, hz, hzy⟩ := hyΓ
    rw [mem_sphere] at hz
    have hzt : z ∈ (chartAt ℂ p).target :=
      hrtp (sphere_subset_closedBall (by rwa [mem_sphere]))
    have hzne : z ≠ chartAt ℂ p p := by
      intro hcon
      rw [hcon, dist_self] at hz
      exact (hr0 p).ne hz
    apply hzne
    have h5 := (chartAt ℂ p).right_inv hzt
    rw [hzy, hyp] at h5
    exact h5.symm
  set Dtot : Set M := ⋃ p ∈ (↑F : Set M), D p with hDtotdef
  have hDtotcomp : IsCompact Dtot :=
    F.finite_toSet.isCompact_biUnion fun p hp => hDcomp p hp
  have hDtotcl : IsClosed Dtot := hDtotcomp.isClosed
  set Γtot : Set M := ⋃ p ∈ (↑F : Set M), Γ p with hΓtotdef
  have hΓtotcomp : IsCompact Γtot :=
    F.finite_toSet.isCompact_biUnion fun p hp => hΓcomp p hp
  have hΓtotne : Γtot.Nonempty := by
    obtain ⟨p, hp⟩ := hFne
    have h1 : (Γ p).Nonempty := by
      simp only [hΓdef]
      exact (NormedSpace.sphere_nonempty.2 (hr0 p).le).image _
    obtain ⟨q, hq⟩ := h1
    rw [hΓtotdef]
    exact ⟨q, Set.mem_biUnion (Finset.mem_coe.mpr hp) hq⟩
  have hΓtotF : ∀ y ∈ Γtot, y ∉ (↑F : Set M) := by
    intro y hy
    rw [hΓtotdef] at hy
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
    exact hΓF p hp y hyp
  have hΓtotcont : ContinuousOn v Γtot :=
    fun q hq => (hvcont q (hΓtotF q hq)).continuousWithinAt
  obtain ⟨xΓ, hxΓ, hxΓmax⟩ := hΓtotcomp.exists_isMaxOn hΓtotne hΓtotcont
  set m₁ : ℝ := max (v xΓ) 0 with hm₁
  have hm₁0 : (0 : ℝ) ≤ m₁ := le_max_right _ _
  have hΓle : ∀ y ∈ Γtot, v y ≤ m₁ := fun y hy => (hxΓmax hy).trans (le_max_left _ _)
  /- ## Constancy propagation on a preconnected open set from an interior
  maximum (clopen argument). -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ x ∈ Ω, w x ≤ w xm) → ∀ x ∈ Ω, w x = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {x | x ∈ Ω ∧ w x = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hmax' : ∀ y ∈ Ω, w y ≤ w x := fun y hy => (hmax y hy).trans_eq hxw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hxΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy.trans hxw⟩
    have hto : IsOpen {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hcont : ContinuousAt w x := (hwsub x hxΩ).continuousAt
      filter_upwards [hcont.eventually_ne hxw, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy⟩
    have hsub : Ω ⊆ {x | x ∈ Ω ∧ w x = w xm} ∪ {x | x ∈ Ω ∧ w x ≠ w xm} := by
      intro x hx
      by_cases hxw : w x = w xm
      · exact Or.inl ⟨hx, hxw⟩
      · exact Or.inr ⟨hx, hxw⟩
    have hdisj : Disjoint {x | x ∈ Ω ∧ w x = w xm} {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro x ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun x hx => (hres hx).2
  /- ## Maximum principle on an open set `Ω ≠ univ`: a subharmonic function
  bounded by `m` off a compact set and bounded by `m` (with continuity) at
  every point of `closure Ω \ Ω` is bounded by `m` on `Ω`. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ x ∈ Ω, x ∉ Kc → w x ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ x ∈ Ω, w x ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ x ∈ Ω, w x ≤ w xm := by
      intro x hx
      by_cases hxK : x ∈ Kc
      · exact hxmax ⟨subset_closure hx, hxK⟩
      · exact (hout x hx hxK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun x hx => hwsub x (hCcΩ hx)) (fun x hx => hall x (hCcΩ hx))
    have hfrne : (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    haveI hne : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## A far point outside `K` and all the punctures. -/
  have hfar : ∃ y₀ : M, y₀ ∉ K ∪ (↑F : Set M) := by
    by_contra hcon
    push Not at hcon
    have huniv : K ∪ (↑F : Set M) = Set.univ := Set.eq_univ_of_forall hcon
    have hcomp : IsCompact (K ∪ (↑F : Set M)) := hK.union F.finite_toSet.isCompact
    rw [huniv] at hcomp
    exact NoncompactSpace.noncompact_univ (X := M) hcomp
  /- ## Outer estimate: maximum principle outside the union of disks. -/
  have houterAll : ∀ x ∈ (Dtotᶜ : Set M), v x ≤ m₁ := by
    refine maxPrin Dtotᶜ v m₁ K hDtotcl.isOpen_compl ?_ ?_ hK ?_ ?_
    · intro hcon
      obtain ⟨p, hp⟩ := hFne
      have h5 : p ∈ (Dtotᶜ : Set M) := by rw [hcon]; trivial
      apply h5
      rw [hDtotdef]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hp) (hpD p)
    · intro q hq
      refine hv q ?_
      intro hqF
      apply hq
      rw [hDtotdef]
      exact Set.mem_biUnion hqF (hpD q)
    · exact fun q _ hqK => (hKv q hqK).trans hm₁0
    · rintro y ⟨hycl, hyc⟩
      have hyD : y ∈ Dtot := not_not.1 hyc
      rw [hDtotdef] at hyD
      obtain ⟨p, hpFc, hyDp⟩ := Set.mem_iUnion₂.mp hyD
      obtain ⟨hrtp, -, havoidp⟩ := hrP p (Finset.mem_coe.mp hpFc)
      have hyDp' : y ∈ (chartAt ℂ p).source ∩
          chartAt ℂ p ⁻¹' closedBall (chartAt ℂ p p) (r p) := by
        rw [← himg p _ hrtp]
        simpa only [hDdef] using hyDp
      obtain ⟨hysrc, hyball⟩ := hyDp'
      have hynb : chartAt ℂ p y ∉ ball (chartAt ℂ p p) (r p) := by
        intro hcon
        have hBopen : IsOpen ((chartAt ℂ p).source ∩
            chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) (r p)) :=
          (chartAt ℂ p).continuousOn.isOpen_inter_preimage
            (chartAt ℂ p).open_source isOpen_ball
        have hBsubD : (chartAt ℂ p).source ∩
            chartAt ℂ p ⁻¹' ball (chartAt ℂ p p) (r p) ⊆ Dtot := by
          rw [hDtotdef]
          refine Set.Subset.trans ?_ (Set.subset_biUnion_of_mem hpFc)
          simp only [hDdef]
          rw [himg p _ hrtp]
          exact Set.inter_subset_inter (subset_refl _)
            (Set.preimage_mono ball_subset_closedBall)
        have hyint : y ∈ interior Dtot := interior_maximal hBsubD hBopen ⟨hysrc, hcon⟩
        rw [closure_compl] at hycl
        exact hycl hyint
      have hyr : dist (chartAt ℂ p y) (chartAt ℂ p p) = r p := by
        rw [mem_ball] at hynb
        rw [Set.mem_preimage, mem_closedBall] at hyball
        exact le_antisymm hyball (not_lt.1 hynb)
      have hyneza : chartAt ℂ p y ≠ chartAt ℂ p p := by
        intro hcon
        rw [hcon, dist_self] at hyr
        exact (hr0 p).ne hyr
      have hynep : y ≠ p := by
        intro hcon
        rw [hcon] at hyneza
        exact hyneza rfl
      have hynF : y ∉ (↑F : Set M) := by
        intro hyF
        exact hynep (havoidp y (by simpa only [hDdef] using hyDp) hyF)
      exact ⟨hvcont y hynF,
        hΓle y (by rw [hΓtotdef]; exact Set.mem_biUnion hpFc (hΓmem p y hysrc hyr))⟩
  /- ## Inner estimate: the `ε·log` barrier on each punctured disk. -/
  have hinner : ∀ p ∈ F, ∀ x ∈ D p, x ≠ p → v x ≤ m₁ := by
    intro p hpF x hxD hxp
    obtain ⟨hrtp, hCbp, havoidp⟩ := hrP p hpF
    have hDpcomp : IsCompact (D p) := hDcomp p (Finset.mem_coe.mpr hpF)
    have hDpcl : IsClosed (D p) := hDpcomp.isClosed
    set e := chartAt ℂ p with he
    have hps : p ∈ e.source := mem_chart_source ℂ p
    set z₀ := e p with hz₀
    have hz₀t : z₀ ∈ e.target := e.map_source hps
    have hsymz₀ : e.symm z₀ = p := e.left_inv hps
    have hpid : ∀ y, y ∈ e.source → e y = z₀ → y = p := by
      intro y hys hyz
      rw [← e.left_inv hys, hyz]
      exact hsymz₀
    have hnep : ∀ y, y ∈ e.source → e y ≠ z₀ → y ≠ p := by
      intro y hys hyne hcon
      rw [hcon] at hyne
      exact hyne hz₀.symm
    have himgE : ∀ s : Set ℂ, s ⊆ e.target → e.symm '' s = e.source ∩ e ⁻¹' s := by
      intro s hs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨e.map_target (hs hz), ?_⟩
        rw [Set.mem_preimage, e.right_inv (hs hz)]
        exact hz
      · rintro ⟨hy, hy2⟩
        exact ⟨e y, hy2, e.left_inv hy⟩
    have hDp : D p = e.symm '' closedBall z₀ (r p) := by
      simp only [hDdef]
      rw [← he, ← hz₀]
    rw [hDp, himgE _ hrtp] at hxD
    obtain ⟨hxsrc, hxball⟩ := hxD
    rw [Set.mem_preimage, mem_closedBall] at hxball
    have hxz : e x ≠ z₀ := fun hcon => hxp (hpid x hxsrc hcon)
    have hdx0 : 0 < dist (e x) z₀ := dist_pos.2 hxz
    rcases eq_or_lt_of_le hxball with heqr | hdxlt
    · refine hΓle x ?_
      rw [hΓtotdef]
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpF) (hΓmem p x hxsrc heqr)
    -- Strict interior: show `v x ≤ m₁ + δ` for every `δ > 0`.
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    set L : ℝ := Real.log (r p) - Real.log (dist (e x) z₀) with hLdef
    have hL0 : 0 < L := sub_pos.2 (Real.log_lt_log hdx0 hdxlt)
    set ε : ℝ := δ / L with hεdef
    have hε0 : 0 < ε := div_pos hδ hL0
    have hεL : ε * L = δ := by
      rw [hεdef]
      exact div_mul_cancel₀ δ hL0.ne'
    -- Excision radius `σ`, small enough for the barrier to beat `C p`.
    set Q : ℝ := (m₁ - C p) / ε + Real.log (r p) with hQdef
    set σ : ℝ := min (dist (e x) z₀ / 2) (Real.exp Q) with hσdef
    have hσ0 : 0 < σ := lt_min (half_pos hdx0) (Real.exp_pos Q)
    have hσdx : σ < dist (e x) z₀ :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hdx0)
    have hσr : σ < r p := hσdx.trans hdxlt
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) := Real.log_le_log hσ0 (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hbarrier : C p + ε * (Real.log σ - Real.log (r p)) ≤ m₁ := by
      have h5 : ε * (Real.log σ - Real.log (r p)) ≤ ε * ((m₁ - C p) / ε) := by
        apply mul_le_mul_of_nonneg_left _ hε0.le
        rw [hQdef] at hσQ
        linarith
      have h6 : ε * ((m₁ - C p) / ε) = m₁ - C p := by field_simp
      linarith
    -- The annulus and the barriered competitor.
    set O : Set ℂ := ball z₀ (r p) \ closedBall z₀ σ with hOdef
    have hOopen : IsOpen O := isOpen_ball.sdiff isClosed_closedBall
    have hOsub : O ⊆ e.target := fun z hz => hrtp (ball_subset_closedBall hz.1)
    set A : Set M := e.symm '' O with hAdef
    have hAopen : IsOpen A := by
      rw [hAdef, himgE _ hOsub]
      exact e.continuousOn.isOpen_inter_preimage e.open_source hOopen
    have hAD : A ⊆ D p := by
      rw [hAdef, hDp, himgE _ hOsub, himgE _ hrtp]
      exact Set.inter_subset_inter (subset_refl _)
        (Set.preimage_mono (Set.diff_subset.trans ball_subset_closedBall))
    have hpclA : p ∉ closure A := by
      intro hcon
      have hU : IsOpen (e.source ∩ e ⁻¹' ball z₀ σ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hpU : p ∈ e.source ∩ e ⁻¹' ball z₀ σ := by
        refine ⟨hps, ?_⟩
        rw [Set.mem_preimage, ← hz₀]
        exact mem_ball_self hσ0
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.1 hcon _ hU hpU
      rw [hAdef, himgE _ hOsub] at hq2
      exact hq2.2.2 (ball_subset_closedBall hq1.2)
    have hAne : A ≠ Set.univ := by
      intro hcon
      apply hpclA
      apply subset_closure
      rw [hcon]
      trivial
    set W : M → ℝ := fun q => v q + ε * (Real.log (dist (e q) z₀) - Real.log (r p))
      with hW
    -- Harmonicity of the logarithmic barrier through the chart.
    have hbharm : ∀ y, y ∈ e.source → e y ≠ z₀ →
        MHarmonicAt (fun q => Real.log (dist (e q) z₀)) y := by
      intro y hys hyne
      rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hys]
      have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - z₀‖) (e y) := by
        apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - z₀)
        · exact analyticAt_id.sub analyticAt_const
        · exact sub_ne_zero.2 hyne
      have heqv : (fun w : ℂ => Real.log ‖w - z₀‖) =ᶠ[𝓝 (e y)]
          ((fun q => Real.log (dist (e q) z₀)) ∘ ⇑e.symm) := by
        filter_upwards [e.open_target.mem_nhds (e.map_source hys)] with w hw
        simp only [Function.comp_apply, e.right_inv hw, dist_eq_norm]
      exact (harmonicAt_congr_nhds heqv).1 hharm
    have hbcont : ∀ y, y ∈ e.source → e y ≠ z₀ →
        ContinuousAt (fun q => Real.log (dist (e q) z₀)) y := by
      intro y hys hyne
      have h2 : ContinuousAt e y := e.continuousAt hys
      have h3 : dist (e y) z₀ ≠ 0 := (dist_pos.2 hyne).ne'
      have h4 : ContinuousAt (fun q : M => dist (e q) z₀) y := h2.dist continuousAt_const
      exact h4.log h3
    have mharm_affine : ∀ (g : M → ℝ) (y : M) (a c : ℝ), MHarmonicAt g y →
        MHarmonicAt (fun q => a * g q + c) y := by
      intro g y a c hg
      have h1 : HarmonicAt (g ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hg
      have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
      have heq2 : (a • (g ∘ (chartAt ℂ y).symm) + fun _ => c) =
          (fun q => a * g q + c) ∘ (chartAt ℂ y).symm := by
        funext w
        simp [smul_eq_mul]
      rw [heq2] at h2
      exact h2
    have hWsub : MSubharmonicOn W A := by
      intro q hqA
      rw [hAdef, himgE _ hOsub] at hqA
      obtain ⟨hqs, hqO⟩ := hqA
      have hqz : e q ≠ z₀ := by
        intro hcon
        apply hqO.2
        rw [hcon, mem_closedBall, dist_self]
        exact hσ0.le
      have hqnF : q ∉ (↑F : Set M) := by
        intro hqF
        have hqDp : q ∈ e.symm '' closedBall z₀ (r p) := by
          rw [← hDp]
          exact hAD (by rw [hAdef, himgE _ hOsub]; exact ⟨hqs, hqO⟩)
        exact hnep q hqs hqz (havoidp q hqDp hqF)
      have hu : MHarmonicAt
          (fun y => (-ε) * Real.log (dist (e y) z₀) + ε * Real.log (r p)) q :=
        mharm_affine _ q _ _ (hbharm q hqs hqz)
      have h7 := (hv q hqnF).sub_mharmonicAt hu
      convert h7 using 2
      simp only [hW]
      ring
    have hWfr : ∀ y ∈ closure A \ A, ContinuousAt W y ∧ W y ≤ m₁ := by
      rintro y ⟨hycl, hyA⟩
      have hyDp : y ∈ e.source ∩ e ⁻¹' closedBall z₀ (r p) := by
        rw [← himgE _ hrtp, ← hDp]
        exact closure_minimal hAD hDpcl hycl
      obtain ⟨hysrc, hyball⟩ := hyDp
      rw [Set.mem_preimage, mem_closedBall] at hyball
      have hyneza : e y ≠ z₀ := by
        intro hcon
        exact hpclA (hpid y hysrc hcon ▸ hycl)
      have hynep : y ≠ p := hnep y hysrc hyneza
      have hynF : y ∉ (↑F : Set M) := by
        intro hyF
        apply hynep
        refine havoidp y ?_ hyF
        rw [himgE _ hrtp]
        refine ⟨hysrc, ?_⟩
        rw [Set.mem_preimage, mem_closedBall]
        exact hyball
      have hy0 : 0 < dist (e y) z₀ := dist_pos.2 hyneza
      have hWcont : ContinuousAt W y := by
        rw [hW]
        exact (hvcont y hynF).add
          (continuousAt_const.mul ((hbcont y hysrc hyneza).sub continuousAt_const))
      have hyO : e y ∉ O := by
        intro hcon
        apply hyA
        rw [hAdef, himgE _ hOsub]
        exact ⟨hysrc, hcon⟩
      refine ⟨hWcont, ?_⟩
      by_cases hyb : e y ∈ ball z₀ (r p)
      · -- Inner circle: the barrier beats the pole bound `C p`.
        have hyσ : dist (e y) z₀ ≤ σ := by
          have h8 : e y ∈ closedBall z₀ σ := by
            by_contra h9
            exact hyO ⟨hyb, h9⟩
          rwa [mem_closedBall] at h8
        have hvy : v y ≤ C p := hCbp y hysrc (by rwa [mem_closedBall]) hynep
        have hlogy : Real.log (dist (e y) z₀) ≤ Real.log σ := Real.log_le_log hy0 hyσ
        have h10 : ε * (Real.log (dist (e y) z₀) - Real.log (r p)) ≤
            ε * (Real.log σ - Real.log (r p)) := by
          apply mul_le_mul_of_nonneg_left _ hε0.le
          linarith
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log (r p)) ≤ m₁
        linarith
      · -- Outer circle: the barrier vanishes and the circles bound `v`.
        have hyr : dist (e y) z₀ = r p := by
          rw [mem_ball] at hyb
          exact le_antisymm hyball (not_lt.1 hyb)
        have hvy : v y ≤ m₁ := by
          refine hΓle y ?_
          rw [hΓtotdef]
          exact Set.mem_biUnion (Finset.mem_coe.mpr hpF) (hΓmem p y hysrc hyr)
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log (r p)) ≤ m₁
        rw [hyr, sub_self, mul_zero, add_zero]
        exact hvy
    have hAx : x ∈ A := by
      rw [hAdef, himgE _ hOsub]
      refine ⟨hxsrc, ?_⟩
      rw [Set.mem_preimage]
      refine ⟨by rwa [mem_ball], ?_⟩
      rw [mem_closedBall]
      exact fun hcon => (not_le.mpr hσdx) hcon
    have hWx := maxPrin A W m₁ (D p) hAopen hAne hWsub hDpcomp
      (fun q hq hqD => absurd (hAD hq) hqD) hWfr x hAx
    have hWxval : v x + ε * (Real.log (dist (e x) z₀) - Real.log (r p)) ≤ m₁ := hWx
    have hflip : ε * (Real.log (dist (e x) z₀) - Real.log (r p)) = -(ε * L) := by
      rw [hLdef]
      ring
    rw [hflip, hεL] at hWxval
    linarith
  /- ## Global bound and conclusion. -/
  have hglobal : ∀ x, x ∉ (↑F : Set M) → v x ≤ m₁ := by
    intro x hx
    by_cases hxD : x ∈ Dtot
    · rw [hDtotdef] at hxD
      obtain ⟨p, hpFc, hxDp⟩ := Set.mem_iUnion₂.mp hxD
      have hxp : x ≠ p := by
        intro hcon
        rw [hcon] at hx
        exact hx hpFc
      exact hinner p (Finset.mem_coe.mp hpFc) x hxDp hxp
    · exact houterAll x hxD
  intro x hx
  have hx' : x ∉ (↑F : Set M) := fun h => hx (Finset.mem_coe.mp h)
  rcases le_or_gt (v xΓ) 0 with hcase | hcase
  · have h11 : m₁ = 0 := max_eq_right hcase
    have h12 := hglobal x hx'
    rwa [h11] at h12
  · exfalso
    have hm₁Γ : m₁ = v xΓ := max_eq_left hcase.le
    have hmax : ∀ q ∈ ((↑F : Set M)ᶜ), v q ≤ v xΓ := by
      intro q hq
      have h12 := hglobal q hq
      rwa [hm₁Γ] at h12
    have hFopen : IsOpen ((↑F : Set M)ᶜ) := F.finite_toSet.isClosed.isOpen_compl
    have hxΓF : xΓ ∈ ((↑F : Set M)ᶜ) := hΓtotF xΓ hxΓ
    have hconst := propagate ((↑F : Set M)ᶜ) v xΓ hFopen (hconnF F).isPreconnected
      hxΓF hv hmax
    obtain ⟨y₀, hy₀⟩ := hfar
    have hy₀K : y₀ ∉ K := fun h => hy₀ (Or.inl h)
    have hy₀F : y₀ ∈ ((↑F : Set M)ᶜ) := fun h => hy₀ (Or.inr h)
    have h13 : v y₀ ≤ 0 := hKv y₀ hy₀K
    have h14 : v y₀ = v xΓ := hconst y₀ hy₀F
    linarith

/-- **The identity theorem for harmonic functions**: two functions harmonic on
a connected open set that agree on a nonempty open subset agree everywhere on
the set. -/
theorem MHarmonicOn.eqOn_of_eqOn {u v : M → ℝ} {s t : Set M} (hs : IsOpen s)
    (hsc : IsPreconnected s) (hu : MHarmonicOn u s) (hv : MHarmonicOn v s)
    (ht : IsOpen t) (htne : t.Nonempty) (hts : t ⊆ s) (heq : Set.EqOn u v t) :
    Set.EqOn u v s := by
  -- The set of points of `s` around which `u` and `v` agree.
  set A : Set M := {x | x ∈ s ∧ ∀ᶠ y in 𝓝 x, u y = v y}
  -- `A` is open.
  have hA_open : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxs, hxev⟩
    filter_upwards [hxev.eventually_nhds, hs.mem_nhds hxs] with y hy1 hy2
    exact ⟨hy2, hy1⟩
  -- `A` meets `s` (it contains `t`).
  obtain ⟨x₀, hx₀⟩ := htne
  have hx₀A : x₀ ∈ A := by
    refine ⟨hts hx₀, ?_⟩
    filter_upwards [ht.mem_nhds hx₀] with y hy using heq hy
  -- Limit points of `A` in `s` lie in `A`: analytic continuation through a chart ball.
  have hA_closed : closure A ∩ s ⊆ A := by
    rintro x ⟨hxcl, hxs⟩
    set e := chartAt ℂ x
    -- A chart ball around `e x` whose `e.symm`-image lies in `s`.
    have hopen : IsOpen (e.symm.source ∩ ↑e.symm ⁻¹' (s ∩ e.source)) :=
      e.symm.isOpen_inter_preimage (hs.inter e.open_source)
    have hmem : e x ∈ e.symm.source ∩ ↑e.symm ⁻¹' (s ∩ e.source) := by
      refine ⟨?_, ?_⟩
      · rw [e.symm_source]; exact mem_chart_target ℂ x
      · rw [Set.mem_preimage, e.left_inv (mem_chart_source ℂ x)]
        exact ⟨hxs, mem_chart_source ℂ x⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (e x) hmem
    -- Both chart readings are real-analytic on the ball.
    have hread : ∀ w : M → ℝ, MHarmonicOn w s →
        AnalyticOnNhd ℝ (w ∘ ↑e.symm) (ball (e x) r) := by
      intro w hw z hz
      obtain ⟨hz_tgt, hz_pre⟩ := hball hz
      rw [e.symm_source] at hz_tgt
      rw [Set.mem_preimage] at hz_pre
      have h1 : MHarmonicAt w (e.symm z) := hw _ hz_pre.1
      have h2 : HarmonicAt (w ∘ ↑e.symm) (e (e.symm z)) :=
        (mharmonicAt_iff_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x) hz_pre.2).mp h1
      rw [e.right_inv hz_tgt] at h2
      exact HarmonicAt.analyticAt h2
    -- A point of `A` inside the chart-ball neighbourhood of `x`.
    have hVopen : IsOpen (e.source ∩ ↑e ⁻¹' ball (e x) r) :=
      e.isOpen_inter_preimage isOpen_ball
    have hxV : x ∈ e.source ∩ ↑e ⁻¹' ball (e x) r :=
      ⟨mem_chart_source ℂ x, Set.mem_preimage.mpr (mem_ball_self hr)⟩
    obtain ⟨y, hyV, hyA⟩ := _root_.mem_closure_iff.mp hxcl _ hVopen hxV
    have hy_ball : e y ∈ ball (e x) r := hyV.2
    -- Transfer the eventual agreement at `y` into the chart.
    have hy_ev : (u ∘ ↑e.symm) =ᶠ[𝓝 (e y)] (v ∘ ↑e.symm) :=
      (e.tendsto_symm hyV.1).eventually hyA.2
    -- The identity theorem for real-analytic functions on the ball.
    have h_eqOn : Set.EqOn (u ∘ ↑e.symm) (v ∘ ↑e.symm) (ball (e x) r) :=
      (hread u hu).eqOn_of_preconnected_of_eventuallyEq (hread v hv)
        (convex_ball (e x) r).isPreconnected hy_ball hy_ev
    -- Hence `u = v` near `x`.
    refine ⟨hxs, ?_⟩
    filter_upwards [hVopen.mem_nhds hxV] with p hp
    have hp2 : e p ∈ ball (e x) r := hp.2
    have hp' : (u ∘ ↑e.symm) (e p) = (v ∘ ↑e.symm) (e p) := h_eqOn hp2
    simpa only [Function.comp_apply, e.left_inv hp.1] using hp'
  -- Preconnectedness spreads `A` over all of `s`.
  have hsA : s ⊆ A :=
    hsc.subset_of_closure_inter_subset hA_open ⟨x₀, hts hx₀, hx₀A⟩ hA_closed
  intro x hxs
  exact ((hsA hxs).2).self_of_nhds

end RiemannDynamics
