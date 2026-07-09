/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.HolomorphicEquiv
import RiemannDynamics.Uniformization.Perron.BipolarGreen
import RiemannDynamics.Analysis.Winding.GridPrimitives
import RMT4.Main

/-!
# The uniformization trichotomy

Every simply connected domain of the Riemann sphere is biholomorphic to
exactly one of the unit disc, the plane, or the sphere
(`sphere_domain_trichotomy`), and — through a holomorphic embedding into the
sphere — the same holds for every abstract simply connected Riemann surface
(`uniformization_trichotomy`).

The route to the disc case is the Riemann mapping theorem for plane domains:
simple connectivity forces every connected component of the complement to be
unbounded (`unbounded_connectedComponentIn_compl_of_simplyConnectedSpace`),
which yields holomorphic primitives on the domain and hence the hypotheses of
the mapping theorem. The sphere case is Möbius normalization; the plane case
is the complement-of-one-point reading in the finite chart. The three models
are mutually non-biholomorphic: compactness separates `ℂ̂` from the other two,
and Liouville's theorem separates `ℂ` from the disc.

## Main statements

* `sphere_domain_trichotomy` — the trichotomy for domains `U : Opens ℂ̂`;
* `planar_dichotomy` — a simply connected plane domain is biholomorphic to
  the disc or to `ℂ`;
* `uniformization_trichotomy` — the trichotomy for abstract simply connected
  Riemann surfaces, reduced through
  `exists_diffeomorph_opens_sphere_of_simplyConnected`.
-/

open OnePoint Topology TopologicalSpace Metric
open scoped Manifold ContDiff

namespace RiemannDynamics

/-- The open unit disc as a plane domain, the disc model of the trichotomy. -/
def unitDiscOpens : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

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

/-! ## The trichotomy for plane and sphere domains -/

/-- **Planar dichotomy**: a simply connected plane domain is biholomorphic to
the unit disc or to the plane. -/
theorem planar_dichotomy (U : Opens ℂ) (hsc : SimplyConnectedSpace ↥U) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  by_cases hne : (U : Set ℂ) = Set.univ
  · right
    have hU : U = ⊤ := Opens.ext (by simpa using hne)
    subst hU
    exact nonempty_diffeomorph_top ℂ
  · left
    obtain ⟨f, hf, hinj, himg⟩ :=
      exists_riemannMap_of_simplyConnectedSpace U.isOpen hne hsc
    exact nonempty_diffeomorph_of_injOn_differentiableOn U unitDiscOpens f hf hinj himg

/-- **The uniformization trichotomy for sphere domains**: a simply connected
domain of the Riemann sphere is biholomorphic to the unit disc, the plane, or
the whole sphere. -/
theorem sphere_domain_trichotomy (U : Opens ℂ̂) (hsc : SimplyConnectedSpace ↥U) :
    Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
        Nonempty (↥U ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  by_cases huniv : (U : Set ℂ̂) = Set.univ
  · right; right
    have hU : U = ⊤ := Opens.ext (by simpa using huniv)
    subst hU
    exact nonempty_diffeomorph_top ℂ̂
  · -- A point omitted by `U`, to be moved to `∞` by a Möbius transformation.
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ̂, z₀ ∉ (U : Set ℂ̂) := by
      by_contra h
      push Not at h
      exact huniv (Set.eq_univ_of_forall h)
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) ℂ, g • z₀ = (∞ : ℂ̂) := by
      by_cases h0 : z₀ = ((0 : ℂ) : ℂ̂)
      · obtain ⟨g, -, -, hg⟩ := exists_glSMul_eq_zero_one_infty
          (a := ((1 : ℂ) : ℂ̂)) (b := ((2 : ℂ) : ℂ̂)) (c := z₀)
          (by rw [Ne, OnePoint.coe_eq_coe]; norm_num)
          (by rw [h0, Ne, OnePoint.coe_eq_coe]; norm_num)
          (by rw [h0, Ne, OnePoint.coe_eq_coe]; norm_num)
        exact ⟨g, hg⟩
      · by_cases h1 : z₀ = ((1 : ℂ) : ℂ̂)
        · obtain ⟨g, -, -, hg⟩ := exists_glSMul_eq_zero_one_infty
            (a := ((0 : ℂ) : ℂ̂)) (b := ((2 : ℂ) : ℂ̂)) (c := z₀)
            (by rw [Ne, OnePoint.coe_eq_coe]; norm_num)
            (by rw [h1, Ne, OnePoint.coe_eq_coe]; norm_num)
            (by rw [h1, Ne, OnePoint.coe_eq_coe]; norm_num)
          exact ⟨g, hg⟩
        · obtain ⟨g, -, -, hg⟩ := exists_glSMul_eq_zero_one_infty
            (a := ((0 : ℂ) : ℂ̂)) (b := ((1 : ℂ) : ℂ̂)) (c := z₀)
            (by rw [Ne, OnePoint.coe_eq_coe]; norm_num)
            (Ne.symm h0) (Ne.symm h1)
          exact ⟨g, hg⟩
    -- Transport `U` by the Möbius biholomorphism; the image avoids `∞`.
    obtain ⟨e_g, he_g⟩ := exists_glSMul_diffeomorph g
    obtain ⟨V, hVimg, ⟨e₁⟩⟩ := exists_diffeomorph_opens_image e_g U
    have hinfV : (∞ : ℂ̂) ∉ (V : Set ℂ̂) := by
      rw [hVimg, he_g]
      rintro ⟨u, huU, hu⟩
      exact hz₀ (MulAction.injective g (hu.trans hg.symm) ▸ huU)
    -- Read the image in the finite chart and apply the planar dichotomy.
    obtain ⟨W, hWimg, ⟨e₂⟩⟩ := exists_diffeomorph_opens_planar V hinfV
    have hscW : SimplyConnectedSpace ↥W :=
      simplyConnectedSpace_of_homeomorph (e₁.trans e₂).toHomeomorph hsc
    rcases planar_dichotomy W hscW with h | h
    · exact Or.inl (h.map fun f => (e₁.trans e₂).trans f)
    · exact Or.inr (Or.inl (h.map fun f => (e₁.trans e₂).trans f))

/-! ## Separation of the three models -/

/-- Liouville separation: the plane is not biholomorphic to the unit disc. -/
theorem not_nonempty_diffeomorph_complex_unitDisc :
    ¬ Nonempty (ℂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) := by
  rintro ⟨e⟩
  -- The composite `F = Subtype.val ∘ e : ℂ → ℂ` is an entire function.
  have hFsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val ∘ e : ℂ → ℂ) :=
    contMDiff_subtype_val.comp e.contMDiff
  have hFdiff : Differentiable ℂ (Subtype.val ∘ e : ℂ → ℂ) :=
    hFsmooth.contDiff.differentiable (by simp)
  -- Its range lies in the unit ball, hence is bounded.
  have hFbdd : Bornology.IsBounded (Set.range (Subtype.val ∘ e : ℂ → ℂ)) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
      (Set.range_subset_iff.mpr fun z => (e z).2)
  -- Liouville: `F` takes the same value at `0` and `1`, contradicting injectivity.
  have h01 : (e 0 : ℂ) = (e 1 : ℂ) := hFdiff.apply_eq_apply_of_bounded hFbdd 0 1
  exact zero_ne_one (e.toEquiv.injective (Subtype.ext h01))

/-- Compactness separation: the sphere is not biholomorphic to the plane. -/
theorem not_nonempty_diffeomorph_sphere_complex :
    ¬ Nonempty (ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  rintro ⟨e⟩
  have hcs : CompactSpace ℂ := e.toHomeomorph.compactSpace
  exact not_compactSpace_iff.mpr inferInstance hcs

/-- Compactness separation: the sphere is not biholomorphic to the unit
disc. -/
theorem not_nonempty_diffeomorph_sphere_unitDisc :
    ¬ Nonempty (ℂ̂ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) := by
  rintro ⟨e⟩
  have hcs : CompactSpace ↥unitDiscOpens := e.toHomeomorph.compactSpace
  have hc : IsCompact (Metric.ball (0 : ℂ) 1) := isCompact_iff_compactSpace.mpr hcs
  have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.ball (0 : ℂ) 1 :=
    hc.isClosed.closure_eq
  rw [closure_ball (0 : ℂ) one_ne_zero] at hcl
  have h1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hcl] at h1
  simp [Metric.mem_ball, dist_eq_norm] at h1

/-! ## The abstract trichotomy -/

/-- **Planarity of simply connected Riemann surfaces**: every simply
connected one-dimensional complex manifold embeds biholomorphically onto a
domain of the Riemann sphere. -/
theorem exists_diffeomorph_opens_sphere_of_simplyConnected (M : Type*)
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    [T2Space M] [SimplyConnectedSpace M] [SecondCountableTopology M] :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  haveI : ConnectedSpace M := PathConnectedSpace.connectedSpace
  by_cases hcomp : CompactSpace M
  · refine exists_diffeomorph_opens_of_forall_not_hasGreenFunction fun p₀ hp₀ => ?_
    obtain ⟨x, hx, hbdd⟩ := hp₀
    exact not_bddAbove_greenFamily_of_compactSpace p₀ x hx hbdd
  · haveI : NoncompactSpace M := not_compactSpace_iff.mp hcomp
    by_cases hG : ∃ p₀ : M, HasGreenFunction p₀
    · obtain ⟨p₀, hp₀⟩ := hG
      exact exists_diffeomorph_opens_of_hasGreenFunction hp₀
    · push Not at hG
      exact exists_diffeomorph_opens_of_forall_not_hasGreenFunction hG

/-- **The uniformization trichotomy**: every simply connected Riemann surface
is biholomorphic to the unit disc, the plane, or the Riemann sphere. -/
theorem uniformization_trichotomy (M : Type*) [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [T2Space M]
    [SimplyConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) ∨
      Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) ∨
        Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_sphere_of_simplyConnected M
  have hsc : SimplyConnectedSpace ↥U :=
    simplyConnectedSpace_of_homeomorph e.toHomeomorph inferInstance
  rcases sphere_domain_trichotomy U hsc with h | h | h
  · exact Or.inl (h.map fun f => e.trans f)
  · exact Or.inr (Or.inl (h.map fun f => e.trans f))
  · exact Or.inr (Or.inr (h.map fun f => e.trans f))

end RiemannDynamics
