/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.MappingClassGroup

/-!
# Simple closed curves, multicurves, and Dehn twists

Simple closed curves on a compact Hausdorff surface are injective continuous
maps from `Circle`; injectivity alone gives closed embeddings. A curve is
essential when it is not freely null-homotopic. Unoriented curves are
compared through their images: two curves are isotopic when an ambient
isotopically-trivial homeomorphism carries one image onto the other, which
quotients by reparametrization and orientation reversal at once.

A multicurve is a finite family of disjoint, pairwise non-isotopic essential
simple closed curves. A mapping class is reducible when some representative
preserves a nonempty multicurve up to isotopy and permutation, periodic when
it has finite order, and pseudo-Anosov when it is neither.

The Dehn twist about a curve is supported on an embedded annulus
neighborhood: transport the model twist `(z, t) ↦ (z · exp (2πt), t)` of
`Circle × I` through the annulus embedding and extend by the identity; the
model twist is the identity on both boundary circles, so the extension is
continuous.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval

namespace RiemannDynamics

/-! ## Simple closed curves -/

/-- A simple closed curve on `S`: an injective continuous map from the
circle. -/
structure SimpleClosedCurve (S : Type*) [TopologicalSpace S] where
  /-- The parametrization of the curve. -/
  toFun : C(Circle, S)
  /-- The parametrization is injective. -/
  inj : Function.Injective toFun

noncomputable instance instFunLikeSCC {S : Type*} [TopologicalSpace S] :
    FunLike (SimpleClosedCurve S) Circle S where
  coe c := c.toFun
  coe_injective' c₁ c₂ h := by
    obtain ⟨t₁, i₁⟩ := c₁
    obtain ⟨t₂, i₂⟩ := c₂
    obtain rfl : t₁ = t₂ := DFunLike.coe_injective h
    rfl

/-- The image of a simple closed curve. -/
def SimpleClosedCurve.range {S : Type*} [TopologicalSpace S]
    (c : SimpleClosedCurve S) : Set S :=
  Set.range c.toFun

/-- A simple closed curve on a Hausdorff space is an embedding: a continuous
injection from a compact space. -/
theorem SimpleClosedCurve.isEmbedding {S : Type*} [TopologicalSpace S]
    [T2Space S] (c : SimpleClosedCurve S) : IsEmbedding c.toFun := by
  exact (c.toFun.continuous.isClosedEmbedding c.inj).isEmbedding

/-- The image of a simple closed curve is compact. -/
theorem SimpleClosedCurve.isCompact_range {S : Type*} [TopologicalSpace S]
    (c : SimpleClosedCurve S) : IsCompact c.range := by
  exact _root_.isCompact_range c.toFun.continuous

/-- The image of a simple closed curve in a Hausdorff space is closed. -/
theorem SimpleClosedCurve.isClosed_range {S : Type*} [TopologicalSpace S]
    [T2Space S] (c : SimpleClosedCurve S) : IsClosed c.range := by
  exact c.isCompact_range.isClosed

/-- A simple closed curve is essential when it is not freely null-homotopic:
no homotopy from its parametrization to any constant map exists. -/
def SimpleClosedCurve.IsEssential {S : Type*} [TopologicalSpace S]
    (c : SimpleClosedCurve S) : Prop :=
  ∀ p : S, IsEmpty (c.toFun.Homotopy (ContinuousMap.const Circle p))

/-- In a path-connected space, a null-homotopy to one constant map yields a
null-homotopy to any other, by concatenating with a path homotopy. -/
theorem isEssential_congr_const {S : Type*} [TopologicalSpace S]
    [PathConnectedSpace S] {c : SimpleClosedCurve S} {p q : S}
    (h : IsEmpty (c.toFun.Homotopy (ContinuousMap.const Circle p))) :
    IsEmpty (c.toFun.Homotopy (ContinuousMap.const Circle q)) := by
  constructor
  intro H
  have hK : (ContinuousMap.const Circle q).Homotopy (ContinuousMap.const Circle p) :=
    { toContinuousMap :=
        ⟨fun sz => PathConnectedSpace.somePath q p sz.1,
          (PathConnectedSpace.somePath q p).continuous.comp continuous_fst⟩
      map_zero_left := fun _ => (PathConnectedSpace.somePath q p).source
      map_one_left := fun _ => (PathConnectedSpace.somePath q p).target }
  exact h.false (H.trans hK)

/-- The image of a simple closed curve under a self-homeomorphism. -/
def _root_.Homeomorph.mapSCC {S : Type*} [TopologicalSpace S] (f : S ≃ₜ S)
    (c : SimpleClosedCurve S) : SimpleClosedCurve S :=
  ⟨⟨f ∘ c.toFun, f.continuous.comp c.toFun.continuous⟩, f.injective.comp c.inj⟩

/-- The image of the mapped curve is the image of the curve. -/
theorem range_mapSCC {S : Type*} [TopologicalSpace S] (f : S ≃ₜ S)
    (c : SimpleClosedCurve S) : (f.mapSCC c).range = f '' c.range := by
  exact Set.range_comp ⇑f ⇑c.toFun

/-- Essentiality is preserved by self-homeomorphisms: compose a
null-homotopy with the inverse. -/
theorem SimpleClosedCurve.IsEssential.mapSCC {S : Type*} [TopologicalSpace S]
    {c : SimpleClosedCurve S} (hc : c.IsEssential) (f : S ≃ₜ S) :
    (f.mapSCC c).IsEssential := by
  intro p
  constructor
  intro H
  have H2 := (ContinuousMap.Homotopy.refl f.symm.toCM).comp H
  have e1 : f.symm.toCM.comp (f.mapSCC c).toFun = c.toFun := by
    ext z
    exact f.symm_apply_apply (c.toFun z)
  have e2 : f.symm.toCM.comp (ContinuousMap.const Circle p) =
      ContinuousMap.const Circle (f.symm p) := rfl
  exact (hc (f.symm p)).false (H2.cast e1 e2)

/-! ## Curve isotopy and multicurves -/

/-- Two simple closed curves are isotopic when an ambient isotopically
trivial homeomorphism carries the image of one onto the image of the
other. -/
def SCCIsotopic {S : Type*} [TopologicalSpace S]
    (c₁ c₂ : SimpleClosedCurve S) : Prop :=
  ∃ f : S ≃ₜ S, IsIsotopicToId f ∧ f '' c₁.range = c₂.range

/-- Curve isotopy is an equivalence relation, by the closure formulas for
isotopies. -/
theorem sccIsotopic_equivalence (S : Type*) [TopologicalSpace S]
    [CompactSpace S] [T2Space S] :
    Equivalence (SCCIsotopic (S := S)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine ⟨1, IsIsotopicToId.refl S, ?_⟩
    have hcoe : ⇑(1 : S ≃ₜ S) = id := rfl
    rw [hcoe, Set.image_id]
  · intro c₁ c₂ h
    obtain ⟨f, hf, hi⟩ := h
    refine ⟨f⁻¹, IsIsotopicToId.inv hf, ?_⟩
    have hcoe : ⇑f⁻¹ = ⇑f.symm := rfl
    rw [← hi, hcoe, ← Set.image_comp, Homeomorph.symm_comp_self, Set.image_id]
  · intro c₁ c₂ c₃ h₁ h₂
    obtain ⟨f, hf, hfi⟩ := h₁
    obtain ⟨g, hg, hgi⟩ := h₂
    refine ⟨g * f, IsIsotopicToId.mul hg hf, ?_⟩
    have hcoe : ⇑(g * f) = ⇑g ∘ ⇑f := rfl
    rw [hcoe, Set.image_comp, hfi, hgi]

/-- A multicurve: a finite family of essential, pairwise disjoint, pairwise
non-isotopic simple closed curves. -/
structure Multicurve (S : Type*) [TopologicalSpace S] where
  /-- The number of components. -/
  n : ℕ
  /-- The component curves. -/
  c : Fin n → SimpleClosedCurve S
  /-- Every component is essential. -/
  essential : ∀ i, (c i).IsEssential
  /-- The components are pairwise disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (c i).range (c j).range
  /-- The components are pairwise non-isotopic. -/
  nonisotopic : ∀ i j, i ≠ j → ¬ SCCIsotopic (c i) (c j)

/-- Curve isotopy is preserved by self-homeomorphisms: conjugate the ambient
isotopy. -/
theorem SCCIsotopic.map {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] (f : S ≃ₜ S) {c₁ c₂ : SimpleClosedCurve S}
    (h : SCCIsotopic c₁ c₂) : SCCIsotopic (f.mapSCC c₁) (f.mapSCC c₂) := by
  obtain ⟨k, hk, hki⟩ := h
  have hconj : IsIsotopicToId (f * k * f⁻¹) := by
    obtain ⟨H⟩ := hk
    have hK : Nonempty (HIsotopy (f * (k * f⁻¹)) (f * (Homeomorph.refl S * f⁻¹))) :=
      ⟨(HIsotopy.refl f).mul (H.mul (HIsotopy.refl f⁻¹))⟩
    have h1 : f * ((Homeomorph.refl S : S ≃ₜ S) * f⁻¹) = Homeomorph.refl S := by
      change f * (1 * f⁻¹) = 1
      rw [one_mul, mul_inv_cancel]
    rw [h1] at hK
    rw [mul_assoc]
    exact hK
  refine ⟨f * k * f⁻¹, hconj, ?_⟩
  rw [range_mapSCC, range_mapSCC]
  have hcoe : ⇑(f * k * f⁻¹) = ⇑f ∘ ⇑k ∘ ⇑f.symm := rfl
  rw [hcoe, Set.image_comp, Set.image_comp, ← Set.image_comp ⇑f.symm ⇑f,
    Homeomorph.symm_comp_self, Set.image_id, hki]

/-- An isotopically trivial homeomorphism carries every curve to an isotopic
curve. -/
theorem SCCIsotopic.of_isIsotopicToId {S : Type*} [TopologicalSpace S]
    {f : S ≃ₜ S} (hf : IsIsotopicToId f) (c : SimpleClosedCurve S) :
    SCCIsotopic c (f.mapSCC c) := by
  exact ⟨f, hf, (range_mapSCC f c).symm⟩

/-- Images of distinct components of a multicurve under a self-homeomorphism
remain disjoint. -/
theorem mapMulticurve_disjoint {S : Type*} [TopologicalSpace S] (f : S ≃ₜ S)
    (M : Multicurve S) (i j : Fin M.n) (hij : i ≠ j) :
    Disjoint (f.mapSCC (M.c i)).range (f.mapSCC (M.c j)).range := by
  rw [range_mapSCC, range_mapSCC]
  exact (Set.disjoint_image_iff f.injective).mpr (M.disjoint i j hij)

/-- Images of distinct components of a multicurve under a self-homeomorphism
remain non-isotopic. -/
theorem mapMulticurve_nonisotopic {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] (f : S ≃ₜ S) (M : Multicurve S)
    (i j : Fin M.n) (hij : i ≠ j) :
    ¬ SCCIsotopic (f.mapSCC (M.c i)) (f.mapSCC (M.c j)) := by
  intro hcon
  have hcan : ∀ d : SimpleClosedCurve S, f⁻¹.mapSCC (f.mapSCC d) = d := by
    intro d
    refine DFunLike.ext _ _ fun z => ?_
    exact f.symm_apply_apply (d z)
  have h2 := SCCIsotopic.map f⁻¹ hcon
  simp only [hcan] at h2
  exact M.nonisotopic i j hij h2

/-- The image of a multicurve under a self-homeomorphism. -/
def _root_.Homeomorph.mapMulticurve {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] (f : S ≃ₜ S) (M : Multicurve S) :
    Multicurve S where
  n := M.n
  c i := f.mapSCC (M.c i)
  essential i := (M.essential i).mapSCC f
  disjoint := mapMulticurve_disjoint f M
  nonisotopic := mapMulticurve_nonisotopic f M

/-! ## Reducibility and the Thurston-type predicates -/

/-- A representative homeomorphism is reducible when it preserves a nonempty
multicurve up to isotopy and permutation of components. -/
def IsReducibleRep {S : Type*} [TopologicalSpace S] (f : S ≃ₜ S) : Prop :=
  ∃ M : Multicurve S, 0 < M.n ∧ ∃ perm : Equiv.Perm (Fin M.n),
    ∀ i, SCCIsotopic (f.mapSCC (M.c i)) (M.c (perm i))

/-- Reducibility of representatives is isotopy-invariant. -/
theorem isReducibleRep_congr {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] {f f' : S ≃ₜ S} (h : IsIsotopicToId (f'⁻¹ * f)) :
    IsReducibleRep f ↔ IsReducibleRep f' := by
  have conj : ∀ u v : S ≃ₜ S, IsIsotopicToId v → IsIsotopicToId (u * v * u⁻¹) := by
    intro u v hv
    obtain ⟨H⟩ := hv
    have hK : Nonempty (HIsotopy (u * (v * u⁻¹)) (u * (Homeomorph.refl S * u⁻¹))) :=
      ⟨(HIsotopy.refl u).mul (H.mul (HIsotopy.refl u⁻¹))⟩
    have h1 : u * ((Homeomorph.refl S : S ≃ₜ S) * u⁻¹) = Homeomorph.refl S := by
      change u * (1 * u⁻¹) = 1
      rw [one_mul, mul_inv_cancel]
    rw [h1] at hK
    rw [mul_assoc]
    exact hK
  have key : ∀ u v : S ≃ₜ S, IsIsotopicToId (v⁻¹ * u) →
      IsReducibleRep u → IsReducibleRep v := by
    intro u v hg hu
    obtain ⟨M, hn, perm, hi⟩ := hu
    refine ⟨M, hn, perm, fun i => ?_⟩
    have hw : IsIsotopicToId (v * u⁻¹) := by
      have hcj := conj v (v⁻¹ * u)⁻¹ (IsIsotopicToId.inv hg)
      have he : v * (v⁻¹ * u)⁻¹ * v⁻¹ = v * u⁻¹ := by group
      rwa [he] at hcj
    have huv : SCCIsotopic (u.mapSCC (M.c i)) (v.mapSCC (M.c i)) := by
      refine ⟨v * u⁻¹, hw, ?_⟩
      rw [range_mapSCC, range_mapSCC]
      have hcoe : ⇑(v * u⁻¹) = ⇑v ∘ ⇑u.symm := rfl
      rw [hcoe, Set.image_comp, ← Set.image_comp ⇑u.symm ⇑u, Homeomorph.symm_comp_self,
        Set.image_id]
    exact (sccIsotopic_equivalence S).trans ((sccIsotopic_equivalence S).symm huv) (hi i)
  constructor
  · exact key f f' h
  · refine key f' f ?_
    have h2 := IsIsotopicToId.inv h
    rwa [mul_inv_rev, inv_inv] at h2

/-- A mapping class is reducible when some representative is. -/
def IsReducible {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)]
    (φ : MappingClassGroup S) : Prop :=
  ∃ f : ↥(homeoPlus S), MCG.mk f = φ ∧ IsReducibleRep (f : S ≃ₜ S)

/-- A mapping class is reducible exactly when every representative is. -/
theorem isReducible_iff_forall {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S]
    [Fact (HasOrientedAtlas S)] (φ : MappingClassGroup S) :
    IsReducible φ ↔
      ∀ f : ↥(homeoPlus S), MCG.mk f = φ → IsReducibleRep (f : S ≃ₜ S) := by
  constructor
  · rintro ⟨f, hf, hred⟩ f' hf'
    have hmk : MCG.mk f = MCG.mk f' := hf.trans hf'.symm
    have hiso : IsIsotopicToId ((f' : S ≃ₜ S)⁻¹ * (f : S ≃ₜ S)) :=
      (mcg_mk_eq_iff f f').mp hmk
    exact (isReducibleRep_congr hiso).mp hred
  · intro hall
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective (isotopicallyTrivial S) φ
    exact ⟨f, hf, hall f hf⟩

/-- A mapping class is periodic when it has finite order. -/
def IsPeriodic {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)]
    (φ : MappingClassGroup S) : Prop :=
  ∃ n : ℕ, 0 < n ∧ φ ^ n = 1

/-- A mapping class is pseudo-Anosov when it is neither periodic nor
reducible. -/
def IsPseudoAnosov {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)]
    (φ : MappingClassGroup S) : Prop :=
  ¬ IsPeriodic φ ∧ ¬ IsReducible φ

/-! ## Annulus neighborhoods and Dehn twists -/

/-- An embedded annulus neighborhood of a simple closed curve: an injective
continuous map of `Circle × I` whose middle circle is the curve, whose open
part has open image, and whose range is proper. -/
structure AnnulusNbhd {S : Type*} [TopologicalSpace S]
    (c : SimpleClosedCurve S) where
  /-- The annulus parametrization. -/
  e : C(Circle × I, S)
  /-- The parametrization is injective. -/
  inj : Function.Injective e
  /-- The middle circle of the annulus is the given curve. -/
  core : ∀ z : Circle, e (z, ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩) = c z
  /-- The open part of the annulus has open image. -/
  openInterior : IsOpen (e '' {zt | 0 < (zt.2 : ℝ) ∧ (zt.2 : ℝ) < 1})
  /-- The annulus is not all of the surface. -/
  proper : (Set.range e)ᶜ.Nonempty

/-- Every annulus neighborhood with open middle part contains a shrunken
annulus neighborhood of the same curve avoiding its boundary circles. -/
theorem AnnulusNbhd.shrink {S : Type*} [TopologicalSpace S]
    {c : SimpleClosedCurve S} (A : AnnulusNbhd c)
    (hopen : IsOpen (A.e '' {zt | 1 / 4 < (zt.2 : ℝ) ∧ (zt.2 : ℝ) < 3 / 4})) :
    ∃ A' : AnnulusNbhd c, Set.range A'.e ⊆
      A.e '' {zt | 1 / 4 ≤ (zt.2 : ℝ) ∧ (zt.2 : ℝ) ≤ 3 / 4} := by
  have hrmem : ∀ t : I, (1 + 2 * (t : ℝ)) / 4 ∈ Set.Icc (0 : ℝ) 1 :=
    fun t => ⟨by nlinarith [t.2.1], by nlinarith [t.2.2]⟩
  set r : I → I := fun t => ⟨(1 + 2 * (t : ℝ)) / 4, hrmem t⟩
  have hr_cont : Continuous r := by
    apply Continuous.subtype_mk
    fun_prop
  have hr_inj : Function.Injective r := fun a b hab => by
    have h1 : (1 + 2 * (a : ℝ)) / 4 = (1 + 2 * (b : ℝ)) / 4 := congrArg Subtype.val hab
    exact Subtype.ext (by linarith)
  refine ⟨⟨⟨fun zt => A.e (zt.1, r zt.2),
      A.e.continuous.comp (continuous_fst.prodMk (hr_cont.comp continuous_snd))⟩,
      ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- injectivity
    intro zt₁ zt₂ h
    have h2 : (zt₁.1, r zt₁.2) = (zt₂.1, r zt₂.2) := A.inj h
    injection h2 with h3 h4
    exact Prod.ext h3 (hr_inj h4)
  · -- core circle
    intro z
    change A.e (z, r ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩) = c z
    have hhalf : r ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩
        = ⟨1 / 2, ⟨by norm_num, by norm_num⟩⟩ := by
      apply Subtype.ext
      change (1 + 2 * ((1 : ℝ) / 2)) / 4 = 1 / 2
      norm_num
    rw [hhalf]
    exact A.core z
  · -- open interior
    have himg : (fun zt : Circle × I => A.e (zt.1, r zt.2)) ''
        {zt : Circle × I | 0 < (zt.2 : ℝ) ∧ (zt.2 : ℝ) < 1}
        = A.e '' {zt : Circle × I | 1 / 4 < (zt.2 : ℝ) ∧ (zt.2 : ℝ) < 3 / 4} := by
      apply Set.Subset.antisymm
      · rintro p ⟨⟨z, t⟩, ⟨ht0, ht1⟩, rfl⟩
        have ht0' : (0 : ℝ) < (t : ℝ) := ht0
        have ht1' : (t : ℝ) < 1 := ht1
        refine ⟨(z, r t), ⟨?_, ?_⟩, ?_⟩
        · change 1 / 4 < (1 + 2 * (t : ℝ)) / 4
          linarith
        · change (1 + 2 * (t : ℝ)) / 4 < 3 / 4
          linarith
        · exact rfl
      · rintro p ⟨⟨z, s⟩, ⟨hs0, hs1⟩, rfl⟩
        have hs0' : (1 : ℝ) / 4 < (s : ℝ) := hs0
        have hs1' : (s : ℝ) < 3 / 4 := hs1
        have hu : 2 * (s : ℝ) - 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        refine ⟨(z, ⟨2 * (s : ℝ) - 1 / 2, hu⟩), ⟨?_, ?_⟩, ?_⟩
        · change (0 : ℝ) < 2 * (s : ℝ) - 1 / 2
          linarith
        · change 2 * (s : ℝ) - 1 / 2 < 1
          linarith
        · have hrs : r ⟨2 * (s : ℝ) - 1 / 2, hu⟩ = s := by
            apply Subtype.ext
            change (1 + 2 * (2 * (s : ℝ) - 1 / 2)) / 4 = (s : ℝ)
            ring
          change A.e (z, r ⟨2 * (s : ℝ) - 1 / 2, hu⟩) = A.e (z, s)
          rw [hrs]
    simp only [ContinuousMap.coe_mk]
    rw [himg]
    exact hopen
  · -- properness
    refine ⟨A.e (1, 0), ?_⟩
    rintro ⟨zt, hzt⟩
    have h2 : (zt.1, r zt.2) = ((1 : Circle), (0 : I)) := A.inj hzt
    have h4 : (1 + 2 * ((zt.2 : I) : ℝ)) / 4 = (0 : ℝ) :=
      congrArg Subtype.val (congrArg Prod.snd h2)
    have h5 : (0 : ℝ) ≤ ((zt.2 : I) : ℝ) := zt.2.2.1
    linarith
  · -- range containment
    rintro p ⟨zt, rfl⟩
    have h5 : (0 : ℝ) ≤ ((zt.2 : I) : ℝ) := zt.2.2.1
    have h6 : ((zt.2 : I) : ℝ) ≤ 1 := zt.2.2.2
    refine ⟨(zt.1, r zt.2), ⟨?_, ?_⟩, ?_⟩
    · change 1 / 4 ≤ (1 + 2 * ((zt.2 : I) : ℝ)) / 4
      linarith
    · change (1 + 2 * ((zt.2 : I) : ℝ)) / 4 ≤ 3 / 4
      linarith
    · exact rfl

/-- The model Dehn twist of the annulus `Circle × I`:
`(z, t) ↦ (z · exp (2πt), t)`. -/
noncomputable def twistCore : (Circle × I) ≃ₜ (Circle × I) where
  toFun zt := (zt.1 * Circle.exp (2 * Real.pi * (zt.2 : ℝ)), zt.2)
  invFun zt := (zt.1 * (Circle.exp (2 * Real.pi * (zt.2 : ℝ)))⁻¹, zt.2)
  left_inv zt := Prod.ext (mul_inv_cancel_right _ _) rfl
  right_inv zt := Prod.ext (inv_mul_cancel_right _ _) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The model twist is the identity on both boundary circles, since
`exp 0 = exp 2π = 1` on the circle. -/
theorem twistCore_boundary (zt : Circle × I)
    (h : (zt.2 : ℝ) = 0 ∨ (zt.2 : ℝ) = 1) : twistCore zt = zt := by
  have hexp : Circle.exp (2 * Real.pi * (zt.2 : ℝ)) = 1 := by
    rcases h with h | h
    · rw [h, mul_zero, Circle.exp_zero]
    · rw [h, mul_one, Circle.exp_two_pi]
  change (zt.1 * Circle.exp (2 * Real.pi * (zt.2 : ℝ)), zt.2) = zt
  rw [hexp, mul_one]

/-- The annulus parametrization as a homeomorphism onto its range: a
continuous injection from a compact space into a Hausdorff space. -/
noncomputable def AnnulusNbhd.embHomeomorph {S : Type*} [TopologicalSpace S]
    [T2Space S] {c : SimpleClosedCurve S} (A : AnnulusNbhd c) :
    (Circle × I) ≃ₜ ↑(Set.range A.e) :=
  (A.e.continuous.isClosedEmbedding A.inj).isEmbedding.toHomeomorph

open Classical in
/-- The Dehn twist map about an annulus: transport the model twist through
the annulus embedding and extend by the identity. -/
noncomputable def dehnTwistFun {S : Type*} [TopologicalSpace S] [T2Space S]
    {c : SimpleClosedCurve S} (A : AnnulusNbhd c) : S → S := fun p =>
  if h : p ∈ Set.range A.e then
    (A.embHomeomorph (twistCore (A.embHomeomorph.symm ⟨p, h⟩)) : S)
  else p

open Classical in
/-- The inverse Dehn twist map: transport the inverse model twist. -/
noncomputable def dehnTwistInvFun {S : Type*} [TopologicalSpace S] [T2Space S]
    {c : SimpleClosedCurve S} (A : AnnulusNbhd c) : S → S := fun p =>
  if h : p ∈ Set.range A.e then
    (A.embHomeomorph (twistCore.symm (A.embHomeomorph.symm ⟨p, h⟩)) : S)
  else p

/-- The Dehn twist map is the identity on the boundary circles of its
annulus. -/
theorem dehnTwistFun_boundary {S : Type*} [TopologicalSpace S] [T2Space S]
    {c : SimpleClosedCurve S} (A : AnnulusNbhd c) :
    Set.EqOn (dehnTwistFun A) id (A.e '' (Set.univ ×ˢ ({0, 1} : Set I))) := by
  rintro p ⟨⟨z, t⟩, hzt, rfl⟩
  have ht : t = 0 ∨ t = 1 := by
    have h2 := hzt.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h2
  have htR : ((z, t).2 : ℝ) = 0 ∨ ((z, t).2 : ℝ) = 1 := by
    rcases ht with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have htw : twistCore (z, t) = (z, t) := twistCore_boundary (z, t) htR
  have hmem : A.e (z, t) ∈ Set.range A.e := ⟨(z, t), rfl⟩
  have hEsymm : A.embHomeomorph.symm ⟨A.e (z, t), hmem⟩ = (z, t) := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext rfl
  have hbranch : dehnTwistFun A (A.e (z, t))
      = (A.embHomeomorph (twistCore (A.embHomeomorph.symm ⟨A.e (z, t), hmem⟩)) : S) :=
    dif_pos hmem
  change dehnTwistFun A (A.e (z, t)) = A.e (z, t)
  rw [hbranch, hEsymm, htw]
  exact rfl

/-- The Dehn twist map is continuous: the surface is covered by the closed
annulus and the closure of its complement; the frontier of the annulus lies
in the boundary circles, where both branches are the identity. -/
theorem continuous_dehnTwistFun {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {c : SimpleClosedCurve S}
    (A : AnnulusNbhd c) : Continuous (dehnTwistFun A) := by
  have hcl1 : IsClosed (Set.range A.e) := (isCompact_range A.e.continuous).isClosed
  have hcont1 : ContinuousOn (dehnTwistFun A) (Set.range A.e) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (Set.range A.e).restrict (dehnTwistFun A) = fun q : ↥(Set.range A.e) =>
        (A.embHomeomorph (twistCore (A.embHomeomorph.symm q)) : S) := by
      funext q
      exact dif_pos q.2
    rw [heq]
    exact continuous_subtype_val.comp (A.embHomeomorph.continuous.comp
      (twistCore.continuous.comp A.embHomeomorph.symm.continuous))
  have hbd := dehnTwistFun_boundary A
  have hcont2 : ContinuousOn (dehnTwistFun A) (closure ((Set.range A.e)ᶜ)) := by
    have heq : Set.EqOn (dehnTwistFun A) id (closure ((Set.range A.e)ᶜ)) := by
      intro p hp
      by_cases hmem : p ∈ Set.range A.e
      · obtain ⟨⟨z, t⟩, rfl⟩ := hmem
        have hnotint : A.e (z, t) ∉ interior (Set.range A.e) := by
          have h2 : closure ((Set.range A.e)ᶜ) = (interior (Set.range A.e))ᶜ :=
            closure_compl
          rw [h2] at hp
          exact hp
        have hsub : A.e '' {zt : Circle × I | 0 < (zt.2 : ℝ) ∧ (zt.2 : ℝ) < 1}
            ⊆ interior (Set.range A.e) :=
          interior_maximal (Set.image_subset_range _ _) A.openInterior
        have htno : ¬(0 < (t : ℝ) ∧ (t : ℝ) < 1) := fun hcon =>
          hnotint (hsub ⟨(z, t), hcon, rfl⟩)
        have ht01 : t = 0 ∨ t = 1 := by
          rcases eq_or_lt_of_le t.2.1 with h0 | h0
          · exact Or.inl (Subtype.ext h0.symm)
          · rcases eq_or_lt_of_le t.2.2 with h1 | h1
            · exact Or.inr (Subtype.ext h1)
            · exact absurd ⟨h0, h1⟩ htno
        apply hbd
        refine ⟨(z, t), Set.mk_mem_prod (Set.mem_univ z) ?_, rfl⟩
        rcases ht01 with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ rfl
      · exact dif_neg hmem
    exact ContinuousOn.congr continuousOn_id heq
  have hcover : Set.range A.e ∪ closure ((Set.range A.e)ᶜ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : p ∈ Set.range A.e
    · exact Set.mem_union_left _ hp
    · exact Set.mem_union_right _ (subset_closure hp)
  have hu := hcont1.union_of_isClosed hcont2 hcl1 isClosed_closure
  rw [hcover] at hu
  exact continuousOn_univ.mp hu

/-- The inverse Dehn twist map undoes the Dehn twist map. -/
theorem dehnTwist_leftInverse {S : Type*} [TopologicalSpace S] [T2Space S]
    {c : SimpleClosedCurve S} (A : AnnulusNbhd c) :
    Function.LeftInverse (dehnTwistInvFun A) (dehnTwistFun A) := by
  intro p
  by_cases hmem : p ∈ Set.range A.e
  · have hbr1 : dehnTwistFun A p
        = (A.embHomeomorph (twistCore (A.embHomeomorph.symm ⟨p, hmem⟩)) : S) :=
      dif_pos hmem
    have hmem2 : dehnTwistFun A p ∈ Set.range A.e := by
      rw [hbr1]
      exact Subtype.coe_prop _
    have hbr2 : dehnTwistInvFun A (dehnTwistFun A p)
        = (A.embHomeomorph (twistCore.symm
            (A.embHomeomorph.symm ⟨dehnTwistFun A p, hmem2⟩)) : S) :=
      dif_pos hmem2
    have hsymm : A.embHomeomorph.symm ⟨dehnTwistFun A p, hmem2⟩
        = twistCore (A.embHomeomorph.symm ⟨p, hmem⟩) := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext hbr1
    rw [hbr2, hsymm, Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  · have h1 : dehnTwistFun A p = p := dif_neg hmem
    rw [h1]
    exact dif_neg hmem

/-- The Dehn twist map undoes the inverse Dehn twist map. -/
theorem dehnTwist_rightInverse {S : Type*} [TopologicalSpace S] [T2Space S]
    {c : SimpleClosedCurve S} (A : AnnulusNbhd c) :
    Function.RightInverse (dehnTwistInvFun A) (dehnTwistFun A) := by
  intro p
  by_cases hmem : p ∈ Set.range A.e
  · have hbr1 : dehnTwistInvFun A p
        = (A.embHomeomorph (twistCore.symm (A.embHomeomorph.symm ⟨p, hmem⟩)) : S) :=
      dif_pos hmem
    have hmem2 : dehnTwistInvFun A p ∈ Set.range A.e := by
      rw [hbr1]
      exact Subtype.coe_prop _
    have hbr2 : dehnTwistFun A (dehnTwistInvFun A p)
        = (A.embHomeomorph (twistCore
            (A.embHomeomorph.symm ⟨dehnTwistInvFun A p, hmem2⟩)) : S) :=
      dif_pos hmem2
    have hsymm : A.embHomeomorph.symm ⟨dehnTwistInvFun A p, hmem2⟩
        = twistCore.symm (A.embHomeomorph.symm ⟨p, hmem⟩) := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext hbr1
    rw [hbr2, hsymm, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  · have h1 : dehnTwistInvFun A p = p := dif_neg hmem
    rw [h1]
    exact dif_neg hmem

/-- The Dehn twist about an annulus neighborhood, as a self-homeomorphism of
a compact Hausdorff surface. -/
noncomputable def dehnTwist {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] {c : SimpleClosedCurve S} (A : AnnulusNbhd c) : S ≃ₜ S :=
  Continuous.homeoOfEquivCompactToT2
    (f := ⟨dehnTwistFun A, dehnTwistInvFun A, dehnTwist_leftInverse A,
      dehnTwist_rightInverse A⟩)
    (continuous_dehnTwistFun A)

/-- The Dehn twist fixes every point outside its annulus. -/
theorem dehnTwist_apply_of_notMem {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {c : SimpleClosedCurve S}
    (A : AnnulusNbhd c) {p : S} (hp : p ∉ Set.range A.e) :
    dehnTwist A p = p := by
  exact dif_neg hp

/-- The support of the Dehn twist lies in its annulus. -/
theorem dehnTwist_support {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] {c : SimpleClosedCurve S} (A : AnnulusNbhd c) :
    ∀ p : S, dehnTwist A p ≠ p → p ∈ Set.range A.e := by
  intro p hne
  by_contra hp
  exact hne (dehnTwist_apply_of_notMem A hp)

/-- The Dehn twist preserves orientation: it is the identity near a point
outside the annulus, and orientation-preservation at one point propagates
over a connected surface with oriented atlas. -/
theorem dehnTwist_orientationPreserving {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S] [ConnectedSpace S]
    (hS : HasOrientedAtlas S) {c : SimpleClosedCurve S} (A : AnnulusNbhd c) :
    (dehnTwist A).IsOrientationPreserving := by
  obtain ⟨p₀, hp₀⟩ := A.proper
  have hfix : ∀ q, q ∈ (Set.range A.e)ᶜ → dehnTwist A q = q := fun q hq =>
    dehnTwist_apply_of_notMem A hq
  have hp₀fix : dehnTwist A p₀ = p₀ := hfix p₀ hp₀
  have hUopen : IsOpen ((Set.range A.e)ᶜ) :=
    (isCompact_range A.e.continuous).isClosed.isOpen_compl
  apply isOrientationPreserving_of_isOrientationPreservingAt_point hS (dehnTwist A) p₀
  have hrep : homeoChartRep (dehnTwist A) p₀ = (chartAt ℂ p₀).symm.trans
      (((dehnTwist A).toOpenPartialHomeomorph).trans (chartAt ℂ p₀)) := by
    unfold homeoChartRep
    rw [hp₀fix]
  rw [hrep]
  have hWopen : IsOpen ((chartAt ℂ p₀).source ∩ (Set.range A.e)ᶜ) :=
    (chartAt ℂ p₀).open_source.inter hUopen
  have hU'open : IsOpen ((chartAt ℂ p₀).symm.source ∩
      (chartAt ℂ p₀).symm ⁻¹' ((chartAt ℂ p₀).source ∩ (Set.range A.e)ᶜ)) :=
    (chartAt ℂ p₀).symm.isOpen_inter_preimage hWopen
  refine isOrientationPreservingAt_id (U := (chartAt ℂ p₀).symm.source ∩
      (chartAt ℂ p₀).symm ⁻¹' ((chartAt ℂ p₀).source ∩ (Set.range A.e)ᶜ))
      ?_ hU'open ?_ ?_
  · -- the composite is the identity on the small open set
    intro z hz
    have h1 : (chartAt ℂ p₀).symm z ∈ (chartAt ℂ p₀).source ∩ (Set.range A.e)ᶜ := hz.2
    have h2 : dehnTwist A ((chartAt ℂ p₀).symm z) = (chartAt ℂ p₀).symm z :=
      hfix _ h1.2
    have h3 : ((chartAt ℂ p₀).symm.trans (((dehnTwist A).toOpenPartialHomeomorph).trans
        (chartAt ℂ p₀))) z
        = chartAt ℂ p₀ (dehnTwist A ((chartAt ℂ p₀).symm z)) := by
      rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply,
        Homeomorph.toOpenPartialHomeomorph_apply]
    have hz_target : z ∈ (chartAt ℂ p₀).target := by
      have h4 : z ∈ (chartAt ℂ p₀).symm.source := hz.1
      rw [OpenPartialHomeomorph.symm_source] at h4
      exact h4
    have h5 : ((chartAt ℂ p₀).symm.trans (((dehnTwist A).toOpenPartialHomeomorph).trans
        (chartAt ℂ p₀))) z = z := by
      rw [h3, h2]
      exact (chartAt ℂ p₀).right_inv hz_target
    exact h5
  · -- the chart image of the base point lies in the small open set
    constructor
    · rw [OpenPartialHomeomorph.symm_source]
      exact (chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀)
    · rw [Set.mem_preimage, (chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)]
      exact ⟨mem_chart_source ℂ p₀, hp₀⟩
  · -- the small open set lies in the source of the composite
    intro z hz
    have h1 : (chartAt ℂ p₀).symm z ∈ (chartAt ℂ p₀).source ∩ (Set.range A.e)ᶜ := hz.2
    have h2 : dehnTwist A ((chartAt ℂ p₀).symm z) = (chartAt ℂ p₀).symm z :=
      hfix _ h1.2
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hz.1, ?_⟩
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [Homeomorph.toOpenPartialHomeomorph_source]
      exact Set.mem_univ _
    · rw [Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply, h2]
      exact h1.1

/-- The mapping class of the Dehn twist about an annulus neighborhood. -/
noncomputable def dehnTwistClass {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S] [ConnectedSpace S]
    [Fact (HasOrientedAtlas S)] {c : SimpleClosedCurve S}
    (A : AnnulusNbhd c) : MappingClassGroup S :=
  MCG.mk ⟨dehnTwist A, dehnTwist_orientationPreserving Fact.out A⟩

/-- Transport of the Dehn twist along a homeomorphism: the twist about the
transported annulus is the conjugate of the twist. -/
theorem dehnTwist_transport {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] {c : SimpleClosedCurve S} (A : AnnulusNbhd c) (f : S ≃ₜ S)
    (A' : AnnulusNbhd (f.mapSCC c)) (hA' : ∀ zt : Circle × I, A'.e zt = f (A.e zt)) :
    dehnTwist A' = f * dehnTwist A * f⁻¹ := by
  have key : ∀ (d : SimpleClosedCurve S) (B : AnnulusNbhd d) (zt : Circle × I),
      dehnTwistFun B (B.e zt) = B.e (twistCore zt) := by
    intro d B zt
    have hmem : B.e zt ∈ Set.range B.e := ⟨zt, rfl⟩
    have hbr : dehnTwistFun B (B.e zt)
        = (B.embHomeomorph (twistCore (B.embHomeomorph.symm ⟨B.e zt, hmem⟩)) : S) :=
      dif_pos hmem
    have hsymm : B.embHomeomorph.symm ⟨B.e zt, hmem⟩ = zt := by
      rw [Homeomorph.symm_apply_eq]
      exact Subtype.ext rfl
    rw [hbr, hsymm]
    rfl
  apply Homeomorph.ext
  intro p
  by_cases hmem : p ∈ Set.range A'.e
  · obtain ⟨zt, rfl⟩ := hmem
    have h1 : f.symm (A'.e zt) = A.e zt := by
      rw [hA' zt]
      exact f.symm_apply_apply (A.e zt)
    have hL : dehnTwist A' (A'.e zt) = A'.e (twistCore zt) := key _ A' zt
    have hR : (f * dehnTwist A * f⁻¹) (A'.e zt)
        = f (dehnTwist A (f.symm (A'.e zt))) := rfl
    have h2 : dehnTwist A (A.e zt) = A.e (twistCore zt) := key _ A zt
    rw [hL, hR, h1, h2]
    exact hA' (twistCore zt)
  · have hmem2 : f.symm p ∉ Set.range A.e := by
      intro hcon
      apply hmem
      obtain ⟨zt, hzt⟩ := hcon
      refine ⟨zt, ?_⟩
      rw [hA' zt, hzt]
      exact f.apply_symm_apply p
    have hL : dehnTwist A' p = p := dehnTwist_apply_of_notMem A' hmem
    have hR : (f * dehnTwist A * f⁻¹) p = f (dehnTwist A (f.symm p)) := rfl
    rw [hL, hR, dehnTwist_apply_of_notMem A hmem2, f.apply_symm_apply]

/-- Isotopic annuli give equal Dehn twist classes: transporting the annulus
by an isotopically trivial homeomorphism conjugates the twist by an element
of the isotopically trivial normal subgroup. -/
theorem dehnTwistClass_transport {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S] [ConnectedSpace S]
    [Fact (HasOrientedAtlas S)] {c : SimpleClosedCurve S} (A : AnnulusNbhd c)
    (f : S ≃ₜ S) (hf : IsIsotopicToId f) (A' : AnnulusNbhd (f.mapSCC c))
    (hA' : ∀ zt : Circle × I, A'.e zt = f (A.e zt)) :
    dehnTwistClass A' = dehnTwistClass A := by
  have htrans : dehnTwist A' = f * dehnTwist A * f⁻¹ := dehnTwist_transport A f A' hA'
  have hiso : IsIsotopicToId ((dehnTwist A)⁻¹ * dehnTwist A') := by
    rw [htrans]
    obtain ⟨H⟩ := hf
    have hconj : IsIsotopicToId ((dehnTwist A)⁻¹ * f * dehnTwist A) := by
      have hK : Nonempty (HIsotopy ((dehnTwist A)⁻¹ * (f * dehnTwist A))
          ((dehnTwist A)⁻¹ * (Homeomorph.refl S * dehnTwist A))) :=
        ⟨(HIsotopy.refl (dehnTwist A)⁻¹).mul (H.mul (HIsotopy.refl (dehnTwist A)))⟩
      have h1 : (dehnTwist A)⁻¹ * ((Homeomorph.refl S : S ≃ₜ S) * dehnTwist A)
          = Homeomorph.refl S := by
        change (dehnTwist A)⁻¹ * (1 * dehnTwist A) = 1
        rw [one_mul, inv_mul_cancel]
      rw [h1] at hK
      rw [mul_assoc]
      exact hK
    have hmul := IsIsotopicToId.mul hconj (IsIsotopicToId.inv ⟨H⟩)
    have heq : (dehnTwist A)⁻¹ * f * dehnTwist A * f⁻¹
        = (dehnTwist A)⁻¹ * (f * dehnTwist A * f⁻¹) := by
      group
    rw [heq] at hmul
    exact hmul
  exact (mcg_mk_eq_iff ⟨dehnTwist A', dehnTwist_orientationPreserving Fact.out A'⟩
    ⟨dehnTwist A, dehnTwist_orientationPreserving Fact.out A⟩).mpr hiso

end RiemannDynamics
