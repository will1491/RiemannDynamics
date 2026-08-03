/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.Orientation.Surface

/-!
# The mapping class group of a charted surface

Self-homeomorphisms of a space form a group under `mul f g = g.trans f`,
so `(f * g) x = f (g x)`. An isotopy between two self-homeomorphisms is a
homotopy of the underlying maps all of whose time slices are bijective; on a
compact Hausdorff space each slice is automatically a homeomorphism, via the
track homeomorphism `(s, x) ↦ (s, H (s, x))` of `I × S`. Isotopies are
closed under reversal, concatenation, pointwise product, and inverse.

The orientation-preserving homeomorphisms of a charted surface with oriented
atlas form a subgroup `homeoPlus S`; those isotopic to the identity form a
normal subgroup, by conjugating isotopies. The mapping class group is the
quotient.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval

namespace RiemannDynamics

/-! ## The group of self-homeomorphisms -/

/-- A homeomorphism as a continuous map. -/
def _root_.Homeomorph.toCM {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ Y) : C(X, Y) :=
  ⟨f, f.continuous⟩

/-- Self-homeomorphisms form a group under `mul f g = g.trans f`, so that
`(f * g) x = f (g x)`. -/
instance instGroupHomeomorph {X : Type*} [TopologicalSpace X] :
    Group (X ≃ₜ X) where
  mul f g := g.trans f
  one := Homeomorph.refl X
  inv := Homeomorph.symm
  mul_assoc _ _ _ := Homeomorph.ext fun _ => rfl
  one_mul _ := Homeomorph.ext fun _ => rfl
  mul_one _ := Homeomorph.ext fun _ => rfl
  inv_mul_cancel f := Homeomorph.ext f.symm_apply_apply

/-- Product of self-homeomorphisms is composition. -/
@[simp]
theorem _root_.Homeomorph.mul_apply {X : Type*} [TopologicalSpace X]
    (f g : X ≃ₜ X) (x : X) : (f * g) x = f (g x) :=
  rfl

/-- The identity self-homeomorphism is the group unit. -/
@[simp]
theorem _root_.Homeomorph.one_apply {X : Type*} [TopologicalSpace X] (x : X) :
    (1 : X ≃ₜ X) x = x :=
  rfl

/-- The group inverse of a self-homeomorphism is its inverse map. -/
@[simp]
theorem _root_.Homeomorph.inv_apply {X : Type*} [TopologicalSpace X]
    (f : X ≃ₜ X) (x : X) : f⁻¹ x = f.symm x :=
  rfl

/-! ## Isotopies through homeomorphisms -/

/-- An isotopy between two self-homeomorphisms: a homotopy of the underlying
maps all of whose time slices are bijective. -/
structure HIsotopy {S : Type*} [TopologicalSpace S] (f₀ f₁ : S ≃ₜ S) extends
    ContinuousMap.Homotopy f₀.toCM f₁.toCM where
  /-- Every time slice of the isotopy is a bijection. -/
  bij : ∀ s : I, Function.Bijective fun x => toHomotopy (s, x)

/-- The track map `(s, x) ↦ (s, H (s, x))` of an isotopy is a bijection of
`I × S`. -/
theorem HIsotopy.track_bijective {S : Type*} [TopologicalSpace S]
    {f₀ f₁ : S ≃ₜ S} (h : HIsotopy f₀ f₁) :
    Function.Bijective fun sx : I × S => (sx.1, h.toHomotopy sx) := by
  constructor
  · rintro ⟨s, x⟩ ⟨t, y⟩ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, hH⟩ := hxy
    exact Prod.ext rfl ((h.bij s).injective hH)
  · rintro ⟨s, y⟩
    obtain ⟨x, hx⟩ := (h.bij s).surjective y
    exact ⟨(s, x), Prod.ext rfl hx⟩

/-- The track homeomorphism of an isotopy on a compact Hausdorff space:
`(s, x) ↦ (s, H (s, x))` is a continuous bijection of the compact Hausdorff
space `I × S`, hence a homeomorphism. -/
noncomputable def HIsotopy.track {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (h : HIsotopy f₀ f₁) :
    (I × S) ≃ₜ (I × S) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ h.track_bijective)
    (continuous_fst.prodMk h.toHomotopy.continuous)

/-- The time-`s` slice of an isotopy on a compact Hausdorff space is a
homeomorphism. -/
noncomputable def HIsotopy.sliceHomeomorph {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (h : HIsotopy f₀ f₁)
    (s : I) : S ≃ₜ S :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (h.bij s))
    (h.toHomotopy.continuous.comp (continuous_const.prodMk continuous_id))

/-- The slice inverses of an isotopy are jointly continuous, via the track
homeomorphism. -/
theorem HIsotopy.continuous_symm_slices {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (h : HIsotopy f₀ f₁) :
    Continuous fun sx : I × S => (h.sliceHomeomorph sx.1).symm sx.2 := by
  have key : ∀ sx : I × S, (h.sliceHomeomorph sx.1).symm sx.2 = (h.track.symm sx).2 := by
    rintro ⟨s, y⟩
    have h1 : h.track (s, (h.sliceHomeomorph s).symm y) = (s, y) :=
      Prod.ext rfl ((h.sliceHomeomorph s).apply_symm_apply y)
    rw [h.track.symm_apply_eq.mpr h1.symm]
  have heq : (fun sx : I × S => (h.sliceHomeomorph sx.1).symm sx.2)
      = fun sx : I × S => (h.track.symm sx).2 := funext key
  rw [heq]
  exact continuous_snd.comp h.track.symm.continuous

/-! ## Closure formulas for isotopies -/

/-- The constant isotopy. -/
def HIsotopy.refl {S : Type*} [TopologicalSpace S] (f : S ≃ₜ S) :
    HIsotopy f f :=
  { ContinuousMap.Homotopy.refl f.toCM with
    bij := fun _ => f.bijective }

/-- Time reversal of an isotopy. -/
def HIsotopy.symm {S : Type*} [TopologicalSpace S] {f₀ f₁ : S ≃ₜ S}
    (h : HIsotopy f₀ f₁) : HIsotopy f₁ f₀ :=
  { h.toHomotopy.symm with
    bij := fun s => h.bij (unitInterval.symm s) }

/-- The slices of a concatenation of isotopies are bijective. -/
theorem HIsotopy.trans_bij {S : Type*} [TopologicalSpace S]
    {f₀ f₁ f₂ : S ≃ₜ S} (h₁ : HIsotopy f₀ f₁) (h₂ : HIsotopy f₁ f₂) (s : I) :
    Function.Bijective fun x => (h₁.toHomotopy.trans h₂.toHomotopy) (s, x) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · have heq : (fun x => (h₁.toHomotopy.trans h₂.toHomotopy) (s, x))
        = fun x => h₁.toHomotopy
            (⟨2 * (s : ℝ),
              (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x) := by
      funext x
      rw [ContinuousMap.Homotopy.trans_apply, dif_pos hs]
    rw [heq]
    exact h₁.bij _
  · have heq : (fun x => (h₁.toHomotopy.trans h₂.toHomotopy) (s, x))
        = fun x => h₂.toHomotopy
            (⟨2 * (s : ℝ) - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x) := by
      funext x
      rw [ContinuousMap.Homotopy.trans_apply, dif_neg hs]
    rw [heq]
    exact h₂.bij _

/-- Concatenation of isotopies. -/
noncomputable def HIsotopy.trans {S : Type*} [TopologicalSpace S] {f₀ f₁ f₂ : S ≃ₜ S}
    (h₁ : HIsotopy f₀ f₁) (h₂ : HIsotopy f₁ f₂) : HIsotopy f₀ f₂ :=
  { h₁.toHomotopy.trans h₂.toHomotopy with
    bij := HIsotopy.trans_bij h₁ h₂ }

/-- Pointwise product of isotopies: `H (s, x) = hf (s, hg (s, x))`. -/
def HIsotopy.mul {S : Type*} [TopologicalSpace S] {f₀ f₁ g₀ g₁ : S ≃ₜ S}
    (hf : HIsotopy f₀ f₁) (hg : HIsotopy g₀ g₁) :
    HIsotopy (f₀ * g₀) (f₁ * g₁) :=
  { hf.toHomotopy.comp hg.toHomotopy with
    bij := fun s => (hf.bij s).comp (hg.bij s) }

/-- The inverse isotopy starts at the inverse of the initial slice. -/
theorem HIsotopy.track_symm_zero {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (hf : HIsotopy f₀ f₁)
    (x : S) : (hf.track.symm (0, x)).2 = f₀.symm x := by
  have h1 : hf.track (0, f₀.symm x) = (0, x) := by
    change ((0 : I), hf.toHomotopy (0, f₀.symm x)) = (0, x)
    rw [hf.toHomotopy.apply_zero]
    change ((0 : I), f₀ (f₀.symm x)) = (0, x)
    rw [f₀.apply_symm_apply]
  rw [hf.track.symm_apply_eq.mpr h1.symm]

/-- The inverse isotopy ends at the inverse of the final slice. -/
theorem HIsotopy.track_symm_one {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (hf : HIsotopy f₀ f₁)
    (x : S) : (hf.track.symm (1, x)).2 = f₁.symm x := by
  have h1 : hf.track (1, f₁.symm x) = (1, x) := by
    change ((1 : I), hf.toHomotopy (1, f₁.symm x)) = (1, x)
    rw [hf.toHomotopy.apply_one]
    change ((1 : I), f₁ (f₁.symm x)) = (1, x)
    rw [f₁.apply_symm_apply]
  rw [hf.track.symm_apply_eq.mpr h1.symm]

/-- The slices of the inverse isotopy are bijective. -/
theorem HIsotopy.track_symm_bij {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (hf : HIsotopy f₀ f₁)
    (s : I) : Function.Bijective fun x : S => (hf.track.symm (s, x)).2 := by
  have key : (fun x : S => (hf.track.symm (s, x)).2)
      = fun x : S => (hf.sliceHomeomorph s).symm x := by
    funext x
    have h1 : hf.track (s, (hf.sliceHomeomorph s).symm x) = (s, x) :=
      Prod.ext rfl ((hf.sliceHomeomorph s).apply_symm_apply x)
    rw [hf.track.symm_apply_eq.mpr h1.symm]
  rw [key]
  exact (hf.sliceHomeomorph s).symm.bijective

/-- The inverse of an isotopy: `H (s, x) = (track⁻¹ (s, x)).2`, an isotopy
between the inverse homeomorphisms. -/
noncomputable def HIsotopy.inv {S : Type*} [TopologicalSpace S]
    [CompactSpace S] [T2Space S] {f₀ f₁ : S ≃ₜ S} (hf : HIsotopy f₀ f₁) :
    HIsotopy f₀⁻¹ f₁⁻¹ where
  toFun sx := (hf.track.symm sx).2
  continuous_toFun := continuous_snd.comp hf.track.symm.continuous
  map_zero_left := hf.track_symm_zero
  map_one_left := hf.track_symm_one
  bij := hf.track_symm_bij

/-- A self-homeomorphism is isotopically trivial when it is isotopic to the
identity. -/
def IsIsotopicToId {S : Type*} [TopologicalSpace S] (f : S ≃ₜ S) : Prop :=
  Nonempty (HIsotopy f (Homeomorph.refl S))

/-- The identity is isotopically trivial. -/
theorem IsIsotopicToId.refl (S : Type*) [TopologicalSpace S] :
    IsIsotopicToId (1 : S ≃ₜ S) :=
  ⟨HIsotopy.refl 1⟩

/-- Isotopic triviality is closed under products. -/
theorem IsIsotopicToId.mul {S : Type*} [TopologicalSpace S] {f g : S ≃ₜ S}
    (hf : IsIsotopicToId f) (hg : IsIsotopicToId g) : IsIsotopicToId (f * g) := by
  obtain ⟨hf'⟩ := hf
  obtain ⟨hg'⟩ := hg
  have h1 : Homeomorph.refl S * Homeomorph.refl S = Homeomorph.refl S :=
    Homeomorph.ext fun _ => rfl
  refine ⟨?_⟩
  have h2 := hf'.mul hg'
  rwa [h1] at h2

/-- Isotopic triviality is closed under inverses. -/
theorem IsIsotopicToId.inv {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] {f : S ≃ₜ S} (hf : IsIsotopicToId f) : IsIsotopicToId f⁻¹ := by
  obtain ⟨h⟩ := hf
  have h1 : (Homeomorph.refl S)⁻¹ = Homeomorph.refl S := Homeomorph.ext fun _ => rfl
  refine ⟨?_⟩
  have h2 := h.inv
  rwa [h1] at h2

/-! ## The mapping class group -/

/-- The subgroup of orientation-preserving self-homeomorphisms of a charted
surface with oriented atlas. -/
noncomputable def homeoPlus (S : Type*) [TopologicalSpace S]
    [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)] : Subgroup (S ≃ₜ S) where
  carrier := {f | f.IsOrientationPreserving}
  one_mem' := Homeomorph.IsOrientationPreserving.refl S
  mul_mem' ha hb := Homeomorph.IsOrientationPreserving.trans hb ha
  inv_mem' ha := Homeomorph.IsOrientationPreserving.symm Fact.out ha

/-- The genus surface has an oriented atlas, as an instance. -/
instance (g : ℕ) [NeZero g] : Fact (HasOrientedAtlas (GenusSurface g)) :=
  ⟨hasOrientedAtlas_genusSurface g⟩

/-- The isotopically trivial orientation-preserving homeomorphisms form a
subgroup of `homeoPlus S`. -/
noncomputable def isotopicallyTrivial (S : Type*) [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S]
    [Fact (HasOrientedAtlas S)] : Subgroup ↥(homeoPlus S) where
  carrier := {f | IsIsotopicToId (f : S ≃ₜ S)}
  one_mem' := IsIsotopicToId.refl S
  mul_mem' ha hb := IsIsotopicToId.mul ha hb
  inv_mem' ha := IsIsotopicToId.inv ha

/-- Isotopic triviality is preserved by conjugation: conjugate the isotopy
by the constant isotopy of the conjugator. -/
theorem isotopicallyTrivial_normal (S : Type*) [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S]
    [Fact (HasOrientedAtlas S)] : (isotopicallyTrivial S).Normal := by
  constructor
  intro n hn g
  have hn' : IsIsotopicToId ((n : S ≃ₜ S)) := hn
  obtain ⟨h⟩ := hn'
  have e0 : ((g * n * g⁻¹ : ↥(homeoPlus S)) : S ≃ₜ S)
      = (g : S ≃ₜ S) * ((n : S ≃ₜ S) * ((g : S ≃ₜ S))⁻¹) :=
    Homeomorph.ext fun _ => rfl
  have e1 : (g : S ≃ₜ S) * (Homeomorph.refl S * ((g : S ≃ₜ S))⁻¹) = Homeomorph.refl S :=
    Homeomorph.ext fun x => (g : S ≃ₜ S).apply_symm_apply x
  have hiso : HIsotopy ((g : S ≃ₜ S) * ((n : S ≃ₜ S) * ((g : S ≃ₜ S))⁻¹))
      ((g : S ≃ₜ S) * (Homeomorph.refl S * ((g : S ≃ₜ S))⁻¹)) :=
    (HIsotopy.refl ((g : S ≃ₜ S))).mul (h.mul (HIsotopy.refl (((g : S ≃ₜ S))⁻¹)))
  rw [e1] at hiso
  change IsIsotopicToId ((g * n * g⁻¹ : ↥(homeoPlus S)) : S ≃ₜ S)
  rw [e0]
  exact ⟨hiso⟩

instance (S : Type*) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)] :
    (isotopicallyTrivial S).Normal :=
  isotopicallyTrivial_normal S

/-- The mapping class group of a charted surface: orientation-preserving
homeomorphisms modulo isotopy. -/
noncomputable def MappingClassGroup (S : Type*) [TopologicalSpace S]
    [CompactSpace S] [T2Space S] [ChartedSpace ℂ S]
    [Fact (HasOrientedAtlas S)] : Type _ :=
  ↥(homeoPlus S) ⧸ isotopicallyTrivial S

noncomputable instance (S : Type*) [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)] :
    Group (MappingClassGroup S) :=
  inferInstanceAs (Group (↥(homeoPlus S) ⧸ isotopicallyTrivial S))

/-- The projection from orientation-preserving homeomorphisms onto their
mapping classes. -/
noncomputable def MCG.mk {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)] :
    ↥(homeoPlus S) →* MappingClassGroup S :=
  QuotientGroup.mk' (isotopicallyTrivial S)

/-- The mapping class group of the closed orientable surface of genus `g`. -/
noncomputable abbrev mappingClassGroupGenus (g : ℕ) [NeZero g] : Type :=
  MappingClassGroup (GenusSurface g)

/-- Two orientation-preserving homeomorphisms define the same mapping class
exactly when they differ by an isotopically trivial element. -/
theorem mcg_mk_eq_iff {S : Type*} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [ChartedSpace ℂ S] [Fact (HasOrientedAtlas S)]
    (f f' : ↥(homeoPlus S)) :
    MCG.mk f = MCG.mk f' ↔ IsIsotopicToId ((f'⁻¹ * f : ↥(homeoPlus S)) : S ≃ₜ S) := by
  constructor
  · intro hff
    have h2 : (f : ↥(homeoPlus S) ⧸ isotopicallyTrivial S)
        = (f' : ↥(homeoPlus S) ⧸ isotopicallyTrivial S) := hff
    have h3 : f⁻¹ * f' ∈ isotopicallyTrivial S := QuotientGroup.eq.mp h2
    have h4 : (f⁻¹ * f')⁻¹ ∈ isotopicallyTrivial S := inv_mem h3
    rw [mul_inv_rev, inv_inv] at h4
    exact h4
  · intro hff
    have h4 : f'⁻¹ * f ∈ isotopicallyTrivial S := hff
    have h3 : (f'⁻¹ * f)⁻¹ ∈ isotopicallyTrivial S := inv_mem h4
    rw [mul_inv_rev, inv_inv] at h3
    exact QuotientGroup.eq.mpr h3

/-- Isotopy invariance of orientation: on a connected compact surface with
oriented atlas, a homeomorphism isotopic to the identity preserves
orientation. -/
theorem isOrientationPreserving_of_isIsotopicToId {S : Type*}
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [ChartedSpace ℂ S]
    [ConnectedSpace S] (hS : HasOrientedAtlas S) {f : S ≃ₜ S}
    (h : IsIsotopicToId f) : f.IsOrientationPreserving := by
  obtain ⟨ht⟩ := h
  obtain ⟨p₀⟩ : Nonempty S := inferInstance
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  have hshift : ∀ (γ₁ γ₂ : C(I, ℂ)) (q₁ q₂ : ℂ),
      shiftedCurve γ₁ q₁ = shiftedCurve γ₂ q₂ →
      windingNumber γ₁ q₁ = windingNumber γ₂ q₂ := by
    intro γ₁ γ₂ q₁ q₂ hsc
    unfold windingNumber
    rw [hsc]
  have hsrcT : ∀ (a b : OpenPartialHomeomorph S ℂ) (w : ℂ),
      w ∈ (a.symm.trans b).source ↔ w ∈ a.target ∧ a.symm w ∈ b.source := by
    intro a b w
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact Iff.rfl
  have hsrcE : ∀ (F : S ≃ₜ S) (c d : OpenPartialHomeomorph S ℂ) (w : ℂ),
      w ∈ (c.symm.trans (F.toOpenPartialHomeomorph.trans d)).source ↔
        w ∈ c.target ∧ F (c.symm w) ∈ d.source := by
    intro F c d w
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (F : S ≃ₜ S) (a : S), chartAt ℂ a a ∈ (homeoChartRep F a).source := by
    intro F a
    exact (hsrcE F (chartAt ℂ a) (chartAt ℂ (F a)) (chartAt ℂ a a)).mpr
      ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), by
        rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
        exact mem_chart_source ℂ (F a)⟩
  have hmove : ∀ (F : S ≃ₜ S) (c c' d d' : OpenPartialHomeomorph S ℂ),
      c ∈ atlas ℂ S → c' ∈ atlas ℂ S → d ∈ atlas ℂ S → d' ∈ atlas ℂ S →
      ∀ q : S, q ∈ c.source → q ∈ c'.source → F q ∈ d.source → F q ∈ d'.source →
      IsOrientationPreservingAt (c.symm.trans (F.toOpenPartialHomeomorph.trans d)) (c q) →
      IsOrientationPreservingAt (c'.symm.trans (F.toOpenPartialHomeomorph.trans d')) (c' q) := by
    intro F c c' d d' hc hc' hd hd' q hqc hqc' hfd hfd' hE
    have hτ₁mem : c' q ∈ (c'.symm.trans c).source := by
      rw [hsrcT]
      refine ⟨c'.map_source hqc', ?_⟩
      rw [c'.left_inv hqc']
      exact hqc
    have hτ₁ : IsOrientationPreservingAt (c'.symm.trans c) (c' q) := hS c' hc' c hc _ hτ₁mem
    have hτ₁val : (c'.symm.trans c) (c' q) = c q := by
      change c (c'.symm (c' q)) = c q
      rw [c'.left_inv hqc']
    rw [← hτ₁val] at hE
    have hstep1 := isOrientationPreservingAt_trans hτ₁ hE
    have hτ₂mem : d (F q) ∈ (d.symm.trans d').source := by
      rw [hsrcT]
      refine ⟨d.map_source hfd, ?_⟩
      rw [d.left_inv hfd]
      exact hfd'
    have hτ₂ : IsOrientationPreservingAt (d.symm.trans d') (d (F q)) := hS d hd d' hd' _ hτ₂mem
    have hval2 : ((c'.symm.trans c).trans
        (c.symm.trans (F.toOpenPartialHomeomorph.trans d))) (c' q) = d (F q) := by
      change (c.symm.trans (F.toOpenPartialHomeomorph.trans d)) ((c'.symm.trans c) (c' q))
        = d (F q)
      rw [hτ₁val]
      change d (F (c.symm (c q))) = d (F q)
      rw [c.left_inv hqc]
    rw [← hval2] at hτ₂
    have hstep2 := isOrientationPreservingAt_trans hstep1 hτ₂
    have hUopen : IsOpen ((((c'.symm.trans c).trans
        (c.symm.trans (F.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
        (c'.symm.trans (F.toOpenPartialHomeomorph.trans d')).source) :=
      (((c'.symm.trans c).trans
        (c.symm.trans (F.toOpenPartialHomeomorph.trans d))).trans
          (d.symm.trans d')).open_source.inter
        (c'.symm.trans (F.toOpenPartialHomeomorph.trans d')).open_source
    have hEq : Set.EqOn (((c'.symm.trans c).trans
        (c.symm.trans (F.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d'))
        (c'.symm.trans (F.toOpenPartialHomeomorph.trans d'))
        ((((c'.symm.trans c).trans
          (c.symm.trans (F.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
          (c'.symm.trans (F.toOpenPartialHomeomorph.trans d')).source) := by
      intro w hw
      obtain ⟨hwC, -⟩ := hw
      rw [OpenPartialHomeomorph.trans_source] at hwC
      obtain ⟨hwC1, -⟩ := hwC
      rw [OpenPartialHomeomorph.trans_source] at hwC1
      obtain ⟨hw1, hw2⟩ := hwC1
      have hw1' := (hsrcT c' c w).mp hw1
      have hw2' : (c'.symm.trans c) w
          ∈ (c.symm.trans (F.toOpenPartialHomeomorph.trans d)).source := hw2
      have hw2'' := (hsrcE F c d _).mp hw2'
      have hcan : c.symm ((c'.symm.trans c) w) = c'.symm w := by
        change c.symm (c (c'.symm w)) = c'.symm w
        exact c.left_inv hw1'.2
      have hfd2 : F (c'.symm w) ∈ d.source := by
        rw [← hcan]
        exact hw2''.2
      change d' (d.symm (d (F (c.symm (c (c'.symm w)))))) = d' (F (c'.symm w))
      rw [c.left_inv hw1'.2, d.left_inv hfd2]
    have hzmem : c' q ∈ ((((c'.symm.trans c).trans
        (c.symm.trans (F.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
        (c'.symm.trans (F.toOpenPartialHomeomorph.trans d')).source) := by
      constructor
      · rw [OpenPartialHomeomorph.trans_source]
        constructor
        · rw [OpenPartialHomeomorph.trans_source]
          refine ⟨hτ₁mem, ?_⟩
          rw [Set.mem_preimage, hτ₁val, hsrcE]
          refine ⟨c.map_source hqc, ?_⟩
          rw [c.left_inv hqc]
          exact hfd
        · rw [Set.mem_preimage, hval2]
          exact hτ₂mem
      · rw [hsrcE]
        refine ⟨c'.map_source hqc', ?_⟩
        rw [c'.left_inv hqc']
        exact hfd'
    exact (isOrientationPreservingAt_congr hEq hUopen hzmem
      Set.inter_subset_left Set.inter_subset_right).mp hstep2
  have hcirc_norm : ∀ (z : ℂ) (ρ : ℝ) (t : I), 0 < ρ → ‖circleLoop z ρ t - z‖ = ρ := by
    intro z ρ t hρ
    have hsub : circleLoop z ρ t - z =
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z ρ t = z +
          (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hρ]
  have hcirc_cl : ∀ (z : ℂ) (ρ : ℝ), circleLoop z ρ 0 = circleLoop z ρ 1 := by
    intro z ρ
    have h0 : circleLoop z ρ 0 = z +
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z ρ 1 = z +
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  -- the key local constancy in the isotopy parameter
  have hkey : ∀ s₀ : I, ∀ᶠ s in 𝓝 s₀,
      (IsOrientationPreservingAt (homeoChartRep (ht.sliceHomeomorph s) p₀)
          (chartAt ℂ p₀ p₀) ↔
        IsOrientationPreservingAt (homeoChartRep (ht.sliceHomeomorph s₀) p₀)
          (chartAt ℂ p₀ p₀)) := by
    intro s₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
      (homeoChartRep (ht.sliceHomeomorph s₀) p₀).open_source _
      (hbase (ht.sliceHomeomorph s₀) p₀)
    have hr : 0 < ε / 2 := by positivity
    have hbr : Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) ⊆
        (homeoChartRep (ht.sliceHomeomorph s₀) p₀).source :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hcirc_mem : ∀ t : I, circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t ∈
        Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) := by
      intro t
      rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm _ _ t hr]
    have hKcompact : IsCompact ((chartAt ℂ p₀).symm ''
        Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2)) := by
      apply (isCompact_closedBall _ _).image_of_continuousOn
      apply ((chartAt ℂ p₀).symm.continuousOn).mono
      rw [OpenPartialHomeomorph.symm_source]
      intro z hz
      exact ((hsrcE (ht.sliceHomeomorph s₀) (chartAt ℂ p₀)
        (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)) z).mp (hbr hz)).1
    have hVopen : IsOpen (⇑ht.toHomotopy ⁻¹'
        (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).source) :=
      (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).open_source.preimage ht.toHomotopy.continuous
    have htube_sub : ({s₀} : Set I) ×ˢ ((chartAt ℂ p₀).symm ''
        Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2)) ⊆
        ⇑ht.toHomotopy ⁻¹' (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).source := by
      rintro ⟨w, x⟩ ⟨hw, hx⟩
      rw [Set.mem_singleton_iff] at hw
      change w = s₀ at hw
      change x ∈ (chartAt ℂ p₀).symm '' Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) at hx
      rw [Set.mem_preimage, hw]
      obtain ⟨z, hz, rfl⟩ := hx
      exact ((hsrcE (ht.sliceHomeomorph s₀) (chartAt ℂ p₀)
        (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)) z).mp (hbr hz)).2
    obtain ⟨W₁, W₂, hW₁open, -, hsW₁sub, hKW₂, hWsub⟩ :=
      generalized_tube_lemma isCompact_singleton hKcompact hVopen htube_sub
    have hs₀W₁ : s₀ ∈ W₁ := hsW₁sub rfl
    obtain ⟨δ, hδ, hballδ⟩ := Metric.isOpen_iff.mp hW₁open s₀ hs₀W₁
    have hVmem : ∀ (w : I) (x : S), w ∈ W₁ →
        x ∈ (chartAt ℂ p₀).symm '' Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) →
        ht.toHomotopy (w, x) ∈ (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).source := by
      intro w x hw hx
      exact hWsub (Set.mem_prod.mpr ⟨hw, hKW₂ hx⟩)
    have hcircK : ∀ t : I, (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t) ∈
        (chartAt ℂ p₀).symm '' Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) := by
      intro t
      exact Set.mem_image_of_mem _ (hcirc_mem t)
    have hx₀K : (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀) ∈
        (chartAt ℂ p₀).symm '' Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) :=
      Set.mem_image_of_mem _ (Metric.mem_closedBall_self hr.le)
    have hbψ : ∀ w : I, w ∈ W₁ → Metric.closedBall (chartAt ℂ p₀ p₀) (ε / 2) ⊆
        ((chartAt ℂ p₀).symm.trans
          ((ht.sliceHomeomorph w).toOpenPartialHomeomorph.trans
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))).source := by
      intro w hw z hz
      rw [hsrcE]
      refine ⟨((hsrcE (ht.sliceHomeomorph s₀) (chartAt ℂ p₀)
        (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)) z).mp (hbr hz)).1, ?_⟩
      exact hVmem w _ hw (Set.mem_image_of_mem _ hz)
    have hcsymm_circ : Continuous fun t : I =>
        (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t) := by
      apply ((chartAt ℂ p₀).symm.continuousOn).comp_continuous
        (circleLoop (chartAt ℂ p₀ p₀) (ε / 2)).continuous
      intro t
      rw [OpenPartialHomeomorph.symm_source]
      exact ((hsrcE (ht.sliceHomeomorph s₀) (chartAt ℂ p₀)
        (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)) _).mp (hbr (hcirc_mem t))).1
    -- eventual containment of the moved base point
    have hcontp : Continuous fun w : I => ht.toHomotopy (w, p₀) :=
      ht.toHomotopy.continuous.comp (continuous_id.prodMk continuous_const)
    have hEd : ∀ᶠ w in 𝓝 s₀, ht.toHomotopy (w, p₀) ∈
        (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).source :=
      hcontp.continuousAt.eventually
        ((chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).open_source.eventually_mem
          (mem_chart_source ℂ (ht.sliceHomeomorph s₀ p₀)))
    filter_upwards [Metric.isOpen_ball.eventually_mem (Metric.mem_ball_self hδ), hEd]
      with s hsδ hsd
    have hsW₁ : s ∈ W₁ := hballδ hsδ
    -- the interpolation path from s₀ to s inside the ball
    have humem : ∀ v : I,
        (1 - (v : ℝ)) * (s₀ : ℝ) + (v : ℝ) * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      intro v
      have h0 : (0 : ℝ) ≤ (v : ℝ) := v.2.1
      have h1 : (v : ℝ) ≤ 1 := v.2.2
      have ha0 : (0 : ℝ) ≤ (s₀ : ℝ) := s₀.2.1
      have ha1 : (s₀ : ℝ) ≤ 1 := s₀.2.2
      have hb0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
      have hb1 : (s : ℝ) ≤ 1 := s.2.2
      constructor <;> nlinarith
    obtain ⟨u, huapp⟩ : ∃ u : C(I, I), ∀ v : I,
        ((u v : I) : ℝ) = (1 - (v : ℝ)) * (s₀ : ℝ) + (v : ℝ) * (s : ℝ) :=
      ⟨⟨fun v => ⟨(1 - (v : ℝ)) * (s₀ : ℝ) + (v : ℝ) * (s : ℝ), humem v⟩, by
        apply Continuous.subtype_mk
        fun_prop⟩, fun v => rfl⟩
    have hu0 : u 0 = s₀ := by
      apply Subtype.ext
      rw [huapp 0]
      norm_num
    have hu1 : u 1 = s := by
      apply Subtype.ext
      rw [huapp 1]
      norm_num
    have huW : ∀ v : I, u v ∈ W₁ := by
      intro v
      apply hballδ
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, huapp v]
      have hsδ' : |(s : ℝ) - (s₀ : ℝ)| < δ := by
        have h1 := hsδ
        rwa [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at h1
      have h0 : (0 : ℝ) ≤ (v : ℝ) := v.2.1
      have h1 : (v : ℝ) ≤ 1 := v.2.2
      have heq : (1 - (v : ℝ)) * (s₀ : ℝ) + (v : ℝ) * (s : ℝ) - (s₀ : ℝ)
          = (v : ℝ) * ((s : ℝ) - (s₀ : ℝ)) := by ring
      rw [heq, abs_mul, abs_of_nonneg h0]
      calc (v : ℝ) * |(s : ℝ) - (s₀ : ℝ)| ≤ 1 * |(s : ℝ) - (s₀ : ℝ)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |(s : ℝ) - (s₀ : ℝ)| := one_mul _
        _ < δ := hsδ'
    -- the free homotopy between the two chart-read circles
    have hinner1 : Continuous fun vt : I × I => ht.toHomotopy (u vt.1,
        (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) vt.2)) :=
      ht.toHomotopy.continuous.comp
        ((u.continuous.comp continuous_fst).prodMk (hcsymm_circ.comp continuous_snd))
    have houter1 : Continuous fun vt : I × I =>
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (u vt.1,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) vt.2))) := by
      apply ((chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).continuousOn).comp_continuous hinner1
      intro vt
      exact hVmem (u vt.1) _ (huW vt.1) (hcircK vt.2)
    have hinner2 : Continuous fun vt : I × I => ht.toHomotopy (u vt.1,
        (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)) :=
      ht.toHomotopy.continuous.comp
        ((u.continuous.comp continuous_fst).prodMk continuous_const)
    have houter2 : Continuous fun vt : I × I =>
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (u vt.1,
          (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀))) := by
      apply ((chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).continuousOn).comp_continuous hinner2
      intro vt
      exact hVmem (u vt.1) _ (huW vt.1) hx₀K
    obtain ⟨G, hGapp⟩ : ∃ G : C(I × I, ℂ), ∀ v t : I, G (v, t) =
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (u v,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t)))
        - chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (u v,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))
        + chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀))) :=
      ⟨⟨_, (houter1.sub houter2).add continuous_const⟩, fun v t => rfl⟩
    have hGcl : ∀ v : I, G (v, 0) = G (v, 1) := by
      intro v
      rw [hGapp v 0, hGapp v 1, hcirc_cl]
    have hGne : ∀ v t : I, G (v, t) ≠
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
          (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀))) := by
      intro v t heq
      rw [hGapp v t] at heq
      have heq2 : chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (u v,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t)))
          = chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (u v,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀))) := by
        linear_combination heq
      have hmem1 := hVmem (u v) _ (huW v) (hcircK t)
      have hmem2 := hVmem (u v) _ (huW v) hx₀K
      have heq3 := (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).injOn hmem1 hmem2 heq2
      have heq4 := (ht.bij (u v)).1 heq3
      have hct : circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t ∈ (chartAt ℂ p₀).target :=
        ((hsrcE (ht.sliceHomeomorph s₀) (chartAt ℂ p₀)
          (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)) _).mp (hbr (hcirc_mem t))).1
      have hx₀t : chartAt ℂ p₀ p₀ ∈ (chartAt ℂ p₀).target :=
        (chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀)
      have hinj := (chartAt ℂ p₀).symm.injOn
      rw [OpenPartialHomeomorph.symm_source] at hinj
      have heq5 : circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t = chartAt ℂ p₀ p₀ :=
        hinj hct hx₀t heq4
      have h6 := hcirc_norm (chartAt ℂ p₀ p₀) (ε / 2) t hr
      rw [heq5, sub_self, norm_zero] at h6
      exact hr.ne h6
    have hHkey := windingNumber_eq_of_loopHomotopy
      (q := chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
        (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))) G hGcl hGne
    -- clean bundled loops at the two parameters
    have hout₀ : Continuous fun t : I =>
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t))) := by
      apply ((chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).continuousOn).comp_continuous
        (ht.toHomotopy.continuous.comp (continuous_const.prodMk hcsymm_circ))
      intro t
      exact hVmem s₀ _ hs₀W₁ (hcircK t)
    have hout₁ : Continuous fun t : I =>
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t))) := by
      apply ((chartAt ℂ (ht.sliceHomeomorph s₀ p₀)).continuousOn).comp_continuous
        (ht.toHomotopy.continuous.comp (continuous_const.prodMk hcsymm_circ))
      intro t
      exact hVmem s _ hsW₁ (hcircK t)
    obtain ⟨A₀, hA₀app⟩ : ∃ A : C(I, ℂ), ∀ t : I, A t =
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t))) :=
      ⟨⟨_, hout₀⟩, fun t => rfl⟩
    obtain ⟨A₁, hA₁app⟩ : ∃ A : C(I, ℂ), ∀ t : I, A t =
        chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s,
          (chartAt ℂ p₀).symm (circleLoop (chartAt ℂ p₀ p₀) (ε / 2) t))) :=
      ⟨⟨_, hout₁⟩, fun t => rfl⟩
    -- the degree equality between the two parameters
    have hdegeq : windingDegreeAt ((chartAt ℂ p₀).symm.trans
        ((ht.sliceHomeomorph s₀).toOpenPartialHomeomorph.trans
          (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) (ε / 2)
        (hbψ s₀ hs₀W₁) hr
        = windingDegreeAt ((chartAt ℂ p₀).symm.trans
          ((ht.sliceHomeomorph s).toOpenPartialHomeomorph.trans
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) (ε / 2)
          (hbψ s hsW₁) hr := by
      have hstep0 : windingDegreeAt ((chartAt ℂ p₀).symm.trans
          ((ht.sliceHomeomorph s₀).toOpenPartialHomeomorph.trans
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) (ε / 2)
          (hbψ s₀ hs₀W₁) hr = windingNumber A₀
          (chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))) := by
        unfold windingDegreeAt
        exact hwn_ext _ _ _ (fun t => (hA₀app t).symm)
      have hstep4 : windingDegreeAt ((chartAt ℂ p₀).symm.trans
          ((ht.sliceHomeomorph s).toOpenPartialHomeomorph.trans
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) (ε / 2)
          (hbψ s hsW₁) hr = windingNumber A₁
          (chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))) := by
        unfold windingDegreeAt
        exact hwn_ext _ _ _ (fun t => (hA₁app t).symm)
      rw [hstep0, hstep4]
      calc windingNumber A₀ (chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀))))
          = windingNumber (⟨fun t => G (0, t), by fun_prop⟩ : C(I, ℂ))
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
              (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))) := by
            refine hwn_ext _ _ _ (fun t => ?_)
            change A₀ t = G (0, t)
            rw [hA₀app t, hGapp 0 t, hu0]
            ring
        _ = windingNumber (⟨fun t => G (1, t), by fun_prop⟩ : C(I, ℂ))
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s₀,
              (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))) := hHkey
        _ = windingNumber A₁ (chartAt ℂ (ht.sliceHomeomorph s₀ p₀) (ht.toHomotopy (s,
            (chartAt ℂ p₀).symm (chartAt ℂ p₀ p₀)))) := by
            apply hshift
            ext t
            simp only [shiftedCurve, ContinuousMap.sub_apply, ContinuousMap.const_apply,
              ContinuousMap.coe_mk]
            rw [hA₁app t, hGapp 1 t, hu1]
            ring
    -- or-preservation transfers between the two parameters at the common chart
    have hiffB : IsOrientationPreservingAt ((chartAt ℂ p₀).symm.trans
        ((ht.sliceHomeomorph s).toOpenPartialHomeomorph.trans
          (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) ↔
        IsOrientationPreservingAt ((chartAt ℂ p₀).symm.trans
          ((ht.sliceHomeomorph s₀).toOpenPartialHomeomorph.trans
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) := by
      constructor
      · intro hOP
        have hall := (isOrientationPreservingAt_iff_forall _ _).mp hOP
        refine ⟨ε / 2, hr, hbψ s₀ hs₀W₁, ?_⟩
        rw [hdegeq]
        exact hall.2 _ hr (hbψ s hsW₁)
      · intro hOP
        have hall := (isOrientationPreservingAt_iff_forall _ _).mp hOP
        refine ⟨ε / 2, hr, hbψ s hsW₁, ?_⟩
        rw [← hdegeq]
        exact hall.2 _ hr (hbψ s₀ hs₀W₁)
    -- chart change on the target side at the parameter s
    have hiffA : IsOrientationPreservingAt (homeoChartRep (ht.sliceHomeomorph s) p₀)
        (chartAt ℂ p₀ p₀) ↔
        IsOrientationPreservingAt ((chartAt ℂ p₀).symm.trans
          ((ht.sliceHomeomorph s).toOpenPartialHomeomorph.trans
            (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)))) (chartAt ℂ p₀ p₀) := by
      constructor
      · intro hOP
        exact hmove (ht.sliceHomeomorph s) (chartAt ℂ p₀) (chartAt ℂ p₀)
          (chartAt ℂ (ht.sliceHomeomorph s p₀)) (chartAt ℂ (ht.sliceHomeomorph s₀ p₀))
          (chart_mem_atlas ℂ p₀) (chart_mem_atlas ℂ p₀)
          (chart_mem_atlas ℂ (ht.sliceHomeomorph s p₀))
          (chart_mem_atlas ℂ (ht.sliceHomeomorph s₀ p₀)) p₀
          (mem_chart_source ℂ p₀) (mem_chart_source ℂ p₀)
          (mem_chart_source ℂ (ht.sliceHomeomorph s p₀)) hsd hOP
      · intro hOP
        exact hmove (ht.sliceHomeomorph s) (chartAt ℂ p₀) (chartAt ℂ p₀)
          (chartAt ℂ (ht.sliceHomeomorph s₀ p₀)) (chartAt ℂ (ht.sliceHomeomorph s p₀))
          (chart_mem_atlas ℂ p₀) (chart_mem_atlas ℂ p₀)
          (chart_mem_atlas ℂ (ht.sliceHomeomorph s₀ p₀))
          (chart_mem_atlas ℂ (ht.sliceHomeomorph s p₀)) p₀
          (mem_chart_source ℂ p₀) (mem_chart_source ℂ p₀) hsd
          (mem_chart_source ℂ (ht.sliceHomeomorph s p₀)) hOP
    exact hiffA.trans hiffB
  -- the parameters with globally orientation-preserving slice form a clopen set
  have hAopen : IsOpen {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving} := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have hs₀' : (ht.sliceHomeomorph s₀).IsOrientationPreserving := hs₀
    have hfinal : ∀ᶠ s in 𝓝 s₀,
        s ∈ {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving} := by
      filter_upwards [hkey s₀] with s hiff
      exact isOrientationPreserving_of_isOrientationPreservingAt_point hS
        (ht.sliceHomeomorph s) p₀ (hiff.mpr (hs₀' p₀))
    rwa [Filter.eventually_iff, Set.setOf_mem_eq] at hfinal
  have hAcopen : IsOpen {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving}ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have hs₀' : ¬ (ht.sliceHomeomorph s₀).IsOrientationPreserving := hs₀
    have hfinal : ∀ᶠ s in 𝓝 s₀,
        s ∈ {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving}ᶜ := by
      filter_upwards [hkey s₀] with s hiff
      intro hcontra
      have hcontra' : (ht.sliceHomeomorph s).IsOrientationPreserving := hcontra
      exact hs₀' (isOrientationPreserving_of_isOrientationPreservingAt_point hS
        (ht.sliceHomeomorph s₀) p₀ (hiff.mp (hcontra' p₀)))
    rwa [Filter.eventually_iff, Set.setOf_mem_eq] at hfinal
  have h1mem : (1 : I) ∈ {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving} := by
    have hslice1 : ht.sliceHomeomorph 1 = Homeomorph.refl S :=
      Homeomorph.ext fun x => ht.toHomotopy.apply_one x
    change (ht.sliceHomeomorph 1).IsOrientationPreserving
    rw [hslice1]
    exact Homeomorph.IsOrientationPreserving.refl S
  have hclopen : IsClopen {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving} :=
    ⟨isOpen_compl_iff.mp hAcopen, hAopen⟩
  have huniv := hclopen.eq_univ ⟨1, h1mem⟩
  have h0mem : (0 : I) ∈ {w : I | (ht.sliceHomeomorph w).IsOrientationPreserving} := by
    rw [huniv]
    exact Set.mem_univ 0
  have hslice0 : ht.sliceHomeomorph 0 = f :=
    Homeomorph.ext fun x => ht.toHomotopy.apply_zero x
  have h0' : (ht.sliceHomeomorph 0).IsOrientationPreserving := h0mem
  rwa [hslice0] at h0'

end RiemannDynamics
