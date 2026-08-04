/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Polygon

/-!
# The rank identity: characters, crossing sums, and the star calculus

The space of additive characters `Γ → (ℝ, +)` of a cocompact free Fuchsian group has
dimension `m - c + 1`, where `m` is the number of side pairs and `c` the number of vertex
orbit classes of its Dirichlet polygon. This file sets up the objects of that count and
develops the local star calculus.

* `homSubmodule` — the `ℝ`-space of additive characters of a group; characters vanish on
  torsion (`homSubmodule_apply_eq_zero_of_sq`).
* `oddSideFunctions` — the odd side functions of the polygon; its dimension is `m`.
* `IsTilePath`, `crossingSum`, `cycleConstrained` — tile paths, the crossing sum of an odd
  side function along a path, and the subspace cut out by the vertex-loop constraints;
  `restrictSides` restricts a character to its side values.
* Crossing-sum list calculus: gluing, reversal, and telescoping of crossing sums, and
  generation of `Γ` by side elements (`closure_sideElements_eq_top`).
* Star chains and the star lemma: crossing sums of tile loops inside the contact star of a
  point vanish; `starVal` — the star value comparing two tiles at a star.
-/

open scoped ENNReal

namespace RiemannDynamics

/-! ## Additive characters of a group -/

/-- The space of **additive characters** of a group: the functions `G → ℝ` with
`f (a b) = f a + f b`, as a submodule of `G → ℝ`. -/
def homSubmodule (G : Type*) [Group G] : Submodule ℝ (G → ℝ) where
  carrier := {f | ∀ a b : G, f (a * b) = f a + f b}
  add_mem' := by
    intro f g hf hg a b
    simp only [Pi.add_apply, hf a b, hg a b]
    ring
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c f hf a b
    simp only [Pi.smul_apply, hf a b, smul_eq_mul]
    ring

/-- An additive character vanishes at the identity, since `f 1 = f (1 * 1) = f 1 + f 1`. -/
theorem homSubmodule_apply_one {G : Type*} [Group G] (f : homSubmodule G) :
    (f : G → ℝ) 1 = 0 := by
  have h1 := f.2 1 1
  simp only [one_mul] at h1
  linarith

/-- Additive characters kill torsion: `f t = 0` whenever `t² = 1`. In particular a
character vanishes on `-1` and takes equal values on `γ` and `-γ`. -/
theorem homSubmodule_apply_eq_zero_of_sq {G : Type*} [Group G] (f : homSubmodule G)
    {t : G} (ht : t * t = 1) : (f : G → ℝ) t = 0 := by
  have h := f.2 t t
  rw [ht] at h
  rw [homSubmodule_apply_one f] at h
  linarith

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## Odd side functions -/

/-- The **odd side functions** of the Dirichlet polygon: functions on the group vanishing
off the side elements, odd under inversion, and constant on the fibers of `γ ↦ γ • τ₀`. -/
def oddSideFunctions (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Submodule ℝ ((↥Γ) → ℝ) where
  carrier := {α | (∀ γ : ↥Γ, ¬IsSideElement Γ τ₀ γ → α γ = 0) ∧
    (∀ γ : ↥Γ, α γ⁻¹ = -α γ) ∧ ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ}
  add_mem' := by
    rintro α β ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    refine ⟨fun γ h => ?_, fun γ => ?_, fun γ δ h => ?_⟩
    · simp only [Pi.add_apply, h1 γ h, g1 γ h, add_zero]
    · simp only [Pi.add_apply, h2 γ, g2 γ]
      ring
    · simp only [Pi.add_apply, h3 γ δ h, g3 γ δ h]
  zero_mem' := by
    refine ⟨fun γ _ => rfl, fun γ => ?_, fun γ δ _ => rfl⟩
    simp
  smul_mem' := by
    rintro c α ⟨h1, h2, h3⟩
    refine ⟨fun γ h => ?_, fun γ => ?_, fun γ δ h => ?_⟩
    · simp only [Pi.smul_apply, h1 γ h, smul_eq_mul, mul_zero]
    · simp only [Pi.smul_apply, h2 γ, smul_eq_mul]
      ring
    · simp only [Pi.smul_apply, h3 γ δ h]

/-- Membership in the odd side functions, unfolded into its three defining conditions:
vanishing off the side elements, oddness under inversion, and constancy on the fibers of
`γ ↦ γ • τ₀`. -/
theorem mem_oddSideFunctions {α : (↥Γ) → ℝ} :
    α ∈ oddSideFunctions Γ τ₀ ↔ (∀ γ : ↥Γ, ¬IsSideElement Γ τ₀ γ → α γ = 0) ∧
      (∀ γ : ↥Γ, α γ⁻¹ = -α γ) ∧ ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ :=
  Iff.rfl

/-! ## Tile paths and crossing sums -/

/-- A **tile path**: a finite sequence of group elements in which consecutive tiles share a
genuine side, the transition elements being side elements. -/
def IsTilePath (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (p : List ↥Γ) : Prop :=
  p.IsChain fun γ δ => IsSideElement Γ τ₀ (γ⁻¹ * δ)

/-- The **crossing sum** of a side function along a tile path: the sum of its values on the
transition elements of consecutive tiles. -/
def crossingSum (α : (↥Γ) → ℝ) (p : List ↥Γ) : ℝ :=
  ((p.zip p.tail).map fun q => α (q.1⁻¹ * q.2)).sum

/-- The crossing sum of the zero side function vanishes along every path. -/
theorem crossingSum_zero (p : List ↥Γ) : crossingSum (0 : (↥Γ) → ℝ) p = 0 := by
  unfold crossingSum
  induction p.zip p.tail with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp

/-- The crossing sum is additive in the side function, for a fixed path. -/
theorem crossingSum_add (α β : (↥Γ) → ℝ) (p : List ↥Γ) :
    crossingSum (α + β) p = crossingSum α p + crossingSum β p := by
  unfold crossingSum
  induction p.zip p.tail with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [Pi.add_apply]
    ring

/-- The crossing sum is homogeneous in the side function, for a fixed path. Together with
`crossingSum_add` this makes `α ↦ crossingSum α p` linear, which is what lets the vertex
constraints cut out a subspace. -/
theorem crossingSum_smul (c : ℝ) (α : (↥Γ) → ℝ) (p : List ↥Γ) :
    crossingSum (c • α) p = c * crossingSum α p := by
  unfold crossingSum
  induction p.zip p.tail with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Singleton paths have zero crossing sum. -/
theorem crossingSum_singleton (α : (↥Γ) → ℝ) (a : ↥Γ) :
    crossingSum α [a] = 0 := by
  simp [crossingSum]
/-- The crossing sum of a two-step-or-longer path splits off its first transition. -/
theorem crossingSum_cons_cons (α : (↥Γ) → ℝ) (a b : ↥Γ) (l : List ↥Γ) :
    crossingSum α (a :: b :: l) = α (a⁻¹ * b) + crossingSum α (b :: l) := by
  simp [crossingSum, List.zip_cons_cons]

/-- A **vertex loop** at `v`: a tile path through tiles all containing `v`, returning to its
starting element. -/
def IsVertexLoop (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (v : UpperHalfPlane) (p : List ↥Γ) : Prop :=
  IsTilePath Γ τ₀ p ∧ (∀ γ ∈ p, γ ∈ contactSet Γ τ₀ v) ∧ p.head? = p.getLast?

/-- The **cycle-constrained side functions**: the odd side functions whose crossing sums
vanish along every vertex loop of the polygon. -/
def cycleConstrained (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Submodule ℝ ((↥Γ) → ℝ) where
  carrier := {α | α ∈ oddSideFunctions Γ τ₀ ∧ ∀ v ∈ polygonVertices Γ τ₀,
    ∀ p : List ↥Γ, IsVertexLoop Γ τ₀ v p → crossingSum α p = 0}
  add_mem' := by
    rintro α β ⟨hα1, hα2⟩ ⟨hβ1, hβ2⟩
    refine ⟨(oddSideFunctions Γ τ₀).add_mem hα1 hβ1, fun v hv p hp => ?_⟩
    rw [crossingSum_add, hα2 v hv p hp, hβ2 v hv p hp, add_zero]
  zero_mem' :=
    ⟨(oddSideFunctions Γ τ₀).zero_mem, fun v _ p _ => crossingSum_zero p⟩
  smul_mem' := by
    rintro c α ⟨hα1, hα2⟩
    refine ⟨(oddSideFunctions Γ τ₀).smul_mem c hα1, fun v hv p hp => ?_⟩
    rw [crossingSum_smul, hα2 v hv p hp, mul_zero]

/-- Membership in the cycle-constrained side functions, unfolded: an odd side function
whose crossing sum vanishes along every vertex loop of the polygon. -/
theorem mem_cycleConstrained {α : (↥Γ) → ℝ} :
    α ∈ cycleConstrained Γ τ₀ ↔ α ∈ oddSideFunctions Γ τ₀ ∧
      ∀ v ∈ polygonVertices Γ τ₀, ∀ p : List ↥Γ,
        IsVertexLoop Γ τ₀ v p → crossingSum α p = 0 :=
  Iff.rfl

/-! ## Restriction of characters to side values -/

/-- Restriction of an additive character to its values on side elements, extended by zero:
a linear map into the side functions. -/
noncomputable def restrictSides (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : homSubmodule (↥Γ) →ₗ[ℝ] ((↥Γ) → ℝ) where
  toFun f := {γ : ↥Γ | IsSideElement Γ τ₀ γ}.indicator (f : (↥Γ) → ℝ)
  map_add' f g := by
    ext γ
    by_cases h : γ ∈ {γ : ↥Γ | IsSideElement Γ τ₀ γ}
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  map_smul' c f := by
    ext γ
    by_cases h : γ ∈ {γ : ↥Γ | IsSideElement Γ τ₀ γ}
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]

/-! ## The rank identity -/

/-- Under a translation-length gap, the square of an element moving the basepoint moves the
basepoint: the element is hyperbolic, the square has trace `t² - 2 > 2`, hence is
hyperbolic, and hyperbolic elements displace every point by the translation length. -/
theorem sq_smul_basepoint_ne {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    {γ : ↥Γ} (hmove : γ • τ₀ ≠ τ₀) : (γ * γ) • τ₀ ≠ τ₀ := by
  intro hfix
  have hnt : actsNontrivially (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    ⟨τ₀, by rw [← Subgroup.smul_def]; exact hmove⟩
  have hlen : ε ≤ translationLength (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    hgap _ γ.2 hnt
  have hhyp : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic :=
    (translationLength_pos_iff _).mp (lt_of_lt_of_le hε hlen)
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d,
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    rwa [hM, Matrix.det_fin_two_of] at h
  have htr : 4 < (a + d) ^ 2 := by
    unfold Matrix.IsHyperbolic at hhyp
    rw [Matrix.discr_fin_two, hM, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at hhyp
    nlinarith [hhyp, hdet]
  have hsq : (((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] * !![a, b; c, d] := by
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hM]
  have hTr : a * a + b * c + (c * b + d * d) = (a + d) ^ 2 - 2 := by
    linear_combination (-2 : ℝ) * hdet
  have hDet : (a * a + b * c) * (c * b + d * d) - (a * b + b * d) * (c * a + d * c) = 1 := by
    linear_combination (a * d - b * c + 1) * hdet
  have hhyp2 : (((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
    unfold Matrix.IsHyperbolic
    rw [Matrix.discr_fin_two, hsq, Matrix.mul_fin_two, Matrix.trace_fin_two_of,
      Matrix.det_fin_two_of, hTr, hDet]
    nlinarith [htr]
  have hpos : 0 < translationLength ((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    (translationLength_pos_iff _).mpr hhyp2
  have hle := translationLength_le_dist_smul
    ((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) hhyp2 τ₀
  rw [← Subgroup.smul_def, hfix, dist_self] at hle
  linarith

/-- The basepoint images of an element moving the basepoint and of its inverse differ:
otherwise the square would fix the basepoint. -/
theorem smul_basepoint_ne_inv {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    {γ : ↥Γ} (hmove : γ • τ₀ ≠ τ₀) : γ • τ₀ ≠ γ⁻¹ • τ₀ := by
  intro h
  refine sq_smul_basepoint_ne hε hgap hmove ?_
  rw [mul_smul, h, smul_inv_smul]

/-- Elements whose basepoint images agree up to the side pairing span the same side pair. -/
theorem pair_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀ ∨ γ • τ₀ = δ⁻¹ • τ₀) :
    ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} := by
  rcases h with h | h
  · rw [sideSet_eq_of_basepoint_eq h,
      sideSet_eq_of_basepoint_eq (inv_smul_eq_of_basepoint_eq hfree h τ₀)]
  · rw [sideSet_eq_of_basepoint_eq h,
      sideSet_eq_of_basepoint_eq (inv_smul_eq_of_basepoint_eq hfree h τ₀), inv_inv]
    exact Set.pair_comm _ _

/-- A side lying in the pair of another side element pins the basepoint image up to the
side pairing. -/
theorem center_or_of_mem_pair (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ) (hδ : IsSideElement Γ τ₀ δ)
    (h : dirichletSideSet Γ τ₀ γ ∈
      ({dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} : Set (Set UpperHalfPlane))) :
    γ • τ₀ = δ • τ₀ ∨ γ • τ₀ = δ⁻¹ • τ₀ := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact Or.inl (smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ h)
  · exact Or.inr (smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ.inv h)

open Classical in
/-- The elementary odd side function of a side element: `1` on its basepoint fiber, `-1` on
the fiber of the inverse, `0` elsewhere. -/
noncomputable def elemSide (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (κ : ↥Γ) : (↥Γ) → ℝ := fun γ =>
  if γ • τ₀ = κ • τ₀ then 1 else if γ • τ₀ = κ⁻¹ • τ₀ then -1 else 0

/-- On the basepoint fiber of the side element the elementary function is `1`. -/
theorem elemSide_apply_of_eq {κ γ : ↥Γ} (h : γ • τ₀ = κ • τ₀) :
    elemSide Γ τ₀ κ γ = 1 := by
  unfold elemSide
  rw [if_pos h]

/-- On the basepoint fiber of the inverse the elementary function is `-1`. -/
theorem elemSide_apply_of_inv {κ γ : ↥Γ} (h : γ • τ₀ = κ⁻¹ • τ₀)
    (hne : κ • τ₀ ≠ κ⁻¹ • τ₀) : elemSide Γ τ₀ κ γ = -1 := by
  unfold elemSide
  rw [if_neg fun hc => hne (hc.symm.trans h), if_pos h]

/-- Off the two basepoint fibers the elementary function vanishes. -/
theorem elemSide_apply_of_ne {κ γ : ↥Γ} (h1 : γ • τ₀ ≠ κ • τ₀)
    (h2 : γ • τ₀ ≠ κ⁻¹ • τ₀) : elemSide Γ τ₀ κ γ = 0 := by
  unfold elemSide
  rw [if_neg h1, if_neg h2]

/-- The elementary function of a side element is an odd side function. -/
theorem elemSide_mem
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    {κ : ↥Γ} (hκ : IsSideElement Γ τ₀ κ) :
    elemSide Γ τ₀ κ ∈ oddSideFunctions Γ τ₀ := by
  have hne : κ • τ₀ ≠ κ⁻¹ • τ₀ := smul_basepoint_ne_inv hε hgap hκ.1
  refine ⟨fun γ hγ => ?_, fun γ => ?_, fun γ δ h => ?_⟩
  · refine elemSide_apply_of_ne (fun h => ?_) fun h => ?_
    · exact hγ ((isSideElement_congr h).mpr hκ)
    · exact hγ ((isSideElement_congr h).mpr hκ.inv)
  · by_cases h1 : γ • τ₀ = κ • τ₀
    · have h2 : γ⁻¹ • τ₀ = κ⁻¹ • τ₀ := inv_smul_eq_of_basepoint_eq hfree h1 τ₀
      rw [elemSide_apply_of_inv h2 hne, elemSide_apply_of_eq h1]
    · by_cases h3 : γ • τ₀ = κ⁻¹ • τ₀
      · have h4 : γ⁻¹ • τ₀ = κ • τ₀ := by
          have h5 := inv_smul_eq_of_basepoint_eq hfree h3 τ₀
          rwa [inv_inv] at h5
        rw [elemSide_apply_of_eq h4, elemSide_apply_of_inv h3 hne]
        norm_num
      · have h5 : γ⁻¹ • τ₀ ≠ κ • τ₀ := fun h => by
          have h6 := inv_smul_eq_of_basepoint_eq hfree h τ₀
          rw [inv_inv] at h6
          exact h3 h6
        have h6 : γ⁻¹ • τ₀ ≠ κ⁻¹ • τ₀ := fun h => by
          have h7 := inv_smul_eq_of_basepoint_eq hfree h τ₀
          rw [inv_inv, inv_inv] at h7
          exact h1 h7
        rw [elemSide_apply_of_ne h5 h6, elemSide_apply_of_ne h1 h3]
        norm_num
  · unfold elemSide
    rw [h]

/-- The odd side functions are linearly equivalent to the functions on the side pairs:
evaluation at a representative of each pair, inverted by summing elementary functions. -/
theorem oddSide_equiv_pairs (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Nonempty ((oddSideFunctions Γ τ₀) ≃ₗ[ℝ] (↥(polygonSidePairs Γ τ₀) → ℝ)) := by
  classical
  haveI := (finite_polygonSidePairs hΓ hfree hε hgap hdense).fintype
  have hrep : ∀ P : ↥(polygonSidePairs Γ τ₀), ∃ gP : ↥Γ, IsSideElement Γ τ₀ gP ∧
      (P : Set (Set UpperHalfPlane))
        = {dirichletSideSet Γ τ₀ gP, dirichletSideSet Γ τ₀ gP⁻¹} := fun P => P.2
  choose g hg1 hg2 using hrep
  have hpin : ∀ (P : ↥(polygonSidePairs Γ τ₀)) {γ : ↥Γ}, IsSideElement Γ τ₀ γ →
      (γ • τ₀ = g P • τ₀ ∨ γ • τ₀ = (g P)⁻¹ • τ₀) →
      (P : Set (Set UpperHalfPlane))
        = {dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} := by
    intro P γ hγ h
    rw [hg2 P]
    exact (pair_eq hfree h).symm
  have hdelta : ∀ P P' : ↥(polygonSidePairs Γ τ₀), P ≠ P' →
      elemSide Γ τ₀ (g P) (g P') = 0 := by
    intro P P' hPP
    refine elemSide_apply_of_ne (fun h => hPP ?_) fun h => hPP ?_
    · exact Subtype.ext ((hpin P (hg1 P') (Or.inl h)).trans (hg2 P').symm)
    · exact Subtype.ext ((hpin P (hg1 P') (Or.inr h)).trans (hg2 P').symm)
  set E : oddSideFunctions Γ τ₀ →ₗ[ℝ] (↥(polygonSidePairs Γ τ₀) → ℝ) :=
    { toFun := fun α P => (α : (↥Γ) → ℝ) (g P)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl } with hEdef
  set G : (↥(polygonSidePairs Γ τ₀) → ℝ) →ₗ[ℝ] oddSideFunctions Γ τ₀ :=
    { toFun := fun w => ⟨∑ P : ↥(polygonSidePairs Γ τ₀), w P • elemSide Γ τ₀ (g P),
        Submodule.sum_mem _ fun P _ =>
          Submodule.smul_mem _ _ (elemSide_mem hfree hε hgap (hg1 P))⟩
      map_add' := fun w w' => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, add_smul]
      map_smul' := fun c w => by
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun P _ => by
          rw [Pi.smul_apply, smul_smul, smul_eq_mul] } with hGdef
  have hEG : E.comp G = LinearMap.id := by
    apply LinearMap.ext
    intro w
    funext P'
    change (∑ P : ↥(polygonSidePairs Γ τ₀), w P • elemSide Γ τ₀ (g P)) (g P') = w P'
    rw [Finset.sum_apply, Finset.sum_eq_single P']
    · rw [Pi.smul_apply, elemSide_apply_of_eq rfl, smul_eq_mul, mul_one]
    · intro P _ hP
      rw [Pi.smul_apply, hdelta P P' hP, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ P') h
  have hGE : G.comp E = LinearMap.id := by
    apply LinearMap.ext
    intro α
    apply Subtype.ext
    funext γ
    obtain ⟨hz, hodd, hfib⟩ := α.2
    change (∑ P : ↥(polygonSidePairs Γ τ₀),
      ((α : (↥Γ) → ℝ) (g P)) • elemSide Γ τ₀ (g P)) γ = (α : (↥Γ) → ℝ) γ
    rw [Finset.sum_apply]
    by_cases hside : IsSideElement Γ τ₀ γ
    · set P₀ : ↥(polygonSidePairs Γ τ₀) :=
        ⟨{dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹}, γ, hside, rfl⟩ with hP₀
      rw [Finset.sum_eq_single P₀]
      · have hmem : dirichletSideSet Γ τ₀ γ ∈
            ({dirichletSideSet Γ τ₀ (g P₀), dirichletSideSet Γ τ₀ (g P₀)⁻¹} :
              Set (Set UpperHalfPlane)) := by
          rw [← hg2 P₀]
          exact Set.mem_insert _ _
        rcases center_or_of_mem_pair hΓ hfree hside (hg1 P₀) hmem with h | h
        · rw [Pi.smul_apply, elemSide_apply_of_eq h, smul_eq_mul, mul_one]
          exact (hfib γ (g P₀) h).symm
        · have hne := smul_basepoint_ne_inv hε hgap (hg1 P₀).1
          rw [Pi.smul_apply, elemSide_apply_of_inv h hne, smul_eq_mul, mul_neg_one]
          rw [hfib γ (g P₀)⁻¹ h, hodd (g P₀)]
      · intro P _ hP
        have hzero : elemSide Γ τ₀ (g P) γ = 0 := by
          refine elemSide_apply_of_ne (fun h => hP ?_) fun h => hP ?_
          · exact Subtype.ext (hpin P hside (Or.inl h))
          · exact Subtype.ext (hpin P hside (Or.inr h))
        rw [Pi.smul_apply, hzero, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ P₀) h
    · rw [hz γ hside]
      refine Finset.sum_eq_zero fun P _ => ?_
      have hzero : elemSide Γ τ₀ (g P) γ = 0 := by
        refine elemSide_apply_of_ne (fun h => hside ?_) fun h => hside ?_
        · exact (isSideElement_congr h).mpr (hg1 P)
        · exact (isSideElement_congr h).mpr (hg1 P).inv
      rw [Pi.smul_apply, hzero, smul_zero]
  exact ⟨LinearEquiv.ofLinear E G hEG hGE⟩

/-- The odd side functions form a finite-dimensional space: they embed into the functions
on the finite side set. -/
theorem finiteDimensional_oddSideFunctions (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (oddSideFunctions Γ τ₀) := by
  obtain ⟨e⟩ := oddSide_equiv_pairs hΓ hfree hε hgap hdense
  haveI : Finite ↥(polygonSidePairs Γ τ₀) :=
    (finite_polygonSidePairs hΓ hfree hε hgap hdense).to_subtype
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- The dimension of the odd side functions is the number `m` of side pairs: one degree of
freedom per pair, the two members of a pair carrying opposite values. -/
theorem finrank_oddSideFunctions (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Module.finrank ℝ (oddSideFunctions Γ τ₀) = polygonSideCount Γ τ₀ := by
  obtain ⟨e⟩ := oddSide_equiv_pairs hΓ hfree hε hgap hdense
  haveI := (finite_polygonSidePairs hΓ hfree hε hgap hdense).fintype
  rw [e.finrank_eq, Module.finrank_pi, polygonSideCount, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card]

/-- Left translation preserves tile paths: the transition elements are unchanged. -/
theorem isTilePath_map (γ : ↥Γ) {p : List ↥Γ} (hp : IsTilePath Γ τ₀ p) :
    IsTilePath Γ τ₀ (p.map (γ * ·)) := by
  refine List.isChain_map_of_isChain _ (fun a b h => ?_) hp
  have he : (γ * a)⁻¹ * (γ * b) = a⁻¹ * b := by group
  rw [he]
  exact h

/-- Contact membership depends only on the basepoint image. -/
theorem mem_contactSet_congr {δ η : ↥Γ} (h : δ • τ₀ = η • τ₀) {z : UpperHalfPlane}
    (hδ : δ ∈ contactSet Γ τ₀ z) : η ∈ contactSet Γ τ₀ z := by
  have h1 : dist z (δ • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀) := hδ
  change dist z (η • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀)
  rw [← h]
  exact h1

/-- Any contact tile of a domain point is reached from the base tile by a tile path: within
the star of the point, tiles chain by genuine side sharing — through the connected side
adjacency at a vertex, or by the direct side transition at a nonvertex contact point. -/
theorem chain_of_contact_base (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) {β : ↥Γ}
    (hβ : β ∈ contactSet Γ τ₀ z) :
    ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ p.head? = some 1 ∧
      ∃ η : ↥Γ, p.getLast? = some η ∧ η • τ₀ = β • τ₀ := by
  classical
  by_cases hβτ : β • τ₀ = τ₀
  · exact ⟨[1], List.isChain_singleton _, rfl, 1, rfl, by rw [one_smul, hβτ]⟩
  by_cases hcard : 3 ≤ (tileCenters Γ τ₀ z).ncard
  · have hv : z ∈ polygonVertices Γ τ₀ := ⟨hz, hcard⟩
    have hrepex : ∀ q : UpperHalfPlane, ∃ g : ↥Γ,
        q ∈ tileCenters Γ τ₀ z → g ∈ contactSet Γ τ₀ z ∧ g • τ₀ = q := by
      intro q
      by_cases hq : q ∈ tileCenters Γ τ₀ z
      · obtain ⟨g, hg, hgq⟩ := hq
        exact ⟨g, fun _ => ⟨hg, hgq⟩⟩
      · exact ⟨1, fun h => absurd h hq⟩
    choose rep hrep using hrepex
    set S : Set UpperHalfPlane := {q | q ∈ tileCenters Γ τ₀ z ∧
      ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ p.head? = some 1 ∧
        ∃ η : ↥Γ, p.getLast? = some η ∧ η • τ₀ = q} with hS
    have hτ₀S : τ₀ ∈ S := ⟨⟨1, one_mem_contactSet hz, one_smul _ τ₀⟩, [1],
      List.isChain_singleton _, rfl, 1, rfl, one_smul _ τ₀⟩
    have hSeq : S = tileCenters Γ τ₀ z := by
      refine adj_closed_eq hΓ hfree hv (fun q hq => (hrep q hq).1)
        (fun q hq => (hrep q hq).2) (fun q hq => hq.1) ⟨τ₀, hτ₀S⟩ ?_
      rintro q ⟨hqP, p, hp, phead, η, plast, hητ⟩ q' hq' hSide
      have hηrep : η • τ₀ = rep q • τ₀ := by rw [hητ, (hrep q hqP).2]
      have htrans : IsSideElement Γ τ₀ (η⁻¹ * rep q') := by
        refine (isSideElement_congr ?_).mpr hSide
        exact transition_basepoint_eq hfree hηrep rfl
      refine ⟨hq', p ++ [rep q'], ?_, ?_, rep q', ?_, (hrep q' hq').2⟩
      · refine hp.append (List.isChain_singleton _) ?_
        intro x hx y hy
        rw [plast, Option.mem_some_iff] at hx
        rw [List.head?_cons, Option.mem_some_iff] at hy
        rw [← hx, ← hy]
        exact htrans
      · cases p with
        | nil => simp at phead
        | cons a l =>
          rw [List.cons_append, List.head?_cons]
          rw [List.head?_cons] at phead
          exact phead
      · rw [List.getLast?_concat]
    have hβS : β • τ₀ ∈ S := by
      rw [hSeq]
      exact ⟨β, hβ, rfl⟩
    obtain ⟨-, p, hp, hh, η, hl, hη⟩ := hβS
    exact ⟨p, hp, hh, η, hl, hη⟩
  · have h1c : (1 : ↥Γ) ∈ contactSet Γ τ₀ z := one_mem_contactSet hz
    have hzs : z ∈ dirichletSideSet Γ τ₀ β := by
      have h := smul_mem_dirichletSideSet_of_contact_pair h1c hβ
      rwa [inv_one, one_mul, one_smul] at h
    have hnontriv : (dirichletSideSet Γ τ₀ β).Nontrivial := by
      by_contra hnt
      rw [Set.not_nontrivial_iff] at hnt
      have hsing : dirichletSideSet Γ τ₀ β = {z} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨hzs, fun x hx => hnt hx hzs⟩
      have hvert := mem_polygonVertices_of_sideSet_eq_singleton hΓ hfree hε hgap hdense
        hβτ hsing
      exact hcard hvert.2
    refine ⟨[1, β], ?_, rfl, β, rfl, rfl⟩
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
    have he : (1 : ↥Γ)⁻¹ * β = β := by group
    rw [he]
    exact ⟨hβτ, hnontriv⟩

/-- Any two contact tiles of a point are joined by a tile path from the first tile to a
tile with the basepoint image of the second: translate the star to the base tile and
chain there. -/
theorem chain_of_contact (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {z : UpperHalfPlane} {γ δ : ↥Γ} (hγ : γ ∈ contactSet Γ τ₀ z)
    (hδ : δ ∈ contactSet Γ τ₀ z) :
    ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ p.head? = some γ ∧
      ∃ η : ↥Γ, p.getLast? = some η ∧ η • τ₀ = δ • τ₀ := by
  have hz' : γ⁻¹ • z ∈ dirichletDomain Γ τ₀ := by
    obtain ⟨u, hu, huz⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain γ z).mp hγ
    have h : γ • u = z := huz
    rw [← h, inv_smul_smul]
    exact hu
  have hβ : (γ⁻¹ * δ) ∈ contactSet Γ τ₀ (γ⁻¹ • z) := (contact_shift γ⁻¹ δ z).mp hδ
  obtain ⟨p, hp, hh, η, hl, hη⟩ :=
    chain_of_contact_base hΓ hfree hε hgap hdense hz' hβ
  refine ⟨p.map (γ * ·), isTilePath_map γ hp, ?_, γ * η, ?_, ?_⟩
  · rw [List.head?_map, hh]
    simp
  · rw [List.getLast?_map, hl]
    rfl
  · rw [mul_smul, hη, mul_smul, ← mul_smul γ γ⁻¹, mul_inv_cancel, one_smul]

/-- Every tile is reachable from the base tile by a tile path: the star covering along the
geodesic segment from the basepoint to the tile center yields a chain of tiles in which
consecutive tiles share genuine sides. -/
theorem exists_tilePath_to (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (γ : ↥Γ) :
    ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ p.head? = some 1 ∧
      ∃ δ : ↥Γ, p.getLast? = some δ ∧ δ • τ₀ = γ • τ₀ := by
  classical
  set c : ℝ → UpperHalfPlane := fun t => geodInterp τ₀ (γ • τ₀) t with hc
  have hcont : Continuous c := continuous_geodInterp.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  set P : ℝ → Prop := fun t => ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ p.head? = some 1 ∧
    ∃ η : ↥Γ, p.getLast? = some η ∧ η ∈ contactSet Γ τ₀ (c t) with hPdef
  have hstep : ∀ (w : UpperHalfPlane) (r : ℝ), 0 < r →
      (∀ g : ↥Γ, ((g • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball w r).Nonempty →
        g ∈ contactSet Γ τ₀ w) →
      (∀ u ∈ Metric.ball w r, ∃ g ∈ contactSet Γ τ₀ w,
        u ∈ (g • ·) '' dirichletDomain Γ τ₀) →
      ∀ t₁ t₂ : ℝ, c t₁ ∈ Metric.ball w r → c t₂ ∈ Metric.ball w r → P t₁ → P t₂ := by
    rintro w r hr hmeets hcover t₁ t₂ h₁ h₂ ⟨p, hp, phead, η, plast, hηc⟩
    have hηw : η ∈ contactSet Γ τ₀ w :=
      hmeets η ⟨c t₁, (mem_contactSet_iff_mem_smul_dirichletDomain η (c t₁)).mp hηc, h₁⟩
    obtain ⟨δ, hδw, hδt⟩ := hcover (c t₂) h₂
    have hδc : δ ∈ contactSet Γ τ₀ (c t₂) :=
      (mem_contactSet_iff_mem_smul_dirichletDomain δ (c t₂)).mpr hδt
    obtain ⟨q, hq, qhead, η₂, qlast, hη₂⟩ :=
      chain_of_contact hΓ hfree hε hgap hdense hηw hδw
    have hη₂c : η₂ ∈ contactSet Γ τ₀ (c t₂) := mem_contactSet_congr hη₂.symm hδc
    cases q with
    | nil => simp at qhead
    | cons η' q₁ =>
      rw [List.head?_cons, Option.some_inj] at qhead
      cases q₁ with
      | nil =>
        rw [List.getLast?_singleton, Option.some_inj] at qlast
        rw [qhead] at qlast
        exact ⟨p, hp, phead, η, plast, by rw [qlast]; exact hη₂c⟩
      | cons b q₂ =>
        obtain ⟨hR, hchain⟩ := List.isChain_cons_cons.mp hq
        refine ⟨p ++ b :: q₂, ?_, ?_, η₂, ?_, hη₂c⟩
        · refine List.isChain_append.mpr ⟨hp, hchain, ?_⟩
          intro x hx y hy
          rw [plast, Option.mem_some_iff] at hx
          rw [List.head?_cons, Option.mem_some_iff] at hy
          rw [← hx, ← hy]
          rw [qhead] at hR
          exact hR
        · cases p with
          | nil => simp at phead
          | cons a l =>
            rw [List.cons_append, List.head?_cons]
            rw [List.head?_cons] at phead
            exact phead
        · rw [List.getLast?_append_cons, ← List.getLast?_cons_cons (a := η') (b := b)]
          exact qlast
  have hP0 : P 0 := by
    refine ⟨[1], List.isChain_singleton _, rfl, 1, rfl, ?_⟩
    have h0 : c 0 = τ₀ := geodInterp_zero τ₀ (γ • τ₀)
    rw [h0]
    exact one_mem_contactSet basepoint_mem_dirichletDomain
  set T : Set ℝ := {t | t ≤ 1 ∧ P t} with hT
  have hT0 : (0 : ℝ) ∈ T := ⟨by norm_num, hP0⟩
  have hTbdd : BddAbove T := ⟨1, fun t ht => ht.1⟩
  set s₀ : ℝ := sSup T with hs₀
  have hs₀le : s₀ ≤ 1 := csSup_le ⟨0, hT0⟩ fun t ht => ht.1
  obtain ⟨r, hr, hmeets, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ (c s₀)
  obtain ⟨θ, hθ, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt r hr
  have hnear : ∀ t : ℝ, |t - s₀| < θ → c t ∈ Metric.ball (c s₀) r := by
    intro t ht
    exact Metric.mem_ball.mpr (hball (by rwa [Real.dist_eq]))
  obtain ⟨t₁, ht₁T, ht₁⟩ :=
    exists_lt_of_lt_csSup ⟨0, hT0⟩ (by linarith : s₀ - θ < s₀)
  have ht₁le : t₁ ≤ s₀ := le_csSup hTbdd ht₁T
  have ht₁near : c t₁ ∈ Metric.ball (c s₀) r := by
    refine hnear t₁ ?_
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  set t₂ : ℝ := min 1 (s₀ + θ / 2) with ht₂def
  have ht₂ub : t₂ ≤ s₀ + θ / 2 := min_le_right _ _
  have ht₂lb : s₀ ≤ t₂ := le_min hs₀le (by linarith)
  have ht₂near : c t₂ ∈ Metric.ball (c s₀) r := by
    refine hnear t₂ ?_
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hPt₂ : P t₂ := hstep (c s₀) r hr hmeets hcover t₁ t₂ ht₁near ht₂near ht₁T.2
  have ht₂T : t₂ ∈ T := ⟨min_le_left _ _, hPt₂⟩
  have ht₂le : t₂ ≤ s₀ := le_csSup hTbdd ht₂T
  have hs₀1 : 1 ≤ s₀ := by
    by_contra h
    rw [not_le] at h
    have hlt : s₀ < t₂ := lt_min h (by linarith)
    linarith
  have ht₂1 : t₂ = 1 := by
    refine le_antisymm (min_le_left _ _) ?_
    rw [ht₂def]
    exact le_min le_rfl (by linarith)
  rw [ht₂1] at hPt₂
  obtain ⟨p, hp, phead, η, plast, hηc⟩ := hPt₂
  refine ⟨p, hp, phead, η, plast, ?_⟩
  have hc1 : c 1 = γ • τ₀ := geodInterp_one τ₀ (γ • τ₀)
  rw [hc1] at hηc
  have hint : γ • τ₀ ∈ (γ • ·) '' interior (dirichletDomain Γ τ₀) :=
    ⟨τ₀, basepoint_mem_interior_dirichletDomain hε hgap, rfl⟩
  have hcs := (mem_smul_interior_iff_contactSet_eq hΓ hdense γ (γ • τ₀)).mp hint
  have hfin : η ∈ {δ : ↥Γ | δ • τ₀ = γ • τ₀} := by
    rw [← hcs]
    exact hηc
  exact hfin

/-- Along a tile path every element lies in a subgroup containing the side elements, once
the head does: the successive transitions telescope. -/
theorem tilePath_mem_closure {K : Subgroup ↥Γ}
    (hK : ∀ β : ↥Γ, IsSideElement Γ τ₀ β → β ∈ K) :
    ∀ p : List ↥Γ, IsTilePath Γ τ₀ p → ∀ a : ↥Γ, p.head? = some a → a ∈ K →
      ∀ b : ↥Γ, p.getLast? = some b → b ∈ K := by
  intro p
  induction p with
  | nil =>
    intro _ a hhead
    simp at hhead
  | cons x l ih =>
    intro hp a hhead haK b hb
    rw [List.head?_cons, Option.some_inj] at hhead
    subst hhead
    cases l with
    | nil =>
      rw [List.getLast?_singleton, Option.some_inj] at hb
      rwa [← hb]
    | cons y l' =>
      obtain ⟨hR, hchain⟩ := List.isChain_cons_cons.mp hp
      rw [List.getLast?_cons_cons] at hb
      refine ih hchain y rfl ?_ b hb
      have h1 : y = x * (x⁻¹ * y) := by group
      rw [h1]
      exact K.mul_mem haK (hK _ hR)

/-- The side elements, together with the trivially-acting elements, generate the group:
walking along the segment from the basepoint to any orbit point crosses finitely many
tiles, consecutive tiles sharing genuine sides. -/
theorem closure_sideElements_eq_top (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Subgroup.closure ({δ : ↥Γ | IsSideElement Γ τ₀ δ} ∪
      {δ : ↥Γ | ∀ τ : UpperHalfPlane, δ • τ = τ}) = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  obtain ⟨p, hp, phead, δ, plast, hδγ⟩ :=
    exists_tilePath_to hΓ hfree hε hgap hdense γ
  have hδK : δ ∈ Subgroup.closure ({δ : ↥Γ | IsSideElement Γ τ₀ δ} ∪
      {δ : ↥Γ | ∀ τ : UpperHalfPlane, δ • τ = τ}) :=
    tilePath_mem_closure (fun β hβ => Subgroup.subset_closure (Or.inl hβ)) p hp 1 phead
      (Subgroup.one_mem _) δ plast
  have hfix : (δ⁻¹ * γ) • τ₀ = τ₀ := by
    rw [mul_smul, ← hδγ, inv_smul_smul]
  have htriv : ∀ τ : UpperHalfPlane, (δ⁻¹ * γ) • τ = τ := hfree (δ⁻¹ * γ) ⟨τ₀, hfix⟩
  have h2 : (δ⁻¹ * γ) ∈ Subgroup.closure ({δ : ↥Γ | IsSideElement Γ τ₀ δ} ∪
      {δ : ↥Γ | ∀ τ : UpperHalfPlane, δ • τ = τ}) :=
    Subgroup.subset_closure (Or.inr htriv)
  have h3 : γ = δ * (δ⁻¹ * γ) := by group
  rw [h3]
  exact Subgroup.mul_mem _ hδK h2

/-! ## Crossing-sum list calculus -/

/-- The empty path has zero crossing sum. -/
theorem crossingSum_nil (α : (↥Γ) → ℝ) : crossingSum α ([] : List ↥Γ) = 0 := by
  simp [crossingSum]

/-- Left translation of a path leaves the crossing sum unchanged: the transition elements
are unchanged. -/
theorem crossingSum_map_mul (α : (↥Γ) → ℝ) (g : ↥Γ) (p : List ↥Γ) :
    crossingSum α (p.map (g * ·)) = crossingSum α p := by
  induction p with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l' =>
      rw [List.map_cons, List.map_cons, crossingSum_cons_cons,
        crossingSum_cons_cons, ← List.map_cons]
      have he : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
      rw [he, ih]

/-- Crossing sums add along a junction: appending a path continuing from the last element
adds the crossing sums. -/
theorem crossingSum_glue_aux (α : (↥Γ) → ℝ) (a : ↥Γ) (q' : List ↥Γ) :
    ∀ p₀ : List ↥Γ, crossingSum α (p₀ ++ a :: q')
      = crossingSum α (p₀ ++ [a]) + crossingSum α (a :: q') := by
  intro p₀
  induction p₀ with
  | nil =>
    rw [List.nil_append, List.nil_append, crossingSum_singleton]
    ring
  | cons x p₀' ih =>
    cases p₀' with
    | nil =>
      rw [List.cons_append, List.nil_append, crossingSum_cons_cons,
        List.cons_append, List.nil_append, crossingSum_cons_cons,
        crossingSum_singleton]
      ring
    | cons y r =>
      rw [List.cons_append, List.cons_append, crossingSum_cons_cons,
        ← List.cons_append, ih]
      simp only [List.cons_append, crossingSum_cons_cons]
      ring

/-- Gluing two paths at a shared junction element adds the crossing sums. -/
theorem crossingSum_glue (α : (↥Γ) → ℝ) {p q : List ↥Γ} {a : ↥Γ}
    (hp : p.getLast? = some a) (hq : q.head? = some a) :
    crossingSum α (p ++ q.tail) = crossingSum α p + crossingSum α q := by
  obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.mp hq
  obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp hp
  rw [List.tail_cons, List.append_assoc, List.singleton_append,
    crossingSum_glue_aux]

/-- Reversal negates the crossing sum of an odd function. -/
theorem crossingSum_reverse {α : (↥Γ) → ℝ} (hodd : ∀ γ : ↥Γ, α γ⁻¹ = -α γ)
    (p : List ↥Γ) : crossingSum α p.reverse = -crossingSum α p := by
  induction p with
  | nil => simp [crossingSum]
  | cons a l ih =>
    cases l with
    | nil => simp [crossingSum]
    | cons b r =>
      have hlast : (b :: r).reverse.getLast? = some b := by
        rw [List.getLast?_reverse]
        rfl
      have hq : ([b, a] : List ↥Γ).head? = some b := rfl
      have hglue := crossingSum_glue α hlast hq
      rw [show ([b, a] : List ↥Γ).tail = [a] from rfl] at hglue
      rw [List.reverse_cons, hglue, ih, crossingSum_cons_cons,
        crossingSum_singleton, crossingSum_cons_cons]
      have h2 : α (b⁻¹ * a) = -α (a⁻¹ * b) := by
        rw [show b⁻¹ * a = (a⁻¹ * b)⁻¹ by group]
        exact hodd _
      rw [h2]
      ring

/-- Reversal preserves tile paths: the transitions invert. -/
theorem isTilePath_reverse {p : List ↥Γ} (hp : IsTilePath Γ τ₀ p) :
    IsTilePath Γ τ₀ p.reverse := by
  rw [IsTilePath, List.isChain_reverse]
  refine hp.imp fun a b h => ?_
  have he : b⁻¹ * a = (a⁻¹ * b)⁻¹ := by group
  rw [he]
  exact h.inv

/-- Gluing two tile paths at a shared junction element yields a tile path. -/
theorem isTilePath_glue {p q : List ↥Γ} {a : ↥Γ} (hp : IsTilePath Γ τ₀ p)
    (hq : IsTilePath Γ τ₀ q) (hpl : p.getLast? = some a) (hqh : q.head? = some a) :
    IsTilePath Γ τ₀ (p ++ q.tail) := by
  obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.mp hqh
  rw [List.tail_cons]
  refine List.isChain_append.mpr ⟨hp, ?_, ?_⟩
  · cases q' with
    | nil => exact List.isChain_nil
    | cons y r => exact (List.isChain_cons_cons.mp hq).2
  · intro x hx y hy
    rw [hpl, Option.mem_some_iff] at hx
    cases q' with
    | nil => simp at hy
    | cons y' r =>
      rw [List.head?_cons, Option.mem_some_iff] at hy
      rw [← hx, ← hy]
      exact (List.isChain_cons_cons.mp hq).1

/-- The head of a glued path is the head of the first factor. -/
theorem head?_glue {p q : List ↥Γ} {a : ↥Γ} (hpl : p.getLast? = some a) :
    (p ++ q.tail).head? = p.head? := by
  obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp hpl
  cases p₀ with
  | nil => cases q <;> rfl
  | cons x r => rw [List.cons_append, List.head?_cons, List.cons_append, List.head?_cons]

/-- The last element of a glued path with nontrivial second factor tail. -/
theorem getLast?_glue {p q : List ↥Γ} {a : ↥Γ} (hpl : p.getLast? = some a)
    (hq : q.head? = some a) : (p ++ q.tail).getLast? = q.getLast? := by
  obtain ⟨q', rfl⟩ := List.head?_eq_some_iff.mp hq
  rw [List.tail_cons]
  cases q' with
  | nil => rw [List.append_nil, hpl, List.getLast?_singleton]
  | cons y r =>
    rw [List.getLast?_append_of_ne_nil p (List.cons_ne_nil y r), List.getLast?_cons_cons]

/-- Swapping the last element of a path for one with the same basepoint image preserves the
crossing sum of a fiber-constant function. -/
theorem crossingSum_congr_last {α : (↥Γ) → ℝ}
    (hfib : ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ) {b e : ↥Γ} (hbe : b • τ₀ = e • τ₀) :
    ∀ p₀ : List ↥Γ, crossingSum α (p₀ ++ [b]) = crossingSum α (p₀ ++ [e]) := by
  intro p₀
  induction p₀ with
  | nil => rw [List.nil_append, List.nil_append, crossingSum_singleton,
      crossingSum_singleton]
  | cons x r ih =>
    cases r with
    | nil =>
      simp only [List.cons_append, List.nil_append, crossingSum_cons_cons,
        crossingSum_singleton]
      have h1 : (x⁻¹ * b) • τ₀ = (x⁻¹ * e) • τ₀ := by
        rw [mul_smul, mul_smul, hbe]
      rw [hfib _ _ h1]
    | cons y r' =>
      simp only [List.cons_append, crossingSum_cons_cons]
      rw [show (y :: r') ++ [b] = (y :: r') ++ [b] from rfl] at ih
      simp only [List.cons_append] at ih
      rw [ih]

/-- Swapping the last element for one with the same basepoint image preserves tile paths. -/
theorem isTilePath_congr_last
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {b e : ↥Γ} (hbe : b • τ₀ = e • τ₀) :
    ∀ p₀ : List ↥Γ, IsTilePath Γ τ₀ (p₀ ++ [b]) → IsTilePath Γ τ₀ (p₀ ++ [e]) := by
  intro p₀
  induction p₀ with
  | nil => intro _; exact List.isChain_singleton e
  | cons x r ih =>
    cases r with
    | nil =>
      intro hp
      simp only [List.cons_append, List.nil_append] at hp ⊢
      have hR := (List.isChain_cons_cons.mp hp).1
      refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton e⟩
      have h1 : (x⁻¹ * b) • τ₀ = (x⁻¹ * e) • τ₀ :=
        transition_basepoint_eq hfree rfl hbe
      exact (isSideElement_congr h1).mp hR
    | cons y r' =>
      intro hp
      simp only [List.cons_append] at hp ⊢
      obtain ⟨hR, hchain⟩ := List.isChain_cons_cons.mp hp
      have hrec := ih (by simpa using hchain)
      refine List.isChain_cons_cons.mpr ⟨hR, by simpa using hrec⟩

/-- Discrete fundamental theorem: a crossing sum telescopes along a potential adapted to
the transitions of the path. -/
theorem crossingSum_telescope (α : (↥Γ) → ℝ) (h : ↥Γ → ℝ) :
    ∀ p : List ↥Γ, IsTilePath Γ τ₀ p →
      (∀ x ∈ p, ∀ y ∈ p, IsSideElement Γ τ₀ (x⁻¹ * y) → α (x⁻¹ * y) = h y - h x) →
      ∀ {a b : ↥Γ}, p.head? = some a → p.getLast? = some b →
      crossingSum α p = h b - h a := by
  intro p
  induction p with
  | nil =>
    intro _ _ a b ha
    simp at ha
  | cons x l ih =>
    intro hp hrel a b ha hb
    rw [List.head?_cons, Option.some_inj] at ha
    subst ha
    cases l with
    | nil =>
      rw [List.getLast?_singleton, Option.some_inj] at hb
      subst hb
      rw [crossingSum_singleton]
      ring
    | cons y r =>
      obtain ⟨hR, hchain⟩ := List.isChain_cons_cons.mp hp
      rw [List.getLast?_cons_cons] at hb
      have hstep := hrel x (List.mem_cons_self) y (by simp) hR
      have hrec := ih hchain
        (fun u hu v hv => hrel u (List.mem_cons_of_mem x hu) v (List.mem_cons_of_mem x hv))
        rfl hb
      rw [crossingSum_cons_cons, hstep, hrec]
      ring

/-- The crossing sum as an indexed sum over the transitions. -/
theorem crossingSum_eq_sum_range (α : (↥Γ) → ℝ) :
    ∀ p : List ↥Γ, crossingSum α p
      = ∑ k ∈ Finset.range (p.length - 1), α ((p.getD k 1)⁻¹ * p.getD (k + 1) 1) := by
  intro p
  induction p with
  | nil => simp [crossingSum]
  | cons a l ih =>
    cases l with
    | nil => simp [crossingSum]
    | cons b r =>
      rw [crossingSum_cons_cons, ih]
      have hlen : (a :: b :: r).length - 1 = ((b :: r).length - 1) + 1 := by
        simp [List.length_cons]
      rw [hlen, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.length_cons,
        Nat.add_sub_cancel]
      ring

/-- Fetching with a default at an index below the length is fetching. -/
theorem getD_eq_getElem {β : Type*} (l : List β) (d : β) {n : ℕ} (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The transitions of a tile path, in indexed form. -/
theorem isTilePath_getD {p : List ↥Γ} (hp : IsTilePath Γ τ₀ p) :
    ∀ k : ℕ, k + 1 < p.length → IsSideElement Γ τ₀ ((p.getD k 1)⁻¹ * p.getD (k + 1) 1) := by
  intro k hk
  have h := List.isChain_iff_getElem.mp hp k hk
  rwa [getD_eq_getElem p 1 (by omega), getD_eq_getElem p 1 hk]

/-- The head of a list in indexed form. -/
theorem head_getD {p : List ↥Γ} {a : ↥Γ} (h : p.head? = some a) : p.getD 0 1 = a := by
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp h
  rfl

/-- The last element of a list in indexed form. -/
theorem getLast_getD {p : List ↥Γ} {b : ↥Γ} (h : p.getLast? = some b) :
    p.getD (p.length - 1) 1 = b := by
  have h1 : p.getLast? = p[p.length - 1]? := List.getLast?_eq_getElem?
  rw [h] at h1
  have hne : p ≠ [] := by
    rintro rfl
    simp at h
  have hlt : p.length - 1 < p.length := by
    have : 0 < p.length := List.length_pos_iff.mpr hne
    omega
  rw [getD_eq_getElem p 1 hlt]
  have h2 := List.getElem?_eq_getElem hlt
  rw [← h1, Option.some_inj] at h2
  exact h2.symm

/-! ## Star chains: tile paths inside the contact star of a point -/

/-- Any contact tile of a domain point is reached from the base tile by a tile path all of
whose tiles touch the point: within the star, tiles chain by genuine side sharing. -/
theorem chain_of_contact_base_star (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) {β : ↥Γ}
    (hβ : β ∈ contactSet Γ τ₀ z) :
    ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ (∀ g ∈ p, g ∈ contactSet Γ τ₀ z) ∧
      p.head? = some 1 ∧ ∃ η : ↥Γ, p.getLast? = some η ∧ η • τ₀ = β • τ₀ := by
  classical
  have h1c : (1 : ↥Γ) ∈ contactSet Γ τ₀ z := one_mem_contactSet hz
  by_cases hβτ : β • τ₀ = τ₀
  · exact ⟨[1], List.isChain_singleton _, by simpa using h1c, rfl, 1, rfl,
      by rw [one_smul, hβτ]⟩
  by_cases hcard : 3 ≤ (tileCenters Γ τ₀ z).ncard
  · have hv : z ∈ polygonVertices Γ τ₀ := ⟨hz, hcard⟩
    have hrepex : ∀ q : UpperHalfPlane, ∃ g : ↥Γ,
        q ∈ tileCenters Γ τ₀ z → g ∈ contactSet Γ τ₀ z ∧ g • τ₀ = q := by
      intro q
      by_cases hq : q ∈ tileCenters Γ τ₀ z
      · obtain ⟨g, hg, hgq⟩ := hq
        exact ⟨g, fun _ => ⟨hg, hgq⟩⟩
      · exact ⟨1, fun h => absurd h hq⟩
    choose rep hrep using hrepex
    set S : Set UpperHalfPlane := {q | q ∈ tileCenters Γ τ₀ z ∧
      ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ (∀ g ∈ p, g ∈ contactSet Γ τ₀ z) ∧
        p.head? = some 1 ∧ ∃ η : ↥Γ, p.getLast? = some η ∧ η • τ₀ = q} with hS
    have hτ₀S : τ₀ ∈ S := ⟨⟨1, h1c, one_smul _ τ₀⟩, [1],
      List.isChain_singleton _, by simpa using h1c, rfl, 1, rfl, one_smul _ τ₀⟩
    have hSeq : S = tileCenters Γ τ₀ z := by
      refine adj_closed_eq hΓ hfree hv (fun q hq => (hrep q hq).1)
        (fun q hq => (hrep q hq).2) (fun q hq => hq.1) ⟨τ₀, hτ₀S⟩ ?_
      rintro q ⟨hqP, p, hp, hpmem, phead, η, plast, hητ⟩ q' hq' hSide
      have hηrep : η • τ₀ = rep q • τ₀ := by rw [hητ, (hrep q hqP).2]
      have htrans : IsSideElement Γ τ₀ (η⁻¹ * rep q') := by
        refine (isSideElement_congr ?_).mpr hSide
        exact transition_basepoint_eq hfree hηrep rfl
      refine ⟨hq', p ++ [rep q'], ?_, ?_, ?_, rep q', ?_, (hrep q' hq').2⟩
      · refine hp.append (List.isChain_singleton _) ?_
        intro x hx y hy
        rw [plast, Option.mem_some_iff] at hx
        rw [List.head?_cons, Option.mem_some_iff] at hy
        rw [← hx, ← hy]
        exact htrans
      · intro g hg
        rcases List.mem_append.mp hg with hgp | hgq
        · exact hpmem g hgp
        · rw [List.mem_singleton.mp hgq]
          exact (hrep q' hq').1
      · cases p with
        | nil => simp at phead
        | cons a l =>
          rw [List.cons_append, List.head?_cons]
          rw [List.head?_cons] at phead
          exact phead
      · rw [List.getLast?_concat]
    have hβS : β • τ₀ ∈ S := by
      rw [hSeq]
      exact ⟨β, hβ, rfl⟩
    obtain ⟨-, p, hp, hpmem, hh, η, hl, hη⟩ := hβS
    exact ⟨p, hp, hpmem, hh, η, hl, hη⟩
  · have hzs : z ∈ dirichletSideSet Γ τ₀ β := by
      have h := smul_mem_dirichletSideSet_of_contact_pair h1c hβ
      rwa [inv_one, one_mul, one_smul] at h
    have hnontriv : (dirichletSideSet Γ τ₀ β).Nontrivial := by
      by_contra hnt
      rw [Set.not_nontrivial_iff] at hnt
      have hsing : dirichletSideSet Γ τ₀ β = {z} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨hzs, fun x hx => hnt hx hzs⟩
      have hvert := mem_polygonVertices_of_sideSet_eq_singleton hΓ hfree hε hgap hdense
        hβτ hsing
      exact hcard hvert.2
    refine ⟨[1, β], ?_, ?_, rfl, β, rfl, rfl⟩
    · refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
      have he : (1 : ↥Γ)⁻¹ * β = β := by group
      rw [he]
      exact ⟨hβτ, hnontriv⟩
    · intro g hg
      rcases List.mem_cons.mp hg with h | h
      · rw [h]; exact h1c
      · rw [List.mem_singleton.mp h]; exact hβ

/-- Any two contact tiles of a point are joined by a tile path staying in the star of the
point, from the first tile to a tile with the basepoint image of the second. -/
theorem chain_of_contact_star (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {z : UpperHalfPlane} {γ δ : ↥Γ} (hγ : γ ∈ contactSet Γ τ₀ z)
    (hδ : δ ∈ contactSet Γ τ₀ z) :
    ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ (∀ g ∈ p, g ∈ contactSet Γ τ₀ z) ∧
      p.head? = some γ ∧ ∃ η : ↥Γ, p.getLast? = some η ∧ η • τ₀ = δ • τ₀ := by
  have hz' : γ⁻¹ • z ∈ dirichletDomain Γ τ₀ := by
    obtain ⟨u, hu, huz⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain γ z).mp hγ
    have h : γ • u = z := huz
    rw [← h, inv_smul_smul]
    exact hu
  have hβ : (γ⁻¹ * δ) ∈ contactSet Γ τ₀ (γ⁻¹ • z) := (contact_shift γ⁻¹ δ z).mp hδ
  obtain ⟨p, hp, hmem, hh, η, hl, hη⟩ :=
    chain_of_contact_base_star hΓ hfree hε hgap hdense hz' hβ
  refine ⟨p.map (γ * ·), isTilePath_map γ hp, ?_, ?_, γ * η, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    have h2 := (contact_shift γ x (γ⁻¹ • z)).mp (hmem x hx)
    rwa [smul_inv_smul] at h2
  · rw [List.head?_map, hh]
    simp
  · rw [List.getLast?_map, hl]
    rfl
  · rw [mul_smul, hη, mul_smul, ← mul_smul γ γ⁻¹, mul_inv_cancel, one_smul]

/-! ## The star lemma: crossing sums of star loops vanish -/

/-- Base form of the star lemma: a tile path inside the star of a domain point, from the
base tile back to a tile with basepoint image `τ₀`, has zero crossing sum. At a vertex the
loop closes up to a vertex loop killed by the constraint; at a side or interior point the
two-tile alternation telescopes and is killed by oddness. -/
theorem star_zero_base (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) {p : List ↥Γ}
    (hp : IsTilePath Γ τ₀ p) (hmem : ∀ g ∈ p, g ∈ contactSet Γ τ₀ z)
    (hhead : p.head? = some 1) {b : ↥Γ} (hlast : p.getLast? = some b)
    (hb : b • τ₀ = τ₀) : crossingSum α p = 0 := by
  classical
  obtain ⟨⟨hzero, hodd, hfib⟩, hloop⟩ := mem_cycleConstrained.mp hα
  obtain ⟨p₀, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  cases p₀ with
  | nil => exact crossingSum_singleton α b
  | cons x r =>
    have hhead' : x = 1 := by
      rw [List.cons_append, List.head?_cons, Option.some_inj] at hhead
      exact hhead
    subst hhead'
    by_cases hcard : 3 ≤ (tileCenters Γ τ₀ z).ncard
    · -- vertex case: close the loop exactly and apply the constraint
      have hbe : b • τ₀ = (1 : ↥Γ) • τ₀ := by rw [hb, one_smul]
      have hsum := crossingSum_congr_last hfib hbe (1 :: r)
      have hpath := isTilePath_congr_last hfree hbe (1 :: r) hp
      have hloopmem : ∀ g ∈ (1 :: r) ++ [(1 : ↥Γ)], g ∈ contactSet Γ τ₀ z := by
        intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hmem g (List.mem_append.mpr (Or.inl h))
        · rw [List.mem_singleton.mp h]
          exact one_mem_contactSet hz
      have hvloop : IsVertexLoop Γ τ₀ z ((1 :: r) ++ [(1 : ↥Γ)]) := by
        refine ⟨hpath, hloopmem, ?_⟩
        rw [List.cons_append, List.head?_cons, ← List.cons_append, List.getLast?_concat]
      rw [hsum]
      exact hloop z ⟨hz, hcard⟩ _ hvloop
    · -- at most two tiles: telescope against a two-valued potential
      have hfin : (tileCenters Γ τ₀ z).Finite :=
        (finite_contactSet hΓ τ₀ z).image _
      have hτ₀mem : τ₀ ∈ tileCenters Γ τ₀ z := ⟨1, one_mem_contactSet hz, one_smul _ _⟩
      obtain ⟨w, β, hβc, hβw, hdich⟩ : ∃ (w : UpperHalfPlane) (β : ↥Γ),
          β ∈ contactSet Γ τ₀ z ∧ β • τ₀ = w ∧
            ∀ u ∈ tileCenters Γ τ₀ z, u = τ₀ ∨ u = w := by
        by_cases hex : ∃ u ∈ tileCenters Γ τ₀ z, u ≠ τ₀
        · obtain ⟨w, hw, hwne⟩ := hex
          obtain ⟨β, hβc, hβw⟩ := hw
          refine ⟨w, β, hβc, hβw, fun u hu => ?_⟩
          by_contra hcon
          push Not at hcon
          refine hcard ?_
          have h3 : ({τ₀, w, u} : Set UpperHalfPlane).ncard = 3 :=
            Set.ncard_eq_three.mpr ⟨τ₀, w, u, fun h => hwne h.symm,
              fun h => hcon.1 h.symm, fun h => hcon.2 h.symm, rfl⟩
          rw [← h3]
          refine Set.ncard_le_ncard ?_ hfin
          intro v hv
          rcases hv with h | h | h
          · rw [h]; exact hτ₀mem
          · rw [h]; exact ⟨β, hβc, hβw⟩
          · rw [h]; exact hu
        · push Not at hex
          exact ⟨τ₀, 1, one_mem_contactSet hz, one_smul _ _, fun u hu => Or.inl (hex u hu)⟩
      set h : ↥Γ → ℝ := fun g => if g • τ₀ = τ₀ then 0 else α β with hh
      have htriv : ∀ g : ↥Γ, g • τ₀ = τ₀ → ∀ σ : UpperHalfPlane, g⁻¹ • σ = σ := by
        intro g hg σ
        have hg' := hfree g ⟨τ₀, hg⟩
        conv_lhs => rw [← hg' (g⁻¹ • σ)]
        rw [smul_inv_smul]
      have hrel : ∀ x ∈ (1 : ↥Γ) :: r ++ [b], ∀ y ∈ (1 : ↥Γ) :: r ++ [b],
          IsSideElement Γ τ₀ (x⁻¹ * y) → α (x⁻¹ * y) = h y - h x := by
        intro x hx y hy hside
        have hxc : x • τ₀ ∈ tileCenters Γ τ₀ z := ⟨x, hmem x hx, rfl⟩
        have hyc : y • τ₀ ∈ tileCenters Γ τ₀ z := ⟨y, hmem y hy, rfl⟩
        by_cases hxx : x • τ₀ = τ₀ <;> by_cases hyy : y • τ₀ = τ₀
        · exact absurd (by rw [mul_smul, hyy, htriv x hxx]) hside.1
        · have hyw : y • τ₀ = w := (hdich _ hyc).resolve_left hyy
          have he : (x⁻¹ * y) • τ₀ = β • τ₀ := by
            rw [mul_smul, hyw, ← hβw, htriv x hxx]
          rw [hfib _ _ he, hh]
          simp only []
          rw [if_neg hyy, if_pos hxx]
          ring
        · have hxw : x • τ₀ = w := (hdich _ hxc).resolve_left hxx
          have he : (x⁻¹ * y) • τ₀ = β⁻¹ • τ₀ := by
            rw [mul_smul, hyy]
            exact inv_smul_eq_of_basepoint_eq hfree (hxw.trans hβw.symm) τ₀
          rw [hfib _ _ he, hodd, hh]
          simp only []
          rw [if_neg hxx, if_pos hyy]
          ring
        · have hxw : x • τ₀ = w := (hdich _ hxc).resolve_left hxx
          have hyw : y • τ₀ = w := (hdich _ hyc).resolve_left hyy
          have he : (x⁻¹ * y) • τ₀ = τ₀ := by
            rw [mul_smul, hyw, ← hxw, inv_smul_smul]
          exact absurd he hside.1
      have htel := crossingSum_telescope α h ((1 : ↥Γ) :: r ++ [b]) hp hrel
        (by rw [List.cons_append, List.head?_cons]) hlast
      rw [htel, hh]
      simp only []
      rw [if_pos hb, if_pos (one_smul _ τ₀)]
      ring

/-- **The star lemma**: a tile path inside the star of any point, whose head and last tiles
have the same basepoint image, has zero crossing sum. -/
theorem star_zero (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {p : List ↥Γ}
    (hp : IsTilePath Γ τ₀ p) (hmem : ∀ g ∈ p, g ∈ contactSet Γ τ₀ z)
    {a b : ↥Γ} (hhead : p.head? = some a) (hlast : p.getLast? = some b)
    (hab : a • τ₀ = b • τ₀) : crossingSum α p = 0 := by
  have haz : a ∈ contactSet Γ τ₀ z := by
    obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hhead
    exact hmem a List.mem_cons_self
  have hz' : a⁻¹ • z ∈ dirichletDomain Γ τ₀ := by
    obtain ⟨u, hu, huz⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain a z).mp haz
    have h : a • u = z := huz
    rw [← h, inv_smul_smul]
    exact hu
  have hsum := crossingSum_map_mul α a⁻¹ p
  rw [← hsum]
  refine star_zero_base hΓ hfree hα hz' (isTilePath_map a⁻¹ hp) ?_ ?_
    (b := a⁻¹ * b) ?_ ?_
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    exact (contact_shift a⁻¹ x z).mp (hmem x hx)
  · rw [List.head?_map, hhead]
    simp
  · rw [List.getLast?_map, hlast]
    rfl
  · rw [mul_smul, ← hab, inv_smul_smul]

/-! ## Star comparison and the star value -/

/-- A trivially acting element translates any tile to a tile with the same basepoint
image; contact membership is preserved. -/
theorem map_mem_contact
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {t : ↥Γ} (ht : t • τ₀ = τ₀) {z : UpperHalfPlane} {x : ↥Γ}
    (hx : x ∈ contactSet Γ τ₀ z) : t * x ∈ contactSet Γ τ₀ z := by
  have htriv := hfree t ⟨τ₀, ht⟩
  exact mem_contactSet_congr (by rw [mul_smul, htriv]) hx

/-- The junction normalizer is trivially acting. -/
theorem junction_trivial
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {b a' : ↥Γ} (hba : b • τ₀ = a' • τ₀) : (b * a'⁻¹) • τ₀ = τ₀ := by
  rw [mul_smul, ← inv_smul_eq_of_basepoint_eq hfree hba τ₀, smul_inv_smul]

/-- **Star comparison**: two tile paths inside the star of a point, with basepoint-equal
heads and basepoint-equal last tiles, have equal crossing sums. -/
theorem star_comparison (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {p q : List ↥Γ}
    (hp : IsTilePath Γ τ₀ p) (hq : IsTilePath Γ τ₀ q)
    (hpmem : ∀ g ∈ p, g ∈ contactSet Γ τ₀ z) (hqmem : ∀ g ∈ q, g ∈ contactSet Γ τ₀ z)
    {a a' b b' : ↥Γ} (hpa : p.head? = some a) (hpb : p.getLast? = some b)
    (hqa : q.head? = some a') (hqb : q.getLast? = some b')
    (ha : a • τ₀ = a' • τ₀) (hb : b • τ₀ = b' • τ₀) :
    crossingSum α p = crossingSum α q := by
  obtain ⟨⟨hzero, hodd, hfib⟩, -⟩ := mem_cycleConstrained.mp hα
  set u : ↥Γ := b * b'⁻¹ with hu
  have hut : u • τ₀ = τ₀ := junction_trivial hfree hb
  set q' : List ↥Γ := q.reverse.map (u * ·) with hq'
  have hq'path : IsTilePath Γ τ₀ q' := isTilePath_map u (isTilePath_reverse hq)
  have hq'mem : ∀ g ∈ q', g ∈ contactSet Γ τ₀ z := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
    exact map_mem_contact hfree hut (hqmem x (List.mem_reverse.mp hx))
  have hq'head : q'.head? = some b := by
    rw [hq', List.head?_map, List.head?_reverse, hqb, Option.map_some]
    simp [hu]
  have hq'last : q'.getLast? = some (u * a') := by
    rw [hq', List.getLast?_map, List.getLast?_reverse, hqa, Option.map_some]
  have hglue := crossingSum_glue α hpb hq'head
  have hr : IsTilePath Γ τ₀ (p ++ q'.tail) := isTilePath_glue hp hq'path hpb hq'head
  have hrmem : ∀ g ∈ p ++ q'.tail, g ∈ contactSet Γ τ₀ z := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hpmem g h
    · exact hq'mem g (List.mem_of_mem_tail h)
  have hzero' := star_zero hΓ hfree hα hr hrmem
    ((head?_glue (q := q') hpb).trans hpa)
    ((getLast?_glue hpb hq'head).trans hq'last) ?_
  · have hrev := crossingSum_reverse hodd q
    have hmap := crossingSum_map_mul α u q.reverse
    rw [hglue, hmap, hrev] at hzero'
    linarith
  · have htriv := hfree u ⟨τ₀, hut⟩
    rw [mul_smul, htriv, ha]

open Classical in
/-- The **star value** from tile `g` to tile `h` at the point `z`: the common crossing sum
of the tile paths inside the star of `z` joining the basepoint fibers of `g` and `h`. -/
noncomputable def starVal (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (α : (↥Γ) → ℝ) (z : UpperHalfPlane) (g h : ↥Γ) : ℝ :=
  if hp : ∃ p : List ↥Γ, IsTilePath Γ τ₀ p ∧ (∀ x ∈ p, x ∈ contactSet Γ τ₀ z) ∧
      (∃ a : ↥Γ, p.head? = some a ∧ a • τ₀ = g • τ₀) ∧
      (∃ b : ↥Γ, p.getLast? = some b ∧ b • τ₀ = h • τ₀) then
    crossingSum α hp.choose
  else 0

/-- Characterization of the star value by any witnessing star chain. -/
theorem starVal_eq (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {g h : ↥Γ} {p : List ↥Γ}
    (hp : IsTilePath Γ τ₀ p) (hmem : ∀ x ∈ p, x ∈ contactSet Γ τ₀ z)
    {a b : ↥Γ} (hhead : p.head? = some a) (hlast : p.getLast? = some b)
    (hag : a • τ₀ = g • τ₀) (hbh : b • τ₀ = h • τ₀) :
    starVal Γ τ₀ α z g h = crossingSum α p := by
  classical
  have hex : ∃ q : List ↥Γ, IsTilePath Γ τ₀ q ∧ (∀ x ∈ q, x ∈ contactSet Γ τ₀ z) ∧
      (∃ a' : ↥Γ, q.head? = some a' ∧ a' • τ₀ = g • τ₀) ∧
      (∃ b' : ↥Γ, q.getLast? = some b' ∧ b' • τ₀ = h • τ₀) :=
    ⟨p, hp, hmem, ⟨a, hhead, hag⟩, ⟨b, hlast, hbh⟩⟩
  rw [starVal, dif_pos hex]
  obtain ⟨hq, hqmem, ⟨a', ha'1, ha'2⟩, ⟨b', hb'1, hb'2⟩⟩ := hex.choose_spec
  exact star_comparison hΓ hfree hα hq hp hqmem hmem ha'1 hb'1 hhead hlast
    (ha'2.trans hag.symm) (hb'2.trans hbh.symm)

/-- The star value vanishes on basepoint-equal tiles. -/
theorem starVal_class_zero (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {g h : ↥Γ} (hg : g ∈ contactSet Γ τ₀ z)
    (hgh : g • τ₀ = h • τ₀) : starVal Γ τ₀ α z g h = 0 := by
  rw [starVal_eq hΓ hfree hα (List.isChain_singleton g)
    (by intro x hx; rw [List.mem_singleton.mp hx]; exact hg)
    (a := g) (b := g) rfl rfl rfl hgh]
  exact crossingSum_singleton α g

/-- The star value across a shared side is the value of the side function. -/
theorem starVal_side (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {g h : ↥Γ} (hg : g ∈ contactSet Γ τ₀ z)
    (hh : h ∈ contactSet Γ τ₀ z) (hside : IsSideElement Γ τ₀ (g⁻¹ * h)) :
    starVal Γ τ₀ α z g h = α (g⁻¹ * h) := by
  have hpath : IsTilePath Γ τ₀ [g, h] :=
    List.isChain_cons_cons.mpr ⟨hside, List.isChain_singleton h⟩
  have hmem : ∀ x ∈ ([g, h] : List ↥Γ), x ∈ contactSet Γ τ₀ z := by
    intro x hx
    rcases List.mem_cons.mp hx with h1 | h1
    · rw [h1]; exact hg
    · rw [List.mem_singleton.mp h1]; exact hh
  rw [starVal_eq hΓ hfree hα hpath hmem (a := g) (b := h) rfl rfl rfl rfl,
    crossingSum_cons_cons, crossingSum_singleton]
  ring

/-- Star values compose along intermediate tiles. -/
theorem starVal_trans (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {g h k : ↥Γ} (hg : g ∈ contactSet Γ τ₀ z)
    (hh : h ∈ contactSet Γ τ₀ z) (hk : k ∈ contactSet Γ τ₀ z) :
    starVal Γ τ₀ α z g h + starVal Γ τ₀ α z h k
      = starVal Γ τ₀ α z g k := by
  obtain ⟨p, hp, hpmem, hph, ηp, hpl, hpη⟩ :=
    chain_of_contact_star hΓ hfree hε hgap hdense hg hh
  obtain ⟨q, hq, hqmem, hqh, ηq, hql, hqη⟩ :=
    chain_of_contact_star hΓ hfree hε hgap hdense hh hk
  set u : ↥Γ := ηp * h⁻¹ with hu
  have hut : u • τ₀ = τ₀ := junction_trivial hfree hpη
  have hutriv := hfree u ⟨τ₀, hut⟩
  set q' : List ↥Γ := q.map (u * ·) with hq'def
  have hq'path : IsTilePath Γ τ₀ q' := isTilePath_map u hq
  have hq'mem : ∀ x ∈ q', x ∈ contactSet Γ τ₀ z := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact map_mem_contact hfree hut (hqmem y hy)
  have hq'head : q'.head? = some ηp := by
    rw [hq'def, List.head?_map, hqh, Option.map_some]
    simp [hu]
  have hq'last : q'.getLast? = some (u * ηq) := by
    rw [hq'def, List.getLast?_map, hql, Option.map_some]
  have hrpath := isTilePath_glue hp hq'path hpl hq'head
  have hrmem : ∀ x ∈ p ++ q'.tail, x ∈ contactSet Γ τ₀ z := by
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact hpmem x h1
    · exact hq'mem x (List.mem_of_mem_tail h1)
  have hphead : p.head? = some g := hph
  have hVgk := starVal_eq (g := g) (h := k) hΓ hfree hα hrpath hrmem
    ((head?_glue (q := q') hpl).trans hphead)
    ((getLast?_glue hpl hq'head).trans hq'last) rfl
    (by rw [mul_smul, hutriv, hqη])
  have hVgh := starVal_eq hΓ hfree hα hp hpmem hphead hpl rfl hpη
  have hVhk := starVal_eq hΓ hfree hα hq hqmem hqh hql rfl hqη
  rw [hVgk, hVgh, hVhk, crossingSum_glue α hpl hq'head, hq'def,
    crossingSum_map_mul]

/-- Star values are antisymmetric. -/
theorem starVal_symm (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {g h : ↥Γ} (hg : g ∈ contactSet Γ τ₀ z)
    (hh : h ∈ contactSet Γ τ₀ z) :
    starVal Γ τ₀ α z h g = -starVal Γ τ₀ α z g h := by
  have htr := starVal_trans hΓ hfree hε hgap hdense hα hg hh hg
  rw [starVal_class_zero hΓ hfree hα hg rfl] at htr
  linarith

/-- Star values transfer to a coarser star. -/
theorem starVal_mono (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z z' : UpperHalfPlane} (hsub : ∀ x : ↥Γ, x ∈ contactSet Γ τ₀ z →
      x ∈ contactSet Γ τ₀ z')
    {g h : ↥Γ} (hg : g ∈ contactSet Γ τ₀ z) (hh : h ∈ contactSet Γ τ₀ z) :
    starVal Γ τ₀ α z g h = starVal Γ τ₀ α z' g h := by
  obtain ⟨p, hp, hpmem, hph, ηp, hpl, hpη⟩ :=
    chain_of_contact_star hΓ hfree hε hgap hdense hg hh
  rw [starVal_eq hΓ hfree hα hp hpmem hph hpl rfl hpη,
    starVal_eq hΓ hfree hα hp (fun x hx => hsub x (hpmem x hx)) hph hpl rfl hpη]

/-- **Two-star comparison**: star values agree at two centers whose special balls overlap
on a common point, on tiles in both stars. -/
theorem starVal_two_star (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z z' : UpperHalfPlane} {r r' : ℝ}
    (hmeets : ∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball z r).Nonempty →
      γ ∈ contactSet Γ τ₀ z)
    (hmeets' : ∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball z' r').Nonempty →
      γ ∈ contactSet Γ τ₀ z')
    (hd : dist z z' < r / 2 + r' / 2)
    {g h : ↥Γ} (hg : g ∈ contactSet Γ τ₀ z) (hh : h ∈ contactSet Γ τ₀ z)
    (hg' : g ∈ contactSet Γ τ₀ z') (hh' : h ∈ contactSet Γ τ₀ z') :
    starVal Γ τ₀ α z g h = starVal Γ τ₀ α z' g h := by
  rcases le_total r r' with hle | hle
  · refine starVal_mono hΓ hfree hε hgap hdense hα (fun x hx => ?_) hg hh
    refine hmeets' x ⟨z, (mem_contactSet_iff_mem_smul_dirichletDomain x z).mp hx, ?_⟩
    rw [Metric.mem_ball]
    linarith
  · refine (starVal_mono hΓ hfree hε hgap hdense hα (fun x hx => ?_) hg' hh').symm
    refine hmeets x ⟨z', (mem_contactSet_iff_mem_smul_dirichletDomain x z').mp hx, ?_⟩
    rw [Metric.mem_ball, dist_comm]
    linarith

end RiemannDynamics
