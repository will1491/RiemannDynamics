/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Polygon

/-!
# The rank identity for the Dirichlet polygon

The space of additive characters `Γ → (ℝ, +)` of a cocompact free Fuchsian group has
dimension `m - c + 1`, where `m` is the number of side pairs and `c` the number of vertex
orbit classes of its Dirichlet polygon. Characters kill torsion, hence are blind to `±1`;
they are determined by their values on the side elements, which are odd functions constant
on the fibers of `γ ↦ γ • τ₀`; and the constraints cutting the character values out of the
odd side functions are exactly the vanishing of the crossing sums around the vertex cycles:
one linear constraint per vertex class, with a single linear dependency among them.

* `homSubmodule` — the `ℝ`-space of additive characters of a group; characters vanish on
  torsion (`homSubmodule_apply_eq_zero_of_sq`).
* `oddSideFunctions` — the odd side functions of the polygon; its dimension is `m`.
* `IsTilePath`, `crossingSum`, `IsVertexLoop`, `cycleConstrained` — tile paths, the crossing
  sum of an odd side function along a path, and the subspace cut out by the vertex-loop
  constraints; its dimension is `m - c + 1`.
* `crossingSum_eq_zero_of_closed` — crossing sums vanish on all closed tile paths: the
  vertex-local constraints globalize by contracting a closed tile loop through the star
  covering of the compact homotopy square.
* `exists_crossingSum_hom` — integration of a constrained odd side function into an additive
  character along tile paths.
* `restrictSides` — restriction of a character to its side values.
* `finrank_homSubmodule_add_classCount` — the rank identity `Q + c = m + 1`.
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

/-! ## The grid: row invariance of star-value sums -/

/-- The four-tile square identity at a fixed star. -/
theorem starVal_square (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {a b c d : ↥Γ} (ha : a ∈ contactSet Γ τ₀ z)
    (hb : b ∈ contactSet Γ τ₀ z) (hc : c ∈ contactSet Γ τ₀ z)
    (hd : d ∈ contactSet Γ τ₀ z) :
    starVal Γ τ₀ α z c d - starVal Γ τ₀ α z a b
      = starVal Γ τ₀ α z b d - starVal Γ τ₀ α z a c := by
  have h1 := starVal_trans hΓ hfree hε hgap hdense hα ha hc hd
  have h2 := starVal_trans hΓ hfree hε hgap hdense hα ha hb hd
  linarith

/-- **Row invariance on a grid**: on an `(m+1) × (n+1)` grid of squares with centers `z`
and node tiles `G`, with the four corner tiles of each square in its star, vertical edges
recentered across horizontal neighbors and horizontal edges recentered across vertical
neighbors, the top row sum differs from the bottom row sum by the column sums. -/
theorem grid_rows (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    (m n : ℕ) (z : ℕ → ℕ → UpperHalfPlane) (G : ℕ → ℕ → ↥Γ)
    (h4 : ∀ i ≤ m, ∀ l ≤ n, G i l ∈ contactSet Γ τ₀ (z i l) ∧
      G i (l + 1) ∈ contactSet Γ τ₀ (z i l) ∧ G (i + 1) l ∈ contactSet Γ τ₀ (z i l) ∧
      G (i + 1) (l + 1) ∈ contactSet Γ τ₀ (z i l))
    (hvert : ∀ i ≤ m, ∀ l, l < n → starVal Γ τ₀ α (z i l) (G i (l + 1))
        (G (i + 1) (l + 1))
      = starVal Γ τ₀ α (z i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)))
    (hhor : ∀ i, i < m → ∀ l ≤ n, starVal Γ τ₀ α (z (i + 1) l) (G (i + 1) l)
        (G (i + 1) (l + 1))
      = starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))) :
    ∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z m l) (G (m + 1) l) (G (m + 1) (l + 1))
      = (∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z 0 l) (G 0 l) (G 0 (l + 1)))
        + ∑ i ∈ Finset.range (m + 1),
            (starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1))
              - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) := by
  set V : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ := fun c cl i l i' =>
    starVal Γ τ₀ α (z c cl) (G i l) (G i' l) with hV
  have step2 : ∀ i ≤ m,
      ∑ l ∈ Finset.range (n + 1),
          starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))
        = (∑ l ∈ Finset.range (n + 1),
            starVal Γ τ₀ α (z i l) (G i l) (G i (l + 1)))
          + (starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1))
            - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) := by
    intro i hi
    have hsq : ∀ l ≤ n,
        starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))
          - starVal Γ τ₀ α (z i l) (G i l) (G i (l + 1))
        = starVal Γ τ₀ α (z i l) (G i (l + 1)) (G (i + 1) (l + 1))
          - starVal Γ τ₀ α (z i l) (G i l) (G (i + 1) l) := by
      intro l hl
      obtain ⟨ha, hb, hc, hd⟩ := h4 i hi l hl
      exact starVal_square hΓ hfree hε hgap hdense hα ha hb hc hd
    have hsplit : ∀ l ∈ Finset.range (n + 1),
        starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))
        = starVal Γ τ₀ α (z i l) (G i l) (G i (l + 1))
          + (starVal Γ τ₀ α (z i l) (G i (l + 1)) (G (i + 1) (l + 1))
            - starVal Γ τ₀ α (z i l) (G i l) (G (i + 1) l)) := by
      intro l hl
      have hln : l ≤ n := by
        have := Finset.mem_range.mp hl
        omega
      have := hsq l hln
      linarith
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hWtel : ∑ l ∈ Finset.range (n + 1),
        starVal Γ τ₀ α (z i l) (G i (l + 1)) (G (i + 1) (l + 1))
        = (∑ l ∈ Finset.range n,
            starVal Γ τ₀ α (z i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)))
          + starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1)) := by
      rw [Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      exact hvert i hi l (Finset.mem_range.mp hl)
    have hWtel' : ∑ l ∈ Finset.range (n + 1),
        starVal Γ τ₀ α (z i l) (G i l) (G (i + 1) l)
        = starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)
          + ∑ l ∈ Finset.range n,
            starVal Γ τ₀ α (z i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)) := by
      rw [Finset.sum_range_succ']
      ring
    rw [hWtel, hWtel']
    ring
  have step1 : ∀ i, i < m →
      ∑ l ∈ Finset.range (n + 1),
          starVal Γ τ₀ α (z (i + 1) l) (G (i + 1) l) (G (i + 1) (l + 1))
        = ∑ l ∈ Finset.range (n + 1),
          starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1)) := by
    intro i hi
    refine Finset.sum_congr rfl fun l hl => ?_
    exact hhor i hi l (by have := Finset.mem_range.mp hl; omega)
  have main : ∀ k, k ≤ m + 1 →
      ∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z (min k m) l) (G k l) (G k (l + 1))
        = (∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z 0 l) (G 0 l) (G 0 (l + 1)))
          + ∑ i ∈ Finset.range k,
              (starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1))
                - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkm : k ≤ m := by omega
      have hmin : min k m = k := by omega
      have ihk := ih (by omega)
      rw [hmin] at ihk
      rw [Finset.sum_range_succ (fun i => starVal Γ τ₀ α (z i n) (G i (n + 1))
        (G (i + 1) (n + 1)) - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) k,
        ← add_assoc, ← ihk]
      by_cases hkm' : k < m
      · have hmin' : min (k + 1) m = k + 1 := by omega
        rw [hmin', step1 k hkm', step2 k hkm]
      · have hkeq : k = m := by omega
        subst hkeq
        have hmin' : min (k + 1) k = k := by omega
        rw [hmin', step2 k le_rfl]
  have hfin := main (m + 1) le_rfl
  rwa [show min (m + 1) m = m by omega] at hfin

/-! ## Geometric helpers for the homotopy grid -/

/-- A tile containing the basepoint is centered at the basepoint. -/
theorem class_one_of_mem_tile (hΓ : IsFuchsianGroup Γ)
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {X : ↥Γ} (hX : τ₀ ∈ (X • ·) '' dirichletDomain Γ τ₀) : X • τ₀ = τ₀ := by
  have hint : τ₀ ∈ (fun x => (1 : ↥Γ) • x) '' interior (dirichletDomain Γ τ₀) :=
    ⟨τ₀, basepoint_mem_interior_dirichletDomain hε hgap, one_smul _ _⟩
  have hcs := (mem_smul_interior_iff_contactSet_eq hΓ hdense 1 τ₀).mp hint
  have hXc : X ∈ contactSet Γ τ₀ τ₀ :=
    (mem_contactSet_iff_mem_smul_dirichletDomain X τ₀).mpr hX
  rw [hcs] at hXc
  simpa using hXc

/-- A tile through a point near a center is a contact tile of the center. -/
theorem contact_of_near {w x : UpperHalfPlane} {rw : ℝ}
    (hmeets : ∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩
      Metric.ball w rw).Nonempty → γ ∈ contactSet Γ τ₀ w)
    {X : ↥Γ} (hx : x ∈ (X • ·) '' dirichletDomain Γ τ₀) (hd : dist x w < rw) :
    X ∈ contactSet Γ τ₀ w :=
  hmeets X ⟨x, hx, Metric.mem_ball.mpr hd⟩

/-- Interpolation points lie on the geodesic segment. -/
theorem geodInterp_mem_seg {a b : UpperHalfPlane} {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    geodInterp a b t ∈ geodSeg a b := by
  rw [geodSeg_eq_image_geodInterp]
  exact ⟨t, ht, rfl⟩

/-- The segment from a tile center to a point of the tile stays in the tile, in
interpolation form. -/
theorem tile_interp {X : ↥Γ} {u : UpperHalfPlane}
    (hu : u ∈ (X • ·) '' dirichletDomain Γ τ₀) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    geodInterp (X • τ₀) u t ∈ (X • ·) '' dirichletDomain Γ τ₀ :=
  geodSeg_center_subset_tile
    ((mem_contactSet_iff_mem_smul_dirichletDomain X u).mpr hu)
    (geodInterp_mem_seg ht)

/-- The segment from a point of the tile to the tile center stays in the tile, in
interpolation form. -/
theorem tile_interp' {X : ↥Γ} {u : UpperHalfPlane}
    (hu : u ∈ (X • ·) '' dirichletDomain Γ τ₀) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    geodInterp u (X • τ₀) t ∈ (X • ·) '' dirichletDomain Γ τ₀ := by
  refine geodSeg_center_subset_tile
    ((mem_contactSet_iff_mem_smul_dirichletDomain X u).mpr hu) ?_
  rw [geodSeg_comm]
  exact geodInterp_mem_seg ht

/-- The basepoint tile membership of the basepoint. -/
theorem basepoint_mem_tile (X : ↥Γ) (hX : X • τ₀ = τ₀) :
    τ₀ ∈ (X • ·) '' dirichletDomain Γ τ₀ :=
  ⟨τ₀, basepoint_mem_dirichletDomain, hX⟩

/-! ## The homotopy piece: contracting one crossing over a grid -/

/-- **The piece lemma**: for a crossing from tile `A` to tile `B` through a shared point
`q`, the geodesic homotopy of the two-segment curve `A•τ₀ → q → B•τ₀` onto the basepoint,
discretized on a sufficiently fine even grid against junction tile columns `CA`, `CB`,
expresses the side value `α (A⁻¹ B)` as the difference of the two junction column sums. -/
theorem piece (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    (r : UpperHalfPlane → ℝ) (hr : ∀ w, 0 < r w)
    (hmeets : ∀ w : UpperHalfPlane, ∀ γ : ↥Γ,
      ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball w (r w)).Nonempty →
        γ ∈ contactSet Γ τ₀ w)
    {A B : ↥Γ} {q : UpperHalfPlane}
    (hqA : q ∈ (A • ·) '' dirichletDomain Γ τ₀)
    (hqB : q ∈ (B • ·) '' dirichletDomain Γ τ₀)
    (hside : IsSideElement Γ τ₀ (A⁻¹ * B)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N' : ℕ, N₀ ≤ N' → ∀ CA CB : ℕ → ↥Γ,
      (∀ i ≤ 2 * N', geodInterp τ₀ (A • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (CA i • ·) '' dirichletDomain Γ τ₀) →
      (∀ i ≤ 2 * N', geodInterp τ₀ (B • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (CB i • ·) '' dirichletDomain Γ τ₀) →
      CA (2 * N') = A → CB (2 * N') = B →
      ∃ y : ℕ → ℕ → UpperHalfPlane,
        (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
            (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
          dist (geodInterp τ₀ (A • τ₀) s) (y i 0) < r (y i 0) / 2) ∧
        (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
            (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
          dist (geodInterp τ₀ (B • τ₀) s) (y i (2 * N' - 1))
            < r (y i (2 * N' - 1)) / 2) ∧
        α (A⁻¹ * B)
          = (∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i (2 * N' - 1)) (CB i) (CB (i + 1)))
            - ∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1)) := by
  classical
  set c : ℝ → UpperHalfPlane := fun t =>
    if t ≤ 1 / 2 then geodInterp (A • τ₀) q (2 * t)
    else geodInterp q (B • τ₀) (2 * t - 1) with hc
  have hcont : Continuous c := by
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · exact continuous_geodInterp.comp (continuous_const.prodMk
        (continuous_const.prodMk (continuous_const.mul continuous_id)))
    · exact continuous_geodInterp.comp (continuous_const.prodMk
        (continuous_const.prodMk ((continuous_const.mul continuous_id).sub
          continuous_const)))
    · intro t ht
      rw [ht, show (2 : ℝ) * (1 / 2) = 1 by norm_num, geodInterp_one,
        show (1 : ℝ) - 1 = 0 by norm_num, geodInterp_zero]
  have hc0 : c 0 = A • τ₀ := by
    simp only [hc]
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_zero, geodInterp_zero]
  have hc1 : c 1 = B • τ₀ := by
    simp only [hc]
    rw [if_neg (by norm_num : ¬(1 : ℝ) ≤ 1 / 2),
      show (2 : ℝ) * 1 - 1 = 1 by norm_num, geodInterp_one]
  have hcA : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → c t ∈ (A • ·) '' dirichletDomain Γ τ₀ := by
    intro t ht0 ht2
    simp only [hc]
    rw [if_pos ht2]
    exact tile_interp hqA ⟨by linarith, by linarith⟩
  have hcB : ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 1 → c t ∈ (B • ·) '' dirichletDomain Γ τ₀ := by
    intro t ht2 ht1
    simp only [hc]
    by_cases hle : t ≤ 1 / 2
    · rw [if_pos hle, show t = 1 / 2 from le_antisymm hle ht2,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, geodInterp_one]
      exact hqB
    · rw [if_neg hle]
      push Not at hle
      exact tile_interp' hqB ⟨by linarith, by linarith⟩
  set Hu : ℝ × ℝ → UpperHalfPlane := fun P => geodInterp τ₀ (c P.2) P.1 with hHu
  have hHcont : Continuous Hu := continuous_geodInterp.comp
    (continuous_const.prodMk ((hcont.comp continuous_snd).prodMk continuous_fst))
  set K : Set UpperHalfPlane := Hu '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) with hK
  have hKcomp : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hHcont
  have hcover : K ⊆ ⋃ w : UpperHalfPlane, Metric.ball w (r w / 2) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by linarith [hr x])⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hKcomp
    (fun w => Metric.isOpen_ball) hcover
  have hcomp2 : IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hUC := hcomp2.uniformContinuousOn_of_continuous hHcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨η, hη, hUCd⟩ := hUC δ hδ
  refine ⟨⌈1 / η⌉₊ + 1, Nat.le_add_left 1 _, ?_⟩
  intro N' hN' CA CB hCA hCB hCAN hCBN
  have hN'pos : 1 ≤ N' := le_trans (Nat.le_add_left 1 _) hN'
  have hNpos : 0 < 2 * N' := by omega
  have hNR : (0 : ℝ) < ((2 * N' : ℕ) : ℝ) := Nat.cast_pos.mpr hNpos
  have hfine : 1 / ((2 * N' : ℕ) : ℝ) < η := by
    have hceil : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : ((⌈1 / η⌉₊ + 1 : ℕ) : ℝ) ≤ ((N' : ℕ) : ℝ) := Nat.cast_le.mpr hN'
    have hN'le : ((N' : ℕ) : ℝ) ≤ ((2 * N' : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    push_cast at hcast
    have h1 : 1 / η < ((2 * N' : ℕ) : ℝ) := by linarith
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hη] at h1
    linarith [mul_comm η ((2 * N' : ℕ) : ℝ)]
  have hFex : ∀ w : UpperHalfPlane, ∃ g : ↥Γ, w ∈ (g • ·) '' dirichletDomain Γ τ₀ := by
    intro w
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ τ₀ w
    exact ⟨γ⁻¹, γ • w, hγ, inv_smul_smul γ w⟩
  choose F hF using hFex
  set G : ℕ → ℕ → ↥Γ := fun i l =>
    if l = 0 then CA i else if l = 2 * N' then CB i
    else if i = 2 * N' then (if l ≤ N' then A else B)
    else F (Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))) with hG
  have hnode : ∀ i ≤ 2 * N', ∀ l ≤ 2 * N',
      Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (G i l • ·) '' dirichletDomain Γ τ₀ := by
    intro i hi l hl
    by_cases hl0 : l = 0
    · subst hl0
      simp only [hG, if_pos rfl]
      change geodInterp τ₀ (c (((0 : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ)))
        ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ _
      rw [Nat.cast_zero, zero_div, hc0]
      exact hCA i hi
    by_cases hlN : l = 2 * N'
    · subst hlN
      simp only [hG, if_neg hl0]
      change geodInterp τ₀ (c (((2 * N' : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ)))
        ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ _
      rw [div_self hNR.ne', hc1]
      exact hCB i hi
    by_cases hiN : i = 2 * N'
    · subst hiN
      simp only [hG, if_neg hl0, if_neg hlN]
      change geodInterp τ₀ (c ((l : ℝ) / ((2 * N' : ℕ) : ℝ)))
        (((2 * N' : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ _
      rw [div_self hNR.ne', geodInterp_one]
      by_cases hlmid : l ≤ N'
      · rw [if_pos hlmid]
        refine hcA _ (div_nonneg (Nat.cast_nonneg l) hNR.le) ?_
        rw [div_le_iff₀ hNR]
        have : (l : ℝ) ≤ (N' : ℝ) := Nat.cast_le.mpr hlmid
        push_cast
        linarith
      · rw [if_neg hlmid]
        push Not at hlmid
        refine hcB _ ?_ ?_
        · rw [le_div_iff₀ hNR]
          have : ((N' : ℕ) : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hlmid
          push_cast
          linarith
        · rw [div_le_one hNR]
          exact Nat.cast_le.mpr hl
    · simp only [hG, if_neg hl0, if_neg hlN, if_neg hiN]
      exact hF _
  have hyex : ∀ i l : ℕ, ∃ w : UpperHalfPlane, i < 2 * N' → l < 2 * N' →
      Metric.ball (Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))) δ
        ⊆ Metric.ball w (r w / 2) := by
    intro i l
    by_cases h : i < 2 * N' ∧ l < 2 * N'
    · have hmem : Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ K := by
        refine ⟨((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ)),
          Set.mem_prod.mpr ⟨⟨div_nonneg (Nat.cast_nonneg i) hNR.le, ?_⟩,
            ⟨div_nonneg (Nat.cast_nonneg l) hNR.le, ?_⟩⟩, rfl⟩
        · rw [div_le_one hNR]
          exact Nat.cast_le.mpr (le_of_lt h.1)
        · rw [div_le_one hNR]
          exact Nat.cast_le.mpr (le_of_lt h.2)
      obtain ⟨w, hw⟩ := hleb _ hmem
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨τ₀, fun hi hl => absurd ⟨hi, hl⟩ h⟩
  choose y hy using hyex
  have hsq : ∀ i l : ℕ, i < 2 * N' → l < 2 * N' → ∀ s t : ℝ,
      s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) →
      t ∈ Set.Icc ((l : ℝ) / ((2 * N' : ℕ) : ℝ)) (((l : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) →
      dist (Hu (s, t)) (y i l) < r (y i l) / 2 := by
    intro i l hi hl s t hs htt
    have hIccs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans (div_nonneg (Nat.cast_nonneg i) hNR.le) hs.1
      · refine le_trans hs.2 ?_
        rw [div_le_one hNR]
        exact_mod_cast Nat.succ_le_of_lt hi
    have hIcct : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans (div_nonneg (Nat.cast_nonneg l) hNR.le) htt.1
      · refine le_trans htt.2 ?_
        rw [div_le_one hNR]
        exact_mod_cast Nat.succ_le_of_lt hl
    have hInode : ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1) := by
      refine Set.mem_prod.mpr ⟨⟨div_nonneg (Nat.cast_nonneg i) hNR.le, ?_⟩,
        ⟨div_nonneg (Nat.cast_nonneg l) hNR.le, ?_⟩⟩
      · rw [div_le_one hNR]
        exact Nat.cast_le.mpr (le_of_lt hi)
      · rw [div_le_one hNR]
        exact Nat.cast_le.mpr (le_of_lt hl)
    have hdiff : ((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ) - (i : ℝ) / ((2 * N' : ℕ) : ℝ)
        = 1 / ((2 * N' : ℕ) : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hdiffl : ((l : ℝ) + 1) / ((2 * N' : ℕ) : ℝ) - (l : ℝ) / ((2 * N' : ℕ) : ℝ)
        = 1 / ((2 * N' : ℕ) : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hdist : dist ((s, t) : ℝ × ℝ)
        ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ)) < η := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2]
      · rw [Real.dist_eq, abs_of_nonneg (by linarith [htt.1])]
        linarith [htt.2]
    have hδd := hUCd (s, t) (Set.mem_prod.mpr ⟨hIccs, hIcct⟩) _ hInode hdist
    exact Metric.mem_ball.mp (hy i l hi hl (Metric.mem_ball.mpr hδd))
  have hcontact : ∀ i l, i < 2 * N' → l < 2 * N' → ∀ i' l', i ≤ i' → i' ≤ i + 1 →
      l ≤ l' → l' ≤ l + 1 → G i' l' ∈ contactSet Γ τ₀ (y i l) := by
    intro i l hi hl i' l' hii' hi'i hll' hl'l
    have hi'N : i' ≤ 2 * N' := by omega
    have hl'N : l' ≤ 2 * N' := by omega
    have hs : ((i' : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      constructor
      · gcongr
      · gcongr
        exact_mod_cast hi'i
    have ht : ((l' : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ Set.Icc ((l : ℝ) / ((2 * N' : ℕ) : ℝ)) (((l : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      constructor
      · gcongr
      · gcongr
        exact_mod_cast hl'l
    have hd := hsq i l hi hl _ _ hs ht
    exact contact_of_near (hmeets (y i l)) (hnode i' hi'N l' hl'N)
      (lt_trans hd (half_lt_self (hr (y i l))))
  have hydist : ∀ i l i₂ l₂, i < 2 * N' → l < 2 * N' → i₂ < 2 * N' → l₂ < 2 * N' →
      ∀ i' l', i ≤ i' → i' ≤ i + 1 → l ≤ l' → l' ≤ l + 1 →
      i₂ ≤ i' → i' ≤ i₂ + 1 → l₂ ≤ l' → l' ≤ l₂ + 1 →
      dist (y i l) (y i₂ l₂) < r (y i l) / 2 + r (y i₂ l₂) / 2 := by
    intro i l i₂ l₂ hi hl hi₂ hl₂ i' l' h1 h2 h3 h4 h5 h6 h7 h8
    have hmk : ∀ j k jc kc : ℕ, j ≤ jc → jc ≤ j + 1 →
        ((jc : ℝ) / ((2 * N' : ℕ) : ℝ))
          ∈ Set.Icc ((j : ℝ) / ((2 * N' : ℕ) : ℝ)) (((j : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      intro j k jc kc hj hj'
      constructor
      · gcongr
      · gcongr
        exact_mod_cast hj'
    have hda := hsq i l hi hl _ _ (hmk i 0 i' 0 h1 h2) (hmk l 0 l' 0 h3 h4)
    have hdb := hsq i₂ l₂ hi₂ hl₂ _ _ (hmk i₂ 0 i' 0 h5 h6) (hmk l₂ 0 l' 0 h7 h8)
    calc dist (y i l) (y i₂ l₂)
        ≤ dist (y i l) (Hu ((i' : ℝ) / ((2 * N' : ℕ) : ℝ),
            (l' : ℝ) / ((2 * N' : ℕ) : ℝ)))
          + dist (Hu ((i' : ℝ) / ((2 * N' : ℕ) : ℝ),
            (l' : ℝ) / ((2 * N' : ℕ) : ℝ))) (y i₂ l₂) := dist_triangle _ _ _
      _ < r (y i l) / 2 + r (y i₂ l₂) / 2 := by
          rw [dist_comm (y i l)]
          exact add_lt_add hda hdb
  have hvert : ∀ i ≤ 2 * N' - 1, ∀ l, l < 2 * N' - 1 →
      starVal Γ τ₀ α (y i l) (G i (l + 1)) (G (i + 1) (l + 1))
        = starVal Γ τ₀ α (y i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)) := by
    intro i hi l hl
    have hiN : i < 2 * N' := by omega
    have hlN : l < 2 * N' := by omega
    have hl1N : l + 1 < 2 * N' := by omega
    exact starVal_two_star hΓ hfree hε hgap hdense hα (hmeets (y i l))
      (hmeets (y i (l + 1)))
      (hydist i l i (l + 1) hiN hlN hiN hl1N i (l + 1) le_rfl (by omega) (by omega)
        le_rfl le_rfl (by omega) le_rfl (by omega))
      (hcontact i l hiN hlN i (l + 1) le_rfl (by omega) (by omega) le_rfl)
      (hcontact i l hiN hlN (i + 1) (l + 1) (by omega) le_rfl (by omega) le_rfl)
      (hcontact i (l + 1) hiN hl1N i (l + 1) le_rfl (by omega) le_rfl (by omega))
      (hcontact i (l + 1) hiN hl1N (i + 1) (l + 1) (by omega) le_rfl le_rfl (by omega))
  have hhor : ∀ i, i < 2 * N' - 1 → ∀ l ≤ 2 * N' - 1,
      starVal Γ τ₀ α (y (i + 1) l) (G (i + 1) l) (G (i + 1) (l + 1))
        = starVal Γ τ₀ α (y i l) (G (i + 1) l) (G (i + 1) (l + 1)) := by
    intro i hi l hl
    have hiN : i < 2 * N' := by omega
    have hi1N : i + 1 < 2 * N' := by omega
    have hlN : l < 2 * N' := by omega
    exact starVal_two_star hΓ hfree hε hgap hdense hα (hmeets (y (i + 1) l))
      (hmeets (y i l))
      (hydist (i + 1) l i l hi1N hlN hiN hlN (i + 1) l le_rfl (by omega) le_rfl
        (by omega) (by omega) le_rfl le_rfl (by omega))
      (hcontact (i + 1) l hi1N hlN (i + 1) l le_rfl (by omega) le_rfl (by omega))
      (hcontact (i + 1) l hi1N hlN (i + 1) (l + 1) le_rfl (by omega) (by omega) le_rfl)
      (hcontact i l hiN hlN (i + 1) l (by omega) le_rfl le_rfl (by omega))
      (hcontact i l hiN hlN (i + 1) (l + 1) (by omega) le_rfl (by omega) le_rfl)
  have h4 : ∀ i ≤ 2 * N' - 1, ∀ l ≤ 2 * N' - 1, G i l ∈ contactSet Γ τ₀ (y i l) ∧
      G i (l + 1) ∈ contactSet Γ τ₀ (y i l) ∧ G (i + 1) l ∈ contactSet Γ τ₀ (y i l) ∧
      G (i + 1) (l + 1) ∈ contactSet Γ τ₀ (y i l) := by
    intro i hi l hl
    have hiN : i < 2 * N' := by omega
    have hlN : l < 2 * N' := by omega
    exact ⟨hcontact i l hiN hlN i l le_rfl (by omega) le_rfl (by omega),
      hcontact i l hiN hlN i (l + 1) le_rfl (by omega) (by omega) le_rfl,
      hcontact i l hiN hlN (i + 1) l (by omega) le_rfl le_rfl (by omega),
      hcontact i l hiN hlN (i + 1) (l + 1) (by omega) le_rfl (by omega) le_rfl⟩
  have hgrid := grid_rows hΓ hfree hε hgap hdense hα (2 * N' - 1) (2 * N' - 1)
    y G h4 hvert hhor
  have hNN1 : 2 * N' - 1 + 1 = 2 * N' := by omega
  rw [hNN1] at hgrid
  have hG0 : ∀ i, G i 0 = CA i := by
    intro i
    simp [hG]
  have hGN : ∀ i, G i (2 * N') = CB i := by
    intro i
    simp only [hG]
    rw [if_neg (by omega : ¬2 * N' = 0), if_pos trivial]
  have hTop : ∀ l ≤ 2 * N', G (2 * N') l = if l ≤ N' then A else B := by
    intro l hl
    by_cases hl0 : l = 0
    · subst hl0
      rw [hG0, hCAN, if_pos (Nat.zero_le N')]
    by_cases hlN : l = 2 * N'
    · subst hlN
      rw [hGN, hCBN, if_neg (by omega)]
    · simp only [hG]
      rw [if_neg hl0, if_neg hlN, if_pos trivial]
  have htopmem : ∀ l' l, l < 2 * N' → l ≤ l' → l' ≤ l + 1 →
      G (2 * N') l' ∈ contactSet Γ τ₀ (y (2 * N' - 1) l) := by
    intro l' l hl hll' hl'l
    exact hcontact (2 * N' - 1) l (by omega) hl (2 * N') l' (by omega) (by omega) hll' hl'l
  have htopsum : ∑ l ∈ Finset.range (2 * N'),
      starVal Γ τ₀ α (y (2 * N' - 1) l) (G (2 * N') l) (G (2 * N') (l + 1))
      = α (A⁻¹ * B) := by
    refine Finset.sum_eq_single_of_mem N' (Finset.mem_range.mpr (by omega)) ?_ |>.trans ?_
    · intro b hb hbN
      have hblt : b < 2 * N' := Finset.mem_range.mp hb
      have hmem : G (2 * N') b ∈ contactSet Γ τ₀ (y (2 * N' - 1) b) :=
        htopmem b b hblt le_rfl (by omega)
      rcases lt_or_gt_of_ne hbN with hcase | hcase
      · have he1 : G (2 * N') b = A := by rw [hTop b (by omega), if_pos (by omega)]
        have he2 : G (2 * N') (b + 1) = A := by rw [hTop (b + 1) (by omega), if_pos (by omega)]
        rw [he1] at hmem ⊢
        rw [he2]
        exact starVal_class_zero hΓ hfree hα hmem rfl
      · have he1 : G (2 * N') b = B := by rw [hTop b (by omega), if_neg (by omega)]
        have he2 : G (2 * N') (b + 1) = B := by rw [hTop (b + 1) (by omega), if_neg (by omega)]
        rw [he1] at hmem ⊢
        rw [he2]
        exact starVal_class_zero hΓ hfree hα hmem rfl
    · have he1 : G (2 * N') N' = A := by rw [hTop N' (by omega), if_pos le_rfl]
      have he2 : G (2 * N') (N' + 1) = B := by rw [hTop (N' + 1) (by omega), if_neg (by omega)]
      have hmA : G (2 * N') N' ∈ contactSet Γ τ₀ (y (2 * N' - 1) N') :=
        htopmem N' N' (by omega) le_rfl (by omega)
      have hmB : G (2 * N') (N' + 1) ∈ contactSet Γ τ₀ (y (2 * N' - 1) N') :=
        htopmem (N' + 1) N' (by omega) (by omega) le_rfl
      rw [he1] at hmA
      rw [he2] at hmB
      rw [he1, he2]
      exact starVal_side hΓ hfree hα hmA hmB hside
  have hbase : ∀ l ≤ 2 * N', (G 0 l) • τ₀ = τ₀ := by
    intro l hl
    have h := hnode 0 (by omega) l hl
    rw [Nat.cast_zero, zero_div] at h
    simp only [hHu] at h
    rw [geodInterp_zero] at h
    exact class_one_of_mem_tile hΓ hε hgap hdense h
  have hbotsum : ∑ l ∈ Finset.range (2 * N'),
      starVal Γ τ₀ α (y 0 l) (G 0 l) (G 0 (l + 1)) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    have hllt : l < 2 * N' := Finset.mem_range.mp hl
    have hmem : G 0 l ∈ contactSet Γ τ₀ (y 0 l) :=
      hcontact 0 l (by omega) hllt 0 l le_rfl (by omega) le_rfl (by omega)
    exact starVal_class_zero hΓ hfree hα hmem
      ((hbase l (by omega)).trans (hbase (l + 1) (by omega)).symm)
  refine ⟨y, ?_, ?_, ?_⟩
  · intro i hi s hs
    have h := hsq i 0 hi (by omega) s 0 hs
      (by
        constructor
        · rw [Nat.cast_zero, zero_div]
        · rw [Nat.cast_zero]
          positivity)
    simp only [hHu] at h
    rwa [hc0] at h
  · intro i hi s hs
    have hone : (1 : ℝ) ∈ Set.Icc (((2 * N' - 1 : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ))
        ((((2 * N' - 1 : ℕ) : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      have hcast : ((2 * N' - 1 : ℕ) : ℝ) + 1 = ((2 * N' : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * N')]
        push_cast
        ring
      constructor
      · rw [div_le_one hNR]
        linarith [hNR]
      · rw [hcast, div_self hNR.ne']
    have h := hsq i (2 * N' - 1) hi (by omega) s 1 hs hone
    simp only [hHu] at h
    rwa [hc1] at h
  · have hcolL : ∀ i, G i 0 = CA i ∧ G (i + 1) 0 = CA (i + 1) := fun i => ⟨hG0 i, hG0 (i + 1)⟩
    calc α (A⁻¹ * B)
        = ∑ l ∈ Finset.range (2 * N'),
            starVal Γ τ₀ α (y (2 * N' - 1) l) (G (2 * N') l) (G (2 * N') (l + 1)) :=
          htopsum.symm
      _ = (∑ l ∈ Finset.range (2 * N'),
            starVal Γ τ₀ α (y 0 l) (G 0 l) (G 0 (l + 1)))
          + ∑ i ∈ Finset.range (2 * N'),
              (starVal Γ τ₀ α (y i (2 * N' - 1)) (G i (2 * N')) (G (i + 1) (2 * N'))
                - starVal Γ τ₀ α (y i 0) (G i 0) (G (i + 1) 0)) := hgrid
      _ = ∑ i ∈ Finset.range (2 * N'),
              (starVal Γ τ₀ α (y i (2 * N' - 1)) (CB i) (CB (i + 1))
                - starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1))) := by
          rw [hbotsum, zero_add]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hGN i, hGN (i + 1), hG0 i, hG0 (i + 1)]
      _ = (∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i (2 * N' - 1)) (CB i) (CB (i + 1)))
            - ∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1)) := Finset.sum_sub_distrib _ _

/-- Closed tile loops based at the base tile have zero crossing sum: each transition is
contracted onto the basepoint through its homotopy grid, and the junction column sums
telescope away. -/
theorem closed_zero_base (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {p : List ↥Γ} (hp : IsTilePath Γ τ₀ p) (hhead : p.head? = some 1)
    {δ' : ↥Γ} (hlast : p.getLast? = some δ') (hδ : δ' • τ₀ = τ₀) :
    crossingSum α p = 0 := by
  classical
  set M : ℕ := p.length - 1 with hM
  set g : ℕ → ↥Γ := fun k => p.getD k 1 with hgdef
  have hpne : p ≠ [] := by
    rintro rfl
    simp at hhead
  have hplen : p.length = M + 1 := by
    have := List.length_pos_iff.mpr hpne
    omega
  have hg0 : g 0 = 1 := head_getD hhead
  have hgM : g M = δ' := getLast_getD hlast
  have hsum : crossingSum α p = ∑ k ∈ Finset.range M, α ((g k)⁻¹ * g (k + 1)) :=
    crossingSum_eq_sum_range α p
  have htrans : ∀ k, k < M → IsSideElement Γ τ₀ ((g k)⁻¹ * g (k + 1)) := by
    intro k hk
    exact isTilePath_getD hp k (by omega)
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hsum, hM0]
    simp
  have hqex : ∀ k, ∃ w : UpperHalfPlane, k < M →
      w ∈ (g k • ·) '' dirichletDomain Γ τ₀ ∧
        w ∈ (g (k + 1) • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    by_cases hk : k < M
    · obtain ⟨x, hx⟩ := (htrans k hk).2.nonempty
      refine ⟨g k • x, fun _ => ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩
      have hxσ : ((g k)⁻¹ * g (k + 1))⁻¹ • x ∈ dirichletDomain Γ τ₀ :=
        (smul_mem_dirichletSideSet_inv hx).1
      refine ⟨((g k)⁻¹ * g (k + 1))⁻¹ • x, hxσ, ?_⟩
      change g (k + 1) • ((g k)⁻¹ * g (k + 1))⁻¹ • x = g k • x
      rw [← mul_smul]
      congr 1
      group
    · exact ⟨τ₀, fun h => absurd h hk⟩
  choose Q hQ using hqex
  choose r hr hmeets hcover using fun w => exists_ball_inter_tiles_subset_contact hΓ τ₀ w
  set P : ℕ → ℕ → Prop := fun k Nx => ∀ CA CB : ℕ → ↥Γ,
    (∀ i ≤ 2 * Nx, geodInterp τ₀ (g k • τ₀) ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
      ∈ (CA i • ·) '' dirichletDomain Γ τ₀) →
    (∀ i ≤ 2 * Nx, geodInterp τ₀ (g (k + 1) • τ₀) ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
      ∈ (CB i • ·) '' dirichletDomain Γ τ₀) →
    CA (2 * Nx) = g k → CB (2 * Nx) = g (k + 1) →
    ∃ y : ℕ → ℕ → UpperHalfPlane,
      (∀ i < 2 * Nx, ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
          (((i : ℝ) + 1) / ((2 * Nx : ℕ) : ℝ)),
        dist (geodInterp τ₀ (g k • τ₀) s) (y i 0) < r (y i 0) / 2) ∧
      (∀ i < 2 * Nx, ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
          (((i : ℝ) + 1) / ((2 * Nx : ℕ) : ℝ)),
        dist (geodInterp τ₀ (g (k + 1) • τ₀) s) (y i (2 * Nx - 1))
          < r (y i (2 * Nx - 1)) / 2) ∧
      α ((g k)⁻¹ * g (k + 1))
        = (∑ i ∈ Finset.range (2 * Nx),
            starVal Γ τ₀ α (y i (2 * Nx - 1)) (CB i) (CB (i + 1)))
          - ∑ i ∈ Finset.range (2 * Nx),
            starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1)) with hPdef
  have hNex : ∀ k, ∃ N₀ : ℕ, k < M → ∀ Nx, N₀ ≤ Nx → P k Nx := by
    intro k
    by_cases hk : k < M
    · obtain ⟨N₀, -, hN₀⟩ := piece hΓ hfree hε hgap hdense hα r hr hmeets
        (hQ k hk).1 (hQ k hk).2 (htrans k hk)
      exact ⟨N₀, fun _ Nx hNx => hN₀ Nx hNx⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose Nf hNf using hNex
  set N' : ℕ := (Finset.range M).sup Nf + 1 with hN'def
  have hgetP : ∀ k, k < M → P k N' := by
    intro k hk
    refine hNf k hk N' ?_
    have := Finset.le_sup (f := Nf) (Finset.mem_range.mpr hk)
    omega
  have hNR : (0 : ℝ) < ((2 * N' : ℕ) : ℝ) := by
    rw [hN'def]
    push_cast
    positivity
  have hFex : ∀ w : UpperHalfPlane, ∃ X : ↥Γ, w ∈ (X • ·) '' dirichletDomain Γ τ₀ := by
    intro w
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ τ₀ w
    exact ⟨γ⁻¹, γ • w, hγ, inv_smul_smul γ w⟩
  choose F hF using hFex
  set C : ℕ → ℕ → ↥Γ := fun J i => if i = 2 * N' then g J
    else F (geodInterp τ₀ (g J • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))) with hCdef
  have hCN : ∀ J, C J (2 * N') = g J := by
    intro J
    simp [hCdef]
  have hCmem : ∀ J, ∀ i ≤ 2 * N', geodInterp τ₀ (g J • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
      ∈ (C J i • ·) '' dirichletDomain Γ τ₀ := by
    intro J i hi
    by_cases h : i = 2 * N'
    · subst h
      rw [hCN J, div_self hNR.ne', geodInterp_one]
      exact ⟨τ₀, basepoint_mem_dirichletDomain, rfl⟩
    · simp only [hCdef, if_neg h]
      exact hF _
  set W : ℕ → (ℕ → ℕ → UpperHalfPlane) → Prop := fun k y =>
    (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
      dist (geodInterp τ₀ (g k • τ₀) s) (y i 0) < r (y i 0) / 2) ∧
    (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
      dist (geodInterp τ₀ (g (k + 1) • τ₀) s) (y i (2 * N' - 1))
        < r (y i (2 * N' - 1)) / 2) ∧
    α ((g k)⁻¹ * g (k + 1))
      = (∑ i ∈ Finset.range (2 * N'),
          starVal Γ τ₀ α (y i (2 * N' - 1)) (C (k + 1) i) (C (k + 1) (i + 1)))
        - ∑ i ∈ Finset.range (2 * N'),
          starVal Γ τ₀ α (y i 0) (C k i) (C k (i + 1)) with hWdef
  have hYex : ∀ k, ∃ y : ℕ → ℕ → UpperHalfPlane, k < M → W k y := by
    intro k
    by_cases hk : k < M
    · obtain ⟨y, hy1, hy2, hy3⟩ := hgetP k hk (C k) (C (k + 1)) (hCmem k) (hCmem (k + 1))
        (hCN k) (hCN (k + 1))
      exact ⟨y, fun _ => ⟨hy1, hy2, hy3⟩⟩
    · exact ⟨fun _ _ => τ₀, fun h => absurd h hk⟩
  choose Y hYW using hYex
  set L : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (2 * N'),
    starVal Γ τ₀ α (Y k i 0) (C k i) (C k (i + 1)) with hLdef
  set Rt : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (2 * N'),
    starVal Γ τ₀ α (Y k i (2 * N' - 1)) (C (k + 1) i) (C (k + 1) (i + 1)) with hRdef
  have hkey : ∀ k, k < M → α ((g k)⁻¹ * g (k + 1)) = Rt k - L k :=
    fun k hk => (hYW k hk).2.2
  have hcolmem : ∀ (J : ℕ) (zc : UpperHalfPlane) (i' : ℕ), i' ≤ 2 * N' →
      dist (geodInterp τ₀ (g J • τ₀) ((i' : ℝ) / ((2 * N' : ℕ) : ℝ))) zc < r zc / 2 →
      C J i' ∈ contactSet Γ τ₀ zc := by
    intro J zc i' hi' hd
    exact contact_of_near (hmeets zc) (hCmem J i' hi')
      (lt_trans hd (half_lt_self (hr zc)))
  have hstep : ∀ i : ℕ, (i : ℝ) / ((2 * N' : ℕ) : ℝ) ≤ ((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ) := by
    intro i
    gcongr
    linarith
  have hIccl : ∀ i : ℕ, ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈
      Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) :=
    fun i => ⟨le_rfl, hstep i⟩
  have hIccr : ∀ i : ℕ, (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) ∈
      Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) :=
    fun i => ⟨hstep i, le_rfl⟩
  have hcast1 : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
    intro i
    push_cast
    ring
  have hmatch : ∀ k, k + 1 < M → Rt k = L (k + 1) := by
    intro k hk1
    have hkM : k < M := by omega
    have hE1 := (hYW k hkM).2.1
    have hE2 := (hYW (k + 1) (by omega)).1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hilt : i < 2 * N' := Finset.mem_range.mp hi
    have hxL := hE1 i hilt _ (hIccl i)
    have hxR := hE2 i hilt _ (hIccl i)
    have hx1L := hE1 i hilt _ (hIccr i)
    have hx1R := hE2 i hilt _ (hIccr i)
    refine starVal_two_star hΓ hfree hε hgap hdense hα
      (hmeets (Y k i (2 * N' - 1))) (hmeets (Y (k + 1) i 0)) ?_
      (hcolmem (k + 1) _ i (by omega) hxL)
      (hcolmem (k + 1) _ (i + 1) (by omega) (by rw [hcast1 i]; exact hx1L))
      (hcolmem (k + 1) _ i (by omega) hxR)
      (hcolmem (k + 1) _ (i + 1) (by omega) (by rw [hcast1 i]; exact hx1R))
    calc dist (Y k i (2 * N' - 1)) (Y (k + 1) i 0)
        ≤ dist (Y k i (2 * N' - 1))
            (geodInterp τ₀ (g (k + 1) • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ)))
          + dist (geodInterp τ₀ (g (k + 1) • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ)))
            (Y (k + 1) i 0) := dist_triangle _ _ _
      _ < r (Y k i (2 * N' - 1)) / 2 + r (Y (k + 1) i 0) / 2 := by
          rw [dist_comm (Y k i (2 * N' - 1))]
          exact add_lt_add hxL hxR
  have hg0τ : ∀ s : ℝ, geodInterp τ₀ (g 0 • τ₀) s = τ₀ := by
    intro s
    rw [hg0, one_smul, geodInterp_self]
  have hcl0 : ∀ i' ≤ 2 * N', (C 0 i') • τ₀ = τ₀ := by
    intro i' hi'
    have hmem := hCmem 0 i' hi'
    rw [hg0τ] at hmem
    exact class_one_of_mem_tile hΓ hε hgap hdense hmem
  have hL0 : L 0 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hilt : i < 2 * N' := Finset.mem_range.mp hi
    have hE2 := (hYW 0 hMpos).1
    exact starVal_class_zero hΓ hfree hα
      (hcolmem 0 _ i (by omega) (hE2 i hilt _ (hIccl i)))
      ((hcl0 i (by omega)).trans (hcl0 (i + 1) (by omega)).symm)
  have hM1 : M - 1 + 1 = M := by omega
  have hgMτ : ∀ s : ℝ, geodInterp τ₀ (g (M - 1 + 1) • τ₀) s = τ₀ := by
    intro s
    rw [hM1, hgM, hδ, geodInterp_self]
  have hclM : ∀ i' ≤ 2 * N', (C (M - 1 + 1) i') • τ₀ = τ₀ := by
    intro i' hi'
    have hmem := hCmem (M - 1 + 1) i' hi'
    rw [hgMτ] at hmem
    exact class_one_of_mem_tile hΓ hε hgap hdense hmem
  have hRM : Rt (M - 1) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hilt : i < 2 * N' := Finset.mem_range.mp hi
    have hE1 := (hYW (M - 1) (by omega)).2.1
    exact starVal_class_zero hΓ hfree hα
      (hcolmem (M - 1 + 1) _ i (by omega) (hE1 i hilt _ (hIccl i)))
      ((hclM i (by omega)).trans (hclM (i + 1) (by omega)).symm)
  have h1 : ∑ k ∈ Finset.range M, Rt k
      = (∑ k ∈ Finset.range (M - 1), Rt k) + Rt (M - 1) := by
    conv_lhs => rw [← hM1]
    exact Finset.sum_range_succ _ _
  have h2 : ∑ k ∈ Finset.range M, L k
      = (∑ k ∈ Finset.range (M - 1), L (k + 1)) + L 0 := by
    conv_lhs => rw [← hM1]
    exact Finset.sum_range_succ' _ _
  have h3 : ∑ k ∈ Finset.range (M - 1), L (k + 1) = ∑ k ∈ Finset.range (M - 1), Rt k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    refine (hmatch k ?_).symm
    have := Finset.mem_range.mp hk
    omega
  rw [hsum]
  calc ∑ k ∈ Finset.range M, α ((g k)⁻¹ * g (k + 1))
      = ∑ k ∈ Finset.range M, (Rt k - L k) :=
        Finset.sum_congr rfl fun k hk => hkey k (Finset.mem_range.mp hk)
    _ = (∑ k ∈ Finset.range M, Rt k) - ∑ k ∈ Finset.range M, L k :=
        Finset.sum_sub_distrib _ _
    _ = 0 := by
        rw [h1, h2, h3, hRM, hL0]
        ring

/-- **Path independence**: the crossing sum of a cycle-constrained side function vanishes
along every closed tile path — a closed tile loop contracts to the basepoint by geodesic
homotopy, a Lebesgue number for the star covering of the compact homotopy square reduces
the contraction to local moves within a vertex star, and the local moves are multiples of
vertex loops, on which the constraint vanishes; backtracking cancels by oddness. -/
theorem crossingSum_eq_zero_of_closed (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀) {p : List ↥Γ}
    (hp : IsTilePath Γ τ₀ p) {γ δ : ↥Γ} (hhead : p.head? = some γ)
    (hlast : p.getLast? = some δ) (hclose : γ • τ₀ = δ • τ₀) :
    crossingSum α p = 0 := by
  rw [← crossingSum_map_mul α γ⁻¹ p]
  refine closed_zero_base hΓ hfree hε hgap hdense hα (isTilePath_map γ⁻¹ hp) ?_
    (δ' := γ⁻¹ * δ) ?_ ?_
  · rw [List.head?_map, hhead]
    simp
  · rw [List.getLast?_map, hlast]
    rfl
  · rw [mul_smul, ← hclose, inv_smul_smul]

/-- Path independence: any two tile paths with basepoint-equal heads and basepoint-equal
last tiles have equal crossing sums. -/
theorem crossingSum_pathIndep (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {p q : List ↥Γ} (hp : IsTilePath Γ τ₀ p) (hq : IsTilePath Γ τ₀ q)
    {a a' b b' : ↥Γ} (hpa : p.head? = some a) (hpb : p.getLast? = some b)
    (hqa : q.head? = some a') (hqb : q.getLast? = some b')
    (ha : a • τ₀ = a' • τ₀) (hb : b • τ₀ = b' • τ₀) :
    crossingSum α p = crossingSum α q := by
  obtain ⟨⟨hzero, hodd, hfib⟩, -⟩ := mem_cycleConstrained.mp hα
  set u : ↥Γ := b * b'⁻¹ with hu
  have hut : u • τ₀ = τ₀ := junction_trivial hfree hb
  have hutriv := hfree u ⟨τ₀, hut⟩
  set q' : List ↥Γ := q.reverse.map (u * ·) with hq'
  have hq'path : IsTilePath Γ τ₀ q' := isTilePath_map u (isTilePath_reverse hq)
  have hq'head : q'.head? = some b := by
    rw [hq', List.head?_map, List.head?_reverse, hqb, Option.map_some]
    simp [hu]
  have hq'last : q'.getLast? = some (u * a') := by
    rw [hq', List.getLast?_map, List.getLast?_reverse, hqa, Option.map_some]
  have hglue := crossingSum_glue α hpb hq'head
  have hr : IsTilePath Γ τ₀ (p ++ q'.tail) := isTilePath_glue hp hq'path hpb hq'head
  have hzero' := crossingSum_eq_zero_of_closed hΓ hfree hε hgap hdense hα hr
    ((head?_glue (q := q') hpb).trans hpa)
    ((getLast?_glue hpb hq'head).trans hq'last)
    (by rw [mul_smul, hutriv, ha])
  have hrev := crossingSum_reverse hodd q
  have hmap := crossingSum_map_mul α u q.reverse
  rw [hglue, hmap, hrev] at hzero'
  linarith

/-- **Integration along tile paths**: every cycle-constrained side function extends to an
additive character whose values on side elements are the given ones — the value at `γ` is
the crossing sum along any tile path from the base tile to the tile of `γ`, well defined by
path independence, additive under path concatenation. -/
theorem exists_crossingSum_hom (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ Φ : cycleConstrained Γ τ₀ →ₗ[ℝ] homSubmodule (↥Γ),
      ∀ (α : cycleConstrained Γ τ₀) (γ : ↥Γ), IsSideElement Γ τ₀ γ →
        (Φ α : (↥Γ) → ℝ) γ = (α : (↥Γ) → ℝ) γ := by
  classical
  choose Pth hPtile hPhead Pend hPlast hPclass using
    fun γ : ↥Γ => exists_tilePath_to hΓ hfree hε hgap hdense γ
  have hhom : ∀ α : cycleConstrained Γ τ₀, ∀ a b : ↥Γ,
      crossingSum (α : (↥Γ) → ℝ) (Pth (a * b))
        = crossingSum (α : (↥Γ) → ℝ) (Pth a) + crossingSum (α : (↥Γ) → ℝ) (Pth b) := by
    intro α a b
    set ea : ↥Γ := Pend a with hea
    set eb : ↥Γ := Pend b with heb
    set p₂' : List ↥Γ := (Pth b).map (ea * ·) with hp₂'
    have hp₂path : IsTilePath Γ τ₀ p₂' := isTilePath_map ea (hPtile b)
    have hp₂head : p₂'.head? = some ea := by
      rw [hp₂', List.head?_map, hPhead b, Option.map_some, mul_one]
    have hp₂last : p₂'.getLast? = some (ea * eb) := by
      rw [hp₂', List.getLast?_map, hPlast b, Option.map_some]
    have hglue := crossingSum_glue (α : (↥Γ) → ℝ) (hPlast a) hp₂head
    have hrpath : IsTilePath Γ τ₀ (Pth a ++ p₂'.tail) :=
      isTilePath_glue (hPtile a) hp₂path (hPlast a) hp₂head
    have hclass : (ea * eb) • τ₀ = (a * b) • τ₀ := by
      have h1 : (a⁻¹ * ea) • τ₀ = τ₀ := by
        rw [mul_smul, hPclass a, inv_smul_smul]
      have h2 := hfree (a⁻¹ * ea) ⟨τ₀, h1⟩
      calc (ea * eb) • τ₀ = (a * ((a⁻¹ * ea) * eb)) • τ₀ := by
            congr 1
            group
        _ = a • ((a⁻¹ * ea) • (eb • τ₀)) := by rw [mul_smul, mul_smul]
        _ = a • (eb • τ₀) := by rw [h2]
        _ = a • (b • τ₀) := by rw [hPclass b]
        _ = (a * b) • τ₀ := (mul_smul a b τ₀).symm
    have hPI := crossingSum_pathIndep hΓ hfree hε hgap hdense α.2
      (hPtile (a * b)) hrpath (hPhead (a * b)) (hPlast (a * b))
      ((head?_glue (q := p₂') (hPlast a)).trans (hPhead a))
      ((getLast?_glue (hPlast a) hp₂head).trans hp₂last)
      rfl ((hPclass (a * b)).trans hclass.symm)
    rw [hPI, hglue, hp₂', crossingSum_map_mul]
  refine ⟨{ toFun := fun α =>
              ⟨fun γ => crossingSum (α : (↥Γ) → ℝ) (Pth γ), fun a b => hhom α a b⟩
            map_add' := fun α β => ?_
            map_smul' := fun t α => ?_ }, ?_⟩
  · apply Subtype.ext
    funext γ
    change crossingSum ((α + β : cycleConstrained Γ τ₀) : (↥Γ) → ℝ) (Pth γ)
      = crossingSum (α : (↥Γ) → ℝ) (Pth γ) + crossingSum (β : (↥Γ) → ℝ) (Pth γ)
    rw [Submodule.coe_add, crossingSum_add]
  · apply Subtype.ext
    funext γ
    change crossingSum ((t • α : cycleConstrained Γ τ₀) : (↥Γ) → ℝ) (Pth γ)
      = t * crossingSum (α : (↥Γ) → ℝ) (Pth γ)
    rw [SetLike.val_smul, crossingSum_smul]
  · intro α γ hγside
    change crossingSum (α : (↥Γ) → ℝ) (Pth γ) = (α : (↥Γ) → ℝ) γ
    have hdirect : IsTilePath Γ τ₀ [1, γ] := by
      refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
      rw [inv_one, one_mul]
      exact hγside
    have hPI := crossingSum_pathIndep hΓ hfree hε hgap hdense α.2
      (hPtile γ) hdirect (hPhead γ) (hPlast γ) rfl (by simp) rfl (hPclass γ)
    rw [hPI, crossingSum_cons_cons, crossingSum_singleton, inv_one, one_mul]
    ring


/-- Two nonreal factors whose absolute arguments add under multiplication lie on the same
side of the real axis. -/
theorem same_sign_of_abs_arg_add {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hadd : |Complex.arg (A * B)| = |Complex.arg A| + |Complex.arg B|)
    (hAim : A.im ≠ 0) (hBim : B.im ≠ 0) : 0 < A.im * B.im := by
  have hπ := Real.pi_pos
  have hbound : ∀ z : ℂ, 0 < z.im → 0 < z.arg ∧ z.arg < Real.pi := by
    intro z hz
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) fun h => ?_,
      lt_of_le_of_ne (Complex.arg_le_pi z) fun h => ?_⟩
    · exact hz.ne (Complex.arg_eq_zero_iff.mp h.symm).2.symm
    · exact hz.ne (Complex.arg_eq_pi_iff.mp h).2.symm
  have hboundn : ∀ z : ℂ, z.im < 0 → -Real.pi < z.arg ∧ z.arg < 0 :=
    fun z hz => ⟨Complex.neg_pi_lt_arg z, Complex.arg_neg_iff.mpr hz⟩
  rcases lt_trichotomy A.im 0 with hA1 | hA1 | hA1
  · rcases lt_trichotomy B.im 0 with hB1 | hB1 | hB1
    · exact mul_pos_of_neg_of_neg hA1 hB1
    · exact absurd hB1 hBim
    · exfalso
      obtain ⟨hAa, hAb⟩ := hboundn A hA1
      obtain ⟨hBa, hBb⟩ := hbound B hB1
      have hmem : Complex.arg A + Complex.arg B ∈ Set.Ioc (-Real.pi) Real.pi :=
        ⟨by linarith, by linarith⟩
      have harg := (Complex.arg_mul_eq_add_arg_iff hA hB).mpr hmem
      rw [harg, abs_of_neg hAb, abs_of_pos hBa] at hadd
      rcases abs_cases (Complex.arg A + Complex.arg B) with ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] at hadd <;> [linarith; linarith]
  · exact absurd hA1 hAim
  · rcases lt_trichotomy B.im 0 with hB1 | hB1 | hB1
    · exfalso
      obtain ⟨hAa, hAb⟩ := hbound A hA1
      obtain ⟨hBa, hBb⟩ := hboundn B hB1
      have hmem : Complex.arg A + Complex.arg B ∈ Set.Ioc (-Real.pi) Real.pi :=
        ⟨by linarith, by linarith⟩
      have harg := (Complex.arg_mul_eq_add_arg_iff hA hB).mpr hmem
      rw [harg, abs_of_pos hAa, abs_of_neg hBb] at hadd
      rcases abs_cases (Complex.arg A + Complex.arg B) with ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] at hadd <;> [linarith; linarith]
    · exact absurd hB1 hBim
    · exact mul_pos hA1 hB1

/-- A vertical pair admits a unique metric midpoint, at the geometric mean height. -/
theorem exists_unique_mid_axis {P Q : UpperHalfPlane} (hP : P.re = 0) (hQ : Q.re = 0)
    (hPQ : P ≠ Q) :
    ∃! m : UpperHalfPlane, dist P m = dist m Q ∧ dist P m + dist m Q = dist P Q := by
  have ha : 0 < P.im := P.im_pos
  have hb : 0 < Q.im := Q.im_pos
  have hab : P.im ≠ Q.im := by
    intro h
    exact hPQ (UpperHalfPlane.ext (Complex.ext (hP.trans hQ.symm) h))
  have hMpos : 0 < Real.sqrt (P.im * Q.im) := Real.sqrt_pos.mpr (mul_pos ha hb)
  set M : UpperHalfPlane := ⟨⟨0, Real.sqrt (P.im * Q.im)⟩, hMpos⟩ with hMdef
  have hMre : M.re = 0 := rfl
  have hMim : M.im = Real.sqrt (P.im * Q.im) := rfl
  have hlM : Real.log M.im = (Real.log P.im + Real.log Q.im) / 2 := by
    rw [hMim, Real.log_sqrt (mul_pos ha hb).le, Real.log_mul ha.ne' hb.ne']
  have hdPM : dist P M = |Real.log P.im - Real.log Q.im| / 2 := by
    rw [UpperHalfPlane.dist_of_re_eq (hP.trans hMre.symm), Real.dist_eq, hlM,
      show Real.log P.im - (Real.log P.im + Real.log Q.im) / 2
        = (Real.log P.im - Real.log Q.im) / 2 by ring, abs_div, abs_two]
  have hdMQ : dist M Q = |Real.log P.im - Real.log Q.im| / 2 := by
    rw [UpperHalfPlane.dist_of_re_eq (hMre.trans hQ.symm), Real.dist_eq, hlM,
      show (Real.log P.im + Real.log Q.im) / 2 - Real.log Q.im
        = (Real.log P.im - Real.log Q.im) / 2 by ring, abs_div, abs_two]
  have hdPQ : dist P Q = |Real.log P.im - Real.log Q.im| := by
    rw [UpperHalfPlane.dist_of_re_eq (hP.trans hQ.symm), Real.dist_eq]
  refine ⟨M, ⟨by rw [hdPM, hdMQ], by rw [hdPM, hdMQ, hdPQ]; ring⟩, ?_⟩
  rintro m ⟨heq, hsum⟩
  have hmseg : m ∈ geodSeg P Q := mem_geodSeg.mpr hsum
  obtain ⟨hmre, hmlow, hmhigh⟩ := mem_geodSeg_vertical (hP.trans hQ.symm) hmseg
  have hm0 : m.re = 0 := hmre.trans hP
  have hL : 0 < m.im := m.im_pos
  have hdPm : dist P m = |Real.log P.im - Real.log m.im| := by
    rw [UpperHalfPlane.dist_of_re_eq (hP.trans hm0.symm), Real.dist_eq]
  have hdmQ : dist m Q = |Real.log m.im - Real.log Q.im| := by
    rw [UpperHalfPlane.dist_of_re_eq (hm0.trans hQ.symm), Real.dist_eq]
  have hkey : Real.log m.im = (Real.log P.im + Real.log Q.im) / 2 := by
    rw [hdPm, hdmQ] at heq
    rcases le_total P.im Q.im with hle | hle
    · rw [min_eq_left hle] at hmlow
      rw [max_eq_right hle] at hmhigh
      have h1 : Real.log P.im ≤ Real.log m.im := Real.log_le_log ha hmlow
      have h2 : Real.log m.im ≤ Real.log Q.im := Real.log_le_log hL hmhigh
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at heq
      linarith
    · rw [min_eq_right hle] at hmlow
      rw [max_eq_left hle] at hmhigh
      have h1 : Real.log Q.im ≤ Real.log m.im := Real.log_le_log hb hmlow
      have h2 : Real.log m.im ≤ Real.log P.im := Real.log_le_log hL hmhigh
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at heq
      linarith
  have hmim : m.im = M.im := by
    have h3 := congrArg Real.exp hkey
    rw [Real.exp_log hL, ← hlM, Real.exp_log M.im_pos] at h3
    exact h3
  exact UpperHalfPlane.ext (Complex.ext (hm0.trans hMre.symm) hmim)

/-- Any pair of distinct points admits a unique metric midpoint. -/
theorem exists_unique_mid (p q : UpperHalfPlane) (hpq : p ≠ q) :
    ∃! m : UpperHalfPlane, dist p m = dist m q ∧ dist p m + dist m q = dist p q := by
  obtain ⟨g, hgp, hgq⟩ := exists_verticalize p q
  have hPQ : g • p ≠ g • q := fun h => hpq (smul_left_cancel g h)
  obtain ⟨M, ⟨hM1, hM2⟩, hMuniq⟩ := exists_unique_mid_axis hgp hgq hPQ
  have htrans : ∀ z w : UpperHalfPlane, dist z w = dist (g • z) (g • w) :=
    fun z w => (dist_smul g z w).symm
  refine ⟨g⁻¹ • M, ⟨?_, ?_⟩, ?_⟩
  · rw [htrans p (g⁻¹ • M), htrans (g⁻¹ • M) q, smul_inv_smul]
    exact hM1
  · rw [htrans p (g⁻¹ • M), htrans (g⁻¹ • M) q, htrans p q, smul_inv_smul]
    exact hM2
  · rintro m ⟨h1, h2⟩
    have hgm : g • m = M := by
      refine hMuniq (g • m) ⟨?_, ?_⟩
      · rw [← htrans p m, ← htrans m q]
        exact h1
      · rw [← htrans p m, ← htrans m q, ← htrans p q]
        exact h2
    rw [← hgm, inv_smul_smul]

/-- A side element never carries the basepoint to the same orbit point as its inverse: the
midpoint of the basepoint and its translate would be fixed. -/
theorem sideElement_smul_ne_inv
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {β : ↥Γ} (hβ : IsSideElement Γ τ₀ β) : β • τ₀ ≠ β⁻¹ • τ₀ := by
  intro h
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hp : β • τ₀ ≠ τ₀ := hβ.1
  obtain ⟨m, ⟨h1, h2⟩, huniq⟩ := exists_unique_mid τ₀ (β • τ₀) (Ne.symm hp)
  have hττ : β • (β • τ₀) = τ₀ := by rw [h, smul_inv_smul]
  have hd1 : dist τ₀ (β • m) = dist (β • τ₀) m := by
    conv_lhs => rw [← hττ]
    exact dist_smul β (β • τ₀) m
  have hd2 : dist (β • m) (β • τ₀) = dist m τ₀ := dist_smul β m τ₀
  have hm1 : dist τ₀ (β • m) = dist (β • m) (β • τ₀) := by
    rw [hd1, hd2, dist_comm (β • τ₀) m, dist_comm m τ₀, ← h1]
  have hm2 : dist τ₀ (β • m) + dist (β • m) (β • τ₀) = dist τ₀ (β • τ₀) := by
    rw [hd1, hd2, dist_comm (β • τ₀) m, dist_comm m τ₀]
    linarith [h2]
  have hfix : β • m = m := huniq (β • m) ⟨hm1, hm2⟩
  exact hp (hfree β ⟨m, hfix⟩ τ₀)

/-- The odd side function supported on one side pair: value `1` on the fiber of `β` and
`-1` on the fiber of `β⁻¹`. -/
theorem exists_indicator
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {β : ↥Γ} (hβ : IsSideElement Γ τ₀ β) :
    ∃ α : (↥Γ) → ℝ, α ∈ oddSideFunctions Γ τ₀ ∧
      (∀ γ : ↥Γ, γ • τ₀ = β • τ₀ → α γ = 1) ∧
      (∀ γ : ↥Γ, γ • τ₀ = β⁻¹ • τ₀ → α γ = -1) ∧
      (∀ γ : ↥Γ, γ • τ₀ ≠ β • τ₀ → γ • τ₀ ≠ β⁻¹ • τ₀ → α γ = 0) := by
  classical
  have hne := sideElement_smul_ne_inv hfree hβ
  refine ⟨fun γ => if γ • τ₀ = β • τ₀ then 1 else if γ • τ₀ = β⁻¹ • τ₀ then -1 else 0,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ hγ
    have h1 : ¬ γ • τ₀ = β • τ₀ := fun h => hγ ((isSideElement_congr h).mpr hβ)
    have h2 : ¬ γ • τ₀ = β⁻¹ • τ₀ := fun h => hγ ((isSideElement_congr h).mpr hβ.inv)
    simp only [if_neg h1, if_neg h2]
  · intro γ
    by_cases c1 : γ • τ₀ = β • τ₀
    · have hinv : γ⁻¹ • τ₀ = β⁻¹ • τ₀ := inv_smul_eq_of_basepoint_eq hfree c1 τ₀
      have hno : ¬ γ⁻¹ • τ₀ = β • τ₀ := fun h => hne (h.symm.trans hinv)
      simp only [if_neg hno, if_pos hinv, if_pos c1]
    · by_cases c2 : γ • τ₀ = β⁻¹ • τ₀
      · have hinv : γ⁻¹ • τ₀ = β • τ₀ := by
          have h2 := inv_smul_eq_of_basepoint_eq hfree c2 τ₀
          rwa [inv_inv] at h2
        simp only [if_pos hinv, if_neg c1, if_pos c2]
        norm_num
      · have hno1 : ¬ γ⁻¹ • τ₀ = β • τ₀ := fun h => by
          have h2 := inv_smul_eq_of_basepoint_eq hfree h τ₀
          rw [inv_inv] at h2
          exact c2 h2
        have hno2 : ¬ γ⁻¹ • τ₀ = β⁻¹ • τ₀ := fun h => by
          have h2 := inv_smul_eq_of_basepoint_eq hfree h τ₀
          rw [inv_inv, inv_inv] at h2
          exact c1 h2
        simp only [if_neg hno1, if_neg hno2, if_neg c1, if_neg c2]
        norm_num
  · intro γ δ h
    simp only [h]
  · intro γ h
    simp only [if_pos h]
  · intro γ h
    have hno : ¬ γ • τ₀ = β • τ₀ := fun h1 => hne (h1.symm.trans h)
    simp only [if_neg hno, if_pos h]
  · intro γ h1 h2
    simp only [if_neg h1, if_neg h2]

/-- Equal side pairs identify the orbit points of their elements up to inversion. -/
theorem pair_cases (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ) (hδ : IsSideElement Γ τ₀ δ)
    (h : ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹}) :
    γ • τ₀ = δ • τ₀ ∨ γ • τ₀ = δ⁻¹ • τ₀ := by
  have hmem : dirichletSideSet Γ τ₀ γ
      ∈ ({dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} : Set (Set UpperHalfPlane)) := by
    rw [← h]
    exact Set.mem_insert _ _
  rcases hmem with h1 | h1
  · exact Or.inl (smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ h1)
  · rw [Set.mem_singleton_iff] at h1
    exact Or.inr (smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ.inv h1)

/-- Orbit-point identification up to inversion produces equal side pairs. -/
theorem pair_eq_of_smul_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀ ∨ γ • τ₀ = δ⁻¹ • τ₀) :
    ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} := by
  rcases h with h | h
  · have hinv : γ⁻¹ • τ₀ = δ⁻¹ • τ₀ := inv_smul_eq_of_basepoint_eq hfree h τ₀
    rw [sideSet_eq_of_basepoint_eq h, sideSet_eq_of_basepoint_eq hinv]
  · have hinv : γ⁻¹ • τ₀ = δ • τ₀ := by
      have h2 := inv_smul_eq_of_basepoint_eq hfree h τ₀
      rwa [inv_inv] at h2
    rw [sideSet_eq_of_basepoint_eq h, sideSet_eq_of_basepoint_eq hinv, Set.pair_comm]

/-- The tile list of a cyclic enumeration: the consecutive tiles from position `x` through
position `x + m`. -/
def loopList (e : ℕ → ↥Γ) : ℕ → ℕ → List ↥Γ
  | x, 0 => [e x]
  | x, m + 1 => e x :: loopList e (x + 1) m

/-- The tile list of length zero is the single tile at the starting position. -/
theorem loopList_zero (e : ℕ → ↥Γ) (x : ℕ) : loopList e x 0 = [e x] := rfl

/-- The tile list unfolds from the left: one more step prepends the tile at the current
position to the list starting one position later. -/
theorem loopList_succ (e : ℕ → ↥Γ) (x m : ℕ) :
    loopList e x (m + 1) = e x :: loopList e (x + 1) m := rfl

/-- A tile list is never empty; it always contains at least its starting tile. -/
theorem loopList_ne_nil (e : ℕ → ↥Γ) (x m : ℕ) : loopList e x m ≠ [] := by
  cases m <;> simp [loopList_zero, loopList_succ]

/-- The tile list begins at the starting position. -/
theorem loopList_head? (e : ℕ → ↥Γ) (x m : ℕ) :
    (loopList e x m).head? = some (e x) := by
  cases m <;> rfl

/-- The tile list of length `m` from position `x` ends at position `x + m`. -/
theorem loopList_getLast? (e : ℕ → ↥Γ) : ∀ m x,
    (loopList e x m).getLast? = some (e (x + m)) := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    rw [loopList_succ]
    cases hm : loopList e (x + 1) m with
    | nil => exact absurd hm (loopList_ne_nil e (x + 1) m)
    | cons b l =>
      rw [List.getLast?_cons_cons, ← hm, ih (x + 1),
        show x + 1 + m = x + (m + 1) from by omega]

/-- Every tile of the list occurs at one of the enumerated positions `x, …, x + m`. -/
theorem loopList_mem (e : ℕ → ↥Γ) : ∀ m x γ, γ ∈ loopList e x m →
    ∃ i, i ≤ m ∧ γ = e (x + i) := by
  intro m
  induction m with
  | zero =>
    intro x γ hγ
    rw [loopList_zero, List.mem_singleton] at hγ
    exact ⟨0, le_rfl, by simpa using hγ⟩
  | succ m ih =>
    intro x γ hγ
    rw [loopList_succ, List.mem_cons] at hγ
    rcases hγ with rfl | hγ
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih (x + 1) γ hγ
      exact ⟨i + 1, by omega, by rw [show x + (i + 1) = x + 1 + i by omega]⟩


/-- The crossing sum along a tile list is the sum of the side function over the transition
elements between consecutive positions of the enumeration. -/
theorem crossingSum_loopList (α : (↥Γ) → ℝ) (e : ℕ → ↥Γ) : ∀ m x,
    crossingSum α (loopList e x m)
      = ∑ i ∈ Finset.range m, α ((e (x + i))⁻¹ * e (x + i + 1)) := by
  intro m
  induction m with
  | zero =>
    intro x
    rw [loopList_zero, crossingSum_singleton, Finset.sum_range_zero]
  | succ m ih =>
    intro x
    have hshape : loopList e (x + 1) m
        = e (x + 1) :: (loopList e (x + 1) m).tail := by
      cases m <;> rfl
    rw [loopList_succ, hshape, crossingSum_cons_cons, ← hshape, ih (x + 1),
      Finset.sum_range_succ']
    have hre : ∀ i, x + 1 + i = x + (i + 1) := fun i => by omega
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hre i, show x + (i + 1) + 1 = x + (i + 1) + 1 from rfl]

/-- A tile list is a tile path whenever consecutive positions of the enumeration are
separated by a genuine side element. -/
theorem isTilePath_loopList (e : ℕ → ↥Γ)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1))) : ∀ m x,
    IsTilePath Γ τ₀ (loopList e x m) := by
  intro m
  induction m with
  | zero => intro x; exact List.isChain_singleton _
  | succ m ih =>
    intro x
    have hshape : loopList e (x + 1) m
        = e (x + 1) :: (loopList e (x + 1) m).tail := by
      cases m <;> rfl
    change List.IsChain _ (loopList e x (m + 1))
    rw [loopList_succ, hshape, List.isChain_cons_cons]
    exact ⟨hadj x, by rw [← hshape]; exact ih (x + 1)⟩

/-- An `n`-periodic enumeration is invariant under shifting by any multiple of `n`. -/
theorem periodic_add_mul {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k) :
    ∀ j k, e (k + j * n) = e k := by
  intro j
  induction j with
  | zero => intro k; rw [Nat.zero_mul, Nat.add_zero]
  | succ j ih =>
    intro k
    rw [show k + (j + 1) * n = k + j * n + n from by ring, hper, ih]

/-- An `n`-periodic enumeration is determined by the residue of the position mod `n`. -/
theorem periodic_mod {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k)
    (k : ℕ) : e (k % n) = e k := by
  conv_rhs => rw [show k = k % n + (k / n) * n from by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div k n).symm]
  rw [periodic_add_mul hper]

/-- The crossing-value sum over a window of `n` consecutive positions of an `n`-periodic
enumeration is window-independent. -/
theorem W_add (α : (↥Γ) → ℝ) {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k) :
    ∀ x, ∑ i ∈ Finset.range (x + n), α ((e i)⁻¹ * e (i + 1))
      = (∑ i ∈ Finset.range x, α ((e i)⁻¹ * e (i + 1)))
        + ∑ i ∈ Finset.range n, α ((e i)⁻¹ * e (i + 1)) := by
  intro x
  induction x with
  | zero => rw [Nat.zero_add, Finset.sum_range_zero, zero_add]
  | succ x ih =>
    rw [show x + 1 + n = (x + n) + 1 from by omega, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : e (x + n) = e x := hper x
    have h2 : e (x + n + 1) = e (x + 1) := by
      rw [show x + n + 1 = x + 1 + n from by omega, hper]
    rw [h1, h2]
    ring

/-- The partial crossing sums of a periodic enumeration depend only on the position mod
`n`, once the sum over one full period vanishes: the surplus positions contribute whole
periods, each of which sums to zero. -/
theorem W_congr_mod (α : (↥Γ) → ℝ) {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k)
    (hzero : ∑ i ∈ Finset.range n, α ((e i)⁻¹ * e (i + 1)) = 0) {x y : ℕ}
    (hxy : x % n = y % n) :
    ∑ i ∈ Finset.range x, α ((e i)⁻¹ * e (i + 1))
      = ∑ i ∈ Finset.range y, α ((e i)⁻¹ * e (i + 1)) := by
  have hred : ∀ z : ℕ, ∑ i ∈ Finset.range z, α ((e i)⁻¹ * e (i + 1))
      = ∑ i ∈ Finset.range (z % n), α ((e i)⁻¹ * e (i + 1)) := by
    intro z
    have hmul : ∀ j r, ∑ i ∈ Finset.range (r + j * n), α ((e i)⁻¹ * e (i + 1))
        = ∑ i ∈ Finset.range r, α ((e i)⁻¹ * e (i + 1)) := by
      intro j
      induction j with
      | zero => intro r; rw [Nat.zero_mul, Nat.add_zero]
      | succ j ih =>
        intro r
        rw [show r + (j + 1) * n = (r + j * n) + n from by ring, W_add α hper, hzero,
          add_zero, ih]
    conv_lhs => rw [show z = z % n + (z / n) * n from by
      rw [Nat.mul_comm]
      exact (Nat.mod_add_div z n).symm]
    exact hmul (z / n) (z % n)
  rw [hred x, hred y, hxy]

/-- Along a cyclic tile enumeration at a vertex, a tile adjacent to the tile at position
`x + 1` sits at position `x + 2` or at position `x`. -/
theorem step_dichotomy (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {γ δ : ↥Γ} (_hγ : γ ∈ contactSet Γ τ₀ v) (hδ : δ ∈ contactSet Γ τ₀ v)
    (hside : IsSideElement Γ τ₀ (γ⁻¹ * δ)) {x : ℕ} (hγτ : γ • τ₀ = e (x + 1) • τ₀) :
    δ • τ₀ = e (x + 2) • τ₀ ∨ δ • τ₀ = e x • τ₀ := by
  classical
  have hposdiff : ∀ a b : ℕ, e a • τ₀ = e b • τ₀ → a % n = b % n := by
    intro a b hab
    obtain ⟨k, -, hk⟩ := huniq (e a) (hcon a)
    have h1 := hk (a % n) ⟨Nat.mod_lt a (by omega), by rw [periodic_mod hper]⟩
    have h2 := hk (b % n) ⟨Nat.mod_lt b (by omega), by
      rw [periodic_mod hper]
      exact hab⟩
    rw [h1, h2]
  have hne2 : e (x + 2) • τ₀ ≠ e x • τ₀ := by
    intro hcontra
    have := hposdiff (x + 2) x hcontra
    have h2 : (x + 2) % n = x % n := this
    have hdvd : n ∣ (x + 2) - x := (Nat.modEq_iff_dvd' (by omega)).mp h2.symm
    rw [show x + 2 - x = 2 from by omega] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hrepex : ∀ p ∈ tileCenters Γ τ₀ v,
      ∃ g : ↥Γ, g ∈ contactSet Γ τ₀ v ∧ g • τ₀ = p := by
    rintro p ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  choose! rep hrep₁ hrep₂ using hrepex
  have hpP : e (x + 1) • τ₀ ∈ tileCenters Γ τ₀ v := ⟨e (x + 1), hcon (x + 1), rfl⟩
  obtain ⟨q₁, hq₁, q₂, hq₂, hq12, hchar⟩ :=
    two_neighbors hΓ hfree hε hgap hdense hv hrep₁ hrep₂ hpP
  have hsideTrans : ∀ g : ↥Γ, g ∈ contactSet Γ τ₀ v →
      ∀ w : ↥Γ, w • τ₀ = e (x + 1) • τ₀ → IsSideElement Γ τ₀ (w⁻¹ * g) →
      IsSideElement Γ τ₀ ((rep (e (x + 1) • τ₀))⁻¹ * rep (g • τ₀)) := by
    intro g hg w hw hwside
    have hgP : g • τ₀ ∈ tileCenters Γ τ₀ v := ⟨g, hg, rfl⟩
    have h1 : (w⁻¹ * g) • τ₀ = ((rep (e (x + 1) • τ₀))⁻¹ * rep (g • τ₀)) • τ₀ :=
      transition_basepoint_eq hfree (hw.trans (hrep₂ _ hpP).symm) (hrep₂ _ hgP).symm
    exact (isSideElement_congr h1).mp hwside
  have hmemplus : e (x + 2) • τ₀ = q₁ ∨ e (x + 2) • τ₀ = q₂ := by
    refine (hchar _ ⟨e (x + 2), hcon (x + 2), rfl⟩).mp ?_
    exact hsideTrans (e (x + 2)) (hcon (x + 2)) (e (x + 1)) rfl (hadj (x + 1))
  have hmemminus : e x • τ₀ = q₁ ∨ e x • τ₀ = q₂ := by
    refine (hchar _ ⟨e x, hcon x, rfl⟩).mp ?_
    refine hsideTrans (e x) (hcon x) (e (x + 1)) rfl ?_
    have h1 := (hadj x).inv
    rwa [mul_inv_rev, inv_inv] at h1
  have hmemδ : δ • τ₀ = q₁ ∨ δ • τ₀ = q₂ := by
    refine (hchar _ ⟨δ, hδ, rfl⟩).mp ?_
    exact hsideTrans δ hδ γ hγτ hside
  rcases hmemplus with h1 | h1 <;> rcases hmemminus with h2 | h2 <;>
    rcases hmemδ with h3 | h3
  · exact absurd (h1.trans h2.symm) hne2
  · exact absurd (h1.trans h2.symm) hne2
  · exact Or.inl (h3.trans h1.symm)
  · exact Or.inr (h3.trans h2.symm)
  · exact Or.inr (h3.trans h2.symm)
  · exact Or.inl (h3.trans h1.symm)
  · exact absurd (h1.trans h2.symm) hne2
  · exact absurd (h1.trans h2.symm) hne2

/-- The crossing sum of a tile path at a vertex is the difference of the crossing-value
potential between the end position and the start position of the path on the cycle. -/
theorem walk_sum (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {α : (↥Γ) → ℝ} (hodd : ∀ γ : ↥Γ, α γ⁻¹ = -α γ)
    (hfib : ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ) :
    ∀ (l : List ↥Γ) (γ : ↥Γ) (x : ℕ), IsTilePath Γ τ₀ (γ :: l) →
      (∀ g ∈ γ :: l, g ∈ contactSet Γ τ₀ v) → l.length ≤ x → γ • τ₀ = e x • τ₀ →
      ∃ y : ℕ, (γ :: l).getLast (List.cons_ne_nil γ l) • τ₀ = e y • τ₀ ∧
        crossingSum α (γ :: l)
          = (∑ i ∈ Finset.range y, α ((e i)⁻¹ * e (i + 1)))
            - ∑ i ∈ Finset.range x, α ((e i)⁻¹ * e (i + 1)) := by
  have hW : ∀ z : ℕ, ∑ i ∈ Finset.range (z + 1), α ((e i)⁻¹ * e (i + 1))
      = (∑ i ∈ Finset.range z, α ((e i)⁻¹ * e (i + 1))) + α ((e z)⁻¹ * e (z + 1)) :=
    fun z => Finset.sum_range_succ _ z
  intro l
  induction l with
  | nil =>
    intro γ x hpath hmem hlen hpos
    exact ⟨x, hpos, by rw [crossingSum_singleton, sub_self]⟩
  | cons δ l' ih =>
    intro γ x hpath hmem hlen hpos
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hpath
    have hlen' : l'.length + 1 ≤ x := by simpa using hlen
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    have hmemδ : δ ∈ contactSet Γ τ₀ v := hmem δ (List.mem_cons_of_mem γ (List.mem_cons_self))
    have hmemtail : ∀ g ∈ δ :: l', g ∈ contactSet Γ τ₀ v :=
      fun g hg => hmem g (List.mem_cons_of_mem γ hg)
    have hdich := step_dichotomy hΓ hfree hε hgap hdense hv hn3 hper hcon huniq hadj
      (hmem γ List.mem_cons_self) hmemδ hstep hpos
    have hlast : (γ :: δ :: l').getLast (List.cons_ne_nil γ (δ :: l'))
        = (δ :: l').getLast (List.cons_ne_nil δ l') := List.getLast_cons _
    rcases hdich with hδpos | hδpos
    · obtain ⟨y, hy1, hy2⟩ := ih δ (x' + 2) htail hmemtail (by omega) hδpos
      refine ⟨y, by rw [hlast]; exact hy1, ?_⟩
      rw [crossingSum_cons_cons, hy2]
      have hα : α (γ⁻¹ * δ) = α ((e (x' + 1))⁻¹ * e (x' + 2)) :=
        hfib _ _ (transition_basepoint_eq hfree hpos hδpos)
      rw [hα]
      have h1 := hW (x' + 1)
      linarith
    · obtain ⟨y, hy1, hy2⟩ := ih δ x' htail hmemtail (by omega) hδpos
      refine ⟨y, by rw [hlast]; exact hy1, ?_⟩
      rw [crossingSum_cons_cons, hy2]
      have hα : α (γ⁻¹ * δ) = α ((e (x' + 1))⁻¹ * e x') :=
        hfib _ _ (transition_basepoint_eq hfree hpos hδpos)
      have hα2 : α ((e (x' + 1))⁻¹ * e x') = -α ((e x')⁻¹ * e (x' + 1)) := by
        have h1 := hodd ((e x')⁻¹ * e (x' + 1))
        rwa [mul_inv_rev, inv_inv] at h1
      rw [hα, hα2]
      have h1 := hW x'
      linarith

/-- On a cyclic tile enumeration, equal tiles have equal positions modulo the period. -/
theorem position_mod_eq {v : UpperHalfPlane}
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    {a b : ℕ} (hab : e a • τ₀ = e b • τ₀) : a % n = b % n := by
  obtain ⟨k, -, hk⟩ := huniq (e a) (hcon a)
  have h1 := hk (a % n) ⟨Nat.mod_lt a (by omega), by rw [periodic_mod hper]⟩
  have h2 := hk (b % n) ⟨Nat.mod_lt b (by omega), by
    rw [periodic_mod hper]
    exact hab⟩
  rw [h1, h2]

/-- If the full-cycle crossing sum at a vertex vanishes, so does the crossing sum of every
vertex loop there. -/
theorem closed_loop_sum (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {α : (↥Γ) → ℝ} (hodd : ∀ γ : ↥Γ, α γ⁻¹ = -α γ)
    (hfib : ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ)
    (hzero : ∑ i ∈ Finset.range n, α ((e i)⁻¹ * e (i + 1)) = 0)
    {p : List ↥Γ} (hp : IsVertexLoop Γ τ₀ v p) : crossingSum α p = 0 := by
  obtain ⟨hpath, hmemp, hclose⟩ := hp
  cases p with
  | nil => simp [crossingSum]
  | cons γ l =>
    obtain ⟨k₀, ⟨hk₀n, hk₀⟩, -⟩ := huniq γ (hmemp γ List.mem_cons_self)
    have hx : γ • τ₀ = e (k₀ + (l.length + 1) * n) • τ₀ := by
      rw [periodic_add_mul hper]
      exact hk₀
    have hlen : l.length ≤ k₀ + (l.length + 1) * n := by
      have h1 : l.length + 1 ≤ (l.length + 1) * n := Nat.le_mul_of_pos_right _ (by omega)
      omega
    obtain ⟨y, hy1, hy2⟩ := walk_sum hΓ hfree hε hgap hdense hv hn3 hper hcon huniq
      hadj hodd hfib l γ _ hpath hmemp hlen hx
    have hlasteq : γ = (γ :: l).getLast (List.cons_ne_nil γ l) := by
      have h1 : (γ :: l).head? = some γ := rfl
      have h2 : (γ :: l).getLast? = some ((γ :: l).getLast (List.cons_ne_nil γ l)) :=
        List.getLast?_eq_some_getLast _
      rw [h1, h2] at hclose
      exact Option.some_injective _ hclose
    have hclosepos : e y • τ₀ = e (k₀ + (l.length + 1) * n) • τ₀ := by
      rw [← hy1, ← hlasteq, hx]
    have hmodeq := position_mod_eq hn3 hper hcon huniq hclosepos
    rw [hy2, W_congr_mod α hper hzero hmodeq, sub_self]

/-- Frame ratios are invariant under the Möbius action: the unimodular frame factor
cancels. -/
theorem discChart_ratio_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z w x : UpperHalfPlane) :
    discChart (g • z) (g • x) / discChart (g • z) (g • w) = discChart z x / discChart z w := by
  have hzim : ((z : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact z.im_pos.ne'
  have hzbim : (((starRingEnd ℂ) (z : ℂ))).im ≠ 0 := by
    rw [Complex.conj_im, UpperHalfPlane.coe_im]
    simpa using z.im_pos.ne'
  have hμ : (((g 1 0 : ℝ) : ℂ) * (starRingEnd ℂ) (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) ≠ 0 :=
    div_ne_zero (denom_ne_zero g hzbim) (denom_ne_zero g hzim)
  rw [discChart_smul g z x, discChart_smul g z w, mul_div_mul_left _ _ hμ]

/-- The frame-ratio imaginary part at a bisector point, computed in the normalizing frame:
the direction toward another bisector point is real, of the sign of the height increment. -/
theorem ratio_im_formula {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {u w : UpperHalfPlane} (hu : dist u p = dist u q) (hw : dist w p = dist w q)
    (x : UpperHalfPlane) :
    (discChart u x / discChart u w).im
      = (discChart (g • u) (g • x)).im
        * (((g • w).im + (g • u).im) / ((g • w).im - (g • u).im)) := by
  have hgu : (g • u).re = 0 := normalizer_re_eq_zero hε' hle hge hu
  have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
  rw [← discChart_ratio_smul g u w x, discChart_axis hgu hgw, div_ofReal_im,
    div_div_eq_mul_div, mul_div_assoc]

section SignLemmas

variable {p q : UpperHalfPlane} {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ}

/-- The frame-ratio imaginary part at a bisector point in a bisector direction does not
vanish on a strict-side test point. -/
theorem ratio_im_ne_zero (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {u w : UpperHalfPlane} (hu : dist u p = dist u q) (hw : dist w p = dist w q)
    (huw : u ≠ w) {x : UpperHalfPlane} (hx : dist x p < dist x q) :
    (discChart u x / discChart u w).im ≠ 0 := by
  have hgu : (g • u).re = 0 := normalizer_re_eq_zero hε' hle hge hu
  have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
  have hxre : (g • x).re ≠ 0 := by
    have h1 := (normalizer_lt_iff hle hge x).mp hx
    rcases hε' with rfl | rfl
    · rw [one_mul] at h1
      exact h1.ne
    · rw [neg_one_mul, neg_lt_zero] at h1
      exact h1.ne'
  have himA : (discChart (g • u) (g • x)).im ≠ 0 :=
    fun h => hxre (((discChart_im_sign hgu (g • x)).2.1).mp h)
  have hsum : 0 < (g • w).im + (g • u).im := by
    have := (g • w).im_pos
    have := (g • u).im_pos
    linarith
  have hdiff : (g • w).im - (g • u).im ≠ 0 := by
    intro h
    refine huw (smul_left_cancel g ?_)
    refine (UpperHalfPlane.ext (Complex.ext ?_ ?_)).symm
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hgu, hgw]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      linarith
  rw [ratio_im_formula hε' hle hge hu hw x]
  exact mul_ne_zero himA (div_ne_zero hsum.ne' hdiff)

/-- Strict-side test points on opposite sides of a bisector have frame-ratio imaginary
parts of opposite signs, in a common frame at a bisector point. -/
theorem ratio_im_mul_neg_targets (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {u w : UpperHalfPlane} (hu : dist u p = dist u q) (hw : dist w p = dist w q)
    (huw : u ≠ w) {x y : UpperHalfPlane} (hx : dist x p < dist x q)
    (hy : dist y q < dist y p) :
    (discChart u x / discChart u w).im * (discChart u y / discChart u w).im < 0 := by
  have hgu : (g • u).re = 0 := normalizer_re_eq_zero hε' hle hge hu
  have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
  have hx' : ε' * (g • x).re < 0 := (normalizer_lt_iff hle hge x).mp hx
  have hy' : 0 < ε' * (g • y).re := by
    have h1 : 0 ≤ ε' * (g • y).re := (hge y).mp hy.le
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact h2
    · exact absurd ((hle y).mpr h2.symm.le) (not_le.mpr hy)
  have hAB : (discChart (g • u) (g • x)).im * (discChart (g • u) (g • y)).im < 0 := by
    rcases hε' with rfl | rfl
    · rw [one_mul] at hx' hy'
      exact mul_neg_of_pos_of_neg (((discChart_im_sign hgu (g • x)).1).mpr hx')
        (((discChart_im_sign hgu (g • y)).2.2).mpr hy')
    · rw [neg_one_mul, neg_lt_zero] at hx'
      rw [neg_one_mul, lt_neg, neg_zero] at hy'
      exact mul_neg_of_neg_of_pos (((discChart_im_sign hgu (g • x)).2.2).mpr hx')
        (((discChart_im_sign hgu (g • y)).1).mpr hy')
  have hsum : 0 < (g • w).im + (g • u).im := by
    have := (g • w).im_pos
    have := (g • u).im_pos
    linarith
  have hdiff : (g • w).im - (g • u).im ≠ 0 := by
    intro h
    refine huw (smul_left_cancel g ?_)
    refine (UpperHalfPlane.ext (Complex.ext ?_ ?_)).symm
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hgu, hgw]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      linarith
  have hr : ((g • w).im + (g • u).im) / ((g • w).im - (g • u).im) ≠ 0 :=
    div_ne_zero hsum.ne' hdiff
  rw [ratio_im_formula hε' hle hge hu hw x, ratio_im_formula hε' hle hge hu hw y,
    show ∀ A B r : ℝ, A * r * (B * r) = A * B * (r * r) from fun A B r => by ring]
  exact mul_neg_of_neg_of_pos hAB (mul_self_pos.mpr hr)

/-- A strict-side test point has frame-ratio imaginary parts of opposite signs at the two
ends of a bisector segment, each frame directed toward the other end. -/
theorem ratio_im_mul_neg_frames (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {a b : UpperHalfPlane} (ha : dist a p = dist a q) (hb : dist b p = dist b q)
    (hab : a ≠ b) {x : UpperHalfPlane} (hx : dist x p < dist x q) :
    (discChart a x / discChart a b).im * (discChart b x / discChart b a).im < 0 := by
  have hga : (g • a).re = 0 := normalizer_re_eq_zero hε' hle hge ha
  have hgb : (g • b).re = 0 := normalizer_re_eq_zero hε' hle hge hb
  have hxre : (g • x).re ≠ 0 := by
    have h1 := (normalizer_lt_iff hle hge x).mp hx
    rcases hε' with rfl | rfl
    · rw [one_mul] at h1
      exact h1.ne
    · rw [neg_one_mul, neg_lt_zero] at h1
      exact h1.ne'
  have hAB : 0 < (discChart (g • a) (g • x)).im * (discChart (g • b) (g • x)).im := by
    rcases lt_trichotomy ((g • x)).re 0 with h1 | h1 | h1
    · exact mul_pos (((discChart_im_sign hga (g • x)).1).mpr h1)
        (((discChart_im_sign hgb (g • x)).1).mpr h1)
    · exact absurd h1 hxre
    · exact mul_pos_of_neg_of_neg (((discChart_im_sign hga (g • x)).2.2).mpr h1)
        (((discChart_im_sign hgb (g • x)).2.2).mpr h1)
  have hsum : 0 < (g • b).im + (g • a).im := by
    have := (g • b).im_pos
    have := (g • a).im_pos
    linarith
  have hdiff : (g • b).im - (g • a).im ≠ 0 := by
    intro h
    refine hab (smul_left_cancel g ?_)
    refine (UpperHalfPlane.ext (Complex.ext ?_ ?_)).symm
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hga, hgb]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      linarith
  have hr1 : ((g • b).im + (g • a).im) / ((g • b).im - (g • a).im) ≠ 0 :=
    div_ne_zero hsum.ne' hdiff
  have hr2 : ((g • a).im + (g • b).im) / ((g • a).im - (g • b).im)
      = -(((g • b).im + (g • a).im) / ((g • b).im - (g • a).im)) := by
    rw [show (g • a).im - (g • b).im = -((g • b).im - (g • a).im) from by ring, div_neg,
      add_comm]
  rw [ratio_im_formula hε' hle hge ha hb x, ratio_im_formula hε' hle hge hb ha x,
    hr2, show ∀ A B r : ℝ, A * r * (B * -r) = -(A * B * (r * r)) from fun A B r => by ring]
  rw [neg_lt_zero]
  exact mul_pos hAB (mul_self_pos.mpr hr1)

end SignLemmas

/-- The basepoint direction at a point of a side is transverse to the side direction. -/
theorem side_chi_ne_zero {γ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ)
    {u w : UpperHalfPlane} (hu : u ∈ dirichletSideSet Γ τ₀ γ)
    (hw : w ∈ dirichletSideSet Γ τ₀ γ) (hwu : w ≠ u) :
    (discChart u τ₀ / discChart u w).im ≠ 0 := by
  have hpq : τ₀ ≠ γ • τ₀ := Ne.symm hγ.1
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hpq
  have hx : dist τ₀ τ₀ < dist τ₀ (γ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq
  exact ratio_im_ne_zero hε' hle hge hu.2 hw.2 (Ne.symm hwu) hx

/-- Crossing a side toward its paired side reverses the transverse sign of the basepoint
direction. -/
theorem side_chi_flip_pair {γ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ)
    {u w : UpperHalfPlane} (hu : u ∈ dirichletSideSet Γ τ₀ γ)
    (hw : w ∈ dirichletSideSet Γ τ₀ γ) (hwu : w ≠ u) :
    (discChart u τ₀ / discChart u w).im
      * (discChart (γ⁻¹ • u) τ₀ / discChart (γ⁻¹ • u) (γ⁻¹ • w)).im < 0 := by
  have hpq : τ₀ ≠ γ • τ₀ := Ne.symm hγ.1
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hpq
  have hcoe : ∀ (δ : ↥Γ) (z : UpperHalfPlane),
      δ • z = (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z := fun _ _ => rfl
  have hsecond : (discChart (γ⁻¹ • u) τ₀ / discChart (γ⁻¹ • u) (γ⁻¹ • w)).im
      = (discChart u (γ • τ₀) / discChart u w).im := by
    have key := discChart_ratio_smul ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ u w
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ₀)
    rw [inv_smul_smul] at key
    change (discChart (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ • u) τ₀
        / discChart (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ • u)
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ • w)).im = _
    rw [key]
    rfl
  rw [hsecond]
  have hx : dist τ₀ τ₀ < dist τ₀ (γ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq
  have hy : dist (γ • τ₀) (γ • τ₀) < dist (γ • τ₀) τ₀ := by
    rw [dist_self]
    exact dist_pos.mpr (Ne.symm hpq)
  exact ratio_im_mul_neg_targets hε' hle hge hu.2 hw.2 (Ne.symm hwu) hx hy

/-- At the two endpoints of one side, the basepoint direction has opposite transverse
signs. -/
theorem side_chi_flip_ends {γ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ)
    {a b : UpperHalfPlane} (ha : a ∈ dirichletSideSet Γ τ₀ γ)
    (hb : b ∈ dirichletSideSet Γ τ₀ γ) (hab : a ≠ b) :
    (discChart a τ₀ / discChart a b).im * (discChart b τ₀ / discChart b a).im < 0 := by
  have hpq : τ₀ ≠ γ • τ₀ := Ne.symm hγ.1
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hpq
  have hx : dist τ₀ τ₀ < dist τ₀ (γ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq
  exact ratio_im_mul_neg_frames hε' hle hge ha.2 hb.2 hab hx

/-- At a vertex, the basepoint direction has opposite transverse signs against the two
sides through the vertex. -/
theorem vertex_chi_flip (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {s₁ s₂ : Set UpperHalfPlane} (hs₁ : s₁ ∈ polygonSides Γ τ₀)
    (hs₂ : s₂ ∈ polygonSides Γ τ₀) (hne : s₁ ≠ s₂)
    (he₁ : IsSegEndpoint s₁ v) (he₂ : IsSegEndpoint s₂ v)
    {w₁ w₂ : UpperHalfPlane} (hw₁ : w₁ ∈ s₁) (hw₂ : w₂ ∈ s₂)
    (hw₁v : w₁ ≠ v) (hw₂v : w₂ ≠ v) :
    (discChart v τ₀ / discChart v w₁).im * (discChart v τ₀ / discChart v w₂).im < 0 := by
  have hvτ : τ₀ ≠ v := by
    intro h
    exact basepoint_notMem_side hΓ hfree hε hgap hdense hs₁ (h ▸ he₁.1)
  have ht0 : discChart v τ₀ ≠ 0 := discChart_ne_zero hvτ
  obtain ⟨γ₁, hγ₁, hs₁def⟩ := id hs₁
  obtain ⟨γ₂, hγ₂, hs₂def⟩ := id hs₂
  have hAim : (discChart v τ₀ / discChart v w₁).im ≠ 0 :=
    side_chi_ne_zero hγ₁ (hs₁def ▸ he₁.1) (hs₁def ▸ hw₁) hw₁v
  have hinvim : (discChart v τ₀ / discChart v w₂).im ≠ 0 :=
    side_chi_ne_zero hγ₂ (hs₂def ▸ he₂.1) (hs₂def ▸ hw₂) hw₂v
  have hBinv : discChart v τ₀ / discChart v w₂ = (discChart v w₂ / discChart v τ₀)⁻¹ :=
    (inv_div _ _).symm
  have hBim : (discChart v w₂ / discChart v τ₀).im ≠ 0 := by
    intro h
    rw [hBinv, Complex.inv_im, h] at hinvim
    simp at hinvim
  have hB0 : discChart v w₂ / discChart v τ₀ ≠ 0 := by
    intro h
    rw [h] at hBim
    simp at hBim
  have hA0 : discChart v τ₀ / discChart v w₁ ≠ 0 := by
    intro h
    rw [h] at hAim
    simp at hAim
  have hprod : discChart v τ₀ / discChart v w₁ * (discChart v w₂ / discChart v τ₀)
      = discChart v w₂ / discChart v w₁ := by
    rw [div_mul_div_comm, mul_comm (discChart v w₁) (discChart v τ₀),
      mul_div_mul_left _ _ ht0]
  have hadd := sectorAngle_eq_add_basepoint hΓ hfree hε hgap hdense hv hs₁ hs₂ hne he₁ he₂
    hw₁ hw₂ hw₁v hw₂v
  have hadd' : |Complex.arg (discChart v τ₀ / discChart v w₁
      * (discChart v w₂ / discChart v τ₀))|
      = |Complex.arg (discChart v τ₀ / discChart v w₁)|
        + |Complex.arg (discChart v w₂ / discChart v τ₀)| := by
    rw [hprod]
    exact hadd
  have hsign := same_sign_of_abs_arg_add hA0 hB0 hadd' hAim hBim
  rw [hBinv, Complex.inv_im]
  have hns : 0 < Complex.normSq (discChart v w₂ / discChart v τ₀) :=
    Complex.normSq_pos.mpr hB0
  rw [show (discChart v τ₀ / discChart v w₁).im
      * (-(discChart v w₂ / discChart v τ₀).im
        / Complex.normSq (discChart v w₂ / discChart v τ₀))
      = -((discChart v τ₀ / discChart v w₁).im * (discChart v w₂ / discChart v τ₀).im
        / Complex.normSq (discChart v w₂ / discChart v τ₀)) from by ring]
  exact neg_lt_zero.mpr (div_pos hsign hns)

/-- The paired side is the inverse translate of the side. -/
theorem sideSet_inv_image (γ : ↥Γ) :
    dirichletSideSet Γ τ₀ γ⁻¹ = (γ⁻¹ • ·) '' dirichletSideSet Γ τ₀ γ := by
  ext z
  constructor
  · intro hz
    have h1 := smul_mem_dirichletSideSet_inv (γ := γ⁻¹) hz
    rw [inv_inv] at h1
    exact ⟨γ • z, h1, inv_smul_smul γ z⟩
  · rintro ⟨w, hw, rfl⟩
    exact smul_mem_dirichletSideSet_inv hw

/-- Endpoints of a set transport along the isometric action. -/
theorem isSegEndpoint_smul (γ : ↥Γ) {s : Set UpperHalfPlane} {v : UpperHalfPlane}
    (h : IsSegEndpoint s v) : IsSegEndpoint ((γ • ·) '' s) (γ • v) := by
  obtain ⟨hvs, hext⟩ := h
  refine ⟨⟨v, hvs, rfl⟩, ?_⟩
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩ hmem
  have hcoe : ∀ z : UpperHalfPlane, γ • z = (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z :=
    fun _ => rfl
  have hseg : γ • v ∈ ((γ • ·) '' geodSeg x' y') := by
    have himg := smul_geodSeg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) x' y'
    have : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) '' geodSeg x' y'
        = geodSeg (γ • x') (γ • y') := himg
    rw [show ((γ • ·) '' geodSeg x' y') = ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·)
      '' geodSeg x' y' from rfl, this]
    exact hmem
  obtain ⟨w, hw, hweq⟩ := hseg
  have hvw : v = w := smul_left_cancel γ hweq.symm
  have hvseg : v ∈ geodSeg x' y' := by
    rw [hvw]
    exact hw
  rcases hext x' hx' y' hy' hvseg with h1 | h1
  · exact Or.inl (by change γ • v = γ • x'; rw [h1])
  · exact Or.inr (by change γ • v = γ • y'; rw [h1])

/-- Membership characterization of the endpoints of a nondegenerate side. -/
theorem endpoint_pair {s : Set UpperHalfPlane} {a b : UpperHalfPlane} (hab : a ≠ b)
    (hseq : s = geodSeg a b) (v : UpperHalfPlane) :
    IsSegEndpoint s v ↔ v = a ∨ v = b := by
  rw [hseq, isSegEndpoint_geodSeg_iff hab]

/-- Extraction of the other member of an unordered pair presented two ways. -/
theorem other_of_pair {a b u X : UpperHalfPlane} (_hab : a ≠ b)
    (h : ∀ v : UpperHalfPlane, (v = a ∨ v = b) ↔ (v = u ∨ v = X)) (hXu : X ≠ u)
    [Decidable (u = a)] :
    (if u = a then b else a) = X := by
  by_cases hua : u = a
  · rw [if_pos hua]
    rcases (h X).mpr (Or.inr rfl) with h1 | h1
    · exact absurd (h1.trans hua.symm) hXu
    · exact h1.symm
  · rw [if_neg hua]
    rcases (h u).mpr (Or.inl rfl) with h1 | h1
    · exact absurd h1 hua
    · rcases (h X).mpr (Or.inr rfl) with h2 | h2
      · exact h2.symm
      · exact absurd (h2.trans h1.symm) hXu

/-- Interchange of a filtered incidence double sum. -/
theorem sum_incidence_swap {X Y : Type*} (A : Finset X) (B : Finset Y)
    (P : X → Y → Prop) [∀ x y, Decidable (P x y)] (F : X → Y → ℝ) :
    ∑ x ∈ A, ∑ y ∈ B.filter (fun y => P x y), F x y
      = ∑ y ∈ B, ∑ x ∈ A.filter (fun x => P x y), F x y := by
  simp_rw [Finset.sum_filter]
  exact Finset.sum_comm

/-- A cyclic shift leaves the window sum of a sequence with equal window ends unchanged. -/
theorem sum_shift (f : ℕ → ℝ) (n : ℕ) (hf : f n = f 0) :
    ∑ k ∈ Finset.range n, f (k + 1) = ∑ k ∈ Finset.range n, f k := by
  have h4 := Finset.sum_range_succ' f n
  have h5 := Finset.sum_range_succ f n
  rw [h4, hf] at h5
  linarith

/-- Sign algebra: a unit factor with product `-1` determines the other factor. -/
theorem sign_neg_of_mul {x y : ℝ} (hx : x = 1 ∨ x = -1) (hxy : x * y = -1) :
    y = -x := by
  rcases hx with rfl | rfl <;> linarith

open Classical in
/-- The full-cycle crossing sum at a class vertex, written as a signed dart sum over the
class vertices: the loop contributes each vertex of the class once, through its two sides,
with the transverse signs aligned by one global unit `ς`. -/
theorem class_identity (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ' : UpperHalfPlane, Metric.infDist σ' (MulAction.orbit Γ τ₀) ≤ R)
    {v₀ : UpperHalfPlane} (hv₀ : v₀ ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v₀)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v₀, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {σ : UpperHalfPlane → Set UpperHalfPlane → ℝ}
    (hσpm : ∀ u s, σ u s = 1 ∨ σ u s = -1)
    (hσvert : ∀ v ∈ polygonVertices Γ τ₀, ∀ s₁ ∈ polygonSides Γ τ₀,
      ∀ s₂ ∈ polygonSides Γ τ₀, s₁ ≠ s₂ → IsSegEndpoint s₁ v → IsSegEndpoint s₂ v →
      σ v s₁ * σ v s₂ = -1)
    (hσtrans : ∀ γ : ↥Γ, IsSideElement Γ τ₀ γ → ∀ u : UpperHalfPlane,
      IsSegEndpoint (dirichletSideSet Γ τ₀ γ) u →
      σ u (dirichletSideSet Γ τ₀ γ) * σ (γ⁻¹ • u) (dirichletSideSet Γ τ₀ γ⁻¹) = -1)
    {sel : Set UpperHalfPlane → ↥Γ}
    (hsel : ∀ s ∈ polygonSides Γ τ₀, IsSideElement Γ τ₀ (sel s) ∧
      s = dirichletSideSet Γ τ₀ (sel s))
    (hVfin : (MulAction.orbit Γ v₀ ∩ polygonVertices Γ τ₀).Finite)
    (hSfin : (polygonSides Γ τ₀).Finite) :
    ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧ ∀ α ∈ oddSideFunctions Γ τ₀,
      ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1))
        = ς / 2 * ∑ u ∈ hVfin.toFinset,
            ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u), σ u s * α (sel s) := by
  classical
  set u : ℕ → UpperHalfPlane := fun k => (e k)⁻¹ • v₀ with hudef
  set so : ℕ → Set UpperHalfPlane :=
    fun k => dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) with hsodef
  set si : ℕ → Set UpperHalfPlane :=
    fun k => dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + (n - 1))) with hsidef
  have hFa : ∀ k, u k ∈ polygonVertices Γ τ₀ :=
    fun k => smul_mem_polygonVertices hv₀ (hcon k)
  have hSoMem : ∀ k, so k ∈ polygonSides Γ τ₀ := fun k => ⟨_, hadj k, rfl⟩
  have hSiElt : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + (n - 1))) := by
    intro k
    have h1 := (hadj (k + (n - 1))).inv
    rw [mul_inv_rev, inv_inv, show k + (n - 1) + 1 = k + n from by omega, hper k] at h1
    exact h1
  have hSiMem : ∀ k, si k ∈ polygonSides Γ τ₀ := fun k => ⟨_, hSiElt k, rfl⟩
  have hUo : ∀ k, u k ∈ so k :=
    fun k => smul_mem_dirichletSideSet_of_contact_pair (hcon k) (hcon (k + 1))
  have hUi : ∀ k, u k ∈ si k :=
    fun k => smul_mem_dirichletSideSet_of_contact_pair (hcon k) (hcon (k + (n - 1)))
  have hEo : ∀ k, IsSegEndpoint (so k) (u k) :=
    fun k => isSegEndpoint_of_vertex hΓ hfree hε hgap hdense (hFa k) (hSoMem k) (hUo k)
  have hEi : ∀ k, IsSegEndpoint (si k) (u k) :=
    fun k => isSegEndpoint_of_vertex hΓ hfree hε hgap hdense (hFa k) (hSiMem k) (hUi k)
  have hNe : ∀ k, so k ≠ si k := by
    intro k h
    have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree (hadj k) (hSiElt k) h
    rw [mul_smul, mul_smul] at h1
    have h2 : e (k + 1) • τ₀ = e (k + (n - 1)) • τ₀ := smul_left_cancel _ h1
    have h3 := position_mod_eq hn3 hper hcon huniq h2
    have h4 : n ∣ k + (n - 1) - (k + 1) := (Nat.modEq_iff_dvd' (by omega)).mp h3
    rw [show k + (n - 1) - (k + 1) = n - 2 from by omega] at h4
    have h5 := Nat.le_of_dvd (by omega) h4
    omega
  have hSiNext : ∀ k, si (k + 1) = dirichletSideSet Γ τ₀ (((e k)⁻¹ * e (k + 1))⁻¹) := by
    intro k
    change dirichletSideSet Γ τ₀ ((e (k + 1))⁻¹ * e (k + 1 + (n - 1))) = _
    rw [show k + 1 + (n - 1) = k + n from by omega, hper k, mul_inv_rev, inv_inv]
  have hUNext : ∀ k, ((e k)⁻¹ * e (k + 1))⁻¹ • u k = u (k + 1) := by
    intro k
    change ((e k)⁻¹ * e (k + 1))⁻¹ • ((e k)⁻¹ • v₀) = (e (k + 1))⁻¹ • v₀
    rw [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
  have hsign : ∀ k, σ (u k) (so k) = σ (u 0) (so 0) ∧
      σ (u k) (si k) = -σ (u 0) (so 0) := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, ?_⟩
      have h1 := hσvert (u 0) (hFa 0) (so 0) (hSoMem 0) (si 0) (hSiMem 0) (hNe 0)
        (hEo 0) (hEi 0)
      exact sign_neg_of_mul (hσpm (u 0) (so 0)) h1
    | succ k ih =>
      have h1 := hσtrans ((e k)⁻¹ * e (k + 1)) (hadj k) (u k) (hEo k)
      rw [hUNext k, ← hSiNext k] at h1
      have h2 : σ (u (k + 1)) (si (k + 1)) = -σ (u k) (so k) :=
        sign_neg_of_mul (hσpm (u k) (so k)) h1
      have h4 : σ (u (k + 1)) (so (k + 1)) = -σ (u (k + 1)) (si (k + 1)) := by
        have h5 := hσvert (u (k + 1)) (hFa (k + 1)) (si (k + 1)) (hSiMem (k + 1))
          (so (k + 1)) (hSoMem (k + 1)) (Ne.symm (hNe (k + 1))) (hEi (k + 1)) (hEo (k + 1))
        exact sign_neg_of_mul (hσpm (u (k + 1)) (si (k + 1))) h5
      rw [h2, ih.1] at h4
      exact ⟨by rw [h4, neg_neg], by rw [h2, ih.1]⟩
  refine ⟨σ (u 0) (so 0), hσpm _ _, ?_⟩
  intro α hα
  obtain ⟨-, hodd, hfib⟩ := hα
  have hAout : ∀ k, α (sel (so k)) = α ((e k)⁻¹ * e (k + 1)) := by
    intro k
    have h1 := hsel (so k) (hSoMem k)
    exact hfib _ _ (smul_basepoint_eq_of_sideSet_eq hΓ hfree h1.1 (hadj k) h1.2.symm)
  have hAin : ∀ k, α (sel (si k)) = α ((e k)⁻¹ * e (k + (n - 1))) := by
    intro k
    have h1 := hsel (si k) (hSiMem k)
    exact hfib _ _ (smul_basepoint_eq_of_sideSet_eq hΓ hfree h1.1 (hSiElt k) h1.2.symm)
  have hstepG : ∀ k, α ((e (k + 1))⁻¹ * e (k + 1 + (n - 1))) = α (((e k)⁻¹ * e (k + 1))⁻¹) := by
    intro k
    rw [show k + 1 + (n - 1) = k + n from by omega, hper k, mul_inv_rev, inv_inv]
  have hG0 : α ((e n)⁻¹ * e (n + (n - 1))) = α ((e 0)⁻¹ * e (0 + (n - 1))) := by
    have he1 : e n = e 0 := by
      have h1 := hper 0
      rwa [Nat.zero_add] at h1
    have he2 : e (n + (n - 1)) = e (0 + (n - 1)) := by
      have h1 := hper (n - 1)
      rw [show n + (n - 1) = n - 1 + n from by omega, h1, Nat.zero_add]
    rw [he1, he2]
  have hGshift : ∑ k ∈ Finset.range n, α (((e k)⁻¹ * e (k + 1))⁻¹)
      = ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + (n - 1))) := by
    calc ∑ k ∈ Finset.range n, α (((e k)⁻¹ * e (k + 1))⁻¹)
        = ∑ k ∈ Finset.range n, α ((e (k + 1))⁻¹ * e (k + 1 + (n - 1))) :=
          Finset.sum_congr rfl fun k _ => (hstepG k).symm
      _ = ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + (n - 1))) :=
          sum_shift (fun k => α ((e k)⁻¹ * e (k + (n - 1)))) n hG0
  have hoddsum : ∑ k ∈ Finset.range n, α (((e k)⁻¹ * e (k + 1))⁻¹)
      = -∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hodd _
  have hperk : ∀ k, α ((e k)⁻¹ * e (k + 1)) - α ((e k)⁻¹ * e (k + (n - 1)))
      = σ (u 0) (so 0) * (σ (u k) (so k) * α (sel (so k))
        + σ (u k) (si k) * α (sel (si k))) := by
    intro k
    rw [hAout k, hAin k, (hsign k).1, (hsign k).2]
    rcases hσpm (u 0) (so 0) with h | h <;> rw [h] <;> ring
  have hfilter : ∀ k, hSfin.toFinset.filter (fun s => IsSegEndpoint s (u k))
      = ({so k, si k} : Finset (Set UpperHalfPlane)) := by
    intro k
    ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hsS, hsE⟩
      obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂, he₁, he₂, huniq2⟩ :=
        exists_two_sides_at_vertex hΓ hfree hε hgap hdense (hFa k)
      rcases huniq2 (so k) (hSoMem k) (hEo k) with h1 | h1 <;>
        rcases huniq2 (si k) (hSiMem k) (hEi k) with h2 | h2 <;>
        rcases huniq2 s hsS hsE with h3 | h3
      · exact absurd (h1.trans h2.symm) (hNe k)
      · exact absurd (h1.trans h2.symm) (hNe k)
      · exact Or.inl (h3.trans h1.symm)
      · exact Or.inr (h3.trans h2.symm)
      · exact Or.inr (h3.trans h2.symm)
      · exact Or.inl (h3.trans h1.symm)
      · exact absurd (h1.trans h2.symm) (hNe k)
      · exact absurd (h1.trans h2.symm) (hNe k)
    · rintro (rfl | rfl)
      · exact ⟨hSoMem k, hEo k⟩
      · exact ⟨hSiMem k, hEi k⟩
  have hbij : ∑ k ∈ Finset.range n, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s (u k)), σ (u k) s * α (sel s)
      = ∑ w ∈ hVfin.toFinset, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s w), σ w s * α (sel s) := by
    refine Finset.sum_bij (fun k _ => u k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Set.Finite.mem_toFinset]
      exact ⟨MulAction.mem_orbit_iff.mpr ⟨(e k)⁻¹, rfl⟩, hFa k⟩
    · intro k hk j hj huv
      rw [Finset.mem_range] at hk hj
      have h1 : (e j * (e k)⁻¹) • v₀ = v₀ := by
        rw [mul_smul, show (e k)⁻¹ • v₀ = (e j)⁻¹ • v₀ from huv, smul_inv_smul]
      have h2 := hfree (e j * (e k)⁻¹) ⟨v₀, h1⟩ (e k • τ₀)
      rw [mul_smul, inv_smul_smul] at h2
      have h3 := position_mod_eq hn3 hper hcon huniq h2
      rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] at h3
      exact h3.symm
    · intro w hw
      rw [Set.Finite.mem_toFinset] at hw
      obtain ⟨horb, hvert⟩ := hw
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horb
      have hcon' : g⁻¹ ∈ contactSet Γ τ₀ v₀ := by
        rw [mem_contactSet_iff_mem_smul_dirichletDomain]
        refine ⟨w, hvert.1, ?_⟩
        change g⁻¹ • w = v₀
        rw [← hg, inv_smul_smul]
      obtain ⟨k, ⟨hkn, hkτ⟩, -⟩ := huniq g⁻¹ hcon'
      refine ⟨k, Finset.mem_range.mpr hkn, ?_⟩
      have h4 := inv_smul_eq_of_basepoint_eq hfree hkτ v₀
      rw [inv_inv] at h4
      exact h4.symm.trans hg
    · intro k hk
      rfl
  have hpairs : ∑ k ∈ Finset.range n, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s (u k)), σ (u k) s * α (sel s)
      = ∑ k ∈ Finset.range n, (σ (u k) (so k) * α (sel (so k))
        + σ (u k) (si k) * α (sel (si k))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfilter k]
    exact Finset.sum_pair (hNe k)
  have hmain : 2 * ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1))
      = σ (u 0) (so 0) * ∑ w ∈ hVfin.toFinset, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s w), σ w s * α (sel s) := by
    calc 2 * ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1))
        = ∑ k ∈ Finset.range n,
            (α ((e k)⁻¹ * e (k + 1)) - α ((e k)⁻¹ * e (k + (n - 1)))) := by
          rw [Finset.sum_sub_distrib, ← hGshift, hoddsum]
          ring
      _ = ∑ k ∈ Finset.range n, σ (u 0) (so 0) * (σ (u k) (so k) * α (sel (so k))
            + σ (u k) (si k) * α (sel (si k))) :=
          Finset.sum_congr rfl fun k _ => hperk k
      _ = σ (u 0) (so 0) * ∑ k ∈ Finset.range n, (σ (u k) (so k) * α (sel (so k))
            + σ (u k) (si k) * α (sel (si k))) := by
          rw [Finset.mul_sum]
      _ = σ (u 0) (so 0) * ∑ w ∈ hVfin.toFinset, ∑ s ∈ hSfin.toFinset.filter
            (fun s => IsSegEndpoint s w), σ w s * α (sel s) := by
          rw [← hpairs, hbij]
  linear_combination hmain / 2

/-- Unit signs of two reals with negative product multiply to `-1`. -/
theorem ite_sign_mul {x y : ℝ} (h : x * y < 0) [Decidable (0 < x)]
    [Decidable (0 < y)] :
    (if 0 < x then (1 : ℝ) else -1) * (if 0 < y then (1 : ℝ) else -1) = -1 := by
  by_cases h1 : 0 < x <;> by_cases h2 : 0 < y
  · exact absurd h (by nlinarith)
  · simp [h1, h2]
  · simp [h1, h2]
  · exfalso
    push Not at h1 h2
    nlinarith

/-- Two presentations of an unordered pair give the same membership predicate. -/
theorem pair_perm {p1 p2 a b : UpperHalfPlane} (hab : a ≠ b)
    (ha : a = p1 ∨ a = p2) (hb : b = p1 ∨ b = p2) (v : UpperHalfPlane) :
    (v = p1 ∨ v = p2) ↔ (v = a ∨ v = b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact Iff.rfl
  · exact or_comm
  · exact absurd rfl hab

open Classical in
/-- A transverse-sign function on vertex-side darts, together with side-element and
endpoint selections: the sign flips across each vertex, along each side, and under the
side pairing. -/
theorem exists_sigma_sel (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ' : UpperHalfPlane, Metric.infDist σ' (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ (σ : UpperHalfPlane → Set UpperHalfPlane → ℝ) (sel : Set UpperHalfPlane → ↥Γ)
      (ep1 ep2 : Set UpperHalfPlane → UpperHalfPlane),
      (∀ u s, σ u s = 1 ∨ σ u s = -1) ∧
      (∀ s ∈ polygonSides Γ τ₀, IsSideElement Γ τ₀ (sel s) ∧
        s = dirichletSideSet Γ τ₀ (sel s)) ∧
      (∀ s ∈ polygonSides Γ τ₀, ep1 s ≠ ep2 s ∧ s = geodSeg (ep1 s) (ep2 s)) ∧
      (∀ v ∈ polygonVertices Γ τ₀, ∀ s₁ ∈ polygonSides Γ τ₀, ∀ s₂ ∈ polygonSides Γ τ₀,
        s₁ ≠ s₂ → IsSegEndpoint s₁ v → IsSegEndpoint s₂ v → σ v s₁ * σ v s₂ = -1) ∧
      (∀ s ∈ polygonSides Γ τ₀, ∀ a b : UpperHalfPlane, IsSegEndpoint s a →
        IsSegEndpoint s b → a ≠ b → σ a s * σ b s = -1) ∧
      (∀ γ : ↥Γ, IsSideElement Γ τ₀ γ → ∀ u : UpperHalfPlane,
        IsSegEndpoint (dirichletSideSet Γ τ₀ γ) u →
        σ u (dirichletSideSet Γ τ₀ γ) * σ (γ⁻¹ • u) (dirichletSideSet Γ τ₀ γ⁻¹) = -1) := by
  classical
  have hselex : ∀ s ∈ polygonSides Γ τ₀, ∃ γ : ↥Γ, IsSideElement Γ τ₀ γ ∧
      s = dirichletSideSet Γ τ₀ γ := fun s hs => hs
  choose! sel hsel1 hsel2 using hselex
  choose! ep1 ep2 hepne hepeq using
    (fun s (hs : s ∈ polygonSides Γ τ₀) =>
      exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs)
  obtain ⟨oe, hoedef⟩ : ∃ oe : UpperHalfPlane → Set UpperHalfPlane → UpperHalfPlane,
      oe = fun u s => if u = ep1 s then ep2 s else ep1 s := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : UpperHalfPlane → Set UpperHalfPlane → ℝ,
      σ = fun u s =>
        if 0 < (discChart u τ₀ / discChart u (oe u s)).im then 1 else -1 := ⟨_, rfl⟩
  have hoeval : ∀ u s, oe u s = if u = ep1 s then ep2 s else ep1 s :=
    fun u s => by rw [hoedef]
  have hσval : ∀ u s,
      σ u s = if 0 < (discChart u τ₀ / discChart u (oe u s)).im then 1 else -1 :=
    fun u s => by rw [hσdef]
  have hσpm : ∀ u s, σ u s = 1 ∨ σ u s = -1 := by
    intro u s
    rw [hσval]
    by_cases h : 0 < (discChart u τ₀ / discChart u (oe u s)).im
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  have hoe : ∀ s ∈ polygonSides Γ τ₀, ∀ u : UpperHalfPlane, IsSegEndpoint s u →
      oe u s ∈ s ∧ oe u s ≠ u ∧ IsSegEndpoint s (oe u s) ∧ s = geodSeg u (oe u s) := by
    intro s hs u hu
    have hiff := endpoint_pair (hepne s hs) (hepeq s hs)
    have hmem1 : ep1 s ∈ s := by
      have h := left_mem_geodSeg (ep1 s) (ep2 s)
      rwa [← hepeq s hs] at h
    have hmem2 : ep2 s ∈ s := by
      have h := right_mem_geodSeg (ep1 s) (ep2 s)
      rwa [← hepeq s hs] at h
    rcases (hiff u).mp hu with h1 | h1
    · have hval : oe u s = ep2 s := by rw [hoeval, if_pos h1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hval]
        exact hmem2
      · rw [hval, h1]
        exact Ne.symm (hepne s hs)
      · rw [hval]
        exact (hiff _).mpr (Or.inr rfl)
      · rw [hval, h1]
        exact hepeq s hs
    · have hne1 : u ≠ ep1 s := by
        rw [h1]
        exact Ne.symm (hepne s hs)
      have hval : oe u s = ep1 s := by rw [hoeval, if_neg hne1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hval]
        exact hmem1
      · rw [hval]
        exact fun h => hne1 h.symm
      · rw [hval]
        exact (hiff _).mpr (Or.inl rfl)
      · rw [hval, h1]
        exact (hepeq s hs).trans (geodSeg_comm _ _)
  refine ⟨σ, sel, ep1, ep2, hσpm, fun s hs => ⟨hsel1 s hs, hsel2 s hs⟩,
    fun s hs => ⟨hepne s hs, hepeq s hs⟩, ?_, ?_, ?_⟩
  · intro v hv s₁ hs₁ s₂ hs₂ hne he₁ he₂
    obtain ⟨hw₁s, hw₁v, -, -⟩ := hoe s₁ hs₁ v he₁
    obtain ⟨hw₂s, hw₂v, -, -⟩ := hoe s₂ hs₂ v he₂
    have hflip := vertex_chi_flip hΓ hfree hε hgap hdense hv hs₁ hs₂ hne he₁ he₂
      hw₁s hw₂s hw₁v hw₂v
    rw [hσval, hσval]
    exact ite_sign_mul hflip
  · intro s hs a b ha hb hab
    have ha' := (endpoint_pair (hepne s hs) (hepeq s hs) a).mp ha
    have hb' := (endpoint_pair (hepne s hs) (hepeq s hs) b).mp hb
    have hoea : oe a s = b := by
      rw [hoeval]
      exact other_of_pair (hepne s hs) (pair_perm hab ha' hb') (Ne.symm hab)
    have hoeb : oe b s = a := by
      rw [hoeval]
      exact other_of_pair (hepne s hs) (pair_perm (Ne.symm hab) hb' ha') hab
    have haS : a ∈ dirichletSideSet Γ τ₀ (sel s) := by
      rw [← hsel2 s hs]
      exact ha.1
    have hbS : b ∈ dirichletSideSet Γ τ₀ (sel s) := by
      rw [← hsel2 s hs]
      exact hb.1
    have hflip := side_chi_flip_ends (hsel1 s hs) haS hbS hab
    rw [hσval, hσval, hoea, hoeb]
    exact ite_sign_mul hflip
  · intro γ hγ u hu
    have hsγ : dirichletSideSet Γ τ₀ γ ∈ polygonSides Γ τ₀ := ⟨γ, hγ, rfl⟩
    have hsγ' : dirichletSideSet Γ τ₀ γ⁻¹ ∈ polygonSides Γ τ₀ := ⟨γ⁻¹, hγ.inv, rfl⟩
    obtain ⟨hwmem, hwne, hwend, hseq⟩ := hoe _ hsγ u hu
    have himg : dirichletSideSet Γ τ₀ γ⁻¹ = (γ⁻¹ • ·) '' dirichletSideSet Γ τ₀ γ :=
      sideSet_inv_image γ
    have hu' : IsSegEndpoint (dirichletSideSet Γ τ₀ γ⁻¹) (γ⁻¹ • u) := by
      rw [himg]
      exact isSegEndpoint_smul γ⁻¹ hu
    have hw' : IsSegEndpoint (dirichletSideSet Γ τ₀ γ⁻¹)
        (γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ)) := by
      rw [himg]
      exact isSegEndpoint_smul γ⁻¹ hwend
    have hne' : γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ) ≠ γ⁻¹ • u :=
      fun h => hwne (smul_left_cancel γ⁻¹ h)
    have hseq' : dirichletSideSet Γ τ₀ γ⁻¹
        = geodSeg (γ⁻¹ • u) (γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ)) := by
      refine himg.trans ((congrArg (fun t => (γ⁻¹ • ·) '' t) hseq).trans ?_)
      exact smul_geodSeg ((γ⁻¹ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) u
        (oe u (dirichletSideSet Γ τ₀ γ))
    have hoeu' : oe (γ⁻¹ • u) (dirichletSideSet Γ τ₀ γ⁻¹)
        = γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ) := by
      rw [hoeval]
      refine other_of_pair (hepne _ hsγ') ?_ hne'
      intro v
      refine (endpoint_pair (hepne _ hsγ') (hepeq _ hsγ') v).symm.trans ?_
      constructor
      · intro hv
        rw [hseq'] at hv
        exact (isSegEndpoint_geodSeg_iff (Ne.symm hne')).mp hv
      · rintro (rfl | rfl)
        · exact hu'
        · exact hw'
    have hflip := side_chi_flip_pair hγ hu.1 hwmem hwne
    rw [hσval, hσval, hoeu']
    exact ite_sign_mul hflip

open Classical in
/-- The vertex-class constraint functionals of the polygon: one crossing-sum functional per
vertex class, cutting out exactly the cycle-constrained side functions, with unit weights
whose weighted constraint sum vanishes identically and spans all linear dependencies. -/
theorem exists_constraint_data (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ' : UpperHalfPlane, Metric.infDist σ' (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ (Φ : Set UpperHalfPlane → ((↥Γ) → ℝ) → ℝ) (εs : Set UpperHalfPlane → ℝ),
      (∀ C ∈ polygonVertexClasses Γ τ₀, εs C = 1 ∨ εs C = -1) ∧
      (∀ C ∈ polygonVertexClasses Γ τ₀, ∀ α β : (↥Γ) → ℝ,
        Φ C (α + β) = Φ C α + Φ C β) ∧
      (∀ C ∈ polygonVertexClasses Γ τ₀, ∀ (c : ℝ) (α : (↥Γ) → ℝ),
        Φ C (c • α) = c * Φ C α) ∧
      (∀ α ∈ cycleConstrained Γ τ₀, ∀ C ∈ polygonVertexClasses Γ τ₀, Φ C α = 0) ∧
      (∀ α ∈ oddSideFunctions Γ τ₀,
        (∀ C ∈ polygonVertexClasses Γ τ₀, Φ C α = 0) → α ∈ cycleConstrained Γ τ₀) ∧
      (∀ α ∈ oddSideFunctions Γ τ₀,
        ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, εs C * Φ C α = 0) ∧
      (∀ m : Set UpperHalfPlane → ℝ,
        (∀ α ∈ oddSideFunctions Γ τ₀,
          ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, m C * Φ C α = 0) →
        ∀ C ∈ polygonVertexClasses Γ τ₀, ∀ C' ∈ polygonVertexClasses Γ τ₀,
          m C * εs C = m C' * εs C') := by
  classical
  obtain ⟨σ, sel, ep1, ep2, hσpm, hselp, hepp, hσvert, hσside, hσtrans⟩ :=
    exists_sigma_sel hΓ hfree hε hgap hdense
  have hSfin := finite_polygonSides hΓ hfree hε hgap hdense
  have hVfin := finite_polygonVertices hΓ hfree hε hgap hdense
  have hclassrep : ∀ C ∈ polygonVertexClasses Γ τ₀, ∃ v₀ : UpperHalfPlane,
      v₀ ∈ polygonVertices Γ τ₀ ∧ C = MulAction.orbit Γ v₀ ∩ polygonVertices Γ τ₀ :=
    fun C hC => hC
  choose! vC hvC1 hvC2 using hclassrep
  have hcycex : ∀ C ∈ polygonVertexClasses Γ τ₀, ∃ p : ℕ × (ℕ → ↥Γ),
      3 ≤ p.1 ∧ (∀ k, p.2 (k + p.1) = p.2 k) ∧
      (∀ k, p.2 k ∈ contactSet Γ τ₀ (vC C)) ∧
      (∀ γ ∈ contactSet Γ τ₀ (vC C), ∃! k, k < p.1 ∧ γ • τ₀ = p.2 k • τ₀) ∧
      ∀ k, IsSideElement Γ τ₀ ((p.2 k)⁻¹ * p.2 (k + 1)) := by
    intro C hC
    obtain ⟨n, e, h1, h2, h3, h4, h5⟩ :=
      exists_vertex_cycle hΓ hfree hε hgap hdense (hvC1 C hC)
    exact ⟨(n, e), h1, h2, h3, h4, h5⟩
  choose! cyc hcyc1 hcyc2 hcyc3 hcyc4 hcyc5 using hcycex
  have hCfin : ∀ C : Set UpperHalfPlane,
      (MulAction.orbit Γ (vC C) ∩ polygonVertices Γ τ₀).Finite :=
    fun C => hVfin.subset Set.inter_subset_right
  have hkey : ∀ C ∈ polygonVertexClasses Γ τ₀, ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧
      ∀ α ∈ oddSideFunctions Γ τ₀,
      ∑ k ∈ Finset.range (cyc C).1, α (((cyc C).2 k)⁻¹ * (cyc C).2 (k + 1))
        = ς / 2 * ∑ u ∈ (hCfin C).toFinset,
            ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u),
              σ u s * α (sel s) :=
    fun C hC => class_identity hΓ hfree hε hgap hdense (hvC1 C hC) (hcyc1 C hC)
      (hcyc2 C hC) (hcyc3 C hC) (hcyc4 C hC) (hcyc5 C hC) hσpm hσvert hσtrans
      (fun s hs => hselp s hs) (hCfin C) hSfin
  choose! ςf hς1 hς2 using hkey
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Set UpperHalfPlane → ((↥Γ) → ℝ) → ℝ,
      Φ = fun C α =>
        ∑ k ∈ Finset.range (cyc C).1, α (((cyc C).2 k)⁻¹ * (cyc C).2 (k + 1)) := ⟨_, rfl⟩
  have hΦval : ∀ C α, Φ C α
      = ∑ k ∈ Finset.range (cyc C).1, α (((cyc C).2 k)⁻¹ * (cyc C).2 (k + 1)) :=
    fun C α => by rw [hΦdef]
  have hclassfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine (hVfin.image (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have hfconv : ∀ f : Set UpperHalfPlane → ℝ,
      ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, f C = ∑ C ∈ hclassfin.toFinset, f C := by
    intro f
    exact finsum_mem_eq_finite_toFinset_sum f hclassfin
  have hepfilter : ∀ s ∈ polygonSides Γ τ₀,
      hVfin.toFinset.filter (fun u => IsSegEndpoint s u)
        = ({ep1 s, ep2 s} : Finset UpperHalfPlane) ∧
      IsSegEndpoint s (ep1 s) ∧ IsSegEndpoint s (ep2 s) := by
    intro s hs
    have he1 : IsSegEndpoint s (ep1 s) :=
      (endpoint_pair (hepp s hs).1 (hepp s hs).2 _).mpr (Or.inl rfl)
    have he2 : IsSegEndpoint s (ep2 s) :=
      (endpoint_pair (hepp s hs).1 (hepp s hs).2 _).mpr (Or.inr rfl)
    refine ⟨?_, he1, he2⟩
    ext u
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, hu⟩
      exact (endpoint_pair (hepp s hs).1 (hepp s hs).2 u).mp hu
    · rintro (rfl | rfl)
      · exact ⟨mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs he1, he1⟩
      · exact ⟨mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs he2, he2⟩
  have hweighted : ∀ w : Set UpperHalfPlane → ℝ, ∀ α ∈ oddSideFunctions Γ τ₀,
      ∑ C ∈ hclassfin.toFinset, w C * Φ C α
        = ∑ s ∈ hSfin.toFinset, ∑ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s u),
            w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ u s * α (sel s)) := by
    intro w α hα
    have h1 : ∀ C ∈ hclassfin.toFinset, w C * Φ C α
        = ∑ u ∈ (hCfin C).toFinset, w C * ςf C / 2
            * ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u),
                σ u s * α (sel s) := by
      intro C hC'
      rw [Set.Finite.mem_toFinset] at hC'
      rw [hΦval, hς2 C hC' α hα, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl h1]
    have h2 : ∀ C ∈ hclassfin.toFinset, ∑ u ∈ (hCfin C).toFinset, w C * ςf C / 2
        * ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u), σ u s * α (sel s)
        = ∑ u ∈ (hCfin C).toFinset,
            w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u),
                  σ u s * α (sel s) := by
      intro C hC'
      rw [Set.Finite.mem_toFinset] at hC'
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Set.Finite.mem_toFinset] at hu
      have h3 : MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ = C := by
        rw [hvC2 C hC']
        congr 1
        exact MulAction.orbit_eq_iff.mpr hu.1
      rw [h3]
    rw [Finset.sum_congr rfl h2]
    have hdisj : (↑hclassfin.toFinset : Set (Set UpperHalfPlane)).PairwiseDisjoint
        (fun C => (hCfin C).toFinset) := by
      intro C hCm C' hC'm hne
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hCm hC'm
      refine Finset.disjoint_left.mpr fun u hu1 hu2 => ?_
      rw [Set.Finite.mem_toFinset] at hu1 hu2
      refine hne ?_
      rw [hvC2 C hCm, hvC2 C' hC'm]
      congr 1
      rw [← MulAction.orbit_eq_iff.mpr hu1.1, ← MulAction.orbit_eq_iff.mpr hu2.1]
    have hbiun : hclassfin.toFinset.biUnion (fun C => (hCfin C).toFinset)
        = hVfin.toFinset := by
      ext u
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨C, hC', hu⟩
        exact hu.2
      · intro hu
        refine ⟨MulAction.orbit Γ u ∩ polygonVertices Γ τ₀, ⟨u, hu, rfl⟩, ?_, hu⟩
        have h1' := hvC2 _ (⟨u, hu, rfl⟩ :
          MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ ∈ polygonVertexClasses Γ τ₀)
        have h2' : u ∈ MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ :=
          ⟨MulAction.mem_orbit_self u, hu⟩
        rw [h1'] at h2'
        exact h2'.1
    rw [← Finset.sum_biUnion hdisj, hbiun]
    rw [Finset.sum_congr rfl fun u (_ : u ∈ hVfin.toFinset) => Finset.mul_sum
      (hSfin.toFinset.filter (fun s => IsSegEndpoint s u))
      (fun s => σ u s * α (sel s))
      (w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
        * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2)]
    exact sum_incidence_swap hVfin.toFinset hSfin.toFinset
      (fun u s => IsSegEndpoint s u)
      (fun u s => w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
        * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2 * (σ u s * α (sel s)))
  refine ⟨Φ, ςf, hς1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC α β
    rw [hΦval, hΦval, hΦval]
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  · intro C hC c α
    rw [hΦval, hΦval]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm
  · intro α hα C hC
    have hloop : IsVertexLoop Γ τ₀ (vC C) (loopList (cyc C).2 0 (cyc C).1) := by
      refine ⟨isTilePath_loopList _ (hcyc5 C hC) _ _, ?_, ?_⟩
      · intro γ hγ
        obtain ⟨i, hi, rfl⟩ := loopList_mem _ _ _ _ hγ
        exact hcyc3 C hC (0 + i)
      · rw [loopList_head?, loopList_getLast?, hcyc2 C hC 0]
    have hcs := (mem_cycleConstrained.mp hα).2 (vC C) (hvC1 C hC) _ hloop
    rw [crossingSum_loopList] at hcs
    rw [hΦval]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hcs
    rw [Nat.zero_add]
  · intro α hα hzeros
    refine ⟨hα, ?_⟩
    intro v hv p hp
    have hC : MulAction.orbit Γ v ∩ polygonVertices Γ τ₀ ∈ polygonVertexClasses Γ τ₀ :=
      ⟨v, hv, rfl⟩
    have hvorb : v ∈ MulAction.orbit Γ (vC (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)) := by
      have h1 := hvC2 _ hC
      have h2 : v ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀ :=
        ⟨MulAction.mem_orbit_self v, hv⟩
      rw [h1] at h2
      exact h2.1
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hvorb
    obtain ⟨e', he'⟩ : ∃ e' : ℕ → ↥Γ,
        e' = fun k => g * (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 k := ⟨_, rfl⟩
    have he'val : ∀ k, e' k
        = g * (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 k :=
      fun k => by rw [he']
    have htrans' : ∀ k, (e' k)⁻¹ * e' (k + 1)
        = ((cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 k)⁻¹
          * (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 (k + 1) := by
      intro k
      rw [he'val, he'val, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    have hper' : ∀ k, e' (k + (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).1) = e' k := by
      intro k
      rw [he'val, he'val, hcyc2 _ hC k]
    have hcon' : ∀ k, e' k ∈ contactSet Γ τ₀ v := by
      intro k
      rw [he'val]
      have h1 := (contact_shift g _ _).mp (hcyc3 _ hC k)
      rwa [hg] at h1
    have huniq' : ∀ γ ∈ contactSet Γ τ₀ v,
        ∃! k, k < (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).1
          ∧ γ • τ₀ = e' k • τ₀ := by
      intro γ hγ
      have hγ' : g⁻¹ * γ
          ∈ contactSet Γ τ₀ (vC (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)) := by
        refine (contact_shift g (g⁻¹ * γ) _).mpr ?_
        rw [mul_inv_cancel_left, hg]
        exact hγ
      obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hcyc4 _ hC (g⁻¹ * γ) hγ'
      refine ⟨k, ⟨hk1, ?_⟩, ?_⟩
      · rw [he'val, mul_smul, ← hk2, mul_smul, smul_inv_smul]
      · rintro k' ⟨hk'1, hk'2⟩
        refine hk3 k' ⟨hk'1, ?_⟩
        rw [he'val] at hk'2
        rw [mul_smul, hk'2, mul_smul, inv_smul_smul]
    have hadj' : ∀ k, IsSideElement Γ τ₀ ((e' k)⁻¹ * e' (k + 1)) := by
      intro k
      rw [htrans' k]
      exact hcyc5 _ hC k
    have hzero' : ∑ i ∈ Finset.range
        (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).1,
        α ((e' i)⁻¹ * e' (i + 1)) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun k _ => by rw [htrans' k]) ?_
      have h1 := hzeros _ hC
      rw [hΦval] at h1
      exact h1
    exact closed_loop_sum hΓ hfree hε hgap hdense hv (hcyc1 _ hC) hper' hcon'
      huniq' hadj' hα.2.1 hα.2.2 hzero' hp
  · intro α hα
    rw [hfconv, hweighted ςf α hα]
    refine Finset.sum_eq_zero fun s hs' => ?_
    rw [Set.Finite.mem_toFinset] at hs'
    obtain ⟨hfeq, he1, he2⟩ := hepfilter s hs'
    rw [hfeq, Finset.sum_pair (hepp s hs').1]
    have hc1 : MulAction.orbit Γ (ep1 s) ∩ polygonVertices Γ τ₀
        ∈ polygonVertexClasses Γ τ₀ :=
      ⟨ep1 s, mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs' he1, rfl⟩
    have hc2 : MulAction.orbit Γ (ep2 s) ∩ polygonVertices Γ τ₀
        ∈ polygonVertexClasses Γ τ₀ :=
      ⟨ep2 s, mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs' he2, rfl⟩
    have hσs : σ (ep2 s) s = -σ (ep1 s) s :=
      sign_neg_of_mul (hσpm (ep1 s) s) (hσside s hs' _ _ he1 he2 (hepp s hs').1)
    rw [hσs]
    rcases hς1 _ hc1 with h | h <;> rcases hς1 _ hc2 with h' | h' <;> rw [h, h'] <;> ring
  · intro m hm C hC C' hC'
    have hsideRel : ∀ s ∈ polygonSides Γ τ₀, ∀ a b : UpperHalfPlane, IsSegEndpoint s a →
        IsSegEndpoint s b →
        m (MulAction.orbit Γ a ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ a ∩ polygonVertices Γ τ₀)
        = m (MulAction.orbit Γ b ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ b ∩ polygonVertices Γ τ₀) := by
      intro s hs a b ha hb
      have hβ := (hselp s hs).1
      have hsβ := (hselp s hs).2
      have hs' : dirichletSideSet Γ τ₀ (sel s)⁻¹ ∈ polygonSides Γ τ₀ :=
        ⟨(sel s)⁻¹, hβ.inv, rfl⟩
      have hnss' : s ≠ dirichletSideSet Γ τ₀ (sel s)⁻¹ := by
        intro h
        exact sideElement_smul_ne_inv hfree hβ
          (smul_basepoint_eq_of_sideSet_eq hΓ hfree hβ hβ.inv (hsβ.symm.trans h))
      obtain ⟨αP, hαPV, hαP1, hαP2, hαP3⟩ := exists_indicator hfree hβ
      have h0 := hm αP hαPV
      rw [hfconv, hweighted m αP hαPV] at h0
      have hval_other : ∀ s'' ∈ polygonSides Γ τ₀, s'' ≠ s →
          s'' ≠ dirichletSideSet Γ τ₀ (sel s)⁻¹ → αP (sel s'') = 0 := by
        intro s'' hs'' hne1 hne2
        refine hαP3 _ (fun h => hne1 ?_) (fun h => hne2 ?_)
        · rw [(hselp s'' hs'').2, hsβ]
          exact sideSet_eq_of_basepoint_eq h
        · rw [(hselp s'' hs'').2]
          exact sideSet_eq_of_basepoint_eq h
      have hsub : ({s, dirichletSideSet Γ τ₀ (sel s)⁻¹} : Finset (Set UpperHalfPlane))
          ⊆ hSfin.toFinset := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Set.Finite.mem_toFinset]
        rcases hx with rfl | rfl
        · exact hs
        · exact hs'
      have hcollapse : ∑ s'' ∈ hSfin.toFinset, ∑ u ∈ hVfin.toFinset.filter
            (fun u => IsSegEndpoint s'' u),
            m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ u s'' * αP (sel s''))
          = ∑ s'' ∈ ({s, dirichletSideSet Γ τ₀ (sel s)⁻¹} : Finset (Set UpperHalfPlane)),
              ∑ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s'' u),
                m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
                  * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
                  * (σ u s'' * αP (sel s'')) := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx hxmem
        rw [Set.Finite.mem_toFinset] at hx
        have hx1 : x ≠ s := fun h => hxmem (by rw [h]; exact Finset.mem_insert_self _ _)
        have hx2 : x ≠ dirichletSideSet Γ τ₀ (sel s)⁻¹ := fun h => hxmem (by
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [hval_other x hx hx1 hx2, mul_zero, mul_zero]
      rw [hcollapse, Finset.sum_pair hnss'] at h0
      have hσflip : ∀ u : UpperHalfPlane, IsSegEndpoint s u →
          σ ((sel s)⁻¹ • u) (dirichletSideSet Γ τ₀ (sel s)⁻¹) = -σ u s := by
        intro u hu
        have h1 : IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)) u := by
          rw [← hsβ]
          exact hu
        have h2 := hσtrans (sel s) hβ u h1
        rw [← hsβ] at h2
        exact sign_neg_of_mul (hσpm u s) h2
      have hocinv : ∀ u : UpperHalfPlane,
          MulAction.orbit Γ ((sel s)⁻¹ • u) ∩ polygonVertices Γ τ₀
            = MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ := by
        intro u
        congr 1
        exact MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit u (sel s)⁻¹)
      have hendp' : ∀ u : UpperHalfPlane, IsSegEndpoint s u →
          IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)⁻¹) ((sel s)⁻¹ • u) := by
        intro u hu
        rw [sideSet_inv_image (sel s)]
        refine isSegEndpoint_smul _ ?_
        rw [← hsβ]
        exact hu
      have hendp'' : ∀ u' : UpperHalfPlane,
          IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)⁻¹) u' →
          IsSegEndpoint s ((sel s) • u') := by
        intro u' hu'
        have h1 := sideSet_inv_image (τ₀ := τ₀) (sel s)⁻¹
        rw [inv_inv] at h1
        have h2 : IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)) ((sel s) • u') := by
          rw [h1]
          exact isSegEndpoint_smul _ hu'
        rw [← hsβ] at h2
        exact h2
      have hbij2 : ∑ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s u),
            m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ ((sel s)⁻¹ • u) (dirichletSideSet Γ τ₀ (sel s)⁻¹)
                * αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹)))
          = ∑ u' ∈ hVfin.toFinset.filter
              (fun u => IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)⁻¹) u),
              m (MulAction.orbit Γ u' ∩ polygonVertices Γ τ₀)
                * ςf (MulAction.orbit Γ u' ∩ polygonVertices Γ τ₀) / 2
                * (σ u' (dirichletSideSet Γ τ₀ (sel s)⁻¹)
                  * αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹))) := by
        refine Finset.sum_bij (fun u _ => (sel s)⁻¹ • u) ?_ ?_ ?_ ?_
        · intro u hu
          rw [Finset.mem_filter] at hu ⊢
          refine ⟨?_, hendp' u hu.2⟩
          rw [Set.Finite.mem_toFinset]
          exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs'
            (hendp' u hu.2)
        · intro u hu u₂ hu₂ h
          exact smul_left_cancel _ h
        · intro u' hu'
          rw [Finset.mem_filter] at hu'
          refine ⟨(sel s) • u', ?_, inv_smul_smul _ _⟩
          rw [Finset.mem_filter]
          refine ⟨?_, hendp'' u' hu'.2⟩
          rw [Set.Finite.mem_toFinset]
          exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs
            (hendp'' u' hu'.2)
        · intro u hu
          rw [← hocinv u]
      rw [← hbij2, ← Finset.sum_add_distrib] at h0
      have hv2 : αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹)) = -1 :=
        hαP2 _ (smul_basepoint_eq_of_sideSet_eq hΓ hfree (hselp _ hs').1 hβ.inv
          (hselp _ hs').2.symm)
      have hsimpl : ∀ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s u),
          m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ u s * αP (sel s))
            + m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ ((sel s)⁻¹ • u) (dirichletSideSet Γ τ₀ (sel s)⁻¹)
                * αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹)))
          = m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) * σ u s := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [hαP1 _ rfl, hv2, hσflip u hu.2]
        ring
      rw [Finset.sum_congr rfl hsimpl] at h0
      obtain ⟨hfeq, he1, he2⟩ := hepfilter s hs
      rw [hfeq, Finset.sum_pair (hepp s hs).1] at h0
      have hσ21 : σ (ep2 s) s = -σ (ep1 s) s :=
        sign_neg_of_mul (hσpm (ep1 s) s) (hσside s hs _ _ he1 he2 (hepp s hs).1)
      rw [hσ21] at h0
      have hkey2 : m (MulAction.orbit Γ (ep1 s) ∩ polygonVertices Γ τ₀)
            * ςf (MulAction.orbit Γ (ep1 s) ∩ polygonVertices Γ τ₀)
          = m (MulAction.orbit Γ (ep2 s) ∩ polygonVertices Γ τ₀)
            * ςf (MulAction.orbit Γ (ep2 s) ∩ polygonVertices Γ τ₀) := by
        rcases hσpm (ep1 s) s with h | h <;> rw [h] at h0 <;> linarith
      have ha' := (endpoint_pair (hepp s hs).1 (hepp s hs).2 a).mp ha
      have hb' := (endpoint_pair (hepp s hs).1 (hepp s hs).2 b).mp hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · rfl
      · exact hkey2
      · exact hkey2.symm
      · rfl
    obtain ⟨N, es, hN0, hesper, hesmem, hesuniq, hesshare⟩ :=
      exists_boundary_side_cycle hΓ hfree hε hgap hdense
    obtain ⟨r0, hr0v, hr0e, -⟩ := hesshare 0
    have hchain : ∀ k, ∀ u : UpperHalfPlane, IsSegEndpoint (es k) u →
        m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
        = m (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀) := by
      intro k
      induction k with
      | zero =>
        intro u hu
        exact hsideRel (es 0) (hesmem 0) u r0 hu hr0e
      | succ k ih =>
        intro u hu
        obtain ⟨w, hwv, hwk, hwk1⟩ := hesshare k
        exact (hsideRel (es (k + 1)) (hesmem (k + 1)) u w hu hwk1).trans (ih w hwk)
    have hval : ∀ D ∈ polygonVertexClasses Γ τ₀, m D * ςf D
        = m (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀) := by
      intro D hD
      obtain ⟨s₁, hs₁, s₂, hs₂, -, he₁, -, -⟩ :=
        exists_two_sides_at_vertex hΓ hfree hε hgap hdense (hvC1 D hD)
      obtain ⟨k, ⟨hkN, hks⟩, -⟩ := hesuniq s₁ hs₁
      have h1 : IsSegEndpoint (es k) (vC D) := by
        rw [hks]
        exact he₁
      have h2 := hchain k (vC D) h1
      rw [← hvC2 D hD] at h2
      exact h2
    rw [hval C hC, hval C' hC']

/-- A proper subspace of a finite-dimensional space is annihilated by a nonzero
functional. -/
theorem exists_ann_functional {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {U : Submodule ℝ W} (hU : U ≠ ⊤) :
    ∃ h : W →ₗ[ℝ] ℝ, h ≠ 0 ∧ ∀ u ∈ U, h u = 0 := by
  haveI : Nontrivial (W ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hU
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : W ⧸ U)
  set b := Module.finBasis ℝ (W ⧸ U) with hbdef
  have hrep : b.repr q₀ ≠ 0 := fun h => hq₀ (by
    have h2 := b.repr.map_eq_zero_iff.mp h
    exact h2)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrep
  refine ⟨(b.coord i).comp U.mkQ, ?_, ?_⟩
  · intro h
    obtain ⟨w, hw⟩ := U.mkQ_surjective q₀
    have h3 := congrFun (congrArg DFunLike.coe h) w
    rw [LinearMap.comp_apply, hw] at h3
    rw [Module.Basis.coord_apply] at h3
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    exact hi h3
  · intro u hu
    rw [LinearMap.comp_apply, show U.mkQ u = 0 from (Submodule.Quotient.mk_eq_zero U).mpr hu,
      map_zero]

/-- **The cycle-constrained side functions form a finite-dimensional space.** For a
Fuchsian group in which every element with a fixed point acts trivially, with a
translation-length gap and an `R`-dense orbit, the polygon has finitely many side pairs;
the odd side functions are then finite-dimensional and these form a subspace of them. -/
theorem finiteDimensional_cycleConstrained (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (cycleConstrained Γ τ₀) := by
  haveI := finiteDimensional_oddSideFunctions hΓ hfree hε hgap hdense
  exact Submodule.finiteDimensional_of_le (fun α hα => hα.1)

/-- **Dimension of the constrained space**: the vertex-loop constraints impose one linear
condition per vertex class with exactly one linear dependency among them — traversing every
vertex loop counterclockwise, each side pair is crossed once in each direction, so the
signed sum of all class constraints is zero; conversely the class-adjacency graph is
connected through the boundary cycle, so the corank is exactly one. Hence
`dim = m - (c - 1)`, in addition form. -/
theorem finrank_cycleConstrained_add_classCount (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Module.finrank ℝ (cycleConstrained Γ τ₀) + polygonVertexClassCount Γ τ₀
      = polygonSideCount Γ τ₀ + 1 := by
  classical
  haveI hFD := finiteDimensional_oddSideFunctions hΓ hfree hε hgap hdense
  have hVfin := finite_polygonVertices hΓ hfree hε hgap hdense
  have hclassfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine (hVfin.image (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  haveI := hclassfin.fintype
  obtain ⟨Φ, εs, hεpm, hadd, hsmul, hP1, hP2, hP3, hP5⟩ :=
    exists_constraint_data hΓ hfree hε hgap hdense
  set Ψ : ↥(oddSideFunctions Γ τ₀) →ₗ[ℝ] (↥(polygonVertexClasses Γ τ₀) → ℝ) :=
    { toFun := fun α C => Φ ↑C ↑α
      map_add' := fun α β => funext fun C => hadd ↑C C.2 ↑α ↑β
      map_smul' := fun c α => funext fun C => hsmul ↑C C.2 c ↑α } with hΨdef
  have hΨval : ∀ (α : ↥(oddSideFunctions Γ τ₀)) (C : ↥(polygonVertexClasses Γ τ₀)),
      Ψ α C = Φ ↑C ↑α := fun α C => rfl
  have hle : cycleConstrained Γ τ₀ ≤ oddSideFunctions Γ τ₀ := fun α hα => hα.1
  have hker : Submodule.comap (oddSideFunctions Γ τ₀).subtype (cycleConstrained Γ τ₀)
      = LinearMap.ker Ψ := by
    ext α
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    constructor
    · intro hmem
      funext C
      exact hP1 ↑α hmem ↑C C.2
    · intro h0
      exact hP2 ↑α α.2 fun C hC => congrFun h0 ⟨C, hC⟩
  have hfr1 : Module.finrank ℝ (cycleConstrained Γ τ₀)
      = Module.finrank ℝ (LinearMap.ker Ψ) := by
    rw [← hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  obtain ⟨sing, hsing⟩ : ∃ sing : ↥(polygonVertexClasses Γ τ₀) →
      (↥(polygonVertexClasses Γ τ₀) → ℝ),
      sing = fun i j => if i = j then 1 else 0 := ⟨_, rfl⟩
  set lam : (↥(polygonVertexClasses Γ τ₀) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ C : ↥(polygonVertexClasses Γ τ₀), εs ↑C * f C
      map_add' := fun f g => by
        simp only [Pi.add_apply, mul_add]
        exact Finset.sum_add_distrib
      map_smul' := fun c f => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C _ => by ring } with hlamdef
  have hlamval : ∀ f, lam f = ∑ C : ↥(polygonVertexClasses Γ τ₀), εs ↑C * f C :=
    fun f => rfl
  have hsingval : ∀ i : ↥(polygonVertexClasses Γ τ₀), lam (sing i) = εs ↑i := by
    intro i
    rw [hlamval]
    rw [Finset.sum_eq_single i]
    · rw [hsing]
      simp
    · intro b _ hb
      rw [hsing]
      simp only [if_neg (fun h : i = b => hb h.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hΨsum : ∀ α : ↥(oddSideFunctions Γ τ₀), lam (Ψ α) = 0 := by
    intro α
    have h3 := hP3 ↑α α.2
    rw [finsum_mem_eq_finite_toFinset_sum _ hclassfin] at h3
    have h4 : ∑ i ∈ hclassfin.toFinset, εs i * Φ i ↑α
        = ∑ C : ↥(polygonVertexClasses Γ τ₀), εs ↑C * Φ ↑C ↑α :=
      Finset.sum_subtype hclassfin.toFinset (fun x => hclassfin.mem_toFinset)
        (fun C => εs C * Φ C ↑α)
    rw [h4] at h3
    exact h3
  have hrange : LinearMap.range Ψ ≤ LinearMap.ker lam := by
    rintro f ⟨α, rfl⟩
    exact hΨsum α
  have hCne : ∃ C, C ∈ polygonVertexClasses Γ τ₀ := by
    obtain ⟨N, es, hN0, -, -, -, hesshare⟩ :=
      exists_boundary_side_cycle hΓ hfree hε hgap hdense
    obtain ⟨v, hv, -, -⟩ := hesshare 0
    exact ⟨_, ⟨v, hv, rfl⟩⟩
  obtain ⟨C₀, hC₀⟩ := hCne
  have hεC₀ : εs C₀ ≠ 0 := by
    rcases hεpm C₀ hC₀ with h | h <;> rw [h] <;> norm_num
  have hlamne : lam ≠ 0 := by
    intro h
    have h2 := congrFun (congrArg DFunLike.coe h) (sing ⟨C₀, hC₀⟩)
    rw [hsingval ⟨C₀, hC₀⟩] at h2
    exact hεC₀ h2
  have hlam_rn := LinearMap.finrank_range_add_finrank_ker lam
  have hlamrange : LinearMap.range lam = ⊤ := by
    obtain ⟨f, hf⟩ : ∃ f, lam f ≠ 0 := by
      by_contra h
      push Not at h
      exact hlamne (LinearMap.ext fun f => h f)
    rw [LinearMap.range_eq_top]
    intro r
    refine ⟨(r / lam f) • f, ?_⟩
    rw [map_smul, smul_eq_mul]
    field_simp
  rw [hlamrange, finrank_top, Module.finrank_self] at hlam_rn
  have hcard : Module.finrank ℝ ((↥(polygonVertexClasses Γ τ₀)) → ℝ)
      = polygonVertexClassCount Γ τ₀ := by
    rw [Module.finrank_fintype_fun_eq_card]
    change Fintype.card _ = (polygonVertexClasses Γ τ₀).ncard
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hupper : Module.finrank ℝ (LinearMap.range Ψ)
      ≤ Module.finrank ℝ (LinearMap.ker lam) := Submodule.finrank_mono hrange
  have hlower : Module.finrank ℝ (LinearMap.ker lam)
      ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    by_contra hlt
    push Not at hlt
    have hw0ne : sing ⟨C₀, hC₀⟩ ≠ 0 := by
      intro h
      have h2 := congrFun h ⟨C₀, hC₀⟩
      rw [hsing] at h2
      simp at h2
    have hspan1 : Module.finrank ℝ (ℝ ∙ sing ⟨C₀, hC₀⟩) = 1 := finrank_span_singleton hw0ne
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Ψ)
      (ℝ ∙ sing ⟨C₀, hC₀⟩)
    have hU'' : LinearMap.range Ψ ⊔ (ℝ ∙ sing ⟨C₀, hC₀⟩) ≠ ⊤ := by
      intro htop
      have h4 : Module.finrank ℝ ((↥(polygonVertexClasses Γ τ₀)) → ℝ)
          = Module.finrank ℝ ↥(LinearMap.range Ψ ⊔ (ℝ ∙ sing ⟨C₀, hC₀⟩)) := by
        rw [htop, finrank_top]
      omega
    obtain ⟨h, hne0, hann⟩ := exists_ann_functional hU''
    have hcoef : ∀ f : ↥(polygonVertexClasses Γ τ₀) → ℝ,
        h f = ∑ C : ↥(polygonVertexClasses Γ τ₀), f C * h (sing C) := by
      intro f
      conv_lhs => rw [pi_eq_sum_univ f]
      rw [map_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [map_smul, smul_eq_mul, hsing]
    obtain ⟨mfun, hmfun⟩ : ∃ mfun : Set UpperHalfPlane → ℝ,
        mfun = fun C => if hC : C ∈ polygonVertexClasses Γ τ₀
          then h (sing ⟨C, hC⟩) else 0 := ⟨_, rfl⟩
    have hmval : ∀ C : ↥(polygonVertexClasses Γ τ₀), mfun ↑C = h (sing C) := by
      intro C
      rw [hmfun]
      simp only
      rw [dif_pos C.2]
    have hmhyp : ∀ α ∈ oddSideFunctions Γ τ₀,
        ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, mfun C * Φ C α = 0 := by
      intro α hα
      rw [finsum_mem_eq_finite_toFinset_sum _ hclassfin]
      have h4 : ∑ i ∈ hclassfin.toFinset, mfun i * Φ i α
          = ∑ C : ↥(polygonVertexClasses Γ τ₀), mfun ↑C * Φ ↑C α :=
        Finset.sum_subtype hclassfin.toFinset (fun x => hclassfin.mem_toFinset)
          (fun C => mfun C * Φ C α)
      rw [h4]
      have h5 : ∑ C : ↥(polygonVertexClasses Γ τ₀), mfun ↑C * Φ ↑C α
          = h (Ψ ⟨α, hα⟩) := by
        rw [hcoef]
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [hmval C]
        exact mul_comm _ _
      rw [h5]
      exact hann _ (Submodule.mem_sup_left (LinearMap.mem_range_self Ψ ⟨α, hα⟩))
    have hP5app := hP5 mfun hmhyp
    have hcoords : ∀ C : ↥(polygonVertexClasses Γ τ₀),
        h (sing C) = mfun C₀ * εs C₀ * εs ↑C := by
      intro C
      have h1 := hP5app ↑C C.2 C₀ hC₀
      rw [← hmval C]
      rcases hεpm ↑C C.2 with h2 | h2 <;> rw [h2] at h1 ⊢ <;> linarith
    have ht0 : mfun C₀ * εs C₀ = 0 := by
      have h1 := hcoords ⟨C₀, hC₀⟩
      have h2 : h (sing ⟨C₀, hC₀⟩) = 0 :=
        hann _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      rw [h2] at h1
      rcases hεpm C₀ hC₀ with h3 | h3 <;> rw [h3] at h1 ⊢ <;> linarith
    refine hne0 (LinearMap.ext fun f => ?_)
    rw [hcoef f]
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [hcoords C, ht0]
    ring
  have hfr_range : Module.finrank ℝ (LinearMap.range Ψ)
      = Module.finrank ℝ (LinearMap.ker lam) := le_antisymm hupper hlower
  have hm := finrank_oddSideFunctions hΓ hfree hε hgap hdense
  rw [hm] at hrn
  rw [hcard] at hlam_rn
  rw [hfr1]
  omega


/-- A trivially-acting element of a subgroup of `SL(2, ℝ)` squares to the identity: it is
`±1` as a matrix. -/
theorem sq_eq_one_of_smul_id {δ : ↥Γ} (h : ∀ τ : UpperHalfPlane, δ • τ = τ) :
    δ * δ = 1 := by
  have h' : ∀ τ : UpperHalfPlane, (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := by
    intro τ
    rw [← Subgroup.smul_def]
    exact h τ
  have hsq : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      * ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rcases (smul_id_iff_pm_one _).mp h' with h1 | h1 <;> rw [h1]
    · rw [one_mul]
    · rw [neg_mul_neg, one_mul]
  have hSL : (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 := by
    have hmat : (((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
        = ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact hsq
    exact Subtype.coe_injective hmat
  have hval : ((δ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      = ((1 : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
    rw [Subgroup.coe_mul, OneMemClass.coe_one]
    exact hSL
  exact Subtype.coe_injective hval

/-- An additive character is odd. -/
theorem hom_apply_inv {G : Type*} [Group G] (f : homSubmodule G) (g : G) :
    (f : G → ℝ) g⁻¹ = -(f : G → ℝ) g := by
  have h := f.2 g⁻¹ g
  rw [inv_mul_cancel, homSubmodule_apply_one f] at h
  linarith

/-- Restriction to side values is the indicator of the side elements. -/
theorem restrictSides_apply (f : homSubmodule (↥Γ)) :
    restrictSides Γ τ₀ f
      = {γ : ↥Γ | IsSideElement Γ τ₀ γ}.indicator (f : (↥Γ) → ℝ) := rfl

/-- The side values of an additive character are cycle-constrained: they are odd and
fiber-constant since characters kill torsion, and the crossing sum along a vertex loop
telescopes to the value of the character at a trivially-acting element. -/
theorem restrictSides_mem_cycleConstrained (_hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (f : homSubmodule (↥Γ)) :
    restrictSides Γ τ₀ f ∈ cycleConstrained Γ τ₀ := by
  rw [restrictSides_apply]
  set S : Set ↥Γ := {γ : ↥Γ | IsSideElement Γ τ₀ γ} with hS
  refine ⟨⟨fun γ hγ => ?_, fun γ => ?_, fun γ δ h => ?_⟩, fun v hv p hp => ?_⟩
  · exact Set.indicator_of_notMem (show γ ∉ S from hγ) _
  · by_cases hγ : IsSideElement Γ τ₀ γ
    · rw [Set.indicator_of_mem (show γ⁻¹ ∈ S from hγ.inv),
        Set.indicator_of_mem (show γ ∈ S from hγ)]
      exact hom_apply_inv f γ
    · have hγi : ¬IsSideElement Γ τ₀ γ⁻¹ := fun hi => hγ (by simpa using hi.inv)
      rw [Set.indicator_of_notMem (show γ⁻¹ ∉ S from hγi),
        Set.indicator_of_notMem (show γ ∉ S from hγ)]
      ring
  · by_cases hγ : IsSideElement Γ τ₀ γ
    · have hδ : IsSideElement Γ τ₀ δ := (isSideElement_congr h).mp hγ
      rw [Set.indicator_of_mem (show γ ∈ S from hγ), Set.indicator_of_mem (show δ ∈ S from hδ)]
      have ht : (δ⁻¹ * γ) • τ₀ = τ₀ := by rw [mul_smul, h, inv_smul_smul]
      have htriv := hfree (δ⁻¹ * γ) ⟨τ₀, ht⟩
      have h0 := homSubmodule_apply_eq_zero_of_sq f (sq_eq_one_of_smul_id htriv)
      have h2 := f.2 δ (δ⁻¹ * γ)
      rw [show δ * (δ⁻¹ * γ) = γ by group] at h2
      linarith
    · have hδ : ¬IsSideElement Γ τ₀ δ := fun hd => hγ ((isSideElement_congr h).mpr hd)
      rw [Set.indicator_of_notMem (show γ ∉ S from hγ),
        Set.indicator_of_notMem (show δ ∉ S from hδ)]
  · obtain ⟨htile, hmem, hclose⟩ := hp
    cases p with
    | nil => exact crossingSum_nil _
    | cons x l =>
      have hhead : (x :: l).head? = some x := rfl
      have hlast : (x :: l).getLast? = some x := by rw [← hclose]; exact hhead
      have hrel : ∀ u ∈ (x :: l), ∀ w ∈ (x :: l), IsSideElement Γ τ₀ (u⁻¹ * w) →
          S.indicator (f : (↥Γ) → ℝ) (u⁻¹ * w)
            = (f : (↥Γ) → ℝ) w - (f : (↥Γ) → ℝ) u := by
        intro u _ w _ hside
        rw [Set.indicator_of_mem (show u⁻¹ * w ∈ S from hside)]
        have h2 := f.2 u⁻¹ w
        rw [hom_apply_inv f u] at h2
        linarith
      rw [crossingSum_telescope (S.indicator (f : (↥Γ) → ℝ)) (f : (↥Γ) → ℝ)
        (x :: l) htile hrel hhead hlast]
      ring

/-- A character with vanishing side values vanishes: the side elements and the
trivially-acting elements generate the group, and the character kills both kinds of
generators. -/
theorem restrictSides_eq_zero_imp (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {F : homSubmodule (↥Γ)} (hF : restrictSides Γ τ₀ F = 0) : F = 0 := by
  have hside : ∀ γ : ↥Γ, IsSideElement Γ τ₀ γ → (F : (↥Γ) → ℝ) γ = 0 := by
    intro γ hγ
    have h1 := congrFun hF γ
    rw [restrictSides_apply,
      Set.indicator_of_mem (show γ ∈ {γ : ↥Γ | IsSideElement Γ τ₀ γ} from hγ)] at h1
    simpa using h1
  set K : Subgroup ↥Γ :=
    { carrier := {γ : ↥Γ | (F : (↥Γ) → ℝ) γ = 0}
      one_mem' := homSubmodule_apply_one F
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [F.2 a b, ha, hb, add_zero]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [hom_apply_inv F a, ha, neg_zero] } with hK
  have htop : Subgroup.closure ({δ : ↥Γ | IsSideElement Γ τ₀ δ} ∪
      {δ : ↥Γ | ∀ τ : UpperHalfPlane, δ • τ = τ}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro γ (hγ | hγ)
    · exact hside γ hγ
    · exact homSubmodule_apply_eq_zero_of_sq F (sq_eq_one_of_smul_id hγ)
  rw [closure_sideElements_eq_top hΓ hfree hε hgap hdense] at htop
  apply Subtype.ext
  funext γ
  have hγK : γ ∈ K := htop (Subgroup.mem_top γ)
  simpa using hγK

/-- Restriction to side values is injective: the side elements generate the group modulo
trivially-acting elements, on which every character vanishes. -/
theorem restrictSides_injective (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Function.Injective (restrictSides Γ τ₀) := by
  intro f g h
  have hz : restrictSides Γ τ₀ (f - g) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (restrictSides_eq_zero_imp hΓ hfree hε hgap hdense hz)

/-- The characters form a finite-dimensional space: restriction to side values embeds them
into the odd side functions. -/
theorem finiteDimensional_homSubmodule (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (homSubmodule (↥Γ)) := by
  haveI := finiteDimensional_cycleConstrained hΓ hfree hε hgap hdense
  set φ : homSubmodule (↥Γ) →ₗ[ℝ] cycleConstrained Γ τ₀ :=
    LinearMap.codRestrict (cycleConstrained Γ τ₀) (restrictSides Γ τ₀)
      (fun f => restrictSides_mem_cycleConstrained hΓ hfree hε hgap hdense f) with hφ
  have hinj : Function.Injective φ := by
    intro f g h
    apply restrictSides_injective hΓ hfree hε hgap hdense
    exact congrArg Subtype.val h
  exact FiniteDimensional.of_injective φ hinj

/-- **The rank identity**: the dimension `Q` of the character space satisfies
`Q + c = m + 1`. Restriction to side values and integration along tile paths are mutually
inverse linear embeddings between the characters and the cycle-constrained side
functions. -/
theorem finrank_homSubmodule_add_classCount (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Module.finrank ℝ (homSubmodule (↥Γ)) + polygonVertexClassCount Γ τ₀
      = polygonSideCount Γ τ₀ + 1 := by
  classical
  haveI := finiteDimensional_cycleConstrained hΓ hfree hε hgap hdense
  obtain ⟨Φ, hΦ⟩ := exists_crossingSum_hom hΓ hfree hε hgap hdense
  set φ : homSubmodule (↥Γ) →ₗ[ℝ] cycleConstrained Γ τ₀ :=
    LinearMap.codRestrict (cycleConstrained Γ τ₀) (restrictSides Γ τ₀)
      (fun f => restrictSides_mem_cycleConstrained hΓ hfree hε hgap hdense f) with hφ
  have hinj : Function.Injective φ := by
    intro f g h
    apply restrictSides_injective hΓ hfree hε hgap hdense
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective φ := by
    intro β
    refine ⟨Φ β, ?_⟩
    apply Subtype.ext
    change restrictSides Γ τ₀ (Φ β) = (β : (↥Γ) → ℝ)
    funext γ
    rw [restrictSides_apply]
    by_cases hγ : IsSideElement Γ τ₀ γ
    · rw [Set.indicator_of_mem (show γ ∈ {γ : ↥Γ | IsSideElement Γ τ₀ γ} from hγ)]
      exact hΦ β γ hγ
    · rw [Set.indicator_of_notMem (show γ ∉ {γ : ↥Γ | IsSideElement Γ τ₀ γ} from hγ)]
      obtain ⟨⟨hz, -, -⟩, -⟩ := mem_cycleConstrained.mp β.2
      exact (hz γ hγ).symm
  have e : (homSubmodule (↥Γ)) ≃ₗ[ℝ] (cycleConstrained Γ τ₀) :=
    LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  rw [e.finrank_eq]
  exact finrank_cycleConstrained_add_classCount hΓ hfree hε hgap hdense

end RiemannDynamics
