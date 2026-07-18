import RiemannDynamics.Teichmuller.Polygon

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

theorem mem_oddSideFunctions {α : (↥Γ) → ℝ} :
    α ∈ oddSideFunctions Γ τ₀ ↔ (∀ γ : ↥Γ, ¬IsSideElement Γ τ₀ γ → α γ = 0) ∧
      (∀ γ : ↥Γ, α γ⁻¹ = -α γ) ∧ ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ :=
  Iff.rfl

/-! ## Generation by side elements -/

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

theorem crossingSum_zero (p : List ↥Γ) : crossingSum (0 : (↥Γ) → ℝ) p = 0 := by
  unfold crossingSum
  induction p.zip p.tail with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp

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

theorem mem_cycleConstrained {α : (↥Γ) → ℝ} :
    α ∈ cycleConstrained Γ τ₀ ↔ α ∈ oddSideFunctions Γ τ₀ ∧
      ∀ v ∈ polygonVertices Γ τ₀, ∀ p : List ↥Γ,
        IsVertexLoop Γ τ₀ v p → crossingSum α p = 0 :=
  Iff.rfl

theorem finiteDimensional_cycleConstrained (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (cycleConstrained Γ τ₀) := by
  sorry

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
  sorry

/-! ## Path reachability and path independence -/

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
  sorry

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
  sorry

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

/-- The side values of an additive character are cycle-constrained: they are odd and
fiber-constant since characters kill torsion, and the crossing sum along a vertex loop
telescopes to the value of the character at a trivially-acting element. -/
theorem restrictSides_mem_cycleConstrained (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (f : homSubmodule (↥Γ)) :
    restrictSides Γ τ₀ f ∈ cycleConstrained Γ τ₀ := by
  sorry

/-- Restriction to side values is injective: the side elements generate the group modulo
trivially-acting elements, on which every character vanishes. -/
theorem restrictSides_injective (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Function.Injective (restrictSides Γ τ₀) := by
  sorry

/-! ## The rank identity -/

/-- The characters form a finite-dimensional space: restriction to side values embeds them
into the odd side functions. -/
theorem finiteDimensional_homSubmodule (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (homSubmodule (↥Γ)) := by
  sorry

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
  sorry


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

/-- The side pairs form a finite set: each is a doubleton of sides. -/
theorem finite_polygonSidePairs (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSidePairs Γ τ₀).Finite := by
  have hfin := finite_polygonSides hΓ hfree hε hgap hdense
  refine ((hfin.prod hfin).image fun q : Set UpperHalfPlane × Set UpperHalfPlane =>
    ({q.1, q.2} : Set (Set UpperHalfPlane))).subset ?_
  rintro P ⟨γ, hγ, rfl⟩
  exact ⟨(dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹),
    Set.mem_prod.mpr ⟨⟨γ, hγ, rfl⟩, ⟨γ⁻¹, hγ.inv, rfl⟩⟩, rfl⟩

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
    show (∑ P : ↥(polygonSidePairs Γ τ₀), w P • elemSide Γ τ₀ (g P)) (g P') = w P'
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
    show (∑ P : ↥(polygonSidePairs Γ τ₀),
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
  show dist z (η • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀)
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

end RiemannDynamics
