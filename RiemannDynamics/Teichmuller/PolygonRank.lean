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

/-- The odd side functions form a finite-dimensional space: they embed into the functions
on the finite side set. -/
theorem finiteDimensional_oddSideFunctions (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (oddSideFunctions Γ τ₀) := by
  sorry

/-- The dimension of the odd side functions is the number `m` of side pairs: one degree of
freedom per pair, the two members of a pair carrying opposite values. -/
theorem finrank_oddSideFunctions (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Module.finrank ℝ (oddSideFunctions Γ τ₀) = polygonSideCount Γ τ₀ := by
  sorry

/-! ## Generation by side elements -/

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
  sorry

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
  sorry

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

end RiemannDynamics
