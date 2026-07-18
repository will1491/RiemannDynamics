import RiemannDynamics.Teichmuller.Dirichlet
import RiemannDynamics.Hyperbolic.TriangleArea
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Dirichlet polygon: sides, vertices, fan, and the combinatorial Gauss–Bonnet formula

For a Fuchsian group with a translation-length gap and a dense orbit, the Dirichlet domain
is a compact geodesically convex polygon: its frontier is a finite union of geodesic
segments (the sides), the sides meet at the vertices, and the tiles containing a vertex form
a finite cyclic fan. The polygon is the union of the geodesic cones from the basepoint over
its sides; each cone is a geodesic triangle, and the angle-deficit formula for triangles
yields the quantized area
`volume (dirichletDomain Γ τ₀) = 2π (m - 1 - c)`, where `m` is the number of side pairs and
`c` the number of vertex orbit classes: the apex angles at the basepoint sum to `2π`, and
the interior angles along each vertex orbit class sum to `2π` through the bijection between
the tiles at a vertex and the class vertices of the polygon.

* `IsSideElement`, `polygonSides`, `polygonSidePairs`, `polygonSideCount` — the sides, their
  pairing `γ ↔ γ⁻¹`, and the pair count `m`.
* `tileCenters`, `polygonVertices`, `polygonVertexClasses`, `polygonVertexClassCount` — the
  vertices (points lying in at least three tiles) and the class count `c`.
* `geodConvex_dirichletDomain` — the Dirichlet domain is geodesically convex.
* `dirichletDomain_eq_biUnion_geodCone` — the fan decomposition over the sides.
* `exists_vertex_cycle`, `exists_vertex_star_bijection` — the cyclic fan of tiles at a
  vertex and the developed bijection onto the class vertices.
* `sum_interiorAngle_vertexClass`, `sum_apexAngle_basepoint` — the `2π` angle sums.
* `volume_dirichletDomain_gaussBonnet` — the quantized area formula.
-/

open MeasureTheory
open scoped ENNReal MatrixGroups

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## Sides and side pairs -/

/-- A **side element**: a group element moving the basepoint whose equidistance set meets
the Dirichlet domain in more than one point. -/
def IsSideElement (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (γ : ↥Γ) : Prop :=
  γ • τ₀ ≠ τ₀ ∧ (dirichletSideSet Γ τ₀ γ).Nontrivial

/-- The **sides** of the Dirichlet polygon: the nondegenerate side sets, as a set of subsets
of the upper half plane, so that elements differing by the stabilizer of the basepoint give
the same side. -/
def polygonSides (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Set (Set UpperHalfPlane) :=
  {s | ∃ γ : ↥Γ, IsSideElement Γ τ₀ γ ∧ s = dirichletSideSet Γ τ₀ γ}

/-- The **side pairs** of the Dirichlet polygon: the unordered pairs `{S_γ, S_{γ⁻¹}}` of a
side and its partner under the side pairing. -/
def polygonSidePairs (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Set (Set (Set UpperHalfPlane)) :=
  {P | ∃ γ : ↥Γ, IsSideElement Γ τ₀ γ ∧
    P = {dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹}}

/-- The number `m` of side pairs of the Dirichlet polygon. -/
noncomputable def polygonSideCount (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : ℕ :=
  (polygonSidePairs Γ τ₀).ncard

/-- Side elements are closed under inversion: the side pairing carries the side of `γ`
bijectively onto the side of `γ⁻¹`. -/
theorem IsSideElement.inv {γ : ↥Γ} (h : IsSideElement Γ τ₀ γ) : IsSideElement Γ τ₀ γ⁻¹ := by
  obtain ⟨hmove, x, hx, y, hy, hxy⟩ := h
  refine ⟨fun hfix => hmove ?_, γ⁻¹ • x, smul_mem_dirichletSideSet_inv hx,
    γ⁻¹ • y, smul_mem_dirichletSideSet_inv hy,
    fun hcon => hxy ((smul_left_cancel_iff γ⁻¹).mp hcon)⟩
  conv_lhs => rw [← hfix]
  rw [smul_inv_smul]

/-! ## Vertices and vertex classes -/

/-- The **tile centers** at a point: the orbit points of the basepoint realized by the
contact elements of the point, one for each tile containing it. -/
def tileCenters (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ z : UpperHalfPlane) : Set UpperHalfPlane :=
  (fun γ : ↥Γ => γ • τ₀) '' contactSet Γ τ₀ z

/-- The **vertices** of the Dirichlet polygon: the points of the domain lying in at least
three tiles. -/
def polygonVertices (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Set UpperHalfPlane :=
  {z ∈ dirichletDomain Γ τ₀ | 3 ≤ (tileCenters Γ τ₀ z).ncard}

/-- The **vertex classes**: the traces on the vertex set of the `Γ`-orbits of vertices. -/
def polygonVertexClasses (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Set (Set UpperHalfPlane) :=
  {C | ∃ v ∈ polygonVertices Γ τ₀, C = MulAction.orbit Γ v ∩ polygonVertices Γ τ₀}

/-- The number `c` of vertex orbit classes of the Dirichlet polygon. -/
noncomputable def polygonVertexClassCount (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : ℕ :=
  (polygonVertexClasses Γ τ₀).ncard

/-! ## Convexity of the Dirichlet domain -/

/-- The Dirichlet domain is geodesically convex: it is an intersection of half-spaces of
distance comparisons. -/
theorem geodConvex_dirichletDomain : GeodConvex (dirichletDomain Γ τ₀) := by
  intro a ha b hb z hz γ
  exact geodSeg_subset_setOf_dist_le (ha γ) (hb γ) hz

/-! ## The structure of sides and vertices -/

/-! ## The side pairing is a fixed-point-free involution -/

/-- No side is paired with itself: a self-paired side forces `γ² • τ₀ = τ₀`, so `γ²` acts
trivially, and `γ² = 1` gives `γ = ±1` while `γ² = -1` gives a zero trace, an elliptic
element with a fixed point — both excluded. -/
theorem dirichletSideSet_inv_ne (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {γ : ↥Γ} (h : IsSideElement Γ τ₀ γ) :
    dirichletSideSet Γ τ₀ γ⁻¹ ≠ dirichletSideSet Γ τ₀ γ := by
  sorry

/-- The polygon has `2m` sides: the fixed-point-free pairing matches the sides in `m`
two-element pairs. -/
theorem ncard_polygonSides (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSides Γ τ₀).ncard = 2 * polygonSideCount Γ τ₀ := by
  sorry

/-- The polygon has at least one side pair: the orbit of the basepoint is dense, so the
group acts nontrivially and the domain is a proper subset of the plane. -/
theorem polygonSideCount_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    0 < polygonSideCount Γ τ₀ := by
  sorry

/-- The polygon has at least one vertex class: the compact domain has a frontier, the
frontier is a union of segments, and segments have endpoints. -/
theorem polygonVertexClassCount_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    0 < polygonVertexClassCount Γ τ₀ := by
  sorry

/-! ## The fan decomposition -/

/-! ## The vertex star -/

/-! ## Angle sums -/

/-- `θ` is the **interior angle** of the Dirichlet polygon at `v`: the sector angle at `v`
between the two sides meeting there, measured toward any of their points other than `v`. -/
def IsInteriorAngleAt (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (v : UpperHalfPlane) (θ : ℝ) : Prop :=
  ∃ s₁ ∈ polygonSides Γ τ₀, ∃ s₂ ∈ polygonSides Γ τ₀, s₁ ≠ s₂ ∧
    IsSegEndpoint s₁ v ∧ IsSegEndpoint s₂ v ∧
    ∃ w₁ ∈ s₁, ∃ w₂ ∈ s₂, w₁ ≠ v ∧ w₂ ≠ v ∧ θ = sectorAngle v w₁ w₂

/-- **Angle sum over a vertex class**: the interior angles of the polygon at the vertices of
one orbit class sum to `2π` — the sectors of the tiles at any vertex of the class partition
a disk about it, and the developed bijection carries them isometrically onto the class
angles. -/
theorem sum_interiorAngle_vertexClass (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) {α : UpperHalfPlane → ℝ}
    (hα : ∀ v' ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀,
      IsInteriorAngleAt Γ τ₀ v' (α v')) :
    ∑ᶠ v' ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀, α v' = 2 * Real.pi := by
  sorry

/-- **Total angle sum**: the interior angles over all vertices of the polygon sum to
`2π c`. -/
theorem sum_interiorAngle_total (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : UpperHalfPlane → ℝ}
    (hα : ∀ v ∈ polygonVertices Γ τ₀, IsInteriorAngleAt Γ τ₀ v (α v)) :
    ∑ᶠ v ∈ polygonVertices Γ τ₀, α v
      = 2 * Real.pi * (polygonVertexClassCount Γ τ₀ : ℝ) := by
  sorry

/-- **Apex angle sum**: the apex angles at the basepoint of the cones of the fan sum to
`2π` — the cones partition a disk about the interior basepoint. -/
theorem sum_apexAngle_basepoint (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {β : Set UpperHalfPlane → ℝ}
    (hβ : ∀ s ∈ polygonSides Γ τ₀, IsApexAngleAt τ₀ s (β s)) :
    ∑ᶠ s ∈ polygonSides Γ τ₀, β s = 2 * Real.pi := by
  sorry

/-! ## The combinatorial Gauss–Bonnet formula -/

/-- **Polygon Gauss–Bonnet**: the hyperbolic area of the Dirichlet polygon is
`2π (m - 1 - c)`, where `m` is the number of side pairs and `c` the number of vertex orbit
classes. Summing the angle-deficit areas of the `2m` cones of the fan: the `π`'s contribute
`2πm`, the apex angles contribute `-2π`, and the base angles reassemble along the vertices
into the interior angles, contributing `-2πc`. -/
theorem volume_dirichletDomain_gaussBonnet (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    volume (dirichletDomain Γ τ₀) = ENNReal.ofReal
      (2 * Real.pi * ((polygonSideCount Γ τ₀ : ℝ) - 1 - (polygonVertexClassCount Γ τ₀ : ℝ))) := by
  sorry

/-- **Quantization**: the area of the Dirichlet polygon is a positive integer multiple of
`2π`. -/
theorem volume_dirichletDomain_quantized (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ k : ℕ, 1 ≤ k ∧
      volume (dirichletDomain Γ τ₀) = ENNReal.ofReal (2 * Real.pi * (k : ℝ)) := by
  sorry


variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## Connectivity of a punctured disc -/

/-- A point is off a segment when no convex combination of the endpoint offsets vanishes. -/
theorem notMem_segment {p x y : ℂ}
    (h : ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
      (α : ℂ) * (x - p) + (β : ℂ) * (y - p) ≠ 0) :
    p ∉ segment ℝ x y := by
  rintro ⟨a, b, ha, hb, hab, hpxy⟩
  refine h a b ha hb hab ?_
  have h2 : ((a : ℂ) * x + (b : ℂ) * y) = p := by
    rw [← hpxy]
    simp [Complex.real_smul]
  have h3 : ((a + b : ℝ) : ℂ) = 1 := by rw [hab]; norm_num
  push_cast at h3
  linear_combination h2 - p * h3

/-- Two points of a ball joined by a segment avoiding a puncture are joined off the
puncture. -/
theorem joinedIn_of_segment_avoid {c : ℂ} {R : ℝ} {p x y : ℂ}
    (hxB : x ∈ Metric.ball c R) (hyB : y ∈ Metric.ball c R) (hp : p ∉ segment ℝ x y) :
    JoinedIn (Metric.ball c R \ {p}) x y :=
  JoinedIn.of_segment_subset fun w hw =>
    ⟨(convex_ball c R).segment_subset hxB hyB hw,
      fun hwp => hp (Set.mem_singleton_iff.mp hwp ▸ hw)⟩

/-- Any two points of a punctured ball are joined inside the punctured ball: when the
straight segment hits the puncture, a perpendicular detour avoids it. -/
theorem joinedIn_ball_diff_singleton {c p x y : ℂ} {R : ℝ}
    (hx : x ∈ Metric.ball c R \ {p}) (hy : y ∈ Metric.ball c R \ {p}) :
    JoinedIn (Metric.ball c R \ {p}) x y := by
  obtain ⟨hxB, hxp⟩ := hx
  obtain ⟨hyB, hyp⟩ := hy
  rw [Set.mem_singleton_iff] at hxp hyp
  by_cases hseg : p ∈ segment ℝ x y
  · obtain ⟨a, b, ha, hb, hab, hpxy⟩ := hseg
    have hpB : p ∈ Metric.ball c R := (convex_ball c R).segment_subset hxB hyB
      ⟨a, b, ha, hb, hab, hpxy⟩
    have hcomb : (a : ℂ) * x + (b : ℂ) * y = p := by
      rw [← hpxy]
      simp [Complex.real_smul]
    have habC : ((a + b : ℝ) : ℂ) = 1 := by rw [hab]; norm_num
    push_cast at habC
    have ha0 : a ≠ 0 := by
      intro h
      rw [h] at hcomb habC
      push_cast at hcomb habC
      rw [zero_add] at habC
      rw [zero_mul, zero_add, habC, one_mul] at hcomb
      exact hyp hcomb
    have hb0 : b ≠ 0 := by
      intro h
      rw [h] at hcomb habC
      push_cast at hcomb habC
      rw [add_zero] at habC
      rw [zero_mul, add_zero, habC, one_mul] at hcomb
      exact hxp hcomb
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hbC : ((b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb0
    set u : ℂ := x - p with hu
    have hune : u ≠ 0 := sub_ne_zero.mpr (fun h => hxp h)
    have huy : (b : ℂ) * (y - p) = -(a : ℂ) * u := by
      rw [hu]
      linear_combination hcomb - p * habC
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hune
    have hRp : 0 < R - dist p c := by
      rw [sub_pos]
      exact Metric.mem_ball.mp hpB
    set t : ℝ := (R - dist p c) / (2 * ‖u‖) with ht
    have htpos : 0 < t := div_pos hRp (by positivity)
    set w : ℂ := p + (t : ℂ) * Complex.I * u with hw
    have hwp : w - p = (t : ℂ) * Complex.I * u := by rw [hw]; ring
    have hwB : w ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      have h1 : dist w c ≤ dist w p + dist p c := dist_triangle _ _ _
      have h2 : dist w p = t * ‖u‖ := by
        rw [dist_eq_norm, hwp, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
      have h3 : t * ‖u‖ = (R - dist p c) / 2 := by
        rw [ht]
        field_simp
      rw [h2, h3] at h1
      linarith
    have hwpne : w ≠ p := by
      intro h
      have h2 : (t : ℂ) * Complex.I * u = 0 := by rw [← hwp, h, sub_self]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · exact htpos.ne' (by exact_mod_cast h4)
        · exact Complex.I_ne_zero h4
      · exact hune h3
    have hp1 : p ∉ segment ℝ x w := by
      refine notMem_segment fun α β hα hβ hαβ hzero => ?_
      rw [hwp, ← hu] at hzero
      have h4 : ((α : ℂ) + (β : ℂ) * ((t : ℂ) * Complex.I)) * u = 0 := by
        linear_combination hzero
      have h5 : (α : ℂ) + (β : ℂ) * ((t : ℂ) * Complex.I) = 0 :=
        (mul_eq_zero.mp h4).resolve_right hune
      have h6 : (α : ℂ) + ((β * t : ℝ) : ℂ) * Complex.I = 0 := by
        rw [← h5]
        push_cast
        ring
      rw [Complex.ext_iff] at h6
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.zero_re,
        Complex.zero_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add,
        zero_sub] at h6
      obtain ⟨h7, h8⟩ := h6
      have hβ0 : β = 0 := by
        rcases mul_eq_zero.mp h8 with h | h
        · exact h
        · exact absurd h htpos.ne'
      rw [h7, hβ0] at hαβ
      norm_num at hαβ
    have hp2 : p ∉ segment ℝ w y := by
      refine notMem_segment fun α β hα hβ hαβ hzero => ?_
      rw [hwp] at hzero
      have h4 : (((b * α * t : ℝ) : ℂ) * Complex.I - ((β * a : ℝ) : ℂ)) * u = 0 := by
        push_cast
        linear_combination (b : ℂ) * hzero - (β : ℂ) * huy
      have h5 : ((b * α * t : ℝ) : ℂ) * Complex.I - ((β * a : ℝ) : ℂ) = 0 :=
        (mul_eq_zero.mp h4).resolve_right hune
      rw [Complex.ext_iff] at h5
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.mul_im,
        Complex.zero_re, Complex.zero_im, mul_zero, mul_one, zero_mul, sub_zero,
        zero_sub, add_zero, zero_add, neg_eq_zero] at h5
      obtain ⟨h7, h8⟩ := h5
      have hβ0 : β = 0 := by
        rcases mul_eq_zero.mp (by linarith [h7] : β * a = 0) with h | h
        · exact h
        · exact absurd h ha0
      have hα0 : α = 0 := by
        rcases mul_eq_zero.mp h8 with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hb0
          · exact h'
        · exact absurd h htpos.ne'
      rw [hα0, hβ0] at hαβ
      norm_num at hαβ
    have hj1 : JoinedIn (Metric.ball c R \ {p}) x w :=
      joinedIn_of_segment_avoid hxB hwB hp1
    have hj2 : JoinedIn (Metric.ball c R \ {p}) w y :=
      joinedIn_of_segment_avoid hwB hyB hp2
    exact hj1.trans hj2
  · exact joinedIn_of_segment_avoid hxB hyB hseg

/-- A punctured ball of the plane is preconnected. -/
theorem isPreconnected_ball_diff_singleton (c p : ℂ) (R : ℝ) :
    IsPreconnected (Metric.ball c R \ {p}) := by
  rcases Set.eq_empty_or_nonempty (Metric.ball c R \ {p}) with h | ⟨x₀, hx₀⟩
  · rw [h]
    exact isPreconnected_empty
  · have hpc : IsPathConnected (Metric.ball c R \ {p}) :=
      ⟨x₀, hx₀, fun _ hy => joinedIn_ball_diff_singleton hx₀ hy⟩
    exact hpc.isConnected.isPreconnected

/-- A punctured hyperbolic ball of the upper half plane is preconnected: its image under
the coordinate embedding is a punctured Euclidean disc. -/
theorem isPreconnected_punctured_ball (z : UpperHalfPlane) (r : ℝ) :
    IsPreconnected (Metric.ball z r \ {z}) := by
  rw [← UpperHalfPlane.isEmbedding_coe.toIsInducing.isPreconnected_image]
  have himg : ((↑) : UpperHalfPlane → ℂ) '' (Metric.ball z r \ {z})
      = Metric.ball ((z.center r : UpperHalfPlane) : ℂ) (z.im * Real.sinh r)
        \ {(z : ℂ)} := by
    rw [Set.image_diff UpperHalfPlane.coe_injective, Set.image_singleton,
      UpperHalfPlane.image_coe_ball]
  rw [himg]
  exact isPreconnected_ball_diff_singleton _ _ _

/-! ## Points of a segment near an endpoint -/

/-- A nondegenerate geodesic segment contains points arbitrarily close to, and distinct
from, its right endpoint. -/
theorem exists_near_on_geodSeg {a v : UpperHalfPlane} (hav : a ≠ v) {r : ℝ}
    (hr : 0 < r) :
    ∃ w ∈ geodSeg a v, w ≠ v ∧ dist w v < r := by
  have hd : 0 < dist a v := dist_pos.mpr hav
  set s : ℝ := min (r / (2 * dist a v)) (1 / 2) with hs
  have hspos : 0 < s := lt_min (by positivity) (by norm_num)
  have hs1 : s ≤ 1 / 2 := min_le_right _ _
  set t : ℝ := 1 - s with htdef
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  refine ⟨geodInterp a v t, geodInterp_mem_geodSeg a v ht, ?_, ?_⟩
  · intro h
    have h1 := dist_geodInterp_right_abs a v t
    rw [h, dist_self] at h1
    have h2 : |1 - t| = s := by
      rw [htdef, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (1 - s))]
      ring_nf
    rw [h2] at h1
    have := mul_pos hspos hd
    linarith
  · have h1 := dist_geodInterp_right_abs a v t
    have h2 : |1 - t| = s := by
      rw [htdef, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (1 - s))]
      ring_nf
    rw [h2] at h1
    have h3 : s * dist a v ≤ (r / (2 * dist a v)) * dist a v :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hd.le
    have h4 : (r / (2 * dist a v)) * dist a v = r / 2 := by
      field_simp
    rw [h1]
    rw [h4] at h3
    linarith

/-! ## Two points determine the mirror across their geodesic -/

/-- The quadratic consequence of equidistance from a point of the imaginary axis. -/
theorem axis_dist_eq {X W T : UpperHalfPlane} (hX : X.re = 0)
    (h : dist X W = dist X T) :
    (Complex.normSq (W : ℂ) + X.im ^ 2) * T.im
      = (Complex.normSq (T : ℂ) + X.im ^ 2) * W.im := by
  have hcosh := congrArg Real.cosh h
  rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hcosh
  have h1 : dist (X : ℂ) (W : ℂ) ^ 2 / (2 * X.im * W.im)
      = dist (X : ℂ) (T : ℂ) ^ 2 / (2 * X.im * T.im) := by
    linarith [hcosh]
  rw [div_eq_div_iff (by positivity) (by positivity)] at h1
  have hdW : dist (X : ℂ) (W : ℂ) ^ 2
      = Complex.normSq (W : ℂ) - 2 * X.im * W.im + X.im ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    rw [hX]
    ring
  have hdT : dist (X : ℂ) (T : ℂ) ^ 2
      = Complex.normSq (T : ℂ) - 2 * X.im * T.im + X.im ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    rw [hX]
    ring
  rw [hdW, hdT] at h1
  have h2 : (Complex.normSq (W : ℂ) + X.im ^ 2) * T.im * (2 * X.im)
      = (Complex.normSq (T : ℂ) + X.im ^ 2) * W.im * (2 * X.im) := by
    linear_combination h1
  exact mul_right_cancel₀ (by positivity : (0:ℝ) < 2 * X.im).ne' h2

/-- Two distinct points lying on the perpendicular bisectors of `(τ', p)` and of `(τ', q)`
force `p = q`: the mirror of a point across the geodesic through two points is unique. -/
theorem bisector_pair_unique {x y τ' p q : UpperHalfPlane} (hxy : x ≠ y)
    (hxp : dist x τ' = dist x p) (hyp : dist y τ' = dist y p)
    (hxq : dist x τ' = dist x q) (hyq : dist y τ' = dist y q)
    (hp : p ≠ τ') (hq : q ≠ τ') : p = q := by
  obtain ⟨g, hgx, hgy⟩ := exists_verticalize x y
  have hgxy : g • x ≠ g • y := fun h => hxy (smul_left_cancel g h)
  have him_ne : (g • x).im ≠ (g • y).im := fun h => hgxy (ext_re_im
    (hgx.trans hgy.symm) h)
  have hsq_ne : (g • x).im ^ 2 ≠ (g • y).im ^ 2 := by
    intro h
    have h2 : ((g • x).im - (g • y).im) * ((g • x).im + (g • y).im) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact him_ne (by linarith)
    · linarith [(g • x).im_pos, (g • y).im_pos]
  have key : ∀ w : UpperHalfPlane, w ≠ τ' →
      dist x τ' = dist x w → dist y τ' = dist y w →
      (g • w).im = (g • τ').im ∧ (g • w).re = -(g • τ').re ∧ (g • τ').re ≠ 0 := by
    intro w hw hxw hyw
    have E1 := axis_dist_eq hgx
      (show dist (g • x) (g • τ') = dist (g • x) (g • w) by
        rw [dist_smul, dist_smul]; exact hxw)
    have E2 := axis_dist_eq hgy
      (show dist (g • y) (g • τ') = dist (g • y) (g • w) by
        rw [dist_smul, dist_smul]; exact hyw)
    have h5 : ((g • x).im ^ 2 - (g • y).im ^ 2)
        * ((g • w).im - (g • τ').im) = 0 := by
      linear_combination E1 - E2
    have him : (g • w).im = (g • τ').im := by
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd (by linarith : (g • x).im ^ 2 = (g • y).im ^ 2) hsq_ne
      · linarith
    have hgwτ : g • w ≠ g • τ' := fun h => hw (smul_left_cancel g h)
    have hn : Complex.normSq ((g • w : UpperHalfPlane) : ℂ)
        = Complex.normSq ((g • τ' : UpperHalfPlane) : ℂ) := by
      have h7 : (Complex.normSq ((g • w : UpperHalfPlane) : ℂ)
            - Complex.normSq ((g • τ' : UpperHalfPlane) : ℂ)) * (g • τ').im = 0 := by
        rw [him] at E1
        linear_combination -E1
      rcases mul_eq_zero.mp h7 with h8 | h8
      · linarith
      · linarith [(g • τ').im_pos]
    have hre2 : (g • w).re ^ 2 = (g • τ').re ^ 2 := by
      rw [Complex.normSq_apply, Complex.normSq_apply] at hn
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn
      linear_combination hn - ((g • w).im + (g • τ').im) * him
    have hre_ne : (g • w).re ≠ (g • τ').re := fun h => hgwτ (ext_re_im h him)
    have hre : (g • w).re = -(g • τ').re := by
      have h9 : ((g • w).re - (g • τ').re) * ((g • w).re + (g • τ').re) = 0 := by
        linear_combination hre2
      rcases mul_eq_zero.mp h9 with h10 | h10
      · exact absurd (by linarith) hre_ne
      · linarith
    have h0 : (g • τ').re ≠ 0 := by
      intro h11
      exact hre_ne (by rw [hre, h11, neg_zero])
    exact ⟨him, hre, h0⟩
  obtain ⟨himp, hrep, -⟩ := key p hp hxp hyp
  obtain ⟨himq, hreq, -⟩ := key q hq hxq hyq
  have : g • p = g • q := ext_re_im (hrep.trans hreq.symm) (himp.trans himq.symm)
  exact smul_left_cancel g this

/-! ## The oriented bisector normalizer -/

/-- The mirror normalizer with an orientation sign: after a Möbius normalization the
`p`-side of the perpendicular bisector of `(p, q)` is a coordinate half-plane. -/
theorem bisector_normalizer {p q : UpperHalfPlane} (hpq : p ≠ q) :
    ∃ (g : SL(2, ℝ)) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      (∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε * (g • z).re ≤ 0) ∧
      (∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε * (g • z).re) := by
  obtain ⟨g, him, hre, h0⟩ := exists_mirror_normalizer hpq
  have hkey : ∀ z : UpperHalfPlane, dist z p = dist (g • z) (g • p) :=
    fun z => (dist_smul g z p).symm
  have hkey' : ∀ z : UpperHalfPlane, dist z q = dist (g • z) (g • q) :=
    fun z => (dist_smul g z q).symm
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · refine ⟨g, 1, Or.inl rfl, ?_, ?_⟩
    · intro z
      have hset := setOf_dist_le_eq_of_im_eq (a := g • p) (b := g • q) him.symm
        (by rw [hre]; linarith)
      have h := Set.ext_iff.mp hset (g • z)
      simp only [Set.mem_setOf_eq] at h
      rw [hkey z, hkey' z, h, hre, one_mul]
      constructor <;> intro <;> linarith
    · intro z
      have hset := setOf_dist_le_eq_of_im_eq' (a := g • q) (b := g • p) him
        (by rw [hre]; linarith)
      have h := Set.ext_iff.mp hset (g • z)
      simp only [Set.mem_setOf_eq] at h
      rw [hkey z, hkey' z, h, hre, one_mul]
      constructor <;> intro <;> linarith
  · refine ⟨g, -1, Or.inr rfl, ?_, ?_⟩
    · intro z
      have hset := setOf_dist_le_eq_of_im_eq' (a := g • p) (b := g • q) him.symm
        (by rw [hre]; linarith)
      have h := Set.ext_iff.mp hset (g • z)
      simp only [Set.mem_setOf_eq] at h
      rw [hkey z, hkey' z, h, hre]
      constructor <;> intro <;> linarith
    · intro z
      have hset := setOf_dist_le_eq_of_im_eq (a := g • q) (b := g • p) him
        (by rw [hre]; linarith)
      have h := Set.ext_iff.mp hset (g • z)
      simp only [Set.mem_setOf_eq] at h
      rw [hkey z, hkey' z, h, hre]
      constructor <;> intro <;> linarith

/-! ## Points of a circle-carried segment are determined by their real part -/

/-- On a geodesic segment carried by a semicircle, the real part determines the point. -/
theorem eq_of_re_eq_of_mem_geodSeg {A B x y : UpperHalfPlane}
    (hAB : ¬ A.re = B.re) (hx : x ∈ geodSeg A B) (hy : y ∈ geodSeg A B)
    (hre : x.re = y.re) : x = y := by
  have hxc := mem_geodSeg_circle hAB hx
  have hyc := mem_geodSeg_circle hAB hy
  have hxn : Complex.normSq ((x : ℂ) - (geodCenter A B : ℂ))
      = geodRadius A B ^ 2 := by
    rw [← Complex.sq_norm, hxc]
  have hyn : Complex.normSq ((y : ℂ) - (geodCenter A B : ℂ))
      = geodRadius A B ^ 2 := by
    rw [← Complex.sq_norm, hyc]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hxn hyn
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero] at hxn hyn
  have him2 : x.im ^ 2 = y.im ^ 2 := by
    linear_combination hxn - hyn - ((x.re - geodCenter A B) + (y.re - geodCenter A B))
      * hre
  have him : x.im = y.im := by
    have h2 : (x.im - y.im) * (x.im + y.im) = 0 := by linear_combination him2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith [x.im_pos, y.im_pos]
  exact ext_re_im hre him

/-! ## Tiles as half-spaces; contact elements and sides -/

/-- Every point of the `γ`-tile is at least as close to the tile center as to any other
orbit point. -/
theorem smul_dirichletDomain_subset (γ η : ↥Γ) :
    (γ • ·) '' dirichletDomain Γ τ₀ ⊆
      {w : UpperHalfPlane | dist w (γ • τ₀) ≤ dist w (η • τ₀)} := by
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  rintro w ⟨u, hu, rfl⟩
  have e1 : dist (γ • u) (γ • τ₀) = dist u τ₀ := dist_smul γ u τ₀
  have e2 : dist (γ • u) (η • τ₀) = dist u ((γ⁻¹ * η) • τ₀) := by
    calc dist (γ • u) (η • τ₀) = dist (γ⁻¹ • γ • u) (γ⁻¹ • η • τ₀) :=
        (dist_smul γ⁻¹ _ _).symm
      _ = dist u ((γ⁻¹ * η) • τ₀) := by rw [inv_smul_smul, mul_smul]
  rw [Set.mem_setOf_eq, e1, e2]
  exact hu (γ⁻¹ * η)

/-- A point common to the domain and to the `γ`-tile lies on the side of `γ`. -/
theorem inter_smul_subset_sideSet (γ : ↥Γ) :
    dirichletDomain Γ τ₀ ∩ (γ • ·) '' dirichletDomain Γ τ₀
      ⊆ dirichletSideSet Γ τ₀ γ := by
  rintro w ⟨hwD, hwT⟩
  have h1 : dist w (γ • τ₀) ≤ dist w ((1 : ↥Γ) • τ₀) :=
    smul_dirichletDomain_subset γ 1 hwT
  rw [one_smul] at h1
  exact ⟨hwD, le_antisymm (hwD γ) h1⟩

/-- Under freeness, elements with the same basepoint image act identically. -/
theorem smul_eq_of_basepoint_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀) (w : UpperHalfPlane) : γ • w = δ • w := by
  have h1 : (δ⁻¹ * γ) • τ₀ = τ₀ := by
    rw [mul_smul, h, inv_smul_smul]
  have h2 := hfree (δ⁻¹ * γ) ⟨τ₀, h1⟩ w
  rw [mul_smul] at h2
  calc γ • w = δ • δ⁻¹ • γ • w := by rw [smul_inv_smul]
    _ = δ • w := by rw [h2]

/-- Tiles of elements with the same basepoint image coincide. -/
theorem smul_image_eq_of_basepoint_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀) :
    (γ • ·) '' dirichletDomain Γ τ₀ = (δ • ·) '' dirichletDomain Γ τ₀ := by
  have hfun : (γ • ·) = (δ • · : UpperHalfPlane → UpperHalfPlane) :=
    funext (smul_eq_of_basepoint_eq hfree h)
  rw [hfun]

/-- The side set depends only on the basepoint image of its element. -/
theorem sideSet_eq_of_basepoint_eq {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀) :
    dirichletSideSet Γ τ₀ γ = dirichletSideSet Γ τ₀ δ := by
  unfold dirichletSideSet
  rw [h]

/-- Domain membership realizes the distance to the orbit at the basepoint itself. -/
theorem dist_basepoint_eq_infDist {z : UpperHalfPlane}
    (hz : z ∈ dirichletDomain Γ τ₀) :
    dist z τ₀ = Metric.infDist z (MulAction.orbit Γ τ₀) := by
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_self τ₀))
  refine (Metric.le_infDist ⟨τ₀, MulAction.mem_orbit_self τ₀⟩).mpr ?_
  intro y hy
  obtain ⟨δ, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  exact hz δ

theorem one_mem_contactSet {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) :
    (1 : ↥Γ) ∈ contactSet Γ τ₀ z := by
  simp only [contactSet, Set.mem_setOf_eq, one_smul]
  exact dist_basepoint_eq_infDist hz

theorem mem_contactSet_of_mem_sideSet {γ : ↥Γ} {z : UpperHalfPlane}
    (hz : z ∈ dirichletSideSet Γ τ₀ γ) : γ ∈ contactSet Γ τ₀ z := by
  obtain ⟨hzD, hzeq⟩ := hz
  simp only [contactSet, Set.mem_setOf_eq]
  rw [← hzeq]
  exact dist_basepoint_eq_infDist hzD

/-- A domain point lies on the side set of each of its contact elements. -/
theorem mem_sideSet_of_contact {δ : ↥Γ} {z : UpperHalfPlane}
    (hzD : z ∈ dirichletDomain Γ τ₀) (hδ : δ ∈ contactSet Γ τ₀ z) :
    z ∈ dirichletSideSet Γ τ₀ δ := by
  have h := smul_mem_dirichletSideSet_of_contact_pair (one_mem_contactSet hzD) hδ
  rw [inv_one, one_smul, one_mul] at h
  exact h

/-- A point equidistant from the basepoint and a moved basepoint differs from both. -/
theorem ne_of_bisector {γ : ↥Γ} (hmove : γ • τ₀ ≠ τ₀) {z : UpperHalfPlane}
    (hzeq : dist z τ₀ = dist z (γ • τ₀)) : z ≠ τ₀ ∧ z ≠ γ • τ₀ := by
  constructor
  · intro h
    subst h
    rw [dist_self] at hzeq
    exact hmove (dist_eq_zero.mp hzeq.symm).symm
  · intro h
    subst h
    rw [dist_self] at hzeq
    exact hmove (dist_eq_zero.mp hzeq)

/-! ## A segment from inside to outside meets the frontier -/

/-- A geodesic segment with one end in a set and the other off it meets the frontier. -/
theorem exists_frontier_mem_geodSeg {S : Set UpperHalfPlane} {x y : UpperHalfPlane}
    (hx : x ∈ S) (hy : y ∉ S) :
    ∃ w ∈ geodSeg x y, w ∈ frontier S := by
  have hconn : IsPreconnected (geodSeg x y) := by
    rw [geodSeg_eq_image_geodInterp]
    refine isPreconnected_Icc.image _ ?_
    exact (continuous_geodInterp.comp (continuous_const.prodMk
      (continuous_const.prodMk continuous_id))).continuousOn
  by_contra hcon
  push_neg at hcon
  have hxint : x ∈ interior S := by
    have h1 : x ∈ closure S := subset_closure hx
    have h2 := hcon x (left_mem_geodSeg x y)
    rw [frontier, Set.mem_diff] at h2
    push_neg at h2
    exact h2 h1
  have hyext : y ∈ (closure S)ᶜ := by
    intro h1
    have h2 := hcon y (right_mem_geodSeg x y)
    rw [frontier, Set.mem_diff] at h2
    push_neg at h2
    exact hy (interior_subset (h2 h1))
  have hcover : geodSeg x y ⊆ interior S ∪ (closure S)ᶜ := by
    intro w hw
    by_cases h1 : w ∈ closure S
    · left
      have h2 := hcon w hw
      rw [frontier, Set.mem_diff] at h2
      push_neg at h2
      exact h2 h1
    · right
      exact h1
  obtain ⟨z, -, hz1, hz2⟩ := hconn (interior S) (closure S)ᶜ isOpen_interior
    isClosed_closure.isOpen_compl hcover ⟨x, left_mem_geodSeg x y, hxint⟩
    ⟨y, right_mem_geodSeg x y, hyext⟩
  exact hz2 (subset_closure (interior_subset hz1))

/-! ## Interior of the radial segment -/

/-- Points of the segment from the basepoint to a domain point, other than the far end,
are interior points of the Dirichlet domain: a bisector touching the segment strictly
inside would collapse the touching point onto the far end. -/
theorem mem_interior_of_mem_geodSeg (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v w : UpperHalfPlane} (hv : v ∈ dirichletDomain Γ τ₀)
    (hw : w ∈ geodSeg τ₀ v) (hwv : w ≠ v) :
    w ∈ interior (dirichletDomain Γ τ₀) := by
  have hwD : w ∈ dirichletDomain Γ τ₀ :=
    geodConvex_dirichletDomain τ₀ basepoint_mem_dirichletDomain v hv hw
  rw [interior_dirichletDomain_eq hΓ hdense]
  intro η hmove
  rcases lt_or_eq_of_le (hwD η) with h | heq
  · exact h
  exfalso
  have hpq : τ₀ ≠ η • τ₀ := Ne.symm hmove
  obtain ⟨g, ε, hε, hle, hge⟩ := bisector_normalizer hpq
  have hw0 : ε * (g • w).re = 0 := le_antisymm ((hle w).mp heq.le) ((hge w).mp heq.ge)
  have hτ₀neg : ε * (g • τ₀).re < 0 := by
    have h1 : ¬ dist τ₀ (η • τ₀) ≤ dist τ₀ τ₀ := by
      rw [dist_self]
      intro h2
      exact hmove (dist_le_zero.mp h2).symm
    have h2 : ¬ (0 ≤ ε * (g • τ₀).re) := fun h3 => h1 ((hge τ₀).mpr h3)
    exact not_le.mp h2
  have hvle : ε * (g • v).re ≤ 0 := (hle v).mp (hv η)
  have hwseg : g • w ∈ geodSeg (g • τ₀) (g • v) := by
    rw [← smul_geodSeg]
    exact ⟨w, hw, rfl⟩
  have hbounds := re_mem_geodSeg hwseg
  have hvre : (g • v).re = 0 ∧ ¬ (g • τ₀).re = (g • v).re ∧ (g • w).re = 0 := by
    rcases hε with hε1 | hε1
    · rw [hε1, one_mul] at hw0 hτ₀neg hvle
      have h5 := hbounds.2
      have h4 : (g • v).re = 0 := by
        rcases max_cases ((g • τ₀).re) ((g • v).re) with ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [hm] at h5; linarith
        · rw [hm] at h5; linarith
      exact ⟨h4, by rw [h4]; exact hτ₀neg.ne, hw0⟩
    · rw [hε1] at hw0 hτ₀neg hvle
      have hw0' : (g • w).re = 0 := by linarith
      have hτ₀' : 0 < (g • τ₀).re := by linarith
      have hv' : 0 ≤ (g • v).re := by linarith
      have h5 := hbounds.1
      rw [hw0'] at h5
      have h4 : (g • v).re = 0 := by
        rcases min_cases ((g • τ₀).re) ((g • v).re) with ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [hm] at h5; linarith
        · rw [hm] at h5; linarith
      exact ⟨h4, by rw [h4]; exact hτ₀'.ne', hw0'⟩
  obtain ⟨hvre0, hABne, hwre0⟩ := hvre
  have heqwv : g • w = g • v :=
    eq_of_re_eq_of_mem_geodSeg hABne hwseg (right_mem_geodSeg _ _)
      (by rw [hvre0, hwre0])
  exact hwv (smul_left_cancel g heqwv)

/-! ## Horizontal displacements and axis points -/

/-- The hyperbolic distance between two points at the same height. -/
theorem dist_mk_horizontal (a b y : ℝ) (h₁ : 0 < ((⟨a, y⟩ : ℂ)).im)
    (h₂ : 0 < ((⟨b, y⟩ : ℂ)).im) :
    dist (UpperHalfPlane.mk ⟨a, y⟩ h₁) (UpperHalfPlane.mk ⟨b, y⟩ h₂)
      = 2 * Real.arsinh (|a - b| / (2 * y)) := by
  have hy : 0 < y := h₁
  rw [UpperHalfPlane.dist_eq, UpperHalfPlane.coe_mk, UpperHalfPlane.mk_im,
    UpperHalfPlane.mk_im, Real.sqrt_mul_self hy.le]
  congr 2
  rw [Complex.dist_eq]
  have h1 : ((⟨a, y⟩ : ℂ) - (⟨b, y⟩ : ℂ)) = ((a - b : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re]
    · simp [Complex.sub_im]
  rw [show ((UpperHalfPlane.mk ⟨b, y⟩ hy : UpperHalfPlane) : ℂ) = (⟨b, y⟩ : ℂ) from
    UpperHalfPlane.coe_mk _ _, h1, Complex.norm_real, Real.norm_eq_abs]

/-- Every point of the upper half plane is the `mk` of its coordinates. -/
theorem mk_coords (z : UpperHalfPlane) :
    UpperHalfPlane.mk ⟨z.re, z.im⟩ z.im_pos = z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_mk]
  apply Complex.ext
  · rw [UpperHalfPlane.coe_re]
  · rw [UpperHalfPlane.coe_im]

/-! ## The bisector extends beyond each of its points -/

/-- On the perpendicular bisector of a pair, beyond any bisector point `v` as seen from a
second bisector point `e`, there are bisector points at every prescribed distance. -/
theorem exists_beyond {p q v e : UpperHalfPlane} (hpq : p ≠ q)
    (hv : dist v p = dist v q) (he : dist e p = dist e q) (hve : v ≠ e)
    {t : ℝ} (ht : 0 < t) :
    ∃ w : UpperHalfPlane, dist w p = dist w q ∧ dist w v = t ∧ v ∈ geodSeg w e := by
  obtain ⟨g, ε, hε, hle, hge⟩ := bisector_normalizer hpq
  have hv0 : (g • v).re = 0 := by
    have h := le_antisymm ((hle v).mp hv.le) ((hge v).mp hv.ge)
    rcases hε with h1 | h1 <;> rw [h1] at h <;> linarith
  have he0 : (g • e).re = 0 := by
    have h := le_antisymm ((hle e).mp he.le) ((hge e).mp he.ge)
    rcases hε with h1 | h1 <;> rw [h1] at h <;> linarith
  have him_ne : (g • v).im ≠ (g • e).im := fun h => hve (smul_left_cancel g
    (ext_re_im (hv0.trans he0.symm) h))
  have hlne : Real.log (g • v).im ≠ Real.log (g • e).im := by
    intro h
    apply him_ne
    rw [← Real.exp_log (g • v).im_pos, ← Real.exp_log (g • e).im_pos, h]
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℝ,
      |L - Real.log (g • v).im| = t ∧
      |L - Real.log (g • v).im| + |Real.log (g • v).im - Real.log (g • e).im|
        = |L - Real.log (g • e).im| := by
    rcases lt_or_gt_of_ne hlne with hc | hc
    · refine ⟨Real.log (g • v).im - t, ?_, ?_⟩
      · rw [show Real.log (g • v).im - t - Real.log (g • v).im = -t by ring, abs_neg,
          abs_of_pos ht]
      · rw [show Real.log (g • v).im - t - Real.log (g • v).im = -t by ring, abs_neg,
          abs_of_pos ht, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        ring
    · refine ⟨Real.log (g • v).im + t, ?_, ?_⟩
      · rw [show Real.log (g • v).im + t - Real.log (g • v).im = t by ring, abs_of_pos ht]
      · rw [show Real.log (g • v).im + t - Real.log (g • v).im = t by ring, abs_of_pos ht,
          abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        ring
  have hWpos : (0 : ℝ) < ((⟨0, Real.exp L⟩ : ℂ)).im := Real.exp_pos L
  set W : UpperHalfPlane := UpperHalfPlane.mk ⟨0, Real.exp L⟩ hWpos with hWdef
  have hWre : W.re = 0 := by rw [hWdef, UpperHalfPlane.mk_re]
  have hWim : W.im = Real.exp L := by rw [hWdef, UpperHalfPlane.mk_im]
  have hgW : g • (g⁻¹ • W) = W := smul_inv_smul g W
  have hdWv : dist (g⁻¹ • W) v = |L - Real.log (g • v).im| := by
    calc dist (g⁻¹ • W) v = dist (g • g⁻¹ • W) (g • v) := (dist_smul g _ _).symm
      _ = dist W (g • v) := by rw [smul_inv_smul]
      _ = |L - Real.log (g • v).im| := by
          rw [dist_of_re_eq (hWre.trans hv0.symm), hWim, Real.log_exp]
  refine ⟨g⁻¹ • W, ?_, ?_, ?_⟩
  · have h1 : ε * (g • (g⁻¹ • W)).re = 0 := by rw [hgW, hWre, mul_zero]
    exact le_antisymm ((hle _).mpr h1.le) ((hge _).mpr h1.ge)
  · rw [hdWv, hL1]
  · rw [mem_geodSeg]
    have hdve : dist v e = |Real.log (g • v).im - Real.log (g • e).im| := by
      calc dist v e = dist (g • v) (g • e) := (dist_smul g _ _).symm
        _ = _ := dist_of_re_eq (hv0.trans he0.symm)
    have hdWe : dist (g⁻¹ • W) e = |L - Real.log (g • e).im| := by
      calc dist (g⁻¹ • W) e = dist (g • g⁻¹ • W) (g • e) := (dist_smul g _ _).symm
        _ = dist W (g • e) := by rw [smul_inv_smul]
        _ = |L - Real.log (g • e).im| := by
            rw [dist_of_re_eq (hWre.trans he0.symm), hWim, Real.log_exp]
    rw [hdWv, hdve, hdWe]
    exact hL2

/-! ## Bisector points are limits of strict-side points -/

/-- A bisector point of an open set all of whose strict-side points lie in a closed set
belongs to the closed set. -/
theorem mem_of_strict_side {p q : UpperHalfPlane} (hpq : p ≠ q)
    {U D' : Set UpperHalfPlane} (hU : IsOpen U) (hD : IsClosed D')
    (hsub : ∀ x ∈ U, dist x p < dist x q → x ∈ D')
    {w : UpperHalfPlane} (hweq : dist w p = dist w q) (hwU : w ∈ U) : w ∈ D' := by
  obtain ⟨g, ε, hε, hle, hge⟩ := bisector_normalizer hpq
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hw0 : ε * (g • w).re = 0 := le_antisymm ((hle w).mp hweq.le) ((hge w).mp hweq.ge)
  rw [← hD.closure_eq, Metric.mem_closure_iff]
  intro ρ hρ
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.mp hU w hwU
  set m : ℝ := min ρ ρ₁ with hm
  have hmpos : 0 < m := lt_min hρ hρ₁
  have hypos : 0 < (g • w).im := (g • w).im_pos
  set δ : ℝ := 2 * (g • w).im * Real.sinh (m / 4) with hδdef
  have hδpos : 0 < δ := by
    have := Real.sinh_pos_iff.mpr (by positivity : (0:ℝ) < m / 4)
    positivity
  have hP₁pos : (0 : ℝ) < ((⟨(g • w).re - ε * δ, (g • w).im⟩ : ℂ)).im := hypos
  set P₁ : UpperHalfPlane :=
    UpperHalfPlane.mk ⟨(g • w).re - ε * δ, (g • w).im⟩ hP₁pos with hP₁def
  have hP₁re : P₁.re = (g • w).re - ε * δ := by rw [hP₁def, UpperHalfPlane.mk_re]
  have hgP₁ : g • (g⁻¹ • P₁) = P₁ := smul_inv_smul g P₁
  have hd : dist (g⁻¹ • P₁) w = 2 * Real.arsinh (δ / (2 * (g • w).im)) := by
    calc dist (g⁻¹ • P₁) w = dist (g • g⁻¹ • P₁) (g • w) := (dist_smul g _ _).symm
      _ = dist P₁ (g • w) := by rw [smul_inv_smul]
      _ = 2 * Real.arsinh (δ / (2 * (g • w).im)) := by
          conv_lhs => rw [← mk_coords (g • w), hP₁def]
          rw [dist_mk_horizontal ((g • w).re - ε * δ) (g • w).re (g • w).im
            hP₁pos ((g • w).im_pos)]
          congr 2
          rw [show (g • w).re - ε * δ - (g • w).re = -(ε * δ) by ring, abs_neg, abs_mul,
            hεabs, one_mul, abs_of_pos hδpos]
  have hdval : dist (g⁻¹ • P₁) w = m / 2 := by
    rw [hd, hδdef]
    rw [show 2 * (g • w).im * Real.sinh (m / 4) / (2 * (g • w).im) = Real.sinh (m / 4) by
      field_simp]
    rw [Real.arsinh_sinh]
    ring
  have hmem : g⁻¹ • P₁ ∈ U := by
    apply hball
    rw [Metric.mem_ball, hdval]
    calc m / 2 < m := by linarith
      _ ≤ ρ₁ := min_le_right _ _
  have hstrict : ε * (g • (g⁻¹ • P₁)).re < 0 := by
    rw [hgP₁, hP₁re]
    have : ε * ((g • w).re - ε * δ) = ε * (g • w).re - δ := by
      rw [mul_sub]
      congr 1
      rw [← mul_assoc, hεsq, one_mul]
    rw [this, hw0]
    linarith
  have hP₁D : g⁻¹ • P₁ ∈ D' := by
    refine hsub _ hmem ?_
    rw [lt_iff_not_ge]
    intro h6
    exact (not_le.mpr hstrict) ((hge _).mp h6)
  refine ⟨g⁻¹ • P₁, hP₁D, ?_⟩
  rw [dist_comm, hdval]
  calc m / 2 < m := by linarith
    _ ≤ ρ := min_le_left _ _

/-! ## The targets: finiteness of sides, side determination, sides are segments -/

/-- The sides are finitely many: a side constrains the domain, so its element lies in the
finite active-side set of the density radius. -/
theorem finite_polygonSides (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSides Γ τ₀).Finite := by
  refine ((finite_dirichletSides hΓ τ₀ R).image
    (fun γ => dirichletSideSet Γ τ₀ γ)).subset ?_
  rintro s ⟨γ, ⟨hmove, x, hx, y, hy, hxy⟩, rfl⟩
  refine ⟨γ, ?_, rfl⟩
  have hx1 : dist x τ₀ ≤ R := Metric.mem_closedBall.mp
    (dirichletDomain_subset_closedBall hdense hx.1)
  have hx2 : dist x (γ • τ₀) = dist x τ₀ := hx.2.symm
  have h3 : dist τ₀ (γ • τ₀) ≤ dist τ₀ x + dist x (γ • τ₀) := dist_triangle _ _ _
  have h4 : dist τ₀ x = dist x τ₀ := dist_comm _ _
  show dist τ₀ (γ • τ₀) ≤ 2 * R + 1
  linarith

/-- A nondegenerate side determines the orbit point of its element: two points of the side
lie on both perpendicular bisectors, which then coincide, and a bisector determines the
reflected center. -/
theorem smul_basepoint_eq_of_sideSet_eq (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ) (hδ : IsSideElement Γ τ₀ δ)
    (h : dirichletSideSet Γ τ₀ γ = dirichletSideSet Γ τ₀ δ) :
    γ • τ₀ = δ • τ₀ := by
  obtain ⟨hmoveγ, x, hx, y, hy, hxy⟩ := hγ
  have hxδ : x ∈ dirichletSideSet Γ τ₀ δ := h ▸ hx
  have hyδ : y ∈ dirichletSideSet Γ τ₀ δ := h ▸ hy
  exact bisector_pair_unique hxy hx.2 hy.2 hxδ.2 hyδ.2 hmoveγ hδ.1

/-- Each side is a nondegenerate geodesic segment: the intersection of the convex compact
domain with the bisector geodesic. -/
theorem exists_geodSeg_of_polygonSide (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) :
    ∃ a b : UpperHalfPlane, a ≠ b ∧ s = geodSeg a b := by
  obtain ⟨γ, ⟨hmove, hnt⟩, rfl⟩ := hs
  obtain ⟨a, b, heq⟩ := exists_geodSeg_eq_inter_bisector
    (isCompact_dirichletDomain hdense) geodConvex_dirichletDomain (Ne.symm hmove)
    hnt.nonempty
  have heq' : dirichletSideSet Γ τ₀ γ = geodSeg a b := heq
  refine ⟨a, b, ?_, heq'⟩
  rintro rfl
  rw [geodSeg_self] at heq'
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  rw [heq'] at hx hy
  exact hxy (hx.trans hy.symm)

/-- The vertices are finitely many: each is an endpoint of one of the finitely many
sides. -/
theorem finite_polygonVertices (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonVertices Γ τ₀).Finite := by
  classical
  have hCBfin : ((fun γ : ↥Γ => γ • τ₀) '' (dirichletSides Γ τ₀ R)).Finite :=
    (finite_dirichletSides hΓ τ₀ R).image _
  set CB : Set UpperHalfPlane := (fun γ : ↥Γ => γ • τ₀) '' (dirichletSides Γ τ₀ R)
    with hCB
  have hsub : polygonVertices Γ τ₀ ⊆ ⋃ pq ∈ CB ×ˢ CB,
      {z : UpperHalfPlane | dist z τ₀ = dist z pq.1 ∧ dist z τ₀ = dist z pq.2 ∧
        pq.1 ≠ pq.2 ∧ pq.1 ≠ τ₀ ∧ pq.2 ≠ τ₀} := by
    intro z hz
    obtain ⟨hzD, hz3⟩ := hz
    have hfin : (tileCenters Γ τ₀ z).Finite := (finite_contactSet hΓ τ₀ z).image _
    have h3 : 2 < (tileCenters Γ τ₀ z).ncard := hz3
    rw [Set.two_lt_ncard hfin] at h3
    obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, h12, h13, h23⟩ := h3
    have hdist : ∀ c ∈ tileCenters Γ τ₀ z, dist z τ₀ = dist z c := by
      rintro c ⟨δ, hδ, rfl⟩
      simp only [contactSet, Set.mem_setOf_eq] at hδ
      rw [dist_basepoint_eq_infDist hzD]
      exact hδ.symm
    have hCBmem : ∀ c ∈ tileCenters Γ τ₀ z, c ∈ CB := by
      rintro c ⟨δ, hδ, rfl⟩
      refine ⟨δ, ?_, rfl⟩
      have h5 : dist z τ₀ = dist z (δ • τ₀) := hdist _ ⟨δ, hδ, rfl⟩
      have h6 : dist z τ₀ ≤ R := Metric.mem_closedBall.mp
        (dirichletDomain_subset_closedBall hdense hzD)
      have h7 : dist τ₀ (δ • τ₀) ≤ dist τ₀ z + dist z (δ • τ₀) := dist_triangle _ _ _
      have h8 : dist τ₀ z = dist z τ₀ := dist_comm _ _
      show dist τ₀ (δ • τ₀) ≤ 2 * R + 1
      linarith
    obtain ⟨p, hp, q, hq, hpq, hpτ, hqτ⟩ : ∃ p ∈ tileCenters Γ τ₀ z,
        ∃ q ∈ tileCenters Γ τ₀ z, p ≠ q ∧ p ≠ τ₀ ∧ q ≠ τ₀ := by
      by_cases h1 : c₁ = τ₀
      · exact ⟨c₂, hc₂, c₃, hc₃, h23, by rw [← h1]; exact Ne.symm h12,
          by rw [← h1]; exact Ne.symm h13⟩
      · by_cases h2 : c₂ = τ₀
        · exact ⟨c₁, hc₁, c₃, hc₃, h13, h1, by rw [← h2]; exact Ne.symm h23⟩
        · exact ⟨c₁, hc₁, c₂, hc₂, h12, h1, h2⟩
    rw [Set.mem_iUnion₂]
    exact ⟨(p, q), Set.mem_prod.mpr ⟨hCBmem p hp, hCBmem q hq⟩,
      ⟨hdist p hp, hdist q hq, hpq, hpτ, hqτ⟩⟩
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (hCBfin.prod hCBfin) ?_
  rintro ⟨p, q⟩ -
  refine Set.Subsingleton.finite ?_
  rintro z ⟨hz1, hz2, hpq, hpτ, hqτ⟩ w ⟨hw1, hw2, -, -, -⟩
  by_contra hzw
  exact hpq (bisector_pair_unique hzw hz1 hw1 hz2 hw2 hpτ hqτ)

/-! ## Tiles are closed; radial segments inside tiles -/

/-- Geodesic segments transport along the subgroup action. -/
theorem subgroup_smul_geodSeg (γ : ↥Γ) (a b : UpperHalfPlane) :
    (γ • ·) '' geodSeg a b = geodSeg (γ • a) (γ • b) := by
  have h1 : ((γ • ·) : UpperHalfPlane → UpperHalfPlane)
      = (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) • ·) := by
    funext w
    rw [Subgroup.smul_def]
  rw [h1, smul_geodSeg, ← Subgroup.smul_def, ← Subgroup.smul_def]

/-- Each tile of the Dirichlet tiling is closed. -/
theorem isClosed_tile (γ : ↥Γ) :
    IsClosed ((γ • ·) '' dirichletDomain Γ τ₀) := by
  have himg : (γ • ·) '' dirichletDomain Γ τ₀
      = (γ⁻¹ • ·) ⁻¹' dirichletDomain Γ τ₀ := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [inv_smul_smul] using hu
    · intro hw
      exact ⟨γ⁻¹ • w, hw, smul_inv_smul γ w⟩
  rw [himg]
  have hcont : Continuous ((γ⁻¹ • ·) : UpperHalfPlane → UpperHalfPlane) := by
    have h1 : ((γ⁻¹ • ·) : UpperHalfPlane → UpperHalfPlane)
        = (((γ⁻¹ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) := by
      funext w
      rw [Subgroup.smul_def]
    rw [h1]
    exact (isometry_smul UpperHalfPlane _).continuous
  exact (isClosed_dirichletDomain Γ τ₀).preimage hcont

/-- The segment from a tile center to a point of the tile stays inside the tile. -/
theorem geodSeg_center_subset_tile {γ : ↥Γ} {z : UpperHalfPlane}
    (hγ : γ ∈ contactSet Γ τ₀ z) :
    geodSeg (γ • τ₀) z ⊆ (γ • ·) '' dirichletDomain Γ τ₀ := by
  obtain ⟨u, huD, huz⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain γ z).mp hγ
  have huz' : γ • u = z := huz
  intro w hw
  rw [← huz', ← subgroup_smul_geodSeg] at hw
  obtain ⟨x, hx, hxw⟩ := hw
  exact ⟨x, geodConvex_dirichletDomain τ₀ basepoint_mem_dirichletDomain u huD hx, hxw⟩

/-- Two closed sets covering a punctured ball and meeting only at the puncture cannot both
meet the punctured ball. -/
theorem punctured_ball_two_closed {z : UpperHalfPlane} {r : ℝ} (hr : 0 < r)
    {A C : Set UpperHalfPlane} (hA : IsClosed A) (hC : IsClosed C)
    (hcov : Metric.ball z r \ {z} ⊆ A ∪ C) (hdisj : A ∩ C ⊆ {z})
    (hAne : (A ∩ (Metric.ball z r \ {z})).Nonempty)
    (hCne : (C ∩ (Metric.ball z r \ {z})).Nonempty) : False := by
  have hpre := isPreconnected_punctured_ball z r
  rw [isPreconnected_closed_iff] at hpre
  obtain ⟨w, hw⟩ := hpre A C hA hC hcov
    (hAne.imp fun x hx => ⟨hx.2, hx.1⟩) (hCne.imp fun x hx => ⟨hx.2, hx.1⟩)
  exact hw.1.2 (hdisj hw.2)

/-- **Point-contact dichotomy**: a bisector meeting the domain in exactly one point meets it
at a vertex — two tiles alone cannot cover a punctured disk about the contact point by
disjoint nonempty closed sets. -/
theorem mem_polygonVertices_of_sideSet_eq_singleton (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {γ : ↥Γ} (hmove : γ • τ₀ ≠ τ₀) {z : UpperHalfPlane}
    (h : dirichletSideSet Γ τ₀ γ = {z}) :
    z ∈ polygonVertices Γ τ₀ := by
  classical
  have hzS : z ∈ dirichletSideSet Γ τ₀ γ := by rw [h]; rfl
  obtain ⟨hzD, hzeq'⟩ := hzS
  have hzeq : dist z τ₀ = dist z (γ • τ₀) := hzeq'
  obtain ⟨hzτ, hzγτ⟩ := ne_of_bisector hmove hzeq
  have hγcon : γ ∈ contactSet Γ τ₀ z := mem_contactSet_of_mem_sideSet ⟨hzD, hzeq⟩
  refine ⟨hzD, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hfin : (tileCenters Γ τ₀ z).Finite := (finite_contactSet hΓ τ₀ z).image _
  have hmem1 : τ₀ ∈ tileCenters Γ τ₀ z :=
    ⟨1, one_mem_contactSet hzD, one_smul _ _⟩
  have hmem2 : γ • τ₀ ∈ tileCenters Γ τ₀ z := ⟨γ, hγcon, rfl⟩
  have hpairsub : ({τ₀, γ • τ₀} : Set UpperHalfPlane) ⊆ tileCenters Γ τ₀ z := by
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc'
    · exact hmem1
    · rw [Set.mem_singleton_iff] at hc'
      subst hc'
      exact hmem2
  have heqset : ({τ₀, γ • τ₀} : Set UpperHalfPlane) = tileCenters Γ τ₀ z := by
    refine Set.eq_of_subset_of_ncard_le hpairsub ?_ hfin
    rw [Set.ncard_pair (Ne.symm hmove)]
    omega
  obtain ⟨r, hr, hloc, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ z
  have hcov : Metric.ball z r \ {z} ⊆
      dirichletDomain Γ τ₀ ∪ (γ • ·) '' dirichletDomain Γ τ₀ := by
    rintro w ⟨hwB, -⟩
    obtain ⟨δ, hδcon, hδw⟩ := hcover w hwB
    have hδc : δ • τ₀ ∈ tileCenters Γ τ₀ z := ⟨δ, hδcon, rfl⟩
    rw [← heqset] at hδc
    rcases Set.mem_insert_iff.mp hδc with h1 | h1
    · left
      have heq1 : δ • τ₀ = (1 : ↥Γ) • τ₀ := by rw [one_smul]; exact h1
      rw [smul_image_eq_of_basepoint_eq hfree heq1] at hδw
      obtain ⟨u, hu, huw⟩ := hδw
      have huw' : u = w := by simpa using huw
      rw [← huw']
      exact hu
    · right
      have heq1 : δ • τ₀ = γ • τ₀ := Set.mem_singleton_iff.mp h1
      rw [smul_image_eq_of_basepoint_eq hfree heq1] at hδw
      exact hδw
  have hdisj : dirichletDomain Γ τ₀ ∩ (γ • ·) '' dirichletDomain Γ τ₀ ⊆ {z} := by
    intro w hw
    have h2 := inter_smul_subset_sideSet γ hw
    rw [h] at h2
    exact h2
  have hAne : (dirichletDomain Γ τ₀ ∩ (Metric.ball z r \ {z})).Nonempty := by
    obtain ⟨w, hwseg, hwz, hwd⟩ := exists_near_on_geodSeg (Ne.symm hzτ) hr
    exact ⟨w, geodConvex_dirichletDomain τ₀ basepoint_mem_dirichletDomain z hzD hwseg,
      Metric.mem_ball.mpr hwd, fun hc => hwz (Set.mem_singleton_iff.mp hc)⟩
  have hCne : ((γ • ·) '' dirichletDomain Γ τ₀ ∩ (Metric.ball z r \ {z})).Nonempty := by
    obtain ⟨w, hwseg, hwz, hwd⟩ := exists_near_on_geodSeg (Ne.symm hzγτ) hr
    exact ⟨w, geodSeg_center_subset_tile hγcon hwseg,
      Metric.mem_ball.mpr hwd, fun hc => hwz (Set.mem_singleton_iff.mp hc)⟩
  exact punctured_ball_two_closed hr (isClosed_dirichletDomain Γ τ₀)
    (isClosed_tile γ) hcov hdisj hAne hCne

/-- The frontier of the Dirichlet domain is the union of its sides. -/
theorem frontier_dirichletDomain_eq_sUnion (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    frontier (dirichletDomain Γ τ₀) = ⋃₀ polygonSides Γ τ₀ := by
  classical
  apply Set.Subset.antisymm
  · intro τ hτ
    have hτD : τ ∈ dirichletDomain Γ τ₀ := by
      rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hτ
      exact hτ.1
    have hbis := frontier_dirichletDomain_subset hΓ hdense hτ
    rw [Set.mem_iUnion₂] at hbis
    obtain ⟨γ, hγact, hτbis⟩ := hbis
    obtain ⟨-, hγmove⟩ := hγact
    have hτeq : dist τ τ₀ = dist τ (γ • τ₀) := hτbis
    by_cases hex : ∃ δ ∈ contactSet Γ τ₀ τ, δ • τ₀ ≠ τ₀ ∧
        (dirichletSideSet Γ τ₀ δ).Nontrivial
    · obtain ⟨δ, hδcon, hδmove, hδnt⟩ := hex
      exact ⟨dirichletSideSet Γ τ₀ δ, ⟨δ, ⟨hδmove, hδnt⟩, rfl⟩,
        mem_sideSet_of_contact hτD hδcon⟩
    · exfalso
      push_neg at hex
      have hsingle : ∀ δ ∈ contactSet Γ τ₀ τ, δ • τ₀ ≠ τ₀ →
          dirichletSideSet Γ τ₀ δ = {τ} := by
        intro δ hδ hδm
        have hτδ : τ ∈ dirichletSideSet Γ τ₀ δ := mem_sideSet_of_contact hτD hδ
        exact (hex δ hδ hδm).eq_singleton_of_mem hτδ
      have hγcon : γ ∈ contactSet Γ τ₀ τ :=
        mem_contactSet_of_mem_sideSet ⟨hτD, hτeq⟩
      obtain ⟨hττ₀, hτγ⟩ := ne_of_bisector hγmove hτeq
      obtain ⟨r, hr, hloc, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ τ
      have hMCfin : ({δ ∈ contactSet Γ τ₀ τ | δ • τ₀ ≠ τ₀}).Finite :=
        (finite_contactSet hΓ τ₀ τ).subset (fun δ hδ => hδ.1)
      have hCclosed : IsClosed (⋃ δ ∈ {δ ∈ contactSet Γ τ₀ τ | δ • τ₀ ≠ τ₀},
          (δ • ·) '' dirichletDomain Γ τ₀) :=
        Set.Finite.isClosed_biUnion hMCfin (fun δ _ => isClosed_tile δ)
      have hcov : Metric.ball τ r \ {τ} ⊆ dirichletDomain Γ τ₀ ∪
          ⋃ δ ∈ {δ ∈ contactSet Γ τ₀ τ | δ • τ₀ ≠ τ₀},
            (δ • ·) '' dirichletDomain Γ τ₀ := by
        rintro w ⟨hwB, -⟩
        obtain ⟨δ, hδcon, hδw⟩ := hcover w hwB
        by_cases hδm : δ • τ₀ = τ₀
        · left
          have heq1 : δ • τ₀ = (1 : ↥Γ) • τ₀ := by rw [one_smul]; exact hδm
          rw [smul_image_eq_of_basepoint_eq hfree heq1] at hδw
          obtain ⟨u, hu, huw⟩ := hδw
          have huw' : u = w := by simpa using huw
          rw [← huw']
          exact hu
        · right
          rw [Set.mem_iUnion₂]
          exact ⟨δ, ⟨hδcon, hδm⟩, hδw⟩
      have hdisj : dirichletDomain Γ τ₀ ∩
          (⋃ δ ∈ {δ ∈ contactSet Γ τ₀ τ | δ • τ₀ ≠ τ₀},
            (δ • ·) '' dirichletDomain Γ τ₀) ⊆ {τ} := by
        rintro w ⟨hwD, hwC⟩
        rw [Set.mem_iUnion₂] at hwC
        obtain ⟨δ, hδMC, hwδ⟩ := hwC
        have hwside := inter_smul_subset_sideSet δ ⟨hwD, hwδ⟩
        rw [hsingle δ hδMC.1 hδMC.2] at hwside
        exact hwside
      have hAne : (dirichletDomain Γ τ₀ ∩ (Metric.ball τ r \ {τ})).Nonempty := by
        obtain ⟨w, hwseg, hwτ, hwd⟩ := exists_near_on_geodSeg (Ne.symm hττ₀) hr
        exact ⟨w, geodConvex_dirichletDomain τ₀ basepoint_mem_dirichletDomain τ hτD hwseg,
          Metric.mem_ball.mpr hwd, fun hc => hwτ (Set.mem_singleton_iff.mp hc)⟩
      have hCne : ((⋃ δ ∈ {δ ∈ contactSet Γ τ₀ τ | δ • τ₀ ≠ τ₀},
          (δ • ·) '' dirichletDomain Γ τ₀) ∩ (Metric.ball τ r \ {τ})).Nonempty := by
        obtain ⟨w, hwseg, hwτ, hwd⟩ := exists_near_on_geodSeg (Ne.symm hτγ) hr
        refine ⟨w, ?_, Metric.mem_ball.mpr hwd,
          fun hc => hwτ (Set.mem_singleton_iff.mp hc)⟩
        rw [Set.mem_iUnion₂]
        exact ⟨γ, ⟨hγcon, hγmove⟩, geodSeg_center_subset_tile hγcon hwseg⟩
      exact punctured_ball_two_closed hr (isClosed_dirichletDomain Γ τ₀)
        hCclosed hcov hdisj hAne hCne
  · intro w hw
    obtain ⟨s, hs, hws⟩ := hw
    obtain ⟨γ, ⟨hγmove, -⟩, rfl⟩ := hs
    obtain ⟨hwD, hweq'⟩ := hws
    have hweq : dist w τ₀ = dist w (γ • τ₀) := hweq'
    rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq]
    refine ⟨hwD, ?_⟩
    intro hcon
    rw [interior_dirichletDomain_eq hΓ hdense] at hcon
    exact absurd hweq (ne_of_lt (hcon γ hγmove))

/-- A point at which a side set is a nondegenerate segment with that point as an end is a
vertex: were there only two tiles, the domain would contain the bisector beyond the end. -/
theorem vertex_of_endpoint_core (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {γ : ↥Γ} (hmove : γ • τ₀ ≠ τ₀) {v e : UpperHalfPlane} (hve : v ≠ e)
    (hside : dirichletSideSet Γ τ₀ γ = geodSeg v e) :
    v ∈ polygonVertices Γ τ₀ := by
  classical
  have hvS : v ∈ dirichletSideSet Γ τ₀ γ := by
    rw [hside]
    exact left_mem_geodSeg v e
  obtain ⟨hvD, hveq'⟩ := hvS
  have hveq : dist v τ₀ = dist v (γ • τ₀) := hveq'
  have heS : e ∈ dirichletSideSet Γ τ₀ γ := by
    rw [hside]
    exact right_mem_geodSeg v e
  have heeq : dist e τ₀ = dist e (γ • τ₀) := heS.2
  obtain ⟨hvτ, hvγτ⟩ := ne_of_bisector hmove hveq
  have hγcon : γ ∈ contactSet Γ τ₀ v := mem_contactSet_of_mem_sideSet ⟨hvD, hveq⟩
  refine ⟨hvD, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hfin : (tileCenters Γ τ₀ v).Finite := (finite_contactSet hΓ τ₀ v).image _
  have hmem1 : τ₀ ∈ tileCenters Γ τ₀ v :=
    ⟨1, one_mem_contactSet hvD, one_smul _ _⟩
  have hmem2 : γ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨γ, hγcon, rfl⟩
  have hpairsub : ({τ₀, γ • τ₀} : Set UpperHalfPlane) ⊆ tileCenters Γ τ₀ v := by
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc'
    · exact hmem1
    · rw [Set.mem_singleton_iff] at hc'
      subst hc'
      exact hmem2
  have heqset : ({τ₀, γ • τ₀} : Set UpperHalfPlane) = tileCenters Γ τ₀ v := by
    refine Set.eq_of_subset_of_ncard_le hpairsub ?_ hfin
    rw [Set.ncard_pair (Ne.symm hmove)]
    omega
  obtain ⟨r, hr, hloc, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ v
  have hsub : ∀ x ∈ Metric.ball v r, dist x τ₀ < dist x (γ • τ₀) →
      x ∈ dirichletDomain Γ τ₀ := by
    intro x hxB hxlt
    obtain ⟨δ, hδcon, hδw⟩ := hcover x hxB
    have hδc : δ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨δ, hδcon, rfl⟩
    rw [← heqset] at hδc
    rcases Set.mem_insert_iff.mp hδc with h1 | h1
    · have heq1 : δ • τ₀ = (1 : ↥Γ) • τ₀ := by rw [one_smul]; exact h1
      rw [smul_image_eq_of_basepoint_eq hfree heq1] at hδw
      obtain ⟨u, hu, huw⟩ := hδw
      have huw' : u = x := by simpa using huw
      rw [← huw']
      exact hu
    · exfalso
      have heq1 : δ • τ₀ = γ • τ₀ := Set.mem_singleton_iff.mp h1
      rw [smul_image_eq_of_basepoint_eq hfree heq1] at hδw
      have h2 : dist x (γ • τ₀) ≤ dist x ((1 : ↥Γ) • τ₀) :=
        smul_dirichletDomain_subset γ 1 hδw
      rw [one_smul] at h2
      linarith
  obtain ⟨wb, hwb_eq, hwb_dist, hwb_between⟩ :=
    exists_beyond (Ne.symm hmove) hveq heeq hve (half_pos hr)
  have hwbU : wb ∈ Metric.ball v r := by
    rw [Metric.mem_ball, hwb_dist]
    linarith
  have hwbD : wb ∈ dirichletDomain Γ τ₀ :=
    mem_of_strict_side (Ne.symm hmove) Metric.isOpen_ball
      (isClosed_dirichletDomain Γ τ₀) hsub hwb_eq hwbU
  have hwbS : wb ∈ geodSeg v e := by
    rw [← hside]
    exact ⟨hwbD, hwb_eq⟩
  have hEnd : IsSegEndpoint (geodSeg v e) v :=
    (isSegEndpoint_geodSeg_iff hve).mpr (Or.inl rfl)
  rcases hEnd.2 wb hwbS e (right_mem_geodSeg v e) hwb_between with h3 | h3
  · rw [← h3, dist_self] at hwb_dist
    linarith
  · exact hve h3

/-- The endpoints of sides are vertices of the polygon. -/
theorem mem_polygonVertices_of_isSegEndpoint (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) {v : UpperHalfPlane}
    (hv : IsSegEndpoint s v) :
    v ∈ polygonVertices Γ τ₀ := by
  obtain ⟨a, b, hab, hseq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  obtain ⟨γ, ⟨hmove, hnt⟩, hsdef⟩ := hs
  rw [hsdef] at hseq hv
  rw [hseq] at hv
  rcases (isSegEndpoint_geodSeg_iff hab).mp hv with rfl | rfl
  · exact vertex_of_endpoint_core hΓ hfree hdense hmove hab hseq
  · refine vertex_of_endpoint_core hΓ hfree hdense hmove (Ne.symm hab) ?_
    rw [hseq, geodSeg_comm]

/-! ## Normalizer characterizations of the bisector and its strict sides -/

theorem normalizer_re_eq_zero {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {z : UpperHalfPlane} (hz : dist z p = dist z q) : (g • z).re = 0 := by
  have h := le_antisymm ((hle z).mp hz.le) ((hge z).mp hz.ge)
  rcases hε' with h1 | h1 <;> rw [h1] at h <;> linarith

theorem normalizer_eq_iff {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    (z : UpperHalfPlane) : dist z p = dist z q ↔ (g • z).re = 0 := by
  constructor
  · exact normalizer_re_eq_zero hε' hle hge
  · intro h0
    have h1 : ε' * (g • z).re = 0 := by rw [h0, mul_zero]
    exact le_antisymm ((hle z).mpr h1.le) ((hge z).mpr h1.ge)

theorem normalizer_lt_iff {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ}
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    (z : UpperHalfPlane) : dist z p < dist z q ↔ ε' * (g • z).re < 0 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact absurd ((hge z).mpr hc) (not_le.mpr h)
  · intro h
    by_contra hc
    push_neg at hc
    have := (hge z).mp hc
    linarith

/-! ## Sides through a vertex end at the vertex -/

/-- At a vertex, every side containing the vertex has it as an endpoint: a third tile
provides a half-space through the vertex which no side may cross. -/
theorem isSegEndpoint_of_vertex (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hvs : v ∈ s) :
    IsSegEndpoint s v := by
  classical
  obtain ⟨a, b, hab, hseq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  obtain ⟨γ, ⟨hmove, hnt⟩, rfl⟩ := hs
  obtain ⟨hvD, hv3⟩ := hv
  have hveq : dist v τ₀ = dist v (γ • τ₀) := hvs.2
  have hfin : (tileCenters Γ τ₀ v).Finite := (finite_contactSet hΓ τ₀ v).image _
  have h3 : 2 < (tileCenters Γ τ₀ v).ncard := hv3
  rw [Set.two_lt_ncard hfin] at h3
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, h12, h13, h23⟩ := h3
  obtain ⟨q, hqmem, hqτ, hqγ⟩ : ∃ q ∈ tileCenters Γ τ₀ v, q ≠ τ₀ ∧ q ≠ γ • τ₀ := by
    by_cases e1 : c₁ ≠ τ₀ ∧ c₁ ≠ γ • τ₀
    · exact ⟨c₁, hc₁, e1.1, e1.2⟩
    by_cases e2 : c₂ ≠ τ₀ ∧ c₂ ≠ γ • τ₀
    · exact ⟨c₂, hc₂, e2.1, e2.2⟩
    by_cases e3 : c₃ ≠ τ₀ ∧ c₃ ≠ γ • τ₀
    · exact ⟨c₃, hc₃, e3.1, e3.2⟩
    · exfalso
      rw [not_and_or, not_not, not_not] at e1 e2 e3
      rcases e1 with f1 | f1 <;> rcases e2 with f2 | f2 <;> rcases e3 with f3 | f3 <;>
        first
        | exact h12 (f1.trans f2.symm)
        | exact h13 (f1.trans f3.symm)
        | exact h23 (f2.trans f3.symm)
  obtain ⟨δ, hδcon, rfl⟩ := hqmem
  have hδmove : δ • τ₀ ≠ τ₀ := hqτ
  have hvδ : dist v τ₀ = dist v (δ • τ₀) := by
    simp only [contactSet, Set.mem_setOf_eq] at hδcon
    rw [dist_basepoint_eq_infDist hvD]
    exact hδcon.symm
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer (Ne.symm hδmove)
  have hε'ne : ε' ≠ 0 := by rcases hε' with h | h <;> rw [h] <;> norm_num
  have hgv : (g • v).re = 0 := normalizer_re_eq_zero hε' hle hge hvδ
  rw [hseq]
  rw [isSegEndpoint_geodSeg_iff hab]
  by_contra hcon
  push_neg at hcon
  obtain ⟨hvA, hvB⟩ := hcon
  have hvseg : v ∈ geodSeg a b := by rw [← hseq]; exact hvs
  have hgvseg : g • v ∈ geodSeg (g • a) (g • b) := by
    rw [← smul_geodSeg]
    exact ⟨v, hvseg, rfl⟩
  have haD : a ∈ dirichletDomain Γ τ₀ := by
    have h1 : a ∈ dirichletSideSet Γ τ₀ γ := by
      rw [hseq]
      exact left_mem_geodSeg a b
    exact h1.1
  have hbD : b ∈ dirichletDomain Γ τ₀ := by
    have h1 : b ∈ dirichletSideSet Γ τ₀ γ := by
      rw [hseq]
      exact right_mem_geodSeg a b
    exact h1.1
  have hale : ε' * (g • a).re ≤ 0 := (hle a).mp (haD δ)
  have hble : ε' * (g • b).re ≤ 0 := (hle b).mp (hbD δ)
  have hbounds := re_mem_geodSeg hgvseg
  have hψ : min (ε' * (g • a).re) (ε' * (g • b).re) ≤ ε' * (g • v).re ∧
      ε' * (g • v).re ≤ max (ε' * (g • a).re) (ε' * (g • b).re) := by
    rcases hε' with hE | hE <;> rw [hE]
    · simpa using hbounds
    · simp only [neg_one_mul]
      rw [min_neg_neg, max_neg_neg]
      exact ⟨neg_le_neg hbounds.2, neg_le_neg hbounds.1⟩
  have h5 := hψ.2
  rw [hgv, mul_zero] at h5
  have hor : (g • a).re = 0 ∨ (g • b).re = 0 := by
    rcases max_cases (ε' * (g • a).re) (ε' * (g • b).re) with ⟨hm, -⟩ | ⟨hm, -⟩
    · left
      rw [hm] at h5
      rcases mul_eq_zero.mp (le_antisymm hale h5) with h | h
      · exact absurd h hε'ne
      · exact h
    · right
      rw [hm] at h5
      rcases mul_eq_zero.mp (le_antisymm hble h5) with h | h
      · exact absurd h hε'ne
      · exact h
  by_cases hab' : (g • a).re = (g • b).re
  · have hare : (g • a).re = 0 := by
      rcases hor with h | h
      · exact h
      · rw [hab']; exact h
    have hxb : ∀ w ∈ dirichletSideSet Γ τ₀ γ, dist w τ₀ = dist w (δ • τ₀) := by
      intro w hw
      rw [hseq] at hw
      have hwseg : g • w ∈ geodSeg (g • a) (g • b) := by
        rw [← smul_geodSeg]
        exact ⟨w, hw, rfl⟩
      have hwre : (g • w).re = 0 := by
        rw [(mem_geodSeg_vertical hab' hwseg).1, hare]
      exact (normalizer_eq_iff hε' hle hge w).mpr hwre
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact hqγ (bisector_pair_unique hxy hx.2 hy.2 (hxb x hx) (hxb y hy)
      hmove hδmove).symm
  · rcases hor with h | h
    · exact hvA (smul_left_cancel g (eq_of_re_eq_of_mem_geodSeg hab' hgvseg
        (left_mem_geodSeg _ _) (by rw [hgv, h])))
    · exact hvB (smul_left_cancel g (eq_of_re_eq_of_mem_geodSeg hab' hgvseg
        (right_mem_geodSeg _ _) (by rw [hgv, h])))

/-! ## The sign of the disc frame at an axis point -/

/-- Based at an axis point, the imaginary part of the disc frame has the sign opposite to
the real part of the argument. -/
theorem discChart_im_sign {z : UpperHalfPlane} (hz : z.re = 0) (w : UpperHalfPlane) :
    ((0 : ℝ) < (discChart z w).im ↔ w.re < 0) ∧
      ((discChart z w).im = 0 ↔ w.re = 0) ∧
      ((discChart z w).im < 0 ↔ 0 < w.re) := by
  have hyy : 0 < z.im := z.im_pos
  have hden_im : ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I).im = w.im / z.im + 1 := by
    rw [Complex.add_im, Complex.div_ofReal_im, Complex.I_im, UpperHalfPlane.coe_im]
  have hden_ne : ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I) ≠ 0 := by
    intro hc
    have h2 := congrArg Complex.im hc
    rw [hden_im, Complex.zero_im] at h2
    have h3 : 0 < w.im / z.im := div_pos w.im_pos hyy
    linarith
  have hN : 0 < Complex.normSq ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I) :=
    Complex.normSq_pos.mpr hden_ne
  have him : (discChart z w).im = -2 * (w.re / z.im)
      / Complex.normSq ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I) := by
    rw [discChart, hz]
    rw [show ((0 : ℝ) : ℂ) = 0 by norm_num, sub_zero, Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.I_re, Complex.I_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero, add_zero]
    ring
  have hfirst : (0 : ℝ) < (discChart z w).im ↔ w.re < 0 := by
    rw [him]
    constructor
    · intro h
      have h2 := mul_pos h hN
      rw [div_mul_cancel₀ _ hN.ne'] at h2
      have h3 : w.re / z.im < 0 := by linarith
      rcases div_neg_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
      · linarith
      · exact h4
    · intro h
      refine div_pos ?_ hN
      have h3 : w.re / z.im < 0 := div_neg_of_neg_of_pos h hyy
      linarith
  have hsecond : (discChart z w).im = 0 ↔ w.re = 0 := by
    rw [him]
    rw [div_eq_zero_iff]
    constructor
    · intro h
      rcases h with h | h
      · have h2 : w.re / z.im = 0 := by linarith
        rcases div_eq_zero_iff.mp h2 with h3 | h3
        · exact h3
        · exact absurd h3 hyy.ne'
      · exact absurd h hN.ne'
    · intro h
      left
      rw [h, zero_div, mul_zero]
  refine ⟨hfirst, hsecond, ?_⟩
  constructor
  · intro h
    rcases lt_trichotomy w.re 0 with hr | hr | hr
    · exact absurd (hfirst.mpr hr) (by linarith)
    · exact absurd (hsecond.mpr hr) (by linarith)
    · exact hr
  · intro h
    rcases lt_trichotomy (discChart z w).im 0 with hr | hr | hr
    · exact hr
    · exact absurd (hsecond.mp hr) (by linarith)
    · exact absurd (hfirst.mp hr) (by linarith)

/-- The half-space of a bisector through `v`, read in the disc frame at `v`: a real-linear
functional of the frame value is zero exactly on the bisector and positive exactly on the
open near side. -/
theorem functional_sign {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {v : UpperHalfPlane} (hv : dist v p = dist v q) :
    ∃ m : ℂ, m ≠ 0 ∧
      (∀ w : UpperHalfPlane, dist w p = dist w q → ε' * (m * discChart v w).im = 0) ∧
      (∀ w : UpperHalfPlane, dist w p < dist w q → 0 < ε' * (m * discChart v w).im) := by
  have hvre : (g • v).re = 0 := normalizer_re_eq_zero hε' hle hge hv
  have hzim : ((v : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact v.im_pos.ne'
  have hzbim : (((starRingEnd ℂ) (v : ℂ))).im ≠ 0 := by
    rw [Complex.conj_im, UpperHalfPlane.coe_im]
    simpa using v.im_pos.ne'
  refine ⟨(((g 1 0 : ℝ) : ℂ) * (starRingEnd ℂ) (v : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (v : ℂ) + ((g 1 1 : ℝ) : ℂ)), ?_, ?_, ?_⟩
  · exact div_ne_zero (denom_ne_zero g hzbim) (denom_ne_zero g hzim)
  · intro w hw
    rw [(discChart_smul g v w).symm]
    have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
    rw [((discChart_im_sign hvre (g • w)).2.1).mpr hgw, mul_zero]
  · intro w hw
    rw [(discChart_smul g v w).symm]
    have hlt : ε' * (g • w).re < 0 := (normalizer_lt_iff hle hge w).mp hw
    rcases hε' with hE | hE
    · rw [hE, one_mul] at hlt ⊢
      exact ((discChart_im_sign hvre (g • w)).1).mpr hlt
    · rw [hE] at hlt ⊢
      have h2 : 0 < (g • w).re := by linarith
      have h3 := ((discChart_im_sign hvre (g • w)).2.2).mpr h2
      rw [neg_one_mul]
      exact neg_pos.mpr h3

set_option maxHeartbeats 400000 in
-- The three-normalizer assembly elaborates nine sign facts and a Cramer decomposition in
-- one declaration; the default heartbeat budget does not cover it.
/-- No point lies on three pairwise distinct sides: the boundary directions of the three
bisector half-planes through the point admit no compatible sign pattern. -/
theorem not_three_sides
    {γ₁ γ₂ γ₃ : ↥Γ} (h₁ : IsSideElement Γ τ₀ γ₁) (h₂ : IsSideElement Γ τ₀ γ₂)
    (h₃ : IsSideElement Γ τ₀ γ₃) {v : UpperHalfPlane}
    (hv₁ : v ∈ dirichletSideSet Γ τ₀ γ₁) (hv₂ : v ∈ dirichletSideSet Γ τ₀ γ₂)
    (hv₃ : v ∈ dirichletSideSet Γ τ₀ γ₃)
    (h12 : dirichletSideSet Γ τ₀ γ₁ ≠ dirichletSideSet Γ τ₀ γ₂)
    (h13 : dirichletSideSet Γ τ₀ γ₁ ≠ dirichletSideSet Γ τ₀ γ₃)
    (h23 : dirichletSideSet Γ τ₀ γ₂ ≠ dirichletSideSet Γ τ₀ γ₃) : False := by
  classical
  have hp12 : γ₁ • τ₀ ≠ γ₂ • τ₀ := fun hc => h12 (sideSet_eq_of_basepoint_eq hc)
  have hp13 : γ₁ • τ₀ ≠ γ₃ • τ₀ := fun hc => h13 (sideSet_eq_of_basepoint_eq hc)
  have hp23 : γ₂ • τ₀ ≠ γ₃ • τ₀ := fun hc => h23 (sideSet_eq_of_basepoint_eq hc)
  have hpick : ∀ γ : ↥Γ, (dirichletSideSet Γ τ₀ γ).Nontrivial →
      ∃ b ∈ dirichletSideSet Γ τ₀ γ, b ≠ v := by
    intro γ hnt
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    by_cases hxv : x = v
    · exact ⟨y, hy, fun h => hxy (hxv.trans h.symm)⟩
    · exact ⟨x, hx, hxv⟩
  obtain ⟨b₁, hb₁, hb₁v⟩ := hpick γ₁ h₁.2
  obtain ⟨b₂, hb₂, hb₂v⟩ := hpick γ₂ h₂.2
  obtain ⟨b₃, hb₃, hb₃v⟩ := hpick γ₃ h₃.2
  have hstrict : ∀ γa γb : ↥Γ, γa • τ₀ ≠ γb • τ₀ → γa • τ₀ ≠ τ₀ → γb • τ₀ ≠ τ₀ →
      dist v τ₀ = dist v (γa • τ₀) → dist v τ₀ = dist v (γb • τ₀) →
      ∀ b ∈ dirichletSideSet Γ τ₀ γa, b ≠ v → dist b τ₀ < dist b (γb • τ₀) := by
    intro γa γb hab ha hb hva hvb b hbmem hbv
    rcases lt_or_eq_of_le (hbmem.1 γb) with h | h
    · exact h
    · exact absurd (bisector_pair_unique (Ne.symm hbv) hva hbmem.2 hvb h ha hb) hab
  obtain ⟨g₁, ε₁, hε₁, hle₁, hge₁⟩ := bisector_normalizer (Ne.symm h₁.1)
  obtain ⟨g₂, ε₂, hε₂, hle₂, hge₂⟩ := bisector_normalizer (Ne.symm h₂.1)
  obtain ⟨g₃, ε₃, hε₃, hle₃, hge₃⟩ := bisector_normalizer (Ne.symm h₃.1)
  obtain ⟨m₁, hm₁, hf₁eq, hf₁lt⟩ := functional_sign hε₁ hle₁ hge₁ hv₁.2
  obtain ⟨m₂, hm₂, hf₂eq, hf₂lt⟩ := functional_sign hε₂ hle₂ hge₂ hv₂.2
  obtain ⟨m₃, hm₃, hf₃eq, hf₃lt⟩ := functional_sign hε₃ hle₃ hge₃ hv₃.2
  set d₁ : ℂ := discChart v b₁ with hd₁
  set d₂ : ℂ := discChart v b₂ with hd₂
  set d₃ : ℂ := discChart v b₃ with hd₃
  have hd₁ne : d₁ ≠ 0 := discChart_ne_zero hb₁v
  have hd₂ne : d₂ ≠ 0 := discChart_ne_zero hb₂v
  have hd₃ne : d₃ ≠ 0 := discChart_ne_zero hb₃v
  have hL11 : ε₁ * (m₁ * d₁).im = 0 := hf₁eq b₁ hb₁.2
  have hL22 : ε₂ * (m₂ * d₂).im = 0 := hf₂eq b₂ hb₂.2
  have hL33 : ε₃ * (m₃ * d₃).im = 0 := hf₃eq b₃ hb₃.2
  have hL12 : 0 < ε₂ * (m₂ * d₁).im :=
    hf₂lt b₁ (hstrict γ₁ γ₂ hp12 h₁.1 h₂.1 hv₁.2 hv₂.2 b₁ hb₁ hb₁v)
  have hL13 : 0 < ε₃ * (m₃ * d₁).im :=
    hf₃lt b₁ (hstrict γ₁ γ₃ hp13 h₁.1 h₃.1 hv₁.2 hv₃.2 b₁ hb₁ hb₁v)
  have hL21 : 0 < ε₁ * (m₁ * d₂).im :=
    hf₁lt b₂ (hstrict γ₂ γ₁ (Ne.symm hp12) h₂.1 h₁.1 hv₂.2 hv₁.2 b₂ hb₂ hb₂v)
  have hL23 : 0 < ε₃ * (m₃ * d₂).im :=
    hf₃lt b₂ (hstrict γ₂ γ₃ hp23 h₂.1 h₃.1 hv₂.2 hv₃.2 b₂ hb₂ hb₂v)
  have hL31 : 0 < ε₁ * (m₁ * d₃).im :=
    hf₁lt b₃ (hstrict γ₃ γ₁ (Ne.symm hp13) h₃.1 h₁.1 hv₃.2 hv₁.2 b₃ hb₃ hb₃v)
  have hL32 : 0 < ε₂ * (m₂ * d₃).im :=
    hf₂lt b₃ (hstrict γ₃ γ₂ (Ne.symm hp23) h₃.1 h₂.1 hv₃.2 hv₂.2 b₃ hb₃ hb₃v)
  have hlin : ∀ (m : ℂ) (e α β : ℝ) (ξ ζ : ℂ),
      e * (m * ((α : ℂ) * ξ + (β : ℂ) * ζ)).im
        = α * (e * (m * ξ).im) + β * (e * (m * ζ).im) := by
    intro m e α β ξ ζ
    have h1 : m * ((α : ℂ) * ξ + (β : ℂ) * ζ) = (α : ℂ) * (m * ξ) + (β : ℂ) * (m * ζ) := by
      ring
    rw [h1, Complex.add_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  have hΔne : d₁.re * d₂.im - d₁.im * d₂.re ≠ 0 := by
    intro hΔ0
    have hnsq : 0 < d₁.re * d₁.re + d₁.im * d₁.im := by
      have h4 := Complex.normSq_pos.mpr hd₁ne
      rwa [Complex.normSq_apply] at h4
    have hd₂eq : d₂ = (((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) : ℝ) : ℂ) * d₁ := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]
        rw [div_mul_eq_mul_div, eq_div_iff hnsq.ne']
        linear_combination -d₁.im * hΔ0
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]
        rw [div_mul_eq_mul_div, eq_div_iff hnsq.ne']
        linear_combination d₁.re * hΔ0
    have h4 : ε₂ * (m₂ * d₂).im = ((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im)) * (ε₂ * (m₂ * d₁).im) := by
      conv_lhs => rw [hd₂eq]
      have h5 := hlin m₂ ε₂ ((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im)) 0 d₁ 0
      rw [show ((0:ℝ) : ℂ) * (0 : ℂ) = 0 by ring] at h5
      rw [show (((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) : ℝ) : ℂ) * d₁ + 0
          = (((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) : ℝ) : ℂ) * d₁ by ring] at h5
      rw [h5]
      simp
    rw [hL22] at h4
    have hc0 : (d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) = 0 := by
      rcases mul_eq_zero.mp h4.symm with h | h
      · exact h
      · linarith
    rw [hc0] at hd₂eq
    push_cast at hd₂eq
    rw [zero_mul] at hd₂eq
    exact hd₂ne hd₂eq
  set α : ℝ := (d₃.re * d₂.im - d₃.im * d₂.re) / (d₁.re * d₂.im - d₁.im * d₂.re) with hα
  set β : ℝ := (d₁.re * d₃.im - d₁.im * d₃.re) / (d₁.re * d₂.im - d₁.im * d₂.re) with hβ
  have hdecomp : d₃ = (α : ℂ) * d₁ + (β : ℂ) * d₂ := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        eq_div_iff hΔne]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        eq_div_iff hΔne]
      ring
  have hE1 : ε₁ * (m₁ * d₃).im = α * (ε₁ * (m₁ * d₁).im) + β * (ε₁ * (m₁ * d₂).im) := by
    conv_lhs => rw [hdecomp]
    exact hlin m₁ ε₁ α β d₁ d₂
  have hE2 : ε₂ * (m₂ * d₃).im = α * (ε₂ * (m₂ * d₁).im) + β * (ε₂ * (m₂ * d₂).im) := by
    conv_lhs => rw [hdecomp]
    exact hlin m₂ ε₂ α β d₁ d₂
  have hE3 : ε₃ * (m₃ * d₃).im = α * (ε₃ * (m₃ * d₁).im) + β * (ε₃ * (m₃ * d₂).im) := by
    conv_lhs => rw [hdecomp]
    exact hlin m₃ ε₃ α β d₁ d₂
  rw [hL11] at hE1
  rw [hL22] at hE2
  rw [hL33] at hE3
  have hβpos : 0 < β := by
    by_contra hc
    push_neg at hc
    nlinarith [hL31, hL21, hE1]
  have hαneg : α < 0 := by
    by_contra hc
    push_neg at hc
    nlinarith [hL13, hL23, hE3]
  nlinarith [hL32, hL12, hE2]

/-- A positive radius within which any point of any side forces the side through `v`. -/
theorem exists_sep_radius (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (v : UpperHalfPlane) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ s ∈ polygonSides Γ τ₀, ∀ w ∈ s, dist w v < ρ₀ → v ∈ s := by
  classical
  have hfin : ({s ∈ polygonSides Γ τ₀ | v ∉ s}).Finite :=
    (finite_polygonSides hΓ hfree hε hgap hdense).subset (fun s hs => hs.1)
  have hpos : ∀ s ∈ {s ∈ polygonSides Γ τ₀ | v ∉ s}, 0 < Metric.infDist v s := by
    rintro s ⟨hs, hvs⟩
    obtain ⟨γ, ⟨hmove, hnt⟩, rfl⟩ := hs
    have hclosed : IsClosed (dirichletSideSet Γ τ₀ γ) :=
      (isClosed_dirichletDomain Γ τ₀).inter (isClosed_eq
        (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
    exact (hclosed.notMem_iff_infDist_pos hnt.nonempty).mp hvs
  rcases Set.eq_empty_or_nonempty {s ∈ polygonSides Γ τ₀ | v ∉ s} with hemp | hnem
  · refine ⟨1, one_pos, ?_⟩
    intro s hs w hw hd
    by_contra hvs
    have h1 : s ∈ {s ∈ polygonSides Γ τ₀ | v ∉ s} := ⟨hs, hvs⟩
    rw [hemp] at h1
    exact h1
  · obtain ⟨s₀, hs₀, hs₀min⟩ := Set.exists_min_image _
      (fun s => Metric.infDist v s) hfin hnem
    refine ⟨Metric.infDist v s₀, hpos s₀ hs₀, ?_⟩
    intro s hs w hw hd
    by_contra hvs
    have h1 : Metric.infDist v s₀ ≤ Metric.infDist v s := hs₀min s ⟨hs, hvs⟩
    have h2 : Metric.infDist v s ≤ dist v w := Metric.infDist_le_dist_of_mem hw
    rw [dist_comm v w] at h2
    linarith

set_option maxHeartbeats 400000 in
-- The two-sides extraction runs the frontier-accumulation, crossing, and three-sides
-- exclusion arguments in one declaration; the default heartbeat budget does not cover it.
/-- **Two sides per vertex**: each vertex is an endpoint of exactly two sides, the two
boundary rays of the local convex sector of the domain at the vertex. -/
theorem exists_two_sides_at_vertex (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) :
    ∃ s₁ ∈ polygonSides Γ τ₀, ∃ s₂ ∈ polygonSides Γ τ₀, s₁ ≠ s₂ ∧
      IsSegEndpoint s₁ v ∧ IsSegEndpoint s₂ v ∧
      ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v → s = s₁ ∨ s = s₂ := by
  classical
  obtain ⟨hvD, hv3⟩ := hv
  have hvint : v ∉ interior (dirichletDomain Γ τ₀) := by
    intro hcon
    have h1 : v ∈ ((1 : ↥Γ) • ·) '' interior (dirichletDomain Γ τ₀) :=
      ⟨v, hcon, one_smul _ _⟩
    rw [mem_smul_interior_iff_contactSet_eq hΓ hdense] at h1
    have h2 : tileCenters Γ τ₀ v ⊆ {τ₀} := by
      rintro c ⟨δ, hδ, rfl⟩
      rw [h1] at hδ
      have h3 : δ • τ₀ = (1 : ↥Γ) • τ₀ := hδ
      rw [one_smul] at h3
      exact h3
    have h3 := Set.ncard_le_ncard h2 (Set.finite_singleton τ₀)
    rw [Set.ncard_singleton] at h3
    omega
  have hvτ : v ≠ τ₀ := by
    intro h
    rw [h] at hvint
    exact hvint (basepoint_mem_interior_dirichletDomain hε hgap)
  obtain ⟨ρ₀, hρ₀, hsep⟩ := exists_sep_radius hΓ hfree hε hgap hdense v
  have hfr : ∀ ρ : ℝ, 0 < ρ → ∃ w, w ∈ frontier (dirichletDomain Γ τ₀) ∧ w ≠ v ∧
      dist w v < ρ := by
    intro ρ hρ
    by_contra hcon
    push_neg at hcon
    have hpre := isPreconnected_punctured_ball v ρ
    have hcover : Metric.ball v ρ \ {v} ⊆ interior (dirichletDomain Γ τ₀) ∪
        (dirichletDomain Γ τ₀)ᶜ := by
      rintro w ⟨hwB, hwne⟩
      have hwv : w ≠ v := fun h => hwne (by rw [h]; exact rfl)
      by_cases hwD : w ∈ dirichletDomain Γ τ₀
      · left
        have hwfr : w ∉ frontier (dirichletDomain Γ τ₀) := by
          intro hf
          exact absurd (Metric.mem_ball.mp hwB) (not_lt.mpr (hcon w hf hwv))
        rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hwfr
        by_cases hwint : w ∈ interior (dirichletDomain Γ τ₀)
        · exact hwint
        · exact absurd ⟨hwD, hwint⟩ hwfr
      · right
        exact hwD
    have hne1 : ((Metric.ball v ρ \ {v}) ∩ interior (dirichletDomain Γ τ₀)).Nonempty := by
      obtain ⟨w, hwseg, hwv, hwd⟩ := exists_near_on_geodSeg (Ne.symm hvτ) hρ
      exact ⟨w, ⟨Metric.mem_ball.mpr hwd, fun hc => hwv (Set.mem_singleton_iff.mp hc)⟩,
        mem_interior_of_mem_geodSeg hΓ hdense hvD hwseg hwv⟩
    have hne2 : ((Metric.ball v ρ \ {v}) ∩ (dirichletDomain Γ τ₀)ᶜ).Nonempty := by
      by_contra h2
      rw [Set.not_nonempty_iff_eq_empty] at h2
      have hball : Metric.ball v ρ ⊆ dirichletDomain Γ τ₀ := by
        intro y hy
        by_contra hyD
        by_cases hyv : y = v
        · rw [hyv] at hyD
          exact hyD hvD
        · have h4 : y ∈ (Metric.ball v ρ \ {v}) ∩ (dirichletDomain Γ τ₀)ᶜ :=
            ⟨⟨hy, fun hc => hyv (Set.mem_singleton_iff.mp hc)⟩, hyD⟩
          rw [h2] at h4
          exact h4
      exact hvint (interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hρ))
    obtain ⟨z0, hz0⟩ := hpre (interior (dirichletDomain Γ τ₀)) (dirichletDomain Γ τ₀)ᶜ
      isOpen_interior (isClosed_dirichletDomain Γ τ₀).isOpen_compl hcover hne1 hne2
    exact hz0.2.2 (interior_subset hz0.2.1)
  obtain ⟨w₁, hw₁fr, hw₁v, hw₁d⟩ := hfr ρ₀ hρ₀
  have hw₁un : w₁ ∈ ⋃₀ polygonSides Γ τ₀ := by
    rw [← frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
    exact hw₁fr
  obtain ⟨s₁, hs₁mem, hw₁s⟩ := hw₁un
  have hvs₁ : v ∈ s₁ := hsep s₁ hs₁mem w₁ hw₁s hw₁d
  have hend₁ : IsSegEndpoint s₁ v :=
    isSegEndpoint_of_vertex hΓ hfree hε hgap hdense ⟨hvD, hv3⟩ hs₁mem hvs₁
  obtain ⟨a, b, hab, hs₁eq⟩ :=
    exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs₁mem
  obtain ⟨e₁, he₁v, hs₁eq'⟩ : ∃ e₁ : UpperHalfPlane, e₁ ≠ v ∧ s₁ = geodSeg v e₁ := by
    have hend' : IsSegEndpoint (geodSeg a b) v := by rw [← hs₁eq]; exact hend₁
    rcases (isSegEndpoint_geodSeg_iff hab).mp hend' with h | h
    · refine ⟨b, ?_, by rw [hs₁eq, ← h]⟩
      intro hc
      rw [← h] at hab
      exact hab (hc.symm ▸ rfl)
    · refine ⟨a, ?_, by rw [hs₁eq, ← h, geodSeg_comm]⟩
      intro hc
      rw [← h] at hab
      exact hab (hc ▸ rfl)
  obtain ⟨γ₁, hγ₁elem, hs₁def⟩ := hs₁mem
  have hvseq : dist v τ₀ = dist v (γ₁ • τ₀) := by
    have h5 : v ∈ dirichletSideSet Γ τ₀ γ₁ := by rw [← hs₁def]; exact hvs₁
    exact h5.2
  have he₁seq : dist e₁ τ₀ = dist e₁ (γ₁ • τ₀) := by
    have h5 : e₁ ∈ dirichletSideSet Γ τ₀ γ₁ := by
      rw [← hs₁def, hs₁eq']
      exact right_mem_geodSeg v e₁
    exact h5.2
  obtain ⟨wb, hwb_eq, hwb_dist, hwb_between⟩ := exists_beyond
    (Ne.symm hγ₁elem.1) hvseq he₁seq (Ne.symm he₁v)
    (show (0:ℝ) < ρ₀ / 4 by linarith)
  have hwbD : wb ∉ dirichletDomain Γ τ₀ := by
    intro hwbDmem
    have hwbside : wb ∈ geodSeg v e₁ := by
      rw [← hs₁eq', hs₁def]
      exact ⟨hwbDmem, hwb_eq⟩
    have hEnd := (isSegEndpoint_geodSeg_iff (Ne.symm he₁v)).mpr (Or.inl rfl)
    rcases hEnd.2 wb hwbside e₁ (right_mem_geodSeg v e₁) hwb_between with h4 | h4
    · rw [← h4, dist_self] at hwb_dist
      linarith
    · exact he₁v h4.symm
  obtain ⟨xi, hxiseg, hxiv, hxid⟩ := exists_near_on_geodSeg (Ne.symm hvτ)
    (show (0:ℝ) < ρ₀ / 4 by linarith)
  have hxiint : xi ∈ interior (dirichletDomain Γ τ₀) :=
    mem_interior_of_mem_geodSeg hΓ hdense hvD hxiseg hxiv
  have hxiD : xi ∈ dirichletDomain Γ τ₀ := interior_subset hxiint
  have hxioff : dist xi τ₀ ≠ dist xi (γ₁ • τ₀) := by
    rw [interior_dirichletDomain_eq hΓ hdense] at hxiint
    exact ne_of_lt (hxiint γ₁ hγ₁elem.1)
  obtain ⟨w₂, hw₂seg, hw₂fr⟩ := exists_frontier_mem_geodSeg hxiD hwbD
  have hw₂D : w₂ ∈ dirichletDomain Γ τ₀ := by
    rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hw₂fr
    exact hw₂fr.1
  have hw₂wb : w₂ ≠ wb := fun h => hwbD (h ▸ hw₂D)
  have hw₂off : dist w₂ τ₀ ≠ dist w₂ (γ₁ • τ₀) := by
    intro hw₂eq
    obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer (Ne.symm hγ₁elem.1)
    have hgwb : (g • wb).re = 0 := normalizer_re_eq_zero hε' hle hge hwb_eq
    have hgw₂ : (g • w₂).re = 0 := normalizer_re_eq_zero hε' hle hge hw₂eq
    by_cases hAB : (g • xi).re = (g • wb).re
    · refine hxioff ((normalizer_eq_iff hε' hle hge xi).mpr ?_)
      rw [hAB, hgwb]
    · have hseg' : g • w₂ ∈ geodSeg (g • xi) (g • wb) := by
        rw [← smul_geodSeg]
        exact ⟨w₂, hw₂seg, rfl⟩
      have h5 := eq_of_re_eq_of_mem_geodSeg hAB hseg' (right_mem_geodSeg _ _)
        (by rw [hgw₂, hgwb])
      exact hw₂wb (smul_left_cancel g h5)
  have hw₂s₁ : w₂ ∉ s₁ := by
    intro hcon
    have h5 : w₂ ∈ dirichletSideSet Γ τ₀ γ₁ := by rw [← hs₁def]; exact hcon
    exact hw₂off h5.2
  have hw₂d : dist w₂ v < ρ₀ := by
    have h5 : dist xi w₂ + dist w₂ wb = dist xi wb := hw₂seg
    have hd1 : dist xi w₂ ≤ dist xi wb := by
      linarith [dist_nonneg (x := w₂) (y := wb)]
    have hd2 : dist xi wb ≤ dist xi v + dist v wb := dist_triangle _ _ _
    have hd3 : dist w₂ v ≤ dist w₂ xi + dist xi v := dist_triangle _ _ _
    have h6 : dist xi v < ρ₀ / 4 := hxid
    have h7 : dist v wb = ρ₀ / 4 := by rw [dist_comm]; exact hwb_dist
    have h8 : dist w₂ xi = dist xi w₂ := dist_comm _ _
    linarith
  have hw₂un : w₂ ∈ ⋃₀ polygonSides Γ τ₀ := by
    rw [← frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
    exact hw₂fr
  obtain ⟨s₂, hs₂mem, hw₂s₂⟩ := hw₂un
  have hvs₂ : v ∈ s₂ := hsep s₂ hs₂mem w₂ hw₂s₂ hw₂d
  have hs₁₂ : s₁ ≠ s₂ := fun h => hw₂s₁ (h ▸ hw₂s₂)
  have hend₂ : IsSegEndpoint s₂ v :=
    isSegEndpoint_of_vertex hΓ hfree hε hgap hdense ⟨hvD, hv3⟩ hs₂mem hvs₂
  refine ⟨s₁, ⟨γ₁, hγ₁elem, hs₁def⟩, s₂, hs₂mem, hs₁₂, hend₁, hend₂, ?_⟩
  intro s hs hsend
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne₁, hne₂⟩ := hcon
  obtain ⟨γs, hγselem, hsdef⟩ := hs
  obtain ⟨γ₂', hγ₂elem, hs₂def⟩ := hs₂mem
  refine not_three_sides hγ₁elem hγ₂elem hγselem
    (v := v) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hs₁def]; exact hvs₁
  · rw [← hs₂def]; exact hvs₂
  · rw [← hsdef]; exact hsend.1
  · rw [← hs₁def, ← hs₂def]; exact hs₁₂
  · rw [← hs₁def, ← hsdef]; exact Ne.symm hne₁
  · rw [← hs₂def, ← hsdef]; exact Ne.symm hne₂

#print axioms finite_polygonSides
#print axioms finite_polygonVertices
#print axioms smul_basepoint_eq_of_sideSet_eq
#print axioms exists_geodSeg_of_polygonSide
#print axioms mem_polygonVertices_of_sideSet_eq_singleton
#print axioms frontier_dirichletDomain_eq_sUnion
#print axioms mem_polygonVertices_of_isSegEndpoint
#print axioms exists_two_sides_at_vertex


variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

theorem contact_shift (g δ : ↥Γ) (z : UpperHalfPlane) :
    δ ∈ contactSet Γ τ₀ z ↔ (g * δ) ∈ contactSet Γ τ₀ (g • z) := by
  rw [mem_contactSet_iff_mem_smul_dirichletDomain,
    mem_contactSet_iff_mem_smul_dirichletDomain]
  constructor
  · rintro ⟨u, hu, huz⟩
    refine ⟨u, hu, ?_⟩
    show (g * δ) • u = g • z
    rw [mul_smul]
    exact congrArg (g • ·) huz
  · rintro ⟨u, hu, huz⟩
    refine ⟨u, hu, ?_⟩
    have h1 : g • δ • u = g • z := by
      rw [← mul_smul]
      exact huz
    exact smul_left_cancel g h1

theorem inv_smul_eq_of_basepoint_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ γ' : ↥Γ} (h : γ • τ₀ = γ' • τ₀) (w : UpperHalfPlane) : γ⁻¹ • w = γ'⁻¹ • w := by
  have h1 : γ • γ'⁻¹ • w = γ' • γ'⁻¹ • w := smul_eq_of_basepoint_eq hfree h (γ'⁻¹ • w)
  rw [smul_inv_smul] at h1
  conv_lhs => rw [← h1]
  rw [inv_smul_smul]

theorem transition_basepoint_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ γ' δ δ' : ↥Γ} (hγ : γ • τ₀ = γ' • τ₀) (hδ : δ • τ₀ = δ' • τ₀) :
    (γ⁻¹ * δ) • τ₀ = (γ'⁻¹ * δ') • τ₀ := by
  rw [mul_smul, mul_smul, hδ]
  exact inv_smul_eq_of_basepoint_eq hfree hγ (δ' • τ₀)

theorem isSideElement_congr {β β' : ↥Γ} (h : β • τ₀ = β' • τ₀) :
    IsSideElement Γ τ₀ β ↔ IsSideElement Γ τ₀ β' := by
  unfold IsSideElement
  rw [h, sideSet_eq_of_basepoint_eq h]

theorem smul_basepoint_ne {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {γ : ↥Γ} (hγ : γ ∈ contactSet Γ τ₀ v) : γ • τ₀ ≠ v := by
  intro h
  have h1 : dist v (γ • τ₀) = Metric.infDist v (MulAction.orbit Γ τ₀) := hγ
  rw [h, dist_self] at h1
  have hsub : tileCenters Γ τ₀ v ⊆ {v} := by
    rintro c ⟨δ, hδ, rfl⟩
    have h3 : dist v (δ • τ₀) = Metric.infDist v (MulAction.orbit Γ τ₀) := hδ
    rw [← h1] at h3
    simp only [Set.mem_singleton_iff]
    exact (dist_eq_zero.mp h3).symm
  have h4 := Set.ncard_le_ncard hsub (Set.finite_singleton v)
  rw [Set.ncard_singleton] at h4
  have h5 : 3 ≤ (tileCenters Γ τ₀ v).ncard := hv.2
  omega

theorem tileCenters_smul {v : UpperHalfPlane} (γ : ↥Γ) :
    tileCenters Γ τ₀ (γ⁻¹ • v) = (γ⁻¹ • ·) '' tileCenters Γ τ₀ v := by
  ext c
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    have h1 : (γ * δ) ∈ contactSet Γ τ₀ (γ • γ⁻¹ • v) := (contact_shift γ δ _).mp hδ
    rw [smul_inv_smul] at h1
    refine ⟨(γ * δ) • τ₀, ⟨γ * δ, h1, rfl⟩, ?_⟩
    show γ⁻¹ • (γ * δ) • τ₀ = δ • τ₀
    rw [mul_smul, inv_smul_smul]
  · rintro ⟨c', ⟨δ, hδ, rfl⟩, rfl⟩
    refine ⟨γ⁻¹ * δ, (contact_shift γ⁻¹ δ v).mp hδ, ?_⟩
    show (γ⁻¹ * δ) • τ₀ = γ⁻¹ • δ • τ₀
    rw [mul_smul]

theorem smul_mem_polygonVertices {v : UpperHalfPlane}
    (hv : v ∈ polygonVertices Γ τ₀) {γ : ↥Γ} (hγ : γ ∈ contactSet Γ τ₀ v) :
    γ⁻¹ • v ∈ polygonVertices Γ τ₀ := by
  obtain ⟨u, huD, huv⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain γ v).mp hγ
  have huv' : γ • u = v := huv
  refine ⟨?_, ?_⟩
  · rw [← huv', inv_smul_smul]
    exact huD
  · rw [tileCenters_smul γ,
      Set.ncard_image_of_injective _ (fun a b h => smul_left_cancel γ⁻¹ h)]
    exact hv.2

theorem two_neighbors (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {rep : UpperHalfPlane → ↥Γ}
    (hrep₁ : ∀ p ∈ tileCenters Γ τ₀ v, rep p ∈ contactSet Γ τ₀ v)
    (hrep₂ : ∀ p ∈ tileCenters Γ τ₀ v, rep p • τ₀ = p)
    {p : UpperHalfPlane} (hp : p ∈ tileCenters Γ τ₀ v) :
    ∃ q₁ ∈ tileCenters Γ τ₀ v, ∃ q₂ ∈ tileCenters Γ τ₀ v, q₁ ≠ q₂ ∧
      ∀ q ∈ tileCenters Γ τ₀ v,
        (IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) ↔ q = q₁ ∨ q = q₂) := by
  have hγC : rep p ∈ contactSet Γ τ₀ v := hrep₁ p hp
  have hvγ : (rep p)⁻¹ • v ∈ polygonVertices Γ τ₀ := smul_mem_polygonVertices hv hγC
  have hvγD : (rep p)⁻¹ • v ∈ dirichletDomain Γ τ₀ := hvγ.1
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂, hend₁, hend₂, huniq⟩ :=
    exists_two_sides_at_vertex hΓ hfree hε hgap hdense hvγ
  obtain ⟨β₁, hβ₁elem, hs₁def⟩ := hs₁
  obtain ⟨β₂, hβ₂elem, hs₂def⟩ := hs₂
  have hβ₁v : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β₁ := by
    rw [← hs₁def]; exact hend₁.1
  have hβ₂v : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β₂ := by
    rw [← hs₂def]; exact hend₂.1
  have hmk : ∀ β : ↥Γ, (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β →
      (rep p * β) • τ₀ ∈ tileCenters Γ τ₀ v := by
    intro β hβv
    have hβcon := mem_contactSet_of_mem_sideSet hβv
    have h1 := (contact_shift (rep p) β ((rep p)⁻¹ • v)).mp hβcon
    rw [smul_inv_smul] at h1
    exact ⟨rep p * β, h1, rfl⟩
  have hforw : ∀ β : ↥Γ, IsSideElement Γ τ₀ β →
      ∀ q ∈ tileCenters Γ τ₀ v, IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) →
      dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) = dirichletSideSet Γ τ₀ β →
      q = (rep p * β) • τ₀ := by
    intro β hβelem q hq hSide heq
    have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree hSide hβelem heq
    calc q = rep q • τ₀ := (hrep₂ q hq).symm
      _ = rep p • (((rep p)⁻¹ * rep q) • τ₀) := by rw [mul_smul, smul_inv_smul]
      _ = rep p • (β • τ₀) := by rw [h1]
      _ = (rep p * β) • τ₀ := (mul_smul _ _ _).symm
  have hback : ∀ β : ↥Γ, IsSideElement Γ τ₀ β → (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β →
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep ((rep p * β) • τ₀)) := by
    intro β hβelem hβv'
    have hqP := hmk β hβv'
    have h2 : rep ((rep p * β) • τ₀) • τ₀ = (rep p * β) • τ₀ := hrep₂ _ hqP
    have h3 := transition_basepoint_eq hfree (rfl : rep p • τ₀ = rep p • τ₀) h2
    rw [inv_mul_cancel_left] at h3
    exact (isSideElement_congr h3).mpr hβelem
  refine ⟨(rep p * β₁) • τ₀, hmk β₁ hβ₁v, (rep p * β₂) • τ₀, hmk β₂ hβ₂v, ?_, ?_⟩
  · intro h
    have h1 : β₁ • τ₀ = β₂ • τ₀ := by
      have h2 : rep p • (β₁ • τ₀) = rep p • (β₂ • τ₀) := by
        rw [← mul_smul, ← mul_smul]
        exact h
      exact smul_left_cancel _ h2
    exact hs₁₂ (by rw [hs₁def, hs₂def, sideSet_eq_of_basepoint_eq h1])
  · intro q hq
    constructor
    · intro hSide
      have hβq := (contact_shift (rep p)⁻¹ (rep q) v).mp (hrep₁ q hq)
      have hvs : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) :=
        mem_sideSet_of_contact hvγD hβq
      have hmemS : dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) ∈ polygonSides Γ τ₀ :=
        ⟨_, hSide, rfl⟩
      have hendS := isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hvγ hmemS hvs
      rcases huniq _ hmemS hendS with h | h
      · exact Or.inl (hforw β₁ hβ₁elem q hq hSide (by rw [h, hs₁def]))
      · exact Or.inr (hforw β₂ hβ₂elem q hq hSide (by rw [h, hs₂def]))
    · rintro (rfl | rfl)
      · exact hback β₁ hβ₁elem hβ₁v
      · exact hback β₂ hβ₂elem hβ₂v

theorem adj_closed_eq (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {rep : UpperHalfPlane → ↥Γ}
    (hrep₁ : ∀ p ∈ tileCenters Γ τ₀ v, rep p ∈ contactSet Γ τ₀ v)
    (hrep₂ : ∀ p ∈ tileCenters Γ τ₀ v, rep p • τ₀ = p)
    {S : Set UpperHalfPlane} (hSsub : S ⊆ tileCenters Γ τ₀ v) (hSne : S.Nonempty)
    (hclosed : ∀ p ∈ S, ∀ q ∈ tileCenters Γ τ₀ v,
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) → q ∈ S) :
    S = tileCenters Γ τ₀ v := by
  classical
  by_contra hne
  have hTne : (tileCenters Γ τ₀ v \ S).Nonempty :=
    Set.diff_nonempty.mpr (fun h => hne (hSsub.antisymm h))
  obtain ⟨r, hr, hmeets, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ v
  have hPfin : (tileCenters Γ τ₀ v).Finite := (finite_contactSet hΓ τ₀ v).image _
  have hAcl : IsClosed (⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) :=
    Set.Finite.isClosed_biUnion (hPfin.subset hSsub) (fun p _ => isClosed_tile _)
  have hBcl : IsClosed (⋃ p ∈ tileCenters Γ τ₀ v \ S,
      (rep p • ·) '' dirichletDomain Γ τ₀) :=
    Set.Finite.isClosed_biUnion hPfin.diff (fun p _ => isClosed_tile _)
  have hcov : Metric.ball v r \ {v} ⊆ (⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∪
      ⋃ p ∈ tileCenters Γ τ₀ v \ S, (rep p • ·) '' dirichletDomain Γ τ₀ := by
    rintro w ⟨hwB, -⟩
    obtain ⟨δ, hδ, hδw⟩ := hcover w hwB
    have hδP : δ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨δ, hδ, rfl⟩
    have htile : (δ • ·) '' dirichletDomain Γ τ₀
        = (rep (δ • τ₀) • ·) '' dirichletDomain Γ τ₀ :=
      smul_image_eq_of_basepoint_eq hfree (hrep₂ _ hδP).symm
    rw [htile] at hδw
    by_cases hmem : δ • τ₀ ∈ S
    · exact Or.inl (Set.mem_biUnion hmem hδw)
    · exact Or.inr (Set.mem_biUnion ⟨hδP, hmem⟩ hδw)
  have hdisj : (⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∩
      (⋃ p ∈ tileCenters Γ τ₀ v \ S, (rep p • ·) '' dirichletDomain Γ τ₀) ⊆ {v} := by
    rintro w ⟨hwA, hwB'⟩
    obtain ⟨p, hpS, hwp⟩ := Set.mem_iUnion₂.mp hwA
    obtain ⟨q, hqT, hwq⟩ := Set.mem_iUnion₂.mp hwB'
    by_contra hwv
    have hpq : p ≠ q := fun h => hqT.2 (h ▸ hpS)
    have hγ := hrep₁ p (hSsub hpS)
    have hδ := hrep₁ q hqT.1
    obtain ⟨u, huD, huw⟩ := hwp
    obtain ⟨u', hu'D, hu'w⟩ := hwq
    have h1 : (rep p)⁻¹ • w ∈ dirichletDomain Γ τ₀ := by
      have h1' : (rep p)⁻¹ • w = u := by rw [← huw]; exact inv_smul_smul _ _
      rw [h1']
      exact huD
    have h2 : (rep p)⁻¹ • w ∈ (((rep p)⁻¹ * rep q) • ·) '' dirichletDomain Γ τ₀ := by
      refine ⟨u', hu'D, ?_⟩
      show ((rep p)⁻¹ * rep q) • u' = (rep p)⁻¹ • w
      rw [mul_smul]
      exact congrArg ((rep p)⁻¹ • ·) hu'w
    have h3 : (rep p)⁻¹ • w ∈ dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) :=
      inter_smul_subset_sideSet _ ⟨h1, h2⟩
    have h4 : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) :=
      smul_mem_dirichletSideSet_of_contact_pair hγ hδ
    have h5 : ((rep p)⁻¹ * rep q) • τ₀ ≠ τ₀ := by
      intro h
      apply hpq
      have h6 : rep q • τ₀ = rep p • τ₀ := by
        calc rep q • τ₀ = rep p • (((rep p)⁻¹ * rep q) • τ₀) := by
              rw [mul_smul, smul_inv_smul]
          _ = rep p • τ₀ := by rw [h]
      rw [← hrep₂ p (hSsub hpS), ← hrep₂ q hqT.1, h6]
    have h8 : (rep p)⁻¹ • w ≠ (rep p)⁻¹ • v := by
      intro h
      exact hwv (Set.mem_singleton_iff.mpr (smul_left_cancel _ h))
    have hSide : IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) :=
      ⟨h5, (rep p)⁻¹ • w, h3, (rep p)⁻¹ • v, h4, h8⟩
    exact hqT.2 (hclosed p hpS q hqT.1 hSide)
  have hAne : ((⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∩
      (Metric.ball v r \ {v})).Nonempty := by
    obtain ⟨p, hpS⟩ := hSne
    have hne' : rep p • τ₀ ≠ v := smul_basepoint_ne hv (hrep₁ p (hSsub hpS))
    obtain ⟨w, hwseg, hwv, hwd⟩ := exists_near_on_geodSeg hne' hr
    exact ⟨w, Set.mem_biUnion hpS
        (geodSeg_center_subset_tile (hrep₁ p (hSsub hpS)) hwseg),
      Metric.mem_ball.mpr hwd, fun hc => hwv (Set.mem_singleton_iff.mp hc)⟩
  have hBne : ((⋃ p ∈ tileCenters Γ τ₀ v \ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∩
      (Metric.ball v r \ {v})).Nonempty := by
    obtain ⟨p, hpT⟩ := hTne
    have hne' : rep p • τ₀ ≠ v := smul_basepoint_ne hv (hrep₁ p hpT.1)
    obtain ⟨w, hwseg, hwv, hwd⟩ := exists_near_on_geodSeg hne' hr
    exact ⟨w, Set.mem_biUnion hpT (geodSeg_center_subset_tile (hrep₁ p hpT.1) hwseg),
      Metric.mem_ball.mpr hwd, fun hc => hwv (Set.mem_singleton_iff.mp hc)⟩
  exact punctured_ball_two_closed hr hAcl hBcl hcov hdisj hAne hBne

theorem cycle_of_two_regular {α : Type*} {P : Set α} {A : α → α → Prop}
    (hfin : P.Finite) (hne : P.Nonempty)
    (hmem : ∀ p q, A p q → p ∈ P ∧ q ∈ P)
    (hsymm : ∀ p q, A p q → A q p)
    (hirr : ∀ p q, A p q → p ≠ q)
    (htwo : ∀ p ∈ P, ∃ q₁ ∈ P, ∃ q₂ ∈ P, q₁ ≠ q₂ ∧
      ∀ q ∈ P, (A p q ↔ q = q₁ ∨ q = q₂))
    (hconn : ∀ S : Set α, S ⊆ P → S.Nonempty →
      (∀ p ∈ S, ∀ q, A p q → q ∈ S) → S = P) :
    ∃ (n : ℕ) (e : ℕ → α), 3 ≤ n ∧ (∀ k, e (k + n) = e k) ∧ (∀ k, e k ∈ P) ∧
      (∀ q ∈ P, ∃! k, k < n ∧ e k = q) ∧ ∀ k, A (e k) (e (k + 1)) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  haveI : Nonempty α := ⟨p₀⟩
  choose! nb₁ hnb₁ nb₂ hnb₂ hnb hiff using htwo
  obtain ⟨F, hF⟩ : ∃ F : α → α → α,
      ∀ p q, F p q = if nb₁ q = p then nb₂ q else nb₁ q := ⟨_, fun _ _ => rfl⟩
  have hFmem : ∀ p q, q ∈ P → F p q ∈ P := by
    intro p q hq
    rw [hF]
    split_ifs
    · exact hnb₂ q hq
    · exact hnb₁ q hq
  have hFne : ∀ p q, q ∈ P → F p q ≠ p := by
    intro p q hq
    rw [hF]
    split_ifs with h
    · rw [← h]
      exact (hnb q hq).symm
    · exact h
  have hFadj : ∀ p q, q ∈ P → A q (F p q) := by
    intro p q hq
    rw [hF]
    split_ifs
    · exact (hiff q hq _ (hnb₂ q hq)).mpr (Or.inr rfl)
    · exact (hiff q hq _ (hnb₁ q hq)).mpr (Or.inl rfl)
  have hFuniq : ∀ p q x, q ∈ P → A q p → A q x → x ≠ p → x = F p q := by
    intro p q x hq hp hx hxp
    have h1 := (hiff q hq p (hmem q p hp).2).mp hp
    have h2 := (hiff q hq x (hmem q x hx).2).mp hx
    rw [hF]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h2.trans h1.symm) hxp
    · rw [if_pos h1.symm]
      exact h2
    · have hng : ¬ nb₁ q = p := by
        rw [h1]
        exact hnb q hq
      rw [if_neg hng]
      exact h2
    · exact absurd (h2.trans h1.symm) hxp
  have hFinvol : ∀ p q, q ∈ P → A q p → F (F p q) q = p := by
    intro p q hq hp
    exact (hFuniq (F p q) q p hq (hFadj p q hq) hp (fun h => hFne p q hq h.symm)).symm
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → α × α, g 0 = (p₀, nb₁ p₀) ∧
      ∀ k, g (k + 1) = ((g k).2, F (g k).1 (g k).2) :=
    ⟨fun k => Nat.rec (p₀, nb₁ p₀) (fun _ gk => (gk.2, F gk.1 gk.2)) k, rfl, fun _ => rfl⟩
  obtain ⟨pp, hppdef⟩ : ∃ pp : ℕ → α, pp = fun k => (g k).1 := ⟨_, rfl⟩
  have hpp0 : ∀ k, pp k = (g k).1 := fun k => by simp only [hppdef]
  have hpp1 : ∀ k, pp (k + 1) = (g k).2 := by
    intro k
    rw [hpp0 (k + 1), hgs k]
  have hpp2 : ∀ k, pp (k + 2) = F (pp k) (pp (k + 1)) := by
    intro k
    rw [show k + 2 = k + 1 + 1 by omega, hpp1 (k + 1), hgs k, hpp0 k, hpp1 k]
  have hstep : ∀ k, pp k ∈ P ∧ A (pp k) (pp (k + 1)) := by
    intro k
    induction k with
    | zero =>
      constructor
      · rw [hpp0 0, hg0]
        exact hp₀
      · rw [hpp0 0, hpp1 0, hg0]
        exact (hiff p₀ hp₀ _ (hnb₁ p₀ hp₀)).mpr (Or.inl rfl)
    | succ k ih =>
      have hk1P : pp (k + 1) ∈ P := (hmem _ _ ih.2).2
      refine ⟨hk1P, ?_⟩
      rw [hpp2 k]
      exact hFadj (pp k) (pp (k + 1)) hk1P
  have hppP : ∀ k, pp k ∈ P := fun k => (hstep k).1
  have hadj : ∀ k, A (pp k) (pp (k + 1)) := fun k => (hstep k).2
  have hne2 : ∀ k, pp (k + 2) ≠ pp k := by
    intro k
    rw [hpp2 k]
    exact hFne (pp k) (pp (k + 1)) (hppP (k + 1))
  obtain ⟨a, b, hab, hgab⟩ : ∃ a b : ℕ, a < b ∧ g a = g b := by
    refine Set.Finite.exists_lt_map_eq_of_forall_mem (f := g) (t := P ×ˢ P) ?_
      (hfin.prod hfin)
    intro k
    rw [Set.mem_prod]
    exact ⟨hpp0 k ▸ hppP k, hpp1 k ▸ hppP (k + 1)⟩
  have hfwd : ∀ k l, g k = g l → ∀ j, g (k + j) = g (l + j) := by
    intro k l h j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [← Nat.add_assoc, ← Nat.add_assoc, hgs (k + j), hgs (l + j), ih]
  have hbwd : ∀ k l, g (k + 1) = g (l + 1) → g k = g l := by
    intro k l h
    rw [hgs k, hgs l] at h
    have h2 : (g k).2 = (g l).2 := congrArg Prod.fst h
    have h3 : F (g k).1 (g k).2 = F (g l).1 (g l).2 := congrArg Prod.snd h
    have h4 : A ((g k).2) ((g k).1) := by
      have h4' := hsymm _ _ (hadj k)
      rwa [hpp0 k, hpp1 k] at h4'
    have h5 : A ((g l).2) ((g l).1) := by
      have h5' := hsymm _ _ (hadj l)
      rwa [hpp0 l, hpp1 l] at h5'
    have hkP : (g k).2 ∈ P := by
      rw [← hpp1 k]
      exact hppP (k + 1)
    have hlP : (g l).2 ∈ P := by
      rw [← hpp1 l]
      exact hppP (l + 1)
    have h6 : (g k).1 = (g l).1 := by
      have e1 : F (F (g k).1 (g k).2) ((g k).2) = (g k).1 := hFinvol _ _ hkP h4
      have e2 : F (F (g l).1 (g l).2) ((g l).2) = (g l).1 := hFinvol _ _ hlP h5
      rw [← e1, ← e2, h3, h2]
    exact Prod.ext h6 h2
  have hback : ∀ i k l, g (k + i) = g (l + i) → g k = g l := by
    intro i
    induction i with
    | zero => intro k l h; exact h
    | succ i ih =>
      intro k l h
      refine ih k l (hbwd (k + i) (l + i) ?_)
      have e1 : k + i + 1 = k + (i + 1) := by omega
      have e2 : l + i + 1 = l + (i + 1) := by omega
      rw [e1, e2]
      exact h
  have hex : ∃ m, 0 < m ∧ g m = g 0 := by
    refine ⟨b - a, by omega, hback a (b - a) 0 ?_⟩
    rw [show b - a + a = b by omega, show 0 + a = a by omega]
    exact hgab.symm
  obtain ⟨n, ⟨hnpos, hgn⟩, hnmin⟩ : ∃ n : ℕ, (0 < n ∧ g n = g 0) ∧
      ∀ m : ℕ, 0 < m → g m = g 0 → n ≤ m := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro m hm hgm
    exact Nat.find_le ⟨hm, hgm⟩
  have hper : ∀ k, g (k + n) = g k := by
    intro k
    have h := hfwd n 0 hgn k
    rwa [show n + k = k + n by omega, show 0 + k = k by omega] at h
  have hpper : ∀ k, pp (k + n) = pp k := by
    intro k
    rw [hpp0 (k + n), hpp0 k, hper k]
  have hpermul : ∀ m k, pp (k + m * n) = pp k := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      rw [show k + (m + 1) * n = k + m * n + n by ring, hpper (k + m * n), ih k]
  have hnbrs : ∀ k x, 1 ≤ k → A (pp k) x → x = pp (k - 1) ∨ x = pp (k + 1) := by
    intro k x hk hx
    have hxP := (hmem _ _ hx).2
    have h1 : A (pp k) (pp (k + 1)) := hadj k
    have h2 : A (pp k) (pp (k - 1)) := by
      have h2' := hsymm _ _ (hadj (k - 1))
      rwa [show k - 1 + 1 = k by omega] at h2'
    have h3 : pp (k + 1) ≠ pp (k - 1) := by
      have h4 := hne2 (k - 1)
      rwa [show k - 1 + 2 = k + 1 by omega] at h4
    have e1 := (hiff (pp k) (hppP k) x hxP).mp hx
    have e2 := (hiff (pp k) (hppP k) _ (hppP (k + 1))).mp h1
    have e3 := (hiff (pp k) (hppP k) _ (hppP (k - 1))).mp h2
    rcases e2 with h5 | h5 <;> rcases e3 with h6 | h6
    · exact absurd (h5.trans h6.symm) h3
    · rcases e1 with h7 | h7
      · exact Or.inr (h7.trans h5.symm)
      · exact Or.inl (h7.trans h6.symm)
    · rcases e1 with h7 | h7
      · exact Or.inl (h7.trans h6.symm)
      · exact Or.inr (h7.trans h5.symm)
    · exact absurd (h5.trans h6.symm) h3
  have hppb : ∀ m, pp m = F (pp (m + 2)) (pp (m + 1)) := by
    intro m
    have hp' : A (pp (m + 1)) (pp (m + 2)) := by
      have h := hadj (m + 1)
      rwa [show m + 1 + 1 = m + 2 by omega] at h
    exact hFuniq _ _ _ (hppP (m + 1)) hp' (hsymm _ _ (hadj m)) (hne2 m).symm
  have hrev : ∀ I J, pp I = pp J → pp (I + 1) = pp (J - 1) →
      ∀ k, k + 1 ≤ J → pp (I + k) = pp (J - k) ∧ pp (I + k + 1) = pp (J - k - 1) := by
    intro I J h0 h1 k
    induction k with
    | zero =>
      intro _
      constructor
      · rw [show I + 0 = I by omega, show J - 0 = J by omega]
        exact h0
      · rw [show I + 0 + 1 = I + 1 by omega, show J - 0 - 1 = J - 1 by omega]
        exact h1
    | succ k ih =>
      intro hk
      obtain ⟨ha', hb'⟩ := ih (by omega)
      have hfirst : pp (I + (k + 1)) = pp (J - (k + 1)) := by
        rw [show I + (k + 1) = I + k + 1 by omega, show J - (k + 1) = J - k - 1 by omega]
        exact hb'
      refine ⟨hfirst, ?_⟩
      have hf : pp (I + k + 2) = F (pp (I + k)) (pp (I + k + 1)) := hpp2 (I + k)
      have hbk : pp (J - k - 2) = F (pp (J - k)) (pp (J - k - 1)) := by
        have h2 := hppb (J - k - 2)
        rwa [show J - k - 2 + 2 = J - k by omega,
          show J - k - 2 + 1 = J - k - 1 by omega] at h2
      have hmain : pp (I + k + 2) = pp (J - k - 2) := by
        rw [hf, hbk, ha', hb']
      rwa [show I + k + 2 = I + (k + 1) + 1 by omega,
        show J - k - 2 = J - (k + 1) - 1 by omega] at hmain
  have hlt_false : ∀ i j, i < j → j < n → pp i = pp j → False := by
    intro i j hij hjn he
    have hIJ : pp (i + n) = pp (j + n) := by
      rw [hpper i, hpper j]
      exact he
    have hAn : A (pp (j + n)) (pp (i + n + 1)) := by
      have h := hadj (i + n)
      rwa [hIJ] at h
    rcases hnbrs (j + n) (pp (i + n + 1)) (by omega) hAn with hcase | hcase
    · rcases Nat.even_or_odd (j - i) with ⟨t, ht⟩ | ⟨t, ht⟩
      · obtain ⟨h1, -⟩ := hrev (i + n) (j + n) hIJ hcase (t - 1) (by omega)
        have h2 : pp (i + n + t - 1) = pp (i + n + t - 1 + 2) := by
          rwa [show i + n + (t - 1) = i + n + t - 1 by omega,
            show j + n - (t - 1) = i + n + t - 1 + 2 by omega] at h1
        exact hne2 (i + n + t - 1) h2.symm
      · obtain ⟨h1, -⟩ := hrev (i + n) (j + n) hIJ hcase t (by omega)
        have h2 : pp (i + n + t) = pp (i + n + t + 1) := by
          rwa [show j + n - t = i + n + t + 1 by omega] at h1
        exact hirr _ _ (hadj (i + n + t)) h2
    · have hgIJ : g (i + n) = g (j + n) := by
        refine Prod.ext ?_ ?_
        · rw [← hpp0, ← hpp0]
          exact hIJ
        · rw [← hpp1, ← hpp1]
          exact hcase
      have h0 : g 0 = g (j - i) := by
        refine hback (i + n) 0 (j - i) ?_
        rw [show 0 + (i + n) = i + n by omega, show j - i + (i + n) = j + n by omega]
        exact hgIJ
      have := hnmin (j - i) (by omega) h0.symm
      omega
  have hinj : ∀ i j, i < n → j < n → pp i = pp j → i = j := by
    intro i j hi hj he
    rcases lt_trichotomy i j with h | h | h
    · exact absurd he (fun he' => hlt_false i j h hj he')
    · exact h
    · exact absurd he.symm (fun he' => hlt_false j i h hi he')
  have hrange : Set.range pp = P := by
    refine hconn _ (Set.range_subset_iff.mpr hppP) ⟨pp 0, Set.mem_range_self 0⟩ ?_
    rintro x ⟨k, rfl⟩ q hq
    have hA' : A (pp (k + n)) q := by rwa [hpper k]
    rcases hnbrs (k + n) q (by omega) hA' with h | h
    · exact ⟨k + n - 1, h.symm⟩
    · exact ⟨k + n + 1, h.symm⟩
  have hn1 : n ≠ 1 := by
    intro h
    have h2 := hpper 0
    rw [h] at h2
    exact hirr _ _ (hadj 0) h2.symm
  have hn2 : n ≠ 2 := by
    intro h
    have h2 := hpper 0
    rw [h] at h2
    exact hne2 0 h2
  have hn3 : 3 ≤ n := by omega
  refine ⟨n, pp, hn3, hpper, hppP, ?_, hadj⟩
  intro q hq
  have hq' : q ∈ Set.range pp := by
    rw [hrange]
    exact hq
  obtain ⟨k, hk⟩ := hq'
  have hmod : pp (k % n) = pp k := by
    have h1 := hpermul (k / n) (k % n)
    rw [show k % n + k / n * n = k from Nat.mod_add_div' k n] at h1
    exact h1.symm
  refine ⟨k % n, ⟨Nat.mod_lt k hnpos, hmod.trans hk⟩, ?_⟩
  rintro k' ⟨hk', he⟩
  exact hinj k' (k % n) hk' (Nat.mod_lt k hnpos) (he.trans (hmod.trans hk).symm)

/-- **Vertex cycle**: the tiles at a vertex admit a cyclic enumeration in rotational order,
without repetition of tiles, in which consecutive tiles share a genuine side through the
vertex. -/
theorem exists_vertex_cycle (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) :
    ∃ (n : ℕ) (e : ℕ → ↥Γ), 3 ≤ n ∧ (∀ k, e (k + n) = e k) ∧
      (∀ k, e k ∈ contactSet Γ τ₀ v) ∧
      (∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀) ∧
      ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)) := by
  classical
  haveI : Nonempty ↥Γ := ⟨1⟩
  have hPfin : (tileCenters Γ τ₀ v).Finite := (finite_contactSet hΓ τ₀ v).image _
  have hPne : (tileCenters Γ τ₀ v).Nonempty :=
    ⟨τ₀, 1, one_mem_contactSet hv.1, one_smul _ _⟩
  have hrepex : ∀ p ∈ tileCenters Γ τ₀ v,
      ∃ γ : ↥Γ, γ ∈ contactSet Γ τ₀ v ∧ γ • τ₀ = p := by
    rintro p ⟨γ, hγ, rfl⟩
    exact ⟨γ, hγ, rfl⟩
  choose! rep hrep₁ hrep₂ using hrepex
  have hmem : ∀ p q : UpperHalfPlane, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) →
      p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v := fun p q h => ⟨h.1, h.2.1⟩
  have hsymm : ∀ p q : UpperHalfPlane, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) →
      q ∈ tileCenters Γ τ₀ v ∧ p ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep q)⁻¹ * rep p) := by
    rintro p q ⟨hp, hq, hside⟩
    refine ⟨hq, hp, ?_⟩
    have h1 := hside.inv
    rwa [mul_inv_rev, inv_inv] at h1
  have hirr : ∀ p q : UpperHalfPlane, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) → p ≠ q := by
    rintro p q ⟨hp, hq, hside⟩ rfl
    exact hside.1 (by rw [inv_mul_cancel, one_smul])
  have htwo : ∀ p ∈ tileCenters Γ τ₀ v, ∃ q₁ ∈ tileCenters Γ τ₀ v,
      ∃ q₂ ∈ tileCenters Γ τ₀ v, q₁ ≠ q₂ ∧ ∀ q ∈ tileCenters Γ τ₀ v,
      ((p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
        IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) ↔ q = q₁ ∨ q = q₂) := by
    intro p hp
    obtain ⟨q₁, hq₁, q₂, hq₂, hne', hchar⟩ :=
      two_neighbors hΓ hfree hε hgap hdense hv hrep₁ hrep₂ hp
    refine ⟨q₁, hq₁, q₂, hq₂, hne', ?_⟩
    intro q hq
    constructor
    · rintro ⟨-, -, hside⟩
      exact (hchar q hq).mp hside
    · intro h
      exact ⟨hp, hq, (hchar q hq).mpr h⟩
  have hconn : ∀ S : Set UpperHalfPlane, S ⊆ tileCenters Γ τ₀ v → S.Nonempty →
      (∀ p ∈ S, ∀ q, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
        IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) → q ∈ S) → S = tileCenters Γ τ₀ v := by
    intro S hsub hSne hclosed
    refine adj_closed_eq hΓ hfree hv hrep₁ hrep₂ hsub hSne ?_
    intro p hpS q hqP hside
    exact hclosed p hpS q ⟨hsub hpS, hqP, hside⟩
  obtain ⟨n, e₀, hn3, hper, heP, huniq, hadj⟩ :=
    cycle_of_two_regular (A := fun p q => p ∈ tileCenters Γ τ₀ v ∧
      q ∈ tileCenters Γ τ₀ v ∧ IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q))
      hPfin hPne hmem hsymm hirr htwo hconn
  refine ⟨n, fun k => rep (e₀ k), hn3, ?_, ?_, ?_, ?_⟩
  · intro k
    show rep (e₀ (k + n)) = rep (e₀ k)
    rw [hper k]
  · intro k
    exact hrep₁ _ (heP k)
  · intro γ hγ
    have hγP : γ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨γ, hγ, rfl⟩
    obtain ⟨k, ⟨hk, hek⟩, hkuniq⟩ := huniq (γ • τ₀) hγP
    refine ⟨k, ⟨hk, ?_⟩, ?_⟩
    · show γ • τ₀ = rep (e₀ k) • τ₀
      rw [hrep₂ _ (heP k), hek]
    · rintro k' ⟨hk', hek'⟩
      refine hkuniq k' ⟨hk', ?_⟩
      show e₀ k' = γ • τ₀
      rw [← hrep₂ _ (heP k')]
      exact hek'.symm
  · intro k
    exact (hadj k).2.2

/-- **Developed vertex star**: the tiles at a vertex correspond bijectively to the vertices
of the polygon in the orbit class of the vertex, the tile of a contact element `γ`
corresponding to the developed vertex `γ⁻¹ • v`. -/
theorem exists_vertex_star_bijection (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) :
    ∃ Φ : UpperHalfPlane → UpperHalfPlane,
      Set.BijOn Φ (tileCenters Γ τ₀ v) (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀) ∧
      ∀ γ ∈ contactSet Γ τ₀ v, Φ (γ • τ₀) = γ⁻¹ • v := by
  classical
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : UpperHalfPlane → UpperHalfPlane, Φ = fun c =>
      if h : ∃ γ : ↥Γ, γ ∈ contactSet Γ τ₀ v ∧ γ • τ₀ = c
      then (Classical.choose h)⁻¹ • v else v := ⟨_, rfl⟩
  have hΦ : ∀ γ ∈ contactSet Γ τ₀ v, Φ (γ • τ₀) = γ⁻¹ • v := by
    intro γ hγ
    have hex : ∃ δ : ↥Γ, δ ∈ contactSet Γ τ₀ v ∧ δ • τ₀ = γ • τ₀ := ⟨γ, hγ, rfl⟩
    rw [hΦdef]
    simp only
    rw [dif_pos hex]
    obtain ⟨-, hδτ⟩ := Classical.choose_spec hex
    have h1 : γ • (Classical.choose hex)⁻¹ • v
        = Classical.choose hex • (Classical.choose hex)⁻¹ • v :=
      smul_eq_of_basepoint_eq hfree hδτ.symm _
    rw [smul_inv_smul] at h1
    exact eq_inv_smul_iff.mpr h1
  have hmaps : Set.MapsTo Φ (tileCenters Γ τ₀ v)
      (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀) := by
    rintro c ⟨γ, hγ, rfl⟩
    show Φ (γ • τ₀) ∈ _
    rw [hΦ γ hγ]
    exact ⟨MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, rfl⟩, smul_mem_polygonVertices hv hγ⟩
  have hinj : Set.InjOn Φ (tileCenters Γ τ₀ v) := by
    rintro c₁ ⟨γ₁, hγ₁, rfl⟩ c₂ ⟨γ₂, hγ₂, rfl⟩ he
    have he' : γ₁⁻¹ • v = γ₂⁻¹ • v := by
      rw [← hΦ γ₁ hγ₁, ← hΦ γ₂ hγ₂]
      exact he
    have h1 : (γ₂ * γ₁⁻¹) • v = v := by
      rw [mul_smul, he', smul_inv_smul]
    have h2 := hfree (γ₂ * γ₁⁻¹) ⟨v, h1⟩ (γ₁ • τ₀)
    show γ₁ • τ₀ = γ₂ • τ₀
    rw [← h2, mul_smul, inv_smul_smul]
  have hsurj : Set.SurjOn Φ (tileCenters Γ τ₀ v)
      (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀) := by
    rintro v' ⟨horb, hvert⟩
    obtain ⟨η, hη⟩ := MulAction.mem_orbit_iff.mp horb
    have hcon : η⁻¹ ∈ contactSet Γ τ₀ v := by
      rw [mem_contactSet_iff_mem_smul_dirichletDomain]
      refine ⟨η • v, ?_, ?_⟩
      · rw [hη]
        exact hvert.1
      · show η⁻¹ • η • v = v
        rw [inv_smul_smul]
    refine ⟨η⁻¹ • τ₀, ⟨η⁻¹, hcon, rfl⟩, ?_⟩
    show Φ (η⁻¹ • τ₀) = v'
    rw [hΦ η⁻¹ hcon, inv_inv, hη]
  exact ⟨Φ, ⟨hmaps, hinj, hsurj⟩, hΦ⟩

#print axioms exists_vertex_cycle
#print axioms exists_vertex_star_bijection


variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-- Every side is contained in the Dirichlet domain. -/
theorem side_subset_dirichletDomain {s : Set UpperHalfPlane}
    (hs : s ∈ polygonSides Γ τ₀) : s ⊆ dirichletDomain Γ τ₀ := by
  obtain ⟨γ, -, rfl⟩ := hs
  exact fun x hx => hx.1

/-- Two distinct sides meet in at most one point. -/
theorem side_inter_subsingleton {s s' : Set UpperHalfPlane}
    (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀) (hne : s ≠ s') :
    (s ∩ s').Subsingleton := by
  obtain ⟨γ, hγ, rfl⟩ := hs
  obtain ⟨δ, hδ, rfl⟩ := hs'
  intro x hx y hy
  by_contra hxy
  exact hne (sideSet_eq_of_basepoint_eq
    (bisector_pair_unique hxy hx.1.2 hy.1.2 hx.2.2 hy.2.2 hγ.1 hδ.1))

/-- The cone over a side stays in the Dirichlet domain. -/
theorem geodCone_side_subset {s : Set UpperHalfPlane}
    (hs : s ∈ polygonSides Γ τ₀) : geodCone τ₀ s ⊆ dirichletDomain Γ τ₀ := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := mem_geodCone.mp hx
  exact geodConvex_dirichletDomain τ₀ basepoint_mem_dirichletDomain w
    (side_subset_dirichletDomain hs hw) hxw

/-- The Dirichlet domain is not all of the upper half plane. -/
theorem exists_notMem_dirichletDomain {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ y : UpperHalfPlane, y ∉ dirichletDomain Γ τ₀ := by
  have hR : 0 ≤ R := le_trans Metric.infDist_nonneg (hdense τ₀)
  have hy : (0 : ℝ) < ((⟨τ₀.re, τ₀.im * Real.exp (R + 1)⟩ : ℂ)).im :=
    mul_pos τ₀.im_pos (Real.exp_pos _)
  set y : UpperHalfPlane := UpperHalfPlane.mk ⟨τ₀.re, τ₀.im * Real.exp (R + 1)⟩ hy with hydef
  refine ⟨y, fun hyD => ?_⟩
  have h1 : dist τ₀ y ≤ R := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hyD)
  have hre : τ₀.re = y.re := rfl
  have him : y.im = τ₀.im * Real.exp (R + 1) := rfl
  have h2 : dist τ₀ y = |Real.log τ₀.im - Real.log y.im| := dist_of_re_eq hre
  rw [him, Real.log_mul τ₀.im_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [show Real.log τ₀.im - (Real.log τ₀.im + (R + 1)) = -(R + 1) by ring, abs_neg,
    abs_of_pos (by linarith)] at h2
  linarith [h1, h2.symm.le]

/-- Of two points beyond a common ray point, the nearer lies on the segment to the
farther. -/
theorem mem_geodSeg_of_ray_le {a x w w' : UpperHalfPlane} (hxa : x ≠ a)
    (hw : x ∈ geodSeg a w) (hw' : x ∈ geodSeg a w') (hle : dist a w ≤ dist a w') :
    w ∈ geodSeg a w' := by
  have hbw : dist a x + dist x w = dist a w := mem_geodSeg.mp hw
  have hbw' : dist a x + dist x w' = dist a w' := mem_geodSeg.mp hw'
  have haw' : a ≠ w' := by
    rintro rfl
    rw [geodSeg_self] at hw'
    exact hxa (Set.mem_singleton_iff.mp hw')
  have hd' : 0 < dist a w' := dist_pos.mpr haw'
  set t : ℝ := dist a w / dist a w' with htdef
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hd').mpr hle⟩
  set p : UpperHalfPlane := geodInterp a w' t with hpdef
  have hp : p ∈ geodSeg a w' := geodInterp_mem_geodSeg a w' ht
  have hdap : dist a p = dist a w := by
    rw [hpdef, dist_geodInterp_left a w' ht, htdef, div_mul_cancel₀ _ hd'.ne']
  obtain ⟨sx, hsx, hxeq⟩ := (geodSeg_eq_image_geodInterp a w' ▸ hw' :
    x ∈ geodInterp a w' '' Set.Icc (0 : ℝ) 1)
  have hdax : dist a x = sx * dist a w' := by
    rw [← hxeq, dist_geodInterp_left a w' hsx]
  have htd : t * dist a w' = dist a w := by
    rw [htdef]
    exact div_mul_cancel₀ _ hd'.ne'
  have hst : sx ≤ t := by
    by_contra hcon
    have hcon' : t < sx := not_le.mp hcon
    have h1 : t * dist a w' < sx * dist a w' := mul_lt_mul_of_pos_right hcon' hd'
    have := dist_nonneg (x := x) (y := w)
    linarith [htd, hdax.symm.le, hbw]
  have hdxp : dist x p = (t - sx) * dist a w' := by
    rw [← hxeq, hpdef, dist_geodInterp_pair, abs_of_nonpos (by linarith), neg_sub]
  have hexp : (t - sx) * dist a w' = t * dist a w' - sx * dist a w' := by ring
  have hxp : x ∈ geodSeg a p := by
    rw [mem_geodSeg, hdax, hdxp, hdap]
    linarith [htd, hexp]
  have hwp : w = p :=
    collinear_unique (Ne.symm hxa) (Or.inr (Or.inl hbw)) (Or.inr (Or.inl (mem_geodSeg.mp hxp)))
      hdap.symm (by linarith [hbw, hdxp, hdax, htd, hexp])
  rw [hwp]
  exact hp

/-- Every domain point lies on a radial segment from the basepoint to a side point. -/
theorem exists_exit (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) :
    ∃ s ∈ polygonSides Γ τ₀, ∃ w ∈ s, z ∈ geodSeg τ₀ w := by
  by_cases hzτ : z = τ₀
  · obtain ⟨y, hy⟩ := exists_notMem_dirichletDomain hdense
    obtain ⟨w, -, hwfr⟩ := exists_frontier_mem_geodSeg basepoint_mem_dirichletDomain hy
    rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense] at hwfr
    obtain ⟨s, hs, hws⟩ := hwfr
    exact ⟨s, hs, w, hws, by rw [hzτ]; exact left_mem_geodSeg τ₀ w⟩
  · have hd : 0 < dist τ₀ z := dist_pos.mpr (Ne.symm hzτ)
    have hzR : dist τ₀ z ≤ R := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hz)
    set T : ℝ := (R + 1) / dist τ₀ z with hTdef
    have hR : 0 ≤ R := le_trans Metric.infDist_nonneg (hdense τ₀)
    have hTd : T * dist τ₀ z = R + 1 := div_mul_cancel₀ _ hd.ne'
    have hT1 : 1 < T := by
      rw [hTdef]
      exact (one_lt_div hd).mpr (by linarith)
    set y : UpperHalfPlane := geodInterp τ₀ z T with hydef
    have hdy : dist τ₀ y = R + 1 := by
      rw [hydef, dist_geodInterp_left_abs, abs_of_pos (by linarith), hTd]
    have hyD : y ∉ dirichletDomain Γ τ₀ := fun hc => by
      have h1 : dist y τ₀ ≤ R :=
        Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hc)
      rw [dist_comm] at h1
      linarith [hdy ▸ h1]
    have hzy : z ∈ geodSeg τ₀ y := by
      rw [mem_geodSeg]
      have h2 : dist z y = (T - 1) * dist τ₀ z := by
        conv_lhs => rw [show z = geodInterp τ₀ z 1 from (geodInterp_one τ₀ z).symm]
        rw [hydef, dist_geodInterp_pair, abs_of_nonpos (by linarith), neg_sub]
      rw [h2, hdy]
      linarith [hTd]
    obtain ⟨w, hwseg, hwfr⟩ := exists_frontier_mem_geodSeg hz hyD
    have hzw : z ∈ geodSeg τ₀ w := by
      rw [mem_geodSeg]
      have e1 : dist τ₀ z + dist z y = dist τ₀ y := mem_geodSeg.mp hzy
      have e2 : dist z w + dist w y = dist z y := mem_geodSeg.mp hwseg
      have t1 : dist τ₀ w ≤ dist τ₀ z + dist z w := dist_triangle _ _ _
      have t2 : dist τ₀ y ≤ dist τ₀ w + dist w y := dist_triangle _ _ _
      linarith
    rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense] at hwfr
    obtain ⟨s, hs, hws⟩ := hwfr
    exact ⟨s, hs, w, hws, hzw⟩

/-- **Fan decomposition**: the Dirichlet domain is the union of the geodesic cones from the
basepoint over its sides. -/
theorem dirichletDomain_eq_biUnion_geodCone (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    dirichletDomain Γ τ₀ = ⋃ s ∈ polygonSides Γ τ₀, geodCone τ₀ s := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨s, hs, w, hws, hzw⟩ := exists_exit hΓ hfree hε hgap hdense hz
    exact Set.mem_biUnion hs (mem_geodCone.mpr ⟨w, hws, hzw⟩)
  · intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    exact geodCone_side_subset hs hzs

/-- A common point of two cones away from the apex lies on a radial segment through a
common point of the two sides. -/
theorem geodCone_inter_carrier (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s s' : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀)
    {x : UpperHalfPlane} (hx : x ∈ geodCone τ₀ s) (hx' : x ∈ geodCone τ₀ s')
    (hxτ : x ≠ τ₀) : ∃ p ∈ s ∩ s', x ∈ geodSeg τ₀ p := by
  obtain ⟨w, hws, hxw⟩ := mem_geodCone.mp hx
  obtain ⟨w', hws', hxw'⟩ := mem_geodCone.mp hx'
  have hfr := frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense
  have hwfr : w ∈ frontier (dirichletDomain Γ τ₀) := by rw [hfr]; exact ⟨s, hs, hws⟩
  have hw'fr : w' ∈ frontier (dirichletDomain Γ τ₀) := by rw [hfr]; exact ⟨s', hs', hws'⟩
  rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hwfr hw'fr
  rcases le_total (dist τ₀ w) (dist τ₀ w') with h | h
  · have hseg : w ∈ geodSeg τ₀ w' := mem_geodSeg_of_ray_le hxτ hxw hxw' h
    by_cases hww' : w = w'
    · exact ⟨w, ⟨hws, hww' ▸ hws'⟩, hxw⟩
    · exact absurd (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain hs' hws') hseg hww') hwfr.2
  · have hseg : w' ∈ geodSeg τ₀ w := mem_geodSeg_of_ray_le hxτ hxw' hxw h
    by_cases hww' : w' = w
    · exact ⟨w, ⟨hws, hww' ▸ hws'⟩, hxw⟩
    · exact absurd (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain hs hws) hseg hww') hw'fr.2

/-- Distinct cones of the fan overlap in a null set: their intersection is carried by the
shared boundary rays, which are geodesic segments. -/
theorem volume_geodCone_inter_eq_zero (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s s' : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀)
    (hne : s ≠ s') :
    volume (geodCone τ₀ s ∩ geodCone τ₀ s') = 0 := by
  have hsub := side_inter_subsingleton hs hs' hne
  rcases Set.eq_empty_or_nonempty (s ∩ s') with hemp | ⟨p, hp⟩
  · have h0 : volume ({τ₀} : Set UpperHalfPlane) = 0 := by
      rw [← geodSeg_self τ₀]
      exact volume_geodSeg_eq_zero τ₀ τ₀
    refine measure_mono_null (fun x hx => ?_) h0
    by_cases hxτ : x = τ₀
    · exact hxτ ▸ rfl
    · obtain ⟨q, hq, -⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense hs hs'
        hx.1 hx.2 hxτ
      rw [hemp] at hq
      exact absurd hq (Set.notMem_empty q)
  · refine measure_mono_null (fun x hx => ?_) (volume_geodSeg_eq_zero τ₀ p)
    by_cases hxτ : x = τ₀
    · rw [hxτ]
      exact left_mem_geodSeg τ₀ p
    · obtain ⟨q, hq, hxq⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense hs hs'
        hx.1 hx.2 hxτ
      rw [hsub hq hp] at hxq
      exact hxq

/-- Arguments add absolutely for a product of upper-half-plane factors with upper-half
product. -/
theorem abs_arg_mul_pos {A B : ℂ} (hA : 0 < A.im) (hB : 0 < B.im)
    (hAB : 0 < (A * B).im) : |(A * B).arg| = |A.arg| + |B.arg| := by
  have hA0 : A ≠ 0 := fun h => by rw [h, Complex.zero_im] at hA; exact lt_irrefl 0 hA
  have hB0 : B ≠ 0 := fun h => by rw [h, Complex.zero_im] at hB; exact lt_irrefl 0 hB
  have hπ := Real.pi_pos
  have hbound : ∀ z : ℂ, 0 < z.im → 0 < z.arg ∧ z.arg < Real.pi := by
    intro z hz
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) fun h => ?_,
      lt_of_le_of_ne (Complex.arg_le_pi z) fun h => ?_⟩
    · exact hz.ne (Complex.arg_eq_zero_iff.mp h.symm).2.symm
    · exact hz.ne (Complex.arg_eq_pi_iff.mp h).2.symm
  obtain ⟨hA1, hA2⟩ := hbound A hA
  obtain ⟨hB1, hB2⟩ := hbound B hB
  obtain ⟨hC1, hC2⟩ := hbound (A * B) hAB
  have h2 : (((A * B).arg : ℝ) : Real.Angle) = ((A.arg + B.arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact Complex.arg_mul_coe_angle hA0 hB0
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h2
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < (k : ℝ) := by nlinarith
  have hk0 : k = 0 := by
    have h3 : k < 1 := by exact_mod_cast hk1
    have h4 : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  push_cast at hk
  rw [abs_of_pos hC1, abs_of_pos hA1, abs_of_pos hB1]
  linarith

/-- Conjugation preserves the absolute argument off the real axis. -/
theorem abs_arg_conj_of_im_ne {z : ℂ} (hz : z.im ≠ 0) :
    |((starRingEnd ℂ) z).arg| = |z.arg| := by
  rw [Complex.arg_conj, if_neg fun h => hz (Complex.arg_eq_pi_iff.mp h).2, abs_neg]

/-- Arguments add absolutely for factors on a common side of the real axis whose product
stays on that side. -/
theorem abs_arg_mul_of_same_side {A B : ℂ}
    (h : 0 < A.im ∧ 0 < B.im ∧ 0 < (A * B).im ∨ A.im < 0 ∧ B.im < 0 ∧ (A * B).im < 0) :
    |(A * B).arg| = |A.arg| + |B.arg| := by
  rcases h with ⟨hA, hB, hAB⟩ | ⟨hA, hB, hAB⟩
  · exact abs_arg_mul_pos hA hB hAB
  · have hconj : (starRingEnd ℂ) A * (starRingEnd ℂ) B = (starRingEnd ℂ) (A * B) :=
      (map_mul _ A B).symm
    have h1 : |((starRingEnd ℂ) (A * B)).arg|
        = |((starRingEnd ℂ) A).arg| + |((starRingEnd ℂ) B).arg| := by
      rw [← hconj]
      exact abs_arg_mul_pos (by rw [Complex.conj_im]; linarith)
        (by rw [Complex.conj_im]; linarith)
        (by rw [hconj, Complex.conj_im]; linarith)
    rw [abs_arg_conj_of_im_ne hAB.ne, abs_arg_conj_of_im_ne hA.ne, abs_arg_conj_of_im_ne hB.ne] at h1
    exact h1

/-- A sign functional vanishing along a direction is a multiple of the imaginary part in
that frame. -/
theorem functional_ratio {m : ℂ} {e : ℝ} (he : e = 1 ∨ e = -1) {u : ℂ} (hu : u ≠ 0)
    (h0 : e * (m * u).im = 0) (x : ℂ) :
    e * (m * x).im = (e * (m * u).re) * (x / u).im := by
  have him : (m * u).im = 0 := by rcases he with h | h <;> rw [h] at h0 <;> linarith
  have hmu : m * u = (((m * u).re : ℝ) : ℂ) :=
    Complex.ext rfl (by rw [him, Complex.ofReal_im])
  have hx : m * x = (m * u) * (x / u) := by
    rw [mul_assoc, mul_comm u (x / u), div_mul_cancel₀ x hu]
  rw [hx, hmu]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

/-- The segment from a vertex to the basepoint splits the interior angle into the base
angles of the two adjacent cones of the fan. -/
theorem sectorAngle_eq_add_basepoint (hΓ : IsFuchsianGroup Γ)
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
    sectorAngle v w₁ w₂ = sectorAngle v w₁ τ₀ + sectorAngle v τ₀ w₂ := by
  have hs₁' := hs₁
  have hs₂' := hs₂
  obtain ⟨γ₁, hγ₁, hs₁def⟩ := hs₁'
  obtain ⟨γ₂, hγ₂, hs₂def⟩ := hs₂'
  have hpq₁ : τ₀ ≠ γ₁ • τ₀ := Ne.symm hγ₁.1
  have hpq₂ : τ₀ ≠ γ₂ • τ₀ := Ne.symm hγ₂.1
  obtain ⟨g₁, ε₁, hε₁, hle₁, hge₁⟩ := bisector_normalizer hpq₁
  obtain ⟨g₂, ε₂, hε₂, hle₂, hge₂⟩ := bisector_normalizer hpq₂
  have hveq₁ : dist v τ₀ = dist v (γ₁ • τ₀) := by
    have h := he₁.1
    rw [hs₁def] at h
    exact h.2
  have hveq₂ : dist v τ₀ = dist v (γ₂ • τ₀) := by
    have h := he₂.1
    rw [hs₂def] at h
    exact h.2
  obtain ⟨m₁, hm₁, hf₁eq, hf₁lt⟩ := functional_sign hε₁ hle₁ hge₁ hveq₁
  obtain ⟨m₂, hm₂, hf₂eq, hf₂lt⟩ := functional_sign hε₂ hle₂ hge₂ hveq₂
  have hssub := side_inter_subsingleton hs₁ hs₂ hne
  have hvmem : v ∈ s₁ ∩ s₂ := ⟨he₁.1, he₂.1⟩
  have hw₁eq : dist w₁ τ₀ = dist w₁ (γ₁ • τ₀) := by
    have h := hw₁
    rw [hs₁def] at h
    exact h.2
  have hw₂eq : dist w₂ τ₀ = dist w₂ (γ₂ • τ₀) := by
    have h := hw₂
    rw [hs₂def] at h
    exact h.2
  have hw₂lt : dist w₂ τ₀ < dist w₂ (γ₁ • τ₀) := by
    have hD : w₂ ∈ dirichletDomain Γ τ₀ := side_subset_dirichletDomain hs₂ hw₂
    rcases lt_or_eq_of_le (hD γ₁) with h | h
    · exact h
    · exact absurd (hssub ⟨by rw [hs₁def]; exact ⟨hD, h⟩, hw₂⟩ hvmem) hw₂v
  have hw₁lt : dist w₁ τ₀ < dist w₁ (γ₂ • τ₀) := by
    have hD : w₁ ∈ dirichletDomain Γ τ₀ := side_subset_dirichletDomain hs₁ hw₁
    rcases lt_or_eq_of_le (hD γ₂) with h | h
    · exact h
    · exact absurd (hssub ⟨hw₁, by rw [hs₂def]; exact ⟨hD, h⟩⟩ hvmem) hw₁v
  have hτlt₁ : dist τ₀ τ₀ < dist τ₀ (γ₁ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq₁
  have hτlt₂ : dist τ₀ τ₀ < dist τ₀ (γ₂ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq₂
  have hu₁ : discChart v w₁ ≠ 0 := discChart_ne_zero hw₁v
  have hu₂ : discChart v w₂ ≠ 0 := discChart_ne_zero hw₂v
  have E₁ : ε₁ * (m₁ * discChart v w₁).im = 0 := hf₁eq w₁ hw₁eq
  have E₂ : ε₂ * (m₂ * discChart v w₂).im = 0 := hf₂eq w₂ hw₂eq
  have P12 : 0 < ε₁ * (m₁ * discChart v w₂).im := hf₁lt w₂ hw₂lt
  have P1t : 0 < ε₁ * (m₁ * discChart v τ₀).im := hf₁lt τ₀ hτlt₁
  have P21 : 0 < ε₂ * (m₂ * discChart v w₁).im := hf₂lt w₁ hw₁lt
  have P2t : 0 < ε₂ * (m₂ * discChart v τ₀).im := hf₂lt τ₀ hτlt₂
  have htc : discChart v τ₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at P1t
    simp at P1t
  rw [functional_ratio hε₁ hu₁ E₁ (discChart v w₂)] at P12
  rw [functional_ratio hε₁ hu₁ E₁ (discChart v τ₀)] at P1t
  rw [functional_ratio hε₂ hu₂ E₂ (discChart v w₁)] at P21
  rw [functional_ratio hε₂ hu₂ E₂ (discChart v τ₀)] at P2t
  have hsgn_pp : ∀ a b : ℝ, 0 < a * b → 0 < a → 0 < b := by
    intro a b hab ha
    nlinarith
  have hsgn_nn : ∀ a b : ℝ, 0 < a * b → a < 0 → b < 0 := by
    intro a b hab ha
    nlinarith
  have hsgn_bp : ∀ a b : ℝ, 0 < a * b → 0 < b → 0 < a := by
    intro a b hab hb
    nlinarith
  have hsgn_bn : ∀ a b : ℝ, 0 < a * b → b < 0 → a < 0 := by
    intro a b hab hb
    nlinarith
  have hABeq : discChart v τ₀ / discChart v w₁ * (discChart v w₂ / discChart v τ₀)
      = discChart v w₂ / discChart v w₁ := by
    field_simp
  have hNC : 0 < Complex.normSq (discChart v w₂ / discChart v w₁) :=
    Complex.normSq_pos.mpr (div_ne_zero hu₂ hu₁)
  have hNt : 0 < Complex.normSq (discChart v τ₀ / discChart v w₂) :=
    Complex.normSq_pos.mpr (div_ne_zero htc hu₂)
  have hCinv : (discChart v w₁ / discChart v w₂).im
      = -(discChart v w₂ / discChart v w₁).im
        / Complex.normSq (discChart v w₂ / discChart v w₁) := by
    rw [← inv_div (discChart v w₂) (discChart v w₁), Complex.inv_im]
  have hBinv : (discChart v w₂ / discChart v τ₀).im
      = -(discChart v τ₀ / discChart v w₂).im
        / Complex.normSq (discChart v τ₀ / discChart v w₂) := by
    rw [← inv_div (discChart v τ₀) (discChart v w₂), Complex.inv_im]
  have hCne0 : (discChart v w₂ / discChart v w₁).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at P12
    exact lt_irrefl 0 P12
  have key : 0 < (discChart v τ₀ / discChart v w₁).im
        ∧ 0 < (discChart v w₂ / discChart v τ₀).im
        ∧ 0 < (discChart v w₂ / discChart v w₁).im
      ∨ (discChart v τ₀ / discChart v w₁).im < 0
        ∧ (discChart v w₂ / discChart v τ₀).im < 0
        ∧ (discChart v w₂ / discChart v w₁).im < 0 := by
    rcases lt_or_gt_of_ne hCne0 with hC | hC
    · right
      have hq₁ : ε₁ * (m₁ * discChart v w₁).re < 0 := hsgn_bn _ _ P12 hC
      have hA : (discChart v τ₀ / discChart v w₁).im < 0 := hsgn_nn _ _ P1t hq₁
      have hu₁₂ : 0 < (discChart v w₁ / discChart v w₂).im := by
        rw [hCinv]
        exact div_pos (by linarith) hNC
      have hq₂ : 0 < ε₂ * (m₂ * discChart v w₂).re := hsgn_bp _ _ P21 hu₁₂
      have ht₂ : 0 < (discChart v τ₀ / discChart v w₂).im := hsgn_pp _ _ P2t hq₂
      have hB : (discChart v w₂ / discChart v τ₀).im < 0 := by
        rw [hBinv]
        exact div_neg_of_neg_of_pos (by linarith) hNt
      exact ⟨hA, hB, hC⟩
    · left
      have hq₁ : 0 < ε₁ * (m₁ * discChart v w₁).re := hsgn_bp _ _ P12 hC
      have hA : 0 < (discChart v τ₀ / discChart v w₁).im := hsgn_pp _ _ P1t hq₁
      have hu₁₂ : (discChart v w₁ / discChart v w₂).im < 0 := by
        rw [hCinv]
        exact div_neg_of_neg_of_pos (by linarith) hNC
      have hq₂ : ε₂ * (m₂ * discChart v w₂).re < 0 := hsgn_bn _ _ P21 hu₁₂
      have ht₂ : (discChart v τ₀ / discChart v w₂).im < 0 := hsgn_nn _ _ P2t hq₂
      have hB : 0 < (discChart v w₂ / discChart v τ₀).im := by
        rw [hBinv]
        exact div_pos (by linarith) hNt
      exact ⟨hA, hB, hC⟩
  rw [← hABeq] at key
  have hfinal := abs_arg_mul_of_same_side key
  rw [hABeq] at hfinal
  simp only [sectorAngle]
  exact hfinal

/-- The boundary-walk step on side-vertex darts: switch to the other side through the
vertex, then move to its other endpoint. -/
def stepDart {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d : α × β) : α × β :=
  (oside d.2 d.1, oend (oside d.2 d.1) d.2)

/-- The reversal of a dart: the same side, seen from its other endpoint. -/
def revDart {α β : Type*} (oend : α → β → β) (d : α × β) : α × β :=
  (d.1, oend d.1 d.2)

/-- The orbit of a dart under the boundary-walk step. -/
def dartOrbit {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) (k : ℕ) : α × β :=
  (stepDart oside oend)^[k] d₀

theorem dartOrbit_zero {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) : dartOrbit oside oend d₀ 0 = d₀ :=
  rfl

theorem dartOrbit_succ {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) (k : ℕ) :
    dartOrbit oside oend d₀ (k + 1)
      = stepDart oside oend (dartOrbit oside oend d₀ k) :=
  Function.iterate_succ_apply' _ k d₀

theorem dartOrbit_add {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) (m k : ℕ) :
    dartOrbit oside oend d₀ (m + k)
      = (stepDart oside oend)^[m] (dartOrbit oside oend d₀ k) :=
  Function.iterate_add_apply _ m k d₀

/-- A finite connected two-regular side-vertex incidence structure is traversed by a
single closed boundary walk meeting every side exactly once per period. -/
theorem two_regular_cycle {α β : Type*} {SS : Set α} {V : Set β}
    (hfin : SS.Finite) (Endp : α → β → Prop)
    (oend : α → β → β) (oside : β → α → α)
    (hvtx : ∀ s ∈ SS, ∀ v, Endp s v → v ∈ V)
    (hoend : ∀ s ∈ SS, ∀ v, Endp s v →
      Endp s (oend s v) ∧ oend s v ≠ v ∧ oend s (oend s v) = v)
    (htwoend : ∀ s ∈ SS, ∀ v w, Endp s v → Endp s w → w = v ∨ w = oend s v)
    (hoside : ∀ v ∈ V, ∀ s ∈ SS, Endp s v →
      oside v s ∈ SS ∧ oside v s ≠ s ∧ Endp (oside v s) v ∧ oside v (oside v s) = s)
    (hconn : ∀ C : Set α, C ⊆ SS → C.Nonempty →
      (∀ s ∈ C, ∀ v, Endp s v → oside v s ∈ C) → SS ⊆ C)
    {s₀ : α} {v₀ : β} (hs₀ : s₀ ∈ SS) (hv₀ : Endp s₀ v₀) :
    ∃ (n : ℕ) (f : ℕ → α × β), 0 < n ∧ (∀ k, f (k + n) = f k) ∧
      (∀ k, (f k).1 ∈ SS ∧ Endp (f k).1 (f k).2) ∧
      (∀ s ∈ SS, ∃! k, k < n ∧ (f k).1 = s) ∧
      (∀ k, (f (k + 1)).1 = oside (f k).2 (f k).1) := by
  classical
  have hpres : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      (stepDart oside oend d).1 ∈ SS
        ∧ Endp (stepDart oside oend d).1 (stepDart oside oend d).2 := by
    rintro ⟨s, v⟩ hs hv
    have hvV : v ∈ V := hvtx s hs v hv
    obtain ⟨h1, h2, h3, h4⟩ := hoside v hvV s hs hv
    exact ⟨h1, (hoend _ h1 v h3).1⟩
  have hrevmem : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      (revDart oend d).1 ∈ SS
        ∧ Endp (revDart oend d).1 (revDart oend d).2 := by
    rintro ⟨s, v⟩ hs hv
    exact ⟨hs, (hoend s hs v hv).1⟩
  have hrevne : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 → revDart oend d ≠ d := by
    rintro ⟨s, v⟩ hs hv hcon
    exact (hoend s hs v hv).2.1 (congrArg Prod.snd hcon)
  have hrevrev : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      revDart oend (revDart oend d) = d := by
    rintro ⟨s, v⟩ hs hv
    show (s, oend s (oend s v)) = (s, v)
    rw [(hoend s hs v hv).2.2]
  have hconj : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      stepDart oside oend (revDart oend (stepDart oside oend d))
        = revDart oend d := by
    rintro ⟨s, v⟩ hs hv
    have hvV : v ∈ V := hvtx s hs v hv
    obtain ⟨h1, h2, h3, h4⟩ := hoside v hvV s hs hv
    have e1 : oend (oside v s) (oend (oside v s) v) = v := (hoend _ h1 v h3).2.2
    show stepDart oside oend
        (oside v s, oend (oside v s) (oend (oside v s) v)) = (s, oend s v)
    rw [e1]
    show (oside v (oside v s), oend (oside v (oside v s)) v) = (s, oend s v)
    rw [h4]
  have hinj : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      ∀ d' : α × β, d'.1 ∈ SS → Endp d'.1 d'.2 →
      stepDart oside oend d = stepDart oside oend d' → d = d' := by
    intro d hd1 hd2 d' hd1' hd2' h
    have h1 : revDart oend (stepDart oside oend
        (revDart oend (stepDart oside oend d))) = d := by
      rw [hconj d hd1 hd2]
      exact hrevrev d hd1 hd2
    have h2 : revDart oend (stepDart oside oend
        (revDart oend (stepDart oside oend d'))) = d' := by
      rw [hconj d' hd1' hd2']
      exact hrevrev d' hd1' hd2'
    rw [← h1, ← h2, h]
  set f : ℕ → α × β := dartOrbit oside oend (s₀, v₀) with hfdef
  have hfsucc : ∀ k, f (k + 1) = stepDart oside oend (f k) := fun k =>
    dartOrbit_succ oside oend (s₀, v₀) k
  have hfadd : ∀ m k, f (m + k) = (stepDart oside oend)^[m] (f k) := fun m k =>
    dartOrbit_add oside oend (s₀, v₀) m k
  have hfk : ∀ k, (f k).1 ∈ SS ∧ Endp (f k).1 (f k).2 := by
    intro k
    induction k with
    | zero => exact ⟨hs₀, hv₀⟩
    | succ k ih =>
      rw [hfsucc k]
      exact hpres _ ih.1 ih.2
  have hiterpres : ∀ m, ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      ((stepDart oside oend)^[m] d).1 ∈ SS
        ∧ Endp ((stepDart oside oend)^[m] d).1
            ((stepDart oside oend)^[m] d).2 := by
    intro m
    induction m with
    | zero => intro d hd1 hd2; exact ⟨hd1, hd2⟩
    | succ m ih =>
      intro d hd1 hd2
      rw [Function.iterate_succ_apply]
      exact ih _ (hpres d hd1 hd2).1 (hpres d hd1 hd2).2
  have hiterinj : ∀ m, ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      ∀ d' : α × β, d'.1 ∈ SS → Endp d'.1 d'.2 →
      (stepDart oside oend)^[m] d = (stepDart oside oend)^[m] d' → d = d' := by
    intro m
    induction m with
    | zero => intro d _ _ d' _ _ h; exact h
    | succ m ih =>
      intro d hd1 hd2 d' hd1' hd2' h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact hinj d hd1 hd2 d' hd1' hd2'
        (ih _ (hpres d hd1 hd2).1 (hpres d hd1 hd2).2
          _ (hpres d' hd1' hd2').1 (hpres d' hd1' hd2').2 h)
  have hEfin : ∀ s ∈ SS, {v : β | Endp s v}.Finite := by
    intro s hs
    by_cases hex : ∃ v, Endp s v
    · obtain ⟨v₁, hv₁⟩ := hex
      refine ((Set.finite_singleton (oend s v₁)).insert v₁).subset ?_
      intro w hw
      rcases htwoend s hs v₁ w hv₁ hw with h | h
      · rw [h]
        exact Set.mem_insert _ _
      · rw [h]
        exact Set.mem_insert_of_mem _ rfl
    · exact Set.finite_empty.subset (fun w hw => absurd ⟨w, hw⟩ hex)
  have hDtfin : {d : α × β | d.1 ∈ SS ∧ Endp d.1 d.2}.Finite := by
    refine (hfin.biUnion (fun s hs => (hEfin s hs).image (fun v => (s, v)))).subset ?_
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    exact Set.mem_biUnion hs ⟨v, hv, rfl⟩
  have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
    have hmaps : Set.MapsTo f Set.univ {d : α × β | d.1 ∈ SS ∧ Endp d.1 d.2} :=
      fun k _ => ⟨(hfk k).1, (hfk k).2⟩
    obtain ⟨i, -, j, -, hij, hfij⟩ :=
      Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hDtfin
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hfij⟩
    · exact ⟨j, i, h, hfij.symm⟩
  have hret : ∃ k, 0 < k ∧ f k = (s₀, v₀) := by
    obtain ⟨i, j, hij, hfij⟩ := hrep
    have h2 : f j = (stepDart oside oend)^[i] (f (j - i)) := by
      rw [← hfadd i (j - i)]
      congr 1
      omega
    have h3 : (stepDart oside oend)^[i] (f 0)
        = (stepDart oside oend)^[i] (f (j - i)) := by
      rw [← hfadd i 0]
      rw [show i + 0 = i from rfl, hfij, h2]
    have h4 : f 0 = f (j - i) :=
      hiterinj i _ (hfk 0).1 (hfk 0).2 _ (hfk (j - i)).1 (hfk (j - i)).2 h3
    exact ⟨j - i, by omega, h4.symm⟩
  set n : ℕ := Nat.find hret with hndef
  obtain ⟨hn0, hnfix⟩ : 0 < n ∧ f n = (s₀, v₀) := Nat.find_spec hret
  have hper : ∀ k, f (k + n) = f k := by
    intro k
    rw [hfadd k n, hnfix]
    exact (hfadd k 0).symm.trans (by rw [show k + 0 = k from rfl])
  have hkey0 : ∀ a b, a < b → b < n → f a = f b → False := by
    intro a b hab hbn hfab
    have h2 : f b = (stepDart oside oend)^[a] (f (b - a)) := by
      rw [← hfadd a (b - a)]
      congr 1
      omega
    have h3 : (stepDart oside oend)^[a] (f 0)
        = (stepDart oside oend)^[a] (f (b - a)) := by
      rw [← hfadd a 0, show a + 0 = a from rfl, hfab, h2]
    have h4 : f 0 = f (b - a) :=
      hiterinj a _ (hfk 0).1 (hfk 0).2 _ (hfk (b - a)).1 (hfk (b - a)).2 h3
    exact Nat.find_min hret (show b - a < n by omega) ⟨by omega, h4.symm⟩
  have hinjres : ∀ a b, a < n → b < n → f a = f b → a = b := by
    intro a b ha hb hab
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hkey0 a b h hb hab
    · exact hkey0 b a h ha hab.symm
  have hmod : ∀ q r, f (r + q * n) = f r := by
    intro q
    induction q with
    | zero => intro r; rw [Nat.zero_mul, Nat.add_zero]
    | succ q ih =>
      intro r
      rw [show r + (q + 1) * n = (r + q * n) + n from by ring, hper, ih]
  have hmodlt : ∀ k, f (k % n) = f k := by
    intro k
    conv_rhs => rw [show k = k % n + (k / n) * n from (Nat.mod_add_div' k n).symm]
    rw [hmod]
  have hriter : ∀ m k,
      (stepDart oside oend)^[m] (revDart oend (f (k + m)))
        = revDart oend (f k) := by
    intro m
    induction m with
    | zero =>
      intro k
      rw [Nat.add_zero]
      rfl
    | succ m ih =>
      intro k
      rw [show k + (m + 1) = (k + m) + 1 from by omega, hfsucc (k + m),
        Function.iterate_succ_apply, hconj _ (hfk (k + m)).1 (hfk (k + m)).2]
      exact ih k
  have hkey2 : ∀ i j, i < j → j < n → f j = revDart oend (f i) → False := by
    intro i j hij hjn hji
    have hstepm : ∀ m, m ≤ n → revDart oend (f (i + m)) = f (j + n - m) := by
      intro m hm
      have h1 : (stepDart oside oend)^[m] (revDart oend (f (i + m))) = f j :=
        (hriter m i).trans hji.symm
      have h2 : (stepDart oside oend)^[m] (f (j + n - m)) = f j := by
        rw [← hfadd m (j + n - m), show m + (j + n - m) = j + n from by omega, hper]
      have hd1 := hrevmem _ (hfk (i + m)).1 (hfk (i + m)).2
      exact hiterinj m _ hd1.1 hd1.2 _ (hfk (j + n - m)).1 (hfk (j + n - m)).2
        (h1.trans h2.symm)
    rcases Nat.even_or_odd (j - i) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h5 := hstepm m (by omega)
      rw [show j + n - m = (i + m) + n from by omega, hper] at h5
      exact hrevne _ (hfk (i + m)).1 (hfk (i + m)).2 h5
    · have h5 := hstepm (m + 1) (by omega)
      rw [show j + n - (m + 1) = (i + m) + n from by omega, hper] at h5
      rw [show i + (m + 1) = (i + m) + 1 from by omega, hfsucc (i + m)] at h5
      have h8 : (stepDart oside oend (f (i + m))).1 = (f (i + m)).1 := by
        have := congrArg Prod.fst h5
        exact this
      obtain ⟨hs, hv⟩ := hfk (i + m)
      have hvV := hvtx _ hs _ hv
      exact (hoside _ hvV _ hs hv).2.1 h8
  have hnodouble : ∀ i j, i < n → j < n → (f i).1 = (f j).1 → i = j := by
    intro i j hi hj hside
    by_contra hne'
    have hvne : (f i).2 ≠ (f j).2 := by
      intro h
      exact hne' (hinjres i j hi hj (Prod.ext hside h))
    have hrel : f j = revDart oend (f i) := by
      rcases htwoend _ (hfk i).1 (f i).2 (f j).2 (hfk i).2
        (by rw [hside]; exact (hfk j).2) with h | h
      · exact absurd h.symm hvne
      · exact Prod.ext hside.symm h
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hkey2 i j h hj hrel
    · have hrel' : f i = revDart oend (f j) := by
        rw [hrel, hrevrev _ (hfk i).1 (hfk i).2]
      exact hkey2 j i h hi hrel'
  have hCsub : (fun k => (f k).1) '' Set.Iio n ⊆ SS := by
    rintro s ⟨k, -, rfl⟩
    exact (hfk k).1
  have hCne : ((fun k => (f k).1) '' Set.Iio n).Nonempty := ⟨(f 0).1, 0, hn0, rfl⟩
  have hCclosed : ∀ s ∈ (fun k => (f k).1) '' Set.Iio n, ∀ v, Endp s v →
      oside v s ∈ (fun k => (f k).1) '' Set.Iio n := by
    rintro s ⟨k, hk, rfl⟩ v hv
    rcases htwoend _ (hfk k).1 _ v (hfk k).2 hv with h | h
    · refine ⟨(k + 1) % n, Nat.mod_lt _ hn0, ?_⟩
      show (f ((k + 1) % n)).1 = oside v (f k).1
      rw [congrArg Prod.fst (hmodlt (k + 1)), hfsucc k, h]
      rfl
    · have hstepk : stepDart oside oend (f (k + n - 1)) = f k := by
        rw [← hfsucc (k + n - 1), show (k + n - 1) + 1 = k + n from by omega, hper]
      obtain ⟨hs', hv'⟩ := hfk (k + n - 1)
      have hv'V := hvtx _ hs' _ hv'
      obtain ⟨ho1, ho2, ho3, ho4⟩ := hoside _ hv'V _ hs' hv'
      have hfst : (f k).1 = oside (f (k + n - 1)).2 (f (k + n - 1)).1 :=
        (congrArg Prod.fst hstepk).symm
      have hsnd : (f k).2 = oend (f k).1 (f (k + n - 1)).2 := by
        conv_lhs => rw [← hstepk]
        conv_rhs => rw [← hstepk]
        rfl
      have hEnd' : Endp (f k).1 (f (k + n - 1)).2 := by
        rw [hfst]
        exact ho3
      have hvd : v = (f (k + n - 1)).2 := by
        rw [h, hsnd, (hoend _ (hfk k).1 _ hEnd').2.2]
      have hgoal : oside v (f k).1 = (f (k + n - 1)).1 := by
        rw [hvd, hfst, ho4]
      refine ⟨(k + n - 1) % n, Nat.mod_lt _ hn0, ?_⟩
      show (f ((k + n - 1) % n)).1 = oside v (f k).1
      rw [congrArg Prod.fst (hmodlt (k + n - 1)), hgoal]
  have hall : SS ⊆ (fun k => (f k).1) '' Set.Iio n :=
    hconn _ hCsub hCne hCclosed
  refine ⟨n, f, hn0, hper, hfk, ?_, ?_⟩
  · intro s hs
    obtain ⟨k, hk, hks⟩ := hall hs
    refine ⟨k, ⟨Set.mem_Iio.mp hk, hks⟩, ?_⟩
    rintro k' ⟨hk', hks'⟩
    exact hnodouble k' k hk' (Set.mem_Iio.mp hk) (hks'.trans hks.symm)
  · intro k
    rw [hfsucc k]
    rfl

/-- The basepoint lies on no side. -/
theorem basepoint_notMem_side (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) : τ₀ ∉ s := by
  intro hcon
  have hfr : τ₀ ∈ frontier (dirichletDomain Γ τ₀) := by
    rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
    exact ⟨s, hs, hcon⟩
  rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hfr
  exact hfr.2 (basepoint_mem_interior_dirichletDomain hε hgap)

/-- A common point of two distinct sides is a vertex and an endpoint of both. -/
theorem shared_point_endpoint (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s s' : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀)
    (hne : s ≠ s') {p : UpperHalfPlane} (hp : p ∈ s) (hp' : p ∈ s') :
    p ∈ polygonVertices Γ τ₀ ∧ IsSegEndpoint s p ∧ IsSegEndpoint s' p := by
  have hpv : p ∈ polygonVertices Γ τ₀ := by
    obtain ⟨γ, hγ, hsdef⟩ := hs
    obtain ⟨δ, hδ, hsdef'⟩ := hs'
    have hpS : p ∈ dirichletSideSet Γ τ₀ γ := hsdef ▸ hp
    have hpS' : p ∈ dirichletSideSet Γ τ₀ δ := hsdef' ▸ hp'
    have hγδ : γ • τ₀ ≠ δ • τ₀ := fun h =>
      hne (by rw [hsdef, hsdef', sideSet_eq_of_basepoint_eq h])
    have hfin : (tileCenters Γ τ₀ p).Finite := (finite_contactSet hΓ τ₀ p).image _
    refine ⟨hpS.1, (Set.two_lt_ncard hfin).mpr
      ⟨τ₀, ⟨1, one_mem_contactSet hpS.1, one_smul _ _⟩,
        γ • τ₀, ⟨γ, mem_contactSet_of_mem_sideSet hpS, rfl⟩,
        δ • τ₀, ⟨δ, mem_contactSet_of_mem_sideSet hpS', rfl⟩,
        Ne.symm hγ.1, Ne.symm hδ.1, hγδ⟩⟩
  exact ⟨hpv, isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hpv hs hp,
    isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hpv hs' hp'⟩

/-- Cones over sides are closed. -/
theorem isClosed_geodCone_side (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) :
    IsClosed (geodCone τ₀ s) := by
  obtain ⟨a, b, hab, heq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  rw [heq]
  exact (isCompact_hyperbolicTriangle τ₀ a b).isClosed

/-- A nonempty family of sides closed under passing to the second side at any endpoint
exhausts the sides. -/
theorem sides_connected (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (oside : UpperHalfPlane → Set UpperHalfPlane → Set UpperHalfPlane)
    (huniq : ∀ v ∈ polygonVertices Γ τ₀, ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v →
      ∀ s' ∈ polygonSides Γ τ₀, IsSegEndpoint s' v → s' ≠ s → s' = oside v s)
    (C : Set (Set UpperHalfPlane)) (hCsub : C ⊆ polygonSides Γ τ₀) (hCne : C.Nonempty)
    (hCcl : ∀ s ∈ C, ∀ v, IsSegEndpoint s v → oside v s ∈ C) :
    polygonSides Γ τ₀ ⊆ C := by
  classical
  intro sx hsx
  by_contra hsC
  have hr : 0 < ε / 2 := by linarith
  have hAcl : IsClosed (⋃ t ∈ C, geodCone τ₀ t) :=
    Set.Finite.isClosed_biUnion
      ((finite_polygonSides hΓ hfree hε hgap hdense).subset hCsub)
      (fun t ht => isClosed_geodCone_side hΓ hfree hε hgap hdense (hCsub ht))
  have hBcl : IsClosed (⋃ t ∈ polygonSides Γ τ₀ \ C, geodCone τ₀ t) :=
    Set.Finite.isClosed_biUnion
      ((finite_polygonSides hΓ hfree hε hgap hdense).subset fun t ht => ht.1)
      (fun t ht => isClosed_geodCone_side hΓ hfree hε hgap hdense ht.1)
  have hcov : Metric.ball τ₀ (ε / 2) \ {τ₀} ⊆
      (⋃ t ∈ C, geodCone τ₀ t) ∪ ⋃ t ∈ polygonSides Γ τ₀ \ C, geodCone τ₀ t := by
    rintro x ⟨hxB, -⟩
    have hxD : x ∈ dirichletDomain Γ τ₀ := ball_subset_dirichletDomain hε hgap hxB
    rw [dirichletDomain_eq_biUnion_geodCone hΓ hfree hε hgap hdense] at hxD
    rw [Set.mem_iUnion₂] at hxD
    obtain ⟨t, ht, hxt⟩ := hxD
    by_cases htC : t ∈ C
    · exact Or.inl (Set.mem_biUnion htC hxt)
    · exact Or.inr (Set.mem_biUnion ⟨ht, htC⟩ hxt)
  have hdisj : (⋃ t ∈ C, geodCone τ₀ t) ∩
      (⋃ t ∈ polygonSides Γ τ₀ \ C, geodCone τ₀ t) ⊆ {τ₀} := by
    rintro x ⟨hxA, hxB⟩
    rw [Set.mem_iUnion₂] at hxA hxB
    obtain ⟨t, htC, hxt⟩ := hxA
    obtain ⟨t', ht', hxt'⟩ := hxB
    by_contra hxτ
    have hxτ' : x ≠ τ₀ := fun h => hxτ (h ▸ rfl)
    have htne : t ≠ t' := fun h => ht'.2 (h ▸ htC)
    obtain ⟨p, ⟨hpt, hpt'⟩, -⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense
      (hCsub htC) ht'.1 hxt hxt' hxτ'
    obtain ⟨hpv, hpe, hpe'⟩ := shared_point_endpoint hΓ hfree hε hgap hdense
      (hCsub htC) ht'.1 htne hpt hpt'
    have ht'os : t' = oside p t :=
      huniq p hpv t (hCsub htC) hpe t' ht'.1 hpe' (Ne.symm htne)
    exact ht'.2 (ht'os ▸ hCcl t htC p hpe)
  have hpick : ∀ t ∈ polygonSides Γ τ₀,
      ((geodCone τ₀ t) ∩ (Metric.ball τ₀ (ε / 2) \ {τ₀})).Nonempty := by
    intro t ht
    obtain ⟨a, b, hab, heq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense ht
    have haT : a ∈ t := by rw [heq]; exact left_mem_geodSeg a b
    have haτ : a ≠ τ₀ := fun h =>
      basepoint_notMem_side hΓ hfree hε hgap hdense ht (h ▸ haT)
    obtain ⟨w, hwseg, hwτ, hwd⟩ := exists_near_on_geodSeg haτ hr
    refine ⟨w, mem_geodCone.mpr ⟨a, haT, by rwa [geodSeg_comm]⟩,
      Metric.mem_ball.mpr hwd, fun hc => hwτ (Set.mem_singleton_iff.mp hc)⟩
  obtain ⟨t₀, ht₀⟩ := hCne
  obtain ⟨wA, hwA1, hwA2⟩ := hpick t₀ (hCsub ht₀)
  obtain ⟨wB, hwB1, hwB2⟩ := hpick sx hsx
  exact punctured_ball_two_closed hr hAcl hBcl hcov hdisj
    ⟨wA, Set.mem_biUnion ht₀ hwA1, hwA2⟩ ⟨wB, Set.mem_biUnion ⟨hsx, hsC⟩ hwB1, hwB2⟩

/-- **Cyclic boundary order**: the sides admit a cyclic enumeration in which consecutive
sides share an endpoint vertex. -/
theorem exists_boundary_side_cycle (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ (n : ℕ) (e : ℕ → Set UpperHalfPlane), 0 < n ∧ (∀ k, e (k + n) = e k) ∧
      (∀ k, e k ∈ polygonSides Γ τ₀) ∧
      (∀ s ∈ polygonSides Γ τ₀, ∃! k, k < n ∧ e k = s) ∧
      ∀ k, ∃ v ∈ polygonVertices Γ τ₀, IsSegEndpoint (e k) v ∧ IsSegEndpoint (e (k + 1)) v := by
  classical
  have hends := fun s (hs : s ∈ polygonSides Γ τ₀) =>
    exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  choose! ep1 ep2 hepne hepeq using hends
  have htwo := fun v (hv : v ∈ polygonVertices Γ τ₀) =>
    exists_two_sides_at_vertex hΓ hfree hε hgap hdense hv
  choose! t1 ht1 t2 ht2 h12 hbe1 hbe2 hbuniq using htwo
  set oendF : Set UpperHalfPlane → UpperHalfPlane → UpperHalfPlane :=
    fun s v => if v = ep1 s then ep2 s else ep1 s with hoendF
  set osideF : UpperHalfPlane → Set UpperHalfPlane → Set UpperHalfPlane :=
    fun v s => if s = t1 v then t2 v else t1 v with hosideF
  have hoendF1 : ∀ s v, v = ep1 s → oendF s v = ep2 s := by
    intro s v h
    simp only [hoendF]
    rw [if_pos h]
  have hoendF2 : ∀ s v, v ≠ ep1 s → oendF s v = ep1 s := by
    intro s v h
    simp only [hoendF]
    rw [if_neg h]
  have hosideF1 : ∀ v s, s = t1 v → osideF v s = t2 v := by
    intro v s h
    simp only [hosideF]
    rw [if_pos h]
  have hosideF2 : ∀ v s, s ≠ t1 v → osideF v s = t1 v := by
    intro v s h
    simp only [hosideF]
    rw [if_neg h]
  have hEiff : ∀ s ∈ polygonSides Γ τ₀, ∀ v : UpperHalfPlane,
      IsSegEndpoint s v ↔ (v = ep1 s ∨ v = ep2 s) := by
    intro s hs v
    conv_lhs => rw [hepeq s hs]
    exact isSegEndpoint_geodSeg_iff (hepne s hs)
  have hvtxP : ∀ s ∈ polygonSides Γ τ₀, ∀ v, IsSegEndpoint s v →
      v ∈ polygonVertices Γ τ₀ :=
    fun s hs v hv => mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs hv
  have hoendP : ∀ s ∈ polygonSides Γ τ₀, ∀ v, IsSegEndpoint s v →
      IsSegEndpoint s (oendF s v) ∧ oendF s v ≠ v ∧ oendF s (oendF s v) = v := by
    intro s hs v hv
    have hne := hepne s hs
    by_cases h1 : v = ep1 s
    · rw [hoendF1 s v h1]
      refine ⟨(hEiff s hs _).mpr (Or.inr rfl), by rw [h1]; exact Ne.symm hne, ?_⟩
      rw [hoendF2 s (ep2 s) (Ne.symm hne), h1]
    · have h2 : v = ep2 s := ((hEiff s hs v).mp hv).resolve_left h1
      rw [hoendF2 s v h1]
      refine ⟨(hEiff s hs _).mpr (Or.inl rfl), by rw [h2]; exact hne, ?_⟩
      rw [hoendF1 s (ep1 s) rfl, h2]
  have htwoendP : ∀ s ∈ polygonSides Γ τ₀, ∀ v w, IsSegEndpoint s v → IsSegEndpoint s w →
      w = v ∨ w = oendF s v := by
    intro s hs v w hv hw
    rcases (hEiff s hs v).mp hv with h1 | h1 <;> rcases (hEiff s hs w).mp hw with h2 | h2
    · exact Or.inl (h2.trans h1.symm)
    · refine Or.inr ?_
      rw [hoendF1 s v h1, h2]
    · refine Or.inr ?_
      rw [hoendF2 s v (fun hc => (hepne s hs) (hc.symm.trans h1)), h2]
    · exact Or.inl (h2.trans h1.symm)
  have hosideP : ∀ v ∈ polygonVertices Γ τ₀, ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v →
      osideF v s ∈ polygonSides Γ τ₀ ∧ osideF v s ≠ s ∧ IsSegEndpoint (osideF v s) v ∧
        osideF v (osideF v s) = s := by
    intro v hv s hs hEnd
    by_cases h1 : s = t1 v
    · rw [hosideF1 v s h1]
      refine ⟨ht2 v hv, by rw [h1]; exact Ne.symm (h12 v hv), hbe2 v hv, ?_⟩
      rw [hosideF2 v (t2 v) (Ne.symm (h12 v hv)), h1]
    · have h2 : s = t2 v := (hbuniq v hv s hs hEnd).resolve_left h1
      rw [hosideF2 v s h1]
      refine ⟨ht1 v hv, by rw [h2]; exact h12 v hv, hbe1 v hv, ?_⟩
      rw [hosideF1 v (t1 v) rfl, h2]
  have hosuniq : ∀ v ∈ polygonVertices Γ τ₀, ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v →
      ∀ s' ∈ polygonSides Γ τ₀, IsSegEndpoint s' v → s' ≠ s → s' = osideF v s := by
    intro v hv s hs hE s' hs' hE' hne'
    rcases hbuniq v hv s hs hE with h1 | h1 <;>
      rcases hbuniq v hv s' hs' hE' with h2 | h2
    · exact absurd (h2.trans h1.symm) hne'
    · rw [hosideF1 v s h1, h2]
    · rw [hosideF2 v s (fun hc => h12 v hv (hc.symm.trans h1)), h2]
    · exact absurd (h2.trans h1.symm) hne'
  obtain ⟨s₀, hs₀, -, -, -⟩ :=
    exists_exit hΓ hfree hε hgap hdense basepoint_mem_dirichletDomain
  have hv₀ : IsSegEndpoint s₀ (ep1 s₀) := (hEiff s₀ hs₀ _).mpr (Or.inl rfl)
  obtain ⟨n, F, hn0, hper, hdart, hexu, hstep⟩ :=
    two_regular_cycle (finite_polygonSides hΓ hfree hε hgap hdense) IsSegEndpoint
      oendF osideF hvtxP hoendP htwoendP hosideP
      (sides_connected hΓ hfree hε hgap hdense osideF hosuniq) hs₀ hv₀
  refine ⟨n, fun k => (F k).1, hn0, fun k => congrArg Prod.fst (hper k),
    fun k => (hdart k).1, fun s hs => hexu s hs, ?_⟩
  intro k
  refine ⟨(F k).2, hvtxP _ (hdart k).1 _ (hdart k).2, (hdart k).2, ?_⟩
  show IsSegEndpoint (F (k + 1)).1 (F k).2
  rw [hstep k]
  exact (hosideP _ (hvtxP _ (hdart k).1 _ (hdart k).2) _ (hdart k).1 (hdart k).2).2.2.1

end RiemannDynamics
