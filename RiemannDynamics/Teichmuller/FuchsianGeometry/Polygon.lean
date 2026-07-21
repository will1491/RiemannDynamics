import RiemannDynamics.Teichmuller.FuchsianGeometry.Dirichlet
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

/-! ## Interior angles -/

/-- `θ` is the **interior angle** of the Dirichlet polygon at `v`: the sector angle at `v`
between the two sides meeting there, measured toward any of their points other than `v`. -/
def IsInteriorAngleAt (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (v : UpperHalfPlane) (θ : ℝ) : Prop :=
  ∃ s₁ ∈ polygonSides Γ τ₀, ∃ s₂ ∈ polygonSides Γ τ₀, s₁ ≠ s₂ ∧
    IsSegEndpoint s₁ v ∧ IsSegEndpoint s₂ v ∧
    ∃ w₁ ∈ s₁, ∃ w₂ ∈ s₂, w₁ ≠ v ∧ w₂ ≠ v ∧ θ = sectorAngle v w₁ w₂

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
  JoinedIn.of_segment_subset fun _w hw =>
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
        Complex.zero_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at h6
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
        Complex.zero_re, Complex.zero_im, mul_zero, mul_one, sub_zero,
        zero_sub, add_zero, neg_eq_zero] at h5
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
  push Not at hcon
  have hxint : x ∈ interior S := by
    have h1 : x ∈ closure S := subset_closure hx
    have h2 := hcon x (left_mem_geodSeg x y)
    rw [frontier, Set.mem_diff] at h2
    push Not at h2
    exact h2 h1
  have hyext : y ∈ (closure S)ᶜ := by
    intro h1
    have h2 := hcon y (right_mem_geodSeg x y)
    rw [frontier, Set.mem_diff] at h2
    push Not at h2
    exact hy (interior_subset (h2 h1))
  have hcover : geodSeg x y ⊆ interior S ∪ (closure S)ᶜ := by
    intro w hw
    by_cases h1 : w ∈ closure S
    · left
      have h2 := hcon w hw
      rw [frontier, Set.mem_diff] at h2
      push Not at h2
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

/-! ## The structure of sides and vertices -/

/-- The sides are finitely many: a side constrains the domain, so its element lies in the
finite active-side set of the density radius. -/
theorem finite_polygonSides (hΓ : IsFuchsianGroup Γ)
    (_hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
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
  change dist τ₀ (γ • τ₀) ≤ 2 * R + 1
  linarith

/-- A nondegenerate side determines the orbit point of its element: two points of the side
lie on both perpendicular bisectors, which then coincide, and a bisector determines the
reflected center. -/
theorem smul_basepoint_eq_of_sideSet_eq (_hΓ : IsFuchsianGroup Γ)
    (_hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
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
theorem exists_geodSeg_of_polygonSide (_hΓ : IsFuchsianGroup Γ)
    (_hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
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
    (_hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
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
      change dist τ₀ (δ • τ₀) ≤ 2 * R + 1
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
theorem punctured_ball_two_closed {z : UpperHalfPlane} {r : ℝ} (_hr : 0 < r)
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
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
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
  push Not at hlt
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
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
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
      push Not at hex
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
  push Not at hlt
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
    (_hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    (z : UpperHalfPlane) : dist z p < dist z q ↔ ε' * (g • z).re < 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd ((hge z).mpr hc) (not_le.mpr h)
  · intro h
    by_contra hc
    push Not at hc
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
  push Not at hcon
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
    push Not at hc
    nlinarith [hL31, hL21, hE1]
  have hαneg : α < 0 := by
    by_contra hc
    push Not at hc
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
    push Not at hcon
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
  push Not at hcon
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

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

theorem contact_shift (g δ : ↥Γ) (z : UpperHalfPlane) :
    δ ∈ contactSet Γ τ₀ z ↔ (g * δ) ∈ contactSet Γ τ₀ (g • z) := by
  rw [mem_contactSet_iff_mem_smul_dirichletDomain,
    mem_contactSet_iff_mem_smul_dirichletDomain]
  constructor
  · rintro ⟨u, hu, huz⟩
    refine ⟨u, hu, ?_⟩
    change (g * δ) • u = g • z
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
    change γ⁻¹ • (γ * δ) • τ₀ = δ • τ₀
    rw [mul_smul, inv_smul_smul]
  · rintro ⟨c', ⟨δ, hδ, rfl⟩, rfl⟩
    refine ⟨γ⁻¹ * δ, (contact_shift γ⁻¹ δ v).mp hδ, ?_⟩
    change (γ⁻¹ * δ) • τ₀ = γ⁻¹ • δ • τ₀
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
      change ((rep p)⁻¹ * rep q) • u' = (rep p)⁻¹ • w
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

/-! ## The vertex star -/

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
    change rep (e₀ (k + n)) = rep (e₀ k)
    rw [hper k]
  · intro k
    exact hrep₁ _ (heP k)
  · intro γ hγ
    have hγP : γ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨γ, hγ, rfl⟩
    obtain ⟨k, ⟨hk, hek⟩, hkuniq⟩ := huniq (γ • τ₀) hγP
    refine ⟨k, ⟨hk, ?_⟩, ?_⟩
    · change γ • τ₀ = rep (e₀ k) • τ₀
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
theorem exists_vertex_star_bijection (_hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
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
    change Φ (γ • τ₀) ∈ _
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
    change γ₁ • τ₀ = γ₂ • τ₀
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
      · change η⁻¹ • η • v = v
        rw [inv_smul_smul]
    refine ⟨η⁻¹ • τ₀, ⟨η⁻¹, hcon, rfl⟩, ?_⟩
    show Φ (η⁻¹ • τ₀) = v'
    rw [hΦ η⁻¹ hcon, inv_inv, hη]
  exact ⟨Φ, ⟨hmaps, hinj, hsurj⟩, hΦ⟩

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

/-! ## The fan decomposition -/

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
    rw [abs_arg_conj_of_im_ne hAB.ne, abs_arg_conj_of_im_ne hA.ne,
      abs_arg_conj_of_im_ne hB.ne] at h1
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
theorem sectorAngle_eq_add_basepoint (_hΓ : IsFuchsianGroup Γ)
    (_hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (_hv : v ∈ polygonVertices Γ τ₀)
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
    change (s, oend s (oend s v)) = (s, v)
    rw [(hoend s hs v hv).2.2]
  have hconj : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      stepDart oside oend (revDart oend (stepDart oside oend d))
        = revDart oend d := by
    rintro ⟨s, v⟩ hs hv
    have hvV : v ∈ V := hvtx s hs v hv
    obtain ⟨h1, h2, h3, h4⟩ := hoside v hvV s hs hv
    have e1 : oend (oside v s) (oend (oside v s) v) = v := (hoend _ h1 v h3).2.2
    change stepDart oside oend
        (oside v s, oend (oside v s) (oend (oside v s) v)) = (s, oend s v)
    rw [e1]
    change (oside v (oside v s), oend (oside v (oside v s)) v) = (s, oend s v)
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
      change (f ((k + 1) % n)).1 = oside v (f k).1
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
      change (f ((k + n - 1) % n)).1 = oside v (f k).1
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
  change IsSegEndpoint (F (k + 1)).1 (F k).2
  rw [hstep k]
  exact (hosideP _ (hvtxP _ (hdart k).1 _ (hdart k).2) _ (hdart k).1 (hdart k).2).2.2.1

/-- A special linear matrix squaring to the identity is central: `A² = 1` forces `A = ±1`. -/
theorem eq_pm_one_of_sq_eq_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) = 1) :
    (A : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, (A : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe A
    rwa [hM, Matrix.det_fin_two_of] at h1
  rw [hM, Matrix.mul_fin_two] at h
  have h00 : a * a + b * c = 1 := by
    have h2 := congrFun (congrFun h 0) 0
    simpa using h2
  have h01 : a * b + b * d = 0 := by
    have h2 := congrFun (congrFun h 0) 1
    simpa using h2
  have h10 : c * a + d * c = 0 := by
    have h2 := congrFun (congrFun h 1) 0
    simpa using h2
  have h11 : c * b + d * d = 1 := by
    have h2 := congrFun (congrFun h 1) 1
    simpa using h2
  by_cases had : a + d = 0
  · exfalso
    nlinarith [h00, hdet, sq_nonneg (a - d), sq_nonneg (a + d)]
  · have hb : b = 0 := by
      have h2 : b * (a + d) = 0 := by linarith [h01]
      exact (mul_eq_zero.mp h2).resolve_right had
    have hc : c = 0 := by
      have h2 : c * (a + d) = 0 := by linarith [h10]
      exact (mul_eq_zero.mp h2).resolve_right had
    rw [hb, hc] at h00 h11 hdet
    have ha1 : a = 1 ∨ a = -1 := by
      rcases mul_self_eq_one_iff.mp (by linarith [h00] : a * a = 1) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr h3
    have hda : d = a := by
      rcases ha1 with h3 | h3 <;> nlinarith [hdet, h11]
    rcases ha1 with h3 | h3
    · left
      rw [hM, hb, hc, hda, h3, ← Matrix.one_fin_two]
    · right
      rw [hM, hb, hc, hda, h3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]

/-- A special linear matrix squaring to minus the identity is elliptic: it fixes a point of
the upper half plane. -/
theorem exists_fixed_of_sq_eq_neg_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) = -1) :
    ∃ τ : UpperHalfPlane, A • τ = τ := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, (A : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe A
    rwa [hM, Matrix.det_fin_two_of] at h1
  rw [hM, Matrix.mul_fin_two] at h
  have h00 : a * a + b * c = -1 := by
    have h2 := congrFun (congrFun h 0) 0
    simpa using h2
  have h01 : a * b + b * d = 0 := by
    have h2 := congrFun (congrFun h 0) 1
    simpa using h2
  have h10 : c * a + d * c = 0 := by
    have h2 := congrFun (congrFun h 1) 0
    simpa using h2
  have had : a + d = 0 := by
    by_contra had
    have hb : b = 0 := by
      have h2 : b * (a + d) = 0 := by linarith [h01]
      exact (mul_eq_zero.mp h2).resolve_right had
    have hc : c = 0 := by
      have h2 : c * (a + d) = 0 := by linarith [h10]
      exact (mul_eq_zero.mp h2).resolve_right had
    rw [hb, hc] at h00
    nlinarith [h00, sq_nonneg a]
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0] at h00 hdet
    nlinarith [h00, sq_nonneg a, hdet]
  have habs : 0 < |c| := abs_pos.mpr hc
  have hy₀ : (0 : ℝ) < 1 / |c| := by positivity
  have hz : (0 : ℝ) < ((⟨a / c, 1 / |c|⟩ : ℂ)).im := hy₀
  set τz : UpperHalfPlane := UpperHalfPlane.mk ⟨a / c, 1 / |c|⟩ hz with hτz
  have hcoez : (τz : ℂ) = ⟨a / c, 1 / |c|⟩ := rfl
  refine ⟨τz, ?_⟩
  have hA00 : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = a := by rw [hM]; rfl
  have hA01 : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b := by rw [hM]; rfl
  have hA10 : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = c := by rw [hM]; rfl
  have hA11 : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = d := by rw [hM]; rfl
  have hden : ((c : ℝ) : ℂ) * (τz : ℂ) + ((d : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, zero_mul, add_zero] at h1
    rw [hcoez] at h1
    have h2 : c * (1 / |c|) = 0 := by simpa using h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact absurd h3 (by positivity)
  apply UpperHalfPlane.ext
  rw [coe_smul, hA00, hA01, hA10, hA11, div_eq_iff hden]
  have hZ : (τz : ℂ) = ((a / c : ℝ) : ℂ) + ((1 / |c| : ℝ) : ℂ) * Complex.I := by
    rw [hcoez]
    apply Complex.ext
    · simp
    · simp only [one_div, Complex.ofReal_div, Complex.ofReal_inv, Complex.add_im,
        Complex.div_ofReal_im, Complex.ofReal_im, zero_div, Complex.mul_im, Complex.inv_re,
        Complex.ofReal_re, Complex.normSq_ofReal, abs_mul_abs_self, Complex.I_im, mul_one,
        Complex.inv_im, neg_zero, Complex.I_re, mul_zero, add_zero, zero_add]
      rw [← abs_mul_abs_self c]
      field_simp
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have h₁ : ((c : ℝ) : ℂ) * ((a / c : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  have h₂ : ((c : ℝ) : ℂ) ^ 2 * ((1 / |c| : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [show c ^ 2 * (1 / |c|) ^ 2 = c ^ 2 / |c| ^ 2 by ring, sq_abs]
    rw [div_self (by positivity : c ^ 2 ≠ (0 : ℝ))]
    norm_num
  have h₃ : ((b : ℝ) : ℂ) * ((c : ℝ) : ℂ) = -1 - ((a : ℝ) : ℂ) * ((a : ℝ) : ℂ) := by
    have hbc : b * c = -1 - a * a := by linarith [h00]
    rw [← Complex.ofReal_mul, hbc]
    push_cast
    ring
  have h₄ : ((d : ℝ) : ℂ) = -((a : ℝ) : ℂ) := by
    have : d = -a := by linarith [had]
    rw [this]
    push_cast
    ring
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  refine mul_left_cancel₀ hcC ?_
  rw [hZ, h₄]
  linear_combination (-(((c : ℝ) : ℂ) * ((a / c : ℝ) : ℂ) - ((a : ℝ) : ℂ))
      - 2 * ((c : ℝ) : ℂ) * ((1 / |c| : ℝ) : ℂ) * Complex.I) * h₁
    + h₃ + (-(Complex.I ^ 2)) * h₂ + (-1) * hI

/-! ## The side pairing is a fixed-point-free involution -/

/-- No side is paired with itself: a self-paired side forces `γ² • τ₀ = τ₀`, so `γ²` acts
trivially, and `γ² = 1` gives `γ = ±1` while `γ² = -1` gives a zero trace, an elliptic
element with a fixed point — both excluded. -/
theorem dirichletSideSet_inv_ne (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {γ : ↥Γ} (h : IsSideElement Γ τ₀ γ) :
    dirichletSideSet Γ τ₀ γ⁻¹ ≠ dirichletSideSet Γ τ₀ γ := by
  intro heq
  have h1 : γ⁻¹ • τ₀ = γ • τ₀ := smul_basepoint_eq_of_sideSet_eq hΓ hfree h.inv h heq
  have h2 : (γ * γ) • τ₀ = τ₀ := by
    rw [mul_smul, ← h1, smul_inv_smul]
  have h3 : ∀ τ' : UpperHalfPlane, (γ * γ) • τ' = τ' := hfree (γ * γ) ⟨τ₀, h2⟩
  have h4 : ∀ τ' : UpperHalfPlane,
      ((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ' = τ' := by
    intro τ'
    rw [← Subgroup.smul_def]
    exact h3 τ'
  have hcoe : ((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      = (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    rfl
  have htriv : γ • τ₀ ≠ τ₀ := h.1
  rcases (smul_id_iff_pm_one _).mp h4 with h5 | h5
  · -- `γ² = 1`: then `γ = ±1` acts trivially, contradicting the side element moving `τ₀`.
    have h6 : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← hcoe]
      exact h5
    have h7 := (smul_eq_self_of_pm_one _ (eq_pm_one_of_sq_eq_one _ h6)).1 τ₀
    rw [← Subgroup.smul_def] at h7
    exact htriv h7
  · -- `γ² = -1`: elliptic, with an interior fixed point; freeness makes `γ` trivial.
    have h6 : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← hcoe]
      exact h5
    obtain ⟨τf, hτf⟩ := exists_fixed_of_sq_eq_neg_one _ h6
    have h7 : γ • τf = τf := by
      rw [Subgroup.smul_def]
      exact hτf
    exact htriv (hfree γ ⟨τf, h7⟩ τ₀)

/-- Equal basepoint images give equal inverse side sets. -/
theorem sideSet_inv_congr
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀) :
    dirichletSideSet Γ τ₀ γ⁻¹ = dirichletSideSet Γ τ₀ δ⁻¹ :=
  sideSet_eq_of_basepoint_eq (inv_smul_eq_of_basepoint_eq hfree h τ₀)

/-- Each side pair is contained in the side set. -/
theorem pair_subset_sides {P : Set (Set UpperHalfPlane)}
    (hP : P ∈ polygonSidePairs Γ τ₀) : P ⊆ polygonSides Γ τ₀ := by
  obtain ⟨γ, hγ, rfl⟩ := hP
  rintro s (rfl | hs)
  · exact ⟨γ, hγ, rfl⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨γ⁻¹, hγ.inv, rfl⟩

/-- The side pairs are finitely many. -/
theorem finite_polygonSidePairs (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSidePairs Γ τ₀).Finite :=
  ((finite_polygonSides hΓ hfree hε hgap hdense).finite_subsets).subset
    fun _ hP => pair_subset_sides hP

/-- Two side pairs sharing a side coincide. -/
theorem pair_eq_of_shared (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ) (hδ : IsSideElement Γ τ₀ δ)
    {s : Set UpperHalfPlane}
    (hs₁ : s ∈ ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} :
      Set (Set UpperHalfPlane)))
    (hs₂ : s ∈ ({dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} :
      Set (Set UpperHalfPlane))) :
    ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} := by
  rcases hs₁ with rfl | hs₁
  · rcases hs₂ with heq | hs₂
    · have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ heq
      rw [sideSet_eq_of_basepoint_eq hbase, sideSet_inv_congr hfree hbase]
    · rw [Set.mem_singleton_iff] at hs₂
      have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ.inv hs₂
      have hbase' : γ⁻¹ • τ₀ = δ • τ₀ := by
        have h1 := inv_smul_eq_of_basepoint_eq hfree hbase τ₀
        rwa [inv_inv] at h1
      rw [sideSet_eq_of_basepoint_eq hbase, sideSet_eq_of_basepoint_eq hbase',
        Set.pair_comm]
  · rw [Set.mem_singleton_iff] at hs₁
    subst hs₁
    rcases hs₂ with heq | hs₂
    · have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ.inv hδ heq
      have hbase' : γ • τ₀ = δ⁻¹ • τ₀ := by
        have h1 := inv_smul_eq_of_basepoint_eq hfree hbase τ₀
        rwa [inv_inv] at h1
      rw [sideSet_eq_of_basepoint_eq hbase, sideSet_eq_of_basepoint_eq hbase',
        Set.pair_comm]
    · rw [Set.mem_singleton_iff] at hs₂
      have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ.inv hδ.inv hs₂
      have hbase' : γ • τ₀ = δ • τ₀ := by
        have h1 := inv_smul_eq_of_basepoint_eq hfree hbase τ₀
        rwa [inv_inv, inv_inv] at h1
      rw [sideSet_eq_of_basepoint_eq hbase', sideSet_inv_congr hfree hbase']

/-- The polygon has `2m` sides: the fixed-point-free pairing matches the sides in `m`
two-element pairs. -/
theorem ncard_polygonSides (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSides Γ τ₀).ncard = 2 * polygonSideCount Γ τ₀ := by
  classical
  have hSfin := finite_polygonSides hΓ hfree hε hgap hdense
  have hPfin := finite_polygonSidePairs hΓ hfree hε hgap hdense
  set 𝒮 : Finset (Set UpperHalfPlane) := hSfin.toFinset with h𝒮
  set 𝒬 : Finset (Set (Set UpperHalfPlane)) := hPfin.toFinset with h𝒬
  have hfilter : ∀ P ∈ 𝒬, (↑(𝒮.filter (· ∈ P)) : Set (Set UpperHalfPlane)) = P := by
    intro P hP
    have hPmem : P ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hP
      exact hP
    ext s
    simp only [Finset.coe_filter, Set.mem_setOf_eq, h𝒮, Set.Finite.mem_toFinset]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨pair_subset_sides hPmem h1, h1⟩⟩
  have hcard2 : ∀ P ∈ 𝒬, (𝒮.filter (· ∈ P)).card = 2 := by
    intro P hP
    have hPmem : P ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hP
      exact hP
    obtain ⟨γ, hγ, hPdef⟩ := hPmem
    rw [← Set.ncard_coe_finset, hfilter P hP, hPdef]
    exact Set.ncard_pair
      (Ne.symm (dirichletSideSet_inv_ne hΓ hfree hε hgap hdense hγ))
  have hbi : 𝒮 = 𝒬.biUnion (fun P => 𝒮.filter (· ∈ P)) := by
    ext s
    constructor
    · intro hs
      have hsS : s ∈ polygonSides Γ τ₀ := by
        rw [h𝒮, Set.Finite.mem_toFinset] at hs
        exact hs
      obtain ⟨γ, hγ, hsdef⟩ := hsS
      have hQ' : ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} :
          Set (Set UpperHalfPlane)) ∈ 𝒬 := by
        rw [h𝒬, Set.Finite.mem_toFinset]
        exact ⟨γ, hγ, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨_, hQ', ?_⟩
      have hgoal : s ∈ 𝒮 ∧ s ∈ ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} :
          Set (Set UpperHalfPlane)) := ⟨hs, by rw [hsdef]; exact Set.mem_insert _ _⟩
      simp only [Finset.mem_filter]
      exact hgoal
    · intro hs
      obtain ⟨P, -, hsP⟩ := Finset.mem_biUnion.mp hs
      exact (Finset.filter_subset _ _) hsP
  have hdisj : ∀ P ∈ 𝒬, ∀ Q ∈ 𝒬, P ≠ Q →
      Disjoint (𝒮.filter (· ∈ P)) (𝒮.filter (· ∈ Q)) := by
    intro P hP Q hQ hPQ
    rw [Finset.disjoint_left]
    intro s hsP hsQ
    apply hPQ
    have hPmem : P ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hP
      exact hP
    have hQmem : Q ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hQ
      exact hQ
    obtain ⟨γ, hγ, hPdef⟩ := hPmem
    obtain ⟨δ, hδ, hQdef⟩ := hQmem
    have h1 : s ∈ P := (Finset.mem_filter.mp hsP).2
    have h2 : s ∈ Q := (Finset.mem_filter.mp hsQ).2
    rw [hPdef] at h1 ⊢
    rw [hQdef] at h2 ⊢
    exact pair_eq_of_shared hΓ hfree hγ hδ h1 h2
  have e1 : (polygonSides Γ τ₀).ncard = 𝒮.card := by
    rw [← Set.ncard_coe_finset 𝒮, h𝒮, Set.Finite.coe_toFinset]
  have e2 : polygonSideCount Γ τ₀ = 𝒬.card := by
    rw [polygonSideCount, ← Set.ncard_coe_finset 𝒬, h𝒬, Set.Finite.coe_toFinset]
  rw [e1, e2, hbi, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard2,
    Finset.sum_const, smul_eq_mul, mul_comm]

/-- The polygon has at least one side. -/
theorem exists_polygonSide (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ s, s ∈ polygonSides Γ τ₀ := by
  obtain ⟨y, hy⟩ := exists_notMem_dirichletDomain hdense
  obtain ⟨w, -, hwfr⟩ := exists_frontier_mem_geodSeg basepoint_mem_dirichletDomain hy
  rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense] at hwfr
  obtain ⟨s, hs, -⟩ := hwfr
  exact ⟨s, hs⟩

/-- The polygon has at least one side pair: the orbit of the basepoint is dense, so the
group acts nontrivially and the domain is a proper subset of the plane. -/
theorem polygonSideCount_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    0 < polygonSideCount Γ τ₀ := by
  obtain ⟨s, hs⟩ := exists_polygonSide hΓ hfree hε hgap hdense
  obtain ⟨γ, hγ, -⟩ := hs
  rw [polygonSideCount]
  rw [Set.ncard_pos (finite_polygonSidePairs hΓ hfree hε hgap hdense)]
  exact ⟨_, γ, hγ, rfl⟩

/-- The polygon has at least one vertex class: the compact domain has a frontier, the
frontier is a union of segments, and segments have endpoints. -/
theorem polygonVertexClassCount_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    0 < polygonVertexClassCount Γ τ₀ := by
  obtain ⟨s, hs⟩ := exists_polygonSide hΓ hfree hε hgap hdense
  obtain ⟨a, b, hab, hseq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  have hend : IsSegEndpoint s a := by
    rw [hseq]
    exact (isSegEndpoint_geodSeg_iff hab).mpr (Or.inl rfl)
  have hav : a ∈ polygonVertices Γ τ₀ :=
    mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs hend
  have hfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine ((finite_polygonVertices hΓ hfree hε hgap hdense).image
      (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  rw [polygonVertexClassCount, Set.ncard_pos hfin]
  exact ⟨_, a, hav, rfl⟩

/-! ## Planar tier: circle directions, sine windows, and arc measures -/

/-- The imaginary part of a rotated unit direction over a nonzero complex number. -/
theorem exp_div_im (φ : ℝ) {u : ℂ} (_hu : u ≠ 0) :
    (Complex.exp ((φ : ℂ) * Complex.I) / u).im
      = ‖u‖⁻¹ * Real.sin (φ - Complex.arg u) := by
  have h1 : Complex.exp ((φ : ℂ) * Complex.I) / Complex.exp ((Complex.arg u : ℂ) * Complex.I)
      = Complex.exp (((φ - Complex.arg u : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  calc (Complex.exp ((φ : ℂ) * Complex.I) / u).im
      = (Complex.exp ((φ : ℂ) * Complex.I)
          / ((‖u‖ : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I))).im := by
        rw [Complex.norm_mul_exp_arg_mul_I u]
    _ = (Complex.exp (((φ - Complex.arg u : ℝ) : ℂ) * Complex.I) / ((‖u‖ : ℝ) : ℂ)).im := by
        rw [div_mul_eq_div_div_swap, h1]
    _ = ‖u‖⁻¹ * Real.sin (φ - Complex.arg u) := by
        rw [div_ofReal_im, Complex.exp_ofReal_mul_I_im]
        ring

/-- The sign data of a direction pair against a nonzero complex number. -/
theorem div_im_sign {x u : ℂ} (hu : u ≠ 0) (_hx : x ≠ 0) :
    (x / u).im = ‖x‖ * (‖u‖⁻¹ * Real.sin (Complex.arg x - Complex.arg u)) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_div_assoc, Complex.mul_im, exp_div_im _ hu, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The closed sine window on one period: the two sine sign conditions carve the arc from
`0` to `δ`. -/
theorem sin_window_weak {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ < Real.pi) :
    {ψ : ℝ | ψ ∈ Set.Ico 0 (2 * Real.pi) ∧ 0 ≤ Real.sin ψ ∧ Real.sin (ψ - δ) ≤ 0}
      = Set.Icc 0 δ := by
  have hπ := Real.pi_pos
  ext ψ
  simp only [Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, h2π⟩, hs1, hs2⟩
    refine ⟨h0, ?_⟩
    by_contra hcon
    have hcon' : δ < ψ := not_le.mp hcon
    rcases le_or_gt ψ Real.pi with hψπ | hψπ
    · have h1 : 0 < Real.sin (ψ - δ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      linarith
    · have h1 : 0 < Real.sin (ψ - Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h2 : Real.sin ψ = -Real.sin (ψ - Real.pi) := by
        conv_lhs => rw [show ψ = ψ - Real.pi + Real.pi by ring]
        rw [Real.sin_add_pi]
      linarith
  · rintro ⟨h0, hδ'⟩
    refine ⟨⟨h0, by linarith⟩, ?_, ?_⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    · have h1 : 0 ≤ Real.sin (δ - ψ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have h2 : Real.sin (ψ - δ) = -Real.sin (δ - ψ) := by
        rw [← Real.sin_neg, neg_sub]
      linarith [h2]

/-- The open sine window on one period. -/
theorem sin_window_strict {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ < Real.pi) :
    {ψ : ℝ | ψ ∈ Set.Ico 0 (2 * Real.pi) ∧ 0 < Real.sin ψ ∧ Real.sin (ψ - δ) < 0}
      = Set.Ioo 0 δ := by
  have hπ := Real.pi_pos
  ext ψ
  simp only [Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h0, h2π⟩, hs1, hs2⟩
    have hweak : ψ ∈ Set.Icc 0 δ := by
      rw [← sin_window_weak hδ0 hδπ]
      exact ⟨⟨h0, h2π⟩, hs1.le, hs2.le⟩
    obtain ⟨hl, hr⟩ := Set.mem_Icc.mp hweak
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hl with h1 | h1
      · rw [← h1, Real.sin_zero] at hs1
        exact absurd hs1 (lt_irrefl 0)
      · exact h1
    · rcases eq_or_lt_of_le hr with h1 | h1
      · rw [h1, sub_self, Real.sin_zero] at hs2
        exact absurd hs2 (lt_irrefl 0)
      · exact h1
  · rintro ⟨h0, hδ'⟩
    refine ⟨⟨h0.le, by linarith⟩, ?_, ?_⟩
    · exact Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
    · have h1 : 0 < Real.sin (δ - ψ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h2 : Real.sin (ψ - δ) = -Real.sin (δ - ψ) := by
        rw [← Real.sin_neg, neg_sub]
      linarith [h2]

/-- Sliding a length-`2π` window across a `2π`-periodic set preserves its trace measure. -/
theorem vol_window_shift {T : Set ℝ} (hT : MeasurableSet T)
    (hper : ∀ x, x ∈ T ↔ x + 2 * Real.pi ∈ T) {c t : ℝ} (ht0 : 0 ≤ t)
    (ht2 : t ≤ 2 * Real.pi) :
    volume (T ∩ Set.Ico (c + t) (c + t + 2 * Real.pi))
      = volume (T ∩ Set.Ico c (c + 2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have htrans : T ∩ Set.Ico (c + 2 * Real.pi) (c + t + 2 * Real.pi)
      = (fun x => x + -(2 * Real.pi)) ⁻¹' (T ∩ Set.Ico c (c + t)) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_preimage]
    constructor
    · rintro ⟨hyT, hy1, hy2⟩
      refine ⟨(hper (y + -(2 * Real.pi))).mpr (by simpa using hyT), by linarith, by linarith⟩
    · rintro ⟨hyT, hy1, hy2⟩
      have h2 := (hper (y + -(2 * Real.pi))).mp hyT
      refine ⟨by simpa using h2, by linarith, by linarith⟩
  have hsplit1 : T ∩ Set.Ico (c + t) (c + t + 2 * Real.pi)
      = (T ∩ Set.Ico (c + t) (c + 2 * Real.pi))
        ∪ (T ∩ Set.Ico (c + 2 * Real.pi) (c + t + 2 * Real.pi)) := by
    rw [← Set.inter_union_distrib_left, Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  have hsplit2 : T ∩ Set.Ico c (c + 2 * Real.pi)
      = (T ∩ Set.Ico c (c + t)) ∪ (T ∩ Set.Ico (c + t) (c + 2 * Real.pi)) := by
    rw [← Set.inter_union_distrib_left, Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  have hd1 : Disjoint (T ∩ Set.Ico (c + t) (c + 2 * Real.pi))
      (T ∩ Set.Ico (c + 2 * Real.pi) (c + t + 2 * Real.pi)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨-, -, hy2⟩ ⟨-, hy3, -⟩
    linarith
  have hd2 : Disjoint (T ∩ Set.Ico c (c + t)) (T ∩ Set.Ico (c + t) (c + 2 * Real.pi)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨-, -, hy2⟩ ⟨-, hy3, -⟩
    linarith
  rw [hsplit1, hsplit2, measure_union hd1 (hT.inter measurableSet_Ico),
    measure_union hd2 (hT.inter measurableSet_Ico), htrans]
  rw [show (fun x : ℝ => x + -(2 * Real.pi)) = (fun x : ℝ => -(2 * Real.pi) + x) by
    funext x; ring]
  rw [measure_preimage_add]
  ring

/-- The argument of a quotient lifts the argument difference modulo full turns. -/
theorem arg_div_add_int {u₁ u₂ : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    ∃ k : ℤ, Complex.arg u₂
      = Complex.arg (u₂ / u₁) + Complex.arg u₁ + 2 * Real.pi * k := by
  have hq : u₂ / u₁ ≠ 0 := div_ne_zero hu₂ hu₁
  have h1 : (((u₂ / u₁ * u₁).arg : ℝ) : Real.Angle)
      = (((u₂ / u₁).arg + u₁.arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact Complex.arg_mul_coe_angle hq hu₁
  rw [div_mul_cancel₀ u₂ hu₁] at h1
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h1
  exact ⟨k, by linarith [hk]⟩

/-- Sine sign against the direction of a nonzero complex number. -/
theorem sin_arg_div {u₁ u₂ : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    (u₂ / u₁).im = ‖u₂ / u₁‖ * Real.sin (Complex.arg (u₂ / u₁)) := by
  have hq : u₂ / u₁ ≠ 0 := div_ne_zero hu₂ hu₁
  rw [Complex.sin_arg, mul_div_cancel₀]
  exact norm_ne_zero_iff.mpr hq

/-- The two-half-plane direction window has measure the positive argument gap. -/
theorem vol_arc_pos {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    (hδpos : 0 < Complex.arg (u₂ / u₁)) :
    volume {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
      = ENNReal.ofReal |Complex.arg (u₂ / u₁)| := by
  have hπ := Real.pi_pos
  set δ : ℝ := Complex.arg (u₂ / u₁) with hδdef
  set a₁ : ℝ := Complex.arg u₁ with ha₁def
  set a₂ : ℝ := Complex.arg u₂ with ha₂def
  have hqnorm : 0 < ‖u₂ / u₁‖ :=
    norm_pos_iff.mpr (div_ne_zero hu₂ hu₁)
  have hqnorm' : 0 < ‖u₁ / u₂‖ :=
    norm_pos_iff.mpr (div_ne_zero hu₁ hu₂)
  have hsinδ : 0 < σ₁ * Real.sin δ := by
    have h1 := sin_arg_div hu₁ hu₂
    rw [h1] at h12
    nlinarith [h12, hqnorm]
  have hδπ : δ < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi (u₂ / u₁)) with h1 | h1
    · exact h1
    · exfalso
      rw [← hδdef] at h1
      rw [h1, Real.sin_pi, mul_zero] at hsinδ
      exact lt_irrefl 0 hsinδ
  have hσ₁1 : σ₁ = 1 := by
    rcases hσ₁ with h1 | h1
    · exact h1
    · exfalso
      have h2 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
      rw [h1] at hsinδ
      nlinarith
  have hsinδ' : 0 < Real.sin δ := by
    rw [hσ₁1, one_mul] at hsinδ
    exact hsinδ
  have harginv : Complex.arg (u₁ / u₂) = -δ := by
    rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, ← hδdef,
      if_neg (by intro h1; rw [h1] at hδπ; exact lt_irrefl _ hδπ)]
  have hσ₂1 : σ₂ = -1 := by
    have h1 := sin_arg_div hu₂ hu₁
    rw [h1, harginv, Real.sin_neg] at h21
    rcases hσ₂ with h2 | h2
    · exfalso
      rw [h2] at h21
      nlinarith
    · exact h2
  obtain ⟨k, hk⟩ := arg_div_add_int hu₁ hu₂
  have hsin₂ : ∀ φ : ℝ, Real.sin (φ - a₂) = Real.sin (φ - a₁ - δ) := by
    intro φ
    have h1 : φ - a₂ = φ - a₁ - δ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [ha₂def, hk]
      push_cast
      ring
    rw [h1, Real.sin_add_int_mul_two_pi]
  have hn₁ : (0 : ℝ) < ‖u₁‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₁)
  have hn₂ : (0 : ℝ) < ‖u₂‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₂)
  set T : Set ℝ := {ψ : ℝ | 0 ≤ Real.sin ψ ∧ Real.sin (ψ - δ) ≤ 0} with hTdef
  have hset : {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
      0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
      0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
      = (fun ψ => ψ + a₁) ''
          (T ∩ Set.Ico (-Real.pi - a₁) (Real.pi - a₁)) := by
    ext φ
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_Ico, hTdef]
    constructor
    · rintro ⟨⟨hφ1, hφ2⟩, hc1, hc2⟩
      rw [exp_div_im φ hu₁, hσ₁1, one_mul] at hc1
      rw [exp_div_im φ hu₂, hσ₂1] at hc2
      refine ⟨φ - a₁, ⟨⟨?_, ?_⟩, by linarith, by linarith⟩, by ring⟩
      · nlinarith [hc1, hn₁]
      · have h2 := hsin₂ φ
        have h3 : Real.sin (φ - a₂) ≤ 0 := by nlinarith [hc2, hn₂]
        rw [show φ - a₁ - δ = φ - a₁ - δ by ring, ← h2]
        exact h3
    · rintro ⟨ψ, ⟨⟨hs1, hs2⟩, hw1, hw2⟩, hφeq⟩
      subst hφeq
      refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
      · rw [exp_div_im _ hu₁, hσ₁1, one_mul, add_sub_cancel_right]
        positivity
      · rw [exp_div_im _ hu₂, hσ₂1]
        have h2 := hsin₂ (ψ + a₁)
        have h3 : ψ + a₁ - a₁ - δ = ψ - δ := by ring
        rw [h3] at h2
        rw [h2]
        nlinarith [hs2, hn₂]
  have hTmeas : MeasurableSet T := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le measurable_const Real.continuous_sin.measurable
    · exact measurableSet_le
        (Real.continuous_sin.comp (continuous_id.sub continuous_const)).measurable
        measurable_const
  have hTper : ∀ x, x ∈ T ↔ x + 2 * Real.pi ∈ T := by
    intro x
    simp only [hTdef, Set.mem_setOf_eq]
    rw [Real.sin_add_two_pi, show x + 2 * Real.pi - δ = x - δ + 2 * Real.pi by ring,
      Real.sin_add_two_pi]
  have ht0 : (0 : ℝ) ≤ Real.pi + a₁ := by
    have := Complex.neg_pi_lt_arg u₁
    rw [← ha₁def] at this
    linarith
  have ht2 : Real.pi + a₁ ≤ 2 * Real.pi := by
    have := Complex.arg_le_pi u₁
    rw [← ha₁def] at this
    linarith
  have hshift := vol_window_shift hTmeas hTper (c := -Real.pi - a₁) ht0 ht2
  rw [show -Real.pi - a₁ + (Real.pi + a₁) = 0 by ring,
    show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring,
    show -Real.pi - a₁ + 2 * Real.pi = Real.pi - a₁ by ring] at hshift
  have himg : ((fun ψ : ℝ => ψ + a₁) ''
      (T ∩ Set.Ico (-Real.pi - a₁) (Real.pi - a₁)))
      = (fun x : ℝ => -a₁ + x) ⁻¹' (T ∩ Set.Ico (-Real.pi - a₁) (Real.pi - a₁)) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      have h1 : -a₁ + (ψ + a₁) = ψ := by ring
      rw [h1]
      exact hψ
    · intro hy
      exact ⟨-a₁ + y, hy, by ring⟩
  have e3 : T ∩ Set.Ico 0 (2 * Real.pi) = Set.Icc 0 δ := by
    rw [← sin_window_weak hδpos hδπ]
    ext ψ
    simp only [hTdef, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [hset, himg, measure_preimage_add, ← hshift, e3, Real.volume_Icc, sub_zero,
    abs_of_pos hδpos]

/-- The sine of an angle against the second direction shifts by the quotient argument. -/
theorem sin_sub_arg {u₁ u₂ : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (φ : ℝ) :
    Real.sin (φ - Complex.arg u₂)
      = Real.sin (φ - Complex.arg u₁ - Complex.arg (u₂ / u₁)) := by
  obtain ⟨k, hk⟩ := arg_div_add_int hu₁ hu₂
  have h1 : φ - Complex.arg u₂
      = φ - Complex.arg u₁ - Complex.arg (u₂ / u₁) + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hk]
    push_cast
    ring
  rw [h1, Real.sin_add_int_mul_two_pi]

/-- The nonzero-argument-gap direction window has measure the absolute argument gap. -/
theorem vol_arc {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im) :
    volume {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
      = ENNReal.ofReal |Complex.arg (u₂ / u₁)| := by
  have hδne : Complex.arg (u₂ / u₁) ≠ 0 := by
    intro h0
    have h1 := sin_arg_div hu₁ hu₂
    rw [h0, Real.sin_zero, mul_zero] at h1
    rw [h1, mul_zero] at h12
    exact lt_irrefl 0 h12
  rcases lt_or_gt_of_ne hδne with hδneg | hδpos
  · have hπ' : Complex.arg (u₂ / u₁) ≠ Real.pi := by
      intro h0
      linarith [Real.pi_pos, hδneg, h0 ▸ hδneg]
    have harginv : Complex.arg (u₁ / u₂) = -Complex.arg (u₂ / u₁) := by
      rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, if_neg hπ']
    have hδpos' : 0 < Complex.arg (u₁ / u₂) := by
      rw [harginv]
      linarith
    have h1 := vol_arc_pos hσ₂ hσ₁ hu₂ hu₁ h21 h12 hδpos'
    have hsets : {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
        = {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im} := by
      ext φ
      simp only [Set.mem_setOf_eq]
      tauto
    rw [hsets, h1, harginv, abs_neg]
  · exact vol_arc_pos hσ₁ hσ₂ hu₁ hu₂ h12 h21 hδpos

/-- Away from the two boundary rays, a point of the punctured disc either satisfies both
strict sector conditions or violates one of them strictly. -/
theorem slit_trichotomy {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ}
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    {x : ℂ} (hx : x ≠ 0)
    (hr₁ : ¬ ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * u₁)
    (hr₂ : ¬ ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * u₂) :
    (0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im) ∨
      σ₁ * (x / u₁).im < 0 ∨ σ₂ * (x / u₂).im < 0 := by
  have hσ₁ne : σ₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h12
    exact lt_irrefl 0 h12
  have hσ₂ne : σ₂ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h21
    exact lt_irrefl 0 h21
  have hmul : ∀ u u' : ℂ, u ≠ 0 → u' ≠ 0 → (x / u).im = 0 →
      (¬ ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * u) →
      ∃ t : ℝ, t < 0 ∧ x = (t : ℂ) * u := by
    intro u u' hu hu' him hray
    have hre : x / u = (((x / u).re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    have hx1 : x = (((x / u).re : ℝ) : ℂ) * u := by
      rw [← hre, div_mul_cancel₀ x hu]
    have htne : (x / u).re ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, zero_mul] at hx1
      exact hx hx1
    rcases lt_or_gt_of_ne htne with h1 | h1
    · exact ⟨(x / u).re, h1, hx1⟩
    · exact absurd ⟨(x / u).re, h1, hx1⟩ hray
  rcases lt_trichotomy (σ₁ * (x / u₁).im) 0 with h1 | h1 | h1
  · exact Or.inr (Or.inl h1)
  · have him : (x / u₁).im = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hσ₁ne
      · exact h2
    obtain ⟨t, ht, hx1⟩ := hmul u₁ u₂ hu₁ hu₂ him hr₁
    refine Or.inr (Or.inr ?_)
    have h2 : x / u₂ = (t : ℂ) * (u₁ / u₂) := by
      rw [hx1, mul_div_assoc]
    rw [h2, Complex.im_ofReal_mul]
    nlinarith [h21, ht]
  · rcases lt_trichotomy (σ₂ * (x / u₂).im) 0 with h2 | h2 | h2
    · exact Or.inr (Or.inr h2)
    · have him : (x / u₂).im = 0 := by
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 hσ₂ne
        · exact h3
      obtain ⟨t, ht, hx1⟩ := hmul u₂ u₁ hu₂ hu₁ him hr₂
      refine Or.inr (Or.inl ?_)
      have h3 : x / u₁ = (t : ℂ) * (u₂ / u₁) := by
        rw [hx1, mul_div_assoc]
      rw [h3, Complex.im_ofReal_mul]
      nlinarith [h12, ht]
    · exact Or.inl ⟨h1, h2⟩

/-- The strict two-half-plane sector inside a disc is a polar rectangle over the positive
argument gap. -/
theorem sector_eq_polar {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    (hδpos : 0 < Complex.arg (u₂ / u₁)) :
    {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im}
      = (fun p : ℝ × ℝ =>
          (p.1 : ℂ) * Complex.exp (((p.2 + Complex.arg u₁ : ℝ) : ℂ) * Complex.I))
        '' (Set.Ioo 0 s ×ˢ Set.Ioo 0 (Complex.arg (u₂ / u₁))) := by
  have hπ := Real.pi_pos
  set δ : ℝ := Complex.arg (u₂ / u₁) with hδdef
  set a₁ : ℝ := Complex.arg u₁ with ha₁def
  set a₂ : ℝ := Complex.arg u₂ with ha₂def
  have hqnorm : 0 < ‖u₂ / u₁‖ := norm_pos_iff.mpr (div_ne_zero hu₂ hu₁)
  have hn₁ : (0 : ℝ) < ‖u₁‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₁)
  have hn₂ : (0 : ℝ) < ‖u₂‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₂)
  have hsinδ : 0 < σ₁ * Real.sin δ := by
    have h1 := sin_arg_div hu₁ hu₂
    rw [h1] at h12
    nlinarith [h12, hqnorm]
  have hδπ : δ < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi (u₂ / u₁)) with h1 | h1
    · exact h1
    · exfalso
      rw [← hδdef] at h1
      rw [h1, Real.sin_pi, mul_zero] at hsinδ
      exact lt_irrefl 0 hsinδ
  have hσ₁1 : σ₁ = 1 := by
    rcases hσ₁ with h1 | h1
    · exact h1
    · exfalso
      have h2 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
      rw [h1] at hsinδ
      nlinarith
  have harginv : Complex.arg (u₁ / u₂) = -δ := by
    rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, ← hδdef,
      if_neg (by intro h1; rw [h1] at hδπ; exact lt_irrefl _ hδπ)]
  have hσ₂1 : σ₂ = -1 := by
    have h1 := sin_arg_div hu₂ hu₁
    rw [h1, harginv, Real.sin_neg] at h21
    rcases hσ₂ with h2 | h2
    · exfalso
      rw [h2] at h21
      have h3 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
      nlinarith [norm_pos_iff.mpr (div_ne_zero hu₁ hu₂)]
    · exact h2
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨hxs, hc1, hc2⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hc1
      simp at hc1
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    rw [div_im_sign hu₁ hx0, hσ₁1, one_mul, ← ha₁def] at hc1
    rw [div_im_sign hu₂ hx0, hσ₂1, ← ha₂def] at hc2
    have hs1 : 0 < Real.sin (Complex.arg x - a₁) := by nlinarith [hc1, mul_pos hnx hn₁]
    have hs2 : Real.sin (Complex.arg x - a₂) < 0 := by nlinarith [hc2, mul_pos hnx hn₂]
    have hs2' : Real.sin (Complex.arg x - a₁ - δ) < 0 := by
      rw [← sin_sub_arg hu₁ hu₂]
      exact hs2
    set ψ₀ : ℝ := Complex.arg x - a₁ with hψ₀def
    have hψ₀lb : -(2 * Real.pi) < ψ₀ := by
      have b1 := Complex.neg_pi_lt_arg x
      have b2 := Complex.arg_le_pi u₁
      rw [← ha₁def] at b2
      simp only [hψ₀def]
      linarith
    have hψ₀ub : ψ₀ < 2 * Real.pi := by
      have b1 := Complex.arg_le_pi x
      have b2 := Complex.neg_pi_lt_arg u₁
      rw [← ha₁def] at b2
      simp only [hψ₀def]
      linarith
    by_cases hcase : 0 ≤ ψ₀
    · have hmem : ψ₀ ∈ Set.Ioo 0 δ := by
        have h1 := (Set.ext_iff.mp (sin_window_strict hδpos hδπ) ψ₀).mp
          ⟨⟨hcase, hψ₀ub⟩, hs1, hs2'⟩
        exact h1
      refine ⟨(‖x‖, ψ₀), ⟨⟨hnx, hxs⟩, hmem⟩, ?_⟩
      have h2 : ψ₀ + a₁ = Complex.arg x := by
        simp only [hψ₀def]
        ring
      rw [h2]
      exact Complex.norm_mul_exp_arg_mul_I x
    · have hψ' : ψ₀ + 2 * Real.pi ∈ Set.Ico 0 (2 * Real.pi) :=
        ⟨by linarith, by linarith [not_le.mp hcase]⟩
      have hsin1 : 0 < Real.sin (ψ₀ + 2 * Real.pi) := by
        rw [Real.sin_add_two_pi]
        exact hs1
      have hsin2 : Real.sin (ψ₀ + 2 * Real.pi - δ) < 0 := by
        rw [show ψ₀ + 2 * Real.pi - δ = ψ₀ - δ + 2 * Real.pi by ring,
          Real.sin_add_two_pi]
        exact hs2'
      have hmem : ψ₀ + 2 * Real.pi ∈ Set.Ioo 0 δ :=
        (Set.ext_iff.mp (sin_window_strict hδpos hδπ) _).mp ⟨hψ', hsin1, hsin2⟩
      refine ⟨(‖x‖, ψ₀ + 2 * Real.pi), ⟨⟨hnx, hxs⟩, hmem⟩, ?_⟩
      have h2 : ((ψ₀ + 2 * Real.pi + a₁ : ℝ) : ℂ) * Complex.I
          = ((Complex.arg x : ℝ) : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
        simp only [hψ₀def]
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      exact Complex.norm_mul_exp_arg_mul_I x
  · rintro ⟨⟨r, ψ⟩, ⟨⟨hr0, hrs⟩, hψ0, hψδ⟩, rfl⟩
    dsimp only at hr0 hrs hψ0 hψδ ⊢
    have hsinψ : 0 < Real.sin ψ :=
      Real.sin_pos_of_pos_of_lt_pi hψ0 (by linarith)
    have hsinψδ : Real.sin (ψ - δ) < 0 := by
      have h1 : 0 < Real.sin (δ - ψ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h2 : Real.sin (ψ - δ) = -Real.sin (δ - ψ) := by
        rw [← Real.sin_neg, neg_sub]
      linarith
    have hnorm : ‖(r : ℂ) * Complex.exp (((ψ + a₁ : ℝ) : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0]
    refine ⟨by rw [hnorm]; exact hrs, ?_, ?_⟩
    · rw [mul_div_assoc, Complex.im_ofReal_mul, exp_div_im _ hu₁, ← ha₁def,
        add_sub_cancel_right, hσ₁1]
      nlinarith [mul_pos (mul_pos hr0 hn₁) hsinψ]
    · rw [mul_div_assoc, Complex.im_ofReal_mul, exp_div_im _ hu₂, ← ha₂def, hσ₂1]
      have h2 : Real.sin (ψ + a₁ - a₂) = Real.sin (ψ - δ) := by
        rw [sin_sub_arg hu₁ hu₂, ← ha₁def, ← hδdef,
          show ψ + a₁ - a₁ - δ = ψ - δ by ring]
      rw [h2]
      nlinarith [mul_pos (mul_pos hr0 hn₂) (neg_pos.mpr hsinψδ)]

/-- The strict two-half-plane sector inside a disc is preconnected. -/
theorem sector_preconnected {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    (hδpos : 0 < Complex.arg (u₂ / u₁)) :
    IsPreconnected {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im} := by
  rw [sector_eq_polar hσ₁ hσ₂ hu₁ hu₂ h12 h21 hδpos]
  refine IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_Ioo) _ ?_
  refine Continuous.continuousOn ?_
  refine Continuous.mul (Complex.continuous_ofReal.comp continuous_fst) ?_
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  exact Complex.continuous_ofReal.comp (continuous_snd.add continuous_const)

/-- The strict sector over the reversed direction pair is the same set. -/
theorem sector_comm {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ} :
    {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im}
      = {x : ℂ | ‖x‖ < s ∧ 0 < σ₂ * (x / u₂).im ∧ 0 < σ₁ * (x / u₁).im} := by
  ext x
  simp only [Set.mem_setOf_eq]
  tauto

/-- The zero set of a sine shifted by a principal argument on the principal window is
finite. -/
theorem finite_sin_zero {a : ℝ} (ha : -Real.pi < a) (ha' : a ≤ Real.pi) :
    {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧ Real.sin (φ - a) = 0}.Finite := by
  have hπ := Real.pi_pos
  refine ((((Set.finite_singleton (a + Real.pi)).insert a).insert
    (a - Real.pi)).insert (a - 2 * Real.pi)).subset ?_
  rintro φ ⟨⟨h1, h2⟩, hz⟩
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
  have hn2 : (-2 : ℝ) ≤ (n : ℝ) := by nlinarith [hn, hπ, h1, h2, ha, ha']
  have hn2' : (n : ℝ) < 2 := by nlinarith [hn, hπ, h1, h2, ha, ha']
  have hn3 : n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 := by
    have hlt : n < 2 := by exact_mod_cast hn2'
    have hgt : (-2 : ℤ) ≤ n := by exact_mod_cast hn2
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hn3 with h3 | h3 | h3 | h3 <;> rw [h3] at hn <;> push_cast at hn
  · left; linarith
  · right; left; linarith
  · right; right; left; linarith
  · right; right; right; linarith

/-! ## Dictionary tier: the disc frame as a homeomorphic chart with a `tanh` radius law -/

/-- The frame at a base point is continuous. -/
theorem continuous_discChart (v : UpperHalfPlane) :
    Continuous fun w : UpperHalfPlane => discChart v w := by
  have h1 : (fun w : UpperHalfPlane => discChart v w)
      = fun w : UpperHalfPlane =>
        ((w : ℂ) - (v : ℂ)) / ((w : ℂ) - (starRingEnd ℂ) (v : ℂ)) := by
    funext w
    exact discChart_eq v w
  rw [h1]
  refine Continuous.div ?_ ?_ ?_
  · exact (UpperHalfPlane.continuous_coe.sub continuous_const)
  · exact (UpperHalfPlane.continuous_coe.sub continuous_const)
  · intro w
    exact sub_conj_ne_zero v w

/-- The `tanh` radius law of the frame: hyperbolic balls become Euclidean discs. -/
theorem dist_lt_iff_norm_chart {v w : UpperHalfPlane} {r : ℝ} (hr : 0 < r) :
    dist v w < r ↔ ‖discChart v w‖ < Real.tanh (r / 2) := by
  have hd : dist v w = 2 * Real.arsinh (‖discChart v w‖
      / Real.sqrt (1 - ‖discChart v w‖ ^ 2)) := by
    have h1 := dist_eq_hDD v v w
    rw [discChart_self] at h1
    rw [h1, hyperbolicDistDisk, norm_sub_rev, sub_zero, norm_zero]
    norm_num
  set t : ℝ := ‖discChart v w‖ with htdef
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t < 1 := norm_discChart_lt_one v w
  have htsq : 0 < 1 - t ^ 2 := by nlinarith
  have hsq : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr htsq
  set S : ℝ := Real.sinh (r / 2) with hSdef
  have hS0 : 0 < S := by
    rw [hSdef]
    exact Real.sinh_pos_iff.mpr (by linarith)
  have hcosh : 0 < Real.cosh (r / 2) := Real.cosh_pos _
  have hchain1 : dist v w < r ↔ t / Real.sqrt (1 - t ^ 2) < S := by
    rw [hd]
    constructor
    · intro h1
      have h2 : Real.arsinh (t / Real.sqrt (1 - t ^ 2)) < r / 2 := by linarith
      have h3 := Real.arsinh_lt_arsinh.mp (by rwa [Real.arsinh_sinh] : Real.arsinh
        (t / Real.sqrt (1 - t ^ 2)) < Real.arsinh S)
      exact h3
    · intro h1
      have h2 : Real.arsinh (t / Real.sqrt (1 - t ^ 2)) < Real.arsinh S :=
        Real.arsinh_lt_arsinh.mpr h1
      rw [hSdef, Real.arsinh_sinh] at h2
      linarith
  have hchain2 : t / Real.sqrt (1 - t ^ 2) < S ↔ t ^ 2 < S ^ 2 * (1 - t ^ 2) := by
    rw [div_lt_iff₀ hsq]
    constructor
    · intro h1
      have h2 : t * t < (S * Real.sqrt (1 - t ^ 2)) * (S * Real.sqrt (1 - t ^ 2)) :=
        mul_self_lt_mul_self ht0 h1
      have h3 : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
        Real.mul_self_sqrt htsq.le
      nlinarith
    · intro h1
      have h2 : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
        Real.mul_self_sqrt htsq.le
      nlinarith [mul_pos hS0 hsq, sq_nonneg (t - S * Real.sqrt (1 - t ^ 2)),
        sq_nonneg (t + S * Real.sqrt (1 - t ^ 2))]
  have hchain3 : t ^ 2 < S ^ 2 * (1 - t ^ 2) ↔ t * Real.cosh (r / 2) < S := by
    have hc2 : Real.cosh (r / 2) ^ 2 = S ^ 2 + 1 := by
      rw [hSdef, Real.cosh_sq]
    constructor
    · intro h1
      have h2 : (t * Real.cosh (r / 2)) ^ 2 < S ^ 2 := by
        rw [mul_pow, hc2]
        nlinarith
      have h3 : t * Real.cosh (r / 2) < S := by
        nlinarith [mul_nonneg ht0 hcosh.le, hS0]
      exact h3
    · intro h1
      have h3 : 0 ≤ t * Real.cosh (r / 2) := by positivity
      have h2 : (t * Real.cosh (r / 2)) ^ 2 < S ^ 2 := by nlinarith
      rw [mul_pow, hc2] at h2
      nlinarith
  have hchain4 : t * Real.cosh (r / 2) < S ↔ t < Real.tanh (r / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh, ← hSdef, lt_div_iff₀ hcosh]
  rw [hchain1, hchain2, hchain3, hchain4]

/-- The inverse Cayley formula has positive imaginary part on the open unit disc. -/
theorem invChart_im (v : UpperHalfPlane) {u : ℂ} (hu : ‖u‖ < 1) :
    0 < ((v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u))).im := by
  have hden : (1 : ℂ) - u ≠ 0 := by
    intro h0
    have h1 : u = 1 := by linear_combination -h0
    rw [h1] at hu
    simp at hu
  have hre : ((1 + u) / (1 - u)).re = (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
    rw [Complex.div_re, ← add_div]
    congr 1
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply]
    ring
  have him : ((v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u))).im
      = v.im * ((1 + u) / (1 - u)).re := by
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [him, hre]
  have h2 : Complex.normSq u < 1 := by
    have h3 : Complex.normSq u = ‖u‖ ^ 2 := (Complex.sq_norm u).symm
    nlinarith [norm_nonneg u]
  have h4 : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hden
  have h5 : 0 < v.im := v.im_pos
  exact mul_pos h5 (div_pos (by linarith) h4)

/-- The frame at a base point surjects onto the open unit disc, with an explicit inverse. -/
theorem chart_surj (v : UpperHalfPlane) {u : ℂ} (hu : ‖u‖ < 1) :
    ∃ w : UpperHalfPlane, discChart v w = u ∧
      (w : ℂ) = (v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u)) := by
  have hden : (1 : ℂ) - u ≠ 0 := by
    intro h0
    have h1 : u = 1 := by linear_combination -h0
    rw [h1] at hu
    simp at hu
  set w : UpperHalfPlane := UpperHalfPlane.mk
    ((v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u))) (invChart_im v hu)
    with hwdef
  have hcoe : (w : ℂ) = (v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u)) := rfl
  refine ⟨w, ?_, hcoe⟩
  rw [discChart_eq]
  have hne2 : (w : ℂ) - (starRingEnd ℂ) (v : ℂ) ≠ 0 := sub_conj_ne_zero v w
  rw [div_eq_iff hne2, hcoe, conj_coe, coe_eq_re_add_im v]
  have hW : (1 + u) / (1 - u) * (1 - u) = 1 + u := div_mul_cancel₀ _ hden
  linear_combination ((v.im : ℂ) * Complex.I) * hW

/-- The frame at a base point is injective. -/
theorem discChart_injective (v : UpperHalfPlane) {w w' : UpperHalfPlane}
    (h : discChart v w = discChart v w') : w = w' := by
  have h1 := dist_eq_hDD v w w'
  rw [h, hyperbolicDistDisk_self] at h1
  exact dist_eq_zero.mp h1

/-- Every short direction multiple of a far ray point is realized on the radial segment. -/
theorem slit_full {v y : UpperHalfPlane} (hy : y ≠ v) {r' : ℝ} (hr' : 0 < r')
    (hyfar : r' ≤ dist v y) {x : ℂ} (hx : ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * discChart v y)
    (hxs : ‖x‖ < Real.tanh (r' / 2)) :
    ∃ w : UpperHalfPlane, w ∈ geodSeg v y ∧ w ≠ v ∧ discChart v w = x := by
  obtain ⟨t, ht, hxdef⟩ := hx
  have hyc : discChart v y ≠ 0 := discChart_ne_zero hy
  have hx0 : x ≠ 0 := by
    rw [hxdef]
    exact mul_ne_zero (by exact_mod_cast ht.ne') hyc
  have hg : Continuous fun τ : ℝ => ‖discChart v (geodInterp v y τ)‖ := by
    refine Continuous.norm ?_
    refine (continuous_discChart v).comp ?_
    exact continuous_geodInterp.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hg0 : ‖discChart v (geodInterp v y 0)‖ = 0 := by
    rw [geodInterp_zero, discChart_self, norm_zero]
  have hg1 : Real.tanh (r' / 2) ≤ ‖discChart v (geodInterp v y 1)‖ := by
    rw [geodInterp_one]
    by_contra hcon
    have h2 : dist v y < r' := (dist_lt_iff_norm_chart hr').mpr (not_le.mp hcon)
    linarith
  have hmem : ‖x‖ ∈ Set.Icc (‖discChart v (geodInterp v y 0)‖)
      (‖discChart v (geodInterp v y 1)‖) := by
    rw [hg0]
    exact ⟨norm_nonneg x, le_trans hxs.le hg1⟩
  obtain ⟨τ, hτmem, hτeq⟩ := intermediate_value_Icc (by norm_num) hg.continuousOn hmem
  have hτeq' : ‖discChart v (geodInterp v y τ)‖ = ‖x‖ := hτeq
  set w : UpperHalfPlane := geodInterp v y τ with hwdef
  have hwseg : w ∈ geodSeg v y := geodInterp_mem_geodSeg v y hτmem
  have hwv : w ≠ v := by
    intro h0
    rw [h0, discChart_self, norm_zero] at hτeq'
    exact norm_ne_zero_iff.mpr hx0 hτeq'.symm
  obtain ⟨t', ht', hchart⟩ := discChart_smul_of_mem_geodSeg hwseg hwv
  refine ⟨w, hwseg, hwv, ?_⟩
  have hnorm : t' * ‖discChart v y‖ = t * ‖discChart v y‖ := by
    have h2 : ‖discChart v w‖ = ‖x‖ := hτeq'
    rw [hchart, hxdef] at h2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht', abs_of_pos ht] at h2
    exact h2
  have htt : t' = t :=
    mul_right_cancel₀ (norm_ne_zero_iff.mpr hyc) hnorm
  rw [hchart, htt, hxdef]

/-! ## Assembly helpers: ray order, ray-independence of angles, side transport -/

/-- Of two points of a radial segment, the nearer lies on the segment to the farther. -/
theorem ray_order {g y p q : UpperHalfPlane} (hp : p ∈ geodSeg g y)
    (hq : q ∈ geodSeg g y) (hle : dist g p ≤ dist g q) : p ∈ geodSeg g q := by
  rw [geodSeg_eq_image_geodInterp] at hp hq
  obtain ⟨sp, hsp, hpe⟩ := hp
  obtain ⟨sq, hsq, hqe⟩ := hq
  have hdp : dist g p = sp * dist g y := by rw [← hpe, dist_geodInterp_left g y hsp]
  have hdq : dist g q = sq * dist g y := by rw [← hqe, dist_geodInterp_left g y hsq]
  rcases eq_or_ne (dist g y) 0 with hd0 | hd0
  · have h1 : g = y := dist_eq_zero.mp hd0
    rw [← hpe, ← hqe, h1, geodInterp_self, geodInterp_self]
    exact left_mem_geodSeg _ _
  · have hd0' : 0 < dist g y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    have hsple : sp ≤ sq := by
      by_contra hcon
      have h1 : sq * dist g y < sp * dist g y :=
        mul_lt_mul_of_pos_right (not_le.mp hcon) hd0'
      rw [← hdp, ← hdq] at h1
      linarith
    rw [mem_geodSeg, ← hpe, ← hqe, dist_geodInterp_pair,
      abs_of_nonpos (by linarith), dist_geodInterp_left g y hsp,
      dist_geodInterp_left g y hsq]
    ring

/-- The sector angle does not depend on the chosen non-apex point of a radial segment. -/
theorem sectorAngle_ray_congr {g y p q : UpperHalfPlane} (hp : p ∈ geodSeg g y)
    (hq : q ∈ geodSeg g y) (hpg : p ≠ g) (hqg : q ≠ g) (w₂ : UpperHalfPlane) :
    sectorAngle g p w₂ = sectorAngle g q w₂ := by
  rcases le_total (dist g p) (dist g q) with h1 | h1
  · exact sectorAngle_congr_of_mem_geodSeg (ray_order hp hq h1) hpg w₂
  · exact (sectorAngle_congr_of_mem_geodSeg (ray_order hq hp h1) hqg w₂).symm

/-- The inverse translate of a side set is the side set of the inverse. -/
theorem smul_sideSet_inv (γ : ↥Γ) :
    (γ⁻¹ • ·) '' dirichletSideSet Γ τ₀ γ = dirichletSideSet Γ τ₀ γ⁻¹ := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact smul_mem_dirichletSideSet_inv hy
  · intro x hx
    have h1 := smul_mem_dirichletSideSet_inv (γ := γ⁻¹) hx
    rw [inv_inv] at h1
    exact ⟨γ • x, h1, by change γ⁻¹ • γ • x = x; rw [inv_smul_smul]⟩

/-- The half-plane functional of one side of a tile in the frame at a vertex: sign data
with the tile on the closed side, the tile interior on the open side, and a transverse
reference segment strictly inside. -/
theorem side_functional (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {b c : ↥Γ} (hmove : b • τ₀ ≠ c • τ₀)
    {v : UpperHalfPlane} (hveq : dist v (b • τ₀) = dist v (c • τ₀))
    {Wn : UpperHalfPlane} (hWnbis : dist Wn (b • τ₀) = dist Wn (c • τ₀)) (hWnv : Wn ≠ v)
    {q : UpperHalfPlane} (hqc : q ≠ c • τ₀) (hqb : q ≠ b • τ₀)
    {P : UpperHalfPlane} (hPv : P ≠ v)
    (hPbis : ∀ w ∈ geodSeg v P, dist w (b • τ₀) = dist w q)
    (hPT : geodSeg v P ⊆ (b • ·) '' dirichletDomain Γ τ₀) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart v P / discChart v Wn).im ∧
      (∀ w ∈ (b • ·) '' dirichletDomain Γ τ₀,
        0 ≤ σ * (discChart v w / discChart v Wn).im) ∧
      (∀ w ∈ (b • ·) '' interior (dirichletDomain Γ τ₀),
        0 < σ * (discChart v w / discChart v Wn).im) := by
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hmove
  obtain ⟨m, hm, hfeq, hflt⟩ := functional_sign hε' hle hge hveq
  have hWn0 : discChart v Wn ≠ 0 := discChart_ne_zero hWnv
  have hzero : ε' * (m * discChart v Wn).im = 0 := hfeq Wn hWnbis
  have hratio := functional_ratio hε' hWn0 hzero
  set C : ℝ := ε' * (m * discChart v Wn).re with hCdef
  have hweak : ∀ w ∈ (b • ·) '' dirichletDomain Γ τ₀,
      0 ≤ C * (discChart v w / discChart v Wn).im := by
    intro w hw
    have h1 : dist w (b • τ₀) ≤ dist w (c • τ₀) := smul_dirichletDomain_subset b c hw
    rw [← hratio (discChart v w)]
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact (hflt w h2).le
    · exact (hfeq w h2).ge
  have hCne : C ≠ 0 := by
    intro hC0
    have h2 : dist (b • τ₀) (b • τ₀) < dist (b • τ₀) (c • τ₀) := by
      rw [dist_self]
      exact dist_pos.mpr hmove
    have h3 := hflt (b • τ₀) h2
    rw [hratio (discChart v (b • τ₀)), hC0, zero_mul] at h3
    exact lt_irrefl 0 h3
  have hint : ∀ w ∈ (b • ·) '' interior (dirichletDomain Γ τ₀),
      0 < C * (discChart v w / discChart v Wn).im := by
    rintro w ⟨y, hy, rfl⟩
    haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
      ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
    have hbc' : (b⁻¹ * c) • τ₀ ≠ τ₀ := by
      intro h0
      have h1 : b • (b⁻¹ * c) • τ₀ = b • τ₀ := congrArg (b • ·) h0
      rw [← mul_smul, mul_inv_cancel_left] at h1
      exact hmove h1.symm
    have hylt : dist y τ₀ < dist y ((b⁻¹ * c) • τ₀) := by
      rw [interior_dirichletDomain_eq hΓ hdense] at hy
      exact hy (b⁻¹ * c) hbc'
    have e1 : dist (b • y) (b • τ₀) = dist y τ₀ := dist_smul b y τ₀
    have e2 : dist (b • y) (c • τ₀) = dist y ((b⁻¹ * c) • τ₀) := by
      calc dist (b • y) (c • τ₀) = dist (b⁻¹ • b • y) (b⁻¹ • c • τ₀) :=
          (dist_smul b⁻¹ _ _).symm
        _ = dist y ((b⁻¹ * c) • τ₀) := by rw [inv_smul_smul, mul_smul]
    have h2 : dist (b • y) (b • τ₀) < dist (b • y) (c • τ₀) := by
      rw [e1, e2]
      exact hylt
    have h3 := hflt (b • y) h2
    rw [hratio (discChart v (b • y))] at h3
    exact h3
  have hstrictP : 0 < C * (discChart v P / discChart v Wn).im := by
    have hP1 : P ∈ geodSeg v P := right_mem_geodSeg v P
    have hd : 0 < dist v P := dist_pos.mpr (Ne.symm hPv)
    rcases lt_or_eq_of_le (hweak P (hPT hP1)) with h1 | h1
    · exact h1
    exfalso
    have hratioP0 : (discChart v P / discChart v Wn).im = 0 := by
      rcases mul_eq_zero.mp h1.symm with h5 | h5
      · exact absurd h5 hCne
      · exact h5
    set P2 : UpperHalfPlane := geodInterp v P (1 / 2) with hP2def
    have hP2seg : P2 ∈ geodSeg v P := geodInterp_mem_geodSeg v P (by norm_num)
    have hdP2 : dist v P2 = 1 / 2 * dist v P :=
      dist_geodInterp_left v P (by norm_num)
    have hP2v : P2 ≠ v := by
      intro h0
      rw [h0, dist_self] at hdP2
      linarith
    have hPP2 : P ≠ P2 := by
      intro h0
      rw [← h0] at hdP2
      linarith
    obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hP2seg hP2v
    have hzP : ε' * (m * discChart v P).im = 0 := by
      rw [hratio (discChart v P), hratioP0, mul_zero]
    have hzP2 : ε' * (m * discChart v P2).im = 0 := by
      rw [hratio (discChart v P2), hchart]
      have h3 : ((t : ℝ) : ℂ) * discChart v P / discChart v Wn
          = (t : ℂ) * (discChart v P / discChart v Wn) := by ring
      rw [h3, Complex.im_ofReal_mul, hratioP0, mul_zero, mul_zero]
    have hbisP : dist P (b • τ₀) = dist P (c • τ₀) := by
      by_contra hne
      have hle' : dist P (b • τ₀) ≤ dist P (c • τ₀) :=
        smul_dirichletDomain_subset b c (hPT hP1)
      rcases lt_or_eq_of_le hle' with h3 | h3
      · exact absurd (hflt P h3) (by rw [hzP]; exact lt_irrefl 0)
      · exact hne h3
    have hbisP2 : dist P2 (b • τ₀) = dist P2 (c • τ₀) := by
      by_contra hne
      have hle' : dist P2 (b • τ₀) ≤ dist P2 (c • τ₀) :=
        smul_dirichletDomain_subset b c (hPT hP2seg)
      rcases lt_or_eq_of_le hle' with h3 | h3
      · exact absurd (hflt P2 h3) (by rw [hzP2]; exact lt_irrefl 0)
      · exact hne h3
    exact hqc (bisector_pair_unique hPP2 hbisP hbisP2 (hPbis P hP1)
      (hPbis P2 hP2seg) (Ne.symm hmove) hqb).symm
  rcases lt_or_gt_of_ne hCne with hCneg | hCpos
  · refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩
    · nlinarith [hstrictP]
    · intro w hw
      nlinarith [hweak w hw]
    · intro w hw
      nlinarith [hint w hw]
  · refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
    · nlinarith [hstrictP]
    · intro w hw
      nlinarith [hweak w hw]
    · intro w hw
      nlinarith [hint w hw]

/-- The strict two-half-plane sector is preconnected, either orientation. -/
theorem sector_preconnected' {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im) :
    IsPreconnected {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im} := by
  have hδne : Complex.arg (u₂ / u₁) ≠ 0 := by
    intro h0
    have h1 := sin_arg_div hu₁ hu₂
    rw [h0, Real.sin_zero, mul_zero] at h1
    rw [h1, mul_zero] at h12
    exact lt_irrefl 0 h12
  rcases lt_or_gt_of_ne hδne with hδneg | hδpos
  · have hπ' : Complex.arg (u₂ / u₁) ≠ Real.pi := by
      intro h0
      linarith [Real.pi_pos, h0 ▸ hδneg]
    have harginv : Complex.arg (u₁ / u₂) = -Complex.arg (u₂ / u₁) := by
      rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, if_neg hπ']
    have hδpos' : 0 < Complex.arg (u₁ / u₂) := by
      rw [harginv]
      linarith
    rw [sector_comm]
    exact sector_preconnected hσ₂ hσ₁ hu₂ hu₁ h21 h12 hδpos'
  · exact sector_preconnected hσ₁ hσ₂ hu₁ hu₂ h12 h21 hδpos

/-- Composition of set translates along the subgroup action. -/
theorem smul_smul_image (a b : ↥Γ) (S : Set UpperHalfPlane) :
    (a • ·) '' ((b • ·) '' S) = ((a * b) • ·) '' S := by
  rw [← Set.image_comp]
  congr 1
  funext x
  change a • b • x = (a * b) • x
  rw [mul_smul]

/-- A point of a radial slit from the frame base has a purely real frame ratio. -/
theorem ray_kill {v y w : UpperHalfPlane} (hyv : y ≠ v)
    (hw : w ∈ geodSeg v y) (hwv : w ≠ v) :
    (discChart v w / discChart v y).im = 0 := by
  obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hw hwv
  rw [hchart, mul_div_assoc, div_self (discChart_ne_zero hyv), mul_one,
    Complex.ofReal_im]

/-! ## Angle sums -/

set_option maxHeartbeats 400000 in
-- The vertex-star assembly elaborates the full cycle, functional, and measure bookkeeping
-- in one declaration; the default heartbeat budget does not cover it.
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
  classical
  obtain ⟨n, e, hn3, hper, hecon, huniq, hadj⟩ :=
    exists_vertex_cycle hΓ hfree hε hgap hdense hv
  have hn0 : 0 < n := by omega
  -- distances from the vertex to the tile centers all realize the contact distance
  have hvd : ∀ k : ℕ, dist v (e k • τ₀) = Metric.infDist v (MulAction.orbit Γ τ₀) := by
    intro k
    have h1 := hecon k
    simp only [contactSet, Set.mem_setOf_eq] at h1
    exact h1
  have hveq : ∀ k j : ℕ, dist v (e k • τ₀) = dist v (e j • τ₀) := by
    intro k j
    rw [hvd k, hvd j]
  -- periodic reduction of the enumeration
  have hemod : ∀ k : ℕ, e k = e (k % n) := by
    intro k
    conv_lhs => rw [show k = k % n + n * (k / n) from (Nat.mod_add_div k n).symm]
    generalize k / n = q
    induction q with
    | zero => rw [Nat.mul_zero, Nat.add_zero]
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  -- distinct centers detect distinct residues
  have hcent : ∀ a b : ℕ, e a • τ₀ = e b • τ₀ → a % n = b % n := by
    intro a b hab
    obtain ⟨k, -, hk⟩ := huniq (e a) (hecon a)
    have h1 := hk (a % n) ⟨Nat.mod_lt a hn0, by rw [← hemod a]⟩
    have h2 := hk (b % n) ⟨Nat.mod_lt b hn0, by rw [← hemod b, ← hab]⟩
    rw [h1, h2]
  have hcne : ∀ a b : ℕ, ¬ a ≡ b [MOD n] → e a • τ₀ ≠ e b • τ₀ := by
    intro a b hmod hab
    exact hmod (hcent a b hab)
  -- index bookkeeping for the previous side
  set p : ℕ → ℕ := fun k => k + (n - 1) with hpdef
  have hp1 : ∀ k, p k + 1 = k + n := by
    intro k
    simp only [hpdef]
    omega
  have hep1 : ∀ k, e (p k + 1) = e k := by
    intro k
    rw [hp1 k, hper]
  have hmod_k_k1 : ∀ k : ℕ, ¬ k ≡ k + 1 [MOD n] := by
    intro k h1
    have h2 := (Nat.modEq_iff_dvd' (by omega)).mp h1
    have h3 : n ∣ 1 := by simpa using h2
    have h4 := Nat.le_of_dvd one_pos h3
    omega
  have hmod_k_pk : ∀ k : ℕ, ¬ k ≡ p k [MOD n] := by
    intro k h1
    have h2 := (Nat.modEq_iff_dvd' (by simp only [hpdef]; omega)).mp h1
    simp only [hpdef] at h2
    have h3 : n ∣ n - 1 := by
      have h4 : k + (n - 1) - k = n - 1 := by omega
      rwa [h4] at h2
    have h5 := Nat.le_of_dvd (by omega) h3
    omega
  have hmod_k1_pk : ∀ k : ℕ, ¬ k + 1 ≡ p k [MOD n] := by
    intro k h1
    have h2 := (Nat.modEq_iff_dvd' (by simp only [hpdef]; omega)).mp h1
    simp only [hpdef] at h2
    have h3 : n ∣ n - 2 := by
      have h4 : k + (n - 1) - (k + 1) = n - 2 := by omega
      rwa [h4] at h2
    have h5 : n - 2 = 0 ∨ n ≤ n - 2 := by
      rcases Nat.eq_zero_or_pos (n - 2) with h6 | h6
      · exact Or.inl h6
      · exact Or.inr (Nat.le_of_dvd h6 h3)
    omega
  -- the far endpoints of the shared sides
  have hWex : ∀ k : ℕ, ∃ W : UpperHalfPlane, W ≠ v ∧
      dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
        = geodSeg ((e k)⁻¹ • v) ((e k)⁻¹ • W) := by
    intro k
    have hSide : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∈ polygonSides Γ τ₀ :=
      ⟨_, hadj k, rfl⟩
    have hgS : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) :=
      smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon (k + 1))
    have hgvert : (e k)⁻¹ • v ∈ polygonVertices Γ τ₀ :=
      smul_mem_polygonVertices hv (hecon k)
    have hend := isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hSide hgS
    obtain ⟨a, b, hab, heq⟩ :=
      exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hSide
    rw [heq] at hend
    rcases (isSegEndpoint_geodSeg_iff hab).mp hend with h1 | h1
    · refine ⟨e k • b, ?_, ?_⟩
      · intro h2
        rw [← h2, inv_smul_smul] at h1
        exact hab (h1.symm ▸ rfl)
      · rw [inv_smul_smul, heq, ← h1]
    · refine ⟨e k • a, ?_, ?_⟩
      · intro h2
        rw [← h2, inv_smul_smul] at h1
        exact hab (h1 ▸ rfl)
      · rw [inv_smul_smul, heq, ← h1, geodSeg_comm]
  choose W hWv hWrep using hWex
  -- the shared sides as radial segments at the vertex
  have hσ : ∀ k : ℕ, (e k • ·) '' dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
      = geodSeg v (W k) := by
    intro k
    rw [hWrep k, subgroup_smul_geodSeg, smul_inv_smul, smul_inv_smul]
  have hσsubT : ∀ k : ℕ, geodSeg v (W k) ⊆ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    rw [← hσ k]
    exact Set.image_mono fun x hx => hx.1
  have hσsubT' : ∀ k : ℕ, geodSeg v (W k) ⊆ (e (k + 1) • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    rw [← hσ k]
    rintro x ⟨y, hy, rfl⟩
    have h1 := smul_mem_dirichletSideSet_inv hy
    refine ⟨((e k)⁻¹ * e (k + 1))⁻¹ • y, h1.1, ?_⟩
    change e (k + 1) • ((e k)⁻¹ * e (k + 1))⁻¹ • y = e k • y
    rw [← mul_smul, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have hσbis : ∀ k : ℕ, ∀ x ∈ geodSeg v (W k),
      dist x (e k • τ₀) = dist x (e (k + 1) • τ₀) := by
    intro k x hx
    rw [← hσ k] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
      ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
    have h1 : dist y τ₀ = dist y (((e k)⁻¹ * e (k + 1)) • τ₀) := hy.2
    have e1 : dist (e k • y) (e k • τ₀) = dist y τ₀ := dist_smul (e k) y τ₀
    have e2 : dist (e k • y) (e (k + 1) • τ₀)
        = dist y (((e k)⁻¹ * e (k + 1)) • τ₀) := by
      calc dist (e k • y) (e (k + 1) • τ₀)
          = dist ((e k)⁻¹ • e k • y) ((e k)⁻¹ • e (k + 1) • τ₀) :=
            (dist_smul (e k)⁻¹ _ _).symm
        _ = dist y (((e k)⁻¹ * e (k + 1)) • τ₀) := by rw [inv_smul_smul, mul_smul]
    rw [e1, e2]
    exact h1
  -- the sign functionals of the two sides of each tile
  have hmove_next : ∀ k : ℕ, e k • τ₀ ≠ e (k + 1) • τ₀ := fun k => hcne _ _ (hmod_k_k1 k)
  have hmove_prev : ∀ k : ℕ, e k • τ₀ ≠ e (p k) • τ₀ := fun k => hcne _ _ (hmod_k_pk k)
  have hmove_np : ∀ k : ℕ, e (k + 1) • τ₀ ≠ e (p k) • τ₀ := fun k => hcne _ _ (hmod_k1_pk k)
  have hσprev_bis : ∀ k : ℕ, ∀ x ∈ geodSeg v (W (p k)),
      dist x (e k • τ₀) = dist x (e (p k) • τ₀) := by
    intro k x hx
    have h1 := hσbis (p k) x hx
    rw [hep1 k] at h1
    exact h1.symm
  have hσprev_subT : ∀ k : ℕ, geodSeg v (W (p k)) ⊆ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    have h1 := hσsubT' (p k)
    rw [hep1 k] at h1
    exact h1
  have hd2 : ∀ k : ℕ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart v (W (p k)) / discChart v (W k)).im ∧
      (∀ w ∈ (e k • ·) '' dirichletDomain Γ τ₀,
        0 ≤ σ * (discChart v w / discChart v (W k)).im) ∧
      (∀ w ∈ (e k • ·) '' interior (dirichletDomain Γ τ₀),
        0 < σ * (discChart v w / discChart v (W k)).im) := by
    intro k
    exact side_functional hΓ hdense (hmove_next k) (hveq k (k + 1))
      (hσbis k (W k) (right_mem_geodSeg v (W k))) (hWv k)
      (Ne.symm (hmove_np k)) (Ne.symm (hmove_prev k)) (hWv (p k))
      (fun w hw => hσprev_bis k w hw) (hσprev_subT k)
  have hd1 : ∀ k : ℕ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart v (W k) / discChart v (W (p k))).im ∧
      (∀ w ∈ (e k • ·) '' dirichletDomain Γ τ₀,
        0 ≤ σ * (discChart v w / discChart v (W (p k))).im) ∧
      (∀ w ∈ (e k • ·) '' interior (dirichletDomain Γ τ₀),
        0 < σ * (discChart v w / discChart v (W (p k))).im) := by
    intro k
    exact side_functional hΓ hdense (hmove_prev k) (hveq k (p k))
      (hσprev_bis k (W (p k)) (right_mem_geodSeg v (W (p k)))) (hWv (p k))
      (hmove_np k) (Ne.symm (hmove_next k)) (hWv k)
      (fun w hw => hσbis k w hw) (hσsubT k)
  choose σ₁ hσ₁pm hσ₁P hσ₁w hσ₁i using hd1
  choose σ₂ hσ₂pm hσ₂P hσ₂w hσ₂i using hd2
  -- two tiles meet only along the shared sides through the vertex
  have hδ'elem : ∀ k : ℕ, IsSideElement Γ τ₀ ((e k)⁻¹ * e (p k)) := by
    intro k
    have h1 := (hadj (p k)).inv
    have h2 : ((e (p k))⁻¹ * e (p k + 1))⁻¹ = (e k)⁻¹ * e (p k) := by
      rw [hep1 k, mul_inv_rev, inv_inv]
    rwa [h2] at h1
  have hσ'eq : ∀ k : ℕ, (e k • ·) '' dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k))
      = geodSeg v (W (p k)) := by
    intro k
    have h2 : ((e (p k))⁻¹ * e (p k + 1))⁻¹ = (e k)⁻¹ * e (p k) := by
      rw [hep1 k, mul_inv_rev, inv_inv]
    rw [← h2, ← smul_sideSet_inv, smul_smul_image]
    have h3 : e k * ((e (p k))⁻¹ * e (p k + 1))⁻¹ = e (p k) := by
      rw [mul_inv_rev, inv_inv, hep1 k, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [h3, hσ (p k)]
  have hTinter : ∀ k j : ℕ, ¬ k ≡ j [MOD n] → ∀ y : UpperHalfPlane,
      y ∈ (e k • ·) '' dirichletDomain Γ τ₀ → y ∈ (e j • ·) '' dirichletDomain Γ τ₀ →
      y = v ∨ y ∈ geodSeg v (W k) ∨ y ∈ geodSeg v (W (p k)) := by
    intro k j hmod y hyk hyj
    have hβmove : ((e k)⁻¹ * e j) • τ₀ ≠ τ₀ := by
      intro h0
      have h1 : e k • ((e k)⁻¹ * e j) • τ₀ = e k • τ₀ := congrArg (e k • ·) h0
      rw [← mul_smul, mul_inv_cancel_left] at h1
      exact hcne k j hmod h1.symm
    have hz₁S : (e k)⁻¹ • y ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j) := by
      refine inter_smul_subset_sideSet _ ⟨?_, ?_⟩
      · obtain ⟨w₁, hw₁, rfl⟩ := hyk
        rw [inv_smul_smul]
        exact hw₁
      · obtain ⟨w₂, hw₂, hw₂y⟩ := hyj
        have hw₂y' : e j • w₂ = y := hw₂y
        refine ⟨w₂, hw₂, ?_⟩
        change ((e k)⁻¹ * e j) • w₂ = (e k)⁻¹ • y
        rw [mul_smul, hw₂y']
    have hgS : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j) :=
      smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon j)
    by_cases hnt : (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)).Nontrivial
    · have hgvert : (e k)⁻¹ • v ∈ polygonVertices Γ τ₀ :=
        smul_mem_polygonVertices hv (hecon k)
      have hSβ : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j) ∈ polygonSides Γ τ₀ :=
        ⟨_, ⟨hβmove, hnt⟩, rfl⟩
      have hendβ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)) ((e k)⁻¹ • v) :=
        isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hSβ hgS
      have hA₁side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∈ polygonSides Γ τ₀ :=
        ⟨_, hadj k, rfl⟩
      have hgA₁ : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) :=
        smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon (k + 1))
      have hendA₁ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)))
          ((e k)⁻¹ • v) :=
        isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hA₁side hgA₁
      have hA₂side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) ∈ polygonSides Γ τ₀ :=
        ⟨_, hδ'elem k, rfl⟩
      have hgA₂ : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) :=
        smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon (p k))
      have hendA₂ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)))
          ((e k)⁻¹ • v) :=
        isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hA₂side hgA₂
      have hA12 : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
          ≠ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) := by
        intro h0
        have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree (hadj k) (hδ'elem k) h0
        have h2 := congrArg (e k • ·) h1
        simp only at h2
        rw [← mul_smul, ← mul_smul, mul_inv_cancel_left, mul_inv_cancel_left] at h2
        exact hmove_np k h2
      obtain ⟨s₁, hs₁, s₂, hs₂, hs12, he₁, he₂, hu2q⟩ :=
        exists_two_sides_at_vertex hΓ hfree hε hgap hdense hgvert
      have hm₁ := hu2q _ hA₁side hendA₁
      have hm₂ := hu2q _ hA₂side hendA₂
      have hmβ := hu2q _ hSβ hendβ
      have hcase : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)
          = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∨
          dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)
          = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) := by
        rcases hm₁ with h₁ | h₁ <;> rcases hm₂ with h₂ | h₂ <;> rcases hmβ with h₃ | h₃ <;>
          first
          | exact absurd (h₁.trans h₂.symm) hA12
          | exact Or.inl (h₃.trans h₁.symm)
          | exact Or.inr (h₃.trans h₂.symm)
      rcases hcase with h4 | h4
      · right
        left
        rw [← hσ k]
        rw [h4] at hz₁S
        exact ⟨(e k)⁻¹ • y, hz₁S, by change e k • (e k)⁻¹ • y = y; rw [smul_inv_smul]⟩
      · right
        right
        rw [← hσ'eq k]
        rw [h4] at hz₁S
        exact ⟨(e k)⁻¹ • y, hz₁S, by change e k • (e k)⁻¹ • y = y; rw [smul_inv_smul]⟩
    · have hsub : (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)).Subsingleton :=
        Set.not_nontrivial_iff.mp hnt
      have h1 : (e k)⁻¹ • y = (e k)⁻¹ • v := hsub hz₁S hgS
      left
      have h2 := congrArg (e k • ·) h1
      simp only at h2
      rw [smul_inv_smul, smul_inv_smul] at h2
      exact h2
  -- the working radius and chart scale
  obtain ⟨rc, hrc, hloc, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ v
  set r' : ℝ := min rc 1 with hr'def
  have hr' : 0 < r' := lt_min hrc one_pos
  have hr'1 : r' ≤ 1 := min_le_right _ _
  have hr'rc : r' ≤ rc := min_le_left _ _
  set sc : ℝ := Real.tanh (r' / 2) with hscdef
  have hsc0 : 0 < sc := by
    rw [hscdef, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hsc1 : sc < 1 := Real.tanh_lt_one _
  have hballT : ∀ y : UpperHalfPlane, dist v y < r' → ∃ k < n,
      y ∈ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro y hy
    have h1 : y ∈ Metric.ball v rc := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy hr'rc
    obtain ⟨δ, hδ, hδy⟩ := hcover y h1
    obtain ⟨k, ⟨hkn, hkc⟩, -⟩ := huniq δ hδ
    refine ⟨k, hkn, ?_⟩
    rw [← smul_image_eq_of_basepoint_eq hfree hkc]
    exact hδy
  -- corner filling: a strict sector point of the working ball lies in the tile
  have hfill : ∀ k, k < n → ∀ y₀ : UpperHalfPlane, dist v y₀ < r' →
      0 < σ₁ k * (discChart v y₀ / discChart v (W (p k))).im →
      0 < σ₂ k * (discChart v y₀ / discChart v (W k)).im →
      y₀ ∈ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro k hkn y₀ hy₀r hy₀1 hy₀2
    set OS : Set ℂ := {x : ℂ | ‖x‖ < sc ∧
        0 < σ₁ k * (x / discChart v (W (p k))).im ∧
        0 < σ₂ k * (x / discChart v (W k)).im} with hOSdef
    set POS : Set UpperHalfPlane :=
      {w : UpperHalfPlane | dist v w < r' ∧ discChart v w ∈ OS} with hPOSdef
    have hchartmem : ∀ w : UpperHalfPlane, dist v w < r' →
        0 < σ₁ k * (discChart v w / discChart v (W (p k))).im →
        0 < σ₂ k * (discChart v w / discChart v (W k)).im → w ∈ POS := by
      intro w h1 h2 h3
      exact ⟨h1, (dist_lt_iff_norm_chart hr').mp h1, h2, h3⟩
    have hy₀POS : y₀ ∈ POS := hchartmem y₀ hy₀r hy₀1 hy₀2
    have hOSpre : IsPreconnected OS :=
      sector_preconnected' (hσ₁pm k) (hσ₂pm k)
        (discChart_ne_zero (hWv (p k))) (discChart_ne_zero (hWv k)) (hσ₁P k) (hσ₂P k)
    have hOSsub : OS ⊆ {u : ℂ | ‖u‖ < 1} := fun u hu => lt_trans hu.1 hsc1
    have hPOSimg : (fun w : UpperHalfPlane => (w : ℂ)) '' POS = (fun u : ℂ =>
        ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u))) '' OS := by
      apply Set.Subset.antisymm
      · rintro x ⟨w, ⟨hwr, hwOS⟩, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj v (lt_trans hwOS.1 hsc1)
        have hww : w' = w := discChart_injective v hw'chart
        refine ⟨discChart v w, hwOS, ?_⟩
        change ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I
            * ((1 + discChart v w) / (1 - discChart v w)) = (w : ℂ)
        rw [← hw'coe, hww]
      · rintro x ⟨u, huOS, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj v (hOSsub huOS)
        refine ⟨w', ⟨?_, ?_⟩, ?_⟩
        · exact (dist_lt_iff_norm_chart hr').mpr (by rw [hw'chart]; exact huOS.1)
        · rw [hw'chart]
          exact huOS
        · change (w' : ℂ) = ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I
            * ((1 + u) / (1 - u))
          exact hw'coe
    have hFcont : ContinuousOn (fun u : ℂ =>
        ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
        {u : ℂ | ‖u‖ < 1} := by
      refine ContinuousOn.add continuousOn_const ?_
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div ((continuous_const.add continuous_id).continuousOn)
        ((continuous_const.sub continuous_id).continuousOn) ?_
      intro u hu h0
      have h1 : u = 1 := by linear_combination -h0
      rw [Set.mem_setOf_eq, h1] at hu
      simp at hu
    have hPOSpre : IsPreconnected POS := by
      have h1 : IsPreconnected ((fun u : ℂ =>
          ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u))) '' OS) :=
        hOSpre.image _ (hFcont.mono hOSsub)
      rw [← hPOSimg] at h1
      exact (UpperHalfPlane.isEmbedding_coe.toIsInducing.isPreconnected_image).mp h1
    have hPne : ∀ w ∈ POS, w ≠ v := by
      intro w hw h0
      have h1 := hw.2.2.1
      rw [h0, discChart_self, zero_div] at h1
      simp at h1
    have hPray : ∀ w ∈ POS, w ∉ geodSeg v (W k) ∧ w ∉ geodSeg v (W (p k)) := by
      intro w hw
      constructor
      · intro h1
        have h2 := ray_kill (hWv k) h1 (hPne w hw)
        have h3 := hw.2.2.2
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
      · intro h1
        have h2 := ray_kill (hWv (p k)) h1 (hPne w hw)
        have h3 := hw.2.2.1
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
    set A : Set UpperHalfPlane := (e k • ·) '' dirichletDomain Γ τ₀ with hAdef
    set C : Set UpperHalfPlane := ⋃ j ∈ (Finset.range n).erase k,
        (e j • ·) '' dirichletDomain Γ τ₀ with hCdef
    have hAcl : IsClosed A := isClosed_tile (e k)
    have hCcl : IsClosed C :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun j _ => isClosed_tile (e j)
    have hPsub : POS ⊆ A ∪ C := by
      intro w hw
      obtain ⟨j, hjn, hjw⟩ := hballT w hw.1
      by_cases hjk : j = k
      · subst hjk
        left
        exact hjw
      · right
        exact Set.mem_biUnion (Finset.mem_erase.mpr ⟨hjk, Finset.mem_range.mpr hjn⟩) hjw
    have hPAC : ∀ w ∈ POS, w ∈ A → w ∈ C → False := by
      intro w hwP hwA hwC
      rw [hCdef, Set.mem_iUnion₂] at hwC
      obtain ⟨j, hj, hjw⟩ := hwC
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      have hjn' : j < n := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
      have hmod : ¬ k ≡ j [MOD n] := by
        intro h0
        have hk' : k % n = k := Nat.mod_eq_of_lt hkn
        have hj' : j % n = j := Nat.mod_eq_of_lt hjn'
        rw [Nat.ModEq, hk', hj'] at h0
        exact hjk h0.symm
      rcases hTinter k j hmod w hwA hjw with h1 | h1 | h1
      · exact hPne w hwP h1
      · exact (hPray w hwP).1 h1
      · exact (hPray w hwP).2 h1
    have hgkD : (e k)⁻¹ • v ∈ dirichletDomain Γ τ₀ :=
      (smul_mem_polygonVertices hv (hecon k)).1
    have hgkτ : (e k)⁻¹ • v ≠ τ₀ := by
      intro h0
      have h1 := smul_basepoint_ne hv (hecon k)
      apply h1
      have h2 := congrArg (e k • ·) h0
      simp only at h2
      rw [smul_inv_smul] at h2
      exact h2.symm
    set d : ℝ := dist τ₀ ((e k)⁻¹ • v) with hddef
    have hd0 : 0 < d := dist_pos.mpr (Ne.symm hgkτ)
    set t : ℝ := 1 - r' / (2 * (d + 1)) with htdef
    have hx0 : 0 < r' / (2 * (d + 1)) := by positivity
    have hxhalf : r' / (2 * (d + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by simp only [htdef]; linarith,
      by simp only [htdef]; linarith⟩
    set xt : UpperHalfPlane := geodInterp τ₀ ((e k)⁻¹ • v) t with hxtdef
    have hxtseg : xt ∈ geodSeg τ₀ ((e k)⁻¹ • v) := geodInterp_mem_geodSeg _ _ ht01
    have hxtdist : dist τ₀ xt = t * d := dist_geodInterp_left _ _ ht01
    have hxtne : xt ≠ (e k)⁻¹ • v := by
      intro h0
      have h1 : dist τ₀ xt = d := by rw [h0]
      rw [hxtdist] at h1
      nlinarith
    have hxtint : xt ∈ interior (dirichletDomain Γ τ₀) :=
      mem_interior_of_mem_geodSeg hΓ hdense hgkD hxtseg hxtne
    set wt : UpperHalfPlane := e k • xt with hwtdef
    have hwtint : wt ∈ (e k • ·) '' interior (dirichletDomain Γ τ₀) := ⟨xt, hxtint, rfl⟩
    have hwtdist : dist v wt < r' := by
      have h1 : dist v wt = dist ((e k)⁻¹ • v) xt := by
        haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
          ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
        rw [hwtdef, ← dist_smul (e k) ((e k)⁻¹ • v) xt, smul_inv_smul]
      have h2 : dist ((e k)⁻¹ • v) xt = (1 - t) * d := by
        rw [hxtdef, dist_comm]
        have h3 := dist_geodInterp_pair τ₀ ((e k)⁻¹ • v) t 1
        rw [geodInterp_one] at h3
        rw [h3, abs_of_nonpos (by simp only [htdef]; linarith), ← hddef]
        ring
      rw [h1, h2]
      have h4 : (1 - t) * d = r' * (d / (2 * (d + 1))) := by
        simp only [htdef]
        field_simp
        ring
      rw [h4]
      have h5 : d / (2 * (d + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 hr'.le
      linarith
    have hwtPOS : wt ∈ POS :=
      hchartmem wt hwtdist (hσ₁i k wt hwtint) (hσ₂i k wt hwtint)
    have hwtA : wt ∈ A := ⟨xt, interior_subset hxtint, rfl⟩
    have hPC : ∀ w ∈ POS, w ∉ C := by
      intro w hw hwC
      by_cases hwA : w ∈ A
      · exact hPAC w hw hwA hwC
      · rw [isPreconnected_closed_iff] at hPOSpre
        obtain ⟨z, hz⟩ := hPOSpre A C hAcl hCcl hPsub ⟨wt, hwtPOS, hwtA⟩ ⟨w, hw, hwC⟩
        exact hPAC z hz.1 hz.2.1 hz.2.2
    rcases hPsub hy₀POS with h1 | h1
    · exact h1
    · exact absurd h1 (hPC y₀ hy₀POS)
  -- direction windows of the tiles and their measures
  set Dir : ℕ → Set ℝ := fun k => {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
      0 ≤ σ₁ k * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W (p k))).im ∧
      0 ≤ σ₂ k * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W k)).im} with hDirdef
  have hDirvol : ∀ k, volume (Dir k) = ENNReal.ofReal (sectorAngle v (W (p k)) (W k)) := by
    intro k
    exact vol_arc (hσ₁pm k) (hσ₂pm k) (discChart_ne_zero (hWv (p k)))
      (discChart_ne_zero (hWv k)) (hσ₁P k) (hσ₂P k)
  have hsc2 : (0 : ℝ) < sc / 2 := by linarith
  have hEnorm : ∀ φ : ℝ, ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖
      = sc / 2 := by
    intro φ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsc2]
  have hscale : ∀ (σv : ℝ) (u : ℂ) (φ : ℝ),
      (0 ≤ σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im ↔
        0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im) ∧
      (0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im →
        0 < σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im) := by
    intro σv u φ
    have h1 : ((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u
        = ((sc / 2 : ℝ) : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) / u) := mul_div_assoc _ _ _
    rw [h1, Complex.im_ofReal_mul]
    constructor
    · constructor
      · intro h2
        nlinarith
      · intro h2
        nlinarith
    · intro h2
      nlinarith
  have hDircov : Set.Ico (-Real.pi) Real.pi ⊆ ⋃ k ∈ Finset.range n, Dir k := by
    intro φ hφ
    have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
      rw [hEnorm φ]
      linarith
    obtain ⟨y, hychart, -⟩ := chart_surj v hu1
    have hyd : dist v y < r' := by
      refine (dist_lt_iff_norm_chart hr').mpr ?_
      rw [hychart, hEnorm φ]
      linarith
    obtain ⟨k, hkn, hyT⟩ := hballT y hyd
    have h₁ := hσ₁w k y hyT
    have h₂ := hσ₂w k y hyT
    rw [hychart] at h₁ h₂
    refine Set.mem_biUnion (Finset.mem_range.mpr hkn) ⟨hφ, ?_, ?_⟩
    · exact ((hscale (σ₁ k) (discChart v (W (p k))) φ).1).mp h₁
    · exact ((hscale (σ₂ k) (discChart v (W k)) φ).1).mp h₂
  have hDirdisj : ∀ k, k < n → ∀ j, j < n → k ≠ j → volume (Dir k ∩ Dir j) = 0 := by
    intro k hkn j hjn hkj
    have hzero : Dir k ∩ Dir j ⊆
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W (p k)))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W k))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W (p j)))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W j))) = 0} := by
      intro φ hφ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and] at hcon
      obtain ⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩ := hcon
      obtain ⟨⟨hφw, hc1k, hc2k⟩, -, hc1j, hc2j⟩ := hφ
      have hstrict : ∀ (σv : ℝ), (σv = 1 ∨ σv = -1) → ∀ y : UpperHalfPlane, y ≠ v →
          Real.sin (φ - Complex.arg (discChart v y)) ≠ 0 →
          0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v y).im →
          0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v y).im := by
        intro σv hσv y hyv hsin hle
        rcases lt_or_eq_of_le hle with h1 | h1
        · exact h1
        · exfalso
          have h2 : (Complex.exp ((φ : ℂ) * Complex.I) / discChart v y).im = 0 := by
            rcases mul_eq_zero.mp h1.symm with h3 | h3
            · rcases hσv with h4 | h4 <;> rw [h4] at h3 <;> norm_num at h3
            · exact h3
          rw [exp_div_im φ (discChart_ne_zero hyv)] at h2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · have h4 : ‖discChart v y‖ ≠ 0 :=
              norm_ne_zero_iff.mpr (discChart_ne_zero hyv)
            exact h4 (by rwa [inv_eq_zero] at h3)
          · exact hsin h3
      have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
        rw [hEnorm φ]
        linarith
      obtain ⟨y, hychart, -⟩ := chart_surj v hu1
      have hyd : dist v y < r' := by
        refine (dist_lt_iff_norm_chart hr').mpr ?_
        rw [hychart, hEnorm φ]
        linarith
      have hyk : y ∈ (e k • ·) '' dirichletDomain Γ τ₀ := by
        refine hfill k hkn y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₁pm k) _ (hWv (p k)) (fun h => hz1 hφw h) hc1k)
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₂pm k) _ (hWv k) (fun h => hz2 hφw h) hc2k)
      have hyj : y ∈ (e j • ·) '' dirichletDomain Γ τ₀ := by
        refine hfill j hjn y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₁pm j) _ (hWv (p j)) (fun h => hz3 hφw h) hc1j)
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₂pm j) _ (hWv j) (fun h => hz4 hφw h) hc2j)
      have hyv : y ≠ v := by
        intro h0
        rw [h0, discChart_self] at hychart
        have h1 := congrArg norm hychart
        rw [norm_zero, hEnorm φ] at h1
        linarith
      have hmod : ¬ k ≡ j [MOD n] := by
        intro h0
        have hk' : k % n = k := Nat.mod_eq_of_lt hkn
        have hj' : j % n = j := Nat.mod_eq_of_lt hjn
        rw [Nat.ModEq, hk', hj'] at h0
        exact hkj h0
      rcases hTinter k j hmod y hyk hyj with h1 | h1 | h1
      · exact hyv h1
      · have h2 := ray_kill (hWv k) h1 hyv
        rw [hychart, mul_div_assoc, Complex.im_ofReal_mul] at h2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · linarith
        · rw [exp_div_im φ (discChart_ne_zero (hWv k))] at h3
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact norm_ne_zero_iff.mpr (discChart_ne_zero (hWv k))
              (by rwa [inv_eq_zero] at h4)
          · exact hz2 hφw h4
      · have h2 := ray_kill (hWv (p k)) h1 hyv
        rw [hychart, mul_div_assoc, Complex.im_ofReal_mul] at h2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · linarith
        · rw [exp_div_im φ (discChart_ne_zero (hWv (p k)))] at h3
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact norm_ne_zero_iff.mpr (discChart_ne_zero (hWv (p k)))
              (by rwa [inv_eq_zero] at h4)
          · exact hz1 hφw h4
    refine measure_mono_null hzero ?_
    have hfin4 : ∀ y : UpperHalfPlane, y ≠ v → ({φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        Real.sin (φ - Complex.arg (discChart v y)) = 0}).Finite := by
      intro y hy
      exact finite_sin_zero (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_ <;>
      exact Set.Finite.measure_zero (hfin4 _ (by first
        | exact hWv (p k) | exact hWv k | exact hWv (p j) | exact hWv j)) volume
  have hDirmeas : ∀ k : ℕ, MeasurableSet (Dir k) := by
    intro k
    have hc : ∀ u : ℂ, Continuous fun φ : ℝ =>
        (Complex.exp ((φ : ℂ) * Complex.I) / u).im := by
      intro u
      exact Complex.continuous_im.comp ((Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).div_const u)
    have h1 : Dir k = Set.Ico (-Real.pi) Real.pi ∩
        ({φ : ℝ | 0 ≤ σ₁ k *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W (p k))).im}
          ∩ {φ : ℝ | 0 ≤ σ₂ k *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W k)).im}) := by
      ext φ
      simp only [hDirdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ico]
    rw [h1]
    refine measurableSet_Ico.inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
  have hEq2π : ∑ k ∈ Finset.range n, volume (Dir k) = ENNReal.ofReal (2 * Real.pi) := by
    have h1 : volume (⋃ k ∈ Finset.range n, Dir k)
        = ∑ k ∈ Finset.range n, volume (Dir k) := by
      refine measure_biUnion_finset₀ ?_ ?_
      · intro k hk j hj hkj
        exact hDirdisj k (Finset.mem_range.mp hk) j (Finset.mem_range.mp hj) hkj
      · intro k hk
        exact (hDirmeas k).nullMeasurableSet
    have h2 : volume (⋃ k ∈ Finset.range n, Dir k) = volume (Set.Ico (-Real.pi) Real.pi) := by
      apply le_antisymm
      · refine measure_mono (Set.iUnion₂_subset fun k hk => fun φ hφ => hφ.1)
      · exact measure_mono hDircov
    rw [← h1, h2, Real.volume_Ico]
    congr 1
    ring
  have hreal : ∑ k ∈ Finset.range n, sectorAngle v (W (p k)) (W k) = 2 * Real.pi := by
    have h1 : ENNReal.ofReal (∑ k ∈ Finset.range n, sectorAngle v (W (p k)) (W k))
        = ENNReal.ofReal (2 * Real.pi) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sectorAngle_nonneg v (W (p k)) (W k)]
      rw [← hEq2π]
      exact Finset.sum_congr rfl fun k _ => (hDirvol k).symm
    have h2 : 0 ≤ ∑ k ∈ Finset.range n, sectorAngle v (W (p k)) (W k) :=
      Finset.sum_nonneg fun k _ => sectorAngle_nonneg v (W (p k)) (W k)
    have h3 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    exact (ENNReal.ofReal_eq_ofReal_iff h2 h3).mp h1
  -- transport of angles along the subgroup action
  have hsect_smul : ∀ (γ : ↥Γ) (z w₁ w₂ : UpperHalfPlane),
      sectorAngle (γ • z) (γ • w₁) (γ • w₂) = sectorAngle z w₁ w₂ := by
    intro γ z w₁ w₂
    rw [Subgroup.smul_def, Subgroup.smul_def, Subgroup.smul_def]
    exact sectorAngle_smul _ z w₁ w₂
  have himg_one : ∀ S : Set UpperHalfPlane, ((1 : ↥Γ) • ·) '' S = S := by
    intro S
    rw [show (((1 : ↥Γ) • ·) : UpperHalfPlane → UpperHalfPlane) = id from
      funext fun x => one_smul _ x, Set.image_id]
  have hA₂rep : ∀ k : ℕ, dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k))
      = geodSeg ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) := by
    intro k
    have h1 := congrArg (fun S => ((e k)⁻¹ • ·) '' S) (hσ'eq k)
    simp only at h1
    rw [smul_smul_image, inv_mul_cancel, himg_one, subgroup_smul_geodSeg] at h1
    exact h1
  have hgmem : ∀ k : ℕ, (e k)⁻¹ • v ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀ :=
    fun k => ⟨MulAction.mem_orbit_iff.mpr ⟨(e k)⁻¹, rfl⟩,
      smul_mem_polygonVertices hv (hecon k)⟩
  have hαmatch : ∀ k : ℕ, α ((e k)⁻¹ • v) = sectorAngle v (W (p k)) (W k) := by
    intro k
    have hgvert : (e k)⁻¹ • v ∈ polygonVertices Γ τ₀ :=
      smul_mem_polygonVertices hv (hecon k)
    have hxkne : (e k)⁻¹ • v ≠ (e k)⁻¹ • W k := by
      intro h0
      exact hWv k (smul_left_cancel _ h0).symm
    have hxpkne : (e k)⁻¹ • v ≠ (e k)⁻¹ • W (p k) := by
      intro h0
      exact hWv (p k) (smul_left_cancel _ h0).symm
    have hA₁side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∈ polygonSides Γ τ₀ :=
      ⟨_, hadj k, rfl⟩
    have hA₂side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) ∈ polygonSides Γ τ₀ :=
      ⟨_, hδ'elem k, rfl⟩
    have hendA₁ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)))
        ((e k)⁻¹ • v) := by
      rw [hWrep k]
      exact (isSegEndpoint_geodSeg_iff hxkne).mpr (Or.inl rfl)
    have hendA₂ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)))
        ((e k)⁻¹ • v) := by
      rw [hA₂rep k]
      exact (isSegEndpoint_geodSeg_iff hxpkne).mpr (Or.inl rfl)
    have hA12 : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
        ≠ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) := by
      intro h0
      have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree (hadj k) (hδ'elem k) h0
      have h2 := congrArg (e k • ·) h1
      simp only at h2
      rw [← mul_smul, ← mul_smul, mul_inv_cancel_left, mul_inv_cancel_left] at h2
      exact hmove_np k h2
    obtain ⟨t₁, ht₁, t₂, ht₂, ht12, hte₁, hte₂, htu⟩ :=
      exists_two_sides_at_vertex hΓ hfree hε hgap hdense hgvert
    obtain ⟨s₁', hs₁', s₂', hs₂', hne', he₁', he₂', w₁', hw₁', w₂', hw₂', hw₁v', hw₂v',
      hval⟩ := hα _ (hgmem k)
    have hmA₁ := htu _ hA₁side hendA₁
    have hmA₂ := htu _ hA₂side hendA₂
    have hm₁ := htu _ hs₁' he₁'
    have hm₂ := htu _ hs₂' he₂'
    have hcase : (s₁' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∧
        s₂' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k))) ∨
        (s₁' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) ∧
        s₂' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))) := by
      rcases hmA₁ with hA | hA <;> rcases hmA₂ with hB | hB <;>
        rcases hm₁ with hC | hC <;> rcases hm₂ with hD | hD <;>
        first
        | exact absurd (hA.trans hB.symm) hA12
        | exact absurd (hC.trans hD.symm) hne'
        | exact Or.inl ⟨hC.trans hA.symm, hD.trans hB.symm⟩
        | exact Or.inr ⟨hC.trans hB.symm, hD.trans hA.symm⟩
    have htransport : sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k)
        = sectorAngle v (W (p k)) (W k) := by
      have h1 := hsect_smul (e k) ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k)
      rw [smul_inv_smul, smul_inv_smul, smul_inv_smul] at h1
      exact h1.symm
    rcases hcase with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, hWrep k] at hw₁'
      rw [h₂, hA₂rep k] at hw₂'
      rw [hval, ← htransport]
      calc sectorAngle ((e k)⁻¹ • v) w₁' w₂'
          = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W k) w₂' :=
            sectorAngle_ray_congr hw₁' (right_mem_geodSeg _ _) hw₁v'
              (Ne.symm hxkne) w₂'
        _ = sectorAngle ((e k)⁻¹ • v) w₂' ((e k)⁻¹ • W k) := sectorAngle_comm _ _ _
        _ = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k) :=
            sectorAngle_ray_congr hw₂' (right_mem_geodSeg _ _) hw₂v'
              (Ne.symm hxpkne) _
    · rw [h₁, hA₂rep k] at hw₁'
      rw [h₂, hWrep k] at hw₂'
      rw [hval, ← htransport]
      calc sectorAngle ((e k)⁻¹ • v) w₁' w₂'
          = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) w₂' :=
            sectorAngle_ray_congr hw₁' (right_mem_geodSeg _ _) hw₁v'
              (Ne.symm hxpkne) w₂'
        _ = sectorAngle ((e k)⁻¹ • v) w₂' ((e k)⁻¹ • W (p k)) := sectorAngle_comm _ _ _
        _ = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W k) ((e k)⁻¹ • W (p k)) :=
            sectorAngle_ray_congr hw₂' (right_mem_geodSeg _ _) hw₂v'
              (Ne.symm hxkne) _
        _ = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k) :=
            sectorAngle_comm _ _ _
  have hfin : (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀).Finite :=
    (finite_polygonVertices hΓ hfree hε hgap hdense).subset Set.inter_subset_right
  rw [finsum_mem_eq_finite_toFinset_sum α hfin, ← hreal]
  refine (Finset.sum_bij (fun k _ => (e k)⁻¹ • v) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [Set.Finite.mem_toFinset]
    exact hgmem k
  · intro k₁ hk₁ k₂ hk₂ hkk
    simp only at hkk
    have h1 : (e k₂ * (e k₁)⁻¹) • v = v := by
      rw [mul_smul, hkk, smul_inv_smul]
    have h2 := hfree (e k₂ * (e k₁)⁻¹) ⟨v, h1⟩ (e k₁ • τ₀)
    rw [mul_smul, inv_smul_smul] at h2
    have h3 := hcent k₂ k₁ h2
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk₂),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hk₁)] at h3
    exact h3.symm
  · intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨horb, hvert⟩ := hb
    obtain ⟨η, hη⟩ := MulAction.mem_orbit_iff.mp horb
    have hcon : η⁻¹ ∈ contactSet Γ τ₀ v := by
      rw [mem_contactSet_iff_mem_smul_dirichletDomain]
      refine ⟨η • v, ?_, ?_⟩
      · rw [hη]
        exact hvert.1
      · change η⁻¹ • η • v = v
        rw [inv_smul_smul]
    obtain ⟨k, ⟨hkn, hkc⟩, -⟩ := huniq η⁻¹ hcon
    refine ⟨k, Finset.mem_range.mpr hkn, ?_⟩
    change (e k)⁻¹ • v = b
    have h1 := inv_smul_eq_of_basepoint_eq hfree hkc v
    rw [inv_inv] at h1
    rw [← h1, hη]
  · intro k hk
    exact (hαmatch k).symm

set_option maxHeartbeats 400000 in
-- The class-partition bookkeeping over the vertex set elaborates several Finset partitions
-- in one declaration; the default heartbeat budget does not cover it.
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
  classical
  have hVfin : (polygonVertices Γ τ₀).Finite :=
    finite_polygonVertices hΓ hfree hε hgap hdense
  have hCfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine (hVfin.image (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  set 𝒱 : Finset UpperHalfPlane := hVfin.toFinset with h𝒱
  set 𝒬 : Finset (Set UpperHalfPlane) := hCfin.toFinset with h𝒬
  have hCsub : ∀ C ∈ polygonVertexClasses Γ τ₀, C ⊆ polygonVertices Γ τ₀ := by
    rintro C ⟨v, hv, rfl⟩
    exact Set.inter_subset_right
  have hfilter : ∀ C ∈ 𝒬, (↑(𝒱.filter (· ∈ C)) : Set UpperHalfPlane) = C := by
    intro C hC
    have hCmem : C ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC
      exact hC
    ext w
    simp only [Finset.coe_filter, Set.mem_setOf_eq, h𝒱, Set.Finite.mem_toFinset]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hCsub C hCmem h1, h1⟩⟩
  have hbi : 𝒱 = 𝒬.biUnion (fun C => 𝒱.filter (· ∈ C)) := by
    ext w
    constructor
    · intro hw
      have hwV : w ∈ polygonVertices Γ τ₀ := by
        rw [h𝒱, Set.Finite.mem_toFinset] at hw
        exact hw
      have hC' : (MulAction.orbit Γ w ∩ polygonVertices Γ τ₀ : Set UpperHalfPlane) ∈ 𝒬 := by
        rw [h𝒬, Set.Finite.mem_toFinset]
        exact ⟨w, hwV, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨_, hC', ?_⟩
      have hgoal : w ∈ 𝒱 ∧ w ∈ (MulAction.orbit Γ w ∩ polygonVertices Γ τ₀ :
          Set UpperHalfPlane) := ⟨hw, MulAction.mem_orbit_self w, hwV⟩
      simp only [Finset.mem_filter]
      exact hgoal
    · intro hw
      obtain ⟨C, -, hwC⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.filter_subset _ _) hwC
  have hdisj : ∀ C ∈ 𝒬, ∀ C' ∈ 𝒬, C ≠ C' →
      Disjoint (𝒱.filter (· ∈ C)) (𝒱.filter (· ∈ C')) := by
    intro C hC C' hC' hne
    rw [Finset.disjoint_left]
    intro w hwC hwC'
    apply hne
    have h1' : w ∈ C := (Finset.mem_filter.mp hwC).2
    have h2' : w ∈ C' := (Finset.mem_filter.mp hwC').2
    have hCmem : C ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC
      exact hC
    have hC'mem : C' ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC'
      exact hC'
    obtain ⟨v₁, hv₁, rfl⟩ := hCmem
    obtain ⟨v₂, hv₂, rfl⟩ := hC'mem
    have h3 : MulAction.orbit Γ v₁ = MulAction.orbit Γ v₂ := by
      rw [← MulAction.orbit_eq_iff.mpr h1'.1, ← MulAction.orbit_eq_iff.mpr h2'.1]
    rw [h3]
  have hclass2π : ∀ C ∈ 𝒬, ∑ w ∈ 𝒱.filter (· ∈ C), α w = 2 * Real.pi := by
    intro C hC
    have hCmem : C ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC
      exact hC
    have hCC := hfilter C hC
    obtain ⟨vC, hvC, hCdef⟩ := hCmem
    have hCfin' : (MulAction.orbit Γ vC ∩ polygonVertices Γ τ₀).Finite :=
      hVfin.subset Set.inter_subset_right
    have h2 := sum_interiorAngle_vertexClass hΓ hfree hε hgap hdense hvC
      (fun v' hv' => hα v' hv'.2)
    rw [finsum_mem_eq_finite_toFinset_sum α hCfin'] at h2
    rw [← h2]
    apply Finset.sum_congr
    · apply Finset.coe_injective
      rw [hCC, Set.Finite.coe_toFinset, hCdef]
    · intro x hx
      rfl
  rw [finsum_mem_eq_finite_toFinset_sum α hVfin]
  have hfinal : ∑ w ∈ 𝒱, α w = ∑ C ∈ 𝒬, (2 * Real.pi) := by
    rw [hbi, Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl hclass2π
  rw [hfinal, Finset.sum_const, nsmul_eq_mul]
  have hcount : (polygonVertexClassCount Γ τ₀ : ℝ) = (𝒬.card : ℝ) := by
    rw [polygonVertexClassCount, ← Set.ncard_coe_finset 𝒬, h𝒬, Set.Finite.coe_toFinset]
  rw [hcount]
  ring

/-- The complete geodesic through two points, realized as a perpendicular bisector: mirror
pair, equidistance at both points, and the collinearity of any equidistant point. -/
theorem apex_line_functional {z x : UpperHalfPlane} (_hxz : x ≠ z) :
    ∃ P Q : UpperHalfPlane, P ≠ Q ∧ dist z P = dist z Q ∧ dist x P = dist x Q ∧
      ∀ w : UpperHalfPlane, dist w P = dist w Q → w ∈ geodSeg z x ∨
        x ∈ geodSeg z w ∨ z ∈ geodSeg w x := by
  obtain ⟨g, hgz, hgx⟩ := exists_verticalize z x
  have hpm : (0 : ℝ) < ((⟨1, 1⟩ : ℂ)).im := by norm_num
  have hpm' : (0 : ℝ) < ((⟨-1, 1⟩ : ℂ)).im := by norm_num
  set ptP : UpperHalfPlane := UpperHalfPlane.mk ⟨1, 1⟩ hpm with hptP
  set ptM : UpperHalfPlane := UpperHalfPlane.mk ⟨-1, 1⟩ hpm' with hptM
  have hPre : ptP.re = 1 := rfl
  have hPim : ptP.im = 1 := rfl
  have hMre : ptM.re = -1 := rfl
  have hMim : ptM.im = 1 := rfl
  have hJP : UpperHalfPlane.J • ptP = ptM :=
    ext_re_im (by rw [J_smul_re, hPre, hMre]) (by rw [J_smul_im, hPim, hMim])
  have hJM : UpperHalfPlane.J • ptM = ptP := by
    rw [← hJP, J_J]
  have hplus : ∀ τ : UpperHalfPlane, dist τ ptP ≤ dist τ ptM ↔ 0 ≤ τ.re := by
    intro τ
    have h1 := setOf_dist_le_eq_of_im_eq' (a := ptP) (b := ptM)
      (by rw [hPim, hMim]) (by rw [hPre, hMre]; norm_num)
    have h2 := Set.ext_iff.mp h1 τ
    simp only [Set.mem_setOf_eq, hPre, hMre] at h2
    rw [h2]
    norm_num
  have hminus : ∀ τ : UpperHalfPlane, dist τ ptM ≤ dist τ ptP ↔ τ.re ≤ 0 := by
    intro τ
    have e1 : dist τ ptM = dist (UpperHalfPlane.J • τ) ptP := by
      rw [← dist_J τ ptM, hJM]
    have e2 : dist τ ptP = dist (UpperHalfPlane.J • τ) ptM := by
      rw [← dist_J τ ptP, hJP]
    rw [e1, e2, hplus, J_smul_re]
    constructor <;> intro h <;> linarith
  have hchar : ∀ w : UpperHalfPlane,
      dist w (g⁻¹ • ptM) = dist w (g⁻¹ • ptP) ↔ (g • w).re = 0 := by
    intro w
    have e1 : dist w (g⁻¹ • ptM) = dist (g • w) ptM := by
      rw [← dist_smul g w (g⁻¹ • ptM), smul_inv_smul]
    have e2 : dist w (g⁻¹ • ptP) = dist (g • w) ptP := by
      rw [← dist_smul g w (g⁻¹ • ptP), smul_inv_smul]
    rw [e1, e2]
    constructor
    · intro h
      have h1 := (hminus (g • w)).mp h.le
      have h2 := (hplus (g • w)).mp h.ge
      linarith
    · intro h
      have h1 := (hminus (g • w)).mpr h.le
      have h2 := (hplus (g • w)).mpr h.ge
      linarith
  have hMP : ptM ≠ ptP := by
    intro h0
    have h1 := congrArg UpperHalfPlane.re h0
    rw [hMre, hPre] at h1
    norm_num at h1
  refine ⟨g⁻¹ • ptM, g⁻¹ • ptP, fun h0 => hMP (MulAction.injective g⁻¹ h0), ?_, ?_, ?_⟩
  · exact (hchar z).mpr hgz
  · exact (hchar x).mpr hgx
  · intro w hw
    have hgw : (g • w).re = 0 := (hchar w).mp hw
    have hvert : ∀ Y₁ Y₂ Y₃ : UpperHalfPlane, Y₁.re = 0 → Y₂.re = 0 → Y₃.re = 0 →
        min Y₁.im Y₂.im ≤ Y₃.im → Y₃.im ≤ max Y₁.im Y₂.im → Y₃ ∈ geodSeg Y₁ Y₂ := by
      intro Y₁ Y₂ Y₃ h₁ h₂ h₃ hlo hhi
      rw [geodSeg_vertical_eq (h₁.trans h₂.symm)]
      exact ⟨h₃.trans h₁.symm, hlo, hhi⟩
    have hpull : ∀ a b c : UpperHalfPlane, g • a ∈ geodSeg (g • b) (g • c) →
        a ∈ geodSeg b c := by
      intro a b c hmem
      rw [← smul_geodSeg] at hmem
      obtain ⟨y, hy, hya⟩ := hmem
      rw [MulAction.injective g hya] at hy
      exact hy
    rcases le_total (g • w).im (g • z).im with hWZ | hWZ <;>
      rcases le_total (g • w).im (g • x).im with hWX | hWX <;>
      rcases le_total (g • z).im (g • x).im with hZX | hZX
    · exact Or.inr (Or.inr (hpull z w x (hvert _ _ _ hgw hgx hgz
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith))))
    · exact Or.inr (Or.inl (hpull x z w (hvert _ _ _ hgz hgw hgx
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith))))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith)))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith)))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith)))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith)))
    · exact Or.inr (Or.inl (hpull x z w (hvert _ _ _ hgz hgw hgx
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith))))
    · exact Or.inr (Or.inr (hpull z w x (hvert _ _ _ hgw hgx hgz
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith))))

/-- The sign functional of one boundary ray of a fan cone: the cone on the closed side,
radial segments through other side points strictly inside. -/
theorem cone_functional (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀)
    {a b : UpperHalfPlane} (hab : a ≠ b) (hseq : s = geodSeg a b) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart τ₀ b / discChart τ₀ a).im ∧
      (∀ w ∈ geodCone τ₀ s, 0 ≤ σ * (discChart τ₀ w / discChart τ₀ a).im) ∧
      (∀ x ∈ s, x ≠ a → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
        0 < σ * (discChart τ₀ w / discChart τ₀ a).im) := by
  have hτ₀s : τ₀ ∉ s := basepoint_notMem_side hΓ hfree hε hgap hdense hs
  have has : a ∈ s := hseq ▸ left_mem_geodSeg a b
  have hbs : b ∈ s := hseq ▸ right_mem_geodSeg a b
  have haτ : a ≠ τ₀ := fun h => hτ₀s (h ▸ has)
  have hxτ : ∀ x ∈ s, x ≠ τ₀ := fun x hx h => hτ₀s (h ▸ hx)
  have hfr : ∀ x ∈ s, x ∉ interior (dirichletDomain Γ τ₀) := by
    intro x hx hcon
    have h1 : x ∈ frontier (dirichletDomain Γ τ₀) := by
      rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
      exact ⟨s, hs, hx⟩
    rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at h1
    exact h1.2 hcon
  obtain ⟨γ, hγel, hsdef⟩ := hs
  have hbisτ : ∀ x ∈ s, ∀ y ∈ s, τ₀ ∉ geodSeg x y := by
    intro x hx y hy hτmem
    have h1 : ∀ w ∈ geodSeg x y, dist w τ₀ = dist w (γ • τ₀) := by
      intro w hw
      have hxb : dist x τ₀ = dist x (γ • τ₀) := (hsdef ▸ hx).2
      have hyb : dist y τ₀ = dist y (γ • τ₀) := (hsdef ▸ hy).2
      exact le_antisymm (geodSeg_subset_setOf_dist_le hxb.le hyb.le hw)
        (geodSeg_subset_setOf_dist_le hxb.ge hyb.ge hw)
    have h2 := h1 τ₀ hτmem
    rw [dist_self] at h2
    exact hγel.1 (dist_eq_zero.mp h2.symm).symm
  have hcollin : ∀ x ∈ s, x ≠ a →
      ¬(x ∈ geodSeg τ₀ a ∨ a ∈ geodSeg τ₀ x ∨ τ₀ ∈ geodSeg x a) := by
    rintro x hx hxa (h1 | h1 | h1)
    · exact hfr x hx (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain ⟨γ, hγel, hsdef⟩ has) h1 hxa)
    · exact hfr a has (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain ⟨γ, hγel, hsdef⟩ hx) h1 (Ne.symm hxa))
    · exact hbisτ x hx a has h1
  obtain ⟨P, Q, hPQ, hzeq, haeq, hline, hblt⟩ : ∃ P Q : UpperHalfPlane, P ≠ Q ∧
      dist τ₀ P = dist τ₀ Q ∧ dist a P = dist a Q ∧
      (∀ w : UpperHalfPlane, dist w P = dist w Q → w ∈ geodSeg τ₀ a ∨
        a ∈ geodSeg τ₀ w ∨ τ₀ ∈ geodSeg w a) ∧ dist b P < dist b Q := by
    obtain ⟨P, Q, hPQ, hzeq, haeq, hline⟩ := apex_line_functional haτ
    have hboff : dist b P ≠ dist b Q := by
      intro h0
      exact hcollin b hbs (Ne.symm hab) (hline b h0)
    rcases lt_or_gt_of_ne hboff with h1 | h1
    · exact ⟨P, Q, hPQ, hzeq, haeq, hline, h1⟩
    · exact ⟨Q, P, Ne.symm hPQ, hzeq.symm, haeq.symm,
        fun w hw => hline w hw.symm, h1⟩
  obtain ⟨g', ε', hε', hle, hge⟩ := bisector_normalizer hPQ
  obtain ⟨m, hm, hfeq, hflt⟩ := functional_sign hε' hle hge hzeq
  have hΨa0 : discChart τ₀ a ≠ 0 := discChart_ne_zero haτ
  have hratio := functional_ratio hε' hΨa0 (hfeq a haeq)
  set C : ℝ := ε' * (m * discChart τ₀ a).re with hCdef
  have hside_le : ∀ x ∈ s, dist x P ≤ dist x Q := by
    intro x hx
    rw [hseq] at hx
    exact geodSeg_subset_setOf_dist_le haeq.le hblt.le hx
  have hweakside : ∀ x ∈ s, 0 ≤ C * (discChart τ₀ x / discChart τ₀ a).im := by
    intro x hx
    rw [← hratio (discChart τ₀ x)]
    rcases lt_or_eq_of_le (hside_le x hx) with h1 | h1
    · exact (hflt x h1).le
    · exact (hfeq x h1).ge
  have hCb : 0 < C * (discChart τ₀ b / discChart τ₀ a).im := by
    rw [← hratio (discChart τ₀ b)]
    exact hflt b hblt
  have hCne : C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hCb
    exact lt_irrefl 0 hCb
  have hstrictside : ∀ x ∈ s, x ≠ a → 0 < C * (discChart τ₀ x / discChart τ₀ a).im := by
    intro x hx hxa
    rcases lt_or_eq_of_le (hweakside x hx) with h1 | h1
    · exact h1
    · exfalso
      have h2 : (discChart τ₀ x / discChart τ₀ a).im = 0 := by
        rcases mul_eq_zero.mp h1.symm with h3 | h3
        · exact absurd h3 hCne
        · exact h3
      have h3 : dist x P = dist x Q := by
        rcases lt_or_eq_of_le (hside_le x hx) with h4 | h4
        · exfalso
          have h5 := hflt x h4
          rw [hratio (discChart τ₀ x), h2, mul_zero] at h5
          exact lt_irrefl 0 h5
        · exact h4
      exact hcollin x hx hxa (hline x h3)
  have hconeval : ∀ w ∈ geodCone τ₀ s, w ≠ τ₀ → ∃ x ∈ s, ∃ t : ℝ, 0 < t ∧
      discChart τ₀ w = (t : ℂ) * discChart τ₀ x := by
    intro w hw hwτ
    obtain ⟨x, hxs, hwseg⟩ := mem_geodCone.mp hw
    obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hwseg hwτ
    exact ⟨x, hxs, t, ht, hchart⟩
  have hCcone : ∀ w ∈ geodCone τ₀ s, 0 ≤ C * (discChart τ₀ w / discChart τ₀ a).im := by
    intro w hw
    by_cases hwτ : w = τ₀
    · rw [hwτ, discChart_self, zero_div]
      simp
    · obtain ⟨x, hxs, t, ht, hchart⟩ := hconeval w hw hwτ
      rw [hchart, mul_div_assoc, Complex.im_ofReal_mul]
      nlinarith [hweakside x hxs, ht]
  have hCray : ∀ x ∈ s, x ≠ a → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
      0 < C * (discChart τ₀ w / discChart τ₀ a).im := by
    intro x hx hxa w hwseg hwτ
    obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hwseg hwτ
    rw [hchart, mul_div_assoc, Complex.im_ofReal_mul]
    nlinarith [hstrictside x hx hxa, ht]
  rcases lt_or_gt_of_ne hCne with hC1 | hC1
  · refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩
    · nlinarith [hCb]
    · intro w hw
      nlinarith [hCcone w hw]
    · intro x hx hxa w hw hwτ
      nlinarith [hCray x hx hxa w hw hwτ]
  · refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
    · nlinarith [hCb]
    · intro w hw
      nlinarith [hCcone w hw]
    · intro x hx hxa w hw hwτ
      nlinarith [hCray x hx hxa w hw hwτ]

set_option maxHeartbeats 400000 in
-- The fan assembly at the basepoint elaborates the cone functionals and the measure
-- bookkeeping in one declaration; the default heartbeat budget does not cover it.
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
  classical
  have hSfin : (polygonSides Γ τ₀).Finite := finite_polygonSides hΓ hfree hε hgap hdense
  have hepex : ∀ s ∈ polygonSides Γ τ₀, ∃ a b : UpperHalfPlane, a ≠ b ∧ s = geodSeg a b :=
    fun s hs => exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  choose! A B hAB hrep using hepex
  have hAmem : ∀ s ∈ polygonSides Γ τ₀, A s ∈ s := by
    intro s hs
    have h1 := left_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hBmem : ∀ s ∈ polygonSides Γ τ₀, B s ∈ s := by
    intro s hs
    have h1 := right_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hAτ : ∀ s ∈ polygonSides Γ τ₀, A s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hAmem s hs)
  have hBτ : ∀ s ∈ polygonSides Γ τ₀, B s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hBmem s hs)
  have hdA : ∀ s ∈ polygonSides Γ τ₀, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart τ₀ (B s) / discChart τ₀ (A s)).im ∧
      (∀ w ∈ geodCone τ₀ s, 0 ≤ σ * (discChart τ₀ w / discChart τ₀ (A s)).im) ∧
      (∀ x ∈ s, x ≠ A s → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
        0 < σ * (discChart τ₀ w / discChart τ₀ (A s)).im) := fun s hs =>
    cone_functional hΓ hfree hε hgap hdense hs (hAB s hs) (hrep s hs)
  have hdB : ∀ s ∈ polygonSides Γ τ₀, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart τ₀ (A s) / discChart τ₀ (B s)).im ∧
      (∀ w ∈ geodCone τ₀ s, 0 ≤ σ * (discChart τ₀ w / discChart τ₀ (B s)).im) ∧
      (∀ x ∈ s, x ≠ B s → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
        0 < σ * (discChart τ₀ w / discChart τ₀ (B s)).im) := fun s hs =>
    cone_functional hΓ hfree hε hgap hdense hs (Ne.symm (hAB s hs))
      ((hrep s hs).trans (geodSeg_comm _ _))
  choose! σA hσApm hσAB hσAcone hσAray using hdA
  choose! σB hσBpm hσBA hσBcone hσBray using hdB
  have hβmatch : ∀ s ∈ polygonSides Γ τ₀, β s = sectorAngle τ₀ (A s) (B s) := by
    intro s hs
    obtain ⟨a', b', hab', hs'eq, hval⟩ := hβ s hs
    have hends : ∀ x : UpperHalfPlane, IsSegEndpoint s x → x = A s ∨ x = B s := by
      intro x hx
      rw [hrep s hs] at hx
      exact (isSegEndpoint_geodSeg_iff (hAB s hs)).mp hx
    have ha' : a' = A s ∨ a' = B s := by
      refine hends a' ?_
      rw [hs'eq]
      exact (isSegEndpoint_geodSeg_iff hab').mpr (Or.inl rfl)
    have hb' : b' = A s ∨ b' = B s := by
      refine hends b' ?_
      rw [hs'eq]
      exact (isSegEndpoint_geodSeg_iff hab').mpr (Or.inr rfl)
    rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
    · exact absurd (h1.trans h2.symm) hab'
    · rw [hval, h1, h2]
    · rw [hval, h1, h2, sectorAngle_comm]
    · exact absurd (h1.trans h2.symm) hab'
  set r' : ℝ := min (ε / 2) 1 with hr'def
  have hr' : 0 < r' := lt_min (by linarith) one_pos
  have hr'1 : r' ≤ 1 := min_le_right _ _
  set sc : ℝ := Real.tanh (r' / 2) with hscdef
  have hsc0 : 0 < sc := by
    rw [hscdef, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hsc1 : sc < 1 := Real.tanh_lt_one _
  have hballC : ∀ y : UpperHalfPlane, dist τ₀ y < r' →
      ∃ s ∈ polygonSides Γ τ₀, y ∈ geodCone τ₀ s := by
    intro y hy
    have h1 : y ∈ dirichletDomain Γ τ₀ := by
      refine ball_subset_dirichletDomain hε hgap ?_
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    rw [dirichletDomain_eq_biUnion_geodCone hΓ hfree hε hgap hdense] at h1
    rw [Set.mem_iUnion₂] at h1
    obtain ⟨t, ht, hyt⟩ := h1
    exact ⟨t, ht, hyt⟩
  have hfillC : ∀ s ∈ polygonSides Γ τ₀, ∀ y₀ : UpperHalfPlane, dist τ₀ y₀ < r' →
      0 < σA s * (discChart τ₀ y₀ / discChart τ₀ (A s)).im →
      0 < σB s * (discChart τ₀ y₀ / discChart τ₀ (B s)).im →
      y₀ ∈ geodCone τ₀ s := by
    intro s hs y₀ hy₀r hy₀1 hy₀2
    set OS : Set ℂ := {x : ℂ | ‖x‖ < sc ∧
        0 < σA s * (x / discChart τ₀ (A s)).im ∧
        0 < σB s * (x / discChart τ₀ (B s)).im} with hOSdef
    set POS : Set UpperHalfPlane :=
      {w : UpperHalfPlane | dist τ₀ w < r' ∧ discChart τ₀ w ∈ OS} with hPOSdef
    have hchartmem : ∀ w : UpperHalfPlane, dist τ₀ w < r' →
        0 < σA s * (discChart τ₀ w / discChart τ₀ (A s)).im →
        0 < σB s * (discChart τ₀ w / discChart τ₀ (B s)).im → w ∈ POS := by
      intro w h1 h2 h3
      exact ⟨h1, (dist_lt_iff_norm_chart hr').mp h1, h2, h3⟩
    have hy₀POS : y₀ ∈ POS := hchartmem y₀ hy₀r hy₀1 hy₀2
    have hOSpre : IsPreconnected OS :=
      sector_preconnected' (hσApm s hs) (hσBpm s hs)
        (discChart_ne_zero (hAτ s hs)) (discChart_ne_zero (hBτ s hs))
        (hσAB s hs) (hσBA s hs)
    have hOSsub : OS ⊆ {u : ℂ | ‖u‖ < 1} := fun u hu => lt_trans hu.1 hsc1
    have hPOSimg : (fun w : UpperHalfPlane => (w : ℂ)) '' POS = (fun u : ℂ =>
        ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
          '' OS := by
      apply Set.Subset.antisymm
      · rintro x ⟨w, ⟨hwr, hwOS⟩, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj τ₀ (lt_trans hwOS.1 hsc1)
        have hww : w' = w := discChart_injective τ₀ hw'chart
        refine ⟨discChart τ₀ w, hwOS, ?_⟩
        change ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I
            * ((1 + discChart τ₀ w) / (1 - discChart τ₀ w)) = (w : ℂ)
        rw [← hw'coe, hww]
      · rintro x ⟨u, huOS, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj τ₀ (hOSsub huOS)
        refine ⟨w', ⟨?_, ?_⟩, ?_⟩
        · exact (dist_lt_iff_norm_chart hr').mpr (by rw [hw'chart]; exact huOS.1)
        · rw [hw'chart]
          exact huOS
        · change (w' : ℂ) = ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I
            * ((1 + u) / (1 - u))
          exact hw'coe
    have hFcont : ContinuousOn (fun u : ℂ =>
        ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
        {u : ℂ | ‖u‖ < 1} := by
      refine ContinuousOn.add continuousOn_const ?_
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div ((continuous_const.add continuous_id).continuousOn)
        ((continuous_const.sub continuous_id).continuousOn) ?_
      intro u hu h0
      have h1 : u = 1 := by linear_combination -h0
      rw [Set.mem_setOf_eq, h1] at hu
      simp at hu
    have hPOSpre : IsPreconnected POS := by
      have h1 : IsPreconnected ((fun u : ℂ =>
          ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
            '' OS) := hOSpre.image _ (hFcont.mono hOSsub)
      rw [← hPOSimg] at h1
      exact (UpperHalfPlane.isEmbedding_coe.toIsInducing.isPreconnected_image).mp h1
    have hPneτ : ∀ w ∈ POS, w ≠ τ₀ := by
      intro w hw h0
      have h1 := hw.2.2.1
      rw [h0, discChart_self, zero_div] at h1
      simp at h1
    have hPray : ∀ w ∈ POS, w ∉ geodSeg τ₀ (A s) ∧ w ∉ geodSeg τ₀ (B s) := by
      intro w hw
      constructor
      · intro h1
        have h2 := ray_kill (hAτ s hs) h1 (hPneτ w hw)
        have h3 := hw.2.2.1
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
      · intro h1
        have h2 := ray_kill (hBτ s hs) h1 (hPneτ w hw)
        have h3 := hw.2.2.2
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
    set Acone : Set UpperHalfPlane := geodCone τ₀ s with hAconedef
    set Ccone : Set UpperHalfPlane := ⋃ t ∈ hSfin.toFinset.erase s, geodCone τ₀ t
      with hCconedef
    have hAcl : IsClosed Acone := isClosed_geodCone_side hΓ hfree hε hgap hdense hs
    have hCcl : IsClosed Ccone := by
      refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun t ht => ?_
      have ht' : t ∈ polygonSides Γ τ₀ := by
        have := Finset.mem_of_mem_erase ht
        rwa [Set.Finite.mem_toFinset] at this
      exact isClosed_geodCone_side hΓ hfree hε hgap hdense ht'
    have hPsub : POS ⊆ Acone ∪ Ccone := by
      intro w hw
      obtain ⟨t, ht, htw⟩ := hballC w hw.1
      by_cases hts : t = s
      · subst hts
        left
        exact htw
      · right
        refine Set.mem_biUnion (Finset.mem_erase.mpr ⟨hts, ?_⟩) htw
        rw [Set.Finite.mem_toFinset]
        exact ht
    have hPAC : ∀ w ∈ POS, w ∈ Acone → w ∈ Ccone → False := by
      intro w hwP hwA hwC
      rw [hCconedef, Set.mem_iUnion₂] at hwC
      obtain ⟨t, ht, htw⟩ := hwC
      have hts : t ≠ s := (Finset.mem_erase.mp ht).1
      have ht' : t ∈ polygonSides Γ τ₀ := by
        have := (Finset.mem_erase.mp ht).2
        rwa [Set.Finite.mem_toFinset] at this
      obtain ⟨q, ⟨hq1, hq2⟩, hwseg⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense
        hs ht' hwA htw (hPneτ w hwP)
      obtain ⟨-, hqend, -⟩ := shared_point_endpoint hΓ hfree hε hgap hdense hs ht'
        (fun h => hts h.symm) hq1 hq2
      have hq' : q = A s ∨ q = B s := by
        rw [hrep s hs] at hqend
        exact (isSegEndpoint_geodSeg_iff (hAB s hs)).mp hqend
      rcases hq' with h1 | h1
      · rw [h1] at hwseg
        exact (hPray w hwP).1 hwseg
      · rw [h1] at hwseg
        exact (hPray w hwP).2 hwseg
    set mid : UpperHalfPlane := geodInterp (A s) (B s) (1 / 2) with hmiddef
    have hmidmem : mid ∈ s := by
      have h1 := geodInterp_mem_geodSeg (A s) (B s) (t := 1 / 2) (by norm_num)
      rwa [← hrep s hs] at h1
    have hdAB : 0 < dist (A s) (B s) := dist_pos.mpr (hAB s hs)
    have hdAmid : dist (A s) mid = 1 / 2 * dist (A s) (B s) :=
      dist_geodInterp_left (A s) (B s) (by norm_num)
    have hmidA : mid ≠ A s := by
      intro h0
      rw [h0, dist_self] at hdAmid
      linarith
    have hmidB : mid ≠ B s := by
      intro h0
      rw [h0] at hdAmid
      linarith
    have hmidτ : mid ≠ τ₀ :=
      fun h => basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hmidmem)
    set d : ℝ := dist τ₀ mid with hddef
    have hd0 : 0 < d := dist_pos.mpr (Ne.symm hmidτ)
    set t : ℝ := r' / (2 * (d + 1)) with htdef
    have ht0 : 0 < t := by positivity
    have hthalf : t ≤ 1 / 2 := by
      rw [htdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set wt : UpperHalfPlane := geodInterp τ₀ mid t with hwtdef
    have hwtseg : wt ∈ geodSeg τ₀ mid :=
      geodInterp_mem_geodSeg _ _ ⟨ht0.le, by linarith⟩
    have hwtdist : dist τ₀ wt = t * d :=
      dist_geodInterp_left _ _ ⟨ht0.le, by linarith⟩
    have hwtτ : wt ≠ τ₀ := by
      intro h0
      rw [h0, dist_self] at hwtdist
      nlinarith
    have hwtr : dist τ₀ wt < r' := by
      rw [hwtdist, htdef]
      have h5 : d / (2 * (d + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 hr'.le
      calc r' / (2 * (d + 1)) * d = r' * (d / (2 * (d + 1))) := by ring
        _ ≤ r' * (1 / 2) := h6
        _ < r' := by linarith
    have hwtPOS : wt ∈ POS :=
      hchartmem wt hwtr (hσAray s hs mid hmidmem hmidA wt hwtseg hwtτ)
        (hσBray s hs mid hmidmem hmidB wt hwtseg hwtτ)
    have hwtA : wt ∈ Acone := mem_geodCone.mpr ⟨mid, hmidmem, hwtseg⟩
    have hPC : ∀ w ∈ POS, w ∉ Ccone := by
      intro w hw hwC
      by_cases hwA : w ∈ Acone
      · exact hPAC w hw hwA hwC
      · rw [isPreconnected_closed_iff] at hPOSpre
        obtain ⟨z, hz⟩ := hPOSpre Acone Ccone hAcl hCcl hPsub ⟨wt, hwtPOS, hwtA⟩
          ⟨w, hw, hwC⟩
        exact hPAC z hz.1 hz.2.1 hz.2.2
    rcases hPsub hy₀POS with h1 | h1
    · exact h1
    · exact absurd h1 (hPC y₀ hy₀POS)
  set Dir : Set UpperHalfPlane → Set ℝ := fun s =>
      {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
      0 ≤ σA s * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (A s)).im ∧
      0 ≤ σB s * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (B s)).im}
    with hDirdef
  have hDirvol : ∀ s ∈ polygonSides Γ τ₀,
      volume (Dir s) = ENNReal.ofReal (sectorAngle τ₀ (A s) (B s)) := by
    intro s hs
    exact vol_arc (hσApm s hs) (hσBpm s hs) (discChart_ne_zero (hAτ s hs))
      (discChart_ne_zero (hBτ s hs)) (hσAB s hs) (hσBA s hs)
  have hsc2 : (0 : ℝ) < sc / 2 := by linarith
  have hEnorm : ∀ φ : ℝ, ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖
      = sc / 2 := by
    intro φ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsc2]
  have hscale : ∀ (σv : ℝ) (u : ℂ) (φ : ℝ),
      (0 ≤ σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im ↔
        0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im) ∧
      (0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im →
        0 < σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im) := by
    intro σv u φ
    have h1 : ((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u
        = ((sc / 2 : ℝ) : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) / u) :=
      mul_div_assoc _ _ _
    rw [h1, Complex.im_ofReal_mul]
    refine ⟨⟨fun h2 => by nlinarith, fun h2 => by nlinarith⟩, fun h2 => by nlinarith⟩
  have hDircov : Set.Ico (-Real.pi) Real.pi ⊆ ⋃ s ∈ hSfin.toFinset, Dir s := by
    intro φ hφ
    have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
      rw [hEnorm φ]
      linarith
    obtain ⟨y, hychart, -⟩ := chart_surj τ₀ hu1
    have hyd : dist τ₀ y < r' := by
      refine (dist_lt_iff_norm_chart hr').mpr ?_
      rw [hychart, hEnorm φ]
      linarith
    obtain ⟨s, hs, hyC⟩ := hballC y hyd
    have h₁ := hσAcone s hs y hyC
    have h₂ := hσBcone s hs y hyC
    rw [hychart] at h₁ h₂
    have hsmem : s ∈ hSfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hs
    refine Set.mem_biUnion hsmem ⟨hφ, ?_, ?_⟩
    · exact ((hscale (σA s) (discChart τ₀ (A s)) φ).1).mp h₁
    · exact ((hscale (σB s) (discChart τ₀ (B s)) φ).1).mp h₂
  have hDirdisj : ∀ s ∈ polygonSides Γ τ₀, ∀ s' ∈ polygonSides Γ τ₀, s ≠ s' →
      volume (Dir s ∩ Dir s') = 0 := by
    intro s hs s' hs' hss
    have hzero : Dir s ∩ Dir s' ⊆
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (A s))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (B s))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (A s'))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (B s'))) = 0} := by
      intro φ hφ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and] at hcon
      obtain ⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩ := hcon
      obtain ⟨⟨hφw, hc1k, hc2k⟩, -, hc1j, hc2j⟩ := hφ
      have hstrict : ∀ (σv : ℝ), (σv = 1 ∨ σv = -1) → ∀ y : UpperHalfPlane, y ≠ τ₀ →
          Real.sin (φ - Complex.arg (discChart τ₀ y)) ≠ 0 →
          0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ y).im →
          0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ y).im := by
        intro σv hσv y hyv hsin hle
        rcases lt_or_eq_of_le hle with h1 | h1
        · exact h1
        · exfalso
          have h2 : (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ y).im = 0 := by
            rcases mul_eq_zero.mp h1.symm with h3 | h3
            · rcases hσv with h4 | h4 <;> rw [h4] at h3 <;> norm_num at h3
            · exact h3
          rw [exp_div_im φ (discChart_ne_zero hyv)] at h2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · exact norm_ne_zero_iff.mpr (discChart_ne_zero hyv)
              (by rwa [inv_eq_zero] at h3)
          · exact hsin h3
      have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
        rw [hEnorm φ]
        linarith
      obtain ⟨y, hychart, -⟩ := chart_surj τ₀ hu1
      have hyd : dist τ₀ y < r' := by
        refine (dist_lt_iff_norm_chart hr').mpr ?_
        rw [hychart, hEnorm φ]
        linarith
      have hys : y ∈ geodCone τ₀ s := by
        refine hfillC s hs y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσApm s hs) _ (hAτ s hs)
            (fun h => hz1 hφw h) hc1k)
        · exact (hscale _ _ φ).2 (hstrict _ (hσBpm s hs) _ (hBτ s hs)
            (fun h => hz2 hφw h) hc2k)
      have hys' : y ∈ geodCone τ₀ s' := by
        refine hfillC s' hs' y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσApm s' hs') _ (hAτ s' hs')
            (fun h => hz3 hφw h) hc1j)
        · exact (hscale _ _ φ).2 (hstrict _ (hσBpm s' hs') _ (hBτ s' hs')
            (fun h => hz4 hφw h) hc2j)
      have hyτ : y ≠ τ₀ := by
        intro h0
        rw [h0, discChart_self] at hychart
        have h1 := congrArg norm hychart
        rw [norm_zero, hEnorm φ] at h1
        linarith
      obtain ⟨q, ⟨hq1, hq2⟩, hyseg⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense
        hs hs' hys hys' hyτ
      obtain ⟨-, hqend, -⟩ := shared_point_endpoint hΓ hfree hε hgap hdense hs hs'
        hss hq1 hq2
      have hq' : q = A s ∨ q = B s := by
        rw [hrep s hs] at hqend
        exact (isSegEndpoint_geodSeg_iff (hAB s hs)).mp hqend
      have hkill : ∀ z : UpperHalfPlane, z ≠ τ₀ → y ∈ geodSeg τ₀ z →
          Real.sin (φ - Complex.arg (discChart τ₀ z)) = 0 := by
        intro z hzτ hyz
        have h2 := ray_kill hzτ hyz hyτ
        rw [hychart, mul_div_assoc, Complex.im_ofReal_mul] at h2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · linarith
        · rw [exp_div_im φ (discChart_ne_zero hzτ)] at h3
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd (by rwa [inv_eq_zero] at h4)
              (norm_ne_zero_iff.mpr (discChart_ne_zero hzτ))
          · exact h4
      rcases hq' with h1 | h1
      · rw [h1] at hyseg
        exact hz1 hφw (hkill (A s) (hAτ s hs) hyseg)
      · rw [h1] at hyseg
        exact hz2 hφw (hkill (B s) (hBτ s hs) hyseg)
    refine measure_mono_null hzero ?_
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_ <;>
      exact Set.Finite.measure_zero
        (finite_sin_zero (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)) volume
  have hDirmeas : ∀ s : Set UpperHalfPlane, MeasurableSet (Dir s) := by
    intro s
    have hc : ∀ u : ℂ, Continuous fun φ : ℝ =>
        (Complex.exp ((φ : ℂ) * Complex.I) / u).im := by
      intro u
      exact Complex.continuous_im.comp ((Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).div_const u)
    have h1 : Dir s = Set.Ico (-Real.pi) Real.pi ∩
        ({φ : ℝ | 0 ≤ σA s *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (A s)).im}
          ∩ {φ : ℝ | 0 ≤ σB s *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (B s)).im}) := by
      ext φ
      simp only [hDirdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ico]
    rw [h1]
    refine measurableSet_Ico.inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
  have hEq2π : ∑ s ∈ hSfin.toFinset, volume (Dir s) = ENNReal.ofReal (2 * Real.pi) := by
    have h1 : volume (⋃ s ∈ hSfin.toFinset, Dir s)
        = ∑ s ∈ hSfin.toFinset, volume (Dir s) := by
      refine measure_biUnion_finset₀ ?_ ?_
      · intro s hsm s' hsm' hss
        refine hDirdisj s ?_ s' ?_ hss
        · rwa [Finset.mem_coe, Set.Finite.mem_toFinset] at hsm
        · rwa [Finset.mem_coe, Set.Finite.mem_toFinset] at hsm'
      · intro s hsm
        exact (hDirmeas s).nullMeasurableSet
    have h2 : volume (⋃ s ∈ hSfin.toFinset, Dir s)
        = volume (Set.Ico (-Real.pi) Real.pi) := by
      apply le_antisymm
      · exact measure_mono (Set.iUnion₂_subset fun s hsm => fun φ hφ => hφ.1)
      · exact measure_mono hDircov
    rw [← h1, h2, Real.volume_Ico]
    congr 1
    ring
  have hreal : ∑ s ∈ hSfin.toFinset, sectorAngle τ₀ (A s) (B s) = 2 * Real.pi := by
    have h1 : ENNReal.ofReal (∑ s ∈ hSfin.toFinset, sectorAngle τ₀ (A s) (B s))
        = ENNReal.ofReal (2 * Real.pi) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun s _ => sectorAngle_nonneg τ₀ (A s) (B s),
        ← hEq2π]
      refine Finset.sum_congr rfl fun s hsm => ?_
      rw [hDirvol s (by rwa [Set.Finite.mem_toFinset] at hsm)]
    have h2 : 0 ≤ ∑ s ∈ hSfin.toFinset, sectorAngle τ₀ (A s) (B s) :=
      Finset.sum_nonneg fun s _ => sectorAngle_nonneg τ₀ (A s) (B s)
    exact (ENNReal.ofReal_eq_ofReal_iff h2 (by positivity)).mp h1
  rw [finsum_mem_eq_finite_toFinset_sum β hSfin, ← hreal]
  refine Finset.sum_congr rfl fun s hsm => ?_
  exact hβmatch s (by rwa [Set.Finite.mem_toFinset] at hsm)


section
open Real Set UpperHalfPlane
open scoped NNReal Pointwise

/-! ## The combinatorial Gauss–Bonnet formula -/

set_option maxHeartbeats 400000 in
-- The fan-additivity, triangle-formula, and incidence double-count assembly elaborates in
-- one declaration; the default heartbeat budget does not cover it.
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
  classical
  have hSfin : (polygonSides Γ τ₀).Finite := finite_polygonSides hΓ hfree hε hgap hdense
  have hVfin : (polygonVertices Γ τ₀).Finite :=
    finite_polygonVertices hΓ hfree hε hgap hdense
  set 𝒮 : Finset (Set UpperHalfPlane) := hSfin.toFinset with h𝒮
  set 𝒱 : Finset UpperHalfPlane := hVfin.toFinset with h𝒱
  have hmem𝒮 : ∀ {s}, s ∈ 𝒮 → s ∈ polygonSides Γ τ₀ := fun {s} hs => by
    rw [h𝒮, Set.Finite.mem_toFinset] at hs; exact hs
  have hepex : ∀ s ∈ polygonSides Γ τ₀, ∃ a b : UpperHalfPlane, a ≠ b ∧ s = geodSeg a b :=
    fun s hs => exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  choose! A B hAB hrep using hepex
  have hfan : volume (dirichletDomain Γ τ₀) = ∑ s ∈ 𝒮, volume (geodCone τ₀ s) := by
    rw [dirichletDomain_eq_biUnion_geodCone hΓ hfree hε hgap hdense, ← hSfin.coe_toFinset,
      ← h𝒮, Finset.set_biUnion_coe]
    refine measure_biUnion_finset₀ ?_ ?_
    · intro s hs s' hs' hne
      exact volume_geodCone_inter_eq_zero hΓ hfree hε hgap hdense
        (hmem𝒮 (Finset.mem_coe.mp hs)) (hmem𝒮 (Finset.mem_coe.mp hs')) hne
    · intro s hs
      exact (isClosed_geodCone_side hΓ hfree hε hgap hdense
        (hmem𝒮 hs)).measurableSet.nullMeasurableSet
  have hAmem : ∀ s ∈ polygonSides Γ τ₀, A s ∈ s := by
    intro s hs
    have h1 := left_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hBmem : ∀ s ∈ polygonSides Γ τ₀, B s ∈ s := by
    intro s hs
    have h1 := right_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hAτ : ∀ s ∈ polygonSides Γ τ₀, A s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hAmem s hs)
  have hBτ : ∀ s ∈ polygonSides Γ τ₀, B s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hBmem s hs)
  have htri : ∀ s ∈ 𝒮, volume (geodCone τ₀ s) = ENNReal.ofReal
      (π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
        - sectorAngle (B s) τ₀ (A s)) := by
    intro s hs
    have hsP := hmem𝒮 hs
    conv_lhs => rw [hrep s hsP]
    exact volume_hyperbolicTriangle τ₀ (A s) (B s) (hAτ s hsP).symm (hBτ s hsP).symm
      (hAB s hsP)
  have hd0 : ∀ s ∈ 𝒮, 0 ≤ π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
      - sectorAngle (B s) τ₀ (A s) := fun s hs =>
    deficit_nonneg τ₀ (A s) (B s) (hAτ s (hmem𝒮 hs)).symm (hBτ s (hmem𝒮 hs)).symm
      (hAB s (hmem𝒮 hs))
  have hsum : volume (dirichletDomain Γ τ₀) = ENNReal.ofReal
      (∑ s ∈ 𝒮, (π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
        - sectorAngle (B s) τ₀ (A s))) := by
    rw [hfan, Finset.sum_congr rfl htri, ENNReal.ofReal_sum_of_nonneg hd0]
  have hcard : 𝒮.card = 2 * polygonSideCount Γ τ₀ := by
    rw [h𝒮, ← Set.ncard_eq_toFinset_card _ hSfin]
    exact ncard_polygonSides hΓ hfree hε hgap hdense
  have happex : ∑ s ∈ 𝒮, sectorAngle τ₀ (A s) (B s) = 2 * π := by
    have h := sum_apexAngle_basepoint hΓ hfree hε hgap hdense
      (β := fun s => sectorAngle τ₀ (A s) (B s))
      (fun s hs => ⟨A s, B s, hAB s hs, hrep s hs, rfl⟩)
    rwa [finsum_mem_eq_finite_toFinset_sum _ hSfin, ← h𝒮] at h
  have hbase2 : ∀ s ∈ polygonSides Γ τ₀,
      𝒱.filter (fun v => IsSegEndpoint s v) = {A s, B s} := by
    intro s hsP
    have hendA : IsSegEndpoint s (A s) := by
      have h := (isSegEndpoint_geodSeg_iff (hAB s hsP)).mpr (Or.inl rfl)
      rwa [← hrep s hsP] at h
    have hendB : IsSegEndpoint s (B s) := by
      have h := (isSegEndpoint_geodSeg_iff (hAB s hsP)).mpr (Or.inr rfl)
      rwa [← hrep s hsP] at h
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hend⟩
      rw [hrep s hsP] at hend
      exact (isSegEndpoint_geodSeg_iff (hAB s hsP)).mp hend
    · rintro (rfl | rfl)
      · refine ⟨?_, hendA⟩
        rw [h𝒱, Set.Finite.mem_toFinset]
        exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hsP hendA
      · refine ⟨?_, hendB⟩
        rw [h𝒱, Set.Finite.mem_toFinset]
        exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hsP hendB
  have hbases : ∀ s ∈ 𝒮, sectorAngle (A s) τ₀ (B s) + sectorAngle (B s) τ₀ (A s)
      = ∑ v ∈ 𝒱.filter (fun v => IsSegEndpoint s v),
          (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s)) := by
    intro s hs
    have hsP := hmem𝒮 hs
    rw [hbase2 s hsP, Finset.sum_insert (by
        simp only [Finset.mem_singleton]; exact hAB s hsP), Finset.sum_singleton,
      if_pos rfl, if_neg (Ne.symm (hAB s hsP))]
  have hswap : ∑ s ∈ 𝒮, ∑ v ∈ 𝒱.filter (fun v => IsSegEndpoint s v),
      (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))
      = ∑ v ∈ 𝒱, ∑ s ∈ 𝒮.filter (fun s => IsSegEndpoint s v),
          (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s)) := by
    simp_rw [Finset.sum_filter]
    exact Finset.sum_comm
  have hα : ∀ v ∈ polygonVertices Γ τ₀, IsInteriorAngleAt Γ τ₀ v
      (∑ s ∈ 𝒮.filter (fun s => IsSegEndpoint s v),
        (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))) := by
    intro v hv
    obtain ⟨s₁, hs₁, s₂, hs₂, hne, he₁, he₂, huniq⟩ :=
      exists_two_sides_at_vertex hΓ hfree hε hgap hdense hv
    have hfe : 𝒮.filter (fun s => IsSegEndpoint s v) = {s₁, s₂} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hsS, hend⟩
        exact huniq s (hmem𝒮 hsS) hend
      · rintro (rfl | rfl)
        · refine ⟨?_, he₁⟩
          rw [h𝒮, Set.Finite.mem_toFinset]
          exact hs₁
        · refine ⟨?_, he₂⟩
          rw [h𝒮, Set.Finite.mem_toFinset]
          exact hs₂
    have hother : ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v → ∃ w ∈ s, w ≠ v ∧
        (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))
          = sectorAngle v τ₀ w := by
      intro s hsP hend
      have hcase : v = A s ∨ v = B s := by
        rw [hrep s hsP] at hend
        exact (isSegEndpoint_geodSeg_iff (hAB s hsP)).mp hend
      rcases hcase with hva | hvb
      · refine ⟨B s, hBmem s hsP, ?_, by rw [if_pos hva]⟩
        rw [hva]
        exact Ne.symm (hAB s hsP)
      · have hvA : v ≠ A s := by
          rw [hvb]
          exact Ne.symm (hAB s hsP)
        refine ⟨A s, hAmem s hsP, ?_, by rw [if_neg hvA]⟩
        rw [hvb]
        exact hAB s hsP
    obtain ⟨w₁, hw₁s, hw₁v, hb₁⟩ := hother s₁ hs₁ he₁
    obtain ⟨w₂, hw₂s, hw₂v, hb₂⟩ := hother s₂ hs₂ he₂
    refine ⟨s₁, hs₁, s₂, hs₂, hne, he₁, he₂, w₁, hw₁s, w₂, hw₂s, hw₁v, hw₂v, ?_⟩
    rw [hfe, Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hne),
      Finset.sum_singleton, hb₁, hb₂,
      sectorAngle_eq_add_basepoint hΓ hfree hε hgap hdense hv hs₁ hs₂ hne he₁ he₂
        hw₁s hw₂s hw₁v hw₂v, sectorAngle_comm v w₁ τ₀]
  have hbtotal : ∑ v ∈ 𝒱, ∑ s ∈ 𝒮.filter (fun s => IsSegEndpoint s v),
      (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))
      = 2 * π * (polygonVertexClassCount Γ τ₀ : ℝ) := by
    have h := sum_interiorAngle_total hΓ hfree hε hgap hdense hα
    rwa [finsum_mem_eq_finite_toFinset_sum _ hVfin, ← h𝒱] at h
  rw [hsum]
  congr 1
  have e1 : ∑ s ∈ 𝒮, (π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
      - sectorAngle (B s) τ₀ (A s))
      = ∑ s ∈ 𝒮, π - ∑ s ∈ 𝒮, sectorAngle τ₀ (A s) (B s)
        - ∑ s ∈ 𝒮, (sectorAngle (A s) τ₀ (B s) + sectorAngle (B s) τ₀ (A s)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [e1, Finset.sum_const, hcard, happex, Finset.sum_congr rfl hbases, hswap, hbtotal]
  ring

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
  have hGB := volume_dirichletDomain_gaussBonnet hΓ hfree hε hgap hdense
  have hpos : 0 < volume (dirichletDomain Γ τ₀) :=
    lt_of_lt_of_le (volume_ball_pos τ₀ (half_pos hε))
      (measure_mono (ball_subset_dirichletDomain hε hgap))
  rw [hGB] at hpos
  have hlt : 0 < 2 * Real.pi * ((polygonSideCount Γ τ₀ : ℝ) - 1
      - (polygonVertexClassCount Γ τ₀ : ℝ)) := ENNReal.ofReal_pos.mp hpos
  have hgtR : (polygonVertexClassCount Γ τ₀ : ℝ) + 1 < (polygonSideCount Γ τ₀ : ℝ) := by
    nlinarith [Real.pi_pos]
  have hgtN : polygonVertexClassCount Γ τ₀ + 1 < polygonSideCount Γ τ₀ := by
    exact_mod_cast hgtR
  refine ⟨polygonSideCount Γ τ₀ - 1 - polygonVertexClassCount Γ τ₀, by omega, ?_⟩
  rw [hGB]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]

end

end RiemannDynamics
