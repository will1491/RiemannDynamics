/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Dirichlet
import RiemannDynamics.Hyperbolic.PlaneGeometry.TriangleArea
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Dirichlet polygon: sides, vertices, and the tile geometry

For a Fuchsian group with a translation-length gap and a dense orbit, the Dirichlet domain
is a compact geodesically convex polygon. This file defines the combinatorial data and
develops the point-set geometry of the tiles.

* `IsSideElement`, `polygonSides`, `polygonSidePairs`, `polygonSideCount` — the sides,
  their pairing `γ ↔ γ⁻¹`, and the pair count `m`.
* `tileCenters`, `polygonVertices`, `polygonVertexClasses`, `polygonVertexClassCount` —
  the vertices (points lying in at least three tiles) and the class count `c`.
* `geodConvex_dirichletDomain` — the Dirichlet domain is geodesically convex.
* Tiles as half-spaces: contact elements, the mirror across a geodesic, the oriented
  bisector normalizer, frontier crossings of segments, and radial segments inside tiles.
* The structure of sides and vertices: sides through a vertex end at the vertex, and the
  normalizer characterizations of the bisector and its strict sides.
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

/-- The identity is a contact element of every point of the Dirichlet domain: by definition
of the domain, `τ₀` itself already realizes the distance to its own orbit. -/
theorem one_mem_contactSet {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) :
    (1 : ↥Γ) ∈ contactSet Γ τ₀ z := by
  simp only [contactSet, Set.mem_setOf_eq, one_smul]
  exact dist_basepoint_eq_infDist hz

/-- A point on the side of `γ` has `γ` as a contact element: on that side the distances to
`τ₀` and to `γ • τ₀` agree, and the first is already minimal over the orbit. -/
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

/-- In a normalizing coordinate with orientation sign `ε' = ±1`, where the two half-spaces of
a distance comparison read as the sign conditions `ε' · Re (g • z) ≤ 0` and
`0 ≤ ε' · Re (g • z)`, a point equidistant from `p` and `q` is carried to the imaginary axis. -/
theorem normalizer_re_eq_zero {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {z : UpperHalfPlane} (hz : dist z p = dist z q) : (g • z).re = 0 := by
  have h := le_antisymm ((hle z).mp hz.le) ((hge z).mp hz.ge)
  rcases hε' with h1 | h1 <;> rw [h1] at h <;> linarith

/-- In such a normalizing coordinate the equidistance set of `p` and `q` is exactly the
preimage of the imaginary axis. -/
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

/-- In such a normalizing coordinate strict proximity to `p` over `q` is exactly the strict
sign condition `ε' · Re (g • z) < 0`. Only the second half-space hypothesis is used. -/
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

end RiemannDynamics
