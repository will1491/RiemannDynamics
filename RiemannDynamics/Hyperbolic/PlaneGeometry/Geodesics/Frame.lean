/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import RiemannDynamics.Hyperbolic.DiskModel.DiskMetric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Geodesic segments, frames, and angles on the upper half plane

Geodesic segments as triangle-equality sets, geodesic convexity, the
constant-speed parametrization data, cones and triangles, the disc-model frame
and sector angles, `SL(2, ℝ)`-equivariance, the frame along the imaginary
axis, vertical projection, and angle additivity.
-/

open scoped MatrixGroups

namespace RiemannDynamics

/-! ## Geodesic segments -/

/-- The **geodesic segment** between two points of the upper half plane: the points through
which the triangle inequality is an equality. -/
def geodSeg (a b : UpperHalfPlane) : Set UpperHalfPlane :=
  {z | dist a z + dist z b = dist a b}

/-- Membership in the geodesic segment, unfolded: `z` lies between `a` and `b` exactly when
the triangle inequality through `z` is an equality. -/
theorem mem_geodSeg {a b z : UpperHalfPlane} :
    z ∈ geodSeg a b ↔ dist a z + dist z b = dist a b :=
  Iff.rfl

/-- The left endpoint lies on its own geodesic segment. -/
theorem left_mem_geodSeg (a b : UpperHalfPlane) : a ∈ geodSeg a b := by
  simp [geodSeg]

/-- The right endpoint lies on its own geodesic segment. -/
theorem right_mem_geodSeg (a b : UpperHalfPlane) : b ∈ geodSeg a b := by
  simp [geodSeg]

/-- The geodesic segment is symmetric in its endpoints. -/
theorem geodSeg_comm (a b : UpperHalfPlane) : geodSeg a b = geodSeg b a := by
  ext z
  simp only [geodSeg, Set.mem_ofPred_eq]
  rw [dist_comm a z, dist_comm z b, dist_comm a b]
  constructor <;> intro h <;> linarith

/-- A degenerate segment is a single point. -/
theorem geodSeg_self (a : UpperHalfPlane) : geodSeg a a = {a} := by
  ext z
  simp only [geodSeg, Set.mem_ofPred_eq, dist_self, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 : 0 ≤ dist a z := dist_nonneg
    have h2 : 0 ≤ dist z a := dist_nonneg
    have h3 : dist z a = 0 := by linarith
    exact dist_eq_zero.mp h3
  · rintro rfl
    simp

/-- Geodesic segments transport along the isometric `SL(2, ℝ)`-action. -/
theorem smul_geodSeg (g : SL(2, ℝ)) (a b : UpperHalfPlane) :
    (g • ·) '' geodSeg a b = geodSeg (g • a) (g • b) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [geodSeg, Set.mem_ofPred_eq] at hw ⊢
    rw [dist_smul g a w, dist_smul g w b, dist_smul g a b]
    exact hw
  · intro hz
    refine ⟨g⁻¹ • z, ?_, smul_inv_smul g z⟩
    simp only [geodSeg, Set.mem_ofPred_eq] at hz ⊢
    have e1 : dist a (g⁻¹ • z) = dist (g • a) z := by
      calc dist a (g⁻¹ • z) = dist (g⁻¹ • (g • a)) (g⁻¹ • z) := by rw [inv_smul_smul]
        _ = dist (g • a) z := dist_smul g⁻¹ (g • a) z
    have e2 : dist (g⁻¹ • z) b = dist z (g • b) := by
      calc dist (g⁻¹ • z) b = dist (g⁻¹ • z) (g⁻¹ • (g • b)) := by rw [inv_smul_smul]
        _ = dist z (g • b) := dist_smul g⁻¹ z (g • b)
    rw [e1, e2, ← dist_smul g a b]
    exact hz

/-! ## Endpoints and geodesic convexity -/

/-- An **endpoint** of a set of points of the upper half plane: a member that is extreme for
the geodesic betweenness relation. -/
def IsSegEndpoint (s : Set UpperHalfPlane) (v : UpperHalfPlane) : Prop :=
  v ∈ s ∧ ∀ x ∈ s, ∀ y ∈ s, v ∈ geodSeg x y → v = x ∨ v = y

/-- A set is **geodesically convex** when it contains the geodesic segment between any two
of its points. -/
def GeodConvex (K : Set UpperHalfPlane) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, geodSeg a b ⊆ K

/-! ## The constant-speed parametrization -/

/-- The Euclidean center of the semicircle carrying the geodesic through two points of
distinct real parts: the unique real number equidistant from both points. -/
noncomputable def geodCenter (a b : UpperHalfPlane) : ℝ :=
  (Complex.normSq (a : ℂ) - Complex.normSq (b : ℂ)) / (2 * (a.re - b.re))

/-- The Euclidean radius of the semicircle carrying the geodesic through two points. -/
noncomputable def geodRadius (a b : UpperHalfPlane) : ℝ :=
  ‖(a : ℂ) - (geodCenter a b : ℂ)‖

/-- The radius is always positive: `a` lies off the real axis, so it never coincides with
the real number `geodCenter a b`. No relation between `a.re` and `b.re` is needed — in the
degenerate case `a.re = b.re` the center is the junk value `0` and the radius is `‖a‖`. -/
theorem geodRadius_pos (a b : UpperHalfPlane) : 0 < geodRadius a b := by
  rw [geodRadius, norm_pos_iff, sub_ne_zero]
  intro h
  have h1 := congrArg Complex.im h
  rw [UpperHalfPlane.coe_im, Complex.ofReal_im] at h1
  exact absurd h1 a.im_pos.ne'

/-- The arc-length coordinate of a point of the upper half plane on the semicircle centered
at `c`: the primitive `log (tan (θ/2))` of the hyperbolic length element `dθ / sin θ`,
evaluated at the angle `θ = arg (z - c)`. -/
noncomputable def circCoord (c : ℝ) (z : UpperHalfPlane) : ℝ :=
  Real.log (Real.tan (Complex.arg ((z : ℂ) - (c : ℂ)) / 2))

/-- The angle of the semicircle point at arc-length coordinate `u`: the inverse
`θ = 2 arctan (exp u)` of `u = log (tan (θ/2))`, valued in `(0, π)`. -/
noncomputable def circAngle (u : ℝ) : ℝ :=
  2 * Real.arctan (Real.exp u)

/-- The semicircle angle lies strictly between `0` and `π`, so its sine is positive — which
is what places `circPoint` in the upper half plane. -/
theorem sin_circAngle_pos (u : ℝ) : 0 < Real.sin (circAngle u) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have h := Real.arctan_pos.mpr (Real.exp_pos u)
    unfold circAngle
    linarith
  · have h := Real.arctan_lt_pi_div_two (Real.exp u)
    unfold circAngle
    linarith

/-- The point of the semicircle of center `c` and radius `r` at arc-length coordinate
`u`. -/
noncomputable def circPoint (c r u : ℝ) (hr : 0 < r) : UpperHalfPlane :=
  UpperHalfPlane.mk ⟨c + r * Real.cos (circAngle u), r * Real.sin (circAngle u)⟩
    (mul_pos hr (sin_circAngle_pos u))

open Classical in
/-- **Constant-speed geodesic interpolation** from `a` to `b`: at parameter `t ∈ [0, 1]` the
point of the segment at distance `t · dist a b` from `a`. On a vertical line the height is
log-linear; on a semicircle the arc-length coordinate is interpolated linearly. -/
noncomputable def geodInterp (a b : UpperHalfPlane) (t : ℝ) : UpperHalfPlane :=
  if a.re = b.re then
    UpperHalfPlane.mk ⟨a.re, Real.exp ((1 - t) * Real.log a.im + t * Real.log b.im)⟩
      (Real.exp_pos _)
  else
    circPoint (geodCenter a b) (geodRadius a b)
      ((1 - t) * circCoord (geodCenter a b) a + t * circCoord (geodCenter a b) b)
      (geodRadius_pos a b)

/-! ## Cones and triangles -/

/-- The **geodesic cone** over a set from an apex: the union of the geodesic segments from
the apex to the points of the set. -/
def geodCone (z : UpperHalfPlane) (s : Set UpperHalfPlane) : Set UpperHalfPlane :=
  ⋃ w ∈ s, geodSeg z w

/-- The **geodesic triangle** on three vertices: the cone from the first vertex over the
opposite side. -/
def hyperbolicTriangle (v₁ v₂ v₃ : UpperHalfPlane) : Set UpperHalfPlane :=
  geodCone v₁ (geodSeg v₂ v₃)

/-- Membership in a geodesic cone, unfolded: `w` lies in the cone from `z` over `s` exactly
when it lies on some geodesic segment from `z` to a point of `s`. -/
theorem mem_geodCone {z : UpperHalfPlane} {s : Set UpperHalfPlane} {w : UpperHalfPlane} :
    w ∈ geodCone z s ↔ ∃ x ∈ s, w ∈ geodSeg z x := by
  simp [geodCone]

/-! ## The disc-model frame and angles -/

/-- The **disc-model frame** at `z`: the affine Möbius normalization moving `z` to `i`
followed by the Cayley map `ξ ↦ (ξ - i) / (ξ + i)` onto the unit disc; the point `z` itself
is sent to the origin, and geodesics through `z` become Euclidean diameters. -/
noncomputable def discChart (z w : UpperHalfPlane) : ℂ :=
  (((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) - Complex.I) /
    (((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) + Complex.I)

/-- The disc-model frame at `z` sends `z` itself to the origin. -/
theorem discChart_self (z : UpperHalfPlane) : discChart z z = 0 := by
  have him : ((z.im : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast z.im_pos.ne'
  have h : ((z : ℂ) - (z.re : ℂ)) / (z.im : ℂ) = Complex.I := by
    rw [div_eq_iff him]
    apply Complex.ext
    · simp
    · simp
  rw [discChart, h, sub_self, zero_div]

/-- The **angle at `z` between the geodesic rays toward `w₁` and `w₂`**: the absolute
angular difference of the images of `w₁` and `w₂` under the disc-model frame at `z`, valued
in `[0, π]`. Convention: `sectorAngle z w₁ w₂ = |arg (discChart z w₂ / discChart z w₁)|`. -/
noncomputable def sectorAngle (z w₁ w₂ : UpperHalfPlane) : ℝ :=
  |Complex.arg (discChart z w₂ / discChart z w₁)|

/-- The angle between two geodesic rays is nonnegative. -/
theorem sectorAngle_nonneg (z w₁ w₂ : UpperHalfPlane) : 0 ≤ sectorAngle z w₁ w₂ :=
  abs_nonneg _

/-- The angle between two geodesic rays is at most `π`, being an unsigned argument. -/
theorem sectorAngle_le_pi (z w₁ w₂ : UpperHalfPlane) : sectorAngle z w₁ w₂ ≤ Real.pi :=
  Complex.abs_arg_le_pi _

/-- The angle between two geodesic rays does not depend on the order of the rays. -/
theorem sectorAngle_comm (z w₁ w₂ : UpperHalfPlane) :
    sectorAngle z w₁ w₂ = sectorAngle z w₂ w₁ := by
  unfold sectorAngle
  rcases eq_or_ne (discChart z w₁) 0 with h1 | h1
  · rw [h1, div_zero, zero_div, Complex.arg_zero]
  rcases eq_or_ne (discChart z w₂) 0 with h2 | h2
  · rw [h2, div_zero, zero_div, Complex.arg_zero]
  rw [show discChart z w₁ / discChart z w₂ = (discChart z w₂ / discChart z w₁)⁻¹ by
    rw [inv_div], Complex.arg_inv]
  split_ifs with hπ
  · rw [hπ]
  · rw [abs_neg]

/-! ## The disc-model frame: fractional form -/

/-- The coercion of a point of the upper half plane decomposes as `re + im·I`. -/
theorem coe_eq_re_add_im (z : UpperHalfPlane) :
    (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- The conjugate coercion decomposes as `re − im·I`. -/
theorem conj_coe (z : UpperHalfPlane) :
    (starRingEnd ℂ) (z : ℂ) = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- A point of the upper half plane never meets a conjugated one. -/
theorem sub_conj_ne_zero (z w : UpperHalfPlane) :
    (w : ℂ) - (starRingEnd ℂ) (z : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at him
  have h1 : 0 < w.im := w.im_pos
  have h2 : 0 < z.im := z.im_pos
  linarith

/-- The disc-model frame in fractional form: `discChart z w = (w − z)/(w − z̄)`. -/
theorem discChart_eq (z w : UpperHalfPlane) :
    discChart z w = ((w : ℂ) - (z : ℂ)) / ((w : ℂ) - (starRingEnd ℂ) (z : ℂ)) := by
  have him : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  have hden := sub_conj_ne_zero z w
  have hden1 : ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) + Complex.I
      = ((w : ℂ) - (starRingEnd ℂ) (z : ℂ)) / (z.im : ℂ) := by
    rw [conj_coe]
    field_simp
    ring
  have hden1' : ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) + Complex.I ≠ 0 := by
    rw [hden1]
    exact div_ne_zero hden him
  rw [discChart, div_eq_div_iff hden1' hden, conj_coe, coe_eq_re_add_im z]
  field_simp
  ring

/-- The frame vanishes exactly at the base point. -/
theorem discChart_eq_zero_iff {z w : UpperHalfPlane} : discChart z w = 0 ↔ w = z := by
  rw [discChart_eq, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact UpperHalfPlane.ext (sub_eq_zero.mp h)
    · exact absurd h (sub_conj_ne_zero z w)
  · rintro rfl
    exact Or.inl (sub_self _)

/-- Only the basepoint is sent to the origin by its own disc-model frame. -/
theorem discChart_ne_zero {z w : UpperHalfPlane} (h : w ≠ z) : discChart z w ≠ 0 :=
  fun h0 => h (discChart_eq_zero_iff.mp h0)

/-- The angle of a nondegenerate ray with itself is zero. -/
theorem sectorAngle_self {z w : UpperHalfPlane} (h : w ≠ z) : sectorAngle z w w = 0 := by
  unfold sectorAngle
  rw [div_self (discChart_ne_zero h), Complex.arg_one, abs_zero]

/-! ## Transport of the metric into the disc model -/

/-- Imaginary part of a quotient by a real number. -/
theorem div_ofReal_im (a : ℂ) (r : ℝ) : (a / (r : ℂ)).im = a.im / r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal, mul_zero, zero_div,
      sub_zero]
    field_simp

/-- The affine normalization at `z`, as a point of the upper half plane. -/
noncomputable def affPt (z w : UpperHalfPlane) : UpperHalfPlane :=
  UpperHalfPlane.mk (((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ)) (by
    rw [div_ofReal_im]
    simp only [Complex.sub_im, Complex.ofReal_im, UpperHalfPlane.coe_im, sub_zero]
    exact div_pos w.im_pos z.im_pos)

/-- The affine normalization at `z` reads as `w ↦ (w - Re z) / Im z`. -/
theorem affPt_coe (z w : UpperHalfPlane) :
    ((affPt z w : UpperHalfPlane) : ℂ) = ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) := rfl

/-- The affine normalization at `z` rescales heights by `1 / Im z`, so it carries `z`
itself to height `1`. -/
theorem affPt_im (z w : UpperHalfPlane) : (affPt z w).im = w.im / z.im := by
  change ((((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ))).im = w.im / z.im
  rw [div_ofReal_im]
  simp only [Complex.sub_im, Complex.ofReal_im, UpperHalfPlane.coe_im, sub_zero]

/-- The affine normalization is an isometry of the upper half plane. -/
theorem dist_affPt (z w w' : UpperHalfPlane) :
    dist (affPt z w) (affPt z w') = dist w w' := by
  rw [UpperHalfPlane.dist_eq, UpperHalfPlane.dist_eq]
  congr 1
  rw [Complex.dist_eq, Complex.dist_eq, affPt_coe, affPt_coe, affPt_im,
    affPt_im]
  have him : (0 : ℝ) < z.im := z.im_pos
  have hsub : ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) - ((w' : ℂ) - (z.re : ℂ)) / (z.im : ℂ)
      = ((w : ℂ) - (w' : ℂ)) / (z.im : ℂ) := by ring
  rw [hsub, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos him]
  have hsq : w.im / z.im * (w'.im / z.im) = w.im * w'.im / z.im ^ 2 := by ring
  rw [hsq, Real.sqrt_div (by positivity), Real.sqrt_sq him.le]
  have hS : 0 < Real.sqrt (w.im * w'.im) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- The frame realizes the hyperbolic distance as the Poincaré disc distance. -/
theorem hDD_eq_dist (z w w' : UpperHalfPlane) :
    hyperbolicDistDisk (discChart z w) (discChart z w')
      = dist (affPt z w) (affPt z w') := by
  have h1 : 0 < ((((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ))).im := (affPt z w).2
  have h1' : 0 < ((((w' : ℂ) - (z.re : ℂ)) / (z.im : ℂ))).im := (affPt z w').2
  have hmem : discChart z w ∈ Metric.ball (0 : ℂ) 1 :=
    halfPlaneToCayley_mem_ball h1
  have hmem' : discChart z w' ∈ Metric.ball (0 : ℂ) 1 :=
    halfPlaneToCayley_mem_ball h1'
  rw [hyperbolicDistDisk_eq_upperHalfPlane_dist hmem hmem']
  congr 1
  · apply UpperHalfPlane.ext
    change cayleyToHalfPlane (discChart z w) = _
    exact cayleyToHalfPlane_halfPlaneToCayley h1
  · apply UpperHalfPlane.ext
    change cayleyToHalfPlane (discChart z w') = _
    exact cayleyToHalfPlane_halfPlaneToCayley h1'

/-- The hyperbolic distance transported through the frame at any base point. -/
theorem dist_eq_hDD (z w w' : UpperHalfPlane) :
    dist w w' = hyperbolicDistDisk (discChart z w) (discChart z w') := by
  rw [hDD_eq_dist, dist_affPt]

/-- Frame values lie in the open unit disc. -/
theorem norm_discChart_lt_one (z w : UpperHalfPlane) : ‖discChart z w‖ < 1 := by
  have h1 : 0 < ((((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ))).im := (affPt z w).2
  have := halfPlaneToCayley_mem_ball h1
  rwa [Metric.mem_ball, dist_zero_right] at this

/-! ## The triangle equality forces collinear frame values -/

/-- Equality in the hyperbolic triangle inequality from the origin of the disc forces the
Euclidean equality `‖u − u'‖ = ‖u‖ − ‖u'‖`. -/
theorem norm_sub_of_between {u u' : ℂ} (hu : ‖u‖ < 1) (hu' : ‖u'‖ < 1)
    (h : hyperbolicDistDisk 0 u' + hyperbolicDistDisk u' u = hyperbolicDistDisk 0 u) :
    ‖u - u'‖ = ‖u‖ - ‖u'‖ := by
  have ha0 : (0 : ℝ) ≤ ‖u'‖ := norm_nonneg _
  have hb0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
  have ha2 : 0 < 1 - ‖u'‖ ^ 2 := by nlinarith
  have hb2 : 0 < 1 - ‖u‖ ^ 2 := by nlinarith
  have hsa : 0 < Real.sqrt (1 - ‖u'‖ ^ 2) := Real.sqrt_pos.mpr ha2
  have hsb : 0 < Real.sqrt (1 - ‖u‖ ^ 2) := Real.sqrt_pos.mpr hb2
  have e1 : hyperbolicDistDisk 0 u'
      = 2 * Real.arsinh (‖u'‖ / Real.sqrt (1 - ‖u'‖ ^ 2)) := by
    unfold hyperbolicDistDisk
    rw [zero_sub, norm_neg, norm_zero]
    norm_num
  have e3 : hyperbolicDistDisk 0 u
      = 2 * Real.arsinh (‖u‖ / Real.sqrt (1 - ‖u‖ ^ 2)) := by
    unfold hyperbolicDistDisk
    rw [zero_sub, norm_neg, norm_zero]
    norm_num
  have e2 : hyperbolicDistDisk u' u = 2 * Real.arsinh
      (‖u - u'‖ / (Real.sqrt (1 - ‖u'‖ ^ 2) * Real.sqrt (1 - ‖u‖ ^ 2))) := by
    unfold hyperbolicDistDisk
    rw [norm_sub_rev, Real.sqrt_mul ha2.le]
  rw [e1, e2, e3] at h
  have harsinh : Real.arsinh
      (‖u - u'‖ / (Real.sqrt (1 - ‖u'‖ ^ 2) * Real.sqrt (1 - ‖u‖ ^ 2)))
      = Real.arsinh (‖u‖ / Real.sqrt (1 - ‖u‖ ^ 2))
        - Real.arsinh (‖u'‖ / Real.sqrt (1 - ‖u'‖ ^ 2)) := by linarith
  have hA2 : Real.sqrt (1 + (‖u'‖ / Real.sqrt (1 - ‖u'‖ ^ 2)) ^ 2)
      = 1 / Real.sqrt (1 - ‖u'‖ ^ 2) := by
    rw [div_pow, Real.sq_sqrt ha2.le,
      show 1 + ‖u'‖ ^ 2 / (1 - ‖u'‖ ^ 2) = (1 - ‖u'‖ ^ 2)⁻¹ by field_simp; ring,
      Real.sqrt_inv, one_div]
  have hB2 : Real.sqrt (1 + (‖u‖ / Real.sqrt (1 - ‖u‖ ^ 2)) ^ 2)
      = 1 / Real.sqrt (1 - ‖u‖ ^ 2) := by
    rw [div_pow, Real.sq_sqrt hb2.le,
      show 1 + ‖u‖ ^ 2 / (1 - ‖u‖ ^ 2) = (1 - ‖u‖ ^ 2)⁻¹ by field_simp; ring,
      Real.sqrt_inv, one_div]
  have hM := congrArg Real.sinh harsinh
  rw [Real.sinh_arsinh, Real.sinh_sub, Real.sinh_arsinh, Real.sinh_arsinh,
    Real.cosh_arsinh, Real.cosh_arsinh, hA2, hB2] at hM
  have hM' : ‖u - u'‖ / (Real.sqrt (1 - ‖u'‖ ^ 2) * Real.sqrt (1 - ‖u‖ ^ 2))
      = (‖u‖ - ‖u'‖) / (Real.sqrt (1 - ‖u'‖ ^ 2) * Real.sqrt (1 - ‖u‖ ^ 2)) := by
    rw [hM]
    field_simp
  have hSne : Real.sqrt (1 - ‖u'‖ ^ 2) * Real.sqrt (1 - ‖u‖ ^ 2) ≠ 0 :=
    (mul_pos hsa hsb).ne'
  rw [div_eq_div_iff hSne hSne] at hM'
  exact mul_right_cancel₀ hSne hM'

/-- The Euclidean equality `‖u − u'‖ = ‖u‖ − ‖u'‖` places `u'` on the open ray toward `u`. -/
theorem exists_smul_of_norm_sub {u u' : ℂ} (h : ‖u - u'‖ = ‖u‖ - ‖u'‖) (h0 : u' ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ u' = (t : ℂ) * u := by
  rcases eq_or_ne u u' with rfl | hne
  · exact ⟨1, one_pos, by rw [Complex.ofReal_one, one_mul]⟩
  set v := u - u' with hv
  have hvne : v ≠ 0 := sub_ne_zero.mpr hne
  have hadd : u' + v = u := by rw [hv]; ring
  have hsum : ‖u' + v‖ = ‖u'‖ + ‖v‖ := by
    rw [hadd, hv, h]
    ring
  have hkey : (u' * (starRingEnd ℂ) v).re = ‖u'‖ * ‖v‖ := by
    have hsq := congrArg (· ^ 2) hsum
    try simp only at hsq
    rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm u', ← Complex.sq_norm v] at hsq
    nlinarith [hsq]
  set ζ := u' * (starRingEnd ℂ) v with hζ
  have habs : ‖ζ‖ = ‖u'‖ * ‖v‖ := by
    rw [hζ, norm_mul, Complex.norm_conj]
  have hnormpos : 0 < ‖u'‖ * ‖v‖ :=
    mul_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr hvne)
  have him : ζ.im = 0 := by
    have h2 : ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have him2 : ζ.im ^ 2 = 0 := by nlinarith [hkey, habs, h2]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp him2
  have hζval : ζ = ((‖u'‖ * ‖v‖ : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hkey, Complex.ofReal_re]
    · rw [him, Complex.ofReal_im]
  set s : ℝ := ‖u'‖ * ‖v‖ / Complex.normSq v with hs
  have hnsqpos : 0 < Complex.normSq v := Complex.normSq_pos.mpr hvne
  have hspos : 0 < s := div_pos hnormpos hnsqpos
  have hu'v : u' = (s : ℂ) * v := by
    have hmul := congrArg (· * v) hζval
    try simp only at hmul
    rw [hζ, mul_assoc, mul_comm ((starRingEnd ℂ) v) v, Complex.mul_conj] at hmul
    push_cast at hmul
    rw [hs]
    push_cast
    rw [div_mul_eq_mul_div,
      eq_div_iff (by exact_mod_cast hnsqpos.ne' : ((Complex.normSq v : ℝ) : ℂ) ≠ 0)]
    linear_combination hmul
  have huv : u = ((s + 1 : ℝ) : ℂ) * v := by
    rw [← hadd, hu'v]
    push_cast
    ring
  refine ⟨s / (s + 1), div_pos hspos (by linarith), ?_⟩
  have hs1 : ((s : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by linarith : (0 : ℝ) < s + 1).ne'
  rw [huv, hu'v]
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff hs1]
  ring

/-- A point of the geodesic ray from `z` has frame value on the ray of the endpoint. -/
theorem discChart_smul_of_mem_geodSeg {z w w' : UpperHalfPlane}
    (hw : w' ∈ geodSeg z w) (hne : w' ≠ z) :
    ∃ t : ℝ, 0 < t ∧ discChart z w' = (t : ℂ) * discChart z w := by
  have hbet : dist z w' + dist w' w = dist z w := hw
  rw [dist_eq_hDD z z w', dist_eq_hDD z w' w, dist_eq_hDD z z w,
    discChart_self] at hbet
  have h := norm_sub_of_between (norm_discChart_lt_one z w)
    (norm_discChart_lt_one z w') hbet
  exact exists_smul_of_norm_sub h (discChart_ne_zero hne)

/-! ## `SL(2, ℝ)`-equivariance of the frame -/

/-- Coordinates of the Möbius action of `SL(2, ℝ)` on the upper half plane. -/
theorem coe_smul (g : SL(2, ℝ)) (w : UpperHalfPlane) :
    ((g • w : UpperHalfPlane) : ℂ) =
      (((g 0 0 : ℝ) : ℂ) * (w : ℂ) + ((g 0 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (w : ℂ) + ((g 1 1 : ℝ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num

/-- Determinant unfolding for `SL(2, ℝ)`. -/
theorem det_entries (g : SL(2, ℝ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

/-- The Möbius denominator does not vanish off the real axis. -/
theorem denom_ne_zero (g : SL(2, ℝ)) {ξ : ℂ} (hξ : ξ.im ≠ 0) :
    ((g 1 0 : ℝ) : ℂ) * ξ + ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.zero_im] at him
  have hc : g 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact h'
    · exact absurd h' hξ
  rw [hc] at h
  simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_eq_zero] at h
  have hdet := det_entries g
  rw [hc, h] at hdet
  simp at hdet

/-- Difference of two Möbius images: the determinant cross identity. -/
theorem moebius_sub (A B C D u v : ℂ) (hu : C * u + D ≠ 0) (hv : C * v + D ≠ 0) :
    (A * u + B) / (C * u + D) - (A * v + B) / (C * v + D)
      = (A * D - B * C) * (u - v) / ((C * u + D) * (C * v + D)) := by
  rw [div_sub_div _ _ hu hv]
  congr 1
  ring

/-- Conjugation intertwines a real-coefficient Möbius map with itself. -/
theorem conj_moebius (A B C D : ℝ) (ξ : ℂ) :
    (starRingEnd ℂ) (((A : ℂ) * ξ + (B : ℂ)) / ((C : ℂ) * ξ + (D : ℂ)))
      = ((A : ℂ) * (starRingEnd ℂ) ξ + (B : ℂ)) /
        ((C : ℂ) * (starRingEnd ℂ) ξ + (D : ℂ)) := by
  simp [map_div₀, map_add, map_mul, Complex.conj_ofReal]

/-- The full frame transport under a determinant-one Möbius map, at the level of `ℂ`. -/
theorem frame_moebius (A B C D u z zb : ℂ) (hdet : A * D - B * C = 1)
    (hCu : C * u + D ≠ 0) (hCz : C * z + D ≠ 0) (hCzb : C * zb + D ≠ 0) :
    ((A * u + B) / (C * u + D) - (A * z + B) / (C * z + D)) /
      ((A * u + B) / (C * u + D) - (A * zb + B) / (C * zb + D))
      = ((C * zb + D) / (C * z + D)) * ((u - z) / (u - zb)) := by
  rw [moebius_sub A B C D u z hCu hCz, moebius_sub A B C D u zb hCu hCzb, hdet,
    one_mul, one_mul, div_div_div_comm, mul_div_mul_left _ _ hCu, div_div_eq_mul_div]
  ring

/-- The frame at a translated base point is a unimodular multiple of the frame. -/
theorem discChart_smul (g : SL(2, ℝ)) (z w : UpperHalfPlane) :
    discChart (g • z) (g • w)
      = ((((g 1 0 : ℝ) : ℂ) * (starRingEnd ℂ) (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
          (((g 1 0 : ℝ) : ℂ) * (z : ℂ) + ((g 1 1 : ℝ) : ℂ))) * discChart z w := by
  have hzim : ((z : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact z.im_pos.ne'
  have hwim : ((w : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact w.im_pos.ne'
  have hzbim : (((starRingEnd ℂ) (z : ℂ))).im ≠ 0 := by
    rw [Complex.conj_im, UpperHalfPlane.coe_im]
    simpa using z.im_pos.ne'
  have hCz := denom_ne_zero g hzim
  have hCw := denom_ne_zero g hwim
  have hCzb := denom_ne_zero g hzbim
  have hdet : ((g 0 0 : ℝ) : ℂ) * ((g 1 1 : ℝ) : ℂ)
      - ((g 0 1 : ℝ) : ℂ) * ((g 1 0 : ℝ) : ℂ) = 1 := by
    exact_mod_cast det_entries g
  rw [discChart_eq, discChart_eq, coe_smul g z, coe_smul g w,
    conj_moebius]
  exact frame_moebius _ _ _ _ _ _ _ hdet hCw hCz hCzb

/-! ## Additivity of absolute arguments in the closed upper half plane -/

/-- Absolute arguments add under multiplication when the two factors and their product all
lie in the closed upper half plane and the factors are not both negative reals. -/
theorem abs_arg_mul {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (h1 : 0 ≤ α.im) (h2 : 0 ≤ β.im) (h3 : 0 ≤ (α * β).im)
    (h4 : ¬(Complex.arg α = Real.pi ∧ Complex.arg β = Real.pi)) :
    |Complex.arg (α * β)| = |Complex.arg α| + |Complex.arg β| := by
  have ha1 : 0 ≤ Complex.arg α := Complex.arg_nonneg_iff.mpr h1
  have ha2 : 0 ≤ Complex.arg β := Complex.arg_nonneg_iff.mpr h2
  have hp1 : Complex.arg α ≤ Real.pi := Complex.arg_le_pi α
  have hp2 : Complex.arg β ≤ Real.pi := Complex.arg_le_pi β
  have hprod0 : 0 ≤ Complex.arg (α * β) := Complex.arg_nonneg_iff.mpr h3
  have hprodpi : Complex.arg (α * β) ≤ Real.pi := Complex.arg_le_pi _
  have hpi := Real.pi_pos
  have hs : Complex.arg α + Complex.arg β ≤ Real.pi := by
    by_contra hgt
    rw [not_le] at hgt
    have hlt : Complex.arg α + Complex.arg β < 2 * Real.pi := by
      rcases lt_or_eq_of_le hp1 with h | h
      · linarith
      · rcases lt_or_eq_of_le hp2 with h' | h'
        · linarith
        · exact absurd ⟨h, h'⟩ h4
    have hcoe := Complex.arg_mul_coe_angle hα hβ
    rw [← Real.Angle.coe_add] at hcoe
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hcoe
    have hlow : -(2 * Real.pi) < 2 * Real.pi * (k : ℝ) := by rw [← hk]; linarith
    have hhigh : 2 * Real.pi * (k : ℝ) < 0 := by rw [← hk]; linarith
    have hk1 : (-1 : ℝ) < (k : ℝ) := by nlinarith
    have hk2 : ((k : ℝ)) < 0 := by nlinarith
    have hk1' : (-1 : ℤ) < k := by exact_mod_cast hk1
    have hk2' : k < 0 := by exact_mod_cast hk2
    omega
  have harg : Complex.arg (α * β) = Complex.arg α + Complex.arg β :=
    (Complex.arg_mul_eq_add_arg_iff hα hβ).mpr (Set.mem_Ioc.mpr ⟨by linarith, hs⟩)
  rw [harg, abs_of_nonneg (by linarith), abs_of_nonneg ha1, abs_of_nonneg ha2]

/-! ## The frame along the imaginary axis -/

/-- The frame value at `p + qi` of the point `i·t` of the imaginary axis. -/
noncomputable def vf (p q t : ℝ) : ℂ :=
  (Complex.I * (t : ℂ) - ((p : ℂ) + (q : ℂ) * Complex.I)) /
    (Complex.I * (t : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I))

/-- The denominator of the frame value never vanishes on the imaginary axis: the point
`i·t` with `t > 0` cannot equal the reflected center `p - qi`, which lies in the lower half
plane when `q > 0`. -/
theorem vf_den_ne_zero {q : ℝ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) (p : ℝ) :
    Complex.I * (t : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_im, one_mul, mul_zero, add_zero, zero_add,
    mul_one, zero_sub, sub_neg_eq_add] at him
  linarith

/-- The frame value vanishes only at the basepoint: away from `p + qi` the numerator is
nonzero, and the denominator never is. -/
theorem vf_ne_zero {p q t : ℝ} (hq : 0 < q) (ht : 0 < t)
    (hn : Complex.I * (t : ℂ) ≠ (p : ℂ) + (q : ℂ) * Complex.I) : vf p q t ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr hn) (vf_den_ne_zero hq ht p)

/-- The ratio of two frame values along the axis, as a single fraction. -/
theorem vf_ratio (p q s t : ℝ) :
    vf p q s / vf p q t
      = ((Complex.I * (s : ℂ) - ((p : ℂ) + (q : ℂ) * Complex.I)) *
          (Complex.I * (t : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I))) /
        ((Complex.I * (s : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I)) *
          (Complex.I * (t : ℂ) - ((p : ℂ) + (q : ℂ) * Complex.I))) := by
  unfold vf
  rw [div_div_div_comm, div_div_eq_mul_div, div_mul_eq_mul_div, div_div]
  ring

/-- Sign structure of the ratio: the imaginary part is a positive multiple of `p·(t − s)`. -/
theorem vf_ratio_im (p q s t : ℝ) (hq : 0 < q) (hs : 0 < s) (ht : 0 < t)
    (hnt : Complex.I * (t : ℂ) ≠ (p : ℂ) + (q : ℂ) * Complex.I) :
    ∃ K : ℝ, 0 < K ∧ (vf p q s / vf p q t).im = K * (p * (t - s)) := by
  have hDs := vf_den_ne_zero hq hs p
  have hNt := sub_ne_zero.mpr hnt
  have hDne : (Complex.I * (s : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I)) *
      (Complex.I * (t : ℂ) - ((p : ℂ) + (q : ℂ) * Complex.I)) ≠ 0 := mul_ne_zero hDs hNt
  have hnsq : 0 < Complex.normSq ((Complex.I * (s : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I)) *
      (Complex.I * (t : ℂ) - ((p : ℂ) + (q : ℂ) * Complex.I))) := Complex.normSq_pos.mpr hDne
  refine ⟨2 * q * (s + t) / Complex.normSq ((Complex.I * (s : ℂ) - ((p : ℂ) -
      (q : ℂ) * Complex.I)) * (Complex.I * (t : ℂ) - ((p : ℂ) + (q : ℂ) * Complex.I))),
    div_pos (by positivity) hnsq, ?_⟩
  rw [vf_ratio p q s t, Complex.div_im, div_sub_div_same, div_mul_eq_mul_div]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- With the base point on the axis, the frame values are real. -/
theorem vf_zero_re (q t : ℝ) :
    vf 0 q t = (((t - q) / (t + q) : ℝ) : ℂ) := by
  unfold vf
  have h1 : Complex.I * (t : ℂ) - (((0 : ℝ) : ℂ) + (q : ℂ) * Complex.I)
      = Complex.I * (((t - q : ℝ)) : ℂ) := by push_cast; ring
  have h2 : Complex.I * (t : ℂ) - (((0 : ℝ) : ℂ) - (q : ℂ) * Complex.I)
      = Complex.I * (((t + q : ℝ)) : ℂ) := by push_cast; ring
  rw [h1, h2, mul_div_mul_left _ _ Complex.I_ne_zero]
  push_cast
  ring

/-- Monotonicity of the axis frame with a base point on the axis. -/
theorem G_mono {q x y : ℝ} (hq : 0 < q) (hx : 0 < x) (hxy : x ≤ y) :
    (x - q) / (x + q) ≤ (y - q) / (y + q) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Angle additivity along the imaginary axis, ordered form: for a base point anywhere and
axis points `i·a`, `i·c`, `i·b` with `a ≤ c ≤ b`, the two partial angles at the base point
sum to the full angle. -/
theorem vertical_core {p q a c b : ℝ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hac : a ≤ c) (hcb : c ≤ b)
    (hna : Complex.I * (a : ℂ) ≠ (p : ℂ) + (q : ℂ) * Complex.I)
    (hnb : Complex.I * (b : ℂ) ≠ (p : ℂ) + (q : ℂ) * Complex.I)
    (hnc : Complex.I * (c : ℂ) ≠ (p : ℂ) + (q : ℂ) * Complex.I) :
    |Complex.arg (vf p q c / vf p q a)|
      + |Complex.arg (vf p q b / vf p q c)|
      = |Complex.arg (vf p q b / vf p q a)| := by
  have hfa := vf_ne_zero hq ha hna
  have hfb := vf_ne_zero hq hb hnb
  have hfc := vf_ne_zero hq hc hnc
  rcases le_or_gt p 0 with hp | hp
  · -- base point on or left of the axis: the three ratios lie in the closed upper half plane
    obtain ⟨K₁, hK₁, him₁⟩ := vf_ratio_im p q c a hq hc ha hna
    obtain ⟨K₂, hK₂, him₂⟩ := vf_ratio_im p q b c hq hb hc hnc
    obtain ⟨K₃, hK₃, him₃⟩ := vf_ratio_im p q b a hq hb ha hna
    have hprod : vf p q c / vf p q a * (vf p q b / vf p q c)
        = vf p q b / vf p q a := by
      rw [mul_comm]
      exact div_mul_div_cancel₀ hfc
    have h1 : 0 ≤ (vf p q c / vf p q a).im := by
      rw [him₁]
      have hnn : 0 ≤ p * (a - c) := by nlinarith
      positivity
    have h2 : 0 ≤ (vf p q b / vf p q c).im := by
      rw [him₂]
      have hnn : 0 ≤ p * (c - b) := by nlinarith
      positivity
    have h3 : 0 ≤ (vf p q c / vf p q a * (vf p q b / vf p q c)).im := by
      rw [hprod, him₃]
      have hnn : 0 ≤ p * (a - b) := by nlinarith
      positivity
    have h4 : ¬(Complex.arg (vf p q c / vf p q a) = Real.pi ∧
        Complex.arg (vf p q b / vf p q c) = Real.pi) := by
      rintro ⟨hπ₁, hπ₂⟩
      obtain ⟨-, him₁'⟩ := Complex.arg_eq_pi_iff.mp hπ₁
      rw [him₁] at him₁'
      have hpac : p * (a - c) = 0 := by
        rcases mul_eq_zero.mp him₁' with h' | h'
        · exact absurd h' hK₁.ne'
        · exact h'
      rcases mul_eq_zero.mp hpac with hpz | hacz
      · -- the base point is on the axis: the ratios are real, sign analysis
        subst hpz
        rw [vf_zero_re q c, vf_zero_re q a, ← Complex.ofReal_div] at hπ₁
        rw [vf_zero_re q b, vf_zero_re q c, ← Complex.ofReal_div] at hπ₂
        have hr₁ : (c - q) / (c + q) / ((a - q) / (a + q)) < 0 := by
          rcases lt_or_ge ((c - q) / (c + q) / ((a - q) / (a + q))) 0 with hge | hge
          · exact hge
          · rw [Complex.arg_ofReal_of_nonneg hge] at hπ₁
            exact absurd hπ₁.symm Real.pi_ne_zero
        have hr₂ : (b - q) / (b + q) / ((c - q) / (c + q)) < 0 := by
          rcases lt_or_ge ((b - q) / (b + q) / ((c - q) / (c + q))) 0 with hge | hge
          · exact hge
          · rw [Complex.arg_ofReal_of_nonneg hge] at hπ₂
            exact absurd hπ₂.symm Real.pi_ne_zero
        have hGa := G_mono hq ha hac
        have hGb := G_mono hq hc hcb
        rcases div_neg_iff.mp hr₁ with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
          rcases div_neg_iff.mp hr₂ with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;> linarith
      · -- degenerate ray: the first ratio is 1
        have hca : a = c := by
          have := sub_eq_zero.mp hacz
          linarith
        rw [hca, div_self hfc, Complex.arg_one] at hπ₁
        exact Real.pi_ne_zero hπ₁.symm
    have hcore := abs_arg_mul (div_ne_zero hfc hfa) (div_ne_zero hfb hfc) h1 h2 h3 h4
    rw [hprod] at hcore
    linarith
  · -- base point right of the axis: run the argument on the inverted ratios
    obtain ⟨K₁, hK₁, him₁⟩ := vf_ratio_im p q a c hq ha hc hnc
    obtain ⟨K₂, hK₂, him₂⟩ := vf_ratio_im p q c b hq hc hb hnb
    obtain ⟨K₃, hK₃, him₃⟩ := vf_ratio_im p q a b hq ha hb hnb
    have hprod : vf p q a / vf p q c * (vf p q c / vf p q b)
        = vf p q a / vf p q b := div_mul_div_cancel₀ hfc
    have h1 : 0 ≤ (vf p q a / vf p q c).im := by
      rw [him₁]
      have hnn : 0 ≤ p * (c - a) := mul_nonneg hp.le (by linarith)
      positivity
    have h2 : 0 ≤ (vf p q c / vf p q b).im := by
      rw [him₂]
      have hnn : 0 ≤ p * (b - c) := mul_nonneg hp.le (by linarith)
      positivity
    have h3 : 0 ≤ (vf p q a / vf p q c * (vf p q c / vf p q b)).im := by
      rw [hprod, him₃]
      have hnn : 0 ≤ p * (b - a) := mul_nonneg hp.le (by linarith)
      positivity
    have h4 : ¬(Complex.arg (vf p q a / vf p q c) = Real.pi ∧
        Complex.arg (vf p q c / vf p q b) = Real.pi) := by
      rintro ⟨hπ₁, -⟩
      obtain ⟨-, him₁'⟩ := Complex.arg_eq_pi_iff.mp hπ₁
      rw [him₁] at him₁'
      have hpca : p * (c - a) = 0 := by
        rcases mul_eq_zero.mp him₁' with h' | h'
        · exact absurd h' hK₁.ne'
        · exact h'
      rcases mul_eq_zero.mp hpca with hpz | hacz
      · exact absurd hpz hp.ne'
      · have hca : a = c := by
          have := sub_eq_zero.mp hacz
          linarith
        rw [hca, div_self hfc, Complex.arg_one] at hπ₁
        exact Real.pi_ne_zero hπ₁.symm
    have hcore := abs_arg_mul (div_ne_zero hfa hfc) (div_ne_zero hfc hfb) h1 h2 h3 h4
    rw [hprod] at hcore
    have e1 : |Complex.arg (vf p q a / vf p q b)|
        = |Complex.arg (vf p q b / vf p q a)| := by
      rw [show vf p q a / vf p q b = (vf p q b / vf p q a)⁻¹ from
        (inv_div _ _).symm, Complex.abs_arg_inv]
    have e2 : |Complex.arg (vf p q a / vf p q c)|
        = |Complex.arg (vf p q c / vf p q a)| := by
      rw [show vf p q a / vf p q c = (vf p q c / vf p q a)⁻¹ from
        (inv_div _ _).symm, Complex.abs_arg_inv]
    have e3 : |Complex.arg (vf p q c / vf p q b)|
        = |Complex.arg (vf p q b / vf p q c)| := by
      rw [show vf p q c / vf p q b = (vf p q b / vf p q c)⁻¹ from
        (inv_div _ _).symm, Complex.abs_arg_inv]
    linarith

/-! ## Vertical projection: segments between axis points stay on the axis -/

/-- The vertical distance primitive on heights, ordered form. -/
theorem log_dist_aux {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (hle : y₁ ≤ y₂) :
    2 * Real.arsinh ((y₂ - y₁) / (2 * Real.sqrt (y₁ * y₂)))
      = Real.log y₂ - Real.log y₁ := by
  have h₂ : 0 < y₂ := lt_of_lt_of_le h₁ hle
  have hs₁ : 0 < Real.sqrt y₁ := Real.sqrt_pos.mpr h₁
  have hs₂ : 0 < Real.sqrt y₂ := Real.sqrt_pos.mpr h₂
  have hss : Real.sqrt y₁ * Real.sqrt y₁ = y₁ := Real.mul_self_sqrt h₁.le
  have hss' : Real.sqrt y₂ * Real.sqrt y₂ = y₂ := Real.mul_self_sqrt h₂.le
  have he : Real.exp ((Real.log y₂ - Real.log y₁) / 2)
      = Real.sqrt y₂ / Real.sqrt y₁ := by
    rw [show (Real.log y₂ - Real.log y₁) / 2 = Real.log y₂ / 2 - Real.log y₁ / 2 by ring,
      ← Real.log_sqrt h₂.le, ← Real.log_sqrt h₁.le, Real.exp_sub, Real.exp_log hs₂,
      Real.exp_log hs₁]
  have hkey : (y₂ - y₁) / (2 * Real.sqrt (y₁ * y₂))
      = Real.sinh ((Real.log y₂ - Real.log y₁) / 2) := by
    rw [Real.sinh_eq, he, Real.exp_neg, he, inv_div, Real.sqrt_mul h₁.le,
      div_sub_div _ _ hs₁.ne' hs₂.ne', hss, hss']
    ring
  rw [hkey, Real.arsinh_sinh]
  ring

/-- The vertical distance primitive on heights. -/
theorem log_dist (y₁ y₂ : ℝ) (h₁ : 0 < y₁) (h₂ : 0 < y₂) :
    2 * Real.arsinh (|y₁ - y₂| / (2 * Real.sqrt (y₁ * y₂)))
      = |Real.log y₁ - Real.log y₂| := by
  rcases le_total y₁ y₂ with hle | hle
  · rw [abs_of_nonpos (by linarith), neg_sub, log_dist_aux h₁ hle,
      abs_of_nonpos (sub_nonpos.mpr ((Real.log_le_log_iff h₁ h₂).mpr hle)), neg_sub]
  · have haux := log_dist_aux h₂ hle
    rw [mul_comm y₂ y₁] at haux
    rw [abs_of_nonneg (by linarith), haux,
      abs_of_nonneg (sub_nonneg.mpr ((Real.log_le_log_iff h₂ h₁).mpr hle))]

/-- The hyperbolic distance dominates the vertical logarithmic displacement. -/
theorem log_le_dist (τ σ : UpperHalfPlane) :
    |Real.log τ.im - Real.log σ.im| ≤ dist τ σ := by
  rw [← log_dist τ.im σ.im τ.im_pos σ.im_pos, UpperHalfPlane.dist_eq]
  have h1 : |τ.im - σ.im| ≤ dist (τ : ℂ) (σ : ℂ) := by
    rw [Complex.dist_eq]
    have h := Complex.abs_im_le_norm ((τ : ℂ) - (σ : ℂ))
    rwa [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
  have hd : (0 : ℝ) < 2 * Real.sqrt (τ.im * σ.im) := by positivity
  have h2 := Real.arsinh_le_arsinh.mpr
    (show |τ.im - σ.im| / (2 * Real.sqrt (τ.im * σ.im))
      ≤ dist (τ : ℂ) (σ : ℂ) / (2 * Real.sqrt (τ.im * σ.im)) by gcongr)
  linarith

/-- Equality in the vertical projection forces equal real parts. -/
theorem re_eq_of_dist_eq_log {τ σ : UpperHalfPlane}
    (h : dist τ σ = |Real.log τ.im - Real.log σ.im|) : τ.re = σ.re := by
  by_contra hne
  have h0 : τ.re - σ.re ≠ 0 := sub_ne_zero.mpr hne
  have hlt : |τ.im - σ.im| < dist (τ : ℂ) (σ : ℂ) := by
    rw [Complex.dist_eq]
    have hsq : |τ.im - σ.im| ^ 2 < ‖(τ : ℂ) - (σ : ℂ)‖ ^ 2 := by
      rw [sq_abs, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      nlinarith [mul_self_pos.mpr h0]
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq
  have hd : (0 : ℝ) < 2 * Real.sqrt (τ.im * σ.im) := by positivity
  have h2 := Real.arsinh_lt_arsinh.mpr
    (show |τ.im - σ.im| / (2 * Real.sqrt (τ.im * σ.im))
      < dist (τ : ℂ) (σ : ℂ) / (2 * Real.sqrt (τ.im * σ.im)) by gcongr)
  have h3 : |Real.log τ.im - Real.log σ.im| < dist τ σ := by
    rw [← log_dist τ.im σ.im τ.im_pos σ.im_pos, UpperHalfPlane.dist_eq]
    linarith
  linarith [h, h3]

/-- A geodesic segment with endpoints on a common vertical line stays on the line, with
height between the endpoint heights. -/
theorem mem_geodSeg_vertical {a b x : UpperHalfPlane} (hre : a.re = b.re)
    (hx : x ∈ geodSeg a b) :
    x.re = a.re ∧ min a.im b.im ≤ x.im ∧ x.im ≤ max a.im b.im := by
  have hbet : dist a x + dist x b = dist a b := hx
  have hab : dist a b = |Real.log a.im - Real.log b.im| := by
    rw [UpperHalfPlane.dist_of_re_eq hre, Real.dist_eq]
  have h1 := log_le_dist a x
  have h2 := log_le_dist x b
  have htri : |Real.log a.im - Real.log b.im|
      ≤ |Real.log a.im - Real.log x.im| + |Real.log x.im - Real.log b.im| :=
    abs_sub_le _ _ _
  have he1 : dist a x = |Real.log a.im - Real.log x.im| := by linarith
  have hxre : x.re = a.re := (re_eq_of_dist_eq_log he1).symm
  have hsum : |Real.log a.im - Real.log x.im| + |Real.log x.im - Real.log b.im|
      = |Real.log a.im - Real.log b.im| := by linarith
  have hlow : min (Real.log a.im) (Real.log b.im) ≤ Real.log x.im := by
    by_contra hlt
    rw [not_le, lt_min_iff] at hlt
    obtain ⟨hla, hlb⟩ := hlt
    rw [abs_of_pos (by linarith), abs_of_neg (by linarith)] at hsum
    rcases abs_cases (Real.log a.im - Real.log b.im) with ⟨heq, -⟩ | ⟨heq, -⟩ <;>
      rw [heq] at hsum <;> linarith
  have hhigh : Real.log x.im ≤ max (Real.log a.im) (Real.log b.im) := by
    by_contra hlt
    rw [not_le, max_lt_iff] at hlt
    obtain ⟨hla, hlb⟩ := hlt
    rw [abs_of_neg (by linarith), abs_of_pos (by linarith)] at hsum
    rcases abs_cases (Real.log a.im - Real.log b.im) with ⟨heq, -⟩ | ⟨heq, -⟩ <;>
      rw [heq] at hsum <;> linarith
  refine ⟨hxre, ?_, ?_⟩
  · rcases le_total a.im b.im with him | him
    · rw [min_eq_left him]
      have hll : Real.log a.im ≤ Real.log b.im :=
        (Real.log_le_log_iff a.im_pos b.im_pos).mpr him
      rw [min_eq_left hll] at hlow
      exact (Real.log_le_log_iff a.im_pos x.im_pos).mp hlow
    · rw [min_eq_right him]
      have hll : Real.log b.im ≤ Real.log a.im :=
        (Real.log_le_log_iff b.im_pos a.im_pos).mpr him
      rw [min_eq_right hll] at hlow
      exact (Real.log_le_log_iff b.im_pos x.im_pos).mp hlow
  · rcases le_total a.im b.im with him | him
    · rw [max_eq_right him]
      have hll : Real.log a.im ≤ Real.log b.im :=
        (Real.log_le_log_iff a.im_pos b.im_pos).mpr him
      rw [max_eq_right hll] at hhigh
      exact (Real.log_le_log_iff x.im_pos b.im_pos).mp hhigh
    · rw [max_eq_left him]
      have hll : Real.log b.im ≤ Real.log a.im :=
        (Real.log_le_log_iff b.im_pos a.im_pos).mpr him
      rw [max_eq_left hll] at hhigh
      exact (Real.log_le_log_iff x.im_pos a.im_pos).mp hhigh

/-! ## Moving two points onto the imaginary axis -/

/-- Both endpoints lie on the circle about the geodesic center. -/
theorem norm_sub_geodCenter {a b : UpperHalfPlane} (h : a.re ≠ b.re) :
    ‖(b : ℂ) - (geodCenter a b : ℂ)‖ = geodRadius a b := by
  rw [geodRadius]
  have hd : a.re - b.re ≠ 0 := sub_ne_zero.mpr h
  have hns : Complex.normSq ((b : ℂ) - (geodCenter a b : ℂ))
      = Complex.normSq ((a : ℂ) - (geodCenter a b : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero, geodCenter]
    field_simp
    ring
  have hsq : ‖(b : ℂ) - (geodCenter a b : ℂ)‖ ^ 2
      = ‖(a : ℂ) - (geodCenter a b : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    exact hns
  calc ‖(b : ℂ) - (geodCenter a b : ℂ)‖
      = Real.sqrt (‖(b : ℂ) - (geodCenter a b : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖(a : ℂ) - (geodCenter a b : ℂ)‖ ^ 2) := by rw [hsq]
    _ = ‖(a : ℂ) - (geodCenter a b : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

/-- The horizontal translation as an element of `SL(2, ℝ)`. -/
noncomputable def transSL (r : ℝ) : SL(2, ℝ) :=
  ⟨!![1, -r; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

/-- The horizontal translation shifts the real part by `-r`. -/
theorem transSL_re (r : ℝ) (w : UpperHalfPlane) :
    ((transSL r) • w).re = w.re - r := by
  have hcoe := coe_smul (transSL r) w
  have h00 : (transSL r) 0 0 = 1 := by simp [transSL]
  have h01 : (transSL r) 0 1 = -r := by simp [transSL]
  have h10 : (transSL r) 1 0 = 0 := by simp [transSL]
  have h11 : (transSL r) 1 1 = 1 := by simp [transSL]
  rw [h00, h01, h10, h11] at hcoe
  have hval : ((transSL r • w : UpperHalfPlane) : ℂ) = (w : ℂ) - (r : ℂ) := by
    rw [hcoe]
    push_cast
    rw [one_mul, zero_mul, zero_add, div_one]
    ring
  rw [← UpperHalfPlane.coe_re, hval, Complex.sub_re, Complex.ofReal_re,
    UpperHalfPlane.coe_re]

/-- The semicircle-to-axis element of `SL(2, ℝ)`: sends the circle of center `c ∈ ℝ` and
radius `R` to the imaginary axis. -/
noncomputable def circSL (c R : ℝ) (hR : 0 < R) : SL(2, ℝ) :=
  ⟨!![1 / Real.sqrt (2 * R), -(c - R) / Real.sqrt (2 * R);
      -(1 / Real.sqrt (2 * R)), (c + R) / Real.sqrt (2 * R)], by
    have hs : Real.sqrt (2 * R) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    have hss : Real.sqrt (2 * R) * Real.sqrt (2 * R) = 2 * R :=
      Real.mul_self_sqrt (by linarith)
    rw [Matrix.det_fin_two_of]
    field_simp
    linarith [hss]⟩

/-- The semicircle-to-axis element carries the circle of center `c` and radius `R` onto the
imaginary axis: a point at distance exactly `R` from `c` is sent to real part `0`. -/
theorem circSL_re {c R : ℝ} (hR : 0 < R) (w : UpperHalfPlane)
    (hw : ‖(w : ℂ) - (c : ℂ)‖ = R) : ((circSL c R hR) • w).re = 0 := by
  have hs : Real.sqrt (2 * R) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsC : ((Real.sqrt (2 * R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcoe := coe_smul (circSL c R hR) w
  have h00 : (circSL c R hR) 0 0 = 1 / Real.sqrt (2 * R) := by simp [circSL]
  have h01 : (circSL c R hR) 0 1 = -(c - R) / Real.sqrt (2 * R) := by
    simp [circSL]
  have h10 : (circSL c R hR) 1 0 = -(1 / Real.sqrt (2 * R)) := by simp [circSL]
  have h11 : (circSL c R hR) 1 1 = (c + R) / Real.sqrt (2 * R) := by
    simp [circSL]
  rw [h00, h01, h10, h11] at hcoe
  have hval : ((circSL c R hR • w : UpperHalfPlane) : ℂ)
      = ((w : ℂ) - (c : ℂ) + (R : ℂ)) / (-(w : ℂ) + (c : ℂ) + (R : ℂ)) := by
    rw [hcoe]
    push_cast
    rw [show ((1 : ℂ) / Real.sqrt (2 * R)) * (w : ℂ) + -((c : ℂ) - (R : ℂ)) /
        Real.sqrt (2 * R) = (((w : ℂ) - (c : ℂ) + (R : ℂ)) * (1 / Real.sqrt (2 * R)))
        from by field_simp; ring]
    rw [show -((1 : ℂ) / Real.sqrt (2 * R)) * (w : ℂ) + ((c : ℂ) + (R : ℂ)) /
        Real.sqrt (2 * R) = ((-(w : ℂ) + (c : ℂ) + (R : ℂ)) * (1 / Real.sqrt (2 * R)))
        from by field_simp; ring]
    rw [mul_comm ((w : ℂ) - (c : ℂ) + (R : ℂ)) _,
      mul_comm (-(w : ℂ) + (c : ℂ) + (R : ℂ)) _,
      mul_div_mul_left _ _ (one_div_ne_zero hsC)]
  have hns : Complex.normSq ((w : ℂ) - (c : ℂ)) = R ^ 2 := by
    rw [← Complex.sq_norm, hw]
  rw [← UpperHalfPlane.coe_re, hval, Complex.div_re, ← add_div]
  have hnum : ((w : ℂ) - (c : ℂ) + (R : ℂ)).re * (-(w : ℂ) + (c : ℂ) + (R : ℂ)).re
      + ((w : ℂ) - (c : ℂ) + (R : ℂ)).im * (-(w : ℂ) + (c : ℂ) + (R : ℂ)).im = 0 := by
    rw [Complex.normSq_apply] at hns
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero] at hns
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero, add_zero]
    nlinarith [hns]
  rw [hnum, zero_div]

/-- Some element of `SL(2, ℝ)` carries two given points onto the imaginary axis. -/
theorem exists_verticalize (w₁ w₂ : UpperHalfPlane) :
    ∃ g : SL(2, ℝ), (g • w₁).re = 0 ∧ (g • w₂).re = 0 := by
  rcases eq_or_ne w₁.re w₂.re with hre | hre
  · refine ⟨transSL w₁.re, ?_, ?_⟩
    · rw [transSL_re, sub_self]
    · rw [transSL_re, ← hre, sub_self]
  · have hb := norm_sub_geodCenter hre
    have ha : ‖(w₁ : ℂ) - (geodCenter w₁ w₂ : ℂ)‖ = geodRadius w₁ w₂ := rfl
    exact ⟨circSL _ _ (geodRadius_pos w₁ w₂),
      circSL_re (geodRadius_pos w₁ w₂) w₁ ha,
      circSL_re (geodRadius_pos w₁ w₂) w₂ hb⟩

/-! ## Angle additivity -/

/-- Additivity for a segment carried by the imaginary axis. -/
theorem sectorAngle_add_vertical {z W₁ W₂ X : UpperHalfPlane}
    (h1re : W₁.re = 0) (h2re : W₂.re = 0) (hX : X ∈ geodSeg W₁ W₂)
    (hXz : X ≠ z) (h1z : W₁ ≠ z) (h2z : W₂ ≠ z) :
    sectorAngle z W₁ X + sectorAngle z X W₂ = sectorAngle z W₁ W₂ := by
  obtain ⟨hXre, hmin, hmax⟩ := mem_geodSeg_vertical (h1re.trans h2re.symm) hX
  rw [h1re] at hXre
  have hW₁ : (W₁ : ℂ) = Complex.I * (W₁.im : ℂ) := by
    apply Complex.ext <;> simp [h1re]
  have hW₂ : (W₂ : ℂ) = Complex.I * (W₂.im : ℂ) := by
    apply Complex.ext <;> simp [h2re]
  have hXc : (X : ℂ) = Complex.I * (X.im : ℂ) := by
    apply Complex.ext <;> simp [hXre]
  have hzc := coe_eq_re_add_im z
  have hd1 : discChart z W₁ = vf z.re z.im W₁.im := by
    rw [discChart_eq, conj_coe, hW₁, hzc]
    rfl
  have hd2 : discChart z X = vf z.re z.im X.im := by
    rw [discChart_eq, conj_coe, hXc, hzc]
    rfl
  have hd3 : discChart z W₂ = vf z.re z.im W₂.im := by
    rw [discChart_eq, conj_coe, hW₂, hzc]
    rfl
  have hne1 : Complex.I * (W₁.im : ℂ) ≠ (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    rw [← hW₁, ← hzc]
    exact fun h => h1z (UpperHalfPlane.ext h)
  have hne2 : Complex.I * (X.im : ℂ) ≠ (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    rw [← hXc, ← hzc]
    exact fun h => hXz (UpperHalfPlane.ext h)
  have hne3 : Complex.I * (W₂.im : ℂ) ≠ (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    rw [← hW₂, ← hzc]
    exact fun h => h2z (UpperHalfPlane.ext h)
  unfold sectorAngle
  rw [hd1, hd2, hd3]
  rcases le_total W₁.im W₂.im with him | him
  · rw [min_eq_left him] at hmin
    rw [max_eq_right him] at hmax
    exact vertical_core z.im_pos W₁.im_pos W₂.im_pos X.im_pos hmin hmax hne1 hne3 hne2
  · rw [min_eq_right him] at hmin
    rw [max_eq_left him] at hmax
    have hcore := vertical_core z.im_pos W₂.im_pos W₁.im_pos X.im_pos hmin hmax
      hne3 hne1 hne2
    have e1 : |Complex.arg (vf z.re z.im X.im / vf z.re z.im W₁.im)|
        = |Complex.arg (vf z.re z.im W₁.im / vf z.re z.im X.im)| := by
      rw [show vf z.re z.im X.im / vf z.re z.im W₁.im
          = (vf z.re z.im W₁.im / vf z.re z.im X.im)⁻¹ from (inv_div _ _).symm,
        Complex.abs_arg_inv]
    have e2 : |Complex.arg (vf z.re z.im W₂.im / vf z.re z.im X.im)|
        = |Complex.arg (vf z.re z.im X.im / vf z.re z.im W₂.im)| := by
      rw [show vf z.re z.im W₂.im / vf z.re z.im X.im
          = (vf z.re z.im X.im / vf z.re z.im W₂.im)⁻¹ from (inv_div _ _).symm,
        Complex.abs_arg_inv]
    have e3 : |Complex.arg (vf z.re z.im W₂.im / vf z.re z.im W₁.im)|
        = |Complex.arg (vf z.re z.im W₁.im / vf z.re z.im W₂.im)| := by
      rw [show vf z.re z.im W₂.im / vf z.re z.im W₁.im
          = (vf z.re z.im W₁.im / vf z.re z.im W₂.im)⁻¹ from (inv_div _ _).symm,
        Complex.abs_arg_inv]
    linarith

/-- Angles are invariant under the `SL(2, ℝ)`-action: a Möbius automorphism of the disc
fixing the origin is a rotation. -/
theorem sectorAngle_smul (g : SL(2, ℝ)) (z w₁ w₂ : UpperHalfPlane) :
    sectorAngle (g • z) (g • w₁) (g • w₂) = sectorAngle z w₁ w₂ := by
  have hzim : ((z : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact z.im_pos.ne'
  have hzbim : (((starRingEnd ℂ) (z : ℂ))).im ≠ 0 := by
    rw [Complex.conj_im, UpperHalfPlane.coe_im]
    simpa using z.im_pos.ne'
  have hη : ((((g 1 0 : ℝ) : ℂ) * (starRingEnd ℂ) (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (z : ℂ) + ((g 1 1 : ℝ) : ℂ))) ≠ 0 :=
    div_ne_zero (denom_ne_zero g hzbim) (denom_ne_zero g hzim)
  unfold sectorAngle
  rw [discChart_smul g z w₁, discChart_smul g z w₂, mul_div_mul_left _ _ hη]

/-- The angle depends only on the geodesic ray: replacing `w₁` by another point of the
segment from `z` through `w₁` does not change the angle. -/
theorem sectorAngle_congr_of_mem_geodSeg {z w₁ w₁' : UpperHalfPlane}
    (hw : w₁' ∈ geodSeg z w₁) (hne : w₁' ≠ z) (w₂ : UpperHalfPlane) :
    sectorAngle z w₁' w₂ = sectorAngle z w₁ w₂ := by
  obtain ⟨t, ht, hEq⟩ := discChart_smul_of_mem_geodSeg hw hne
  unfold sectorAngle
  rw [hEq]
  have harg : Complex.arg (discChart z w₂ / ((t : ℂ) * discChart z w₁))
      = Complex.arg (discChart z w₂ / discChart z w₁) := by
    rw [div_mul_eq_div_div_swap, div_eq_mul_inv (discChart z w₂ / discChart z w₁),
      ← Complex.ofReal_inv]
    exact Complex.arg_mul_real (inv_pos.mpr ht) _
  rw [harg]

/-- **Angle additivity**: a ray into the triangle spanned at `z` splits the sector angle. -/
theorem sectorAngle_add_of_mem_triangle {z w₁ w₂ w : UpperHalfPlane}
    (hw : w ∈ hyperbolicTriangle z w₁ w₂) (hwz : w ≠ z) (h1 : w₁ ≠ z) (h2 : w₂ ≠ z) :
    sectorAngle z w₁ w + sectorAngle z w w₂ = sectorAngle z w₁ w₂ := by
  obtain ⟨x, hxseg, hwseg⟩ := mem_geodCone.mp hw
  have hxz : x ≠ z := by
    rintro rfl
    rw [geodSeg_self] at hwseg
    exact hwz (Set.mem_singleton_iff.mp hwseg)
  have e2 : sectorAngle z w w₂ = sectorAngle z x w₂ :=
    sectorAngle_congr_of_mem_geodSeg hwseg hwz w₂
  have e1 : sectorAngle z w₁ w = sectorAngle z w₁ x := by
    rw [sectorAngle_comm z w₁ w, sectorAngle_comm z w₁ x]
    exact sectorAngle_congr_of_mem_geodSeg hwseg hwz w₁
  rw [e1, e2]
  rcases eq_or_ne w₁ w₂ with h12 | h12
  · subst h12
    rw [geodSeg_self] at hxseg
    have hxw : x = w₁ := Set.mem_singleton_iff.mp hxseg
    subst hxw
    rw [sectorAngle_self h1]
    norm_num
  · obtain ⟨g, hg1, hg2⟩ := exists_verticalize w₁ w₂
    rw [← sectorAngle_smul g z w₁ x, ← sectorAngle_smul g z x w₂,
      ← sectorAngle_smul g z w₁ w₂]
    have hseg' : g • x ∈ geodSeg (g • w₁) (g • w₂) := by
      rw [← smul_geodSeg]
      exact ⟨x, hxseg, rfl⟩
    exact sectorAngle_add_vertical hg1 hg2 hseg'
      (fun h => hxz (MulAction.injective g h))
      (fun h => h1 (MulAction.injective g h))
      (fun h => h2 (MulAction.injective g h))

/-- `θ` is the **apex angle** at `z` of the cone over the geodesic segment `s`: the sector
angle at `z` between the two ends of `s`. -/
def IsApexAngleAt (z : UpperHalfPlane) (s : Set UpperHalfPlane) (θ : ℝ) : Prop :=
  ∃ a b : UpperHalfPlane, a ≠ b ∧ s = geodSeg a b ∧ θ = sectorAngle z a b

end RiemannDynamics
