import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import RiemannDynamics.Hyperbolic.DiskModel.DiskMetric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Geodesic segments and angles on the upper half plane

The geodesic segment between two points of the upper half plane is the set of points through
which the triangle inequality is an equality; it is carried by a vertical line (equal real
parts) or by a semicircle centered on the real axis.

* `geodSeg` — the segment; `geodInterp` — its explicit constant-speed parametrization, by a
  log-linear height on vertical lines and by the arc-length coordinate `log (tan (θ/2))` on
  semicircles.
* `IsSegEndpoint` — extreme points of a segment; `GeodConvex` — geodesic convexity;
  `geodCone`, `hyperbolicTriangle` — geodesic cones and triangles.
* `geodSeg_subset_setOf_dist_le` — half-spaces of a distance comparison are geodesically
  convex; `exists_geodSeg_eq_inter_bisector` — a convex compact set meets a perpendicular
  bisector in a geodesic segment.
* `discChart` — the disc-model frame at a point: the Möbius normalization moving the point
  to `i` followed by the Cayley map to the unit disc; geodesic rays from the point become
  Euclidean diameters through the origin.
* `sectorAngle` — the unsigned angle in `[0, π]` between the rays from `z` toward `w₁` and
  `w₂`. Convention: `sectorAngle z w₁ w₂ = |arg (discChart z w₂ / discChart z w₁)|`.
* `dist_le_dist_iff_quadratic`, `setOf_dist_le_eq_of_im_eq` — the distance comparison
  between two centers is a Euclidean quadratic inequality; with equal heights the half-space
  is a vertical Euclidean half-plane.
-/

open scoped MatrixGroups

namespace RiemannDynamics

/-! ## Geodesic segments -/

/-- The **geodesic segment** between two points of the upper half plane: the points through
which the triangle inequality is an equality. -/
def geodSeg (a b : UpperHalfPlane) : Set UpperHalfPlane :=
  {z | dist a z + dist z b = dist a b}

theorem mem_geodSeg {a b z : UpperHalfPlane} :
    z ∈ geodSeg a b ↔ dist a z + dist z b = dist a b :=
  Iff.rfl

theorem left_mem_geodSeg (a b : UpperHalfPlane) : a ∈ geodSeg a b := by
  simp [geodSeg]

theorem right_mem_geodSeg (a b : UpperHalfPlane) : b ∈ geodSeg a b := by
  simp [geodSeg]

theorem geodSeg_comm (a b : UpperHalfPlane) : geodSeg a b = geodSeg b a := by
  ext z
  simp only [geodSeg, Set.mem_setOf_eq]
  rw [dist_comm a z, dist_comm z b, dist_comm a b]
  constructor <;> intro h <;> linarith

theorem geodSeg_self (a : UpperHalfPlane) : geodSeg a a = {a} := by
  ext z
  simp only [geodSeg, Set.mem_setOf_eq, dist_self, Set.mem_singleton_iff]
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
    simp only [geodSeg, Set.mem_setOf_eq] at hw ⊢
    rw [dist_smul g a w, dist_smul g w b, dist_smul g a b]
    exact hw
  · intro hz
    refine ⟨g⁻¹ • z, ?_, smul_inv_smul g z⟩
    simp only [geodSeg, Set.mem_setOf_eq] at hz ⊢
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

theorem sectorAngle_nonneg (z w₁ w₂ : UpperHalfPlane) : 0 ≤ sectorAngle z w₁ w₂ :=
  abs_nonneg _

theorem sectorAngle_le_pi (z w₁ w₂ : UpperHalfPlane) : sectorAngle z w₁ w₂ ≤ Real.pi :=
  Complex.abs_arg_le_pi _

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

theorem affPt_coe (z w : UpperHalfPlane) :
    ((affPt z w : UpperHalfPlane) : ℂ) = ((w : ℂ) - (z.re : ℂ)) / (z.im : ℂ) := rfl

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
    simp only at hsq
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
    simp only at hmul
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

theorem vf_den_ne_zero {q : ℝ} (hq : 0 < q) {t : ℝ} (ht : 0 < t) (p : ℝ) :
    Complex.I * (t : ℂ) - ((p : ℂ) - (q : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_im, one_mul, mul_zero, add_zero, zero_add,
    mul_one, zero_sub, sub_neg_eq_add] at him
  linarith

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

/-! ## The Euclidean shape of the distance comparison -/

/-- The hyperbolic distance comparison `dist τ a ≤ dist τ b` is the Euclidean quadratic
inequality `b.im · |τ - a|² ≤ a.im · |τ - b|²`; the equidistance set is the trace on the
upper half plane of a vertical line or of a circle centered on the real axis. -/
theorem dist_le_dist_iff_quadratic (τ a b : UpperHalfPlane) :
    dist τ a ≤ dist τ b ↔
      b.im * dist (τ : ℂ) (a : ℂ) ^ 2 ≤ a.im * dist (τ : ℂ) (b : ℂ) ^ 2 := by
  have hτ : 0 < τ.im := τ.im_pos
  have ha : 0 < a.im := a.im_pos
  have hb : 0 < b.im := b.im_pos
  have hcosh : dist τ a ≤ dist τ b ↔ Real.cosh (dist τ a) ≤ Real.cosh (dist τ b) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg]
  rw [hcosh, UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist, add_le_add_iff_left,
    div_le_div_iff₀ (by positivity) (by positivity)]
  constructor
  · intro h
    have h2 : 2 * τ.im * (b.im * dist (τ : ℂ) (a : ℂ) ^ 2)
        ≤ 2 * τ.im * (a.im * dist (τ : ℂ) (b : ℂ) ^ 2) := by linarith
    exact le_of_mul_le_mul_left h2 (by positivity)
  · intro h
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * τ.im)
    linarith

/-- With equal heights the half-space of the distance comparison is exactly a vertical
Euclidean half-plane. -/
theorem setOf_dist_le_eq_of_im_eq {a b : UpperHalfPlane} (him : a.im = b.im)
    (hre : a.re < b.re) :
    {τ : UpperHalfPlane | dist τ a ≤ dist τ b}
      = {τ : UpperHalfPlane | τ.re ≤ (a.re + b.re) / 2} := by
  ext τ
  simp only [Set.mem_setOf_eq]
  rw [dist_le_dist_iff_quadratic]
  have ha : 0 < a.im := a.im_pos
  have hda : dist (τ : ℂ) (a : ℂ) ^ 2 = (τ.re - a.re) ^ 2 + (τ.im - a.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hdb : dist (τ : ℂ) (b : ℂ) ^ 2 = (τ.re - b.re) ^ 2 + (τ.im - b.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [hda, hdb, ← him]
  constructor
  · intro h
    have h1 : (τ.re - a.re) ^ 2 + (τ.im - a.im) ^ 2
        ≤ (τ.re - b.re) ^ 2 + (τ.im - a.im) ^ 2 := le_of_mul_le_mul_left h ha
    have h3 : 0 < b.re - a.re := by linarith
    nlinarith [h1, h3]
  · intro h
    have h3 : 0 < b.re - a.re := by linarith
    have h1 : (τ.re - a.re) ^ 2 ≤ (τ.re - b.re) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le


/-! ## Trigonometry of the arc-length angle -/

/-- The semicircle angle lies in `(0, π)`. -/
theorem circAngle_mem (u : ℝ) : circAngle u ∈ Set.Ioo 0 Real.pi := by
  constructor
  · have h := Real.arctan_pos.mpr (Real.exp_pos u)
    unfold circAngle
    linarith
  · have h := Real.arctan_lt_pi_div_two (Real.exp u)
    unfold circAngle
    linarith

/-- The half-angle tangent inverts the arc-length coordinate. -/
theorem tan_half_circAngle (u : ℝ) : Real.tan (circAngle u / 2) = Real.exp u := by
  unfold circAngle
  rw [mul_div_cancel_left₀ _ (two_ne_zero' ℝ), Real.tan_arctan]

/-- The sine of the semicircle angle in terms of the arc-length coordinate. -/
theorem sin_circAngle (u : ℝ) :
    Real.sin (circAngle u) = 2 * Real.exp u / (1 + Real.exp u ^ 2) := by
  have hpos : (0 : ℝ) < 1 + Real.exp u ^ 2 := by positivity
  have hsq : Real.sqrt (1 + Real.exp u ^ 2) * Real.sqrt (1 + Real.exp u ^ 2)
      = 1 + Real.exp u ^ 2 := Real.mul_self_sqrt hpos.le
  have hs : (0 : ℝ) < Real.sqrt (1 + Real.exp u ^ 2) := Real.sqrt_pos.mpr hpos
  unfold circAngle
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  linarith [hsq]

/-- The cosine of the semicircle angle in terms of the arc-length coordinate. -/
theorem cos_circAngle (u : ℝ) :
    Real.cos (circAngle u) = (1 - Real.exp u ^ 2) / (1 + Real.exp u ^ 2) := by
  have hpos : (0 : ℝ) < 1 + Real.exp u ^ 2 := by positivity
  have hsq : Real.sqrt (1 + Real.exp u ^ 2) * Real.sqrt (1 + Real.exp u ^ 2)
      = 1 + Real.exp u ^ 2 := Real.mul_self_sqrt hpos.le
  unfold circAngle
  rw [Real.cos_two_mul, Real.cos_arctan]
  rw [div_pow, one_pow, sq (Real.sqrt (1 + Real.exp u ^ 2)), hsq]
  field_simp
  ring

/-- The angle map recovers an angle of `(0, π)` from its arc-length coordinate. -/
theorem circAngle_circCoord {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    circAngle (Real.log (Real.tan (θ / 2))) = θ := by
  have htan : 0 < Real.tan (θ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  unfold circAngle
  rw [Real.exp_log htan, Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith)]
  ring

/-- Monotonicity of the angle map. -/
theorem circAngle_mono {u v : ℝ} (h : u ≤ v) : circAngle u ≤ circAngle v := by
  unfold circAngle
  have := Real.arctan_strictMono.monotone (Real.exp_le_exp.mpr h)
  linarith

/-! ## The semicircle point -/

theorem circPoint_re (c r u : ℝ) (hr : 0 < r) :
    (circPoint c r u hr).re = c + r * Real.cos (circAngle u) := rfl

theorem circPoint_im (c r u : ℝ) (hr : 0 < r) :
    (circPoint c r u hr).im = r * Real.sin (circAngle u) := rfl

/-- The semicircle point lies on its circle. -/
theorem circPoint_norm_sub (c r u : ℝ) (hr : 0 < r) :
    ‖((circPoint c r u hr : UpperHalfPlane) : ℂ) - (c : ℂ)‖ = r := by
  have hsq : Complex.normSq (((circPoint c r u hr : UpperHalfPlane) : ℂ) - (c : ℂ))
      = r ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      circPoint_re, circPoint_im]
    have := Real.sin_sq_add_cos_sq (circAngle u)
    ring_nf
    nlinarith [this]
  calc ‖((circPoint c r u hr : UpperHalfPlane) : ℂ) - (c : ℂ)‖
      = Real.sqrt (‖((circPoint c r u hr : UpperHalfPlane) : ℂ) - (c : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [Complex.sq_norm, hsq]
    _ = r := by rw [Real.sqrt_sq hr.le]

/-- The semicircle-to-axis normalizer in fractional form. -/
theorem circSL_coe {c R : ℝ} (hR : 0 < R) (w : UpperHalfPlane) :
    ((circSL c R hR • w : UpperHalfPlane) : ℂ)
      = ((w : ℂ) - (c : ℂ) + (R : ℂ)) / (-(w : ℂ) + (c : ℂ) + (R : ℂ)) := by
  have hs : Real.sqrt (2 * R) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsC : ((Real.sqrt (2 * R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcoe := coe_smul (circSL c R hR) w
  have h00 : (circSL c R hR) 0 0 = 1 / Real.sqrt (2 * R) := by simp [circSL]
  have h01 : (circSL c R hR) 0 1 = -(c - R) / Real.sqrt (2 * R) := by simp [circSL]
  have h10 : (circSL c R hR) 1 0 = -(1 / Real.sqrt (2 * R)) := by simp [circSL]
  have h11 : (circSL c R hR) 1 1 = (c + R) / Real.sqrt (2 * R) := by simp [circSL]
  rw [h00, h01, h10, h11] at hcoe
  rw [hcoe]
  push_cast
  rw [show ((1 : ℂ) / Real.sqrt (2 * R)) * (w : ℂ) + -((c : ℂ) - (R : ℂ)) /
      Real.sqrt (2 * R) = (((w : ℂ) - (c : ℂ) + (R : ℂ)) * (1 / Real.sqrt (2 * R)))
      from by field_simp; ring]
  rw [show -((1 : ℂ) / Real.sqrt (2 * R)) * (w : ℂ) + ((c : ℂ) + (R : ℂ)) /
      Real.sqrt (2 * R) = ((-(w : ℂ) + (c : ℂ) + (R : ℂ)) * (1 / Real.sqrt (2 * R)))
      from by field_simp; ring]
  rw [mul_comm ((w : ℂ) - (c : ℂ) + (R : ℂ)) _, mul_comm (-(w : ℂ) + (c : ℂ) + (R : ℂ)) _,
    mul_div_mul_left _ _ (one_div_ne_zero hsC)]

/-- The normalizer sends the semicircle point at coordinate `u` to the axis point of
height `exp (-u)`. -/
theorem circSL_smul_circPoint (c r u : ℝ) (hr : 0 < r) :
    ((circSL c r hr • circPoint c r u hr : UpperHalfPlane) : ℂ)
      = Complex.I * (Real.exp (-u) : ℂ) := by
  have hsin := sin_circAngle_pos u
  have hden : -((circPoint c r u hr : UpperHalfPlane) : ℂ) + (c : ℂ) + (r : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, UpperHalfPlane.coe_im,
      Complex.zero_im, add_zero, circPoint_im] at him
    nlinarith [him]
  rw [circSL_coe hr, div_eq_iff hden]
  have hcos := cos_circAngle u
  have hsin' := sin_circAngle u
  have hexp : Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
  have hepos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hS : (0 : ℝ) < 1 + Real.exp u ^ 2 := by positivity
  apply Complex.ext <;>
  · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, circPoint_re, circPoint_im,
      zero_mul, one_mul, zero_sub, zero_add, add_zero, mul_zero, sub_zero]
    rw [hcos, hsin', hexp]
    field_simp
    ring

/-- The arc-length coordinate is the hyperbolic arc length: distances along the semicircle
are coordinate differences. -/
theorem dist_circPoint (c r : ℝ) (hr : 0 < r) (u v : ℝ) :
    dist (circPoint c r u hr) (circPoint c r v hr) = |u - v| := by
  have hre : ∀ w : ℝ, (circSL c r hr • circPoint c r w hr).re = 0 := by
    intro w
    have h := congrArg Complex.re (circSL_smul_circPoint c r w hr)
    rw [UpperHalfPlane.coe_re] at h
    rwa [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero] at h
  have him : ∀ w : ℝ, (circSL c r hr • circPoint c r w hr).im = Real.exp (-w) := by
    intro w
    have h := congrArg Complex.im (circSL_smul_circPoint c r w hr)
    rw [UpperHalfPlane.coe_im] at h
    rwa [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, one_mul, zero_add] at h
  rw [← dist_smul (circSL c r hr) (circPoint c r u hr) (circPoint c r v hr),
    UpperHalfPlane.dist_of_re_eq ((hre u).trans (hre v).symm), him u, him v,
    Real.log_exp, Real.log_exp, Real.dist_eq]
  rw [show -u - -v = -(u - v) by ring, abs_neg]

/-- A point of the semicircle is recovered from its arc-length coordinate. -/
theorem circPoint_circCoord {c r : ℝ} (hr : 0 < r) {z : UpperHalfPlane}
    (hz : ‖(z : ℂ) - (c : ℂ)‖ = r) : circPoint c r (circCoord c z) hr = z := by
  have hzc : ((z : ℂ) - (c : ℂ)).im = z.im := by
    simp [UpperHalfPlane.coe_im]
  have hzim : 0 < ((z : ℂ) - (c : ℂ)).im := by rw [hzc]; exact z.im_pos
  have hne : (z : ℂ) - (c : ℂ) ≠ 0 := fun h => by rw [h] at hzim; simp at hzim
  set θ := Complex.arg ((z : ℂ) - (c : ℂ)) with hθ
  have hθ0 : 0 < θ := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr hzim.le) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_zero_iff.mp h.symm
      exact hzim.ne' this.2
  have hθπ : θ < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi ((z : ℂ) - (c : ℂ))) with h | h
    · exact h
    · exfalso
      have := Complex.arg_eq_pi_iff.mp h
      exact hzim.ne' this.2
  have hang : circAngle (circCoord c z) = θ := by
    rw [circCoord]
    exact circAngle_circCoord hθ0 hθπ
  have hcosθ : Real.cos θ = ((z : ℂ) - (c : ℂ)).re / r := by
    rw [hθ, Complex.cos_arg hne, hz]
  have hsinθ : Real.sin θ = ((z : ℂ) - (c : ℂ)).im / r := by
    rw [hθ, Complex.sin_arg, hz]
  apply UpperHalfPlane.ext
  apply Complex.ext
  · have : ((z : ℂ) - (c : ℂ)).re = (z : ℂ).re - c := by simp
    rw [show ((circPoint c r (circCoord c z) hr : UpperHalfPlane) : ℂ).re
        = c + r * Real.cos (circAngle (circCoord c z)) from rfl, hang, hcosθ, this]
    field_simp
    ring
  · have : ((z : ℂ) - (c : ℂ)).im = (z : ℂ).im := by simp
    rw [show ((circPoint c r (circCoord c z) hr : UpperHalfPlane) : ℂ).im
        = r * Real.sin (circAngle (circCoord c z)) from rfl, hang, hsinθ, this]
    field_simp

/-! ## The two branches of the interpolation -/

theorem geodInterp_vertical {a b : UpperHalfPlane} (hre : a.re = b.re) (t : ℝ) :
    geodInterp a b t
      = UpperHalfPlane.mk ⟨a.re, Real.exp ((1 - t) * Real.log a.im + t * Real.log b.im)⟩
        (Real.exp_pos _) := by
  unfold geodInterp
  rw [if_pos hre]

theorem geodInterp_circle {a b : UpperHalfPlane} (hre : ¬ a.re = b.re) (t : ℝ) :
    geodInterp a b t
      = circPoint (geodCenter a b) (geodRadius a b)
        ((1 - t) * circCoord (geodCenter a b) a + t * circCoord (geodCenter a b) b)
        (geodRadius_pos a b) := by
  unfold geodInterp
  rw [if_neg hre]

theorem geodInterp_self (a : UpperHalfPlane) (t : ℝ) : geodInterp a a t = a := by
  rw [geodInterp_vertical rfl]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_mk]
  apply Complex.ext
  · rw [show ((⟨(a.re : ℝ), Real.exp ((1 - t) * Real.log a.im + t * Real.log a.im)⟩ : ℂ)).re
      = a.re from rfl, UpperHalfPlane.coe_re]
  · rw [show ((⟨(a.re : ℝ), Real.exp ((1 - t) * Real.log a.im + t * Real.log a.im)⟩ : ℂ)).im
      = Real.exp ((1 - t) * Real.log a.im + t * Real.log a.im) from rfl,
      show (1 - t) * Real.log a.im + t * Real.log a.im = Real.log a.im by ring,
      Real.exp_log a.im_pos, UpperHalfPlane.coe_im]

/-! ## Signed distances along the interpolation -/

/-- The vertical distance in logarithmic height. -/
theorem dist_of_re_eq {z w : UpperHalfPlane} (h : z.re = w.re) :
    dist z w = |Real.log z.im - Real.log w.im| := by
  rw [UpperHalfPlane.dist_of_re_eq h, Real.dist_eq]

/-- The interpolation has constant speed: the distance from the left end grows linearly. -/
theorem dist_geodInterp_left_abs (a b : UpperHalfPlane) (t : ℝ) :
    dist a (geodInterp a b t) = |t| * dist a b := by
  by_cases hre : a.re = b.re
  · have hXre : a.re = (geodInterp a b t).re := by rw [geodInterp_vertical hre]; rfl
    have hXim : (geodInterp a b t).im
        = Real.exp ((1 - t) * Real.log a.im + t * Real.log b.im) := by
      rw [geodInterp_vertical hre]; rfl
    rw [dist_of_re_eq hXre, hXim, Real.log_exp, dist_of_re_eq hre,
      show Real.log a.im - ((1 - t) * Real.log a.im + t * Real.log b.im)
        = t * (Real.log a.im - Real.log b.im) by ring, abs_mul]
  · have ha : circPoint (geodCenter a b) (geodRadius a b) (circCoord (geodCenter a b) a)
        (geodRadius_pos a b) = a := circPoint_circCoord (geodRadius_pos a b) rfl
    have hb : circPoint (geodCenter a b) (geodRadius a b) (circCoord (geodCenter a b) b)
        (geodRadius_pos a b) = b :=
      circPoint_circCoord (geodRadius_pos a b) (norm_sub_geodCenter hre)
    have h2 := dist_circPoint (geodCenter a b) (geodRadius a b) (geodRadius_pos a b)
      (circCoord (geodCenter a b) a)
      ((1 - t) * circCoord (geodCenter a b) a + t * circCoord (geodCenter a b) b)
    rw [ha] at h2
    have h3 := dist_circPoint (geodCenter a b) (geodRadius a b) (geodRadius_pos a b)
      (circCoord (geodCenter a b) a) (circCoord (geodCenter a b) b)
    rw [ha, hb] at h3
    rw [geodInterp_circle hre, h2, h3,
      show circCoord (geodCenter a b) a - ((1 - t) * circCoord (geodCenter a b) a
          + t * circCoord (geodCenter a b) b)
        = t * (circCoord (geodCenter a b) a - circCoord (geodCenter a b) b) by ring,
      abs_mul]

/-- The distance to the right endpoint at any real parameter. -/
theorem dist_geodInterp_right_abs (a b : UpperHalfPlane) (t : ℝ) :
    dist (geodInterp a b t) b = |1 - t| * dist a b := by
  by_cases hre : a.re = b.re
  · have hXre : (geodInterp a b t).re = b.re := by
      rw [geodInterp_vertical hre]
      exact hre
    have hXim : (geodInterp a b t).im
        = Real.exp ((1 - t) * Real.log a.im + t * Real.log b.im) := by
      rw [geodInterp_vertical hre]; rfl
    rw [dist_of_re_eq hXre, hXim, Real.log_exp, dist_of_re_eq hre,
      show (1 - t) * Real.log a.im + t * Real.log b.im - Real.log b.im
        = (1 - t) * (Real.log a.im - Real.log b.im) by ring, abs_mul]
  · have ha : circPoint (geodCenter a b) (geodRadius a b) (circCoord (geodCenter a b) a)
        (geodRadius_pos a b) = a := circPoint_circCoord (geodRadius_pos a b) rfl
    have hb : circPoint (geodCenter a b) (geodRadius a b) (circCoord (geodCenter a b) b)
        (geodRadius_pos a b) = b :=
      circPoint_circCoord (geodRadius_pos a b) (norm_sub_geodCenter hre)
    have h2 := dist_circPoint (geodCenter a b) (geodRadius a b) (geodRadius_pos a b)
      ((1 - t) * circCoord (geodCenter a b) a + t * circCoord (geodCenter a b) b)
      (circCoord (geodCenter a b) b)
    rw [hb] at h2
    have h3 := dist_circPoint (geodCenter a b) (geodRadius a b) (geodRadius_pos a b)
      (circCoord (geodCenter a b) a) (circCoord (geodCenter a b) b)
    rw [ha, hb] at h3
    rw [geodInterp_circle hre, h2, h3,
      show (1 - t) * circCoord (geodCenter a b) a + t * circCoord (geodCenter a b) b
          - circCoord (geodCenter a b) b
        = (1 - t) * (circCoord (geodCenter a b) a - circCoord (geodCenter a b) b) by ring,
      abs_mul]

/-! ## Targets: endpoint values, membership, constant speed -/

theorem geodInterp_zero (a b : UpperHalfPlane) : geodInterp a b 0 = a := by
  have h := dist_geodInterp_left_abs a b 0
  rw [abs_zero, zero_mul, dist_eq_zero] at h
  exact h.symm

theorem geodInterp_one (a b : UpperHalfPlane) : geodInterp a b 1 = b := by
  have h := dist_geodInterp_right_abs a b 1
  rw [sub_self, abs_zero, zero_mul, dist_eq_zero] at h
  exact h

theorem geodInterp_mem_geodSeg (a b : UpperHalfPlane) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    geodInterp a b t ∈ geodSeg a b := by
  obtain ⟨h0, h1⟩ := ht
  rw [mem_geodSeg, dist_geodInterp_left_abs, dist_geodInterp_right_abs,
    abs_of_nonneg h0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
  ring

/-- The distance from the left endpoint at any real parameter. -/
theorem dist_geodInterp_left (a b : UpperHalfPlane) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist a (geodInterp a b t) = t * dist a b := by
  rw [dist_geodInterp_left_abs, abs_of_nonneg ht.1]

/-- Distances between two interpolation points are parameter differences. -/
theorem dist_geodInterp_pair (a b : UpperHalfPlane) (s t : ℝ) :
    dist (geodInterp a b s) (geodInterp a b t) = |s - t| * dist a b := by
  by_cases hre : a.re = b.re
  · have hres : (geodInterp a b s).re = (geodInterp a b t).re := by
      rw [geodInterp_vertical hre, geodInterp_vertical hre]; rfl
    have hims : (geodInterp a b s).im
        = Real.exp ((1 - s) * Real.log a.im + s * Real.log b.im) := by
      rw [geodInterp_vertical hre]; rfl
    have himt : (geodInterp a b t).im
        = Real.exp ((1 - t) * Real.log a.im + t * Real.log b.im) := by
      rw [geodInterp_vertical hre]; rfl
    rw [dist_of_re_eq hres, hims, himt, Real.log_exp, Real.log_exp,
      dist_of_re_eq hre,
      show (1 - s) * Real.log a.im + s * Real.log b.im
          - ((1 - t) * Real.log a.im + t * Real.log b.im)
        = (s - t) * (Real.log b.im - Real.log a.im) by ring, abs_mul, abs_sub_comm
        (Real.log b.im) (Real.log a.im)]
  · have ha : circPoint (geodCenter a b) (geodRadius a b) (circCoord (geodCenter a b) a)
        (geodRadius_pos a b) = a := circPoint_circCoord (geodRadius_pos a b) rfl
    have hb : circPoint (geodCenter a b) (geodRadius a b) (circCoord (geodCenter a b) b)
        (geodRadius_pos a b) = b :=
      circPoint_circCoord (geodRadius_pos a b) (norm_sub_geodCenter hre)
    have h3 := dist_circPoint (geodCenter a b) (geodRadius a b) (geodRadius_pos a b)
      (circCoord (geodCenter a b) a) (circCoord (geodCenter a b) b)
    rw [ha, hb] at h3
    rw [geodInterp_circle hre, geodInterp_circle hre, dist_circPoint, h3,
      show (1 - s) * circCoord (geodCenter a b) a + s * circCoord (geodCenter a b) b
          - ((1 - t) * circCoord (geodCenter a b) a + t * circCoord (geodCenter a b) b)
        = (s - t) * (circCoord (geodCenter a b) b - circCoord (geodCenter a b) a) by ring,
      abs_mul, abs_sub_comm (circCoord (geodCenter a b) b) (circCoord (geodCenter a b) a)]

/-! ## Uniqueness on a segment -/

theorem ext_re_im {z w : UpperHalfPlane} (hre : z.re = w.re) (him : z.im = w.im) :
    z = w := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re]
    exact hre
  · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
    exact him

theorem log_bounds {x y v : ℝ} (hx : 0 < x) (hy : 0 < y) (hv : 0 < v)
    (hlo : min x y ≤ v) (hhi : v ≤ max x y) :
    min (Real.log x) (Real.log y) ≤ Real.log v
      ∧ Real.log v ≤ max (Real.log x) (Real.log y) := by
  rcases le_total x y with hxy | hxy
  · rw [min_eq_left hxy] at hlo
    rw [max_eq_right hxy] at hhi
    have hl : Real.log x ≤ Real.log y := (Real.log_le_log_iff hx hy).mpr hxy
    rw [min_eq_left hl, max_eq_right hl]
    exact ⟨(Real.log_le_log_iff hx hv).mpr hlo, (Real.log_le_log_iff hv hy).mpr hhi⟩
  · rw [min_eq_right hxy] at hlo
    rw [max_eq_left hxy] at hhi
    have hl : Real.log y ≤ Real.log x := (Real.log_le_log_iff hy hx).mpr hxy
    rw [min_eq_right hl, max_eq_left hl]
    exact ⟨(Real.log_le_log_iff hy hv).mpr hlo, (Real.log_le_log_iff hv hx).mpr hhi⟩

/-- Two points of a segment at the same distance from the left end coincide. -/
theorem eq_on_geodSeg_of_dist_eq {a b z w : UpperHalfPlane} (hz : z ∈ geodSeg a b)
    (hw : w ∈ geodSeg a b) (h : dist a z = dist a w) : z = w := by
  obtain ⟨g, hga, hgb⟩ := exists_verticalize a b
  have hzmem : g • z ∈ geodSeg (g • a) (g • b) := by
    rw [← smul_geodSeg]
    exact ⟨z, hz, rfl⟩
  have hwmem : g • w ∈ geodSeg (g • a) (g • b) := by
    rw [← smul_geodSeg]
    exact ⟨w, hw, rfl⟩
  have hre : (g • a).re = (g • b).re := by rw [hga, hgb]
  obtain ⟨hzre, hzlo, hzhi⟩ := mem_geodSeg_vertical hre hzmem
  obtain ⟨hwre, hwlo, hwhi⟩ := mem_geodSeg_vertical hre hwmem
  have habs : |Real.log (g • a).im - Real.log (g • z).im|
      = |Real.log (g • a).im - Real.log (g • w).im| := by
    rw [← dist_of_re_eq hzre.symm, ← dist_of_re_eq hwre.symm,
      dist_smul g a z, dist_smul g a w, h]
  obtain ⟨hzlo', hzhi'⟩ := log_bounds (g • a).im_pos (g • b).im_pos (g • z).im_pos
    hzlo hzhi
  obtain ⟨hwlo', hwhi'⟩ := log_bounds (g • a).im_pos (g • b).im_pos (g • w).im_pos
    hwlo hwhi
  have hlog : Real.log (g • z).im = Real.log (g • w).im := by
    rcases le_total (Real.log (g • a).im) (Real.log (g • b).im) with hab | hab
    · rw [min_eq_left hab] at hzlo' hwlo'
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at habs
      linarith
    · rw [max_eq_left hab] at hzhi' hwhi'
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at habs
      linarith
  have him : (g • z).im = (g • w).im := by
    rw [← Real.exp_log (g • z).im_pos, ← Real.exp_log (g • w).im_pos, hlog]
  exact smul_left_cancel g (ext_re_im (hzre.trans hwre.symm) him)

/-- A point of a geodesic segment is determined by its distance from the left end. -/
theorem eq_of_mem_geodSeg_of_dist_eq {a b z w : UpperHalfPlane} (hz : z ∈ geodSeg a b)
    (hw : w ∈ geodSeg a b) (h : dist a z = dist a w) : z = w :=
  eq_on_geodSeg_of_dist_eq hz hw h

/-- The geodesic segment is the image of the parameter interval. -/
theorem geodSeg_eq_image_geodInterp (a b : UpperHalfPlane) :
    geodSeg a b = geodInterp a b '' Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_ne a b with rfl | hab
  · rw [geodSeg_self]
    ext z
    constructor
    · rintro rfl
      exact ⟨0, Set.mem_Icc.mpr (by norm_num), geodInterp_self _ 0⟩
    · rintro ⟨t, -, rfl⟩
      rw [geodInterp_self]
      rfl
  · have hd : 0 < dist a b := dist_pos.mpr hab
    ext z
    constructor
    · intro hz
      have hbet : dist a z + dist z b = dist a b := hz
      have hle : dist a z ≤ dist a b := by
        have := dist_nonneg (x := z) (y := b)
        linarith
      refine ⟨dist a z / dist a b, Set.mem_Icc.mpr ⟨by positivity,
        (div_le_one hd).mpr hle⟩, ?_⟩
      have hmem := geodInterp_mem_geodSeg a b
        (t := dist a z / dist a b) (Set.mem_Icc.mpr ⟨by positivity, (div_le_one hd).mpr hle⟩)
      have hdist : dist a (geodInterp a b (dist a z / dist a b)) = dist a z := by
        rw [dist_geodInterp_left_abs, abs_of_nonneg (by positivity),
          div_mul_cancel₀ _ hd.ne']
      exact eq_on_geodSeg_of_dist_eq hmem hz hdist
    · rintro ⟨t, ht, rfl⟩
      exact geodInterp_mem_geodSeg a b ht

/-- A segment carried by a semicircle stays on the circle. -/
theorem mem_geodSeg_circle {a b : UpperHalfPlane} (hre : ¬ a.re = b.re)
    {x : UpperHalfPlane} (hx : x ∈ geodSeg a b) :
    ‖(x : ℂ) - (geodCenter a b : ℂ)‖ = geodRadius a b := by
  rw [geodSeg_eq_image_geodInterp] at hx
  obtain ⟨t, -, rfl⟩ := hx
  rw [geodInterp_circle hre]
  exact circPoint_norm_sub _ _ _ _

/-! ## Endpoints of a segment -/

/-- The left end of a nondegenerate segment is extreme for betweenness. -/
theorem isSegEndpoint_left {a b : UpperHalfPlane} (hab : a ≠ b) :
    IsSegEndpoint (geodSeg a b) a := by
  refine ⟨left_mem_geodSeg a b, ?_⟩
  intro x hx y hy hmem
  have hd : 0 < dist a b := dist_pos.mpr hab
  rw [geodSeg_eq_image_geodInterp] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨u, hu, rfl⟩ := hy
  have hbet : dist (geodInterp a b s) a + dist a (geodInterp a b u)
      = dist (geodInterp a b s) (geodInterp a b u) := hmem
  rw [dist_comm (geodInterp a b s) a, dist_geodInterp_left_abs,
    abs_of_nonneg hs.1, dist_geodInterp_left_abs, abs_of_nonneg hu.1,
    dist_geodInterp_pair a b s u] at hbet
  have hsum : s + u = |s - u| := by
    have h4 : (s + u) * dist a b = |s - u| * dist a b := by
      rw [add_mul]
      exact hbet
    exact mul_right_cancel₀ hd.ne' h4
  rcases le_total s u with hsu | hsu
  · rw [abs_of_nonpos (by linarith)] at hsum
    have hs0 : s = 0 := by linarith
    left
    rw [hs0, geodInterp_zero]
  · rw [abs_of_nonneg (by linarith)] at hsum
    have hu0 : u = 0 := by linarith
    right
    rw [hu0, geodInterp_zero]

/-- The endpoints of a nondegenerate geodesic segment are exactly its two ends. -/
theorem isSegEndpoint_geodSeg_iff {a b v : UpperHalfPlane} (hab : a ≠ b) :
    IsSegEndpoint (geodSeg a b) v ↔ v = a ∨ v = b := by
  constructor
  · rintro ⟨hv, hext⟩
    exact hext a (left_mem_geodSeg a b) b (right_mem_geodSeg a b) hv
  · rintro (rfl | rfl)
    · exact isSegEndpoint_left hab
    · rw [geodSeg_comm]
      exact isSegEndpoint_left (Ne.symm hab)

/-! ## Normalizing a pair to mirror position -/

/-- A point on the imaginary axis in product form. -/
theorem coe_of_re_zero {z : UpperHalfPlane} (h : z.re = 0) :
    (z : ℂ) = Complex.I * (z.im : ℂ) := by
  rw [coe_eq_re_add_im, h]
  push_cast
  ring

/-- The dilation by a positive ratio as an element of `SL(2, ℝ)`. -/
noncomputable def scaleSL (l : ℝ) (hl : 0 < l) : SL(2, ℝ) :=
  ⟨!![Real.sqrt l, 0; 0, (Real.sqrt l)⁻¹], by
    have hs : Real.sqrt l ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
    rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hs]
    ring⟩

theorem scaleSL_coe (l : ℝ) (hl : 0 < l) (w : UpperHalfPlane) :
    ((scaleSL l hl • w : UpperHalfPlane) : ℂ) = (l : ℂ) * (w : ℂ) := by
  have hs : Real.sqrt l ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
  have hsC : ((Real.sqrt l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcoe := coe_smul (scaleSL l hl) w
  have h00 : (scaleSL l hl) 0 0 = Real.sqrt l := by simp [scaleSL]
  have h01 : (scaleSL l hl) 0 1 = 0 := by simp [scaleSL]
  have h10 : (scaleSL l hl) 1 0 = 0 := by simp [scaleSL]
  have h11 : (scaleSL l hl) 1 1 = (Real.sqrt l)⁻¹ := by simp [scaleSL]
  rw [h00, h01, h10, h11] at hcoe
  rw [hcoe]
  push_cast
  rw [zero_mul, add_zero, zero_add, div_eq_mul_inv, inv_inv,
    show (Real.sqrt l : ℂ) * (w : ℂ) * (Real.sqrt l : ℂ)
      = ((Real.sqrt l * Real.sqrt l : ℝ) : ℂ) * (w : ℂ) by push_cast; ring,
    Real.mul_self_sqrt hl.le]

/-- The rotation by a quarter turn about `i` as an element of `SL(2, ℝ)`: the Möbius map
`z ↦ (z - 1)/(z + 1)`. -/
noncomputable def cayleySL : SL(2, ℝ) :=
  ⟨!![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹; (Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹], by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs : Real.sqrt 2 ≠ 0 := by
      intro h
      rw [h, zero_mul] at h2
      norm_num at h2
    rw [Matrix.det_fin_two_of]
    field_simp
    linarith⟩

theorem cayleySL_coe (w : UpperHalfPlane) :
    ((cayleySL • w : UpperHalfPlane) : ℂ) = ((w : ℂ) - 1) / ((w : ℂ) + 1) := by
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hne : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact h2
  have hcoe := coe_smul cayleySL w
  have h00 : cayleySL 0 0 = (Real.sqrt 2)⁻¹ := by simp [cayleySL]
  have h01 : cayleySL 0 1 = -(Real.sqrt 2)⁻¹ := by simp [cayleySL]
  have h10 : cayleySL 1 0 = (Real.sqrt 2)⁻¹ := by simp [cayleySL]
  have h11 : cayleySL 1 1 = (Real.sqrt 2)⁻¹ := by simp [cayleySL]
  rw [h00, h01, h10, h11] at hcoe
  rw [hcoe]
  push_cast
  rw [show ((Real.sqrt 2)⁻¹ : ℂ) * (w : ℂ) + -((Real.sqrt 2 : ℂ))⁻¹
      = ((Real.sqrt 2)⁻¹ : ℂ) * ((w : ℂ) - 1) by ring,
    show ((Real.sqrt 2)⁻¹ : ℂ) * (w : ℂ) + ((Real.sqrt 2 : ℂ))⁻¹
      = ((Real.sqrt 2)⁻¹ : ℂ) * ((w : ℂ) + 1) by ring]
  push_cast at hne
  rw [mul_div_mul_left _ _ hne]

/-- The quarter-turn sends the axis point of height `Y` to the point of coordinates
`((Y² - 1)/(Y² + 1), 2Y/(Y² + 1))`. -/
theorem cayley_axis {Y : ℝ} {w : UpperHalfPlane} (hw : (w : ℂ) = Complex.I * (Y : ℂ)) :
    (cayleySL • w).re = (Y ^ 2 - 1) / (Y ^ 2 + 1)
      ∧ (cayleySL • w).im = 2 * Y / (Y ^ 2 + 1) := by
  have hY : 0 < Y := by
    have := w.im_pos
    rw [← UpperHalfPlane.coe_im, hw] at this
    simpa using this
  have hcoe : ((cayleySL • w : UpperHalfPlane) : ℂ)
      = (Complex.I * (Y : ℂ) - 1) / (Complex.I * (Y : ℂ) + 1) := by
    rw [cayleySL_coe, hw]
  constructor
  · rw [← UpperHalfPlane.coe_re, hcoe, Complex.div_re]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_mul, one_mul,
      mul_zero, zero_sub, sub_zero, zero_add, add_zero]
    have hd : Y * Y + 1 ≠ 0 := by positivity
    field_simp
    ring
  · rw [← UpperHalfPlane.coe_im, hcoe, Complex.div_im]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_mul, one_mul,
      mul_zero, zero_sub, sub_zero, zero_add, add_zero]
    have hd : Y * Y + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Some element of `SL(2, ℝ)` places two distinct points at equal height, mirror-symmetric
about the imaginary axis and off it. -/
theorem exists_mirror_normalizer {p q : UpperHalfPlane} (hpq : p ≠ q) :
    ∃ g : SL(2, ℝ),
      (g • q).im = (g • p).im ∧ (g • q).re = -(g • p).re ∧ (g • p).re ≠ 0 := by
  obtain ⟨g₀, hp0, hq0⟩ := exists_verticalize p q
  have hne1 : g₀ • p ≠ g₀ • q := fun h => hpq (smul_left_cancel g₀ h)
  have him : (g₀ • p).im ≠ (g₀ • q).im := fun h => hne1 (ext_re_im
    (hp0.trans hq0.symm) h)
  have hyp : 0 < (g₀ • p).im := (g₀ • p).im_pos
  have hyq : 0 < (g₀ • q).im := (g₀ • q).im_pos
  have hm : 0 < Real.sqrt ((g₀ • p).im * (g₀ • q).im) := Real.sqrt_pos.mpr (by positivity)
  set l := (Real.sqrt ((g₀ • p).im * (g₀ • q).im))⁻¹ with hldef
  have hl : 0 < l := inv_pos.mpr hm
  set Y := l * (g₀ • p).im with hYdef
  set Y' := l * (g₀ • q).im with hY'def
  have hY : 0 < Y := by positivity
  have hY' : 0 < Y' := by positivity
  have hprod : Y * Y' = 1 := by
    rw [hYdef, hY'def, hldef]
    have hsq : Real.sqrt ((g₀ • p).im * (g₀ • q).im)
        * Real.sqrt ((g₀ • p).im * (g₀ • q).im) = (g₀ • p).im * (g₀ • q).im :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    linarith [hsq]
  have hY1 : Y ≠ 1 := by
    intro h1
    have h2 : Y' = 1 := by
      rw [h1, one_mul] at hprod
      exact hprod
    have h3 : l * (g₀ • p).im = l * (g₀ • q).im := by
      rw [← hYdef, ← hY'def, h1, h2]
    exact him (mul_left_cancel₀ hl.ne' h3)
  have hwp : ((scaleSL l hl • (g₀ • p) : UpperHalfPlane) : ℂ)
      = Complex.I * (Y : ℂ) := by
    rw [scaleSL_coe, coe_of_re_zero hp0, hYdef]
    push_cast
    ring
  have hwq : ((scaleSL l hl • (g₀ • q) : UpperHalfPlane) : ℂ)
      = Complex.I * (Y' : ℂ) := by
    rw [scaleSL_coe, coe_of_re_zero hq0, hY'def]
    push_cast
    ring
  obtain ⟨hre_p, him_p⟩ := cayley_axis hwp
  obtain ⟨hre_q, him_q⟩ := cayley_axis hwq
  have hY'eq : Y' = Y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  refine ⟨cayleySL * (scaleSL l hl * g₀), ?_, ?_, ?_⟩
  · simp only [mul_smul]
    rw [him_q, him_p, hY'eq]
    field_simp
    ring
  · simp only [mul_smul]
    rw [hre_q, hre_p, hY'eq]
    field_simp
    ring
  · simp only [mul_smul]
    rw [hre_p]
    intro h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · have h2 : (Y - 1) * (Y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact hY1 (by linarith)
      · linarith
    · nlinarith

/-! ## Half-space convexity -/

/-- With equal heights and reversed order the half-space of the distance comparison is the
right vertical Euclidean half-plane. -/
theorem setOf_dist_le_eq_of_im_eq' {a b : UpperHalfPlane} (him : a.im = b.im)
    (hre : b.re < a.re) :
    {τ : UpperHalfPlane | dist τ a ≤ dist τ b}
      = {τ : UpperHalfPlane | (a.re + b.re) / 2 ≤ τ.re} := by
  ext τ
  simp only [Set.mem_setOf_eq]
  rw [dist_le_dist_iff_quadratic]
  have ha : 0 < a.im := a.im_pos
  have hda : dist (τ : ℂ) (a : ℂ) ^ 2 = (τ.re - a.re) ^ 2 + (τ.im - a.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hdb : dist (τ : ℂ) (b : ℂ) ^ 2 = (τ.re - b.re) ^ 2 + (τ.im - b.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  rw [hda, hdb, ← him]
  constructor
  · intro h
    have h1 : (τ.re - a.re) ^ 2 + (τ.im - a.im) ^ 2
        ≤ (τ.re - b.re) ^ 2 + (τ.im - a.im) ^ 2 := le_of_mul_le_mul_left h ha
    have h3 : 0 < a.re - b.re := by linarith
    nlinarith [h1, h3]
  · intro h
    have h3 : 0 < a.re - b.re := by linarith
    have h1 : (τ.re - a.re) ^ 2 ≤ (τ.re - b.re) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le

/-- The real part along a geodesic segment stays between the endpoint real parts. -/
theorem re_mem_geodSeg {A B τ : UpperHalfPlane} (hτ : τ ∈ geodSeg A B) :
    min A.re B.re ≤ τ.re ∧ τ.re ≤ max A.re B.re := by
  by_cases hre : A.re = B.re
  · have h := (mem_geodSeg_vertical hre hτ).1
    rw [h]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  · rw [geodSeg_eq_image_geodInterp] at hτ
    obtain ⟨t, ht, rfl⟩ := hτ
    obtain ⟨h0, h1⟩ := ht
    have hA : circPoint (geodCenter A B) (geodRadius A B) (circCoord (geodCenter A B) A)
        (geodRadius_pos A B) = A := circPoint_circCoord (geodRadius_pos A B) rfl
    have hB : circPoint (geodCenter A B) (geodRadius A B) (circCoord (geodCenter A B) B)
        (geodRadius_pos A B) = B :=
      circPoint_circCoord (geodRadius_pos A B) (norm_sub_geodCenter hre)
    have hreA := congrArg UpperHalfPlane.re hA
    have hreB := congrArg UpperHalfPlane.re hB
    rw [circPoint_re] at hreA hreB
    have hret : (geodInterp A B t).re = geodCenter A B + geodRadius A B
        * Real.cos (circAngle ((1 - t) * circCoord (geodCenter A B) A
          + t * circCoord (geodCenter A B) B)) := by
      rw [geodInterp_circle hre]
      rfl
    have hrpos := geodRadius_pos A B
    have hmem : ∀ u : ℝ, circAngle u ∈ Set.Icc 0 Real.pi := fun u =>
      ⟨(circAngle_mem u).1.le, (circAngle_mem u).2.le⟩
    have hkey : ∀ u v : ℝ, u ≤ v → geodCenter A B + geodRadius A B * Real.cos (circAngle v)
        ≤ geodCenter A B + geodRadius A B * Real.cos (circAngle u) := by
      intro u v huv
      have hcos : Real.cos (circAngle v) ≤ Real.cos (circAngle u) :=
        Real.strictAntiOn_cos.antitoneOn (hmem u) (hmem v) (circAngle_mono huv)
      nlinarith [hrpos, hcos]
    rcases le_total (circCoord (geodCenter A B) A) (circCoord (geodCenter A B) B)
      with hAB | hAB
    · have hlo : circCoord (geodCenter A B) A ≤ (1 - t) * circCoord (geodCenter A B) A
          + t * circCoord (geodCenter A B) B := by nlinarith
      have hhi : (1 - t) * circCoord (geodCenter A B) A
          + t * circCoord (geodCenter A B) B ≤ circCoord (geodCenter A B) B := by nlinarith
      constructor
      · refine le_trans (min_le_right _ _) ?_
        rw [← hreB, hret]
        exact hkey _ _ hhi
      · refine le_trans ?_ (le_max_left _ _)
        rw [← hreA, hret]
        exact hkey _ _ hlo
    · have hlo : circCoord (geodCenter A B) B ≤ (1 - t) * circCoord (geodCenter A B) A
          + t * circCoord (geodCenter A B) B := by nlinarith
      have hhi : (1 - t) * circCoord (geodCenter A B) A
          + t * circCoord (geodCenter A B) B ≤ circCoord (geodCenter A B) A := by nlinarith
      constructor
      · refine le_trans (min_le_left _ _) ?_
        rw [← hreA, hret]
        exact hkey _ _ hhi
      · refine le_trans ?_ (le_max_right _ _)
        rw [← hreB, hret]
        exact hkey _ _ hlo

/-- **Half-space convexity**: the set of points at least as close to `p` as to `q` contains
the geodesic segment between any two of its members. The perpendicular bisector of `p, q`
is a complete geodesic, and the real part is monotone along geodesics after the Möbius
normalization moving the bisector to the imaginary axis. -/
theorem geodSeg_subset_setOf_dist_le {p q a b : UpperHalfPlane}
    (ha : dist a p ≤ dist a q) (hb : dist b p ≤ dist b q) :
    geodSeg a b ⊆ {τ : UpperHalfPlane | dist τ p ≤ dist τ q} := by
  rcases eq_or_ne p q with rfl | hpq
  · intro τ _
    change dist τ p ≤ dist τ p
    exact le_refl _
  · obtain ⟨g, him, hre, h0⟩ := exists_mirror_normalizer hpq
    intro τ hτ
    have hτ' : g • τ ∈ geodSeg (g • a) (g • b) := by
      rw [← smul_geodSeg]
      exact ⟨τ, hτ, rfl⟩
    have hmid : ((g • p).re + (g • q).re) / 2 = 0 := by rw [hre]; ring
    have key : ∀ z : UpperHalfPlane,
        dist z p ≤ dist z q ↔ dist (g • z) (g • p) ≤ dist (g • z) (g • q) := by
      intro z
      rw [dist_smul, dist_smul]
    have hbetw := re_mem_geodSeg hτ'
    change dist τ p ≤ dist τ q
    rcases lt_or_gt_of_ne h0 with hlt | hgt
    · have hset := setOf_dist_le_eq_of_im_eq (a := g • p) (b := g • q) him.symm
        (by rw [hre]; linarith)
      have hsub : ∀ z : UpperHalfPlane,
          dist z (g • p) ≤ dist z (g • q) ↔ z.re ≤ 0 := by
        intro z
        have h := Set.ext_iff.mp hset z
        simp only [Set.mem_setOf_eq] at h
        rw [hmid] at h
        exact h
      have hare : (g • a).re ≤ 0 := (hsub _).mp ((key a).mp ha)
      have hbre : (g • b).re ≤ 0 := (hsub _).mp ((key b).mp hb)
      exact (key τ).mpr ((hsub _).mpr (le_trans hbetw.2 (max_le hare hbre)))
    · have hset := setOf_dist_le_eq_of_im_eq' (a := g • p) (b := g • q) him.symm
        (by rw [hre]; linarith)
      have hsub : ∀ z : UpperHalfPlane,
          dist z (g • p) ≤ dist z (g • q) ↔ 0 ≤ z.re := by
        intro z
        have h := Set.ext_iff.mp hset z
        simp only [Set.mem_setOf_eq] at h
        rw [hmid] at h
        exact h
      have hare : 0 ≤ (g • a).re := (hsub _).mp ((key a).mp ha)
      have hbre : 0 ≤ (g • b).re := (hsub _).mp ((key b).mp hb)
      exact (key τ).mpr ((hsub _).mpr (le_trans (le_min hare hbre) hbetw.1))

/-! ## Sections of a bisector -/

/-- The geodesic segment between two points of a common vertical line is the vertical arc
between their heights. -/
theorem geodSeg_vertical_eq {A B : UpperHalfPlane} (hre : A.re = B.re) :
    geodSeg A B = {x : UpperHalfPlane |
      x.re = A.re ∧ min A.im B.im ≤ x.im ∧ x.im ≤ max A.im B.im} := by
  ext x
  constructor
  · intro hx
    exact mem_geodSeg_vertical hre hx
  · rintro ⟨hxre, hxlo, hxhi⟩
    obtain ⟨hlo, hhi⟩ := log_bounds A.im_pos B.im_pos x.im_pos hxlo hxhi
    change dist A x + dist x B = dist A B
    rw [dist_of_re_eq hxre.symm, dist_of_re_eq (hxre.trans hre),
      dist_of_re_eq hre]
    rcases le_total A.im B.im with hAB | hAB
    · have hl : Real.log A.im ≤ Real.log B.im :=
        (Real.log_le_log_iff A.im_pos B.im_pos).mpr hAB
      rw [min_eq_left hl] at hlo
      rw [max_eq_right hl] at hhi
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      ring
    · have hl : Real.log B.im ≤ Real.log A.im :=
        (Real.log_le_log_iff B.im_pos A.im_pos).mpr hAB
      rw [min_eq_right hl] at hlo
      rw [max_eq_left hl] at hhi
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      ring

/-- After the mirror normalization, the bisector is carried onto the imaginary axis. -/
theorem bisector_re_eq_zero {p q : UpperHalfPlane} {g : SL(2, ℝ)}
    (him : (g • q).im = (g • p).im) (hre : (g • q).re = -(g • p).re)
    (h0 : (g • p).re ≠ 0) (z : UpperHalfPlane) :
    dist z p = dist z q ↔ (g • z).re = 0 := by
  have hmid : ((g • p).re + (g • q).re) / 2 = 0 := by rw [hre]; ring
  have hmid' : ((g • q).re + (g • p).re) / 2 = 0 := by rw [hre]; ring
  have hd : dist z p = dist (g • z) (g • p) := (dist_smul g z p).symm
  have hd' : dist z q = dist (g • z) (g • q) := (dist_smul g z q).symm
  rcases lt_or_gt_of_ne h0 with hlt | hgt
  · have hle := setOf_dist_le_eq_of_im_eq (a := g • p) (b := g • q) him.symm
      (by rw [hre]; linarith)
    have hge := setOf_dist_le_eq_of_im_eq' (a := g • q) (b := g • p) him
      (by rw [hre]; linarith)
    have h1 := Set.ext_iff.mp hle (g • z)
    have h2 := Set.ext_iff.mp hge (g • z)
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [hmid] at h1
    rw [hmid'] at h2
    constructor
    · intro h
      rw [hd, hd'] at h
      exact le_antisymm (h1.mp h.le) (h2.mp h.ge)
    · intro h
      rw [hd, hd']
      exact le_antisymm (h1.mpr h.le) (h2.mpr h.ge)
  · have hle := setOf_dist_le_eq_of_im_eq (a := g • q) (b := g • p) him
      (by rw [hre]; linarith)
    have hge := setOf_dist_le_eq_of_im_eq' (a := g • p) (b := g • q) him.symm
      (by rw [hre]; linarith)
    have h1 := Set.ext_iff.mp hle (g • z)
    have h2 := Set.ext_iff.mp hge (g • z)
    simp only [Set.mem_setOf_eq] at h1 h2
    rw [hmid'] at h1
    rw [hmid] at h2
    constructor
    · intro h
      rw [hd, hd'] at h
      exact le_antisymm (h1.mp h.ge) (h2.mp h.le)
    · intro h
      rw [hd, hd']
      exact le_antisymm (h2.mpr h.ge) (h1.mpr h.le)

/-- A geodesically convex compact set meets a perpendicular bisector in a geodesic segment
(a single point being the degenerate segment). -/
theorem exists_geodSeg_eq_inter_bisector {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hconv : GeodConvex K) {p q : UpperHalfPlane} (hpq : p ≠ q)
    (hne : (K ∩ {τ : UpperHalfPlane | dist τ p = dist τ q}).Nonempty) :
    ∃ a b : UpperHalfPlane, K ∩ {τ : UpperHalfPlane | dist τ p = dist τ q} = geodSeg a b := by
  set S := K ∩ {τ : UpperHalfPlane | dist τ p = dist τ q} with hSdef
  have hSconv : ∀ x ∈ S, ∀ y ∈ S, geodSeg x y ⊆ S := by
    intro x hx y hy z hz
    refine ⟨hconv x hx.1 y hy.1 hz, ?_⟩
    have h1 : dist z p ≤ dist z q :=
      geodSeg_subset_setOf_dist_le (le_of_eq hx.2) (le_of_eq hy.2) hz
    have h2 : dist z q ≤ dist z p :=
      geodSeg_subset_setOf_dist_le (le_of_eq hx.2.symm) (le_of_eq hy.2.symm) hz
    exact le_antisymm h1 h2
  obtain ⟨g, him, hre, h0⟩ := exists_mirror_normalizer hpq
  have hScpt : IsCompact S := hK.inter_right (isClosed_eq
    (Continuous.dist continuous_id continuous_const)
    (Continuous.dist continuous_id continuous_const))
  have hgcont : Continuous ((g • ·) : UpperHalfPlane → UpperHalfPlane) :=
    (isometry_smul UpperHalfPlane g).continuous
  have hS'cpt : IsCompact ((g • ·) '' S) := hScpt.image hgcont
  have hS'ne : ((g • ·) '' S).Nonempty := hne.image _
  have hS're : ∀ x ∈ (g • ·) '' S, x.re = 0 := by
    rintro x ⟨z, hz, rfl⟩
    exact (bisector_re_eq_zero him hre h0 z).mp hz.2
  have hLcpt : IsCompact (UpperHalfPlane.im '' ((g • ·) '' S)) :=
    hS'cpt.image UpperHalfPlane.continuous_im
  have hLne : (UpperHalfPlane.im '' ((g • ·) '' S)).Nonempty := hS'ne.image _
  obtain ⟨x₀, hx₀, hx₀im⟩ := hLcpt.sInf_mem hLne
  obtain ⟨x₁, hx₁, hx₁im⟩ := hLcpt.sSup_mem hLne
  have hy01 : sInf (UpperHalfPlane.im '' ((g • ·) '' S))
      ≤ sSup (UpperHalfPlane.im '' ((g • ·) '' S)) :=
    csInf_le_csSup hLne hLcpt.bddBelow hLcpt.bddAbove
  have hclaim : (g • ·) '' S = geodSeg x₀ x₁ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxlo : sInf (UpperHalfPlane.im '' ((g • ·) '' S)) ≤ x.im :=
        csInf_le hLcpt.bddBelow ⟨x, hx, rfl⟩
      have hxhi : x.im ≤ sSup (UpperHalfPlane.im '' ((g • ·) '' S)) :=
        le_csSup hLcpt.bddAbove ⟨x, hx, rfl⟩
      rw [geodSeg_vertical_eq ((hS're _ hx₀).trans (hS're _ hx₁).symm)]
      refine ⟨(hS're _ hx).trans (hS're _ hx₀).symm, ?_, ?_⟩
      · rw [hx₀im, hx₁im, min_eq_left hy01]
        exact hxlo
      · rw [hx₀im, hx₁im, max_eq_right hy01]
        exact hxhi
    · obtain ⟨z₀, hz₀, hz₀eq⟩ := hx₀
      obtain ⟨z₁, hz₁, hz₁eq⟩ := hx₁
      intro x hx
      have hz₀' : g • z₀ = x₀ := hz₀eq
      have hz₁' : g • z₁ = x₁ := hz₁eq
      have hseg : geodSeg x₀ x₁ = (g • ·) '' geodSeg z₀ z₁ := by
        rw [smul_geodSeg, hz₀', hz₁']
      rw [hseg] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, hSconv z₀ hz₀ z₁ hz₁ hw, rfl⟩
  have hback : (g⁻¹ • ·) '' ((g • ·) '' S) = S := by
    rw [Set.image_image]
    simp only [inv_smul_smul, Set.image_id']
  refine ⟨g⁻¹ • x₀, g⁻¹ • x₁, ?_⟩
  calc S = (g⁻¹ • ·) '' ((g • ·) '' S) := hback.symm
    _ = (g⁻¹ • ·) '' geodSeg x₀ x₁ := by rw [hclaim]
    _ = geodSeg (g⁻¹ • x₀) (g⁻¹ • x₁) := smul_geodSeg g⁻¹ x₀ x₁

/-! ## Collinearity and joint continuity -/

/-- Every interpolation point satisfies one of the three betweenness relations. -/
theorem collinear_geodInterp (a b : UpperHalfPlane) (t : ℝ) :
    dist a (geodInterp a b t) + dist (geodInterp a b t) b = dist a b
      ∨ dist a b + dist b (geodInterp a b t) = dist a (geodInterp a b t)
      ∨ dist (geodInterp a b t) a + dist a b = dist (geodInterp a b t) b := by
  have hL := dist_geodInterp_left_abs a b t
  have hR := dist_geodInterp_right_abs a b t
  rcases le_or_gt 0 t with h0 | h0
  · rcases le_or_gt t 1 with h1 | h1
    · left
      rw [hL, hR, abs_of_nonneg h0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
      ring
    · right; left
      rw [dist_comm b (geodInterp a b t), hL, hR, abs_of_nonneg h0,
        abs_of_neg (by linarith : 1 - t < 0)]
      ring
  · right; right
    rw [dist_comm (geodInterp a b t) a, hL, hR, abs_of_neg h0,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
    ring

/-- Two distinct axis points cannot lie on a common semicircle centered on the real
axis. -/
theorem two_axis_on_circle {E₁ E₂ A B : UpperHalfPlane} (_hre : ¬ E₁.re = E₂.re)
    (hA0 : A.re = 0) (hB0 : B.re = 0) (hAB : A ≠ B)
    (hAc : ‖(A : ℂ) - (geodCenter E₁ E₂ : ℂ)‖ = geodRadius E₁ E₂)
    (hBc : ‖(B : ℂ) - (geodCenter E₁ E₂ : ℂ)‖ = geodRadius E₁ E₂) : False := by
  have hsq : Complex.normSq ((A : ℂ) - (geodCenter E₁ E₂ : ℂ))
      = Complex.normSq ((B : ℂ) - (geodCenter E₁ E₂ : ℂ)) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, hAc, hBc]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero] at hsq
  rw [hA0, hB0] at hsq
  have him : A.im = B.im := by nlinarith [A.im_pos, B.im_pos]
  exact hAB (ext_re_im (hA0.trans hB0.symm) him)

/-- A point collinear with two distinct axis points lies on the axis. -/
theorem collinear_re_zero {A B z : UpperHalfPlane} (hA : A.re = 0) (hB : B.re = 0)
    (hAB : A ≠ B)
    (hcol : dist A z + dist z B = dist A B ∨ dist A B + dist B z = dist A z
      ∨ dist z A + dist A B = dist z B) : z.re = 0 := by
  rcases hcol with hc | hc | hc
  · exact ((mem_geodSeg_vertical (hA.trans hB.symm) hc).1).trans hA
  · have hmem : B ∈ geodSeg A z := hc
    by_cases hAz : A.re = z.re
    · rw [← hAz]
      exact hA
    · exact (two_axis_on_circle hAz hA hB hAB rfl
        (mem_geodSeg_circle hAz hmem)).elim
  · have hmem : A ∈ geodSeg B z := by
      change dist B A + dist A z = dist B z
      rw [dist_comm B A, dist_comm A z, dist_comm B z]
      linarith [hc]
    by_cases hBz : B.re = z.re
    · rw [← hBz]
      exact hB
    · exact (two_axis_on_circle hBz hB hA (Ne.symm hAB) rfl
        (mem_geodSeg_circle hBz hmem)).elim

/-- A point collinear with two distinct base points is determined by its distances from
them. -/
theorem collinear_unique {a b z w : UpperHalfPlane} (hab : a ≠ b)
    (hzc : dist a z + dist z b = dist a b ∨ dist a b + dist b z = dist a z
      ∨ dist z a + dist a b = dist z b)
    (hwc : dist a w + dist w b = dist a b ∨ dist a b + dist b w = dist a w
      ∨ dist w a + dist a b = dist w b)
    (h1 : dist a z = dist a w) (h2 : dist b z = dist b w) : z = w := by
  obtain ⟨g, hga, hgb⟩ := exists_verticalize a b
  have hAB : g • a ≠ g • b := fun h => hab (smul_left_cancel g h)
  have htrans : ∀ u v : UpperHalfPlane, dist (g • u) (g • v) = dist u v := fun u v =>
    dist_smul g u v
  have hzc' : dist (g • a) (g • z) + dist (g • z) (g • b) = dist (g • a) (g • b)
      ∨ dist (g • a) (g • b) + dist (g • b) (g • z) = dist (g • a) (g • z)
      ∨ dist (g • z) (g • a) + dist (g • a) (g • b) = dist (g • z) (g • b) := by
    rcases hzc with h | h | h
    · left; rw [htrans, htrans, htrans]; exact h
    · right; left; rw [htrans, htrans, htrans]; exact h
    · right; right; rw [htrans, htrans, htrans]; exact h
  have hwc' : dist (g • a) (g • w) + dist (g • w) (g • b) = dist (g • a) (g • b)
      ∨ dist (g • a) (g • b) + dist (g • b) (g • w) = dist (g • a) (g • w)
      ∨ dist (g • w) (g • a) + dist (g • a) (g • b) = dist (g • w) (g • b) := by
    rcases hwc with h | h | h
    · left; rw [htrans, htrans, htrans]; exact h
    · right; left; rw [htrans, htrans, htrans]; exact h
    · right; right; rw [htrans, htrans, htrans]; exact h
  have hzre := collinear_re_zero hga hgb hAB hzc'
  have hwre := collinear_re_zero hga hgb hAB hwc'
  by_cases him : (g • z).im = (g • w).im
  · exact smul_left_cancel g (ext_re_im (hzre.trans hwre.symm) him)
  exfalso
  have hlzw : Real.log (g • z).im ≠ Real.log (g • w).im := fun h => him
    (by rw [← Real.exp_log (g • z).im_pos, ← Real.exp_log (g • w).im_pos, h])
  have e1 : |Real.log (g • a).im - Real.log (g • z).im|
      = |Real.log (g • a).im - Real.log (g • w).im| := by
    rw [← dist_of_re_eq (hga.trans hzre.symm),
      ← dist_of_re_eq (hga.trans hwre.symm), htrans, htrans, h1]
  have e2 : |Real.log (g • b).im - Real.log (g • z).im|
      = |Real.log (g • b).im - Real.log (g • w).im| := by
    rw [← dist_of_re_eq (hgb.trans hzre.symm),
      ← dist_of_re_eq (hgb.trans hwre.symm), htrans, htrans, h2]
  rcases abs_eq_abs.mp e1 with h' | h'
  · exact hlzw (by linarith)
  rcases abs_eq_abs.mp e2 with h'' | h''
  · exact hlzw (by linarith)
  have hlab : Real.log (g • a).im = Real.log (g • b).im := by linarith
  have himab : (g • a).im = (g • b).im := by
    rw [← Real.exp_log (g • a).im_pos, ← Real.exp_log (g • b).im_pos, hlab]
  exact hAB (ext_re_im (hga.trans hgb.symm) himab)

open Filter in
/-- Sequential continuity of the interpolation at a diagonal point. -/
theorem tendsto_interp_diag {x : ℕ → UpperHalfPlane × UpperHalfPlane × ℝ}
    {P : UpperHalfPlane × UpperHalfPlane × ℝ}
    (ha : Tendsto (fun n => (x n).1) atTop (nhds P.1))
    (hb : Tendsto (fun n => (x n).2.1) atTop (nhds P.2.1))
    (ht : Tendsto (fun n => (x n).2.2) atTop (nhds P.2.2)) (hab : P.1 = P.2.1) :
    Tendsto (fun n => geodInterp (x n).1 (x n).2.1 (x n).2.2) atTop
      (nhds (geodInterp P.1 P.2.1 P.2.2)) := by
  have hval : geodInterp P.1 P.2.1 P.2.2 = P.1 := by
    rw [← hab]
    exact geodInterp_self P.1 P.2.2
  rw [hval, tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ n, dist (geodInterp (x n).1 (x n).2.1 (x n).2.2) P.1
      ≤ |(x n).2.2| * dist (x n).1 (x n).2.1 + dist (x n).1 P.1 := by
    intro n
    calc dist (geodInterp (x n).1 (x n).2.1 (x n).2.2) P.1
        ≤ dist (geodInterp (x n).1 (x n).2.1 (x n).2.2) (x n).1 + dist (x n).1 P.1 :=
          dist_triangle _ _ _
      _ = |(x n).2.2| * dist (x n).1 (x n).2.1 + dist (x n).1 P.1 := by
          rw [dist_comm (geodInterp (x n).1 (x n).2.1 (x n).2.2) (x n).1,
            dist_geodInterp_left_abs]
  have hg : Tendsto (fun n => |(x n).2.2| * dist (x n).1 (x n).2.1 + dist (x n).1 P.1)
      atTop (nhds (|P.2.2| * dist P.1 P.2.1 + dist P.1 P.1)) :=
    (ht.abs.mul (ha.dist hb)).add (ha.dist tendsto_const_nhds)
  have hzero : |P.2.2| * dist P.1 P.2.1 + dist P.1 P.1 = 0 := by
    rw [hab, dist_self, mul_zero, add_zero]
  rw [hzero] at hg
  exact squeeze_zero (fun n => dist_nonneg) hbound hg

open Filter in
/-- Sequential continuity of the interpolation at a point with distinct ends. -/
theorem tendsto_interp_offdiag {x : ℕ → UpperHalfPlane × UpperHalfPlane × ℝ}
    {P : UpperHalfPlane × UpperHalfPlane × ℝ}
    (ha : Tendsto (fun n => (x n).1) atTop (nhds P.1))
    (hb : Tendsto (fun n => (x n).2.1) atTop (nhds P.2.1))
    (ht : Tendsto (fun n => (x n).2.2) atTop (nhds P.2.2)) (hab : P.1 ≠ P.2.1) :
    Tendsto (fun n => geodInterp (x n).1 (x n).2.1 (x n).2.2) atTop
      (nhds (geodInterp P.1 P.2.1 P.2.2)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have ha' := ha.comp hns
  have hb' := hb.comp hns
  have ht' := ht.comp hns
  have e1 : ∀ᶠ i in atTop, |(x (ns i)).2.2| < |P.2.2| + 1 :=
    ht'.abs.eventually_lt_const (lt_add_one _)
  have e2 : ∀ᶠ i in atTop, dist (x (ns i)).1 (x (ns i)).2.1 < dist P.1 P.2.1 + 1 :=
    (ha'.dist hb').eventually_lt_const (lt_add_one _)
  have e3 : ∀ᶠ i in atTop, dist (x (ns i)).1 P.1 < 1 := by
    have h := ha'.dist (tendsto_const_nhds (x := P.1))
    rw [dist_self] at h
    exact h.eventually_lt_const one_pos
  have hev : ∀ᶠ i in atTop, geodInterp (x (ns i)).1 (x (ns i)).2.1 (x (ns i)).2.2
      ∈ Metric.closedBall P.1 ((|P.2.2| + 1) * (dist P.1 P.2.1 + 1) + 1) := by
    filter_upwards [e1, e2, e3] with i h1 h2 h3
    rw [Metric.mem_closedBall]
    have h4 : dist (geodInterp (x (ns i)).1 (x (ns i)).2.1 (x (ns i)).2.2) P.1
        ≤ |(x (ns i)).2.2| * dist (x (ns i)).1 (x (ns i)).2.1
          + dist (x (ns i)).1 P.1 := by
      calc dist (geodInterp (x (ns i)).1 (x (ns i)).2.1 (x (ns i)).2.2) P.1
          ≤ dist (geodInterp (x (ns i)).1 (x (ns i)).2.1 (x (ns i)).2.2) (x (ns i)).1
            + dist (x (ns i)).1 P.1 := dist_triangle _ _ _
        _ = |(x (ns i)).2.2| * dist (x (ns i)).1 (x (ns i)).2.1
            + dist (x (ns i)).1 P.1 := by
            rw [dist_comm (geodInterp (x (ns i)).1 (x (ns i)).2.1 (x (ns i)).2.2)
              (x (ns i)).1, dist_geodInterp_left_abs]
    have h5 : |(x (ns i)).2.2| * dist (x (ns i)).1 (x (ns i)).2.1
        ≤ (|P.2.2| + 1) * (dist P.1 P.2.1 + 1) :=
      mul_le_mul h1.le h2.le dist_nonneg (by positivity)
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  obtain ⟨z₂, hz₂, φ, hφ, hcv⟩ := (isCompact_closedBall P.1
    ((|P.2.2| + 1) * (dist P.1 P.2.1 + 1) + 1)).tendsto_subseq
    (x := fun i => geodInterp (x (ns (i + N))).1 (x (ns (i + N))).2.1 (x (ns (i + N))).2.2)
    (fun i => hN (i + N) (Nat.le_add_left N i))
  refine ⟨fun i => φ i + N, ?_⟩
  have hms : Tendsto (fun i => φ i + N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right (φ i) N) hφ.tendsto_atTop
  have hA2 : Tendsto (fun i => (x (ns (φ i + N))).1) atTop (nhds P.1) := ha'.comp hms
  have hB2 : Tendsto (fun i => (x (ns (φ i + N))).2.1) atTop (nhds P.2.1) := hb'.comp hms
  have hT2 : Tendsto (fun i => (x (ns (φ i + N))).2.2) atTop (nhds P.2.2) := ht'.comp hms
  have hd1 : dist P.1 z₂ = |P.2.2| * dist P.1 P.2.1 :=
    tendsto_nhds_unique (hA2.dist hcv)
      ((hT2.abs.mul (hA2.dist hB2)).congr
        (fun i => (dist_geodInterp_left_abs _ _ _).symm))
  have hd2 : dist z₂ P.2.1 = |1 - P.2.2| * dist P.1 P.2.1 :=
    tendsto_nhds_unique (hcv.dist hB2)
      ((((tendsto_const_nhds (x := (1:ℝ))).sub hT2).abs.mul (hA2.dist hB2)).congr
        (fun i => (dist_geodInterp_right_abs _ _ _).symm))
  have c1 : Continuous fun w : UpperHalfPlane × UpperHalfPlane × UpperHalfPlane => w.1 :=
    continuous_fst
  have c2 : Continuous fun w : UpperHalfPlane × UpperHalfPlane × UpperHalfPlane => w.2.1 :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun w : UpperHalfPlane × UpperHalfPlane × UpperHalfPlane => w.2.2 :=
    continuous_snd.comp continuous_snd
  have hclosed : IsClosed {w : UpperHalfPlane × UpperHalfPlane × UpperHalfPlane |
      dist w.1 w.2.2 + dist w.2.2 w.2.1 = dist w.1 w.2.1
        ∨ dist w.1 w.2.1 + dist w.2.1 w.2.2 = dist w.1 w.2.2
        ∨ dist w.2.2 w.1 + dist w.1 w.2.1 = dist w.2.2 w.2.1} :=
    (isClosed_eq ((c1.dist c3).add (c3.dist c2)) (c1.dist c2)).union
      ((isClosed_eq ((c1.dist c2).add (c2.dist c3)) (c1.dist c3)).union
        (isClosed_eq ((c3.dist c1).add (c1.dist c2)) (c3.dist c2)))
  have htuple : Tendsto (fun i => ((x (ns (φ i + N))).1, (x (ns (φ i + N))).2.1,
      geodInterp (x (ns (φ i + N))).1 (x (ns (φ i + N))).2.1 (x (ns (φ i + N))).2.2))
      atTop (nhds (P.1, P.2.1, z₂)) :=
    hA2.prodMk_nhds (hB2.prodMk_nhds hcv)
  have hcol := hclosed.mem_of_tendsto htuple
    (Filter.Eventually.of_forall (fun i => collinear_geodInterp _ _ _))
  have heq : z₂ = geodInterp P.1 P.2.1 P.2.2 := by
    apply collinear_unique hab hcol (collinear_geodInterp P.1 P.2.1 P.2.2)
    · exact hd1.trans (dist_geodInterp_left_abs P.1 P.2.1 P.2.2).symm
    · rw [dist_comm P.2.1 z₂, dist_comm P.2.1 (geodInterp P.1 P.2.1 P.2.2), hd2,
        dist_geodInterp_right_abs]
  exact heq ▸ hcv

open Filter in
/-- Geodesic interpolation is jointly continuous in the two endpoints and the parameter. -/
theorem continuous_geodInterp :
    Continuous fun p : UpperHalfPlane × UpperHalfPlane × ℝ => geodInterp p.1 p.2.1 p.2.2 := by
  apply SeqContinuous.continuous
  intro x P hx
  have ha : Tendsto (fun n => (x n).1) atTop (nhds P.1) :=
    (continuous_fst.tendsto P).comp hx
  have hb : Tendsto (fun n => (x n).2.1) atTop (nhds P.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto P).comp hx
  have ht : Tendsto (fun n => (x n).2.2) atTop (nhds P.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto P).comp hx
  by_cases hab : P.1 = P.2.1
  · exact tendsto_interp_diag ha hb ht hab
  · exact tendsto_interp_offdiag ha hb ht hab

end RiemannDynamics
