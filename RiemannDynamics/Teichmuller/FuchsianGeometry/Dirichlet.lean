import RiemannDynamics.Teichmuller.Compactness.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dirichlet domains of Fuchsian groups on the upper half plane

The Dirichlet domain `D(τ₀) = {τ | ∀ γ ∈ Γ, dist τ τ₀ ≤ dist τ (γ • τ₀)}` of a Fuchsian
group and its tiling structure.

* `dirichletDomain` — basepoint membership, closedness, `Γ`-tiling.
* `dirichletDomain_subset_closedBall`, `isCompact_dirichletDomain` — boundedness and
  compactness under orbit density.
* `dirichletSides`, `dirichletDomain_eq_ball_inter_sides` — the finite side set and the
  reconstruction of the domain from finitely many side conditions.
* `ball_subset_dirichletDomain` — interior nonemptiness under a translation-length gap.
* `volume_bisector_eq_zero`, `volume_frontier_dirichletDomain_eq_zero` — bisectors and the
  frontier are volume-null.
* `exists_orbit_density_bound` — orbit density from cocompactness and a trace gap.
* `interior_dirichletDomain_eq`, `disjoint_smul_interior_dirichletDomain`,
  `smul_mem_dirichletSideSet_inv` — the strict-interior characterization, disjointness of
  the open tiles, and the side pairing.
* `contactSet` — the local structure of the tiling: contact tiles at a point, the
  neighborhood meeting only contact tiles, the interior and side characterizations, and the
  cyclic structure of the contact tiles around a vertex.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-- The **Dirichlet domain** of `Γ` centered at `τ₀`: the points at least as close to `τ₀`
as to any other point of its `Γ`-orbit. -/
def dirichletDomain (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : Set UpperHalfPlane :=
  {τ | ∀ γ : Γ, dist τ τ₀ ≤ dist τ (γ • τ₀)}

/-- Membership in the Dirichlet domain, unfolded: `τ` belongs exactly when no point of the
`Γ`-orbit of `τ₀` is strictly closer to `τ` than `τ₀` itself. -/
theorem mem_dirichletDomain {τ : UpperHalfPlane} :
    τ ∈ dirichletDomain Γ τ₀ ↔ ∀ γ : Γ, dist τ τ₀ ≤ dist τ (γ • τ₀) :=
  Iff.rfl

/-! ## Basepoint membership, closedness, tiling -/

/-- The center lies in its own Dirichlet domain: no orbit point can be closer to `τ₀` than
the distance `0` from `τ₀` to itself. -/
theorem basepoint_mem_dirichletDomain : τ₀ ∈ dirichletDomain Γ τ₀ := by
  intro γ
  rw [dist_self]
  exact dist_nonneg

/-- The Dirichlet domain is closed: it is an intersection, over the group, of the closed
half-planes `{τ | dist τ τ₀ ≤ dist τ (γ • τ₀)}`. -/
theorem isClosed_dirichletDomain (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) : IsClosed (dirichletDomain Γ τ₀) := by
  have h : dirichletDomain Γ τ₀ =
      ⋂ γ : Γ, {τ : UpperHalfPlane | dist τ τ₀ ≤ dist τ (γ • τ₀)} := by
    ext τ
    simp only [dirichletDomain, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun γ =>
    isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

/-- **Tiling**: every point has a `Γ`-translate inside the Dirichlet domain. The orbit point
of `τ₀` nearest to `τ` exists because only finitely many translates of `τ₀` enter the closed
ball of radius `dist τ τ₀` about `τ`. -/
theorem exists_smul_mem_dirichletDomain (hΓ : IsFuchsianGroup Γ)
    (τ₀ τ : UpperHalfPlane) : ∃ γ : Γ, γ • τ ∈ dirichletDomain Γ τ₀ := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall τ (dist τ τ₀)).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  have hS : {γ : ↥Γ | dist τ (γ • τ₀) ≤ dist τ τ₀}.Finite := by
    refine hfin1.subset ?_
    intro γ hγ
    refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hγ
  have h1S : (1 : ↥Γ) ∈ {γ : ↥Γ | dist τ (γ • τ₀) ≤ dist τ τ₀} := by
    simp only [Set.mem_setOf_eq, one_smul, le_refl]
  obtain ⟨γ₀, hγ₀S, hγ₀min⟩ :=
    Set.exists_min_image _ (fun γ : ↥Γ => dist τ (γ • τ₀)) hS ⟨1, h1S⟩
  have hglobal : ∀ γ : ↥Γ, dist τ (γ₀ • τ₀) ≤ dist τ (γ • τ₀) := by
    intro γ
    by_cases hγ : dist τ (γ • τ₀) ≤ dist τ τ₀
    · exact hγ₀min γ hγ
    · exact le_trans hγ₀S (le_of_lt (not_le.mp hγ))
  refine ⟨γ₀⁻¹, ?_⟩
  intro γ
  have e1 : dist (γ₀⁻¹ • τ) τ₀ = dist τ (γ₀ • τ₀) := by
    calc dist (γ₀⁻¹ • τ) τ₀ = dist (γ₀ • γ₀⁻¹ • τ) (γ₀ • τ₀) := (dist_smul γ₀ _ _).symm
      _ = dist τ (γ₀ • τ₀) := by rw [smul_inv_smul]
  have e2 : dist (γ₀⁻¹ • τ) (γ • τ₀) = dist τ ((γ₀ * γ) • τ₀) := by
    calc dist (γ₀⁻¹ • τ) (γ • τ₀) = dist (γ₀ • γ₀⁻¹ • τ) (γ₀ • γ • τ₀) :=
        (dist_smul γ₀ _ _).symm
      _ = dist τ ((γ₀ * γ) • τ₀) := by rw [smul_inv_smul, mul_smul]
  rw [e1, e2]
  exact hglobal (γ₀ * γ)

/-! ## Boundedness and compactness under orbit density -/

/-- Under `R`-density of the orbit of `τ₀`, the Dirichlet domain lies in the closed `R`-ball:
the distance to `τ₀` is a lower bound for the distances to all orbit points, hence at most
the infimum. -/
theorem dirichletDomain_subset_closedBall {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    dirichletDomain Γ τ₀ ⊆ Metric.closedBall τ₀ R := by
  intro τ hτ
  rw [Metric.mem_closedBall]
  have hne : (MulAction.orbit Γ τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
  have hlb : dist τ τ₀ ≤ Metric.infDist τ (MulAction.orbit Γ τ₀) := by
    rw [Metric.le_infDist hne]
    intro y hy
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    exact hτ γ
  exact le_trans hlb (hdense τ)

/-- The Dirichlet domain is compact when the orbit of `τ₀` is `R`-dense: it is then a
closed subset of the closed ball of radius `R` about `τ₀`. -/
theorem isCompact_dirichletDomain {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    IsCompact (dirichletDomain Γ τ₀) :=
  (isCompact_closedBall τ₀ R).of_isClosed_subset (isClosed_dirichletDomain Γ τ₀)
    (dirichletDomain_subset_closedBall hdense)

/-! ## The finite side set and reconstruction -/

/-- The **side set** of the Dirichlet domain at density scale `R`: the elements whose
translate of `τ₀` lies within `2R + 1` of `τ₀`. Elements outside it cannot constrain the
domain. -/
def dirichletSides (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (R : ℝ) : Set ↥Γ :=
  {γ : ↥Γ | dist τ₀ (γ • τ₀) ≤ 2 * R + 1}

/-- A Fuchsian group has only finitely many side elements: proper discontinuity bounds the
number of `γ` carrying `τ₀` to within `2R + 1` of itself. -/
theorem finite_dirichletSides (hΓ : IsFuchsianGroup Γ) (τ₀ : UpperHalfPlane) (R : ℝ) :
    (dirichletSides Γ τ₀ R).Finite := by
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall τ₀ (2 * R + 1)).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  refine hfin1.subset ?_
  intro γ hγ
  refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact hγ

/-- **Reconstruction**: the Dirichlet domain is the closed `R`-ball cut by the finitely many
side conditions. The far elements are discharged by the triangle inequality alone. -/
theorem dirichletDomain_eq_ball_inter_sides {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    dirichletDomain Γ τ₀ = {τ ∈ Metric.closedBall τ₀ R |
      ∀ γ ∈ dirichletSides Γ τ₀ R, dist τ τ₀ ≤ dist τ (γ • τ₀)} := by
  ext τ
  constructor
  · intro hτ
    exact ⟨dirichletDomain_subset_closedBall hdense hτ, fun γ _ => hτ γ⟩
  · rintro ⟨hball, hsides⟩
    intro γ
    by_cases hγ : γ ∈ dirichletSides Γ τ₀ R
    · exact hsides γ hγ
    · have h1 : 2 * R + 1 < dist τ₀ (γ • τ₀) := not_le.mp hγ
      have h2 : dist τ τ₀ ≤ R := Metric.mem_closedBall.mp hball
      have h3 : dist τ₀ (γ • τ₀) ≤ dist τ₀ τ + dist τ (γ • τ₀) := dist_triangle _ _ _
      have h4 : dist τ₀ τ = dist τ τ₀ := dist_comm _ _
      linarith

/-! ## Interior nonemptiness under a trace gap -/

/-- Under a translation-length gap `ε`, the open `ε/2`-ball about `τ₀` lies in the Dirichlet
domain: nontrivially-acting elements displace `τ₀` by at least `ε`, and trivially-acting
elements impose no constraint. -/
theorem ball_subset_dirichletDomain {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ) :
    Metric.ball τ₀ (ε / 2) ⊆ dirichletDomain Γ τ₀ := by
  intro τ hτ
  have hd : dist τ τ₀ < ε / 2 := Metric.mem_ball.mp hτ
  intro γ
  by_cases hnt : actsNontrivially (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
  · have hlen : ε ≤ translationLength (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
      hgap _ γ.2 hnt
    have hhyp : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic :=
      (translationLength_pos_iff _).mp (lt_of_lt_of_le hε hlen)
    have hdisp := translationLength_le_dist_smul
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) hhyp τ₀
    rw [← Subgroup.smul_def] at hdisp
    have htri : dist τ₀ (γ • τ₀) ≤ dist τ₀ τ + dist τ (γ • τ₀) := dist_triangle _ _ _
    have hcomm : dist τ₀ τ = dist τ τ₀ := dist_comm _ _
    linarith
  · simp only [actsNontrivially, not_exists, not_not] at hnt
    have hfix : γ • τ₀ = τ₀ := by
      rw [Subgroup.smul_def]
      exact hnt τ₀
    rw [hfix]

/-- Under a trace gap the basepoint is an interior point of its Dirichlet domain. -/
theorem basepoint_mem_interior_dirichletDomain {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ) :
    τ₀ ∈ interior (dirichletDomain Γ τ₀) :=
  interior_maximal (ball_subset_dirichletDomain hε hgap) Metric.isOpen_ball
    (Metric.mem_ball_self (by linarith))

/-! ## Bisectors are volume-null; the frontier is volume-null -/

/-- Vertical lines in `ℂ` are volume-null. -/
theorem volume_re_line_eq_zero (r : ℝ) : volume {w : ℂ | w.re = r} = 0 := by
  have h : {w : ℂ | w.re = r} =
      Complex.measurableEquivRealProd ⁻¹' ({r} ×ˢ (Set.univ : Set ℝ)) := by
    ext w
    simp [Complex.measurableEquivRealProd_apply, Set.mem_prod]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton r).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- Level sets of `normSq (· - c)` in `ℂ` are volume-null: they are empty or spheres. -/
theorem volume_normSq_levelSet_eq_zero (c : ℂ) (k : ℝ) :
    volume {w : ℂ | Complex.normSq (w - c) = k} = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · have h : {w : ℂ | Complex.normSq (w - c) = k} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ Complex.normSq_nonneg (w - c)) (not_le.mpr hk)
    rw [h, measure_empty]
  · have h : {w : ℂ | Complex.normSq (w - c) = k} = Metric.sphere c (Real.sqrt k) := by
      ext w
      rw [Set.mem_setOf_eq, Metric.mem_sphere, dist_eq_norm]
      constructor
      · intro h
        rw [← Real.sqrt_sq (norm_nonneg (w - c)), Complex.sq_norm, h]
      · intro h
        rw [← Complex.sq_norm, h, Real.sq_sqrt hk]
    rw [h]
    exact Measure.addHaar_sphere volume c _

/-- A subset of the upper half plane whose complex image is Lebesgue-null is null for the
hyperbolic measure: the latter is a density against the pullback of the Lebesgue measure. -/
theorem volume_eq_zero_of_coe_image_null {s : Set UpperHalfPlane}
    (h : volume (UpperHalfPlane.coe '' s) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_def]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [UpperHalfPlane.measurableEmbedding_coe.comap_apply]
  exact h

/-- The perpendicular bisector of two distinct points of the upper half plane lies on a
volume-null subset of `ℂ`: equidistance transforms under `cosh_dist` into a real quadratic
equation whose solution set is a vertical line (equal heights) or a circle centered on the
real axis (distinct heights). -/
theorem exists_null_carrier_bisector (a b : UpperHalfPlane) (hab : a ≠ b) :
    ∃ S : Set ℂ, volume S = 0 ∧
      ∀ τ : UpperHalfPlane, dist τ a = dist τ b → (τ : ℂ) ∈ S := by
  have key : ∀ τ : UpperHalfPlane, dist τ a = dist τ b →
      b.im * (((τ : ℂ).re - (a : ℂ).re) ^ 2 + (τ.im - a.im) ^ 2) =
      a.im * (((τ : ℂ).re - (b : ℂ).re) ^ 2 + (τ.im - b.im) ^ 2) := by
    intro τ hd
    have hy : 0 < τ.im := τ.im_pos
    have hA : 0 < a.im := a.im_pos
    have hB : 0 < b.im := b.im_pos
    have hcosh := congrArg Real.cosh hd
    rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hcosh
    have h1 : dist (τ : ℂ) (a : ℂ) ^ 2 / (2 * τ.im * a.im) =
        dist (τ : ℂ) (b : ℂ) ^ 2 / (2 * τ.im * b.im) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h1
    have h2 : (2 * τ.im) * (b.im * dist (τ : ℂ) (a : ℂ) ^ 2) =
        (2 * τ.im) * (a.im * dist (τ : ℂ) (b : ℂ) ^ 2) := by linear_combination h1
    have hkey := mul_left_cancel₀ (by positivity : (2 * τ.im : ℝ) ≠ 0) h2
    have hda : dist (τ : ℂ) (a : ℂ) ^ 2 =
        ((τ : ℂ).re - (a : ℂ).re) ^ 2 + ((τ : ℂ).im - (a : ℂ).im) ^ 2 := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    have hdb : dist (τ : ℂ) (b : ℂ) ^ 2 =
        ((τ : ℂ).re - (b : ℂ).re) ^ 2 + ((τ : ℂ).im - (b : ℂ).im) ^ 2 := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hda, hdb] at hkey
    simpa only [UpperHalfPlane.coe_im] using hkey
  by_cases hAB : a.im = b.im
  · -- equal heights: the bisector lies on a vertical line
    have hpq : (a : ℂ).re ≠ (b : ℂ).re := by
      intro h
      apply hab
      apply UpperHalfPlane.ext
      apply Complex.ext h
      rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      exact hAB
    refine ⟨{w : ℂ | w.re = ((a : ℂ).re + (b : ℂ).re) / 2}, volume_re_line_eq_zero _, ?_⟩
    intro τ hd
    have hkey := key τ hd
    rw [Set.mem_setOf_eq]
    have hB : 0 < b.im := b.im_pos
    have hsq : ((τ : ℂ).re - (a : ℂ).re) ^ 2 = ((τ : ℂ).re - (b : ℂ).re) ^ 2 := by
      have hcancel := mul_left_cancel₀ hB.ne'
        (by linear_combination hkey
          + (((τ : ℂ).re - (b : ℂ).re) ^ 2 + (τ.im - b.im) ^ 2) * hAB :
          b.im * (((τ : ℂ).re - (a : ℂ).re) ^ 2 + (τ.im - a.im) ^ 2) =
          b.im * (((τ : ℂ).re - (b : ℂ).re) ^ 2 + (τ.im - b.im) ^ 2))
      have him : (τ.im - a.im) ^ 2 = (τ.im - b.im) ^ 2 := by rw [hAB]
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact absurd (by linarith) hpq
    · linarith
  · -- distinct heights: the bisector lies on a circle centered on the real axis
    obtain ⟨c, hc⟩ : ∃ c : ℝ,
        c = ((a : ℂ).re * b.im - (b : ℂ).re * a.im) / (b.im - a.im) := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = (b.im * ((a : ℂ).re ^ 2 + a.im ^ 2)
        - a.im * ((b : ℂ).re ^ 2 + b.im ^ 2)) / (b.im - a.im) := ⟨_, rfl⟩
    refine ⟨{w : ℂ | Complex.normSq (w - (c : ℂ)) = c ^ 2 - e},
      volume_normSq_levelSet_eq_zero _ _, ?_⟩
    intro τ hd
    have hkey := key τ hd
    have hBA : b.im - a.im ≠ 0 := sub_ne_zero.mpr fun h => hAB h.symm
    rw [Set.mem_setOf_eq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [UpperHalfPlane.coe_im]
    have hG' : (b.im - a.im) * (τ : ℂ).re ^ 2
        - 2 * ((a : ℂ).re * b.im - (b : ℂ).re * a.im) * (τ : ℂ).re
        + (b.im - a.im) * τ.im ^ 2
        + (b.im * (((a : ℂ).re) ^ 2 + a.im ^ 2) - a.im * (((b : ℂ).re) ^ 2 + b.im ^ 2))
        = 0 := by linear_combination hkey
    have hG : (τ : ℂ).re ^ 2 - 2 * c * (τ : ℂ).re + τ.im ^ 2 + e = 0 := by
      rw [hc, he]
      field_simp
      linear_combination hG'
    linear_combination hG

/-- **Bisectors are volume-null** in the upper half plane. -/
theorem volume_bisector_eq_zero (a b : UpperHalfPlane) (hab : a ≠ b) :
    volume {τ : UpperHalfPlane | dist τ a = dist τ b} = 0 := by
  obtain ⟨S, hS0, hsub⟩ := exists_null_carrier_bisector a b hab
  apply volume_eq_zero_of_coe_image_null
  refine measure_mono_null ?_ hS0
  rintro w ⟨τ, hτ, rfl⟩
  exact hsub τ hτ

/-- The **active sides**: side elements moving the center. Only these can carry frontier. -/
def activeSides (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (R : ℝ) : Set ↥Γ :=
  {γ : ↥Γ | dist τ₀ (γ • τ₀) ≤ 2 * R + 1 ∧ γ • τ₀ ≠ τ₀}

/-- There are only finitely many active sides: they form a subset of the finitely many
side elements. -/
theorem finite_activeSides (hΓ : IsFuchsianGroup Γ) (τ₀ : UpperHalfPlane) (R : ℝ) :
    (activeSides Γ τ₀ R).Finite :=
  (finite_dirichletSides hΓ τ₀ R).subset fun _ hγ => hγ.1

/-- The frontier of the Dirichlet domain lies in the finitely many active bisectors: a domain
point off all active bisectors satisfies its near-side conditions strictly, and an open
neighborhood retains all conditions — the far sides by the triangle inequality. -/
theorem frontier_dirichletDomain_subset (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    frontier (dirichletDomain Γ τ₀) ⊆ ⋃ γ ∈ activeSides Γ τ₀ R,
      {τ : UpperHalfPlane | dist τ τ₀ = dist τ (γ • τ₀)} := by
  intro τ hτ
  rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hτ
  obtain ⟨hτD, hτni⟩ := hτ
  by_contra hcon
  apply hτni
  have hstrict : ∀ γ ∈ activeSides Γ τ₀ R, dist τ τ₀ < dist τ (γ • τ₀) := by
    intro γ hγ
    rcases lt_or_eq_of_le (hτD γ) with h | h
    · exact h
    · exact absurd (Set.mem_biUnion hγ h) hcon
  set V : Set UpperHalfPlane := {τ' | dist τ' τ₀ < R + 1 / 2} ∩
    ⋂ γ ∈ activeSides Γ τ₀ R, {τ' | dist τ' τ₀ < dist τ' (γ • τ₀)} with hVdef
  have hVopen : IsOpen V := by
    refine IsOpen.inter (isOpen_lt (continuous_id.dist continuous_const) continuous_const) ?_
    refine (finite_activeSides hΓ τ₀ R).isOpen_biInter fun γ _ => ?_
    exact isOpen_lt (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
  have hτV : τ ∈ V := by
    constructor
    · have h1 : dist τ τ₀ ≤ R :=
        Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hτD)
      simp only [Set.mem_setOf_eq]
      linarith
    · exact Set.mem_iInter₂.mpr hstrict
  have hVD : V ⊆ dirichletDomain Γ τ₀ := by
    rintro τ' ⟨h1, h2⟩
    intro γ
    by_cases hfix : γ • τ₀ = τ₀
    · rw [hfix]
    · by_cases hγS : dist τ₀ (γ • τ₀) ≤ 2 * R + 1
      · exact le_of_lt (Set.mem_iInter₂.mp h2 γ ⟨hγS, hfix⟩)
      · have h3 : 2 * R + 1 < dist τ₀ (γ • τ₀) := not_le.mp hγS
        have h4 : dist τ₀ (γ • τ₀) ≤ dist τ₀ τ' + dist τ' (γ • τ₀) := dist_triangle _ _ _
        have h5 : dist τ₀ τ' = dist τ' τ₀ := dist_comm _ _
        have h6 : dist τ' τ₀ < R + 1 / 2 := h1
        linarith
  exact interior_maximal hVD hVopen hτV

/-- **The frontier of the Dirichlet domain is volume-null**: it lies in finitely many
bisectors, each of which is null. -/
theorem volume_frontier_dirichletDomain_eq_zero (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    volume (frontier (dirichletDomain Γ τ₀)) = 0 := by
  refine measure_mono_null (frontier_dirichletDomain_subset hΓ hdense) ?_
  rw [measure_biUnion_null_iff (finite_activeSides hΓ τ₀ R).countable]
  intro γ hγ
  exact volume_bisector_eq_zero τ₀ (γ • τ₀) (Ne.symm hγ.2)

/-! ## Orbit density from cocompactness and a trace gap -/

/-- A cocompact Fuchsian group with a trace gap has an orbit-density radius: every point of
the upper half plane lies within a fixed distance of every orbit of the group. -/
theorem exists_orbit_density_bound (hΓ : IsFuchsianGroup Γ) {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (τ₀ : UpperHalfPlane) :
    ∃ R : ℝ, 0 < R ∧ ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R := by
  obtain ⟨A, hA, harea⟩ := hasAreaBound_of_cocompact Γ hcc
  have hgap' : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ := by
    intro γ hγ hnt
    have htr := hgap γ hγ hnt
    have h1c : 1 < Real.cosh (ε / 2) := Real.one_lt_cosh.mpr (half_pos hε).ne'
    have hmax : max 1 (|Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| / 2)
        = |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| / 2 := max_eq_right (by linarith)
    have harc : ε / 2 ≤ Real.arcosh (|Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| / 2) := by
      have h0 : ε / 2 = Real.arcosh (Real.cosh (ε / 2)) :=
        (Real.arcosh_cosh (by linarith : (0 : ℝ) ≤ ε / 2)).symm
      rw [h0]
      exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr (by linarith)
    unfold translationLength
    rw [hmax]
    linarith
  refine ⟨mumfordDensityBound A ε, ?_, fun σ =>
    orbit_infDist_le_of_hasAreaBound hΓ hε hgap' hA harea σ τ₀⟩
  unfold mumfordDensityBound
  have h1 : (0 : ℝ) ≤ (2 * A / upperBallVolume (ε / 8)).toReal := ENNReal.toReal_nonneg
  linarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ ε / 4)]

/-! ## The strict interior, tile disjointness, and the side pairing -/

/-- **Strict-interior characterization**: the interior of the Dirichlet domain consists of
the points whose side conditions at all center-moving elements are strict. A point with an
equality condition is approached by violating points on the extended geodesic through `τ₀`,
and a point with all conditions strict retains them on a neighborhood, the far conditions by
the triangle inequality. -/
theorem interior_dirichletDomain_eq (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    interior (dirichletDomain Γ τ₀) =
      {τ : UpperHalfPlane | ∀ γ : ↥Γ, γ • τ₀ ≠ τ₀ → dist τ τ₀ < dist τ (γ • τ₀)} := by
  ext τ
  constructor
  · intro hτint γ hmove
    have hτD : τ ∈ dirichletDomain Γ τ₀ := interior_subset hτint
    rcases lt_or_eq_of_le (hτD γ) with h | heq
    · exact h
    exfalso
    obtain ⟨b, hbdef⟩ : ∃ b : UpperHalfPlane, b = γ • τ₀ := ⟨_, rfl⟩
    rw [← hbdef] at heq
    have hmoveb : b ≠ τ₀ := by
      rw [hbdef]
      exact hmove
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior τ hτint
    have hy : 0 < τ.im := τ.im_pos
    have hq : 0 < τ₀.im := τ₀.im_pos
    have hu : 0 < b.im := b.im_pos
    -- the equidistance identity at `τ` in coordinates
    have hcosh := congrArg Real.cosh heq
    rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist] at hcosh
    have h1 : dist (τ : ℂ) (τ₀ : ℂ) ^ 2 / (2 * τ.im * τ₀.im) =
        dist (τ : ℂ) (b : ℂ) ^ 2 / (2 * τ.im * b.im) := by
      linarith only [hcosh]
    rw [div_eq_div_iff (by positivity) (by positivity)] at h1
    have h2 : (2 * τ.im) * (b.im * dist (τ : ℂ) (τ₀ : ℂ) ^ 2) =
        (2 * τ.im) * (τ₀.im * dist (τ : ℂ) (b : ℂ) ^ 2) := by
      linear_combination h1
    have hkey := mul_left_cancel₀ (by positivity : (2 * τ.im : ℝ) ≠ 0) h2
    have hda : dist (τ : ℂ) (τ₀ : ℂ) ^ 2 =
        ((τ : ℂ).re - (τ₀ : ℂ).re) ^ 2 + ((τ : ℂ).im - (τ₀ : ℂ).im) ^ 2 := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    have hdb : dist (τ : ℂ) (b : ℂ) ^ 2 =
        ((τ : ℂ).re - (b : ℂ).re) ^ 2 +
          ((τ : ℂ).im - (b : ℂ).im) ^ 2 := by
      rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hda, hdb] at hkey
    simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at hkey
    -- the displacement scale
    have hr1 : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
    have hc : 0 < Real.cosh r - 1 := by linarith only [hr1]
    have hsq : 0 < Real.sqrt (Real.cosh r - 1) := Real.sqrt_pos.mpr hc
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ,
        δ = min (τ.im / 2) (τ.im * Real.sqrt (Real.cosh r - 1) / 2) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by
      rw [hδdef]
      refine lt_min (by positivity) ?_
      linarith only [mul_pos hy hsq]
    have hδy : δ ≤ τ.im / 2 := by
      rw [hδdef]
      exact min_le_left _ _
    have hδsq : δ ^ 2 < τ.im ^ 2 * (Real.cosh r - 1) := by
      have h1' : δ ≤ τ.im * Real.sqrt (Real.cosh r - 1) / 2 := by
        rw [hδdef]
        exact min_le_right _ _
      have h0' : 0 ≤ τ.im * Real.sqrt (Real.cosh r - 1) / 2 := by positivity
      have h2' : δ ^ 2 ≤ (τ.im * Real.sqrt (Real.cosh r - 1) / 2) ^ 2 :=
        sq_le_sq' (by linarith only [hδpos, h0']) h1'
      have h3' : (τ.im * Real.sqrt (Real.cosh r - 1) / 2) ^ 2
          = τ.im ^ 2 * (Real.cosh r - 1) / 4 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hc.le]
        norm_num
      have h4' : 0 < τ.im ^ 2 * (Real.cosh r - 1) := by positivity
      linarith only [h2', h3', h4']
    -- displaced points stay in the ball
    have hclose_of : ∀ w : UpperHalfPlane,
        (w.re - τ.re) ^ 2 + (w.im - τ.im) ^ 2 ≤ δ ^ 2 → τ.im / 2 ≤ w.im →
        w ∈ Metric.ball τ r := by
      intro w hwd hwim
      rw [Metric.mem_ball]
      have hcw : Real.cosh (dist w τ) ≤ 1 + δ ^ 2 / τ.im ^ 2 := by
        rw [UpperHalfPlane.cosh_dist]
        have e : dist (w : ℂ) (τ : ℂ) ^ 2 =
            ((w : ℂ).re - (τ : ℂ).re) ^ 2 + ((w : ℂ).im - (τ : ℂ).im) ^ 2 := by
          rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
            Complex.sub_im]
          ring
        rw [e]
        simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
        have hden : τ.im ^ 2 ≤ 2 * w.im * τ.im := by
          have hp' := mul_nonneg hy.le
            (by linarith only [hwim] : (0 : ℝ) ≤ 2 * w.im - τ.im)
          linarith only [hp']
        have hquot : ((w.re - τ.re) ^ 2 + (w.im - τ.im) ^ 2) / (2 * w.im * τ.im)
            ≤ δ ^ 2 / τ.im ^ 2 :=
          div_le_div₀ (sq_nonneg δ) hwd (by positivity) hden
        linarith only [hquot]
      have hlt : Real.cosh (dist w τ) < Real.cosh r := by
        have hq2 : δ ^ 2 / τ.im ^ 2 < Real.cosh r - 1 := by
          rw [div_lt_iff₀ (by positivity)]
          linarith only [hδsq]
        linarith only [hcw, hq2]
      rw [Real.cosh_lt_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg hr.le] at hlt
      exact hlt
    -- crossing the bisector reverses the strict inequality
    have hswap_of : ∀ w : UpperHalfPlane,
        τ₀.im * ((w.re - b.re) ^ 2 + (w.im - b.im) ^ 2) <
          b.im * ((w.re - τ₀.re) ^ 2 + (w.im - τ₀.im) ^ 2) →
        dist w b < dist w τ₀ := by
      intro w hw
      have hcw : Real.cosh (dist w b) < Real.cosh (dist w τ₀) := by
        rw [UpperHalfPlane.cosh_dist, UpperHalfPlane.cosh_dist]
        have e1 : dist (w : ℂ) (b : ℂ) ^ 2 =
            ((w : ℂ).re - (b : ℂ).re) ^ 2 +
              ((w : ℂ).im - (b : ℂ).im) ^ 2 := by
          rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
            Complex.sub_im]
          ring
        have e2 : dist (w : ℂ) (τ₀ : ℂ) ^ 2 =
            ((w : ℂ).re - (τ₀ : ℂ).re) ^ 2 + ((w : ℂ).im - (τ₀ : ℂ).im) ^ 2 := by
          rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
            Complex.sub_im]
          ring
        rw [e1, e2]
        simp only [UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
        have h2w : (0 : ℝ) < 2 * w.im := by linarith only [w.im_pos]
        refine add_lt_add_of_le_of_lt le_rfl ?_
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        linarith only [mul_lt_mul_of_pos_left hw h2w]
      rwa [Real.cosh_lt_cosh, abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at hcw
    by_cases hqu : τ₀.im = b.im
    · -- equal heights: horizontal displacement toward the farther center
      have hps : τ₀.re ≠ b.re := by
        intro h
        apply hmoveb
        apply UpperHalfPlane.ext
        apply Complex.ext
        · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re]
          exact h.symm
        · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
          exact hqu.symm
      rcases lt_or_gt_of_ne hps with hplt | hpgt
      · have him : 0 < ((τ : ℂ) + (δ : ℂ)).im := by
          rw [Complex.add_im, Complex.ofReal_im, add_zero, UpperHalfPlane.coe_im]
          exact hy
        obtain ⟨w, hwdef⟩ : ∃ w : UpperHalfPlane,
            w = UpperHalfPlane.mk ((τ : ℂ) + (δ : ℂ)) him := ⟨_, rfl⟩
        have hwcoe : (w : ℂ) = (τ : ℂ) + (δ : ℂ) := by rw [hwdef]
        have hwre : w.re = τ.re + δ := by
          rw [← UpperHalfPlane.coe_re, hwcoe, Complex.add_re, Complex.ofReal_re,
            UpperHalfPlane.coe_re]
        have hwim : w.im = τ.im := by
          rw [← UpperHalfPlane.coe_im, hwcoe, Complex.add_im, Complex.ofReal_im, add_zero,
            UpperHalfPlane.coe_im]
        have hwD : w ∈ dirichletDomain Γ τ₀ := by
          refine interior_subset (hball (hclose_of w ?_ ?_))
          · rw [hwre, hwim]
            exact le_of_eq (by ring)
          · rw [hwim]
            linarith only [hy, hδpos, hδy]
        have hid : b.im * ((τ.re + δ - τ₀.re) ^ 2 + (τ.im - τ₀.im) ^ 2)
            - τ₀.im * ((τ.re + δ - b.re) ^ 2 + (τ.im - b.im) ^ 2)
            = 2 * δ * τ₀.im * (b.re - τ₀.re) := by
          linear_combination hkey - (2 * δ * (τ.re - τ₀.re) + δ ^ 2) * hqu
        have hpos : 0 < 2 * δ * τ₀.im * (b.re - τ₀.re) := by
          have h1' : 0 < b.re - τ₀.re := by linarith only [hplt]
          have h2' : (0 : ℝ) < 2 * δ := by linarith only [hδpos]
          exact mul_pos (mul_pos h2' hq) h1'
        have hswap : dist w b < dist w τ₀ := by
          refine hswap_of w ?_
          rw [hwre, hwim]
          linarith only [hid, hpos]
        have hle := hwD γ
        rw [← hbdef] at hle
        exact absurd hle (not_le.mpr hswap)
      · have him : 0 < ((τ : ℂ) - (δ : ℂ)).im := by
          rw [Complex.sub_im, Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_im]
          exact hy
        obtain ⟨w, hwdef⟩ : ∃ w : UpperHalfPlane,
            w = UpperHalfPlane.mk ((τ : ℂ) - (δ : ℂ)) him := ⟨_, rfl⟩
        have hwcoe : (w : ℂ) = (τ : ℂ) - (δ : ℂ) := by rw [hwdef]
        have hwre : w.re = τ.re - δ := by
          rw [← UpperHalfPlane.coe_re, hwcoe, Complex.sub_re, Complex.ofReal_re,
            UpperHalfPlane.coe_re]
        have hwim : w.im = τ.im := by
          rw [← UpperHalfPlane.coe_im, hwcoe, Complex.sub_im, Complex.ofReal_im, sub_zero,
            UpperHalfPlane.coe_im]
        have hwD : w ∈ dirichletDomain Γ τ₀ := by
          refine interior_subset (hball (hclose_of w ?_ ?_))
          · rw [hwre, hwim]
            exact le_of_eq (by ring)
          · rw [hwim]
            linarith only [hy, hδpos, hδy]
        have hid : b.im * ((τ.re - δ - τ₀.re) ^ 2 + (τ.im - τ₀.im) ^ 2)
            - τ₀.im * ((τ.re - δ - b.re) ^ 2 + (τ.im - b.im) ^ 2)
            = 2 * δ * τ₀.im * (τ₀.re - b.re) := by
          linear_combination hkey + (2 * δ * (τ.re - τ₀.re) - δ ^ 2) * hqu
        have hpos : 0 < 2 * δ * τ₀.im * (τ₀.re - b.re) := by
          have h1' : 0 < τ₀.re - b.re := by linarith only [hpgt]
          have h2' : (0 : ℝ) < 2 * δ := by linarith only [hδpos]
          exact mul_pos (mul_pos h2' hq) h1'
        have hswap : dist w b < dist w τ₀ := by
          refine hswap_of w ?_
          rw [hwre, hwim]
          linarith only [hid, hpos]
        have hle := hwD γ
        rw [← hbdef] at hle
        exact absurd hle (not_le.mpr hswap)
    · -- distinct heights: vertical displacement toward the lower center
      rcases lt_or_gt_of_ne hqu with hlt | hgt
      · have him : 0 < ((τ : ℂ) + (δ : ℂ) * Complex.I).im := by
          rw [Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, UpperHalfPlane.coe_im]
          linarith only [hy, hδpos]
        obtain ⟨w, hwdef⟩ : ∃ w : UpperHalfPlane,
            w = UpperHalfPlane.mk ((τ : ℂ) + (δ : ℂ) * Complex.I) him := ⟨_, rfl⟩
        have hwcoe : (w : ℂ) = (τ : ℂ) + (δ : ℂ) * Complex.I := by rw [hwdef]
        have hwre : w.re = τ.re := by
          rw [← UpperHalfPlane.coe_re, hwcoe, Complex.add_re, Complex.mul_I_re,
            Complex.ofReal_im, neg_zero, add_zero, UpperHalfPlane.coe_re]
        have hwim : w.im = τ.im + δ := by
          rw [← UpperHalfPlane.coe_im, hwcoe, Complex.add_im, Complex.mul_I_im,
            Complex.ofReal_re, UpperHalfPlane.coe_im]
        have hwD : w ∈ dirichletDomain Γ τ₀ := by
          refine interior_subset (hball (hclose_of w ?_ ?_))
          · rw [hwre, hwim]
            exact le_of_eq (by ring)
          · rw [hwim]
            linarith only [hy, hδpos, hδy]
        have hid : b.im * ((τ.re - τ₀.re) ^ 2 + (τ.im + δ - τ₀.im) ^ 2)
            - τ₀.im * ((τ.re - b.re) ^ 2 + (τ.im + δ - b.im) ^ 2)
            = (b.im - τ₀.im) * δ * (2 * τ.im + δ) := by
          linear_combination hkey
        have hpos : 0 < (b.im - τ₀.im) * δ * (2 * τ.im + δ) := by
          have h1' : 0 < b.im - τ₀.im := by linarith only [hlt]
          exact mul_pos (mul_pos h1' hδpos) (by linarith only [hy, hδpos, hδy])
        have hswap : dist w b < dist w τ₀ := by
          refine hswap_of w ?_
          rw [hwre, hwim]
          linarith only [hid, hpos]
        have hle := hwD γ
        rw [← hbdef] at hle
        exact absurd hle (not_le.mpr hswap)
      · have him : 0 < ((τ : ℂ) - (δ : ℂ) * Complex.I).im := by
          rw [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re, UpperHalfPlane.coe_im]
          linarith only [hy, hδy]
        obtain ⟨w, hwdef⟩ : ∃ w : UpperHalfPlane,
            w = UpperHalfPlane.mk ((τ : ℂ) - (δ : ℂ) * Complex.I) him := ⟨_, rfl⟩
        have hwcoe : (w : ℂ) = (τ : ℂ) - (δ : ℂ) * Complex.I := by rw [hwdef]
        have hwre : w.re = τ.re := by
          rw [← UpperHalfPlane.coe_re, hwcoe, Complex.sub_re, Complex.mul_I_re,
            Complex.ofReal_im, neg_zero, sub_zero, UpperHalfPlane.coe_re]
        have hwim : w.im = τ.im - δ := by
          rw [← UpperHalfPlane.coe_im, hwcoe, Complex.sub_im, Complex.mul_I_im,
            Complex.ofReal_re, UpperHalfPlane.coe_im]
        have hwD : w ∈ dirichletDomain Γ τ₀ := by
          refine interior_subset (hball (hclose_of w ?_ ?_))
          · rw [hwre, hwim]
            exact le_of_eq (by ring)
          · rw [hwim]
            linarith only [hy, hδpos, hδy]
        have hid : b.im * ((τ.re - τ₀.re) ^ 2 + (τ.im - δ - τ₀.im) ^ 2)
            - τ₀.im * ((τ.re - b.re) ^ 2 + (τ.im - δ - b.im) ^ 2)
            = (τ₀.im - b.im) * δ * (2 * τ.im - δ) := by
          linear_combination hkey
        have hpos : 0 < (τ₀.im - b.im) * δ * (2 * τ.im - δ) := by
          have h1' : 0 < τ₀.im - b.im := by linarith only [hgt]
          exact mul_pos (mul_pos h1' hδpos) (by linarith only [hy, hδpos, hδy])
        have hswap : dist w b < dist w τ₀ := by
          refine hswap_of w ?_
          rw [hwre, hwim]
          linarith only [hid, hpos]
        have hle := hwD γ
        rw [← hbdef] at hle
        exact absurd hle (not_le.mpr hswap)
  · intro hτ
    have hτD : τ ∈ dirichletDomain Γ τ₀ := by
      intro γ
      by_cases hfix : γ • τ₀ = τ₀
      · rw [hfix]
      · exact (hτ γ hfix).le
    set V : Set UpperHalfPlane := {τ' | dist τ' τ₀ < R + 1 / 2} ∩
      ⋂ γ ∈ activeSides Γ τ₀ R, {τ' | dist τ' τ₀ < dist τ' (γ • τ₀)} with hVdef
    have hVopen : IsOpen V := by
      refine IsOpen.inter (isOpen_lt (continuous_id.dist continuous_const) continuous_const) ?_
      refine (finite_activeSides hΓ τ₀ R).isOpen_biInter fun γ _ => ?_
      exact isOpen_lt (continuous_id.dist continuous_const)
        (continuous_id.dist continuous_const)
    have hτV : τ ∈ V := by
      constructor
      · have h1 : dist τ τ₀ ≤ R :=
          Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hτD)
        simp only [Set.mem_setOf_eq]
        linarith
      · exact Set.mem_iInter₂.mpr fun γ hγ => hτ γ hγ.2
    have hVD : V ⊆ dirichletDomain Γ τ₀ := by
      rintro τ' ⟨h1, h2⟩
      intro γ
      by_cases hfix : γ • τ₀ = τ₀
      · rw [hfix]
      · by_cases hγS : dist τ₀ (γ • τ₀) ≤ 2 * R + 1
        · exact le_of_lt (Set.mem_iInter₂.mp h2 γ ⟨hγS, hfix⟩)
        · have h3 : 2 * R + 1 < dist τ₀ (γ • τ₀) := not_le.mp hγS
          have h4 : dist τ₀ (γ • τ₀) ≤ dist τ₀ τ' + dist τ' (γ • τ₀) := dist_triangle _ _ _
          have h5 : dist τ₀ τ' = dist τ' τ₀ := dist_comm _ _
          have h6 : dist τ' τ₀ < R + 1 / 2 := h1
          linarith
    exact interior_maximal hVD hVopen hτV

/-- **Open tiles are disjoint**: an element moving the center maps the interior of the
Dirichlet domain off itself, as a common point would satisfy contradictory strict
inequalities for `γ` and `γ⁻¹`. -/
theorem disjoint_smul_interior_dirichletDomain (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {γ : ↥Γ} (hmove : γ • τ₀ ≠ τ₀) :
    Disjoint (interior (dirichletDomain Γ τ₀))
      ((γ • ·) '' interior (dirichletDomain Γ τ₀)) := by
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  rw [Set.disjoint_left]
  rintro z hz ⟨w, hw, rfl⟩
  rw [interior_dirichletDomain_eq hΓ hdense] at hz hw
  have hmove' : γ⁻¹ • τ₀ ≠ τ₀ := by
    intro h
    apply hmove
    conv_lhs => rw [← h]
    rw [smul_inv_smul]
  have h1 : dist (γ • w) τ₀ < dist (γ • w) (γ • τ₀) := hz γ hmove
  have h2 : dist w τ₀ < dist w (γ⁻¹ • τ₀) := hw γ⁻¹ hmove'
  have e1 : dist (γ • w) (γ • τ₀) = dist w τ₀ := dist_smul γ w τ₀
  have e2 : dist w (γ⁻¹ • τ₀) = dist (γ • w) τ₀ := by
    calc dist w (γ⁻¹ • τ₀) = dist (γ • w) (γ • γ⁻¹ • τ₀) := (dist_smul γ _ _).symm
      _ = dist (γ • w) τ₀ := by rw [smul_inv_smul]
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- The complement of the open tiles lies in the `Γ`-orbit of the frontier of the Dirichlet
domain, a countable union of null sets; hence the open tiles cover almost every point. -/
theorem volume_compl_iUnion_smul_interior_eq_zero (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    volume ((⋃ γ : ↥Γ, (γ • ·) '' interior (dirichletDomain Γ τ₀))ᶜ) = 0 := by
  classical
  haveI : SMulInvariantMeasure (↥Γ) UpperHalfPlane volume :=
    ⟨fun c s hs => SMulInvariantMeasure.measure_preimage_smul
      (μ := (volume : Measure UpperHalfPlane))
      (Matrix.SpecialLinearGroup.mapGL ℝ (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)) hs⟩
  haveI : Countable ↥Γ := IsFuchsianGroup.countable hΓ
  have hsub : (⋃ γ : ↥Γ, (γ • ·) '' interior (dirichletDomain Γ τ₀))ᶜ ⊆
      ⋃ γ : ↥Γ, (γ • ·) '' frontier (dirichletDomain Γ τ₀) := by
    intro z hz
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ τ₀ z
    have hnot : γ • z ∉ interior (dirichletDomain Γ τ₀) := by
      intro hin
      exact hz (Set.mem_iUnion.mpr ⟨γ⁻¹, γ • z, hin, inv_smul_smul γ z⟩)
    have hfr : γ • z ∈ frontier (dirichletDomain Γ τ₀) := by
      rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq]
      exact ⟨hγ, hnot⟩
    exact Set.mem_iUnion.mpr ⟨γ⁻¹, γ • z, hfr, inv_smul_smul γ z⟩
  refine measure_mono_null hsub ?_
  rw [measure_iUnion_null_iff]
  intro γ
  have himg : (γ • ·) '' frontier (dirichletDomain Γ τ₀) =
      (γ⁻¹ • ·) ⁻¹' frontier (dirichletDomain Γ τ₀) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [inv_smul_smul] using hw
    · intro hz
      exact ⟨γ⁻¹ • z, hz, smul_inv_smul γ z⟩
  rw [himg, SMulInvariantMeasure.measure_preimage_smul (μ := (volume : Measure UpperHalfPlane))
    γ⁻¹ isClosed_frontier.measurableSet]
  exact volume_frontier_dirichletDomain_eq_zero hΓ hdense

/-- A **side** of the Dirichlet domain: the domain points equidistant from `τ₀` and from the
`γ`-translate of `τ₀`. -/
def dirichletSideSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (γ : ↥Γ) : Set UpperHalfPlane :=
  dirichletDomain Γ τ₀ ∩ {τ | dist τ τ₀ = dist τ (γ • τ₀)}

/-- **Side pairing**: `γ⁻¹` carries the side of `γ` onto the side of `γ⁻¹`, since
`dist (γ⁻¹ • τ) (δ • τ₀) = dist τ ((γ * δ) • τ₀) ≥ dist τ τ₀ = dist (γ⁻¹ • τ) τ₀`. -/
theorem smul_mem_dirichletSideSet_inv {γ : ↥Γ} {τ : UpperHalfPlane}
    (hτ : τ ∈ dirichletSideSet Γ τ₀ γ) : γ⁻¹ • τ ∈ dirichletSideSet Γ τ₀ γ⁻¹ := by
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  obtain ⟨hD, heq⟩ := hτ
  have hbase : dist (γ⁻¹ • τ) τ₀ = dist τ τ₀ := by
    calc dist (γ⁻¹ • τ) τ₀ = dist (γ • γ⁻¹ • τ) (γ • τ₀) := (dist_smul γ _ _).symm
      _ = dist τ (γ • τ₀) := by rw [smul_inv_smul]
      _ = dist τ τ₀ := heq.symm
  refine ⟨fun δ => ?_, ?_⟩
  · have e : dist (γ⁻¹ • τ) (δ • τ₀) = dist τ ((γ * δ) • τ₀) := by
      calc dist (γ⁻¹ • τ) (δ • τ₀) = dist (γ • γ⁻¹ • τ) (γ • δ • τ₀) := (dist_smul γ _ _).symm
        _ = dist τ ((γ * δ) • τ₀) := by rw [smul_inv_smul, mul_smul]
    rw [hbase, e]
    exact hD (γ * δ)
  · have e : dist (γ⁻¹ • τ) (γ⁻¹ • τ₀) = dist τ τ₀ := dist_smul γ⁻¹ τ τ₀
    change dist (γ⁻¹ • τ) τ₀ = dist (γ⁻¹ • τ) (γ⁻¹ • τ₀)
    rw [hbase, e]

/-! ## Contact sets and the local structure of the tiling -/

/-- The **contact set** of a point: the elements whose translate of `τ₀` realizes the
distance from the point to the orbit of `τ₀`. -/
def contactSet (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (τ₀ : UpperHalfPlane) (z : UpperHalfPlane) : Set ↥Γ :=
  {γ : ↥Γ | dist z (γ • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀)}

/-- The contact set is nonempty: the nearest orbit point exists by proper discontinuity. -/
theorem nonempty_contactSet (hΓ : IsFuchsianGroup Γ) (τ₀ z : UpperHalfPlane) :
    (contactSet Γ τ₀ z).Nonempty := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall z (dist z τ₀)).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  have hS : {γ : ↥Γ | dist z (γ • τ₀) ≤ dist z τ₀}.Finite := by
    refine hfin1.subset ?_
    intro γ hγ
    refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hγ
  have h1S : (1 : ↥Γ) ∈ {γ : ↥Γ | dist z (γ • τ₀) ≤ dist z τ₀} := by
    simp only [Set.mem_setOf_eq, one_smul, le_refl]
  obtain ⟨γ₀, hγ₀S, hγ₀min⟩ :=
    Set.exists_min_image _ (fun γ : ↥Γ => dist z (γ • τ₀)) hS ⟨1, h1S⟩
  have hglobal : ∀ γ : ↥Γ, dist z (γ₀ • τ₀) ≤ dist z (γ • τ₀) := by
    intro γ
    by_cases hγ : dist z (γ • τ₀) ≤ dist z τ₀
    · exact hγ₀min γ hγ
    · exact le_trans hγ₀S (le_of_lt (not_le.mp hγ))
  have hne : (MulAction.orbit Γ τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
  refine ⟨γ₀, ?_⟩
  simp only [contactSet, Set.mem_setOf_eq]
  refine le_antisymm ?_
    (Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γ₀, rfl⟩))
  refine (Metric.le_infDist hne).mpr ?_
  intro y hy
  obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  exact hglobal γ

/-- The contact set is finite: only finitely many orbit points enter a closed ball. -/
theorem finite_contactSet (hΓ : IsFuchsianGroup Γ) (τ₀ z : UpperHalfPlane) :
    (contactSet Γ τ₀ z).Finite := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall z (dist z τ₀)).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  have hS : {γ : ↥Γ | dist z (γ • τ₀) ≤ dist z τ₀}.Finite := by
    refine hfin1.subset ?_
    intro γ hγ
    refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hγ
  refine hS.subset ?_
  intro γ hγ
  simp only [contactSet, Set.mem_setOf_eq] at hγ
  simp only [Set.mem_setOf_eq]
  rw [hγ]
  exact Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_self τ₀)

/-- A point lies in the `γ`-tile exactly when `γ` is a contact element of the point. -/
theorem mem_contactSet_iff_mem_smul_dirichletDomain (γ : ↥Γ) (z : UpperHalfPlane) :
    γ ∈ contactSet Γ τ₀ z ↔ z ∈ (γ • ·) '' dirichletDomain Γ τ₀ := by
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hkey : ∀ (β δ : ↥Γ) (w : UpperHalfPlane),
      dist (β⁻¹ • w) (δ • τ₀) = dist w ((β * δ) • τ₀) := by
    intro β δ w
    calc dist (β⁻¹ • w) (δ • τ₀) = dist (β • β⁻¹ • w) (β • δ • τ₀) :=
        (dist_smul β _ _).symm
      _ = dist w ((β * δ) • τ₀) := by rw [smul_inv_smul, mul_smul]
  have h1 : dist (γ⁻¹ • z) τ₀ = dist z (γ • τ₀) := by
    have h := hkey γ 1 z
    rwa [mul_one, one_smul] at h
  simp only [contactSet, Set.mem_setOf_eq]
  constructor
  · intro hγc
    refine ⟨γ⁻¹ • z, ?_, smul_inv_smul γ z⟩
    rw [mem_dirichletDomain]
    intro δ
    rw [h1, hkey γ δ z, hγc]
    exact Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γ * δ, rfl⟩)
  · rintro ⟨x, hx, rfl⟩
    change dist (γ • x) (γ • τ₀) = Metric.infDist (γ • x) (MulAction.orbit Γ τ₀)
    have he : dist (γ • x) (γ • τ₀) = dist x τ₀ := dist_smul γ _ _
    refine le_antisymm ?_
      (Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩))
    refine (Metric.le_infDist ⟨τ₀, MulAction.mem_orbit_self τ₀⟩).mpr ?_
    intro y hy
    obtain ⟨δ, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    have h2 := hkey γ⁻¹ δ x
    rw [inv_inv] at h2
    rw [he, h2]
    exact hx (γ⁻¹ * δ)

/-- **Local finiteness of the tiling**: some ball about any point meets only the tiles of
its contact elements, and is covered by them. The non-contact near conditions are strict and
survive on a neighborhood; the far conditions are discharged by the triangle inequality. -/
theorem exists_ball_inter_tiles_subset_contact (hΓ : IsFuchsianGroup Γ)
    (τ₀ z : UpperHalfPlane) :
    ∃ r : ℝ, 0 < r ∧
      (∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball z r).Nonempty →
        γ ∈ contactSet Γ τ₀ z) ∧
      (∀ w ∈ Metric.ball z r, ∃ γ ∈ contactSet Γ τ₀ z,
        w ∈ (γ • ·) '' dirichletDomain Γ τ₀) := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = Metric.infDist z (MulAction.orbit Γ τ₀) := ⟨_, rfl⟩
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall z (d + 2)).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  have hN : {γ : ↥Γ | dist z (γ • τ₀) ≤ d + 2}.Finite := by
    refine hfin1.subset ?_
    intro γ hγ
    refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hγ
  have hforce : ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∀ γ : ↥Γ, γ ∉ contactSet Γ τ₀ z → dist z (γ • τ₀) ≤ d + 2 →
        d + 2 * r < dist z (γ • τ₀)) →
      ∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball z r).Nonempty →
        γ ∈ contactSet Γ τ₀ z := by
    intro r hr hr1 hgap γ hmeets
    obtain ⟨w, hwT, hwB⟩ := hmeets
    by_contra hγc
    have hwcon : γ ∈ contactSet Γ τ₀ w :=
      (mem_contactSet_iff_mem_smul_dirichletDomain γ w).mpr hwT
    simp only [contactSet, Set.mem_setOf_eq] at hwcon
    have h2 : Metric.infDist w (MulAction.orbit Γ τ₀) ≤ d + dist w z := by
      rw [hddef]
      exact Metric.infDist_le_infDist_add_dist
    have h3 : dist w z < r := Metric.mem_ball.mp hwB
    have h4 : dist z (γ • τ₀) ≤ dist z w + dist w (γ • τ₀) := dist_triangle _ _ _
    have h5 : dist z w = dist w z := dist_comm _ _
    have h6 : dist z (γ • τ₀) < d + 2 * r := by
      rw [hwcon] at h4
      linarith
    have h7 := hgap γ hγc (by linarith)
    linarith
  have hcover : ∀ r : ℝ,
      (∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball z r).Nonempty →
        γ ∈ contactSet Γ τ₀ z) →
      ∀ w ∈ Metric.ball z r, ∃ γ ∈ contactSet Γ τ₀ z,
        w ∈ (γ • ·) '' dirichletDomain Γ τ₀ := by
    intro r ha w hw
    obtain ⟨δ, hδ⟩ := exists_smul_mem_dirichletDomain hΓ τ₀ w
    have hwT : w ∈ (δ⁻¹ • ·) '' dirichletDomain Γ τ₀ := ⟨δ • w, hδ, inv_smul_smul δ w⟩
    exact ⟨δ⁻¹, ha δ⁻¹ ⟨w, hwT, hw⟩, hwT⟩
  by_cases hNC : ({γ : ↥Γ | dist z (γ • τ₀) ≤ d + 2} \ contactSet Γ τ₀ z).Nonempty
  · obtain ⟨γs, hγsmem, hγsmin⟩ := Set.exists_min_image _
      (fun γ : ↥Γ => dist z (γ • τ₀)) (hN.subset Set.diff_subset) hNC
    have hle : d ≤ dist z (γs • τ₀) := by
      rw [hddef]
      exact Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γs, rfl⟩)
    have hne' : dist z (γs • τ₀) ≠ d := by
      intro h
      refine hγsmem.2 ?_
      simp only [contactSet, Set.mem_setOf_eq]
      rw [h, hddef]
    have hγsd : d < dist z (γs • τ₀) := lt_of_le_of_ne hle (Ne.symm hne')
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min ((dist z (γs • τ₀) - d) / 4) 1 := ⟨_, rfl⟩
    have hrpos : 0 < r := by
      rw [hrdef]
      exact lt_min (by linarith) one_pos
    have hr1 : r ≤ 1 := by
      rw [hrdef]
      exact min_le_right _ _
    have hgap : ∀ γ : ↥Γ, γ ∉ contactSet Γ τ₀ z → dist z (γ • τ₀) ≤ d + 2 →
        d + 2 * r < dist z (γ • τ₀) := by
      intro γ hγc hγn
      have hmin := hγsmin γ ⟨hγn, hγc⟩
      have h2r : r ≤ (dist z (γs • τ₀) - d) / 4 := by
        rw [hrdef]
        exact min_le_left _ _
      linarith
    exact ⟨r, hrpos, hforce r hrpos hr1 hgap,
      hcover r (hforce r hrpos hr1 hgap)⟩
  · have hgap : ∀ γ : ↥Γ, γ ∉ contactSet Γ τ₀ z → dist z (γ • τ₀) ≤ d + 2 →
        d + 2 * (1 / 2) < dist z (γ • τ₀) := by
      intro γ hγc hγn
      exact absurd ⟨γ, hγn, hγc⟩ hNC
    exact ⟨1 / 2, by norm_num, hforce (1 / 2) (by norm_num) (by norm_num) hgap,
      hcover (1 / 2) (hforce (1 / 2) (by norm_num) (by norm_num) hgap)⟩

/-- Any two contact elements of a point are related through a side: developing the point
into the domain along one contact element places it on the side of the quotient element. -/
theorem smul_mem_dirichletSideSet_of_contact_pair {γ δ : ↥Γ} {z : UpperHalfPlane}
    (hγ : γ ∈ contactSet Γ τ₀ z) (hδ : δ ∈ contactSet Γ τ₀ z) :
    γ⁻¹ • z ∈ dirichletSideSet Γ τ₀ (γ⁻¹ * δ) := by
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  simp only [contactSet, Set.mem_setOf_eq] at hγ hδ
  have hkey : ∀ β : ↥Γ, dist (γ⁻¹ • z) (β • τ₀) = dist z ((γ * β) • τ₀) := by
    intro β
    calc dist (γ⁻¹ • z) (β • τ₀) = dist (γ • γ⁻¹ • z) (γ • β • τ₀) :=
        (dist_smul γ _ _).symm
      _ = dist z ((γ * β) • τ₀) := by rw [smul_inv_smul, mul_smul]
  have h1 : dist (γ⁻¹ • z) τ₀ = dist z (γ • τ₀) := by
    have h := hkey 1
    rwa [mul_one, one_smul] at h
  refine ⟨?_, ?_⟩
  · rw [mem_dirichletDomain]
    intro β
    rw [h1, hkey β, hγ]
    exact Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γ * β, rfl⟩)
  · simp only [Set.mem_setOf_eq]
    rw [h1, hkey (γ⁻¹ * δ), mul_inv_cancel_left, hγ, hδ]

/-- A point lies in an open tile exactly when its contact elements are the translates of the
tile element by the stabilizer of the center. -/
theorem mem_smul_interior_iff_contactSet_eq (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (γ : ↥Γ) (z : UpperHalfPlane) :
    z ∈ (γ • ·) '' interior (dirichletDomain Γ τ₀) ↔
      contactSet Γ τ₀ z = {δ : ↥Γ | δ • τ₀ = γ • τ₀} := by
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hIeq := interior_dirichletDomain_eq hΓ hdense
  constructor
  · rintro ⟨u, hu, huz⟩
    have huz' : γ • u = z := huz
    subst huz'
    have huD : u ∈ dirichletDomain Γ τ₀ := interior_subset hu
    rw [hIeq] at hu
    simp only [Set.mem_setOf_eq] at hu
    have hγcon : γ ∈ contactSet Γ τ₀ (γ • u) :=
      (mem_contactSet_iff_mem_smul_dirichletDomain γ (γ • u)).mpr ⟨u, huD, rfl⟩
    ext δ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hδcon
      have hside := smul_mem_dirichletSideSet_of_contact_pair hγcon hδcon
      rw [inv_smul_smul] at hside
      have heq2 : dist u τ₀ = dist u ((γ⁻¹ * δ) • τ₀) := hside.2
      by_contra hne'
      have hmove : (γ⁻¹ * δ) • τ₀ ≠ τ₀ := by
        intro h
        apply hne'
        calc δ • τ₀ = γ • (γ⁻¹ * δ) • τ₀ := by rw [← mul_smul, mul_inv_cancel_left]
          _ = γ • τ₀ := by rw [h]
      exact absurd heq2 (ne_of_lt (hu _ hmove))
    · intro hδτ
      simp only [contactSet, Set.mem_setOf_eq]
      rw [hδτ]
      simpa only [contactSet, Set.mem_setOf_eq] using hγcon
  · intro hEq
    have hγcon : γ ∈ contactSet Γ τ₀ z := by
      rw [hEq]
      simp only [Set.mem_setOf_eq]
    obtain ⟨u, huD, huz⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain γ z).mp hγcon
    refine ⟨u, ?_, huz⟩
    have huz' : γ • u = z := huz
    rw [hIeq]
    simp only [Set.mem_setOf_eq]
    intro β hβ
    rcases lt_or_eq_of_le (huD β) with h | heq
    · exact h
    exfalso
    have hcon2 : (γ * β) ∈ contactSet Γ τ₀ z := by
      simp only [contactSet, Set.mem_setOf_eq]
      have e1 : dist z ((γ * β) • τ₀) = dist u (β • τ₀) := by
        rw [← huz', mul_smul]
        exact dist_smul γ u (β • τ₀)
      have e2 : dist z (γ • τ₀) = dist u τ₀ := by
        rw [← huz']
        exact dist_smul γ u τ₀
      have hγc' : dist z (γ • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀) := hγcon
      rw [e1, ← heq, ← e2, hγc']
    rw [hEq] at hcon2
    have hcon2' : (γ * β) • τ₀ = γ • τ₀ := hcon2
    have hβfix : β • τ₀ = τ₀ := by
      have h2 : γ • β • τ₀ = γ • τ₀ := by
        rw [← mul_smul]
        exact hcon2'
      exact (smul_left_cancel_iff γ).mp h2
    exact hβ hβfix

set_option maxHeartbeats 400000 in
-- The contact-cycle proof develops the full sphere/adjacency/walk apparatus in one
-- declaration; the default heartbeat budget does not cover its elaboration.
/-- **Contact cycle**: the pointed orbit points of the contact set of a point admit a cyclic
enumeration in which consecutive tiles meet arbitrarily close to the point, so that
consecutive contact elements are related by side pairings through the point. -/
theorem exists_contact_cycle (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (z : UpperHalfPlane) :
    ∃ (m : ℕ) (e : ℕ → ↥Γ), 0 < m ∧ (∀ k, e (k + m) = e k) ∧
      (∀ k, e k ∈ contactSet Γ τ₀ z) ∧
      (∀ γ ∈ contactSet Γ τ₀ z, ∃ k < m, γ • τ₀ = e k • τ₀) ∧
      (∀ k, ∀ r : ℝ, 0 < r → ∃ w ∈ Metric.ball z r, w ≠ z ∧
        w ∈ (e k • ·) '' dirichletDomain Γ τ₀ ∧
        w ∈ (e (k + 1) • ·) '' dirichletDomain Γ τ₀) := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hCfin := finite_contactSet hΓ τ₀ z
  obtain ⟨c₀, hc₀⟩ := nonempty_contactSet hΓ τ₀ z
  obtain ⟨r₄, hr₄pos, hr₄meets, hr₄cover⟩ :=
    exists_ball_inter_tiles_subset_contact hΓ τ₀ z
  -- a ball about the center inside the Dirichlet domain
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧
      Metric.ball τ₀ r₀ ⊆ dirichletDomain Γ τ₀ := by
    have hgen : ∀ b : ℝ, 0 < b →
        (∀ γ : ↥Γ, γ • τ₀ ≠ τ₀ → b ≤ dist τ₀ (γ • τ₀)) →
        Metric.ball τ₀ (b / 2) ⊆ dirichletDomain Γ τ₀ := by
      intro b hb hmove τ hτ
      have hτb : dist τ τ₀ < b / 2 := Metric.mem_ball.mp hτ
      intro γ
      by_cases hfix : γ • τ₀ = τ₀
      · rw [hfix]
      · have h1 := hmove γ hfix
        have h2 : dist τ₀ (γ • τ₀) ≤ dist τ₀ τ + dist τ (γ • τ₀) := dist_triangle _ _ _
        have h3 : dist τ₀ τ = dist τ τ₀ := dist_comm _ _
        linarith
    by_cases hA : (activeSides Γ τ₀ 0).Nonempty
    · obtain ⟨γm, hγm, hγmin⟩ := Set.exists_min_image _
        (fun γ : ↥Γ => dist τ₀ (γ • τ₀)) (finite_activeSides hΓ τ₀ 0) hA
      have hdm : 0 < dist τ₀ (γm • τ₀) := dist_pos.mpr (Ne.symm hγm.2)
      refine ⟨min (dist τ₀ (γm • τ₀)) 1 / 2, by positivity, hgen _ (by positivity) ?_⟩
      intro γ hγfix
      by_cases hγn : dist τ₀ (γ • τ₀) ≤ 2 * 0 + 1
      · exact le_trans (min_le_left _ _) (hγmin γ ⟨hγn, hγfix⟩)
      · have h1 : 1 < dist τ₀ (γ • τ₀) := by linarith [not_le.mp hγn]
        exact le_trans (min_le_right _ _) h1.le
    · refine ⟨1 / 2, by norm_num, hgen 1 one_pos ?_⟩
      intro γ hγfix
      by_contra hlt
      rw [not_le] at hlt
      exact hA ⟨γ, by linarith, hγfix⟩
  -- geodesic interpolation from `z` toward any point
  have hvert : ∀ u v : UpperHalfPlane, (u : ℂ).re = (v : ℂ).re → ∀ s : ℝ, 0 < s →
      s < dist u v → ∃ w : UpperHalfPlane, dist u w = s ∧ dist w v = dist u v - s := by
    intro u v hre s hs hsd
    have hd0 : 0 < dist u v := lt_trans hs hsd
    have hre' : u.re = v.re := by
      rw [← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_re, hre]
    have hd : dist u v = |Real.log u.im - Real.log v.im| := by
      rw [UpperHalfPlane.dist_of_re_eq hre', Real.dist_eq]
    obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = s / dist u v := ⟨_, rfl⟩
    have ht0 : 0 < t := htdef ▸ div_pos hs hd0
    have ht1 : t < 1 := by
      rw [htdef]
      exact (div_lt_one hd0).mpr hsd
    obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (1 - t) * Real.log u.im + t * Real.log v.im :=
      ⟨_, rfl⟩
    obtain ⟨w, hwdef⟩ : ∃ w : UpperHalfPlane,
        w = UpperHalfPlane.mk (((u : ℂ).re : ℂ) + (Real.exp X : ℝ) * Complex.I)
          (by
            simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
            exact Real.exp_pos X) := ⟨_, rfl⟩
    have hwcoe : (w : ℂ) = ((u : ℂ).re : ℂ) + (Real.exp X : ℝ) * Complex.I := by
      rw [hwdef]
    have hwre : w.re = u.re := by
      rw [← UpperHalfPlane.coe_re w, ← UpperHalfPlane.coe_re u, hwcoe]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
    have hwim : w.im = Real.exp X := by
      rw [← UpperHalfPlane.coe_im w, hwcoe]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    have hlogw : Real.log w.im = X := by rw [hwim, Real.log_exp]
    have hduw : dist u w = t * dist u v := by
      rw [UpperHalfPlane.dist_of_re_eq (by rw [hwre]), Real.dist_eq, hlogw, hXdef, hd]
      rw [show Real.log u.im - ((1 - t) * Real.log u.im + t * Real.log v.im)
          = t * (Real.log u.im - Real.log v.im) by ring]
      rw [abs_mul, abs_of_nonneg ht0.le]
    have hdwv : dist w v = (1 - t) * dist u v := by
      rw [UpperHalfPlane.dist_of_re_eq (by rw [hwre, hre']), Real.dist_eq, hlogw, hXdef, hd]
      rw [show (1 - t) * Real.log u.im + t * Real.log v.im - Real.log v.im
          = (1 - t) * (Real.log u.im - Real.log v.im) by ring]
      rw [abs_mul, abs_of_nonneg (by linarith)]
    refine ⟨w, ?_, ?_⟩
    · rw [hduw, htdef]
      field_simp
    · rw [hdwv, htdef]
      field_simp
  have hbetween : ∀ p : UpperHalfPlane, ∀ s : ℝ, 0 < s → s < dist z p →
      ∃ w : UpperHalfPlane, dist z w = s ∧ dist w p = dist z p - s := by
    intro p s hs hsd
    by_cases hre : (z : ℂ).re = (p : ℂ).re
    · exact hvert z p hre s hs hsd
    · have hren : (p : ℂ).re - (z : ℂ).re ≠ 0 := sub_ne_zero.mpr (Ne.symm hre)
      obtain ⟨cc, hccdef⟩ : ∃ cc : ℝ, cc = (Complex.normSq (p : ℂ) - Complex.normSq (z : ℂ))
          / (2 * ((p : ℂ).re - (z : ℂ).re)) := ⟨_, rfl⟩
      have hzim0 : 0 < (z : ℂ).im := by
        rw [UpperHalfPlane.coe_im]
        exact z.im_pos
      have hpim0 : 0 < (p : ℂ).im := by
        rw [UpperHalfPlane.coe_im]
        exact p.im_pos
      obtain ⟨Rc, hRcdef⟩ : ∃ Rc : ℝ,
          Rc = Real.sqrt (((z : ℂ).re - cc) ^ 2 + (z : ℂ).im ^ 2) := ⟨_, rfl⟩
      have hsum_pos : 0 < ((z : ℂ).re - cc) ^ 2 + (z : ℂ).im ^ 2 := by
        nlinarith [sq_nonneg ((z : ℂ).re - cc)]
      have hRcpos : 0 < Rc := by
        rw [hRcdef]
        exact Real.sqrt_pos.mpr hsum_pos
      have hcz : ((z : ℂ).re - cc) ^ 2 + (z : ℂ).im ^ 2 = Rc ^ 2 := by
        rw [hRcdef, Real.sq_sqrt hsum_pos.le]
      have hsame : ((p : ℂ).re - cc) ^ 2 + (p : ℂ).im ^ 2
          = ((z : ℂ).re - cc) ^ 2 + (z : ℂ).im ^ 2 := by
        have h2 : cc * (2 * ((p : ℂ).re - (z : ℂ).re))
            = Complex.normSq (p : ℂ) - Complex.normSq (z : ℂ) := by
          rw [hccdef]
          field_simp
        simp only [Complex.normSq_apply] at h2
        linear_combination -h2
      have hcp : ((p : ℂ).re - cc) ^ 2 + (p : ℂ).im ^ 2 = Rc ^ 2 := by
        rw [hsame]
        exact hcz
      have h2R : (0 : ℝ) < 2 * Rc := by linarith
      have hdet : ((Real.sqrt (2 * Rc))⁻¹ • !![(1 : ℝ), Rc - cc; -1, Rc + cc]).det = 1 := by
        rw [Matrix.det_smul, Matrix.det_fin_two_of]
        simp only [Fintype.card_fin]
        rw [inv_pow, Real.sq_sqrt h2R.le]
        rw [show (1 : ℝ) * (Rc + cc) - (Rc - cc) * (-1) = 2 * Rc by ring]
        exact inv_mul_cancel₀ h2R.ne'
      obtain ⟨g, hgdef⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
          g = ⟨(Real.sqrt (2 * Rc))⁻¹ • !![(1 : ℝ), Rc - cc; -1, Rc + cc], hdet⟩ := ⟨_, rfl⟩
      have hgmat : (g : Matrix (Fin 2) (Fin 2) ℝ)
          = (Real.sqrt (2 * Rc))⁻¹ • !![(1 : ℝ), Rc - cc; -1, Rc + cc] := by
        rw [hgdef]
      have hre0 : ∀ u : UpperHalfPlane, ((u : ℂ).re - cc) ^ 2 + (u : ℂ).im ^ 2 = Rc ^ 2 →
          ((g • u : UpperHalfPlane) : ℂ).re = 0 := by
        intro u hcirc
        have hqne : ((Real.sqrt (2 * Rc))⁻¹ : ℂ) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
          positivity
        have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply g u
        simp only [Algebra.algebraMap_self, RingHom.id_apply] at hcoe
        have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (Real.sqrt (2 * Rc))⁻¹ * 1 := by
          rw [hgmat]
          simp [Matrix.smul_apply]
        have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1
            = (Real.sqrt (2 * Rc))⁻¹ * (Rc - cc) := by
          rw [hgmat]
          simp [Matrix.smul_apply]
        have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (Real.sqrt (2 * Rc))⁻¹ * (-1) := by
          rw [hgmat]
          simp [Matrix.smul_apply]
        have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1
            = (Real.sqrt (2 * Rc))⁻¹ * (Rc + cc) := by
          rw [hgmat]
          simp [Matrix.smul_apply]
        rw [h00, h01, h10, h11] at hcoe
        push_cast at hcoe
        rw [show ((Real.sqrt (2 * Rc))⁻¹ : ℂ) * 1 * ↑u
            + (Real.sqrt (2 * Rc) : ℂ)⁻¹ * ((Rc : ℂ) - cc)
            = (Real.sqrt (2 * Rc) : ℂ)⁻¹ * (↑u + ((Rc : ℂ) - cc)) by ring] at hcoe
        rw [show ((Real.sqrt (2 * Rc))⁻¹ : ℂ) * (-1) * ↑u
            + (Real.sqrt (2 * Rc) : ℂ)⁻¹ * ((Rc : ℂ) + cc)
            = (Real.sqrt (2 * Rc) : ℂ)⁻¹ * (-↑u + ((Rc : ℂ) + cc)) by ring] at hcoe
        rw [mul_div_mul_left _ _ hqne] at hcoe
        rw [hcoe, Complex.div_re, ← add_div]
        have hnum : (↑u + ((Rc : ℂ) - cc)).re * (-↑u + ((Rc : ℂ) + cc)).re
            + (↑u + ((Rc : ℂ) - cc)).im * (-↑u + ((Rc : ℂ) + cc)).im = 0 := by
          simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
            Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
          nlinarith [hcirc]
        rw [hnum, zero_div]
      have disteq : ∀ a b : UpperHalfPlane, dist (g • a) (g • b) = dist a b :=
        fun a b => (isometry_smul UpperHalfPlane g).dist_eq a b
      obtain ⟨w', hw1, hw2⟩ := hvert (g • z) (g • p)
        (by rw [hre0 z hcz, hre0 p hcp]) s hs (by rw [disteq z p]; exact hsd)
      refine ⟨g⁻¹ • w', ?_, ?_⟩
      · calc dist z (g⁻¹ • w') = dist (g • z) (g • g⁻¹ • w') := (disteq _ _).symm
          _ = dist (g • z) w' := by rw [smul_inv_smul]
          _ = s := hw1
      · calc dist (g⁻¹ • w') p = dist (g • g⁻¹ • w') (g • p) := (disteq _ _).symm
          _ = dist w' (g • p) := by rw [smul_inv_smul]
          _ = dist (g • z) (g • p) - s := hw2
          _ = dist z p - s := by rw [disteq]
  -- hyperbolic spheres about `z` are euclidean circles
  have hsph_char : ∀ s : ℝ, 0 < s → ∀ w : UpperHalfPlane, dist w z = s ↔
      Complex.normSq ((w : ℂ) - (((z : ℂ).re : ℂ) + (z.im * Real.cosh s : ℝ) * Complex.I))
        = (z.im * Real.sinh s) ^ 2 := by
    intro s hs w
    have hzim : 0 < z.im := z.im_pos
    have hwim : 0 < w.im := w.im_pos
    have hcosh_eq : dist w z = s ↔ Real.cosh (dist w z) = Real.cosh s := by
      constructor
      · intro h
        rw [h]
      · intro h
        rcases lt_trichotomy (dist w z) s with hlt | heq | hgt
        · exfalso
          have h2 : Real.cosh (dist w z) < Real.cosh s := Real.cosh_lt_cosh.mpr
            (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hs.le]; exact hlt)
          linarith
        · exact heq
        · exfalso
          have h2 : Real.cosh s < Real.cosh (dist w z) := Real.cosh_lt_cosh.mpr
            (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hs.le]; exact hgt)
          linarith
    rw [hcosh_eq, UpperHalfPlane.cosh_dist, dist_eq_norm, Complex.sq_norm]
    have hexp : Complex.normSq ((w : ℂ)
        - (((z : ℂ).re : ℂ) + (z.im * Real.cosh s : ℝ) * Complex.I))
        = ((w : ℂ).re - (z : ℂ).re) ^ 2 + ((w : ℂ).im - z.im * Real.cosh s) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
      ring
    have hnsq : Complex.normSq ((w : ℂ) - (z : ℂ))
        = ((w : ℂ).re - (z : ℂ).re) ^ 2 + ((w : ℂ).im - (z : ℂ).im) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      ring
    rw [hexp, hnsq]
    have hch : Real.cosh s ^ 2 - Real.sinh s ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq s
    have hwim' : (w : ℂ).im = w.im := UpperHalfPlane.coe_im w
    have hzim' : (z : ℂ).im = z.im := UpperHalfPlane.coe_im z
    rw [hwim', hzim']
    constructor
    · intro h
      have h2 : ((w : ℂ).re - (z : ℂ).re) ^ 2 + (w.im - z.im) ^ 2
          = (Real.cosh s - 1) * (2 * w.im * z.im) := by
        have hne : (2 : ℝ) * w.im * z.im ≠ 0 := by positivity
        field_simp at h
        linarith
      linear_combination h2 + z.im ^ 2 * hch
    · intro h
      have h2 : ((w : ℂ).re - (z : ℂ).re) ^ 2 + (w.im - z.im) ^ 2
          = (Real.cosh s - 1) * (2 * w.im * z.im) := by
        linear_combination h - z.im ^ 2 * hch
      have hne : (2 : ℝ) * w.im * z.im ≠ 0 := by positivity
      rw [h2, mul_div_assoc, div_self hne]
      ring
  -- spheres about `z`: preconnected and nonempty
  have hsph_conn : ∀ s : ℝ, 0 < s →
      IsPreconnected {w : UpperHalfPlane | dist w z = s} ∧
      ∃ w : UpperHalfPlane, dist w z = s := by
    intro s hs
    have hzim : 0 < z.im := z.im_pos
    obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ,
        ζ = ((z : ℂ).re : ℂ) + (z.im * Real.cosh s : ℝ) * Complex.I := ⟨_, rfl⟩
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = z.im * Real.sinh s := ⟨_, rfl⟩
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact mul_pos hzim (Real.sinh_pos_iff.mpr hs)
    have hζim : ζ.im = z.im * Real.cosh s := by
      rw [hζdef]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    have hmemH : ∀ θ : ℝ, 0 < (ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I)).im := by
      intro θ
      have h1 : (ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I)).im
          = z.im * Real.cosh s + ρ * Real.sin θ := by
        rw [Complex.add_im, hζim]
        congr 1
        rw [Complex.mul_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        rw [Complex.exp_ofReal_mul_I_im]
      rw [h1, hρdef]
      have hsin : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
      have hcs : Real.cosh s - Real.sinh s = Real.exp (-s) := Real.cosh_sub_sinh s
      have hexp : 0 < Real.exp (-s) := Real.exp_pos _
      nlinarith [Real.sinh_pos_iff.mpr hs]
    have hcont : Continuous (fun θ : ℝ =>
        UpperHalfPlane.mk (ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I)) (hmemH θ)) := by
      rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.isInducing.continuous_iff]
      fun_prop
    have hsurj : ∀ w : UpperHalfPlane, Complex.normSq ((w : ℂ) - ζ) = ρ ^ 2 →
        ∃ θ : ℝ, (w : ℂ) = ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I) := by
      intro w hw
      have hnorm : ‖(w : ℂ) - ζ‖ = ρ := by
        have h1 : ‖(w : ℂ) - ζ‖ ^ 2 = ρ ^ 2 := by rw [Complex.sq_norm, hw]
        have h2 : (0 : ℝ) ≤ ‖(w : ℂ) - ζ‖ := norm_nonneg _
        nlinarith
      refine ⟨Complex.arg ((w : ℂ) - ζ), ?_⟩
      have h3 := Complex.norm_mul_exp_arg_mul_I ((w : ℂ) - ζ)
      rw [hnorm] at h3
      linear_combination -h3
    have hrange : {w : UpperHalfPlane | dist w z = s} = Set.range (fun θ : ℝ =>
        UpperHalfPlane.mk (ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I)) (hmemH θ)) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_range]
      rw [hsph_char s hs w, ← hζdef, ← hρdef]
      constructor
      · intro hw
        obtain ⟨θ, hθ⟩ := hsurj w hw
        exact ⟨θ, UpperHalfPlane.ext hθ.symm⟩
      · rintro ⟨θ, rfl⟩
        rw [show ((UpperHalfPlane.mk (ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I))
            (hmemH θ)) : ℂ) = ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I) from rfl]
        rw [show ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I) - ζ
            = (ρ : ℂ) * Complex.exp (θ * Complex.I) by ring]
        rw [Complex.normSq_mul]
        have h1 : Complex.normSq ((ρ : ℝ) : ℂ) = ρ ^ 2 := by
          rw [Complex.normSq_ofReal]
          ring
        have h2 : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
          rw [← Complex.sq_norm, Complex.norm_exp_ofReal_mul_I]
          norm_num
        rw [h1, h2, mul_one]
    constructor
    · rw [hrange]
      exact (isConnected_range hcont).isPreconnected
    · have hmem : (UpperHalfPlane.mk (ζ + (ρ : ℂ) * Complex.exp ((0 : ℝ) * Complex.I))
          (hmemH 0)) ∈ Set.range (fun θ : ℝ =>
          UpperHalfPlane.mk (ζ + (ρ : ℂ) * Complex.exp (θ * Complex.I)) (hmemH θ)) :=
        ⟨0, rfl⟩
      rw [← hrange] at hmem
      exact ⟨_, hmem⟩
  have hsph_ne : ∀ s : ℝ, 0 < s → ∃ w : UpperHalfPlane, dist w z = s :=
    fun s hs => (hsph_conn s hs).2
  -- every contact tile meets every small sphere about `z`
  obtain ⟨s0, hs0pos, hs0r₄, htiles⟩ : ∃ s0 : ℝ, 0 < s0 ∧ s0 ≤ r₄ ∧
      ∀ s : ℝ, 0 < s → s < s0 → ∀ γ ∈ contactSet Γ τ₀ z,
        ∃ w : UpperHalfPlane, dist w z = s ∧ w ∈ (γ • ·) '' dirichletDomain Γ τ₀ := by
    have hR0 : (0 : ℝ) ≤ R := le_trans Metric.infDist_nonneg (hdense z)
    by_cases hd0 : Metric.infDist z (MulAction.orbit Γ τ₀) = 0
    · refine ⟨min (min r₄ (R + 1)) r₀, lt_min (lt_min hr₄pos (by linarith)) hr₀pos,
        le_trans (min_le_left _ _) (min_le_left _ _), ?_⟩
      intro s hs hslt γ hγ
      have hγc : dist z (γ • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀) := hγ
      have hγz : γ • τ₀ = z := by
        have h1 : dist z (γ • τ₀) = 0 := by rw [hγc, hd0]
        exact (dist_eq_zero.mp h1).symm
      obtain ⟨w, hw⟩ := hsph_ne s hs
      refine ⟨w, hw, γ⁻¹ • w, ?_, smul_inv_smul γ w⟩
      apply hr₀sub
      rw [Metric.mem_ball]
      have h2 : dist (γ⁻¹ • w) τ₀ = dist w (γ • τ₀) := by
        calc dist (γ⁻¹ • w) τ₀ = dist (γ • γ⁻¹ • w) (γ • τ₀) := (dist_smul γ _ _).symm
          _ = dist w (γ • τ₀) := by rw [smul_inv_smul]
      rw [h2, hγz, hw]
      calc s < min (min r₄ (R + 1)) r₀ := hslt
        _ ≤ r₀ := min_le_right _ _
    · have hdpos : 0 < Metric.infDist z (MulAction.orbit Γ τ₀) :=
        lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hd0)
      refine ⟨min (min r₄ (R + 1)) (Metric.infDist z (MulAction.orbit Γ τ₀)),
        lt_min (lt_min hr₄pos (by linarith)) hdpos,
        le_trans (min_le_left _ _) (min_le_left _ _), ?_⟩
      intro s hs hslt γ hγ
      have hγc : dist z (γ • τ₀) = Metric.infDist z (MulAction.orbit Γ τ₀) := hγ
      have hsd : s < dist z (γ • τ₀) := by
        rw [hγc]
        exact lt_of_lt_of_le hslt (min_le_right _ _)
      obtain ⟨w, hw1, hw2⟩ := hbetween (γ • τ₀) s hs hsd
      refine ⟨w, by rw [dist_comm]; exact hw1, ?_⟩
      rw [← mem_contactSet_iff_mem_smul_dirichletDomain]
      simp only [contactSet, Set.mem_setOf_eq]
      have hwlb : ∀ y ∈ MulAction.orbit Γ τ₀, dist z (γ • τ₀) - s ≤ dist w y := by
        intro y hy
        have h1 : Metric.infDist z (MulAction.orbit Γ τ₀) ≤ dist z y :=
          Metric.infDist_le_dist_of_mem hy
        have h2 : dist z y ≤ dist z w + dist w y := dist_triangle _ _ _
        rw [← hγc] at h1
        linarith [hw1]
      refine le_antisymm ?_
        (Metric.infDist_le_dist_of_mem (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩))
      rw [hw2]
      exact (Metric.le_infDist ⟨τ₀, MulAction.mem_orbit_self τ₀⟩).mpr hwlb
  -- tiles are closed
  have htileclosed : ∀ γ : ↥Γ, IsClosed ((γ • ·) '' dirichletDomain Γ τ₀) := by
    intro γ
    have heq : (γ • ·) '' dirichletDomain Γ τ₀ = (γ⁻¹ • ·) ⁻¹' dirichletDomain Γ τ₀ := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [inv_smul_smul] using hx
      · intro hw
        exact ⟨γ⁻¹ • w, hw, smul_inv_smul γ w⟩
    rw [heq]
    have hcont : Continuous (fun w : UpperHalfPlane => γ⁻¹ • w) := by
      have h1 : ∀ w : UpperHalfPlane, γ⁻¹ • w
          = ((γ⁻¹ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • w := fun w => rfl
      simp only [h1]
      exact (isometry_smul UpperHalfPlane
        ((γ⁻¹ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)).continuous
    exact (isClosed_dirichletDomain Γ τ₀).preimage hcont
  -- the scale-`n` contact adjacency edge sets, and a pigeonholed stable edge set
  obtain ⟨Es, hEsdef⟩ : ∃ Es : ℕ → Finset (↥Γ × ↥Γ),
      Es = fun n : ℕ => (hCfin.toFinset ×ˢ hCfin.toFinset).filter (fun q : ↥Γ × ↥Γ =>
        (((q.1 • ·) '' dirichletDomain Γ τ₀) ∩ ((q.2 • ·) '' dirichletDomain Γ τ₀) ∩
          {w : UpperHalfPlane | dist w z = s0 / ((n : ℝ) + 2)}).Nonempty) := ⟨_, rfl⟩
  have hsn_pos : ∀ n : ℕ, 0 < s0 / ((n : ℝ) + 2) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact div_pos hs0pos h1
  have hsn_lt : ∀ n : ℕ, s0 / ((n : ℝ) + 2) < s0 := by
    intro n
    have h1 : (1 : ℝ) < (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    exact div_lt_self hs0pos h1
  have hEs_mem : ∀ (n : ℕ) (a b : ↥Γ), (a, b) ∈ Es n ↔
      (a ∈ contactSet Γ τ₀ z ∧ b ∈ contactSet Γ τ₀ z) ∧
      (((a • ·) '' dirichletDomain Γ τ₀) ∩ ((b • ·) '' dirichletDomain Γ τ₀) ∩
        {w : UpperHalfPlane | dist w z = s0 / ((n : ℝ) + 2)}).Nonempty := by
    intro n a b
    rw [hEsdef]
    simp only [Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset]
  obtain ⟨E, hE⟩ : ∃ E : Finset (↥Γ × ↥Γ), {n : ℕ | Es n = E}.Infinite := by
    have hsub : ∀ n, Es n ⊆ hCfin.toFinset ×ˢ hCfin.toFinset := by
      intro n
      rw [hEsdef]
      exact Finset.filter_subset _ _
    obtain ⟨E, hE⟩ := Finite.exists_infinite_fiber
      (fun n : ℕ => (⟨Es n, Finset.mem_powerset.mpr (hsub n)⟩ :
        ↥((hCfin.toFinset ×ˢ hCfin.toFinset).powerset)))
    refine ⟨E.1, ?_⟩
    have h2 : {n : ℕ | Es n = E.1} ⊇ (fun n : ℕ =>
        (⟨Es n, Finset.mem_powerset.mpr (hsub n)⟩ :
          ↥((hCfin.toFinset ×ˢ hCfin.toFinset).powerset))) ⁻¹' {E} := by
      intro n hn
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
      simp only [Set.mem_setOf_eq]
      rw [← hn]
    exact (Set.infinite_coe_iff.mp hE).mono h2
  obtain ⟨n₀, hn₀⟩ := hE.nonempty
  have hn₀' : Es n₀ = E := hn₀
  have hdiagE : ∀ a ∈ contactSet Γ τ₀ z, (a, a) ∈ E := by
    intro a ha
    rw [← hn₀', hEs_mem]
    obtain ⟨w, hw1, hw2⟩ := htiles (s0 / (n₀ + 2)) (hsn_pos n₀) (hsn_lt n₀) a ha
    exact ⟨⟨ha, ha⟩, ⟨w, ⟨hw2, hw2⟩, hw1⟩⟩
  have hadjE : ∀ a b : ↥Γ, (a, b) ∈ E → ∀ r : ℝ, 0 < r →
      ∃ w ∈ Metric.ball z r, w ≠ z ∧ w ∈ (a • ·) '' dirichletDomain Γ τ₀ ∧
        w ∈ (b • ·) '' dirichletDomain Γ τ₀ := by
    intro a b hab r hr
    obtain ⟨n, hn, hngt⟩ := hE.exists_gt ⌈s0 / r⌉₊
    have hslt : s0 / ((n : ℝ) + 2) < r := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
      have h1 : s0 / r ≤ (⌈s0 / r⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈s0 / r⌉₊ : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hngt
      have h3 : s0 / r < (n : ℝ) + 2 := by linarith
      have h4 : s0 = s0 / r * r := (div_mul_cancel₀ s0 hr.ne').symm
      calc s0 = s0 / r * r := h4
        _ < ((n : ℝ) + 2) * r := mul_lt_mul_of_pos_right h3 hr
        _ = r * ((n : ℝ) + 2) := mul_comm _ _
    have hEn : Es n = E := hn
    rw [← hEn, hEs_mem] at hab
    obtain ⟨-, ⟨w, ⟨⟨hwa, hwb⟩, hwS⟩⟩⟩ := hab
    have hwz : dist w z = s0 / (n + 2) := hwS
    refine ⟨w, ?_, ?_, hwa, hwb⟩
    · rw [Metric.mem_ball, hwz]
      exact hslt
    · intro hwzeq
      rw [hwzeq, dist_self] at hwz
      exact (hsn_pos n).ne' hwz.symm
  have hsymmE : ∀ a b : ↥Γ, (a, b) ∈ E → (b, a) ∈ E := by
    intro a b hab
    rw [← hn₀', hEs_mem] at hab ⊢
    obtain ⟨⟨ha, hb⟩, ⟨w, ⟨⟨hwa, hwb⟩, hwS⟩⟩⟩ := hab
    exact ⟨⟨hb, ha⟩, ⟨w, ⟨hwb, hwa⟩, hwS⟩⟩
  -- the adjacency relation and reachability
  obtain ⟨RR, hRRdef⟩ : ∃ RR : ↥Γ → ↥Γ → Prop, RR = fun a b =>
      a ∈ contactSet Γ τ₀ z ∧ b ∈ contactSet Γ τ₀ z ∧ (a, b) ∈ E := ⟨_, rfl⟩
  have hRRsymm : ∀ a b : ↥Γ, RR a b → RR b a := by
    simp only [hRRdef]
    exact fun a b h => ⟨h.2.1, h.1, hsymmE a b h.2.2⟩
  have hRRdiag : ∀ a ∈ contactSet Γ τ₀ z, RR a a := by
    simp only [hRRdef]
    exact fun a ha => ⟨ha, ha, hdiagE a ha⟩
  have hRRC : ∀ a b : ↥Γ, RR a b → a ∈ contactSet Γ τ₀ z ∧ b ∈ contactSet Γ τ₀ z := by
    simp only [hRRdef]
    exact fun a b h => ⟨h.1, h.2.1⟩
  have hreach : ∀ γ ∈ contactSet Γ τ₀ z, Relation.ReflTransGen RR c₀ γ := by
    by_contra hcon
    simp only [not_forall] at hcon
    obtain ⟨δ₀, hδ₀C, hδ₀n⟩ := hcon
    have hconnS := (hsph_conn (s0 / (n₀ + 2)) (hsn_pos n₀)).1
    obtain ⟨A, hAdef⟩ : ∃ A : Set UpperHalfPlane, A = ⋃ γ ∈ {γ : ↥Γ |
        γ ∈ contactSet Γ τ₀ z ∧ Relation.ReflTransGen RR c₀ γ},
        (γ • ·) '' dirichletDomain Γ τ₀ := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : Set UpperHalfPlane, B = ⋃ γ ∈ {γ : ↥Γ |
        γ ∈ contactSet Γ τ₀ z ∧ ¬Relation.ReflTransGen RR c₀ γ},
        (γ • ·) '' dirichletDomain Γ τ₀ := ⟨_, rfl⟩
    have hAclosed : IsClosed A := by
      rw [hAdef]
      exact Set.Finite.isClosed_biUnion (hCfin.subset fun γ h => h.1)
        (fun γ _ => htileclosed γ)
    have hBclosed : IsClosed B := by
      rw [hBdef]
      exact Set.Finite.isClosed_biUnion (hCfin.subset fun γ h => h.1)
        (fun γ _ => htileclosed γ)
    have hcover : {w : UpperHalfPlane | dist w z = s0 / (n₀ + 2)} ⊆ A ∪ B := by
      intro w hwS
      have hwball : w ∈ Metric.ball z r₄ := by
        rw [Metric.mem_ball]
        have h1 : dist w z = s0 / (n₀ + 2) := hwS
        rw [h1]
        exact lt_of_lt_of_le (hsn_lt n₀) hs0r₄
      obtain ⟨γ, hγC, hwT⟩ := hr₄cover w hwball
      by_cases hγr : Relation.ReflTransGen RR c₀ γ
      · left
        rw [hAdef]
        exact Set.mem_biUnion ⟨hγC, hγr⟩ hwT
      · right
        rw [hBdef]
        exact Set.mem_biUnion ⟨hγC, hγr⟩ hwT
    have hAne : ({w : UpperHalfPlane | dist w z = s0 / (n₀ + 2)} ∩ A).Nonempty := by
      obtain ⟨w, hw1, hw2⟩ := htiles (s0 / (n₀ + 2)) (hsn_pos n₀) (hsn_lt n₀) c₀ hc₀
      refine ⟨w, hw1, ?_⟩
      rw [hAdef]
      exact Set.mem_biUnion ⟨hc₀, Relation.ReflTransGen.refl⟩ hw2
    have hBne : ({w : UpperHalfPlane | dist w z = s0 / (n₀ + 2)} ∩ B).Nonempty := by
      obtain ⟨w, hw1, hw2⟩ := htiles (s0 / (n₀ + 2)) (hsn_pos n₀) (hsn_lt n₀) δ₀ hδ₀C
      refine ⟨w, hw1, ?_⟩
      rw [hBdef]
      exact Set.mem_biUnion ⟨hδ₀C, hδ₀n⟩ hw2
    obtain ⟨w, hwS, hwA, hwB⟩ :=
      isPreconnected_closed_iff.mp hconnS A B hAclosed hBclosed hcover hAne hBne
    rw [hAdef] at hwA
    rw [hBdef] at hwB
    obtain ⟨γ, hγmem, hwγ⟩ := Set.mem_iUnion₂.mp hwA
    obtain ⟨δ, hδmem, hwδ⟩ := Set.mem_iUnion₂.mp hwB
    have hedge : (γ, δ) ∈ E := by
      rw [← hn₀', hEs_mem]
      exact ⟨⟨hγmem.1, hδmem.1⟩, ⟨w, ⟨hwγ, hwδ⟩, hwS⟩⟩
    have hRRγδ : RR γ δ := by
      rw [hRRdef]
      exact ⟨hγmem.1, hδmem.1, hedge⟩
    exact hδmem.2 (Relation.ReflTransGen.tail hγmem.2 hRRγδ)
  -- the closed walk through all contact elements
  have hchainmem : ∀ (a : ↥Γ) (l' : List ↥Γ), List.IsChain RR (a :: l') →
      ∀ x ∈ l', x ∈ contactSet Γ τ₀ z := by
    intro a l'
    induction l' generalizing a with
    | nil =>
      intro _ x hx
      cases hx
    | cons b rest ih =>
      intro hch x hx
      have h1 : RR a b ∧ List.IsChain RR (b :: rest) := List.isChain_cons_cons.mp hch
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact (hRRC _ _ h1.1).2
      · exact ih b h1.2 x hx'
  have hwalk : ∀ L : List ↥Γ, (∀ γ ∈ L, γ ∈ contactSet Γ τ₀ z) →
      ∃ W : List ↥Γ, W ≠ [] ∧ W.head? = some c₀ ∧ W.getLast? = some c₀ ∧
        List.IsChain RR W ∧ (∀ x ∈ W, x ∈ contactSet Γ τ₀ z) ∧ ∀ γ ∈ L, γ ∈ W := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨[c₀], by simp, by simp, by simp, List.IsChain.singleton _, ?_, by simp⟩
      intro x hx
      rw [List.mem_singleton] at hx
      rw [hx]
      exact hc₀
    | cons γ rest ih =>
      intro hL
      obtain ⟨W, hWne, hWhead, hWlast, hWchain, hWC, hWcov⟩ :=
        ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      have hγC : γ ∈ contactSet Γ τ₀ z := hL γ List.mem_cons_self
      obtain ⟨l, hlchain, hllast⟩ :=
        List.exists_isChain_cons_of_relationReflTransGen (hreach γ hγC)
      have hlmem : ∀ x ∈ (c₀ :: l), x ∈ contactSet Γ τ₀ z := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hc₀
        · exact hchainmem c₀ l hlchain x hx'
      have hrevne : (c₀ :: l).reverse ≠ [] := by simp
      have hPchain : List.IsChain RR ((c₀ :: l) ++ (c₀ :: l).reverse) := by
        refine List.IsChain.append hlchain ?_ ?_
        · exact List.isChain_reverse.mpr (hlchain.imp fun a b h => hRRsymm a b h)
        · intro x hx y hy
          rw [List.getLast?_eq_some_getLast (List.cons_ne_nil c₀ l)] at hx
          rw [Option.mem_some_iff] at hx
          rw [List.head?_reverse,
            List.getLast?_eq_some_getLast (List.cons_ne_nil c₀ l)] at hy
          rw [Option.mem_some_iff] at hy
          rw [← hx, ← hy, hllast]
          exact hRRdiag γ hγC
      refine ⟨((c₀ :: l) ++ (c₀ :: l).reverse) ++ W, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.head?_append_of_ne_nil _ (by simp)]
        rw [List.head?_append_of_ne_nil _ (by simp)]
        simp
      · rw [List.getLast?_append_of_ne_nil _ hWne]
        exact hWlast
      · refine List.IsChain.append hPchain hWchain ?_
        intro x hx y hy
        rw [List.getLast?_append_of_ne_nil _ hrevne, List.getLast?_reverse] at hx
        simp only [List.head?_cons, Option.mem_some_iff] at hx
        rw [hWhead, Option.mem_some_iff] at hy
        rw [← hx, ← hy]
        exact hRRdiag c₀ hc₀
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · rcases List.mem_append.mp h1 with h3 | h4
          · exact hlmem x h3
          · exact hlmem x (List.mem_reverse.mp h4)
        · exact hWC x h2
      · intro γ' hγ'
        rcases List.mem_cons.mp hγ' with rfl | hγ''
        · have hγin : γ' ∈ (c₀ :: l) := by
            rw [← hllast]
            exact List.getLast_mem _
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hγin)))
        · exact List.mem_append.mpr (Or.inr (hWcov γ' hγ''))
  obtain ⟨W, hWne, hWhead, hWlast, hWchain, hWC, hWcov⟩ :=
    hwalk hCfin.toFinset.toList (fun γ h =>
      (Set.Finite.mem_toFinset hCfin).mp (Finset.mem_toList.mp h))
  have hm : 0 < W.length := List.length_pos_iff.mpr hWne
  -- cyclic adjacency along the walk
  have hcyc : ∀ k : ℕ, RR ((W[k % W.length]?).getD c₀) ((W[(k + 1) % W.length]?).getD c₀) := by
    intro k
    have hj : k % W.length < W.length := Nat.mod_lt k hm
    have hstep : (k + 1) % W.length = (k % W.length + 1) % W.length := by
      rw [Nat.mod_add_mod]
    by_cases hjm : k % W.length + 1 < W.length
    · have h2 : (k + 1) % W.length = k % W.length + 1 := by
        rw [hstep]
        exact Nat.mod_eq_of_lt hjm
      rw [h2, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjm,
        Option.getD_some, Option.getD_some]
      exact List.isChain_iff_getElem.mp hWchain (k % W.length) hjm
    · have hje : k % W.length + 1 = W.length := by omega
      have h2 : (k + 1) % W.length = 0 := by
        rw [hstep, hje, Nat.mod_self]
      rw [h2, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hm,
        Option.getD_some, Option.getD_some]
      have hlast : W[k % W.length] = c₀ := by
        have h3 : W.getLast hWne = c₀ := by
          rw [List.getLast?_eq_some_getLast hWne, Option.some_inj] at hWlast
          exact hWlast
        rw [← h3, List.getLast_eq_getElem]
        congr 1
        omega
      have hhead : W[0] = c₀ := by
        have h4 : W.head hWne = c₀ := by
          rw [List.head?_eq_some_head hWne, Option.some_inj] at hWhead
          exact hWhead
        rw [← h4, List.head_eq_getElem]
      rw [hlast, hhead]
      exact hRRdiag c₀ hc₀
  -- assemble
  refine ⟨W.length, fun k => (W[k % W.length]?).getD c₀, hm, ?_, ?_, ?_, ?_⟩
  · intro k
    exact congrArg (fun j => (W[j]?).getD c₀) (Nat.add_mod_right k W.length)
  · intro k
    have hj : k % W.length < W.length := Nat.mod_lt k hm
    change (W[k % W.length]?).getD c₀ ∈ contactSet Γ τ₀ z
    rw [List.getElem?_eq_getElem hj, Option.getD_some]
    exact hWC _ (List.getElem_mem hj)
  · intro γ hγ
    have hγW : γ ∈ W := hWcov γ (by
      rw [Finset.mem_toList, Set.Finite.mem_toFinset]
      exact hγ)
    obtain ⟨i, hi, hWi⟩ := List.mem_iff_getElem.mp hγW
    refine ⟨i, hi, ?_⟩
    have hei : (W[i % W.length]?).getD c₀ = γ := by
      rw [Nat.mod_eq_of_lt hi, List.getElem?_eq_getElem hi, Option.getD_some, hWi]
    exact (congrArg (· • τ₀) hei).symm
  · intro k r hr
    have hRRk := hcyc k
    rw [hRRdef] at hRRk
    exact hadjE _ _ hRRk.2.2 r hr

end RiemannDynamics
