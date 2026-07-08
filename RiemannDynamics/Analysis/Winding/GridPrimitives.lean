/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Winding.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import RMT4.has_sqrt

/-!
# Primitives on domains with no bounded complementary components

Every holomorphic function on an open set `T ⊆ ℂ` all of whose complementary
components are unbounded has primitives (`has_primitives T`, in the sense of
the vendored Riemann-mapping development). This is the plane form of "the
sphere complement of `T` is connected", and it is the input that unlocks the
Riemann mapping theorem for such domains.

The construction is a grid integral: fix a scale `δ` and integrate along
axis-parallel lattice paths. Well-definedness reduces to the vanishing of
grid-loop integrals, which follows from a purely combinatorial
**edge-counting identity** — a grid-loop integral equals the sum over lattice
squares of the square-boundary integrals weighted by the winding numbers of
the loop about the square centers, because on both sides the coefficient of
a directed edge is the same: the winding difference across the edge equals
its net signed traversal count. Squares carrying nonzero winding have their
closed squares inside `T` (a complementary point there would lie in a
bounded pocket of the winding region, whose frontier is on the loop — the
**escape argument**), so each square term vanishes by the rectangle Cauchy
theorem, and the loop integral is zero. The derivative of the resulting
primitive is computed on small rectangles.
-/

open Complex Set unitInterval

namespace RiemannDynamics

/-- The line-segment contour integral from `a` to `b`. -/
noncomputable def segmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (b - a) * f (a + t • (b - a))

/-- The lattice point of the `δ`-grid indexed by `p : ℤ × ℤ`. -/
def gridPoint (δ : ℝ) (p : ℤ × ℤ) : ℂ :=
  δ * (p.1 + p.2 * Complex.I)

/-- Two lattice indices are adjacent when they differ by one unit step in
exactly one coordinate. -/
def GridAdj (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1) ∨ ((p.1 - q.1).natAbs = 1 ∧ p.2 = q.2)

/-- A grid path: a list of pairwise-consecutively adjacent lattice indices. -/
def IsGridPath (L : List (ℤ × ℤ)) : Prop :=
  L.Chain' GridAdj

/-- The integral of `f` along the `δ`-realization of a grid path. -/
noncomputable def gridPathIntegral (f : ℂ → ℂ) (δ : ℝ) :
    List (ℤ × ℤ) → ℂ
  | [] => 0
  | [_] => 0
  | p :: q :: L =>
      segmentIntegral f (gridPoint δ p) (gridPoint δ q) +
        gridPathIntegral f δ (q :: L)

/-- The `δ`-realization of a grid path as a set: the union of its closed
segments. -/
def gridPathTrace (δ : ℝ) : List (ℤ × ℤ) → Set ℂ
  | [] => ∅
  | [p] => {gridPoint δ p}
  | p :: q :: L =>
      segment ℝ (gridPoint δ p) (gridPoint δ q) ∪ gridPathTrace δ (q :: L)

/-- The closed `δ`-square with lower-left lattice corner `p`. -/
def gridSquare (δ : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | z.re ∈ Set.Icc (δ * p.1) (δ * (p.1 + 1)) ∧
    z.im ∈ Set.Icc (δ * p.2) (δ * (p.2 + 1))}

/-- The center of the `δ`-square with lower-left corner `p`. -/
noncomputable def gridSquareCenter (δ : ℝ) (p : ℤ × ℤ) : ℂ :=
  gridPoint δ p + (δ / 2) * (1 + Complex.I)

/-- The boundary contour integral of `f` around the `δ`-square at `p`,
traversed counterclockwise. -/
noncomputable def gridSquareBoundaryIntegral (f : ℂ → ℂ) (δ : ℝ)
    (p : ℤ × ℤ) : ℂ :=
  gridPathIntegral f δ
    [p, (p.1 + 1, p.2), (p.1 + 1, p.2 + 1), (p.1, p.2 + 1), p]

/-- The affine segment from `a` to `b` as a path. -/
noncomputable def segmentPath (a b : ℂ) : Path a b where
  toFun t := a + ((t : ℝ) : ℂ) * (b - a)
  continuous_toFun := by
    exact continuous_const.add ((Complex.continuous_ofReal.comp
      continuous_subtype_val).mul continuous_const)
  source' := by simp
  target' := by simp

/-- The last vertex of a grid path with a given head, structurally. -/
def gridLast : (ℤ × ℤ) → List (ℤ × ℤ) → ℤ × ℤ
  | p, [] => p
  | _, q :: L => gridLast q L

/-- The piecewise-linear realization of a grid path from a head vertex,
folding segment paths by concatenation. -/
noncomputable def gridPathRealize (δ : ℝ) :
    (p : ℤ × ℤ) → (L : List (ℤ × ℤ)) →
      Path (gridPoint δ p) (gridPoint δ (gridLast p L))
  | _, [] => Path.refl _
  | p, q :: L => (segmentPath (gridPoint δ p) (gridPoint δ q)).trans
      (gridPathRealize δ q L)

/-- A grid path realizes as a continuous curve on the unit interval (the
empty path realizes as the constant curve at the origin's lattice point). -/
noncomputable def gridLoopCurve (δ : ℝ) (L : List (ℤ × ℤ)) : C(I, ℂ) :=
  match L with
  | [] => ContinuousMap.const I (gridPoint δ (0, 0))
  | p :: L => (gridPathRealize δ p L).toContinuousMap

/-- The realization of a nonempty closed grid path is a closed curve
starting and ending at its head vertex. -/
theorem gridLoopCurve_closed {δ : ℝ} {L : List (ℤ × ℤ)}
    (hne : L ≠ []) (hcl : L.head? = L.getLast?) :
    gridLoopCurve δ L 0 = gridLoopCurve δ L 1 := by
  obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hlast : ∀ (r : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (r :: M).getLast? = some (gridLast r M) := by
    intro r M
    induction M generalizing r with
    | nil => simp [gridLast]
    | cons q M ih =>
      rw [List.getLast?_cons_cons, ih]
      rfl
  have hp : p = gridLast p L' := by
    have h := hcl
    rw [List.head?_cons, hlast] at h
    exact Option.some.inj h
  have h0 : gridLoopCurve δ (p :: L') 0 = gridPoint δ p :=
    (gridPathRealize δ p L').source
  have h1 : gridLoopCurve δ (p :: L') 1 = gridPoint δ (gridLast p L') :=
    (gridPathRealize δ p L').target
  rw [h0, h1, ← hp]

/-- The realization's range is the grid-path trace. -/
theorem range_gridLoopCurve {δ : ℝ} (hδ : 0 < δ) {L : List (ℤ × ℤ)}
    (hL : IsGridPath L) (hne : L ≠ []) :
    Set.range (gridLoopCurve δ L) = gridPathTrace δ L := by
  obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hseg : ∀ a b : ℂ, Set.range (segmentPath a b) = segment ℝ a b := by
    intro a b
    have h1 : ⇑(segmentPath a b)
        = (fun θ : ℝ => a + θ • (b - a)) ∘ ((↑) : I → ℝ) := by
      funext t
      show a + ((t : ℝ) : ℂ) * (b - a) = a + (t : ℝ) • (b - a)
      rw [Complex.real_smul]
    rw [h1, Set.range_comp, Subtype.range_coe]
    exact (segment_eq_image' ℝ a b).symm
  have key : ∀ (r : ℤ × ℤ) (M : List (ℤ × ℤ)),
      Set.range (gridPathRealize δ r M) = gridPathTrace δ (r :: M) := by
    intro r M
    induction M generalizing r with
    | nil =>
      show Set.range (Path.refl (gridPoint δ r)) = ({gridPoint δ r} : Set ℂ)
      exact Path.refl_range
    | cons q M ih =>
      show Set.range ((segmentPath (gridPoint δ r) (gridPoint δ q)).trans
          (gridPathRealize δ q M)) = _
      rw [Path.trans_range, hseg, ih]
      rfl
  exact key p L'

/-- **Edge-counting identity.** The integral of any function along a closed
grid loop equals the winding-weighted sum of square-boundary integrals over
the squares of nonzero winding: on both sides the coefficient of each
directed edge is the net signed traversal count, which equals the winding
difference of the two adjacent squares. The sum is finite because the
winding region is bounded. -/
theorem gridPathIntegral_eq_sum_windings (f : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    {L : List (ℤ × ℤ)} (hL : IsGridPath L) (hne : L ≠ [])
    (hcl : L.head? = L.getLast?) :
    ∃ S : Finset (ℤ × ℤ),
      (∀ p ∈ S,
        windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) ≠ 0 ∧
          gridSquareCenter δ p ∉ gridPathTrace δ L) ∧
      gridPathIntegral f δ L =
        ∑ p ∈ S,
          (windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) : ℂ) *
            gridSquareBoundaryIntegral f δ p := by
  sorry

/-- **Escape lemma.** If every complementary component of the open set `T`
is unbounded, then every grid square whose center carries nonzero winding of
a grid loop in `T` lies entirely (as a closed square) inside `T`: a
complementary point in the closed square would belong to a bounded pocket of
the winding region, whose frontier lies on the loop trace — but the trace is
in `T`, so the unbounded component through that point cannot escape. -/
theorem gridSquare_subset_of_windingNumber_ne_zero {T : Set ℂ}
    (hT : IsOpen T)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z))
    {δ : ℝ} (hδ : 0 < δ) {L : List (ℤ × ℤ)} (hL : IsGridPath L)
    (hne : L ≠ []) (hcl : L.head? = L.getLast?)
    (htrace : gridPathTrace δ L ⊆ T) {p : ℤ × ℤ}
    (hp : gridSquareCenter δ p ∉ gridPathTrace δ L)
    (hw : windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) ≠ 0) :
    gridSquare δ p ⊆ T := by
  intro z hz
  by_contra hzT
  -- Basic facts about the loop curve.
  have hclosed : gridLoopCurve δ L 0 = gridLoopCurve δ L 1 :=
    gridLoopCurve_closed hne hcl
  have hrange : Set.range (gridLoopCurve δ L) = gridPathTrace δ L :=
    range_gridLoopCurve hδ hL hne
  have hmemtr : ∀ t : I, gridLoopCurve δ L t ∈ gridPathTrace δ L := by
    intro t
    rw [← hrange]
    exact Set.mem_range_self t
  -- Coordinates of lattice points.
  have hgpre : ∀ q : ℤ × ℤ, (gridPoint δ q).re = δ * q.1 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hgpim : ∀ q : ℤ × ℤ, (gridPoint δ q).im = δ * q.2 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  -- Real and imaginary parts of convex combinations.
  have hsegre : ∀ (a b : ℂ) (u v : ℝ), (u • a + v • b).re = u * a.re + v * b.re := by
    intro a b u v
    simp [Complex.add_re]
  have hsegim : ∀ (a b : ℂ) (u v : ℝ), (u • a + v • b).im = u * a.im + v * b.im := by
    intro a b u v
    simp [Complex.add_im]
  -- Every point of the trace lies on a grid line.
  have hlines : ∀ M : List (ℤ × ℤ), IsGridPath M → ∀ w ∈ gridPathTrace δ M,
      (∃ m : ℤ, w.re = δ * m) ∨ (∃ n : ℤ, w.im = δ * n) := by
    intro M
    induction M with
    | nil => intro _ w hwtr; exact absurd hwtr (Set.notMem_empty w)
    | cons a M ih =>
      intro hM w hwtr
      cases M with
      | nil =>
        have hwa : w = gridPoint δ a := hwtr
        exact Or.inl ⟨a.1, by rw [hwa]; exact hgpre a⟩
      | cons b M' =>
        have hMc : List.IsChain GridAdj (a :: b :: M') := hM
        have hadj : GridAdj a b := (List.isChain_cons_cons.mp hMc).1
        have htl : IsGridPath (b :: M') := (List.isChain_cons_cons.mp hMc).2
        rcases hwtr with hseg | htr
        · obtain ⟨u, v, hu, hv, huv, hwe⟩ := hseg
          rcases hadj with ⟨hx, -⟩ | ⟨-, hy⟩
          · refine Or.inl ⟨a.1, ?_⟩
            rw [← hwe, hsegre, hgpre a, hgpre b, ← hx]
            calc u * (δ * (a.1 : ℝ)) + v * (δ * a.1)
                = (u + v) * (δ * a.1) := by ring
              _ = δ * a.1 := by rw [huv, one_mul]
          · refine Or.inr ⟨a.2, ?_⟩
            rw [← hwe, hsegim, hgpim a, hgpim b, ← hy]
            calc u * (δ * (a.2 : ℝ)) + v * (δ * a.2)
                = (u + v) * (δ * a.2) := by ring
              _ = δ * a.2 := by rw [huv, one_mul]
        · exact ih htl w htr
  -- The square as a product of intervals; its interior.
  have hKeq : gridSquare δ p =
      Set.Icc (δ * p.1) (δ * (p.1 + 1)) ×ℂ Set.Icc (δ * p.2) (δ * (p.2 + 1)) := rfl
  have hKint : interior (gridSquare δ p) =
      Set.Ioo (δ * p.1) (δ * (p.1 + 1)) ×ℂ Set.Ioo (δ * p.2) (δ * (p.2 + 1)) := by
    rw [hKeq, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  -- Coordinates of the square's center.
  have hhalf : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
  have hcre : (gridSquareCenter δ p).re = δ * p.1 + δ / 2 := by
    simp only [gridSquareCenter, gridPoint, hhalf, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.one_re, Complex.one_im]
    ring
  have hcim : (gridSquareCenter δ p).im = δ * p.2 + δ / 2 := by
    simp only [gridSquareCenter, gridPoint, hhalf, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      Complex.one_re, Complex.one_im]
    ring
  -- The center lies in the interior of the square.
  have hcint : gridSquareCenter δ p ∈ interior (gridSquare δ p) := by
    rw [hKint, Complex.mem_reProdIm, hcre, hcim]
    have e1 : δ * ((p.1 : ℝ) + 1) = δ * p.1 + δ := by ring
    have e2 : δ * ((p.2 : ℝ) + 1) = δ * p.2 + δ := by ring
    exact ⟨⟨by linarith, by rw [e1]; linarith⟩, ⟨by linarith, by rw [e2]; linarith⟩⟩
  -- The interior of the square misses the trace.
  have hIntDisj : ∀ w, w ∈ interior (gridSquare δ p) → w ∉ gridPathTrace δ L := by
    intro w hwint hwtr
    rw [hKint, Complex.mem_reProdIm] at hwint
    obtain ⟨⟨hre1, hre2⟩, him1, him2⟩ := hwint
    rcases hlines L hL w hwtr with ⟨m, hm⟩ | ⟨n, hn⟩
    · rw [hm] at hre1 hre2
      have h1 : p.1 < m := by exact_mod_cast lt_of_mul_lt_mul_left hre1 hδ.le
      have h2 : m < p.1 + 1 := by exact_mod_cast lt_of_mul_lt_mul_left hre2 hδ.le
      omega
    · rw [hn] at him1 him2
      have h1 : p.2 < n := by exact_mod_cast lt_of_mul_lt_mul_left him1 hδ.le
      have h2 : n < p.2 + 1 := by exact_mod_cast lt_of_mul_lt_mul_left him2 hδ.le
      omega
  -- The square is convex.
  have hKconv : Convex ℝ (gridSquare δ p) := by
    intro x hx y hy u v hu hv huv
    obtain ⟨⟨hxr1, hxr2⟩, hxi1, hxi2⟩ := hx
    obtain ⟨⟨hyr1, hyr2⟩, hyi1, hyi2⟩ := hy
    have hcombo : ∀ c : ℝ, c = u * c + v * c := by
      intro c
      rw [← add_mul, huv, one_mul]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hsegre, hcombo (δ * (p.1 : ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxr1 hu)
        (mul_le_mul_of_nonneg_left hyr1 hv)
    · rw [hsegre, hcombo (δ * ((p.1 : ℝ) + 1))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxr2 hu)
        (mul_le_mul_of_nonneg_left hyr2 hv)
    · rw [hsegim, hcombo (δ * (p.2 : ℝ))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxi1 hu)
        (mul_le_mul_of_nonneg_left hyi1 hv)
    · rw [hsegim, hcombo (δ * ((p.2 : ℝ) + 1))]
      exact add_le_add (mul_le_mul_of_nonneg_left hxi2 hu)
        (mul_le_mul_of_nonneg_left hyi2 hv)
  -- The square minus the trace is preconnected (star-shaped about the center).
  have hSpre : IsPreconnected (gridSquare δ p \ gridPathTrace δ L) := by
    apply isPreconnected_of_forall (gridSquareCenter δ p)
    intro y hy
    refine ⟨segment ℝ (gridSquareCenter δ p) y, ?_, left_mem_segment ℝ _ _,
      right_mem_segment ℝ _ _, (convex_segment _ _).isPreconnected⟩
    intro x hx
    rcases eq_or_ne x (gridSquareCenter δ p) with rfl | hxc
    · exact ⟨interior_subset hcint, hp⟩
    rcases eq_or_ne x y with rfl | hxy
    · exact hy
    have hxopen : x ∈ openSegment ℝ (gridSquareCenter δ p) y := by
      obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
      rcases hu.eq_or_lt with hu0 | hu0
      · have hv1 : v = 1 := by linarith
        refine absurd (Complex.ext ?_ ?_) hxy
        · rw [← hxe, hsegre, ← hu0, hv1]; ring
        · rw [← hxe, hsegim, ← hu0, hv1]; ring
      · rcases hv.eq_or_lt with hv0 | hv0
        · have hu1 : u = 1 := by linarith
          refine absurd (Complex.ext ?_ ?_) hxc
          · rw [← hxe, hsegre, ← hv0, hu1]; ring
          · rw [← hxe, hsegim, ← hv0, hu1]; ring
        · exact ⟨u, v, hu0, hv0, huv, hxe⟩
    have hxint : x ∈ interior (gridSquare δ p) :=
      hKconv.openSegment_interior_self_subset_interior hcint hy.1 hxopen
    exact ⟨interior_subset hxint, hIntDisj x hxint⟩
  -- Winding is constant on the square minus the trace: center vs `z`.
  have hznt : z ∉ gridPathTrace δ L := fun hzt => hzT (htrace hzt)
  have hzS : z ∈ gridSquare δ p \ gridPathTrace δ L := ⟨hz, hznt⟩
  have hcS : gridSquareCenter δ p ∈ gridSquare δ p \ gridPathTrace δ L :=
    ⟨interior_subset hcint, hp⟩
  have hdisjS : ∀ t : I,
      gridLoopCurve δ L t ∉ gridSquare δ p \ gridPathTrace δ L :=
    fun t ht => ht.2 (hmemtr t)
  have heq1 : windingNumber (gridLoopCurve δ L) (gridSquareCenter δ p) =
      windingNumber (gridLoopCurve δ L) z :=
    windingNumber_eq_of_preconnected hclosed hSpre hdisjS hcS hzS
  -- Winding is constant on the unbounded complementary component of `z`.
  have hzC : z ∈ connectedComponentIn Tᶜ z := mem_connectedComponentIn hzT
  have hCsub : connectedComponentIn Tᶜ z ⊆ Tᶜ := connectedComponentIn_subset _ _
  have hCpre : IsPreconnected (connectedComponentIn Tᶜ z) :=
    isPreconnected_connectedComponentIn
  have hdisjC : ∀ t : I, gridLoopCurve δ L t ∉ connectedComponentIn Tᶜ z :=
    fun t ht => (hCsub ht) (htrace (hmemtr t))
  have hcompact : IsCompact (Set.range (gridLoopCurve δ L)) :=
    isCompact_range (gridLoopCurve δ L).continuous
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall 0
  have hnsub : ¬ connectedComponentIn Tᶜ z ⊆ Metric.closedBall (0 : ℂ) (R + 1) :=
    fun hsub => hcompl z hzT (Metric.isBounded_closedBall.subset hsub)
  obtain ⟨x₀, hx₀C, hx₀out⟩ := Set.not_subset.mp hnsub
  have hx₀zero : windingNumber (gridLoopCurve δ L) x₀ = 0 := by
    refine windingNumber_eq_zero_of_ball (c := 0) (r := R + 1) hclosed ?_ ?_
    · intro t
      have ht := hR (Set.mem_range_self t)
      rw [Metric.mem_closedBall] at ht
      rw [Metric.mem_ball]
      linarith
    · exact fun hb => hx₀out (Metric.ball_subset_closedBall hb)
  have heq2 : windingNumber (gridLoopCurve δ L) z =
      windingNumber (gridLoopCurve δ L) x₀ :=
    windingNumber_eq_of_preconnected hclosed hCpre hdisjC hzC hx₀C
  exact hw (heq1.trans (heq2.trans hx₀zero))

/-- Grid-loop integrals of holomorphic functions vanish on domains with no
bounded complementary components: combine the edge-counting identity, the
escape lemma, and the rectangle Cauchy theorem. -/
theorem gridPathIntegral_eq_zero {T : Set ℂ} (hT : IsOpen T)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z))
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f T) {δ : ℝ} (hδ : 0 < δ)
    {L : List (ℤ × ℤ)} (hL : IsGridPath L) (hne : L ≠ [])
    (hcl : L.head? = L.getLast?) (htrace : gridPathTrace δ L ⊆ T) :
    gridPathIntegral f δ L = 0 := by
  -- Horizontal segment integrals as interval integrals.
  have hseg_h : ∀ x₀ x₁ y : ℝ,
      segmentIntegral f ((x₀ : ℂ) + (y : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y : ℂ) * Complex.I) =
        ∫ x in x₀..x₁, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x₀ x₁ y
    have e1 : (x₁ - x₀) * (0 : ℝ) + x₀ = x₀ := by ring
    have e2 : (x₁ - x₀) * (1 : ℝ) + x₀ = x₁ := by ring
    have key := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun v : ℝ => f ((v : ℂ) + (y : ℂ) * Complex.I)) (x₁ - x₀) x₀
    rw [e1, e2] at key
    have key' : ((x₁ - x₀ : ℝ) : ℂ) *
        (∫ t in (0 : ℝ)..1,
          f ((((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = ∫ v in x₀..x₁, f ((v : ℂ) + (y : ℂ) * Complex.I) := by
      rw [← Complex.real_smul]
      exact key
    calc segmentIntegral f ((x₀ : ℂ) + (y : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y : ℂ) * Complex.I)
        = ∫ t in (0 : ℝ)..1, ((x₁ - x₀ : ℝ) : ℂ) *
            f ((((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
          unfold segmentIntegral
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp only [Complex.real_smul]
          have harg : ((x₀ : ℂ) + (y : ℂ) * Complex.I) + (t : ℂ) *
                (((x₁ : ℂ) + (y : ℂ) * Complex.I) -
                  ((x₀ : ℂ) + (y : ℂ) * Complex.I))
              = (((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg]
          have hco : ((x₁ : ℂ) + (y : ℂ) * Complex.I) -
                ((x₀ : ℂ) + (y : ℂ) * Complex.I) = ((x₁ - x₀ : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hco]
      _ = ((x₁ - x₀ : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
            f ((((x₁ - x₀) * t + x₀ : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
          intervalIntegral.integral_const_mul _ _
      _ = ∫ x in x₀..x₁, f ((x : ℂ) + (y : ℂ) * Complex.I) := key'
  -- Vertical segment integrals as interval integrals.
  have hseg_v : ∀ x y₀ y₁ : ℝ,
      segmentIntegral f ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x : ℂ) + (y₁ : ℂ) * Complex.I) =
        Complex.I * ∫ y in y₀..y₁, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
    intro x y₀ y₁
    have e1 : (y₁ - y₀) * (0 : ℝ) + y₀ = y₀ := by ring
    have e2 : (y₁ - y₀) * (1 : ℝ) + y₀ = y₁ := by ring
    have key := intervalIntegral.smul_integral_comp_mul_add
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun v : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) (y₁ - y₀) y₀
    rw [e1, e2] at key
    have key' : ((y₁ - y₀ : ℝ) : ℂ) *
        (∫ t in (0 : ℝ)..1,
          f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I))
        = ∫ v in y₀..y₁, f ((x : ℂ) + (v : ℂ) * Complex.I) := by
      rw [← Complex.real_smul]
      exact key
    calc segmentIntegral f ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x : ℂ) + (y₁ : ℂ) * Complex.I)
        = ∫ t in (0 : ℝ)..1, Complex.I * (((y₁ - y₀ : ℝ) : ℂ) *
            f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I)) := by
          unfold segmentIntegral
          refine intervalIntegral.integral_congr fun t _ => ?_
          simp only [Complex.real_smul]
          have harg : ((x : ℂ) + (y₀ : ℂ) * Complex.I) + (t : ℂ) *
                (((x : ℂ) + (y₁ : ℂ) * Complex.I) -
                  ((x : ℂ) + (y₀ : ℂ) * Complex.I))
              = (x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg]
          have hco : ((x : ℂ) + (y₁ : ℂ) * Complex.I) -
                ((x : ℂ) + (y₀ : ℂ) * Complex.I)
              = Complex.I * ((y₁ - y₀ : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hco, mul_assoc]
      _ = Complex.I * ∫ t in (0 : ℝ)..1, ((y₁ - y₀ : ℝ) : ℂ) *
            f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I) :=
          intervalIntegral.integral_const_mul _ _
      _ = Complex.I * (((y₁ - y₀ : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
            f ((x : ℂ) + (((y₁ - y₀) * t + y₀ : ℝ) : ℂ) * Complex.I)) :=
          congrArg (Complex.I * ·) (intervalIntegral.integral_const_mul _ _)
      _ = Complex.I * ∫ y in y₀..y₁, f ((x : ℂ) + (y : ℂ) * Complex.I) :=
          congrArg (Complex.I * ·) key'
  -- Cauchy's theorem for an axis-parallel square boundary, in segment form.
  have hsquare : ∀ x₀ x₁ y₀ y₁ : ℝ, x₀ ≤ x₁ → y₀ ≤ y₁ →
      DifferentiableOn ℂ f (Set.Icc x₀ x₁ ×ℂ Set.Icc y₀ y₁) →
      segmentIntegral f ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y₀ : ℂ) * Complex.I) +
        segmentIntegral f ((x₁ : ℂ) + (y₀ : ℂ) * Complex.I)
          ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) +
        segmentIntegral f ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I)
          ((x₀ : ℂ) + (y₁ : ℂ) * Complex.I) +
        segmentIntegral f ((x₀ : ℂ) + (y₁ : ℂ) * Complex.I)
          ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I) = 0 := by
    intro x₀ x₁ y₀ y₁ hx hy hdiff
    have h1 : ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re = x₀ := by simp
    have h2 : ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re = x₁ := by simp
    have h3 : ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im = y₀ := by simp
    have h4 : ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im = y₁ := by simp
    have hd : DifferentiableOn ℂ f
        (Set.uIcc ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).re
            ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).re ×ℂ
          Set.uIcc ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I).im
            ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I).im) := by
      rw [h1, h2, h3, h4, Set.uIcc_of_le hx, Set.uIcc_of_le hy]
      exact hdiff
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((x₀ : ℂ) + (y₀ : ℂ) * Complex.I) ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) hd
    rw [h1, h2, h3, h4] at hrect
    have hrect' : (∫ x in x₀..x₁, f ((x : ℂ) + (y₀ : ℂ) * Complex.I)) -
        (∫ x in x₀..x₁, f ((x : ℂ) + (y₁ : ℂ) * Complex.I)) +
        Complex.I * (∫ y in y₀..y₁, f ((x₁ : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in y₀..y₁, f ((x₀ : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
      hrect
    rw [hseg_h x₀ x₁ y₀, hseg_v x₁ y₀ y₁, hseg_h x₁ x₀ y₁, hseg_v x₀ y₁ y₀,
      intervalIntegral.integral_symm x₀ x₁, intervalIntegral.integral_symm y₀ y₁]
    linear_combination hrect'
  -- Edge-counting identity gives the winding-weighted sum.
  obtain ⟨S, hS, hsum⟩ := gridPathIntegral_eq_sum_windings f hδ hL hne hcl
  rw [hsum]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hw, hcen⟩ := hS p hp
  -- Escape lemma: the closed square lies in `T`.
  have hsub : gridSquare δ p ⊆ T :=
    gridSquare_subset_of_windingNumber_ne_zero hT hcompl hδ hL hne hcl htrace
      hcen hw
  have hset : (Set.Icc (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) ×ℂ
      Set.Icc (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1))) = gridSquare δ p := by
    ext z
    simp only [Complex.mem_reProdIm, gridSquare, Set.mem_setOf_eq]
  have hdiff : DifferentiableOn ℂ f
      (Set.Icc (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) ×ℂ
        Set.Icc (δ * (p.2 : ℝ)) (δ * ((p.2 : ℝ) + 1))) :=
    hf.mono (by rw [hset]; exact hsub)
  have hxle : δ * (p.1 : ℝ) ≤ δ * ((p.1 : ℝ) + 1) := by nlinarith [hδ]
  have hyle : δ * (p.2 : ℝ) ≤ δ * ((p.2 : ℝ) + 1) := by nlinarith [hδ]
  have hsq := hsquare (δ * (p.1 : ℝ)) (δ * ((p.1 : ℝ) + 1)) (δ * (p.2 : ℝ))
    (δ * ((p.2 : ℝ) + 1)) hxle hyle hdiff
  -- Identify the four corners of the grid square.
  have hA : gridPoint δ p
      = ((δ * (p.1 : ℝ) : ℝ) : ℂ) + ((δ * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  have hB : gridPoint δ (p.1 + 1, p.2)
      = ((δ * ((p.1 : ℝ) + 1) : ℝ) : ℂ) + ((δ * (p.2 : ℝ) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  have hC : gridPoint δ (p.1 + 1, p.2 + 1)
      = ((δ * ((p.1 : ℝ) + 1) : ℝ) : ℂ) +
        ((δ * ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  have hD : gridPoint δ (p.1, p.2 + 1)
      = ((δ * (p.1 : ℝ) : ℝ) : ℂ) + ((δ * ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.I := by
    simp only [gridPoint]
    push_cast
    ring
  -- Unfold the square boundary integral into its four segments.
  have hb0 : gridSquareBoundaryIntegral f δ p
      = segmentIntegral f (gridPoint δ p) (gridPoint δ (p.1 + 1, p.2)) +
        (segmentIntegral f (gridPoint δ (p.1 + 1, p.2))
            (gridPoint δ (p.1 + 1, p.2 + 1)) +
          (segmentIntegral f (gridPoint δ (p.1 + 1, p.2 + 1))
              (gridPoint δ (p.1, p.2 + 1)) +
            (segmentIntegral f (gridPoint δ (p.1, p.2 + 1)) (gridPoint δ p) +
              0))) := rfl
  have hbz : gridSquareBoundaryIntegral f δ p = 0 := by
    rw [hb0, hA, hB, hC, hD]
    linear_combination hsq
  rw [hbz, mul_zero]

/-- Any two lattice points of an open connected set are joined by a grid
path inside the set, for all sufficiently fine scales. -/
theorem exists_gridPath_join {T : Set ℂ} (hT : IsOpen T)
    (hconn : IsPreconnected T) {a b : ℂ} (ha : a ∈ T) (hb : b ∈ T) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ (p q : ℤ × ℤ) (L : List (ℤ × ℤ)),
        IsGridPath L ∧ L.head? = some p ∧ L.getLast? = some q ∧
        gridPathTrace δ L ⊆ T ∧
        ‖gridPoint δ p - a‖ ≤ 2 * δ ∧ ‖gridPoint δ q - b‖ ≤ 2 * δ := by
  -- Step 1: a path from `a` to `b` inside `T`.
  have hTc : IsConnected T := ⟨⟨a, ha⟩, hconn⟩
  have hTp : IsPathConnected T := hT.isConnected_iff_isPathConnected.mp hTc
  obtain ⟨γ, hγ⟩ := hTp.joinedIn a ha b hb
  -- Step 2: Lebesgue radius for the compact trace inside the open set.
  have hKc : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hKT : Set.range γ ⊆ T := Set.range_subset_iff.mpr hγ
  obtain ⟨r, hr, hrT⟩ := hKc.exists_thickening_subset_open hT hKT
  have hball : ∀ x ∈ Set.range γ, Metric.ball x r ⊆ T := by
    intro x hx y hy
    exact hrT (Metric.mem_thickening_iff.mpr ⟨x, hx, Metric.mem_ball.mp hy⟩)
  have hUC : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  refine ⟨r / 100, div_pos hr (by norm_num), ?_⟩
  intro δ hδ hδ₀
  -- ## Combinatorial toolkit: unit steps, straight walks, gluing
  have hadjHL : ∀ p : ℤ × ℤ, GridAdj p (p.1 - 1, p.2) :=
    fun p => Or.inr ⟨show (p.1 - (p.1 - 1)).natAbs = 1 by omega, rfl⟩
  have hadjHR : ∀ p : ℤ × ℤ, GridAdj p (p.1 + 1, p.2) :=
    fun p => Or.inr ⟨show (p.1 - (p.1 + 1)).natAbs = 1 by omega, rfl⟩
  have hadjVD : ∀ p : ℤ × ℤ, GridAdj p (p.1, p.2 - 1) :=
    fun p => Or.inl ⟨rfl, show (p.2 - (p.2 - 1)).natAbs = 1 by omega⟩
  have hadjVU : ∀ p : ℤ × ℤ, GridAdj p (p.1, p.2 + 1) :=
    fun p => Or.inl ⟨rfl, show (p.2 - (p.2 + 1)).natAbs = 1 by omega⟩
  -- Horizontal straight walk from `p` by `d` steps (excluding the start).
  have hwalkH : ∀ (n : ℕ) (p : ℤ × ℤ) (d : ℤ), d.natAbs = n →
      ∃ L : List (ℤ × ℤ), List.IsChain GridAdj (p :: L) ∧
        (p :: L).getLast? = some (p.1 + d, p.2) ∧
        ∀ v ∈ p :: L, v.2 = p.2 ∧ (v.1 - p.1).natAbs ≤ d.natAbs := by
    intro n
    induction n with
    | zero =>
      intro p d hd
      have hd0 : d = 0 := by omega
      subst hd0
      refine ⟨[], List.isChain_singleton p, by simp, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨rfl, by omega⟩
    | succ m ih =>
      intro p d hd
      rcases lt_trichotomy d 0 with hneg | h0 | hpos
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1 - 1, p.2) (d + 1) (by omega)
        refine ⟨(p.1 - 1, p.2) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjHL p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          show some (p.1 - 1 + (d + 1), p.2) = some (p.1 + d, p.2)
          rw [show p.1 - 1 + (d + 1) = p.1 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h2, h1⟩ := hbd v hv'
            have h2' : v.2 = p.2 := h2
            have h1' : (v.1 - (p.1 - 1)).natAbs ≤ (d + 1).natAbs := h1
            exact ⟨h2', by omega⟩
      · exfalso; omega
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1 + 1, p.2) (d - 1) (by omega)
        refine ⟨(p.1 + 1, p.2) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjHR p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          show some (p.1 + 1 + (d - 1), p.2) = some (p.1 + d, p.2)
          rw [show p.1 + 1 + (d - 1) = p.1 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h2, h1⟩ := hbd v hv'
            have h2' : v.2 = p.2 := h2
            have h1' : (v.1 - (p.1 + 1)).natAbs ≤ (d - 1).natAbs := h1
            exact ⟨h2', by omega⟩
  -- Vertical straight walk from `p` by `d` steps (excluding the start).
  have hwalkV : ∀ (n : ℕ) (p : ℤ × ℤ) (d : ℤ), d.natAbs = n →
      ∃ L : List (ℤ × ℤ), List.IsChain GridAdj (p :: L) ∧
        (p :: L).getLast? = some (p.1, p.2 + d) ∧
        ∀ v ∈ p :: L, v.1 = p.1 ∧ (v.2 - p.2).natAbs ≤ d.natAbs := by
    intro n
    induction n with
    | zero =>
      intro p d hd
      have hd0 : d = 0 := by omega
      subst hd0
      refine ⟨[], List.isChain_singleton p, by simp, ?_⟩
      intro v hv
      rw [List.mem_singleton] at hv
      subst hv
      exact ⟨rfl, by omega⟩
    | succ m ih =>
      intro p d hd
      rcases lt_trichotomy d 0 with hneg | h0 | hpos
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1, p.2 - 1) (d + 1) (by omega)
        refine ⟨(p.1, p.2 - 1) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjVD p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          show some (p.1, p.2 - 1 + (d + 1)) = some (p.1, p.2 + d)
          rw [show p.2 - 1 + (d + 1) = p.2 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h1, h2⟩ := hbd v hv'
            have h1' : v.1 = p.1 := h1
            have h2' : (v.2 - (p.2 - 1)).natAbs ≤ (d + 1).natAbs := h2
            exact ⟨h1', by omega⟩
      · exfalso; omega
      · obtain ⟨L, hc, hl, hbd⟩ := ih (p.1, p.2 + 1) (d - 1) (by omega)
        refine ⟨(p.1, p.2 + 1) :: L, ?_, ?_, ?_⟩
        · exact List.isChain_cons_cons.mpr ⟨hadjVU p, hc⟩
        · rw [List.getLast?_cons_cons, hl]
          show some (p.1, p.2 + 1 + (d - 1)) = some (p.1, p.2 + d)
          rw [show p.2 + 1 + (d - 1) = p.2 + d from by ring]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, by omega⟩
          · obtain ⟨h1, h2⟩ := hbd v hv'
            have h1' : v.1 = p.1 := h1
            have h2' : (v.2 - (p.2 + 1)).natAbs ≤ (d - 1).natAbs := h2
            exact ⟨h1', by omega⟩
  -- Gluing chains along a shared junction.
  have hglue : ∀ (l₁ l₂ : List (ℤ × ℤ)) (m : ℤ × ℤ), List.IsChain GridAdj l₁ →
      l₁.getLast? = some m → List.IsChain GridAdj (m :: l₂) →
      List.IsChain GridAdj (l₁ ++ l₂) := by
    intro l₁ l₂ m h₁ hm h₂
    obtain ⟨hhead, htail⟩ := List.isChain_cons.mp h₂
    refine h₁.append htail ?_
    intro x hx y hy
    rw [hm] at hx
    simp only [Option.mem_some_iff] at hx
    subst hx
    exact hhead y hy
  have hglueLast : ∀ (l₁ l₂ : List (ℤ × ℤ)) (m x : ℤ × ℤ), l₁.getLast? = some m →
      (m :: l₂).getLast? = some x → (l₁ ++ l₂).getLast? = some x := by
    intro l₁ l₂ m x h₁ h₂
    cases l₂ with
    | nil =>
      simp only [List.getLast?_singleton] at h₂
      rw [List.append_nil, h₁]
      exact h₂
    | cons y l =>
      rw [List.getLast?_append_cons]
      rw [List.getLast?_cons_cons] at h₂
      exact h₂
  -- L-shaped walk joining two arbitrary lattice points.
  have hwalk : ∀ p q : ℤ × ℤ, ∃ L : List (ℤ × ℤ), List.IsChain GridAdj (p :: L) ∧
      (p :: L).getLast? = some q ∧
      ∀ v ∈ p :: L, (v.1 - p.1).natAbs ≤ (q.1 - p.1).natAbs ∧
        (v.2 - p.2).natAbs ≤ (q.2 - p.2).natAbs := by
    intro p q
    obtain ⟨L₁, hc₁, hl₁, hb₁⟩ := hwalkH (q.1 - p.1).natAbs p (q.1 - p.1) rfl
    obtain ⟨L₂, hc₂, hl₂, hb₂⟩ :=
      hwalkV (q.2 - p.2).natAbs (p.1 + (q.1 - p.1), p.2) (q.2 - p.2) rfl
    refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
    · rw [← List.cons_append]
      exact hglue (p :: L₁) L₂ (p.1 + (q.1 - p.1), p.2) hc₁ hl₁ hc₂
    · rw [← List.cons_append]
      have h := hglueLast (p :: L₁) L₂ (p.1 + (q.1 - p.1), p.2) _ hl₁ hl₂
      rw [h]
      show some (p.1 + (q.1 - p.1), p.2 + (q.2 - p.2)) = some q
      rw [show p.1 + (q.1 - p.1) = q.1 from by ring, show p.2 + (q.2 - p.2) = q.2 from by ring]
    · intro v hv
      rw [← List.cons_append] at hv
      rcases List.mem_append.mp hv with hv1 | hv2
      · obtain ⟨h2, h1⟩ := hb₁ v hv1
        exact ⟨h1, by omega⟩
      · obtain ⟨h1, h2⟩ := hb₂ v (List.mem_cons_of_mem _ hv2)
        have h1' : v.1 = p.1 + (q.1 - p.1) := h1
        have h2' : (v.2 - p.2).natAbs ≤ (q.2 - p.2).natAbs := h2
        exact ⟨by omega, h2'⟩
  -- ## Trace toolkit
  have htrace_single : ∀ p : ℤ × ℤ, gridPathTrace δ [p] = {gridPoint δ p} := fun p => rfl
  have htrace_cons : ∀ (p q : ℤ × ℤ) (L : List (ℤ × ℤ)),
      gridPathTrace δ (p :: q :: L) =
        segment ℝ (gridPoint δ p) (gridPoint δ q) ∪ gridPathTrace δ (q :: L) :=
    fun p q L => rfl
  have htraceConv : ∀ (S : Set ℂ), Convex ℝ S → ∀ L : List (ℤ × ℤ),
      (∀ v ∈ L, gridPoint δ v ∈ S) → gridPathTrace δ L ⊆ S := by
    intro S hS L
    induction L with
    | nil => intro _ w hw; cases hw
    | cons x l ih =>
      intro hv
      cases l with
      | nil =>
        rw [htrace_single]
        rw [Set.singleton_subset_iff]
        exact hv x (List.mem_singleton_self x)
      | cons y l' =>
        rw [htrace_cons]
        apply Set.union_subset
        · exact hS.segment_subset (hv x (by simp)) (hv y (by simp))
        · exact ih fun v hv' => hv v (List.mem_cons_of_mem x hv')
  have htraceApp : ∀ (l₁ l₂ : List (ℤ × ℤ)) (m : ℤ × ℤ), l₁.getLast? = some m →
      gridPathTrace δ (l₁ ++ l₂) ⊆ gridPathTrace δ l₁ ∪ gridPathTrace δ (m :: l₂) := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ m hm; simp at hm
    | cons x l ih =>
      intro l₂ m hm
      cases l with
      | nil =>
        have hx : x = m := by
          simp only [List.getLast?_singleton, Option.some.injEq] at hm
          exact hm
        subst hx
        intro w hw
        rw [List.singleton_append] at hw
        exact Set.mem_union_right _ hw
      | cons y l' =>
        have hm' : (y :: l').getLast? = some m := by
          rwa [List.getLast?_cons_cons] at hm
        intro w hw
        rw [List.cons_append, List.cons_append, htrace_cons] at hw
        rcases hw with hw | hw
        · exact Set.mem_union_left _ (by rw [htrace_cons]; exact Set.mem_union_left _ hw)
        · have hw2 : w ∈ gridPathTrace δ ((y :: l') ++ l₂) := by
            rw [List.cons_append]; exact hw
          rcases ih l₂ m hm' hw2 with h | h
          · exact Set.mem_union_left _ (by rw [htrace_cons]; exact Set.mem_union_right _ h)
          · exact Set.mem_union_right _ h
  -- ## Metric toolkit
  have hgpre : ∀ p : ℤ × ℤ, (gridPoint δ p).re = δ * (p.1 : ℝ) ∧
      (gridPoint δ p).im = δ * (p.2 : ℝ) := by
    intro p
    constructor <;> simp [gridPoint, Complex.mul_re, Complex.mul_im]
  have hgpsub : ∀ p q : ℤ × ℤ, (gridPoint δ q - gridPoint δ p).re = δ * ((q.1 : ℝ) - (p.1 : ℝ)) ∧
      (gridPoint δ q - gridPoint δ p).im = δ * ((q.2 : ℝ) - (p.2 : ℝ)) := by
    intro p q
    rw [Complex.sub_re, Complex.sub_im, (hgpre p).1, (hgpre p).2, (hgpre q).1, (hgpre q).2]
    constructor <;> ring
  have hgp_le : ∀ p q : ℤ × ℤ, ‖gridPoint δ q - gridPoint δ p‖ ≤
      δ * |(q.1 : ℝ) - (p.1 : ℝ)| + δ * |(q.2 : ℝ) - (p.2 : ℝ)| := by
    intro p q
    calc ‖gridPoint δ q - gridPoint δ p‖
        ≤ |(gridPoint δ q - gridPoint δ p).re| + |(gridPoint δ q - gridPoint δ p).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = δ * |(q.1 : ℝ) - (p.1 : ℝ)| + δ * |(q.2 : ℝ) - (p.2 : ℝ)| := by
          rw [(hgpsub p q).1, (hgpsub p q).2, abs_mul, abs_mul, abs_of_pos hδ]
  have hgp_ge1 : ∀ p q : ℤ × ℤ, δ * |(q.1 : ℝ) - (p.1 : ℝ)| ≤
      ‖gridPoint δ q - gridPoint δ p‖ := by
    intro p q
    have h := Complex.abs_re_le_norm (gridPoint δ q - gridPoint δ p)
    rwa [(hgpsub p q).1, abs_mul, abs_of_pos hδ] at h
  have hgp_ge2 : ∀ p q : ℤ × ℤ, δ * |(q.2 : ℝ) - (p.2 : ℝ)| ≤
      ‖gridPoint δ q - gridPoint δ p‖ := by
    intro p q
    have h := Complex.abs_im_le_norm (gridPoint δ q - gridPoint δ p)
    rwa [(hgpsub p q).2, abs_mul, abs_of_pos hδ] at h
  have hfloor : ∀ u : ℝ, |δ * ((⌊u / δ⌋ : ℤ) : ℝ) - u| ≤ δ := by
    intro u
    have h1 : ((⌊u / δ⌋ : ℤ) : ℝ) ≤ u / δ := Int.floor_le _
    have h2 : u / δ < ((⌊u / δ⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hcancel : δ * (u / δ) = u := by field_simp
    have h1' : δ * ((⌊u / δ⌋ : ℤ) : ℝ) ≤ u := by
      have := mul_le_mul_of_nonneg_left h1 hδ.le
      rwa [hcancel] at this
    have h2' : u < δ * ((⌊u / δ⌋ : ℤ) : ℝ) + δ := by
      have := mul_lt_mul_of_pos_left h2 hδ
      rw [hcancel] at this
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  have hsnapz : ∀ z : ℂ, ‖gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z‖ ≤ 2 * δ := by
    intro z
    have hre : (gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋)).re = δ * ((⌊z.re / δ⌋ : ℤ) : ℝ) :=
      (hgpre _).1
    have him : (gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋)).im = δ * ((⌊z.im / δ⌋ : ℤ) : ℝ) :=
      (hgpre _).2
    calc ‖gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z‖
        ≤ |(gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z).re| +
          |(gridPoint δ (⌊z.re / δ⌋, ⌊z.im / δ⌋) - z).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ δ + δ := by
          rw [Complex.sub_re, Complex.sub_im, hre, him]
          exact add_le_add (hfloor z.re) (hfloor z.im)
      _ = 2 * δ := by ring
  have cast_bound : ∀ x y w : ℤ, (x - y).natAbs ≤ (w - y).natAbs →
      |(x : ℝ) - (y : ℝ)| ≤ |(w : ℝ) - (y : ℝ)| := by
    intro x y w h
    have h1 : |x - y| ≤ |w - y| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast h
    have h2 : ((|x - y| : ℤ) : ℝ) ≤ ((|w - y| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs, Int.cast_abs] at h2
    push_cast at h2
    exact h2
  -- ## Sampling the path
  obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuous_iff.mp hUC δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
  set N : ℕ := n + 1 with hNdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNη : 1 / (N : ℝ) < η := by
    have hn' : 1 / η < (N : ℝ) := lt_of_lt_of_le hn (by exact_mod_cast Nat.le_succ n)
    rw [div_lt_iff₀ hη] at hn'
    rw [div_lt_iff₀ hNpos, mul_comm]
    exact hn'
  have hmem : ∀ k : ℕ, k ≤ N → ((k : ℝ) / (N : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    intro k hk
    constructor
    · positivity
    · rw [div_le_one hNpos]
      exact_mod_cast hk
  let τ : ℕ → I := fun k => Set.projIcc 0 1 zero_le_one ((k : ℝ) / (N : ℝ))
  have hτ : ∀ k : ℕ, k ≤ N → ((τ k : ℝ)) = (k : ℝ) / (N : ℝ) := by
    intro k hk
    show ((Set.projIcc (0 : ℝ) 1 zero_le_one ((k : ℝ) / (N : ℝ)) : Set.Icc (0 : ℝ) 1) : ℝ) =
      (k : ℝ) / (N : ℝ)
    rw [Set.projIcc_of_mem zero_le_one (hmem k hk)]
  let zf : ℕ → ℂ := fun k => γ (τ k)
  let pt : ℕ → ℤ × ℤ := fun k => (⌊(zf k).re / δ⌋, ⌊(zf k).im / δ⌋)
  have hzK : ∀ k, zf k ∈ Set.range γ := fun k => ⟨τ k, rfl⟩
  have hz0 : zf 0 = a := by
    have h0 : τ 0 = 0 := by
      apply Subtype.ext
      rw [hτ 0 (Nat.zero_le N)]
      simp
    show γ (τ 0) = a
    rw [h0]
    exact γ.source
  have hzN : zf N = b := by
    have h1 : τ N = 1 := by
      apply Subtype.ext
      rw [hτ N le_rfl, div_self (ne_of_gt hNpos)]
      simp
    show γ (τ N) = b
    rw [h1]
    exact γ.target
  have hstep : ∀ k : ℕ, k < N → ‖zf (k + 1) - zf k‖ ≤ δ := by
    intro k hk
    have e1 : ((τ (k + 1) : ℝ)) = ((k : ℝ) + 1) / (N : ℝ) := by
      rw [hτ (k + 1) (by omega)]
      push_cast
      ring
    have e2 : ((τ k : ℝ)) = (k : ℝ) / (N : ℝ) := hτ k (by omega)
    have hd : dist (τ (k + 1)) (τ k) < η := by
      rw [Subtype.dist_eq, e1, e2, Real.dist_eq]
      rw [show ((k : ℝ) + 1) / (N : ℝ) - (k : ℝ) / (N : ℝ) = 1 / (N : ℝ) from by ring]
      rw [abs_of_pos (div_pos one_pos hNpos)]
      exact hNη
    have h := hmod hd
    rw [dist_eq_norm] at h
    exact h.le
  have hsnap : ∀ k : ℕ, ‖gridPoint δ (pt k) - zf k‖ ≤ 2 * δ := fun k => hsnapz (zf k)
  -- ## Main induction: grid path from `pt 0` to `pt k` with trace in `T`
  have hmain : ∀ k : ℕ, k ≤ N → ∃ L : List (ℤ × ℤ), List.IsChain GridAdj L ∧
      L.head? = some (pt 0) ∧ L.getLast? = some (pt k) ∧ gridPathTrace δ L ⊆ T := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[pt 0], List.isChain_singleton _, by simp, by simp, ?_⟩
      intro w hw
      rw [htrace_single] at hw
      have hw' : w = gridPoint δ (pt 0) := hw
      apply hball (zf 0) (hzK 0)
      rw [Metric.mem_ball, dist_eq_norm, hw']
      calc ‖gridPoint δ (pt 0) - zf 0‖ ≤ 2 * δ := hsnap 0
        _ < r := by linarith
    | succ k ih =>
      intro hk1
      have hk' : k < N := by omega
      obtain ⟨L, hLc, hLh, hLl, hLt⟩ := ih (by omega)
      obtain ⟨W, hWc, hWl, hWb⟩ := hwalk (pt k) (pt (k + 1))
      -- distance between consecutive snapped points
      have h5 : ‖gridPoint δ (pt (k + 1)) - gridPoint δ (pt k)‖ ≤ 5 * δ := by
        have e1 := hsnap k
        have e2 := hsnap (k + 1)
        have e3 := hstep k hk'
        have hsplit : gridPoint δ (pt (k + 1)) - gridPoint δ (pt k) =
            (gridPoint δ (pt (k + 1)) - zf (k + 1)) +
              ((zf (k + 1) - zf k) + (zf k - gridPoint δ (pt k))) := by ring
        rw [hsplit]
        have t1 := norm_add_le (gridPoint δ (pt (k + 1)) - zf (k + 1))
          ((zf (k + 1) - zf k) + (zf k - gridPoint δ (pt k)))
        have t2 := norm_add_le (zf (k + 1) - zf k) (zf k - gridPoint δ (pt k))
        have t3 : ‖zf k - gridPoint δ (pt k)‖ = ‖gridPoint δ (pt k) - zf k‖ :=
          norm_sub_rev _ _
        rw [t3] at t2
        linarith
      -- every vertex of the walk stays near `zf k`
      have hvert : ∀ v ∈ pt k :: W, gridPoint δ v ∈ Metric.ball (zf k) r := by
        intro v hv
        obtain ⟨hb1, hb2⟩ := hWb v hv
        have hc1 := cast_bound v.1 (pt k).1 (pt (k + 1)).1 hb1
        have hc2 := cast_bound v.2 (pt k).2 (pt (k + 1)).2 hb2
        rw [Metric.mem_ball, dist_eq_norm]
        have hle := hgp_le (pt k) v
        have hge1 := hgp_ge1 (pt k) (pt (k + 1))
        have hge2 := hgp_ge2 (pt k) (pt (k + 1))
        have hsn := hsnap k
        have htri : ‖gridPoint δ v - zf k‖ ≤
            ‖gridPoint δ v - gridPoint δ (pt k)‖ + ‖gridPoint δ (pt k) - zf k‖ := by
          rw [show gridPoint δ v - zf k = (gridPoint δ v - gridPoint δ (pt k)) +
            (gridPoint δ (pt k) - zf k) from by ring]
          exact norm_add_le _ _
        have hmul1 : δ * |(v.1 : ℝ) - ((pt k).1 : ℝ)| ≤
            δ * |((pt (k + 1)).1 : ℝ) - ((pt k).1 : ℝ)| :=
          mul_le_mul_of_nonneg_left hc1 hδ.le
        have hmul2 : δ * |(v.2 : ℝ) - ((pt k).2 : ℝ)| ≤
            δ * |((pt (k + 1)).2 : ℝ) - ((pt k).2 : ℝ)| :=
          mul_le_mul_of_nonneg_left hc2 hδ.le
        have hr12 : 12 * δ < r := by linarith
        linarith
      have hWtr : gridPathTrace δ (pt k :: W) ⊆ T := by
        intro w hw
        exact hball (zf k) (hzK k)
          (htraceConv (Metric.ball (zf k) r) (convex_ball _ _) (pt k :: W) hvert hw)
      refine ⟨L ++ W, hglue L W (pt k) hLc hLl hWc, ?_,
        hglueLast L W (pt k) (pt (k + 1)) hLl hWl, ?_⟩
      · cases L with
        | nil => simp at hLh
        | cons x L' =>
          rw [List.cons_append, List.head?_cons]
          rw [List.head?_cons] at hLh
          exact hLh
      · intro w hw
        rcases htraceApp L W (pt k) hLl hw with h | h
        · exact hLt h
        · exact hWtr h
  obtain ⟨L, hc, hh, hl, ht⟩ := hmain N le_rfl
  refine ⟨pt 0, pt N, L, hc, hh, hl, ht, ?_, ?_⟩
  · have h := hsnap 0
    rwa [hz0] at h
  · have h := hsnap N
    rwa [hzN] at h

/-- **Essential loops around separated compact complementary pieces.** If a
compact piece `A` of the closed complement of an open set `T` is metrically
separated from the rest of the complement, then some closed curve in `T`
has nonzero winding number about any prescribed point of `A`: the boundary
of the union of small grid squares meeting `A` consists of grid edges lying
in `T`, and by the per-edge principal-logarithm increment linearity the
total winding of its boundary cycles about the point is one, so some cycle
is essential. -/
theorem exists_gridLoop_winding_ne_zero {T : Set ℂ} (hT : IsOpen T)
    {z₀ : ℂ} (A : Set ℂ) (ε : ℝ) (hε : 0 < ε) (hA : IsCompact A)
    (hzA : z₀ ∈ A) (hAT : A ⊆ Tᶜ)
    (hsep : ∀ w ∈ Tᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a) :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧ (∀ t : unitInterval, γ t ∈ T) ∧
      windingNumber γ z₀ ≠ 0 := by
  sorry

set_option maxHeartbeats 400000 in
/-- **Primitives exist on domains with no bounded complementary
components.** The grid integral from a basepoint is path-independent by the
vanishing of grid-loop integrals, defines a function on each component, and
differentiates to `f` by the small-rectangle estimate. This provides the
`has_primitives` hypothesis of the vendored Riemann mapping theorem. -/
theorem has_primitives_of_unbounded_components {T : Set ℂ} (hT : IsOpen T)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z)) :
    has_primitives T := by
  intro f hf
  -- ================================================================
  -- STAGE 1: FTC along segments inside the domain of a local primitive.
  -- ================================================================
  have hfc : ∀ w ∈ T, ContinuousAt f w := by
    intro w hw
    exact (hf.differentiableAt (hT.mem_nhds hw)).continuousAt
  have hFTC : ∀ (F : ℂ → ℂ) (O : Set ℂ), IsOpen O → O ⊆ T →
      (∀ w ∈ O, HasDerivAt F (f w) w) →
      ∀ a b : ℂ, segment ℝ a b ⊆ O → segmentIntegral f a b = F b - F a := by
    intro F O hO hOT hF a b hseg
    have hmem : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) 1 → a + (t:ℂ) * (b - a) ∈ O := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      refine hseg ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun s : ℝ => F (a + (s:ℂ) * (b - a)))
          ((b - a) * f (a + (t:ℂ) * (b - a))) t := by
      intro t ht
      have hinner : HasDerivAt (fun w : ℂ => a + w * (b - a)) (b - a) ((t:ℂ)) := by
        simpa using ((hasDerivAt_id ((t:ℂ))).mul_const (b - a)).const_add a
      have hFd : HasDerivAt F (f (a + (t:ℂ) * (b - a))) (a + (t:ℂ) * (b - a)) :=
        hF _ (hmem t ht)
      have hcomp := (hFd.comp ((t:ℂ)) hinner).comp_ofReal
      simpa [Function.comp, mul_comm] using hcomp
    have hpar : Continuous fun s : ℝ => a + (s:ℂ) * (b - a) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcont : ContinuousOn (fun t : ℝ => (b - a) * f (a + (t:ℂ) * (b - a)))
        (Set.uIcc (0:ℝ) 1) := by
      intro t ht
      have hgc : ContinuousAt (fun s : ℝ => f (a + (s:ℂ) * (b - a))) t :=
        ContinuousAt.comp (x := t) (g := f)
          (f := fun s : ℝ => a + (s:ℂ) * (b - a))
          (hfc _ (hOT (hmem t ht))) hpar.continuousAt
      exact (continuousAt_const.mul hgc).continuousWithinAt
    have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      hcont.intervalIntegrable
    have e1 : a + ((1:ℝ):ℂ) * (b - a) = b := by push_cast; ring
    have e0 : a + ((0:ℝ):ℂ) * (b - a) = a := by push_cast; ring
    have hval : segmentIntegral f a b
        = ∫ t in (0:ℝ)..1, (b - a) * f (a + (t:ℂ) * (b - a)) := by
      unfold segmentIntegral
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [Complex.real_smul]
    rw [hval, hkey]
    simp only [e1, e0]
  -- ================================================================
  -- STAGE 2: local primitives on balls inside `T` (Mathlib disk theory).
  -- ================================================================
  have hlocal : ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → Metric.ball c ρ ⊆ T →
      ∃ F : ℂ → ℂ, ∀ w ∈ Metric.ball c ρ, HasDerivAt F (f w) w := by
    intro c ρ _ hball
    exact (hf.mono hball).isExactOn_ball
  -- ================================================================
  -- STAGE 3: combinatorial integral calculus for grid paths.
  -- ================================================================
  -- Segment antisymmetry via the substitution `t ↦ 1 - t`.
  have hanti : ∀ a b : ℂ, segmentIntegral f b a = -segmentIntegral f a b := by
    intro a b
    have harg : ∀ t : ℝ, b + (1 - t) • (a - b) = a + t • (b - a) := by
      intro t
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hflip := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun s : ℝ => (a - b) * f (b + s • (a - b))) 1
    simp only [sub_self, sub_zero] at hflip
    have hcong : (∫ t in (0:ℝ)..1, (a - b) * f (b + (1 - t) • (a - b)))
        = ∫ t in (0:ℝ)..1, -((b - a) * f (a + t • (b - a))) :=
      intervalIntegral.integral_congr (fun t _ => by rw [harg t]; ring)
    calc segmentIntegral f b a
        = ∫ t in (0:ℝ)..1, (a - b) * f (b + t • (a - b)) := rfl
      _ = ∫ t in (0:ℝ)..1, (a - b) * f (b + (1 - t) • (a - b)) := hflip.symm
      _ = ∫ t in (0:ℝ)..1, -((b - a) * f (a + t • (b - a))) := hcong
      _ = -segmentIntegral f a b := by
          rw [intervalIntegral.integral_neg]; rfl
  -- Append additivity (shared junction vertex).
  have happend : ∀ (δ : ℝ) (L₁ L₂ : List (ℤ × ℤ)) (j : ℤ × ℤ),
      L₁.getLast? = some j → L₂.head? = some j →
      gridPathIntegral f δ (L₁ ++ L₂.tail) =
        gridPathIntegral f δ L₁ + gridPathIntegral f δ L₂ := by
    intro δ L₁ L₂ j hlast hhead
    cases L₂ with
    | nil => simp at hhead
    | cons b t =>
      have hbj : b = j := by simpa using hhead
      subst hbj
      clear hhead
      revert hlast
      induction L₁ with
      | nil => intro hlast; simp at hlast
      | cons p rest ih =>
        intro hlast
        cases rest with
        | nil =>
          have hpj : p = b := by simpa using hlast
          subst hpj
          simp [gridPathIntegral]
        | cons q L =>
          have hlast' : (q :: L).getLast? = some b := by
            rwa [List.getLast?_cons_cons] at hlast
          have ihv := ih hlast'
          simp only [List.cons_append, List.tail_cons, gridPathIntegral] at ihv ⊢
          rw [ihv]
          ring
  -- Reversal negates (segment antisymmetry via `t ↦ 1 - t`).
  have hrev : ∀ (δ : ℝ) (L : List (ℤ × ℤ)),
      gridPathIntegral f δ L.reverse = -gridPathIntegral f δ L := by
    intro δ L
    induction L with
    | nil => simp [gridPathIntegral]
    | cons p rest ih =>
      cases rest with
      | nil => simp [gridPathIntegral]
      | cons q L' =>
        have hLast : (q :: L').reverse.getLast? = some q := by
          rw [List.getLast?_reverse]
          rfl
        have hApp := happend δ ((q :: L').reverse) [q, p] q hLast rfl
        have hrw : (p :: q :: L').reverse = (q :: L').reverse ++ [p] := by
          simp [List.reverse_cons]
        rw [hrw]
        have htl : ([q, p] : List (ℤ × ℤ)).tail = [p] := rfl
        rw [htl] at hApp
        rw [hApp, ih]
        simp only [gridPathIntegral]
        rw [hanti (gridPoint δ p) (gridPoint δ q)]
        ring
  -- Structural helpers for lists of lattice points.
  have hheadne : ∀ (L : List (ℤ × ℤ)) (x : ℤ × ℤ), L.head? = some x → L ≠ [] := by
    intro L x h hnil
    subst hnil
    simp at h
  have hlast_cons : ∀ (a : ℤ × ℤ) (l : List (ℤ × ℤ)), l ≠ [] →
      (a :: l).getLast? = l.getLast? := by
    intro a l hl
    cases l with
    | nil => exact absurd rfl hl
    | cons c s => rw [List.getLast?_cons_cons]
  -- Gluing of grid paths at a shared junction vertex.
  have hglue : ∀ (L₁ L₂ : List (ℤ × ℤ)) (j : ℤ × ℤ), IsGridPath L₁ → IsGridPath L₂ →
      L₁.getLast? = some j → L₂.head? = some j →
      IsGridPath (L₁ ++ L₂.tail) ∧ (L₁ ++ L₂.tail).head? = L₁.head? ∧
        (L₁ ++ L₂.tail).getLast? = L₂.getLast? := by
    intro L₁ L₂ j h1 h2 hl1 hh2
    cases L₂ with
    | nil => simp at hh2
    | cons b t =>
      have hbj : b = j := by simpa using hh2
      subst hbj
      refine ⟨?_, ?_, ?_⟩
      · show List.IsChain GridAdj (L₁ ++ (b :: t).tail)
        rw [List.tail_cons, List.isChain_append]
        refine ⟨h1, (List.isChain_cons.mp h2).2, ?_⟩
        intro x hx y hy
        rw [hl1] at hx
        have hxj : b = x := by simpa using hx
        subst hxj
        exact (List.isChain_cons.mp h2).1 y hy
      · cases L₁ with
        | nil => simp at hl1
        | cons a s => rfl
      · cases t with
        | nil => simpa using hl1
        | cons c s =>
          rw [List.tail_cons, List.getLast?_append_cons, List.getLast?_cons_cons]
  -- The trace of a grid path all of whose vertices lie in a convex set is
  -- contained in that set.
  have htrace_sub : ∀ (δ : ℝ) (S : Set ℂ), Convex ℝ S →
      ∀ L : List (ℤ × ℤ), (∀ v ∈ L, gridPoint δ v ∈ S) →
      gridPathTrace δ L ⊆ S := by
    intro δ S hS L
    induction L with
    | nil => intro _; simp [gridPathTrace]
    | cons a l ih =>
      cases l with
      | nil =>
        intro hv
        simp only [gridPathTrace, Set.singleton_subset_iff]
        exact hv a (by simp)
      | cons b t =>
        intro hv
        simp only [gridPathTrace]
        apply Set.union_subset
        · exact hS.segment_subset (hv a (by simp)) (hv b (by simp))
        · exact ih (fun v hvm => hv v (List.mem_cons_of_mem _ hvm))
  -- Real coordinates of lattice points.
  have hcoord : ∀ (δ : ℝ) (v : ℤ × ℤ),
      (gridPoint δ v).re = δ * (v.1 : ℝ) ∧ (gridPoint δ v).im = δ * (v.2 : ℝ) := by
    intro δ v
    constructor <;> simp [gridPoint]
  have hnormB : ∀ z : ℂ, ‖z‖ ≤ |z.re| + |z.im| := by
    intro z
    calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by simp
  -- Horizontal straight walks along a row of the lattice.
  have hwalkH : ∀ (n : ℕ) (x y j : ℤ), (y - x).natAbs = n →
      ∃ L : List (ℤ × ℤ), IsGridPath L ∧ L.head? = some (x, j) ∧
        L.getLast? = some (y, j) ∧
        ∀ v ∈ L, v.2 = j ∧ ((x ≤ v.1 ∧ v.1 ≤ y) ∨ (y ≤ v.1 ∧ v.1 ≤ x)) := by
    intro n
    induction n with
    | zero =>
      intro x y j hn
      have hxy : x = y := by omega
      subst hxy
      refine ⟨[(x, j)], List.isChain_singleton _, by simp, by simp, ?_⟩
      intro v hv
      have hv' : v = (x, j) := by simpa using hv
      subst hv'
      exact ⟨rfl, Or.inl ⟨le_refl x, le_refl x⟩⟩
    | succ m ih =>
      intro x y j hn
      rcases lt_or_gt_of_ne (show x ≠ y by omega) with hlt | hgt
      · obtain ⟨L', hL', hh', hl', hb'⟩ := ih (x + 1) y j (by omega)
        refine ⟨(x, j) :: L', ?_, rfl, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hL'⟩
          intro y' hy'
          rw [hh'] at hy'
          have hy'' : (x + 1, j) = y' := by simpa using hy'
          subst hy''
          refine Or.inr ⟨?_, rfl⟩
          show (x - (x + 1)).natAbs = 1
          omega
        · rw [hlast_cons _ _ (hheadne L' _ hh')]
          exact hl'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, Or.inl ⟨le_refl x, hlt.le⟩⟩
          · obtain ⟨h2, hb⟩ := hb' v hv'
            exact ⟨h2, by omega⟩
      · obtain ⟨L', hL', hh', hl', hb'⟩ := ih (x - 1) y j (by omega)
        refine ⟨(x, j) :: L', ?_, rfl, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hL'⟩
          intro y' hy'
          rw [hh'] at hy'
          have hy'' : (x - 1, j) = y' := by simpa using hy'
          subst hy''
          refine Or.inr ⟨?_, rfl⟩
          show (x - (x - 1)).natAbs = 1
          omega
        · rw [hlast_cons _ _ (hheadne L' _ hh')]
          exact hl'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, Or.inr ⟨hgt.le, le_refl x⟩⟩
          · obtain ⟨h2, hb⟩ := hb' v hv'
            exact ⟨h2, by omega⟩
  -- Vertical straight walks along a column of the lattice.
  have hwalkV : ∀ (n : ℕ) (i x y : ℤ), (y - x).natAbs = n →
      ∃ L : List (ℤ × ℤ), IsGridPath L ∧ L.head? = some (i, x) ∧
        L.getLast? = some (i, y) ∧
        ∀ v ∈ L, v.1 = i ∧ ((x ≤ v.2 ∧ v.2 ≤ y) ∨ (y ≤ v.2 ∧ v.2 ≤ x)) := by
    intro n
    induction n with
    | zero =>
      intro i x y hn
      have hxy : x = y := by omega
      subst hxy
      refine ⟨[(i, x)], List.isChain_singleton _, by simp, by simp, ?_⟩
      intro v hv
      have hv' : v = (i, x) := by simpa using hv
      subst hv'
      exact ⟨rfl, Or.inl ⟨le_refl x, le_refl x⟩⟩
    | succ m ih =>
      intro i x y hn
      rcases lt_or_gt_of_ne (show x ≠ y by omega) with hlt | hgt
      · obtain ⟨L', hL', hh', hl', hb'⟩ := ih i (x + 1) y (by omega)
        refine ⟨(i, x) :: L', ?_, rfl, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hL'⟩
          intro y' hy'
          rw [hh'] at hy'
          have hy'' : (i, x + 1) = y' := by simpa using hy'
          subst hy''
          refine Or.inl ⟨rfl, ?_⟩
          show (x - (x + 1)).natAbs = 1
          omega
        · rw [hlast_cons _ _ (hheadne L' _ hh')]
          exact hl'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, Or.inl ⟨le_refl x, hlt.le⟩⟩
          · obtain ⟨h2, hb⟩ := hb' v hv'
            exact ⟨h2, by omega⟩
      · obtain ⟨L', hL', hh', hl', hb'⟩ := ih i (x - 1) y (by omega)
        refine ⟨(i, x) :: L', ?_, rfl, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hL'⟩
          intro y' hy'
          rw [hh'] at hy'
          have hy'' : (i, x - 1) = y' := by simpa using hy'
          subst hy''
          refine Or.inl ⟨rfl, ?_⟩
          show (x - (x - 1)).natAbs = 1
          omega
        · rw [hlast_cons _ _ (hheadne L' _ hh')]
          exact hl'
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact ⟨rfl, Or.inr ⟨hgt.le, le_refl x⟩⟩
          · obtain ⟨h2, hb⟩ := hb' v hv'
            exact ⟨h2, by omega⟩
  -- Doubling and midpoint arithmetic for lattice points.
  have hgp2 : ∀ (δ : ℝ) (r : ℤ × ℤ),
      gridPoint (δ / 2) (2 * r.1, 2 * r.2) = gridPoint δ r := by
    intro δ r
    unfold gridPoint
    push_cast
    ring
  have hgpmid : ∀ (δ : ℝ) (r s : ℤ × ℤ),
      gridPoint (δ / 2) (r.1 + s.1, r.2 + s.2) =
        (gridPoint δ r + gridPoint δ s) / 2 := by
    intro δ r s
    unfold gridPoint
    push_cast
    ring
  have hmid_mem : ∀ A B : ℂ, (A + B) / 2 ∈ segment ℝ A B := by
    intro A B
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    ring
  -- Midpoint splitting of a segment integral (inside the domain).
  have hsplit : ∀ A B : ℂ, segment ℝ A B ⊆ T →
      segmentIntegral f A B =
        segmentIntegral f A ((A + B) / 2) + segmentIntegral f ((A + B) / 2) B := by
    intro A B hsub
    have hparc : Continuous fun s : ℝ => A + (s:ℂ) * (B - A) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hmemT : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → A + (t:ℂ) * (B - A) ∈ T := by
      intro t ht
      refine hsub ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_⟩
      simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hgcont : ContinuousOn (fun u : ℝ => (B - A) * f (A + (u:ℂ) * (B - A)))
        (Set.Icc (0:ℝ) 1) := by
      intro t ht
      have hgc : ContinuousAt (fun s : ℝ => f (A + (s:ℂ) * (B - A))) t :=
        ContinuousAt.comp (x := t) (g := f)
          (f := fun s : ℝ => A + (s:ℂ) * (B - A))
          (hfc _ (hmemT t ht)) hparc.continuousAt
      exact (continuousAt_const.mul hgc).continuousWithinAt
    have hint1 : IntervalIntegrable (fun u : ℝ => (B - A) * f (A + (u:ℂ) * (B - A)))
        MeasureTheory.volume 0 (1/2) := by
      apply ContinuousOn.intervalIntegrable
      apply hgcont.mono
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
      exact Set.Icc_subset_Icc (le_refl _) (by norm_num)
    have hint2 : IntervalIntegrable (fun u : ℝ => (B - A) * f (A + (u:ℂ) * (B - A)))
        MeasureTheory.volume (1/2) 1 := by
      apply ContinuousOn.intervalIntegrable
      apply hgcont.mono
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc (by norm_num) (le_refl _)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hfull : segmentIntegral f A B
        = ∫ u in (0:ℝ)..1, (B - A) * f (A + (u:ℂ) * (B - A)) := by
      unfold segmentIntegral
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [Complex.real_smul]
    have hhalf1 : segmentIntegral f A ((A + B) / 2)
        = ∫ u in (0:ℝ)..(1/2), (B - A) * f (A + (u:ℂ) * (B - A)) := by
      have hcomp := intervalIntegral.smul_integral_comp_mul_add
        (a := (0:ℝ)) (b := 1)
        (fun u : ℝ => (B - A) * f (A + (u:ℂ) * (B - A))) (1/2) 0
      have hb0 : (1/2 : ℝ) * 0 + 0 = 0 := by norm_num
      have hb1 : (1/2 : ℝ) * 1 + 0 = 1/2 := by norm_num
      rw [hb0, hb1] at hcomp
      calc segmentIntegral f A ((A + B) / 2)
          = ∫ t in (0:ℝ)..1, ((A + B) / 2 - A) * f (A + t • ((A + B) / 2 - A)) := rfl
        _ = ∫ t in (0:ℝ)..1, (1/2 : ℝ) •
              ((B - A) * f (A + ((1/2 * t + 0 : ℝ) : ℂ) * (B - A))) := by
            refine intervalIntegral.integral_congr fun t _ => ?_
            have earg : A + t • ((A + B) / 2 - A)
                = A + ((1/2 * t + 0 : ℝ) : ℂ) * (B - A) := by
              simp only [Complex.real_smul]
              push_cast
              ring
            rw [earg]
            simp only [Complex.real_smul]
            push_cast
            ring
        _ = (1/2 : ℝ) • ∫ t in (0:ℝ)..1,
              (B - A) * f (A + ((1/2 * t + 0 : ℝ) : ℂ) * (B - A)) :=
            intervalIntegral.integral_smul _ _
        _ = ∫ u in (0:ℝ)..(1/2), (B - A) * f (A + (u:ℂ) * (B - A)) := hcomp
    have hhalf2 : segmentIntegral f ((A + B) / 2) B
        = ∫ u in (1/2:ℝ)..1, (B - A) * f (A + (u:ℂ) * (B - A)) := by
      have hcomp := intervalIntegral.smul_integral_comp_mul_add
        (a := (0:ℝ)) (b := 1)
        (fun u : ℝ => (B - A) * f (A + (u:ℂ) * (B - A))) (1/2) (1/2)
      have hb0 : (1/2 : ℝ) * 0 + 1/2 = 1/2 := by norm_num
      have hb1 : (1/2 : ℝ) * 1 + 1/2 = 1 := by norm_num
      rw [hb0, hb1] at hcomp
      calc segmentIntegral f ((A + B) / 2) B
          = ∫ t in (0:ℝ)..1, (B - (A + B) / 2) *
              f ((A + B) / 2 + t • (B - (A + B) / 2)) := rfl
        _ = ∫ t in (0:ℝ)..1, (1/2 : ℝ) •
              ((B - A) * f (A + ((1/2 * t + 1/2 : ℝ) : ℂ) * (B - A))) := by
            refine intervalIntegral.integral_congr fun t _ => ?_
            have earg : (A + B) / 2 + t • (B - (A + B) / 2)
                = A + ((1/2 * t + 1/2 : ℝ) : ℂ) * (B - A) := by
              simp only [Complex.real_smul]
              push_cast
              ring
            rw [earg]
            simp only [Complex.real_smul]
            push_cast
            ring
        _ = (1/2 : ℝ) • ∫ t in (0:ℝ)..1,
              (B - A) * f (A + ((1/2 * t + 1/2 : ℝ) : ℂ) * (B - A)) :=
            intervalIntegral.integral_smul _ _
        _ = ∫ u in (1/2:ℝ)..1, (B - A) * f (A + (u:ℂ) * (B - A)) := hcomp
    rw [hfull, hhalf1, hhalf2, ← hadd]
  -- Midpoint union of segments.
  have hsegunion : ∀ A B : ℂ,
      segment ℝ A ((A + B) / 2) ∪ segment ℝ ((A + B) / 2) B = segment ℝ A B := by
    intro A B
    apply Set.Subset.antisymm
    · apply Set.union_subset
      · exact (convex_segment A B).segment_subset (left_mem_segment ℝ A B)
          (hmid_mem A B)
      · exact (convex_segment A B).segment_subset (hmid_mem A B)
          (right_mem_segment ℝ A B)
    · rintro x ⟨s, t, hs, ht, hst, rfl⟩
      have hs' : s = 1 - t := by linarith
      subst hs'
      rcases le_total t (1/2) with h | h
      · left
        refine ⟨1 - 2*t, 2*t, by linarith, by linarith, by ring, ?_⟩
        simp only [Complex.real_smul]
        push_cast
        ring
      · right
        refine ⟨2 - 2*t, 2*t - 1, by linarith, by linarith, by ring, ?_⟩
        simp only [Complex.real_smul]
        push_cast
        ring
  -- Doubled and midpoint lattice points inherit adjacency.
  have hadj2 : ∀ p q : ℤ × ℤ, GridAdj p q →
      GridAdj (2*p.1, 2*p.2) (p.1+q.1, p.2+q.2) ∧
        GridAdj (p.1+q.1, p.2+q.2) (2*q.1, 2*q.2) := by
    intro p q h
    simp only [GridAdj] at h ⊢
    omega
  -- The refinement operation: double indices, intersperse midpoints.
  obtain ⟨refineL, hrefL_nil, hrefL_single, hrefL_cons⟩ :
      ∃ refineL : List (ℤ × ℤ) → List (ℤ × ℤ),
        refineL [] = [] ∧ (∀ p, refineL [p] = [(2*p.1, 2*p.2)]) ∧
        (∀ p q t, refineL (p :: q :: t) =
          (2*p.1, 2*p.2) :: (p.1+q.1, p.2+q.2) :: refineL (q :: t)) := by
    refine ⟨fun L => List.rec [] (fun p rest ih =>
      match rest, ih with
      | [], _ => [(2*p.1, 2*p.2)]
      | q :: _, ih => (2*p.1, 2*p.2) :: (p.1+q.1, p.2+q.2) :: ih) L,
      rfl, fun p => rfl, fun p q t => rfl⟩
  have hrefL_head_cons : ∀ (q : ℤ × ℤ) (t : List (ℤ × ℤ)),
      ∃ M, refineL (q :: t) = (2*q.1, 2*q.2) :: M := by
    intro q t
    cases t with
    | nil => exact ⟨[], hrefL_single q⟩
    | cons r t' => exact ⟨_, hrefL_cons q r t'⟩
  -- Refinement preserves grid-path-ness.
  have hrefine_path : ∀ L : List (ℤ × ℤ), IsGridPath L → IsGridPath (refineL L) := by
    intro L
    induction L with
    | nil => intro _; rw [hrefL_nil]; exact List.isChain_nil
    | cons p rest ih =>
      cases rest with
      | nil => intro _; rw [hrefL_single]; exact List.isChain_singleton _
      | cons q t =>
        intro hL
        obtain ⟨M, hM⟩ := hrefL_head_cons q t
        have hadjpq : GridAdj p q := List.IsChain.rel_head hL
        have htail : IsGridPath (q :: t) := List.IsChain.tail hL
        have hih := ih htail
        rw [hM] at hih
        rw [hrefL_cons, hM]
        refine List.isChain_cons_cons.mpr ⟨(hadj2 p q hadjpq).1, ?_⟩
        exact List.isChain_cons_cons.mpr ⟨(hadj2 p q hadjpq).2, hih⟩
  -- Refinement head/last bookkeeping.
  have hrefine_head : ∀ L : List (ℤ × ℤ),
      (refineL L).head? = (L.head?.map fun r => (2*r.1, 2*r.2)) := by
    intro L
    cases L with
    | nil => rw [hrefL_nil]; rfl
    | cons p rest =>
      cases rest with
      | nil => rw [hrefL_single]; rfl
      | cons q t => rw [hrefL_cons]; rfl
  have hrefine_last : ∀ L : List (ℤ × ℤ),
      (refineL L).getLast? = (L.getLast?.map fun r => (2*r.1, 2*r.2)) := by
    intro L
    induction L with
    | nil => rw [hrefL_nil]; rfl
    | cons p rest ih =>
      cases rest with
      | nil => rw [hrefL_single]; rfl
      | cons q t =>
        obtain ⟨M, hM⟩ := hrefL_head_cons q t
        rw [hrefL_cons]
        rw [hlast_cons _ _ (by simp), hlast_cons _ _ (by rw [hM]; simp)]
        rw [ih, List.getLast?_cons_cons]
  -- Refinement preserves the trace.
  have hrefine_trace : ∀ (δ : ℝ) (L : List (ℤ × ℤ)),
      gridPathTrace (δ / 2) (refineL L) = gridPathTrace δ L := by
    intro δ L
    induction L with
    | nil => rw [hrefL_nil]; rfl
    | cons p rest ih =>
      cases rest with
      | nil =>
        rw [hrefL_single]
        show {gridPoint (δ/2) (2*p.1, 2*p.2)} = {gridPoint δ p}
        rw [hgp2]
      | cons q t =>
        obtain ⟨M, hM⟩ := hrefL_head_cons q t
        rw [hrefL_cons, hM]
        rw [hM] at ih
        show segment ℝ (gridPoint (δ/2) (2*p.1, 2*p.2))
            (gridPoint (δ/2) (p.1+q.1, p.2+q.2)) ∪
          (segment ℝ (gridPoint (δ/2) (p.1+q.1, p.2+q.2))
            (gridPoint (δ/2) (2*q.1, 2*q.2)) ∪
            gridPathTrace (δ/2) ((2*q.1, 2*q.2) :: M)) =
          segment ℝ (gridPoint δ p) (gridPoint δ q) ∪ gridPathTrace δ (q :: t)
        rw [hgp2 δ p, hgp2 δ q, hgpmid δ p q, ih, ← Set.union_assoc,
          hsegunion (gridPoint δ p) (gridPoint δ q)]
  -- Refinement preserves the integral (inside the domain).
  have hrefine_integral : ∀ (δ : ℝ) (L : List (ℤ × ℤ)),
      gridPathTrace δ L ⊆ T →
      gridPathIntegral f (δ / 2) (refineL L) = gridPathIntegral f δ L := by
    intro δ L
    induction L with
    | nil => intro _; rw [hrefL_nil]; rfl
    | cons p rest ih =>
      cases rest with
      | nil => intro _; rw [hrefL_single]; rfl
      | cons q t =>
        intro hsub
        have hsub_seg : segment ℝ (gridPoint δ p) (gridPoint δ q) ⊆ T :=
          fun x hx => hsub (Set.mem_union_left _ hx)
        have hsub_tail : gridPathTrace δ (q :: t) ⊆ T :=
          fun x hx => hsub (Set.mem_union_right _ hx)
        obtain ⟨M, hM⟩ := hrefL_head_cons q t
        have hih := ih hsub_tail
        rw [hM] at hih
        rw [hrefL_cons, hM]
        show segmentIntegral f (gridPoint (δ/2) (2*p.1, 2*p.2))
            (gridPoint (δ/2) (p.1+q.1, p.2+q.2)) +
          (segmentIntegral f (gridPoint (δ/2) (p.1+q.1, p.2+q.2))
            (gridPoint (δ/2) (2*q.1, 2*q.2)) +
            gridPathIntegral f (δ/2) ((2*q.1, 2*q.2) :: M)) =
          segmentIntegral f (gridPoint δ p) (gridPoint δ q) +
            gridPathIntegral f δ (q :: t)
        rw [hgp2 δ p, hgp2 δ q, hgpmid δ p q, hih,
          hsplit (gridPoint δ p) (gridPoint δ q) hsub_seg]
        ring
  -- Bridge walks: lattice points inside a small ball are joined by a grid
  -- path staying in a slightly larger ball (L-shaped walk).
  have hbridge : ∀ (δ : ℝ), 0 < δ → ∀ (c : ℂ) (p q : ℤ × ℤ),
      gridPoint δ p ∈ Metric.ball c (8 * δ) → gridPoint δ q ∈ Metric.ball c (8 * δ) →
      ∃ L : List (ℤ × ℤ), IsGridPath L ∧ L.head? = some p ∧ L.getLast? = some q ∧
        gridPathTrace δ L ⊆ Metric.ball c (40 * δ) := by
    intro δ hδ c p q hp hq
    obtain ⟨H, hH, hHh, hHl, hHb⟩ := hwalkH (q.1 - p.1).natAbs p.1 q.1 p.2 rfl
    obtain ⟨V, hV, hVh, hVl, hVb⟩ := hwalkV (q.2 - p.2).natAbs q.1 p.2 q.2 rfl
    obtain ⟨hW, hWh, hWl⟩ := hglue H V (q.1, p.2) hH hV hHl hVh
    have hcomp_bound : ∀ (r : ℤ × ℤ), gridPoint δ r ∈ Metric.ball c (8 * δ) →
        |δ * (r.1 : ℝ) - c.re| < 8 * δ ∧ |δ * (r.2 : ℝ) - c.im| < 8 * δ := by
      intro r hr
      have hn : ‖gridPoint δ r - c‖ < 8 * δ := by
        rwa [Metric.mem_ball, dist_eq_norm] at hr
      constructor
      · have h1 : |(gridPoint δ r - c).re| ≤ ‖gridPoint δ r - c‖ :=
          Complex.abs_re_le_norm _
        rw [Complex.sub_re, (hcoord δ r).1] at h1
        linarith
      · have h1 : |(gridPoint δ r - c).im| ≤ ‖gridPoint δ r - c‖ :=
          Complex.abs_im_le_norm _
        rw [Complex.sub_im, (hcoord δ r).2] at h1
        linarith
    obtain ⟨hpre, hpim⟩ := hcomp_bound p hp
    obtain ⟨hqre, hqim⟩ := hcomp_bound q hq
    refine ⟨H ++ V.tail, hW, ?_, ?_, ?_⟩
    · rw [hWh, hHh]
    · rw [hWl, hVl]
    · apply htrace_sub δ _ (convex_ball c (40 * δ))
      intro v hv
      have hvmem : v ∈ H ∨ v ∈ V := by
        rcases List.mem_append.mp hv with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_of_mem_tail h)
      have hvre : |δ * (v.1 : ℝ) - c.re| < 8 * δ := by
        have hb : (p.1 ≤ v.1 ∧ v.1 ≤ q.1) ∨ (q.1 ≤ v.1 ∧ v.1 ≤ p.1) := by
          rcases hvmem with h | h
          · exact (hHb v h).2
          · have h1 := (hVb v h).1
            omega
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        · have s1 : δ * (min (p.1 : ℝ) (q.1 : ℝ)) ≤ δ * (v.1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hδ.le
            first
            | exact le_trans (min_le_left _ _) (by exact_mod_cast h1)
            | exact le_trans (min_le_right _ _) (by exact_mod_cast h1)
          have s2 : δ * (v.1 : ℝ) ≤ δ * (max (p.1 : ℝ) (q.1 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hδ.le
            first
            | exact le_trans (by exact_mod_cast h2) (le_max_right _ _)
            | exact le_trans (by exact_mod_cast h2) (le_max_left _ _)
          have hinf : min (p.1 : ℝ) (q.1 : ℝ) = p.1 ∨ min (p.1 : ℝ) (q.1 : ℝ) = q.1 :=
            min_choice _ _
          have hsup : max (p.1 : ℝ) (q.1 : ℝ) = p.1 ∨ max (p.1 : ℝ) (q.1 : ℝ) = q.1 :=
            max_choice _ _
          rw [abs_lt] at hpre hqre ⊢
          rcases hinf with h3 | h3 <;> rcases hsup with h4 | h4 <;>
            rw [h3] at s1 <;> rw [h4] at s2 <;> constructor <;> linarith
      have hvim : |δ * (v.2 : ℝ) - c.im| < 8 * δ := by
        have hb : (p.2 ≤ v.2 ∧ v.2 ≤ q.2) ∨ (q.2 ≤ v.2 ∧ v.2 ≤ p.2) := by
          rcases hvmem with h | h
          · have h1 := (hHb v h).1
            omega
          · exact (hVb v h).2
        rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        · have s1 : δ * (min (p.2 : ℝ) (q.2 : ℝ)) ≤ δ * (v.2 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hδ.le
            first
            | exact le_trans (min_le_left _ _) (by exact_mod_cast h1)
            | exact le_trans (min_le_right _ _) (by exact_mod_cast h1)
          have s2 : δ * (v.2 : ℝ) ≤ δ * (max (p.2 : ℝ) (q.2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hδ.le
            first
            | exact le_trans (by exact_mod_cast h2) (le_max_right _ _)
            | exact le_trans (by exact_mod_cast h2) (le_max_left _ _)
          have hinf : min (p.2 : ℝ) (q.2 : ℝ) = p.2 ∨ min (p.2 : ℝ) (q.2 : ℝ) = q.2 :=
            min_choice _ _
          have hsup : max (p.2 : ℝ) (q.2 : ℝ) = p.2 ∨ max (p.2 : ℝ) (q.2 : ℝ) = q.2 :=
            max_choice _ _
          rw [abs_lt] at hpim hqim ⊢
          rcases hinf with h3 | h3 <;> rcases hsup with h4 | h4 <;>
            rw [h3] at s1 <;> rw [h4] at s2 <;> constructor <;> linarith
      have h1 := hnormB (gridPoint δ v - c)
      rw [Complex.sub_re, Complex.sub_im, (hcoord δ v).1, (hcoord δ v).2] at h1
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖gridPoint δ v - c‖
          ≤ |δ * (v.1:ℝ) - c.re| + |δ * (v.2:ℝ) - c.im| := h1
        _ < 8 * δ + 8 * δ := add_lt_add hvre hvim
        _ ≤ 40 * δ := by linarith
  -- ================================================================
  -- STAGE 4: admissible tuples and well-definedness of the grid value.
  -- ================================================================
  -- Scale is `δ = (2 : ℝ)⁻¹ ^ k`; the tuple joins `b`-side to `z`-side.
  set Adm : ℂ → ℂ → ℕ → ℤ × ℤ → ℤ × ℤ → List (ℤ × ℤ) → Prop :=
    fun b z k p q L =>
      IsGridPath L ∧ L.head? = some p ∧ L.getLast? = some q ∧
      gridPathTrace ((2 : ℝ)⁻¹ ^ k) L ⊆ T ∧
      ‖gridPoint ((2 : ℝ)⁻¹ ^ k) p - b‖ ≤ 2 * (2 : ℝ)⁻¹ ^ k ∧
      ‖gridPoint ((2 : ℝ)⁻¹ ^ k) q - z‖ ≤ 2 * (2 : ℝ)⁻¹ ^ k ∧
      Metric.ball b (100 * (2 : ℝ)⁻¹ ^ k) ⊆ T ∧
      Metric.ball z (100 * (2 : ℝ)⁻¹ ^ k) ⊆ T with hAdm_def
  set Val : ℂ → ℂ → ℕ → ℤ × ℤ → ℤ × ℤ → List (ℤ × ℤ) → ℂ :=
    fun b z k p q L =>
      segmentIntegral f b (gridPoint ((2 : ℝ)⁻¹ ^ k) p) +
        gridPathIntegral f ((2 : ℝ)⁻¹ ^ k) L +
        segmentIntegral f (gridPoint ((2 : ℝ)⁻¹ ^ k) q) z with hVal_def
  -- Trace of a glued path is inside the union of traces.
  have htrace_append : ∀ (δ : ℝ) (L₁ L₂ : List (ℤ × ℤ)) (j : ℤ × ℤ),
      L₁.getLast? = some j → L₂.head? = some j →
      gridPathTrace δ (L₁ ++ L₂.tail) ⊆ gridPathTrace δ L₁ ∪ gridPathTrace δ L₂ := by
    intro δ L₁ L₂ j hlast hhead
    cases L₂ with
    | nil => simp at hhead
    | cons b t =>
      have hbj : b = j := by simpa using hhead
      subst hbj
      clear hhead
      revert hlast
      induction L₁ with
      | nil => intro hlast; simp at hlast
      | cons x rest ih =>
        intro hlast
        cases rest with
        | nil =>
          have hxb : x = b := by simpa using hlast
          subst hxb
          simp only [List.cons_append, List.nil_append, List.tail_cons]
          exact fun y hy => Set.mem_union_right _ hy
        | cons y L =>
          have hlast' : (y :: L).getLast? = some b := by
            rwa [List.getLast?_cons_cons] at hlast
          have ihv := ih hlast'
          simp only [List.cons_append] at ihv ⊢
          show segment ℝ (gridPoint δ x) (gridPoint δ y) ∪
              gridPathTrace δ (y :: L ++ (b :: t).tail) ⊆ _
          apply Set.union_subset
          · intro w hw
            exact Set.mem_union_left _ (Set.mem_union_left _ hw)
          · intro w hw
            rcases ihv hw with h | h
            · exact Set.mem_union_left _ (Set.mem_union_right _ h)
            · exact Set.mem_union_right _ h
  -- FTC telescoping along a grid path inside the domain of a primitive.
  have hFTC_path : ∀ (F : ℂ → ℂ) (O : Set ℂ), IsOpen O → O ⊆ T →
      (∀ w ∈ O, HasDerivAt F (f w) w) →
      ∀ (δ : ℝ) (L : List (ℤ × ℤ)) (p q : ℤ × ℤ),
        L.head? = some p → L.getLast? = some q → gridPathTrace δ L ⊆ O →
        gridPathIntegral f δ L = F (gridPoint δ q) - F (gridPoint δ p) := by
    intro F O hO hOT hF δ L
    induction L with
    | nil => intro p q hh _ _; simp at hh
    | cons x rest ih =>
      intro p q hh hl htr
      have hxp : x = p := by simpa using hh
      cases rest with
      | nil =>
        have hpq : x = q := by simpa using hl
        show (0 : ℂ) = _
        rw [← hxp, ← hpq]
        ring
      | cons y L' =>
        have hl' : (y :: L').getLast? = some q := by
          rwa [List.getLast?_cons_cons] at hl
        have htr_seg : segment ℝ (gridPoint δ x) (gridPoint δ y) ⊆ O :=
          fun w hw => htr (Set.mem_union_left _ hw)
        have htr_tail : gridPathTrace δ (y :: L') ⊆ O :=
          fun w hw => htr (Set.mem_union_right _ hw)
        have ihv := ih y q rfl hl' htr_tail
        show segmentIntegral f (gridPoint δ x) (gridPoint δ y) +
            gridPathIntegral f δ (y :: L') = _
        rw [ihv, hFTC F O hO hOT hF _ _ htr_seg, ← hxp]
        ring
  -- Trace of a path extended by one vertex.
  have htrace_snoc : ∀ (δ : ℝ) (L : List (ℤ × ℤ)) (j x : ℤ × ℤ),
      L.getLast? = some j →
      gridPathTrace δ (L ++ [x]) =
        gridPathTrace δ L ∪ segment ℝ (gridPoint δ j) (gridPoint δ x) := by
    intro δ L
    induction L with
    | nil => intro j x hj; simp at hj
    | cons a rest ih =>
      intro j x hj
      cases rest with
      | nil =>
        have haj : a = j := by simpa using hj
        subst haj
        show segment ℝ (gridPoint δ a) (gridPoint δ x) ∪ {gridPoint δ x} =
          {gridPoint δ a} ∪ segment ℝ (gridPoint δ a) (gridPoint δ x)
        apply Set.Subset.antisymm
        · apply Set.union_subset
          · exact Set.subset_union_right
          · exact fun w hw => Set.mem_union_right _
              (by rw [Set.mem_singleton_iff] at hw; rw [hw];
                  exact right_mem_segment ℝ _ _)
        · apply Set.union_subset
          · exact fun w hw => Set.mem_union_left _
              (by rw [Set.mem_singleton_iff] at hw; rw [hw];
                  exact left_mem_segment ℝ _ _)
          · exact Set.subset_union_left
      | cons c t =>
        have hj' : (c :: t).getLast? = some j := by
          rwa [List.getLast?_cons_cons] at hj
        have ihv := ih j x hj'
        show segment ℝ (gridPoint δ a) (gridPoint δ c) ∪
            gridPathTrace δ (c :: (t ++ [x])) = _
        have : gridPathTrace δ (c :: (t ++ [x])) =
            gridPathTrace δ (c :: t) ∪ segment ℝ (gridPoint δ j) (gridPoint δ x) := ihv
        rw [this, ← Set.union_assoc]
        rfl
  -- Trace is invariant under reversal.
  have htrace_reverse : ∀ (δ : ℝ) (L : List (ℤ × ℤ)),
      gridPathTrace δ L.reverse = gridPathTrace δ L := by
    intro δ L
    induction L with
    | nil => rfl
    | cons p rest ih =>
      cases rest with
      | nil => rfl
      | cons q t =>
        have hrw : (p :: q :: t).reverse = (q :: t).reverse ++ [p] := by
          simp [List.reverse_cons]
        have hlast : (q :: t).reverse.getLast? = some q := by
          rw [List.getLast?_reverse]
          rfl
        rw [hrw, htrace_snoc δ _ q p hlast, ih]
        show gridPathTrace δ (q :: t) ∪ segment ℝ (gridPoint δ q) (gridPoint δ p) =
          segment ℝ (gridPoint δ p) (gridPoint δ q) ∪ gridPathTrace δ (q :: t)
        rw [segment_symm, Set.union_comm]
  -- Adjacency is symmetric; grid paths reverse.
  have hadj_symm : ∀ p q : ℤ × ℤ, GridAdj p q → GridAdj q p := by
    intro p q h
    simp only [GridAdj] at h ⊢
    omega
  have hpath_reverse : ∀ L : List (ℤ × ℤ), IsGridPath L → IsGridPath L.reverse := by
    intro L hL
    exact List.isChain_reverse.mpr
      (List.IsChain.imp_of_mem_imp (fun a b _ _ h => hadj_symm a b h) hL)
  -- Nearest lattice point at scale `δ`.
  have hfloor : ∀ (δ : ℝ), 0 < δ → ∀ c : ℂ,
      ∃ r : ℤ × ℤ, ‖gridPoint δ r - c‖ ≤ 2 * δ := by
    intro δ hδ c
    refine ⟨(⌊c.re / δ⌋, ⌊c.im / δ⌋), ?_⟩
    have hre1 : (⌊c.re / δ⌋ : ℝ) ≤ c.re / δ := Int.floor_le _
    have hre2 : c.re / δ < ⌊c.re / δ⌋ + 1 := Int.lt_floor_add_one _
    have him1 : (⌊c.im / δ⌋ : ℝ) ≤ c.im / δ := Int.floor_le _
    have him2 : c.im / δ < ⌊c.im / δ⌋ + 1 := Int.lt_floor_add_one _
    have hre1' : δ * (⌊c.re / δ⌋ : ℝ) ≤ c.re := by
      have := mul_le_mul_of_nonneg_left hre1 hδ.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hδ)] at this
    have hre2' : c.re < δ * (⌊c.re / δ⌋ : ℝ) + δ := by
      have := mul_lt_mul_of_pos_left hre2 hδ
      rw [mul_div_cancel₀ _ (ne_of_gt hδ)] at this
      linarith [this]
    have him1' : δ * (⌊c.im / δ⌋ : ℝ) ≤ c.im := by
      have := mul_le_mul_of_nonneg_left him1 hδ.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hδ)] at this
    have him2' : c.im < δ * (⌊c.im / δ⌋ : ℝ) + δ := by
      have := mul_lt_mul_of_pos_left him2 hδ
      rw [mul_div_cancel₀ _ (ne_of_gt hδ)] at this
      linarith [this]
    have h1 := hnormB (gridPoint δ (⌊c.re / δ⌋, ⌊c.im / δ⌋) - c)
    rw [Complex.sub_re, Complex.sub_im, (hcoord δ _).1, (hcoord δ _).2] at h1
    have hre : |δ * ((⌊c.re / δ⌋, ⌊c.im / δ⌋).1 : ℝ) - c.re| ≤ δ := by
      rw [abs_le]
      constructor <;> simp only [] <;> linarith
    have him : |δ * ((⌊c.re / δ⌋, ⌊c.im / δ⌋).2 : ℝ) - c.im| ≤ δ := by
      rw [abs_le]
      constructor <;> simp only [] <;> linarith
    linarith
  -- Existence of admissible tuples for two points of one component.
  have hEX : ∀ b z : ℂ, b ∈ T → z ∈ T →
      connectedComponentIn T b = connectedComponentIn T z →
      ∃ k p q L, Adm b z k p q L := by
    intro b z hb hz hcomp
    -- The component is open and preconnected.
    set V := connectedComponentIn T b with hV_def
    have hVopen : IsOpen V := hT.connectedComponentIn
    have hVpre : IsPreconnected V := isPreconnected_connectedComponentIn
    have hbV : b ∈ V := mem_connectedComponentIn hb
    have hzV : z ∈ V := by
      have h0 : z ∈ connectedComponentIn T z := mem_connectedComponentIn hz
      rwa [← hcomp] at h0
    have hVT : V ⊆ T := connectedComponentIn_subset T b
    obtain ⟨δ₀, hδ₀, hjoin⟩ := exists_gridPath_join hVopen hVpre hbV hzV
    -- Radii around `b` and `z` inside the open set `T`.
    obtain ⟨rb, hrb, hrbT⟩ := Metric.isOpen_iff.mp hT b hb
    obtain ⟨rz, hrz, hrzT⟩ := Metric.isOpen_iff.mp hT z hz
    -- A dyadic scale below all three bounds.
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
      (lt_min (lt_min hδ₀ (by linarith : (0:ℝ) < rb / 100))
        (by linarith : (0:ℝ) < rz / 100)) (by norm_num : (2:ℝ)⁻¹ < 1)
    have hdyad_pos : (0:ℝ) < (2:ℝ)⁻¹ ^ k := pow_pos (by norm_num) k
    have hkδ₀ : (2:ℝ)⁻¹ ^ k ≤ δ₀ :=
      le_of_lt (lt_of_lt_of_le hk (le_trans (min_le_left _ _) (min_le_left _ _)))
    have hkrb : 100 * (2:ℝ)⁻¹ ^ k ≤ rb := by
      have := lt_of_lt_of_le hk (le_trans (min_le_left _ _) (min_le_right _ _))
      linarith
    have hkrz : 100 * (2:ℝ)⁻¹ ^ k ≤ rz := by
      have := lt_of_lt_of_le hk (min_le_right _ _)
      linarith
    obtain ⟨p, q, L, hL, hh, hl, htr, hpb, hqz⟩ :=
      hjoin ((2:ℝ)⁻¹ ^ k) hdyad_pos hkδ₀
    refine ⟨k, p, q, L, hL, hh, hl, htr.trans hVT, hpb, hqz, ?_, ?_⟩
    · exact fun x hx => hrbT (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hx) hkrb))
    · exact fun x hx => hrzT (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hx) hkrz))
  -- Segments with endpoints near a center stay in the ball (convexity).
  have hseg_ball : ∀ (c A B : ℂ) (r : ℝ), ‖A - c‖ < r → ‖B - c‖ < r →
      segment ℝ A B ⊆ Metric.ball c r := by
    intro c A B r hA hB
    exact (convex_ball c r).segment_subset
      (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
      (Metric.mem_ball.mpr (by rwa [dist_eq_norm]))
  -- Same-scale well-definedness: bridge the near ends, close the circuit,
  -- kill the grid loop by `gridPathIntegral_eq_zero`, and telescope the
  -- ball corrections by `hFTC` with `hlocal` primitives.
  have hWD1 : ∀ b z k p q L p' q' L', Adm b z k p q L → Adm b z k p' q' L' →
      Val b z k p q L = Val b z k p' q' L' := by
    intro b z k p q L p' q' L' hA hA'
    obtain ⟨hL, hh, hl, htr, hpb, hqz, hballb, hballz⟩ := hA
    obtain ⟨hL', hh', hl', htr', hpb', hqz', _, _⟩ := hA'
    set δ : ℝ := (2:ℝ)⁻¹ ^ k with hδ_def
    have hδpos : 0 < δ := pow_pos (by norm_num) k
    -- Balls at the two ends.
    have hball40b : Metric.ball b (40 * δ) ⊆ T := by
      intro x hx
      apply hballb
      rw [Metric.mem_ball] at hx ⊢
      linarith [hx]
    have hball40z : Metric.ball z (40 * δ) ⊆ T := by
      intro x hx
      apply hballz
      rw [Metric.mem_ball] at hx ⊢
      linarith [hx]
    -- All four path endpoints are in the small balls.
    have hp_ball : gridPoint δ p ∈ Metric.ball b (8 * δ) := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hpb]
    have hp'_ball : gridPoint δ p' ∈ Metric.ball b (8 * δ) := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hpb']
    have hq_ball : gridPoint δ q ∈ Metric.ball z (8 * δ) := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hqz]
    have hq'_ball : gridPoint δ q' ∈ Metric.ball z (8 * δ) := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith [hqz']
    -- Bridges: `q → q'` near `z`, and `p' → p` near `b`.
    obtain ⟨Bq, hBq, hBqh, hBql, hBqtr⟩ := hbridge δ hδpos z q q' hq_ball hq'_ball
    obtain ⟨Bp, hBp, hBph, hBpl, hBptr⟩ := hbridge δ hδpos b p' p hp'_ball hp_ball
    -- The reversed second path.
    have hrevL' : IsGridPath L'.reverse := hpath_reverse L' hL'
    have hrevL'_h : L'.reverse.head? = some q' := by
      rw [List.head?_reverse, hl']
    have hrevL'_l : L'.reverse.getLast? = some p' := by
      rw [List.getLast?_reverse, hh']
    -- Assemble the closed circuit `W`.
    obtain ⟨hW1, hW1h, hW1l⟩ := hglue L Bq q hL hBq hl hBqh
    obtain ⟨hW2, hW2h, hW2l⟩ := hglue (L ++ Bq.tail) L'.reverse q' hW1 hrevL'
      (by rw [hW1l, hBql]) hrevL'_h
    obtain ⟨hW3, hW3h, hW3l⟩ := hglue ((L ++ Bq.tail) ++ L'.reverse.tail) Bp p'
      hW2 hBp (by rw [hW2l, hrevL'_l]) hBph
    set W : List (ℤ × ℤ) := (((L ++ Bq.tail) ++ L'.reverse.tail) ++ Bp.tail)
      with hW_def
    have hWh : W.head? = some p := by
      rw [hW3h, hW2h, hW1h, hh]
    have hWl : W.getLast? = some p := by
      rw [hW3l, hBpl]
    have hWne : W ≠ [] := hheadne W p hWh
    have hWcl : W.head? = W.getLast? := by rw [hWh, hWl]
    -- Trace of the circuit is inside `T`.
    have hWtr : gridPathTrace δ W ⊆ T := by
      intro x hx
      have h3 := htrace_append δ ((L ++ Bq.tail) ++ L'.reverse.tail) Bp p'
        (by rw [hW2l, hrevL'_l]) hBph hx
      rcases h3 with h3 | h3
      · have h2 := htrace_append δ (L ++ Bq.tail) L'.reverse q'
          (by rw [hW1l, hBql]) hrevL'_h h3
        rcases h2 with h2 | h2
        · have h1 := htrace_append δ L Bq q hl hBqh h2
          rcases h1 with h1 | h1
          · exact htr h1
          · exact hball40z (hBqtr h1)
        · rw [htrace_reverse] at h2
          exact htr' h2
      · exact hball40b (hBptr h3)
    -- The loop integral vanishes.
    have hWzero : gridPathIntegral f δ W = 0 :=
      gridPathIntegral_eq_zero hT hcompl hf hδpos hW3 hWne hWcl hWtr
    -- Decompose the loop integral.
    have hWint : gridPathIntegral f δ W =
        gridPathIntegral f δ L + gridPathIntegral f δ Bq -
          gridPathIntegral f δ L' + gridPathIntegral f δ Bp := by
      rw [hW_def,
        happend δ ((L ++ Bq.tail) ++ L'.reverse.tail) Bp p'
          (by rw [hW2l, hrevL'_l]) hBph,
        happend δ (L ++ Bq.tail) L'.reverse q' (by rw [hW1l, hBql]) hrevL'_h,
        happend δ L Bq q hl hBqh, hrev δ L']
      ring
    -- Local primitives at both ends.
    obtain ⟨Fb, hFb⟩ := hlocal b (40 * δ) (by linarith) hball40b
    obtain ⟨Fz, hFz⟩ := hlocal z (40 * δ) (by linarith) hball40z
    -- FTC values for all six small pieces.
    have hsegP : segmentIntegral f b (gridPoint δ p) =
        Fb (gridPoint δ p) - Fb b := by
      apply hFTC Fb _ Metric.isOpen_ball hball40b hFb
      apply hseg_ball
      · simp only [sub_self, norm_zero]; linarith
      · linarith [hpb]
    have hsegP' : segmentIntegral f b (gridPoint δ p') =
        Fb (gridPoint δ p') - Fb b := by
      apply hFTC Fb _ Metric.isOpen_ball hball40b hFb
      apply hseg_ball
      · simp only [sub_self, norm_zero]; linarith
      · linarith [hpb']
    have hsegQ : segmentIntegral f (gridPoint δ q) z =
        Fz z - Fz (gridPoint δ q) := by
      apply hFTC Fz _ Metric.isOpen_ball hball40z hFz
      apply hseg_ball
      · linarith [hqz]
      · simp only [sub_self, norm_zero]; linarith
    have hsegQ' : segmentIntegral f (gridPoint δ q') z =
        Fz z - Fz (gridPoint δ q') := by
      apply hFTC Fz _ Metric.isOpen_ball hball40z hFz
      apply hseg_ball
      · linarith [hqz']
      · simp only [sub_self, norm_zero]; linarith
    have hBq_val : gridPathIntegral f δ Bq =
        Fz (gridPoint δ q') - Fz (gridPoint δ q) :=
      hFTC_path Fz _ Metric.isOpen_ball hball40z hFz δ Bq q q' hBqh hBql hBqtr
    have hBp_val : gridPathIntegral f δ Bp =
        Fb (gridPoint δ p) - Fb (gridPoint δ p') :=
      hFTC_path Fb _ Metric.isOpen_ball hball40b hFb δ Bp p' p hBph hBpl hBptr
    -- Conclude.
    have hmain : gridPathIntegral f δ L - gridPathIntegral f δ L' =
        -(Fz (gridPoint δ q') - Fz (gridPoint δ q)) -
          (Fb (gridPoint δ p) - Fb (gridPoint δ p')) := by
      rw [← hBq_val, ← hBp_val]
      have := hWzero
      rw [hWint] at this
      linear_combination this
    show segmentIntegral f b (gridPoint δ p) + gridPathIntegral f δ L +
        segmentIntegral f (gridPoint δ q) z =
      segmentIntegral f b (gridPoint δ p') + gridPathIntegral f δ L' +
        segmentIntegral f (gridPoint δ q') z
    rw [hsegP, hsegP', hsegQ, hsegQ']
    linear_combination hmain
  -- Scale bump via `hrefine`: admissibility and value survive `k ↦ k + 1`.
  have hWD2 : ∀ b z k p q L, Adm b z k p q L →
      ∃ p' q' L', Adm b z (k + 1) p' q' L' ∧
        Val b z (k + 1) p' q' L' = Val b z k p q L := by
    intro b z k p q L hA
    obtain ⟨hL, hh, hl, htr, hpb, hqz, hballb, hballz⟩ := hA
    set δ : ℝ := (2:ℝ)⁻¹ ^ k with hδ_def
    have hδpos : 0 < δ := pow_pos (by norm_num) k
    have he : (2:ℝ)⁻¹ ^ (k+1) = δ / 2 := by
      rw [pow_succ]
      ring
    have hδ'pos : 0 < δ / 2 := by linarith
    -- Floor lattice points at the finer scale.
    obtain ⟨p'', hp''⟩ := hfloor (δ/2) hδ'pos b
    obtain ⟨q'', hq''⟩ := hfloor (δ/2) hδ'pos z
    -- The refined main path.
    have href_path := hrefine_path L hL
    have href_head := hrefine_head L
    have href_last := hrefine_last L
    have href_trace := hrefine_trace δ L
    have href_int := hrefine_integral δ L htr
    rw [hh] at href_head
    rw [hl] at href_last
    -- Doubled endpoints coincide with the coarse ones.
    have hgp_p : gridPoint (δ/2) (2*p.1, 2*p.2) = gridPoint δ p := hgp2 δ p
    have hgp_q : gridPoint (δ/2) (2*q.1, 2*q.2) = gridPoint δ q := hgp2 δ q
    -- Bridges: `p'' → 2p` near `b`, `2q → q''` near `z`.
    have hp2_ball : gridPoint (δ/2) (2*p.1, 2*p.2) ∈ Metric.ball b (8 * (δ/2)) := by
      rw [Metric.mem_ball, dist_eq_norm, hgp_p]
      calc ‖gridPoint δ p - b‖ ≤ 2 * δ := hpb
        _ < 8 * (δ/2) := by linarith
    have hp''_ball : gridPoint (δ/2) p'' ∈ Metric.ball b (8 * (δ/2)) := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖gridPoint (δ/2) p'' - b‖ ≤ 2 * (δ/2) := hp''
        _ < 8 * (δ/2) := by linarith
    have hq2_ball : gridPoint (δ/2) (2*q.1, 2*q.2) ∈ Metric.ball z (8 * (δ/2)) := by
      rw [Metric.mem_ball, dist_eq_norm, hgp_q]
      calc ‖gridPoint δ q - z‖ ≤ 2 * δ := hqz
        _ < 8 * (δ/2) := by linarith
    have hq''_ball : gridPoint (δ/2) q'' ∈ Metric.ball z (8 * (δ/2)) := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖gridPoint (δ/2) q'' - z‖ ≤ 2 * (δ/2) := hq''
        _ < 8 * (δ/2) := by linarith
    obtain ⟨Bp, hBp, hBph, hBpl, hBptr⟩ :=
      hbridge (δ/2) hδ'pos b p'' (2*p.1, 2*p.2) hp''_ball hp2_ball
    obtain ⟨Bq, hBq, hBqh, hBql, hBqtr⟩ :=
      hbridge (δ/2) hδ'pos z (2*q.1, 2*q.2) q'' hq2_ball hq''_ball
    -- Small balls sit inside `T`.
    have hball40b : Metric.ball b (40 * (δ/2)) ⊆ T := by
      intro x hx
      apply hballb
      rw [Metric.mem_ball] at hx ⊢
      calc dist x b < 40 * (δ/2) := hx
        _ ≤ 100 * δ := by linarith
    have hball40z : Metric.ball z (40 * (δ/2)) ⊆ T := by
      intro x hx
      apply hballz
      rw [Metric.mem_ball] at hx ⊢
      calc dist x z < 40 * (δ/2) := hx
        _ ≤ 100 * δ := by linarith
    -- Glue: Bp ++ refined ++ Bq.
    obtain ⟨hW1, hW1h, hW1l⟩ := hglue Bp (refineL L) (2*p.1, 2*p.2) hBp href_path
      hBpl href_head
    obtain ⟨hW2, hW2h, hW2l⟩ := hglue (Bp ++ (refineL L).tail) Bq (2*q.1, 2*q.2)
      hW1 hBq (by rw [hW1l, href_last]; rfl) hBqh
    set W : List (ℤ × ℤ) := (Bp ++ (refineL L).tail) ++ Bq.tail with hW_def
    have hWh : W.head? = some p'' := by
      rw [hW2h, hW1h, hBph]
    have hWl : W.getLast? = some q'' := by
      rw [hW2l, hBql]
    -- Trace of the glued path is inside `T`.
    have hWtr : gridPathTrace (δ/2) W ⊆ T := by
      intro x hx
      have h1 := htrace_append (δ/2) (Bp ++ (refineL L).tail) Bq (2*q.1, 2*q.2)
        (by rw [hW1l, href_last]; rfl) hBqh hx
      rcases h1 with h1 | h1
      · have h2 := htrace_append (δ/2) Bp (refineL L) (2*p.1, 2*p.2)
          hBpl href_head h1
        rcases h2 with h2 | h2
        · exact hball40b (hBptr h2)
        · rw [href_trace] at h2
          exact htr h2
      · exact hball40z (hBqtr h1)
    -- Integral of the glued path.
    have hWint : gridPathIntegral f (δ/2) W =
        gridPathIntegral f (δ/2) Bp + gridPathIntegral f δ L +
          gridPathIntegral f (δ/2) Bq := by
      rw [hW_def, happend (δ/2) (Bp ++ (refineL L).tail) Bq (2*q.1, 2*q.2)
        (by rw [hW1l, href_last]; rfl) hBqh,
        happend (δ/2) Bp (refineL L) (2*p.1, 2*p.2) hBpl href_head, href_int]
    -- Local primitives near `b` and `z`.
    obtain ⟨Fb, hFb⟩ := hlocal b (40 * (δ/2)) (by linarith) hball40b
    obtain ⟨Fz, hFz⟩ := hlocal z (40 * (δ/2)) (by linarith) hball40z
    -- FTC telescoping on the `b` side.
    have hFb_seg1 : segmentIntegral f b (gridPoint (δ/2) p'') =
        Fb (gridPoint (δ/2) p'') - Fb b := by
      apply hFTC Fb _ Metric.isOpen_ball hball40b hFb
      apply hseg_ball
      · simp only [sub_self, norm_zero]; linarith
      · calc ‖gridPoint (δ/2) p'' - b‖ ≤ 2 * (δ/2) := hp''
          _ < 40 * (δ/2) := by linarith
    have hFb_seg2 : segmentIntegral f b (gridPoint δ p) =
        Fb (gridPoint δ p) - Fb b := by
      apply hFTC Fb _ Metric.isOpen_ball hball40b hFb
      apply hseg_ball
      · simp only [sub_self, norm_zero]; linarith
      · calc ‖gridPoint δ p - b‖ ≤ 2 * δ := hpb
          _ < 40 * (δ/2) := by linarith
    have hFb_bridge : gridPathIntegral f (δ/2) Bp =
        Fb (gridPoint δ p) - Fb (gridPoint (δ/2) p'') := by
      have := hFTC_path Fb _ Metric.isOpen_ball hball40b hFb (δ/2) Bp p''
        (2*p.1, 2*p.2) hBph hBpl hBptr
      rwa [hgp_p] at this
    -- FTC telescoping on the `z` side.
    have hFz_seg1 : segmentIntegral f (gridPoint (δ/2) q'') z =
        Fz z - Fz (gridPoint (δ/2) q'') := by
      apply hFTC Fz _ Metric.isOpen_ball hball40z hFz
      apply hseg_ball
      · calc ‖gridPoint (δ/2) q'' - z‖ ≤ 2 * (δ/2) := hq''
          _ < 40 * (δ/2) := by linarith
      · simp only [sub_self, norm_zero]; linarith
    have hFz_seg2 : segmentIntegral f (gridPoint δ q) z =
        Fz z - Fz (gridPoint δ q) := by
      apply hFTC Fz _ Metric.isOpen_ball hball40z hFz
      apply hseg_ball
      · calc ‖gridPoint δ q - z‖ ≤ 2 * δ := hqz
          _ < 40 * (δ/2) := by linarith
      · simp only [sub_self, norm_zero]; linarith
    have hFz_bridge : gridPathIntegral f (δ/2) Bq =
        Fz (gridPoint (δ/2) q'') - Fz (gridPoint δ q) := by
      have := hFTC_path Fz _ Metric.isOpen_ball hball40z hFz (δ/2) Bq
        (2*q.1, 2*q.2) q'' hBqh hBql hBqtr
      rwa [hgp_q] at this
    -- Assemble.
    refine ⟨p'', q'', W, ⟨hW2, hWh, hWl, by rwa [he], ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [he]
      exact hp''
    · rw [he]
      exact hq''
    · intro x hx
      apply hballb
      rw [Metric.mem_ball] at hx ⊢
      rw [he] at hx
      calc dist x b < 100 * (δ/2) := hx
        _ ≤ 100 * δ := by linarith
    · intro x hx
      apply hballz
      rw [Metric.mem_ball] at hx ⊢
      rw [he] at hx
      calc dist x z < 100 * (δ/2) := hx
        _ ≤ 100 * δ := by linarith
    · show segmentIntegral f b (gridPoint ((2:ℝ)⁻¹ ^ (k+1)) p'') +
          gridPathIntegral f ((2:ℝ)⁻¹ ^ (k+1)) W +
          segmentIntegral f (gridPoint ((2:ℝ)⁻¹ ^ (k+1)) q'') z =
        segmentIntegral f b (gridPoint δ p) + gridPathIntegral f δ L +
          segmentIntegral f (gridPoint δ q) z
      rw [he, hWint, hFb_seg1, hFb_seg2, hFb_bridge, hFz_seg1, hFz_seg2, hFz_bridge]
      ring
  -- Full well-definedness across scales (iterate `hWD2` to a common scale,
  -- then `hWD1`).
  -- Iterate `hWD2` any number of steps.
  have hlift : ∀ (n : ℕ) (b z : ℂ) (k : ℕ) (p q : ℤ × ℤ) (L : List (ℤ × ℤ)),
      Adm b z k p q L → ∃ p' q' L', Adm b z (k + n) p' q' L' ∧
        Val b z (k + n) p' q' L' = Val b z k p q L := by
    intro n
    induction n with
    | zero => intro b z k p q L hA; exact ⟨p, q, L, hA, rfl⟩
    | succ m ih =>
      intro b z k p q L hA
      obtain ⟨p₁, q₁, L₁, hA₁, hV₁⟩ := ih b z k p q L hA
      obtain ⟨p₂, q₂, L₂, hA₂, hV₂⟩ := hWD2 b z (k + m) p₁ q₁ L₁ hA₁
      exact ⟨p₂, q₂, L₂, hA₂, by rw [show k + (m+1) = k + m + 1 from rfl, hV₂, hV₁]⟩
  have hWD : ∀ b z k p q L k' p' q' L', Adm b z k p q L → Adm b z k' p' q' L' →
      Val b z k p q L = Val b z k' p' q' L' := by
    intro b z k p q L k' p' q' L' hA hA'
    obtain ⟨p₁, q₁, L₁, hA₁, hV₁⟩ := hlift (max k k' - k) b z k p q L hA
    obtain ⟨p₂, q₂, L₂, hA₂, hV₂⟩ := hlift (max k k' - k') b z k' p' q' L' hA'
    have e1 : k + (max k k' - k) = max k k' := by omega
    have e2 : k' + (max k k' - k') = max k k' := by omega
    rw [e1] at hA₁ hV₁
    rw [e2] at hA₂ hV₂
    rw [← hV₁, ← hV₂]
    exact hWD1 b z (max k k') p₁ q₁ L₁ p₂ q₂ L₂ hA₁ hA₂
  -- ================================================================
  -- STAGE 5: the primitive.
  -- ================================================================
  -- Canonical basepoint of the component of `z` (depends only on the
  -- component as a set, hence constant along the component).
  classical
  set base : ℂ → ℂ := fun z =>
    if hz : z ∈ T then
      Set.Nonempty.some (s := connectedComponentIn T z)
        ⟨z, mem_connectedComponentIn hz⟩ else 0 with hbase_def
  have hbase_in_comp : ∀ z (hz : z ∈ T), base z ∈ connectedComponentIn T z := by
    intro z hz
    simp only [hbase_def, dif_pos hz]
    exact Set.Nonempty.some_mem _
  have hbase_mem : ∀ z ∈ T, base z ∈ T := by
    intro z hz
    exact connectedComponentIn_subset T z (hbase_in_comp z hz)
  have hbase_comp : ∀ z ∈ T, connectedComponentIn T (base z) =
      connectedComponentIn T z := by
    intro z hz
    exact (connectedComponentIn_eq (hbase_in_comp z hz)).symm
  have hbase_const : ∀ z w, w ∈ connectedComponentIn T z → z ∈ T →
      base w = base z := by
    intro z w hw hzT
    have hwT : w ∈ T := connectedComponentIn_subset T z hw
    have hcomp : connectedComponentIn T w = connectedComponentIn T z :=
      (connectedComponentIn_eq hw).symm
    have hkey : ∀ (s₁ s₂ : Set ℂ) (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty),
        s₁ = s₂ → h₁.some = h₂.some := by
      rintro s₁ s₂ h₁ h₂ rfl
      rfl
    simp only [hbase_def, dif_pos hwT, dif_pos hzT]
    exact hkey _ _ _ _ hcomp
  set g : ℂ → ℂ := fun z =>
    if hz : z ∈ T then
      Val (base z) z (hEX (base z) z (hbase_mem z hz) hz
        (hbase_comp z hz)).choose
        (hEX (base z) z (hbase_mem z hz) hz (hbase_comp z hz)).choose_spec.choose
        (hEX (base z) z (hbase_mem z hz) hz
          (hbase_comp z hz)).choose_spec.choose_spec.choose
        (hEX (base z) z (hbase_mem z hz) hz
          (hbase_comp z hz)).choose_spec.choose_spec.choose_spec.choose
    else 0 with hg_def
  -- `g` evaluates as the common value of EVERY admissible tuple.
  have hg_eval : ∀ z (hz : z ∈ T) k p q L, Adm (base z) z k p q L →
      g z = Val (base z) z k p q L := by
    intro z hz k p q L hA
    have hspec := (hEX (base z) z (hbase_mem z hz) hz
      (hbase_comp z hz)).choose_spec.choose_spec.choose_spec.choose_spec
    simp only [hg_def, dif_pos hz]
    exact hWD (base z) z _ _ _ _ k p q L hspec hA
  -- The derivative: near `z₀`, compare `g w` with `F w` for a local
  -- primitive `F` from `hlocal`; the difference is locally constant
  -- (extend an admissible tuple for `z₀` towards `w` inside the ball,
  -- using `hbridge`, `happend`, `hWD`, and `hFTC` telescoping), and a
  -- locally-constant difference on a ball forces
  -- `HasDerivAt g (f z₀) z₀` via `HasDerivAt.congr_of_eventuallyEq`.
  have hderiv : ∀ z₀ ∈ T, HasDerivAt g (f z₀) z₀ := by
    intro z₀ hz₀
    obtain ⟨ρ, hρ, hρT⟩ := Metric.isOpen_iff.mp hT z₀ hz₀
    obtain ⟨F, hF⟩ := hlocal z₀ ρ hρ hρT
    -- A coarse admissible tuple for `z₀`, lifted to a fine dyadic scale.
    obtain ⟨k₀, p₀, q₀, L₀, hA₀⟩ := hEX (base z₀) z₀ (hbase_mem z₀ hz₀) hz₀
      (hbase_comp z₀ hz₀)
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (by linarith : (0:ℝ) < ρ / 1000) (by norm_num : (2:ℝ)⁻¹ < 1)
    obtain ⟨p, q, L, hAk, _⟩ := hlift m (base z₀) z₀ k₀ p₀ q₀ L₀ hA₀
    set k := k₀ + m with hk_def
    obtain ⟨hL, hh, hl, htr, hpb, hqz, hballb, hballz⟩ := hAk
    have hgz₀ : g z₀ = Val (base z₀) z₀ k p q L :=
      hg_eval z₀ hz₀ k p q L ⟨hL, hh, hl, htr, hpb, hqz, hballb, hballz⟩
    set δ : ℝ := (2:ℝ)⁻¹ ^ k with hδ_def
    have hδpos : 0 < δ := pow_pos (by norm_num) k
    have hδρ : δ < ρ / 1000 := by
      calc δ = (2:ℝ)⁻¹ ^ k₀ * (2:ℝ)⁻¹ ^ m := by
            rw [hδ_def, hk_def, pow_add]
        _ ≤ 1 * (2:ℝ)⁻¹ ^ m := by
            apply mul_le_mul_of_nonneg_right _ (pow_pos (by norm_num) m).le
            exact pow_le_one₀ (by norm_num) (by norm_num)
        _ = (2:ℝ)⁻¹ ^ m := one_mul _
        _ < ρ / 1000 := hm
    -- The pointwise comparison on the tiny ball.
    have hcompare : ∀ w ∈ Metric.ball z₀ δ, g w = F w + (g z₀ - F z₀) := by
      intro w hw
      have hwz₀ : ‖w - z₀‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hw
      have hwT : w ∈ T := hρT (Metric.mem_ball.mpr
        (lt_trans (Metric.mem_ball.mp hw) (by linarith)))
      -- `w` is in the component of `z₀`; the basepoint agrees.
      have hw_comp : w ∈ connectedComponentIn T z₀ := by
        apply (convex_ball z₀ ρ).isPreconnected.subset_connectedComponentIn
          (Metric.mem_ball_self hρ) hρT
        exact Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hw) (by linarith))
      have hbw : base w = base z₀ := hbase_const z₀ w hw_comp hz₀
      -- Floor point of `w` and bridge from `q` centred at `w`.
      obtain ⟨qw, hqw⟩ := hfloor δ hδpos w
      have hq_ballw : gridPoint δ q ∈ Metric.ball w (8 * δ) := by
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖gridPoint δ q - w‖ ≤ ‖gridPoint δ q - z₀‖ + ‖z₀ - w‖ := by
              have := norm_add_le (gridPoint δ q - z₀) (z₀ - w)
              simpa using this
          _ ≤ 2 * δ + ‖z₀ - w‖ := by linarith [hqz]
          _ < 8 * δ := by
              have h5 : ‖z₀ - w‖ < δ := by rwa [norm_sub_rev]
              linarith
      have hqw_ballw : gridPoint δ qw ∈ Metric.ball w (8 * δ) := by
        rw [Metric.mem_ball, dist_eq_norm]
        linarith [hqw]
      obtain ⟨B, hB, hBh, hBl, hBtr⟩ := hbridge δ hδpos w q qw hq_ballw hqw_ballw
      -- The bridge ball sits inside `ball z₀ ρ ⊆ T`.
      have hball40w : Metric.ball w (40 * δ) ⊆ Metric.ball z₀ ρ := by
        intro x hx
        rw [Metric.mem_ball] at hx ⊢
        calc dist x z₀ ≤ dist x w + dist w z₀ := dist_triangle _ _ _
          _ < 40 * δ + δ := by
              have h6 : dist w z₀ < δ := by rwa [dist_eq_norm]
              exact add_lt_add hx h6
          _ < ρ := by linarith
      -- The extended path is admissible for `w`.
      obtain ⟨hWp, hWph, hWpl⟩ := hglue L B q hL hB hl hBh
      have hWtr : gridPathTrace δ (L ++ B.tail) ⊆ T := by
        intro x hx
        rcases htrace_append δ L B q hl hBh hx with h | h
        · exact htr h
        · exact hρT (hball40w (hBtr h))
      have hAdm_w : Adm (base w) w k p qw (L ++ B.tail) := by
        rw [hbw]
        refine ⟨hWp, by rw [hWph, hh], by rw [hWpl, hBl], hWtr, hpb, hqw, hballb, ?_⟩
        intro x hx
        apply hρT
        rw [Metric.mem_ball] at hx ⊢
        calc dist x z₀ ≤ dist x w + dist w z₀ := dist_triangle _ _ _
          _ < 100 * δ + δ := by
              have h6 : dist w z₀ < δ := by rwa [dist_eq_norm]
              exact add_lt_add hx h6
          _ < ρ := by linarith
      have hgw : g w = Val (base w) w k p qw (L ++ B.tail) :=
        hg_eval w hwT k p qw (L ++ B.tail) hAdm_w
      -- FTC telescoping of the difference.
      have hB_val : gridPathIntegral f δ B =
          F (gridPoint δ qw) - F (gridPoint δ q) :=
        hFTC_path F _ Metric.isOpen_ball hρT hF δ B q qw hBh hBl
          (fun x hx => hball40w (hBtr hx))
      have hseg_w : segmentIntegral f (gridPoint δ qw) w =
          F w - F (gridPoint δ qw) := by
        apply hFTC F _ Metric.isOpen_ball hρT hF
        apply hseg_ball
        · calc ‖gridPoint δ qw - z₀‖
              ≤ ‖gridPoint δ qw - w‖ + ‖w - z₀‖ := by
                have := norm_add_le (gridPoint δ qw - w) (w - z₀)
                simpa using this
            _ < 2 * δ + δ := add_lt_add_of_le_of_lt hqw hwz₀
            _ < ρ := by linarith
        · linarith [hwz₀]
      have hseg_z₀ : segmentIntegral f (gridPoint δ q) z₀ =
          F z₀ - F (gridPoint δ q) := by
        apply hFTC F _ Metric.isOpen_ball hρT hF
        apply hseg_ball
        · calc ‖gridPoint δ q - z₀‖ ≤ 2 * δ := hqz
            _ < ρ := by linarith
        · simp only [sub_self, norm_zero]; linarith
      have hint_app : gridPathIntegral f δ (L ++ B.tail) =
          gridPathIntegral f δ L + gridPathIntegral f δ B :=
        happend δ L B q hl hBh
      rw [hgw, hgz₀]
      show segmentIntegral f (base w) (gridPoint δ p) +
          gridPathIntegral f δ (L ++ B.tail) +
          segmentIntegral f (gridPoint δ qw) w =
        F w + (segmentIntegral f (base z₀) (gridPoint δ p) +
          gridPathIntegral f δ L + segmentIntegral f (gridPoint δ q) z₀ - F z₀)
      rw [hbw, hint_app, hB_val, hseg_w, hseg_z₀]
      ring
    -- Transfer the derivative from `F + const` to `g`.
    have hFz₀ : HasDerivAt F (f z₀) z₀ := hF z₀ (Metric.mem_ball_self hρ)
    have hconst : HasDerivAt (fun w => F w + (g z₀ - F z₀)) (f z₀) z₀ :=
      hFz₀.add_const _
    have heq : g =ᶠ[nhds z₀] fun w => F w + (g z₀ - F z₀) := by
      filter_upwards [Metric.ball_mem_nhds z₀ hδpos] with w hw
      exact hcompare w hw
    exact hconst.congr_of_eventuallyEq heq
  -- ================================================================
  -- STAGE 6: package `has_primitives` (DifferentiableOn + EqOn deriv).
  -- ================================================================
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact (hderiv z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hderiv z hz).deriv

end RiemannDynamics
