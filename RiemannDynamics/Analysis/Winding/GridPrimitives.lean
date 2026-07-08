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

set_option maxHeartbeats 400000 in
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
  classical
  set γ : C(unitInterval, ℂ) := gridLoopCurve δ L with hγ_def
  set w : ℤ × ℤ → ℤ := fun p => windingNumber γ (gridSquareCenter δ p) with hw_def
  set prs : List ((ℤ × ℤ) × (ℤ × ℤ)) := L.zip L.tail with hprs_def
  -- ================================================================
  -- STAGE 0: coordinate helpers.
  -- ================================================================
  have hgre : ∀ q : ℤ × ℤ, (gridPoint δ q).re = δ * q.1 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hgim : ∀ q : ℤ × ℤ, (gridPoint δ q).im = δ * q.2 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hsegre : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).re = u * a.re + v * b.re := by
    intro a b u v
    simp [Complex.add_re]
  have hsegim : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).im = u * a.im + v * b.im := by
    intro a b u v
    simp [Complex.add_im]
  have hhalf_ne : ∀ n : ℤ, δ / 2 ≠ δ * n := by
    intro n heq
    have h' : δ * (1 / 2 : ℝ) = δ * (n : ℝ) := by linarith
    have h2 : (1 / 2 : ℝ) = (n : ℝ) := mul_left_cancel₀ (ne_of_gt hδ) h'
    have h3 : (2 * n : ℝ) = 1 := by linarith
    have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hcen_re : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).re = δ * p.1 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_re, hgre]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((δ : ℂ) / 2 * (1 + Complex.I)).re = δ / 2 := by
      rw [hh]
      simp [Complex.mul_re]
    rw [h2]
  have hcen_im : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).im = δ * p.2 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_im, hgim]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((δ : ℂ) / 2 * (1 + Complex.I)).im = δ / 2 := by
      rw [hh]
      simp [Complex.mul_im]
    rw [h2]
  -- (0) all square centers avoid all grid-path traces
  have hcenter : ∀ (p : ℤ × ℤ) (M : List (ℤ × ℤ)), IsGridPath M →
      ∀ x ∈ gridPathTrace δ M, gridSquareCenter δ p ≠ x := by
    intro p M
    induction M with
    | nil =>
      intro _ x hx
      simp [gridPathTrace] at hx
    | cons r M ih =>
      intro hpath x hx heq
      cases M with
      | nil =>
        have hxr : x = gridPoint δ r := hx
        have hre := congrArg Complex.re heq
        rw [hcen_re, hxr, hgre] at hre
        exact hhalf_ne (r.1 - p.1) (by push_cast; linarith)
      | cons s M' =>
        rcases hx with hseg | htr
        · have hadj : GridAdj r s := (List.isChain_cons_cons.mp hpath).1
          obtain ⟨u, v', hu, hv', huv, hxe⟩ := hseg
          rcases hadj with ⟨h1, -⟩ | ⟨-, h2⟩
          · have hxre : x.re = δ * r.1 := by
              rw [← hxe, hsegre, hgre, hgre, ← h1]
              have hcomb : u * (δ * (r.1 : ℝ)) + v' * (δ * (r.1 : ℝ)) =
                  (u + v') * (δ * r.1) := by ring
              rw [hcomb, huv, one_mul]
            have hre := congrArg Complex.re heq
            rw [hcen_re, hxre] at hre
            exact hhalf_ne (r.1 - p.1) (by push_cast; linarith)
          · have hxim : x.im = δ * r.2 := by
              rw [← hxe, hsegim, hgim, hgim, ← h2]
              have hcomb : u * (δ * (r.2 : ℝ)) + v' * (δ * (r.2 : ℝ)) =
                  (u + v') * (δ * r.2) := by ring
              rw [hcomb, huv, one_mul]
            have him := congrArg Complex.im heq
            rw [hcen_im, hxim] at him
            exact hhalf_ne (r.2 - p.2) (by push_cast; linarith)
        · exact ih (List.isChain_cons_cons.mp hpath).2 x htr heq
  have hgp_ne_cen : ∀ r p : ℤ × ℤ,
      gridPoint δ r - gridSquareCenter δ p ≠ 0 := by
    intro r p h
    have h1 := congrArg Complex.re h
    rw [Complex.sub_re, hgre, hcen_re, Complex.zero_re] at h1
    exact hhalf_ne (r.1 - p.1) (by push_cast; linarith)
  -- ================================================================
  -- STAGE 1: segment antisymmetry, LHS/RHS decompositions.
  -- ================================================================
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
  have hLHS : ∀ M : List (ℤ × ℤ), gridPathIntegral f δ M =
      ((M.zip M.tail).map
        (fun e => segmentIntegral f (gridPoint δ e.1) (gridPoint δ e.2))).sum := by
    intro M
    induction M with
    | nil => simp [gridPathIntegral]
    | cons p M ih =>
      cases M with
      | nil => simp [gridPathIntegral]
      | cons q M' =>
        show segmentIntegral f (gridPoint δ p) (gridPoint δ q) +
            gridPathIntegral f δ (q :: M') = _
        rw [ih]
        simp only [List.tail_cons, List.zip_cons_cons, List.map_cons,
          List.sum_cons]
  -- consecutive-pair facts
  have hpair_adj : ∀ M : List (ℤ × ℤ), IsGridPath M →
      ∀ e ∈ M.zip M.tail, GridAdj e.1 e.2 := by
    intro M
    induction M with
    | nil => intro _ e he; simp at he
    | cons a M ih =>
      intro hM e he
      cases M with
      | nil => simp at he
      | cons b M' =>
        have hz : (a :: b :: M').zip (a :: b :: M').tail =
            (a, b) :: ((b :: M').zip M') := rfl
        rw [hz] at he
        rcases List.mem_cons.mp he with rfl | he'
        · exact (List.isChain_cons_cons.mp hM).1
        · refine ih (List.isChain_cons_cons.mp hM).2 e ?_
          show e ∈ (b :: M').zip (b :: M').tail
          exact he'
  have hpair_mem : ∀ (M : List (ℤ × ℤ)) (e : (ℤ × ℤ) × (ℤ × ℤ)),
      e ∈ M.zip M.tail → e.1 ∈ M ∧ e.2 ∈ M := by
    rintro M ⟨x, y⟩ he
    have h := List.of_mem_zip he
    exact ⟨h.1, List.mem_of_mem_tail h.2⟩
  have hpair_seg : ∀ (M : List (ℤ × ℤ)) (e : (ℤ × ℤ) × (ℤ × ℤ)),
      e ∈ M.zip M.tail →
      segment ℝ (gridPoint δ e.1) (gridPoint δ e.2) ⊆ gridPathTrace δ M := by
    intro M
    induction M with
    | nil => intro e he; simp at he
    | cons a M ih =>
      intro e he
      cases M with
      | nil => simp at he
      | cons b M' =>
        have hz : (a :: b :: M').zip (a :: b :: M').tail =
            (a, b) :: ((b :: M').zip M') := rfl
        rw [hz] at he
        rcases List.mem_cons.mp he with rfl | he'
        · intro z hz'
          exact Or.inl hz'
        · intro z hz'
          refine Or.inr (ih e ?_ hz')
          show e ∈ (b :: M').zip (b :: M').tail
          exact he'
  have hshape : ∀ e : (ℤ × ℤ) × (ℤ × ℤ), GridAdj e.1 e.2 →
      (e.2 = (e.1.1 + 1, e.1.2)) ∨ (e.1 = (e.2.1 + 1, e.2.2)) ∨
      (e.2 = (e.1.1, e.1.2 + 1)) ∨ (e.1 = (e.2.1, e.2.2 + 1)) := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ he
    simp only [GridAdj] at he
    simp only [Prod.mk.injEq]
    omega
  have hseg_h : ∀ (i j : ℤ), ∀ x ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i + 1, j)),
      x.im = δ * j ∧ δ * i ≤ x.re ∧ x.re ≤ δ * (i + 1) := by
    intro i j x hx
    obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
    have hv1 : v ≤ 1 := by linarith
    have hre : x.re = δ * i + v * δ := by
      rw [← hxe, hsegre, hgre, hgre]
      push_cast
      linear_combination (δ * (i : ℝ)) * huv
    have him : x.im = δ * j := by
      rw [← hxe, hsegim, hgim, hgim]
      show u * (δ * (j : ℝ)) + v * (δ * (j : ℝ)) = δ * j
      linear_combination (δ * (j : ℝ)) * huv
    refine ⟨him, ?_, ?_⟩
    · rw [hre]
      nlinarith
    · rw [hre]
      nlinarith
  have hseg_v : ∀ (i j : ℤ), ∀ x ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i, j + 1)),
      x.re = δ * i ∧ δ * j ≤ x.im ∧ x.im ≤ δ * (j + 1) := by
    intro i j x hx
    obtain ⟨u, v, hu, hv, huv, hxe⟩ := hx
    have hv1 : v ≤ 1 := by linarith
    have him : x.im = δ * j + v * δ := by
      rw [← hxe, hsegim, hgim, hgim]
      push_cast
      linear_combination (δ * (j : ℝ)) * huv
    have hre : x.re = δ * i := by
      rw [← hxe, hsegre, hgre, hgre]
      show u * (δ * (i : ℝ)) + v * (δ * (i : ℝ)) = δ * i
      linear_combination (δ * (i : ℝ)) * huv
    refine ⟨hre, ?_, ?_⟩
    · rw [him]
      nlinarith
    · rw [him]
      nlinarith
  -- ================================================================
  -- STAGE 2: per-edge principal-log increments and the lift gluing.
  -- ================================================================
  have hslit : ∀ a b q : ℂ, (∀ x ∈ segment ℝ a b, q ≠ x) →
      (b - q) / (a - q) ∈ Complex.slitPlane := by
    intro a b q hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr fun h => hoff a (left_mem_segment ℝ a b) h.symm
    by_contra hns
    rw [Complex.mem_slitPlane_iff] at hns
    push Not at hns
    obtain ⟨hre, him⟩ := hns
    set r : ℝ := ((b - q) / (a - q)).re with hr_def
    have hratio : (b - q) / (a - q) = ((r : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im]
        exact him
    have hbq : b - q = ((r : ℝ) : ℂ) * (a - q) := by
      rw [← hratio, div_mul_cancel₀ _ haq]
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have hqseg : q ∈ segment ℝ a b := by
      refine ⟨-r / (1 - r), 1 / (1 - r), div_nonneg (by linarith) h1r.le,
        by positivity, ?_, ?_⟩
      · field_simp
        ring
      · rw [Complex.real_smul, Complex.real_smul]
        push_cast
        have hcne : ((1 : ℂ) - (r : ℂ)) ≠ 0 := by
          have h0 : ((1 - r : ℝ) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt h1r)
          push_cast at h0
          exact h0
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          div_eq_iff hcne]
        linear_combination hbq
    exact hoff q hqseg rfl
  set inc : (ℤ × ℤ) × (ℤ × ℤ) → ℂ → ℂ := fun e q =>
    Complex.log ((gridPoint δ e.2 - q) / (gridPoint δ e.1 - q)) with hinc_def
  have hsegmem : ∀ (a b : ℂ) (s : unitInterval),
      segmentPath a b s ∈ segment ℝ a b := by
    intro a b s
    refine ⟨1 - (s : ℝ), (s : ℝ), by linarith [s.2.2], s.2.1, by ring, ?_⟩
    show (1 - (s : ℝ)) • a + (s : ℝ) • b = a + ((s : ℝ) : ℂ) * (b - a)
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hseglift : ∀ a b q : ℂ, (∀ x ∈ segment ℝ a b, q ≠ x) →
      ∃ g : C(unitInterval, ℂ),
        (∀ s : unitInterval, Complex.exp (g s) = segmentPath a b s - q) ∧
        g 1 - g 0 = Complex.log ((b - q) / (a - q)) ∧
        Complex.exp (g 1) = b - q := by
    intro a b q hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hoff a (left_mem_segment ℝ a b)))
    have hgmem : ∀ s : unitInterval,
        (segmentPath a b s - q) / (a - q) ∈ Complex.slitPlane := by
      intro s
      refine hslit a (segmentPath a b s) q ?_
      intro x hx
      exact hoff x ((convex_segment a b).segment_subset
        (left_mem_segment ℝ a b) (hsegmem a b s) hx)
    have hgcont : Continuous fun s : unitInterval =>
        (segmentPath a b s - q) / (a - q) :=
      ((segmentPath a b).continuous.sub continuous_const).div_const _
    have hgcont' : Continuous fun s : unitInterval =>
        Complex.log ((segmentPath a b s - q) / (a - q)) +
          Complex.log (a - q) := by
      refine Continuous.add ?_ continuous_const
      rw [continuous_iff_continuousAt]
      intro s
      exact hgcont.continuousAt.clog (hgmem s)
    refine ⟨⟨fun s => Complex.log ((segmentPath a b s - q) / (a - q)) +
      Complex.log (a - q), hgcont'⟩, ?_, ?_, ?_⟩
    · intro s
      show Complex.exp (Complex.log ((segmentPath a b s - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [Complex.exp_add, Complex.exp_log haq,
        Complex.exp_log (Complex.slitPlane_ne_zero (hgmem s)),
        div_mul_cancel₀ _ haq]
    · show (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) - (Complex.log ((segmentPath a b 0 - q) /
          (a - q)) + Complex.log (a - q)) = _
      rw [(segmentPath a b).source, (segmentPath a b).target,
        div_self haq, Complex.log_one]
      ring
    · show Complex.exp (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [(segmentPath a b).target, Complex.exp_add, Complex.exp_log haq]
      have hbq : b - q ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hoff b (right_mem_segment ℝ a b)))
      rw [Complex.exp_log (by
        exact div_ne_zero hbq haq), div_mul_cancel₀ _ haq]
  have hliftInd : ∀ (Lst : List (ℤ × ℤ)) (p : ℤ × ℤ),
      IsGridPath (p :: Lst) →
      ∀ q : ℂ, (∀ x ∈ gridPathTrace δ (p :: Lst), q ≠ x) →
      ∃ Lf : C(unitInterval, ℂ),
        IsLogLiftOf Lf
          (shiftedCurve (gridPathRealize δ p Lst).toContinuousMap q) ∧
        Lf 1 - Lf 0 = (((p :: Lst).zip Lst).map (fun e => inc e q)).sum := by
    intro Lst
    induction Lst with
    | nil =>
      intro p _ q hoff
      have hqp : q ≠ gridPoint δ p := hoff _ rfl
      refine ⟨ContinuousMap.const unitInterval
        (Complex.log (gridPoint δ p - q)), ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        rw [Complex.exp_log (sub_ne_zero.mpr (Ne.symm hqp))]
        show gridPoint δ p - q = (Path.refl (gridPoint δ p)) t - q
        simp
      · simp
    | cons r M ih =>
      intro p hpath q hoff
      have htail : IsGridPath (r :: M) :=
        (List.isChain_cons_cons.mp hpath).2
      have hofftrace : ∀ x ∈ gridPathTrace δ (r :: M), q ≠ x :=
        fun x hx => hoff x (Or.inr hx)
      have hoffseg : ∀ x ∈ segment ℝ (gridPoint δ p) (gridPoint δ r),
          q ≠ x := fun x hx => hoff x (Or.inl hx)
      obtain ⟨Lrest, hLrest, hLrest_inc⟩ := ih r htail q hofftrace
      obtain ⟨fseg, hfseg_lift, hfseg_inc, hfseg1⟩ :=
        hseglift (gridPoint δ p) (gridPoint δ r) q hoffseg
      have hbq : gridPoint δ r - q ≠ 0 := by
        rw [← hfseg1]
        exact Complex.exp_ne_zero _
      have hLrest0 : Complex.exp (Lrest 0) = gridPoint δ r - q := by
        have h := hLrest 0
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] at h
        rw [h, (gridPathRealize δ r M).source]
      have hexpc : Complex.exp (fseg 1 - Lrest 0) = 1 := by
        rw [Complex.exp_sub, hfseg1, hLrest0, div_self hbq]
      have hstart : (Lrest + ContinuousMap.const unitInterval
          (fseg 1 - Lrest 0)) 0 = fseg 1 := by
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        ring
      have hLrest'_lift : ∀ t, Complex.exp ((Lrest +
          ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) t) =
          (gridPathRealize δ r M) t - q := by
        intro t
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [Complex.exp_add, hexpc, mul_one]
        have h := hLrest t
        simpa only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] using h
      refine ⟨((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
        (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
          hstart, rfl⟩ : Path (fseg 1) ((Lrest +
            ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
          ).toContinuousMap, ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        show Complex.exp _ =
          ((segmentPath (gridPoint δ p) (gridPoint δ r)).trans
            (gridPathRealize δ r M)) t - q
        rw [Path.trans_apply, Path.trans_apply]
        split_ifs with ht
        · exact hfseg_lift _
        · exact hLrest'_lift _
      · have h0 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 0 = fseg 0 := by simp
        have h1 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 1 = (Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1 := by
          simp
        rw [h0, h1]
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ← hLrest_inc]
        have hincpr : inc (p, r) q =
            Complex.log ((gridPoint δ r - q) / (gridPoint δ p - q)) := rfl
        rw [hincpr, ← hfseg_inc]
        ring
  have hlift : ∀ (M : List (ℤ × ℤ)), IsGridPath M → M ≠ [] →
      M.head? = M.getLast? →
      ∀ q : ℂ, (∀ x ∈ gridPathTrace δ M, q ≠ x) →
      (2 * Real.pi * Complex.I) * windingNumber (gridLoopCurve δ M) q =
        ((M.zip M.tail).map (fun e => inc e q)).sum := by
    intro M hM hMne hMcl q hoff
    obtain ⟨p, M', rfl⟩ := List.exists_cons_of_ne_nil hMne
    obtain ⟨Lf, hLf, hLf_inc⟩ := hliftInd M' p hM q hoff
    have hclosed : gridLoopCurve δ (p :: M') 0 = gridLoopCurve δ (p :: M') 1 :=
      gridLoopCurve_closed (by simp) hMcl
    have hrange : Set.range (gridLoopCurve δ (p :: M')) =
        gridPathTrace δ (p :: M') := range_gridLoopCurve hδ hM (by simp)
    have hq : ∀ t : unitInterval, gridLoopCurve δ (p :: M') t ≠ q := by
      intro t heq
      exact hoff _ (hrange ▸ Set.mem_range_self t) heq.symm
    have hspec := windingNumber_spec hclosed hq hLf
    rw [← hspec]
    exact hLf_inc
  -- ================================================================
  -- STAGE 3: list-sum utilities and telescoping over the closed loop.
  -- ================================================================
  have hmapsub : ∀ (P : List ((ℤ × ℤ) × (ℤ × ℤ)))
      (g₁ g₂ : (ℤ × ℤ) × (ℤ × ℤ) → ℂ),
      (P.map (fun x => g₁ x - g₂ x)).sum = (P.map g₁).sum - (P.map g₂).sum := by
    intro P g₁ g₂
    induction P with
    | nil => simp
    | cons e P ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  have hmapc : ∀ (P : List ((ℤ × ℤ) × (ℤ × ℤ)))
      (g : (ℤ × ℤ) × (ℤ × ℤ) → ℂ) (n : (ℤ × ℤ) × (ℤ × ℤ) → ℤ) (c : ℂ),
      (∀ x ∈ P, g x = c * n x) →
      (P.map g).sum = c * ((P.map n).sum : ℤ) := by
    intro P g n c
    induction P with
    | nil => intro _; simp
    | cons e P ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        h e List.mem_cons_self]
      push_cast
      ring
  have hlastq : ∀ (r : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (r :: M).getLast? = some (gridLast r M) := by
    intro r M
    induction M generalizing r with
    | nil => simp [gridLast]
    | cons q M ih =>
      rw [List.getLast?_cons_cons, ih]
      rfl
  have htele : ∀ (G : ℤ × ℤ → ℂ) (x : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (((x :: M).zip M).map (fun e => G e.2 - G e.1)).sum =
        G (gridLast x M) - G x := by
    intro G x M
    induction M generalizing x with
    | nil => simp [gridLast]
    | cons y M' ih =>
      have hz : ((x :: y :: M').zip (y :: M')) =
          (x, y) :: ((y :: M').zip M') := rfl
      rw [hz, List.map_cons, List.sum_cons, ih y]
      show G y - G x + (G (gridLast y M') - G y) =
        G (gridLast x (y :: M')) - G x
      have hgl : gridLast x (y :: M') = gridLast y M' := rfl
      rw [hgl]
      ring
  have hteleL : ∀ G : ℤ × ℤ → ℂ,
      (prs.map (fun e => G e.2 - G e.1)).sum = 0 := by
    intro G
    obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
    have h := htele G p L'
    have hp : p = gridLast p L' := by
      have h2 := hcl
      rw [List.head?_cons, hlastq] at h2
      exact Option.some.inj h2
    rw [hprs_def]
    show (((p :: L').zip L').map (fun e => G e.2 - G e.1)).sum = 0
    rw [h, ← hp, sub_self]
  -- signed traversal indicator of a canonical directed edge
  set ind : (ℤ × ℤ) × (ℤ × ℤ) → (ℤ × ℤ) × (ℤ × ℤ) → ℤ := fun E e =>
    if e = E then 1 else if e = (E.2, E.1) then -1 else 0 with hind_def
  -- ================================================================
  -- STAGE 4: the jump engine.
  -- ================================================================
  -- division shortcuts for the crossing-edge Gaussian ratios
  have hdivI : ∀ x y : ℂ, y ≠ 0 → x = Complex.I * y → x / y = Complex.I := by
    intro x y hy hxy
    rw [hxy, mul_div_assoc, div_self hy, mul_one]
  have hdivnI : ∀ x y : ℂ, y ≠ 0 → x = -Complex.I * y → x / y = -Complex.I := by
    intro x y hy hxy
    rw [hxy, mul_div_assoc, div_self hy, mul_one]
  have hdivI' : ∀ x y : ℂ, x ≠ 0 → y = Complex.I * x → x / y = -Complex.I := by
    intro x y hx hxy
    rw [hxy, div_mul_eq_div_div_swap, div_self hx, one_div, Complex.inv_I]
  have hdivnI' : ∀ x y : ℂ, x ≠ 0 → y = -Complex.I * x → x / y = Complex.I := by
    intro x y hx hxy
    rw [hxy, div_mul_eq_div_div_swap, div_self hx, one_div, inv_neg,
      Complex.inv_I, neg_neg]
  -- the defect vanishes on edges avoiding the branch cut [cm, cp]
  have hD_zero : ∀ A B cp cm : ℂ,
      (∀ x ∈ segment ℝ A B, cp ≠ x) →
      (∀ x ∈ segment ℝ A B, cm ≠ x) →
      (∀ z ∈ segment ℝ A B, ∀ y ∈ segment ℝ cm cp, z ≠ y) →
      Complex.log ((B - cp) / (A - cp)) - Complex.log ((B - cm) / (A - cm)) -
        (Complex.log ((B - cp) / (B - cm)) -
          Complex.log ((A - cp) / (A - cm))) = 0 := by
    intro A B cp cm hcp hcm hcut
    have hAcp : A - cp ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hcp A (left_mem_segment ℝ A B)))
    have hAcm : A - cm ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hcm A (left_mem_segment ℝ A B)))
    have hz_ne_cp : ∀ s : unitInterval, segmentPath A B s - cp ≠ 0 := fun s =>
      sub_ne_zero.mpr (Ne.symm (hcp _ (hsegmem A B s)))
    have hz_ne_cm : ∀ s : unitInterval, segmentPath A B s - cm ≠ 0 := fun s =>
      sub_ne_zero.mpr (Ne.symm (hcm _ (hsegmem A B s)))
    have humem : ∀ s : unitInterval,
        (segmentPath A B s - cp) / (A - cp) ∈ Complex.slitPlane := by
      intro s
      refine hslit A (segmentPath A B s) cp ?_
      intro x hx
      exact hcp x ((convex_segment A B).segment_subset
        (left_mem_segment ℝ A B) (hsegmem A B s) hx)
    have hvmem : ∀ s : unitInterval,
        (segmentPath A B s - cm) / (A - cm) ∈ Complex.slitPlane := by
      intro s
      refine hslit A (segmentPath A B s) cm ?_
      intro x hx
      exact hcm x ((convex_segment A B).segment_subset
        (left_mem_segment ℝ A B) (hsegmem A B s) hx)
    have hwmem : ∀ s : unitInterval,
        (segmentPath A B s - cp) / (segmentPath A B s - cm) ∈
          Complex.slitPlane := by
      intro s
      have h1 : (cp - segmentPath A B s) / (cm - segmentPath A B s) ∈
          Complex.slitPlane :=
        hslit cm cp (segmentPath A B s)
          (fun y hy => hcut _ (hsegmem A B s) y hy)
      have h2 : (segmentPath A B s - cp) / (segmentPath A B s - cm) =
          (cp - segmentPath A B s) / (cm - segmentPath A B s) := by
        rw [← neg_sub cp (segmentPath A B s), ← neg_sub cm (segmentPath A B s),
          neg_div_neg_eq]
      rw [h2]
      exact h1
    have hφcont : Continuous fun s : unitInterval =>
        Complex.log ((segmentPath A B s - cp) / (A - cp)) -
          Complex.log ((segmentPath A B s - cm) / (A - cm)) -
          Complex.log ((segmentPath A B s - cp) / (segmentPath A B s - cm)) +
          Complex.log ((A - cp) / (A - cm)) := by
      have hc1 : Continuous fun s : unitInterval =>
          Complex.log ((segmentPath A B s - cp) / (A - cp)) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (((segmentPath A B).continuous.sub
          continuous_const).div_const _).continuousAt.clog (humem s)
      have hc2 : Continuous fun s : unitInterval =>
          Complex.log ((segmentPath A B s - cm) / (A - cm)) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (((segmentPath A B).continuous.sub
          continuous_const).div_const _).continuousAt.clog (hvmem s)
      have hc3 : Continuous fun s : unitInterval =>
          Complex.log ((segmentPath A B s - cp) /
            (segmentPath A B s - cm)) := by
        rw [continuous_iff_continuousAt]
        intro s
        refine ContinuousAt.clog ?_ (hwmem s)
        exact (((segmentPath A B).continuous.sub continuous_const).div
          ((segmentPath A B).continuous.sub continuous_const)
          (fun t => hz_ne_cm t)).continuousAt
      exact ((hc1.sub hc2).sub hc3).add continuous_const
    set φ : C(unitInterval, ℂ) := ⟨fun s =>
      Complex.log ((segmentPath A B s - cp) / (A - cp)) -
        Complex.log ((segmentPath A B s - cm) / (A - cm)) -
        Complex.log ((segmentPath A B s - cp) / (segmentPath A B s - cm)) +
        Complex.log ((A - cp) / (A - cm)), hφcont⟩ with hφ_def
    have hφlift : IsLogLiftOf φ (ContinuousMap.const unitInterval 1) := by
      intro s
      simp only [hφ_def, ContinuousMap.coe_mk, ContinuousMap.const_apply]
      rw [Complex.exp_add, Complex.exp_sub, Complex.exp_sub,
        Complex.exp_log (div_ne_zero (hz_ne_cp s) hAcp),
        Complex.exp_log (div_ne_zero (hz_ne_cm s) hAcm),
        Complex.exp_log (div_ne_zero (hz_ne_cp s) (hz_ne_cm s)),
        Complex.exp_log (div_ne_zero hAcp hAcm)]
      field_simp [hz_ne_cp s, hz_ne_cm s, hAcp, hAcm]
    have h0lift : IsLogLiftOf (ContinuousMap.const unitInterval 0)
        (ContinuousMap.const unitInterval 1) := by
      intro s
      simp
    have hincr := isLogLiftOf_increment_eq hφlift h0lift
    have hφ0 : φ 0 = 0 := by
      simp only [hφ_def, ContinuousMap.coe_mk]
      rw [(segmentPath A B).source, div_self hAcp, div_self hAcm,
        Complex.log_one]
      ring
    have hφ1 : φ 1 = Complex.log ((B - cp) / (A - cp)) -
        Complex.log ((B - cm) / (A - cm)) -
        Complex.log ((B - cp) / (B - cm)) +
        Complex.log ((A - cp) / (A - cm)) := by
      simp only [hφ_def, ContinuousMap.coe_mk]
      rw [(segmentPath A B).target]
    rw [hφ0, hφ1] at hincr
    simp only [ContinuousMap.const_apply, sub_zero, sub_self] at hincr
    linear_combination hincr
  -- the engine: winding difference across an edge = signed traversal count
  have hENGINE : ∀ (t₀ h₀ : ℤ × ℤ) (cp cm : ℂ),
      (∀ x ∈ gridPathTrace δ L, cp ≠ x) →
      (∀ x ∈ gridPathTrace δ L, cm ≠ x) →
      gridPoint δ t₀ - cp ≠ 0 → gridPoint δ t₀ - cm ≠ 0 →
      gridPoint δ h₀ - cp ≠ 0 → gridPoint δ h₀ - cm ≠ 0 →
      gridPoint δ h₀ - cp = Complex.I * (gridPoint δ t₀ - cp) →
      gridPoint δ h₀ - cm = -Complex.I * (gridPoint δ t₀ - cm) →
      gridPoint δ t₀ - cp = Complex.I * (gridPoint δ t₀ - cm) →
      gridPoint δ h₀ - cp = -Complex.I * (gridPoint δ h₀ - cm) →
      (∀ e ∈ prs, e ≠ (t₀, h₀) → e ≠ (h₀, t₀) →
        ∀ z ∈ segment ℝ (gridPoint δ e.1) (gridPoint δ e.2),
          ∀ y ∈ segment ℝ cm cp, z ≠ y) →
      (windingNumber γ cp : ℤ) - windingNumber γ cm =
        (prs.map (ind (t₀, h₀))).sum := by
    intro t₀ h₀ cp cm hcpoff hcmoff hAcp hAcm hBcp hBcm hr1 hr2 hr3 hr4 hcut
    set G : ℤ × ℤ → ℂ := fun r =>
      Complex.log ((gridPoint δ r - cp) / (gridPoint δ r - cm)) with hG_def
    -- the two crossed-edge defect values
    have hDcan : inc (t₀, h₀) cp - inc (t₀, h₀) cm - (G h₀ - G t₀) =
        2 * Real.pi * Complex.I := by
      have h1 : inc (t₀, h₀) cp = Complex.log Complex.I := by
        show Complex.log ((gridPoint δ h₀ - cp) / (gridPoint δ t₀ - cp)) = _
        rw [hdivI _ _ hAcp hr1]
      have h2 : inc (t₀, h₀) cm = Complex.log (-Complex.I) := by
        show Complex.log ((gridPoint δ h₀ - cm) / (gridPoint δ t₀ - cm)) = _
        rw [hdivnI _ _ hAcm hr2]
      have h3 : G t₀ = Complex.log Complex.I := by
        show Complex.log ((gridPoint δ t₀ - cp) / (gridPoint δ t₀ - cm)) = _
        rw [hdivI _ _ hAcm hr3]
      have h4 : G h₀ = Complex.log (-Complex.I) := by
        show Complex.log ((gridPoint δ h₀ - cp) / (gridPoint δ h₀ - cm)) = _
        rw [hdivnI _ _ hBcm hr4]
      rw [h1, h2, h3, h4, Complex.log_I, Complex.log_neg_I]
      ring
    have hDswap : inc (h₀, t₀) cp - inc (h₀, t₀) cm - (G t₀ - G h₀) =
        -(2 * Real.pi * Complex.I) := by
      have h1 : inc (h₀, t₀) cp = Complex.log (-Complex.I) := by
        show Complex.log ((gridPoint δ t₀ - cp) / (gridPoint δ h₀ - cp)) = _
        rw [hdivI' _ _ hAcp hr1]
      have h2 : inc (h₀, t₀) cm = Complex.log Complex.I := by
        show Complex.log ((gridPoint δ t₀ - cm) / (gridPoint δ h₀ - cm)) = _
        rw [hdivnI' _ _ hAcm hr2]
      have h3 : G t₀ = Complex.log Complex.I := by
        show Complex.log ((gridPoint δ t₀ - cp) / (gridPoint δ t₀ - cm)) = _
        rw [hdivI _ _ hAcm hr3]
      have h4 : G h₀ = Complex.log (-Complex.I) := by
        show Complex.log ((gridPoint δ h₀ - cp) / (gridPoint δ h₀ - cm)) = _
        rw [hdivnI _ _ hBcm hr4]
      rw [h1, h2, h3, h4, Complex.log_I, Complex.log_neg_I]
      ring
    -- the crossed edge has distinct endpoints
    have hth : t₀ ≠ h₀ := by
      intro h
      subst h
      have h1 : (1 - Complex.I) * (gridPoint δ t₀ - cp) = 0 := by
        linear_combination hr1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · have h3 := congrArg Complex.re h2
        simp [Complex.sub_re] at h3
      · exact hAcp h2
    -- pointwise defect values along the loop
    have hDval : ∀ e ∈ prs, inc e cp - inc e cm - (G e.2 - G e.1) =
        (2 * Real.pi * Complex.I) * ((ind (t₀, h₀) e : ℤ) : ℂ) := by
      intro e he
      by_cases hcan : e = (t₀, h₀)
      · subst hcan
        have hival : ind (t₀, h₀) (t₀, h₀) = 1 := by
          simp [hind_def]
        rw [hival]
        show inc (t₀, h₀) cp - inc (t₀, h₀) cm - (G h₀ - G t₀) =
          2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ)
        rw [hDcan, Int.cast_one, mul_one]
      · by_cases hswap : e = (h₀, t₀)
        · subst hswap
          have hne2 : ((h₀, t₀) : (ℤ × ℤ) × (ℤ × ℤ)) ≠ (t₀, h₀) :=
            fun hh => hth ((Prod.ext_iff.mp hh).1).symm
          have hival : ind (t₀, h₀) (h₀, t₀) = -1 := by
            simp only [hind_def]
            rw [if_neg hne2]
            simp
          rw [hival]
          show inc (h₀, t₀) cp - inc (h₀, t₀) cm - (G t₀ - G h₀) =
            2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
          rw [hDswap]
          push_cast
          ring
        · have hival : ind (t₀, h₀) e = 0 := by
            simp only [hind_def]
            rw [if_neg hcan, if_neg (fun hh => hswap hh)]
          rw [hival, Int.cast_zero, mul_zero]
          have hcpoffseg : ∀ x ∈ segment ℝ (gridPoint δ e.1)
              (gridPoint δ e.2), cp ≠ x :=
            fun x hx => hcpoff x (hpair_seg L e he hx)
          have hcmoffseg : ∀ x ∈ segment ℝ (gridPoint δ e.1)
              (gridPoint δ e.2), cm ≠ x :=
            fun x hx => hcmoff x (hpair_seg L e he hx)
          exact hD_zero (gridPoint δ e.1) (gridPoint δ e.2) cp cm
            hcpoffseg hcmoffseg (hcut e he hcan hswap)
    -- sum the defects and cancel 2πi
    have h1 : (prs.map (fun e => inc e cp - inc e cm - (G e.2 - G e.1))).sum =
        (2 * Real.pi * Complex.I) * ((prs.map (ind (t₀, h₀))).sum : ℤ) :=
      hmapc prs _ _ _ hDval
    have h2 : (prs.map (fun e => inc e cp - inc e cm - (G e.2 - G e.1))).sum =
        (2 * Real.pi * Complex.I) * (windingNumber γ cp : ℤ) -
        (2 * Real.pi * Complex.I) * (windingNumber γ cm : ℤ) := by
      rw [hmapsub prs (fun e => inc e cp - inc e cm) (fun e => G e.2 - G e.1),
        hmapsub prs (fun e => inc e cp) (fun e => inc e cm), hteleL G,
        sub_zero, hprs_def, hγ_def]
      rw [← hlift L hL hne hcl cp hcpoff, ← hlift L hL hne hcl cm hcmoff]
    have h4 : (((windingNumber γ cp : ℤ) - windingNumber γ cm : ℤ) : ℂ) =
        (((prs.map (ind (t₀, h₀))).sum : ℤ) : ℂ) := by
      have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      apply mul_left_cancel₀ h2πi
      rw [Int.cast_sub, mul_sub, ← h2]
      exact h1
    exact_mod_cast h4
  -- cut segments: coordinates
  have hcutH : ∀ v : ℤ × ℤ, ∀ y ∈ segment ℝ
      (gridSquareCenter δ (v.1, v.2 - 1)) (gridSquareCenter δ v),
      y.re = δ * v.1 + δ / 2 ∧
        δ * v.2 - δ / 2 ≤ y.im ∧ y.im ≤ δ * v.2 + δ / 2 := by
    intro v y hy
    obtain ⟨u, u', hu, hu', huu, hye⟩ := hy
    have hare : (gridSquareCenter δ (v.1, v.2 - 1)).re = δ * v.1 + δ / 2 :=
      hcen_re _
    have haim : (gridSquareCenter δ (v.1, v.2 - 1)).im = δ * v.2 - δ / 2 := by
      rw [hcen_im]
      show δ * ((v.2 - 1 : ℤ) : ℝ) + δ / 2 = δ * v.2 - δ / 2
      push_cast
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [← hye, hsegre, hare, hcen_re]
      linear_combination (δ * (v.1 : ℝ) + δ / 2) * huu
    · rw [← hye, hsegim, haim, hcen_im]
      have hu1 : u = 1 - u' := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu']
    · rw [← hye, hsegim, haim, hcen_im]
      have hu1 : u' = 1 - u := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu]
  have hcutU : ∀ v : ℤ × ℤ, ∀ y ∈ segment ℝ
      (gridSquareCenter δ v) (gridSquareCenter δ (v.1 - 1, v.2)),
      y.im = δ * v.2 + δ / 2 ∧
        δ * v.1 - δ / 2 ≤ y.re ∧ y.re ≤ δ * v.1 + δ / 2 := by
    intro v y hy
    obtain ⟨u, u', hu, hu', huu, hye⟩ := hy
    have hbre : (gridSquareCenter δ (v.1 - 1, v.2)).re = δ * v.1 - δ / 2 := by
      rw [hcen_re]
      show δ * ((v.1 - 1 : ℤ) : ℝ) + δ / 2 = δ * v.1 - δ / 2
      push_cast
      ring
    have hbim : (gridSquareCenter δ (v.1 - 1, v.2)).im = δ * v.2 + δ / 2 :=
      hcen_im _
    refine ⟨?_, ?_, ?_⟩
    · rw [← hye, hsegim, hbim, hcen_im]
      linear_combination (δ * (v.2 : ℝ) + δ / 2) * huu
    · rw [← hye, hsegre, hbre, hcen_re]
      have hu1 : u' = 1 - u := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu]
    · rw [← hye, hsegre, hbre, hcen_re]
      have hu1 : u = 1 - u' := by linarith
      subst hu1
      nlinarith [mul_nonneg hδ.le hu']
  -- cut avoidance: the cut only crosses the grid inside the crossed edge
  have havoidH : ∀ v : ℤ × ℤ, ∀ e ∈ prs,
      e ≠ (v, (v.1 + 1, v.2)) → e ≠ ((v.1 + 1, v.2), v) →
      ∀ z ∈ segment ℝ (gridPoint δ e.1) (gridPoint δ e.2),
        ∀ y ∈ segment ℝ (gridSquareCenter δ (v.1, v.2 - 1))
          (gridSquareCenter δ v), z ≠ y := by
    intro v e he hecan heswap z hz y hy heq
    obtain ⟨hyre, hyim1, hyim2⟩ := hcutH v y hy
    have hadj := hpair_adj L hL e he
    rcases hshape e hadj with h | h | h | h
    · -- canonical horizontal edge based at e.1
      rw [h] at hz
      obtain ⟨hzim, hzre1, hzre2⟩ := hseg_h e.1.1 e.1.2 z hz
      have him1 : δ * (v.2 : ℝ) - δ / 2 ≤ δ * e.1.2 := by
        rw [← hzim, heq]; exact hyim1
      have him2 : δ * (e.1.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hzim, heq]; exact hyim2
      have hre1 : δ * (e.1.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hyre, ← heq]; exact hzre1
      have hre2 : δ * v.1 + δ / 2 ≤ δ * ((e.1.1 : ℝ) + 1) := by
        rw [← hyre, ← heq]; exact hzre2
      have hj : e.1.2 = v.2 := by
        have a1 : (2 * v.2 - 1 : ℝ) ≤ 2 * e.1.2 := by nlinarith
        have a2 : (2 * e.1.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have b1 : (2 * v.2 - 1 : ℤ) ≤ 2 * e.1.2 := by exact_mod_cast a1
        have b2 : (2 * e.1.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a2
        omega
      have hi : e.1.1 = v.1 := by
        have a1 : (2 * e.1.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have a2 : (2 * v.1 + 1 : ℝ) ≤ 2 * e.1.1 + 2 := by nlinarith
        have b1 : (2 * e.1.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.1 + 1 : ℤ) ≤ 2 * e.1.1 + 2 := by exact_mod_cast a2
        omega
      exact hecan (Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨hi, hj⟩,
        by rw [h, hi, hj]⟩)
    · -- reversed horizontal edge based at e.2
      rw [h, segment_symm] at hz
      obtain ⟨hzim, hzre1, hzre2⟩ := hseg_h e.2.1 e.2.2 z hz
      have him1 : δ * (v.2 : ℝ) - δ / 2 ≤ δ * e.2.2 := by
        rw [← hzim, heq]; exact hyim1
      have him2 : δ * (e.2.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hzim, heq]; exact hyim2
      have hre1 : δ * (e.2.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hyre, ← heq]; exact hzre1
      have hre2 : δ * v.1 + δ / 2 ≤ δ * ((e.2.1 : ℝ) + 1) := by
        rw [← hyre, ← heq]; exact hzre2
      have hj : e.2.2 = v.2 := by
        have a1 : (2 * v.2 - 1 : ℝ) ≤ 2 * e.2.2 := by nlinarith
        have a2 : (2 * e.2.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have b1 : (2 * v.2 - 1 : ℤ) ≤ 2 * e.2.2 := by exact_mod_cast a1
        have b2 : (2 * e.2.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a2
        omega
      have hi : e.2.1 = v.1 := by
        have a1 : (2 * e.2.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have a2 : (2 * v.1 + 1 : ℝ) ≤ 2 * e.2.1 + 2 := by nlinarith
        have b1 : (2 * e.2.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.1 + 1 : ℤ) ≤ 2 * e.2.1 + 2 := by exact_mod_cast a2
        omega
      exact heswap (Prod.ext_iff.mpr ⟨by rw [h, hi, hj],
        Prod.ext_iff.mpr ⟨hi, hj⟩⟩)
    · -- vertical edges never meet the horizontal-jump cut
      rw [h] at hz
      obtain ⟨hzre, -, -⟩ := hseg_v e.1.1 e.1.2 z hz
      have hh : δ * (e.1.1 : ℝ) = δ * v.1 + δ / 2 := by
        rw [← hzre, heq, hyre]
      exact hhalf_ne (e.1.1 - v.1) (by push_cast; linarith)
    · rw [h, segment_symm] at hz
      obtain ⟨hzre, -, -⟩ := hseg_v e.2.1 e.2.2 z hz
      have hh : δ * (e.2.1 : ℝ) = δ * v.1 + δ / 2 := by
        rw [← hzre, heq, hyre]
      exact hhalf_ne (e.2.1 - v.1) (by push_cast; linarith)
  have havoidU : ∀ v : ℤ × ℤ, ∀ e ∈ prs,
      e ≠ (v, (v.1, v.2 + 1)) → e ≠ ((v.1, v.2 + 1), v) →
      ∀ z ∈ segment ℝ (gridPoint δ e.1) (gridPoint δ e.2),
        ∀ y ∈ segment ℝ (gridSquareCenter δ v)
          (gridSquareCenter δ (v.1 - 1, v.2)), z ≠ y := by
    intro v e he hecan heswap z hz y hy heq
    obtain ⟨hyim, hyre1, hyre2⟩ := hcutU v y hy
    have hadj := hpair_adj L hL e he
    rcases hshape e hadj with h | h | h | h
    · -- horizontal edges never meet the vertical-jump cut
      rw [h] at hz
      obtain ⟨hzim, -, -⟩ := hseg_h e.1.1 e.1.2 z hz
      have hh : δ * (e.1.2 : ℝ) = δ * v.2 + δ / 2 := by
        rw [← hzim, heq, hyim]
      exact hhalf_ne (e.1.2 - v.2) (by push_cast; linarith)
    · rw [h, segment_symm] at hz
      obtain ⟨hzim, -, -⟩ := hseg_h e.2.1 e.2.2 z hz
      have hh : δ * (e.2.2 : ℝ) = δ * v.2 + δ / 2 := by
        rw [← hzim, heq, hyim]
      exact hhalf_ne (e.2.2 - v.2) (by push_cast; linarith)
    · -- canonical vertical edge based at e.1
      rw [h] at hz
      obtain ⟨hzre, hzim1, hzim2⟩ := hseg_v e.1.1 e.1.2 z hz
      have hre1 : δ * (v.1 : ℝ) - δ / 2 ≤ δ * e.1.1 := by
        rw [← hzre, heq]; exact hyre1
      have hre2 : δ * (e.1.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hzre, heq]; exact hyre2
      have him1 : δ * (e.1.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hyim, ← heq]; exact hzim1
      have him2 : δ * v.2 + δ / 2 ≤ δ * ((e.1.2 : ℝ) + 1) := by
        rw [← hyim, ← heq]; exact hzim2
      have hi : e.1.1 = v.1 := by
        have a1 : (2 * v.1 - 1 : ℝ) ≤ 2 * e.1.1 := by nlinarith
        have a2 : (2 * e.1.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have b1 : (2 * v.1 - 1 : ℤ) ≤ 2 * e.1.1 := by exact_mod_cast a1
        have b2 : (2 * e.1.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a2
        omega
      have hj : e.1.2 = v.2 := by
        have a1 : (2 * e.1.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have a2 : (2 * v.2 + 1 : ℝ) ≤ 2 * e.1.2 + 2 := by nlinarith
        have b1 : (2 * e.1.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.2 + 1 : ℤ) ≤ 2 * e.1.2 + 2 := by exact_mod_cast a2
        omega
      exact hecan (Prod.ext_iff.mpr ⟨Prod.ext_iff.mpr ⟨hi, hj⟩,
        by rw [h, hi, hj]⟩)
    · -- reversed vertical edge based at e.2
      rw [h, segment_symm] at hz
      obtain ⟨hzre, hzim1, hzim2⟩ := hseg_v e.2.1 e.2.2 z hz
      have hre1 : δ * (v.1 : ℝ) - δ / 2 ≤ δ * e.2.1 := by
        rw [← hzre, heq]; exact hyre1
      have hre2 : δ * (e.2.1 : ℝ) ≤ δ * v.1 + δ / 2 := by
        rw [← hzre, heq]; exact hyre2
      have him1 : δ * (e.2.2 : ℝ) ≤ δ * v.2 + δ / 2 := by
        rw [← hyim, ← heq]; exact hzim1
      have him2 : δ * v.2 + δ / 2 ≤ δ * ((e.2.2 : ℝ) + 1) := by
        rw [← hyim, ← heq]; exact hzim2
      have hi : e.2.1 = v.1 := by
        have a1 : (2 * v.1 - 1 : ℝ) ≤ 2 * e.2.1 := by nlinarith
        have a2 : (2 * e.2.1 : ℝ) ≤ 2 * v.1 + 1 := by nlinarith
        have b1 : (2 * v.1 - 1 : ℤ) ≤ 2 * e.2.1 := by exact_mod_cast a1
        have b2 : (2 * e.2.1 : ℤ) ≤ 2 * v.1 + 1 := by exact_mod_cast a2
        omega
      have hj : e.2.2 = v.2 := by
        have a1 : (2 * e.2.2 : ℝ) ≤ 2 * v.2 + 1 := by nlinarith
        have a2 : (2 * v.2 + 1 : ℝ) ≤ 2 * e.2.2 + 2 := by nlinarith
        have b1 : (2 * e.2.2 : ℤ) ≤ 2 * v.2 + 1 := by exact_mod_cast a1
        have b2 : (2 * v.2 + 1 : ℤ) ≤ 2 * e.2.2 + 2 := by exact_mod_cast a2
        omega
      exact heswap (Prod.ext_iff.mpr ⟨by rw [h, hi, hj],
        Prod.ext_iff.mpr ⟨hi, hj⟩⟩)
  -- the two jump lemmas
  have hjumpR : ∀ v : ℤ × ℤ, (w v : ℤ) - w (v.1, v.2 - 1) =
      (prs.map (ind (v, (v.1 + 1, v.2)))).sum := by
    intro v
    have hr1 : gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ v =
        Complex.I * (gridPoint δ v - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr2 : gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ (v.1, v.2 - 1) =
        -Complex.I * (gridPoint δ v - gridSquareCenter δ (v.1, v.2 - 1)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr3 : gridPoint δ v - gridSquareCenter δ v =
        Complex.I * (gridPoint δ v - gridSquareCenter δ (v.1, v.2 - 1)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination (-(δ : ℂ) / 2) * Complex.I_sq
    have hr4 : gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ v =
        -Complex.I *
          (gridPoint δ (v.1 + 1, v.2) - gridSquareCenter δ (v.1, v.2 - 1)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    exact hENGINE v (v.1 + 1, v.2) (gridSquareCenter δ v)
      (gridSquareCenter δ (v.1, v.2 - 1)) (hcenter v L hL)
      (hcenter (v.1, v.2 - 1) L hL) (hgp_ne_cen v v)
      (hgp_ne_cen v (v.1, v.2 - 1)) (hgp_ne_cen (v.1 + 1, v.2) v)
      (hgp_ne_cen (v.1 + 1, v.2) (v.1, v.2 - 1)) hr1 hr2 hr3 hr4 (havoidH v)
  have hjumpU : ∀ v : ℤ × ℤ, (w (v.1 - 1, v.2) : ℤ) - w v =
      (prs.map (ind (v, (v.1, v.2 + 1)))).sum := by
    intro v
    have hr1 : gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ (v.1 - 1, v.2) =
        Complex.I * (gridPoint δ v - gridSquareCenter δ (v.1 - 1, v.2)) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr2 : gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ v =
        -Complex.I * (gridPoint δ v - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination (-(δ : ℂ) / 2) * Complex.I_sq
    have hr3 : gridPoint δ v - gridSquareCenter δ (v.1 - 1, v.2) =
        Complex.I * (gridPoint δ v - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    have hr4 : gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ (v.1 - 1, v.2) =
        -Complex.I *
          (gridPoint δ (v.1, v.2 + 1) - gridSquareCenter δ v) := by
      simp only [gridPoint, gridSquareCenter]
      push_cast
      linear_combination ((δ : ℂ) / 2) * Complex.I_sq
    exact hENGINE v (v.1, v.2 + 1) (gridSquareCenter δ (v.1 - 1, v.2))
      (gridSquareCenter δ v) (hcenter (v.1 - 1, v.2) L hL)
      (hcenter v L hL) (hgp_ne_cen v (v.1 - 1, v.2))
      (hgp_ne_cen v v) (hgp_ne_cen (v.1, v.2 + 1) (v.1 - 1, v.2))
      (hgp_ne_cen (v.1, v.2 + 1) v) hr1 hr2 hr3 hr4 (havoidU v)
  -- ================================================================
  -- STAGE 5: finiteness — the support box, S, and V.
  -- ================================================================
  have hclosedγ : γ 0 = γ 1 := gridLoopCurve_closed hne hcl
  have hrangeγ : Set.range γ = gridPathTrace δ L :=
    range_gridLoopCurve hδ hL hne
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p : ℤ × ℤ, w p ≠ 0 →
      -(K : ℤ) ≤ p.1 ∧ p.1 ≤ K ∧ -(K : ℤ) ≤ p.2 ∧ p.2 ≤ K := by
    obtain ⟨R, hR⟩ := (isBounded_windingRegion hclosedγ).subset_closedBall 0
    obtain ⟨K, hKgt⟩ := exists_nat_gt ((R + δ) / δ)
    rw [div_lt_iff₀ hδ] at hKgt
    have hKδ : R + δ ≤ δ * K := by nlinarith
    refine ⟨K, fun p hwp => ?_⟩
    have hnotin : gridSquareCenter δ p ∉ Set.range γ := by
      rw [hrangeγ]
      intro hmem
      exact hcenter p L hL _ hmem rfl
    have hin : gridSquareCenter δ p ∈ Metric.closedBall (0 : ℂ) R :=
      hR ⟨hnotin, hwp⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hin
    have hre : |(gridSquareCenter δ p).re| ≤ R :=
      le_trans (Complex.abs_re_le_norm _) hin
    have him : |(gridSquareCenter δ p).im| ≤ R :=
      le_trans (Complex.abs_im_le_norm _) hin
    rw [hcen_re, abs_le] at hre
    rw [hcen_im, abs_le] at him
    have h1 : (-(K : ℤ) : ℝ) ≤ (p.1 : ℝ) := by push_cast; nlinarith [hre.1]
    have h2 : (p.1 : ℝ) ≤ (K : ℝ) := by nlinarith [hre.2]
    have h3 : (-(K : ℤ) : ℝ) ≤ (p.2 : ℝ) := by push_cast; nlinarith [him.1]
    have h4 : (p.2 : ℝ) ≤ (K : ℝ) := by nlinarith [him.2]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4⟩
  set S : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(K : ℤ), -(K : ℤ)) ((K : ℤ), (K : ℤ))).filter
      (fun p => w p ≠ 0) with hS_def
  set V : Finset (ℤ × ℤ) :=
    Finset.Icc (-(K : ℤ) - 1, -(K : ℤ) - 1) ((K : ℤ) + 1, (K : ℤ) + 1) ∪
      L.toFinset with hV_def
  have hSmem : ∀ p : ℤ × ℤ, p ∈ S ↔ w p ≠ 0 := by
    intro p
    rw [hS_def, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hwp
      refine ⟨?_, hwp⟩
      obtain ⟨h1, h2, h3, h4⟩ := hK p hwp
      rw [Finset.mem_Icc]
      constructor
      · rw [Prod.le_def]
        exact ⟨by omega, by omega⟩
      · rw [Prod.le_def]
        exact ⟨by omega, by omega⟩
  have hwzero : ∀ p : ℤ × ℤ, p ∉ S → w p = 0 := by
    intro p hp
    by_contra h
    exact hp ((hSmem p).mpr h)
  have hSbox : ∀ p ∈ S, -(K : ℤ) ≤ p.1 ∧ p.1 ≤ K ∧
      -(K : ℤ) ≤ p.2 ∧ p.2 ≤ K := by
    intro p hp
    exact hK p ((hSmem p).mp hp)
  have hSV : S ⊆ V := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSbox p hp
    rw [hV_def, Finset.mem_union]
    left
    rw [Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hSupV : ∀ p ∈ S, (p.1, p.2 + 1) ∈ V := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSbox p hp
    rw [hV_def, Finset.mem_union]
    left
    rw [Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hSrtV : ∀ p ∈ S, (p.1 + 1, p.2) ∈ V := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSbox p hp
    rw [hV_def, Finset.mem_union]
    left
    rw [Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  -- ================================================================
  -- STAGE 6: assembly over the common vertex Finset V.
  -- ================================================================
  set segR : ℤ × ℤ → ℂ := fun v =>
    segmentIntegral f (gridPoint δ v) (gridPoint δ (v.1 + 1, v.2)) with hsegR_def
  set segU : ℤ × ℤ → ℂ := fun v =>
    segmentIntegral f (gridPoint δ v) (gridPoint δ (v.1, v.2 + 1)) with hsegU_def
  have hbdry : ∀ p : ℤ × ℤ, gridSquareBoundaryIntegral f δ p =
      segR p + segU (p.1 + 1, p.2) - segR (p.1, p.2 + 1) - segU p := by
    intro p
    show segmentIntegral f (gridPoint δ p) (gridPoint δ (p.1 + 1, p.2)) +
        (segmentIntegral f (gridPoint δ (p.1 + 1, p.2))
          (gridPoint δ (p.1 + 1, p.2 + 1)) +
          (segmentIntegral f (gridPoint δ (p.1 + 1, p.2 + 1))
            (gridPoint δ (p.1, p.2 + 1)) +
            (segmentIntegral f (gridPoint δ (p.1, p.2 + 1))
              (gridPoint δ p) + 0))) = _
    simp only [hsegR_def, hsegU_def]
    rw [hanti (gridPoint δ (p.1, p.2 + 1)) (gridPoint δ (p.1 + 1, p.2 + 1)),
      hanti (gridPoint δ p) (gridPoint δ (p.1, p.2 + 1))]
    ring
  -- LHS regrouping: path integral as V-indexed coefficient sum
  have hclaimA : ∀ P : List ((ℤ × ℤ) × (ℤ × ℤ)),
      (∀ e ∈ P, GridAdj e.1 e.2 ∧ e.1 ∈ V ∧ e.2 ∈ V) →
      (P.map (fun e =>
        segmentIntegral f (gridPoint δ e.1) (gridPoint δ e.2))).sum =
      ∑ v ∈ V, (((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℂ) * segR v +
        ((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℂ) * segU v) := by
    intro P
    induction P with
    | nil =>
      intro _
      simp
    | cons e P ih =>
      intro hall
      have hE := hall e List.mem_cons_self
      have htail : ∀ x ∈ P, GridAdj x.1 x.2 ∧ x.1 ∈ V ∧ x.2 ∈ V :=
        fun x hx => hall x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.sum_cons]
      rw [ih htail]
      rcases hshape e hE.1 with h | h | h | h
      · -- rightward canonical edge based at e.1
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e =
            (if v = e.1 then 1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.1 then segR e.1 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.1
          · subst hv
            rw [if_pos rfl, if_pos rfl]
            push_cast
            ring
          · rw [if_neg hv, if_neg hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.1, if_pos hE.2.1, h]
        simp only [hsegR_def]
        ring
      · -- reversed rightward edge based at e.2
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e =
            (if v = e.2 then -1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.2 then -segR e.2 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.2
          · subst hv
            rw [if_pos rfl, if_pos rfl]
            push_cast
            ring
          · rw [if_neg hv, if_neg hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.2, if_pos hE.2.2,
          hanti (gridPoint δ e.2) (gridPoint δ e.1), h]
        simp only [hsegR_def]
        ring
      · -- upward canonical edge based at e.1
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e =
            (if v = e.1 then 1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.1 then segU e.1 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.1
          · subst hv
            rw [if_pos rfl, if_pos rfl]
            push_cast
            ring
          · rw [if_neg hv, if_neg hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.1, if_pos hE.2.1, h]
        simp only [hsegU_def]
        ring
      · -- reversed upward edge based at e.2
        have g3 := congrArg Prod.fst h
        have g4 := congrArg Prod.snd h
        have hiR : ∀ v : ℤ × ℤ, ind (v, (v.1 + 1, v.2)) e = 0 := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hiU : ∀ v : ℤ × ℤ, ind (v, (v.1, v.2 + 1)) e =
            (if v = e.2 then -1 else 0) := by
          intro v
          simp only [hind_def, Prod.ext_iff]
          split_ifs <;> omega
        have hstep : ∀ v ∈ V,
            ((ind (v, (v.1 + 1, v.2)) e +
              (P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
            ((ind (v, (v.1, v.2 + 1)) e +
              (P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
            ((((P.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
              (((P.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v) +
            (if v = e.2 then -segU e.2 else 0) := by
          intro v _
          rw [hiR v, hiU v]
          by_cases hv : v = e.2
          · subst hv
            rw [if_pos rfl, if_pos rfl]
            push_cast
            ring
          · rw [if_neg hv, if_neg hv]
            push_cast
            ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq' V e.2, if_pos hE.2.2,
          hanti (gridPoint δ e.2) (gridPoint δ e.1), h]
        simp only [hsegU_def]
        ring
  have hpairsV : ∀ e ∈ prs, GridAdj e.1 e.2 ∧ e.1 ∈ V ∧ e.2 ∈ V := by
    intro e he
    refine ⟨hpair_adj L hL e he, ?_, ?_⟩
    · rw [hV_def, Finset.mem_union]
      right
      rw [List.mem_toFinset]
      exact (hpair_mem L e he).1
    · rw [hV_def, Finset.mem_union]
      right
      rw [List.mem_toFinset]
      exact (hpair_mem L e he).2
  -- RHS regrouping: shifted sums reindexed over V
  have himgUp : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1, p.2 + 1)) ↔ (v.1, v.2 - 1) ∈ S := by
    intro v
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have hpv : p = (v.1, v.2 - 1) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← hpv]
      exact hp
    · intro h
      exact ⟨(v.1, v.2 - 1), h, Prod.ext_iff.mpr ⟨rfl, by omega⟩⟩
  have himgRt : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1 + 1, p.2)) ↔ (v.1 - 1, v.2) ∈ S := by
    intro v
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have hpv : p = (v.1 - 1, v.2) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← hpv]
      exact hp
    · intro h
      exact ⟨(v.1 - 1, v.2), h, Prod.ext_iff.mpr ⟨by omega, rfl⟩⟩
  have hT2 : ∑ p ∈ V, (w p : ℂ) * segR (p.1, p.2 + 1) =
      ∑ v ∈ V, (w (v.1, v.2 - 1) : ℂ) * segR v := by
    have e1 : ∑ p ∈ V, (w p : ℂ) * segR (p.1, p.2 + 1) =
        ∑ p ∈ S, (w p : ℂ) * segR (p.1, p.2 + 1) := by
      refine (Finset.sum_subset hSV ?_).symm
      intro p _ hpS
      rw [hwzero p hpS]
      simp
    have hinj : ∀ x ∈ S, ∀ y ∈ S,
        (fun p : ℤ × ℤ => (p.1, p.2 + 1)) x =
          (fun p : ℤ × ℤ => (p.1, p.2 + 1)) y → x = y := by
      intro x _ y _ h
      have h' : ((x.1, x.2 + 1) : ℤ × ℤ) = (y.1, y.2 + 1) := h
      have h1 := congrArg Prod.fst h'
      have h2 := congrArg Prod.snd h'
      exact Prod.ext_iff.mpr ⟨by omega, by omega⟩
    have e2 : ∑ v ∈ S.image (fun p => (p.1, p.2 + 1)),
        (w (v.1, v.2 - 1) : ℂ) * segR v =
        ∑ p ∈ S, (w p : ℂ) * segR (p.1, p.2 + 1) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have hpp : p = (((p.1, p.2 + 1) : ℤ × ℤ).1,
          ((p.1, p.2 + 1) : ℤ × ℤ).2 - 1) := Prod.ext_iff.mpr ⟨rfl, by omega⟩
      exact (congrArg (fun q : ℤ × ℤ =>
        (w q : ℂ) * segR (p.1, p.2 + 1)) hpp).symm
    have e3 : ∑ v ∈ S.image (fun p => (p.1, p.2 + 1)),
        (w (v.1, v.2 - 1) : ℂ) * segR v =
        ∑ v ∈ V, (w (v.1, v.2 - 1) : ℂ) * segR v := by
      refine Finset.sum_subset ?_ ?_
      · intro v hv
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hv
        rw [← heq]
        exact hSupV p hp
      · intro v _ hvimg
        have hns : (v.1, v.2 - 1) ∉ S := fun hmem => hvimg ((himgUp v).mpr hmem)
        rw [hwzero _ hns]
        simp
    rw [e1, ← e2, e3]
  have hT3 : ∑ p ∈ V, (w p : ℂ) * segU (p.1 + 1, p.2) =
      ∑ v ∈ V, (w (v.1 - 1, v.2) : ℂ) * segU v := by
    have e1 : ∑ p ∈ V, (w p : ℂ) * segU (p.1 + 1, p.2) =
        ∑ p ∈ S, (w p : ℂ) * segU (p.1 + 1, p.2) := by
      refine (Finset.sum_subset hSV ?_).symm
      intro p _ hpS
      rw [hwzero p hpS]
      simp
    have hinj : ∀ x ∈ S, ∀ y ∈ S,
        (fun p : ℤ × ℤ => (p.1 + 1, p.2)) x =
          (fun p : ℤ × ℤ => (p.1 + 1, p.2)) y → x = y := by
      intro x _ y _ h
      have h' : ((x.1 + 1, x.2) : ℤ × ℤ) = (y.1 + 1, y.2) := h
      have h1 := congrArg Prod.fst h'
      have h2 := congrArg Prod.snd h'
      exact Prod.ext_iff.mpr ⟨by omega, by omega⟩
    have e2 : ∑ v ∈ S.image (fun p => (p.1 + 1, p.2)),
        (w (v.1 - 1, v.2) : ℂ) * segU v =
        ∑ p ∈ S, (w p : ℂ) * segU (p.1 + 1, p.2) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have hpp : p = (((p.1 + 1, p.2) : ℤ × ℤ).1 - 1,
          ((p.1 + 1, p.2) : ℤ × ℤ).2) := Prod.ext_iff.mpr ⟨by omega, rfl⟩
      exact (congrArg (fun q : ℤ × ℤ =>
        (w q : ℂ) * segU (p.1 + 1, p.2)) hpp).symm
    have e3 : ∑ v ∈ S.image (fun p => (p.1 + 1, p.2)),
        (w (v.1 - 1, v.2) : ℂ) * segU v =
        ∑ v ∈ V, (w (v.1 - 1, v.2) : ℂ) * segU v := by
      refine Finset.sum_subset ?_ ?_
      · intro v hv
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hv
        rw [← heq]
        exact hSrtV p hp
      · intro v _ hvimg
        have hns : (v.1 - 1, v.2) ∉ S := fun hmem => hvimg ((himgRt v).mpr hmem)
        rw [hwzero _ hns]
        simp
    rw [e1, ← e2, e3]
  -- the main identity over V
  have hmain : gridPathIntegral f δ L =
      ∑ p ∈ V, (w p : ℂ) * gridSquareBoundaryIntegral f δ p := by
    rw [hLHS L, ← hprs_def, hclaimA prs hpairsV]
    have step1 : ∀ v ∈ V,
        (((prs.map (ind (v, (v.1 + 1, v.2)))).sum : ℤ) : ℂ) * segR v +
        (((prs.map (ind (v, (v.1, v.2 + 1)))).sum : ℤ) : ℂ) * segU v =
        ((w v : ℂ) * segR v - (w (v.1, v.2 - 1) : ℂ) * segR v) +
        ((w (v.1 - 1, v.2) : ℂ) * segU v - (w v : ℂ) * segU v) := by
      intro v _
      rw [← hjumpR v, ← hjumpU v]
      push_cast
      ring
    have step2 : ∀ p ∈ V, (w p : ℂ) * gridSquareBoundaryIntegral f δ p =
        ((w p : ℂ) * segR p - (w p : ℂ) * segR (p.1, p.2 + 1)) +
        ((w p : ℂ) * segU (p.1 + 1, p.2) - (w p : ℂ) * segU p) := by
      intro p _
      rw [hbdry p]
      ring
    rw [Finset.sum_congr rfl step1, Finset.sum_congr rfl step2,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, hT2, hT3]
  have hshrink : ∑ p ∈ V, (w p : ℂ) * gridSquareBoundaryIntegral f δ p =
      ∑ p ∈ S, (w p : ℂ) * gridSquareBoundaryIntegral f δ p := by
    refine (Finset.sum_subset hSV ?_).symm
    intro p _ hpS
    rw [hwzero p hpS]
    simp
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    refine ⟨(hSmem p).mp hp, ?_⟩
    intro hmem
    exact hcenter p L hL _ hmem rfl
  · exact hmain.trans hshrink

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

set_option maxHeartbeats 400000 in
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
  classical
  -- ================================================================
  -- STAGE 0: translation invariance of the winding number, and the
  -- reduction to a configuration where the marked point is the center
  -- of the `(0,0)` grid square.
  -- ================================================================
  -- Winding is invariant under simultaneous translation of curve and point
  -- (the shifted curves are literally equal).
  have htw : ∀ (γ : C(unitInterval, ℂ)) (w q : ℂ),
      windingNumber (γ - ContinuousMap.const unitInterval w) (q - w) =
        windingNumber γ q := by
    intro γ w q
    have hsc : shiftedCurve (γ - ContinuousMap.const unitInterval w) (q - w) =
        shiftedCurve γ q := by
      ext t
      simp only [shiftedCurve, ContinuousMap.sub_apply,
        ContinuousMap.const_apply]
      ring
    unfold windingNumber
    rw [hsc]
  set δ : ℝ := ε / 100 with hδ_def
  have hδ : 0 < δ := by positivity
  set c₀ : ℂ := gridSquareCenter δ (0, 0) with hc₀_def
  set τ : ℂ := c₀ - z₀ with hτ_def
  set A' : Set ℂ := (fun w => w + τ) '' A with hA'_def
  set T' : Set ℂ := (fun w => w + τ) '' T with hT'_def
  have hT'open : IsOpen T' := isOpenMap_add_right τ T hT
  have hA'cpt : IsCompact A' := hA.image (continuous_add_const τ)
  have hc₀A' : c₀ ∈ A' := ⟨z₀, hzA, by rw [hτ_def]; ring⟩
  have hA'T' : A' ⊆ T'ᶜ := by
    rintro x ⟨a, haA, rfl⟩ ⟨t, htT, hteq⟩
    have hat : t = a := by
      have := add_right_cancel hteq
      exact this
    exact hAT haA (hat ▸ htT)
  have hsep' : ∀ w ∈ T'ᶜ, w ∉ A' → ∀ a ∈ A', ε ≤ dist w a := by
    intro w hw hwA a' ha'
    obtain ⟨a, haA, rfl⟩ := ha'
    have hw₀T : w - τ ∈ Tᶜ := by
      intro hmem
      exact hw ⟨w - τ, hmem, by ring⟩
    have hw₀A : w - τ ∉ A := by
      intro hmem
      exact hwA ⟨w - τ, hmem, by ring⟩
    have hd := hsep (w - τ) hw₀T hw₀A a haA
    calc ε ≤ dist (w - τ) a := hd
      _ = dist w (a + τ) := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          ring
  -- It suffices to find the loop in the translated configuration.
  suffices h : ∃ γ : C(unitInterval, ℂ), γ 0 = γ 1 ∧
      (∀ t : unitInterval, γ t ∈ T') ∧ windingNumber γ c₀ ≠ 0 by
    obtain ⟨γ, hγcl, hγT', hγw⟩ := h
    refine ⟨γ - ContinuousMap.const unitInterval τ, ?_, ?_, ?_⟩
    · simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply, hγcl]
    · intro t
      obtain ⟨s, hsT, hseq⟩ := hγT' t
      have hst : (γ - ContinuousMap.const unitInterval τ) t = s := by
        simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
        rw [← hseq]
        ring
      rw [hst]
      exact hsT
    · have h1 := htw γ τ c₀
      have h2 : c₀ - τ = z₀ := by rw [hτ_def]; ring
      rw [h2] at h1
      rw [h1]
      exact hγw
  -- ================================================================
  -- STAGE 1: the square complex `S` and its geometry.
  -- ================================================================
  -- A bounding box: `A'` is bounded, so its squares have indices in a box.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, A' ⊆ Metric.ball 0 (δ * N) := by
    obtain ⟨R, hR⟩ := hA'cpt.isBounded.subset_closedBall 0
    obtain ⟨N, hNgt⟩ := exists_nat_gt ((R + 1) / δ)
    rw [div_lt_iff₀ hδ] at hNgt
    refine ⟨N, fun x hx => ?_⟩
    have hxR : dist x 0 ≤ R := hR hx
    have hlt : R < δ * N := by nlinarith
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hxR hlt)
  set B₀ : Finset (ℤ × ℤ) :=
    Finset.Icc (-(N : ℤ) - 2, -(N : ℤ) - 2) ((N : ℤ) + 2, (N : ℤ) + 2)
    with hB₀_def
  set S : Finset (ℤ × ℤ) :=
    B₀.filter (fun p => (gridSquare δ p ∩ A').Nonempty) with hS_def
  -- Coordinate helpers.
  have hgre : ∀ q : ℤ × ℤ, (gridPoint δ q).re = δ * q.1 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hgim : ∀ q : ℤ × ℤ, (gridPoint δ q).im = δ * q.2 := by
    intro q
    simp only [gridPoint, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have hsegre : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).re = u * a.re + v * b.re := by
    intro a b u v
    simp [Complex.add_re]
  have hsegim : ∀ (a b : ℂ) (u v : ℝ),
      (u • a + v • b).im = u * a.im + v * b.im := by
    intro a b u v
    simp [Complex.add_im]
  have hsq_mem : ∀ (p : ℤ × ℤ) (z : ℂ), z ∈ gridSquare δ p ↔
      (δ * p.1 ≤ z.re ∧ z.re ≤ δ * (p.1 + 1)) ∧
      (δ * p.2 ≤ z.im ∧ z.im ≤ δ * (p.2 + 1)) := by
    intro p z
    exact Iff.rfl
  have hKint : ∀ p : ℤ × ℤ, interior (gridSquare δ p) =
      Set.Ioo (δ * p.1) (δ * (p.1 + 1)) ×ℂ
        Set.Ioo (δ * p.2) (δ * (p.2 + 1)) := by
    intro p
    have hKeq : gridSquare δ p =
        Set.Icc (δ * p.1) (δ * (p.1 + 1)) ×ℂ
          Set.Icc (δ * p.2) (δ * (p.2 + 1)) := rfl
    rw [hKeq, Complex.interior_reProdIm, interior_Icc, interior_Icc]
  have hgp00 : gridPoint δ (0, 0) = 0 := by
    simp [gridPoint]
  have hc₀eq : c₀ = ((δ / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
    rw [hc₀_def]
    simp only [gridSquareCenter, hgp00, zero_add]
    push_cast
    ring
  have hcre : c₀.re = δ / 2 := by
    rw [hc₀eq]
    simp [Complex.mul_re]
  have hcim : c₀.im = δ / 2 := by
    rw [hc₀eq]
    simp [Complex.mul_im]
  have hnorm_le : ∀ z : ℂ, ‖z‖ ≤ |z.re| + |z.im| := by
    intro z
    calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
          rw [Complex.re_add_im]
      _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z.re| + |z.im| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  -- Every point of the plane lies in the square of its floor indices;
  -- squares meeting `A'` have indices in the box.
  have hfloor : ∀ w : ℂ, w ∈ gridSquare δ (⌊w.re / δ⌋, ⌊w.im / δ⌋) := by
    intro w
    have hre1 : δ * (⌊w.re / δ⌋ : ℝ) ≤ w.re := by
      have h1 : (⌊w.re / δ⌋ : ℝ) ≤ w.re / δ := Int.floor_le _
      have h2 : δ * (⌊w.re / δ⌋ : ℝ) ≤ δ * (w.re / δ) := by nlinarith
      calc δ * (⌊w.re / δ⌋ : ℝ) ≤ δ * (w.re / δ) := h2
        _ = w.re := by field_simp
    have hre2 : w.re ≤ δ * ((⌊w.re / δ⌋ : ℝ) + 1) := by
      have h1 : w.re / δ < (⌊w.re / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : w.re < ((⌊w.re / δ⌋ : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h1
      nlinarith
    have him1 : δ * (⌊w.im / δ⌋ : ℝ) ≤ w.im := by
      have h1 : (⌊w.im / δ⌋ : ℝ) ≤ w.im / δ := Int.floor_le _
      have h2 : δ * (⌊w.im / δ⌋ : ℝ) ≤ δ * (w.im / δ) := by nlinarith
      calc δ * (⌊w.im / δ⌋ : ℝ) ≤ δ * (w.im / δ) := h2
        _ = w.im := by field_simp
    have him2 : w.im ≤ δ * ((⌊w.im / δ⌋ : ℝ) + 1) := by
      have h1 : w.im / δ < (⌊w.im / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h2 : w.im < ((⌊w.im / δ⌋ : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp h1
      nlinarith
    exact ⟨⟨hre1, hre2⟩, him1, him2⟩
  have hbox : ∀ p : ℤ × ℤ, (gridSquare δ p ∩ A').Nonempty → p ∈ B₀ := by
    rintro p ⟨x, hxsq, hxA⟩
    have hxball := hN hxA
    rw [Metric.mem_ball, dist_zero_right] at hxball
    have hre : |x.re| < δ * N :=
      lt_of_le_of_lt (Complex.abs_re_le_norm x) hxball
    have him : |x.im| < δ * N :=
      lt_of_le_of_lt (Complex.abs_im_le_norm x) hxball
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hsq_mem p x).mp hxsq
    rw [abs_lt] at hre him
    have hp1u : (p.1 : ℝ) < N := by nlinarith [hre.2, hre.1]
    have hp1l : -(N : ℝ) < (p.1 : ℝ) + 1 := by nlinarith [hre.1]
    have hp2u : (p.2 : ℝ) < N := by nlinarith [him.2]
    have hp2l : -(N : ℝ) < (p.2 : ℝ) + 1 := by nlinarith [him.1]
    have hi1 : p.1 < (N : ℤ) := by exact_mod_cast hp1u
    have hi2 : -(N : ℤ) < p.1 + 1 := by exact_mod_cast hp1l
    have hi3 : p.2 < (N : ℤ) := by exact_mod_cast hp2u
    have hi4 : -(N : ℤ) < p.2 + 1 := by exact_mod_cast hp2l
    rw [hB₀_def, Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hcoverA : A' ⊆ ⋃ p ∈ S, gridSquare δ p := by
    intro w hw
    have hwsq := hfloor w
    have hne : (gridSquare δ (⌊w.re / δ⌋, ⌊w.im / δ⌋) ∩ A').Nonempty :=
      ⟨w, hwsq, hw⟩
    have hpS : (⌊w.re / δ⌋, ⌊w.im / δ⌋) ∈ S := by
      rw [hS_def, Finset.mem_filter]
      exact ⟨hbox _ hne, hne⟩
    exact Set.mem_biUnion hpS hwsq
  -- Squares of `S` avoid the rest of the complement (diameter < ε), hence
  -- lie in `T' ∪ A'`.
  have hsq_diam : ∀ p : ℤ × ℤ, ∀ x y : ℂ, x ∈ gridSquare δ p →
      y ∈ gridSquare δ p → dist x y ≤ 2 * δ := by
    intro p x y hx hy
    obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := (hsq_mem p x).mp hx
    obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := (hsq_mem p y).mp hy
    have hexp1 : δ * ((p.1 : ℝ) + 1) = δ * p.1 + δ := by ring
    have hexp2 : δ * ((p.2 : ℝ) + 1) = δ * p.2 + δ := by ring
    rw [hexp1] at hx2 hy2
    rw [hexp2] at hx4 hy4
    rw [dist_eq_norm]
    calc ‖x - y‖ ≤ |(x - y).re| + |(x - y).im| := hnorm_le _
      _ ≤ δ + δ := by
          rw [Complex.sub_re, Complex.sub_im]
          have h1 : |x.re - y.re| ≤ δ := by
            rw [abs_le]
            constructor <;> linarith
          have h2 : |x.im - y.im| ≤ δ := by
            rw [abs_le]
            constructor <;> linarith
          linarith
      _ = 2 * δ := by ring
  have hSsub : ∀ p ∈ S, gridSquare δ p ⊆ T' ∪ A' := by
    intro p hp x hx
    by_contra hxn
    rw [Set.mem_union] at hxn
    push Not at hxn
    obtain ⟨hxT, hxA⟩ := hxn
    rw [hS_def, Finset.mem_filter] at hp
    obtain ⟨-, a, hasq, haA⟩ := hp
    have hd := hsep' x hxT hxA a haA
    have hdle := hsq_diam p x a hx hasq
    rw [hδ_def] at hdle
    linarith
  -- The marked square: `(0,0) ∈ S`, `c₀` interior to it and to no other.
  have hc₀sq : c₀ ∈ gridSquare δ (0, 0) := by
    rw [hsq_mem (0, 0) c₀]
    rw [hcre, hcim]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> push_cast <;> nlinarith
  have h00 : (0, 0) ∈ S := by
    rw [hS_def, Finset.mem_filter]
    refine ⟨?_, c₀, hc₀sq, hc₀A'⟩
    rw [hB₀_def, Finset.mem_Icc]
    constructor
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
    · rw [Prod.le_def]
      exact ⟨by omega, by omega⟩
  have hc₀in : c₀ ∈ interior (gridSquare δ (0, 0)) := by
    rw [hKint, Complex.mem_reProdIm, hcre, hcim]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> push_cast <;> nlinarith
  have hc₀only : ∀ p : ℤ × ℤ, p ≠ (0, 0) → c₀ ∉ gridSquare δ p := by
    intro p hp hmem
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hsq_mem p c₀).mp hmem
    rw [hcre] at h1 h2
    rw [hcim] at h3 h4
    have hp1 : p.1 = 0 := by
      have ha : (p.1 : ℝ) < 1 := by
        by_contra hcon
        push Not at hcon
        have : δ * 1 ≤ δ * (p.1 : ℝ) := by nlinarith
        linarith
      have hb : (-1 : ℝ) < (p.1 : ℝ) := by
        by_contra hcon
        push Not at hcon
        have : δ * ((p.1 : ℝ) + 1) ≤ δ * 0 := by nlinarith
        linarith
      have ha' : p.1 < 1 := by exact_mod_cast ha
      have hb' : (-1 : ℤ) < p.1 := by exact_mod_cast hb
      omega
    have hp2 : p.2 = 0 := by
      have ha : (p.2 : ℝ) < 1 := by
        by_contra hcon
        push Not at hcon
        have : δ * 1 ≤ δ * (p.2 : ℝ) := by nlinarith
        linarith
      have hb : (-1 : ℝ) < (p.2 : ℝ) := by
        by_contra hcon
        push Not at hcon
        have : δ * ((p.2 : ℝ) + 1) ≤ δ * 0 := by nlinarith
        linarith
      have ha' : p.2 < 1 := by exact_mod_cast ha
      have hb' : (-1 : ℤ) < p.2 := by exact_mod_cast hb
      omega
    exact hp (Prod.ext_iff.mpr ⟨hp1, hp2⟩)
  -- `c₀` is off every grid line (both coordinates are half-integer
  -- multiples of `δ`), hence off every grid-path trace.
  have hhalf_ne : ∀ n : ℤ, δ / 2 ≠ δ * n := by
    intro n heq
    have h' : δ * (1 / 2 : ℝ) = δ * (n : ℝ) := by linarith
    have h2 : (1 / 2 : ℝ) = (n : ℝ) := mul_left_cancel₀ (ne_of_gt hδ) h'
    have h3 : (2 * n : ℝ) = 1 := by linarith
    have h4 : (2 * n : ℤ) = 1 := by exact_mod_cast h3
    omega
  have hc₀line : ∀ q : ℤ × ℤ, ∀ w ∈ segment ℝ (gridPoint δ q)
      (gridPoint δ (q.1 + 1, q.2)), c₀ ≠ w := by
    intro q w hw heq
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have him : w.im = δ * q.2 := by
      rw [← hwe, hsegim, hgim, hgim]
      show u * (δ * (q.2 : ℝ)) + v * (δ * (q.2 : ℝ)) = δ * q.2
      have : u * (δ * (q.2 : ℝ)) + v * (δ * (q.2 : ℝ)) =
          (u + v) * (δ * q.2) := by ring
      rw [this, huv, one_mul]
    have : δ / 2 = δ * q.2 := by rw [← hcim, heq, him]
    exact hhalf_ne q.2 this
  have hc₀line' : ∀ q : ℤ × ℤ, ∀ w ∈ segment ℝ (gridPoint δ q)
      (gridPoint δ (q.1, q.2 + 1)), c₀ ≠ w := by
    intro q w hw heq
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have hre : w.re = δ * q.1 := by
      rw [← hwe, hsegre, hgre, hgre]
      show u * (δ * (q.1 : ℝ)) + v * (δ * (q.1 : ℝ)) = δ * q.1
      have : u * (δ * (q.1 : ℝ)) + v * (δ * (q.1 : ℝ)) =
          (u + v) * (δ * q.1) := by ring
      rw [this, huv, one_mul]
    have : δ / 2 = δ * q.1 := by rw [← hcre, heq, hre]
    exact hhalf_ne q.1 this
  -- ================================================================
  -- STAGE 2: the oriented boundary-edge set `E` (counterclockwise around
  -- `S`) and its vertex balance.
  -- ================================================================
  -- Oriented edges are ordered pairs of adjacent lattice indices; the
  -- boundary keeps an edge iff exactly one adjacent square is in `S`,
  -- oriented with the `S`-square on the left.
  set B₁ : Finset (ℤ × ℤ) :=
    Finset.Icc (-(N : ℤ) - 3, -(N : ℤ) - 3) ((N : ℤ) + 3, (N : ℤ) + 3)
    with hB₁_def
  set bdry : (ℤ × ℤ) × (ℤ × ℤ) → Prop := fun e =>
    -- rightward: from (i,j) to (i+1,j), square above (i,j) in S,
    -- square below (i,j-1) not in S
    (e.2 = (e.1.1 + 1, e.1.2) ∧ (e.1.1, e.1.2) ∈ S ∧ (e.1.1, e.1.2 - 1) ∉ S) ∨
    -- leftward: from (i+1,j) to (i,j)
    (e.1 = (e.2.1 + 1, e.2.2) ∧ (e.2.1, e.2.2 - 1) ∈ S ∧ (e.2.1, e.2.2) ∉ S) ∨
    -- upward: from (i,j) to (i,j+1), square left (i-1,j) in S,
    -- square right (i,j) not in S
    (e.2 = (e.1.1, e.1.2 + 1) ∧ (e.1.1 - 1, e.1.2) ∈ S ∧ (e.1.1, e.1.2) ∉ S) ∨
    -- downward: from (i,j+1) to (i,j)
    (e.1 = (e.2.1, e.2.2 + 1) ∧ (e.2.1, e.2.2) ∈ S ∧ (e.2.1 - 1, e.2.2) ∉ S)
    with hbdry_def
  set E : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := (B₁ ×ˢ B₁).filter bdry with hE_def
  -- Squares of `S` have box-bounded indices, so boundary-edge endpoints
  -- lie in the bigger box `B₁`; membership in `E` is exactly `bdry`.
  have hSbound : ∀ p ∈ S, -(N : ℤ) - 2 ≤ p.1 ∧ p.1 ≤ (N : ℤ) + 2 ∧
      -(N : ℤ) - 2 ≤ p.2 ∧ p.2 ≤ (N : ℤ) + 2 := by
    intro p hp
    rw [hS_def, Finset.mem_filter, hB₀_def, Finset.mem_Icc] at hp
    obtain ⟨⟨hlo, hhi⟩, -⟩ := hp
    rw [Prod.le_def] at hlo hhi
    exact ⟨hlo.1, hhi.1, hlo.2, hhi.2⟩
  have hB₁mem : ∀ a : ℤ × ℤ, -(N : ℤ) - 3 ≤ a.1 → a.1 ≤ (N : ℤ) + 3 →
      -(N : ℤ) - 3 ≤ a.2 → a.2 ≤ (N : ℤ) + 3 → a ∈ B₁ := by
    intro a h1 h2 h3 h4
    rw [hB₁_def, Finset.mem_Icc]
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  have hbdry_bound : ∀ e : (ℤ × ℤ) × (ℤ × ℤ), bdry e → e ∈ B₁ ×ˢ B₁ := by
    intro e h
    rw [hbdry_def] at h
    rw [Finset.mem_product]
    rcases h with ⟨he, hs, -⟩ | ⟨he, hs, -⟩ | ⟨he, hs, -⟩ | ⟨he, hs, -⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.1.1 := q1
      have b2 : e.1.1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.1.2 := q3
      have b4 : e.1.2 ≤ (N : ℤ) + 2 := q4
      have h21 : e.2.1 = e.1.1 + 1 := by rw [he]
      have h22 : e.2.2 = e.1.2 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.2.1 := q1
      have b2 : e.2.1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.2.2 - 1 := q3
      have b4 : e.2.2 - 1 ≤ (N : ℤ) + 2 := q4
      have h11 : e.1.1 = e.2.1 + 1 := by rw [he]
      have h12 : e.1.2 = e.2.2 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.1.1 - 1 := q1
      have b2 : e.1.1 - 1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.1.2 := q3
      have b4 : e.1.2 ≤ (N : ℤ) + 2 := q4
      have h21 : e.2.1 = e.1.1 := by rw [he]
      have h22 : e.2.2 = e.1.2 + 1 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
    · obtain ⟨q1, q2, q3, q4⟩ := hSbound _ hs
      have b1 : -(N : ℤ) - 2 ≤ e.2.1 := q1
      have b2 : e.2.1 ≤ (N : ℤ) + 2 := q2
      have b3 : -(N : ℤ) - 2 ≤ e.2.2 := q3
      have b4 : e.2.2 ≤ (N : ℤ) + 2 := q4
      have h11 : e.1.1 = e.2.1 := by rw [he]
      have h12 : e.1.2 = e.2.2 + 1 := by rw [he]
      exact ⟨hB₁mem e.1 (by omega) (by omega) (by omega) (by omega),
        hB₁mem e.2 (by omega) (by omega) (by omega) (by omega)⟩
  have hEmem : ∀ e : (ℤ × ℤ) × (ℤ × ℤ), e ∈ E ↔ bdry e := by
    intro e
    rw [hE_def, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hbdry_bound e h, h⟩⟩
  -- Vertex balance: at every lattice vertex, the number of `E`-edges
  -- entering equals the number leaving (case analysis on the membership
  -- pattern of the four squares at the vertex).
  have hbal : ∀ v : ℤ × ℤ,
      (E.filter (fun e => e.2 = v)).card =
        (E.filter (fun e => e.1 = v)).card := by
    intro v
    clear * - hEmem hbdry_def
    obtain ⟨v1, v2⟩ := v
    -- Membership characterizations for the eight candidate edges at `v`,
    -- in terms of the four squares at `v`.
    have hc1E : ((((v1 - 1, v2), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2) ∈ S ∧ (v1 - 1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inl ⟨?_, hs, hn⟩
        show ((v1, v2) : ℤ × ℤ) = (v1 - 1 + 1, v2)
        congr 1
        omega
    have hc2E : ((((v1 + 1, v2), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2 - 1) ∈ S ∧ (v1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inl ⟨?_, hs, hn⟩)
        exact trivial
    have hc3E : ((((v1, v2 - 1), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2 - 1) ∈ S ∧ (v1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inl ⟨?_, hs, hn⟩))
        show ((v1, v2) : ℤ × ℤ) = (v1, v2 - 1 + 1)
        congr 1
        omega
    have hc4E : ((((v1, v2 + 1), (v1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2) ∈ S ∧ (v1 - 1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inr ⟨?_, hs, hn⟩))
        trivial
    have hd1E : ((((v1, v2), (v1 + 1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2) ∈ S ∧ (v1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inl ⟨?_, hs, hn⟩
        exact trivial
    have hd2E : ((((v1, v2), (v1 - 1, v2))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2 - 1) ∈ S ∧ (v1 - 1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inl ⟨?_, hs, hn⟩)
        show ((v1, v2) : ℤ × ℤ) = (v1 - 1 + 1, v2)
        congr 1
        omega
    have hd3E : ((((v1, v2), (v1, v2 + 1))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1 - 1, v2) ∈ S ∧ (v1, v2) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
        · injection h with h1 h2
          exfalso
          omega
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inl ⟨?_, hs, hn⟩))
        trivial
    have hd4E : ((((v1, v2), (v1, v2 - 1))) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E ↔
        ((v1, v2 - 1) ∈ S ∧ (v1 - 1, v2 - 1) ∉ S) := by
      rw [hEmem]
      simp only [hbdry_def]
      constructor
      · rintro (⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩ | ⟨h, hs, hn⟩)
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · injection h with h1 h2
          exfalso
          omega
        · exact ⟨hs, hn⟩
      · rintro ⟨hs, hn⟩
        refine Or.inr (Or.inr (Or.inr ⟨?_, hs, hn⟩))
        show ((v1, v2) : ℤ × ℤ) = (v1, v2 - 1 + 1)
        congr 1
        omega
    -- Every in-edge is one of the four candidates, and dually.
    have hin_eq : E.filter (fun e => e.2 = (v1, v2)) =
        ({((v1 - 1, v2), (v1, v2)), ((v1 + 1, v2), (v1, v2)),
          ((v1, v2 - 1), (v1, v2)), ((v1, v2 + 1), (v1, v2))} :
            Finset ((ℤ × ℤ) × (ℤ × ℤ))).filter (fun e => e ∈ E) := by
      ext e
      obtain ⟨⟨x, y⟩, s, t⟩ := e
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨heE, he2⟩
        refine ⟨?_, heE⟩
        injection he2 with hs1 hs2
        have hb := (hEmem ((x, y), s, t)).mp heE
        simp only [hbdry_def] at hb
        simp only [Prod.mk.injEq]
        rcases hb with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
          (injection h with h1 h2
           omega)
      · rintro ⟨h | h | h | h, heE⟩ <;>
          exact ⟨heE, congrArg Prod.snd h⟩
    have hout_eq : E.filter (fun e => e.1 = (v1, v2)) =
        ({((v1, v2), (v1 + 1, v2)), ((v1, v2), (v1 - 1, v2)),
          ((v1, v2), (v1, v2 + 1)), ((v1, v2), (v1, v2 - 1))} :
            Finset ((ℤ × ℤ) × (ℤ × ℤ))).filter (fun e => e ∈ E) := by
      ext e
      obtain ⟨⟨x, y⟩, s, t⟩ := e
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨heE, he1⟩
        refine ⟨?_, heE⟩
        injection he1 with hs1 hs2
        have hb := (hEmem ((x, y), s, t)).mp heE
        simp only [hbdry_def] at hb
        simp only [Prod.mk.injEq]
        rcases hb with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
          (injection h with h1 h2
           omega)
      · rintro ⟨h | h | h | h, heE⟩ <;>
          exact ⟨heE, congrArg Prod.fst h⟩
    -- Cards as indicator sums over the four candidates.
    have hin_card : (E.filter (fun e => e.2 = (v1, v2))).card =
        (if (((v1 - 1, v2), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1 + 1, v2), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1, v2 - 1), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        (if (((v1, v2 + 1), (v1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0))) := by
      rw [hin_eq, Finset.card_filter]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_singleton]
    have hout_card : (E.filter (fun e => e.1 = (v1, v2))).card =
        (if (((v1, v2), (v1 + 1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1, v2), (v1 - 1, v2)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        ((if (((v1, v2), (v1, v2 + 1)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0) +
        (if (((v1, v2), (v1, v2 - 1)) : (ℤ × ℤ) × (ℤ × ℤ)) ∈ E then 1 else 0))) := by
      rw [hout_eq, Finset.card_filter]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      rw [Finset.sum_singleton]
    rw [hin_card, hout_card]
    rw [if_congr hc1E rfl rfl, if_congr hc2E rfl rfl, if_congr hc3E rfl rfl,
      if_congr hc4E rfl rfl, if_congr hd1E rfl rfl, if_congr hd2E rfl rfl,
      if_congr hd3E rfl rfl, if_congr hd4E rfl rfl]
    -- telescoping indicator identity: [P ∧ ¬Q] + [Q] = [Q ∧ ¬P] + [P]
    have hf : ∀ P Q : Prop, ∀ (_ : Decidable P) (_ : Decidable Q),
        (if P ∧ ¬Q then (1 : ℕ) else 0) + (if Q then 1 else 0) =
          (if Q ∧ ¬P then 1 else 0) + (if P then 1 else 0) := by
      intro P Q dP dQ
      by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
    have h1 := hf ((v1 - 1, v2) ∈ S) ((v1 - 1, v2 - 1) ∈ S)
      inferInstance inferInstance
    have h2 := hf ((v1, v2 - 1) ∈ S) ((v1, v2) ∈ S)
      inferInstance inferInstance
    have h3 := hf ((v1 - 1, v2 - 1) ∈ S) ((v1, v2 - 1) ∈ S)
      inferInstance inferInstance
    have h4 := hf ((v1, v2) ∈ S) ((v1 - 1, v2) ∈ S)
      inferInstance inferInstance
    linarith [h1, h2, h3, h4]
  have hseg_h : ∀ (i j : ℤ), ∀ w ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i + 1, j)),
      w.im = δ * j ∧ δ * i ≤ w.re ∧ w.re ≤ δ * (i + 1) := by
    intro i j w hw
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have hv1 : v ≤ 1 := by linarith
    have hre : w.re = δ * i + v * δ := by
      rw [← hwe, hsegre, hgre, hgre]
      push_cast
      linear_combination (δ * (i : ℝ)) * huv
    have him : w.im = δ * j := by
      rw [← hwe, hsegim, hgim, hgim]
      show u * (δ * (j : ℝ)) + v * (δ * (j : ℝ)) = δ * j
      linear_combination (δ * (j : ℝ)) * huv
    refine ⟨him, ?_, ?_⟩
    · rw [hre]
      nlinarith
    · rw [hre]
      nlinarith
  have hseg_v : ∀ (i j : ℤ), ∀ w ∈ segment ℝ (gridPoint δ (i, j))
      (gridPoint δ (i, j + 1)),
      w.re = δ * i ∧ δ * j ≤ w.im ∧ w.im ≤ δ * (j + 1) := by
    intro i j w hw
    obtain ⟨u, v, hu, hv, huv, hwe⟩ := hw
    have hv1 : v ≤ 1 := by linarith
    have him : w.im = δ * j + v * δ := by
      rw [← hwe, hsegim, hgim, hgim]
      push_cast
      linear_combination (δ * (j : ℝ)) * huv
    have hre : w.re = δ * i := by
      rw [← hwe, hsegre, hgre, hgre]
      show u * (δ * (i : ℝ)) + v * (δ * (i : ℝ)) = δ * i
      linear_combination (δ * (i : ℝ)) * huv
    refine ⟨hre, ?_, ?_⟩
    · rw [him]
      nlinarith
    · rw [him]
      nlinarith
  have hkey : ∀ (pS pN : ℤ × ℤ) (w : ℂ), pS ∈ S → pN ∉ S →
      w ∈ gridSquare δ pS → w ∈ gridSquare δ pN → w ∈ T' := by
    intro pS pN w hpS hpN hwS hwN
    rcases hSsub pS hpS hwS with hwT | hwA
    · exact hwT
    · exact absurd (by
        rw [hS_def, Finset.mem_filter]
        exact ⟨hbox pN ⟨w, hwN, hwA⟩, ⟨w, hwN, hwA⟩⟩) hpN
  have hET : ∀ e ∈ E, segment ℝ (gridPoint δ e.1) (gridPoint δ e.2) ⊆ T' := by
    intro e he w hw
    clear * - hEmem hbdry_def hseg_h hseg_v hkey hsq_mem hδ he hw
    rw [hEmem, hbdry_def] at he
    obtain ⟨⟨i, j⟩, ⟨k, l⟩⟩ := e
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨⟨hk, hl⟩, hs, hn⟩ | ⟨⟨hi, hj⟩, hs, hn⟩ |
      ⟨⟨hk, hl⟩, hs, hn⟩ | ⟨⟨hi, hj⟩, hs, hn⟩
    · -- rightward from (i,j) to (i+1,j): S-square (i,j) above, (i,j-1) below
      rw [hk, hl] at hw
      obtain ⟨him, hre1, hre2⟩ := hseg_h i j w hw
      refine hkey (i, j) (i, j - 1) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him]
        push_cast
        nlinarith
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him] <;> push_cast <;> nlinarith
    · -- leftward: from (i,j) = (k+1,l) to (k,l);
      -- S-square (k, l-1) below, (k, l) above
      rw [hi, hj, segment_symm] at hw
      obtain ⟨him, hre1, hre2⟩ := hseg_h k l w hw
      refine hkey (k, l - 1) (k, l) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him] <;> push_cast <;> nlinarith
      · rw [hsq_mem]
        refine ⟨⟨hre1, hre2⟩, ?_, ?_⟩ <;> rw [him]
        push_cast
        nlinarith
    · -- upward from (i,j) to (i,j+1): S-square (i-1,j) left, (i,j) right
      rw [hk, hl] at hw
      obtain ⟨hre, him1, him2⟩ := hseg_v i j w hw
      refine hkey (i - 1, j) (i, j) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre] <;> push_cast <;> nlinarith
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre]
        push_cast
        nlinarith
    · -- downward: from (i,j) = (k,l+1) to (k,l);
      -- S-square (k,l) right, (k-1,l) left
      rw [hi, hj, segment_symm] at hw
      obtain ⟨hre, him1, him2⟩ := hseg_v k l w hw
      refine hkey (k, l) (k - 1, l) w hs hn ?_ ?_
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre]
        push_cast
        nlinarith
      · rw [hsq_mem]
        refine ⟨⟨?_, ?_⟩, him1, him2⟩ <;> rw [hre] <;> push_cast <;> nlinarith
  -- ================================================================
  -- STAGE 3: per-edge principal-logarithm increments.
  -- ================================================================
  -- For `q` off a closed segment, the endpoint ratio avoids `ℝ≤0`.
  have hslit : ∀ a b q : ℂ, (∀ w ∈ segment ℝ a b, q ≠ w) →
      (b - q) / (a - q) ∈ Complex.slitPlane := by
    intro a b q hoff
    clear * - hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr fun h => hoff a (left_mem_segment ℝ a b) h.symm
    by_contra hns
    rw [Complex.mem_slitPlane_iff] at hns
    push Not at hns
    obtain ⟨hre, him⟩ := hns
    set r : ℝ := ((b - q) / (a - q)).re with hr_def
    have hratio : (b - q) / (a - q) = ((r : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im]
        exact him
    have hbq : b - q = ((r : ℝ) : ℂ) * (a - q) := by
      rw [← hratio, div_mul_cancel₀ _ haq]
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have hqseg : q ∈ segment ℝ a b := by
      refine ⟨-r / (1 - r), 1 / (1 - r), div_nonneg (by linarith) h1r.le,
        by positivity, ?_, ?_⟩
      · field_simp
        ring
      · rw [Complex.real_smul, Complex.real_smul]
        push_cast
        have hcne : ((1 : ℂ) - (r : ℂ)) ≠ 0 := by
          have : ((1 - r : ℝ) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt h1r)
          push_cast at this
          exact this
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          div_eq_iff hcne]
        linear_combination hbq
    exact hoff q hqseg rfl
  -- The per-edge increment.
  set inc : (ℤ × ℤ) × (ℤ × ℤ) → ℂ → ℂ := fun e q =>
    Complex.log ((gridPoint δ e.2 - q) / (gridPoint δ e.1 - q)) with hinc_def
  -- Reversal negates the increment.
  have hincrev : ∀ (a b : ℤ × ℤ) (q : ℂ),
      (∀ w ∈ segment ℝ (gridPoint δ a) (gridPoint δ b), q ≠ w) →
      gridPoint δ a ≠ gridPoint δ b →
      inc (b, a) q = -inc (a, b) q := by
    intro a b q hoff _hab
    clear * - hslit hinc_def hoff
    have hx : (gridPoint δ b - q) / (gridPoint δ a - q) ∈ Complex.slitPlane :=
      hslit _ _ q hoff
    have harg : ((gridPoint δ b - q) / (gridPoint δ a - q)).arg ≠ Real.pi :=
      Complex.slitPlane_arg_ne_pi hx
    simp only [hinc_def]
    have hswap : (gridPoint δ a - q) / (gridPoint δ b - q) =
        ((gridPoint δ b - q) / (gridPoint δ a - q))⁻¹ := (inv_div _ _).symm
    rw [hswap, Complex.log_inv _ harg]
  -- Lift gluing: `2πi · wind = Σ inc` over the consecutive pairs of a
  -- closed grid path avoiding `q` (explicit piecewise principal-log lift
  -- glued with accumulated constants; `windingNumber_spec` pins the value).
  -- Points of a parametrized segment lie in the segment.
  have hsegmem : ∀ (a b : ℂ) (s : unitInterval),
      segmentPath a b s ∈ segment ℝ a b := by
    intro a b s
    clear * -
    refine ⟨1 - (s : ℝ), (s : ℝ), by linarith [s.2.2], s.2.1, by ring, ?_⟩
    show (1 - (s : ℝ)) • a + (s : ℝ) • b = a + ((s : ℝ) : ℂ) * (b - a)
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  -- The principal-log lift along one segment avoided by `q`.
  have hseglift : ∀ a b q : ℂ, (∀ w ∈ segment ℝ a b, q ≠ w) →
      ∃ f : C(unitInterval, ℂ),
        (∀ s : unitInterval, Complex.exp (f s) = segmentPath a b s - q) ∧
        f 1 - f 0 = Complex.log ((b - q) / (a - q)) ∧
        Complex.exp (f 1) = b - q := by
    intro a b q hoff
    clear * - hslit hsegmem hoff
    have haq : a - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hoff a (left_mem_segment ℝ a b)))
    have hgmem : ∀ s : unitInterval,
        (segmentPath a b s - q) / (a - q) ∈ Complex.slitPlane := by
      intro s
      refine hslit a (segmentPath a b s) q ?_
      intro w hw
      exact hoff w ((convex_segment a b).segment_subset
        (left_mem_segment ℝ a b) (hsegmem a b s) hw)
    have hgcont : Continuous fun s : unitInterval =>
        (segmentPath a b s - q) / (a - q) :=
      ((segmentPath a b).continuous.sub continuous_const).div_const _
    have hfcont : Continuous fun s : unitInterval =>
        Complex.log ((segmentPath a b s - q) / (a - q)) +
          Complex.log (a - q) := by
      refine Continuous.add ?_ continuous_const
      rw [continuous_iff_continuousAt]
      intro s
      exact hgcont.continuousAt.clog (hgmem s)
    refine ⟨⟨fun s => Complex.log ((segmentPath a b s - q) / (a - q)) +
      Complex.log (a - q), hfcont⟩, ?_, ?_, ?_⟩
    · intro s
      show Complex.exp (Complex.log ((segmentPath a b s - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [Complex.exp_add, Complex.exp_log haq,
        Complex.exp_log (Complex.slitPlane_ne_zero (hgmem s)),
        div_mul_cancel₀ _ haq]
    · show (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) - (Complex.log ((segmentPath a b 0 - q) /
          (a - q)) + Complex.log (a - q)) = _
      rw [(segmentPath a b).source, (segmentPath a b).target,
        div_self haq, Complex.log_one]
      ring
    · show Complex.exp (Complex.log ((segmentPath a b 1 - q) / (a - q)) +
        Complex.log (a - q)) = _
      rw [(segmentPath a b).target, Complex.exp_add, Complex.exp_log haq]
      have hbq : b - q ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (hoff b (right_mem_segment ℝ a b)))
      rw [Complex.exp_log (by
        exact div_ne_zero hbq haq), div_mul_cancel₀ _ haq]
  -- The glued lift along a grid path, by induction on the path.
  have hliftInd : ∀ (Lst : List (ℤ × ℤ)) (p : ℤ × ℤ),
      IsGridPath (p :: Lst) →
      ∀ q : ℂ, (∀ w ∈ gridPathTrace δ (p :: Lst), q ≠ w) →
      ∃ Lf : C(unitInterval, ℂ),
        IsLogLiftOf Lf
          (shiftedCurve (gridPathRealize δ p Lst).toContinuousMap q) ∧
        Lf 1 - Lf 0 = (((p :: Lst).zip Lst).map (fun e => inc e q)).sum := by
    intro Lst
    clear * - hseglift
    induction Lst with
    | nil =>
      intro p _ q hoff
      have hqp : q ≠ gridPoint δ p := hoff _ rfl
      refine ⟨ContinuousMap.const unitInterval
        (Complex.log (gridPoint δ p - q)), ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        rw [Complex.exp_log (sub_ne_zero.mpr (Ne.symm hqp))]
        show gridPoint δ p - q = (Path.refl (gridPoint δ p)) t - q
        simp
      · simp
    | cons r M ih =>
      intro p hpath q hoff
      have htail : IsGridPath (r :: M) :=
        (List.isChain_cons_cons.mp hpath).2
      have hofftrace : ∀ w ∈ gridPathTrace δ (r :: M), q ≠ w :=
        fun w hw => hoff w (Or.inr hw)
      have hoffseg : ∀ w ∈ segment ℝ (gridPoint δ p) (gridPoint δ r),
          q ≠ w := fun w hw => hoff w (Or.inl hw)
      obtain ⟨Lrest, hLrest, hLrest_inc⟩ := ih r htail q hofftrace
      obtain ⟨fseg, hfseg_lift, hfseg_inc, hfseg1⟩ :=
        hseglift (gridPoint δ p) (gridPoint δ r) q hoffseg
      have hbq : gridPoint δ r - q ≠ 0 := by
        rw [← hfseg1]
        exact Complex.exp_ne_zero _
      -- the rest lift starts at the seam value `gridPoint δ r − q`
      have hLrest0 : Complex.exp (Lrest 0) = gridPoint δ r - q := by
        have h := hLrest 0
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] at h
        rw [h, (gridPathRealize δ r M).source]
      have hexpc : Complex.exp (fseg 1 - Lrest 0) = 1 := by
        rw [Complex.exp_sub, hfseg1, hLrest0, div_self hbq]
      have hstart : (Lrest + ContinuousMap.const unitInterval
          (fseg 1 - Lrest 0)) 0 = fseg 1 := by
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        ring
      have hLrest'_lift : ∀ t, Complex.exp ((Lrest +
          ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) t) =
          (gridPathRealize δ r M) t - q := by
        intro t
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [Complex.exp_add, hexpc, mul_one]
        have h := hLrest t
        simpa only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap] using h
      refine ⟨((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
        (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
          hstart, rfl⟩ : Path (fseg 1) ((Lrest +
            ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
          ).toContinuousMap, ?_, ?_⟩
      · intro t
        simp only [shiftedCurve, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, Path.coe_toContinuousMap]
        show Complex.exp _ =
          ((segmentPath (gridPoint δ p) (gridPoint δ r)).trans
            (gridPathRealize δ r M)) t - q
        rw [Path.trans_apply, Path.trans_apply]
        split_ifs with ht
        · exact hfseg_lift _
        · exact hLrest'_lift _
      · have h0 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 0 = fseg 0 := by simp
        have h1 : ((⟨fseg, rfl, rfl⟩ : Path (fseg 0) (fseg 1)).trans
            (⟨Lrest + ContinuousMap.const unitInterval (fseg 1 - Lrest 0),
              hstart, rfl⟩ : Path (fseg 1) ((Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1))
              ).toContinuousMap 1 = (Lrest +
                ContinuousMap.const unitInterval (fseg 1 - Lrest 0)) 1 := by
          simp
        rw [h0, h1]
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        rw [List.zip_cons_cons, List.map_cons, List.sum_cons, ← hLrest_inc]
        have hincpr : inc (p, r) q =
            Complex.log ((gridPoint δ r - q) / (gridPoint δ p - q)) := rfl
        rw [hincpr, ← hfseg_inc]
        ring
  have hlift : ∀ (L : List (ℤ × ℤ)), IsGridPath L → L ≠ [] →
      L.head? = L.getLast? →
      ∀ q : ℂ, (∀ w ∈ gridPathTrace δ L, q ≠ w) →
      (2 * Real.pi * Complex.I) * windingNumber (gridLoopCurve δ L) q =
        ((L.zip L.tail).map (fun e => inc e q)).sum := by
    intro L hL hne hcl q hoff
    clear * - hliftInd hδ hL hne hcl hoff
    obtain ⟨p, L', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨Lf, hLf, hLf_inc⟩ := hliftInd L' p hL q hoff
    have hclosed : gridLoopCurve δ (p :: L') 0 = gridLoopCurve δ (p :: L') 1 :=
      gridLoopCurve_closed (by simp) hcl
    have hrange : Set.range (gridLoopCurve δ (p :: L')) =
        gridPathTrace δ (p :: L') := range_gridLoopCurve hδ hL (by simp)
    have hq : ∀ t : unitInterval, gridLoopCurve δ (p :: L') t ≠ q := by
      intro t heq
      exact hoff _ (hrange ▸ Set.mem_range_self t) heq.symm
    have hspec := windingNumber_spec hclosed hq hLf
    rw [← hspec]
    exact hLf_inc
  -- ================================================================
  -- STAGE 4: square-boundary windings.
  -- ================================================================
  -- The counterclockwise boundary 5-cycle of the square at `p`.
  set sqB : ℤ × ℤ → List (ℤ × ℤ) := fun p =>
    [p, (p.1 + 1, p.2), (p.1 + 1, p.2 + 1), (p.1, p.2 + 1), p] with hsqB_def
  have hsqB_path : ∀ p, IsGridPath (sqB p) := by
    intro p
    show List.IsChain GridAdj _
    simp only [hsqB_def]
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
      List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_,
        List.isChain_singleton _⟩⟩⟩⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨rfl, by simp⟩
    · exact Or.inr ⟨by simp, rfl⟩
    · exact Or.inl ⟨rfl, by simp⟩
  have hsqB_closed : ∀ p, (sqB p).head? = (sqB p).getLast? := by
    intro p
    simp [hsqB_def]
  -- Interior points have winding one (four increments with positive-
  -- imaginary-part cross ratios summing into `(0, 4π)` ∩ `2πℤ` = `{2π}`,
  -- pinned by the telescoping product `exp (Σ inc) = 1`).
  have hratio_im : ∀ z w : ℂ, w ≠ 0 →
      0 < z.im * w.re - z.re * w.im → 0 < (z / w).im := by
    intro z w hw hcross
    rw [Complex.div_im]
    have hnormSq : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
    rw [div_sub_div_same]
    exact div_pos hcross hnormSq
  have hlog_im_bounds : ∀ z : ℂ, z ≠ 0 → 0 < z.im →
      0 < (Complex.log z).im ∧ (Complex.log z).im < Real.pi := by
    intro z hz him
    rw [Complex.log_im]
    constructor
    · rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr him.le) with h | h
      · exact h
      · exfalso
        have h0 := Complex.arg_eq_zero_iff.mp h.symm
        · linarith [h0.2]
    · rcases lt_or_eq_of_le (Complex.arg_le_pi z) with h | h
      · exact h
      · exfalso
        have h0 := Complex.arg_eq_pi_iff.mp h
        linarith [h0.2]
  have hsq_in : ∀ p : ℤ × ℤ, ∀ q ∈ interior (gridSquare δ p),
      windingNumber (gridLoopCurve δ (sqB p)) q = 1 := by
    intro p q hqint
    clear * - hKint hseg_h hseg_v hsqB_def hgre hgim hlog_im_bounds
      hratio_im hlift hsqB_path hsqB_closed hδ hqint
    rw [hKint, Complex.mem_reProdIm] at hqint
    obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hqint
    -- `q` avoids the boundary trace (strict interior coordinates).
    have hqoff : ∀ w ∈ gridPathTrace δ (sqB p), q ≠ w := by
      intro w hw heq
      simp only [hsqB_def, gridPathTrace] at hw
      rcases hw with h | h | h | h | h
      · obtain ⟨him, -, -⟩ := hseg_h p.1 p.2 w h
        rw [← heq] at him
        linarith
      · obtain ⟨hre, -, -⟩ := hseg_v (p.1 + 1) p.2 w h
        rw [← heq] at hre
        push_cast at hre
        linarith
      · rw [segment_symm] at h
        obtain ⟨him, -, -⟩ := hseg_h p.1 (p.2 + 1) w h
        rw [← heq] at him
        push_cast at him
        linarith
      · rw [segment_symm] at h
        obtain ⟨hre, -, -⟩ := hseg_v p.1 p.2 w h
        rw [← heq] at hre
        linarith
      · have hwp : w = gridPoint δ p := h
        have hqim : q.im = δ * p.2 := by rw [heq, hwp, hgim]
        linarith
    -- corner points are on the trace, hence differ from `q`
    have hmem1 : gridPoint δ p ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inl (left_mem_segment ℝ _ _)
    have hmem2 : gridPoint δ (p.1 + 1, p.2) ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inr (Or.inl (left_mem_segment ℝ _ _))
    have hmem3 : gridPoint δ (p.1 + 1, p.2 + 1) ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inr (Or.inr (Or.inl (left_mem_segment ℝ _ _)))
    have hmem4 : gridPoint δ (p.1, p.2 + 1) ∈ gridPathTrace δ (sqB p) := by
      simp only [hsqB_def, gridPathTrace]
      exact Or.inr (Or.inr (Or.inr (Or.inl (left_mem_segment ℝ _ _))))
    have hne1 : gridPoint δ p - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem1))
    have hne2 : gridPoint δ (p.1 + 1, p.2) - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem2))
    have hne3 : gridPoint δ (p.1 + 1, p.2 + 1) - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem3))
    have hne4 : gridPoint δ (p.1, p.2 + 1) - q ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hqoff _ hmem4))
    -- the four increments have imaginary parts in `(0, π)`
    have hb1 : 0 < (inc (p, (p.1 + 1, p.2)) q).im ∧
        (inc (p, (p.1 + 1, p.2)) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne2 hne1) (hratio_im _ _ hne1 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    have hb2 : 0 < (inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) q).im ∧
        (inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne3 hne2) (hratio_im _ _ hne2 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    have hb3 : 0 < (inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) q).im ∧
        (inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne4 hne3) (hratio_im _ _ hne3 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    have hb4 : 0 < (inc ((p.1, p.2 + 1), p) q).im ∧
        (inc ((p.1, p.2 + 1), p) q).im < Real.pi := by
      refine hlog_im_bounds _ (div_ne_zero hne1 hne4) (hratio_im _ _ hne4 ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.sub_re, Complex.sub_im,
        hgre, hgim, hgre, hgim]
      push_cast
      nlinarith
    -- pin the winding by the total imaginary part
    have hli := hlift (sqB p) (hsqB_path p) (by simp [hsqB_def])
      (hsqB_closed p) q hqoff
    have hzip : ((sqB p).zip (sqB p).tail).map (fun e => inc e q) =
        [inc (p, (p.1 + 1, p.2)) q,
         inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) q,
         inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) q,
         inc ((p.1, p.2 + 1), p) q] := by
      simp only [hsqB_def, List.tail_cons, List.zip_cons_cons,
        List.zip_nil_right, List.map_cons, List.map_nil]
    rw [hzip] at hli
    have hW := congrArg Complex.im hli
    simp only [List.sum_cons, List.sum_nil, add_zero, Complex.add_im] at hW
    set W : ℤ := windingNumber (gridLoopCurve δ (sqB p)) q with hW_def
    have hLim : ((2 * (Real.pi : ℂ) * Complex.I) * ((W : ℤ) : ℂ)).im =
        2 * Real.pi * (W : ℝ) := by
      have h : (2 * (Real.pi : ℂ) * Complex.I) * ((W : ℤ) : ℂ) =
          (((2 * Real.pi * (W : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h]
      simp [Complex.mul_im]
    rw [hLim] at hW
    have hWpos : (0 : ℝ) < 2 * Real.pi * (W : ℝ) := by
      rw [hW]
      linarith [hb1.1, hb2.1, hb3.1, hb4.1]
    have hWlt : 2 * Real.pi * (W : ℝ) < 4 * Real.pi := by
      rw [hW]
      linarith [hb1.2, hb2.2, hb3.2, hb4.2]
    have hπ := Real.pi_pos
    have hW1 : (0 : ℝ) < (W : ℝ) := by nlinarith
    have hW2 : (W : ℝ) < 2 := by nlinarith
    have hW1' : (0 : ℤ) < W := by exact_mod_cast hW1
    have hW2' : W < 2 := by exact_mod_cast hW2
    omega
  -- The trace of the square boundary is contained in the closed square.
  have hsqB_trace : ∀ p : ℤ × ℤ,
      gridPathTrace δ (sqB p) ⊆ gridSquare δ p := by
    intro p w hw
    clear * - hsqB_def hseg_h hseg_v hsq_mem hgre hgim hδ hw
    simp only [hsqB_def, gridPathTrace] at hw
    rw [hsq_mem]
    rcases hw with h | h | h | h | h
    · obtain ⟨him, h1, h2⟩ := hseg_h p.1 p.2 w h
      refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> rw [him]
      nlinarith
    · obtain ⟨hre, h1, h2⟩ := hseg_v (p.1 + 1) p.2 w (by
        convert h using 2)
      refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> rw [hre] <;> push_cast <;> nlinarith
    · rw [segment_symm] at h
      obtain ⟨him, h1, h2⟩ := hseg_h p.1 (p.2 + 1) w (by
        convert h using 2)
      refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> rw [him] <;> push_cast <;> nlinarith
    · rw [segment_symm] at h
      obtain ⟨hre, h1, h2⟩ := hseg_v p.1 p.2 w h
      refine ⟨⟨?_, ?_⟩, h1, h2⟩ <;> rw [hre]
      nlinarith
    · have hwp : w = gridPoint δ p := h
      rw [hwp]
      rw [hgre, hgim]  -- rewrites inside the goal via hsq_mem shape
      refine ⟨⟨le_refl _, ?_⟩, le_refl _, ?_⟩ <;> nlinarith
  -- Center coordinates of a square.
  have hcen_re : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).re = δ * p.1 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_re, hgre]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have : ((δ : ℂ) / 2 * (1 + Complex.I)).re = δ / 2 := by
      rw [hh]
      simp [Complex.mul_re]
    rw [this]
  have hcen_im : ∀ p : ℤ × ℤ, (gridSquareCenter δ p).im = δ * p.2 + δ / 2 := by
    intro p
    simp only [gridSquareCenter]
    rw [Complex.add_im, hgim]
    have hh : ((δ : ℂ) / 2) = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
    have : ((δ : ℂ) / 2 * (1 + Complex.I)).im = δ / 2 := by
      rw [hh]
      simp [Complex.mul_im]
    rw [this]
  have hcen_mem : ∀ p : ℤ × ℤ, gridSquareCenter δ p ∈ gridSquare δ p := by
    intro p
    rw [hsq_mem, hcen_re, hcen_im]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  -- Points outside the closed square have winding zero.
  have hsq_out : ∀ p : ℤ × ℤ, ∀ q : ℂ, q ∉ gridSquare δ p →
      windingNumber (gridLoopCurve δ (sqB p)) q = 0 := by
    intro p q hq
    clear * - hsqB_def hsqB_closed hsqB_path hsq_mem hδ hsq_diam
      hcen_mem hcen_re hsqB_trace hq
    have hclosed : gridLoopCurve δ (sqB p) 0 = gridLoopCurve δ (sqB p) 1 :=
      gridLoopCurve_closed (by simp [hsqB_def]) (hsqB_closed p)
    have hrange : Set.range (gridLoopCurve δ (sqB p)) =
        gridPathTrace δ (sqB p) :=
      range_gridLoopCurve hδ (hsqB_path p) (by simp [hsqB_def])
    -- The four open half-planes forming the complement of the square,
    -- grouped as two path-connected corner pairs.
    set U : Set ℂ :=
      ({z : ℂ | z.re < δ * p.1} ∪ {z : ℂ | z.im < δ * p.2}) ∪
      ({z : ℂ | δ * (p.1 + 1) < z.re} ∪ {z : ℂ | δ * (p.2 + 1) < z.im})
      with hU_def
    have hqU : q ∈ U := by
      by_contra hqn
      rw [hU_def] at hqn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hqn
      exact hq ((hsq_mem p q).mpr ⟨⟨hqn.1.1, hqn.2.1⟩, hqn.1.2, hqn.2.2⟩)
    have hdisjU : ∀ z ∈ U, z ∉ gridSquare δ p := by
      intro z hz hzsq
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (hsq_mem p z).mp hzsq
      rw [hU_def] at hz
      simp only [Set.mem_union, Set.mem_setOf_eq] at hz
      rcases hz with (h | h) | h | h <;> linarith
    -- A far reference point in `U`.
    set qf : ℂ := ((δ * p.1 - 3 * δ : ℝ) : ℂ) +
      ((δ * p.2 : ℝ) : ℂ) * Complex.I with hqf_def
    have hqf_re : qf.re = δ * p.1 - 3 * δ := by
      simp [hqf_def]
    have hqfU : qf ∈ U := by
      rw [hU_def]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      left; left
      rw [hqf_re]
      linarith
    -- `U` is path-connected, hence preconnected.
    have hUconn : IsPreconnected U := by
      have hpc1 : IsPathConnected {z : ℂ | z.re < δ * p.1} := by
        refine (convex_halfSpace_lt (.mk Complex.add_re Complex.smul_re)
          _).isPathConnected ⟨((δ * p.1 - 1 : ℝ) : ℂ), ?_⟩
        simp [Set.mem_setOf_eq]
      have hpc2 : IsPathConnected {z : ℂ | δ * (p.1 + 1) < z.re} := by
        refine (convex_halfSpace_gt (.mk Complex.add_re Complex.smul_re)
          _).isPathConnected ⟨((δ * (p.1 + 1) + 1 : ℝ) : ℂ), ?_⟩
        simp [Set.mem_setOf_eq]
      have hpc3 : IsPathConnected {z : ℂ | z.im < δ * p.2} := by
        refine (convex_halfSpace_lt (.mk Complex.add_im Complex.smul_im)
          _).isPathConnected ⟨((δ * p.2 - 1 : ℝ) : ℂ) * Complex.I, ?_⟩
        simp [Set.mem_setOf_eq]
      have hpc4 : IsPathConnected {z : ℂ | δ * (p.2 + 1) < z.im} := by
        refine (convex_halfSpace_gt (.mk Complex.add_im Complex.smul_im)
          _).isPathConnected ⟨((δ * (p.2 + 1) + 1 : ℝ) : ℂ) * Complex.I, ?_⟩
        simp [Set.mem_setOf_eq]
      -- below-left corner joins piece 1 and piece 3
      have h13 : IsPathConnected
          ({z : ℂ | z.re < δ * p.1} ∪ {z : ℂ | z.im < δ * p.2}) := by
        refine hpc1.union hpc3
          ⟨((δ * p.1 - 1 : ℝ) : ℂ) + ((δ * p.2 - 1 : ℝ) : ℂ) * Complex.I,
            ?_, ?_⟩ <;> simp [Set.mem_setOf_eq]
      -- above-right corner joins piece 2 and piece 4
      have h24 : IsPathConnected
          ({z : ℂ | δ * (p.1 + 1) < z.re} ∪
            {z : ℂ | δ * (p.2 + 1) < z.im}) := by
        refine hpc2.union hpc4
          ⟨((δ * (p.1 + 1) + 1 : ℝ) : ℂ) +
            ((δ * (p.2 + 1) + 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩ <;>
          simp [Set.mem_setOf_eq]
      -- below-right corner joins the two pairs (below piece ∋ it, right
      -- piece ∋ it)
      have hU : IsPathConnected U := by
        rw [hU_def]
        refine h13.union h24
          ⟨((δ * (p.1 + 1) + 1 : ℝ) : ℂ) +
            ((δ * p.2 - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
        · right
          simp [Set.mem_setOf_eq]
        · left
          simp [Set.mem_setOf_eq]
      exact hU.isConnected.isPreconnected
    -- Winding at the far point is zero: trace inside a ball missing `qf`.
    have htrace_ball : ∀ t : unitInterval, gridLoopCurve δ (sqB p) t ∈
        Metric.ball (gridSquareCenter δ p) (3 * δ) := by
      intro t
      have hmem : gridLoopCurve δ (sqB p) t ∈ gridPathTrace δ (sqB p) := by
        rw [← hrange]
        exact Set.mem_range_self t
      have hd := hsq_diam p _ _ (hsqB_trace p hmem) (hcen_mem p)
      rw [Metric.mem_ball]
      linarith
    have hqf_far : qf ∉ Metric.ball (gridSquareCenter δ p) (3 * δ) := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm]
      have h1 : |(qf - gridSquareCenter δ p).re| ≤
          ‖qf - gridSquareCenter δ p‖ := Complex.abs_re_le_norm _
      have h2 : (qf - gridSquareCenter δ p).re = -(3 * δ) - δ / 2 := by
        rw [Complex.sub_re, hqf_re, hcen_re]
        ring
      rw [h2] at h1
      have h3 : |(-(3 * δ) - δ / 2)| = 3 * δ + δ / 2 := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [h3] at h1
      linarith
    have hqf_wind : windingNumber (gridLoopCurve δ (sqB p)) qf = 0 :=
      windingNumber_eq_zero_of_ball hclosed htrace_ball hqf_far
    rw [← hqf_wind]
    exact windingNumber_eq_of_preconnected hclosed hUconn
      (fun t hmem => hdisjU _ hmem (hsqB_trace p (by
        rw [← hrange]; exact Set.mem_range_self t))) hqU hqfU
  -- ================================================================
  -- STAGE 5: cancellation — summing the square boundaries over `S`
  -- leaves exactly the `E`-edge increments.
  -- ================================================================
  -- Distinct adjacent grid points.
  have hgp_ne_h : ∀ v : ℤ × ℤ, gridPoint δ v ≠ gridPoint δ (v.1 + 1, v.2) := by
    intro v h
    clear * - hgre hδ h
    have h' := congrArg Complex.re h
    rw [hgre, hgre] at h'
    push_cast at h'
    nlinarith
  have hgp_ne_v : ∀ v : ℤ × ℤ, gridPoint δ v ≠ gridPoint δ (v.1, v.2 + 1) := by
    intro v h
    clear * - hgim hδ h
    have h' := congrArg Complex.im h
    rw [hgim, hgim] at h'
    push_cast at h'
    nlinarith
  -- Reversal identities for the two edge directions at `c₀`.
  have hRrev : ∀ v : ℤ × ℤ,
      inc ((v.1 + 1, v.2), v) c₀ = -inc (v, (v.1 + 1, v.2)) c₀ :=
    fun v => hincrev v (v.1 + 1, v.2) c₀ (hc₀line v) (hgp_ne_h v)
  have hUrev : ∀ v : ℤ × ℤ,
      inc ((v.1, v.2 + 1), v) c₀ = -inc (v, (v.1, v.2 + 1)) c₀ :=
    fun v => hincrev v (v.1, v.2 + 1) c₀ (hc₀line' v) (hgp_ne_v v)
  -- The square-boundary increment sum, reorganized into oriented
  -- rightward/upward edge contributions with signs.
  have hsq_rw : ∀ p : ℤ × ℤ,
      (((sqB p).zip (sqB p).tail).map (fun e => inc e c₀)).sum =
        (inc (p, (p.1 + 1, p.2)) c₀ -
          inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀) +
        (inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀ -
          inc (p, (p.1, p.2 + 1)) c₀) := by
    intro p
    clear * - hsqB_def hincrev hc₀line hc₀line' hgp_ne_h hgp_ne_v
    have hzip : ((sqB p).zip (sqB p).tail).map (fun e => inc e c₀) =
        [inc (p, (p.1 + 1, p.2)) c₀,
         inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀,
         inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) c₀,
         inc ((p.1, p.2 + 1), p) c₀] := by
      simp only [hsqB_def, List.tail_cons, List.zip_cons_cons,
        List.zip_nil_right, List.map_cons, List.map_nil]
    rw [hzip]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    have h3 : inc ((p.1 + 1, p.2 + 1), (p.1, p.2 + 1)) c₀ =
        -inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀ :=
      hincrev (p.1, p.2 + 1) (p.1 + 1, p.2 + 1) c₀
        (hc₀line (p.1, p.2 + 1)) (hgp_ne_h (p.1, p.2 + 1))
    have h4 : inc ((p.1, p.2 + 1), p) c₀ = -inc (p, (p.1, p.2 + 1)) c₀ :=
      hincrev p (p.1, p.2 + 1) c₀ (hc₀line' p) (hgp_ne_v p)
    rw [h3, h4]
    ring
  -- Assemble the left side into four plain sums over `S`.
  have hLHS : (S.sum fun p => ((( sqB p).zip (sqB p).tail).map
      (fun e => inc e c₀)).sum) =
      ((S.sum fun p => inc (p, (p.1 + 1, p.2)) c₀) -
        (S.sum fun p => inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀)) +
      ((S.sum fun p => inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀) -
        (S.sum fun p => inc (p, (p.1, p.2 + 1)) c₀)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => hsq_rw p)
  -- Shifted-image membership characterizations.
  have himgUp : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1, p.2 + 1)) ↔ (v.1, v.2 - 1) ∈ S := by
    intro v
    clear * -
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have hp1 : p.1 = v.1 ∧ p.2 + 1 = v.2 := Prod.mk.injEq .. ▸ Prod.ext_iff.mp heq
      have : p = (v.1, v.2 - 1) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← this]
      exact hp
    · intro h
      exact ⟨(v.1, v.2 - 1), h, Prod.ext_iff.mpr ⟨rfl, by omega⟩⟩
  have himgRt : ∀ v : ℤ × ℤ,
      v ∈ S.image (fun p => (p.1 + 1, p.2)) ↔ (v.1 - 1, v.2) ∈ S := by
    intro v
    clear * -
    rw [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, heq⟩
      have hp1 : p.1 + 1 = v.1 ∧ p.2 = v.2 := Prod.mk.injEq .. ▸ Prod.ext_iff.mp heq
      have : p = (v.1 - 1, v.2) := Prod.ext_iff.mpr ⟨by omega, by omega⟩
      rw [← this]
      exact hp
    · intro h
      exact ⟨(v.1 - 1, v.2), h, Prod.ext_iff.mpr ⟨by omega, rfl⟩⟩
  -- Reindex the shifted sums over the image Finsets.
  have hreidxUp : (S.sum fun p => inc ((p.1, p.2 + 1), (p.1 + 1, p.2 + 1)) c₀) =
      ((S.image fun p => (p.1, p.2 + 1)).sum
        fun v => inc (v, (v.1 + 1, v.2)) c₀) := by
    rw [Finset.sum_image (fun x _ y _ h => by
      have := Prod.ext_iff.mp h
      exact Prod.ext_iff.mpr ⟨this.1, by omega⟩)]
  have hreidxRt : (S.sum fun p => inc ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)) c₀) =
      ((S.image fun p => (p.1 + 1, p.2)).sum
        fun v => inc (v, (v.1, v.2 + 1)) c₀) := by
    rw [Finset.sum_image (fun x _ y _ h => by
      have := Prod.ext_iff.mp h
      exact Prod.ext_iff.mpr ⟨by omega, this.2⟩)]
  -- Difference-of-sums splitting helper.
  have hsplit : ∀ (s t : Finset (ℤ × ℤ)) (g : ℤ × ℤ → ℂ),
      s.sum g - t.sum g = (s.filter (fun v => v ∉ t)).sum g -
        (t.filter (fun v => v ∉ s)).sum g := by
    intro s t g
    clear * -
    have hs := Finset.sum_filter_add_sum_filter_not s (fun v => v ∈ t) g
    have ht := Finset.sum_filter_add_sum_filter_not t (fun v => v ∈ s) g
    have hst : s.filter (fun v => v ∈ t) = t.filter (fun v => v ∈ s) := by
      ext v
      simp only [Finset.mem_filter]
      exact and_comm
    rw [← hs, ← ht, hst]
    ring
  have hcancel :
      (S.sum fun p => ((( sqB p).zip (sqB p).tail).map
          (fun e => inc e c₀)).sum) =
        E.sum (fun e => inc e c₀) := by
    clear * - hEmem hbdry_def himgUp himgRt hreidxUp hreidxRt hsplit hLHS
      hRrev hUrev
    -- Four classes of boundary edges, indexed by lattice vertices.
    set HR : Finset (ℤ × ℤ) :=
      S.filter (fun v => v ∉ S.image (fun p => (p.1, p.2 + 1))) with hHR_def
    set HL : Finset (ℤ × ℤ) :=
      (S.image (fun p => (p.1, p.2 + 1))).filter (fun v => v ∉ S) with hHL_def
    set VU : Finset (ℤ × ℤ) :=
      (S.image (fun p => (p.1 + 1, p.2))).filter (fun v => v ∉ S) with hVU_def
    set VD : Finset (ℤ × ℤ) :=
      S.filter (fun v => v ∉ S.image (fun p => (p.1 + 1, p.2))) with hVD_def
    -- `E` is the disjoint union of the four edge images.
    have hE_eq : E = ((HR.image (fun v => (v, (v.1 + 1, v.2))) ∪
        HL.image (fun v => ((v.1 + 1, v.2), v))) ∪
        VU.image (fun v => (v, (v.1, v.2 + 1)))) ∪
        VD.image (fun v => ((v.1, v.2 + 1), v)) := by
      ext e
      rw [hEmem, hbdry_def]
      simp only [Finset.mem_union, Finset.mem_image, hHR_def, hHL_def,
        hVU_def, hVD_def, Finset.mem_filter, himgUp, himgRt]
      constructor
      · rintro (⟨he2, hs, hn⟩ | ⟨he1, hs, hn⟩ | ⟨he2, hs, hn⟩ | ⟨he1, hs, hn⟩)
        · refine Or.inl (Or.inl (Or.inl ⟨e.1, ⟨hs, ?_⟩, ?_⟩))
          · simpa using hn
          · rw [← he2]
        · refine Or.inl (Or.inl (Or.inr ⟨e.2, ⟨by simpa using hs,
            by simpa using hn⟩, ?_⟩))
          exact Prod.ext_iff.mpr ⟨he1.symm, rfl⟩
        · refine Or.inl (Or.inr ⟨e.1, ⟨by simpa using hs,
            by simpa using hn⟩, ?_⟩)
          rw [← he2]
        · refine Or.inr ⟨e.2, ⟨by simpa using hs, ?_⟩, ?_⟩
          · simpa using hn
          · exact Prod.ext_iff.mpr ⟨he1.symm, rfl⟩
      · rintro (((⟨v, ⟨hvS, hvn⟩, rfl⟩ | ⟨v, ⟨hvS, hvn⟩, rfl⟩) |
          ⟨v, ⟨hvS, hvn⟩, rfl⟩) | ⟨v, ⟨hvS, hvn⟩, rfl⟩)
        · exact Or.inl ⟨rfl, hvS, by simpa using hvn⟩
        · refine Or.inr (Or.inl ⟨rfl, ?_, ?_⟩) <;> simpa
        · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)) <;> simpa
        · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)) <;> simpa
    -- Pairwise disjointness of the four images.
    have hd12 : Disjoint (HR.image (fun v => (v, (v.1 + 1, v.2))))
        (HL.image (fun v => ((v.1 + 1, v.2), v))) := by
      rw [Finset.disjoint_left]
      rintro e he1 he2
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp he1
      obtain ⟨w, -, hw⟩ := Finset.mem_image.mp he2
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hw
      obtain ⟨h11, -⟩ := Prod.ext_iff.mp h1
      obtain ⟨h21, -⟩ := Prod.ext_iff.mp h2
      simp only at h11 h21
      omega
    have hd3 : Disjoint (HR.image (fun v => (v, (v.1 + 1, v.2))) ∪
        HL.image (fun v => ((v.1 + 1, v.2), v)))
        (VU.image (fun v => (v, (v.1, v.2 + 1)))) := by
      rw [Finset.disjoint_left]
      rintro e he1 he2
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp he2
      rw [Finset.mem_union] at he1
      rcases he1 with h | h
      · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
        obtain ⟨h11, h12⟩ := Prod.ext_iff.mp h1
        obtain ⟨h21, h22⟩ := Prod.ext_iff.mp h2
        simp only at h11 h12 h21 h22
        omega
      · obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
        obtain ⟨h11, h12⟩ := Prod.ext_iff.mp h1
        obtain ⟨h21, h22⟩ := Prod.ext_iff.mp h2
        simp only at h11 h12 h21 h22
        omega
    have hd4 : Disjoint ((HR.image (fun v => (v, (v.1 + 1, v.2))) ∪
        HL.image (fun v => ((v.1 + 1, v.2), v))) ∪
        VU.image (fun v => (v, (v.1, v.2 + 1))))
        (VD.image (fun v => ((v.1, v.2 + 1), v))) := by
      rw [Finset.disjoint_left]
      rintro e he1 he2
      obtain ⟨v, -, hv⟩ := Finset.mem_image.mp he2
      rw [Finset.mem_union, Finset.mem_union] at he1
      rcases he1 with (h | h) | h <;>
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp h <;>
        · obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
          obtain ⟨h11, h12⟩ := Prod.ext_iff.mp h1
          obtain ⟨h21, h22⟩ := Prod.ext_iff.mp h2
          simp only at h11 h12 h21 h22
          omega
    -- Sums over the four images.
    have hinj1 : ∀ x ∈ HR, ∀ y ∈ HR,
        (x, (x.1 + 1, x.2)) = (y, (y.1 + 1, y.2)) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).1
    have hinj2 : ∀ x ∈ HL, ∀ y ∈ HL,
        ((x.1 + 1, x.2), x) = ((y.1 + 1, y.2), y) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).2
    have hinj3 : ∀ x ∈ VU, ∀ y ∈ VU,
        (x, (x.1, x.2 + 1)) = (y, (y.1, y.2 + 1)) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).1
    have hinj4 : ∀ x ∈ VD, ∀ y ∈ VD,
        ((x.1, x.2 + 1), x) = ((y.1, y.2 + 1), y) → x = y :=
      fun x _ y _ h => (Prod.ext_iff.mp h).2
    have hs1 : (HR.image (fun v => (v, (v.1 + 1, v.2)))).sum
        (fun e => inc e c₀) = HR.sum (fun v => inc (v, (v.1 + 1, v.2)) c₀) :=
      Finset.sum_image hinj1
    have hs2 : (HL.image (fun v => ((v.1 + 1, v.2), v))).sum
        (fun e => inc e c₀) =
        -(HL.sum (fun v => inc (v, (v.1 + 1, v.2)) c₀)) := by
      rw [Finset.sum_image hinj2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => hRrev v)
    have hs3 : (VU.image (fun v => (v, (v.1, v.2 + 1)))).sum
        (fun e => inc e c₀) = VU.sum (fun v => inc (v, (v.1, v.2 + 1)) c₀) :=
      Finset.sum_image hinj3
    have hs4 : (VD.image (fun v => ((v.1, v.2 + 1), v))).sum
        (fun e => inc e c₀) =
        -(VD.sum (fun v => inc (v, (v.1, v.2 + 1)) c₀)) := by
      rw [Finset.sum_image hinj4, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => hUrev v)
    -- Assemble.
    rw [hLHS, hreidxUp, hreidxRt, hE_eq,
      Finset.sum_union hd4, Finset.sum_union hd3, Finset.sum_union hd12,
      hs1, hs2, hs3, hs4,
      hsplit S (S.image (fun p => (p.1, p.2 + 1)))
        (fun v => inc (v, (v.1 + 1, v.2)) c₀),
      hsplit (S.image (fun p => (p.1 + 1, p.2))) S
        (fun v => inc (v, (v.1, v.2 + 1)) c₀)]
    simp only [← hHR_def, ← hHL_def, ← hVU_def, ← hVD_def]
    ring
  -- The left side equals `2πi` (exactly the `(0,0)` square contributes).
  -- First: `c₀` avoids every square-boundary trace (it is off grid lines).
  have hc₀offsq : ∀ p : ℤ × ℤ, ∀ w ∈ gridPathTrace δ (sqB p), c₀ ≠ w := by
    intro p w hw heq
    clear * - hsqB_def hseg_h hseg_v hcim hcre hhalf_ne hgim hw heq
    simp only [hsqB_def, gridPathTrace] at hw
    rcases hw with h | h | h | h | h
    · obtain ⟨him, -, -⟩ := hseg_h p.1 p.2 w h
      rw [← heq, hcim] at him
      exact hhalf_ne p.2 him
    · obtain ⟨hre, -, -⟩ := hseg_v (p.1 + 1) p.2 w h
      rw [← heq, hcre] at hre
      exact hhalf_ne (p.1 + 1) (by push_cast at hre ⊢; linarith)
    · rw [segment_symm] at h
      obtain ⟨him, -, -⟩ := hseg_h p.1 (p.2 + 1) w h
      rw [← heq, hcim] at him
      exact hhalf_ne (p.2 + 1) (by push_cast at him ⊢; linarith)
    · rw [segment_symm] at h
      obtain ⟨hre, -, -⟩ := hseg_v p.1 p.2 w h
      rw [← heq, hcre] at hre
      exact hhalf_ne p.1 hre
    · have hwp : w = gridPoint δ p := h
      have him : c₀.im = δ * p.2 := by rw [heq, hwp, hgim]
      rw [hcim] at him
      exact hhalf_ne p.2 him
  -- per-square increment sums via the lift identity
  have hsq_sum : ∀ p : ℤ × ℤ,
      (((sqB p).zip (sqB p).tail).map (fun e => inc e c₀)).sum =
        (2 * Real.pi * Complex.I) *
          (windingNumber (gridLoopCurve δ (sqB p)) c₀ : ℤ) := by
    intro p
    clear * - hlift hsqB_path hsqB_closed hsqB_def hc₀offsq
    rw [← hlift (sqB p) (hsqB_path p) (by simp [hsqB_def]) (hsqB_closed p)
      c₀ (hc₀offsq p)]
  have hsum_sq :
      (S.sum fun p => ((( sqB p).zip (sqB p).tail).map
          (fun e => inc e c₀)).sum) = 2 * Real.pi * Complex.I := by
    clear * - hsq_sum hsq_in hsq_out hc₀in hc₀only h00
    rw [Finset.sum_eq_single (0, 0)]
    · rw [hsq_sum (0, 0), hsq_in (0, 0) c₀ hc₀in]
      simp
    · intro p _ hp
      rw [hsq_sum p, hsq_out p c₀ (hc₀only p hp)]
      simp
    · intro h00'
      exact absurd h00 h00'
  -- ================================================================
  -- STAGE 6: cycle extraction and the essential cycle.
  -- ================================================================
  -- The balanced edge set decomposes into edge-disjoint closed grid
  -- cycles exhausting `E` (strong induction on `E.card`).
  -- Edges of `E` join distinct adjacent lattice points.
  have hEadj : ∀ e ∈ E, GridAdj e.1 e.2 := by
    intro e he
    clear * - hEmem hbdry_def he
    rw [hEmem, hbdry_def] at he
    rcases he with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  have hE_ne : ∀ e ∈ E, e.1 ≠ e.2 := by
    intro e he heq
    clear * - hEmem hbdry_def he heq
    rw [hEmem, hbdry_def] at he
    obtain ⟨hq1, hq2⟩ := Prod.ext_iff.mp heq
    rcases he with ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;>
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h <;> omega
  -- Lists whose consecutive pairs are `E`-edges are grid paths.
  have hpathE : ∀ L : List (ℤ × ℤ),
      (∀ e ∈ L.zip L.tail, e ∈ E) → IsGridPath L := by
    clear * - hEadj
    intro L
    induction L with
    | nil => intro _; exact List.isChain_nil
    | cons a M ih =>
      intro hedges
      cases M with
      | nil => exact List.isChain_singleton _
      | cons b M' =>
        refine List.isChain_cons_cons.mpr ⟨?_, ih ?_⟩
        · exact hEadj (a, b) (hedges (a, b) (List.mem_cons_self))
        · intro e he
          refine hedges e (List.mem_cons_of_mem _ ?_)
          exact he
  -- Nodup edge lists sum like their finsets.
  have hsum_nodup : ∀ ℓ : List ((ℤ × ℤ) × (ℤ × ℤ)), ℓ.Nodup →
      (ℓ.map (fun e => inc e c₀)).sum =
        ℓ.toFinset.sum (fun e => inc e c₀) := by
    clear * -
    intro ℓ
    induction ℓ with
    | nil => intro _; simp
    | cons e ℓ ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert (by rw [List.mem_toFinset]; exact hnd.1), ih hnd.2]
  -- Degree bookkeeping under `erase`.
  have hdegInErase : ∀ (R : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (x y : ℤ × ℤ),
      (x, y) ∈ R → ∀ w : ℤ × ℤ,
      (R.filter (fun e => e.2 = w)).card =
        ((R.erase (x, y)).filter (fun e => e.2 = w)).card +
          (if w = y then 1 else 0) := by
    intro R x y hxy w
    clear * - hxy
    rw [Finset.filter_erase]
    by_cases h : w = y
    · subst h
      have hmem : (x, w) ∈ R.filter (fun e => e.2 = w) :=
        Finset.mem_filter.mpr ⟨hxy, rfl⟩
      rw [if_pos rfl, Finset.card_erase_of_mem hmem]
      have hpos : 1 ≤ (R.filter (fun e => e.2 = w)).card :=
        Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · have hnot : (x, y) ∉ R.filter (fun e => e.2 = w) := by
        intro hmem
        rw [Finset.mem_filter] at hmem
        exact h hmem.2.symm
      rw [if_neg h, add_zero, Finset.erase_eq_of_notMem hnot]
  have hdegOutErase : ∀ (R : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (x y : ℤ × ℤ),
      (x, y) ∈ R → ∀ w : ℤ × ℤ,
      (R.filter (fun e => e.1 = w)).card =
        ((R.erase (x, y)).filter (fun e => e.1 = w)).card +
          (if w = x then 1 else 0) := by
    intro R x y hxy w
    clear * - hxy
    rw [Finset.filter_erase]
    by_cases h : w = x
    · subst h
      have hmem : (w, y) ∈ R.filter (fun e => e.1 = w) :=
        Finset.mem_filter.mpr ⟨hxy, rfl⟩
      rw [if_pos rfl, Finset.card_erase_of_mem hmem]
      have hpos : 1 ≤ (R.filter (fun e => e.1 = w)).card :=
        Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · have hnot : (x, y) ∉ R.filter (fun e => e.1 = w) := by
        intro hmem
        rw [Finset.mem_filter] at hmem
        exact h hmem.2.symm
      rw [if_neg h, add_zero, Finset.erase_eq_of_notMem hnot]
  -- Trail extraction: from an imbalance `+1 at v, −1 at v₀`, walk from `v`
  -- back to `v₀` along unused edges.
  have hTRAIL : ∀ n : ℕ, ∀ (R : Finset ((ℤ × ℤ) × (ℤ × ℤ))) (v₀ v : ℤ × ℤ),
      R.card ≤ n → R ⊆ E → v ≠ v₀ →
      (∀ w, (R.filter (fun e => e.2 = w)).card + (if w = v then 1 else 0) =
        (R.filter (fun e => e.1 = w)).card + (if w = v₀ then 1 else 0)) →
      ∃ M : List (ℤ × ℤ),
        (v :: M).getLast? = some v₀ ∧
        ((v :: M).zip M).Nodup ∧
        (∀ e ∈ (v :: M).zip M, e ∈ R) ∧
        (∀ w, ((R \ ((v :: M).zip M).toFinset).filter
            (fun e => e.2 = w)).card =
          ((R \ ((v :: M).zip M).toFinset).filter
            (fun e => e.1 = w)).card) := by
    clear * - hdegInErase hdegOutErase
    intro n
    induction n with
    | zero =>
      intro R v₀ v hcard hRE hne hinv
      exfalso
      have hR : R = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have h := hinv v
      rw [hR, if_pos rfl, if_neg hne] at h
      simp only [Finset.filter_empty, Finset.card_empty] at h
      omega
    | succ n ih =>
      intro R v₀ v hcard hRE hne hinv
      have h := hinv v
      rw [if_pos rfl, if_neg hne] at h
      have hpos : 0 < (R.filter (fun e => e.1 = v)).card := by omega
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at he
      obtain ⟨heR, he1⟩ := he
      obtain ⟨ea, eb⟩ := e
      have hea : v = ea := he1.symm
      subst hea
      have hcard' : (R.erase (v, eb)).card ≤ n := by
        have h1 := Finset.card_erase_of_mem heR
        have h2 : 1 ≤ R.card := Finset.card_pos.mpr ⟨_, heR⟩
        omega
      have hinv' : ∀ w, ((R.erase (v, eb)).filter
          (fun e => e.2 = w)).card + (if w = eb then 1 else 0) =
          ((R.erase (v, eb)).filter (fun e => e.1 = w)).card +
            (if w = v₀ then 1 else 0) := by
        intro w
        have h0 := hinv w
        rw [hdegInErase R v eb heR w, hdegOutErase R v eb heR w] at h0
        split_ifs at h0 ⊢ <;> omega
      by_cases heb : eb = v₀
      · have heb' : v₀ = eb := heb.symm
        subst heb'
        refine ⟨[v₀], by simp, by simp, ?_, ?_⟩
        · intro e he
          have hz : (v :: [v₀]).zip [v₀] = [(v, v₀)] := rfl
          rw [hz, List.mem_singleton] at he
          rw [he]
          exact heR
        · intro w
          have hz : ((v :: [v₀]).zip [v₀]).toFinset = {(v, v₀)} := by
            rfl
          rw [hz, Finset.sdiff_singleton_eq_erase]
          have h0 := hinv' w
          split_ifs at h0 <;> omega
      · have hR'E : R.erase (v, eb) ⊆ E :=
          (Finset.erase_subset _ _).trans hRE
        obtain ⟨M', hlast', hnodup', hmem', hbal'⟩ :=
          ih (R.erase (v, eb)) v₀ eb hcard' hR'E heb hinv'
        have hz : (v :: eb :: M').zip (eb :: M') =
            (v, eb) :: ((eb :: M').zip M') := rfl
        refine ⟨eb :: M', ?_, ?_, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]
          exact hlast'
        · rw [hz, List.nodup_cons]
          refine ⟨?_, hnodup'⟩
          intro hmem
          exact Finset.notMem_erase _ _ (hmem' _ hmem)
        · intro e he
          rw [hz] at he
          rcases List.mem_cons.mp he with rfl | he'
          · exact heR
          · exact Finset.mem_of_mem_erase (hmem' _ he')
        · intro w
          have hset : R \ ((v :: eb :: M').zip (eb :: M')).toFinset =
              (R.erase (v, eb)) \ ((eb :: M').zip M').toFinset := by
            rw [hz, List.toFinset_cons]
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert,
              Finset.mem_erase, List.mem_toFinset]
            constructor
            · rintro ⟨hxR, hxn⟩
              push Not at hxn
              exact ⟨⟨hxn.1, hxR⟩, hxn.2⟩
            · rintro ⟨⟨hx1, hxR⟩, hx2⟩
              refine ⟨hxR, ?_⟩
              push Not
              exact ⟨hx1, hx2⟩
          rw [hset]
          exact hbal' w
  -- Full decomposition by strong induction on the number of edges.
  have hMAIN : ∀ n : ℕ, ∀ F : Finset ((ℤ × ℤ) × (ℤ × ℤ)),
      F.card ≤ n → F ⊆ E →
      (∀ w, (F.filter (fun e => e.2 = w)).card =
        (F.filter (fun e => e.1 = w)).card) →
      ∃ cycles : List (List (ℤ × ℤ)),
        (∀ C ∈ cycles, IsGridPath C ∧ C ≠ [] ∧ C.head? = C.getLast? ∧
          ∀ e ∈ C.zip C.tail, e ∈ E) ∧
        ((cycles.map fun C =>
          ((C.zip C.tail).map (fun e => inc e c₀)).sum).sum
          = F.sum (fun e => inc e c₀)) := by
    clear * - hTRAIL hE_ne hpathE hsum_nodup hdegInErase hdegOutErase
    intro n
    induction n with
    | zero =>
      intro F hcard _ _
      have hF : F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hF
      exact ⟨[], by simp, by simp⟩
    | succ n ih =>
      intro F hcard hFE hbalF
      rcases Finset.eq_empty_or_nonempty F with rfl | ⟨e₀, he₀⟩
      · exact ⟨[], by simp, by simp⟩
      obtain ⟨a, b⟩ := e₀
      have hba : b ≠ a := fun h => hE_ne (a, b) (hFE he₀) h.symm
      have hcard' : (F.erase (a, b)).card ≤ n := by
        have h1 := Finset.card_erase_of_mem he₀
        have h2 : 1 ≤ F.card := Finset.card_pos.mpr ⟨_, he₀⟩
        omega
      have hinv : ∀ w, ((F.erase (a, b)).filter
          (fun e => e.2 = w)).card + (if w = b then 1 else 0) =
          ((F.erase (a, b)).filter (fun e => e.1 = w)).card +
            (if w = a then 1 else 0) := by
        intro w
        have h0 := hbalF w
        rw [hdegInErase F a b he₀ w, hdegOutErase F a b he₀ w] at h0
        split_ifs at h0 ⊢ <;> omega
      obtain ⟨M, hM_last, hM_nodup, hM_mem, hM_bal⟩ :=
        hTRAIL n (F.erase (a, b)) a b hcard'
          ((Finset.erase_subset _ _).trans hFE) hba hinv
      have hz : (a :: b :: M).zip (b :: M) = (a, b) :: ((b :: M).zip M) := rfl
      have hW_sub : ((b :: M).zip M).toFinset ⊆ F.erase (a, b) :=
        fun x hx => hM_mem x (List.mem_toFinset.mp hx)
      have hF'card : ((F.erase (a, b)) \ ((b :: M).zip M).toFinset).card ≤ n :=
        le_trans (Finset.card_le_card Finset.sdiff_subset) hcard'
      have hF'E : (F.erase (a, b)) \ ((b :: M).zip M).toFinset ⊆ E :=
        Finset.sdiff_subset.trans ((Finset.erase_subset _ _).trans hFE)
      obtain ⟨cycles', hc'prop, hc'sum⟩ :=
        ih ((F.erase (a, b)) \ ((b :: M).zip M).toFinset) hF'card hF'E hM_bal
      refine ⟨(a :: b :: M) :: cycles', ?_, ?_⟩
      · intro C hC
        rcases List.mem_cons.mp hC with rfl | hC'
        · have hedges : ∀ e ∈ (a :: b :: M).zip (b :: M), e ∈ E := by
            intro e he
            rw [hz] at he
            rcases List.mem_cons.mp he with rfl | he'
            · exact hFE he₀
            · exact ((Finset.erase_subset _ _).trans hFE) (hM_mem e he')
          refine ⟨hpathE _ hedges, by simp, ?_, hedges⟩
          rw [List.head?_cons, List.getLast?_cons_cons, hM_last]
        · exact hc'prop C hC'
      · rw [List.map_cons, List.sum_cons, hc'sum]
        simp only [List.tail_cons]
        have h3 : (((a :: b :: M).zip (b :: M)).map
            (fun e => inc e c₀)).sum = inc (a, b) c₀ +
              (((b :: M).zip M).toFinset).sum (fun e => inc e c₀) := by
          rw [hz, List.map_cons, List.sum_cons, hsum_nodup _ hM_nodup]
        have h1 : (F.erase (a, b)).sum (fun e => inc e c₀) + inc (a, b) c₀ =
            F.sum (fun e => inc e c₀) :=
          Finset.sum_erase_add F _ he₀
        have h2 : ((F.erase (a, b)) \ ((b :: M).zip M).toFinset).sum
            (fun e => inc e c₀) +
            (((b :: M).zip M).toFinset).sum (fun e => inc e c₀) =
            (F.erase (a, b)).sum (fun e => inc e c₀) :=
          Finset.sum_sdiff hW_sub
        rw [h3]
        linear_combination h1 + h2
  have hcycles : ∃ cycles : List (List (ℤ × ℤ)),
      (∀ C ∈ cycles, IsGridPath C ∧ C ≠ [] ∧ C.head? = C.getLast? ∧
        ∀ e ∈ C.zip C.tail, e ∈ E) ∧
      ((cycles.map fun C => ((C.zip C.tail).map (fun e => inc e c₀)).sum).sum
        = E.sum (fun e => inc e c₀)) :=
    hMAIN E.card E le_rfl (fun _ h => h) hbal
  obtain ⟨cycles, hcycles_ok, hcycles_sum⟩ := hcycles
  clear * - hcancel hsum_sq hcycles_ok hcycles_sum hET hδ hA'T' hc₀A' hlift
  -- Some cycle has nonzero increment sum, hence nonzero winding.
  have hexists : ∃ C ∈ cycles, ((C.zip C.tail).map (fun e => inc e c₀)).sum ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : (cycles.map fun C =>
        ((C.zip C.tail).map (fun e => inc e c₀)).sum).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx
      exact hall C hC
    rw [hzero, ← hcancel, hsum_sq] at hcycles_sum
    have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    exact hπ hcycles_sum.symm
  obtain ⟨C, hC_mem, hC_ne⟩ := hexists
  obtain ⟨hC_path, hC_nonempty, hC_closed, hC_edges⟩ := hcycles_ok C hC_mem
  -- The essential cycle has at least one edge.
  obtain ⟨a, b, M, rfl⟩ : ∃ a b M, C = a :: b :: M := by
    match C, hC_nonempty with
    | [_], _ => exact absurd (by simp) hC_ne
    | a :: b :: M, _ => exact ⟨a, b, M, rfl⟩
  -- Its trace lies in `T'` (all edges are boundary edges).
  have htraceT : ∀ (a b : ℤ × ℤ) (M : List (ℤ × ℤ)),
      (∀ e ∈ (a :: b :: M).zip (b :: M), e ∈ E) →
      gridPathTrace δ (a :: b :: M) ⊆ T' := by
    intro a b M
    induction M generalizing a b with
    | nil =>
      intro hedge w hw
      have habE : (a, b) ∈ E := hedge (a, b) (by simp)
      rcases hw with hseg | hpt
      · exact hET (a, b) habE hseg
      · have hbw : w = gridPoint δ b := hpt
        exact hET (a, b) habE
          (hbw ▸ right_mem_segment ℝ (gridPoint δ a) (gridPoint δ b))
    | cons c M ih =>
      intro hedge w hw
      have habE : (a, b) ∈ E := hedge (a, b) (by simp)
      rcases hw with hseg | htr
      · exact hET (a, b) habE hseg
      · refine ih b c (fun e he => hedge e ?_) htr
        simp only [List.zip_cons_cons, List.mem_cons] at he ⊢
        tauto
  have hCtrace : gridPathTrace δ (a :: b :: M) ⊆ T' := htraceT a b M hC_edges
  -- `c₀` avoids the trace (it lies in the complement of `T'`).
  have hc₀off : ∀ w ∈ gridPathTrace δ (a :: b :: M), c₀ ≠ w := by
    intro w hw heq
    exact hA'T' hc₀A' (heq ▸ hCtrace hw)
  refine ⟨gridLoopCurve δ (a :: b :: M), ?_, ?_, ?_⟩
  · exact gridLoopCurve_closed (by simp) hC_closed
  · intro t
    have hrange : Set.range (gridLoopCurve δ (a :: b :: M)) =
        gridPathTrace δ (a :: b :: M) :=
      range_gridLoopCurve hδ hC_path (by simp)
    exact hCtrace (hrange ▸ Set.mem_range_self t)
  · intro hzero
    have hli := hlift (a :: b :: M) hC_path (by simp) hC_closed c₀ hc₀off
    rw [hzero] at hli
    simp only [Int.cast_zero, mul_zero] at hli
    exact hC_ne hli.symm

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
