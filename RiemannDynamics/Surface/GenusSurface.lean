/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import RiemannDynamics.Analysis.Winding.Basic

/-!
# The reference genus-`g` surface: the `4g`-gon model

The closed orientable surface of genus `g ≥ 1`, built as a quotient of the
closed unit disc `D̄ ⊆ ℂ`. The unit circle plays the role of the boundary of
a `4g`-gon: the `4g` vertices are `polyVertex g m = exp (π m i / (2g))` and
the sides are the circular arcs between consecutive vertices. Reading the
boundary counterclockwise, block `j` carries the word
`a_{j+1} b_{j+1} a_{j+1}⁻¹ b_{j+1}⁻¹` on arcs `4j, …, 4j+3`, so the source
arcs are those with `k % 4 ∈ {0, 1}` and arc `k` is glued to arc `k + 2` by
the side pairing `sidePairing g k z = exp (π (2k+3) i / (2g)) / z`, an
anti-orientation gluing on the circle which extends to a holomorphic
involution of `ℂ ∖ {0}` swapping disc and exterior.

The quotient `GenusSurface g` is a compact, connected, Hausdorff space with
an explicit atlas of `2g + 2` complex charts (interior, one per source arc,
and one at the single vertex class), all of whose transitions are analytic
with nonvanishing derivative, so `GenusSurface g` is an analytic
one-dimensional complex manifold.

Charts are built inverse-first: each chart is assembled from an explicit
continuous injective open map `ψ : ℂ → GenusSurface g` on an open plane set
via `OpenPartialHomeomorph.ofInvFunOn`.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval
open scoped Manifold

namespace RiemannDynamics

/-! ## The closed disc and the polygon data -/

/-- The closed unit disc in `ℂ`, the model polygon of the `4g`-gon
construction. -/
noncomputable def ClosedDisc : Type := ↥(Metric.closedBall (0 : ℂ) 1)

noncomputable instance : TopologicalSpace ClosedDisc :=
  instTopologicalSpaceSubtype

instance : CompactSpace ClosedDisc :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)

instance : T2Space ClosedDisc :=
  inferInstanceAs (T2Space ↥(Metric.closedBall (0 : ℂ) 1))

instance : PathConnectedSpace ClosedDisc :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩)

instance : Nonempty ClosedDisc := ⟨⟨0, by simp⟩⟩

/-- Vertex `m` of the `4g`-gon: `exp (π m i / (2g))` on the unit circle.
Periodic in `m` with period `4g`. -/
noncomputable def polyVertex (g : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (Real.pi * m * Complex.I / (2 * g))

/-- The point of arc `k` at parameter `t ∈ [0, 1]`:
`exp (π (k + t) i / (2g))`, running from `polyVertex g k` to
`polyVertex g (k + 1)`. -/
noncomputable def arcPoint (g : ℕ) (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (Real.pi * (k + t) * Complex.I / (2 * g))

/-- The side pairing of arc `k`: `z ↦ exp (π (2k+3) i / (2g)) / z`, a
holomorphic involution of `ℂ ∖ {0}` mapping arc `k` onto arc `k + 2` with
reversed orientation and swapping the open disc with the exterior. -/
noncomputable def sidePairing (g : ℕ) (k : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (Real.pi * (2 * k + 3) * Complex.I / (2 * g)) / z

/-- The side pairing maps the parameter-`t` point of arc `k` to the
parameter-`(1 - t)` point of arc `k + 2`. -/
theorem sidePairing_arcPoint (g : ℕ) [NeZero g] (k : ℤ) (t : ℝ) :
    sidePairing g k (arcPoint g k t) = arcPoint g (k + 2) (1 - t) := by
  unfold sidePairing arcPoint
  rw [← Complex.exp_sub, div_sub_div_same]
  congr 2
  push_cast
  ring

/-- The side pairing is an involution away from the origin. -/
theorem sidePairing_involutive (g : ℕ) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    sidePairing g k (sidePairing g k z) = z := by
  unfold sidePairing
  have hω : Complex.exp (Real.pi * (2 * k + 3) * Complex.I / (2 * g)) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

/-- The side pairing preserves the unit circle. -/
theorem norm_sidePairing (g : ℕ) (k : ℤ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖sidePairing g k z‖ = 1 := by
  unfold sidePairing
  have h : (Real.pi * (2 * k + 3) * Complex.I / (2 * g) : ℂ)
      = ((Real.pi * (2 * k + 3) / (2 * g) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [norm_div, h, Complex.norm_exp_ofReal_mul_I, hz, div_one]

/-- The vertices are `4g`-periodic in the index. -/
theorem polyVertex_periodic (g : ℕ) (m : ℤ) :
    polyVertex g (m + 4 * g) = polyVertex g m := by
  unfold polyVertex
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    norm_num
  · have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
    have h : (Real.pi * (↑(m + 4 * g) : ℂ) * Complex.I / (2 * g) : ℂ)
        = Real.pi * m * Complex.I / (2 * g) + 2 * Real.pi * Complex.I := by
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The arc points are `4g`-periodic in the arc index. -/
theorem arcPoint_periodic (g : ℕ) (k : ℤ) (t : ℝ) :
    arcPoint g (k + 4 * g) t = arcPoint g k t := by
  unfold arcPoint
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    norm_num
  · have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
    have h : (Real.pi * ((↑(k + 4 * g) : ℂ) + t) * Complex.I / (2 * g) : ℂ)
        = Real.pi * (k + t) * Complex.I / (2 * g) + 2 * Real.pi * Complex.I := by
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The side pairings are `4g`-periodic in the arc index. -/
theorem sidePairing_periodic (g : ℕ) (k : ℤ) (z : ℂ) :
    sidePairing g (k + 4 * g) z = sidePairing g k z := by
  unfold sidePairing
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    norm_num
  · have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
    have h : (Real.pi * (2 * (↑(k + 4 * g) : ℂ) + 3) * Complex.I / (2 * g) : ℂ)
        = Real.pi * (2 * k + 3) * Complex.I / (2 * g)
          + (2 : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Arc `k` starts at vertex `k`. -/
theorem arcPoint_zero (g : ℕ) (k : ℤ) :
    arcPoint g k 0 = polyVertex g k := by
  unfold arcPoint polyVertex
  norm_num

/-- Arc `k` ends at vertex `k + 1`. -/
theorem arcPoint_one (g : ℕ) (k : ℤ) :
    arcPoint g k 1 = polyVertex g (k + 1) := by
  unfold arcPoint polyVertex
  congr 2
  push_cast
  ring

/-- A point of the plane is a vertex of the `4g`-gon. -/
def IsPolyVertex (g : ℕ) (z : ℂ) : Prop :=
  ∃ m : ℤ, z = polyVertex g m

/-- The graph of the gluing of arc `k` onto arc `k + 2`: the pairs
`(arcPoint g k t, arcPoint g (k+2) (1-t))` for `t ∈ [0, 1]`. -/
noncomputable def pairGraph (g : ℕ) (k : ℤ) : Set (ℂ × ℂ) :=
  (fun t : unitInterval => (arcPoint g k t, arcPoint g (k + 2) (1 - t))) '' Set.univ

/-! ## Arc separation -/

/-- The parametrization of a single arc is injective on `[0, 1]`. -/
theorem arcPoint_inj (g : ℕ) [NeZero g] (k : ℤ) {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1)
    (h : arcPoint g k t = arcPoint g k t') : t = t' := by
  have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  unfold arcPoint at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have key : (t : ℂ) - t' = 4 * g * n := by
    field_simp at hn
    linear_combination hn
  have keyR : t - t' = 4 * g * n := by exact_mod_cast key
  have hg1 : (1 : ℝ) ≤ g := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with h0 | h0 | h0
    · exfalso
      have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      have hmul : 4 * (g : ℝ) * n ≤ 4 * (g : ℝ) * (-1) := by
        apply mul_le_mul_of_nonneg_left h1
        linarith
      linarith [ht.1, ht.2, ht'.1, ht'.2]
    · exact h0
    · exfalso
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
      have hmul : 4 * (g : ℝ) * 1 ≤ 4 * (g : ℝ) * n := by
        apply mul_le_mul_of_nonneg_left h1
        linarith
      linarith [ht.1, ht.2, ht'.1, ht'.2]
  rw [hn0] at keyR
  push_cast at keyR
  linarith

/-- Two arc points coincide exactly when their angle parameters differ by a
multiple of the full turn `4g`. -/
theorem arcPoint_eq_iff (g : ℕ) [NeZero g] (k k' : ℤ) (t t' : ℝ) :
    arcPoint g k t = arcPoint g k' t' ↔
      ∃ n : ℤ, (k + t) - (k' + t') = (4 * g : ℤ) * n := by
  have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  unfold arcPoint
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have key : ((k : ℂ) + t) - ((k' : ℂ) + t') = 4 * g * n := by
      field_simp at hn
      linear_combination hn
    exact_mod_cast key
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : ((k : ℂ) + t) - ((k' : ℂ) + t') = 4 * g * n := by exact_mod_cast hn
    field_simp
    linear_combination hn'

/-- Distinct arcs (indices distinct mod `4g`) meet only in vertices. -/
theorem arc_inter_arc (g : ℕ) [NeZero g] {k k' : ℤ} {t t' : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1)
    (hkk' : ¬ (k : ZMod (4 * g)) = (k' : ZMod (4 * g)))
    (h : arcPoint g k t = arcPoint g k' t') : IsPolyVertex g (arcPoint g k t) := by
  obtain ⟨n, hn⟩ := (arcPoint_eq_iff g k k' t t').mp h
  push_cast at hn
  have hjR : t - t' = ((4 * g * n - k + k' : ℤ) : ℝ) := by
    push_cast
    linarith
  have hj_lb : (-1 : ℤ) ≤ 4 * g * n - k + k' := by
    have hR : (-1 : ℝ) ≤ ((4 * g * n - k + k' : ℤ) : ℝ) := by
      rw [← hjR]
      linarith [ht.1, ht.2, ht'.1, ht'.2]
    exact_mod_cast hR
  have hj_ub : 4 * (g : ℤ) * n - k + k' ≤ 1 := by
    have hR : ((4 * g * n - k + k' : ℤ) : ℝ) ≤ 1 := by
      rw [← hjR]
      linarith [ht.1, ht.2, ht'.1, ht'.2]
    exact_mod_cast hR
  have htri : 4 * (g : ℤ) * n - k + k' = -1 ∨ 4 * (g : ℤ) * n - k + k' = 0 ∨
      4 * (g : ℤ) * n - k + k' = 1 := by omega
  rcases htri with hc | hc | hc
  · have h0 : t = 0 := by
      rw [hc] at hjR
      push_cast at hjR
      linarith [ht.1, ht'.2]
    rw [h0]
    exact ⟨k, arcPoint_zero g k⟩
  · exfalso
    apply hkk'
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    push_cast
    linear_combination hc
  · have h1 : t = 1 := by
      rw [hc] at hjR
      push_cast at hjR
      linarith [ht.2, ht'.1]
    rw [h1]
    exact ⟨k + 1, arcPoint_one g k⟩

/-! ## The gluing relation and the quotient -/

/-- The gluing relation on the closed disc: two points are related when they
are equal, matched by a source-arc side pairing (`k % 4 ∈ {0, 1}`), or both
vertices. All `4g` vertices form a single class. -/
noncomputable def genusRel (g : ℕ) (z w : ClosedDisc) : Prop :=
  z = w
  ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
      ((z.1, w.1) ∈ pairGraph g k ∨ (w.1, z.1) ∈ pairGraph g k))
  ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1)

/-- A pair in a pairing graph consisting of vertices arises only at the arc
endpoints. -/
theorem pairGraph_vertex_iff (g : ℕ) [NeZero g] (k : ℤ) {z w : ℂ}
    (h : (z, w) ∈ pairGraph g k) :
    IsPolyVertex g z ↔ IsPolyVertex g w := by
  have hvchar : ∀ (a : ℤ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      (IsPolyVertex g (arcPoint g a t) ↔ t = 0 ∨ t = 1) := by
    intro a t ht
    constructor
    · rintro ⟨m, hm⟩
      rw [← arcPoint_zero g m] at hm
      obtain ⟨n, hn⟩ := (arcPoint_eq_iff g a m t 0).mp hm
      push_cast at hn
      have hjt : t = ((m - a + 4 * g * n : ℤ) : ℝ) := by
        push_cast
        linarith
      have h0 : (0 : ℤ) ≤ m - a + 4 * g * n := by
        have hR : (0 : ℝ) ≤ ((m - a + 4 * g * n : ℤ) : ℝ) := by
          rw [← hjt]
          exact ht.1
        exact_mod_cast hR
      have h1 : (m - a + 4 * g * n : ℤ) ≤ 1 := by
        have hR : ((m - a + 4 * g * n : ℤ) : ℝ) ≤ 1 := by
          rw [← hjt]
          exact ht.2
        exact_mod_cast hR
      have hcase : m - a + 4 * g * n = 0 ∨ m - a + 4 * g * n = 1 := by omega
      rcases hcase with hc | hc
      · left
        rw [hjt, hc]
        norm_num
      · right
        rw [hjt, hc]
        norm_num
    · rintro (rfl | rfl)
      · exact ⟨a, arcPoint_zero g a⟩
      · exact ⟨a + 1, arcPoint_one g a⟩
  obtain ⟨t, -, ht⟩ := h
  have hz : arcPoint g k (t : ℝ) = z := congrArg Prod.fst ht
  have hw : arcPoint g (k + 2) (1 - (t : ℝ)) = w := congrArg Prod.snd ht
  have ht2 : (1 - (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
  rw [← hz, ← hw, hvchar k _ t.2, hvchar (k + 2) _ ht2]
  constructor
  · rintro (h0 | h1)
    · right
      rw [h0]
      norm_num
    · left
      rw [h1]
      norm_num
  · rintro (h0 | h1)
    · right
      linarith
    · left
      linarith

/-- A non-vertex point lies in at most one pairing pair: the partner in the
gluing relation is uniquely determined. -/
theorem mem_pairGraph_unique (g : ℕ) [NeZero g] {z w w' : ℂ}
    (hz : ¬ IsPolyVertex g z)
    {k k' : ℤ} (hk : k % 4 = 0 ∨ k % 4 = 1) (hk' : k' % 4 = 0 ∨ k' % 4 = 1)
    (h : (z, w) ∈ pairGraph g k ∨ (w, z) ∈ pairGraph g k)
    (h' : (z, w') ∈ pairGraph g k' ∨ (w', z) ∈ pairGraph g k') : w = w' := by
  have harc_ne : ∀ (a : ℤ) (u : ℝ), arcPoint g a u ≠ 0 := by
    intro a u
    unfold arcPoint
    exact Complex.exp_ne_zero _
  have hside : ∀ (a : ℤ) (zz ww : ℂ),
      ((zz, ww) ∈ pairGraph g a ∨ (ww, zz) ∈ pairGraph g a) →
      ∃ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 ∧
        (zz = arcPoint g a u ∨ zz = arcPoint g (a + 2) u) ∧ ww = sidePairing g a zz := by
    intro a zz ww hmem
    rcases hmem with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
    · have h1 : arcPoint g a (t : ℝ) = zz := congrArg Prod.fst ht
      have h2 : arcPoint g (a + 2) (1 - (t : ℝ)) = ww := congrArg Prod.snd ht
      refine ⟨(t : ℝ), t.2, Or.inl h1.symm, ?_⟩
      rw [← h2, ← h1, sidePairing_arcPoint]
    · have h1 : arcPoint g a (t : ℝ) = ww := congrArg Prod.fst ht
      have h2 : arcPoint g (a + 2) (1 - (t : ℝ)) = zz := congrArg Prod.snd ht
      refine ⟨1 - (t : ℝ), ⟨by linarith [t.2.2], by linarith [t.2.1]⟩, Or.inr h2.symm, ?_⟩
      rw [← h1, ← h2, ← sidePairing_arcPoint g a (t : ℝ),
        sidePairing_involutive g a (harc_ne a (t : ℝ))]
  have hmod4 : ∀ a b : ℤ, ((a : ZMod (4 * g)) = (b : ZMod (4 * g))) → a % 4 = b % 4 := by
    intro a b hab
    have h1 : a ≡ b [ZMOD ((4 * g : ℕ) : ℤ)] := (ZMod.intCast_eq_intCast_iff a b (4 * g)).mp hab
    have h2 : (4 : ℤ) ∣ ((4 * g : ℕ) : ℤ) := by
      push_cast
      exact ⟨(g : ℤ), rfl⟩
    exact h1.of_dvd h2
  obtain ⟨u, hu, hzarc, hwz⟩ := hside k z w h
  obtain ⟨u', hu', hzarc', hwz'⟩ := hside k' z w' h'
  have hcong : (k : ZMod (4 * g)) = (k' : ZMod (4 * g)) := by
    rcases hzarc with h1 | h1 <;> rcases hzarc' with h2 | h2
    · by_contra hne
      apply hz
      rw [h1]
      exact arc_inter_arc g hu hu' hne (h1.symm.trans h2)
    · exfalso
      have hcc : (k : ZMod (4 * g)) = ((k' + 2 : ℤ) : ZMod (4 * g)) := by
        by_contra hne
        apply hz
        rw [h1]
        exact arc_inter_arc g hu hu' hne (h1.symm.trans h2)
      have h4 := hmod4 _ _ hcc
      omega
    · exfalso
      have hcc : ((k + 2 : ℤ) : ZMod (4 * g)) = (k' : ZMod (4 * g)) := by
        by_contra hne
        apply hz
        rw [h1]
        exact arc_inter_arc g hu hu' hne (h1.symm.trans h2)
      have h4 := hmod4 _ _ hcc
      omega
    · have hcc : ((k + 2 : ℤ) : ZMod (4 * g)) = ((k' + 2 : ℤ) : ZMod (4 * g)) := by
        by_contra hne
        apply hz
        rw [h1]
        exact arc_inter_arc g hu hu' hne (h1.symm.trans h2)
      have hcc' : (k : ZMod (4 * g)) + 2 = (k' : ZMod (4 * g)) + 2 := by
        push_cast at hcc
        exact hcc
      exact add_right_cancel hcc'
  have hnum : Complex.exp (Real.pi * (2 * k + 3) * Complex.I / (2 * g))
      = Complex.exp (Real.pi * (2 * k' + 3) * Complex.I / (2 * g)) := by
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at hcong
    obtain ⟨n, hn⟩ := hcong
    have hnC : (k' : ℂ) - k = 4 * g * n := by exact_mod_cast hn
    have hg' : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-2 * n, ?_⟩
    push_cast
    field_simp
    linear_combination (-2 : ℂ) * hnC
  rw [hwz, hwz']
  unfold sidePairing
  rw [hnum]

/-- The gluing relation is an equivalence: classes are singletons in the
interior, pairs `{z, sidePairing g k z}` on open edges, and the single
vertex class. -/
theorem genusRel_equivalence (g : ℕ) [NeZero g] : Equivalence (genusRel g) := by
  constructor
  · intro x
    exact Or.inl rfl
  · intro x y hxy
    have hxy' : x = y ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
        ((x.1, y.1) ∈ pairGraph g k ∨ (y.1, x.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g x.1 ∧ IsPolyVertex g y.1) := hxy
    rcases hxy' with hh | ⟨k, hk, hp⟩ | ⟨h1, h2⟩
    · exact Or.inl hh.symm
    · exact Or.inr (Or.inl ⟨k, hk, hp.symm⟩)
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
  · intro x y v hxy hyv
    have hxy' : x = y ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
        ((x.1, y.1) ∈ pairGraph g k ∨ (y.1, x.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g x.1 ∧ IsPolyVertex g y.1) := hxy
    have hyv' : y = v ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
        ((y.1, v.1) ∈ pairGraph g k ∨ (v.1, y.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g y.1 ∧ IsPolyVertex g v.1) := hyv
    rcases hxy' with rfl | ⟨k, hk, hp⟩ | ⟨h1, h2⟩
    · exact hyv
    · rcases hyv' with rfl | ⟨k', hk', hp'⟩ | ⟨h1', h2'⟩
      · exact Or.inr (Or.inl ⟨k, hk, hp⟩)
      · by_cases hVy : IsPolyVertex g y.1
        · have hVx : IsPolyVertex g x.1 := by
            rcases hp with hp1 | hp1
            · exact (pairGraph_vertex_iff g k hp1).mpr hVy
            · exact (pairGraph_vertex_iff g k hp1).mp hVy
          have hVv : IsPolyVertex g v.1 := by
            rcases hp' with hp2 | hp2
            · exact (pairGraph_vertex_iff g k' hp2).mp hVy
            · exact (pairGraph_vertex_iff g k' hp2).mpr hVy
          exact Or.inr (Or.inr ⟨hVx, hVv⟩)
        · have hxv : x.1 = v.1 := mem_pairGraph_unique g hVy hk hk' hp.symm hp'
          exact Or.inl (Subtype.ext hxv)
      · have hVx : IsPolyVertex g x.1 := by
          rcases hp with hp1 | hp1
          · exact (pairGraph_vertex_iff g k hp1).mpr h1'
          · exact (pairGraph_vertex_iff g k hp1).mp h1'
        exact Or.inr (Or.inr ⟨hVx, h2'⟩)
    · rcases hyv' with rfl | ⟨k', hk', hp'⟩ | ⟨h1', h2'⟩
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · have hVv : IsPolyVertex g v.1 := by
          rcases hp' with hp2 | hp2
          · exact (pairGraph_vertex_iff g k' hp2).mp h2
          · exact (pairGraph_vertex_iff g k' hp2).mpr h2
        exact Or.inr (Or.inr ⟨h1, hVv⟩)
      · exact Or.inr (Or.inr ⟨h1, h2'⟩)

/-- The gluing relation as a setoid on the closed disc. -/
noncomputable def genusSetoid (g : ℕ) [NeZero g] : Setoid ClosedDisc :=
  ⟨genusRel g, genusRel_equivalence g⟩

/-- The closed orientable surface of genus `g`: the quotient of the closed
unit disc by the `4g`-gon side pairings. -/
noncomputable def GenusSurface (g : ℕ) [NeZero g] : Type :=
  Quotient (genusSetoid g)

noncomputable instance (g : ℕ) [NeZero g] : TopologicalSpace (GenusSurface g) :=
  instTopologicalSpaceQuotient

instance (g : ℕ) [NeZero g] : CompactSpace (GenusSurface g) :=
  Quotient.compactSpace

instance (g : ℕ) [NeZero g] : PathConnectedSpace (GenusSurface g) :=
  (Quotient.mk_surjective (s := genusSetoid g)).pathConnectedSpace
    continuous_quotient_mk'

instance (g : ℕ) [NeZero g] : ConnectedSpace (GenusSurface g) :=
  inferInstance

instance (g : ℕ) [NeZero g] : Nonempty (GenusSurface g) :=
  inferInstance

/-- The graph of the gluing relation is closed in `ClosedDisc × ClosedDisc`:
the diagonal, finitely many compact pairing graphs (indices reduced mod
`4g`), and the finite vertex square. -/
theorem isClosed_genusRel (g : ℕ) [NeZero g] :
    IsClosed {p : ClosedDisc × ClosedDisc | genusRel g p.1 p.2} := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hg1' : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg1
  have hgZ : (0 : ℤ) < 4 * (g : ℤ) := by linarith
  have harc : ∀ k k' : ℤ, (4 * (g : ℤ)) ∣ (k - k') →
      ∀ t : ℝ, arcPoint g k t = arcPoint g k' t := by
    intro k k' hdvd t
    obtain ⟨n, hn⟩ := hdvd
    rw [arcPoint_eq_iff]
    refine ⟨n, ?_⟩
    have hnR : (k : ℝ) - k' = 4 * g * n := by exact_mod_cast hn
    push_cast
    linarith
  have hvertP : ∀ m : ℤ, polyVertex g m = polyVertex g (m % (4 * (g : ℤ))) := by
    intro m
    rw [← arcPoint_zero g m, ← arcPoint_zero g (m % (4 * (g : ℤ)))]
    refine harc m (m % (4 * (g : ℤ))) ⟨m / (4 * (g : ℤ)), ?_⟩ 0
    have hdm := Int.emod_add_mul_ediv m (4 * (g : ℤ))
    linarith
  have hVfin : Set.Finite {zc : ℂ | IsPolyVertex g zc} := by
    have hsub : {zc : ℂ | IsPolyVertex g zc}
        = (fun m : ℤ => polyVertex g m) '' (Set.Icc (0 : ℤ) (4 * (g : ℤ) - 1)) := by
      ext zc
      constructor
      · rintro ⟨m, rfl⟩
        refine ⟨m % (4 * (g : ℤ)), ⟨Int.emod_nonneg m hgZ.ne', ?_⟩, (hvertP m).symm⟩
        have hlt := Int.emod_lt_of_pos m hgZ
        linarith
      · rintro ⟨m, -, rfl⟩
        exact ⟨m, rfl⟩
    rw [hsub]
    exact (Set.finite_Icc _ _).image _
  have hVclosed : IsClosed {zc : ℂ | IsPolyVertex g zc} := hVfin.isClosed
  have harc_cont : ∀ a : ℤ, Continuous fun s : ℝ => arcPoint g a s := by
    intro a
    unfold arcPoint
    exact Complex.continuous_exp.comp (by fun_prop)
  have hpg_cpt : ∀ a : ℤ, IsCompact (pairGraph g a) := by
    intro a
    unfold pairGraph
    rw [Set.image_univ]
    exact isCompact_range (((harc_cont a).comp continuous_subtype_val).prodMk
      ((harc_cont (a + 2)).comp (continuous_const.sub continuous_subtype_val)))
  have hcoord1 : Continuous fun p : ClosedDisc × ClosedDisc => p.1.1 :=
    continuous_subtype_val.comp continuous_fst
  have hcoord2 : Continuous fun p : ClosedDisc × ClosedDisc => p.2.1 :=
    continuous_subtype_val.comp continuous_snd
  have hTclosed : ∀ a : ℤ, IsClosed {p : ClosedDisc × ClosedDisc |
      (a % 4 = 0 ∨ a % 4 = 1) ∧
        ((p.1.1, p.2.1) ∈ pairGraph g a ∨ (p.2.1, p.1.1) ∈ pairGraph g a)} := by
    intro a
    by_cases ha : a % 4 = 0 ∨ a % 4 = 1
    · have hEq : {p : ClosedDisc × ClosedDisc |
          (a % 4 = 0 ∨ a % 4 = 1) ∧
            ((p.1.1, p.2.1) ∈ pairGraph g a ∨ (p.2.1, p.1.1) ∈ pairGraph g a)}
          = {p : ClosedDisc × ClosedDisc | (p.1.1, p.2.1) ∈ pairGraph g a}
            ∪ {p : ClosedDisc × ClosedDisc | (p.2.1, p.1.1) ∈ pairGraph g a} := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_union, ha, true_and]
      rw [hEq]
      have hc1 : IsClosed {p : ClosedDisc × ClosedDisc | (p.1.1, p.2.1) ∈ pairGraph g a} :=
        (hpg_cpt a).isClosed.preimage (hcoord1.prodMk hcoord2)
      have hc2 : IsClosed {p : ClosedDisc × ClosedDisc | (p.2.1, p.1.1) ∈ pairGraph g a} :=
        (hpg_cpt a).isClosed.preimage (hcoord2.prodMk hcoord1)
      exact hc1.union hc2
    · have hEq : {p : ClosedDisc × ClosedDisc |
          (a % 4 = 0 ∨ a % 4 = 1) ∧
            ((p.1.1, p.2.1) ∈ pairGraph g a ∨ (p.2.1, p.1.1) ∈ pairGraph g a)} = ∅ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hcontra, -⟩
        exact ha hcontra
      rw [hEq]
      exact isClosed_empty
  have hmain : {p : ClosedDisc × ClosedDisc | genusRel g p.1 p.2}
      = {p : ClosedDisc × ClosedDisc | p.1 = p.2}
        ∪ ((⋃ a ∈ Set.Icc (0 : ℤ) (4 * (g : ℤ) - 1),
            {p : ClosedDisc × ClosedDisc | (a % 4 = 0 ∨ a % 4 = 1) ∧
              ((p.1.1, p.2.1) ∈ pairGraph g a ∨ (p.2.1, p.1.1) ∈ pairGraph g a)})
          ∪ {p : ClosedDisc × ClosedDisc |
              IsPolyVertex g p.1.1 ∧ IsPolyVertex g p.2.1}) := by
    ext p
    constructor
    · intro hp
      have hp' : p.1 = p.2 ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
          ((p.1.1, p.2.1) ∈ pairGraph g k ∨ (p.2.1, p.1.1) ∈ pairGraph g k))
          ∨ (IsPolyVertex g p.1.1 ∧ IsPolyVertex g p.2.1) := hp
      rcases hp' with hh | ⟨k, hk, hmem⟩ | hh
      · exact Or.inl hh
      · refine Or.inr (Or.inl ?_)
        have hpg_congr : pairGraph g k = pairGraph g (k % (4 * (g : ℤ))) := by
          have hdvd : (4 * (g : ℤ)) ∣ (k - k % (4 * (g : ℤ))) := by
            refine ⟨k / (4 * (g : ℤ)), ?_⟩
            have hdm := Int.emod_add_mul_ediv k (4 * (g : ℤ))
            linarith
          have h1 : ∀ t : ℝ, arcPoint g k t = arcPoint g (k % (4 * (g : ℤ))) t :=
            harc _ _ hdvd
          have h2 : ∀ t : ℝ, arcPoint g (k + 2) t = arcPoint g (k % (4 * (g : ℤ)) + 2) t := by
            refine harc _ _ ?_
            obtain ⟨n, hn⟩ := hdvd
            exact ⟨n, by linarith⟩
          unfold pairGraph
          congr 1
          funext t
          rw [h1, h2]
        have hkmod : k % (4 * (g : ℤ)) % 4 = k % 4 :=
          Int.emod_emod_of_dvd k ⟨(g : ℤ), rfl⟩
        have hidx : k % (4 * (g : ℤ)) ∈ Set.Icc (0 : ℤ) (4 * (g : ℤ) - 1) := by
          refine ⟨Int.emod_nonneg k hgZ.ne', ?_⟩
          have hlt := Int.emod_lt_of_pos k hgZ
          linarith
        have hmemT : p ∈ {p : ClosedDisc × ClosedDisc |
            (k % (4 * (g : ℤ)) % 4 = 0 ∨ k % (4 * (g : ℤ)) % 4 = 1) ∧
              ((p.1.1, p.2.1) ∈ pairGraph g (k % (4 * (g : ℤ)))
                ∨ (p.2.1, p.1.1) ∈ pairGraph g (k % (4 * (g : ℤ))))} := by
          refine ⟨by rw [hkmod]; exact hk, ?_⟩
          rw [← hpg_congr]
          exact hmem
        exact Set.mem_biUnion hidx hmemT
      · exact Or.inr (Or.inr hh)
    · intro hp
      rcases hp with hh | hh | hh
      · exact Or.inl hh
      · obtain ⟨a, -, haT⟩ := Set.mem_iUnion₂.mp hh
        exact Or.inr (Or.inl ⟨a, haT.1, haT.2⟩)
      · exact Or.inr (Or.inr hh)
  rw [hmain]
  refine IsClosed.union ?_ (IsClosed.union ?_ ?_)
  · exact isClosed_eq continuous_fst continuous_snd
  · exact (Set.finite_Icc _ _).isClosed_biUnion fun a _ => hTclosed a
  · exact (hVclosed.preimage hcoord1).inter (hVclosed.preimage hcoord2)

/-- A quotient of a compact Hausdorff space by a setoid with closed graph is
Hausdorff: the quotient map is closed (saturations of closed sets are
projections of closed subsets of a compact square), so distinct fibers can
be separated by saturated open sets via normality. -/
theorem t2Space_quotient_of_isClosed_setoidGraph {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (s : Setoid X)
    (h : IsClosed {p : X × X | s.r p.1 p.2}) : T2Space (Quotient s) := by
  have hqm : IsQuotientMap (Quotient.mk s) := isQuotientMap_quot_mk
  have hsat : ∀ C : Set X, Quotient.mk s ⁻¹' (Quotient.mk s '' C)
      = Prod.fst '' ({p : X × X | s.r p.1 p.2} ∩ Set.univ ×ˢ C) := by
    intro C
    ext x
    constructor
    · rintro ⟨c, hc, hcx⟩
      exact ⟨(x, c), ⟨Quotient.exact hcx.symm, Set.mem_univ x, hc⟩, rfl⟩
    · rintro ⟨⟨x1, c⟩, ⟨hq, -, hqC⟩, rfl⟩
      exact ⟨c, hqC, (Quotient.sound hq).symm⟩
  have hclosedmap : ∀ C : Set X, IsClosed C → IsClosed (Quotient.mk s '' C) := by
    intro C hC
    rw [← hqm.isClosed_preimage, hsat C]
    exact ((h.inter (isClosed_univ.prod hC)).isCompact.image continuous_fst).isClosed
  constructor
  intro q₁ q₂ hne
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q₂
  have hA : IsClosed {x : X | s.r x a} := by
    have hcont : Continuous fun x : X => (x, a) := continuous_id.prodMk continuous_const
    exact h.preimage hcont
  have hB : IsClosed {x : X | s.r x b} := by
    have hcont : Continuous fun x : X => (x, b) := continuous_id.prodMk continuous_const
    exact h.preimage hcont
  have hdisj : Disjoint {x : X | s.r x a} {x : X | s.r x b} := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hne (Quotient.sound (s.iseqv.trans (s.iseqv.symm hxa) hxb))
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA.isCompact hB.isCompact hdisj
  refine ⟨(Quotient.mk s '' Uᶜ)ᶜ, (Quotient.mk s '' Vᶜ)ᶜ,
    isOpen_compl_iff.mpr (hclosedmap _ hUo.isClosed_compl),
    isOpen_compl_iff.mpr (hclosedmap _ hVo.isClosed_compl), ?_, ?_, ?_⟩
  · rintro ⟨x, hxU, hxa⟩
    exact hxU (hAU (Quotient.exact hxa))
  · rintro ⟨x, hxV, hxb⟩
    exact hxV (hBV (Quotient.exact hxb))
  · rw [Set.disjoint_left]
    intro q hqU hqV
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    have hxU : x ∈ U := by
      by_contra hxU
      exact hqU ⟨x, hxU, rfl⟩
    have hxV : x ∈ V := by
      by_contra hxV
      exact hqV ⟨x, hxV, rfl⟩
    exact Set.disjoint_left.mp hUV hxU hxV

instance (g : ℕ) [NeZero g] : T2Space (GenusSurface g) :=
  t2Space_quotient_of_isClosed_setoidGraph (genusSetoid g) (isClosed_genusRel g)

/-! ## Charts, inverse-first -/

/-- The forward map `Function.invFunOn ψ V` of an inverse-first chart is
continuous on `ψ '' V` when `ψ` is continuous, injective, and open on the
open set `V`: openness of `ψ` on subsets of `V` is exactly continuity of the
inverse on the image. -/
theorem continuousOn_invFunOn_of_isOpen_image {S : Type*} [TopologicalSpace S]
    (ψ : ℂ → S) (V : Set ℂ) (hV : IsOpen V) (hc : ContinuousOn ψ V)
    (hi : Set.InjOn ψ V) (ho : ∀ W ⊆ V, IsOpen W → IsOpen (ψ '' W)) :
    ContinuousOn (Function.invFunOn ψ V) (ψ '' V) := by
  -- `hc` is not needed: openness of the images alone is continuity of the inverse.
  have := hc
  rw [_root_.continuousOn_iff']
  intro t ht
  refine ⟨ψ '' (t ∩ V), ho (t ∩ V) inter_subset_right (ht.inter hV), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hyt, x, hxV, rfl⟩
    have hmem : Function.invFunOn ψ V (ψ x) ∈ V := Function.invFunOn_mem ⟨x, hxV, rfl⟩
    have heq : ψ (Function.invFunOn ψ V (ψ x)) = ψ x := Function.invFunOn_eq ⟨x, hxV, rfl⟩
    exact ⟨⟨Function.invFunOn ψ V (ψ x), ⟨hyt, hmem⟩, heq⟩, x, hxV, rfl⟩
  · rintro ⟨⟨x, ⟨hxt, hxV⟩, rfl⟩, hyV⟩
    have hmem : Function.invFunOn ψ V (ψ x) ∈ V := Function.invFunOn_mem ⟨x, hxV, rfl⟩
    have heq : ψ (Function.invFunOn ψ V (ψ x)) = ψ x := Function.invFunOn_eq ⟨x, hxV, rfl⟩
    have hx : Function.invFunOn ψ V (ψ x) = x := hi hmem hxV heq
    refine ⟨?_, x, hxV, rfl⟩
    rw [hx]
    exact hxt

/-- Inverse-first assembly of a chart: a continuous injective open map
`ψ : ℂ → S` on an open set `V` is a homeomorphism onto its image, packaged
as a partial homeomorphism `S → ℂ` with source `ψ '' V`, target `V`,
inverse `ψ`, and forward map `Function.invFunOn ψ V`. -/
noncomputable def OpenPartialHomeomorph.ofInvFunOn {S : Type*} [TopologicalSpace S]
    (ψ : ℂ → S) (V : Set ℂ) (hV : IsOpen V) (hc : ContinuousOn ψ V)
    (hi : Set.InjOn ψ V) (ho : ∀ W ⊆ V, IsOpen W → IsOpen (ψ '' W)) :
    OpenPartialHomeomorph S ℂ where
  toFun := Function.invFunOn ψ V
  invFun := ψ
  source := ψ '' V
  target := V
  map_source' _ hx := Function.invFunOn_mem hx
  map_target' _ hy := Set.mem_image_of_mem ψ hy
  left_inv' _ hx := Function.invFunOn_eq hx
  right_inv' _ hy := hi.leftInvOn_invFunOn hy
  open_source := ho V (subset_refl V) hV
  open_target := hV
  continuousOn_toFun := continuousOn_invFunOn_of_isOpen_image ψ V hV hc hi ho
  continuousOn_invFun := hc

/-- The continuous clamp of the plane onto the closed disc: the identity on
the disc, radial projection outside. -/
noncomputable def projDisc (u : ℂ) : ClosedDisc :=
  ⟨u / (max 1 ‖u‖ : ℝ), by
    have hpos : (0 : ℝ) < max 1 ‖u‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
    exact (div_le_one hpos).mpr (le_max_right _ _)⟩

/-- The clamp is the identity on the closed disc. -/
theorem projDisc_eq {u : ℂ} (h : ‖u‖ ≤ 1) : (projDisc u).1 = u := by
  have hval : (projDisc u).1 = u / ((max 1 ‖u‖ : ℝ) : ℂ) := rfl
  rw [hval, max_eq_left h, Complex.ofReal_one, div_one]

/-- The clamp is continuous. -/
theorem continuous_projDisc : Continuous projDisc := by
  have h : Continuous fun u : ℂ => u / ((max 1 ‖u‖ : ℝ) : ℂ) := by
    refine continuous_id.div
      (Complex.continuous_ofReal.comp (continuous_const.max continuous_norm)) ?_
    intro x
    have hpos : (0 : ℝ) < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  exact h.subtype_mk _

/-! ### The interior chart -/

/-- Continuity of the interior chart inverse `u ↦ ⟦projDisc u⟧` on the open
unit disc. -/
theorem interiorChart_continuousOn (g : ℕ) [NeZero g] :
    ContinuousOn (fun u => Quotient.mk (genusSetoid g) (projDisc u))
      (Metric.ball (0 : ℂ) 1) := by
  have hq : Continuous (Quotient.mk (genusSetoid g)) := continuous_quot_mk
  exact (hq.comp continuous_projDisc).continuousOn

/-- Injectivity of the interior chart inverse on the open unit disc:
interior classes are singletons. -/
theorem interiorChart_injOn (g : ℕ) [NeZero g] :
    Set.InjOn (fun u => Quotient.mk (genusSetoid g) (projDisc u))
      (Metric.ball (0 : ℂ) 1) := by
  have harc : ∀ (k : ℤ) (t : ℝ), ‖arcPoint g k t‖ = 1 := by
    intro k t
    have hrw : arcPoint g k t
        = Complex.exp (((Real.pi * ((k : ℝ) + t) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold arcPoint
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    have hrw : polyVertex g m
        = Complex.exp (((Real.pi * (m : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k ∨ (w.1, z.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvert] at hz
      exact absurd hz (lt_irrefl 1)
  intro u hu u' hu' h
  have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
  have hu1' : ‖u'‖ < 1 := mem_ball_zero_iff.mp hu'
  have hrel : genusRel g (projDisc u) (projDisc u') := Quotient.exact h
  have hzu : ‖(projDisc u).1‖ < 1 := by
    rw [projDisc_eq hu1.le]
    exact hu1
  have hval := congrArg Subtype.val (hsingle _ _ hzu hrel)
  rwa [projDisc_eq hu1.le, projDisc_eq hu1'.le] at hval

/-- Openness of the interior chart inverse: interior subsets of the disc are
saturated, so their images are open in the quotient. -/
theorem interiorChart_isOpen_image (g : ℕ) [NeZero g] :
    ∀ W ⊆ Metric.ball (0 : ℂ) 1, IsOpen W →
      IsOpen ((fun u => Quotient.mk (genusSetoid g) (projDisc u)) '' W) := by
  have harc : ∀ (k : ℤ) (t : ℝ), ‖arcPoint g k t‖ = 1 := by
    intro k t
    have hrw : arcPoint g k t
        = Complex.exp (((Real.pi * ((k : ℝ) + t) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold arcPoint
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    have hrw : polyVertex g m
        = Complex.exp (((Real.pi * (m : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k ∨ (w.1, z.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvert] at hz
      exact absurd hz (lt_irrefl 1)
  intro W hWV hW
  have key : (fun u => Quotient.mk (genusSetoid g) (projDisc u)) '' W
      = Quotient.mk (genusSetoid g) '' {z : ClosedDisc | z.1 ∈ W} := by
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨projDisc u, ?_, rfl⟩
      change (projDisc u).1 ∈ W
      rw [projDisc_eq (mem_ball_zero_iff.mp (hWV hu)).le]
      exact hu
    · rintro ⟨z, hz, rfl⟩
      have hz1 : z.1 ∈ W := hz
      refine ⟨z.1, hz1, ?_⟩
      exact congrArg _ (Subtype.ext (projDisc_eq (mem_closedBall_zero_iff.mp z.2)))
  rw [key]
  have hcont : Continuous fun z : ClosedDisc => z.1 := continuous_subtype_val
  have hAopen : IsOpen {z : ClosedDisc | z.1 ∈ W} := hW.preimage hcont
  have hsat : Quotient.mk (genusSetoid g) ⁻¹'
      (Quotient.mk (genusSetoid g) '' {z : ClosedDisc | z.1 ∈ W})
      = {z : ClosedDisc | z.1 ∈ W} := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro p ⟨z, hz, hzp⟩
    have hz1 : ‖z.1‖ < 1 := mem_ball_zero_iff.mp (hWV hz)
    have hzp' : z = p := hsingle z p hz1 (Quotient.exact hzp)
    exact hzp' ▸ hz
  have hpre : IsOpen (Quotient.mk (genusSetoid g) ⁻¹'
      (Quotient.mk (genusSetoid g) '' {z : ClosedDisc | z.1 ∈ W})) := by
    rw [hsat]
    exact hAopen
  exact isOpen_coinduced.mpr hpre

/-- The interior chart of the genus surface, with target the open unit disc
and source the classes of interior points. -/
noncomputable def interiorChart (g : ℕ) [NeZero g] :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  OpenPartialHomeomorph.ofInvFunOn (fun u => Quotient.mk (genusSetoid g) (projDisc u))
    (Metric.ball 0 1) isOpen_ball (interiorChart_continuousOn g)
    (interiorChart_injOn g) (interiorChart_isOpen_image g)

/-- The source of the interior chart is the set of classes of interior
points of the disc. -/
theorem interiorChart_source (g : ℕ) [NeZero g] :
    (interiorChart g).source =
      Quotient.mk (genusSetoid g) '' {z : ClosedDisc | ‖z.1‖ < 1} := by
  have hsrc : (interiorChart g).source
      = (fun u => Quotient.mk (genusSetoid g) (projDisc u)) '' Metric.ball 0 1 := rfl
  rw [hsrc]
  ext p
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu1 : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
    refine ⟨projDisc u, ?_, rfl⟩
    change ‖(projDisc u).1‖ < 1
    rw [projDisc_eq hu1.le]
    exact hu1
  · rintro ⟨z, hz, rfl⟩
    have hz1 : ‖z.1‖ < 1 := hz
    refine ⟨z.1, mem_ball_zero_iff.mpr hz1, ?_⟩
    exact congrArg _ (Subtype.ext (projDisc_eq hz1.le))

/-- The inverse of the interior chart is the clamped quotient map. -/
theorem interiorChart_symm_apply (g : ℕ) [NeZero g] (u : ℂ) :
    (interiorChart g).symm u = Quotient.mk (genusSetoid g) (projDisc u) := by
  rfl

/-! ### The edge charts -/

/-- The open annular sector over the open arc `k`: radii in `(1/2, 2)` and
angle parameter `θ' ∈ (k, k + 1)` in units of `π/(2g)`. -/
noncomputable def edgeSector (g : ℕ) (k : ℤ) : Set ℂ :=
  {u : ℂ | ∃ ρ θ' : ℝ, (1 / 2 : ℝ) < ρ ∧ ρ < 2 ∧ (k : ℝ) < θ' ∧ θ' < k + 1 ∧
    u = ρ * Complex.exp (Real.pi * θ' * Complex.I / (2 * g))}

/-- The annular sector over an open arc is open. -/
theorem isOpen_edgeSector (g : ℕ) [NeZero g] (k : ℤ) : IsOpen (edgeSector g k) := by
  sorry

/-- The edge chart inverse over the source arc `k`: the clamped quotient map
on the disc side, the side pairing followed by it on the exterior side. -/
noncomputable def edgeChartFun (g : ℕ) [NeZero g] (k : ℤ) (u : ℂ) : GenusSurface g :=
  if ‖u‖ ≤ 1 then Quotient.mk (genusSetoid g) (projDisc u)
  else Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u))

/-- Continuity of the edge chart inverse: the two closed pieces
`{‖u‖ ≤ 1}`, `{‖u‖ ≥ 1}` agree on the circle by the pairing clause. -/
theorem edgeChart_continuousOn (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    ContinuousOn (edgeChartFun g k) (edgeSector g k) := by
  sorry

/-- Injectivity of the edge chart inverse on its sector: the disc part has
angle parameter in `(k, k+1)`, the reflected exterior part in `(k+2, k+3)`,
and no vertices occur. -/
theorem edgeChart_injOn (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    Set.InjOn (edgeChartFun g k) (edgeSector g k) := by
  sorry

/-- Openness of the edge chart inverse: the saturation of the image of an
open subset adds the pairing mirror of its boundary trace, which is open in
the disc by the two-sided half-ball argument. -/
theorem edgeChart_isOpen_image (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    ∀ W ⊆ edgeSector g k, IsOpen W → IsOpen (edgeChartFun g k '' W) := by
  sorry

/-- The source-arc index of the edge chart labelled by `j : Fin g` and
`b : Bool` is `≡ 0` or `1 (mod 4)`. -/
theorem edgeIndex_mod (g : ℕ) (j : Fin g) (b : Bool) :
    (4 * (j : ℤ) + if b then 1 else 0) % 4 = 0 ∨
      (4 * (j : ℤ) + if b then 1 else 0) % 4 = 1 := by
  cases b
  · rw [if_neg Bool.false_ne_true]
    omega
  · rw [if_pos rfl]
    omega

/-- The edge chart over the source arc `4j` (for `b = false`, carrying
`a_{j+1}`) or `4j + 1` (for `b = true`, carrying `b_{j+1}`). Its source is a
neighborhood of the glued open edge, its target the open annular sector. -/
noncomputable def edgeChart (g : ℕ) [NeZero g] (j : Fin g) (b : Bool) :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  OpenPartialHomeomorph.ofInvFunOn (edgeChartFun g (4 * j + if b then 1 else 0))
    (edgeSector g (4 * j + if b then 1 else 0))
    (isOpen_edgeSector g _)
    (edgeChart_continuousOn g _ (edgeIndex_mod g j b))
    (edgeChart_injOn g _ (edgeIndex_mod g j b))
    (edgeChart_isOpen_image g _ (edgeIndex_mod g j b))

/-- The inverse of an edge chart is the two-piece gluing map. -/
theorem edgeChart_symm_apply (g : ℕ) [NeZero g] (j : Fin g) (b : Bool) (u : ℂ) :
    (edgeChart g j b).symm u = edgeChartFun g (4 * j + if b then 1 else 0) u := by
  sorry

/-! ### The vertex chart -/

/-- The arc involution `π̂` on indices mod `4g`: source arcs (`n % 4 ∈
{0, 1}`) go to `n + 2`, target arcs to `n - 2`. -/
def pairInv (g : ℕ) (n : ZMod (4 * g)) : ZMod (4 * g) :=
  if n.val % 4 = 0 ∨ n.val % 4 = 1 then n + 2 else n - 2

/-- The corner-slot map of the vertex chart: sector `m` of the chart disc is
laid down at the corner `vertexSlot g m`. Closed form: `c 0 = 0`, and for
`m ≥ 1` with `m - 1 = 4i + s`, `c m = 4(g - 1 - i) + [1, 2, 3, 0]ₛ`. -/
def vertexSlot (g : ℕ) (m : ZMod (4 * g)) : ZMod (4 * g) :=
  if m = 0 then 0
  else
    ((4 * (g - 1 - (m.val - 1) / 4) +
      (if (m.val - 1) % 4 = 3 then 0 else (m.val - 1) % 4 + 1) : ℕ) : ZMod (4 * g))

/-- The slot map fixes `0`. -/
theorem vertexSlot_zero (g : ℕ) : vertexSlot g 0 = 0 := by
  unfold vertexSlot
  rw [if_pos rfl]

/-- The slot recurrence: the successor slot is the arc involution of the
predecessor arc, `c (m+1) = π̂ (c m - 1)`. -/
theorem vertexSlot_succ (g : ℕ) [NeZero g] (m : ZMod (4 * g)) :
    vertexSlot g (m + 1) = pairInv g (vertexSlot g m - 1) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  have hval : ∀ a : ℕ, a < 4 * g → ((a : ZMod (4 * g))).val = a := fun a ha =>
    ZMod.val_cast_of_lt ha
  have hslot : ∀ v : ℕ, 1 ≤ v → v < 4 * g →
      vertexSlot g ((v : ℕ) : ZMod (4 * g)) =
        ((4 * (g - 1 - (v - 1) / 4) +
          (if (v - 1) % 4 = 3 then 0 else (v - 1) % 4 + 1) : ℕ) : ZMod (4 * g)) := by
    intro v hv1 hvlt
    have hne : ((v : ℕ) : ZMod (4 * g)) ≠ 0 := by
      intro hcontra
      have hv := hval v hvlt
      rw [hcontra, ZMod.val_zero] at hv
      omega
    unfold vertexSlot
    rw [if_neg hne, hval v hvlt]
  have hpair : ∀ b : ℕ, b < 4 * g →
      pairInv g ((b : ℕ) : ZMod (4 * g)) =
        if b % 4 = 0 ∨ b % 4 = 1 then ((b + 2 : ℕ) : ZMod (4 * g))
        else ((b - 2 : ℕ) : ZMod (4 * g)) := by
    intro b hb
    unfold pairInv
    rw [hval b hb]
    split_ifs with hcond
    · push_cast
      ring
    · have hb2 : 2 ≤ b := by omega
      rw [Nat.cast_sub hb2]
      push_cast
      ring
  have hsub1 : ∀ a : ℕ, 1 ≤ a →
      ((a : ℕ) : ZMod (4 * g)) - 1 = ((a - 1 : ℕ) : ZMod (4 * g)) := by
    intro a ha
    rw [Nat.cast_sub ha, Nat.cast_one]
  by_cases hm0 : m = 0
  · subst hm0
    rw [zero_add, vertexSlot_zero]
    have hneg : (0 : ZMod (4 * g)) - 1 = ((4 * g - 1 : ℕ) : ZMod (4 * g)) := by
      rw [← ZMod.natCast_self (4 * g)]
      exact hsub1 (4 * g) (by omega)
    rw [hneg, hpair (4 * g - 1) (by omega), if_neg (by omega)]
    rw [show (1 : ZMod (4 * g)) = ((1 : ℕ) : ZMod (4 * g)) from Nat.cast_one.symm]
    rw [hslot 1 le_rfl (by omega), if_neg (by omega : ¬(1 - 1) % 4 = 3)]
    congr 1
    omega
  · obtain ⟨v, hvlt, hv1, hmc⟩ :
        ∃ v : ℕ, v < 4 * g ∧ 1 ≤ v ∧ ((v : ℕ) : ZMod (4 * g)) = m :=
      ⟨m.val, ZMod.val_lt m,
        Nat.one_le_iff_ne_zero.mpr (fun hc => hm0 ((ZMod.val_eq_zero m).mp hc)),
        ZMod.natCast_rightInverse m⟩
    rw [← hmc, hslot v hv1 hvlt]
    rcases Nat.lt_or_ge (v + 1) (4 * g) with hlt | hge
    · have hm1 : ((v : ℕ) : ZMod (4 * g)) + 1 = ((v + 1 : ℕ) : ZMod (4 * g)) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hm1, hslot (v + 1) (by omega) hlt]
      simp only [Nat.add_sub_cancel]
      have hs4 : (v - 1) % 4 = 0 ∨ (v - 1) % 4 = 1 ∨ (v - 1) % 4 = 2 ∨
          (v - 1) % 4 = 3 := by omega
      rcases hs4 with hs | hs | hs | hs
      · rw [if_neg (by omega : ¬v % 4 = 3), if_neg (by omega : ¬(v - 1) % 4 = 3)]
        rw [hsub1 _ (by omega), hpair _ (by omega), if_pos (by omega)]
        congr 1
        omega
      · rw [if_neg (by omega : ¬v % 4 = 3), if_neg (by omega : ¬(v - 1) % 4 = 3)]
        rw [hsub1 _ (by omega), hpair _ (by omega), if_pos (by omega)]
        congr 1
        omega
      · rw [if_pos (by omega : v % 4 = 3), if_neg (by omega : ¬(v - 1) % 4 = 3)]
        rw [hsub1 _ (by omega), hpair _ (by omega), if_neg (by omega)]
        congr 1
        omega
      · rw [if_neg (by omega : ¬v % 4 = 3), if_pos hs]
        rw [hsub1 _ (by omega), hpair _ (by omega), if_neg (by omega)]
        congr 1
        omega
    · have hveq : v = 4 * g - 1 := by omega
      have hm1 : ((v : ℕ) : ZMod (4 * g)) + 1 = 0 := by
        have h2 : ((v : ℕ) : ZMod (4 * g)) + 1 = ((v + 1 : ℕ) : ZMod (4 * g)) := by
          rw [Nat.cast_add, Nat.cast_one]
        rw [h2, show v + 1 = 4 * g from by omega, ZMod.natCast_self]
      rw [hm1, vertexSlot_zero]
      have hS : 4 * (g - 1 - (v - 1) / 4) +
          (if (v - 1) % 4 = 3 then 0 else (v - 1) % 4 + 1) = 3 := by
        rw [if_neg (by omega)]
        omega
      rw [hS, hsub1 3 (by omega), hpair (3 - 1) (by omega), if_neg (by omega)]
      have h32 : (3 - 1 - 2 : ℕ) = 0 := by omega
      rw [h32, Nat.cast_zero]

/-- The slot map is a bijection of `ZMod (4g)` (a single `4g`-cycle). -/
theorem vertexSlot_bijective (g : ℕ) [NeZero g] :
    Function.Bijective (vertexSlot g) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  rw [← Finite.injective_iff_bijective]
  intro a b hab
  have hval : ∀ c : ℕ, c < 4 * g → ((c : ZMod (4 * g))).val = c := fun c hc =>
    ZMod.val_cast_of_lt hc
  have hslotval : ∀ x : ZMod (4 * g), x ≠ 0 →
      (vertexSlot g x).val =
        4 * (g - 1 - (x.val - 1) / 4) +
          (if (x.val - 1) % 4 = 3 then 0 else (x.val - 1) % 4 + 1) := by
    intro x hx
    have hxlt : x.val < 4 * g := ZMod.val_lt x
    have hx1 : 1 ≤ x.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hx ((ZMod.val_eq_zero x).mp hc))
    unfold vertexSlot
    rw [if_neg hx]
    exact hval _ (by split_ifs <;> omega)
  by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
  · rw [ha0, hb0]
  · exfalso
    rw [ha0, vertexSlot_zero] at hab
    have h0 : (vertexSlot g b).val = 0 := by
      rw [← hab, ZMod.val_zero]
    rw [hslotval b hb0] at h0
    have hblt : b.val < 4 * g := ZMod.val_lt b
    have hb1 : 1 ≤ b.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hb0 ((ZMod.val_eq_zero b).mp hc))
    split_ifs at h0
    all_goals omega
  · exfalso
    rw [hb0, vertexSlot_zero] at hab
    have h0 : (vertexSlot g a).val = 0 := by
      rw [hab, ZMod.val_zero]
    rw [hslotval a ha0] at h0
    have halt : a.val < 4 * g := ZMod.val_lt a
    have ha1 : 1 ≤ a.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => ha0 ((ZMod.val_eq_zero a).mp hc))
    split_ifs at h0
    all_goals omega
  · have hv : (vertexSlot g a).val = (vertexSlot g b).val := by rw [hab]
    rw [hslotval a ha0, hslotval b hb0] at hv
    have halt : a.val < 4 * g := ZMod.val_lt a
    have hblt : b.val < 4 * g := ZMod.val_lt b
    have ha1 : 1 ≤ a.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => ha0 ((ZMod.val_eq_zero a).mp hc))
    have hb1 : 1 ≤ b.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hb0 ((ZMod.val_eq_zero b).mp hc))
    have hveq : a.val = b.val := by
      split_ifs at hv <;> omega
    exact ZMod.val_injective (4 * g) hveq

/-- The radius of the vertex chart: small enough that
`vertexRadius g ^ (2g) < π/(2g)`, keeping each compressed corner inside its
adjacent arcs. -/
noncomputable def vertexRadius (g : ℕ) : ℝ :=
  min (1 / 2) (Real.pi / (4 * g))

/-- The vertex chart radius is positive. -/
theorem vertexRadius_pos (g : ℕ) [NeZero g] : 0 < vertexRadius g := by
  sorry

/-- The compressed corner scale is below the arc scale:
`vertexRadius g ^ (2g) < π/(2g)`. -/
theorem vertexRadius_pow_lt (g : ℕ) [NeZero g] :
    vertexRadius g ^ (2 * g) < Real.pi / (2 * g) := by
  sorry

/-- The sector index of a chart-disc point: the integer part of its angle in
units of `π/(2g)`, with the angle normalized to `[0, 2π)`. -/
noncomputable def vertexSectorIndex (g : ℕ) (u : ℂ) : ℕ :=
  (⌊(2 * g / Real.pi) *
    (if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u)⌋).toNat

/-- The vertex chart inverse: on sector `m` of the chart disc, the class of
`polyVertex (c m) · exp (i · (-1)^m · u^(2g))`; the integer power `u^(2g)`
compresses each corner angle `π` to `π/(2g)`. -/
noncomputable def vertexChartFun (g : ℕ) [NeZero g] (u : ℂ) : GenusSurface g :=
  Quotient.mk (genusSetoid g)
    (projDisc (polyVertex g ((vertexSlot g (vertexSectorIndex g u)).val : ℤ) *
      Complex.exp (Complex.I * (-1) ^ vertexSectorIndex g u * u ^ (2 * g))))

/-- Ray consistency of the vertex chart: on the ray shared by sectors `m`
and `m + 1` the two sector formulas give `genusRel`-equal points — the side
pairing of arc `c m - 1` carries `polyVertex (c m) · e^{-iθ}` to
`polyVertex (π̂ (c m - 1)) · e^{+iθ}` and `π̂ (c m - 1) = c (m + 1)`. -/
theorem vertexRay_glue (g : ℕ) [NeZero g] (m : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : r ^ (2 * g) < Real.pi / (2 * g)) :
    genusRel g
      (projDisc (polyVertex g ((vertexSlot g (m : ZMod (4 * g))).val : ℤ) *
        Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g)))))
      (projDisc (polyVertex g ((vertexSlot g ((m : ZMod (4 * g)) + 1)).val : ℤ) *
        Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)))) := by
  sorry

/-- Continuity of the vertex chart inverse on the chart disc: `4g` closed
sectors glued along consistent rays, with all formulas tending to the vertex
class at `0`. -/
theorem vertexChart_continuousOn (g : ℕ) [NeZero g] :
    ContinuousOn (vertexChartFun g) (Metric.ball (0 : ℂ) (vertexRadius g)) := by
  sorry

/-- Injectivity of the vertex chart inverse on the chart disc: same-sector
collisions force `u^(2g) = u'^(2g)` within one closed angular sector, and
cross-sector collisions occur only on the shared rays, where the formulas
agree; uses injectivity of the slot map. -/
theorem vertexChart_injOn (g : ℕ) [NeZero g] :
    Set.InjOn (vertexChartFun g) (Metric.ball (0 : ℂ) (vertexRadius g)) := by
  sorry

/-- Openness of the vertex chart inverse: the union of the log-polar corner
neighborhoods is saturated and open in the disc. -/
theorem vertexChart_isOpen_image (g : ℕ) [NeZero g] :
    ∀ W ⊆ Metric.ball (0 : ℂ) (vertexRadius g), IsOpen W →
      IsOpen (vertexChartFun g '' W) := by
  sorry

/-- The vertex chart at the single vertex class, compressing the `4g`
corners of angle `π` into `4g` sectors of angle `π/(2g)`. -/
noncomputable def vertexChart (g : ℕ) [NeZero g] :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  OpenPartialHomeomorph.ofInvFunOn (vertexChartFun g)
    (Metric.ball 0 (vertexRadius g)) isOpen_ball (vertexChart_continuousOn g)
    (vertexChart_injOn g) (vertexChart_isOpen_image g)

/-! ## The atlas and the charted-space instance -/

/-- The atlas of the genus surface: the interior chart, the `2g` edge
charts, and the vertex chart. -/
noncomputable def genusAtlas (g : ℕ) [NeZero g] :
    Set (OpenPartialHomeomorph (GenusSurface g) ℂ) :=
  {interiorChart g} ∪ (Set.range fun jb : Fin g × Bool => edgeChart g jb.1 jb.2)
    ∪ {vertexChart g}

/-- Every class of the genus surface contains an interior point, an
edge-interior point, or is the vertex class, so the chart sources cover. -/
theorem chart_sources_cover (g : ℕ) [NeZero g] (p : GenusSurface g) :
    p ∈ (interiorChart g).source ∨
      (∃ jb : Fin g × Bool, p ∈ (edgeChart g jb.1 jb.2).source) ∨
      p ∈ (vertexChart g).source := by
  sorry

open Classical in
/-- The preferred chart at a point: the interior chart when possible, else
an edge chart, else the vertex chart. -/
noncomputable def genusChartAt (g : ℕ) [NeZero g] (p : GenusSurface g) :
    OpenPartialHomeomorph (GenusSurface g) ℂ :=
  if p ∈ (interiorChart g).source then interiorChart g
  else if h : ∃ jb : Fin g × Bool, p ∈ (edgeChart g jb.1 jb.2).source then
    edgeChart g h.choose.1 h.choose.2
  else vertexChart g

/-- Each point lies in the source of its preferred chart. -/
theorem mem_genusChartAt_source (g : ℕ) [NeZero g] (p : GenusSurface g) :
    p ∈ (genusChartAt g p).source := by
  sorry

/-- The preferred chart belongs to the atlas. -/
theorem genusChartAt_mem_atlas (g : ℕ) [NeZero g] (p : GenusSurface g) :
    genusChartAt g p ∈ genusAtlas g := by
  sorry

noncomputable instance instChartedSpaceGenusSurface (g : ℕ) [NeZero g] :
    ChartedSpace ℂ (GenusSurface g) where
  atlas := genusAtlas g
  chartAt := genusChartAt g
  mem_chart_source := mem_genusChartAt_source g
  chart_mem_atlas := genusChartAt_mem_atlas g

/-! ## Analytic transitions and the manifold instance -/

/-- The pairing-root identity along the corner cycle: with `n = c m - 1` a
source arc, the pairing root `exp (πi (2 c m + 1)/(2g))` of arc `n` divided
by the vertex `c (m+1)` is the vertex `c m`. -/
theorem pairingRoot_vertexSlot (g : ℕ) [NeZero g] (m : ℕ)
    (hsrc : (((vertexSlot g (m : ZMod (4 * g))).val : ℤ) - 1) % 4 = 0 ∨
      (((vertexSlot g (m : ZMod (4 * g))).val : ℤ) - 1) % 4 = 1) :
    Complex.exp (Real.pi * (2 * ((vertexSlot g (m : ZMod (4 * g))).val : ℤ) + 1) *
        Complex.I / (2 * g)) /
      polyVertex g ((vertexSlot g ((m : ZMod (4 * g)) + 1)).val : ℤ) =
      polyVertex g ((vertexSlot g (m : ZMod (4 * g))).val : ℤ) := by
  sorry

/-- Every transition map of the genus-surface atlas is analytic with
nonvanishing derivative on its source: each overlap component carries a
single formula `id`, `u ↦ ω/u`, or `u ↦ A · exp (± i u^(2g))`. -/
theorem transition_analyticAt (g : ℕ) [NeZero g] :
    ∀ e ∈ atlas ℂ (GenusSurface g), ∀ e' ∈ atlas ℂ (GenusSurface g),
      ∀ z ∈ (e.symm.trans e').source,
        AnalyticAt ℂ (e.symm.trans e') z ∧ deriv (e.symm.trans e') z ≠ 0 := by
  sorry

open scoped ContDiff in
/-- The genus surface is an analytic complex manifold: all atlas transitions
are analytic. -/
theorem isManifold_genusSurface (g : ℕ) [NeZero g] :
    IsManifold 𝓘(ℂ) ω (GenusSurface g) := by
  sorry

open scoped ContDiff in
instance (g : ℕ) [NeZero g] : IsManifold 𝓘(ℂ) ω (GenusSurface g) :=
  isManifold_genusSurface g

/-! ## Base points and the quotient map -/

/-- The base point of the genus surface: the class of the center of the
disc. -/
noncomputable def basePoint (g : ℕ) [NeZero g] : GenusSurface g :=
  Quotient.mk (genusSetoid g) ⟨0, Metric.mem_closedBall_self zero_le_one⟩

/-- The vertex of the `4g`-gon lies on the closed unit disc. -/
theorem polyVertex_mem_closedBall (g : ℕ) (m : ℤ) :
    polyVertex g m ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold polyVertex
  have h : (Real.pi * m * Complex.I / (2 * g) : ℂ)
      = ((Real.pi * m / (2 * g) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The vertex class of the genus surface. -/
noncomputable def vertexPoint (g : ℕ) [NeZero g] : GenusSurface g :=
  Quotient.mk (genusSetoid g) ⟨polyVertex g 0, polyVertex_mem_closedBall g 0⟩

/-- The projection to the genus surface is a quotient map. -/
theorem quotientMap_genus (g : ℕ) [NeZero g] :
    IsQuotientMap (Quotient.mk (genusSetoid g)) := isQuotientMap_quot_mk

/-- Openness in the genus surface is openness of the saturation in the
disc. -/
theorem isOpen_saturated_iff (g : ℕ) [NeZero g] (A : Set (GenusSurface g)) :
    IsOpen A ↔ IsOpen (Quotient.mk (genusSetoid g) ⁻¹' A) := (quotientMap_genus g).isOpen_preimage.symm

end RiemannDynamics
