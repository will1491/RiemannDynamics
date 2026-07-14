/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import RiemannDynamics.Analysis.Winding.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

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
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  rw [isOpen_iff_mem_nhds]
  intro u hu
  obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
  have hρ0 : (0 : ℝ) < ρ := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (θ' - k) (k + 1 - θ') := ⟨_, rfl⟩
  have hm1 : m ≤ θ' - k := by rw [hm]; exact min_le_left _ _
  have hm2 : m ≤ k + 1 - θ' := by rw [hm]; exact min_le_right _ _
  have hm0 : 0 < m := by rw [hm]; exact lt_min (by linarith) (by linarith)
  have h2g : (0 : ℝ) < 2 * g := by linarith
  have hb0 : 0 < Real.pi * m / (2 * g) := div_pos (mul_pos hπ hm0) h2g
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = Complex.exp (-(Real.pi * (θ' : ℂ) * Complex.I / (2 * g))) :=
    ⟨_, rfl⟩
  have hcnorm : ‖c‖ = 1 := by
    rw [hc]
    have h : (-(Real.pi * (θ' : ℂ) * Complex.I / (2 * g)))
        = ((-(Real.pi * θ' / (2 * g)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have huc : u * c = (ρ : ℂ) := by
    rw [hue, hc, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  have hunorm : ‖u‖ = ρ := by
    rw [hue, norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hmemA : ‖u‖ ∈ Set.Ioo (1 / 2 : ℝ) 2 := by
    rw [hunorm]
    exact ⟨hρ1, hρ2⟩
  have hA : (fun w : ℂ => ‖w‖) ⁻¹' Set.Ioo (1 / 2 : ℝ) 2 ∈ 𝓝 u :=
    ContinuousAt.preimage_mem_nhds continuous_norm.continuousAt (isOpen_Ioo.mem_nhds hmemA)
  have harg0 : Complex.arg (u * c) = 0 := by
    rw [huc]
    exact Complex.arg_ofReal_of_nonneg hρ0.le
  have hslit : u * c ∈ Complex.slitPlane := by
    rw [huc]
    exact Complex.ofReal_mem_slitPlane.mpr hρ0
  have hmemB : Complex.arg (u * c)
      ∈ Set.Ioo (-(Real.pi * m / (2 * g))) (Real.pi * m / (2 * g)) := by
    rw [harg0]
    exact ⟨by linarith, hb0⟩
  have hmulc : ContinuousAt (fun w : ℂ => w * c) u := continuousAt_id.mul continuousAt_const
  have hargc : ContinuousAt (fun w : ℂ => Complex.arg (w * c)) u := by
    exact ContinuousAt.comp (x := u) (f := fun w : ℂ => w * c)
      (Complex.continuousAt_arg hslit) hmulc
  have hB : (fun w : ℂ => Complex.arg (w * c)) ⁻¹'
      Set.Ioo (-(Real.pi * m / (2 * g))) (Real.pi * m / (2 * g)) ∈ 𝓝 u :=
    ContinuousAt.preimage_mem_nhds hargc (isOpen_Ioo.mem_nhds hmemB)
  filter_upwards [hA, hB] with w hw1 hw2
  simp only [Set.mem_preimage, Set.mem_Ioo] at hw1 hw2
  refine ⟨‖w‖, θ' + 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi, hw1.1, hw1.2, ?_, ?_, ?_⟩
  · have h1 : -(Real.pi * m) < Complex.arg (w * c) * (2 * g) := by
      have e1 : -(Real.pi * m / (2 * g)) * (2 * g) = -(Real.pi * m) := by field_simp
      rw [← e1]
      exact mul_lt_mul_of_pos_right hw2.1 h2g
    have h2 : -m < 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi := by
      rw [lt_div_iff₀ hπ]
      linarith
    linarith
  · have h1 : Complex.arg (w * c) * (2 * g) < Real.pi * m := by
      have e1 : Real.pi * m / (2 * g) * (2 * g) = Real.pi * m := by field_simp
      rw [← e1]
      exact mul_lt_mul_of_pos_right hw2.2 h2g
    have h2 : 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi < m := by
      rw [div_lt_iff₀ hπ]
      linarith
    linarith
  · have hwc := Complex.norm_mul_exp_arg_mul_I (w * c)
    have hnwc : ‖w * c‖ = ‖w‖ := by rw [norm_mul, hcnorm, mul_one]
    have hcc : c * Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) = 1 := by
      rw [hc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
    calc w = w * (c * Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g))) := by
            rw [hcc, mul_one]
      _ = ↑‖w * c‖ * Complex.exp ((Complex.arg (w * c) : ℂ) * Complex.I) *
            Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
            rw [hwc, ← mul_assoc]
      _ = ↑‖w‖ * Complex.exp
            (Real.pi * ((θ' + 2 * (g : ℝ) * Complex.arg (w * c) / Real.pi : ℝ) : ℂ) *
              Complex.I / (2 * g)) := by
            rw [hnwc, mul_assoc, ← Complex.exp_add]
            congr 2
            push_cast
            field_simp
            ring

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
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hne0 : ∀ u ∈ edgeSector g k, u ≠ 0 := by
    intro u hu
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    rw [hue]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (Complex.exp_ne_zero _)
  have hq : Continuous (Quotient.mk (genusSetoid g)) := continuous_quot_mk
  have hσc : ContinuousOn (sidePairing g k) {u : ℂ | u ≠ 0} := by
    unfold sidePairing
    exact continuousOn_const.div continuousOn_id fun x hx => hx
  have hσq : ContinuousOn
      (fun u => Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)))
      {u : ℂ | u ≠ 0} := by
    exact ((hq.comp continuous_projDisc).comp_continuousOn hσc)
  have hfr : frontier {a : ℂ | ‖a‖ ≤ 1} ⊆ {a : ℂ | ‖a‖ = 1} := by
    have hset : {a : ℂ | ‖a‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
      ext a
      simp
    rw [hset, frontier_closedBall (0 : ℂ) one_ne_zero]
    intro a ha
    exact mem_sphere_zero_iff_norm.mp ha
  unfold edgeChartFun
  refine ContinuousOn.if ?_ ?_ ?_
  · rintro a ⟨haS, hafr⟩
    have hA1 : ‖a‖ = 1 := hfr hafr
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hae⟩ := haS
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hρval : ρ = 1 := by
      rw [hae, norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ0] at hA1
      exact hA1
    have hae1 : a = Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
      rw [hae, hρval, Complex.ofReal_one, one_mul]
    have haarc : a = arcPoint g k (θ' - k) := by
      rw [hae1]
      unfold arcPoint
      congr 1
      push_cast
      ring
    have hσarc : sidePairing g k a = arcPoint g (k + 2) (1 - (θ' - k)) := by
      rw [haarc, sidePairing_arcPoint]
    have ht0 : (0 : ℝ) ≤ θ' - k := by linarith
    have ht1 : θ' - (k : ℝ) ≤ 1 := by linarith
    have hva : (projDisc a).1 = a := projDisc_eq hA1.le
    have hσnorm : ‖sidePairing g k a‖ = 1 := norm_sidePairing g k hA1
    have hvσ : (projDisc (sidePairing g k a)).1 = sidePairing g k a := projDisc_eq hσnorm.le
    have hfst : arcPoint g k (θ' - k) = (projDisc a).1 := by
      rw [hva]
      exact haarc.symm
    have hsnd : arcPoint g (k + 2) (1 - (θ' - k)) = (projDisc (sidePairing g k a)).1 := by
      rw [hvσ]
      exact hσarc.symm
    have hrel : genusRel g (projDisc a) (projDisc (sidePairing g k a)) := by
      have hpair : ((projDisc a).1, (projDisc (sidePairing g k a)).1) ∈ pairGraph g k := by
        refine ⟨⟨θ' - k, ht0, ht1⟩, Set.mem_univ _, ?_⟩
        rw [← hfst, ← hsnd]
      exact Or.inr (Or.inl ⟨k, hk, Or.inl hpair⟩)
    exact Quotient.sound hrel
  · exact (hq.comp continuous_projDisc).continuousOn
  · exact hσq.mono fun x hx => hne0 x hx.1

/-- Injectivity of the edge chart inverse on its sector: the disc part has
angle parameter in `(k, k+1)`, the reflected exterior part in `(k+2, k+3)`,
and no vertices occur. -/
theorem edgeChart_injOn (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    Set.InjOn (edgeChartFun g k) (edgeSector g k) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hnormE : ∀ r s : ℝ, 0 ≤ r →
      ‖(r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = r := by
    intro r s hr
    rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have harc0 : ∀ s : ℝ,
      arcPoint g 0 s = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
    intro s
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hEeq : ∀ s s' : ℝ,
      Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
      ↔ ∃ n : ℤ, s - s' = 4 * g * n := by
    intro s s'
    rw [← harc0 s, ← harc0 s', arcPoint_eq_iff g 0 0 s s']
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast at hn
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast
      linarith
  have harcE : ∀ (j : ℤ) (t : ℝ), arcPoint g j t
      = Complex.exp (Real.pi * (((j : ℝ) + t : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro j t
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hvertE : ∀ m : ℤ, polyVertex g m
      = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro m
    unfold polyVertex
    congr 1
  have hσE : ∀ r s : ℝ, r ≠ 0 →
      sidePairing g k ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))
        = ((r⁻¹ : ℝ) : ℂ) *
          Complex.exp (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro r s hr
    unfold sidePairing
    have hne : ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)
    rw [div_eq_iff hne, mul_mul_mul_comm, ← Complex.ofReal_mul, inv_mul_cancel₀ hr,
      Complex.ofReal_one, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have harc : ∀ (k₁ : ℤ) (t : ℝ), ‖arcPoint g k₁ t‖ = 1 := by
    intro k₁ t
    rw [harcE]
    exact hnorm1 _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    rw [hvertE]
    exact hnorm1 _
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k₁ ∨ (w.1, z.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k₁, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k₁ (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k₁ + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvert] at hz
      exact absurd hz (lt_irrefl 1)
  have hclass : ∀ (s : ℝ) (w z : ClosedDisc),
      ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) →
      w.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) →
      genusRel g w z →
      z.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) ∨
        z.1 = Complex.exp
          (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro s w z hs hw hrel
    have hrel' : w = z
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((w.1, z.1) ∈ pairGraph g k₁ ∨ (z.1, w.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g w.1 ∧ IsPolyVertex g z.1) := hrel
    rcases hrel' with h | ⟨k₁, hk₁, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · left
      rw [← h]
      exact hw
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = w.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = z.1 := congrArg Prod.snd ht
      rw [harcE, hw] at h1
      rw [harcE] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((4 * P + k - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ)) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k - k₁ ∧ 4 * P + k - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ0 : 4 * P + k - k₁ = 0 := by omega
        have htv : (t : ℝ) - (s - (k : ℝ)) = 0 := by
          have h0 : ((4 * P + k - k₁ : ℤ) : ℝ) = 0 := by
            rw [hJ0]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h2]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        push_cast
        linarith [hn, htv]
      · exfalso
        have hJr : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ) - 2) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k + 2 - k₁ ∧ 4 * P + k + 2 - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k + 2 - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = z.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = w.1 := congrArg Prod.snd ht
      rw [harcE] at h1
      rw [harcE, hw] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h2
      push_cast at hn
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · exfalso
        have hJr : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ)) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 3 - k - 4 * P ∧ k₁ + 3 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ) - 2) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 1 - k - 4 * P ∧ k₁ + 1 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ1 : k₁ + 1 - k - 4 * P = 1 := by omega
        have htv : (s - (k : ℝ) - 2) + (t : ℝ) = 1 := by
          have h0 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = 1 := by
            rw [hJ1]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h1]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        linarith [hn, htv]
    · exfalso
      have h1 : Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
          = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
        rw [← hw, ← hvertE]
        exact hm
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((m + 4 * P - k : ℤ) : ℝ) = s - (k : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k ∧ m + 4 * P - k < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((m + 4 * P - k - 2 : ℤ) : ℝ) = s - (k : ℝ) - 2 := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k - 2 ∧ m + 4 * P - k - 2 < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k - 2 : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k - 2 : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
  have hkey : ∀ r s r' s' : ℝ, 1 / 2 < r → r ≤ 1 → 1 / 2 < r' → r' ≤ 1 →
      ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) →
      ((k : ℝ) < s' ∧ s' < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s' ∧ s' < (k : ℝ) + 3) →
      Quotient.mk (genusSetoid g)
          (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))))
        = Quotient.mk (genusSetoid g)
          (projDisc ((r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))) →
      (r = r' ∧ ∃ n : ℤ, s - s' = 4 * g * n) ∨
        (r = 1 ∧ r' = 1 ∧ ∃ n : ℤ, s + s' - (2 * (k : ℝ) + 3) = 4 * g * n) := by
    intro r s r' s' hr1 hr2 hr1' hr2' hsA hsA' hquot
    have hr0 : (0 : ℝ) < r := by linarith
    have hr0' : (0 : ℝ) < r' := by linarith
    have hns : ‖(r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = r :=
      hnormE r s hr0.le
    have hns' : ‖(r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))‖ = r' :=
      hnormE r' s' hr0'.le
    have hv : (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))).1
        = (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) :=
      projDisc_eq (by rw [hns]; exact hr2)
    have hv' : (projDisc ((r' : ℂ) *
          Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))).1
        = (r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)) :=
      projDisc_eq (by rw [hns']; exact hr2')
    have hrel : genusRel g
        (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))))
        (projDisc ((r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))) :=
      Quotient.exact hquot
    rcases lt_or_eq_of_le hr2 with hlt | heq1
    · have hz : ‖(projDisc ((r : ℂ) *
          Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))).1‖ < 1 := by
        rw [hv, hns]
        exact hlt
      have heqd := hsingle _ _ hz hrel
      have hvals : (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
          = (r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)) := by
        rw [← hv, ← hv', heqd]
      have hrr : r = r' := by
        have h1 := hns
        rw [hvals, hns'] at h1
        exact h1.symm
      left
      refine ⟨hrr, (hEeq s s').mp ?_⟩
      have hcan : ((r' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0'.ne'
      rw [hrr] at hvals
      exact mul_left_cancel₀ hcan hvals
    · rcases lt_or_eq_of_le hr2' with hlt' | heq1'
      · exfalso
        have hrel2 : genusRel g
            (projDisc ((r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))))
            (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))) :=
          Quotient.exact hquot.symm
        have hz' : ‖(projDisc ((r' : ℂ) *
            Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))).1‖ < 1 := by
          rw [hv', hns']
          exact hlt'
        have heqd := hsingle _ _ hz' hrel2
        have hvals : (r' : ℂ) * Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
            = (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
          rw [← hv', ← hv, heqd]
        have h1 := hns'
        rw [hvals, hns] at h1
        linarith
      · have hw1 : (projDisc ((r : ℂ) *
            Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))).1
            = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
          rw [hv, heq1, Complex.ofReal_one, one_mul]
        have hz1' : (projDisc ((r' : ℂ) *
            Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)))).1
            = Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g)) := by
          rw [hv', heq1', Complex.ofReal_one, one_mul]
        have hcls := hclass s _ _ hsA hw1 hrel
        rcases hcls with hcase | hcase
        · left
          refine ⟨by rw [heq1, heq1'], (hEeq s s').mp ?_⟩
          have h3 : Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
              = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
            rw [← hz1']
            exact hcase
          exact h3.symm
        · right
          refine ⟨heq1, heq1', ?_⟩
          have h3 : Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
              = Complex.exp
                (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
            rw [← hz1']
            exact hcase
          obtain ⟨n, hn⟩ := (hEeq _ _).mp h3
          exact ⟨n, by linarith [hn]⟩
  have hnf : ∀ u ∈ edgeSector g k, ∃ r s : ℝ, 1 / 2 < r ∧ r ≤ 1 ∧
      edgeChartFun g k u
        = Quotient.mk (genusSetoid g)
            (projDisc ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))) ∧
      (((k : ℝ) < s ∧ s < (k : ℝ) + 1 ∧
          u = (r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))) ∨
        ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3 ∧ r < 1 ∧
          u = ((r⁻¹ : ℝ) : ℂ) *
            Complex.exp
              (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)))) := by
    intro u hu
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hun : ‖u‖ = ρ := by
      rw [hue]
      exact hnormE ρ θ' hρ0.le
    by_cases hA : ‖u‖ ≤ 1
    · refine ⟨ρ, θ', hρ1, by rw [← hun]; exact hA, ?_, Or.inl ⟨hθ1, hθ2, hue⟩⟩
      unfold edgeChartFun
      rw [if_pos hA, hue]
    · have hρgt : 1 < ρ := by
        rw [← hun]
        exact not_le.mp hA
      have hinv0 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
      have hcancel : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0.ne'
      have hinv1 : ρ⁻¹ < 1 := by nlinarith
      have hinvhalf : 1 / 2 < ρ⁻¹ := by nlinarith
      refine ⟨ρ⁻¹, 2 * (k : ℝ) + 3 - θ', hinvhalf, hinv1.le, ?_,
        Or.inr ⟨by linarith, by linarith, hinv1, ?_⟩⟩
      · unfold edgeChartFun
        rw [if_neg hA, hue, hσE ρ θ' hρ0.ne']
      · have e1 : (ρ⁻¹)⁻¹ = ρ := inv_inv ρ
        have e2 : 2 * (k : ℝ) + 3 - (2 * (k : ℝ) + 3 - θ') = θ' := by ring
        rw [e1, e2]
        exact hue
  intro u hu u' hu' heq
  obtain ⟨r, s, hr1, hr2, hval, hcase⟩ := hnf u hu
  obtain ⟨r', s', hr1', hr2', hval', hcase'⟩ := hnf u' hu'
  rw [hval, hval'] at heq
  have hranges : ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) := by
    rcases hcase with ⟨h1, h2, -⟩ | ⟨h1, h2, -, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hranges' : ((k : ℝ) < s' ∧ s' < (k : ℝ) + 1) ∨
      ((k : ℝ) + 2 < s' ∧ s' < (k : ℝ) + 3) := by
    rcases hcase' with ⟨h1, h2, -⟩ | ⟨h1, h2, -, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  rcases hkey r s r' s' hr1 hr2 hr1' hr2' hranges hranges' heq with
    ⟨hrr, n, hn⟩ | ⟨hre1, hre1', n, hn⟩
  · obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
    have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
      rw [← hP]
      push_cast
      ring
    have hJr : ((4 * P : ℤ) : ℝ) = s - s' := by
      push_cast
      linarith [hn, hPr]
    rcases hcase with ⟨hs1, hs2, hueq⟩ | ⟨hs1, hs2, -, hueq⟩
    · rcases hcase' with ⟨hs1', hs2', hueq'⟩ | ⟨hs1', hs2', -, -⟩
      · have hss : s = s' := by
          have hJZ : (-1 : ℤ) < 4 * P ∧ 4 * P < 1 := by
            have hR1 : (-1 : ℝ) < ((4 * P : ℤ) : ℝ) := by
              rw [hJr]
              linarith
            have hR2 : ((4 * P : ℤ) : ℝ) < 1 := by
              rw [hJr]
              linarith
            exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
          have hP0 : (4 * P : ℤ) = 0 := by omega
          have h0 : ((4 * P : ℤ) : ℝ) = 0 := by
            rw [hP0]
            norm_num
          rw [hJr] at h0
          linarith
        rw [hueq, hueq', hrr, hss]
      · exfalso
        have hJZ : (-3 : ℤ) < 4 * P ∧ 4 * P < -1 := by
          have hR1 : (-3 : ℝ) < ((4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P : ℤ) : ℝ) < -1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
    · rcases hcase' with ⟨hs1', hs2', -⟩ | ⟨hs1', hs2', -, hueq'⟩
      · exfalso
        have hJZ : (1 : ℤ) < 4 * P ∧ 4 * P < 3 := by
          have hR1 : (1 : ℝ) < ((4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P : ℤ) : ℝ) < 3 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hss : s = s' := by
          have hJZ : (-1 : ℤ) < 4 * P ∧ 4 * P < 1 := by
            have hR1 : (-1 : ℝ) < ((4 * P : ℤ) : ℝ) := by
              rw [hJr]
              linarith
            have hR2 : ((4 * P : ℤ) : ℝ) < 1 := by
              rw [hJr]
              linarith
            exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
          have hP0 : (4 * P : ℤ) = 0 := by omega
          have h0 : ((4 * P : ℤ) : ℝ) = 0 := by
            rw [hP0]
            norm_num
          rw [hJr] at h0
          linarith
        rw [hueq, hueq', hrr, hss]
  · rcases hcase with ⟨hs1, hs2, -⟩ | ⟨-, -, hrlt, -⟩
    · rcases hcase' with ⟨hs1', hs2', -⟩ | ⟨-, -, hrlt', -⟩
      · exfalso
        obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
        have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
          rw [← hP]
          push_cast
          ring
        have hJr : ((4 * P : ℤ) : ℝ) = s + s' - (2 * (k : ℝ) + 3) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-3 : ℤ) < 4 * P ∧ 4 * P < -1 := by
          have hR1 : (-3 : ℝ) < ((4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P : ℤ) : ℝ) < -1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · exfalso
        rw [hre1'] at hrlt'
        exact lt_irrefl 1 hrlt'
    · exfalso
      rw [hre1] at hrlt
      exact lt_irrefl 1 hrlt

/-- Openness of the edge chart inverse: the saturation of the image of an
open subset adds the pairing mirror of its boundary trace, which is open in
the disc by the two-sided half-ball argument. -/
theorem edgeChart_isOpen_image (g : ℕ) [NeZero g] (k : ℤ)
    (hk : k % 4 = 0 ∨ k % 4 = 1) :
    ∀ W ⊆ edgeSector g k, IsOpen W → IsOpen (edgeChartFun g k '' W) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne g)
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hnormE : ∀ r s : ℝ, 0 ≤ r →
      ‖(r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = r := by
    intro r s hr
    rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have harc0 : ∀ s : ℝ,
      arcPoint g 0 s = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) := by
    intro s
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hEeq : ∀ s s' : ℝ,
      Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = Complex.exp (Real.pi * (s' : ℂ) * Complex.I / (2 * g))
      ↔ ∃ n : ℤ, s - s' = 4 * g * n := by
    intro s s'
    rw [← harc0 s, ← harc0 s', arcPoint_eq_iff g 0 0 s s']
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast at hn
      linarith
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      push_cast
      linarith
  have harcE : ∀ (j : ℤ) (t : ℝ), arcPoint g j t
      = Complex.exp (Real.pi * (((j : ℝ) + t : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro j t
    unfold arcPoint
    congr 1
    push_cast
    ring
  have hvertE : ∀ m : ℤ, polyVertex g m
      = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro m
    unfold polyVertex
    congr 1
  have hσE : ∀ r s : ℝ, r ≠ 0 →
      sidePairing g k ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)))
        = ((r⁻¹ : ℝ) : ℂ) *
          Complex.exp (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro r s hr
    unfold sidePairing
    have hne : ((r : ℂ) * Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)
    rw [div_eq_iff hne, mul_mul_mul_comm, ← Complex.ofReal_mul, inv_mul_cancel₀ hr,
      Complex.ofReal_one, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have harc : ∀ (k₁ : ℤ) (t : ℝ), ‖arcPoint g k₁ t‖ = 1 := by
    intro k₁ t
    rw [harcE]
    exact hnorm1 _
  have hvert : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    rw [hvertE]
    exact hnorm1 _
  have hsingle : ∀ z w : ClosedDisc, ‖z.1‖ < 1 → genusRel g z w → z = w := by
    intro z w hz hrel
    have hrel' : z = w
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((z.1, w.1) ∈ pairGraph g k₁ ∨ (w.1, z.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hrel
    rcases hrel' with h | ⟨k₁, -, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · exact h
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g k₁ (s : ℝ) = z.1 := congrArg Prod.fst hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k₁ + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harc] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvert] at hz
      exact absurd hz (lt_irrefl 1)
  have hclass : ∀ (s : ℝ) (w z : ClosedDisc),
      ((k : ℝ) < s ∧ s < (k : ℝ) + 1) ∨ ((k : ℝ) + 2 < s ∧ s < (k : ℝ) + 3) →
      w.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) →
      genusRel g w z →
      z.1 = Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g)) ∨
        z.1 = Complex.exp
          (Real.pi * ((2 * (k : ℝ) + 3 - s : ℝ) : ℂ) * Complex.I / (2 * g)) := by
    intro s w z hs hw hrel
    have hrel' : w = z
        ∨ (∃ k₁ : ℤ, (k₁ % 4 = 0 ∨ k₁ % 4 = 1) ∧
            ((w.1, z.1) ∈ pairGraph g k₁ ∨ (z.1, w.1) ∈ pairGraph g k₁))
        ∨ (IsPolyVertex g w.1 ∧ IsPolyVertex g z.1) := hrel
    rcases hrel' with h | ⟨k₁, hk₁, h | h⟩ | ⟨⟨m, hm⟩, -⟩
    · left
      rw [← h]
      exact hw
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = w.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = z.1 := congrArg Prod.snd ht
      rw [harcE, hw] at h1
      rw [harcE] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((4 * P + k - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ)) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k - k₁ ∧ 4 * P + k - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ0 : 4 * P + k - k₁ = 0 := by omega
        have htv : (t : ℝ) - (s - (k : ℝ)) = 0 := by
          have h0 : ((4 * P + k - k₁ : ℤ) : ℝ) = 0 := by
            rw [hJ0]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h2]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        push_cast
        linarith [hn, htv]
      · exfalso
        have hJr : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) = (t : ℝ) - (s - (k : ℝ) - 2) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (-1 : ℤ) < 4 * P + k + 2 - k₁ ∧ 4 * P + k + 2 - k₁ < 1 := by
          have hR1 : (-1 : ℝ) < ((4 * P + k + 2 - k₁ : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((4 * P + k + 2 - k₁ : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
    · obtain ⟨t, -, ht⟩ := h
      have h1 : arcPoint g k₁ (t : ℝ) = z.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k₁ + 2) (1 - (t : ℝ)) = w.1 := congrArg Prod.snd ht
      rw [harcE] at h1
      rw [harcE, hw] at h2
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h2
      push_cast at hn
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · exfalso
        have hJr : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ)) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 3 - k - 4 * P ∧ k₁ + 3 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 3 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = (s - (k : ℝ) - 2) + (t : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < k₁ + 1 - k - 4 * P ∧ k₁ + 1 - k - 4 * P < 2 := by
          have hR1 : (0 : ℝ) < ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) < 2 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        have hJ1 : k₁ + 1 - k - 4 * P = 1 := by omega
        have htv : (s - (k : ℝ) - 2) + (t : ℝ) = 1 := by
          have h0 : ((k₁ + 1 - k - 4 * P : ℤ) : ℝ) = 1 := by
            rw [hJ1]
            norm_num
          rw [hJr] at h0
          exact h0
        right
        rw [← h1]
        refine (hEeq _ _).mpr ⟨n, ?_⟩
        linarith [hn, htv]
    · exfalso
      have h1 : Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))
          = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
        rw [← hw, ← hvertE]
        exact hm
      obtain ⟨n, hn⟩ := (hEeq _ _).mp h1
      obtain ⟨P, hP⟩ : ∃ P : ℤ, (g : ℤ) * n = P := ⟨_, rfl⟩
      have hPr : ((P : ℤ) : ℝ) = (g : ℝ) * (n : ℝ) := by
        rw [← hP]
        push_cast
        ring
      rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · have hJr : ((m + 4 * P - k : ℤ) : ℝ) = s - (k : ℝ) := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k ∧ m + 4 * P - k < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
      · have hJr : ((m + 4 * P - k - 2 : ℤ) : ℝ) = s - (k : ℝ) - 2 := by
          push_cast
          linarith [hn, hPr]
        have hJZ : (0 : ℤ) < m + 4 * P - k - 2 ∧ m + 4 * P - k - 2 < 1 := by
          have hR1 : (0 : ℝ) < ((m + 4 * P - k - 2 : ℤ) : ℝ) := by
            rw [hJr]
            linarith
          have hR2 : ((m + 4 * P - k - 2 : ℤ) : ℝ) < 1 := by
            rw [hJr]
            linarith
          exact ⟨by exact_mod_cast hR1, by exact_mod_cast hR2⟩
        omega
  have hne0 : ∀ u ∈ edgeSector g k, u ≠ 0 := by
    intro u hu
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    rw [hue]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (Complex.exp_ne_zero _)
  have hσc : ContinuousOn (sidePairing g k) {u : ℂ | u ≠ 0} := by
    unfold sidePairing
    exact continuousOn_const.div continuousOn_id fun x hx => hx
  have hωnorm : ‖Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))‖ = 1 := by
    have harg2 : (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))
        = Real.pi * ((2 * (k : ℝ) + 3 : ℝ) : ℂ) * Complex.I / (2 * g) := by
      push_cast
      ring
    rw [harg2]
    exact hnorm1 _
  have hσnorm : ∀ u : ℂ, ‖sidePairing g k u‖ = 1 / ‖u‖ := by
    intro u
    unfold sidePairing
    rw [norm_div, hωnorm]
  have hvalA : ∀ u : ℂ, ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc u) := by
    intro u h
    unfold edgeChartFun
    rw [if_pos h]
  have hvalB : ∀ u : ℂ, ¬ ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)) := by
    intro u h
    unfold edgeChartFun
    rw [if_neg h]
  have hσimg : ∀ V : Set ℂ, V ⊆ edgeSector g k →
      sidePairing g k '' V = {z : ℂ | z ≠ 0} ∩ sidePairing g k ⁻¹' V := by
    intro V hVsec
    ext z
    constructor
    · rintro ⟨v, hvV, rfl⟩
      have hv0 : v ≠ 0 := hne0 v (hVsec hvV)
      refine ⟨?_, ?_⟩
      · have hne : sidePairing g k v ≠ 0 := by
          unfold sidePairing
          exact div_ne_zero (Complex.exp_ne_zero _) hv0
        exact hne
      · have hmem : sidePairing g k (sidePairing g k v) ∈ V := by
          rw [sidePairing_involutive g k hv0]
          exact hvV
        exact hmem
    · rintro ⟨hz0, hzV⟩
      exact ⟨sidePairing g k z, hzV, sidePairing_involutive g k hz0⟩
  have hσopen : ∀ V : Set ℂ, V ⊆ edgeSector g k → IsOpen V →
      IsOpen (sidePairing g k '' V) := by
    intro V hVsec hV
    rw [hσimg V hVsec]
    exact hσc.isOpen_inter_preimage isOpen_ne hV
  have hpairrel : ∀ a ∈ edgeSector g k, ‖a‖ = 1 →
      genusRel g (projDisc a) (projDisc (sidePairing g k a)) := by
    intro a haS hA1
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hae⟩ := haS
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hρval : ρ = 1 := by
      rw [hae, hnormE ρ θ' hρ0.le] at hA1
      exact hA1
    have haarc : a = arcPoint g k (θ' - k) := by
      rw [hae, hρval, Complex.ofReal_one, one_mul]
      unfold arcPoint
      congr 1
      push_cast
      ring
    have hσarc : sidePairing g k a = arcPoint g (k + 2) (1 - (θ' - k)) := by
      rw [haarc, sidePairing_arcPoint]
    have ht0 : (0 : ℝ) ≤ θ' - k := by linarith
    have ht1 : θ' - (k : ℝ) ≤ 1 := by linarith
    have hva : (projDisc a).1 = a := projDisc_eq hA1.le
    have hσn1 : ‖sidePairing g k a‖ = 1 := norm_sidePairing g k hA1
    have hvσ : (projDisc (sidePairing g k a)).1 = sidePairing g k a := projDisc_eq hσn1.le
    have hfst : arcPoint g k (θ' - k) = (projDisc a).1 := by
      rw [hva]
      exact haarc.symm
    have hsnd : arcPoint g (k + 2) (1 - (θ' - k)) = (projDisc (sidePairing g k a)).1 := by
      rw [hvσ]
      exact hσarc.symm
    have hpair : ((projDisc a).1, (projDisc (sidePairing g k a)).1) ∈ pairGraph g k := by
      refine ⟨⟨θ' - k, ht0, ht1⟩, Set.mem_univ _, ?_⟩
      rw [← hfst, ← hsnd]
    exact Or.inr (Or.inl ⟨k, hk, Or.inl hpair⟩)
  intro W hWsec hW
  have hqimg : edgeChartFun g k '' W
      = Quotient.mk (genusSetoid g) ''
        {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W} := by
    ext p
    constructor
    · rintro ⟨u, huW, rfl⟩
      by_cases hA : ‖u‖ ≤ 1
      · refine ⟨projDisc u, ?_, (hvalA u hA).symm⟩
        have hmem : (projDisc u).1 ∈ W := by
          rw [projDisc_eq hA]
          exact huW
        exact Or.inl hmem
      · have hu1 : 1 < ‖u‖ := not_le.mp hA
        have hlt : ‖sidePairing g k u‖ < 1 := by
          rw [hσnorm u]
          exact (div_lt_one (by linarith)).mpr hu1
        refine ⟨projDisc (sidePairing g k u), ?_, (hvalB u hA).symm⟩
        have hmem : (projDisc (sidePairing g k u)).1 ∈ sidePairing g k '' W := by
          rw [projDisc_eq hlt.le]
          exact ⟨u, huW, rfl⟩
        exact Or.inr hmem
    · rintro ⟨z, hz, rfl⟩
      have hz' : z.1 ∈ W ∨ z.1 ∈ sidePairing g k '' W := hz
      have hznorm : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      rcases hz' with hzW | ⟨v, hvW, hzv⟩
      · refine ⟨z.1, hzW, ?_⟩
        rw [hvalA z.1 hznorm]
        exact congrArg _ (Subtype.ext (projDisc_eq hznorm))
      · by_cases hv1 : ‖v‖ ≤ 1
        · have hv0 : v ≠ 0 := hne0 v (hWsec hvW)
          have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
          have hveq : ‖v‖ = 1 := by
            have h2 : (1 : ℝ) / ‖v‖ ≤ 1 := by
              rw [← hσnorm v, hzv]
              exact hznorm
            rw [div_le_one hvpos] at h2
            linarith
          have hσv1 : ‖sidePairing g k v‖ ≤ 1 := by
            rw [hσnorm v, hveq]
            norm_num
          have hz_eq : projDisc (sidePairing g k v) = z :=
            Subtype.ext ((projDisc_eq hσv1).trans hzv)
          refine ⟨v, hvW, ?_⟩
          rw [hvalA v hv1, ← hz_eq]
          exact Quotient.sound (hpairrel v (hWsec hvW) hveq)
        · have hu1 : 1 < ‖v‖ := not_le.mp hv1
          have hlt : ‖sidePairing g k v‖ < 1 := by
            rw [hσnorm v]
            exact (div_lt_one (by linarith)).mpr hu1
          refine ⟨v, hvW, ?_⟩
          rw [hvalB v hv1]
          exact congrArg _ (Subtype.ext ((projDisc_eq hlt.le).trans hzv))
  rw [hqimg]
  have hAopen : IsOpen (W ∪ sidePairing g k '' W) := hW.union (hσopen W hWsec hW)
  have hsat : Quotient.mk (genusSetoid g) ⁻¹'
      (Quotient.mk (genusSetoid g) '' {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W})
      = {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W} := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro p ⟨z, hz, hzp⟩
    have hrel : genusRel g z p := Quotient.exact hzp
    have hz' : z.1 ∈ W ∨ z.1 ∈ sidePairing g k '' W := hz
    rcases hz' with hzW | ⟨v, hvW, hzv⟩
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hze⟩ := hWsec hzW
      have hρ0 : (0 : ℝ) < ρ := by linarith
      have hznorm : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have hzρ : ‖z.1‖ = ρ := by
        rw [hze]
        exact hnormE ρ θ' hρ0.le
      have hρle : ρ ≤ 1 := by
        rw [← hzρ]
        exact hznorm
      rcases lt_or_eq_of_le hρle with hρlt | hρ1eq
      · have hzn : ‖z.1‖ < 1 := by
          rw [hzρ]
          exact hρlt
        have hzp' := hsingle z p hzn hrel
        rw [← hzp']
        exact Or.inl hzW
      · have hze1 : z.1 = Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
          rw [hze, hρ1eq, Complex.ofReal_one, one_mul]
        have hcls := hclass θ' z p (Or.inl ⟨hθ1, hθ2⟩) hze1 hrel
        rcases hcls with hp | hp
        · have hmem : p.1 ∈ W := by
            rw [hp, ← hze1]
            exact hzW
          exact Or.inl hmem
        · have hz1' : z.1 = ((1 : ℝ) : ℂ) *
              Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
            rw [hze1, Complex.ofReal_one, one_mul]
          have hσz := hσE 1 θ' one_ne_zero
          rw [← hz1'] at hσz
          have hσz' : sidePairing g k z.1 = Complex.exp
              (Real.pi * ((2 * (k : ℝ) + 3 - θ' : ℝ) : ℂ) * Complex.I / (2 * g)) := by
            rw [hσz, inv_one, Complex.ofReal_one, one_mul]
          have hmem : p.1 ∈ sidePairing g k '' W := by
            refine ⟨z.1, hzW, ?_⟩
            rw [hσz', ← hp]
          exact Or.inr hmem
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hve⟩ := hWsec hvW
      have hρ0 : (0 : ℝ) < ρ := by linarith
      have hσv : sidePairing g k v = ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp
          (Real.pi * ((2 * (k : ℝ) + 3 - θ' : ℝ) : ℂ) * Complex.I / (2 * g)) := by
        rw [hve]
        exact hσE ρ θ' hρ0.ne'
      have hznorm : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have hinv0 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
      have hzρ : ‖z.1‖ = ρ⁻¹ := by
        rw [← hzv, hσv]
        exact hnormE _ _ hinv0.le
      have hcancel : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0.ne'
      have hρge : 1 ≤ ρ := by
        have h2 : ρ⁻¹ ≤ 1 := by
          rw [← hzρ]
          exact hznorm
        nlinarith
      rcases lt_or_eq_of_le hρge with hρgt | hρeq1
      · have hzn : ‖z.1‖ < 1 := by
          rw [hzρ]
          nlinarith
        have hzp' := hsingle z p hzn hrel
        rw [← hzp']
        exact Or.inr ⟨v, hvW, hzv⟩
      · have hz1' : z.1 = Complex.exp
            (Real.pi * ((2 * (k : ℝ) + 3 - θ' : ℝ) : ℂ) * Complex.I / (2 * g)) := by
          rw [← hzv, hσv, ← hρeq1, inv_one, Complex.ofReal_one, one_mul]
        have hcls := hclass (2 * (k : ℝ) + 3 - θ') z p
          (Or.inr ⟨by linarith, by linarith⟩) hz1' hrel
        rcases hcls with hp | hp
        · have hmem : p.1 ∈ sidePairing g k '' W := by
            refine ⟨v, hvW, ?_⟩
            rw [hzv, hz1', hp]
          exact Or.inr hmem
        · have he2 : 2 * (k : ℝ) + 3 - (2 * (k : ℝ) + 3 - θ') = θ' := by ring
          rw [he2] at hp
          have hveq1 : v = Complex.exp (Real.pi * (θ' : ℂ) * Complex.I / (2 * g)) := by
            rw [hve, ← hρeq1, Complex.ofReal_one, one_mul]
          have hmem : p.1 ∈ W := by
            rw [hp, ← hveq1]
            exact hvW
          exact Or.inl hmem
  have hpre : IsOpen (Quotient.mk (genusSetoid g) ⁻¹'
      (Quotient.mk (genusSetoid g) ''
        {z : ClosedDisc | z.1 ∈ W ∪ sidePairing g k '' W})) := by
    rw [hsat]
    exact hAopen.preimage continuous_subtype_val
  exact isOpen_coinduced.mpr hpre

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
  rfl

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
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  unfold vertexRadius
  exact lt_min (by norm_num) (div_pos Real.pi_pos (by linarith))

/-- The compressed corner scale is below the arc scale:
`vertexRadius g ^ (2g) < π/(2g)`. -/
theorem vertexRadius_pow_lt (g : ℕ) [NeZero g] :
    vertexRadius g ^ (2 * g) < Real.pi / (2 * g) := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hg : (0 : ℝ) < g := by exact_mod_cast hg1
  have hpos : 0 < vertexRadius g := vertexRadius_pos g
  have h12 : vertexRadius g ≤ 1 / 2 := min_le_left _ _
  have hpow : vertexRadius g ^ (2 * g) ≤ vertexRadius g :=
    pow_le_of_le_one hpos.le (by linarith) (by omega)
  have hquarter : vertexRadius g ≤ Real.pi / (4 * g) := min_le_right _ _
  have hlt : Real.pi / (4 * g) < Real.pi / (2 * g) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by linarith)
    linarith
  linarith

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
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set θ : ℝ := r ^ (2 * g) with hθ
  have hθ0 : 0 ≤ θ := pow_nonneg hr _
  set w : ℝ := 2 * g * θ / Real.pi with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w < 1 := by
    rw [hw, div_lt_one hπ]
    calc 2 * g * θ < 2 * g * (Real.pi / (2 * g)) := by
          exact mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = Real.pi := by field_simp
  have hwθ : Real.pi * w / (2 * g) = θ := by
    rw [hw]
    field_simp
  have hθC : ((r : ℂ)) ^ (2 * g) = ((θ : ℝ) : ℂ) := by
    rw [hθ]
    push_cast
    ring
  -- Norms: both sides are on the unit circle.
  have hvert : ∀ c : ℤ, ‖polyVertex g c‖ = 1 := by
    intro c
    have hrw : polyVertex g c
        = Complex.exp (((Real.pi * (c : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  set a := vertexSlot g ((m : ℕ) : ZMod (4 * g)) with ha
  set b := vertexSlot g (((m : ℕ) : ZMod (4 * g)) + 1) with hb
  have hnorm1 : ‖polyVertex g ((a.val : ℤ)) *
      Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g)))‖ = 1 := by
    rw [norm_mul, hvert]
    have hre : -(Complex.I * (r : ℂ) ^ (2 * g)) = ((-θ : ℝ) : ℂ) * Complex.I := by
      rw [hθC]
      push_cast
      ring
    rw [hre, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hnorm2 : ‖polyVertex g ((b.val : ℤ)) *
      Complex.exp (Complex.I * (r : ℂ) ^ (2 * g))‖ = 1 := by
    rw [norm_mul, hvert]
    have hre : Complex.I * (r : ℂ) ^ (2 * g) = ((θ : ℝ) : ℂ) * Complex.I := by
      rw [hθC]
      ring
    rw [hre, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hp1 : (projDisc (polyVertex g ((a.val : ℤ)) *
      Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g))))).1
      = polyVertex g ((a.val : ℤ)) * Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g))) :=
    projDisc_eq (le_of_eq hnorm1)
  have hp2 : (projDisc (polyVertex g ((b.val : ℤ)) *
      Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)))).1
      = polyVertex g ((b.val : ℤ)) * Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)) :=
    projDisc_eq (le_of_eq hnorm2)
  -- ZMod plumbing.
  have hcast : ∀ x : ZMod (4 * g), (((x.val : ℤ)) : ZMod (4 * g)) = x := by
    intro x
    rw [Int.cast_natCast]
    exact ZMod.natCast_rightInverse x
  have hpv : ∀ x y : ℤ, ((x : ZMod (4 * g)) = (y : ZMod (4 * g))) →
      polyVertex g x = polyVertex g y := by
    intro x y hxy
    rw [ZMod.intCast_eq_intCast_iff] at hxy
    obtain ⟨j, hj⟩ := Int.ModEq.dvd hxy
    have hjZ : x - y = 4 * (g : ℤ) * (-j) := by push_cast at hj ⊢; linarith
    have hjC : (x : ℂ) - y = 4 * g * (-j : ℤ) := by exact_mod_cast hjZ
    unfold polyVertex
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-j, ?_⟩
    push_cast at hjC ⊢
    field_simp
    linear_combination hjC
  have hsub1val : ∀ x : ZMod (4 * g), x ≠ 0 → (x - 1).val = x.val - 1 := by
    intro x hx
    have hx1 : 1 ≤ x.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hx ((ZMod.val_eq_zero x).mp hc))
    have hxlt : x.val < 4 * g := ZMod.val_lt x
    have hxe : x - 1 = ((x.val - 1 : ℕ) : ZMod (4 * g)) := by
      rw [Nat.cast_sub hx1, Nat.cast_one, ZMod.natCast_rightInverse x]
    rw [hxe, ZMod.val_cast_of_lt (by omega)]
  have hneg1val : (0 - 1 : ZMod (4 * g)).val = 4 * g - 1 := by
    have h1 : (0 - 1 : ZMod (4 * g)) = ((4 * g - 1 : ℕ) : ZMod (4 * g)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self]
    rw [h1, ZMod.val_cast_of_lt (by omega)]
  have hsucc : b = pairInv g (a - 1) := vertexSlot_succ g _
  have hπw : Real.pi * w = 2 * g * θ := by
    rw [hw]
    field_simp
  -- The two component identities, one per sign of the exponent.
  have harcM : ∀ (k : ℤ) (t : ℝ) (c : ℤ), ((k : ℝ) + t) = (c : ℝ) - w →
      arcPoint g k t = polyVertex g c * Complex.exp (-(Complex.I * (r : ℂ) ^ (2 * g))) := by
    intro k t c hkt
    unfold arcPoint polyVertex
    rw [hθC, ← Complex.exp_add]
    congr 1
    have key : Real.pi * ((k : ℝ) + t) = Real.pi * c - 2 * g * θ := by
      rw [hkt]
      linear_combination -hπw
    have keyC : (Real.pi : ℂ) * ((k : ℂ) + t) = (Real.pi : ℂ) * c - 2 * g * θ := by
      exact_mod_cast key
    field_simp
    linear_combination keyC
  have harcP : ∀ (k : ℤ) (t : ℝ) (c : ℤ), ((k : ℝ) + t) = (c : ℝ) + w →
      arcPoint g k t = polyVertex g c * Complex.exp (Complex.I * (r : ℂ) ^ (2 * g)) := by
    intro k t c hkt
    unfold arcPoint polyVertex
    rw [hθC, ← Complex.exp_add]
    congr 1
    have key : Real.pi * ((k : ℝ) + t) = Real.pi * c + 2 * g * θ := by
      rw [hkt]
      linear_combination hπw
    have keyC : (Real.pi : ℂ) * ((k : ℂ) + t) = (Real.pi : ℂ) * c + 2 * g * θ := by
      exact_mod_cast key
    field_simp
    linear_combination keyC
  by_cases hs : (a - 1).val % 4 = 0 ∨ (a - 1).val % 4 = 1
  · -- Source case: `b = a + 1`, pairing arc `k = a.val - 1`.
    have hane : a ≠ 0 := by
      intro ha0
      rw [ha0, hneg1val] at hs
      omega
    have haval : (a - 1).val = a.val - 1 := hsub1val a hane
    have ha1 : 1 ≤ a.val :=
      Nat.one_le_iff_ne_zero.mpr (fun hc => hane ((ZMod.val_eq_zero a).mp hc))
    have hbval : b = a + 1 := by
      rw [hsucc]
      unfold pairInv
      rw [if_pos hs]
      ring
    have hpvb : polyVertex g ((b.val : ℤ)) = polyVertex g ((a.val : ℤ) + 1) := by
      apply hpv
      rw [hcast]
      push_cast
      rw [ZMod.natCast_rightInverse a, hbval]
    refine Or.inr (Or.inl ⟨(a.val : ℤ) - 1, by omega, Or.inl ?_⟩)
    unfold pairGraph
    refine ⟨⟨1 - w, by constructor <;> [linarith; linarith]⟩, Set.mem_univ _, ?_⟩
    rw [Prod.ext_iff]
    constructor
    · change arcPoint g ((a.val : ℤ) - 1) (1 - w) = _
      rw [hp1]
      exact harcM ((a.val : ℤ) - 1) (1 - w) (a.val : ℤ) (by push_cast; ring)
    · change arcPoint g ((a.val : ℤ) - 1 + 2) (1 - (1 - w)) = _
      rw [hp2, hpvb]
      exact harcP ((a.val : ℤ) - 1 + 2) (1 - (1 - w)) ((a.val : ℤ) + 1) (by push_cast; ring)
  · -- Target case: `b = a - 3`, pairing arc `k = a.val - 3`.
    have hbval : b = a - 3 := by
      rw [hsucc]
      unfold pairInv
      rw [if_neg hs]
      ring
    have hmod4 : (((a - 1).val : ℤ)) % 4 = ((a.val : ℤ) - 1) % 4 := by
      by_cases ha0 : a = 0
      · simp only [ha0, hneg1val, ZMod.val_zero]
        omega
      · rw [hsub1val a ha0]
        have ha1 : 1 ≤ a.val :=
          Nat.one_le_iff_ne_zero.mpr (fun hc => ha0 ((ZMod.val_eq_zero a).mp hc))
        omega
    have hs' : ((a.val : ℤ) - 1) % 4 = 2 ∨ ((a.val : ℤ) - 1) % 4 = 3 := by omega
    have hpvb : polyVertex g ((b.val : ℤ)) = polyVertex g ((a.val : ℤ) - 3) := by
      apply hpv
      rw [hcast]
      push_cast
      rw [ZMod.natCast_rightInverse a, hbval]
    refine Or.inr (Or.inl ⟨(a.val : ℤ) - 3, by omega, Or.inr ?_⟩)
    unfold pairGraph
    refine ⟨⟨w, by constructor <;> [linarith; linarith]⟩, Set.mem_univ _, ?_⟩
    rw [Prod.ext_iff]
    constructor
    · change arcPoint g ((a.val : ℤ) - 3) w = _
      rw [hp2, hpvb]
      exact harcP ((a.val : ℤ) - 3) w ((a.val : ℤ) - 3) (by push_cast; ring)
    · change arcPoint g ((a.val : ℤ) - 3 + 2) (1 - w) = _
      rw [hp1]
      exact harcM ((a.val : ℤ) - 3 + 2) (1 - w) (a.val : ℤ) (by push_cast; ring)

/-- Continuity of the vertex chart inverse on the chart disc: `4g` closed
sectors glued along consistent rays, with all formulas tending to the vertex
class at `0`. -/
theorem vertexChart_continuousOn (g : ℕ) [NeZero g] :
    ContinuousOn (vertexChartFun g) (Metric.ball (0 : ℂ) (vertexRadius g)) := by
  classical
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := vertexRadius g with hδdef
  have hδ0 : 0 < δ := vertexRadius_pos g
  have hδp : δ ^ (2 * g) < Real.pi / (2 * g) := vertexRadius_pow_lt g
  set h₀ : ℝ := Real.pi / (2 * g) with hh₀
  have hh0 : 0 < h₀ := by rw [hh₀]; positivity
  have hg1R : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hh2 : h₀ ≤ Real.pi / 2 := by
    rw [hh₀, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
    have h2g : (2 : ℝ) ≤ 2 * g := by linarith
    exact mul_le_mul_of_nonneg_left h2g hπ.le
  have h4gh : (4 * (g : ℝ)) * h₀ = 2 * Real.pi := by
    rw [hh₀]
    field_simp
    norm_num
  -- The unit-circle exponential and the closed sectors.
  set E : ℝ → ℂ := fun x => Complex.exp ((x : ℂ) * Complex.I) with hEdef
  have hE : ∀ x y : ℝ, E x * E y = E (x + y) := by
    intro x y
    simp only [hEdef]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEim : ∀ x : ℝ, (E x).im = Real.sin x := by
    intro x
    simp only [hEdef]
    exact Complex.exp_ofReal_mul_I_im x
  have hSim : ∀ ρ x θ : ℝ, (((ρ : ℂ) * E x) * E (-θ)).im = ρ * Real.sin (x - θ) := by
    intro ρ x θ
    rw [mul_assoc, hE, Complex.im_ofReal_mul, hEim, ← sub_eq_add_neg]
  set S : ℕ → Set ℂ := fun n =>
    {u : ℂ | 0 ≤ (u * E (-((n : ℝ) * h₀))).im ∧ (u * E (-(((n : ℝ) + 1) * h₀))).im ≤ 0}
    with hS
  have hSclosed : ∀ n : ℕ, IsClosed (S n) := by
    intro n
    have h1 : Continuous fun u : ℂ => (u * E (-((n : ℝ) * h₀))).im :=
      Complex.continuous_im.comp (continuous_mul_const _)
    have h2 : Continuous fun u : ℂ => (u * E (-(((n : ℝ) + 1) * h₀))).im :=
      Complex.continuous_im.comp (continuous_mul_const _)
    have hrw : S n = {u : ℂ | 0 ≤ (u * E (-((n : ℝ) * h₀))).im} ∩
        {u : ℂ | (u * E (-(((n : ℝ) + 1) * h₀))).im ≤ 0} := by
      simp only [hS]
      exact Set.setOf_and
    rw [hrw]
    exact (isClosed_le continuous_const h1).inter (isClosed_le h2 continuous_const)
  -- Sector index basics.
  have hsec0 : vertexSectorIndex g (0 : ℂ) = 0 := by
    unfold vertexSectorIndex
    rw [Complex.arg_zero]
    norm_num
  have hpolar : ∀ u : ℂ, u ≠ 0 →
      ∃ α : ℝ, 0 ≤ α ∧ α < 2 * Real.pi ∧ u = (‖u‖ : ℂ) * E α ∧
        (vertexSectorIndex g u : ℝ) * h₀ ≤ α ∧
        α < ((vertexSectorIndex g u : ℝ) + 1) * h₀ ∧ vertexSectorIndex g u < 4 * g := by
    intro u hu
    have harg1 : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
    have harg2 : Complex.arg u ≤ Real.pi := Complex.arg_le_pi u
    set α : ℝ := if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u
      with hα
    have hα0 : 0 ≤ α := by
      rw [hα]
      split_ifs with hc
      · linarith
      · linarith [not_lt.mp hc]
    have hα2 : α < 2 * Real.pi := by
      rw [hα]
      split_ifs with hc
      · linarith
      · linarith
    have hue : u = (‖u‖ : ℂ) * E α := by
      have hbase : u = (‖u‖ : ℂ) * E (Complex.arg u) := by
        simp only [hEdef]
        exact (Complex.norm_mul_exp_arg_mul_I u).symm
      rw [hα]
      split_ifs with hc
      · have h2π : E (2 * Real.pi) = 1 := by
          simp only [hEdef]
          have harg : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg, Complex.exp_two_pi_mul_I]
        calc u = (‖u‖ : ℂ) * E (Complex.arg u) := hbase
          _ = (‖u‖ : ℂ) * (E (Complex.arg u) * E (2 * Real.pi)) := by rw [h2π, mul_one]
          _ = (‖u‖ : ℂ) * E (Complex.arg u + 2 * Real.pi) := by rw [hE]
      · exact hbase
    have hsec : vertexSectorIndex g u = (⌊2 * (g : ℝ) / Real.pi * α⌋).toNat := by
      unfold vertexSectorIndex
      rw [hα]
    set x : ℝ := 2 * (g : ℝ) / Real.pi * α with hx
    have hx0 : 0 ≤ x := by
      rw [hx]
      exact mul_nonneg (by positivity) hα0
    have hfl0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
    have hsecZ : ((vertexSectorIndex g u : ℕ) : ℤ) = ⌊x⌋ := by
      rw [hsec]
      exact Int.toNat_of_nonneg hfl0
    have hle : ((vertexSectorIndex g u : ℝ)) ≤ x := by
      have h1 := Int.floor_le x
      have h2 : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      rw [h2]
      exact h1
    have hlt : x < (vertexSectorIndex g u : ℝ) + 1 := by
      have h1 := Int.lt_floor_add_one x
      have h2 : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      rw [h2]
      exact h1
    have hxα : x * h₀ = α := by
      rw [hx, hh₀]
      field_simp
    have hb1 : (vertexSectorIndex g u : ℝ) * h₀ ≤ α := by
      rw [← hxα]
      exact mul_le_mul_of_nonneg_right hle hh0.le
    have hb2 : α < ((vertexSectorIndex g u : ℝ) + 1) * h₀ := by
      rw [← hxα]
      exact (mul_lt_mul_of_pos_right hlt hh0)
    have hm4 : vertexSectorIndex g u < 4 * g := by
      have hxlt : x < 4 * g := by
        rw [hx]
        calc 2 * (g : ℝ) / Real.pi * α < 2 * g / Real.pi * (2 * Real.pi) := by
              exact mul_lt_mul_of_pos_left hα2 (by positivity)
          _ = 4 * g := by field_simp; ring
      have hflt : ⌊x⌋ < ((4 * g : ℕ) : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hxlt)
      omega
    exact ⟨α, hα0, hα2, hue, hb1, hb2, hm4⟩
  have hcover : ∀ u : ℂ, u ∈ S (vertexSectorIndex g u) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      refine ⟨?_, ?_⟩ <;> simp
    · obtain ⟨α, hα0, hα2, hue, hb1, hb2, hm4⟩ := hpolar u hu
      set msec := vertexSectorIndex g u with hmsecdef
      refine ⟨?_, ?_⟩
      · rw [hue, hSim]
        apply mul_nonneg (norm_nonneg u)
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith
        · linarith [hh2, hπ]
      · rw [hue, hSim]
        have hsin : Real.sin (α - ((msec : ℝ) + 1) * h₀) ≤ 0 := by
          have hneg : 0 ≤ Real.sin (-(α - ((msec : ℝ) + 1) * h₀)) := by
            apply Real.sin_nonneg_of_nonneg_of_le_pi
            · linarith
            · linarith [hh2, hπ]
          rw [Real.sin_neg] at hneg
          linarith
        have hp := mul_nonneg (norm_nonneg u) (neg_nonneg.mpr hsin)
        linarith [hp]
  -- Interval extraction from the sign of sin.
  have hsinA : ∀ x : ℝ, -(2 * Real.pi) < x → x < 2 * Real.pi → 0 ≤ Real.sin x →
      (0 ≤ x ∧ x ≤ Real.pi) ∨ x ≤ -Real.pi := by
    intro x hx1 hx2 hs
    rcases le_or_gt x (-Real.pi) with hc | hc
    · exact Or.inr hc
    rcases lt_or_ge x 0 with h0 | h0
    · exact absurd hs (not_le.mpr (Real.sin_neg_of_neg_of_neg_pi_lt h0 hc))
    rcases le_or_gt x Real.pi with h1 | h1
    · exact Or.inl ⟨h0, h1⟩
    exfalso
    have h2 : 0 < Real.sin (x - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h2
    linarith
  have hsinB : ∀ y : ℝ, -(2 * Real.pi) - Real.pi / 2 < y → y < 2 * Real.pi →
      Real.sin y ≤ 0 → (-Real.pi ≤ y ∧ y ≤ 0) ∨ Real.pi ≤ y ∨ y ≤ -(2 * Real.pi) := by
    intro y hy1 hy2 hs
    rcases le_or_gt y 0 with h0 | h0
    · rcases le_or_gt (-Real.pi) y with h1 | h1
      · exact Or.inl ⟨h1, h0⟩
      rcases le_or_gt y (-(2 * Real.pi)) with h2 | h2
      · exact Or.inr (Or.inr h2)
      exfalso
      have h3 : 0 < Real.sin (y + 2 * Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_add_two_pi] at h3
      linarith
    rcases le_or_gt Real.pi y with h1 | h1
    · exact Or.inr (Or.inl h1)
    exact absurd hs (not_le.mpr (Real.sin_pos_of_pos_of_lt_pi h0 h1))
  have hchar : ∀ n : ℕ, n < 4 * g → ∀ u : ℂ, u ≠ 0 → u ∈ S n → ∀ α : ℝ,
      0 ≤ α → α < 2 * Real.pi → u = (‖u‖ : ℂ) * E α →
      ((n : ℝ) * h₀ ≤ α ∧ α ≤ ((n : ℝ) + 1) * h₀) ∨ (α = 0 ∧ n = 4 * g - 1) := by
    intro n hn u hu hmem α hα0 hα2 hue
    have hr0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    obtain ⟨hm1, hm2⟩ := hmem
    rw [hue, hSim] at hm1 hm2
    have hs1 : 0 ≤ Real.sin (α - (n : ℝ) * h₀) := (mul_nonneg_iff_of_pos_left hr0).mp hm1
    have hs2 : Real.sin (α - ((n : ℝ) + 1) * h₀) ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := mul_pos hr0 hcon
      linarith
    have hn' : (n : ℝ) < 4 * g := by exact_mod_cast hn
    have hnh0 : 0 ≤ (n : ℝ) * h₀ := mul_nonneg (Nat.cast_nonneg n) hh0.le
    have hnh : (n : ℝ) * h₀ < 2 * Real.pi := by
      have := mul_lt_mul_of_pos_right hn' hh0
      linarith
    have hx1 : -(2 * Real.pi) < α - (n : ℝ) * h₀ := by linarith
    have hx2 : α - (n : ℝ) * h₀ < 2 * Real.pi := by linarith
    have hy1 : -(2 * Real.pi) - Real.pi / 2 < α - ((n : ℝ) + 1) * h₀ := by linarith
    have hy2 : α - ((n : ℝ) + 1) * h₀ < 2 * Real.pi := by linarith
    rcases hsinA _ hx1 hx2 hs1 with ⟨hA1, hA2⟩ | hA
    · rcases hsinB _ hy1 hy2 hs2 with ⟨hB1, hB2⟩ | hB | hB
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exfalso; linarith
      · exfalso; linarith [hh2, hπ]
    · rcases hsinB _ hy1 hy2 hs2 with ⟨hB1, hB2⟩ | hB | hB
      · exfalso; linarith
      · exfalso; linarith
      · have hle' : ((n : ℝ) + 1) ≤ 4 * g := by exact_mod_cast hn
        have hn1 : ((n : ℝ) + 1) * h₀ ≤ 4 * g * h₀ :=
          mul_le_mul_of_nonneg_right hle' hh0.le
        have hα0' : α = 0 := le_antisymm (by linarith) hα0
        have hnge : 4 * g ≤ n + 1 := by
          by_contra hcon
          push Not at hcon
          have hlt' : ((n : ℝ) + 1) < 4 * g := by exact_mod_cast hcon
          have := mul_lt_mul_of_pos_right hlt' hh0
          linarith
        exact Or.inr ⟨hα0', by omega⟩
  -- The per-sector continuous formulas.
  set F : ℕ → ℂ → GenusSurface g := fun n u =>
    Quotient.mk (genusSetoid g)
      (projDisc (polyVertex g ((vertexSlot g (n : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ n * u ^ (2 * g)))) with hF
  have hfF : ∀ u : ℂ, vertexChartFun g u = F (vertexSectorIndex g u) u := by
    intro u
    rw [hF]
    rfl
  have hFc : ∀ n : ℕ, Continuous (F n) := by
    intro n
    rw [hF]
    have h1 : Continuous fun u : ℂ => Complex.I * (-1) ^ n * u ^ (2 * g) :=
      continuous_const.mul (continuous_pow (2 * g))
    have h2 : Continuous fun u : ℂ =>
        polyVertex g ((vertexSlot g (n : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ n * u ^ (2 * g)) :=
      continuous_const.mul (Complex.continuous_exp.comp h1)
    exact continuous_quot_mk.comp (continuous_projDisc.comp h2)
  have hvert : ∀ c : ℤ, ‖polyVertex g c‖ = 1 := by
    intro c
    have hrw : polyVertex g c
        = Complex.exp (((Real.pi * (c : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  -- The glue across shared rays, in quotient form.
  have hglue : ∀ n : ℕ, ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ →
      (Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g (n : ZMod (4 * g))).val : ℤ) *
          Complex.exp (-(Complex.I * (ρ : ℂ) ^ (2 * g))))) : GenusSurface g) =
      Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g ((n : ZMod (4 * g)) + 1)).val : ℤ) *
          Complex.exp (Complex.I * (ρ : ℂ) ^ (2 * g)))) := by
    intro n ρ hρ0 hρδ
    apply Quotient.sound
    apply vertexRay_glue g n hρ0
    calc ρ ^ (2 * g) ≤ δ ^ (2 * g) :=
          pow_le_pow_left₀ hρ0 hρδ.le (2 * g)
      _ < Real.pi / (2 * g) := hδp
  -- The function agrees with the fixed-sector formula on each closed sector.
  have hEqOn : ∀ n : ℕ, n < 4 * g → ∀ u : ℂ, u ∈ S n → u ∈ Metric.ball (0 : ℂ) δ →
      vertexChartFun g u = F n u := by
    intro n hn u hmem hball
    by_cases hu : u = 0
    · subst hu
      rw [hfF 0, hsec0]
      have hzero : ∀ k : ℕ, F k 0 = Quotient.mk (genusSetoid g)
          (projDisc (polyVertex g ((vertexSlot g (k : ZMod (4 * g))).val : ℤ))) := by
        intro k
        rw [hF]
        simp only []
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
      rw [hzero 0, hzero n]
      apply Quotient.sound
      refine Or.inr (Or.inr ⟨?_, ?_⟩) <;>
        · rw [projDisc_eq (le_of_eq (hvert _))]
          exact ⟨_, rfl⟩
    · obtain ⟨α, hα0, hα2, hue, hb1, hb2, hm4⟩ := hpolar u hu
      rcases hchar n hn u hu hmem α hα0 hα2 hue with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · -- interior-or-shared-ray case
        have hnm1 : n ≤ vertexSectorIndex g u := by
          by_contra hcon
          push Not at hcon
          have hle' : (vertexSectorIndex g u : ℝ) + 1 ≤ (n : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hcon
          have := mul_le_mul_of_nonneg_right hle' hh0.le
          linarith
        have hnm2 : vertexSectorIndex g u ≤ n + 1 := by
          by_contra hcon
          push Not at hcon
          have hle' : (n : ℝ) + 2 ≤ (vertexSectorIndex g u : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hcon
          have := mul_le_mul_of_nonneg_right hle' hh0.le
          linarith
        rcases Nat.eq_or_lt_of_le hnm1 with heq | hlt
        · rw [hfF u, ← heq]
        · have hmeq : vertexSectorIndex g u = n + 1 := by omega
          have hαeq : α = ((n : ℝ) + 1) * h₀ := by
            rw [hmeq] at hb1
            push_cast at hb1
            linarith
          have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
          have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hball
          have hupow : u ^ (2 * g) = ((‖u‖ : ℂ)) ^ (2 * g) * (-1) ^ (n + 1) := by
            have h1 : u ^ (2 * g) = ((‖u‖ : ℂ)) ^ (2 * g) * (E α) ^ (2 * g) := by
              rw [← mul_pow]
              exact congrArg (fun z : ℂ => z ^ (2 * g)) hue
            rw [h1, hαeq]
            congr 1
            simp only [hEdef]
            rw [← Complex.exp_nat_mul]
            have hexp : ((2 * g : ℕ) : ℂ) * (((((n : ℝ) + 1) * h₀ : ℝ) : ℂ) * Complex.I)
                = ((n + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
              rw [hh₀]
              push_cast
              have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
              field_simp
            rw [hexp, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
          have hodd : ((-1 : ℂ)) ^ n * (-1) ^ (n + 1) = -1 := by
            rw [← pow_add]
            exact Odd.neg_one_pow ⟨n, by ring⟩
          have heven : ((-1 : ℂ)) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
            rw [← pow_add]
            exact Even.neg_one_pow ⟨n + 1, by ring⟩
          have idA : Complex.I * (-1) ^ n * u ^ (2 * g)
              = -(Complex.I * (‖u‖ : ℂ) ^ (2 * g)) := by
            rw [hupow]
            calc Complex.I * (-1) ^ n * ((‖u‖ : ℂ) ^ (2 * g) * (-1) ^ (n + 1))
                = Complex.I * (‖u‖ : ℂ) ^ (2 * g) * ((-1) ^ n * (-1) ^ (n + 1)) := by ring
              _ = -(Complex.I * (‖u‖ : ℂ) ^ (2 * g)) := by rw [hodd]; ring
          have idB : Complex.I * (-1) ^ (n + 1) * u ^ (2 * g)
              = Complex.I * (‖u‖ : ℂ) ^ (2 * g) := by
            rw [hupow]
            calc Complex.I * (-1) ^ (n + 1) * ((‖u‖ : ℂ) ^ (2 * g) * (-1) ^ (n + 1))
                = Complex.I * (‖u‖ : ℂ) ^ (2 * g) * ((-1) ^ (n + 1) * (-1) ^ (n + 1)) := by
                  ring
              _ = Complex.I * (‖u‖ : ℂ) ^ (2 * g) := by rw [heven]; ring
          have hslot : ((n + 1 : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1 := by
            push_cast
            ring
          rw [hfF u, hmeq, hF]
          simp only []
          rw [idA, idB, hslot]
          exact (hglue n ‖u‖ hρ0 hρδ).symm
      · -- wrap-around case: `α = 0`, `n = 4g - 1`.
        have hmsec0 : vertexSectorIndex g u = 0 := by
          by_contra hcon
          have h1 : (1 : ℝ) ≤ (vertexSectorIndex g u : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcon
          have h2 := mul_le_mul_of_nonneg_right h1 hh0.le
          rw [hc1] at hb1
          linarith
        have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
        have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hball
        have hE0 : E 0 = 1 := by
          simp only [hEdef]
          norm_num
        have hueρ : u = ((‖u‖ : ℝ) : ℂ) := by
          calc u = (‖u‖ : ℂ) * E α := hue
            _ = (‖u‖ : ℂ) * E 0 := by rw [hc1]
            _ = (‖u‖ : ℂ) := by rw [hE0, mul_one]
        have hupow : u ^ (2 * g) = ((‖u‖ : ℂ)) ^ (2 * g) :=
          congrArg (fun z : ℂ => z ^ (2 * g)) hueρ
        have idB : Complex.I * (-1) ^ (0 : ℕ) * u ^ (2 * g)
            = Complex.I * (‖u‖ : ℂ) ^ (2 * g) := by
          rw [hupow, pow_zero, mul_one]
        have idA : Complex.I * (-1) ^ (4 * g - 1) * u ^ (2 * g)
            = -(Complex.I * (‖u‖ : ℂ) ^ (2 * g)) := by
          rw [hupow]
          have hodd : ((-1 : ℂ)) ^ (4 * g - 1) = -1 :=
            Odd.neg_one_pow ⟨2 * g - 1, by omega⟩
          rw [hodd]
          ring
        have hslot : ((0 : ℕ) : ZMod (4 * g)) = (((4 * g - 1 : ℕ)) : ZMod (4 * g)) + 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 4 * g), Nat.cast_one, ZMod.natCast_self,
            Nat.cast_zero]
          ring
        rw [hfF u, hmsec0, hc2, hF]
        simp only []
        rw [idA, idB, hslot]
        exact (hglue (4 * g - 1) ‖u‖ hρ0 hρδ).symm
  -- Assembly: pasting over the finitely many closed sectors through the point.
  intro u₀ hu₀
  have hunionT : ∀ t : Finset ℕ,
      (∀ n ∈ t, ContinuousWithinAt (vertexChartFun g) (S n ∩ Metric.ball 0 δ) u₀) →
      ContinuousWithinAt (vertexChartFun g) (⋃ n ∈ t, S n ∩ Metric.ball 0 δ) u₀ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hempty : (⋃ n ∈ (∅ : Finset ℕ), S n ∩ Metric.ball 0 δ) = (∅ : Set ℂ) := by
        simp
      rw [hempty]
      change Filter.Tendsto _ _ _
      rw [nhdsWithin_empty]
      exact tendsto_bot
    | insert a s ha ih =>
      intro hall
      rw [Finset.set_biUnion_insert]
      exact (hall a (Finset.mem_insert_self a s)).union
        (ih fun n hn => hall n (Finset.mem_insert_of_mem hn))
  set Bad : Finset ℕ := (Finset.range (4 * g)).filter (fun n => u₀ ∉ S n) with hBad
  set V : Set ℂ := Metric.ball (0 : ℂ) δ ∩ ⋂ n ∈ Bad, (S n)ᶜ with hV
  have hVopen : IsOpen V := by
    rw [hV]
    apply IsOpen.inter isOpen_ball
    apply isOpen_biInter_finset
    intro n _
    exact (hSclosed n).isOpen_compl
  have hu₀V : u₀ ∈ V := by
    rw [hV]
    refine ⟨hu₀, ?_⟩
    apply Set.mem_iInter₂.mpr
    intro n hn
    rw [hBad, Finset.mem_filter] at hn
    exact hn.2
  set Good : Finset ℕ := (Finset.range (4 * g)).filter (fun n => u₀ ∈ S n) with hGood
  have hVsub : V ⊆ ⋃ n ∈ Good, S n ∩ Metric.ball 0 δ := by
    intro u hu
    rw [hV] at hu
    have hsub4 : vertexSectorIndex g u < 4 * g := by
      by_cases hu0 : u = 0
      · rw [hu0, hsec0]
        omega
      · exact (hpolar u hu0).choose_spec.2.2.2.2.2
    have hgood : vertexSectorIndex g u ∈ Good := by
      rw [hGood, Finset.mem_filter, Finset.mem_range]
      refine ⟨hsub4, ?_⟩
      by_contra hcon
      have hbad : vertexSectorIndex g u ∈ Bad := by
        rw [hBad, Finset.mem_filter, Finset.mem_range]
        exact ⟨hsub4, hcon⟩
      have hcompl := Set.mem_iInter₂.mp hu.2
      exact (hcompl _ hbad) (hcover u)
    exact Set.mem_biUnion hgood ⟨hcover u, hu.1⟩
  have hpiece : ∀ n ∈ Good, ContinuousWithinAt (vertexChartFun g)
      (S n ∩ Metric.ball 0 δ) u₀ := by
    intro n hnG
    rw [hGood, Finset.mem_filter, Finset.mem_range] at hnG
    have hcw : ContinuousWithinAt (F n) (S n ∩ Metric.ball 0 δ) u₀ :=
      (hFc n).continuousAt.continuousWithinAt
    apply hcw.congr
    · intro y hy
      exact hEqOn n hnG.1 y hy.1 hy.2
    · exact hEqOn n hnG.1 u₀ hnG.2 hu₀
  have hCW : ContinuousWithinAt (vertexChartFun g) V u₀ :=
    (hunionT Good hpiece).mono hVsub
  exact (hCW.continuousAt (hVopen.mem_nhds hu₀V)).continuousWithinAt

/-- Injectivity of the vertex chart inverse on the chart disc: same-sector
collisions force `u^(2g) = u'^(2g)` within one closed angular sector, and
cross-sector collisions occur only on the shared rays, where the formulas
agree; uses injectivity of the slot map. -/
theorem vertexChart_injOn (g : ℕ) [NeZero g] :
    Set.InjOn (vertexChartFun g) (Metric.ball (0 : ℂ) (vertexRadius g)) := by
  classical
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hg1R : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := vertexRadius g with hδdef
  have hδ0 : 0 < δ := vertexRadius_pos g
  set h₀ : ℝ := Real.pi / (2 * g) with hh₀
  have hh0 : 0 < h₀ := by rw [hh₀]; positivity
  have h4gh : (4 * (g : ℝ)) * h₀ = 2 * Real.pi := by
    rw [hh₀]
    field_simp
    norm_num
  -- `δ ^ (2g) ≤ h₀ / 4`.
  have hδ8 : δ ^ (2 * g) ≤ h₀ / 4 := by
    have h12 : δ ≤ 1 / 2 := min_le_left _ _
    have hq : δ ≤ Real.pi / (4 * g) := min_le_right _ _
    have h2 : δ ^ (2 * g) ≤ δ ^ 2 :=
      pow_le_pow_of_le_one hδ0.le (by linarith) (by omega)
    have h3 : δ ^ 2 ≤ (1 / 2) * (Real.pi / (4 * g)) := by
      rw [sq]
      exact mul_le_mul h12 hq hδ0.le (by norm_num)
    have h4 : (1 / 2) * (Real.pi / (4 * g)) = h₀ / 4 := by
      rw [hh₀]
      field_simp
    linarith
  -- Angle extraction from equality of unit exponentials.
  have hexpI : ∀ Z₁ Z₂ : ℂ, Complex.exp (Complex.I * Z₁) = Complex.exp (Complex.I * Z₂) →
      ∃ n : ℤ, Z₁ = Z₂ + 2 * Real.pi * n := by
    intro Z₁ Z₂ hZ
    rw [Complex.exp_eq_exp_iff_exists_int] at hZ
    obtain ⟨n, hn⟩ := hZ
    refine ⟨n, ?_⟩
    have h2 : Complex.I * Z₁ = Complex.I * (Z₂ + 2 * Real.pi * n) := by
      rw [hn]
      ring
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hkey : ∀ x₁ y₁ x₂ y₂ : ℝ,
      Complex.exp (Complex.I * (((x₁ : ℝ) : ℂ) + ((y₁ : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * (((x₂ : ℝ) : ℂ) + ((y₂ : ℝ) : ℂ) * Complex.I)) →
      ∃ n : ℤ, x₁ = x₂ + 2 * Real.pi * n ∧ y₁ = y₂ := by
    intro x₁ y₁ x₂ y₂ hx
    obtain ⟨n, hn⟩ := hexpI _ _ hx
    refine ⟨n, ?_, ?_⟩
    · have := congrArg Complex.re hn
      simpa using this
    · have := congrArg Complex.im hn
      simpa using this
  -- Exponential forms of vertices and arc points.
  have hpv2 : ∀ p : ℤ, polyVertex g p =
      Complex.exp (Complex.I * (((h₀ * (p : ℝ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro p
    unfold polyVertex
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
    field_simp
  have harc2 : ∀ (k : ℤ) (t : ℝ), arcPoint g k t =
      Complex.exp (Complex.I * (((h₀ * ((k : ℝ) + t) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro k t
    unfold arcPoint
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
    field_simp
  have hnormz : ∀ x y : ℝ,
      ‖Complex.exp (Complex.I * (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        = Real.exp (-y) := by
    intro x y
    rw [Complex.norm_exp]
    congr 1
    simp
  have hsec0 : vertexSectorIndex g (0 : ℂ) = 0 := by
    unfold vertexSectorIndex
    rw [Complex.arg_zero]
    norm_num
  have hvert : ∀ c : ℤ, ‖polyVertex g c‖ = 1 := by
    intro c
    have hrw : polyVertex g c
        = Complex.exp (((Real.pi * (c : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  -- Normal form of the chart formula at any point of the chart disc.
  have hsetup : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
      ∃ (α φ W : ℝ) (c : ℤ),
        c = ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) ∧
        (0 ≤ c ∧ c < 4 * g) ∧ vertexSectorIndex g u < 4 * g ∧
        u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) ∧
        W = ‖u‖ ^ (2 * g) ∧ (0 ≤ W ∧ W < h₀ / 4) ∧
        (0 ≤ φ ∧ φ < Real.pi) ∧
        φ = 2 * g * α - (vertexSectorIndex g u : ℝ) * Real.pi ∧
        polyVertex g c * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))
          = Complex.exp (Complex.I * (((h₀ * (c : ℝ) + W * Real.cos φ : ℝ) : ℂ) +
              ((W * Real.sin φ : ℝ) : ℂ) * Complex.I)) ∧
        ‖polyVertex g c *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))‖ ≤ 1 ∧
        (W = 0 → u = 0) := by
    intro u hu
    have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hu
    have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
    have hWlt : ‖u‖ ^ (2 * g) < h₀ / 4 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ hρδ hρ0 (by omega)) hδ8
    have hW0 : (0 : ℝ) ≤ ‖u‖ ^ (2 * g) := pow_nonneg hρ0 _
    have hcval : (0 : ℤ) ≤ ((vertexSlot g ((vertexSectorIndex g u : ℕ) :
        ZMod (4 * g))).val : ℤ) ∧
        ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) < 4 * g := by
      constructor
      · positivity
      · exact_mod_cast ZMod.val_lt _
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨0, 0, ‖(0 : ℂ)‖ ^ (2 * g), _, rfl, hcval, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsec0]
        omega
      · simp
      · exact ⟨hW0, hWlt⟩
      · exact ⟨le_refl 0, hπ⟩
      · rw [hsec0]
        push_cast
        ring
      · rw [hsec0, norm_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
        rw [hpv2]
        norm_num
        simp [zero_pow (show 2 * g ≠ 0 by omega)]
      · rw [hsec0]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
        rw [hvert]
      · intro _
        rfl
    · -- polar decomposition
      have harg1 : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
      have harg2 : Complex.arg u ≤ Real.pi := Complex.arg_le_pi u
      set α : ℝ := if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u
        with hα
      have hα0 : 0 ≤ α := by
        rw [hα]
        split_ifs with hc
        · linarith
        · linarith [not_lt.mp hc]
      have hα2 : α < 2 * Real.pi := by
        rw [hα]
        split_ifs with hc
        · linarith
        · linarith
      have hue : u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) := by
        have hbase : u = (‖u‖ : ℂ) * Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) :=
          (Complex.norm_mul_exp_arg_mul_I u).symm
        rw [hα]
        split_ifs with hc
        · have h2π : Complex.exp (((Complex.arg u + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
              = Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.exp_eq_exp_iff_exists_int]
            refine ⟨1, ?_⟩
            push_cast
            ring
          rw [h2π]
          exact hbase
        · exact hbase
      have hsec : vertexSectorIndex g u = (⌊2 * (g : ℝ) / Real.pi * α⌋).toNat := by
        unfold vertexSectorIndex
        rw [hα]
      set x : ℝ := 2 * (g : ℝ) / Real.pi * α with hx
      have hx0 : 0 ≤ x := by
        rw [hx]
        exact mul_nonneg (by positivity) hα0
      have hfl0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
      have hsecZ : ((vertexSectorIndex g u : ℕ) : ℤ) = ⌊x⌋ := by
        rw [hsec]
        exact Int.toNat_of_nonneg hfl0
      have hsecR : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      have hle : ((vertexSectorIndex g u : ℝ)) ≤ x := by
        rw [hsecR]
        exact Int.floor_le x
      have hlt : x < (vertexSectorIndex g u : ℝ) + 1 := by
        rw [hsecR]
        exact Int.lt_floor_add_one x
      have hm4 : vertexSectorIndex g u < 4 * g := by
        have hxlt : x < 4 * g := by
          rw [hx]
          calc 2 * (g : ℝ) / Real.pi * α < 2 * g / Real.pi * (2 * Real.pi) := by
                exact mul_lt_mul_of_pos_left hα2 (by positivity)
            _ = 4 * g := by field_simp; ring
        have hflt : ⌊x⌋ < ((4 * g : ℕ) : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hxlt)
        omega
      have hπx : Real.pi * x = 2 * g * α := by
        rw [hx]
        field_simp
      set m : ℕ := vertexSectorIndex g u with hm
      set φ : ℝ := 2 * g * α - (m : ℝ) * Real.pi with hφ
      have hφx : φ = Real.pi * (x - (m : ℝ)) := by
        rw [hφ, ← hπx]
        ring
      have hφ0 : 0 ≤ φ := by
        rw [hφx]
        exact mul_nonneg hπ.le (by linarith)
      have hφπ : φ < Real.pi := by
        rw [hφx]
        calc Real.pi * (x - (m : ℝ)) < Real.pi * 1 :=
              mul_lt_mul_of_pos_left (by linarith) hπ
          _ = Real.pi := mul_one _
      -- the exponential identity
      have hIarg : Complex.I * (-1) ^ m * u ^ (2 * g)
          = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
              (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
        have hupow : u ^ (2 * g)
            = ((‖u‖ ^ (2 * g) : ℝ) : ℂ) * Complex.exp (((2 * g * α : ℝ) : ℂ) * Complex.I) := by
          have h1 : u ^ (2 * g)
              = ((‖u‖ : ℂ)) ^ (2 * g) * Complex.exp ((α : ℂ) * Complex.I) ^ (2 * g) := by
            rw [← mul_pow]
            exact congrArg (fun z : ℂ => z ^ (2 * g)) hue
          rw [h1, ← Complex.exp_nat_mul]
          congr 1
          · push_cast
            ring
          · congr 1
            push_cast
            ring
        have hsplit : Complex.exp (((2 * g * α : ℝ) : ℂ) * Complex.I)
            = (-1) ^ m * Complex.exp (((φ : ℝ) : ℂ) * Complex.I) := by
          have h2 : (2 * g * α : ℝ) = (m : ℝ) * Real.pi + φ := by
            rw [hφ]
            ring
          rw [h2]
          have h3 : ((((m : ℝ) * Real.pi + φ : ℝ)) : ℂ) * Complex.I
              = ((m : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) + ((φ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [h3, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
        have hcs : Complex.exp (((φ : ℝ) : ℂ) * Complex.I)
            = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
          rw [Complex.exp_mul_I]
          rw [Complex.ofReal_cos, Complex.ofReal_sin]
        have hm2 : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
          rw [← pow_add]
          exact Even.neg_one_pow ⟨m, by ring⟩
        calc Complex.I * (-1) ^ m * u ^ (2 * g)
            = Complex.I * (-1) ^ m * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                ((-1) ^ m * (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I))) := by
              rw [hupow, hsplit, hcs]
          _ = Complex.I * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I)) *
                ((-1) ^ m * (-1) ^ m) := by ring
          _ = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
                (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
              rw [hm2]
              push_cast
              ring
      have hzid : polyVertex g ((vertexSlot g ((m : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ m * u ^ (2 * g))
          = Complex.exp (Complex.I *
              (((h₀ * (((vertexSlot g ((m : ℕ) : ZMod (4 * g))).val : ℤ) : ℝ) +
                ‖u‖ ^ (2 * g) * Real.cos φ : ℝ) : ℂ) +
              ((‖u‖ ^ (2 * g) * Real.sin φ : ℝ) : ℂ) * Complex.I)) := by
        rw [hpv2, hIarg, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      refine ⟨α, φ, ‖u‖ ^ (2 * g), _, rfl, hcval, hm4, hue, rfl, ⟨hW0, hWlt⟩, ⟨hφ0, hφπ⟩,
        rfl, hzid, ?_, ?_⟩
      · rw [hzid, hnormz]
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ‖u‖ ^ (2 * g) * Real.sin φ :=
          mul_nonneg hW0 (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ.le)
        linarith
      · intro hWz
        exact norm_eq_zero.mp ((pow_eq_zero_iff (by omega : 2 * g ≠ 0)).mp hWz)
  -- pinning and collapse helpers
  have hcollapse : ∀ W₁ φ₁ : ℝ, 0 ≤ φ₁ → φ₁ < Real.pi → W₁ * Real.sin φ₁ = 0 →
      W₁ * Real.cos φ₁ = W₁ := by
    intro W₁ φ₁ h0 hπ₁ hs
    rcases mul_eq_zero.mp hs with hW | hsin
    · rw [hW, zero_mul]
    · have hφz : φ₁ = 0 := by
        by_contra hne
        have hpos : 0 < Real.sin φ₁ :=
          Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne h0 (Ne.symm hne)) hπ₁
        rw [hsin] at hpos
        exact absurd hpos (lt_irrefl 0)
      rw [hφz, Real.cos_zero, mul_one]
  have hWpin : ∀ (W₁ : ℝ) (e : ℤ) (s : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 → 0 ≤ s → s ≤ 1 →
      W₁ = h₀ * (s - (e : ℝ)) → (e = 0 ∧ W₁ = h₀ * s) ∨ (s = 1 ∧ W₁ = 0) := by
    intro W₁ e s hW1 hW2 hs0 hs1 hWe
    have hse0 : 0 ≤ s - (e : ℝ) := by
      by_contra hcon
      push Not at hcon
      have : h₀ * (s - (e : ℝ)) < 0 := mul_neg_of_pos_of_neg hh0 hcon
      linarith
    have hse1 : s - (e : ℝ) < 1 / 4 := by
      by_contra hcon
      push Not at hcon
      have : h₀ * (1 / 4) ≤ h₀ * (s - (e : ℝ)) := mul_le_mul_of_nonneg_left hcon hh0.le
      have h4 : h₀ * (1 / 4) = h₀ / 4 := by ring
      linarith
    have he1 : ((e : ℝ)) < 2 := by linarith
    have he2 : (-1 : ℝ) < ((e : ℝ)) := by linarith
    have hei : e < 2 ∧ -1 < e := ⟨by exact_mod_cast he1, by exact_mod_cast he2⟩
    have : e = 0 ∨ e = 1 := by omega
    rcases this with he | he
    · left
      refine ⟨he, ?_⟩
      rw [hWe, he]
      norm_num
    · right
      have hs1' : s = 1 := by
        rw [he] at hse0
        push_cast at hse0
        linarith
      refine ⟨hs1', ?_⟩
      rw [hWe, he, hs1']
      norm_num
  have hslotinj : ∀ m m' : ℕ, m < 4 * g → m' < 4 * g →
      (vertexSlot g ((m : ℕ) : ZMod (4 * g))).val
        = (vertexSlot g ((m' : ℕ) : ZMod (4 * g))).val → m = m' := by
    intro m m' hm hm' hval
    have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = vertexSlot g ((m' : ℕ) : ZMod (4 * g)) :=
      ZMod.val_injective _ hval
    have h2 : ((m : ℕ) : ZMod (4 * g)) = ((m' : ℕ) : ZMod (4 * g)) :=
      (vertexSlot_bijective g).injective h1
    have h3 := congrArg ZMod.val h2
    rwa [ZMod.val_cast_of_lt hm, ZMod.val_cast_of_lt hm'] at h3
  -- Main argument.
  intro u hu u' hu' heqf
  obtain ⟨α, φ, W, c, hcdef, ⟨hc0, hc4⟩, hm4, hue, hWdef, ⟨hW0, hWlt⟩, ⟨hφ0, hφπ⟩,
    hφdef, hz, hn1, hzero⟩ := hsetup u hu
  obtain ⟨α', φ', W', c', hcdef', ⟨hc0', hc4'⟩, hm4', hue', hWdef', ⟨hW0', hWlt'⟩,
    ⟨hφ0', hφπ'⟩, hφdef', hz', hn1', hzero'⟩ := hsetup u' hu'
  have hrel : genusRel g
      (projDisc (polyVertex g
          ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))))
      (projDisc (polyVertex g
          ((vertexSlot g ((vertexSectorIndex g u' : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)))) :=
    Quotient.exact heqf
  rw [← hcdef, ← hcdef'] at hrel
  have hpd : (projDisc (polyVertex g c *
      Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g)))).1
      = polyVertex g c *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g)) :=
    projDisc_eq hn1
  have hpd' : (projDisc (polyVertex g c' *
      Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)))).1
      = polyVertex g c' *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)) :=
    projDisc_eq hn1'
  -- endgame from matched data
  have hfinish : W = W' → φ = φ' → c = c' → u = u' := by
    intro hWeq hφeq hceq
    by_cases hWz : W = 0
    · rw [hzero hWz, hzero' (by rw [← hWeq]; exact hWz)]
    · have hmm : vertexSectorIndex g u = vertexSectorIndex g u' := by
        apply hslotinj _ _ hm4 hm4'
        have h1 : ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ)
            = ((vertexSlot g ((vertexSectorIndex g u' : ℕ) : ZMod (4 * g))).val : ℤ) := by
          rw [← hcdef, ← hcdef', hceq]
        exact_mod_cast h1
      have hαeq : α = α' := by
        have h2 : 2 * (g : ℝ) * α = 2 * g * α' := by
          have e1 : φ = 2 * g * α - (vertexSectorIndex g u : ℝ) * Real.pi := hφdef
          have e2 : φ' = 2 * g * α' - (vertexSectorIndex g u' : ℝ) * Real.pi := hφdef'
          have e3 : ((vertexSectorIndex g u : ℕ) : ℝ)
              = ((vertexSectorIndex g u' : ℕ) : ℝ) := by
            exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hmm
          rw [e1, e2, e3] at hφeq
          linarith
        have h2g0 : (2 * (g : ℝ)) ≠ 0 := by positivity
        have h3 : 2 * (g : ℝ) * α = 2 * (g : ℝ) * α' := by linarith
        exact mul_left_cancel₀ h2g0 h3
      have hρeq : ‖u‖ = ‖u'‖ := by
        have hpow : ‖u‖ ^ (2 * g) = ‖u'‖ ^ (2 * g) := by
          rw [← hWdef, ← hWdef', hWeq]
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := pow_lt_pow_left₀ hlt (norm_nonneg u) (by omega : 2 * g ≠ 0)
          linarith
        · have := pow_lt_pow_left₀ hlt (norm_nonneg u') (by omega : 2 * g ≠ 0)
          linarith
      rw [hue, hue', hρeq, hαeq]
  -- shared pairing analysis
  have hpaircase : ∀ (c₁ c₂ : ℤ) (W₁ W₂ φ₁ φ₂ : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 →
      0 ≤ W₂ → W₂ < h₀ / 4 → 0 ≤ φ₁ → φ₁ < Real.pi → 0 ≤ φ₂ → φ₂ < Real.pi →
      ∀ (k : ℤ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      arcPoint g k t = Complex.exp (Complex.I *
        (((h₀ * (c₁ : ℝ) + W₁ * Real.cos φ₁ : ℝ) : ℂ) +
          ((W₁ * Real.sin φ₁ : ℝ) : ℂ) * Complex.I)) →
      arcPoint g (k + 2) (1 - t) = Complex.exp (Complex.I *
        (((h₀ * (c₂ : ℝ) + W₂ * Real.cos φ₂ : ℝ) : ℂ) +
          ((W₂ * Real.sin φ₂ : ℝ) : ℂ) * Complex.I)) →
      W₁ = 0 ∧ W₂ = 0 := by
    intro c₁ c₂ W₁ W₂ φ₁ φ₂ hW₁0 hW₁lt hW₂0 hW₂lt hφ₁0 hφ₁π hφ₂0 hφ₂π k t ht0 ht1 harc harc'
    rw [harc2] at harc harc'
    obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ harc
    obtain ⟨n₂, hx₂, hy₂⟩ := hkey _ _ _ _ harc'
    have hc₁ : W₁ * Real.cos φ₁ = W₁ := hcollapse W₁ φ₁ hφ₁0 hφ₁π hy₁.symm
    have hc₂ : W₂ * Real.cos φ₂ = W₂ := hcollapse W₂ φ₂ hφ₂0 hφ₂π hy₂.symm
    rw [hc₁] at hx₁
    rw [hc₂] at hx₂
    -- W₁ = h₀ (t - e₁), W₂ = h₀ ((1 - t) - e₂)
    have h2πn₁ : 2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁ := by rw [← h4gh]
    have h2πn₂ : 2 * Real.pi * (n₂ : ℝ) = 4 * g * h₀ * n₂ := by rw [← h4gh]
    have hW₁e : W₁ = h₀ * (t - ((c₁ - k + 4 * g * n₁ : ℤ) : ℝ)) := by
      push_cast
      linear_combination -hx₁ - h2πn₁
    have hW₂e : W₂ = h₀ * ((1 - t) - ((c₂ - (k + 2) + 4 * g * n₂ : ℤ) : ℝ)) := by
      push_cast
      push_cast at hx₂
      linear_combination -hx₂ - h2πn₂
    rcases hWpin W₁ _ t hW₁0 hW₁lt ht0 ht1 hW₁e with ⟨he₁, hW₁t⟩ | ⟨ht1', hW₁z⟩
    · rcases hWpin W₂ _ (1 - t) hW₂0 hW₂lt (by linarith) (by linarith) hW₂e with
        ⟨he₂, hW₂t⟩ | ⟨ht0', hW₂z⟩
      · -- W₁ = h₀ t, W₂ = h₀ (1 - t): sum is h₀, too large
        exfalso
        have hsum : W₁ + W₂ = h₀ := by
          rw [hW₁t, hW₂t]
          ring
        linarith
      · -- 1 - t = 1: t = 0 hence W₁ = 0 too
        have ht0'' : t = 0 := by linarith
        constructor
        · rw [hW₁t, ht0'', mul_zero]
        · exact hW₂z
    · rcases hWpin W₂ _ (1 - t) hW₂0 hW₂lt (by linarith) (by linarith) hW₂e with
        ⟨he₂, hW₂t⟩ | ⟨ht0', hW₂z⟩
      · have : W₂ = 0 := by
          rw [hW₂t, ht1']
          norm_num
        exact ⟨hW₁z, this⟩
      · exfalso
        linarith
  -- shared vertex analysis
  have hvertcase : ∀ (c₁ : ℤ) (W₁ φ₁ : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 →
      0 ≤ φ₁ → φ₁ < Real.pi → ∀ p : ℤ,
      Complex.exp (Complex.I * (((h₀ * (c₁ : ℝ) + W₁ * Real.cos φ₁ : ℝ) : ℂ) +
        ((W₁ * Real.sin φ₁ : ℝ) : ℂ) * Complex.I)) = polyVertex g p →
      W₁ = 0 := by
    intro c₁ W₁ φ₁ hW₁0 hW₁lt hφ₁0 hφ₁π p hpe
    rw [hpv2] at hpe
    obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ hpe
    have hcc : W₁ * Real.cos φ₁ = W₁ := hcollapse W₁ φ₁ hφ₁0 hφ₁π hy₁
    rw [hcc] at hx₁
    have h2πn₁ : 2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁ := by rw [← h4gh]
    have hW₁e : W₁ = h₀ * ((0 : ℝ) - ((c₁ - p - 4 * g * n₁ : ℤ) : ℝ)) := by
      push_cast
      linear_combination hx₁ + h2πn₁
    rcases hWpin W₁ _ 0 hW₁0 hW₁lt le_rfl (by norm_num) hW₁e with ⟨_, hW₁t⟩ | ⟨h01, _⟩
    · rw [hW₁t, mul_zero]
    · exact absurd h01 (by norm_num)
  -- case analysis on the gluing relation
  rcases hrel with h1 | ⟨k, -, hpg | hpg⟩ | ⟨hv, hv'⟩
  · -- equality clause
    have hZZ : polyVertex g c *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))
        = polyVertex g c' *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u') * u' ^ (2 * g)) := by
      have hval := congrArg Subtype.val h1
      rwa [hpd, hpd'] at hval
    rw [hz, hz'] at hZZ
    obtain ⟨n, hxeq, hyeq⟩ := hkey _ _ _ _ hZZ
    have h2πn : 2 * Real.pi * (n : ℝ) = 4 * g * h₀ * n := by rw [← h4gh]
    have hdh : ((c - c' - 4 * g * n : ℤ) : ℝ) * h₀ = W' * Real.cos φ' - W * Real.cos φ := by
      push_cast
      linear_combination hxeq + h2πn
    have habs : |W * Real.cos φ| ≤ W := by
      rw [abs_mul, abs_of_nonneg hW0]
      calc W * |Real.cos φ| ≤ W * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one φ) hW0
        _ = W := mul_one W
    have habs' : |W' * Real.cos φ'| ≤ W' := by
      rw [abs_mul, abs_of_nonneg hW0']
      calc W' * |Real.cos φ'| ≤ W' * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one φ') hW0'
        _ = W' := mul_one W'
    have hbd : |W' * Real.cos φ' - W * Real.cos φ| < h₀ / 2 := by
      have h1 := abs_le.mp habs
      have h2 := abs_le.mp habs'
      rw [abs_lt]
      constructor <;> linarith
    have hd0 : (c - c' - 4 * g * n : ℤ) = 0 := by
      have h1 : ((c - c' - 4 * g * n : ℤ) : ℝ) < 1 := by
        by_contra hcon
        push Not at hcon
        have h2 : 1 * h₀ ≤ ((c - c' - 4 * g * n : ℤ) : ℝ) * h₀ :=
          mul_le_mul_of_nonneg_right hcon hh0.le
        rw [one_mul, hdh] at h2
        have := (abs_lt.mp hbd).2
        linarith
      have h2 : (-1 : ℝ) < ((c - c' - 4 * g * n : ℤ) : ℝ) := by
        by_contra hcon
        push Not at hcon
        have h3 : ((c - c' - 4 * g * n : ℤ) : ℝ) * h₀ ≤ (-1) * h₀ :=
          mul_le_mul_of_nonneg_right hcon hh0.le
        rw [hdh] at h3
        have := (abs_lt.mp hbd).1
        linarith
      have hz1 : (c - c' - 4 * g * n : ℤ) < 1 := by exact_mod_cast h1
      have hz2 : (-1 : ℤ) < (c - c' - 4 * g * n : ℤ) := by exact_mod_cast h2
      omega
    have hn0 : n = 0 := by
      have hce : c - c' = 4 * (g : ℤ) * n := by omega
      rcases lt_trichotomy n 0 with hlt | h0 | hgt
      · exfalso
        have h1 : n ≤ -1 := by omega
        have h2 : 4 * (g : ℤ) * n ≤ 4 * (g : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (4 : ℤ) * g * (-1) = -(4 * g) := by ring
        rw [h3] at h2
        omega
      · exact h0
      · exfalso
        have h1 : (1 : ℤ) ≤ n := by omega
        have h2 : 4 * (g : ℤ) * 1 ≤ 4 * (g : ℤ) * n :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [mul_one] at h2
        omega
    have hcc : c = c' := by
      have := hd0
      rw [hn0] at this
      omega
    have hcos : W * Real.cos φ = W' * Real.cos φ' := by
      have h1 : ((c - c' - 4 * g * n : ℤ) : ℝ) = 0 := by
        rw [hd0]
        norm_num
      rw [h1, zero_mul] at hdh
      linarith
    have hsin : W * Real.sin φ = W' * Real.sin φ' := hyeq
    have hWW : W = W' := by
      have e1 : (W * Real.sin φ) ^ 2 + (W * Real.cos φ) ^ 2 = W ^ 2 := by
        have hpyth := Real.sin_sq_add_cos_sq φ
        linear_combination (W ^ 2) * hpyth
      have e2 : (W' * Real.sin φ') ^ 2 + (W' * Real.cos φ') ^ 2 = W' ^ 2 := by
        have hpyth := Real.sin_sq_add_cos_sq φ'
        linear_combination (W' ^ 2) * hpyth
      have hsq : W ^ 2 = W' ^ 2 := by
        rw [← e1, ← e2, hsin, hcos]
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hp2 := pow_lt_pow_left₀ hlt hW0 (by norm_num : (2 : ℕ) ≠ 0)
        linarith only [hp2, hsq]
      · have hp2 := pow_lt_pow_left₀ hlt hW0' (by norm_num : (2 : ℕ) ≠ 0)
        linarith only [hp2, hsq]
    by_cases hWz : W = 0
    · rw [hzero hWz, hzero' (by rw [← hWW]; exact hWz)]
    · have hWne : W ≠ 0 := hWz
      have hcosφ : Real.cos φ = Real.cos φ' := by
        apply mul_left_cancel₀ hWne
        rw [hcos, hWW]
      have hφφ : φ = φ' :=
        Real.injOn_cos ⟨hφ0, hφπ.le⟩ ⟨hφ0', hφπ'.le⟩ hcosφ
      exact hfinish hWW hφφ hcc
  · -- pairing clause, (z, z') order
    obtain ⟨t, -, hteq⟩ := hpg
    have ht1 := congrArg Prod.fst hteq
    have ht2 := congrArg Prod.snd hteq
    simp only at ht1 ht2
    rw [hpd] at ht1
    rw [hpd'] at ht2
    rw [hz] at ht1
    rw [hz'] at ht2
    obtain ⟨hWzz, hWzz'⟩ := hpaircase c c' W W' φ φ' hW0 hWlt hW0' hWlt' hφ0 hφπ hφ0' hφπ'
      k (t : ℝ) t.2.1 t.2.2 ht1 ht2
    rw [hzero hWzz, hzero' hWzz']
  · -- pairing clause, (z', z) order
    obtain ⟨t, -, hteq⟩ := hpg
    have ht1 := congrArg Prod.fst hteq
    have ht2 := congrArg Prod.snd hteq
    simp only at ht1 ht2
    rw [hpd'] at ht1
    rw [hpd] at ht2
    rw [hz'] at ht1
    rw [hz] at ht2
    obtain ⟨hWzz', hWzz⟩ := hpaircase c' c W' W φ' φ hW0' hWlt' hW0 hWlt hφ0' hφπ' hφ0 hφπ
      k (t : ℝ) t.2.1 t.2.2 ht1 ht2
    rw [hzero hWzz, hzero' hWzz']
  · -- vertex clause
    obtain ⟨p, hp⟩ := hv
    obtain ⟨p', hp'⟩ := hv'
    rw [hpd, hz] at hp
    rw [hpd', hz'] at hp'
    have hWz : W = 0 := hvertcase c W φ hW0 hWlt hφ0 hφπ p hp
    have hWz' : W' = 0 := hvertcase c' W' φ' hW0' hWlt' hφ0' hφπ' p' hp'
    rw [hzero hWz, hzero' hWz']

set_option maxHeartbeats 400000 in
-- The saturation argument covers 4g corner charts with three kinds of ball
-- estimates; the resulting single proof term is large, so we raise the
-- heartbeat limit.
/-- Openness of the vertex chart inverse: the union of the log-polar corner
neighborhoods is saturated and open in the disc. -/
theorem vertexChart_isOpen_image (g : ℕ) [NeZero g] :
    ∀ W ⊆ Metric.ball (0 : ℂ) (vertexRadius g), IsOpen W →
      IsOpen (vertexChartFun g '' W) := by
  classical
  intro Wo hWsub hWopen
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hg1R : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set δ : ℝ := vertexRadius g with hδdef
  have hδ0 : 0 < δ := vertexRadius_pos g
  set h₀ : ℝ := Real.pi / (2 * g) with hh₀
  have hh0 : 0 < h₀ := by rw [hh₀]; positivity
  have hh2 : h₀ ≤ Real.pi / 2 := by
    rw [hh₀, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
    have h2g : (2 : ℝ) ≤ 2 * g := by linarith
    exact mul_le_mul_of_nonneg_left h2g hπ.le
  have h4gh : (4 * (g : ℝ)) * h₀ = 2 * Real.pi := by
    rw [hh₀]
    field_simp
    norm_num
  have hδ8 : δ ^ (2 * g) ≤ h₀ / 4 := by
    have h12 : δ ≤ 1 / 2 := min_le_left _ _
    have hq : δ ≤ Real.pi / (4 * g) := min_le_right _ _
    have h2 : δ ^ (2 * g) ≤ δ ^ 2 :=
      pow_le_pow_of_le_one hδ0.le (by linarith) (by omega)
    have h3 : δ ^ 2 ≤ (1 / 2) * (Real.pi / (4 * g)) := by
      rw [sq]
      exact mul_le_mul h12 hq hδ0.le (by norm_num)
    have h4 : (1 / 2) * (Real.pi / (4 * g)) = h₀ / 4 := by
      rw [hh₀]
      field_simp
    linarith
  -- the model closed disc
  set D : Set ℂ := Metric.closedBall (0 : ℂ) 1 with hD
  -- angle extraction
  have hexpI : ∀ Z₁ Z₂ : ℂ, Complex.exp (Complex.I * Z₁) = Complex.exp (Complex.I * Z₂) →
      ∃ n : ℤ, Z₁ = Z₂ + 2 * Real.pi * n := by
    intro Z₁ Z₂ hZ
    rw [Complex.exp_eq_exp_iff_exists_int] at hZ
    obtain ⟨n, hn⟩ := hZ
    refine ⟨n, ?_⟩
    have h2 : Complex.I * Z₁ = Complex.I * (Z₂ + 2 * Real.pi * n) := by
      rw [hn]
      ring
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hkey : ∀ x₁ y₁ x₂ y₂ : ℝ,
      Complex.exp (Complex.I * (((x₁ : ℝ) : ℂ) + ((y₁ : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * (((x₂ : ℝ) : ℂ) + ((y₂ : ℝ) : ℂ) * Complex.I)) →
      ∃ n : ℤ, x₁ = x₂ + 2 * Real.pi * n ∧ y₁ = y₂ := by
    intro x₁ y₁ x₂ y₂ hx
    obtain ⟨n, hn⟩ := hexpI _ _ hx
    refine ⟨n, ?_, ?_⟩
    · have := congrArg Complex.re hn
      simpa using this
    · have := congrArg Complex.im hn
      simpa using this
  have hpv2 : ∀ p : ℤ, polyVertex g p =
      Complex.exp (Complex.I * (((h₀ * (p : ℝ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro p
    unfold polyVertex
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    field_simp
  have harc2 : ∀ (k : ℤ) (t : ℝ), arcPoint g k t =
      Complex.exp (Complex.I * (((h₀ * ((k : ℝ) + t) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) := by
    intro k t
    unfold arcPoint
    rw [Complex.ofReal_zero, zero_mul, add_zero]
    congr 1
    rw [hh₀]
    push_cast
    field_simp
  have hnormz : ∀ x y : ℝ,
      ‖Complex.exp (Complex.I * (((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        = Real.exp (-y) := by
    intro x y
    rw [Complex.norm_exp]
    congr 1
    simp
  have hsec0 : vertexSectorIndex g (0 : ℂ) = 0 := by
    unfold vertexSectorIndex
    rw [Complex.arg_zero]
    norm_num
  have hvert : ∀ c : ℤ, ‖polyVertex g c‖ = 1 := by
    intro c
    have hrw : polyVertex g c
        = Complex.exp (((Real.pi * (c : ℝ) / (2 * (g : ℝ))) : ℝ) * Complex.I) := by
      unfold polyVertex
      congr 1
      push_cast
      ring
    rw [hrw]
    exact Complex.norm_exp_ofReal_mul_I _
  have hpvne : ∀ c : ℤ, polyVertex g c ≠ 0 := by
    intro c hc
    have := hvert c
    rw [hc, norm_zero] at this
    exact absurd this (by norm_num)
  -- normal form of the chart value at a point of the chart disc
  have hsetup : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
      ∃ (α φ W : ℝ) (c : ℤ),
        c = ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) ∧
        (0 ≤ c ∧ c < 4 * g) ∧ vertexSectorIndex g u < 4 * g ∧
        u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) ∧
        W = ‖u‖ ^ (2 * g) ∧ (0 ≤ W ∧ W < h₀ / 4) ∧
        (0 ≤ φ ∧ φ < Real.pi) ∧
        φ = 2 * g * α - (vertexSectorIndex g u : ℝ) * Real.pi ∧
        Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g)
          = Complex.I * ((((W * Real.cos φ : ℝ)) : ℂ) +
              (((W * Real.sin φ : ℝ)) : ℂ) * Complex.I) ∧
        polyVertex g c * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))
          = Complex.exp (Complex.I * (((h₀ * (c : ℝ) + W * Real.cos φ : ℝ) : ℂ) +
              ((W * Real.sin φ : ℝ) : ℂ) * Complex.I)) ∧
        ‖polyVertex g c *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u) * u ^ (2 * g))‖ ≤ 1 ∧
        (W = 0 → u = 0) := by
    intro u hu
    have hρδ : ‖u‖ < δ := mem_ball_zero_iff.mp hu
    have hρ0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
    have hWlt : ‖u‖ ^ (2 * g) < h₀ / 4 :=
      lt_of_lt_of_le (pow_lt_pow_left₀ hρδ hρ0 (by omega)) hδ8
    have hW0 : (0 : ℝ) ≤ ‖u‖ ^ (2 * g) := pow_nonneg hρ0 _
    have hcval : (0 : ℤ) ≤ ((vertexSlot g ((vertexSectorIndex g u : ℕ) :
        ZMod (4 * g))).val : ℤ) ∧
        ((vertexSlot g ((vertexSectorIndex g u : ℕ) : ZMod (4 * g))).val : ℤ) < 4 * g := by
      constructor
      · positivity
      · exact_mod_cast ZMod.val_lt _
    by_cases hu0 : u = 0
    · subst hu0
      refine ⟨0, 0, ‖(0 : ℂ)‖ ^ (2 * g), _, rfl, hcval, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsec0]
        omega
      · simp
      · exact ⟨hW0, hWlt⟩
      · exact ⟨le_refl 0, hπ⟩
      · rw [hsec0]
        push_cast
        ring
      · rw [hsec0, norm_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0)]
        simp
      · rw [hsec0, norm_zero]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
        rw [hpv2]
        norm_num
        simp [zero_pow (show 2 * g ≠ 0 by omega)]
      · rw [hsec0]
        rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
        rw [hvert]
      · intro _
        rfl
    · have harg1 : -Real.pi < Complex.arg u := Complex.neg_pi_lt_arg u
      have harg2 : Complex.arg u ≤ Real.pi := Complex.arg_le_pi u
      set α : ℝ := if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u
        with hα
      have hα0 : 0 ≤ α := by
        rw [hα]
        split_ifs with hc
        · linarith
        · linarith [not_lt.mp hc]
      have hα2 : α < 2 * Real.pi := by
        rw [hα]
        split_ifs with hc
        · linarith
        · linarith
      have hue : u = (‖u‖ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) := by
        have hbase : u = (‖u‖ : ℂ) * Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) :=
          (Complex.norm_mul_exp_arg_mul_I u).symm
        rw [hα]
        split_ifs with hc
        · have h2π : Complex.exp (((Complex.arg u + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
              = Complex.exp (((Complex.arg u : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.exp_eq_exp_iff_exists_int]
            refine ⟨1, ?_⟩
            push_cast
            ring
          rw [h2π]
          exact hbase
        · exact hbase
      have hsec : vertexSectorIndex g u = (⌊2 * (g : ℝ) / Real.pi * α⌋).toNat := by
        unfold vertexSectorIndex
        rw [hα]
      set x : ℝ := 2 * (g : ℝ) / Real.pi * α with hx
      have hx0 : 0 ≤ x := by
        rw [hx]
        exact mul_nonneg (by positivity) hα0
      have hfl0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
      have hsecZ : ((vertexSectorIndex g u : ℕ) : ℤ) = ⌊x⌋ := by
        rw [hsec]
        exact Int.toNat_of_nonneg hfl0
      have hsecR : ((vertexSectorIndex g u : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsecZ
      have hle : ((vertexSectorIndex g u : ℝ)) ≤ x := by
        rw [hsecR]
        exact Int.floor_le x
      have hlt : x < (vertexSectorIndex g u : ℝ) + 1 := by
        rw [hsecR]
        exact Int.lt_floor_add_one x
      have hm4 : vertexSectorIndex g u < 4 * g := by
        have hxlt : x < 4 * g := by
          rw [hx]
          calc 2 * (g : ℝ) / Real.pi * α < 2 * g / Real.pi * (2 * Real.pi) := by
                exact mul_lt_mul_of_pos_left hα2 (by positivity)
            _ = 4 * g := by field_simp; ring
        have hflt : ⌊x⌋ < ((4 * g : ℕ) : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hxlt)
        omega
      have hπx : Real.pi * x = 2 * g * α := by
        rw [hx]
        field_simp
      set msec : ℕ := vertexSectorIndex g u with hmsec
      set φ : ℝ := 2 * g * α - (msec : ℝ) * Real.pi with hφ
      have hφx : φ = Real.pi * (x - (msec : ℝ)) := by
        rw [hφ, ← hπx]
        ring
      have hφ0 : 0 ≤ φ := by
        rw [hφx]
        exact mul_nonneg hπ.le (by linarith)
      have hφπ : φ < Real.pi := by
        rw [hφx]
        calc Real.pi * (x - (msec : ℝ)) < Real.pi * 1 :=
              mul_lt_mul_of_pos_left (by linarith) hπ
          _ = Real.pi := mul_one _
      have hIarg : Complex.I * (-1) ^ msec * u ^ (2 * g)
          = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
              (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
        have hupow : u ^ (2 * g)
            = ((‖u‖ ^ (2 * g) : ℝ) : ℂ) * Complex.exp (((2 * g * α : ℝ) : ℂ) * Complex.I) := by
          have h1 : u ^ (2 * g)
              = ((‖u‖ : ℂ)) ^ (2 * g) * Complex.exp ((α : ℂ) * Complex.I) ^ (2 * g) := by
            rw [← mul_pow]
            exact congrArg (fun z : ℂ => z ^ (2 * g)) hue
          rw [h1, ← Complex.exp_nat_mul]
          congr 1
          · push_cast
            ring
          · congr 1
            push_cast
            ring
        have hsplit : Complex.exp (((2 * g * α : ℝ) : ℂ) * Complex.I)
            = (-1) ^ msec * Complex.exp (((φ : ℝ) : ℂ) * Complex.I) := by
          have h2 : (2 * g * α : ℝ) = (msec : ℝ) * Real.pi + φ := by
            rw [hφ]
            ring
          rw [h2]
          have h3 : ((((msec : ℝ) * Real.pi + φ : ℝ)) : ℂ) * Complex.I
              = ((msec : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) + ((φ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [h3, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
        have hcs : Complex.exp (((φ : ℝ) : ℂ) * Complex.I)
            = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
          rw [Complex.exp_mul_I]
          rw [Complex.ofReal_cos, Complex.ofReal_sin]
        have hm2 : ((-1 : ℂ)) ^ msec * (-1) ^ msec = 1 := by
          rw [← pow_add]
          exact Even.neg_one_pow ⟨msec, by ring⟩
        calc Complex.I * (-1) ^ msec * u ^ (2 * g)
            = Complex.I * (-1) ^ msec * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                ((-1) ^ msec * (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) *
                  Complex.I))) := by
              rw [hupow, hsplit, hcs]
          _ = Complex.I * (((‖u‖ ^ (2 * g) : ℝ) : ℂ) *
                (((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I)) *
                ((-1) ^ msec * (-1) ^ msec) := by ring
          _ = Complex.I * ((((‖u‖ ^ (2 * g) * Real.cos φ : ℝ)) : ℂ) +
                (((‖u‖ ^ (2 * g) * Real.sin φ : ℝ)) : ℂ) * Complex.I) := by
              rw [hm2]
              push_cast
              ring
      have hzid : polyVertex g ((vertexSlot g ((msec : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ msec * u ^ (2 * g))
          = Complex.exp (Complex.I *
              (((h₀ * (((vertexSlot g ((msec : ℕ) : ZMod (4 * g))).val : ℤ) : ℝ) +
                ‖u‖ ^ (2 * g) * Real.cos φ : ℝ) : ℂ) +
              ((‖u‖ ^ (2 * g) * Real.sin φ : ℝ) : ℂ) * Complex.I)) := by
        rw [hpv2, hIarg, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      refine ⟨α, φ, ‖u‖ ^ (2 * g), _, rfl, hcval, hm4, hue, rfl, ⟨hW0, hWlt⟩, ⟨hφ0, hφπ⟩,
        rfl, hIarg, hzid, ?_, ?_⟩
      · rw [hzid, hnormz]
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ‖u‖ ^ (2 * g) * Real.sin φ :=
          mul_nonneg hW0 (Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ.le)
        linarith
      · intro hWz
        exact norm_eq_zero.mp ((pow_eq_zero_iff (by omega : 2 * g ≠ 0)).mp hWz)
  -- pinning helpers
  have hcollapse : ∀ W₁ φ₁ : ℝ, 0 < W₁ → 0 ≤ φ₁ → φ₁ < Real.pi → W₁ * Real.sin φ₁ = 0 →
      φ₁ = 0 := by
    intro W₁ φ₁ hW₁ h0 hπ₁ hs
    rcases mul_eq_zero.mp hs with hW | hsin
    · exact absurd hW (ne_of_gt hW₁)
    · by_contra hne
      have hpos : 0 < Real.sin φ₁ :=
        Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne h0 (Ne.symm hne)) hπ₁
      rw [hsin] at hpos
      exact absurd hpos (lt_irrefl 0)
  have hWpin : ∀ (W₁ : ℝ) (e : ℤ) (s : ℝ), 0 ≤ W₁ → W₁ < h₀ / 4 → 0 ≤ s → s ≤ 1 →
      W₁ = h₀ * (s - (e : ℝ)) → (e = 0 ∧ W₁ = h₀ * s) ∨ (s = 1 ∧ W₁ = 0) := by
    intro W₁ e s hW1 hW2 hs0 hs1 hWe
    have hse0 : 0 ≤ s - (e : ℝ) := by
      by_contra hcon
      push Not at hcon
      have : h₀ * (s - (e : ℝ)) < 0 := mul_neg_of_pos_of_neg hh0 hcon
      linarith
    have hse1 : s - (e : ℝ) < 1 / 4 := by
      by_contra hcon
      push Not at hcon
      have h5 : h₀ * (1 / 4) ≤ h₀ * (s - (e : ℝ)) := mul_le_mul_of_nonneg_left hcon hh0.le
      have h6 : h₀ * (1 / 4) = h₀ / 4 := by ring
      linarith
    have he1 : ((e : ℝ)) < 2 := by linarith
    have he2 : (-1 : ℝ) < ((e : ℝ)) := by linarith
    have hei : e < 2 ∧ -1 < e := ⟨by exact_mod_cast he1, by exact_mod_cast he2⟩
    have hcases : e = 0 ∨ e = 1 := by omega
    rcases hcases with he | he
    · left
      refine ⟨he, ?_⟩
      rw [hWe, he]
      norm_num
    · right
      have hs1' : s = 1 := by
        rw [he] at hse0
        push_cast at hse0
        linarith
      refine ⟨hs1', ?_⟩
      rw [hWe, he, hs1']
      norm_num
  -- ZMod plumbing
  have hcast : ∀ x : ZMod (4 * g), (((x.val : ℤ)) : ZMod (4 * g)) = x := by
    intro x
    rw [Int.cast_natCast]
    exact ZMod.natCast_rightInverse x
  have hplus2 : ∀ x : ZMod (4 * g), (x + 2).val % 4 = (x.val + 2) % 4 := by
    intro x
    have h1 : x + 2 = ((x.val + 2 : ℕ) : ZMod (4 * g)) := by
      push_cast
      rw [ZMod.natCast_rightInverse x]
    rw [h1, ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd _ ⟨g, rfl⟩
  have hminus2 : ∀ x : ZMod (4 * g), (x - 2).val % 4 = (x.val + 2) % 4 := by
    intro x
    have h0 : ((4 * g - 2 : ℕ) : ZMod (4 * g)) = -2 := by
      have h1 : ((4 * g - 2 : ℕ) : ZMod (4 * g)) + ((2 : ℕ) : ZMod (4 * g)) = 0 := by
        rw [← Nat.cast_add]
        have h2 : 4 * g - 2 + 2 = 4 * g := by omega
        rw [h2, ZMod.natCast_self]
      have h3 := eq_neg_of_add_eq_zero_left h1
      rwa [show ((2 : ℕ) : ZMod (4 * g)) = (2 : ZMod (4 * g)) from by push_cast; ring] at h3
    have h1 : x - 2 = ((x.val + (4 * g - 2) : ℕ) : ZMod (4 * g)) := by
      rw [Nat.cast_add, h0, ZMod.natCast_rightInverse x]
      ring
    rw [h1, ZMod.val_natCast]
    have h2 := Nat.mod_mod_of_dvd (x.val + (4 * g - 2)) (⟨g, rfl⟩ : (4 : ℕ) ∣ 4 * g)
    rw [h2]
    omega
  have hcornerexp : ∀ (a : ℤ) (θ : ℝ),
      polyVertex g a * Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ)))
        = Complex.exp (Complex.I * (((h₀ * (a : ℝ) - θ : ℝ)) : ℂ)) := by
    intro a θ
    rw [hpv2 a, Complex.ofReal_zero, zero_mul, add_zero, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the sector root: `RT j V` is the sector-`j` preimage of the corner point `v_{c_j} e^{iV}`.
  set RT : ℕ → ℂ → ℂ := fun j V =>
    Complex.exp ((Complex.log V + (j : ℕ) * Real.pi * Complex.I) / ((2 * (g : ℝ) : ℝ) : ℂ))
    with hRT
  have hRTnorm : ∀ (j : ℕ) (V : ℂ),
      ‖RT j V‖ = Real.exp ((Real.log ‖V‖ + 0) / (2 * (g : ℝ))) := by
    intro j V
    rw [hRT]
    simp only []
    rw [Complex.norm_exp]
    congr 1
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.re_ofReal_mul]
    rw [Complex.add_re, Complex.log_re]
    have him : ((j : ℕ) * Real.pi * Complex.I : ℂ).re = 0 := by
      simp [Complex.mul_re]
    rw [him]
    ring
  have hRTpow : ∀ (j : ℕ) (V : ℂ), V ≠ 0 → (RT j V) ^ (2 * g) = V * (-1) ^ j := by
    intro j V hV
    rw [hRT]
    simp only []
    rw [← Complex.exp_nat_mul]
    have harg : ((2 * g : ℕ) : ℂ) * ((Complex.log V + (j : ℕ) * Real.pi * Complex.I) /
        ((2 * (g : ℝ) : ℝ) : ℂ)) = Complex.log V + (j : ℕ) * Real.pi * Complex.I := by
      have hne : (((2 * (g : ℝ) : ℝ)) : ℂ) ≠ 0 := by
        push_cast
        intro hc
        have : (g : ℂ) = 0 := by linear_combination hc / 2
        exact hgC this
      field_simp
      push_cast
      ring
    have hexpj : Complex.exp (((j : ℕ) : ℂ) * Real.pi * Complex.I) = (-1) ^ j := by
      rw [mul_assoc, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    rw [harg, Complex.exp_add, Complex.exp_log hV, hexpj]
  -- the sector index of the root
  have hRTsec : ∀ (j : ℕ), j < 4 * g → ∀ V : ℂ, V ≠ 0 → 0 ≤ V.arg → V.arg < Real.pi →
      vertexSectorIndex g (RT j V) = j := by
    intro j hj V hV h0 hπV
    set w : ℂ := (Complex.log V + (j : ℕ) * Real.pi * Complex.I) / ((2 * (g : ℝ) : ℝ) : ℂ)
      with hw
    have hwim : w.im = (V.arg + j * Real.pi) / (2 * (g : ℝ)) := by
      rw [hw, div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm, Complex.im_ofReal_mul]
      rw [Complex.add_im, Complex.log_im]
      have him : ((j : ℕ) * Real.pi * Complex.I : ℂ).im = j * Real.pi := by
        simp [Complex.mul_im]
      rw [him]
      ring
    set y : ℝ := (V.arg + j * Real.pi) / (2 * (g : ℝ)) with hy
    have hy0 : 0 ≤ y := by
      rw [hy]
      apply div_nonneg _ (by linarith)
      have : (0 : ℝ) ≤ j * Real.pi := by positivity
      linarith
    have hy2 : y < 2 * Real.pi := by
      rw [hy, div_lt_iff₀ (by linarith)]
      have hjR : (j : ℝ) ≤ 4 * g - 1 := by
        have : (j : ℝ) + 1 ≤ 4 * g := by exact_mod_cast hj
        linarith
      have : (j : ℝ) * Real.pi ≤ (4 * g - 1) * Real.pi :=
        mul_le_mul_of_nonneg_right hjR hπ.le
      nlinarith
    -- `RT j V = e^{w.re} · exp(y i)`
    have hsplit : RT j V = ((Real.exp w.re : ℝ) : ℂ) * Complex.exp ((y : ℝ) * Complex.I) := by
      rw [hRT]
      simp only []
      rw [← hw]
      calc Complex.exp w = Complex.exp (((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I) := by
            rw [Complex.re_add_im]
        _ = Complex.exp ((w.re : ℝ) : ℂ) * Complex.exp (((w.im : ℝ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
        _ = ((Real.exp w.re : ℝ) : ℂ) * Complex.exp ((y : ℝ) * Complex.I) := by
            rw [Complex.ofReal_exp, hwim]
    have hargRT : Complex.arg (RT j V) = if y ≤ Real.pi then y else y - 2 * Real.pi := by
      rw [hsplit]
      rw [Complex.arg_real_mul _ (Real.exp_pos _)]
      split_ifs with hcase
      · rw [Complex.exp_mul_I]
        exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, hcase⟩
      · have hper : Complex.exp ((y : ℝ) * Complex.I)
            = Complex.exp (((y - 2 * Real.pi : ℝ) : ℝ) * Complex.I) := by
          rw [Complex.exp_eq_exp_iff_exists_int]
          refine ⟨1, ?_⟩
          push_cast
          ring
        rw [hper, Complex.exp_mul_I]
        exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩
    -- normalized angle is `y` in both cases
    have hA : (if Complex.arg (RT j V) < 0 then Complex.arg (RT j V) + 2 * Real.pi
        else Complex.arg (RT j V)) = y := by
      rw [hargRT]
      rcases le_or_gt y Real.pi with hcase | hcase
      · rw [if_pos hcase, if_neg (not_lt.mpr hy0)]
      · rw [if_neg (not_le.mpr hcase), if_pos (by linarith : y - 2 * Real.pi < 0)]
        ring
    unfold vertexSectorIndex
    rw [hA]
    have hxval : 2 * (g : ℝ) / Real.pi * y = V.arg / Real.pi + (j : ℤ) := by
      rw [hy]
      push_cast
      field_simp
    rw [hxval, Int.floor_add_intCast]
    have hfl : ⌊V.arg / Real.pi⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · positivity
      · rw [div_lt_one hπ]
        exact hπV
    rw [hfl, zero_add]
    exact Int.toNat_natCast j
  -- the root hits the corner point
  have hroot : ∀ (j : ℕ), j < 4 * g → ∀ V : ℂ, V ≠ 0 → 0 ≤ V.arg → V.arg < Real.pi →
      vertexChartFun g (RT j V) = Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * V))) := by
    intro j hj V hV h0 hπV
    have hs := hRTsec j hj V hV h0 hπV
    have hp := hRTpow j V hV
    have h1 : vertexChartFun g (RT j V) = Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g
            ((vertexSlot g ((vertexSectorIndex g (RT j V) : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g (RT j V)) *
            (RT j V) ^ (2 * g)))) := rfl
    rw [h1, hs, hp]
    have h2 : Complex.I * (-1) ^ j * (V * (-1) ^ j) = Complex.I * V := by
      have hm2 : ((-1 : ℂ)) ^ j * (-1) ^ j = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨j, by ring⟩
      calc Complex.I * (-1) ^ j * (V * (-1) ^ j)
          = Complex.I * V * ((-1) ^ j * (-1) ^ j) := by ring
        _ = Complex.I * V := by rw [hm2]; ring
    rw [h2]
  -- glue across a shared ray, in the `θ`-parametrization
  have hglueθ : ∀ (n : ℕ) (θ : ℝ), 0 ≤ θ → θ < h₀ →
      (Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g ((n : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (-(Complex.I * ((θ : ℝ) : ℂ))))) : GenusSurface g) =
      Quotient.mk (genusSetoid g)
        (projDisc (polyVertex g ((vertexSlot g (((n : ℕ) : ZMod (4 * g)) + 1)).val : ℤ) *
          Complex.exp (Complex.I * ((θ : ℝ) : ℂ)))) := by
    intro n θ hθ0 hθh
    set r : ℝ := if θ = 0 then 0 else Real.exp (Real.log θ / (2 * (g : ℝ))) with hr
    have hr0 : 0 ≤ r := by
      rw [hr]
      split_ifs
      · exact le_refl 0
      · exact (Real.exp_pos _).le
    have hrpow : r ^ (2 * g) = θ := by
      rw [hr]
      split_ifs with hθz
      · rw [hθz, zero_pow (by omega : 2 * g ≠ 0)]
      · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθz)
        rw [← Real.exp_nat_mul]
        have h2 : ((2 * g : ℕ) : ℝ) * (Real.log θ / (2 * (g : ℝ))) = Real.log θ := by
          push_cast
          field_simp
        rw [h2, Real.exp_log hθpos]
    have hrC : ((r : ℂ)) ^ (2 * g) = ((θ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hrpow]
    have hsmall : r ^ (2 * g) < Real.pi / (2 * g) := by
      rw [hrpow]
      rw [hh₀] at hθh
      exact hθh
    have hres := Quotient.sound (s := genusSetoid g) (vertexRay_glue g n hr0 hsmall)
    rw [hrC] at hres
    exact hres
  -- norm control for the root
  have hRTball : ∀ (η : ℝ), 0 < η → ∀ (i : ℕ) (V : ℂ), V ≠ 0 → ‖V‖ < η ^ (2 * g) →
      ‖RT i V‖ < η := by
    intro η hη i V hV hVη
    rw [hRTnorm, add_zero]
    have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
    have hlog : Real.log ‖V‖ < Real.log (η ^ (2 * g)) := Real.log_lt_log hVpos hVη
    rw [Real.log_pow] at hlog
    have h2 : Real.log ‖V‖ / (2 * (g : ℝ)) < Real.log η := by
      rw [div_lt_iff₀ (by linarith)]
      push_cast at hlog
      linarith
    calc Real.exp (Real.log ‖V‖ / (2 * (g : ℝ))) < Real.exp (Real.log η) :=
          Real.exp_lt_exp.mpr h2
      _ = η := Real.exp_log hη
  -- reduction to a ball criterion on the saturation
  apply isOpen_coinduced.mpr
  set T : Set ClosedDisc := Quotient.mk (genusSetoid g) ⁻¹' (vertexChartFun g '' Wo) with hT
  have hTmem : ∀ (z : ClosedDisc) (u : ℂ), u ∈ Wo →
      vertexChartFun g u = Quotient.mk (genusSetoid g) z → z ∈ T := by
    intro z u hu he
    exact ⟨u, hu, he⟩
  have hopen_of_balls : (∀ z₀ ∈ T, ∃ ε, 0 < ε ∧
      ∀ z : ClosedDisc, ‖z.1 - z₀.1‖ < ε → z ∈ T) → IsOpen T := by
    intro hTb
    rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨ε, hε0, hball⟩ := hTb z₀ hz₀
    refine ⟨Subtype.val ⁻¹' Metric.ball z₀.1 ε, ?_, ?_, ?_⟩
    · intro z hz
      apply hball z
      have hz' : z.1 ∈ Metric.ball z₀.1 ε := hz
      rwa [Metric.mem_ball, dist_eq_norm] at hz'
    · exact isOpen_ball.preimage continuous_subtype_val
    · change z₀.1 ∈ Metric.ball z₀.1 ε
      exact Metric.mem_ball_self hε0
  -- membership of a closed-disc point whose value is a known corner form
  have hzT : ∀ (z : ClosedDisc) (u : ℂ), u ∈ Wo →
      vertexChartFun g u = Quotient.mk (genusSetoid g) (projDisc z.1) → z ∈ T := by
    intro z u hu he
    apply hTmem z u hu
    rw [he]
    congr 1
    exact Subtype.ext (projDisc_eq (mem_closedBall_zero_iff.mp z.2))
  -- the vertex-ball lemma
  have hballB : (0 : ℂ) ∈ Wo → ∀ p : ℤ, ∃ ε, 0 < ε ∧
      ∀ z : ClosedDisc, ‖z.1 - polyVertex g p‖ < ε → z ∈ T := by
    intro h0W p
    obtain ⟨η, hη0, hηsub⟩ := Metric.isOpen_iff.mp hWopen 0 h0W
    -- normalize the vertex index
    set p' : ℤ := p % ((4 * g : ℕ) : ℤ) with hp'
    have h4gZ : (0 : ℤ) < ((4 * g : ℕ) : ℤ) := by positivity
    have hp'0 : 0 ≤ p' := Int.emod_nonneg p (by omega)
    have hp'lt : p' < ((4 * g : ℕ) : ℤ) := Int.emod_lt_of_pos p h4gZ
    have hmodeq : (p : ZMod (4 * g)) = ((p' : ℤ) : ZMod (4 * g)) := by
      rw [ZMod.intCast_eq_intCast_iff]
      exact (Int.emod_emod_of_dvd p dvd_rfl).symm
    have hpvcongr : ∀ x y : ℤ, ((x : ZMod (4 * g)) = (y : ZMod (4 * g))) →
        polyVertex g x = polyVertex g y := by
      intro x y hxy
      rw [ZMod.intCast_eq_intCast_iff] at hxy
      obtain ⟨q, hq⟩ := Int.ModEq.dvd hxy
      have hqZ : x - y = 4 * (g : ℤ) * (-q) := by push_cast at hq ⊢; linarith
      have hqC : (x : ℂ) - y = 4 * g * (-q : ℤ) := by exact_mod_cast hqZ
      unfold polyVertex
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-q, ?_⟩
      push_cast at hqC ⊢
      field_simp
      linear_combination hqC
    have hpvp : polyVertex g p = polyVertex g p' := hpvcongr p p' hmodeq
    -- the sector landing at this corner
    obtain ⟨jz, hjz⟩ := (vertexSlot_bijective g).surjective ((p' : ℤ) : ZMod (4 * g))
    set j : ℕ := jz.val with hjdef
    have hj4 : j < 4 * g := ZMod.val_lt jz
    have hslotj : vertexSlot g ((j : ℕ) : ZMod (4 * g)) = ((p' : ℤ) : ZMod (4 * g)) := by
      rw [hjdef, ZMod.natCast_rightInverse jz]
      exact hjz
    have hslotval : ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) = p' := by
      rw [hslotj]
      have h1 : ((p' : ℤ) : ZMod (4 * g)) = ((p'.toNat : ℕ) : ZMod (4 * g)) := by
        rw [← Int.toNat_of_nonneg hp'0]
        push_cast
        rw [Int.toNat_of_nonneg hp'0]
      rw [h1, ZMod.val_cast_of_lt (by omega)]
      omega
    -- the successor sector index
    set j₂ : ℕ := if j + 1 = 4 * g then 0 else j + 1 with hj₂
    have hj₂4 : j₂ < 4 * g := by
      rw [hj₂]
      split_ifs <;> omega
    have hj₂cast : ((j₂ : ℕ) : ZMod (4 * g)) = ((j : ℕ) : ZMod (4 * g)) + 1 := by
      rw [hj₂]
      split_ifs with hcase
      · rw [Nat.cast_zero]
        have : ((j + 1 : ℕ) : ZMod (4 * g)) = ((j : ℕ) : ZMod (4 * g)) + 1 := by push_cast; ring
        rw [← this, hcase, ZMod.natCast_self]
      · push_cast
        ring
    -- the eventual conditions near the vertex
    set b : ℝ := min (min (η ^ (2 * g)) (h₀ / 2)) 1 with hb
    have hb0 : 0 < b := by
      rw [hb]
      have : (0:ℝ) < η ^ (2*g) := by positivity
      simp only [lt_min_iff]
      exact ⟨⟨this, by linarith⟩, by norm_num⟩
    set U₁ : Set ℂ := {w : ℂ | 0 < (w / polyVertex g p').re} with hU₁
    have hU₁open : IsOpen U₁ := by
      have hcont : Continuous fun w : ℂ => (w / polyVertex g p').re :=
        Complex.continuous_re.comp (continuous_id.div_const _)
      exact isOpen_lt continuous_const hcont
    have hVmcont : ContinuousOn (fun w : ℂ => -Complex.I * Complex.log (w / polyVertex g p'))
        U₁ := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.clog (continuousOn_id.div_const _)
      intro w hw
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hw)
    set C : Set ℂ := U₁ ∩ (fun w : ℂ => -Complex.I * Complex.log (w / polyVertex g p')) ⁻¹'
        (Metric.ball (0 : ℂ) b) with hC
    have hCopen : IsOpen C := hVmcont.isOpen_inter_preimage hU₁open isOpen_ball
    have hCmem : polyVertex g p' ∈ C := by
      constructor
      · change 0 < (polyVertex g p' / polyVertex g p').re
        rw [div_self (hpvne p')]
        norm_num
      · change -Complex.I * Complex.log (polyVertex g p' / polyVertex g p') ∈ Metric.ball 0 b
        rw [div_self (hpvne p'), Complex.log_one, mul_zero]
        exact Metric.mem_ball_self hb0
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp (hCopen.mem_nhds hCmem)
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    rw [hpvp] at hz
    have hwC : z.1 ∈ C := hεsub (by rwa [Metric.mem_ball, dist_eq_norm])
    obtain ⟨hw1, hw2⟩ := hwC
    set V : ℂ := -Complex.I * Complex.log (z.1 / polyVertex g p') with hV
    have hVb : ‖V‖ < b := by
      have := hw2
      rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at this
    have hzne : z.1 ≠ 0 := by
      intro hc
      have : (0 : ℝ) < ((z.1 / polyVertex g p').re) := hw1
      rw [hc, zero_div] at this
      simp at this
    have hζne : z.1 / polyVertex g p' ≠ 0 := div_ne_zero hzne (hpvne p')
    have hwexp : z.1 = polyVertex g p' * Complex.exp (Complex.I * V) := by
      have h1 : Complex.I * V = Complex.log (z.1 / polyVertex g p') := by
        rw [hV]
        calc Complex.I * (-Complex.I * Complex.log (z.1 / polyVertex g p'))
            = -(Complex.I * Complex.I) * Complex.log (z.1 / polyVertex g p') := by ring
          _ = Complex.log (z.1 / polyVertex g p') := by
              rw [Complex.I_mul_I]
              ring
      rw [h1, Complex.exp_log hζne, mul_comm]
      exact (div_mul_cancel₀ z.1 (hpvne p')).symm
    have hVim : 0 ≤ V.im := by
      have h1 : V.im = -(Complex.log (z.1 / polyVertex g p')).re := by
        rw [hV]
        have : (-Complex.I * Complex.log (z.1 / polyVertex g p')).im
            = -(Complex.log (z.1 / polyVertex g p')).re := by
          simp [Complex.mul_im]
        exact this
      rw [h1, Complex.log_re]
      have h2 : ‖z.1 / polyVertex g p'‖ = ‖z.1‖ := by
        rw [Complex.norm_div, hvert, div_one]
      rw [h2]
      have h3 : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have := Real.log_nonpos (norm_nonneg _) h3
      linarith
    by_cases hV0 : V = 0
    · -- the vertex itself
      have hzp : z.1 = polyVertex g p' := by
        rw [hwexp, hV0, mul_zero, Complex.exp_zero, mul_one]
      apply hzT z 0 h0W
      have hf0 : vertexChartFun g (0 : ℂ) = Quotient.mk (genusSetoid g)
          (projDisc (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g (0 : ℂ) : ℕ) : ZMod (4 * g))).val : ℤ) *
            Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g (0 : ℂ)) *
              (0 : ℂ) ^ (2 * g)))) := rfl
      rw [hf0]
      rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
      apply Quotient.sound
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [projDisc_eq (le_of_eq (hvert _))]
        exact ⟨_, rfl⟩
      · rw [projDisc_eq (by rw [hzp, hvert] : ‖z.1‖ ≤ 1), hzp]
        exact ⟨p', rfl⟩
    · have hargV0 : 0 ≤ V.arg := Complex.arg_nonneg_iff.mpr hVim
      have hVη : ‖V‖ < η ^ (2 * g) := by
        apply lt_of_lt_of_le hVb
        rw [hb]
        exact le_trans (min_le_left _ _) (min_le_left _ _)
      have hVh : ‖V‖ < h₀ / 2 := by
        apply lt_of_lt_of_le hVb
        rw [hb]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      by_cases hargVπ : V.arg = Real.pi
      · -- on the circle, clockwise side: jump to the paired sector
        obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp hargVπ
        set θw : ℝ := -V.re with hθw
        have hθw0 : 0 < θw := by rw [hθw]; linarith
        have hVθ : V = ((-θw : ℝ) : ℂ) := by
          apply Complex.ext
          · rw [hθw]
            simp
          · rw [him]
            simp
        have hθwn : θw ≤ ‖V‖ := by
          have := Complex.abs_re_le_norm V
          rw [abs_of_nonpos (by linarith : V.re ≤ 0)] at this
          rw [hθw]
          exact this
        have hθC : ((θw : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast ne_of_gt hθw0
        have hargθ : Complex.arg ((θw : ℝ) : ℂ) = 0 := Complex.arg_ofReal_of_nonneg hθw0.le
        have hu := hroot j₂ hj₂4 ((θw : ℝ) : ℂ) hθC (by rw [hargθ]) (by rw [hargθ]; exact hπ)
        apply hzT z (RT j₂ ((θw : ℝ) : ℂ))
        · apply hηsub
          rw [Metric.mem_ball, dist_zero_right]
          apply hRTball η hη0
          · exact hθC
          · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hθw0]
            linarith
        · rw [hu]
          have hslot2 : vertexSlot g ((j₂ : ℕ) : ZMod (4 * g))
              = vertexSlot g (((j : ℕ) : ZMod (4 * g)) + 1) := by
            rw [hj₂cast]
          rw [hslot2]
          rw [← hglueθ j θw hθw0.le (by linarith)]
          congr 2
          rw [hslotval]
          rw [hwexp, hVθ]
          congr 1
          push_cast
          ring_nf
      · -- interior or counterclockwise side: direct root
        have hargVπ' : V.arg < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi V) hargVπ
        have hu := hroot j hj4 V hV0 hargV0 hargVπ'
        apply hzT z (RT j V)
        · apply hηsub
          rw [Metric.mem_ball, dist_zero_right]
          exact hRTball η hη0 j V hV0 hVη
        · rw [hu, hwexp]
          congr 3
          rw [hslotval]
  -- corner-ball lemma: coverage around a corner point with angle in `[0, π)`
  have hballA : ∀ (j : ℕ), j < 4 * g → ∀ V₀ : ℂ, V₀ ≠ 0 → 0 ≤ V₀.arg →
      V₀.arg < Real.pi → ‖V₀‖ < 1 → RT j V₀ ∈ Wo → ∃ ε, 0 < ε ∧
      ∀ z : ClosedDisc,
        ‖z.1 - polyVertex g ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (Complex.I * V₀)‖ < ε → z ∈ T := by
    intro j hj V₀ hV₀ne h0 hπV hV₀1 hRTW
    set c : ℤ := ((vertexSlot g ((j : ℕ) : ZMod (4 * g))).val : ℤ) with hc
    set z₀ : ℂ := polyVertex g c * Complex.exp (Complex.I * V₀) with hz₀d
    have hπ2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have hV₀im : 0 ≤ V₀.im := Complex.arg_nonneg_iff.mp h0
    have hV₀U : 0 < V₀.re ∨ 0 < V₀.im := by
      rcases lt_or_eq_of_le hV₀im with him | him
      · exact Or.inr him
      · left
        rcases lt_trichotomy V₀.re 0 with hre | hre | hre
        · exfalso
          have : V₀.arg = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre, him.symm⟩
          linarith
        · exfalso
          apply hV₀ne
          apply Complex.ext
          · simpa using hre
          · simpa using him.symm
        · exact hre
    have hreV₀ : |V₀.re| ≤ ‖V₀‖ := Complex.abs_re_le_norm V₀
    have hζ₀ : z₀ / polyVertex g c = Complex.exp (Complex.I * V₀) := by
      rw [hz₀d, mul_comm, mul_div_assoc, div_self (hpvne c), mul_one]
    have hlogexp : Complex.log (Complex.exp (Complex.I * V₀)) = Complex.I * V₀ := by
      apply Complex.log_exp
      · have him : (Complex.I * V₀).im = V₀.re := by simp [Complex.mul_im]
        rw [him]
        have := abs_le.mp hreV₀
        linarith
      · have him : (Complex.I * V₀).im = V₀.re := by simp [Complex.mul_im]
        rw [him]
        have := abs_le.mp hreV₀
        linarith
    set Vm : ℂ → ℂ := fun w => -Complex.I * Complex.log (w / polyVertex g c) with hVm
    have hVmz₀ : Vm z₀ = V₀ := by
      rw [hVm]
      simp only []
      rw [hζ₀, hlogexp]
      calc -Complex.I * (Complex.I * V₀) = -(Complex.I * Complex.I) * V₀ := by ring
        _ = V₀ := by rw [Complex.I_mul_I]; ring
    set U₁ : Set ℂ := {w : ℂ | 0 < (w / polyVertex g c).re} with hU₁
    have hU₁open : IsOpen U₁ := by
      have hcont : Continuous fun w : ℂ => (w / polyVertex g c).re :=
        Complex.continuous_re.comp (continuous_id.div_const _)
      exact isOpen_lt continuous_const hcont
    have hz₀U₁ : z₀ ∈ U₁ := by
      change 0 < (z₀ / polyVertex g c).re
      rw [hζ₀]
      rw [Complex.exp_re]
      apply mul_pos (Real.exp_pos _)
      have him : (Complex.I * V₀).im = V₀.re := by simp [Complex.mul_im]
      rw [him]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have := abs_le.mp hreV₀
        linarith
      · have := abs_le.mp hreV₀
        linarith
    have hVmcont : ContinuousOn Vm U₁ := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.clog (continuousOn_id.div_const _)
      intro w hw
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hw)
    set Up : Set ℂ := {v : ℂ | 0 < v.re ∨ 0 < v.im} with hUp
    have hUpopen : IsOpen Up := by
      have h1 : Up = {v : ℂ | 0 < v.re} ∪ {v : ℂ | 0 < v.im} := by
        rw [hUp]
        exact Set.setOf_or
      rw [h1]
      exact (isOpen_lt continuous_const Complex.continuous_re).union
        (isOpen_lt continuous_const Complex.continuous_im)
    have hUpslit : Up ⊆ Complex.slitPlane := by
      intro v hv
      apply Complex.mem_slitPlane_iff.mpr
      rcases hv with h | h
      · exact Or.inl h
      · exact Or.inr (ne_of_gt h)
    set U₂ : Set ℂ := U₁ ∩ Vm ⁻¹' (Up ∩ Metric.ball 0 1) with hU₂
    have hU₂open : IsOpen U₂ :=
      hVmcont.isOpen_inter_preimage hU₁open (hUpopen.inter isOpen_ball)
    have hz₀U₂ : z₀ ∈ U₂ := by
      refine ⟨hz₀U₁, ?_⟩
      rw [Set.mem_preimage, hVmz₀]
      refine ⟨hV₀U, ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      exact hV₀1
    have hRTcont : ContinuousOn (fun w : ℂ => RT j (Vm w)) U₂ := by
      rw [hRT]
      simp only []
      apply Complex.continuous_exp.comp_continuousOn
      apply ContinuousOn.div_const
      apply ContinuousOn.add ?_ continuousOn_const
      apply ContinuousOn.clog ((hVmcont.mono Set.inter_subset_left))
      intro w hw
      have h2 : Vm w ∈ Up := (Set.mem_preimage.mp hw.2).1
      exact hUpslit h2
    set U₃ : Set ℂ := U₂ ∩ (fun w : ℂ => RT j (Vm w)) ⁻¹' Wo with hU₃
    have hU₃open : IsOpen U₃ := hRTcont.isOpen_inter_preimage hU₂open hWopen
    have hz₀U₃ : z₀ ∈ U₃ := by
      refine ⟨hz₀U₂, ?_⟩
      rw [Set.mem_preimage, hVmz₀]
      exact hRTW
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.mp (hU₃open.mem_nhds hz₀U₃)
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    have hwU₃ : z.1 ∈ U₃ := hεsub (by rw [Metric.mem_ball, dist_eq_norm]; exact hz)
    obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hwU₃
    set V : ℂ := Vm z.1 with hVdef
    have hVU : V ∈ Up := (Set.mem_preimage.mp hw2).1
    have hzne : z.1 ≠ 0 := by
      intro hcon
      have h2 : (0 : ℝ) < ((z.1 / polyVertex g c).re) := hw1
      rw [hcon, zero_div] at h2
      simp at h2
    have hζne : z.1 / polyVertex g c ≠ 0 := div_ne_zero hzne (hpvne c)
    have hwexp : z.1 = polyVertex g c * Complex.exp (Complex.I * V) := by
      have h1 : Complex.I * V = Complex.log (z.1 / polyVertex g c) := by
        rw [hVdef, hVm]
        simp only []
        calc Complex.I * (-Complex.I * Complex.log (z.1 / polyVertex g c))
            = -(Complex.I * Complex.I) * Complex.log (z.1 / polyVertex g c) := by ring
          _ = Complex.log (z.1 / polyVertex g c) := by
              rw [Complex.I_mul_I]
              ring
      rw [h1, Complex.exp_log hζne, mul_comm]
      exact (div_mul_cancel₀ z.1 (hpvne c)).symm
    have hVim : 0 ≤ V.im := by
      have h1 : V.im = -(Complex.log (z.1 / polyVertex g c)).re := by
        rw [hVdef, hVm]
        have h2 : (-Complex.I * Complex.log (z.1 / polyVertex g c)).im
            = -(Complex.log (z.1 / polyVertex g c)).re := by
          simp [Complex.mul_im]
        exact h2
      rw [h1, Complex.log_re]
      have h2 : ‖z.1 / polyVertex g c‖ = ‖z.1‖ := by
        rw [Complex.norm_div, hvert, div_one]
      rw [h2]
      have h3 : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
      have := Real.log_nonpos (norm_nonneg _) h3
      linarith
    have hVne : V ≠ 0 := by
      intro hcon
      rcases hVU with h | h <;> rw [hcon] at h <;> simp at h
    have hVarg0 : 0 ≤ V.arg := Complex.arg_nonneg_iff.mpr hVim
    have hVargπ : V.arg < Real.pi := by
      rcases lt_or_eq_of_le (Complex.arg_le_pi V) with h | h
      · exact h
      · exfalso
        obtain ⟨hre, him⟩ := Complex.arg_eq_pi_iff.mp h
        rcases hVU with h2 | h2
        · linarith
        · linarith [him ▸ h2]
    have hu := hroot j hj V hVne hVarg0 hVargπ
    apply hzT z (RT j V) hw3
    rw [hu, hwexp]
  -- partner-ball lemma: coverage around a corner point on the clockwise ray
  have hballC : ∀ (n j₂ : ℕ), n < 4 * g → j₂ < 4 * g →
      (((j₂ : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1) →
      ∀ θ₀ : ℝ, 0 < θ₀ → θ₀ < h₀ / 2 → RT j₂ ((θ₀ : ℝ) : ℂ) ∈ Wo →
      ∃ ε, 0 < ε ∧ ∀ z : ClosedDisc,
        ‖z.1 - polyVertex g ((vertexSlot g ((n : ℕ) : ZMod (4 * g))).val : ℤ) *
          Complex.exp (-(Complex.I * ((θ₀ : ℝ) : ℂ)))‖ < ε → z ∈ T := by
    intro n j₂ hn hj₂4 hj₂c θ₀ hθ₀0 hθ₀h hRTW
    set c : ℤ := ((vertexSlot g ((n : ℕ) : ZMod (4 * g))).val : ℤ) with hc
    set z₀ : ℂ := polyVertex g c * Complex.exp (-(Complex.I * ((θ₀ : ℝ) : ℂ))) with hz₀d
    have hπ2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have hθ₀π : θ₀ < Real.pi / 2 := by
      have h1 : h₀ / 2 ≤ Real.pi / 4 := by linarith [hh2]
      linarith
    have hζ₀ : z₀ / polyVertex g c = Complex.exp (Complex.I * ((-θ₀ : ℝ) : ℂ)) := by
      rw [hz₀d, mul_comm, mul_div_assoc, div_self (hpvne c), mul_one]
      congr 1
      push_cast
      ring
    have hlogexp : Complex.log (Complex.exp (Complex.I * ((-θ₀ : ℝ) : ℂ)))
        = Complex.I * ((-θ₀ : ℝ) : ℂ) := by
      apply Complex.log_exp
      · have him : (Complex.I * ((-θ₀ : ℝ) : ℂ)).im = -θ₀ := by
          simp [Complex.mul_im]
        rw [him]
        linarith
      · have him : (Complex.I * ((-θ₀ : ℝ) : ℂ)).im = -θ₀ := by
          simp [Complex.mul_im]
        rw [him]
        linarith
    set Vm : ℂ → ℂ := fun w => -Complex.I * Complex.log (w / polyVertex g c) with hVm
    have hVmz₀ : Vm z₀ = ((-θ₀ : ℝ) : ℂ) := by
      rw [hVm]
      simp only []
      rw [hζ₀, hlogexp]
      calc -Complex.I * (Complex.I * ((-θ₀ : ℝ) : ℂ))
          = -(Complex.I * Complex.I) * ((-θ₀ : ℝ) : ℂ) := by ring
        _ = ((-θ₀ : ℝ) : ℂ) := by rw [Complex.I_mul_I]; ring
    set U₁ : Set ℂ := {w : ℂ | 0 < (w / polyVertex g c).re} with hU₁
    have hU₁open : IsOpen U₁ := by
      have hcont : Continuous fun w : ℂ => (w / polyVertex g c).re :=
        Complex.continuous_re.comp (continuous_id.div_const _)
      exact isOpen_lt continuous_const hcont
    have hz₀U₁ : z₀ ∈ U₁ := by
      change 0 < (z₀ / polyVertex g c).re
      rw [hζ₀, Complex.exp_re]
      apply mul_pos (Real.exp_pos _)
      have him : (Complex.I * ((-θ₀ : ℝ) : ℂ)).im = -θ₀ := by simp [Complex.mul_im]
      rw [him]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> [linarith; linarith]
    have hVmcont : ContinuousAt Vm z₀ := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.clog (continuousAt_id.div_const _)
      have h1 : z₀ / polyVertex g c ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.mpr (Or.inl hz₀U₁)
      exact h1
    -- the two membership certificates
    have hIm_nonneg : ∀ w : ℂ, w ∈ D → 0 ≤ (Vm w).im := by
      intro w hw
      by_cases hw0 : w = 0
      · rw [hVm]
        simp only []
        rw [hw0, zero_div, Complex.log_zero, mul_zero]
        norm_num
      · have h1 : (Vm w).im = -(Complex.log (w / polyVertex g c)).re := by
          rw [hVm]
          have h2 : (-Complex.I * Complex.log (w / polyVertex g c)).im
              = -(Complex.log (w / polyVertex g c)).re := by
            simp [Complex.mul_im]
          exact h2
        rw [h1, Complex.log_re]
        have h2 : ‖w / polyVertex g c‖ = ‖w‖ := by
          rw [Complex.norm_div, hvert, div_one]
        rw [h2]
        have h3 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
        have := Real.log_nonpos (norm_nonneg _) h3
        linarith
    -- the interior root map, continuous within `D` at `z₀`
    have hΨ₁ : ContinuousWithinAt (fun w : ℂ => RT n (Vm w)) D z₀ := by
      have hlog : ContinuousWithinAt (fun w : ℂ => Complex.log (Vm w)) D z₀ := by
        have hbase : ContinuousWithinAt Complex.log {v : ℂ | 0 ≤ v.im} (Vm z₀) := by
          rw [hVmz₀]
          apply Complex.continuousWithinAt_log_of_re_neg_of_im_zero
          · simpa using hθ₀0
          · simp
        exact hbase.comp hVmcont.continuousWithinAt hIm_nonneg
      have haff : ContinuousWithinAt (fun w : ℂ =>
          (Complex.log (Vm w) + (n : ℕ) * Real.pi * Complex.I) / ((2 * (g : ℝ) : ℝ) : ℂ)) D
          z₀ := (hlog.add continuousWithinAt_const).div_const _
      rw [hRT]
      simp only []
      exact Complex.continuous_exp.continuousAt.comp_continuousWithinAt haff
    -- its boundary value is the paired root
    have hlogneg : Complex.log ((-θ₀ : ℝ) : ℂ)
        = ((Real.log θ₀ : ℝ) : ℂ) + Real.pi * Complex.I := by
      apply Complex.ext
      · rw [Complex.log_re]
        have h1 : ‖((-θ₀ : ℝ) : ℂ)‖ = θ₀ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : -θ₀ < 0)]
          ring
        rw [h1]
        simp
      · rw [Complex.log_im, Complex.arg_ofReal_of_neg (by linarith : -θ₀ < 0)]
        simp
    have hlim : RT n ((-θ₀ : ℝ) : ℂ) = RT j₂ ((θ₀ : ℝ) : ℂ) := by
      rw [hRT]
      simp only []
      rw [hlogneg, ← Complex.ofReal_log hθ₀0.le]
      -- exponents differ by an integer multiple of `2πi`
      rw [Complex.exp_eq_exp_iff_exists_int]
      have hj₂Z : ((j₂ : ℤ) : ZMod (4 * g)) = ((n + 1 : ℤ) : ZMod (4 * g)) := by
        push_cast
        push_cast at hj₂c
        rw [hj₂c]
      rw [ZMod.intCast_eq_intCast_iff] at hj₂Z
      obtain ⟨q, hq⟩ := Int.ModEq.dvd hj₂Z
      refine ⟨q, ?_⟩
      have hqR : ((n : ℝ) + 1) - (j₂ : ℝ) = 4 * g * q := by
        have : ((n + 1 : ℤ) : ℝ) - ((j₂ : ℤ) : ℝ) = ((4 * g : ℕ) : ℝ) * (q : ℝ) := by
          exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) hq
        push_cast at this
        linarith
      have hqC : ((n : ℂ) + 1) - (j₂ : ℂ) = 4 * g * q := by exact_mod_cast hqR
      have hne : (((2 * (g : ℝ) : ℝ)) : ℂ) ≠ 0 := by
        push_cast
        intro hcon
        exact hgC (by linear_combination hcon / 2)
      field_simp
      push_cast
      linear_combination (Real.pi : ℂ) * Complex.I * hqC
    -- the jump root map, continuous at `z₀`
    have hΨ₂ : ContinuousAt (fun w : ℂ => RT j₂ ((( -(Vm w).re : ℝ)) : ℂ)) z₀ := by
      have hre : ContinuousAt (fun w : ℂ => ((( -(Vm w).re : ℝ)) : ℂ)) z₀ := by
        apply Complex.continuous_ofReal.continuousAt.comp
        exact (Complex.continuous_re.continuousAt.comp hVmcont).neg
      have hval : ((( -(Vm z₀).re : ℝ)) : ℂ) = ((θ₀ : ℝ) : ℂ) := by
        rw [hVmz₀]
        simp
      have hlogc : ContinuousAt (fun w : ℂ => Complex.log ((( -(Vm w).re : ℝ)) : ℂ)) z₀ := by
        apply ContinuousAt.clog hre
        rw [hval]
        apply Complex.mem_slitPlane_iff.mpr
        left
        simpa using hθ₀0
      rw [hRT]
      simp only []
      apply Complex.continuous_exp.continuousAt.comp
      exact (hlogc.add continuousAt_const).div_const _
    -- assemble the eventual conditions within the closed disc
    have hev1 : ∀ᶠ w in nhdsWithin z₀ D, w ∈ U₁ :=
      mem_nhdsWithin_of_mem_nhds (hU₁open.mem_nhds hz₀U₁)
    have hev2 : ∀ᶠ w in nhdsWithin z₀ D,
        Vm w ∈ Metric.ball ((( -θ₀ : ℝ)) : ℂ) (θ₀ / 2) := by
      apply mem_nhdsWithin_of_mem_nhds
      apply hVmcont
      rw [hVmz₀]
      exact isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
    have hev3 : ∀ᶠ w in nhdsWithin z₀ D,
        RT j₂ ((( -(Vm w).re : ℝ)) : ℂ) ∈ Wo := by
      apply mem_nhdsWithin_of_mem_nhds
      apply hΨ₂
      apply hWopen.mem_nhds
      have hval : ((( -(Vm z₀).re : ℝ)) : ℂ) = ((θ₀ : ℝ) : ℂ) := by
        rw [hVmz₀]
        simp
      change RT j₂ ((( -(Vm z₀).re : ℝ)) : ℂ) ∈ Wo
      rw [hval]
      exact hRTW
    have hev4 : ∀ᶠ w in nhdsWithin z₀ D, RT n (Vm w) ∈ Wo := by
      apply hΨ₁
      apply hWopen.mem_nhds
      change RT n (Vm z₀) ∈ Wo
      rw [hVmz₀, hlim]
      exact hRTW
    have hall := ((hev1.and hev2).and (hev3.and hev4))
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hall
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    have hzD : z.1 ∈ D := z.2
    have hcond := hεsub ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hz, hzD⟩
    obtain ⟨⟨hw1, hw2⟩, hw3, hw4⟩ := hcond
    set V : ℂ := Vm z.1 with hVdef
    have hVball : ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ < θ₀ / 2 := by
      have := hw2
      rwa [Metric.mem_ball, dist_eq_norm] at this
    have hVre : V.re < 0 := by
      have h1 : |V.re - (-θ₀)| ≤ ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (V - ((( -θ₀ : ℝ)) : ℂ))
        have h3 : (V - ((( -θ₀ : ℝ)) : ℂ)).re = V.re - (-θ₀) := by
          simp
        rwa [h3] at h2
      obtain ⟨h4a, h4b⟩ := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hVball))
      linarith
    set θw : ℝ := -V.re with hθw
    have hθw1 : θ₀ / 2 < θw := by
      have h1 : |V.re - (-θ₀)| ≤ ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (V - ((( -θ₀ : ℝ)) : ℂ))
        have h3 : (V - ((( -θ₀ : ℝ)) : ℂ)).re = V.re - (-θ₀) := by simp
        rwa [h3] at h2
      obtain ⟨h4a, h4b⟩ := abs_lt.mp (lt_of_le_of_lt h1 hVball)
      rw [hθw]
      linarith
    have hθw2 : θw < 3 * θ₀ / 2 := by
      have h1 : |V.re - (-θ₀)| ≤ ‖V - ((( -θ₀ : ℝ)) : ℂ)‖ := by
        have h2 := Complex.abs_re_le_norm (V - ((( -θ₀ : ℝ)) : ℂ))
        have h3 : (V - ((( -θ₀ : ℝ)) : ℂ)).re = V.re - (-θ₀) := by simp
        rwa [h3] at h2
      obtain ⟨h4a, h4b⟩ := abs_lt.mp (lt_of_le_of_lt h1 hVball)
      rw [hθw]
      linarith
    have hzne : z.1 ≠ 0 := by
      intro hcon
      have h2 : (0 : ℝ) < ((z.1 / polyVertex g c).re) := hw1
      rw [hcon, zero_div] at h2
      simp at h2
    have hζne : z.1 / polyVertex g c ≠ 0 := div_ne_zero hzne (hpvne c)
    have hwexp : z.1 = polyVertex g c * Complex.exp (Complex.I * V) := by
      have h1 : Complex.I * V = Complex.log (z.1 / polyVertex g c) := by
        rw [hVdef, hVm]
        simp only []
        calc Complex.I * (-Complex.I * Complex.log (z.1 / polyVertex g c))
            = -(Complex.I * Complex.I) * Complex.log (z.1 / polyVertex g c) := by ring
          _ = Complex.log (z.1 / polyVertex g c) := by
              rw [Complex.I_mul_I]
              ring
      rw [h1, Complex.exp_log hζne, mul_comm]
      exact (div_mul_cancel₀ z.1 (hpvne c)).symm
    have hVim : 0 ≤ V.im := hIm_nonneg z.1 hzD
    rcases lt_or_eq_of_le hVim with hVim' | hVim'
    · -- interior side: direct root in sector `n`
      have hVne : V ≠ 0 := by
        intro hcon
        rw [hcon] at hVim'
        simp at hVim'
      have hVarg0 : 0 ≤ V.arg := Complex.arg_nonneg_iff.mpr hVim
      have hVargπ : V.arg < Real.pi := by
        rcases lt_or_eq_of_le (Complex.arg_le_pi V) with h | h
        · exact h
        · exfalso
          obtain ⟨-, him⟩ := Complex.arg_eq_pi_iff.mp h
          rw [him] at hVim'
          exact absurd hVim' (lt_irrefl 0)
      have hu := hroot n hn V hVne hVarg0 hVargπ
      apply hzT z (RT n V) hw4
      rw [hu, hwexp]
    · -- boundary: jump across the ray
      have hVreal : V = ((( -θw : ℝ)) : ℂ) := by
        apply Complex.ext
        · rw [hθw]
          simp
        · rw [← hVim']
          simp
      have hθC : ((θw : ℝ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < θw := by linarith
        exact_mod_cast ne_of_gt this
      have hargθ : Complex.arg ((θw : ℝ) : ℂ) = 0 :=
        Complex.arg_ofReal_of_nonneg (by linarith)
      have hu := hroot j₂ hj₂4 ((θw : ℝ) : ℂ) hθC (by rw [hargθ]) (by rw [hargθ]; exact hπ)
      apply hzT z (RT j₂ ((θw : ℝ) : ℂ))
      · have hval : ((( -(Vm z.1).re : ℝ)) : ℂ) = ((θw : ℝ) : ℂ) := by
          rw [← hVdef, hθw]
        rw [← hval]
        exact hw3
      · rw [hu]
        have hslot2 : vertexSlot g ((j₂ : ℕ) : ZMod (4 * g))
            = vertexSlot g (((n : ℕ) : ZMod (4 * g)) + 1) := by
          rw [hj₂c]
        rw [hslot2]
        rw [← hglueθ n θw (by linarith) (by linarith)]
        congr 2
        rw [hwexp, hVreal]
        congr 1
        push_cast
        ring_nf
  -- main dispatch
  apply hopen_of_balls
  intro z₀ hz₀
  rw [hT] at hz₀
  obtain ⟨u₀, hu₀W, hfu₀⟩ := hz₀
  obtain ⟨α₀, φ₀, W₀, c, hcdef, ⟨hc0, hc4⟩, hm4, hue, hWdef, ⟨hW00, hWlt⟩, ⟨hφ0, hφπ⟩,
    hφdef, hIV, hz9, hnle, hzero⟩ := hsetup u₀ (hWsub hu₀W)
  have hrel : genusRel g
      (projDisc (polyVertex g
          ((vertexSlot g ((vertexSectorIndex g u₀ : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g u₀) * u₀ ^ (2 * g)))) z₀ :=
    Quotient.exact hfu₀
  rw [← hcdef] at hrel
  set m : ℕ := vertexSectorIndex g u₀ with hmdef
  by_cases hW₀ : W₀ = 0
  · -- the value is the vertex class
    have hu₀0 : u₀ = 0 := hzero hW₀
    have h0W : (0 : ℂ) ∈ Wo := by
      rw [← hu₀0]
      exact hu₀W
    rw [hu₀0, zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one] at hrel
    have hpvdisc : (projDisc (polyVertex g c)).1 = polyVertex g c :=
      projDisc_eq (le_of_eq (hvert c))
    have hzvert : IsPolyVertex g z₀.1 := by
      rcases hrel with h1 | ⟨k, -, hpg | hpg⟩ | ⟨-, hv'⟩
      · have hval := congrArg Subtype.val h1
        rw [hpvdisc] at hval
        exact ⟨c, hval.symm⟩
      · exact (pairGraph_vertex_iff g k hpg).mp (by rw [hpvdisc]; exact ⟨c, rfl⟩)
      · exact (pairGraph_vertex_iff g k hpg).mpr (by rw [hpvdisc]; exact ⟨c, rfl⟩)
      · exact hv'
    obtain ⟨p, hp⟩ := hzvert
    obtain ⟨ε, hε0, hball⟩ := hballB h0W p
    refine ⟨ε, hε0, ?_⟩
    intro z hz
    apply hball z
    rw [← hp]
    exact hz
  · -- positive radius
    have hW₀pos : 0 < W₀ := lt_of_le_of_ne hW00 (Ne.symm hW₀)
    set V₀ : ℂ := (((W₀ * Real.cos φ₀ : ℝ)) : ℂ) + (((W₀ * Real.sin φ₀ : ℝ)) : ℂ) * Complex.I
      with hV₀d
    have hV₀exp : V₀ = ((W₀ : ℝ) : ℂ) * Complex.exp (((φ₀ : ℝ) : ℂ) * Complex.I) := by
      rw [hV₀d, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
    have hV₀norm : ‖V₀‖ = W₀ := by
      rw [hV₀exp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW₀pos]
      have h2 : ((φ₀ : ℝ) : ℂ) * Complex.I = ((φ₀ : ℝ) : ℂ) * Complex.I := rfl
      rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    have hV₀ne : V₀ ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hV₀norm
      exact hW₀ hV₀norm.symm
    have hV₀arg : V₀.arg = φ₀ := by
      rw [hV₀exp, Complex.arg_real_mul _ hW₀pos, Complex.exp_mul_I]
      exact Complex.arg_cos_add_sin_mul_I ⟨by linarith, hφπ.le⟩
    have hV₀arg0 : 0 ≤ V₀.arg := by
      rw [hV₀arg]
      exact hφ0
    have hV₀argπ : V₀.arg < Real.pi := by
      rw [hV₀arg]
      exact hφπ
    have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
    have hV₀1 : ‖V₀‖ < 1 := by
      rw [hV₀norm]
      have h1 : h₀ / 4 ≤ Real.pi / 8 := by linarith [hh2]
      linarith
    -- the root recovers `u₀`
    have hu₀ne : u₀ ≠ 0 := by
      intro hcon
      apply hW₀
      rw [hWdef, hcon, norm_zero]
      exact zero_pow (by omega)
    have hRTV₀ : RT m V₀ = u₀ := by
      have hlogV₀ : Complex.log V₀ = ((Real.log W₀ : ℝ) : ℂ) + ((φ₀ : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · rw [Complex.log_re, hV₀norm]
          simp
        · rw [Complex.log_im, hV₀arg]
          simp
      have hnormpos : 0 < ‖u₀‖ := norm_pos_iff.mpr hu₀ne
      have hueexp : u₀
          = Complex.exp (((Real.log ‖u₀‖ : ℝ) : ℂ) + ((α₀ : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hnormpos]
        exact hue
      rw [hRT]
      simp only []
      rw [hlogV₀, hueexp]
      congr 1
      have hlogW : Real.log W₀ = 2 * g * Real.log ‖u₀‖ := by
        rw [hWdef, Real.log_pow]
        push_cast
        ring
      have hlogWC : ((Real.log W₀ : ℝ) : ℂ) = 2 * g * ((Real.log ‖u₀‖ : ℝ) : ℂ) := by
        exact_mod_cast hlogW
      have hφαR : φ₀ = 2 * g * α₀ - (m : ℝ) * Real.pi := hφdef
      have hφαC : ((φ₀ : ℝ) : ℂ) = 2 * g * ((α₀ : ℝ) : ℂ) - (m : ℂ) * Real.pi := by
        exact_mod_cast hφαR
      have hne2g : (((2 * (g : ℝ) : ℝ)) : ℂ) ≠ 0 := by
        push_cast
        intro hcon
        exact hgC (by linear_combination hcon / 2)
      field_simp
      push_cast
      linear_combination hlogWC + Complex.I * hφαC
    rcases hrel with h1 | ⟨k, hk4, hpg | hpg⟩ | ⟨hv, -⟩
    · -- clause 1: the point is the corner point itself
      have hval := congrArg Subtype.val h1
      rw [projDisc_eq hnle] at hval
      have hzform : z₀.1 = polyVertex g c * Complex.exp (Complex.I * V₀) := by
        rw [← hval, hIV]
      obtain ⟨ε, hε0, hball⟩ := hballA m hm4 V₀ hV₀ne hV₀arg0 hV₀argπ hV₀1
        (by rw [hRTV₀]; exact hu₀W)
      refine ⟨ε, hε0, ?_⟩
      intro z hz
      apply hball z
      rw [← hcdef, ← hzform]
      exact hz
    · -- pairing, order A: the corner point lies on the source arc `k`
      obtain ⟨t, -, hteq⟩ := hpg
      have ht1 := congrArg Prod.fst hteq
      have ht2 := congrArg Prod.snd hteq
      simp only at ht1 ht2
      rw [projDisc_eq hnle] at ht1
      rw [hz9] at ht1
      rw [harc2] at ht1
      obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ ht1
      have hφ00 : φ₀ = 0 := hcollapse W₀ φ₀ hW₀pos hφ0 hφπ hy₁.symm
      rw [hφ00, Real.cos_zero, mul_one] at hx₁
      have hW₀e : W₀ = h₀ * ((t : ℝ) - ((c - k + 4 * g * n₁ : ℤ) : ℝ)) := by
        push_cast
        linear_combination -hx₁ - (by rw [← h4gh] :
          2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁)
      rcases hWpin W₀ _ (t : ℝ) hW00 hWlt t.2.1 t.2.2 hW₀e with ⟨he₁, hW₀t⟩ | ⟨-, hW₀z⟩
      swap
      · exact absurd hW₀z hW₀
      -- source case: `c ≡ k`, partner corner is `c + 3`
      have hck : c - k + 4 * g * n₁ = 0 := he₁
      have hcmod : c % 4 = k % 4 := by
        have hdvd : (4 : ℤ) ∣ k - c := ⟨g * n₁, by linarith⟩
        have := Int.emod_emod_of_dvd c hdvd
        omega
      -- the predecessor sector
      set n : ℕ := if m = 0 then 4 * g - 1 else m - 1 with hn
      have hn4 : n < 4 * g := by
        rw [hn]
        split_ifs <;> omega
      have hncast : ((n : ℕ) : ZMod (4 * g)) = ((m : ℕ) : ZMod (4 * g)) - 1 := by
        rw [hn]
        split_ifs with hcase
        · rw [hcase, Nat.cast_zero, Nat.cast_sub (by omega : 1 ≤ 4 * g)]
          push_cast
          have h4g0 : (4 : ZMod (4 * g)) * (g : ZMod (4 * g)) = 0 := by
            have h5 := ZMod.natCast_self (4 * g)
            push_cast at h5
            exact h5
          rw [h4g0]
        · rw [Nat.cast_sub (by omega : 1 ≤ m)]
          push_cast
          ring
      have hj₂c : ((m : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1 := by
        rw [hncast]
        ring
      have hCm : ((c : ℤ) : ZMod (4 * g)) = vertexSlot g ((m : ℕ) : ZMod (4 * g)) := by
        rw [hcdef]
        exact hcast _
      have hsucc := vertexSlot_succ g ((n : ℕ) : ZMod (4 * g))
      rw [← hj₂c] at hsucc
      set s : ZMod (4 * g) := vertexSlot g ((n : ℕ) : ZMod (4 * g)) with hs
      have hCval : ((((c : ℤ) : ZMod (4 * g))).val : ℤ) = c := by
        rw [hCm, ← hcdef]
      have hsn : s = ((c + 3 : ℤ) : ZMod (4 * g)) := by
        by_cases hcond : ((s - 1).val % 4 = 0 ∨ (s - 1).val % 4 = 1)
        · exfalso
          have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s + 1 := by
            rw [hsucc]
            unfold pairInv
            rw [if_pos hcond]
            ring
          have h2 : s - 1 = ((c : ℤ) : ZMod (4 * g)) - 2 := by
            rw [hCm, h1]
            ring
          rw [h2, hminus2] at hcond
          omega
        · have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s - 3 := by
            rw [hsucc]
            unfold pairInv
            rw [if_neg hcond]
            ring
          have h2 : s = ((c : ℤ) : ZMod (4 * g)) + 3 := by
            rw [hCm, h1]
            ring
          rw [h2]
          push_cast
          ring
      obtain ⟨q₂, hq₂⟩ : ∃ q₂ : ℤ, ((s.val : ℤ)) = c + 3 + 4 * g * q₂ := by
        have h1 : ((s.val : ℤ) : ZMod (4 * g)) = ((c + 3 : ℤ) : ZMod (4 * g)) := by
          rw [hcast s, hsn]
        rw [ZMod.intCast_eq_intCast_iff] at h1
        obtain ⟨q₂, hq₂⟩ := Int.ModEq.dvd h1
        refine ⟨-q₂, ?_⟩
        push_cast at hq₂ ⊢
        linarith
      have hz₀form : z₀.1 = polyVertex g ((s.val : ℤ)) *
          Complex.exp (-(Complex.I * ((W₀ : ℝ) : ℂ))) := by
        rw [hcornerexp]
        rw [← ht2, harc2]
        rw [Complex.ofReal_zero, zero_mul, add_zero]
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨n₁ - q₂, ?_⟩
        have hq₂R : ((s.val : ℤ) : ℝ) = c + 3 + 4 * g * q₂ := by exact_mod_cast hq₂
        have hckR : (c : ℝ) - k + 4 * g * n₁ = 0 := by exact_mod_cast hck
        have h2πR : 2 * Real.pi = 4 * (g : ℝ) * h₀ := by linarith [h4gh]
        have hreal : h₀ * (((k : ℝ) + 2) + (1 - (t : ℝ)))
            = (h₀ * ((s.val : ℤ) : ℝ) - W₀) + 2 * Real.pi * ((n₁ : ℝ) - q₂) := by
          rw [hq₂R, hW₀t, h2πR]
          linear_combination (-h₀) * hckR
        have hC : ((h₀ * (((k : ℝ) + 2) + (1 - (t : ℝ))) : ℝ) : ℂ)
            = ((h₀ * ((s.val : ℤ) : ℝ) - W₀ : ℝ) : ℂ)
              + 2 * Real.pi * (((n₁ : ℝ) - q₂ : ℝ) : ℂ) := by
          exact_mod_cast hreal
        push_cast at hC ⊢
        linear_combination Complex.I * hC
      have hW₀h2 : W₀ < h₀ / 2 := by linarith
      have hRTW₀ : RT m ((W₀ : ℝ) : ℂ) ∈ Wo := by
        have hV₀W : V₀ = ((W₀ : ℝ) : ℂ) := by
          rw [hV₀d, hφ00]
          simp
        rw [← hV₀W, hRTV₀]
        exact hu₀W
      obtain ⟨ε, hε0, hball⟩ := hballC n m hn4 hm4 hj₂c W₀ hW₀pos hW₀h2 hRTW₀
      refine ⟨ε, hε0, ?_⟩
      intro z hz
      apply hball z
      rw [← hz₀form]
      exact hz
    · -- pairing, order B: the point lies on the source arc `k`
      obtain ⟨t, -, hteq⟩ := hpg
      have ht1 := congrArg Prod.fst hteq
      have ht2 := congrArg Prod.snd hteq
      simp only at ht1 ht2
      rw [projDisc_eq hnle] at ht2
      rw [hz9] at ht2
      rw [harc2] at ht2
      obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ ht2
      have hφ00 : φ₀ = 0 := hcollapse W₀ φ₀ hW₀pos hφ0 hφπ hy₁.symm
      rw [hφ00, Real.cos_zero, mul_one] at hx₁
      have hW₀e : W₀ = h₀ * ((1 - (t : ℝ)) - ((c - (k + 2) + 4 * g * n₁ : ℤ) : ℝ)) := by
        push_cast
        push_cast at hx₁
        linear_combination -hx₁ - (by rw [← h4gh] :
          2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁)
      rcases hWpin W₀ _ (1 - (t : ℝ)) hW00 hWlt (by linarith [t.2.2]) (by linarith [t.2.1])
        hW₀e with ⟨he₁, hW₀t⟩ | ⟨-, hW₀z⟩
      swap
      · exact absurd hW₀z hW₀
      have hck : c - (k + 2) + 4 * g * n₁ = 0 := he₁
      have hcmod : c % 4 = (k + 2) % 4 := by
        have hdvd : (4 : ℤ) ∣ (k + 2) - c := ⟨(g : ℤ) * n₁, by linarith⟩
        exact Int.modEq_iff_dvd.mpr hdvd
      set n : ℕ := if m = 0 then 4 * g - 1 else m - 1 with hn
      have hn4 : n < 4 * g := by
        rw [hn]
        split_ifs <;> omega
      have hncast : ((n : ℕ) : ZMod (4 * g)) = ((m : ℕ) : ZMod (4 * g)) - 1 := by
        rw [hn]
        split_ifs with hcase
        · rw [hcase, Nat.cast_zero, Nat.cast_sub (by omega : 1 ≤ 4 * g)]
          push_cast
          have h4g0 : (4 : ZMod (4 * g)) * (g : ZMod (4 * g)) = 0 := by
            have h5 := ZMod.natCast_self (4 * g)
            push_cast at h5
            exact h5
          rw [h4g0]
        · rw [Nat.cast_sub (by omega : 1 ≤ m)]
          push_cast
          ring
      have hj₂c : ((m : ℕ) : ZMod (4 * g)) = ((n : ℕ) : ZMod (4 * g)) + 1 := by
        rw [hncast]
        ring
      have hCm : ((c : ℤ) : ZMod (4 * g)) = vertexSlot g ((m : ℕ) : ZMod (4 * g)) := by
        rw [hcdef]
        exact hcast _
      have hsucc := vertexSlot_succ g ((n : ℕ) : ZMod (4 * g))
      rw [← hj₂c] at hsucc
      set s : ZMod (4 * g) := vertexSlot g ((n : ℕ) : ZMod (4 * g)) with hs
      have hCval : ((((c : ℤ) : ZMod (4 * g))).val : ℤ) = c := by
        rw [hCm, ← hcdef]
      have hsn : s = ((c - 1 : ℤ) : ZMod (4 * g)) := by
        by_cases hcond : ((s - 1).val % 4 = 0 ∨ (s - 1).val % 4 = 1)
        · have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s + 1 := by
            rw [hsucc]
            unfold pairInv
            rw [if_pos hcond]
            ring
          have h2 : s = ((c : ℤ) : ZMod (4 * g)) - 1 := by
            rw [hCm, h1]
            ring
          rw [h2]
          push_cast
          ring
        · exfalso
          have h1 : vertexSlot g ((m : ℕ) : ZMod (4 * g)) = s - 3 := by
            rw [hsucc]
            unfold pairInv
            rw [if_neg hcond]
            ring
          have h2 : s - 1 = ((c : ℤ) : ZMod (4 * g)) + 2 := by
            rw [hCm, h1]
            ring
          rw [h2, hplus2] at hcond
          omega
      obtain ⟨q₂, hq₂⟩ : ∃ q₂ : ℤ, ((s.val : ℤ)) = c - 1 + 4 * g * q₂ := by
        have h1 : ((s.val : ℤ) : ZMod (4 * g)) = ((c - 1 : ℤ) : ZMod (4 * g)) := by
          rw [hcast s, hsn]
        rw [ZMod.intCast_eq_intCast_iff] at h1
        obtain ⟨q₂, hq₂⟩ := Int.ModEq.dvd h1
        refine ⟨-q₂, ?_⟩
        push_cast at hq₂ ⊢
        linarith
      have hz₀form : z₀.1 = polyVertex g ((s.val : ℤ)) *
          Complex.exp (-(Complex.I * ((W₀ : ℝ) : ℂ))) := by
        rw [hcornerexp]
        rw [← ht1, harc2]
        rw [Complex.ofReal_zero, zero_mul, add_zero]
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨n₁ - q₂, ?_⟩
        have hq₂R : ((s.val : ℤ) : ℝ) = c - 1 + 4 * g * q₂ := by exact_mod_cast hq₂
        have hckR : (c : ℝ) - (k + 2) + 4 * g * n₁ = 0 := by exact_mod_cast hck
        have h2πR : 2 * Real.pi = 4 * (g : ℝ) * h₀ := by linarith [h4gh]
        have hreal : h₀ * ((k : ℝ) + (t : ℝ))
            = (h₀ * ((s.val : ℤ) : ℝ) - W₀) + 2 * Real.pi * ((n₁ : ℝ) - q₂) := by
          rw [hq₂R, hW₀t, h2πR]
          linear_combination (-h₀) * hckR
        have hC : ((h₀ * ((k : ℝ) + (t : ℝ)) : ℝ) : ℂ)
            = ((h₀ * ((s.val : ℤ) : ℝ) - W₀ : ℝ) : ℂ)
              + 2 * Real.pi * (((n₁ : ℝ) - q₂ : ℝ) : ℂ) := by
          exact_mod_cast hreal
        push_cast at hC ⊢
        linear_combination Complex.I * hC
      have hW₀h2 : W₀ < h₀ / 2 := by linarith
      have hRTW₀ : RT m ((W₀ : ℝ) : ℂ) ∈ Wo := by
        have hV₀W : V₀ = ((W₀ : ℝ) : ℂ) := by
          rw [hV₀d, hφ00]
          simp
        rw [← hV₀W, hRTV₀]
        exact hu₀W
      obtain ⟨ε, hε0, hball⟩ := hballC n m hn4 hm4 hj₂c W₀ hW₀pos hW₀h2 hRTW₀
      refine ⟨ε, hε0, ?_⟩
      intro z hz
      apply hball z
      rw [← hz₀form]
      exact hz
    · -- vertex clause is impossible at positive radius
      exfalso
      obtain ⟨p, hp⟩ := hv
      rw [projDisc_eq hnle, hz9, hpv2 p] at hp
      obtain ⟨n₁, hx₁, hy₁⟩ := hkey _ _ _ _ hp
      have hφ00 : φ₀ = 0 := hcollapse W₀ φ₀ hW₀pos hφ0 hφπ hy₁
      rw [hφ00, Real.cos_zero, mul_one] at hx₁
      have hW₀e : W₀ = h₀ * ((0 : ℝ) - ((c - p - 4 * g * n₁ : ℤ) : ℝ)) := by
        push_cast
        linear_combination hx₁ + (by rw [← h4gh] :
          2 * Real.pi * (n₁ : ℝ) = 4 * g * h₀ * n₁)
      rcases hWpin W₀ _ 0 hW00 hWlt le_rfl (by norm_num) hW₀e with ⟨-, hW₀t⟩ | ⟨h01, -⟩
      · rw [mul_zero] at hW₀t
        exact hW₀ hW₀t
      · exact absurd h01 (by norm_num)

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
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  haveI : NeZero (4 * g) := ⟨by omega⟩
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
  obtain ⟨z, rfl⟩ := Quotient.exists_rep p
  have hz1 : ‖z.1‖ ≤ 1 := by
    have hz2 := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at hz2
  rcases lt_or_eq_of_le hz1 with hlt | hcirc
  · -- Interior point: the interior chart.
    left
    rw [interiorChart_source]
    exact ⟨z, hlt, rfl⟩
  · -- Boundary point: write `z.1 = arcPoint g m t` with `t ∈ [0, 1)`.
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 2 * g * Complex.arg z.1 / Real.pi := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌊x⌋ := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x - m := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by
      rw [ht, hm]
      exact sub_nonneg.mpr (Int.floor_le x)
    have ht1 : t < 1 := by
      rw [ht, hm]
      have := Int.lt_floor_add_one x
      linarith
    have h1exp := Complex.norm_mul_exp_arg_mul_I z.1
    rw [hcirc, Complex.ofReal_one, one_mul] at h1exp
    have harcz : arcPoint g m t = z.1 := by
      have hmt : (m : ℝ) + t = x := by rw [ht]; ring
      have hang : Real.pi * ((m : ℝ) + t) / (2 * g) = Complex.arg z.1 := by
        rw [hmt, hx]
        field_simp
      rw [← h1exp]
      unfold arcPoint
      congr 1
      have hangC := congrArg (fun r : ℝ => (r : ℂ)) hang
      push_cast at hangC
      linear_combination Complex.I * hangC
    rcases eq_or_lt_of_le ht0 with ht0' | htpos
    · -- Vertex: `t = 0`, so `z` is a vertex and lies in the vertex chart.
      right; right
      have hzv : z.1 = polyVertex g m := by
        rw [← harcz, ← ht0']
        exact arcPoint_zero g m
      have hsrc : (vertexChart g).source
          = vertexChartFun g '' Metric.ball 0 (vertexRadius g) := rfl
      rw [hsrc]
      refine ⟨0, Metric.mem_ball_self (vertexRadius_pos g), ?_⟩
      have hidx : vertexSectorIndex g 0 = 0 := by
        unfold vertexSectorIndex
        rw [Complex.arg_zero]
        simp
      have hfun0 : vertexChartFun g 0
          = Quotient.mk (genusSetoid g) (projDisc (polyVertex g 0)) := by
        unfold vertexChartFun
        rw [hidx]
        rw [Nat.cast_zero, vertexSlot_zero, ZMod.val_zero, Nat.cast_zero, pow_zero,
          mul_one, zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one]
      rw [hfun0]
      have hrel : genusRel g (projDisc (polyVertex g 0)) z :=
        Or.inr (Or.inr ⟨⟨0, projDisc_eq (hvert 0).le⟩, ⟨m, hzv⟩⟩)
      exact Quotient.sound hrel
    · -- Edge-interior: `0 < t < 1`, so `z` lies in an edge chart.
      right; left
      obtain ⟨m', hm'⟩ : ∃ m' : ℤ, m' = m % (4 * g) := ⟨_, rfl⟩
      have hgZ : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg1
      have h4g : (0 : ℤ) < 4 * (g : ℤ) := by linarith
      have hm'0 : 0 ≤ m' := hm' ▸ Int.emod_nonneg m (ne_of_gt h4g)
      have hm'lt : m' < 4 * g := hm' ▸ Int.emod_lt_of_pos m h4g
      have harcz' : arcPoint g m' t = z.1 := by
        rw [← harcz, arcPoint_eq_iff]
        refine ⟨-(m / (4 * g)), ?_⟩
        have hZ : m' - m = (4 * g : ℤ) * (-(m / (4 * g))) := by
          rw [hm', Int.emod_def]
          ring
        have hR : (m' : ℝ) - (m : ℝ) = (4 * (g : ℝ)) * (-(((m / (4 * g) : ℤ)) : ℝ)) := by
          exact_mod_cast hZ
        push_cast
        linarith [hR]
      have main : ∀ k : ℤ, 0 ≤ k → k < 4 * g → (k % 4 = 0 ∨ k % 4 = 1) →
          (∃ u ∈ edgeSector g k, edgeChartFun g k u = Quotient.mk (genusSetoid g) z) →
          ∃ jb : Fin g × Bool,
            Quotient.mk (genusSetoid g) z ∈ (edgeChart g jb.1 jb.2).source := by
        intro k hk0 hklt hk4 hex
        obtain ⟨u, hu, hfu⟩ := hex
        have hjlt : (k / 4).toNat < g := by omega
        obtain ⟨b, hb⟩ : ∃ b : Bool, (if b then (1 : ℤ) else 0) = k % 4 := by
          rcases hk4 with h | h
          · exact ⟨false, by rw [if_neg Bool.false_ne_true, h]⟩
          · exact ⟨true, by rw [if_pos rfl, h]⟩
        have hgoal : Quotient.mk (genusSetoid g) z
            ∈ (edgeChart g ⟨(k / 4).toNat, hjlt⟩ b).source := by
          have hidx : (4 * ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) + if b then 1 else 0)
              = k := by
            have h1 : ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) = ((k / 4).toNat : ℤ) := rfl
            rw [h1, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k / 4), hb]
            omega
          have hsrc : (edgeChart g ⟨(k / 4).toNat, hjlt⟩ b).source
              = edgeChartFun g
                  (4 * ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) + if b then 1 else 0) ''
                edgeSector g
                  (4 * ((⟨(k / 4).toNat, hjlt⟩ : Fin g) : ℤ) + if b then 1 else 0) := rfl
          rw [hsrc, hidx]
          exact ⟨u, hu, hfu⟩
        exact ⟨(⟨(k / 4).toNat, hjlt⟩, b), hgoal⟩
      have hdisj : (m' % 4 = 0 ∨ m' % 4 = 1) ∨
          ((m' - 2) % 4 = 0 ∨ (m' - 2) % 4 = 1) := by omega
      rcases hdisj with hA | hB
      · -- `z` lies on a source arc `m'`.
        refine main m' hm'0 hm'lt hA ⟨arcPoint g m' t, ?_, ?_⟩
        · exact ⟨1, (m' : ℝ) + t, by norm_num, by norm_num, by linarith, by linarith, by
            rw [Complex.ofReal_one, one_mul]
            unfold arcPoint
            congr 1
            push_cast
            ring⟩
        · unfold edgeChartFun
          rw [if_pos (harc m' t).le]
          exact congrArg (Quotient.mk (genusSetoid g)) (Subtype.ext (by
            rw [projDisc_eq (harc m' t).le]
            exact harcz'))
      · -- `z` lies on the target arc `m' = (m' - 2) + 2`: use the pairing.
        have hk0 : (0 : ℤ) ≤ m' - 2 := by omega
        have hklt : m' - 2 < 4 * g := by omega
        refine main (m' - 2) hk0 hklt hB ⟨arcPoint g (m' - 2) (1 - t), ?_, ?_⟩
        · exact ⟨1, ((m' - 2 : ℤ) : ℝ) + (1 - t), by norm_num, by norm_num, by linarith,
            by linarith, by
              rw [Complex.ofReal_one, one_mul]
              unfold arcPoint
              congr 1
              push_cast
              ring⟩
        · unfold edgeChartFun
          rw [if_pos (harc (m' - 2) (1 - t)).le]
          have hpair : ((projDisc (arcPoint g (m' - 2) (1 - t))).1, z.1)
              ∈ pairGraph g (m' - 2) := by
            refine ⟨⟨1 - t, Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩,
              Set.mem_univ _, ?_⟩
            have hfst : arcPoint g (m' - 2) (1 - t)
                = (projDisc (arcPoint g (m' - 2) (1 - t))).1 :=
              (projDisc_eq (harc (m' - 2) (1 - t)).le).symm
            have hsnd : arcPoint g ((m' - 2) + 2) (1 - (1 - t)) = z.1 := by
              rw [(by ring : (m' - 2) + 2 = m'), (by ring : 1 - (1 - t) = t)]
              exact harcz'
            simp only [Prod.mk.injEq]
            exact ⟨hfst, hsnd⟩
          have hrel : genusRel g (projDisc (arcPoint g (m' - 2) (1 - t))) z :=
            Or.inr (Or.inl ⟨m' - 2, hB, Or.inl hpair⟩)
          exact Quotient.sound hrel

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
  unfold genusChartAt
  split_ifs with h1 h2
  · exact h1
  · exact h2.choose_spec
  · rcases chart_sources_cover g p with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact h

/-- The preferred chart belongs to the atlas. -/
theorem genusChartAt_mem_atlas (g : ℕ) [NeZero g] (p : GenusSurface g) :
    genusChartAt g p ∈ genusAtlas g := by
  unfold genusChartAt genusAtlas
  split_ifs with h1 h2
  · exact Set.mem_union_left _ (Set.mem_union_left _ rfl)
  · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨h2.choose, rfl⟩)
  · exact Set.mem_union_right _ rfl

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
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  haveI : NeZero (4 * g) := ⟨by omega⟩
  set c := vertexSlot g (m : ZMod (4 * g)) with hc
  set v := c.val with hv
  have hvlt : v < 4 * g := ZMod.val_lt c
  -- `v ≥ 1`: otherwise the source-arc hypothesis reads `(-1) % 4 ∈ {0, 1}`.
  have hv1 : 1 ≤ v := by
    by_contra hcon
    have hv0 : v = 0 := by omega
    rw [hv0] at hsrc
    omega
  -- `v ≠ 4g - 1`: otherwise the hypothesis reads `(4g - 2) % 4 = 2 ∈ {0, 1}`.
  have hvne : v ≠ 4 * g - 1 := by
    intro hcon
    have h2 : (((v : ℤ)) - 1) % 4 = 2 := by omega
    omega
  have hvsucc : v + 1 < 4 * g := by omega
  -- The successor slot is `c + 1`.
  have hsub1 : c - 1 = ((v - 1 : ℕ) : ZMod (4 * g)) := by
    have hcv : ((v : ℕ) : ZMod (4 * g)) = c := ZMod.natCast_rightInverse c
    rw [← hcv, Nat.cast_sub hv1, Nat.cast_one]
  have hpair : vertexSlot g ((m : ZMod (4 * g)) + 1) = c + 1 := by
    rw [vertexSlot_succ, ← hc, hsub1]
    unfold pairInv
    rw [ZMod.val_cast_of_lt (by omega : v - 1 < 4 * g)]
    rw [if_pos (by omega : (v - 1) % 4 = 0 ∨ (v - 1) % 4 = 1)]
    have hcv : ((v : ℕ) : ZMod (4 * g)) = c := ZMod.natCast_rightInverse c
    rw [← hcv, Nat.cast_sub hv1, Nat.cast_one]
    ring
  have hval : (vertexSlot g ((m : ZMod (4 * g)) + 1)).val = v + 1 := by
    rw [hpair]
    have hcv : ((v : ℕ) : ZMod (4 * g)) = c := ZMod.natCast_rightInverse c
    rw [← hcv, ← Nat.cast_one, ← Nat.cast_add]
    exact ZMod.val_cast_of_lt hvsucc
  rw [hval]
  unfold polyVertex
  rw [div_eq_iff (Complex.exp_ne_zero _), ← Complex.exp_add]
  congr 1
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  push_cast
  ring

set_option maxHeartbeats 400000 in
-- The single proof elaborates the full 3-family × 3-family transition case analysis
-- (interior/edge/vertex charts, with the two-sided ray analysis of the vertex chart);
-- the default 200000 heartbeats are exhausted during the final case dispatch.
/-- Every transition map of the genus-surface atlas is analytic with
nonvanishing derivative on its source: each overlap component carries a
single formula `id`, `u ↦ ω/u`, or `u ↦ A · exp (± i u^(2g))`. -/
theorem transition_analyticAt (g : ℕ) [NeZero g] :
    ∀ e ∈ atlas ℂ (GenusSurface g), ∀ e' ∈ atlas ℂ (GenusSurface g),
      ∀ z ∈ (e.symm.trans e').source,
        AnalyticAt ℂ (e.symm.trans e') z ∧ deriv (e.symm.trans e') z ≠ 0 := by
  have hg1 : 1 ≤ g := Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg1
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  haveI : NeZero (4 * g) := ⟨by omega⟩
  -- ## Norm facts
  have hnorm1 : ∀ s : ℝ, ‖Complex.exp (Real.pi * (s : ℂ) * Complex.I / (2 * g))‖ = 1 := by
    intro s
    have h : (Real.pi * (s : ℂ) * Complex.I / (2 * g))
        = ((Real.pi * s / (2 * g) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hvertnorm : ∀ m : ℤ, ‖polyVertex g m‖ = 1 := by
    intro m
    have hrw : polyVertex g m
        = Complex.exp (Real.pi * ((m : ℝ) : ℂ) * Complex.I / (2 * g)) := by
      unfold polyVertex
      norm_num
    rw [hrw, hnorm1]
  have harcnorm : ∀ (k : ℤ) (t : ℝ), ‖arcPoint g k t‖ = 1 := by
    intro k t
    have hrw : arcPoint g k t
        = Complex.exp (Real.pi * (((k : ℝ) + t : ℝ) : ℂ) * Complex.I / (2 * g)) := by
      unfold arcPoint
      norm_num
    rw [hrw, hnorm1]
  have hωnorm : ∀ k : ℤ,
      ‖Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))‖ = 1 := by
    intro k
    have hrw : (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))
        = Real.pi * (((2 * (k : ℝ) + 3 : ℝ)) : ℂ) * Complex.I / (2 * g) := by
      push_cast
      ring
    rw [hrw, hnorm1]
  have hσnorm : ∀ (k : ℤ) (u : ℂ), ‖sidePairing g k u‖ = 1 / ‖u‖ := by
    intro k u
    unfold sidePairing
    rw [norm_div, hωnorm]
  -- ## Interior classes are singletons
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
      rw [← h1, harcnorm] at hz
      exact absurd hz (lt_irrefl 1)
    · obtain ⟨s, -, hs⟩ := h
      have h1 : arcPoint g (k + 2) (1 - (s : ℝ)) = z.1 := congrArg Prod.snd hs
      rw [← h1, harcnorm] at hz
      exact absurd hz (lt_irrefl 1)
    · rw [hm, hvertnorm] at hz
      exact absurd hz (lt_irrefl 1)
  -- ## Interior representative extraction
  have hintRep : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ ≤ 1 →
      Quotient.mk (genusSetoid g) (projDisc y) = Quotient.mk (genusSetoid g) (projDisc x) →
      y = x := by
    intro x y hx hy h
    have hrel : genusRel g (projDisc x) (projDisc y) :=
      (genusRel_equivalence g).symm (Quotient.exact h)
    have heq := hsingle (projDisc x) (projDisc y)
      (by rw [projDisc_eq hx.le]; exact hx) hrel
    have hval := congrArg Subtype.val heq
    rw [projDisc_eq hx.le, projDisc_eq hy] at hval
    exact hval.symm
  -- ## Edge chart pieces
  have hEFin : ∀ (k : ℤ) (u : ℂ), ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc u) := by
    intro k u h
    unfold edgeChartFun
    rw [if_pos h]
  have hEFout : ∀ (k : ℤ) (u : ℂ), ¬ ‖u‖ ≤ 1 →
      edgeChartFun g k u = Quotient.mk (genusSetoid g) (projDisc (sidePairing g k u)) := by
    intro k u h
    unfold edgeChartFun
    rw [if_neg h]
  -- Identify the preimage of an interior class under an edge-chart inverse.
  have hedgeW : ∀ (k : ℤ) (x w : ℂ), ‖x‖ < 1 →
      edgeChartFun g k w = Quotient.mk (genusSetoid g) (projDisc x) →
      (‖w‖ ≤ 1 ∧ w = x) ∨ (1 < ‖w‖ ∧ x ≠ 0 ∧ w = sidePairing g k x) := by
    intro k x w hx h
    by_cases hcase : ‖w‖ ≤ 1
    · rw [hEFin k w hcase] at h
      exact Or.inl ⟨hcase, hintRep x w hx hcase h⟩
    · rw [hEFout k w hcase] at h
      push Not at hcase
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hcase
        linarith
      have hσle : ‖sidePairing g k w‖ ≤ 1 := by
        rw [hσnorm]
        rw [div_le_one (lt_trans one_pos hcase)]
        linarith
      have hσw : sidePairing g k w = x := hintRep x _ hx hσle h
      have hx0 : x ≠ 0 := by
        intro h0
        have hn : ‖sidePairing g k w‖ = 0 := by rw [hσw, h0, norm_zero]
        rw [hσnorm k w] at hn
        have hwpos : (0 : ℝ) < ‖w‖ := lt_trans one_pos hcase
        rw [div_eq_zero_iff] at hn
        rcases hn with h1 | h1
        · exact one_ne_zero h1
        · linarith
      have hww : w = sidePairing g k x := by
        rw [← hσw, sidePairing_involutive g k hw0]
      exact Or.inr ⟨hcase, hx0, hww⟩
  -- ## Arc separation bricks
  have harc_eq : ∀ (a b : ℤ) (t s : ℝ), -1 < t - s → t - s < 1 →
      arcPoint g a t = arcPoint g b s →
      t = s ∧ (a : ZMod (4 * g)) = (b : ZMod (4 * g)) := by
    intro a b t s h1 h2 heq
    obtain ⟨n, hn⟩ := (arcPoint_eq_iff g a b t s).mp heq
    push_cast at hn
    have hts : t - s = ((4 * g * n - a + b : ℤ) : ℝ) := by
      push_cast
      linarith
    have hJ0 : (4 * (g : ℤ) * n - a + b) = 0 := by
      have hlb : (-1 : ℝ) < ((4 * g * n - a + b : ℤ) : ℝ) := by
        rw [← hts]
        exact h1
      have hub : ((4 * g * n - a + b : ℤ) : ℝ) < 1 := by
        rw [← hts]
        exact h2
      have hlb' : (-1 : ℤ) < 4 * (g : ℤ) * n - a + b := by exact_mod_cast hlb
      have hub' : 4 * (g : ℤ) * n - a + b < 1 := by exact_mod_cast hub
      omega
    have hts0 : t - s = 0 := by
      rw [hts, hJ0]
      norm_num
    refine ⟨by linarith, ?_⟩
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    push_cast
    linear_combination hJ0
  have hnotvert : ∀ (a : ℤ) (t : ℝ), 0 < t → t < 1 → ¬ IsPolyVertex g (arcPoint g a t) := by
    intro a t ht0 ht1 ⟨mv, hmv⟩
    rw [← arcPoint_zero g mv] at hmv
    obtain ⟨ht, -⟩ := harc_eq a mv t 0 (by linarith) (by linarith) hmv
    linarith
  -- The class of an open-arc point never meets the vertex class.
  have hvert_rel : ∀ (a : ℤ) (t : ℝ), 0 < t → t < 1 → ∀ mv : ℤ,
      ¬ genusRel g (projDisc (arcPoint g a t)) (projDisc (polyVertex g mv)) := by
    intro a t ht0 ht1 mv hrel
    have hva : (projDisc (arcPoint g a t)).1 = arcPoint g a t :=
      projDisc_eq (harcnorm a t).le
    have hvv : (projDisc (polyVertex g mv)).1 = polyVertex g mv :=
      projDisc_eq (hvertnorm mv).le
    have hrel' : projDisc (arcPoint g a t) = projDisc (polyVertex g mv)
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            (((projDisc (arcPoint g a t)).1, (projDisc (polyVertex g mv)).1) ∈ pairGraph g k ∨
             ((projDisc (polyVertex g mv)).1, (projDisc (arcPoint g a t)).1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g (projDisc (arcPoint g a t)).1
            ∧ IsPolyVertex g (projDisc (polyVertex g mv)).1) := hrel
    rcases hrel' with h | ⟨k, -, h | h⟩ | ⟨h, -⟩
    · have := congrArg Subtype.val h
      rw [hva, hvv] at this
      exact hnotvert a t ht0 ht1 ⟨mv, this⟩
    · rw [hva, hvv] at h
      have hiff := pairGraph_vertex_iff g k h
      exact hnotvert a t ht0 ht1 (hiff.mpr ⟨mv, rfl⟩)
    · rw [hva, hvv] at h
      have hiff := pairGraph_vertex_iff g k h
      exact hnotvert a t ht0 ht1 (hiff.mp ⟨mv, rfl⟩)
    · rw [hva] at h
      exact hnotvert a t ht0 ht1 h
  -- Full relation analysis between two open-arc points.
  have harc_rel : ∀ (a b : ℤ) (t s : ℝ), 0 < t → t < 1 → 0 < s → s < 1 →
      genusRel g (projDisc (arcPoint g a t)) (projDisc (arcPoint g b s)) →
      ((b : ZMod (4 * g)) = (a : ZMod (4 * g)) ∧ s = t) ∨
      (∃ k₀ : ℤ, (k₀ % 4 = 0 ∨ k₀ % 4 = 1) ∧
        (((a : ZMod (4 * g)) = (k₀ : ZMod (4 * g)) ∧
            (b : ZMod (4 * g)) = ((k₀ + 2 : ℤ) : ZMod (4 * g)) ∧ s = 1 - t) ∨
         ((b : ZMod (4 * g)) = (k₀ : ZMod (4 * g)) ∧
            (a : ZMod (4 * g)) = ((k₀ + 2 : ℤ) : ZMod (4 * g)) ∧ s = 1 - t))) := by
    intro a b t s ht0 ht1 hs0 hs1 hrel
    have hva : (projDisc (arcPoint g a t)).1 = arcPoint g a t :=
      projDisc_eq (harcnorm a t).le
    have hvb : (projDisc (arcPoint g b s)).1 = arcPoint g b s :=
      projDisc_eq (harcnorm b s).le
    have hrel' : projDisc (arcPoint g a t) = projDisc (arcPoint g b s)
        ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
            (((projDisc (arcPoint g a t)).1, (projDisc (arcPoint g b s)).1) ∈ pairGraph g k ∨
             ((projDisc (arcPoint g b s)).1, (projDisc (arcPoint g a t)).1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g (projDisc (arcPoint g a t)).1
            ∧ IsPolyVertex g (projDisc (arcPoint g b s)).1) := hrel
    rcases hrel' with h | ⟨k, hk, h | h⟩ | ⟨h, -⟩
    · have hval := congrArg Subtype.val h
      rw [hva, hvb] at hval
      obtain ⟨hts, hab⟩ := harc_eq a b t s (by linarith) (by linarith) hval
      exact Or.inl ⟨hab.symm, hts.symm⟩
    · -- (arc a, arc b) matched by pairGraph k: a ≡ k, b ≡ k+2, s = 1 - t.
      obtain ⟨τ, -, hτ⟩ := h
      have h1 : arcPoint g k (τ : ℝ) = arcPoint g a t := by
        rw [← hva]
        exact congrArg Prod.fst hτ
      have h2 : arcPoint g (k + 2) (1 - (τ : ℝ)) = arcPoint g b s := by
        rw [← hvb]
        exact congrArg Prod.snd hτ
      obtain ⟨hτt, hka⟩ := harc_eq k a (τ : ℝ) t
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h1
      obtain ⟨hτs, hkb⟩ := harc_eq (k + 2) b (1 - (τ : ℝ)) s
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h2
      refine Or.inr ⟨k, hk, Or.inl ⟨hka.symm, hkb.symm, ?_⟩⟩
      rw [← hτs, hτt]
    · obtain ⟨τ, -, hτ⟩ := h
      have h1 : arcPoint g k (τ : ℝ) = arcPoint g b s := by
        rw [← hvb]
        exact congrArg Prod.fst hτ
      have h2 : arcPoint g (k + 2) (1 - (τ : ℝ)) = arcPoint g a t := by
        rw [← hva]
        exact congrArg Prod.snd hτ
      obtain ⟨hτs, hkb⟩ := harc_eq k b (τ : ℝ) s
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h1
      obtain ⟨hτt, hka⟩ := harc_eq (k + 2) a (1 - (τ : ℝ)) t
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith)
        (by have hτa := τ.2.1; have hτb := τ.2.2; linarith) h2
      refine Or.inr ⟨k, hk, Or.inr ⟨hkb.symm, hka.symm, ?_⟩⟩
      rw [← hτs]
      linarith [hτt]
    · rw [hva] at h
      exact absurd h (hnotvert a t ht0 ht1)
  -- ## ZMod-to-exponential bridges
  have hzmodDvd : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      ∃ q : ℤ, a - b = 4 * g * q := by
    intro a b hab
    rw [ZMod.intCast_eq_intCast_iff] at hab
    obtain ⟨q, hq⟩ := Int.ModEq.dvd hab
    refine ⟨-q, ?_⟩
    push_cast at hq ⊢
    linarith
  have hpvEq : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      polyVertex g a = polyVertex g b := by
    intro a b hab
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    unfold polyVertex
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨q, ?_⟩
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqC : (a : ℂ) - b = 4 * g * q := by exact_mod_cast hq
    field_simp
    linear_combination hqC
  have harcEqZ : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) → ∀ t : ℝ,
      arcPoint g a t = arcPoint g b t := by
    intro a b hab t
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    unfold arcPoint
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨q, ?_⟩
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqC : (a : ℂ) - b = 4 * g * q := by exact_mod_cast hq
    field_simp
    linear_combination hqC
  have hσEq : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      sidePairing g a = sidePairing g b := by
    intro a b hab
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    funext u
    unfold sidePairing
    congr 1
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨2 * q, ?_⟩
    have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqC : (a : ℂ) - b = 4 * g * q := by exact_mod_cast hq
    field_simp
    push_cast
    linear_combination 2 * hqC
  have hsectorEq : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) →
      edgeSector g a = edgeSector g b := by
    intro a b hab
    obtain ⟨q, hq⟩ := hzmodDvd a b hab
    ext u
    constructor <;> intro hu
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
      refine ⟨ρ, θ' - 4 * g * q, hρ1, hρ2, ?_, ?_, ?_⟩
      · have : (b : ℝ) = a - 4 * g * q := by exact_mod_cast (by linarith [hq] : (b:ℤ) = a - 4*g*q)
        rw [this]
        linarith
      · have : (b : ℝ) = a - 4 * g * q := by exact_mod_cast (by linarith [hq] : (b:ℤ) = a - 4*g*q)
        rw [this]
        linarith
      · rw [hue]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨q, ?_⟩
        have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring
    · obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
      refine ⟨ρ, θ' + 4 * g * q, hρ1, hρ2, ?_, ?_, ?_⟩
      · have : (a : ℝ) = b + 4 * g * q := by exact_mod_cast (by linarith [hq] : (a:ℤ) = b + 4*g*q)
        rw [this]
        linarith
      · have : (a : ℝ) = b + 4 * g * q := by exact_mod_cast (by linarith [hq] : (a:ℤ) = b + 4*g*q)
        rw [this]
        linarith
      · rw [hue]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨-q, ?_⟩
        have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring
  -- ## Sector-index machinery for the vertex chart
  set N : ℂ → ℝ :=
    fun u => if Complex.arg u < 0 then Complex.arg u + 2 * Real.pi else Complex.arg u with hN
  have hidx : ∀ u : ℂ, vertexSectorIndex g u = (⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat := by
    intro u
    simp only [hN]
    rfl
  have hN0 : ∀ u : ℂ, 0 ≤ N u := by
    intro u
    simp only [hN]
    split_ifs with h
    · have := Complex.neg_pi_lt_arg u
      linarith
    · linarith [not_lt.mp h]
  have hNlt : ∀ u : ℂ, N u < 2 * Real.pi := by
    intro u
    simp only [hN]
    split_ifs with h
    · linarith
    · linarith [Complex.arg_le_pi u]
  have hNrep : ∀ u : ℂ, u = (‖u‖ : ℂ) * Complex.exp (((N u : ℝ) : ℂ) * Complex.I) := by
    intro u
    simp only [hN]
    split_ifs with h
    · have hcast : (((Complex.arg u + 2 * Real.pi : ℝ) : ℂ)) * Complex.I
          = ((Complex.arg u : ℝ) : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by
        push_cast
        ring
      rw [hcast, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one,
        Complex.norm_mul_exp_arg_mul_I]
    · rw [Complex.norm_mul_exp_arg_mul_I]
  have him : ∀ u : ℂ, (u ^ (2 * g)).im = ‖u‖ ^ (2 * g) * Real.sin (2 * g * N u) := by
    intro u
    conv_lhs => rw [hNrep u]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have h1 : ((2 * g : ℕ) : ℂ) * (((N u : ℝ) : ℂ) * Complex.I)
        = ((2 * g * N u : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have h2 : ((‖u‖ : ℂ)) ^ (2 * g) = ((‖u‖ ^ (2 * g) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, h2, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hpix : ∀ u : ℂ, 2 * (g : ℝ) * N u = Real.pi * ((2 * (g : ℝ) / Real.pi) * N u) := by
    intro u
    field_simp
  have hsin_sign : ∀ u : ℂ,
      0 ≤ (-1 : ℝ) ^ (vertexSectorIndex g u) * Real.sin (2 * g * N u) := by
    intro u
    rw [hidx u, hpix u]
    have hx0 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N u := mul_nonneg (by positivity) (hN0 u)
    have hfl0 : 0 ≤ ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ := Int.floor_nonneg.mpr hx0
    have hfl : (⌊(2 * (g : ℝ) / Real.pi) * N u⌋ : ℝ) ≤ (2 * (g : ℝ) / Real.pi) * N u :=
      Int.floor_le _
    have hfl1 : (2 * (g : ℝ) / Real.pi) * N u < ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ + 1 :=
      Int.lt_floor_add_one _
    have hdecomp : Real.pi * ((2 * (g : ℝ) / Real.pi) * N u)
        = Real.pi * ((2 * (g : ℝ) / Real.pi) * N u - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋)
          + ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ * Real.pi := by
      ring
    rw [hdecomp, Real.sin_add_int_mul_pi]
    have hpow : ((-1 : ℝ) ^ ((⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat))
        * ((-1 : ℝ) ^ (⌊(2 * (g : ℝ) / Real.pi) * N u⌋) : ℝ) = 1 := by
      rw [← Int.toNat_of_nonneg hfl0, zpow_natCast, ← pow_add]
      exact Even.neg_one_pow ⟨(⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat, rfl⟩
    have hs0 : 0 ≤ Real.sin (Real.pi *
        ((2 * (g : ℝ) / Real.pi) * N u - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have hd : (0 : ℝ) ≤ (2 * (g : ℝ) / Real.pi) * N u
            - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ := by
          linarith
        positivity
      · nlinarith
    calc (0 : ℝ) ≤ (((-1 : ℝ) ^ ((⌊(2 * (g : ℝ) / Real.pi) * N u⌋).toNat))
          * ((-1 : ℝ) ^ (⌊(2 * (g : ℝ) / Real.pi) * N u⌋) : ℝ))
          * Real.sin (Real.pi *
            ((2 * (g : ℝ) / Real.pi) * N u - ⌊(2 * (g : ℝ) / Real.pi) * N u⌋)) := by
            rw [hpow, one_mul]
            exact hs0
      _ = _ := by ring
  have hidx_lt : ∀ u : ℂ, vertexSectorIndex g u < 4 * g := by
    intro u
    rw [hidx u]
    have h2 : (2 * (g : ℝ) / Real.pi) * N u < (2 * (g : ℝ) / Real.pi) * (2 * Real.pi) :=
      mul_lt_mul_of_pos_left (hNlt u) (by positivity)
    have h3 : (2 * (g : ℝ) / Real.pi) * (2 * Real.pi) = 4 * g := by
      field_simp
      ring
    rw [h3] at h2
    have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ < (4 * g : ℤ) := by
      rw [Int.floor_lt]
      exact_mod_cast h2
    omega
  have hNoff : ∀ u : ℂ, ¬(u.im = 0 ∧ 0 ≤ u.re) → N u = Real.pi + Complex.arg (-u) := by
    intro u hu
    rcases lt_trichotomy u.im 0 with h | h | h
    · simp only [hN]
      rw [if_pos (Complex.arg_neg_iff.mpr h), Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
      ring
    · have hre : u.re < 0 := by
        by_contra hcon
        exact hu ⟨h, not_lt.mp hcon⟩
      have h1 : Complex.arg u = Real.pi := Complex.arg_eq_pi_iff.mpr ⟨hre, h⟩
      have h2 : Complex.arg (-u) = 0 := by
        rw [Complex.arg_eq_zero_iff]
        constructor
        · rw [Complex.neg_re]
          linarith
        · rw [Complex.neg_im, h, neg_zero]
      simp only [hN]
      rw [if_neg (by rw [h1]; linarith), h1, h2]
      ring
    · have hnneg : ¬ Complex.arg u < 0 := by
        rw [not_lt]
        exact Complex.arg_nonneg_iff.mpr h.le
      simp only [hN]
      rw [if_neg hnneg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
      ring
  have hNcont : ∀ u : ℂ, ¬(u.im = 0 ∧ 0 ≤ u.re) → ContinuousAt N u := by
    intro u hu
    have hcl : IsClosed {v : ℂ | v.im = 0 ∧ 0 ≤ v.re} :=
      (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_re)
    have hopen : IsOpen {v : ℂ | ¬(v.im = 0 ∧ 0 ≤ v.re)} := hcl.isOpen_compl
    have hslit : -u ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases him0 : u.im = 0
      · left
        rw [Complex.neg_re]
        have hre : u.re < 0 := by
          by_contra hcon
          exact hu ⟨him0, not_lt.mp hcon⟩
        linarith
      · right
        rw [Complex.neg_im]
        exact neg_ne_zero.mpr him0
    have hc : ContinuousAt (fun v : ℂ => Real.pi + Complex.arg (-v)) u :=
      continuousAt_const.add
        ((Complex.continuousAt_arg hslit).comp continuous_neg.continuousAt)
    apply hc.congr
    filter_upwards [hopen.eventually_mem hu] with v hv
    exact (hNoff v hv).symm
  -- Local constancy of the sector index off the rays.
  have hidx_const : ∀ z : ℂ, Real.sin (2 * g * N z) ≠ 0 →
      ∀ᶠ u in 𝓝 z, vertexSectorIndex g u = vertexSectorIndex g z := by
    intro z hsin
    have hnp : ¬(z.im = 0 ∧ 0 ≤ z.re) := by
      intro hcon
      have harg : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hcon.2, hcon.1⟩
      have hNz : N z = 0 := by
        simp only [hN]
        rw [if_neg (by rw [harg]; exact lt_irrefl 0), harg]
      rw [hNz] at hsin
      simp at hsin
    have hcont : ContinuousAt (fun u : ℂ => (2 * (g : ℝ) / Real.pi) * N u) z :=
      continuousAt_const.mul (hNcont z hnp)
    have hxm : ((⌊(2 * (g : ℝ) / Real.pi) * N z⌋ : ℝ)) ≤ (2 * (g : ℝ) / Real.pi) * N z :=
      Int.floor_le _
    have hxm1 : (2 * (g : ℝ) / Real.pi) * N z < ⌊(2 * (g : ℝ) / Real.pi) * N z⌋ + 1 :=
      Int.lt_floor_add_one _
    have hxne : (2 * (g : ℝ) / Real.pi) * N z
        ≠ ((⌊(2 * (g : ℝ) / Real.pi) * N z⌋ : ℝ)) := by
      intro hcon
      apply hsin
      rw [hpix z, hcon, mul_comm]
      exact Real.sin_int_mul_pi _
    have hlt : ((⌊(2 * (g : ℝ) / Real.pi) * N z⌋ : ℝ)) < (2 * (g : ℝ) / Real.pi) * N z :=
      lt_of_le_of_ne hxm (Ne.symm hxne)
    have hev := hcont.eventually_mem (Ioo_mem_nhds hlt hxm1)
    filter_upwards [hev] with u hu
    rw [hidx u, hidx z]
    congr 1
    rw [Int.floor_eq_iff]
    exact ⟨hu.1.le, hu.2⟩
  -- The two-sided dichotomy at a ray point.
  have hray : ∀ z : ℂ, z ≠ 0 → Real.sin (2 * g * N z) = 0 →
      ((2 * (g : ℝ) / Real.pi) * N z = (vertexSectorIndex g z : ℝ)) ∧
      (∀ᶠ u in 𝓝 z, vertexSectorIndex g u = vertexSectorIndex g z ∨
        (vertexSectorIndex g u
            = (if vertexSectorIndex g z = 0 then 4 * g - 1 else vertexSectorIndex g z - 1) ∧
          Real.sin (2 * g * N u) ≠ 0)) := by
    intro z hz0 hsin
    have hx0 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N z := mul_nonneg (by positivity) (hN0 z)
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) * Real.pi = 2 * g * N z := by
      rw [← Real.sin_eq_zero_iff]
      exact hsin
    have hxn : (2 * (g : ℝ) / Real.pi) * N z = (n : ℝ) := by
      field_simp
      linarith [hn]
    have hn0 : 0 ≤ n := by
      have hc : (0 : ℝ) ≤ (n : ℝ) := by
        rw [← hxn]
        exact hx0
      exact_mod_cast hc
    have hidxz : vertexSectorIndex g z = n.toNat := by
      rw [hidx z, hxn, Int.floor_intCast]
    have hfst : (2 * (g : ℝ) / Real.pi) * N z = (vertexSectorIndex g z : ℝ) := by
      rw [hidxz, hxn]
      congr 1
      omega
    refine ⟨hfst, ?_⟩
    by_cases hm0 : vertexSectorIndex g z = 0
    · -- ray along the positive real axis
      have hNz : N z = 0 := by
        have hz' : (2 * (g : ℝ) / Real.pi) * N z = 0 := by
          rw [hfst, hm0]
          norm_num
        rcases mul_eq_zero.mp hz' with h | h
        · exact absurd h (by positivity)
        · exact h
      have harg : Complex.arg z = 0 := by
        simp only [hN] at hNz
        by_cases h : Complex.arg z < 0
        · rw [if_pos h] at hNz
          have := Complex.neg_pi_lt_arg z
          linarith
        · rw [if_neg h] at hNz
          exact hNz
      have hslit : z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        left
        obtain ⟨hre, him0⟩ := Complex.arg_eq_zero_iff.mp harg
        rcases lt_or_eq_of_le hre with h | h
        · exact h
        · exact absurd (Complex.ext h.symm him0) hz0
      have hargc : ContinuousAt Complex.arg z := Complex.continuousAt_arg hslit
      have hwin : ∀ᶠ u in 𝓝 z,
          Complex.arg u ∈ Set.Ioo (-(Real.pi / (4 * g))) (Real.pi / (4 * g)) := by
        apply hargc.eventually_mem
        rw [harg]
        have hq : (0 : ℝ) < Real.pi / (4 * g) := by positivity
        exact Ioo_mem_nhds (by linarith) hq
      filter_upwards [hwin] with u hu
      by_cases hcase : Complex.arg u < 0
      · right
        have hNu : N u = Complex.arg u + 2 * Real.pi := by
          simp only [hN]
          rw [if_pos hcase]
        have hsplit : (2 * (g : ℝ) / Real.pi) * N u
            = (2 * (g : ℝ) / Real.pi) * Complex.arg u + 4 * g := by
          rw [hNu]
          field_simp
          ring
        have hb1 : (2 * (g : ℝ) / Real.pi) * (-(Real.pi / (4 * g)))
            < (2 * (g : ℝ) / Real.pi) * Complex.arg u :=
          mul_lt_mul_of_pos_left hu.1 (by positivity)
        have hc1 : (2 * (g : ℝ) / Real.pi) * (-(Real.pi / (4 * g))) = -(1 / 2) := by
          field_simp
          norm_num
        have hb2 : (2 * (g : ℝ) / Real.pi) * Complex.arg u < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hcase
        rw [hc1] at hb1
        have hy1 : 4 * (g : ℝ) - 1 / 2 < (2 * (g : ℝ) / Real.pi) * N u := by
          rw [hsplit]
          linarith
        have hy2 : (2 * (g : ℝ) / Real.pi) * N u < 4 * g := by
          rw [hsplit]
          linarith
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = 4 * g - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · push_cast
            linarith
          · push_cast
            linarith
        constructor
        · rw [hidx u, hfl, if_pos hm0]
          omega
        · intro hcon
          obtain ⟨n', hn'⟩ : ∃ n' : ℤ, (n' : ℝ) * Real.pi = 2 * g * N u := by
            rw [← Real.sin_eq_zero_iff]
            exact hcon
          have hxn' : (2 * (g : ℝ) / Real.pi) * N u = (n' : ℝ) := by
            field_simp
            linarith [hn']
          rw [hxn'] at hy1 hy2
          have h1 : 4 * (g : ℤ) - 1 < n' := by
            have hr : (4 * (g : ℝ) - 1 : ℝ) < n' := by linarith
            exact_mod_cast hr
          have h2 : n' < 4 * (g : ℤ) := by exact_mod_cast hy2
          omega
      · left
        have hNu : N u = Complex.arg u := by
          simp only [hN]
          rw [if_neg hcase]
        have hy1 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N u := mul_nonneg (by positivity) (hN0 u)
        have hb1 : (2 * (g : ℝ) / Real.pi) * Complex.arg u
            < (2 * (g : ℝ) / Real.pi) * (Real.pi / (4 * g)) :=
          mul_lt_mul_of_pos_left hu.2 (by positivity)
        have hc1 : (2 * (g : ℝ) / Real.pi) * (Real.pi / (4 * g)) = 1 / 2 := by
          field_simp
          norm_num
        rw [hc1] at hb1
        have hy2 : (2 * (g : ℝ) / Real.pi) * N u < 1 / 2 := by
          rw [hNu]
          linarith
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = 0 := by
          rw [Int.floor_eq_iff]
          constructor
          · push_cast
            linarith
          · push_cast
            linarith
        rw [hidx u, hfl, hm0]
        rfl
    · -- interior ray: the normalized angle is continuous at `z`
      have hm1 : 1 ≤ vertexSectorIndex g z := Nat.one_le_iff_ne_zero.mpr hm0
      have hNzpos : 0 < N z := by
        rcases lt_or_eq_of_le (hN0 z) with h | h
        · exact h
        · exfalso
          apply hm0
          rw [hidx z, ← h, mul_zero, Int.floor_zero]
          rfl
      have hnp : ¬(z.im = 0 ∧ 0 ≤ z.re) := by
        intro hcon
        have harg : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hcon.2, hcon.1⟩
        have hNz : N z = 0 := by
          simp only [hN]
          rw [if_neg (by rw [harg]; exact lt_irrefl 0), harg]
        linarith
      have hcont : ContinuousAt (fun u : ℂ => (2 * (g : ℝ) / Real.pi) * N u) z :=
        continuousAt_const.mul (hNcont z hnp)
      have hwin : ∀ᶠ u in 𝓝 z, (2 * (g : ℝ) / Real.pi) * N u ∈
          Set.Ioo ((vertexSectorIndex g z : ℝ) - 1 / 2)
            ((vertexSectorIndex g z : ℝ) + 1 / 2) := by
        apply hcont.eventually_mem
        rw [hfst]
        exact Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [hwin] with u hu
      by_cases hcase : (vertexSectorIndex g z : ℝ) ≤ (2 * (g : ℝ) / Real.pi) * N u
      · left
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = (vertexSectorIndex g z : ℤ) := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast hcase
          · have := hu.2
            push_cast
            linarith
        rw [hidx u, hfl]
        omega
      · right
        push Not at hcase
        have hfl : ⌊(2 * (g : ℝ) / Real.pi) * N u⌋ = (vertexSectorIndex g z : ℤ) - 1 := by
          rw [Int.floor_eq_iff]
          constructor
          · have := hu.1
            push_cast
            linarith
          · push_cast
            linarith
        constructor
        · rw [hidx u, hfl, if_neg hm0]
          omega
        · intro hcon
          obtain ⟨n', hn'⟩ : ∃ n' : ℤ, (n' : ℝ) * Real.pi = 2 * g * N u := by
            rw [← Real.sin_eq_zero_iff]
            exact hcon
          have hxn' : (2 * (g : ℝ) / Real.pi) * N u = (n' : ℝ) := by
            field_simp
            linarith [hn']
          rw [hxn'] at hu hcase
          have h1 : (vertexSectorIndex g z : ℤ) - 1 < n' := by
            have hr : ((vertexSectorIndex g z : ℝ)) - 1 < (n' : ℝ) := by
              have := hu.1
              linarith
            exact_mod_cast hr
          have h2 : n' < (vertexSectorIndex g z : ℤ) := by exact_mod_cast hcase
          omega
    -- ## Vertex-chart formula bricks
  have hAne : ∀ a : ℤ, polyVertex g a ≠ 0 := by
    intro a h
    have hn := hvertnorm a
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hPnorm : ∀ (a : ℤ) (mm : ℕ) (u : ℂ),
      ‖polyVertex g a * Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g))‖
        = Real.exp (-((-1 : ℝ) ^ mm * (u ^ (2 * g)).im)) := by
    intro a mm u
    rw [norm_mul, hvertnorm, one_mul, Complex.norm_exp]
    congr 1
    have h1 : Complex.I * (-1 : ℂ) ^ mm * u ^ (2 * g)
        = (((-1 : ℝ) ^ mm : ℝ) : ℂ) * (u ^ (2 * g) * Complex.I) := by
      push_cast
      ring
    rw [h1, Complex.re_ofReal_mul, Complex.mul_I_re]
    ring
  have hψv : ∀ (mm : ℕ) (u : ℂ), vertexSectorIndex g u = mm →
      vertexChartFun g u = Quotient.mk (genusSetoid g) (projDisc (polyVertex g
        ((vertexSlot g ((mm : ℕ) : ZMod (4 * g))).val : ℤ) *
        Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g)))) := by
    intro mm u h
    unfold vertexChartFun
    rw [h]
  have hparityR : ∀ m₀ : ℕ,
      ((-1 : ℝ) ^ (if m₀ = 0 then 4 * g - 1 else m₀ - 1)) = -((-1 : ℝ)) ^ m₀ := by
    intro m₀
    by_cases h : m₀ = 0
    · rw [if_pos h, h, pow_zero]
      exact Odd.neg_one_pow ⟨2 * g - 1, by omega⟩
    · rw [if_neg h]
      have h1 : m₀ = (m₀ - 1) + 1 := by omega
      conv_rhs => rw [h1]
      rw [pow_succ]
      ring
  have hparityC : ∀ m₀ : ℕ,
      ((-1 : ℂ) ^ (if m₀ = 0 then 4 * g - 1 else m₀ - 1)) = -((-1 : ℂ)) ^ m₀ := by
    intro m₀
    by_cases h : m₀ = 0
    · rw [if_pos h, h, pow_zero]
      exact Odd.neg_one_pow ⟨2 * g - 1, by omega⟩
    · rw [if_neg h]
      have h1 : m₀ = (m₀ - 1) + 1 := by omega
      conv_rhs => rw [h1]
      rw [pow_succ]
      ring
  have hzslot : ∀ m₀ : ℕ,
      (((if m₀ = 0 then 4 * g - 1 else m₀ - 1 : ℕ) : ZMod (4 * g)) + 1)
        = ((m₀ : ℕ) : ZMod (4 * g)) := by
    intro m₀
    by_cases h : m₀ = 0
    · rw [if_pos h, h]
      have h1 : ((4 * g - 1 : ℕ) : ZMod (4 * g)) + 1 = ((4 * g - 1 + 1 : ℕ) : ZMod (4 * g)) := by
        push_cast
        ring
      have h2 : 4 * g - 1 + 1 = 4 * g := by omega
      rw [h1, h2, ZMod.natCast_self]
      exact Nat.cast_zero.symm
    · rw [if_neg h]
      have h1 : ((m₀ - 1 : ℕ) : ZMod (4 * g)) + 1 = ((m₀ - 1 + 1 : ℕ) : ZMod (4 * g)) := by
        push_cast
        ring
      rw [h1]
      congr 1
      omega
  -- ## The reduction of a transition to a local analytic model
  have hred : ∀ (E E' : OpenPartialHomeomorph (GenusSurface g) ℂ) (z : ℂ) (F : ℂ → ℂ),
      AnalyticAt ℂ F z → deriv F z ≠ 0 →
      (∀ᶠ u in 𝓝 z, F u ∈ E'.target ∧ E'.symm (F u) = E.symm u) →
      AnalyticAt ℂ (E.symm.trans E') z ∧ deriv (E.symm.trans E') z ≠ 0 := by
    intro E E' z F hF hdF hev
    have hEq : (⇑(E.symm.trans E') : ℂ → ℂ) =ᶠ[𝓝 z] F := by
      filter_upwards [hev] with u hu
      rw [OpenPartialHomeomorph.trans_apply, ← hu.2, E'.right_inv hu.1]
    refine ⟨hF.congr hEq.symm, ?_⟩
    rw [hEq.deriv_eq]
    exact hdF
  -- ## Diagonal transitions are the identity
  have hdiag : ∀ E : OpenPartialHomeomorph (GenusSurface g) ℂ, ∀ z ∈ (E.symm.trans E).source,
      AnalyticAt ℂ (E.symm.trans E) z ∧ deriv (E.symm.trans E) z ≠ 0 := by
    intro E z hz
    have hzt : z ∈ E.target := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
      exact hz.1
    refine hred E E z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
    filter_upwards [E.open_target.eventually_mem hzt] with u hu
    exact ⟨hu, rfl⟩
  -- ## The inverse bootstrap: a transition inverse to an analytic one is analytic
  have hsymm : ∀ E E' : OpenPartialHomeomorph (GenusSurface g) ℂ,
      (∀ w ∈ (E.symm.trans E').source,
        AnalyticAt ℂ (E.symm.trans E') w ∧ deriv (E.symm.trans E') w ≠ 0) →
      ∀ z ∈ (E'.symm.trans E).source,
        AnalyticAt ℂ (E'.symm.trans E) z ∧ deriv (E'.symm.trans E) z ≠ 0 := by
    intro E E' hfwd z hz
    have hTsymm : E'.symm.trans E = (E.symm.trans E').symm := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    rw [hTsymm] at hz ⊢
    have hzt : z ∈ (E.symm.trans E').target := by
      rwa [OpenPartialHomeomorph.symm_source] at hz
    have hdiff : DifferentiableOn ℂ (⇑(E.symm.trans E').symm) (E.symm.trans E').target := by
      intro y hy
      have hwy : (E.symm.trans E').symm y ∈ (E.symm.trans E').source :=
        (E.symm.trans E').map_target hy
      obtain ⟨hAy, hdy⟩ := hfwd _ hwy
      have hev : ∀ᶠ y' in 𝓝 y, (E.symm.trans E') ((E.symm.trans E').symm y') = y' := by
        filter_upwards [(E.symm.trans E').open_target.eventually_mem hy] with y' hy'
        exact (E.symm.trans E').right_inv hy'
      exact (HasDerivAt.of_local_left_inverse
        ((E.symm.trans E').continuousAt_symm hy)
        hAy.differentiableAt.hasDerivAt hdy hev).differentiableAt.differentiableWithinAt
    have hAz : AnalyticAt ℂ (⇑(E.symm.trans E').symm) z :=
      hdiff.analyticAt ((E.symm.trans E').open_target.mem_nhds hzt)
    refine ⟨hAz, ?_⟩
    have hws : (E.symm.trans E').symm z ∈ (E.symm.trans E').source :=
      (E.symm.trans E').map_target hzt
    obtain ⟨hAw, hdw⟩ := hfwd _ hws
    have hTz : (E.symm.trans E') ((E.symm.trans E').symm z) = z :=
      (E.symm.trans E').right_inv hzt
    have hd2 : DifferentiableAt ℂ (⇑(E.symm.trans E').symm)
        ((E.symm.trans E') ((E.symm.trans E').symm z)) := by
      rw [hTz]
      exact hAz.differentiableAt
    have hder := deriv_comp ((E.symm.trans E').symm z) hd2 hAw.differentiableAt
    have hidEq : (⇑(E.symm.trans E').symm ∘ ⇑(E.symm.trans E') : ℂ → ℂ)
        =ᶠ[𝓝 ((E.symm.trans E').symm z)] id := by
      filter_upwards [(E.symm.trans E').open_source.eventually_mem hws] with u hu
      exact (E.symm.trans E').left_inv hu
    have hder1 : deriv (⇑(E.symm.trans E').symm ∘ ⇑(E.symm.trans E'))
        ((E.symm.trans E').symm z) = 1 := by
      rw [hidEq.deriv_eq, deriv_id]
    rw [hder1, hTz] at hder
    intro h0
    rw [h0, zero_mul] at hder
    exact one_ne_zero hder
  -- ## Source membership decomposition
  have hsrc_mem : ∀ (E E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      ∀ z ∈ (E.symm.trans E').source, z ∈ E.target ∧ E.symm z ∈ E'.source := by
    intro E E' z hz
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    exact ⟨hz.1, hz.2⟩
    -- ## Side-pairing analytic bricks
  have hσmulinv : ∀ k : ℤ, sidePairing g k
      = fun u : ℂ => Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) * u⁻¹ := by
    intro k
    funext u
    unfold sidePairing
    rw [div_eq_mul_inv]
  have hσana : ∀ (k : ℤ) (z : ℂ), z ≠ 0 → AnalyticAt ℂ (sidePairing g k) z := by
    intro k z hz
    rw [hσmulinv k]
    exact analyticAt_const.mul (analyticAt_id.inv hz)
  have hσderiv : ∀ (k : ℤ) (z : ℂ), z ≠ 0 →
      HasDerivAt (sidePairing g k)
        (Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) * (-(z ^ 2)⁻¹)) z := by
    intro k z hz
    rw [hσmulinv k]
    exact (hasDerivAt_inv hz).const_mul _
  have hσdne : ∀ (k : ℤ) (z : ℂ), z ≠ 0 →
      Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) * (-(z ^ 2)⁻¹) ≠ 0 := by
    intro k z hz
    apply mul_ne_zero (Complex.exp_ne_zero _)
    rw [neg_ne_zero]
    exact inv_ne_zero (pow_ne_zero 2 hz)
  have hopen_gt : IsOpen {u : ℂ | 1 < ‖u‖} := isOpen_lt continuous_const continuous_norm
  -- Boundary points of an edge sector are open-arc points.
  have hsector_arc : ∀ (k : ℤ) (u : ℂ), u ∈ edgeSector g k → ‖u‖ = 1 →
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ u = arcPoint g k t := by
    intro k u hu hu1
    obtain ⟨ρ, θ', hρ1, hρ2, hθ1, hθ2, hue⟩ := hu
    have hρpos : (0 : ℝ) < ρ := by linarith
    have hρval : ρ = 1 := by
      have hn : ‖u‖ = ρ := by
        rw [hue, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, hnorm1,
          mul_one]
      rw [hn] at hu1
      exact hu1
    refine ⟨θ' - k, by linarith, by linarith, ?_⟩
    rw [hue, hρval, Complex.ofReal_one, one_mul]
    unfold arcPoint
    congr 1
    push_cast
    ring
  -- Open-arc points lie in their edge sector.
  have harc_mem : ∀ (k : ℤ) (t : ℝ), 0 < t → t < 1 → arcPoint g k t ∈ edgeSector g k := by
    intro k t ht0 ht1
    refine ⟨1, k + t, by norm_num, by norm_num, by linarith, by linarith, ?_⟩
    rw [Complex.ofReal_one, one_mul]
    unfold arcPoint
    congr 1
    push_cast
    ring
  -- ## Interior chart data
  have hIsymm : ∀ u : ℂ, (interiorChart g).symm u
      = Quotient.mk (genusSetoid g) (projDisc u) := interiorChart_symm_apply g
  -- ## Core: interior source to edge target
  have hIEcore : ∀ (k' : ℤ) (E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E'.source = edgeChartFun g k' '' edgeSector g k' →
      E'.target = edgeSector g k' →
      (∀ u, E'.symm u = edgeChartFun g k' u) →
      ∀ z ∈ ((interiorChart g).symm.trans E').source,
        AnalyticAt ℂ ((interiorChart g).symm.trans E') z ∧
          deriv ((interiorChart g).symm.trans E') z ≠ 0 := by
    intro k' E' hsrc' htgt' hsym' z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    have hzt1 : z ∈ Metric.ball (0 : ℂ) 1 := hzt
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzt1
    rw [hIsymm z, hsrc'] at hzs
    obtain ⟨w, hwV, hww⟩ := hzs
    rcases hedgeW k' z w hz1 hww with ⟨-, hwz⟩ | ⟨hw2, hz0, hwσ⟩
    · -- the identity branch
      rw [hwz] at hwV
      refine hred _ E' z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
      filter_upwards [(isOpen_edgeSector g k').eventually_mem hwV,
        Metric.isOpen_ball.eventually_mem hzt1] with u hu1 hu2
      have hu2' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu2
      simp only [id_eq]
      constructor
      · rw [htgt']
        exact hu1
      · rw [hsym', hIsymm, hEFin k' u hu2'.le]
    · -- the side-pairing branch
      have hFz : sidePairing g k' z = w := hwσ.symm
      refine hred _ E' z (sidePairing g k') (hσana k' z hz0)
        (by rw [(hσderiv k' z hz0).deriv]; exact hσdne k' z hz0) ?_
      have hσc : ContinuousAt (sidePairing g k') z := (hσana k' z hz0).continuousAt
      have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ edgeSector g k' := by
        apply hσc.eventually_mem
        rw [hFz]
        exact (isOpen_edgeSector g k').mem_nhds hwV
      have hev2 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ {v : ℂ | 1 < ‖v‖} := by
        apply hσc.eventually_mem
        rw [hFz]
        exact hopen_gt.mem_nhds hw2
      have hev3 : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
      filter_upwards [hev1, hev2, hev3] with u hu1 hu2 hu3
      refine ⟨by rw [htgt']; exact hu1, ?_⟩
      rw [hsym', hIsymm, hEFout k' _ (not_le.mpr hu2), sidePairing_involutive g k' hu3]
  -- ## Core: edge source to interior target
  have hEIcore : ∀ (k : ℤ) (E : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E.target = edgeSector g k →
      (∀ u, E.symm u = edgeChartFun g k u) →
      ∀ z ∈ (E.symm.trans (interiorChart g)).source,
        AnalyticAt ℂ (E.symm.trans (interiorChart g)) z ∧
          deriv (E.symm.trans (interiorChart g)) z ≠ 0 := by
    intro k E htgt hsymE z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    rw [htgt] at hzt
    have hzs1 : E.symm z ∈ (fun u => Quotient.mk (genusSetoid g) (projDisc u))
        '' Metric.ball (0 : ℂ) 1 := hzs
    obtain ⟨w, hwV, hww⟩ := hzs1
    have hww' : Quotient.mk (genusSetoid g) (projDisc w) = E.symm z := hww
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hwV
    rcases lt_trichotomy ‖z‖ 1 with hz1 | hz1 | hz1
    · -- interior branch: identity
      refine hred E _ z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
      filter_upwards [Metric.isOpen_ball.eventually_mem
        (mem_ball_zero_iff.mpr hz1)] with u hu
      have hu' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu
      simp only [id_eq]
      refine ⟨hu, ?_⟩
      rw [hIsymm, hsymE, hEFin k u hu'.le]
    · -- boundary: impossible
      exfalso
      rw [hsymE, hEFin k z (le_of_eq hz1)] at hww'
      have hzw : z = w := hintRep w z hw1 (le_of_eq hz1) hww'.symm
      rw [hzw] at hz1
      linarith
    · -- exterior branch: the side pairing
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz1
        linarith
      refine hred E _ z (sidePairing g k) (hσana k z hz0)
        (by rw [(hσderiv k z hz0).deriv]; exact hσdne k z hz0) ?_
      filter_upwards [hopen_gt.eventually_mem hz1] with u hu
      have hu1 : (1 : ℝ) < ‖u‖ := hu
      have hσlt : ‖sidePairing g k u‖ < 1 := by
        rw [hσnorm, div_lt_one (lt_trans one_pos hu1)]
        linarith
      refine ⟨mem_ball_zero_iff.mpr hσlt, ?_⟩
      rw [hIsymm, hsymE, hEFout k u (not_le.mpr hu1)]
  -- ## Core: edge source to a distinct edge target
  have hEEcore : ∀ (k k' : ℤ) (E E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E.target = edgeSector g k →
      (∀ u, E.symm u = edgeChartFun g k u) →
      E'.source = edgeChartFun g k' '' edgeSector g k' →
      E'.target = edgeSector g k' →
      (∀ u, E'.symm u = edgeChartFun g k' u) →
      ¬(k : ZMod (4 * g)) = (k' : ZMod (4 * g)) →
      ¬(k : ZMod (4 * g)) = ((k' + 2 : ℤ) : ZMod (4 * g)) →
      ¬((k + 2 : ℤ) : ZMod (4 * g)) = (k' : ZMod (4 * g)) →
      ∀ z ∈ (E.symm.trans E').source,
        AnalyticAt ℂ (E.symm.trans E') z ∧ deriv (E.symm.trans E') z ≠ 0 := by
    intro k k' E E' htgt hsymE hsrc' htgt' hsym' hne hne2 hne2' z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    rw [htgt] at hzt
    rw [hsrc'] at hzs
    obtain ⟨w, hwV, hww⟩ := hzs
    rw [hsymE] at hww
    rcases lt_trichotomy ‖z‖ 1 with hz1 | hz1 | hz1
    · -- z interior
      rw [hEFin k z hz1.le] at hww
      rcases hedgeW k' z w hz1 hww with ⟨-, hwz⟩ | ⟨hw2, hz0, hwσ⟩
      · rw [hwz] at hwV
        refine hred E E' z id analyticAt_id (by rw [deriv_id]; exact one_ne_zero) ?_
        filter_upwards [(isOpen_edgeSector g k').eventually_mem hwV,
          Metric.isOpen_ball.eventually_mem (mem_ball_zero_iff.mpr hz1)] with u hu1 hu2
        have hu2' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu2
        simp only [id_eq]
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rw [hsym', hsymE, hEFin k' u hu2'.le, hEFin k u hu2'.le]
      · have hFz : sidePairing g k' z = w := hwσ.symm
        refine hred E E' z (sidePairing g k') (hσana k' z hz0)
          (by rw [(hσderiv k' z hz0).deriv]; exact hσdne k' z hz0) ?_
        have hσc : ContinuousAt (sidePairing g k') z := (hσana k' z hz0).continuousAt
        have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ edgeSector g k' := by
          apply hσc.eventually_mem
          rw [hFz]
          exact (isOpen_edgeSector g k').mem_nhds hwV
        have hev2 : ∀ᶠ u in 𝓝 z, sidePairing g k' u ∈ {v : ℂ | 1 < ‖v‖} := by
          apply hσc.eventually_mem
          rw [hFz]
          exact hopen_gt.mem_nhds hw2
        have hev3 : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
        have hev4 : ∀ᶠ u in 𝓝 z, u ∈ Metric.ball (0 : ℂ) 1 :=
          Metric.isOpen_ball.eventually_mem (mem_ball_zero_iff.mpr hz1)
        filter_upwards [hev1, hev2, hev3, hev4] with u hu1 hu2 hu3 hu4
        have hu4' : ‖u‖ < 1 := mem_ball_zero_iff.mp hu4
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rw [hsym', hsymE, hEFout k' _ (not_le.mpr hu2), sidePairing_involutive g k' hu3,
          hEFin k u hu4'.le]
    · -- z on the open arc: impossible for distinct charts
      exfalso
      rw [hEFin k z (le_of_eq hz1)] at hww
      obtain ⟨t, ht0, ht1, hzarc⟩ := hsector_arc k z hzt hz1
      rcases lt_trichotomy ‖w‖ 1 with hw1 | hw1 | hw1
      · rw [hEFin k' w hw1.le] at hww
        have hzw : z = w := hintRep w z hw1 (le_of_eq hz1) hww.symm
        rw [hzw] at hz1
        linarith
      · rw [hEFin k' w (le_of_eq hw1)] at hww
        obtain ⟨t', ht'0, ht'1, hwarc⟩ := hsector_arc k' w hwV hw1
        have hrel : genusRel g (projDisc (arcPoint g k' t')) (projDisc (arcPoint g k t)) := by
          rw [← hwarc, ← hzarc]
          exact Quotient.exact hww
        rcases harc_rel k' k t' t ht'0 ht'1 ht0 ht1 hrel with
          ⟨hab, -⟩ | ⟨k₀, -, ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩⟩
        · exact hne hab
        · apply hne2
          rw [h2]
          push_cast
          rw [h1]
        · apply hne2'
          rw [h2]
          push_cast
          rw [h1]
      · rw [hEFout k' w (not_le.mpr hw1)] at hww
        have hσw1 : ‖sidePairing g k' w‖ < 1 := by
          rw [hσnorm, div_lt_one (lt_trans one_pos hw1)]
          linarith
        have hzw : z = sidePairing g k' w :=
          hintRep (sidePairing g k' w) z hσw1 (le_of_eq hz1) hww.symm
        rw [hzw] at hz1
        linarith
    · -- z exterior
      rw [hEFout k z (not_le.mpr hz1)] at hww
      have hz0 : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz1
        linarith
      have hσz1 : ‖sidePairing g k z‖ < 1 := by
        rw [hσnorm, div_lt_one (lt_trans one_pos hz1)]
        linarith
      rcases hedgeW k' (sidePairing g k z) w hσz1 hww with ⟨-, hwz⟩ | ⟨hw2, -, hwσ⟩
      · -- w = σ_k z
        rw [hwz] at hwV
        refine hred E E' z (sidePairing g k) (hσana k z hz0)
          (by rw [(hσderiv k z hz0).deriv]; exact hσdne k z hz0) ?_
        have hσc : ContinuousAt (sidePairing g k) z := (hσana k z hz0).continuousAt
        have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k u ∈ edgeSector g k' := by
          apply hσc.eventually_mem
          exact (isOpen_edgeSector g k').mem_nhds hwV
        filter_upwards [hev1, hopen_gt.eventually_mem hz1] with u hu1 hu2
        have hu2' : (1 : ℝ) < ‖u‖ := hu2
        have hσu : ‖sidePairing g k u‖ < 1 := by
          rw [hσnorm, div_lt_one (lt_trans one_pos hu2')]
          linarith
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rw [hsym', hsymE, hEFin k' _ hσu.le, hEFout k u (not_le.mpr hu2')]
      · -- w = σ_{k'} (σ_k z): the transition is the linear map (ω'/ω) · u
        have hcomp : ∀ u : ℂ, u ≠ 0 → sidePairing g k' (sidePairing g k u)
            = (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u := by
          intro u hu
          unfold sidePairing
          have h1 : Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) ≠ 0 :=
            Complex.exp_ne_zero _
          have h2 : Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g)) ≠ 0 :=
            Complex.exp_ne_zero _
          field_simp
        have hcne : Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
            / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g)) ≠ 0 :=
          div_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
        have hFz : (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
            / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * z = w := by
          rw [← hcomp z hz0]
          exact hwσ.symm
        have hnormF : ∀ u : ℂ,
            ‖(Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
              / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u‖
              = ‖u‖ := by
          intro u
          rw [norm_mul, norm_div, hωnorm, hωnorm]
          norm_num
        refine hred E E' z (fun u : ℂ =>
          (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
            / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u)
          (analyticAt_const.mul analyticAt_id) ?_ ?_
        · have hd : HasDerivAt (fun u : ℂ =>
              (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u)
              ((Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * 1) z :=
            (hasDerivAt_id z).const_mul _
          rw [hd.deriv, mul_one]
          exact hcne
        · have hFc : ContinuousAt (fun u : ℂ =>
              (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u) z :=
            (continuous_const.mul continuous_id).continuousAt
          have hev1 : ∀ᶠ u in 𝓝 z,
              (Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u
                ∈ edgeSector g k' := by
            apply hFc.eventually_mem
            rw [hFz]
            exact (isOpen_edgeSector g k').mem_nhds hwV
          have hev3 : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
          filter_upwards [hev1, hopen_gt.eventually_mem hz1, hev3] with u hu1 hu2 hu3
          have hu2' : (1 : ℝ) < ‖u‖ := hu2
          have hσku0 : sidePairing g k u ≠ 0 := by
            rw [hσmulinv k]
            exact mul_ne_zero (Complex.exp_ne_zero _) (inv_ne_zero hu3)
          have hgtF : ¬ ‖(Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
              / Complex.exp (Real.pi * (2 * (k : ℂ) + 3) * Complex.I / (2 * g))) * u‖ ≤ 1 := by
            rw [hnormF]
            exact not_le.mpr hu2'
          refine ⟨by rw [htgt']; exact hu1, ?_⟩
          rw [hsym', hsymE, hEFout k' _ hgtF, hEFout k u (not_le.mpr hu2'), ← hcomp u hu3,
            sidePairing_involutive g k' hσku0]
    -- ## Vertex-chart bricks
  have hVsym : ∀ u : ℂ, (vertexChart g).symm u = vertexChartFun g u := fun _ => rfl
  have hccast : ∀ x : ZMod (4 * g), ((x.val : ℤ) : ZMod (4 * g)) = x := by
    intro x
    rw [Int.cast_natCast]
    exact ZMod.natCast_rightInverse x
  have hncastN : ∀ x : ZMod (4 * g), ((x.val : ℕ) : ZMod (4 * g)) = x := fun x =>
    ZMod.natCast_rightInverse x
  have hzmod4 : ∀ a b : ℤ, (a : ZMod (4 * g)) = (b : ZMod (4 * g)) → a % 4 = b % 4 := by
    intro a b h
    obtain ⟨q, hq⟩ := hzmodDvd a b h
    have hdvd : (4 : ℤ) ∣ b - a := ⟨-(g * q), by linarith⟩
    exact Int.modEq_iff_dvd.mpr hdvd
  have hpvMul : ∀ a b : ℤ, polyVertex g a * polyVertex g b = polyVertex g (a + b) := by
    intro a b
    unfold polyVertex
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hωpv : ∀ kk : ℤ,
      Complex.exp (Real.pi * (2 * (kk : ℂ) + 3) * Complex.I / (2 * g))
        = polyVertex g (2 * kk + 3) := by
    intro kk
    unfold polyVertex
    congr 1
    push_cast
    ring
  have hsign_at : ∀ (mm : ℕ) (u : ℂ), vertexSectorIndex g u = mm →
      0 ≤ (-1 : ℝ) ^ mm * (u ^ (2 * g)).im := by
    intro mm u hu
    rw [him u]
    have hs := hsin_sign u
    rw [hu] at hs
    calc (0 : ℝ) ≤ ‖u‖ ^ (2 * g) * ((-1 : ℝ) ^ mm * Real.sin (2 * g * N u)) :=
          mul_nonneg (pow_nonneg (norm_nonneg u) _) hs
      _ = (-1 : ℝ) ^ mm * (‖u‖ ^ (2 * g) * Real.sin (2 * g * N u)) := by ring
  have hsign_lt : ∀ (mm : ℕ) (u : ℂ), vertexSectorIndex g u = mm → u ≠ 0 →
      Real.sin (2 * g * N u) ≠ 0 → 0 < (-1 : ℝ) ^ mm * (u ^ (2 * g)).im := by
    intro mm u hu hu0 hsin
    rcases lt_or_eq_of_le (hsign_at mm u hu) with h | h
    · exact h
    · exfalso
      have hIm : (u ^ (2 * g)).im = 0 := by
        have hpm : ((-1 : ℝ) ^ mm) ≠ 0 := pow_ne_zero _ (by norm_num)
        rcases mul_eq_zero.mp h.symm with h1 | h1
        · exact absurd h1 hpm
        · exact h1
      rw [him u] at hIm
      rcases mul_eq_zero.mp hIm with h1 | h1
      · exact absurd h1 (pow_ne_zero _ (norm_ne_zero_iff.mpr hu0))
      · exact hsin h1
  have hPana : ∀ (a : ℤ) (mm : ℕ) (z : ℂ),
      AnalyticAt ℂ (fun u : ℂ => polyVertex g a
        * Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g))) z := by
    intro a mm z
    exact analyticAt_const.mul
      (analyticAt_cexp.comp (analyticAt_const.mul (analyticAt_id.pow _)))
  have hPderivne : ∀ (a : ℤ) (mm : ℕ) (z : ℂ), z ≠ 0 →
      deriv (fun u : ℂ => polyVertex g a
        * Complex.exp (Complex.I * (-1) ^ mm * u ^ (2 * g))) z ≠ 0 := by
    intro a mm z hz0
    have hd := (((hasDerivAt_pow (2 * g) z).const_mul
      (Complex.I * (-1) ^ mm)).cexp).const_mul (polyVertex g a)
    rw [hd.deriv]
    apply mul_ne_zero (hAne a)
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero
    · exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (by norm_num))
    · apply mul_ne_zero
      · have h2g : ((2 * g : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        exact_mod_cast h2g
      · exact pow_ne_zero _ hz0
  have hraypow : ∀ (u : ℂ) (mm : ℕ), vertexSectorIndex g u = mm →
      Real.sin (2 * g * N u) = 0 →
      u ^ (2 * g) = ((-1 : ℂ)) ^ mm * ((‖u‖ ^ (2 * g) : ℝ) : ℂ) := by
    intro u mm hidxu hsinu
    have hx0 : 0 ≤ (2 * (g : ℝ) / Real.pi) * N u := mul_nonneg (by positivity) (hN0 u)
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) * Real.pi = 2 * g * N u := by
      rw [← Real.sin_eq_zero_iff]
      exact hsinu
    have hxn : (2 * (g : ℝ) / Real.pi) * N u = (n : ℝ) := by
      field_simp
      linarith [hn]
    have hn0 : 0 ≤ n := by
      have hc : (0 : ℝ) ≤ (n : ℝ) := by
        rw [← hxn]
        exact hx0
      exact_mod_cast hc
    have hmm : (mm : ℤ) = n := by
      rw [← hidxu, hidx u, hxn, Int.floor_intCast]
      omega
    have hreal : 2 * (g : ℝ) * N u = (mm : ℝ) * Real.pi := by
      rw [← hn]
      congr 1
      exact_mod_cast hmm.symm
    conv_lhs => rw [hNrep u]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have hexp : ((2 * g : ℕ) : ℂ) * (((N u : ℝ) : ℂ) * Complex.I)
        = ((mm : ℕ) : ℂ) * (Real.pi * Complex.I) := by
      have hC := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hreal
      push_cast at hC ⊢
      linear_combination Complex.I * hC
    rw [hexp, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    push_cast
    ring
  -- ## Core: vertex source to interior target
  have hVI : ∀ z ∈ ((vertexChart g).symm.trans (interiorChart g)).source,
      AnalyticAt ℂ ((vertexChart g).symm.trans (interiorChart g)) z ∧
        deriv ((vertexChart g).symm.trans (interiorChart g)) z ≠ 0 := by
    intro z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    have hzs1 : (vertexChart g).symm z ∈ (fun u => Quotient.mk (genusSetoid g) (projDisc u))
        '' Metric.ball (0 : ℂ) 1 := hzs
    obtain ⟨w, hwV, hww⟩ := hzs1
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hwV
    have hww' : Quotient.mk (genusSetoid g) (projDisc w) = vertexChartFun g z := hww
    rw [hψv (vertexSectorIndex g z) z rfl] at hww'
    have hPle1 : ‖polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))‖ ≤ 1 := by
      rw [hPnorm, Real.exp_le_one_iff]
      linarith [hsign_at (vertexSectorIndex g z) z rfl]
    have hwP : polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g)) = w :=
      hintRep w _ hw1 hPle1 hww'.symm
    have hPlt : ‖polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))‖ < 1 := by
      rw [hwP]
      exact hw1
    have hsin_ne : Real.sin (2 * g * N z) ≠ 0 := by
      intro hcon
      have hIm : (z ^ (2 * g)).im = 0 := by
        rw [him z, hcon, mul_zero]
      rw [hPnorm, hIm, mul_zero, neg_zero, Real.exp_zero] at hPlt
      exact lt_irrefl 1 hPlt
    have hz0 : z ≠ 0 := by
      intro hcon
      apply hsin_ne
      have hN0z : N z = 0 := by
        simp only [hN, hcon, Complex.arg_zero]
        norm_num
      rw [hN0z, mul_zero, Real.sin_zero]
    refine hred _ _ z (fun u : ℂ => polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
      (hPana _ _ z) (hPderivne _ _ z hz0) ?_
    have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g
        ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
        * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
        ∈ Metric.ball (0 : ℂ) 1 := by
      apply (hPana _ _ z).continuousAt.eventually_mem
      exact Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hPlt)
    filter_upwards [hev1, hidx_const z hsin_ne] with u hu1 hu2
    refine ⟨hu1, ?_⟩
    rw [hIsymm, hVsym, hψv (vertexSectorIndex g z) u hu2]
  have hPdval : ∀ (a : ℤ) (mm : ℕ) (z : ℂ), z ≠ 0 →
      polyVertex g a * (Complex.exp (Complex.I * (-1) ^ mm * z ^ (2 * g))
        * (Complex.I * (-1) ^ mm * (((2 * g : ℕ) : ℂ) * z ^ (2 * g - 1)))) ≠ 0 := by
    intro a mm z hz0
    apply mul_ne_zero (hAne a)
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply mul_ne_zero
    · exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (by norm_num))
    · apply mul_ne_zero
      · have h2g : ((2 * g : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        exact h2g
      · exact pow_ne_zero _ hz0
  -- ## Core: vertex source to edge target
  have hVEcore : ∀ (k' : ℤ) (E' : OpenPartialHomeomorph (GenusSurface g) ℂ),
      E'.source = edgeChartFun g k' '' edgeSector g k' →
      E'.target = edgeSector g k' →
      (∀ u, E'.symm u = edgeChartFun g k' u) →
      (k' % 4 = 0 ∨ k' % 4 = 1) →
      ∀ z ∈ ((vertexChart g).symm.trans E').source,
        AnalyticAt ℂ ((vertexChart g).symm.trans E') z ∧
          deriv ((vertexChart g).symm.trans E') z ≠ 0 := by
    intro k' E' hsrc' htgt' hsym' hk'4 z hz
    obtain ⟨hzt, hzs⟩ := hsrc_mem _ _ z hz
    have hztb : z ∈ Metric.ball (0 : ℂ) (vertexRadius g) := hzt
    rw [hsrc'] at hzs
    obtain ⟨w, hwV, hww⟩ := hzs
    have hww' : edgeChartFun g k' w = vertexChartFun g z := hww
    rw [hψv (vertexSectorIndex g z) z rfl] at hww'
    -- `z = 0` is impossible: the vertex class does not meet an edge-chart source.
    have hz0 : z ≠ 0 := by
      intro hcon
      rw [hcon] at hww'
      rw [zero_pow (by omega : 2 * g ≠ 0), mul_zero, Complex.exp_zero, mul_one] at hww'
      rcases lt_trichotomy ‖w‖ 1 with hw1 | hw1 | hw1
      · rw [hEFin k' w hw1.le] at hww'
        have h1 := hintRep w _ hw1 (hvertnorm _).le hww'.symm
        rw [← h1, hvertnorm] at hw1
        exact lt_irrefl 1 hw1
      · obtain ⟨t', ht'0, ht'1, hwarc⟩ := hsector_arc k' w hwV hw1
        rw [hEFin k' w (le_of_eq hw1), hwarc] at hww'
        exact hvert_rel k' t' ht'0 ht'1 _ (Quotient.exact hww')
      · rw [hEFout k' w (not_le.mpr hw1)] at hww'
        have hσw1 : ‖sidePairing g k' w‖ < 1 := by
          rw [hσnorm, div_lt_one (lt_trans one_pos hw1)]
          linarith
        have h1 := hintRep (sidePairing g k' w) _ hσw1 (hvertnorm _).le hww'.symm
        rw [← h1, hvertnorm] at hσw1
        exact lt_irrefl 1 hσw1
    by_cases hsin : Real.sin (2 * g * N z) = 0
    · -- ray case
      set mv := vertexSectorIndex g z with hmv
      set cv := ((vertexSlot g ((mv : ℕ) : ZMod (4 * g))).val : ℤ) with hcvdef
      set jv := (if mv = 0 then 4 * g - 1 else mv - 1 : ℕ) with hjv
      set cj := ((vertexSlot g ((jv : ℕ) : ZMod (4 * g))).val : ℤ) with hcjdef
      have hdich := (hray z hz0 hsin).2
      have hzpow : z ^ (2 * g) = ((-1 : ℂ)) ^ mv * ((‖z‖ ^ (2 * g) : ℝ) : ℂ) :=
        hraypow z mv hmv.symm hsin
      have hsq : ((-1 : ℂ)) ^ mv * ((-1 : ℂ)) ^ mv = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow ⟨mv, rfl⟩
      have hIm0 : (z ^ (2 * g)).im = 0 := by
        rw [him z, hsin, mul_zero]
      have hPz1 : ‖polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * z ^ (2 * g))‖
          = 1 := by
        rw [hPnorm, hIm0, mul_zero, neg_zero, Real.exp_zero]
      have hnz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
      have hrlt : ‖z‖ ^ (2 * g) < Real.pi / (2 * g) := by
        have h1 : ‖z‖ < vertexRadius g := mem_ball_zero_iff.mp hztb
        have h2 : ‖z‖ ^ (2 * g) < vertexRadius g ^ (2 * g) :=
          pow_lt_pow_left₀ h1 (norm_nonneg z) (by omega)
        exact lt_trans h2 (vertexRadius_pow_lt g)
      have hs₀pos : 0 < (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g) := by positivity
      have hs₀lt : (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g) < 1 := by
        have h1 : (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)
            < (2 * (g : ℝ) / Real.pi) * (Real.pi / (2 * g)) :=
          mul_lt_mul_of_pos_left hrlt (by positivity)
        have h2 : (2 * (g : ℝ) / Real.pi) * (Real.pi / (2 * g)) = 1 := by
          field_simp
        linarith
      have hPzarc : polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * z ^ (2 * g))
          = arcPoint g cv ((2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)) := by
        rw [hzpow]
        unfold polyVertex arcPoint
        rw [← Complex.exp_add]
        congr 1
        have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast
        field_simp
        ring_nf
        linear_combination (2 * (g : ℂ) * ((‖z‖ : ℂ)) ^ (2 * g)) * hsq
      -- identify the target arc of the chart from `w`
      have hwid : ((cv : ZMod (4 * g)) = (k' : ZMod (4 * g)))
          ∨ ((cv : ZMod (4 * g)) = ((k' + 2 : ℤ) : ZMod (4 * g))) := by
        rcases lt_trichotomy ‖w‖ 1 with hw1 | hw1 | hw1
        · exfalso
          rw [hEFin k' w hw1.le] at hww'
          have h1 := hintRep w _ hw1 (le_of_eq hPz1) hww'.symm
          rw [h1] at hPz1
          rw [hPz1] at hw1
          exact lt_irrefl 1 hw1
        · rw [hEFin k' w (le_of_eq hw1)] at hww'
          obtain ⟨t', ht'0, ht'1, hwarc⟩ := hsector_arc k' w hwV hw1
          rw [hwarc, hPzarc] at hww'
          have hrel := Quotient.exact hww'
          rcases harc_rel k' cv t' ((2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)) ht'0 ht'1
            hs₀pos hs₀lt hrel with
            ⟨hab, -⟩ | ⟨k₀, hk₀4, ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩⟩
          · exact Or.inl hab
          · refine Or.inr ?_
            rw [h2]
            push_cast
            rw [h1]
          · exfalso
            have h4 := hzmod4 k' (k₀ + 2) h2
            omega
        · exfalso
          rw [hEFout k' w (not_le.mpr hw1)] at hww'
          have hσw1 : ‖sidePairing g k' w‖ < 1 := by
            rw [hσnorm, div_lt_one (lt_trans one_pos hw1)]
            linarith
          have h1 := hintRep (sidePairing g k' w) _ hσw1 (le_of_eq hPz1) hww'.symm
          rw [h1] at hPz1
          rw [hPz1] at hσw1
          exact lt_irrefl 1 hσw1
      -- the slot recurrence at the ray
      have hsuccrel := vertexSlot_succ g ((jv : ℕ) : ZMod (4 * g))
      rw [hjv] at hsuccrel
      rw [hzslot mv] at hsuccrel
      rw [← hjv] at hsuccrel
      -- hsuccrel : vertexSlot g (mv-cast) = pairInv g (vertexSlot g (jv-cast) - 1)
      have hncast : (((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) : ZMod (4 * g))
          = ((cj - 1 : ℤ) : ZMod (4 * g)) := by
        rw [hccast]
        push_cast
        rw [hccast]
      -- the two sides of the key identity
      have hkey2 : ((2 * k' + 3 : ℤ) : ZMod (4 * g)) = ((cj + cv : ℤ) : ZMod (4 * g)) ∧
          (((cv : ZMod (4 * g)) = (k' : ZMod (4 * g))) ∨
            (((cj - 1 : ℤ) : ZMod (4 * g)) = (k' : ZMod (4 * g)))) := by
        have hcvelt : ((cv : ℤ) : ZMod (4 * g)) = vertexSlot g ((mv : ℕ) : ZMod (4 * g)) :=
          hccast _
        have hcjelt : ((cj : ℤ) : ZMod (4 * g)) = vertexSlot g ((jv : ℕ) : ZMod (4 * g)) :=
          hccast _
        by_cases hcond : ((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 0 ∨
            (vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 1)
        · -- source-arc branch: `c mv = n + 2 = c jv + 1`
          unfold pairInv at hsuccrel
          rw [if_pos hcond] at hsuccrel
          have hcv1 : ((cv : ℤ) : ZMod (4 * g)) = ((cj + 1 : ℤ) : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hcjelt, hsuccrel]
            ring
          have hcvn : ((cv : ℤ) : ZMod (4 * g))
              = ((((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) + 2 : ℤ)
                : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hsuccrel, hncastN]
          rcases hwid with hB | hA
          · -- `cv ≡ k'` is impossible on the source branch (mod 4)
            exfalso
            have e1 := hzmod4 cv k' hB
            have e2 := hzmod4 cv
              (((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) + 2) hcvn
            have e3 : (0 : ℤ) ≤ ((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) := by
              positivity
            omega
          · -- main source case: `k' ≡ c jv - 1`
            have hk'n : ((k' : ℤ) : ZMod (4 * g)) = ((cj - 1 : ℤ) : ZMod (4 * g)) := by
              have h5 : ((k' + 2 : ℤ) : ZMod (4 * g)) = ((cj + 1 : ℤ) : ZMod (4 * g)) := by
                rw [← hA]
                exact hcv1
              push_cast at h5 ⊢
              linear_combination h5
            refine ⟨?_, Or.inr hk'n.symm⟩
            have h6 := hk'n
            have h7 := hcv1
            push_cast at h6 h7 ⊢
            linear_combination 2 * h6 - h7
        · -- target-arc branch: `c mv = n - 2 = c jv - 3`
          unfold pairInv at hsuccrel
          rw [if_neg hcond] at hsuccrel
          have hcv3 : ((cv : ℤ) : ZMod (4 * g)) = ((cj - 3 : ℤ) : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hcjelt, hsuccrel]
            ring
          have hcvn : ((cv : ℤ) : ZMod (4 * g))
              = ((((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) - 2 : ℤ)
                : ZMod (4 * g)) := by
            push_cast
            rw [hcvelt, hsuccrel, hncastN]
          have hcond' : (vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 2 ∨
              (vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val % 4 = 3 := by
            omega
          rcases hwid with hB | hA
          · -- main target case: `k' ≡ cv`
            refine ⟨?_, Or.inl hB⟩
            have h6 := hB
            have h7 := hcv3
            push_cast at h6 h7 ⊢
            linear_combination (-2 : ZMod (4 * g)) * h6 + h7
          · -- `cv ≡ k' + 2` is impossible on the target branch (mod 4)
            exfalso
            have e1 := hzmod4 cv (k' + 2) hA
            have e2 := hzmod4 cv
              (((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) - 2) hcvn
            have e3 : (0 : ℤ) ≤ ((vertexSlot g ((jv : ℕ) : ZMod (4 * g)) - 1).val : ℤ) := by
              positivity
            omega
      have hkey : Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
          = polyVertex g cj * polyVertex g cv := by
        rw [hωpv k', hpvMul, hpvEq (2 * k' + 3) (cj + cv) hkey2.1]
      rw [← hmv] at hdich
      rw [← hjv] at hdich
      have hjv1 : ((jv : ℕ) : ZMod (4 * g)) + 1 = ((mv : ℕ) : ZMod (4 * g)) := by
        rw [hjv]
        exact hzslot mv
      have hparR : ((-1 : ℝ) ^ jv) = -((-1 : ℝ)) ^ mv := by
        rw [hjv]
        exact hparityR mv
      have hparC : ((-1 : ℂ) ^ jv) = -((-1 : ℂ)) ^ mv := by
        rw [hjv]
        exact hparityC mv
      have hψvz : ∀ u : ℂ, vertexSectorIndex g u = mv → vertexChartFun g u
          = Quotient.mk (genusSetoid g) (projDisc (polyVertex g cv
            * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)))) := by
        intro u hu
        rw [hψv mv u hu, hcvdef]
      have hψvj : ∀ u : ℂ, vertexSectorIndex g u = jv → vertexChartFun g u
          = Quotient.mk (genusSetoid g) (projDisc (polyVertex g cj
            * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)))) := by
        intro u hu
        rw [hψv jv u hu, hcjdef]
      have hσP : ∀ u : ℂ, sidePairing g k'
          (polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)))
          = polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)) := by
        intro u
        unfold sidePairing
        rw [div_eq_iff (mul_ne_zero (hAne cv) (Complex.exp_ne_zero _)), hkey]
        have hst : Complex.I * (-1 : ℂ) ^ jv * u ^ (2 * g)
            + Complex.I * (-1 : ℂ) ^ mv * u ^ (2 * g) = 0 := by
          rw [hparC]
          ring
        rw [mul_mul_mul_comm, ← Complex.exp_add, hst, Complex.exp_zero, mul_one]
      have hσP' : ∀ u : ℂ, sidePairing g k'
          (polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)))
          = polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)) := by
        intro u
        unfold sidePairing
        rw [div_eq_iff (mul_ne_zero (hAne cj) (Complex.exp_ne_zero _)), hkey]
        have hst : Complex.I * (-1 : ℂ) ^ mv * u ^ (2 * g)
            + Complex.I * (-1 : ℂ) ^ jv * u ^ (2 * g) = 0 := by
          rw [hparC]
          ring
        rw [mul_mul_mul_comm, ← Complex.exp_add, hst, Complex.exp_zero, mul_one]
        exact mul_comm _ _
      have hballz : ∀ᶠ u in 𝓝 z, u ∈ Metric.ball (0 : ℂ) (vertexRadius g) :=
        Metric.isOpen_ball.eventually_mem hztb
      have hne0ev : ∀ᶠ u in 𝓝 z, u ≠ 0 := isOpen_compl_singleton.eventually_mem hz0
      rcases hkey2.2 with hB | hA
      · -- the chart carries the sector arc: use the `mv`-side formula
        have hsecEq : edgeSector g cv = edgeSector g k' := hsectorEq cv k' hB
        have hFmem : polyVertex g cv * Complex.exp (Complex.I * (-1) ^ mv * z ^ (2 * g))
            ∈ edgeSector g k' := by
          rw [hPzarc, ← hsecEq]
          exact harc_mem cv _ hs₀pos hs₀lt
        refine hred _ E' z (fun u : ℂ => polyVertex g cv
            * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)))
          (hPana _ _ z) (hPderivne _ _ z hz0) ?_
        have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g cv
            * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g)) ∈ edgeSector g k' :=
          (hPana cv mv z).continuousAt.eventually_mem
            ((isOpen_edgeSector g k').mem_nhds hFmem)
        filter_upwards [hev1, hne0ev, hdich] with u hu1 hu2 hu3
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rcases hu3 with hidxu | ⟨hidxu, hsinu⟩
        · have hle : ‖polyVertex g cv
              * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g))‖ ≤ 1 := by
            rw [hPnorm, Real.exp_le_one_iff]
            linarith [hsign_at mv u hidxu]
          rw [hsym', hEFin k' _ hle, hVsym, hψvz u hidxu]
        · have hgt : ¬ ‖polyVertex g cv
              * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g))‖ ≤ 1 := by
            rw [hPnorm, not_le, Real.one_lt_exp_iff]
            have h1 := hsign_lt jv u hidxu hu2 hsinu
            rw [hparR] at h1
            linarith
          rw [hsym', hEFout k' _ hgt, hσP u, hVsym, hψvj u hidxu]
      · -- the chart carries the paired arc: use the `jv`-side formula
        have hsecEq : edgeSector g (cj - 1) = edgeSector g k' := hsectorEq (cj - 1) k' hA
        have hPsarc : polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * z ^ (2 * g))
            = arcPoint g (cj - 1) (1 - (2 * (g : ℝ) / Real.pi) * ‖z‖ ^ (2 * g)) := by
          rw [hzpow, hparC]
          unfold polyVertex arcPoint
          rw [← Complex.exp_add]
          congr 1
          have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast
          field_simp
          ring_nf
          linear_combination (-(2 * (g : ℂ) * ((‖z‖ : ℂ)) ^ (2 * g))) * hsq
        have hFmem : polyVertex g cj * Complex.exp (Complex.I * (-1) ^ jv * z ^ (2 * g))
            ∈ edgeSector g k' := by
          rw [hPsarc, ← hsecEq]
          exact harc_mem (cj - 1) _ (by linarith) (by linarith)
        refine hred _ E' z (fun u : ℂ => polyVertex g cj
            * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)))
          (hPana _ _ z) (hPderivne _ _ z hz0) ?_
        have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g cj
            * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g)) ∈ edgeSector g k' :=
          (hPana cj jv z).continuousAt.eventually_mem
            ((isOpen_edgeSector g k').mem_nhds hFmem)
        filter_upwards [hev1, hne0ev, hdich, hballz] with u hu1 hu2 hu3 hu4
        refine ⟨by rw [htgt']; exact hu1, ?_⟩
        rcases hu3 with hidxu | ⟨hidxu, hsinu⟩
        · -- the `mv` side, including the shared ray
          by_cases hsinu : Real.sin (2 * g * N u) = 0
          · -- on the ray: the two sector formulas are glued
            have hupow := hraypow u mv hidxu hsinu
            have hIm0u : (u ^ (2 * g)).im = 0 := by
              rw [him u, hsinu, mul_zero]
            have hle : ‖polyVertex g cj
                * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))‖ ≤ 1 := by
              rw [hPnorm, hIm0u, mul_zero, neg_zero, Real.exp_zero]
            have hsu : ‖u‖ ^ (2 * g) < Real.pi / (2 * g) :=
              lt_trans (pow_lt_pow_left₀ (mem_ball_zero_iff.mp hu4) (norm_nonneg u)
                (by omega)) (vertexRadius_pow_lt g)
            have hglue := vertexRay_glue g jv (norm_nonneg u) hsu
            rw [hjv1] at hglue
            have hQ : Quotient.mk (genusSetoid g) (projDisc (polyVertex g
                ((vertexSlot g ((jv : ℕ) : ZMod (4 * g))).val : ℤ)
                * Complex.exp (-(Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)))))
                = Quotient.mk (genusSetoid g) (projDisc (polyVertex g
                  ((vertexSlot g ((mv : ℕ) : ZMod (4 * g))).val : ℤ)
                  * Complex.exp (Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)))) :=
              Quotient.sound hglue
            have hform1 : polyVertex g cj
                * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))
                = polyVertex g ((vertexSlot g ((jv : ℕ) : ZMod (4 * g))).val : ℤ)
                  * Complex.exp (-(Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g))) := by
              rw [hcjdef, hupow, hparC]
              have harg : Complex.I * -(-1 : ℂ) ^ mv
                  * ((-1 : ℂ) ^ mv * ((‖u‖ ^ (2 * g) : ℝ) : ℂ))
                  = -(Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)) := by
                push_cast
                linear_combination (-(Complex.I) * ((‖u‖ : ℂ)) ^ (2 * g)) * hsq
              rw [harg]
            have hform2 : polyVertex g cv
                * Complex.exp (Complex.I * (-1) ^ mv * u ^ (2 * g))
                = polyVertex g ((vertexSlot g ((mv : ℕ) : ZMod (4 * g))).val : ℤ)
                  * Complex.exp (Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g)) := by
              rw [hcvdef, hupow]
              have harg : Complex.I * (-1 : ℂ) ^ mv
                  * ((-1 : ℂ) ^ mv * ((‖u‖ ^ (2 * g) : ℝ) : ℂ))
                  = Complex.I * ((‖u‖ : ℝ) : ℂ) ^ (2 * g) := by
                push_cast
                linear_combination (Complex.I * ((‖u‖ : ℂ)) ^ (2 * g)) * hsq
              rw [harg]
            rw [hsym', hEFin k' _ hle, hVsym, hψvz u hidxu, hform1, hform2]
            exact hQ
          · -- off the ray on the `mv` side: pair back
            have hgt : ¬ ‖polyVertex g cj
                * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))‖ ≤ 1 := by
              rw [hPnorm, not_le, Real.one_lt_exp_iff, hparR]
              have h1 := hsign_lt mv u hidxu hu2 hsinu
              linarith
            rw [hsym', hEFout k' _ hgt, hσP' u, hVsym, hψvz u hidxu]
        · -- the `jv` side: direct
          have hle : ‖polyVertex g cj
              * Complex.exp (Complex.I * (-1) ^ jv * u ^ (2 * g))‖ ≤ 1 := by
            rw [hPnorm, Real.exp_le_one_iff]
            linarith [hsign_at jv u hidxu]
          rw [hsym', hEFin k' _ hle, hVsym, hψvj u hidxu]
    · -- off the rays: the sector formula, possibly post-composed with the pairing
      have hPlt : ‖polyVertex g
          ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
          * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))‖ < 1 := by
        rw [hPnorm, Real.exp_lt_one_iff]
        linarith [hsign_lt (vertexSectorIndex g z) z rfl hz0 hsin]
      rcases hedgeW k' _ w hPlt hww' with ⟨-, hwz⟩ | ⟨hw2, hPz0, hwσ⟩
      · -- direct branch
        rw [hwz] at hwV
        refine hred _ E' z (fun u : ℂ => polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
          (hPana _ _ z) (hPderivne _ _ z hz0) ?_
        have hev1 : ∀ᶠ u in 𝓝 z, polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
            ∈ edgeSector g k' :=
          (hPana _ _ z).continuousAt.eventually_mem ((isOpen_edgeSector g k').mem_nhds hwV)
        have hev2 : ∀ᶠ u in 𝓝 z, polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
            ∈ Metric.ball (0 : ℂ) 1 :=
          (hPana _ _ z).continuousAt.eventually_mem
            (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hPlt))
        filter_upwards [hev1, hev2, hidx_const z hsin] with u h1 h2 h3
        refine ⟨by rw [htgt']; exact h1, ?_⟩
        rw [hsym', hEFin k' _ (mem_ball_zero_iff.mp h2).le, hVsym,
          hψv (vertexSectorIndex g z) u h3]
      · -- pairing branch
        have hPz0' : polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g)) ≠ 0 :=
          mul_ne_zero (hAne _) (Complex.exp_ne_zero _)
        refine hred _ E' z (fun u : ℂ => sidePairing g k' (polyVertex g
            ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
            * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))))
          ?_ ?_ ?_
        · exact AnalyticAt.comp (g := sidePairing g k') (f := fun u : ℂ => polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
            (x := z) (hσana k' _ hPz0') (hPana _ _ z)
        · have hPhd := (((hasDerivAt_pow (2 * g) z).const_mul
            (Complex.I * (-1) ^ (vertexSectorIndex g z))).cexp).const_mul (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ))
          have hchain := HasDerivAt.comp z (hσderiv k' _ hPz0') hPhd
          have hd2 : deriv (fun u : ℂ => sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))) z
              = Complex.exp (Real.pi * (2 * (k' : ℂ) + 3) * Complex.I / (2 * g))
                  * (-((polyVertex g
                    ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
                    * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z)
                      * z ^ (2 * g))) ^ 2)⁻¹)
                * (polyVertex g
                    ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
                  * (Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))
                    * (Complex.I * (-1) ^ (vertexSectorIndex g z)
                      * (((2 * g : ℕ) : ℂ) * z ^ (2 * g - 1))))) := hchain.deriv
          rw [hd2]
          exact mul_ne_zero (hσdne k' _ hPz0') (hPdval _ _ z hz0)
        · have hFz : sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * z ^ (2 * g))) = w :=
            hwσ.symm
          have hσPc : ContinuousAt (fun u : ℂ => sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))) z :=
            (AnalyticAt.comp (g := sidePairing g k') (f := fun u : ℂ => polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
              (x := z) (hσana k' _ hPz0') (hPana _ _ z)).continuousAt
          have hev1 : ∀ᶠ u in 𝓝 z, sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))
              ∈ edgeSector g k' := by
            apply hσPc.eventually_mem
            rw [hFz]
            exact (isOpen_edgeSector g k').mem_nhds hwV
          have hev2 : ∀ᶠ u in 𝓝 z, polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))
              ∈ Metric.ball (0 : ℂ) 1 :=
            (hPana _ _ z).continuousAt.eventually_mem
              (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hPlt))
          filter_upwards [hev1, hev2, hidx_const z hsin] with u h1 h2 h3
          have hPu0 : polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)) ≠ 0 :=
            mul_ne_zero (hAne _) (Complex.exp_ne_zero _)
          have hPu1 : ‖polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))‖ < 1 :=
            mem_ball_zero_iff.mp h2
          have hPupos : 0 < ‖polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g))‖ :=
            norm_pos_iff.mpr hPu0
          have hgt : ¬ ‖sidePairing g k' (polyVertex g
              ((vertexSlot g ((vertexSectorIndex g z : ℕ) : ZMod (4 * g))).val : ℤ)
              * Complex.exp (Complex.I * (-1) ^ (vertexSectorIndex g z) * u ^ (2 * g)))‖
              ≤ 1 := by
            rw [hσnorm, not_le, lt_div_iff₀ hPupos, one_mul]
            exact hPu1
          refine ⟨by rw [htgt']; exact h1, ?_⟩
          rw [hsym', hEFout k' _ hgt, sidePairing_involutive g k' hPu0, hVsym,
            hψv (vertexSectorIndex g z) u h3]
    -- ## Assembly over the atlas
  have hcases : ∀ f ∈ atlas ℂ (GenusSurface g), f = interiorChart g ∨
      (∃ jb : Fin g × Bool, f = edgeChart g jb.1 jb.2) ∨ f = vertexChart g := by
    intro f hf
    have hf' : f ∈ ({interiorChart g}
        ∪ Set.range (fun jb : Fin g × Bool => edgeChart g jb.1 jb.2)
        ∪ {vertexChart g} : Set (OpenPartialHomeomorph (GenusSurface g) ℂ)) := hf
    rcases hf' with (hf1 | hf1) | hf1
    · exact Or.inl hf1
    · obtain ⟨jb, hjb⟩ := hf1
      exact Or.inr (Or.inl ⟨jb, hjb.symm⟩)
    · exact Or.inr (Or.inr hf1)
  have hedgeIdxNe : ∀ (j j' : Fin g) (b b' : Bool),
      ((4 * (j : ℤ) + if b then 1 else 0 : ℤ) : ZMod (4 * g))
        = ((4 * (j' : ℤ) + if b' then 1 else 0 : ℤ) : ZMod (4 * g)) →
      j = j' ∧ b = b' := by
    intro j j' b b' hcon
    obtain ⟨q, hq⟩ := hzmodDvd _ _ hcon
    have hgZ : (1 : ℤ) ≤ g := by exact_mod_cast hg1
    have hjZ : (j : ℤ) < g := by exact_mod_cast j.2
    have hj'Z : (j' : ℤ) < g := by exact_mod_cast j'.2
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le _
    have hj'0 : (0 : ℤ) ≤ (j' : ℤ) := by exact_mod_cast Nat.zero_le _
    have hifb : ∀ c : Bool, (0 : ℤ) ≤ (if c then (1 : ℤ) else 0) ∧
        (if c then (1 : ℤ) else 0) ≤ 1 := by
      intro c
      cases c
      · rw [if_neg Bool.false_ne_true]
        norm_num
      · rw [if_pos rfl]
        norm_num
    have hgq : 4 * (g : ℤ) * q = 4 * ((g : ℤ) * q) := by ring
    rw [hgq] at hq
    have hq0 : (g : ℤ) * q = 0 := by
      rcases lt_trichotomy q 0 with h | h | h
      · exfalso
        have h1 : (g : ℤ) * q ≤ -g := by nlinarith
        linarith [(hifb b).1, (hifb b).2, (hifb b').1, (hifb b').2]
      · rw [h, mul_zero]
      · exfalso
        have h1 : (g : ℤ) ≤ g * q := by nlinarith
        linarith [(hifb b).1, (hifb b).2, (hifb b').1, (hifb b').2]
    rw [hq0, mul_zero] at hq
    cases b <;> cases b' <;> (try simp only [Bool.false_eq_true, if_false, if_true] at hq)
    · refine ⟨Fin.ext ?_, rfl⟩
      omega
    · exfalso
      omega
    · exfalso
      omega
    · refine ⟨Fin.ext ?_, rfl⟩
      omega
  intro e he e' he'
  rcases hcases e he with he1 | ⟨⟨j, b⟩, he1⟩ | he1
  · subst he1
    rcases hcases e' he' with he2 | ⟨⟨j', b'⟩, he2⟩ | he2
    · subst he2
      exact hdiag _
    · subst he2
      exact hIEcore (4 * (j' : ℤ) + if b' then 1 else 0) (edgeChart g j' b') rfl rfl
        (fun u => rfl)
    · subst he2
      exact hsymm (vertexChart g) (interiorChart g) hVI
  · subst he1
    rcases hcases e' he' with he2 | ⟨⟨j', b'⟩, he2⟩ | he2
    · subst he2
      exact hEIcore (4 * (j : ℤ) + if b then 1 else 0) (edgeChart g j b) rfl (fun u => rfl)
    · subst he2
      by_cases hsame : j = j' ∧ b = b'
      · obtain ⟨rfl, rfl⟩ := hsame
        exact hdiag _
      · refine hEEcore (4 * (j : ℤ) + if b then 1 else 0)
          (4 * (j' : ℤ) + if b' then 1 else 0) (edgeChart g j b) (edgeChart g j' b')
          rfl (fun u => rfl) rfl rfl (fun u => rfl) ?_ ?_ ?_
        · intro hcon
          exact hsame (hedgeIdxNe j j' b b' hcon)
        · intro hcon
          have h4 := hzmod4 _ _ hcon
          have e1 := edgeIndex_mod g j b
          have e2 := edgeIndex_mod g j' b'
          omega
        · intro hcon
          have h4 := hzmod4 _ _ hcon
          have e1 := edgeIndex_mod g j b
          have e2 := edgeIndex_mod g j' b'
          omega
    · subst he2
      exact hsymm (vertexChart g) (edgeChart g j b)
        (hVEcore (4 * (j : ℤ) + if b then 1 else 0) (edgeChart g j b) rfl rfl
          (fun u => rfl) (edgeIndex_mod g j b))
  · subst he1
    rcases hcases e' he' with he2 | ⟨⟨j', b'⟩, he2⟩ | he2
    · subst he2
      exact hVI
    · subst he2
      exact hVEcore (4 * (j' : ℤ) + if b' then 1 else 0) (edgeChart g j' b') rfl rfl
        (fun u => rfl) (edgeIndex_mod g j' b')
    · subst he2
      exact hdiag _

open scoped ContDiff in
/-- The genus surface is an analytic complex manifold: all atlas transitions
are analytic. -/
theorem isManifold_genusSurface (g : ℕ) [NeZero g] :
    IsManifold 𝓘(ℂ) ω (GenusSurface g) := by
  have hana : ∀ e ∈ atlas ℂ (GenusSurface g), ∀ e' ∈ atlas ℂ (GenusSurface g),
      ContDiffOn ℂ ω (e.symm.trans e') (e.symm.trans e').source := by
    intro e he e' he'
    have h : AnalyticOnNhd ℂ (e.symm.trans e') (e.symm.trans e').source :=
      fun z hz => (transition_analyticAt g e he e' he' z hz).1
    exact h.contDiffOn (e.symm.trans e').open_source.uniqueDiffOn
  have hgr : HasGroupoid (GenusSurface g) (contDiffGroupoid ω 𝓘(ℂ)) := by
    constructor
    intro e e' he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    have hsymmEq : (e.symm.trans e').symm = e'.symm.trans e := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    constructor
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
        Set.preimage_id, Set.range_id, Set.inter_univ]
      exact hana e he e' he'
    · simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
        Set.preimage_id, Set.range_id, Set.inter_univ]
      have hset : (e.symm.trans e').target = (e'.symm.trans e).source := by
        rw [← hsymmEq, OpenPartialHomeomorph.symm_source]
      rw [hsymmEq, hset]
      exact hana e' he' e he
  exact IsManifold.mk' 𝓘(ℂ) ω (GenusSurface g) (gr := hgr)

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
    IsOpen A ↔ IsOpen (Quotient.mk (genusSetoid g) ⁻¹' A) :=
  (quotientMap_genus g).isOpen_preimage.symm

end RiemannDynamics
