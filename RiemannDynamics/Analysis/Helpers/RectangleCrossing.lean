/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The planar rectangle crossing lemma

This file proves the **planar rectangle crossing lemma** (a form of the
Poincaré–Miranda / two–dimensional intermediate value theorem):

> In the closed unit square, a continuous path `α` running from the left
> edge to the right edge must intersect any continuous path `β` running
> from the bottom edge to the top edge.

The mathematical content is the Poincaré–Miranda theorem on `[0,1]²`:
a continuous map `[0,1]² → ℝ²` whose two coordinate functions have
opposite signs on the two opposite pairs of edges has a zero.

## Architecture

The public statement `rectangle_crossing` is phrased for paths into `ℂ`
(via `Complex.reProdIm`, written `s ×ℂ t`), which is how the surrounding
quasiconformal-reciprocity development consumes it. All of the
complex ↔ real-coordinate translation and the edge-sign bookkeeping
(turning the four edge conditions on `α`, `β` into the four sign
conditions on the two real coordinate functions of `G (s,t) = α s − β t`)
is proved here for real.

The single genuinely combinatorial ingredient that Mathlib does not yet
provide — equivalent to **Sperner's lemma** / the Brouwer fixed point
theorem in dimension two — is the finite, purely combinatorial

* `discrete_poincare_miranda`

(a discrete Poincaré–Miranda lemma on an `n × n` grid). It is proved here
from scratch by the classical Sperner argument (a mod-`2` door-counting
double count on the lower-left triangulation of the grid, with the
Poincaré–Miranda labeling, and a perturbation-and-limit step to handle the
non-strict boundary conditions). Everything else, including the
two-dimensional intermediate value theorem itself, is then derived from it:
the continuous theorem `poincare_miranda_unit_square` is obtained from the
discrete one by uniform continuity (Heine–Cantor) plus a
sequential-compactness limit, and the geometric crossing lemma
`rectangle_crossing` is then pure coordinate bookkeeping.

The whole file is `sorry`-free; every result is axiom-clean.

## Main results

* `discrete_poincare_miranda`: the discrete Poincaré–Miranda lemma on a
  grid — the Sperner-equivalent combinatorial core, proved from scratch.
* `poincare_miranda_approx`: the approximate (common-approximate-zero)
  Poincaré–Miranda theorem, proved from the discrete lemma by uniform
  continuity.
* `poincare_miranda_unit_square`: the two-dimensional intermediate value
  theorem on the closed unit square, proved from `poincare_miranda_approx`
  by a compactness limit.
* `rectangle_crossing`: the crossing lemma for paths in the unit square,
  proved in full.
-/

namespace RiemannDynamics

open Set Filter Topology

/-! ### The combinatorial core: an approximate Poincaré–Miranda theorem

The irreducible content of the two-dimensional intermediate value theorem
is combinatorial (Sperner's lemma / a discrete Poincaré–Miranda argument on
a fine grid). Mathlib provides the one-dimensional `intermediate_value_Icc`
but no Brouwer fixed point theorem, no Sperner's lemma, and no degree
theory, so this content is developed from scratch below.

The bridge result is `poincare_miranda_approx`: under the Poincaré–Miranda
hypotheses, `f` and `g` admit a *common approximate zero* — for every
`ε > 0` a point of the square at which both `|f|` and `|g|` are below `ε`.
This is exactly what running the discrete Poincaré–Miranda lemma
(`discrete_poincare_miranda`, the Sperner core) on an `n × n` grid yields:
the discrete lemma produces a single small cell across whose corners both
`f` and `g` change sign, and uniform continuity then bounds `|f|, |g|` by
`ε` on that cell.

From this approximate statement the exact theorem
`poincare_miranda_unit_square` follows by a genuine compactness/continuity
limit, proved in full below: take a sequence of approximate zeros `pₙ`
with errors `→ 0`, extract a convergent subsequence by sequential
compactness of the square, and pass to the limit using continuity. -/

/-- The four corner grid points of the cell with lower-left corner `(i, j)`. -/
def cellCorners (i j : ℕ) : Finset (ℕ × ℕ) :=
  {(i, j), (i + 1, j), (i, j + 1), (i + 1, j + 1)}

section SpernerCombinatorics

open Finset

/-! ### Combinatorial core: Sperner's lemma for the lower-left triangulation.

We abstract over a labeling `L : ℕ → ℕ → Fin 3`.  The triangulation of cell
`(i,j)` (with `i, j < n`) consists of
`T_low(i,j) = {(i,j), (i+1,j), (i+1,j+1)}` and
`T_up(i,j) = {(i,j), (i,j+1), (i+1,j+1)}`, sharing the lower-left to upper-right
diagonal `{(i,j),(i+1,j+1)}`.  We prove that under the strict boundary
conditions (right edge all label `0`; no `0` on the left edge; no `2` on the
bottom; no `1` on the top) some triangle is "rainbow" (carries all of
`{0,1,2}`). -/

/-- "Door" indicator (in `ZMod 2`) of an edge: `1` iff the two endpoint labels
are exactly `{0,1}`. -/
def dind (a b : Fin 3) : ZMod 2 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else 0

/-- A triple of labels is rainbow if all of `0,1,2` occur. -/
@[reducible] def isRainbow (a b c : Fin 3) : Prop :=
  (a = 0 ∨ b = 0 ∨ c = 0) ∧ (a = 1 ∨ b = 1 ∨ c = 1) ∧ (a = 2 ∨ b = 2 ∨ c = 2)

/-- Door parity of a single triangle: a non-rainbow triangle has an even number
of `{0,1}`-edges. -/
private lemma doors_even_of_not_rainbow (a b c : Fin 3) (h : ¬ isRainbow a b c) :
    dind a b + dind a c + dind b c = 0 := by
  revert h; revert a b c; decide

/-- Door parity of a single triangle: a rainbow triangle has exactly one
`{0,1}`-edge. -/
private lemma doors_one_of_rainbow (a b c : Fin 3) (h : isRainbow a b c) :
    dind a b + dind a c + dind b c = 1 := by
  revert h; revert a b c; decide

/-- The `ZMod 2` "shift" telescoping identity used to collapse interior-edge
multiplicities. -/
private lemma zmod2_shift (f : ℕ → ZMod 2) (n : ℕ) :
    (∑ j ∈ range n, f j) + (∑ j ∈ range n, f (j + 1)) = f 0 + f n := by
  have h1 : (∑ j ∈ range n, f (j + 1)) = (∑ k ∈ range (n + 1), f k) - f 0 := by
    rw [Finset.sum_range_succ']; ring
  rw [h1, Finset.sum_range_succ]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have h3 : ∀ x : ZMod 2, -x = x := by decide
  set S := ∑ j ∈ range n, f j
  have : S + (S + f n - f 0) = (S + S) + f n - f 0 := by ring
  rw [this, h2]
  simp only [zero_add]
  rw [sub_eq_add_neg, h3 (f 0)]; ring

/-- Horizontal-edge door indicator: edge `{(i,j),(i+1,j)}`. -/
private def hD (L : ℕ → ℕ → Fin 3) (i j : ℕ) : ZMod 2 := dind (L i j) (L (i + 1) j)

/-- Vertical-edge door indicator: edge `{(i,j),(i,j+1)}`. -/
private def vD (L : ℕ → ℕ → Fin 3) (i j : ℕ) : ZMod 2 := dind (L i j) (L i (j + 1))

/-- Diagonal-edge door indicator: edge `{(i,j),(i+1,j+1)}`. -/
private def gD (L : ℕ → ℕ → Fin 3) (i j : ℕ) : ZMod 2 := dind (L i j) (L (i + 1) (j + 1))

/-- Door count (mod 2) of the lower triangle `T_low(i,j)`. -/
private def doorsLow (L : ℕ → ℕ → Fin 3) (i j : ℕ) : ZMod 2 :=
  hD L i j + gD L i j + dind (L (i + 1) j) (L (i + 1) (j + 1))

/-- Door count (mod 2) of the upper triangle `T_up(i,j)`. -/
private def doorsUp (L : ℕ → ℕ → Fin 3) (i j : ℕ) : ZMod 2 :=
  vD L i j + dind (L i (j + 1)) (L (i + 1) (j + 1)) + gD L i j

/-- Per-cell decomposition of the two triangles' door counts into oriented edge
indicators (the two diagonal contributions cancel in `ZMod 2`). -/
private lemma doorsLow_add_doorsUp (L : ℕ → ℕ → Fin 3) (i j : ℕ) :
    doorsLow L i j + doorsUp L i j
      = hD L i j + vD L (i + 1) j + vD L i j + hD L i (j + 1) := by
  have e1 : dind (L (i + 1) j) (L (i + 1) (j + 1)) = vD L (i + 1) j := rfl
  have e2 : dind (L i (j + 1)) (L (i + 1) (j + 1)) = hD L i (j + 1) := rfl
  unfold doorsLow doorsUp gD
  rw [e1, e2]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  set d := dind (L i j) (L (i + 1) (j + 1)) with hd
  generalize hD L i j = a
  generalize vD L (i + 1) j = b
  generalize vD L i j = c
  generalize hD L i (j + 1) = e
  have : a + d + b + (c + e + d) = (a + b + c + e) + (d + d) := by ring
  rw [this, h2, add_zero]

/-- The total door count `S = Σ_{i,j<n} (doorsLow + doorsUp)` collapses (mod 2)
to the boundary horizontal/vertical contributions. -/
private lemma total_doors_eq_boundary (L : ℕ → ℕ → Fin 3) (n : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range n, (doorsLow L i j + doorsUp L i j))
      = (∑ i ∈ range n, (hD L i 0 + hD L i n))
        + (∑ j ∈ range n, (vD L 0 j + vD L n j)) := by
  have hsum : (∑ i ∈ range n, ∑ j ∈ range n, (doorsLow L i j + doorsUp L i j))
      = (∑ i ∈ range n, ∑ j ∈ range n,
          (hD L i j + vD L (i + 1) j + vD L i j + hD L i (j + 1))) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    exact doorsLow_add_doorsUp L i j
  rw [hsum]
  -- regroup
  have step1 :
      (∑ i ∈ range n, ∑ j ∈ range n,
        (hD L i j + vD L (i + 1) j + vD L i j + hD L i (j + 1)))
      = (∑ i ∈ range n, ∑ j ∈ range n,
          ((hD L i j + hD L i (j + 1)) + (vD L i j + vD L (i + 1) j))) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  rw [step1]
  have step2 :
      (∑ i ∈ range n, ∑ j ∈ range n,
        ((hD L i j + hD L i (j + 1)) + (vD L i j + vD L (i + 1) j)))
      = (∑ i ∈ range n, ∑ j ∈ range n, (hD L i j + hD L i (j + 1)))
        + (∑ i ∈ range n, ∑ j ∈ range n, (vD L i j + vD L (i + 1) j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
  rw [step2]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_add_distrib]
    exact zmod2_shift (hD L i) n
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_add_distrib]
    exact zmod2_shift (fun i => vD L i j) n

/-- Map `Fin 3 → ZMod 2` distinguishing label `1`. -/
private def t01 : Fin 3 → ZMod 2 := fun x => if x = 1 then 1 else 0

/-- For labels avoiding `2`, the door indicator is the `ZMod 2` sum of the
`t01` values of the endpoints. -/
private lemma dind_eq_t01 : ∀ a b : Fin 3, a ≠ 2 → b ≠ 2 → dind a b = t01 a + t01 b := by
  decide

/-- 1-dimensional Sperner along the bottom edge: if every bottom-row label is in
`{0,1}` (i.e. `≠ 2`), with `L 0 0 = 1` and `L n 0 = 0`, then the number of
`{0,1}`-doors on the bottom is odd, i.e. the `ZMod 2` sum is `1`. -/
private lemma bottom_doors_odd (L : ℕ → ℕ → Fin 3) (n : ℕ)
    (hbot : ∀ i ≤ n, L i 0 ≠ 2) (h0 : L 0 0 = 1) (hn : L n 0 = 0) :
    (∑ i ∈ range n, hD L i 0) = 1 := by
  have key : (∑ i ∈ range n, hD L i 0)
      = (∑ i ∈ range n, (t01 (L i 0) + t01 (L (i + 1) 0))) := by
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mem_range] at hi
    have hi' : i ≤ n := le_of_lt hi
    have hi1 : i + 1 ≤ n := hi
    exact dind_eq_t01 (L i 0) (L (i + 1) 0) (hbot i hi') (hbot (i + 1) hi1)
  rw [key]
  rw [Finset.sum_add_distrib]
  rw [zmod2_shift (fun i => t01 (L i 0)) n]
  simp only [t01]
  rw [h0, hn]
  decide

/-- `Fin 3` value `1` from "not `0`, not `2`". -/
private lemma eq_one_of_ne (a : Fin 3) (h0 : a ≠ 0) (h2 : a ≠ 2) : a = 1 := by
  revert h0 h2; revert a; decide

/-- **Strict Sperner core.**  Under the strict boundary conditions, some
triangle of the lower-left triangulation is rainbow. -/
private lemma strict_sperner (n : ℕ) (_hn1 : 1 ≤ n) (L : ℕ → ℕ → Fin 3)
    (hright : ∀ j ≤ n, L n j = 0) (hleft : ∀ j ≤ n, L 0 j ≠ 0)
    (hbot : ∀ i ≤ n, L i 0 ≠ 2) (htop : ∀ i ≤ n, L i n ≠ 1) :
    ∃ i < n, ∃ j < n,
      isRainbow (L i j) (L (i + 1) j) (L (i + 1) (j + 1)) ∨
      isRainbow (L i j) (L i (j + 1)) (L (i + 1) (j + 1)) := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  replace hcon : ∀ i, i < n → ∀ j, j < n →
      ¬ isRainbow (L i j) (L (i + 1) j) (L (i + 1) (j + 1)) ∧
      ¬ isRainbow (L i j) (L i (j + 1)) (L (i + 1) (j + 1)) := by
    intro i hi j hj; exact not_or.1 (hcon i hi j hj)
  -- `hcon : ∀ i, i < n → ∀ j, j < n → ¬P ∧ ¬Q`
  -- `doorsLow` matches `dind a b + dind a c + dind b c` for the T_low vertices.
  have lowEq : ∀ i j, doorsLow L i j
      = dind (L i j) (L (i + 1) j) + dind (L i j) (L (i + 1) (j + 1))
        + dind (L (i + 1) j) (L (i + 1) (j + 1)) := fun i j => rfl
  have upEq : ∀ i j, doorsUp L i j
      = dind (L i j) (L i (j + 1)) + dind (L i j) (L (i + 1) (j + 1))
        + dind (L i (j + 1)) (L (i + 1) (j + 1)) := by
    intro i j; unfold doorsUp vD gD; ring
  -- The total door count is 0.
  have htot0 : (∑ i ∈ range n, ∑ j ∈ range n, (doorsLow L i j + doorsUp L i j)) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    apply Finset.sum_eq_zero; intro j hj
    rw [Finset.mem_range] at hi hj
    obtain ⟨hnr1, hnr2⟩ := hcon i hi j hj
    rw [lowEq, upEq, doors_even_of_not_rainbow _ _ _ hnr1,
      doors_even_of_not_rainbow _ _ _ hnr2, add_zero]
  -- The total door count collapses to the boundary, which equals the bottom doors = 1.
  rw [total_doors_eq_boundary] at htot0
  -- kill top, left, right
  have htop0 : (∑ i ∈ range n, hD L i n) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    rw [Finset.mem_range] at hi
    have hin : i ≤ n := le_of_lt hi
    have hi1 : i + 1 ≤ n := hi
    have d0 : ∀ a b : Fin 3, a ≠ 1 → b ≠ 1 → dind a b = 0 := by decide
    exact d0 (L i n) (L (i + 1) n) (htop i hin) (htop (i + 1) hi1)
  have hleft0 : (∑ j ∈ range n, vD L 0 j) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := le_of_lt hj
    have hj1 : j + 1 ≤ n := hj
    have d0 : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → dind a b = 0 := by decide
    exact d0 (L 0 j) (L 0 (j + 1)) (hleft j hjn) (hleft (j + 1) hj1)
  have hright0 : (∑ j ∈ range n, vD L n j) = 0 := by
    apply Finset.sum_eq_zero; intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j ≤ n := le_of_lt hj
    have hj1 : j + 1 ≤ n := hj
    have : vD L n j = dind (L n j) (L n (j + 1)) := rfl
    rw [this, hright j hjn, hright (j + 1) hj1]
    decide
  -- Simplify the boundary sum.
  have hsplit : (∑ i ∈ range n, (hD L i 0 + hD L i n))
      + (∑ j ∈ range n, (vD L 0 j + vD L n j))
      = (∑ i ∈ range n, hD L i 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htop0, hleft0, hright0]
    simp
  rw [hsplit] at htot0
  -- The bottom sum is 1.
  have hc0 : L 0 0 = 1 := eq_one_of_ne (L 0 0) (hleft 0 (Nat.zero_le n)) (hbot 0 (Nat.zero_le n))
  have hcn : L n 0 = 0 := hright 0 (Nat.zero_le n)
  have hbottom := bottom_doors_odd L n hbot hc0 hcn
  rw [hbottom] at htot0
  exact (by decide : (1 : ZMod 2) ≠ 0) htot0

/-! ### Labeling derived from two real functions, and the rainbow → goal step. -/

open Classical in
/-- Poincaré–Miranda labeling of a vertex from grid values `x = u(·)`, `y = v(·)`:
label `0` if `x > 0`, else `1` if `y > 0`, else `2`. -/
noncomputable def label (x y : ℝ) : Fin 3 :=
  if x > 0 then 0 else if y > 0 then 1 else 2

private lemma label_left_ne (x y : ℝ) (h : ¬ x > 0) : label x y ≠ 0 := by
  unfold label; rw [if_neg h]; by_cases hy : y > 0
  · rw [if_pos hy]; decide
  · rw [if_neg hy]; decide

private lemma label_ne_two (x y : ℝ) (h : y > 0) : label x y ≠ 2 := by
  unfold label; by_cases hx : x > 0
  · rw [if_pos hx]; decide
  · rw [if_neg hx, if_pos h]; decide

private lemma label_ne_one (x y : ℝ) (h : ¬ y > 0) : label x y ≠ 1 := by
  unfold label; by_cases hx : x > 0
  · rw [if_pos hx]; decide
  · rw [if_neg hx, if_neg h]; decide

private lemma label_eq_zero (x y : ℝ) (h : x > 0) : label x y = 0 := by
  unfold label; rw [if_pos h]

private lemma label_zero_inv (x y : ℝ) (h : label x y = 0) : x > 0 := by
  unfold label at h; by_contra hx; rw [if_neg hx] at h; split at h <;> simp_all

private lemma label_one_inv (x y : ℝ) (h : label x y = 1) : ¬ x > 0 ∧ y > 0 := by
  unfold label at h
  by_cases hx : x > 0
  · rw [if_pos hx] at h; exact absurd h (by decide)
  · rw [if_neg hx] at h
    by_cases hy : y > 0
    · exact ⟨hx, hy⟩
    · rw [if_neg hy] at h; exact absurd h (by decide)

private lemma label_two_inv (x y : ℝ) (h : label x y = 2) : ¬ x > 0 ∧ ¬ y > 0 := by
  unfold label at h
  by_cases hx : x > 0
  · rw [if_pos hx] at h; exact absurd h (by decide)
  · rw [if_neg hx] at h
    by_cases hy : y > 0
    · rw [if_pos hy] at h; exact absurd h (by decide)
    · exact ⟨hx, hy⟩

/-- If, among the four corners of cell `(i,j)`, the labels `0`, `1`, `2` all
appear (each at some corner), then the cell is bichromatic in both `U` and `V`. -/
private lemma goal_of_three_labels (U V : ℕ → ℕ → ℝ) (i j : ℕ)
    (h0 : ∃ p ∈ cellCorners i j, label (U p.1 p.2) (V p.1 p.2) = 0)
    (h1 : ∃ p ∈ cellCorners i j, label (U p.1 p.2) (V p.1 p.2) = 1)
    (h2 : ∃ p ∈ cellCorners i j, label (U p.1 p.2) (V p.1 p.2) = 2) :
    (∃ p ∈ cellCorners i j, U p.1 p.2 ≤ 0) ∧ (∃ p ∈ cellCorners i j, 0 ≤ U p.1 p.2) ∧
    (∃ p ∈ cellCorners i j, V p.1 p.2 ≤ 0) ∧ (∃ p ∈ cellCorners i j, 0 ≤ V p.1 p.2) := by
  obtain ⟨p0, hp0, e0⟩ := h0
  obtain ⟨p1, hp1, e1⟩ := h1
  obtain ⟨p2, hp2, e2⟩ := h2
  have k0 := label_zero_inv _ _ e0   -- U p0 > 0
  have k1 := label_one_inv _ _ e1     -- ¬ U p1 > 0 ∧ V p1 > 0
  have k2 := label_two_inv _ _ e2     -- ¬ U p2 > 0 ∧ ¬ V p2 > 0
  refine ⟨⟨p1, hp1, le_of_not_gt k1.1⟩, ⟨p0, hp0, le_of_lt k0⟩,
    ⟨p2, hp2, le_of_not_gt k2.2⟩, ⟨p1, hp1, le_of_lt k1.2⟩⟩

private lemma corner_lj (i j : ℕ) : (i, j) ∈ cellCorners i j := by
  unfold cellCorners; simp
private lemma corner_rj (i j : ℕ) : (i + 1, j) ∈ cellCorners i j := by
  unfold cellCorners; simp
private lemma corner_lu (i j : ℕ) : (i, j + 1) ∈ cellCorners i j := by
  unfold cellCorners; simp
private lemma corner_ru (i j : ℕ) : (i + 1, j + 1) ∈ cellCorners i j := by
  unfold cellCorners; simp

/-- From a rainbow triple over three corners (with membership proofs), extract the
three "label `k` appears at a corner" facts. -/
private lemma three_labels_of_rainbow (U V : ℕ → ℕ → ℝ) (i j : ℕ)
    (a b c : ℕ × ℕ) (ha : a ∈ cellCorners i j) (hb : b ∈ cellCorners i j)
    (hc : c ∈ cellCorners i j)
    (hr : isRainbow (label (U a.1 a.2) (V a.1 a.2)) (label (U b.1 b.2) (V b.1 b.2))
          (label (U c.1 c.2) (V c.1 c.2))) :
    (∃ p ∈ cellCorners i j, label (U p.1 p.2) (V p.1 p.2) = 0) ∧
    (∃ p ∈ cellCorners i j, label (U p.1 p.2) (V p.1 p.2) = 1) ∧
    (∃ p ∈ cellCorners i j, label (U p.1 p.2) (V p.1 p.2) = 2) := by
  obtain ⟨r0, r1, r2⟩ := hr
  refine ⟨?_, ?_, ?_⟩
  · rcases r0 with h | h | h
    · exact ⟨a, ha, h⟩
    · exact ⟨b, hb, h⟩
    · exact ⟨c, hc, h⟩
  · rcases r1 with h | h | h
    · exact ⟨a, ha, h⟩
    · exact ⟨b, hb, h⟩
    · exact ⟨c, hc, h⟩
  · rcases r2 with h | h | h
    · exact ⟨a, ha, h⟩
    · exact ⟨b, hb, h⟩
    · exact ⟨c, hc, h⟩

/-- For fixed perturbed data `U, V`, a rainbow triangle (from `strict_sperner`)
yields the goal cell. -/
private lemma exists_goal_cell_of_strict (n : ℕ) (hn1 : 1 ≤ n) (U V : ℕ → ℕ → ℝ)
    (hright : ∀ j ≤ n, U n j > 0)
    (hleft : ∀ j ≤ n, ¬ U 0 j > 0)
    (hbot : ∀ i ≤ n, V i 0 > 0)
    (htop : ∀ i ≤ n, ¬ V i n > 0) :
    ∃ i < n, ∃ j < n,
      (∃ p ∈ cellCorners i j, U p.1 p.2 ≤ 0) ∧ (∃ p ∈ cellCorners i j, 0 ≤ U p.1 p.2) ∧
      (∃ p ∈ cellCorners i j, V p.1 p.2 ≤ 0) ∧ (∃ p ∈ cellCorners i j, 0 ≤ V p.1 p.2) := by
  set L : ℕ → ℕ → Fin 3 := fun i j => label (U i j) (V i j) with hL
  have bRight : ∀ j ≤ n, L n j = 0 := fun j hj => label_eq_zero _ _ (hright j hj)
  have bLeft : ∀ j ≤ n, L 0 j ≠ 0 := fun j hj => label_left_ne _ _ (hleft j hj)
  have bBot : ∀ i ≤ n, L i 0 ≠ 2 := fun i hi => label_ne_two _ _ (hbot i hi)
  have bTop : ∀ i ≤ n, L i n ≠ 1 := fun i hi => label_ne_one _ _ (htop i hi)
  obtain ⟨i, hi, j, hj, hrain⟩ := strict_sperner n hn1 L bRight bLeft bBot bTop
  refine ⟨i, hi, j, hj, ?_⟩
  rcases hrain with hlow | hup
  · -- T_low: corners (i,j),(i+1,j),(i+1,j+1)
    obtain ⟨t0, t1, t2⟩ := three_labels_of_rainbow U V i j (i, j) (i + 1, j) (i + 1, j + 1)
      (corner_lj i j) (corner_rj i j) (corner_ru i j) hlow
    exact goal_of_three_labels U V i j t0 t1 t2
  · -- T_up: corners (i,j),(i,j+1),(i+1,j+1)
    obtain ⟨t0, t1, t2⟩ := three_labels_of_rainbow U V i j (i, j) (i, j + 1) (i + 1, j + 1)
      (corner_lj i j) (corner_lu i j) (corner_ru i j) hup
    exact goal_of_three_labels U V i j t0 t1 t2

/-! ### Perturbation and limit. -/

open Filter Topology

/-- Pigeonhole into a finite type along a `frequently` predicate. -/
private lemma freq_pigeon_inf {β : Type} [Finite β] (P : ℕ → Prop) (F : ℕ → β)
    (h : ∃ᶠ k in atTop, P k) : ∃ y : β, ∃ᶠ k in atTop, (P k ∧ F k = y) := by
  by_contra hc
  simp only [not_exists, Filter.not_frequently, not_and] at hc
  have hall : ∀ᶠ k in atTop, ∀ y, P k → F k ≠ y := eventually_all.2 hc
  have : ∃ᶠ k in atTop, P k ∧ (∀ y, P k → F k ≠ y) := h.and_eventually hall
  obtain ⟨k, hPk, hk⟩ := this.exists
  exact hk (F k) hPk rfl

/-- Limit of a `≤ 0` witness over a fixed finset: if frequently some element of `s`
satisfies `f k p ≤ 0`, and each `f · p` converges to `g p`, then some `p ∈ s` has
`g p ≤ 0`. -/
private lemma limit_witness_le {ι : Type} (s : Finset ι)
    (f : ℕ → ι → ℝ) (g : ι → ℝ)
    (hconv : ∀ p ∈ s, Tendsto (fun k => f k p) atTop (𝓝 (g p)))
    (hwit : ∃ᶠ k in atTop, ∃ p ∈ s, f k p ≤ 0) :
    ∃ p ∈ s, g p ≤ 0 := by
  classical
  -- Choose a witnessing element for every `k` (junk when the witness fails).
  have hwit' : ∀ k, ∃ p : {x // x ∈ s}, (∃ q ∈ s, f k q ≤ 0) → f k p.1 ≤ 0 := by
    intro k
    by_cases h : ∃ q ∈ s, f k q ≤ 0
    · obtain ⟨q, hq, hle⟩ := h
      exact ⟨⟨q, hq⟩, fun _ => hle⟩
    · -- pick any element of s (s is nonempty because the frequently hyp will be used elsewhere);
      -- but here just need an element; use a default via the frequently witness existence.
      -- s nonempty: from hwit there is some k with a witness, so s nonempty.
      have hne : s.Nonempty := by
        obtain ⟨k0, q, hq, _⟩ := hwit.exists
        exact ⟨q, hq⟩
      exact ⟨⟨hne.choose, hne.choose_spec⟩, fun hcontra => absurd hcontra h⟩
  choose W hW using hwit'
  obtain ⟨y, hy⟩ := freq_pigeon_inf (fun k => ∃ q ∈ s, f k q ≤ 0) W hwit
  refine ⟨y.1, y.2, ?_⟩
  have hconvY : Tendsto (fun k => f k y.1) atTop (𝓝 (g y.1)) := hconv y.1 y.2
  have hfreq : ∃ᶠ k in atTop, f k y.1 ≤ 0 := by
    apply hy.mono
    rintro k ⟨hPk, hWk⟩
    have hle := hW k hPk
    rw [hWk] at hle
    exact hle
  exact le_of_tendsto_of_frequently hconvY hfreq

/-- Limit of a `0 ≤` witness, dual of `limit_witness_le`. -/
private lemma limit_witness_ge {ι : Type} (s : Finset ι)
    (f : ℕ → ι → ℝ) (g : ι → ℝ)
    (hconv : ∀ p ∈ s, Tendsto (fun k => f k p) atTop (𝓝 (g p)))
    (hwit : ∃ᶠ k in atTop, ∃ p ∈ s, 0 ≤ f k p) :
    ∃ p ∈ s, 0 ≤ g p := by
  have hconv' : ∀ p ∈ s, Tendsto (fun k => -(f k p)) atTop (𝓝 (-(g p))) :=
    fun p hp => (hconv p hp).neg
  have hwit' : ∃ᶠ k in atTop, ∃ p ∈ s, (fun k p => -(f k p)) k p ≤ 0 := by
    apply hwit.mono; rintro k ⟨p, hp, hle⟩; exact ⟨p, hp, by simpa using hle⟩
  obtain ⟨p, hp, hle⟩ := limit_witness_le s (fun k p => -(f k p)) (fun p => -(g p)) hconv' hwit'
  exact ⟨p, hp, by linarith⟩

/-- The perturbed `u`-values: `Uε k i j = u i j + (1/(k+1))·(2i - n)`. -/
private noncomputable def Uε (u : ℕ → ℕ → ℝ) (n k : ℕ) (i j : ℕ) : ℝ :=
  u i j + (1 / ((k : ℝ) + 1)) * (2 * (i : ℝ) - n)

/-- The perturbed `v`-values: `Vε k i j = v i j + (1/(k+1))·(n - 2j)`. -/
private noncomputable def Vε (v : ℕ → ℕ → ℝ) (n k : ℕ) (i j : ℕ) : ℝ :=
  v i j + (1 / ((k : ℝ) + 1)) * ((n : ℝ) - 2 * (j : ℝ))

private lemma Uε_tendsto (u : ℕ → ℕ → ℝ) (n i j : ℕ) :
    Tendsto (fun k => Uε u n k i j) atTop (𝓝 (u i j)) := by
  unfold Uε
  have h0 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have : Tendsto (fun k : ℕ => u i j + (1 / ((k:ℝ) + 1)) * (2 * (i:ℝ) - n)) atTop
      (𝓝 (u i j + 0 * (2 * (i:ℝ) - n))) :=
    (h0.mul_const _).const_add _
  simpa using this

private lemma Vε_tendsto (v : ℕ → ℕ → ℝ) (n i j : ℕ) :
    Tendsto (fun k => Vε v n k i j) atTop (𝓝 (v i j)) := by
  unfold Vε
  have h0 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have : Tendsto (fun k : ℕ => v i j + (1 / ((k:ℝ) + 1)) * ((n:ℝ) - 2 * (j:ℝ))) atTop
      (𝓝 (v i j + 0 * ((n:ℝ) - 2 * (j:ℝ)))) :=
    (h0.mul_const _).const_add _
  simpa using this

/-- **Discrete Poincaré–Miranda lemma on an `n × n` grid**.

This is the genuinely combinatorial heart of the two-dimensional
intermediate value theorem, equivalent to **Sperner's lemma**.

Consider real values `u v : ℕ → ℕ → ℝ` on the grid `{0, …, n}²`
(`n ≥ 1`). Assume the discrete edge-sign conditions:

* `u` is `≤ 0` on the left column (`i = 0`) and `≥ 0` on the right column
  (`i = n`);
* `v` is `≥ 0` on the bottom row (`j = 0`) and `≤ 0` on the top row
  (`j = n`).

Then some unit cell of the grid is **bichromatic in both coordinates**:
there is a cell `(i, j)` (with `i, j < n`) across whose four corners `u`
takes both a nonpositive and a nonnegative value, and likewise `v`.

The proof is the standard Sperner argument for the lower-left triangulation
of the square. The labeling `label x y = 0 / 1 / 2` according to the first
of `x > 0`, `y > 0` that holds turns the grid into a Sperner coloring; a
mod-`2` door-counting double count (`strict_sperner`) produces a rainbow
triangle under *strict* boundary conditions, and its three labels give all
four sign witnesses on the enclosing cell. The non-strict boundary
hypotheses are handled by perturbing `u, v` by a vanishing linear term
(`Uε`, `Vε`) to make all four boundary inequalities strict, then passing to
the limit (`limit_witness_le`, `limit_witness_ge`) along a frequently-hit
cell. Mathlib has no Sperner's lemma / Brouwer fixed point theorem, so the
combinatorial argument is developed from scratch in the private lemmas
above. -/
theorem discrete_poincare_miranda
    {n : ℕ} (hn : 1 ≤ n) (u v : ℕ → ℕ → ℝ)
    (hu_left : ∀ j ≤ n, u 0 j ≤ 0) (hu_right : ∀ j ≤ n, 0 ≤ u n j)
    (hv_bot : ∀ i ≤ n, 0 ≤ v i 0) (hv_top : ∀ i ≤ n, v i n ≤ 0) :
    ∃ i < n, ∃ j < n,
      (∃ p ∈ cellCorners i j, u p.1 p.2 ≤ 0) ∧ (∃ p ∈ cellCorners i j, 0 ≤ u p.1 p.2) ∧
      (∃ p ∈ cellCorners i j, v p.1 p.2 ≤ 0) ∧ (∃ p ∈ cellCorners i j, 0 ≤ v p.1 p.2) := by
  classical
  -- The finite set of cells.
  set C : Finset (ℕ × ℕ) := (range n) ×ˢ (range n) with hC
  -- For each `k`, the perturbed data satisfies the strict boundary conditions, hence
  -- yields a goal cell.
  have hεpos : ∀ k : ℕ, (1 / ((k:ℝ) + 1)) > 0 := by
    intro k; positivity
  have perCell : ∀ k : ℕ, ∃ c ∈ C, ∃ hij : c.1 < n ∧ c.2 < n,
      (∃ p ∈ cellCorners c.1 c.2, Uε u n k p.1 p.2 ≤ 0) ∧
      (∃ p ∈ cellCorners c.1 c.2, 0 ≤ Uε u n k p.1 p.2) ∧
      (∃ p ∈ cellCorners c.1 c.2, Vε v n k p.1 p.2 ≤ 0) ∧
      (∃ p ∈ cellCorners c.1 c.2, 0 ≤ Vε v n k p.1 p.2) := by
    intro k
    set ε := (1 / ((k:ℝ) + 1)) with hε
    have hεp : ε > 0 := hεpos k
    have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hεn : ε * (n:ℝ) > 0 := mul_pos hεp (by linarith)
    -- strict boundary conditions
    have hright : ∀ j ≤ n, Uε u n k n j > 0 := by
      intro j hj; unfold Uε; rw [← hε]
      have : (2 * (n:ℝ) - n) = n := by ring
      rw [this]; have := hu_right j hj; linarith
    have hleft : ∀ j ≤ n, ¬ Uε u n k 0 j > 0 := by
      intro j hj; unfold Uε; rw [← hε, gt_iff_lt, not_lt]
      have h1 : (2 * ((0:ℕ):ℝ) - n) = -(n:ℝ) := by push_cast; ring
      rw [h1]; have := hu_left j hj; nlinarith [hεn]
    have hbot : ∀ i ≤ n, Vε v n k i 0 > 0 := by
      intro i hi; unfold Vε; rw [← hε]
      have h1 : ((n:ℝ) - 2 * ((0:ℕ):ℝ)) = (n:ℝ) := by push_cast; ring
      rw [h1]; have := hv_bot i hi; linarith
    have htop : ∀ i ≤ n, ¬ Vε v n k i n > 0 := by
      intro i hi; unfold Vε; rw [← hε, gt_iff_lt, not_lt]
      have h1 : ((n:ℝ) - 2 * (n:ℝ)) = -(n:ℝ) := by ring
      rw [h1]; have := hv_top i hi; nlinarith [hεn]
    obtain ⟨i, hi, j, hj, hgoal⟩ :=
      exists_goal_cell_of_strict n hn (Uε u n k) (Vε v n k) hright hleft hbot htop
    refine ⟨(i, j), ?_, ⟨hi, hj⟩, hgoal⟩
    simp only [hC, Finset.mem_product, Finset.mem_range]; exact ⟨hi, hj⟩
  -- Choose, for every `k`, such a cell `c k ∈ C`.
  choose cell hcellC hcellLt hgoalAll using perCell
  -- Pigeonhole: some cell is hit frequently.
  -- Move to the finite subtype.
  set F : ℕ → {p // p ∈ C} := fun k => ⟨cell k, hcellC k⟩ with hF
  have hfreqTrue : ∃ᶠ _k in (atTop : Filter ℕ), True :=
    Filter.Frequently.of_forall (fun _ => trivial)
  obtain ⟨y, hy⟩ := freq_pigeon_inf (fun _ => True) F hfreqTrue
  set i0 := y.1.1 with hi0
  set j0 := y.1.2 with hj0
  have hyeq : y.1 = (i0, j0) := by rw [hi0, hj0]
  have hy0 : y.1 ∈ C := y.2
  have hij0 : i0 < n ∧ j0 < n := by
    rw [hyeq, hC, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy0; exact hy0
  -- frequently, `cell k = (i0, j0)`.
  have hfreqCell : ∃ᶠ k in atTop, cell k = (i0, j0) := by
    apply hy.mono; rintro k ⟨_, hFk⟩
    have hcv := congrArg Subtype.val hFk
    rw [hF] at hcv
    simp only at hcv
    rw [hcv, ← hyeq]
  refine ⟨i0, hij0.1, j0, hij0.2, ?_, ?_, ?_, ?_⟩
  · -- u ≤ 0 witness
    apply limit_witness_le (cellCorners i0 j0) (fun k p => Uε u n k p.1 p.2)
      (fun p => u p.1 p.2)
    · intro p _; exact Uε_tendsto u n p.1 p.2
    · apply hfreqCell.mono; intro k hk
      have := (hgoalAll k).1
      rw [hk] at this; exact this
  · apply limit_witness_ge (cellCorners i0 j0) (fun k p => Uε u n k p.1 p.2)
      (fun p => u p.1 p.2)
    · intro p _; exact Uε_tendsto u n p.1 p.2
    · apply hfreqCell.mono; intro k hk
      have := (hgoalAll k).2.1
      rw [hk] at this; exact this
  · apply limit_witness_le (cellCorners i0 j0) (fun k p => Vε v n k p.1 p.2)
      (fun p => v p.1 p.2)
    · intro p _; exact Vε_tendsto v n p.1 p.2
    · apply hfreqCell.mono; intro k hk
      have := (hgoalAll k).2.2.1
      rw [hk] at this; exact this
  · apply limit_witness_ge (cellCorners i0 j0) (fun k p => Vε v n k p.1 p.2)
      (fun p => v p.1 p.2)
    · intro p _; exact Vε_tendsto v n p.1 p.2
    · apply hfreqCell.mono; intro k hk
      have := (hgoalAll k).2.2.2
      rw [hk] at this; exact this


end SpernerCombinatorics

/-- **Approximate Poincaré–Miranda theorem**.

Under the Poincaré–Miranda sign hypotheses, `f` and `g` have a common
*approximate* zero: for every `ε > 0` there is a point of the closed unit
square at which both `|f|` and `|g|` are strictly below `ε`.

It is proved from the discrete Poincaré–Miranda lemma
`discrete_poincare_miranda` (the Sperner core): for a grid fine enough that
Heine–Cantor uniform continuity makes the oscillation of `f, g` below `ε`
on every cell, the discrete lemma yields a single cell across whose corners
both coordinate functions change sign, and "changes sign on a small cell"
then forces "is small at a corner". The exact theorem
`poincare_miranda_unit_square` is in turn derived from this by a
compactness limit (no further topological input). -/
theorem poincare_miranda_approx
    {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hf_left : ∀ t ∈ Icc (0 : ℝ) 1, f 0 t ≤ 0)
    (hf_right : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f 1 t)
    (hg_bot : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ g s 0)
    (hg_top : ∀ s ∈ Icc (0 : ℝ) 1, g s 1 ≤ 0) :
    ∀ ε > (0 : ℝ), ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      |f s t| < ε ∧ |g s t| < ε := by
  intro ε hε
  -- Setup: the compact square and the coordinate maps on `ℝ × ℝ`.
  set K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hK_def
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  set F : ℝ × ℝ → ℝ := fun q => f q.1 q.2 with hF_def
  set G : ℝ × ℝ → ℝ := fun q => g q.1 q.2 with hG_def
  -- Uniform continuity (Heine–Cantor) gives a single modulus `δ` for both `F` and `G`.
  obtain ⟨δf, hδf_pos, hδf⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous hf)) ε hε
  obtain ⟨δg, hδg_pos, hδg⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous hg)) ε hε
  set δ : ℝ := min δf δg with hδ_def
  have hδ_pos : 0 < δ := lt_min hδf_pos hδg_pos
  -- Choose a grid fineness `N ≥ 1` with cell width `1 / N < δ`.
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ_pos
  set N : ℕ := m + 1 with hN_def
  have hN1 : 1 ≤ N := Nat.le_add_left 1 m
  have hNpos : (0 : ℝ) < N := by positivity
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hwidth : (1 : ℝ) / N < δ := by simpa [hN_def] using hm
  -- A grid index `k ≤ N` gives a point `k / N ∈ [0, 1]`.
  have hgrid_mem : ∀ k : ℕ, k ≤ N → (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    constructor
    · positivity
    · rw [div_le_one hNpos]; exact_mod_cast hk
  -- Grid values feeding the discrete lemma.
  set u : ℕ → ℕ → ℝ := fun i j => f ((i : ℝ) / N) ((j : ℝ) / N) with hu_def
  set v : ℕ → ℕ → ℝ := fun i j => g ((i : ℝ) / N) ((j : ℝ) / N) with hv_def
  -- Discrete edge-sign conditions, inherited from the continuous ones.
  have hu_left : ∀ j ≤ N, u 0 j ≤ 0 := by
    intro j hj
    simp only [hu_def, Nat.cast_zero, zero_div]
    exact hf_left _ (hgrid_mem j hj)
  have hu_right : ∀ j ≤ N, 0 ≤ u N j := by
    intro j hj
    simp only [hu_def, div_self hNne]
    exact hf_right _ (hgrid_mem j hj)
  have hv_bot : ∀ i ≤ N, 0 ≤ v i 0 := by
    intro i hi
    simp only [hv_def, Nat.cast_zero, zero_div]
    exact hg_bot _ (hgrid_mem i hi)
  have hv_top : ∀ i ≤ N, v i N ≤ 0 := by
    intro i hi
    simp only [hv_def, div_self hNne]
    exact hg_top _ (hgrid_mem i hi)
  -- Apply the discrete Poincaré–Miranda lemma.
  obtain ⟨i, hi, j, hj, ⟨pu0, hpu0_mem, hpu0⟩, ⟨pu1, hpu1_mem, hpu1⟩,
      ⟨pv0, hpv0_mem, hpv0⟩, ⟨pv1, hpv1_mem, hpv1⟩⟩ :=
    discrete_poincare_miranda hN1 u v hu_left hu_right hv_bot hv_top
  -- The corner point we will return.
  set s : ℝ := (i : ℝ) / N with hs_def
  set t : ℝ := (j : ℝ) / N with ht_def
  have his : i ≤ N := le_of_lt hi
  have hjs : j ≤ N := le_of_lt hj
  have hs_mem : s ∈ Icc (0 : ℝ) 1 := hgrid_mem i his
  have ht_mem : t ∈ Icc (0 : ℝ) 1 := hgrid_mem j hjs
  -- Every corner of the cell is a grid point in the square, within `δ` of `(s, t)`.
  -- A coordinate index of the cell is `i` or `i + 1`; both are `≤ N`.
  have hcorner_mem : ∀ p : ℕ × ℕ, p ∈ cellCorners i j →
      ((p.1 : ℝ) / N, (p.2 : ℝ) / N) ∈ K ∧
      dist ((p.1 : ℝ) / N, (p.2 : ℝ) / N) (s, t) < δ := by
    intro p hp
    -- The corner indices are bounded by `i + 1 ≤ N` and `j + 1 ≤ N`.
    have hp1_le : p.1 ≤ N := by
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h <;>
        (rw [Prod.ext_iff] at h; rw [h.1]) <;> omega
    have hp2_le : p.2 ≤ N := by
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h <;>
        (rw [Prod.ext_iff] at h; rw [h.2]) <;> omega
    -- The corner indices differ from `(i, j)` by at most `1`.
    have hp1_close : ((p.1 : ℝ) - i) ≤ 1 ∧ (-(1 : ℝ)) ≤ ((p.1 : ℝ) - i) := by
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h <;>
        (rw [Prod.ext_iff] at h; rw [h.1]) <;> push_cast <;> constructor <;> linarith
    have hp2_close : ((p.2 : ℝ) - j) ≤ 1 ∧ (-(1 : ℝ)) ≤ ((p.2 : ℝ) - j) := by
      simp only [cellCorners, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h | h | h <;>
        (rw [Prod.ext_iff] at h; rw [h.2]) <;> push_cast <;> constructor <;> linarith
    refine ⟨Set.mk_mem_prod (hgrid_mem p.1 hp1_le) (hgrid_mem p.2 hp2_le), ?_⟩
    -- Bound the sup-distance by `1 / N < δ`.
    rw [Prod.dist_eq]
    apply max_lt
    · rw [Real.dist_eq, hs_def]
      rw [show (p.1 : ℝ) / N - (i : ℝ) / N = ((p.1 : ℝ) - i) / N by ring]
      rw [abs_div, abs_of_pos hNpos]
      rw [div_lt_iff₀ hNpos]
      have : |(p.1 : ℝ) - i| ≤ 1 := abs_le.mpr ⟨hp1_close.2, hp1_close.1⟩
      calc |(p.1 : ℝ) - i| ≤ 1 := this
        _ = (1 / N) * N := by field_simp
        _ < δ * N := by apply mul_lt_mul_of_pos_right hwidth hNpos
    · rw [Real.dist_eq, ht_def]
      rw [show (p.2 : ℝ) / N - (j : ℝ) / N = ((p.2 : ℝ) - j) / N by ring]
      rw [abs_div, abs_of_pos hNpos]
      rw [div_lt_iff₀ hNpos]
      have : |(p.2 : ℝ) - j| ≤ 1 := abs_le.mpr ⟨hp2_close.2, hp2_close.1⟩
      calc |(p.2 : ℝ) - j| ≤ 1 := this
        _ = (1 / N) * N := by field_simp
        _ < δ * N := by apply mul_lt_mul_of_pos_right hwidth hNpos
  -- The base corner is in `K`.
  have hst_mem : (s, t) ∈ K := Set.mk_mem_prod hs_mem ht_mem
  -- Uniform-continuity bound: `|F c - F (s,t)| < ε` for any cell corner `c`.
  have hF_close : ∀ p : ℕ × ℕ, p ∈ cellCorners i j →
      |F ((p.1 : ℝ) / N, (p.2 : ℝ) / N) - F (s, t)| < ε := by
    intro p hp
    obtain ⟨hp_mem, hp_dist⟩ := hcorner_mem p hp
    have := hδf ((p.1 : ℝ) / N, (p.2 : ℝ) / N) hp_mem (s, t) hst_mem
      (lt_of_lt_of_le hp_dist (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have hG_close : ∀ p : ℕ × ℕ, p ∈ cellCorners i j →
      |G ((p.1 : ℝ) / N, (p.2 : ℝ) / N) - G (s, t)| < ε := by
    intro p hp
    obtain ⟨hp_mem, hp_dist⟩ := hcorner_mem p hp
    have := hδg ((p.1 : ℝ) / N, (p.2 : ℝ) / N) hp_mem (s, t) hst_mem
      (lt_of_lt_of_le hp_dist (min_le_right _ _))
    rwa [Real.dist_eq] at this
  -- Now bound `|F (s,t)| = |f s t|`. We have a corner where `u ≤ 0` and one where `u ≥ 0`,
  -- and `F` at each corner equals `u` there; with the modulus bound this forces `|F (s,t)| < ε`.
  have hFval : ∀ p : ℕ × ℕ, F ((p.1 : ℝ) / N, (p.2 : ℝ) / N) = u p.1 p.2 := by
    intro p; rfl
  have hGval : ∀ p : ℕ × ℕ, G ((p.1 : ℝ) / N, (p.2 : ℝ) / N) = v p.1 p.2 := by
    intro p; rfl
  refine ⟨s, hs_mem, t, ht_mem, ?_, ?_⟩
  · -- `|f s t| < ε`, i.e. `|F (s,t)| < ε`.
    rw [abs_lt]
    constructor
    · -- `-ε < F (s,t)`: use the corner where `u ≥ 0`.
      have h1 := hF_close pu1 hpu1_mem
      have h2 : 0 ≤ F ((pu1.1 : ℝ) / N, (pu1.2 : ℝ) / N) := by rw [hFval]; exact hpu1
      rw [abs_lt] at h1
      have hFst : F (s, t) = f s t := rfl
      rw [hFst] at h1
      linarith [h1.1, h2]
    · -- `F (s,t) < ε`: use the corner where `u ≤ 0`.
      have h1 := hF_close pu0 hpu0_mem
      have h2 : F ((pu0.1 : ℝ) / N, (pu0.2 : ℝ) / N) ≤ 0 := by rw [hFval]; exact hpu0
      rw [abs_lt] at h1
      have hFst : F (s, t) = f s t := rfl
      rw [hFst] at h1
      linarith [h1.2]
  · -- `|g s t| < ε`, symmetric, using `v`.
    rw [abs_lt]
    constructor
    · have h1 := hG_close pv1 hpv1_mem
      have h2 : 0 ≤ G ((pv1.1 : ℝ) / N, (pv1.2 : ℝ) / N) := by rw [hGval]; exact hpv1
      rw [abs_lt] at h1
      have hGst : G (s, t) = g s t := rfl
      rw [hGst] at h1
      linarith [h1.1, h2]
    · have h1 := hG_close pv0 hpv0_mem
      have h2 : G ((pv0.1 : ℝ) / N, (pv0.2 : ℝ) / N) ≤ 0 := by rw [hGval]; exact hpv0
      rw [abs_lt] at h1
      have hGst : G (s, t) = g s t := rfl
      rw [hGst] at h1
      linarith [h1.2]

/-- **Poincaré–Miranda theorem on the closed unit square**.

Let `f g : ℝ → ℝ → ℝ` be continuous on the closed unit square
`Icc 0 1 ×ˢ Icc 0 1`. Suppose the first coordinate `f` is `≤ 0` on the
left edge (`s = 0`) and `≥ 0` on the right edge (`s = 1`), and the second
coordinate `g` is `≥ 0` on the bottom edge (`t = 0`) and `≤ 0` on the top
edge (`t = 1`). Then `f` and `g` have a common zero in the square.

This is the two-dimensional intermediate value theorem (Poincaré 1883 /
Miranda 1940, equivalent to the Brouwer fixed point theorem). It is proved
here from `poincare_miranda_approx` — the approximate (combinatorial,
Sperner-flavored) form — by a compactness limit: choosing for each `n` a
point `pₙ` of the square at which `|f|, |g| < 1 / (n + 1)`, sequential
compactness of the square extracts a convergent subsequence whose limit,
by continuity, is a common exact zero. -/
theorem poincare_miranda_unit_square
    {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hf_left : ∀ t ∈ Icc (0 : ℝ) 1, f 0 t ≤ 0)
    (hf_right : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f 1 t)
    (hg_bot : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ g s 0)
    (hg_top : ∀ s ∈ Icc (0 : ℝ) 1, g s 1 ≤ 0) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, f s t = 0 ∧ g s t = 0 := by
  -- The compact unit square.
  set K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hK_def
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  -- Coordinate functions as maps on `ℝ × ℝ`.
  set F : ℝ × ℝ → ℝ := fun q => f q.1 q.2 with hF_def
  set G : ℝ × ℝ → ℝ := fun q => g q.1 q.2 with hG_def
  -- Approximate zeros: for each `n`, pick a point with errors below `1 / (n + 1)`.
  have happrox := poincare_miranda_approx hf hg hf_left hf_right hg_bot hg_top
  have hchoose : ∀ n : ℕ, ∃ q : ℝ × ℝ, q ∈ K ∧ |F q| < 1 / (n + 1) ∧ |G q| < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨s, hs, t, ht, hfs, hgs⟩ := happrox (1 / (n + 1)) hpos
    exact ⟨(s, t), Set.mk_mem_prod hs ht, hfs, hgs⟩
  choose p hp_mem hp_f hp_g using hchoose
  -- Sequential compactness: extract a convergent subsequence.
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq hp_mem
  -- The error sequence along the subsequence tends to `0`.
  have herr : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact hbase.comp hφ_mono.tendsto_atTop
  -- The subsequence tends to `a` within `K` (its terms all lie in `K`).
  have hsub_within : Tendsto (p ∘ φ) atTop (𝓝[K] a) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hφ_tendsto, Filter.Eventually.of_forall (fun k => hp_mem (φ k))⟩
  -- `F` and `G` are continuous within `K` at the limit point `a`.
  have hFa : Tendsto (F ∘ (p ∘ φ)) atTop (𝓝 (F a)) :=
    (hf.continuousWithinAt ha_mem).tendsto.comp hsub_within
  have hGa : Tendsto (G ∘ (p ∘ φ)) atTop (𝓝 (G a)) :=
    (hg.continuousWithinAt ha_mem).tendsto.comp hsub_within
  -- The values `F (p (φ k))` tend to `0` (squeezed by the error sequence).
  have hF0 : Tendsto (fun k : ℕ => F (p (φ k))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) herr
    simp only [Real.norm_eq_abs]
    exact (hp_f (φ k)).le
  have hG0 : Tendsto (fun k : ℕ => G (p (φ k))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) herr
    simp only [Real.norm_eq_abs]
    exact (hp_g (φ k)).le
  -- By uniqueness of limits, `F a = 0` and `G a = 0`.
  have hFa0 : F a = 0 := tendsto_nhds_unique hFa hF0
  have hGa0 : G a = 0 := tendsto_nhds_unique hGa hG0
  -- Unpack `a` as a point of the square.
  obtain ⟨ha1, ha2⟩ := Set.mem_prod.mp ha_mem
  exact ⟨a.1, ha1, a.2, ha2, hFa0, hGa0⟩

/-- A point of the closed unit square (encoded in `ℂ` via `×ℂ`) has
real and imaginary parts in `[0,1]`. -/
theorem reProdIm_unitSquare_iff {z : ℂ} :
    z ∈ (Icc (0 : ℝ) 1) ×ℂ (Icc (0 : ℝ) 1) ↔ z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc (0 : ℝ) 1 :=
  Complex.mem_reProdIm

/-- **Planar rectangle crossing lemma.**

In the closed unit square `[0,1]² ⊆ ℂ` (encoded as `Icc 0 1 ×ℂ Icc 0 1`),
a continuous path `α : [0,1] → ℂ` whose real part runs from `0` (left
edge, at `α 0`) to `1` (right edge, at `α 1`) must meet any continuous
path `β : [0,1] → ℂ` whose imaginary part runs from `0` (bottom edge, at
`β 0`) to `1` (top edge, at `β 1`). Both paths are assumed to stay inside
the closed unit square.

This is the two-dimensional intermediate value theorem in the geometric
"a left→right crossing and a bottom→top crossing of a square must
intersect" form. The proof applies `poincare_miranda_unit_square` to the
coordinate functions of `G (s,t) = α s − β t`:
`f s t = (α s − β t).re` and `g s t = (α s − β t).im`. The four edge
conditions translate to the four sign conditions:

* left  (`s = 0`): `f 0 t = (α 0).re − (β t).re = −(β t).re ≤ 0`
  (since `(β t).re ∈ [0,1]`);
* right (`s = 1`): `f 1 t = (α 1).re − (β t).re = 1 − (β t).re ≥ 0`;
* bottom(`t = 0`): `g s 0 = (α s).im − (β 0).im = (α s).im ≥ 0`
  (since `(α s).im ∈ [0,1]`);
* top   (`t = 1`): `g s 1 = (α s).im − (β 1).im = (α s).im − 1 ≤ 0`.

A common zero `(s,t)` of `f, g` is exactly a point where
`α s − β t = 0`, i.e. `α s = β t`. -/
theorem rectangle_crossing {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc 0 1))
    (hβ : ContinuousOn β (Icc 0 1))
    (hαmem : ∀ s ∈ Icc (0 : ℝ) 1, α s ∈ (Icc (0 : ℝ) 1) ×ℂ (Icc (0 : ℝ) 1))
    (hβmem : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ (Icc (0 : ℝ) 1) ×ℂ (Icc (0 : ℝ) 1))
    (hα0 : (α 0).re = 0) (hα1 : (α 1).re = 1)
    (hβ0 : (β 0).im = 0) (hβ1 : (β 1).im = 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, α s = β t := by
  -- Coordinate functions of G (s,t) = α s − β t.
  set f : ℝ → ℝ → ℝ := fun s t => (α s).re - (β t).re with hf_def
  set g : ℝ → ℝ → ℝ := fun s t => (α s).im - (β t).im with hg_def
  -- Joint continuity of f and g on the square, from continuity of α, β.
  -- The projection p ↦ p.1 (resp p.2) is continuous and maps the square
  -- into Icc 0 1, so α ∘ fst and β ∘ snd are continuous on the square.
  have hα_sq : ContinuousOn (fun p : ℝ × ℝ => α p.1) (Icc 0 1 ×ˢ Icc 0 1) := by
    apply hα.comp continuousOn_fst
    intro p hp; exact hp.1
  have hβ_sq : ContinuousOn (fun p : ℝ × ℝ => β p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
    apply hβ.comp continuousOn_snd
    intro p hp; exact hp.2
  have hf_cont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : ContinuousOn (fun p : ℝ × ℝ => (α p.1).re - (β p.2).re) (Icc 0 1 ×ˢ Icc 0 1) :=
      (Complex.continuous_re.comp_continuousOn hα_sq).sub
        (Complex.continuous_re.comp_continuousOn hβ_sq)
    exact this
  have hg_cont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
    have : ContinuousOn (fun p : ℝ × ℝ => (α p.1).im - (β p.2).im) (Icc 0 1 ×ˢ Icc 0 1) :=
      (Complex.continuous_im.comp_continuousOn hα_sq).sub
        (Complex.continuous_im.comp_continuousOn hβ_sq)
    exact this
  -- Edge sign conditions.
  -- Left edge s = 0:  f 0 t = (α 0).re − (β t).re = −(β t).re ≤ 0.
  have hf_left : ∀ t ∈ Icc (0 : ℝ) 1, f 0 t ≤ 0 := by
    intro t ht
    have hβt := (Complex.mem_reProdIm.mp (hβmem t ht)).1
    simp only [hf_def, hα0]
    linarith [hβt.1]
  -- Right edge s = 1: f 1 t = 1 − (β t).re ≥ 0.
  have hf_right : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f 1 t := by
    intro t ht
    have hβt := (Complex.mem_reProdIm.mp (hβmem t ht)).1
    simp only [hf_def, hα1]
    linarith [hβt.2]
  -- Bottom edge t = 0: g s 0 = (α s).im − 0 = (α s).im ≥ 0.
  have hg_bot : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ g s 0 := by
    intro s hs
    have hαs := (Complex.mem_reProdIm.mp (hαmem s hs)).2
    simp only [hg_def, hβ0]
    linarith [hαs.1]
  -- Top edge t = 1: g s 1 = (α s).im − 1 ≤ 0.
  have hg_top : ∀ s ∈ Icc (0 : ℝ) 1, g s 1 ≤ 0 := by
    intro s hs
    have hαs := (Complex.mem_reProdIm.mp (hαmem s hs)).2
    simp only [hg_def, hβ1]
    linarith [hαs.2]
  -- Apply Poincaré–Miranda.
  obtain ⟨s, hs, t, ht, hfst, hgst⟩ :=
    poincare_miranda_unit_square hf_cont hg_cont hf_left hf_right hg_bot hg_top
  -- A common zero of f, g means α s = β t.
  refine ⟨s, hs, t, ht, ?_⟩
  apply Complex.ext
  · simpa only [hf_def, sub_eq_zero] using hfst
  · simpa only [hg_def, sub_eq_zero] using hgst

end RiemannDynamics
