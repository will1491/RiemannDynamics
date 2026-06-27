/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.ReverseLengthAreaForward

/-!
# Loewner planar reciprocity — architectural target for `imageConjugate_cross_bound`

This file is the **multi-session architectural target** for closing
`imageConjugate_cross_bound` (the atomic conjugate-modulus reciprocity sorry sitting at
`QC/GeometricDifferentiable.lean:5065`). It states the headline planar Loewner reciprocity
inequality the geometric ⇒ analytic direction needs, decomposes the proof into an
**affine atom** and an **image-to-source reduction**, and exposes each as its own named
sorry. Subsequent sessions fill the sorries bottom-up; the original
`imageConjugate_cross_bound` is then closed in one line by calling
`loewner_image_cross_bound_axisRect`.

## Why this workstream exists

The serious Phase-3 investigation summarized in `imageConjugate_cross_bound`'s docstring
(`QC/GeometricDifferentiable.lean:5018-5057`) confirmed that the proved Sobolev co-area
engine (`Analysis/Sobolev/Coarea/Assembly.lean`'s `eilenberg_coarea_grad_le` and
`coarea_set_sharp`) plus the proved planar Sperner / Poincaré–Miranda crossing
(`Analysis/RectangleCrossing.lean`'s `rectangle_crossing`) are **insufficient** to close
the cross-bound directly:

* a Lipschitz scalar `u : ℂ → ℝ` whose level sets are the image foliation does not exist
  from a mere homeomorphism `f`;
* the source-plane co-area route needs a change-of-variables for `f` (Mathlib's
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` needs a known `fderiv`), which the
  geometric ⇒ analytic direction is precisely constructing on top of this lemma;
* the natural foliation `c ↦ f({c} × [s,t])` consists of continuous but not
  necessarily absolutely continuous curves, so σ-admissibility does not apply along
  the foliation leaves.

The classical Beurling ρ-potential route is ruled out by a planar Kakeya / Nikodym
counterexample (see the cross-bound docstring). The genuine closure runs through the
**Loewner condition** for the planar Jordan domain (Heinonen 2001, *Lectures on Analysis
on Metric Spaces*; Heinonen–Koskela 1998; Hesse 1975), which equates extremal length and
capacity for conjugate families. The Mathlib-absent Loewner-space machinery (and the
analogous planar reciprocity / Beurling–Ahlfors length–width inequality in tight form)
is what this file architects.

## Architecture

* `loewner_affine_cross_bound` — slice-admissibility variant of the affine case.
  **⚠ Unprovable as currently stated**: a 2026-06-26 audit found an explicit
  counterexample (`ρ(x,y) = 1 + sin(2πx)sin(2πy)`, `σ` symmetric) on `[0,1]²` for which
  the slice hypotheses hold but the cross bound `1 ≤ ∫∫ ρσ` fails (the integral equals
  `3/4`). See the docstring of `loewner_affine_cross_bound` and the private
  `loewner_slice_counterexample` lemma for details. Retained as a `sorry` only because
  removing the signature would be out of scope this session; **no callers should depend
  on it**.

* `loewner_affine_cross_bound_full` — the **corrected** affine atom, with full
  AC-curve-family admissibility. This is the genuine Loewner content; the homeomorphism
  case reduces to it (not to the broken slice variant). The Mathlib-absent Beurling /
  Loewner machinery is what its remaining `sorry` covers.

* `loewner_image_cross_bound_axisRect` — the **image** case with the exact signature
  consumed by `imageConjugate_cross_bound`. Reduces to
  `loewner_affine_cross_bound_full` via `rectangle_crossing` and a measure-preserving
  topological parametrization of the image quadrilateral.

## Closeability roadmap

The affine atom can be proved by a combination of:

1. **Truncation to bounded densities.** For bounded admissible `ρ_n = min(ρ, n)`,
   the Beurling ρ-potential `u_ρ(z) = inf_γ ∫_γ ρ ds` is Lipschitz with constant
   `≤ n · diam`, so the classical co-area + Cauchy–Schwarz proof goes through
   (`u_ρ` provides the Lipschitz scalar for `eilenberg_coarea_grad_le`).
2. **Admissibility-preserving renormalization.** Replace `ρ_n` by
   `ρ_n / (1 - ε_n)` where `ε_n` measures the admissibility loss of truncation; show
   `ε_n → 0` in L² as `n → ∞`.
3. **L²-passage to limits.** Monotone convergence of `∫⁻ ρ_n σ` to `∫⁻ ρ σ` as
   `n → ∞`, combined with `1 ≤ ∫⁻ ρ_n σ_n` to conclude.

The image case then reduces to the affine atom via:

4. **Source-side reduction.** Define `ρ̃(x, y) := ρ(f ⟨x, y⟩)`. The image-admissibility
   of `ρ` along *AC* image curves implies a weaker source-side admissibility along
   *continuous* source curves whose `f`-images are AC.
5. **Rectifiable-subfamily reduction.** By the existing
   `curveModulus_mono` + Eilenberg–Harrold simple-arc analysis, restricting the image
   family to AC curves whose source preimages are *also* AC has the same modulus. This
   yields a sufficiently rich AC source subfamily to run `loewner_affine_cross_bound`.
6. **Sperner topological crossing.** Use `rectangle_crossing` to guarantee that source
   crossings always meet, transferring the integral inequality from source to image.

This is multi-session research engineering authorized by the user 2026-06-26.

## Status

Both sorries below are **architectural placeholders**, written today as the Phase-1
skeleton of the Loewner workstream. They are honest residuals at the depth of the ACL half
of the geometric ⇒ analytic QC equivalence. The classical mathematics is Beurling 1956 /
Ahlfors 1973 / Heinonen 2001; the Lean infrastructure (planar Loewner condition,
extremal-length capacity equality, AC-subfamily modulus invariance) is Mathlib-absent and
will be developed across several sessions.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RiemannDynamics

/-- **Loewner affine cross-bound — slice-admissibility variant (UNPROVABLE AS STATED).**

For nonneg measurable densities `ρ, σ : ℂ → ℝ≥0∞` on the closed axis rectangle
`R = [a, b] × [s, t]`, satisfying the affine **slice** admissibility conditions

  `∀ᵐ y ∈ [s, t], 1 ≤ ∫⁻ x ∈ [a, b], ρ (⟨x, y⟩ : ℂ)`  (horizontal slices),
  `∀ᵐ x ∈ [a, b], 1 ≤ ∫⁻ y ∈ [s, t], σ (⟨x, y⟩ : ℂ)`  (vertical slices),

the conclusion *claimed* below is

  `1 ≤ ∫⁻ z in R, ρ z * σ z`.

## ⚠ Soundness flaw discovered 2026-06-26

The slice-admissibility hypotheses above are **strictly weaker** than the genuine
admissibility-against-all-AC-curves condition needed for the Beurling–Ahlfors cross
bound. With only slice admissibility, the conclusion `1 ≤ ∫∫ ρσ` is **mathematically
false**, as the following explicit counterexample shows (on the unit square `[0,1]²`):

  `ρ(x, y) := 1 + sin(2πx) · sin(2πy)`        — pointwise in `[0, 2]`,
  `σ(x, y) := 1 − sin(2πx) · sin(2πy)`        — pointwise in `[0, 2]`.

Both are nonneg measurable. Each horizontal slice of `ρ` integrates to exactly `1`
(the `sin(2πx)` factor has zero mean on `[0, 1]`), so the horizontal slice
admissibility is satisfied with equality; symmetrically for `σ`'s vertical slices.
But

  `∫∫ ρ σ = ∫∫ (1 − sin²(2πx) · sin²(2πy)) = 1 − ¼ = ¾ < 1`.

(The formal sketch is recorded as `private theorem loewner_slice_counterexample` below;
its numerical residuals are standard Fourier identities Mathlib has not formalised in
a directly applicable form, but the math is iron-clad.)

The classical Beurling reciprocity requires admissibility against **every** AC curve
connecting the two sides of the rectangle, not merely the axis-aligned slice family.
The correct affine atom is the *full*-admissibility variant
`loewner_affine_cross_bound_full` introduced below. The image consumer
`imageConjugate_cross_bound`
(`QC/GeometricDifferentiable.lean:5058`) uses curve-family admissibility, so it does
in fact reduce to `loewner_affine_cross_bound_full`, not to this (broken) statement.

## Classical references

Ahlfors, *Conformal Invariants* Ch. 4 §4-1 to §4-2 (Beurling reciprocity); Heinonen,
*Lectures on Analysis on Metric Spaces* §3.2 (the planar Loewner condition); Hesse 1975,
*A p-extremal length and p-capacity equality* (extremal-length capacity equality for
conjugate families).

## Multi-session status

Phase-1 architectural sorry. **The signature itself is provably wrong** — see the
counterexample sketch below and the corrected `loewner_affine_cross_bound_full`. The
sorry is retained so as not to break callers that may already reference this name,
but **no callers should depend on this lemma**; downstream uses must instead invoke
`loewner_affine_cross_bound_full`. -/
theorem loewner_affine_cross_bound {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {ρ σ : ℂ → ℝ≥0∞} (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρadm : ∀ᵐ y, y ∈ Set.Icc s t →
      1 ≤ ∫⁻ x in Set.Icc a b, ρ (⟨x, y⟩ : ℂ))
    (hσadm : ∀ᵐ x, x ∈ Set.Icc a b →
      1 ≤ ∫⁻ y in Set.Icc s t, σ (⟨x, y⟩ : ℂ)) :
    1 ≤ ∫⁻ z in axisRect a b s t, ρ z * σ z := by
  -- UNPROVABLE: the slice hypotheses are insufficient. See the docstring counterexample
  -- and `loewner_affine_cross_bound_full` for the corrected statement.
  sorry

/-! ## Architectural infrastructure for the corrected affine atom

The section below builds the bridge between **slice admissibility** (integral over a
horizontal line in the rectangle ≥ 1) and **curve-family admissibility** (arc-length
line integral along every AC connecting curve ≥ 1). Horizontal segments at any height
`y ∈ [s, t]` are AC connecting curves of the rectangle quadrilateral
(`axisRect_segmentFamily_subset`, already in `ReverseLengthAreaForward.lean`), so

  `full admissibility ⟹ slice admissibility`

is a one-line implication.  The reverse implication is **false** (see the soundness
counterexample sketched above), which is precisely the gap distinguishing the two
versions of the affine atom.

These helpers are reusable from the image reduction (`loewner_image_cross_bound_axisRect`)
once it is closed via the corrected atom. -/

/-- The horizontal segment at height `y`: the AC curve `t ↦ ⟨a + (b−a)·t, y⟩` on `[0, 1]`,
parametrizing the line `{im = y, a ≤ re ≤ b}` left-to-right. -/
private noncomputable def horizontalSegment (a b y : ℝ) : ℝ → ℂ :=
  fun x => Complex.mk (a + (b - a) * x) y

/-- The vertical segment at column `x`: the AC curve `t ↦ ⟨x, s + (t−s)·t⟩` on `[0, 1]`,
parametrizing the line `{re = x, s ≤ im ≤ t}` bottom-to-top. -/
private noncomputable def verticalSegment (s t x : ℝ) : ℝ → ℂ :=
  fun y => Complex.mk x (s + (t - s) * y)

/-- Every horizontal segment `horizontalSegment a b y` with `y ∈ [s, t]` is a member of
the rectangle's connecting curve family. Direct corollary of
`axisRect_segmentFamily_subset`. -/
private theorem horizontalSegment_mem_curveFamily {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {y : ℝ} (hy : y ∈ Set.Icc s t) :
    horizontalSegment a b y ∈ (axisRectQuadrilateral a b s t hab hst).curveFamily := by
  refine axisRect_segmentFamily_subset hab hst ?_
  exact ⟨y, hy, rfl⟩

/-- Every vertical segment `verticalSegment s t x` with `x ∈ [a, b]` is a member of the
**swapped** rectangle's connecting curve family — i.e., a bottom-to-top curve of the
axis rectangle. The swap exchanges the roles of horizontal/vertical, so the proof is
the same as `horizontalSegment_mem_curveFamily` with `a ↔ s`, `b ↔ t`. -/
private theorem verticalSegment_mem_curveFamilySwap {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    verticalSegment s t x ∈
      (axisRectQuadrilateralSwap a b s t hab hst).curveFamily := by
  -- The swapped quadrilateral parametrises the rectangle by `(p, q) ↦ ⟨a + (b−a)·q,
  -- s + (t−s)·p⟩`, i.e., the unit-square direction `(1, 0) ↦` "go up". Its left side
  -- is the bottom edge `{im = s}`, right side the top edge `{im = t}`. The vertical
  -- segment at column `x` is the AC curve from bottom edge to top edge; the strategy
  -- is to use the same `axisRect_segmentFamily_subset`-style argument adapted to the
  -- swap. Mathematically straightforward; reserved as a single named residual for the
  -- next session since the swap variant of `axisRect_segmentFamily_subset` is not yet
  -- in `ReverseLengthAreaForward.lean`.
  sorry

/-- **Slice-to-arc-length identity for horizontal segments.**

The arc-length line integral of `ρ` along the horizontal segment at height `y` (with
endpoints `⟨a, y⟩` and `⟨b, y⟩`) equals the 1D Lebesgue slice integral
`∫⁻ x in [a, b], ρ ⟨x, y⟩`. Together with `horizontalSegment_mem_curveFamily` this
turns curve-family admissibility into horizontal slice admissibility for `ρ`. -/
private theorem arcLengthLineIntegral_horizontalSegment {a b : ℝ} (hab : a < b)
    (ρ : ℂ → ℝ≥0∞) (y : ℝ) :
    arcLengthLineIntegral ρ (horizontalSegment a b y)
      = ∫⁻ x in Set.Icc a b, ρ (⟨x, y⟩ : ℂ) := by
  -- The derivative of `horizontalSegment a b y` is the constant `(b − a : ℂ)`, so the
  -- arc-length factor `‖γ'‖` is `(b − a)`. The substitution `t ↦ a + (b − a)·t` maps
  -- `[0, 1]` onto `[a, b]` with Jacobian `(b − a)`, cancelling the arc-length factor.
  --
  -- Reduces to the Mathlib affine-substitution `lintegral_comp_mul_add` lemma.
  -- Single-residual stub: well-localised, no `axisRect` machinery involved.
  sorry

/-- **Slice-to-arc-length identity for vertical segments.** Swap analogue of
`arcLengthLineIntegral_horizontalSegment`. -/
private theorem arcLengthLineIntegral_verticalSegment {s t : ℝ} (hst : s < t)
    (σ : ℂ → ℝ≥0∞) (x : ℝ) :
    arcLengthLineIntegral σ (verticalSegment s t x)
      = ∫⁻ y in Set.Icc s t, σ (⟨x, y⟩ : ℂ) := by
  -- Symmetric to `arcLengthLineIntegral_horizontalSegment`: derivative is `(t−s : ℂ) · I`
  -- with norm `(t − s)`; affine substitution `y ↦ s + (t−s)·y` cancels the arc-length
  -- factor against the 1D Lebesgue integral on `[s, t]`.
  sorry

/-- **Full admissibility implies horizontal slice admissibility.** If `ρ` is admissible
against the rectangle's whole AC connecting family, then for every `y ∈ [s, t]` the
1D slice integral `∫⁻ x in [a, b], ρ ⟨x, y⟩` is at least `1`. (No "a.e. `y`" needed —
holds for every `y` in the closed interval.) -/
private theorem slice_admissibility_of_full_admissibility {a b s t : ℝ}
    (hab : a < b) (hst : s < t) {ρ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ (axisRectQuadrilateral a b s t hab hst).curveFamily) :
    ∀ y ∈ Set.Icc s t, 1 ≤ ∫⁻ x in Set.Icc a b, ρ (⟨x, y⟩ : ℂ) := by
  intro y hy
  have hseg := horizontalSegment_mem_curveFamily hab hst hy
  have hadm := hρ.2 _ hseg
  rwa [arcLengthLineIntegral_horizontalSegment hab ρ y] at hadm

/-- **Full admissibility implies vertical slice admissibility** (swap analogue). -/
private theorem slice_admissibility_swap_of_full_admissibility {a b s t : ℝ}
    (hab : a < b) (hst : s < t) {σ : ℂ → ℝ≥0∞}
    (hσ : IsAdmissibleDensity σ
      (axisRectQuadrilateralSwap a b s t hab hst).curveFamily) :
    ∀ x ∈ Set.Icc a b, 1 ≤ ∫⁻ y in Set.Icc s t, σ (⟨x, y⟩ : ℂ) := by
  intro x hx
  have hseg := verticalSegment_mem_curveFamilySwap hab hst hx
  have hadm := hσ.2 _ hseg
  rwa [arcLengthLineIntegral_verticalSegment hst σ x] at hadm

/-- **Loewner affine cross-bound — full-admissibility variant (the genuine atom).**

For nonneg measurable densities `ρ, σ : ℂ → ℝ≥0∞` admissible against the rectangle's
left↔right (`ρ`) and bottom↔top (`σ`) **AC connecting curve families**, the
cross-product integrates to at least `1` over the closed axis rectangle:

  `1 ≤ ∫⁻ z in [a, b] × [s, t], ρ z · σ z`.

This is the **correct** affine atom of the Beurling–Ahlfors reciprocity. Unlike the
slice-only version (`loewner_affine_cross_bound` above), it uses full admissibility
against every AC connecting curve in the rectangle — the hypothesis that the genuine
Beurling proof requires, and that the consuming `imageConjugate_cross_bound` actually
provides (via curve-family admissibility, in the image setting).

## Closeability roadmap (next sessions)

The classical Beurling proof has three steps:

1. **Truncate to bounded densities.** For each `n`, let `ρₙ := min(ρ, n)` and
   `σₙ := min(σ, n)`. These are bounded admissible (admissibility is *not* preserved
   by truncation in general — needs an admissibility-preserving renormalisation by a
   factor `1/(1 − εₙ)` with `εₙ → 0`).
2. **Bounded case via Beurling ρ-potential.** For bounded `ρₙ`, define
   `uₙ(z) := inf over AC paths γ from left edge to z, of ∫_γ ρₙ ds`. Then `uₙ` is
   Lipschitz (constant `≤ n · diam(R)`) and satisfies the eikonal `‖∇uₙ‖ ≤ ρₙ` a.e.
   Level sets `uₙ⁻¹{c}` for `c ∈ (0, 1)` are AC curves separating left from right;
   by σ-admissibility they have σ-mass `≥ 1`. The proved Sobolev co-area
   `Analysis.Sobolev.Coarea.Assembly.eilenberg_coarea_grad_le` then gives
   `1 ≤ ∫_0^1 (∫_{uₙ=c} σ dμH¹) dc ≤ ∫ ρₙ · σ`.
3. **Pass to the limit.** Monotone convergence of `∫ ρₙ · σ → ∫ ρ · σ` as `n → ∞`,
   combined with `1 ≤ ∫ ρₙ · σₙ` and the renormalisation factor `→ 1`.

The bounded case is doable with the existing Sobolev co-area + Lipschitz potential
infrastructure; the truncation/renormalisation step is technically delicate (preserves
admissibility only by a renormalisation factor whose limit is `1`).

## Multi-session status

Phase-1 architectural sorry. The slice-implication helpers
(`slice_admissibility_of_full_admissibility`, …`_swap`) are proved modulo the
single-step `arcLengthLineIntegral_*Segment` substitution residuals (clean Mathlib
applications of `lintegral_comp_mul_add`) and `verticalSegment_mem_curveFamilySwap`
(the bottom-to-top analogue of `axisRect_segmentFamily_subset`). -/
theorem loewner_affine_cross_bound_full {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ (axisRectQuadrilateral a b s t hab hst).curveFamily)
    (hσ : IsAdmissibleDensity σ
      (axisRectQuadrilateralSwap a b s t hab hst).curveFamily) :
    1 ≤ ∫⁻ z in axisRect a b s t, ρ z * σ z := by
  -- Genuine Beurling–Ahlfors content. See the docstring closeability roadmap for the
  -- three-step plan (truncation → bounded Beurling potential → limit).
  sorry

/-- **Soundness sketch for the slice-only affine atom: explicit counterexample.**

This *private* lemma records the explicit counterexample
`ρ(x, y) := 1 + sin(2πx)·sin(2πy)`, `σ(x, y) := 1 − sin(2πx)·sin(2πy)` on the unit
square `[0, 1]²` proving that the slice-admissibility hypotheses of
`loewner_affine_cross_bound` are **insufficient** for the cross-bound conclusion.

The cross integral evaluates to

  `∫_[0,1]² ρ · σ = ∫_[0,1]² (1 − sin²(2πx)·sin²(2πy)) = 1 − ¼ = ¾`,

while each horizontal slice of `ρ` and each vertical slice of `σ` integrates to
exactly `1`. So the hypotheses are met but the conclusion `1 ≤ ¾` is false.

The proof is reserved as a `sorry`-d *private* lemma: formalising the numerical
identities `∫_0^1 sin(2πx) dx = 0` and `∫_0^1 sin²(2πx) dx = 1/2` in Lean requires
specific Mathlib lemmas about Lebesgue integrals of trig functions that are not
immediately in the right shape, but the mathematics is iron-clad. The point of the
statement is purely *documentary*: it pins down the soundness gap as an in-file
Lean obligation that downstream maintainers can recognise. -/
private theorem loewner_slice_counterexample :
    ∃ (ρ σ : ℂ → ℝ≥0∞), Measurable ρ ∧ Measurable σ ∧
      (∀ᵐ y, y ∈ Set.Icc (0 : ℝ) 1 →
        1 ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, ρ (⟨x, y⟩ : ℂ)) ∧
      (∀ᵐ x, x ∈ Set.Icc (0 : ℝ) 1 →
        1 ≤ ∫⁻ y in Set.Icc (0 : ℝ) 1, σ (⟨x, y⟩ : ℂ)) ∧
      ¬ (1 ≤ ∫⁻ z in axisRect 0 1 0 1, ρ z * σ z) := by
  -- Witnesses: `ρ(x, y) := ENNReal.ofReal (1 + sin(2πx) · sin(2πy))`, `σ(x, y) :=
  -- ENNReal.ofReal (1 − sin(2πx) · sin(2πy))`. See docstring for the arithmetic.
  --
  -- The Fourier identities `∫_0^1 sin(2πx) dx = 0` and `∫_0^1 sin²(2πx) dx = 1/2`
  -- close both the slice-admissibility hypotheses (each slice integrates to exactly
  -- `1`) and the cross-integral evaluation (`∫∫ ρσ = 1 − 1/4 = 3/4`). Mathlib has
  -- the Bochner-integral form of these identities (`MeasureTheory.integral_sin`,
  -- `MeasureTheory.integral_sin_sq_Ioc_pi`, etc.); transferring them to the
  -- `ℝ≥0∞`-valued setting via `ENNReal.ofReal` is mechanical but lengthy.
  --
  -- Architectural placeholder reserved for a Phase-2 audit pass. Its purpose is to
  -- document — as a Lean obligation, not just a docstring comment — that the slice
  -- version of `loewner_affine_cross_bound` is unsound.
  sorry

/-- **Loewner image cross-bound — the architectural target for
`imageConjugate_cross_bound`.**

For a geometric `K`-quasiconformal homeomorphism `f : ℂ → ℂ` and admissible densities
`ρ, σ : ℂ → ℝ≥0∞` for the image crossing family and the image separating (swap) family
of an axis rectangle, the cross-product integrates to at least `1`:

  `1 ≤ ∫⁻ z, ρ z * σ z`.

This has the **identical signature** to `imageConjugate_cross_bound`
(`QC/GeometricDifferentiable.lean:5058`); once both sorries below are closed, the original
sorry is discharged by a one-line call into this lemma.

## Closeability roadmap

Reduces to `loewner_affine_cross_bound_full` (**not** the slice-only
`loewner_affine_cross_bound`, which has a soundness flaw — see its docstring) via:
* the topological intersection guarantee `RiemannDynamics.rectangle_crossing`
  (`Analysis/RectangleCrossing.lean:950`) — every image crossing curve meets every image
  separating curve;
* a topological / measure-preserving parametrization of `f`'s image quadrilateral by
  the source axis rectangle (giving the source-side admissibility transfer);
* the `IsQCGeometric f K` modulus bound to control the AC-vs-continuous discrepancy on
  the slice family (the genuine source ↔ image transfer step).

## Multi-session status

Phase-1 architectural sorry. -/
theorem loewner_image_cross_bound_axisRect {f : ℂ → ℂ} (hf : IsHomeomorph f)
    {K : ℝ} (hfqc : IsQCGeometric f K)
    {a b s t : ℝ} (hab : a < b) (hst : s < t)
    {ρ σ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleDensity ρ ((axisRectQuadrilateral a b s t hab hst).imageCurveFamily f))
    (hσ : IsAdmissibleDensity σ
      ((axisRectQuadrilateralSwap a b s t hab hst).imageCurveFamily f)) :
    1 ≤ ∫⁻ z, ρ z * σ z := by
  sorry

end RiemannDynamics
