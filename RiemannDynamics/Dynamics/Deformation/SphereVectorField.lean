/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.MRMT.NeumannSeries

/-!
# Continuous vector fields on the sphere and the canonical `∂̄`-solver

A *sphere vector field* is a continuous vector field on the Riemann sphere,
recorded concretely through its finite-chart reading: a continuous
`v : ℂ → ℂ` such that the infinity-chart reading `w ↦ w²·v(1/w)` extends
continuously at `w = 0` (`IsSphereVectorField`). No bundle language is used;
the two charts of `Sphere/Basic.lean` are the only geometry.

The main construction is the **canonical linear solver** `dbarSolver μ` of the
equation `∂̄v = μ` for a measurable, essentially bounded coefficient
`μ : ℂ → ℂ`. The coefficient is split into the piece carried by the closed
unit disk and the piece outside it:

* the near piece `ballTruncation μ` is handled directly by the Cauchy
  transform;
* the far piece is transported to the infinity chart `w = 1/z`. A Beltrami
  coefficient `μ dz̄/dz` pulls back under the holomorphic change of variables
  `z = φ(w) = 1/w` with the unimodular factor `conj(φ'(w))/φ'(w)`; since
  `φ'(w) = −w⁻²`, this factor is `(−w̄⁻²)/(−w⁻²) = w²/w̄²`, giving the
  transported coefficient `ν(w) = (w²/w̄²)·μ(1/w)` (`inftyChartCoeff μ`),
  supported in the punctured open unit disk (`|w| < 1 ∧ w ≠ 0` corresponds
  exactly to `|1/w| > 1`, the far piece's carrier). Note `|ν(w)| = |μ(1/w)|`.
  The Cauchy transform solves `∂̄u = ν` in the `w`-chart, and the solution is
  transported back as a *vector field*: a field with finite-chart reading
  `v(z)` has infinity-chart reading `ṽ(w) = (dw/dz)·v(1/w) = −w²·v(1/w)`, so
  a chart reading `u(w)` at infinity corresponds to `z ↦ −z²·u(1/z)` in the
  finite chart. The consistency check
  `∂̄_z(−z²·u(1/z)) = (z²/z̄²)·(∂̄u)(1/z)` (anti-holomorphic chain rule)
  shows this piece has weak `∂̄` equal to `μ` off the closed unit disk and
  `0` inside the open unit disk.

The definition `dbarSolver` is total and pointwise; its properties —
linearity in `μ`, the sphere-field property, and the weak derivative identity
`∂̄(dbarSolver μ) = μ` a.e. — are theorems, resting on the Cauchy-transform
calculus (`continuous_cauchyTransform_of_memLp_of_support`,
`cauchyTransform_tendsto_cocompact`, `hasWeakGradient_cauchyTransform`) plus
the chart-transport lemma `exists_weakGradient_inversion_transport` proved
here. This layer is purely infinitesimal: there is no `‖μ‖∞ < 1` hypothesis
anywhere, only measurability and essential boundedness.
-/

open MeasureTheory Complex Metric Filter Topology

namespace RiemannDynamics

/-- `v` has a **weak `∂̄`-derivative `μ` with locally square-integrable
gradient** on `Ω`: there are weak partial derivatives `gx` (direction `1`) and
`gy` (direction `I`) of `v` on `Ω`, both `L²_loc` on `Ω`, whose Wirtinger
combination satisfies `gx + i·gy = 2μ` almost everywhere on `Ω` (the
dictionary `∂̄ = ½(∂ₓ + i∂ᵧ)`). The `L²` class is the natural one here: the
Dirichlet integral is conformally invariant, so this predicate transports
cleanly under holomorphic composition and under the inversion chart. It also
implies local integrability of the witnesses, which is what Weyl's lemma
consumes. -/
def HasL2WeakDzbar (v μ : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∃ gx gy : ℂ → ℂ, HasWeakGradient gx gy v Ω ∧
    MemLpLocOn gx 2 Ω ∧ MemLpLocOn gy 2 Ω ∧
    (∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω →
      gx z + Complex.I * gy z = 2 * μ z)

/-- A **sphere vector field** in finite-chart reading: `v : ℂ → ℂ` is
continuous, and the infinity-chart reading `w ↦ w²·v(1/w)` extends
continuously at `w = 0` — i.e. it has a limit `L` along the punctured
neighborhoods of `0`. This is the concrete, two-chart formulation of a
continuous vector field on the Riemann sphere. (The geometric infinity-chart
reading is `−w²·v(1/w)`; the sign does not affect the extension property and
is omitted.) -/
def IsSphereVectorField (v : ℂ → ℂ) : Prop :=
  Continuous v ∧ ∃ L : ℂ,
    Tendsto (fun w : ℂ => w ^ 2 * v w⁻¹) (nhdsWithin 0 {0}ᶜ) (nhds L)

/-- The truncation of a coefficient to the closed unit disk — the *near piece*
of the canonical splitting. -/
noncomputable def ballTruncation (μ : ℂ → ℂ) : ℂ → ℂ := fun z =>
  open Classical in
  if z ∈ Metric.closedBall (0 : ℂ) 1 then μ z else 0

/-- The infinity-chart transport of the *far piece* of a coefficient: the
Beltrami transformation law under `z = 1/w` applied to `μ·1_{|z|>1}`, giving
`ν(w) = (w²/w̄²)·μ(1/w)` carried by the punctured open unit disk. The factor
`w²/w̄²` is unimodular, so `|ν(w)| = |μ(1/w)|` and essential bounds are
preserved. -/
noncomputable def inftyChartCoeff (μ : ℂ → ℂ) : ℂ → ℂ := fun w =>
  open Classical in
  if w ∈ Metric.ball (0 : ℂ) 1 ∧ w ≠ 0
    then w ^ 2 / (starRingEnd ℂ w) ^ 2 * μ w⁻¹ else 0

/-- The **canonical `∂̄`-solver**: a totally defined, pointwise formula
producing a continuous sphere vector field with weak `∂̄` equal to `μ`. The
near piece is the Cauchy transform of the disk truncation; the far piece is
solved in the infinity chart and transported back as a vector field (the
finite-chart reading of a field whose infinity-chart reading is `u` is
`z ↦ −z²·u(1/z)`; at `z = 0` the junk value `0⁻¹ = 0` is harmless since the
prefactor `−z²` vanishes). -/
noncomputable def dbarSolver (μ : ℂ → ℂ) : ℂ → ℂ := fun z =>
  cauchyTransform (ballTruncation μ) z
    - z ^ 2 * cauchyTransform (inftyChartCoeff μ) z⁻¹

/-- **Additivity of the solver.** The truncation and transport operations are
pointwise linear; the Cauchy transform is additive on integrable integrands,
which the measurability and essential boundedness of the two coefficients
provide. -/
theorem dbarSolver_add {μ σ : ℂ → ℂ}
    (hμ : AEMeasurable μ volume) (hσ : AEMeasurable σ volume)
    (hμb : eLpNormEssSup μ volume < ⊤) (hσb : eLpNormEssSup σ volume < ⊤) :
    dbarSolver (fun z => μ z + σ z)
      = fun z => dbarSolver μ z + dbarSolver σ z := by
  sorry

/-- **Homogeneity of the solver.** Scalar multiples pass through the
truncation, the transport, and the (Bochner) integral unconditionally. -/
theorem dbarSolver_smul (c : ℂ) (μ : ℂ → ℂ) :
    dbarSolver (fun z => c * μ z) = fun z => c * dbarSolver μ z := by
  sorry

/-- The canonical solution of `∂̄v = μ` for a measurable, essentially bounded
coefficient is a sphere vector field: it is continuous on `ℂ` (Hölder
continuity of the Cauchy transform of a bounded compactly supported density,
in each chart), and its infinity-chart reading extends continuously at `0`
(the near piece decays at infinity; the far piece's reading near `0` *is* the
Cauchy transform in the `w`-chart, continuous there). -/
theorem isSphereVectorField_dbarSolver {μ : ℂ → ℂ}
    (hμ : AEMeasurable μ volume) (hb : eLpNormEssSup μ volume < ⊤) :
    IsSphereVectorField (dbarSolver μ) := by
  sorry

/-- **Chart transport of weak `∂̄`-data under the inversion `z ↦ 1/z`.**
Let `Ω ⊆ ℂ ∖ {0}` be open and let `u` be continuous with weak `∂̄`-derivative
`ν` (and `L²_loc` gradient) on the inverted set `(·⁻¹) '' Ω`. Then the
transported vector field `z ↦ −z²·u(1/z)` has weak `∂̄`-derivative
`(z²/z̄²)·ν(1/z)` on `Ω` — the Beltrami transformation law at the level of
weak derivatives:

`∂̄(−z²·u(1/z)) = (z²/z̄²)·(∂̄u)(1/z)` a.e. on `Ω`.

The `L²_loc` class is preserved because the Dirichlet integral is conformally
invariant under the (holomorphic) inversion. This is the analytic core of the
far-piece bookkeeping in `dbarSolver`, stated as a reusable node: mollify `u`
in the inverted chart, transport the classical chain rule, and pass to the
limit against test functions supported in `Ω`. -/
theorem hasL2WeakDzbar_inversion_transport {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩ0 : Ω ⊆ {(0 : ℂ)}ᶜ) {u ν : ℂ → ℂ}
    (hu : ContinuousOn u ((fun z : ℂ => z⁻¹) '' Ω))
    (hgrad : HasL2WeakDzbar u ν ((fun z : ℂ => z⁻¹) '' Ω)) :
    HasL2WeakDzbar (fun z => -z ^ 2 * u z⁻¹)
      (fun z => z ^ 2 / (starRingEnd ℂ z) ^ 2 * ν z⁻¹) Ω := by
  sorry

/-- **The solver solves.** `dbarSolver μ` has weak `∂̄`-derivative `μ` on all
of `ℂ`, with locally square-integrable weak gradient. The near piece is
`hasWeakGradient_cauchyTransform` (whose witnesses are Beurling transforms,
hence `L²_loc`); the far piece combines the same identity in the infinity
chart with `hasL2WeakDzbar_inversion_transport` and the cancellation of the
two unimodular factors; the two pieces are glued by additivity of weak
derivatives. -/
theorem hasL2WeakDzbar_dbarSolver {μ : ℂ → ℂ}
    (hμ : AEMeasurable μ volume) (hb : eLpNormEssSup μ volume < ⊤) :
    HasL2WeakDzbar (dbarSolver μ) μ Set.univ := by
  sorry

end RiemannDynamics
