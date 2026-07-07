/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.Deformation.SphereVectorField
import RiemannDynamics.QC.Calculus.WeylLocal
import RiemannDynamics.Sphere.OpenMapping
import RiemannDynamics.Sphere.Iterate
import RiemannDynamics.Dynamics.JuliaFatou.RepellingDensity

/-!
# The delta operator of a rational map and its finite-dimensional target

For a rational map `f` given by `r : RationalData`, a continuous vector field
`v` on the sphere determines the *deformation field*

`δv = f′·v − v ∘ f`

read in the finite chart (`deltaField`). Classically `δv = Df(v) − v ∘ f` is
a section of the pullback bundle `f*(T ℂ̂)`; here everything is chart-concrete:
`f′` is the finite-chart derivative `wronskian/denReduced²` (`fderivRational`)
and the composition point is the finite reading of `f(z)` (junk at the poles
of `f`, a finite — hence null — set).

The two main results stated here are the heart of Sullivan's finiteness
argument:

* **Invariance kills `∂̄`**: if `μ = ∂̄v` is `f`-invariant
  (`IsInvariantBeltrami`, the pullback law `f*μ = μ` in multiplied-out form),
  then `∂̄(δv) = f′·μ − (μ∘f)·conj(f′) = 0` weakly off the poles, so `δv` is
  holomorphic off the poles (open-set Weyl); chart analysis at each pole and
  at infinity then places `δv` in the concrete `(2d+1)`-dimensional space
  `SectionSpaceCarrier r = {A/denReduced² : A ∈ ℂ[X], natDegree A ≤ 2d}`
  (`exists_sectionSpace_rep_deltaField`, with `finrank_sectionSpaceCarrier`).
  Because Lean's junk value of `A/Q²` at a root of `Q` is `0` while
  `deltaField`'s junk value there is `−v(0)`, membership is stated as the
  existence of a carrier element agreeing with `δv` off the poles; such a
  representative is unique (`sectionSpaceCarrier_eqOn_nonpoles_eq`).

* **Trivial deformations vanish on the Julia set**: if `δv = 0` off the
  poles then `v(f z) = f′(z)·v(z)` there; iterating
  (`deltaField_zero_iterate`) and evaluating at a repelling periodic point
  `p` gives `v(p) = m·v(p)` with `|m| > 1`, so `v(p) = 0`; density of
  repelling cycles (`juliaSet_eq_closure_repelling`) and continuity give
  `v = 0` at every finite point of the Julia set
  (`sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero`). The finite-point
  statement is all downstream consumers need: the frontier of a Fatou
  component is consumed through its finite part, and behavior at `∞` is
  handled by the sphere-field decay built into the seed-triviality argument.
-/

open MeasureTheory Complex Metric Filter Topology Polynomial OnePoint

namespace RiemannDynamics

/-! ## The finite-chart derivative and the invariance law -/

/-- The finite-chart derivative of the rational map given by `r`: the
Wronskian of the reduced representation divided by the squared reduced
denominator. Away from the poles this equals the derivative of the
finite-chart reading (`RationalData.deriv_reading`); at a pole the value is
junk (`x/0 = 0` in Lean) and every downstream statement restricts to
non-poles or works almost everywhere. -/
noncomputable def fderivRational (r : RationalData) : ℂ → ℂ := fun z =>
  r.wronskian.eval z / (r.denReduced.eval z) ^ 2

/-- Away from poles, `fderivRational` is the derivative of the finite-chart
reading of the map. -/
theorem fderivRational_eq_deriv_reading (r : RationalData) {w : ℂ}
    (hden : r.denReduced.eval w ≠ 0) :
    fderivRational r w
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂)))) w := by
  sorry

/-- A coefficient `μ : ℂ → ℂ` is an **invariant Beltrami coefficient** for
the rational map given by `r` when the pullback law `f*μ = μ` holds almost
everywhere in the finite chart. The pullback convention is

`(f*μ)(z) = μ(f z) · conj(f′(z)) / f′(z)`,

and the law is stated in multiplied-out form to avoid division:

`μ(z) · f′(z) = μ(f z) · conj(f′(z))` for a.e. `z`,

with `f′ = fderivRational r` and `f z` read through `chartFiniteMap` (the
junk value `0` at the finitely many poles is harmless almost everywhere).
`Spreading.lean` *proves* this law for coefficients spread from a seed on a
wandering component; this file *consumes* it to kill the weak `∂̄` of the
deformation field. -/
def IsInvariantBeltrami (r : RationalData) (μ : ℂ → ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ),
    μ z * fderivRational r z
      = μ (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))
          * starRingEnd ℂ (fderivRational r z)

/-! ## The delta operator -/

/-- The **deformation field** `δv = f′·v − v∘f` of a vector field `v` along
the rational map given by `r`, read in the finite chart. Total: at a pole of
`f` the value is junk (`fderivRational` is junk there and the composition
point is the junk reading `0` of `∞`), and every statement about `deltaField`
restricts to non-poles. -/
noncomputable def deltaField (r : RationalData) (v : ℂ → ℂ) : ℂ → ℂ := fun z =>
  fderivRational r z * v z
    - v (chartFiniteMap (r.toSphereMap ((z : ℂ̂))))

/-! ## The finite-dimensional section space -/

/-- The linear map sending a polynomial `A` to the function
`z ↦ A(z)/denReduced(z)²` — the concrete realization of "polynomial sections
over the squared denominator". -/
noncomputable def polyOverDenSq (r : RationalData) : ℂ[X] →ₗ[ℂ] (ℂ → ℂ) where
  toFun A := fun z => A.eval z / (r.denReduced.eval z) ^ 2
  map_add' A B := by
    funext z
    simp [Polynomial.eval_add, add_div]
  map_smul' c A := by
    funext z
    simp [Polynomial.eval_smul, smul_eq_mul, mul_div_assoc]

/-- The **section space** of the rational map given by `r`: the space of
functions `z ↦ A(z)/denReduced(z)²` with `A` a polynomial of degree at most
`2·degree r` — concretely, the image of `Polynomial.degreeLT ℂ (2d+1)` under
`polyOverDenSq`. This is the chart-concrete model of the space of holomorphic
sections of the pullback bundle `f*(T ℂ̂)`, of dimension `2d+1`. -/
noncomputable def SectionSpaceCarrier (r : RationalData) : Submodule ℂ (ℂ → ℂ) :=
  (Polynomial.degreeLT ℂ (2 * r.degree + 1)).map (polyOverDenSq r)

/-- Unfolding characterization of the section space: membership means being
the function `A/denReduced²` for some polynomial `A` with
`natDegree A ≤ 2·degree r`. -/
theorem mem_sectionSpaceCarrier_iff {r : RationalData} {s : ℂ → ℂ} :
    s ∈ SectionSpaceCarrier r
      ↔ ∃ A : ℂ[X], A.natDegree ≤ 2 * r.degree ∧
          s = fun z => A.eval z / (r.denReduced.eval z) ^ 2 := by
  sorry

/-- Two elements of the section space that agree off the (finitely many)
poles are equal: `A/Q²` determines `A` by polynomial function-agreement off a
finite set, and the junk values at the poles are `0` for both. This provides
the uniqueness of the carrier representative of a deformation field, which
makes the endgame's linear map into the carrier well defined. -/
theorem sectionSpaceCarrier_eqOn_nonpoles_eq {r : RationalData} {s₁ s₂ : ℂ → ℂ}
    (h₁ : s₁ ∈ SectionSpaceCarrier r) (h₂ : s₂ ∈ SectionSpaceCarrier r)
    (h : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → s₁ z = s₂ z) :
    s₁ = s₂ := by
  sorry

/-- The section space has dimension `2d+1`: the parametrization
`A ↦ A/denReduced²` is injective on `degreeLT ℂ (2d+1)` (a polynomial is
determined by its values off the finite root set of `denReduced`), and
`degreeLT ℂ (2d+1)` has dimension `2d+1`. -/
theorem finrank_sectionSpaceCarrier (r : RationalData) :
    Module.finrank ℂ (SectionSpaceCarrier r) = 2 * r.degree + 1 := by
  sorry

/-! ## Weak Wirtinger calculus: product and chain rules

The two generic transport rules feeding the holomorphy of the deformation
field. Both stay in the conformally invariant class `HasL2WeakDzbar`. -/

/-- **Product rule with a holomorphic factor.** If `F` is holomorphic on the
open set `Ω` and `v` has weak `∂̄`-derivative `μ` (with `L²_loc` gradient) on
`Ω`, then `F·v` has weak `∂̄`-derivative `F·μ` on `Ω` — `∂̄(Fv) = F·∂̄v` since
`∂̄F = 0`. Local integrability of `v` on `Ω` feeds the Leibniz rule for weak
derivatives. -/
theorem hasL2WeakDzbar_holomorphic_mul {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {F v μ : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω)
    (hvloc : LocallyIntegrableOn v Ω)
    (hgrad : HasL2WeakDzbar v μ Ω) :
    HasL2WeakDzbar (fun z => F z * v z) (fun z => F z * μ z) Ω := by
  sorry

/-- **Chain rule under a holomorphic map.** If `φ` is holomorphic on the open
set `Ω` and `v` is continuous with weak `∂̄`-derivative `μ` (and `L²_loc`
gradient) on all of `ℂ`, then `v ∘ φ` has weak `∂̄`-derivative
`(μ∘φ)·conj(φ′)` on `Ω`:

`∂̄(v∘φ) = (∂̄v)(φ)·conj(φ′)` a.e. on `Ω`

(the `(∂v)(φ)·∂̄φ` term vanishes since `φ` is holomorphic). The `L²_loc`
class survives composition by the conformal invariance of the Dirichlet
integral together with local boundedness of the covering multiplicity of a
holomorphic map; critical points of `φ` are isolated and are absorbed by the
a.e. formulation. -/
theorem hasL2WeakDzbar_comp_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {φ v μ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ Ω)
    (hv : Continuous v)
    (hgrad : HasL2WeakDzbar v μ Set.univ) :
    HasL2WeakDzbar (fun z => v (φ z))
      (fun z => μ (φ z) * starRingEnd ℂ (deriv φ z)) Ω := by
  sorry

/-! ## Invariance places the deformation field in the section space -/

/-- **Holomorphy of the deformation field off the poles.** If `v` is a sphere
vector field with weak `∂̄`-derivative `μ` and `μ` is `f`-invariant, then
`δv` is holomorphic on the complement of the pole set: its weak `∂̄` is
`f′·μ − (μ∘f)·conj(f′)`, which vanishes a.e. by the invariance law, and the
open-set Weyl lemma upgrades this to holomorphy. -/
theorem differentiableOn_deltaField {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ) :
    DifferentiableOn ℂ (deltaField r v)
      {z : ℂ | r.denReduced.eval z ≠ 0} := by
  sorry

/-- **Pole-order bound.** At a root `p` of the reduced denominator of
multiplicity `k`, the deformation field has a pole of order at most `2k`:
there is a holomorphic `h` near `p` with `δv = h(z)/(z−p)^{2k}` off `p`.
Route: the transformed reading `−δv/f² = −(f′/f²)·v + u(1/f)` — where `u` is
the continuous infinity-chart reading `w ↦ w²·v(1/w)` of `v` and `f′/f²`,
`1/f` are holomorphic near `p` (coprimality of the reduced fraction) — is
continuous near `p` and weakly holomorphic (invariance transported through
the chain rule, essential boundedness of `μ` controlling the transported
gradient), hence holomorphic by the open-set Weyl lemma; then
`δv = −(that reading)·f²` and `f²` has a pole of order exactly `2k` at `p`. -/
theorem deltaField_pole_bound {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤)
    {p : ℂ} (hp : r.denReduced.eval p = 0) :
    ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ p ∈ W ∧
      DifferentiableOn ℂ h W ∧
      ∀ z ∈ W, z ≠ p →
        deltaField r v z
          = h z / (z - p) ^ (2 * Polynomial.rootMultiplicity p r.denReduced) := by
  sorry

/-- **Growth bound at infinity.** Multiplied by the squared reduced
denominator, the deformation field grows at most like `|z|^{2d}` near
infinity — the two-chart bookkeeping: `v(z) = O(|z|²)` (sphere field), the
numerator and denominator have degree at most `d`, and the composed term
`v(f z)` is controlled by the infinity-chart reading of `v` when `f z` is
large. This is exactly the numerator-degree bound `natDegree A ≤ 2d` of the
section-space representation. -/
theorem deltaField_growth_at_infty {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤) :
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      ‖(r.denReduced.eval z) ^ 2 * deltaField r v z‖
        ≤ C * ‖z‖ ^ (2 * r.degree) := by
  sorry

/-- **Representation from pole and growth data** (pure function theory /
polynomial algebra). A function holomorphic off the roots of the reduced
denominator, with pole order at most twice the root multiplicity at each
root and with `Q²`-weighted growth `O(|z|^{2d})` at infinity, agrees off the
poles with an element of the section space: `Q²·g` extends to an entire
function of polynomial growth `O(|z|^{2d})`, hence is a polynomial of degree
at most `2d` by Liouville/Cauchy estimates. -/
theorem exists_sectionSpace_rep_of_pole_growth {r : RationalData} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g {z : ℂ | r.denReduced.eval z ≠ 0})
    (hpole : ∀ p : ℂ, r.denReduced.eval p = 0 →
      ∃ (W : Set ℂ) (h : ℂ → ℂ), IsOpen W ∧ p ∈ W ∧
        DifferentiableOn ℂ h W ∧
        ∀ z ∈ W, z ≠ p →
          g z = h z / (z - p) ^ (2 * Polynomial.rootMultiplicity p r.denReduced))
    (hgrow : ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ →
      ‖(r.denReduced.eval z) ^ 2 * g z‖ ≤ C * ‖z‖ ^ (2 * r.degree)) :
    ∃ s ∈ SectionSpaceCarrier r,
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 → g z = s z := by
  sorry

/-- **The deformation field of an invariant coefficient lies in the section
space** — the assembly of holomorphy off poles, the pole-order bound, the
growth bound at infinity, and the representation lemma. The carrier
representative agrees with `δv` off the poles and is unique by
`sectionSpaceCarrier_eqOn_nonpoles_eq`. -/
theorem exists_sectionSpace_rep_deltaField {r : RationalData} (hd : 1 ≤ r.degree)
    {v μ : ℂ → ℂ} (hv : IsSphereVectorField v)
    (hgrad : HasL2WeakDzbar v μ Set.univ)
    (hinv : IsInvariantBeltrami r μ)
    (hb : eLpNormEssSup μ volume < ⊤) :
    ∃ s ∈ SectionSpaceCarrier r,
      ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = s z := by
  sorry

/-! ## Trivial deformations vanish on the Julia set -/

/-- **Iterated functional equation from a trivial deformation.** If
`δv = 0` off the poles — i.e. `v(f z) = f′(z)·v(z)` at every non-pole `z` —
then along any finite orbit segment that stays off `∞`,

`v(fⁿ z) = (fⁿ)′(z)·v(z)`,

with `(fⁿ)′` the derivative of the finite-chart reading of the iterate (the
chain rule telescopes the one-step law along the orbit). -/
theorem deltaField_zero_iterate {r : RationalData} {v : ℂ → ℂ}
    (hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = 0)
    (n : ℕ) (z : ℂ)
    (hfin : ∀ j : ℕ, j ≤ n → r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞) :
    v (chartFiniteMap (r.toSphereMap^[n] ((z : ℂ̂))))
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap^[n] ((x : ℂ̂)))) z
          * v z := by
  sorry

/-- **A trivial deformation vanishes on the Julia set** (at its finite
points). At a repelling periodic point `p` of period `n` whose cycle avoids
`∞`, the iterated functional equation gives `v(p) = m·v(p)` with
`m = multiplier (f^[n]) p`, `|m| > 1`, forcing `v(p) = 0`; repelling cycles
through `∞` are handled by discarding the at most one exceptional cycle
(density is preserved under removing finitely many points from a subset
dense in the perfect Julia set). Density of repelling cycles
(`juliaSet_eq_closure_repelling`, needing degree at least two) and
continuity of `v` conclude. -/
theorem sphereField_eq_zero_on_juliaSet_of_deltaField_eq_zero
    {r : RationalData} (hd : 2 ≤ r.degree) {v : ℂ → ℂ}
    (hv : IsSphereVectorField v)
    (hδ : ∀ z : ℂ, r.denReduced.eval z ≠ 0 → deltaField r v z = 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ JuliaSet r.toSphereMap) → v z = 0 := by
  sorry

end RiemannDynamics
