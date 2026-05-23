/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Sphere.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Complex.Basic

/-!
# Rational maps `ℂ̂ → ℂ̂`

A rational map is a ratio `P/Q` of two complex polynomials. After cancelling
the common factor `gcd(P, Q)`, the resulting coprime pair `(P', Q')` defines
a unique map `ℂ̂ → ℂ̂`:

* on a finite point `w ∈ ℂ` with `Q'(w) ≠ 0`, send `w ↦ P'(w)/Q'(w)`;
* on a finite point `w ∈ ℂ` with `Q'(w) = 0` (necessarily `P'(w) ≠ 0` since
  `P'` and `Q'` are coprime), send `w ↦ ∞`;
* at `∞`, send to the limit of `P'/Q'` as the argument grows: `0` if
  `deg P' < deg Q'`, `lc P' / lc Q'` if degrees agree, and `∞` if
  `deg P' > deg Q'`.

The degree of the resulting rational map is `max(deg P', deg Q')`. This
section defines the underlying data carrier, the extension, the predicate
`IsRational`, and the function `degreeOfRational`.
-/

open OnePoint Polynomial

namespace RiemannDynamics

/-- The raw data of a rational map: two complex polynomials with nonzero
denominator. We do not quotient by `(P, Q) ~ (λP, λQ)` here; downstream
results are stated invariantly. -/
structure RationalData where
  /-- Numerator polynomial. -/
  num : ℂ[X]
  /-- Denominator polynomial. -/
  den : ℂ[X]
  /-- The denominator is nonzero. -/
  den_ne_zero : den ≠ 0

namespace RationalData

variable (r : RationalData)

/-- The reduced numerator: `num` divided by `gcd(num, den)`. -/
noncomputable def numReduced : ℂ[X] := r.num / EuclideanDomain.gcd r.num r.den

/-- The reduced denominator: `den` divided by `gcd(num, den)`. -/
noncomputable def denReduced : ℂ[X] := r.den / EuclideanDomain.gcd r.num r.den

/-- The extension of the rational map `num/den` to `ℂ̂ → ℂ̂`. -/
noncomputable def toSphereMap : ℂ̂ → ℂ̂ := fun z =>
  match z with
  | OnePoint.some w =>
      if r.denReduced.eval w = 0 then ∞
      else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)
  | ∞ =>
      if r.numReduced.natDegree < r.denReduced.natDegree then
        ((0 : ℂ) : ℂ̂)
      else if r.numReduced.natDegree = r.denReduced.natDegree then
        ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂)
      else ∞

/-- The degree of the rational map associated with `r`, defined as the maximum
of the reduced numerator's and denominator's degrees. -/
noncomputable def degree : ℕ :=
  max r.numReduced.natDegree r.denReduced.natDegree

end RationalData

/-- A map `f : ℂ̂ → ℂ̂` is *rational* if it arises from some `RationalData`. -/
def IsRational (f : ℂ̂ → ℂ̂) : Prop :=
  ∃ r : RationalData, f = r.toSphereMap

/-- The degree of a rational map `f : ℂ̂ → ℂ̂`. If `f` is not rational, returns
`0` by convention (we never invoke `degreeOfRational` on non-rational maps in
downstream code). -/
noncomputable def degreeOfRational (f : ℂ̂ → ℂ̂) : ℕ :=
  open Classical in if h : IsRational f then h.choose.degree else 0

/-! ## Basic theorems

These are the Phase 1 statements; proofs land in a later prover pass. -/

/-- A rational map extends uniquely from its `RationalData`: any two
`RationalData` values producing the same `ℂ̂ → ℂ̂` map have equal `degree`. -/
theorem RationalData.degree_well_defined
    (r₁ r₂ : RationalData) (h : r₁.toSphereMap = r₂.toSphereMap) :
    r₁.degree = r₂.degree := by
  sorry

/-- `degreeOfRational` is consistent with `RationalData.degree` for any
witness producing the map. -/
theorem degreeOfRational_eq_of_witness
    (f : ℂ̂ → ℂ̂) (r : RationalData) (h : f = r.toSphereMap) :
    degreeOfRational f = r.degree := by
  have hf : IsRational f := ⟨r, h⟩
  unfold degreeOfRational
  rw [dif_pos hf]
  apply RationalData.degree_well_defined
  rw [← hf.choose_spec, ← h]

/-- A rational map sends `ℂ̂` into `ℂ̂` and is `Continuous` for the
one-point-compactification topology. -/
theorem RationalData.toSphereMap_continuous (r : RationalData) :
    Continuous r.toSphereMap := by
  sorry

/-- The composition of two rational maps is rational, with degree equal to
the product of the degrees (assuming both are nonconstant). -/
theorem isRational_comp {f g : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hg : IsRational g) :
    IsRational (f ∘ g) := by
  sorry

/-- Degree multiplicativity under composition for nonconstant rational maps. -/
theorem degreeOfRational_comp {f g : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hg : IsRational g)
    (hfd : 1 ≤ degreeOfRational f) (hgd : 1 ≤ degreeOfRational g) :
    degreeOfRational (f ∘ g) = degreeOfRational f * degreeOfRational g := by
  sorry

end RiemannDynamics
