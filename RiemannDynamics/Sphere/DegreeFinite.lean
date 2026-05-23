/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Sphere.RationalMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finsupp.Defs

/-!
# The parameter space of degree-`d` rational maps

A rational map of degree exactly `d` is parameterised — up to common nonzero
scalar — by the pair of polynomials `(P, Q)` with `deg P, deg Q ≤ d`. We model
this as a pair of coefficient tuples `(Fin (d+1) → ℂ) × (Fin (d+1) → ℂ)`,
which inherits the vector-space structure from Mathlib automatically. The
affine carrier has `ℂ`-dimension `2(d+1) = 2d + 2`; modding out by common
nonzero scalars (the projectivisation that gives the actual moduli space)
takes it down to `2d + 1`.

The finite-dimensionality of this carrier is the *contradiction target* of
Sullivan's No Wandering Domains: a wandering Fatou component would yield an
injective holomorphic map from a polydisk of dimension `> 2d + 1` into the
projectivised carrier, contradicting `2d + 1`-dimensionality.
-/

open Polynomial

namespace RiemannDynamics

/-- The parameter space of degree-at-most-`d` rational maps, represented as a
pair of coefficient tuples for the numerator and denominator polynomials. The
projectivisation (quotient by nonzero ℂ-scalar) is `2d + 1`-dimensional; the
underlying affine carrier we define here is `2d + 2`-dimensional. -/
abbrev RatMap (d : ℕ) : Type :=
  (Fin (d + 1) → ℂ) × (Fin (d + 1) → ℂ)

namespace RatMap

variable {d : ℕ}

/-- Assemble a `RatMap d` value into its numerator polynomial in `ℂ[X]`. -/
noncomputable def toNumPoly (r : RatMap d) : ℂ[X] :=
  ∑ i : Fin (d + 1), Polynomial.C (r.1 i) * X ^ (i : ℕ)

/-- Assemble a `RatMap d` value into its denominator polynomial in `ℂ[X]`. -/
noncomputable def toDenPoly (r : RatMap d) : ℂ[X] :=
  ∑ i : Fin (d + 1), Polynomial.C (r.2 i) * X ^ (i : ℕ)

/-- Convert a `RatMap d` value to the corresponding `RationalData`, provided
its denominator polynomial is nonzero. -/
noncomputable def toRationalData (r : RatMap d) (h : toDenPoly r ≠ 0) :
    RationalData :=
  { num := toNumPoly r, den := toDenPoly r, den_ne_zero := h }

/-! ## Finite-dimensionality

`RatMap d` is finite-dimensional over `ℂ` because it is a finite product of
finite-dimensional spaces. Mathlib's `Module.Finite` infers this directly. -/

/-- The space of degree-at-most-`d` rational-map coefficients is
finite-dimensional over `ℂ`. -/
instance finiteDimensional (d : ℕ) : Module.Finite ℂ (RatMap d) := by
  unfold RatMap
  infer_instance

/-- The `ℂ`-dimension of the affine coefficient carrier is `2(d+1) = 2d + 2`.
The projectivised moduli space has one fewer dimension, namely `2d + 1`. -/
theorem finrank_eq (d : ℕ) :
    Module.finrank ℂ (RatMap d) = 2 * (d + 1) := by
  unfold RatMap
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  ring

/-! ## Connection to the `RationalData` / `IsRational` API -/

/-- Every `RatMap d` value with nonzero denominator induces a rational map
of `degree ≤ d`. -/
theorem toRationalData_degree_le (r : RatMap d) (h : toDenPoly r ≠ 0) :
    (toRationalData r h).degree ≤ d := by
  have hN : (toNumPoly r).natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    calc (Polynomial.C (r.1 i) * X ^ (i : ℕ)).natDegree
        ≤ (i : ℕ) := Polynomial.natDegree_C_mul_X_pow_le _ _
      _ ≤ d := by omega
  have hD : (toDenPoly r).natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    calc (Polynomial.C (r.2 i) * X ^ (i : ℕ)).natDegree
        ≤ (i : ℕ) := Polynomial.natDegree_C_mul_X_pow_le _ _
      _ ≤ d := by omega
  change max (RationalData.numReduced _).natDegree (RationalData.denReduced _).natDegree ≤ d
  apply max_le
  · calc ((toNumPoly r) / gcd (toNumPoly r) (toDenPoly r)).natDegree
        ≤ (toNumPoly r).natDegree :=
            Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le _ _)
      _ ≤ d := hN
  · calc ((toDenPoly r) / gcd (toNumPoly r) (toDenPoly r)).natDegree
        ≤ (toDenPoly r).natDegree :=
            Polynomial.natDegree_le_natDegree (Polynomial.degree_div_le _ _)
      _ ≤ d := hD

/-- Conversely, every rational map of degree `≤ d` arises from some
`RatMap d` value. -/
theorem exists_of_isRational_of_degree_le
    {f : ℂ̂ → ℂ̂} (hf : IsRational f) (hd : degreeOfRational f ≤ d) :
    ∃ r : RatMap d, ∃ h : toDenPoly r ≠ 0,
      f = (toRationalData r h).toSphereMap := by
  obtain ⟨r₀, hr₀⟩ := hf
  -- r₀.degree ≤ d
  have hdeg : r₀.degree ≤ d := by
    have := degreeOfRational_eq_of_witness f r₀ hr₀
    omega
  have hnatNum : r₀.numReduced.natDegree ≤ d := by
    unfold RationalData.degree at hdeg
    exact le_trans (le_max_left _ _) hdeg
  have hnatDen : r₀.denReduced.natDegree ≤ d := by
    unfold RationalData.degree at hdeg
    exact le_trans (le_max_right _ _) hdeg
  have hdenR_ne_zero : r₀.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r₀.den = gcd r₀.num r₀.den * (r₀.den / gcd r₀.num r₀.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r₀.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r₀.den_ne_zero h1
  -- Build the RatMap d from coefficient tuples
  refine ⟨⟨fun i : Fin (d+1) => r₀.numReduced.coeff i,
           fun i : Fin (d+1) => r₀.denReduced.coeff i⟩, ?_, ?_⟩
  · -- toDenPoly ≠ 0 since it equals r₀.denReduced
    show toDenPoly _ ≠ 0
    unfold toDenPoly
    have heq : (∑ i : Fin (d+1), C (r₀.denReduced.coeff (i : ℕ)) * X^(i : ℕ))
             = r₀.denReduced := by
      rw [Fin.sum_univ_eq_sum_range (fun i => C (r₀.denReduced.coeff i) * X^i)]
      exact (Polynomial.as_sum_range_C_mul_X_pow' r₀.denReduced
        (Nat.lt_succ_of_le hnatDen)).symm
    rw [heq]
    exact hdenR_ne_zero
  · -- f = (toRationalData ...).toSphereMap
    -- First show toNumPoly = r₀.numReduced, toDenPoly = r₀.denReduced
    have hNumEq : toNumPoly (d := d) ⟨fun i : Fin (d+1) => r₀.numReduced.coeff i,
                                       fun i : Fin (d+1) => r₀.denReduced.coeff i⟩
                = r₀.numReduced := by
      unfold toNumPoly
      rw [Fin.sum_univ_eq_sum_range (fun i => C (r₀.numReduced.coeff i) * X^i)]
      exact (Polynomial.as_sum_range_C_mul_X_pow' r₀.numReduced
        (Nat.lt_succ_of_le hnatNum)).symm
    have hDenEq : toDenPoly (d := d) ⟨fun i : Fin (d+1) => r₀.numReduced.coeff i,
                                       fun i : Fin (d+1) => r₀.denReduced.coeff i⟩
                = r₀.denReduced := by
      unfold toDenPoly
      rw [Fin.sum_univ_eq_sum_range (fun i => C (r₀.denReduced.coeff i) * X^i)]
      exact (Polynomial.as_sum_range_C_mul_X_pow' r₀.denReduced
        (Nat.lt_succ_of_le hnatDen)).symm
    -- r₀.numReduced and r₀.denReduced are coprime, so gcd = 1
    have hcop : IsCoprime r₀.numReduced r₀.denReduced :=
      isCoprime_div_gcd_div_gcd r₀.den_ne_zero
    have hgcd_one : gcd r₀.numReduced r₀.denReduced = 1 := by
      have hu : IsUnit (gcd r₀.numReduced r₀.denReduced) :=
        (gcd_isUnit_iff _ _).mpr hcop
      have hn : normalize (gcd r₀.numReduced r₀.denReduced) = 1 :=
        normalize_eq_one.mpr hu
      rwa [normalize_gcd] at hn
    -- The h needed: toDenPoly r ≠ 0 — proven from hDenEq + hdenR_ne_zero
    have h_toDen_ne_zero : toDenPoly (d := d) ⟨fun i : Fin (d+1) => r₀.numReduced.coeff i,
                                        fun i : Fin (d+1) => r₀.denReduced.coeff i⟩ ≠ 0 := by
      rw [hDenEq]; exact hdenR_ne_zero
    -- Show (toRationalData ...).numReduced = r₀.numReduced
    have hNumRedEq : (toRationalData ⟨fun i : Fin (d+1) => r₀.numReduced.coeff i,
                                       fun i : Fin (d+1) => r₀.denReduced.coeff i⟩
                                       h_toDen_ne_zero).numReduced
                   = r₀.numReduced := by
      change toNumPoly _ / gcd (toNumPoly _) (toDenPoly _) = r₀.numReduced
      rw [hNumEq, hDenEq, hgcd_one, EuclideanDomain.div_one]
    have hDenRedEq : (toRationalData ⟨fun i : Fin (d+1) => r₀.numReduced.coeff i,
                                       fun i : Fin (d+1) => r₀.denReduced.coeff i⟩
                                       h_toDen_ne_zero).denReduced
                   = r₀.denReduced := by
      change toDenPoly _ / gcd (toNumPoly _) (toDenPoly _) = r₀.denReduced
      rw [hNumEq, hDenEq, hgcd_one, EuclideanDomain.div_one]
    -- toSphereMap depends only on numReduced and denReduced
    rw [hr₀]
    funext z
    change r₀.toSphereMap z = (toRationalData _ h_toDen_ne_zero).toSphereMap z
    rcases z with _ | w
    · -- z = ∞
      simp only [RationalData.toSphereMap]
      rw [hNumRedEq, hDenRedEq]
    · -- z = (w : ℂ̂)
      simp only [RationalData.toSphereMap]
      rw [hNumRedEq, hDenRedEq]

end RatMap

end RiemannDynamics
