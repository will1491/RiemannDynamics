/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.Deformation.DeltaOperator
import RiemannDynamics.Dynamics.FatouComponents.Periodic
import RiemannDynamics.Dynamics.FatouComponents.GrandOrbit

/-!
# Spreading a seed coefficient over a wandering grand orbit

Given a rational map `f` (through `r : RationalData`), a wandering Fatou
component `U` on which every iterate is injective, and a *seed* coefficient
`σ` carried by a set `S` whose points lie in `U`, this file constructs the
**spread** `spreadCoeff r S σ`: the `f`-invariant Beltrami coefficient on `ℂ`
that restricts to `σ` on `U` and vanishes off the grand-orbit saturation
of `S`.

The construction is by the invariance transport law. Iterating the pullback
convention `μ(z) = μ(f z)·conj(f′(z))/f′(z)` (see `IsInvariantBeltrami`)
along orbit segments, a point `z` with `f^[m] z = f^[n] y` for some `y ∈ S`
must carry the value

`μ(z) = σ(y) · Dⁿ(y)/conj(Dⁿ(y)) · conj(Dᵐ(z))/Dᵐ(z)`,

where `Dᵏ = iterDeriv r k` is the finite-chart derivative of the `k`-th
iterate (a product of `fderivRational` along the orbit, `iterDeriv`), and the
two unimodular quotients form the twist cocycle `spreadTwist`. The definition
selects a witness `(m, n, y)` by choice; crucially the selection predicate
depends only on `(r, S, z)` and *not* on `σ`, so `spreadCoeff` is genuinely
pointwise-linear in the seed (`spreadCoeff_add`, `spreadCoeff_smul`).

All dynamical content lives in the theorems, not the definition:

* *witness independence* — cross-time identifications are impossible because
  the components `fcOrbit f U k` are pairwise disjoint (wandering), same-time
  identifications collapse by injectivity of the iterates on `U`, and the
  twist values agree by the derivative cocycle. This yields the restriction
  law `spreadCoeff_restrict` (the spread extends `σ` pointwise on the finite
  part of `U`) and the invariance law `isInvariantBeltrami_spreadCoeff`.
* *size and regularity* — the twist is unimodular (or Lean-junk `0`, on the
  null set of points whose orbit segment meets a critical point or `∞`), so
  the essential sup does not grow (`spreadCoeff_eLpNormEssSup_le`); the
  countable decomposition of the saturation into `(m, n)`-pieces gives
  almost-everywhere measurability (`spreadCoeff_aemeasurable` — plain
  measurability is not available because the value on the exceptional null
  set is produced by an arbitrary choice function).
-/

open MeasureTheory Complex Metric Filter Topology Function OnePoint

namespace RiemannDynamics

/-! ## The derivative cocycle along orbits -/

/-- The finite-chart derivative of the `m`-th iterate along the orbit of `z`:
the product of `fderivRational` at the finite readings of
`z, f z, …, f^[m−1] z`. Junk if the orbit segment meets `∞` (the reading `0`
is used); all statements either assume finiteness of the segment or work
almost everywhere. -/
noncomputable def iterDeriv (r : RationalData) (m : ℕ) : ℂ → ℂ := fun z =>
  ∏ j ∈ Finset.range m,
    fderivRational r (chartFiniteMap (r.toSphereMap^[j] ((z : ℂ̂))))

/-- The cocycle law for `iterDeriv`: the derivative of the `(m+n)`-th iterate
splits at time `m`, provided the time-`m` point is finite (so that its
finite-chart reading really is the point). -/
theorem iterDeriv_add (r : RationalData) (m n : ℕ) (z : ℂ)
    (hfin : r.toSphereMap^[m] ((z : ℂ̂)) ≠ ∞) :
    iterDeriv r (m + n) z
      = iterDeriv r m z
          * iterDeriv r n (chartFiniteMap (r.toSphereMap^[m] ((z : ℂ̂)))) := by
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  obtain ⟨w, hw⟩ : ∃ w : ℂ, r.toSphereMap^[m] ((z : ℂ̂)) = ((w : ℂ̂)) := by
    cases hc : r.toSphereMap^[m] ((z : ℂ̂)) with
    | infty => exact absurd hc hfin
    | coe v => exact ⟨v, rfl⟩
  simp only [iterDeriv]
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hw, cf, ← hw, add_comm m j, Function.iterate_add_apply]

/-- Along an orbit segment that stays finite, `iterDeriv` is the honest
derivative of the finite-chart reading of the iterate (chain rule telescoped
through `RationalData.deriv_reading`). -/
theorem iterDeriv_eq_deriv_iterate (r : RationalData) (m : ℕ) (z : ℂ)
    (hfin : ∀ j : ℕ, j ≤ m → r.toSphereMap^[j] ((z : ℂ̂)) ≠ ∞) :
    iterDeriv r m z
      = deriv (fun x : ℂ => chartFiniteMap (r.toSphereMap^[m] ((x : ℂ̂)))) z := by
  have cf : ∀ x : ℂ, chartFiniteMap ((x : ℂ̂)) = x := fun _ => rfl
  have key : ∀ (k : ℕ) (w : ℂ), (∀ j : ℕ, j ≤ k → r.toSphereMap^[j] ((w : ℂ̂)) ≠ ∞) →
      HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂))))
        (iterDeriv r k w) w := by
    intro k
    induction k with
    | zero =>
        intro w _
        have h1 : iterDeriv r 0 w = 1 := by simp [iterDeriv]
        have h2 : (fun x : ℂ => chartFiniteMap (r.toSphereMap^[0] ((x : ℂ̂))))
            = fun x : ℂ => x := funext fun x => rfl
        rw [h1, h2]
        exact hasDerivAt_id w
    | succ k ih =>
        intro w hw
        -- the derivative of the `k`-th reading at `w`, from the induction hypothesis
        have hk := ih w fun j hj => hw j (Nat.le_succ_of_le hj)
        -- the finite reading `u` of the `k`-th iterate at `w`
        obtain ⟨u, hu⟩ : ∃ u : ℂ, r.toSphereMap^[k] ((w : ℂ̂)) = ((u : ℂ̂)) := by
          cases hc : r.toSphereMap^[k] ((w : ℂ̂)) with
          | infty => exact absurd hc (hw k (Nat.le_succ k))
          | coe v => exact ⟨v, rfl⟩
        have hhw : chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))) = u := by
          rw [hu, cf]
        -- `u` is not a pole: the `(k+1)`-st point is finite
        have hfu : r.toSphereMap ((u : ℂ̂)) ≠ ∞ := by
          have h1 : r.toSphereMap^[k + 1] ((w : ℂ̂)) ≠ ∞ := hw (k + 1) le_rfl
          rw [Function.iterate_succ_apply', hu] at h1
          exact h1
        have hden : r.denReduced.eval u ≠ 0 := by
          intro h0
          apply hfu
          have hread : r.toSphereMap ((u : ℂ̂))
              = if r.denReduced.eval u = 0 then (∞ : ℂ̂)
                else ((r.numReduced.eval u / r.denReduced.eval u : ℂ) : ℂ̂) := rfl
          rw [hread, if_pos h0]
        -- the derivative of the reading of `f` at the non-pole `u`
        have hg : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u) u := by
          have hdiv : HasDerivAt (fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x)
              (((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2) u :=
            (r.numReduced.hasDerivAt u).div (r.denReduced.hasDerivAt u) hden
          have hev' : (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              =ᶠ[𝓝 u] fun x : ℂ => r.numReduced.eval x / r.denReduced.eval x := by
            filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with x hx
            have hread : r.toSphereMap ((x : ℂ̂))
                = if r.denReduced.eval x = 0 then (∞ : ℂ̂)
                  else ((r.numReduced.eval x / r.denReduced.eval x : ℂ) : ℂ̂) := rfl
            rw [hread, if_neg hx, cf]
          have hfd : fderivRational r u
              = ((Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u)
                / r.denReduced.eval u ^ 2 := by
            have hwr : r.wronskian.eval u
                = (Polynomial.derivative r.numReduced).eval u * r.denReduced.eval u
                  - r.numReduced.eval u * (Polynomial.derivative r.denReduced).eval u := by
              simp only [RationalData.wronskian, Polynomial.eval_sub, Polynomial.eval_mul]
            have hfd0 : fderivRational r u
                = r.wronskian.eval u / (r.denReduced.eval u) ^ 2 := rfl
            rw [hfd0, hwr]
          rw [hfd]
          exact hdiv.congr_of_eventuallyEq hev'
        -- the set where the `k`-th iterate stays finite is open
        have hopen : IsOpen {x : ℂ | r.toSphereMap^[k] ((x : ℂ̂)) ≠ ∞} := by
          have hc : Continuous fun x : ℂ => r.toSphereMap^[k] ((x : ℂ̂)) :=
            (r.toSphereMap_continuous.iterate k).comp OnePoint.continuous_coe
          exact OnePoint.isClosed_infty.isOpen_compl.preimage hc
        -- near `w`, the `(k+1)`-reading is the composite of the two readings
        have hev : ((fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
              ∘ fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂))))
            =ᶠ[𝓝 w] fun x : ℂ => chartFiniteMap (r.toSphereMap^[k + 1] ((x : ℂ̂))) := by
          filter_upwards [hopen.mem_nhds (hw k (Nat.le_succ k))] with x hx
          obtain ⟨v, hv⟩ : ∃ v : ℂ, r.toSphereMap^[k] ((x : ℂ̂)) = ((v : ℂ̂)) := by
            cases hc : r.toSphereMap^[k] ((x : ℂ̂)) with
            | infty => exact absurd hc hx
            | coe v => exact ⟨v, rfl⟩
          simp only [Function.comp_apply]
          rw [Function.iterate_succ_apply', hv, cf]
        -- chain rule at the pair of matched points
        have hg2 : HasDerivAt (fun x : ℂ => chartFiniteMap (r.toSphereMap ((x : ℂ̂))))
            (fderivRational r u)
            ((fun x : ℂ => chartFiniteMap (r.toSphereMap^[k] ((x : ℂ̂)))) w) := by
          show HasDerivAt _ _ (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂))))
          rw [hhw]
          exact hg
        have hcomp := HasDerivAt.comp w hg2 hk
        -- convert the derivative value through the cocycle product
        have hval : iterDeriv r (k + 1) w = fderivRational r u * iterDeriv r k w := by
          have h1 : iterDeriv r (k + 1) w
              = iterDeriv r k w
                  * fderivRational r (chartFiniteMap (r.toSphereMap^[k] ((w : ℂ̂)))) := by
            simp only [iterDeriv]
            exact Finset.prod_range_succ _ k
          rw [h1, hhw, mul_comm]
        rw [hval]
        exact hcomp.congr_of_eventuallyEq hev.symm
  exact (key m z hfin).deriv.symm

/-! ## The spread coefficient -/

/-- The **twist cocycle** transporting a seed value at `y` (pushed forward
`n` steps) back to `z` (pulled back `m` steps):
`Dⁿ(y)/conj(Dⁿ(y)) · conj(Dᵐ(z))/Dᵐ(z)`. Unimodular whenever both iterate
derivatives are nonzero; the Lean junk value when one vanishes is `0`
(as `0/0 = 0`), which is measure-theoretically harmless — such `z` lie in
the countable union of iterated preimages of the critical points and `∞`,
a null set. -/
noncomputable def spreadTwist (r : RationalData) (m n : ℕ) (z y : ℂ) : ℂ :=
  iterDeriv r n y / starRingEnd ℂ (iterDeriv r n y)
    * (starRingEnd ℂ (iterDeriv r m z) / iterDeriv r m z)

/-- The **spread** of a seed `σ` carried by `S ⊆ ℂ` to a coefficient on all
of `ℂ`: at a point `z` of the grand-orbit saturation of `S` — i.e. admitting
`(m, n, y)` with `y ∈ S` and `f^[m] z = f^[n] y` — the value is the twisted
seed value `spreadTwist · σ(y)` at a chosen witness; elsewhere `0`.

The witness is produced by `Classical.choose` from a predicate that mentions
only `r`, `S`, and `z` — never `σ` — so the map `σ ↦ spreadCoeff r S σ` is
pointwise linear by construction. Independence of the value from the chosen
witness is *not* built into the definition; it is the content of the
restriction and invariance theorems below, under the wandering/injectivity
hypothesis package. -/
noncomputable def spreadCoeff (r : RationalData) (S : Set ℂ) (σ : ℂ → ℂ) :
    ℂ → ℂ := fun z =>
  open Classical in
  if h : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  then
    spreadTwist r (Classical.choose h).1 (Classical.choose h).2.1 z
        (Classical.choose h).2.2
      * σ (Classical.choose h).2.2
  else 0

/-- **Additivity in the seed.** The witness selection does not depend on the
seed, so the spread of a sum is the sum of the spreads, pointwise and
unconditionally. -/
theorem spreadCoeff_add (r : RationalData) (S : Set ℂ) (σ₁ σ₂ : ℂ → ℂ) :
    spreadCoeff r S (fun z => σ₁ z + σ₂ z)
      = fun z => spreadCoeff r S σ₁ z + spreadCoeff r S σ₂ z := by
  funext z
  unfold spreadCoeff
  by_cases h : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  · simp only [dif_pos h]
    ring
  · simp only [dif_neg h]
    ring

/-- **Homogeneity in the seed.** As for additivity: the selection is
seed-independent, so scalars pass through pointwise and unconditionally. -/
theorem spreadCoeff_smul (r : RationalData) (S : Set ℂ) (c : ℂ) (σ : ℂ → ℂ) :
    spreadCoeff r S (fun z => c * σ z)
      = fun z => c * spreadCoeff r S σ z := by
  funext z
  unfold spreadCoeff
  by_cases h : ∃ p : ℕ × ℕ × ℂ, p.2.2 ∈ S ∧
      r.toSphereMap^[p.1] ((z : ℂ̂)) = r.toSphereMap^[p.2.1] ((p.2.2 : ℂ̂))
  · simp only [dif_pos h]
    ring
  · simp only [dif_neg h]
    ring

/-! ## The hypothesis package

The dynamical theorems below share the following data: a wandering Fatou
component `U` of `f = r.toSphereMap` with all iterates injective on `U`,
whose forward orbit components avoid `∞`, with no critical point of any
iterate on `U` (phrased through the nonvanishing of `iterDeriv`); a carrier
`S` whose points lie in `U`; and a seed `σ` vanishing off `S`. The interface
theorem of `EventualInjectivity.lean` produces exactly this package from an
arbitrary wandering component. -/

/-- **The spread extends the seed.** On the finite part of `U`, the spread
equals `σ` pointwise: a witness `(m, n, y)` for `z ∈ U` forces `m = n` (the
orbit components are pairwise disjoint) and then `y = z` (injectivity of
`f^[m]` on `U`), and the twist collapses to `1` because the iterate
derivative at `z` does not vanish; points of `U ∖ S` admit no witness at
all, matching `σ = 0` there. -/
theorem spreadCoeff_restrict {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U))
    (hσ : ∀ z : ℂ, z ∉ S → σ z = 0) :
    ∀ z : ℂ, ((z : ℂ̂) ∈ U) → spreadCoeff r S σ z = σ z := by
  sorry

/-- **Almost-everywhere measurability of the spread.** The saturation
decomposes into the countable family of `(m, n)`-pieces; on each piece, off
the null set of orbit segments meeting critical points or `∞`, the witness
point `y` is uniquely determined (wandering plus injectivity) and depends on
`z` through local holomorphic inverse branches, so the spread agrees a.e.
with a measurable function. Plain measurability is not claimed: on the
exceptional null set the value is produced by an arbitrary choice
function. -/
theorem spreadCoeff_aemeasurable {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U)) (hSm : MeasurableSet S)
    (hσ : ∀ z : ℂ, z ∉ S → σ z = 0) (hσm : Measurable σ) :
    AEMeasurable (spreadCoeff r S σ) volume := by
  sorry

/-- **The spread does not increase the essential sup.** The twist is
unimodular off a null set (and Lean-junk `0` on it), and the seed value is
sampled through grand-orbit correspondences built from holomorphic maps,
which pull null sets back to null sets; hence
`‖spreadCoeff r S σ‖∞ ≤ ‖σ‖∞`. -/
theorem spreadCoeff_eLpNormEssSup_le {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U)) (hSm : MeasurableSet S)
    (hσ : ∀ z : ℂ, z ∉ S → σ z = 0) (hσm : Measurable σ) :
    eLpNormEssSup (spreadCoeff r S σ) volume
      ≤ eLpNormEssSup σ volume := by
  sorry

/-- **Invariance of the spread.** The spread satisfies the pullback law
`μ(z)·f′(z) = μ(f z)·conj(f′(z))` almost everywhere: the saturation is fully
invariant with witnesses shifting by one time step, the transported values
agree by witness independence (wandering, injectivity, and the twist
cocycle `iterDeriv_add`), the complement carries `0` on both sides, and the
finitely many poles together with the orbit segments through critical points
or `∞` form a null set. This is the hypothesis `DeltaOperator.lean` consumes
to kill the weak `∂̄` of the deformation field. -/
theorem isInvariantBeltrami_spreadCoeff {r : RationalData} (hd : 1 ≤ r.degree)
    {U : Set ℂ̂} {S : Set ℂ} {σ : ℂ → ℂ}
    (hU : IsFatouComponent r.toSphereMap U)
    (hW : IsWandering r.toSphereMap U)
    (hinj : ∀ n : ℕ, Set.InjOn (r.toSphereMap^[n]) U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit r.toSphereMap U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ U) → ∀ n : ℕ, iterDeriv r n z ≠ 0)
    (hS : ∀ z ∈ S, ((z : ℂ̂) ∈ U)) (hSm : MeasurableSet S)
    (hσ : ∀ z : ℂ, z ∉ S → σ z = 0) (hσm : Measurable σ) :
    IsInvariantBeltrami r (spreadCoeff r S σ) := by
  sorry

end RiemannDynamics
