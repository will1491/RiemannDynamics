/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Equivalence
import RiemannDynamics.Analysis.SingularIntegral.Beurling.LpHighOpNorm

/-!
# The inverse of an analytic-quasiconformal map is analytic-quasiconformal

This file lays out a **Phase-1 scaffold**: a dependency-ordered chain of theorem
*signatures*, each `:= by sorry`, for the fact that the homeomorphic inverse of an
`IsQCAnalytic` map is again `IsQCAnalytic` (with the "reflected" Beltrami
coefficient). This is the *inverse-is-QC* root that unlocks two of the milestone
9.2 walls: `IsQCAnalytic.image_modulus_zero`'s residual
`image_chainRule_exceptional_modulus_zero` (planar Lusin-(N)) and the genuine
`isQCGeometric_of_isQCAnalytic` modulus bound, both of which follow by applying the
*source-side* length–area machinery to the inverse map `g = f⁻¹`.

Nothing here is proved; the file states maximally-general, mathematically-faithful
signatures that compile, so the proofs can be slotted in later. The two existing
wall sorries in `QC/LengthArea.lean` and `QC/Equivalence.lean` are **not** touched —
this scaffold is standalone.

## The chain

1. `beltrami_higher_integrability` — **Bojarski higher integrability** (the hard
   load-bearing analytic lemma): a `W^{1,2}_loc` solution of an elliptic Beltrami
   equation `∂̄f = μ ∂f` with `‖μ‖∞ < 1` has its `∂`-derivative locally in `Lᵖ` for
   some exponent `p > 2`. Driven by the `Lᵖ` operator-norm continuity of the
   Beurling transform near `p = 2` (`Analysis/SingularIntegral/Beurling`).
2. `IsQCAnalytic.dz_higher_integrability` — the same conclusion specialised to an
   `IsQCAnalytic` map, feeding (1) the `MemW12loc` and Beltrami fields.
3. `IsQCAnalytic.inverse_differentiableAt_ae` — the inverse homeomorphism `g = f⁻¹`
   is differentiable almost everywhere (a `W^{1,p}`, `p > 2`, inverse function
   theorem fed by (2)).
4. `IsQCAnalytic.inverse_beltrami` — `g` solves a Beltrami equation
   `∂̄g = b'.μ ∂g` a.e. for an explicit `b' : BeltramiCoeff` (so `b'.normInf < 1`),
   the "reflected" coefficient.
5. `IsQCAnalytic.inverse_memW12loc` — `g ∈ W^{1,2}_loc`.
6. `IsQCAnalytic.inverse_orientationPreservingHomeo` — `g` is an
   orientation-preserving homeomorphism.
7. `IsQCAnalytic.inverse_isQCAnalytic` — **the root**: `g` is `IsQCAnalytic` for
   some `b'` (assembles 4, 5, 6).
8. `IsQCAnalytic.image_lusinN` — planar **Lusin-(N)** for the degeneracy set:
   `volume (f '' {z | f not differentiable-with-positive-Jacobian at z}) = 0`,
   the crux of the image-side exceptional sweep (follows from (7) by running the
   source-side change of variables for `g`).
9. `IsQCAnalytic.inverse_image_chainRule_exceptional_modulus_zero` — ties (7)/(8)
   to the exact shape of the existing wall
   `IsQCAnalytic.image_chainRule_exceptional_modulus_zero` (stated standalone here;
   the wall sorry in `QC/LengthArea.lean` is left untouched).

The predicate used for "`∂f` is locally `Lᵖ`" is the repo's existing
`MemLpLocOn (fun z => dz f z) (ENNReal.ofReal p) Set.univ` (from
`Analysis/Sobolev/WeakDeriv.lean`): `Lᵖ` on every compact subset of the plane.
-/

open MeasureTheory Complex
open scoped ENNReal

namespace RiemannDynamics

/-- **Bojarski higher integrability** (the hard load-bearing analytic lemma).

A function `f : ℂ → ℂ` in `W^{1,2}_loc` solving an *elliptic* Beltrami equation
`∂̄f = μ ∂f` almost everywhere, with a measurable coefficient `μ` of essential
supremum `< 1`, has its holomorphic Wirtinger derivative `∂f` locally in `Lᵖ` for
some exponent `p > 2`. (Statement is maximally general: it consumes a raw
measurable `μ` with `‖μ‖∞ < 1`, not a bundled `BeltramiCoeff`, and the `W^{1,2}_loc`
membership rather than full quasiconformality.)

*Proof sketch.* Write the Beltrami equation as a fixed point of the
Beurling/Hilbert transform `S` on `∂f`: `∂f = h + S(μ · ∂f)` for a holomorphic
remainder. The `Lᵖ` operator norm of `S` is continuous in `p` with `‖S‖₂ = 1`
(`Analysis/SingularIntegral/Beurling`), so for `p` slightly above `2` one still has
`‖μ‖∞ · ‖S‖ₚ < 1`; the resulting Neumann series converges in `Lᵖ`, giving local
`Lᵖ` control of `∂f`. *Dependency:* the Beurling `Lᵖ` op-norm continuity engine. -/
theorem beltrami_higher_integrability {μ : ℂ → ℂ} (hμmeas : Measurable μ)
    (hμbound : eLpNormEssSup μ volume < 1) {f : ℂ → ℂ} (hf : MemW12loc f)
    (hbel : ∀ᵐ z, dzbar f z = μ z * dz f z) :
    ∃ p : ℝ, 2 < p ∧ MemLpLocOn (fun z => dz f z) (ENNReal.ofReal p) Set.univ := by
  sorry

/-- **Higher integrability for an analytic-quasiconformal map.** The holomorphic
Wirtinger derivative `∂f` of an `IsQCAnalytic` map is locally `Lᵖ` for some `p > 2`.

*Proof sketch.* Apply `beltrami_higher_integrability` to the `MemW12loc` field
`hf.2.1` and the Beltrami field `hf.2.2`, with the bundled coefficient
`b.μ` (measurable by `b.measurable`, `‖μ‖∞ < 1` by `b.bound`).
*Dependency:* `beltrami_higher_integrability`. -/
theorem IsQCAnalytic.dz_higher_integrability {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ p : ℝ, 2 < p ∧ MemLpLocOn (fun z => dz f z) (ENNReal.ofReal p) Set.univ :=
  beltrami_higher_integrability b.measurable b.bound hf.2.1 hf.2.2

/-- **Almost-everywhere differentiability of the inverse.** For an `IsQCAnalytic`
map `f` with inverse homeomorphism `g = f⁻¹`, the inverse `g` is real-differentiable
at almost every point of the plane.

*Proof sketch.* Higher integrability (`dz_higher_integrability`) puts `f` in
`W^{1,p}_loc` with `p > 2`; in the plane `W^{1,p}_loc`, `p > 2`, embeds in
continuously-differentiable-enough maps that the Gehring–Lehto / `W^{1,p}` inverse
function theorem applies, giving a.e. differentiability of `g`. *Dependency:*
`dz_higher_integrability`, `IsHomeomorph.homeomorph`. -/
theorem IsQCAnalytic.inverse_differentiableAt_ae {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ᵐ w, DifferentiableAt ℝ (⇑(hf.1.1.homeomorph f).symm) w := by
  sorry

/-- **The inverse solves a Beltrami equation.** The inverse homeomorphism
`g = f⁻¹` of an `IsQCAnalytic` map satisfies, almost everywhere, a Beltrami
equation `∂̄g = b'.μ ∂g` for an explicit Beltrami coefficient `b'` (so
`b'.normInf < 1`). The coefficient `b'` is the "reflected" one:
`b'.μ (f z) = − (b.μ z) · (∂f z / conj (∂f z))` where it is invertible, the
algebraic image of `b` under `f`.

*Proof sketch.* Where both `f` and `g` are differentiable with invertible
differential (a.e., by `inverse_differentiableAt_ae` and `ae_differentiableAt`),
the Wirtinger chain rule for `g ∘ f = id` inverts the linear relation
`∂̄f = b.μ ∂f`, yielding `∂̄g = b'.μ ∂g` with `‖b'.μ‖ = ‖b.μ‖` pointwise — hence
`‖b'‖∞ = ‖b‖∞ < 1`, so `b'` is a genuine `BeltramiCoeff`. *Dependency:*
`inverse_differentiableAt_ae`, `dzbar_comp`/`dz_comp`. -/
theorem IsQCAnalytic.inverse_beltrami {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ b' : BeltramiCoeff,
      ∀ᵐ w, dzbar (⇑(hf.1.1.homeomorph f).symm) w
        = b'.μ w * dz (⇑(hf.1.1.homeomorph f).symm) w := by
  sorry

/-- **The inverse lies in `W^{1,2}_loc`.** The inverse homeomorphism `g = f⁻¹` of an
`IsQCAnalytic` map is itself `W^{1,2}_loc`.

*Proof sketch.* The change-of-variables `w = f z` transfers the local `L²`
integrability of `∂g`, `∂̄g` from the (higher-than-`2`) integrability of `∂f` and the
Jacobian bounds (`det (Df) ≥ c > 0` locally, via the dilatation inequality
`‖(Df)⁻¹‖² det (Df) ≤ K`); the weak-gradient structure transfers along the a.e.
differentiability of `g`. *Dependency:* `dz_higher_integrability`,
`inverse_differentiableAt_ae`. -/
theorem IsQCAnalytic.inverse_memW12loc {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    MemW12loc (⇑(hf.1.1.homeomorph f).symm) := by
  sorry

/-- **The inverse is an orientation-preserving homeomorphism.** The inverse
`g = f⁻¹` of an `IsQCAnalytic` map is a homeomorphism with a.e. positive Jacobian.

*Proof sketch.* `g = (hf.1.1.homeomorph f).symm` is a homeomorphism by construction.
For the Jacobian: where `g` is differentiable with `f` differentiable at `g w`
(a.e.), `Dg w = (Df (g w))⁻¹`, so `det (Dg w) = 1 / det (Df (g w)) > 0` from the
a.e. positivity field `hf.1.2` pulled back through the measure-preserving-up-to-
Jacobian change of variables. *Dependency:* `inverse_differentiableAt_ae`,
`IsQCAnalytic.ae_differentiableAt`. -/
theorem IsQCAnalytic.inverse_orientationPreservingHomeo {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    OrientationPreservingHomeo (⇑(hf.1.1.homeomorph f).symm) := by
  sorry

/-- **The inverse of an analytic-quasiconformal map is analytic-quasiconformal**
(the ROOT). The inverse homeomorphism `g = f⁻¹` of an `IsQCAnalytic` map satisfies
`IsQCAnalytic g b'` for some Beltrami coefficient `b'`.

*Proof sketch.* Assemble the three `IsQCAnalytic` fields for `g`:
`inverse_orientationPreservingHomeo`, `inverse_memW12loc`, and the Beltrami
equation from `inverse_beltrami` (whose `b'` is the witness). *Dependency:*
`inverse_beltrami`, `inverse_memW12loc`,
`inverse_orientationPreservingHomeo`. -/
theorem IsQCAnalytic.inverse_isQCAnalytic {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∃ b' : BeltramiCoeff, IsQCAnalytic (⇑(hf.1.1.homeomorph f).symm) b' := by
  obtain ⟨b', hbel⟩ := hf.inverse_beltrami
  exact ⟨b', hf.inverse_orientationPreservingHomeo, hf.inverse_memW12loc, hbel⟩

/-- **Planar Lusin-(N) for the degeneracy set.** For an `IsQCAnalytic` map `f`, the
image under `f` of the set where `f` fails to be differentiable with positive
Jacobian is Lebesgue-null. This is the crux of the image-side exceptional sweep
`IsQCAnalytic.image_chainRule_exceptional_modulus_zero`.

*Proof sketch.* The degeneracy set `N = {z | ¬DifferentiableAt ℝ f z ∨
¬ 0 < det (Df z)}` is null (`ae_differentiableAt` + `hf.1.2`). Apply the
source-side change-of-variables / Lusin-(N) property to the *inverse*
`g = f⁻¹` (which is `IsQCAnalytic` by `inverse_isQCAnalytic`, hence
`W^{1,2}_loc` and so satisfies Lusin-(N)): `f '' N = g⁻¹ '' N` has measure
`∫_N |det (Df)| = 0`. *Dependency:* `inverse_isQCAnalytic`,
`IsQCAnalytic.ae_differentiableAt`. -/
theorem IsQCAnalytic.image_lusinN {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    volume (f '' {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det}) = 0 := by
  sorry

/-- **Image-side exceptional sweep, via inverse-is-QC** (standalone restatement of
the existing wall `IsQCAnalytic.image_chainRule_exceptional_modulus_zero`). For an
`IsQCAnalytic` map `f` and a family `Γ` of continuous, absolutely continuous curves,
the image under `f` of the chain-rule exceptional subfamily has zero modulus.

This is stated here with the **same shape** as the `QC/LengthArea.lean` wall, to
record that the inverse-is-QC root (`inverse_isQCAnalytic`) plus planar Lusin-(N)
(`image_lusinN`) supplies its missing ingredient. The original wall sorry in
`QC/LengthArea.lean` is deliberately left untouched; this scaffold is standalone.

*Proof sketch.* The exceptional curves' images form, via the inverse `g = f⁻¹`, a
source-side exceptional family for `g`; apply `g`'s own
`IsQCAnalytic.chainRule_exceptional_modulus_zero` (from `inverse_isQCAnalytic`)
together with `image_lusinN` to conclude the image modulus vanishes. *Dependency:*
`inverse_isQCAnalytic`, `image_lusinN`,
`IsQCAnalytic.chainRule_exceptional_modulus_zero`. -/
theorem IsQCAnalytic.inverse_image_chainRule_exceptional_modulus_zero {f : ℂ → ℂ}
    {b : BeltramiCoeff} (hf : IsQCAnalytic f b) (Γ : Set (ℝ → ℂ))
    (hcont : ∀ γ ∈ Γ, Continuous γ)
    (hac : ∀ γ ∈ Γ, AbsolutelyContinuousOnInterval γ 0 1) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) ''
      {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
        (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
        ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
          HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)}) = 0 := by
  sorry

end RiemannDynamics
