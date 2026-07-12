/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Sobolev.WeakDeriv

/-!
# Conformal change of variables for weak derivatives

This file states the two Sobolev bricks transporting the `W^{1,2}_loc` theory across a
conformal conjugation `z ↦ ψ (w (φ z))` and across a puncture.

* `hasWeakDirDeriv_comp_conformal` — the chain rule for weak directional derivatives under a
  holomorphic change of variables on both sides. Let `φ` be holomorphic, injective, with
  nonvanishing derivative `φ'` on an open set `U`, and let `ψ` be holomorphic with derivative
  `ψ'` on an open set `V` receiving `w ∘ φ`. If `w` is continuous on `φ '' U` and carries a
  weak gradient `(gx, gy)` there with locally square-integrable components, then any function
  agreeing with `ψ ∘ w ∘ φ` on `U` has, in each real direction `v`, the weak directional
  derivative `z ↦ ψ'(w(φ z)) · ((v·φ'(z)).re · gx(φ z) + (v·φ'(z)).im · gy(φ z))` on `U`
  (the real differential of `w` at `φ z` evaluated at `v · φ'(z)`, then rotated and scaled by
  `ψ'`), and this derivative is again locally square-integrable on `U`: the Dirichlet class
  is conformally invariant in the plane. Taking `ψ = id` (resp. `φ = id`) specializes to the
  one-sided pre-composition (resp. post-composition) chain rules.

* `HasWeakDirDeriv.removable_singleton` — a single point has zero `W^{1,2}`-capacity: a weak
  directional derivative identity holding on `Ω \ {p}`, for a function continuous on the open
  set `Ω` with locally square-integrable derivative on `Ω`, holds on all of `Ω`.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- **Weak chain rule under conformal change of variables.** For `φ` holomorphic, injective,
with nonvanishing derivative `φ'` on the open set `U`, and `ψ` holomorphic with derivative
`ψ'` on the open set `V` containing `w '' (φ '' U)`: if `w` is continuous on `φ '' U` with a
weak gradient `(gx, gy)` there whose components are locally square-integrable, then every
function agreeing with `ψ ∘ w ∘ φ` on `U` has, in each real direction `v`, the weak
directional derivative `z ↦ ψ'(w(φ z)) · ((v·φ' z).re · gx(φ z) + (v·φ' z).im · gy(φ z))`
on `U`, and this derivative is locally square-integrable on `U`. -/
theorem hasWeakDirDeriv_comp_conformal {w gx gy φ φ' ψ ψ' f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hφ : ∀ z ∈ U, HasDerivAt φ (φ' z) z) (hφ0 : ∀ z ∈ U, φ' z ≠ 0)
    (hφinj : Set.InjOn φ U)
    (hψ : ∀ u ∈ V, HasDerivAt ψ (ψ' u) u)
    (hmaps : Set.MapsTo w (φ '' U) V)
    (hwc : ContinuousOn w (φ '' U))
    (hw : HasWeakGradient gx gy w (φ '' U))
    (hgx : MemLpLocOn gx 2 (φ '' U)) (hgy : MemLpLocOn gy 2 (φ '' U))
    (hfeq : Set.EqOn f (fun z => ψ (w (φ z))) U) (v : ℂ) :
    HasWeakDirDeriv v (fun z =>
        ψ' (w (φ z)) * (((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z)))
      f U ∧
    MemLpLocOn (fun z =>
        ψ' (w (φ z)) * (((v * φ' z).re : ℂ) * gx (φ z) + ((v * φ' z).im : ℂ) * gy (φ z)))
      2 U := by
  sorry

/-- **`W^{1,2}` removability of a point.** A single point has zero `W^{1,2}`-capacity: if `f`
is continuous on the open set `Ω`, `g` is locally square-integrable on `Ω`, and `g` is a weak
directional derivative of `f` in the direction `v` on `Ω \ {p}`, then `g` is a weak
directional derivative of `f` in the direction `v` on all of `Ω`. -/
theorem HasWeakDirDeriv.removable_singleton {f g : ℂ → ℂ} {v p : ℂ} {Ω : Set ℂ}
    (h : HasWeakDirDeriv v g f (Ω \ {p})) (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hg : MemLpLocOn g 2 Ω) :
    HasWeakDirDeriv v g f Ω := by
  sorry

end RiemannDynamics
