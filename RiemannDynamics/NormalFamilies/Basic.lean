/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Defs.Sequences

/-!
# Normal families

A family `𝓕` of functions `ℂ → Y` is *normal* on an open set `U ⊆ ℂ` if every
sequence in `𝓕` has a subsequence converging locally uniformly on `U` (to some
limit `g : ℂ → Y`). The target `Y` is left polymorphic (a topological space).
The classical case has `Y = ℂ`; the spherical case has `Y = ℂ̂`.

This file gives the abstract definitions; `Montel.lean` contains the classical
Montel theorem (locally uniformly bounded ⇒ normal).
-/

namespace RiemannDynamics

/-- A family `𝓕` of functions `ℂ → Y` is *normal* on `U` if every sequence drawn
from `𝓕` has a subsequence that converges locally uniformly on `U` to some
limit function `g : ℂ → Y`. -/
def IsNormal {Y : Type*} [UniformSpace Y] (𝓕 : Set (ℂ → Y)) (U : Set ℂ) :
    Prop :=
  ∀ seq : ℕ → 𝓕, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ g : ℂ → Y,
      TendstoLocallyUniformlyOn (fun n => (seq (φ n) : ℂ → Y)) g Filter.atTop U

/-- A family `𝓕` of complex functions is *locally uniformly bounded* on `U` if
the family is uniformly bounded on every compact subset of `U`. -/
def LocallyUniformlyBounded (𝓕 : Set (ℂ → ℂ)) (U : Set ℂ) : Prop :=
  ∀ K, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝓕, ∀ z ∈ K, ‖f z‖ ≤ M

end RiemannDynamics
