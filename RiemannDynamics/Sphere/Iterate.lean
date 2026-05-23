/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Sphere.RationalMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Setoid.Basic

/-!
# Iteration of rational maps and orbit structures

For a rational self-map `f : ℂ̂ → ℂ̂` we record three dynamical orbit
structures used throughout Phases 5–11:

* `ForwardOrbit f z = {f^[n] z | n : ℕ}` — the trajectory forward;
* `BackwardOrbit f z = {w : ℂ̂ | ∃ n, f^[n] w = z}` — preimages under iteration;
* `GrandOrbit f z = {w : ℂ̂ | ∃ m n, f^[m] z = f^[n] w}` — the smallest
  fully `f`-stable set containing `z`. This is the equivalence relation
  Sullivan's deformation argument quotients over.

We use Mathlib's `f^[n]` (= `Nat.iterate f n`) for iteration.
-/

open OnePoint Function

namespace RiemannDynamics

variable (f : ℂ̂ → ℂ̂) (z : ℂ̂)

/-- The forward orbit of `z` under `f`: the set of all forward iterates. -/
def ForwardOrbit : Set ℂ̂ := {w | ∃ n : ℕ, f^[n] z = w}

/-- The backward orbit of `z` under `f`: the set of all preimages under
iteration. -/
def BackwardOrbit : Set ℂ̂ := {w | ∃ n : ℕ, f^[n] w = z}

/-- The grand orbit of `z` under `f`: two points share a grand orbit iff some
forward iterate of one equals some forward iterate of the other. -/
def GrandOrbit : Set ℂ̂ := {w | ∃ m n : ℕ, f^[m] z = f^[n] w}

/-- The grand-orbit equivalence relation on `ℂ̂`. -/
def grandOrbitSetoid : Setoid ℂ̂ where
  r z w := ∃ m n : ℕ, f^[m] z = f^[n] w
  iseqv := {
    refl := fun z => ⟨0, 0, rfl⟩
    symm := fun ⟨m, n, h⟩ => ⟨n, m, h.symm⟩
    trans := by
      rintro x y w ⟨m₁, n₁, h₁⟩ ⟨m₂, n₂, h₂⟩
      refine ⟨m₂ + m₁, n₁ + n₂, ?_⟩
      calc f^[m₂ + m₁] x
          = f^[m₂] (f^[m₁] x) := by rw [Function.iterate_add_apply]
        _ = f^[m₂] (f^[n₁] y) := by rw [h₁]
        _ = f^[n₁] (f^[m₂] y) := by rw [← Function.Commute.iterate_iterate_self]
        _ = f^[n₁] (f^[n₂] w) := by rw [h₂]
        _ = f^[n₁ + n₂] w := by rw [← Function.iterate_add_apply]
  }

/-! ## Basic invariance lemmas (signatures) -/

/-- The forward orbit contains the basepoint `z`. -/
theorem mem_forwardOrbit_self : z ∈ ForwardOrbit f z := ⟨0, rfl⟩

/-- The forward orbit is closed under `f`. -/
theorem forward_invariant_forwardOrbit :
    ∀ w ∈ ForwardOrbit f z, f w ∈ ForwardOrbit f z := by
  rintro w ⟨n, rfl⟩
  exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

/-- The backward orbit contains the basepoint `z`. -/
theorem mem_backwardOrbit_self : z ∈ BackwardOrbit f z := ⟨0, rfl⟩

/-- The backward orbit is `f`-invariant in the sense that preimages stay
inside it. -/
theorem backward_invariant_backwardOrbit
    {w : ℂ̂} (hw : w ∈ BackwardOrbit f z) :
    ∀ v, f v = w → v ∈ BackwardOrbit f z := by
  obtain ⟨n, hn⟩ := hw
  intro v hv
  exact ⟨n + 1, by rw [Function.iterate_succ_apply, hv]; exact hn⟩

/-- The grand orbit contains the basepoint `z`. -/
theorem mem_grandOrbit_self : z ∈ GrandOrbit f z := ⟨0, 0, rfl⟩

/-- The grand orbit is `f`-invariant (closed under `f`). -/
theorem forward_invariant_grandOrbit :
    ∀ w ∈ GrandOrbit f z, f w ∈ GrandOrbit f z := by
  rintro w ⟨m, n, h⟩
  refine ⟨m + 1, n, ?_⟩
  calc f^[m + 1] z
      = f (f^[m] z) := Function.iterate_succ_apply' f m z
    _ = f (f^[n] w) := by rw [h]
    _ = f^[n + 1] w := (Function.iterate_succ_apply' f n w).symm
    _ = f^[n] (f w) := Function.iterate_succ_apply f n w

/-- The grand orbit is closed under `f`-preimages. -/
theorem backward_invariant_grandOrbit :
    ∀ w ∈ GrandOrbit f z, ∀ v, f v = w → v ∈ GrandOrbit f z := by
  rintro w ⟨m, n, h⟩ v hv
  refine ⟨m, n + 1, ?_⟩
  calc f^[m] z
      = f^[n] w := h
    _ = f^[n] (f v) := by rw [hv]
    _ = f^[n + 1] v := (Function.iterate_succ_apply f n v).symm

/-- The grand orbit is the union of the forward and backward orbits over the
forward iterates of `z`. -/
theorem grandOrbit_eq_union_iterate :
    GrandOrbit f z = ⋃ m : ℕ, BackwardOrbit f (f^[m] z) := by
  ext w
  simp only [GrandOrbit, BackwardOrbit, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, h.symm⟩

end RiemannDynamics
