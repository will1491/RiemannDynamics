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

A family `𝓕` of functions `X → Y` is *normal* on a set `U ⊆ X` if every
sequence in `𝓕` has a subsequence converging locally uniformly on `U` (to
some limit `g : X → Y`). The domain `X` is a topological space and the
target `Y` a uniform space. The classical case has `X = ℂ` and `Y = ℂ`;
the spherical case has `Y = ℂ̂`; the dynamics of rational maps uses
`X = Y = ℂ̂`.

`IsNormalAt 𝓕 z` localizes the notion to a neighborhood of a point; it is
the membership predicate defining the Fatou set.

This file gives the abstract definitions and their monotonicity/transfer
lemmas; `Montel.lean` contains the classical Montel theorem (locally
uniformly bounded ⇒ normal).
-/

namespace RiemannDynamics

/-- A family `𝓕` of functions `X → Y` is *normal* on `U` if every sequence
drawn from `𝓕` has a subsequence that converges locally uniformly on `U` to
some limit function `g : X → Y`. -/
def IsNormal {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (𝓕 : Set (X → Y)) (U : Set X) : Prop :=
  ∀ seq : ℕ → 𝓕, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ g : X → Y,
      TendstoLocallyUniformlyOn (fun n => (seq (φ n) : X → Y)) g Filter.atTop U

/-- A family `𝓕` is *normal at a point* `z` if it is normal on some
neighborhood of `z`. -/
def IsNormalAt {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    (𝓕 : Set (X → Y)) (z : X) : Prop :=
  ∃ U ∈ nhds z, IsNormal 𝓕 U

/-- A family `𝓕` of complex functions is *locally uniformly bounded* on `U` if
the family is uniformly bounded on every compact subset of `U`. -/
def LocallyUniformlyBounded (𝓕 : Set (ℂ → ℂ)) (U : Set ℂ) : Prop :=
  ∀ K, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ f ∈ 𝓕, ∀ z ∈ K, ‖f z‖ ≤ M

/-- Normality is antitone in the domain: a family normal on `U` is normal on
any subset of `U`. -/
theorem IsNormal.mono {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {𝓕 : Set (X → Y)} {U V : Set X} (hN : IsNormal 𝓕 U) (hVU : V ⊆ U) :
    IsNormal 𝓕 V := by
  intro seq
  obtain ⟨φ, hφ, g, hg⟩ := hN seq
  exact ⟨φ, hφ, g, hg.mono hVU⟩

/-- Normality passes to subfamilies. -/
theorem IsNormal.of_subfamily {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {𝓕 𝓖 : Set (X → Y)} {U : Set X} (hN : IsNormal 𝓕 U)
    (h𝓖 : 𝓖 ⊆ 𝓕) : IsNormal 𝓖 U := by
  intro seq
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨(seq n : X → Y), h𝓖 (seq n).2⟩
  exact ⟨φ, hφ, g, hg⟩

/-- The set of points at which a family is normal is open. -/
theorem isOpen_setOf_isNormalAt {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] (𝓕 : Set (X → Y)) :
    IsOpen {z : X | IsNormalAt 𝓕 z} := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨U, hU, hN⟩
  refine ⟨interior U, fun w hw => ?_, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hU⟩
  exact ⟨interior U, isOpen_interior.mem_nhds hw, hN.mono interior_subset⟩

/-- Normality transfers along post-composition with a uniformly continuous
map: locally uniform convergence of a subsequence is preserved by `T ∘ ·`. -/
theorem IsNormal.comp_uniformContinuous {X Y Z : Type*} [TopologicalSpace X]
    [UniformSpace Y] [UniformSpace Z] {𝓕 : Set (X → Y)} {U : Set X}
    (hN : IsNormal 𝓕 U) {T : Y → Z} (hT : UniformContinuous T) :
    IsNormal ((fun f => fun z => T (f z)) '' 𝓕) U := by
  intro seq
  choose f hf hfe using fun n => (seq n).2
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨f n, hf n⟩
  refine ⟨φ, hφ, fun z => T (g z), ?_⟩
  exact (hT.comp_tendstoLocallyUniformlyOn hg).congr
    fun n z _ => congrFun (hfe (φ n)) z

/-- Normality only depends on the restrictions of the family members to `U`:
if every member of `𝓖` agrees on `U` with some member of a normal family
`𝓕`, then `𝓖` is normal. -/
theorem IsNormal.of_forall_exists_eqOn {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {𝓕 𝓖 : Set (X → Y)} {U : Set X} (hN : IsNormal 𝓕 U)
    (h : ∀ g ∈ 𝓖, ∃ f ∈ 𝓕, Set.EqOn f g U) :
    IsNormal 𝓖 U := by
  intro seq
  choose f hf hfe using fun n => h (seq n) (seq n).2
  obtain ⟨φ, hφ, g, hg⟩ := hN fun n => ⟨f n, hf n⟩
  exact ⟨φ, hφ, g, hg.congr fun n => hfe (φ n)⟩

end RiemannDynamics
