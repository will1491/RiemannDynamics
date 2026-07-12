import RiemannDynamics.Teichmuller.Metric
import RiemannDynamics.Surface.MappingClassGroup
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# The moduli group and its isometric action on Teichmüller space

The moduli group `modGroup Γ₀` consists of the normalized symmetric quasiconformal
self-homeomorphisms of the plane compatible with `Γ₀` on both sides (`F ∘ γ = γ' ∘ F` a.e.
with `γ, γ'` running through `Γ₀`). It acts on `Teich Γ₀` by pulling back representatives
along the inverse, `F • [x] = [x.pull F⁻¹]`, where the pulled representative is characterized
by `(x.pull F).w = x.w ∘ F`. The action is isometric: candidate maps for a pair of pulled
representatives are literally the candidates for the original pair, reindexed along the real
line. The orbit space is the moduli space `Moduli Γ₀`.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The moduli group -/

/-- The carrier of the moduli group: quasiconformal, conjugation-symmetric, normalized plane
homeomorphisms compatible with `Γ₀` on both sides. -/
def modGroupCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Set (ℂ ≃ₜ ℂ) :=
  {F | (∃ K : ℝ, IsQCGeometric (⇑F) K)
    ∧ (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    ∧ F 0 = 0 ∧ F 1 = 1
    ∧ (∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap γ' (F z))
    ∧ (∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap γ' (F z))}

/-- The identity homeomorphism belongs to the moduli carrier. -/
theorem one_mem_modGroupCarrier (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    (1 : ℂ ≃ₜ ℂ) ∈ modGroupCarrier Γ₀ := by
  sorry

/-- The moduli carrier is closed under composition: dilatations multiply, and the two-sided
compatibility clauses chain, pulling null sets back through Möbius maps and quasiconformal
inverses. -/
theorem mul_mem_modGroupCarrier {F G : ℂ ≃ₜ ℂ} (hF : F ∈ modGroupCarrier Γ₀)
    (hG : G ∈ modGroupCarrier Γ₀) : F * G ∈ modGroupCarrier Γ₀ := by
  sorry

/-- The moduli carrier is closed under inversion: the two-sided compatibility clauses swap. -/
theorem inv_mem_modGroupCarrier {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroupCarrier Γ₀) :
    F⁻¹ ∈ modGroupCarrier Γ₀ := by
  sorry

/-- The **moduli group** over the base `Γ₀`: normalized symmetric quasiconformal plane
homeomorphisms compatible with `Γ₀` on both sides, a subgroup of the group of plane
self-homeomorphisms. -/
def modGroup (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Subgroup (ℂ ≃ₜ ℂ) where
  carrier := modGroupCarrier Γ₀
  one_mem' := one_mem_modGroupCarrier Γ₀
  mul_mem' := fun hF hG => mul_mem_modGroupCarrier hF hG
  inv_mem' := fun hF => inv_mem_modGroupCarrier hF

/-- Membership in the moduli group unfolds to membership in its carrier. -/
theorem mem_modGroup_iff {F : ℂ ≃ₜ ℂ} : F ∈ modGroup Γ₀ ↔ F ∈ modGroupCarrier Γ₀ :=
  Iff.rfl

/-- A compatibility identity of a moduli-group element holds at every non-pole point, by
continuity of both sides on the open co-null set. -/
theorem modGroup_equivariant_offPole {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀)
    {γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hae : ∀ᵐ z : ℂ, F (moebiusMap γ z) = moebiusMap γ' (F z)) :
    ∀ z : ℂ, moebiusDenom γ z ≠ 0 → F (moebiusMap γ z) = moebiusMap γ' (F z) := by
  sorry

/-- A moduli-group element maps real points to real points. -/
theorem modGroup_real_im {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀) (t : ℝ) :
    (F (t : ℂ)).im = 0 := by
  sorry

/-- The real trace of a moduli-group element is strictly increasing. -/
theorem modGroup_real_strictMono {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀) :
    StrictMono fun t : ℝ => (F (t : ℂ)).re := by
  sorry

/-- The real trace of a moduli-group element is onto the real line. -/
theorem modGroup_real_surjective {F : ℂ ≃ₜ ℂ} (hF : F ∈ modGroup Γ₀) :
    Function.Surjective fun t : ℝ => (F (t : ℂ)).re := by
  sorry

/-! ## Pulling back representatives -/

/-- The coefficient of `x.w ∘ F` for a moduli-group element `F` is again a Teichmüller
representative: symmetric by the symmetry clauses, invariant by the compatibility clauses and
the equivariance of `x.w`. -/
theorem exists_pull_rep (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) :
    ∃ y : TeichRep Γ₀, IsQCAnalytic (x.w ∘ ⇑F) y.b := by
  sorry

/-- The pullback of a representative along a moduli-group element: a representative whose
coefficient is the coefficient of `x.w ∘ F`. -/
noncomputable def TeichRep.pull (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ)
    (hF : F ∈ modGroup Γ₀) : TeichRep Γ₀ :=
  (exists_pull_rep x F hF).choose

/-- The pulled representative carries a coefficient of `x.w ∘ F`. -/
theorem TeichRep.pull_isQCAnalytic (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ)
    (hF : F ∈ modGroup Γ₀) : IsQCAnalytic (x.w ∘ ⇑F) (x.pull F hF).b :=
  (exists_pull_rep x F hF).choose_spec

/-- A quasiconformal map that is Möbius-conjugated by `γ` has a `γ`-invariant coefficient:
differentiating `h ∘ γ = W ∘ h` a.e. yields the multiplicative invariance law. -/
theorem isInvariantBeltrami'_single_of_moebius_conj {h : ℂ → ℂ} {bh : BeltramiCoeff}
    (hh : IsQCAnalytic h bh) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hconj : ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ᵐ z : ℂ, h (moebiusMap γ z) = moebiusMap W (h z)) :
    ∀ᵐ z : ℂ, bh.μ (moebiusMap γ z) * (moebiusDenom γ z) ^ 2
      = bh.μ z * (starRingEnd ℂ (moebiusDenom γ z)) ^ 2 := by
  sorry

/-- The normalized solution of the pulled representative is `x.w ∘ F`: the composition is
quasiconformal with the pulled coefficient and fixes `0` and `1`. -/
theorem TeichRep.pull_w (x : TeichRep Γ₀) (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) :
    (x.pull F hF).w = x.w ∘ ⇑F := by
  sorry

/-! ## The action on Teichmüller space -/

/-- Pulling back respects inseparability: inseparable representatives have equal boundary
values, hence so do their pullbacks. -/
theorem pull_mk_congr (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) :
    ∀ x y : TeichRep Γ₀, Inseparable x y →
      (SeparationQuotient.mk (x.pull F hF) : Teich Γ₀)
        = SeparationQuotient.mk (y.pull F hF) := by
  sorry

/-- The left action of the moduli group on Teichmüller space: `F` acts by pulling back
representatives along `F⁻¹`. -/
noncomputable def Teich.modSMul (F : modGroup Γ₀) (ξ : Teich Γ₀) : Teich Γ₀ :=
  SeparationQuotient.lift
    (fun x : TeichRep Γ₀ =>
      (SeparationQuotient.mk (x.pull (↑(F⁻¹)) (F⁻¹).2) : Teich Γ₀))
    (pull_mk_congr (↑(F⁻¹)) (F⁻¹).2) ξ

/-- The identity of the moduli group acts trivially: `x.w ∘ id = x.w`. -/
theorem Teich.modSMul_one (ξ : Teich Γ₀) : Teich.modSMul 1 ξ = ξ := by
  sorry

/-- Pull-by-inverse is a left action: `(F G)⁻¹ = G⁻¹ F⁻¹` composes contravariantly with the
contravariant pullback. -/
theorem Teich.modSMul_mul (F G : modGroup Γ₀) (ξ : Teich Γ₀) :
    Teich.modSMul (F * G) ξ = Teich.modSMul F (Teich.modSMul G ξ) := by
  sorry

/-- The moduli group acts on Teichmüller space. -/
noncomputable instance : MulAction (modGroup Γ₀) (Teich Γ₀) where
  smul := Teich.modSMul
  one_smul := Teich.modSMul_one
  mul_smul := Teich.modSMul_mul

/-- The action computed on classes of representatives. -/
theorem Teich.smul_mk (F : modGroup Γ₀) (x : TeichRep Γ₀) :
    F • Teich.mk x = Teich.mk (x.pull (↑(F⁻¹)) (F⁻¹).2) := by
  sorry

/-! ## Isometry of the action -/

/-- Pulling back both representatives along a moduli-group element does not change the
dilatation set: candidates are reindexed along the real line by the boundary values of `F`. -/
theorem dilatationSet_pull (F : ℂ ≃ₜ ℂ) (hF : F ∈ modGroup Γ₀) (x y : TeichRep Γ₀) :
    dilatationSet (x.pull F hF) (y.pull F hF) = dilatationSet x y := by
  sorry

/-- Each moduli-group element acts isometrically on Teichmüller space. -/
theorem Teich.isometry_smul_mod (F : modGroup Γ₀) :
    Isometry (fun ξ : Teich Γ₀ => F • ξ) := by
  sorry

/-- The moduli-group action on Teichmüller space is isometric. -/
instance : IsIsometricSMul (modGroup Γ₀) (Teich Γ₀) :=
  ⟨Teich.isometry_smul_mod⟩

/-- **Moduli space** over the base `Γ₀`: the orbit space of Teichmüller space under the
moduli group. -/
def Moduli (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quotient (MulAction.orbitRel (modGroup Γ₀) (Teich Γ₀))

end RiemannDynamics
