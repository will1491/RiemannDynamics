/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Algebra.Module.ZLattice.Basic
import RiemannDynamics.Uniformization.Trichotomy
import RiemannDynamics.Uniformization.HyperbolicSurface
import RiemannDynamics.Uniformization.Fuchsian
import RiemannDynamics.Uniformization.CoverCountable
import RiemannDynamics.Surface.WindingFunctionals
import RiemannDynamics.QC.MRMT.Uniqueness

/-!
# Hyperbolicity of the genus surface

The genus-`g` surface, `2 ≤ g`, is hyperbolic (`isHyperbolic_genusSurface`): the
uniformization trichotomy on its path cover leaves only the disc branch.

The sphere branch is excluded by a winding functional: a nonvanishing continuous `w : M → ℂ`
and a loop whose image winds nontrivially about `0` force infinitely many loop classes at
the basepoint, so the path cover has an infinite fiber and cannot be compact
(`sphere_exclusion_of_winding_functional`, `not_pathCover_sphere`).

The plane branch is excluded through the deck translations: a biholomorphism
`PathCover x₀ ≃ ℂ` conjugates each deck map to a fixed-point-free injective entire map,
hence a translation (`exists_deck_translation`), and the translation set is a discrete
additive subgroup (`discreteTopology_deck_translations`). If the translations lie on one
real line, the base cannot be compact (`no_compact_line_quotient`,
`plane_exclusion_of_line_deck`); otherwise the translations form a lattice of `ℤ`-rank two,
contradicting the surjection of the loop classes onto `ℤ³` (`not_pathCover_plane`).
-/

open Metric Topology Filter TopologicalSpace OnePoint
open scoped Manifold ContDiff unitInterval

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M]

/-! ## Sphere exclusion from infinitely many loop classes -/

/-- With infinitely many loop classes at the basepoint, the path cover is not compact:
the fiber over the basepoint injects the loop classes, while fibers meet compacta in
finite sets. -/
theorem not_compactSpace_pathCover_of_infinite (x₀ : M) [ChartedSpace ℂ M] [T2Space M]
    (h : Infinite (Path.Homotopic.Quotient x₀ x₀)) :
    ¬ CompactSpace (PathCover x₀) := by
  intro hcomp
  have hfin : (pathCoverProj x₀ ⁻¹' {x₀} ∩ Set.univ).Finite :=
    finite_fiber_inter_compact x₀ isCompact_univ x₀
  rw [Set.inter_univ] at hfin
  have hinf : (pathCoverProj x₀ ⁻¹' {x₀}).Infinite := by
    refine Set.infinite_of_injective_forall_mem
      (f := fun γ : Path.Homotopic.Quotient x₀ x₀ => (⟨x₀, γ⟩ : PathCover x₀)) ?_ ?_
    · intro γ δ hγδ
      injection hγδ
    · intro γ
      exact rfl
  exact hinf hfin

/-- **Sphere exclusion skeleton**: no homeomorphism from the path cover to the Riemann
sphere once the basepoint carries infinitely many loop classes. -/
theorem not_nonempty_homeomorph_sphere_of_infinite (x₀ : M) [ChartedSpace ℂ M]
    [T2Space M] (h : Infinite (Path.Homotopic.Quotient x₀ x₀)) :
    ¬ Nonempty (PathCover x₀ ≃ₜ ℂ̂) := by
  rintro ⟨e⟩
  exact not_compactSpace_pathCover_of_infinite x₀ h e.symm.compactSpace

/-- **Sphere exclusion from one winding functional**: a nonvanishing continuous
`w : M → ℂ` and a loop whose image winds nontrivially about `0` rule out the sphere as
the universal cover. -/
theorem sphere_exclusion_of_winding_functional (x₀ : M) [ChartedSpace ℂ M] [T2Space M]
    {w : M → ℂ} (hw : Continuous w) (hw0 : ∀ x, w x ≠ 0) (p₀ : Path x₀ x₀)
    (hwind : windingNumber ((p₀.map hw).toContinuousMap) 0 ≠ 0) :
    ¬ Nonempty (PathCover x₀ ≃ₜ ℂ̂) :=
  not_nonempty_homeomorph_sphere_of_infinite x₀
    (infinite_loopClasses_of_loopWinding_ne_zero x₀ hw hw0 ⟦p₀⟧ hwind)

/-- The biholomorphic form of the sphere exclusion. -/
theorem not_nonempty_diffeomorph_sphere_of_winding_functional (x₀ : M)
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] [T2Space M]
    {w : M → ℂ} (hw : Continuous w) (hw0 : ∀ x, w x ≠ 0) (p₀ : Path x₀ x₀)
    (hwind : windingNumber ((p₀.map hw).toContinuousMap) 0 ≠ 0) :
    ¬ Nonempty (PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  rintro ⟨e⟩
  exact sphere_exclusion_of_winding_functional x₀ hw hw0 p₀ hwind ⟨e.toHomeomorph⟩

/-! ## Plane exclusion, rank ≤ 1 branch -/

/-- **No compact quotient of the plane along a line**: a quotient map from `ℂ` onto a
compact space whose fibers displace along a fixed line `ℝ·b` is impossible — the
distance-to-the-line coordinate descends and is unbounded. -/
theorem no_compact_line_quotient {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : ℂ → X} (hq : IsQuotientMap f) (b : ℂ)
    (hfib : ∀ z w : ℂ, f z = f w → ∃ t : ℝ, w - z = t * b) : False := by
  -- Generic descent of a fiber-invariant unbounded continuous function.
  have descend : ∀ h : ℂ → ℝ, Continuous h → (∀ z w, f z = f w → h z = h w) →
      (∀ C : ℝ, ∃ z, C < h z) → False := by
    intro h hcont hconst hunb
    have hsurj := hq.surjective
    have hgf : ∀ z, h (hsurj (f z)).choose = h z := fun z =>
      hconst _ _ ((hsurj (f z)).choose_spec)
    have hgcont : Continuous fun x : X => h (hsurj x).choose := by
      rw [hq.continuous_iff]
      have hcomp : ((fun x : X => h (hsurj x).choose) ∘ f) = h := funext hgf
      rw [hcomp]
      exact hcont
    obtain ⟨C, hC⟩ := (isCompact_range hgcont).bddAbove
    obtain ⟨z, hz⟩ := hunb C
    have hle : h (hsurj (f z)).choose ≤ C := hC (Set.mem_range_self (f z))
    rw [hgf] at hle
    exact absurd hz (not_lt.mpr hle)
  by_cases hb : b = 0
  · -- Trivial fibers: `‖·‖` descends and is unbounded.
    refine descend (fun z => ‖z‖) continuous_norm ?_ ?_
    · intro z w hzw
      obtain ⟨t, ht⟩ := hfib z w hzw
      rw [hb, mul_zero, sub_eq_zero] at ht
      rw [ht]
    · intro C
      refine ⟨((|C| + 1 : ℝ) : ℂ), ?_⟩
      change C < ‖((|C| + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc C ≤ |C| := le_abs_self C
        _ < |C| + 1 := lt_add_one _
        _ ≤ |(|C| + 1)| := le_abs_self _
  · -- Line fibers: the component orthogonal to `b` descends and is unbounded.
    refine descend (fun z => |(z * (starRingEnd ℂ) b).im|) ?_ ?_ ?_
    · exact (Complex.continuous_im.comp (continuous_id.mul continuous_const)).abs
    · intro z w hzw
      change |(z * (starRingEnd ℂ) b).im| = |(w * (starRingEnd ℂ) b).im|
      obtain ⟨t, ht⟩ := hfib z w hzw
      have him : (w * (starRingEnd ℂ) b).im = (z * (starRingEnd ℂ) b).im := by
        have h2 : w * (starRingEnd ℂ) b - z * (starRingEnd ℂ) b
            = (t : ℂ) * (b * (starRingEnd ℂ) b) := by
          rw [← sub_mul, ht]
          ring
        have h3 := congrArg Complex.im h2
        rw [Complex.sub_im, Complex.mul_conj, ← Complex.ofReal_mul,
          Complex.ofReal_im] at h3
        linarith
      rw [him]
    · intro C
      have hs : (0 : ℝ) < Complex.normSq b := Complex.normSq_pos.mpr hb
      refine ⟨(((|C| + 1) / Complex.normSq b : ℝ) : ℂ) * Complex.I * b, ?_⟩
      change C < |((((|C| + 1) / Complex.normSq b : ℝ) : ℂ) * Complex.I * b *
        (starRingEnd ℂ) b).im|
      have hval : ((((|C| + 1) / Complex.normSq b : ℝ) : ℂ) * Complex.I * b *
          (starRingEnd ℂ) b) = ((|C| + 1 : ℝ) : ℂ) * Complex.I := by
        rw [mul_assoc, mul_assoc, Complex.mul_conj]
        rw [show ((((|C| + 1) / Complex.normSq b : ℝ) : ℂ) *
            (Complex.I * ((Complex.normSq b : ℝ) : ℂ)))
            = ((((|C| + 1) / Complex.normSq b) * Complex.normSq b : ℝ) : ℂ) *
              Complex.I by push_cast; ring]
        rw [div_mul_cancel₀ _ (ne_of_gt hs)]
      rw [hval]
      have him : (((|C| + 1 : ℝ) : ℂ) * Complex.I).im = |C| + 1 := by
        simp [Complex.mul_im]
      rw [him]
      calc C ≤ |C| := le_abs_self C
        _ < |C| + 1 := lt_add_one _
        _ ≤ |(|C| + 1)| := le_abs_self _

/-- The projection of the path cover is a quotient map. -/
theorem isQuotientMap_pathCoverProj (x₀ : M) [ChartedSpace ℂ M] [ConnectedSpace M] :
    IsQuotientMap (pathCoverProj x₀) := by
  haveI : LocPathConnectedSpace M := ChartedSpace.locPathConnectedSpace ℂ M
  haveI : PathConnectedSpace M := PathConnectedSpace.of_locPathConnectedSpace
  exact (pathCoverProj_isCoveringMap x₀).isQuotientMap
    fun y => ⟨⟨y, ⟦PathConnectedSpace.somePath x₀ y⟧⟩, rfl⟩

/-- Fibers of the path cover projection are exactly the deck orbits. -/
theorem pathCoverProj_eq_iff_deck (x₀ : M) [ChartedSpace ℂ M] (pc qc : PathCover x₀) :
    pathCoverProj x₀ pc = pathCoverProj x₀ qc
      ↔ ∃ γ : Path.Homotopic.Quotient x₀ x₀, pathCoverDeck x₀ γ pc = qc := by
  constructor
  · exact pathCoverDeck_transitive x₀ pc qc
  · rintro ⟨γ, rfl⟩
    exact (pathCoverProj_deck x₀ γ pc).symm

/-- **Plane exclusion, rank ≤ 1 branch**: if the path cover is homeomorphic to `ℂ` and
the transported deck displacements lie on a single line `ℝ·b`, the base cannot be
compact. (The rank-2 lattice/torus branch is excluded separately.) -/
theorem plane_exclusion_of_line_deck (x₀ : M) [ChartedSpace ℂ M] [ConnectedSpace M]
    [CompactSpace M] (e : PathCover x₀ ≃ₜ ℂ) (b : ℂ)
    (hdeck : ∀ pc qc : PathCover x₀, pathCoverProj x₀ pc = pathCoverProj x₀ qc →
      ∃ t : ℝ, e qc - e pc = t * b) : False := by
  have hq : IsQuotientMap (pathCoverProj x₀ ∘ e.symm) :=
    (isQuotientMap_pathCoverProj x₀).comp e.symm.isQuotientMap
  refine no_compact_line_quotient hq b ?_
  intro z w hzw
  obtain ⟨t, ht⟩ := hdeck (e.symm z) (e.symm w) hzw
  rw [e.apply_symm_apply, e.apply_symm_apply] at ht
  exact ⟨t, ht⟩

/-! ## Möbius fixed points and affine translations -/

/-- **Every Möbius transformation of the sphere has a fixed point**: for `c = 0` the
point `∞` is fixed; otherwise the fixed-point equation is a genuine quadratic, solved by
the fundamental theorem of algebra, and nondegeneracy guards the denominator. -/
theorem mobiusApply_exists_fixedPoint {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    ∃ z : ℂ̂, mobiusApply a b c d z = z := by
  by_cases hc : c = 0
  · exact ⟨∞, by rw [mobiusApply_infty, if_pos hc]⟩
  · have hdeg : 0 < (Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C (d - a) *
        Polynomial.X + Polynomial.C (-b)).degree := by
      rw [Polynomial.degree_quadratic hc]
      norm_num
    obtain ⟨x, hx⟩ := Complex.exists_root hdeg
    have hxeq : c * x ^ 2 + (d - a) * x + (-b) = 0 := by
      have hx' := hx
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at hx'
      exact hx'
    have hden : c * x + d ≠ 0 := by
      intro h0
      apply h
      have hb : a * x + b = 0 := by linear_combination x * h0 - hxeq
      linear_combination a * h0 - c * hb
    refine ⟨(x : ℂ̂), ?_⟩
    rw [mobiusApply_coe, if_neg hden, OnePoint.coe_eq_coe, div_eq_iff hden]
    linear_combination -hxeq

/-- A fixed-point-free affine map of the plane is a translation. -/
theorem affine_isTranslation_of_fixedPointFree {a b : ℂ}
    (h : ∀ z : ℂ, a * z + b ≠ z) : a = 1 := by
  by_contra ha
  have h1 : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr fun hcon => ha hcon.symm
  apply h (b / (1 - a))
  field_simp
  ring

/-! ## The exclusions on the genus surface -/

/-- **Sphere exclusion** for the genus surface, `2 ≤ g`: the first winding functional has
winding `1` along the zeroth edge loop. -/
theorem not_pathCover_sphere (g : ℕ) [NeZero g] (hg : 2 ≤ g) :
    ¬ Nonempty (PathCover (vertexPoint g) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ̂) := by
  obtain ⟨w, hw, hw0, hmat⟩ := exists_winding_functionals g hg
  refine not_nonempty_diffeomorph_sphere_of_winding_functional (vertexPoint g)
    (hw 0) (fun x => hw0 0 x) (edgeLoop g (![0, 1, 4] 0)) ?_
  have h00 : loopWinding (vertexPoint g) (hw 0) (fun x => hw0 0 x)
      ⟦edgeLoop g (![0, 1, 4] 0)⟧ = 1 := by
    rw [hmat 0 0, if_pos rfl]
  rw [loopWinding_mk] at h00
  rw [h00]
  exact one_ne_zero

/-- **Deck maps are translations** under a biholomorphism `PathCover x₀ ≃ ℂ`: each
conjugated deck map is an injective entire self-map of the plane, hence affine, and
fixed-point-free unless trivial, hence a translation; the translation constants are
additive in the loop class and injective. -/
theorem exists_deck_translation {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] [T2Space N] [ConnectedSpace N] (x₀ : N)
    (E : PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) :
    ∃ ψ : Path.Homotopic.Quotient x₀ x₀ → ℂ,
      (∀ γ δ : Path.Homotopic.Quotient x₀ x₀, ψ (γ.trans δ) = ψ γ + ψ δ) ∧
      Function.Injective ψ ∧
      ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
        E (pathCoverDeck x₀ γ pc) = E pc + ψ γ := by
  classical
  -- Each deck map conjugates to a translation of the plane.
  have hex : ∀ γ : Path.Homotopic.Quotient x₀ x₀, ∃ c : ℂ,
      ∀ pc : PathCover x₀, E (pathCoverDeck x₀ γ pc) = E pc + c := by
    intro γ
    obtain ⟨D, hD⟩ := exists_pathCoverDeck_diffeomorph x₀ γ
    set A := (E.symm.trans D).trans E
    have hAapp : ∀ z : ℂ, A z = E (pathCoverDeck x₀ γ (E.symm z)) := by
      intro z
      have h1 : A z = E (D (E.symm z)) := rfl
      rw [h1, hD]
    have hAsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (⇑A) := A.contMDiff
    have hAdiff : Differentiable ℂ (⇑A) := hAsm.contDiff.differentiable (by simp)
    have hAinj : Function.Injective (⇑A) := A.toEquiv.injective
    obtain ⟨a, c, ha0, hAeq⟩ := eq_affine_of_differentiable_of_injective hAdiff hAinj
    have ha1 : a = 1 := by
      by_cases hfix : ∃ z : ℂ, A z = z
      · obtain ⟨z, hz⟩ := hfix
        have h2 : pathCoverDeck x₀ γ (E.symm z) = E.symm z := by
          apply E.toEquiv.injective
          change E (pathCoverDeck x₀ γ (E.symm z)) = E (E.symm z)
          rw [← hAapp z, hz, E.apply_symm_apply]
        have hid := pathCoverDeck_id_of_fixed x₀ γ h2
        have hAid : ∀ v : ℂ, A v = v := by
          intro v
          rw [hAapp v, hid (E.symm v), E.apply_symm_apply]
        have e0 : a * 0 + c = 0 := (congrFun hAeq.symm 0).trans (hAid 0)
        have e1 : a * 1 + c = 1 := (congrFun hAeq.symm 1).trans (hAid 1)
        linear_combination e1 - e0
      · push Not at hfix
        refine affine_isTranslation_of_fixedPointFree (a := a) (b := c) ?_
        intro z heq
        exact hfix z ((congrFun hAeq z).trans heq)
    refine ⟨c, fun pc => ?_⟩
    have h4 : A (E pc) = a * E pc + c := by rw [hAeq]
    have h3 : A (E pc) = E (pathCoverDeck x₀ γ pc) := by
      rw [hAapp (E pc), E.symm_apply_apply]
    rw [← h3, h4, ha1, one_mul]
  choose ψ hψ using hex
  -- Additivity of the translation constants.
  have hadd : ∀ γ δ : Path.Homotopic.Quotient x₀ x₀, ψ (γ.trans δ) = ψ γ + ψ δ := by
    intro γ δ
    have hcomp : pathCoverDeck x₀ γ (pathCoverDeck x₀ δ (pathCoverBase x₀))
        = pathCoverDeck x₀ (γ.trans δ) (pathCoverBase x₀) :=
      congrArg (PathCover.mk (pathCoverBase x₀).pt)
        (Path.Homotopic.Quotient.trans_assoc γ δ (pathCoverBase x₀).cls).symm
    have h2 : E (pathCoverDeck x₀ γ (pathCoverDeck x₀ δ (pathCoverBase x₀)))
        = E (pathCoverBase x₀) + ψ δ + ψ γ := by
      rw [hψ γ (pathCoverDeck x₀ δ (pathCoverBase x₀)), hψ δ (pathCoverBase x₀)]
    rw [hcomp, hψ (γ.trans δ) (pathCoverBase x₀)] at h2
    have h3 : ψ (γ.trans δ) = ψ δ + ψ γ := by
      rw [add_assoc] at h2
      exact add_left_cancel h2
    rw [h3, add_comm]
  -- Injectivity of the translation constants.
  have hinj : Function.Injective ψ := by
    intro γ δ h
    have h1 : E (pathCoverDeck x₀ γ (pathCoverBase x₀))
        = E (pathCoverDeck x₀ δ (pathCoverBase x₀)) := by
      rw [hψ γ (pathCoverBase x₀), hψ δ (pathCoverBase x₀), h]
    have h2 : pathCoverDeck x₀ γ (pathCoverBase x₀)
        = pathCoverDeck x₀ δ (pathCoverBase x₀) := E.toEquiv.injective h1
    have h' : (⟨x₀, γ.trans (⟦Path.refl x₀⟧ : Path.Homotopic.Quotient x₀ x₀)⟩ :
          PathCover x₀)
        = ⟨x₀, δ.trans (⟦Path.refl x₀⟧ : Path.Homotopic.Quotient x₀ x₀)⟩ := h2
    rw [PathCover.mk.injEq] at h'
    have h3 : γ.trans (Path.Homotopic.Quotient.refl x₀)
        = δ.trans (Path.Homotopic.Quotient.refl x₀) := eq_of_heq h'.2
    calc γ = γ.trans (Path.Homotopic.Quotient.refl x₀) :=
          (Path.Homotopic.Quotient.trans_refl γ).symm
      _ = δ.trans (Path.Homotopic.Quotient.refl x₀) := h3
      _ = δ := Path.Homotopic.Quotient.trans_refl δ
  exact ⟨ψ, hadd, hinj, fun γ pc => hψ γ pc⟩

/-- **Discreteness of the deck translations**: the translation constants are the fiber over
the basepoint transported through the homeomorphism and a translation, and fibers of a
covering map are discrete. -/
theorem discreteTopology_deck_translations {N : Type*} [TopologicalSpace N]
    [ChartedSpace ℂ N] [T2Space N] [ConnectedSpace N] (x₀ : N)
    (E : PathCover x₀ ≃ₜ ℂ) (ψ : Path.Homotopic.Quotient x₀ x₀ → ℂ)
    (hdeck : ∀ (γ : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
      E (pathCoverDeck x₀ γ pc) = E pc + ψ γ) :
    DiscreteTopology ↥(Set.range ψ) := by
  classical
  haveI hfib : DiscreteTopology ↥(pathCoverProj x₀ ⁻¹' {x₀}) :=
    (pathCoverProj_isCoveringMap x₀ x₀).1
  have hmem : ∀ τ : ↥(Set.range ψ),
      E.symm ((τ : ℂ) + E (pathCoverBase x₀)) ∈ pathCoverProj x₀ ⁻¹' {x₀} := by
    rintro ⟨τ, γ, rfl⟩
    have h1 : ψ γ + E (pathCoverBase x₀) = E (pathCoverDeck x₀ γ (pathCoverBase x₀)) := by
      rw [hdeck γ (pathCoverBase x₀), add_comm]
    change E.symm (ψ γ + E (pathCoverBase x₀)) ∈ pathCoverProj x₀ ⁻¹' {x₀}
    rw [Set.mem_preimage, Set.mem_singleton_iff, h1, E.symm_apply_apply,
      pathCoverProj_deck]
    rfl
  have hcont : Continuous fun τ : ↥(Set.range ψ) =>
      (⟨E.symm ((τ : ℂ) + E (pathCoverBase x₀)), hmem τ⟩ :
        ↥(pathCoverProj x₀ ⁻¹' {x₀})) := by
    refine Continuous.subtype_mk ?_ _
    exact E.symm.continuous.comp (continuous_subtype_val.add continuous_const)
  have hinj : Function.Injective fun τ : ↥(Set.range ψ) =>
      (⟨E.symm ((τ : ℂ) + E (pathCoverBase x₀)), hmem τ⟩ :
        ↥(pathCoverProj x₀ ⁻¹' {x₀})) := by
    intro τ τ₂ h
    have h1 : E.symm ((τ : ℂ) + E (pathCoverBase x₀))
        = E.symm ((τ₂ : ℂ) + E (pathCoverBase x₀)) := congrArg Subtype.val h
    have h2 := E.symm.injective h1
    exact Subtype.ext (add_right_cancel h2)
  exact DiscreteTopology.of_continuous_injective hcont hinj

/-- **Plane exclusion** for the genus surface, `2 ≤ g`: if the deck translations lie on one
real line the base cannot be compact, and otherwise they form a `ℤ`-lattice of rank two,
against the surjection of the loop classes onto `ℤ³`. -/
theorem not_pathCover_plane (g : ℕ) [NeZero g] (hg : 2 ≤ g) :
    ¬ Nonempty (PathCover (vertexPoint g) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ℂ) := by
  classical
  rintro ⟨E⟩
  obtain ⟨ψ, hadd, hinj, hdeck⟩ := exists_deck_translation (vertexPoint g) E
  by_cases hline : ∃ b : ℂ, ∀ γ : Path.Homotopic.Quotient (vertexPoint g) (vertexPoint g),
      ∃ t : ℝ, ψ γ = t * b
  · -- Rank ≤ 1: the translations lie on one real line.
    obtain ⟨b, hb⟩ := hline
    refine plane_exclusion_of_line_deck (vertexPoint g) E.toHomeomorph b ?_
    intro pc qc hpq
    obtain ⟨γ, rfl⟩ := (pathCoverProj_eq_iff_deck (vertexPoint g) pc qc).mp hpq
    obtain ⟨t, ht⟩ := hb γ
    refine ⟨t, ?_⟩
    change E (pathCoverDeck (vertexPoint g) γ pc) - E pc = (t : ℂ) * b
    rw [hdeck γ pc, ht]
    ring
  · -- Rank 2: the translations contain an `ℝ`-independent pair, hence form a lattice
    -- of `ℤ`-rank two, against the surjection onto `ℤ³`.
    push Not at hline
    obtain ⟨γ₁, hγ₁⟩ := hline 0
    have hb0 : ψ γ₁ ≠ 0 := by
      have h := hγ₁ 0
      rwa [Complex.ofReal_zero, zero_mul] at h
    obtain ⟨γ₂, hγ₂⟩ := hline (ψ γ₁)
    -- The translation constants of the identity and inverse classes.
    have hψrefl : ψ (Path.Homotopic.Quotient.refl (vertexPoint g)) = 0 := by
      have h := hadd (Path.Homotopic.Quotient.refl (vertexPoint g))
        (Path.Homotopic.Quotient.refl (vertexPoint g))
      rw [Path.Homotopic.Quotient.refl_trans] at h
      have h2 : ψ (Path.Homotopic.Quotient.refl (vertexPoint g)) + 0
          = ψ (Path.Homotopic.Quotient.refl (vertexPoint g))
            + ψ (Path.Homotopic.Quotient.refl (vertexPoint g)) := by
        rw [add_zero]
        exact h
      exact (add_left_cancel h2).symm
    have hψsymm : ∀ γ : Path.Homotopic.Quotient (vertexPoint g) (vertexPoint g),
        ψ γ.symm = -ψ γ := by
      intro γ
      have h := hadd γ γ.symm
      rw [Path.Homotopic.Quotient.trans_symm, hψrefl] at h
      linear_combination h.symm
    -- The translations as a `ℤ`-submodule of the plane.
    set L : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule
      { carrier := Set.range ψ
        add_mem' := by
          rintro a b ⟨γ, rfl⟩ ⟨δ, rfl⟩
          exact ⟨γ.trans δ, hadd γ δ⟩
        zero_mem' := ⟨Path.Homotopic.Quotient.refl (vertexPoint g), hψrefl⟩
        neg_mem' := by
          rintro a ⟨γ, rfl⟩
          exact ⟨γ.symm, hψsymm γ⟩ }
    have hset : (L : Set ℂ) = Set.range ψ := AddSubgroup.coe_toIntSubmodule _
    have hmemL : ∀ z : ℂ, z ∈ L ↔ z ∈ Set.range ψ := by
      intro z
      rw [← SetLike.mem_coe, hset]
    -- Discreteness, from the discreteness of the fiber.
    haveI hdiscR : DiscreteTopology ↥(Set.range ψ) :=
      discreteTopology_deck_translations (vertexPoint g) E.toHomeomorph ψ
        (fun γ pc => hdeck γ pc)
    haveI hdiscL : DiscreteTopology ↥L :=
      DiscreteTopology.of_continuous_injective (β := ↥(Set.range ψ))
        (f := fun x => ⟨(x : ℂ), (hmemL x).mp x.2⟩)
        (Continuous.subtype_mk continuous_subtype_val _)
        (fun x y h => Subtype.ext (congrArg Subtype.val h))
    -- The two independent translations span the plane.
    have htC : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ≠ 0 := fun t ht =>
      Complex.ofReal_ne_zero.mpr ht
    have hli : LinearIndependent ℝ ![ψ γ₁, ψ γ₂] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        rcases smul_eq_zero.mp hst with hs | hb'
        · exact ⟨hs, rfl⟩
        · exact absurd hb' hb0
      · exfalso
        have htC' : (t : ℂ) ≠ 0 := htC t ht
        have hst' : (s : ℂ) * ψ γ₁ + (t : ℂ) * ψ γ₂ = 0 := by
          rw [← Complex.real_smul, ← Complex.real_smul]
          exact hst
        apply hγ₂ (-(s / t))
        apply mul_left_cancel₀ htC'
        have h1 : (t : ℂ) * ((-(s / t) : ℝ) : ℂ) = -(s : ℂ) := by
          push_cast
          field_simp
        rw [← mul_assoc, h1]
        linear_combination hst'
    have h2 : Submodule.span ℝ (Set.range ![ψ γ₁, ψ γ₂]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hli, Complex.finrank_real_complex, Fintype.card_fin]
    have hsub : Set.range ![ψ γ₁, ψ γ₂] ⊆ (L : Set ℂ) := by
      rw [hset]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact ⟨γ₁, rfl⟩
      · exact ⟨γ₂, rfl⟩
    have hspan : Submodule.span ℝ (L : Set ℂ) = ⊤ := by
      refine le_antisymm le_top ?_
      calc (⊤ : Submodule ℝ ℂ) = Submodule.span ℝ (Set.range ![ψ γ₁, ψ γ₂]) := h2.symm
        _ ≤ Submodule.span ℝ (L : Set ℂ) := Submodule.span_mono hsub
    haveI : IsZLattice ℝ L := ⟨hspan⟩
    have hrk : Module.finrank ℤ ↥L = 2 :=
      (ZLattice.rank ℝ L).trans Complex.finrank_real_complex
    -- The transported surjection onto `ℤ³`.
    obtain ⟨μ, hμadd, hμsurj⟩ := exists_pi1_surjection_zpow3 g hg
    have hLmem : ∀ x : ↥L, ∃ γ, ψ γ = (x : ℂ) := fun x => (hmemL x).mp x.2
    choose γof hγof using hLmem
    have hνadd : ∀ τ τ₂ : ↥L, μ (γof (τ + τ₂)) = μ (γof τ) + μ (γof τ₂) := by
      intro τ τ₂
      have h1 : ψ (γof (τ + τ₂)) = ψ ((γof τ).trans (γof τ₂)) := by
        rw [hγof (τ + τ₂), hadd (γof τ) (γof τ₂), hγof τ, hγof τ₂]
        push_cast
        ring
      rw [hinj h1, hμadd]
    set ν : ↥L →ₗ[ℤ] (Fin 3 → ℤ) :=
      (AddMonoidHom.mk' (fun τ : ↥L => μ (γof τ)) hνadd).toIntLinearMap
    have hνsurj : Function.Surjective ν := by
      intro v
      obtain ⟨γ, hγ⟩ := hμsurj v
      have hγL : ψ γ ∈ L := (hmemL (ψ γ)).mpr ⟨γ, rfl⟩
      refine ⟨⟨ψ γ, hγL⟩, ?_⟩
      have h1 : ψ (γof ⟨ψ γ, hγL⟩) = ψ γ := hγof ⟨ψ γ, hγL⟩
      have h2 : ν ⟨ψ γ, hγL⟩ = μ (γof ⟨ψ γ, hγL⟩) := rfl
      rw [h2, hinj h1, hγ]
    -- Rank contradiction: a rank-two lattice cannot surject onto `ℤ³`.
    haveI : Module.Finite ℤ ↥L := ZLattice.module_finite ℝ L
    have hle : Module.finrank ℤ ↥(LinearMap.range ν) ≤ Module.finrank ℤ ↥L :=
      ν.finrank_range_le
    rw [LinearMap.range_eq_top.mpr hνsurj, finrank_top, Module.finrank_pi,
      Fintype.card_fin, hrk] at hle
    omega

/-- **The genus surface is hyperbolic** for `2 ≤ g`: the uniformization trichotomy on the
path cover leaves only the disc branch. -/
theorem isHyperbolic_genusSurface (g : ℕ) [NeZero g] (hg : 2 ≤ g) :
    IsHyperbolic (GenusSurface g) := by
  haveI : T2Space (PathCover (vertexPoint g)) := t2space_pathCover (vertexPoint g)
  haveI : PathConnectedSpace (PathCover (vertexPoint g)) :=
    pathConnectedSpace_pathCover (vertexPoint g)
  haveI : ConnectedSpace (PathCover (vertexPoint g)) := PathConnectedSpace.connectedSpace
  haveI : SimplyConnectedSpace (PathCover (vertexPoint g)) :=
    simplyConnectedSpace_pathCover (vertexPoint g)
  haveI : SecondCountableTopology (PathCover (vertexPoint g)) :=
    secondCountableTopology_pathCover (vertexPoint g)
  rcases uniformization_trichotomy (PathCover (vertexPoint g)) with h | h | h
  · exact isHyperbolic_of_nonempty_diffeomorph_disc h
  · exact absurd h (not_pathCover_plane g hg)
  · exact absurd h (not_pathCover_sphere g hg)

end RiemannDynamics
