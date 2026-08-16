/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.HyperbolicSurface

/-!
# Fuchsian models of hyperbolic surfaces

Every hyperbolic surface is the quotient of the upper half plane by a
Fuchsian group: the universal path cover uniformizes to the disc, the deck
transformations become disc automorphisms, every disc automorphism is a
Möbius map and corresponds through the Cayley transform to an element of
`SL(2, ℝ)` acting on the upper half plane, and the covering projection
exhibits the surface as the orbit space of the resulting subgroup, which
acts properly discontinuously with trivial stabilizers modulo center.

Main declarations:
* `upperHalfOpens`, `toUpperHalfPlane` — the upper half plane as an open
  plane domain, bridged to `UpperHalfPlane`;
* `IsFuchsianGroup` — a subgroup of `SL(2, ℝ)` acting properly
  discontinuously on the upper half plane;
* `pathCoverDeck_id_of_fixed` — a deck transformation with a fixed point is
  the identity;
* `exists_mobius_of_diffeomorph_unitDisc` — disc automorphisms are Möbius;
* `exists_sl2_of_diffeomorph_unitDisc` — disc automorphisms act as
  `SL(2, ℝ)` through the Cayley transform;
* `exists_fuchsian_model` — the Fuchsian uniformization: a holomorphic
  covering of the surface by the upper half plane whose fibers are the
  orbits of a Fuchsian group with central stabilizers.
-/

open Metric Topology Filter TopologicalSpace
open scoped Manifold ContDiff unitInterval

namespace RiemannDynamics

/-- The upper half plane, as an open set of the plane carrying the
charted-space structure of an open submanifold. -/
def upperHalfOpens : Opens ℂ :=
  ⟨{z | 0 < z.im}, isOpen_lt continuous_const Complex.continuous_im⟩

/-- The identification of the open-submanifold upper half plane with
`UpperHalfPlane`. -/
def toUpperHalfPlane (z : ↥upperHalfOpens) : UpperHalfPlane := ⟨(z : ℂ), z.2⟩

/-- A **Fuchsian group**: a subgroup of `SL(2, ℝ)` acting properly
discontinuously on the upper half plane. -/
def IsFuchsianGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Prop :=
  ProperlyDiscontinuousSMul Γ UpperHalfPlane

/-- **A deck transformation with a fixed point is the identity**: the loop
class is cancelled by the fixed path class, and precomposition by the trivial
class fixes every point. -/
theorem pathCoverDeck_id_of_fixed {M : Type*} [TopologicalSpace M] (x₀ : M)
    (γ : Path.Homotopic.Quotient x₀ x₀) {pc : PathCover x₀}
    (h : pathCoverDeck x₀ γ pc = pc) :
    ∀ qc : PathCover x₀, pathCoverDeck x₀ γ qc = qc := by
  intro qc
  have h' : (⟨pc.pt, γ.trans pc.cls⟩ : PathCover x₀) = ⟨pc.pt, pc.cls⟩ := h
  rw [PathCover.mk.injEq] at h'
  have h1 : γ.trans pc.cls = pc.cls := eq_of_heq h'.2
  have hγ : γ = Path.Homotopic.Quotient.refl x₀ :=
    calc γ = γ.trans (Path.Homotopic.Quotient.refl x₀) :=
          (Path.Homotopic.Quotient.trans_refl γ).symm
      _ = γ.trans (pc.cls.trans pc.cls.symm) := by
          rw [Path.Homotopic.Quotient.trans_symm]
      _ = (γ.trans pc.cls).trans pc.cls.symm :=
          (Path.Homotopic.Quotient.trans_assoc γ pc.cls pc.cls.symm).symm
      _ = pc.cls.trans pc.cls.symm := by rw [h1]
      _ = Path.Homotopic.Quotient.refl x₀ := Path.Homotopic.Quotient.trans_symm pc.cls
  rw [hγ]
  change (⟨qc.pt, (Path.Homotopic.Quotient.refl x₀).trans qc.cls⟩ : PathCover x₀) = qc
  exact congrArg (PathCover.mk qc.pt) (Path.Homotopic.Quotient.refl_trans qc.cls)

/-- **Disc automorphisms are Möbius**: a biholomorphism of the unit disc is a
rotation composed with a disc Möbius map, by the Schwarz lemma applied to the
composition fixing the origin and to its inverse. -/
theorem exists_mobius_of_diffeomorph_unitDisc
    (e : ↥unitDiscOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) :
    ∃ η w : ℂ, ‖η‖ = 1 ∧ w ∈ ball (0 : ℂ) 1 ∧
      ∀ z : ↥unitDiscOpens, (e z : ℂ) = η * mobiusDisk w (z : ℂ) := by
  classical
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- The point sent to the origin by `e`.
  set p0 : ↥unitDiscOpens := (⟨0, h0⟩ : ↥unitDiscOpens) with hp0def
  set w' : ℂ := ((e.symm p0 : ↥unitDiscOpens) : ℂ) with hw'def
  have hw' : w' ∈ ball (0 : ℂ) 1 := (e.symm p0).2
  have hnw' : -w' ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.mp hw'
  -- Plane reading of a disc diffeomorphism is holomorphic on the ball.
  have key : ∀ f : ↥unitDiscOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens,
      DifferentiableOn ℂ
        (fun z : ℂ => if hz : z ∈ ball (0 : ℂ) 1 then (f ⟨z, hz⟩ : ℂ) else 0)
        (ball (0 : ℂ) 1) := by
    intro f z₀ hz₀
    have hval : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun q : ↥unitDiscOpens => (f q : ℂ)) :=
      contMDiff_subtype_val.comp f.contMDiff
    -- Local analytic section of the inclusion of the ball.
    set F : ℂ → ↥unitDiscOpens :=
      fun p => if hp : p ∈ ball (0 : ℂ) 1 then (⟨p, hp⟩ : ↥unitDiscOpens) else ⟨0, h0⟩
      with hFdef
    have hFval : ∀ p ∈ ball (0 : ℂ) 1, (F p : ℂ) = p := by
      intro p hp
      simp only [hFdef]
      rw [dif_pos hp]
    have h_analytic : AnalyticAt ℂ (fun p : ℂ => (F p : ℂ)) z₀ := by
      refine analyticAt_id.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hz₀] with p hp
      exact (hFval p hp).symm
    have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F z₀ := by
      rw [contMDiffAt_iff]
      constructor
      · exact IsInducing.subtypeVal.continuousAt_iff.mpr h_analytic.continuousAt
      · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
          Function.comp_id, modelWithCornersSelf_coe, Set.range_id, id_eq]
        rw [contDiffWithinAt_univ]
        exact h_analytic.contDiffAt
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        ((fun q : ↥unitDiscOpens => (f q : ℂ)) ∘ F) z₀ :=
      (hval.contMDiffAt).comp z₀ hF
    have h3 : ContDiffAt ℂ ω ((fun q : ↥unitDiscOpens => (f q : ℂ)) ∘ F) z₀ :=
      contMDiffAt_iff_contDiffAt.mp hcomp
    have hev : (fun z : ℂ => if hz : z ∈ ball (0 : ℂ) 1 then (f ⟨z, hz⟩ : ℂ) else 0)
        =ᶠ[𝓝 z₀] ((fun q : ↥unitDiscOpens => (f q : ℂ)) ∘ F) := by
      filter_upwards [isOpen_ball.mem_nhds hz₀] with p hp
      simp only [Function.comp_apply, hFdef]
      rw [dif_pos hp, dif_pos hp]
    exact (h3.analyticAt.differentiableAt.congr_of_eventuallyEq
      hev).differentiableWithinAt
  -- The plane readings of `e` and `e.symm`.
  set E : ℂ → ℂ :=
    fun z => if hz : z ∈ ball (0 : ℂ) 1 then (e ⟨z, hz⟩ : ℂ) else 0 with hEdef
  set E' : ℂ → ℂ :=
    fun z => if hz : z ∈ ball (0 : ℂ) 1 then (e.symm ⟨z, hz⟩ : ℂ) else 0 with hE'def
  have hEdiff : DifferentiableOn ℂ E (ball (0 : ℂ) 1) := key e
  have hE'diff : DifferentiableOn ℂ E' (ball (0 : ℂ) 1) := key e.symm
  have hEval : ∀ q : ↥unitDiscOpens, E (q : ℂ) = (e q : ℂ) := by
    intro q
    have hq : (q : ℂ) ∈ ball (0 : ℂ) 1 := q.2
    simp only [hEdef]
    rw [dif_pos hq]
  have hEmaps : Set.MapsTo E (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hEdef]
    rw [dif_pos hz]
    exact (e ⟨z, hz⟩).2
  have hE'maps : Set.MapsTo E' (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hE'def]
    rw [dif_pos hz]
    exact (e.symm ⟨z, hz⟩).2
  -- `E'` inverts `E` on the ball.
  have hE'E : ∀ u ∈ ball (0 : ℂ) 1, E' (E u) = u := by
    intro u hu
    have h1 : E u = (e ⟨u, hu⟩ : ℂ) := by simp only [hEdef]; rw [dif_pos hu]
    have h2 : E u ∈ ball (0 : ℂ) 1 := hEmaps hu
    simp only [hE'def]
    rw [dif_pos h2]
    have h3 : (⟨E u, h2⟩ : ↥unitDiscOpens) = e ⟨u, hu⟩ := Subtype.ext h1
    rw [h3, e.symm_apply_apply]
  -- Möbius self-maps of the ball.
  have hMmaps : Set.MapsTo (mobiusDisk (-w')) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun z hz => mobiusDisk_mapsTo hz hnw'
  have hM'maps : Set.MapsTo (mobiusDisk w') (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun z hz => mobiusDisk_mapsTo hz hw'
  -- Normalized composition and its inverse.
  set φ : ℂ → ℂ := fun z => E (mobiusDisk (-w') z) with hφdef
  set ψ : ℂ → ℂ := fun z => mobiusDisk w' (E' z) with hψdef
  have hφdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) := by
    rw [hφdef]
    exact hEdiff.comp (mobiusDisk_differentiableOn hnw') hMmaps
  have hψdiff : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1) := by
    rw [hψdef]
    exact (mobiusDisk_differentiableOn hw').comp hE'diff hE'maps
  have hφmaps : Set.MapsTo φ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hφdef]
    exact hEmaps (hMmaps hz)
  have hψmaps : Set.MapsTo ψ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hψdef]
    exact hM'maps (hE'maps hz)
  have hφ0 : φ 0 = 0 := by
    simp only [hφdef, mobiusDisk_neg_apply_zero]
    have h1 : E w' = (e ⟨w', hw'⟩ : ℂ) := by simp only [hEdef]; rw [dif_pos hw']
    rw [h1]
    have h2 : (⟨w', hw'⟩ : ↥unitDiscOpens) = e.symm p0 := Subtype.ext hw'def
    rw [h2, e.apply_symm_apply, hp0def]
  have hψ0 : ψ 0 = 0 := by
    simp only [hψdef]
    have h1 : E' 0 = (e.symm ⟨0, h0⟩ : ℂ) := by simp only [hE'def]; rw [dif_pos h0]
    rw [h1, ← hp0def, ← hw'def, mobiusDisk_self]
  -- `ψ` inverts `φ` on the ball.
  have hψφ : ∀ z ∈ ball (0 : ℂ) 1, ψ (φ z) = z := by
    intro z hz
    have hu : mobiusDisk (-w') z ∈ ball (0 : ℂ) 1 := hMmaps hz
    simp only [hψdef, hφdef]
    rw [hE'E _ hu]
    have h1 := mobiusDisk_neg_mobiusDisk hz hnw'
    rwa [neg_neg] at h1
  -- Schwarz in both directions: `φ` is a norm isometry.
  have hφle : ∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ ≤ ‖z‖ := fun z hz =>
    Complex.norm_le_norm_of_mapsTo_ball hφdiff
      (fun u hu => ball_subset_closedBall (hφmaps hu)) hφ0 (mem_ball_zero_iff.mp hz)
  have hψle : ∀ z ∈ ball (0 : ℂ) 1, ‖ψ z‖ ≤ ‖z‖ := fun z hz =>
    Complex.norm_le_norm_of_mapsTo_ball hψdiff
      (fun u hu => ball_subset_closedBall (hψmaps hu)) hψ0 (mem_ball_zero_iff.mp hz)
  have hφnorm : ∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ = ‖z‖ := by
    intro z hz
    refine le_antisymm (hφle z hz) ?_
    have h1 := hψle (φ z) (hφmaps hz)
    rwa [hψφ z hz] at h1
  -- The slope at a fixed interior point has unit norm.
  have hz₀mem : (2⁻¹ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv, Complex.norm_ofNat]
    norm_num
  have hz₀ne : (2⁻¹ : ℂ) ≠ 0 := by norm_num
  have hn2 : ‖(2⁻¹ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz₀ne
  have hnds : ‖dslope φ 0 (2⁻¹ : ℂ)‖ = 1 := by
    rw [dslope_of_ne φ hz₀ne, slope_def_module, hφ0, sub_zero, sub_zero, norm_smul,
      norm_inv, hφnorm _ hz₀mem]
    exact inv_mul_cancel₀ hn2
  -- Equality case of the Schwarz lemma: `φ` is a rotation.
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div (c := (0 : ℂ))
    (R₁ := 1) (R₂ := 1) hφdiff
    (by
      rw [hφ0]
      exact fun u hu => ball_subset_closedBall (hφmaps hu))
    hz₀mem (by rw [hnds]; norm_num)
  refine ⟨dslope φ 0 (2⁻¹ : ℂ), w', hnds, hw', ?_⟩
  intro z
  have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 := z.2
  have hu : mobiusDisk w' (z : ℂ) ∈ ball (0 : ℂ) 1 := hM'maps hz
  have h1 := haff hu
  simp only [hφ0, zero_add, sub_zero, smul_eq_mul] at h1
  have h2 : mobiusDisk (-w') (mobiusDisk w' (z : ℂ)) = (z : ℂ) :=
    mobiusDisk_neg_mobiusDisk hz hw'
  have h3 : φ (mobiusDisk w' (z : ℂ)) = (e z : ℂ) := by
    simp only [hφdef]
    rw [h2]
    exact hEval z
  rw [h3] at h1
  rw [h1]
  exact mul_comm _ _

/-- **Disc automorphisms act as `SL(2, ℝ)` on the upper half plane**: the
Cayley conjugate of a rotation-Möbius automorphism of the disc is a real
fractional linear map of positive determinant, normalized to determinant
one. -/
theorem exists_sl2_of_diffeomorph_unitDisc
    (e : ↥unitDiscOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ↥unitDiscOpens, ∃ τ τ' : UpperHalfPlane,
        (τ : ℂ) = cayleyToHalfPlane (z : ℂ) ∧
        (τ' : ℂ) = cayleyToHalfPlane ((e z : ℂ)) ∧ A • τ = τ' := by
  obtain ⟨η, w, hη, hw, he⟩ := exists_mobius_of_diffeomorph_unitDisc e
  -- A square root `u` of the rotation `η`, with `‖u‖ = 1`.
  set u : ℂ := Complex.exp ((η.arg / 2 : ℝ) * Complex.I) with hu_def
  have hu_norm : ‖u‖ = 1 := by rw [hu_def]; exact Complex.norm_exp_ofReal_mul_I _
  have hu_ne : u ≠ 0 := by rw [hu_def]; exact Complex.exp_ne_zero _
  have hu_sq : u ^ 2 = η := by
    rw [hu_def, ← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * ((η.arg / 2 : ℝ) * Complex.I) = (η.arg : ℝ) * Complex.I by
        push_cast; ring]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I η]
    rw [hη, Complex.ofReal_one, one_mul]
  have hcu_inv : (starRingEnd ℂ) u = u⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm, Complex.mul_conj', hu_norm]
    norm_num
  -- The scaling factor `s = √(1 - ‖w‖²)`.
  have hw1 : ‖w‖ < 1 := by
    have h := hw
    rwa [mem_ball, dist_zero_right] at h
  have hs2pos : (0 : ℝ) < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  set s : ℝ := Real.sqrt (1 - ‖w‖ ^ 2) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr hs2pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = 1 - ‖w‖ ^ 2 := by rw [hs_def]; exact Real.sq_sqrt hs2pos.le
  -- The two complex seeds of the matrix entries.
  set x : ℂ := u * (1 - w) with hx_def
  set y : ℂ := u * (1 + w) with hy_def
  set a : ℝ := x.re / s with ha_def
  set b : ℝ := y.im / s with hb_def
  set c : ℝ := (-x.im) / s with hc_def
  set d : ℝ := y.re / s with hd_def
  have haR : a * s = x.re := by rw [ha_def]; exact div_mul_cancel₀ x.re hs_ne
  have hbR : b * s = y.im := by rw [hb_def]; exact div_mul_cancel₀ y.im hs_ne
  have hcR : c * s = -x.im := by rw [hc_def]; exact div_mul_cancel₀ (-x.im) hs_ne
  have hdR : d * s = y.re := by rw [hd_def]; exact div_mul_cancel₀ y.re hs_ne
  have hcx : (starRingEnd ℂ) x = u⁻¹ * (1 - (starRingEnd ℂ) w) := by
    rw [hx_def, map_mul, map_sub, map_one, hcu_inv]
  have hcy : (starRingEnd ℂ) y = u⁻¹ * (1 + (starRingEnd ℂ) w) := by
    rw [hy_def, map_mul, map_add, map_one, hcu_inv]
  -- Complex bridges for the four real entries.
  have haxC : (a : ℂ) * (s : ℂ) * 2 = x + (starRingEnd ℂ) x := by
    rw [Complex.add_conj, ← haR]; push_cast; ring
  have hdxC : (d : ℂ) * (s : ℂ) * 2 = y + (starRingEnd ℂ) y := by
    rw [Complex.add_conj, ← hdR]; push_cast; ring
  have hbxC : (b : ℂ) * (s : ℂ) * 2 = -Complex.I * (y - (starRingEnd ℂ) y) := by
    rw [Complex.sub_conj, ← hbR]; push_cast
    linear_combination (2 * (b : ℂ) * (s : ℂ)) * Complex.I_sq
  have hcxC : (c : ℂ) * (s : ℂ) * 2 = Complex.I * (x - (starRingEnd ℂ) x) := by
    rw [Complex.sub_conj]
    have hxim : x.im = -(c * s) := by rw [hcR, neg_neg]
    rw [hxim]; push_cast
    linear_combination (2 * (c : ℂ) * (s : ℂ)) * Complex.I_sq
  -- Determinant one.
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq u
    rw [hu_norm, Complex.normSq_apply] at h
    linear_combination h
  have hnw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hdet_aux : x.re * y.re + x.im * y.im = 1 - ‖w‖ ^ 2 := by
    rw [hnw, hx_def, hy_def]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    linear_combination (1 - w.re ^ 2 - w.im ^ 2) * hu2
  have hdet1 : a * d - b * c = 1 := by
    have h1 : (a * d - b * c) * s ^ 2 = x.re * y.re + x.im * y.im := by
      linear_combination (a * s) * hdR + y.re * haR - (b * s) * hcR + x.im * hbR
    have h2 : (a * d - b * c) * s ^ 2 = 1 * s ^ 2 := by
      rw [h1, hdet_aux, hs_sq]; ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hs_ne) h2
  have hdetM : Matrix.det !![a, b; c, d] = 1 := by
    rw [Matrix.det_fin_two_of]; exact hdet1
  -- The fractional linear action identity, for every point of the disc.
  have main : ∀ ζ : ℂ, ζ ∈ ball (0 : ℂ) 1 →
      ((a : ℂ) * cayleyToHalfPlane ζ + (b : ℂ)) /
        ((c : ℂ) * cayleyToHalfPlane ζ + (d : ℂ))
        = cayleyToHalfPlane (η * mobiusDisk w ζ) := by
    intro ζ hζ
    have h1ζ : (1 : ℂ) - ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hζ
    have hdζ : (1 : ℂ) - (starRingEnd ℂ) w * ζ ≠ 0 := mobiusDisk_denom_ne_zero hζ hw
    have hFmem : η * mobiusDisk w ζ ∈ ball (0 : ℂ) 1 := by
      have hm := mobiusDisk_mapsTo hζ hw
      rw [mem_ball, dist_zero_right] at hm ⊢
      rw [norm_mul, hη, one_mul]; exact hm
    have h1F : (1 : ℂ) - η * mobiusDisk w ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hFmem
    have hCim : 0 < (cayleyToHalfPlane ζ).im := cayleyToHalfPlane_im_pos hζ
    have hDen : (c : ℂ) * cayleyToHalfPlane ζ + (d : ℂ) ≠ 0 := by
      intro h0
      have him : c * (cayleyToHalfPlane ζ).im = 0 := by
        simpa using congrArg Complex.im h0
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp him with h | h
        · exact h
        · exact absurd h (ne_of_gt hCim)
      have hre : c * (cayleyToHalfPlane ζ).re + d = 0 := by
        simpa using congrArg Complex.re h0
      rw [hc0, zero_mul, zero_add] at hre
      rw [hc0, hre] at hdet1
      norm_num at hdet1
    have hCF : cayleyToHalfPlane (η * mobiusDisk w ζ)
        = Complex.I * (1 + η * mobiusDisk w ζ) / (1 - η * mobiusDisk w ζ) := rfl
    rw [hCF, div_eq_div_iff hDen h1F]
    set G : ℂ := (1 + ζ) / (1 - ζ) with hG_def
    have hC_eq : cayleyToHalfPlane ζ = Complex.I * G := by
      rw [hG_def]
      simp only [cayleyToHalfPlane]
      ring
    rw [hC_eq]
    have star : ((x + (starRingEnd ℂ) x) * G - (y - (starRingEnd ℂ) y))
          * (1 - η * mobiusDisk w ζ)
        = (1 + η * mobiusDisk w ζ)
          * ((y + (starRingEnd ℂ) y) - (x - (starRingEnd ℂ) x) * G) := by
      rw [hcx, hcy, hx_def, hy_def, hG_def, ← hu_sq]
      simp only [mobiusDisk]
      field_simp
      ring
    have h2s : ((s : ℂ) * 2) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hs_ne) two_ne_zero
    refine mul_right_cancel₀ h2s ?_
    linear_combination (Complex.I * G * (1 - η * mobiusDisk w ζ)) * haxC
      + (1 - η * mobiusDisk w ζ) * hbxC
      + (-(Complex.I ^ 2) * G * (1 + η * mobiusDisk w ζ)) * hcxC
      + (-Complex.I * (1 + η * mobiusDisk w ζ)) * hdxC
      + Complex.I * star
      + (-Complex.I * G * (1 + η * mobiusDisk w ζ) * (x - (starRingEnd ℂ) x))
        * Complex.I_sq
  -- Assemble the `SL(2, ℝ)` element and verify the action pointwise.
  set A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![a, b; c, d], hdetM⟩
  refine ⟨A, fun z => ?_⟩
  have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 := z.2
  have hez : ((e z : ℂ)) ∈ ball (0 : ℂ) 1 := (e z).2
  refine ⟨⟨cayleyToHalfPlane (z : ℂ), cayleyToHalfPlane_im_pos hz⟩,
    ⟨cayleyToHalfPlane ((e z : ℂ)), cayleyToHalfPlane_im_pos hez⟩, rfl, rfl, ?_⟩
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change ((a : ℂ) * cayleyToHalfPlane (z : ℂ) + (b : ℂ)) /
      ((c : ℂ) * cayleyToHalfPlane (z : ℂ) + (d : ℂ)) = cayleyToHalfPlane ((e z : ℂ))
  rw [he z]
  exact main _ hz

/-- **The Fuchsian uniformization**: a hyperbolic surface is covered
holomorphically by the upper half plane, and the fibers of the covering are
the orbits of a Fuchsian group whose nontrivial elements act without fixed
points; in particular the surface is homeomorphic to the orbit space. -/
theorem exists_fuchsian_model {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X]
    (hX : IsHyperbolic X) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
      (π : ↥upperHalfOpens → X),
      IsFuchsianGroup Γ ∧
      (∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
        ∀ τ' : UpperHalfPlane, γ • τ' = τ') ∧
      IsCoveringMap π ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π ∧ Function.Surjective π ∧
      (∀ z w : ↥upperHalfOpens,
        π z = π w ↔ ∃ γ : Γ, γ • toUpperHalfPlane z = toUpperHalfPlane w) ∧
      Nonempty (X ≃ₜ Quotient (MulAction.orbitRel Γ UpperHalfPlane)) := by
  classical
  have : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  have : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  set x₀ : X := Classical.arbitrary X
  obtain ⟨E⟩ := hX x₀
  -- The Cayley homeomorphism from the disc to the upper half plane.
  have hcont_c : Continuous fun ζ : ↥unitDiscOpens =>
      (⟨cayleyToHalfPlane (ζ : ℂ), cayleyToHalfPlane_im_pos ζ.2⟩ : UpperHalfPlane) := by
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    change Continuous fun ζ : ↥unitDiscOpens => Complex.I * (1 + (ζ : ℂ)) / (1 - (ζ : ℂ))
    exact (continuous_const.mul (continuous_const.add continuous_subtype_val)).div
      (continuous_const.sub continuous_subtype_val)
      (fun ζ => one_sub_ne_zero_of_mem_ball ζ.2)
  have hcont_c' : Continuous fun τ : UpperHalfPlane =>
      (⟨halfPlaneToCayley (τ : ℂ), halfPlaneToCayley_mem_ball τ.2⟩ : ↥unitDiscOpens) := by
    refine Continuous.subtype_mk ?_ _
    change Continuous fun τ : UpperHalfPlane => ((τ : ℂ) - Complex.I) / ((τ : ℂ) + Complex.I)
    exact ((UpperHalfPlane.continuous_coe.sub continuous_const).div
      (UpperHalfPlane.continuous_coe.add continuous_const)
      (fun τ => add_I_ne_zero_of_im_pos τ.2))
  let cHomeo : ↥unitDiscOpens ≃ₜ UpperHalfPlane :=
    { toFun := fun ζ => ⟨cayleyToHalfPlane (ζ : ℂ), cayleyToHalfPlane_im_pos ζ.2⟩
      invFun := fun τ => ⟨halfPlaneToCayley (τ : ℂ), halfPlaneToCayley_mem_ball τ.2⟩
      left_inv := fun ζ => Subtype.ext (halfPlaneToCayley_cayleyToHalfPlane ζ.2)
      right_inv := fun τ => UpperHalfPlane.ext (cayleyToHalfPlane_halfPlaneToCayley τ.2)
      continuous_toFun := hcont_c
      continuous_invFun := hcont_c' }
  -- The uniformizing homeomorphism onto the upper half plane.
  set Φ : PathCover x₀ ≃ₜ UpperHalfPlane := E.toHomeomorph.trans cHomeo with hΦdef
  -- The Cayley diffeomorphism between the plane domains.
  have bridge : ∀ (W : Opens ℂ) (F : ℂ → ↥W) (z : ℂ),
      AnalyticAt ℂ (fun p => (F p : ℂ)) z → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F z := by
    intro W F z hFa
    rw [contMDiffAt_iff]
    constructor
    · exact IsInducing.subtypeVal.continuousAt_iff.mpr hFa.continuousAt
    · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
        Function.comp_id, modelWithCornersSelf_coe, Set.range_id, id_eq]
      rw [contDiffWithinAt_univ]
      exact hFa.contDiffAt
  have hKd_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ↥upperHalfOpens =>
        (⟨halfPlaneToCayley (z : ℂ), halfPlaneToCayley_mem_ball z.2⟩ : ↥unitDiscOpens)) := by
    intro z
    have hz : (0 : ℝ) < (z : ℂ).im := z.2
    set F : ℂ → ↥unitDiscOpens := fun w =>
      if h : 0 < w.im then ⟨halfPlaneToCayley w, halfPlaneToCayley_mem_ball h⟩
      else ⟨0, by simp [unitDiscOpens]⟩ with hFdef
    have hFa : AnalyticAt ℂ (fun p => (F p : ℂ)) (z : ℂ) := by
      have h1 : AnalyticAt ℂ halfPlaneToCayley (z : ℂ) := by
        change AnalyticAt ℂ (fun w => (w - Complex.I) / (w + Complex.I)) (z : ℂ)
        exact ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const)
          (add_I_ne_zero_of_im_pos hz))
      refine h1.congr ?_
      have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds hz] with w hw
      simp only [F, dif_pos hw]
    have key : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z' : ↥upperHalfOpens => F (z' : ℂ)) z :=
      contMDiffAt_subtype_iff.mpr (bridge unitDiscOpens F (z : ℂ) hFa)
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z' => ?_)
    have hz' : (0 : ℝ) < (z' : ℂ).im := z'.2
    simp only [F, dif_pos hz']
  have hKd_smooth' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun ζ : ↥unitDiscOpens =>
        (⟨cayleyToHalfPlane (ζ : ℂ), cayleyToHalfPlane_im_pos ζ.2⟩ : ↥upperHalfOpens)) := by
    intro ζ
    have hζ : (ζ : ℂ) ∈ ball (0 : ℂ) 1 := ζ.2
    set F : ℂ → ↥upperHalfOpens := fun w =>
      if h : w ∈ ball (0 : ℂ) 1 then ⟨cayleyToHalfPlane w, cayleyToHalfPlane_im_pos h⟩
      else ⟨Complex.I, by simp [upperHalfOpens]⟩ with hFdef
    have hFa : AnalyticAt ℂ (fun p => (F p : ℂ)) (ζ : ℂ) := by
      have h1 : AnalyticAt ℂ cayleyToHalfPlane (ζ : ℂ) := by
        change AnalyticAt ℂ (fun w => Complex.I * (1 + w) / (1 - w)) (ζ : ℂ)
        exact ((analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
          (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero_of_mem_ball hζ))
      refine h1.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hζ] with w hw
      simp only [F, dif_pos hw]
    have key : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun ζ' : ↥unitDiscOpens => F (ζ' : ℂ)) ζ :=
      contMDiffAt_subtype_iff.mpr (bridge upperHalfOpens F (ζ : ℂ) hFa)
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ζ' => ?_)
    have hζ' : (ζ' : ℂ) ∈ ball (0 : ℂ) 1 := ζ'.2
    simp only [F, dif_pos hζ']
  let Kd : ↥upperHalfOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens :=
    { toFun := fun z => ⟨halfPlaneToCayley (z : ℂ), halfPlaneToCayley_mem_ball z.2⟩
      invFun := fun ζ => ⟨cayleyToHalfPlane (ζ : ℂ), cayleyToHalfPlane_im_pos ζ.2⟩
      left_inv := fun z => Subtype.ext (cayleyToHalfPlane_halfPlaneToCayley z.2)
      right_inv := fun ζ => Subtype.ext (halfPlaneToCayley_cayleyToHalfPlane ζ.2)
      contMDiff_toFun := hKd_smooth
      contMDiff_invFun := hKd_smooth' }
  -- Smoothness of the covering projection: it reads as the identity in charts.
  have hproj_smooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (pathCoverProj x₀) := by
    intro pc
    obtain ⟨e₁, he₁, f₁, hf₁, hpc₁, hprojpc₁, hall₁, hcomm₁⟩ :=
      exists_charts_pathCoverProj_comm x₀ pc
    have hA : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e₁ pc := contMDiffAt_of_mem_maximalAtlas he₁ hpc₁
    have he₁pc : e₁ pc ∈ f₁.target := by
      rw [← hcomm₁ pc hpc₁]
      exact f₁.map_source hprojpc₁
    have hB : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f₁.symm (e₁ pc) :=
      contMDiffAt_symm_of_mem_maximalAtlas hf₁ he₁pc
    have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun qc : PathCover x₀ => f₁.symm (e₁ qc)) pc :=
      hB.comp pc hA
    refine hF.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (e₁.open_source.mem_nhds hpc₁) fun qc hqc => ?_)
    rw [← hcomm₁ qc hqc]
    exact (f₁.left_inv (hall₁ qc hqc)).symm
  -- The covering map from the upper half plane.
  set π : ↥upperHalfOpens → X := fun z => pathCoverProj x₀ (E.symm (Kd z)) with hπdef
  have hπcov : IsCoveringMap π :=
    (pathCoverProj_isCoveringMap x₀).comp_homeomorph (Kd.toHomeomorph.trans E.toHomeomorph.symm)
  have hπsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π :=
    hproj_smooth.comp ((E.symm.contMDiff).comp Kd.contMDiff)
  have hπsurj : Function.Surjective π := by
    intro x
    refine ⟨Kd.symm (E ⟨x, ⟦PathConnectedSpace.somePath x₀ x⟧⟩), ?_⟩
    change pathCoverProj x₀ (E.symm (Kd (Kd.symm (E ⟨x, ⟦PathConnectedSpace.somePath x₀ x⟧⟩)))) = x
    rw [Kd.apply_symm_apply, E.symm_apply_apply]
    rfl
  -- Bridge identity: Φ of the lift of a half-plane point recovers the point.
  have hZΦ : ∀ z : ↥upperHalfOpens, Φ (E.symm (Kd z)) = toUpperHalfPlane z := by
    intro z
    apply UpperHalfPlane.ext
    have h1 : (Φ (E.symm (Kd z)) : ℂ) = cayleyToHalfPlane ((E (E.symm (Kd z)) : ℂ)) := rfl
    rw [h1, E.apply_symm_apply]
    change cayleyToHalfPlane (halfPlaneToCayley (z : ℂ)) = (z : ℂ)
    exact cayleyToHalfPlane_halfPlaneToCayley z.2
  -- Deck algebra.
  have hdeck_refl : ∀ pc : PathCover x₀,
      pathCoverDeck x₀ (Path.Homotopic.Quotient.refl x₀) pc = pc := by
    intro pc
    obtain ⟨pt, cls⟩ := pc
    exact congrArg (PathCover.mk pt) (Path.Homotopic.Quotient.refl_trans cls)
  have hdeck_comp : ∀ (δ δ' : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
      pathCoverDeck x₀ δ (pathCoverDeck x₀ δ' pc) =
        pathCoverDeck x₀ (Path.Homotopic.Quotient.trans δ δ') pc := fun δ δ' pc =>
    congrArg (PathCover.mk pc.pt) (Path.Homotopic.Quotient.trans_assoc δ δ' pc.cls).symm
  have hdeck_cancel : ∀ (δ : Path.Homotopic.Quotient x₀ x₀) (pc : PathCover x₀),
      pathCoverDeck x₀ δ (pathCoverDeck x₀ (Path.Homotopic.Quotient.symm δ) pc) = pc := by
    intro δ pc
    rw [hdeck_comp, Path.Homotopic.Quotient.trans_symm]
    exact hdeck_refl pc
  -- Every deck transformation is realized by an element of SL(2, ℝ).
  have hrealize : ∀ δ : Path.Homotopic.Quotient x₀ x₀,
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        ∀ pc : PathCover x₀, A • Φ pc = Φ (pathCoverDeck x₀ δ pc) := by
    intro δ
    obtain ⟨D, hD⟩ := exists_pathCoverDeck_diffeomorph x₀ δ
    obtain ⟨A, hA⟩ := exists_sl2_of_diffeomorph_unitDisc ((E.symm.trans D).trans E)
    refine ⟨A, fun pc => ?_⟩
    obtain ⟨τ, τ', h1, h2, h3⟩ := hA (E pc)
    have hτ : τ = Φ pc := UpperHalfPlane.ext h1
    have he : (((E.symm.trans D).trans E) (E pc) : ℂ) = ((E (pathCoverDeck x₀ δ pc)) : ℂ) := by
      have h0 : ((E.symm.trans D).trans E) (E pc) = E (D (E.symm (E pc))) := rfl
      rw [h0, E.symm_apply_apply, hD pc]
    have hτ' : τ' = Φ (pathCoverDeck x₀ δ pc) := by
      apply UpperHalfPlane.ext
      rw [h2, he]
      rfl
    rw [← hτ, ← hτ']
    exact h3
  -- The Fuchsian group: SL(2, ℝ) elements realizing some deck transformation.
  set S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {A | ∃ δ : Path.Homotopic.Quotient x₀ x₀,
      ∀ pc : PathCover x₀, A • Φ pc = Φ (pathCoverDeck x₀ δ pc)} with hSdef
  have hone : (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ S := by
    refine ⟨Path.Homotopic.Quotient.refl x₀, fun pc => ?_⟩
    rw [one_smul, hdeck_refl pc]
  have hmul : ∀ A B, A ∈ S → B ∈ S → A * B ∈ S := by
    rintro A B ⟨δ, hδ⟩ ⟨δ', hδ'⟩
    refine ⟨Path.Homotopic.Quotient.trans δ δ', fun pc => ?_⟩
    rw [mul_smul, hδ' pc, hδ (pathCoverDeck x₀ δ' pc), hdeck_comp]
  have hinv : ∀ A, A ∈ S → A⁻¹ ∈ S := by
    rintro A ⟨δ, hδ⟩
    refine ⟨Path.Homotopic.Quotient.symm δ, fun pc => ?_⟩
    have h2 : A • Φ (pathCoverDeck x₀ (Path.Homotopic.Quotient.symm δ) pc) = Φ pc := by
      rw [hδ, hdeck_cancel]
    rw [← h2, inv_smul_smul]
  set Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    { carrier := S
      one_mem' := hone
      mul_mem' := fun ha hb => hmul _ _ ha hb
      inv_mem' := fun ha => hinv _ ha } with hΓdef
  have hΓmem : ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, A ∈ Γ ↔ A ∈ S := fun A => Iff.rfl
  -- Fibers of the projection are the Γ-orbits, read through Φ.
  have hfib : ∀ pc qc : PathCover x₀,
      pathCoverProj x₀ pc = pathCoverProj x₀ qc ↔ ∃ γ : Γ, γ • Φ pc = Φ qc := by
    intro pc qc
    constructor
    · intro h
      obtain ⟨δ, hδeq⟩ := pathCoverDeck_transitive x₀ pc qc h
      obtain ⟨A, hA⟩ := hrealize δ
      refine ⟨⟨A, (hΓmem A).mpr ⟨δ, hA⟩⟩, ?_⟩
      rw [Subgroup.smul_def, hA pc, hδeq]
    · rintro ⟨⟨A, hAΓ⟩, hsm⟩
      obtain ⟨δ, hδ⟩ := (hΓmem A).mp hAΓ
      rw [Subgroup.smul_def] at hsm
      have h1 : Φ (pathCoverDeck x₀ δ pc) = Φ qc := by rw [← hδ pc, hsm]
      have h2 : pathCoverDeck x₀ δ pc = qc := Φ.injective h1
      rw [← h2, pathCoverProj_deck]
  -- Stabilizer clause: an element of Γ with a fixed point acts trivially.
  have hstab : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ' := by
    rintro ⟨A, hAΓ⟩ ⟨τ, hτ⟩ τ'
    obtain ⟨δ, hδ⟩ := (hΓmem A).mp hAΓ
    rw [Subgroup.smul_def] at hτ ⊢
    have h1 : A • Φ (Φ.symm τ) = Φ (pathCoverDeck x₀ δ (Φ.symm τ)) := hδ (Φ.symm τ)
    rw [Φ.apply_symm_apply, hτ] at h1
    have h2 : pathCoverDeck x₀ δ (Φ.symm τ) = Φ.symm τ := by
      apply Φ.injective
      rw [← h1, Φ.apply_symm_apply]
    have h3 := pathCoverDeck_id_of_fixed x₀ δ h2 (Φ.symm τ')
    have h4 : A • Φ (Φ.symm τ') = Φ (pathCoverDeck x₀ δ (Φ.symm τ')) := hδ (Φ.symm τ')
    rw [Φ.apply_symm_apply, h3, Φ.apply_symm_apply] at h4
    exact h4
  -- Fibers-orbits, in the statement's normal form.
  have hfibπ : ∀ z w : ↥upperHalfOpens,
      π z = π w ↔ ∃ γ : Γ, γ • toUpperHalfPlane z = toUpperHalfPlane w := by
    intro z w
    rw [← hZΦ z, ← hZΦ w]
    exact hfib (E.symm (Kd z)) (E.symm (Kd w))
  -- The kernel of the action on the upper half plane is {±1}.
  set negOne : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨-(1 : Matrix (Fin 2) (Fin 2) ℝ), by rw [Matrix.det_neg, Matrix.det_one]; simp⟩ with hnegOne
  have hkernel : ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ τ' : UpperHalfPlane, A • τ' = τ') → A = 1 ∨ A = negOne := by
    intro A h
    have key : ∀ (z : ℂ), 0 < z.im →
        ((A 0 0 : ℝ) * z + (A 0 1 : ℝ)) / ((A 1 0 : ℝ) * z + (A 1 1 : ℝ)) = z := by
      intro z hz
      have h1 := congrArg UpperHalfPlane.coe (h (UpperHalfPlane.mk z hz))
      rw [UpperHalfPlane.coe_specialLinearGroup_apply] at h1
      simpa using h1
    have hden : ∀ (z : ℂ), 0 < z.im → ((A 1 0 : ℝ) * z + (A 1 1 : ℝ)) ≠ 0 := by
      intro z hz h0
      have h1 := key z hz
      rw [h0, div_zero] at h1
      rw [← h1] at hz
      simp at hz
    have hcross : ∀ (z : ℂ), 0 < z.im →
        ((A 0 0 : ℝ) * z + (A 0 1 : ℝ)) = z * ((A 1 0 : ℝ) * z + (A 1 1 : ℝ)) := by
      intro z hz
      exact (div_eq_iff (hden z hz)).mp (key z hz)
    have hI : 0 < (Complex.I).im := by simp
    have h2I : 0 < ((2 : ℂ) * Complex.I).im := by simp
    have e1 := hcross Complex.I hI
    have e2 := hcross ((2 : ℂ) * Complex.I) h2I
    have e1re := congrArg Complex.re e1
    have e1im := congrArg Complex.im e1
    have e2re := congrArg Complex.re e2
    simp only [Fin.isValue, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, zero_add, zero_mul,
      Complex.add_im, Complex.mul_im, add_zero, one_mul, zero_sub, Complex.re_ofNat,
      Complex.im_ofNat] at e1re e1im e2re
    have hc : A 1 0 = 0 := by nlinarith [e1re, e2re]
    have hb : A 0 1 = 0 := by nlinarith [e1re, hc]
    have had : A 0 0 = A 1 1 := by nlinarith [e1im]
    have hdet := A.2
    rw [Matrix.det_fin_two] at hdet
    have ha2 : A 0 0 * A 0 0 = 1 := by
      rw [hb, hc, ← had] at hdet
      linarith
    have ha : A 0 0 = 1 ∨ A 0 0 = -1 := by
      rcases mul_eq_zero.mp (show (A 0 0 - 1) * (A 0 0 + 1) = 0 by nlinarith) with h' | h'
      · left; linarith
      · right; linarith
    rcases ha with h' | h'
    · left
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h', hb, hc, had ▸ h']
    · right
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [negOne, Matrix.neg_apply, h', hb, hc, had ▸ h']
  -- The subgroup of Γ acting trivially is finite.
  have hK₀fin : {g : Γ | ∀ τ' : UpperHalfPlane, g • τ' = τ'}.Finite := by
    have himg : Subtype.val '' {g : Γ | ∀ τ' : UpperHalfPlane, g • τ' = τ'} ⊆ {1, negOne} := by
      rintro B ⟨g, hg, rfl⟩
      rcases hkernel (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        (fun τ' => by rw [← Subgroup.smul_def]; exact hg τ') with h' | h'
      · exact Set.mem_insert_iff.mpr (Or.inl h')
      · exact Set.mem_insert_iff.mpr (Or.inr h')
    exact Set.Finite.of_finite_image
      (((Set.finite_singleton negOne).insert 1).subset himg) Subtype.val_injective.injOn
  -- The base point of the orbit-counting argument.
  set τ₀ : UpperHalfPlane := Φ (pathCoverBase x₀) with hτ₀def
  -- Elements of Γ moving τ₀ to a fixed point form a finite set.
  have hfiber_fin : ∀ v : UpperHalfPlane, {γ : Γ | γ • τ₀ = v}.Finite := by
    intro v
    rcases Set.eq_empty_or_nonempty {γ : Γ | γ • τ₀ = v} with he | ⟨γ₁, hγ₁⟩
    · rw [he]; exact Set.finite_empty
    · have hγ₁' : γ₁ • τ₀ = v := hγ₁
      have hsub2 : {γ : Γ | γ • τ₀ = v} ⊆
          (fun g : Γ => γ₁ * g) '' {g : Γ | ∀ τ' : UpperHalfPlane, g • τ' = τ'} := by
        intro γ hγ
        have hγ' : γ • τ₀ = v := hγ
        have hfix : (γ₁⁻¹ * γ) • τ₀ = τ₀ := by
          rw [mul_smul, hγ', ← hγ₁', inv_smul_smul]
        exact ⟨γ₁⁻¹ * γ, hstab _ ⟨τ₀, hfix⟩, mul_inv_cancel_left γ₁ γ⟩
      exact ((hK₀fin.image _).subset hsub2)
  -- Proper discontinuity of the action of Γ.
  have hproper : ProperlyDiscontinuousSMul Γ UpperHalfPlane := by
    refine ⟨?_⟩
    intro K L hK hL
    obtain ⟨rK, hrK⟩ := hK.isBounded.subset_closedBall τ₀
    obtain ⟨rL, hrL⟩ := hL.isBounded.subset_closedBall τ₀
    have hCco : IsCompact (Φ ⁻¹' closedBall τ₀ (rK + rL)) :=
      Φ.isCompact_preimage.mpr (isCompact_closedBall τ₀ _)
    have hFfin : (pathCoverProj x₀ ⁻¹' {x₀} ∩ Φ ⁻¹' closedBall τ₀ (rK + rL)).Finite :=
      finite_fiber_inter_compact x₀ hCco x₀
    refine Set.Finite.subset (hFfin.biUnion (fun pc _ => hfiber_fin (Φ pc))) ?_
    intro γ hγ
    obtain ⟨y, ⟨k, hkK, hky⟩, hyL⟩ := hγ
    obtain ⟨δ, hδ⟩ := (hΓmem (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)).mp γ.2
    have hky' : γ • k = y := hky
    have hbound : dist (γ • τ₀) τ₀ ≤ rK + rL := by
      have h1 : dist (γ • τ₀) (γ • k) = dist τ₀ k := by
        rw [Subgroup.smul_def, Subgroup.smul_def, dist_smul]
      have h2 : dist k τ₀ ≤ rK := mem_closedBall.mp (hrK hkK)
      have h3 : dist y τ₀ ≤ rL := mem_closedBall.mp (hrL hyL)
      calc dist (γ • τ₀) τ₀ ≤ dist (γ • τ₀) (γ • k) + dist (γ • k) τ₀ := dist_triangle _ _ _
        _ = dist τ₀ k + dist (γ • k) τ₀ := by rw [h1]
        _ ≤ rK + rL := by
            rw [dist_comm τ₀ k, hky']
            exact add_le_add h2 h3
    have hΓτ₀ : γ • τ₀ = Φ (pathCoverDeck x₀ δ (pathCoverBase x₀)) := by
      rw [Subgroup.smul_def, hτ₀def]
      exact hδ (pathCoverBase x₀)
    have hpc' : pathCoverDeck x₀ δ (pathCoverBase x₀) ∈
        pathCoverProj x₀ ⁻¹' {x₀} ∩ Φ ⁻¹' closedBall τ₀ (rK + rL) := by
      constructor
      · change pathCoverProj x₀ (pathCoverDeck x₀ δ (pathCoverBase x₀)) ∈ ({x₀} : Set X)
        rw [pathCoverProj_deck]
        rfl
      · change Φ (pathCoverDeck x₀ δ (pathCoverBase x₀)) ∈ closedBall τ₀ (rK + rL)
        rw [← hΓτ₀]
        exact mem_closedBall.mpr hbound
    exact Set.mem_biUnion hpc' hΓτ₀
  -- The descent of the covering to the orbit space.
  set ρ : UpperHalfPlane → X := fun τ => pathCoverProj x₀ (Φ.symm τ) with hρdef
  have hρresp : ∀ a b : UpperHalfPlane, (MulAction.orbitRel Γ UpperHalfPlane) a b →
      ρ a = ρ b := by
    intro a b hab
    obtain ⟨⟨A, hAΓ⟩, hab'⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    obtain ⟨δ, hδ⟩ := (hΓmem A).mp hAΓ
    rw [Subgroup.smul_def] at hab'
    have h1 : A • Φ (Φ.symm b) = Φ (pathCoverDeck x₀ δ (Φ.symm b)) := hδ (Φ.symm b)
    rw [Φ.apply_symm_apply, hab'] at h1
    change pathCoverProj x₀ (Φ.symm a) = pathCoverProj x₀ (Φ.symm b)
    rw [h1, Φ.symm_apply_apply, pathCoverProj_deck]
  have hρcont : Continuous ρ :=
    ((pathCoverProj_isCoveringMap x₀).continuous).comp Φ.symm.continuous
  have hρopen : IsOpenMap ρ :=
    ((pathCoverProj_isCoveringMap x₀).isOpenMap).comp Φ.symm.isOpenMap
  have hqcont : Continuous (Quotient.lift ρ hρresp) := hρcont.quotient_lift hρresp
  have hqsurj : Function.Surjective (Quotient.lift ρ hρresp) := by
    intro x
    refine ⟨⟦Φ ⟨x, ⟦PathConnectedSpace.somePath x₀ x⟧⟩⟧, ?_⟩
    change pathCoverProj x₀ (Φ.symm (Φ ⟨x, ⟦PathConnectedSpace.somePath x₀ x⟧⟩)) = x
    rw [Φ.symm_apply_apply]
    rfl
  have hqinj : Function.Injective (Quotient.lift ρ hρresp) := by
    intro qa qb h
    obtain ⟨a, rfl⟩ := Quotient.exists_rep qa
    obtain ⟨b, rfl⟩ := Quotient.exists_rep qb
    have h' : pathCoverProj x₀ (Φ.symm a) = pathCoverProj x₀ (Φ.symm b) := h
    obtain ⟨γ, hγ⟩ := (hfib (Φ.symm a) (Φ.symm b)).mp h'
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply] at hγ
    refine Quotient.sound ?_
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, by rw [← hγ, inv_smul_smul]⟩)
  have hqopen : IsOpenMap (Quotient.lift ρ hρresp) := by
    intro U hU
    have hcm : Continuous
        (fun a : UpperHalfPlane =>
          (⟦a⟧ : Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :=
      continuous_quotient_mk'
    have himg : Quotient.lift ρ hρresp '' U =
        ρ '' ((fun a : UpperHalfPlane =>
          (⟦a⟧ : Quotient (MulAction.orbitRel Γ UpperHalfPlane))) ⁻¹' U) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨a, rfl⟩ := Quotient.exists_rep u
        exact ⟨a, hu, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟦a⟧, ha, rfl⟩
    rw [himg]
    exact hρopen _ (hU.preimage hcm)
  -- Assemble.
  refine ⟨Γ, π, hproper, hstab, hπcov, hπsmooth, hπsurj, hfibπ, ?_⟩
  exact ⟨((Equiv.ofBijective _ ⟨hqinj, hqsurj⟩).toHomeomorphOfContinuousOpen
    hqcont hqopen).symm⟩

end RiemannDynamics
