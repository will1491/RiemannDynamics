/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Geometric
import RiemannDynamics.QC.Modulus
import RiemannDynamics.QC.LengthArea
import RiemannDynamics.QC.ReverseLengthAreaForward
import RiemannDynamics.QC.GeometricDifferentiable
import RiemannDynamics.QC.GeometricToAnalytic
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Lusin's condition (N) for geometric quasiconformal maps

A geometric `K`-quasiconformal map `f : ℂ → ℂ` satisfies **Lusin's condition (N)**:
the image of every Lebesgue-null set is Lebesgue-null,
`volume S = 0 → volume (f '' S) = 0`.

This is the unified keystone for the dilatation-nondegeneracy and no-singular-part
residuals of the geometric ⇒ analytic direction. The proof is the classical
**modulus method** (Väisälä, *Lectures on n-dimensional QC mappings*, §33): a
null source set cannot carry positive image area, because the connecting curve
family of any image square is bounded in modulus by `K` times the modulus of the
corresponding source family, and the source family of curves meeting a null set has
modulus zero.

## Main result

* `IsQCGeometric.lusinN` — geometric `K`-QC maps satisfy Lusin's condition (N).
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-! ## Step 2 ingredient: a Fubini lower bound for a horizontal-segment subfamily

For a measurable height set `Y ⊆ ℝ` and a horizontal width `[a, b]`, the family of
horizontal segments `x ↦ ⟨a + (b−a)·x, y⟩` with `y ∈ Y` has modulus at least
`volume Y / (b − a)`. This is the length–area / Fubini lower bound restricted to the
heights in `Y`; it is the exact analogue of `lengthArea_modulus_lower_bound` (which
is the special case `Y = [s, t]`, giving `(t − s)/(b − a)`). The proof is the same
Cauchy–Schwarz-and-Fubini argument: admissibility gives `1 ≤ ∫ ρ` along each
segment, Cauchy–Schwarz upgrades this to `1/(b−a) ≤ ∫ ρ²` per line, and integrating
over `y ∈ Y` gives `volume Y / (b−a) ≤ ∫∫ ρ²`. -/
theorem segmentFamily_modulus_ge {a b : ℝ} (hab : a < b) {Y : Set ℝ}
    (hY : MeasurableSet Y) :
    (volume Y) * ENNReal.ofReal (1 / (b - a))
      ≤ curveModulus {γ : ℝ → ℂ |
          ∃ y ∈ Y, γ = fun x : ℝ => Complex.mk (a + (b - a) * x) y} := by
  have hbma : (0:ℝ) < b - a := by linarith
  -- Reduce the infimum to a per-density bound.
  unfold curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hadm⟩
  -- ===== STEP A: area = iterated integral (Tonelli + volume-preserving equiv) =====
  have harea : (∫⁻ z, (ρ z) ^ 2) = ∫⁻ y : ℝ, ∫⁻ u : ℝ, (ρ (Complex.mk u y)) ^ 2 := by
    have hmeas : Measurable (fun z => (ρ z) ^ 2) := (hρmeas.pow_const 2)
    have h1 : (∫⁻ z, (ρ z) ^ 2)
        = ∫⁻ p : ℝ × ℝ, (ρ (Complex.measurableEquivRealProd.symm p)) ^ 2 := by
      rw [← (Complex.volume_preserving_equiv_real_prod.symm
        Complex.measurableEquivRealProd).lintegral_comp hmeas]
    rw [h1, Measure.volume_eq_prod, lintegral_prod_symm]
    · simp only [Complex.measurableEquivRealProd_symm_apply]
    · rw [← Measure.volume_eq_prod]
      exact (hmeas.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable
  -- ===== STEP B: the per-y lower bound `ofReal(1/(b-a)) ≤ ∫⁻ u in [a,b], (ρ⟨u,y⟩)²` =====
  have hper : ∀ y ∈ Y,
      ENNReal.ofReal (1/(b-a)) ≤ ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 := by
    intro y hy
    -- measurability of u ↦ ρ⟨u,y⟩
    have hmkmeas : Measurable (fun u : ℝ => Complex.mk u y) := by
      have : (fun u : ℝ => Complex.mk u y) = (fun u : ℝ => (u : ℂ) + (y:ℝ) * Complex.I) := by
        funext u; apply Complex.ext <;> simp
      rw [this]; exact (Complex.measurable_ofReal).add_const _
    have hmeasu : Measurable (fun u : ℝ => ρ (Complex.mk u y)) := hρmeas.comp hmkmeas
    -- B1: `1 ≤ ∫⁻ u in [a,b], ρ⟨u,y⟩` (admissibility + change of variables)
    have hone : (1 : ℝ≥0∞) ≤ ∫⁻ u : ℝ in Set.Icc a b, ρ (Complex.mk u y) := by
      set γ : ℝ → ℂ := fun x : ℝ => Complex.mk (a + (b - a) * x) y with hγdef
      -- deriv of γ
      have hderiv : ∀ x, deriv γ x = ((b - a : ℝ) : ℂ) := by
        intro x
        have hd : HasDerivAt γ ((b - a : ℝ) : ℂ) x := by
          have h : γ = (fun x : ℝ => ((a + (b - a) * x : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
            funext x; apply Complex.ext <;> simp [hγdef]
          rw [h]
          have hr : HasDerivAt (fun x : ℝ => (a + (b - a) * x : ℝ)) (b - a) x := by
            have h1 : HasDerivAt (fun x : ℝ => (b - a) * x) (b - a) x := by
              simpa only [mul_one] using (hasDerivAt_id x).const_mul (b - a)
            simpa only [zero_add] using (hasDerivAt_const x a).add h1
          exact (hr.ofReal_comp).add_const ((y : ℝ) * Complex.I)
        exact hd.deriv
      -- norm of deriv = ofReal (b - a)
      have hnorm : ∀ x, (‖deriv γ x‖₊ : ℝ≥0∞) = ENNReal.ofReal (b - a) := by
        intro x
        rw [hderiv x, ← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hbma]
      -- arc-length integral
      have harc : arcLengthLineIntegral ρ γ
          = ENNReal.ofReal (b - a) * ∫⁻ x in Set.Icc (0:ℝ) 1, ρ (γ x) := by
        unfold arcLengthLineIntegral
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro x
        rw [hnorm x, mul_comm]
      have hadm' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (b - a) * ∫⁻ x in Set.Icc (0:ℝ) 1, ρ (γ x) := by
        rw [← harc]; exact hadm γ ⟨y, hy, rfl⟩
      -- change of variables: ∫⁻ u in [a,b], ρ⟨u,y⟩ = (b-a) * ∫⁻ x in [0,1], ρ(γ x)
      have hcov : ∫⁻ u : ℝ in Set.Icc a b, ρ (Complex.mk u y)
          = ENNReal.ofReal (b - a) * ∫⁻ x in Set.Icc (0:ℝ) 1, ρ (γ x) := by
        set fmap : ℝ → ℝ := fun x => a + (b - a) * x with hf
        have himg : fmap '' (Set.Icc 0 1) = Set.Icc a b := by
          apply Set.Subset.antisymm
          · rintro _ ⟨x, hx, rfl⟩
            simp only [hf, Set.mem_Icc] at hx ⊢
            constructor <;> nlinarith [hx.1, hx.2]
          · intro u hu
            simp only [Set.mem_Icc] at hu
            refine ⟨(u - a)/(b-a), ?_, ?_⟩
            · simp only [Set.mem_Icc]
              refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
              rw [div_le_one hbma]; linarith
            · simp only [hf]; field_simp; ring
        have hderivf : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt fmap (b - a) (Set.Icc 0 1) x := by
          intro x hx
          have : HasDerivAt fmap (b - a) x := by
            have h1 : HasDerivAt (fun x : ℝ => (b - a) * x) (b - a) x := by
              simpa only [mul_one] using (hasDerivAt_id x).const_mul (b - a)
            simpa only [zero_add] using (hasDerivAt_const x a).add h1
          exact this.hasDerivWithinAt
        have hinj : Set.InjOn fmap (Set.Icc 0 1) := by
          intro x1 _ x2 _ h
          simp only [hf, add_right_inj, mul_right_inj' (ne_of_gt hbma)] at h
          exact h
        have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderivf hinj
          (fun u => ρ (Complex.mk u y))
        rw [himg] at key
        rw [key, abs_of_pos hbma, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [hcov]; exact hadm'
    -- B2: Cauchy–Schwarz `1/(b-a) ≤ ∫⁻ (ρ⟨u,y⟩)²`
    have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc a b)) hconj
      (f := fun u => ρ (Complex.mk u y)) (g := fun _ => (1:ℝ≥0∞))
      hmeasu.aemeasurable aemeasurable_const
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow] at hcs
    have hvol : ∫⁻ (a_1 : ℝ) in Set.Icc a b, (1:ℝ≥0∞) = ENNReal.ofReal (b - a) := by
      rw [setLIntegral_one, Real.volume_Icc]
    rw [hvol] at hcs
    have h2 : (1:ℝ≥0∞) ≤ (∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^(2:ℝ))^(1/2:ℝ)
        * (ENNReal.ofReal (b - a))^(1/2:ℝ) := le_trans hone hcs
    -- normalize `^(2:ℝ)` to `^2`
    have hpow : (∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^(2:ℝ))
        = ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 := by
      apply lintegral_congr; intro u; rw [ENNReal.rpow_two]
    rw [hpow] at h2
    set A : ℝ≥0∞ := ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 with hA
    -- square both sides
    have hsq : (1:ℝ≥0∞) ≤ A * ENNReal.ofReal (b - a) := by
      have hh := ENNReal.rpow_le_rpow h2 (by norm_num : (0:ℝ) ≤ 2)
      rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hh
      norm_num at hh
      exact hh
    have hbne : ENNReal.ofReal (b - a) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    rw [show ENNReal.ofReal (1/(b-a)) = (ENNReal.ofReal (b-a))⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos hbma]]
    rw [ENNReal.inv_le_iff_le_mul (fun _ => hbne) (fun h => absurd h ENNReal.ofReal_ne_top)]
    rwa [mul_comm]
  -- ===== STEP C: integrate the per-y bound over y ∈ Y =====
  have hconst : ∫⁻ (_ : ℝ) in Y, ENNReal.ofReal (1/(b-a))
      = (volume Y) * ENNReal.ofReal (1/(b-a)) := by
    rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
  rw [← hconst, harea]
  calc ∫⁻ (_ : ℝ) in Y, ENNReal.ofReal (1/(b-a))
      ≤ ∫⁻ y : ℝ in Y, ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 := by
        refine setLIntegral_mono_ae' hY ?_
        filter_upwards with y hy using hper y hy
    _ ≤ ∫⁻ y : ℝ, ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ y : ℝ, ∫⁻ u : ℝ, (ρ (Complex.mk u y))^2 := by
        exact lintegral_mono (fun y => setLIntegral_le_lintegral _ _)

/-! ## The general curve-family distortion

The geometric quasiconformality hypothesis `hf.2.2` bounds the modulus of the image
*connecting* family of every quadrilateral by `K` times the source modulus. The
**general curve-family distortion** upgrades this from quadrilaterals to an arbitrary
curve family `Γ`: the modulus of the pushforward family `(f ∘ ·) '' Γ` is at most `K`
times the modulus of `Γ`. It is the analogue, for geometric maps, of the analytic-side
energy-transfer `pushforwardGood_modulus_le` (`QC/Equivalence.lean`), and is proved here
by the *same* length–area change-of-variables route, fed by the geometric infinitesimal
data `IsQCGeometric.reverseLengthArea_data` (a.e. differentiability, positive Jacobian,
and the pointwise dilatation bound `‖Df‖² ≤ K · det Df`).

The pushforward family is split, exactly as on the analytic side, into the **chain-rule
good** curves (those `γ` for which `f ∘ γ` is absolutely continuous, the differential
of `f` is nondegenerate along `γ`, and the chain rule holds a.e.) and their complement.
The good part is bounded by `K · curveModulus Γ` by the length–area energy transfer
(`IsQCGeometric.pushforwardGood_modulus_le` below); the complementary image part has
zero modulus (`IsQCGeometric.image_chainRule_exceptional_modulus_zero`). -/

/-- **The pushforward of the chain-rule-good subfamily is `K`-quasiconformally bounded
(geometric side).** For a geometric `K`-quasiconformal map `f` and an arbitrary curve
family `Γ`, the image under `f` of the chain-rule **good** subfamily — those `γ ∈ Γ` for
which `f ∘ γ` is absolutely continuous with the a.e. chain rule and positive Jacobian —
has modulus at most `K · curveModulus Γ`.

This is the geometric analogue of the analytic-side `pushforwardGood_modulus_le`
(`QC/Equivalence.lean`); the proof is identical (the dilatation-controlled change of
variables transferring the density `σ(w) = ρ(g w)·‖(Df(g w))⁻¹‖`, `g = f⁻¹`), the only
difference being that the infinitesimal data — a.e. differentiability, positive Jacobian,
and the pointwise dilatation bound `‖(Df)⁻¹‖²·det Df ≤ K` — is taken from
`IsQCGeometric.reverseLengthArea_data` rather than from a Beltrami coefficient. -/
private theorem IsQCGeometric.pushforwardGood_modulus_le {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (Γ : Set (ℝ → ℂ)) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) ''
      (Γ \ {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
            AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
          (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
              deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
            HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)}))
      ≤ ENNReal.ofReal K * curveModulus Γ := by
  classical
  -- `f` is a homeomorphism and `K` is positive.
  have hhom : IsHomeomorph f := hf.2.1.isHomeomorph
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hf.1
  -- The geometric infinitesimal data: a.e. differentiability, positive Jacobian, and the
  -- pointwise dilatation bound `‖Df‖² ≤ K · det Df`.
  obtain ⟨hdiff_ae, hdetpos_ae, hdil_norm, -, -⟩ := hf.reverseLengthArea_data
  -- Rewrite the dilatation bound into the `‖(Df)⁻¹‖² · det ≤ K` form used by the transfer.
  -- For a holomorphic-shaped real differential with `det > 0`, the two forms coincide
  -- (both equal `(p+q)/(p-q)` in the Wirtinger norms).
  have hdil : ∀ᵐ z : ℂ,
      ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * (fderiv ℝ f z).det ≤ K := by
    filter_upwards [hdetpos_ae, hdil_norm] with z hdetz hnormz
    set p : ℝ := ‖dz f z‖ with hp
    set q : ℝ := ‖dzbar f z‖ with hq
    set d : ℝ := (fderiv ℝ f z).det with hd
    have hdval : d = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger f z
    have hop : ‖fderiv ℝ f z‖ = p + q := opNorm_fderiv_eq_wirtinger f z
    have hdpos : 0 < d := hdetz
    have hp0 : 0 ≤ p := norm_nonneg _
    have hq0 : 0 ≤ q := norm_nonneg _
    -- From `0 < det` deduce `q < p`, hence `0 < p` and `0 < p − q`.
    have hpqlt : q < p := by nlinarith [hdval, hdpos, hp0, hq0]
    have hppos : 0 < p := lt_of_le_of_lt hq0 hpqlt
    have hpmq : 0 < p - q := by linarith
    have hinvval : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ = (p + q) / d :=
      opNorm_inverse_eq_wirtinger f z hdetz
    have hfactor : ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2 * d
        = (p + q) / (p - q) := by
      rw [hinvval, div_pow, hdval]
      have hsplit : p ^ 2 - q ^ 2 = (p + q) * (p - q) := by ring
      rw [hsplit]
      have hsum_ne : p + q ≠ 0 := by positivity
      have hpmq_ne : p - q ≠ 0 := ne_of_gt hpmq
      field_simp
    rw [hfactor]
    -- The `‖Df‖² ≤ K·det` bound rewrites as `(p+q)² ≤ K·(p+q)(p−q)`, giving `(p+q)/(p−q) ≤ K`.
    rw [hop, hdval] at hnormz
    rw [div_le_iff₀ hpmq]
    nlinarith [hnormz, hpqlt]
  -- The differentiability set `S` and the inverse homeomorphism `g = f⁻¹`.
  set S : Set ℂ := {z : ℂ | DifferentiableAt ℝ f z ∧ 0 < (fderiv ℝ f z).det} with hSdef
  have hSmeas : MeasurableSet S := by
    apply MeasurableSet.inter (measurableSet_of_differentiableAt ℝ f)
    exact measurableSet_lt measurable_const
      ((ContinuousLinearMap.continuous_det).measurable.comp (measurable_fderiv ℝ f))
  set g : ℂ → ℂ := ⇑(hhom.homeomorph f).symm with hg_def
  have hgf : ∀ z, g (f z) = z := (hhom.homeomorph f).symm_apply_apply
  have hg_cont : Continuous g := (hhom.homeomorph f).symm.continuous
  have hfderiv_S : ∀ z ∈ S, HasFDerivWithinAt f (fderiv ℝ f z) S z := fun z hz =>
    (hz.1.hasFDerivAt).hasFDerivWithinAt
  have hfinj_S : Set.InjOn f S := hhom.injective.injOn
  -- The exceptional (bad) and good subfamilies of `Γ`.
  set badProp : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hbadProp
  set Γbad : Set (ℝ → ℂ) := {γ ∈ Γ | badProp γ} with hΓbad
  set Γgood : Set (ℝ → ℂ) := Γ \ Γbad with hΓgood
  -- KEY: for every density `ρ` admissible for `Γ`,
  --   curveModulus ((f∘·)''Γgood) ≤ ofReal K * ∫⁻ ρ².
  have key : ∀ ρ : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ Γ →
      curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
        ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
    intro ρ ⟨hρmeas, hρadm⟩
    set wt : ℂ → ℝ≥0∞ := fun z =>
      ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (fderiv ℝ f z).det) with hwt_def
    have hwt_eq : ∀ z ∈ S, wt z =
        ENNReal.ofReal ‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ := by
      intro z hz
      rw [hwt_def, opNorm_inverse_eq_wirtinger f z hz.2]
    set σ : ℂ → ℝ≥0∞ := fun w =>
      (f '' S).indicator (fun w => ρ (g w) * wt (g w)) w with hσ_def
    have hfderivmeas : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    have hdzmeas : Measurable (fun z : ℂ => dz f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dz] using (measurable_const.mul ((h1.sub (measurable_const.mul h2))))
    have hdzbarmeas : Measurable (fun z : ℂ => dzbar f z) := by
      have h1 : Measurable (fun z : ℂ => (fderiv ℝ f z) 1) :=
        measurable_fderiv_apply_const ℝ f 1
      have h2 : Measurable (fun z : ℂ => (fderiv ℝ f z) Complex.I) :=
        measurable_fderiv_apply_const ℝ f Complex.I
      simpa only [dzbar] using (measurable_const.mul ((h1.add (measurable_const.mul h2))))
    have hdetmeas : Measurable (fun z : ℂ => (fderiv ℝ f z).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp hfderivmeas
    have hwtmeas : Measurable wt := by
      refine ENNReal.measurable_ofReal.comp ?_
      exact ((hdzmeas.norm.add hdzbarmeas.norm).div hdetmeas)
    have hfSmeas : MeasurableSet (f '' S) :=
      measurable_image_of_fderivWithin hSmeas hfderiv_S hfinj_S
    have hσmeas : Measurable σ := by
      refine (Measurable.indicator ?_ hfSmeas)
      exact (hρmeas.comp hg_cont.measurable).mul (hwtmeas.comp hg_cont.measurable)
    -- STEP 2.  Energy bound: ∫⁻ σ² ≤ ofReal K * ∫⁻ ρ².
    have henergy : ∫⁻ w, (σ w) ^ 2 ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := by
      have hσsq_ind : (fun w => (σ w) ^ 2)
          = (f '' S).indicator (fun w => (ρ (g w) * wt (g w)) ^ 2) := by
        funext w
        simp only [hσ_def]
        by_cases hw : w ∈ f '' S
        · simp only [Set.indicator_of_mem hw]
        · simp only [Set.indicator_of_notMem hw]; ring
      rw [hσsq_ind, lintegral_indicator hfSmeas]
      have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (volume : Measure ℂ) hSmeas hfderiv_S hfinj_S
        (fun w => (ρ (g w) * wt (g w)) ^ 2)
      rw [hcov]
      have hmono : ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := by
        refine setLIntegral_mono_ae' hSmeas ?_
        filter_upwards [hdil] with z hzdil hzS
        rw [hgf z, hwt_eq z hzS]
        have hdetpos : 0 < (fderiv ℝ f z).det := hzS.2
        rw [abs_of_pos hdetpos, mul_pow, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [show ENNReal.ofReal (fderiv ℝ f z).det *
              ((ρ z) ^ 2 * ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2))
            = (ρ z) ^ 2 * (ENNReal.ofReal (fderiv ℝ f z).det *
                ENNReal.ofReal (‖ContinuousLinearMap.inverse (fderiv ℝ f z)‖ ^ 2)) by ring]
        rw [← ENNReal.ofReal_mul hdetpos.le, mul_comm (ENNReal.ofReal K) ((ρ z) ^ 2)]
        gcongr
        rw [mul_comm]; exact hzdil
      calc ∫⁻ z in S, ENNReal.ofReal |(fderiv ℝ f z).det| *
              (ρ (g (f z)) * wt (g (f z))) ^ 2
          ≤ ∫⁻ z in S, ENNReal.ofReal K * (ρ z) ^ 2 := hmono
        _ = ENNReal.ofReal K * ∫⁻ z in S, (ρ z) ^ 2 := by
            rw [lintegral_const_mul _ (hρmeas.pow_const 2)]
        _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 :=
            mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    -- STEP 3.  `σ` is admissible for `(f∘·)''Γgood`.
    have hσadm : IsAdmissibleDensity σ ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood) := by
      refine ⟨hσmeas, ?_⟩
      rintro δ ⟨γ, hγgood, rfl⟩
      have hγΓ : γ ∈ Γ := hγgood.1
      have hnotbad : ¬ badProp γ := by
        intro hbad; exact hγgood.2 ⟨hγΓ, hbad⟩
      rw [hbadProp] at hnotbad
      obtain ⟨hAC, hdetγ, hchainγ⟩ := not_not.mp hnotbad
      have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ σ ((f ∘ γ) t) * (‖deriv (f ∘ γ) t‖₊ : ℝ≥0∞) := by
        filter_upwards [hdetγ, hchainγ] with t hdett₀ hchaint₀
        rcases eq_or_ne (deriv γ t) 0 with hd0 | hd0
        · simp [hd0]
        have hdett : 0 < (fderiv ℝ f (γ t)).det := hdett₀ hd0
        have hchaint : HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t :=
          hchaint₀ hd0
        set A : ℂ →L[ℝ] ℂ := fderiv ℝ f (γ t) with hA
        have hdett' : 0 < (fderiv ℝ f (γ t)).det := hdett
        have hγtS : γ t ∈ S := by
          refine ⟨?_, hdett'⟩
          by_contra hnd
          rw [fderiv_zero_of_not_differentiableAt hnd] at hdett'
          simp [ContinuousLinearMap.det] at hdett'
        have hAinv : A.IsInvertible :=
          ⟨A.toContinuousLinearEquivOfDetNeZero hdett.ne',
            A.coe_toContinuousLinearEquivOfDetNeZero hdett.ne'⟩
        have hderiv : deriv (f ∘ γ) t = A (deriv γ t) := hchaint.deriv
        have hfγtS : f (γ t) ∈ f '' S := ⟨γ t, hγtS, rfl⟩
        have hσval : σ ((f ∘ γ) t) = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ := by
          simp only [Function.comp_apply, hσ_def]
          rw [Set.indicator_of_mem hfγtS, hgf, hwt_eq (γ t) hγtS]
        rw [hσval, hderiv]
        have hkey : (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by
          have hself : A.inverse (A (deriv γ t)) = deriv γ t :=
            ContinuousLinearMap.IsInvertible.inverse_apply_self hAinv (deriv γ t)
          have hop : ‖deriv γ t‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ := by
            have hle : ‖A.inverse (A (deriv γ t))‖₊ ≤ ‖A.inverse‖₊ * ‖A (deriv γ t)‖₊ :=
              A.inverse.le_opNNNorm _
            rwa [hself] at hle
          have hcoe : ENNReal.ofReal ‖A.inverse‖ = (‖A.inverse‖₊ : ℝ≥0∞) := by
            rw [ofReal_norm_eq_enorm, enorm_eq_nnnorm]
          rw [hcoe, ← ENNReal.coe_mul]
          exact_mod_cast hop
        calc ρ (γ t) * (‖deriv γ t‖₊ : ℝ≥0∞)
            ≤ ρ (γ t) * (ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞)) := by
              gcongr
          _ = ρ (γ t) * ENNReal.ofReal ‖A.inverse‖ * (‖A (deriv γ t)‖₊ : ℝ≥0∞) := by ring
      have hint : arcLengthLineIntegral ρ γ ≤ arcLengthLineIntegral σ (f ∘ γ) := by
        unfold arcLengthLineIntegral
        exact lintegral_mono_ae hpoint
      exact le_trans (hρadm γ hγΓ) hint
    calc curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood)
        ≤ ∫⁻ w, (σ w) ^ 2 := iInf₂_le σ hσadm
      _ ≤ ENNReal.ofReal K * ∫⁻ z, (ρ z) ^ 2 := henergy
  -- Conclude: `curveModulus ((f∘·)''Γgood) ≤ ofReal K * curveModulus Γ` from `key`.
  have hKne0 : ENNReal.ofReal K ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hKnetop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
  change curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γgood) ≤ ENNReal.ofReal K * curveModulus Γ
  conv_rhs => rw [curveModulus, ENNReal.mul_iInf_of_ne hKne0 hKnetop]
  refine le_iInf fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne hKne0 hKnetop]
  refine le_iInf fun hρ => ?_
  exact key ρ hρ

/-- **The chain-rule exceptional image curves have zero modulus (geometric side).** For
a geometric `K`-quasiconformal map `f` and an arbitrary curve family `Γ`, the pushforward
of the chain-rule **exceptional** subfamily — those `γ ∈ Γ` for which `f ∘ γ` fails to be
absolutely continuous, or along which the differential of `f` is degenerate, or for which
the a.e. chain rule fails — has zero modulus.

This is the image-side length–area / Fuglede residual. On the analytic side the
corresponding image family is killed via the **inverse** map `g = f⁻¹` being itself
analytic-quasiconformal (`IsQCAnalytic.chainRule_exceptional_modulus_zero` applied to `g`,
inside `isQCGeometric_of_isQCAnalytic`); that route is unavailable here without circularity
(it would presuppose the full geometric/analytic equivalence). The genuine geometric
content is the planar image-side length–area inequality bounding the *image* arc length
over the degeneracy contact — the same wall recorded for the forward Lusin-(N) cluster as
`image_chainRule_exceptional_modulus_zero` (`QC/LengthArea.lean`, the 2-D image-modulus
length–area inequality absent from Mathlib). It is isolated here as the single residual of
the general distortion; the good part (`IsQCGeometric.pushforwardGood_modulus_le`) and the
assembly (`IsQCGeometric.curveModulus_image_le`) are proved against it in full. -/
theorem IsQCGeometric.image_chainRule_exceptional_modulus_zero {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (Γ : Set (ℝ → ℂ)) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) ''
      {γ ∈ Γ | ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
            AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
          (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
              deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
          ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
            HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t)}) = 0 := by
  sorry

/-- **The general curve-family distortion.** For a geometric `K`-quasiconformal map `f`,
the modulus of the pushforward family `(f ∘ ·) '' Γ` is at most `K` times the modulus of
`Γ`, for an arbitrary curve family `Γ`.

The pushforward image splits into the chain-rule **good** image part — bounded by
`K · curveModulus Γ` via the length–area energy transfer
(`IsQCGeometric.pushforwardGood_modulus_le`) — and the complementary chain-rule
**exceptional** image part, which has zero modulus
(`IsQCGeometric.image_chainRule_exceptional_modulus_zero`); removing the zero-modulus part
(`curveModulus_sdiff_modulus_zero`) and bounding the good part gives the claim. -/
theorem IsQCGeometric.curveModulus_image_le {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) (Γ : Set (ℝ → ℂ)) :
    curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ) ≤ ENNReal.ofReal K * curveModulus Γ := by
  classical
  -- The chain-rule bad subfamily of `Γ`, its complement, and the two image families.
  set badProp : (ℝ → ℂ) → Prop := fun γ =>
    ¬ ((∀ a c : ℝ, Set.uIcc a c ⊆ Set.Icc (0 : ℝ) 1 →
          AbsolutelyContinuousOnInterval (f ∘ γ) a c) ∧
      (∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
          deriv γ t ≠ 0 → 0 < (fderiv ℝ f (γ t)).det) ∧
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), deriv γ t ≠ 0 →
        HasDerivAt (f ∘ γ) ((fderiv ℝ f (γ t)) (deriv γ t)) t) with hbadProp
  set Γbad : Set (ℝ → ℂ) := {γ ∈ Γ | badProp γ} with hΓbad
  -- The image of `Γbad` has zero modulus.
  have hbadImg0 : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γbad) = 0 :=
    hf.image_chainRule_exceptional_modulus_zero Γ
  -- The image of the good part is bounded by `K · curveModulus Γ`.
  have hgoodImg_le : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' (Γ \ Γbad))
      ≤ ENNReal.ofReal K * curveModulus Γ := hf.pushforwardGood_modulus_le Γ
  -- The full image family splits as the union of these two pieces.
  have hsplit : (fun γ : ℝ → ℂ => f ∘ γ) '' Γ
      = (fun γ : ℝ → ℂ => f ∘ γ) '' (Γ \ Γbad) ∪ (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad := by
    rw [← Set.image_union, Set.diff_union_of_subset (Set.sep_subset _ _)]
  -- The bad image part is a zero-modulus subfamily of the full image; remove it.
  have hbadsub : (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad ⊆ (fun γ : ℝ → ℂ => f ∘ γ) '' Γ :=
    Set.image_mono (Set.sep_subset _ _)
  have hsdiff : curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ
        \ (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad)
      = curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ) :=
    curveModulus_sdiff_modulus_zero hbadsub hbadImg0
  -- After removing the (zero-modulus) bad image, the remainder is contained in the good image.
  have hremsub : (fun γ : ℝ → ℂ => f ∘ γ) '' Γ \ (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad
      ⊆ (fun γ : ℝ → ℂ => f ∘ γ) '' (Γ \ Γbad) := by
    rw [hsplit, Set.union_diff_right]
    exact Set.diff_subset
  calc curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ)
      = curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' Γ
          \ (fun γ : ℝ → ℂ => f ∘ γ) '' Γbad) := hsdiff.symm
    _ ≤ curveModulus ((fun γ : ℝ → ℂ => f ∘ γ) '' (Γ \ Γbad)) := curveModulus_mono hremsub
    _ ≤ ENNReal.ofReal K * curveModulus Γ := hgoodImg_le

/-! ## The horizontal slice set and the Fubini positivity lemma -/

/-- The **horizontal-height slice set** of a set `T ⊆ ℂ`: the heights `y` at which the
horizontal line `{⟨x, y⟩ : x}` meets `T` in a set of positive one-dimensional measure. -/
def heightSlicePos (T : Set ℂ) : Set ℝ :=
  {y : ℝ | 0 < volume {x : ℝ | Complex.mk x y ∈ T}}

/-- The set `U ⊆ ℝ × ℝ` obtained from `T ⊆ ℂ` by reading `⟨height, width⟩` as
`⟨p.1, p.2⟩` (so `Prod.mk y` slices are horizontal lines at height `y`). -/
private def heightProdSet (T : Set ℂ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | Complex.mk p.2 p.1 ∈ T}

private theorem measurableSet_heightProdSet {T : Set ℂ} (hT : MeasurableSet T) :
    MeasurableSet (heightProdSet T) := by
  have hmk : Measurable (fun p : ℝ × ℝ => Complex.mk p.1 p.2) :=
    Complex.measurableEquivRealProd.symm.measurable
  have : heightProdSet T = (fun p : ℝ × ℝ => Complex.mk p.2 p.1) ⁻¹' T := rfl
  rw [this]; exact (hmk.comp measurable_swap) hT

private theorem heightSlice_eq (T : Set ℂ) (y : ℝ) :
    Prod.mk y ⁻¹' (heightProdSet T) = {x : ℝ | Complex.mk x y ∈ T} := by
  ext x; simp [heightProdSet]

private theorem volume_heightProdSet {T : Set ℂ} (hT : MeasurableSet T) :
    (volume : Measure (ℝ × ℝ)) (heightProdSet T) = volume T := by
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
      (volume : Measure (ℝ × ℝ)) volume := Measure.measurePreserving_swap
  have hmp : MeasurePreserving
      (fun p : ℝ × ℝ => Complex.mk p.2 p.1) (volume : Measure (ℝ × ℝ)) volume := by
    have h1 : (fun p : ℝ × ℝ => Complex.mk p.2 p.1)
        = Complex.measurableEquivRealProd.symm ∘ Prod.swap := by funext p; rfl
    rw [h1]
    exact (Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).comp hswap
  have := hmp.measure_preimage (hT.nullMeasurableSet)
  simpa [heightProdSet, Set.preimage] using this

/-- The slice set of a measurable set is measurable. -/
theorem measurableSet_heightSlicePos {T : Set ℂ} (hT : MeasurableSet T) :
    MeasurableSet (heightSlicePos T) := by
  have hUmeas := measurableSet_heightProdSet hT
  have heq : heightSlicePos T
      = {y : ℝ | 0 < volume (Prod.mk y ⁻¹' (heightProdSet T))} := by
    ext y
    simp only [heightSlicePos, Set.mem_setOf_eq, heightSlice_eq]
  rw [heq]
  exact measurableSet_lt measurable_const (measurable_measure_prodMk_left hUmeas)

/-- **Fubini positivity.** If a measurable set `T ⊆ ℂ` has positive Lebesgue measure,
then its horizontal-height slice set `heightSlicePos T` has positive measure: positively
many heights cut `T` in a positive-length horizontal slice. (Contrapositive of
`measure_prod_null`: if a.e. slice were null, `T` would be null.) -/
theorem volume_heightSlicePos_pos {T : Set ℂ} (hT : MeasurableSet T)
    (hTpos : 0 < volume T) : 0 < volume (heightSlicePos T) := by
  by_contra hcon
  simp only [not_lt] at hcon
  have hzero : volume (heightSlicePos T) = 0 := le_antisymm hcon (zero_le _)
  -- a.e. height has a null slice
  have haenull : (fun y : ℝ => volume (Prod.mk y ⁻¹' (heightProdSet T))) =ᵐ[volume] 0 := by
    have hcompl : ∀ y ∉ heightSlicePos T,
        volume (Prod.mk y ⁻¹' (heightProdSet T)) = 0 := by
      intro y hy
      rw [heightSlice_eq]
      simp only [heightSlicePos, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy (zero_le _)
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(heightSlicePos T)ᶜ, ?_, fun y hy => hcompl y hy⟩
    rw [mem_ae_iff, compl_compl]; exact hzero
  have hUnull : (volume : Measure (ℝ × ℝ)) (heightProdSet T) = 0 := by
    rw [Measure.volume_eq_prod, Measure.measure_prod_null (measurableSet_heightProdSet hT)]
    exact haenull
  rw [volume_heightProdSet hT] at hUnull
  exact (ne_of_gt hTpos) hUnull

/-! ## The pullback contact residual

The second classical ingredient is the **absolute-continuity transport** of the
inverse homeomorphism `g = f⁻¹` on the horizontal segments that meet the image set
`f '' S` in positive length. A geometric quasiconformal map is `ACL` (absolutely
continuous on almost every line), and so is its inverse; consequently, on a horizontal
image segment `δ_y` meeting `f '' S` in a positive-length parameter set, the pulled-back
curve `g ∘ δ_y` is absolutely continuous with a.e. nonvanishing derivative on that
contact, so it accumulates *positive arc length inside the null set* `S`. Equivalently,
its `∞ · 𝟙_S`-weighted arc-length line integral is at least `1`.

This is exactly the ingredient that fails for the area-preserving singular shear and
the Minkowski-`?` map (whose slices are singular): it is the genuine ACL / no-singular-
part content of the geometric definition, and is the inverse-side analogue of the
forward chain-rule transport `pushforwardGood_modulus_le`. It is isolated here as the
second precise residual; everything downstream (the segment lower bound, the slice
Fubini, and the modulus contradiction) is proved against it. -/
theorem IsQCGeometric.pullback_segment_meetsNullSet {f : ℂ → ℂ} {K : ℝ}
    (hf : IsQCGeometric f K) {S : Set ℂ} (hSmeas : MeasurableSet S) (hSnull : volume S = 0)
    {a b : ℝ} (hab : a < b) {y : ℝ}
    (hcontact : 0 < volume {x : ℝ | Complex.mk x y ∈ f '' S ∧ a ≤ x ∧ x ≤ b}) :
    1 ≤ arcLengthLineIntegral (S.indicator (fun _ => ∞))
      (fun x : ℝ => ⇑(hf.2.1.isHomeomorph.homeomorph f).symm
        (Complex.mk (a + (b - a) * x) y)) := by
  sorry

/-! ## The per-square reduction -/

/-- **Per-square Lusin (N).** For a geometric `K`-QC map `f` and a measurable null set
`S`, the image `f '' S` meets every axis rectangle `R = (a, b) × (s, t)` in a null set.
The argument: if `volume (f '' S ∩ R) > 0`, then positively many heights `y` cut it in a
positive-length slice (`volume_heightSlicePos_pos`); the image horizontal segments at
those heights form a family of strictly positive modulus (`segmentFamily_modulus_ge`);
but each such segment is the `f`-image of the pulled-back curve `g ∘ δ_y`, which meets the
null set `S` (so the source family has modulus `0` by `curveModulus_meetsNullSet_zero`);
the general distortion `curveModulus_image_le` then forces the image-segment modulus to be
`≤ K · 0 = 0`, a contradiction. -/
theorem IsQCGeometric.lusinN_axisRect {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K)
    {S : Set ℂ} (hSmeas : MeasurableSet S) (hSnull : volume S = 0)
    {a b s t : ℝ} (hab : a < b) (_hst : s < t) :
    volume (f '' S ∩ axisRect a b s t) = 0 := by
  classical
  set g : ℂ → ℂ := ⇑(hf.2.1.isHomeomorph.homeomorph f).symm with hg
  have hfg : ∀ w, f (g w) = w := by
    intro w
    have := (hf.2.1.isHomeomorph.homeomorph f).apply_symm_apply w
    rwa [IsHomeomorph.homeomorph_apply] at this
  have hgf : ∀ z, g (f z) = z := fun z =>
    (hf.2.1.isHomeomorph.homeomorph f).symm_apply_apply z
  -- `f '' S` is measurable: `f '' S = g ⁻¹' S` and `g` is continuous.
  have hgcont : Continuous g := (hf.2.1.isHomeomorph.homeomorph f).continuous_symm
  have himgeq : f '' S = g ⁻¹' S := by
    ext w; constructor
    · rintro ⟨p, hp, rfl⟩; rw [Set.mem_preimage, hgf]; exact hp
    · intro hw; exact ⟨g w, hw, hfg w⟩
  have hfSmeasSet : MeasurableSet (f '' S) := by
    rw [himgeq]; exact hgcont.measurable hSmeas
  set T : Set ℂ := f '' S ∩ axisRect a b s t with hT
  have hTmeas : MeasurableSet T := hfSmeasSet.inter (measurableSet_axisRect a b s t)
  by_contra hcon
  have hTpos : 0 < volume T := pos_iff_ne_zero.mpr hcon
  -- Positively many heights cut `T` in a positive-length slice.
  have hYpos : 0 < volume (heightSlicePos T) := volume_heightSlicePos_pos hTmeas hTpos
  set Y : Set ℝ := heightSlicePos T with hY
  have hYmeas : MeasurableSet Y := measurableSet_heightSlicePos hTmeas
  -- The image segment family over `Y`.
  set Δ : Set (ℝ → ℂ) :=
    {γ : ℝ → ℂ | ∃ y ∈ Y, γ = fun x : ℝ => Complex.mk (a + (b - a) * x) y} with hΔ
  -- Lower bound: `M(Δ) ≥ volume Y · (1/(b-a)) > 0`.
  have hΔlb : (volume Y) * ENNReal.ofReal (1 / (b - a)) ≤ curveModulus Δ :=
    segmentFamily_modulus_ge hab hYmeas
  have hΔpos : 0 < curveModulus Δ := by
    refine lt_of_lt_of_le ?_ hΔlb
    apply ENNReal.mul_pos
    · exact ne_of_gt hYpos
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : (0:ℝ) < b - a := by linarith
      positivity
  -- The source family: pulled-back segments meeting `S`.
  set ΓS : Set (ℝ → ℂ) :=
    {γ : ℝ → ℂ | 1 ≤ arcLengthLineIntegral (S.indicator (fun _ => ∞)) γ} with hΓS
  have hΓSzero : curveModulus ΓS = 0 := by
    have := curveModulus_meetsNullSet_zero hSmeas hSnull Set.univ
    simpa [hΓS, Set.sep_univ] using this
  -- `Δ ⊆ (f ∘ ·) '' ΓS`: each image segment is `f ∘ (g ∘ δ_y)` with `g ∘ δ_y ∈ ΓS`.
  have hsub : Δ ⊆ (fun γ : ℝ → ℂ => f ∘ γ) '' ΓS := by
    rintro γ ⟨y, hyY, rfl⟩
    -- the pulled-back curve
    set γS : ℝ → ℂ := fun x : ℝ => g (Complex.mk (a + (b - a) * x) y) with hγS
    refine ⟨γS, ?_, ?_⟩
    · -- `γS ∈ ΓS`: meets `S` with `ALI ≥ 1`, from the contact residual.
      rw [hΓS, Set.mem_setOf_eq]
      -- The contact set in the slice has positive measure.
      have hcontact : 0 < volume
          {x : ℝ | Complex.mk x y ∈ f '' S ∧ a ≤ x ∧ x ≤ b} := by
        -- The slice of `T` (which is `f''S ∩ R`) at height `y` lies in this set.
        have hyY' : y ∈ heightSlicePos T := hyY
        have hslice : 0 < volume {x : ℝ | Complex.mk x y ∈ T} := hyY'
        refine lt_of_lt_of_le hslice (measure_mono ?_)
        intro x hx
        simp only [hT, Set.mem_setOf_eq, Set.mem_inter_iff] at hx ⊢
        obtain ⟨hxS, hxR⟩ := hx
        refine ⟨hxS, ?_, ?_⟩
        · exact hxR.1.1
        · exact hxR.1.2
      have := hf.pullback_segment_meetsNullSet hSmeas hSnull hab (y := y) hcontact
      simpa [hγS, hg] using this
    · -- `f ∘ γS = δ_y`.
      funext x
      simp only [Function.comp_apply, hγS, hfg]
  -- Combine: `M(Δ) ≤ M((f∘·)''ΓS) ≤ K · M(ΓS) = 0`, contradicting `M(Δ) > 0`.
  have hchain : curveModulus Δ ≤ ENNReal.ofReal K * curveModulus ΓS :=
    le_trans (curveModulus_mono hsub) (hf.curveModulus_image_le ΓS)
  rw [hΓSzero, mul_zero] at hchain
  exact (lt_irrefl 0) (lt_of_lt_of_le hΔpos hchain)

/-! ## The main theorem: Lusin's condition (N) -/

/-- **Lusin's condition (N) for geometric quasiconformal maps.** A geometric
`K`-quasiconformal map `f : ℂ → ℂ` maps Lebesgue-null sets to Lebesgue-null sets:
`volume S = 0 → volume (f '' S) = 0`.

The plane is exhausted by the countable family of integer-corner unit squares; on each,
the image `f '' S` is null by the per-square reduction `IsQCGeometric.lusinN_axisRect`,
and a countable union of null sets is null. -/
theorem IsQCGeometric.lusinN {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∀ S : Set ℂ, volume S = 0 → volume (f '' S) = 0 := by
  intro S hSnull
  -- Replace `S` by a measurable null superset; the image of `S` lies in the image of `S'`.
  obtain ⟨S', hSS', hS'meas, hS'null⟩ := exists_measurable_superset_of_null hSnull
  -- It suffices to show `volume (f '' S') = 0`, since `f '' S ⊆ f '' S'`.
  suffices h : volume (f '' S') = 0 by
    refine le_antisymm ?_ (zero_le _)
    calc volume (f '' S) ≤ volume (f '' S') := measure_mono (Set.image_mono hSS')
      _ = 0 := h
  -- Exhaust the plane by integer-corner unit squares indexed by `ℤ × ℤ`.
  have hcover : (Set.univ : Set ℂ)
      ⊆ ⋃ nm : ℤ × ℤ, axisRect (nm.1 : ℝ) ((nm.1 : ℝ) + 1) (nm.2 : ℝ) ((nm.2 : ℝ) + 1) := by
    intro z _
    rw [Set.mem_iUnion]
    refine ⟨(⌊z.re⌋, ⌊z.im⌋), ?_⟩
    simp only [axisRect, Set.mem_setOf_eq]
    refine ⟨⟨Int.floor_le z.re, ?_⟩, ⟨Int.floor_le z.im, ?_⟩⟩
    · exact le_of_lt (Int.lt_floor_add_one z.re)
    · exact le_of_lt (Int.lt_floor_add_one z.im)
  -- `f '' S'` lies in the countable union of its square-slices.
  have hsub : f '' S'
      ⊆ ⋃ nm : ℤ × ℤ, (f '' S' ∩ axisRect (nm.1 : ℝ) ((nm.1 : ℝ) + 1)
          (nm.2 : ℝ) ((nm.2 : ℝ) + 1)) := by
    intro w hw
    have hwu : w ∈ ⋃ nm : ℤ × ℤ, axisRect (nm.1 : ℝ) ((nm.1 : ℝ) + 1)
        (nm.2 : ℝ) ((nm.2 : ℝ) + 1) := hcover (Set.mem_univ w)
    rw [Set.mem_iUnion] at hwu ⊢
    obtain ⟨nm, hnm⟩ := hwu
    exact ⟨nm, hw, hnm⟩
  -- Each square-slice is null by the per-square reduction.
  have hpiece : ∀ nm : ℤ × ℤ, volume (f '' S' ∩ axisRect (nm.1 : ℝ) ((nm.1 : ℝ) + 1)
      (nm.2 : ℝ) ((nm.2 : ℝ) + 1)) = 0 := by
    intro nm
    exact hf.lusinN_axisRect hS'meas hS'null (by linarith) (by linarith)
  -- A countable union of null sets is null.
  refine le_antisymm ?_ (zero_le _)
  calc volume (f '' S')
      ≤ volume (⋃ nm : ℤ × ℤ, (f '' S' ∩ axisRect (nm.1 : ℝ) ((nm.1 : ℝ) + 1)
          (nm.2 : ℝ) ((nm.2 : ℝ) + 1))) := measure_mono hsub
    _ ≤ ∑' nm : ℤ × ℤ, volume (f '' S' ∩ axisRect (nm.1 : ℝ) ((nm.1 : ℝ) + 1)
          (nm.2 : ℝ) ((nm.2 : ℝ) + 1)) := measure_iUnion_le _
    _ = 0 := by simp only [hpiece, tsum_zero]

end RiemannDynamics

