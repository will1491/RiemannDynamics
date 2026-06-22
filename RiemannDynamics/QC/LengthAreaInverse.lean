/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.LengthArea
import RiemannDynamics.QC.ConditionNToACL
import RiemannDynamics.Analysis.Sobolev.SobolevToACL

/-!
# Length–area / Lusin-N⁺ for the quasiconformal inverse

This file builds the classical **length–area** development needed to close the
keystone `IsQCAnalytic.inverse_acl_weakGradient` (`QC/InverseQC.lean`): the inverse
homeomorphism `g = f⁻¹` of an analytic-quasiconformal map is absolutely continuous
on almost every line with `L²_loc` partials (Väisälä §31.2 / Lehto–Virtanen).

The load-bearing classical content is the **absolute continuity of the image area**
(Lusin condition N⁺) under the modulus / dilatation bound. The *correctness*
discipline here is sharp: a.e.-differentiability of a homeomorphism is **not**
enough to force ACL — the Minkowski-`?` map `g(x + iy) = ?(x) + iy` (`?` the
strictly-increasing singular Cantor function) is continuous, injective,
a.e.-differentiable, with finite line integrals, yet `g ∘ γ` fails to be absolutely
continuous on horizontal lines. Absolute continuity must therefore come from the
area's absolute continuity (condition N⁺), never from pointwise differentiability
alone. Every statement below is sanity-checked against this obstruction.

## Contents

* `fderiv_normSq_le_K_mul_det` — **dilatation inequality** (pure linear algebra,
  PROVEN): for `f : ℂ → ℂ` with `det (Df z) > 0` and Beltrami bound
  `‖∂̄f z‖ ≤ c · ‖∂f z‖` (`0 ≤ c < 1`), one has
  `‖Df z‖² ≤ ((1 + c)/(1 − c)) · det (Df z)`. The reciprocal-side inequality
  `‖(Df)⁻¹‖² · det ≤ (1 + c)/(1 − c)` that the inverse map consumes follows from the
  same Wirtinger identities applied to the inverse differential.

* `inverse_fderiv_normSq_le_K_mul_det` — the **inverse-side** dilatation inequality
  (PROVEN): `‖Dg w‖² ≤ K · det (Dg w)` where `Dg w = (Df (g w))⁻¹`, so the pointwise
  derivative of `g` already has `L²`-controlled size *relative to its Jacobian*.

* `lengthArea_modulus_lower_bound` — the **length–area inequality** (classical,
  PROVEN): a rectangle's horizontal-segment family has modulus at least
  `(height)/(width)`. This is the Cauchy–Schwarz lower bound for the modulus that
  drives the reverse length–area method.

* `IsQCAnalytic.inverse_conditionNPlus` — **condition N⁺** for the inverse (PROVEN,
  through the forward map `f`): the image of a null set under `g = f⁻¹` is null. The
  genuine analytic core where the Minkowski-`?` obstruction is defeated (via the
  forward map's a.e. positive-Jacobian differentiability and the inverse relation).

* `acl_weakGradient_of_conditionNPlus` — the **ACL extraction** (PROVEN; converse
  Sobolev embedding `W^{1,1}_loc ⇒ ACL`): a continuous map whose `L²_loc` partials are
  its **weak (distributional)** derivatives is ACL with those partials. The
  weak-gradient hypothesis is genuinely necessary — pointwise a.e. data (condition N⁺
  + pointwise dilatation/L²) is insufficient (the area-preserving singular shear is a
  counterexample); see that theorem's docstring.

* `acl_weakGradient_of_qcInverse` — the keystone assembly, taking the inverse-map
  dilatation/Jacobian data plus the genuine weak gradient (supplied by
  `IsQCAnalytic.inverse_memW12loc` at the caller) and producing ACL with `L²_loc`
  partials.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace RiemannDynamics

/-! ## The dilatation inequality (pure linear algebra) -/

/-- **Dilatation inequality.** If the real Jacobian determinant of `f : ℂ → ℂ` at
`z` is positive and the Beltrami bound `‖∂̄f z‖ ≤ c · ‖∂f z‖` holds with `0 ≤ c < 1`,
then the squared operator norm of the differential is controlled by its Jacobian:
`‖Df z‖² ≤ ((1 + c)/(1 − c)) · det (Df z)`.

This is the source-side dilatation inequality. It is sound (sanity check: for the
Minkowski-`?` map the differential is *not* a.e. positive-determinant, so this
hypothesis genuinely excludes it). The proof is the singular-value algebra:
`‖Df‖ = ‖∂f‖ + ‖∂̄f‖`, `det (Df) = ‖∂f‖² − ‖∂̄f‖² = (‖∂f‖ + ‖∂̄f‖)(‖∂f‖ − ‖∂̄f‖)`, so
`‖Df‖²/det = (‖∂f‖ + ‖∂̄f‖)/(‖∂f‖ − ‖∂̄f‖) ≤ (1 + c)/(1 − c)`. -/
theorem fderiv_normSq_le_K_mul_det (f : ℂ → ℂ) (z : ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hdet : 0 < (fderiv ℝ f z).det)
    (hbel : ‖dzbar f z‖ ≤ c * ‖dz f z‖) :
    ‖fderiv ℝ f z‖ ^ 2 ≤ ((1 + c) / (1 - c)) * (fderiv ℝ f z).det := by
  set p : ℝ := ‖dz f z‖ with hp
  set q : ℝ := ‖dzbar f z‖ with hq
  have hpnn : 0 ≤ p := norm_nonneg _
  have hqnn : 0 ≤ q := norm_nonneg _
  -- The two singular-value identities.
  have hopn : ‖fderiv ℝ f z‖ = p + q := opNorm_fderiv_eq_wirtinger f z
  have hdetval : (fderiv ℝ f z).det = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger f z
  -- From positive determinant: `q < p`, in particular `p > 0`.
  rw [hdetval] at hdet
  have hqp : q < p := by nlinarith [sq_nonneg (p - q), sq_nonneg (p + q)]
  have hppos : 0 < p := lt_of_le_of_lt hqnn hqp
  -- Positivity of the denominator `1 − c`.
  have hden : 0 < 1 - c := by linarith
  -- Rewrite the goal entirely in terms of `p, q, c`.
  rw [hopn, hdetval]
  -- `det = (p + q)(p − q)`, and `(p + q)² ≤ ((1+c)/(1−c)) (p + q)(p − q)`
  -- ⟺ `(1 − c)(p + q) ≤ (1 + c)(p − q)` (after cancelling the positive `p + q`),
  -- ⟺ `q ≤ c p`, which is `hbel`.
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  have hbel' : q ≤ c * p := hbel
  have hsum_pos : 0 < p + q := by linarith
  nlinarith [hsum_pos, hbel', mul_nonneg hc0 hpnn]

/-- **Inverse-side dilatation inequality.** Let `g` be a map whose differential at
`w` is the inverse of `Df (g w)` (the easy inverse-function-theorem situation), with
`det (Df (g w)) > 0` and source Beltrami bound `‖∂̄f (g w)‖ ≤ c · ‖∂f (g w)‖`,
`0 ≤ c < 1`. Then the differential of `g` satisfies the same dilatation inequality
`‖Dg w‖² ≤ ((1 + c)/(1 − c)) · det (Dg w)`, with the *same* constant.

This is the inverse-map dilatation control. It says the pointwise derivative of `g`
is `L²`-controlled by the Jacobian of `g`; combined with condition N⁺ (which gives
`∫ det (Dg) < ∞` locally) it yields `L²_loc` partials for `g`. The constant is
preserved because a real-linear map and its inverse have reciprocal singular values,
so `‖A⁻¹‖² / det (A⁻¹) = ‖A‖² / det (A)` is invariant. -/
theorem inverse_fderiv_normSq_le_K_mul_det {f g : ℂ → ℂ} {w : ℂ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hdet : 0 < (fderiv ℝ f (g w)).det)
    (hbel : ‖dzbar f (g w)‖ ≤ c * ‖dz f (g w)‖)
    (hgderiv : fderiv ℝ g w = ContinuousLinearMap.inverse (fderiv ℝ f (g w))) :
    ‖fderiv ℝ g w‖ ^ 2 ≤ ((1 + c) / (1 - c)) * (fderiv ℝ g w).det := by
  classical
  -- Abbreviations for the source singular values.
  set p : ℝ := ‖dz f (g w)‖ with hp
  set q : ℝ := ‖dzbar f (g w)‖ with hq
  have hpnn : 0 ≤ p := norm_nonneg _
  have hqnn : 0 ≤ q := norm_nonneg _
  -- The source identities.
  have hdetf : (fderiv ℝ f (g w)).det = p ^ 2 - q ^ 2 := det_fderiv_eq_wirtinger f (g w)
  -- From positive determinant: `q < p`, `p > 0`.
  have hdetpos' : 0 < p ^ 2 - q ^ 2 := by rw [← hdetf]; exact hdet
  have hqp : q < p := by nlinarith [sq_nonneg (p - q), sq_nonneg (p + q)]
  have hppos : 0 < p := lt_of_le_of_lt hqnn hqp
  have hden : 0 < 1 - c := by linarith
  -- The continuous-linear-equivalence built from the nonvanishing determinant of `Df`.
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hA
  have hdetne : A.det ≠ 0 := ne_of_gt hdet
  set e : ℂ ≃L[ℝ] ℂ := A.toContinuousLinearEquivOfDetNeZero hdetne with he
  have hecoe : (e : ℂ →L[ℝ] ℂ) = A :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero A hdetne
  -- `inverse A = ↑e.symm`, hence `Dg w = ↑e.symm`.
  have hinv_eq : ContinuousLinearMap.inverse A = (e.symm : ℂ →L[ℝ] ℂ) := by
    rw [← hecoe]; exact ContinuousLinearMap.inverse_equiv e
  have hgderiv' : fderiv ℝ g w = (e.symm : ℂ →L[ℝ] ℂ) := by rw [hgderiv, hA, hinv_eq]
  -- The operator norm of the inverse differential (`opNorm_inverse_eq_wirtinger`).
  have hopninv : ‖ContinuousLinearMap.inverse A‖ = (p + q) / A.det := by
    rw [hA, hp, hq]; exact opNorm_inverse_eq_wirtinger f (g w) hdet
  have hnormg : ‖fderiv ℝ g w‖ = (p + q) / A.det := by
    rw [hgderiv', ← hinv_eq]; exact hopninv
  -- `det (Dg w) = (det A)⁻¹` via `det_coe_symm`.
  have hdetg : (fderiv ℝ g w).det = (A.det)⁻¹ := by
    rw [hgderiv', ContinuousLinearEquiv.det_coe_symm, hecoe]
  -- Reduce the goal to the source dilatation inequality.
  rw [hnormg, hdetg, hdetf]
  -- Now: `((p+q)/(p²−q²))² ≤ ((1+c)/(1−c)) · (p²−q²)⁻¹`.
  have hsum_pos : 0 < p + q := by linarith
  have hdiff_pos : 0 < p - q := by linarith
  have hsq_pos : 0 < p ^ 2 - q ^ 2 := hdetpos'
  have hbel' : q ≤ c * p := hbel
  have hfac : p ^ 2 - q ^ 2 = (p + q) * (p - q) := by ring
  -- It suffices to prove `(1−c)(p+q) ≤ (1+c)(p−q)`, i.e. `q ≤ c p`.
  have hkey : (1 - c) * (p + q) ≤ (1 + c) * (p - q) := by nlinarith [hbel', hpnn, hqnn]
  -- Both sides share the positive denominator `(1−c)·(p²−q²)·(p−q)`. Reduce by `sub_nonneg`.
  rw [← sub_nonneg]
  have hpq_ne : (p ^ 2 - q ^ 2) ≠ 0 := ne_of_gt hsq_pos
  have hd_ne : (1 - c) ≠ 0 := ne_of_gt hden
  have hdiff_ne : (p - q) ≠ 0 := ne_of_gt hdiff_pos
  have hcommon : (1 + c) / (1 - c) * (p ^ 2 - q ^ 2)⁻¹ - ((p + q) / (p ^ 2 - q ^ 2)) ^ 2
      = ((1 + c) * (p - q) - (1 - c) * (p + q)) / ((1 - c) * (p ^ 2 - q ^ 2) * (p - q)) := by
    rw [div_pow]
    field_simp
    ring
  rw [hcommon]
  apply div_nonneg
  · linarith [hkey]
  · positivity

/-! ## The length–area inequality (classical) -/

/-- **Length–area inequality** (classical; the converse direction of the modulus /
length–area method). For an axis-aligned rectangle `R = (a, b) × (s, t)` in the
plane, the family `Γ` of horizontal segments crossing `R` (the curves
`x ↦ ⟨x, y⟩`, `x ∈ [a, b]`, indexed by `y ∈ [s, t]`) has modulus bounded below by
the rectangle height over its width:
`(t − s)/(b − a) ≤ curveModulus Γ`.

This is the Cauchy–Schwarz lower bound `(∫ ρ)² ≤ (length) · (∫ ρ²)` integrated over
the rectangle: every admissible `ρ` satisfies `1 ≤ ∫ ρ` along each segment, so by
Cauchy–Schwarz and Fubini `(t − s) ≤ ∫∫_R ρ² · (b − a)`, giving the bound. It is the
sound, true lower bound the reverse length–area extraction rests on.

PROVEN: the Cauchy–Schwarz/Fubini argument over the rectangle (admissibility gives
`1 ≤ ∫ ρ` along each horizontal segment; Cauchy–Schwarz and Fubini upgrade to the
area bound) is carried out in full below. -/
theorem lengthArea_modulus_lower_bound {a b s t : ℝ} (hab : a < b) (hst : s < t) :
    ENNReal.ofReal ((t - s) / (b - a))
      ≤ curveModulus {γ : ℝ → ℂ |
          ∃ y ∈ Set.Icc s t, γ = fun x : ℝ => Complex.mk (a + (b - a) * x) y} := by
  have hbma : (0:ℝ) < b - a := by linarith
  have htms : (0:ℝ) < t - s := by linarith
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
  have hper : ∀ y ∈ Set.Icc s t,
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
        set f : ℝ → ℝ := fun x => a + (b - a) * x with hf
        have himg : f '' (Set.Icc 0 1) = Set.Icc a b := by
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
        have hderivf : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt f (b - a) (Set.Icc 0 1) x := by
          intro x hx
          have : HasDerivAt f (b - a) x := by
            have h1 : HasDerivAt (fun x : ℝ => (b - a) * x) (b - a) x := by
              simpa only [mul_one] using (hasDerivAt_id x).const_mul (b - a)
            simpa only [zero_add] using (hasDerivAt_const x a).add h1
          exact this.hasDerivWithinAt
        have hinj : Set.InjOn f (Set.Icc 0 1) := by
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
  -- ===== STEP C: integrate the per-y bound over y ∈ [s,t] =====
  have hlhs : ENNReal.ofReal ((t - s) / (b - a))
      = ENNReal.ofReal (t - s) * ENNReal.ofReal (1/(b-a)) := by
    rw [← ENNReal.ofReal_mul htms.le]; congr 1; field_simp
  have hconst : ∫⁻ (_ : ℝ) in Set.Icc s t, ENNReal.ofReal (1/(b-a))
      = ENNReal.ofReal (t - s) * ENNReal.ofReal (1/(b-a)) := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, mul_comm]
  rw [hlhs, ← hconst, harea]
  calc ∫⁻ (_ : ℝ) in Set.Icc s t, ENNReal.ofReal (1/(b-a))
      ≤ ∫⁻ y : ℝ in Set.Icc s t, ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 := by
        refine setLIntegral_mono_ae' measurableSet_Icc ?_
        filter_upwards with y hy using hper y hy
    _ ≤ ∫⁻ y : ℝ, ∫⁻ u : ℝ in Set.Icc a b, (ρ (Complex.mk u y))^2 :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ y : ℝ, ∫⁻ u : ℝ, (ρ (Complex.mk u y))^2 := by
        exact lintegral_mono (fun y => setLIntegral_le_lintegral _ _)

/-! ## Condition N⁺ for the inverse (the genuine analytic core) -/

/-- **Condition N⁺ for the quasiconformal inverse** (the load-bearing classical
content), proved through the *forward* quasiconformal map `f`. For `f : ℂ → ℂ` with
`hf : IsQCAnalytic f b`, its inverse homeomorphism `g = ⇑(hf.1.1.homeomorph f).symm`
maps Lebesgue-null sets to Lebesgue-null sets: for every null `S`,
`volume (g '' S) = 0`.

Equivalently, the area `w ↦ det (Dg w)` is an absolutely continuous density for the
pushforward — the image area has no singular part. **This is exactly the property
the Minkowski-`?` map fails**: `?` smears a unit of length (hence, in the product
map, a unit of area) onto the null Cantor set, so its image area is *not* absolutely
continuous and `?` violates condition N⁺. Here the structure of the *forward* map
`f` is what rules this out: `f` is differentiable with positive Jacobian almost
everywhere (`hf.1.2` / `IsQCAnalytic.ae_differentiableAt`), so the inverse-function
theorem forces `g` to inherit a genuine a.e. differential, leaving no singular part.

The statement carries the forward map deliberately: pointwise a.e. quasiconformality
of `g` alone does *not* imply Lusin condition (N) (the Minkowski-`?` obstruction),
so the proof must use the global inverse-function-theorem structure of `f`.

**Non-circular proof.** Split `S = (S ∩ D) ∪ (S ∩ Dᶜ)` along the
differentiability set `D = {w | DifferentiableAt ℝ g w}`:
* On `S ∩ D` the map `g` is differentiable, so the differentiable-map null-image
  theorem `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` gives a null
  image.
* On `S ∩ Dᶜ ⊆ Dᶜ` we use the *forward* map: `g '' Dᶜ = f ⁻¹' Dᶜ` (since `f`, `g` are
  mutual inverses), and `f ⁻¹' Dᶜ ⊆ {z | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < det (Df z)}`
  by the easy half of the inverse function theorem (wherever `f` is differentiable at
  `z` with positive Jacobian, `g` is differentiable at `f z`). That degeneracy set is
  null by `IsQCAnalytic.ae_differentiableAt` and `hf.1.2`, so `g '' Dᶜ` is null.
This uses **only** the forward map `f`'s a.e. positive-Jacobian differentiability and
the inverse-relation; it never assumes Lusin-(N) for `g`. -/
theorem IsQCAnalytic.inverse_conditionNPlus {f : ℂ → ℂ} {b : BeltramiCoeff}
    (hf : IsQCAnalytic f b) :
    ∀ S : Set ℂ, volume S = 0 → volume ((⇑(hf.1.1.homeomorph f).symm) '' S) = 0 := by
  classical
  -- The inverse homeomorphism `g = f⁻¹` and the mutual-inverse relations.
  set g : ℂ → ℂ := ⇑(hf.1.1.homeomorph f).symm with hg
  have hfwd : ∀ z, (hf.1.1.homeomorph f) z = f z := fun z =>
    IsHomeomorph.homeomorph_apply f hf.1.1 z
  have hfg : ∀ w, f (g w) = w := fun w => by
    rw [hg, ← hfwd ((hf.1.1.homeomorph f).symm w)]
    exact (hf.1.1.homeomorph f).apply_symm_apply w
  have hgf : ∀ z, g (f z) = z := fun z => by
    rw [hg, ← hfwd z]
    exact (hf.1.1.homeomorph f).symm_apply_apply z
  have hgcont : Continuous g := (hf.1.1.homeomorph f).continuous_symm
  -- The differentiability set `D` of `g` (measurable).
  set D : Set ℂ := {w : ℂ | DifferentiableAt ℝ g w} with hD
  have hDmeas : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  -- The degeneracy set of the forward map `f`, which is null.
  set E : Set ℂ := {z : ℂ | ¬ DifferentiableAt ℝ f z ∨ ¬ 0 < (fderiv ℝ f z).det} with hE
  have hEnull : volume E = 0 := by
    have hdiffnull : volume {z : ℂ | ¬ DifferentiableAt ℝ f z} = 0 :=
      MeasureTheory.ae_iff.mp (IsQCAnalytic.ae_differentiableAt hf)
    have hdetnull : volume {z : ℂ | ¬ 0 < (fderiv ℝ f z).det} = 0 := by
      rw [← ae_iff]; exact hf.1.2
    have hsub : E ⊆ {z : ℂ | ¬ DifferentiableAt ℝ f z} ∪ {z : ℂ | ¬ 0 < (fderiv ℝ f z).det} := by
      intro z hz; exact hz
    exact measure_mono_null hsub (measure_union_null hdiffnull hdetnull)
  -- KEY: `g '' Dᶜ ⊆ E`, hence `volume (g '' Dᶜ) = 0`.
  -- For `w ∉ D` (i.e. `g` not differentiable at `w`), `g w ∈ E`: otherwise `f` is
  -- differentiable at `g w` with positive Jacobian, and the easy inverse function
  -- theorem makes `g` differentiable at `w = f (g w)`, a contradiction.
  have hsingular : g '' Dᶜ ⊆ E := by
    rintro _ ⟨w, hwD, rfl⟩
    by_contra hgwE
    -- `g w ∉ E` means `f` is differentiable at `g w` with positive Jacobian.
    rw [hE, Set.mem_setOf_eq, not_or, not_not, not_not] at hgwE
    obtain ⟨hdiff, hdetpos⟩ := hgwE
    -- Build the linear equivalence from the nonvanishing determinant of `Df (g w)`.
    set f' : ℂ →L[ℝ] ℂ := fderiv ℝ f (g w) with hf'
    have hdetne : f'.det ≠ 0 := ne_of_gt hdetpos
    set e : ℂ ≃L[ℝ] ℂ := f'.toContinuousLinearEquivOfDetNeZero hdetne with he
    have hecoe : (e : ℂ →L[ℝ] ℂ) = f' :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero f' hdetne
    have hfderiv : HasFDerivAt f (e : ℂ →L[ℝ] ℂ) (g w) := by
      rw [hecoe]; exact hdiff.hasFDerivAt
    have hloc : ∀ᶠ y in nhds w, f (g y) = y := Filter.Eventually.of_forall hfg
    -- The easy half of the inverse function theorem: `g` is differentiable at `w`.
    have hgfderiv : HasFDerivAt g (e.symm : ℂ →L[ℝ] ℂ) w :=
      HasFDerivAt.of_local_left_inverse hgcont.continuousAt hfderiv hloc
    -- But `w ∉ D` says `g` is *not* differentiable at `w`.
    exact hwD hgfderiv.differentiableAt
  have hsingular_null : volume (g '' Dᶜ) = 0 := measure_mono_null hsingular hEnull
  -- Now the main split, for an arbitrary null `S`.
  intro S hS
  -- `S = (S ∩ D) ∪ (S ∩ Dᶜ)`, hence `g '' S = g '' (S ∩ D) ∪ g '' (S ∩ Dᶜ)`.
  have hSsplit : g '' S = g '' (S ∩ D) ∪ g '' (S ∩ Dᶜ) := by
    rw [← Set.image_union, ← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  rw [hSsplit]
  refine measure_union_null ?_ ?_
  · -- Differentiable part: `g` is differentiable on `S ∩ D` (null), so its image is null.
    have hSDnull : volume (S ∩ D) = 0 := measure_mono_null Set.inter_subset_left hS
    have hgdiffOn : DifferentiableOn ℝ g (S ∩ D) := fun w hw => hw.2.differentiableWithinAt
    exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hgdiffOn hSDnull
  · -- Singular part: `g '' (S ∩ Dᶜ) ⊆ g '' Dᶜ`, which is null.
    exact measure_mono_null (Set.image_mono Set.inter_subset_right) hsingular_null

/-! ## ACL extraction from condition N⁺ -/

/-- **ACL from the weak gradient (Sobolev ⇒ ACL).** A continuous map `g : ℂ → ℂ` with
`L²_loc` partials `gx`, `gy` that are its **weak (distributional) directional
derivatives** (`hweakx : HasWeakDirDeriv 1 gx g univ`,
`hweaky : HasWeakDirDeriv I gy g univ`) is absolutely continuous on almost every
horizontal and vertical line, with `gx`, `gy` as the classical line-partials. This is
the converse Sobolev embedding `W^{1,1}_loc ⇒ ACL` (Nikodym; Evans–Gariepy §4.9.2),
**fully proven** here from the weak-gradient hypotheses.

**⚠ Why the weak-gradient hypothesis is genuinely needed (correctness fix, 2026-06-20).**
It is a *false* route to derive ACL from condition N⁺ together with merely *pointwise*
a.e. data. Condition N⁺ (`E ↦ volume (g '' E)` absolutely continuous) constrains only
the **Jacobian / swept area**, never the off-diagonal *tangential* partial, whose
**distributional** part can be singular while its **pointwise a.e.** value is harmless.
The decisive counterexample is the **area-preserving singular shear**
`g ⟨x, y⟩ = x + i·(y + s x)` with `s` a continuous strictly-increasing singular
function (e.g. Minkowski `?`): it is injective, continuous, a.e.-differentiable with
`Dg = id` a.e., hence **measure-preserving** (so it satisfies condition N⁺, the
pointwise dilatation bound `‖Dg‖² ≤ K·det`, and has `L²_loc` *pointwise* partials), yet
every horizontal slice's imaginary part `y + s ·` is **singular (not AC)**. So
{injective, continuous, a.e.-diff, N⁺, pointwise dilatation/L²} is **insufficient** for
ACL. The honest extra ingredient is exactly that `gx`/`gy` be the *weak* derivatives —
i.e. `g ∈ W^{1,1}_loc` — which the shear fails (`∂ₓ(g.im)` is the singular measure `ds`,
not the a.e.-pointwise `0`). For the quasiconformal inverse this holds genuinely via
`MemW12loc` (`IsQCAnalytic.inverse_memW12loc`); see `acl_weakGradient_of_qcInverse`.

**Proof.** From `hweakx`/`hweaky`, `exists_aclHorizontal_of_hasWeakDirDeriv_one` /
`exists_aclVertical_of_hasWeakDirDeriv_I` produce representatives `g' =ᵐ g`, `g'' =ᵐ g`
that are AC on a.e. line; continuity of `g` upgrades the AC to `g` itself (on a.e. line
the slices of `g`/`g'` are continuous and agree a.e., hence everywhere). All proven,
axiom-clean. -/
theorem acl_weakGradient_of_conditionNPlus {g : ℂ → ℂ}
    (hgcont : Continuous g)
    (gx gy : ℂ → ℂ)
    (hgxL2 : MemLpLocOn gx (2 : ℝ≥0∞) Set.univ) (hgyL2 : MemLpLocOn gy (2 : ℝ≥0∞) Set.univ)
    (hweakx : HasWeakDirDeriv 1 gx g Set.univ)
    (hweaky : HasWeakDirDeriv Complex.I gy g Set.univ) :
    ACLHorizontal g gx ∧ ACLVertical g gy := by
  classical
  -- ===== Local integrability: `g` continuous; `gx, gy ∈ L²_loc ⊆ L¹_loc`. =====
  have hgLI : LocallyIntegrable g := hgcont.locallyIntegrable
  have hLIofL2 : ∀ {h : ℂ → ℂ}, MemLpLocOn h (2 : ℝ≥0∞) Set.univ → LocallyIntegrable h := by
    intro h hh
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    have hmem : MemLp h (2 : ℝ≥0∞) (volume.restrict K) := hh K (Set.subset_univ _) hK
    have : IsFiniteMeasure (volume.restrict K) := by
      constructor; rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top
    exact (hmem.mono_exponent (by norm_num)).integrable (le_refl 1)
  have hgxLI : LocallyIntegrable gx := hLIofL2 hgxL2
  have hgyLI : LocallyIntegrable gy := hLIofL2 hgyL2
  -- ===== THE ANALYTIC CORE: `gx`, `gy` are the weak (distributional) directional =====
  -- derivatives of `g` (supplied as the hypotheses `hweakx`, `hweaky`). This is the
  -- genuine `W^{1,1}_loc`/Sobolev input — exactly the ingredient the pointwise a.e. data
  -- (condition N⁺ + L²_loc *pointwise* partials) does NOT supply. The area-preserving
  -- singular shear `g ⟨x,y⟩ = x + i·(y + s x)` (`s` continuous singular increasing) is
  -- injective, continuous, a.e.-differentiable with `Dg = id` a.e. (so it satisfies N⁺,
  -- the pointwise dilatation bound, and `L²_loc` pointwise partials), yet every horizontal
  -- slice's imaginary part `y + s ·` is singular (not AC): condition N⁺ alone is therefore
  -- *insufficient* (it constrains only the Jacobian/area, never the off-diagonal
  -- tangential partial whose distributional part is singular). The honest hypothesis is
  -- that `gx`/`gy` are the *weak* derivatives — true for the quasiconformal inverse via
  -- `MemW12loc` (`IsQCAnalytic.inverse_memW12loc`). See `acl_weakGradient_of_qcInverse`.
  -- ===== From the weak derivatives: AC representatives `g' =ᵐ g`, `g'' =ᵐ g`. =====
  obtain ⟨g', hg'ae, hg'acl⟩ :=
    exists_aclHorizontal_of_hasWeakDirDeriv_one hgLI hgxLI hweakx
  obtain ⟨g'', hg''ae, hg''acl⟩ :=
    exists_aclVertical_of_hasWeakDirDeriv_I hgLI hgyLI hweaky
  -- ===== Continuity transfer: the representative's per-line AC lifts to `g` itself. =====
  -- On almost every line, `g`'s slice and the representative's slice are continuous
  -- and agree almost everywhere, hence agree everywhere on the line; so `g`'s own slice
  -- inherits absolute continuity (and the line-derivative).
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  -- Horizontal transfer.
  have transferH : ∀ {h : ℂ → ℂ}, h =ᵐ[volume] g → ACLHorizontal h gx → ACLHorizontal g gx := by
    intro h hae hacl
    have hae2 : (fun p : ℝ × ℝ => h ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) := by
      rw [← Measure.volume_eq_prod]
      have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hae
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    have hslice_eq : ∀ᵐ y : ℝ,
        (fun x : ℝ => h ⟨x, y⟩) =ᵐ[volume] (fun x : ℝ => g ⟨x, y⟩) := by
      have hswap : (fun p : ℝ × ℝ => h ⟨p.2, p.1⟩) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => g ⟨p.2, p.1⟩) := by
        have hh := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq hae2
        simpa [Function.comp_def, Prod.swap] using hh
      exact Measure.ae_ae_eq_of_ae_eq_uncurry hswap
    have hsliceCont : ∀ y : ℝ, Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
      intro y
      have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
        funext x; apply Complex.ext <;> simp
      rw [he]; exact (Complex.continuous_ofReal.add continuous_const)
    unfold ACLHorizontal at hacl ⊢
    filter_upwards [hacl, hslice_eq] with y hy hy_eq
    obtain ⟨hac', hderiv'⟩ := hy
    set s  : ℝ → ℂ := fun x => g ⟨x, y⟩ with hs
    set s' : ℝ → ℂ := fun x => h ⟨x, y⟩ with hs'
    have hcont_s : Continuous s := hgcont.comp (hsliceCont y)
    have hcont_s' : Continuous s' := by
      rw [continuous_iff_continuousAt]
      intro x
      have hco := (hac' (x - 1) (x + 1)).continuousOn
      rw [Set.uIcc_of_le (by linarith)] at hco
      exact (hco x ⟨by linarith, by linarith⟩).continuousAt
        (Icc_mem_nhds (by linarith) (by linarith))
    have heq : s' = s := (hcont_s'.ae_eq_iff_eq (μ := volume) hcont_s).mp hy_eq
    refine ⟨?_, ?_⟩
    · intro a b; rw [← heq]; exact hac' a b
    · filter_upwards [hderiv'] with x hx; rw [← heq]; exact hx
  -- Vertical transfer.
  have transferV : ∀ {h : ℂ → ℂ}, h =ᵐ[volume] g → ACLVertical h gy → ACLVertical g gy := by
    intro h hae hacl
    have hae2 : (fun p : ℝ × ℝ => h ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) := by
      rw [← Measure.volume_eq_prod]
      have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hae
      filter_upwards [this] with p hp
      simpa [Complex.measurableEquivRealProd_symm_apply] using hp
    have hslice_eq : ∀ᵐ x : ℝ,
        (fun y : ℝ => h ⟨x, y⟩) =ᵐ[volume] (fun y : ℝ => g ⟨x, y⟩) :=
      Measure.ae_ae_eq_of_ae_eq_uncurry hae2
    have hsliceCont : ∀ x : ℝ, Continuous (fun y : ℝ => (⟨x, y⟩ : ℂ)) := by
      intro x
      have he : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
        funext y; apply Complex.ext <;> simp
      rw [he]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    unfold ACLVertical at hacl ⊢
    filter_upwards [hacl, hslice_eq] with x hx hx_eq
    obtain ⟨hac', hderiv'⟩ := hx
    set s  : ℝ → ℂ := fun y => g ⟨x, y⟩ with hs
    set s' : ℝ → ℂ := fun y => h ⟨x, y⟩ with hs'
    have hcont_s : Continuous s := hgcont.comp (hsliceCont x)
    have hcont_s' : Continuous s' := by
      rw [continuous_iff_continuousAt]
      intro y
      have hco := (hac' (y - 1) (y + 1)).continuousOn
      rw [Set.uIcc_of_le (by linarith)] at hco
      exact (hco y ⟨by linarith, by linarith⟩).continuousAt
        (Icc_mem_nhds (by linarith) (by linarith))
    have heq : s' = s := (hcont_s'.ae_eq_iff_eq (μ := volume) hcont_s).mp hx_eq
    refine ⟨?_, ?_⟩
    · intro a b; rw [← heq]; exact hac' a b
    · filter_upwards [hderiv'] with y hy; rw [← heq]; exact hy
  -- ===== Assembly. =====
  exact ⟨transferH hg'ae hg'acl, transferV hg''ae hg''acl⟩

/-! ## `L²_loc` of the inverse partials -/

/-- **`L²_loc` energy bound for the inverse partials.** A homeomorphism `g` that is
differentiable almost everywhere with the inverse-side dilatation bound
`‖Dg w‖² ≤ K · det (Dg w)` (`0 < K`) and `det (Dg w) > 0` a.e. has its pointwise
partials `w ↦ (Dg w) v` (`v ∈ {1, I}`) locally square-integrable.

This is the change-of-variables energy bound: on every compact `K`,
`∫_K ‖Dg‖² ≤ ∫_K K · det (Dg) = K · ∫_K |det (Dg)| = K · volume (g '' K)` by the
Lebesgue change-of-variables formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
and `volume (g '' K) < ∞` because `g` is a homeomorphism (so `g '' K` is compact).
The partial `‖(Dg w) v‖ ≤ ‖Dg w‖ · ‖v‖` then inherits the local `L²` bound.

PROVEN: the standard Jacobian change of variables, promoting the a.e.
`DifferentiableAt` to the `HasFDerivWithinAt`-on-`K` and `InjOn` hypotheses of
`lintegral_abs_det_fderiv_le_addHaar_image` and handling the null exceptional set, is
carried out in full below. -/
theorem memLpLocOn_inverse_partial_of_dilatation {g : ℂ → ℂ} {K : ℝ} (hK : 0 < K)
    (hghomeo : IsHomeomorph g)
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    (hdetpos : ∀ᵐ w, 0 < (fderiv ℝ g w).det)
    (hdil : ∀ᵐ w, ‖fderiv ℝ g w‖ ^ 2 ≤ K * (fderiv ℝ g w).det)
    (v : ℂ) :
    MemLpLocOn (fun w => (fderiv ℝ g w) v) (2 : ℝ≥0∞) Set.univ := by
  classical
  -- The candidate partial.
  set F : ℂ → ℂ := fun w => (fderiv ℝ g w) v with hF
  -- Measurability of `F`, `‖Dg‖²` and `det (Dg)`.
  have hFmeas : Measurable F := measurable_fderiv_apply_const ℝ g v
  have hfderivmeas : Measurable (fderiv ℝ g) := measurable_fderiv ℝ g
  have hdetmeas : Measurable (fun w : ℂ => (fderiv ℝ g w).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp hfderivmeas
  have hnormmeas : Measurable (fun w : ℂ => ‖fderiv ℝ g w‖) :=
    continuous_norm.measurable.comp hfderivmeas
  -- The differentiability set is measurable and co-null.
  set D : Set ℂ := {w : ℂ | DifferentiableAt ℝ g w} with hD
  have hDmeas : MeasurableSet D := measurableSet_of_differentiableAt ℝ g
  -- Work compact-by-compact.
  intro C _ hCcpt
  have hCmeas : MeasurableSet C := hCcpt.measurableSet
  -- The good set `s = C ∩ D`: measurable, where `g` is differentiable.
  set s : Set ℂ := C ∩ D with hs
  have hsmeas : MeasurableSet s := hCmeas.inter hDmeas
  -- On `s`, `g` has the within-derivative `fderiv ℝ g`, and `g` is injective.
  have hgderiv_s : ∀ w ∈ s, HasFDerivWithinAt g (fderiv ℝ g w) s w := by
    intro w hw
    exact ((hw.2 : DifferentiableAt ℝ g w).hasFDerivAt).hasFDerivWithinAt
  have hginj_s : Set.InjOn g s := hghomeo.injective.injOn
  -- The image `g '' C` is compact, hence of finite measure.
  have hgCcpt : IsCompact (g '' C) := hCcpt.image hghomeo.continuous
  have hgCfin : volume (g '' C) < ∞ := hgCcpt.measure_lt_top
  -- Change-of-variables inequality: `∫_s det ≤ volume (g '' s) ≤ volume (g '' C)`.
  have hcov : (∫⁻ w in s, ENNReal.ofReal |(fderiv ℝ g w).det| ∂volume) ≤ volume (g '' s) :=
    MeasureTheory.lintegral_abs_det_fderiv_le_addHaar_image volume hsmeas hgderiv_s hginj_s
  have hgss_le : volume (g '' s) ≤ volume (g '' C) :=
    measure_mono (Set.image_mono Set.inter_subset_left)
  -- `C \ s = C ∩ Dᶜ` is null, so integrals over `C` and `s` agree.
  have hCdiff_null : volume (C \ s) = 0 := by
    have hsub : C \ s ⊆ Dᶜ := by
      intro w hw
      simp only [hs, Set.mem_diff, Set.mem_inter_iff, not_and] at hw
      exact hw.2 hw.1
    have hDc_null : volume (Dᶜ) = 0 := by
      have := hgdiff
      rw [MeasureTheory.ae_iff] at this
      simpa only [hD, Set.compl_setOf, not_not] using this
    exact measure_mono_null hsub hDc_null
  -- The pointwise energy bound `‖F w‖² ≤ ‖v‖² · K · det (Dg w)` for a.e. `w` in `K`.
  -- We bound the lintegral of `‖F w‖ₑ²` over `K`.
  have hp2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  -- Reduce `MemLp` to: a.e.-strongly-measurable + finite eLpNorm.
  refine ⟨hFmeas.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num), hp2]
  -- Now bound `∫⁻ w in K, ‖F w‖ₑ ^ 2`.
  -- Step 1: `‖F w‖ₑ² ≤ ‖v‖ₑ² · ‖Dg w‖ₑ²` pointwise.
  have hstep1 : ∀ w, (‖F w‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
      ≤ (‖v‖ₑ) ^ (2 : ℝ) * (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) := by
    intro w
    have hle : ‖F w‖ ≤ ‖fderiv ℝ g w‖ * ‖v‖ := (fderiv ℝ g w).le_opNorm v
    have hle' : (‖F w‖ₑ : ℝ≥0∞) ≤ ‖fderiv ℝ g w‖ₑ * ‖v‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hle
    calc (‖F w‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
        ≤ (‖fderiv ℝ g w‖ₑ * ‖v‖ₑ) ^ (2 : ℝ) := by
          gcongr
      _ = (‖v‖ₑ) ^ (2 : ℝ) * (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]; ring
  -- Step 2: integrate Step 1.
  calc ∫⁻ w in C, (‖F w‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂volume
      ≤ ∫⁻ w in C, (‖v‖ₑ) ^ (2 : ℝ) * (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume :=
        lintegral_mono (fun w => hstep1 w)
    _ = (‖v‖ₑ) ^ (2 : ℝ) * ∫⁻ w in C, (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume := by
        rw [lintegral_const_mul']
        exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp [enorm_ne_top])
    _ < ∞ := by
        apply ENNReal.mul_lt_top
        · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simp [enorm_ne_top])
        -- It remains to bound `∫⁻ w in C, ‖Dg w‖ₑ²`.
        -- `‖Dg w‖ₑ² = ofReal (‖Dg w‖²) ≤ ofReal (K · det (Dg w))` a.e.
        have hbound : ∫⁻ w in C, (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume
            ≤ ENNReal.ofReal K * volume (g '' C) := by
          -- Move from `C` to `s` (they differ by a null set).
          have hCs : ∫⁻ w in C, (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume
              = ∫⁻ w in s, (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume := by
            apply (setLIntegral_congr _).symm
            -- `s =ᵐ C` since `C \ s` is null and `s ⊆ C`.
            refine MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩
            · -- `volume (s \ C) = 0` (in fact `s \ C = ∅`).
              have : s \ C = ∅ := by
                rw [Set.diff_eq_empty]; exact Set.inter_subset_left
              rw [this]; simp
            · exact hCdiff_null
          rw [hCs]
          -- On `s`, use the dilatation bound a.e. and change of variables.
          have hmono : ∫⁻ w in s, (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume
              ≤ ∫⁻ w in s, ENNReal.ofReal K * ENNReal.ofReal |(fderiv ℝ g w).det| ∂volume := by
            refine setLIntegral_mono_ae' hsmeas ?_
            filter_upwards [hdil, hdetpos] with w hwdil hwdet _
            -- `‖Dg w‖ₑ² = ofReal (‖Dg w‖²)`, and `‖Dg w‖² ≤ K · det`.
            have hnn : (0:ℝ) ≤ ‖fderiv ℝ g w‖ := norm_nonneg _
            rw [show (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ)
                  = ENNReal.ofReal (‖fderiv ℝ g w‖ ^ 2) by
                rw [← ofReal_norm_eq_enorm,
                  ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num : (0:ℝ) ≤ 2)]
                norm_num]
            rw [abs_of_pos hwdet, ← ENNReal.ofReal_mul hK.le]
            exact ENNReal.ofReal_le_ofReal hwdil
          calc ∫⁻ w in s, (‖fderiv ℝ g w‖ₑ) ^ (2 : ℝ) ∂volume
              ≤ ∫⁻ w in s, ENNReal.ofReal K * ENNReal.ofReal |(fderiv ℝ g w).det| ∂volume := hmono
            _ = ENNReal.ofReal K * ∫⁻ w in s, ENNReal.ofReal |(fderiv ℝ g w).det| ∂volume := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            _ ≤ ENNReal.ofReal K * volume (g '' C) := by
                gcongr
                exact le_trans hcov hgss_le
        exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgCfin)

/-! ## The keystone assembly -/

/-- **ACL weak gradient of a quasiconformal-type inverse** (keystone assembly). Given
the inverse-map data that `QC/InverseQC.lean` already supplies for `g = f⁻¹` — `g` is
a homeomorphism, differentiable a.e., with a.e. positive Jacobian and the inverse-side
dilatation bound `‖Dg w‖² ≤ K · det (Dg w)` — the map `g` is absolutely continuous on
almost every horizontal and vertical line, with `L²_loc` partials.

This assembles `memLpLocOn_inverse_partial_of_dilatation` (the `L²_loc` energy bound)
and `acl_weakGradient_of_conditionNPlus` (the Sobolev ⇒ ACL extraction) into the exact
shape consumed by `IsQCAnalytic.inverse_acl_weakGradient`. The witnesses for the
line-partials are the pointwise differential evaluations `gx w = (Dg w) 1`,
`gy w = (Dg w) I`.

**The genuine analytic input is the weak gradient** (`hweakx`, `hweaky`): the pointwise
partials are the *distributional* derivatives of `g`, i.e. `g ∈ W^{1,2}_loc`. This is
taken as a hypothesis — and is *not* derivable from the a.e. data (condition N⁺ + the
pointwise dilatation bound) alone: the area-preserving singular shear
`g ⟨x,y⟩ = x + i·(y + s x)` satisfies all of those a.e. facts yet has singular
(non-AC) slices (see `acl_weakGradient_of_conditionNPlus` for the full counterexample
audit). For the quasiconformal inverse the weak gradient is genuine, supplied via
`IsQCAnalytic.inverse_memW12loc` (the inverse lies in `W^{1,2}_loc`). -/
theorem acl_weakGradient_of_qcInverse {g : ℂ → ℂ} {K : ℝ} (hK : 0 < K)
    (hghomeo : IsHomeomorph g)
    (hgdiff : ∀ᵐ w, DifferentiableAt ℝ g w)
    (hdetpos : ∀ᵐ w, 0 < (fderiv ℝ g w).det)
    (hdil : ∀ᵐ w, ‖fderiv ℝ g w‖ ^ 2 ≤ K * (fderiv ℝ g w).det)
    (hweakx : HasWeakDirDeriv 1 (fun w => (fderiv ℝ g w) 1) g Set.univ)
    (hweaky : HasWeakDirDeriv Complex.I (fun w => (fderiv ℝ g w) Complex.I) g Set.univ) :
    ∃ gx gy : ℂ → ℂ,
      ACLHorizontal g gx ∧ ACLVertical g gy ∧
      MemLpLocOn gx (2 : ℝ≥0∞) Set.univ ∧ MemLpLocOn gy (2 : ℝ≥0∞) Set.univ := by
  -- The candidate partials: the pointwise differential evaluations.
  refine ⟨fun w => (fderiv ℝ g w) 1, fun w => (fderiv ℝ g w) Complex.I, ?_, ?_, ?_, ?_⟩
  · -- ACLHorizontal: from the weak gradient and the `L²_loc` partials.
    exact (acl_weakGradient_of_conditionNPlus hghomeo.continuous
      _ _
      (memLpLocOn_inverse_partial_of_dilatation hK hghomeo hgdiff hdetpos hdil 1)
      (memLpLocOn_inverse_partial_of_dilatation hK hghomeo hgdiff hdetpos hdil Complex.I)
      hweakx hweaky).1
  · -- ACLVertical: same package, second component.
    exact (acl_weakGradient_of_conditionNPlus hghomeo.continuous
      _ _
      (memLpLocOn_inverse_partial_of_dilatation hK hghomeo hgdiff hdetpos hdil 1)
      (memLpLocOn_inverse_partial_of_dilatation hK hghomeo hgdiff hdetpos hdil Complex.I)
      hweakx hweaky).2
  · exact memLpLocOn_inverse_partial_of_dilatation hK hghomeo hgdiff hdetpos hdil 1
  · exact memLpLocOn_inverse_partial_of_dilatation hK hghomeo hgdiff hdetpos hdil Complex.I

end RiemannDynamics
