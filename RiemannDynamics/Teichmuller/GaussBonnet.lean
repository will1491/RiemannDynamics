import RiemannDynamics.Teichmuller.PolygonRank
import RiemannDynamics.Teichmuller.Limit

/-!
# The uniform Gauss–Bonnet area bound across the Teichmüller family

The covolume of a cocompact free Fuchsian group is the hyperbolic area of its Dirichlet
domain centered at `i`. By the combinatorial Gauss–Bonnet formula and the rank identity of
the Dirichlet polygon, the covolume equals `2π (Q - 2)` where `Q` is the dimension of the
space of additive characters `Γ → (ℝ, +)` — a group invariant. The character spaces of the
base group and of the Fuchsian group of any Teichmüller representative are linearly
isomorphic, transported through the almost-everywhere Möbius equivariance of the
representative's normalized solution, with the `±1` ambiguity absorbed because characters
kill torsion. Hence all groups of the family share one covolume, and the Dirichlet domain
of each representative's group is a covering set of that fixed finite area: the area
hypothesis of the Mumford subconvergence theorems holds uniformly with
`A = fuchsianCovolume Γ₀`.

* `exists_translation_gap`, `exists_trace_gap` — a cocompact free Fuchsian group has a
  positive lower bound on the translation lengths of its nontrivially-acting elements, and
  the corresponding trace gap.
* `fuchsianCovolume` — the covolume; it is positive and finite.
* `fuchsianCovolume_eq_two_pi_mul` — the covolume is `2π (Q - 2)`.
* `TeichRep.exists_homSubmodule_linearEquiv` — the character-space transport.
* `TeichRep.fuchsianCovolume_group`, `TeichRep.hasAreaBound_covol` — the uniform area
  bound across the family.
* `mumford_subconvergence_thick_uniform`, `mumford_dT_subconvergence_uniform` — the Mumford
  subconvergence theorems with the area hypothesis discharged.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The translation gap of a cocompact free Fuchsian group -/

/-- The action of an element of `SL(2, ℝ)` on the upper half plane in explicit entries:
`τ ↦ (aτ + b)/(cτ + d)`. -/
theorem coe_smul_entries (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {a b c d : ℝ}
    (hM : (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d]) (τ : UpperHalfPlane) :
    ((γ • τ : UpperHalfPlane) : ℂ)
      = ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, hM]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one,
    show ∀ x : ℝ, (algebraMap ℝ ℝ) x = x from fun _ => rfl]

/-- Monotonicity of `cosh` inverted: a point with smaller `cosh` value lies below. -/
theorem dist_lt_of_cosh_lt {x ε : ℝ} (hε : 0 < ε) (hx : 0 ≤ x)
    (h : Real.cosh x < Real.cosh ε) : x < ε := by
  by_contra hle
  rw [not_lt] at hle
  have h2 : Real.cosh ε ≤ Real.cosh x := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hε.le, abs_of_nonneg hx]
    exact hle
  linarith

/-- A non-hyperbolic element of `SL(2, ℝ)` either fixes a point of the upper half plane
(central and elliptic cases) or has arbitrarily small displacement (parabolic case, points
escaping toward the fixed boundary point). -/
theorem fixed_or_small_displacement (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hnh : ¬ (γ : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) :
    (∃ τ : UpperHalfPlane, γ • τ = τ) ∨
      ∀ ε : ℝ, 0 < ε → ∃ τ : UpperHalfPlane, dist τ (γ • τ) < ε := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [hM, Matrix.det_fin_two_of] at h
  have htr : (a + d) ^ 2 ≤ 4 := by
    unfold Matrix.IsHyperbolic at hnh
    rw [Matrix.discr_fin_two, hM, Matrix.trace_fin_two_of, Matrix.det_fin_two_of,
      not_lt] at hnh
    nlinarith [hnh, hdet]
  by_cases hc : c = 0
  · -- upper triangular: `a = d = ±1`; central or a horizontal translation
    rw [hc] at hM hdet
    have had : a = d := by
      have h0 : (a - d) ^ 2 = 0 :=
        le_antisymm (by nlinarith [hdet, htr]) (sq_nonneg _)
      have h1 : a - d = 0 := sq_eq_zero_iff.mp h0
      linarith
    rw [← had] at hM hdet
    have ha2 : a * a = 1 := by linear_combination hdet
    have hane : a ≠ 0 := left_ne_zero_of_mul_eq_one ha2
    by_cases hb : b = 0
    · -- the central elements fix everything
      subst hb
      left
      have hpm : (γ : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (γ : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
        rcases mul_self_eq_one_iff.mp ha2 with ha | ha
        · left
          rw [hM, ha, ← Matrix.one_fin_two]
        · right
          rw [hM, ha]
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.neg_apply]
      exact ⟨UpperHalfPlane.I, (smul_eq_self_of_pm_one γ hpm).1 UpperHalfPlane.I⟩
    · -- translation by `a * b ≠ 0`: displacement `→ 0` as `im → ∞`
      right
      intro ε hε
      have hδ : 0 < Real.cosh ε - 1 := by
        have := Real.one_lt_cosh.mpr hε.ne'
        linarith
      have hs : 0 < Real.sqrt (Real.cosh ε - 1) := Real.sqrt_pos.mpr hδ
      set y : ℝ := |a * b| / Real.sqrt (Real.cosh ε - 1) + 1 with hydef
      have hy0 : 0 < y := by positivity
      have hyδ : (a * b) ^ 2 < y ^ 2 * (Real.cosh ε - 1) := by
        have h1 : |a * b| < y * Real.sqrt (Real.cosh ε - 1) := by
          rw [hydef, add_mul, div_mul_cancel₀ _ hs.ne']
          linarith
        have h2 : |a * b| * |a * b|
            < (y * Real.sqrt (Real.cosh ε - 1)) * (y * Real.sqrt (Real.cosh ε - 1)) :=
          mul_self_lt_mul_self (abs_nonneg _) h1
        have h3 : Real.sqrt (Real.cosh ε - 1) ^ 2 = Real.cosh ε - 1 := Real.sq_sqrt hδ.le
        nlinarith [sq_abs (a * b)]
      have himz : ((y : ℂ) * Complex.I).im = y := by
        simp [Complex.mul_im]
      set τy : UpperHalfPlane := UpperHalfPlane.mk ((y : ℂ) * Complex.I)
        (by rw [himz]; exact hy0) with hτydef
      have hcoeτ : (τy : ℂ) = (y : ℂ) * Complex.I := rfl
      have hτim : τy.im = y := by
        rw [← UpperHalfPlane.coe_im, hcoeτ, himz]
      have haC : (a : ℂ) * (a : ℂ) = 1 := by exact_mod_cast ha2
      have haCne : (a : ℂ) ≠ 0 := fun h0 => by simp [h0] at haC
      have hcoe2 : ((γ • τy : UpperHalfPlane) : ℂ) = (y : ℂ) * Complex.I + ((a * b : ℝ) : ℂ) := by
        rw [coe_smul_entries γ hM, hcoeτ]
        push_cast
        rw [zero_mul, zero_add, div_eq_iff haCne]
        linear_combination (-(b : ℂ)) * haC
      have him2 : (γ • τy).im = y := by
        rw [← UpperHalfPlane.coe_im, hcoe2]
        simp [himz]
      have hdc : dist ((τy : UpperHalfPlane) : ℂ) ((γ • τy : UpperHalfPlane) : ℂ) = |a * b| := by
        rw [hcoe2, hcoeτ, Complex.dist_eq, sub_add_cancel_left, norm_neg, Complex.norm_real,
          Real.norm_eq_abs]
      have hcosh : Real.cosh (dist τy (γ • τy)) = 1 + (a * b) ^ 2 / (2 * y ^ 2) := by
        rw [UpperHalfPlane.cosh_dist, hdc, hτim, him2, sq_abs]
        ring_nf
      refine ⟨τy, dist_lt_of_cosh_lt hε dist_nonneg ?_⟩
      rw [hcosh]
      have hq : (a * b) ^ 2 / (2 * y ^ 2) < Real.cosh ε - 1 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [hyδ, sq_nonneg y, hδ, sq_nonneg (a * b)]
      linarith
  · -- `c ≠ 0`: elliptic fixed point or parabolic escape
    have hx0 : 2 * c * ((a - d) / (2 * c)) = a - d := by
      field_simp
    set x₀ : ℝ := (a - d) / (2 * c) with hx₀def
    have habs : 0 < |c| := abs_pos.mpr hc
    rcases lt_or_eq_of_le htr with h4 | h4
    · -- elliptic: an interior fixed point
      left
      have h4' : 0 < 4 - (a + d) ^ 2 := by linarith
      set y₀ : ℝ := Real.sqrt (4 - (a + d) ^ 2) / (2 * |c|) with hy₀def
      have hy₀ : 0 < y₀ := div_pos (Real.sqrt_pos.mpr h4') (by positivity)
      have hy₀sq : c ^ 2 * y₀ ^ 2 = (4 - (a + d) ^ 2) / 4 := by
        rw [hy₀def, div_pow, mul_pow, Real.sq_sqrt h4'.le, sq_abs]
        have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
        field_simp
        ring
      set z₀ : ℂ := (x₀ : ℂ) + (y₀ : ℂ) * Complex.I with hz₀
      have himz₀ : z₀.im = y₀ := by simp [hz₀]
      set τ₀ : UpperHalfPlane := UpperHalfPlane.mk z₀ (by rw [himz₀]; exact hy₀) with hτ₀def
      have hden : (c : ℂ) * z₀ + (d : ℂ) ≠ 0 := by
        intro h0
        have h1 : ((c : ℂ) * z₀ + (d : ℂ)).im = c * y₀ := by
          simp [hz₀, Complex.add_im, Complex.mul_im]
        rw [h0] at h1
        simp only [Complex.zero_im] at h1
        exact (mul_ne_zero hc hy₀.ne') h1.symm
      have h1 : (z₀ - (x₀ : ℂ)) ^ 2 = -((y₀ : ℂ) ^ 2) := by
        have hsub : z₀ - (x₀ : ℂ) = (y₀ : ℂ) * Complex.I := by rw [hz₀]; ring
        rw [hsub, mul_pow, Complex.I_sq]
        ring
      have h2 : (2 : ℂ) * (c : ℂ) * (x₀ : ℂ) = (a : ℂ) - (d : ℂ) := by
        exact_mod_cast hx0
      have hreal : c * y₀ ^ 2 + c * x₀ ^ 2 + b = 0 := by
        have h4c : 4 * c ^ 2 * x₀ ^ 2 = (a - d) ^ 2 := by
          linear_combination (2 * c * x₀ + (a - d)) * hx0
        have h4y : 4 * c ^ 2 * y₀ ^ 2 = 4 - (a + d) ^ 2 := by
          linear_combination 4 * hy₀sq
        have hmul : 4 * c * (c * y₀ ^ 2 + c * x₀ ^ 2 + b) = 0 := by
          linear_combination h4y + h4c - 4 * hdet
        exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hc)
      have h3 : (c : ℂ) * (y₀ : ℂ) ^ 2 + (c : ℂ) * (x₀ : ℂ) ^ 2 + (b : ℂ) = 0 := by
        exact_mod_cast hreal
      have hkey : (a : ℂ) * z₀ + (b : ℂ) = z₀ * ((c : ℂ) * z₀ + (d : ℂ)) := by
        linear_combination (-(c : ℂ)) * h1 - z₀ * h2 + h3
      refine ⟨τ₀, ?_⟩
      apply UpperHalfPlane.ext
      rw [coe_smul_entries γ hM, show ((τ₀ : UpperHalfPlane) : ℂ) = z₀ from rfl, hkey]
      exact mul_div_cancel_right₀ z₀ hden
    · -- parabolic: displacement `→ 0` toward the real fixed point
      right
      intro ε hε
      have hδ : 0 < Real.cosh ε - 1 := by
        have := Real.one_lt_cosh.mpr hε.ne'
        linarith
      set y : ℝ := Real.sqrt (Real.cosh ε - 1) / (|c| + 1) with hydef
      have hy0 : 0 < y := div_pos (Real.sqrt_pos.mpr hδ) (by positivity)
      have hysq : y ^ 2 = (Real.cosh ε - 1) / (|c| + 1) ^ 2 := by
        rw [hydef, div_pow, Real.sq_sqrt hδ.le]
      have hyk : y ^ 2 * (|c| + 1) ^ 2 = Real.cosh ε - 1 := by
        rw [hysq]
        field_simp
      have hck : c ^ 2 < (|c| + 1) ^ 2 := by
        nlinarith [abs_nonneg c, sq_abs c]
      have hcy : c ^ 2 * y ^ 2 / 2 < Real.cosh ε - 1 := by
        rw [← hyk]
        nlinarith [mul_lt_mul_of_pos_right hck (pow_pos hy0 2), sq_nonneg (c * y)]
      set z : ℂ := (x₀ : ℂ) + (y : ℂ) * Complex.I with hz
      have himz : z.im = y := by simp [hz]
      set τy : UpperHalfPlane := UpperHalfPlane.mk z (by rw [himz]; exact hy0) with hτydef
      have hτim : τy.im = y := by
        rw [← UpperHalfPlane.coe_im, show ((τy : UpperHalfPlane) : ℂ) = z from rfl, himz]
      set e : ℝ := c * x₀ + d with hedef
      have h2e : 2 * e = a + d := by
        rw [hedef]
        linear_combination hx0
      have he2 : e ^ 2 = 1 := by
        linear_combination (1 / 4) * h4 + ((2 * e + (a + d)) / 4) * h2e
      have hDim : ((c : ℂ) * z + (d : ℂ)).im = c * y := by
        simp [hz, Complex.add_im, Complex.mul_im]
      have hDre : ((c : ℂ) * z + (d : ℂ)).re = e := by
        rw [hedef]
        simp [hz, Complex.add_re, Complex.mul_re]
      have hden : (c : ℂ) * z + (d : ℂ) ≠ 0 := by
        intro h0
        rw [h0] at hDim
        simp only [Complex.zero_im] at hDim
        exact (mul_ne_zero hc hy0.ne') hDim.symm
      have hD : (c : ℂ) * z + (d : ℂ) = (e : ℂ) + ((c * y : ℝ) : ℂ) * Complex.I := by
        rw [hedef, hz]
        push_cast
        ring
      have hN : Complex.normSq ((c : ℂ) * z + (d : ℂ)) = 1 + c ^ 2 * y ^ 2 := by
        rw [hD, Complex.normSq_add_mul_I]
        linear_combination he2
      have hNpos : (0 : ℝ) < 1 + c ^ 2 * y ^ 2 := by positivity
      have h1 : (z - (x₀ : ℂ)) ^ 2 = -((y : ℂ) ^ 2) := by
        have hsub : z - (x₀ : ℂ) = (y : ℂ) * Complex.I := by rw [hz]; ring
        rw [hsub, mul_pow, Complex.I_sq]
        ring
      have h2 : (2 : ℂ) * (c : ℂ) * (x₀ : ℂ) = (a : ℂ) - (d : ℂ) := by
        exact_mod_cast hx0
      have hb3 : c * x₀ ^ 2 + b = 0 := by
        have h4c : 4 * c ^ 2 * x₀ ^ 2 = (a - d) ^ 2 := by
          linear_combination (2 * c * x₀ + (a - d)) * hx0
        have hmul : 4 * c * (c * x₀ ^ 2 + b) = 0 := by
          linear_combination h4c + h4 - 4 * hdet
        exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hc)
      have hb3C : (c : ℂ) * (x₀ : ℂ) ^ 2 + (b : ℂ) = 0 := by
        exact_mod_cast hb3
      have hkey : (a : ℂ) * z + (b : ℂ)
          = z * ((c : ℂ) * z + (d : ℂ)) + ((c * y ^ 2 : ℝ) : ℂ) := by
        push_cast
        linear_combination (-(c : ℂ)) * h1 - z * h2 + hb3C
      have hw2 : ((γ • τy : UpperHalfPlane) : ℂ)
          = z + ((c * y ^ 2 : ℝ) : ℂ) / ((c : ℂ) * z + (d : ℂ)) := by
        rw [coe_smul_entries γ hM, show ((τy : UpperHalfPlane) : ℂ) = z from rfl, hkey,
          add_div, mul_div_cancel_right₀ z hden]
      have him2 : (γ • τy).im = y / (1 + c ^ 2 * y ^ 2) := by
        rw [← UpperHalfPlane.coe_im, hw2, Complex.add_im, himz, Complex.div_im, hN, hDre, hDim]
        simp only [Complex.ofReal_im, Complex.ofReal_re]
        field_simp
        ring
      have hdc : dist ((τy : UpperHalfPlane) : ℂ) ((γ • τy : UpperHalfPlane) : ℂ) ^ 2
          = (c * y ^ 2) ^ 2 / (1 + c ^ 2 * y ^ 2) := by
        rw [Complex.dist_eq, hw2, show ((τy : UpperHalfPlane) : ℂ) = z from rfl,
          sub_add_cancel_left, norm_neg, norm_div, div_pow, Complex.norm_real,
          Real.norm_eq_abs, sq_abs, Complex.sq_norm, hN]
      have hcosh : Real.cosh (dist τy (γ • τy)) = 1 + c ^ 2 * y ^ 2 / 2 := by
        rw [UpperHalfPlane.cosh_dist, hdc, hτim, him2]
        field_simp
      refine ⟨τy, dist_lt_of_cosh_lt hε dist_nonneg ?_⟩
      rw [hcosh]
      linarith

/-- The displacement gap of a cocompact free Fuchsian group: nontrivially-acting elements
move every point by at least a uniform positive amount — the point is translated into a
compact covering set by the group, conjugation preserves the displacement, and only finitely
many elements displace any point of the enlarged compact set boundedly, each by a positive
minimum attained on the compact set and nonzero by freeness. -/
theorem exists_displacement_gap (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ ∈ Γ, actsNontrivially γ →
      ∀ τ : UpperHalfPlane, ε ≤ dist τ (γ • τ) := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul (↥Γ) UpperHalfPlane := hΓ
  obtain ⟨K, hK, hcov⟩ := exists_compact_covering Γ hcc
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall UpperHalfPlane.I
  have hK₁c : IsCompact (Metric.closedBall UpperHalfPlane.I (R + 1)) :=
    isCompact_closedBall _ _
  have hKK₁ : K ⊆ Metric.closedBall UpperHalfPlane.I (R + 1) :=
    hKR.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hfree' : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, g ∈ Γ → actsNontrivially g →
      ∀ τ : UpperHalfPlane, g • τ ≠ τ := by
    intro g hg hnt τ heq
    obtain ⟨σ, hσ⟩ := hnt
    exact hσ (hfree ⟨g, hg⟩ ⟨τ, heq⟩ σ)
  set F : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    {g | g ∈ Γ ∧ actsNontrivially g ∧
      ∃ τ ∈ Metric.closedBall UpperHalfPlane.I (R + 1),
        g • τ ∈ Metric.closedBall UpperHalfPlane.I (R + 1)} with hFdef
  have hFfin : F.Finite := by
    have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (Γ := ↥Γ) (T := UpperHalfPlane) hK₁c hK₁c
    refine (hfin.image (fun γ : ↥Γ => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))).subset ?_
    rintro g ⟨hg, hnt, τ, hτ, hgτ⟩
    exact ⟨⟨g, hg⟩, ⟨g • τ, ⟨τ, hτ, rfl⟩, hgτ⟩, rfl⟩
  set m : Matrix.SpecialLinearGroup (Fin 2) ℝ → ℝ := fun g =>
    sInf ((fun τ => dist τ (g • τ)) '' Metric.closedBall UpperHalfPlane.I (R + 1)) with hmdef
  have hmpos : ∀ g ∈ F, 0 < m g := by
    rintro g ⟨hg, hnt, τw, hτw, -⟩
    have hcont : Continuous fun τ : UpperHalfPlane => dist τ (g • τ) :=
      Continuous.dist continuous_id (isometry_smul UpperHalfPlane g).continuous
    obtain ⟨τ₀, hτ₀K, hmin⟩ := hK₁c.exists_isMinOn ⟨τw, hτw⟩ hcont.continuousOn
    have hpos : 0 < dist τ₀ (g • τ₀) := dist_pos.mpr (hfree' g hg hnt τ₀).symm
    refine lt_of_lt_of_le hpos (le_csInf ⟨_, Set.mem_image_of_mem _ hτw⟩ ?_)
    rintro v ⟨τ, hτ, rfl⟩
    exact hmin hτ
  have hmle : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ τ ∈ Metric.closedBall UpperHalfPlane.I (R + 1), m g ≤ dist τ (g • τ) := by
    intro g τ hτ
    exact csInf_le ⟨0, by rintro v ⟨σ, hσ, rfl⟩; exact dist_nonneg⟩
      (Set.mem_image_of_mem _ hτ)
  have hSfin : (insert (1 : ℝ) (m '' F)).Finite := (hFfin.image m).insert 1
  have hSne : (1 : ℝ) ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr (Set.mem_insert 1 _)
  refine ⟨hSfin.toFinset.min' ⟨1, hSne⟩, ?_, ?_⟩
  · have hmem := hSfin.toFinset.min'_mem ⟨1, hSne⟩
    rw [hSfin.mem_toFinset] at hmem
    rcases Set.mem_insert_iff.mp hmem with h1 | ⟨g, hgF, hgm⟩
    · rw [h1]
      norm_num
    · rw [← hgm]
      exact hmpos g hgF
  · have hle1 : hSfin.toFinset.min' ⟨1, hSne⟩ ≤ 1 := Finset.min'_le _ _ hSne
    have hleF : ∀ g ∈ F, hSfin.toFinset.min' ⟨1, hSne⟩ ≤ m g := fun g hg =>
      Finset.min'_le _ _ (hSfin.mem_toFinset.mpr (Set.mem_insert_of_mem _ ⟨g, hg, rfl⟩))
    intro g hg hnt τ
    obtain ⟨δ, hδK⟩ := hcov τ
    have hg'Γ : (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
        (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem δ.2 hg) (Γ.inv_mem δ.2)
    have hg'smul : ∀ σ : UpperHalfPlane,
        ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
          (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) •
            ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • σ)
          = (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • (g • σ) := by
      intro σ
      rw [← mul_smul, inv_mul_cancel_right, mul_smul]
    have hdisteq : dist ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ)
        (((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
          (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) •
            ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ)) = dist τ (g • τ) := by
      rw [hg'smul τ, dist_smul]
    have hσK : (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ ∈ K := hδK
    have hσK₁ : (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ
        ∈ Metric.closedBall UpperHalfPlane.I (R + 1) := hKK₁ hσK
    rcases le_or_gt 1 (dist ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ)
        (((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
          (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) •
            ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ))) with hbig | hsmol
    · rw [← hdisteq]
      exact hle1.trans hbig
    · have hnt' : actsNontrivially ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
          (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) := by
        obtain ⟨σ, hσ⟩ := hnt
        refine ⟨(δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • σ, fun h0 => hσ ?_⟩
        rw [hg'smul σ] at h0
        exact smul_left_cancel _ h0
      have hgK₁ : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
          (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) •
            ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ)
          ∈ Metric.closedBall UpperHalfPlane.I (R + 1) := by
        rw [Metric.mem_closedBall]
        have h2 : dist ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ) UpperHalfPlane.I ≤ R := by
          rw [← Metric.mem_closedBall]
          exact hKR hσK
        have h3 := dist_triangle
          (((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
            (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) •
              ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ))
          ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ) UpperHalfPlane.I
        have h4 := dist_comm
          (((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
            (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) •
              ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ))
          ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ)
        linarith
      have hgF : (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * g *
          (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ ∈ F :=
        ⟨hg'Γ, hnt', _, hσK₁, hgK₁⟩
      rw [← hdisteq]
      exact (hleF _ hgF).trans (hmle _ _ hσK₁)

/-- **Translation gap**: in a cocompact Fuchsian group acting freely, the translation
lengths of the nontrivially-acting elements are bounded below by a positive constant — the
displacement function is minimized over conjugates meeting a compact covering set, where
only finitely many elements displace boundedly. -/
theorem exists_translation_gap (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ := by
  obtain ⟨ε, hε, hdisp⟩ := exists_displacement_gap hΓ hfree hcc
  refine ⟨ε, hε, ?_⟩
  intro γ hγ hnt
  by_cases hyp : (γ : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic
  · obtain ⟨τ₀, hτ₀⟩ := exists_dist_smul_eq_translationLength γ hyp
    rw [← hτ₀]
    exact hdisp γ hγ hnt τ₀
  · exfalso
    rcases fixed_or_small_displacement γ hyp with ⟨τ, hτ⟩ | hsmall
    · obtain ⟨σ, hσ⟩ := hnt
      exact hσ (hfree ⟨γ, hγ⟩ ⟨τ, hτ⟩ σ)
    · obtain ⟨τ, hτ⟩ := hsmall ε hε
      exact absurd (hdisp γ hγ hnt τ) (not_le.mpr hτ)

/-- **Trace gap**: in a cocompact Fuchsian group acting freely, the nontrivially-acting
elements satisfy `2 cosh (ε/2) ≤ |tr|` for some `ε > 0`. -/
theorem exists_trace_gap (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ ∈ Γ, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| := by
  obtain ⟨ε, hε, hgap⟩ := exists_translation_gap hΓ hfree hcc
  refine ⟨ε, hε, ?_⟩
  intro γ hγ hnt
  have hlen : ε ≤ translationLength γ := hgap γ hγ hnt
  unfold translationLength at hlen
  set M := max 1 (|Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| / 2) with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have harc : ε / 2 ≤ Real.arcosh M := by linarith
  have hcosh : Real.cosh (ε / 2) ≤ M := by
    have h : Real.cosh (ε / 2) ≤ Real.cosh (Real.arcosh M) := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ε / 2),
        abs_of_nonneg (Real.arcosh_nonneg hM1)]
      exact harc
    rwa [Real.cosh_arcosh hM1] at h
  have h1c : (1 : ℝ) < Real.cosh (ε / 2) :=
    Real.one_lt_cosh.mpr (by positivity : (0 : ℝ) < ε / 2).ne'
  have htr2 : 1 < |Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| / 2 := by
    rcases le_or_gt (|Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) ℝ))| / 2) 1 with hle | hlt
    · exfalso
      rw [hMdef, max_eq_left hle] at hcosh
      linarith
    · exact hlt
  rw [hMdef, max_eq_right htr2.le] at hcosh
  linarith

/-! ## The covolume -/

/-- The **covolume** of a Fuchsian group: the hyperbolic area of its Dirichlet domain
centered at `i`. -/
noncomputable def fuchsianCovolume
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : ℝ≥0∞ :=
  volume (dirichletDomain Γ UpperHalfPlane.I)

/-- The covolume of a cocompact free Fuchsian group is finite: the Dirichlet domain is
compact under the orbit density supplied by cocompactness and the trace gap. -/
theorem fuchsianCovolume_ne_top (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    fuchsianCovolume Γ ≠ ⊤ := by
  obtain ⟨ε, hε, hgap⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε hgap hcc UpperHalfPlane.I
  change volume (dirichletDomain Γ UpperHalfPlane.I) ≠ ⊤
  exact (isCompact_dirichletDomain hdense).measure_lt_top.ne

/-- The covolume of a cocompact free Fuchsian group is positive: under the translation gap
the domain contains a ball about the basepoint. -/
theorem fuchsianCovolume_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    0 < fuchsianCovolume Γ := by
  obtain ⟨ε, hε, hgap⟩ := exists_translation_gap hΓ hfree hcc
  have hball := ball_subset_dirichletDomain (τ₀ := UpperHalfPlane.I) hε hgap
  have h1 : (0 : ℝ≥0∞) < volume (Metric.ball UpperHalfPlane.I (ε / 2)) :=
    volume_ball_pos UpperHalfPlane.I (half_pos hε)
  have h2 : volume (Metric.ball UpperHalfPlane.I (ε / 2))
      ≤ volume (dirichletDomain Γ UpperHalfPlane.I) := measure_mono hball
  exact lt_of_lt_of_le h1 h2

/-- The character space of a cocompact free Fuchsian group is finite dimensional. -/
theorem finiteDimensional_homSubmodule_of_cocompact (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    FiniteDimensional ℝ (homSubmodule (↥Γ)) := by
  obtain ⟨ε, hε, hgap⟩ := exists_translation_gap hΓ hfree hcc
  obtain ⟨ε', hε', hgap'⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, hR, hdense⟩ := exists_orbit_density_bound hΓ hε' hgap' hcc UpperHalfPlane.I
  exact finiteDimensional_homSubmodule hΓ hfree hε hgap hdense

/-- **The covolume formula**: the covolume of a cocompact free Fuchsian group is
`2π (Q - 2)`, where `Q` is the dimension of its space of additive characters — the
combinatorial Gauss–Bonnet formula `2π (m - 1 - c)` for the Dirichlet polygon combined with
the rank identity `Q = m - c + 1`. -/
theorem fuchsianCovolume_eq_two_pi_mul (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    fuchsianCovolume Γ = ENNReal.ofReal
      (2 * Real.pi * ((Module.finrank ℝ (homSubmodule (↥Γ)) : ℝ) - 2)) := by
  obtain ⟨ε, hε, hgap⟩ := exists_translation_gap hΓ hfree hcc
  obtain ⟨εt, hεt, hgapt⟩ := exists_trace_gap hΓ hfree hcc
  obtain ⟨R, -, hdense⟩ := exists_orbit_density_bound hΓ hεt hgapt hcc UpperHalfPlane.I
  have hGB := volume_dirichletDomain_gaussBonnet hΓ hfree hε hgap hdense
  have hrank := finrank_homSubmodule_add_classCount hΓ hfree hε hgap hdense
  rw [fuchsianCovolume, hGB]
  have hcast : (Module.finrank ℝ (homSubmodule (↥Γ)) : ℝ)
      + (polygonVertexClassCount Γ UpperHalfPlane.I : ℝ)
      = (polygonSideCount Γ UpperHalfPlane.I : ℝ) + 1 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hrank
  have h2 : (polygonSideCount Γ UpperHalfPlane.I : ℝ) - 1
      - (polygonVertexClassCount Γ UpperHalfPlane.I : ℝ)
      = (Module.finrank ℝ (homSubmodule (↥Γ)) : ℝ) - 2 := by linarith
  rw [h2]

/-! ## Transport of the character space across the Teichmüller family -/

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- Additive characters of a subgroup of `SL(2, ℝ)` do not see the matrix sign: two
subgroup elements whose underlying matrices are negatives of each other take equal values
under every character, since their quotient squares to the identity. -/
theorem homSubmodule_apply_eq_of_neg_matrix
    {H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (f : homSubmodule (↥H)) {U V : ↥H}
    (h : ((U : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = -((V : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
    (f : (↥H) → ℝ) U = (f : (↥H) → ℝ) V := by
  have hVV : ((V : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      * (((V : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hsl : ((U : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        * (V : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹)
      * ((U : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        * (V : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹) = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, h]
    simp only [neg_mul, mul_neg]
    rw [hVV, one_mul]
    exact neg_neg 1
  have hsq : (U * V⁻¹) * (U * V⁻¹) = (1 : ↥H) := by
    apply Subtype.ext
    exact_mod_cast hsl
  have hzero : (f : (↥H) → ℝ) (U * V⁻¹) = 0 := homSubmodule_apply_eq_zero_of_sq f hsq
  have hUdec : U = (U * V⁻¹) * V := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hstep : (f : (↥H) → ℝ) ((U * V⁻¹) * V)
      = (f : (↥H) → ℝ) (U * V⁻¹) + (f : (↥H) → ℝ) V := f.2 _ _
  rw [hUdec, hstep, hzero, zero_add]

/-- Two functions continuous on the open upper half plane and equal almost everywhere on
the plane agree at every point of the upper half plane. -/
theorem eq_on_upper {g h : ℂ → ℂ}
    (hg : ContinuousOn g {w : ℂ | 0 < w.im}) (hh : ContinuousOn h {w : ℂ | 0 < w.im})
    (hae : ∀ᵐ z : ℂ, g z = h z) {z : ℂ} (hz : 0 < z.im) : g z = h z := by
  have hUopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have heq : Set.EqOn g h {w : ℂ | 0 < w.im} := by
    refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae hae) hg hh ?_
    rw [hUopen.interior_eq]
    exact subset_closure
  exact heq hz

/-- The imaginary part of `2i` is `2`. -/
theorem im_twoI : ((2 : ℂ) * Complex.I).im = 2 := by
  simp [Complex.mul_im]

/-- The imaginary part of `3i` is `3`. -/
theorem im_threeI : ((3 : ℂ) * Complex.I).im = 3 := by
  simp [Complex.mul_im]

/-- The points `i`, `2i`, `3i` are pairwise distinct. -/
theorem ne_I_twoI : (Complex.I : ℂ) ≠ 2 * Complex.I := by
  intro hEq
  have h' := congrArg Complex.im hEq
  rw [Complex.I_im, im_twoI] at h'
  norm_num at h'

/-- The points `i`, `2i`, `3i` are pairwise distinct. -/
theorem ne_I_threeI : (Complex.I : ℂ) ≠ 3 * Complex.I := by
  intro hEq
  have h' := congrArg Complex.im hEq
  rw [Complex.I_im, im_threeI] at h'
  norm_num at h'

/-- The points `i`, `2i`, `3i` are pairwise distinct. -/
theorem ne_twoI_threeI : ((2 : ℂ) * Complex.I) ≠ 3 * Complex.I := by
  intro hEq
  have h' := congrArg Complex.im hEq
  rw [im_twoI, im_threeI] at h'
  norm_num at h'

/-- **Conjugator rigidity**: two Möbius conjugators of the same base element against the
normalized solution have equal or opposite matrices — the two conjugation identities force
the Möbius maps to agree almost everywhere, hence on the upper half plane by continuity,
hence at the images of the three interior points `i`, `2i`, `3i`. -/
theorem conjugator_sign (x : TeichRep Γ₀)
    {γ W W' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hW : ∀ᵐ z : ℂ, x.w (moebiusMap γ z) = moebiusMap W (x.w z))
    (hW' : ∀ᵐ z : ℂ, x.w (moebiusMap γ z) = moebiusMap W' (x.w z)) :
    (W : Matrix (Fin 2) (Fin 2) ℝ) = (W' : Matrix (Fin 2) (Fin 2) ℝ) ∨
      (W : Matrix (Fin 2) (Fin 2) ℝ) = -(W' : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hfc : Continuous x.w := x.w_isQCAnalytic.1.1.continuous
  have him0 : ∀ z : ℂ, 0 < z.im → (x.w z).im ≠ 0 := by
    rcases x.w_halfPlane_dichotomy with ⟨hpos, _⟩ | ⟨hneg, _⟩
    · exact fun z hz => ne_of_gt (hpos z hz)
    · exact fun z hz => ne_of_lt (hneg z hz)
  have hae : ∀ᵐ z : ℂ, moebiusMap W (x.w z) = moebiusMap W' (x.w z) := by
    filter_upwards [hW, hW'] with z h1 h2
    rw [← h1]
    exact h2
  have hcont : ∀ V : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ContinuousOn (fun w => moebiusMap V (x.w w)) {w : ℂ | 0 < w.im} := by
    intro V w hw
    have hd := moebiusDenom_ne_zero_of_im_ne_zero V (him0 w hw)
    exact ((hasDerivAt_moebiusMap V hd).continuousAt.comp
      hfc.continuousAt).continuousWithinAt
  have hup : ∀ z : ℂ, 0 < z.im → moebiusMap W (x.w z) = moebiusMap W' (x.w z) := by
    intro z hz
    exact eq_on_upper (hcont W) (hcont W') hae hz
  have h01 : (0 : ℝ) < (Complex.I).im := by
    rw [Complex.I_im]
    norm_num
  have h02 : (0 : ℝ) < ((2 : ℂ) * Complex.I).im := by
    rw [im_twoI]
    norm_num
  have h03 : (0 : ℝ) < ((3 : ℂ) * Complex.I).im := by
    rw [im_threeI]
    norm_num
  have hz12 : x.w Complex.I ≠ x.w (2 * Complex.I) :=
    fun hEq => ne_I_twoI (x.w_injective hEq)
  have hz13 : x.w Complex.I ≠ x.w (3 * Complex.I) :=
    fun hEq => ne_I_threeI (x.w_injective hEq)
  have hz23 : x.w (2 * Complex.I) ≠ x.w (3 * Complex.I) :=
    fun hEq => ne_twoI_threeI (x.w_injective hEq)
  have hdenW : ∀ z ∈ ({x.w Complex.I, x.w (2 * Complex.I), x.w (3 * Complex.I)} : Set ℂ),
      moebiusDenom W z ≠ 0 := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact moebiusDenom_ne_zero_of_im_ne_zero W (him0 Complex.I h01)
    · exact moebiusDenom_ne_zero_of_im_ne_zero W (him0 _ h02)
    · exact moebiusDenom_ne_zero_of_im_ne_zero W (him0 _ h03)
  have hdenW' : ∀ z ∈ ({x.w Complex.I, x.w (2 * Complex.I), x.w (3 * Complex.I)} : Set ℂ),
      moebiusDenom W' z ≠ 0 := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact moebiusDenom_ne_zero_of_im_ne_zero W' (him0 Complex.I h01)
    · exact moebiusDenom_ne_zero_of_im_ne_zero W' (him0 _ h02)
    · exact moebiusDenom_ne_zero_of_im_ne_zero W' (him0 _ h03)
  have hagree : ∀ z ∈ ({x.w Complex.I, x.w (2 * Complex.I), x.w (3 * Complex.I)} : Set ℂ),
      moebiusMap W z = moebiusMap W' z := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hup Complex.I h01
    · exact hup _ h02
    · exact hup _ h03
  exact moebius_ext_three hz12 hz13 hz23 hdenW hdenW' hagree

/-- **Base rigidity**: two base elements conjugating to the same Möbius matrix against the
normalized solution have equal or opposite matrices — injectivity of the solution forces
their Möbius maps to agree almost everywhere, hence on the upper half plane by continuity,
hence at the three interior points `i`, `2i`, `3i`. -/
theorem base_sign (x : TeichRep Γ₀)
    {γ γ' W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : ∀ᵐ z : ℂ, x.w (moebiusMap γ z) = moebiusMap W (x.w z))
    (hγ' : ∀ᵐ z : ℂ, x.w (moebiusMap γ' z) = moebiusMap W (x.w z)) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) = (γ' : Matrix (Fin 2) (Fin 2) ℝ) ∨
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = -(γ' : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hae : ∀ᵐ z : ℂ, moebiusMap γ z = moebiusMap γ' z := by
    filter_upwards [hγ, hγ'] with z h1 h2
    exact x.w_injective (h1.trans h2.symm)
  have hcont : ∀ V : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ContinuousOn (moebiusMap V) {w : ℂ | 0 < w.im} := by
    intro V w hw
    have hd := moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hw)
    exact (hasDerivAt_moebiusMap V hd).continuousAt.continuousWithinAt
  have hup : ∀ z : ℂ, 0 < z.im → moebiusMap γ z = moebiusMap γ' z := by
    intro z hz
    exact eq_on_upper (hcont γ) (hcont γ') hae hz
  have h01 : (0 : ℝ) < (Complex.I).im := by
    rw [Complex.I_im]
    norm_num
  have h02 : (0 : ℝ) < ((2 : ℂ) * Complex.I).im := by
    rw [im_twoI]
    norm_num
  have h03 : (0 : ℝ) < ((3 : ℂ) * Complex.I).im := by
    rw [im_threeI]
    norm_num
  have hdenγ : ∀ z ∈ ({Complex.I, (2 : ℂ) * Complex.I, (3 : ℂ) * Complex.I} : Set ℂ),
      moebiusDenom γ z ≠ 0 := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt h01)
    · exact moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt h02)
    · exact moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt h03)
  have hdenγ' : ∀ z ∈ ({Complex.I, (2 : ℂ) * Complex.I, (3 : ℂ) * Complex.I} : Set ℂ),
      moebiusDenom γ' z ≠ 0 := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact moebiusDenom_ne_zero_of_im_ne_zero γ' (ne_of_gt h01)
    · exact moebiusDenom_ne_zero_of_im_ne_zero γ' (ne_of_gt h02)
    · exact moebiusDenom_ne_zero_of_im_ne_zero γ' (ne_of_gt h03)
  have hagree : ∀ z ∈ ({Complex.I, (2 : ℂ) * Complex.I, (3 : ℂ) * Complex.I} : Set ℂ),
      moebiusMap γ z = moebiusMap γ' z := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hup Complex.I h01
    · exact hup _ h02
    · exact hup _ h03
  exact moebius_ext_three ne_I_twoI ne_I_threeI ne_twoI_threeI
    hdenγ hdenγ' hagree

/-- Almost-everywhere Möbius conjugation identities of the normalized solution compose:
the product of two conjugators conjugates the product of the base elements, the null sets
pulling back through the smooth Möbius factors and through point preimages of the
injective solution. -/
theorem ae_conj_mul (x : TeichRep Γ₀)
    {γ₁ γ₂ W₁ W₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hae₁ : ∀ᵐ z : ℂ, x.w (moebiusMap γ₁ z) = moebiusMap W₁ (x.w z))
    (hae₂ : ∀ᵐ z : ℂ, x.w (moebiusMap γ₂ z) = moebiusMap W₂ (x.w z)) :
    ∀ᵐ z : ℂ, x.w (moebiusMap (γ₁ * γ₂) z) = moebiusMap (W₁ * W₂) (x.w z) := by
  have haeMoeb : ∀ (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (P : ℂ → Prop),
      (∀ᵐ w : ℂ, P w) → ∀ᵐ z : ℂ, moebiusDenom δ z ≠ 0 → P (moebiusMap δ z) := by
    intro δ P hP
    have hopen : IsOpen {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0} := by
      have hc : Continuous (moebiusDenom δ⁻¹) := by
        unfold moebiusDenom
        fun_prop
      exact isOpen_compl_singleton.preimage hc
    rw [ae_iff] at hP ⊢
    have himg : volume (moebiusMap δ⁻¹ ''
        (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0})) = 0 := by
      have hSmeas : MeasurableSet
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) :=
        (measurableSet_toMeasurable _ _).inter hopen.measurableSet
      have hSnull : volume
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) = 0 := by
        refine le_antisymm (le_trans (measure_mono Set.inter_subset_left) ?_) (zero_le _)
        rw [measure_toMeasurable]
        exact hP.le
      have hfd : ∀ w ∈ toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0},
          HasFDerivWithinAt (moebiusMap δ⁻¹) (fderiv ℝ (moebiusMap δ⁻¹) w)
            (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) w := by
        intro w hw
        have hder := hasDerivAt_moebiusMap δ⁻¹ hw.2
        exact ((hder.complexToReal_fderiv).differentiableAt.hasFDerivAt).hasFDerivWithinAt
      have hinjOn : Set.InjOn (moebiusMap δ⁻¹)
          (toMeasurable volume {w | ¬ P w} ∩ {w : ℂ | moebiusDenom δ⁻¹ w ≠ 0}) := by
        intro u hu v hv huv
        have hu1 : moebiusMap δ (moebiusMap δ⁻¹ u) = u := by
          rw [moebiusMap_mul δ δ⁻¹ u hu.2, mul_inv_cancel, moebiusMap_one]
        have hv1 : moebiusMap δ (moebiusMap δ⁻¹ v) = v := by
          rw [moebiusMap_mul δ δ⁻¹ v hv.2, mul_inv_cancel, moebiusMap_one]
        rw [← hu1, ← hv1, huv]
      have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSmeas hfd hinjOn
        (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_one, setLIntegral_measure_zero _ _ hSnull] at hcov
      exact hcov
    refine measure_mono_null ?_ himg
    intro z hz
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hz
    obtain ⟨hden, hbad⟩ := hz
    have hd1 : moebiusDenom δ⁻¹ (moebiusMap δ z) * moebiusDenom δ z = 1 := by
      rw [moebiusDenom_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusDenom_one]
    have hdinv : moebiusDenom δ⁻¹ (moebiusMap δ z) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hd1
      exact zero_ne_one hd1
    refine ⟨moebiusMap δ z, ⟨subset_toMeasurable _ _ hbad, hdinv⟩, ?_⟩
    rw [moebiusMap_mul δ⁻¹ δ z hden, inv_mul_cancel, moebiusMap_one]
  have haePole : ∀ᵐ z : ℂ, moebiusDenom γ₂ z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact volume_moebiusDenom_zero γ₂
  have hfPole : ∀ᵐ z : ℂ, moebiusDenom W₂ (x.w z) ≠ 0 := by
    have hPsub : Set.Subsingleton {w : ℂ | moebiusDenom W₂ w = 0} := by
      intro w₁ hw₁ w₂ hw₂
      have h₁' : (W₂ 1 0 : ℂ) * w₁ + (W₂ 1 1 : ℂ) = 0 := hw₁
      have h₂' : (W₂ 1 0 : ℂ) * w₂ + (W₂ 1 1 : ℂ) = 0 := hw₂
      by_cases hc : W₂ 1 0 = 0
      · exfalso
        have hdet : W₂ 0 0 * W₂ 1 1 - W₂ 0 1 * W₂ 1 0 = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe W₂
          rwa [Matrix.det_fin_two] at h
        have hcC : ((W₂ 1 0 : ℝ) : ℂ) = 0 := by
          rw [hc, Complex.ofReal_zero]
        rw [hcC, zero_mul, zero_add] at h₁'
        have hd : W₂ 1 1 = 0 := by exact_mod_cast h₁'
        rw [hc, hd] at hdet
        simp at hdet
      · have hcC : ((W₂ 1 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
        have hmul : (W₂ 1 0 : ℂ) * w₁ = (W₂ 1 0 : ℂ) * w₂ := by
          linear_combination h₁' - h₂'
        exact mul_left_cancel₀ hcC hmul
    have hpre : Set.Subsingleton (x.w ⁻¹' {w : ℂ | moebiusDenom W₂ w = 0}) := by
      intro u hu v hv
      exact x.w_injective (hPsub hu hv)
    rw [ae_iff]
    refine measure_mono_null ?_ (hpre.measure_zero volume)
    intro z hz
    simp only [Set.mem_setOf_eq, ne_eq, not_not] at hz
    exact hz
  have hpull := haeMoeb γ₂ (fun w => x.w (moebiusMap γ₁ w) = moebiusMap W₁ (x.w w)) hae₁
  filter_upwards [haePole, hae₂, hpull, hfPole] with z hd2 h2 h1 hdW2
  rw [← moebiusMap_mul γ₁ γ₂ z hd2, h1 hd2, h2, moebiusMap_mul W₁ W₂ (x.w z) hdW2]

/-- A choice of Möbius conjugator in the image group attached to a base group element by
the almost-everywhere equivariance of the normalized solution. -/
noncomputable def conjOf (x : TeichRep Γ₀) (γ : ↥Γ₀) : ↥x.group :=
  ⟨(x.mem_group_of γ.2).choose, (x.mem_group_of γ.2).choose_spec.1⟩

/-- The chosen conjugator satisfies the almost-everywhere conjugation identity. -/
theorem conjOf_spec (x : TeichRep Γ₀) (γ : ↥Γ₀) :
    ∀ᵐ z : ℂ, x.w (moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) z)
      = moebiusMap ((conjOf x γ : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        (x.w z) :=
  (x.mem_group_of γ.2).choose_spec.2

/-- Membership in the image group unfolded to the carrier: every element of the group of a
representative is attached to some base element by the almost-everywhere identity. -/
theorem mem_carrier (x : TeichRep Γ₀) (W : ↥x.group) :
    ∃ γ ∈ Γ₀, ∀ᵐ z : ℂ, x.w (moebiusMap γ z)
      = moebiusMap (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x.w z) := by
  have hmem : (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ fuchsianImageCarrier Γ₀ x.w :=
    W.2
  exact hmem

/-- A choice of base element attached to an element of the image group. -/
noncomputable def baseOf (x : TeichRep Γ₀) (W : ↥x.group) : ↥Γ₀ :=
  ⟨(mem_carrier x W).choose, (mem_carrier x W).choose_spec.1⟩

/-- The chosen base element satisfies the almost-everywhere conjugation identity. -/
theorem baseOf_spec (x : TeichRep Γ₀) (W : ↥x.group) :
    ∀ᵐ z : ℂ, x.w (moebiusMap
        ((baseOf x W : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) z)
      = moebiusMap (W : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x.w z) :=
  (mem_carrier x W).choose_spec.2

/-- A character of the image group takes equal values on any two conjugators of the same
base element: the conjugators agree up to matrix sign, which characters do not see. -/
theorem apply_conj_eq (x : TeichRep Γ₀) (f : homSubmodule (↥x.group))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {U V : ↥x.group}
    (hU : ∀ᵐ z : ℂ, x.w (moebiusMap γ z)
      = moebiusMap (U : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x.w z))
    (hV : ∀ᵐ z : ℂ, x.w (moebiusMap γ z)
      = moebiusMap (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x.w z)) :
    (f : (↥x.group) → ℝ) U = (f : (↥x.group) → ℝ) V := by
  rcases conjugator_sign x hU hV with heq | hneg
  · have hUV : U = V := Subtype.ext (Subtype.ext heq)
    rw [hUV]
  · exact homSubmodule_apply_eq_of_neg_matrix f hneg

/-- A character of the base group takes equal values on any two base elements attached to
the same image element: the base elements agree up to matrix sign, which characters do not
see. -/
theorem apply_base_eq (x : TeichRep Γ₀) (g : homSubmodule (↥Γ₀))
    {W : Matrix.SpecialLinearGroup (Fin 2) ℝ} {γ δ : ↥Γ₀}
    (hγ : ∀ᵐ z : ℂ, x.w (moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) z)
      = moebiusMap W (x.w z))
    (hδ : ∀ᵐ z : ℂ, x.w (moebiusMap (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) z)
      = moebiusMap W (x.w z)) :
    (g : (↥Γ₀) → ℝ) γ = (g : (↥Γ₀) → ℝ) δ := by
  rcases base_sign x hγ hδ with heq | hneg
  · have hγδ : γ = δ := Subtype.ext (Subtype.ext heq)
    rw [hγδ]
  · exact homSubmodule_apply_eq_of_neg_matrix g hneg

/-- The forward transport of characters: pull back along the conjugator choice. The value
on a product is the value on the product of the conjugators by conjugator rigidity, so the
transported function is again a character. -/
noncomputable def transportFwd (x : TeichRep Γ₀) :
    homSubmodule (↥x.group) →ₗ[ℝ] homSubmodule (↥Γ₀) where
  toFun f := ⟨fun γ => (f : (↥x.group) → ℝ) (conjOf x γ), by
    change ∀ a b : ↥Γ₀, (f : (↥x.group) → ℝ) (conjOf x (a * b))
      = (f : (↥x.group) → ℝ) (conjOf x a) + (f : (↥x.group) → ℝ) (conjOf x b)
    intro a b
    have hab := conjOf_spec x (a * b)
    have hcab : ((a * b : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        = ((a : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          * ((b : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := rfl
    rw [hcab] at hab
    have hprod : ∀ᵐ z : ℂ, x.w (moebiusMap
        (((a : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          * ((b : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)) z)
        = moebiusMap ((conjOf x a * conjOf x b :
            ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x.w z) := by
      have hc2 : ((conjOf x a * conjOf x b :
            ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          = ((conjOf x a : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            * ((conjOf x b : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := rfl
      rw [hc2]
      exact ae_conj_mul x (conjOf_spec x a) (conjOf_spec x b)
    have hkey := apply_conj_eq x f hab hprod
    rw [hkey]
    exact f.2 _ _⟩
  map_add' f g := by
    apply Subtype.ext
    funext γ
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext γ
    rfl

/-- The backward transport of characters: pull back along the base-element choice. The
value on a product is the value on the product of the base elements by base rigidity, so
the transported function is again a character. -/
noncomputable def transportBwd (x : TeichRep Γ₀) :
    homSubmodule (↥Γ₀) →ₗ[ℝ] homSubmodule (↥x.group) where
  toFun g := ⟨fun W => (g : (↥Γ₀) → ℝ) (baseOf x W), by
    change ∀ U V : ↥x.group, (g : (↥Γ₀) → ℝ) (baseOf x (U * V))
      = (g : (↥Γ₀) → ℝ) (baseOf x U) + (g : (↥Γ₀) → ℝ) (baseOf x V)
    intro U V
    have hUV := baseOf_spec x (U * V)
    have hcUV : ((U * V : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        = ((U : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          * ((V : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := rfl
    rw [hcUV] at hUV
    have hprod : ∀ᵐ z : ℂ, x.w (moebiusMap
        ((baseOf x U * baseOf x V :
          ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) z)
        = moebiusMap (((U : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            * ((V : ↥x.group) : Matrix.SpecialLinearGroup (Fin 2) ℝ)) (x.w z) := by
      have hc2 : ((baseOf x U * baseOf x V :
            ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          = ((baseOf x U : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            * ((baseOf x V : ↥Γ₀) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := rfl
      rw [hc2]
      exact ae_conj_mul x (baseOf_spec x U) (baseOf_spec x V)
    have hkey := apply_base_eq x g hUV hprod
    rw [hkey]
    exact g.2 _ _⟩
  map_add' f g := by
    apply Subtype.ext
    funext W
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext W
    rfl

/-- **Character transport**: the character spaces of the Fuchsian group of a Teichmüller
representative and of the base group are linearly isomorphic. A character of the image
group pulls back along `γ ↦ W` of the almost-everywhere Möbius equivariance of the
normalized solution; the conjugator is unique up to sign since two conjugators agree at
three points, and characters do not see the sign. -/
theorem TeichRep.exists_homSubmodule_linearEquiv (x : TeichRep Γ₀) :
    Nonempty (homSubmodule (↥x.group) ≃ₗ[ℝ] homSubmodule (↥Γ₀)) := by
  refine ⟨LinearEquiv.ofLinear (transportFwd x) (transportBwd x) ?_ ?_⟩
  · apply LinearMap.ext
    intro g
    apply Subtype.ext
    funext γ
    change (g : (↥Γ₀) → ℝ) (baseOf x (conjOf x γ)) = (g : (↥Γ₀) → ℝ) γ
    exact apply_base_eq x g (baseOf_spec x (conjOf x γ))
      (conjOf_spec x γ)
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext W
    change (f : (↥x.group) → ℝ) (conjOf x (baseOf x W))
      = (f : (↥x.group) → ℝ) W
    exact apply_conj_eq x f (conjOf_spec x (baseOf x W))
      (baseOf_spec x W)

/-- **Covolume rigidity across the family**: the Fuchsian group of every Teichmüller
representative has the covolume of the base group — both covolumes are `2π (Q - 2)` for
the common character-space dimension `Q`. -/
theorem TeichRep.fuchsianCovolume_group (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x : TeichRep Γ₀) :
    fuchsianCovolume x.group = fuchsianCovolume Γ₀ := by
  obtain ⟨e⟩ := x.exists_homSubmodule_linearEquiv
  rw [fuchsianCovolume_eq_two_pi_mul (x.isFuchsian_group hΓ₀ hfree) (x.group_free hfree)
      (x.group_cocompact hcc),
    fuchsianCovolume_eq_two_pi_mul hΓ₀ hfree hcc, e.finrank_eq]

/-! ## The uniform area bound -/

/-- **Uniform Gauss–Bonnet area bound**: the Fuchsian group of every Teichmüller
representative over a cocompact free base admits its Dirichlet domain as a covering set of
volume the covolume of the base group. -/
theorem TeichRep.hasAreaBound_covol (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x : TeichRep Γ₀) :
    HasAreaBound x.group (fuchsianCovolume Γ₀) := by
  refine ⟨dirichletDomain x.group UpperHalfPlane.I,
    (isClosed_dirichletDomain x.group UpperHalfPlane.I).measurableSet,
    Filter.Eventually.of_forall fun τ =>
      exists_smul_mem_dirichletDomain (TeichRep.isFuchsian_group hΓ₀ hfree x)
        UpperHalfPlane.I τ, ?_⟩
  exact le_of_eq (TeichRep.fuchsianCovolume_group hΓ₀ hfree hcc x)

/-! ## The Mumford subconvergence theorems with the area hypothesis discharged -/

/-- **Thick Mumford subconvergence, uniform form**: the area hypothesis of
`mumford_subconvergence_thick` holds for every representative with the covolume of the base
group as the bound, so a thick sequence carries subconvergent ball-generator tuples whose
limit generates a trace-gapped, free, Fuchsian, cocompact group with an explicit
covering-volume bound. -/
theorem mumford_subconvergence_thick_uniform (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {ε : ℝ} (hε : 0 < ε)
    (x : ℕ → TeichRep Γ₀) (hthick : ∀ n, ε ≤ systoleRep (x n)) :
    ∃ (φ : ℕ → ℕ)
      (gens : ℕ →
        Fin (ballGensCard ε (2 * mumfordDensityBound (fuchsianCovolume Γ₀) ε + 1)) →
        Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (ρ : Fin (ballGensCard ε (2 * mumfordDensityBound (fuchsianCovolume Γ₀) ε + 1)) →
        Matrix.SpecialLinearGroup (Fin 2) ℝ),
      StrictMono φ ∧
      (∀ k i, gens k i ∈ (x (φ k)).group) ∧
      (∀ k, Subgroup.closure (Set.range (gens k)) = (x (φ k)).group) ∧
      (∀ i, Filter.Tendsto (fun k => gens k i) Filter.atTop (nhds (ρ i))) ∧
      (∀ h ∈ Subgroup.closure (Set.range ρ), actsNontrivially h →
        2 * Real.cosh (ε / 2) ≤ |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)|) ∧
      IsFuchsianGroup (Subgroup.closure (Set.range ρ)) ∧
      (∀ h : Subgroup.closure (Set.range ρ), (∃ τ : UpperHalfPlane, h • τ = τ) →
        ∀ τ' : UpperHalfPlane, h • τ' = τ') ∧
      CompactSpace (Quotient (MulAction.orbitRel (Subgroup.closure (Set.range ρ))
        UpperHalfPlane)) ∧
      HasAreaBound (Subgroup.closure (Set.range ρ))
        (volume (Metric.closedBall UpperHalfPlane.I
          (mumfordDensityBound (fuchsianCovolume Γ₀) ε + 1))) :=
  mumford_subconvergence_thick hΓ₀ hfree hcc hε (fuchsianCovolume_ne_top hΓ₀ hfree hcc)
    x hthick fun n => TeichRep.hasAreaBound_covol hΓ₀ hfree hcc (x n)

/-- **Mumford subconvergence in the Teichmüller metric, uniform form**: a thick sequence
subconverges, modulo upper-half-plane re-markings, to a point of Teichmüller space; the
area hypothesis is discharged by the covolume of the base group. -/
theorem mumford_dT_subconvergence_uniform (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {ε : ℝ} (hε : 0 < ε)
    (x : ℕ → TeichRep Γ₀) (hthick : ∀ n, ε ≤ systoleRep (x n)) :
    ∃ (φ : ℕ → ℕ) (F : ℕ → ModGroupUpper Γ₀) (y : TeichRep Γ₀), StrictMono φ ∧
      Filter.Tendsto (fun k => dist (F k • Teich.mk (x (φ k))) (Teich.mk y))
        Filter.atTop (nhds 0) :=
  mumford_dT_subconvergence hΓ₀ hfree hcc hε (fuchsianCovolume_ne_top hΓ₀ hfree hcc)
    x hthick fun n => TeichRep.hasAreaBound_covol hΓ₀ hfree hcc (x n)

end RiemannDynamics
