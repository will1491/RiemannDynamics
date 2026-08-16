/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Polygon.Basic

/-!
# The Dirichlet polygon: the sign of the disc frame at an axis point

The disc-model frame at an axis point separates the two strict sides of the bisector by
the sign of its imaginary part (`discChart_im_sign` and its transport along contact
elements, `contact_shift`); the vertex data is equivariant under the group action
(`tileCenters_smul`). These sign controls orient the tiles around a vertex and feed the
star and fan development.
-/

open MeasureTheory
open scoped ENNReal MatrixGroups

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## The sign of the disc frame at an axis point -/

/-- Based at an axis point, the imaginary part of the disc frame has the sign opposite to
the real part of the argument. -/
theorem discChart_im_sign {z : UpperHalfPlane} (hz : z.re = 0) (w : UpperHalfPlane) :
    ((0 : ℝ) < (discChart z w).im ↔ w.re < 0) ∧
      ((discChart z w).im = 0 ↔ w.re = 0) ∧
      ((discChart z w).im < 0 ↔ 0 < w.re) := by
  have hyy : 0 < z.im := z.im_pos
  have hden_im : ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I).im = w.im / z.im + 1 := by
    rw [Complex.add_im, Complex.div_ofReal_im, Complex.I_im, UpperHalfPlane.coe_im]
  have hden_ne : ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I) ≠ 0 := by
    intro hc
    have h2 := congrArg Complex.im hc
    rw [hden_im, Complex.zero_im] at h2
    have h3 : 0 < w.im / z.im := div_pos w.im_pos hyy
    linarith
  have hN : 0 < Complex.normSq ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I) :=
    Complex.normSq_pos.mpr hden_ne
  have him : (discChart z w).im = -2 * (w.re / z.im)
      / Complex.normSq ((w : ℂ) / ((z.im : ℝ) : ℂ) + Complex.I) := by
    rw [discChart, hz]
    rw [show ((0 : ℝ) : ℂ) = 0 by norm_num, sub_zero, Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.I_re, Complex.I_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, sub_zero, add_zero]
    ring
  have hfirst : (0 : ℝ) < (discChart z w).im ↔ w.re < 0 := by
    rw [him]
    constructor
    · intro h
      have h2 := mul_pos h hN
      rw [div_mul_cancel₀ _ hN.ne'] at h2
      have h3 : w.re / z.im < 0 := by linarith
      rcases div_neg_iff.mp h3 with ⟨-, h4⟩ | ⟨h4, -⟩
      · linarith
      · exact h4
    · intro h
      refine div_pos ?_ hN
      have h3 : w.re / z.im < 0 := div_neg_of_neg_of_pos h hyy
      linarith
  have hsecond : (discChart z w).im = 0 ↔ w.re = 0 := by
    rw [him]
    rw [div_eq_zero_iff]
    constructor
    · intro h
      rcases h with h | h
      · have h2 : w.re / z.im = 0 := by linarith
        rcases div_eq_zero_iff.mp h2 with h3 | h3
        · exact h3
        · exact absurd h3 hyy.ne'
      · exact absurd h hN.ne'
    · intro h
      left
      rw [h, zero_div, mul_zero]
  refine ⟨hfirst, hsecond, ?_⟩
  constructor
  · intro h
    rcases lt_trichotomy w.re 0 with hr | hr | hr
    · exact absurd (hfirst.mpr hr) (by linarith)
    · exact absurd (hsecond.mpr hr) (by linarith)
    · exact hr
  · intro h
    rcases lt_trichotomy (discChart z w).im 0 with hr | hr | hr
    · exact hr
    · exact absurd (hsecond.mp hr) (by linarith)
    · exact absurd (hfirst.mp hr) (by linarith)

/-- The half-space of a bisector through `v`, read in the disc frame at `v`: a real-linear
functional of the frame value is zero exactly on the bisector and positive exactly on the
open near side. -/
theorem functional_sign {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {v : UpperHalfPlane} (hv : dist v p = dist v q) :
    ∃ m : ℂ, m ≠ 0 ∧
      (∀ w : UpperHalfPlane, dist w p = dist w q → ε' * (m * discChart v w).im = 0) ∧
      (∀ w : UpperHalfPlane, dist w p < dist w q → 0 < ε' * (m * discChart v w).im) := by
  have hvre : (g • v).re = 0 := normalizer_re_eq_zero hε' hle hge hv
  have hzim : ((v : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact v.im_pos.ne'
  have hzbim : (((starRingEnd ℂ) (v : ℂ))).im ≠ 0 := by
    rw [Complex.conj_im, UpperHalfPlane.coe_im]
    simpa using v.im_pos.ne'
  refine ⟨(((g 1 0 : ℝ) : ℂ) * (starRingEnd ℂ) (v : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (v : ℂ) + ((g 1 1 : ℝ) : ℂ)), ?_, ?_, ?_⟩
  · exact div_ne_zero (denom_ne_zero g hzbim) (denom_ne_zero g hzim)
  · intro w hw
    rw [(discChart_smul g v w).symm]
    have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
    rw [((discChart_im_sign hvre (g • w)).2.1).mpr hgw, mul_zero]
  · intro w hw
    rw [(discChart_smul g v w).symm]
    have hlt : ε' * (g • w).re < 0 := (normalizer_lt_iff hle hge w).mp hw
    rcases hε' with hE | hE
    · rw [hE, one_mul] at hlt ⊢
      exact ((discChart_im_sign hvre (g • w)).1).mpr hlt
    · rw [hE] at hlt ⊢
      have h2 : 0 < (g • w).re := by linarith
      have h3 := ((discChart_im_sign hvre (g • w)).2.2).mpr h2
      rw [neg_one_mul]
      exact neg_pos.mpr h3

set_option maxHeartbeats 400000 in
-- The three-normalizer assembly elaborates nine sign facts and a Cramer decomposition in
-- one declaration; the default heartbeat budget does not cover it.
/-- No point lies on three pairwise distinct sides: the boundary directions of the three
bisector half-planes through the point admit no compatible sign pattern. -/
theorem not_three_sides
    {γ₁ γ₂ γ₃ : ↥Γ} (h₁ : IsSideElement Γ τ₀ γ₁) (h₂ : IsSideElement Γ τ₀ γ₂)
    (h₃ : IsSideElement Γ τ₀ γ₃) {v : UpperHalfPlane}
    (hv₁ : v ∈ dirichletSideSet Γ τ₀ γ₁) (hv₂ : v ∈ dirichletSideSet Γ τ₀ γ₂)
    (hv₃ : v ∈ dirichletSideSet Γ τ₀ γ₃)
    (h12 : dirichletSideSet Γ τ₀ γ₁ ≠ dirichletSideSet Γ τ₀ γ₂)
    (h13 : dirichletSideSet Γ τ₀ γ₁ ≠ dirichletSideSet Γ τ₀ γ₃)
    (h23 : dirichletSideSet Γ τ₀ γ₂ ≠ dirichletSideSet Γ τ₀ γ₃) : False := by
  classical
  have hp12 : γ₁ • τ₀ ≠ γ₂ • τ₀ := fun hc => h12 (sideSet_eq_of_basepoint_eq hc)
  have hp13 : γ₁ • τ₀ ≠ γ₃ • τ₀ := fun hc => h13 (sideSet_eq_of_basepoint_eq hc)
  have hp23 : γ₂ • τ₀ ≠ γ₃ • τ₀ := fun hc => h23 (sideSet_eq_of_basepoint_eq hc)
  have hpick : ∀ γ : ↥Γ, (dirichletSideSet Γ τ₀ γ).Nontrivial →
      ∃ b ∈ dirichletSideSet Γ τ₀ γ, b ≠ v := by
    intro γ hnt
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    by_cases hxv : x = v
    · exact ⟨y, hy, fun h => hxy (hxv.trans h.symm)⟩
    · exact ⟨x, hx, hxv⟩
  obtain ⟨b₁, hb₁, hb₁v⟩ := hpick γ₁ h₁.2
  obtain ⟨b₂, hb₂, hb₂v⟩ := hpick γ₂ h₂.2
  obtain ⟨b₃, hb₃, hb₃v⟩ := hpick γ₃ h₃.2
  have hstrict : ∀ γa γb : ↥Γ, γa • τ₀ ≠ γb • τ₀ → γa • τ₀ ≠ τ₀ → γb • τ₀ ≠ τ₀ →
      dist v τ₀ = dist v (γa • τ₀) → dist v τ₀ = dist v (γb • τ₀) →
      ∀ b ∈ dirichletSideSet Γ τ₀ γa, b ≠ v → dist b τ₀ < dist b (γb • τ₀) := by
    intro γa γb hab ha hb hva hvb b hbmem hbv
    rcases lt_or_eq_of_le (hbmem.1 γb) with h | h
    · exact h
    · exact absurd (bisector_pair_unique (Ne.symm hbv) hva hbmem.2 hvb h ha hb) hab
  obtain ⟨g₁, ε₁, hε₁, hle₁, hge₁⟩ := bisector_normalizer (Ne.symm h₁.1)
  obtain ⟨g₂, ε₂, hε₂, hle₂, hge₂⟩ := bisector_normalizer (Ne.symm h₂.1)
  obtain ⟨g₃, ε₃, hε₃, hle₃, hge₃⟩ := bisector_normalizer (Ne.symm h₃.1)
  obtain ⟨m₁, hm₁, hf₁eq, hf₁lt⟩ := functional_sign hε₁ hle₁ hge₁ hv₁.2
  obtain ⟨m₂, hm₂, hf₂eq, hf₂lt⟩ := functional_sign hε₂ hle₂ hge₂ hv₂.2
  obtain ⟨m₃, hm₃, hf₃eq, hf₃lt⟩ := functional_sign hε₃ hle₃ hge₃ hv₃.2
  set d₁ : ℂ := discChart v b₁ with hd₁
  set d₂ : ℂ := discChart v b₂ with hd₂
  set d₃ : ℂ := discChart v b₃ with hd₃
  have hd₁ne : d₁ ≠ 0 := discChart_ne_zero hb₁v
  have hd₂ne : d₂ ≠ 0 := discChart_ne_zero hb₂v
  have hd₃ne : d₃ ≠ 0 := discChart_ne_zero hb₃v
  have hL11 : ε₁ * (m₁ * d₁).im = 0 := hf₁eq b₁ hb₁.2
  have hL22 : ε₂ * (m₂ * d₂).im = 0 := hf₂eq b₂ hb₂.2
  have hL33 : ε₃ * (m₃ * d₃).im = 0 := hf₃eq b₃ hb₃.2
  have hL12 : 0 < ε₂ * (m₂ * d₁).im :=
    hf₂lt b₁ (hstrict γ₁ γ₂ hp12 h₁.1 h₂.1 hv₁.2 hv₂.2 b₁ hb₁ hb₁v)
  have hL13 : 0 < ε₃ * (m₃ * d₁).im :=
    hf₃lt b₁ (hstrict γ₁ γ₃ hp13 h₁.1 h₃.1 hv₁.2 hv₃.2 b₁ hb₁ hb₁v)
  have hL21 : 0 < ε₁ * (m₁ * d₂).im :=
    hf₁lt b₂ (hstrict γ₂ γ₁ (Ne.symm hp12) h₂.1 h₁.1 hv₂.2 hv₁.2 b₂ hb₂ hb₂v)
  have hL23 : 0 < ε₃ * (m₃ * d₂).im :=
    hf₃lt b₂ (hstrict γ₂ γ₃ hp23 h₂.1 h₃.1 hv₂.2 hv₃.2 b₂ hb₂ hb₂v)
  have hL31 : 0 < ε₁ * (m₁ * d₃).im :=
    hf₁lt b₃ (hstrict γ₃ γ₁ (Ne.symm hp13) h₃.1 h₁.1 hv₃.2 hv₁.2 b₃ hb₃ hb₃v)
  have hL32 : 0 < ε₂ * (m₂ * d₃).im :=
    hf₂lt b₃ (hstrict γ₃ γ₂ (Ne.symm hp23) h₃.1 h₂.1 hv₃.2 hv₂.2 b₃ hb₃ hb₃v)
  have hlin : ∀ (m : ℂ) (e α β : ℝ) (ξ ζ : ℂ),
      e * (m * ((α : ℂ) * ξ + (β : ℂ) * ζ)).im
        = α * (e * (m * ξ).im) + β * (e * (m * ζ).im) := by
    intro m e α β ξ ζ
    have h1 : m * ((α : ℂ) * ξ + (β : ℂ) * ζ) = (α : ℂ) * (m * ξ) + (β : ℂ) * (m * ζ) := by
      ring
    rw [h1, Complex.add_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring
  have hΔne : d₁.re * d₂.im - d₁.im * d₂.re ≠ 0 := by
    intro hΔ0
    have hnsq : 0 < d₁.re * d₁.re + d₁.im * d₁.im := by
      have h4 := Complex.normSq_pos.mpr hd₁ne
      rwa [Complex.normSq_apply] at h4
    have hd₂eq : d₂ = (((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) : ℝ) : ℂ) * d₁ := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]
        rw [div_mul_eq_mul_div, eq_div_iff hnsq.ne']
        linear_combination -d₁.im * hΔ0
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]
        rw [div_mul_eq_mul_div, eq_div_iff hnsq.ne']
        linear_combination d₁.re * hΔ0
    have h4 : ε₂ * (m₂ * d₂).im = ((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im)) * (ε₂ * (m₂ * d₁).im) := by
      conv_lhs => rw [hd₂eq]
      have h5 := hlin m₂ ε₂ ((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im)) 0 d₁ 0
      rw [show ((0:ℝ) : ℂ) * (0 : ℂ) = 0 by ring] at h5
      rw [show (((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) : ℝ) : ℂ) * d₁ + 0
          = (((d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) : ℝ) : ℂ) * d₁ by ring] at h5
      rw [h5]
      simp
    rw [hL22] at h4
    have hc0 : (d₁.re * d₂.re + d₁.im * d₂.im)
        / (d₁.re * d₁.re + d₁.im * d₁.im) = 0 := by
      rcases mul_eq_zero.mp h4.symm with h | h
      · exact h
      · linarith
    rw [hc0] at hd₂eq
    push_cast at hd₂eq
    rw [zero_mul] at hd₂eq
    exact hd₂ne hd₂eq
  set α : ℝ := (d₃.re * d₂.im - d₃.im * d₂.re) / (d₁.re * d₂.im - d₁.im * d₂.re) with hα
  set β : ℝ := (d₁.re * d₃.im - d₁.im * d₃.re) / (d₁.re * d₂.im - d₁.im * d₂.re) with hβ
  have hdecomp : d₃ = (α : ℂ) * d₁ + (β : ℂ) * d₂ := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        eq_div_iff hΔne]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      rw [hα, hβ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        eq_div_iff hΔne]
      ring
  have hE1 : ε₁ * (m₁ * d₃).im = α * (ε₁ * (m₁ * d₁).im) + β * (ε₁ * (m₁ * d₂).im) := by
    conv_lhs => rw [hdecomp]
    exact hlin m₁ ε₁ α β d₁ d₂
  have hE2 : ε₂ * (m₂ * d₃).im = α * (ε₂ * (m₂ * d₁).im) + β * (ε₂ * (m₂ * d₂).im) := by
    conv_lhs => rw [hdecomp]
    exact hlin m₂ ε₂ α β d₁ d₂
  have hE3 : ε₃ * (m₃ * d₃).im = α * (ε₃ * (m₃ * d₁).im) + β * (ε₃ * (m₃ * d₂).im) := by
    conv_lhs => rw [hdecomp]
    exact hlin m₃ ε₃ α β d₁ d₂
  rw [hL11] at hE1
  rw [hL22] at hE2
  rw [hL33] at hE3
  have hβpos : 0 < β := by
    by_contra hc
    push Not at hc
    nlinarith [hL31, hL21, hE1]
  have hαneg : α < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [hL13, hL23, hE3]
  nlinarith [hL32, hL12, hE2]

/-- A positive radius within which any point of any side forces the side through `v`. -/
theorem exists_sep_radius (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (v : UpperHalfPlane) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ s ∈ polygonSides Γ τ₀, ∀ w ∈ s, dist w v < ρ₀ → v ∈ s := by
  classical
  have hfin : ({s ∈ polygonSides Γ τ₀ | v ∉ s}).Finite :=
    (finite_polygonSides hΓ hfree hε hgap hdense).subset (fun s hs => hs.1)
  have hpos : ∀ s ∈ {s ∈ polygonSides Γ τ₀ | v ∉ s}, 0 < Metric.infDist v s := by
    rintro s ⟨hs, hvs⟩
    obtain ⟨γ, ⟨hmove, hnt⟩, rfl⟩ := hs
    have hclosed : IsClosed (dirichletSideSet Γ τ₀ γ) :=
      (isClosed_dirichletDomain Γ τ₀).inter (isClosed_eq
        (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
    exact (hclosed.notMem_iff_infDist_pos hnt.nonempty).mp hvs
  rcases Set.eq_empty_or_nonempty {s ∈ polygonSides Γ τ₀ | v ∉ s} with hemp | hnem
  · refine ⟨1, one_pos, ?_⟩
    intro s hs w hw hd
    by_contra hvs
    have h1 : s ∈ {s ∈ polygonSides Γ τ₀ | v ∉ s} := ⟨hs, hvs⟩
    rw [hemp] at h1
    exact h1
  · obtain ⟨s₀, hs₀, hs₀min⟩ := Set.exists_min_image _
      (fun s => Metric.infDist v s) hfin hnem
    refine ⟨Metric.infDist v s₀, hpos s₀ hs₀, ?_⟩
    intro s hs w hw hd
    by_contra hvs
    have h1 : Metric.infDist v s₀ ≤ Metric.infDist v s := hs₀min s ⟨hs, hvs⟩
    have h2 : Metric.infDist v s ≤ dist v w := Metric.infDist_le_dist_of_mem hw
    rw [dist_comm v w] at h2
    linarith

set_option maxHeartbeats 400000 in
-- The two-sides extraction runs the frontier-accumulation, crossing, and three-sides
-- exclusion arguments in one declaration; the default heartbeat budget does not cover it.
/-- **Two sides per vertex**: each vertex is an endpoint of exactly two sides, the two
boundary rays of the local convex sector of the domain at the vertex. -/
theorem exists_two_sides_at_vertex (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) :
    ∃ s₁ ∈ polygonSides Γ τ₀, ∃ s₂ ∈ polygonSides Γ τ₀, s₁ ≠ s₂ ∧
      IsSegEndpoint s₁ v ∧ IsSegEndpoint s₂ v ∧
      ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v → s = s₁ ∨ s = s₂ := by
  classical
  obtain ⟨hvD, hv3⟩ := hv
  have hvint : v ∉ interior (dirichletDomain Γ τ₀) := by
    intro hcon
    have h1 : v ∈ ((1 : ↥Γ) • ·) '' interior (dirichletDomain Γ τ₀) :=
      ⟨v, hcon, one_smul _ _⟩
    rw [mem_smul_interior_iff_contactSet_eq hΓ hdense] at h1
    have h2 : tileCenters Γ τ₀ v ⊆ {τ₀} := by
      rintro c ⟨δ, hδ, rfl⟩
      rw [h1] at hδ
      have h3 : δ • τ₀ = (1 : ↥Γ) • τ₀ := hδ
      rw [one_smul] at h3
      exact h3
    have h3 := Set.ncard_le_ncard h2 (Set.finite_singleton τ₀)
    rw [Set.ncard_singleton] at h3
    omega
  have hvτ : v ≠ τ₀ := by
    intro h
    rw [h] at hvint
    exact hvint (basepoint_mem_interior_dirichletDomain hε hgap)
  obtain ⟨ρ₀, hρ₀, hsep⟩ := exists_sep_radius hΓ hfree hε hgap hdense v
  have hfr : ∀ ρ : ℝ, 0 < ρ → ∃ w, w ∈ frontier (dirichletDomain Γ τ₀) ∧ w ≠ v ∧
      dist w v < ρ := by
    intro ρ hρ
    by_contra hcon
    push Not at hcon
    have hpre := isPreconnected_punctured_ball v ρ
    have hcover : Metric.ball v ρ \ {v} ⊆ interior (dirichletDomain Γ τ₀) ∪
        (dirichletDomain Γ τ₀)ᶜ := by
      rintro w ⟨hwB, hwne⟩
      have hwv : w ≠ v := fun h => hwne (by rw [h]; exact rfl)
      by_cases hwD : w ∈ dirichletDomain Γ τ₀
      · left
        have hwfr : w ∉ frontier (dirichletDomain Γ τ₀) := by
          intro hf
          exact absurd (Metric.mem_ball.mp hwB) (not_lt.mpr (hcon w hf hwv))
        rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hwfr
        by_cases hwint : w ∈ interior (dirichletDomain Γ τ₀)
        · exact hwint
        · exact absurd ⟨hwD, hwint⟩ hwfr
      · right
        exact hwD
    have hne1 : ((Metric.ball v ρ \ {v}) ∩ interior (dirichletDomain Γ τ₀)).Nonempty := by
      obtain ⟨w, hwseg, hwv, hwd⟩ := exists_near_on_geodSeg (Ne.symm hvτ) hρ
      exact ⟨w, ⟨Metric.mem_ball.mpr hwd, fun hc => hwv (Set.mem_singleton_iff.mp hc)⟩,
        mem_interior_of_mem_geodSeg hΓ hdense hvD hwseg hwv⟩
    have hne2 : ((Metric.ball v ρ \ {v}) ∩ (dirichletDomain Γ τ₀)ᶜ).Nonempty := by
      by_contra h2
      rw [Set.not_nonempty_iff_eq_empty] at h2
      have hball : Metric.ball v ρ ⊆ dirichletDomain Γ τ₀ := by
        intro y hy
        by_contra hyD
        by_cases hyv : y = v
        · rw [hyv] at hyD
          exact hyD hvD
        · have h4 : y ∈ (Metric.ball v ρ \ {v}) ∩ (dirichletDomain Γ τ₀)ᶜ :=
            ⟨⟨hy, fun hc => hyv (Set.mem_singleton_iff.mp hc)⟩, hyD⟩
          rw [h2] at h4
          exact h4
      exact hvint (interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hρ))
    obtain ⟨z0, hz0⟩ := hpre (interior (dirichletDomain Γ τ₀)) (dirichletDomain Γ τ₀)ᶜ
      isOpen_interior (isClosed_dirichletDomain Γ τ₀).isOpen_compl hcover hne1 hne2
    exact hz0.2.2 (interior_subset hz0.2.1)
  obtain ⟨w₁, hw₁fr, hw₁v, hw₁d⟩ := hfr ρ₀ hρ₀
  have hw₁un : w₁ ∈ ⋃₀ polygonSides Γ τ₀ := by
    rw [← frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
    exact hw₁fr
  obtain ⟨s₁, hs₁mem, hw₁s⟩ := hw₁un
  have hvs₁ : v ∈ s₁ := hsep s₁ hs₁mem w₁ hw₁s hw₁d
  have hend₁ : IsSegEndpoint s₁ v :=
    isSegEndpoint_of_vertex hΓ hfree hε hgap hdense ⟨hvD, hv3⟩ hs₁mem hvs₁
  obtain ⟨a, b, hab, hs₁eq⟩ :=
    exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs₁mem
  obtain ⟨e₁, he₁v, hs₁eq'⟩ : ∃ e₁ : UpperHalfPlane, e₁ ≠ v ∧ s₁ = geodSeg v e₁ := by
    have hend' : IsSegEndpoint (geodSeg a b) v := by rw [← hs₁eq]; exact hend₁
    rcases (isSegEndpoint_geodSeg_iff hab).mp hend' with h | h
    · refine ⟨b, ?_, by rw [hs₁eq, ← h]⟩
      intro hc
      rw [← h] at hab
      exact hab (hc.symm ▸ rfl)
    · refine ⟨a, ?_, by rw [hs₁eq, ← h, geodSeg_comm]⟩
      intro hc
      rw [← h] at hab
      exact hab (hc ▸ rfl)
  obtain ⟨γ₁, hγ₁elem, hs₁def⟩ := hs₁mem
  have hvseq : dist v τ₀ = dist v (γ₁ • τ₀) := by
    have h5 : v ∈ dirichletSideSet Γ τ₀ γ₁ := by rw [← hs₁def]; exact hvs₁
    exact h5.2
  have he₁seq : dist e₁ τ₀ = dist e₁ (γ₁ • τ₀) := by
    have h5 : e₁ ∈ dirichletSideSet Γ τ₀ γ₁ := by
      rw [← hs₁def, hs₁eq']
      exact right_mem_geodSeg v e₁
    exact h5.2
  obtain ⟨wb, hwb_eq, hwb_dist, hwb_between⟩ := exists_beyond
    (Ne.symm hγ₁elem.1) hvseq he₁seq (Ne.symm he₁v)
    (show (0:ℝ) < ρ₀ / 4 by linarith)
  have hwbD : wb ∉ dirichletDomain Γ τ₀ := by
    intro hwbDmem
    have hwbside : wb ∈ geodSeg v e₁ := by
      rw [← hs₁eq', hs₁def]
      exact ⟨hwbDmem, hwb_eq⟩
    have hEnd := (isSegEndpoint_geodSeg_iff (Ne.symm he₁v)).mpr (Or.inl rfl)
    rcases hEnd.2 wb hwbside e₁ (right_mem_geodSeg v e₁) hwb_between with h4 | h4
    · rw [← h4, dist_self] at hwb_dist
      linarith
    · exact he₁v h4.symm
  obtain ⟨xi, hxiseg, hxiv, hxid⟩ := exists_near_on_geodSeg (Ne.symm hvτ)
    (show (0:ℝ) < ρ₀ / 4 by linarith)
  have hxiint : xi ∈ interior (dirichletDomain Γ τ₀) :=
    mem_interior_of_mem_geodSeg hΓ hdense hvD hxiseg hxiv
  have hxiD : xi ∈ dirichletDomain Γ τ₀ := interior_subset hxiint
  have hxioff : dist xi τ₀ ≠ dist xi (γ₁ • τ₀) := by
    rw [interior_dirichletDomain_eq hΓ hdense] at hxiint
    exact ne_of_lt (hxiint γ₁ hγ₁elem.1)
  obtain ⟨w₂, hw₂seg, hw₂fr⟩ := exists_frontier_mem_geodSeg hxiD hwbD
  have hw₂D : w₂ ∈ dirichletDomain Γ τ₀ := by
    rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hw₂fr
    exact hw₂fr.1
  have hw₂wb : w₂ ≠ wb := fun h => hwbD (h ▸ hw₂D)
  have hw₂off : dist w₂ τ₀ ≠ dist w₂ (γ₁ • τ₀) := by
    intro hw₂eq
    obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer (Ne.symm hγ₁elem.1)
    have hgwb : (g • wb).re = 0 := normalizer_re_eq_zero hε' hle hge hwb_eq
    have hgw₂ : (g • w₂).re = 0 := normalizer_re_eq_zero hε' hle hge hw₂eq
    by_cases hAB : (g • xi).re = (g • wb).re
    · refine hxioff ((normalizer_eq_iff hε' hle hge xi).mpr ?_)
      rw [hAB, hgwb]
    · have hseg' : g • w₂ ∈ geodSeg (g • xi) (g • wb) := by
        rw [← smul_geodSeg]
        exact ⟨w₂, hw₂seg, rfl⟩
      have h5 := eq_of_re_eq_of_mem_geodSeg hAB hseg' (right_mem_geodSeg _ _)
        (by rw [hgw₂, hgwb])
      exact hw₂wb (smul_left_cancel g h5)
  have hw₂s₁ : w₂ ∉ s₁ := by
    intro hcon
    have h5 : w₂ ∈ dirichletSideSet Γ τ₀ γ₁ := by rw [← hs₁def]; exact hcon
    exact hw₂off h5.2
  have hw₂d : dist w₂ v < ρ₀ := by
    have h5 : dist xi w₂ + dist w₂ wb = dist xi wb := hw₂seg
    have hd1 : dist xi w₂ ≤ dist xi wb := by
      linarith [dist_nonneg (x := w₂) (y := wb)]
    have hd2 : dist xi wb ≤ dist xi v + dist v wb := dist_triangle _ _ _
    have hd3 : dist w₂ v ≤ dist w₂ xi + dist xi v := dist_triangle _ _ _
    have h6 : dist xi v < ρ₀ / 4 := hxid
    have h7 : dist v wb = ρ₀ / 4 := by rw [dist_comm]; exact hwb_dist
    have h8 : dist w₂ xi = dist xi w₂ := dist_comm _ _
    linarith
  have hw₂un : w₂ ∈ ⋃₀ polygonSides Γ τ₀ := by
    rw [← frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
    exact hw₂fr
  obtain ⟨s₂, hs₂mem, hw₂s₂⟩ := hw₂un
  have hvs₂ : v ∈ s₂ := hsep s₂ hs₂mem w₂ hw₂s₂ hw₂d
  have hs₁₂ : s₁ ≠ s₂ := fun h => hw₂s₁ (h ▸ hw₂s₂)
  have hend₂ : IsSegEndpoint s₂ v :=
    isSegEndpoint_of_vertex hΓ hfree hε hgap hdense ⟨hvD, hv3⟩ hs₂mem hvs₂
  refine ⟨s₁, ⟨γ₁, hγ₁elem, hs₁def⟩, s₂, hs₂mem, hs₁₂, hend₁, hend₂, ?_⟩
  intro s hs hsend
  by_contra hcon
  push Not at hcon
  obtain ⟨hne₁, hne₂⟩ := hcon
  obtain ⟨γs, hγselem, hsdef⟩ := hs
  obtain ⟨γ₂', hγ₂elem, hs₂def⟩ := hs₂mem
  refine not_three_sides hγ₁elem hγ₂elem hγselem
    (v := v) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hs₁def]; exact hvs₁
  · rw [← hs₂def]; exact hvs₂
  · rw [← hsdef]; exact hsend.1
  · rw [← hs₁def, ← hs₂def]; exact hs₁₂
  · rw [← hs₁def, ← hsdef]; exact Ne.symm hne₁
  · rw [← hs₂def, ← hsdef]; exact Ne.symm hne₂

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-- Contact sets are equivariant: `δ` touches `z` exactly when `g δ` touches `g • z`, since
the group acts by isometries and permutes the orbit of the basepoint. -/
theorem contact_shift (g δ : ↥Γ) (z : UpperHalfPlane) :
    δ ∈ contactSet Γ τ₀ z ↔ (g * δ) ∈ contactSet Γ τ₀ (g • z) := by
  rw [mem_contactSet_iff_mem_smul_dirichletDomain,
    mem_contactSet_iff_mem_smul_dirichletDomain]
  constructor
  · rintro ⟨u, hu, huz⟩
    refine ⟨u, hu, ?_⟩
    change (g * δ) • u = g • z
    rw [mul_smul]
    exact congrArg (g • ·) huz
  · rintro ⟨u, hu, huz⟩
    refine ⟨u, hu, ?_⟩
    have h1 : g • δ • u = g • z := by
      rw [← mul_smul]
      exact huz
    exact smul_left_cancel g h1

/-- When every element with a fixed point acts trivially, two elements agreeing on the
basepoint have the same inverse action everywhere: they differ by a stabilizer element,
which is then the identity map. -/
theorem inv_smul_eq_of_basepoint_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ γ' : ↥Γ} (h : γ • τ₀ = γ' • τ₀) (w : UpperHalfPlane) : γ⁻¹ • w = γ'⁻¹ • w := by
  have h1 : γ • γ'⁻¹ • w = γ' • γ'⁻¹ • w := smul_eq_of_basepoint_eq hfree h (γ'⁻¹ • w)
  rw [smul_inv_smul] at h1
  conv_lhs => rw [← h1]
  rw [inv_smul_smul]

/-- Under the same hypothesis the transition element `γ⁻¹ δ` moves the basepoint in a way
depending only on where `γ` and `δ` send it — so transitions are well defined on tiles
rather than on group elements. -/
theorem transition_basepoint_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ γ' δ δ' : ↥Γ} (hγ : γ • τ₀ = γ' • τ₀) (hδ : δ • τ₀ = δ' • τ₀) :
    (γ⁻¹ * δ) • τ₀ = (γ'⁻¹ * δ') • τ₀ := by
  rw [mul_smul, mul_smul, hδ]
  exact inv_smul_eq_of_basepoint_eq hfree hγ (δ' • τ₀)

/-- Being a side element depends only on where the element sends the basepoint, so it is a
property of the tile rather than of the group element. -/
theorem isSideElement_congr {β β' : ↥Γ} (h : β • τ₀ = β' • τ₀) :
    IsSideElement Γ τ₀ β ↔ IsSideElement Γ τ₀ β' := by
  unfold IsSideElement
  rw [h, sideSet_eq_of_basepoint_eq h]

/-- A contact element of a vertex never carries the basepoint onto that vertex: if it did, the
vertex would sit on the orbit of the basepoint at distance `0`, so every contact element would
send the basepoint there as well, leaving one tile center where a vertex has at least three. -/
theorem smul_basepoint_ne {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {γ : ↥Γ} (hγ : γ ∈ contactSet Γ τ₀ v) : γ • τ₀ ≠ v := by
  intro h
  have h1 : dist v (γ • τ₀) = Metric.infDist v (MulAction.orbit Γ τ₀) := hγ
  rw [h, dist_self] at h1
  have hsub : tileCenters Γ τ₀ v ⊆ {v} := by
    rintro c ⟨δ, hδ, rfl⟩
    have h3 : dist v (δ • τ₀) = Metric.infDist v (MulAction.orbit Γ τ₀) := hδ
    rw [← h1] at h3
    simp only [Set.mem_singleton_iff]
    exact (dist_eq_zero.mp h3).symm
  have h4 := Set.ncard_le_ncard hsub (Set.finite_singleton v)
  rw [Set.ncard_singleton] at h4
  have h5 : 3 ≤ (tileCenters Γ τ₀ v).ncard := hv.2
  omega

/-- The tile centers transport along the group action: those at `γ⁻¹ • v` are the
`γ⁻¹`-images of those at `v`. -/
theorem tileCenters_smul {v : UpperHalfPlane} (γ : ↥Γ) :
    tileCenters Γ τ₀ (γ⁻¹ • v) = (γ⁻¹ • ·) '' tileCenters Γ τ₀ v := by
  ext c
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    have h1 : (γ * δ) ∈ contactSet Γ τ₀ (γ • γ⁻¹ • v) := (contact_shift γ δ _).mp hδ
    rw [smul_inv_smul] at h1
    refine ⟨(γ * δ) • τ₀, ⟨γ * δ, h1, rfl⟩, ?_⟩
    change γ⁻¹ • (γ * δ) • τ₀ = δ • τ₀
    rw [mul_smul, inv_smul_smul]
  · rintro ⟨c', ⟨δ, hδ, rfl⟩, rfl⟩
    refine ⟨γ⁻¹ * δ, (contact_shift γ⁻¹ δ v).mp hδ, ?_⟩
    change (γ⁻¹ * δ) • τ₀ = γ⁻¹ • δ • τ₀
    rw [mul_smul]

/-- Pulling a vertex back by one of its own contact elements lands on a vertex again: being a
contact element places the vertex in the `γ`-tile, so the pullback lies in the Dirichlet
domain, and the action permutes tile centers bijectively, so the bound of at least three
tiles survives. -/
theorem smul_mem_polygonVertices {v : UpperHalfPlane}
    (hv : v ∈ polygonVertices Γ τ₀) {γ : ↥Γ} (hγ : γ ∈ contactSet Γ τ₀ v) :
    γ⁻¹ • v ∈ polygonVertices Γ τ₀ := by
  obtain ⟨u, huD, huv⟩ := (mem_contactSet_iff_mem_smul_dirichletDomain γ v).mp hγ
  have huv' : γ • u = v := huv
  refine ⟨?_, ?_⟩
  · rw [← huv', inv_smul_smul]
    exact huD
  · rw [tileCenters_smul γ,
      Set.ncard_image_of_injective _ (fun a b h => smul_left_cancel γ⁻¹ h)]
    exact hv.2

/-- **The tiles at a vertex are 2-regular.** Every tile meeting a vertex is adjacent —
across a genuine side — to exactly two others there. This is the local step that makes the
fan of tiles around a vertex a cycle rather than a tree or a longer configuration. -/
theorem two_neighbors (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {rep : UpperHalfPlane → ↥Γ}
    (hrep₁ : ∀ p ∈ tileCenters Γ τ₀ v, rep p ∈ contactSet Γ τ₀ v)
    (hrep₂ : ∀ p ∈ tileCenters Γ τ₀ v, rep p • τ₀ = p)
    {p : UpperHalfPlane} (hp : p ∈ tileCenters Γ τ₀ v) :
    ∃ q₁ ∈ tileCenters Γ τ₀ v, ∃ q₂ ∈ tileCenters Γ τ₀ v, q₁ ≠ q₂ ∧
      ∀ q ∈ tileCenters Γ τ₀ v,
        (IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) ↔ q = q₁ ∨ q = q₂) := by
  have hγC : rep p ∈ contactSet Γ τ₀ v := hrep₁ p hp
  have hvγ : (rep p)⁻¹ • v ∈ polygonVertices Γ τ₀ := smul_mem_polygonVertices hv hγC
  have hvγD : (rep p)⁻¹ • v ∈ dirichletDomain Γ τ₀ := hvγ.1
  obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂, hend₁, hend₂, huniq⟩ :=
    exists_two_sides_at_vertex hΓ hfree hε hgap hdense hvγ
  obtain ⟨β₁, hβ₁elem, hs₁def⟩ := hs₁
  obtain ⟨β₂, hβ₂elem, hs₂def⟩ := hs₂
  have hβ₁v : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β₁ := by
    rw [← hs₁def]; exact hend₁.1
  have hβ₂v : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β₂ := by
    rw [← hs₂def]; exact hend₂.1
  have hmk : ∀ β : ↥Γ, (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β →
      (rep p * β) • τ₀ ∈ tileCenters Γ τ₀ v := by
    intro β hβv
    have hβcon := mem_contactSet_of_mem_sideSet hβv
    have h1 := (contact_shift (rep p) β ((rep p)⁻¹ • v)).mp hβcon
    rw [smul_inv_smul] at h1
    exact ⟨rep p * β, h1, rfl⟩
  have hforw : ∀ β : ↥Γ, IsSideElement Γ τ₀ β →
      ∀ q ∈ tileCenters Γ τ₀ v, IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) →
      dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) = dirichletSideSet Γ τ₀ β →
      q = (rep p * β) • τ₀ := by
    intro β hβelem q hq hSide heq
    have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree hSide hβelem heq
    calc q = rep q • τ₀ := (hrep₂ q hq).symm
      _ = rep p • (((rep p)⁻¹ * rep q) • τ₀) := by rw [mul_smul, smul_inv_smul]
      _ = rep p • (β • τ₀) := by rw [h1]
      _ = (rep p * β) • τ₀ := (mul_smul _ _ _).symm
  have hback : ∀ β : ↥Γ, IsSideElement Γ τ₀ β → (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ β →
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep ((rep p * β) • τ₀)) := by
    intro β hβelem hβv'
    have hqP := hmk β hβv'
    have h2 : rep ((rep p * β) • τ₀) • τ₀ = (rep p * β) • τ₀ := hrep₂ _ hqP
    have h3 := transition_basepoint_eq hfree (rfl : rep p • τ₀ = rep p • τ₀) h2
    rw [inv_mul_cancel_left] at h3
    exact (isSideElement_congr h3).mpr hβelem
  refine ⟨(rep p * β₁) • τ₀, hmk β₁ hβ₁v, (rep p * β₂) • τ₀, hmk β₂ hβ₂v, ?_, ?_⟩
  · intro h
    have h1 : β₁ • τ₀ = β₂ • τ₀ := by
      have h2 : rep p • (β₁ • τ₀) = rep p • (β₂ • τ₀) := by
        rw [← mul_smul, ← mul_smul]
        exact h
      exact smul_left_cancel _ h2
    exact hs₁₂ (by rw [hs₁def, hs₂def, sideSet_eq_of_basepoint_eq h1])
  · intro q hq
    constructor
    · intro hSide
      have hβq := (contact_shift (rep p)⁻¹ (rep q) v).mp (hrep₁ q hq)
      have hvs : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) :=
        mem_sideSet_of_contact hvγD hβq
      have hmemS : dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) ∈ polygonSides Γ τ₀ :=
        ⟨_, hSide, rfl⟩
      have hendS := isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hvγ hmemS hvs
      rcases huniq _ hmemS hendS with h | h
      · exact Or.inl (hforw β₁ hβ₁elem q hq hSide (by rw [h, hs₁def]))
      · exact Or.inr (hforw β₂ hβ₂elem q hq hSide (by rw [h, hs₂def]))
    · rintro (rfl | rfl)
      · exact hback β₁ hβ₁elem hβ₁v
      · exact hback β₂ hβ₂elem hβ₂v

/-- **The tiles at a vertex are connected under adjacency.** A nonempty set of tiles at a
vertex closed under crossing sides is all of them — proved by separating the set from its
complement by two closed unions of tiles, which a small ball around the vertex forbids. -/
theorem adj_closed_eq (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {rep : UpperHalfPlane → ↥Γ}
    (hrep₁ : ∀ p ∈ tileCenters Γ τ₀ v, rep p ∈ contactSet Γ τ₀ v)
    (hrep₂ : ∀ p ∈ tileCenters Γ τ₀ v, rep p • τ₀ = p)
    {S : Set UpperHalfPlane} (hSsub : S ⊆ tileCenters Γ τ₀ v) (hSne : S.Nonempty)
    (hclosed : ∀ p ∈ S, ∀ q ∈ tileCenters Γ τ₀ v,
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) → q ∈ S) :
    S = tileCenters Γ τ₀ v := by
  classical
  by_contra hne
  have hTne : (tileCenters Γ τ₀ v \ S).Nonempty :=
    Set.sdiff_nonempty.mpr (fun h => hne (hSsub.antisymm h))
  obtain ⟨r, hr, hmeets, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ v
  have hPfin : (tileCenters Γ τ₀ v).Finite := (finite_contactSet hΓ τ₀ v).image _
  have hAcl : IsClosed (⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) :=
    Set.Finite.isClosed_biUnion (hPfin.subset hSsub) (fun p _ => isClosed_tile _)
  have hBcl : IsClosed (⋃ p ∈ tileCenters Γ τ₀ v \ S,
      (rep p • ·) '' dirichletDomain Γ τ₀) :=
    Set.Finite.isClosed_biUnion hPfin.sdiff (fun p _ => isClosed_tile _)
  have hcov : Metric.ball v r \ {v} ⊆ (⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∪
      ⋃ p ∈ tileCenters Γ τ₀ v \ S, (rep p • ·) '' dirichletDomain Γ τ₀ := by
    rintro w ⟨hwB, -⟩
    obtain ⟨δ, hδ, hδw⟩ := hcover w hwB
    have hδP : δ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨δ, hδ, rfl⟩
    have htile : (δ • ·) '' dirichletDomain Γ τ₀
        = (rep (δ • τ₀) • ·) '' dirichletDomain Γ τ₀ :=
      smul_image_eq_of_basepoint_eq hfree (hrep₂ _ hδP).symm
    rw [htile] at hδw
    by_cases hmem : δ • τ₀ ∈ S
    · exact Or.inl (Set.mem_biUnion hmem hδw)
    · exact Or.inr (Set.mem_biUnion ⟨hδP, hmem⟩ hδw)
  have hdisj : (⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∩
      (⋃ p ∈ tileCenters Γ τ₀ v \ S, (rep p • ·) '' dirichletDomain Γ τ₀) ⊆ {v} := by
    rintro w ⟨hwA, hwB'⟩
    obtain ⟨p, hpS, hwp⟩ := Set.mem_iUnion₂.mp hwA
    obtain ⟨q, hqT, hwq⟩ := Set.mem_iUnion₂.mp hwB'
    by_contra hwv
    have hpq : p ≠ q := fun h => hqT.2 (h ▸ hpS)
    have hγ := hrep₁ p (hSsub hpS)
    have hδ := hrep₁ q hqT.1
    obtain ⟨u, huD, huw⟩ := hwp
    obtain ⟨u', hu'D, hu'w⟩ := hwq
    have h1 : (rep p)⁻¹ • w ∈ dirichletDomain Γ τ₀ := by
      have h1' : (rep p)⁻¹ • w = u := by rw [← huw]; exact inv_smul_smul _ _
      rw [h1']
      exact huD
    have h2 : (rep p)⁻¹ • w ∈ (((rep p)⁻¹ * rep q) • ·) '' dirichletDomain Γ τ₀ := by
      refine ⟨u', hu'D, ?_⟩
      change ((rep p)⁻¹ * rep q) • u' = (rep p)⁻¹ • w
      rw [mul_smul]
      exact congrArg ((rep p)⁻¹ • ·) hu'w
    have h3 : (rep p)⁻¹ • w ∈ dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) :=
      inter_smul_subset_sideSet _ ⟨h1, h2⟩
    have h4 : (rep p)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((rep p)⁻¹ * rep q) :=
      smul_mem_dirichletSideSet_of_contact_pair hγ hδ
    have h5 : ((rep p)⁻¹ * rep q) • τ₀ ≠ τ₀ := by
      intro h
      apply hpq
      have h6 : rep q • τ₀ = rep p • τ₀ := by
        calc rep q • τ₀ = rep p • (((rep p)⁻¹ * rep q) • τ₀) := by
              rw [mul_smul, smul_inv_smul]
          _ = rep p • τ₀ := by rw [h]
      rw [← hrep₂ p (hSsub hpS), ← hrep₂ q hqT.1, h6]
    have h8 : (rep p)⁻¹ • w ≠ (rep p)⁻¹ • v := by
      intro h
      exact hwv (Set.mem_singleton_iff.mpr (smul_left_cancel _ h))
    have hSide : IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q) :=
      ⟨h5, (rep p)⁻¹ • w, h3, (rep p)⁻¹ • v, h4, h8⟩
    exact hqT.2 (hclosed p hpS q hqT.1 hSide)
  have hAne : ((⋃ p ∈ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∩
      (Metric.ball v r \ {v})).Nonempty := by
    obtain ⟨p, hpS⟩ := hSne
    have hne' : rep p • τ₀ ≠ v := smul_basepoint_ne hv (hrep₁ p (hSsub hpS))
    obtain ⟨w, hwseg, hwv, hwd⟩ := exists_near_on_geodSeg hne' hr
    exact ⟨w, Set.mem_biUnion hpS
        (geodSeg_center_subset_tile (hrep₁ p (hSsub hpS)) hwseg),
      Metric.mem_ball.mpr hwd, fun hc => hwv (Set.mem_singleton_iff.mp hc)⟩
  have hBne : ((⋃ p ∈ tileCenters Γ τ₀ v \ S, (rep p • ·) '' dirichletDomain Γ τ₀) ∩
      (Metric.ball v r \ {v})).Nonempty := by
    obtain ⟨p, hpT⟩ := hTne
    have hne' : rep p • τ₀ ≠ v := smul_basepoint_ne hv (hrep₁ p hpT.1)
    obtain ⟨w, hwseg, hwv, hwd⟩ := exists_near_on_geodSeg hne' hr
    exact ⟨w, Set.mem_biUnion hpT (geodSeg_center_subset_tile (hrep₁ p hpT.1) hwseg),
      Metric.mem_ball.mpr hwd, fun hc => hwv (Set.mem_singleton_iff.mp hc)⟩
  exact punctured_ball_two_closed hr hAcl hBcl hcov hdisj hAne hBne

/-- **A finite connected 2-regular graph is a single cycle.** Purely combinatorial: from a
symmetric irreflexive relation in which every point has exactly two neighbours, and which
admits no proper closed nonempty subset, one extracts a periodic enumeration `e` of period
`n ≥ 3` traversing each point exactly once per period along edges. Applied to the tiles at a
vertex, this turns `two_neighbors` and `adj_closed_eq` into the cyclic fan. -/
theorem cycle_of_two_regular {α : Type*} {P : Set α} {A : α → α → Prop}
    (hfin : P.Finite) (hne : P.Nonempty)
    (hmem : ∀ p q, A p q → p ∈ P ∧ q ∈ P)
    (hsymm : ∀ p q, A p q → A q p)
    (hirr : ∀ p q, A p q → p ≠ q)
    (htwo : ∀ p ∈ P, ∃ q₁ ∈ P, ∃ q₂ ∈ P, q₁ ≠ q₂ ∧
      ∀ q ∈ P, (A p q ↔ q = q₁ ∨ q = q₂))
    (hconn : ∀ S : Set α, S ⊆ P → S.Nonempty →
      (∀ p ∈ S, ∀ q, A p q → q ∈ S) → S = P) :
    ∃ (n : ℕ) (e : ℕ → α), 3 ≤ n ∧ (∀ k, e (k + n) = e k) ∧ (∀ k, e k ∈ P) ∧
      (∀ q ∈ P, ∃! k, k < n ∧ e k = q) ∧ ∀ k, A (e k) (e (k + 1)) := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  have : Nonempty α := ⟨p₀⟩
  choose! nb₁ hnb₁ nb₂ hnb₂ hnb hiff using htwo
  obtain ⟨F, hF⟩ : ∃ F : α → α → α,
      ∀ p q, F p q = if nb₁ q = p then nb₂ q else nb₁ q := ⟨_, fun _ _ => rfl⟩
  have hFmem : ∀ p q, q ∈ P → F p q ∈ P := by
    intro p q hq
    rw [hF]
    split_ifs
    · exact hnb₂ q hq
    · exact hnb₁ q hq
  have hFne : ∀ p q, q ∈ P → F p q ≠ p := by
    intro p q hq
    rw [hF]
    split_ifs with h
    · rw [← h]
      exact (hnb q hq).symm
    · exact h
  have hFadj : ∀ p q, q ∈ P → A q (F p q) := by
    intro p q hq
    rw [hF]
    split_ifs
    · exact (hiff q hq _ (hnb₂ q hq)).mpr (Or.inr rfl)
    · exact (hiff q hq _ (hnb₁ q hq)).mpr (Or.inl rfl)
  have hFuniq : ∀ p q x, q ∈ P → A q p → A q x → x ≠ p → x = F p q := by
    intro p q x hq hp hx hxp
    have h1 := (hiff q hq p (hmem q p hp).2).mp hp
    have h2 := (hiff q hq x (hmem q x hx).2).mp hx
    rw [hF]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h2.trans h1.symm) hxp
    · rw [if_pos h1.symm]
      exact h2
    · have hng : ¬ nb₁ q = p := by
        rw [h1]
        exact hnb q hq
      rw [if_neg hng]
      exact h2
    · exact absurd (h2.trans h1.symm) hxp
  have hFinvol : ∀ p q, q ∈ P → A q p → F (F p q) q = p := by
    intro p q hq hp
    exact (hFuniq (F p q) q p hq (hFadj p q hq) hp (fun h => hFne p q hq h.symm)).symm
  obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → α × α, g 0 = (p₀, nb₁ p₀) ∧
      ∀ k, g (k + 1) = ((g k).2, F (g k).1 (g k).2) :=
    ⟨fun k => Nat.rec (p₀, nb₁ p₀) (fun _ gk => (gk.2, F gk.1 gk.2)) k, rfl, fun _ => rfl⟩
  obtain ⟨pp, hppdef⟩ : ∃ pp : ℕ → α, pp = fun k => (g k).1 := ⟨_, rfl⟩
  have hpp0 : ∀ k, pp k = (g k).1 := fun k => by simp only [hppdef]
  have hpp1 : ∀ k, pp (k + 1) = (g k).2 := by
    intro k
    rw [hpp0 (k + 1), hgs k]
  have hpp2 : ∀ k, pp (k + 2) = F (pp k) (pp (k + 1)) := by
    intro k
    rw [show k + 2 = k + 1 + 1 by omega, hpp1 (k + 1), hgs k, hpp0 k, hpp1 k]
  have hstep : ∀ k, pp k ∈ P ∧ A (pp k) (pp (k + 1)) := by
    intro k
    induction k with
    | zero =>
      constructor
      · rw [hpp0 0, hg0]
        exact hp₀
      · rw [hpp0 0, hpp1 0, hg0]
        exact (hiff p₀ hp₀ _ (hnb₁ p₀ hp₀)).mpr (Or.inl rfl)
    | succ k ih =>
      have hk1P : pp (k + 1) ∈ P := (hmem _ _ ih.2).2
      refine ⟨hk1P, ?_⟩
      rw [hpp2 k]
      exact hFadj (pp k) (pp (k + 1)) hk1P
  have hppP : ∀ k, pp k ∈ P := fun k => (hstep k).1
  have hadj : ∀ k, A (pp k) (pp (k + 1)) := fun k => (hstep k).2
  have hne2 : ∀ k, pp (k + 2) ≠ pp k := by
    intro k
    rw [hpp2 k]
    exact hFne (pp k) (pp (k + 1)) (hppP (k + 1))
  obtain ⟨a, b, hab, hgab⟩ : ∃ a b : ℕ, a < b ∧ g a = g b := by
    refine Set.Finite.exists_lt_map_eq_of_forall_mem (f := g) (t := P ×ˢ P) ?_
      (hfin.prod hfin)
    intro k
    rw [Set.mem_prod]
    exact ⟨hpp0 k ▸ hppP k, hpp1 k ▸ hppP (k + 1)⟩
  have hfwd : ∀ k l, g k = g l → ∀ j, g (k + j) = g (l + j) := by
    intro k l h j
    induction j with
    | zero => exact h
    | succ j ih =>
      rw [← Nat.add_assoc, ← Nat.add_assoc, hgs (k + j), hgs (l + j), ih]
  have hbwd : ∀ k l, g (k + 1) = g (l + 1) → g k = g l := by
    intro k l h
    rw [hgs k, hgs l] at h
    have h2 : (g k).2 = (g l).2 := congrArg Prod.fst h
    have h3 : F (g k).1 (g k).2 = F (g l).1 (g l).2 := congrArg Prod.snd h
    have h4 : A ((g k).2) ((g k).1) := by
      have h4' := hsymm _ _ (hadj k)
      rwa [hpp0 k, hpp1 k] at h4'
    have h5 : A ((g l).2) ((g l).1) := by
      have h5' := hsymm _ _ (hadj l)
      rwa [hpp0 l, hpp1 l] at h5'
    have hkP : (g k).2 ∈ P := by
      rw [← hpp1 k]
      exact hppP (k + 1)
    have hlP : (g l).2 ∈ P := by
      rw [← hpp1 l]
      exact hppP (l + 1)
    have h6 : (g k).1 = (g l).1 := by
      have e1 : F (F (g k).1 (g k).2) ((g k).2) = (g k).1 := hFinvol _ _ hkP h4
      have e2 : F (F (g l).1 (g l).2) ((g l).2) = (g l).1 := hFinvol _ _ hlP h5
      rw [← e1, ← e2, h3, h2]
    exact Prod.ext h6 h2
  have hback : ∀ i k l, g (k + i) = g (l + i) → g k = g l := by
    intro i
    induction i with
    | zero => intro k l h; exact h
    | succ i ih =>
      intro k l h
      refine ih k l (hbwd (k + i) (l + i) ?_)
      have e1 : k + i + 1 = k + (i + 1) := by omega
      have e2 : l + i + 1 = l + (i + 1) := by omega
      rw [e1, e2]
      exact h
  have hex : ∃ m, 0 < m ∧ g m = g 0 := by
    refine ⟨b - a, by omega, hback a (b - a) 0 ?_⟩
    rw [show b - a + a = b by omega, show 0 + a = a by omega]
    exact hgab.symm
  obtain ⟨n, ⟨hnpos, hgn⟩, hnmin⟩ : ∃ n : ℕ, (0 < n ∧ g n = g 0) ∧
      ∀ m : ℕ, 0 < m → g m = g 0 → n ≤ m := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro m hm hgm
    exact Nat.find_le ⟨hm, hgm⟩
  have hper : ∀ k, g (k + n) = g k := by
    intro k
    have h := hfwd n 0 hgn k
    rwa [show n + k = k + n by omega, show 0 + k = k by omega] at h
  have hpper : ∀ k, pp (k + n) = pp k := by
    intro k
    rw [hpp0 (k + n), hpp0 k, hper k]
  have hpermul : ∀ m k, pp (k + m * n) = pp k := by
    intro m
    induction m with
    | zero => intro k; simp
    | succ m ih =>
      intro k
      rw [show k + (m + 1) * n = k + m * n + n by ring, hpper (k + m * n), ih k]
  have hnbrs : ∀ k x, 1 ≤ k → A (pp k) x → x = pp (k - 1) ∨ x = pp (k + 1) := by
    intro k x hk hx
    have hxP := (hmem _ _ hx).2
    have h1 : A (pp k) (pp (k + 1)) := hadj k
    have h2 : A (pp k) (pp (k - 1)) := by
      have h2' := hsymm _ _ (hadj (k - 1))
      rwa [show k - 1 + 1 = k by omega] at h2'
    have h3 : pp (k + 1) ≠ pp (k - 1) := by
      have h4 := hne2 (k - 1)
      rwa [show k - 1 + 2 = k + 1 by omega] at h4
    have e1 := (hiff (pp k) (hppP k) x hxP).mp hx
    have e2 := (hiff (pp k) (hppP k) _ (hppP (k + 1))).mp h1
    have e3 := (hiff (pp k) (hppP k) _ (hppP (k - 1))).mp h2
    rcases e2 with h5 | h5 <;> rcases e3 with h6 | h6
    · exact absurd (h5.trans h6.symm) h3
    · rcases e1 with h7 | h7
      · exact Or.inr (h7.trans h5.symm)
      · exact Or.inl (h7.trans h6.symm)
    · rcases e1 with h7 | h7
      · exact Or.inl (h7.trans h6.symm)
      · exact Or.inr (h7.trans h5.symm)
    · exact absurd (h5.trans h6.symm) h3
  have hppb : ∀ m, pp m = F (pp (m + 2)) (pp (m + 1)) := by
    intro m
    have hp' : A (pp (m + 1)) (pp (m + 2)) := by
      have h := hadj (m + 1)
      rwa [show m + 1 + 1 = m + 2 by omega] at h
    exact hFuniq _ _ _ (hppP (m + 1)) hp' (hsymm _ _ (hadj m)) (hne2 m).symm
  have hrev : ∀ I J, pp I = pp J → pp (I + 1) = pp (J - 1) →
      ∀ k, k + 1 ≤ J → pp (I + k) = pp (J - k) ∧ pp (I + k + 1) = pp (J - k - 1) := by
    intro I J h0 h1 k
    induction k with
    | zero =>
      intro _
      constructor
      · rw [show I + 0 = I by omega, show J - 0 = J by omega]
        exact h0
      · rw [show I + 0 + 1 = I + 1 by omega, show J - 0 - 1 = J - 1 by omega]
        exact h1
    | succ k ih =>
      intro hk
      obtain ⟨ha', hb'⟩ := ih (by omega)
      have hfirst : pp (I + (k + 1)) = pp (J - (k + 1)) := by
        rw [show I + (k + 1) = I + k + 1 by omega, show J - (k + 1) = J - k - 1 by omega]
        exact hb'
      refine ⟨hfirst, ?_⟩
      have hf : pp (I + k + 2) = F (pp (I + k)) (pp (I + k + 1)) := hpp2 (I + k)
      have hbk : pp (J - k - 2) = F (pp (J - k)) (pp (J - k - 1)) := by
        have h2 := hppb (J - k - 2)
        rwa [show J - k - 2 + 2 = J - k by omega,
          show J - k - 2 + 1 = J - k - 1 by omega] at h2
      have hmain : pp (I + k + 2) = pp (J - k - 2) := by
        rw [hf, hbk, ha', hb']
      rwa [show I + k + 2 = I + (k + 1) + 1 by omega,
        show J - k - 2 = J - (k + 1) - 1 by omega] at hmain
  have hlt_false : ∀ i j, i < j → j < n → pp i = pp j → False := by
    intro i j hij hjn he
    have hIJ : pp (i + n) = pp (j + n) := by
      rw [hpper i, hpper j]
      exact he
    have hAn : A (pp (j + n)) (pp (i + n + 1)) := by
      have h := hadj (i + n)
      rwa [hIJ] at h
    rcases hnbrs (j + n) (pp (i + n + 1)) (by omega) hAn with hcase | hcase
    · rcases Nat.even_or_odd (j - i) with ⟨t, ht⟩ | ⟨t, ht⟩
      · obtain ⟨h1, -⟩ := hrev (i + n) (j + n) hIJ hcase (t - 1) (by omega)
        have h2 : pp (i + n + t - 1) = pp (i + n + t - 1 + 2) := by
          rwa [show i + n + (t - 1) = i + n + t - 1 by omega,
            show j + n - (t - 1) = i + n + t - 1 + 2 by omega] at h1
        exact hne2 (i + n + t - 1) h2.symm
      · obtain ⟨h1, -⟩ := hrev (i + n) (j + n) hIJ hcase t (by omega)
        have h2 : pp (i + n + t) = pp (i + n + t + 1) := by
          rwa [show j + n - t = i + n + t + 1 by omega] at h1
        exact hirr _ _ (hadj (i + n + t)) h2
    · have hgIJ : g (i + n) = g (j + n) := by
        refine Prod.ext ?_ ?_
        · rw [← hpp0, ← hpp0]
          exact hIJ
        · rw [← hpp1, ← hpp1]
          exact hcase
      have h0 : g 0 = g (j - i) := by
        refine hback (i + n) 0 (j - i) ?_
        rw [show 0 + (i + n) = i + n by omega, show j - i + (i + n) = j + n by omega]
        exact hgIJ
      have := hnmin (j - i) (by omega) h0.symm
      omega
  have hinj : ∀ i j, i < n → j < n → pp i = pp j → i = j := by
    intro i j hi hj he
    rcases lt_trichotomy i j with h | h | h
    · exact absurd he (fun he' => hlt_false i j h hj he')
    · exact h
    · exact absurd he.symm (fun he' => hlt_false j i h hi he')
  have hrange : Set.range pp = P := by
    refine hconn _ (Set.range_subset_iff.mpr hppP) ⟨pp 0, Set.mem_range_self 0⟩ ?_
    rintro x ⟨k, rfl⟩ q hq
    have hA' : A (pp (k + n)) q := by rwa [hpper k]
    rcases hnbrs (k + n) q (by omega) hA' with h | h
    · exact ⟨k + n - 1, h.symm⟩
    · exact ⟨k + n + 1, h.symm⟩
  have hn1 : n ≠ 1 := by
    intro h
    have h2 := hpper 0
    rw [h] at h2
    exact hirr _ _ (hadj 0) h2.symm
  have hn2 : n ≠ 2 := by
    intro h
    have h2 := hpper 0
    rw [h] at h2
    exact hne2 0 h2
  have hn3 : 3 ≤ n := by omega
  refine ⟨n, pp, hn3, hpper, hppP, ?_, hadj⟩
  intro q hq
  have hq' : q ∈ Set.range pp := by
    rw [hrange]
    exact hq
  obtain ⟨k, hk⟩ := hq'
  have hmod : pp (k % n) = pp k := by
    have h1 := hpermul (k / n) (k % n)
    rw [show k % n + k / n * n = k from Nat.mod_add_div' k n] at h1
    exact h1.symm
  refine ⟨k % n, ⟨Nat.mod_lt k hnpos, hmod.trans hk⟩, ?_⟩
  rintro k' ⟨hk', he⟩
  exact hinj k' (k % n) hk' (Nat.mod_lt k hnpos) (he.trans (hmod.trans hk).symm)

end RiemannDynamics
