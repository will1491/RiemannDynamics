/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.PolygonRank.Homotopy

/-!
# The rank identity `Q + c = m + 1`

The dimension count for the additive characters of a cocompact free Fuchsian group:
`restrictSides` maps characters isomorphically onto the cycle-constrained odd side
functions, whose dimension is `m - c + 1`.

* Sign lemmas (`ratio_im_ne_zero`, …): non-vanishing and sign control of the frame ratio
  at bisector points, feeding the flip-end analysis of side values.
* `exists_sigma_sel` — selection of coherent signs along the side elements.
* `finrank_cycleConstrained_add_classCount` — the dimension of the cycle-constrained
  subspace: `dim + c = m + 1`.
* `finrank_homSubmodule_add_classCount` — the rank identity: the character space of `Γ`
  has dimension `m - c + 1`.
-/

open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

section SignLemmas

variable {p q : UpperHalfPlane} {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ}

/-- The frame-ratio imaginary part at a bisector point in a bisector direction does not
vanish on a strict-side test point. -/
theorem ratio_im_ne_zero (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {u w : UpperHalfPlane} (hu : dist u p = dist u q) (hw : dist w p = dist w q)
    (huw : u ≠ w) {x : UpperHalfPlane} (hx : dist x p < dist x q) :
    (discChart u x / discChart u w).im ≠ 0 := by
  have hgu : (g • u).re = 0 := normalizer_re_eq_zero hε' hle hge hu
  have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
  have hxre : (g • x).re ≠ 0 := by
    have h1 := (normalizer_lt_iff hle hge x).mp hx
    rcases hε' with rfl | rfl
    · rw [one_mul] at h1
      exact h1.ne
    · rw [neg_one_mul, neg_lt_zero] at h1
      exact h1.ne'
  have himA : (discChart (g • u) (g • x)).im ≠ 0 :=
    fun h => hxre (((discChart_im_sign hgu (g • x)).2.1).mp h)
  have hsum : 0 < (g • w).im + (g • u).im := by
    have := (g • w).im_pos
    have := (g • u).im_pos
    linarith
  have hdiff : (g • w).im - (g • u).im ≠ 0 := by
    intro h
    refine huw (smul_left_cancel g ?_)
    refine (UpperHalfPlane.ext (Complex.ext ?_ ?_)).symm
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hgu, hgw]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      linarith
  rw [ratio_im_formula hε' hle hge hu hw x]
  exact mul_ne_zero himA (div_ne_zero hsum.ne' hdiff)

/-- Strict-side test points on opposite sides of a bisector have frame-ratio imaginary
parts of opposite signs, in a common frame at a bisector point. -/
theorem ratio_im_mul_neg_targets (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {u w : UpperHalfPlane} (hu : dist u p = dist u q) (hw : dist w p = dist w q)
    (huw : u ≠ w) {x y : UpperHalfPlane} (hx : dist x p < dist x q)
    (hy : dist y q < dist y p) :
    (discChart u x / discChart u w).im * (discChart u y / discChart u w).im < 0 := by
  have hgu : (g • u).re = 0 := normalizer_re_eq_zero hε' hle hge hu
  have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
  have hx' : ε' * (g • x).re < 0 := (normalizer_lt_iff hle hge x).mp hx
  have hy' : 0 < ε' * (g • y).re := by
    have h1 : 0 ≤ ε' * (g • y).re := (hge y).mp hy.le
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact h2
    · exact absurd ((hle y).mpr h2.symm.le) (not_le.mpr hy)
  have hAB : (discChart (g • u) (g • x)).im * (discChart (g • u) (g • y)).im < 0 := by
    rcases hε' with rfl | rfl
    · rw [one_mul] at hx' hy'
      exact mul_neg_of_pos_of_neg (((discChart_im_sign hgu (g • x)).1).mpr hx')
        (((discChart_im_sign hgu (g • y)).2.2).mpr hy')
    · rw [neg_one_mul, neg_lt_zero] at hx'
      rw [neg_one_mul, lt_neg, neg_zero] at hy'
      exact mul_neg_of_neg_of_pos (((discChart_im_sign hgu (g • x)).2.2).mpr hx')
        (((discChart_im_sign hgu (g • y)).1).mpr hy')
  have hsum : 0 < (g • w).im + (g • u).im := by
    have := (g • w).im_pos
    have := (g • u).im_pos
    linarith
  have hdiff : (g • w).im - (g • u).im ≠ 0 := by
    intro h
    refine huw (smul_left_cancel g ?_)
    refine (UpperHalfPlane.ext (Complex.ext ?_ ?_)).symm
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hgu, hgw]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      linarith
  have hr : ((g • w).im + (g • u).im) / ((g • w).im - (g • u).im) ≠ 0 :=
    div_ne_zero hsum.ne' hdiff
  rw [ratio_im_formula hε' hle hge hu hw x, ratio_im_formula hε' hle hge hu hw y,
    show ∀ A B r : ℝ, A * r * (B * r) = A * B * (r * r) from fun A B r => by ring]
  exact mul_neg_of_neg_of_pos hAB (mul_self_pos.mpr hr)

/-- A strict-side test point has frame-ratio imaginary parts of opposite signs at the two
ends of a bisector segment, each frame directed toward the other end. -/
theorem ratio_im_mul_neg_frames (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {a b : UpperHalfPlane} (ha : dist a p = dist a q) (hb : dist b p = dist b q)
    (hab : a ≠ b) {x : UpperHalfPlane} (hx : dist x p < dist x q) :
    (discChart a x / discChart a b).im * (discChart b x / discChart b a).im < 0 := by
  have hga : (g • a).re = 0 := normalizer_re_eq_zero hε' hle hge ha
  have hgb : (g • b).re = 0 := normalizer_re_eq_zero hε' hle hge hb
  have hxre : (g • x).re ≠ 0 := by
    have h1 := (normalizer_lt_iff hle hge x).mp hx
    rcases hε' with rfl | rfl
    · rw [one_mul] at h1
      exact h1.ne
    · rw [neg_one_mul, neg_lt_zero] at h1
      exact h1.ne'
  have hAB : 0 < (discChart (g • a) (g • x)).im * (discChart (g • b) (g • x)).im := by
    rcases lt_trichotomy ((g • x)).re 0 with h1 | h1 | h1
    · exact mul_pos (((discChart_im_sign hga (g • x)).1).mpr h1)
        (((discChart_im_sign hgb (g • x)).1).mpr h1)
    · exact absurd h1 hxre
    · exact mul_pos_of_neg_of_neg (((discChart_im_sign hga (g • x)).2.2).mpr h1)
        (((discChart_im_sign hgb (g • x)).2.2).mpr h1)
  have hsum : 0 < (g • b).im + (g • a).im := by
    have := (g • b).im_pos
    have := (g • a).im_pos
    linarith
  have hdiff : (g • b).im - (g • a).im ≠ 0 := by
    intro h
    refine hab (smul_left_cancel g ?_)
    refine (UpperHalfPlane.ext (Complex.ext ?_ ?_)).symm
    · rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, hga, hgb]
    · rw [UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
      linarith
  have hr1 : ((g • b).im + (g • a).im) / ((g • b).im - (g • a).im) ≠ 0 :=
    div_ne_zero hsum.ne' hdiff
  have hr2 : ((g • a).im + (g • b).im) / ((g • a).im - (g • b).im)
      = -(((g • b).im + (g • a).im) / ((g • b).im - (g • a).im)) := by
    rw [show (g • a).im - (g • b).im = -((g • b).im - (g • a).im) from by ring, div_neg,
      add_comm]
  rw [ratio_im_formula hε' hle hge ha hb x, ratio_im_formula hε' hle hge hb ha x,
    hr2, show ∀ A B r : ℝ, A * r * (B * -r) = -(A * B * (r * r)) from fun A B r => by ring]
  rw [neg_lt_zero]
  exact mul_pos hAB (mul_self_pos.mpr hr1)

end SignLemmas

/-- The basepoint direction at a point of a side is transverse to the side direction. -/
theorem side_chi_ne_zero {γ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ)
    {u w : UpperHalfPlane} (hu : u ∈ dirichletSideSet Γ τ₀ γ)
    (hw : w ∈ dirichletSideSet Γ τ₀ γ) (hwu : w ≠ u) :
    (discChart u τ₀ / discChart u w).im ≠ 0 := by
  have hpq : τ₀ ≠ γ • τ₀ := Ne.symm hγ.1
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hpq
  have hx : dist τ₀ τ₀ < dist τ₀ (γ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq
  exact ratio_im_ne_zero hε' hle hge hu.2 hw.2 (Ne.symm hwu) hx

/-- Crossing a side toward its paired side reverses the transverse sign of the basepoint
direction. -/
theorem side_chi_flip_pair {γ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ)
    {u w : UpperHalfPlane} (hu : u ∈ dirichletSideSet Γ τ₀ γ)
    (hw : w ∈ dirichletSideSet Γ τ₀ γ) (hwu : w ≠ u) :
    (discChart u τ₀ / discChart u w).im
      * (discChart (γ⁻¹ • u) τ₀ / discChart (γ⁻¹ • u) (γ⁻¹ • w)).im < 0 := by
  have hpq : τ₀ ≠ γ • τ₀ := Ne.symm hγ.1
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hpq
  have hcoe : ∀ (δ : ↥Γ) (z : UpperHalfPlane),
      δ • z = (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z := fun _ _ => rfl
  have hsecond : (discChart (γ⁻¹ • u) τ₀ / discChart (γ⁻¹ • u) (γ⁻¹ • w)).im
      = (discChart u (γ • τ₀) / discChart u w).im := by
    have key := discChart_ratio_smul ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ u w
      ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ₀)
    rw [inv_smul_smul] at key
    change (discChart (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ • u) τ₀
        / discChart (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ • u)
          (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ • w)).im = _
    rw [key]
    rfl
  rw [hsecond]
  have hx : dist τ₀ τ₀ < dist τ₀ (γ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq
  have hy : dist (γ • τ₀) (γ • τ₀) < dist (γ • τ₀) τ₀ := by
    rw [dist_self]
    exact dist_pos.mpr (Ne.symm hpq)
  exact ratio_im_mul_neg_targets hε' hle hge hu.2 hw.2 (Ne.symm hwu) hx hy

/-- At the two endpoints of one side, the basepoint direction has opposite transverse
signs. -/
theorem side_chi_flip_ends {γ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ)
    {a b : UpperHalfPlane} (ha : a ∈ dirichletSideSet Γ τ₀ γ)
    (hb : b ∈ dirichletSideSet Γ τ₀ γ) (hab : a ≠ b) :
    (discChart a τ₀ / discChart a b).im * (discChart b τ₀ / discChart b a).im < 0 := by
  have hpq : τ₀ ≠ γ • τ₀ := Ne.symm hγ.1
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hpq
  have hx : dist τ₀ τ₀ < dist τ₀ (γ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq
  exact ratio_im_mul_neg_frames hε' hle hge ha.2 hb.2 hab hx

/-- At a vertex, the basepoint direction has opposite transverse signs against the two
sides through the vertex. -/
theorem vertex_chi_flip (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {s₁ s₂ : Set UpperHalfPlane} (hs₁ : s₁ ∈ polygonSides Γ τ₀)
    (hs₂ : s₂ ∈ polygonSides Γ τ₀) (hne : s₁ ≠ s₂)
    (he₁ : IsSegEndpoint s₁ v) (he₂ : IsSegEndpoint s₂ v)
    {w₁ w₂ : UpperHalfPlane} (hw₁ : w₁ ∈ s₁) (hw₂ : w₂ ∈ s₂)
    (hw₁v : w₁ ≠ v) (hw₂v : w₂ ≠ v) :
    (discChart v τ₀ / discChart v w₁).im * (discChart v τ₀ / discChart v w₂).im < 0 := by
  have hvτ : τ₀ ≠ v := by
    intro h
    exact basepoint_notMem_side hΓ hfree hε hgap hdense hs₁ (h ▸ he₁.1)
  have ht0 : discChart v τ₀ ≠ 0 := discChart_ne_zero hvτ
  obtain ⟨γ₁, hγ₁, hs₁def⟩ := id hs₁
  obtain ⟨γ₂, hγ₂, hs₂def⟩ := id hs₂
  have hAim : (discChart v τ₀ / discChart v w₁).im ≠ 0 :=
    side_chi_ne_zero hγ₁ (hs₁def ▸ he₁.1) (hs₁def ▸ hw₁) hw₁v
  have hinvim : (discChart v τ₀ / discChart v w₂).im ≠ 0 :=
    side_chi_ne_zero hγ₂ (hs₂def ▸ he₂.1) (hs₂def ▸ hw₂) hw₂v
  have hBinv : discChart v τ₀ / discChart v w₂ = (discChart v w₂ / discChart v τ₀)⁻¹ :=
    (inv_div _ _).symm
  have hBim : (discChart v w₂ / discChart v τ₀).im ≠ 0 := by
    intro h
    rw [hBinv, Complex.inv_im, h] at hinvim
    simp at hinvim
  have hB0 : discChart v w₂ / discChart v τ₀ ≠ 0 := by
    intro h
    rw [h] at hBim
    simp at hBim
  have hA0 : discChart v τ₀ / discChart v w₁ ≠ 0 := by
    intro h
    rw [h] at hAim
    simp at hAim
  have hprod : discChart v τ₀ / discChart v w₁ * (discChart v w₂ / discChart v τ₀)
      = discChart v w₂ / discChart v w₁ := by
    rw [div_mul_div_comm, mul_comm (discChart v w₁) (discChart v τ₀),
      mul_div_mul_left _ _ ht0]
  have hadd := sectorAngle_eq_add_basepoint hΓ hfree hε hgap hdense hv hs₁ hs₂ hne he₁ he₂
    hw₁ hw₂ hw₁v hw₂v
  have hadd' : |Complex.arg (discChart v τ₀ / discChart v w₁
      * (discChart v w₂ / discChart v τ₀))|
      = |Complex.arg (discChart v τ₀ / discChart v w₁)|
        + |Complex.arg (discChart v w₂ / discChart v τ₀)| := by
    rw [hprod]
    exact hadd
  have hsign := same_sign_of_abs_arg_add hA0 hB0 hadd' hAim hBim
  rw [hBinv, Complex.inv_im]
  have hns : 0 < Complex.normSq (discChart v w₂ / discChart v τ₀) :=
    Complex.normSq_pos.mpr hB0
  rw [show (discChart v τ₀ / discChart v w₁).im
      * (-(discChart v w₂ / discChart v τ₀).im
        / Complex.normSq (discChart v w₂ / discChart v τ₀))
      = -((discChart v τ₀ / discChart v w₁).im * (discChart v w₂ / discChart v τ₀).im
        / Complex.normSq (discChart v w₂ / discChart v τ₀)) from by ring]
  exact neg_lt_zero.mpr (div_pos hsign hns)

/-- The paired side is the inverse translate of the side. -/
theorem sideSet_inv_image (γ : ↥Γ) :
    dirichletSideSet Γ τ₀ γ⁻¹ = (γ⁻¹ • ·) '' dirichletSideSet Γ τ₀ γ := by
  ext z
  constructor
  · intro hz
    have h1 := smul_mem_dirichletSideSet_inv (γ := γ⁻¹) hz
    rw [inv_inv] at h1
    exact ⟨γ • z, h1, inv_smul_smul γ z⟩
  · rintro ⟨w, hw, rfl⟩
    exact smul_mem_dirichletSideSet_inv hw

/-- Endpoints of a set transport along the isometric action. -/
theorem isSegEndpoint_smul (γ : ↥Γ) {s : Set UpperHalfPlane} {v : UpperHalfPlane}
    (h : IsSegEndpoint s v) : IsSegEndpoint ((γ • ·) '' s) (γ • v) := by
  obtain ⟨hvs, hext⟩ := h
  refine ⟨⟨v, hvs, rfl⟩, ?_⟩
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩ hmem
  have hcoe : ∀ z : UpperHalfPlane, γ • z = (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z :=
    fun _ => rfl
  have hseg : γ • v ∈ ((γ • ·) '' geodSeg x' y') := by
    have himg := smul_geodSeg (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) x' y'
    have : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·) '' geodSeg x' y'
        = geodSeg (γ • x') (γ • y') := himg
    rw [show ((γ • ·) '' geodSeg x' y') = ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ·)
      '' geodSeg x' y' from rfl, this]
    exact hmem
  obtain ⟨w, hw, hweq⟩ := hseg
  have hvw : v = w := smul_left_cancel γ hweq.symm
  have hvseg : v ∈ geodSeg x' y' := by
    rw [hvw]
    exact hw
  rcases hext x' hx' y' hy' hvseg with h1 | h1
  · exact Or.inl (by change γ • v = γ • x'; rw [h1])
  · exact Or.inr (by change γ • v = γ • y'; rw [h1])

/-- Membership characterization of the endpoints of a nondegenerate side. -/
theorem endpoint_pair {s : Set UpperHalfPlane} {a b : UpperHalfPlane} (hab : a ≠ b)
    (hseq : s = geodSeg a b) (v : UpperHalfPlane) :
    IsSegEndpoint s v ↔ v = a ∨ v = b := by
  rw [hseq, isSegEndpoint_geodSeg_iff hab]

/-- Extraction of the other member of an unordered pair presented two ways. -/
theorem other_of_pair {a b u X : UpperHalfPlane} (_hab : a ≠ b)
    (h : ∀ v : UpperHalfPlane, (v = a ∨ v = b) ↔ (v = u ∨ v = X)) (hXu : X ≠ u)
    [Decidable (u = a)] :
    (if u = a then b else a) = X := by
  by_cases hua : u = a
  · rw [if_pos hua]
    rcases (h X).mpr (Or.inr rfl) with h1 | h1
    · exact absurd (h1.trans hua.symm) hXu
    · exact h1.symm
  · rw [if_neg hua]
    rcases (h u).mpr (Or.inl rfl) with h1 | h1
    · exact absurd h1 hua
    · rcases (h X).mpr (Or.inr rfl) with h2 | h2
      · exact h2.symm
      · exact absurd (h2.trans h1.symm) hXu

/-- Interchange of a filtered incidence double sum. -/
theorem sum_incidence_swap {X Y : Type*} (A : Finset X) (B : Finset Y)
    (P : X → Y → Prop) [∀ x y, Decidable (P x y)] (F : X → Y → ℝ) :
    ∑ x ∈ A, ∑ y ∈ B.filter (fun y => P x y), F x y
      = ∑ y ∈ B, ∑ x ∈ A.filter (fun x => P x y), F x y := by
  simp_rw [Finset.sum_filter]
  exact Finset.sum_comm

/-- A cyclic shift leaves the window sum of a sequence with equal window ends unchanged. -/
theorem sum_shift (f : ℕ → ℝ) (n : ℕ) (hf : f n = f 0) :
    ∑ k ∈ Finset.range n, f (k + 1) = ∑ k ∈ Finset.range n, f k := by
  have h4 := Finset.sum_range_succ' f n
  have h5 := Finset.sum_range_succ f n
  rw [h4, hf] at h5
  linarith

/-- Sign algebra: a unit factor with product `-1` determines the other factor. -/
theorem sign_neg_of_mul {x y : ℝ} (hx : x = 1 ∨ x = -1) (hxy : x * y = -1) :
    y = -x := by
  rcases hx with rfl | rfl <;> linarith

open Classical in
/-- The full-cycle crossing sum at a class vertex, written as a signed dart sum over the
class vertices: the loop contributes each vertex of the class once, through its two sides,
with the transverse signs aligned by one global unit `ς`. -/
theorem class_identity (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ' : UpperHalfPlane, Metric.infDist σ' (MulAction.orbit Γ τ₀) ≤ R)
    {v₀ : UpperHalfPlane} (hv₀ : v₀ ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v₀)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v₀, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {σ : UpperHalfPlane → Set UpperHalfPlane → ℝ}
    (hσpm : ∀ u s, σ u s = 1 ∨ σ u s = -1)
    (hσvert : ∀ v ∈ polygonVertices Γ τ₀, ∀ s₁ ∈ polygonSides Γ τ₀,
      ∀ s₂ ∈ polygonSides Γ τ₀, s₁ ≠ s₂ → IsSegEndpoint s₁ v → IsSegEndpoint s₂ v →
      σ v s₁ * σ v s₂ = -1)
    (hσtrans : ∀ γ : ↥Γ, IsSideElement Γ τ₀ γ → ∀ u : UpperHalfPlane,
      IsSegEndpoint (dirichletSideSet Γ τ₀ γ) u →
      σ u (dirichletSideSet Γ τ₀ γ) * σ (γ⁻¹ • u) (dirichletSideSet Γ τ₀ γ⁻¹) = -1)
    {sel : Set UpperHalfPlane → ↥Γ}
    (hsel : ∀ s ∈ polygonSides Γ τ₀, IsSideElement Γ τ₀ (sel s) ∧
      s = dirichletSideSet Γ τ₀ (sel s))
    (hVfin : (MulAction.orbit Γ v₀ ∩ polygonVertices Γ τ₀).Finite)
    (hSfin : (polygonSides Γ τ₀).Finite) :
    ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧ ∀ α ∈ oddSideFunctions Γ τ₀,
      ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1))
        = ς / 2 * ∑ u ∈ hVfin.toFinset,
            ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u), σ u s * α (sel s) := by
  classical
  set u : ℕ → UpperHalfPlane := fun k => (e k)⁻¹ • v₀ with hudef
  set so : ℕ → Set UpperHalfPlane :=
    fun k => dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) with hsodef
  set si : ℕ → Set UpperHalfPlane :=
    fun k => dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + (n - 1))) with hsidef
  have hFa : ∀ k, u k ∈ polygonVertices Γ τ₀ :=
    fun k => smul_mem_polygonVertices hv₀ (hcon k)
  have hSoMem : ∀ k, so k ∈ polygonSides Γ τ₀ := fun k => ⟨_, hadj k, rfl⟩
  have hSiElt : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + (n - 1))) := by
    intro k
    have h1 := (hadj (k + (n - 1))).inv
    rw [mul_inv_rev, inv_inv, show k + (n - 1) + 1 = k + n from by omega, hper k] at h1
    exact h1
  have hSiMem : ∀ k, si k ∈ polygonSides Γ τ₀ := fun k => ⟨_, hSiElt k, rfl⟩
  have hUo : ∀ k, u k ∈ so k :=
    fun k => smul_mem_dirichletSideSet_of_contact_pair (hcon k) (hcon (k + 1))
  have hUi : ∀ k, u k ∈ si k :=
    fun k => smul_mem_dirichletSideSet_of_contact_pair (hcon k) (hcon (k + (n - 1)))
  have hEo : ∀ k, IsSegEndpoint (so k) (u k) :=
    fun k => isSegEndpoint_of_vertex hΓ hfree hε hgap hdense (hFa k) (hSoMem k) (hUo k)
  have hEi : ∀ k, IsSegEndpoint (si k) (u k) :=
    fun k => isSegEndpoint_of_vertex hΓ hfree hε hgap hdense (hFa k) (hSiMem k) (hUi k)
  have hNe : ∀ k, so k ≠ si k := by
    intro k h
    have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree (hadj k) (hSiElt k) h
    rw [mul_smul, mul_smul] at h1
    have h2 : e (k + 1) • τ₀ = e (k + (n - 1)) • τ₀ := smul_left_cancel _ h1
    have h3 := position_mod_eq hn3 hper hcon huniq h2
    have h4 : n ∣ k + (n - 1) - (k + 1) := (Nat.modEq_iff_dvd' (by omega)).mp h3
    rw [show k + (n - 1) - (k + 1) = n - 2 from by omega] at h4
    have h5 := Nat.le_of_dvd (by omega) h4
    omega
  have hSiNext : ∀ k, si (k + 1) = dirichletSideSet Γ τ₀ (((e k)⁻¹ * e (k + 1))⁻¹) := by
    intro k
    change dirichletSideSet Γ τ₀ ((e (k + 1))⁻¹ * e (k + 1 + (n - 1))) = _
    rw [show k + 1 + (n - 1) = k + n from by omega, hper k, mul_inv_rev, inv_inv]
  have hUNext : ∀ k, ((e k)⁻¹ * e (k + 1))⁻¹ • u k = u (k + 1) := by
    intro k
    change ((e k)⁻¹ * e (k + 1))⁻¹ • ((e k)⁻¹ • v₀) = (e (k + 1))⁻¹ • v₀
    rw [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
  have hsign : ∀ k, σ (u k) (so k) = σ (u 0) (so 0) ∧
      σ (u k) (si k) = -σ (u 0) (so 0) := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, ?_⟩
      have h1 := hσvert (u 0) (hFa 0) (so 0) (hSoMem 0) (si 0) (hSiMem 0) (hNe 0)
        (hEo 0) (hEi 0)
      exact sign_neg_of_mul (hσpm (u 0) (so 0)) h1
    | succ k ih =>
      have h1 := hσtrans ((e k)⁻¹ * e (k + 1)) (hadj k) (u k) (hEo k)
      rw [hUNext k, ← hSiNext k] at h1
      have h2 : σ (u (k + 1)) (si (k + 1)) = -σ (u k) (so k) :=
        sign_neg_of_mul (hσpm (u k) (so k)) h1
      have h4 : σ (u (k + 1)) (so (k + 1)) = -σ (u (k + 1)) (si (k + 1)) := by
        have h5 := hσvert (u (k + 1)) (hFa (k + 1)) (si (k + 1)) (hSiMem (k + 1))
          (so (k + 1)) (hSoMem (k + 1)) (Ne.symm (hNe (k + 1))) (hEi (k + 1)) (hEo (k + 1))
        exact sign_neg_of_mul (hσpm (u (k + 1)) (si (k + 1))) h5
      rw [h2, ih.1] at h4
      exact ⟨by rw [h4, neg_neg], by rw [h2, ih.1]⟩
  refine ⟨σ (u 0) (so 0), hσpm _ _, ?_⟩
  intro α hα
  obtain ⟨-, hodd, hfib⟩ := hα
  have hAout : ∀ k, α (sel (so k)) = α ((e k)⁻¹ * e (k + 1)) := by
    intro k
    have h1 := hsel (so k) (hSoMem k)
    exact hfib _ _ (smul_basepoint_eq_of_sideSet_eq hΓ hfree h1.1 (hadj k) h1.2.symm)
  have hAin : ∀ k, α (sel (si k)) = α ((e k)⁻¹ * e (k + (n - 1))) := by
    intro k
    have h1 := hsel (si k) (hSiMem k)
    exact hfib _ _ (smul_basepoint_eq_of_sideSet_eq hΓ hfree h1.1 (hSiElt k) h1.2.symm)
  have hstepG : ∀ k, α ((e (k + 1))⁻¹ * e (k + 1 + (n - 1))) = α (((e k)⁻¹ * e (k + 1))⁻¹) := by
    intro k
    rw [show k + 1 + (n - 1) = k + n from by omega, hper k, mul_inv_rev, inv_inv]
  have hG0 : α ((e n)⁻¹ * e (n + (n - 1))) = α ((e 0)⁻¹ * e (0 + (n - 1))) := by
    have he1 : e n = e 0 := by
      have h1 := hper 0
      rwa [Nat.zero_add] at h1
    have he2 : e (n + (n - 1)) = e (0 + (n - 1)) := by
      have h1 := hper (n - 1)
      rw [show n + (n - 1) = n - 1 + n from by omega, h1, Nat.zero_add]
    rw [he1, he2]
  have hGshift : ∑ k ∈ Finset.range n, α (((e k)⁻¹ * e (k + 1))⁻¹)
      = ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + (n - 1))) := by
    calc ∑ k ∈ Finset.range n, α (((e k)⁻¹ * e (k + 1))⁻¹)
        = ∑ k ∈ Finset.range n, α ((e (k + 1))⁻¹ * e (k + 1 + (n - 1))) :=
          Finset.sum_congr rfl fun k _ => (hstepG k).symm
      _ = ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + (n - 1))) :=
          sum_shift (fun k => α ((e k)⁻¹ * e (k + (n - 1)))) n hG0
  have hoddsum : ∑ k ∈ Finset.range n, α (((e k)⁻¹ * e (k + 1))⁻¹)
      = -∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hodd _
  have hperk : ∀ k, α ((e k)⁻¹ * e (k + 1)) - α ((e k)⁻¹ * e (k + (n - 1)))
      = σ (u 0) (so 0) * (σ (u k) (so k) * α (sel (so k))
        + σ (u k) (si k) * α (sel (si k))) := by
    intro k
    rw [hAout k, hAin k, (hsign k).1, (hsign k).2]
    rcases hσpm (u 0) (so 0) with h | h <;> rw [h] <;> ring
  have hfilter : ∀ k, hSfin.toFinset.filter (fun s => IsSegEndpoint s (u k))
      = ({so k, si k} : Finset (Set UpperHalfPlane)) := by
    intro k
    ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hsS, hsE⟩
      obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂, he₁, he₂, huniq2⟩ :=
        exists_two_sides_at_vertex hΓ hfree hε hgap hdense (hFa k)
      rcases huniq2 (so k) (hSoMem k) (hEo k) with h1 | h1 <;>
        rcases huniq2 (si k) (hSiMem k) (hEi k) with h2 | h2 <;>
        rcases huniq2 s hsS hsE with h3 | h3
      · exact absurd (h1.trans h2.symm) (hNe k)
      · exact absurd (h1.trans h2.symm) (hNe k)
      · exact Or.inl (h3.trans h1.symm)
      · exact Or.inr (h3.trans h2.symm)
      · exact Or.inr (h3.trans h2.symm)
      · exact Or.inl (h3.trans h1.symm)
      · exact absurd (h1.trans h2.symm) (hNe k)
      · exact absurd (h1.trans h2.symm) (hNe k)
    · rintro (rfl | rfl)
      · exact ⟨hSoMem k, hEo k⟩
      · exact ⟨hSiMem k, hEi k⟩
  have hbij : ∑ k ∈ Finset.range n, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s (u k)), σ (u k) s * α (sel s)
      = ∑ w ∈ hVfin.toFinset, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s w), σ w s * α (sel s) := by
    refine Finset.sum_bij (fun k _ => u k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Set.Finite.mem_toFinset]
      exact ⟨MulAction.mem_orbit_iff.mpr ⟨(e k)⁻¹, rfl⟩, hFa k⟩
    · intro k hk j hj huv
      rw [Finset.mem_range] at hk hj
      have h1 : (e j * (e k)⁻¹) • v₀ = v₀ := by
        rw [mul_smul, show (e k)⁻¹ • v₀ = (e j)⁻¹ • v₀ from huv, smul_inv_smul]
      have h2 := hfree (e j * (e k)⁻¹) ⟨v₀, h1⟩ (e k • τ₀)
      rw [mul_smul, inv_smul_smul] at h2
      have h3 := position_mod_eq hn3 hper hcon huniq h2
      rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] at h3
      exact h3.symm
    · intro w hw
      rw [Set.Finite.mem_toFinset] at hw
      obtain ⟨horb, hvert⟩ := hw
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horb
      have hcon' : g⁻¹ ∈ contactSet Γ τ₀ v₀ := by
        rw [mem_contactSet_iff_mem_smul_dirichletDomain]
        refine ⟨w, hvert.1, ?_⟩
        change g⁻¹ • w = v₀
        rw [← hg, inv_smul_smul]
      obtain ⟨k, ⟨hkn, hkτ⟩, -⟩ := huniq g⁻¹ hcon'
      refine ⟨k, Finset.mem_range.mpr hkn, ?_⟩
      have h4 := inv_smul_eq_of_basepoint_eq hfree hkτ v₀
      rw [inv_inv] at h4
      exact h4.symm.trans hg
    · intro k hk
      rfl
  have hpairs : ∑ k ∈ Finset.range n, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s (u k)), σ (u k) s * α (sel s)
      = ∑ k ∈ Finset.range n, (σ (u k) (so k) * α (sel (so k))
        + σ (u k) (si k) * α (sel (si k))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfilter k]
    exact Finset.sum_pair (hNe k)
  have hmain : 2 * ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1))
      = σ (u 0) (so 0) * ∑ w ∈ hVfin.toFinset, ∑ s ∈ hSfin.toFinset.filter
        (fun s => IsSegEndpoint s w), σ w s * α (sel s) := by
    calc 2 * ∑ k ∈ Finset.range n, α ((e k)⁻¹ * e (k + 1))
        = ∑ k ∈ Finset.range n,
            (α ((e k)⁻¹ * e (k + 1)) - α ((e k)⁻¹ * e (k + (n - 1)))) := by
          rw [Finset.sum_sub_distrib, ← hGshift, hoddsum]
          ring
      _ = ∑ k ∈ Finset.range n, σ (u 0) (so 0) * (σ (u k) (so k) * α (sel (so k))
            + σ (u k) (si k) * α (sel (si k))) :=
          Finset.sum_congr rfl fun k _ => hperk k
      _ = σ (u 0) (so 0) * ∑ k ∈ Finset.range n, (σ (u k) (so k) * α (sel (so k))
            + σ (u k) (si k) * α (sel (si k))) := by
          rw [Finset.mul_sum]
      _ = σ (u 0) (so 0) * ∑ w ∈ hVfin.toFinset, ∑ s ∈ hSfin.toFinset.filter
            (fun s => IsSegEndpoint s w), σ w s * α (sel s) := by
          rw [← hpairs, hbij]
  linear_combination hmain / 2

/-- Unit signs of two reals with negative product multiply to `-1`. -/
theorem ite_sign_mul {x y : ℝ} (h : x * y < 0) [Decidable (0 < x)]
    [Decidable (0 < y)] :
    (if 0 < x then (1 : ℝ) else -1) * (if 0 < y then (1 : ℝ) else -1) = -1 := by
  by_cases h1 : 0 < x <;> by_cases h2 : 0 < y
  · exact absurd h (by nlinarith)
  · simp [h1, h2]
  · simp [h1, h2]
  · exfalso
    push Not at h1 h2
    nlinarith

/-- Two presentations of an unordered pair give the same membership predicate. -/
theorem pair_perm {p1 p2 a b : UpperHalfPlane} (hab : a ≠ b)
    (ha : a = p1 ∨ a = p2) (hb : b = p1 ∨ b = p2) (v : UpperHalfPlane) :
    (v = p1 ∨ v = p2) ↔ (v = a ∨ v = b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact Iff.rfl
  · exact or_comm
  · exact absurd rfl hab

open Classical in
/-- A transverse-sign function on vertex-side darts, together with side-element and
endpoint selections: the sign flips across each vertex, along each side, and under the
side pairing. -/
theorem exists_sigma_sel (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ' : UpperHalfPlane, Metric.infDist σ' (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ (σ : UpperHalfPlane → Set UpperHalfPlane → ℝ) (sel : Set UpperHalfPlane → ↥Γ)
      (ep1 ep2 : Set UpperHalfPlane → UpperHalfPlane),
      (∀ u s, σ u s = 1 ∨ σ u s = -1) ∧
      (∀ s ∈ polygonSides Γ τ₀, IsSideElement Γ τ₀ (sel s) ∧
        s = dirichletSideSet Γ τ₀ (sel s)) ∧
      (∀ s ∈ polygonSides Γ τ₀, ep1 s ≠ ep2 s ∧ s = geodSeg (ep1 s) (ep2 s)) ∧
      (∀ v ∈ polygonVertices Γ τ₀, ∀ s₁ ∈ polygonSides Γ τ₀, ∀ s₂ ∈ polygonSides Γ τ₀,
        s₁ ≠ s₂ → IsSegEndpoint s₁ v → IsSegEndpoint s₂ v → σ v s₁ * σ v s₂ = -1) ∧
      (∀ s ∈ polygonSides Γ τ₀, ∀ a b : UpperHalfPlane, IsSegEndpoint s a →
        IsSegEndpoint s b → a ≠ b → σ a s * σ b s = -1) ∧
      (∀ γ : ↥Γ, IsSideElement Γ τ₀ γ → ∀ u : UpperHalfPlane,
        IsSegEndpoint (dirichletSideSet Γ τ₀ γ) u →
        σ u (dirichletSideSet Γ τ₀ γ) * σ (γ⁻¹ • u) (dirichletSideSet Γ τ₀ γ⁻¹) = -1) := by
  classical
  have hselex : ∀ s ∈ polygonSides Γ τ₀, ∃ γ : ↥Γ, IsSideElement Γ τ₀ γ ∧
      s = dirichletSideSet Γ τ₀ γ := fun s hs => hs
  choose! sel hsel1 hsel2 using hselex
  choose! ep1 ep2 hepne hepeq using
    (fun s (hs : s ∈ polygonSides Γ τ₀) =>
      exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs)
  obtain ⟨oe, hoedef⟩ : ∃ oe : UpperHalfPlane → Set UpperHalfPlane → UpperHalfPlane,
      oe = fun u s => if u = ep1 s then ep2 s else ep1 s := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : UpperHalfPlane → Set UpperHalfPlane → ℝ,
      σ = fun u s =>
        if 0 < (discChart u τ₀ / discChart u (oe u s)).im then 1 else -1 := ⟨_, rfl⟩
  have hoeval : ∀ u s, oe u s = if u = ep1 s then ep2 s else ep1 s :=
    fun u s => by rw [hoedef]
  have hσval : ∀ u s,
      σ u s = if 0 < (discChart u τ₀ / discChart u (oe u s)).im then 1 else -1 :=
    fun u s => by rw [hσdef]
  have hσpm : ∀ u s, σ u s = 1 ∨ σ u s = -1 := by
    intro u s
    rw [hσval]
    by_cases h : 0 < (discChart u τ₀ / discChart u (oe u s)).im
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  have hoe : ∀ s ∈ polygonSides Γ τ₀, ∀ u : UpperHalfPlane, IsSegEndpoint s u →
      oe u s ∈ s ∧ oe u s ≠ u ∧ IsSegEndpoint s (oe u s) ∧ s = geodSeg u (oe u s) := by
    intro s hs u hu
    have hiff := endpoint_pair (hepne s hs) (hepeq s hs)
    have hmem1 : ep1 s ∈ s := by
      have h := left_mem_geodSeg (ep1 s) (ep2 s)
      rwa [← hepeq s hs] at h
    have hmem2 : ep2 s ∈ s := by
      have h := right_mem_geodSeg (ep1 s) (ep2 s)
      rwa [← hepeq s hs] at h
    rcases (hiff u).mp hu with h1 | h1
    · have hval : oe u s = ep2 s := by rw [hoeval, if_pos h1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hval]
        exact hmem2
      · rw [hval, h1]
        exact Ne.symm (hepne s hs)
      · rw [hval]
        exact (hiff _).mpr (Or.inr rfl)
      · rw [hval, h1]
        exact hepeq s hs
    · have hne1 : u ≠ ep1 s := by
        rw [h1]
        exact Ne.symm (hepne s hs)
      have hval : oe u s = ep1 s := by rw [hoeval, if_neg hne1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hval]
        exact hmem1
      · rw [hval]
        exact fun h => hne1 h.symm
      · rw [hval]
        exact (hiff _).mpr (Or.inl rfl)
      · rw [hval, h1]
        exact (hepeq s hs).trans (geodSeg_comm _ _)
  refine ⟨σ, sel, ep1, ep2, hσpm, fun s hs => ⟨hsel1 s hs, hsel2 s hs⟩,
    fun s hs => ⟨hepne s hs, hepeq s hs⟩, ?_, ?_, ?_⟩
  · intro v hv s₁ hs₁ s₂ hs₂ hne he₁ he₂
    obtain ⟨hw₁s, hw₁v, -, -⟩ := hoe s₁ hs₁ v he₁
    obtain ⟨hw₂s, hw₂v, -, -⟩ := hoe s₂ hs₂ v he₂
    have hflip := vertex_chi_flip hΓ hfree hε hgap hdense hv hs₁ hs₂ hne he₁ he₂
      hw₁s hw₂s hw₁v hw₂v
    rw [hσval, hσval]
    exact ite_sign_mul hflip
  · intro s hs a b ha hb hab
    have ha' := (endpoint_pair (hepne s hs) (hepeq s hs) a).mp ha
    have hb' := (endpoint_pair (hepne s hs) (hepeq s hs) b).mp hb
    have hoea : oe a s = b := by
      rw [hoeval]
      exact other_of_pair (hepne s hs) (pair_perm hab ha' hb') (Ne.symm hab)
    have hoeb : oe b s = a := by
      rw [hoeval]
      exact other_of_pair (hepne s hs) (pair_perm (Ne.symm hab) hb' ha') hab
    have haS : a ∈ dirichletSideSet Γ τ₀ (sel s) := by
      rw [← hsel2 s hs]
      exact ha.1
    have hbS : b ∈ dirichletSideSet Γ τ₀ (sel s) := by
      rw [← hsel2 s hs]
      exact hb.1
    have hflip := side_chi_flip_ends (hsel1 s hs) haS hbS hab
    rw [hσval, hσval, hoea, hoeb]
    exact ite_sign_mul hflip
  · intro γ hγ u hu
    have hsγ : dirichletSideSet Γ τ₀ γ ∈ polygonSides Γ τ₀ := ⟨γ, hγ, rfl⟩
    have hsγ' : dirichletSideSet Γ τ₀ γ⁻¹ ∈ polygonSides Γ τ₀ := ⟨γ⁻¹, hγ.inv, rfl⟩
    obtain ⟨hwmem, hwne, hwend, hseq⟩ := hoe _ hsγ u hu
    have himg : dirichletSideSet Γ τ₀ γ⁻¹ = (γ⁻¹ • ·) '' dirichletSideSet Γ τ₀ γ :=
      sideSet_inv_image γ
    have hu' : IsSegEndpoint (dirichletSideSet Γ τ₀ γ⁻¹) (γ⁻¹ • u) := by
      rw [himg]
      exact isSegEndpoint_smul γ⁻¹ hu
    have hw' : IsSegEndpoint (dirichletSideSet Γ τ₀ γ⁻¹)
        (γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ)) := by
      rw [himg]
      exact isSegEndpoint_smul γ⁻¹ hwend
    have hne' : γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ) ≠ γ⁻¹ • u :=
      fun h => hwne (smul_left_cancel γ⁻¹ h)
    have hseq' : dirichletSideSet Γ τ₀ γ⁻¹
        = geodSeg (γ⁻¹ • u) (γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ)) := by
      refine himg.trans ((congrArg (fun t => (γ⁻¹ • ·) '' t) hseq).trans ?_)
      exact smul_geodSeg ((γ⁻¹ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) u
        (oe u (dirichletSideSet Γ τ₀ γ))
    have hoeu' : oe (γ⁻¹ • u) (dirichletSideSet Γ τ₀ γ⁻¹)
        = γ⁻¹ • oe u (dirichletSideSet Γ τ₀ γ) := by
      rw [hoeval]
      refine other_of_pair (hepne _ hsγ') ?_ hne'
      intro v
      refine (endpoint_pair (hepne _ hsγ') (hepeq _ hsγ') v).symm.trans ?_
      constructor
      · intro hv
        rw [hseq'] at hv
        exact (isSegEndpoint_geodSeg_iff (Ne.symm hne')).mp hv
      · rintro (rfl | rfl)
        · exact hu'
        · exact hw'
    have hflip := side_chi_flip_pair hγ hu.1 hwmem hwne
    rw [hσval, hσval, hoeu']
    exact ite_sign_mul hflip

open Classical in
/-- The vertex-class constraint functionals of the polygon: one crossing-sum functional per
vertex class, cutting out exactly the cycle-constrained side functions, with unit weights
whose weighted constraint sum vanishes identically and spans all linear dependencies. -/
theorem exists_constraint_data (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ' : UpperHalfPlane, Metric.infDist σ' (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ (Φ : Set UpperHalfPlane → ((↥Γ) → ℝ) → ℝ) (εs : Set UpperHalfPlane → ℝ),
      (∀ C ∈ polygonVertexClasses Γ τ₀, εs C = 1 ∨ εs C = -1) ∧
      (∀ C ∈ polygonVertexClasses Γ τ₀, ∀ α β : (↥Γ) → ℝ,
        Φ C (α + β) = Φ C α + Φ C β) ∧
      (∀ C ∈ polygonVertexClasses Γ τ₀, ∀ (c : ℝ) (α : (↥Γ) → ℝ),
        Φ C (c • α) = c * Φ C α) ∧
      (∀ α ∈ cycleConstrained Γ τ₀, ∀ C ∈ polygonVertexClasses Γ τ₀, Φ C α = 0) ∧
      (∀ α ∈ oddSideFunctions Γ τ₀,
        (∀ C ∈ polygonVertexClasses Γ τ₀, Φ C α = 0) → α ∈ cycleConstrained Γ τ₀) ∧
      (∀ α ∈ oddSideFunctions Γ τ₀,
        ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, εs C * Φ C α = 0) ∧
      (∀ m : Set UpperHalfPlane → ℝ,
        (∀ α ∈ oddSideFunctions Γ τ₀,
          ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, m C * Φ C α = 0) →
        ∀ C ∈ polygonVertexClasses Γ τ₀, ∀ C' ∈ polygonVertexClasses Γ τ₀,
          m C * εs C = m C' * εs C') := by
  classical
  obtain ⟨σ, sel, ep1, ep2, hσpm, hselp, hepp, hσvert, hσside, hσtrans⟩ :=
    exists_sigma_sel hΓ hfree hε hgap hdense
  have hSfin := finite_polygonSides hΓ hfree hε hgap hdense
  have hVfin := finite_polygonVertices hΓ hfree hε hgap hdense
  have hclassrep : ∀ C ∈ polygonVertexClasses Γ τ₀, ∃ v₀ : UpperHalfPlane,
      v₀ ∈ polygonVertices Γ τ₀ ∧ C = MulAction.orbit Γ v₀ ∩ polygonVertices Γ τ₀ :=
    fun C hC => hC
  choose! vC hvC1 hvC2 using hclassrep
  have hcycex : ∀ C ∈ polygonVertexClasses Γ τ₀, ∃ p : ℕ × (ℕ → ↥Γ),
      3 ≤ p.1 ∧ (∀ k, p.2 (k + p.1) = p.2 k) ∧
      (∀ k, p.2 k ∈ contactSet Γ τ₀ (vC C)) ∧
      (∀ γ ∈ contactSet Γ τ₀ (vC C), ∃! k, k < p.1 ∧ γ • τ₀ = p.2 k • τ₀) ∧
      ∀ k, IsSideElement Γ τ₀ ((p.2 k)⁻¹ * p.2 (k + 1)) := by
    intro C hC
    obtain ⟨n, e, h1, h2, h3, h4, h5⟩ :=
      exists_vertex_cycle hΓ hfree hε hgap hdense (hvC1 C hC)
    exact ⟨(n, e), h1, h2, h3, h4, h5⟩
  choose! cyc hcyc1 hcyc2 hcyc3 hcyc4 hcyc5 using hcycex
  have hCfin : ∀ C : Set UpperHalfPlane,
      (MulAction.orbit Γ (vC C) ∩ polygonVertices Γ τ₀).Finite :=
    fun C => hVfin.subset Set.inter_subset_right
  have hkey : ∀ C ∈ polygonVertexClasses Γ τ₀, ∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧
      ∀ α ∈ oddSideFunctions Γ τ₀,
      ∑ k ∈ Finset.range (cyc C).1, α (((cyc C).2 k)⁻¹ * (cyc C).2 (k + 1))
        = ς / 2 * ∑ u ∈ (hCfin C).toFinset,
            ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u),
              σ u s * α (sel s) :=
    fun C hC => class_identity hΓ hfree hε hgap hdense (hvC1 C hC) (hcyc1 C hC)
      (hcyc2 C hC) (hcyc3 C hC) (hcyc4 C hC) (hcyc5 C hC) hσpm hσvert hσtrans
      (fun s hs => hselp s hs) (hCfin C) hSfin
  choose! ςf hς1 hς2 using hkey
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Set UpperHalfPlane → ((↥Γ) → ℝ) → ℝ,
      Φ = fun C α =>
        ∑ k ∈ Finset.range (cyc C).1, α (((cyc C).2 k)⁻¹ * (cyc C).2 (k + 1)) := ⟨_, rfl⟩
  have hΦval : ∀ C α, Φ C α
      = ∑ k ∈ Finset.range (cyc C).1, α (((cyc C).2 k)⁻¹ * (cyc C).2 (k + 1)) :=
    fun C α => by rw [hΦdef]
  have hclassfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine (hVfin.image (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have hfconv : ∀ f : Set UpperHalfPlane → ℝ,
      ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, f C = ∑ C ∈ hclassfin.toFinset, f C := by
    intro f
    exact finsum_mem_eq_finite_toFinset_sum f hclassfin
  have hepfilter : ∀ s ∈ polygonSides Γ τ₀,
      hVfin.toFinset.filter (fun u => IsSegEndpoint s u)
        = ({ep1 s, ep2 s} : Finset UpperHalfPlane) ∧
      IsSegEndpoint s (ep1 s) ∧ IsSegEndpoint s (ep2 s) := by
    intro s hs
    have he1 : IsSegEndpoint s (ep1 s) :=
      (endpoint_pair (hepp s hs).1 (hepp s hs).2 _).mpr (Or.inl rfl)
    have he2 : IsSegEndpoint s (ep2 s) :=
      (endpoint_pair (hepp s hs).1 (hepp s hs).2 _).mpr (Or.inr rfl)
    refine ⟨?_, he1, he2⟩
    ext u
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, hu⟩
      exact (endpoint_pair (hepp s hs).1 (hepp s hs).2 u).mp hu
    · rintro (rfl | rfl)
      · exact ⟨mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs he1, he1⟩
      · exact ⟨mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs he2, he2⟩
  have hweighted : ∀ w : Set UpperHalfPlane → ℝ, ∀ α ∈ oddSideFunctions Γ τ₀,
      ∑ C ∈ hclassfin.toFinset, w C * Φ C α
        = ∑ s ∈ hSfin.toFinset, ∑ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s u),
            w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ u s * α (sel s)) := by
    intro w α hα
    have h1 : ∀ C ∈ hclassfin.toFinset, w C * Φ C α
        = ∑ u ∈ (hCfin C).toFinset, w C * ςf C / 2
            * ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u),
                σ u s * α (sel s) := by
      intro C hC'
      rw [Set.Finite.mem_toFinset] at hC'
      rw [hΦval, hς2 C hC' α hα, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl h1]
    have h2 : ∀ C ∈ hclassfin.toFinset, ∑ u ∈ (hCfin C).toFinset, w C * ςf C / 2
        * ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u), σ u s * α (sel s)
        = ∑ u ∈ (hCfin C).toFinset,
            w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * ∑ s ∈ hSfin.toFinset.filter (fun s => IsSegEndpoint s u),
                  σ u s * α (sel s) := by
      intro C hC'
      rw [Set.Finite.mem_toFinset] at hC'
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Set.Finite.mem_toFinset] at hu
      have h3 : MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ = C := by
        rw [hvC2 C hC']
        congr 1
        exact MulAction.orbit_eq_iff.mpr hu.1
      rw [h3]
    rw [Finset.sum_congr rfl h2]
    have hdisj : (↑hclassfin.toFinset : Set (Set UpperHalfPlane)).PairwiseDisjoint
        (fun C => (hCfin C).toFinset) := by
      intro C hCm C' hC'm hne
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hCm hC'm
      refine Finset.disjoint_left.mpr fun u hu1 hu2 => ?_
      rw [Set.Finite.mem_toFinset] at hu1 hu2
      refine hne ?_
      rw [hvC2 C hCm, hvC2 C' hC'm]
      congr 1
      rw [← MulAction.orbit_eq_iff.mpr hu1.1, ← MulAction.orbit_eq_iff.mpr hu2.1]
    have hbiun : hclassfin.toFinset.biUnion (fun C => (hCfin C).toFinset)
        = hVfin.toFinset := by
      ext u
      simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨C, hC', hu⟩
        exact hu.2
      · intro hu
        refine ⟨MulAction.orbit Γ u ∩ polygonVertices Γ τ₀, ⟨u, hu, rfl⟩, ?_, hu⟩
        have h1' := hvC2 _ (⟨u, hu, rfl⟩ :
          MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ ∈ polygonVertexClasses Γ τ₀)
        have h2' : u ∈ MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ :=
          ⟨MulAction.mem_orbit_self u, hu⟩
        rw [h1'] at h2'
        exact h2'.1
    rw [← Finset.sum_biUnion hdisj, hbiun]
    rw [Finset.sum_congr rfl fun u (_ : u ∈ hVfin.toFinset) => Finset.mul_sum
      (hSfin.toFinset.filter (fun s => IsSegEndpoint s u))
      (fun s => σ u s * α (sel s))
      (w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
        * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2)]
    exact sum_incidence_swap hVfin.toFinset hSfin.toFinset
      (fun u s => IsSegEndpoint s u)
      (fun u s => w (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
        * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2 * (σ u s * α (sel s)))
  refine ⟨Φ, ςf, hς1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC α β
    rw [hΦval, hΦval, hΦval]
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  · intro C hC c α
    rw [hΦval, hΦval]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm
  · intro α hα C hC
    have hloop : IsVertexLoop Γ τ₀ (vC C) (loopList (cyc C).2 0 (cyc C).1) := by
      refine ⟨isTilePath_loopList _ (hcyc5 C hC) _ _, ?_, ?_⟩
      · intro γ hγ
        obtain ⟨i, hi, rfl⟩ := loopList_mem _ _ _ _ hγ
        exact hcyc3 C hC (0 + i)
      · rw [loopList_head?, loopList_getLast?, hcyc2 C hC 0]
    have hcs := (mem_cycleConstrained.mp hα).2 (vC C) (hvC1 C hC) _ hloop
    rw [crossingSum_loopList] at hcs
    rw [hΦval]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hcs
    rw [Nat.zero_add]
  · intro α hα hzeros
    refine ⟨hα, ?_⟩
    intro v hv p hp
    have hC : MulAction.orbit Γ v ∩ polygonVertices Γ τ₀ ∈ polygonVertexClasses Γ τ₀ :=
      ⟨v, hv, rfl⟩
    have hvorb : v ∈ MulAction.orbit Γ (vC (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)) := by
      have h1 := hvC2 _ hC
      have h2 : v ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀ :=
        ⟨MulAction.mem_orbit_self v, hv⟩
      rw [h1] at h2
      exact h2.1
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hvorb
    obtain ⟨e', he'⟩ : ∃ e' : ℕ → ↥Γ,
        e' = fun k => g * (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 k := ⟨_, rfl⟩
    have he'val : ∀ k, e' k
        = g * (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 k :=
      fun k => by rw [he']
    have htrans' : ∀ k, (e' k)⁻¹ * e' (k + 1)
        = ((cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 k)⁻¹
          * (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).2 (k + 1) := by
      intro k
      rw [he'val, he'val, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    have hper' : ∀ k, e' (k + (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).1) = e' k := by
      intro k
      rw [he'val, he'val, hcyc2 _ hC k]
    have hcon' : ∀ k, e' k ∈ contactSet Γ τ₀ v := by
      intro k
      rw [he'val]
      have h1 := (contact_shift g _ _).mp (hcyc3 _ hC k)
      rwa [hg] at h1
    have huniq' : ∀ γ ∈ contactSet Γ τ₀ v,
        ∃! k, k < (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).1
          ∧ γ • τ₀ = e' k • τ₀ := by
      intro γ hγ
      have hγ' : g⁻¹ * γ
          ∈ contactSet Γ τ₀ (vC (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)) := by
        refine (contact_shift g (g⁻¹ * γ) _).mpr ?_
        rw [mul_inv_cancel_left, hg]
        exact hγ
      obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hcyc4 _ hC (g⁻¹ * γ) hγ'
      refine ⟨k, ⟨hk1, ?_⟩, ?_⟩
      · rw [he'val, mul_smul, ← hk2, mul_smul, smul_inv_smul]
      · rintro k' ⟨hk'1, hk'2⟩
        refine hk3 k' ⟨hk'1, ?_⟩
        rw [he'val] at hk'2
        rw [mul_smul, hk'2, mul_smul, inv_smul_smul]
    have hadj' : ∀ k, IsSideElement Γ τ₀ ((e' k)⁻¹ * e' (k + 1)) := by
      intro k
      rw [htrans' k]
      exact hcyc5 _ hC k
    have hzero' : ∑ i ∈ Finset.range
        (cyc (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).1,
        α ((e' i)⁻¹ * e' (i + 1)) = 0 := by
      refine Eq.trans (Finset.sum_congr rfl fun k _ => by rw [htrans' k]) ?_
      have h1 := hzeros _ hC
      rw [hΦval] at h1
      exact h1
    exact closed_loop_sum hΓ hfree hε hgap hdense hv (hcyc1 _ hC) hper' hcon'
      huniq' hadj' hα.2.1 hα.2.2 hzero' hp
  · intro α hα
    rw [hfconv, hweighted ςf α hα]
    refine Finset.sum_eq_zero fun s hs' => ?_
    rw [Set.Finite.mem_toFinset] at hs'
    obtain ⟨hfeq, he1, he2⟩ := hepfilter s hs'
    rw [hfeq, Finset.sum_pair (hepp s hs').1]
    have hc1 : MulAction.orbit Γ (ep1 s) ∩ polygonVertices Γ τ₀
        ∈ polygonVertexClasses Γ τ₀ :=
      ⟨ep1 s, mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs' he1, rfl⟩
    have hc2 : MulAction.orbit Γ (ep2 s) ∩ polygonVertices Γ τ₀
        ∈ polygonVertexClasses Γ τ₀ :=
      ⟨ep2 s, mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs' he2, rfl⟩
    have hσs : σ (ep2 s) s = -σ (ep1 s) s :=
      sign_neg_of_mul (hσpm (ep1 s) s) (hσside s hs' _ _ he1 he2 (hepp s hs').1)
    rw [hσs]
    rcases hς1 _ hc1 with h | h <;> rcases hς1 _ hc2 with h' | h' <;> rw [h, h'] <;> ring
  · intro m hm C hC C' hC'
    have hsideRel : ∀ s ∈ polygonSides Γ τ₀, ∀ a b : UpperHalfPlane, IsSegEndpoint s a →
        IsSegEndpoint s b →
        m (MulAction.orbit Γ a ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ a ∩ polygonVertices Γ τ₀)
        = m (MulAction.orbit Γ b ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ b ∩ polygonVertices Γ τ₀) := by
      intro s hs a b ha hb
      have hβ := (hselp s hs).1
      have hsβ := (hselp s hs).2
      have hs' : dirichletSideSet Γ τ₀ (sel s)⁻¹ ∈ polygonSides Γ τ₀ :=
        ⟨(sel s)⁻¹, hβ.inv, rfl⟩
      have hnss' : s ≠ dirichletSideSet Γ τ₀ (sel s)⁻¹ := by
        intro h
        exact sideElement_smul_ne_inv hfree hβ
          (smul_basepoint_eq_of_sideSet_eq hΓ hfree hβ hβ.inv (hsβ.symm.trans h))
      obtain ⟨αP, hαPV, hαP1, hαP2, hαP3⟩ := exists_indicator hfree hβ
      have h0 := hm αP hαPV
      rw [hfconv, hweighted m αP hαPV] at h0
      have hval_other : ∀ s'' ∈ polygonSides Γ τ₀, s'' ≠ s →
          s'' ≠ dirichletSideSet Γ τ₀ (sel s)⁻¹ → αP (sel s'') = 0 := by
        intro s'' hs'' hne1 hne2
        refine hαP3 _ (fun h => hne1 ?_) (fun h => hne2 ?_)
        · rw [(hselp s'' hs'').2, hsβ]
          exact sideSet_eq_of_basepoint_eq h
        · rw [(hselp s'' hs'').2]
          exact sideSet_eq_of_basepoint_eq h
      have hsub : ({s, dirichletSideSet Γ τ₀ (sel s)⁻¹} : Finset (Set UpperHalfPlane))
          ⊆ hSfin.toFinset := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Set.Finite.mem_toFinset]
        rcases hx with rfl | rfl
        · exact hs
        · exact hs'
      have hcollapse : ∑ s'' ∈ hSfin.toFinset, ∑ u ∈ hVfin.toFinset.filter
            (fun u => IsSegEndpoint s'' u),
            m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ u s'' * αP (sel s''))
          = ∑ s'' ∈ ({s, dirichletSideSet Γ τ₀ (sel s)⁻¹} : Finset (Set UpperHalfPlane)),
              ∑ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s'' u),
                m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
                  * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
                  * (σ u s'' * αP (sel s'')) := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx hxmem
        rw [Set.Finite.mem_toFinset] at hx
        have hx1 : x ≠ s := fun h => hxmem (by rw [h]; exact Finset.mem_insert_self _ _)
        have hx2 : x ≠ dirichletSideSet Γ τ₀ (sel s)⁻¹ := fun h => hxmem (by
          rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [hval_other x hx hx1 hx2, mul_zero, mul_zero]
      rw [hcollapse, Finset.sum_pair hnss'] at h0
      have hσflip : ∀ u : UpperHalfPlane, IsSegEndpoint s u →
          σ ((sel s)⁻¹ • u) (dirichletSideSet Γ τ₀ (sel s)⁻¹) = -σ u s := by
        intro u hu
        have h1 : IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)) u := by
          rw [← hsβ]
          exact hu
        have h2 := hσtrans (sel s) hβ u h1
        rw [← hsβ] at h2
        exact sign_neg_of_mul (hσpm u s) h2
      have hocinv : ∀ u : UpperHalfPlane,
          MulAction.orbit Γ ((sel s)⁻¹ • u) ∩ polygonVertices Γ τ₀
            = MulAction.orbit Γ u ∩ polygonVertices Γ τ₀ := by
        intro u
        congr 1
        exact MulAction.orbit_eq_iff.mpr (MulAction.mem_orbit u (sel s)⁻¹)
      have hendp' : ∀ u : UpperHalfPlane, IsSegEndpoint s u →
          IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)⁻¹) ((sel s)⁻¹ • u) := by
        intro u hu
        rw [sideSet_inv_image (sel s)]
        refine isSegEndpoint_smul _ ?_
        rw [← hsβ]
        exact hu
      have hendp'' : ∀ u' : UpperHalfPlane,
          IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)⁻¹) u' →
          IsSegEndpoint s ((sel s) • u') := by
        intro u' hu'
        have h1 := sideSet_inv_image (τ₀ := τ₀) (sel s)⁻¹
        rw [inv_inv] at h1
        have h2 : IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)) ((sel s) • u') := by
          rw [h1]
          exact isSegEndpoint_smul _ hu'
        rw [← hsβ] at h2
        exact h2
      have hbij2 : ∑ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s u),
            m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ ((sel s)⁻¹ • u) (dirichletSideSet Γ τ₀ (sel s)⁻¹)
                * αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹)))
          = ∑ u' ∈ hVfin.toFinset.filter
              (fun u => IsSegEndpoint (dirichletSideSet Γ τ₀ (sel s)⁻¹) u),
              m (MulAction.orbit Γ u' ∩ polygonVertices Γ τ₀)
                * ςf (MulAction.orbit Γ u' ∩ polygonVertices Γ τ₀) / 2
                * (σ u' (dirichletSideSet Γ τ₀ (sel s)⁻¹)
                  * αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹))) := by
        refine Finset.sum_bij (fun u _ => (sel s)⁻¹ • u) ?_ ?_ ?_ ?_
        · intro u hu
          rw [Finset.mem_filter] at hu ⊢
          refine ⟨?_, hendp' u hu.2⟩
          rw [Set.Finite.mem_toFinset]
          exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs'
            (hendp' u hu.2)
        · intro u hu u₂ hu₂ h
          exact smul_left_cancel _ h
        · intro u' hu'
          rw [Finset.mem_filter] at hu'
          refine ⟨(sel s) • u', ?_, inv_smul_smul _ _⟩
          rw [Finset.mem_filter]
          refine ⟨?_, hendp'' u' hu'.2⟩
          rw [Set.Finite.mem_toFinset]
          exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs
            (hendp'' u' hu'.2)
        · intro u hu
          rw [← hocinv u]
      rw [← hbij2, ← Finset.sum_add_distrib] at h0
      have hv2 : αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹)) = -1 :=
        hαP2 _ (smul_basepoint_eq_of_sideSet_eq hΓ hfree (hselp _ hs').1 hβ.inv
          (hselp _ hs').2.symm)
      have hsimpl : ∀ u ∈ hVfin.toFinset.filter (fun u => IsSegEndpoint s u),
          m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ u s * αP (sel s))
            + m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) / 2
              * (σ ((sel s)⁻¹ • u) (dirichletSideSet Γ τ₀ (sel s)⁻¹)
                * αP (sel (dirichletSideSet Γ τ₀ (sel s)⁻¹)))
          = m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
              * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀) * σ u s := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [hαP1 _ rfl, hv2, hσflip u hu.2]
        ring
      rw [Finset.sum_congr rfl hsimpl] at h0
      obtain ⟨hfeq, he1, he2⟩ := hepfilter s hs
      rw [hfeq, Finset.sum_pair (hepp s hs).1] at h0
      have hσ21 : σ (ep2 s) s = -σ (ep1 s) s :=
        sign_neg_of_mul (hσpm (ep1 s) s) (hσside s hs _ _ he1 he2 (hepp s hs).1)
      rw [hσ21] at h0
      have hkey2 : m (MulAction.orbit Γ (ep1 s) ∩ polygonVertices Γ τ₀)
            * ςf (MulAction.orbit Γ (ep1 s) ∩ polygonVertices Γ τ₀)
          = m (MulAction.orbit Γ (ep2 s) ∩ polygonVertices Γ τ₀)
            * ςf (MulAction.orbit Γ (ep2 s) ∩ polygonVertices Γ τ₀) := by
        rcases hσpm (ep1 s) s with h | h <;> rw [h] at h0 <;> linarith
      have ha' := (endpoint_pair (hepp s hs).1 (hepp s hs).2 a).mp ha
      have hb' := (endpoint_pair (hepp s hs).1 (hepp s hs).2 b).mp hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · rfl
      · exact hkey2
      · exact hkey2.symm
      · rfl
    obtain ⟨N, es, hN0, hesper, hesmem, hesuniq, hesshare⟩ :=
      exists_boundary_side_cycle hΓ hfree hε hgap hdense
    obtain ⟨r0, hr0v, hr0e, -⟩ := hesshare 0
    have hchain : ∀ k, ∀ u : UpperHalfPlane, IsSegEndpoint (es k) u →
        m (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ u ∩ polygonVertices Γ τ₀)
        = m (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀) := by
      intro k
      induction k with
      | zero =>
        intro u hu
        exact hsideRel (es 0) (hesmem 0) u r0 hu hr0e
      | succ k ih =>
        intro u hu
        obtain ⟨w, hwv, hwk, hwk1⟩ := hesshare k
        exact (hsideRel (es (k + 1)) (hesmem (k + 1)) u w hu hwk1).trans (ih w hwk)
    have hval : ∀ D ∈ polygonVertexClasses Γ τ₀, m D * ςf D
        = m (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀)
          * ςf (MulAction.orbit Γ r0 ∩ polygonVertices Γ τ₀) := by
      intro D hD
      obtain ⟨s₁, hs₁, s₂, hs₂, -, he₁, -, -⟩ :=
        exists_two_sides_at_vertex hΓ hfree hε hgap hdense (hvC1 D hD)
      obtain ⟨k, ⟨hkN, hks⟩, -⟩ := hesuniq s₁ hs₁
      have h1 : IsSegEndpoint (es k) (vC D) := by
        rw [hks]
        exact he₁
      have h2 := hchain k (vC D) h1
      rw [← hvC2 D hD] at h2
      exact h2
    rw [hval C hC, hval C' hC']

/-- A proper subspace of a finite-dimensional space is annihilated by a nonzero
functional. -/
theorem exists_ann_functional {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {U : Submodule ℝ W} (hU : U ≠ ⊤) :
    ∃ h : W →ₗ[ℝ] ℝ, h ≠ 0 ∧ ∀ u ∈ U, h u = 0 := by
  have : Nontrivial (W ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hU
  obtain ⟨q₀, hq₀⟩ := exists_ne (0 : W ⧸ U)
  set b := Module.finBasis ℝ (W ⧸ U) with hbdef
  have hrep : b.repr q₀ ≠ 0 := fun h => hq₀ (by
    have h2 := b.repr.map_eq_zero_iff.mp h
    exact h2)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrep
  refine ⟨(b.coord i).comp U.mkQ, ?_, ?_⟩
  · intro h
    obtain ⟨w, hw⟩ := U.mkQ_surjective q₀
    have h3 := congrFun (congrArg DFunLike.coe h) w
    rw [LinearMap.comp_apply, hw] at h3
    rw [Module.Basis.coord_apply] at h3
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    exact hi h3
  · intro u hu
    rw [LinearMap.comp_apply, show U.mkQ u = 0 from (Submodule.Quotient.mk_eq_zero U).mpr hu,
      map_zero]

/-- **The cycle-constrained side functions form a finite-dimensional space.** For a
Fuchsian group in which every element with a fixed point acts trivially, with a
translation-length gap and an `R`-dense orbit, the polygon has finitely many side pairs;
the odd side functions are then finite-dimensional and these form a subspace of them. -/
theorem finiteDimensional_cycleConstrained (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (cycleConstrained Γ τ₀) := by
  have := finiteDimensional_oddSideFunctions hΓ hfree hε hgap hdense
  exact Submodule.finiteDimensional_of_le (fun α hα => hα.1)

/-- **Dimension of the constrained space**: the vertex-loop constraints impose one linear
condition per vertex class with exactly one linear dependency among them — traversing every
vertex loop counterclockwise, each side pair is crossed once in each direction, so the
signed sum of all class constraints is zero; conversely the class-adjacency graph is
connected through the boundary cycle, so the corank is exactly one. Hence
`dim = m - (c - 1)`, in addition form. -/
theorem finrank_cycleConstrained_add_classCount (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Module.finrank ℝ (cycleConstrained Γ τ₀) + polygonVertexClassCount Γ τ₀
      = polygonSideCount Γ τ₀ + 1 := by
  classical
  have hFD := finiteDimensional_oddSideFunctions hΓ hfree hε hgap hdense
  have hVfin := finite_polygonVertices hΓ hfree hε hgap hdense
  have hclassfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine (hVfin.image (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have := hclassfin.fintype
  obtain ⟨Φ, εs, hεpm, hadd, hsmul, hP1, hP2, hP3, hP5⟩ :=
    exists_constraint_data hΓ hfree hε hgap hdense
  set Ψ : ↥(oddSideFunctions Γ τ₀) →ₗ[ℝ] (↥(polygonVertexClasses Γ τ₀) → ℝ) :=
    { toFun := fun α C => Φ ↑C ↑α
      map_add' := fun α β => funext fun C => hadd ↑C C.2 ↑α ↑β
      map_smul' := fun c α => funext fun C => hsmul ↑C C.2 c ↑α } with hΨdef
  have hΨval : ∀ (α : ↥(oddSideFunctions Γ τ₀)) (C : ↥(polygonVertexClasses Γ τ₀)),
      Ψ α C = Φ ↑C ↑α := fun α C => rfl
  have hle : cycleConstrained Γ τ₀ ≤ oddSideFunctions Γ τ₀ := fun α hα => hα.1
  have hker : Submodule.comap (oddSideFunctions Γ τ₀).subtype (cycleConstrained Γ τ₀)
      = LinearMap.ker Ψ := by
    ext α
    rw [Submodule.mem_comap, LinearMap.mem_ker]
    constructor
    · intro hmem
      funext C
      exact hP1 ↑α hmem ↑C C.2
    · intro h0
      exact hP2 ↑α α.2 fun C hC => congrFun h0 ⟨C, hC⟩
  have hfr1 : Module.finrank ℝ (cycleConstrained Γ τ₀)
      = Module.finrank ℝ (LinearMap.ker Ψ) := by
    rw [← hker]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq.symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  obtain ⟨sing, hsing⟩ : ∃ sing : ↥(polygonVertexClasses Γ τ₀) →
      (↥(polygonVertexClasses Γ τ₀) → ℝ),
      sing = fun i j => if i = j then 1 else 0 := ⟨_, rfl⟩
  set lam : (↥(polygonVertexClasses Γ τ₀) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ C : ↥(polygonVertexClasses Γ τ₀), εs ↑C * f C
      map_add' := fun f g => by
        simp only [Pi.add_apply, mul_add]
        exact Finset.sum_add_distrib
      map_smul' := fun c f => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun C _ => by ring } with hlamdef
  have hlamval : ∀ f, lam f = ∑ C : ↥(polygonVertexClasses Γ τ₀), εs ↑C * f C :=
    fun f => rfl
  have hsingval : ∀ i : ↥(polygonVertexClasses Γ τ₀), lam (sing i) = εs ↑i := by
    intro i
    rw [hlamval]
    rw [Finset.sum_eq_single i]
    · rw [hsing]
      simp
    · intro b _ hb
      rw [hsing]
      simp only [if_neg (fun h : i = b => hb h.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hΨsum : ∀ α : ↥(oddSideFunctions Γ τ₀), lam (Ψ α) = 0 := by
    intro α
    have h3 := hP3 ↑α α.2
    rw [finsum_mem_eq_finite_toFinset_sum _ hclassfin] at h3
    have h4 : ∑ i ∈ hclassfin.toFinset, εs i * Φ i ↑α
        = ∑ C : ↥(polygonVertexClasses Γ τ₀), εs ↑C * Φ ↑C ↑α :=
      Finset.sum_subtype hclassfin.toFinset (fun x => hclassfin.mem_toFinset)
        (fun C => εs C * Φ C ↑α)
    rw [h4] at h3
    exact h3
  have hrange : LinearMap.range Ψ ≤ LinearMap.ker lam := by
    rintro f ⟨α, rfl⟩
    exact hΨsum α
  have hCne : ∃ C, C ∈ polygonVertexClasses Γ τ₀ := by
    obtain ⟨N, es, hN0, -, -, -, hesshare⟩ :=
      exists_boundary_side_cycle hΓ hfree hε hgap hdense
    obtain ⟨v, hv, -, -⟩ := hesshare 0
    exact ⟨_, ⟨v, hv, rfl⟩⟩
  obtain ⟨C₀, hC₀⟩ := hCne
  have hεC₀ : εs C₀ ≠ 0 := by
    rcases hεpm C₀ hC₀ with h | h <;> rw [h] <;> norm_num
  have hlamne : lam ≠ 0 := by
    intro h
    have h2 := congrFun (congrArg DFunLike.coe h) (sing ⟨C₀, hC₀⟩)
    rw [hsingval ⟨C₀, hC₀⟩] at h2
    exact hεC₀ h2
  have hlam_rn := LinearMap.finrank_range_add_finrank_ker lam
  have hlamrange : LinearMap.range lam = ⊤ := by
    obtain ⟨f, hf⟩ : ∃ f, lam f ≠ 0 := by
      by_contra h
      push Not at h
      exact hlamne (LinearMap.ext fun f => h f)
    rw [LinearMap.range_eq_top]
    intro r
    refine ⟨(r / lam f) • f, ?_⟩
    rw [map_smul, smul_eq_mul]
    field_simp
  rw [hlamrange, finrank_top, Module.finrank_self] at hlam_rn
  have hcard : Module.finrank ℝ ((↥(polygonVertexClasses Γ τ₀)) → ℝ)
      = polygonVertexClassCount Γ τ₀ := by
    rw [Module.finrank_fintype_fun_eq_card]
    change Fintype.card _ = (polygonVertexClasses Γ τ₀).ncard
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hupper : Module.finrank ℝ (LinearMap.range Ψ)
      ≤ Module.finrank ℝ (LinearMap.ker lam) := Submodule.finrank_mono hrange
  have hlower : Module.finrank ℝ (LinearMap.ker lam)
      ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    by_contra hlt
    push Not at hlt
    have hw0ne : sing ⟨C₀, hC₀⟩ ≠ 0 := by
      intro h
      have h2 := congrFun h ⟨C₀, hC₀⟩
      rw [hsing] at h2
      simp at h2
    have hspan1 : Module.finrank ℝ (ℝ ∙ sing ⟨C₀, hC₀⟩) = 1 := finrank_span_singleton hw0ne
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Ψ)
      (ℝ ∙ sing ⟨C₀, hC₀⟩)
    have hU'' : LinearMap.range Ψ ⊔ (ℝ ∙ sing ⟨C₀, hC₀⟩) ≠ ⊤ := by
      intro htop
      have h4 : Module.finrank ℝ ((↥(polygonVertexClasses Γ τ₀)) → ℝ)
          = Module.finrank ℝ ↥(LinearMap.range Ψ ⊔ (ℝ ∙ sing ⟨C₀, hC₀⟩)) := by
        rw [htop, finrank_top]
      omega
    obtain ⟨h, hne0, hann⟩ := exists_ann_functional hU''
    have hcoef : ∀ f : ↥(polygonVertexClasses Γ τ₀) → ℝ,
        h f = ∑ C : ↥(polygonVertexClasses Γ τ₀), f C * h (sing C) := by
      intro f
      conv_lhs => rw [pi_eq_sum_univ f]
      rw [map_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [map_smul, smul_eq_mul, hsing]
    obtain ⟨mfun, hmfun⟩ : ∃ mfun : Set UpperHalfPlane → ℝ,
        mfun = fun C => if hC : C ∈ polygonVertexClasses Γ τ₀
          then h (sing ⟨C, hC⟩) else 0 := ⟨_, rfl⟩
    have hmval : ∀ C : ↥(polygonVertexClasses Γ τ₀), mfun ↑C = h (sing C) := by
      intro C
      rw [hmfun]
      simp only
      rw [dif_pos C.2]
    have hmhyp : ∀ α ∈ oddSideFunctions Γ τ₀,
        ∑ᶠ C ∈ polygonVertexClasses Γ τ₀, mfun C * Φ C α = 0 := by
      intro α hα
      rw [finsum_mem_eq_finite_toFinset_sum _ hclassfin]
      have h4 : ∑ i ∈ hclassfin.toFinset, mfun i * Φ i α
          = ∑ C : ↥(polygonVertexClasses Γ τ₀), mfun ↑C * Φ ↑C α :=
        Finset.sum_subtype hclassfin.toFinset (fun x => hclassfin.mem_toFinset)
          (fun C => mfun C * Φ C α)
      rw [h4]
      have h5 : ∑ C : ↥(polygonVertexClasses Γ τ₀), mfun ↑C * Φ ↑C α
          = h (Ψ ⟨α, hα⟩) := by
        rw [hcoef]
        refine Finset.sum_congr rfl fun C _ => ?_
        rw [hmval C]
        exact mul_comm _ _
      rw [h5]
      exact hann _ (Submodule.mem_sup_left (LinearMap.mem_range_self Ψ ⟨α, hα⟩))
    have hP5app := hP5 mfun hmhyp
    have hcoords : ∀ C : ↥(polygonVertexClasses Γ τ₀),
        h (sing C) = mfun C₀ * εs C₀ * εs ↑C := by
      intro C
      have h1 := hP5app ↑C C.2 C₀ hC₀
      rw [← hmval C]
      rcases hεpm ↑C C.2 with h2 | h2 <;> rw [h2] at h1 ⊢ <;> linarith
    have ht0 : mfun C₀ * εs C₀ = 0 := by
      have h1 := hcoords ⟨C₀, hC₀⟩
      have h2 : h (sing ⟨C₀, hC₀⟩) = 0 :=
        hann _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      rw [h2] at h1
      rcases hεpm C₀ hC₀ with h3 | h3 <;> rw [h3] at h1 ⊢ <;> linarith
    refine hne0 (LinearMap.ext fun f => ?_)
    rw [hcoef f]
    refine Finset.sum_eq_zero fun C _ => ?_
    rw [hcoords C, ht0]
    ring
  have hfr_range : Module.finrank ℝ (LinearMap.range Ψ)
      = Module.finrank ℝ (LinearMap.ker lam) := le_antisymm hupper hlower
  have hm := finrank_oddSideFunctions hΓ hfree hε hgap hdense
  rw [hm] at hrn
  rw [hcard] at hlam_rn
  rw [hfr1]
  omega

/-- A trivially-acting element of a subgroup of `SL(2, ℝ)` squares to the identity: it is
`±1` as a matrix. -/
theorem sq_eq_one_of_smul_id {δ : ↥Γ} (h : ∀ τ : UpperHalfPlane, δ • τ = τ) :
    δ * δ = 1 := by
  have h' : ∀ τ : UpperHalfPlane, (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := by
    intro τ
    rw [← Subgroup.smul_def]
    exact h τ
  have hsq : ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      * ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rcases (smul_id_iff_pm_one _).mp h' with h1 | h1 <;> rw [h1]
    · rw [one_mul]
    · rw [neg_mul_neg, one_mul]
  have hSL : (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1 := by
    have hmat : (((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)
        = ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact hsq
    exact Subtype.coe_injective hmat
  have hval : ((δ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      = ((1 : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
    rw [Subgroup.coe_mul, OneMemClass.coe_one]
    exact hSL
  exact Subtype.coe_injective hval

/-- An additive character is odd. -/
theorem hom_apply_inv {G : Type*} [Group G] (f : homSubmodule G) (g : G) :
    (f : G → ℝ) g⁻¹ = -(f : G → ℝ) g := by
  have h := f.2 g⁻¹ g
  rw [inv_mul_cancel, homSubmodule_apply_one f] at h
  linarith

/-- Restriction to side values is the indicator of the side elements. -/
theorem restrictSides_apply (f : homSubmodule (↥Γ)) :
    restrictSides Γ τ₀ f
      = {γ : ↥Γ | IsSideElement Γ τ₀ γ}.indicator (f : (↥Γ) → ℝ) := rfl

/-- The side values of an additive character are cycle-constrained: they are odd and
fiber-constant since characters kill torsion, and the crossing sum along a vertex loop
telescopes to the value of the character at a trivially-acting element. -/
theorem restrictSides_mem_cycleConstrained (_hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (f : homSubmodule (↥Γ)) :
    restrictSides Γ τ₀ f ∈ cycleConstrained Γ τ₀ := by
  rw [restrictSides_apply]
  set S : Set ↥Γ := {γ : ↥Γ | IsSideElement Γ τ₀ γ} with hS
  refine ⟨⟨fun γ hγ => ?_, fun γ => ?_, fun γ δ h => ?_⟩, fun v hv p hp => ?_⟩
  · exact Set.indicator_of_notMem (show γ ∉ S from hγ) _
  · by_cases hγ : IsSideElement Γ τ₀ γ
    · rw [Set.indicator_of_mem (show γ⁻¹ ∈ S from hγ.inv),
        Set.indicator_of_mem (show γ ∈ S from hγ)]
      exact hom_apply_inv f γ
    · have hγi : ¬IsSideElement Γ τ₀ γ⁻¹ := fun hi => hγ (by simpa using hi.inv)
      rw [Set.indicator_of_notMem (show γ⁻¹ ∉ S from hγi),
        Set.indicator_of_notMem (show γ ∉ S from hγ)]
      ring
  · by_cases hγ : IsSideElement Γ τ₀ γ
    · have hδ : IsSideElement Γ τ₀ δ := (isSideElement_congr h).mp hγ
      rw [Set.indicator_of_mem (show γ ∈ S from hγ), Set.indicator_of_mem (show δ ∈ S from hδ)]
      have ht : (δ⁻¹ * γ) • τ₀ = τ₀ := by rw [mul_smul, h, inv_smul_smul]
      have htriv := hfree (δ⁻¹ * γ) ⟨τ₀, ht⟩
      have h0 := homSubmodule_apply_eq_zero_of_sq f (sq_eq_one_of_smul_id htriv)
      have h2 := f.2 δ (δ⁻¹ * γ)
      rw [show δ * (δ⁻¹ * γ) = γ by group] at h2
      linarith
    · have hδ : ¬IsSideElement Γ τ₀ δ := fun hd => hγ ((isSideElement_congr h).mpr hd)
      rw [Set.indicator_of_notMem (show γ ∉ S from hγ),
        Set.indicator_of_notMem (show δ ∉ S from hδ)]
  · obtain ⟨htile, hmem, hclose⟩ := hp
    cases p with
    | nil => exact crossingSum_nil _
    | cons x l =>
      have hhead : (x :: l).head? = some x := rfl
      have hlast : (x :: l).getLast? = some x := by rw [← hclose]; exact hhead
      have hrel : ∀ u ∈ (x :: l), ∀ w ∈ (x :: l), IsSideElement Γ τ₀ (u⁻¹ * w) →
          S.indicator (f : (↥Γ) → ℝ) (u⁻¹ * w)
            = (f : (↥Γ) → ℝ) w - (f : (↥Γ) → ℝ) u := by
        intro u _ w _ hside
        rw [Set.indicator_of_mem (show u⁻¹ * w ∈ S from hside)]
        have h2 := f.2 u⁻¹ w
        rw [hom_apply_inv f u] at h2
        linarith
      rw [crossingSum_telescope (S.indicator (f : (↥Γ) → ℝ)) (f : (↥Γ) → ℝ)
        (x :: l) htile hrel hhead hlast]
      ring

/-- A character with vanishing side values vanishes: the side elements and the
trivially-acting elements generate the group, and the character kills both kinds of
generators. -/
theorem restrictSides_eq_zero_imp (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {F : homSubmodule (↥Γ)} (hF : restrictSides Γ τ₀ F = 0) : F = 0 := by
  have hside : ∀ γ : ↥Γ, IsSideElement Γ τ₀ γ → (F : (↥Γ) → ℝ) γ = 0 := by
    intro γ hγ
    have h1 := congrFun hF γ
    rw [restrictSides_apply,
      Set.indicator_of_mem (show γ ∈ {γ : ↥Γ | IsSideElement Γ τ₀ γ} from hγ)] at h1
    simpa using h1
  set K : Subgroup ↥Γ :=
    { carrier := {γ : ↥Γ | (F : (↥Γ) → ℝ) γ = 0}
      one_mem' := homSubmodule_apply_one F
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [F.2 a b, ha, hb, add_zero]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [hom_apply_inv F a, ha, neg_zero] } with hK
  have htop : Subgroup.closure ({δ : ↥Γ | IsSideElement Γ τ₀ δ} ∪
      {δ : ↥Γ | ∀ τ : UpperHalfPlane, δ • τ = τ}) ≤ K := by
    rw [Subgroup.closure_le]
    rintro γ (hγ | hγ)
    · exact hside γ hγ
    · exact homSubmodule_apply_eq_zero_of_sq F (sq_eq_one_of_smul_id hγ)
  rw [closure_sideElements_eq_top hΓ hfree hε hgap hdense] at htop
  apply Subtype.ext
  funext γ
  have hγK : γ ∈ K := htop (Subgroup.mem_top γ)
  simpa using! hγK

/-- Restriction to side values is injective: the side elements generate the group modulo
trivially-acting elements, on which every character vanishes. -/
theorem restrictSides_injective (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Function.Injective (restrictSides Γ τ₀) := by
  intro f g h
  have hz : restrictSides Γ τ₀ (f - g) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (restrictSides_eq_zero_imp hΓ hfree hε hgap hdense hz)

/-- The characters form a finite-dimensional space: restriction to side values embeds them
into the odd side functions. -/
theorem finiteDimensional_homSubmodule (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    FiniteDimensional ℝ (homSubmodule (↥Γ)) := by
  have := finiteDimensional_cycleConstrained hΓ hfree hε hgap hdense
  set φ : homSubmodule (↥Γ) →ₗ[ℝ] cycleConstrained Γ τ₀ :=
    LinearMap.codRestrict (cycleConstrained Γ τ₀) (restrictSides Γ τ₀)
      (fun f => restrictSides_mem_cycleConstrained hΓ hfree hε hgap hdense f) with hφ
  have hinj : Function.Injective φ := by
    intro f g h
    apply restrictSides_injective hΓ hfree hε hgap hdense
    exact congrArg Subtype.val h
  exact FiniteDimensional.of_injective φ hinj

/-- **The rank identity**: the dimension `Q` of the character space satisfies
`Q + c = m + 1`. Restriction to side values and integration along tile paths are mutually
inverse linear embeddings between the characters and the cycle-constrained side
functions. -/
theorem finrank_homSubmodule_add_classCount (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    Module.finrank ℝ (homSubmodule (↥Γ)) + polygonVertexClassCount Γ τ₀
      = polygonSideCount Γ τ₀ + 1 := by
  classical
  have := finiteDimensional_cycleConstrained hΓ hfree hε hgap hdense
  obtain ⟨Φ, hΦ⟩ := exists_crossingSum_hom hΓ hfree hε hgap hdense
  set φ : homSubmodule (↥Γ) →ₗ[ℝ] cycleConstrained Γ τ₀ :=
    LinearMap.codRestrict (cycleConstrained Γ τ₀) (restrictSides Γ τ₀)
      (fun f => restrictSides_mem_cycleConstrained hΓ hfree hε hgap hdense f) with hφ
  have hinj : Function.Injective φ := by
    intro f g h
    apply restrictSides_injective hΓ hfree hε hgap hdense
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective φ := by
    intro β
    refine ⟨Φ β, ?_⟩
    apply Subtype.ext
    change restrictSides Γ τ₀ (Φ β) = (β : (↥Γ) → ℝ)
    funext γ
    rw [restrictSides_apply]
    by_cases hγ : IsSideElement Γ τ₀ γ
    · rw [Set.indicator_of_mem (show γ ∈ {γ : ↥Γ | IsSideElement Γ τ₀ γ} from hγ)]
      exact hΦ β γ hγ
    · rw [Set.indicator_of_notMem (show γ ∉ {γ : ↥Γ | IsSideElement Γ τ₀ γ} from hγ)]
      obtain ⟨⟨hz, -, -⟩, -⟩ := mem_cycleConstrained.mp β.2
      exact (hz γ hγ).symm
  have e : (homSubmodule (↥Γ)) ≃ₗ[ℝ] (cycleConstrained Γ τ₀) :=
    LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  rw [e.finrank_eq]
  exact finrank_cycleConstrained_add_classCount hΓ hfree hε hgap hdense

end RiemannDynamics
