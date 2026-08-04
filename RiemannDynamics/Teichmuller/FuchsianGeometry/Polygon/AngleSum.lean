/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Polygon.SidePairing

/-!
# The Dirichlet polygon: angle sums and the combinatorial Gauss–Bonnet formula

* `sum_interiorAngle_vertexClass` — the interior angles along each vertex orbit class sum
  to `2π` through the bijection between the tiles at a vertex and the class vertices.
* `sum_apexAngle_basepoint` — the apex angles at the basepoint sum to `2π`.
* `volume_dirichletDomain_gaussBonnet` — the quantized area
  `volume (dirichletDomain Γ τ₀) = 2π (m - 1 - c)`, where `m` is the number of side
  pairs and `c` the number of vertex orbit classes.
-/

open MeasureTheory
open scoped ENNReal MatrixGroups

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## Angle sums -/

set_option maxHeartbeats 400000 in
-- The vertex-star assembly elaborates the full cycle, functional, and measure bookkeeping
-- in one declaration; the default heartbeat budget does not cover it.
/-- **Angle sum over a vertex class**: the interior angles of the polygon at the vertices of
one orbit class sum to `2π` — the sectors of the tiles at any vertex of the class partition
a disk about it, and the developed bijection carries them isometrically onto the class
angles. -/
theorem sum_interiorAngle_vertexClass (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) {α : UpperHalfPlane → ℝ}
    (hα : ∀ v' ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀,
      IsInteriorAngleAt Γ τ₀ v' (α v')) :
    ∑ᶠ v' ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀, α v' = 2 * Real.pi := by
  classical
  obtain ⟨n, e, hn3, hper, hecon, huniq, hadj⟩ :=
    exists_vertex_cycle hΓ hfree hε hgap hdense hv
  have hn0 : 0 < n := by omega
  -- distances from the vertex to the tile centers all realize the contact distance
  have hvd : ∀ k : ℕ, dist v (e k • τ₀) = Metric.infDist v (MulAction.orbit Γ τ₀) := by
    intro k
    have h1 := hecon k
    simp only [contactSet, Set.mem_setOf_eq] at h1
    exact h1
  have hveq : ∀ k j : ℕ, dist v (e k • τ₀) = dist v (e j • τ₀) := by
    intro k j
    rw [hvd k, hvd j]
  -- periodic reduction of the enumeration
  have hemod : ∀ k : ℕ, e k = e (k % n) := by
    intro k
    conv_lhs => rw [show k = k % n + n * (k / n) from (Nat.mod_add_div k n).symm]
    generalize k / n = q
    induction q with
    | zero => rw [Nat.mul_zero, Nat.add_zero]
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  -- distinct centers detect distinct residues
  have hcent : ∀ a b : ℕ, e a • τ₀ = e b • τ₀ → a % n = b % n := by
    intro a b hab
    obtain ⟨k, -, hk⟩ := huniq (e a) (hecon a)
    have h1 := hk (a % n) ⟨Nat.mod_lt a hn0, by rw [← hemod a]⟩
    have h2 := hk (b % n) ⟨Nat.mod_lt b hn0, by rw [← hemod b, ← hab]⟩
    rw [h1, h2]
  have hcne : ∀ a b : ℕ, ¬ a ≡ b [MOD n] → e a • τ₀ ≠ e b • τ₀ := by
    intro a b hmod hab
    exact hmod (hcent a b hab)
  -- index bookkeeping for the previous side
  set p : ℕ → ℕ := fun k => k + (n - 1) with hpdef
  have hp1 : ∀ k, p k + 1 = k + n := by
    intro k
    simp only [hpdef]
    omega
  have hep1 : ∀ k, e (p k + 1) = e k := by
    intro k
    rw [hp1 k, hper]
  have hmod_k_k1 : ∀ k : ℕ, ¬ k ≡ k + 1 [MOD n] := by
    intro k h1
    have h2 := (Nat.modEq_iff_dvd' (by omega)).mp h1
    have h3 : n ∣ 1 := by simpa using h2
    have h4 := Nat.le_of_dvd one_pos h3
    omega
  have hmod_k_pk : ∀ k : ℕ, ¬ k ≡ p k [MOD n] := by
    intro k h1
    have h2 := (Nat.modEq_iff_dvd' (by simp only [hpdef]; omega)).mp h1
    simp only [hpdef] at h2
    have h3 : n ∣ n - 1 := by
      have h4 : k + (n - 1) - k = n - 1 := by omega
      rwa [h4] at h2
    have h5 := Nat.le_of_dvd (by omega) h3
    omega
  have hmod_k1_pk : ∀ k : ℕ, ¬ k + 1 ≡ p k [MOD n] := by
    intro k h1
    have h2 := (Nat.modEq_iff_dvd' (by simp only [hpdef]; omega)).mp h1
    simp only [hpdef] at h2
    have h3 : n ∣ n - 2 := by
      have h4 : k + (n - 1) - (k + 1) = n - 2 := by omega
      rwa [h4] at h2
    have h5 : n - 2 = 0 ∨ n ≤ n - 2 := by
      rcases Nat.eq_zero_or_pos (n - 2) with h6 | h6
      · exact Or.inl h6
      · exact Or.inr (Nat.le_of_dvd h6 h3)
    omega
  -- the far endpoints of the shared sides
  have hWex : ∀ k : ℕ, ∃ W : UpperHalfPlane, W ≠ v ∧
      dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
        = geodSeg ((e k)⁻¹ • v) ((e k)⁻¹ • W) := by
    intro k
    have hSide : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∈ polygonSides Γ τ₀ :=
      ⟨_, hadj k, rfl⟩
    have hgS : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) :=
      smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon (k + 1))
    have hgvert : (e k)⁻¹ • v ∈ polygonVertices Γ τ₀ :=
      smul_mem_polygonVertices hv (hecon k)
    have hend := isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hSide hgS
    obtain ⟨a, b, hab, heq⟩ :=
      exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hSide
    rw [heq] at hend
    rcases (isSegEndpoint_geodSeg_iff hab).mp hend with h1 | h1
    · refine ⟨e k • b, ?_, ?_⟩
      · intro h2
        rw [← h2, inv_smul_smul] at h1
        exact hab (h1.symm ▸ rfl)
      · rw [inv_smul_smul, heq, ← h1]
    · refine ⟨e k • a, ?_, ?_⟩
      · intro h2
        rw [← h2, inv_smul_smul] at h1
        exact hab (h1 ▸ rfl)
      · rw [inv_smul_smul, heq, ← h1, geodSeg_comm]
  choose W hWv hWrep using hWex
  -- the shared sides as radial segments at the vertex
  have hσ : ∀ k : ℕ, (e k • ·) '' dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
      = geodSeg v (W k) := by
    intro k
    rw [hWrep k, subgroup_smul_geodSeg, smul_inv_smul, smul_inv_smul]
  have hσsubT : ∀ k : ℕ, geodSeg v (W k) ⊆ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    rw [← hσ k]
    exact Set.image_mono fun x hx => hx.1
  have hσsubT' : ∀ k : ℕ, geodSeg v (W k) ⊆ (e (k + 1) • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    rw [← hσ k]
    rintro x ⟨y, hy, rfl⟩
    have h1 := smul_mem_dirichletSideSet_inv hy
    refine ⟨((e k)⁻¹ * e (k + 1))⁻¹ • y, h1.1, ?_⟩
    change e (k + 1) • ((e k)⁻¹ * e (k + 1))⁻¹ • y = e k • y
    rw [← mul_smul, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  have hσbis : ∀ k : ℕ, ∀ x ∈ geodSeg v (W k),
      dist x (e k • τ₀) = dist x (e (k + 1) • τ₀) := by
    intro k x hx
    rw [← hσ k] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
      ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
    have h1 : dist y τ₀ = dist y (((e k)⁻¹ * e (k + 1)) • τ₀) := hy.2
    have e1 : dist (e k • y) (e k • τ₀) = dist y τ₀ := dist_smul (e k) y τ₀
    have e2 : dist (e k • y) (e (k + 1) • τ₀)
        = dist y (((e k)⁻¹ * e (k + 1)) • τ₀) := by
      calc dist (e k • y) (e (k + 1) • τ₀)
          = dist ((e k)⁻¹ • e k • y) ((e k)⁻¹ • e (k + 1) • τ₀) :=
            (dist_smul (e k)⁻¹ _ _).symm
        _ = dist y (((e k)⁻¹ * e (k + 1)) • τ₀) := by rw [inv_smul_smul, mul_smul]
    rw [e1, e2]
    exact h1
  -- the sign functionals of the two sides of each tile
  have hmove_next : ∀ k : ℕ, e k • τ₀ ≠ e (k + 1) • τ₀ := fun k => hcne _ _ (hmod_k_k1 k)
  have hmove_prev : ∀ k : ℕ, e k • τ₀ ≠ e (p k) • τ₀ := fun k => hcne _ _ (hmod_k_pk k)
  have hmove_np : ∀ k : ℕ, e (k + 1) • τ₀ ≠ e (p k) • τ₀ := fun k => hcne _ _ (hmod_k1_pk k)
  have hσprev_bis : ∀ k : ℕ, ∀ x ∈ geodSeg v (W (p k)),
      dist x (e k • τ₀) = dist x (e (p k) • τ₀) := by
    intro k x hx
    have h1 := hσbis (p k) x hx
    rw [hep1 k] at h1
    exact h1.symm
  have hσprev_subT : ∀ k : ℕ, geodSeg v (W (p k)) ⊆ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    have h1 := hσsubT' (p k)
    rw [hep1 k] at h1
    exact h1
  have hd2 : ∀ k : ℕ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart v (W (p k)) / discChart v (W k)).im ∧
      (∀ w ∈ (e k • ·) '' dirichletDomain Γ τ₀,
        0 ≤ σ * (discChart v w / discChart v (W k)).im) ∧
      (∀ w ∈ (e k • ·) '' interior (dirichletDomain Γ τ₀),
        0 < σ * (discChart v w / discChart v (W k)).im) := by
    intro k
    exact side_functional hΓ hdense (hmove_next k) (hveq k (k + 1))
      (hσbis k (W k) (right_mem_geodSeg v (W k))) (hWv k)
      (Ne.symm (hmove_np k)) (Ne.symm (hmove_prev k)) (hWv (p k))
      (fun w hw => hσprev_bis k w hw) (hσprev_subT k)
  have hd1 : ∀ k : ℕ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart v (W k) / discChart v (W (p k))).im ∧
      (∀ w ∈ (e k • ·) '' dirichletDomain Γ τ₀,
        0 ≤ σ * (discChart v w / discChart v (W (p k))).im) ∧
      (∀ w ∈ (e k • ·) '' interior (dirichletDomain Γ τ₀),
        0 < σ * (discChart v w / discChart v (W (p k))).im) := by
    intro k
    exact side_functional hΓ hdense (hmove_prev k) (hveq k (p k))
      (hσprev_bis k (W (p k)) (right_mem_geodSeg v (W (p k)))) (hWv (p k))
      (hmove_np k) (Ne.symm (hmove_next k)) (hWv k)
      (fun w hw => hσbis k w hw) (hσsubT k)
  choose σ₁ hσ₁pm hσ₁P hσ₁w hσ₁i using hd1
  choose σ₂ hσ₂pm hσ₂P hσ₂w hσ₂i using hd2
  -- two tiles meet only along the shared sides through the vertex
  have hδ'elem : ∀ k : ℕ, IsSideElement Γ τ₀ ((e k)⁻¹ * e (p k)) := by
    intro k
    have h1 := (hadj (p k)).inv
    have h2 : ((e (p k))⁻¹ * e (p k + 1))⁻¹ = (e k)⁻¹ * e (p k) := by
      rw [hep1 k, mul_inv_rev, inv_inv]
    rwa [h2] at h1
  have hσ'eq : ∀ k : ℕ, (e k • ·) '' dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k))
      = geodSeg v (W (p k)) := by
    intro k
    have h2 : ((e (p k))⁻¹ * e (p k + 1))⁻¹ = (e k)⁻¹ * e (p k) := by
      rw [hep1 k, mul_inv_rev, inv_inv]
    rw [← h2, ← smul_sideSet_inv, smul_smul_image]
    have h3 : e k * ((e (p k))⁻¹ * e (p k + 1))⁻¹ = e (p k) := by
      rw [mul_inv_rev, inv_inv, hep1 k, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [h3, hσ (p k)]
  have hTinter : ∀ k j : ℕ, ¬ k ≡ j [MOD n] → ∀ y : UpperHalfPlane,
      y ∈ (e k • ·) '' dirichletDomain Γ τ₀ → y ∈ (e j • ·) '' dirichletDomain Γ τ₀ →
      y = v ∨ y ∈ geodSeg v (W k) ∨ y ∈ geodSeg v (W (p k)) := by
    intro k j hmod y hyk hyj
    have hβmove : ((e k)⁻¹ * e j) • τ₀ ≠ τ₀ := by
      intro h0
      have h1 : e k • ((e k)⁻¹ * e j) • τ₀ = e k • τ₀ := congrArg (e k • ·) h0
      rw [← mul_smul, mul_inv_cancel_left] at h1
      exact hcne k j hmod h1.symm
    have hz₁S : (e k)⁻¹ • y ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j) := by
      refine inter_smul_subset_sideSet _ ⟨?_, ?_⟩
      · obtain ⟨w₁, hw₁, rfl⟩ := hyk
        rw [inv_smul_smul]
        exact hw₁
      · obtain ⟨w₂, hw₂, hw₂y⟩ := hyj
        have hw₂y' : e j • w₂ = y := hw₂y
        refine ⟨w₂, hw₂, ?_⟩
        change ((e k)⁻¹ * e j) • w₂ = (e k)⁻¹ • y
        rw [mul_smul, hw₂y']
    have hgS : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j) :=
      smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon j)
    by_cases hnt : (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)).Nontrivial
    · have hgvert : (e k)⁻¹ • v ∈ polygonVertices Γ τ₀ :=
        smul_mem_polygonVertices hv (hecon k)
      have hSβ : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j) ∈ polygonSides Γ τ₀ :=
        ⟨_, ⟨hβmove, hnt⟩, rfl⟩
      have hendβ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)) ((e k)⁻¹ • v) :=
        isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hSβ hgS
      have hA₁side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∈ polygonSides Γ τ₀ :=
        ⟨_, hadj k, rfl⟩
      have hgA₁ : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) :=
        smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon (k + 1))
      have hendA₁ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)))
          ((e k)⁻¹ • v) :=
        isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hA₁side hgA₁
      have hA₂side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) ∈ polygonSides Γ τ₀ :=
        ⟨_, hδ'elem k, rfl⟩
      have hgA₂ : (e k)⁻¹ • v ∈ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) :=
        smul_mem_dirichletSideSet_of_contact_pair (hecon k) (hecon (p k))
      have hendA₂ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)))
          ((e k)⁻¹ • v) :=
        isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hgvert hA₂side hgA₂
      have hA12 : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
          ≠ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) := by
        intro h0
        have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree (hadj k) (hδ'elem k) h0
        have h2 := congrArg (e k • ·) h1
        simp only at h2
        rw [← mul_smul, ← mul_smul, mul_inv_cancel_left, mul_inv_cancel_left] at h2
        exact hmove_np k h2
      obtain ⟨s₁, hs₁, s₂, hs₂, hs12, he₁, he₂, hu2q⟩ :=
        exists_two_sides_at_vertex hΓ hfree hε hgap hdense hgvert
      have hm₁ := hu2q _ hA₁side hendA₁
      have hm₂ := hu2q _ hA₂side hendA₂
      have hmβ := hu2q _ hSβ hendβ
      have hcase : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)
          = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∨
          dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)
          = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) := by
        rcases hm₁ with h₁ | h₁ <;> rcases hm₂ with h₂ | h₂ <;> rcases hmβ with h₃ | h₃ <;>
          first
          | exact absurd (h₁.trans h₂.symm) hA12
          | exact Or.inl (h₃.trans h₁.symm)
          | exact Or.inr (h₃.trans h₂.symm)
      rcases hcase with h4 | h4
      · right
        left
        rw [← hσ k]
        rw [h4] at hz₁S
        exact ⟨(e k)⁻¹ • y, hz₁S, by change e k • (e k)⁻¹ • y = y; rw [smul_inv_smul]⟩
      · right
        right
        rw [← hσ'eq k]
        rw [h4] at hz₁S
        exact ⟨(e k)⁻¹ • y, hz₁S, by change e k • (e k)⁻¹ • y = y; rw [smul_inv_smul]⟩
    · have hsub : (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e j)).Subsingleton :=
        Set.not_nontrivial_iff.mp hnt
      have h1 : (e k)⁻¹ • y = (e k)⁻¹ • v := hsub hz₁S hgS
      left
      have h2 := congrArg (e k • ·) h1
      simp only at h2
      rw [smul_inv_smul, smul_inv_smul] at h2
      exact h2
  -- the working radius and chart scale
  obtain ⟨rc, hrc, hloc, hcover⟩ := exists_ball_inter_tiles_subset_contact hΓ τ₀ v
  set r' : ℝ := min rc 1 with hr'def
  have hr' : 0 < r' := lt_min hrc one_pos
  have hr'1 : r' ≤ 1 := min_le_right _ _
  have hr'rc : r' ≤ rc := min_le_left _ _
  set sc : ℝ := Real.tanh (r' / 2) with hscdef
  have hsc0 : 0 < sc := by
    rw [hscdef, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hsc1 : sc < 1 := Real.tanh_lt_one _
  have hballT : ∀ y : UpperHalfPlane, dist v y < r' → ∃ k < n,
      y ∈ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro y hy
    have h1 : y ∈ Metric.ball v rc := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy hr'rc
    obtain ⟨δ, hδ, hδy⟩ := hcover y h1
    obtain ⟨k, ⟨hkn, hkc⟩, -⟩ := huniq δ hδ
    refine ⟨k, hkn, ?_⟩
    rw [← smul_image_eq_of_basepoint_eq hfree hkc]
    exact hδy
  -- corner filling: a strict sector point of the working ball lies in the tile
  have hfill : ∀ k, k < n → ∀ y₀ : UpperHalfPlane, dist v y₀ < r' →
      0 < σ₁ k * (discChart v y₀ / discChart v (W (p k))).im →
      0 < σ₂ k * (discChart v y₀ / discChart v (W k)).im →
      y₀ ∈ (e k • ·) '' dirichletDomain Γ τ₀ := by
    intro k hkn y₀ hy₀r hy₀1 hy₀2
    set OS : Set ℂ := {x : ℂ | ‖x‖ < sc ∧
        0 < σ₁ k * (x / discChart v (W (p k))).im ∧
        0 < σ₂ k * (x / discChart v (W k)).im} with hOSdef
    set POS : Set UpperHalfPlane :=
      {w : UpperHalfPlane | dist v w < r' ∧ discChart v w ∈ OS} with hPOSdef
    have hchartmem : ∀ w : UpperHalfPlane, dist v w < r' →
        0 < σ₁ k * (discChart v w / discChart v (W (p k))).im →
        0 < σ₂ k * (discChart v w / discChart v (W k)).im → w ∈ POS := by
      intro w h1 h2 h3
      exact ⟨h1, (dist_lt_iff_norm_chart hr').mp h1, h2, h3⟩
    have hy₀POS : y₀ ∈ POS := hchartmem y₀ hy₀r hy₀1 hy₀2
    have hOSpre : IsPreconnected OS :=
      sector_preconnected' (hσ₁pm k) (hσ₂pm k)
        (discChart_ne_zero (hWv (p k))) (discChart_ne_zero (hWv k)) (hσ₁P k) (hσ₂P k)
    have hOSsub : OS ⊆ {u : ℂ | ‖u‖ < 1} := fun u hu => lt_trans hu.1 hsc1
    have hPOSimg : (fun w : UpperHalfPlane => (w : ℂ)) '' POS = (fun u : ℂ =>
        ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u))) '' OS := by
      apply Set.Subset.antisymm
      · rintro x ⟨w, ⟨hwr, hwOS⟩, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj v (lt_trans hwOS.1 hsc1)
        have hww : w' = w := discChart_injective v hw'chart
        refine ⟨discChart v w, hwOS, ?_⟩
        change ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I
            * ((1 + discChart v w) / (1 - discChart v w)) = (w : ℂ)
        rw [← hw'coe, hww]
      · rintro x ⟨u, huOS, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj v (hOSsub huOS)
        refine ⟨w', ⟨?_, ?_⟩, ?_⟩
        · exact (dist_lt_iff_norm_chart hr').mpr (by rw [hw'chart]; exact huOS.1)
        · rw [hw'chart]
          exact huOS
        · change (w' : ℂ) = ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I
            * ((1 + u) / (1 - u))
          exact hw'coe
    have hFcont : ContinuousOn (fun u : ℂ =>
        ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
        {u : ℂ | ‖u‖ < 1} := by
      refine ContinuousOn.add continuousOn_const ?_
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div ((continuous_const.add continuous_id).continuousOn)
        ((continuous_const.sub continuous_id).continuousOn) ?_
      intro u hu h0
      have h1 : u = 1 := by linear_combination -h0
      rw [Set.mem_setOf_eq, h1] at hu
      simp at hu
    have hPOSpre : IsPreconnected POS := by
      have h1 : IsPreconnected ((fun u : ℂ =>
          ((v.re : ℝ) : ℂ) + ((v.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u))) '' OS) :=
        hOSpre.image _ (hFcont.mono hOSsub)
      rw [← hPOSimg] at h1
      exact (UpperHalfPlane.isEmbedding_coe.toIsInducing.isPreconnected_image).mp h1
    have hPne : ∀ w ∈ POS, w ≠ v := by
      intro w hw h0
      have h1 := hw.2.2.1
      rw [h0, discChart_self, zero_div] at h1
      simp at h1
    have hPray : ∀ w ∈ POS, w ∉ geodSeg v (W k) ∧ w ∉ geodSeg v (W (p k)) := by
      intro w hw
      constructor
      · intro h1
        have h2 := ray_kill (hWv k) h1 (hPne w hw)
        have h3 := hw.2.2.2
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
      · intro h1
        have h2 := ray_kill (hWv (p k)) h1 (hPne w hw)
        have h3 := hw.2.2.1
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
    set A : Set UpperHalfPlane := (e k • ·) '' dirichletDomain Γ τ₀ with hAdef
    set C : Set UpperHalfPlane := ⋃ j ∈ (Finset.range n).erase k,
        (e j • ·) '' dirichletDomain Γ τ₀ with hCdef
    have hAcl : IsClosed A := isClosed_tile (e k)
    have hCcl : IsClosed C :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun j _ => isClosed_tile (e j)
    have hPsub : POS ⊆ A ∪ C := by
      intro w hw
      obtain ⟨j, hjn, hjw⟩ := hballT w hw.1
      by_cases hjk : j = k
      · subst hjk
        left
        exact hjw
      · right
        exact Set.mem_biUnion (Finset.mem_erase.mpr ⟨hjk, Finset.mem_range.mpr hjn⟩) hjw
    have hPAC : ∀ w ∈ POS, w ∈ A → w ∈ C → False := by
      intro w hwP hwA hwC
      rw [hCdef, Set.mem_iUnion₂] at hwC
      obtain ⟨j, hj, hjw⟩ := hwC
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      have hjn' : j < n := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
      have hmod : ¬ k ≡ j [MOD n] := by
        intro h0
        have hk' : k % n = k := Nat.mod_eq_of_lt hkn
        have hj' : j % n = j := Nat.mod_eq_of_lt hjn'
        rw [Nat.ModEq, hk', hj'] at h0
        exact hjk h0.symm
      rcases hTinter k j hmod w hwA hjw with h1 | h1 | h1
      · exact hPne w hwP h1
      · exact (hPray w hwP).1 h1
      · exact (hPray w hwP).2 h1
    have hgkD : (e k)⁻¹ • v ∈ dirichletDomain Γ τ₀ :=
      (smul_mem_polygonVertices hv (hecon k)).1
    have hgkτ : (e k)⁻¹ • v ≠ τ₀ := by
      intro h0
      have h1 := smul_basepoint_ne hv (hecon k)
      apply h1
      have h2 := congrArg (e k • ·) h0
      simp only at h2
      rw [smul_inv_smul] at h2
      exact h2.symm
    set d : ℝ := dist τ₀ ((e k)⁻¹ • v) with hddef
    have hd0 : 0 < d := dist_pos.mpr (Ne.symm hgkτ)
    set t : ℝ := 1 - r' / (2 * (d + 1)) with htdef
    have hx0 : 0 < r' / (2 * (d + 1)) := by positivity
    have hxhalf : r' / (2 * (d + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by simp only [htdef]; linarith,
      by simp only [htdef]; linarith⟩
    set xt : UpperHalfPlane := geodInterp τ₀ ((e k)⁻¹ • v) t with hxtdef
    have hxtseg : xt ∈ geodSeg τ₀ ((e k)⁻¹ • v) := geodInterp_mem_geodSeg _ _ ht01
    have hxtdist : dist τ₀ xt = t * d := dist_geodInterp_left _ _ ht01
    have hxtne : xt ≠ (e k)⁻¹ • v := by
      intro h0
      have h1 : dist τ₀ xt = d := by rw [h0]
      rw [hxtdist] at h1
      nlinarith
    have hxtint : xt ∈ interior (dirichletDomain Γ τ₀) :=
      mem_interior_of_mem_geodSeg hΓ hdense hgkD hxtseg hxtne
    set wt : UpperHalfPlane := e k • xt with hwtdef
    have hwtint : wt ∈ (e k • ·) '' interior (dirichletDomain Γ τ₀) := ⟨xt, hxtint, rfl⟩
    have hwtdist : dist v wt < r' := by
      have h1 : dist v wt = dist ((e k)⁻¹ • v) xt := by
        haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
          ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
        rw [hwtdef, ← dist_smul (e k) ((e k)⁻¹ • v) xt, smul_inv_smul]
      have h2 : dist ((e k)⁻¹ • v) xt = (1 - t) * d := by
        rw [hxtdef, dist_comm]
        have h3 := dist_geodInterp_pair τ₀ ((e k)⁻¹ • v) t 1
        rw [geodInterp_one] at h3
        rw [h3, abs_of_nonpos (by simp only [htdef]; linarith), ← hddef]
        ring
      rw [h1, h2]
      have h4 : (1 - t) * d = r' * (d / (2 * (d + 1))) := by
        simp only [htdef]
        field_simp
        ring
      rw [h4]
      have h5 : d / (2 * (d + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 hr'.le
      linarith
    have hwtPOS : wt ∈ POS :=
      hchartmem wt hwtdist (hσ₁i k wt hwtint) (hσ₂i k wt hwtint)
    have hwtA : wt ∈ A := ⟨xt, interior_subset hxtint, rfl⟩
    have hPC : ∀ w ∈ POS, w ∉ C := by
      intro w hw hwC
      by_cases hwA : w ∈ A
      · exact hPAC w hw hwA hwC
      · rw [isPreconnected_closed_iff] at hPOSpre
        obtain ⟨z, hz⟩ := hPOSpre A C hAcl hCcl hPsub ⟨wt, hwtPOS, hwtA⟩ ⟨w, hw, hwC⟩
        exact hPAC z hz.1 hz.2.1 hz.2.2
    rcases hPsub hy₀POS with h1 | h1
    · exact h1
    · exact absurd h1 (hPC y₀ hy₀POS)
  -- direction windows of the tiles and their measures
  set Dir : ℕ → Set ℝ := fun k => {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
      0 ≤ σ₁ k * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W (p k))).im ∧
      0 ≤ σ₂ k * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W k)).im} with hDirdef
  have hDirvol : ∀ k, volume (Dir k) = ENNReal.ofReal (sectorAngle v (W (p k)) (W k)) := by
    intro k
    exact vol_arc (hσ₁pm k) (hσ₂pm k) (discChart_ne_zero (hWv (p k)))
      (discChart_ne_zero (hWv k)) (hσ₁P k) (hσ₂P k)
  have hsc2 : (0 : ℝ) < sc / 2 := by linarith
  have hEnorm : ∀ φ : ℝ, ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖
      = sc / 2 := by
    intro φ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsc2]
  have hscale : ∀ (σv : ℝ) (u : ℂ) (φ : ℝ),
      (0 ≤ σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im ↔
        0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im) ∧
      (0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im →
        0 < σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im) := by
    intro σv u φ
    have h1 : ((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u
        = ((sc / 2 : ℝ) : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) / u) := mul_div_assoc _ _ _
    rw [h1, Complex.im_ofReal_mul]
    constructor
    · constructor
      · intro h2
        nlinarith
      · intro h2
        nlinarith
    · intro h2
      nlinarith
  have hDircov : Set.Ico (-Real.pi) Real.pi ⊆ ⋃ k ∈ Finset.range n, Dir k := by
    intro φ hφ
    have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
      rw [hEnorm φ]
      linarith
    obtain ⟨y, hychart, -⟩ := chart_surj v hu1
    have hyd : dist v y < r' := by
      refine (dist_lt_iff_norm_chart hr').mpr ?_
      rw [hychart, hEnorm φ]
      linarith
    obtain ⟨k, hkn, hyT⟩ := hballT y hyd
    have h₁ := hσ₁w k y hyT
    have h₂ := hσ₂w k y hyT
    rw [hychart] at h₁ h₂
    refine Set.mem_biUnion (Finset.mem_range.mpr hkn) ⟨hφ, ?_, ?_⟩
    · exact ((hscale (σ₁ k) (discChart v (W (p k))) φ).1).mp h₁
    · exact ((hscale (σ₂ k) (discChart v (W k)) φ).1).mp h₂
  have hDirdisj : ∀ k, k < n → ∀ j, j < n → k ≠ j → volume (Dir k ∩ Dir j) = 0 := by
    intro k hkn j hjn hkj
    have hzero : Dir k ∩ Dir j ⊆
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W (p k)))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W k))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W (p j)))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart v (W j))) = 0} := by
      intro φ hφ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and] at hcon
      obtain ⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩ := hcon
      obtain ⟨⟨hφw, hc1k, hc2k⟩, -, hc1j, hc2j⟩ := hφ
      have hstrict : ∀ (σv : ℝ), (σv = 1 ∨ σv = -1) → ∀ y : UpperHalfPlane, y ≠ v →
          Real.sin (φ - Complex.arg (discChart v y)) ≠ 0 →
          0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v y).im →
          0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart v y).im := by
        intro σv hσv y hyv hsin hle
        rcases lt_or_eq_of_le hle with h1 | h1
        · exact h1
        · exfalso
          have h2 : (Complex.exp ((φ : ℂ) * Complex.I) / discChart v y).im = 0 := by
            rcases mul_eq_zero.mp h1.symm with h3 | h3
            · rcases hσv with h4 | h4 <;> rw [h4] at h3 <;> norm_num at h3
            · exact h3
          rw [exp_div_im φ (discChart_ne_zero hyv)] at h2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · have h4 : ‖discChart v y‖ ≠ 0 :=
              norm_ne_zero_iff.mpr (discChart_ne_zero hyv)
            exact h4 (by rwa [inv_eq_zero] at h3)
          · exact hsin h3
      have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
        rw [hEnorm φ]
        linarith
      obtain ⟨y, hychart, -⟩ := chart_surj v hu1
      have hyd : dist v y < r' := by
        refine (dist_lt_iff_norm_chart hr').mpr ?_
        rw [hychart, hEnorm φ]
        linarith
      have hyk : y ∈ (e k • ·) '' dirichletDomain Γ τ₀ := by
        refine hfill k hkn y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₁pm k) _ (hWv (p k)) (fun h => hz1 hφw h) hc1k)
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₂pm k) _ (hWv k) (fun h => hz2 hφw h) hc2k)
      have hyj : y ∈ (e j • ·) '' dirichletDomain Γ τ₀ := by
        refine hfill j hjn y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₁pm j) _ (hWv (p j)) (fun h => hz3 hφw h) hc1j)
        · exact (hscale _ _ φ).2 (hstrict _ (hσ₂pm j) _ (hWv j) (fun h => hz4 hφw h) hc2j)
      have hyv : y ≠ v := by
        intro h0
        rw [h0, discChart_self] at hychart
        have h1 := congrArg norm hychart
        rw [norm_zero, hEnorm φ] at h1
        linarith
      have hmod : ¬ k ≡ j [MOD n] := by
        intro h0
        have hk' : k % n = k := Nat.mod_eq_of_lt hkn
        have hj' : j % n = j := Nat.mod_eq_of_lt hjn
        rw [Nat.ModEq, hk', hj'] at h0
        exact hkj h0
      rcases hTinter k j hmod y hyk hyj with h1 | h1 | h1
      · exact hyv h1
      · have h2 := ray_kill (hWv k) h1 hyv
        rw [hychart, mul_div_assoc, Complex.im_ofReal_mul] at h2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · linarith
        · rw [exp_div_im φ (discChart_ne_zero (hWv k))] at h3
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact norm_ne_zero_iff.mpr (discChart_ne_zero (hWv k))
              (by rwa [inv_eq_zero] at h4)
          · exact hz2 hφw h4
      · have h2 := ray_kill (hWv (p k)) h1 hyv
        rw [hychart, mul_div_assoc, Complex.im_ofReal_mul] at h2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · linarith
        · rw [exp_div_im φ (discChart_ne_zero (hWv (p k)))] at h3
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact norm_ne_zero_iff.mpr (discChart_ne_zero (hWv (p k)))
              (by rwa [inv_eq_zero] at h4)
          · exact hz1 hφw h4
    refine measure_mono_null hzero ?_
    have hfin4 : ∀ y : UpperHalfPlane, y ≠ v → ({φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        Real.sin (φ - Complex.arg (discChart v y)) = 0}).Finite := by
      intro y hy
      exact finite_sin_zero (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_ <;>
      exact Set.Finite.measure_zero (hfin4 _ (by first
        | exact hWv (p k) | exact hWv k | exact hWv (p j) | exact hWv j)) volume
  have hDirmeas : ∀ k : ℕ, MeasurableSet (Dir k) := by
    intro k
    have hc : ∀ u : ℂ, Continuous fun φ : ℝ =>
        (Complex.exp ((φ : ℂ) * Complex.I) / u).im := by
      intro u
      exact Complex.continuous_im.comp ((Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).div_const u)
    have h1 : Dir k = Set.Ico (-Real.pi) Real.pi ∩
        ({φ : ℝ | 0 ≤ σ₁ k *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W (p k))).im}
          ∩ {φ : ℝ | 0 ≤ σ₂ k *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart v (W k)).im}) := by
      ext φ
      simp only [hDirdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ico]
    rw [h1]
    refine measurableSet_Ico.inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
  have hEq2π : ∑ k ∈ Finset.range n, volume (Dir k) = ENNReal.ofReal (2 * Real.pi) := by
    have h1 : volume (⋃ k ∈ Finset.range n, Dir k)
        = ∑ k ∈ Finset.range n, volume (Dir k) := by
      refine measure_biUnion_finset₀ ?_ ?_
      · intro k hk j hj hkj
        exact hDirdisj k (Finset.mem_range.mp hk) j (Finset.mem_range.mp hj) hkj
      · intro k hk
        exact (hDirmeas k).nullMeasurableSet
    have h2 : volume (⋃ k ∈ Finset.range n, Dir k) = volume (Set.Ico (-Real.pi) Real.pi) := by
      apply le_antisymm
      · refine measure_mono (Set.iUnion₂_subset fun k hk => fun φ hφ => hφ.1)
      · exact measure_mono hDircov
    rw [← h1, h2, Real.volume_Ico]
    congr 1
    ring
  have hreal : ∑ k ∈ Finset.range n, sectorAngle v (W (p k)) (W k) = 2 * Real.pi := by
    have h1 : ENNReal.ofReal (∑ k ∈ Finset.range n, sectorAngle v (W (p k)) (W k))
        = ENNReal.ofReal (2 * Real.pi) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sectorAngle_nonneg v (W (p k)) (W k)]
      rw [← hEq2π]
      exact Finset.sum_congr rfl fun k _ => (hDirvol k).symm
    have h2 : 0 ≤ ∑ k ∈ Finset.range n, sectorAngle v (W (p k)) (W k) :=
      Finset.sum_nonneg fun k _ => sectorAngle_nonneg v (W (p k)) (W k)
    have h3 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    exact (ENNReal.ofReal_eq_ofReal_iff h2 h3).mp h1
  -- transport of angles along the subgroup action
  have hsect_smul : ∀ (γ : ↥Γ) (z w₁ w₂ : UpperHalfPlane),
      sectorAngle (γ • z) (γ • w₁) (γ • w₂) = sectorAngle z w₁ w₂ := by
    intro γ z w₁ w₂
    rw [Subgroup.smul_def, Subgroup.smul_def, Subgroup.smul_def]
    exact sectorAngle_smul _ z w₁ w₂
  have himg_one : ∀ S : Set UpperHalfPlane, ((1 : ↥Γ) • ·) '' S = S := by
    intro S
    rw [show (((1 : ↥Γ) • ·) : UpperHalfPlane → UpperHalfPlane) = id from
      funext fun x => one_smul _ x, Set.image_id]
  have hA₂rep : ∀ k : ℕ, dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k))
      = geodSeg ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) := by
    intro k
    have h1 := congrArg (fun S => ((e k)⁻¹ • ·) '' S) (hσ'eq k)
    simp only at h1
    rw [smul_smul_image, inv_mul_cancel, himg_one, subgroup_smul_geodSeg] at h1
    exact h1
  have hgmem : ∀ k : ℕ, (e k)⁻¹ • v ∈ MulAction.orbit Γ v ∩ polygonVertices Γ τ₀ :=
    fun k => ⟨MulAction.mem_orbit_iff.mpr ⟨(e k)⁻¹, rfl⟩,
      smul_mem_polygonVertices hv (hecon k)⟩
  have hαmatch : ∀ k : ℕ, α ((e k)⁻¹ • v) = sectorAngle v (W (p k)) (W k) := by
    intro k
    have hgvert : (e k)⁻¹ • v ∈ polygonVertices Γ τ₀ :=
      smul_mem_polygonVertices hv (hecon k)
    have hxkne : (e k)⁻¹ • v ≠ (e k)⁻¹ • W k := by
      intro h0
      exact hWv k (smul_left_cancel _ h0).symm
    have hxpkne : (e k)⁻¹ • v ≠ (e k)⁻¹ • W (p k) := by
      intro h0
      exact hWv (p k) (smul_left_cancel _ h0).symm
    have hA₁side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∈ polygonSides Γ τ₀ :=
      ⟨_, hadj k, rfl⟩
    have hA₂side : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) ∈ polygonSides Γ τ₀ :=
      ⟨_, hδ'elem k, rfl⟩
    have hendA₁ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)))
        ((e k)⁻¹ • v) := by
      rw [hWrep k]
      exact (isSegEndpoint_geodSeg_iff hxkne).mpr (Or.inl rfl)
    have hendA₂ : IsSegEndpoint (dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)))
        ((e k)⁻¹ • v) := by
      rw [hA₂rep k]
      exact (isSegEndpoint_geodSeg_iff hxpkne).mpr (Or.inl rfl)
    have hA12 : dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))
        ≠ dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) := by
      intro h0
      have h1 := smul_basepoint_eq_of_sideSet_eq hΓ hfree (hadj k) (hδ'elem k) h0
      have h2 := congrArg (e k • ·) h1
      simp only at h2
      rw [← mul_smul, ← mul_smul, mul_inv_cancel_left, mul_inv_cancel_left] at h2
      exact hmove_np k h2
    obtain ⟨t₁, ht₁, t₂, ht₂, ht12, hte₁, hte₂, htu⟩ :=
      exists_two_sides_at_vertex hΓ hfree hε hgap hdense hgvert
    obtain ⟨s₁', hs₁', s₂', hs₂', hne', he₁', he₂', w₁', hw₁', w₂', hw₂', hw₁v', hw₂v',
      hval⟩ := hα _ (hgmem k)
    have hmA₁ := htu _ hA₁side hendA₁
    have hmA₂ := htu _ hA₂side hendA₂
    have hm₁ := htu _ hs₁' he₁'
    have hm₂ := htu _ hs₂' he₂'
    have hcase : (s₁' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1)) ∧
        s₂' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k))) ∨
        (s₁' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (p k)) ∧
        s₂' = dirichletSideSet Γ τ₀ ((e k)⁻¹ * e (k + 1))) := by
      rcases hmA₁ with hA | hA <;> rcases hmA₂ with hB | hB <;>
        rcases hm₁ with hC | hC <;> rcases hm₂ with hD | hD <;>
        first
        | exact absurd (hA.trans hB.symm) hA12
        | exact absurd (hC.trans hD.symm) hne'
        | exact Or.inl ⟨hC.trans hA.symm, hD.trans hB.symm⟩
        | exact Or.inr ⟨hC.trans hB.symm, hD.trans hA.symm⟩
    have htransport : sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k)
        = sectorAngle v (W (p k)) (W k) := by
      have h1 := hsect_smul (e k) ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k)
      rw [smul_inv_smul, smul_inv_smul, smul_inv_smul] at h1
      exact h1.symm
    rcases hcase with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, hWrep k] at hw₁'
      rw [h₂, hA₂rep k] at hw₂'
      rw [hval, ← htransport]
      calc sectorAngle ((e k)⁻¹ • v) w₁' w₂'
          = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W k) w₂' :=
            sectorAngle_ray_congr hw₁' (right_mem_geodSeg _ _) hw₁v'
              (Ne.symm hxkne) w₂'
        _ = sectorAngle ((e k)⁻¹ • v) w₂' ((e k)⁻¹ • W k) := sectorAngle_comm _ _ _
        _ = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k) :=
            sectorAngle_ray_congr hw₂' (right_mem_geodSeg _ _) hw₂v'
              (Ne.symm hxpkne) _
    · rw [h₁, hA₂rep k] at hw₁'
      rw [h₂, hWrep k] at hw₂'
      rw [hval, ← htransport]
      calc sectorAngle ((e k)⁻¹ • v) w₁' w₂'
          = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) w₂' :=
            sectorAngle_ray_congr hw₁' (right_mem_geodSeg _ _) hw₁v'
              (Ne.symm hxpkne) w₂'
        _ = sectorAngle ((e k)⁻¹ • v) w₂' ((e k)⁻¹ • W (p k)) := sectorAngle_comm _ _ _
        _ = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W k) ((e k)⁻¹ • W (p k)) :=
            sectorAngle_ray_congr hw₂' (right_mem_geodSeg _ _) hw₂v'
              (Ne.symm hxkne) _
        _ = sectorAngle ((e k)⁻¹ • v) ((e k)⁻¹ • W (p k)) ((e k)⁻¹ • W k) :=
            sectorAngle_comm _ _ _
  have hfin : (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀).Finite :=
    (finite_polygonVertices hΓ hfree hε hgap hdense).subset Set.inter_subset_right
  rw [finsum_mem_eq_finite_toFinset_sum α hfin, ← hreal]
  refine (Finset.sum_bij (fun k _ => (e k)⁻¹ • v) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [Set.Finite.mem_toFinset]
    exact hgmem k
  · intro k₁ hk₁ k₂ hk₂ hkk
    simp only at hkk
    have h1 : (e k₂ * (e k₁)⁻¹) • v = v := by
      rw [mul_smul, hkk, smul_inv_smul]
    have h2 := hfree (e k₂ * (e k₁)⁻¹) ⟨v, h1⟩ (e k₁ • τ₀)
    rw [mul_smul, inv_smul_smul] at h2
    have h3 := hcent k₂ k₁ h2
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hk₂),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hk₁)] at h3
    exact h3.symm
  · intro b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨horb, hvert⟩ := hb
    obtain ⟨η, hη⟩ := MulAction.mem_orbit_iff.mp horb
    have hcon : η⁻¹ ∈ contactSet Γ τ₀ v := by
      rw [mem_contactSet_iff_mem_smul_dirichletDomain]
      refine ⟨η • v, ?_, ?_⟩
      · rw [hη]
        exact hvert.1
      · change η⁻¹ • η • v = v
        rw [inv_smul_smul]
    obtain ⟨k, ⟨hkn, hkc⟩, -⟩ := huniq η⁻¹ hcon
    refine ⟨k, Finset.mem_range.mpr hkn, ?_⟩
    change (e k)⁻¹ • v = b
    have h1 := inv_smul_eq_of_basepoint_eq hfree hkc v
    rw [inv_inv] at h1
    rw [← h1, hη]
  · intro k hk
    exact (hαmatch k).symm

set_option maxHeartbeats 400000 in
-- The class-partition bookkeeping over the vertex set elaborates several Finset partitions
-- in one declaration; the default heartbeat budget does not cover it.
/-- **Total angle sum**: the interior angles over all vertices of the polygon sum to
`2π c`. -/
theorem sum_interiorAngle_total (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : UpperHalfPlane → ℝ}
    (hα : ∀ v ∈ polygonVertices Γ τ₀, IsInteriorAngleAt Γ τ₀ v (α v)) :
    ∑ᶠ v ∈ polygonVertices Γ τ₀, α v
      = 2 * Real.pi * (polygonVertexClassCount Γ τ₀ : ℝ) := by
  classical
  have hVfin : (polygonVertices Γ τ₀).Finite :=
    finite_polygonVertices hΓ hfree hε hgap hdense
  have hCfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine (hVfin.image (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  set 𝒱 : Finset UpperHalfPlane := hVfin.toFinset with h𝒱
  set 𝒬 : Finset (Set UpperHalfPlane) := hCfin.toFinset with h𝒬
  have hCsub : ∀ C ∈ polygonVertexClasses Γ τ₀, C ⊆ polygonVertices Γ τ₀ := by
    rintro C ⟨v, hv, rfl⟩
    exact Set.inter_subset_right
  have hfilter : ∀ C ∈ 𝒬, (↑(𝒱.filter (· ∈ C)) : Set UpperHalfPlane) = C := by
    intro C hC
    have hCmem : C ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC
      exact hC
    ext w
    simp only [Finset.coe_filter, Set.mem_setOf_eq, h𝒱, Set.Finite.mem_toFinset]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hCsub C hCmem h1, h1⟩⟩
  have hbi : 𝒱 = 𝒬.biUnion (fun C => 𝒱.filter (· ∈ C)) := by
    ext w
    constructor
    · intro hw
      have hwV : w ∈ polygonVertices Γ τ₀ := by
        rw [h𝒱, Set.Finite.mem_toFinset] at hw
        exact hw
      have hC' : (MulAction.orbit Γ w ∩ polygonVertices Γ τ₀ : Set UpperHalfPlane) ∈ 𝒬 := by
        rw [h𝒬, Set.Finite.mem_toFinset]
        exact ⟨w, hwV, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨_, hC', ?_⟩
      have hgoal : w ∈ 𝒱 ∧ w ∈ (MulAction.orbit Γ w ∩ polygonVertices Γ τ₀ :
          Set UpperHalfPlane) := ⟨hw, MulAction.mem_orbit_self w, hwV⟩
      simp only [Finset.mem_filter]
      exact hgoal
    · intro hw
      obtain ⟨C, -, hwC⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.filter_subset _ _) hwC
  have hdisj : ∀ C ∈ 𝒬, ∀ C' ∈ 𝒬, C ≠ C' →
      Disjoint (𝒱.filter (· ∈ C)) (𝒱.filter (· ∈ C')) := by
    intro C hC C' hC' hne
    rw [Finset.disjoint_left]
    intro w hwC hwC'
    apply hne
    have h1' : w ∈ C := (Finset.mem_filter.mp hwC).2
    have h2' : w ∈ C' := (Finset.mem_filter.mp hwC').2
    have hCmem : C ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC
      exact hC
    have hC'mem : C' ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC'
      exact hC'
    obtain ⟨v₁, hv₁, rfl⟩ := hCmem
    obtain ⟨v₂, hv₂, rfl⟩ := hC'mem
    have h3 : MulAction.orbit Γ v₁ = MulAction.orbit Γ v₂ := by
      rw [← MulAction.orbit_eq_iff.mpr h1'.1, ← MulAction.orbit_eq_iff.mpr h2'.1]
    rw [h3]
  have hclass2π : ∀ C ∈ 𝒬, ∑ w ∈ 𝒱.filter (· ∈ C), α w = 2 * Real.pi := by
    intro C hC
    have hCmem : C ∈ polygonVertexClasses Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hC
      exact hC
    have hCC := hfilter C hC
    obtain ⟨vC, hvC, hCdef⟩ := hCmem
    have hCfin' : (MulAction.orbit Γ vC ∩ polygonVertices Γ τ₀).Finite :=
      hVfin.subset Set.inter_subset_right
    have h2 := sum_interiorAngle_vertexClass hΓ hfree hε hgap hdense hvC
      (fun v' hv' => hα v' hv'.2)
    rw [finsum_mem_eq_finite_toFinset_sum α hCfin'] at h2
    rw [← h2]
    apply Finset.sum_congr
    · apply Finset.coe_injective
      rw [hCC, Set.Finite.coe_toFinset, hCdef]
    · intro x hx
      rfl
  rw [finsum_mem_eq_finite_toFinset_sum α hVfin]
  have hfinal : ∑ w ∈ 𝒱, α w = ∑ C ∈ 𝒬, (2 * Real.pi) := by
    rw [hbi, Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl hclass2π
  rw [hfinal, Finset.sum_const, nsmul_eq_mul]
  have hcount : (polygonVertexClassCount Γ τ₀ : ℝ) = (𝒬.card : ℝ) := by
    rw [polygonVertexClassCount, ← Set.ncard_coe_finset 𝒬, h𝒬, Set.Finite.coe_toFinset]
  rw [hcount]
  ring

/-- The complete geodesic through two points, realized as a perpendicular bisector: mirror
pair, equidistance at both points, and the collinearity of any equidistant point. -/
theorem apex_line_functional {z x : UpperHalfPlane} (_hxz : x ≠ z) :
    ∃ P Q : UpperHalfPlane, P ≠ Q ∧ dist z P = dist z Q ∧ dist x P = dist x Q ∧
      ∀ w : UpperHalfPlane, dist w P = dist w Q → w ∈ geodSeg z x ∨
        x ∈ geodSeg z w ∨ z ∈ geodSeg w x := by
  obtain ⟨g, hgz, hgx⟩ := exists_verticalize z x
  have hpm : (0 : ℝ) < ((⟨1, 1⟩ : ℂ)).im := by norm_num
  have hpm' : (0 : ℝ) < ((⟨-1, 1⟩ : ℂ)).im := by norm_num
  set ptP : UpperHalfPlane := UpperHalfPlane.mk ⟨1, 1⟩ hpm with hptP
  set ptM : UpperHalfPlane := UpperHalfPlane.mk ⟨-1, 1⟩ hpm' with hptM
  have hPre : ptP.re = 1 := rfl
  have hPim : ptP.im = 1 := rfl
  have hMre : ptM.re = -1 := rfl
  have hMim : ptM.im = 1 := rfl
  have hJP : UpperHalfPlane.J • ptP = ptM :=
    ext_re_im (by rw [J_smul_re, hPre, hMre]) (by rw [J_smul_im, hPim, hMim])
  have hJM : UpperHalfPlane.J • ptM = ptP := by
    rw [← hJP, J_J]
  have hplus : ∀ τ : UpperHalfPlane, dist τ ptP ≤ dist τ ptM ↔ 0 ≤ τ.re := by
    intro τ
    have h1 := setOf_dist_le_eq_of_im_eq' (a := ptP) (b := ptM)
      (by rw [hPim, hMim]) (by rw [hPre, hMre]; norm_num)
    have h2 := Set.ext_iff.mp h1 τ
    simp only [Set.mem_setOf_eq, hPre, hMre] at h2
    rw [h2]
    norm_num
  have hminus : ∀ τ : UpperHalfPlane, dist τ ptM ≤ dist τ ptP ↔ τ.re ≤ 0 := by
    intro τ
    have e1 : dist τ ptM = dist (UpperHalfPlane.J • τ) ptP := by
      rw [← dist_J τ ptM, hJM]
    have e2 : dist τ ptP = dist (UpperHalfPlane.J • τ) ptM := by
      rw [← dist_J τ ptP, hJP]
    rw [e1, e2, hplus, J_smul_re]
    constructor <;> intro h <;> linarith
  have hchar : ∀ w : UpperHalfPlane,
      dist w (g⁻¹ • ptM) = dist w (g⁻¹ • ptP) ↔ (g • w).re = 0 := by
    intro w
    have e1 : dist w (g⁻¹ • ptM) = dist (g • w) ptM := by
      rw [← dist_smul g w (g⁻¹ • ptM), smul_inv_smul]
    have e2 : dist w (g⁻¹ • ptP) = dist (g • w) ptP := by
      rw [← dist_smul g w (g⁻¹ • ptP), smul_inv_smul]
    rw [e1, e2]
    constructor
    · intro h
      have h1 := (hminus (g • w)).mp h.le
      have h2 := (hplus (g • w)).mp h.ge
      linarith
    · intro h
      have h1 := (hminus (g • w)).mpr h.le
      have h2 := (hplus (g • w)).mpr h.ge
      linarith
  have hMP : ptM ≠ ptP := by
    intro h0
    have h1 := congrArg UpperHalfPlane.re h0
    rw [hMre, hPre] at h1
    norm_num at h1
  refine ⟨g⁻¹ • ptM, g⁻¹ • ptP, fun h0 => hMP (MulAction.injective g⁻¹ h0), ?_, ?_, ?_⟩
  · exact (hchar z).mpr hgz
  · exact (hchar x).mpr hgx
  · intro w hw
    have hgw : (g • w).re = 0 := (hchar w).mp hw
    have hvert : ∀ Y₁ Y₂ Y₃ : UpperHalfPlane, Y₁.re = 0 → Y₂.re = 0 → Y₃.re = 0 →
        min Y₁.im Y₂.im ≤ Y₃.im → Y₃.im ≤ max Y₁.im Y₂.im → Y₃ ∈ geodSeg Y₁ Y₂ := by
      intro Y₁ Y₂ Y₃ h₁ h₂ h₃ hlo hhi
      rw [geodSeg_vertical_eq (h₁.trans h₂.symm)]
      exact ⟨h₃.trans h₁.symm, hlo, hhi⟩
    have hpull : ∀ a b c : UpperHalfPlane, g • a ∈ geodSeg (g • b) (g • c) →
        a ∈ geodSeg b c := by
      intro a b c hmem
      rw [← smul_geodSeg] at hmem
      obtain ⟨y, hy, hya⟩ := hmem
      rw [MulAction.injective g hya] at hy
      exact hy
    rcases le_total (g • w).im (g • z).im with hWZ | hWZ <;>
      rcases le_total (g • w).im (g • x).im with hWX | hWX <;>
      rcases le_total (g • z).im (g • x).im with hZX | hZX
    · exact Or.inr (Or.inr (hpull z w x (hvert _ _ _ hgw hgx hgz
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith))))
    · exact Or.inr (Or.inl (hpull x z w (hvert _ _ _ hgz hgw hgx
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith))))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith)))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith)))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith)))
    · exact Or.inl (hpull w z x (hvert _ _ _ hgz hgx hgw
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith)))
    · exact Or.inr (Or.inl (hpull x z w (hvert _ _ _ hgz hgw hgx
        (by rw [min_def]; split_ifs; linarith) (by rw [max_def]; split_ifs; linarith))))
    · exact Or.inr (Or.inr (hpull z w x (hvert _ _ _ hgw hgx hgz
        (by rw [min_def]; split_ifs <;> linarith) (by rw [max_def]; split_ifs <;> linarith))))

/-- The sign functional of one boundary ray of a fan cone: the cone on the closed side,
radial segments through other side points strictly inside. -/
theorem cone_functional (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀)
    {a b : UpperHalfPlane} (hab : a ≠ b) (hseq : s = geodSeg a b) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart τ₀ b / discChart τ₀ a).im ∧
      (∀ w ∈ geodCone τ₀ s, 0 ≤ σ * (discChart τ₀ w / discChart τ₀ a).im) ∧
      (∀ x ∈ s, x ≠ a → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
        0 < σ * (discChart τ₀ w / discChart τ₀ a).im) := by
  have hτ₀s : τ₀ ∉ s := basepoint_notMem_side hΓ hfree hε hgap hdense hs
  have has : a ∈ s := hseq ▸ left_mem_geodSeg a b
  have hbs : b ∈ s := hseq ▸ right_mem_geodSeg a b
  have haτ : a ≠ τ₀ := fun h => hτ₀s (h ▸ has)
  have hxτ : ∀ x ∈ s, x ≠ τ₀ := fun x hx h => hτ₀s (h ▸ hx)
  have hfr : ∀ x ∈ s, x ∉ interior (dirichletDomain Γ τ₀) := by
    intro x hx hcon
    have h1 : x ∈ frontier (dirichletDomain Γ τ₀) := by
      rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
      exact ⟨s, hs, hx⟩
    rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at h1
    exact h1.2 hcon
  obtain ⟨γ, hγel, hsdef⟩ := hs
  have hbisτ : ∀ x ∈ s, ∀ y ∈ s, τ₀ ∉ geodSeg x y := by
    intro x hx y hy hτmem
    have h1 : ∀ w ∈ geodSeg x y, dist w τ₀ = dist w (γ • τ₀) := by
      intro w hw
      have hxb : dist x τ₀ = dist x (γ • τ₀) := (hsdef ▸ hx).2
      have hyb : dist y τ₀ = dist y (γ • τ₀) := (hsdef ▸ hy).2
      exact le_antisymm (geodSeg_subset_setOf_dist_le hxb.le hyb.le hw)
        (geodSeg_subset_setOf_dist_le hxb.ge hyb.ge hw)
    have h2 := h1 τ₀ hτmem
    rw [dist_self] at h2
    exact hγel.1 (dist_eq_zero.mp h2.symm).symm
  have hcollin : ∀ x ∈ s, x ≠ a →
      ¬(x ∈ geodSeg τ₀ a ∨ a ∈ geodSeg τ₀ x ∨ τ₀ ∈ geodSeg x a) := by
    rintro x hx hxa (h1 | h1 | h1)
    · exact hfr x hx (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain ⟨γ, hγel, hsdef⟩ has) h1 hxa)
    · exact hfr a has (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain ⟨γ, hγel, hsdef⟩ hx) h1 (Ne.symm hxa))
    · exact hbisτ x hx a has h1
  obtain ⟨P, Q, hPQ, hzeq, haeq, hline, hblt⟩ : ∃ P Q : UpperHalfPlane, P ≠ Q ∧
      dist τ₀ P = dist τ₀ Q ∧ dist a P = dist a Q ∧
      (∀ w : UpperHalfPlane, dist w P = dist w Q → w ∈ geodSeg τ₀ a ∨
        a ∈ geodSeg τ₀ w ∨ τ₀ ∈ geodSeg w a) ∧ dist b P < dist b Q := by
    obtain ⟨P, Q, hPQ, hzeq, haeq, hline⟩ := apex_line_functional haτ
    have hboff : dist b P ≠ dist b Q := by
      intro h0
      exact hcollin b hbs (Ne.symm hab) (hline b h0)
    rcases lt_or_gt_of_ne hboff with h1 | h1
    · exact ⟨P, Q, hPQ, hzeq, haeq, hline, h1⟩
    · exact ⟨Q, P, Ne.symm hPQ, hzeq.symm, haeq.symm,
        fun w hw => hline w hw.symm, h1⟩
  obtain ⟨g', ε', hε', hle, hge⟩ := bisector_normalizer hPQ
  obtain ⟨m, hm, hfeq, hflt⟩ := functional_sign hε' hle hge hzeq
  have hΨa0 : discChart τ₀ a ≠ 0 := discChart_ne_zero haτ
  have hratio := functional_ratio hε' hΨa0 (hfeq a haeq)
  set C : ℝ := ε' * (m * discChart τ₀ a).re with hCdef
  have hside_le : ∀ x ∈ s, dist x P ≤ dist x Q := by
    intro x hx
    rw [hseq] at hx
    exact geodSeg_subset_setOf_dist_le haeq.le hblt.le hx
  have hweakside : ∀ x ∈ s, 0 ≤ C * (discChart τ₀ x / discChart τ₀ a).im := by
    intro x hx
    rw [← hratio (discChart τ₀ x)]
    rcases lt_or_eq_of_le (hside_le x hx) with h1 | h1
    · exact (hflt x h1).le
    · exact (hfeq x h1).ge
  have hCb : 0 < C * (discChart τ₀ b / discChart τ₀ a).im := by
    rw [← hratio (discChart τ₀ b)]
    exact hflt b hblt
  have hCne : C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hCb
    exact lt_irrefl 0 hCb
  have hstrictside : ∀ x ∈ s, x ≠ a → 0 < C * (discChart τ₀ x / discChart τ₀ a).im := by
    intro x hx hxa
    rcases lt_or_eq_of_le (hweakside x hx) with h1 | h1
    · exact h1
    · exfalso
      have h2 : (discChart τ₀ x / discChart τ₀ a).im = 0 := by
        rcases mul_eq_zero.mp h1.symm with h3 | h3
        · exact absurd h3 hCne
        · exact h3
      have h3 : dist x P = dist x Q := by
        rcases lt_or_eq_of_le (hside_le x hx) with h4 | h4
        · exfalso
          have h5 := hflt x h4
          rw [hratio (discChart τ₀ x), h2, mul_zero] at h5
          exact lt_irrefl 0 h5
        · exact h4
      exact hcollin x hx hxa (hline x h3)
  have hconeval : ∀ w ∈ geodCone τ₀ s, w ≠ τ₀ → ∃ x ∈ s, ∃ t : ℝ, 0 < t ∧
      discChart τ₀ w = (t : ℂ) * discChart τ₀ x := by
    intro w hw hwτ
    obtain ⟨x, hxs, hwseg⟩ := mem_geodCone.mp hw
    obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hwseg hwτ
    exact ⟨x, hxs, t, ht, hchart⟩
  have hCcone : ∀ w ∈ geodCone τ₀ s, 0 ≤ C * (discChart τ₀ w / discChart τ₀ a).im := by
    intro w hw
    by_cases hwτ : w = τ₀
    · rw [hwτ, discChart_self, zero_div]
      simp
    · obtain ⟨x, hxs, t, ht, hchart⟩ := hconeval w hw hwτ
      rw [hchart, mul_div_assoc, Complex.im_ofReal_mul]
      nlinarith [hweakside x hxs, ht]
  have hCray : ∀ x ∈ s, x ≠ a → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
      0 < C * (discChart τ₀ w / discChart τ₀ a).im := by
    intro x hx hxa w hwseg hwτ
    obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hwseg hwτ
    rw [hchart, mul_div_assoc, Complex.im_ofReal_mul]
    nlinarith [hstrictside x hx hxa, ht]
  rcases lt_or_gt_of_ne hCne with hC1 | hC1
  · refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩
    · nlinarith [hCb]
    · intro w hw
      nlinarith [hCcone w hw]
    · intro x hx hxa w hw hwτ
      nlinarith [hCray x hx hxa w hw hwτ]
  · refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
    · nlinarith [hCb]
    · intro w hw
      nlinarith [hCcone w hw]
    · intro x hx hxa w hw hwτ
      nlinarith [hCray x hx hxa w hw hwτ]

set_option maxHeartbeats 400000 in
-- The fan assembly at the basepoint elaborates the cone functionals and the measure
-- bookkeeping in one declaration; the default heartbeat budget does not cover it.
/-- **Apex angle sum**: the apex angles at the basepoint of the cones of the fan sum to
`2π` — the cones partition a disk about the interior basepoint. -/
theorem sum_apexAngle_basepoint (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {β : Set UpperHalfPlane → ℝ}
    (hβ : ∀ s ∈ polygonSides Γ τ₀, IsApexAngleAt τ₀ s (β s)) :
    ∑ᶠ s ∈ polygonSides Γ τ₀, β s = 2 * Real.pi := by
  classical
  have hSfin : (polygonSides Γ τ₀).Finite := finite_polygonSides hΓ hfree hε hgap hdense
  have hepex : ∀ s ∈ polygonSides Γ τ₀, ∃ a b : UpperHalfPlane, a ≠ b ∧ s = geodSeg a b :=
    fun s hs => exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  choose! A B hAB hrep using hepex
  have hAmem : ∀ s ∈ polygonSides Γ τ₀, A s ∈ s := by
    intro s hs
    have h1 := left_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hBmem : ∀ s ∈ polygonSides Γ τ₀, B s ∈ s := by
    intro s hs
    have h1 := right_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hAτ : ∀ s ∈ polygonSides Γ τ₀, A s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hAmem s hs)
  have hBτ : ∀ s ∈ polygonSides Γ τ₀, B s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hBmem s hs)
  have hdA : ∀ s ∈ polygonSides Γ τ₀, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart τ₀ (B s) / discChart τ₀ (A s)).im ∧
      (∀ w ∈ geodCone τ₀ s, 0 ≤ σ * (discChart τ₀ w / discChart τ₀ (A s)).im) ∧
      (∀ x ∈ s, x ≠ A s → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
        0 < σ * (discChart τ₀ w / discChart τ₀ (A s)).im) := fun s hs =>
    cone_functional hΓ hfree hε hgap hdense hs (hAB s hs) (hrep s hs)
  have hdB : ∀ s ∈ polygonSides Γ τ₀, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart τ₀ (A s) / discChart τ₀ (B s)).im ∧
      (∀ w ∈ geodCone τ₀ s, 0 ≤ σ * (discChart τ₀ w / discChart τ₀ (B s)).im) ∧
      (∀ x ∈ s, x ≠ B s → ∀ w ∈ geodSeg τ₀ x, w ≠ τ₀ →
        0 < σ * (discChart τ₀ w / discChart τ₀ (B s)).im) := fun s hs =>
    cone_functional hΓ hfree hε hgap hdense hs (Ne.symm (hAB s hs))
      ((hrep s hs).trans (geodSeg_comm _ _))
  choose! σA hσApm hσAB hσAcone hσAray using hdA
  choose! σB hσBpm hσBA hσBcone hσBray using hdB
  have hβmatch : ∀ s ∈ polygonSides Γ τ₀, β s = sectorAngle τ₀ (A s) (B s) := by
    intro s hs
    obtain ⟨a', b', hab', hs'eq, hval⟩ := hβ s hs
    have hends : ∀ x : UpperHalfPlane, IsSegEndpoint s x → x = A s ∨ x = B s := by
      intro x hx
      rw [hrep s hs] at hx
      exact (isSegEndpoint_geodSeg_iff (hAB s hs)).mp hx
    have ha' : a' = A s ∨ a' = B s := by
      refine hends a' ?_
      rw [hs'eq]
      exact (isSegEndpoint_geodSeg_iff hab').mpr (Or.inl rfl)
    have hb' : b' = A s ∨ b' = B s := by
      refine hends b' ?_
      rw [hs'eq]
      exact (isSegEndpoint_geodSeg_iff hab').mpr (Or.inr rfl)
    rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2
    · exact absurd (h1.trans h2.symm) hab'
    · rw [hval, h1, h2]
    · rw [hval, h1, h2, sectorAngle_comm]
    · exact absurd (h1.trans h2.symm) hab'
  set r' : ℝ := min (ε / 2) 1 with hr'def
  have hr' : 0 < r' := lt_min (by linarith) one_pos
  have hr'1 : r' ≤ 1 := min_le_right _ _
  set sc : ℝ := Real.tanh (r' / 2) with hscdef
  have hsc0 : 0 < sc := by
    rw [hscdef, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hsc1 : sc < 1 := Real.tanh_lt_one _
  have hballC : ∀ y : UpperHalfPlane, dist τ₀ y < r' →
      ∃ s ∈ polygonSides Γ τ₀, y ∈ geodCone τ₀ s := by
    intro y hy
    have h1 : y ∈ dirichletDomain Γ τ₀ := by
      refine ball_subset_dirichletDomain hε hgap ?_
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    rw [dirichletDomain_eq_biUnion_geodCone hΓ hfree hε hgap hdense] at h1
    rw [Set.mem_iUnion₂] at h1
    obtain ⟨t, ht, hyt⟩ := h1
    exact ⟨t, ht, hyt⟩
  have hfillC : ∀ s ∈ polygonSides Γ τ₀, ∀ y₀ : UpperHalfPlane, dist τ₀ y₀ < r' →
      0 < σA s * (discChart τ₀ y₀ / discChart τ₀ (A s)).im →
      0 < σB s * (discChart τ₀ y₀ / discChart τ₀ (B s)).im →
      y₀ ∈ geodCone τ₀ s := by
    intro s hs y₀ hy₀r hy₀1 hy₀2
    set OS : Set ℂ := {x : ℂ | ‖x‖ < sc ∧
        0 < σA s * (x / discChart τ₀ (A s)).im ∧
        0 < σB s * (x / discChart τ₀ (B s)).im} with hOSdef
    set POS : Set UpperHalfPlane :=
      {w : UpperHalfPlane | dist τ₀ w < r' ∧ discChart τ₀ w ∈ OS} with hPOSdef
    have hchartmem : ∀ w : UpperHalfPlane, dist τ₀ w < r' →
        0 < σA s * (discChart τ₀ w / discChart τ₀ (A s)).im →
        0 < σB s * (discChart τ₀ w / discChart τ₀ (B s)).im → w ∈ POS := by
      intro w h1 h2 h3
      exact ⟨h1, (dist_lt_iff_norm_chart hr').mp h1, h2, h3⟩
    have hy₀POS : y₀ ∈ POS := hchartmem y₀ hy₀r hy₀1 hy₀2
    have hOSpre : IsPreconnected OS :=
      sector_preconnected' (hσApm s hs) (hσBpm s hs)
        (discChart_ne_zero (hAτ s hs)) (discChart_ne_zero (hBτ s hs))
        (hσAB s hs) (hσBA s hs)
    have hOSsub : OS ⊆ {u : ℂ | ‖u‖ < 1} := fun u hu => lt_trans hu.1 hsc1
    have hPOSimg : (fun w : UpperHalfPlane => (w : ℂ)) '' POS = (fun u : ℂ =>
        ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
          '' OS := by
      apply Set.Subset.antisymm
      · rintro x ⟨w, ⟨hwr, hwOS⟩, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj τ₀ (lt_trans hwOS.1 hsc1)
        have hww : w' = w := discChart_injective τ₀ hw'chart
        refine ⟨discChart τ₀ w, hwOS, ?_⟩
        change ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I
            * ((1 + discChart τ₀ w) / (1 - discChart τ₀ w)) = (w : ℂ)
        rw [← hw'coe, hww]
      · rintro x ⟨u, huOS, rfl⟩
        obtain ⟨w', hw'chart, hw'coe⟩ := chart_surj τ₀ (hOSsub huOS)
        refine ⟨w', ⟨?_, ?_⟩, ?_⟩
        · exact (dist_lt_iff_norm_chart hr').mpr (by rw [hw'chart]; exact huOS.1)
        · rw [hw'chart]
          exact huOS
        · change (w' : ℂ) = ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I
            * ((1 + u) / (1 - u))
          exact hw'coe
    have hFcont : ContinuousOn (fun u : ℂ =>
        ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
        {u : ℂ | ‖u‖ < 1} := by
      refine ContinuousOn.add continuousOn_const ?_
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.div ((continuous_const.add continuous_id).continuousOn)
        ((continuous_const.sub continuous_id).continuousOn) ?_
      intro u hu h0
      have h1 : u = 1 := by linear_combination -h0
      rw [Set.mem_setOf_eq, h1] at hu
      simp at hu
    have hPOSpre : IsPreconnected POS := by
      have h1 : IsPreconnected ((fun u : ℂ =>
          ((τ₀.re : ℝ) : ℂ) + ((τ₀.im : ℝ) : ℂ) * Complex.I * ((1 + u) / (1 - u)))
            '' OS) := hOSpre.image _ (hFcont.mono hOSsub)
      rw [← hPOSimg] at h1
      exact (UpperHalfPlane.isEmbedding_coe.toIsInducing.isPreconnected_image).mp h1
    have hPneτ : ∀ w ∈ POS, w ≠ τ₀ := by
      intro w hw h0
      have h1 := hw.2.2.1
      rw [h0, discChart_self, zero_div] at h1
      simp at h1
    have hPray : ∀ w ∈ POS, w ∉ geodSeg τ₀ (A s) ∧ w ∉ geodSeg τ₀ (B s) := by
      intro w hw
      constructor
      · intro h1
        have h2 := ray_kill (hAτ s hs) h1 (hPneτ w hw)
        have h3 := hw.2.2.1
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
      · intro h1
        have h2 := ray_kill (hBτ s hs) h1 (hPneτ w hw)
        have h3 := hw.2.2.2
        rw [h2, mul_zero] at h3
        exact lt_irrefl 0 h3
    set Acone : Set UpperHalfPlane := geodCone τ₀ s with hAconedef
    set Ccone : Set UpperHalfPlane := ⋃ t ∈ hSfin.toFinset.erase s, geodCone τ₀ t
      with hCconedef
    have hAcl : IsClosed Acone := isClosed_geodCone_side hΓ hfree hε hgap hdense hs
    have hCcl : IsClosed Ccone := by
      refine Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun t ht => ?_
      have ht' : t ∈ polygonSides Γ τ₀ := by
        have := Finset.mem_of_mem_erase ht
        rwa [Set.Finite.mem_toFinset] at this
      exact isClosed_geodCone_side hΓ hfree hε hgap hdense ht'
    have hPsub : POS ⊆ Acone ∪ Ccone := by
      intro w hw
      obtain ⟨t, ht, htw⟩ := hballC w hw.1
      by_cases hts : t = s
      · subst hts
        left
        exact htw
      · right
        refine Set.mem_biUnion (Finset.mem_erase.mpr ⟨hts, ?_⟩) htw
        rw [Set.Finite.mem_toFinset]
        exact ht
    have hPAC : ∀ w ∈ POS, w ∈ Acone → w ∈ Ccone → False := by
      intro w hwP hwA hwC
      rw [hCconedef, Set.mem_iUnion₂] at hwC
      obtain ⟨t, ht, htw⟩ := hwC
      have hts : t ≠ s := (Finset.mem_erase.mp ht).1
      have ht' : t ∈ polygonSides Γ τ₀ := by
        have := (Finset.mem_erase.mp ht).2
        rwa [Set.Finite.mem_toFinset] at this
      obtain ⟨q, ⟨hq1, hq2⟩, hwseg⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense
        hs ht' hwA htw (hPneτ w hwP)
      obtain ⟨-, hqend, -⟩ := shared_point_endpoint hΓ hfree hε hgap hdense hs ht'
        (fun h => hts h.symm) hq1 hq2
      have hq' : q = A s ∨ q = B s := by
        rw [hrep s hs] at hqend
        exact (isSegEndpoint_geodSeg_iff (hAB s hs)).mp hqend
      rcases hq' with h1 | h1
      · rw [h1] at hwseg
        exact (hPray w hwP).1 hwseg
      · rw [h1] at hwseg
        exact (hPray w hwP).2 hwseg
    set mid : UpperHalfPlane := geodInterp (A s) (B s) (1 / 2) with hmiddef
    have hmidmem : mid ∈ s := by
      have h1 := geodInterp_mem_geodSeg (A s) (B s) (t := 1 / 2) (by norm_num)
      rwa [← hrep s hs] at h1
    have hdAB : 0 < dist (A s) (B s) := dist_pos.mpr (hAB s hs)
    have hdAmid : dist (A s) mid = 1 / 2 * dist (A s) (B s) :=
      dist_geodInterp_left (A s) (B s) (by norm_num)
    have hmidA : mid ≠ A s := by
      intro h0
      rw [h0, dist_self] at hdAmid
      linarith
    have hmidB : mid ≠ B s := by
      intro h0
      rw [h0] at hdAmid
      linarith
    have hmidτ : mid ≠ τ₀ :=
      fun h => basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hmidmem)
    set d : ℝ := dist τ₀ mid with hddef
    have hd0 : 0 < d := dist_pos.mpr (Ne.symm hmidτ)
    set t : ℝ := r' / (2 * (d + 1)) with htdef
    have ht0 : 0 < t := by positivity
    have hthalf : t ≤ 1 / 2 := by
      rw [htdef, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set wt : UpperHalfPlane := geodInterp τ₀ mid t with hwtdef
    have hwtseg : wt ∈ geodSeg τ₀ mid :=
      geodInterp_mem_geodSeg _ _ ⟨ht0.le, by linarith⟩
    have hwtdist : dist τ₀ wt = t * d :=
      dist_geodInterp_left _ _ ⟨ht0.le, by linarith⟩
    have hwtτ : wt ≠ τ₀ := by
      intro h0
      rw [h0, dist_self] at hwtdist
      nlinarith
    have hwtr : dist τ₀ wt < r' := by
      rw [hwtdist, htdef]
      have h5 : d / (2 * (d + 1)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      have h6 := mul_le_mul_of_nonneg_left h5 hr'.le
      calc r' / (2 * (d + 1)) * d = r' * (d / (2 * (d + 1))) := by ring
        _ ≤ r' * (1 / 2) := h6
        _ < r' := by linarith
    have hwtPOS : wt ∈ POS :=
      hchartmem wt hwtr (hσAray s hs mid hmidmem hmidA wt hwtseg hwtτ)
        (hσBray s hs mid hmidmem hmidB wt hwtseg hwtτ)
    have hwtA : wt ∈ Acone := mem_geodCone.mpr ⟨mid, hmidmem, hwtseg⟩
    have hPC : ∀ w ∈ POS, w ∉ Ccone := by
      intro w hw hwC
      by_cases hwA : w ∈ Acone
      · exact hPAC w hw hwA hwC
      · rw [isPreconnected_closed_iff] at hPOSpre
        obtain ⟨z, hz⟩ := hPOSpre Acone Ccone hAcl hCcl hPsub ⟨wt, hwtPOS, hwtA⟩
          ⟨w, hw, hwC⟩
        exact hPAC z hz.1 hz.2.1 hz.2.2
    rcases hPsub hy₀POS with h1 | h1
    · exact h1
    · exact absurd h1 (hPC y₀ hy₀POS)
  set Dir : Set UpperHalfPlane → Set ℝ := fun s =>
      {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
      0 ≤ σA s * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (A s)).im ∧
      0 ≤ σB s * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (B s)).im}
    with hDirdef
  have hDirvol : ∀ s ∈ polygonSides Γ τ₀,
      volume (Dir s) = ENNReal.ofReal (sectorAngle τ₀ (A s) (B s)) := by
    intro s hs
    exact vol_arc (hσApm s hs) (hσBpm s hs) (discChart_ne_zero (hAτ s hs))
      (discChart_ne_zero (hBτ s hs)) (hσAB s hs) (hσBA s hs)
  have hsc2 : (0 : ℝ) < sc / 2 := by linarith
  have hEnorm : ∀ φ : ℝ, ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖
      = sc / 2 := by
    intro φ
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsc2]
  have hscale : ∀ (σv : ℝ) (u : ℂ) (φ : ℝ),
      (0 ≤ σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im ↔
        0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im) ∧
      (0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / u).im →
        0 < σv * (((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u).im) := by
    intro σv u φ
    have h1 : ((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) / u
        = ((sc / 2 : ℝ) : ℂ) * (Complex.exp ((φ : ℂ) * Complex.I) / u) :=
      mul_div_assoc _ _ _
    rw [h1, Complex.im_ofReal_mul]
    refine ⟨⟨fun h2 => by nlinarith, fun h2 => by nlinarith⟩, fun h2 => by nlinarith⟩
  have hDircov : Set.Ico (-Real.pi) Real.pi ⊆ ⋃ s ∈ hSfin.toFinset, Dir s := by
    intro φ hφ
    have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
      rw [hEnorm φ]
      linarith
    obtain ⟨y, hychart, -⟩ := chart_surj τ₀ hu1
    have hyd : dist τ₀ y < r' := by
      refine (dist_lt_iff_norm_chart hr').mpr ?_
      rw [hychart, hEnorm φ]
      linarith
    obtain ⟨s, hs, hyC⟩ := hballC y hyd
    have h₁ := hσAcone s hs y hyC
    have h₂ := hσBcone s hs y hyC
    rw [hychart] at h₁ h₂
    have hsmem : s ∈ hSfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact hs
    refine Set.mem_biUnion hsmem ⟨hφ, ?_, ?_⟩
    · exact ((hscale (σA s) (discChart τ₀ (A s)) φ).1).mp h₁
    · exact ((hscale (σB s) (discChart τ₀ (B s)) φ).1).mp h₂
  have hDirdisj : ∀ s ∈ polygonSides Γ τ₀, ∀ s' ∈ polygonSides Γ τ₀, s ≠ s' →
      volume (Dir s ∩ Dir s') = 0 := by
    intro s hs s' hs' hss
    have hzero : Dir s ∩ Dir s' ⊆
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (A s))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (B s))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (A s'))) = 0} ∪
        {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
          Real.sin (φ - Complex.arg (discChart τ₀ (B s'))) = 0} := by
      intro φ hφ
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and] at hcon
      obtain ⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩ := hcon
      obtain ⟨⟨hφw, hc1k, hc2k⟩, -, hc1j, hc2j⟩ := hφ
      have hstrict : ∀ (σv : ℝ), (σv = 1 ∨ σv = -1) → ∀ y : UpperHalfPlane, y ≠ τ₀ →
          Real.sin (φ - Complex.arg (discChart τ₀ y)) ≠ 0 →
          0 ≤ σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ y).im →
          0 < σv * (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ y).im := by
        intro σv hσv y hyv hsin hle
        rcases lt_or_eq_of_le hle with h1 | h1
        · exact h1
        · exfalso
          have h2 : (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ y).im = 0 := by
            rcases mul_eq_zero.mp h1.symm with h3 | h3
            · rcases hσv with h4 | h4 <;> rw [h4] at h3 <;> norm_num at h3
            · exact h3
          rw [exp_div_im φ (discChart_ne_zero hyv)] at h2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · exact norm_ne_zero_iff.mpr (discChart_ne_zero hyv)
              (by rwa [inv_eq_zero] at h3)
          · exact hsin h3
      have hu1 : ‖((sc / 2 : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ < 1 := by
        rw [hEnorm φ]
        linarith
      obtain ⟨y, hychart, -⟩ := chart_surj τ₀ hu1
      have hyd : dist τ₀ y < r' := by
        refine (dist_lt_iff_norm_chart hr').mpr ?_
        rw [hychart, hEnorm φ]
        linarith
      have hys : y ∈ geodCone τ₀ s := by
        refine hfillC s hs y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσApm s hs) _ (hAτ s hs)
            (fun h => hz1 hφw h) hc1k)
        · exact (hscale _ _ φ).2 (hstrict _ (hσBpm s hs) _ (hBτ s hs)
            (fun h => hz2 hφw h) hc2k)
      have hys' : y ∈ geodCone τ₀ s' := by
        refine hfillC s' hs' y hyd ?_ ?_ <;> rw [hychart]
        · exact (hscale _ _ φ).2 (hstrict _ (hσApm s' hs') _ (hAτ s' hs')
            (fun h => hz3 hφw h) hc1j)
        · exact (hscale _ _ φ).2 (hstrict _ (hσBpm s' hs') _ (hBτ s' hs')
            (fun h => hz4 hφw h) hc2j)
      have hyτ : y ≠ τ₀ := by
        intro h0
        rw [h0, discChart_self] at hychart
        have h1 := congrArg norm hychart
        rw [norm_zero, hEnorm φ] at h1
        linarith
      obtain ⟨q, ⟨hq1, hq2⟩, hyseg⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense
        hs hs' hys hys' hyτ
      obtain ⟨-, hqend, -⟩ := shared_point_endpoint hΓ hfree hε hgap hdense hs hs'
        hss hq1 hq2
      have hq' : q = A s ∨ q = B s := by
        rw [hrep s hs] at hqend
        exact (isSegEndpoint_geodSeg_iff (hAB s hs)).mp hqend
      have hkill : ∀ z : UpperHalfPlane, z ≠ τ₀ → y ∈ geodSeg τ₀ z →
          Real.sin (φ - Complex.arg (discChart τ₀ z)) = 0 := by
        intro z hzτ hyz
        have h2 := ray_kill hzτ hyz hyτ
        rw [hychart, mul_div_assoc, Complex.im_ofReal_mul] at h2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · linarith
        · rw [exp_div_im φ (discChart_ne_zero hzτ)] at h3
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd (by rwa [inv_eq_zero] at h4)
              (norm_ne_zero_iff.mpr (discChart_ne_zero hzτ))
          · exact h4
      rcases hq' with h1 | h1
      · rw [h1] at hyseg
        exact hz1 hφw (hkill (A s) (hAτ s hs) hyseg)
      · rw [h1] at hyseg
        exact hz2 hφw (hkill (B s) (hBτ s hs) hyseg)
    refine measure_mono_null hzero ?_
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_ <;>
      exact Set.Finite.measure_zero
        (finite_sin_zero (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)) volume
  have hDirmeas : ∀ s : Set UpperHalfPlane, MeasurableSet (Dir s) := by
    intro s
    have hc : ∀ u : ℂ, Continuous fun φ : ℝ =>
        (Complex.exp ((φ : ℂ) * Complex.I) / u).im := by
      intro u
      exact Complex.continuous_im.comp ((Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).div_const u)
    have h1 : Dir s = Set.Ico (-Real.pi) Real.pi ∩
        ({φ : ℝ | 0 ≤ σA s *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (A s)).im}
          ∩ {φ : ℝ | 0 ≤ σB s *
            (Complex.exp ((φ : ℂ) * Complex.I) / discChart τ₀ (B s)).im}) := by
      ext φ
      simp only [hDirdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ico]
    rw [h1]
    refine measurableSet_Ico.inter (MeasurableSet.inter ?_ ?_)
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
    · exact measurableSet_le measurable_const (continuous_const.mul (hc _)).measurable
  have hEq2π : ∑ s ∈ hSfin.toFinset, volume (Dir s) = ENNReal.ofReal (2 * Real.pi) := by
    have h1 : volume (⋃ s ∈ hSfin.toFinset, Dir s)
        = ∑ s ∈ hSfin.toFinset, volume (Dir s) := by
      refine measure_biUnion_finset₀ ?_ ?_
      · intro s hsm s' hsm' hss
        refine hDirdisj s ?_ s' ?_ hss
        · rwa [Finset.mem_coe, Set.Finite.mem_toFinset] at hsm
        · rwa [Finset.mem_coe, Set.Finite.mem_toFinset] at hsm'
      · intro s hsm
        exact (hDirmeas s).nullMeasurableSet
    have h2 : volume (⋃ s ∈ hSfin.toFinset, Dir s)
        = volume (Set.Ico (-Real.pi) Real.pi) := by
      apply le_antisymm
      · exact measure_mono (Set.iUnion₂_subset fun s hsm => fun φ hφ => hφ.1)
      · exact measure_mono hDircov
    rw [← h1, h2, Real.volume_Ico]
    congr 1
    ring
  have hreal : ∑ s ∈ hSfin.toFinset, sectorAngle τ₀ (A s) (B s) = 2 * Real.pi := by
    have h1 : ENNReal.ofReal (∑ s ∈ hSfin.toFinset, sectorAngle τ₀ (A s) (B s))
        = ENNReal.ofReal (2 * Real.pi) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun s _ => sectorAngle_nonneg τ₀ (A s) (B s),
        ← hEq2π]
      refine Finset.sum_congr rfl fun s hsm => ?_
      rw [hDirvol s (by rwa [Set.Finite.mem_toFinset] at hsm)]
    have h2 : 0 ≤ ∑ s ∈ hSfin.toFinset, sectorAngle τ₀ (A s) (B s) :=
      Finset.sum_nonneg fun s _ => sectorAngle_nonneg τ₀ (A s) (B s)
    exact (ENNReal.ofReal_eq_ofReal_iff h2 (by positivity)).mp h1
  rw [finsum_mem_eq_finite_toFinset_sum β hSfin, ← hreal]
  refine Finset.sum_congr rfl fun s hsm => ?_
  exact hβmatch s (by rwa [Set.Finite.mem_toFinset] at hsm)


section
open Real Set UpperHalfPlane
open scoped NNReal Pointwise

/-! ## The combinatorial Gauss–Bonnet formula -/

set_option maxHeartbeats 400000 in
-- The fan-additivity, triangle-formula, and incidence double-count assembly elaborates in
-- one declaration; the default heartbeat budget does not cover it.
/-- **Polygon Gauss–Bonnet**: the hyperbolic area of the Dirichlet polygon is
`2π (m - 1 - c)`, where `m` is the number of side pairs and `c` the number of vertex orbit
classes. Summing the angle-deficit areas of the `2m` cones of the fan: the `π`'s contribute
`2πm`, the apex angles contribute `-2π`, and the base angles reassemble along the vertices
into the interior angles, contributing `-2πc`. -/
theorem volume_dirichletDomain_gaussBonnet (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    volume (dirichletDomain Γ τ₀) = ENNReal.ofReal
      (2 * Real.pi * ((polygonSideCount Γ τ₀ : ℝ) - 1 - (polygonVertexClassCount Γ τ₀ : ℝ))) := by
  classical
  have hSfin : (polygonSides Γ τ₀).Finite := finite_polygonSides hΓ hfree hε hgap hdense
  have hVfin : (polygonVertices Γ τ₀).Finite :=
    finite_polygonVertices hΓ hfree hε hgap hdense
  set 𝒮 : Finset (Set UpperHalfPlane) := hSfin.toFinset with h𝒮
  set 𝒱 : Finset UpperHalfPlane := hVfin.toFinset with h𝒱
  have hmem𝒮 : ∀ {s}, s ∈ 𝒮 → s ∈ polygonSides Γ τ₀ := fun {s} hs => by
    rw [h𝒮, Set.Finite.mem_toFinset] at hs; exact hs
  have hepex : ∀ s ∈ polygonSides Γ τ₀, ∃ a b : UpperHalfPlane, a ≠ b ∧ s = geodSeg a b :=
    fun s hs => exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  choose! A B hAB hrep using hepex
  have hfan : volume (dirichletDomain Γ τ₀) = ∑ s ∈ 𝒮, volume (geodCone τ₀ s) := by
    rw [dirichletDomain_eq_biUnion_geodCone hΓ hfree hε hgap hdense, ← hSfin.coe_toFinset,
      ← h𝒮, Finset.set_biUnion_coe]
    refine measure_biUnion_finset₀ ?_ ?_
    · intro s hs s' hs' hne
      exact volume_geodCone_inter_eq_zero hΓ hfree hε hgap hdense
        (hmem𝒮 (Finset.mem_coe.mp hs)) (hmem𝒮 (Finset.mem_coe.mp hs')) hne
    · intro s hs
      exact (isClosed_geodCone_side hΓ hfree hε hgap hdense
        (hmem𝒮 hs)).measurableSet.nullMeasurableSet
  have hAmem : ∀ s ∈ polygonSides Γ τ₀, A s ∈ s := by
    intro s hs
    have h1 := left_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hBmem : ∀ s ∈ polygonSides Γ τ₀, B s ∈ s := by
    intro s hs
    have h1 := right_mem_geodSeg (A s) (B s)
    rwa [← hrep s hs] at h1
  have hAτ : ∀ s ∈ polygonSides Γ τ₀, A s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hAmem s hs)
  have hBτ : ∀ s ∈ polygonSides Γ τ₀, B s ≠ τ₀ := fun s hs h =>
    basepoint_notMem_side hΓ hfree hε hgap hdense hs (h ▸ hBmem s hs)
  have htri : ∀ s ∈ 𝒮, volume (geodCone τ₀ s) = ENNReal.ofReal
      (π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
        - sectorAngle (B s) τ₀ (A s)) := by
    intro s hs
    have hsP := hmem𝒮 hs
    conv_lhs => rw [hrep s hsP]
    exact volume_hyperbolicTriangle τ₀ (A s) (B s) (hAτ s hsP).symm (hBτ s hsP).symm
      (hAB s hsP)
  have hd0 : ∀ s ∈ 𝒮, 0 ≤ π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
      - sectorAngle (B s) τ₀ (A s) := fun s hs =>
    deficit_nonneg τ₀ (A s) (B s) (hAτ s (hmem𝒮 hs)).symm (hBτ s (hmem𝒮 hs)).symm
      (hAB s (hmem𝒮 hs))
  have hsum : volume (dirichletDomain Γ τ₀) = ENNReal.ofReal
      (∑ s ∈ 𝒮, (π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
        - sectorAngle (B s) τ₀ (A s))) := by
    rw [hfan, Finset.sum_congr rfl htri, ENNReal.ofReal_sum_of_nonneg hd0]
  have hcard : 𝒮.card = 2 * polygonSideCount Γ τ₀ := by
    rw [h𝒮, ← Set.ncard_eq_toFinset_card _ hSfin]
    exact ncard_polygonSides hΓ hfree hε hgap hdense
  have happex : ∑ s ∈ 𝒮, sectorAngle τ₀ (A s) (B s) = 2 * π := by
    have h := sum_apexAngle_basepoint hΓ hfree hε hgap hdense
      (β := fun s => sectorAngle τ₀ (A s) (B s))
      (fun s hs => ⟨A s, B s, hAB s hs, hrep s hs, rfl⟩)
    rwa [finsum_mem_eq_finite_toFinset_sum _ hSfin, ← h𝒮] at h
  have hbase2 : ∀ s ∈ polygonSides Γ τ₀,
      𝒱.filter (fun v => IsSegEndpoint s v) = {A s, B s} := by
    intro s hsP
    have hendA : IsSegEndpoint s (A s) := by
      have h := (isSegEndpoint_geodSeg_iff (hAB s hsP)).mpr (Or.inl rfl)
      rwa [← hrep s hsP] at h
    have hendB : IsSegEndpoint s (B s) := by
      have h := (isSegEndpoint_geodSeg_iff (hAB s hsP)).mpr (Or.inr rfl)
      rwa [← hrep s hsP] at h
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hend⟩
      rw [hrep s hsP] at hend
      exact (isSegEndpoint_geodSeg_iff (hAB s hsP)).mp hend
    · rintro (rfl | rfl)
      · refine ⟨?_, hendA⟩
        rw [h𝒱, Set.Finite.mem_toFinset]
        exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hsP hendA
      · refine ⟨?_, hendB⟩
        rw [h𝒱, Set.Finite.mem_toFinset]
        exact mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hsP hendB
  have hbases : ∀ s ∈ 𝒮, sectorAngle (A s) τ₀ (B s) + sectorAngle (B s) τ₀ (A s)
      = ∑ v ∈ 𝒱.filter (fun v => IsSegEndpoint s v),
          (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s)) := by
    intro s hs
    have hsP := hmem𝒮 hs
    rw [hbase2 s hsP, Finset.sum_insert (by
        simp only [Finset.mem_singleton]; exact hAB s hsP), Finset.sum_singleton,
      if_pos rfl, if_neg (Ne.symm (hAB s hsP))]
  have hswap : ∑ s ∈ 𝒮, ∑ v ∈ 𝒱.filter (fun v => IsSegEndpoint s v),
      (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))
      = ∑ v ∈ 𝒱, ∑ s ∈ 𝒮.filter (fun s => IsSegEndpoint s v),
          (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s)) := by
    simp_rw [Finset.sum_filter]
    exact Finset.sum_comm
  have hα : ∀ v ∈ polygonVertices Γ τ₀, IsInteriorAngleAt Γ τ₀ v
      (∑ s ∈ 𝒮.filter (fun s => IsSegEndpoint s v),
        (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))) := by
    intro v hv
    obtain ⟨s₁, hs₁, s₂, hs₂, hne, he₁, he₂, huniq⟩ :=
      exists_two_sides_at_vertex hΓ hfree hε hgap hdense hv
    have hfe : 𝒮.filter (fun s => IsSegEndpoint s v) = {s₁, s₂} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hsS, hend⟩
        exact huniq s (hmem𝒮 hsS) hend
      · rintro (rfl | rfl)
        · refine ⟨?_, he₁⟩
          rw [h𝒮, Set.Finite.mem_toFinset]
          exact hs₁
        · refine ⟨?_, he₂⟩
          rw [h𝒮, Set.Finite.mem_toFinset]
          exact hs₂
    have hother : ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v → ∃ w ∈ s, w ≠ v ∧
        (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))
          = sectorAngle v τ₀ w := by
      intro s hsP hend
      have hcase : v = A s ∨ v = B s := by
        rw [hrep s hsP] at hend
        exact (isSegEndpoint_geodSeg_iff (hAB s hsP)).mp hend
      rcases hcase with hva | hvb
      · refine ⟨B s, hBmem s hsP, ?_, by rw [if_pos hva]⟩
        rw [hva]
        exact Ne.symm (hAB s hsP)
      · have hvA : v ≠ A s := by
          rw [hvb]
          exact Ne.symm (hAB s hsP)
        refine ⟨A s, hAmem s hsP, ?_, by rw [if_neg hvA]⟩
        rw [hvb]
        exact hAB s hsP
    obtain ⟨w₁, hw₁s, hw₁v, hb₁⟩ := hother s₁ hs₁ he₁
    obtain ⟨w₂, hw₂s, hw₂v, hb₂⟩ := hother s₂ hs₂ he₂
    refine ⟨s₁, hs₁, s₂, hs₂, hne, he₁, he₂, w₁, hw₁s, w₂, hw₂s, hw₁v, hw₂v, ?_⟩
    rw [hfe, Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hne),
      Finset.sum_singleton, hb₁, hb₂,
      sectorAngle_eq_add_basepoint hΓ hfree hε hgap hdense hv hs₁ hs₂ hne he₁ he₂
        hw₁s hw₂s hw₁v hw₂v, sectorAngle_comm v w₁ τ₀]
  have hbtotal : ∑ v ∈ 𝒱, ∑ s ∈ 𝒮.filter (fun s => IsSegEndpoint s v),
      (if v = A s then sectorAngle v τ₀ (B s) else sectorAngle v τ₀ (A s))
      = 2 * π * (polygonVertexClassCount Γ τ₀ : ℝ) := by
    have h := sum_interiorAngle_total hΓ hfree hε hgap hdense hα
    rwa [finsum_mem_eq_finite_toFinset_sum _ hVfin, ← h𝒱] at h
  rw [hsum]
  congr 1
  have e1 : ∑ s ∈ 𝒮, (π - sectorAngle τ₀ (A s) (B s) - sectorAngle (A s) τ₀ (B s)
      - sectorAngle (B s) τ₀ (A s))
      = ∑ s ∈ 𝒮, π - ∑ s ∈ 𝒮, sectorAngle τ₀ (A s) (B s)
        - ∑ s ∈ 𝒮, (sectorAngle (A s) τ₀ (B s) + sectorAngle (B s) τ₀ (A s)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [e1, Finset.sum_const, hcard, happex, Finset.sum_congr rfl hbases, hswap, hbtotal]
  ring

/-- **Quantization**: the area of the Dirichlet polygon is a positive integer multiple of
`2π`. -/
theorem volume_dirichletDomain_quantized (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ k : ℕ, 1 ≤ k ∧
      volume (dirichletDomain Γ τ₀) = ENNReal.ofReal (2 * Real.pi * (k : ℝ)) := by
  have hGB := volume_dirichletDomain_gaussBonnet hΓ hfree hε hgap hdense
  have hpos : 0 < volume (dirichletDomain Γ τ₀) :=
    lt_of_lt_of_le (volume_ball_pos τ₀ (half_pos hε))
      (measure_mono (ball_subset_dirichletDomain hε hgap))
  rw [hGB] at hpos
  have hlt : 0 < 2 * Real.pi * ((polygonSideCount Γ τ₀ : ℝ) - 1
      - (polygonVertexClassCount Γ τ₀ : ℝ)) := ENNReal.ofReal_pos.mp hpos
  have hgtR : (polygonVertexClassCount Γ τ₀ : ℝ) + 1 < (polygonSideCount Γ τ₀ : ℝ) := by
    nlinarith [Real.pi_pos]
  have hgtN : polygonVertexClassCount Γ τ₀ + 1 < polygonSideCount Γ τ₀ := by
    exact_mod_cast hgtR
  refine ⟨polygonSideCount Γ τ₀ - 1 - polygonVertexClassCount Γ τ₀, by omega, ?_⟩
  rw [hGB]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]

end

end RiemannDynamics
