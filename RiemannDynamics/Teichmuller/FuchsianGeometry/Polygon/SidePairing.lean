/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Polygon.Fan

/-!
# The Dirichlet polygon: the side pairing and the planar angle toolkit

* The side pairing is a fixed-point-free involution (`dirichletSideSet_inv_ne`), and the
  side count is realized (`ncard_polygonSides`).
* Planar tier: circle directions, sine windows, and arc measures for angles between
  nonzero complex directions (`sin_arg_div`, `sector_eq_polar`).
* Dictionary tier: the disc frame as a homeomorphic chart with a `tanh` radius law
  (`dist_lt_iff_norm_chart`).
* Assembly helpers: ray order, ray-independence of angles, and side transport across the
  pairing (`ray_order`).
-/

open MeasureTheory
open scoped ENNReal MatrixGroups

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## The side pairing is a fixed-point-free involution -/

/-- No side is paired with itself: a self-paired side forces `γ² • τ₀ = τ₀`, so `γ²` acts
trivially, and `γ² = 1` gives `γ = ±1` while `γ² = -1` gives a zero trace, an elliptic
element with a fixed point — both excluded. -/
theorem dirichletSideSet_inv_ne (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {γ : ↥Γ} (h : IsSideElement Γ τ₀ γ) :
    dirichletSideSet Γ τ₀ γ⁻¹ ≠ dirichletSideSet Γ τ₀ γ := by
  intro heq
  have h1 : γ⁻¹ • τ₀ = γ • τ₀ := smul_basepoint_eq_of_sideSet_eq hΓ hfree h.inv h heq
  have h2 : (γ * γ) • τ₀ = τ₀ := by
    rw [mul_smul, ← h1, smul_inv_smul]
  have h3 : ∀ τ' : UpperHalfPlane, (γ * γ) • τ' = τ' := hfree (γ * γ) ⟨τ₀, h2⟩
  have h4 : ∀ τ' : UpperHalfPlane,
      ((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ' = τ' := by
    intro τ'
    rw [← Subgroup.smul_def]
    exact h3 τ'
  have hcoe : ((γ * γ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      = (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    rfl
  have htriv : γ • τ₀ ≠ τ₀ := h.1
  rcases (smul_id_iff_pm_one _).mp h4 with h5 | h5
  · -- `γ² = 1`: then `γ = ±1` acts trivially, contradicting the side element moving `τ₀`.
    have h6 : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← hcoe]
      exact h5
    have h7 := (smul_eq_self_of_pm_one _ (eq_pm_one_of_sq_eq_one _ h6)).1 τ₀
    rw [← Subgroup.smul_def] at h7
    exact htriv h7
  · -- `γ² = -1`: elliptic, with an interior fixed point; freeness makes `γ` trivial.
    have h6 : ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← hcoe]
      exact h5
    obtain ⟨τf, hτf⟩ := exists_fixed_of_sq_eq_neg_one _ h6
    have h7 : γ • τf = τf := by
      rw [Subgroup.smul_def]
      exact hτf
    exact htriv (hfree γ ⟨τf, h7⟩ τ₀)

/-- Equal basepoint images give equal inverse side sets. -/
theorem sideSet_inv_congr
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀) :
    dirichletSideSet Γ τ₀ γ⁻¹ = dirichletSideSet Γ τ₀ δ⁻¹ :=
  sideSet_eq_of_basepoint_eq (inv_smul_eq_of_basepoint_eq hfree h τ₀)

/-- Each side pair is contained in the side set. -/
theorem pair_subset_sides {P : Set (Set UpperHalfPlane)}
    (hP : P ∈ polygonSidePairs Γ τ₀) : P ⊆ polygonSides Γ τ₀ := by
  obtain ⟨γ, hγ, rfl⟩ := hP
  rintro s (rfl | hs)
  · exact ⟨γ, hγ, rfl⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨γ⁻¹, hγ.inv, rfl⟩

/-- The side pairs are finitely many. -/
theorem finite_polygonSidePairs (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSidePairs Γ τ₀).Finite :=
  ((finite_polygonSides hΓ hfree hε hgap hdense).finite_subsets).subset
    fun _ hP => pair_subset_sides hP

/-- Two side pairs sharing a side coincide. -/
theorem pair_eq_of_shared (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ) (hδ : IsSideElement Γ τ₀ δ)
    {s : Set UpperHalfPlane}
    (hs₁ : s ∈ ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} :
      Set (Set UpperHalfPlane)))
    (hs₂ : s ∈ ({dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} :
      Set (Set UpperHalfPlane))) :
    ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} := by
  rcases hs₁ with rfl | hs₁
  · rcases hs₂ with heq | hs₂
    · have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ heq
      rw [sideSet_eq_of_basepoint_eq hbase, sideSet_inv_congr hfree hbase]
    · rw [Set.mem_singleton_iff] at hs₂
      have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ.inv hs₂
      have hbase' : γ⁻¹ • τ₀ = δ • τ₀ := by
        have h1 := inv_smul_eq_of_basepoint_eq hfree hbase τ₀
        rwa [inv_inv] at h1
      rw [sideSet_eq_of_basepoint_eq hbase, sideSet_eq_of_basepoint_eq hbase',
        Set.pair_comm]
  · rw [Set.mem_singleton_iff] at hs₁
    subst hs₁
    rcases hs₂ with heq | hs₂
    · have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ.inv hδ heq
      have hbase' : γ • τ₀ = δ⁻¹ • τ₀ := by
        have h1 := inv_smul_eq_of_basepoint_eq hfree hbase τ₀
        rwa [inv_inv] at h1
      rw [sideSet_eq_of_basepoint_eq hbase, sideSet_eq_of_basepoint_eq hbase',
        Set.pair_comm]
    · rw [Set.mem_singleton_iff] at hs₂
      have hbase := smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ.inv hδ.inv hs₂
      have hbase' : γ • τ₀ = δ • τ₀ := by
        have h1 := inv_smul_eq_of_basepoint_eq hfree hbase τ₀
        rwa [inv_inv, inv_inv] at h1
      rw [sideSet_eq_of_basepoint_eq hbase', sideSet_inv_congr hfree hbase']

/-- The polygon has `2m` sides: the fixed-point-free pairing matches the sides in `m`
two-element pairs. -/
theorem ncard_polygonSides (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    (polygonSides Γ τ₀).ncard = 2 * polygonSideCount Γ τ₀ := by
  classical
  have hSfin := finite_polygonSides hΓ hfree hε hgap hdense
  have hPfin := finite_polygonSidePairs hΓ hfree hε hgap hdense
  set 𝒮 : Finset (Set UpperHalfPlane) := hSfin.toFinset with h𝒮
  set 𝒬 : Finset (Set (Set UpperHalfPlane)) := hPfin.toFinset with h𝒬
  have hfilter : ∀ P ∈ 𝒬, (↑(𝒮.filter (· ∈ P)) : Set (Set UpperHalfPlane)) = P := by
    intro P hP
    have hPmem : P ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hP
      exact hP
    ext s
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, h𝒮, Set.Finite.mem_toFinset]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨pair_subset_sides hPmem h1, h1⟩⟩
  have hcard2 : ∀ P ∈ 𝒬, (𝒮.filter (· ∈ P)).card = 2 := by
    intro P hP
    have hPmem : P ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hP
      exact hP
    obtain ⟨γ, hγ, hPdef⟩ := hPmem
    rw [← Set.ncard_coe_finset, hfilter P hP, hPdef]
    exact Set.ncard_pair
      (Ne.symm (dirichletSideSet_inv_ne hΓ hfree hε hgap hdense hγ))
  have hbi : 𝒮 = 𝒬.biUnion (fun P => 𝒮.filter (· ∈ P)) := by
    ext s
    constructor
    · intro hs
      have hsS : s ∈ polygonSides Γ τ₀ := by
        rw [h𝒮, Set.Finite.mem_toFinset] at hs
        exact hs
      obtain ⟨γ, hγ, hsdef⟩ := hsS
      have hQ' : ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} :
          Set (Set UpperHalfPlane)) ∈ 𝒬 := by
        rw [h𝒬, Set.Finite.mem_toFinset]
        exact ⟨γ, hγ, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨_, hQ', ?_⟩
      have hgoal : s ∈ 𝒮 ∧ s ∈ ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} :
          Set (Set UpperHalfPlane)) := ⟨hs, by rw [hsdef]; exact Set.mem_insert _ _⟩
      simp only [Finset.mem_filter]
      exact hgoal
    · intro hs
      obtain ⟨P, -, hsP⟩ := Finset.mem_biUnion.mp hs
      exact (Finset.filter_subset _ _) hsP
  have hdisj : ∀ P ∈ 𝒬, ∀ Q ∈ 𝒬, P ≠ Q →
      Disjoint (𝒮.filter (· ∈ P)) (𝒮.filter (· ∈ Q)) := by
    intro P hP Q hQ hPQ
    rw [Finset.disjoint_left]
    intro s hsP hsQ
    apply hPQ
    have hPmem : P ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hP
      exact hP
    have hQmem : Q ∈ polygonSidePairs Γ τ₀ := by
      rw [h𝒬, Set.Finite.mem_toFinset] at hQ
      exact hQ
    obtain ⟨γ, hγ, hPdef⟩ := hPmem
    obtain ⟨δ, hδ, hQdef⟩ := hQmem
    have h1 : s ∈ P := (Finset.mem_filter.mp hsP).2
    have h2 : s ∈ Q := (Finset.mem_filter.mp hsQ).2
    rw [hPdef] at h1 ⊢
    rw [hQdef] at h2 ⊢
    exact pair_eq_of_shared hΓ hfree hγ hδ h1 h2
  have e1 : (polygonSides Γ τ₀).ncard = 𝒮.card := by
    rw [← Set.ncard_coe_finset 𝒮, h𝒮, Set.Finite.coe_toFinset]
  have e2 : polygonSideCount Γ τ₀ = 𝒬.card := by
    rw [polygonSideCount, ← Set.ncard_coe_finset 𝒬, h𝒬, Set.Finite.coe_toFinset]
  rw [e1, e2, hbi, Finset.card_biUnion hdisj, Finset.sum_congr rfl hcard2,
    Finset.sum_const, smul_eq_mul, mul_comm]

/-- The polygon has at least one side. -/
theorem exists_polygonSide (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ s, s ∈ polygonSides Γ τ₀ := by
  obtain ⟨y, hy⟩ := exists_notMem_dirichletDomain hdense
  obtain ⟨w, -, hwfr⟩ := exists_frontier_mem_geodSeg basepoint_mem_dirichletDomain hy
  rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense] at hwfr
  obtain ⟨s, hs, -⟩ := hwfr
  exact ⟨s, hs⟩

/-- The polygon has at least one side pair: the orbit of the basepoint is dense, so the
group acts nontrivially and the domain is a proper subset of the plane. -/
theorem polygonSideCount_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    0 < polygonSideCount Γ τ₀ := by
  obtain ⟨s, hs⟩ := exists_polygonSide hΓ hfree hε hgap hdense
  obtain ⟨γ, hγ, -⟩ := hs
  rw [polygonSideCount]
  rw [Set.ncard_pos (finite_polygonSidePairs hΓ hfree hε hgap hdense)]
  exact ⟨_, γ, hγ, rfl⟩

/-- The polygon has at least one vertex class: the compact domain has a frontier, the
frontier is a union of segments, and segments have endpoints. -/
theorem polygonVertexClassCount_pos (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    0 < polygonVertexClassCount Γ τ₀ := by
  obtain ⟨s, hs⟩ := exists_polygonSide hΓ hfree hε hgap hdense
  obtain ⟨a, b, hab, hseq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  have hend : IsSegEndpoint s a := by
    rw [hseq]
    exact (isSegEndpoint_geodSeg_iff hab).mpr (Or.inl rfl)
  have hav : a ∈ polygonVertices Γ τ₀ :=
    mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs hend
  have hfin : (polygonVertexClasses Γ τ₀).Finite := by
    refine ((finite_polygonVertices hΓ hfree hε hgap hdense).image
      (fun v => MulAction.orbit Γ v ∩ polygonVertices Γ τ₀)).subset ?_
    rintro C ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  rw [polygonVertexClassCount, Set.ncard_pos hfin]
  exact ⟨_, a, hav, rfl⟩

/-! ## Planar tier: circle directions, sine windows, and arc measures -/

/-- The imaginary part of a rotated unit direction over a nonzero complex number. -/
theorem exp_div_im (φ : ℝ) {u : ℂ} (_hu : u ≠ 0) :
    (Complex.exp ((φ : ℂ) * Complex.I) / u).im
      = ‖u‖⁻¹ * Real.sin (φ - Complex.arg u) := by
  have h1 : Complex.exp ((φ : ℂ) * Complex.I) / Complex.exp ((Complex.arg u : ℂ) * Complex.I)
      = Complex.exp (((φ - Complex.arg u : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  calc (Complex.exp ((φ : ℂ) * Complex.I) / u).im
      = (Complex.exp ((φ : ℂ) * Complex.I)
          / ((‖u‖ : ℂ) * Complex.exp ((Complex.arg u : ℂ) * Complex.I))).im := by
        rw [Complex.norm_mul_exp_arg_mul_I u]
    _ = (Complex.exp (((φ - Complex.arg u : ℝ) : ℂ) * Complex.I) / ((‖u‖ : ℝ) : ℂ)).im := by
        rw [div_mul_eq_div_div_swap, h1]
    _ = ‖u‖⁻¹ * Real.sin (φ - Complex.arg u) := by
        rw [div_ofReal_im, Complex.exp_ofReal_mul_I_im]
        ring

/-- The sign data of a direction pair against a nonzero complex number. -/
theorem div_im_sign {x u : ℂ} (hu : u ≠ 0) (_hx : x ≠ 0) :
    (x / u).im = ‖x‖ * (‖u‖⁻¹ * Real.sin (Complex.arg x - Complex.arg u)) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_div_assoc, Complex.mul_im, exp_div_im _ hu, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The closed sine window on one period: the two sine sign conditions carve the arc from
`0` to `δ`. -/
theorem sin_window_weak {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ < Real.pi) :
    {ψ : ℝ | ψ ∈ Set.Ico 0 (2 * Real.pi) ∧ 0 ≤ Real.sin ψ ∧ Real.sin (ψ - δ) ≤ 0}
      = Set.Icc 0 δ := by
  have hπ := Real.pi_pos
  ext ψ
  simp only [Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h0, h2π⟩, hs1, hs2⟩
    refine ⟨h0, ?_⟩
    by_contra hcon
    have hcon' : δ < ψ := not_le.mp hcon
    rcases le_or_gt ψ Real.pi with hψπ | hψπ
    · have h1 : 0 < Real.sin (ψ - δ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      linarith
    · have h1 : 0 < Real.sin (ψ - Real.pi) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h2 : Real.sin ψ = -Real.sin (ψ - Real.pi) := by
        conv_lhs => rw [show ψ = ψ - Real.pi + Real.pi by ring]
        rw [Real.sin_add_pi]
      linarith
  · rintro ⟨h0, hδ'⟩
    refine ⟨⟨h0, by linarith⟩, ?_, ?_⟩
    · exact Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    · have h1 : 0 ≤ Real.sin (δ - ψ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have h2 : Real.sin (ψ - δ) = -Real.sin (δ - ψ) := by
        rw [← Real.sin_neg, neg_sub]
      linarith [h2]

/-- The open sine window on one period. -/
theorem sin_window_strict {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ < Real.pi) :
    {ψ : ℝ | ψ ∈ Set.Ico 0 (2 * Real.pi) ∧ 0 < Real.sin ψ ∧ Real.sin (ψ - δ) < 0}
      = Set.Ioo 0 δ := by
  have hπ := Real.pi_pos
  ext ψ
  simp only [Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h0, h2π⟩, hs1, hs2⟩
    have hweak : ψ ∈ Set.Icc 0 δ := by
      rw [← sin_window_weak hδ0 hδπ]
      exact ⟨⟨h0, h2π⟩, hs1.le, hs2.le⟩
    obtain ⟨hl, hr⟩ := Set.mem_Icc.mp hweak
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hl with h1 | h1
      · rw [← h1, Real.sin_zero] at hs1
        exact absurd hs1 (lt_irrefl 0)
      · exact h1
    · rcases eq_or_lt_of_le hr with h1 | h1
      · rw [h1, sub_self, Real.sin_zero] at hs2
        exact absurd hs2 (lt_irrefl 0)
      · exact h1
  · rintro ⟨h0, hδ'⟩
    refine ⟨⟨h0.le, by linarith⟩, ?_, ?_⟩
    · exact Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
    · have h1 : 0 < Real.sin (δ - ψ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h2 : Real.sin (ψ - δ) = -Real.sin (δ - ψ) := by
        rw [← Real.sin_neg, neg_sub]
      linarith [h2]

/-- Sliding a length-`2π` window across a `2π`-periodic set preserves its trace measure. -/
theorem vol_window_shift {T : Set ℝ} (hT : MeasurableSet T)
    (hper : ∀ x, x ∈ T ↔ x + 2 * Real.pi ∈ T) {c t : ℝ} (ht0 : 0 ≤ t)
    (ht2 : t ≤ 2 * Real.pi) :
    volume (T ∩ Set.Ico (c + t) (c + t + 2 * Real.pi))
      = volume (T ∩ Set.Ico c (c + 2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have htrans : T ∩ Set.Ico (c + 2 * Real.pi) (c + t + 2 * Real.pi)
      = (fun x => x + -(2 * Real.pi)) ⁻¹' (T ∩ Set.Ico c (c + t)) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_preimage]
    constructor
    · rintro ⟨hyT, hy1, hy2⟩
      refine ⟨(hper (y + -(2 * Real.pi))).mpr (by simpa using hyT), by linarith, by linarith⟩
    · rintro ⟨hyT, hy1, hy2⟩
      have h2 := (hper (y + -(2 * Real.pi))).mp hyT
      refine ⟨by simpa using h2, by linarith, by linarith⟩
  have hsplit1 : T ∩ Set.Ico (c + t) (c + t + 2 * Real.pi)
      = (T ∩ Set.Ico (c + t) (c + 2 * Real.pi))
        ∪ (T ∩ Set.Ico (c + 2 * Real.pi) (c + t + 2 * Real.pi)) := by
    rw [← Set.inter_union_distrib_left, Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  have hsplit2 : T ∩ Set.Ico c (c + 2 * Real.pi)
      = (T ∩ Set.Ico c (c + t)) ∪ (T ∩ Set.Ico (c + t) (c + 2 * Real.pi)) := by
    rw [← Set.inter_union_distrib_left, Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  have hd1 : Disjoint (T ∩ Set.Ico (c + t) (c + 2 * Real.pi))
      (T ∩ Set.Ico (c + 2 * Real.pi) (c + t + 2 * Real.pi)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨-, -, hy2⟩ ⟨-, hy3, -⟩
    linarith
  have hd2 : Disjoint (T ∩ Set.Ico c (c + t)) (T ∩ Set.Ico (c + t) (c + 2 * Real.pi)) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨-, -, hy2⟩ ⟨-, hy3, -⟩
    linarith
  rw [hsplit1, hsplit2, measure_union hd1 (hT.inter measurableSet_Ico),
    measure_union hd2 (hT.inter measurableSet_Ico), htrans]
  rw [show (fun x : ℝ => x + -(2 * Real.pi)) = (fun x : ℝ => -(2 * Real.pi) + x) by
    funext x; ring]
  rw [measure_preimage_add]
  ring

/-- The argument of a quotient lifts the argument difference modulo full turns. -/
theorem arg_div_add_int {u₁ u₂ : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    ∃ k : ℤ, Complex.arg u₂
      = Complex.arg (u₂ / u₁) + Complex.arg u₁ + 2 * Real.pi * k := by
  have hq : u₂ / u₁ ≠ 0 := div_ne_zero hu₂ hu₁
  have h1 : (((u₂ / u₁ * u₁).arg : ℝ) : Real.Angle)
      = (((u₂ / u₁).arg + u₁.arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact Complex.arg_mul_coe_angle hq hu₁
  rw [div_mul_cancel₀ u₂ hu₁] at h1
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h1
  exact ⟨k, by linarith [hk]⟩

/-- Sine sign against the direction of a nonzero complex number. -/
theorem sin_arg_div {u₁ u₂ : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    (u₂ / u₁).im = ‖u₂ / u₁‖ * Real.sin (Complex.arg (u₂ / u₁)) := by
  have hq : u₂ / u₁ ≠ 0 := div_ne_zero hu₂ hu₁
  rw [Complex.sin_arg, mul_div_cancel₀]
  exact norm_ne_zero_iff.mpr hq

/-- The two-half-plane direction window has measure the positive argument gap. -/
theorem vol_arc_pos {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    (hδpos : 0 < Complex.arg (u₂ / u₁)) :
    volume {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
      = ENNReal.ofReal |Complex.arg (u₂ / u₁)| := by
  have hπ := Real.pi_pos
  set δ : ℝ := Complex.arg (u₂ / u₁) with hδdef
  set a₁ : ℝ := Complex.arg u₁ with ha₁def
  set a₂ : ℝ := Complex.arg u₂ with ha₂def
  have hqnorm : 0 < ‖u₂ / u₁‖ :=
    norm_pos_iff.mpr (div_ne_zero hu₂ hu₁)
  have hqnorm' : 0 < ‖u₁ / u₂‖ :=
    norm_pos_iff.mpr (div_ne_zero hu₁ hu₂)
  have hsinδ : 0 < σ₁ * Real.sin δ := by
    have h1 := sin_arg_div hu₁ hu₂
    rw [h1] at h12
    nlinarith [h12, hqnorm]
  have hδπ : δ < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi (u₂ / u₁)) with h1 | h1
    · exact h1
    · exfalso
      rw [← hδdef] at h1
      rw [h1, Real.sin_pi, mul_zero] at hsinδ
      exact lt_irrefl 0 hsinδ
  have hσ₁1 : σ₁ = 1 := by
    rcases hσ₁ with h1 | h1
    · exact h1
    · exfalso
      have h2 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
      rw [h1] at hsinδ
      nlinarith
  have hsinδ' : 0 < Real.sin δ := by
    rw [hσ₁1, one_mul] at hsinδ
    exact hsinδ
  have harginv : Complex.arg (u₁ / u₂) = -δ := by
    rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, ← hδdef,
      if_neg (by intro h1; rw [h1] at hδπ; exact lt_irrefl _ hδπ)]
  have hσ₂1 : σ₂ = -1 := by
    have h1 := sin_arg_div hu₂ hu₁
    rw [h1, harginv, Real.sin_neg] at h21
    rcases hσ₂ with h2 | h2
    · exfalso
      rw [h2] at h21
      nlinarith
    · exact h2
  obtain ⟨k, hk⟩ := arg_div_add_int hu₁ hu₂
  have hsin₂ : ∀ φ : ℝ, Real.sin (φ - a₂) = Real.sin (φ - a₁ - δ) := by
    intro φ
    have h1 : φ - a₂ = φ - a₁ - δ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [ha₂def, hk]
      push_cast
      ring
    rw [h1, Real.sin_add_int_mul_two_pi]
  have hn₁ : (0 : ℝ) < ‖u₁‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₁)
  have hn₂ : (0 : ℝ) < ‖u₂‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₂)
  set T : Set ℝ := {ψ : ℝ | 0 ≤ Real.sin ψ ∧ Real.sin (ψ - δ) ≤ 0} with hTdef
  have hset : {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
      0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
      0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
      = (fun ψ => ψ + a₁) ''
          (T ∩ Set.Ico (-Real.pi - a₁) (Real.pi - a₁)) := by
    ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_Ico, hTdef]
    constructor
    · rintro ⟨⟨hφ1, hφ2⟩, hc1, hc2⟩
      rw [exp_div_im φ hu₁, hσ₁1, one_mul] at hc1
      rw [exp_div_im φ hu₂, hσ₂1] at hc2
      refine ⟨φ - a₁, ⟨⟨?_, ?_⟩, by linarith, by linarith⟩, by ring⟩
      · nlinarith [hc1, hn₁]
      · have h2 := hsin₂ φ
        have h3 : Real.sin (φ - a₂) ≤ 0 := by nlinarith [hc2, hn₂]
        rw [show φ - a₁ - δ = φ - a₁ - δ by ring, ← h2]
        exact h3
    · rintro ⟨ψ, ⟨⟨hs1, hs2⟩, hw1, hw2⟩, hφeq⟩
      subst hφeq
      refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
      · rw [exp_div_im _ hu₁, hσ₁1, one_mul, add_sub_cancel_right]
        positivity
      · rw [exp_div_im _ hu₂, hσ₂1]
        have h2 := hsin₂ (ψ + a₁)
        have h3 : ψ + a₁ - a₁ - δ = ψ - δ := by ring
        rw [h3] at h2
        rw [h2]
        nlinarith [hs2, hn₂]
  have hTmeas : MeasurableSet T := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le measurable_const Real.continuous_sin.measurable
    · exact measurableSet_le
        (Real.continuous_sin.comp (continuous_id.sub continuous_const)).measurable
        measurable_const
  have hTper : ∀ x, x ∈ T ↔ x + 2 * Real.pi ∈ T := by
    intro x
    simp only [hTdef, Set.mem_ofPred_eq]
    rw [Real.sin_add_two_pi, show x + 2 * Real.pi - δ = x - δ + 2 * Real.pi by ring,
      Real.sin_add_two_pi]
  have ht0 : (0 : ℝ) ≤ Real.pi + a₁ := by
    have := Complex.neg_pi_lt_arg u₁
    rw [← ha₁def] at this
    linarith
  have ht2 : Real.pi + a₁ ≤ 2 * Real.pi := by
    have := Complex.arg_le_pi u₁
    rw [← ha₁def] at this
    linarith
  have hshift := vol_window_shift hTmeas hTper (c := -Real.pi - a₁) ht0 ht2
  rw [show -Real.pi - a₁ + (Real.pi + a₁) = 0 by ring,
    show (0 : ℝ) + 2 * Real.pi = 2 * Real.pi by ring,
    show -Real.pi - a₁ + 2 * Real.pi = Real.pi - a₁ by ring] at hshift
  have himg : ((fun ψ : ℝ => ψ + a₁) ''
      (T ∩ Set.Ico (-Real.pi - a₁) (Real.pi - a₁)))
      = (fun x : ℝ => -a₁ + x) ⁻¹' (T ∩ Set.Ico (-Real.pi - a₁) (Real.pi - a₁)) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      have h1 : -a₁ + (ψ + a₁) = ψ := by ring
      rw [h1]
      exact hψ
    · intro hy
      exact ⟨-a₁ + y, hy, by ring⟩
  have e3 : T ∩ Set.Ico 0 (2 * Real.pi) = Set.Icc 0 δ := by
    rw [← sin_window_weak hδpos hδπ]
    ext ψ
    simp only [hTdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hset, himg, measure_preimage_add, ← hshift, e3, Real.volume_Icc, sub_zero,
    abs_of_pos hδpos]

/-- The sine of an angle against the second direction shifts by the quotient argument. -/
theorem sin_sub_arg {u₁ u₂ : ℂ} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (φ : ℝ) :
    Real.sin (φ - Complex.arg u₂)
      = Real.sin (φ - Complex.arg u₁ - Complex.arg (u₂ / u₁)) := by
  obtain ⟨k, hk⟩ := arg_div_add_int hu₁ hu₂
  have h1 : φ - Complex.arg u₂
      = φ - Complex.arg u₁ - Complex.arg (u₂ / u₁) + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hk]
    push_cast
    ring
  rw [h1, Real.sin_add_int_mul_two_pi]

/-- The nonzero-argument-gap direction window has measure the absolute argument gap. -/
theorem vol_arc {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im) :
    volume {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
      = ENNReal.ofReal |Complex.arg (u₂ / u₁)| := by
  have hδne : Complex.arg (u₂ / u₁) ≠ 0 := by
    intro h0
    have h1 := sin_arg_div hu₁ hu₂
    rw [h0, Real.sin_zero, mul_zero] at h1
    rw [h1, mul_zero] at h12
    exact lt_irrefl 0 h12
  rcases lt_or_gt_of_ne hδne with hδneg | hδpos
  · have hπ' : Complex.arg (u₂ / u₁) ≠ Real.pi := by
      intro h0
      linarith [Real.pi_pos, hδneg, h0 ▸ hδneg]
    have harginv : Complex.arg (u₁ / u₂) = -Complex.arg (u₂ / u₁) := by
      rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, if_neg hπ']
    have hδpos' : 0 < Complex.arg (u₁ / u₂) := by
      rw [harginv]
      linarith
    have h1 := vol_arc_pos hσ₂ hσ₁ hu₂ hu₁ h21 h12 hδpos'
    have hsets : {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im}
        = {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧
        0 ≤ σ₂ * (Complex.exp ((φ : ℂ) * Complex.I) / u₂).im ∧
        0 ≤ σ₁ * (Complex.exp ((φ : ℂ) * Complex.I) / u₁).im} := by
      ext φ
      simp only [Set.mem_ofPred_eq]
      tauto
    rw [hsets, h1, harginv, abs_neg]
  · exact vol_arc_pos hσ₁ hσ₂ hu₁ hu₂ h12 h21 hδpos

/-- Away from the two boundary rays, a point of the punctured disc either satisfies both
strict sector conditions or violates one of them strictly. -/
theorem slit_trichotomy {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ}
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    {x : ℂ} (hx : x ≠ 0)
    (hr₁ : ¬ ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * u₁)
    (hr₂ : ¬ ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * u₂) :
    (0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im) ∨
      σ₁ * (x / u₁).im < 0 ∨ σ₂ * (x / u₂).im < 0 := by
  have hσ₁ne : σ₁ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h12
    exact lt_irrefl 0 h12
  have hσ₂ne : σ₂ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h21
    exact lt_irrefl 0 h21
  have hmul : ∀ u u' : ℂ, u ≠ 0 → u' ≠ 0 → (x / u).im = 0 →
      (¬ ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * u) →
      ∃ t : ℝ, t < 0 ∧ x = (t : ℂ) * u := by
    intro u u' hu hu' him hray
    have hre : x / u = (((x / u).re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    have hx1 : x = (((x / u).re : ℝ) : ℂ) * u := by
      rw [← hre, div_mul_cancel₀ x hu]
    have htne : (x / u).re ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, zero_mul] at hx1
      exact hx hx1
    rcases lt_or_gt_of_ne htne with h1 | h1
    · exact ⟨(x / u).re, h1, hx1⟩
    · exact absurd ⟨(x / u).re, h1, hx1⟩ hray
  rcases lt_trichotomy (σ₁ * (x / u₁).im) 0 with h1 | h1 | h1
  · exact Or.inr (Or.inl h1)
  · have him : (x / u₁).im = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hσ₁ne
      · exact h2
    obtain ⟨t, ht, hx1⟩ := hmul u₁ u₂ hu₁ hu₂ him hr₁
    refine Or.inr (Or.inr ?_)
    have h2 : x / u₂ = (t : ℂ) * (u₁ / u₂) := by
      rw [hx1, mul_div_assoc]
    rw [h2, Complex.im_ofReal_mul]
    nlinarith [h21, ht]
  · rcases lt_trichotomy (σ₂ * (x / u₂).im) 0 with h2 | h2 | h2
    · exact Or.inr (Or.inr h2)
    · have him : (x / u₂).im = 0 := by
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 hσ₂ne
        · exact h3
      obtain ⟨t, ht, hx1⟩ := hmul u₂ u₁ hu₂ hu₁ him hr₂
      refine Or.inr (Or.inl ?_)
      have h3 : x / u₁ = (t : ℂ) * (u₂ / u₁) := by
        rw [hx1, mul_div_assoc]
      rw [h3, Complex.im_ofReal_mul]
      nlinarith [h12, ht]
    · exact Or.inl ⟨h1, h2⟩

/-- The strict two-half-plane sector inside a disc is a polar rectangle over the positive
argument gap. -/
theorem sector_eq_polar {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    (hδpos : 0 < Complex.arg (u₂ / u₁)) :
    {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im}
      = (fun p : ℝ × ℝ =>
          (p.1 : ℂ) * Complex.exp (((p.2 + Complex.arg u₁ : ℝ) : ℂ) * Complex.I))
        '' (Set.Ioo 0 s ×ˢ Set.Ioo 0 (Complex.arg (u₂ / u₁))) := by
  have hπ := Real.pi_pos
  set δ : ℝ := Complex.arg (u₂ / u₁) with hδdef
  set a₁ : ℝ := Complex.arg u₁ with ha₁def
  set a₂ : ℝ := Complex.arg u₂ with ha₂def
  have hqnorm : 0 < ‖u₂ / u₁‖ := norm_pos_iff.mpr (div_ne_zero hu₂ hu₁)
  have hn₁ : (0 : ℝ) < ‖u₁‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₁)
  have hn₂ : (0 : ℝ) < ‖u₂‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hu₂)
  have hsinδ : 0 < σ₁ * Real.sin δ := by
    have h1 := sin_arg_div hu₁ hu₂
    rw [h1] at h12
    nlinarith [h12, hqnorm]
  have hδπ : δ < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi (u₂ / u₁)) with h1 | h1
    · exact h1
    · exfalso
      rw [← hδdef] at h1
      rw [h1, Real.sin_pi, mul_zero] at hsinδ
      exact lt_irrefl 0 hsinδ
  have hσ₁1 : σ₁ = 1 := by
    rcases hσ₁ with h1 | h1
    · exact h1
    · exfalso
      have h2 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
      rw [h1] at hsinδ
      nlinarith
  have harginv : Complex.arg (u₁ / u₂) = -δ := by
    rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, ← hδdef,
      if_neg (by intro h1; rw [h1] at hδπ; exact lt_irrefl _ hδπ)]
  have hσ₂1 : σ₂ = -1 := by
    have h1 := sin_arg_div hu₂ hu₁
    rw [h1, harginv, Real.sin_neg] at h21
    rcases hσ₂ with h2 | h2
    · exfalso
      rw [h2] at h21
      have h3 : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos hδπ
      nlinarith [norm_pos_iff.mpr (div_ne_zero hu₁ hu₂)]
    · exact h2
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨hxs, hc1, hc2⟩
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hc1
      simp at hc1
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    rw [div_im_sign hu₁ hx0, hσ₁1, one_mul, ← ha₁def] at hc1
    rw [div_im_sign hu₂ hx0, hσ₂1, ← ha₂def] at hc2
    have hs1 : 0 < Real.sin (Complex.arg x - a₁) := by nlinarith [hc1, mul_pos hnx hn₁]
    have hs2 : Real.sin (Complex.arg x - a₂) < 0 := by nlinarith [hc2, mul_pos hnx hn₂]
    have hs2' : Real.sin (Complex.arg x - a₁ - δ) < 0 := by
      rw [← sin_sub_arg hu₁ hu₂]
      exact hs2
    set ψ₀ : ℝ := Complex.arg x - a₁ with hψ₀def
    have hψ₀lb : -(2 * Real.pi) < ψ₀ := by
      have b1 := Complex.neg_pi_lt_arg x
      have b2 := Complex.arg_le_pi u₁
      rw [← ha₁def] at b2
      simp only [hψ₀def]
      linarith
    have hψ₀ub : ψ₀ < 2 * Real.pi := by
      have b1 := Complex.arg_le_pi x
      have b2 := Complex.neg_pi_lt_arg u₁
      rw [← ha₁def] at b2
      simp only [hψ₀def]
      linarith
    by_cases hcase : 0 ≤ ψ₀
    · have hmem : ψ₀ ∈ Set.Ioo 0 δ := by
        have h1 := (Set.ext_iff.mp (sin_window_strict hδpos hδπ) ψ₀).mp
          ⟨⟨hcase, hψ₀ub⟩, hs1, hs2'⟩
        exact h1
      refine ⟨(‖x‖, ψ₀), ⟨⟨hnx, hxs⟩, hmem⟩, ?_⟩
      have h2 : ψ₀ + a₁ = Complex.arg x := by
        simp only [hψ₀def]
        ring
      rw [h2]
      exact Complex.norm_mul_exp_arg_mul_I x
    · have hψ' : ψ₀ + 2 * Real.pi ∈ Set.Ico 0 (2 * Real.pi) :=
        ⟨by linarith, by linarith [not_le.mp hcase]⟩
      have hsin1 : 0 < Real.sin (ψ₀ + 2 * Real.pi) := by
        rw [Real.sin_add_two_pi]
        exact hs1
      have hsin2 : Real.sin (ψ₀ + 2 * Real.pi - δ) < 0 := by
        rw [show ψ₀ + 2 * Real.pi - δ = ψ₀ - δ + 2 * Real.pi by ring,
          Real.sin_add_two_pi]
        exact hs2'
      have hmem : ψ₀ + 2 * Real.pi ∈ Set.Ioo 0 δ :=
        (Set.ext_iff.mp (sin_window_strict hδpos hδπ) _).mp ⟨hψ', hsin1, hsin2⟩
      refine ⟨(‖x‖, ψ₀ + 2 * Real.pi), ⟨⟨hnx, hxs⟩, hmem⟩, ?_⟩
      have h2 : ((ψ₀ + 2 * Real.pi + a₁ : ℝ) : ℂ) * Complex.I
          = ((Complex.arg x : ℝ) : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
        simp only [hψ₀def]
        push_cast
        ring
      rw [h2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      exact Complex.norm_mul_exp_arg_mul_I x
  · rintro ⟨⟨r, ψ⟩, ⟨⟨hr0, hrs⟩, hψ0, hψδ⟩, rfl⟩
    dsimp only at hr0 hrs hψ0 hψδ ⊢
    have hsinψ : 0 < Real.sin ψ :=
      Real.sin_pos_of_pos_of_lt_pi hψ0 (by linarith)
    have hsinψδ : Real.sin (ψ - δ) < 0 := by
      have h1 : 0 < Real.sin (δ - ψ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have h2 : Real.sin (ψ - δ) = -Real.sin (δ - ψ) := by
        rw [← Real.sin_neg, neg_sub]
      linarith
    have hnorm : ‖(r : ℂ) * Complex.exp (((ψ + a₁ : ℝ) : ℂ) * Complex.I)‖ = r := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0]
    refine ⟨by rw [hnorm]; exact hrs, ?_, ?_⟩
    · rw [mul_div_assoc, Complex.im_ofReal_mul, exp_div_im _ hu₁, ← ha₁def,
        add_sub_cancel_right, hσ₁1]
      nlinarith [mul_pos (mul_pos hr0 hn₁) hsinψ]
    · rw [mul_div_assoc, Complex.im_ofReal_mul, exp_div_im _ hu₂, ← ha₂def, hσ₂1]
      have h2 : Real.sin (ψ + a₁ - a₂) = Real.sin (ψ - δ) := by
        rw [sin_sub_arg hu₁ hu₂, ← ha₁def, ← hδdef,
          show ψ + a₁ - a₁ - δ = ψ - δ by ring]
      rw [h2]
      nlinarith [mul_pos (mul_pos hr0 hn₂) (neg_pos.mpr hsinψδ)]

/-- The strict two-half-plane sector inside a disc is preconnected. -/
theorem sector_preconnected {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im)
    (hδpos : 0 < Complex.arg (u₂ / u₁)) :
    IsPreconnected {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im} := by
  rw [sector_eq_polar hσ₁ hσ₂ hu₁ hu₂ h12 h21 hδpos]
  refine IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_Ioo) _ ?_
  refine Continuous.continuousOn ?_
  refine Continuous.mul (Complex.continuous_ofReal.comp continuous_fst) ?_
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  exact Complex.continuous_ofReal.comp (continuous_snd.add continuous_const)

/-- The strict sector over the reversed direction pair is the same set. -/
theorem sector_comm {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ} :
    {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im}
      = {x : ℂ | ‖x‖ < s ∧ 0 < σ₂ * (x / u₂).im ∧ 0 < σ₁ * (x / u₁).im} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  tauto

/-- The zero set of a sine shifted by a principal argument on the principal window is
finite. -/
theorem finite_sin_zero {a : ℝ} (ha : -Real.pi < a) (ha' : a ≤ Real.pi) :
    {φ : ℝ | φ ∈ Set.Ico (-Real.pi) Real.pi ∧ Real.sin (φ - a) = 0}.Finite := by
  have hπ := Real.pi_pos
  refine ((((Set.finite_singleton (a + Real.pi)).insert a).insert
    (a - Real.pi)).insert (a - 2 * Real.pi)).subset ?_
  rintro φ ⟨⟨h1, h2⟩, hz⟩
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
  have hn2 : (-2 : ℝ) ≤ (n : ℝ) := by nlinarith [hn, hπ, h1, h2, ha, ha']
  have hn2' : (n : ℝ) < 2 := by nlinarith [hn, hπ, h1, h2, ha, ha']
  have hn3 : n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 := by
    have hlt : n < 2 := by exact_mod_cast hn2'
    have hgt : (-2 : ℤ) ≤ n := by exact_mod_cast hn2
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hn3 with h3 | h3 | h3 | h3 <;> rw [h3] at hn <;> push_cast at hn
  · left; linarith
  · right; left; linarith
  · right; right; left; linarith
  · right; right; right; linarith

/-! ## Dictionary tier: the disc frame as a homeomorphic chart with a `tanh` radius law -/

/-- The frame at a base point is continuous. -/
theorem continuous_discChart (v : UpperHalfPlane) :
    Continuous fun w : UpperHalfPlane => discChart v w := by
  have h1 : (fun w : UpperHalfPlane => discChart v w)
      = fun w : UpperHalfPlane =>
        ((w : ℂ) - (v : ℂ)) / ((w : ℂ) - (starRingEnd ℂ) (v : ℂ)) := by
    funext w
    exact discChart_eq v w
  rw [h1]
  refine Continuous.div ?_ ?_ ?_
  · exact (UpperHalfPlane.continuous_coe.sub continuous_const)
  · exact (UpperHalfPlane.continuous_coe.sub continuous_const)
  · intro w
    exact sub_conj_ne_zero v w

/-- The `tanh` radius law of the frame: hyperbolic balls become Euclidean discs. -/
theorem dist_lt_iff_norm_chart {v w : UpperHalfPlane} {r : ℝ} (hr : 0 < r) :
    dist v w < r ↔ ‖discChart v w‖ < Real.tanh (r / 2) := by
  have hd : dist v w = 2 * Real.arsinh (‖discChart v w‖
      / Real.sqrt (1 - ‖discChart v w‖ ^ 2)) := by
    have h1 := dist_eq_hDD v v w
    rw [discChart_self] at h1
    rw [h1, hyperbolicDistDisk, norm_sub_rev, sub_zero, norm_zero]
    norm_num
  set t : ℝ := ‖discChart v w‖ with htdef
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t < 1 := norm_discChart_lt_one v w
  have htsq : 0 < 1 - t ^ 2 := by nlinarith
  have hsq : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr htsq
  set S : ℝ := Real.sinh (r / 2) with hSdef
  have hS0 : 0 < S := by
    rw [hSdef]
    exact Real.sinh_pos_iff.mpr (by linarith)
  have hcosh : 0 < Real.cosh (r / 2) := Real.cosh_pos _
  have hchain1 : dist v w < r ↔ t / Real.sqrt (1 - t ^ 2) < S := by
    rw [hd]
    constructor
    · intro h1
      have h2 : Real.arsinh (t / Real.sqrt (1 - t ^ 2)) < r / 2 := by linarith
      have h3 := Real.arsinh_lt_arsinh.mp (by rwa [Real.arsinh_sinh] : Real.arsinh
        (t / Real.sqrt (1 - t ^ 2)) < Real.arsinh S)
      exact h3
    · intro h1
      have h2 : Real.arsinh (t / Real.sqrt (1 - t ^ 2)) < Real.arsinh S :=
        Real.arsinh_lt_arsinh.mpr h1
      rw [hSdef, Real.arsinh_sinh] at h2
      linarith
  have hchain2 : t / Real.sqrt (1 - t ^ 2) < S ↔ t ^ 2 < S ^ 2 * (1 - t ^ 2) := by
    rw [div_lt_iff₀ hsq]
    constructor
    · intro h1
      have h2 : t * t < (S * Real.sqrt (1 - t ^ 2)) * (S * Real.sqrt (1 - t ^ 2)) :=
        mul_self_lt_mul_self ht0 h1
      have h3 : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
        Real.mul_self_sqrt htsq.le
      nlinarith
    · intro h1
      have h2 : Real.sqrt (1 - t ^ 2) * Real.sqrt (1 - t ^ 2) = 1 - t ^ 2 :=
        Real.mul_self_sqrt htsq.le
      nlinarith [mul_pos hS0 hsq, sq_nonneg (t - S * Real.sqrt (1 - t ^ 2)),
        sq_nonneg (t + S * Real.sqrt (1 - t ^ 2))]
  have hchain3 : t ^ 2 < S ^ 2 * (1 - t ^ 2) ↔ t * Real.cosh (r / 2) < S := by
    have hc2 : Real.cosh (r / 2) ^ 2 = S ^ 2 + 1 := by
      rw [hSdef, Real.cosh_sq]
    constructor
    · intro h1
      have h2 : (t * Real.cosh (r / 2)) ^ 2 < S ^ 2 := by
        rw [mul_pow, hc2]
        nlinarith
      have h3 : t * Real.cosh (r / 2) < S := by
        nlinarith [mul_nonneg ht0 hcosh.le, hS0]
      exact h3
    · intro h1
      have h3 : 0 ≤ t * Real.cosh (r / 2) := by positivity
      have h2 : (t * Real.cosh (r / 2)) ^ 2 < S ^ 2 := by nlinarith
      rw [mul_pow, hc2] at h2
      nlinarith
  have hchain4 : t * Real.cosh (r / 2) < S ↔ t < Real.tanh (r / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh, ← hSdef, lt_div_iff₀ hcosh]
  rw [hchain1, hchain2, hchain3, hchain4]

/-- The inverse Cayley formula has positive imaginary part on the open unit disc. -/
theorem invChart_im (v : UpperHalfPlane) {u : ℂ} (hu : ‖u‖ < 1) :
    0 < ((v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u))).im := by
  have hden : (1 : ℂ) - u ≠ 0 := by
    intro h0
    have h1 : u = 1 := by linear_combination -h0
    rw [h1] at hu
    simp at hu
  have hre : ((1 + u) / (1 - u)).re = (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
    rw [Complex.div_re, ← add_div]
    congr 1
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply]
    ring
  have him : ((v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u))).im
      = v.im * ((1 + u) / (1 - u)).re := by
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [him, hre]
  have h2 : Complex.normSq u < 1 := by
    have h3 : Complex.normSq u = ‖u‖ ^ 2 := (Complex.sq_norm u).symm
    nlinarith [norm_nonneg u]
  have h4 : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hden
  have h5 : 0 < v.im := v.im_pos
  exact mul_pos h5 (div_pos (by linarith) h4)

/-- The frame at a base point surjects onto the open unit disc, with an explicit inverse. -/
theorem chart_surj (v : UpperHalfPlane) {u : ℂ} (hu : ‖u‖ < 1) :
    ∃ w : UpperHalfPlane, discChart v w = u ∧
      (w : ℂ) = (v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u)) := by
  have hden : (1 : ℂ) - u ≠ 0 := by
    intro h0
    have h1 : u = 1 := by linear_combination -h0
    rw [h1] at hu
    simp at hu
  set w : UpperHalfPlane := UpperHalfPlane.mk
    ((v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u))) (invChart_im v hu)
    with hwdef
  have hcoe : (w : ℂ) = (v.re : ℂ) + (v.im : ℂ) * Complex.I * ((1 + u) / (1 - u)) := rfl
  refine ⟨w, ?_, hcoe⟩
  rw [discChart_eq]
  have hne2 : (w : ℂ) - (starRingEnd ℂ) (v : ℂ) ≠ 0 := sub_conj_ne_zero v w
  rw [div_eq_iff hne2, hcoe, conj_coe, coe_eq_re_add_im v]
  have hW : (1 + u) / (1 - u) * (1 - u) = 1 + u := div_mul_cancel₀ _ hden
  linear_combination ((v.im : ℂ) * Complex.I) * hW

/-- The frame at a base point is injective. -/
theorem discChart_injective (v : UpperHalfPlane) {w w' : UpperHalfPlane}
    (h : discChart v w = discChart v w') : w = w' := by
  have h1 := dist_eq_hDD v w w'
  rw [h, hyperbolicDistDisk_self] at h1
  exact dist_eq_zero.mp h1

/-- Every short direction multiple of a far ray point is realized on the radial segment. -/
theorem slit_full {v y : UpperHalfPlane} (hy : y ≠ v) {r' : ℝ} (hr' : 0 < r')
    (hyfar : r' ≤ dist v y) {x : ℂ} (hx : ∃ t : ℝ, 0 < t ∧ x = (t : ℂ) * discChart v y)
    (hxs : ‖x‖ < Real.tanh (r' / 2)) :
    ∃ w : UpperHalfPlane, w ∈ geodSeg v y ∧ w ≠ v ∧ discChart v w = x := by
  obtain ⟨t, ht, hxdef⟩ := hx
  have hyc : discChart v y ≠ 0 := discChart_ne_zero hy
  have hx0 : x ≠ 0 := by
    rw [hxdef]
    exact mul_ne_zero (by exact_mod_cast ht.ne') hyc
  have hg : Continuous fun τ : ℝ => ‖discChart v (geodInterp v y τ)‖ := by
    refine Continuous.norm ?_
    refine (continuous_discChart v).comp ?_
    exact continuous_geodInterp.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hg0 : ‖discChart v (geodInterp v y 0)‖ = 0 := by
    rw [geodInterp_zero, discChart_self, norm_zero]
  have hg1 : Real.tanh (r' / 2) ≤ ‖discChart v (geodInterp v y 1)‖ := by
    rw [geodInterp_one]
    by_contra hcon
    have h2 : dist v y < r' := (dist_lt_iff_norm_chart hr').mpr (not_le.mp hcon)
    linarith
  have hmem : ‖x‖ ∈ Set.Icc (‖discChart v (geodInterp v y 0)‖)
      (‖discChart v (geodInterp v y 1)‖) := by
    rw [hg0]
    exact ⟨norm_nonneg x, le_trans hxs.le hg1⟩
  obtain ⟨τ, hτmem, hτeq⟩ := intermediate_value_Icc (by norm_num) hg.continuousOn hmem
  have hτeq' : ‖discChart v (geodInterp v y τ)‖ = ‖x‖ := hτeq
  set w : UpperHalfPlane := geodInterp v y τ with hwdef
  have hwseg : w ∈ geodSeg v y := geodInterp_mem_geodSeg v y hτmem
  have hwv : w ≠ v := by
    intro h0
    rw [h0, discChart_self, norm_zero] at hτeq'
    exact norm_ne_zero_iff.mpr hx0 hτeq'.symm
  obtain ⟨t', ht', hchart⟩ := discChart_smul_of_mem_geodSeg hwseg hwv
  refine ⟨w, hwseg, hwv, ?_⟩
  have hnorm : t' * ‖discChart v y‖ = t * ‖discChart v y‖ := by
    have h2 : ‖discChart v w‖ = ‖x‖ := hτeq'
    rw [hchart, hxdef] at h2
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht', abs_of_pos ht] at h2
    exact h2
  have htt : t' = t :=
    mul_right_cancel₀ (norm_ne_zero_iff.mpr hyc) hnorm
  rw [hchart, htt, hxdef]

/-! ## Assembly helpers: ray order, ray-independence of angles, side transport -/

/-- Of two points of a radial segment, the nearer lies on the segment to the farther. -/
theorem ray_order {g y p q : UpperHalfPlane} (hp : p ∈ geodSeg g y)
    (hq : q ∈ geodSeg g y) (hle : dist g p ≤ dist g q) : p ∈ geodSeg g q := by
  rw [geodSeg_eq_image_geodInterp] at hp hq
  obtain ⟨sp, hsp, hpe⟩ := hp
  obtain ⟨sq, hsq, hqe⟩ := hq
  have hdp : dist g p = sp * dist g y := by rw [← hpe, dist_geodInterp_left g y hsp]
  have hdq : dist g q = sq * dist g y := by rw [← hqe, dist_geodInterp_left g y hsq]
  rcases eq_or_ne (dist g y) 0 with hd0 | hd0
  · have h1 : g = y := dist_eq_zero.mp hd0
    rw [← hpe, ← hqe, h1, geodInterp_self, geodInterp_self]
    exact left_mem_geodSeg _ _
  · have hd0' : 0 < dist g y := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    have hsple : sp ≤ sq := by
      by_contra hcon
      have h1 : sq * dist g y < sp * dist g y :=
        mul_lt_mul_of_pos_right (not_le.mp hcon) hd0'
      rw [← hdp, ← hdq] at h1
      linarith
    rw [mem_geodSeg, ← hpe, ← hqe, dist_geodInterp_pair,
      abs_of_nonpos (by linarith), dist_geodInterp_left g y hsp,
      dist_geodInterp_left g y hsq]
    ring

/-- The sector angle does not depend on the chosen non-apex point of a radial segment. -/
theorem sectorAngle_ray_congr {g y p q : UpperHalfPlane} (hp : p ∈ geodSeg g y)
    (hq : q ∈ geodSeg g y) (hpg : p ≠ g) (hqg : q ≠ g) (w₂ : UpperHalfPlane) :
    sectorAngle g p w₂ = sectorAngle g q w₂ := by
  rcases le_total (dist g p) (dist g q) with h1 | h1
  · exact sectorAngle_congr_of_mem_geodSeg (ray_order hp hq h1) hpg w₂
  · exact (sectorAngle_congr_of_mem_geodSeg (ray_order hq hp h1) hqg w₂).symm

/-- The inverse translate of a side set is the side set of the inverse. -/
theorem smul_sideSet_inv (γ : ↥Γ) :
    (γ⁻¹ • ·) '' dirichletSideSet Γ τ₀ γ = dirichletSideSet Γ τ₀ γ⁻¹ := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact smul_mem_dirichletSideSet_inv hy
  · intro x hx
    have h1 := smul_mem_dirichletSideSet_inv (γ := γ⁻¹) hx
    rw [inv_inv] at h1
    exact ⟨γ • x, h1, by change γ⁻¹ • γ • x = x; rw [inv_smul_smul]⟩

/-- The half-plane functional of one side of a tile in the frame at a vertex: sign data
with the tile on the closed side, the tile interior on the open side, and a transverse
reference segment strictly inside. -/
theorem side_functional (hΓ : IsFuchsianGroup Γ) {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {b c : ↥Γ} (hmove : b • τ₀ ≠ c • τ₀)
    {v : UpperHalfPlane} (hveq : dist v (b • τ₀) = dist v (c • τ₀))
    {Wn : UpperHalfPlane} (hWnbis : dist Wn (b • τ₀) = dist Wn (c • τ₀)) (hWnv : Wn ≠ v)
    {q : UpperHalfPlane} (hqc : q ≠ c • τ₀) (hqb : q ≠ b • τ₀)
    {P : UpperHalfPlane} (hPv : P ≠ v)
    (hPbis : ∀ w ∈ geodSeg v P, dist w (b • τ₀) = dist w q)
    (hPT : geodSeg v P ⊆ (b • ·) '' dirichletDomain Γ τ₀) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      0 < σ * (discChart v P / discChart v Wn).im ∧
      (∀ w ∈ (b • ·) '' dirichletDomain Γ τ₀,
        0 ≤ σ * (discChart v w / discChart v Wn).im) ∧
      (∀ w ∈ (b • ·) '' interior (dirichletDomain Γ τ₀),
        0 < σ * (discChart v w / discChart v Wn).im) := by
  obtain ⟨g, ε', hε', hle, hge⟩ := bisector_normalizer hmove
  obtain ⟨m, hm, hfeq, hflt⟩ := functional_sign hε' hle hge hveq
  have hWn0 : discChart v Wn ≠ 0 := discChart_ne_zero hWnv
  have hzero : ε' * (m * discChart v Wn).im = 0 := hfeq Wn hWnbis
  have hratio := functional_ratio hε' hWn0 hzero
  set C : ℝ := ε' * (m * discChart v Wn).re with hCdef
  have hweak : ∀ w ∈ (b • ·) '' dirichletDomain Γ τ₀,
      0 ≤ C * (discChart v w / discChart v Wn).im := by
    intro w hw
    have h1 : dist w (b • τ₀) ≤ dist w (c • τ₀) := smul_dirichletDomain_subset b c hw
    rw [← hratio (discChart v w)]
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact (hflt w h2).le
    · exact (hfeq w h2).ge
  have hCne : C ≠ 0 := by
    intro hC0
    have h2 : dist (b • τ₀) (b • τ₀) < dist (b • τ₀) (c • τ₀) := by
      rw [dist_self]
      exact dist_pos.mpr hmove
    have h3 := hflt (b • τ₀) h2
    rw [hratio (discChart v (b • τ₀)), hC0, zero_mul] at h3
    exact lt_irrefl 0 h3
  have hint : ∀ w ∈ (b • ·) '' interior (dirichletDomain Γ τ₀),
      0 < C * (discChart v w / discChart v Wn).im := by
    rintro w ⟨y, hy, rfl⟩
    have : IsIsometricSMul (↥Γ) UpperHalfPlane :=
      ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
    have hbc' : (b⁻¹ * c) • τ₀ ≠ τ₀ := by
      intro h0
      have h1 : b • (b⁻¹ * c) • τ₀ = b • τ₀ := congrArg (b • ·) h0
      rw [← mul_smul, mul_inv_cancel_left] at h1
      exact hmove h1.symm
    have hylt : dist y τ₀ < dist y ((b⁻¹ * c) • τ₀) := by
      rw [interior_dirichletDomain_eq hΓ hdense] at hy
      exact hy (b⁻¹ * c) hbc'
    have e1 : dist (b • y) (b • τ₀) = dist y τ₀ := dist_smul b y τ₀
    have e2 : dist (b • y) (c • τ₀) = dist y ((b⁻¹ * c) • τ₀) := by
      calc dist (b • y) (c • τ₀) = dist (b⁻¹ • b • y) (b⁻¹ • c • τ₀) :=
          (dist_smul b⁻¹ _ _).symm
        _ = dist y ((b⁻¹ * c) • τ₀) := by rw [inv_smul_smul, mul_smul]
    have h2 : dist (b • y) (b • τ₀) < dist (b • y) (c • τ₀) := by
      rw [e1, e2]
      exact hylt
    have h3 := hflt (b • y) h2
    rw [hratio (discChart v (b • y))] at h3
    exact h3
  have hstrictP : 0 < C * (discChart v P / discChart v Wn).im := by
    have hP1 : P ∈ geodSeg v P := right_mem_geodSeg v P
    have hd : 0 < dist v P := dist_pos.mpr (Ne.symm hPv)
    rcases lt_or_eq_of_le (hweak P (hPT hP1)) with h1 | h1
    · exact h1
    exfalso
    have hratioP0 : (discChart v P / discChart v Wn).im = 0 := by
      rcases mul_eq_zero.mp h1.symm with h5 | h5
      · exact absurd h5 hCne
      · exact h5
    set P2 : UpperHalfPlane := geodInterp v P (1 / 2) with hP2def
    have hP2seg : P2 ∈ geodSeg v P := geodInterp_mem_geodSeg v P (by norm_num)
    have hdP2 : dist v P2 = 1 / 2 * dist v P :=
      dist_geodInterp_left v P (by norm_num)
    have hP2v : P2 ≠ v := by
      intro h0
      rw [h0, dist_self] at hdP2
      linarith
    have hPP2 : P ≠ P2 := by
      intro h0
      rw [← h0] at hdP2
      linarith
    obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hP2seg hP2v
    have hzP : ε' * (m * discChart v P).im = 0 := by
      rw [hratio (discChart v P), hratioP0, mul_zero]
    have hzP2 : ε' * (m * discChart v P2).im = 0 := by
      rw [hratio (discChart v P2), hchart]
      have h3 : ((t : ℝ) : ℂ) * discChart v P / discChart v Wn
          = (t : ℂ) * (discChart v P / discChart v Wn) := by ring
      rw [h3, Complex.im_ofReal_mul, hratioP0, mul_zero, mul_zero]
    have hbisP : dist P (b • τ₀) = dist P (c • τ₀) := by
      by_contra hne
      have hle' : dist P (b • τ₀) ≤ dist P (c • τ₀) :=
        smul_dirichletDomain_subset b c (hPT hP1)
      rcases lt_or_eq_of_le hle' with h3 | h3
      · exact absurd (hflt P h3) (by rw [hzP]; exact lt_irrefl 0)
      · exact hne h3
    have hbisP2 : dist P2 (b • τ₀) = dist P2 (c • τ₀) := by
      by_contra hne
      have hle' : dist P2 (b • τ₀) ≤ dist P2 (c • τ₀) :=
        smul_dirichletDomain_subset b c (hPT hP2seg)
      rcases lt_or_eq_of_le hle' with h3 | h3
      · exact absurd (hflt P2 h3) (by rw [hzP2]; exact lt_irrefl 0)
      · exact hne h3
    exact hqc (bisector_pair_unique hPP2 hbisP hbisP2 (hPbis P hP1)
      (hPbis P2 hP2seg) (Ne.symm hmove) hqb).symm
  rcases lt_or_gt_of_ne hCne with hCneg | hCpos
  · refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩
    · nlinarith [hstrictP]
    · intro w hw
      nlinarith [hweak w hw]
    · intro w hw
      nlinarith [hint w hw]
  · refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
    · nlinarith [hstrictP]
    · intro w hw
      nlinarith [hweak w hw]
    · intro w hw
      nlinarith [hint w hw]

/-- The strict two-half-plane sector is preconnected, either orientation. -/
theorem sector_preconnected' {u₁ u₂ : ℂ} {σ₁ σ₂ : ℝ} {s : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (h12 : 0 < σ₁ * (u₂ / u₁).im) (h21 : 0 < σ₂ * (u₁ / u₂).im) :
    IsPreconnected {x : ℂ | ‖x‖ < s ∧ 0 < σ₁ * (x / u₁).im ∧ 0 < σ₂ * (x / u₂).im} := by
  have hδne : Complex.arg (u₂ / u₁) ≠ 0 := by
    intro h0
    have h1 := sin_arg_div hu₁ hu₂
    rw [h0, Real.sin_zero, mul_zero] at h1
    rw [h1, mul_zero] at h12
    exact lt_irrefl 0 h12
  rcases lt_or_gt_of_ne hδne with hδneg | hδpos
  · have hπ' : Complex.arg (u₂ / u₁) ≠ Real.pi := by
      intro h0
      linarith [Real.pi_pos, h0 ▸ hδneg]
    have harginv : Complex.arg (u₁ / u₂) = -Complex.arg (u₂ / u₁) := by
      rw [show u₁ / u₂ = (u₂ / u₁)⁻¹ by rw [inv_div], Complex.arg_inv, if_neg hπ']
    have hδpos' : 0 < Complex.arg (u₁ / u₂) := by
      rw [harginv]
      linarith
    rw [sector_comm]
    exact sector_preconnected hσ₂ hσ₁ hu₂ hu₁ h21 h12 hδpos'
  · exact sector_preconnected hσ₁ hσ₂ hu₁ hu₂ h12 h21 hδpos

/-- Composition of set translates along the subgroup action. -/
theorem smul_smul_image (a b : ↥Γ) (S : Set UpperHalfPlane) :
    (a • ·) '' ((b • ·) '' S) = ((a * b) • ·) '' S := by
  rw [← Set.image_comp]
  congr 1
  funext x
  change a • b • x = (a * b) • x
  rw [mul_smul]

/-- A point of a radial slit from the frame base has a purely real frame ratio. -/
theorem ray_kill {v y w : UpperHalfPlane} (hyv : y ≠ v)
    (hw : w ∈ geodSeg v y) (hwv : w ≠ v) :
    (discChart v w / discChart v y).im = 0 := by
  obtain ⟨t, ht, hchart⟩ := discChart_smul_of_mem_geodSeg hw hwv
  rw [hchart, mul_div_assoc, div_self (discChart_ne_zero hyv), mul_one,
    Complex.ofReal_im]

end RiemannDynamics
