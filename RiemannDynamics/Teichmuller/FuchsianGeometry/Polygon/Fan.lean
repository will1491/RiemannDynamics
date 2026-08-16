/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.Polygon.FrameSign

/-!
# The Dirichlet polygon: the vertex star and the fan decomposition

* The vertex star: the tiles containing a vertex form a finite cyclic fan
  (`exists_vertex_cycle`), developed by a bijection onto the class vertices of the
  polygon (`exists_vertex_star_bijection`).
* The fan decomposition: the polygon is the union of the geodesic cones from the
  basepoint over its sides (`dirichletDomain_eq_biUnion_geodCone`).
-/

open MeasureTheory
open scoped ENNReal MatrixGroups

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## The vertex star -/

/-- **Vertex cycle**: the tiles at a vertex admit a cyclic enumeration in rotational order,
without repetition of tiles, in which consecutive tiles share a genuine side through the
vertex. -/
theorem exists_vertex_cycle (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) :
    ∃ (n : ℕ) (e : ℕ → ↥Γ), 3 ≤ n ∧ (∀ k, e (k + n) = e k) ∧
      (∀ k, e k ∈ contactSet Γ τ₀ v) ∧
      (∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀) ∧
      ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)) := by
  classical
  have : Nonempty ↥Γ := ⟨1⟩
  have hPfin : (tileCenters Γ τ₀ v).Finite := (finite_contactSet hΓ τ₀ v).image _
  have hPne : (tileCenters Γ τ₀ v).Nonempty :=
    ⟨τ₀, 1, one_mem_contactSet hv.1, one_smul _ _⟩
  have hrepex : ∀ p ∈ tileCenters Γ τ₀ v,
      ∃ γ : ↥Γ, γ ∈ contactSet Γ τ₀ v ∧ γ • τ₀ = p := by
    rintro p ⟨γ, hγ, rfl⟩
    exact ⟨γ, hγ, rfl⟩
  choose! rep hrep₁ hrep₂ using hrepex
  have hmem : ∀ p q : UpperHalfPlane, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) →
      p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v := fun p q h => ⟨h.1, h.2.1⟩
  have hsymm : ∀ p q : UpperHalfPlane, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) →
      q ∈ tileCenters Γ τ₀ v ∧ p ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep q)⁻¹ * rep p) := by
    rintro p q ⟨hp, hq, hside⟩
    refine ⟨hq, hp, ?_⟩
    have h1 := hside.inv
    rwa [mul_inv_rev, inv_inv] at h1
  have hirr : ∀ p q : UpperHalfPlane, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
      IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) → p ≠ q := by
    rintro p q ⟨hp, hq, hside⟩ rfl
    exact hside.1 (by rw [inv_mul_cancel, one_smul])
  have htwo : ∀ p ∈ tileCenters Γ τ₀ v, ∃ q₁ ∈ tileCenters Γ τ₀ v,
      ∃ q₂ ∈ tileCenters Γ τ₀ v, q₁ ≠ q₂ ∧ ∀ q ∈ tileCenters Γ τ₀ v,
      ((p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
        IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) ↔ q = q₁ ∨ q = q₂) := by
    intro p hp
    obtain ⟨q₁, hq₁, q₂, hq₂, hne', hchar⟩ :=
      two_neighbors hΓ hfree hε hgap hdense hv hrep₁ hrep₂ hp
    refine ⟨q₁, hq₁, q₂, hq₂, hne', ?_⟩
    intro q hq
    constructor
    · rintro ⟨-, -, hside⟩
      exact (hchar q hq).mp hside
    · intro h
      exact ⟨hp, hq, (hchar q hq).mpr h⟩
  have hconn : ∀ S : Set UpperHalfPlane, S ⊆ tileCenters Γ τ₀ v → S.Nonempty →
      (∀ p ∈ S, ∀ q, (p ∈ tileCenters Γ τ₀ v ∧ q ∈ tileCenters Γ τ₀ v ∧
        IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q)) → q ∈ S) → S = tileCenters Γ τ₀ v := by
    intro S hsub hSne hclosed
    refine adj_closed_eq hΓ hfree hv hrep₁ hrep₂ hsub hSne ?_
    intro p hpS q hqP hside
    exact hclosed p hpS q ⟨hsub hpS, hqP, hside⟩
  obtain ⟨n, e₀, hn3, hper, heP, huniq, hadj⟩ :=
    cycle_of_two_regular (A := fun p q => p ∈ tileCenters Γ τ₀ v ∧
      q ∈ tileCenters Γ τ₀ v ∧ IsSideElement Γ τ₀ ((rep p)⁻¹ * rep q))
      hPfin hPne hmem hsymm hirr htwo hconn
  refine ⟨n, fun k => rep (e₀ k), hn3, ?_, ?_, ?_, ?_⟩
  · intro k
    change rep (e₀ (k + n)) = rep (e₀ k)
    rw [hper k]
  · intro k
    exact hrep₁ _ (heP k)
  · intro γ hγ
    have hγP : γ • τ₀ ∈ tileCenters Γ τ₀ v := ⟨γ, hγ, rfl⟩
    obtain ⟨k, ⟨hk, hek⟩, hkuniq⟩ := huniq (γ • τ₀) hγP
    refine ⟨k, ⟨hk, ?_⟩, ?_⟩
    · change γ • τ₀ = rep (e₀ k) • τ₀
      rw [hrep₂ _ (heP k), hek]
    · rintro k' ⟨hk', hek'⟩
      refine hkuniq k' ⟨hk', ?_⟩
      show e₀ k' = γ • τ₀
      rw [← hrep₂ _ (heP k')]
      exact hek'.symm
  · intro k
    exact (hadj k).2.2

/-- **Developed vertex star**: the tiles at a vertex correspond bijectively to the vertices
of the polygon in the orbit class of the vertex, the tile of a contact element `γ`
corresponding to the developed vertex `γ⁻¹ • v`. -/
theorem exists_vertex_star_bijection (_hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀) :
    ∃ Φ : UpperHalfPlane → UpperHalfPlane,
      Set.BijOn Φ (tileCenters Γ τ₀ v) (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀) ∧
      ∀ γ ∈ contactSet Γ τ₀ v, Φ (γ • τ₀) = γ⁻¹ • v := by
  classical
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : UpperHalfPlane → UpperHalfPlane, Φ = fun c =>
      if h : ∃ γ : ↥Γ, γ ∈ contactSet Γ τ₀ v ∧ γ • τ₀ = c
      then (Classical.choose h)⁻¹ • v else v := ⟨_, rfl⟩
  have hΦ : ∀ γ ∈ contactSet Γ τ₀ v, Φ (γ • τ₀) = γ⁻¹ • v := by
    intro γ hγ
    have hex : ∃ δ : ↥Γ, δ ∈ contactSet Γ τ₀ v ∧ δ • τ₀ = γ • τ₀ := ⟨γ, hγ, rfl⟩
    rw [hΦdef]
    simp only
    rw [dif_pos hex]
    obtain ⟨-, hδτ⟩ := Classical.choose_spec hex
    have h1 : γ • (Classical.choose hex)⁻¹ • v
        = Classical.choose hex • (Classical.choose hex)⁻¹ • v :=
      smul_eq_of_basepoint_eq hfree hδτ.symm _
    rw [smul_inv_smul] at h1
    exact eq_inv_smul_iff.mpr h1
  have hmaps : Set.MapsTo Φ (tileCenters Γ τ₀ v)
      (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀) := by
    rintro c ⟨γ, hγ, rfl⟩
    change Φ (γ • τ₀) ∈ _
    rw [hΦ γ hγ]
    exact ⟨MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, rfl⟩, smul_mem_polygonVertices hv hγ⟩
  have hinj : Set.InjOn Φ (tileCenters Γ τ₀ v) := by
    rintro c₁ ⟨γ₁, hγ₁, rfl⟩ c₂ ⟨γ₂, hγ₂, rfl⟩ he
    have he' : γ₁⁻¹ • v = γ₂⁻¹ • v := by
      rw [← hΦ γ₁ hγ₁, ← hΦ γ₂ hγ₂]
      exact he
    have h1 : (γ₂ * γ₁⁻¹) • v = v := by
      rw [mul_smul, he', smul_inv_smul]
    have h2 := hfree (γ₂ * γ₁⁻¹) ⟨v, h1⟩ (γ₁ • τ₀)
    change γ₁ • τ₀ = γ₂ • τ₀
    rw [← h2, mul_smul, inv_smul_smul]
  have hsurj : Set.SurjOn Φ (tileCenters Γ τ₀ v)
      (MulAction.orbit Γ v ∩ polygonVertices Γ τ₀) := by
    rintro v' ⟨horb, hvert⟩
    obtain ⟨η, hη⟩ := MulAction.mem_orbit_iff.mp horb
    have hcon : η⁻¹ ∈ contactSet Γ τ₀ v := by
      rw [mem_contactSet_iff_mem_smul_dirichletDomain]
      refine ⟨η • v, ?_, ?_⟩
      · rw [hη]
        exact hvert.1
      · change η⁻¹ • η • v = v
        rw [inv_smul_smul]
    refine ⟨η⁻¹ • τ₀, ⟨η⁻¹, hcon, rfl⟩, ?_⟩
    show Φ (η⁻¹ • τ₀) = v'
    rw [hΦ η⁻¹ hcon, inv_inv, hη]
  exact ⟨Φ, ⟨hmaps, hinj, hsurj⟩, hΦ⟩

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-- Every side is contained in the Dirichlet domain. -/
theorem side_subset_dirichletDomain {s : Set UpperHalfPlane}
    (hs : s ∈ polygonSides Γ τ₀) : s ⊆ dirichletDomain Γ τ₀ := by
  obtain ⟨γ, -, rfl⟩ := hs
  exact fun x hx => hx.1

/-- Two distinct sides meet in at most one point. -/
theorem side_inter_subsingleton {s s' : Set UpperHalfPlane}
    (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀) (hne : s ≠ s') :
    (s ∩ s').Subsingleton := by
  obtain ⟨γ, hγ, rfl⟩ := hs
  obtain ⟨δ, hδ, rfl⟩ := hs'
  intro x hx y hy
  by_contra hxy
  exact hne (sideSet_eq_of_basepoint_eq
    (bisector_pair_unique hxy hx.1.2 hy.1.2 hx.2.2 hy.2.2 hγ.1 hδ.1))

/-- The cone over a side stays in the Dirichlet domain. -/
theorem geodCone_side_subset {s : Set UpperHalfPlane}
    (hs : s ∈ polygonSides Γ τ₀) : geodCone τ₀ s ⊆ dirichletDomain Γ τ₀ := by
  intro x hx
  obtain ⟨w, hw, hxw⟩ := mem_geodCone.mp hx
  exact geodConvex_dirichletDomain τ₀ basepoint_mem_dirichletDomain w
    (side_subset_dirichletDomain hs hw) hxw

/-- The Dirichlet domain is not all of the upper half plane. -/
theorem exists_notMem_dirichletDomain {R : ℝ}
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ y : UpperHalfPlane, y ∉ dirichletDomain Γ τ₀ := by
  have hR : 0 ≤ R := le_trans Metric.infDist_nonneg (hdense τ₀)
  have hy : (0 : ℝ) < ((⟨τ₀.re, τ₀.im * Real.exp (R + 1)⟩ : ℂ)).im :=
    mul_pos τ₀.im_pos (Real.exp_pos _)
  set y : UpperHalfPlane := UpperHalfPlane.mk ⟨τ₀.re, τ₀.im * Real.exp (R + 1)⟩ hy with hydef
  refine ⟨y, fun hyD => ?_⟩
  have h1 : dist τ₀ y ≤ R := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hyD)
  have hre : τ₀.re = y.re := rfl
  have him : y.im = τ₀.im * Real.exp (R + 1) := rfl
  have h2 : dist τ₀ y = |Real.log τ₀.im - Real.log y.im| := dist_of_re_eq hre
  rw [him, Real.log_mul τ₀.im_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [show Real.log τ₀.im - (Real.log τ₀.im + (R + 1)) = -(R + 1) by ring, abs_neg,
    abs_of_pos (by linarith)] at h2
  linarith [h1, h2.symm.le]

/-- Of two points beyond a common ray point, the nearer lies on the segment to the
farther. -/
theorem mem_geodSeg_of_ray_le {a x w w' : UpperHalfPlane} (hxa : x ≠ a)
    (hw : x ∈ geodSeg a w) (hw' : x ∈ geodSeg a w') (hle : dist a w ≤ dist a w') :
    w ∈ geodSeg a w' := by
  have hbw : dist a x + dist x w = dist a w := mem_geodSeg.mp hw
  have hbw' : dist a x + dist x w' = dist a w' := mem_geodSeg.mp hw'
  have haw' : a ≠ w' := by
    rintro rfl
    rw [geodSeg_self] at hw'
    exact hxa (Set.mem_singleton_iff.mp hw')
  have hd' : 0 < dist a w' := dist_pos.mpr haw'
  set t : ℝ := dist a w / dist a w' with htdef
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, (div_le_one hd').mpr hle⟩
  set p : UpperHalfPlane := geodInterp a w' t with hpdef
  have hp : p ∈ geodSeg a w' := geodInterp_mem_geodSeg a w' ht
  have hdap : dist a p = dist a w := by
    rw [hpdef, dist_geodInterp_left a w' ht, htdef, div_mul_cancel₀ _ hd'.ne']
  obtain ⟨sx, hsx, hxeq⟩ := (geodSeg_eq_image_geodInterp a w' ▸ hw' :
    x ∈ geodInterp a w' '' Set.Icc (0 : ℝ) 1)
  have hdax : dist a x = sx * dist a w' := by
    rw [← hxeq, dist_geodInterp_left a w' hsx]
  have htd : t * dist a w' = dist a w := by
    rw [htdef]
    exact div_mul_cancel₀ _ hd'.ne'
  have hst : sx ≤ t := by
    by_contra hcon
    have hcon' : t < sx := not_le.mp hcon
    have h1 : t * dist a w' < sx * dist a w' := mul_lt_mul_of_pos_right hcon' hd'
    have := dist_nonneg (x := x) (y := w)
    linarith [htd, hdax.symm.le, hbw]
  have hdxp : dist x p = (t - sx) * dist a w' := by
    rw [← hxeq, hpdef, dist_geodInterp_pair, abs_of_nonpos (by linarith), neg_sub]
  have hexp : (t - sx) * dist a w' = t * dist a w' - sx * dist a w' := by ring
  have hxp : x ∈ geodSeg a p := by
    rw [mem_geodSeg, hdax, hdxp, hdap]
    linarith [htd, hexp]
  have hwp : w = p :=
    collinear_unique (Ne.symm hxa) (Or.inr (Or.inl hbw)) (Or.inr (Or.inl (mem_geodSeg.mp hxp)))
      hdap.symm (by linarith [hbw, hdxp, hdax, htd, hexp])
  rw [hwp]
  exact hp

/-- Every domain point lies on a radial segment from the basepoint to a side point. -/
theorem exists_exit (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {z : UpperHalfPlane} (hz : z ∈ dirichletDomain Γ τ₀) :
    ∃ s ∈ polygonSides Γ τ₀, ∃ w ∈ s, z ∈ geodSeg τ₀ w := by
  by_cases hzτ : z = τ₀
  · obtain ⟨y, hy⟩ := exists_notMem_dirichletDomain hdense
    obtain ⟨w, -, hwfr⟩ := exists_frontier_mem_geodSeg basepoint_mem_dirichletDomain hy
    rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense] at hwfr
    obtain ⟨s, hs, hws⟩ := hwfr
    exact ⟨s, hs, w, hws, by rw [hzτ]; exact left_mem_geodSeg τ₀ w⟩
  · have hd : 0 < dist τ₀ z := dist_pos.mpr (Ne.symm hzτ)
    have hzR : dist τ₀ z ≤ R := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hz)
    set T : ℝ := (R + 1) / dist τ₀ z with hTdef
    have hR : 0 ≤ R := le_trans Metric.infDist_nonneg (hdense τ₀)
    have hTd : T * dist τ₀ z = R + 1 := div_mul_cancel₀ _ hd.ne'
    have hT1 : 1 < T := by
      rw [hTdef]
      exact (one_lt_div hd).mpr (by linarith)
    set y : UpperHalfPlane := geodInterp τ₀ z T with hydef
    have hdy : dist τ₀ y = R + 1 := by
      rw [hydef, dist_geodInterp_left_abs, abs_of_pos (by linarith), hTd]
    have hyD : y ∉ dirichletDomain Γ τ₀ := fun hc => by
      have h1 : dist y τ₀ ≤ R :=
        Metric.mem_closedBall.mp (dirichletDomain_subset_closedBall hdense hc)
      rw [dist_comm] at h1
      linarith [hdy ▸ h1]
    have hzy : z ∈ geodSeg τ₀ y := by
      rw [mem_geodSeg]
      have h2 : dist z y = (T - 1) * dist τ₀ z := by
        conv_lhs => rw [show z = geodInterp τ₀ z 1 from (geodInterp_one τ₀ z).symm]
        rw [hydef, dist_geodInterp_pair, abs_of_nonpos (by linarith), neg_sub]
      rw [h2, hdy]
      linarith [hTd]
    obtain ⟨w, hwseg, hwfr⟩ := exists_frontier_mem_geodSeg hz hyD
    have hzw : z ∈ geodSeg τ₀ w := by
      rw [mem_geodSeg]
      have e1 : dist τ₀ z + dist z y = dist τ₀ y := mem_geodSeg.mp hzy
      have e2 : dist z w + dist w y = dist z y := mem_geodSeg.mp hwseg
      have t1 : dist τ₀ w ≤ dist τ₀ z + dist z w := dist_triangle _ _ _
      have t2 : dist τ₀ y ≤ dist τ₀ w + dist w y := dist_triangle _ _ _
      linarith
    rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense] at hwfr
    obtain ⟨s, hs, hws⟩ := hwfr
    exact ⟨s, hs, w, hws, hzw⟩

/-! ## The fan decomposition -/

/-- **Fan decomposition**: the Dirichlet domain is the union of the geodesic cones from the
basepoint over its sides. -/
theorem dirichletDomain_eq_biUnion_geodCone (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    dirichletDomain Γ τ₀ = ⋃ s ∈ polygonSides Γ τ₀, geodCone τ₀ s := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨s, hs, w, hws, hzw⟩ := exists_exit hΓ hfree hε hgap hdense hz
    exact Set.mem_biUnion hs (mem_geodCone.mpr ⟨w, hws, hzw⟩)
  · intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    exact geodCone_side_subset hs hzs

/-- A common point of two cones away from the apex lies on a radial segment through a
common point of the two sides. -/
theorem geodCone_inter_carrier (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s s' : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀)
    {x : UpperHalfPlane} (hx : x ∈ geodCone τ₀ s) (hx' : x ∈ geodCone τ₀ s')
    (hxτ : x ≠ τ₀) : ∃ p ∈ s ∩ s', x ∈ geodSeg τ₀ p := by
  obtain ⟨w, hws, hxw⟩ := mem_geodCone.mp hx
  obtain ⟨w', hws', hxw'⟩ := mem_geodCone.mp hx'
  have hfr := frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense
  have hwfr : w ∈ frontier (dirichletDomain Γ τ₀) := by rw [hfr]; exact ⟨s, hs, hws⟩
  have hw'fr : w' ∈ frontier (dirichletDomain Γ τ₀) := by rw [hfr]; exact ⟨s', hs', hws'⟩
  rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hwfr hw'fr
  rcases le_total (dist τ₀ w) (dist τ₀ w') with h | h
  · have hseg : w ∈ geodSeg τ₀ w' := mem_geodSeg_of_ray_le hxτ hxw hxw' h
    by_cases hww' : w = w'
    · exact ⟨w, ⟨hws, hww' ▸ hws'⟩, hxw⟩
    · exact absurd (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain hs' hws') hseg hww') hwfr.2
  · have hseg : w' ∈ geodSeg τ₀ w := mem_geodSeg_of_ray_le hxτ hxw' hxw h
    by_cases hww' : w' = w
    · exact ⟨w, ⟨hws, hww' ▸ hws'⟩, hxw⟩
    · exact absurd (mem_interior_of_mem_geodSeg hΓ hdense
        (side_subset_dirichletDomain hs hws) hseg hww') hw'fr.2

/-- Distinct cones of the fan overlap in a null set: their intersection is carried by the
shared boundary rays, which are geodesic segments. -/
theorem volume_geodCone_inter_eq_zero (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s s' : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀)
    (hne : s ≠ s') :
    volume (geodCone τ₀ s ∩ geodCone τ₀ s') = 0 := by
  have hsub := side_inter_subsingleton hs hs' hne
  rcases Set.eq_empty_or_nonempty (s ∩ s') with hemp | ⟨p, hp⟩
  · have h0 : volume ({τ₀} : Set UpperHalfPlane) = 0 := by
      rw [← geodSeg_self τ₀]
      exact volume_geodSeg_eq_zero τ₀ τ₀
    refine measure_mono_null (fun x hx => ?_) h0
    by_cases hxτ : x = τ₀
    · exact hxτ ▸ rfl
    · obtain ⟨q, hq, -⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense hs hs'
        hx.1 hx.2 hxτ
      rw [hemp] at hq
      exact absurd hq (Set.notMem_empty q)
  · refine measure_mono_null (fun x hx => ?_) (volume_geodSeg_eq_zero τ₀ p)
    by_cases hxτ : x = τ₀
    · rw [hxτ]
      exact left_mem_geodSeg τ₀ p
    · obtain ⟨q, hq, hxq⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense hs hs'
        hx.1 hx.2 hxτ
      rw [hsub hq hp] at hxq
      exact hxq

/-- Arguments add absolutely for a product of upper-half-plane factors with upper-half
product. -/
theorem abs_arg_mul_pos {A B : ℂ} (hA : 0 < A.im) (hB : 0 < B.im)
    (hAB : 0 < (A * B).im) : |(A * B).arg| = |A.arg| + |B.arg| := by
  have hA0 : A ≠ 0 := fun h => by rw [h, Complex.zero_im] at hA; exact lt_irrefl 0 hA
  have hB0 : B ≠ 0 := fun h => by rw [h, Complex.zero_im] at hB; exact lt_irrefl 0 hB
  have hπ := Real.pi_pos
  have hbound : ∀ z : ℂ, 0 < z.im → 0 < z.arg ∧ z.arg < Real.pi := by
    intro z hz
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) fun h => ?_,
      lt_of_le_of_ne (Complex.arg_le_pi z) fun h => ?_⟩
    · exact hz.ne (Complex.arg_eq_zero_iff.mp h.symm).2.symm
    · exact hz.ne (Complex.arg_eq_pi_iff.mp h).2.symm
  obtain ⟨hA1, hA2⟩ := hbound A hA
  obtain ⟨hB1, hB2⟩ := hbound B hB
  obtain ⟨hC1, hC2⟩ := hbound (A * B) hAB
  have h2 : (((A * B).arg : ℝ) : Real.Angle) = ((A.arg + B.arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact Complex.arg_mul_coe_angle hA0 hB0
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h2
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < (k : ℝ) := by nlinarith
  have hk0 : k = 0 := by
    have h3 : k < 1 := by exact_mod_cast hk1
    have h4 : -1 < k := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  push_cast at hk
  rw [abs_of_pos hC1, abs_of_pos hA1, abs_of_pos hB1]
  linarith

/-- Conjugation preserves the absolute argument off the real axis. -/
theorem abs_arg_conj_of_im_ne {z : ℂ} (hz : z.im ≠ 0) :
    |((starRingEnd ℂ) z).arg| = |z.arg| := by
  rw [Complex.arg_conj, if_neg fun h => hz (Complex.arg_eq_pi_iff.mp h).2, abs_neg]

/-- Arguments add absolutely for factors on a common side of the real axis whose product
stays on that side. -/
theorem abs_arg_mul_of_same_side {A B : ℂ}
    (h : 0 < A.im ∧ 0 < B.im ∧ 0 < (A * B).im ∨ A.im < 0 ∧ B.im < 0 ∧ (A * B).im < 0) :
    |(A * B).arg| = |A.arg| + |B.arg| := by
  rcases h with ⟨hA, hB, hAB⟩ | ⟨hA, hB, hAB⟩
  · exact abs_arg_mul_pos hA hB hAB
  · have hconj : (starRingEnd ℂ) A * (starRingEnd ℂ) B = (starRingEnd ℂ) (A * B) :=
      (map_mul _ A B).symm
    have h1 : |((starRingEnd ℂ) (A * B)).arg|
        = |((starRingEnd ℂ) A).arg| + |((starRingEnd ℂ) B).arg| := by
      rw [← hconj]
      exact abs_arg_mul_pos (by rw [Complex.conj_im]; linarith)
        (by rw [Complex.conj_im]; linarith)
        (by rw [hconj, Complex.conj_im]; linarith)
    rw [abs_arg_conj_of_im_ne hAB.ne, abs_arg_conj_of_im_ne hA.ne,
      abs_arg_conj_of_im_ne hB.ne] at h1
    exact h1

/-- A sign functional vanishing along a direction is a multiple of the imaginary part in
that frame. -/
theorem functional_ratio {m : ℂ} {e : ℝ} (he : e = 1 ∨ e = -1) {u : ℂ} (hu : u ≠ 0)
    (h0 : e * (m * u).im = 0) (x : ℂ) :
    e * (m * x).im = (e * (m * u).re) * (x / u).im := by
  have him : (m * u).im = 0 := by rcases he with h | h <;> rw [h] at h0 <;> linarith
  have hmu : m * u = (((m * u).re : ℝ) : ℂ) :=
    Complex.ext rfl (by rw [him, Complex.ofReal_im])
  have hx : m * x = (m * u) * (x / u) := by
    rw [mul_assoc, mul_comm u (x / u), div_mul_cancel₀ x hu]
  rw [hx, hmu]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

/-- The segment from a vertex to the basepoint splits the interior angle into the base
angles of the two adjacent cones of the fan. -/
theorem sectorAngle_eq_add_basepoint (_hΓ : IsFuchsianGroup Γ)
    (_hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (_hε : 0 < ε)
    (_hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (_hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (_hv : v ∈ polygonVertices Γ τ₀)
    {s₁ s₂ : Set UpperHalfPlane} (hs₁ : s₁ ∈ polygonSides Γ τ₀)
    (hs₂ : s₂ ∈ polygonSides Γ τ₀) (hne : s₁ ≠ s₂)
    (he₁ : IsSegEndpoint s₁ v) (he₂ : IsSegEndpoint s₂ v)
    {w₁ w₂ : UpperHalfPlane} (hw₁ : w₁ ∈ s₁) (hw₂ : w₂ ∈ s₂)
    (hw₁v : w₁ ≠ v) (hw₂v : w₂ ≠ v) :
    sectorAngle v w₁ w₂ = sectorAngle v w₁ τ₀ + sectorAngle v τ₀ w₂ := by
  have hs₁' := hs₁
  have hs₂' := hs₂
  obtain ⟨γ₁, hγ₁, hs₁def⟩ := hs₁'
  obtain ⟨γ₂, hγ₂, hs₂def⟩ := hs₂'
  have hpq₁ : τ₀ ≠ γ₁ • τ₀ := Ne.symm hγ₁.1
  have hpq₂ : τ₀ ≠ γ₂ • τ₀ := Ne.symm hγ₂.1
  obtain ⟨g₁, ε₁, hε₁, hle₁, hge₁⟩ := bisector_normalizer hpq₁
  obtain ⟨g₂, ε₂, hε₂, hle₂, hge₂⟩ := bisector_normalizer hpq₂
  have hveq₁ : dist v τ₀ = dist v (γ₁ • τ₀) := by
    have h := he₁.1
    rw [hs₁def] at h
    exact h.2
  have hveq₂ : dist v τ₀ = dist v (γ₂ • τ₀) := by
    have h := he₂.1
    rw [hs₂def] at h
    exact h.2
  obtain ⟨m₁, hm₁, hf₁eq, hf₁lt⟩ := functional_sign hε₁ hle₁ hge₁ hveq₁
  obtain ⟨m₂, hm₂, hf₂eq, hf₂lt⟩ := functional_sign hε₂ hle₂ hge₂ hveq₂
  have hssub := side_inter_subsingleton hs₁ hs₂ hne
  have hvmem : v ∈ s₁ ∩ s₂ := ⟨he₁.1, he₂.1⟩
  have hw₁eq : dist w₁ τ₀ = dist w₁ (γ₁ • τ₀) := by
    have h := hw₁
    rw [hs₁def] at h
    exact h.2
  have hw₂eq : dist w₂ τ₀ = dist w₂ (γ₂ • τ₀) := by
    have h := hw₂
    rw [hs₂def] at h
    exact h.2
  have hw₂lt : dist w₂ τ₀ < dist w₂ (γ₁ • τ₀) := by
    have hD : w₂ ∈ dirichletDomain Γ τ₀ := side_subset_dirichletDomain hs₂ hw₂
    rcases lt_or_eq_of_le (hD γ₁) with h | h
    · exact h
    · exact absurd (hssub ⟨by rw [hs₁def]; exact ⟨hD, h⟩, hw₂⟩ hvmem) hw₂v
  have hw₁lt : dist w₁ τ₀ < dist w₁ (γ₂ • τ₀) := by
    have hD : w₁ ∈ dirichletDomain Γ τ₀ := side_subset_dirichletDomain hs₁ hw₁
    rcases lt_or_eq_of_le (hD γ₂) with h | h
    · exact h
    · exact absurd (hssub ⟨hw₁, by rw [hs₂def]; exact ⟨hD, h⟩⟩ hvmem) hw₁v
  have hτlt₁ : dist τ₀ τ₀ < dist τ₀ (γ₁ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq₁
  have hτlt₂ : dist τ₀ τ₀ < dist τ₀ (γ₂ • τ₀) := by
    rw [dist_self]
    exact dist_pos.mpr hpq₂
  have hu₁ : discChart v w₁ ≠ 0 := discChart_ne_zero hw₁v
  have hu₂ : discChart v w₂ ≠ 0 := discChart_ne_zero hw₂v
  have E₁ : ε₁ * (m₁ * discChart v w₁).im = 0 := hf₁eq w₁ hw₁eq
  have E₂ : ε₂ * (m₂ * discChart v w₂).im = 0 := hf₂eq w₂ hw₂eq
  have P12 : 0 < ε₁ * (m₁ * discChart v w₂).im := hf₁lt w₂ hw₂lt
  have P1t : 0 < ε₁ * (m₁ * discChart v τ₀).im := hf₁lt τ₀ hτlt₁
  have P21 : 0 < ε₂ * (m₂ * discChart v w₁).im := hf₂lt w₁ hw₁lt
  have P2t : 0 < ε₂ * (m₂ * discChart v τ₀).im := hf₂lt τ₀ hτlt₂
  have htc : discChart v τ₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at P1t
    simp at P1t
  rw [functional_ratio hε₁ hu₁ E₁ (discChart v w₂)] at P12
  rw [functional_ratio hε₁ hu₁ E₁ (discChart v τ₀)] at P1t
  rw [functional_ratio hε₂ hu₂ E₂ (discChart v w₁)] at P21
  rw [functional_ratio hε₂ hu₂ E₂ (discChart v τ₀)] at P2t
  have hsgn_pp : ∀ a b : ℝ, 0 < a * b → 0 < a → 0 < b := by
    intro a b hab ha
    nlinarith
  have hsgn_nn : ∀ a b : ℝ, 0 < a * b → a < 0 → b < 0 := by
    intro a b hab ha
    nlinarith
  have hsgn_bp : ∀ a b : ℝ, 0 < a * b → 0 < b → 0 < a := by
    intro a b hab hb
    nlinarith
  have hsgn_bn : ∀ a b : ℝ, 0 < a * b → b < 0 → a < 0 := by
    intro a b hab hb
    nlinarith
  have hABeq : discChart v τ₀ / discChart v w₁ * (discChart v w₂ / discChart v τ₀)
      = discChart v w₂ / discChart v w₁ := by
    field_simp
  have hNC : 0 < Complex.normSq (discChart v w₂ / discChart v w₁) :=
    Complex.normSq_pos.mpr (div_ne_zero hu₂ hu₁)
  have hNt : 0 < Complex.normSq (discChart v τ₀ / discChart v w₂) :=
    Complex.normSq_pos.mpr (div_ne_zero htc hu₂)
  have hCinv : (discChart v w₁ / discChart v w₂).im
      = -(discChart v w₂ / discChart v w₁).im
        / Complex.normSq (discChart v w₂ / discChart v w₁) := by
    rw [← inv_div (discChart v w₂) (discChart v w₁), Complex.inv_im]
  have hBinv : (discChart v w₂ / discChart v τ₀).im
      = -(discChart v τ₀ / discChart v w₂).im
        / Complex.normSq (discChart v τ₀ / discChart v w₂) := by
    rw [← inv_div (discChart v τ₀) (discChart v w₂), Complex.inv_im]
  have hCne0 : (discChart v w₂ / discChart v w₁).im ≠ 0 := by
    intro h
    rw [h, mul_zero] at P12
    exact lt_irrefl 0 P12
  have key : 0 < (discChart v τ₀ / discChart v w₁).im
        ∧ 0 < (discChart v w₂ / discChart v τ₀).im
        ∧ 0 < (discChart v w₂ / discChart v w₁).im
      ∨ (discChart v τ₀ / discChart v w₁).im < 0
        ∧ (discChart v w₂ / discChart v τ₀).im < 0
        ∧ (discChart v w₂ / discChart v w₁).im < 0 := by
    rcases lt_or_gt_of_ne hCne0 with hC | hC
    · right
      have hq₁ : ε₁ * (m₁ * discChart v w₁).re < 0 := hsgn_bn _ _ P12 hC
      have hA : (discChart v τ₀ / discChart v w₁).im < 0 := hsgn_nn _ _ P1t hq₁
      have hu₁₂ : 0 < (discChart v w₁ / discChart v w₂).im := by
        rw [hCinv]
        exact div_pos (by linarith) hNC
      have hq₂ : 0 < ε₂ * (m₂ * discChart v w₂).re := hsgn_bp _ _ P21 hu₁₂
      have ht₂ : 0 < (discChart v τ₀ / discChart v w₂).im := hsgn_pp _ _ P2t hq₂
      have hB : (discChart v w₂ / discChart v τ₀).im < 0 := by
        rw [hBinv]
        exact div_neg_of_neg_of_pos (by linarith) hNt
      exact ⟨hA, hB, hC⟩
    · left
      have hq₁ : 0 < ε₁ * (m₁ * discChart v w₁).re := hsgn_bp _ _ P12 hC
      have hA : 0 < (discChart v τ₀ / discChart v w₁).im := hsgn_pp _ _ P1t hq₁
      have hu₁₂ : (discChart v w₁ / discChart v w₂).im < 0 := by
        rw [hCinv]
        exact div_neg_of_neg_of_pos (by linarith) hNC
      have hq₂ : ε₂ * (m₂ * discChart v w₂).re < 0 := hsgn_bn _ _ P21 hu₁₂
      have ht₂ : (discChart v τ₀ / discChart v w₂).im < 0 := hsgn_nn _ _ P2t hq₂
      have hB : 0 < (discChart v w₂ / discChart v τ₀).im := by
        rw [hBinv]
        exact div_pos (by linarith) hNt
      exact ⟨hA, hB, hC⟩
  rw [← hABeq] at key
  have hfinal := abs_arg_mul_of_same_side key
  rw [hABeq] at hfinal
  simp only [sectorAngle]
  exact hfinal

/-- The boundary-walk step on side-vertex darts: switch to the other side through the
vertex, then move to its other endpoint. -/
def stepDart {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d : α × β) : α × β :=
  (oside d.2 d.1, oend (oside d.2 d.1) d.2)

/-- The reversal of a dart: the same side, seen from its other endpoint. -/
def revDart {α β : Type*} (oend : α → β → β) (d : α × β) : α × β :=
  (d.1, oend d.1 d.2)

/-- The orbit of a dart under the boundary-walk step. -/
def dartOrbit {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) (k : ℕ) : α × β :=
  (stepDart oside oend)^[k] d₀

/-- The dart orbit starts at the initial dart. -/
theorem dartOrbit_zero {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) : dartOrbit oside oend d₀ 0 = d₀ :=
  rfl

/-- Each step of the dart orbit applies one boundary-walk step. -/
theorem dartOrbit_succ {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) (k : ℕ) :
    dartOrbit oside oend d₀ (k + 1)
      = stepDart oside oend (dartOrbit oside oend d₀ k) :=
  Function.iterate_succ_apply' _ k d₀

/-- The dart orbit is additive in the step count: walking `m + k` steps is walking `k` and
then iterating the step `m` more times. -/
theorem dartOrbit_add {α β : Type*} (oside : β → α → α) (oend : α → β → β)
    (d₀ : α × β) (m k : ℕ) :
    dartOrbit oside oend d₀ (m + k)
      = (stepDart oside oend)^[m] (dartOrbit oside oend d₀ k) :=
  Function.iterate_add_apply _ m k d₀

/-- A finite connected two-regular side-vertex incidence structure is traversed by a
single closed boundary walk meeting every side exactly once per period. -/
theorem two_regular_cycle {α β : Type*} {SS : Set α} {V : Set β}
    (hfin : SS.Finite) (Endp : α → β → Prop)
    (oend : α → β → β) (oside : β → α → α)
    (hvtx : ∀ s ∈ SS, ∀ v, Endp s v → v ∈ V)
    (hoend : ∀ s ∈ SS, ∀ v, Endp s v →
      Endp s (oend s v) ∧ oend s v ≠ v ∧ oend s (oend s v) = v)
    (htwoend : ∀ s ∈ SS, ∀ v w, Endp s v → Endp s w → w = v ∨ w = oend s v)
    (hoside : ∀ v ∈ V, ∀ s ∈ SS, Endp s v →
      oside v s ∈ SS ∧ oside v s ≠ s ∧ Endp (oside v s) v ∧ oside v (oside v s) = s)
    (hconn : ∀ C : Set α, C ⊆ SS → C.Nonempty →
      (∀ s ∈ C, ∀ v, Endp s v → oside v s ∈ C) → SS ⊆ C)
    {s₀ : α} {v₀ : β} (hs₀ : s₀ ∈ SS) (hv₀ : Endp s₀ v₀) :
    ∃ (n : ℕ) (f : ℕ → α × β), 0 < n ∧ (∀ k, f (k + n) = f k) ∧
      (∀ k, (f k).1 ∈ SS ∧ Endp (f k).1 (f k).2) ∧
      (∀ s ∈ SS, ∃! k, k < n ∧ (f k).1 = s) ∧
      (∀ k, (f (k + 1)).1 = oside (f k).2 (f k).1) := by
  classical
  have hpres : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      (stepDart oside oend d).1 ∈ SS
        ∧ Endp (stepDart oside oend d).1 (stepDart oside oend d).2 := by
    rintro ⟨s, v⟩ hs hv
    have hvV : v ∈ V := hvtx s hs v hv
    obtain ⟨h1, h2, h3, h4⟩ := hoside v hvV s hs hv
    exact ⟨h1, (hoend _ h1 v h3).1⟩
  have hrevmem : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      (revDart oend d).1 ∈ SS
        ∧ Endp (revDart oend d).1 (revDart oend d).2 := by
    rintro ⟨s, v⟩ hs hv
    exact ⟨hs, (hoend s hs v hv).1⟩
  have hrevne : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 → revDart oend d ≠ d := by
    rintro ⟨s, v⟩ hs hv hcon
    exact (hoend s hs v hv).2.1 (congrArg Prod.snd hcon)
  have hrevrev : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      revDart oend (revDart oend d) = d := by
    rintro ⟨s, v⟩ hs hv
    change (s, oend s (oend s v)) = (s, v)
    rw [(hoend s hs v hv).2.2]
  have hconj : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      stepDart oside oend (revDart oend (stepDart oside oend d))
        = revDart oend d := by
    rintro ⟨s, v⟩ hs hv
    have hvV : v ∈ V := hvtx s hs v hv
    obtain ⟨h1, h2, h3, h4⟩ := hoside v hvV s hs hv
    have e1 : oend (oside v s) (oend (oside v s) v) = v := (hoend _ h1 v h3).2.2
    change stepDart oside oend
        (oside v s, oend (oside v s) (oend (oside v s) v)) = (s, oend s v)
    rw [e1]
    change (oside v (oside v s), oend (oside v (oside v s)) v) = (s, oend s v)
    rw [h4]
  have hinj : ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      ∀ d' : α × β, d'.1 ∈ SS → Endp d'.1 d'.2 →
      stepDart oside oend d = stepDart oside oend d' → d = d' := by
    intro d hd1 hd2 d' hd1' hd2' h
    have h1 : revDart oend (stepDart oside oend
        (revDart oend (stepDart oside oend d))) = d := by
      rw [hconj d hd1 hd2]
      exact hrevrev d hd1 hd2
    have h2 : revDart oend (stepDart oside oend
        (revDart oend (stepDart oside oend d'))) = d' := by
      rw [hconj d' hd1' hd2']
      exact hrevrev d' hd1' hd2'
    rw [← h1, ← h2, h]
  set f : ℕ → α × β := dartOrbit oside oend (s₀, v₀) with hfdef
  have hfsucc : ∀ k, f (k + 1) = stepDart oside oend (f k) := fun k =>
    dartOrbit_succ oside oend (s₀, v₀) k
  have hfadd : ∀ m k, f (m + k) = (stepDart oside oend)^[m] (f k) := fun m k =>
    dartOrbit_add oside oend (s₀, v₀) m k
  have hfk : ∀ k, (f k).1 ∈ SS ∧ Endp (f k).1 (f k).2 := by
    intro k
    induction k with
    | zero => exact ⟨hs₀, hv₀⟩
    | succ k ih =>
      rw [hfsucc k]
      exact hpres _ ih.1 ih.2
  have hiterpres : ∀ m, ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      ((stepDart oside oend)^[m] d).1 ∈ SS
        ∧ Endp ((stepDart oside oend)^[m] d).1
            ((stepDart oside oend)^[m] d).2 := by
    intro m
    induction m with
    | zero => intro d hd1 hd2; exact ⟨hd1, hd2⟩
    | succ m ih =>
      intro d hd1 hd2
      rw [Function.iterate_succ_apply]
      exact ih _ (hpres d hd1 hd2).1 (hpres d hd1 hd2).2
  have hiterinj : ∀ m, ∀ d : α × β, d.1 ∈ SS → Endp d.1 d.2 →
      ∀ d' : α × β, d'.1 ∈ SS → Endp d'.1 d'.2 →
      (stepDart oside oend)^[m] d = (stepDart oside oend)^[m] d' → d = d' := by
    intro m
    induction m with
    | zero => intro d _ _ d' _ _ h; exact h
    | succ m ih =>
      intro d hd1 hd2 d' hd1' hd2' h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
      exact hinj d hd1 hd2 d' hd1' hd2'
        (ih _ (hpres d hd1 hd2).1 (hpres d hd1 hd2).2
          _ (hpres d' hd1' hd2').1 (hpres d' hd1' hd2').2 h)
  have hEfin : ∀ s ∈ SS, {v : β | Endp s v}.Finite := by
    intro s hs
    by_cases hex : ∃ v, Endp s v
    · obtain ⟨v₁, hv₁⟩ := hex
      refine ((Set.finite_singleton (oend s v₁)).insert v₁).subset ?_
      intro w hw
      rcases htwoend s hs v₁ w hv₁ hw with h | h
      · rw [h]
        exact Set.mem_insert _ _
      · rw [h]
        exact Set.mem_insert_of_mem _ rfl
    · exact Set.finite_empty.subset (fun w hw => absurd ⟨w, hw⟩ hex)
  have hDtfin : {d : α × β | d.1 ∈ SS ∧ Endp d.1 d.2}.Finite := by
    refine (hfin.biUnion (fun s hs => (hEfin s hs).image (fun v => (s, v)))).subset ?_
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    exact Set.mem_biUnion hs ⟨v, hv, rfl⟩
  have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
    have hmaps : Set.MapsTo f Set.univ {d : α × β | d.1 ∈ SS ∧ Endp d.1 d.2} :=
      fun k _ => ⟨(hfk k).1, (hfk k).2⟩
    obtain ⟨i, -, j, -, hij, hfij⟩ :=
      Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hDtfin
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hfij⟩
    · exact ⟨j, i, h, hfij.symm⟩
  have hret : ∃ k, 0 < k ∧ f k = (s₀, v₀) := by
    obtain ⟨i, j, hij, hfij⟩ := hrep
    have h2 : f j = (stepDart oside oend)^[i] (f (j - i)) := by
      rw [← hfadd i (j - i)]
      congr 1
      omega
    have h3 : (stepDart oside oend)^[i] (f 0)
        = (stepDart oside oend)^[i] (f (j - i)) := by
      rw [← hfadd i 0]
      rw [show i + 0 = i from rfl, hfij, h2]
    have h4 : f 0 = f (j - i) :=
      hiterinj i _ (hfk 0).1 (hfk 0).2 _ (hfk (j - i)).1 (hfk (j - i)).2 h3
    exact ⟨j - i, by omega, h4.symm⟩
  set n : ℕ := Nat.find hret with hndef
  obtain ⟨hn0, hnfix⟩ : 0 < n ∧ f n = (s₀, v₀) := Nat.find_spec hret
  have hper : ∀ k, f (k + n) = f k := by
    intro k
    rw [hfadd k n, hnfix]
    exact (hfadd k 0).symm.trans (by rw [show k + 0 = k from rfl])
  have hkey0 : ∀ a b, a < b → b < n → f a = f b → False := by
    intro a b hab hbn hfab
    have h2 : f b = (stepDart oside oend)^[a] (f (b - a)) := by
      rw [← hfadd a (b - a)]
      congr 1
      omega
    have h3 : (stepDart oside oend)^[a] (f 0)
        = (stepDart oside oend)^[a] (f (b - a)) := by
      rw [← hfadd a 0, show a + 0 = a from rfl, hfab, h2]
    have h4 : f 0 = f (b - a) :=
      hiterinj a _ (hfk 0).1 (hfk 0).2 _ (hfk (b - a)).1 (hfk (b - a)).2 h3
    exact Nat.find_min hret (show b - a < n by omega) ⟨by omega, h4.symm⟩
  have hinjres : ∀ a b, a < n → b < n → f a = f b → a = b := by
    intro a b ha hb hab
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hkey0 a b h hb hab
    · exact hkey0 b a h ha hab.symm
  have hmod : ∀ q r, f (r + q * n) = f r := by
    intro q
    induction q with
    | zero => intro r; rw [Nat.zero_mul, Nat.add_zero]
    | succ q ih =>
      intro r
      rw [show r + (q + 1) * n = (r + q * n) + n from by ring, hper, ih]
  have hmodlt : ∀ k, f (k % n) = f k := by
    intro k
    conv_rhs => rw [show k = k % n + (k / n) * n from (Nat.mod_add_div' k n).symm]
    rw [hmod]
  have hriter : ∀ m k,
      (stepDart oside oend)^[m] (revDart oend (f (k + m)))
        = revDart oend (f k) := by
    intro m
    induction m with
    | zero =>
      intro k
      rw [Nat.add_zero]
      rfl
    | succ m ih =>
      intro k
      rw [show k + (m + 1) = (k + m) + 1 from by omega, hfsucc (k + m),
        Function.iterate_succ_apply, hconj _ (hfk (k + m)).1 (hfk (k + m)).2]
      exact ih k
  have hkey2 : ∀ i j, i < j → j < n → f j = revDart oend (f i) → False := by
    intro i j hij hjn hji
    have hstepm : ∀ m, m ≤ n → revDart oend (f (i + m)) = f (j + n - m) := by
      intro m hm
      have h1 : (stepDart oside oend)^[m] (revDart oend (f (i + m))) = f j :=
        (hriter m i).trans hji.symm
      have h2 : (stepDart oside oend)^[m] (f (j + n - m)) = f j := by
        rw [← hfadd m (j + n - m), show m + (j + n - m) = j + n from by omega, hper]
      have hd1 := hrevmem _ (hfk (i + m)).1 (hfk (i + m)).2
      exact hiterinj m _ hd1.1 hd1.2 _ (hfk (j + n - m)).1 (hfk (j + n - m)).2
        (h1.trans h2.symm)
    rcases Nat.even_or_odd (j - i) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h5 := hstepm m (by omega)
      rw [show j + n - m = (i + m) + n from by omega, hper] at h5
      exact hrevne _ (hfk (i + m)).1 (hfk (i + m)).2 h5
    · have h5 := hstepm (m + 1) (by omega)
      rw [show j + n - (m + 1) = (i + m) + n from by omega, hper] at h5
      rw [show i + (m + 1) = (i + m) + 1 from by omega, hfsucc (i + m)] at h5
      have h8 : (stepDart oside oend (f (i + m))).1 = (f (i + m)).1 := by
        have := congrArg Prod.fst h5
        exact this
      obtain ⟨hs, hv⟩ := hfk (i + m)
      have hvV := hvtx _ hs _ hv
      exact (hoside _ hvV _ hs hv).2.1 h8
  have hnodouble : ∀ i j, i < n → j < n → (f i).1 = (f j).1 → i = j := by
    intro i j hi hj hside
    by_contra hne'
    have hvne : (f i).2 ≠ (f j).2 := by
      intro h
      exact hne' (hinjres i j hi hj (Prod.ext hside h))
    have hrel : f j = revDart oend (f i) := by
      rcases htwoend _ (hfk i).1 (f i).2 (f j).2 (hfk i).2
        (by rw [hside]; exact (hfk j).2) with h | h
      · exact absurd h.symm hvne
      · exact Prod.ext hside.symm h
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hkey2 i j h hj hrel
    · have hrel' : f i = revDart oend (f j) := by
        rw [hrel, hrevrev _ (hfk i).1 (hfk i).2]
      exact hkey2 j i h hi hrel'
  have hCsub : (fun k => (f k).1) '' Set.Iio n ⊆ SS := by
    rintro s ⟨k, -, rfl⟩
    exact (hfk k).1
  have hCne : ((fun k => (f k).1) '' Set.Iio n).Nonempty := ⟨(f 0).1, 0, hn0, rfl⟩
  have hCclosed : ∀ s ∈ (fun k => (f k).1) '' Set.Iio n, ∀ v, Endp s v →
      oside v s ∈ (fun k => (f k).1) '' Set.Iio n := by
    rintro s ⟨k, hk, rfl⟩ v hv
    rcases htwoend _ (hfk k).1 _ v (hfk k).2 hv with h | h
    · refine ⟨(k + 1) % n, Nat.mod_lt _ hn0, ?_⟩
      change (f ((k + 1) % n)).1 = oside v (f k).1
      rw [congrArg Prod.fst (hmodlt (k + 1)), hfsucc k, h]
      rfl
    · have hstepk : stepDart oside oend (f (k + n - 1)) = f k := by
        rw [← hfsucc (k + n - 1), show (k + n - 1) + 1 = k + n from by omega, hper]
      obtain ⟨hs', hv'⟩ := hfk (k + n - 1)
      have hv'V := hvtx _ hs' _ hv'
      obtain ⟨ho1, ho2, ho3, ho4⟩ := hoside _ hv'V _ hs' hv'
      have hfst : (f k).1 = oside (f (k + n - 1)).2 (f (k + n - 1)).1 :=
        (congrArg Prod.fst hstepk).symm
      have hsnd : (f k).2 = oend (f k).1 (f (k + n - 1)).2 := by
        conv_lhs => rw [← hstepk]
        conv_rhs => rw [← hstepk]
        rfl
      have hEnd' : Endp (f k).1 (f (k + n - 1)).2 := by
        rw [hfst]
        exact ho3
      have hvd : v = (f (k + n - 1)).2 := by
        rw [h, hsnd, (hoend _ (hfk k).1 _ hEnd').2.2]
      have hgoal : oside v (f k).1 = (f (k + n - 1)).1 := by
        rw [hvd, hfst, ho4]
      refine ⟨(k + n - 1) % n, Nat.mod_lt _ hn0, ?_⟩
      change (f ((k + n - 1) % n)).1 = oside v (f k).1
      rw [congrArg Prod.fst (hmodlt (k + n - 1)), hgoal]
  have hall : SS ⊆ (fun k => (f k).1) '' Set.Iio n :=
    hconn _ hCsub hCne hCclosed
  refine ⟨n, f, hn0, hper, hfk, ?_, ?_⟩
  · intro s hs
    obtain ⟨k, hk, hks⟩ := hall hs
    refine ⟨k, ⟨Set.mem_Iio.mp hk, hks⟩, ?_⟩
    rintro k' ⟨hk', hks'⟩
    exact hnodouble k' k hk' (Set.mem_Iio.mp hk) (hks'.trans hks.symm)
  · intro k
    rw [hfsucc k]
    rfl

/-- The basepoint lies on no side. -/
theorem basepoint_notMem_side (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) : τ₀ ∉ s := by
  intro hcon
  have hfr : τ₀ ∈ frontier (dirichletDomain Γ τ₀) := by
    rw [frontier_dirichletDomain_eq_sUnion hΓ hfree hε hgap hdense]
    exact ⟨s, hs, hcon⟩
  rw [(isClosed_dirichletDomain Γ τ₀).frontier_eq] at hfr
  exact hfr.2 (basepoint_mem_interior_dirichletDomain hε hgap)

/-- A common point of two distinct sides is a vertex and an endpoint of both. -/
theorem shared_point_endpoint (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s s' : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) (hs' : s' ∈ polygonSides Γ τ₀)
    (hne : s ≠ s') {p : UpperHalfPlane} (hp : p ∈ s) (hp' : p ∈ s') :
    p ∈ polygonVertices Γ τ₀ ∧ IsSegEndpoint s p ∧ IsSegEndpoint s' p := by
  have hpv : p ∈ polygonVertices Γ τ₀ := by
    obtain ⟨γ, hγ, hsdef⟩ := hs
    obtain ⟨δ, hδ, hsdef'⟩ := hs'
    have hpS : p ∈ dirichletSideSet Γ τ₀ γ := hsdef ▸ hp
    have hpS' : p ∈ dirichletSideSet Γ τ₀ δ := hsdef' ▸ hp'
    have hγδ : γ • τ₀ ≠ δ • τ₀ := fun h =>
      hne (by rw [hsdef, hsdef', sideSet_eq_of_basepoint_eq h])
    have hfin : (tileCenters Γ τ₀ p).Finite := (finite_contactSet hΓ τ₀ p).image _
    refine ⟨hpS.1, (Set.two_lt_ncard hfin).mpr
      ⟨τ₀, ⟨1, one_mem_contactSet hpS.1, one_smul _ _⟩,
        γ • τ₀, ⟨γ, mem_contactSet_of_mem_sideSet hpS, rfl⟩,
        δ • τ₀, ⟨δ, mem_contactSet_of_mem_sideSet hpS', rfl⟩,
        Ne.symm hγ.1, Ne.symm hδ.1, hγδ⟩⟩
  exact ⟨hpv, isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hpv hs hp,
    isSegEndpoint_of_vertex hΓ hfree hε hgap hdense hpv hs' hp'⟩

/-- Cones over sides are closed. -/
theorem isClosed_geodCone_side (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {s : Set UpperHalfPlane} (hs : s ∈ polygonSides Γ τ₀) :
    IsClosed (geodCone τ₀ s) := by
  obtain ⟨a, b, hab, heq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  rw [heq]
  exact (isCompact_hyperbolicTriangle τ₀ a b).isClosed

/-- A nonempty family of sides closed under passing to the second side at any endpoint
exhausts the sides. -/
theorem sides_connected (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    (oside : UpperHalfPlane → Set UpperHalfPlane → Set UpperHalfPlane)
    (huniq : ∀ v ∈ polygonVertices Γ τ₀, ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v →
      ∀ s' ∈ polygonSides Γ τ₀, IsSegEndpoint s' v → s' ≠ s → s' = oside v s)
    (C : Set (Set UpperHalfPlane)) (hCsub : C ⊆ polygonSides Γ τ₀) (hCne : C.Nonempty)
    (hCcl : ∀ s ∈ C, ∀ v, IsSegEndpoint s v → oside v s ∈ C) :
    polygonSides Γ τ₀ ⊆ C := by
  classical
  intro sx hsx
  by_contra hsC
  have hr : 0 < ε / 2 := by linarith
  have hAcl : IsClosed (⋃ t ∈ C, geodCone τ₀ t) :=
    Set.Finite.isClosed_biUnion
      ((finite_polygonSides hΓ hfree hε hgap hdense).subset hCsub)
      (fun t ht => isClosed_geodCone_side hΓ hfree hε hgap hdense (hCsub ht))
  have hBcl : IsClosed (⋃ t ∈ polygonSides Γ τ₀ \ C, geodCone τ₀ t) :=
    Set.Finite.isClosed_biUnion
      ((finite_polygonSides hΓ hfree hε hgap hdense).subset fun t ht => ht.1)
      (fun t ht => isClosed_geodCone_side hΓ hfree hε hgap hdense ht.1)
  have hcov : Metric.ball τ₀ (ε / 2) \ {τ₀} ⊆
      (⋃ t ∈ C, geodCone τ₀ t) ∪ ⋃ t ∈ polygonSides Γ τ₀ \ C, geodCone τ₀ t := by
    rintro x ⟨hxB, -⟩
    have hxD : x ∈ dirichletDomain Γ τ₀ := ball_subset_dirichletDomain hε hgap hxB
    rw [dirichletDomain_eq_biUnion_geodCone hΓ hfree hε hgap hdense] at hxD
    rw [Set.mem_iUnion₂] at hxD
    obtain ⟨t, ht, hxt⟩ := hxD
    by_cases htC : t ∈ C
    · exact Or.inl (Set.mem_biUnion htC hxt)
    · exact Or.inr (Set.mem_biUnion ⟨ht, htC⟩ hxt)
  have hdisj : (⋃ t ∈ C, geodCone τ₀ t) ∩
      (⋃ t ∈ polygonSides Γ τ₀ \ C, geodCone τ₀ t) ⊆ {τ₀} := by
    rintro x ⟨hxA, hxB⟩
    rw [Set.mem_iUnion₂] at hxA hxB
    obtain ⟨t, htC, hxt⟩ := hxA
    obtain ⟨t', ht', hxt'⟩ := hxB
    by_contra hxτ
    have hxτ' : x ≠ τ₀ := fun h => hxτ (h ▸ rfl)
    have htne : t ≠ t' := fun h => ht'.2 (h ▸ htC)
    obtain ⟨p, ⟨hpt, hpt'⟩, -⟩ := geodCone_inter_carrier hΓ hfree hε hgap hdense
      (hCsub htC) ht'.1 hxt hxt' hxτ'
    obtain ⟨hpv, hpe, hpe'⟩ := shared_point_endpoint hΓ hfree hε hgap hdense
      (hCsub htC) ht'.1 htne hpt hpt'
    have ht'os : t' = oside p t :=
      huniq p hpv t (hCsub htC) hpe t' ht'.1 hpe' (Ne.symm htne)
    exact ht'.2 (ht'os ▸ hCcl t htC p hpe)
  have hpick : ∀ t ∈ polygonSides Γ τ₀,
      ((geodCone τ₀ t) ∩ (Metric.ball τ₀ (ε / 2) \ {τ₀})).Nonempty := by
    intro t ht
    obtain ⟨a, b, hab, heq⟩ := exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense ht
    have haT : a ∈ t := by rw [heq]; exact left_mem_geodSeg a b
    have haτ : a ≠ τ₀ := fun h =>
      basepoint_notMem_side hΓ hfree hε hgap hdense ht (h ▸ haT)
    obtain ⟨w, hwseg, hwτ, hwd⟩ := exists_near_on_geodSeg haτ hr
    refine ⟨w, mem_geodCone.mpr ⟨a, haT, by rwa [geodSeg_comm]⟩,
      Metric.mem_ball.mpr hwd, fun hc => hwτ (Set.mem_singleton_iff.mp hc)⟩
  obtain ⟨t₀, ht₀⟩ := hCne
  obtain ⟨wA, hwA1, hwA2⟩ := hpick t₀ (hCsub ht₀)
  obtain ⟨wB, hwB1, hwB2⟩ := hpick sx hsx
  exact punctured_ball_two_closed hr hAcl hBcl hcov hdisj
    ⟨wA, Set.mem_biUnion ht₀ hwA1, hwA2⟩ ⟨wB, Set.mem_biUnion ⟨hsx, hsC⟩ hwB1, hwB2⟩

/-- **Cyclic boundary order**: the sides admit a cyclic enumeration in which consecutive
sides share an endpoint vertex. -/
theorem exists_boundary_side_cycle (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ (n : ℕ) (e : ℕ → Set UpperHalfPlane), 0 < n ∧ (∀ k, e (k + n) = e k) ∧
      (∀ k, e k ∈ polygonSides Γ τ₀) ∧
      (∀ s ∈ polygonSides Γ τ₀, ∃! k, k < n ∧ e k = s) ∧
      ∀ k, ∃ v ∈ polygonVertices Γ τ₀, IsSegEndpoint (e k) v ∧ IsSegEndpoint (e (k + 1)) v := by
  classical
  have hends := fun s (hs : s ∈ polygonSides Γ τ₀) =>
    exists_geodSeg_of_polygonSide hΓ hfree hε hgap hdense hs
  choose! ep1 ep2 hepne hepeq using hends
  have htwo := fun v (hv : v ∈ polygonVertices Γ τ₀) =>
    exists_two_sides_at_vertex hΓ hfree hε hgap hdense hv
  choose! t1 ht1 t2 ht2 h12 hbe1 hbe2 hbuniq using htwo
  set oendF : Set UpperHalfPlane → UpperHalfPlane → UpperHalfPlane :=
    fun s v => if v = ep1 s then ep2 s else ep1 s with hoendF
  set osideF : UpperHalfPlane → Set UpperHalfPlane → Set UpperHalfPlane :=
    fun v s => if s = t1 v then t2 v else t1 v with hosideF
  have hoendF1 : ∀ s v, v = ep1 s → oendF s v = ep2 s := by
    intro s v h
    simp only [hoendF]
    rw [if_pos h]
  have hoendF2 : ∀ s v, v ≠ ep1 s → oendF s v = ep1 s := by
    intro s v h
    simp only [hoendF]
    rw [if_neg h]
  have hosideF1 : ∀ v s, s = t1 v → osideF v s = t2 v := by
    intro v s h
    simp only [hosideF]
    rw [if_pos h]
  have hosideF2 : ∀ v s, s ≠ t1 v → osideF v s = t1 v := by
    intro v s h
    simp only [hosideF]
    rw [if_neg h]
  have hEiff : ∀ s ∈ polygonSides Γ τ₀, ∀ v : UpperHalfPlane,
      IsSegEndpoint s v ↔ (v = ep1 s ∨ v = ep2 s) := by
    intro s hs v
    conv_lhs => rw [hepeq s hs]
    exact isSegEndpoint_geodSeg_iff (hepne s hs)
  have hvtxP : ∀ s ∈ polygonSides Γ τ₀, ∀ v, IsSegEndpoint s v →
      v ∈ polygonVertices Γ τ₀ :=
    fun s hs v hv => mem_polygonVertices_of_isSegEndpoint hΓ hfree hε hgap hdense hs hv
  have hoendP : ∀ s ∈ polygonSides Γ τ₀, ∀ v, IsSegEndpoint s v →
      IsSegEndpoint s (oendF s v) ∧ oendF s v ≠ v ∧ oendF s (oendF s v) = v := by
    intro s hs v hv
    have hne := hepne s hs
    by_cases h1 : v = ep1 s
    · rw [hoendF1 s v h1]
      refine ⟨(hEiff s hs _).mpr (Or.inr rfl), by rw [h1]; exact Ne.symm hne, ?_⟩
      rw [hoendF2 s (ep2 s) (Ne.symm hne), h1]
    · have h2 : v = ep2 s := ((hEiff s hs v).mp hv).resolve_left h1
      rw [hoendF2 s v h1]
      refine ⟨(hEiff s hs _).mpr (Or.inl rfl), by rw [h2]; exact hne, ?_⟩
      rw [hoendF1 s (ep1 s) rfl, h2]
  have htwoendP : ∀ s ∈ polygonSides Γ τ₀, ∀ v w, IsSegEndpoint s v → IsSegEndpoint s w →
      w = v ∨ w = oendF s v := by
    intro s hs v w hv hw
    rcases (hEiff s hs v).mp hv with h1 | h1 <;> rcases (hEiff s hs w).mp hw with h2 | h2
    · exact Or.inl (h2.trans h1.symm)
    · refine Or.inr ?_
      rw [hoendF1 s v h1, h2]
    · refine Or.inr ?_
      rw [hoendF2 s v (fun hc => (hepne s hs) (hc.symm.trans h1)), h2]
    · exact Or.inl (h2.trans h1.symm)
  have hosideP : ∀ v ∈ polygonVertices Γ τ₀, ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v →
      osideF v s ∈ polygonSides Γ τ₀ ∧ osideF v s ≠ s ∧ IsSegEndpoint (osideF v s) v ∧
        osideF v (osideF v s) = s := by
    intro v hv s hs hEnd
    by_cases h1 : s = t1 v
    · rw [hosideF1 v s h1]
      refine ⟨ht2 v hv, by rw [h1]; exact Ne.symm (h12 v hv), hbe2 v hv, ?_⟩
      rw [hosideF2 v (t2 v) (Ne.symm (h12 v hv)), h1]
    · have h2 : s = t2 v := (hbuniq v hv s hs hEnd).resolve_left h1
      rw [hosideF2 v s h1]
      refine ⟨ht1 v hv, by rw [h2]; exact h12 v hv, hbe1 v hv, ?_⟩
      rw [hosideF1 v (t1 v) rfl, h2]
  have hosuniq : ∀ v ∈ polygonVertices Γ τ₀, ∀ s ∈ polygonSides Γ τ₀, IsSegEndpoint s v →
      ∀ s' ∈ polygonSides Γ τ₀, IsSegEndpoint s' v → s' ≠ s → s' = osideF v s := by
    intro v hv s hs hE s' hs' hE' hne'
    rcases hbuniq v hv s hs hE with h1 | h1 <;>
      rcases hbuniq v hv s' hs' hE' with h2 | h2
    · exact absurd (h2.trans h1.symm) hne'
    · rw [hosideF1 v s h1, h2]
    · rw [hosideF2 v s (fun hc => h12 v hv (hc.symm.trans h1)), h2]
    · exact absurd (h2.trans h1.symm) hne'
  obtain ⟨s₀, hs₀, -, -, -⟩ :=
    exists_exit hΓ hfree hε hgap hdense basepoint_mem_dirichletDomain
  have hv₀ : IsSegEndpoint s₀ (ep1 s₀) := (hEiff s₀ hs₀ _).mpr (Or.inl rfl)
  obtain ⟨n, F, hn0, hper, hdart, hexu, hstep⟩ :=
    two_regular_cycle (finite_polygonSides hΓ hfree hε hgap hdense) IsSegEndpoint
      oendF osideF hvtxP hoendP htwoendP hosideP
      (sides_connected hΓ hfree hε hgap hdense osideF hosuniq) hs₀ hv₀
  refine ⟨n, fun k => (F k).1, hn0, fun k => congrArg Prod.fst (hper k),
    fun k => (hdart k).1, fun s hs => hexu s hs, ?_⟩
  intro k
  refine ⟨(F k).2, hvtxP _ (hdart k).1 _ (hdart k).2, (hdart k).2, ?_⟩
  change IsSegEndpoint (F (k + 1)).1 (F k).2
  rw [hstep k]
  exact (hosideP _ (hvtxP _ (hdart k).1 _ (hdart k).2) _ (hdart k).1 (hdart k).2).2.2.1

/-- A special linear matrix squaring to the identity is central: `A² = 1` forces `A = ±1`. -/
theorem eq_pm_one_of_sq_eq_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) = 1) :
    (A : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (A : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, (A : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe A
    rwa [hM, Matrix.det_fin_two_of] at h1
  rw [hM, Matrix.mul_fin_two] at h
  have h00 : a * a + b * c = 1 := by
    have h2 := congrFun (congrFun h 0) 0
    simpa using h2
  have h01 : a * b + b * d = 0 := by
    have h2 := congrFun (congrFun h 0) 1
    simpa using h2
  have h10 : c * a + d * c = 0 := by
    have h2 := congrFun (congrFun h 1) 0
    simpa using h2
  have h11 : c * b + d * d = 1 := by
    have h2 := congrFun (congrFun h 1) 1
    simpa using h2
  by_cases had : a + d = 0
  · exfalso
    nlinarith [h00, hdet, sq_nonneg (a - d), sq_nonneg (a + d)]
  · have hb : b = 0 := by
      have h2 : b * (a + d) = 0 := by linarith [h01]
      exact (mul_eq_zero.mp h2).resolve_right had
    have hc : c = 0 := by
      have h2 : c * (a + d) = 0 := by linarith [h10]
      exact (mul_eq_zero.mp h2).resolve_right had
    rw [hb, hc] at h00 h11 hdet
    have ha1 : a = 1 ∨ a = -1 := by
      rcases mul_self_eq_one_iff.mp (by linarith [h00] : a * a = 1) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr h3
    have hda : d = a := by
      rcases ha1 with h3 | h3 <;> nlinarith [hdet, h11]
    rcases ha1 with h3 | h3
    · left
      rw [hM, hb, hc, hda, h3, ← Matrix.one_fin_two]
    · right
      rw [hM, hb, hc, hda, h3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_fin_two]

/-- A special linear matrix squaring to minus the identity is elliptic: it fixes a point of
the upper half plane. -/
theorem exists_fixed_of_sq_eq_neg_one (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ) * (A : Matrix (Fin 2) (Fin 2) ℝ) = -1) :
    ∃ τ : UpperHalfPlane, A • τ = τ := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d, (A : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe A
    rwa [hM, Matrix.det_fin_two_of] at h1
  rw [hM, Matrix.mul_fin_two] at h
  have h00 : a * a + b * c = -1 := by
    have h2 := congrFun (congrFun h 0) 0
    simpa using h2
  have h01 : a * b + b * d = 0 := by
    have h2 := congrFun (congrFun h 0) 1
    simpa using h2
  have h10 : c * a + d * c = 0 := by
    have h2 := congrFun (congrFun h 1) 0
    simpa using h2
  have had : a + d = 0 := by
    by_contra had
    have hb : b = 0 := by
      have h2 : b * (a + d) = 0 := by linarith [h01]
      exact (mul_eq_zero.mp h2).resolve_right had
    have hc : c = 0 := by
      have h2 : c * (a + d) = 0 := by linarith [h10]
      exact (mul_eq_zero.mp h2).resolve_right had
    rw [hb, hc] at h00
    nlinarith [h00, sq_nonneg a]
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0] at h00 hdet
    nlinarith [h00, sq_nonneg a, hdet]
  have habs : 0 < |c| := abs_pos.mpr hc
  have hy₀ : (0 : ℝ) < 1 / |c| := by positivity
  have hz : (0 : ℝ) < ((⟨a / c, 1 / |c|⟩ : ℂ)).im := hy₀
  set τz : UpperHalfPlane := UpperHalfPlane.mk ⟨a / c, 1 / |c|⟩ hz with hτz
  have hcoez : (τz : ℂ) = ⟨a / c, 1 / |c|⟩ := rfl
  refine ⟨τz, ?_⟩
  have hA00 : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = a := by rw [hM]; rfl
  have hA01 : (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b := by rw [hM]; rfl
  have hA10 : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = c := by rw [hM]; rfl
  have hA11 : (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = d := by rw [hM]; rfl
  have hden : ((c : ℝ) : ℂ) * (τz : ℂ) + ((d : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, zero_mul, add_zero] at h1
    rw [hcoez] at h1
    have h2 : c * (1 / |c|) = 0 := by simpa using h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact absurd h3 (by positivity)
  apply UpperHalfPlane.ext
  rw [coe_smul, hA00, hA01, hA10, hA11, div_eq_iff hden]
  have hZ : (τz : ℂ) = ((a / c : ℝ) : ℂ) + ((1 / |c| : ℝ) : ℂ) * Complex.I := by
    rw [hcoez]
    apply Complex.ext
    · simp
    · simp only [one_div, Complex.ofReal_div, Complex.ofReal_inv, Complex.add_im,
        Complex.div_ofReal_im, Complex.ofReal_im, zero_div, Complex.mul_im, Complex.inv_re,
        Complex.ofReal_re, Complex.normSq_ofReal, abs_mul_abs_self, Complex.I_im, mul_one,
        Complex.inv_im, neg_zero, Complex.I_re, mul_zero, add_zero, zero_add]
      rw [← abs_mul_abs_self c]
      field_simp
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  have h₁ : ((c : ℝ) : ℂ) * ((a / c : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  have h₂ : ((c : ℝ) : ℂ) ^ 2 * ((1 / |c| : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [show c ^ 2 * (1 / |c|) ^ 2 = c ^ 2 / |c| ^ 2 by ring, sq_abs]
    rw [div_self (by positivity : c ^ 2 ≠ (0 : ℝ))]
    norm_num
  have h₃ : ((b : ℝ) : ℂ) * ((c : ℝ) : ℂ) = -1 - ((a : ℝ) : ℂ) * ((a : ℝ) : ℂ) := by
    have hbc : b * c = -1 - a * a := by linarith [h00]
    rw [← Complex.ofReal_mul, hbc]
    push_cast
    ring
  have h₄ : ((d : ℝ) : ℂ) = -((a : ℝ) : ℂ) := by
    have : d = -a := by linarith [had]
    rw [this]
    push_cast
    ring
  have hI : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  refine mul_left_cancel₀ hcC ?_
  rw [hZ, h₄]
  linear_combination (-(((c : ℝ) : ℂ) * ((a / c : ℝ) : ℂ) - ((a : ℝ) : ℂ))
      - 2 * ((c : ℝ) : ℂ) * ((1 / |c| : ℝ) : ℂ) * Complex.I) * h₁
    + h₃ + (-(Complex.I ^ 2)) * h₂ + (-1) * hI

end RiemannDynamics
