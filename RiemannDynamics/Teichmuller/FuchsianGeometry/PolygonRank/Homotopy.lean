/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.FuchsianGeometry.PolygonRank.Basic

/-!
# The rank identity: the crossing-sum homomorphism via the homotopy grid

Crossing sums of a cycle-constrained odd side function vanish on all closed tile paths:
a closed tile loop contracts to the basepoint through the star covering of the compact
homotopy square, and each elementary contraction is controlled by the star calculus.

* `starVal_square` and row invariance of star-value sums over the grid.
* `piece` — the piece lemma: a single crossing, homotoped onto the basepoint over a
  sufficiently fine even grid, is the difference of two junction column sums.
* `crossingSum_eq_zero_of_closed` — crossing sums vanish on all closed tile paths.
* `exists_crossingSum_hom` — integration of a constrained odd side function into an
  additive character along tile paths.
* `loopList` and `closed_loop_sum` — periodic loop lists and their crossing sums.
-/

open scoped ENNReal

namespace RiemannDynamics

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {τ₀ : UpperHalfPlane}

/-! ## The grid: row invariance of star-value sums -/

/-- The four-tile square identity at a fixed star. -/
theorem starVal_square (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {z : UpperHalfPlane} {a b c d : ↥Γ} (ha : a ∈ contactSet Γ τ₀ z)
    (hb : b ∈ contactSet Γ τ₀ z) (hc : c ∈ contactSet Γ τ₀ z)
    (hd : d ∈ contactSet Γ τ₀ z) :
    starVal Γ τ₀ α z c d - starVal Γ τ₀ α z a b
      = starVal Γ τ₀ α z b d - starVal Γ τ₀ α z a c := by
  have h1 := starVal_trans hΓ hfree hε hgap hdense hα ha hc hd
  have h2 := starVal_trans hΓ hfree hε hgap hdense hα ha hb hd
  linarith

/-- **Row invariance on a grid**: on an `(m+1) × (n+1)` grid of squares with centers `z`
and node tiles `G`, with the four corner tiles of each square in its star, vertical edges
recentered across horizontal neighbors and horizontal edges recentered across vertical
neighbors, the top row sum differs from the bottom row sum by the column sums. -/
theorem grid_rows (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    (m n : ℕ) (z : ℕ → ℕ → UpperHalfPlane) (G : ℕ → ℕ → ↥Γ)
    (h4 : ∀ i ≤ m, ∀ l ≤ n, G i l ∈ contactSet Γ τ₀ (z i l) ∧
      G i (l + 1) ∈ contactSet Γ τ₀ (z i l) ∧ G (i + 1) l ∈ contactSet Γ τ₀ (z i l) ∧
      G (i + 1) (l + 1) ∈ contactSet Γ τ₀ (z i l))
    (hvert : ∀ i ≤ m, ∀ l, l < n → starVal Γ τ₀ α (z i l) (G i (l + 1))
        (G (i + 1) (l + 1))
      = starVal Γ τ₀ α (z i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)))
    (hhor : ∀ i, i < m → ∀ l ≤ n, starVal Γ τ₀ α (z (i + 1) l) (G (i + 1) l)
        (G (i + 1) (l + 1))
      = starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))) :
    ∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z m l) (G (m + 1) l) (G (m + 1) (l + 1))
      = (∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z 0 l) (G 0 l) (G 0 (l + 1)))
        + ∑ i ∈ Finset.range (m + 1),
            (starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1))
              - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) := by
  set V : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ := fun c cl i l i' =>
    starVal Γ τ₀ α (z c cl) (G i l) (G i' l) with hV
  have step2 : ∀ i ≤ m,
      ∑ l ∈ Finset.range (n + 1),
          starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))
        = (∑ l ∈ Finset.range (n + 1),
            starVal Γ τ₀ α (z i l) (G i l) (G i (l + 1)))
          + (starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1))
            - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) := by
    intro i hi
    have hsq : ∀ l ≤ n,
        starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))
          - starVal Γ τ₀ α (z i l) (G i l) (G i (l + 1))
        = starVal Γ τ₀ α (z i l) (G i (l + 1)) (G (i + 1) (l + 1))
          - starVal Γ τ₀ α (z i l) (G i l) (G (i + 1) l) := by
      intro l hl
      obtain ⟨ha, hb, hc, hd⟩ := h4 i hi l hl
      exact starVal_square hΓ hfree hε hgap hdense hα ha hb hc hd
    have hsplit : ∀ l ∈ Finset.range (n + 1),
        starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1))
        = starVal Γ τ₀ α (z i l) (G i l) (G i (l + 1))
          + (starVal Γ τ₀ α (z i l) (G i (l + 1)) (G (i + 1) (l + 1))
            - starVal Γ τ₀ α (z i l) (G i l) (G (i + 1) l)) := by
      intro l hl
      have hln : l ≤ n := by
        have := Finset.mem_range.mp hl
        omega
      have := hsq l hln
      linarith
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hWtel : ∑ l ∈ Finset.range (n + 1),
        starVal Γ τ₀ α (z i l) (G i (l + 1)) (G (i + 1) (l + 1))
        = (∑ l ∈ Finset.range n,
            starVal Γ τ₀ α (z i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)))
          + starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1)) := by
      rw [Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      exact hvert i hi l (Finset.mem_range.mp hl)
    have hWtel' : ∑ l ∈ Finset.range (n + 1),
        starVal Γ τ₀ α (z i l) (G i l) (G (i + 1) l)
        = starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)
          + ∑ l ∈ Finset.range n,
            starVal Γ τ₀ α (z i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)) := by
      rw [Finset.sum_range_succ']
      ring
    rw [hWtel, hWtel']
    ring
  have step1 : ∀ i, i < m →
      ∑ l ∈ Finset.range (n + 1),
          starVal Γ τ₀ α (z (i + 1) l) (G (i + 1) l) (G (i + 1) (l + 1))
        = ∑ l ∈ Finset.range (n + 1),
          starVal Γ τ₀ α (z i l) (G (i + 1) l) (G (i + 1) (l + 1)) := by
    intro i hi
    refine Finset.sum_congr rfl fun l hl => ?_
    exact hhor i hi l (by have := Finset.mem_range.mp hl; omega)
  have main : ∀ k, k ≤ m + 1 →
      ∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z (min k m) l) (G k l) (G k (l + 1))
        = (∑ l ∈ Finset.range (n + 1), starVal Γ τ₀ α (z 0 l) (G 0 l) (G 0 (l + 1)))
          + ∑ i ∈ Finset.range k,
              (starVal Γ τ₀ α (z i n) (G i (n + 1)) (G (i + 1) (n + 1))
                - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkm : k ≤ m := by omega
      have hmin : min k m = k := by omega
      have ihk := ih (by omega)
      rw [hmin] at ihk
      rw [Finset.sum_range_succ (fun i => starVal Γ τ₀ α (z i n) (G i (n + 1))
        (G (i + 1) (n + 1)) - starVal Γ τ₀ α (z i 0) (G i 0) (G (i + 1) 0)) k,
        ← add_assoc, ← ihk]
      by_cases hkm' : k < m
      · have hmin' : min (k + 1) m = k + 1 := by omega
        rw [hmin', step1 k hkm', step2 k hkm]
      · have hkeq : k = m := by omega
        subst hkeq
        have hmin' : min (k + 1) k = k := by omega
        rw [hmin', step2 k le_rfl]
  have hfin := main (m + 1) le_rfl
  rwa [show min (m + 1) m = m by omega] at hfin

/-! ## Geometric helpers for the homotopy grid -/

/-- A tile containing the basepoint is centered at the basepoint. -/
theorem class_one_of_mem_tile (hΓ : IsFuchsianGroup Γ)
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {X : ↥Γ} (hX : τ₀ ∈ (X • ·) '' dirichletDomain Γ τ₀) : X • τ₀ = τ₀ := by
  have hint : τ₀ ∈ (fun x => (1 : ↥Γ) • x) '' interior (dirichletDomain Γ τ₀) :=
    ⟨τ₀, basepoint_mem_interior_dirichletDomain hε hgap, one_smul _ _⟩
  have hcs := (mem_smul_interior_iff_contactSet_eq hΓ hdense 1 τ₀).mp hint
  have hXc : X ∈ contactSet Γ τ₀ τ₀ :=
    (mem_contactSet_iff_mem_smul_dirichletDomain X τ₀).mpr hX
  rw [hcs] at hXc
  simpa using hXc

/-- A tile through a point near a center is a contact tile of the center. -/
theorem contact_of_near {w x : UpperHalfPlane} {rw : ℝ}
    (hmeets : ∀ γ : ↥Γ, ((γ • ·) '' dirichletDomain Γ τ₀ ∩
      Metric.ball w rw).Nonempty → γ ∈ contactSet Γ τ₀ w)
    {X : ↥Γ} (hx : x ∈ (X • ·) '' dirichletDomain Γ τ₀) (hd : dist x w < rw) :
    X ∈ contactSet Γ τ₀ w :=
  hmeets X ⟨x, hx, Metric.mem_ball.mpr hd⟩

/-- Interpolation points lie on the geodesic segment. -/
theorem geodInterp_mem_seg {a b : UpperHalfPlane} {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    geodInterp a b t ∈ geodSeg a b := by
  rw [geodSeg_eq_image_geodInterp]
  exact ⟨t, ht, rfl⟩

/-- The segment from a tile center to a point of the tile stays in the tile, in
interpolation form. -/
theorem tile_interp {X : ↥Γ} {u : UpperHalfPlane}
    (hu : u ∈ (X • ·) '' dirichletDomain Γ τ₀) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    geodInterp (X • τ₀) u t ∈ (X • ·) '' dirichletDomain Γ τ₀ :=
  geodSeg_center_subset_tile
    ((mem_contactSet_iff_mem_smul_dirichletDomain X u).mpr hu)
    (geodInterp_mem_seg ht)

/-- The segment from a point of the tile to the tile center stays in the tile, in
interpolation form. -/
theorem tile_interp' {X : ↥Γ} {u : UpperHalfPlane}
    (hu : u ∈ (X • ·) '' dirichletDomain Γ τ₀) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    geodInterp u (X • τ₀) t ∈ (X • ·) '' dirichletDomain Γ τ₀ := by
  refine geodSeg_center_subset_tile
    ((mem_contactSet_iff_mem_smul_dirichletDomain X u).mpr hu) ?_
  rw [geodSeg_comm]
  exact geodInterp_mem_seg ht

/-- The basepoint tile membership of the basepoint. -/
theorem basepoint_mem_tile (X : ↥Γ) (hX : X • τ₀ = τ₀) :
    τ₀ ∈ (X • ·) '' dirichletDomain Γ τ₀ :=
  ⟨τ₀, basepoint_mem_dirichletDomain, hX⟩

/-! ## The homotopy piece: contracting one crossing over a grid -/

/-- **The piece lemma**: for a crossing from tile `A` to tile `B` through a shared point
`q`, the geodesic homotopy of the two-segment curve `A•τ₀ → q → B•τ₀` onto the basepoint,
discretized on a sufficiently fine even grid against junction tile columns `CA`, `CB`,
expresses the side value `α (A⁻¹ B)` as the difference of the two junction column sums. -/
theorem piece (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    (r : UpperHalfPlane → ℝ) (hr : ∀ w, 0 < r w)
    (hmeets : ∀ w : UpperHalfPlane, ∀ γ : ↥Γ,
      ((γ • ·) '' dirichletDomain Γ τ₀ ∩ Metric.ball w (r w)).Nonempty →
        γ ∈ contactSet Γ τ₀ w)
    {A B : ↥Γ} {q : UpperHalfPlane}
    (hqA : q ∈ (A • ·) '' dirichletDomain Γ τ₀)
    (hqB : q ∈ (B • ·) '' dirichletDomain Γ τ₀)
    (hside : IsSideElement Γ τ₀ (A⁻¹ * B)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N' : ℕ, N₀ ≤ N' → ∀ CA CB : ℕ → ↥Γ,
      (∀ i ≤ 2 * N', geodInterp τ₀ (A • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (CA i • ·) '' dirichletDomain Γ τ₀) →
      (∀ i ≤ 2 * N', geodInterp τ₀ (B • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (CB i • ·) '' dirichletDomain Γ τ₀) →
      CA (2 * N') = A → CB (2 * N') = B →
      ∃ y : ℕ → ℕ → UpperHalfPlane,
        (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
            (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
          dist (geodInterp τ₀ (A • τ₀) s) (y i 0) < r (y i 0) / 2) ∧
        (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
            (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
          dist (geodInterp τ₀ (B • τ₀) s) (y i (2 * N' - 1))
            < r (y i (2 * N' - 1)) / 2) ∧
        α (A⁻¹ * B)
          = (∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i (2 * N' - 1)) (CB i) (CB (i + 1)))
            - ∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1)) := by
  classical
  set c : ℝ → UpperHalfPlane := fun t =>
    if t ≤ 1 / 2 then geodInterp (A • τ₀) q (2 * t)
    else geodInterp q (B • τ₀) (2 * t - 1) with hc
  have hcont : Continuous c := by
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · exact continuous_geodInterp.comp (continuous_const.prodMk
        (continuous_const.prodMk (continuous_const.mul continuous_id)))
    · exact continuous_geodInterp.comp (continuous_const.prodMk
        (continuous_const.prodMk ((continuous_const.mul continuous_id).sub
          continuous_const)))
    · intro t ht
      rw [ht, show (2 : ℝ) * (1 / 2) = 1 by norm_num, geodInterp_one,
        show (1 : ℝ) - 1 = 0 by norm_num, geodInterp_zero]
  have hc0 : c 0 = A • τ₀ := by
    simp only [hc]
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_zero, geodInterp_zero]
  have hc1 : c 1 = B • τ₀ := by
    simp only [hc]
    rw [if_neg (by norm_num : ¬(1 : ℝ) ≤ 1 / 2),
      show (2 : ℝ) * 1 - 1 = 1 by norm_num, geodInterp_one]
  have hcA : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → c t ∈ (A • ·) '' dirichletDomain Γ τ₀ := by
    intro t ht0 ht2
    simp only [hc]
    rw [if_pos ht2]
    exact tile_interp hqA ⟨by linarith, by linarith⟩
  have hcB : ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 1 → c t ∈ (B • ·) '' dirichletDomain Γ τ₀ := by
    intro t ht2 ht1
    simp only [hc]
    by_cases hle : t ≤ 1 / 2
    · rw [if_pos hle, show t = 1 / 2 from le_antisymm hle ht2,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, geodInterp_one]
      exact hqB
    · rw [if_neg hle]
      push Not at hle
      exact tile_interp' hqB ⟨by linarith, by linarith⟩
  set Hu : ℝ × ℝ → UpperHalfPlane := fun P => geodInterp τ₀ (c P.2) P.1 with hHu
  have hHcont : Continuous Hu := continuous_geodInterp.comp
    (continuous_const.prodMk ((hcont.comp continuous_snd).prodMk continuous_fst))
  set K : Set UpperHalfPlane := Hu '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) with hK
  have hKcomp : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hHcont
  have hcover : K ⊆ ⋃ w : UpperHalfPlane, Metric.ball w (r w / 2) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by linarith [hr x])⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hKcomp
    (fun w => Metric.isOpen_ball) hcover
  have hcomp2 : IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hUC := hcomp2.uniformContinuousOn_of_continuous hHcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨η, hη, hUCd⟩ := hUC δ hδ
  refine ⟨⌈1 / η⌉₊ + 1, Nat.le_add_left 1 _, ?_⟩
  intro N' hN' CA CB hCA hCB hCAN hCBN
  have hN'pos : 1 ≤ N' := le_trans (Nat.le_add_left 1 _) hN'
  have hNpos : 0 < 2 * N' := by omega
  have hNR : (0 : ℝ) < ((2 * N' : ℕ) : ℝ) := Nat.cast_pos.mpr hNpos
  have hfine : 1 / ((2 * N' : ℕ) : ℝ) < η := by
    have hceil : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : ((⌈1 / η⌉₊ + 1 : ℕ) : ℝ) ≤ ((N' : ℕ) : ℝ) := Nat.cast_le.mpr hN'
    have hN'le : ((N' : ℕ) : ℝ) ≤ ((2 * N' : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    push_cast at hcast
    have h1 : 1 / η < ((2 * N' : ℕ) : ℝ) := by linarith
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hη] at h1
    linarith [mul_comm η ((2 * N' : ℕ) : ℝ)]
  have hFex : ∀ w : UpperHalfPlane, ∃ g : ↥Γ, w ∈ (g • ·) '' dirichletDomain Γ τ₀ := by
    intro w
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ τ₀ w
    exact ⟨γ⁻¹, γ • w, hγ, inv_smul_smul γ w⟩
  choose F hF using hFex
  set G : ℕ → ℕ → ↥Γ := fun i l =>
    if l = 0 then CA i else if l = 2 * N' then CB i
    else if i = 2 * N' then (if l ≤ N' then A else B)
    else F (Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))) with hG
  have hnode : ∀ i ≤ 2 * N', ∀ l ≤ 2 * N',
      Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (G i l • ·) '' dirichletDomain Γ τ₀ := by
    intro i hi l hl
    by_cases hl0 : l = 0
    · subst hl0
      simp only [hG, if_pos rfl]
      change geodInterp τ₀ (c (((0 : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ)))
        ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ _
      rw [Nat.cast_zero, zero_div, hc0]
      exact hCA i hi
    by_cases hlN : l = 2 * N'
    · subst hlN
      simp only [hG, if_neg hl0]
      change geodInterp τ₀ (c (((2 * N' : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ)))
        ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ _
      rw [div_self hNR.ne', hc1]
      exact hCB i hi
    by_cases hiN : i = 2 * N'
    · subst hiN
      simp only [hG, if_neg hl0, if_neg hlN]
      change geodInterp τ₀ (c ((l : ℝ) / ((2 * N' : ℕ) : ℝ)))
        (((2 * N' : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ _
      rw [div_self hNR.ne', geodInterp_one]
      by_cases hlmid : l ≤ N'
      · rw [if_pos hlmid]
        refine hcA _ (div_nonneg (Nat.cast_nonneg l) hNR.le) ?_
        rw [div_le_iff₀ hNR]
        have : (l : ℝ) ≤ (N' : ℝ) := Nat.cast_le.mpr hlmid
        push_cast
        linarith
      · rw [if_neg hlmid]
        push Not at hlmid
        refine hcB _ ?_ ?_
        · rw [le_div_iff₀ hNR]
          have : ((N' : ℕ) : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hlmid
          push_cast
          linarith
        · rw [div_le_one hNR]
          exact Nat.cast_le.mpr hl
    · simp only [hG, if_neg hl0, if_neg hlN, if_neg hiN]
      exact hF _
  have hyex : ∀ i l : ℕ, ∃ w : UpperHalfPlane, i < 2 * N' → l < 2 * N' →
      Metric.ball (Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))) δ
        ⊆ Metric.ball w (r w / 2) := by
    intro i l
    by_cases h : i < 2 * N' ∧ l < 2 * N'
    · have hmem : Hu ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈ K := by
        refine ⟨((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ)),
          Set.mem_prod.mpr ⟨⟨div_nonneg (Nat.cast_nonneg i) hNR.le, ?_⟩,
            ⟨div_nonneg (Nat.cast_nonneg l) hNR.le, ?_⟩⟩, rfl⟩
        · rw [div_le_one hNR]
          exact Nat.cast_le.mpr (le_of_lt h.1)
        · rw [div_le_one hNR]
          exact Nat.cast_le.mpr (le_of_lt h.2)
      obtain ⟨w, hw⟩ := hleb _ hmem
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨τ₀, fun hi hl => absurd ⟨hi, hl⟩ h⟩
  choose y hy using hyex
  have hsq : ∀ i l : ℕ, i < 2 * N' → l < 2 * N' → ∀ s t : ℝ,
      s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) →
      t ∈ Set.Icc ((l : ℝ) / ((2 * N' : ℕ) : ℝ)) (((l : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) →
      dist (Hu (s, t)) (y i l) < r (y i l) / 2 := by
    intro i l hi hl s t hs htt
    have hIccs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans (div_nonneg (Nat.cast_nonneg i) hNR.le) hs.1
      · refine le_trans hs.2 ?_
        rw [div_le_one hNR]
        exact_mod_cast Nat.succ_le_of_lt hi
    have hIcct : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans (div_nonneg (Nat.cast_nonneg l) hNR.le) htt.1
      · refine le_trans htt.2 ?_
        rw [div_le_one hNR]
        exact_mod_cast Nat.succ_le_of_lt hl
    have hInode : ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ (Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1) := by
      refine Set.mem_prod.mpr ⟨⟨div_nonneg (Nat.cast_nonneg i) hNR.le, ?_⟩,
        ⟨div_nonneg (Nat.cast_nonneg l) hNR.le, ?_⟩⟩
      · rw [div_le_one hNR]
        exact Nat.cast_le.mpr (le_of_lt hi)
      · rw [div_le_one hNR]
        exact Nat.cast_le.mpr (le_of_lt hl)
    have hdiff : ((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ) - (i : ℝ) / ((2 * N' : ℕ) : ℝ)
        = 1 / ((2 * N' : ℕ) : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hdiffl : ((l : ℝ) + 1) / ((2 * N' : ℕ) : ℝ) - (l : ℝ) / ((2 * N' : ℕ) : ℝ)
        = 1 / ((2 * N' : ℕ) : ℝ) := by
      rw [div_sub_div_same]
      norm_num
    have hdist : dist ((s, t) : ℝ × ℝ)
        ((i : ℝ) / ((2 * N' : ℕ) : ℝ), (l : ℝ) / ((2 * N' : ℕ) : ℝ)) < η := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2]
      · rw [Real.dist_eq, abs_of_nonneg (by linarith [htt.1])]
        linarith [htt.2]
    have hδd := hUCd (s, t) (Set.mem_prod.mpr ⟨hIccs, hIcct⟩) _ hInode hdist
    exact Metric.mem_ball.mp (hy i l hi hl (Metric.mem_ball.mpr hδd))
  have hcontact : ∀ i l, i < 2 * N' → l < 2 * N' → ∀ i' l', i ≤ i' → i' ≤ i + 1 →
      l ≤ l' → l' ≤ l + 1 → G i' l' ∈ contactSet Γ τ₀ (y i l) := by
    intro i l hi hl i' l' hii' hi'i hll' hl'l
    have hi'N : i' ≤ 2 * N' := by omega
    have hl'N : l' ≤ 2 * N' := by omega
    have hs : ((i' : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      constructor
      · gcongr
      · gcongr
        exact_mod_cast hi'i
    have ht : ((l' : ℝ) / ((2 * N' : ℕ) : ℝ))
        ∈ Set.Icc ((l : ℝ) / ((2 * N' : ℕ) : ℝ)) (((l : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      constructor
      · gcongr
      · gcongr
        exact_mod_cast hl'l
    have hd := hsq i l hi hl _ _ hs ht
    exact contact_of_near (hmeets (y i l)) (hnode i' hi'N l' hl'N)
      (lt_trans hd (half_lt_self (hr (y i l))))
  have hydist : ∀ i l i₂ l₂, i < 2 * N' → l < 2 * N' → i₂ < 2 * N' → l₂ < 2 * N' →
      ∀ i' l', i ≤ i' → i' ≤ i + 1 → l ≤ l' → l' ≤ l + 1 →
      i₂ ≤ i' → i' ≤ i₂ + 1 → l₂ ≤ l' → l' ≤ l₂ + 1 →
      dist (y i l) (y i₂ l₂) < r (y i l) / 2 + r (y i₂ l₂) / 2 := by
    intro i l i₂ l₂ hi hl hi₂ hl₂ i' l' h1 h2 h3 h4 h5 h6 h7 h8
    have hmk : ∀ j k jc kc : ℕ, j ≤ jc → jc ≤ j + 1 →
        ((jc : ℝ) / ((2 * N' : ℕ) : ℝ))
          ∈ Set.Icc ((j : ℝ) / ((2 * N' : ℕ) : ℝ)) (((j : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      intro j k jc kc hj hj'
      constructor
      · gcongr
      · gcongr
        exact_mod_cast hj'
    have hda := hsq i l hi hl _ _ (hmk i 0 i' 0 h1 h2) (hmk l 0 l' 0 h3 h4)
    have hdb := hsq i₂ l₂ hi₂ hl₂ _ _ (hmk i₂ 0 i' 0 h5 h6) (hmk l₂ 0 l' 0 h7 h8)
    calc dist (y i l) (y i₂ l₂)
        ≤ dist (y i l) (Hu ((i' : ℝ) / ((2 * N' : ℕ) : ℝ),
            (l' : ℝ) / ((2 * N' : ℕ) : ℝ)))
          + dist (Hu ((i' : ℝ) / ((2 * N' : ℕ) : ℝ),
            (l' : ℝ) / ((2 * N' : ℕ) : ℝ))) (y i₂ l₂) := dist_triangle _ _ _
      _ < r (y i l) / 2 + r (y i₂ l₂) / 2 := by
          rw [dist_comm (y i l)]
          exact add_lt_add hda hdb
  have hvert : ∀ i ≤ 2 * N' - 1, ∀ l, l < 2 * N' - 1 →
      starVal Γ τ₀ α (y i l) (G i (l + 1)) (G (i + 1) (l + 1))
        = starVal Γ τ₀ α (y i (l + 1)) (G i (l + 1)) (G (i + 1) (l + 1)) := by
    intro i hi l hl
    have hiN : i < 2 * N' := by omega
    have hlN : l < 2 * N' := by omega
    have hl1N : l + 1 < 2 * N' := by omega
    exact starVal_two_star hΓ hfree hε hgap hdense hα (hmeets (y i l))
      (hmeets (y i (l + 1)))
      (hydist i l i (l + 1) hiN hlN hiN hl1N i (l + 1) le_rfl (by omega) (by omega)
        le_rfl le_rfl (by omega) le_rfl (by omega))
      (hcontact i l hiN hlN i (l + 1) le_rfl (by omega) (by omega) le_rfl)
      (hcontact i l hiN hlN (i + 1) (l + 1) (by omega) le_rfl (by omega) le_rfl)
      (hcontact i (l + 1) hiN hl1N i (l + 1) le_rfl (by omega) le_rfl (by omega))
      (hcontact i (l + 1) hiN hl1N (i + 1) (l + 1) (by omega) le_rfl le_rfl (by omega))
  have hhor : ∀ i, i < 2 * N' - 1 → ∀ l ≤ 2 * N' - 1,
      starVal Γ τ₀ α (y (i + 1) l) (G (i + 1) l) (G (i + 1) (l + 1))
        = starVal Γ τ₀ α (y i l) (G (i + 1) l) (G (i + 1) (l + 1)) := by
    intro i hi l hl
    have hiN : i < 2 * N' := by omega
    have hi1N : i + 1 < 2 * N' := by omega
    have hlN : l < 2 * N' := by omega
    exact starVal_two_star hΓ hfree hε hgap hdense hα (hmeets (y (i + 1) l))
      (hmeets (y i l))
      (hydist (i + 1) l i l hi1N hlN hiN hlN (i + 1) l le_rfl (by omega) le_rfl
        (by omega) (by omega) le_rfl le_rfl (by omega))
      (hcontact (i + 1) l hi1N hlN (i + 1) l le_rfl (by omega) le_rfl (by omega))
      (hcontact (i + 1) l hi1N hlN (i + 1) (l + 1) le_rfl (by omega) (by omega) le_rfl)
      (hcontact i l hiN hlN (i + 1) l (by omega) le_rfl le_rfl (by omega))
      (hcontact i l hiN hlN (i + 1) (l + 1) (by omega) le_rfl (by omega) le_rfl)
  have h4 : ∀ i ≤ 2 * N' - 1, ∀ l ≤ 2 * N' - 1, G i l ∈ contactSet Γ τ₀ (y i l) ∧
      G i (l + 1) ∈ contactSet Γ τ₀ (y i l) ∧ G (i + 1) l ∈ contactSet Γ τ₀ (y i l) ∧
      G (i + 1) (l + 1) ∈ contactSet Γ τ₀ (y i l) := by
    intro i hi l hl
    have hiN : i < 2 * N' := by omega
    have hlN : l < 2 * N' := by omega
    exact ⟨hcontact i l hiN hlN i l le_rfl (by omega) le_rfl (by omega),
      hcontact i l hiN hlN i (l + 1) le_rfl (by omega) (by omega) le_rfl,
      hcontact i l hiN hlN (i + 1) l (by omega) le_rfl le_rfl (by omega),
      hcontact i l hiN hlN (i + 1) (l + 1) (by omega) le_rfl (by omega) le_rfl⟩
  have hgrid := grid_rows hΓ hfree hε hgap hdense hα (2 * N' - 1) (2 * N' - 1)
    y G h4 hvert hhor
  have hNN1 : 2 * N' - 1 + 1 = 2 * N' := by omega
  rw [hNN1] at hgrid
  have hG0 : ∀ i, G i 0 = CA i := by
    intro i
    simp [hG]
  have hGN : ∀ i, G i (2 * N') = CB i := by
    intro i
    simp only [hG]
    rw [if_neg (by omega : ¬2 * N' = 0), if_pos trivial]
  have hTop : ∀ l ≤ 2 * N', G (2 * N') l = if l ≤ N' then A else B := by
    intro l hl
    by_cases hl0 : l = 0
    · subst hl0
      rw [hG0, hCAN, if_pos (Nat.zero_le N')]
    by_cases hlN : l = 2 * N'
    · subst hlN
      rw [hGN, hCBN, if_neg (by omega)]
    · simp only [hG]
      rw [if_neg hl0, if_neg hlN, if_pos trivial]
  have htopmem : ∀ l' l, l < 2 * N' → l ≤ l' → l' ≤ l + 1 →
      G (2 * N') l' ∈ contactSet Γ τ₀ (y (2 * N' - 1) l) := by
    intro l' l hl hll' hl'l
    exact hcontact (2 * N' - 1) l (by omega) hl (2 * N') l' (by omega) (by omega) hll' hl'l
  have htopsum : ∑ l ∈ Finset.range (2 * N'),
      starVal Γ τ₀ α (y (2 * N' - 1) l) (G (2 * N') l) (G (2 * N') (l + 1))
      = α (A⁻¹ * B) := by
    refine Finset.sum_eq_single_of_mem N' (Finset.mem_range.mpr (by omega)) ?_ |>.trans ?_
    · intro b hb hbN
      have hblt : b < 2 * N' := Finset.mem_range.mp hb
      have hmem : G (2 * N') b ∈ contactSet Γ τ₀ (y (2 * N' - 1) b) :=
        htopmem b b hblt le_rfl (by omega)
      rcases lt_or_gt_of_ne hbN with hcase | hcase
      · have he1 : G (2 * N') b = A := by rw [hTop b (by omega), if_pos (by omega)]
        have he2 : G (2 * N') (b + 1) = A := by rw [hTop (b + 1) (by omega), if_pos (by omega)]
        rw [he1] at hmem ⊢
        rw [he2]
        exact starVal_class_zero hΓ hfree hα hmem rfl
      · have he1 : G (2 * N') b = B := by rw [hTop b (by omega), if_neg (by omega)]
        have he2 : G (2 * N') (b + 1) = B := by rw [hTop (b + 1) (by omega), if_neg (by omega)]
        rw [he1] at hmem ⊢
        rw [he2]
        exact starVal_class_zero hΓ hfree hα hmem rfl
    · have he1 : G (2 * N') N' = A := by rw [hTop N' (by omega), if_pos le_rfl]
      have he2 : G (2 * N') (N' + 1) = B := by rw [hTop (N' + 1) (by omega), if_neg (by omega)]
      have hmA : G (2 * N') N' ∈ contactSet Γ τ₀ (y (2 * N' - 1) N') :=
        htopmem N' N' (by omega) le_rfl (by omega)
      have hmB : G (2 * N') (N' + 1) ∈ contactSet Γ τ₀ (y (2 * N' - 1) N') :=
        htopmem (N' + 1) N' (by omega) (by omega) le_rfl
      rw [he1] at hmA
      rw [he2] at hmB
      rw [he1, he2]
      exact starVal_side hΓ hfree hα hmA hmB hside
  have hbase : ∀ l ≤ 2 * N', (G 0 l) • τ₀ = τ₀ := by
    intro l hl
    have h := hnode 0 (by omega) l hl
    rw [Nat.cast_zero, zero_div] at h
    simp only [hHu] at h
    rw [geodInterp_zero] at h
    exact class_one_of_mem_tile hΓ hε hgap hdense h
  have hbotsum : ∑ l ∈ Finset.range (2 * N'),
      starVal Γ τ₀ α (y 0 l) (G 0 l) (G 0 (l + 1)) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    have hllt : l < 2 * N' := Finset.mem_range.mp hl
    have hmem : G 0 l ∈ contactSet Γ τ₀ (y 0 l) :=
      hcontact 0 l (by omega) hllt 0 l le_rfl (by omega) le_rfl (by omega)
    exact starVal_class_zero hΓ hfree hα hmem
      ((hbase l (by omega)).trans (hbase (l + 1) (by omega)).symm)
  refine ⟨y, ?_, ?_, ?_⟩
  · intro i hi s hs
    have h := hsq i 0 hi (by omega) s 0 hs
      (by
        constructor
        · rw [Nat.cast_zero, zero_div]
        · rw [Nat.cast_zero]
          positivity)
    simp only [hHu] at h
    rwa [hc0] at h
  · intro i hi s hs
    have hone : (1 : ℝ) ∈ Set.Icc (((2 * N' - 1 : ℕ) : ℝ) / ((2 * N' : ℕ) : ℝ))
        ((((2 * N' - 1 : ℕ) : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) := by
      have hcast : ((2 * N' - 1 : ℕ) : ℝ) + 1 = ((2 * N' : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * N')]
        push_cast
        ring
      constructor
      · rw [div_le_one hNR]
        linarith [hNR]
      · rw [hcast, div_self hNR.ne']
    have h := hsq i (2 * N' - 1) hi (by omega) s 1 hs hone
    simp only [hHu] at h
    rwa [hc1] at h
  · have hcolL : ∀ i, G i 0 = CA i ∧ G (i + 1) 0 = CA (i + 1) := fun i => ⟨hG0 i, hG0 (i + 1)⟩
    calc α (A⁻¹ * B)
        = ∑ l ∈ Finset.range (2 * N'),
            starVal Γ τ₀ α (y (2 * N' - 1) l) (G (2 * N') l) (G (2 * N') (l + 1)) :=
          htopsum.symm
      _ = (∑ l ∈ Finset.range (2 * N'),
            starVal Γ τ₀ α (y 0 l) (G 0 l) (G 0 (l + 1)))
          + ∑ i ∈ Finset.range (2 * N'),
              (starVal Γ τ₀ α (y i (2 * N' - 1)) (G i (2 * N')) (G (i + 1) (2 * N'))
                - starVal Γ τ₀ α (y i 0) (G i 0) (G (i + 1) 0)) := hgrid
      _ = ∑ i ∈ Finset.range (2 * N'),
              (starVal Γ τ₀ α (y i (2 * N' - 1)) (CB i) (CB (i + 1))
                - starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1))) := by
          rw [hbotsum, zero_add]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hGN i, hGN (i + 1), hG0 i, hG0 (i + 1)]
      _ = (∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i (2 * N' - 1)) (CB i) (CB (i + 1)))
            - ∑ i ∈ Finset.range (2 * N'),
              starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1)) := Finset.sum_sub_distrib _ _

/-- Closed tile loops based at the base tile have zero crossing sum: each transition is
contracted onto the basepoint through its homotopy grid, and the junction column sums
telescope away. -/
theorem closed_zero_base (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {p : List ↥Γ} (hp : IsTilePath Γ τ₀ p) (hhead : p.head? = some 1)
    {δ' : ↥Γ} (hlast : p.getLast? = some δ') (hδ : δ' • τ₀ = τ₀) :
    crossingSum α p = 0 := by
  classical
  set M : ℕ := p.length - 1 with hM
  set g : ℕ → ↥Γ := fun k => p.getD k 1 with hgdef
  have hpne : p ≠ [] := by
    rintro rfl
    simp at hhead
  have hplen : p.length = M + 1 := by
    have := List.length_pos_iff.mpr hpne
    omega
  have hg0 : g 0 = 1 := head_getD hhead
  have hgM : g M = δ' := getLast_getD hlast
  have hsum : crossingSum α p = ∑ k ∈ Finset.range M, α ((g k)⁻¹ * g (k + 1)) :=
    crossingSum_eq_sum_range α p
  have htrans : ∀ k, k < M → IsSideElement Γ τ₀ ((g k)⁻¹ * g (k + 1)) := by
    intro k hk
    exact isTilePath_getD hp k (by omega)
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hsum, hM0]
    simp
  have hqex : ∀ k, ∃ w : UpperHalfPlane, k < M →
      w ∈ (g k • ·) '' dirichletDomain Γ τ₀ ∧
        w ∈ (g (k + 1) • ·) '' dirichletDomain Γ τ₀ := by
    intro k
    by_cases hk : k < M
    · obtain ⟨x, hx⟩ := (htrans k hk).2.nonempty
      refine ⟨g k • x, fun _ => ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩
      have hxσ : ((g k)⁻¹ * g (k + 1))⁻¹ • x ∈ dirichletDomain Γ τ₀ :=
        (smul_mem_dirichletSideSet_inv hx).1
      refine ⟨((g k)⁻¹ * g (k + 1))⁻¹ • x, hxσ, ?_⟩
      change g (k + 1) • ((g k)⁻¹ * g (k + 1))⁻¹ • x = g k • x
      rw [← mul_smul]
      congr 1
      group
    · exact ⟨τ₀, fun h => absurd h hk⟩
  choose Q hQ using hqex
  choose r hr hmeets hcover using fun w => exists_ball_inter_tiles_subset_contact hΓ τ₀ w
  set P : ℕ → ℕ → Prop := fun k Nx => ∀ CA CB : ℕ → ↥Γ,
    (∀ i ≤ 2 * Nx, geodInterp τ₀ (g k • τ₀) ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
      ∈ (CA i • ·) '' dirichletDomain Γ τ₀) →
    (∀ i ≤ 2 * Nx, geodInterp τ₀ (g (k + 1) • τ₀) ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
      ∈ (CB i • ·) '' dirichletDomain Γ τ₀) →
    CA (2 * Nx) = g k → CB (2 * Nx) = g (k + 1) →
    ∃ y : ℕ → ℕ → UpperHalfPlane,
      (∀ i < 2 * Nx, ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
          (((i : ℝ) + 1) / ((2 * Nx : ℕ) : ℝ)),
        dist (geodInterp τ₀ (g k • τ₀) s) (y i 0) < r (y i 0) / 2) ∧
      (∀ i < 2 * Nx, ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * Nx : ℕ) : ℝ))
          (((i : ℝ) + 1) / ((2 * Nx : ℕ) : ℝ)),
        dist (geodInterp τ₀ (g (k + 1) • τ₀) s) (y i (2 * Nx - 1))
          < r (y i (2 * Nx - 1)) / 2) ∧
      α ((g k)⁻¹ * g (k + 1))
        = (∑ i ∈ Finset.range (2 * Nx),
            starVal Γ τ₀ α (y i (2 * Nx - 1)) (CB i) (CB (i + 1)))
          - ∑ i ∈ Finset.range (2 * Nx),
            starVal Γ τ₀ α (y i 0) (CA i) (CA (i + 1)) with hPdef
  have hNex : ∀ k, ∃ N₀ : ℕ, k < M → ∀ Nx, N₀ ≤ Nx → P k Nx := by
    intro k
    by_cases hk : k < M
    · obtain ⟨N₀, -, hN₀⟩ := piece hΓ hfree hε hgap hdense hα r hr hmeets
        (hQ k hk).1 (hQ k hk).2 (htrans k hk)
      exact ⟨N₀, fun _ Nx hNx => hN₀ Nx hNx⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose Nf hNf using hNex
  set N' : ℕ := (Finset.range M).sup Nf + 1 with hN'def
  have hgetP : ∀ k, k < M → P k N' := by
    intro k hk
    refine hNf k hk N' ?_
    have := Finset.le_sup (f := Nf) (Finset.mem_range.mpr hk)
    omega
  have hNR : (0 : ℝ) < ((2 * N' : ℕ) : ℝ) := by
    rw [hN'def]
    push_cast
    positivity
  have hFex : ∀ w : UpperHalfPlane, ∃ X : ↥Γ, w ∈ (X • ·) '' dirichletDomain Γ τ₀ := by
    intro w
    obtain ⟨γ, hγ⟩ := exists_smul_mem_dirichletDomain hΓ τ₀ w
    exact ⟨γ⁻¹, γ • w, hγ, inv_smul_smul γ w⟩
  choose F hF using hFex
  set C : ℕ → ℕ → ↥Γ := fun J i => if i = 2 * N' then g J
    else F (geodInterp τ₀ (g J • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))) with hCdef
  have hCN : ∀ J, C J (2 * N') = g J := by
    intro J
    simp [hCdef]
  have hCmem : ∀ J, ∀ i ≤ 2 * N', geodInterp τ₀ (g J • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
      ∈ (C J i • ·) '' dirichletDomain Γ τ₀ := by
    intro J i hi
    by_cases h : i = 2 * N'
    · subst h
      rw [hCN J, div_self hNR.ne', geodInterp_one]
      exact ⟨τ₀, basepoint_mem_dirichletDomain, rfl⟩
    · simp only [hCdef, if_neg h]
      exact hF _
  set W : ℕ → (ℕ → ℕ → UpperHalfPlane) → Prop := fun k y =>
    (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
      dist (geodInterp τ₀ (g k • τ₀) s) (y i 0) < r (y i 0) / 2) ∧
    (∀ i < 2 * N', ∀ s ∈ Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ))
        (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)),
      dist (geodInterp τ₀ (g (k + 1) • τ₀) s) (y i (2 * N' - 1))
        < r (y i (2 * N' - 1)) / 2) ∧
    α ((g k)⁻¹ * g (k + 1))
      = (∑ i ∈ Finset.range (2 * N'),
          starVal Γ τ₀ α (y i (2 * N' - 1)) (C (k + 1) i) (C (k + 1) (i + 1)))
        - ∑ i ∈ Finset.range (2 * N'),
          starVal Γ τ₀ α (y i 0) (C k i) (C k (i + 1)) with hWdef
  have hYex : ∀ k, ∃ y : ℕ → ℕ → UpperHalfPlane, k < M → W k y := by
    intro k
    by_cases hk : k < M
    · obtain ⟨y, hy1, hy2, hy3⟩ := hgetP k hk (C k) (C (k + 1)) (hCmem k) (hCmem (k + 1))
        (hCN k) (hCN (k + 1))
      exact ⟨y, fun _ => ⟨hy1, hy2, hy3⟩⟩
    · exact ⟨fun _ _ => τ₀, fun h => absurd h hk⟩
  choose Y hYW using hYex
  set L : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (2 * N'),
    starVal Γ τ₀ α (Y k i 0) (C k i) (C k (i + 1)) with hLdef
  set Rt : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (2 * N'),
    starVal Γ τ₀ α (Y k i (2 * N' - 1)) (C (k + 1) i) (C (k + 1) (i + 1)) with hRdef
  have hkey : ∀ k, k < M → α ((g k)⁻¹ * g (k + 1)) = Rt k - L k :=
    fun k hk => (hYW k hk).2.2
  have hcolmem : ∀ (J : ℕ) (zc : UpperHalfPlane) (i' : ℕ), i' ≤ 2 * N' →
      dist (geodInterp τ₀ (g J • τ₀) ((i' : ℝ) / ((2 * N' : ℕ) : ℝ))) zc < r zc / 2 →
      C J i' ∈ contactSet Γ τ₀ zc := by
    intro J zc i' hi' hd
    exact contact_of_near (hmeets zc) (hCmem J i' hi')
      (lt_trans hd (half_lt_self (hr zc)))
  have hstep : ∀ i : ℕ, (i : ℝ) / ((2 * N' : ℕ) : ℝ) ≤ ((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ) := by
    intro i
    gcongr
    linarith
  have hIccl : ∀ i : ℕ, ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) ∈
      Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) :=
    fun i => ⟨le_rfl, hstep i⟩
  have hIccr : ∀ i : ℕ, (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) ∈
      Set.Icc ((i : ℝ) / ((2 * N' : ℕ) : ℝ)) (((i : ℝ) + 1) / ((2 * N' : ℕ) : ℝ)) :=
    fun i => ⟨hstep i, le_rfl⟩
  have hcast1 : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
    intro i
    push_cast
    ring
  have hmatch : ∀ k, k + 1 < M → Rt k = L (k + 1) := by
    intro k hk1
    have hkM : k < M := by omega
    have hE1 := (hYW k hkM).2.1
    have hE2 := (hYW (k + 1) (by omega)).1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hilt : i < 2 * N' := Finset.mem_range.mp hi
    have hxL := hE1 i hilt _ (hIccl i)
    have hxR := hE2 i hilt _ (hIccl i)
    have hx1L := hE1 i hilt _ (hIccr i)
    have hx1R := hE2 i hilt _ (hIccr i)
    refine starVal_two_star hΓ hfree hε hgap hdense hα
      (hmeets (Y k i (2 * N' - 1))) (hmeets (Y (k + 1) i 0)) ?_
      (hcolmem (k + 1) _ i (by omega) hxL)
      (hcolmem (k + 1) _ (i + 1) (by omega) (by rw [hcast1 i]; exact hx1L))
      (hcolmem (k + 1) _ i (by omega) hxR)
      (hcolmem (k + 1) _ (i + 1) (by omega) (by rw [hcast1 i]; exact hx1R))
    calc dist (Y k i (2 * N' - 1)) (Y (k + 1) i 0)
        ≤ dist (Y k i (2 * N' - 1))
            (geodInterp τ₀ (g (k + 1) • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ)))
          + dist (geodInterp τ₀ (g (k + 1) • τ₀) ((i : ℝ) / ((2 * N' : ℕ) : ℝ)))
            (Y (k + 1) i 0) := dist_triangle _ _ _
      _ < r (Y k i (2 * N' - 1)) / 2 + r (Y (k + 1) i 0) / 2 := by
          rw [dist_comm (Y k i (2 * N' - 1))]
          exact add_lt_add hxL hxR
  have hg0τ : ∀ s : ℝ, geodInterp τ₀ (g 0 • τ₀) s = τ₀ := by
    intro s
    rw [hg0, one_smul, geodInterp_self]
  have hcl0 : ∀ i' ≤ 2 * N', (C 0 i') • τ₀ = τ₀ := by
    intro i' hi'
    have hmem := hCmem 0 i' hi'
    rw [hg0τ] at hmem
    exact class_one_of_mem_tile hΓ hε hgap hdense hmem
  have hL0 : L 0 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hilt : i < 2 * N' := Finset.mem_range.mp hi
    have hE2 := (hYW 0 hMpos).1
    exact starVal_class_zero hΓ hfree hα
      (hcolmem 0 _ i (by omega) (hE2 i hilt _ (hIccl i)))
      ((hcl0 i (by omega)).trans (hcl0 (i + 1) (by omega)).symm)
  have hM1 : M - 1 + 1 = M := by omega
  have hgMτ : ∀ s : ℝ, geodInterp τ₀ (g (M - 1 + 1) • τ₀) s = τ₀ := by
    intro s
    rw [hM1, hgM, hδ, geodInterp_self]
  have hclM : ∀ i' ≤ 2 * N', (C (M - 1 + 1) i') • τ₀ = τ₀ := by
    intro i' hi'
    have hmem := hCmem (M - 1 + 1) i' hi'
    rw [hgMτ] at hmem
    exact class_one_of_mem_tile hΓ hε hgap hdense hmem
  have hRM : Rt (M - 1) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hilt : i < 2 * N' := Finset.mem_range.mp hi
    have hE1 := (hYW (M - 1) (by omega)).2.1
    exact starVal_class_zero hΓ hfree hα
      (hcolmem (M - 1 + 1) _ i (by omega) (hE1 i hilt _ (hIccl i)))
      ((hclM i (by omega)).trans (hclM (i + 1) (by omega)).symm)
  have h1 : ∑ k ∈ Finset.range M, Rt k
      = (∑ k ∈ Finset.range (M - 1), Rt k) + Rt (M - 1) := by
    conv_lhs => rw [← hM1]
    exact Finset.sum_range_succ _ _
  have h2 : ∑ k ∈ Finset.range M, L k
      = (∑ k ∈ Finset.range (M - 1), L (k + 1)) + L 0 := by
    conv_lhs => rw [← hM1]
    exact Finset.sum_range_succ' _ _
  have h3 : ∑ k ∈ Finset.range (M - 1), L (k + 1) = ∑ k ∈ Finset.range (M - 1), Rt k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    refine (hmatch k ?_).symm
    have := Finset.mem_range.mp hk
    omega
  rw [hsum]
  calc ∑ k ∈ Finset.range M, α ((g k)⁻¹ * g (k + 1))
      = ∑ k ∈ Finset.range M, (Rt k - L k) :=
        Finset.sum_congr rfl fun k hk => hkey k (Finset.mem_range.mp hk)
    _ = (∑ k ∈ Finset.range M, Rt k) - ∑ k ∈ Finset.range M, L k :=
        Finset.sum_sub_distrib _ _
    _ = 0 := by
        rw [h1, h2, h3, hRM, hL0]
        ring

/-- **Path independence**: the crossing sum of a cycle-constrained side function vanishes
along every closed tile path — a closed tile loop contracts to the basepoint by geodesic
homotopy, a Lebesgue number for the star covering of the compact homotopy square reduces
the contraction to local moves within a vertex star, and the local moves are multiples of
vertex loops, on which the constraint vanishes; backtracking cancels by oddness. -/
theorem crossingSum_eq_zero_of_closed (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀) {p : List ↥Γ}
    (hp : IsTilePath Γ τ₀ p) {γ δ : ↥Γ} (hhead : p.head? = some γ)
    (hlast : p.getLast? = some δ) (hclose : γ • τ₀ = δ • τ₀) :
    crossingSum α p = 0 := by
  rw [← crossingSum_map_mul α γ⁻¹ p]
  refine closed_zero_base hΓ hfree hε hgap hdense hα (isTilePath_map γ⁻¹ hp) ?_
    (δ' := γ⁻¹ * δ) ?_ ?_
  · rw [List.head?_map, hhead]
    simp
  · rw [List.getLast?_map, hlast]
    rfl
  · rw [mul_smul, ← hclose, inv_smul_smul]

/-- Path independence: any two tile paths with basepoint-equal heads and basepoint-equal
last tiles have equal crossing sums. -/
theorem crossingSum_pathIndep (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {α : (↥Γ) → ℝ} (hα : α ∈ cycleConstrained Γ τ₀)
    {p q : List ↥Γ} (hp : IsTilePath Γ τ₀ p) (hq : IsTilePath Γ τ₀ q)
    {a a' b b' : ↥Γ} (hpa : p.head? = some a) (hpb : p.getLast? = some b)
    (hqa : q.head? = some a') (hqb : q.getLast? = some b')
    (ha : a • τ₀ = a' • τ₀) (hb : b • τ₀ = b' • τ₀) :
    crossingSum α p = crossingSum α q := by
  obtain ⟨⟨hzero, hodd, hfib⟩, -⟩ := mem_cycleConstrained.mp hα
  set u : ↥Γ := b * b'⁻¹ with hu
  have hut : u • τ₀ = τ₀ := junction_trivial hfree hb
  have hutriv := hfree u ⟨τ₀, hut⟩
  set q' : List ↥Γ := q.reverse.map (u * ·) with hq'
  have hq'path : IsTilePath Γ τ₀ q' := isTilePath_map u (isTilePath_reverse hq)
  have hq'head : q'.head? = some b := by
    rw [hq', List.head?_map, List.head?_reverse, hqb, Option.map_some]
    simp [hu]
  have hq'last : q'.getLast? = some (u * a') := by
    rw [hq', List.getLast?_map, List.getLast?_reverse, hqa, Option.map_some]
  have hglue := crossingSum_glue α hpb hq'head
  have hr : IsTilePath Γ τ₀ (p ++ q'.tail) := isTilePath_glue hp hq'path hpb hq'head
  have hzero' := crossingSum_eq_zero_of_closed hΓ hfree hε hgap hdense hα hr
    ((head?_glue (q := q') hpb).trans hpa)
    ((getLast?_glue hpb hq'head).trans hq'last)
    (by rw [mul_smul, hutriv, ha])
  have hrev := crossingSum_reverse hodd q
  have hmap := crossingSum_map_mul α u q.reverse
  rw [hglue, hmap, hrev] at hzero'
  linarith

/-- **Integration along tile paths**: every cycle-constrained side function extends to an
additive character whose values on side elements are the given ones — the value at `γ` is
the crossing sum along any tile path from the base tile to the tile of `γ`, well defined by
path independence, additive under path concatenation. -/
theorem exists_crossingSum_hom (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R) :
    ∃ Φ : cycleConstrained Γ τ₀ →ₗ[ℝ] homSubmodule (↥Γ),
      ∀ (α : cycleConstrained Γ τ₀) (γ : ↥Γ), IsSideElement Γ τ₀ γ →
        (Φ α : (↥Γ) → ℝ) γ = (α : (↥Γ) → ℝ) γ := by
  classical
  choose Pth hPtile hPhead Pend hPlast hPclass using
    fun γ : ↥Γ => exists_tilePath_to hΓ hfree hε hgap hdense γ
  have hhom : ∀ α : cycleConstrained Γ τ₀, ∀ a b : ↥Γ,
      crossingSum (α : (↥Γ) → ℝ) (Pth (a * b))
        = crossingSum (α : (↥Γ) → ℝ) (Pth a) + crossingSum (α : (↥Γ) → ℝ) (Pth b) := by
    intro α a b
    set ea : ↥Γ := Pend a with hea
    set eb : ↥Γ := Pend b with heb
    set p₂' : List ↥Γ := (Pth b).map (ea * ·) with hp₂'
    have hp₂path : IsTilePath Γ τ₀ p₂' := isTilePath_map ea (hPtile b)
    have hp₂head : p₂'.head? = some ea := by
      rw [hp₂', List.head?_map, hPhead b, Option.map_some, mul_one]
    have hp₂last : p₂'.getLast? = some (ea * eb) := by
      rw [hp₂', List.getLast?_map, hPlast b, Option.map_some]
    have hglue := crossingSum_glue (α : (↥Γ) → ℝ) (hPlast a) hp₂head
    have hrpath : IsTilePath Γ τ₀ (Pth a ++ p₂'.tail) :=
      isTilePath_glue (hPtile a) hp₂path (hPlast a) hp₂head
    have hclass : (ea * eb) • τ₀ = (a * b) • τ₀ := by
      have h1 : (a⁻¹ * ea) • τ₀ = τ₀ := by
        rw [mul_smul, hPclass a, inv_smul_smul]
      have h2 := hfree (a⁻¹ * ea) ⟨τ₀, h1⟩
      calc (ea * eb) • τ₀ = (a * ((a⁻¹ * ea) * eb)) • τ₀ := by
            congr 1
            group
        _ = a • ((a⁻¹ * ea) • (eb • τ₀)) := by rw [mul_smul, mul_smul]
        _ = a • (eb • τ₀) := by rw [h2]
        _ = a • (b • τ₀) := by rw [hPclass b]
        _ = (a * b) • τ₀ := (mul_smul a b τ₀).symm
    have hPI := crossingSum_pathIndep hΓ hfree hε hgap hdense α.2
      (hPtile (a * b)) hrpath (hPhead (a * b)) (hPlast (a * b))
      ((head?_glue (q := p₂') (hPlast a)).trans (hPhead a))
      ((getLast?_glue (hPlast a) hp₂head).trans hp₂last)
      rfl ((hPclass (a * b)).trans hclass.symm)
    rw [hPI, hglue, hp₂', crossingSum_map_mul]
  refine ⟨{ toFun := fun α =>
              ⟨fun γ => crossingSum (α : (↥Γ) → ℝ) (Pth γ), fun a b => hhom α a b⟩
            map_add' := fun α β => ?_
            map_smul' := fun t α => ?_ }, ?_⟩
  · apply Subtype.ext
    funext γ
    change crossingSum ((α + β : cycleConstrained Γ τ₀) : (↥Γ) → ℝ) (Pth γ)
      = crossingSum (α : (↥Γ) → ℝ) (Pth γ) + crossingSum (β : (↥Γ) → ℝ) (Pth γ)
    rw [Submodule.coe_add, crossingSum_add]
  · apply Subtype.ext
    funext γ
    change crossingSum ((t • α : cycleConstrained Γ τ₀) : (↥Γ) → ℝ) (Pth γ)
      = t * crossingSum (α : (↥Γ) → ℝ) (Pth γ)
    rw [SetLike.val_smul, crossingSum_smul]
  · intro α γ hγside
    change crossingSum (α : (↥Γ) → ℝ) (Pth γ) = (α : (↥Γ) → ℝ) γ
    have hdirect : IsTilePath Γ τ₀ [1, γ] := by
      refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
      rw [inv_one, one_mul]
      exact hγside
    have hPI := crossingSum_pathIndep hΓ hfree hε hgap hdense α.2
      (hPtile γ) hdirect (hPhead γ) (hPlast γ) rfl (by simp) rfl (hPclass γ)
    rw [hPI, crossingSum_cons_cons, crossingSum_singleton, inv_one, one_mul]
    ring

/-- Two nonreal factors whose absolute arguments add under multiplication lie on the same
side of the real axis. -/
theorem same_sign_of_abs_arg_add {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hadd : |Complex.arg (A * B)| = |Complex.arg A| + |Complex.arg B|)
    (hAim : A.im ≠ 0) (hBim : B.im ≠ 0) : 0 < A.im * B.im := by
  have hπ := Real.pi_pos
  have hbound : ∀ z : ℂ, 0 < z.im → 0 < z.arg ∧ z.arg < Real.pi := by
    intro z hz
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) fun h => ?_,
      lt_of_le_of_ne (Complex.arg_le_pi z) fun h => ?_⟩
    · exact hz.ne (Complex.arg_eq_zero_iff.mp h.symm).2.symm
    · exact hz.ne (Complex.arg_eq_pi_iff.mp h).2.symm
  have hboundn : ∀ z : ℂ, z.im < 0 → -Real.pi < z.arg ∧ z.arg < 0 :=
    fun z hz => ⟨Complex.neg_pi_lt_arg z, Complex.arg_neg_iff.mpr hz⟩
  rcases lt_trichotomy A.im 0 with hA1 | hA1 | hA1
  · rcases lt_trichotomy B.im 0 with hB1 | hB1 | hB1
    · exact mul_pos_of_neg_of_neg hA1 hB1
    · exact absurd hB1 hBim
    · exfalso
      obtain ⟨hAa, hAb⟩ := hboundn A hA1
      obtain ⟨hBa, hBb⟩ := hbound B hB1
      have hmem : Complex.arg A + Complex.arg B ∈ Set.Ioc (-Real.pi) Real.pi :=
        ⟨by linarith, by linarith⟩
      have harg := (Complex.arg_mul_eq_add_arg_iff hA hB).mpr hmem
      rw [harg, abs_of_neg hAb, abs_of_pos hBa] at hadd
      rcases abs_cases (Complex.arg A + Complex.arg B) with ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] at hadd <;> [linarith; linarith]
  · exact absurd hA1 hAim
  · rcases lt_trichotomy B.im 0 with hB1 | hB1 | hB1
    · exfalso
      obtain ⟨hAa, hAb⟩ := hbound A hA1
      obtain ⟨hBa, hBb⟩ := hboundn B hB1
      have hmem : Complex.arg A + Complex.arg B ∈ Set.Ioc (-Real.pi) Real.pi :=
        ⟨by linarith, by linarith⟩
      have harg := (Complex.arg_mul_eq_add_arg_iff hA hB).mpr hmem
      rw [harg, abs_of_pos hAa, abs_of_neg hBb] at hadd
      rcases abs_cases (Complex.arg A + Complex.arg B) with ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] at hadd <;> [linarith; linarith]
    · exact absurd hB1 hBim
    · exact mul_pos hA1 hB1

/-- A vertical pair admits a unique metric midpoint, at the geometric mean height. -/
theorem exists_unique_mid_axis {P Q : UpperHalfPlane} (hP : P.re = 0) (hQ : Q.re = 0)
    (hPQ : P ≠ Q) :
    ∃! m : UpperHalfPlane, dist P m = dist m Q ∧ dist P m + dist m Q = dist P Q := by
  have ha : 0 < P.im := P.im_pos
  have hb : 0 < Q.im := Q.im_pos
  have hab : P.im ≠ Q.im := by
    intro h
    exact hPQ (UpperHalfPlane.ext (Complex.ext (hP.trans hQ.symm) h))
  have hMpos : 0 < Real.sqrt (P.im * Q.im) := Real.sqrt_pos.mpr (mul_pos ha hb)
  set M : UpperHalfPlane := ⟨⟨0, Real.sqrt (P.im * Q.im)⟩, hMpos⟩ with hMdef
  have hMre : M.re = 0 := rfl
  have hMim : M.im = Real.sqrt (P.im * Q.im) := rfl
  have hlM : Real.log M.im = (Real.log P.im + Real.log Q.im) / 2 := by
    rw [hMim, Real.log_sqrt (mul_pos ha hb).le, Real.log_mul ha.ne' hb.ne']
  have hdPM : dist P M = |Real.log P.im - Real.log Q.im| / 2 := by
    rw [UpperHalfPlane.dist_of_re_eq (hP.trans hMre.symm), Real.dist_eq, hlM,
      show Real.log P.im - (Real.log P.im + Real.log Q.im) / 2
        = (Real.log P.im - Real.log Q.im) / 2 by ring, abs_div, abs_two]
  have hdMQ : dist M Q = |Real.log P.im - Real.log Q.im| / 2 := by
    rw [UpperHalfPlane.dist_of_re_eq (hMre.trans hQ.symm), Real.dist_eq, hlM,
      show (Real.log P.im + Real.log Q.im) / 2 - Real.log Q.im
        = (Real.log P.im - Real.log Q.im) / 2 by ring, abs_div, abs_two]
  have hdPQ : dist P Q = |Real.log P.im - Real.log Q.im| := by
    rw [UpperHalfPlane.dist_of_re_eq (hP.trans hQ.symm), Real.dist_eq]
  refine ⟨M, ⟨by rw [hdPM, hdMQ], by rw [hdPM, hdMQ, hdPQ]; ring⟩, ?_⟩
  rintro m ⟨heq, hsum⟩
  have hmseg : m ∈ geodSeg P Q := mem_geodSeg.mpr hsum
  obtain ⟨hmre, hmlow, hmhigh⟩ := mem_geodSeg_vertical (hP.trans hQ.symm) hmseg
  have hm0 : m.re = 0 := hmre.trans hP
  have hL : 0 < m.im := m.im_pos
  have hdPm : dist P m = |Real.log P.im - Real.log m.im| := by
    rw [UpperHalfPlane.dist_of_re_eq (hP.trans hm0.symm), Real.dist_eq]
  have hdmQ : dist m Q = |Real.log m.im - Real.log Q.im| := by
    rw [UpperHalfPlane.dist_of_re_eq (hm0.trans hQ.symm), Real.dist_eq]
  have hkey : Real.log m.im = (Real.log P.im + Real.log Q.im) / 2 := by
    rw [hdPm, hdmQ] at heq
    rcases le_total P.im Q.im with hle | hle
    · rw [min_eq_left hle] at hmlow
      rw [max_eq_right hle] at hmhigh
      have h1 : Real.log P.im ≤ Real.log m.im := Real.log_le_log ha hmlow
      have h2 : Real.log m.im ≤ Real.log Q.im := Real.log_le_log hL hmhigh
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at heq
      linarith
    · rw [min_eq_right hle] at hmlow
      rw [max_eq_left hle] at hmhigh
      have h1 : Real.log Q.im ≤ Real.log m.im := Real.log_le_log hb hmlow
      have h2 : Real.log m.im ≤ Real.log P.im := Real.log_le_log hL hmhigh
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at heq
      linarith
  have hmim : m.im = M.im := by
    have h3 := congrArg Real.exp hkey
    rw [Real.exp_log hL, ← hlM, Real.exp_log M.im_pos] at h3
    exact h3
  exact UpperHalfPlane.ext (Complex.ext (hm0.trans hMre.symm) hmim)

/-- Any pair of distinct points admits a unique metric midpoint. -/
theorem exists_unique_mid (p q : UpperHalfPlane) (hpq : p ≠ q) :
    ∃! m : UpperHalfPlane, dist p m = dist m q ∧ dist p m + dist m q = dist p q := by
  obtain ⟨g, hgp, hgq⟩ := exists_verticalize p q
  have hPQ : g • p ≠ g • q := fun h => hpq (smul_left_cancel g h)
  obtain ⟨M, ⟨hM1, hM2⟩, hMuniq⟩ := exists_unique_mid_axis hgp hgq hPQ
  have htrans : ∀ z w : UpperHalfPlane, dist z w = dist (g • z) (g • w) :=
    fun z w => (dist_smul g z w).symm
  refine ⟨g⁻¹ • M, ⟨?_, ?_⟩, ?_⟩
  · rw [htrans p (g⁻¹ • M), htrans (g⁻¹ • M) q, smul_inv_smul]
    exact hM1
  · rw [htrans p (g⁻¹ • M), htrans (g⁻¹ • M) q, htrans p q, smul_inv_smul]
    exact hM2
  · rintro m ⟨h1, h2⟩
    have hgm : g • m = M := by
      refine hMuniq (g • m) ⟨?_, ?_⟩
      · rw [← htrans p m, ← htrans m q]
        exact h1
      · rw [← htrans p m, ← htrans m q, ← htrans p q]
        exact h2
    rw [← hgm, inv_smul_smul]

/-- A side element never carries the basepoint to the same orbit point as its inverse: the
midpoint of the basepoint and its translate would be fixed. -/
theorem sideElement_smul_ne_inv
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {β : ↥Γ} (hβ : IsSideElement Γ τ₀ β) : β • τ₀ ≠ β⁻¹ • τ₀ := by
  intro h
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hp : β • τ₀ ≠ τ₀ := hβ.1
  obtain ⟨m, ⟨h1, h2⟩, huniq⟩ := exists_unique_mid τ₀ (β • τ₀) (Ne.symm hp)
  have hττ : β • (β • τ₀) = τ₀ := by rw [h, smul_inv_smul]
  have hd1 : dist τ₀ (β • m) = dist (β • τ₀) m := by
    conv_lhs => rw [← hττ]
    exact dist_smul β (β • τ₀) m
  have hd2 : dist (β • m) (β • τ₀) = dist m τ₀ := dist_smul β m τ₀
  have hm1 : dist τ₀ (β • m) = dist (β • m) (β • τ₀) := by
    rw [hd1, hd2, dist_comm (β • τ₀) m, dist_comm m τ₀, ← h1]
  have hm2 : dist τ₀ (β • m) + dist (β • m) (β • τ₀) = dist τ₀ (β • τ₀) := by
    rw [hd1, hd2, dist_comm (β • τ₀) m, dist_comm m τ₀]
    linarith [h2]
  have hfix : β • m = m := huniq (β • m) ⟨hm1, hm2⟩
  exact hp (hfree β ⟨m, hfix⟩ τ₀)

/-- The odd side function supported on one side pair: value `1` on the fiber of `β` and
`-1` on the fiber of `β⁻¹`. -/
theorem exists_indicator
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {β : ↥Γ} (hβ : IsSideElement Γ τ₀ β) :
    ∃ α : (↥Γ) → ℝ, α ∈ oddSideFunctions Γ τ₀ ∧
      (∀ γ : ↥Γ, γ • τ₀ = β • τ₀ → α γ = 1) ∧
      (∀ γ : ↥Γ, γ • τ₀ = β⁻¹ • τ₀ → α γ = -1) ∧
      (∀ γ : ↥Γ, γ • τ₀ ≠ β • τ₀ → γ • τ₀ ≠ β⁻¹ • τ₀ → α γ = 0) := by
  classical
  have hne := sideElement_smul_ne_inv hfree hβ
  refine ⟨fun γ => if γ • τ₀ = β • τ₀ then 1 else if γ • τ₀ = β⁻¹ • τ₀ then -1 else 0,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro γ hγ
    have h1 : ¬ γ • τ₀ = β • τ₀ := fun h => hγ ((isSideElement_congr h).mpr hβ)
    have h2 : ¬ γ • τ₀ = β⁻¹ • τ₀ := fun h => hγ ((isSideElement_congr h).mpr hβ.inv)
    simp only [if_neg h1, if_neg h2]
  · intro γ
    by_cases c1 : γ • τ₀ = β • τ₀
    · have hinv : γ⁻¹ • τ₀ = β⁻¹ • τ₀ := inv_smul_eq_of_basepoint_eq hfree c1 τ₀
      have hno : ¬ γ⁻¹ • τ₀ = β • τ₀ := fun h => hne (h.symm.trans hinv)
      simp only [if_neg hno, if_pos hinv, if_pos c1]
    · by_cases c2 : γ • τ₀ = β⁻¹ • τ₀
      · have hinv : γ⁻¹ • τ₀ = β • τ₀ := by
          have h2 := inv_smul_eq_of_basepoint_eq hfree c2 τ₀
          rwa [inv_inv] at h2
        simp only [if_pos hinv, if_neg c1, if_pos c2]
        norm_num
      · have hno1 : ¬ γ⁻¹ • τ₀ = β • τ₀ := fun h => by
          have h2 := inv_smul_eq_of_basepoint_eq hfree h τ₀
          rw [inv_inv] at h2
          exact c2 h2
        have hno2 : ¬ γ⁻¹ • τ₀ = β⁻¹ • τ₀ := fun h => by
          have h2 := inv_smul_eq_of_basepoint_eq hfree h τ₀
          rw [inv_inv, inv_inv] at h2
          exact c1 h2
        simp only [if_neg hno1, if_neg hno2, if_neg c1, if_neg c2]
        norm_num
  · intro γ δ h
    simp only [h]
  · intro γ h
    simp only [if_pos h]
  · intro γ h
    have hno : ¬ γ • τ₀ = β • τ₀ := fun h1 => hne (h1.symm.trans h)
    simp only [if_neg hno, if_pos h]
  · intro γ h1 h2
    simp only [if_neg h1, if_neg h2]

/-- Equal side pairs identify the orbit points of their elements up to inversion. -/
theorem pair_cases (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (hγ : IsSideElement Γ τ₀ γ) (hδ : IsSideElement Γ τ₀ δ)
    (h : ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹}) :
    γ • τ₀ = δ • τ₀ ∨ γ • τ₀ = δ⁻¹ • τ₀ := by
  have hmem : dirichletSideSet Γ τ₀ γ
      ∈ ({dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} : Set (Set UpperHalfPlane)) := by
    rw [← h]
    exact Set.mem_insert _ _
  rcases hmem with h1 | h1
  · exact Or.inl (smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ h1)
  · rw [Set.mem_singleton_iff] at h1
    exact Or.inr (smul_basepoint_eq_of_sideSet_eq hΓ hfree hγ hδ.inv h1)

/-- Orbit-point identification up to inversion produces equal side pairs. -/
theorem pair_eq_of_smul_eq
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {γ δ : ↥Γ} (h : γ • τ₀ = δ • τ₀ ∨ γ • τ₀ = δ⁻¹ • τ₀) :
    ({dirichletSideSet Γ τ₀ γ, dirichletSideSet Γ τ₀ γ⁻¹} : Set (Set UpperHalfPlane))
      = {dirichletSideSet Γ τ₀ δ, dirichletSideSet Γ τ₀ δ⁻¹} := by
  rcases h with h | h
  · have hinv : γ⁻¹ • τ₀ = δ⁻¹ • τ₀ := inv_smul_eq_of_basepoint_eq hfree h τ₀
    rw [sideSet_eq_of_basepoint_eq h, sideSet_eq_of_basepoint_eq hinv]
  · have hinv : γ⁻¹ • τ₀ = δ • τ₀ := by
      have h2 := inv_smul_eq_of_basepoint_eq hfree h τ₀
      rwa [inv_inv] at h2
    rw [sideSet_eq_of_basepoint_eq h, sideSet_eq_of_basepoint_eq hinv, Set.pair_comm]

/-- The tile list of a cyclic enumeration: the consecutive tiles from position `x` through
position `x + m`. -/
def loopList (e : ℕ → ↥Γ) : ℕ → ℕ → List ↥Γ
  | x, 0 => [e x]
  | x, m + 1 => e x :: loopList e (x + 1) m

/-- The tile list of length zero is the single tile at the starting position. -/
theorem loopList_zero (e : ℕ → ↥Γ) (x : ℕ) : loopList e x 0 = [e x] := rfl

/-- The tile list unfolds from the left: one more step prepends the tile at the current
position to the list starting one position later. -/
theorem loopList_succ (e : ℕ → ↥Γ) (x m : ℕ) :
    loopList e x (m + 1) = e x :: loopList e (x + 1) m := rfl

/-- A tile list is never empty; it always contains at least its starting tile. -/
theorem loopList_ne_nil (e : ℕ → ↥Γ) (x m : ℕ) : loopList e x m ≠ [] := by
  cases m <;> simp [loopList_zero, loopList_succ]

/-- The tile list begins at the starting position. -/
theorem loopList_head? (e : ℕ → ↥Γ) (x m : ℕ) :
    (loopList e x m).head? = some (e x) := by
  cases m <;> rfl

/-- The tile list of length `m` from position `x` ends at position `x + m`. -/
theorem loopList_getLast? (e : ℕ → ↥Γ) : ∀ m x,
    (loopList e x m).getLast? = some (e (x + m)) := by
  intro m
  induction m with
  | zero => intro x; rfl
  | succ m ih =>
    intro x
    rw [loopList_succ]
    cases hm : loopList e (x + 1) m with
    | nil => exact absurd hm (loopList_ne_nil e (x + 1) m)
    | cons b l =>
      rw [List.getLast?_cons_cons, ← hm, ih (x + 1),
        show x + 1 + m = x + (m + 1) from by omega]

/-- Every tile of the list occurs at one of the enumerated positions `x, …, x + m`. -/
theorem loopList_mem (e : ℕ → ↥Γ) : ∀ m x γ, γ ∈ loopList e x m →
    ∃ i, i ≤ m ∧ γ = e (x + i) := by
  intro m
  induction m with
  | zero =>
    intro x γ hγ
    rw [loopList_zero, List.mem_singleton] at hγ
    exact ⟨0, le_rfl, by simpa using hγ⟩
  | succ m ih =>
    intro x γ hγ
    rw [loopList_succ, List.mem_cons] at hγ
    rcases hγ with rfl | hγ
    · exact ⟨0, Nat.zero_le _, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih (x + 1) γ hγ
      exact ⟨i + 1, by omega, by rw [show x + (i + 1) = x + 1 + i by omega]⟩

/-- The crossing sum along a tile list is the sum of the side function over the transition
elements between consecutive positions of the enumeration. -/
theorem crossingSum_loopList (α : (↥Γ) → ℝ) (e : ℕ → ↥Γ) : ∀ m x,
    crossingSum α (loopList e x m)
      = ∑ i ∈ Finset.range m, α ((e (x + i))⁻¹ * e (x + i + 1)) := by
  intro m
  induction m with
  | zero =>
    intro x
    rw [loopList_zero, crossingSum_singleton, Finset.sum_range_zero]
  | succ m ih =>
    intro x
    have hshape : loopList e (x + 1) m
        = e (x + 1) :: (loopList e (x + 1) m).tail := by
      cases m <;> rfl
    rw [loopList_succ, hshape, crossingSum_cons_cons, ← hshape, ih (x + 1),
      Finset.sum_range_succ']
    have hre : ∀ i, x + 1 + i = x + (i + 1) := fun i => by omega
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hre i, show x + (i + 1) + 1 = x + (i + 1) + 1 from rfl]

/-- A tile list is a tile path whenever consecutive positions of the enumeration are
separated by a genuine side element. -/
theorem isTilePath_loopList (e : ℕ → ↥Γ)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1))) : ∀ m x,
    IsTilePath Γ τ₀ (loopList e x m) := by
  intro m
  induction m with
  | zero => intro x; exact List.isChain_singleton _
  | succ m ih =>
    intro x
    have hshape : loopList e (x + 1) m
        = e (x + 1) :: (loopList e (x + 1) m).tail := by
      cases m <;> rfl
    change List.IsChain _ (loopList e x (m + 1))
    rw [loopList_succ, hshape, List.isChain_cons_cons]
    exact ⟨hadj x, by rw [← hshape]; exact ih (x + 1)⟩

/-- An `n`-periodic enumeration is invariant under shifting by any multiple of `n`. -/
theorem periodic_add_mul {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k) :
    ∀ j k, e (k + j * n) = e k := by
  intro j
  induction j with
  | zero => intro k; rw [Nat.zero_mul, Nat.add_zero]
  | succ j ih =>
    intro k
    rw [show k + (j + 1) * n = k + j * n + n from by ring, hper, ih]

/-- An `n`-periodic enumeration is determined by the residue of the position mod `n`. -/
theorem periodic_mod {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k)
    (k : ℕ) : e (k % n) = e k := by
  conv_rhs => rw [show k = k % n + (k / n) * n from by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div k n).symm]
  rw [periodic_add_mul hper]

/-- The crossing-value sum over a window of `n` consecutive positions of an `n`-periodic
enumeration is window-independent. -/
theorem W_add (α : (↥Γ) → ℝ) {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k) :
    ∀ x, ∑ i ∈ Finset.range (x + n), α ((e i)⁻¹ * e (i + 1))
      = (∑ i ∈ Finset.range x, α ((e i)⁻¹ * e (i + 1)))
        + ∑ i ∈ Finset.range n, α ((e i)⁻¹ * e (i + 1)) := by
  intro x
  induction x with
  | zero => rw [Nat.zero_add, Finset.sum_range_zero, zero_add]
  | succ x ih =>
    rw [show x + 1 + n = (x + n) + 1 from by omega, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : e (x + n) = e x := hper x
    have h2 : e (x + n + 1) = e (x + 1) := by
      rw [show x + n + 1 = x + 1 + n from by omega, hper]
    rw [h1, h2]
    ring

/-- The partial crossing sums of a periodic enumeration depend only on the position mod
`n`, once the sum over one full period vanishes: the surplus positions contribute whole
periods, each of which sums to zero. -/
theorem W_congr_mod (α : (↥Γ) → ℝ) {e : ℕ → ↥Γ} {n : ℕ} (hper : ∀ k, e (k + n) = e k)
    (hzero : ∑ i ∈ Finset.range n, α ((e i)⁻¹ * e (i + 1)) = 0) {x y : ℕ}
    (hxy : x % n = y % n) :
    ∑ i ∈ Finset.range x, α ((e i)⁻¹ * e (i + 1))
      = ∑ i ∈ Finset.range y, α ((e i)⁻¹ * e (i + 1)) := by
  have hred : ∀ z : ℕ, ∑ i ∈ Finset.range z, α ((e i)⁻¹ * e (i + 1))
      = ∑ i ∈ Finset.range (z % n), α ((e i)⁻¹ * e (i + 1)) := by
    intro z
    have hmul : ∀ j r, ∑ i ∈ Finset.range (r + j * n), α ((e i)⁻¹ * e (i + 1))
        = ∑ i ∈ Finset.range r, α ((e i)⁻¹ * e (i + 1)) := by
      intro j
      induction j with
      | zero => intro r; rw [Nat.zero_mul, Nat.add_zero]
      | succ j ih =>
        intro r
        rw [show r + (j + 1) * n = (r + j * n) + n from by ring, W_add α hper, hzero,
          add_zero, ih]
    conv_lhs => rw [show z = z % n + (z / n) * n from by
      rw [Nat.mul_comm]
      exact (Nat.mod_add_div z n).symm]
    exact hmul (z / n) (z % n)
  rw [hred x, hred y, hxy]

/-- Along a cyclic tile enumeration at a vertex, a tile adjacent to the tile at position
`x + 1` sits at position `x + 2` or at position `x`. -/
theorem step_dichotomy (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {γ δ : ↥Γ} (_hγ : γ ∈ contactSet Γ τ₀ v) (hδ : δ ∈ contactSet Γ τ₀ v)
    (hside : IsSideElement Γ τ₀ (γ⁻¹ * δ)) {x : ℕ} (hγτ : γ • τ₀ = e (x + 1) • τ₀) :
    δ • τ₀ = e (x + 2) • τ₀ ∨ δ • τ₀ = e x • τ₀ := by
  classical
  have hposdiff : ∀ a b : ℕ, e a • τ₀ = e b • τ₀ → a % n = b % n := by
    intro a b hab
    obtain ⟨k, -, hk⟩ := huniq (e a) (hcon a)
    have h1 := hk (a % n) ⟨Nat.mod_lt a (by omega), by rw [periodic_mod hper]⟩
    have h2 := hk (b % n) ⟨Nat.mod_lt b (by omega), by
      rw [periodic_mod hper]
      exact hab⟩
    rw [h1, h2]
  have hne2 : e (x + 2) • τ₀ ≠ e x • τ₀ := by
    intro hcontra
    have := hposdiff (x + 2) x hcontra
    have h2 : (x + 2) % n = x % n := this
    have hdvd : n ∣ (x + 2) - x := (Nat.modEq_iff_dvd' (by omega)).mp h2.symm
    rw [show x + 2 - x = 2 from by omega] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hrepex : ∀ p ∈ tileCenters Γ τ₀ v,
      ∃ g : ↥Γ, g ∈ contactSet Γ τ₀ v ∧ g • τ₀ = p := by
    rintro p ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  choose! rep hrep₁ hrep₂ using hrepex
  have hpP : e (x + 1) • τ₀ ∈ tileCenters Γ τ₀ v := ⟨e (x + 1), hcon (x + 1), rfl⟩
  obtain ⟨q₁, hq₁, q₂, hq₂, hq12, hchar⟩ :=
    two_neighbors hΓ hfree hε hgap hdense hv hrep₁ hrep₂ hpP
  have hsideTrans : ∀ g : ↥Γ, g ∈ contactSet Γ τ₀ v →
      ∀ w : ↥Γ, w • τ₀ = e (x + 1) • τ₀ → IsSideElement Γ τ₀ (w⁻¹ * g) →
      IsSideElement Γ τ₀ ((rep (e (x + 1) • τ₀))⁻¹ * rep (g • τ₀)) := by
    intro g hg w hw hwside
    have hgP : g • τ₀ ∈ tileCenters Γ τ₀ v := ⟨g, hg, rfl⟩
    have h1 : (w⁻¹ * g) • τ₀ = ((rep (e (x + 1) • τ₀))⁻¹ * rep (g • τ₀)) • τ₀ :=
      transition_basepoint_eq hfree (hw.trans (hrep₂ _ hpP).symm) (hrep₂ _ hgP).symm
    exact (isSideElement_congr h1).mp hwside
  have hmemplus : e (x + 2) • τ₀ = q₁ ∨ e (x + 2) • τ₀ = q₂ := by
    refine (hchar _ ⟨e (x + 2), hcon (x + 2), rfl⟩).mp ?_
    exact hsideTrans (e (x + 2)) (hcon (x + 2)) (e (x + 1)) rfl (hadj (x + 1))
  have hmemminus : e x • τ₀ = q₁ ∨ e x • τ₀ = q₂ := by
    refine (hchar _ ⟨e x, hcon x, rfl⟩).mp ?_
    refine hsideTrans (e x) (hcon x) (e (x + 1)) rfl ?_
    have h1 := (hadj x).inv
    rwa [mul_inv_rev, inv_inv] at h1
  have hmemδ : δ • τ₀ = q₁ ∨ δ • τ₀ = q₂ := by
    refine (hchar _ ⟨δ, hδ, rfl⟩).mp ?_
    exact hsideTrans δ hδ γ hγτ hside
  rcases hmemplus with h1 | h1 <;> rcases hmemminus with h2 | h2 <;>
    rcases hmemδ with h3 | h3
  · exact absurd (h1.trans h2.symm) hne2
  · exact absurd (h1.trans h2.symm) hne2
  · exact Or.inl (h3.trans h1.symm)
  · exact Or.inr (h3.trans h2.symm)
  · exact Or.inr (h3.trans h2.symm)
  · exact Or.inl (h3.trans h1.symm)
  · exact absurd (h1.trans h2.symm) hne2
  · exact absurd (h1.trans h2.symm) hne2

/-- The crossing sum of a tile path at a vertex is the difference of the crossing-value
potential between the end position and the start position of the path on the cycle. -/
theorem walk_sum (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {α : (↥Γ) → ℝ} (hodd : ∀ γ : ↥Γ, α γ⁻¹ = -α γ)
    (hfib : ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ) :
    ∀ (l : List ↥Γ) (γ : ↥Γ) (x : ℕ), IsTilePath Γ τ₀ (γ :: l) →
      (∀ g ∈ γ :: l, g ∈ contactSet Γ τ₀ v) → l.length ≤ x → γ • τ₀ = e x • τ₀ →
      ∃ y : ℕ, (γ :: l).getLast (List.cons_ne_nil γ l) • τ₀ = e y • τ₀ ∧
        crossingSum α (γ :: l)
          = (∑ i ∈ Finset.range y, α ((e i)⁻¹ * e (i + 1)))
            - ∑ i ∈ Finset.range x, α ((e i)⁻¹ * e (i + 1)) := by
  have hW : ∀ z : ℕ, ∑ i ∈ Finset.range (z + 1), α ((e i)⁻¹ * e (i + 1))
      = (∑ i ∈ Finset.range z, α ((e i)⁻¹ * e (i + 1))) + α ((e z)⁻¹ * e (z + 1)) :=
    fun z => Finset.sum_range_succ _ z
  intro l
  induction l with
  | nil =>
    intro γ x hpath hmem hlen hpos
    exact ⟨x, hpos, by rw [crossingSum_singleton, sub_self]⟩
  | cons δ l' ih =>
    intro γ x hpath hmem hlen hpos
    obtain ⟨hstep, htail⟩ := List.isChain_cons_cons.mp hpath
    have hlen' : l'.length + 1 ≤ x := by simpa using hlen
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    have hmemδ : δ ∈ contactSet Γ τ₀ v := hmem δ (List.mem_cons_of_mem γ (List.mem_cons_self))
    have hmemtail : ∀ g ∈ δ :: l', g ∈ contactSet Γ τ₀ v :=
      fun g hg => hmem g (List.mem_cons_of_mem γ hg)
    have hdich := step_dichotomy hΓ hfree hε hgap hdense hv hn3 hper hcon huniq hadj
      (hmem γ List.mem_cons_self) hmemδ hstep hpos
    have hlast : (γ :: δ :: l').getLast (List.cons_ne_nil γ (δ :: l'))
        = (δ :: l').getLast (List.cons_ne_nil δ l') := List.getLast_cons _
    rcases hdich with hδpos | hδpos
    · obtain ⟨y, hy1, hy2⟩ := ih δ (x' + 2) htail hmemtail (by omega) hδpos
      refine ⟨y, by rw [hlast]; exact hy1, ?_⟩
      rw [crossingSum_cons_cons, hy2]
      have hα : α (γ⁻¹ * δ) = α ((e (x' + 1))⁻¹ * e (x' + 2)) :=
        hfib _ _ (transition_basepoint_eq hfree hpos hδpos)
      rw [hα]
      have h1 := hW (x' + 1)
      linarith
    · obtain ⟨y, hy1, hy2⟩ := ih δ x' htail hmemtail (by omega) hδpos
      refine ⟨y, by rw [hlast]; exact hy1, ?_⟩
      rw [crossingSum_cons_cons, hy2]
      have hα : α (γ⁻¹ * δ) = α ((e (x' + 1))⁻¹ * e x') :=
        hfib _ _ (transition_basepoint_eq hfree hpos hδpos)
      have hα2 : α ((e (x' + 1))⁻¹ * e x') = -α ((e x')⁻¹ * e (x' + 1)) := by
        have h1 := hodd ((e x')⁻¹ * e (x' + 1))
        rwa [mul_inv_rev, inv_inv] at h1
      rw [hα, hα2]
      have h1 := hW x'
      linarith

/-- On a cyclic tile enumeration, equal tiles have equal positions modulo the period. -/
theorem position_mod_eq {v : UpperHalfPlane}
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    {a b : ℕ} (hab : e a • τ₀ = e b • τ₀) : a % n = b % n := by
  obtain ⟨k, -, hk⟩ := huniq (e a) (hcon a)
  have h1 := hk (a % n) ⟨Nat.mod_lt a (by omega), by rw [periodic_mod hper]⟩
  have h2 := hk (b % n) ⟨Nat.mod_lt b (by omega), by
    rw [periodic_mod hper]
    exact hab⟩
  rw [h1, h2]

/-- If the full-cycle crossing sum at a vertex vanishes, so does the crossing sum of every
vertex loop there. -/
theorem closed_loop_sum (hΓ : IsFuchsianGroup Γ)
    (hfree : ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {ε R : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ R)
    {v : UpperHalfPlane} (hv : v ∈ polygonVertices Γ τ₀)
    {n : ℕ} {e : ℕ → ↥Γ} (hn3 : 3 ≤ n) (hper : ∀ k, e (k + n) = e k)
    (hcon : ∀ k, e k ∈ contactSet Γ τ₀ v)
    (huniq : ∀ γ ∈ contactSet Γ τ₀ v, ∃! k, k < n ∧ γ • τ₀ = e k • τ₀)
    (hadj : ∀ k, IsSideElement Γ τ₀ ((e k)⁻¹ * e (k + 1)))
    {α : (↥Γ) → ℝ} (hodd : ∀ γ : ↥Γ, α γ⁻¹ = -α γ)
    (hfib : ∀ γ δ : ↥Γ, γ • τ₀ = δ • τ₀ → α γ = α δ)
    (hzero : ∑ i ∈ Finset.range n, α ((e i)⁻¹ * e (i + 1)) = 0)
    {p : List ↥Γ} (hp : IsVertexLoop Γ τ₀ v p) : crossingSum α p = 0 := by
  obtain ⟨hpath, hmemp, hclose⟩ := hp
  cases p with
  | nil => simp [crossingSum]
  | cons γ l =>
    obtain ⟨k₀, ⟨hk₀n, hk₀⟩, -⟩ := huniq γ (hmemp γ List.mem_cons_self)
    have hx : γ • τ₀ = e (k₀ + (l.length + 1) * n) • τ₀ := by
      rw [periodic_add_mul hper]
      exact hk₀
    have hlen : l.length ≤ k₀ + (l.length + 1) * n := by
      have h1 : l.length + 1 ≤ (l.length + 1) * n := Nat.le_mul_of_pos_right _ (by omega)
      omega
    obtain ⟨y, hy1, hy2⟩ := walk_sum hΓ hfree hε hgap hdense hv hn3 hper hcon huniq
      hadj hodd hfib l γ _ hpath hmemp hlen hx
    have hlasteq : γ = (γ :: l).getLast (List.cons_ne_nil γ l) := by
      have h1 : (γ :: l).head? = some γ := rfl
      have h2 : (γ :: l).getLast? = some ((γ :: l).getLast (List.cons_ne_nil γ l)) :=
        List.getLast?_eq_some_getLast _
      rw [h1, h2] at hclose
      exact Option.some_injective _ hclose
    have hclosepos : e y • τ₀ = e (k₀ + (l.length + 1) * n) • τ₀ := by
      rw [← hy1, ← hlasteq, hx]
    have hmodeq := position_mod_eq hn3 hper hcon huniq hclosepos
    rw [hy2, W_congr_mod α hper hzero hmodeq, sub_self]

/-- Frame ratios are invariant under the Möbius action: the unimodular frame factor
cancels. -/
theorem discChart_ratio_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z w x : UpperHalfPlane) :
    discChart (g • z) (g • x) / discChart (g • z) (g • w) = discChart z x / discChart z w := by
  have hzim : ((z : ℂ)).im ≠ 0 := by rw [UpperHalfPlane.coe_im]; exact z.im_pos.ne'
  have hzbim : (((starRingEnd ℂ) (z : ℂ))).im ≠ 0 := by
    rw [Complex.conj_im, UpperHalfPlane.coe_im]
    simpa using z.im_pos.ne'
  have hμ : (((g 1 0 : ℝ) : ℂ) * (starRingEnd ℂ) (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) /
      (((g 1 0 : ℝ) : ℂ) * (z : ℂ) + ((g 1 1 : ℝ) : ℂ)) ≠ 0 :=
    div_ne_zero (denom_ne_zero g hzbim) (denom_ne_zero g hzim)
  rw [discChart_smul g z x, discChart_smul g z w, mul_div_mul_left _ _ hμ]

/-- The frame-ratio imaginary part at a bisector point, computed in the normalizing frame:
the direction toward another bisector point is real, of the sign of the height increment. -/
theorem ratio_im_formula {p q : UpperHalfPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} {ε' : ℝ} (hε' : ε' = 1 ∨ ε' = -1)
    (hle : ∀ z : UpperHalfPlane, dist z p ≤ dist z q ↔ ε' * (g • z).re ≤ 0)
    (hge : ∀ z : UpperHalfPlane, dist z q ≤ dist z p ↔ 0 ≤ ε' * (g • z).re)
    {u w : UpperHalfPlane} (hu : dist u p = dist u q) (hw : dist w p = dist w q)
    (x : UpperHalfPlane) :
    (discChart u x / discChart u w).im
      = (discChart (g • u) (g • x)).im
        * (((g • w).im + (g • u).im) / ((g • w).im - (g • u).im)) := by
  have hgu : (g • u).re = 0 := normalizer_re_eq_zero hε' hle hge hu
  have hgw : (g • w).re = 0 := normalizer_re_eq_zero hε' hle hge hw
  rw [← discChart_ratio_smul g u w x, discChart_axis hgu hgw, div_ofReal_im,
    div_div_eq_mul_div, mul_div_assoc]

end RiemannDynamics
