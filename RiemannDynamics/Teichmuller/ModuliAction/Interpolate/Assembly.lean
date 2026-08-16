/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.ModuliAction.Interpolate.Estimates

/-!
# Interpolation, IV: assembly of the developed interpolation

The uniform two-sided ball bounds for the developed map, the global homeomorphism from
uniform ball injectivity and surjectivity, and the headline theorem
`exists_developed_interpolation`: the development of the corrected tile maps into a
global self-map of the upper half plane with two-sided inverse, locally Sobolev, with
positive Jacobian and Beltrami coefficient at most `κ`, intertwining the generator
tuples exactly.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-! ## The development of the corrected tile maps: assembly -/

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The uniform ball estimates transport the contraction data through hyperbolic isometries;
-- the default heartbeat budget does not cover the elaboration.
/-- **Uniform two-sided ball bounds for the developed map**: exact equivariance, transport
of base points into the analyzed region and the near-identity derivative bounds there give
injectivity on hyperbolic quarter-balls and surjectivity onto hyperbolic balls of a fixed
radius around image points, at every point of the upper half plane. -/
private lemma zz_uniform {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (θ : ↥Γ' → Matrix.SpecialLinearGroup (Fin 2) ℝ) (F : ℂ → ℂ) (UKb : Set ℂ)
    (Cv : ℝ)
    (htr : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ) (hw : 0 < w.im), w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w ∧
      ∀ (x : ℂ) (hx : 0 < x.im),
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 → x ∈ UKb)
    (hequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      F (moebiusMap (↑β) z) = moebiusMap (θ β) (F z))
    (hFim : ∀ z : ℂ, 0 < z.im → 0 < (F z).im)
    (hd : ∀ w ∈ UKb, DifferentiableAt ℝ F w)
    (hop : ∀ w ∈ UKb, ‖fderiv ℝ F w - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hval : ∀ w ∈ UKb, ‖F w - w‖ ≤ Cv)
    (hCvim : ∀ w : ℂ, w ∈ UKb → Cv ≤ w.im)
    (hUKbsub : UKb ⊆ {x : ℂ | 0 < x.im}) :
    (∀ (z a b : ℂ) (hz : 0 < z.im) (ha : 0 < a.im) (hb : 0 < b.im),
      dist (⟨a, ha⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) < 1 / 4 →
      dist (⟨b, hb⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) < 1 / 4 →
      F a = F b → a = b) ∧
    (∀ (z ξ : ℂ) (hz : 0 < z.im) (hξ : 0 < ξ.im) (hFz : 0 < (F z).im),
      dist (⟨ξ, hξ⟩ : UpperHalfPlane) (⟨F z, hFz⟩ : UpperHalfPlane) < 1 / 2048 →
      ∃ (x : ℂ) (hx : 0 < x.im),
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) < 1 / 32 ∧ F x = ξ) := by
  -- Möbius maps are injective on the upper half plane
  have hinvmoe : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x y : ℂ),
      0 < x.im → 0 < y.im → moebiusMap g x = moebiusMap g y → x = y := by
    intro g x y hx hy hxy
    have hcanc : ∀ u : ℂ, 0 < u.im → moebiusMap g⁻¹ (moebiusMap g u) = u := by
      intro u hu
      rw [moebiusMap_mul g⁻¹ g u (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hu)),
        inv_mul_cancel, moebiusMap_one]
    calc x = moebiusMap g⁻¹ (moebiusMap g x) := (hcanc x hx).symm
      _ = moebiusMap g⁻¹ (moebiusMap g y) := by rw [hxy]
      _ = y := hcanc y hy
  have hcanc : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (u : ℂ), 0 < u.im →
      moebiusMap g (moebiusMap g⁻¹ u) = u := by
    intro g u hu
    rw [moebiusMap_mul g g⁻¹ u (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hu)),
      mul_inv_cancel, moebiusMap_one]
  -- transported points and distances
  have hmk : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : ℂ) (hx : 0 < x.im),
      (⟨moebiusMap g x, moebiusMap_im_pos g hx⟩ : UpperHalfPlane)
        = g • (⟨x, hx⟩ : UpperHalfPlane) := by
    intro g x hx
    ext
    change moebiusMap g x = ((g • (⟨x, hx⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
    rw [coe_smul_eq_moebiusMap g (⟨x, hx⟩ : UpperHalfPlane)]
  have hdsmul : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x y : ℂ)
      (hx : 0 < x.im) (hy : 0 < y.im),
      dist (⟨moebiusMap g x, moebiusMap_im_pos g hx⟩ : UpperHalfPlane)
        (⟨moebiusMap g y, moebiusMap_im_pos g hy⟩ : UpperHalfPlane)
        = dist (⟨x, hx⟩ : UpperHalfPlane) (⟨y, hy⟩ : UpperHalfPlane) := by
    intro g x y hx hy
    rw [hmk g x hx, hmk g y hy]
    exact (isometry_smul UpperHalfPlane g).dist_eq _ _
  constructor
  · -- injectivity on hyperbolic quarter-balls
    intro z a b hz ha hb hda hdb hFab
    obtain ⟨γ, w, hw, hwUKb, hwdef, hzw, hball⟩ := htr z hz
    obtain ⟨a', ha'def⟩ : ∃ x : ℂ, x = moebiusMap (↑(γ⁻¹ : ↥Γ')) a := ⟨_, rfl⟩
    obtain ⟨b', hb'def⟩ : ∃ x : ℂ, x = moebiusMap (↑(γ⁻¹ : ↥Γ')) b := ⟨_, rfl⟩
    have ha'im : 0 < a'.im := by
      rw [ha'def]
      exact moebiusMap_im_pos _ ha
    have hb'im : 0 < b'.im := by
      rw [hb'def]
      exact moebiusMap_im_pos _ hb
    have hda' : dist (⟨a', ha'im⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 := by
      have h1 : (⟨a', ha'im⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) a, moebiusMap_im_pos _ ha⟩ : UpperHalfPlane) := by
        ext
        change a' = moebiusMap (↑(γ⁻¹ : ↥Γ')) a
        exact ha'def
      have h2 : (⟨w, hw⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) z, moebiusMap_im_pos _ hz⟩ : UpperHalfPlane) := by
        ext
        change w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z
        exact hwdef
      rw [h1, h2, hdsmul (↑(γ⁻¹ : ↥Γ')) a z ha hz]
      exact hda
    have hdb' : dist (⟨b', hb'im⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 := by
      have h1 : (⟨b', hb'im⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) b, moebiusMap_im_pos _ hb⟩ : UpperHalfPlane) := by
        ext
        change b' = moebiusMap (↑(γ⁻¹ : ↥Γ')) b
        exact hb'def
      have h2 : (⟨w, hw⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) z, moebiusMap_im_pos _ hz⟩ : UpperHalfPlane) := by
        ext
        change w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z
        exact hwdef
      rw [h1, h2, hdsmul (↑(γ⁻¹ : ↥Γ')) b z hb hz]
      exact hdb
    -- the euclidean form of the quarter-ball
    obtain ⟨S, hSdef⟩ : ∃ S : Set ℂ, S = Metric.ball
        ((((((⟨w, hw⟩ : UpperHalfPlane) : ℂ)).re : ℝ) : ℂ)
          + (((⟨w, hw⟩ : UpperHalfPlane).im * Real.cosh (1 / 4) : ℝ) : ℂ) * Complex.I)
        ((⟨w, hw⟩ : UpperHalfPlane).im * Real.sinh (1 / 4)) := ⟨_, rfl⟩
    have hSmem : ∀ x : ℂ, x ∈ S ↔ ∃ hx : 0 < x.im,
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 := by
      intro x
      rw [hSdef]
      exact zz_ball (⟨w, hw⟩ : UpperHalfPlane) (1 / 4) (by norm_num) x
    have hSsub : S ⊆ UKb := by
      intro x hx
      obtain ⟨hxim, hxd⟩ := (hSmem x).mp hx
      exact hball x hxim hxd
    have hSconv : Convex ℝ S := by
      rw [hSdef]
      exact convex_ball _ _
    have hinjS : Set.InjOn F S :=
      zz_inj F S hSconv (fun x hx => hd x (hSsub hx)) (fun x hx => hop x (hSsub hx))
    -- pulled equality of values
    have haeq : a = moebiusMap (↑γ) a' := by
      rw [ha'def]
      rw [show ((↑(γ⁻¹ : ↥Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        = ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ from rfl]
      exact (hcanc (↑γ) a ha).symm
    have hbeq : b = moebiusMap (↑γ) b' := by
      rw [hb'def]
      rw [show ((↑(γ⁻¹ : ↥Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        = ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ from rfl]
      exact (hcanc (↑γ) b hb).symm
    have hFa'b' : F a' = F b' := by
      have h1 : F a = moebiusMap (θ γ) (F a') := by
        rw [haeq]
        exact hequi γ a' ha'im
      have h2 : F b = moebiusMap (θ γ) (F b') := by
        rw [hbeq]
        exact hequi γ b' hb'im
      rw [h1, h2] at hFab
      exact hinvmoe (θ γ) (F a') (F b') (hFim a' ha'im) (hFim b' hb'im) hFab
    have ha'b' : a' = b' :=
      hinjS ((hSmem a').mpr ⟨ha'im, hda'⟩) ((hSmem b').mpr ⟨hb'im, hdb'⟩) hFa'b'
    rw [haeq, hbeq, ha'b']
  · -- surjectivity onto fixed hyperbolic balls around image points
    intro z ξ hz hξ hFz hdist
    obtain ⟨γ, w, hw, hwUKb, hwdef, hzw, hball⟩ := htr z hz
    have hwim := hw
    -- the closed base ball lies in the analyzed region
    have hcBsub : Metric.closedBall w (w.im / 128) ⊆ UKb := by
      intro x hx
      rw [Metric.mem_closedBall] at hx
      have hxball : x ∈ Metric.ball ((⟨w, hw⟩ : UpperHalfPlane) : ℂ)
          ((⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2) := by
        rw [Metric.mem_ball]
        change dist x w < (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2
        have h64 : (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2 = w.im / 64 := by
          change w.im * (1 / 32) / 2 = w.im / 64
          ring
        rw [h64]
        have hwpos : 0 < w.im := hw
        linarith
      obtain ⟨hxim, hxd⟩ := (zz_ballcomp (⟨w, hw⟩ : UpperHalfPlane) (1 / 32)
        (by norm_num) (by norm_num)).1 x hxball
      exact hball x hxim (lt_trans hxd (by norm_num))
    have hr128 : 0 < w.im / 128 := by
      have hwpos : 0 < w.im := hw
      positivity
    obtain ⟨hinjcB, hsurjcB⟩ := zz_surj F w (w.im / 128) hr128
      (fun x hx => hd x (hcBsub hx)) (fun x hx => hop x (hcBsub hx))
    obtain ⟨ξ', hξ'def⟩ : ∃ x : ℂ, x = moebiusMap (θ γ)⁻¹ ξ := ⟨_, rfl⟩
    have hξ'im : 0 < ξ'.im := by
      rw [hξ'def]
      exact moebiusMap_im_pos _ hξ
    have hFweq : F z = moebiusMap (θ γ) (F w) := by
      conv_lhs => rw [hzw]
      exact hequi γ w hw
    have hFwim : 0 < (F w).im := hFim w hw
    have hdξ' : dist (⟨ξ', hξ'im⟩ : UpperHalfPlane) (⟨F w, hFwim⟩ : UpperHalfPlane)
        < 1 / 2048 := by
      have h1 : (⟨ξ, hξ⟩ : UpperHalfPlane)
          = (⟨moebiusMap (θ γ) ξ', moebiusMap_im_pos _ hξ'im⟩ : UpperHalfPlane) := by
        ext
        change ξ = moebiusMap (θ γ) ξ'
        rw [hξ'def]
        exact (hcanc (θ γ) ξ hξ).symm
      have h2 : (⟨F z, hFz⟩ : UpperHalfPlane)
          = (⟨moebiusMap (θ γ) (F w), moebiusMap_im_pos _ hFwim⟩ : UpperHalfPlane) := by
        ext
        change F z = moebiusMap (θ γ) (F w)
        exact hFweq
      rw [h1, h2, hdsmul (θ γ) ξ' (F w) hξ'im hFwim] at hdist
      exact hdist
    have himFw : (F w).im ≤ 2 * w.im := by
      have h1 : |(F w - w).im| ≤ ‖F w - w‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 := hval w hwUKb
      have h3 := hCvim w hwUKb
      have h4 := (abs_le.mp h1).2
      linarith
    have hξ'E : ξ' ∈ Metric.closedBall (F w) (w.im / 128 / 4) := by
      have h1 := (zz_ballcomp (⟨F w, hFwim⟩ : UpperHalfPlane) (1 / 2048)
        (by norm_num) (by norm_num)).2 ξ' hξ'im hdξ'
      rw [Metric.mem_ball] at h1
      have hcoe : dist ξ' ((⟨F w, hFwim⟩ : UpperHalfPlane) : ℂ) = dist ξ' (F w) := rfl
      have himeq : 2 * (⟨F w, hFwim⟩ : UpperHalfPlane).im * (1 / 2048)
          = 2 * (F w).im * (1 / 2048) := rfl
      rw [hcoe, himeq] at h1
      rw [Metric.mem_closedBall]
      have h2 : 2 * (F w).im * (1 / 2048) ≤ w.im / 128 / 4 := by
        have hwpos : 0 < w.im := hw
        nlinarith [himFw]
      linarith
    obtain ⟨x, hxcB, hFx⟩ := hsurjcB ξ' hξ'E
    have hxUKb := hcBsub hxcB
    have hxim : 0 < x.im := hUKbsub hxUKb
    have hxE64 : x ∈ Metric.ball ((⟨w, hw⟩ : UpperHalfPlane) : ℂ)
        ((⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2) := by
      rw [Metric.mem_ball]
      change dist x w < (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2
      have h64 : (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2 = w.im / 64 := by
        change w.im * (1 / 32) / 2 = w.im / 64
        ring
      rw [h64]
      rw [Metric.mem_closedBall] at hxcB
      have hwpos : 0 < w.im := hw
      linarith
    obtain ⟨hxim', hxd⟩ := (zz_ballcomp (⟨w, hw⟩ : UpperHalfPlane) (1 / 32)
      (by norm_num) (by norm_num)).1 x hxE64
    obtain ⟨X, hXdef⟩ : ∃ X : ℂ, X = moebiusMap (↑γ) x := ⟨_, rfl⟩
    have hXim : 0 < X.im := by
      rw [hXdef]
      exact moebiusMap_im_pos _ hxim'
    refine ⟨X, hXim, ?_, ?_⟩
    · have h1 : (⟨X, hXim⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑γ) x, moebiusMap_im_pos _ hxim'⟩ : UpperHalfPlane) := by
        ext
        change X = moebiusMap (↑γ) x
        exact hXdef
      have h2 : (⟨z, hz⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑γ) w, moebiusMap_im_pos _ hw⟩ : UpperHalfPlane) := by
        ext
        change z = moebiusMap (↑γ) w
        exact hzw
      rw [h1, h2, hdsmul (↑γ) x w hxim' hw]
      exact hxd
    · rw [hXdef]
      have h1 : F (moebiusMap (↑γ) x) = moebiusMap (θ γ) (F x) := hequi γ x hxim'
      rw [h1, hFx, hξ'def]
      exact hcanc (θ γ) ξ hξ

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The covering-space construction assembles trivializations from the uniform ball bounds;
-- the default heartbeat budget does not cover the elaboration.
/-- **Bijectivity of a uniformly balanced self-map of the upper half plane**: a continuous
open map with uniform ball injectivity and uniform ball surjectivity is a covering map of
the simply connected upper half plane, hence bijective. -/
private lemma zz_homeo (p : UpperHalfPlane → UpperHalfPlane)
    (hpc : Continuous p)
    (hopen : IsOpenMap p)
    (hinj : ∀ z a b : UpperHalfPlane, dist a z < 1 / 4 → dist b z < 1 / 4 →
      p a = p b → a = b)
    (hsurj : ∀ z ξ : UpperHalfPlane, dist ξ (p z) < 1 / 2048 →
      ∃ x : UpperHalfPlane, dist x z < 1 / 32 ∧ p x = ξ) :
    Function.Bijective p := by
  -- ==== surjectivity: the range is clopen in a preconnected space ====
  have hsurj_glob : Function.Surjective p := by
    have hropen : IsOpen (Set.range p) := by
      rw [show Set.range p = p '' Set.univ from (Set.image_univ).symm]
      exact hopen _ isOpen_univ
    have hrclosed : IsClosed (Set.range p) := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro ξ hξ
      rw [Metric.mem_nhds_iff]
      refine ⟨1 / 2048, by norm_num, ?_⟩
      intro η hη
      rw [Metric.mem_ball] at hη
      intro hmem
      obtain ⟨z, hz⟩ := hmem
      refine hξ ?_
      obtain ⟨x, _, hxp⟩ := hsurj z ξ (by
        rw [hz]
        rwa [dist_comm] at hη)
      exact ⟨x, hxp⟩
    have hne : (Set.range p).Nonempty := ⟨p UpperHalfPlane.I, ⟨UpperHalfPlane.I, rfl⟩⟩
    have huniv : Set.range p = Set.univ := IsClopen.eq_univ ⟨hrclosed, hropen⟩ hne
    exact Set.range_eq_univ.mp huniv
  -- ==== the covering structure ====
  have hcov : IsCoveringMap p := by
    intro ξ
    -- discreteness of the fiber
    have hdisc : DiscreteTopology ↥(p ⁻¹' {ξ}) := by
      rw [discreteTopology_iff_isOpen_singleton]
      rintro ⟨e, he⟩
      have hset : ({(⟨e, he⟩ : ↥(p ⁻¹' {ξ}))} : Set ↥(p ⁻¹' {ξ}))
          = Subtype.val ⁻¹' (Metric.ball e (1 / 4)) := by
        ext ⟨x, hx⟩
        simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball,
          Subtype.mk.injEq]
        constructor
        · rintro rfl
          rw [dist_self]
          norm_num
        · intro hdx
          have hpe : p x = p e := by
            rw [Set.mem_preimage, Set.mem_singleton_iff] at hx he
            rw [hx, he]
          exact hinj x x e (by rw [dist_self]; norm_num)
            (by rw [dist_comm]; exact hdx) hpe
      rw [hset]
      exact (Metric.isOpen_ball).preimage continuous_subtype_val
    -- the trivializing data
    have hsheet : ∀ z : ↥(p ⁻¹' Metric.ball ξ (1 / 2048)), ∃ e : ↥(p ⁻¹' {ξ}),
        dist (z : UpperHalfPlane) (e : UpperHalfPlane) < 1 / 32 := by
      rintro ⟨z, hz⟩
      rw [Set.mem_preimage, Metric.mem_ball] at hz
      obtain ⟨x, hxd, hxp⟩ := hsurj z ξ (by rwa [dist_comm] at hz)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact hxp
      · rw [dist_comm] at hxd
        exact hxd
    choose sh hsh using hsheet
    have hshuniq : ∀ (z : ↥(p ⁻¹' Metric.ball ξ (1 / 2048))) (e : ↥(p ⁻¹' {ξ})),
        dist (z : UpperHalfPlane) (e : UpperHalfPlane) < 1 / 8 → e = sh z := by
      intro z e hd
      have h1 := hsh z
      have hpe : p (e : UpperHalfPlane) = p (sh z : UpperHalfPlane) := by
        have he' := (e : ↥(p ⁻¹' {ξ})).2
        have hs' := (sh z).2
        rw [Set.mem_preimage, Set.mem_singleton_iff] at he' hs'
        rw [he', hs']
      refine Subtype.ext ?_
      refine hinj (z : UpperHalfPlane) (e : UpperHalfPlane) ((sh z : UpperHalfPlane))
        ?_ ?_ hpe
      · calc dist (e : UpperHalfPlane) (z : UpperHalfPlane)
            = dist (z : UpperHalfPlane) (e : UpperHalfPlane) := dist_comm _ _
          _ < 1 / 8 := hd
          _ < 1 / 4 := by norm_num
      · calc dist ((sh z : UpperHalfPlane)) (z : UpperHalfPlane)
            = dist (z : UpperHalfPlane) ((sh z : UpperHalfPlane)) := dist_comm _ _
          _ < 1 / 32 := h1
          _ < 1 / 4 := by norm_num
    have hsec : ∀ (u : ↥(Metric.ball ξ (1 / 2048))) (e : ↥(p ⁻¹' {ξ})),
        ∃ x : UpperHalfPlane, dist x (e : UpperHalfPlane) < 1 / 32
          ∧ p x = (u : UpperHalfPlane) := by
      rintro ⟨u, hu⟩ ⟨e, he⟩
      rw [Metric.mem_ball] at hu
      rw [Set.mem_preimage, Set.mem_singleton_iff] at he
      obtain ⟨x, hxd, hxp⟩ := hsurj e u (by rw [he]; exact hu)
      exact ⟨x, hxd, hxp⟩
    choose sec hsecd hsecp using hsec
    -- assemble the trivializing homeomorphism
    refine ⟨hdisc, Metric.ball ξ (1 / 2048), Metric.mem_ball_self (by norm_num),
      Metric.isOpen_ball, Metric.isOpen_ball.preimage hpc, ?_, ?_⟩
    · refine ⟨⟨fun z => (⟨p (z : UpperHalfPlane), z.2⟩, sh z),
        fun ue => ⟨sec ue.1 ue.2, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      · rw [Set.mem_preimage, hsecp ue.1 ue.2]
        exact ue.1.2
      · -- left inverse
        intro z
        refine Subtype.ext ?_
        have h1 := hsecd (⟨p (z : UpperHalfPlane), z.2⟩ : ↥(Metric.ball ξ (1 / 2048))) (sh z)
        have h2 := hsecp (⟨p (z : UpperHalfPlane), z.2⟩ : ↥(Metric.ball ξ (1 / 2048))) (sh z)
        have h3 := hsh z
        refine hinj ((sh z : UpperHalfPlane))
          (sec (⟨p (z : UpperHalfPlane), z.2⟩ : ↥(Metric.ball ξ (1 / 2048))) (sh z))
          (z : UpperHalfPlane) ?_ ?_ ?_
        · calc dist (sec _ (sh z)) ((sh z : UpperHalfPlane)) < 1 / 32 := h1
            _ < 1 / 4 := by norm_num
        · calc dist (z : UpperHalfPlane) ((sh z : UpperHalfPlane)) < 1 / 32 := h3
            _ < 1 / 4 := by norm_num
        · rw [h2]
      · -- right inverse
        rintro ⟨u, e⟩
        refine Prod.ext ?_ ?_
        · refine Subtype.ext ?_
          exact hsecp u e
        · refine (hshuniq _ e ?_).symm
          calc dist ((sec u e : UpperHalfPlane)) ((e : UpperHalfPlane)) < 1 / 32 :=
              hsecd u e
            _ < 1 / 8 := by norm_num
      · -- continuity of the forward map
        refine Continuous.prodMk ?_ ?_
        · exact Continuous.subtype_mk (hpc.comp continuous_subtype_val) _
        · rw [continuous_discrete_rng]
          intro e
          have hset : (fun z : ↥(p ⁻¹' Metric.ball ξ (1 / 2048)) => sh z) ⁻¹' {e}
              = Subtype.val ⁻¹' (Metric.ball (e : UpperHalfPlane) (1 / 8)) := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball]
            constructor
            · intro hze
              rw [← hze]
              have := hsh z
              rw [dist_comm] at this
              calc dist ((z : UpperHalfPlane)) ((sh z : UpperHalfPlane)) < 1 / 32 := hsh z
                _ < 1 / 8 := by norm_num
            · intro hd
              exact (hshuniq z e hd).symm
          rw [hset]
          exact (Metric.isOpen_ball).preimage continuous_subtype_val
      · -- continuity of the inverse map
        rw [continuous_iff_continuousAt]
        rintro ⟨u, e⟩
        have hslice : ∀ᶠ v : ↥(Metric.ball ξ (1 / 2048)) × ↥(p ⁻¹' {ξ})
            in nhds (u, e), v.2 = e := by
          have h1 : ({e} : Set ↥(p ⁻¹' {ξ})) ∈ nhds e := by
            rw [nhds_discrete]
            exact Set.mem_singleton e
          have h2 : (Set.univ ×ˢ ({e} : Set ↥(p ⁻¹' {ξ}))) ∈ nhds ((u, e)) := by
            rw [nhds_prod_eq]
            exact Filter.prod_mem_prod Filter.univ_mem h1
          filter_upwards [h2] with v hv
          exact hv.2
        -- continuity of the fixed-sheet section
        have hseccont : Continuous fun u' : ↥(Metric.ball ξ (1 / 2048)) => sec u' e := by
          rw [continuous_iff_continuousAt]
          intro u'
          rw [ContinuousAt, Filter.tendsto_iff_forall_eventually_mem]
          intro W hW
          rw [Metric.mem_nhds_iff] at hW
          obtain ⟨r, hr, hrW⟩ := hW
          obtain ⟨r', hr'def⟩ : ∃ x : ℝ, x = min r (1 / 48) := ⟨_, rfl⟩
          have hr'0 : 0 < r' := by
            rw [hr'def]
            exact lt_min hr (by norm_num)
          have hT : IsOpen (p '' Metric.ball (sec u' e) r') := hopen _ Metric.isOpen_ball
          have hTmem : (u' : UpperHalfPlane) ∈ p '' Metric.ball (sec u' e) r' := by
            refine ⟨sec u' e, Metric.mem_ball_self hr'0, hsecp u' e⟩
          have hnb : Subtype.val ⁻¹' (p '' Metric.ball (sec u' e) r')
              ∈ nhds u' := by
            refine (hT.preimage continuous_subtype_val).mem_nhds ?_
            exact hTmem
          filter_upwards [hnb] with u'' hu''
          rw [Set.mem_preimage] at hu''
          obtain ⟨y, hyball, hyp⟩ := hu''
          rw [Metric.mem_ball] at hyball
          -- the section value at u'' equals y
          have hyeq : sec u'' e = y := by
            refine hinj ((e : UpperHalfPlane)) (sec u'' e) y ?_ ?_ ?_
            · calc dist (sec u'' e) ((e : UpperHalfPlane)) < 1 / 32 := hsecd u'' e
                _ < 1 / 4 := by norm_num
            · have hd1 : dist y (sec u' e) < 1 / 48 := by
                refine lt_of_lt_of_le hyball ?_
                rw [hr'def]
                exact min_le_right _ _
              have hd2 : dist (sec u' e) ((e : UpperHalfPlane)) < 1 / 32 := hsecd u' e
              calc dist y ((e : UpperHalfPlane))
                  ≤ dist y (sec u' e) + dist (sec u' e) ((e : UpperHalfPlane)) :=
                    dist_triangle _ _ _
                _ < 1 / 48 + 1 / 32 := by exact add_lt_add hd1 hd2
                _ < 1 / 4 := by norm_num
            · rw [hsecp u'' e, hyp]
          rw [hyeq]
          refine hrW ?_
          rw [Metric.mem_ball]
          refine lt_of_lt_of_le hyball ?_
          rw [hr'def]
          exact min_le_left _ _
        -- combine along the constant-sheet slice
        have hcomb0 : Continuous (fun v : ↥(Metric.ball ξ (1 / 2048))
            × ↥(p ⁻¹' {ξ}) => (⟨sec v.1 e, by
              rw [Set.mem_preimage, hsecp v.1 e]
              exact v.1.2⟩ : ↥(p ⁻¹' Metric.ball ξ (1 / 2048)))) := by
          refine Continuous.subtype_mk ?_ _
          exact hseccont.fst'
        have hcombined := hcomb0.continuousAt (x := (u, e))
        refine hcombined.congr ?_
        filter_upwards [hslice] with v hv
        rw [← hv]
    · intro z
      rfl
  -- ==== injectivity via monodromy over the simply connected plane ====
  refine ⟨?_, hsurj_glob⟩
  intro a b hab
  symm
  obtain ⟨γq⟩ := PathConnectedSpace.joined a b
  obtain ⟨σ, hσdef⟩ : ∃ σ : Path (p a) (p a), σ = (γq.map hpc).cast rfl hab :=
    ⟨_, rfl⟩
  have hhom : σ.Homotopic (Path.refl (p a)) := SimplyConnectedSpace.paths_homotopic _ _
  obtain ⟨H⟩ := hhom
  have hend := hcov.liftPath_apply_one_eq_of_homotopicRel
    (γ₀ := σ.toContinuousMap) (γ₁ := (Path.refl (p a)).toContinuousMap) ⟨H⟩ a
    (by simp) (by simp)
  -- the given path is the lift of `σ`
  have hlift : (γq.toContinuousMap : C(unitInterval, UpperHalfPlane))
      = hcov.liftPath σ.toContinuousMap a (by simp) := by
    rw [IsCoveringMap.eq_liftPath_iff']
    constructor
    · funext t
      rw [hσdef]
      rfl
    · simp
  have hconst : hcov.liftPath (Path.refl (p a)).toContinuousMap a (by simp)
      = ContinuousMap.const _ a := by
    have h := hcov.liftPath_const (e := a) (x := p a) rfl
    convert h using 2
    rfl
  calc b = γq.toContinuousMap 1 := by simp
    _ = hcov.liftPath σ.toContinuousMap a (by simp) 1 := by rw [hlift]
    _ = hcov.liftPath (Path.refl (p a)).toContinuousMap a (by simp) 1 := hend
    _ = a := by rw [hconst]; rfl

set_option maxHeartbeats 400000 in
-- The development assembles the monodromy homomorphism, the averaged coefficient field and
-- the covering endgame in one declaration; the default heartbeat budget does not cover it.
/-- **Development of the interpolation.** Along a generator tuple converging to the tuple of
a cocompact, trace-gapped limit group, the corrected tile maps of the Dirichlet tiling
develop, for every `κ > 0` and eventually in `n`, into a self-map `h` of the upper half
plane with two-sided inverse `hinv`, continuous with continuous inverse, locally Sobolev,
with almost-everywhere positive Jacobian and Beltrami quotient at most `κ`, and intertwining
the generator tuples exactly on the upper half plane. -/
theorem exists_developed_interpolation
    {ι : Type} [Finite ι] {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (_hΓ : ∀ n, IsFuchsianGroup (Γ n))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    (gens : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) (hmem : ∀ n i, gens n i ∈ Γ n)
    (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hlim : ∀ i, Filter.Tendsto (fun n => gens n i) Filter.atTop (nhds (ρ i)))
    (hgapρ : ∀ h ∈ Subgroup.closure (Set.range ρ), actsNontrivially h →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)|)
    (hccρ : CompactSpace (Quotient (MulAction.orbitRel (Subgroup.closure (Set.range ρ))
      UpperHalfPlane))) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ n in Filter.atTop, ∃ h hinv : ℂ → ℂ,
      (∀ z : ℂ, 0 < z.im → 0 < (h z).im) ∧
      (∀ z : ℂ, 0 < z.im → 0 < (hinv z).im) ∧
      (∀ z : ℂ, 0 < z.im → hinv (h z) = z) ∧
      (∀ z : ℂ, 0 < z.im → h (hinv z) = z) ∧
      ContinuousOn h {z : ℂ | 0 < z.im} ∧
      ContinuousOn hinv {z : ℂ | 0 < z.im} ∧
      MemWklocP h 1 2 {z : ℂ | 0 < z.im} ∧
      (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), 0 < (fderiv ℝ h z).det) ∧
      (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖dzbar h z‖ ≤ κ * ‖dz h z‖) ∧
      ∀ i, ∀ z : ℂ, 0 < z.im → h (moebiusMap (ρ i) z) = moebiusMap (gens n i) (h z) := by
  classical
  intro κ hκ
  -- ==== §0 the limit group and the orbit-density radius ====
  obtain ⟨Γ', hΓ'⟩ : ∃ X, X = Subgroup.closure (Set.range ρ) := ⟨_, rfl⟩
  rw [← hΓ'] at hgapρ hccρ
  have hΓ'fuchs : IsFuchsianGroup Γ' := by
    rw [hΓ']
    rw [hΓ'] at hgapρ
    exact isFuchsianGroup_of_trace_gap hε hgapρ
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : UpperHalfPlane, τ = UpperHalfPlane.I := ⟨_, rfl⟩
  obtain ⟨R, hRpos, hdense⟩ := exists_orbit_density_bound hΓ'fuchs hε hgapρ hccρ τ₀
  have : IsIsometricSMul (↥Γ') UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  -- ==== §1 the covering family of hyperbolic balls, as euclidean balls ====
  obtain ⟨RV, hRVdef⟩ : ∃ x : ℝ, x = 2 * R + 5 := ⟨_, rfl⟩
  have hRV0 : 0 < RV := by rw [hRVdef]; linarith
  obtain ⟨VV, hVVdef⟩ : ∃ V : ↥Γ' → Set ℂ, V = fun γ => Metric.ball
      (((((γ • τ₀ : UpperHalfPlane) : ℂ).re : ℝ) : ℂ)
        + (((γ • τ₀ : UpperHalfPlane).im * Real.cosh RV : ℝ) : ℂ) * Complex.I)
      ((γ • τ₀ : UpperHalfPlane).im * Real.sinh RV) := ⟨_, rfl⟩
  have hVmem : ∀ (γ : ↥Γ') (z : ℂ), z ∈ VV γ ↔
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) < RV := by
    intro γ z
    rw [hVVdef]
    exact zz_ball (γ • τ₀) RV hRV0 z
  have hVsub : ∀ γ : ↥Γ', VV γ ⊆ {z : ℂ | 0 < z.im} := by
    intro γ z hz
    obtain ⟨hzim, _⟩ := (hVmem γ z).mp hz
    exact hzim
  have hVopen : ∀ γ : ↥Γ', IsOpen (VV γ) := by
    intro γ
    rw [hVVdef]
    exact Metric.isOpen_ball
  have hVcov : ∀ z : ℂ, 0 < z.im → ∃ γ : ↥Γ', z ∈ VV γ := by
    intro z hz
    have h1 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀) ≤ R :=
      hdense _
    have hne : (MulAction.orbit (↥Γ') τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    have h2 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀)
        < R + 1 := by linarith
    obtain ⟨y, hymem, hylt⟩ := (Metric.infDist_lt_iff hne).mp h2
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hymem
    refine ⟨γ, (hVmem γ z).mpr ⟨hz, ?_⟩⟩
    rw [hRVdef]
    linarith
  have hcoesmul : ∀ (β : ↥Γ') (τ : UpperHalfPlane),
      ((β • τ : UpperHalfPlane) : ℂ) = moebiusMap (↑β) (τ : ℂ) :=
    fun β τ => coe_smul_eq_moebiusMap (↑β) τ
  have hVtrans : ∀ (β γ : ↥Γ') (z : ℂ), z ∈ VV γ → moebiusMap (↑β) z ∈ VV (β * γ) := by
    intro β γ z hz
    obtain ⟨hzim, hd⟩ := (hVmem γ z).mp hz
    have hzim' : 0 < (moebiusMap (↑β) z).im := moebiusMap_im_pos (↑β) hzim
    refine (hVmem (β * γ) (moebiusMap (↑β) z)).mpr ⟨hzim', ?_⟩
    have hpt : (⟨moebiusMap (↑β) z, hzim'⟩ : UpperHalfPlane)
        = β • (⟨z, hzim⟩ : UpperHalfPlane) := by
      ext
      rw [hcoesmul β ⟨z, hzim⟩]
    rw [hpt, mul_smul]
    rw [show dist (β • (⟨z, hzim⟩ : UpperHalfPlane)) (β • γ • τ₀)
      = dist (⟨z, hzim⟩ : UpperHalfPlane) (γ • τ₀) from dist_smul β _ _]
    exact hd
  have hi₀ : ((τ₀ : ℂ)) ∈ VV 1 := by
    refine (hVmem 1 (τ₀ : ℂ)).mpr ⟨?_, ?_⟩
    · rw [UpperHalfPlane.coe_im]
      exact τ₀.im_pos
    · have hτeq : (⟨(τ₀ : ℂ), by rw [UpperHalfPlane.coe_im]; exact τ₀.im_pos⟩
          : UpperHalfPlane) = τ₀ := by
        ext
        rfl
      rw [hτeq, show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _, dist_self]
      exact hRV0
  have hV1conv : Convex ℝ (VV 1) := by
    rw [hVVdef]
    exact convex_ball _ _
  -- ==== §2 words and the local datum ====
  have hword : ∀ γ : ↥Γ', ∃ l : List (ι × Bool), wordEval ρ l = ↑γ := by
    intro γ
    refine exists_wordEval_eq_of_mem_closure ?_
    rw [← hΓ']
    exact γ.2
  choose wrd hwrd using hword
  obtain ⟨tmap, htmapdef⟩ : ∃ t : ℕ → ↥Γ' → Matrix.SpecialLinearGroup (Fin 2) ℝ,
      t = fun n γ => wordEval (gens n) (wrd γ) := ⟨_, rfl⟩
  have htmem : ∀ (n : ℕ) (γ : ↥Γ'), tmap n γ ∈ Γ n := by
    intro n γ
    rw [htmapdef]
    exact wordEval_mem (hmem n) (wrd γ)
  have htconv : ∀ γ : ↥Γ',
      Filter.Tendsto (fun n => tmap n γ) Filter.atTop (nhds (↑γ)) := by
    intro γ
    rw [htmapdef]
    have h := tendsto_wordEval hlim (wrd γ)
    rwa [hwrd γ] at h
  -- ==== §3 finite interaction sets ====
  have hSfin : ∀ r : ℝ, {γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ r}.Finite :=
    fun r => zz_fin hΓ'fuchs τ₀ τ₀ r
  have hOlap : ∀ γ : ↥Γ', (VV 1 ∩ VV γ).Nonempty → dist τ₀ (γ • τ₀) ≤ 2 * RV := by
    rintro γ ⟨q, hq1, hqγ⟩
    obtain ⟨hqim, hd1⟩ := (hVmem 1 q).mp hq1
    obtain ⟨hqim', hdγ⟩ := (hVmem γ q).mp hqγ
    rw [show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _] at hd1
    have htri := dist_triangle τ₀ (⟨q, hqim⟩ : UpperHalfPlane) (γ • τ₀)
    rw [dist_comm τ₀ (⟨q, hqim⟩ : UpperHalfPlane)] at htri
    linarith
  have hStriple : {p : ↥Γ' × ↥Γ' | (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}.Finite := by
    have hinj : Set.InjOn (fun p : ↥Γ' × ↥Γ' => (p.1, p.1 * p.2)) Set.univ := by
      intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      obtain ⟨h1', h2'⟩ := hpq
      rw [h1'] at h2'
      exact Prod.ext h1' (mul_left_cancel h2')
    have hsub : {p : ↥Γ' × ↥Γ' | (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}
        ⊆ (fun p : ↥Γ' × ↥Γ' => (p.1, p.1 * p.2)) ⁻¹'
          ({γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ 2 * RV} ×ˢ
            {γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ 2 * RV}) := by
      rintro ⟨a, b⟩ hp
      obtain ⟨q, ⟨hq1, hqa⟩, hqab⟩ := hp
      constructor
      · exact hOlap a ⟨q, hq1, hqa⟩
      · exact hOlap (a * b) ⟨q, hq1, hqab⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.preimage (hinj.mono (Set.subset_univ _)) ?_
    exact (hSfin (2 * RV)).prod (hSfin (2 * RV))
  -- ==== §4 anchor chains for the generators ====
  have hgen_mem : ∀ i : ι, ρ i ∈ Γ' := by
    intro i
    rw [hΓ']
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨ri, hridef⟩ : ∃ r : ι → ↥Γ', r = fun i => ⟨ρ i, hgen_mem i⟩ := ⟨_, rfl⟩
  have hri : ∀ i, (↑(ri i) : Matrix.SpecialLinearGroup (Fin 2) ℝ) = ρ i := by
    intro i
    rw [hridef]
  have hanchor : ∀ i : ι, ∃ (N : ℕ) (g : ℕ → ↥Γ'), 0 < N ∧
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N →
        ((τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))) ∈ VV (g k)) := by
    intro i
    have hτim : 0 < (τ₀ : ℂ).im := by
      rw [UpperHalfPlane.coe_im]
      exact τ₀.im_pos
    have hqim : 0 < (moebiusMap (↑(ri i)) (τ₀ : ℂ)).im := moebiusMap_im_pos _ hτim
    refine zz_chain_exists VV hVopen _ ?_ ?_
    · exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    · intro t ht0 ht1
      refine hVcov _ ?_
      have him : ((τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))).im
          = (1 - t) * (τ₀ : ℂ).im + t * (moebiusMap (↑(ri i)) (τ₀ : ℂ)).im := by
        simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.sub_re, zero_mul, add_zero]
        ring
      rw [him]
      rcases le_or_gt t (1 / 2) with hc | hc
      · nlinarith
      · nlinarith
  choose Nanc ganc hNanc hsanc using hanchor
  -- the coe of chain values telescopes to the target
  have hsubty : ∀ (N : ℕ) (g : ℕ → ↥Γ') (γt : ↥Γ'), 0 < N →
      ((↑(g 0) : Matrix.SpecialLinearGroup (Fin 2) ℝ) * ((List.range (N - 1)).map
        fun k => (↑((g k)⁻¹ * g (k + 1)) : Matrix.SpecialLinearGroup (Fin 2) ℝ)).prod
        * (↑((g (N - 1))⁻¹ * γt) : Matrix.SpecialLinearGroup (Fin 2) ℝ)) = ↑γt := by
    intro N g γt hN
    exact zz_telescope (Γ'.subtype) N hN g γt
  -- ==== §5 the eventual conditions ====
  have hE1 : ∀ᶠ n in Filter.atTop, ∀ a b : ↥Γ',
      (VV 1 ∩ VV a ∩ VV (a * b)).Nonempty → tmap n a * tmap n b = tmap n (a * b) := by
    have hcond : ∀ p : ↥Γ' × ↥Γ', (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty →
        ∀ᶠ n in Filter.atTop, tmap n p.1 * tmap n p.2 = tmap n (p.1 * p.2) := by
      rintro ⟨a, b⟩ _
      refine zz_ev_eq hε Γ hgap (a := fun n => tmap n a * tmap n b)
        (b := fun n => tmap n (a * b)) (fun n => mul_mem (htmem n a) (htmem n b))
        (fun n => htmem n (a * b)) (L := ↑(a * b)) ?_ (htconv (a * b))
      have h := (htconv a).mul (htconv b)
      rwa [← Subgroup.coe_mul] at h
    -- reduce to the finite triple set
    have hfin := hStriple
    have hsubty' : ∀ᶠ n in Filter.atTop, ∀ p : ↥({p : ↥Γ' × ↥Γ' |
        (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}), tmap n (p : ↥Γ' × ↥Γ').1
          * tmap n (p : ↥Γ' × ↥Γ').2 = tmap n ((p : ↥Γ' × ↥Γ').1 * (p : ↥Γ' × ↥Γ').2) := by
      have : Finite ↥({p : ↥Γ' × ↥Γ' | (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}) :=
        hfin.to_subtype
      rw [Filter.eventually_all]
      intro p
      exact hcond (p : ↥Γ' × ↥Γ') p.2
    filter_upwards [hsubty'] with n hn a b hab
    exact hn ⟨(a, b), hab⟩
  have hE2 : ∀ᶠ n in Filter.atTop, ∀ i : ι,
      tmap n (ganc i 0) * ((List.range (Nanc i - 1)).map
        fun k => tmap n ((ganc i k)⁻¹ * ganc i (k + 1))).prod
        * tmap n ((ganc i (Nanc i - 1))⁻¹ * ri i) = gens n i := by
    rw [Filter.eventually_all]
    intro i
    refine zz_ev_eq hε Γ hgap
      (a := fun n => tmap n (ganc i 0) * ((List.range (Nanc i - 1)).map
        fun k => tmap n ((ganc i k)⁻¹ * ganc i (k + 1))).prod
        * tmap n ((ganc i (Nanc i - 1))⁻¹ * ri i))
      (b := fun n => gens n i) ?_ (fun n => hmem n i) (L := ρ i) ?_ (hlim i)
    · intro n
      refine mul_mem (mul_mem (htmem n _) ?_) (htmem n _)
      refine Subgroup.list_prod_mem _ ?_
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact htmem n _
    · have h := zz_val_tendsto tmap (fun γ : ↥Γ' => (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        htconv (Nanc i) (ganc i) (ri i)
      rw [hsubty (Nanc i) (ganc i) (ri i) (hNanc i), hri i] at h
      exact h
  -- ==== §6 the equivariant weight family ====
  obtain ⟨UK, UKb, SACT, uψ, Mψ, Rz, imK, hUKopen, hUKsub, hUKbopen, hUKbconv, hUKbUK,
    hUKbmem, hRz1, hRzUK, hMψ0, himK0, himUK, huψ01, huψsm, huψD, hsum1, huψvanUK,
    hSACTdist, huψequi, hFz⟩ := zz_weights hΓ'fuchs τ₀ R hRpos hdense
  -- ==== §8 the smallness threshold and eventual closeness ====
  obtain ⟨CM, hCMdef⟩ : ∃ x : ℝ, x = 1 + (SACT.card : ℝ) * Mψ := ⟨_, rfl⟩
  have hCM1 : 1 ≤ CM := by
    rw [hCMdef]
    have h1 : (0 : ℝ) ≤ (SACT.card : ℝ) * Mψ := mul_nonneg (by positivity) hMψ0
    linarith
  have hCM0 : 0 < CM := by linarith
  obtain ⟨ε₂, hε₂def⟩ : ∃ x : ℝ, x = min (min (1 / (1000 * CM * Rz ^ 2))
      (κ / (128 * CM * Rz ^ 2))) (imK / (100 * CM * Rz ^ 2)) := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by
    rw [hε₂def]
    have hRz0 : (0 : ℝ) < Rz := by linarith
    refine lt_min (lt_min ?_ ?_) ?_ <;> positivity
  have hsm1 : CM * ε₂ * Rz ^ 2 ≤ 1 / 1000 := by
    have h := le_trans (le_of_eq hε₂def)
      (le_trans (min_le_left _ _) (min_le_left _ _))
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1000 * CM * Rz ^ 2)] at h
    nlinarith [h]
  have hsm2 : 128 * (CM * ε₂) * Rz ^ 2 ≤ κ := by
    have h := le_trans (le_of_eq hε₂def)
      (le_trans (min_le_left _ _) (min_le_right _ _))
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 128 * CM * Rz ^ 2)] at h
    nlinarith [h]
  have hsm3 : 100 * (CM * ε₂) * Rz ^ 2 ≤ imK := by
    have h := le_trans (le_of_eq hε₂def) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 * CM * Rz ^ 2)] at h
    nlinarith [h]
  have hE3 : ∀ᶠ n in Filter.atTop, ∀ γ ∈ SACT, ∀ i j : Fin 2,
      |((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          : Matrix (Fin 2) (Fin 2) ℝ) i j
        - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
    have hper : ∀ γ : ↥Γ', ∀ᶠ n in Filter.atTop, ∀ i j : Fin 2,
        |((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            : Matrix (Fin 2) (Fin 2) ℝ) i j
          - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
      intro γ
      have hconv : Filter.Tendsto (fun n => tmap n γ * (↑γ)⁻¹) Filter.atTop
          (nhds ((↑γ) * (↑γ)⁻¹)) := (htconv γ).mul tendsto_const_nhds
      rw [mul_inv_cancel] at hconv
      have hmat := tendsto_subtype_rng.mp hconv
      rw [Matrix.SpecialLinearGroup.coe_one] at hmat
      refine Filter.eventually_all.mpr ?_
      intro i
      refine Filter.eventually_all.mpr ?_
      intro j
      have hent : Filter.Tendsto (fun n =>
          ((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            : Matrix (Fin 2) (Fin 2) ℝ) i j) Filter.atTop
          (nhds ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)) :=
        ((continuous_apply_apply i j).tendsto _).comp hmat
      have habs : Filter.Tendsto (fun n =>
          |((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              : Matrix (Fin 2) (Fin 2) ℝ) i j
            - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|) Filter.atTop (nhds 0) := by
        have h := hent.sub (tendsto_const_nhds
          (x := (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (f := Filter.atTop))
        rw [sub_self] at h
        have habs0 : |(0 : ℝ)| = 0 := abs_zero
        exact habs0 ▸ h.abs
      exact (habs.eventually_lt_const hε₂0).mono (fun n h => h.le)
    have hall : ∀ᶠ n in Filter.atTop, ∀ γ : {x // x ∈ SACT}, ∀ i j : Fin 2,
        |((tmap n (γ : ↥Γ') * (↑(γ : ↥Γ'))⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            : Matrix (Fin 2) (Fin 2) ℝ) i j
          - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ :=
      Filter.eventually_all.mpr (fun γ => hper (γ : ↥Γ'))
    filter_upwards [hall] with n hn γ hγ
    exact hn ⟨γ, hγ⟩
  -- ==== §9 the developed map, for large n ====
  filter_upwards [hE1, hE2, hE3] with n htrip' hanc' hclose'
  obtain ⟨θ, hθmul, hθf, hθmemS, hθval⟩ := zz_mfunc VV ((τ₀ : ℂ)) hVsub hVopen hVcov
    hVtrans hi₀ hV1conv (tmap n) htrip'
  have hθΓn : ∀ γ : ↥Γ', θ γ ∈ Γ n := hθmemS (Γ n) (htmem n)
  have hθgen : ∀ i : ι, θ (ri i) = gens n i := by
    intro i
    have hcont : Continuous (fun t : ℝ =>
        (τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h0 : (τ₀ : ℂ) + ((0 : ℝ) : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))
        = (τ₀ : ℂ) := by
      push_cast
      ring
    have h1 : (τ₀ : ℂ) + ((1 : ℝ) : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))
        = moebiusMap (↑(ri i)) (τ₀ : ℂ) := by
      push_cast
      ring
    have h := hθval (ri i) (fun t : ℝ =>
        (τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ)))
      (Nanc i) (ganc i) hcont h0 h1 (hNanc i) (hsanc i)
    rw [h]
    exact hanc' i
  have hθact : ∀ γ ∈ SACT, θ γ = tmap n γ := by
    intro γ hγ
    have hγ' := hSACTdist γ hγ
    have him : 0 < ((γ • τ₀ : UpperHalfPlane) : ℂ).im := by
      rw [UpperHalfPlane.coe_im]
      exact (γ • τ₀).im_pos
    have hpt : (⟨((γ • τ₀ : UpperHalfPlane) : ℂ), him⟩ : UpperHalfPlane) = γ • τ₀ := by
      ext
      rfl
    refine hθf γ ⟨((γ • τ₀ : UpperHalfPlane) : ℂ), ⟨?_, ?_⟩⟩
    · refine (hVmem 1 _).mpr ⟨him, ?_⟩
      rw [hpt, show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _, dist_comm]
      rw [hRVdef]
      linarith [hγ']
    · refine (hVmem γ _).mpr ⟨him, ?_⟩
      rw [hpt, dist_self]
      exact hRV0
  -- the coefficient matrices and their closeness to the identity
  obtain ⟨cmt, hcmtdef⟩ : ∃ c : ↥Γ' → Matrix (Fin 2) (Fin 2) ℝ,
      c = fun γ => ((θ γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
  have hcmclose : ∀ γ ∈ SACT, ∀ i j : Fin 2,
      |cmt γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
    intro γ hγ i j
    rw [hcmtdef]
    simp only
    rw [hθact γ hγ]
    exact hclose' γ hγ i j
  have hcmdet : ∀ γ : ↥Γ', (cmt γ).det = 1 := by
    intro γ
    rw [hcmtdef]
    exact Matrix.SpecialLinearGroup.det_coe _
  -- the averaged coefficient field
  obtain ⟨Bf, hBdef⟩ : ∃ B : ℂ → Matrix (Fin 2) (Fin 2) ℝ,
      B = fun z => ∑' γ : ↥Γ', uψ γ z • cmt γ := ⟨_, rfl⟩
  have hBrep : ∀ z : ℂ, 0 < z.im → ∀ (F : Finset ↥Γ'),
      (∀ γ : ↥Γ', γ ∉ F → uψ γ z = 0) → Bf z = ∑ γ ∈ F, uψ γ z • cmt γ := by
    intro z hz F hvan
    rw [hBdef]
    refine tsum_eq_sum ?_
    intro γ hγ
    rw [hvan γ hγ, zero_smul]
  have hcmequi : ∀ β γ : ↥Γ', cmt (β * γ)
      = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * cmt γ * ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro β γ
    rw [hcmtdef]
    simp only
    rw [hθmul β γ]
    rw [show ((↑(β * γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
      = (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
        * (↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ from by
        rw [Subgroup.coe_mul, mul_inv_rev]]
    rw [show θ β * θ γ * ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
        * (↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹)
      = θ β * (θ γ * (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹)
        * (↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ from by group]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  -- equivariance of the field
  have hBequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      Bf (moebiusMap (↑β) z)
        = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          * Bf z * ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
            : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro β z hz
    obtain ⟨F, hvanz⟩ := hFz z hz
    have hvanβ : ∀ γ : ↥Γ', γ ∉ F.image (fun δ => β * δ) →
        uψ γ (moebiusMap (↑β) z) = 0 := by
      intro γ hγ
      have hne : β⁻¹ * γ ∉ F := by
        intro hmem'
        exact hγ (Finset.mem_image.mpr ⟨β⁻¹ * γ, hmem', by group⟩)
      have h := huψequi β (β⁻¹ * γ) z hz
      rw [show β * (β⁻¹ * γ) = γ from by group] at h
      rw [h]
      exact hvanz _ hne
    rw [hBrep _ (moebiusMap_im_pos _ hz) _ hvanβ, hBrep z hz F hvanz]
    rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel h)]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro δ hδ
    rw [huψequi β δ z hz, hcmequi β δ]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  -- ==== §10 the developed map and the pointwise package on the inner region ====
  obtain ⟨hm, hhdef⟩ : ∃ h : ℂ → ℂ, h = fun z => matMoebius (Bf z) z := ⟨_, rfl⟩
  have hεRzsmall : ε₂ * Rz + ε₂ ≤ 1 / 2 := by
    have ha : 0 ≤ ε₂ * Rz * (Rz - 1) :=
      mul_nonneg (mul_nonneg hε₂0.le (by linarith [hRz1] : (0 : ℝ) ≤ Rz))
        (by linarith [hRz1] : (0 : ℝ) ≤ Rz - 1)
    have hb : 0 ≤ (CM - 1) * (ε₂ * Rz ^ 2) :=
      mul_nonneg (by linarith [hCM1] : (0 : ℝ) ≤ CM - 1)
        (mul_nonneg hε₂0.le (sq_nonneg Rz))
    have hc : 0 ≤ ε₂ * (Rz ^ 2 - 1) :=
      mul_nonneg hε₂0.le (by nlinarith [hRz1] : (0 : ℝ) ≤ Rz ^ 2 - 1)
    nlinarith [hsm1, ha, hb, hc]
  obtain ⟨hBentry, hBD, hBDb, hdenUK⟩ := zz_field UK hUKopen UKb hUKbUK SACT uψ cmt
    Rz ε₂ Mψ hε₂0 hRzUK (fun γ z hz => huψ01 γ z hz) huψsm
    huψD hsum1 hcmclose Bf
    (fun z hz => hBrep z (hUKsub hz) SACT (fun γ hγ => huψvanUK z hz γ hγ)) hεRzsmall
  obtain ⟨εP, hεPdef⟩ : ∃ x : ℝ, x = CM * ε₂ := ⟨_, rfl⟩
  have hεP0 : 0 < εP := by
    rw [hεPdef]
    positivity
  have hεPsmall : εP * Rz ^ 2 ≤ 1 / 1000 := by
    rw [hεPdef]
    nlinarith [hsm1]
  have hε₂εP : ε₂ ≤ εP := by
    rw [hεPdef]
    nlinarith [hε₂0, hCM1]
  have hBDb' : ∀ z ∈ UKb, ∀ i j : Fin 2,
      ‖∑ γ ∈ SACT, (cmt γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
        • fderiv ℝ (uψ γ) z‖ ≤ εP := by
    intro z hz i j
    refine le_trans (hBDb z hz i j) ?_
    rw [hεPdef, hCMdef]
    nlinarith [hε₂0, hMψ0, Nat.cast_nonneg (α := ℝ) SACT.card]
  have hBentry' : ∀ z ∈ UK, ∀ i j : Fin 2,
      |Bf z i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ εP := by
    intro z hz i j
    exact le_trans (hBentry z hz i j) hε₂εP
  have hpack : ∀ z ∈ UKb,
      DifferentiableAt ℝ hm z ∧ ‖hm z - z‖ ≤ 8 * Rz ^ 2 * εP ∧
      ‖dzbar hm z‖ ≤ 64 * Rz ^ 2 * εP ∧ (1 : ℝ) / 2 ≤ ‖dz hm z‖ ∧
      ‖fderiv ℝ hm z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 64 * Rz ^ 2 * εP ∧
      0 < (fderiv ℝ hm z).det := by
    intro z hz
    have hzUK := hUKbUK hz
    have hb00 : |Bf z 0 0 - 1| ≤ εP := by
      have h := hBentry' z hzUK 0 0
      rwa [Matrix.one_apply_eq] at h
    have hb01 : |Bf z 0 1| ≤ εP := by
      have h := hBentry' z hzUK 0 1
      rwa [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero] at h
    have hb10 : |Bf z 1 0| ≤ εP := by
      have h := hBentry' z hzUK 1 0
      rwa [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h
    have hb11 : |Bf z 1 1 - 1| ≤ εP := by
      have h := hBentry' z hzUK 1 1
      rwa [Matrix.one_apply_eq] at h
    obtain ⟨hdA, hvA, hoA⟩ := zz_moeb_packA
      (fun w => Bf w 0 0) (fun w => Bf w 0 1) (fun w => Bf w 1 0) (fun w => Bf w 1 1)
      _ _ _ _ z Rz εP hRz1 (hRzUK z hzUK)
      (hBD z hzUK 0 0) (hBD z hzUK 0 1) (hBD z hzUK 1 0) (hBD z hzUK 1 1)
      hεP0.le hb00 hb01 hb10 hb11
      (hBDb' z hz 0 0) (hBDb' z hz 0 1) (hBDb' z hz 1 0) (hBDb' z hz 1 1) hεPsmall
    obtain ⟨hbB, hzB, hdetB⟩ := zz_moeb_packB
      (fun w => Bf w 0 0) (fun w => Bf w 0 1) (fun w => Bf w 1 0) (fun w => Bf w 1 1)
      _ _ _ _ z Rz εP hRz1 (hRzUK z hzUK)
      (hBD z hzUK 0 0) (hBD z hzUK 0 1) (hBD z hzUK 1 0) (hBD z hzUK 1 1)
      hεP0.le hb00 hb01 hb10 hb11
      (hBDb' z hz 0 0) (hBDb' z hz 0 1) (hBDb' z hz 1 0) (hBDb' z hz 1 1) hεPsmall
    rw [hhdef]
    exact ⟨hdA, hvA, hbB, hzB, hoA, hdetB⟩
  -- ==== §11 conjugation and regularity via the globalization package ====
  have htransport0 : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ) (hw : 0 < w.im), w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w ∧
      ∀ (x : ℂ) (hx : 0 < x.im),
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 → x ∈ UKb := by
    intro z hz
    have h1 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀) ≤ R :=
      hdense _
    have hne : (MulAction.orbit (↥Γ') τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    obtain ⟨y, hymem, hylt⟩ := (Metric.infDist_lt_iff hne).mp
      (lt_of_le_of_lt h1 (by linarith : R < R + 1))
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hymem
    obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z := ⟨_, rfl⟩
    have hwim : 0 < w.im := by
      rw [hwdef]
      exact moebiusMap_im_pos _ hz
    have hwdist : dist (⟨w, hwim⟩ : UpperHalfPlane) τ₀ < R + 1 := by
      have hpt : (⟨w, hwim⟩ : UpperHalfPlane) = γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane) := by
        ext
        change w = ((γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
        rw [hcoesmul γ⁻¹ (⟨z, hz⟩ : UpperHalfPlane), hwdef]
      rw [hpt]
      have hd : dist (γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane)) τ₀
          = dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by
        calc dist (γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane)) τ₀
            = dist (γ • γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane)) (γ • τ₀) :=
              (dist_smul γ _ _).symm
          _ = dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by rw [smul_inv_smul]
      rw [hd]
      exact hylt
    refine ⟨γ, w, hwim, hUKbmem w hwim (by linarith), hwdef, ?_, ?_⟩
    · rw [hwdef]
      have hden : moebiusDenom (↑(γ⁻¹ : ↥Γ')) z ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hz)
      rw [moebiusMap_mul (↑γ) (↑(γ⁻¹ : ↥Γ')) z hden]
      have hone : (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (↑(γ⁻¹ : ↥Γ')) = 1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
      rw [hone, moebiusMap_one]
    · intro x hx hxd
      refine hUKbmem x hx ?_
      have htri := dist_triangle (⟨x, hx⟩ : UpperHalfPlane)
        (⟨w, hwim⟩ : UpperHalfPlane) τ₀
      linarith
  have htransport : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ), 0 < w.im ∧ w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w := by
    intro z hz
    obtain ⟨γ, w, hw, h1, h2, h3, _⟩ := htransport0 z hz
    exact ⟨γ, w, hw, h1, h2, h3⟩
  have hBijsm : ∀ i j : Fin 2, ContDiffOn ℝ 1 (fun w => Bf w i j) UK := by
    intro i j z hz
    have hsumsm : ContDiffWithinAt ℝ 1 (fun w => ∑ γ ∈ SACT, uψ γ w * cmt γ i j) UK z := by
      refine ContDiffWithinAt.sum ?_
      intro γ _
      exact ((huψsm γ) z hz).mul contDiffWithinAt_const
    refine hsumsm.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hBrep w (hUKsub hw) SACT (fun γ hγ => huψvanUK w hw γ hγ), Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro γ _
      rw [Matrix.smul_apply, smul_eq_mul]
    · rw [hBrep z (hUKsub hz) SACT (fun γ hγ => huψvanUK z hz γ hγ), Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro γ _
      rw [Matrix.smul_apply, smul_eq_mul]
  have hmsmUK : ContDiffOn ℝ 1 hm UK := by
    have hnum : ContDiffOn ℝ 1 (fun w => ((Bf w 0 0 : ℝ) : ℂ) * w
        + ((Bf w 0 1 : ℝ) : ℂ)) UK := by
      refine ContDiffOn.add ?_ ?_
      · refine ContDiffOn.mul ?_ contDiffOn_id
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 0 0)
      · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 0 1)
    have hden : ContDiffOn ℝ 1 (fun w => ((Bf w 1 0 : ℝ) : ℂ) * w
        + ((Bf w 1 1 : ℝ) : ℂ)) UK := by
      refine ContDiffOn.add ?_ ?_
      · refine ContDiffOn.mul ?_ contDiffOn_id
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 1 0)
      · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 1 1)
    have hq : ContDiffOn ℝ 1 (fun w => (((Bf w 0 0 : ℝ) : ℂ) * w + ((Bf w 0 1 : ℝ) : ℂ))
        * ((((Bf w 1 0 : ℝ) : ℂ) * w + ((Bf w 1 1 : ℝ) : ℂ))⁻¹)) UK :=
      hnum.mul (hden.inv hdenUK)
    refine hq.congr ?_
    intro w hw
    rw [hhdef]
    simp only
    rw [matMoebius, div_eq_mul_inv]
  have hpk0 : ∀ w ∈ UKb, DifferentiableAt ℝ (fun z => matMoebius (Bf z) z) w ∧
      0 < ((fun z => matMoebius (Bf z) z) w).im ∧
      ‖dzbar (fun z => matMoebius (Bf z) z) w‖ ≤ 64 * Rz ^ 2 * εP ∧
      (1 : ℝ) / 2 ≤ ‖dz (fun z => matMoebius (Bf z) z) w‖ ∧
      0 < (fderiv ℝ (fun z => matMoebius (Bf z) z) w).det := by
    intro w hw
    obtain ⟨hd, hval, hbar, hdzl, hop, hdet⟩ := hpack w hw
    have him : 0 < (hm w).im := by
      have h1 : |(hm w - w).im| ≤ ‖hm w - w‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 := himUK w (hUKbUK hw)
      have h3 : 8 * Rz ^ 2 * εP ≤ 8 / 100 * imK := by
        rw [hεPdef]
        nlinarith [hsm3]
      nlinarith [(abs_le.mp h1).1, hval, h2, himK0, h3]
    exact ⟨by rw [← hhdef]; exact hd, by rw [← hhdef]; exact him,
      by rw [← hhdef]; exact hbar, by rw [← hhdef]; exact hdzl,
      by rw [← hhdef]; exact hdet⟩
  have hCbκ : 2 * (64 * Rz ^ 2 * εP) ≤ κ := by
    rw [hεPdef]
    nlinarith [hsm2]
  have hsm0 : ContDiffOn ℝ 1 (fun z => matMoebius (Bf z) z) UK := by
    rw [← hhdef]
    exact hmsmUK
  obtain ⟨hdenglobal0, himglobal0, hequi0, hmC10, hjb0⟩ := zz_conjreg θ Bf UK UKb hUKopen
    hUKbUK κ (64 * Rz ^ 2 * εP) hκ hCbκ htransport hBequi hdenUK hsm0 hpk0
  have himglobal : ∀ z : ℂ, 0 < z.im → 0 < (hm z).im := by
    intro z hz
    have h := himglobal0 z hz
    rwa [← hhdef] at h
  have hequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      hm (moebiusMap (↑β) z) = moebiusMap (θ β) (hm z) := by
    intro β z hz
    have h := hequi0 β z hz
    rwa [← hhdef] at h
  have hmC1 : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 1 hm z := by
    intro z hz
    have h := hmC10 z hz
    rwa [← hhdef] at h
  have hjb : ∀ z : ℂ, 0 < z.im →
      0 < (fderiv ℝ hm z).det ∧ ‖dzbar hm z‖ ≤ κ * ‖dz hm z‖ := by
    intro z hz
    have h := hjb0 z hz
    rwa [← hhdef] at h
  have hopenH : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcont : ContinuousOn hm {x : ℂ | 0 < x.im} :=
    fun z hz => ((hmC1 z hz).continuousAt).continuousWithinAt
  have hSob : MemWklocP hm 1 2 {x : ℂ | 0 < x.im} :=
    zz_sobolev hm _ hopenH (fun z hz => (hmC1 z hz).contDiffWithinAt)
  have hmeasH : MeasurableSet {x : ℂ | 0 < x.im} := hopenH.measurableSet
  have hjac_ae : ∀ᵐ z ∂(volume.restrict {x : ℂ | 0 < x.im}), 0 < (fderiv ℝ hm z).det :=
    (MeasureTheory.ae_restrict_iff' hmeasH).mpr
      (Filter.Eventually.of_forall (fun z hz => (hjb z hz).1))
  have hbelt_ae : ∀ᵐ z ∂(volume.restrict {x : ℂ | 0 < x.im}),
      ‖dzbar hm z‖ ≤ κ * ‖dz hm z‖ :=
    (MeasureTheory.ae_restrict_iff' hmeasH).mpr
      (Filter.Eventually.of_forall (fun z hz => (hjb z hz).2))
  have hgenequi : ∀ i : ι, ∀ z : ℂ, 0 < z.im →
      hm (moebiusMap (ρ i) z) = moebiusMap (gens n i) (hm z) := by
    intro i z hz
    have h := hequi (ri i) z hz
    rw [hri i, hθgen i] at h
    exact h
  -- ==== §13 the homeomorphism package and the assembly ====
  have hhomeo : ∃ hinv : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → 0 < (hinv z).im) ∧
      (∀ z : ℂ, 0 < z.im → hinv (hm z) = z) ∧
      (∀ z : ℂ, 0 < z.im → hm (hinv z) = z) ∧
      ContinuousOn hinv {x : ℂ | 0 < x.im} := by
    -- uniform local injectivity/surjectivity at the ℂ-level
    obtain ⟨hinjU, hsurjU⟩ := zz_uniform θ hm UKb (8 * Rz ^ 2 * εP) htransport0 hequi
      himglobal (fun w hw => (hpack w hw).1)
      (fun w hw => le_trans (hpack w hw).2.2.2.2.1 (by rw [hεPdef]; nlinarith [hsm1]))
      (fun w hw => (hpack w hw).2.1)
      (fun w hw => by
        have h2 := himUK w (hUKbUK hw)
        rw [hεPdef]
        nlinarith [hsm3, himK0])
      (fun w hw => hUKsub (hUKbUK hw))
    -- the upper-half-plane self-map
    obtain ⟨pH, hpHdef⟩ : ∃ pH : UpperHalfPlane → UpperHalfPlane,
        pH = fun τ : UpperHalfPlane =>
          (⟨hm ↑τ, himglobal ↑τ τ.coe_im_pos⟩ : UpperHalfPlane) := ⟨_, rfl⟩
    have hpHcoe : ∀ τ : UpperHalfPlane, (pH τ : ℂ) = hm ↑τ := by
      intro τ
      rw [hpHdef]
    have hpHc : Continuous pH := by
      rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
      have h1 : Continuous fun τ : UpperHalfPlane => hm ↑τ :=
        hcont.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.coe_im_pos)
      refine h1.congr ?_
      intro τ
      exact (hpHcoe τ).symm
    -- ℂ-level openness of hm on the upper half plane
    have hmapnh : ∀ z : ℂ, 0 < z.im → Filter.map hm (nhds z) = nhds (hm z) := by
      intro z hz
      have hsd : HasStrictFDerivAt hm (fderiv ℝ hm z) z :=
        (hmC1 z hz).hasStrictFDerivAt one_ne_zero
      have hdet : (fderiv ℝ hm z).det ≠ 0 := ne_of_gt (hjb z hz).1
      have hcoe : ((LinearMap.equivOfDetNeZero (fderiv ℝ hm z).toLinearMap
          hdet).toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) = fderiv ℝ hm z := by
        ext x
        rfl
      have hsd' : HasStrictFDerivAt hm
          (((LinearMap.equivOfDetNeZero (fderiv ℝ hm z).toLinearMap
            hdet).toContinuousLinearEquiv : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z := by
        rw [hcoe]
        exact hsd
      exact hsd'.map_nhds_eq_of_equiv
    have himgopen : ∀ V : Set ℂ, IsOpen V → V ⊆ {x : ℂ | 0 < x.im} →
        IsOpen (hm '' V) := by
      intro V hV hVsub
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨z, hzV, rfl⟩
      rw [← hmapnh z (hVsub hzV)]
      exact Filter.image_mem_map (hV.mem_nhds hzV)
    have hpHopen : IsOpenMap pH := by
      intro U hU
      rw [UpperHalfPlane.isOpenEmbedding_coe.isOpen_iff_image_isOpen]
      have himg : ((↑) : UpperHalfPlane → ℂ) '' (pH '' U)
          = hm '' (((↑) : UpperHalfPlane → ℂ) '' U) := by
        ext y
        constructor
        · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
          exact ⟨↑τ, ⟨τ, hτ, rfl⟩, (hpHcoe τ).symm⟩
        · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
          exact ⟨pH τ, ⟨τ, hτ, rfl⟩, hpHcoe τ⟩
      rw [himg]
      refine himgopen _ (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU) ?_
      rintro y ⟨τ, _, rfl⟩
      exact τ.coe_im_pos
    -- ℍ-level uniform local injectivity and surjectivity
    have hinjH : ∀ z a b : UpperHalfPlane, dist a z < 1 / 4 → dist b z < 1 / 4 →
        pH a = pH b → a = b := by
      intro z a b hda hdb hab
      have hab' : hm ↑a = hm ↑b := by
        rw [← hpHcoe a, hab, hpHcoe b]
      exact UpperHalfPlane.ext
        (hinjU ↑z ↑a ↑b z.coe_im_pos a.coe_im_pos b.coe_im_pos hda hdb hab')
    have hsurjH : ∀ z ξ : UpperHalfPlane, dist ξ (pH z) < 1 / 2048 →
        ∃ x : UpperHalfPlane, dist x z < 1 / 32 ∧ pH x = ξ := by
      intro z ξ hd
      rw [hpHdef] at hd
      obtain ⟨x, hx, hxd, hxp⟩ := hsurjU ↑z ↑ξ z.coe_im_pos ξ.coe_im_pos
        (himglobal ↑z z.coe_im_pos) hd
      refine ⟨⟨x, hx⟩, hxd, ?_⟩
      refine UpperHalfPlane.ext ?_
      rw [hpHcoe]
      exact hxp
    -- the global bijection and its homeomorphism upgrade
    have hbij := zz_homeo pH hpHc hpHopen hinjH hsurjH
    obtain ⟨eH, heHdef⟩ : ∃ e : UpperHalfPlane ≃ UpperHalfPlane,
        e = Equiv.ofBijective pH hbij := ⟨_, rfl⟩
    have heHap : ∀ τ : UpperHalfPlane, eH τ = pH τ := by
      intro τ
      rw [heHdef]
      rfl
    have heHc : Continuous (⇑eH) := by
      rw [heHdef]
      exact hpHc
    have heHo : IsOpenMap (⇑eH) := by
      rw [heHdef]
      exact hpHopen
    obtain ⟨HH, hHHdef⟩ : ∃ H : UpperHalfPlane ≃ₜ UpperHalfPlane,
        H = Equiv.toHomeomorphOfContinuousOpen eH heHc heHo := ⟨_, rfl⟩
    have hsymc : Continuous (⇑eH.symm) := by
      have h := HH.symm.continuous
      rw [hHHdef] at h
      exact h
    -- the inverse map and its four clauses
    obtain ⟨hminv0, hminv0def⟩ : ∃ f : ℂ → ℂ,
        f = fun z => if hz : 0 < z.im then (↑(eH.symm ⟨z, hz⟩) : ℂ) else (0 : ℂ) := ⟨_, rfl⟩
    have hminv0eq : ∀ (z : ℂ) (hz : 0 < z.im), hminv0 z = ↑(eH.symm ⟨z, hz⟩) := by
      intro z hz
      rw [hminv0def]
      exact dif_pos hz
    refine ⟨hminv0, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [hminv0eq z hz]
      exact (eH.symm ⟨z, hz⟩).coe_im_pos
    · intro z hz
      rw [hminv0eq (hm z) (himglobal z hz)]
      have hkey : (⟨hm z, himglobal z hz⟩ : UpperHalfPlane) = eH ⟨z, hz⟩ := by
        rw [heHap]
        refine UpperHalfPlane.ext ?_
        change hm z = ↑(pH (⟨z, hz⟩ : UpperHalfPlane))
        rw [hpHcoe]
      rw [hkey, Equiv.symm_apply_apply]
    · intro z hz
      rw [hminv0eq z hz, ← hpHcoe (eH.symm ⟨z, hz⟩), ← heHap, Equiv.apply_symm_apply]
    · rw [continuousOn_iff_continuous_domRestrict]
      have hfun : ({x : ℂ | 0 < x.im}.domRestrict hminv0)
          = fun τ : ↥{x : ℂ | 0 < x.im} => (↑(eH.symm ⟨↑τ, τ.2⟩) : ℂ) := by
        funext τ
        exact hminv0eq ↑τ τ.2
      rw [hfun]
      have hin : Continuous fun τ : ↥{x : ℂ | 0 < x.im} =>
          (⟨↑τ, τ.2⟩ : UpperHalfPlane) := by
        rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
        exact continuous_subtype_val
      exact UpperHalfPlane.continuous_coe.comp (hsymc.comp hin)
  obtain ⟨hminv, hinvim, hleft, hright, hinvcont⟩ := hhomeo
  exact ⟨hm, hminv, himglobal, hinvim, hleft, hright, hcont, hinvcont, hSob,
    hjac_ae, hbelt_ae, hgenequi⟩

end RiemannDynamics
