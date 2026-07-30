/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Winding.Extraction

/-!
# The four-piece rounded loop

The corner pieces and ramp arcs of the rounded loop, their speeds and seam matchings,
and the tangent winding count of the assembled four-piece loop.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

section WindingBricks

open unitInterval

/-- The bigon loop follows its first side up to the corner time. -/
theorem bigonLoop_le {γ τ : ℝ → ℂ} {T : ℝ} {x : ℝ} (hx : x ≤ T) :
    bigonLoop γ τ T x = γ x := if_pos hx

/-- **Continuity of the concatenated loop** on the joint interval. -/
theorem bigonLoop_continuousOn {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {T s μ : ℝ}
    (hT : 0 < T) (hs : 0 ≤ s) (hμ : 0 < μ)
    (hγ : IsTrajOn q γ (Set.Icc (-μ) (T + μ)))
    (hτ : IsTrajOn (fun z => -q z) τ (Set.Icc (-μ) (s + μ)))
    (hcorner : τ 0 = γ T) :
    ContinuousOn (bigonLoop γ τ T) (Set.Icc 0 (T + s)) := by
  have hγc : ContinuousOn γ (Set.Icc (-μ) (T + μ)) := hγ.cont
  have hτc : ContinuousOn τ (Set.Icc (-μ) (s + μ)) := hτ.cont
  intro x hx
  rcases lt_trichotomy x T with hlt | heq | hgt
  · rw [← continuousWithinAt_inter (IsOpen.mem_nhds (isOpen_Iio (a := T)) hlt)]
    have hbase : ContinuousWithinAt γ (Set.Icc 0 (T + s) ∩ Set.Iio T) x := by
      refine (hγc x ⟨by linarith [hx.1], by linarith⟩).mono ?_
      rintro y ⟨hy1, hy2⟩
      have := Set.mem_Iio.mp hy2
      exact ⟨by linarith [hy1.1], by linarith⟩
    refine hbase.congr ?_ (bigonLoop_le hlt.le)
    rintro y ⟨hy1, hy2⟩
    exact bigonLoop_le (le_of_lt (Set.mem_Iio.mp hy2))
  · subst heq
    have hIic : ContinuousWithinAt (bigonLoop γ τ x)
        (Set.Icc 0 (x + s) ∩ Set.Iic x) x := by
      have hbase : ContinuousWithinAt γ (Set.Icc 0 (x + s) ∩ Set.Iic x) x := by
        refine (hγc x ⟨by linarith [hx.1], by linarith⟩).mono ?_
        rintro y ⟨hy1, hy2⟩
        have := Set.mem_Iic.mp hy2
        exact ⟨by linarith [hy1.1], by linarith⟩
      refine hbase.congr ?_ (bigonLoop_le le_rfl)
      rintro y ⟨hy1, hy2⟩
      exact bigonLoop_le (Set.mem_Iic.mp hy2)
    have hIci : ContinuousWithinAt (bigonLoop γ τ x)
        (Set.Icc 0 (x + s) ∩ Set.Ici x) x := by
      have hshift : ContinuousWithinAt (fun y => τ (y - x))
          (Set.Icc 0 (x + s) ∩ Set.Ici x) x := by
        refine ContinuousWithinAt.comp
          (hτc (x - x) (by rw [sub_self]; exact ⟨by linarith, by linarith⟩))
          ((continuous_id.sub continuous_const).continuousWithinAt) ?_
        rintro y ⟨hy1, hy2⟩
        have := Set.mem_Ici.mp hy2
        change y - x ∈ Set.Icc (-μ) (s + μ)
        exact ⟨by linarith, by linarith [hy1.2]⟩
      refine hshift.congr ?_ ?_
      · rintro y ⟨hy1, hy2⟩
        exact bigonLoop_ge hcorner (Set.mem_Ici.mp hy2)
      · exact bigonLoop_ge hcorner le_rfl
    have hunion := hIic.union hIci
    rwa [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]
      at hunion
  · rw [← continuousWithinAt_inter (IsOpen.mem_nhds (isOpen_Ioi (a := T)) hgt)]
    have hshift : ContinuousWithinAt (fun y => τ (y - T))
        (Set.Icc 0 (T + s) ∩ Set.Ioi T) x := by
      refine ContinuousWithinAt.comp
        (hτc (x - T) ⟨by linarith, by linarith [hx.2]⟩)
        ((continuous_id.sub continuous_const).continuousWithinAt) ?_
      rintro y ⟨hy1, hy2⟩
      have := Set.mem_Ioi.mp hy2
      change y - T ∈ Set.Icc (-μ) (s + μ)
      exact ⟨by linarith, by linarith [hy1.2]⟩
    refine hshift.congr ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      exact bigonLoop_ge hcorner (le_of_lt (Set.mem_Ioi.mp hy2))
    · exact bigonLoop_ge hcorner hgt.le

/-- **Local injectivity of the concatenated loop**: piece windows from the trajectory
charts, the junction window from corner transversality. -/
theorem bigonLoop_locally_injective {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {T s μ : ℝ}
    (hT : 0 < T) (hs : 0 ≤ s) (hμ : 0 < μ)
    (hγ : IsTrajOn q γ (Set.Icc (-μ) (T + μ)))
    (hτ : IsTrajOn (fun z => -q z) τ (Set.Icc (-μ) (s + μ)))
    (hcorner : τ 0 = γ T) :
    ∀ x ∈ Set.Icc (0:ℝ) (T + s), ∃ δ > 0,
      Set.InjOn (bigonLoop γ τ T)
        (Set.Icc (x - δ) (x + δ) ∩ Set.Icc 0 (T + s)) := by
  have hTγ : T ∈ Set.Icc (-μ) (T + μ) := ⟨by linarith, by linarith⟩
  have h0τ : (0:ℝ) ∈ Set.Icc (-μ) (s + μ) := ⟨by linarith, by linarith⟩
  intro x hx
  rcases lt_trichotomy x T with hlt | heq | hgt
  · -- interior of the horizontal arc
    obtain ⟨δσ, hδσ, hinjσ⟩ := traj_locally_injective hγ x
      ⟨by linarith [hx.1], by linarith⟩
    refine ⟨min δσ (T - x), lt_min hδσ (by linarith), ?_⟩
    intro z hz z' hz' heq2
    have hzT : z ≤ T := by
      have := hz.1.2
      have h1 : min δσ (T - x) ≤ T - x := min_le_right _ _
      linarith
    have hz'T : z' ≤ T := by
      have := hz'.1.2
      have h1 : min δσ (T - x) ≤ T - x := min_le_right _ _
      linarith
    rw [bigonLoop_le hzT, bigonLoop_le hz'T] at heq2
    refine hinjσ ⟨⟨?_, ?_⟩, ⟨by linarith [hz.2.1], by linarith⟩⟩
      ⟨⟨?_, ?_⟩, ⟨by linarith [hz'.2.1], by linarith⟩⟩ heq2
    · have h1 : min δσ (T - x) ≤ δσ := min_le_left _ _
      linarith [hz.1.1]
    · have h1 : min δσ (T - x) ≤ δσ := min_le_left _ _
      linarith [hz.1.2]
    · have h1 : min δσ (T - x) ≤ δσ := min_le_left _ _
      linarith [hz'.1.1]
    · have h1 : min δσ (T - x) ≤ δσ := min_le_left _ _
      linarith [hz'.1.2]
  · -- the junction
    subst heq
    obtain ⟨δσ, hδσ, hinjσ⟩ := traj_locally_injective hγ x hTγ
    obtain ⟨δτ, hδτ, hinjτ⟩ := traj_locally_injective hτ 0 h0τ
    obtain ⟨δc, hδc, hcornerdisj⟩ := corner_locally_disjoint hγ hTγ hτ
      (show (0:ℝ) < μ/2 by linarith)
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) hcorner
    set δ : ℝ := min (min δσ δτ) δc with hδdef
    have hδpos : 0 < δ := lt_min (lt_min hδσ hδτ) hδc
    have hδ1 : δ ≤ δσ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ2 : δ ≤ δτ := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ3 : δ ≤ δc := min_le_right _ _
    refine ⟨δ, hδpos, ?_⟩
    intro z hz z' hz' heq2
    rcases le_total z x with hzx | hzx <;> rcases le_total z' x with hz'x | hz'x
    · -- both on the horizontal side
      rw [bigonLoop_le hzx, bigonLoop_le hz'x] at heq2
      exact hinjσ ⟨⟨by linarith [hz.1.1], by linarith [hzx]⟩,
          ⟨by linarith [hz.2.1], by linarith⟩⟩
        ⟨⟨by linarith [hz'.1.1], by linarith [hz'x]⟩,
          ⟨by linarith [hz'.2.1], by linarith⟩⟩ heq2
    · -- z horizontal, z' transverse: only the corner, contradiction with order
      rw [bigonLoop_le hzx, bigonLoop_ge hcorner hz'x] at heq2
      have hkill := hcornerdisj z ⟨⟨by linarith [hz.1.1], by linarith⟩,
          ⟨by linarith [hz.2.1], by linarith⟩⟩ (z' - x)
        ⟨by linarith [hz'.1.1], by linarith [hz'.1.2]⟩ heq2
      have hz'eq : z' = x := by linarith [hkill.2]
      rw [hkill.1, hz'eq]
    · -- symmetric mixed case
      rw [bigonLoop_le hz'x, bigonLoop_ge hcorner hzx] at heq2
      have hkill := hcornerdisj z' ⟨⟨by linarith [hz'.1.1], by linarith⟩,
          ⟨by linarith [hz'.2.1], by linarith⟩⟩ (z - x)
        ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩ heq2.symm
      have hzeq : z = x := by linarith [hkill.2]
      rw [hkill.1, hzeq]
    · -- both on the transverse side
      rw [bigonLoop_ge hcorner hzx, bigonLoop_ge hcorner hz'x] at heq2
      have h1 := hinjτ ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
          ⟨by linarith [hzx], by linarith [hz.2.2]⟩⟩
        ⟨⟨by linarith [hz'.1.1], by linarith [hz'.1.2]⟩,
          ⟨by linarith [hz'x], by linarith [hz'.2.2]⟩⟩ heq2
      linarith
  · -- interior of the transverse arc
    obtain ⟨δτ, hδτ, hinjτ⟩ := traj_locally_injective hτ (x - T)
      ⟨by linarith, by linarith [hx.2]⟩
    refine ⟨min δτ (x - T), lt_min hδτ (by linarith), ?_⟩
    intro z hz z' hz' heq2
    have hzT : T ≤ z := by
      have := hz.1.1
      have h1 : min δτ (x - T) ≤ x - T := min_le_right _ _
      linarith
    have hz'T : T ≤ z' := by
      have := hz'.1.1
      have h1 : min δτ (x - T) ≤ x - T := min_le_right _ _
      linarith
    rw [bigonLoop_ge hcorner hzT, bigonLoop_ge hcorner hz'T] at heq2
    have h1 := hinjτ (x₁ := z - T) (x₂ := z' - T)
      ⟨⟨?_, ?_⟩, ⟨by linarith, by linarith [hz.2.2]⟩⟩
      ⟨⟨?_, ?_⟩, ⟨by linarith, by linarith [hz'.2.2]⟩⟩ heq2
    · linarith
    · have h2 : min δτ (x - T) ≤ δτ := min_le_left _ _
      linarith [hz.1.1]
    · have h2 : min δτ (x - T) ≤ δτ := min_le_left _ _
      linarith [hz.1.2]
    · have h2 : min δτ (x - T) ≤ δτ := min_le_left _ _
      linarith [hz'.1.1]
    · have h2 : min δτ (x - T) ≤ δτ := min_le_left _ _
      linarith [hz'.1.2]

/-- **The extraction trichotomy**: from a horizontal arc and a transverse arc sharing
both endpoints, extract a simple horizontal return, a simple transverse return, or a
simple sub-bigon whose arcs meet only at the two corners. -/
theorem bigon_extract {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {T s μ : ℝ}
    (hT : 0 < T) (hs : 0 ≤ s) (hμ : 0 < μ)
    (hγ : IsTrajOn q γ (Set.Icc (-μ) (T + μ)))
    (hτ : IsTrajOn (fun z => -q z) τ (Set.Icc (-μ) (s + μ)))
    (hc1 : τ 0 = γ T) (hc2 : τ s = γ 0) :
    (∃ a b, 0 ≤ a ∧ a < b ∧ b ≤ T ∧ γ a = γ b ∧ Set.InjOn γ (Set.Ico a b))
    ∨ (∃ a b, 0 ≤ a ∧ a < b ∧ b ≤ s ∧ τ a = τ b ∧ Set.InjOn τ (Set.Ico a b))
    ∨ (∃ a b, 0 ≤ a ∧ a < T ∧ 0 < b ∧ b ≤ s ∧ τ b = γ a ∧
        Set.InjOn γ (Set.Icc a T) ∧ Set.InjOn τ (Set.Icc 0 b) ∧
        ∀ x ∈ Set.Icc a T, ∀ u ∈ Set.Icc 0 b, γ x = τ u →
          (x = T ∧ u = 0) ∨ (x = a ∧ u = b)) := by
  have hret : bigonLoop γ τ T 0 = bigonLoop γ τ T (T + s) := by
    rw [bigonLoop_le (by linarith : (0:ℝ) ≤ T),
      bigonLoop_ge hc1 (by linarith : T ≤ T + s),
      show T + s - T = s by ring, hc2]
  obtain ⟨t₀, t₁, ht₀0, ht₀₁, ht₁, hFeq, hFinj⟩ := first_return
    (show (0:ℝ) < T + s by linarith)
    (bigonLoop_continuousOn hT hs hμ hγ hτ hc1)
    (bigonLoop_locally_injective hT hs hμ hγ hτ hc1)
    hret
  rcases le_or_gt t₁ T with hcase1 | hcase1
  · left
    refine ⟨t₀, t₁, ht₀0, ht₀₁, hcase1, ?_, ?_⟩
    · have h1 := bigonLoop_le (γ := γ) (τ := τ) (T := T)
        (show t₀ ≤ T by linarith)
      have h2 := bigonLoop_le (γ := γ) (τ := τ) (T := T) hcase1
      rw [← h1, ← h2]
      exact hFeq
    · intro x hx y hy hxy
      refine hFinj ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ ?_
      rw [bigonLoop_le (by linarith [hx.2] : x ≤ T),
        bigonLoop_le (by linarith [hy.2] : y ≤ T)]
      exact hxy
  · rcases le_or_gt T t₀ with hcase2 | hcase2
    · right; left
      refine ⟨t₀ - T, t₁ - T, by linarith, by linarith, by linarith [ht₁], ?_, ?_⟩
      · rw [show t₀ - T = t₀ - T from rfl]
        have h1 := bigonLoop_ge hc1 hcase2
        have h2 := bigonLoop_ge hc1 (show T ≤ t₁ by linarith)
        rw [← h1, ← h2]
        exact hFeq
      · intro u hu u' hu' huu
        have h3 : u + T = u' + T := by
          refine hFinj (x₁ := u + T) (x₂ := u' + T)
            ⟨by linarith [hu.1], by linarith [hu.2]⟩
            ⟨by linarith [hu'.1], by linarith [hu'.2]⟩ ?_
          rw [bigonLoop_ge hc1 (by linarith [hu.1] : T ≤ u + T),
            bigonLoop_ge hc1 (by linarith [hu'.1] : T ≤ u' + T),
            show u + T - T = u by ring, show u' + T - T = u' by ring]
          exact huu
        linarith
    · right; right
      have hb0 : 0 < t₁ - T := by linarith
      have hbs : t₁ - T ≤ s := by linarith [ht₁]
      have hcornerb : τ (t₁ - T) = γ t₀ := by
        have h2 := bigonLoop_ge hc1 (show T ≤ t₁ by linarith)
        have h1 := bigonLoop_le (γ := γ) (τ := τ) (T := T)
          (show t₀ ≤ T by linarith)
        rw [← h2, ← hFeq, h1]
      have hinjγ : Set.InjOn γ (Set.Icc t₀ T) := by
        intro x hx y hy hxy
        refine hFinj ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ ?_
        rw [bigonLoop_le hx.2, bigonLoop_le hy.2]
        exact hxy
      have hinjτ : Set.InjOn τ (Set.Icc 0 (t₁ - T)) := by
        intro u hu u' hu' huu
        by_cases hub : u = t₁ - T <;> by_cases hu'b : u' = t₁ - T
        · rw [hub, hu'b]
        · exfalso
          have huu' : τ u' = γ t₀ := by
            rw [← huu, hub]
            exact hcornerb
          have h3 : u' + T = t₀ := by
            refine hFinj (x₁ := u' + T) (x₂ := t₀)
              ⟨by linarith [hu'.1], by
                rcases lt_or_eq_of_le hu'.2 with h | h
                · linarith
                · exact absurd h hu'b⟩
              ⟨le_refl t₀, ht₀₁⟩ ?_
            rw [bigonLoop_ge hc1 (by linarith [hu'.1] : T ≤ u' + T),
              bigonLoop_le (by linarith : t₀ ≤ T),
              show u' + T - T = u' by ring]
            exact huu'
          linarith [hu'.1]
        · exfalso
          have huu' : τ u = γ t₀ := by
            rw [huu, hu'b]
            exact hcornerb
          have h3 : u + T = t₀ := by
            refine hFinj (x₁ := u + T) (x₂ := t₀)
              ⟨by linarith [hu.1], by
                rcases lt_or_eq_of_le hu.2 with h | h
                · linarith
                · exact absurd h hub⟩
              ⟨le_refl t₀, ht₀₁⟩ ?_
            rw [bigonLoop_ge hc1 (by linarith [hu.1] : T ≤ u + T),
              bigonLoop_le (by linarith : t₀ ≤ T),
              show u + T - T = u by ring]
            exact huu'
          linarith [hu.1]
        · have h3 : u + T = u' + T := by
            refine hFinj (x₁ := u + T) (x₂ := u' + T)
              ⟨by linarith [hu.1], by
                rcases lt_or_eq_of_le hu.2 with h | h
                · linarith
                · exact absurd h hub⟩
              ⟨by linarith [hu'.1], by
                rcases lt_or_eq_of_le hu'.2 with h | h
                · linarith
                · exact absurd h hu'b⟩ ?_
            rw [bigonLoop_ge hc1 (by linarith [hu.1] : T ≤ u + T),
              bigonLoop_ge hc1 (by linarith [hu'.1] : T ≤ u' + T),
              show u + T - T = u by ring, show u' + T - T = u' by ring]
            exact huu
          linarith
      refine ⟨t₀, t₁ - T, ht₀0, hcase2, hb0, hbs, hcornerb, hinjγ, hinjτ, ?_⟩
      intro x hx u hu hxu
      by_cases hub : u = t₁ - T
      · right
        refine ⟨?_, hub⟩
        have hxa : γ x = γ t₀ := by
          rw [hxu, hub]
          exact hcornerb
        exact hinjγ hx ⟨le_refl t₀, by linarith⟩ hxa
      · left
        have h3 : x = u + T := by
          refine hFinj (x₁ := x) (x₂ := u + T)
            ⟨hx.1, by linarith [hx.2]⟩
            ⟨by linarith [hu.1], by
              rcases lt_or_eq_of_le hu.2 with h | h
              · linarith
              · exact absurd h hub⟩ ?_
          rw [bigonLoop_le hx.2,
            bigonLoop_ge hc1 (by linarith [hu.1] : T ≤ u + T),
            show u + T - T = u by ring]
          exact hxu
        constructor
        · linarith [hx.2, hu.1]
        · linarith [hx.2, hu.1]

/-- **The corner data pack**: at a corner where the transverse arc crosses the
horizontal arc, a single natural chart develops the horizontal arc with unit real
speed and the transverse arc with unit imaginary speed on a common window, the chart
image containing a ball about the developed corner. -/
theorem corner_data {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {sγ sτ : Set ℝ} {t₁ : ℝ}
    (hγ : IsTrajOn q γ sγ) (ht₁ : t₁ ∈ sγ)
    (hτ : IsTrajOn (fun z => -q z) τ sτ) {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hsubτ : Set.Icc (-η₀) η₀ ⊆ sτ)
    (hcorner : τ 0 = γ t₁) :
    ∃ (S : Set ℂ) (Φ : ℂ → ℂ) (ε r₀ : ℝ), 0 < r₀ ∧ (ε = 1 ∨ ε = -1) ∧
      IsOpen S ∧ DifferentiableOn ℂ Φ S ∧ Set.InjOn Φ S ∧
      (∀ z ∈ S, deriv Φ z ^ 2 = -q z) ∧ (∀ z ∈ S, q z ≠ 0) ∧
      Metric.ball (Φ (γ t₁)) (4 * r₀) ⊆ Φ '' S ∧
      (∀ u ∈ Set.Icc (t₁ - r₀) (t₁ + r₀) ∩ sγ,
        γ u ∈ S ∧ Φ (γ u) = Φ (γ t₁) + ((u - t₁ : ℝ) : ℂ)) ∧
      (∀ v ∈ Set.Icc (-r₀) r₀,
        τ v ∈ S ∧ Φ (τ v) = Φ (γ t₁) - Complex.I * ε * ((v : ℝ) : ℂ)) := by
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hγ.chart t₁ ht₁
  rw [Filter.eventually_iff] at hev
  obtain ⟨εγ, hεγ, hballγ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  -- the transverse arc stays in the chart on a symmetric window
  have hτc : ContinuousWithinAt τ sτ 0 := hτ.cont 0 (hsubτ ⟨by linarith, hη₀.le⟩)
  have hτ0U : τ 0 ∈ U := by
    rw [hcorner]
    exact hpU
  obtain ⟨η₁, hη₁, hballτ⟩ := Metric.mem_nhdsWithin_iff.mp (hτc (hUo.mem_nhds hτ0U))
  set η : ℝ := min (η₁ / 2) η₀ with hηdef
  have hη : 0 < η := lt_min (by positivity) hη₀
  have hηsub : Set.Icc (-η) η ⊆ sτ := by
    intro v hv
    have h1 : η ≤ η₀ := min_le_right _ _
    exact hsubτ ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have htrackU : ∀ v ∈ Set.Icc (-η) η, τ v ∈ U := by
    intro v hv
    refine hballτ ⟨?_, hηsub hv⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 : η ≤ η₁ / 2 := min_le_left _ _
    constructor
    · linarith [hv.1]
    · linarith [hv.2]
  obtain ⟨ε, hεpm, hlaw⟩ := horizontal_level hUo hΦd hΦsq hτ
    (by linarith : -η ≤ η) hηsub htrackU
  -- the chart image contains a ball about the developed corner
  have hder : deriv Φ (γ t₁) ≠ 0 := by
    intro h0
    have h1 := hΦsq _ hpU
    rw [h0] at h1
    exact hUne _ hpU (by simpa using h1.symm)
  have han : AnalyticAt ℂ Φ (γ t₁) := (hΦd.analyticOnNhd hUo) _ hpU
  have hstrict : HasStrictDerivAt Φ (deriv Φ (γ t₁)) (γ t₁) :=
    (han.contDiffAt (n := 1)).hasStrictDerivAt one_ne_zero
  have himg : Φ '' U ∈ nhds (Φ (γ t₁)) := by
    rw [← hstrict.map_nhds_eq hder]
    exact Filter.image_mem_map (hUo.mem_nhds hpU)
  obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.mp himg
  -- the common radius
  set r₀ : ℝ := min (min (εγ / 2) η) (ρ / 8) with hr₀def
  have hr₀ : 0 < r₀ := lt_min (lt_min (by positivity) hη) (by positivity)
  have hr₀γ : r₀ ≤ εγ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hr₀η : r₀ ≤ η := le_trans (min_le_left _ _) (min_le_right _ _)
  have hr₀ρ : r₀ ≤ ρ / 8 := min_le_right _ _
  refine ⟨U, Φ, ε, r₀, hr₀, hεpm, hUo, hΦd, hΦinj, hΦsq, hUne, ?_, ?_, ?_⟩
  · -- the ball containment
    refine Set.Subset.trans ?_ hρball
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    linarith [hw]
  · -- the horizontal development
    intro u hu
    have h1 : u ∈ Metric.ball t₁ εγ ∩ sγ := by
      refine ⟨?_, hu.2⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [hu.1.1]
      · linarith [hu.1.2]
    exact hballγ h1
  · -- the transverse development, re-anchored at the corner
    intro v hv
    have hvη : v ∈ Set.Icc (-η) η :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have h0η : (0:ℝ) ∈ Set.Icc (-η) η := ⟨by linarith, hη.le⟩
    have hlv := hlaw v hvη
    have hl0 := hlaw 0 h0η
    refine ⟨htrackU v hvη, ?_⟩
    have h2 : Φ (τ 0) = Φ (γ t₁) := by rw [hcorner]
    rw [hlv]
    rw [← h2]
    rw [hl0]
    push_cast
    ring

/-- **Trajectories shift**: precomposition with a translation is again a trajectory on
the translated domain. -/
theorem isTrajOn_shift {q : ℂ → ℂ} {γ : ℝ → ℂ} {s : Set ℝ} (c : ℝ)
    (hγ : IsTrajOn q γ s) :
    IsTrajOn q (fun v => γ (c + v)) {v | c + v ∈ s} := by
  constructor
  · exact hγ.cont.comp (continuous_const.add continuous_id).continuousOn
      fun v hv => hv
  · intro t ht
    obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hγ.chart (c + t) ht
    refine ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
    have hcont : Filter.Tendsto (fun v : ℝ => c + v)
        (nhdsWithin t {v | c + v ∈ s}) (nhdsWithin (c + t) s) := by
      refine ContinuousWithinAt.tendsto_nhdsWithin
        ((continuous_const.add continuous_id).continuousWithinAt) ?_
      intro v hv
      exact hv
    filter_upwards [hcont.eventually hev] with v hv
    refine ⟨hv.1, ?_⟩
    rw [hv.2]
    push_cast
    ring

/-- **The two corner kits of a sub-bigon**: charts at both corners with a common
radius, developing the horizontal arc with unit real speed and the transverse arc with
unit imaginary speed, the chart images containing balls about the developed
corners. -/
theorem bigon_corner_kits {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {a T b μ s : ℝ}
    (hμ : 0 < μ) (ha0 : 0 ≤ a) (haT : a < T) (hb0 : 0 < b) (hbs : b ≤ s)
    (hγ : IsTrajOn q γ (Set.Icc (-μ) (T + μ)))
    (hτ : IsTrajOn (fun z => -q z) τ (Set.Icc (-μ) (s + μ)))
    (hc1 : τ 0 = γ T) (hc2 : τ b = γ a) :
    ∃ (S₁ S₂ : Set ℂ) (Φ₁ Φ₂ : ℂ → ℂ) (ε₁ ε₂ r₀ : ℝ),
      0 < r₀ ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      IsOpen S₁ ∧ DifferentiableOn ℂ Φ₁ S₁ ∧ Set.InjOn Φ₁ S₁ ∧
      (∀ z ∈ S₁, deriv Φ₁ z ^ 2 = -q z) ∧ (∀ z ∈ S₁, q z ≠ 0) ∧
      IsOpen S₂ ∧ DifferentiableOn ℂ Φ₂ S₂ ∧ Set.InjOn Φ₂ S₂ ∧
      (∀ z ∈ S₂, deriv Φ₂ z ^ 2 = -q z) ∧ (∀ z ∈ S₂, q z ≠ 0) ∧
      Metric.ball (Φ₁ (γ T)) (4 * r₀) ⊆ Φ₁ '' S₁ ∧
      Metric.ball (Φ₂ (γ a)) (4 * r₀) ⊆ Φ₂ '' S₂ ∧
      (∀ u ∈ Set.Icc (T - r₀) (T + r₀) ∩ Set.Icc (-μ) (T + μ),
        γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ)) ∧
      (∀ v ∈ Set.Icc (-r₀) r₀,
        τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ)) ∧
      (∀ u ∈ Set.Icc (a - r₀) (a + r₀) ∩ Set.Icc (-μ) (T + μ),
        γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ)) ∧
      (∀ v ∈ Set.Icc (b - r₀) (b + r₀),
        τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ)) := by
  have hTmem : T ∈ Set.Icc (-μ) (T + μ) := ⟨by linarith, by linarith⟩
  have hamem : a ∈ Set.Icc (-μ) (T + μ) := ⟨by linarith, by linarith⟩
  -- kit at the first corner
  obtain ⟨S₁, Φ₁, ε₁, r₁, hr₁, hε₁, hS₁o, hΦ₁d, hΦ₁inj, hΦ₁sq, hq₁ne, hball₁,
      hdevγ₁, hdevτ₁⟩ :=
    corner_data hγ hTmem hτ (hη₀ := hμ)
      (fun v hv => ⟨hv.1, by linarith [hv.2]⟩) hc1
  -- kit at the second corner, through the shifted transverse arc
  have hτsh := isTrajOn_shift b hτ
  have hshcorner : (fun v => τ (b + v)) 0 = γ a := by
    change τ (b + 0) = γ a
    rw [add_zero, hc2]
  obtain ⟨S₂, Φ₂, ε₂, r₂, hr₂, hε₂, hS₂o, hΦ₂d, hΦ₂inj, hΦ₂sq, hq₂ne, hball₂,
      hdevγ₂, hdevτ₂'⟩ :=
    corner_data hγ hamem hτsh (hη₀ := hμ)
      (fun v hv => by
        change b + v ∈ Set.Icc (-μ) (s + μ)
        exact ⟨by linarith [hv.1], by linarith [hv.2]⟩) hshcorner
  -- the common radius
  refine ⟨S₁, S₂, Φ₁, Φ₂, ε₁, ε₂, min r₁ r₂, lt_min hr₁ hr₂, hε₁, hε₂,
    hS₁o, hΦ₁d, hΦ₁inj, hΦ₁sq, hq₁ne, hS₂o, hΦ₂d, hΦ₂inj, hΦ₂sq, hq₂ne,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Set.Subset.trans ?_ hball₁
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    have h1 : min r₁ r₂ ≤ r₁ := min_le_left _ _
    linarith
  · refine Set.Subset.trans ?_ hball₂
    intro w hw
    rw [Metric.mem_ball] at hw ⊢
    have h1 : min r₁ r₂ ≤ r₂ := min_le_right _ _
    linarith
  · intro u hu
    refine hdevγ₁ u ⟨⟨?_, ?_⟩, hu.2⟩
    · have h1 : min r₁ r₂ ≤ r₁ := min_le_left _ _
      linarith [hu.1.1]
    · have h1 : min r₁ r₂ ≤ r₁ := min_le_left _ _
      linarith [hu.1.2]
  · intro v hv
    refine hdevτ₁ v ⟨?_, ?_⟩
    · have h1 : min r₁ r₂ ≤ r₁ := min_le_left _ _
      linarith [hv.1]
    · have h1 : min r₁ r₂ ≤ r₁ := min_le_left _ _
      linarith [hv.2]
  · intro u hu
    refine hdevγ₂ u ⟨⟨?_, ?_⟩, hu.2⟩
    · have h1 : min r₁ r₂ ≤ r₂ := min_le_right _ _
      linarith [hu.1.1]
    · have h1 : min r₁ r₂ ≤ r₂ := min_le_right _ _
      linarith [hu.1.2]
  · intro v hv
    have h2 := hdevτ₂' (v - b) ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h3 : τ (b + (v - b)) = τ v := by
          rw [show b + (v - b) = v by ring]
        rw [← h3]
        exact h2.1
      · have h3 : τ (b + (v - b)) = τ v := by
          rw [show b + (v - b) = v by ring]
        rw [← h3]
        exact h2.2
    · have h1 : min r₁ r₂ ≤ r₂ := min_le_right _ _
      linarith [hv.1]
    · have h1 : min r₁ r₂ ≤ r₂ := min_le_right _ _
      linarith [hv.2]

/-- **Reciprocal chart velocity along a development**: where a trajectory develops
straight in a chart, its velocity is the reciprocal chart derivative. -/
theorem dev_velocity {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S)
    {γ : ℝ → ℂ} {d : ℂ} {u₀ w₀ T : ℝ} {c : ℂ}
    (hd : HasDerivAt γ d u₀)
    (hwin : 0 < w₀)
    (hdev : ∀ u ∈ Set.Icc (u₀ - w₀) (u₀ + w₀), γ u ∈ S ∧ Φ (γ u) = c + ((u - T : ℝ) : ℂ)) :
    deriv Φ (γ u₀) * d = 1 := by
  have hm := hdev u₀ ⟨by linarith, by linarith⟩
  have hΦat : DifferentiableAt ℂ Φ (γ u₀) := hΦd.differentiableAt (hS.mem_nhds hm.1)
  have hchain : HasDerivAt (fun u => Φ (γ u)) (deriv Φ (γ u₀) * d) u₀ :=
    HasDerivAt.comp (h := γ) u₀ hΦat.hasDerivAt hd
  have haff : HasDerivAt (fun u : ℝ => c + ((u - T : ℝ) : ℂ)) 1 u₀ := by
    have h1 : HasDerivAt (fun z : ℂ => c + (z - (T : ℂ))) 1 ((u₀ : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((u₀ : ℝ) : ℂ)).sub_const (T : ℂ)).const_add c
    have h2 := h1.comp_ofReal
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with u
    push_cast
    ring
  have hloc : (fun u => Φ (γ u)) =ᶠ[nhds u₀] fun u : ℝ => c + ((u - T : ℝ) : ℂ) := by
    have hIoo : Set.Ioo (u₀ - w₀) (u₀ + w₀) ∈ nhds u₀ := by
      refine Ioo_mem_nhds ?_ ?_ <;> linarith
    filter_upwards [hIoo] with u hu
    exact (hdev u ⟨hu.1.le, hu.2.le⟩).2
  have hchain' : HasDerivAt (fun u : ℝ => c + ((u - T : ℝ) : ℂ))
      (deriv Φ (γ u₀) * d) u₀ := hchain.congr_of_eventuallyEq hloc.symm
  exact hchain'.unique haff

/-- **Transverse development velocity**: where a transverse arc develops with unit
imaginary speed, its velocity satisfies the rotated reciprocal law. -/
theorem dev_velocity_vert {Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S)
    {τ : ℝ → ℂ} {d : ℂ} {v₀ w₀ b : ℝ} {c : ℂ} {ε : ℝ}
    (hd : HasDerivAt τ d v₀) (hwin : 0 < w₀)
    (hdev : ∀ v ∈ Set.Icc (v₀ - w₀) (v₀ + w₀),
      τ v ∈ S ∧ Φ (τ v) = c - Complex.I * ε * ((v - b : ℝ) : ℂ)) :
    deriv Φ (τ v₀) * d = -(Complex.I * ε) := by
  have hm := hdev v₀ ⟨by linarith, by linarith⟩
  have hΦat : DifferentiableAt ℂ Φ (τ v₀) := hΦd.differentiableAt (hS.mem_nhds hm.1)
  have hchain : HasDerivAt (fun v => Φ (τ v)) (deriv Φ (τ v₀) * d) v₀ :=
    HasDerivAt.comp (h := τ) v₀ hΦat.hasDerivAt hd
  have haff : HasDerivAt (fun v : ℝ => c - Complex.I * ε * ((v - b : ℝ) : ℂ))
      (-(Complex.I * ε)) v₀ := by
    have h1 : HasDerivAt (fun z : ℂ => c - Complex.I * ε * (z - (b : ℂ)))
        (-(Complex.I * ε)) ((v₀ : ℝ) : ℂ) := by
      have h2 := (((hasDerivAt_id ((v₀ : ℝ) : ℂ)).sub_const
        (b : ℂ)).const_mul (Complex.I * (ε : ℂ))).const_sub c
      simpa using h2
    have h2 := h1.comp_ofReal
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with v
    push_cast
    ring
  have hloc : (fun v => Φ (τ v))
      =ᶠ[nhds v₀] fun v : ℝ => c - Complex.I * ε * ((v - b : ℝ) : ℂ) := by
    have hIoo : Set.Ioo (v₀ - w₀) (v₀ + w₀) ∈ nhds v₀ := by
      refine Ioo_mem_nhds ?_ ?_ <;> linarith
    filter_upwards [hIoo] with v hv
    exact (hdev v ⟨hv.1.le, hv.2.le⟩).2
  have hchain' : HasDerivAt (fun v : ℝ => c - Complex.I * ε * ((v - b : ℝ) : ℂ))
      (deriv Φ (τ v₀) * d) v₀ := hchain.congr_of_eventuallyEq hloc.symm
  exact hchain'.unique haff

/-- **The canonical velocity field of a trajectory**: at interior times the trajectory
differentiates with its canonical derivative, which is continuous there. -/
theorem traj_deriv_continuous {q : ℂ → ℂ} {γ : ℝ → ℂ} {s : Set ℝ}
    (hγ : IsTrajOn q γ s) :
    ∀ t ∈ s, s ∈ nhds t →
      HasDerivAt γ (deriv γ t) t ∧ ContinuousAt (deriv γ) t := by
  intro t ht hnhds
  obtain ⟨d, hd, -⟩ := traj_hasDerivAt hγ ht hnhds
  have hd' : HasDerivAt γ (deriv γ t) t := by
    rw [hd.deriv]
    exact hd
  refine ⟨hd', ?_⟩
  -- the chart window carries the reciprocal formula
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hγ.chart t ht
  rw [nhdsWithin_eq_nhds.mpr hnhds, Filter.eventually_iff] at hev
  obtain ⟨W, hWsub, hWo, hWt⟩ := mem_nhds_iff.mp hev
  -- on the open window the derivative is the reciprocal chart derivative
  have hder : ∀ u ∈ W, deriv Φ (γ u) ≠ 0 := by
    intro u hu h0
    have h1 := hΦsq _ (hWsub hu).1
    rw [h0] at h1
    exact hUne _ (hWsub hu).1 (by simpa using h1.symm)
  have hVnhds : W ∩ interior s ∈ nhds t :=
    Filter.inter_mem (hWo.mem_nhds hWt)
      (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hnhds))
  have hVform : ∀ u ∈ W ∩ interior s, deriv γ u = (deriv Φ (γ u))⁻¹ := by
    rintro u ⟨huW, huint⟩
    have hsu : s ∈ nhds u := mem_interior_iff_mem_nhds.mp huint
    obtain ⟨du, hdu, -⟩ := traj_hasDerivAt hγ (interior_subset huint) hsu
    obtain ⟨δu, hδu, hballW⟩ := Metric.isOpen_iff.mp hWo u huW
    have hdev : ∀ v ∈ Set.Icc (u - δu/2) (u + δu/2),
        γ v ∈ U ∧ Φ (γ v) = Φ (γ t) + ((v - t : ℝ) : ℂ) := by
      intro v hv
      refine hWsub (hballW ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · linarith [hv.1]
      · linarith [hv.2]
    have h1 := dev_velocity hUo hΦd hdu (by positivity : (0:ℝ) < δu/2) hdev
    have h2 : du = (deriv Φ (γ u))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hdu.deriv]
    exact h2
  have hγct : ContinuousAt γ t := hγ.cont.continuousAt hnhds
  have hdΦ : ContinuousAt (deriv Φ) (γ t) :=
    ((hΦd.analyticOnNhd hUo).deriv.continuousOn (s := U)).continuousAt
      (hUo.mem_nhds hpU)
  have hderT : deriv Φ (γ t) ≠ 0 := hder t hWt
  have hRHS : ContinuousAt (fun u => (deriv Φ (γ u))⁻¹) t :=
    (hdΦ.comp hγct).inv₀ hderT
  refine hRHS.congr ?_
  refine (Filter.eventuallyEq_of_mem hVnhds hVform).symm

/-- The corner piece: the chart pullback of the parametrized circle. -/
noncomputable def cornerPiece (Φ : ℂ → ℂ) (S : Set ℂ) (c : ℂ)
    (r α ω : ℝ) : ℝ → ℂ := fun u =>
  Function.invFunOn Φ S
    (c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (u : ℂ))))

/-- The velocity field of the corner piece. -/
noncomputable def cornerSpeed (Φ : ℂ → ℂ) (S : Set ℂ) (c : ℂ)
    (r α ω : ℝ) : ℝ → ℂ := fun u =>
  ((r : ℂ) * Complex.I * (ω : ℂ)
      * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (u : ℂ))))
    / deriv Φ (cornerPiece Φ S c r α ω u)

/-- **The corner-piece package**: membership, development, derivative, and the
exponential presentation, through the named piece. -/
theorem cornerPiece_package {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) (hqne : ∀ z ∈ S, q z ≠ 0)
    {c : ℂ} {r α ω : ℝ} (hr : 0 < r) (hω : ω ≠ 0)
    (htr : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Φ '' S) (u : ℝ) :
    cornerPiece Φ S c r α ω u ∈ S
    ∧ Φ (cornerPiece Φ S c r α ω u)
      = c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
    ∧ HasDerivAt (cornerPiece Φ S c r α ω) (cornerSpeed Φ S c r α ω u) u
    ∧ q (cornerPiece Φ S c r α ω u) * cornerSpeed Φ S c r α ω u ^ 2
      = Complex.exp (((Real.log (r^2 * ω^2) : ℝ) : ℂ)
          + 2 * Complex.I * ((α : ℂ) + (ω : ℂ) * u)) := by
  obtain ⟨hmem, hdev, hderiv, hexp⟩ :=
    corner_pullback hS hΦ hinj hsq hqne hr hω htr u
  exact ⟨hmem, hdev, hderiv, hexp⟩

/-- **The first-corner seam bundle**: the corner piece with signs `(1, -ε₁)` centered at
`Φ₁ (γ T) - r + I·(-ε₁)·r` starts at the truncated horizontal point `γ (T - r)`, ends at
the truncated transverse point `τ r`, its endpoint velocities are the quarter-sweep speed
`r·π/2` times the canonical arc velocities, and its circle lies in the chart image. -/
theorem corner1_seams {γ τ : ℝ → ℂ} {T : ℝ}
    {S₁ : Set ℂ} {Φ₁ : ℂ → ℂ} {ε₁ r r₀ α ω : ℝ}
    (hr : 0 < r) (hrr₀ : r < r₀)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hα : α = -(-ε₁) * (Real.pi / 2)) (hω : ω = 1 * (-ε₁) * (Real.pi / 2))
    (hS₁o : IsOpen S₁) (hΦ₁d : DifferentiableOn ℂ Φ₁ S₁)
    (hΦ₁inj : Set.InjOn Φ₁ S₁)
    (hball₁ : Metric.ball (Φ₁ (γ T)) (4 * r₀) ⊆ Φ₁ '' S₁)
    (hdevγ₁ : ∀ u ∈ Set.Icc (T - r₀) (T + r₀),
      γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ))
    (hdevτ₁ : ∀ v ∈ Set.Icc (-r₀) r₀,
      τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ))
    (hdγ : HasDerivAt γ (deriv γ (T - r)) (T - r))
    (hdτ : HasDerivAt τ (deriv τ r) r) :
    cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 0
      = γ (T - r)
    ∧ cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 1
      = τ r
    ∧ cornerSpeed Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 0
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv γ (T - r)
    ∧ cornerSpeed Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 1
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv τ r
    ∧ ∀ u : ℝ, (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
        + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (u : ℂ)))
      ∈ Φ₁ '' S₁ := by
  have hεv : (-ε₁ : ℝ) = 1 ∨ (-ε₁ : ℝ) = -1 := by
    rcases hε₁ with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ :=
    corner_geometry (εh := (1:ℝ)) (εv := (-ε₁ : ℝ))
      (Or.inl rfl) hεv hr hα hω (Φ₁ (γ T))
  have hTrmem : T - r ∈ Set.Icc (T - r₀) (T + r₀) := by
    constructor <;> linarith
  have hrmem : r ∈ Set.Icc (-r₀) r₀ := ⟨by linarith, by linarith⟩
  obtain ⟨hmγ, hdγv⟩ := hdevγ₁ (T - r) hTrmem
  obtain ⟨hmτ, hdτv⟩ := hdevτ₁ r hrmem
  have htr : ∀ u : ℝ, (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (u : ℂ)))
      ∈ Φ₁ '' S₁ := by
    intro u
    refine hball₁ ?_
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (hg6 u) (by linarith)
  have hP0 : cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 0
      = γ (T - r) := by
    refine seam_match hΦ₁inj hmγ ?_
    rw [hdγv, hg1]
    push_cast
    ring
  have hP1 : cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 1
      = τ r := by
    refine seam_match hΦ₁inj hmτ ?_
    rw [hdτv, hg2]
    push_cast
    ring
  have hdev' : ∀ v ∈ Set.Icc ((T - r) - (r₀ - r)) ((T - r) + (r₀ - r)),
      γ v ∈ S₁ ∧ Φ₁ (γ v) = Φ₁ (γ T) + ((v - T : ℝ) : ℂ) := by
    intro v hv
    exact hdevγ₁ v ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hvelγ := dev_velocity hS₁o hΦ₁d hdγ
    (show (0:ℝ) < r₀ - r by linarith) hdev'
  have hderivγ : deriv γ (T - r) = (deriv Φ₁ (γ (T - r)))⁻¹ :=
    eq_inv_of_mul_eq_one_right hvelγ
  have hdevτ' : ∀ v ∈ Set.Icc (r - (r₀ - r)) (r + (r₀ - r)),
      τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v - 0 : ℝ) : ℂ) := by
    intro v hv
    have h1 := hdevτ₁ v ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine ⟨h1.1, ?_⟩
    rw [h1.2]
    norm_num
  have hvelτ := dev_velocity_vert hS₁o hΦ₁d hdτ
    (show (0:ℝ) < r₀ - r by linarith) hdevτ'
  have hΦτne : deriv Φ₁ (τ r) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hvelτ
    have h1 : (Complex.I * (ε₁ : ℂ)) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      have h2 : ε₁ ≠ 0 := by rcases hε₁ with h | h <;> rw [h] <;> norm_num
      exact_mod_cast h2
    exact h1 (neg_eq_zero.mp hvelτ.symm)
  have hderivτ : deriv τ r = -(Complex.I * ε₁) / deriv Φ₁ (τ r) :=
    (eq_div_iff hΦτne).mpr (by linear_combination hvelτ)
  refine ⟨hP0, hP1, ?_, ?_, htr⟩
  · change ((r : ℂ) * Complex.I * (ω : ℂ)
        * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * ((0:ℝ) : ℂ))))
      / deriv Φ₁ (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 0)
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv γ (T - r)
    rw [hP0, hg3, hderivγ]
    push_cast
    ring
  · change ((r : ℂ) * Complex.I * (ω : ℂ)
        * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * ((1:ℝ) : ℂ))))
      / deriv Φ₁ (cornerPiece Φ₁ S₁
        (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α ω 1)
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv τ r
    rw [hP1, hg4, hderivτ]
    push_cast
    ring

/-- **The second-corner seam bundle**: the corner piece with the reversed circle
(`α' = -ε₂·π`, `ω' = ε₂·π/2`) centered at `Φ₂ (γ a) + r + I·ε₂·r` starts at the truncated
transverse point `τ (b - r)`, ends at the truncated horizontal point `γ (a + r)`, its
endpoint velocities are the quarter-sweep speed `r·π/2` times the canonical arc
velocities, and its circle lies in the chart image. -/
theorem corner2_seams {γ τ : ℝ → ℂ} {a b : ℝ}
    {S₂ : Set ℂ} {Φ₂ : ℂ → ℂ} {ε₂ r r₀ α' ω' : ℝ}
    (hr : 0 < r) (hrr₀ : r < r₀)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hα' : α' = -ε₂ * Real.pi) (hω' : ω' = ε₂ * (Real.pi / 2))
    (hS₂o : IsOpen S₂) (hΦ₂d : DifferentiableOn ℂ Φ₂ S₂)
    (hΦ₂inj : Set.InjOn Φ₂ S₂)
    (hball₂ : Metric.ball (Φ₂ (γ a)) (4 * r₀) ⊆ Φ₂ '' S₂)
    (hdevγ₂ : ∀ u ∈ Set.Icc (a - r₀) (a + r₀),
      γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ))
    (hdevτ₂ : ∀ v ∈ Set.Icc (b - r₀) (b + r₀),
      τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ))
    (hdγ : HasDerivAt γ (deriv γ (a + r)) (a + r))
    (hdτ : HasDerivAt τ (deriv τ (b - r)) (b - r)) :
    cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 0
      = τ (b - r)
    ∧ cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 1
      = γ (a + r)
    ∧ cornerSpeed Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 0
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv τ (b - r)
    ∧ cornerSpeed Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 1
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv γ (a + r)
    ∧ ∀ u : ℝ, (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
        + (r : ℂ) * Complex.exp (Complex.I * ((α' : ℂ) + (ω' : ℂ) * (u : ℂ)))
      ∈ Φ₂ '' S₂ := by
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ :=
    corner_geometry (εh := (-1:ℝ)) (εv := ε₂) (Or.inr rfl) hε₂ hr
      (α := -ε₂*(Real.pi/2)) (ω := (-1)*ε₂*(Real.pi/2)) rfl rfl (Φ₂ (γ a))
  have he0 : Complex.I * ((α' : ℂ) + (ω' : ℂ) * ((0:ℝ) : ℂ))
      = Complex.I * (((-ε₂*(Real.pi/2) : ℝ) : ℂ)
          + (((-1)*ε₂*(Real.pi/2) : ℝ) : ℂ) * ((1:ℝ) : ℂ)) := by
    rw [hα', hω']; push_cast; ring
  have he1 : Complex.I * ((α' : ℂ) + (ω' : ℂ) * ((1:ℝ) : ℂ))
      = Complex.I * (((-ε₂*(Real.pi/2) : ℝ) : ℂ)
          + (((-1)*ε₂*(Real.pi/2) : ℝ) : ℂ) * ((0:ℝ) : ℂ)) := by
    rw [hα', hω']; push_cast; ring
  have hωc : (ω' : ℂ) = -((((-1)*ε₂*(Real.pi/2) : ℝ)) : ℂ) := by
    rw [hω']; push_cast; ring
  have hbrmem : b - r ∈ Set.Icc (b - r₀) (b + r₀) := by
    constructor <;> linarith
  have harmem : a + r ∈ Set.Icc (a - r₀) (a + r₀) := by
    constructor <;> linarith
  obtain ⟨hmτ₂, hdτ₂v⟩ := hdevτ₂ (b - r) hbrmem
  obtain ⟨hmγ₂, hdγ₂v⟩ := hdevγ₂ (a + r) harmem
  have htr : ∀ u : ℝ, (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
      + (r : ℂ) * Complex.exp (Complex.I * ((α' : ℂ) + (ω' : ℂ) * (u : ℂ)))
      ∈ Φ₂ '' S₂ := by
    intro u
    refine hball₂ ?_
    rw [Metric.mem_ball]
    have heu : Complex.I * ((α' : ℂ) + (ω' : ℂ) * (u : ℂ))
        = Complex.I * (((-ε₂*(Real.pi/2) : ℝ) : ℂ)
            + (((-1)*ε₂*(Real.pi/2) : ℝ) : ℂ) * ((1 - u : ℝ) : ℂ)) := by
      rw [hα', hω']; push_cast; ring
    rw [heu]
    exact lt_of_le_of_lt (hg6 (1 - u)) (by linarith)
  have hP0 : cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 0
      = τ (b - r) := by
    refine seam_match hΦ₂inj hmτ₂ ?_
    rw [hdτ₂v, he0, hg2]
    push_cast
    ring
  have hP1 : cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 1
      = γ (a + r) := by
    refine seam_match hΦ₂inj hmγ₂ ?_
    rw [hdγ₂v, he1, hg1]
    push_cast
    ring
  have hdev' : ∀ v ∈ Set.Icc ((a + r) - (r₀ - r)) ((a + r) + (r₀ - r)),
      γ v ∈ S₂ ∧ Φ₂ (γ v) = Φ₂ (γ a) + ((v - a : ℝ) : ℂ) := by
    intro v hv
    exact hdevγ₂ v ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hvelγ := dev_velocity hS₂o hΦ₂d hdγ
    (show (0:ℝ) < r₀ - r by linarith) hdev'
  have hderivγ : deriv γ (a + r) = (deriv Φ₂ (γ (a + r)))⁻¹ :=
    eq_inv_of_mul_eq_one_right hvelγ
  have hdevτ' : ∀ v ∈ Set.Icc ((b - r) - (r₀ - r)) ((b - r) + (r₀ - r)),
      τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ) := by
    intro v hv
    exact hdevτ₂ v ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hvelτ := dev_velocity_vert hS₂o hΦ₂d hdτ
    (show (0:ℝ) < r₀ - r by linarith) hdevτ'
  have hΦτne : deriv Φ₂ (τ (b - r)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hvelτ
    have h1 : (Complex.I * (ε₂ : ℂ)) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      have h2 : ε₂ ≠ 0 := by rcases hε₂ with h | h <;> rw [h] <;> norm_num
      exact_mod_cast h2
    exact h1 (neg_eq_zero.mp hvelτ.symm)
  have hderivτ : deriv τ (b - r) = -(Complex.I * ε₂) / deriv Φ₂ (τ (b - r)) :=
    (eq_div_iff hΦτne).mpr (by linear_combination hvelτ)
  refine ⟨hP0, hP1, ?_, ?_, htr⟩
  · change ((r : ℂ) * Complex.I * (ω' : ℂ)
        * Complex.exp (Complex.I * ((α' : ℂ) + (ω' : ℂ) * ((0:ℝ) : ℂ))))
      / deriv Φ₂ (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 0)
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv τ (b - r)
    rw [hP0, he0, hderivτ]
    have hnum : (r : ℂ) * Complex.I * (ω' : ℂ)
        * Complex.exp (Complex.I * (((-ε₂*(Real.pi/2) : ℝ) : ℂ)
            + (((-1)*ε₂*(Real.pi/2) : ℝ) : ℂ) * ((1:ℝ) : ℂ)))
        = -(((r * (Real.pi/2) : ℝ) : ℂ) * Complex.I * (ε₂ : ℂ)) := by
      rw [hωc]
      linear_combination -hg4
    rw [hnum]
    push_cast
    ring
  · change ((r : ℂ) * Complex.I * (ω' : ℂ)
        * Complex.exp (Complex.I * ((α' : ℂ) + (ω' : ℂ) * ((1:ℝ) : ℂ))))
      / deriv Φ₂ (cornerPiece Φ₂ S₂
        (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α' ω' 1)
      = ((r * (Real.pi/2) : ℝ) : ℂ) * deriv γ (a + r)
    rw [hP1, he1, hderivγ]
    have hnum : (r : ℂ) * Complex.I * (ω' : ℂ)
        * Complex.exp (Complex.I * (((-ε₂*(Real.pi/2) : ℝ) : ℂ)
            + (((-1)*ε₂*(Real.pi/2) : ℝ) : ℂ) * ((0:ℝ) : ℂ)))
        = -(((r * (Real.pi/2) : ℝ) : ℂ) * ((-1:ℝ) : ℂ)) := by
      rw [hωc]
      linear_combination -hg3
    rw [hnum]
    push_cast
    ring

/-- The ramped arc: a trajectory piece reparametrized by the cubic ramp. -/
noncomputable def rampArc (f : ℝ → ℂ) (c v L : ℝ) : ℝ → ℂ :=
  fun u => f (cubicRamp c v L u)

/-- The velocity field of the ramped arc. -/
noncomputable def rampArcSpeed (f : ℝ → ℂ) (c v L : ℝ) : ℝ → ℂ :=
  fun u => ((cubicRampSpeed v L u : ℝ) : ℂ) * deriv f (cubicRamp c v L u)

/-- The ramp arc is the curve reparametrized by the cubic ramp. -/
theorem rampArc_apply (f : ℝ → ℂ) (c v L u : ℝ) :
    rampArc f c v L u = f (cubicRamp c v L u) := rfl

/-- The ramp-arc speed is the chain-rule product of the ramp speed and the curve
derivative. -/
theorem rampArcSpeed_apply (f : ℝ → ℂ) (c v L u : ℝ) :
    rampArcSpeed f c v L u
      = ((cubicRampSpeed v L u : ℝ) : ℂ) * deriv f (cubicRamp c v L u) := rfl

/-- **Arc preparation**: on a closed window in the interior of its domain, a trajectory
has the canonical derivative field everywhere, the field is continuous, and the
quadratic differential squares it to `-1`. -/
theorem arc_prep {q : ℂ → ℂ} {γ : ℝ → ℂ} {s : Set ℝ} {c d : ℝ}
    (hγ : IsTrajOn q γ s) (hs : ∀ w ∈ Set.Icc c d, s ∈ nhds w) :
    (∀ w ∈ Set.Icc c d, HasDerivAt γ (deriv γ w) w)
    ∧ ContinuousOn (deriv γ) (Set.Icc c d)
    ∧ ∀ w ∈ Set.Icc c d, q (γ w) * (deriv γ w) ^ 2 = -1 := by
  have hmem : ∀ w ∈ Set.Icc c d, w ∈ s := fun w hw => mem_of_mem_nhds (hs w hw)
  refine ⟨fun w hw => (traj_deriv_continuous hγ w (hmem w hw) (hs w hw)).1,
    fun w hw =>
      ((traj_deriv_continuous hγ w (hmem w hw) (hs w hw)).2).continuousWithinAt,
    fun w hw => ?_⟩
  obtain ⟨d', hd', hq'⟩ := traj_deriv_qsq hγ (hmem w hw) (hs w hw)
  rw [hd'.deriv]
  exact hq'

/-- **The four-piece bundle**: the two ramped trajectory arcs and the two corner pieces
of the rounded bigon form a piecewise-`C¹` loop; the assembled `quarterPW` curve has
derivative `4·quarterPW` of the velocity fields on `[0,1]`, and all four junction
positions and velocities (including the wrap-around) match. -/
theorem four_piece_bundle {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {a b T : ℝ}
    {S₁ S₂ : Set ℂ} {Φ₁ Φ₂ : ℂ → ℂ} {ε₁ ε₂ r r₀ α₁ ω₁ α₂ ω₂ : ℝ} {c₁ c₂ : ℂ}
    (hr : 0 < r) (hrr₀ : r < r₀)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hα₁ : α₁ = -(-ε₁) * (Real.pi / 2)) (hω₁ : ω₁ = 1 * (-ε₁) * (Real.pi / 2))
    (hα₂ : α₂ = -ε₂ * Real.pi) (hω₂ : ω₂ = ε₂ * (Real.pi / 2))
    (hc₁ : c₁ = Φ₁ (γ T) - ((1 : ℝ) : ℂ) * r + Complex.I * ((-ε₁ : ℝ) : ℂ) * r)
    (hc₂ : c₂ = Φ₂ (γ a) - ((-1 : ℝ) : ℂ) * r + Complex.I * (ε₂ : ℂ) * r)
    (h3γ : r * (Real.pi / 2) < 3 * (T - a - 2 * r))
    (h3τ : r * (Real.pi / 2) < 3 * (b - 2 * r))
    (hS₁o : IsOpen S₁) (hΦ₁d : DifferentiableOn ℂ Φ₁ S₁) (hΦ₁inj : Set.InjOn Φ₁ S₁)
    (hΦ₁sq : ∀ z ∈ S₁, deriv Φ₁ z ^ 2 = -q z) (hq₁ne : ∀ z ∈ S₁, q z ≠ 0)
    (hS₂o : IsOpen S₂) (hΦ₂d : DifferentiableOn ℂ Φ₂ S₂) (hΦ₂inj : Set.InjOn Φ₂ S₂)
    (hΦ₂sq : ∀ z ∈ S₂, deriv Φ₂ z ^ 2 = -q z) (hq₂ne : ∀ z ∈ S₂, q z ≠ 0)
    (hball₁ : Metric.ball (Φ₁ (γ T)) (4 * r₀) ⊆ Φ₁ '' S₁)
    (hball₂ : Metric.ball (Φ₂ (γ a)) (4 * r₀) ⊆ Φ₂ '' S₂)
    (hdevγ₁ : ∀ u ∈ Set.Icc (T - r₀) (T + r₀),
      γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ))
    (hdevτ₁ : ∀ v ∈ Set.Icc (-r₀) r₀,
      τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ))
    (hdevγ₂ : ∀ u ∈ Set.Icc (a - r₀) (a + r₀),
      γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ))
    (hdevτ₂ : ∀ v ∈ Set.Icc (b - r₀) (b + r₀),
      τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ))
    (hdγA : ∀ w ∈ Set.Icc (a + r) (T - r), HasDerivAt γ (deriv γ w) w)
    (hdγC : ContinuousOn (deriv γ) (Set.Icc (a + r) (T - r)))
    (hqγ : ∀ w ∈ Set.Icc (a + r) (T - r), q (γ w) * (deriv γ w) ^ 2 = -1)
    (hdτA : ∀ w ∈ Set.Icc r (b - r), HasDerivAt τ (deriv τ w) w)
    (hdτC : ContinuousOn (deriv τ) (Set.Icc r (b - r)))
    (hqτ : ∀ w ∈ Set.Icc r (b - r), q (τ w) * (deriv τ w) ^ 2 = 1) :
    (∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
      (quarterPW (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
        (cornerPiece Φ₁ S₁ c₁ r α₁ ω₁)
        (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
        (cornerPiece Φ₂ S₂ c₂ r α₂ ω₂))
      (4 * quarterPW (rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
        (cornerSpeed Φ₁ S₁ c₁ r α₁ ω₁)
        (rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
        (cornerSpeed Φ₂ S₂ c₂ r α₂ ω₂) t) t)
    ∧ rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) 1
        = cornerPiece Φ₁ S₁ c₁ r α₁ ω₁ 0
    ∧ cornerPiece Φ₁ S₁ c₁ r α₁ ω₁ 1
        = rampArc τ r (r * (Real.pi/2)) (b - 2*r) 0
    ∧ rampArc τ r (r * (Real.pi/2)) (b - 2*r) 1
        = cornerPiece Φ₂ S₂ c₂ r α₂ ω₂ 0
    ∧ cornerPiece Φ₂ S₂ c₂ r α₂ ω₂ 1
        = rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) 0
    ∧ rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) 1
        = cornerSpeed Φ₁ S₁ c₁ r α₁ ω₁ 0
    ∧ cornerSpeed Φ₁ S₁ c₁ r α₁ ω₁ 1
        = rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r) 0
    ∧ rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r) 1
        = cornerSpeed Φ₂ S₂ c₂ r α₂ ω₂ 0
    ∧ cornerSpeed Φ₂ S₂ c₂ r α₂ ω₂ 1
        = rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r) 0 := by
  subst hc₁
  subst hc₂
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hv : (0:ℝ) < r * (Real.pi/2) := mul_pos hr (by linarith)
  have haT : a + r ≤ T - r := by nlinarith
  have hrb : r ≤ b - r := by nlinarith
  obtain ⟨hc1P0, hc1P1, hc1S0, hc1S1, hc1tr⟩ :=
    corner1_seams hr hrr₀ hε₁ hα₁ hω₁ hS₁o hΦ₁d hΦ₁inj hball₁ hdevγ₁ hdevτ₁
      (hdγA (T - r) ⟨haT, le_refl _⟩) (hdτA r ⟨le_refl _, hrb⟩)
  obtain ⟨hc2P0, hc2P1, hc2S0, hc2S1, hc2tr⟩ :=
    corner2_seams hr hrr₀ hε₂ hα₂ hω₂ hS₂o hΦ₂d hΦ₂inj hball₂ hdevγ₂ hdevτ₂
      (hdγA (a + r) ⟨le_refl _, haT⟩) (hdτA (b - r) ⟨hrb, le_refl _⟩)
  have hω₁ne : ω₁ ≠ 0 := by
    rw [hω₁]
    rcases hε₁ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hω₂ne : ω₂ ≠ 0 := by
    rw [hω₂]
    rcases hε₂ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hpk₁ := cornerPiece_package hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne hc1tr
  have hpk₂ := cornerPiece_package hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne hc2tr
  have heγ : (a + r) + (T - a - 2*r) = T - r := by ring
  have heτ : r + (b - 2*r) = b - r := by ring
  have hdA' : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      HasDerivAt γ (deriv γ w) w := by
    rw [heγ]; exact hdγA
  have hdC' : ContinuousOn (deriv γ) (Set.Icc (a + r) ((a + r) + (T - a - 2*r))) := by
    rw [heγ]; exact hdγC
  have hqγ' : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [heγ, Complex.exp_pi_mul_I]
    exact hqγ
  have hdτA' : ∀ w ∈ Set.Icc r (r + (b - 2*r)), HasDerivAt τ (deriv τ w) w := by
    rw [heτ]; exact hdτA
  have hdτC' : ContinuousOn (deriv τ) (Set.Icc r (r + (b - 2*r))) := by
    rw [heτ]; exact hdτC
  have hqτ' : ∀ w ∈ Set.Icc r (r + (b - 2*r)),
      q (τ w) * (deriv τ w) ^ 2 = Complex.exp 0 := by
    rw [heτ, Complex.exp_zero]
    exact hqτ
  obtain ⟨hA1, -, -, -, -, -, -, -⟩ :=
    arc_piece (f := γ) (df := deriv γ) hv h3γ hdA' hdC' hqγ'
  obtain ⟨hB1, -, -, -, -, -, -, -⟩ :=
    arc_piece (f := τ) (df := deriv τ) hv h3τ hdτA' hdτC' hqτ'
  refine ⟨quarterPW_hasDerivAt_Icc (fun u hu => hA1 u hu)
      (fun u _ => (hpk₁ u).2.2.1) (fun u hu => hB1 u hu) (fun u _ => (hpk₂ u).2.2.1)
      ?hv01 ?hv12 ?hv23 ?hg01 ?hg12 ?hg23,
    ?hv01, ?hv12, ?hv23, ?hv30, ?hg01, ?hg12, ?hg23, ?hg30⟩
  case hv01 =>
    rw [hc1P0, rampArc_apply, cubicRamp_one]
    congr 1
  case hv12 =>
    rw [hc1P1, rampArc_apply, cubicRamp_zero]
  case hv23 =>
    rw [hc2P0, rampArc_apply, cubicRamp_one]
    congr 1
  case hv30 =>
    rw [hc2P1, rampArc_apply, cubicRamp_zero]
  case hg01 =>
    rw [hc1S0, rampArcSpeed_apply, cubicRampSpeed_one, cubicRamp_one,
      show (a + r) + (T - a - 2*r) = T - r from by ring]
  case hg12 =>
    rw [hc1S1, rampArcSpeed_apply, cubicRampSpeed_zero, cubicRamp_zero]
  case hg23 =>
    rw [hc2S0, rampArcSpeed_apply, cubicRampSpeed_one, cubicRamp_one,
      show r + (b - 2*r) = b - r from by ring]
  case hg30 =>
    rw [hc2S1, rampArcSpeed_apply, cubicRampSpeed_zero, cubicRamp_zero]

/-- The first offset: `exp(iπ(1-ε)) = 1` for a sign `ε`. -/
theorem exp_offset {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Complex.exp ((((1 - ε) * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  rcases hε with h | h <;> rw [h]
  · norm_num
  · rw [show (((1 - (-1:ℝ)) * Real.pi : ℝ) : ℂ) * Complex.I
        = ((1:ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I 1

/-- The wrap offset: `exp(iπ((1-ε₁) + 2ε₂)) = 1` for signs `ε₁, ε₂`. -/
theorem exp_offset₂ {ε₁ ε₂ : ℝ} (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) :
    Complex.exp (((((1 - ε₁) + 2*ε₂) * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  rcases hε₁ with h1 | h1 <;> rcases hε₂ with h2 | h2 <;> rw [h1, h2]
  · rw [show ((((1 - (1:ℝ)) + 2*1) * Real.pi : ℝ) : ℂ) * Complex.I
        = ((1:ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I 1
  · rw [show ((((1 - (1:ℝ)) + 2*(-1)) * Real.pi : ℝ) : ℂ) * Complex.I
        = ((-1:ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-1)
  · rw [show ((((1 - (-1:ℝ)) + 2*1) * Real.pi : ℝ) : ℂ) * Complex.I
        = ((2:ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I 2
  · norm_num

/-- **Corner velocity continuity**: the corner piece velocity field is continuous — the
circle numerator is continuous, the corner piece is continuous from its derivative, the
chart derivative is analytic hence continuous, and it is nonvanishing on the chart. -/
theorem cornerSpeed_continuous {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) (hqne : ∀ z ∈ S, q z ≠ 0)
    {c : ℂ} {r α ω : ℝ} (hr : 0 < r) (hω : ω ≠ 0)
    (htr : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Φ '' S) :
    Continuous (cornerSpeed Φ S c r α ω) := by
  have hpk := cornerPiece_package hS hΦ hinj hsq hqne hr hω htr
  have hκc : Continuous (cornerPiece Φ S c r α ω) :=
    continuous_iff_continuousAt.mpr fun u => ((hpk u).2.2.1).continuousAt
  have hdc : ContinuousOn (deriv Φ) S := ((hΦ.analyticOnNhd hS).deriv).continuousOn
  have hden : Continuous fun u => deriv Φ (cornerPiece Φ S c r α ω u) :=
    hdc.comp_continuous hκc fun u => (hpk u).1
  have hdne : ∀ u : ℝ, deriv Φ (cornerPiece Φ S c r α ω u) ≠ 0 := by
    intro u h0
    have h1 := hsq _ (hpk u).1
    rw [h0] at h1
    exact hqne _ (hpk u).1 (by simpa using h1.symm)
  have hnum : Continuous fun u : ℝ => (r : ℂ) * Complex.I * (ω : ℂ)
      * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (u : ℂ))) := by
    fun_prop
  exact hnum.div hden hdne

/-- **Loop composition continuity**: the quadratic differential composed with the
assembled quarter-schedule loop is continuous on the unit interval, given piecewise
continuity, junction matching, and containment in a continuity carrier. -/
theorem loop_q_continuous {q : ℂ → ℂ} {p₀ p₁ p₂ p₃ : ℝ → ℂ} {W : Set ℂ}
    (hq : ContinuousOn q W)
    (hpc₀ : ContinuousOn p₀ (Set.Icc 0 1)) (hpc₁ : ContinuousOn p₁ (Set.Icc 0 1))
    (hpc₂ : ContinuousOn p₂ (Set.Icc 0 1)) (hpc₃ : ContinuousOn p₃ (Set.Icc 0 1))
    (hv01 : p₀ 1 = p₁ 0) (hv12 : p₁ 1 = p₂ 0) (hv23 : p₂ 1 = p₃ 0)
    (hW₀ : ∀ u ∈ Set.Icc (0 : ℝ) 1, p₀ u ∈ W)
    (hW₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1, p₁ u ∈ W)
    (hW₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, p₂ u ∈ W)
    (hW₃ : ∀ u ∈ Set.Icc (0 : ℝ) 1, p₃ u ∈ W) :
    Continuous fun t : I => q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ))) := by
  have hloop := quarterPW_continuousOn_Icc hpc₀ hpc₁ hpc₂ hpc₃ hv01 hv12 hv23
  have hmaps : ∀ t ∈ Set.Icc (0:ℝ) 1, quarterPW p₀ p₁ p₂ p₃ t ∈ W := by
    intro t ht
    by_cases h0 : t ≤ 1/4
    · rw [quarterPW_eval₀ h0]
      exact hW₀ _ ⟨by linarith [ht.1], by linarith⟩
    · by_cases h1 : t ≤ 1/2
      · rw [quarterPW_eval₁ h0 h1]
        exact hW₁ _ ⟨by linarith [not_le.mp h0], by linarith⟩
      · by_cases h2 : t ≤ 3/4
        · rw [quarterPW_eval₂ h0 h1 h2]
          exact hW₂ _ ⟨by linarith [not_le.mp h1], by linarith⟩
        · rw [quarterPW_eval₃ h0 h1 h2]
          exact hW₃ _ ⟨by linarith [not_le.mp h2], by linarith [ht.2]⟩
  have hcomp : ContinuousOn (fun t => q (quarterPW p₀ p₁ p₂ p₃ t)) (Set.Icc 0 1) :=
    hq.comp hloop hmaps
  exact hcomp.comp_continuous continuous_subtype_val fun t => t.2

/-- **The rounded-bigon winding count**: for the assembled four-piece rounded bigon the
argument-principle count reads `winding(q∘ρ) + 2·winding(ρ') = m` with `2m = ε₂ - ε₁`,
for any continuity witnesses of the two winding curves. -/
theorem four_piece_count {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {a b T : ℝ}
    {S₁ S₂ : Set ℂ} {Φ₁ Φ₂ : ℂ → ℂ} {ε₁ ε₂ r r₀ α₁ ω₁ α₂ ω₂ : ℝ} {c₁ c₂ : ℂ}
    {m : ℤ}
    (hr : 0 < r) (hrr₀ : r < r₀)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hα₁ : α₁ = -(-ε₁) * (Real.pi / 2)) (hω₁ : ω₁ = 1 * (-ε₁) * (Real.pi / 2))
    (hα₂ : α₂ = -ε₂ * Real.pi) (hω₂ : ω₂ = ε₂ * (Real.pi / 2))
    (hc₁ : c₁ = Φ₁ (γ T) - ((1 : ℝ) : ℂ) * r + Complex.I * ((-ε₁ : ℝ) : ℂ) * r)
    (hc₂ : c₂ = Φ₂ (γ a) - ((-1 : ℝ) : ℂ) * r + Complex.I * (ε₂ : ℂ) * r)
    (hm : 2 * (m : ℝ) = ε₂ - ε₁)
    (h3γ : r * (Real.pi / 2) < 3 * (T - a - 2 * r))
    (h3τ : r * (Real.pi / 2) < 3 * (b - 2 * r))
    (hS₁o : IsOpen S₁) (hΦ₁d : DifferentiableOn ℂ Φ₁ S₁) (hΦ₁inj : Set.InjOn Φ₁ S₁)
    (hΦ₁sq : ∀ z ∈ S₁, deriv Φ₁ z ^ 2 = -q z) (hq₁ne : ∀ z ∈ S₁, q z ≠ 0)
    (hS₂o : IsOpen S₂) (hΦ₂d : DifferentiableOn ℂ Φ₂ S₂) (hΦ₂inj : Set.InjOn Φ₂ S₂)
    (hΦ₂sq : ∀ z ∈ S₂, deriv Φ₂ z ^ 2 = -q z) (hq₂ne : ∀ z ∈ S₂, q z ≠ 0)
    (hball₁ : Metric.ball (Φ₁ (γ T)) (4 * r₀) ⊆ Φ₁ '' S₁)
    (hball₂ : Metric.ball (Φ₂ (γ a)) (4 * r₀) ⊆ Φ₂ '' S₂)
    (hdevγ₁ : ∀ u ∈ Set.Icc (T - r₀) (T + r₀),
      γ u ∈ S₁ ∧ Φ₁ (γ u) = Φ₁ (γ T) + ((u - T : ℝ) : ℂ))
    (hdevτ₁ : ∀ v ∈ Set.Icc (-r₀) r₀,
      τ v ∈ S₁ ∧ Φ₁ (τ v) = Φ₁ (γ T) - Complex.I * ε₁ * ((v : ℝ) : ℂ))
    (hdevγ₂ : ∀ u ∈ Set.Icc (a - r₀) (a + r₀),
      γ u ∈ S₂ ∧ Φ₂ (γ u) = Φ₂ (γ a) + ((u - a : ℝ) : ℂ))
    (hdevτ₂ : ∀ v ∈ Set.Icc (b - r₀) (b + r₀),
      τ v ∈ S₂ ∧ Φ₂ (τ v) = Φ₂ (γ a) - Complex.I * ε₂ * ((v - b : ℝ) : ℂ))
    (hdγA : ∀ w ∈ Set.Icc (a + r) (T - r), HasDerivAt γ (deriv γ w) w)
    (hdγC : ContinuousOn (deriv γ) (Set.Icc (a + r) (T - r)))
    (hqγ : ∀ w ∈ Set.Icc (a + r) (T - r), q (γ w) * (deriv γ w) ^ 2 = -1)
    (hdτA : ∀ w ∈ Set.Icc r (b - r), HasDerivAt τ (deriv τ w) w)
    (hdτC : ContinuousOn (deriv τ) (Set.Icc r (b - r)))
    (hqτ : ∀ w ∈ Set.Icc r (b - r), q (τ w) * (deriv τ w) ^ 2 = 1) :
    ∀ (hqc : Continuous fun t : I => q (quarterPW
        (rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
        (cornerPiece Φ₁ S₁ c₁ r α₁ ω₁)
        (rampArc τ r (r * (Real.pi/2)) (b - 2*r))
        (cornerPiece Φ₂ S₂ c₂ r α₂ ω₂) ((t : ℝ))))
      (hgc : Continuous fun t : I => 4 * quarterPW
        (rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
        (cornerSpeed Φ₁ S₁ c₁ r α₁ ω₁)
        (rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
        (cornerSpeed Φ₂ S₂ c₂ r α₂ ω₂) ((t : ℝ))),
      windingNumber ⟨_, hqc⟩ 0 + 2 * windingNumber ⟨_, hgc⟩ 0 = m := by
  subst hc₁
  subst hc₂
  intro hqc hgc
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hv : (0:ℝ) < r * (Real.pi/2) := mul_pos hr (by linarith)
  have haT : a + r ≤ T - r := by nlinarith
  have hrb : r ≤ b - r := by nlinarith
  obtain ⟨-, -, -, -, hv30, hg01, hg12, hg23, hg30⟩ :=
    four_piece_bundle hr hrr₀ hε₁ hε₂ hα₁ hω₁ hα₂ hω₂ rfl rfl h3γ h3τ
      hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hball₁ hball₂
      hdevγ₁ hdevτ₁ hdevγ₂ hdevτ₂ hdγA hdγC hqγ hdτA hdτC hqτ
  obtain ⟨-, -, -, -, hc1tr⟩ :=
    corner1_seams hr hrr₀ hε₁ hα₁ hω₁ hS₁o hΦ₁d hΦ₁inj hball₁ hdevγ₁ hdevτ₁
      (hdγA (T - r) ⟨haT, le_refl _⟩) (hdτA r ⟨le_refl _, hrb⟩)
  obtain ⟨-, -, -, -, hc2tr⟩ :=
    corner2_seams hr hrr₀ hε₂ hα₂ hω₂ hS₂o hΦ₂d hΦ₂inj hball₂ hdevγ₂ hdevτ₂
      (hdγA (a + r) ⟨le_refl _, haT⟩) (hdτA (b - r) ⟨hrb, le_refl _⟩)
  have hω₁ne : ω₁ ≠ 0 := by
    rw [hω₁]
    rcases hε₁ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hω₂ne : ω₂ ≠ 0 := by
    rw [hω₂]
    rcases hε₂ with h | h <;> rw [h] <;> norm_num [Real.pi_ne_zero]
  have hpk₁ := cornerPiece_package hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne hc1tr
  have hpk₂ := cornerPiece_package hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne hc2tr
  have heγ : (a + r) + (T - a - 2*r) = T - r := by ring
  have heτ : r + (b - 2*r) = b - r := by ring
  have hdA' : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      HasDerivAt γ (deriv γ w) w := by
    rw [heγ]; exact hdγA
  have hdC' : ContinuousOn (deriv γ) (Set.Icc (a + r) ((a + r) + (T - a - 2*r))) := by
    rw [heγ]; exact hdγC
  have hqγ' : ∀ w ∈ Set.Icc (a + r) ((a + r) + (T - a - 2*r)),
      q (γ w) * (deriv γ w) ^ 2 = Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [heγ, Complex.exp_pi_mul_I]
    exact hqγ
  have hdτA' : ∀ w ∈ Set.Icc r (r + (b - 2*r)), HasDerivAt τ (deriv τ w) w := by
    rw [heτ]; exact hdτA
  have hdτC' : ContinuousOn (deriv τ) (Set.Icc r (r + (b - 2*r))) := by
    rw [heτ]; exact hdτC
  have hqτ' : ∀ w ∈ Set.Icc r (r + (b - 2*r)),
      q (τ w) * (deriv τ w) ^ 2
        = Complex.exp ((((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [heτ, exp_offset hε₁]
    exact hqτ
  obtain ⟨-, -, -, -, -, hA6, hA7, hA8⟩ :=
    arc_piece (f := γ) (df := deriv γ) hv h3γ hdA' hdC' hqγ'
  obtain ⟨-, -, -, -, -, hB6, hB7, hB8⟩ :=
    arc_piece (f := τ) (df := deriv τ) hv h3τ hdτA' hdτC' hqτ'
  have hgc₁c : ContinuousOn (cornerSpeed Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁)
      (Set.Icc 0 1) :=
    (cornerSpeed_continuous hS₁o hΦ₁d hΦ₁inj hΦ₁sq hq₁ne hr hω₁ne
      hc1tr).continuousOn
  have hgc₃c : ContinuousOn (cornerSpeed Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂)
      (Set.Icc 0 1) :=
    (cornerSpeed_continuous hS₂o hΦ₂d hΦ₂inj hΦ₂sq hq₂ne hr hω₂ne
      hc2tr).continuousOn
  have hLc₁ : ContinuousOn (fun u : ℝ => ((Real.log (r^2*ω₁^2) : ℝ) : ℂ)
      + 2*Complex.I*((α₁ : ℂ) + (ω₁ : ℂ)*u)
      + (((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I) (Set.Icc 0 1) :=
    Continuous.continuousOn (by fun_prop)
  have hLc₃ : ContinuousOn (fun u : ℝ => ((Real.log (r^2*ω₂^2) : ℝ) : ℂ)
      + 2*Complex.I*((α₂ : ℂ) + (ω₂ : ℂ)*u)
      + ((((1 - ε₁) + 2*ε₂) * Real.pi : ℝ) : ℂ) * Complex.I) (Set.Icc 0 1) :=
    Continuous.continuousOn (by fun_prop)
  have hcl0 : max 0 (min 1 (0:ℝ)) = 0 := by norm_num
  have hcl1 : max 0 (min 1 (1:ℝ)) = 1 := by norm_num
  have hlog₁ : Real.log ((r * (Real.pi/2))^2) = Real.log (r^2*ω₁^2) := by
    rw [hω₁]
    rcases hε₁ with h | h <;> rw [h] <;> congr 1 <;> ring
  have hlog₂ : Real.log ((r * (Real.pi/2))^2) = Real.log (r^2*ω₂^2) := by
    rw [hω₂]
    rcases hε₂ with h | h <;> rw [h] <;> congr 1 <;> ring
  have hL01 : ((Real.log ((cubicRampSpeed (r * (Real.pi/2)) (T - a - 2*r)
        (max 0 (min 1 (1:ℝ))))^2) : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I
      = ((Real.log (r^2*ω₁^2) : ℝ) : ℂ)
        + 2*Complex.I*((α₁ : ℂ) + (ω₁ : ℂ)*((0:ℝ) : ℂ))
        + (((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [hcl1, cubicRampSpeed_one, hlog₁, hα₁]
    push_cast
    ring
  have hL12 : ((Real.log (r^2*ω₁^2) : ℝ) : ℂ)
        + 2*Complex.I*((α₁ : ℂ) + (ω₁ : ℂ)*((1:ℝ) : ℂ))
        + (((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I
      = ((Real.log ((cubicRampSpeed (r * (Real.pi/2)) (b - 2*r)
          (max 0 (min 1 (0:ℝ))))^2) : ℝ) : ℂ)
        + (((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [hcl0, cubicRampSpeed_zero, hlog₁, hα₁, hω₁]
    push_cast
    ring
  have hL23 : ((Real.log ((cubicRampSpeed (r * (Real.pi/2)) (b - 2*r)
        (max 0 (min 1 (1:ℝ))))^2) : ℝ) : ℂ)
        + (((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I
      = ((Real.log (r^2*ω₂^2) : ℝ) : ℂ)
        + 2*Complex.I*((α₂ : ℂ) + (ω₂ : ℂ)*((0:ℝ) : ℂ))
        + ((((1 - ε₁) + 2*ε₂) * Real.pi : ℝ) : ℂ) * Complex.I := by
    rw [hcl1, cubicRampSpeed_one, hlog₂, hα₂]
    push_cast
    ring
  have hLm : (((Real.log (r^2*ω₂^2) : ℝ) : ℂ)
        + 2*Complex.I*((α₂ : ℂ) + (ω₂ : ℂ)*((1:ℝ) : ℂ))
        + ((((1 - ε₁) + 2*ε₂) * Real.pi : ℝ) : ℂ) * Complex.I)
      - (((Real.log ((cubicRampSpeed (r * (Real.pi/2)) (T - a - 2*r)
          (max 0 (min 1 (0:ℝ))))^2) : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I)
      = 2 * Real.pi * Complex.I * m := by
    have hmC : 2 * (m : ℂ) = (ε₂ : ℂ) - (ε₁ : ℂ) := by exact_mod_cast hm
    rw [hcl0, cubicRampSpeed_zero, hlog₂, hα₂, hω₂]
    push_cast
    linear_combination (-(Real.pi : ℂ)) * Complex.I * hmC
  have hexp₁ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      q (cornerPiece Φ₁ S₁ (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
          r α₁ ω₁ u)
        * cornerSpeed Φ₁ S₁ (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r)
          r α₁ ω₁ u ^ 2
      = Complex.exp (((Real.log (r^2*ω₁^2) : ℝ) : ℂ)
          + 2*Complex.I*((α₁ : ℂ) + (ω₁ : ℂ)*u)
          + (((1 - ε₁) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    intro u _
    rw [Complex.exp_add, exp_offset hε₁, mul_one]
    exact (hpk₁ u).2.2.2
  have hexp₃ : ∀ u ∈ Set.Icc (0:ℝ) 1,
      q (cornerPiece Φ₂ S₂ (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
          r α₂ ω₂ u)
        * cornerSpeed Φ₂ S₂ (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r)
          r α₂ ω₂ u ^ 2
      = Complex.exp (((Real.log (r^2*ω₂^2) : ℝ) : ℂ)
          + 2*Complex.I*((α₂ : ℂ) + (ω₂ : ℂ)*u)
          + ((((1 - ε₁) + 2*ε₂) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    intro u _
    rw [Complex.exp_add, exp_offset₂ hε₁ hε₂, mul_one]
    exact (hpk₂ u).2.2.2
  exact rounded_count_Icc (q := q)
    (p₀ := rampArc γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
    (p₁ := cornerPiece Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁)
    (p₂ := rampArc τ r (r * (Real.pi/2)) (b - 2*r))
    (p₃ := cornerPiece Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂)
    (g₀ := rampArcSpeed γ (a + r) (r * (Real.pi/2)) (T - a - 2*r))
    (g₁ := cornerSpeed Φ₁ S₁
      (Φ₁ (γ T) - ((1:ℝ) : ℂ)*r + Complex.I*((-ε₁ : ℝ) : ℂ)*r) r α₁ ω₁)
    (g₂ := rampArcSpeed τ r (r * (Real.pi/2)) (b - 2*r))
    (g₃ := cornerSpeed Φ₂ S₂
      (Φ₂ (γ a) - ((-1:ℝ) : ℂ)*r + Complex.I*(ε₂ : ℂ)*r) r α₂ ω₂)
    (m := m)
    hA7 hgc₁c hB7 hgc₃c hA8.continuousOn hLc₁ hB8.continuousOn hLc₃
    hv30 hg01 hg12 hg23 hg30 hL01 hL12 hL23 hLm
    hA6 hexp₁ hB6 hexp₃ hqc

/-- The parametrized circle exponential in rectangular form. -/
theorem exp_circle (θ : ℝ) :
    Complex.exp (Complex.I * ((θ : ℝ) : ℂ))
      = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **Ramped-arc injectivity**: the cubic-ramp reparametrization of an injective arc is
injective on the unit interval. -/
theorem rampArc_injOn {f : ℝ → ℂ} {c v L : ℝ} (hv : 0 < v) (h3 : v < 3 * L)
    (hinj : Set.InjOn f (Set.Icc c (c + L))) :
    Set.InjOn (rampArc f c v L) (Set.Icc 0 1) := by
  intro s hs t ht heq
  have h1 := hinj (cubicRamp_mapsTo hv h3 s hs) (cubicRamp_mapsTo hv h3 t ht) heq
  exact (cubicRamp_strictMono hv h3).injOn hs ht h1

/-- **Corner-piece injectivity**: a corner piece with phase speed below a full turn is
injective on the unit interval. -/
theorem cornerPiece_injOn {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) (hqne : ∀ z ∈ S, q z ≠ 0)
    {c : ℂ} {r α ω : ℝ} (hr : 0 < r) (hω : ω ≠ 0)
    (htr : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Φ '' S)
    (hω2 : |ω| < 2 * Real.pi) :
    Set.InjOn (cornerPiece Φ S c r α ω) (Set.Icc 0 1) := by
  intro s hs t ht heq
  have h1 := (cornerPiece_package hS hΦ hinj hsq hqne hr hω htr s).2.1
  have h2 := (cornerPiece_package hS hΦ hinj hsq hqne hr hω htr t).2.1
  rw [heq, h2] at h1
  have h3 : Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ)))
      = Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (s : ℂ))) :=
    mul_left_cancel₀ (by exact_mod_cast hr.ne') (add_left_cancel h1)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h3
  have h4 : Complex.I * ((ω * (t - s) : ℝ) : ℂ)
      = Complex.I * ((n * (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    linear_combination hn
  have h5 : ω * (t - s) = n * (2 * Real.pi) :=
    Complex.ofReal_injective (mul_left_cancel₀ Complex.I_ne_zero h4)
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h6 : |ω * (t - s)| < 2 * Real.pi := by
    rw [abs_mul]
    rcases eq_or_lt_of_le (abs_nonneg (t - s)) with h | h
    · rw [← h, mul_zero]; linarith
    · have h7 : |t - s| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
      nlinarith [abs_nonneg ω]
  have h8 : n = 0 := by
    rcases lt_trichotomy n 0 with h | h | h
    · have h9 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      rw [h5, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)] at h6
      nlinarith [abs_nonneg (n : ℝ), le_abs_self (-(n:ℝ)), neg_le_abs (n : ℝ)]
    · exact h
    · have h9 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      rw [h5, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)] at h6
      nlinarith [le_abs_self (n : ℝ)]
  rw [h8] at h5
  have h10 : t = s := by
    rcases (by simpa using h5 : ω = 0 ∨ t - s = 0) with h | h
    · exact absurd h hω
    · linarith [sub_eq_zero.mp h]
  rw [h10]

/-- **Sine pinning**: on `[0, π]` the sine reaches `1` only at `π/2`. -/
theorem sin_pin {φ : ℝ} (h0 : 0 ≤ φ) (h2 : φ ≤ Real.pi)
    (hs : Real.sin φ = 1) : φ = Real.pi/2 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.mp hs
  have hb1 : (-1:ℝ) < (k:ℝ) := by nlinarith
  have hb2 : (k:ℝ) < 1 := by nlinarith
  have hk0 : k = 0 := by
    have h3 : (-1:ℤ) < k := by exact_mod_cast hb1
    have h4 : k < 1 := by exact_mod_cast hb2
    omega
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- **Cosine pinning at one**: on `[-π/2, π/2]` the cosine reaches `1` only at `0`. -/
theorem cos_pin {φ : ℝ} (h1 : -(Real.pi / 2) ≤ φ) (h2 : φ ≤ Real.pi / 2)
    (hc : Real.cos φ = 1) : φ = 0 := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hc

/-- **Cosine pinning at minus one**: on `[-π, π]` the cosine reaches `-1` only at
`±π`. -/
theorem cos_neg_pin {φ : ℝ} (h1 : -Real.pi ≤ φ) (h2 : φ ≤ Real.pi)
    (hc : Real.cos φ = -1) : φ = Real.pi ∨ φ = -Real.pi := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hc
  have hb1 : (-1:ℝ) ≤ (k:ℝ) := by nlinarith
  have hb2 : (k:ℝ) ≤ 0 := by nlinarith
  have hbi : k = -1 ∨ k = 0 := by
    have h3 : (-1:ℤ) ≤ k := by exact_mod_cast hb1
    have h4 : k ≤ 0 := by exact_mod_cast hb2
    omega
  rcases hbi with h | h <;> rw [h] at hk <;> push_cast at hk
  · right; linarith
  · left; linarith

/-- A real number equal to `I` times a real number forces both to vanish. -/
theorem real_eq_I_mul {x y : ℝ}
    (h : ((x : ℝ) : ℂ) = Complex.I * ((y : ℝ) : ℂ)) : x = 0 ∧ y = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  constructor <;> linarith

/-- **First-corner horizontal pinning**: a point of the first corner circle with purely
real chart increment is the horizontal junction. -/
theorem corner1_horiz {ε₁ r α ω t X : ℝ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hr : 0 < r)
    (hα : α = -(-ε₁) * (Real.pi / 2)) (hω : ω = 1 * (-ε₁) * (Real.pi / 2))
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (heq : ((X : ℝ) : ℂ) = -((1 : ℝ) : ℂ) * r + Complex.I * ((-ε₁ : ℝ) : ℂ) * r
      + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ)))) :
    t = 0 ∧ X = -r := by
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hph : Complex.I * ((α : ℂ) + (ω : ℂ) * (t : ℂ))
      = Complex.I * ((α + ω * t : ℝ) : ℂ) := by push_cast; ring
  rw [hph, exp_circle] at heq
  push_cast at heq
  have hkey : ((X - (-r + r * Real.cos (α + ω*t)) : ℝ) : ℂ)
      = Complex.I * ((-ε₁*r + r * Real.sin (α + ω*t) : ℝ) : ℂ) := by
    push_cast
    linear_combination heq
  obtain ⟨hre0, him0⟩ := real_eq_I_mul hkey
  have hsin : Real.sin (α + ω*t) = ε₁ := by
    have h1 : r * Real.sin (α + ω*t) = r * ε₁ := by linarith
    exact mul_left_cancel₀ hr.ne' h1
  have hφ : α + ω * t = ε₁ * ((1 - t) * (Real.pi/2)) := by rw [hα, hω]; ring
  have ht0 : t = 0 := by
    rcases hε₁ with h | h
    · rw [hφ, h, one_mul] at hsin
      have hp := sin_pin (by nlinarith [ht.1, ht.2]) (by nlinarith [ht.1, ht.2])
        hsin
      have h2 : t * (Real.pi/2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exfalso; linarith
    · rw [hφ, h, show ((-1:ℝ)) * ((1 - t) * (Real.pi/2))
          = -((1 - t) * (Real.pi/2)) by ring, Real.sin_neg] at hsin
      have hsin' : Real.sin ((1 - t) * (Real.pi/2)) = 1 := by linarith
      have hp := sin_pin (by nlinarith [ht.1, ht.2]) (by nlinarith [ht.1, ht.2])
        hsin'
      have h2 : t * (Real.pi/2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exfalso; linarith
  refine ⟨ht0, ?_⟩
  rw [hφ, ht0] at hre0
  have hcos : Real.cos (ε₁ * ((1 - 0) * (Real.pi/2))) = 0 := by
    rcases hε₁ with h | h <;> rw [h]
    · rw [show (1:ℝ) * ((1 - 0) * (Real.pi/2)) = Real.pi/2 by ring]
      exact Real.cos_pi_div_two
    · rw [show ((-1:ℝ)) * ((1 - 0) * (Real.pi/2)) = -(Real.pi/2) by ring,
        Real.cos_neg]
      exact Real.cos_pi_div_two
  rw [hcos] at hre0
  linarith

end WindingBricks

end RiemannDynamics
