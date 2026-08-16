/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Flow.Itinerary

/-!
# Measurable trajectory selection and the dying set

A measurable selection of trajectories, the window estimates near a zero, and the bound
showing that the set of start points whose trajectory dies in finite time is null.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

/-- **Junction glue of trajectory units**: two trajectories meeting at a point with the
same signed slope in one chart concatenate to a trajectory. -/
theorem traj_glue_units {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦd : DifferentiableOn ℂ Φ S) (hΦinj : Set.InjOn Φ S)
    (hSH : S ⊆ {z : ℂ | 0 < z.im}) (hSne : ∀ w ∈ S, q w ≠ 0)
    (hΦsq : ∀ w ∈ S, deriv Φ w ^ 2 = -q w)
    {σ τ : ℝ → ℂ} {b δ : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ)
    (hσ : IsTrajOn q σ (Set.Icc 0 b)) (hτ : IsTrajOn q τ (Set.Icc 0 δ))
    (hmatch : τ 0 = σ b) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hσarr : SlopeAt Φ σ (Set.Icc 0 b) b s)
    (hτ0 : SlopeAt Φ τ (Set.Icc 0 δ) 0 s) (hσbS : σ b ∈ S) :
    ∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Icc 0 b) ∧
      (∀ u ∈ Set.Icc b (b + δ), σ' u = τ (u - b)) ∧
      IsTrajOn q σ' (Set.Icc 0 (b + δ)) := by
  classical
  set σ' : ℝ → ℂ := fun u => if u ≤ b then σ u else τ (u - b) with hσ'def
  have hEq : Set.EqOn σ' σ (Set.Icc 0 b) := fun u hu => if_pos hu.2
  have hσ'b : σ' b = σ b := if_pos le_rfl
  have hEqR : ∀ u ∈ Set.Icc b (b + δ), σ' u = τ (u - b) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with heq | hlt
    · rw [← heq, hσ'b, show b - b = (0 : ℝ) by ring, hmatch]
    · exact if_neg (not_le.mpr hlt)
  have hshift : ∀ t : ℝ, Filter.Tendsto (fun u : ℝ => u - b)
      (nhdsWithin t (Set.Icc b (b + δ))) (nhdsWithin (t - b) (Set.Icc 0 δ)) := by
    intro t
    refine Filter.Tendsto.inf ?_ ?_
    · exact (continuous_id.sub continuous_const).tendsto t
    · refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hτ0S : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 δ), τ v ∈ S := by
    have h0mem : (0 : ℝ) ∈ Set.Icc 0 δ := Set.left_mem_Icc.mpr hδ.le
    exact (hτ.cont 0 h0mem) (hmatch ▸ hS.mem_nhds hσbS)
  have hσbS' : ∀ᶠ u in nhdsWithin b (Set.Icc 0 b), σ u ∈ S := by
    have hbmem : b ∈ Set.Icc 0 b := Set.right_mem_Icc.mpr hb
    exact (hσ.cont b hbmem) (hS.mem_nhds hσbS)
  refine ⟨σ', hEq, hEqR, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (b + δ))) (nhds (σ' t))
      rw [nhdsWithin_left (by linarith) htb, hEq ⟨ht.1, htb.le⟩]
      exact Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
        (hσ.cont t ⟨ht.1, htb.le⟩)
    · subst heq
      change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (t + δ))) (nhds (σ' t))
      rw [nhdsWithin_split hb hδ.le, Filter.tendsto_sup]
      constructor
      · rw [hσ'b]
        exact Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEq hu).symm)
          (hσ.cont t (Set.right_mem_Icc.mpr hb))
      · rw [hσ'b, ← hmatch]
        refine Filter.Tendsto.congr'
          (eventually_mem_nhdsWithin.mono fun u hu => (hEqR u hu).symm) ?_
        have h0mem : (0 : ℝ) ∈ Set.Icc 0 δ := Set.left_mem_Icc.mpr hδ.le
        have hsh := hshift t
        rw [sub_self] at hsh
        exact Filter.Tendsto.comp (hτ.cont 0 h0mem) hsh
    · change Filter.Tendsto σ' (nhdsWithin t (Set.Icc 0 (b + δ))) (nhds (σ' t))
      have htmem : t - b ∈ Set.Icc 0 δ := ⟨by linarith, by linarith [ht.2]⟩
      rw [nhdsWithin_right hb htb, hEqR t ⟨htb.le, ht.2⟩]
      exact Filter.Tendsto.congr'
        (eventually_mem_nhdsWithin.mono fun u hu => (hEqR u hu).symm)
        (Filter.Tendsto.comp (hτ.cont (t - b) htmem) (hshift t))
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hσ.chart t ⟨ht.1, htb.le⟩
      refine ⟨Ut, hUto, by rw [hEq ⟨ht.1, htb.le⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_left (by linarith) htb]
      filter_upwards [hevt, eventually_mem_nhdsWithin] with u hu huIcc
      rw [hEq huIcc, hEq ⟨ht.1, htb.le⟩]
      exact hu
    · subst heq
      have hsne : ((s : ℝ) : ℂ) ≠ 0 := by
        rcases hs with h1 | h1 <;> rw [h1] <;> norm_num
      have hs2 : ((s : ℝ) : ℂ) ^ 2 = 1 := by
        rcases hs with h1 | h1 <;> rw [h1] <;> norm_num
      refine ⟨S, hS, by rw [hσ'b]; exact hσbS, hSH, hSne,
        fun w => ((s : ℝ) : ℂ) * Φ w, fun w hw => ((hΦd w hw).const_mul _),
        ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        exact hΦinj hx hy (mul_left_cancel₀ hsne hxy)
      · intro w hw
        have hdiff : DifferentiableAt ℂ Φ w := hΦd.differentiableAt (hS.mem_nhds hw)
        rw [deriv_const_mul _ hdiff, mul_pow, hs2, one_mul]
        exact hΦsq w hw
      · rw [nhdsWithin_split hb hδ.le, Filter.eventually_sup]
        constructor
        · filter_upwards [hσarr, hσbS', eventually_mem_nhdsWithin] with u hu hSu huIcc
          rw [hEq huIcc, hσ'b]
          refine ⟨hSu, ?_⟩
          show ((s : ℝ) : ℂ) * Φ (σ u) = ((s : ℝ) : ℂ) * Φ (σ t) + _
          rw [hu]
          push_cast
          rcases hs with h1 | h1 <;> rw [h1] <;> push_cast <;> ring
        · have hsh := hshift t
          rw [sub_self] at hsh
          filter_upwards [hsh.eventually hτ0, hsh.eventually hτ0S,
            eventually_mem_nhdsWithin] with u hu hSu huIcc
          rw [hEqR u huIcc, hσ'b]
          refine ⟨hSu, ?_⟩
          show ((s : ℝ) : ℂ) * Φ (τ (u - t)) = ((s : ℝ) : ℂ) * Φ (σ t) + _
          rw [hu, hmatch]
          push_cast
          rcases hs with h1 | h1 <;> rw [h1] <;> push_cast <;> ring
    · have htmem : t - b ∈ Set.Icc 0 δ := ⟨by linarith, by linarith [ht.2]⟩
      obtain ⟨Ut, hUto, hptU, hUtH, hUtne, Φt, hΦtd, hΦtinj, hΦtsq, hevt⟩ :=
        hτ.chart (t - b) htmem
      refine ⟨Ut, hUto, by rw [hEqR t ⟨htb.le, ht.2⟩]; exact hptU, hUtH, hUtne,
        Φt, hΦtd, hΦtinj, hΦtsq, ?_⟩
      rw [nhdsWithin_right hb htb]
      filter_upwards [(hshift t).eventually hevt, eventually_mem_nhdsWithin]
        with u hu huIcc
      rw [hEqR u huIcc, hEqR t ⟨htb.le, ht.2⟩]
      refine ⟨hu.1, ?_⟩
      rw [hu.2]
      congr 1
      push_cast
      ring

/-- Slope transfer through the right piece of a glued curve. -/
theorem slope_glue_shift {Φ : ℂ → ℂ} {σ' τ : ℝ → ℂ} {b δ s : ℝ}
    (hb : 0 ≤ b) (hδ : 0 < δ)
    (hR : ∀ u ∈ Set.Icc b (b + δ), σ' u = τ (u - b))
    (hτ : SlopeAt Φ τ (Set.Icc 0 δ) δ s) :
    SlopeAt Φ σ' (Set.Icc 0 (b + δ)) (b + δ) s := by
  have hshift : Filter.Tendsto (fun u : ℝ => u - b)
      (nhdsWithin (b + δ) (Set.Icc b (b + δ))) (nhdsWithin δ (Set.Icc 0 δ)) := by
    refine Filter.Tendsto.inf ?_ ?_
    · have h1 : Continuous fun u : ℝ => u - b := continuous_id.sub continuous_const
      have h2 := h1.tendsto (b + δ)
      simpa using h2
    · refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  change ∀ᶠ u in nhdsWithin (b + δ) (Set.Icc 0 (b + δ)),
    Φ (σ' u) = Φ (σ' (b + δ)) + s * ((u - (b + δ) : ℝ) : ℂ)
  rw [nhdsWithin_right hb (by linarith : b < b + δ)]
  filter_upwards [hshift.eventually hτ, eventually_mem_nhdsWithin] with u hu huI
  rw [hR u huI, hR (b + δ) (Set.right_mem_Icc.mpr (by linarith)),
    show b + δ - b = δ by ring, hu]
  congr 1
  push_cast
  ring

/-- **Strong-legal runs are trajectories**: a strong-legal point carries a slope-one
trajectory over the whole run window ending at the final stepper position with the
final stepper sign as arrival slope. -/
theorem slegal_traj {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 < h) :
    ∀ N : ℕ, ∀ z, z ∈ slegal A h N →
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h)) 0 1 ∧
      SlopeAt (A.Φ (A.sel (pos A h (N + 1) z))) σ
        (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h)) (((N + 1 : ℕ) : ℝ) * h)
        (sgn A h (N + 1) z) ∧
      σ (((N + 1 : ℕ) : ℝ) * h) = pos A h (N + 1) z := by
  intro N
  induction N with
  | zero =>
    intro z hz
    obtain ⟨hact, hball, hsgn, hseg⟩ := hz 0 (le_refl 0)
    obtain ⟨τ, hτ0, hτtraj, hτslope, hτh, hpm, hτarr⟩ :=
      slegal_step A hh hact hball hsgn hseg
    have hcast : (((0 + 1 : ℕ) : ℝ)) * h = h := by norm_num
    rw [hcast]
    exact ⟨τ, hτ0, hτtraj, hτslope, hτarr, hτh⟩
  | succ N ih =>
    intro z hz
    have hzN : z ∈ slegal A h N := fun k hk => hz k (by omega)
    obtain ⟨σ, hσ0, hσtraj, hσslope, hσarr, hσend⟩ := ih z hzN
    obtain ⟨hact, hball, hsgn, hseg⟩ := hz (N + 1) (le_refl _)
    obtain ⟨τ, hτ0, hτtraj, hτslope, hτh, hpm, hτarr⟩ :=
      slegal_step A hh hact hball hsgn hseg
    set b : ℝ := ((N + 1 : ℕ) : ℝ) * h with hbdef
    have hb : 0 ≤ b := by positivity
    have hmatch : τ 0 = σ b := by rw [hτ0, hσend]
    have hσbS : σ b ∈ Metric.ball (A.c (A.sel (pos A h (N + 1) z)))
        (2 * A.r (A.sel (pos A h (N + 1) z))) := by
      rw [hσend]
      exact Metric.ball_subset_ball (by linarith [A.hr _ hact]) hball
    have hσarr' : SlopeAt (A.Φ (A.sel (pos A h (N + 1) z))) σ (Set.Icc 0 b) b
        (sgn A h (N + 1) z) := hσarr
    obtain ⟨σ', hEqL, hEqR, hσ'traj⟩ := traj_glue_units Metric.isOpen_ball
      (A.hd _ hact) (A.hinj _ hact) (A.hH _ hact) (A.hne _ hact) (A.hsq _ hact)
      hb hh hσtraj hτtraj hmatch hsgn hσarr' hτslope hσbS
    have hcast : (((N + 1 + 1 : ℕ) : ℝ)) * h = b + h := by
      rw [hbdef]
      push_cast
      ring
    rw [hcast]
    have hb0 : 0 < b := by
      rw [hbdef]
      have : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      positivity
    refine ⟨σ', ?_, hσ'traj, ?_, ?_, ?_⟩
    · rw [hEqL (Set.left_mem_Icc.mpr hb), hσ0]
    · change ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 (b + h)),
        A.Φ (A.sel z) (σ' u) = A.Φ (A.sel z) (σ' 0) + 1 * ((u - 0 : ℝ) : ℂ)
      rw [nhdsWithin_left (by linarith : b ≤ b + h) hb0]
      have hσ'0 : σ' 0 = σ 0 := hEqL (Set.left_mem_Icc.mpr hb)
      filter_upwards [hσslope, eventually_mem_nhdsWithin] with u hu huI
      rw [hEqL huI, hσ'0]
      exact hu
    · exact slope_glue_shift hb hh hEqR hτarr
    · rw [hEqR (b + h) (Set.right_mem_Icc.mpr (by linarith)),
        show b + h - b = h by ring, hτh]

/-- Two chart slopes of the same curve at the same accumulating time agree. -/
theorem slope_eq {Φ : ℂ → ℂ} {σ : ℝ → ℂ} {I : Set ℝ} {u s₁ s₂ : ℝ}
    [hne : (nhdsWithin u (I \ {u})).NeBot]
    (h₁ : SlopeAt Φ σ I u s₁) (h₂ : SlopeAt Φ σ I u s₂) : s₁ = s₂ := by
  have hmono : nhdsWithin u (I \ {u}) ≤ nhdsWithin u I :=
    nhdsWithin_mono u Set.sdiff_subset
  obtain ⟨v, hv, e₁, e₂⟩ := (eventually_mem_nhdsWithin.and
    ((h₁.filter_mono hmono).and (h₂.filter_mono hmono))).exists
  have hvne : ((v - u : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ?_)
    intro hvu
    exact hv.2 (hvu ▸ rfl)
  have hmul : (s₁ : ℂ) * ((v - u : ℝ) : ℂ) = s₂ * ((v - u : ℝ) : ℂ) := by
    have := e₁.symm.trans e₂
    linear_combination this
  exact_mod_cast mul_right_cancel₀ hvne hmul

/-- **From strong legality to trajectories**: the backward inclusion of the existence
characterization. -/
theorem traj_of_slegal {q : ℂ → ℂ} (A : Atlas q) {T : ℝ} (hT : 0 < T)
    {z : ℂ} {N : ℕ} (hz : z ∈ slegal A (T / (N + 1)) N) :
    ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1 := by
  have hh : 0 < T / (N + 1) := by positivity
  obtain ⟨σ, hσ0, hσtraj, hσslope, -, -⟩ := slegal_traj A hh N z hz
  have hcast : (((N + 1 : ℕ) : ℝ)) * (T / (N + 1)) = T := by
    push_cast
    field_simp
  rw [hcast] at hσtraj hσslope
  exact ⟨σ, hσ0, hσtraj, hσslope⟩

/-- **From trajectories to strong legality**: the forward inclusion of the existence
characterization. -/
theorem slegal_of_traj {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {T : ℝ}
    (hT : 0 < T) {σ : ℝ → ℂ} (hσ : IsTrajOn q σ (Set.Icc 0 T))
    (hslope0 : SlopeAt (A.Φ (A.sel (σ 0))) σ (Set.Icc 0 T) 0 1) :
    ∃ N : ℕ, σ 0 ∈ slegal A (T / (N + 1)) N := by
  have hreg : ∀ v ∈ Set.Icc 0 T, 0 < (σ v).im ∧ q (σ v) ≠ 0 := fun v hv =>
    traj_regular hσ hv
  have hqcont : ContinuousOn (fun v => ‖q (σ v)‖) (Set.Icc 0 T) := by
    refine ContinuousOn.norm (hq.continuousOn.comp hσ.cont ?_)
    exact fun v hv => (hreg v hv).1
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, Set.left_mem_Icc.mpr hT.le⟩ hqcont
  set m : ℝ := ‖q (σ v₀)‖ with hmdef
  have hm : 0 < m := norm_pos_iff.mpr (hreg v₀ hv₀mem).2
  have hbound : ∀ v ∈ Set.Icc 0 T, m ≤ ‖q (σ v)‖ := fun v hv => hv₀min hv
  obtain ⟨J, hJ⟩ := sel_bound A hσ.cont hreg
  obtain ⟨ρ, hρ, hρle⟩ := atlas_radius_min A J
  have hrad : ∀ v ∈ Set.Icc 0 T, ρ ≤ A.r (A.sel (σ v)) := fun v hv =>
    hρle _ (hJ v hv) (A.sel_spec (hreg v hv).1 (hreg v hv).2).1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt m⁻¹ * T / ρ)
  refine ⟨N, ?_⟩
  set h : ℝ := T / (N + 1) with hhdef
  have hnn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by rw [hhdef]; positivity
  have hsmall : Real.sqrt m⁻¹ * h < ρ := by
    have h2 : Real.sqrt m⁻¹ * T < ρ * ((N : ℝ) + 1) := by
      have h1 : Real.sqrt m⁻¹ * T / ρ < (N : ℝ) + 1 := lt_trans hN (by linarith)
      have := (div_lt_iff₀ hρ).mp h1
      linarith
    rw [hhdef, ← mul_div_assoc, div_lt_iff₀ hnn]
    linarith
  have hth : ((N : ℝ) + 1) * h = T := by rw [hhdef]; field_simp
  intro k hk
  have hk1 : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  have hkT : (k : ℝ) * h ≤ T := by nlinarith
  have hkT' : (k : ℝ) * h + h ≤ T := by nlinarith
  have hklt : (k : ℝ) * h < T := by nlinarith
  obtain ⟨-, hpos, hsl⟩ := stepper_follows A hσ hm hbound hrad hh0 hsmall
    hslope0 k hkT
  have hposdef : pos A h k (σ 0) = σ ((k : ℝ) * h) := hpos
  have hsgnsl : SlopeAt (A.Φ (A.sel (σ ((k : ℝ) * h)))) σ (Set.Icc 0 T)
      ((k : ℝ) * h) (sgn A h k (σ 0)) := hsl
  set t : ℝ := (k : ℝ) * h with htdef
  have ht0 : 0 ≤ t := by positivity
  have htmem : t ∈ Set.Icc 0 T := ⟨ht0, hkT⟩
  obtain ⟨him, hq0⟩ := hreg t htmem
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  have hrpos : 0 < A.r (A.sel (σ t)) := A.hr _ hact
  have htS : σ t ∈ Metric.ball (A.c (A.sel (σ t))) (2 * A.r (A.sel (σ t))) :=
    Metric.ball_subset_ball (by linarith) hmem
  obtain ⟨ε, hε, hev⟩ := traj_ambient_local Metric.isOpen_ball
    (A.hd _ hact) (A.hsq _ hact) hσ Set.Subset.rfl htmem htS
  have hslε : SlopeAt (A.Φ (A.sel (σ t))) σ (Set.Icc 0 T) t ε := hev
  have hne : (nhdsWithin t (Set.Icc 0 T \ {t})).NeBot := by
    have hsub : Set.Ioc t T ⊆ Set.Icc 0 T \ {t} := fun u hu =>
      ⟨⟨le_trans ht0 hu.1.le, hu.2⟩, hu.1.ne'⟩
    have hbot : (nhdsWithin t (Set.Ioc t T)).NeBot := left_nhdsWithin_Ioc_neBot hklt
    exact hbot.mono (nhdsWithin_mono t hsub)
  have hsgn : sgn A h k (σ 0) = ε := slope_eq hsgnsl hslε
  obtain ⟨htrack, haff, -⟩ := step_position A hσ hm hbound hrad hh0 hsmall
    ht0 hkT' hsgnsl
  rw [hposdef]
  refine ⟨hact, hmem, ?_, ?_⟩
  · rcases hε with hε1 | hε1
    · exact Or.inl (hsgn.trans hε1)
    · exact Or.inr (hsgn.trans hε1)
  · intro u hu
    have humem : t + u ∈ Set.Icc t (t + h) :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    refine ⟨σ (t + u), htrack (t + u) humem, ?_⟩
    rw [haff (t + u) humem]
    push_cast
    ring

/-- **Measurability of trajectory existence**: the set of seeds admitting a unit-slope
trajectory of a given duration is the countable union of the strong-legal sets, hence
measurable. -/
theorem traj_exists_measurable {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {T : ℝ}
    (hT : 0 < T) :
    MeasurableSet {z : ℂ | ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1} := by
  have hset : {z : ℂ | ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1}
      = ⋃ N : ℕ, slegal A (T / (N + 1)) N := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨σ, hσ0, hσtraj, hσslope⟩
      rw [← hσ0] at hσslope
      obtain ⟨N, hN⟩ := slegal_of_traj hq A hT hσtraj hσslope
      rw [hσ0] at hN
      exact ⟨N, hN⟩
    · rintro ⟨N, hN⟩
      exact traj_of_slegal A hT hN
  rw [hset]
  exact MeasurableSet.iUnion fun N => slegal_measurable A (by positivity) N

/-- **Inversion of the reach functional**: below the per-zero threshold, the reach
inequality places the seed inside the power ball at its zero. -/
theorem reach_invert {a s r e δ : ℝ} {M : ℕ} (ha : 0 < a) (hδ : 0 < δ)
    (h : a * min s (r / 2) ^ (M + 2) ≤ e ^ 2)
    (hth : e ^ 2 < a * δ ^ (M + 2)) (hδr : δ ≤ r / 2) : s ≤ δ := by
  by_contra hs
  push Not at hs
  have hmin : δ ≤ min s (r / 2) := le_min hs.le hδr
  have hpow : δ ^ (M + 2) ≤ min s (r / 2) ^ (M + 2) :=
    pow_le_pow_left₀ hδ.le hmin _
  nlinarith [mul_le_mul_of_nonneg_left hpow ha.le]

/-- The `|q|`-mass of a small ball at a zero of local order `M` is at most a constant
multiple of `δ ^ (M + 2)`. -/
theorem ball_mass_pow {q : ℂ → ℂ} {z₀ : ℂ} {M : ℕ} {r₀ C₁ C₂ : ℝ}
    (hρr : 0 < r₀) (hC₂ : 0 ≤ C₂)
    (hbounds : ∀ w ∈ Metric.ball z₀ r₀,
      C₁ * ‖w - z₀‖ ^ M ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ * ‖w - z₀‖ ^ M)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ r₀) :
    ∫⁻ w in Metric.ball z₀ δ, ‖q w‖ₑ
      ≤ ENNReal.ofReal (C₂ * Real.pi * δ ^ (M + 2)) := by
  refine le_trans (ball_mass hρr hbounds hδ hδle) (le_of_eq ?_)
  have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [Complex.volume_ball, hpi, ← ENNReal.ofReal_pow hδ.le,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ δ ^ 2),
    ← ENNReal.ofReal_mul (mul_nonneg hC₂ (by positivity : (0 : ℝ) ≤ δ ^ M))]
  congr 1
  ring

/-- Strong legality implies legality: the moving-segment clause at the full step recovers
the single-step clause. -/
theorem slegal_legal {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    slegal A h N ⊆ legal A h N := by
  intro z hz k hk
  obtain ⟨hact, hball, hpm, hmove⟩ := hz k hk
  exact ⟨hact, hball, hpm, hmove h ⟨hh, le_refl h⟩⟩

/-- The stepper arrival sign of a strong-legal seed is a unit. -/
theorem sgn_last_pm {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 < h) {N : ℕ}
    {z : ℂ} (hz : z ∈ slegal A h N) :
    sgn A h (N + 1) z = 1 ∨ sgn A h (N + 1) z = -1 := by
  obtain ⟨σ, hσ0, hσtraj, -, hσarr, hσend⟩ := slegal_traj A hh N z hz
  have hT : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) * h := by push_cast; positivity
  have hTmem : ((N + 1 : ℕ) : ℝ) * h ∈ Set.Icc (0 : ℝ) (((N + 1 : ℕ) : ℝ) * h) :=
    Set.right_mem_Icc.mpr hT.le
  obtain ⟨him, hq0⟩ := traj_regular hσtraj hTmem
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  have hrpos : 0 < A.r (A.sel (σ (((N + 1 : ℕ) : ℝ) * h))) := A.hr _ hact
  have hTS : σ (((N + 1 : ℕ) : ℝ) * h) ∈ Metric.ball
      (A.c (A.sel (σ (((N + 1 : ℕ) : ℝ) * h))))
      (2 * A.r (A.sel (σ (((N + 1 : ℕ) : ℝ) * h)))) :=
    Metric.ball_subset_ball (by linarith) hmem
  obtain ⟨ε, hε, hev⟩ := traj_ambient_local Metric.isOpen_ball
    (A.hd _ hact) (A.hsq _ hact) hσtraj Set.Subset.rfl hTmem hTS
  have hslε : SlopeAt (A.Φ (A.sel (σ (((N + 1 : ℕ) : ℝ) * h)))) σ
      (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h)) (((N + 1 : ℕ) : ℝ) * h) ε := hev
  have : (nhdsWithin (((N + 1 : ℕ) : ℝ) * h)
      (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h) \ {((N + 1 : ℕ) : ℝ) * h})).NeBot := by
    have hsub : Set.Ico 0 (((N + 1 : ℕ) : ℝ) * h)
        ⊆ Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h) \ {((N + 1 : ℕ) : ℝ) * h} := fun u hu =>
      ⟨⟨hu.1, hu.2.le⟩, hu.2.ne⟩
    exact (right_nhdsWithin_Ico_neBot hT).mono (nhdsWithin_mono _ hsub)
  rw [← hσend] at hσarr
  have hkey : sgn A h (N + 1) z = ε := slope_eq hσarr hslε
  rcases hε with h1 | h1
  · exact Or.inl (hkey.trans h1)
  · exact Or.inr (hkey.trans h1)

/-- **Interval-overlap gluing**: a trajectory on `[0, c)` and a shifted closed right
piece agreeing with it on the half-open overlap glue to a trajectory on `[0, c]`. -/
theorem traj_glue_overlap {q : ℂ → ℂ} {σ τ' : ℝ → ℂ} {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b < c)
    (hσ : IsTrajOn q σ (Set.Ico 0 c)) (hτ' : IsTrajOn q τ' (Set.Icc 0 (c - b)))
    (hEq : ∀ u ∈ Set.Ico 0 (c - b), τ' u = σ (u + b)) :
    ∃ σ'' : ℝ → ℂ, Set.EqOn σ'' σ (Set.Ico 0 c) ∧ IsTrajOn q σ'' (Set.Icc 0 c) := by
  classical
  set σ'' : ℝ → ℂ := fun t => if t < c then σ t else τ' (t - b) with hσ''def
  have hE : Set.EqOn σ'' σ (Set.Ico 0 c) := fun t ht => if_pos ht.2
  have hc'' : σ'' c = τ' (c - b) := if_neg (lt_irrefl c)
  have hmid : ∀ t ∈ Set.Icc b c, σ'' t = τ' (t - b) := by
    intro t ht
    rcases lt_or_ge t c with hlt | hge
    · have h1 : τ' (t - b) = σ (t - b + b) :=
        hEq (t - b) ⟨by linarith [ht.1], by linarith⟩
      rw [hE ⟨le_trans hb ht.1, hlt⟩, h1, show t - b + b = t by ring]
    · rw [le_antisymm ht.2 hge, hc'']
  have hfilt : ∀ t ∈ Set.Ico 0 c,
      nhdsWithin t (Set.Icc 0 c) = nhdsWithin t (Set.Ico 0 c) := by
    intro t ht
    have h1 : t < (t + c) / 2 := by linarith [ht.2]
    have h2 : (t + c) / 2 ≤ c := by linarith [ht.2]
    rw [nhdsWithin_agree h1 h2, nhdsWithin_left h2 h1]
  have hright : nhdsWithin c (Set.Icc 0 c) = nhdsWithin c (Set.Icc b c) := by
    have h1 : c = b + (c - b) := by ring
    calc nhdsWithin c (Set.Icc 0 c)
        = nhdsWithin c (Set.Icc 0 (b + (c - b))) := by rw [← h1]
      _ = nhdsWithin c (Set.Icc b (b + (c - b))) := nhdsWithin_right hb hbc
      _ = nhdsWithin c (Set.Icc b c) := by rw [← h1]
  have hshift : Filter.Tendsto (fun u : ℝ => u - b) (nhdsWithin c (Set.Icc b c))
      (nhdsWithin (c - b) (Set.Icc 0 (c - b))) := by
    refine Filter.Tendsto.inf ((continuous_sub_right b).tendsto c) ?_
    refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
    rw [Set.mem_Icc] at hu ⊢
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hcont : ContinuousOn σ'' (Set.Icc 0 c) := by
    intro t ht
    rcases lt_or_ge t c with hlt | hge
    · have htI : t ∈ Set.Ico 0 c := ⟨ht.1, hlt⟩
      have h1 : Filter.Tendsto σ (nhdsWithin t (Set.Icc 0 c)) (nhds (σ t)) := by
        rw [hfilt t htI]
        exact hσ.cont t htI
      have h2 : Filter.Tendsto σ'' (nhdsWithin t (Set.Icc 0 c)) (nhds (σ t)) := by
        refine Filter.Tendsto.congr' ?_ h1
        rw [hfilt t htI]
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (hE hu).symm
      change Filter.Tendsto σ'' (nhdsWithin t (Set.Icc 0 c)) (nhds (σ'' t))
      rw [hE htI]
      exact h2
    · have hτc : ContinuousWithinAt τ' (Set.Icc 0 (c - b)) (c - b) :=
        hτ'.cont (c - b) (Set.right_mem_Icc.mpr (by linarith))
      have h1 : Filter.Tendsto (fun u : ℝ => τ' (u - b))
          (nhdsWithin c (Set.Icc b c)) (nhds (τ' (c - b))) :=
        Filter.Tendsto.comp hτc hshift
      have h2 : Filter.Tendsto σ'' (nhdsWithin c (Set.Icc b c))
          (nhds (τ' (c - b))) := by
        refine Filter.Tendsto.congr' ?_ h1
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (hmid u hu).symm
      rw [le_antisymm ht.2 hge]
      change Filter.Tendsto σ'' (nhdsWithin c (Set.Icc 0 c)) (nhds (σ'' c))
      rw [hc'', hright]
      exact h2
  refine ⟨σ'', hE, ⟨hcont, ?_⟩⟩
  intro t ht
  rcases lt_or_ge t c with hlt | hge
  · have htI : t ∈ Set.Ico 0 c := ⟨ht.1, hlt⟩
    obtain ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hσ.chart t htI
    refine ⟨U, hUo, ?_, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
    · rw [hE htI]
      exact hmem
    · rw [hfilt t htI]
      filter_upwards [hev, self_mem_nhdsWithin] with u hu huI
      rw [hE huI, hE htI]
      exact hu
  · have hEc : t = c := le_antisymm ht.2 hge
    rw [hEc]
    obtain ⟨U, hUo, hmem, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ :=
      hτ'.chart (c - b) (Set.right_mem_Icc.mpr (by linarith))
    refine ⟨U, hUo, ?_, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, ?_⟩
    · rw [hc'']
      exact hmem
    · rw [hright]
      filter_upwards [hshift.eventually hev, self_mem_nhdsWithin] with u hu huI
      rw [hmid u huI, hc'']
      refine ⟨hu.1, ?_⟩
      rw [hu.2]
      push_cast
      ring

/-- **Seed uniqueness**: two trajectories from one seed with equal initial chart slope
in an injective chart around the seed agree on the common interval. -/
theorem seed_unique {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦinj : Set.InjOn Φ S) {σ₁ σ₂ : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (h₁ : IsTrajOn q σ₁ (Set.Icc 0 b)) (h₂ : IsTrajOn q σ₂ (Set.Icc 0 b))
    (h0 : σ₁ 0 = σ₂ 0) (hyS : σ₁ 0 ∈ S) {s : ℝ}
    (hs₁ : SlopeAt Φ σ₁ (Set.Icc 0 b) 0 s) (hs₂ : SlopeAt Φ σ₂ (Set.Icc 0 b) 0 s) :
    Set.EqOn σ₁ σ₂ (Set.Icc 0 b) := by
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 b := Set.left_mem_Icc.mpr hb
  have hσ₁S : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 b), σ₁ u ∈ S :=
    (h₁.cont 0 h0mem) (hS.mem_nhds hyS)
  have hσ₂S : ∀ᶠ u in nhdsWithin 0 (Set.Icc 0 b), σ₂ u ∈ S :=
    (h₂.cont 0 h0mem) (hS.mem_nhds (h0 ▸ hyS))
  refine traj_unique hb h₁ h₂ ?_
  filter_upwards [hs₁, hs₂, hσ₁S, hσ₂S] with u e₁ e₂ m₁ m₂
  refine hΦinj m₁ m₂ ?_
  rw [e₁, e₂, h0]

/-- **Positively oriented seed**: through every regular point there is a unit-slope
trajectory germ in the selected chart. -/
theorem seed_plus {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {z : ℂ}
    (hzim : 0 < z.im) (hz0 : q z ≠ 0) :
    ∃ δ > 0, ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 δ) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 δ) 0 1 := by
  obtain ⟨δ, hδ, σs, hσs0, hσs⟩ := exists_traj_seed hq hzim hz0
  obtain ⟨hact, hmem⟩ := A.sel_spec hzim hz0
  have hrpos : 0 < A.r (A.sel z) := A.hr _ hact
  have hzS : z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) :=
    Metric.ball_subset_ball (by linarith) hmem
  have h0mem : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hzS' : σs 0 ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) := by
    rw [hσs0]
    exact hzS
  obtain ⟨ε, hε, hev⟩ := traj_ambient_local Metric.isOpen_ball
    (A.hd _ hact) (A.hsq _ hact) hσs Set.Subset.rfl h0mem hzS'
  have hsub : Set.Icc (0 : ℝ) δ ⊆ Set.Icc (-δ) δ :=
    Set.Icc_subset_Icc (by linarith) le_rfl
  rcases hε with hε1 | hε1
  · refine ⟨δ, hδ, σs, hσs0, traj_mono hσs hsub, ?_⟩
    have := hev.filter_mono (nhdsWithin_mono 0 hsub)
    rw [hε1] at this
    exact this
  · refine ⟨δ, hδ, fun u => σs (-u),
      by change σs (-0) = z; rw [neg_zero]; exact hσs0, ?_, ?_⟩
    · refine traj_mono (traj_reverse hσs) fun u hu => ?_
      change -u ∈ Set.Icc (-δ) δ
      rw [Set.mem_Icc]
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    · have hneg : Filter.Tendsto (fun u : ℝ => -u) (nhdsWithin 0 (Set.Icc 0 δ))
          (nhdsWithin 0 (Set.Icc (-δ) δ)) := by
        have h0 : Filter.Tendsto (fun u : ℝ => -u) (nhds (0 : ℝ)) (nhds 0) := by
          simpa using continuous_neg.tendsto (0 : ℝ)
        refine Filter.Tendsto.inf h0 ?_
        refine Filter.tendsto_principal_principal.mpr fun u hu => ?_
        rw [Set.mem_Icc] at hu ⊢
        exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
      filter_upwards [hneg.eventually hev] with u hu
      show A.Φ (A.sel z) (σs (-u))
        = A.Φ (A.sel z) (σs (-0)) + ((1 : ℝ) : ℂ) * ((u - 0 : ℝ) : ℂ)
      rw [neg_zero, hu, hε1]
      push_cast
      ring

/-- **Maximal dying data**: a regular seed with no unit-slope trajectory of duration `T`
carries a maximal half-open unit-slope trajectory of lifetime at most `T`. -/
theorem dying_data {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {z : ℂ}
    (hzim : 0 < z.im) (hz0 : q z ≠ 0) {T : ℝ} (hT : 0 < T)
    (hno : ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 T) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 T) 0 1) :
    ∃ c σ, 0 < c ∧ c ≤ T ∧ σ 0 = z ∧ IsTrajOn q σ (Set.Ico 0 c) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Ico 0 c) 0 1 ∧
      ¬∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Ico 0 c) ∧
        IsTrajOn q σ' (Set.Icc 0 c) := by
  classical
  obtain ⟨hact, hmem⟩ := A.sel_spec hzim hz0
  have hrpos : 0 < A.r (A.sel z) := A.hr _ hact
  have hzS : z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) :=
    Metric.ball_subset_ball (by linarith) hmem
  obtain ⟨δ', hδ', σg, hσg0, hσgT, hσgS⟩ := seed_plus hq A hzim hz0
  set δ₀ : ℝ := min δ' (T / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hδ' (by linarith)
  have hδ₀δ' : δ₀ ≤ δ' := min_le_left _ _
  have hσ₀ : IsTrajOn q σg (Set.Icc 0 δ₀) :=
    traj_mono hσgT (Set.Icc_subset_Icc le_rfl hδ₀δ')
  have hσ₀S : SlopeAt (A.Φ (A.sel z)) σg (Set.Icc 0 δ₀) 0 1 := by
    have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 δ'), A.Φ (A.sel z) (σg v)
        = A.Φ (A.sel z) (σg 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσgS
    rw [nhdsWithin_left hδ₀δ' hδ₀] at h1
    exact h1
  set F : Set ℝ := {b | 0 < b ∧ ∃ σ : ℝ → ℂ, σ 0 = z ∧
    IsTrajOn q σ (Set.Icc 0 b) ∧
    SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 b) 0 1} with hFdef
  have hδ₀F : δ₀ ∈ F := ⟨hδ₀, σg, hσg0, hσ₀, hσ₀S⟩
  have hFT : ∀ b ∈ F, b < T := by
    intro b hb
    by_contra hge
    have hTb : T ≤ b := not_lt.mp hge
    obtain ⟨hbpos, σ, hσ0, hσtraj, hσS⟩ := hb
    refine hno ⟨σ, hσ0, traj_mono hσtraj (Set.Icc_subset_Icc le_rfl hTb), ?_⟩
    have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 b), A.Φ (A.sel z) (σ v)
        = A.Φ (A.sel z) (σ 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσS
    rw [nhdsWithin_left hTb hT] at h1
    exact h1
  have hFne : F.Nonempty := ⟨δ₀, hδ₀F⟩
  have hFbdd : BddAbove F := ⟨T, fun b hb => (hFT b hb).le⟩
  have hopen : ∀ b ∈ F, ∃ d, b < d ∧ d ∈ F := by
    intro b hb
    obtain ⟨hbpos, σ, hσ0, hσtraj, hσS⟩ := hb
    obtain ⟨δe, hδe, σ', hE', hσ'⟩ := traj_extend hq hbpos.le hσtraj
    refine ⟨b + δe, by linarith, ⟨by linarith, σ', ?_, hσ', ?_⟩⟩
    · rw [hE' (Set.left_mem_Icc.mpr hbpos.le), hσ0]
    · have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 b), A.Φ (A.sel z) (σ v)
          = A.Φ (A.sel z) (σ 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσS
      change ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 (b + δe)), A.Φ (A.sel z) (σ' v)
        = A.Φ (A.sel z) (σ' 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
      rw [nhdsWithin_left (by linarith : b ≤ b + δe) hbpos]
      filter_upwards [h1, self_mem_nhdsWithin] with v hv hvm
      rw [hE' hvm, hE' (Set.left_mem_Icc.mpr hbpos.le)]
      exact hv
  set c : ℝ := sSup F with hcdef
  have hδ₀c : δ₀ ≤ c := le_csSup hFbdd hδ₀F
  have hcT : c ≤ T := csSup_le hFne fun b hb => (hFT b hb).le
  have hδ₀c' : δ₀ < c := by
    obtain ⟨d, hd, hdF⟩ := hopen δ₀ hδ₀F
    exact lt_of_lt_of_le hd (le_csSup hFbdd hdF)
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le hδ₀ hδ₀c
  have hcoh : ∀ b, δ₀ ≤ b → ∀ σ : ℝ → ℂ, σ 0 = z → IsTrajOn q σ (Set.Icc 0 b) →
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 b) 0 1 →
      Set.EqOn σ σg (Set.Icc 0 δ₀) := by
    intro b hδb σ hσ0 hσtraj hσS
    have hσS' : SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 δ₀) 0 1 := by
      have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 b), A.Φ (A.sel z) (σ v)
          = A.Φ (A.sel z) (σ 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσS
      rw [nhdsWithin_left hδb hδ₀] at h1
      exact h1
    refine seed_unique Metric.isOpen_ball (A.hinj _ hact) hδ₀.le
      (traj_mono hσtraj (Set.Icc_subset_Icc le_rfl hδb)) hσ₀ ?_ ?_ hσS' hσ₀S
    · rw [hσ0, hσg0]
    · rw [hσ0]
      exact hzS
  have hfam : ∀ b ∈ Set.Ico δ₀ c, ∃ σ : ℝ → ℂ,
      Set.EqOn σ σg (Set.Icc 0 δ₀) ∧ IsTrajOn q σ (Set.Icc 0 b) := by
    intro b hb
    obtain ⟨d, hdF, hbd⟩ := exists_lt_of_lt_csSup hFne hb.2
    obtain ⟨hdpos, σ, hσ0, hσtraj, hσS⟩ := hdF
    exact ⟨σ, hcoh d (le_trans hb.1 hbd.le) σ hσ0 hσtraj hσS,
      traj_mono hσtraj (Set.Icc_subset_Icc le_rfl hbd.le)⟩
  obtain ⟨σm, hEg, hσm⟩ := traj_family hδ₀ hδ₀c' hfam
  have hσm0 : σm 0 = z := by
    rw [hEg (Set.left_mem_Icc.mpr hδ₀.le), hσg0]
  have hσmS : SlopeAt (A.Φ (A.sel z)) σm (Set.Ico 0 c) 0 1 := by
    have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 δ₀), A.Φ (A.sel z) (σg v)
        = A.Φ (A.sel z) (σg 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσ₀S
    change ∀ᶠ v in nhdsWithin 0 (Set.Ico 0 c), A.Φ (A.sel z) (σm v)
      = A.Φ (A.sel z) (σm 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
    rw [nhdsWithin_agree hδ₀ (le_of_lt hδ₀c')]
    filter_upwards [h1, self_mem_nhdsWithin] with v hv hvm
    rw [hEg hvm, hEg (Set.left_mem_Icc.mpr hδ₀.le)]
    exact hv
  refine ⟨c, σm, hc0, hcT, hσm0, hσm, hσmS, ?_⟩
  rintro ⟨σ', hE', hσ'⟩
  obtain ⟨δe, hδe, σ'', hE'', hσ''⟩ := traj_extend hq hc0.le hσ'
  have hv0 : σ'' 0 = σm 0 := by
    rw [hE'' (Set.left_mem_Icc.mpr hc0.le), hE' ⟨le_rfl, hc0⟩]
  have hσ''0 : σ'' 0 = z := hv0.trans hσm0
  have hσ''S : SlopeAt (A.Φ (A.sel z)) σ'' (Set.Icc 0 (c + δe)) 0 1 := by
    have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Ico 0 c), A.Φ (A.sel z) (σm v)
        = A.Φ (A.sel z) (σm 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσmS
    change ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 (c + δe)), A.Φ (A.sel z) (σ'' v)
      = A.Φ (A.sel z) (σ'' 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ)
    have hfl : nhdsWithin (0 : ℝ) (Set.Icc 0 (c + δe))
        = nhdsWithin 0 (Set.Ico 0 c) := by
      rw [nhdsWithin_left (by linarith : δ₀ ≤ c + δe) hδ₀,
        nhdsWithin_agree hδ₀ (le_of_lt hδ₀c')]
    rw [hfl]
    filter_upwards [h1, self_mem_nhdsWithin] with v hv hvm
    have he1 : σ'' v = σm v := by
      rw [hE'' ⟨hvm.1, hvm.2.le⟩, hE' hvm]
    rw [he1, hv0]
    exact hv
  have hmemF : c + δe ∈ F := ⟨by linarith, σ'', hσ''0, hσ'', hσ''S⟩
  have hle : c + δe ≤ c := le_csSup hFbdd hmemF
  linarith

/-- **Window dying data**: a seed surviving to time `a` but not to `a + ε` yields
maximal dying data of lifetime at most `ε` starting at its time-`a` arrival point. -/
theorem window_dying {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im}) (A : Atlas q) {z : ℂ}
    (hzim : 0 < z.im) (hz0 : q z ≠ 0) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hyes : ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 a) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 a) 0 1)
    (hno : ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (a + ε)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (a + ε)) 0 1) :
    ∃ σa : ℝ → ℂ, (σa 0 = z ∧ IsTrajOn q σa (Set.Icc 0 a) ∧
      SlopeAt (A.Φ (A.sel z)) σa (Set.Icc 0 a) 0 1) ∧
      ∃ c' τ, 0 < c' ∧ c' ≤ ε ∧ τ 0 = σa a ∧ IsTrajOn q τ (Set.Ico 0 c') ∧
        ¬∃ τ' : ℝ → ℂ, Set.EqOn τ' τ (Set.Ico 0 c') ∧
          IsTrajOn q τ' (Set.Icc 0 c') := by
  obtain ⟨c, σm, hc0, hcT, hσm0, hσm, hσmS, hmaxm⟩ :=
    dying_data hq A hzim hz0 (by linarith : (0 : ℝ) < a + ε) hno
  obtain ⟨σ, hσ0, hσtraj, hσS⟩ := hyes
  obtain ⟨hact, hmem⟩ := A.sel_spec hzim hz0
  have hrpos : 0 < A.r (A.sel z) := A.hr _ hact
  have hzS : z ∈ Metric.ball (A.c (A.sel z)) (2 * A.r (A.sel z)) :=
    Metric.ball_subset_ball (by linarith) hmem
  have hslope_cut : ∀ b, 0 < b → b < c →
      SlopeAt (A.Φ (A.sel z)) σm (Set.Icc 0 b) 0 1 := by
    intro b hb hbc
    have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Ico 0 c), A.Φ (A.sel z) (σm v)
        = A.Φ (A.sel z) (σm 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσmS
    rw [nhdsWithin_agree hb hbc.le] at h1
    exact h1
  have hac : a < c := by
    by_contra hge
    have hca : c ≤ a := not_lt.mp hge
    have hEqOn : Set.EqOn σ σm (Set.Ico 0 c) := by
      intro t ht
      have hb0 : (0 : ℝ) < (t + c) / 2 := by linarith [ht.1, hc0]
      have hbc : (t + c) / 2 < c := by linarith [ht.2]
      have hsub : Set.Icc (0 : ℝ) ((t + c) / 2) ⊆ Set.Ico 0 c := fun u hu =>
        ⟨hu.1, lt_of_le_of_lt hu.2 hbc⟩
      have hσcut : SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 ((t + c) / 2)) 0 1 := by
        have h1 : ∀ᶠ v in nhdsWithin 0 (Set.Icc 0 a), A.Φ (A.sel z) (σ v)
            = A.Φ (A.sel z) (σ 0) + ((1 : ℝ) : ℂ) * ((v - 0 : ℝ) : ℂ) := hσS
        rw [nhdsWithin_left (by linarith : (t + c) / 2 ≤ a) hb0] at h1
        exact h1
      have hkey := seed_unique Metric.isOpen_ball (A.hinj _ hact) hb0.le
        (traj_mono hσtraj (Set.Icc_subset_Icc le_rfl (by linarith)))
        (traj_mono hσm hsub) (by rw [hσ0, hσm0]) (by rw [hσ0]; exact hzS)
        hσcut (hslope_cut _ hb0 hbc)
      exact hkey ⟨ht.1, by linarith [ht.2]⟩
    exact hmaxm ⟨σ, hEqOn, traj_mono hσtraj (Set.Icc_subset_Icc le_rfl hca)⟩
  have hsuba : Set.Icc (0 : ℝ) a ⊆ Set.Ico 0 c := fun u hu =>
    ⟨hu.1, lt_of_le_of_lt hu.2 hac⟩
  refine ⟨σm, ⟨hσm0, traj_mono hσm hsuba, hslope_cut a ha hac⟩,
    c - a, fun u => σm (u + a), by linarith, by linarith, ?_, ?_, ?_⟩
  · change σm (0 + a) = σm a
    rw [zero_add]
  · refine traj_mono (traj_shift a hσm) fun u hu => ?_
    change u + a ∈ Set.Ico 0 c
    rw [Set.mem_Ico]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rintro ⟨τ', hEτ, hτ'⟩
    have hEq : ∀ u ∈ Set.Ico 0 (c - a), τ' u = σm (u + a) := fun u hu => hEτ hu
    obtain ⟨σ'', hE'', hσ''⟩ :=
      traj_glue_overlap ha.le hac hσm hτ' hEq
    exact hmaxm ⟨σ'', hE'', hσ''⟩

set_option maxHeartbeats 1600000 in
-- Heavy elaboration: long induction over trajectory segments with repeated `UpperHalfPlane`
-- smul / set-abbreviation unfolding in `isDefEq`; the default budget is not enough.
/-- **Uniform hyperbolic displacement bound**: a trajectory of flat duration `T` moves
its seed by at most `⌈T / (η / 2)⌉` in the hyperbolic metric, with `η` independent of
the trajectory. -/
theorem track_unif {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ) := by
  have _ := hΓ
  obtain ⟨K, hK, hcov⟩ := exists_compact_covering Γ hcc
  set K' : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' K with hK'def
  have hK'c : IsCompact K' := hK.image UpperHalfPlane.continuous_coe
  have hK'H : ∀ x ∈ K', 0 < x.im := by
    rintro x ⟨τ, hτ, rfl⟩
    exact τ.2
  obtain ⟨η, hη, hstep⟩ := uniform_step q.holo hq0 hK'c hK'H
  refine ⟨η, hη, ?_⟩
  intro σ T hT hσ
  have hreg : ∀ u ∈ Set.Icc 0 T, 0 < (σ u).im := fun u hu => (traj_regular hσ hu).1
  have h0' : 0 < (σ 0).im := hreg 0 (Set.left_mem_Icc.mpr hT)
  set τ₀ : UpperHalfPlane := ⟨σ 0, h0'⟩ with hτ₀def
  have key : ∀ k : ℕ, ∀ u, ∀ hu : u ∈ Set.Icc 0 T, u ≤ k * (η / 2) →
      dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane) τ₀ ≤ k := by
    intro k
    induction k with
    | zero =>
      intro u hu hle
      have hu0 : u = 0 := le_antisymm (by simpa using hle) hu.1
      subst hu0
      simp [hτ₀def]
    | succ k ih =>
      intro u hu hle
      by_cases hcase : u ≤ k * (η / 2)
      · calc dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane) τ₀ ≤ k := ih u hu hcase
          _ ≤ (k + 1 : ℕ) := by push_cast; linarith
      · push Not at hcase
        set a : ℝ := k * (η / 2) with hadef
        have ha0 : 0 ≤ a := by positivity
        have hau : a ≤ u := hcase.le
        have haT : a ∈ Set.Icc 0 T := ⟨ha0, le_trans hau hu.2⟩
        have hspan : u - a < η := by
          have := hle
          push_cast at this
          rw [hadef]
          linarith
        obtain ⟨γ, hγK⟩ := hcov ⟨σ a, hreg a haT⟩
        set σ' : ℝ → ℂ := fun v => moebiusMap (↑γ) (σ v) with hσ'def
        have hσ' : IsTrajOn q σ' (Set.Icc 0 T) :=
          traj_deck (↑γ) (q.automorphy (↑γ) γ.2) hσ
        have hσ'a : σ' a ∈ K' := by
          refine ⟨γ • ⟨σ a, hreg a haT⟩, hγK, ?_⟩
          exact coe_smul_moebius γ ⟨σ a, hreg a haT⟩
        have him : 0 < (σ' u).im := moebiusMap_im_pos _ (hreg u hu)
        have him' : 0 < (σ' a).im := moebiusMap_im_pos _ (hreg a haT)
        have hd1 := hstep σ' T a u hσ' ha0 hau hu.2 hspan hσ'a u
          (Set.right_mem_Icc.mpr hau) him him'
        have hlift : (⟨σ' u, him⟩ : UpperHalfPlane)
            = (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ⟨σ u, hreg u hu⟩ :=
          UpperHalfPlane.ext (coe_smul_eq_moebiusMap (↑γ) ⟨σ u, hreg u hu⟩).symm
        have hlift' : (⟨σ' a, him'⟩ : UpperHalfPlane)
            = (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • ⟨σ a, hreg a haT⟩ :=
          UpperHalfPlane.ext (coe_smul_eq_moebiusMap (↑γ) ⟨σ a, hreg a haT⟩).symm
        rw [hlift, hlift'] at hd1
        have hd2 : dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane)
            (⟨σ a, hreg a haT⟩ : UpperHalfPlane) ≤ 1 := by
          rwa [dist_smul] at hd1
        calc dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane) τ₀
            ≤ dist (⟨σ u, hreg u hu⟩ : UpperHalfPlane)
                (⟨σ a, hreg a haT⟩ : UpperHalfPlane)
              + dist (⟨σ a, hreg a haT⟩ : UpperHalfPlane) τ₀ := dist_triangle _ _ _
          _ ≤ 1 + k := add_le_add hd2 (ih a haT (le_of_eq hadef))
          _ = (k + 1 : ℕ) := by push_cast; ring
  intro u hu h1 h0
  have hle : u ≤ (Nat.ceil (T / (η / 2)) : ℝ) * (η / 2) := by
    have hc1 : T / (η / 2) ≤ (Nat.ceil (T / (η / 2)) : ℝ) := Nat.le_ceil _
    have hc2 : T ≤ (Nat.ceil (T / (η / 2)) : ℝ) * (η / 2) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < η / 2)] at hc1
      linarith
    linarith [hu.2]
  exact key (Nat.ceil (T / (η / 2))) u hu hle

/-- **Located dying-seed keystone**: a maximal trajectory dying by time `ε` singles out a
zero whose reach functional is at most `ε ^ 2` and which lies within half the local
height of a track point. -/
theorem dying_seed_located {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {σ : ℝ → ℂ} {c ε : ℝ} (hc : 0 < c) (hcε : c ≤ ε)
    (hσ : IsTrajOn q σ (Set.Ico 0 c))
    (hmax : ¬∃ σ' : ℝ → ℂ, Set.EqOn σ' σ (Set.Ico 0 c) ∧
      IsTrajOn q σ' (Set.Icc 0 c))
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀) :
    ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ = 0 ∧
      (∃ u ∈ Set.Ico 0 c, ‖σ u - z₀‖ ≤ (σ u).im / 2) ∧
      C₁ z₀ / (2 ^ M z₀ * 16) * min ‖σ 0 - z₀‖ (r₀ z₀ / 2) ^ (M z₀ + 2) ≤ ε ^ 2 := by
  classical
  obtain ⟨L, hLc, hLH, hLtrack⟩ := traj_track_compact_Ico hΓ hcc q hq0 hc hσ
  have h0mem : (0 : ℝ) ∈ Set.Ico 0 c := ⟨le_refl 0, hc⟩
  have hLne : L.Nonempty := ⟨σ 0, hLtrack 0 h0mem⟩
  obtain ⟨w₀, hw₀L, hw₀min⟩ := hLc.exists_isMinOn hLne
    Complex.continuous_im.continuousOn
  set η : ℝ := w₀.im with hηdef
  have hη : 0 < η := hLH hw₀L
  set L' : Set ℂ := Metric.cthickening (η / 2) L ∩ {z : ℂ | η / 2 ≤ z.im} with hL'def
  have hL'c : IsCompact L' := hLc.cthickening.inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hL'H : L' ⊆ {z : ℂ | 0 < z.im} := fun z hz => by
    have h1 : (0 : ℝ) < η / 2 := by positivity
    exact lt_of_lt_of_le h1 hz.2
  set Z : Set ℂ := {z ∈ L' | q z = 0} with hZdef
  have hZfin : Set.Finite Z := zeros_finite q.holo hq0 hL'c hL'H
  have hpool : ∀ ρ, 0 < ρ → ρ ≤ η / 2 →
      ∃ z₀ ∈ Z, ∃ u ∈ Set.Ico 0 c, ‖σ u - z₀‖ < ρ := by
    intro ρ hρ hρη
    obtain ⟨u, hu, z₀, him, h0, hnear⟩ :=
      dying_near_zero hΓ hcc q hq0 hc hσ hmax ρ hρ
    have hz₀u : ‖z₀ - σ u‖ < ρ := by rw [norm_sub_rev]; exact hnear
    refine ⟨z₀, ⟨⟨?_, ?_⟩, h0⟩, u, hu, hnear⟩
    · refine Metric.mem_cthickening_of_dist_le z₀ (σ u) _ _ (hLtrack u hu) ?_
      rw [dist_eq_norm]
      linarith
    · have h1 : η ≤ (σ u).im := hw₀min (hLtrack u hu)
      have h2 : |z₀.im - (σ u).im| ≤ ‖z₀ - σ u‖ := by
        simpa [Complex.sub_im] using Complex.abs_im_le_norm (z₀ - σ u)
      have h3 := (abs_le.mp h2).1
      change η / 2 ≤ z₀.im
      linarith
  have hrec : ∃ z₀ ∈ Z, ∀ ρ, 0 < ρ → ∃ u ∈ Set.Ico 0 c, ‖σ u - z₀‖ < ρ := by
    by_contra hcon
    push Not at hcon
    have hcon' : ∀ z₀ : ℂ, ∃ ρ, 0 < ρ ∧
        (z₀ ∈ Z → ∀ u ∈ Set.Ico 0 c, ρ ≤ ‖σ u - z₀‖) := by
      intro z₀
      by_cases hz : z₀ ∈ Z
      · obtain ⟨ρ, hρ, hfar⟩ := hcon z₀ hz
        exact ⟨ρ, hρ, fun _ => hfar⟩
      · exact ⟨1, one_pos, fun h => absurd h hz⟩
    choose ρf hρf hρfar using hcon'
    obtain ⟨zw, hzw, -⟩ := hpool (η / 2) (by positivity) le_rfl
    have hFne : hZfin.toFinset.Nonempty := ⟨zw, hZfin.mem_toFinset.mpr hzw⟩
    set ρm : ℝ := min (hZfin.toFinset.inf' hFne ρf) (η / 2) with hρmdef
    have hρm : 0 < ρm := by
      refine lt_min ?_ (by positivity)
      exact (Finset.lt_inf'_iff hFne).mpr fun z _ => hρf z
    obtain ⟨z₀, hz₀Z, u, hu, hnear⟩ := hpool ρm hρm (min_le_right _ _)
    have h2 : ρm ≤ ρf z₀ := le_trans (min_le_left _ _)
      (Finset.inf'_le ρf (hZfin.mem_toFinset.mpr hz₀Z))
    have h1 : ρf z₀ ≤ ‖σ u - z₀‖ := hρfar z₀ hz₀Z u hu
    linarith
  obtain ⟨z₀, hz₀Z, hz₀rec⟩ := hrec
  have hz₀im : 0 < z₀.im := hL'H hz₀Z.1
  obtain ⟨hr₀, hC₁, hbounds⟩ := hdata z₀ hz₀im hz₀Z.2
  have hq0' : q (σ 0) ≠ 0 := (traj_regular hσ h0mem).2
  have hz' : 0 < ‖σ 0 - z₀‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro he
    exact hq0' (he ▸ hz₀Z.2)
  have hs : 0 < min ‖σ 0 - z₀‖ (r₀ z₀ / 2) := lt_min hz' (by linarith)
  obtain ⟨u, hu, hunear⟩ := hz₀rec
    (min (min ‖σ 0 - z₀‖ (r₀ z₀ / 2) / 8) (η / 2))
    (lt_min (by linarith) (by positivity))
  have hσu : IsTrajOn q σ (Set.Icc 0 u) :=
    traj_mono hσ fun v hv => ⟨hv.1, lt_of_le_of_lt hv.2 hu.2⟩
  have himu : η ≤ (σ u).im := hw₀min (hLtrack u hu)
  refine ⟨z₀, hz₀im, hz₀Z.2, ⟨u, hu, ?_⟩,
    reach_radius_sq hu.1 (le_trans hu.2.le hcε) hσu hr₀ hC₁ hbounds hz'
      (le_trans hunear.le (min_le_left _ _))⟩
  have h1 : ‖σ u - z₀‖ ≤ η / 2 := le_trans hunear.le (min_le_right _ _)
  linarith

/-- A point within half the local height of a hyperbolic point lies at hyperbolic
distance at most one from it. -/
theorem near_height_dist {p v : ℂ} (hp : 0 < p.im)
    (hv : ‖v - p‖ ≤ p.im / 2) (hvim : 0 < v.im) :
    dist (⟨v, hvim⟩ : UpperHalfPlane) (⟨p, hp⟩ : UpperHalfPlane) ≤ 1 := by
  have him : p.im / 2 ≤ v.im := by
    have h2 : |v.im - p.im| ≤ ‖v - p‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (v - p)
    have h3 := (abs_le.mp h2).1
    linarith
  refine le_trans (UpperHalfPlane.dist_le_dist_coe_div_sqrt _ _) ?_
  have hprod : 0 < v.im * p.im := mul_pos hvim hp
  have hsq : 0 < Real.sqrt (v.im * p.im) := Real.sqrt_pos.mpr hprod
  have hs : p.im / 2 ≤ Real.sqrt (v.im * p.im) := by
    rw [show p.im / 2 = Real.sqrt ((p.im / 2) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  change dist (v : ℂ) (p : ℂ) / Real.sqrt (v.im * p.im) ≤ 1
  rw [div_le_one hsq, dist_eq_norm]
  exact le_trans hv hs

/-- **Located window endpoint**: a seed surviving to `a ∈ (0, T]` but dying before
`a + ε` with `ε ≤ 1` produces a zero within a uniform hyperbolic radius of the seed
whose reach functional at the arrival point is at most `ε ^ 2`. -/
theorem window_endpoint_located
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane)))
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (A : Atlas (q : ℂ → ℂ)) {η : ℝ} (hη : 0 < η)
    (htrack : ∀ (σ : ℝ → ℂ) (T : ℝ), 0 ≤ T → IsTrajOn q σ (Set.Icc 0 T) →
      ∀ u, u ∈ Set.Icc 0 T → ∀ h1 : 0 < (σ u).im, ∀ h0 : 0 < (σ 0).im,
        dist (⟨σ u, h1⟩ : UpperHalfPlane) (⟨σ 0, h0⟩ : UpperHalfPlane)
          ≤ (Nat.ceil (T / (η / 2)) : ℝ))
    {z : ℂ} (hzim : 0 < z.im) (hz0 : q z ≠ 0) {a ε T : ℝ}
    (ha : 0 < a) (haT : a ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hyes : ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 a) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 a) 0 1)
    (hno : ¬∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 (a + ε)) ∧
      SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 (a + ε)) 0 1)
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀) :
    ∃ z₀ : ℂ, ∃ hz₀im : 0 < z₀.im, q z₀ = 0 ∧
      dist (⟨z₀, hz₀im⟩ : UpperHalfPlane) (⟨z, hzim⟩ : UpperHalfPlane)
        ≤ (Nat.ceil (T / (η / 2)) : ℝ) + (Nat.ceil (1 / (η / 2)) : ℝ) + 1 ∧
      ∃ σa : ℝ → ℂ, (σa 0 = z ∧ IsTrajOn q σa (Set.Icc 0 a) ∧
        SlopeAt (A.Φ (A.sel z)) σa (Set.Icc 0 a) 0 1) ∧
        C₁ z₀ / (2 ^ M z₀ * 16) * min ‖σa a - z₀‖ (r₀ z₀ / 2) ^ (M z₀ + 2)
          ≤ ε ^ 2 := by
  obtain ⟨σa, hpre, c', τ, hc'0, hc'ε, hτ0, hτ, hτmax⟩ :=
    window_dying q.holo A hzim hz0 ha hε hyes hno
  obtain ⟨z₀, hz₀im, hz₀0, ⟨u, hu, hunear⟩, hreach⟩ :=
    dying_seed_located hΓ hcc q hq0 hc'0 hc'ε hτ hτmax hdata
  have hτu : IsTrajOn q τ (Set.Icc 0 u) :=
    traj_mono hτ fun v hv => ⟨hv.1, lt_of_le_of_lt hv.2 hu.2⟩
  have himτu : 0 < (τ u).im :=
    (traj_regular hτu (Set.right_mem_Icc.mpr hu.1)).1
  have himτ0 : 0 < (τ 0).im := (traj_regular hτu (Set.left_mem_Icc.mpr hu.1)).1
  have hd1 : dist (⟨z₀, hz₀im⟩ : UpperHalfPlane)
      (⟨τ u, himτu⟩ : UpperHalfPlane) ≤ 1 := by
    refine near_height_dist himτu ?_ hz₀im
    rw [norm_sub_rev]
    exact hunear
  have hu1 : u ≤ 1 := le_trans hu.2.le (le_trans hc'ε hε1)
  have hd2 : dist (⟨τ u, himτu⟩ : UpperHalfPlane) (⟨τ 0, himτ0⟩ : UpperHalfPlane)
      ≤ (Nat.ceil (1 / (η / 2)) : ℝ) := by
    refine le_trans
      (htrack τ u hu.1 hτu u (Set.right_mem_Icc.mpr hu.1) himτu himτ0) ?_
    have hcle : Nat.ceil (u / (η / 2)) ≤ Nat.ceil (1 / (η / 2)) :=
      Nat.ceil_le_ceil (by gcongr)
    exact_mod_cast hcle
  obtain ⟨hσa0, hσatraj, hσaS⟩ := hpre
  have himw : 0 < (σa a).im :=
    (traj_regular hσatraj (Set.right_mem_Icc.mpr ha.le)).1
  have himz : 0 < (σa 0).im :=
    (traj_regular hσatraj (Set.left_mem_Icc.mpr ha.le)).1
  have hd3 : dist (⟨σa a, himw⟩ : UpperHalfPlane) (⟨σa 0, himz⟩ : UpperHalfPlane)
      ≤ (Nat.ceil (T / (η / 2)) : ℝ) := by
    refine le_trans
      (htrack σa a ha.le hσatraj a (Set.right_mem_Icc.mpr ha.le) himw himz) ?_
    have hcle : Nat.ceil (a / (η / 2)) ≤ Nat.ceil (T / (η / 2)) :=
      Nat.ceil_le_ceil (by gcongr)
    exact_mod_cast hcle
  have he1 : (⟨τ 0, himτ0⟩ : UpperHalfPlane) = ⟨σa a, himw⟩ :=
    UpperHalfPlane.ext hτ0
  have he2 : (⟨σa 0, himz⟩ : UpperHalfPlane) = ⟨z, hzim⟩ :=
    UpperHalfPlane.ext hσa0
  refine ⟨z₀, hz₀im, hz₀0, ?_, σa, ⟨hσa0, hσatraj, hσaS⟩, ?_⟩
  · calc dist (⟨z₀, hz₀im⟩ : UpperHalfPlane) (⟨z, hzim⟩ : UpperHalfPlane)
        ≤ dist (⟨z₀, hz₀im⟩ : UpperHalfPlane) (⟨τ u, himτu⟩ : UpperHalfPlane)
          + dist (⟨τ u, himτu⟩ : UpperHalfPlane) (⟨z, hzim⟩ : UpperHalfPlane) :=
        dist_triangle _ _ _
      _ ≤ 1 + ((Nat.ceil (1 / (η / 2)) : ℝ) + (Nat.ceil (T / (η / 2)) : ℝ)) := by
        refine add_le_add hd1 ?_
        calc dist (⟨τ u, himτu⟩ : UpperHalfPlane) (⟨z, hzim⟩ : UpperHalfPlane)
            ≤ dist (⟨τ u, himτu⟩ : UpperHalfPlane)
                (⟨τ 0, himτ0⟩ : UpperHalfPlane)
              + dist (⟨τ 0, himτ0⟩ : UpperHalfPlane)
                (⟨z, hzim⟩ : UpperHalfPlane) := dist_triangle _ _ _
          _ ≤ (Nat.ceil (1 / (η / 2)) : ℝ) + (Nat.ceil (T / (η / 2)) : ℝ) := by
            refine add_le_add hd2 ?_
            rw [he1, ← he2]
            exact hd3
      _ = (Nat.ceil (T / (η / 2)) : ℝ) + (Nat.ceil (1 / (η / 2)) : ℝ) + 1 := by
        ring
  · rw [← hτ0]
    exact hreach

/-- **Finite zero pool**: the zeros lying within hyperbolic distance `R` of a compact
subset of the upper half plane form a finite set. -/
theorem zero_pool {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {K : Set ℂ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKH : K ⊆ {z : ℂ | 0 < z.im}) (R : ℝ) :
    Set.Finite {v : ℂ | q v = 0 ∧ ∃ hv : 0 < v.im, ∃ z ∈ K, ∃ hz : 0 < z.im,
      dist (⟨v, hv⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) ≤ R} := by
  obtain ⟨zm, hzmK, hzmmin⟩ :=
    hKc.exists_isMinOn hKne Complex.continuous_im.continuousOn
  obtain ⟨zM, hzMK, hzMmax⟩ :=
    hKc.exists_isMaxOn hKne Complex.continuous_im.continuousOn
  obtain ⟨B, hB⟩ := hKc.isBounded.subset_closedBall 0
  have hm : 0 < zm.im := hKH hzmK
  set L : Set ℂ := Metric.closedBall 0 (B + zM.im * (Real.exp R - 1))
      ∩ {w : ℂ | zm.im / Real.exp R ≤ w.im} with hLdef
  have hLc : IsCompact L := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hLH : L ⊆ {z : ℂ | 0 < z.im} := fun w hw => by
    have h1 : (0 : ℝ) < zm.im / Real.exp R := by positivity
    exact lt_of_lt_of_le h1 hw.2
  refine Set.Finite.subset (zeros_finite q.holo hq0 hLc hLH) ?_
  rintro v ⟨hv0, hv, z, hzK, hz, hdist⟩
  have hdnn : (0 : ℝ)
      ≤ dist (⟨v, hv⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) := dist_nonneg
  have hRnn : (0 : ℝ) ≤ R := le_trans hdnn hdist
  refine ⟨⟨?_, ?_⟩, hv0⟩
  · have h1 := UpperHalfPlane.dist_coe_le (⟨v, hv⟩ : UpperHalfPlane) ⟨z, hz⟩
    have h3 : z.im ≤ zM.im := hzMmax hzK
    have hee : Real.exp (dist (⟨v, hv⟩ : UpperHalfPlane)
        (⟨z, hz⟩ : UpperHalfPlane)) ≤ Real.exp R := Real.exp_le_exp.mpr hdist
    have hex1 : (1 : ℝ) ≤ Real.exp (dist (⟨v, hv⟩ : UpperHalfPlane)
        (⟨z, hz⟩ : UpperHalfPlane)) := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      exact Real.exp_le_exp.mpr hdnn
    have h1' : dist v (z : ℂ) ≤ z.im * (Real.exp (dist (⟨v, hv⟩ : UpperHalfPlane)
        (⟨z, hz⟩ : UpperHalfPlane)) - 1) := h1
    have hzM0 : (0 : ℝ) ≤ zM.im := le_trans hz.le h3
    have h4 : dist v (z : ℂ) ≤ zM.im * (Real.exp R - 1) := by
      refine le_trans h1' ?_
      nlinarith [hz.le]
    have h5 : dist (z : ℂ) 0 ≤ B := by
      have := hB hzK
      rwa [Metric.mem_closedBall] at this
    rw [Metric.mem_closedBall]
    calc dist v 0 ≤ dist v (z : ℂ) + dist (z : ℂ) 0 := dist_triangle _ _ _
      _ ≤ zM.im * (Real.exp R - 1) + B := add_le_add h4 h5
      _ = B + zM.im * (Real.exp R - 1) := by ring
  · have h1 := UpperHalfPlane.im_div_exp_dist_le (⟨z, hz⟩ : UpperHalfPlane) ⟨v, hv⟩
    have h2 : zm.im ≤ z.im := hzmmin hzK
    have h3 : dist (⟨z, hz⟩ : UpperHalfPlane) (⟨v, hv⟩ : UpperHalfPlane) ≤ R := by
      rw [dist_comm]
      exact hdist
    change zm.im / Real.exp R ≤ v.im
    refine le_trans ?_ h1
    calc zm.im / Real.exp R ≤ z.im / Real.exp R := by gcongr
      _ ≤ z.im / Real.exp (dist (⟨z, hz⟩ : UpperHalfPlane)
          (⟨v, hv⟩ : UpperHalfPlane)) := by
        have h4 : Real.exp (dist (⟨z, hz⟩ : UpperHalfPlane)
            (⟨v, hv⟩ : UpperHalfPlane)) ≤ Real.exp R := Real.exp_le_exp.mpr h3
        gcongr

/-- **Arrival identification**: the stepper chain endpoint of a strong-legal seed equals
the endpoint of any unit-slope trajectory of the full grid duration. -/
theorem pos_eq_traj {q : ℂ → ℂ} (A : Atlas q) {h : ℝ} (hh : 0 < h) {N : ℕ}
    {z : ℂ} (hz : z ∈ slegal A h N) {σ : ℝ → ℂ}
    (hσ0 : σ 0 = z) (hσ : IsTrajOn q σ (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h)))
    (hσS : SlopeAt (A.Φ (A.sel z)) σ
      (Set.Icc 0 (((N + 1 : ℕ) : ℝ) * h)) 0 1) :
    pos A h (N + 1) z = σ (((N + 1 : ℕ) : ℝ) * h) := by
  obtain ⟨σ', hσ'0, hσ'traj, hσ'S, -, hσ'end⟩ := slegal_traj A hh N z hz
  have hT : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) * h := by push_cast; positivity
  have hreg : 0 < z.im ∧ q z ≠ 0 := by
    have := traj_regular hσ (Set.left_mem_Icc.mpr hT.le)
    rwa [hσ0] at this
  obtain ⟨hact, hmem⟩ := A.sel_spec hreg.1 hreg.2
  have hrpos : 0 < A.r (A.sel z) := A.hr _ hact
  have hEq := seed_unique Metric.isOpen_ball (A.hinj _ hact) hT.le hσ'traj hσ
    (by rw [hσ'0, hσ0])
    (by rw [hσ'0]; exact Metric.ball_subset_ball (by linarith) hmem) hσ'S hσS
  rw [← hσ'end]
  exact hEq (Set.right_mem_Icc.mpr hT.le)

/-- **Point-uniform reach ball**: below the per-zero threshold there is one radius
capturing every point satisfying the reach inequality, with ball mass controlled by
`ε ^ 2`. -/
theorem reach_ball' {q : ℂ → ℂ} {z₀ : ℂ} {M : ℕ} {r₀ C₁ C₂ ε : ℝ}
    (hr₀ : 0 < r₀) (hC₁ : 0 < C₁) (hC₂ : 0 ≤ C₂)
    (hbounds : ∀ v ∈ Metric.ball z₀ r₀,
      C₁ * ‖v - z₀‖ ^ M ≤ ‖q v‖ ∧ ‖q v‖ ≤ C₂ * ‖v - z₀‖ ^ M)
    (hε : 0 < ε)
    (hth : ε ^ 2 ≤ C₁ * (r₀ / 2) ^ (M + 2) / (2 ^ (M + 1) * 16)) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ w : ℂ, C₁ / (2 ^ M * 16) * min ‖w - z₀‖ (r₀ / 2) ^ (M + 2) ≤ ε ^ 2 →
        w ∈ Metric.ball z₀ δ) ∧
      ∫⁻ v in Metric.ball z₀ δ, ‖q v‖ₑ
        ≤ ENNReal.ofReal
          (C₂ * Real.pi * (2 ^ (M + 2) * (2 ^ (M + 1) * 16 / C₁)) * ε ^ 2) := by
  set x : ℝ := 2 ^ (M + 1) * 16 / C₁ * ε ^ 2 with hxdef
  have hx : 0 < x := by positivity
  set δ : ℝ := x ^ ((((M + 2 : ℕ) : ℝ))⁻¹ : ℝ) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hx _
  have hδpow : δ ^ (M + 2) = x :=
    Real.rpow_inv_natCast_pow hx.le (by omega)
  have hδr : δ ≤ r₀ / 2 := by
    have h2 := hth
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (M + 1) * 16)] at h2
    have h1 : x ≤ (r₀ / 2) ^ (M + 2) := by
      rw [hxdef, div_mul_eq_mul_div, div_le_iff₀ hC₁]
      nlinarith [h2]
    have h3 : δ ^ (M + 2) ≤ (r₀ / 2) ^ (M + 2) := by
      rw [hδpow]
      exact h1
    exact le_of_pow_le_pow_left₀ (by omega) (by positivity) h3
  refine ⟨2 * δ, by positivity, fun w hreach => ?_, ?_⟩
  · have hcap : ‖w - z₀‖ ≤ δ := by
      refine reach_invert (by positivity : (0 : ℝ) < C₁ / (2 ^ M * 16)) hδ hreach
        ?_ hδr
      rw [hδpow, hxdef]
      have hcomp : C₁ / (2 ^ M * 16) * (2 ^ (M + 1) * 16 / C₁ * ε ^ 2)
          = 2 * ε ^ 2 := by
        field_simp
        ring
      rw [hcomp]
      nlinarith
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  · refine le_trans (ball_mass_pow hr₀ hC₂ hbounds (by positivity)
      (by linarith : 2 * δ ≤ r₀)) ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [mul_pow, hδpow, hxdef]
    ring

/-- **The dying pool**: a finite zero pool with a uniform threshold, capture radii, and
`ε ^ 2`-controlled total ball mass, covering all zeros within hyperbolic reach `R` of a
compact seed set. -/
theorem pool {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (q : QuadraticDifferential Γ) (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    {K : Set ℂ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKH : K ⊆ {z : ℂ | 0 < z.im}) (R : ℝ)
    {M : ℂ → ℕ} {r₀ C₁ C₂ : ℂ → ℝ}
    (hdata : ∀ z₀ : ℂ, 0 < z₀.im → q z₀ = 0 → 0 < r₀ z₀ ∧ 0 < C₁ z₀ ∧
      0 ≤ C₂ z₀ ∧ ∀ w ∈ Metric.ball z₀ (r₀ z₀),
        C₁ z₀ * ‖w - z₀‖ ^ M z₀ ≤ ‖q w‖ ∧ ‖q w‖ ≤ C₂ z₀ * ‖w - z₀‖ ^ M z₀) :
    ∃ Z : Finset ℂ, ∃ ε₀ Cp : ℝ, 0 < ε₀ ∧ 0 ≤ Cp ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ : ℂ → ℝ,
        (∀ z₀ : ℂ, ∀ hz₀ : 0 < z₀.im, q z₀ = 0 →
          (∃ z ∈ K, ∃ hz : 0 < z.im, dist (⟨z₀, hz₀⟩ : UpperHalfPlane)
            (⟨z, hz⟩ : UpperHalfPlane) ≤ R) →
          z₀ ∈ Z ∧ ∀ w : ℂ,
            C₁ z₀ / (2 ^ M z₀ * 16)
                * min ‖w - z₀‖ (r₀ z₀ / 2) ^ (M z₀ + 2) ≤ ε ^ 2 →
            w ∈ Metric.ball z₀ (δ z₀)) ∧
        ∫⁻ v in ⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀), ‖q v‖ₑ
          ≤ ENNReal.ofReal (Cp * ε ^ 2) := by
  classical
  have hfin := zero_pool q hq0 hKc hKne hKH R
  set Z : Finset ℂ := hfin.toFinset with hZdef
  set t : ℂ → ℝ := fun z₀ =>
    Real.sqrt (C₁ z₀ * (r₀ z₀ / 2) ^ (M z₀ + 2) / (2 ^ (M z₀ + 1) * 16)) with htdef
  have htpos : ∀ z₀ ∈ Z, 0 < t z₀ := by
    intro z₀ hz₀
    obtain ⟨h0, hv, -⟩ := hfin.mem_toFinset.mp hz₀
    obtain ⟨hr, hC1, -, -⟩ := hdata z₀ hv h0
    exact Real.sqrt_pos.mpr (by positivity)
  by_cases hZne : Z.Nonempty
  case neg =>
    refine ⟨Z, 1, 0, one_pos, le_refl 0, fun ε hε hεle =>
      ⟨fun _ => 1, ?_, ?_⟩⟩
    · intro z₀ hz₀ h0 hnear
      exact absurd ⟨z₀, hfin.mem_toFinset.mpr ⟨h0, hz₀, hnear⟩⟩ hZne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hZne]
      simp
  case pos =>
  set ε₀ : ℝ := Z.inf' hZne t with hε₀def
  have hε₀pos : 0 < ε₀ := (Finset.lt_inf'_iff hZne).mpr htpos
  set Cp : ℝ := ∑ z₀ ∈ Z, C₂ z₀ * Real.pi *
    (2 ^ (M z₀ + 2) * (2 ^ (M z₀ + 1) * 16 / C₁ z₀)) with hCpdef
  have hterm : ∀ z₀ ∈ Z, 0 ≤ C₂ z₀ * Real.pi *
      (2 ^ (M z₀ + 2) * (2 ^ (M z₀ + 1) * 16 / C₁ z₀)) := by
    intro z₀ hz₀
    obtain ⟨h0, hv, -⟩ := hfin.mem_toFinset.mp hz₀
    obtain ⟨hr, hC1, hC2, -⟩ := hdata z₀ hv h0
    positivity
  have hCp : 0 ≤ Cp := Finset.sum_nonneg hterm
  refine ⟨Z, ε₀, Cp, hε₀pos, hCp, ?_⟩
  intro ε hε hεle
  have key : ∀ z₀ : ℂ, ∃ δv : ℝ, z₀ ∈ Z →
      (0 < δv ∧ (∀ w : ℂ, C₁ z₀ / (2 ^ M z₀ * 16)
          * min ‖w - z₀‖ (r₀ z₀ / 2) ^ (M z₀ + 2) ≤ ε ^ 2 →
        w ∈ Metric.ball z₀ δv) ∧
      ∫⁻ v in Metric.ball z₀ δv, ‖q v‖ₑ ≤ ENNReal.ofReal (C₂ z₀ * Real.pi *
        (2 ^ (M z₀ + 2) * (2 ^ (M z₀ + 1) * 16 / C₁ z₀)) * ε ^ 2)) := by
    intro z₀
    by_cases hz₀ : z₀ ∈ Z
    · obtain ⟨h0, him, -⟩ := hfin.mem_toFinset.mp hz₀
      obtain ⟨hr, hC1, hC2, hb⟩ := hdata z₀ him h0
      have hthr : ε ^ 2
          ≤ C₁ z₀ * (r₀ z₀ / 2) ^ (M z₀ + 2) / (2 ^ (M z₀ + 1) * 16) := by
        have h1 : ε ≤ t z₀ := le_trans hεle (Finset.inf'_le t hz₀)
        have h2 : ε ^ 2 ≤ t z₀ ^ 2 := by nlinarith
        rw [htdef] at h2
        rwa [Real.sq_sqrt (by positivity)] at h2
      obtain ⟨δv, hδv, hcap, hmass⟩ := reach_ball' hr hC1 hC2 hb hε hthr
      exact ⟨δv, fun _ => ⟨hδv, hcap, hmass⟩⟩
    · exact ⟨1, fun h => absurd h hz₀⟩
  choose δ hδ using key
  refine ⟨δ, ?_, ?_⟩
  · intro z₀ hz₀ h0 hnear
    have hz₀Z : z₀ ∈ Z := hfin.mem_toFinset.mpr ⟨h0, hz₀, hnear⟩
    exact ⟨hz₀Z, (hδ z₀ hz₀Z).2.1⟩
  · have hsub : ∫⁻ v in ⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀), ‖q v‖ₑ
        ≤ ∑ z₀ ∈ Z, ∫⁻ v in Metric.ball z₀ (δ z₀), ‖q v‖ₑ := by
      have hconv : (⋃ z₀ ∈ Z, Metric.ball z₀ (δ z₀))
          = ⋃ z₀ : {x // x ∈ Z}, Metric.ball (z₀ : ℂ) (δ z₀) := by
        ext v
        simp only [Set.mem_iUnion, Subtype.exists, exists_prop]
      rw [hconv]
      refine le_trans (lintegral_iUnion_le _ _) ?_
      rw [tsum_fintype]
      exact le_of_eq (Finset.sum_coe_sort Z
        fun z₀ => ∫⁻ v in Metric.ball z₀ (δ z₀), ‖q v‖ₑ)
    refine le_trans hsub ?_
    refine le_trans (Finset.sum_le_sum fun z₀ hz₀ => (hδ z₀ hz₀).2.2)
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun z₀ hz₀ =>
      mul_nonneg (hterm z₀ hz₀) (by positivity)]
    congr 1
    rw [hCpdef, Finset.sum_mul]

/-- **Cross-grid arrival multiplicity**: over all grids of one total duration, at most
two strong-legal seeds arrive at a given point. -/
theorem cross_mult {q : ℂ → ℂ} (A : Atlas q) {a : ℝ} (ha : 0 < a) (y : ℂ) :
    ∃ z₁ z₂ : ℂ, ∀ N : ℕ, ∀ z : ℂ, z ∈ slegal A (a / (N + 1)) N →
      pos A (a / (N + 1)) (N + 1) z = y → z = z₁ ∨ z = z₂ := by
  classical
  have hgrid : ∀ N : ℕ, (0 : ℝ) < a / (N + 1) := fun N => by positivity
  have hTeq : ∀ N : ℕ, ((N + 1 : ℕ) : ℝ) * (a / (N + 1)) = a := fun N => by
    push_cast
    field_simp
  have hdat : ∀ N : ℕ, ∀ z : ℂ, z ∈ slegal A (a / (N + 1)) N →
      ∃ σ : ℝ → ℂ, σ 0 = z ∧ IsTrajOn q σ (Set.Icc 0 a) ∧
        SlopeAt (A.Φ (A.sel z)) σ (Set.Icc 0 a) 0 1 ∧
        SlopeAt (A.Φ (A.sel (pos A (a / (N + 1)) (N + 1) z))) σ (Set.Icc 0 a) a
          (sgn A (a / (N + 1)) (N + 1) z) ∧
        σ a = pos A (a / (N + 1)) (N + 1) z := by
    intro N z hz
    obtain ⟨σ, h0, htraj, hS0, hSa, hend⟩ := slegal_traj A (hgrid N) N z hz
    rw [hTeq N] at htraj hS0 hSa hend
    exact ⟨σ, h0, htraj, hS0, hSa, hend⟩
  by_cases hreg : 0 < y.im ∧ q y ≠ 0
  case neg =>
    refine ⟨0, 0, fun N z hz hpos => ?_⟩
    obtain ⟨σ, h0, htraj, -, -, hend⟩ := hdat N z hz
    have hr := traj_regular htraj (Set.right_mem_Icc.mpr ha.le)
    rw [hend, hpos] at hr
    exact absurd hr hreg
  case pos =>
  obtain ⟨him, hq0⟩ := hreg
  obtain ⟨hact, hmem⟩ := A.sel_spec him hq0
  have hrpos : 0 < A.r (A.sel y) := A.hr _ hact
  have hyS : y ∈ Metric.ball (A.c (A.sel y)) (2 * A.r (A.sel y)) :=
    Metric.ball_subset_ball (by linarith) hmem
  have main : ∀ (N : ℕ) (z : ℂ), z ∈ slegal A (a / (N + 1)) N →
      pos A (a / (N + 1)) (N + 1) z = y →
      ∀ (N' : ℕ) (z' : ℂ), z' ∈ slegal A (a / (N' + 1)) N' →
      pos A (a / (N' + 1)) (N' + 1) z' = y →
      sgn A (a / (N + 1)) (N + 1) z = sgn A (a / (N' + 1)) (N' + 1) z' →
      z = z' := by
    intro N z hz hpos N' z' hz' hpos' hsgn
    obtain ⟨σ, h0, htraj, -, hSa, hend⟩ := hdat N z hz
    obtain ⟨σ', h0', htraj', -, hSa', hend'⟩ := hdat N' z' hz'
    rw [hpos] at hSa
    rw [hpos'] at hSa'
    rw [hsgn] at hSa
    have hkey := arrival_unique Metric.isOpen_ball (A.hinj _ hact) ha.le
      htraj htraj' (by rw [hend, hpos, hend', hpos'])
      (by rw [hend, hpos]; exact hyS) hSa hSa'
    rw [h0, h0'] at hkey
    exact hkey
  by_cases h1 : ∃ (N : ℕ) (z : ℂ), (z ∈ slegal A (a / (N + 1)) N ∧
      pos A (a / (N + 1)) (N + 1) z = y) ∧ sgn A (a / (N + 1)) (N + 1) z = 1
  · by_cases h2 : ∃ (N : ℕ) (z : ℂ), (z ∈ slegal A (a / (N + 1)) N ∧
        pos A (a / (N + 1)) (N + 1) z = y) ∧ sgn A (a / (N + 1)) (N + 1) z = -1
    · obtain ⟨N₁, z₁, ⟨hz₁, hp₁⟩, hs₁⟩ := h1
      obtain ⟨N₂, z₂, ⟨hz₂, hp₂⟩, hs₂⟩ := h2
      refine ⟨z₁, z₂, fun N z hz hpos => ?_⟩
      rcases sgn_last_pm A (hgrid N) hz with hs | hs
      · exact Or.inl (main N z hz hpos N₁ z₁ hz₁ hp₁ (by rw [hs, hs₁]))
      · exact Or.inr (main N z hz hpos N₂ z₂ hz₂ hp₂ (by rw [hs, hs₂]))
    · obtain ⟨N₁, z₁, ⟨hz₁, hp₁⟩, hs₁⟩ := h1
      refine ⟨z₁, z₁, fun N z hz hpos => ?_⟩
      rcases sgn_last_pm A (hgrid N) hz with hs | hs
      · exact Or.inl (main N z hz hpos N₁ z₁ hz₁ hp₁ (by rw [hs, hs₁]))
      · exact absurd ⟨N, z, ⟨hz, hpos⟩, hs⟩ h2
  · by_cases h2 : ∃ (N : ℕ) (z : ℂ), (z ∈ slegal A (a / (N + 1)) N ∧
        pos A (a / (N + 1)) (N + 1) z = y) ∧ sgn A (a / (N + 1)) (N + 1) z = -1
    · obtain ⟨N₂, z₂, ⟨hz₂, hp₂⟩, hs₂⟩ := h2
      refine ⟨z₂, z₂, fun N z hz hpos => ?_⟩
      rcases sgn_last_pm A (hgrid N) hz with hs | hs
      · exact absurd ⟨N, z, ⟨hz, hpos⟩, hs⟩ h1
      · exact Or.inl (main N z hz hpos N₂ z₂ hz₂ hp₂ (by rw [hs, hs₂]))
    · refine ⟨0, 0, fun N z hz hpos => ?_⟩
      rcases sgn_last_pm A (hgrid N) hz with hs | hs
      · exact absurd ⟨N, z, ⟨hz, hpos⟩, hs⟩ h1
      · exact absurd ⟨N, z, ⟨hz, hpos⟩, hs⟩ h2

/-- **Cross-grid union push**: the `|q|`-mass of countably many disjoint strong-legal
layers of one total duration is at most twice the mass of any arrival target. -/
theorem grid_union_push {q : ℂ → ℂ} (hqm : Measurable q) (A : Atlas q)
    {a : ℝ} (ha : 0 < a) {W : ℕ → Set ℂ}
    (hWm : ∀ N, MeasurableSet (W N))
    (hWs : ∀ N, W N ⊆ slegal A (a / (N + 1)) N)
    (hWd : Pairwise (Function.onFun Disjoint W))
    {B : Set ℂ}
    (hB : ∀ N : ℕ, ∀ z ∈ W N, pos A (a / (N + 1)) (N + 1) z ∈ B) :
    ∫⁻ w in ⋃ N, W N, ‖q w‖ₑ ≤ 2 * ∫⁻ w in B, ‖q w‖ₑ := by
  classical
  have hgrid : ∀ N : ℕ, (0 : ℝ) < a / (N + 1) := fun N => by positivity
  have hEL : ∀ N, W N ⊆ legal A (a / (N + 1)) N := fun N =>
    (hWs N).trans (slegal_legal A (hgrid N).le N)
  set P : (Σ N : ℕ, (Fin (N + 1) → ℕ × Bool)) → Set ℂ :=
    fun i => itinPiece A (a / (i.1 + 1)) i.1 (W i.1) i.2 with hPdef
  have hPsub : ∀ i, P i ⊆ W i.1 := fun i z hz => hz.1
  have hPmeas : ∀ i, MeasurableSet (P i) := fun i =>
    piece_measurable A _ _ (hWm i.1) i.2
  have hcov : ⋃ N, W N = ⋃ i, P i := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨N, hz⟩
      refine ⟨⟨N, itin A (a / (N + 1)) N z⟩, hz, fun k => ⟨rfl, ?_⟩⟩
      have hpm := ((hEL N hz) (k : ℕ)
        (by exact Nat.lt_succ_iff.mp k.isLt)).2.2.1
      change sgn A (a / (N + 1)) (k : ℕ) z
        = (if (if sgn A (a / (N + 1)) (k : ℕ) z = 1 then true else false)
          then (1 : ℝ) else -1)
      rcases hpm with h1 | h1
      · rw [if_pos h1]
        simp [h1]
      · rw [if_neg (by rw [h1]; norm_num)]
        simp [h1]
    · rintro ⟨i, hz⟩
      exact ⟨i.1, hz.1⟩
  have hdisj : Pairwise (Function.onFun Disjoint P) := by
    rintro ⟨N, c⟩ ⟨N', c'⟩ hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    by_cases hN : N = N'
    · subst hN
      have h1 := itin_eq A (hEL N) hzi
      have h2 := itin_eq A (hEL N) hzj
      exact hij (by rw [Sigma.mk.injEq]; exact ⟨rfl, heq_of_eq (h1.trans h2.symm)⟩)
    · exact Set.disjoint_left.mp (hWd hN) (hPsub ⟨N, c⟩ hzi) (hPsub ⟨N', c'⟩ hzj)
  have hchain : ∀ i, MeasurableSet (pos A (a / (i.1 + 1)) (i.1 + 1) '' P i) ∧
      ∫⁻ w in pos A (a / (i.1 + 1)) (i.1 + 1) '' P i, ‖q w‖ₑ
        = ∫⁻ w in P i, ‖q w‖ₑ := by
    rintro ⟨N, c⟩
    refine chain_cov A (hPmeas ⟨N, c⟩)
      (fun k => if hk : k < N + 1 then (c ⟨k, hk⟩).1 else 0)
      (fun k => if hk : k < N + 1 then
        (if (c ⟨k, hk⟩).2 then (1 : ℝ) else -1) else 0)
      ?_ (N + 1) (le_refl _)
    intro k hk z hz
    have hk' : k < N + 1 := by omega
    obtain ⟨hzE, hcl⟩ := hz
    obtain ⟨hsel, hsgn⟩ := hcl ⟨k, hk'⟩
    obtain ⟨hact, hball, hpm, hmove⟩ := (hEL N hzE) k hk
    rw [dif_pos hk', dif_pos hk']
    refine ⟨hsel, hsgn, ?_, ?_, ?_⟩
    · rw [← hsel]
      exact hact
    · rw [← hsel]
      exact hball
    · rw [← hsel, ← hsgn]
      exact hmove
  have hsum : ∫⁻ w in ⋃ N, W N, ‖q w‖ₑ = ∑' i, ∫⁻ w in P i, ‖q w‖ₑ := by
    rw [hcov]
    exact lintegral_iUnion hPmeas hdisj _
  have hmult' : ∀ y : ℂ,
      (∑' i : Σ N : ℕ, (Fin (N + 1) → ℕ × Bool),
        (pos A (a / (i.1 + 1)) (i.1 + 1) '' P i).indicator
          (fun _ => (1 : ℝ≥0∞)) y) ≤ 2 := by
    intro y
    obtain ⟨z₁, z₂, hz12⟩ := cross_mult A ha y
    have hidx : ∀ zc : ℂ, ∃ i : Σ N : ℕ, (Fin (N + 1) → ℕ × Bool),
        ∀ j : Σ N : ℕ, (Fin (N + 1) → ℕ × Bool), zc ∈ P j → j = i := by
      intro zc
      by_cases hzc : ∃ N, zc ∈ W N
      · obtain ⟨N, hN⟩ := hzc
        refine ⟨⟨N, itin A (a / (N + 1)) N zc⟩, ?_⟩
        rintro ⟨N', c'⟩ hj
        have hNN : N' = N := by
          by_contra hne
          exact Set.disjoint_left.mp (hWd hne) (hPsub ⟨N', c'⟩ hj) hN
        subst hNN
        rw [Sigma.mk.injEq]
        exact ⟨rfl, heq_of_eq (itin_eq A (hEL N') hj)⟩
      · refine ⟨⟨0, fun _ => (0, true)⟩, ?_⟩
        rintro ⟨N', c'⟩ hj
        exact absurd ⟨N', hPsub ⟨N', c'⟩ hj⟩ hzc
    obtain ⟨i₁, hi₁⟩ := hidx z₁
    obtain ⟨i₂, hi₂⟩ := hidx z₂
    refine tsum_indicator_pair (i₁ := i₁) (i₂ := i₂) ?_
    rintro ⟨N, c⟩ hc
    obtain ⟨z, hzP, hzy⟩ := hc
    rcases hz12 N z (hWs N (hPsub ⟨N, c⟩ hzP)) hzy with rfl | rfl
    · exact Or.inl (hi₁ ⟨N, c⟩ hzP)
    · exact Or.inr (hi₂ ⟨N, c⟩ hzP)
  calc ∫⁻ w in ⋃ N, W N, ‖q w‖ₑ = ∑' i, ∫⁻ w in P i, ‖q w‖ₑ := hsum
    _ = ∑' i : Σ N : ℕ, (Fin (N + 1) → ℕ × Bool),
        ∫⁻ w in pos A (a / (i.1 + 1)) (i.1 + 1) '' P i, ‖q w‖ₑ :=
        tsum_congr fun i => ((hchain i).2).symm
    _ ≤ 2 * ∫⁻ w in ⋃ i : Σ N : ℕ, (Fin (N + 1) → ℕ × Bool),
        pos A (a / (i.1 + 1)) (i.1 + 1) '' P i, ‖q w‖ₑ :=
        lintegral_mult_le' (fun i => (hchain i).1) hqm.enorm hmult'
    _ ≤ 2 * ∫⁻ w in B, ‖q w‖ₑ := by
        refine mul_le_mul_right (lintegral_mono_set ?_) 2
        refine Set.iUnion_subset fun i => ?_
        rintro y ⟨z, hzP, rfl⟩
        exact hB i.1 z (hPsub i hzP)

end RiemannDynamics
