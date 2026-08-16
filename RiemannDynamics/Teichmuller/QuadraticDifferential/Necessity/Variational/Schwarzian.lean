/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.Def

/-!
# The Schwarzian derivative

The Schwarzian derivative `S f = f'''/f' − (3/2)(f''/f')²` measures the deviation of a
locally injective holomorphic map from a Möbius transformation: it vanishes exactly on
fractional linear maps, obeys the cocycle law `S (f ∘ g) = (S f ∘ g)·(g')² + S g`, and a
map with vanishing Schwarzian on a connected open set is a single fractional linear map
there. Together with the nonvanishing of the derivative of an injective holomorphic map,
these are the local tools of the Bers-type map of the variational tier.

* `schwarzian` — the Schwarzian derivative.
* `deriv_ne_zero_of_injOn` — an injective holomorphic map has nonvanishing derivative.
* `schwarzian_ratio_eq_zero`, `schwarzian_moebiusMap` — Möbius maps have vanishing
  Schwarzian.
* `schwarzian_comp` — the cocycle law.
* `exists_ratio_of_schwarzian_eq_zero` — vanishing Schwarzian forces a fractional linear
  map.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- The **Schwarzian derivative** `S f = f'''/f' − (3/2)(f''/f')²`. -/
noncomputable def schwarzian (f : ℂ → ℂ) : ℂ → ℂ := fun z =>
  iteratedDeriv 3 f z / deriv f z - (3 / 2) * (iteratedDeriv 2 f z / deriv f z) ^ 2

/-- The Schwarzian derivative only depends on the germ of the map. -/
theorem schwarzian_congr_nhds {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) :
    schwarzian f z = schwarzian g z := by
  simp only [schwarzian]
  rw [h.iteratedDeriv_eq 3, h.iteratedDeriv_eq 2, h.deriv_eq]

/-- **Nonvanishing of the derivative of an injective holomorphic map**: a holomorphic map
injective on an open set has nonvanishing derivative there. -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {z : ℂ} (hz : z ∈ U) :
    deriv f z ≠ 0 := by
  intro hderiv0
  have hUz : U ∈ nhds z := hU.mem_nhds hz
  have hf_an : AnalyticAt ℂ f z := hf.analyticAt hUz
  set g : ℂ → ℂ := fun w => f w - f z with hg_def
  have hg_an : AnalyticAt ℂ g z := hf_an.sub analyticAt_const
  have hge2 : 2 ≤ analyticOrderAt g z := by
    have hdf_an : AnalyticAt ℂ (deriv f) z := hf_an.deriv
    have key := hf_an.analyticOrderAt_deriv_add_one
    have hge1 : 1 ≤ analyticOrderAt (deriv f) z := by
      rw [Order.one_le_iff_ne_zero, Ne, analyticOrderAt_eq_zero, not_or, not_not, not_ne_iff]
      exact ⟨hdf_an, hderiv0⟩
    calc (2 : ℕ∞) = 1 + 1 := by rfl
      _ ≤ analyticOrderAt (deriv f) z + 1 := by gcongr
      _ = analyticOrderAt g z := key
  have hne_top : analyticOrderAt g z ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    have hev2 : ∀ᶠ w in nhdsWithin z {z}ᶜ, f w = f z ∧ w ∈ U := by
      have hev' : ∀ᶠ w in nhdsWithin z {z}ᶜ, g w = 0 := hev.filter_mono nhdsWithin_le_nhds
      have hU' : ∀ᶠ w in nhdsWithin z {z}ᶜ, w ∈ U :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds hUz
      filter_upwards [hev', hU'] with w hw hwU
      refine ⟨?_, hwU⟩
      simpa [hg_def, sub_eq_zero] using hw
    obtain ⟨w, ⟨hw_eq, hw_U⟩, hwne⟩ := (hev2.and self_mem_nhdsWithin).exists
    exact hwne (hinj hw_U hz hw_eq)
  -- An analytic n-th root of a nonvanishing analytic germ.
  have analytic_nth_root : ∀ {G : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}, AnalyticAt ℂ G z₀ →
      G z₀ ≠ 0 → 1 ≤ n →
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H z₀ ∧ H z₀ ≠ 0 ∧ ∀ᶠ w in nhds z₀, (H w) ^ n = G w := by
    intro G z₀ n hG hGz hn
    set c : ℂ := (↑‖G z₀‖ : ℂ) / G z₀ with hc_def
    have hnorm_pos : 0 < ‖G z₀‖ := by positivity
    have hc_ne : c ≠ 0 := by
      rw [hc_def]; exact div_ne_zero (by exact_mod_cast (norm_ne_zero_iff).mpr hGz) hGz
    have hcG : c * G z₀ = (↑‖G z₀‖ : ℂ) := by rw [hc_def]; field_simp
    have hcG_an : AnalyticAt ℂ (fun w => c * G w) z₀ := analyticAt_const.mul hG
    have hval_slit : (fun w => c * G w) z₀ ∈ Complex.slitPlane := by
      simp only [hcG]; rw [Complex.mem_slitPlane_iff]; left
      simp only [Complex.ofReal_re]; positivity
    set cr : ℂ := Complex.exp (Complex.log c / n) with hcr_def
    have hcr_ne : cr ≠ 0 := Complex.exp_ne_zero _
    have hcr_pow : cr ^ n = c := by
      rw [hcr_def, ← Complex.exp_nat_mul, mul_div_cancel₀]
      · exact Complex.exp_log hc_ne
      · exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    refine ⟨fun w => Complex.exp (Complex.log (c * G w) / n) / cr, ?_, ?_, ?_⟩
    · apply AnalyticAt.div _ analyticAt_const hcr_ne
      have hlog : AnalyticAt ℂ (fun w => Complex.log (c * G w)) z₀ := hcG_an.clog hval_slit
      have hdiv : AnalyticAt ℂ (fun w => Complex.log (c * G w) / n) z₀ :=
        hlog.div analyticAt_const (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))
      exact hdiv.cexp'
    · exact div_ne_zero (Complex.exp_ne_zero _) hcr_ne
    · have hcont : ContinuousAt (fun w => c * G w) z₀ := hcG_an.continuousAt
      have hGne_ev : ∀ᶠ w in nhds z₀, c * G w ≠ 0 := hcont.eventually_ne (mul_ne_zero hc_ne hGz)
      filter_upwards [hGne_ev] with w hw
      rw [div_pow, ← Complex.exp_nat_mul,
        mul_div_cancel₀ _ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn) : (n : ℂ) ≠ 0)]
      rw [Complex.exp_log hw, hcr_pow]; field_simp
  obtain ⟨n, hn2, hordern⟩ : ∃ n : ℕ, 2 ≤ n ∧ analyticOrderAt g z = (n : ℕ∞) := by
    lift analyticOrderAt g z to ℕ using hne_top with m hm
    exact ⟨m, by exact_mod_cast hge2, rfl⟩
  obtain ⟨G, hG_an, hGz, hdecomp⟩ := (hg_an.analyticOrderAt_eq_natCast).mp hordern
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  obtain ⟨H, hH_an, hHz, hHpow⟩ := analytic_nth_root hG_an hGz hn1
  set u : ℂ → ℂ := fun w => (w - z) * H w with hu_def
  have hu_an : AnalyticAt ℂ u z := (analyticAt_id.sub analyticAt_const).mul hH_an
  have huz : u z = 0 := by simp [hu_def]
  have hu_deriv : HasDerivAt u (H z) z := by
    have h1 : HasDerivAt (fun w : ℂ => w - z) 1 z := by
      simpa using (hasDerivAt_id z).sub_const z
    have h2 : HasDerivAt H (deriv H z) z := hH_an.differentiableAt.hasDerivAt
    have h3 := h1.mul h2
    simp only [sub_self, zero_mul, add_zero, one_mul] at h3
    exact h3
  have hu_strict : HasStrictDerivAt u (H z) z := by
    have hs := hu_an.hasStrictDerivAt
    rwa [hu_deriv.deriv] at hs
  have hg_eq_un : ∀ᶠ w in nhds z, g w = (u w) ^ n := by
    filter_upwards [hdecomp, hHpow] with w hw hHw
    rw [hw, hu_def]; simp only; rw [mul_pow, smul_eq_mul, hHw]
  have hu_open : nhds (0 : ℂ) ≤ Filter.map u (nhds z) := by
    rcases hu_an.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · exfalso
      have hconst' : u =ᶠ[nhds z] fun _ => u z := hconst
      have hd0 : deriv u z = 0 := by rw [hconst'.deriv_eq, deriv_const]
      rw [hu_deriv.deriv] at hd0; exact hHz hd0
    · rwa [huz] at hopen
  have hcombined : ∀ᶠ w in nhds z, g w = (u w) ^ n ∧ w ∈ U := hg_eq_un.and hUz
  obtain ⟨s, hs_mem, hs_prop⟩ := Filter.eventually_iff_exists_mem.mp hcombined
  have himg : u '' s ∈ nhds (0 : ℂ) := Filter.le_map_iff.mp hu_open s hs_mem
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp himg
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζ_def
  have hζpow : ζ ^ n = 1 := (Complex.isPrimitiveRoot_exp n (by omega)).pow_eq_one
  have hζne1 : ζ ≠ 1 := (Complex.isPrimitiveRoot_exp n (by omega)).ne_one (by omega)
  have hζabs : ‖ζ‖ = 1 := by
    rw [hζ_def, Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  set t : ℂ := ((ρ / 2 : ℝ) : ℂ) with ht_def
  have ht_norm : ‖t‖ < ρ := by
    rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have ht_ne : t ≠ 0 := by
    rw [ht_def]; simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have ht_ball : t ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact ht_norm
  have hζt_ball : ζ * t ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hζabs, one_mul]; exact ht_norm
  obtain ⟨z₁, hz₁s, hz₁u⟩ := hball ht_ball
  obtain ⟨z₂, hz₂s, hz₂u⟩ := hball hζt_ball
  have hu_z₁ : u z₁ = t := hz₁u
  have hu_z₂ : u z₂ = ζ * t := hz₂u
  have hne12 : z₁ ≠ z₂ := by
    intro heq12; subst heq12
    rw [hu_z₁] at hu_z₂
    have hζeq1 : ζ = 1 := by
      have hkey : (1 - ζ) * t = 0 := by linear_combination hu_z₂
      rcases mul_eq_zero.mp hkey with h1 | h2
      · linear_combination -h1
      · exact (ht_ne h2).elim
    exact hζne1 hζeq1
  have hg1 := (hs_prop z₁ hz₁s).1
  have hg2 := (hs_prop z₂ hz₂s).1
  have heq : g z₁ = g z₂ := by
    rw [hg1, hg2, hu_z₁, hu_z₂, mul_pow, hζpow, one_mul]
  have hfeq : f z₁ = f z₂ := by
    rw [hg_def] at heq; simp only at heq; linear_combination heq
  exact hne12 (hinj (hs_prop z₁ hz₁s).2 (hs_prop z₂ hz₂s).2 hfeq)

/-- A fractional linear map has vanishing Schwarzian off its pole. -/
theorem schwarzian_ratio_eq_zero {a b c d : ℂ} (h : a * d - b * c ≠ 0) {z : ℂ}
    (hz : c * z + d ≠ 0) :
    schwarzian (fun w => (a * w + b) / (c * w + d)) z = 0 := by
  have _hu : a * d - b * c ≠ 0 := h
  have hID2 : ∀ F : ℂ → ℂ, iteratedDeriv 2 F = deriv (deriv F) := fun F => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hID3 : ∀ F : ℂ → ℂ, iteratedDeriv 3 F = deriv (iteratedDeriv 2 F) := fun F => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have hVopen : IsOpen {w : ℂ | c * w + d ≠ 0} := by
    have : Continuous fun w : ℂ => c * w + d := by continuity
    exact isOpen_ne.preimage this
  have hden : ∀ w : ℂ, HasDerivAt (fun x => c * x + d) c w := by
    intro w
    simpa using ((hasDerivAt_id w).const_mul c).add_const d
  have hnum : ∀ w : ℂ, HasDerivAt (fun x => a * x + b) a w := by
    intro w
    simpa using ((hasDerivAt_id w).const_mul a).add_const b
  have hf1 : ∀ w : ℂ, c * w + d ≠ 0 → HasDerivAt (fun x => (a * x + b) / (c * x + d))
      ((a * d - b * c) / (c * w + d) ^ 2) w := by
    intro w hw
    have h1 := (hnum w).div (hden w) hw
    have heq : (a * (c * w + d) - (a * w + b) * c) / (c * w + d) ^ 2
        = (a * d - b * c) / (c * w + d) ^ 2 := by ring
    rwa [heq] at h1
  have hf2 : ∀ w : ℂ, c * w + d ≠ 0 → HasDerivAt (fun x => (a * d - b * c) / (c * x + d) ^ 2)
      (-2 * c * (a * d - b * c) / (c * w + d) ^ 3) w := by
    intro w hw
    have h2 : HasDerivAt (fun x : ℂ => (c * x + d) ^ 2) (2 * (c * w + d) ^ 1 * c) w :=
      (hden w).pow 2
    have h1 := (hasDerivAt_const w (a * d - b * c)).div h2 (pow_ne_zero 2 hw)
    have heq : (0 * (c * w + d) ^ 2 - (a * d - b * c) * (2 * (c * w + d) ^ 1 * c))
        / ((c * w + d) ^ 2) ^ 2 = -2 * c * (a * d - b * c) / (c * w + d) ^ 3 := by
      field_simp
      ring
    rwa [heq] at h1
  have hf3 : ∀ w : ℂ, c * w + d ≠ 0 →
      HasDerivAt (fun x => -2 * c * (a * d - b * c) / (c * x + d) ^ 3)
      (6 * c ^ 2 * (a * d - b * c) / (c * w + d) ^ 4) w := by
    intro w hw
    have h2 : HasDerivAt (fun x : ℂ => (c * x + d) ^ 3) (3 * (c * w + d) ^ 2 * c) w :=
      (hden w).pow 3
    have h1 := (hasDerivAt_const w (-2 * c * (a * d - b * c))).div h2 (pow_ne_zero 3 hw)
    have heq : (0 * (c * w + d) ^ 3 - -2 * c * (a * d - b * c) * (3 * (c * w + d) ^ 2 * c))
        / ((c * w + d) ^ 3) ^ 2 = 6 * c ^ 2 * (a * d - b * c) / (c * w + d) ^ 4 := by
      field_simp
      ring
    rwa [heq] at h1
  have hd1 : ∀ w : ℂ, c * w + d ≠ 0 →
      deriv (fun x => (a * x + b) / (c * x + d)) w = (a * d - b * c) / (c * w + d) ^ 2 :=
    fun w hw => (hf1 w hw).deriv
  have hd2 : ∀ w : ℂ, c * w + d ≠ 0 →
      iteratedDeriv 2 (fun x => (a * x + b) / (c * x + d)) w
        = -2 * c * (a * d - b * c) / (c * w + d) ^ 3 := by
    intro w hw
    rw [hID2]
    have hev : deriv (fun x => (a * x + b) / (c * x + d))
        =ᶠ[nhds w] fun x => (a * d - b * c) / (c * x + d) ^ 2 := by
      filter_upwards [hVopen.mem_nhds hw] with x hx using hd1 x hx
    rw [hev.deriv_eq, (hf2 w hw).deriv]
  have hd3 : iteratedDeriv 3 (fun x => (a * x + b) / (c * x + d)) z
      = 6 * c ^ 2 * (a * d - b * c) / (c * z + d) ^ 4 := by
    rw [hID3]
    have hev : iteratedDeriv 2 (fun x => (a * x + b) / (c * x + d))
        =ᶠ[nhds z] fun x => -2 * c * (a * d - b * c) / (c * x + d) ^ 3 := by
      filter_upwards [hVopen.mem_nhds hz] with x hx using hd2 x hx
    rw [hev.deriv_eq, (hf3 z hz).deriv]
  simp only [schwarzian]
  rw [hd1 z hz, hd2 z hz, hd3]
  field_simp
  ring

/-- The plane Möbius map of a real matrix has vanishing Schwarzian off its pole. -/
theorem schwarzian_moebiusMap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : moebiusDenom γ z ≠ 0) : schwarzian (moebiusMap γ) z = 0 := by
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) ≠ 0 := by
    have h1 : (γ 0 0 : ℝ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) = 1 := by
      rw [← Matrix.det_fin_two]
      exact γ.det_coe
    have h2 : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) h1
    rw [h2]
    exact one_ne_zero
  have hz' : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := hz
  have hMM : moebiusMap γ
      = fun w => ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) := rfl
  rw [hMM]
  exact schwarzian_ratio_eq_zero hdet hz'

/-- **The Schwarzian cocycle law**: for analytic `g` at `z` and `f` at `g z` with
nonvanishing derivatives, `S (f ∘ g) = (S f ∘ g) · (g')² + S g`. -/
theorem schwarzian_comp {f g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (hg' : deriv g z ≠ 0) (hf : AnalyticAt ℂ f (g z)) (hf' : deriv f (g z) ≠ 0) :
    schwarzian (f ∘ g) z = schwarzian f (g z) * (deriv g z) ^ 2 + schwarzian g z := by
  have hID2 : ∀ F : ℂ → ℂ, iteratedDeriv 2 F = deriv (deriv F) := fun F => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hID3 : ∀ F : ℂ → ℂ, iteratedDeriv 3 F = deriv (iteratedDeriv 2 F) := fun F => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  set W : Set ℂ := {w | AnalyticAt ℂ g w ∧ AnalyticAt ℂ f (g w)} with hW_def
  have hWopen : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro w ⟨hw1, hw2⟩
    filter_upwards [(isOpen_analyticAt ℂ g).mem_nhds hw1,
      hw1.continuousAt.preimage_mem_nhds ((isOpen_analyticAt ℂ f).mem_nhds hw2)] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  have hzW : z ∈ W := ⟨hg, hf⟩
  have hd1 : ∀ w ∈ W, deriv (f ∘ g) w = deriv f (g w) * deriv g w := fun w hw =>
    deriv_comp w hw.2.differentiableAt hw.1.differentiableAt
  have hd2 : ∀ w ∈ W, iteratedDeriv 2 (f ∘ g) w
      = iteratedDeriv 2 f (g w) * (deriv g w) ^ 2 + deriv f (g w) * iteratedDeriv 2 g w := by
    intro w hw
    rw [hID2]
    have hev : deriv (f ∘ g) =ᶠ[nhds w] fun x => deriv f (g x) * deriv g x := by
      filter_upwards [hWopen.mem_nhds hw] with x hx using hd1 x hx
    rw [hev.deriv_eq]
    have hf2 : HasDerivAt (deriv f) (iteratedDeriv 2 f (g w)) (g w) := by
      rw [hID2 f]
      exact hw.2.deriv.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun x => deriv f (g x)) (iteratedDeriv 2 f (g w) * deriv g w) w :=
      HasDerivAt.comp w hf2 hw.1.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (deriv g) (iteratedDeriv 2 g w) w := by
      rw [hID2 g]
      exact hw.1.deriv.differentiableAt.hasDerivAt
    rw [(h1.fun_mul h2).deriv]
    ring
  have hd3 : iteratedDeriv 3 (f ∘ g) z
      = iteratedDeriv 3 f (g z) * (deriv g z) ^ 3
        + 3 * iteratedDeriv 2 f (g z) * deriv g z * iteratedDeriv 2 g z
        + deriv f (g z) * iteratedDeriv 3 g z := by
    rw [hID3]
    have hev : iteratedDeriv 2 (f ∘ g) =ᶠ[nhds z] fun x =>
        iteratedDeriv 2 f (g x) * (deriv g x) ^ 2 + deriv f (g x) * iteratedDeriv 2 g x := by
      filter_upwards [hWopen.mem_nhds hzW] with x hx using hd2 x hx
    rw [hev.deriv_eq]
    have hf2an : AnalyticAt ℂ (iteratedDeriv 2 f) (g z) := by
      rw [hID2 f]
      exact hf.deriv.deriv
    have hg2an : AnalyticAt ℂ (iteratedDeriv 2 g) z := by
      rw [hID2 g]
      exact hg.deriv.deriv
    have hBz : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f (g z)) (g z) := by
      rw [hID3 f]
      exact hf2an.differentiableAt.hasDerivAt
    have hB : HasDerivAt (fun x => iteratedDeriv 2 f (g x))
        (iteratedDeriv 3 f (g z) * deriv g z) z :=
      HasDerivAt.comp z hBz hg.differentiableAt.hasDerivAt
    have hg1 : HasDerivAt (deriv g) (iteratedDeriv 2 g z) z := by
      rw [hID2 g]
      exact hg.deriv.differentiableAt.hasDerivAt
    have hpow : HasDerivAt (fun x => (deriv g x) ^ 2)
        ((2 : ℕ) * (deriv g z) ^ 1 * iteratedDeriv 2 g z) z := hg1.pow 2
    have hf2z : HasDerivAt (deriv f) (iteratedDeriv 2 f (g z)) (g z) := by
      rw [hID2 f]
      exact hf.deriv.differentiableAt.hasDerivAt
    have hA : HasDerivAt (fun x => deriv f (g x)) (iteratedDeriv 2 f (g z) * deriv g z) z :=
      HasDerivAt.comp z hf2z hg.differentiableAt.hasDerivAt
    have hb : HasDerivAt (iteratedDeriv 2 g) (iteratedDeriv 3 g z) z := by
      rw [hID3 g]
      exact hg2an.differentiableAt.hasDerivAt
    rw [((hB.fun_mul hpow).fun_add (hA.fun_mul hb)).deriv]
    push_cast
    ring
  simp only [schwarzian]
  rw [hd1 z hzW, hd2 z hzW, hd3]
  field_simp
  ring

/-- **Rigidity of the vanishing Schwarzian**: a holomorphic map with nonvanishing
derivative and vanishing Schwarzian on a connected open set is a single fractional
linear map there. -/
theorem exists_ratio_of_schwarzian_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hne : U.Nonempty) (hf : DifferentiableOn ℂ f U)
    (hf' : ∀ z ∈ U, deriv f z ≠ 0) (hS : ∀ z ∈ U, schwarzian f z = 0) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      ∀ z ∈ U, c * z + d ≠ 0 ∧ f z = (a * z + b) / (c * z + d) := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hID2 : ∀ F : ℂ → ℂ, iteratedDeriv 2 F = deriv (deriv F) := fun F => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hID3 : ∀ F : ℂ → ℂ, iteratedDeriv 3 F = deriv (iteratedDeriv 2 F) := fun F => by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  have hfa : ∀ w ∈ U, AnalyticAt ℂ f w := fun w hw => hf.analyticAt (hU.mem_nhds hw)
  have hw₁ne : deriv f z₀ ≠ 0 := hf' z₀ hz₀
  -- Möbius coefficients matching the 2-jet of `f` at `z₀`.
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = -(iteratedDeriv 2 f z₀) / (2 * deriv f z₀) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d = 1 - c * z₀ := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = deriv f z₀ + f z₀ * c := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = f z₀ - a * z₀ := ⟨_, rfl⟩
  have hD₀ : c * z₀ + d = 1 := by rw [hd]; ring
  have hD₀ne : c * z₀ + d ≠ 0 := by rw [hD₀]; exact one_ne_zero
  have hdet : a * d - b * c = deriv f z₀ := by rw [hb, ha, hd]; ring
  have hdetne : a * d - b * c ≠ 0 := by rw [hdet]; exact hw₁ne
  have hc2 : -2 * c = iteratedDeriv 2 f z₀ / deriv f z₀ := by
    rw [hc]; field_simp
  -- Basic machinery for the target ratio.
  have hVopen : IsOpen {w : ℂ | c * w + d ≠ 0} := by
    have hcont : Continuous fun w : ℂ => c * w + d :=
      (continuous_const.mul continuous_id).add continuous_const
    exact isOpen_ne.preimage hcont
  have hden : ∀ w : ℂ, HasDerivAt (fun x => c * x + d) c w := fun w => by
    simpa using ((hasDerivAt_id w).const_mul c).add_const d
  have hnum : ∀ w : ℂ, HasDerivAt (fun x => a * x + b) a w := fun w => by
    simpa using ((hasDerivAt_id w).const_mul a).add_const b
  have hM1 : ∀ w : ℂ, c * w + d ≠ 0 → HasDerivAt (fun x => (a * x + b) / (c * x + d))
      ((a * d - b * c) / (c * w + d) ^ 2) w := by
    intro w hw
    have h1 := (hnum w).div (hden w) hw
    have heq : (a * (c * w + d) - (a * w + b) * c) / (c * w + d) ^ 2
        = (a * d - b * c) / (c * w + d) ^ 2 := by ring
    rwa [heq] at h1
  have hlin : AnalyticAt ℂ (fun x : ℂ => c * x + d) z₀ :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hMan_any : ∀ w : ℂ, c * w + d ≠ 0 →
      AnalyticAt ℂ (fun x => (a * x + b) / (c * x + d)) w := by
    intro w hw
    exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).fun_div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hw
  -- The Riccati equation `q' = q²/2` for `q := f''/f'` on `U`.
  have hq' : ∀ w ∈ U, HasDerivAt (fun x => iteratedDeriv 2 f x / deriv f x)
      ((iteratedDeriv 2 f w / deriv f w) ^ 2 / 2) w := by
    intro w hw
    have hFan : AnalyticAt ℂ f w := hfa w hw
    have h1 : HasDerivAt (deriv f) (iteratedDeriv 2 f w) w := by
      rw [hID2 f]; exact hFan.deriv.differentiableAt.hasDerivAt
    have h2an : AnalyticAt ℂ (iteratedDeriv 2 f) w := by
      rw [hID2 f]; exact hFan.deriv.deriv
    have h2 : HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f w) w := by
      rw [hID3 f]; exact h2an.differentiableAt.hasDerivAt
    have hdiv := h2.div h1 (hf' w hw)
    have hSw : iteratedDeriv 3 f w / deriv f w
        - 3 / 2 * (iteratedDeriv 2 f w / deriv f w) ^ 2 = 0 := by
      have := hS w hw
      simpa [schwarzian] using this
    have hne := hf' w hw
    have hval : (iteratedDeriv 3 f w * deriv f w - iteratedDeriv 2 f w * iteratedDeriv 2 f w)
        / deriv f w ^ 2 = (iteratedDeriv 2 f w / deriv f w) ^ 2 / 2 := by
      have e1 : (iteratedDeriv 3 f w * deriv f w - iteratedDeriv 2 f w * iteratedDeriv 2 f w)
          / deriv f w ^ 2
          = iteratedDeriv 3 f w / deriv f w - (iteratedDeriv 2 f w / deriv f w) ^ 2 := by
        field_simp
      rw [e1]
      linear_combination hSw
    rwa [hval] at hdiv
  -- The same Riccati equation for the candidate ratio `-2c/(cx+d)`.
  have hQ' : ∀ w : ℂ, c * w + d ≠ 0 → HasDerivAt (fun x => (-2 * c) / (c * x + d))
      (((-2 * c) / (c * w + d)) ^ 2 / 2) w := by
    intro w hw
    have h1 := (hasDerivAt_const w (-2 * c)).div (hden w) hw
    have heq : (0 * (c * w + d) - -2 * c * c) / (c * w + d) ^ 2
        = ((-2 * c) / (c * w + d)) ^ 2 / 2 := by
      field_simp
      ring
    rwa [heq] at h1
  have hUnb : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hVnb : {w : ℂ | c * w + d ≠ 0} ∈ nhds z₀ := hVopen.mem_nhds hD₀ne
  -- `f''/f'` agrees with `-2c/(cx+d)` near `z₀`: both solve the same ODE with equal values.
  have hqQM : ∀ᶠ x in nhds z₀, iteratedDeriv 2 f x / deriv f x = (-2 * c) / (c * x + d) := by
    by_contra hcon
    have hq2an : AnalyticAt ℂ (iteratedDeriv 2 f) z₀ := by
      rw [hID2 f]; exact (hfa z₀ hz₀).deriv.deriv
    have hqan : AnalyticAt ℂ (fun x => iteratedDeriv 2 f x / deriv f x) z₀ :=
      hq2an.fun_div (hfa z₀ hz₀).deriv hw₁ne
    have hQMan : AnalyticAt ℂ (fun x => (-2 * c) / (c * x + d)) z₀ :=
      analyticAt_const.fun_div hlin hD₀ne
    have hdiffan : AnalyticAt ℂ
        (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) z₀ :=
      hqan.sub hQMan
    have hphian : AnalyticAt ℂ
        (fun x => (iteratedDeriv 2 f x / deriv f x + (-2 * c) / (c * x + d)) / 2) z₀ :=
      (hqan.add hQMan).fun_div analyticAt_const (by norm_num)
    have hder_ev : deriv (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d))
        =ᶠ[nhds z₀]
          (fun x => (iteratedDeriv 2 f x / deriv f x + (-2 * c) / (c * x + d)) / 2)
            * (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) := by
      filter_upwards [hUnb, hVnb] with w hwU hwV
      have h1 := hq' w hwU
      have h2 := hQ' w hwV
      have h3 : deriv (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) w
          = (iteratedDeriv 2 f w / deriv f w) ^ 2 / 2
            - ((-2 * c) / (c * w + d)) ^ 2 / 2 := (h1.fun_sub h2).deriv
      rw [Pi.mul_apply, h3]
      ring
    have hh0 : iteratedDeriv 2 f z₀ / deriv f z₀ - (-2 * c) / (c * z₀ + d) = 0 := by
      rw [hD₀, div_one, ← hc2, sub_self]
    have hordne : analyticOrderAt
        (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) z₀ ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]
      intro hev
      apply hcon
      filter_upwards [hev] with x hx
      exact sub_eq_zero.mp hx
    have hord1 : 1 ≤ analyticOrderAt
        (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) z₀ := by
      rw [Order.one_le_iff_ne_zero, Ne, analyticOrderAt_eq_zero, not_or, not_not, not_ne_iff]
      exact ⟨hdiffan, hh0⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, analyticOrderAt
        (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) z₀ = (m : ℕ∞) := by
      lift analyticOrderAt
          (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d)) z₀
        to ℕ using hordne with m hm
      exact ⟨m, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = n + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero ?_
      rintro rfl
      rw [hm] at hord1
      simp at hord1
    have hstep : analyticOrderAt
        (deriv (fun x => iteratedDeriv 2 f x / deriv f x - (-2 * c) / (c * x + d))) z₀
          = (n : ℕ∞) := by
      apply analyticOrderAt_deriv_of_pos hdiffan
      rw [hm, hn]
      push_cast
      rfl
    rw [analyticOrderAt_congr hder_ev, analyticOrderAt_mul hphian hdiffan, hm] at hstep
    have hge : (m : ℕ∞) ≤ analyticOrderAt
        (fun x => (iteratedDeriv 2 f x / deriv f x + (-2 * c) / (c * x + d)) / 2) z₀
          + (m : ℕ∞) := le_add_self
    rw [hstep, hn] at hge
    have hcontra : n + 1 ≤ n := by exact_mod_cast hge
    omega
  -- Local constancy helper: an analytic map with eventually vanishing derivative is
  -- eventually equal to its value.
  have const_of : ∀ (F : ℂ → ℂ) (p : ℂ), AnalyticAt ℂ F p →
      (∀ᶠ x in nhds p, deriv F x = 0) → ∀ᶠ x in nhds p, F x = F p := by
    intro F p hFan hdF
    have hGan : AnalyticAt ℂ (fun x => F x - F p) p := hFan.sub analyticAt_const
    have hall : ∀ k : ℕ, iteratedDeriv k (fun x => F x - F p) p = 0 := by
      intro k
      cases k with
      | zero => simp
      | succ j =>
        rw [iteratedDeriv_succ']
        have hde : deriv (fun x => F x - F p) = fun x => deriv F x := by
          funext x
          exact deriv_sub_const (F p)
        rw [hde]
        have hev0 : (fun x => deriv F x) =ᶠ[nhds p] fun _ => (0 : ℂ) := hdF
        rw [hev0.iteratedDeriv_eq j]
        simp
    have hordtop : analyticOrderAt (fun x => F x - F p) p = ⊤ := by
      by_contra hne'
      lift analyticOrderAt (fun x => F x - F p) p to ℕ using hne' with m hm
      have h1 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hGan
        (n := m + 1)).mpr (fun i _ => hall i)
      rw [← hm] at h1
      have hcontra : m + 1 ≤ m := by exact_mod_cast h1
      omega
    have hev0 := analyticOrderAt_eq_top.mp hordtop
    filter_upwards [hev0] with x hx
    exact sub_eq_zero.mp hx
  -- Integrate once: `f' · (cx+d)²` is locally constant near `z₀`.
  have hrderiv : ∀ᶠ w in nhds z₀, deriv (fun x => deriv f x * (c * x + d) ^ 2) w = 0 := by
    filter_upwards [hUnb, hVnb, hqQM] with w hwU hwV hwq
    have h1 : HasDerivAt (deriv f) (iteratedDeriv 2 f w) w := by
      rw [hID2 f]; exact (hfa w hwU).deriv.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun x : ℂ => (c * x + d) ^ 2) (2 * (c * w + d) ^ 1 * c) w :=
      (hden w).pow 2
    rw [(h1.fun_mul h2).deriv]
    have hcross : iteratedDeriv 2 f w * (c * w + d) = -2 * c * deriv f w := by
      rw [div_eq_div_iff (hf' w hwU) hwV] at hwq
      linear_combination hwq
    linear_combination (c * w + d) * hcross
  have hpolyan : AnalyticAt ℂ (fun x : ℂ => (c * x + d) ^ 2) z₀ := hlin.pow 2
  have hran : AnalyticAt ℂ (fun x => deriv f x * (c * x + d) ^ 2) z₀ :=
    (hfa z₀ hz₀).deriv.mul hpolyan
  have hrconst := const_of (fun x => deriv f x * (c * x + d) ^ 2) z₀ hran hrderiv
  have hrz₀ : deriv f z₀ * (c * z₀ + d) ^ 2 = deriv f z₀ := by rw [hD₀]; ring
  -- Integrate twice: `f − M` is locally constant near `z₀`, with value `0`.
  have hfMderiv : ∀ᶠ w in nhds z₀,
      deriv (fun x => f x - (a * x + b) / (c * x + d)) w = 0 := by
    filter_upwards [hUnb, hVnb, hrconst] with w hwU hwV hwr
    have hdf : DifferentiableAt ℂ f w := (hfa w hwU).differentiableAt
    have hdM : DifferentiableAt ℂ (fun x => (a * x + b) / (c * x + d)) w :=
      (hM1 w hwV).differentiableAt
    rw [deriv_fun_sub hdf hdM, (hM1 w hwV).deriv, hdet]
    have hwr' : deriv f w * (c * w + d) ^ 2 = deriv f z₀ * (c * z₀ + d) ^ 2 := hwr
    rw [hrz₀] at hwr'
    rw [sub_eq_zero, eq_div_iff (pow_ne_zero 2 hwV)]
    exact hwr'
  have hsuban : AnalyticAt ℂ (fun x => f x - (a * x + b) / (c * x + d)) z₀ :=
    (hfa z₀ hz₀).sub (hMan_any z₀ hD₀ne)
  have hsub := const_of (fun x => f x - (a * x + b) / (c * x + d)) z₀ hsuban hfMderiv
  have hMz₀ : (a * z₀ + b) / (c * z₀ + d) = f z₀ := by
    rw [hD₀, div_one, hb]
    ring
  have hfM : ∀ᶠ x in nhds z₀, f x = (a * x + b) / (c * x + d) := by
    filter_upwards [hsub] with x hx
    have hx' : f x - (a * x + b) / (c * x + d)
        = f z₀ - (a * z₀ + b) / (c * z₀ + d) := hx
    rw [hMz₀, sub_self] at hx'
    exact sub_eq_zero.mp hx'
  -- Globalize over the preconnected set `U` by a clopen argument.
  set A : Set ℂ := {ζ | ζ ∈ U ∧ c * ζ + d ≠ 0 ∧
    ∀ᶠ x in nhds ζ, f x = (a * x + b) / (c * x + d)} with hA_def
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro ζ ⟨hζU, hζd, hζev⟩
    filter_upwards [hU.mem_nhds hζU, hVopen.mem_nhds hζd, hζev.eventually_nhds]
      with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  have hz₀A : z₀ ∈ A := ⟨hz₀, hD₀ne, hfM⟩
  have hclosed : closure A ∩ U ⊆ A := by
    rintro ζ ⟨hζcl, hζU⟩
    by_cases hζA : ζ ∈ A
    · exact hζA
    have hNB : (nhdsWithin ζ A).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have hζd : c * ζ + d ≠ 0 := by
      intro h0
      have hnum0 : a * ζ + b ≠ 0 := by
        intro hn0
        apply hdetne
        have hd' : d = -(c * ζ) := by linear_combination h0
        have hb' : b = -(a * ζ) := by linear_combination hn0
        rw [hd', hb']
        ring
      have hfcont : ContinuousAt f ζ := (hf.differentiableAt (hU.mem_nhds hζU)).continuousAt
      have hlim1 : Filter.Tendsto (fun x => f x * (c * x + d)) (nhdsWithin ζ A)
          (nhds (f ζ * (c * ζ + d))) := by
        apply Filter.Tendsto.mul
        · exact hfcont.continuousWithinAt.tendsto
        · have hcont : Continuous fun x : ℂ => c * x + d :=
            (continuous_const.mul continuous_id).add continuous_const
          exact (hcont.tendsto ζ).mono_left nhdsWithin_le_nhds
      have hev_eq : ∀ᶠ x in nhdsWithin ζ A, f x * (c * x + d) = a * x + b := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        obtain ⟨hxU, hxd, hxev⟩ := hx
        rw [hxev.self_of_nhds, div_mul_cancel₀ _ hxd]
      have hlim2 : Filter.Tendsto (fun x => a * x + b) (nhdsWithin ζ A)
          (nhds (a * ζ + b)) := by
        have hcont : Continuous fun x : ℂ => a * x + b :=
          (continuous_const.mul continuous_id).add continuous_const
        exact (hcont.tendsto ζ).mono_left nhdsWithin_le_nhds
      have huniq := tendsto_nhds_unique (hlim1.congr' hev_eq) hlim2
      rw [h0, mul_zero] at huniq
      exact hnum0 huniq.symm
    have hfreq : ∃ᶠ x in nhdsWithin ζ {ζ}ᶜ, f x = (a * x + b) / (c * x + d) := by
      have hsubA : A ⊆ {ζ}ᶜ := by
        intro x hx hxζ
        rw [Set.mem_singleton_iff] at hxζ
        exact hζA (hxζ ▸ hx)
      have hevA : ∀ᶠ x in nhdsWithin ζ A, f x = (a * x + b) / (c * x + d) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact hx.2.2.self_of_nhds
      exact hevA.frequently.filter_mono (nhdsWithin_mono ζ hsubA)
    have hζev := ((hfa ζ hζU).frequently_eq_iff_eventually_eq (hMan_any ζ hζd)).mp hfreq
    exact ⟨hζU, hζd, hζev⟩
  have hUsub : U ⊆ A := hUc.subset_of_closure_inter_subset hAopen ⟨z₀, hz₀, hz₀A⟩ hclosed
  refine ⟨a, b, c, d, hdetne, ?_⟩
  intro w hw
  obtain ⟨-, hwd, hwev⟩ := hUsub hw
  exact ⟨hwd, hwev.self_of_nhds⟩

end RiemannDynamics
