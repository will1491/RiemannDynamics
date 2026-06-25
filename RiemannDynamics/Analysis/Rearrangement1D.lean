/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The one-dimensional decreasing rearrangement on an interval

This file builds the **decreasing rearrangement** `f♯` of an extended-real-valued
function `f : ℝ → ℝ≥0∞` defined on a finite interval `Icc 0 T`, together with its
**equimeasurability** with `f` and the resulting preservation of layer-cake
integrals (in particular `∫⁻ f♯ = ∫⁻ f` and `∫⁻ (f♯)^p = ∫⁻ f^p`).

Mathlib provides the layer-cake / Cavalieri machinery
(`MeasureTheory.lintegral_eq_lintegral_meas_lt`) but no symmetric/decreasing
rearrangement of *functions*; this is the equimeasurable building block needed for
circular symmetrization of the conformal modulus.

## Main definitions

* `RiemannDynamics.distribFun T f t` — the **distribution function**
  `volume {x ∈ Icc 0 T | t < f x}` (`t : ℝ≥0∞`), the measure of the super-level set.
* `RiemannDynamics.decreasingRearrange T f x` — the **decreasing rearrangement**
  `f♯ x := sInf {t : ℝ≥0∞ | distribFun T f t ≤ ENNReal.ofReal x}`, the generalized
  right-inverse of the (antitone, right-continuous) distribution function.

## Main results

* `distribFun_antitone` — `t ↦ distribFun T f t` is antitone.
* `distribFun_le_ofReal_T` — the distribution function is bounded by `ofReal T`.
* `distribFun_decreasingRearrange_le` — the **right-continuity core**:
  `distribFun T f (f♯ x) ≤ ofReal x`, the value of `D` at the inf is attained.
* `lt_decreasingRearrange_iff` — the **fundamental relation**
  `t < f♯ x ↔ ofReal x < distribFun T f t` (for `0 ≤ x`).
* `distribFun_decreasingRearrange` — **equimeasurability**:
  `distribFun T f♯ t = distribFun T f t` for all `t`.
* `lintegral_decreasingRearrange_eq` — `∫⁻ x in Icc 0 T, f♯ x = ∫⁻ x in Icc 0 T, f x`.
* `lintegral_rpow_decreasingRearrange_eq` — `∫⁻ x in Icc 0 T, (f♯ x)^p = ∫⁻ x in Icc 0 T, (f x)^p`
  for `0 ≤ p` (covers the `p = 1, 2` energy cases).
-/

open MeasureTheory Set ENNReal Filter Topology

noncomputable section

namespace RiemannDynamics

variable (T : ℝ) (f : ℝ → ℝ≥0∞)

/-- The **distribution function** of `f` on `Icc 0 T`:
`distribFun T f t = volume {x ∈ Icc 0 T | t < f x}`, the measure of the
super-level set of `f` above the level `t`. -/
def distribFun (t : ℝ≥0∞) : ℝ≥0∞ :=
  volume {x ∈ Icc (0 : ℝ) T | t < f x}

/-- The **decreasing rearrangement** of `f`: the generalized right-inverse of the
distribution function, `f♯ x = sInf {t | distribFun T f t ≤ ofReal x}`. -/
def decreasingRearrange (x : ℝ) : ℝ≥0∞ :=
  sInf {t : ℝ≥0∞ | distribFun T f t ≤ ENNReal.ofReal x}

@[inherit_doc] notation:max f "♯[" T "]" => decreasingRearrange T f

variable {T f}

/-- The distribution function is antitone in the level `t`. -/
theorem distribFun_antitone : Antitone (distribFun T f) := by
  intro s t hst
  apply measure_mono
  intro x hx
  exact ⟨hx.1, lt_of_le_of_lt hst hx.2⟩

/-- The super-level set is contained in `Icc 0 T`, hence its measure is `≤ ofReal T`. -/
theorem distribFun_le_ofReal_T (t : ℝ≥0∞) : distribFun T f t ≤ ENNReal.ofReal T := by
  have h : distribFun T f t ≤ volume (Icc (0 : ℝ) T) :=
    measure_mono (fun x hx => hx.1)
  rwa [Real.volume_Icc, sub_zero] at h

/-- The distribution function is finite. -/
theorem distribFun_ne_top (t : ℝ≥0∞) : distribFun T f t ≠ ∞ :=
  ne_top_of_le_ne_top ofReal_ne_top (distribFun_le_ofReal_T t)

/-- The defining set of the rearrangement is always nonempty: `⊤` belongs to it
since the super-level set above `⊤` is empty. -/
theorem distribFun_top : distribFun T f ⊤ = 0 := by
  have : {x ∈ Icc (0 : ℝ) T | (⊤ : ℝ≥0∞) < f x} = ∅ := by
    ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro _; exact not_top_lt
  rw [distribFun, this, measure_empty]

/-- **Right-continuity core.** The value of the (antitone, right-continuous)
distribution function at the infimum defining `f♯ x` is bounded by `ofReal x`.
This is the only place where right-continuity of the distribution function is used:
it is established by a monotone-convergence argument on the super-level sets. -/
theorem distribFun_decreasingRearrange_le (x : ℝ) :
    distribFun T f (decreasingRearrange T f x) ≤ ENNReal.ofReal x := by
  set s₀ := decreasingRearrange T f x with hs₀def
  -- The defining set `S = {t | D t ≤ ofReal x}` is nonempty (contains `⊤`).
  have hSne : (⊤ : ℝ≥0∞) ∈ {t : ℝ≥0∞ | distribFun T f t ≤ ENNReal.ofReal x} := by
    simp only [mem_setOf_eq, distribFun_top]; exact zero_le _
  -- Case `s₀ = ⊤`: the super-level set above `⊤` is empty.
  rcases eq_or_ne s₀ ⊤ with htop | htop
  · rw [htop, distribFun_top]; exact zero_le _
  -- The monotone sequence of approximating super-level sets.
  set A : ℕ → Set ℝ := fun n => {y ∈ Icc (0 : ℝ) T | s₀ + ((n : ℝ≥0∞) + 1)⁻¹ < f y}
    with hAdef
  have hAmono : Monotone A := by
    intro m n hmn y hy
    refine ⟨hy.1, lt_of_le_of_lt ?_ hy.2⟩
    gcongr
  -- The union of the `A n` is the super-level set above `s₀`.
  have hunion : ⋃ n, A n = {y ∈ Icc (0 : ℝ) T | s₀ < f y} := by
    ext y
    simp only [hAdef, mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hyI, hlt⟩
      exact ⟨hyI, lt_of_le_of_lt le_self_add hlt⟩
    · rintro ⟨hyI, hlt⟩
      -- choose `n` with `(n+1)⁻¹ < f y - s₀`
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := f y - s₀)
        (ne_of_gt (tsub_pos_of_lt hlt))
      refine ⟨n, hyI, ?_⟩
      have hle : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := by gcongr; exact le_self_add
      have : ((n : ℝ≥0∞) + 1)⁻¹ < f y - s₀ := lt_of_le_of_lt hle hn
      exact lt_tsub_iff_left.mp this
  -- Measure of each approximating set is `≤ ofReal x`.
  have hAbound : ∀ n, volume (A n) ≤ ENNReal.ofReal x := by
    intro n
    -- `s₀ + (n+1)⁻¹ > s₀ = sInf S`, so some `t ∈ S` lies strictly below it.
    have hgt : s₀ < s₀ + ((n : ℝ≥0∞) + 1)⁻¹ := by
      refine ENNReal.lt_add_right htop ?_
      simp
    obtain ⟨t, htS, htlt⟩ := sInf_lt_iff.mp (hs₀def ▸ hgt)
    calc volume (A n) = distribFun T f (s₀ + ((n : ℝ≥0∞) + 1)⁻¹) := rfl
      _ ≤ distribFun T f t := distribFun_antitone (le_of_lt htlt)
      _ ≤ ENNReal.ofReal x := htS
  -- Pass to the limit: `D s₀ = volume (⋃ A n) = lim volume (A n) ≤ ofReal x`.
  have htends : Tendsto (fun n => volume (A n)) atTop (𝓝 (volume (⋃ n, A n))) :=
    tendsto_measure_iUnion_atTop hAmono
  rw [hunion] at htends
  have hDeq : distribFun T f s₀ = volume {y ∈ Icc (0 : ℝ) T | s₀ < f y} := rfl
  rw [hDeq]
  exact le_of_tendsto' htends hAbound

/-- **Fundamental relation** for the decreasing rearrangement:
`t < f♯ x ↔ ofReal x < distribFun T f t`. -/
theorem lt_decreasingRearrange_iff (x : ℝ) (t : ℝ≥0∞) :
    t < decreasingRearrange T f x ↔ ENNReal.ofReal x < distribFun T f t := by
  constructor
  · intro hlt
    by_contra hcon
    -- `D t ≤ ofReal x` means `t ∈ S`, so `sInf S ≤ t`, contradicting `t < sInf S`.
    have hcon' : distribFun T f t ≤ ENNReal.ofReal x := not_lt.mp hcon
    have : decreasingRearrange T f x ≤ t :=
      sInf_le (by simp only [mem_setOf_eq]; exact hcon')
    exact absurd hlt (not_lt.mpr this)
  · intro hlt
    -- `D (f♯ x) ≤ ofReal x < D t`; if `f♯ x ≤ t` then `D t ≤ D (f♯ x)`, contradiction.
    by_contra hcon
    have hcon' : decreasingRearrange T f x ≤ t := not_lt.mp hcon
    have h1 : distribFun T f t ≤ distribFun T f (decreasingRearrange T f x) :=
      distribFun_antitone hcon'
    have h2 : distribFun T f (decreasingRearrange T f x) ≤ ENNReal.ofReal x :=
      distribFun_decreasingRearrange_le x
    exact absurd hlt (not_lt.mpr (le_trans h1 h2))

/-- **Equimeasurability**: the decreasing rearrangement has the same distribution
function as `f`. The hypothesis `distribFun T f t ≤ ofReal T` (automatic, see
`distribFun_le_ofReal_T`) is recorded explicitly for clarity. -/
theorem distribFun_decreasingRearrange (hT : 0 ≤ T) (t : ℝ≥0∞) :
    distribFun T (decreasingRearrange T f) t = distribFun T f t := by
  -- By the fundamental relation, the super-level set of `f♯` is `{x | ofReal x < D t}`.
  have hDtop : distribFun T f t ≠ ⊤ := distribFun_ne_top t
  have hseteq : {x ∈ Icc (0 : ℝ) T | t < decreasingRearrange T f x} =
      Ico (0 : ℝ) (distribFun T f t).toReal := by
    ext x
    simp only [mem_setOf_eq, mem_Ico]
    rw [lt_decreasingRearrange_iff]
    constructor
    · rintro ⟨⟨hx0, _⟩, hlt⟩
      refine ⟨hx0, ?_⟩
      rwa [← ENNReal.ofReal_toReal hDtop, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0] at hlt
    · rintro ⟨hx0, hxlt⟩
      -- `x < (D t).toReal ≤ T`, so `x ∈ Icc 0 T`, and `ofReal x < D t`.
      have hxT : x ≤ T := by
        have : (distribFun T f t).toReal ≤ T := by
          have := distribFun_le_ofReal_T (T := T) (f := f) t
          calc (distribFun T f t).toReal ≤ (ENNReal.ofReal T).toReal :=
                ENNReal.toReal_mono ofReal_ne_top this
            _ = T := ENNReal.toReal_ofReal hT
        linarith
      refine ⟨⟨hx0, hxT⟩, ?_⟩
      rw [← ENNReal.ofReal_toReal hDtop, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0]
      exact hxlt
  rw [distribFun, hseteq, Real.volume_Ico, sub_zero, ENNReal.ofReal_toReal hDtop]

/-- The decreasing rearrangement is antitone in `x`: larger `x` enlarges the
defining set `{t | distribFun T f t ≤ ofReal x}`, hence lowers its infimum. -/
theorem decreasingRearrange_antitone : Antitone (decreasingRearrange T f) := by
  intro x y hxy
  apply sInf_le_sInf
  intro t ht
  simp only [mem_setOf_eq] at ht ⊢
  exact le_trans ht (ENNReal.ofReal_le_ofReal hxy)

/-- The decreasing rearrangement is measurable (being antitone). -/
theorem measurable_decreasingRearrange : Measurable (decreasingRearrange T f) :=
  decreasingRearrange_antitone.measurable

/-- The **distribution function of a constant**: the super-level set above `t` is the
whole interval when `t < c` and empty otherwise. -/
theorem distribFun_const (c : ℝ≥0∞) (t : ℝ≥0∞) :
    distribFun T (fun _ => c) t = if t < c then ENNReal.ofReal T else 0 := by
  unfold distribFun
  by_cases h : t < c
  · rw [if_pos h]
    have heq : {x ∈ Icc (0 : ℝ) T | t < (fun _ => c) x} = Icc 0 T := by ext x; simp [h]
    rw [heq, Real.volume_Icc, sub_zero]
  · rw [if_neg h]
    have hempty : {x ∈ Icc (0 : ℝ) T | t < (fun _ => c) x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ => h
    rw [hempty, measure_empty]

/-- The **rearrangement of a constant is the constant**: on `[0, T)` (i.e. for
`0 ≤ x < T`), `(fun _ => c)♯[T] x = c`. The boundary point `x = T` is excluded,
where the rearrangement degenerates to `0`. -/
theorem decreasingRearrange_const (c : ℝ≥0∞) {T : ℝ} {x : ℝ}
    (hx0 : 0 ≤ x) (hxT : x < T) :
    decreasingRearrange T (fun _ => c) x = c := by
  unfold decreasingRearrange
  have hset : {t : ℝ≥0∞ | distribFun T (fun _ => c) t ≤ ENNReal.ofReal x} = Ici c := by
    ext t
    rw [Set.mem_setOf_eq, distribFun_const c t, mem_Ici]
    constructor
    · intro h
      by_contra hc
      rw [not_le] at hc
      rw [if_pos hc] at h
      have : T ≤ x := (ENNReal.ofReal_le_ofReal_iff hx0).mp h
      linarith
    · intro h
      rw [if_neg (not_lt.mpr h)]
      exact zero_le _
  rw [hset, csInf_Ici]

/-- **`ℝ≥0∞`-valued Cavalieri / layer-cake principle on a measurable set.** For a
measurable nonnegative function `g`, the integral over `s` is recovered from the
measures of its super-level sets, weighted over the positive reals. This depends on
`g` only through its distribution function. -/
theorem lintegral_eq_lintegral_meas_lt_ennreal {s : Set ℝ}
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in s, g x) = ∫⁻ t in Ioi (0 : ℝ), volume {x ∈ s | ENNReal.ofReal t < g x} := by
  -- The indicator of the super-level set, viewed pointwise.
  set ind : ℝ → ℝ → ℝ≥0∞ :=
    fun x t => Set.indicator {u : ℝ | ENNReal.ofReal u < g x} (fun _ => (1 : ℝ≥0∞)) t with hind
  -- Pointwise Cavalieri: `g x = ∫⁻ t in Ioi 0, ind x t`.
  have hpt : ∀ x, g x = ∫⁻ t in Ioi (0 : ℝ), ind x t := by
    intro x
    have hmeas : MeasurableSet {u : ℝ | ENNReal.ofReal u < g x} :=
      measurableSet_lt (Measurable.ennreal_ofReal measurable_id) measurable_const
    simp only [hind]
    rw [lintegral_indicator hmeas, lintegral_const,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
    rcases eq_top_or_lt_top (g x) with hgx | hfin
    · have hset : {u : ℝ | ENNReal.ofReal u < g x} ∩ Ioi 0 = Ioi 0 := by
        ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, hgx, ofReal_lt_top, true_and]
      rw [Measure.restrict_apply hmeas, hset, Real.volume_Ioi, hgx]
    · have hset : {u : ℝ | ENNReal.ofReal u < g x} ∩ Ioi 0 = Ioo 0 (g x).toReal := by
        ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
        constructor
        · rintro ⟨hc, hu⟩
          exact ⟨hu, by rw [← ENNReal.ofReal_toReal hfin.ne,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le] at hc; exact hc⟩
        · rintro ⟨hu, hlt⟩
          exact ⟨by rw [← ENNReal.ofReal_toReal hfin.ne,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le]; exact hlt, hu⟩
      rw [Measure.restrict_apply hmeas, hset, Real.volume_Ioo, sub_zero,
        ENNReal.ofReal_toReal hfin.ne]
  -- Joint measurability of `(x, t) ↦ ind x t`.
  have hjoint : Measurable (Function.uncurry ind) := by
    have heq : Function.uncurry ind
         = Set.indicator {p : ℝ × ℝ | ENNReal.ofReal p.2 < g p.1} (fun _ => (1 : ℝ≥0∞)) := by
      ext ⟨x, t⟩; simp only [hind, Function.uncurry, Set.indicator, mem_setOf_eq]
    rw [heq]
    exact (Measurable.indicator measurable_const
      (measurableSet_lt (Measurable.ennreal_ofReal measurable_snd) (hg.comp measurable_fst)))
  -- Inner integral over `s` recovers the super-level measure.
  have hinner : ∀ t, (∫⁻ x in s, ind x t) = volume {x ∈ s | ENNReal.ofReal t < g x} := by
    intro t
    have hfn : (fun x => ind x t) =
        Set.indicator {x | ENNReal.ofReal t < g x} (fun _ => (1 : ℝ≥0∞)) := by
      ext x; simp only [hind, Set.indicator, mem_setOf_eq]
    have hmst : MeasurableSet {x | ENNReal.ofReal t < g x} :=
      measurableSet_lt (Measurable.ennreal_ofReal measurable_const) hg
    rw [hfn, lintegral_indicator hmst, lintegral_const,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
        Measure.restrict_apply hmst, inter_comm]
    rfl
  calc (∫⁻ x in s, g x)
      = ∫⁻ x in s, ∫⁻ t in Ioi (0 : ℝ), ind x t := lintegral_congr (fun x => hpt x)
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in s, ind x t :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), volume {x ∈ s | ENNReal.ofReal t < g x} :=
        lintegral_congr (fun t => hinner t)

/-- **Integral preservation / Hardy–Littlewood equimeasurability.** The decreasing
rearrangement preserves the Lebesgue integral over `Icc 0 T`:
`∫⁻ x in Icc 0 T, f♯ x = ∫⁻ x in Icc 0 T, f x`. This is the `p = 1` energy identity.
Requires `f` measurable and `0 ≤ T`. -/
theorem lintegral_decreasingRearrange_eq (hT : 0 ≤ T) (hf : Measurable f) :
    (∫⁻ x in Icc (0 : ℝ) T, decreasingRearrange T f x) = ∫⁻ x in Icc (0 : ℝ) T, f x := by
  rw [lintegral_eq_lintegral_meas_lt_ennreal measurable_decreasingRearrange,
      lintegral_eq_lintegral_meas_lt_ennreal hf]
  refine lintegral_congr (fun t => ?_)
  exact distribFun_decreasingRearrange hT (ENNReal.ofReal t)

/-- **Energy / `p`-th power preservation.** For `0 < p`, the decreasing rearrangement
preserves the `p`-energy `∫⁻ (f x)^p` over `Icc 0 T`; in particular the `p = 1, 2`
cases relevant to the conformal modulus. Requires `f` measurable and `0 ≤ T`. -/
theorem lintegral_rpow_decreasingRearrange_eq (hT : 0 ≤ T) (hf : Measurable f) {p : ℝ}
    (hp : 0 < p) :
    (∫⁻ x in Icc (0 : ℝ) T, decreasingRearrange T f x ^ p)
      = ∫⁻ x in Icc (0 : ℝ) T, f x ^ p := by
  have hmeasf : Measurable (fun x => f x ^ p) := hf.pow_const p
  have hmeasr : Measurable (fun x => decreasingRearrange T f x ^ p) :=
    measurable_decreasingRearrange.pow_const p
  rw [lintegral_eq_lintegral_meas_lt_ennreal hmeasr,
      lintegral_eq_lintegral_meas_lt_ennreal hmeasf]
  refine lintegral_congr (fun t => ?_)
  -- Super-level set of `g^p` is the super-level set of `g` at the shifted threshold.
  have hrw : ∀ g : ℝ → ℝ≥0∞,
      {x ∈ Icc (0 : ℝ) T | ENNReal.ofReal t < g x ^ p}
        = {x ∈ Icc (0 : ℝ) T | (ENNReal.ofReal t) ^ (p⁻¹) < g x} := by
    intro g
    ext x
    simp only [mem_setOf_eq, and_congr_right_iff]
    intro _
    constructor
    · intro h
      have := ENNReal.rpow_lt_rpow h (by positivity : (0:ℝ) < p⁻¹)
      rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one] at this
    · intro h
      have := ENNReal.rpow_lt_rpow h hp
      rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one] at this
  rw [hrw (decreasingRearrange T f), hrw f]
  exact distribFun_decreasingRearrange hT ((ENNReal.ofReal t) ^ (p⁻¹))

/-! ### The Hardy–Littlewood integral rearrangement inequality

We now prove the **Hardy–Littlewood inequality** stating that rearranging two
nonnegative functions to be decreasing *maximizes* the integral of their product:
`∫⁻ f * g ≤ ∫⁻ f♯ * g♯`.

The argument is the classical **layer-cake / bathtub** method:
`f x * g x = ∫₀^∞∫₀^∞ 1_{a < f x} 1_{b < g x} da db`, so integrating over `x` and
swapping order (Tonelli) gives
`∫⁻ f * g = ∫₀^∞∫₀^∞ volume({f > a} ∩ {g > b}) da db`.

For the original functions, `volume({f > a} ∩ {g > b}) ≤ min (D f a) (D g b)`, while
for the decreasing rearrangements the super-level sets are **left-anchored intervals**
`Ico 0 (D · ·).toReal`, which are nested, so their intersection has measure *exactly*
`min (D f♯ a) (D g♯ b) = min (D f a) (D g b)` by equimeasurability. Pointwise
domination of the integrands plus monotonicity of `∫⁻` closes the inequality. -/

/-- **Product layer-cake / double Cavalieri principle.** For measurable nonnegative
functions `f, g : ℝ → ℝ≥0∞` and a measurable set `s`, the integral of the product is
recovered from the measures of the joint super-level sets, weighted over the positive
quadrant:
`∫⁻ x in s, f x * g x = ∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, volume {x ∈ s | a < f x ∧ b < g x}`
(with thresholds `ofReal a`, `ofReal b`). This depends on `f, g` only through their
joint distribution. -/
theorem lintegral_mul_eq_lintegral_meas_lt_ennreal {s : Set ℝ}
    {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in s, f x * g x)
      = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ),
          volume {x ∈ s | ENNReal.ofReal a < f x ∧ ENNReal.ofReal b < g x} := by
  -- Pointwise indicators of the two super-level sets, in the threshold variables.
  set indF : ℝ → ℝ → ℝ≥0∞ :=
    fun x a => Set.indicator {u : ℝ | ENNReal.ofReal u < f x} (fun _ => (1 : ℝ≥0∞)) a with hindF
  set indG : ℝ → ℝ → ℝ≥0∞ :=
    fun x b => Set.indicator {u : ℝ | ENNReal.ofReal u < g x} (fun _ => (1 : ℝ≥0∞)) b with hindG
  -- Pointwise Cavalieri for each factor (the `Ioi 0` layer-cake).
  have hptF : ∀ x, f x = ∫⁻ a in Ioi (0 : ℝ), indF x a := by
    intro x
    have hmeas : MeasurableSet {u : ℝ | ENNReal.ofReal u < f x} :=
      measurableSet_lt (Measurable.ennreal_ofReal measurable_id) measurable_const
    simp only [hindF]
    rw [lintegral_indicator hmeas, lintegral_const,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
    rcases eq_top_or_lt_top (f x) with hgx | hfin
    · have hset : {u : ℝ | ENNReal.ofReal u < f x} ∩ Ioi 0 = Ioi 0 := by
        ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, hgx, ofReal_lt_top, true_and]
      rw [Measure.restrict_apply hmeas, hset, Real.volume_Ioi, hgx]
    · have hset : {u : ℝ | ENNReal.ofReal u < f x} ∩ Ioi 0 = Ioo 0 (f x).toReal := by
        ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
        constructor
        · rintro ⟨hc, hu⟩
          exact ⟨hu, by rw [← ENNReal.ofReal_toReal hfin.ne,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le] at hc; exact hc⟩
        · rintro ⟨hu, hlt⟩
          exact ⟨by rw [← ENNReal.ofReal_toReal hfin.ne,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le]; exact hlt, hu⟩
      rw [Measure.restrict_apply hmeas, hset, Real.volume_Ioo, sub_zero,
        ENNReal.ofReal_toReal hfin.ne]
  have hptG : ∀ x, g x = ∫⁻ b in Ioi (0 : ℝ), indG x b := by
    intro x
    have hmeas : MeasurableSet {u : ℝ | ENNReal.ofReal u < g x} :=
      measurableSet_lt (Measurable.ennreal_ofReal measurable_id) measurable_const
    simp only [hindG]
    rw [lintegral_indicator hmeas, lintegral_const,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
    rcases eq_top_or_lt_top (g x) with hgx | hfin
    · have hset : {u : ℝ | ENNReal.ofReal u < g x} ∩ Ioi 0 = Ioi 0 := by
        ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, hgx, ofReal_lt_top, true_and]
      rw [Measure.restrict_apply hmeas, hset, Real.volume_Ioi, hgx]
    · have hset : {u : ℝ | ENNReal.ofReal u < g x} ∩ Ioi 0 = Ioo 0 (g x).toReal := by
        ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
        constructor
        · rintro ⟨hc, hu⟩
          exact ⟨hu, by rw [← ENNReal.ofReal_toReal hfin.ne,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le] at hc; exact hc⟩
        · rintro ⟨hu, hlt⟩
          exact ⟨by rw [← ENNReal.ofReal_toReal hfin.ne,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le]; exact hlt, hu⟩
      rw [Measure.restrict_apply hmeas, hset, Real.volume_Ioo, sub_zero,
        ENNReal.ofReal_toReal hfin.ne]
  -- Pointwise: `f x * g x = ∫⁻ a, ∫⁻ b, indF x a * indG x b`.
  have hptMul : ∀ x, f x * g x
      = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), indF x a * indG x b := by
    intro x
    -- measurability of the threshold indicators for fixed `x`
    have hmF : Measurable (fun a => indF x a) := by
      simp only [hindF]
      exact Measurable.indicator measurable_const
        (measurableSet_lt (Measurable.ennreal_ofReal measurable_id) measurable_const)
    have hmG : Measurable (fun b => indG x b) := by
      simp only [hindG]
      exact Measurable.indicator measurable_const
        (measurableSet_lt (Measurable.ennreal_ofReal measurable_id) measurable_const)
    calc f x * g x
        = (∫⁻ a in Ioi (0 : ℝ), indF x a) * (∫⁻ b in Ioi (0 : ℝ), indG x b) := by
          rw [hptF x, hptG x]
      _ = ∫⁻ a in Ioi (0 : ℝ), indF x a * (∫⁻ b in Ioi (0 : ℝ), indG x b) := by
          rw [lintegral_mul_const _ hmF]
      _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), indF x a * indG x b := by
          refine lintegral_congr (fun a => ?_)
          rw [lintegral_const_mul _ hmG]
  -- Joint measurability of `(x, a) ↦ indF x a` and `(x, b) ↦ indG x b`.
  have hjointF : Measurable (Function.uncurry indF) := by
    have heq : Function.uncurry indF
         = Set.indicator {p : ℝ × ℝ | ENNReal.ofReal p.2 < f p.1} (fun _ => (1 : ℝ≥0∞)) := by
      ext ⟨x, a⟩; simp only [hindF, Function.uncurry, Set.indicator, mem_setOf_eq]
    rw [heq]
    exact (Measurable.indicator measurable_const
      (measurableSet_lt (Measurable.ennreal_ofReal measurable_snd) (hf.comp measurable_fst)))
  have hjointG : Measurable (Function.uncurry indG) := by
    have heq : Function.uncurry indG
         = Set.indicator {p : ℝ × ℝ | ENNReal.ofReal p.2 < g p.1} (fun _ => (1 : ℝ≥0∞)) := by
      ext ⟨x, b⟩; simp only [hindG, Function.uncurry, Set.indicator, mem_setOf_eq]
    rw [heq]
    exact (Measurable.indicator measurable_const
      (measurableSet_lt (Measurable.ennreal_ofReal measurable_snd) (hg.comp measurable_fst)))
  -- Joint measurability of `(x, (a, b)) ↦ indF x a * indG x b` over `ℝ × (ℝ × ℝ)`.
  have hjoint3 : Measurable
      (Function.uncurry (fun x p => indF x p.1 * indG x p.2 : ℝ → ℝ × ℝ → ℝ≥0∞)) := by
    have h1 : Measurable (fun q : ℝ × (ℝ × ℝ) => indF q.1 q.2.1) :=
      hjointF.comp (measurable_fst.prodMk measurable_snd.fst)
    have h2 : Measurable (fun q : ℝ × (ℝ × ℝ) => indG q.1 q.2.2) :=
      hjointG.comp (measurable_fst.prodMk measurable_snd.snd)
    exact h1.mul h2
  -- Inner double integral over `s` recovers the joint super-level measure.
  have hinner : ∀ a b, (∫⁻ x in s, indF x a * indG x b)
      = volume {x ∈ s | ENNReal.ofReal a < f x ∧ ENNReal.ofReal b < g x} := by
    intro a b
    have hfn : (fun x => indF x a * indG x b)
        = Set.indicator {x | ENNReal.ofReal a < f x ∧ ENNReal.ofReal b < g x}
            (fun _ => (1 : ℝ≥0∞)) := by
      ext x
      simp only [hindF, hindG, Set.indicator, mem_setOf_eq]
      by_cases hA : ENNReal.ofReal a < f x <;> by_cases hB : ENNReal.ofReal b < g x <;>
        simp [hA, hB]
    have hms : MeasurableSet {x | ENNReal.ofReal a < f x ∧ ENNReal.ofReal b < g x} :=
      (measurableSet_lt (Measurable.ennreal_ofReal measurable_const) hf).inter
        (measurableSet_lt (Measurable.ennreal_ofReal measurable_const) hg)
    rw [hfn, lintegral_indicator hms, lintegral_const,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
        Measure.restrict_apply hms, inter_comm]
    rfl
  -- AE-measurability facts for the two Tonelli swaps (over restricted measures).
  -- Swap 1 moves `x` past `a`; Swap 2 moves `x` past `b`.
  have hae_xa : AEMeasurable
      (Function.uncurry (fun x a => ∫⁻ b in Ioi (0:ℝ), indF x a * indG x b : ℝ → ℝ → ℝ≥0∞))
      ((volume.restrict s).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aemeasurable ?_
    -- `(x,a) ↦ ∫⁻ b, indF x a * indG x b` is measurable
    have hmeas3 : Measurable (Function.uncurry
        (fun (q : ℝ × ℝ) (b : ℝ) => indF q.1 q.2 * indG q.1 b)) := by
      have h1 : Measurable (fun w : (ℝ × ℝ) × ℝ => indF w.1.1 w.1.2) :=
        hjointF.comp (measurable_fst.fst.prodMk measurable_fst.snd)
      have h2 : Measurable (fun w : (ℝ × ℝ) × ℝ => indG w.1.1 w.2) :=
        hjointG.comp (measurable_fst.fst.prodMk measurable_snd)
      exact h1.mul h2
    exact Measurable.lintegral_prod_right
      (f := fun (q : ℝ × ℝ) (b : ℝ) => indF q.1 q.2 * indG q.1 b) hmeas3
  -- Assemble: integrate the pointwise identity over `s`, then swap order.
  calc (∫⁻ x in s, f x * g x)
      = ∫⁻ x in s, ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), indF x a * indG x b :=
        lintegral_congr (fun x => hptMul x)
    -- Swap 1: move `x` past `a`.
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ x in s, ∫⁻ b in Ioi (0 : ℝ), indF x a * indG x b :=
        lintegral_lintegral_swap hae_xa
    -- Swap 2: inside, move `x` past `b`.
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ), ∫⁻ x in s, indF x a * indG x b := by
        refine lintegral_congr (fun a => ?_)
        refine lintegral_lintegral_swap ?_
        -- `(x,b) ↦ indF x a * indG x b` is measurable
        refine Measurable.aemeasurable ?_
        have h1 : Measurable (fun w : ℝ × ℝ => indF w.1 a) :=
          (hjointF.comp (measurable_id.prodMk measurable_const)).comp measurable_fst
        have h2 : Measurable (fun w : ℝ × ℝ => indG w.1 w.2) := hjointG
        exact h1.mul h2
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ b in Ioi (0 : ℝ),
          volume {x ∈ s | ENNReal.ofReal a < f x ∧ ENNReal.ofReal b < g x} := by
        refine lintegral_congr (fun a => lintegral_congr (fun b => ?_))
        exact hinner a b

/-- **The super-level set of a decreasing rearrangement is a left-anchored interval.**
For `0 ≤ T`, the set `{x ∈ Icc 0 T | t < f♯ x}` equals `Ico 0 (distribFun T f t).toReal`,
an interval anchored at the left endpoint `0` whose length is the distribution value
`distribFun T f t`. This is the structural fact that makes super-level sets of decreasing
rearrangements *nested*. -/
theorem superlevel_decreasingRearrange_eq_Ico (hT : 0 ≤ T) (t : ℝ≥0∞) :
    {x ∈ Icc (0 : ℝ) T | t < decreasingRearrange T f x}
      = Ico (0 : ℝ) (distribFun T f t).toReal := by
  have hDtop : distribFun T f t ≠ ⊤ := distribFun_ne_top t
  ext x
  simp only [mem_setOf_eq, mem_Ico]
  rw [lt_decreasingRearrange_iff]
  constructor
  · rintro ⟨⟨hx0, _⟩, hlt⟩
    refine ⟨hx0, ?_⟩
    rwa [← ENNReal.ofReal_toReal hDtop, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0] at hlt
  · rintro ⟨hx0, hxlt⟩
    have hxT : x ≤ T := by
      have : (distribFun T f t).toReal ≤ T := by
        have := distribFun_le_ofReal_T (T := T) (f := f) t
        calc (distribFun T f t).toReal ≤ (ENNReal.ofReal T).toReal :=
              ENNReal.toReal_mono ofReal_ne_top this
          _ = T := ENNReal.toReal_ofReal hT
      linarith
    refine ⟨⟨hx0, hxT⟩, ?_⟩
    rw [← ENNReal.ofReal_toReal hDtop, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0]
    exact hxlt

/-- **Joint super-level measure of two decreasing rearrangements equals the minimum.**
Because each super-level set `{f♯ > a}`, `{g♯ > b}` is a left-anchored interval
`Ico 0 (D · ·).toReal`, their intersection is the shorter interval, of measure
`min (D f a) (D g b)`. Equimeasurability `D f♯ = D f` then expresses this in terms of
the original distribution functions. -/
theorem distribFun_inter_decreasingRearrange_eq_min (hT : 0 ≤ T)
    (a b : ℝ≥0∞) :
    volume {x ∈ Icc (0 : ℝ) T |
        a < decreasingRearrange T f x ∧ b < decreasingRearrange T g x}
      = min (distribFun T f a) (distribFun T g b) := by
  have hDfa : distribFun T f a ≠ ⊤ := distribFun_ne_top a
  have hDgb : distribFun T g b ≠ ⊤ := distribFun_ne_top b
  -- The joint super-level set is the intersection of the two left-anchored intervals,
  -- i.e. `Ico 0 (min of the two lengths)`.
  have hseteq : {x ∈ Icc (0 : ℝ) T |
        a < decreasingRearrange T f x ∧ b < decreasingRearrange T g x}
      = Ico (0 : ℝ) (min (distribFun T f a).toReal (distribFun T g b).toReal) := by
    ext x
    have hf' := superlevel_decreasingRearrange_eq_Ico (f := f) hT a
    have hg' := superlevel_decreasingRearrange_eq_Ico (f := g) hT b
    constructor
    · rintro ⟨hxI, hfx, hgx⟩
      have h1 : x ∈ Ico (0:ℝ) (distribFun T f a).toReal := by
        rw [← hf']; exact ⟨hxI, hfx⟩
      have h2 : x ∈ Ico (0:ℝ) (distribFun T g b).toReal := by
        rw [← hg']; exact ⟨hxI, hgx⟩
      exact ⟨h1.1, lt_min h1.2 h2.2⟩
    · rintro ⟨hx0, hxlt⟩
      have hxf : x ∈ Ico (0:ℝ) (distribFun T f a).toReal :=
        ⟨hx0, lt_of_lt_of_le hxlt (min_le_left _ _)⟩
      have hxg : x ∈ Ico (0:ℝ) (distribFun T g b).toReal :=
        ⟨hx0, lt_of_lt_of_le hxlt (min_le_right _ _)⟩
      rw [← hf'] at hxf
      rw [← hg'] at hxg
      exact ⟨hxf.1, hxf.2, hxg.2⟩
  rw [hseteq, Real.volume_Ico, sub_zero]
  -- `ofReal (min p.toReal q.toReal) = min p q` for finite `p, q`.
  have hmin_ne_top : min (distribFun T f a) (distribFun T g b) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfa (min_le_left _ _)
  rw [← ENNReal.toReal_min hDfa hDgb, ENNReal.ofReal_toReal hmin_ne_top]

/-- **Joint super-level measure of two functions is at most the minimum.** The
intersection of two sets has measure at most the measure of either, hence at most their
minimum. -/
theorem distribFun_inter_le_min (a b : ℝ≥0∞) :
    volume {x ∈ Icc (0 : ℝ) T | a < f x ∧ b < g x}
      ≤ min (distribFun T f a) (distribFun T g b) := by
  refine le_min ?_ ?_
  · exact measure_mono (fun x hx => ⟨hx.1, hx.2.1⟩)
  · exact measure_mono (fun x hx => ⟨hx.1, hx.2.2⟩)

/-- **The one-dimensional Hardy–Littlewood integral rearrangement inequality.**
Rearranging two nonnegative measurable functions to be decreasing *maximizes* the
integral of their product:
`∫⁻ x in Icc 0 T, f x * g x ≤ ∫⁻ x in Icc 0 T, f♯ x * g♯ x`.

The proof is the layer-cake / bathtub argument. By the product layer-cake principle,
both sides equal a double integral over the positive quadrant of the joint super-level
measures `volume({· > a} ∩ {· > b})`. For the original functions this measure is bounded
by `min (D f a) (D g b)`; for the decreasing rearrangements it *equals* `min (D f a)
(D g b)` (the super-level sets are nested left-anchored intervals, and `D f♯ = D f` by
equimeasurability). Pointwise domination of the integrands plus monotonicity of `∫⁻`
yields the inequality. Requires `0 ≤ T` and `f, g` measurable. -/
theorem hardyLittlewood_decreasingRearrange (hT : 0 ≤ T)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in Icc (0 : ℝ) T, f x * g x)
      ≤ ∫⁻ x in Icc (0 : ℝ) T,
          decreasingRearrange T f x * decreasingRearrange T g x := by
  rw [lintegral_mul_eq_lintegral_meas_lt_ennreal hf hg,
      lintegral_mul_eq_lintegral_meas_lt_ennreal
        measurable_decreasingRearrange measurable_decreasingRearrange]
  refine lintegral_mono (fun a => ?_)
  refine lintegral_mono (fun b => ?_)
  calc volume {x ∈ Icc (0 : ℝ) T | ENNReal.ofReal a < f x ∧ ENNReal.ofReal b < g x}
      ≤ min (distribFun T f (ENNReal.ofReal a)) (distribFun T g (ENNReal.ofReal b)) :=
        distribFun_inter_le_min (ENNReal.ofReal a) (ENNReal.ofReal b)
    _ = volume {x ∈ Icc (0 : ℝ) T | ENNReal.ofReal a < decreasingRearrange T f x
          ∧ ENNReal.ofReal b < decreasingRearrange T g x} :=
        (distribFun_inter_decreasingRearrange_eq_min hT
          (ENNReal.ofReal a) (ENNReal.ofReal b)).symm

end RiemannDynamics

end
