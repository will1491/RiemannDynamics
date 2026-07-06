/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.Symmetrization.CircularRearrangement
import RiemannDynamics.Analysis.Potential.Subharmonic
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Baernstein star function and the circular Pólya–Szegő inequality

This file begins the development of the **circular Pólya–Szegő inequality**
`dirichletEnergy (circSymm p u) U ≤ dirichletEnergy u U`: the Dirichlet energy does not increase
under circular symmetrization of a ring potential `u`. The chosen route is **Baernstein's star
function**.

For a fixed centre `p` and radius `r`, write `g_r φ = u (p + r e^{i(φ − π)})` for the *angular
profile* on the parameter interval `[0, 2π]` (the geometric angle `φ − π` ranges over `[−π, π]`;
this is the convention of `RiemannDynamics.angularProfile`). Baernstein's star function is the
cumulative integral, over a *centered* sub-arc of half-aperture `θ`, of the symmetric-decreasing
rearrangement `g_r ♯` of that profile:

`starFunction p u r θ = ∫_{[π − θ, π + θ]} (angularProfile p u r) ♯[2π]`.

By the Hardy–Littlewood inequality the value of this centered-arc integral equals the supremum of
`∫_E g_r` over all measurable arcs `E ⊆ [0, 2π]` of measure `2 θ`, which is the classical Baernstein
definition. Working with the rearranged profile makes the object measurable and lets us reuse the
symmetric-rearrangement layer (`RiemannDynamics.decreasingRearrangeSymm` and its equimeasurability
and integral-preservation lemmas).

## Route (why the star function)

The star-function route converts the *energy* inequality `D(u★) ≤ D(u)` into a *subharmonicity*
statement about `u★` — a shape the project's continuous sub-mean-value subharmonic layer
(`RiemannDynamics.SubharmonicOn` and its max / maximum-principle / Poisson-modification API in
`Analysis/Potential/Subharmonic.lean`) is built to express. Crucially `u★` is assembled from circle integrals
of the *harmonic* (hence smooth) ring potential, so it avoids the missing gradient regularity of the
raw circular rearrangement `circSymm` that obstructs the polarization and coarea routes.

## Main definitions

* `RiemannDynamics.starProfile T g θ` — the abstract cumulative integral of the symmetric-decreasing
  rearrangement `g ♯[T]` over the centered arc `[T/2 − θ, T/2 + θ]`.
* `RiemannDynamics.starFunction p u r θ` — the Baernstein star function of `u` at half-aperture `θ`
  on the circle of radius `r` about `p`, i.e. `starProfile (2π) (angularProfile p u r) θ`.

## Main results (first brick)

* `RiemannDynamics.starProfile_zero` — vanishing at zero aperture.
* `RiemannDynamics.monotone_starProfile` — monotonicity of the star profile in the aperture: larger
  arcs give larger (or equal) cumulative integrals.
* `RiemannDynamics.starProfile_le_lintegral` — the star profile is bounded by the whole-circle
  integral of the rearranged profile.
* `RiemannDynamics.monotone_starFunction`, `RiemannDynamics.starFunction_zero` — the same facts for
  the Baernstein star function.
-/

open MeasureTheory Set ENNReal Filter Topology Complex
open scoped Real ENNReal

noncomputable section

namespace RiemannDynamics

variable {T : ℝ} {g : ℝ → ℝ≥0∞}

/-- **The abstract star profile.** For a nonnegative profile `g : ℝ → ℝ≥0∞` on `[0, T]`, the star
profile at half-aperture `θ` is the integral of the symmetric-decreasing rearrangement `g ♯[T]` over
the centered arc `[T/2 − θ, T/2 + θ]`:

`starProfile T g θ = ∫_{Icc (T/2 − θ) (T/2 + θ)} decreasingRearrangeSymm T g`.

By Hardy–Littlewood this equals `sup_{|E| = 2θ} ∫_E g`, the classical Baernstein star value. -/
def starProfile (T : ℝ) (g : ℝ → ℝ≥0∞) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Icc (T / 2 - θ) (T / 2 + θ), decreasingRearrangeSymm T g x

/-- **The Baernstein star function** of `u : ℂ → ℝ` at the point of the circle of radius `r` about
`p` with half-aperture `θ`: the star profile of the angular profile `angularProfile p u r`
(reinterpreted as an extended-real profile via `ENNReal.ofReal`) on the interval `[0, 2π]`. The peak
(`θ = π`) recovers the whole-circle integral; `θ = 0` gives `0`. -/
def starFunction (p : ℂ) (u : ℂ → ℝ) (r : ℝ) (θ : ℝ) : ℝ≥0∞ :=
  starProfile (2 * π)
    (fun φ => ENNReal.ofReal (angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal) θ

/-- At zero aperture the star profile is `0`: the integral over the degenerate arc `[T/2, T/2]`. -/
@[simp] theorem starProfile_zero (T : ℝ) (g : ℝ → ℝ≥0∞) : starProfile T g 0 = 0 := by
  simp only [starProfile, sub_zero, add_zero, Icc_self, Measure.restrict_singleton,
    lintegral_smul_measure]
  simp

/-- **Monotonicity of the star profile in the aperture.** A wider centered arc yields a larger (or
equal) cumulative integral of the (nonnegative) rearranged profile. This is the first structural
property of Baernstein's star function: `u★(r e^{iθ})` is nondecreasing in `θ ∈ [0, π]`. -/
theorem monotone_starProfile (T : ℝ) (g : ℝ → ℝ≥0∞) :
    MonotoneOn (starProfile T g) (Ici 0) := by
  intro a ha b hb hab
  simp only [starProfile]
  apply lintegral_mono_set
  intro x hx
  simp only [mem_Icc] at hx ⊢
  refine ⟨?_, ?_⟩
  · exact le_trans (by linarith [mem_Ici.1 ha, mem_Ici.1 hb]) hx.1
  · exact le_trans hx.2 (by linarith [mem_Ici.1 ha, mem_Ici.1 hb])

/-- The star profile is bounded above by the integral of the rearranged profile over the whole
parameter interval `[0, T]` (attained at half-aperture `θ = T/2`, i.e. `θ = π` for a circle). -/
theorem starProfile_le_lintegral (hθT : θ ≤ T / 2) :
    starProfile T g θ ≤ ∫⁻ x in Icc (0 : ℝ) T, decreasingRearrangeSymm T g x := by
  simp only [starProfile]
  apply lintegral_mono_set
  intro x hx
  simp only [mem_Icc] at hx ⊢
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **The Baernstein star function vanishes at zero aperture.** -/
@[simp] theorem starFunction_zero (p : ℂ) (u : ℂ → ℝ) (r : ℝ) : starFunction p u r 0 = 0 :=
  starProfile_zero _ _

/-- **Monotonicity of the Baernstein star function in the aperture.** For fixed radius `r`, the star
value `u★(r e^{iθ})` is nondecreasing in the half-aperture `θ ∈ [0, π]`. -/
theorem monotone_starFunction (p : ℂ) (u : ℂ → ℝ) (r : ℝ) :
    MonotoneOn (starFunction p u r) (Ici 0) :=
  monotone_starProfile _ _

/-- **The layer-cake identity for the star profile.** For a nonnegative profile `g : ℝ → ℝ≥0∞` on
`[0, T]` (`0 ≤ T`) and a half-aperture `0 ≤ θ ≤ T/2`, the abstract star profile — the integral of
the symmetric-decreasing rearrangement over the centered arc of length `2θ` — equals the layer-cake
integral of `t ↦ min (2θ) (D t)`, where `D = distribFun T g` is the distribution function:

`starProfile T g θ = ∫_{Ioi 0} min (2θ) (distribFun T g (ofReal t)) dt`.

The super-level sets of the symmetric rearrangement are centered open intervals of length `D t`, and
intersecting the centered arc `[T/2 − θ, T/2 + θ]` with such an interval leaves a centered interval
of length `2 · min (θ, D t / 2) = min (2θ, D t)`; the identity is Cavalieri's principle applied to
that measure. -/
theorem starProfile_eq_lintegral_min (hT : 0 ≤ T) (hθ0 : 0 ≤ θ) (hθT : θ ≤ T / 2) :
    starProfile T g θ = ∫⁻ t in Ioi (0 : ℝ),
      min (ENNReal.ofReal (2 * θ)) (distribFun T g (ENNReal.ofReal t)) := by
  -- Intersection of a centered `Icc` and a centered `Ioo` has measure `2 · min` of the radii.
  have hInterMeas : ∀ (a θ₀ ρ : ℝ), 0 ≤ θ₀ → 0 ≤ ρ →
      volume (Icc (a - θ₀) (a + θ₀) ∩ Ioo (a - ρ) (a + ρ)) = ENNReal.ofReal (2 * min θ₀ ρ) := by
    intro a θ₀ ρ hθ₀ hρ
    set m : ℝ := min θ₀ ρ with hm
    have hval : ENNReal.ofReal (2 * m) = volume (Ioo (a - m) (a + m)) := by
      rw [Real.volume_Ioo]; ring_nf
    have hlow : Ioo (a - m) (a + m) ⊆ Icc (a - θ₀) (a + θ₀) ∩ Ioo (a - ρ) (a + ρ) := by
      intro x hx
      have h1 : m ≤ θ₀ := min_le_left _ _
      have h2 : m ≤ ρ := min_le_right _ _
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
    have hupp : Icc (a - θ₀) (a + θ₀) ∩ Ioo (a - ρ) (a + ρ) ⊆ Icc (a - m) (a + m) := by
      intro x hx
      obtain ⟨⟨hI1, hI2⟩, hO1, hO2⟩ := hx
      refine ⟨?_, ?_⟩
      · rcases le_total ρ θ₀ with h | h
        · have : m = ρ := min_eq_right h; rw [this]; linarith
        · have : m = θ₀ := min_eq_left h; rw [this]; linarith
      · rcases le_total ρ θ₀ with h | h
        · have : m = ρ := min_eq_right h; rw [this]; linarith
        · have : m = θ₀ := min_eq_left h; rw [this]; linarith
    have hle2 : volume (Icc (a - θ₀) (a + θ₀) ∩ Ioo (a - ρ) (a + ρ))
        ≤ volume (Icc (a - m) (a + m)) := measure_mono hupp
    have hIcc : volume (Icc (a - m) (a + m)) = ENNReal.ofReal (2 * m) := by
      rw [Real.volume_Icc]; ring_nf
    exact le_antisymm (le_trans hle2 (le_of_eq hIcc)) (by rw [hval]; exact measure_mono hlow)
  have harc : Icc (T / 2 - θ) (T / 2 + θ) ⊆ Icc (0 : ℝ) T :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [starProfile, lintegral_eq_lintegral_meas_lt_ennreal measurable_decreasingRearrangeSymm]
  refine lintegral_congr (fun t => ?_)
  have hsuper :
      {x ∈ Icc (T / 2 - θ) (T / 2 + θ) | ENNReal.ofReal t < decreasingRearrangeSymm T g x}
        = Icc (T / 2 - θ) (T / 2 + θ)
          ∩ {x ∈ Icc (0 : ℝ) T | ENNReal.ofReal t < decreasingRearrangeSymm T g x} := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨hxa, hlt⟩; exact ⟨hxa, harc hxa, hlt⟩
    · rintro ⟨hxa, _, hlt⟩; exact ⟨hxa, hlt⟩
  rw [hsuper, superlevel_decreasingRearrangeSymm_eq_Ioo hT (ENNReal.ofReal t)]
  set D : ℝ := (distribFun T g (ENNReal.ofReal t)).toReal with hDdef
  have hDnn : 0 ≤ D := ENNReal.toReal_nonneg
  have hmeas : volume (Icc (T / 2 - θ) (T / 2 + θ) ∩ Ioo (T / 2 - D / 2) (T / 2 + D / 2))
      = ENNReal.ofReal (2 * min θ (D / 2)) := hInterMeas (T / 2) θ (D / 2) hθ0 (by linarith)
  rw [hmeas]
  have harith : 2 * min θ (D / 2) = min (2 * θ) D := by
    rcases le_total θ (D / 2) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring
  rw [harith, ENNReal.ofReal_min, hDdef, ENNReal.ofReal_toReal (distribFun_ne_top _)]

/-- **Prescribed-measure measurable subset of a bounded set.** For a measurable set `A ⊆ Icc a b`
and a target `0 ≤ m ≤ |A|`, there is a measurable subset `B ⊆ A` of measure exactly `ofReal m`. The
proof is a one-dimensional intermediate-value argument on the 1-Lipschitz, continuous, monotone map
`x ↦ (volume (A ∩ Iic x)).toReal`, which runs from `0` (at `x = a`) to `|A|` (at `x = b`). -/
theorem exists_measurableSet_subset_volume {a b : ℝ} (hab : a ≤ b) (A : Set ℝ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc a b) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ENNReal.ofReal m ≤ volume A) :
    ∃ B ⊆ A, MeasurableSet B ∧ volume B = ENNReal.ofReal m := by
  have hAfin : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hAsub)
    rw [Real.volume_Icc]; exact ofReal_ne_top
  set G : ℝ → ℝ := fun x => (volume (A ∩ Iic x)).toReal with hG
  have hAIicfin : ∀ x, volume (A ∩ Iic x) ≠ ⊤ :=
    fun x => ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)
  have hGlip : ∀ x y : ℝ, x ≤ y → G y - G x ≤ y - x := by
    intro x y hxy
    have hsplit : A ∩ Iic y ⊆ (A ∩ Iic x) ∪ Ioc x y := by
      intro z hz
      rcases le_or_gt z x with h | h
      · exact Or.inl ⟨hz.1, h⟩
      · exact Or.inr ⟨h, hz.2⟩
    have hstep : volume (A ∩ Iic y) ≤ volume (A ∩ Iic x) + ENNReal.ofReal (y - x) := by
      calc volume (A ∩ Iic y) ≤ volume ((A ∩ Iic x) ∪ Ioc x y) := measure_mono hsplit
        _ ≤ volume (A ∩ Iic x) + volume (Ioc x y) := measure_union_le _ _
        _ = volume (A ∩ Iic x) + ENNReal.ofReal (y - x) := by rw [Real.volume_Ioc]
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAIicfin x, ofReal_ne_top⟩) hstep
    rw [ENNReal.toReal_add (hAIicfin x) ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at this
    simp only [hG]; linarith
  have hGmono : Monotone G := fun x y hxy => ENNReal.toReal_mono (hAIicfin y)
    (measure_mono (inter_subset_inter_right A (Iic_subset_Iic.mpr hxy)))
  have hGcont : Continuous G := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε, hε, fun y hxy => ?_⟩
    rw [Real.dist_eq] at hxy ⊢
    rcases le_total x y with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr (hGmono h))]
      calc G y - G x ≤ y - x := hGlip x y h
        _ = |y - x| := (abs_of_nonneg (by linarith)).symm
        _ < ε := hxy
    · rw [abs_of_nonpos (by linarith [sub_nonneg.mpr (hGmono h)])]
      calc -(G y - G x) = G x - G y := by ring
        _ ≤ x - y := hGlip y x h
        _ = |y - x| := by rw [abs_sub_comm]; exact (abs_of_nonneg (by linarith)).symm
        _ < ε := hxy
  have hGa : G a = 0 := by
    simp only [hG]
    have hsub0 : A ∩ Iic a ⊆ {a} :=
      fun z hz => le_antisymm hz.2 (hAsub hz.1).1
    rw [measure_mono_null hsub0 (measure_singleton a), ENNReal.toReal_zero]
  have hGb : G b = (volume A).toReal := by
    have hAb : A ∩ Iic b = A := inter_eq_self_of_subset_left (fun z hz => (hAsub hz).2)
    simp only [hG, hAb]
  have hmle : m ≤ (volume A).toReal := by
    rw [← ENNReal.toReal_ofReal hm0]; exact ENNReal.toReal_mono hAfin hm
  have hmem : m ∈ Icc (G a) (G b) := by rw [hGa, hGb]; exact ⟨hm0, hmle⟩
  obtain ⟨x, hxmem, hGx⟩ := intermediate_value_Icc hab hGcont.continuousOn hmem
  refine ⟨A ∩ Iic x, inter_subset_left, hA.inter measurableSet_Iic, ?_⟩
  rw [← (show (volume (A ∩ Iic x)).toReal = m from hGx), ENNReal.ofReal_toReal (hAIicfin x)]

/-- **The extremal attaining set for the star profile.** For a measurable nonnegative profile
`g : ℝ → ℝ≥0∞` and a half-aperture `0 ≤ θ ≤ T/2` on `[0, T]` (`0 < T`), there is a *genuine*
measurable set `E ⊆ [0, T]` of measure exactly `2θ` on which the integral of `g` equals the star
profile:

`∫⁻_E g = starProfile T g θ`.

Explicitly `E = {g > c} ∪ B` where `c = g♯(2θ)` is the rearrangement value at `2θ` and `B` is a
subset of the level set `{g = c}` of the exact deficit measure `2θ − |{g > c}|`, produced by a
one-dimensional intermediate-value argument on `x ↦ volume ({g = c} ∩ Iic x)`. The super-level
measures of this `E` equal `min (2θ) (D t)` at every level `t` (`D` the distribution function), so
its layer-cake integral is the layer-cake integral of the star profile.

This upgrades the supremum characterisation `starProfile_eq_iSup_setLIntegral` to an *attained*
equality, the extremality fact underlying `arcIntegral_eq_starPlane_extremal`. -/
theorem exists_attaining_set (hT : 0 < T) (hg : Measurable g) (hθ0 : 0 ≤ θ) (hθT : θ ≤ T / 2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) T
      ∧ volume E = ENNReal.ofReal (2 * θ) ∧ (∫⁻ x in E, g x) = starProfile T g θ := by
  have hTnn : (0 : ℝ) ≤ T := hT.le
  -- Layer-cake identity: `starProfile = ∫ min (2θ) (D t)`.
  have hStarMin : starProfile T g θ = ∫⁻ t in Ioi (0 : ℝ),
      min (ENNReal.ofReal (2 * θ)) (distribFun T g (ENNReal.ofReal t)) :=
    starProfile_eq_lintegral_min hTnn hθ0 hθT
  -- Lower bound on `{c ≤ g}` via a sequence of levels increasing to `c`.
  have hLower : ∀ c : ℝ≥0∞, (∀ t : ℝ≥0∞, t < c → ENNReal.ofReal (2 * θ) < distribFun T g t) →
      ENNReal.ofReal (2 * θ) ≤ volume {x ∈ Icc (0 : ℝ) T | c ≤ g x} := by
    intro c hc
    rcases eq_or_ne c 0 with hc0 | hc0
    · have hset : {x ∈ Icc (0 : ℝ) T | c ≤ g x} = Icc (0 : ℝ) T := by
        ext x; simp only [mem_setOf_eq, hc0, zero_le, and_true]
      rw [hset, Real.volume_Icc, sub_zero]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · obtain ⟨u, humono, humem, hutend⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr hc0)
      set s : ℕ → Set ℝ := fun n => {x ∈ Icc (0 : ℝ) T | u n < g x} with hs
      have hsmeas : ∀ n, MeasurableSet (s n) :=
        fun n => measurableSet_Icc.inter (measurableSet_lt measurable_const hg)
      have hsanti : Antitone s :=
        fun i j hij x hx => ⟨hx.1, lt_of_le_of_lt (humono.monotone hij) hx.2⟩
      have hsfin : ∃ n, volume (s n) ≠ ⊤ := by
        refine ⟨0, ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))⟩
        rw [Real.volume_Icc]; exact ofReal_ne_top
      have hInter : ⋂ n, s n = {x ∈ Icc (0 : ℝ) T | c ≤ g x} := by
        ext x
        simp only [mem_iInter, hs, mem_setOf_eq]
        constructor
        · intro h; exact ⟨(h 0).1, le_of_tendsto' hutend (fun n => (h n).2.le)⟩
        · rintro ⟨hxI, hxc⟩ n; exact ⟨hxI, lt_of_lt_of_le (humem n).2 hxc⟩
      have htend : Tendsto (fun n => volume (s n)) atTop (𝓝 (volume (⋂ n, s n))) :=
        tendsto_measure_iInter_atTop (fun n => (hsmeas n).nullMeasurableSet) hsanti hsfin
      rw [hInter] at htend
      exact ge_of_tendsto' htend (fun n => (hc (u n) (humem n).2).le)
  -- Build the attaining set `E = {g > c} ∪ B`.
  set c : ℝ≥0∞ := decreasingRearrange T g (2 * θ) with hcdef
  have hP1 : distribFun T g c ≤ ENNReal.ofReal (2 * θ) :=
    distribFun_decreasingRearrange_le (2 * θ)
  have hlt : ∀ t : ℝ≥0∞, t < c → ENNReal.ofReal (2 * θ) < distribFun T g t := by
    intro t ht
    have := (lt_decreasingRearrange_iff (2 * θ) t).mp ht
    rwa [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat] at this ⊢
  have hP2 : ENNReal.ofReal (2 * θ) ≤ volume {x ∈ Icc (0 : ℝ) T | c ≤ g x} := hLower c hlt
  set dc : ℝ := (distribFun T g c).toReal with hdcdef
  have hdcnn : 0 ≤ dc := ENNReal.toReal_nonneg
  have hdc_le : dc ≤ 2 * θ := by
    rw [hdcdef, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * θ)]
    exact ENNReal.toReal_mono ofReal_ne_top hP1
  set deficit : ℝ := 2 * θ - dc with hdefdef
  have hdefnn : 0 ≤ deficit := by rw [hdefdef]; linarith
  set super : Set ℝ := {x ∈ Icc (0 : ℝ) T | c < g x} with hsuperdef
  set atom : Set ℝ := {x ∈ Icc (0 : ℝ) T | g x = c} with hatomdef
  have hsupermeas : MeasurableSet super :=
    measurableSet_Icc.inter (measurableSet_lt measurable_const hg)
  have hatommeas : MeasurableSet atom :=
    measurableSet_Icc.inter (measurableSet_eq_fun hg measurable_const)
  have hsupervol : volume super = ENNReal.ofReal dc := by
    rw [hsuperdef]; change distribFun T g c = _
    rw [hdcdef, ENNReal.ofReal_toReal (distribFun_ne_top c)]
  have hcleq : {x ∈ Icc (0 : ℝ) T | c ≤ g x} = super ∪ atom := by
    ext x
    simp only [hsuperdef, hatomdef, mem_setOf_eq, mem_union]
    constructor
    · rintro ⟨hxI, hle⟩
      rcases eq_or_lt_of_le hle with h | h
      · exact Or.inr ⟨hxI, h.symm⟩
      · exact Or.inl ⟨hxI, h⟩
    · rintro (⟨hxI, h⟩ | ⟨hxI, h⟩)
      · exact ⟨hxI, h.le⟩
      · exact ⟨hxI, h.ge⟩
  have hdisj : Disjoint super atom := by
    rw [Set.disjoint_left]
    rintro x ⟨_, h1⟩ ⟨_, h2⟩
    exact absurd h2 (ne_of_gt h1)
  have hatomvol : ENNReal.ofReal deficit ≤ volume atom := by
    have hchain : ENNReal.ofReal (2 * θ) ≤ volume super + volume atom := by
      rw [← measure_union' hdisj hsupermeas, ← hcleq]; exact hP2
    rw [hsupervol] at hchain
    have hstep : ENNReal.ofReal (2 * θ) - ENNReal.ofReal dc ≤ volume atom :=
      tsub_le_iff_left.mpr hchain
    rwa [← ENNReal.ofReal_sub _ hdcnn, ← hdefdef] at hstep
  obtain ⟨B, hBsub, hBmeas, hBvol⟩ :=
    exists_measurableSet_subset_volume hTnn atom hatommeas (fun x hx => hx.1) hdefnn hatomvol
  set E : Set ℝ := super ∪ B with hEdef
  have hEmeas : MeasurableSet E := hsupermeas.union hBmeas
  have hEsub : E ⊆ Icc (0 : ℝ) T := by
    rw [hEdef]
    exact union_subset (fun x hx => hx.1) (fun x hx => (hBsub hx).1)
  have hEdisj : Disjoint super B := Set.disjoint_of_subset_right hBsub hdisj
  have hEvol : volume E = ENNReal.ofReal (2 * θ) := by
    rw [hEdef, measure_union' hEdisj hsupermeas, hsupervol, hBvol,
        ← ENNReal.ofReal_add hdcnn hdefnn]
    congr 1; rw [hdefdef]; ring
  have hkey : ∀ t : ℝ, volume {x ∈ E | ENNReal.ofReal t < g x}
      = min (ENNReal.ofReal (2 * θ)) (distribFun T g (ENNReal.ofReal t)) := by
    intro t
    rcases le_or_gt c (ENNReal.ofReal t) with hct | hct
    · have hset : {x ∈ E | ENNReal.ofReal t < g x}
          = {x ∈ Icc (0 : ℝ) T | ENNReal.ofReal t < g x} := by
        ext x
        simp only [mem_setOf_eq]
        constructor
        · rintro ⟨hxE, hlt⟩; exact ⟨hEsub hxE, hlt⟩
        · rintro ⟨hxI, hlt⟩
          exact ⟨by rw [hEdef]; exact Or.inl ⟨hxI, lt_of_le_of_lt hct hlt⟩, hlt⟩
      rw [hset]; change distribFun T g (ENNReal.ofReal t) = _
      rw [min_eq_right (le_trans (distribFun_antitone hct) hP1)]
    · have hset : {x ∈ E | ENNReal.ofReal t < g x} = E := by
        ext x
        simp only [mem_setOf_eq]
        rw [and_iff_left_iff_imp]
        intro hxE
        have hxcle : c ≤ g x := by
          rw [hEdef] at hxE
          rcases hxE with ⟨_, h⟩ | hxB
          · exact h.le
          · exact (hBsub hxB).2.ge
        exact lt_of_lt_of_le hct hxcle
      rw [hset, hEvol, min_eq_left (hlt _ hct).le]
  have hinteq : (∫⁻ x in E, g x) = ∫⁻ t in Ioi (0 : ℝ),
        min (ENNReal.ofReal (2 * θ)) (distribFun T g (ENNReal.ofReal t)) := by
    rw [lintegral_eq_lintegral_meas_lt_ennreal hg]
    exact lintegral_congr (fun t => hkey t)
  exact ⟨E, hEmeas, hEsub, hEvol, by rw [hinteq, hStarMin]⟩

/-- **The Hardy–Littlewood characterization of the star profile.** For a measurable nonnegative
profile `g : ℝ → ℝ≥0∞` and a half-aperture `0 ≤ θ ≤ T/2` on `[0, T]` (`0 < T`), the abstract star
profile — the integral of the symmetric-decreasing rearrangement over the centered arc of length
`2θ` — equals the supremum, over all measurable subsets `E ⊆ [0, T]` of measure `2θ`, of the
integral of `g` over `E`:

`starProfile T g θ = ⨆_{|E| = 2θ, E ⊆ [0, T]} ∫⁻_E g`.

This is the classical Baernstein definition `sup_{|E| = 2θ} ∫_E g` of the star function. The proof
routes through the layer-cake identity `starProfile = ∫_{Ioi 0} min (2θ) (D t) dt` (with `D` the
distribution function): the supremum is bounded above by this integral for every admissible `E`
(super-level measures are at most `min (2θ) (D t)`), and it is attained by the explicit extremal set
of `exists_attaining_set`. -/
theorem starProfile_eq_iSup_setLIntegral (hT : 0 < T) (hg : Measurable g) (hθ0 : 0 ≤ θ)
    (hθT : θ ≤ T / 2) :
    starProfile T g θ
      = ⨆ E ∈ {E : Set ℝ | MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) T
          ∧ volume E = ENNReal.ofReal (2 * θ)}, ∫⁻ x in E, g x := by
  have hTnn : (0 : ℝ) ≤ T := hT.le
  -- Layer-cake identity: `starProfile = ∫ min (2θ) (D t)`.
  have hStarMin : starProfile T g θ = ∫⁻ t in Ioi (0 : ℝ),
      min (ENNReal.ofReal (2 * θ)) (distribFun T g (ENNReal.ofReal t)) :=
    starProfile_eq_lintegral_min hTnn hθ0 hθT
  -- Upper bound: `∫_E g ≤ ∫ min (2θ) (D t)` for every admissible `E`.
  have hUpper : ∀ E : Set ℝ, E ⊆ Icc (0 : ℝ) T → volume E = ENNReal.ofReal (2 * θ) →
      (∫⁻ x in E, g x) ≤ ∫⁻ t in Ioi (0 : ℝ),
        min (ENNReal.ofReal (2 * θ)) (distribFun T g (ENNReal.ofReal t)) := by
    intro E hEsub hEvol
    rw [lintegral_eq_lintegral_meas_lt_ennreal hg]
    refine lintegral_mono (fun t => le_min ?_ ?_)
    · calc volume {x ∈ E | ENNReal.ofReal t < g x} ≤ volume E := measure_mono (fun x hx => hx.1)
        _ = ENNReal.ofReal (2 * θ) := hEvol
    · exact measure_mono (fun x hx => ⟨hEsub hx.1, hx.2⟩)
  -- Attainment: the explicit extremal set reaches the star profile.
  obtain ⟨E, hEmeas, hEsub, hEvol, hEint⟩ := exists_attaining_set hT hg hθ0 hθT
  have hAttain : starProfile T g θ
      ≤ ⨆ E ∈ {E : Set ℝ | MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) T
          ∧ volume E = ENNReal.ofReal (2 * θ)}, ∫⁻ x in E, g x := by
    rw [← hEint]
    exact le_iSup₂_of_le E ⟨hEmeas, hEsub, hEvol⟩ le_rfl
  -- Combine: `starProfile = ∫ min = sup`.
  refine le_antisymm hAttain (iSup₂_le ?_)
  rintro E' ⟨hE'meas, hE'sub, hE'vol⟩
  rw [hStarMin]
  exact hUpper E' hE'sub hE'vol

/-- **The open log-polar strip** for a ring domain: in log-polar coordinates `w = log r + i θ`, a
concentric annulus `{rI < |z − p| < rO}` symmetrized to the upper half-plane corresponds to the
rectangle `{log rI < Re w < log rO} × {0 < Im w < π}`. This is the ambient domain of the
log-polar star surface `starPlane`. -/
def logPolarStrip (rI rO : ℝ) : Set ℂ :=
  {w : ℂ | w.re ∈ Set.Ioo (Real.log rI) (Real.log rO) ∧ w.im ∈ Set.Ioo (0 : ℝ) Real.pi}

/-- **The log-polar star surface.** Baernstein's star function `u★` re-expressed as a real-valued
function on the log-polar strip: at `w`, the radius is `exp (Re w)` and the half-aperture is `Im w`,
and the value is `(starFunction p u (exp (Re w)) (Im w)).toReal`. The `.toReal` is faithful once the
star value is finite (see `starFunction_lt_top`), i.e. whenever `u` is bounded above on the
circle. -/
def starPlane (p : ℂ) (u : ℂ → ℝ) : ℂ → ℝ :=
  fun w => (starFunction p u (Real.exp w.re) w.im).toReal

/-- **Finiteness of the Baernstein star function.** If the ring potential `u` is bounded above by
`M` on the circle of radius `r` about `p` (an upper bound suffices: the star function wraps
`ENNReal.ofReal (u ·)`, which clips negative values to `0`, so a lower bound on `u` is not needed),
then for any half-aperture `θ ∈ [0, π]` the star value `starFunction p u r θ` is finite. No
measurability of `u` is required: the bound is transferred through the rearrangement pointwise.

The star value is the integral of the symmetric-decreasing rearrangement of the angular profile over
the centered arc of half-aperture `θ ≤ π = (2π)/2`. The pointwise bound `profile φ ≤ ofReal M`
transfers to the rearrangement (its super-level set above `ofReal M` is empty, so the distribution
function there vanishes, forcing the rearrangement `≤ ofReal M` by the fundamental relation), so the
star value is `≤ ofReal M * volume (Icc 0 (2π)) < ⊤`. -/
theorem starFunction_lt_top {p : ℂ} {u : ℂ → ℝ} {r θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π)
    (hbdd : ∃ M : ℝ, ∀ φ : ℝ, u (p + (r : ℂ) * Complex.exp (φ * Complex.I)) ≤ M) :
    starFunction p u r θ < ⊤ := by
  obtain ⟨M, hM⟩ := hbdd
  set g : ℝ → ℝ≥0∞ :=
    fun φ => ENNReal.ofReal (angularProfile p (fun z => ENNReal.ofReal (u z)) r φ).toReal with hgdef
  -- Pointwise: the angular profile is bounded above by `ofReal (max M 0)`.
  have hgle : ∀ φ, g φ ≤ ENNReal.ofReal (max M 0) := by
    intro φ
    rw [hgdef]
    simp only [angularProfile]
    refine ENNReal.ofReal_le_ofReal ?_
    refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_
    exact ENNReal.ofReal_le_ofReal (le_trans (hM (φ - π)) (le_max_left _ _))
  -- The bound transfers to the rearrangement, with no measurability needed on `u`.
  have hrearrLe : ∀ x, decreasingRearrangeSymm (2 * π) g x ≤ ENNReal.ofReal (max M 0) := by
    intro x
    unfold decreasingRearrangeSymm
    by_contra hcon
    have hlt : ENNReal.ofReal (max M 0) < decreasingRearrange (2 * π) g (2 * |x - (2 * π) / 2|) :=
      not_le.mp hcon
    rw [lt_decreasingRearrange_iff] at hlt
    -- `distribFun (2π) g (ofReal (max M 0)) = 0` since the super-level set is empty.
    have hempty : distribFun (2 * π) g (ENNReal.ofReal (max M 0)) = 0 := by
      have : {y ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal (max M 0) < g y} = ∅ := by
        ext y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro _
        exact not_lt.mpr (hgle y)
      rw [distribFun, this, measure_empty]
    rw [hempty] at hlt
    exact absurd hlt (not_lt.mpr (zero_le _))
  -- The star value is the arc integral of the rearrangement; bound by a finite constant integral.
  have hstar : starFunction p u r θ
      = ∫⁻ x in Icc ((2 * π) / 2 - θ) ((2 * π) / 2 + θ), decreasingRearrangeSymm (2 * π) g x := rfl
  rw [hstar]
  refine lt_of_le_of_lt (lintegral_mono (fun x => hrearrLe x)) ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-!
## The fixed-arc integral of a harmonic function is harmonic in log-polar coordinates

For a ring potential `u` harmonic on an annulus `A = {rI < ‖z − p‖ < rO}` and a fixed bounded
measurable arc-parameter set `E ⊆ ℝ`, the **log-polar arc integral**

`arcIntegral p u E w = ∫ φ in E, u (p + exp (w + φ·I))`

is a real function of the log-polar variable `w = ξ + iθ`. The point `p + exp (w + φ·I)` sits at
radius `exp (Re w)` and angle `Im w + φ`, so the imaginary part of `w` *rotates* the whole arc; this
is why the object depends on the full complex `w` and is genuinely harmonic in it (a radius-only
average would not be). We prove `arcIntegral p u E` is harmonic on the log-polar strip
`{log rI < Re w < log rO}`.

The proof is local: harmonicity is `∀ w, HarmonicAt`. Around a base point `w₀` in the strip we work
on a ball `B ⊆ strip`. The Wirtinger derivative of the fibre `w ↦ u (p + exp (w + φ·I))` is
`f (p + exp (w + φ·I)) · exp (w + φ·I)`, where `f = u_x − i·u_y` is the *global holomorphic
gradient* of `u` on `A` (locally `u = Re F` for a holomorphic `F`, `f = F′`). Integrating this over
fixed set `E` gives a holomorphic function `D` on `B` (differentiation under the integral, complex
variable). A primitive `G` of `D` with `G w₀ = arcIntegral w₀` is holomorphic, and both `Re G` and
`arcIntegral` have the same real Fréchet derivative on the convex ball `B` (namely `reCLM ∘ (D ·)`),
so they agree there. Hence `arcIntegral = Re G` near `w₀` with `G` holomorphic, so it is harmonic.
-/

/-- **The log-polar arc integral.** For a centre `p`, a potential `u`, and a fixed arc-parameter set
`E ⊆ ℝ`, the value at the log-polar point `w = ξ + iθ` is the integral over `φ ∈ E` of `u` sampled
at `p + exp (w + φ·I)`, i.e. at radius `exp ξ` and angle `θ + φ`:

`arcIntegral p u E w = ∫ φ in E, u (p + Complex.exp (w + φ * Complex.I))`. -/
def arcIntegral (p : ℂ) (u : ℂ → ℝ) (E : Set ℝ) (w : ℂ) : ℝ :=
  ∫ φ in E, u (p + Complex.exp (w + φ * Complex.I))

/-- The log-polar image point `p + exp (w + φ·I)` has distance `exp (Re w)` from the centre `p`; in
particular it lies in the open annulus `{rI < ‖z − p‖ < rO}` exactly when `Re w ∈ (log rI, log rO)`
(for `0 < rI`). -/
theorem norm_arcPoint_sub (p w : ℂ) (φ : ℝ) :
    ‖(p + Complex.exp (w + φ * Complex.I)) - p‖ = Real.exp w.re := by
  simp [Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im]

/-- **The log-polar map `w ↦ p + exp (w + φ·I)` sends the strip into the annulus.** For `0 < rI`,
`rI < rO` and `Re w ∈ (log rI, log rO)`, the image point lies in `A = {rI < ‖z − p‖ < rO}`. -/
theorem arcPoint_mem_annulus {p : ℂ} {rI rO : ℝ} (hrI : 0 < rI) (hrO : rI < rO) {w : ℂ} (φ : ℝ)
    (hw : Real.log rI < w.re ∧ w.re < Real.log rO) :
    (p + Complex.exp (w + φ * Complex.I))
      ∈ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
  refine ⟨?_, ?_⟩
  · rw [norm_arcPoint_sub]
    calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
      _ < Real.exp w.re := Real.exp_lt_exp.mpr hw.1
  · rw [norm_arcPoint_sub]
    calc Real.exp w.re < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hw.2
      _ = rO := Real.exp_log (lt_trans hrI hrO)

/-- **The holomorphic gradient of a real function.** For `u : ℂ → ℝ`, set
`gradC u z = (fderiv ℝ u z) 1 − i·(fderiv ℝ u z) I` (the Wirtinger `u_x − i·u_y`). This is the
object whose modulus is `‖∇u‖` and which is holomorphic precisely when `u` is harmonic. -/
def gradC (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  (((fderiv ℝ u z) 1 : ℝ) : ℂ) - Complex.I * (((fderiv ℝ u z) Complex.I : ℝ) : ℂ)

/-- The real Fréchet derivative of `u` acts as the real part of multiplication by the holomorphic
gradient: `(fderiv ℝ u z) v = Re (gradC u z · v)`. This is the complex bookkeeping of
`∇u · v = u_x v_x + u_y v_y` and requires no harmonicity, only that `u` be differentiable at `z`. -/
theorem fderiv_eq_re_gradC_mul (u : ℂ → ℝ) (z : ℂ) (v : ℂ) :
    (fderiv ℝ u z) v = (gradC u z * v).re := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp only [gradC, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.mul_im,
    Complex.add_im, smul_eq_mul, Complex.smul_re, Complex.smul_im, Complex.one_re, Complex.one_im,
    Complex.I_im, Complex.I_re]
  ring

/-- The holomorphic gradient `gradC u` agrees with Mathlib's Wirtinger partial
`z ↦ ∂u/∂1 − i·∂u/∂I`. -/
theorem gradC_eq (u : ℂ → ℝ) :
    gradC u = fun z => (fderiv ℝ u z) 1 - Complex.I * (fderiv ℝ u z) Complex.I := by
  funext z; simp [gradC]

/-- **Holomorphy of the gradient of a harmonic function.** If `u` is harmonic in a neighbourhood of
the open set `U`, its holomorphic gradient `gradC u` is complex-differentiable on `U`. -/
theorem gradC_differentiableOn {u : ℂ → ℝ} {U : Set ℂ}
    (hu : InnerProductSpace.HarmonicOnNhd u U) :
    DifferentiableOn ℂ (gradC u) U := by
  rw [gradC_eq]
  intro z hz
  exact (HarmonicAt.differentiableAt_complex_partial (hu z hz)).differentiableWithinAt

/-- The log-polar map `w ↦ p + exp (w + φ·I)` is entire with complex derivative `exp (w + φ·I)`. -/
theorem hasDerivAt_arcPoint (p : ℂ) (φ : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => p + Complex.exp (w + φ * Complex.I))
      (Complex.exp (w + φ * Complex.I)) w := by
  have h1 : HasDerivAt (fun w : ℂ => w + φ * Complex.I) 1 w := by
    simpa using (hasDerivAt_id w).add_const (φ * Complex.I)
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (w + φ * Complex.I))
      (Complex.exp (w + φ * Complex.I) * 1) w := h1.cexp
  simpa using h2.const_add p

/-- **The fibre chain rule.** If `u` is differentiable at the log-polar image point `g_φ w`, then
the fibre `w ↦ u (p + exp (w + φ·I))` has real Fréchet derivative `reCLM ∘ (Dφ w • id)`, where
`Dφ w = gradC u (g_φ w) · exp (w + φ·I)` is the holomorphic candidate derivative. -/
theorem hasFDerivAt_fibre {p : ℂ} {u : ℂ → ℝ} (φ : ℝ) {w : ℂ}
    (hu : DifferentiableAt ℝ u (p + Complex.exp (w + φ * Complex.I))) :
    HasFDerivAt (fun w : ℂ => u (p + Complex.exp (w + φ * Complex.I)))
      (Complex.reCLM.comp
        ((gradC u (p + Complex.exp (w + φ * Complex.I)) * Complex.exp (w + φ * Complex.I))
          • (ContinuousLinearMap.id ℝ ℂ))) w := by
  set z := p + Complex.exp (w + φ * Complex.I) with hz
  set e := Complex.exp (w + φ * Complex.I) with he
  -- The log-polar map is `ℝ`-differentiable with derivative `e • id`.
  have hg : HasFDerivAt (fun w : ℂ => p + Complex.exp (w + φ * Complex.I))
      (e • (ContinuousLinearMap.id ℝ ℂ)) w := by
    rw [hasFDerivAt_iff_isLittleO]
    refine (hasDerivAt_arcPoint p φ w).isLittleO.congr_left fun t => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, he]
    ring
  -- Compose with the real derivative of `u` at `z`.
  have hcomp := hu.hasFDerivAt.comp w hg
  refine hcomp.congr_fderiv ?_
  ext t
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply]
  rw [fderiv_eq_re_gradC_mul u z (e * t)]
  ring_nf

/-- **Fixed-arc harmonicity (pointwise).** Under the hypotheses of `arcIntegral_harmonicOn`, the
log-polar arc integral is harmonic at every base point `w₀` of the strip. -/
theorem arcIntegral_harmonicAt {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {E : Set ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hE : MeasurableSet E) (hEbdd : Bornology.IsBounded E) {w₀ : ℂ}
    (hw₀ : Real.log rI < w₀.re ∧ w₀.re < Real.log rO) :
    InnerProductSpace.HarmonicAt (arcIntegral p u E) w₀ := by
  classical
  set A : Set ℂ := {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} with hA
  set S : Set ℂ := {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} with hS
  have hSopen : IsOpen S := by
    have : S = (fun w : ℂ => w.re) ⁻¹' Set.Ioo (Real.log rI) (Real.log rO) := by
      ext w; simp [hS, Set.mem_Ioo]
    rw [this]; exact isOpen_Ioo.preimage Complex.continuous_re
  have hw₀S : w₀ ∈ S := hw₀
  -- Bounded arc parameters live in a compact interval `Icc a b ⊇ E`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, E ⊆ Set.Icc a b := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hEbdd
    exact ⟨-r, r, fun x hx => by
      have := hr hx; rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at this
      exact ⟨this.1, this.2⟩⟩
  -- A closed ball `B̄ = closedBall w₀ ρ ⊆ S`, and the open ball `B = ball w₀ ρ`.
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ > 0, Metric.closedBall w₀ ρ ⊆ S := by
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hSopen.mem_nhds hw₀S)
    exact ⟨ρ, hρpos, hρsub⟩
  set B : Set ℂ := Metric.ball w₀ ρ with hB
  have hBsub : B ⊆ S := (Metric.ball_subset_closedBall).trans hρsub
  have hBopen : IsOpen B := Metric.isOpen_ball
  -- `gradC u` is holomorphic on the annulus `A`.
  have hfhol : DifferentiableOn ℂ (gradC u) A := gradC_differentiableOn hu
  have hfcont : ContinuousOn (gradC u) A := hfhol.continuousOn
  have hAopen : IsOpen A := by
    have h1 : IsOpen {z : ℂ | rI < ‖z - p‖} :=
      isOpen_lt continuous_const (by fun_prop)
    have h2 : IsOpen {z : ℂ | ‖z - p‖ < rO} :=
      isOpen_lt (by fun_prop) continuous_const
    simpa [hA, Set.setOf_and] using h1.inter h2
  -- Every log-polar image point of `B̄ × Icc a b` lies in the annulus.
  have himg : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ φ : ℝ,
      (p + Complex.exp (w + φ * Complex.I)) ∈ A :=
    fun w hw φ => arcPoint_mem_annulus hrI hrO φ (hρsub hw)
  -- Uniform bound on `‖gradC u (g_φ w)‖` over the compact `B̄ × Icc a b`.
  set gmap : ℂ × ℝ → ℂ := fun q => p + Complex.exp (q.1 + q.2 * Complex.I) with hgmap
  have hgmapcont : Continuous gmap := by
    rw [hgmap]; fun_prop
  set K : Set ℂ := gmap '' (Metric.closedBall w₀ ρ ×ˢ Set.Icc a b) with hK
  have hKcompact : IsCompact K :=
    ((isCompact_closedBall w₀ ρ).prod (isCompact_Icc)).image hgmapcont
  have hKsub : K ⊆ A := by
    rintro z ⟨q, hq, rfl⟩
    exact himg q.1 hq.1 q.2
  obtain ⟨Cf0, hCf0⟩ : ∃ Cf : ℝ, ∀ z ∈ K, ‖gradC u z‖ ≤ Cf :=
    hKcompact.exists_bound_of_continuousOn (hfcont.mono hKsub)
  set Cf : ℝ := max Cf0 0 with hCfdef
  have hCfnn : 0 ≤ Cf := le_max_right _ _
  have hCf : ∀ z ∈ K, ‖gradC u z‖ ≤ Cf := fun z hz => (hCf0 z hz).trans (le_max_left _ _)
  -- Radius bound `exp (Re w) ≤ Cexp` on the closed ball.
  set Cexp : ℝ := Real.exp (w₀.re + ρ) with hCexpdef
  have hCexpnn : 0 ≤ Cexp := (Real.exp_pos _).le
  have hrele : ∀ w ∈ Metric.closedBall w₀ ρ, Real.exp w.re ≤ Cexp := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hre : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm (w - w₀)
    rw [Complex.sub_re] at hre
    have : w.re - w₀.re ≤ ρ := le_trans (le_trans (le_abs_self _) hre) hw
    exact Real.exp_le_exp.mpr (by linarith)
  -- The fibre derivative candidate and its `w`-integral.
  set Dφ : ℝ → ℂ → ℂ :=
    fun φ w => gradC u (gmap (w, φ)) * Complex.exp (w + φ * Complex.I) with hDφ
  set D : ℂ → ℂ := fun w => ∫ φ in E, Dφ φ w with hDdef
  -- Pointwise uniform norm bound on the fibre derivative over `B̄ × Icc a b`.
  have hDφbound : ∀ φ ∈ Set.Icc a b, ∀ w ∈ Metric.closedBall w₀ ρ, ‖Dφ φ w‖ ≤ Cf * Cexp := by
    intro φ hφ w hw
    have hz : gmap (w, φ) ∈ K := ⟨(w, φ), ⟨hw, hφ⟩, rfl⟩
    rw [hDφ]
    simp only [norm_mul]
    have h1 : ‖gradC u (gmap (w, φ))‖ ≤ Cf := hCf _ hz
    have h2 : ‖Complex.exp (w + φ * Complex.I)‖ = Real.exp w.re := by
      rw [Complex.norm_exp]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im]
    rw [h2]
    exact mul_le_mul h1 (hrele w hw) (Real.exp_pos _).le hCfnn
  -- `gmap (·, φ)` is continuous in `w`; hence `w ↦ Dφ φ w` is continuous on `B̄`.
  have hDφcont : ∀ φ : ℝ, ContinuousOn (fun w => Dφ φ w) (Metric.closedBall w₀ ρ) := by
    intro φ
    rw [hDφ]
    apply ContinuousOn.mul
    · apply hfcont.comp (by fun_prop) (fun w hw => himg w hw φ) |>.congr
      intro w hw; rfl
    · fun_prop
  -- Measurability of `φ ↦ Dφ φ w` (jointly continuous in `(w, φ)` on the annulus preimage).
  have hDφmeas : ∀ w ∈ Metric.closedBall w₀ ρ,
      AEStronglyMeasurable (fun φ => Dφ φ w) (volume.restrict E) := by
    intro w hw
    apply ContinuousOn.aestronglyMeasurable (s := Set.Icc a b) _ measurableSet_Icc |>.mono_set hab
    apply ContinuousOn.mul
    · exact (hfcont.mono hKsub).comp (by fun_prop)
        (fun φ hφ => ⟨(w, φ), ⟨hw, hφ⟩, rfl⟩)
    · fun_prop
  -- Integrability of the fibre derivative at each `w ∈ B̄` (bounded on a finite-measure set).
  have hErestr_finite : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hab)
  haveI hEfinite : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.2 hErestr_finite
  have hDφint : ∀ w ∈ Metric.closedBall w₀ ρ, Integrable (fun φ => Dφ φ w) (volume.restrict E) := by
    intro w hw
    refine Integrable.of_bound (hDφmeas w hw) (Cf * Cexp) ?_
    filter_upwards [ae_restrict_mem hE] with φ hφ
    exact hDφbound φ (hab hφ) w hw
  have hbdint : Integrable (fun _ : ℝ => Cf * Cexp) (volume.restrict E) := integrable_const _
  have hw₀ball : w₀ ∈ B := Metric.mem_ball_self hρpos
  have hBsubcb : B ⊆ Metric.closedBall w₀ ρ := Metric.ball_subset_closedBall
  -- The derivative of `gradC u` is continuous on the annulus, hence bounded on the compact `K`.
  have hfanalytic : AnalyticOnNhd ℂ (gradC u) A := hfhol.analyticOnNhd hAopen
  have hfderivcont : ContinuousOn (deriv (gradC u)) A :=
    (hfanalytic.deriv_of_isOpen hAopen).continuousOn
  obtain ⟨Cf'0, hCf'0⟩ : ∃ C : ℝ, ∀ z ∈ K, ‖deriv (gradC u) z‖ ≤ C :=
    hKcompact.exists_bound_of_continuousOn (hfderivcont.mono hKsub)
  set Cf' : ℝ := max Cf'0 0 with hCf'def
  have hCf'nn : 0 ≤ Cf' := le_max_right _ _
  have hCf' : ∀ z ∈ K, ‖deriv (gradC u) z‖ ≤ Cf' :=
    fun z hz => (hCf'0 z hz).trans (le_max_left _ _)
  -- The fibre derivative `Dφ' φ w = ∂_w (Dφ φ) = (gradC u)'(g_φ w)·e² + gradC u(g_φ w)·e`.
  set Dφ' : ℝ → ℂ → ℂ := fun φ w =>
    deriv (gradC u) (gmap (w, φ)) * Complex.exp (w + φ * Complex.I) ^ 2
      + gradC u (gmap (w, φ)) * Complex.exp (w + φ * Complex.I) with hDφ'
  -- The fibre is complex-differentiable in `w`, with derivative `Dφ' φ w`.
  have hDφderiv : ∀ φ : ℝ, ∀ w ∈ B, HasDerivAt (fun w => Dφ φ w) (Dφ' φ w) w := by
    intro φ w hw
    have hgm : HasDerivAt (fun w : ℂ => gmap (w, φ)) (Complex.exp (w + φ * Complex.I)) w := by
      simpa [gmap] using hasDerivAt_arcPoint p φ w
    have hgmem : gmap (w, φ) ∈ A := himg w (hBsubcb hw) φ
    have hgradderiv : HasDerivAt (gradC u) (deriv (gradC u) (gmap (w, φ))) (gmap (w, φ)) :=
      (hfhol.differentiableAt (hAopen.mem_nhds hgmem)).hasDerivAt
    have hcomp : HasDerivAt (gradC u ∘ (fun w => gmap (w, φ)))
        (deriv (gradC u) (gmap (w, φ)) * Complex.exp (w + φ * Complex.I)) w :=
      hgradderiv.comp w hgm
    have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w + φ * Complex.I))
        (Complex.exp (w + φ * Complex.I)) w := by
      have h1 : HasDerivAt (fun w : ℂ => w + φ * Complex.I) 1 w := by
        simpa using (hasDerivAt_id w).add_const (φ * Complex.I)
      simpa using h1.cexp
    have hmul := hcomp.mul hexp
    rw [hDφ, hDφ']
    convert hmul using 1
    simp only [Function.comp_apply]
    ring
  -- Uniform integrable bound on the fibre derivative over `B`.
  set bound' : ℝ := Cf' * Cexp ^ 2 + Cf * Cexp with hbound'
  have hDφ'bound : ∀ φ ∈ Set.Icc a b, ∀ w ∈ B, ‖Dφ' φ w‖ ≤ bound' := by
    intro φ hφ w hw
    have hz : gmap (w, φ) ∈ K := ⟨(w, φ), ⟨hBsubcb hw, hφ⟩, rfl⟩
    have hexpnorm : ‖Complex.exp (w + φ * Complex.I)‖ = Real.exp w.re := by
      rw [Complex.norm_exp]
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im]
    have hle1 : ‖deriv (gradC u) (gmap (w, φ)) * Complex.exp (w + φ * Complex.I) ^ 2‖
        ≤ Cf' * Cexp ^ 2 := by
      rw [norm_mul, norm_pow, hexpnorm]
      exact mul_le_mul (hCf' _ hz) (pow_le_pow_left₀ (Real.exp_pos _).le (hrele w (hBsubcb hw)) 2)
        (by positivity) hCf'nn
    have hle2 : ‖gradC u (gmap (w, φ)) * Complex.exp (w + φ * Complex.I)‖ ≤ Cf * Cexp := by
      rw [norm_mul, hexpnorm]
      exact mul_le_mul (hCf _ hz) (hrele w (hBsubcb hw)) (Real.exp_pos _).le hCfnn
    calc ‖Dφ' φ w‖ ≤ ‖deriv (gradC u) (gmap (w, φ)) * Complex.exp (w + φ * Complex.I) ^ 2‖
          + ‖gradC u (gmap (w, φ)) * Complex.exp (w + φ * Complex.I)‖ := norm_add_le _ _
      _ ≤ bound' := by rw [hbound']; exact add_le_add hle1 hle2
  have hbd'int : Integrable (fun _ : ℝ => bound') (volume.restrict E) := integrable_const _
  have hDφ'meas : ∀ w ∈ B, AEStronglyMeasurable (fun φ => Dφ' φ w) (volume.restrict E) := by
    intro w hw
    apply ContinuousOn.aestronglyMeasurable (s := Set.Icc a b) _ measurableSet_Icc |>.mono_set hab
    rw [hDφ']
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · exact (hfderivcont.mono hKsub).comp (by fun_prop)
          (fun φ hφ => ⟨(w, φ), ⟨hBsubcb hw, hφ⟩, rfl⟩)
      · fun_prop
    · apply ContinuousOn.mul
      · exact (hfcont.mono hKsub).comp (by fun_prop)
          (fun φ hφ => ⟨(w, φ), ⟨hBsubcb hw, hφ⟩, rfl⟩)
      · fun_prop
  -- **Step 1: `D` is holomorphic on `B`.** Complex differentiation under the integral sign.
  have hDdiff : ∀ w ∈ B, HasDerivAt D (∫ φ in E, Dφ' φ w) w := by
    intro w hw
    have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict E) (F := fun w φ => Dφ φ w) (F' := fun w φ => Dφ' φ w)
      (bound := fun _ => bound') (x₀ := w) (s := B)
      (hBopen.mem_nhds hw)
      (Filter.eventually_of_mem (hBopen.mem_nhds hw) (fun w' hw' => hDφmeas w' (hBsubcb hw')))
      (hDφint w (hBsubcb hw)) (hDφ'meas w hw)
      (by
        filter_upwards [ae_restrict_mem hE] with φ hφ w' hw'
        exact hDφ'bound φ (hab hφ) w' hw')
      hbd'int
      (Filter.Eventually.of_forall (fun φ w' hw' => hDφderiv φ w' hw'))
    rw [hDdef]
    simpa only [] using hres.2
  have hDdiffOn : DifferentiableOn ℂ D B :=
    fun w hw => (hDdiff w hw).differentiableAt.differentiableWithinAt
  -- **Step 2: a holomorphic primitive `G` of `D` on `B`, pinned at `w₀`.**
  obtain ⟨G, hGval, hGderiv⟩ := (hDdiffOn.isExactOn_ball (c := w₀) (r := ρ)).with_val_at w₀
    ((arcIntegral p u E w₀ : ℝ) : ℂ)
  have hGderivOn : DifferentiableOn ℂ G B :=
    fun w hw => (hGderiv w hw).differentiableAt.differentiableWithinAt
  have hGanalytic : AnalyticOnNhd ℂ G B := hGderivOn.analyticOnNhd hBopen
  -- **Step 3: `Re G` has real Fréchet derivative `reCLM ∘ (D w • id)` on `B`.**
  have hReGfderiv : ∀ w ∈ B, HasFDerivAt (fun w => (G w).re)
      (Complex.reCLM.comp ((D w) • (ContinuousLinearMap.id ℝ ℂ))) w := by
    intro w hw
    have hGr : HasFDerivAt G (D w • (ContinuousLinearMap.id ℝ ℂ)) w := by
      rw [hasFDerivAt_iff_isLittleO]
      refine (hGderiv w hw).isLittleO.congr_left fun t => ?_
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
    have := Complex.reCLM.hasFDerivAt.comp w hGr
    simpa [Function.comp] using this
  -- Differentiability facts for `u` (harmonic ⟹ `C²` ⟹ differentiable) on the annulus.
  have hudiff : ∀ z ∈ A, DifferentiableAt ℝ u z :=
    fun z hz => (hu z hz).1.differentiableAt (by norm_num)
  have hucont : ContinuousOn u A := hu.continuousOn
  obtain ⟨Cu0, hCu0⟩ : ∃ C : ℝ, ∀ z ∈ K, ‖u z‖ ≤ C :=
    hKcompact.exists_bound_of_continuousOn (hucont.mono hKsub)
  -- **Step 4: `arcIntegral` has the same real Fréchet derivative on `B`.**
  -- The fibre `w ↦ u (g_φ w)` and its `ℝ`-derivative `reCLM ∘ (Dφ φ w • id)`.
  set L : ℝ → ℂ → (ℂ →L[ℝ] ℝ) := fun φ w =>
    Complex.reCLM.comp ((Dφ φ w) • (ContinuousLinearMap.id ℝ ℂ)) with hL
  -- Uniform op-norm bound on the fibre derivative.
  have hLbound : ∀ φ ∈ Set.Icc a b, ∀ w ∈ B, ‖L φ w‖ ≤ Cf * Cexp := by
    intro φ hφ w hw
    refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_)
      (hDφbound φ hφ w (hBsubcb hw))
    rw [hL]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply, Real.norm_eq_abs]
    calc |(Dφ φ w * t).re| ≤ ‖Dφ φ w * t‖ := Complex.abs_re_le_norm _
      _ = ‖Dφ φ w‖ * ‖t‖ := by rw [norm_mul]
  have hufibcont : ∀ w ∈ B, ContinuousOn (fun φ => u (gmap (w, φ))) (Set.Icc a b) :=
    fun w hw => (hucont.mono hKsub).comp (by fun_prop)
      (fun φ hφ => ⟨(w, φ), ⟨hBsubcb hw, hφ⟩, rfl⟩)
  have hufibmeas : ∀ w ∈ B, AEStronglyMeasurable (fun φ => u (gmap (w, φ))) (volume.restrict E) :=
    fun w hw => (hufibcont w hw).aestronglyMeasurable measurableSet_Icc |>.mono_set hab
  have hufibint : ∀ w ∈ B, Integrable (fun φ => u (gmap (w, φ))) (volume.restrict E) := by
    intro w hw
    refine Integrable.of_bound (hufibmeas w hw) Cu0 ?_
    filter_upwards [ae_restrict_mem hE] with φ hφ
    exact hCu0 _ ⟨(w, φ), ⟨hBsubcb hw, hab hφ⟩, rfl⟩
  have hLmeas : ∀ w ∈ B, AEStronglyMeasurable (fun φ => L φ w) (volume.restrict E) := by
    intro w hw
    have : Continuous fun c : ℂ => Complex.reCLM.comp (c • (ContinuousLinearMap.id ℝ ℂ)) := by
      fun_prop
    exact (this.comp_aestronglyMeasurable (hDφmeas w (hBsubcb hw)))
  have hLint : Integrable (fun _ : ℝ => Cf * Cexp) (volume.restrict E) := hbdint
  -- The fibre chain rule holds at each `w ∈ B` (image lands in the open annulus).
  have hfibfderiv : ∀ φ : ℝ, ∀ w ∈ B, HasFDerivAt (fun w => u (gmap (w, φ))) (L φ w) w := by
    intro φ w hw
    have hgmem : gmap (w, φ) ∈ A := himg w (hBsubcb hw) φ
    have := hasFDerivAt_fibre (p := p) (u := u) φ (w := w) (hudiff _ hgmem)
    rw [hL]; exact this
  have harcfderiv : ∀ w ∈ B, HasFDerivAt (arcIntegral p u E) (∫ φ in E, L φ w) w := by
    intro w hw
    have hres := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume.restrict E) (F := fun w φ => u (gmap (w, φ))) (F' := fun w φ => L φ w)
      (bound := fun _ => Cf * Cexp) (x₀ := w) (s := B)
      (hBopen.mem_nhds hw)
      (Filter.eventually_of_mem (hBopen.mem_nhds hw) (fun w' hw' => hufibmeas w' hw'))
      (hufibint w hw) (hLmeas w hw)
      (by
        filter_upwards [ae_restrict_mem hE] with φ hφ w' hw'
        exact hLbound φ (hab hφ) w' hw')
      hLint
      (Filter.Eventually.of_forall (fun φ w' hw' => hfibfderiv φ w' hw'))
    have harc_eq : arcIntegral p u E = fun w => ∫ φ in E, u (gmap (w, φ)) := by
      funext w; rfl
    rw [harc_eq]
    exact hres
  -- The vector integral of the fibre derivatives collapses to `reCLM ∘ (D w • id)`.
  have hLintegral : ∀ w ∈ B, (∫ φ in E, L φ w)
      = Complex.reCLM.comp ((D w) • (ContinuousLinearMap.id ℝ ℂ)) := by
    intro w hw
    have hLint2 : Integrable (fun φ => L φ w) (volume.restrict E) :=
      Integrable.of_bound (hLmeas w hw) (Cf * Cexp) (by
        filter_upwards [ae_restrict_mem hE] with φ hφ
        exact hLbound φ (hab hφ) w hw)
    ext t
    rw [ContinuousLinearMap.integral_apply hLint2]
    have hpt : ∀ φ, (L φ w) t = Complex.reCLM (Dφ φ w * t) := by
      intro φ
      rw [hL]
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, mul_comm]
    simp only [hpt]
    rw [Complex.reCLM.integral_comp_comm ((hDφint w (hBsubcb hw)).mul_const t)]
    have hmc : (∫ x in E, Dφ x w * t) = (∫ x in E, Dφ x w) * t :=
      integral_mul_const t (fun x => Dφ x w)
    rw [hmc]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply]
    rfl
  -- **Step 5: `Re G` and `arcIntegral` agree on the convex ball `B`.**
  have hReGdiffOn : DifferentiableOn ℝ (fun w => (G w).re) B :=
    fun w hw => (hReGfderiv w hw).differentiableAt.differentiableWithinAt
  have harcdiffOn : DifferentiableOn ℝ (arcIntegral p u E) B :=
    fun w hw => (harcfderiv w hw).differentiableAt.differentiableWithinAt
  have heqfderiv : Set.EqOn (fderiv ℝ (fun w => (G w).re)) (fderiv ℝ (arcIntegral p u E)) B := by
    intro w hw
    rw [(hReGfderiv w hw).fderiv, (harcfderiv w hw).fderiv, hLintegral w hw]
  have hEqOn : Set.EqOn (fun w => (G w).re) (arcIntegral p u E) B := by
    have hconvex : Convex ℝ B := convex_ball w₀ ρ
    refine hconvex.eqOn_of_fderivWithin_eq hReGdiffOn harcdiffOn hBopen.uniqueDiffOn ?_
      hw₀ball ?_
    · intro w hw
      rw [fderivWithin_of_isOpen hBopen hw, fderivWithin_of_isOpen hBopen hw]
      exact heqfderiv hw
    · rw [hGval]; simp
  -- **Step 6: harmonicity.** `arcIntegral = Re G` near `w₀`, and `Re G` is harmonic (`G` analytic).
  have hHarmReG : InnerProductSpace.HarmonicAt (fun w => (G w).re) w₀ :=
    (hGanalytic w₀ hw₀ball).harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hHarmReG
  filter_upwards [hBopen.mem_nhds hw₀ball] with w hw using hEqOn hw

/-- **The fixed-arc integral of a harmonic function is harmonic in log-polar coordinates.** Let `u`
be harmonic on the annulus `A = {rI < ‖z − p‖ < rO}` (`0 < rI < rO`), and let `E ⊆ ℝ` be a fixed
bounded measurable arc-parameter set. Then the log-polar arc integral
`arcIntegral p u E w = ∫ φ in E, u (p + exp (w + φ·I))` is harmonic on the open log-polar strip
`{log rI < Re w < log rO}` (the preimage of `A` under `w ↦ p + exp w`). -/
theorem arcIntegral_harmonicOn {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {E : Set ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hE : MeasurableSet E) (hEbdd : Bornology.IsBounded E) :
    InnerProductSpace.HarmonicOnNhd (arcIntegral p u E)
      {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} :=
  fun _ hw => arcIntegral_harmonicAt hrI hrO hu hE hEbdd hw

/-!
## The upper-half fixed-arc domination

The sub-mean-value inequality for the log-polar star surface `starPlane p u` rests on the following
*domination* of the fixed-arc harmonic integral by the star function. The two measure-extension
lemmas below (a 1-Lipschitz intermediate-value argument, the same pattern used inside
`starProfile_eq_iSup_setLIntegral`) turn a measurable subset of a bounded interval into a subset of
*prescribed* measure, or extend it to a *superset* of prescribed larger measure inside the interval.
-/

/-- **Prescribed-measure superset inside a bounded interval.** For a measurable `A ⊆ Icc a b` and a
target `0 ≤ m` with `|A| ≤ ofReal m` and `m ≤ b − a`, there is a measurable superset `A ⊆ F ⊆ Icc a
b` of measure exactly `ofReal m`. Take `F = A ∪ B` where `B` is a prescribed-measure subset of the
complement `Icc a b \ A` (of the exact deficit `m − |A|`), produced by
`exists_measurableSet_subset_volume`. -/
theorem exists_measurableSet_superset_volume {a b : ℝ} (hab : a ≤ b) (A : Set ℝ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Icc a b) {m : ℝ} (hm0 : 0 ≤ m)
    (hmA : volume A ≤ ENNReal.ofReal m) (hmb : m ≤ b - a) :
    ∃ F, A ⊆ F ∧ F ⊆ Set.Icc a b ∧ MeasurableSet F ∧ volume F = ENNReal.ofReal m := by
  have hAfin : volume A ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hAsub)
    rw [Real.volume_Icc]; exact ofReal_ne_top
  -- Work with the real number `dA = |A|`; both `A` and `Icc a b` have finite measure.
  obtain ⟨dA, hdAnn, hAeq⟩ : ∃ dA : ℝ, 0 ≤ dA ∧ volume A = ENNReal.ofReal dA :=
    ⟨(volume A).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hAfin).symm⟩
  have hdAle_m : dA ≤ m := ENNReal.ofReal_le_ofReal_iff hm0 |>.mp (hAeq ▸ hmA)
  have hdAle_ba : dA ≤ b - a := by
    have := (measure_mono hAsub).trans (le_of_eq (Real.volume_Icc (a := a) (b := b)))
    rw [hAeq] at this
    exact ENNReal.ofReal_le_ofReal_iff (by linarith) |>.mp this
  set C : Set ℝ := Set.Icc a b \ A with hCdef
  have hCmeas : MeasurableSet C := measurableSet_Icc.diff hA
  have hCsub : C ⊆ Set.Icc a b := diff_subset
  have hCvol : volume C = ENNReal.ofReal (b - a) - volume A := by
    rw [hCdef, measure_diff (by exact hAsub) hA.nullMeasurableSet hAfin, Real.volume_Icc]
  have hdefnn : 0 ≤ m - dA := by linarith
  have hCge : ENNReal.ofReal (m - dA) ≤ volume C := by
    rw [hCvol, hAeq, ← ENNReal.ofReal_sub _ hdAnn]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨B, hBsub, hBmeas, hBvol⟩ :=
    exists_measurableSet_subset_volume hab C hCmeas hCsub hdefnn hCge
  refine ⟨A ∪ B, subset_union_left, ?_, hA.union hBmeas, ?_⟩
  · exact union_subset hAsub (hBsub.trans hCsub)
  · have hdisj : Disjoint A B := Set.disjoint_of_subset_right hBsub (by
      rw [hCdef]; exact Set.disjoint_sdiff_right)
    rw [measure_union hdisj hBmeas, hBvol, hAeq,
      ← ENNReal.ofReal_add hdAnn hdefnn]
    congr 1; ring

/-- **Upper-half fixed-arc domination (extended-real form).** For a nonnegative measurable ring
potential `u` (`0 ≤ u`, `Measurable u`), a measurable arc-parameter set `E` on which the arc fibre
`φ ↦ u (p + exp (w + φ·I))` is integrable, and a log-polar point `w` with `0 ≤ Im w ≤ π`, the
extended-real value of the arc integral is dominated by the star function at radius `exp (Re w)` and
half-aperture `Im w`, *provided* the arc — rotated by `w` into the profile parametrisation, i.e.
`E' = (· + (Im w + π)) '' E` — lands in the parameter interval `Icc 0 (2π)` and has measure at most
`2·Im w`.

The load-bearing hypotheses are `volume E ≤ ofReal (2·Im w)` and `Im w ≤ π`: the rotated arc `E'`
(same measure as `E`, being a translate) is then *extended* to a subset `F ⊆ Icc 0 (2π)` of measure
exactly `2·Im w` via `exists_measurableSet_superset_volume`, and since the profile `g ≥ 0`,

`ofReal (arcIntegral p u E w) = ∫⁻_{E'} g ≤ ∫⁻_F g ≤ ⨆_{|F'| = 2·Im w} ∫⁻_{F'} g
  = starFunction p u (exp (Re w)) (Im w)`,

the last equality being the Hardy–Littlewood characterisation `starProfile_eq_iSup_setLIntegral`.
The constraint `E' ⊆ Icc 0 (2π)` (equivalently: the arc, once rotated, fits in one period) is
exactly what confines the direct argument to circle points with `Im w ≥ Im w₀`; below the centre
the extremal set is first trimmed along the uncovered window (Sjögren's surgery) before this
lemma applies. -/
theorem arcIntegral_le_starFunction {p : ℂ} {u : ℂ → ℝ} {E : Set ℝ} {w : ℂ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E))
    (hEmeas : MeasurableSet E) (hwim0 : 0 ≤ w.im) (hwimπ : w.im ≤ π)
    (hE'sub : (fun φ : ℝ => φ + (w.im + π)) '' E ⊆ Set.Icc 0 (2 * π))
    (hEvol : volume E ≤ ENNReal.ofReal (2 * w.im)) :
    ENNReal.ofReal (arcIntegral p u E w) ≤ starFunction p u (Real.exp w.re) w.im := by
  classical
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal
      (angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w.re) ψ).toReal with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp w.re)))
  set E' : Set ℝ := (fun φ : ℝ => φ + (w.im + π)) '' E with hE'def
  have hE'meas : MeasurableSet E' :=
    (measurableEmbedding_addRight (w.im + π)).measurableSet_image.2 hEmeas
  have hmp : MeasurePreserving (fun φ : ℝ => φ + (w.im + π)) volume volume :=
    measurePreserving_add_right volume (w.im + π)
  have hE'vol : volume E' = volume E := by
    rw [hE'def, image_add_right, measure_preimage_add_right]
  -- Integral chain: `ofReal (arcIntegral) = ∫⁻_{E'} g`.
  have hchain : ENNReal.ofReal (arcIntegral p u E w) = ∫⁻ ψ in E', g ψ := by
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w + φ * Complex.I)))
        = g (φ + (w.im + π)) := by
      intro φ
      rw [hgdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w + (φ : ℂ) * Complex.I = (w.re : ℂ) + ((φ + w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w.im + π)) g
      ((fun φ : ℝ => φ + (w.im + π)) '' E)
    rw [Set.preimage_image_eq _ (add_left_injective (w.im + π))] at hkey
    rw [hkey]
  -- Extend `E'` to a set `F ⊆ Icc 0 (2π)` of measure exactly `2·Im w`.
  obtain ⟨F, hE'F, hFsub, hFmeas, hFvol⟩ :=
    exists_measurableSet_superset_volume (m := 2 * w.im)
      (by positivity : (0 : ℝ) ≤ 2 * π) E' hE'meas hE'sub
      (by positivity) (by rw [hE'vol]; exact hEvol) (by linarith)
  -- `∫⁻_{E'} g ≤ ∫⁻_F g ≤ sup = starFunction`.
  have hmono : (∫⁻ ψ in E', g ψ) ≤ ∫⁻ ψ in F, g ψ := lintegral_mono_set hE'F
  have hsup : starFunction p u (Real.exp w.re) w.im
      = ⨆ F' ∈ {F' : Set ℝ | MeasurableSet F' ∧ F' ⊆ Icc (0 : ℝ) (2 * π)
          ∧ volume F' = ENNReal.ofReal (2 * w.im)}, ∫⁻ ψ in F', g ψ := by
    rw [show starFunction p u (Real.exp w.re) w.im = starProfile (2 * π) g w.im from rfl]
    exact starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hwim0 (by linarith)
  rw [hchain, hsup]
  exact le_trans hmono (le_iSup₂_of_le F ⟨hFmeas, hFsub, hFvol⟩ le_rfl)

/-- **Upper-half fixed-arc domination (real form).** The real-valued restatement of
`arcIntegral_le_starFunction`: under the same hypotheses, and provided the star value is finite (so
its `.toReal` is faithful; use `starFunction_lt_top` under an upper bound on `u`), the arc integral
is dominated by the log-polar star surface `starPlane p u w`. Since `arcIntegral_harmonicOn` shows
`arcIntegral p u E` is harmonic — hence equal to its own circle average — this domination on the
upper half of a sub-mean-value circle is the buildable half of the star-surface sub-mean-value. -/
theorem arcIntegral_le_starPlane {p : ℂ} {u : ℂ → ℝ} {E : Set ℝ} {w : ℂ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E))
    (hEmeas : MeasurableSet E) (hwim0 : 0 ≤ w.im) (hwimπ : w.im ≤ π)
    (hE'sub : (fun φ : ℝ => φ + (w.im + π)) '' E ⊆ Set.Icc 0 (2 * π))
    (hEvol : volume E ≤ ENNReal.ofReal (2 * w.im))
    (hfin : starFunction p u (Real.exp w.re) w.im < ⊤) :
    arcIntegral p u E w ≤ starPlane p u w := by
  have hdom := arcIntegral_le_starFunction hu0 hu hint hEmeas hwim0 hwimπ hE'sub hEvol
  have harc0 : (0 : ℝ) ≤ arcIntegral p u E w := by
    rw [arcIntegral]
    exact integral_nonneg (fun φ => hu0 _)
  have := ENNReal.toReal_mono hfin.ne hdom
  rwa [ENNReal.toReal_ofReal harc0] at this

/-- **The extremal-arc identity at the centre.** At any log-polar point `w₀` of the strip
`logPolarStrip rI rO` (so `0 < Im w₀ < π`), the star value `starPlane p u w₀` is *attained* by a
genuine fixed arc-parameter set `E₀`: there is a measurable, bounded `E₀ ⊆ ℝ` of measure exactly
`2·Im w₀` such that the fixed-arc harmonic integral `arcIntegral p u E₀` agrees with the star
surface at `w₀`,

`arcIntegral p u E₀ w₀ = starPlane p u w₀`.

Take `F` to be the extremal super-level set of `exists_attaining_set` for the angular profile `g` at
radius `exp (Re w₀)` and half-aperture `Im w₀` (so `∫⁻_F g = starFunction p u (exp (Re w₀)) (Im w₀)`
and `|F| = 2·Im w₀`), and let `E₀ = (· − (Im w₀ + π)) '' F` be its de-rotation into the
arc-parameter frame. The measure-preserving translation and the pointwise `u ↔ g` circle-point
matching give `ofReal (arcIntegral p u E₀ w₀) = ∫⁻_F g = starFunction p u (exp (Re w₀)) (Im w₀)`,
and taking `.toReal` (faithful since the star value is finite by `starFunction_lt_top` and the arc
integral is nonnegative) yields the identity. The extremal arc reproduces the star value at its
centre, seeding the harmonic competitor `arcIntegral p u E₀`. -/
theorem arcIntegral_eq_starPlane_extremal {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {w₀ : ℂ}
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hbdd : ∃ M : ℝ, ∀ φ : ℝ,
        u (p + (Real.exp w₀.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M)
    (hw₀ : w₀ ∈ logPolarStrip rI rO) :
    ∃ E₀ : Set ℝ, MeasurableSet E₀ ∧ Bornology.IsBounded E₀ ∧
      volume E₀ = ENNReal.ofReal (2 * w₀.im) ∧
      arcIntegral p u E₀ w₀ = starPlane p u w₀ := by
  classical
  obtain ⟨hw₀re, hw₀im⟩ := hw₀
  have hwim0 : 0 ≤ w₀.im := hw₀im.1.le
  have hwimπ : w₀.im ≤ π := hw₀im.2.le
  -- The angular profile `g` at radius `exp (Re w₀)`; `starFunction … = starProfile (2π) g (Im w₀)`.
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal
      (angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w₀.re) ψ).toReal with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp w₀.re)))
  -- STEP A: the extremal attaining set `F ⊆ Icc 0 (2π)` with `∫⁻_F g = starFunction …`.
  obtain ⟨F, hFmeas, hFsub, hFvol, hFint⟩ :=
    exists_attaining_set (T := 2 * π) (g := g) (θ := w₀.im) (by positivity) hgmeas hwim0
      (by linarith)
  have hFstar : (∫⁻ ψ in F, g ψ) = starFunction p u (Real.exp w₀.re) w₀.im := hFint
  -- STEP B: de-rotate `F` into the arc-parameter frame: `E₀ = (· + (−(Im w₀ + π))) '' F`.
  set E₀ : Set ℝ := (fun ψ : ℝ => ψ + (-(w₀.im + π))) '' F with hE₀def
  have hE₀meas : MeasurableSet E₀ :=
    (measurableEmbedding_addRight (-(w₀.im + π))).measurableSet_image.2 hFmeas
  -- `E₀` is bounded: it is a translate of the bounded `F ⊆ Icc 0 (2π)`.
  have hFbdd : Bornology.IsBounded F := (Metric.isBounded_Icc _ _).subset hFsub
  have hE₀bdd : Bornology.IsBounded E₀ := by
    refine (Metric.isBounded_Icc (0 + (-(w₀.im + π))) (2 * π + (-(w₀.im + π)))).subset ?_
    rw [hE₀def]
    rintro _ ⟨ψ, hψ, rfl⟩
    exact ⟨by linarith [(hFsub hψ).1], by linarith [(hFsub hψ).2]⟩
  -- Measure of `E₀` equals that of `F` (translation preserves measure).
  have hE₀vol : volume E₀ = volume F := by
    rw [hE₀def, image_add_right, measure_preimage_add_right]
  -- Rotating `E₀` back gives `F`: `(· + (Im w₀ + π)) '' E₀ = F`.
  have hrotback : (fun φ : ℝ => φ + (w₀.im + π)) '' E₀ = F := by
    rw [hE₀def, ← Set.image_comp]
    convert Set.image_id F using 1
    apply Set.image_congr'
    intro ψ
    simp only [Function.comp_apply, id_eq]
    ring
  -- Integrability of the arc fibre on `E₀` (bounded on a finite-measure set).
  obtain ⟨M, hM⟩ := hbdd
  have hE₀fin : volume E₀ ≠ ⊤ := by
    rw [hE₀vol]
    exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ofReal_ne_top) (measure_mono hFsub)
  have hfibmeas : Measurable (fun φ : ℝ => u (p + Complex.exp (w₀ + φ * Complex.I))) := by
    apply hu.comp
    fun_prop
  have hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w₀ + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E₀) := by
    haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict E₀) :=
      isFiniteMeasure_restrict.2 hE₀fin
    refine Integrable.of_bound hfibmeas.aestronglyMeasurable (max M 0) ?_
    filter_upwards with φ
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨by linarith [hu0 (p + Complex.exp (w₀ + φ * Complex.I)), le_max_right M 0], ?_⟩
    -- `u (p + exp (w₀ + φI)) = u (p + exp (Re w₀) · exp ((Im w₀ + φ)I)) ≤ M ≤ max M 0`.
    have hsplit : w₀ + (φ : ℂ) * Complex.I
        = (w₀.re : ℂ) + ((w₀.im + φ : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp
    have hpt : (p + Complex.exp (w₀ + φ * Complex.I))
        = p + (Real.exp w₀.re : ℂ) * Complex.exp ((w₀.im + φ : ℝ) * Complex.I) := by
      rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
    rw [hpt]
    exact le_trans (hM (w₀.im + φ)) (le_max_left M 0)
  -- STEP C: `ofReal (arcIntegral p u E₀ w₀) = ∫⁻_F g`, via the same chain as the domination lemma.
  have hchain : ENNReal.ofReal (arcIntegral p u E₀ w₀) = ∫⁻ ψ in F, g ψ := by
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w₀ + φ * Complex.I)))
        = g (φ + (w₀.im + π)) := by
      intro φ
      rw [hgdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w₀ + (φ : ℂ) * Complex.I = (w₀.re : ℂ) + ((φ + w₀.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hmp : MeasurePreserving (fun φ : ℝ => φ + (w₀.im + π)) volume volume :=
      measurePreserving_add_right volume (w₀.im + π)
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w₀.im + π)) g
      ((fun φ : ℝ => φ + (w₀.im + π)) '' E₀)
    rw [Set.preimage_image_eq _ (add_left_injective (w₀.im + π)), hrotback] at hkey
    rw [hkey]
  -- Finiteness of the star value and nonnegativity of the arc integral: `.toReal` is faithful.
  have hfin : starFunction p u (Real.exp w₀.re) w₀.im < ⊤ :=
    starFunction_lt_top hwim0 hwimπ ⟨M, hM⟩
  have harc0 : (0 : ℝ) ≤ arcIntegral p u E₀ w₀ := by
    rw [arcIntegral]; exact integral_nonneg (fun φ => hu0 _)
  refine ⟨E₀, hE₀meas, hE₀bdd, by rw [hE₀vol, hFvol], ?_⟩
  -- `ofReal (arcIntegral) = ∫⁻_F g = starFunction`, so `arcIntegral = starPlane` after `.toReal`.
  have heq : ENNReal.ofReal (arcIntegral p u E₀ w₀) = starFunction p u (Real.exp w₀.re) w₀.im := by
    rw [hchain, hFstar]
  rw [starPlane, ← heq, ENNReal.toReal_ofReal harc0]

/-!
## The star-surface sub-mean-value inequality (Sjögren's surgery)

The sub-mean-value inequality for `starPlane p u` at a strip point `w₀` is driven by the harmonic
competitor `arcIntegral p u E₀`, where `E₀` de-rotates an extremal structured set
(`exists_attaining_structured`): a set of measure `2·Im w₀` attaining the star value at the centre
and carrying a full leftmost interval of length `δ`. Four ingredients combine:

* **translate bound** (`volume_translate_inter_le`): the translates `E₀ ± ε` overlap in measure at
  most `|E₀| − 2ε` once `2ε ≤ δ` — sliding the leftmost interval uncovers a window of length `2ε`;
* **window domination** (`arcIntegral_le_starPlane`): opposite circle points `w₀ ± ρe^{iψ}` share
  their radius, and cutting/re-gluing the translated extremal sets along the uncovered window
  yields admissible competitors for both target apertures `2·Im w₀ ± 2ρ·sin ψ`;
* **MVP pairing**: `arcIntegral p u E₀` is harmonic on the strip, so its centre value equals its
  circle average; averaging the paired domination gives the sub-mean-value inequality on all
  circles of radius `ρ < δ/2` (`starPlane_subMeanValue_small`);
* **local-to-global**: continuity (`starPlane_continuousOn`) and the Poisson-modification principle
  (`subharmonicOn_of_locally`) extend the inequality to every admissible radius
  (`starPlane_subharmonicOn`).
-/

/-- **Baernstein's translate bound.** For a set `E` with least element `x₀` carrying a full
interval `[x₀, x₀ + ℓ] ⊆ E` (the leftmost component of `E` has length at least `ℓ`), the two
translates `E + ε` and `E − ε` overlap in measure at most `|E| − 2ε` whenever `2ε ≤ ℓ`: the sliding
of the leftmost component uncovers an interval of length `2ε` that belongs to `E − ε` but meets no
point of `E + ε`. -/
theorem volume_translate_inter_le {E : Set ℝ} {x₀ ℓ : ℝ}
    (hx₀ : IsLeast E x₀) (hIcc : Set.Icc x₀ (x₀ + ℓ) ⊆ E) {ε : ℝ}
    (hεℓ : 2 * ε ≤ ℓ) :
    volume ((fun x => x + ε) '' E ∩ (fun x => x - ε) '' E)
      ≤ volume E - ENNReal.ofReal (2 * ε) := by
  -- The uncovered window `[x₀ − ε, x₀ + ε)` lies inside `E − ε` but misses `E + ε` entirely.
  have hwin : Ico (x₀ - ε) (x₀ + ε) ⊆ (fun x => x - ε) '' E := by
    intro x hx
    refine ⟨x + ε, hIcc ⟨by linarith [hx.1], by linarith [hx.2]⟩, by ring⟩
  have hsub : (fun x => x + ε) '' E ∩ (fun x => x - ε) '' E
      ⊆ (fun x => x - ε) '' E \ Ico (x₀ - ε) (x₀ + ε) := by
    rintro y ⟨⟨e₁, he₁, rfl⟩, hy₂⟩
    refine ⟨hy₂, fun hy => ?_⟩
    exact absurd hy.2 (not_lt.mpr (by linarith [hx₀.2 he₁]))
  -- Translates preserve volume; removing the window subtracts exactly `2ε`.
  have hvol₂ : volume ((fun x => x - ε) '' E) = volume E := by
    have himg : (fun x : ℝ => x - ε) '' E = (fun x : ℝ => x + (-ε)) '' E := by
      apply Set.image_congr'
      intro x; ring
    rw [himg, image_add_right, measure_preimage_add_right]
  calc volume ((fun x => x + ε) '' E ∩ (fun x => x - ε) '' E)
      ≤ volume ((fun x => x - ε) '' E \ Ico (x₀ - ε) (x₀ + ε)) := measure_mono hsub
    _ = volume ((fun x => x - ε) '' E) - volume (Ico (x₀ - ε) (x₀ + ε)) :=
        measure_diff hwin measurableSet_Ico.nullMeasurableSet
          (by rw [Real.volume_Ico]; exact ofReal_ne_top)
    _ = volume E - ENNReal.ofReal (2 * ε) := by
        rw [hvol₂, Real.volume_Ico]
        congr 1
        ring_nf

/-- **Windowed fixed-arc domination.** The conclusion of `arcIntegral_le_starFunction` under a
relaxed window hypothesis: the rotated arc `E' = (· + (Im w + π)) '' E` need only fit in *some*
interval `[a, a + 2π]` of length `2π`, not necessarily `[0, 2π]`. Since the angular profile is
`2π`-periodic, the two pieces of `E'` on either side of the lattice point `2π·⌈a/(2π)⌉` can be
shifted by integer multiples of `2π` into the standard window `[0, 2π]` without changing the
integral or the measure, and the standard supremum characterisation of the star profile applies. -/
theorem arcIntegral_le_starFunction_window {p : ℂ} {u : ℂ → ℝ} {E : Set ℝ} {w : ℂ} (a : ℝ)
    (hu0 : ∀ z, 0 ≤ u z) (hu : Measurable u)
    (hint : Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
      ((volume : Measure ℝ).restrict E))
    (hEmeas : MeasurableSet E) (hwim0 : 0 ≤ w.im) (hwimπ : w.im ≤ π)
    (hE'sub : (fun φ : ℝ => φ + (w.im + π)) '' E ⊆ Set.Icc a (a + 2 * π))
    (hEvol : volume E ≤ ENNReal.ofReal (2 * w.im)) :
    ENNReal.ofReal (arcIntegral p u E w) ≤ starFunction p u (Real.exp w.re) w.im := by
  classical
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal
      (angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w.re) ψ).toReal with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp w.re)))
  -- The profile is `2π`-periodic (through any integer number of turns).
  have hgper : ∀ (n : ℤ) (φ : ℝ), g (φ + 2 * π * n) = g φ := by
    intro n φ
    rw [hgdef]
    simp only [angularProfile]
    congr 3
    have hsplit : ((φ + 2 * π * n - π : ℝ) : ℂ) * Complex.I
        = ((φ - π : ℝ) : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  set E' : Set ℝ := (fun φ : ℝ => φ + (w.im + π)) '' E with hE'def
  have hE'meas : MeasurableSet E' :=
    (measurableEmbedding_addRight (w.im + π)).measurableSet_image.2 hEmeas
  have hE'vol : volume E' = volume E := by
    rw [hE'def, image_add_right, measure_preimage_add_right]
  -- Integral chain: `ofReal (arcIntegral) = ∫⁻_{E'} g`.
  have hchain : ENNReal.ofReal (arcIntegral p u E w) = ∫⁻ ψ in E', g ψ := by
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w + φ * Complex.I)))
        = g (φ + (w.im + π)) := by
      intro φ
      rw [hgdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w + (φ : ℂ) * Complex.I = (w.re : ℂ) + ((φ + w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hmp : MeasurePreserving (fun φ : ℝ => φ + (w.im + π)) volume volume :=
      measurePreserving_add_right volume (w.im + π)
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w.im + π)) g
      ((fun φ : ℝ => φ + (w.im + π)) '' E)
    rw [Set.preimage_image_eq _ (add_left_injective (w.im + π))] at hkey
    rw [hkey]
  -- Split `E'` at the lattice point `2π·k`, `k = ⌈a/(2π)⌉`.
  set k : ℤ := ⌈a / (2 * π)⌉ with hkdef
  have hπpos : (0 : ℝ) < 2 * π := by positivity
  have ha1 : a ≤ 2 * π * k := by
    have := Int.le_ceil (a / (2 * π))
    rw [div_le_iff₀ hπpos] at this
    linarith [this]
  have ha2 : 2 * π * k ≤ a + 2 * π := by
    have := Int.ceil_lt_add_one (a / (2 * π))
    have h2 : (k : ℝ) * (2 * π) < (a / (2 * π) + 1) * (2 * π) :=
      mul_lt_mul_of_pos_right this hπpos
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hπpos), one_mul] at h2
    linarith
  set s₀ : ℝ := a + 2 * π - 2 * π * k with hs₀def
  have hs₀0 : 0 ≤ s₀ := by rw [hs₀def]; linarith
  have hs₀2π : s₀ ≤ 2 * π := by rw [hs₀def]; linarith
  set E₁ : Set ℝ := E' ∩ Iio (2 * π * k) with hE₁def
  set E₂ : Set ℝ := E' ∩ Ici (2 * π * k) with hE₂def
  have hE₁meas : MeasurableSet E₁ := hE'meas.inter measurableSet_Iio
  have hE₂meas : MeasurableSet E₂ := hE'meas.inter measurableSet_Ici
  have hEsplit : E' = E₁ ∪ E₂ := by
    rw [hE₁def, hE₂def, ← inter_union_distrib_left, Iio_union_Ici, inter_univ]
  have hEdisj : Disjoint E₁ E₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
    exact absurd (mem_Ici.mp hx2) (not_le.mpr (mem_Iio.mp hx1))
  -- Shift each piece by an integer multiple of `2π` into `[0, 2π]`.
  set c₁ : ℝ := 2 * π * (1 - k) with hc₁def
  set c₂ : ℝ := 2 * π * (0 - k) with hc₂def
  set D₁ : Set ℝ := (fun x => x + c₁) '' E₁ with hD₁def
  set D₂ : Set ℝ := (fun x => x + c₂) '' E₂ with hD₂def
  have hD₁meas : MeasurableSet D₁ := (measurableEmbedding_addRight c₁).measurableSet_image.2 hE₁meas
  have hD₂meas : MeasurableSet D₂ := (measurableEmbedding_addRight c₂).measurableSet_image.2 hE₂meas
  -- Periodic shift invariance of the profile integral.
  have hshift : ∀ (n : ℤ) (S : Set ℝ),
      (∫⁻ ψ in (fun x => x + 2 * π * (n : ℝ)) '' S, g ψ) = ∫⁻ φ in S, g φ := by
    intro n S
    have hmp : MeasurePreserving (fun φ : ℝ => φ + 2 * π * (n : ℝ)) volume volume :=
      measurePreserving_add_right volume _
    have hkey := hmp.setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight (2 * π * (n : ℝ))) g ((fun x => x + 2 * π * (n : ℝ)) '' S)
    rw [Set.preimage_image_eq _ (add_left_injective _)] at hkey
    rw [← hkey]
    exact lintegral_congr_ae (Filter.Eventually.of_forall (fun φ => hgper n φ))
  have hint₁ : (∫⁻ ψ in D₁, g ψ) = ∫⁻ ψ in E₁, g ψ := by
    rw [hD₁def, hc₁def, show (2 * π * ((1 : ℝ) - k)) = 2 * π * (((1 - k : ℤ) : ℝ)) from by
      push_cast; ring]
    exact hshift (1 - k) E₁
  have hint₂ : (∫⁻ ψ in D₂, g ψ) = ∫⁻ ψ in E₂, g ψ := by
    rw [hD₂def, hc₂def, show (2 * π * ((0 : ℝ) - k)) = 2 * π * (((0 - k : ℤ) : ℝ)) from by
      push_cast; ring]
    exact hshift (0 - k) E₂
  have hvol₁ : volume D₁ = volume E₁ := by rw [hD₁def, image_add_right, measure_preimage_add_right]
  have hvol₂ : volume D₂ = volume E₂ := by rw [hD₂def, image_add_right, measure_preimage_add_right]
  -- The shifted pieces land in `[0, 2π]`, meeting at most at the seam point `s₀`.
  have hD₁sub : D₁ ⊆ Ico s₀ (2 * π) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE', hxlt⟩ := hx
    have hxa : a ≤ x := (hE'sub hxE').1
    constructor
    · rw [hs₀def, hc₁def]; push_cast; linarith
    · rw [hc₁def]; push_cast; linarith [mem_Iio.mp hxlt]
  have hD₂sub : D₂ ⊆ Icc 0 s₀ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE', hxge⟩ := hx
    have hxa : x ≤ a + 2 * π := (hE'sub hxE').2
    constructor
    · rw [hc₂def]; push_cast; linarith [mem_Ici.mp hxge]
    · rw [hs₀def, hc₂def]; push_cast; linarith
  have hDinter : volume (D₁ ∩ D₂) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (measure_singleton s₀)
    have h1 := hD₁sub hx.1
    have h2 := hD₂sub hx.2
    exact le_antisymm h2.2 h1.1
  -- Sum of the two shifted integrals is the integral over the union.
  have hsum : (∫⁻ ψ in D₁, g ψ) + ∫⁻ ψ in D₂, g ψ = ∫⁻ ψ in D₁ ∪ D₂, g ψ := by
    have hd₁ : (∫⁻ ψ in D₁, g ψ) = ∫⁻ ψ in D₁ \ D₂, g ψ := by
      conv_lhs => rw [← Set.diff_union_inter D₁ D₂]
      rw [lintegral_union (hD₁meas.inter hD₂meas) Set.disjoint_sdiff_inter,
        setLIntegral_measure_zero _ _ hDinter, add_zero]
    rw [hd₁, ← lintegral_union hD₂meas disjoint_sdiff_left, Set.diff_union_self]
  -- The union is an admissible competitor for the star profile.
  set D : Set ℝ := D₁ ∪ D₂ with hDdef
  have hDmeas : MeasurableSet D := hD₁meas.union hD₂meas
  have hDsub : D ⊆ Icc 0 (2 * π) := by
    rintro x (hx | hx)
    · exact ⟨le_trans hs₀0 (hD₁sub hx).1, (hD₁sub hx).2.le⟩
    · exact ⟨(hD₂sub hx).1, le_trans (hD₂sub hx).2 hs₀2π⟩
  have hDvol : volume D ≤ ENNReal.ofReal (2 * w.im) := by
    calc volume D ≤ volume D₁ + volume D₂ := measure_union_le _ _
      _ = volume E₁ + volume E₂ := by rw [hvol₁, hvol₂]
      _ = volume E' := by rw [← measure_union hEdisj hE₂meas, ← hEsplit]
      _ ≤ ENNReal.ofReal (2 * w.im) := by rw [hE'vol]; exact hEvol
  -- Extend `D` to measure exactly `2·Im w` and conclude via the supremum characterisation.
  obtain ⟨F, hDF, hFsub, hFmeas, hFvol⟩ :=
    exists_measurableSet_superset_volume (m := 2 * w.im)
      (by positivity : (0 : ℝ) ≤ 2 * π) D hDmeas hDsub
      (by positivity) hDvol (by linarith)
  have hmono : (∫⁻ ψ in D, g ψ) ≤ ∫⁻ ψ in F, g ψ := lintegral_mono_set hDF
  have hsup : starFunction p u (Real.exp w.re) w.im
      = ⨆ F' ∈ {F' : Set ℝ | MeasurableSet F' ∧ F' ⊆ Icc (0 : ℝ) (2 * π)
          ∧ volume F' = ENNReal.ofReal (2 * w.im)}, ∫⁻ ψ in F', g ψ := by
    rw [show starFunction p u (Real.exp w.re) w.im = starProfile (2 * π) g w.im from rfl]
    exact starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hwim0 (by linarith)
  calc ENNReal.ofReal (arcIntegral p u E w) = ∫⁻ ψ in E', g ψ := hchain
    _ = (∫⁻ ψ in E₁, g ψ) + ∫⁻ ψ in E₂, g ψ := by
        rw [hEsplit, lintegral_union hE₂meas hEdisj]
    _ = (∫⁻ ψ in D₁, g ψ) + ∫⁻ ψ in D₂, g ψ := by rw [hint₁, hint₂]
    _ = ∫⁻ ψ in D, g ψ := hsum
    _ ≤ ∫⁻ ψ in F, g ψ := hmono
    _ ≤ starFunction p u (Real.exp w.re) w.im := by
        rw [hsup]
        exact le_iSup₂_of_le F ⟨hFmeas, hFsub, hFvol⟩ le_rfl

/-- **Structured extremal attaining set for a harmonic profile.** For `u` harmonic and nonnegative
on the annulus and a radius `r ∈ (rI, rO)`, the star value at half-aperture `θ ∈ (0, π)` is
attained by a set `F` carrying the level structure of the real-analytic circle profile: `F` sits
in a `2π`-window `[τ + δ, τ + 2π − δ]` with slack `δ > 0`, has measure exactly `2θ`, and its least
point carries a full interval `[x₀, x₀ + δ] ⊆ F` (the leftmost component of `F` is an honest
interval). For a non-constant circle profile `G`, the level `c` of the rearrangement has finite
level set on any compact window (one-dimensional identity theorem for the real-analytic `G`), and
`F` is the union of the closed arcs between consecutive zeros of `G − c` on which `G > c`; the
window base `τ` is a point with `G τ < c`, which exists because the super-level measure `2θ` is
less than the full circle `2π`. For a constant profile a centered arc attains. -/
theorem exists_attaining_structured {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {r θ : ℝ}
    (hrI : 0 < rI)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u)
    (hr : r ∈ Set.Ioo rI rO) (hθ : θ ∈ Set.Ioo 0 π) :
    ∃ (τ δ : ℝ) (F : Set ℝ), 0 < δ ∧ MeasurableSet F ∧
      F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
      volume F = ENNReal.ofReal (2 * θ) ∧
      (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
      (∫⁻ ψ in F, ENNReal.ofReal
          ((angularProfile p (fun z => ENNReal.ofReal (u z)) r ψ).toReal))
        = starFunction p u r θ := by
  classical
  obtain ⟨hθ0, hθπ⟩ := hθ
  set A : Set ℂ := {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} with hA
  set g : ℝ → ℝ≥0∞ :=
    fun ψ => ENNReal.ofReal ((angularProfile p (fun z => ENNReal.ofReal (u z)) r ψ).toReal)
    with hgdef
  set G : ℝ → ℝ := fun ψ => u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) with hGdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) r))
  have hgG : ∀ ψ : ℝ, g ψ = ENNReal.ofReal (G ψ) := by
    intro ψ
    simp only [hgdef, hGdef, angularProfile]
    rw [ENNReal.toReal_ofReal (hu0 _)]
  have hG0 : ∀ ψ : ℝ, 0 ≤ G ψ := fun ψ => hu0 _
  rcases Classical.em (∀ ψ₁ ψ₂ : ℝ, G ψ₁ = G ψ₂) with hconst | hconst
  · -- Constant circle profile: any measure-`2θ` set attains; take the centered arc.
    have hgc : ∀ ψ : ℝ, g ψ = ENNReal.ofReal (G 0) := by
      intro ψ; rw [hgG ψ, hconst ψ 0]
    have hval : ∀ E : Set ℝ, volume E = ENNReal.ofReal (2 * θ) →
        (∫⁻ ψ in E, g ψ) = ENNReal.ofReal (G 0) * ENNReal.ofReal (2 * θ) := by
      intro E hE
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hgc), setLIntegral_const, hE]
    have hFsub' : Icc (π - θ) (π + θ) ⊆ Icc (0 : ℝ) (2 * π) := by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hFvol' : volume (Icc (π - θ) (π + θ)) = ENNReal.ofReal (2 * θ) := by
      rw [Real.volume_Icc]; congr 1; ring
    have hFmem : Icc (π - θ) (π + θ) ∈ {E : Set ℝ | MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) (2 * π)
        ∧ volume E = ENNReal.ofReal (2 * θ)} := ⟨measurableSet_Icc, hFsub', hFvol'⟩
    have hstar : starFunction p u r θ = ENNReal.ofReal (G 0) * ENNReal.ofReal (2 * θ) := by
      rw [show starFunction p u r θ = starProfile (2 * π) g θ from rfl,
        starProfile_eq_iSup_setLIntegral (by positivity) hgmeas hθ0.le (by linarith)]
      apply le_antisymm
      · exact iSup₂_le fun E hE => le_of_eq (hval E hE.2.2)
      · exact le_iSup₂_of_le _ hFmem (le_of_eq (hval _ hFvol').symm)
    refine ⟨0, min (π - θ) θ, Icc (π - θ) (π + θ), lt_min (by linarith) hθ0,
      measurableSet_Icc, ?_, hFvol', ⟨π - θ, ⟨⟨le_rfl, by linarith⟩, fun y hy => hy.1⟩, ?_⟩, ?_⟩
    · intro x hx
      constructor
      · have := min_le_left (π - θ) θ; linarith [hx.1]
      · have := min_le_left (π - θ) θ; linarith [hx.2]
    · intro x hx
      have := min_le_right (π - θ) θ
      exact ⟨hx.1, by linarith [hx.2]⟩
    · rw [hval _ hFvol', hstar]
  · -- Non-constant circle profile: identity theorem + arcs between consecutive zeros of `G − c`.
    push Not at hconst
    obtain ⟨ψ₁, ψ₂, hne⟩ := hconst
    have hπpos : (0 : ℝ) < 2 * π := by positivity
    -- Continuity, membership, analyticity of the circle profile.
    have hAopen : IsOpen A := by
      have h1 : IsOpen {z : ℂ | rI < ‖z - p‖} := isOpen_lt continuous_const (by fun_prop)
      have h2 : IsOpen {z : ℂ | ‖z - p‖ < rO} := isOpen_lt (by fun_prop) continuous_const
      simpa [hA, Set.setOf_and] using h1.inter h2
    have hmA : ∀ ψ : ℝ, (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) ∈ A := by
      intro ψ
      have hn : ‖(p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) - p‖ = r := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real,
          Real.norm_eq_abs]
        have him : ((((ψ - π : ℝ)) : ℂ) * Complex.I).re = 0 := by
          simp [Complex.mul_re]
        rw [him, Real.exp_zero, mul_one, abs_of_pos (lt_trans hrI hr.1)]
      rw [hA]
      exact ⟨by rw [hn]; exact hr.1, by rw [hn]; exact hr.2⟩
    have hucont : ContinuousOn u A := hu.continuousOn
    have hGcont : Continuous G := by
      rw [continuous_iff_continuousAt]
      intro ψ
      have hmc : Continuous
          (fun ψ : ℝ => p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) := by fun_prop
      have hcomp := ContinuousAt.comp (x := ψ) (g := u)
        (hucont.continuousAt (hAopen.mem_nhds (hmA ψ))) hmc.continuousAt
      exact hcomp
    have hGanal : ∀ ψ : ℝ, AnalyticAt ℝ G ψ := by
      intro ψ
      have h0 : AnalyticAt ℝ (fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I) ψ := by
        have heqf : (fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I)
            = fun ψ : ℝ => (Complex.ofRealCLM ψ - ((π : ℝ) : ℂ)) * Complex.I := by
          funext φ
          rw [Complex.ofRealCLM_apply, Complex.ofReal_sub]
        rw [heqf]
        exact ((Complex.ofRealCLM.analyticAt ψ).sub analyticAt_const).mul analyticAt_const
      have hexpR : AnalyticAt ℝ Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I) :=
        @AnalyticAt.restrictScalars ℝ _ ℂ ℂ _ _ _ _ ℂ _ _ _ IsScalarTower.right _
          IsScalarTower.right _ _ analyticAt_cexp
      have h1 : AnalyticAt ℝ
          (fun ψ : ℝ => Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) ψ :=
        AnalyticAt.comp (g := Complex.exp)
          (f := fun ψ : ℝ => (((ψ - π : ℝ)) : ℂ) * Complex.I) hexpR h0
      have h2 : AnalyticAt ℝ
          (fun ψ : ℝ => p + (r : ℂ) * Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) ψ :=
        analyticAt_const.add (analyticAt_const.mul h1)
      have h3 : AnalyticAt ℝ u (p + (r : ℂ) * Complex.exp (((ψ - π : ℝ)) * Complex.I)) :=
        HarmonicAt.analyticAt (hu _ (hmA ψ))
      have h4 := AnalyticAt.comp (g := u)
        (f := fun ψ : ℝ => p + (r : ℂ) * Complex.exp ((((ψ - π : ℝ)) : ℂ) * Complex.I)) h3 h2
      exact h4
    -- Periodicity of the profile in the angle, through any integer number of turns.
    have hGperZ : ∀ (n : ℤ) (ψ : ℝ), G (ψ + 2 * π * n) = G ψ := by
      intro n ψ
      have harg : Complex.exp (((ψ + 2 * π * n - π : ℝ)) * Complex.I)
          = Complex.exp (((ψ - π : ℝ)) * Complex.I) := by
        have hsplit : (((ψ + 2 * π * n - π : ℝ)) : ℂ) * Complex.I
            = (((ψ - π : ℝ)) : ℂ) * Complex.I + (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
          push_cast; ring
        rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      simp only [hGdef, harg]
    have hGper : ∀ ψ : ℝ, G (ψ + 2 * π) = G ψ := by
      intro ψ; simpa using hGperZ 1 ψ
    have hgperZ : ∀ (n : ℤ) (ψ : ℝ), g (ψ + 2 * π * n) = g ψ := by
      intro n ψ; rw [hgG, hgG, hGperZ]
    -- Uniform bound on the profile, by compactness and periodic reduction.
    have hred : ∀ ψ : ℝ, ∃ s ∈ Icc (0 : ℝ) (2 * π), G ψ = G s := by
      intro ψ
      set n : ℤ := ⌊ψ / (2 * π)⌋ with hn
      have h1 : (n : ℝ) * (2 * π) ≤ ψ := by
        have := Int.floor_le (ψ / (2 * π))
        rwa [le_div_iff₀ hπpos] at this
      have h2 : ψ < ((n : ℝ) + 1) * (2 * π) := by
        have := Int.lt_floor_add_one (ψ / (2 * π))
        rwa [div_lt_iff₀ hπpos] at this
      refine ⟨ψ - 2 * π * n, ⟨by linarith, by linarith⟩, ?_⟩
      have := hGperZ n (ψ - 2 * π * n)
      rwa [sub_add_cancel] at this
    obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcont.continuousOn
    have hMle : ∀ ψ : ℝ, G ψ ≤ max M0 0 := by
      intro ψ
      obtain ⟨s, hs, hGs⟩ := hred ψ
      rw [hGs]
      calc G s ≤ |G s| := le_abs_self _
        _ ≤ M0 := hM0 s hs
        _ ≤ max M0 0 := le_max_left _ _
    have hgleM : ∀ ψ : ℝ, g ψ ≤ ENNReal.ofReal (max M0 0) := by
      intro ψ
      rw [hgG]
      exact ENNReal.ofReal_le_ofReal (hMle ψ)
    -- The rearrangement level `c` at measure `2θ`, and its real form `c'`.
    set c : ℝ≥0∞ := decreasingRearrange (2 * π) g (2 * θ) with hcdef
    have hP1 : distribFun (2 * π) g c ≤ ENNReal.ofReal (2 * θ) :=
      distribFun_decreasingRearrange_le (2 * θ)
    have hlt : ∀ t : ℝ≥0∞, t < c → ENNReal.ofReal (2 * θ) < distribFun (2 * π) g t :=
      fun t ht => (lt_decreasingRearrange_iff (2 * θ) t).mp ht
    have hcne : c ≠ ⊤ := by
      intro hctop
      have h1 : ENNReal.ofReal (max M0 0) < c := by rw [hctop]; exact ENNReal.ofReal_lt_top
      have h2 := hlt _ h1
      have hempty : distribFun (2 * π) g (ENNReal.ofReal (max M0 0)) = 0 := by
        have hset : {y ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal (max M0 0) < g y} = ∅ := by
          ext y
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun _ => not_lt.mpr (hgleM y)
        rw [distribFun, hset, measure_empty]
      rw [hempty] at h2
      exact absurd h2 (not_lt.mpr (zero_le _))
    set c' : ℝ := c.toReal with hc'def
    have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
    have hcoe : c = ENNReal.ofReal c' := (ENNReal.ofReal_toReal hcne).symm
    have hsuper_iff : ∀ ψ : ℝ, c < g ψ ↔ c' < G ψ := by
      intro ψ
      rw [hgG, hcoe]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc'0
    have heq_iff : ∀ ψ : ℝ, g ψ = c ↔ G ψ = c' := by
      intro ψ
      rw [hgG, hcoe]
      exact ENNReal.ofReal_eq_ofReal_iff (hG0 ψ) hc'0
    -- Lower distribution bound at the level `c` (right-continuity of the distribution function).
    have hP2 : ENNReal.ofReal (2 * θ) ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} := by
      rcases eq_or_ne c 0 with hc0 | hc0
      · have hset : {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} = Icc (0 : ℝ) (2 * π) := by
          ext x; simp only [mem_setOf_eq, hc0, zero_le, and_true]
        rw [hset, Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · obtain ⟨v, hvmono, hvmem, hvtend⟩ :=
          exists_seq_strictMono_tendsto' (pos_iff_ne_zero.mpr hc0)
        set s : ℕ → Set ℝ := fun n => {x ∈ Icc (0 : ℝ) (2 * π) | v n < g x} with hs
        have hsmeas : ∀ n, MeasurableSet (s n) :=
          fun n => measurableSet_Icc.inter (measurableSet_lt measurable_const hgmeas)
        have hsanti : Antitone s :=
          fun i j hij x hx => ⟨hx.1, lt_of_le_of_lt (hvmono.monotone hij) hx.2⟩
        have hsfin : ∃ n, volume (s n) ≠ ⊤ := by
          refine ⟨0, ne_top_of_le_ne_top ?_ (measure_mono (fun x hx => hx.1))⟩
          rw [Real.volume_Icc]; exact ofReal_ne_top
        have hInter : ⋂ n, s n = {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x} := by
          ext x
          simp only [mem_iInter, hs, mem_setOf_eq]
          constructor
          · intro h; exact ⟨(h 0).1, le_of_tendsto' hvtend (fun n => (h n).2.le)⟩
          · rintro ⟨hxI, hxc⟩ n; exact ⟨hxI, lt_of_lt_of_le (hvmem n).2 hxc⟩
        have htend : Tendsto (fun n => volume (s n)) atTop (𝓝 (volume (⋂ n, s n))) :=
          tendsto_measure_iInter_atTop (fun n => (hsmeas n).nullMeasurableSet) hsanti hsfin
        rw [hInter] at htend
        exact ge_of_tendsto' htend (fun n => (hlt (v n) (hvmem n).2).le)
    -- Finiteness of every level set of `G` on every compact window: identity theorem.
    have hlevfin : ∀ d lo hi : ℝ, Set.Finite {ψ ∈ Icc lo hi | G ψ = d} := by
      intro d lo hi
      by_contra hinf
      rw [Set.not_finite] at hinf
      obtain ⟨x, -, hacc⟩ :=
        hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun ψ hψ => hψ.1)
      have hfreq : ∃ᶠ y in 𝓝[≠] x, G y - d = 0 := by
        rw [frequently_nhdsWithin_iff]
        exact (accPt_iff_frequently.mp hacc).mono
          (fun y hy => ⟨by rw [sub_eq_zero]; exact hy.2.2, hy.1⟩)
      have hanal : AnalyticOnNhd ℝ (fun ψ => G ψ - d) univ :=
        fun ψ _ => (hGanal ψ).sub analyticAt_const
      have heqz := hanal.eqOn_zero_of_preconnected_of_frequently_eq_zero
        isPreconnected_univ (mem_univ x) hfreq
      have h1 := heqz (mem_univ ψ₁)
      have h2 := heqz (mem_univ ψ₂)
      simp only [Pi.zero_apply, sub_eq_zero] at h1 h2
      exact hne (h1.trans h2.symm)
    -- Null atoms and the exact super-level measure `2θ`.
    have hatomnull : volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} = 0 := by
      have hset : {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}
          = {x ∈ Icc (0 : ℝ) (2 * π) | G x = c'} := by
        ext x
        simp only [mem_setOf_eq]
        exact and_congr_right (fun _ => heq_iff x)
      rw [hset]
      exact ((hlevfin c' 0 (2 * π)).countable).measure_zero _
    have hsupvol : volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} = ENNReal.ofReal (2 * θ) := by
      refine le_antisymm hP1 (le_trans hP2 ?_)
      have hsplit : {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x}
          ⊆ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := by
        rintro x ⟨hxI, hxc⟩
        rcases eq_or_lt_of_le hxc with h | h
        · exact Or.inr ⟨hxI, h.symm⟩
        · exact Or.inl ⟨hxI, h⟩
      calc volume {x ∈ Icc (0 : ℝ) (2 * π) | c ≤ g x}
          ≤ volume ({x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}) := measure_mono hsplit
        _ ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              + volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := measure_union_le _ _
        _ = volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} := by rw [hatomnull, add_zero]
    -- The window base `τ`: a point strictly below the level.
    obtain ⟨τ, hτlt⟩ : ∃ τ : ℝ, G τ < c' := by
      by_contra hcon
      push Not at hcon
      have hsubs : Icc (0 : ℝ) (2 * π) ⊆ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
          ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := by
        intro x hx
        rcases eq_or_lt_of_le (hcon x) with h | h
        · exact Or.inr ⟨hx, (heq_iff x).mpr h.symm⟩
        · exact Or.inl ⟨hx, (hsuper_iff x).mpr h⟩
      have hchain : ENNReal.ofReal (2 * π) ≤ ENNReal.ofReal (2 * θ) := by
        calc ENNReal.ofReal (2 * π) = volume (Icc (0 : ℝ) (2 * π)) := by
              rw [Real.volume_Icc, sub_zero]
          _ ≤ volume ({x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              ∪ {x ∈ Icc (0 : ℝ) (2 * π) | g x = c}) := measure_mono hsubs
          _ ≤ volume {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}
              + volume {x ∈ Icc (0 : ℝ) (2 * π) | g x = c} := measure_union_le _ _
          _ = ENNReal.ofReal (2 * θ) := by rw [hsupvol, hatomnull, add_zero]
      have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
      linarith
    have hGτ2π : G (τ + 2 * π) < c' := by rw [hGper τ]; exact hτlt
    -- The finite zero set of `G − c'` on the window `[τ, τ + 2π]`.
    have hZfin : Set.Finite {ψ ∈ Icc τ (τ + 2 * π) | G ψ = c'} := hlevfin c' τ (τ + 2 * π)
    set Zs : Finset ℝ := hZfin.toFinset with hZsdef
    have hZmem : ∀ z : ℝ, z ∈ Zs ↔ z ∈ Icc τ (τ + 2 * π) ∧ G z = c' := by
      intro z
      rw [hZsdef, Set.Finite.mem_toFinset]
      exact Iff.rfl
    -- Sign constancy on zero-free open intervals, by the intermediate value theorem.
    have hsign : ∀ z₁ z₂ : ℝ, (∀ y ∈ Ioo z₁ z₂, G y ≠ c') →
        ∀ y₁ ∈ Ioo z₁ z₂, c' < G y₁ → ∀ y ∈ Ioo z₁ z₂, c' < G y := by
      intro z₁ z₂ hnz y₁ hy₁ hy₁gt y hy
      rcases lt_trichotomy (G y) c' with hlt2 | heq2 | hgt2
      · exfalso
        rcases lt_trichotomy y y₁ with hyy | rfl | hyy
        · obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo hyy.le hGcont.continuousOn
            (show c' ∈ Ioo (G y) (G y₁) from ⟨hlt2, hy₁gt⟩)
          exact hnz z ⟨lt_trans hy.1 hz.1, lt_trans hz.2 hy₁.2⟩ hzval
        · exact absurd hy₁gt (not_lt.mpr hlt2.le)
        · obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo' hyy.le hGcont.continuousOn
            (show c' ∈ Ioo (G y) (G y₁) from ⟨hlt2, hy₁gt⟩)
          exact hnz z ⟨lt_trans hy₁.1 hz.1, lt_trans hz.2 hy.2⟩ hzval
      · exact absurd heq2 (hnz y hy)
      · exact hgt2
    -- Every super-level point has zeros of `G − c'` on both sides within the window.
    have hlevbelow : ∀ ψ : ℝ, ψ ∈ Ioo τ (τ + 2 * π) → c' < G ψ → ∃ z ∈ Zs, z < ψ := by
      intro ψ hψ hψgt
      obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo hψ.1.le hGcont.continuousOn
        (show c' ∈ Ioo (G τ) (G ψ) from ⟨hτlt, hψgt⟩)
      exact ⟨z, (hZmem z).mpr ⟨⟨hz.1.le, by linarith [hz.2, hψ.2]⟩, hzval⟩, hz.2⟩
    have hlevabove : ∀ ψ : ℝ, ψ ∈ Ioo τ (τ + 2 * π) → c' < G ψ → ∃ z ∈ Zs, ψ < z := by
      intro ψ hψ hψgt
      obtain ⟨z, hz, hzval⟩ := intermediate_value_Ioo' hψ.2.le hGcont.continuousOn
        (show c' ∈ Ioo (G (τ + 2 * π)) (G ψ) from ⟨hGτ2π, hψgt⟩)
      exact ⟨z, (hZmem z).mpr ⟨⟨by linarith [hz.1, hψ.1], hz.2.le⟩, hzval⟩, hz.1⟩
    -- The qualifying zero pairs and the attaining set `F`.
    set Q : Finset (ℝ × ℝ) :=
      (Zs ×ˢ Zs).filter (fun q => q.1 < q.2 ∧ ∀ y ∈ Ioo q.1 q.2, c' < G y) with hQdef
    set F : Set ℝ := ⋃ q ∈ Q, Icc q.1 q.2 with hFdef
    have hQprop : ∀ q ∈ Q, q.1 ∈ Zs ∧ q.2 ∈ Zs ∧ q.1 < q.2 ∧ ∀ y ∈ Ioo q.1 q.2, c' < G y := by
      intro q hq
      rw [hQdef, Finset.mem_filter, Finset.mem_product] at hq
      exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
    have hFmeas : MeasurableSet F :=
      hFdef ▸ Q.measurableSet_biUnion (fun q _ => measurableSet_Icc)
    have hFmem : ∀ y : ℝ, y ∈ F ↔ ∃ q ∈ Q, y ∈ Icc q.1 q.2 := by
      intro y
      rw [hFdef]
      simp only [Set.mem_iUnion, exists_prop]
    -- The core super-level set and the two-sided sandwich for `F`.
    set S : Set ℝ := {ψ : ℝ | c' < G ψ} with hSdef
    have hSmeas : MeasurableSet S := measurableSet_lt measurable_const hGcont.measurable
    have hFcore : S ∩ Ioo τ (τ + 2 * π) ⊆ F := by
      rintro ψ ⟨hψgt, hψI⟩
      rw [hSdef, mem_setOf_eq] at hψgt
      obtain ⟨zb, hzbZ, hzblt⟩ := hlevbelow ψ hψI hψgt
      obtain ⟨za, hzaZ, hzagt⟩ := hlevabove ψ hψI hψgt
      have hbne : (Zs.filter (fun z => z < ψ)).Nonempty :=
        ⟨zb, Finset.mem_filter.mpr ⟨hzbZ, hzblt⟩⟩
      have hane : (Zs.filter (fun z => ψ < z)).Nonempty :=
        ⟨za, Finset.mem_filter.mpr ⟨hzaZ, hzagt⟩⟩
      set zl : ℝ := (Zs.filter (fun z => z < ψ)).max' hbne with hzldef
      set zr : ℝ := (Zs.filter (fun z => ψ < z)).min' hane with hzrdef
      have hzlmem := Finset.mem_filter.mp ((Zs.filter (fun z => z < ψ)).max'_mem hbne)
      have hzrmem := Finset.mem_filter.mp ((Zs.filter (fun z => ψ < z)).min'_mem hane)
      have hnolevel : ∀ y ∈ Ioo zl zr, G y ≠ c' := by
        intro y hy hyval
        have hyZs : y ∈ Zs := by
          refine (hZmem y).mpr ⟨⟨?_, ?_⟩, hyval⟩
          · exact le_trans ((hZmem zl).mp hzlmem.1).1.1 hy.1.le
          · exact le_trans hy.2.le ((hZmem zr).mp hzrmem.1).1.2
        rcases lt_trichotomy y ψ with h | h | h
        · exact absurd (Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hyZs, h⟩))
            (not_le.mpr hy.1)
        · exact absurd (h ▸ hyval).symm (ne_of_lt hψgt)
        · exact absurd (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyZs, h⟩))
            (not_le.mpr hy.2)
      have hqQ : (zl, zr) ∈ Q := by
        rw [hQdef, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hzlmem.1, hzrmem.1⟩, lt_trans hzlmem.2 hzrmem.2,
          hsign zl zr hnolevel ψ ⟨hzlmem.2, hzrmem.2⟩ hψgt⟩
      exact (hFmem ψ).mpr ⟨(zl, zr), hqQ, ⟨hzlmem.2.le, hzrmem.2.le⟩⟩
    have hFsub : F ⊆ (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ) := by
      intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hFmem y).mp hy
      obtain ⟨hq1, hq2, hqlt, hqpos⟩ := hQprop q hqQ
      rcases eq_or_lt_of_le hyq.1 with h1 | h1
      · exact Or.inr (Finset.mem_coe.mpr (h1 ▸ hq1))
      · rcases eq_or_lt_of_le hyq.2 with h2 | h2
        · exact Or.inr (Finset.mem_coe.mpr (h2 ▸ hq2))
        · refine Or.inl ⟨hqpos y ⟨h1, h2⟩, ?_, ?_⟩
          · exact lt_of_le_of_lt ((hZmem q.1).mp hq1).1.1 h1
          · exact lt_of_lt_of_le h2 ((hZmem q.2).mp hq2).1.2
    -- Periodic transfer of measure and integral from the `τ`-window to the standard window.
    have hshiftIoc : ∀ (f : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), f (x + 2 * π * n) = f x) →
        ∀ (n : ℤ) (a b : ℝ),
          (∫⁻ x in Ioc a b, f x) = ∫⁻ x in Ioc (a + 2 * π * n) (b + 2 * π * n), f x := by
      intro f hper n a b
      have hmp : MeasurePreserving (fun x : ℝ => x + 2 * π * (n : ℝ)) volume volume :=
        measurePreserving_add_right volume _
      have hkey2 := hmp.setLIntegral_comp_preimage_emb
        (measurableEmbedding_addRight (2 * π * (n : ℝ))) f
        (Ioc (a + 2 * π * (n : ℝ)) (b + 2 * π * (n : ℝ)))
      have hpre : (fun x : ℝ => x + 2 * π * (n : ℝ)) ⁻¹'
          Ioc (a + 2 * π * (n : ℝ)) (b + 2 * π * (n : ℝ)) = Ioc a b := by
        ext x
        simp only [mem_preimage, mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
      rw [hpre] at hkey2
      rw [← hkey2]
      exact lintegral_congr_ae (Filter.Eventually.of_forall (fun x => (hper n x).symm))
    have hperwin : ∀ (f : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), f (x + 2 * π * n) = f x) →
        (∫⁻ x in Ioc τ (τ + 2 * π), f x) = ∫⁻ x in Ioc 0 (2 * π), f x := by
      intro f hper
      set k : ℤ := ⌈τ / (2 * π)⌉ with hkdef
      have ha1 : τ ≤ 2 * π * k := by
        have h1 := Int.le_ceil (τ / (2 * π))
        rw [div_le_iff₀ hπpos] at h1
        linarith
      have ha2 : 2 * π * k ≤ τ + 2 * π := by
        have h1 := Int.ceil_lt_add_one (τ / (2 * π))
        have h2 : (k : ℝ) * (2 * π) < (τ / (2 * π) + 1) * (2 * π) :=
          mul_lt_mul_of_pos_right h1 hπpos
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hπpos), one_mul] at h2
        linarith
      set s₀ : ℝ := τ + 2 * π - 2 * π * k with hs₀def
      have hs₀0 : 0 ≤ s₀ := by rw [hs₀def]; linarith
      have hs₀2π : s₀ ≤ 2 * π := by rw [hs₀def]; linarith
      have hdisj1 : Disjoint (Ioc τ (2 * π * k)) (Ioc (2 * π * k) (τ + 2 * π)) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, h1⟩ ⟨h2, -⟩
        exact absurd h2 (not_lt.mpr h1)
      have hdisj2 : Disjoint (Ioc (0 : ℝ) s₀) (Ioc s₀ (2 * π)) := by
        rw [Set.disjoint_left]
        rintro x ⟨-, h1⟩ ⟨h2, -⟩
        exact absurd h2 (not_lt.mpr h1)
      have hs1 : (∫⁻ x in Ioc τ (2 * π * k), f x) = ∫⁻ x in Ioc s₀ (2 * π), f x := by
        rw [hshiftIoc f hper (1 - k) τ (2 * π * k)]
        have he1 : τ + 2 * π * ((1 - k : ℤ) : ℝ) = s₀ := by push_cast; rw [hs₀def]; ring
        have he2 : 2 * π * k + 2 * π * ((1 - k : ℤ) : ℝ) = 2 * π := by push_cast; ring
        rw [he1, he2]
      have hs2 : (∫⁻ x in Ioc (2 * π * k) (τ + 2 * π), f x) = ∫⁻ x in Ioc 0 s₀, f x := by
        rw [hshiftIoc f hper (0 - k) (2 * π * k) (τ + 2 * π)]
        have he1 : 2 * π * k + 2 * π * ((0 - k : ℤ) : ℝ) = 0 := by push_cast; ring
        have he2 : τ + 2 * π + 2 * π * ((0 - k : ℤ) : ℝ) = s₀ := by push_cast; rw [hs₀def]; ring
        rw [he1, he2]
      calc (∫⁻ x in Ioc τ (τ + 2 * π), f x)
          = (∫⁻ x in Ioc τ (2 * π * k), f x) + ∫⁻ x in Ioc (2 * π * k) (τ + 2 * π), f x := by
            rw [← lintegral_union measurableSet_Ioc hdisj1, Ioc_union_Ioc_eq_Ioc ha1 ha2]
        _ = (∫⁻ x in Ioc s₀ (2 * π), f x) + ∫⁻ x in Ioc 0 s₀, f x := by rw [hs1, hs2]
        _ = (∫⁻ x in Ioc (0 : ℝ) s₀, f x) + ∫⁻ x in Ioc s₀ (2 * π), f x := add_comm _ _
        _ = ∫⁻ x in Ioc 0 (2 * π), f x := by
            rw [← lintegral_union measurableSet_Ioc hdisj2, Ioc_union_Ioc_eq_Ioc hs₀0 hs₀2π]
    have hSmemper : ∀ (n : ℤ) (x : ℝ), x + 2 * π * n ∈ S ↔ x ∈ S := by
      intro n x
      simp only [hSdef, mem_setOf_eq, hGperZ]
    have hindper : ∀ (h : ℝ → ℝ≥0∞), (∀ (n : ℤ) (x : ℝ), h (x + 2 * π * n) = h x) →
        ∀ (n : ℤ) (x : ℝ), S.indicator h (x + 2 * π * n) = S.indicator h x := by
      intro h hper n x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem ((hSmemper n x).mpr hx), Set.indicator_of_mem hx, hper]
      · rw [Set.indicator_of_notMem (fun hc => hx ((hSmemper n x).mp hc)),
          Set.indicator_of_notMem hx]
    have hindint : ∀ T : Set ℝ, (∫⁻ x in T, S.indicator g x) = ∫⁻ x in S ∩ T, g x := by
      intro T
      rw [lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas]
    have hindvol : ∀ T : Set ℝ,
        (∫⁻ x in T, S.indicator (fun _ => (1 : ℝ≥0∞)) x) = volume (S ∩ T) := by
      intro T
      rw [lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas, setLIntegral_one]
    have hIoo : (volume : Measure ℝ).restrict (Ioo τ (τ + 2 * π))
        = volume.restrict (Ioc τ (τ + 2 * π)) := Measure.restrict_congr_set Ioo_ae_eq_Ioc
    have hIcc : (volume : Measure ℝ).restrict (Icc (0 : ℝ) (2 * π))
        = volume.restrict (Ioc (0 : ℝ) (2 * π)) := Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
    have hcorevol : volume (S ∩ Ioo τ (τ + 2 * π)) = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by
      rw [← hindvol (Ioo τ (τ + 2 * π)), ← hindvol (Icc (0 : ℝ) (2 * π))]
      calc (∫⁻ x in Ioo τ (τ + 2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x)
          = ∫⁻ x in Ioc τ (τ + 2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x := by rw [hIoo]
        _ = ∫⁻ x in Ioc 0 (2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x :=
            hperwin _ (hindper _ (fun n x => rfl))
        _ = ∫⁻ x in Icc (0 : ℝ) (2 * π), S.indicator (fun _ => (1 : ℝ≥0∞)) x := by rw [hIcc]
    have hcoreint : (∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ)
        = ∫⁻ ψ in S ∩ Icc (0 : ℝ) (2 * π), g ψ := by
      rw [← hindint (Ioo τ (τ + 2 * π)), ← hindint (Icc (0 : ℝ) (2 * π))]
      calc (∫⁻ x in Ioo τ (τ + 2 * π), S.indicator g x)
          = ∫⁻ x in Ioc τ (τ + 2 * π), S.indicator g x := by rw [hIoo]
        _ = ∫⁻ x in Ioc 0 (2 * π), S.indicator g x := hperwin _ (hindper _ hgperZ)
        _ = ∫⁻ x in Icc (0 : ℝ) (2 * π), S.indicator g x := by rw [hIcc]
    -- Identify the standard-window core with the super-level set of `g`.
    have hident : {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} = S ∩ Icc (0 : ℝ) (2 * π) := by
      ext x
      simp only [mem_setOf_eq, mem_inter_iff, hSdef]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(hsuper_iff x).mp h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, (hsuper_iff x).mpr h1⟩
    have hZsnull : volume (Zs : Set ℝ) = 0 := Zs.countable_toSet.measure_zero _
    -- Volume of `F` is exactly `2θ`.
    have hFvol : volume F = ENNReal.ofReal (2 * θ) := by
      apply le_antisymm
      · calc volume F ≤ volume ((S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ)) := measure_mono hFsub
          _ ≤ volume (S ∩ Ioo τ (τ + 2 * π)) + volume (Zs : Set ℝ) := measure_union_le _ _
          _ = volume (S ∩ Icc (0 : ℝ) (2 * π)) := by rw [hZsnull, add_zero, hcorevol]
          _ = ENNReal.ofReal (2 * θ) := by rw [← hident]; exact hsupvol
      · calc ENNReal.ofReal (2 * θ) = volume (S ∩ Ioo τ (τ + 2 * π)) := by
              rw [hcorevol, ← hident]; exact hsupvol.symm
          _ ≤ volume F := measure_mono hFcore
    -- Layer-cake attainment: the integral over the super-level core is the star value.
    have hEstar : (∫⁻ x in {x ∈ Icc (0 : ℝ) (2 * π) | c < g x}, g x)
        = starFunction p u r θ := by
      have hkey : ∀ t : ℝ, volume {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
          = min (ENNReal.ofReal (2 * θ)) (distribFun (2 * π) g (ENNReal.ofReal t)) := by
        intro t
        rcases le_or_gt c (ENNReal.ofReal t) with hct | hct
        · have hset : {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
              = {x ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal t < g x} := by
            ext x
            simp only [mem_setOf_eq]
            constructor
            · rintro ⟨⟨hxI, -⟩, hlt2⟩; exact ⟨hxI, hlt2⟩
            · rintro ⟨hxI, hlt2⟩; exact ⟨⟨hxI, lt_of_le_of_lt hct hlt2⟩, hlt2⟩
          rw [hset]
          change distribFun (2 * π) g (ENNReal.ofReal t) = _
          rw [min_eq_right (le_trans (distribFun_antitone hct) hP1)]
        · have hset : {x ∈ {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} | ENNReal.ofReal t < g x}
              = {x ∈ Icc (0 : ℝ) (2 * π) | c < g x} := by
            ext x
            simp only [mem_setOf_eq]
            constructor
            · rintro ⟨hx, -⟩; exact hx
            · intro hx; exact ⟨hx, lt_trans hct hx.2⟩
          rw [hset, hsupvol, min_eq_left (hlt _ hct).le]
      rw [show starFunction p u r θ = starProfile (2 * π) g θ from rfl,
        starProfile_eq_lintegral_min (by positivity) hθ0.le (by linarith),
        lintegral_eq_lintegral_meas_lt_ennreal hgmeas]
      exact lintegral_congr (fun t => hkey t)
    -- Integral of `g` over `F` equals the star value.
    have hFstar : (∫⁻ ψ in F, g ψ) = starFunction p u r θ := by
      have hup : (∫⁻ ψ in F, g ψ) ≤ ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ := by
        calc (∫⁻ ψ in F, g ψ)
            ≤ ∫⁻ ψ in (S ∩ Ioo τ (τ + 2 * π)) ∪ (Zs : Set ℝ), g ψ := lintegral_mono_set hFsub
          _ ≤ (∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ) + ∫⁻ ψ in (Zs : Set ℝ), g ψ :=
              lintegral_union_le _ _ _
          _ = ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ := by
              rw [setLIntegral_measure_zero _ _ hZsnull, add_zero]
      have heq1 : (∫⁻ ψ in F, g ψ) = ∫⁻ ψ in S ∩ Ioo τ (τ + 2 * π), g ψ :=
        le_antisymm hup (lintegral_mono_set hFcore)
      rw [heq1, hcoreint, ← hident, hEstar]
    -- Nonemptiness and the extremal endpoints.
    have hFne : F.Nonempty := by
      apply nonempty_of_measure_ne_zero (μ := volume)
      rw [hFvol]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    obtain ⟨y₀, hy₀F⟩ := hFne
    obtain ⟨qq, hqqQ, -⟩ := (hFmem y₀).mp hy₀F
    have hQne : Q.Nonempty := ⟨qq, hqqQ⟩
    have hZsne : Zs.Nonempty := ⟨qq.1, (hQprop qq hqqQ).1⟩
    have hminτ : τ < Zs.min' hZsne := by
      have hmem := (hZmem _).mp (Zs.min'_mem hZsne)
      rcases eq_or_lt_of_le hmem.1.1 with h | h
      · exact absurd (h ▸ hmem.2) (ne_of_lt hτlt)
      · exact h
    have hmaxτ : Zs.max' hZsne < τ + 2 * π := by
      have hmem := (hZmem _).mp (Zs.max'_mem hZsne)
      rcases eq_or_lt_of_le hmem.1.2 with h | h
      · exact absurd (h ▸ hmem.2) (ne_of_lt hGτ2π)
      · exact h
    have hFwin : F ⊆ Icc (Zs.min' hZsne) (Zs.max' hZsne) := by
      intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hFmem y).mp hy
      obtain ⟨h1, h2, -, -⟩ := hQprop q hqQ
      exact ⟨le_trans (Finset.min'_le _ _ h1) hyq.1, le_trans hyq.2 (Finset.le_max' _ _ h2)⟩
    have hfne : (Q.image Prod.fst).Nonempty := hQne.image _
    obtain ⟨q₀, hq₀Q, hq₀eq⟩ := Finset.mem_image.mp ((Q.image Prod.fst).min'_mem hfne)
    obtain ⟨hq₀1Z, hq₀2Z, hq₀lt, -⟩ := hQprop q₀ hq₀Q
    -- Assemble the slack `δ` and conclude.
    refine ⟨τ, min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1), F,
      lt_min (lt_min (by linarith) (by linarith)) (by linarith), hFmeas, ?_, hFvol,
      ⟨q₀.1, ⟨(hFmem q₀.1).mpr ⟨q₀, hq₀Q, ⟨le_rfl, hq₀lt.le⟩⟩, ?_⟩, ?_⟩, hFstar⟩
    · intro y hy
      have h := hFwin hy
      constructor
      · have hδ1 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
            ≤ Zs.min' hZsne - τ := le_trans (min_le_left _ _) (min_le_left _ _)
        linarith [h.1]
      · have hδ2 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
            ≤ τ + 2 * π - Zs.max' hZsne := le_trans (min_le_left _ _) (min_le_right _ _)
        linarith [h.2]
    · intro y hy
      obtain ⟨q, hqQ, hyq⟩ := (hFmem y).mp hy
      have hle : (Q.image Prod.fst).min' hfne ≤ q.1 :=
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, hqQ, rfl⟩)
      rw [← hq₀eq] at hle
      linarith [hyq.1]
    · intro y hy
      refine (hFmem y).mpr ⟨q₀, hq₀Q, ⟨hy.1, ?_⟩⟩
      have hδ3 : min (min (Zs.min' hZsne - τ) (τ + 2 * π - Zs.max' hZsne)) (q₀.2 - q₀.1)
          ≤ q₀.2 - q₀.1 := min_le_right _ _
      linarith [hy.2]

/-- **Continuity of the star function on the log-polar strip.** For `u` continuous on the annulus
and nonnegative, `starPlane p u` is continuous on the open strip: the aperture dependence is
continuous from the layer-cake representation by dominated convergence, and the radial dependence
is continuous because the circle profiles of a continuous function vary continuously in `L¹`. -/
theorem starPlane_continuousOn {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hucont : ContinuousOn u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u) :
    ContinuousOn (starPlane p u) (logPolarStrip rI rO) := by
  intro w₀ hw₀
  obtain ⟨hw₀re, hw₀im⟩ := hw₀
  -- A compact log-radius window `[a, b]` around `Re w₀` inside `(log rI, log rO)`.
  set a : ℝ := (Real.log rI + w₀.re) / 2 with hadef
  set b : ℝ := (w₀.re + Real.log rO) / 2 with hbdef
  have ha1 : Real.log rI < a := by rw [hadef]; linarith [hw₀re.1]
  have ha2 : a < w₀.re := by rw [hadef]; linarith [hw₀re.1]
  have hb1 : w₀.re < b := by rw [hbdef]; linarith [hw₀re.2]
  have hb2 : b < Real.log rO := by rw [hbdef]; linarith [hw₀re.2]
  have hw₀ab : w₀.re ∈ Icc a b := ⟨ha2.le, hb1.le⟩
  -- The radial family of circle profiles entering `starFunction`.
  set g : ℝ → ℝ → ℝ≥0∞ := fun ξ φ => ENNReal.ofReal
    ((angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp ξ) φ).toReal) with hgdef
  have hgm : ∀ ξ : ℝ, Measurable (g ξ) := by
    intro ξ
    rw [hgdef]
    exact ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
      (measurable_angularProfile p (fun z => ENNReal.ofReal (u z)) (by fun_prop) (Real.exp ξ)))
  have hgV : ∀ ξ φ : ℝ, g ξ φ
      = ENNReal.ofReal (u (p + (Real.exp ξ : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I))) := by
    intro ξ φ
    rw [hgdef]
    simp only [angularProfile]
    rw [ENNReal.toReal_ofReal (hu0 _)]
  have hSP : ∀ w : ℂ, starPlane p u w = (starProfile (2 * π) (g w.re) w.im).toReal := by
    intro w
    rw [hgdef]
    rfl
  -- The circle sample map is continuous on the compact window.
  have hQcomp : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) (2 * π)) := isCompact_Icc.prod isCompact_Icc
  have hVcont : ContinuousOn
      (fun q : ℝ × ℝ => u (p + (Real.exp q.1 : ℂ) * Complex.exp ((q.2 - π : ℝ) * Complex.I)))
      (Icc a b ×ˢ Icc (0 : ℝ) (2 * π)) := by
    have hPhi : Continuous
        (fun q : ℝ × ℝ => p + (Real.exp q.1 : ℂ) * Complex.exp ((q.2 - π : ℝ) * Complex.I)) := by
      fun_prop
    refine hucont.comp hPhi.continuousOn ?_
    rintro ⟨ξ, φ⟩ ⟨hξ, -⟩
    simp only [Set.mem_setOf_eq]
    have hnorm : ‖p + (Real.exp ξ : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I) - p‖
        = Real.exp ξ := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, Real.abs_exp]
      simp [Complex.mul_re]
    rw [hnorm]
    constructor
    · have hlt := Real.exp_lt_exp.mpr (lt_of_lt_of_le ha1 hξ.1)
      rwa [Real.exp_log hrI] at hlt
    · have hlt := Real.exp_lt_exp.mpr (lt_of_le_of_lt hξ.2 hb2)
      rwa [Real.exp_log (lt_trans hrI hrO)] at hlt
  -- A uniform bound `M` for the circle samples over the window.
  obtain ⟨M, hM⟩ := hQcomp.exists_bound_of_continuousOn hVcont
  have hM0 : 0 ≤ M := by
    have h0mem : ((w₀.re, 0) : ℝ × ℝ) ∈ Icc a b ×ˢ Icc (0 : ℝ) (2 * π) :=
      Set.mk_mem_prod hw₀ab ⟨le_refl 0, by positivity⟩
    exact le_trans (norm_nonneg _) (hM _ h0mem)
  have hgle : ∀ ξ ∈ Icc a b, ∀ φ ∈ Icc (0 : ℝ) (2 * π), g ξ φ ≤ ENNReal.ofReal M := by
    intro ξ hξ φ hφ
    rw [hgV ξ φ]
    exact ENNReal.ofReal_le_ofReal
      (le_trans (le_abs_self _) (hM (ξ, φ) (Set.mk_mem_prod hξ hφ)))
  -- The pointwise bound transfers to the symmetric-decreasing rearrangement.
  have hrearr : ∀ ξ ∈ Icc a b, ∀ x : ℝ,
      decreasingRearrangeSymm (2 * π) (g ξ) x ≤ ENNReal.ofReal M := by
    intro ξ hξ x
    by_contra hcon
    have hlt : ENNReal.ofReal M < decreasingRearrange (2 * π) (g ξ) (2 * |x - 2 * π / 2|) :=
      not_le.mp hcon
    rw [lt_decreasingRearrange_iff] at hlt
    have hempty : distribFun (2 * π) (g ξ) (ENNReal.ofReal M) = 0 := by
      have hset : {y ∈ Icc (0 : ℝ) (2 * π) | ENNReal.ofReal M < g ξ y} = ∅ := by
        ext y
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro hy
        exact not_lt.mpr (hgle ξ hξ y hy)
      rw [distribFun, hset, measure_empty]
    rw [hempty] at hlt
    exact absurd hlt (not_lt.mpr (zero_le _))
  -- Aperture Lipschitz bound: widening the centered arc adds at most the boundary mass.
  have hthetaLip : ∀ ξ ∈ Icc a b, ∀ θ θ' : ℝ, θ ≤ θ' →
      starProfile (2 * π) (g ξ) θ'
        ≤ starProfile (2 * π) (g ξ) θ + ENNReal.ofReal (2 * M * (θ' - θ)) := by
    intro ξ hξ θ θ' hθθ'
    have hMθ : 0 ≤ M * (θ' - θ) := mul_nonneg hM0 (by linarith)
    have hpiece : ∀ c d : ℝ, d - c ≤ θ' - θ →
        (∫⁻ x in Icc c d, decreasingRearrangeSymm (2 * π) (g ξ) x)
          ≤ ENNReal.ofReal (M * (θ' - θ)) := by
      intro c d hcd
      calc (∫⁻ x in Icc c d, decreasingRearrangeSymm (2 * π) (g ξ) x)
          ≤ ∫⁻ _ in Icc c d, ENNReal.ofReal M := lintegral_mono fun x => hrearr ξ hξ x
        _ = ENNReal.ofReal M * volume (Icc c d) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal M * ENNReal.ofReal (θ' - θ) := by
            refine mul_le_mul_right ?_ _
            rw [Real.volume_Icc]
            exact ENNReal.ofReal_le_ofReal hcd
        _ = ENNReal.ofReal (M * (θ' - θ)) := (ENNReal.ofReal_mul hM0).symm
    have hsub : Icc (2 * π / 2 - θ') (2 * π / 2 + θ')
        ⊆ Icc (2 * π / 2 - θ) (2 * π / 2 + θ)
          ∪ (Icc (2 * π / 2 - θ') (2 * π / 2 - θ) ∪ Icc (2 * π / 2 + θ) (2 * π / 2 + θ')) := by
      intro x hx
      rcases le_or_gt x (2 * π / 2 - θ) with h | h
      · exact Or.inr (Or.inl ⟨hx.1, h⟩)
      · rcases le_or_gt x (2 * π / 2 + θ) with h2 | h2
        · exact Or.inl ⟨h.le, h2⟩
        · exact Or.inr (Or.inr ⟨h2.le, hx.2⟩)
    calc starProfile (2 * π) (g ξ) θ'
        = ∫⁻ x in Icc (2 * π / 2 - θ') (2 * π / 2 + θ'),
            decreasingRearrangeSymm (2 * π) (g ξ) x := rfl
      _ ≤ ∫⁻ x in Icc (2 * π / 2 - θ) (2 * π / 2 + θ)
            ∪ (Icc (2 * π / 2 - θ') (2 * π / 2 - θ)
              ∪ Icc (2 * π / 2 + θ) (2 * π / 2 + θ')),
            decreasingRearrangeSymm (2 * π) (g ξ) x := lintegral_mono_set hsub
      _ ≤ (∫⁻ x in Icc (2 * π / 2 - θ) (2 * π / 2 + θ),
              decreasingRearrangeSymm (2 * π) (g ξ) x)
            + ∫⁻ x in Icc (2 * π / 2 - θ') (2 * π / 2 - θ)
                ∪ Icc (2 * π / 2 + θ) (2 * π / 2 + θ'),
                decreasingRearrangeSymm (2 * π) (g ξ) x := lintegral_union_le _ _ _
      _ ≤ starProfile (2 * π) (g ξ) θ
            + ((∫⁻ x in Icc (2 * π / 2 - θ') (2 * π / 2 - θ),
                  decreasingRearrangeSymm (2 * π) (g ξ) x)
              + ∫⁻ x in Icc (2 * π / 2 + θ) (2 * π / 2 + θ'),
                  decreasingRearrangeSymm (2 * π) (g ξ) x) :=
          add_le_add le_rfl (lintegral_union_le _ _ _)
      _ ≤ starProfile (2 * π) (g ξ) θ
            + (ENNReal.ofReal (M * (θ' - θ)) + ENNReal.ofReal (M * (θ' - θ))) :=
          add_le_add le_rfl (add_le_add (hpiece _ _ (by linarith)) (hpiece _ _ (by linarith)))
      _ = starProfile (2 * π) (g ξ) θ + ENNReal.ofReal (2 * M * (θ' - θ)) := by
          rw [← ENNReal.ofReal_add hMθ hMθ,
            show M * (θ' - θ) + M * (θ' - θ) = 2 * M * (θ' - θ) from by ring]
  -- Two-sided aperture estimate via monotonicity.
  have htheta : ∀ ξ ∈ Icc a b, ∀ θ θ' : ℝ, 0 ≤ θ → 0 ≤ θ' →
      starProfile (2 * π) (g ξ) θ'
        ≤ starProfile (2 * π) (g ξ) θ + ENNReal.ofReal (2 * M * |θ' - θ|) := by
    intro ξ hξ θ θ' hθ0 hθ'0
    rcases le_total θ' θ with h | h
    · exact le_trans
        (monotone_starProfile (2 * π) (g ξ) (Set.mem_Ici.mpr hθ'0) (Set.mem_Ici.mpr hθ0) h)
        le_self_add
    · have hLip := hthetaLip ξ hξ θ θ' h
      rwa [abs_of_nonneg (sub_nonneg.mpr h)]
  -- Radial comparison: uniformly close circle profiles have close star profiles.
  have hxi : ∀ ξ ξ' θ : ℝ, 0 ≤ θ → θ ≤ π → ∀ ε : ℝ,
      (∀ φ ∈ Icc (0 : ℝ) (2 * π), g ξ φ ≤ g ξ' φ + ENNReal.ofReal ε) →
      starProfile (2 * π) (g ξ) θ
        ≤ starProfile (2 * π) (g ξ') θ + ENNReal.ofReal ε * ENNReal.ofReal (2 * π) := by
    intro ξ ξ' θ hθ0 hθπ ε hcomp
    rw [starProfile_eq_iSup_setLIntegral (by positivity) (hgm ξ) hθ0 (by linarith)]
    refine iSup₂_le ?_
    rintro E ⟨hEmeas, hEsub, hEvol⟩
    have h1 : (∫⁻ φ in E, g ξ φ) ≤ ∫⁻ φ in E, (g ξ' φ + ENNReal.ofReal ε) :=
      setLIntegral_mono' hEmeas fun φ hφ => hcomp φ (hEsub hφ)
    have h2 : (∫⁻ φ in E, (g ξ' φ + ENNReal.ofReal ε))
        = (∫⁻ φ in E, g ξ' φ) + ENNReal.ofReal ε * volume E := by
      rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    have h3 : (∫⁻ φ in E, g ξ' φ) ≤ starProfile (2 * π) (g ξ') θ := by
      rw [starProfile_eq_iSup_setLIntegral (by positivity) (hgm ξ') hθ0 (by linarith)]
      exact le_iSup₂_of_le E ⟨hEmeas, hEsub, hEvol⟩ le_rfl
    calc (∫⁻ φ in E, g ξ φ)
        ≤ (∫⁻ φ in E, g ξ' φ) + ENNReal.ofReal ε * volume E := h2 ▸ h1
      _ ≤ starProfile (2 * π) (g ξ') θ + ENNReal.ofReal ε * ENNReal.ofReal (2 * π) := by
          refine add_le_add h3 (mul_le_mul_right ?_ _)
          rw [hEvol]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Finiteness of star values over the window.
  have hfin : ∀ ξ ∈ Icc a b, ∀ θ : ℝ, starProfile (2 * π) (g ξ) θ ≠ ⊤ := by
    intro ξ hξ θ
    have hle : starProfile (2 * π) (g ξ) θ
        ≤ ENNReal.ofReal M * volume (Icc (2 * π / 2 - θ) (2 * π / 2 + θ)) := by
      calc starProfile (2 * π) (g ξ) θ
          = ∫⁻ x in Icc (2 * π / 2 - θ) (2 * π / 2 + θ),
              decreasingRearrangeSymm (2 * π) (g ξ) x := rfl
        _ ≤ ∫⁻ _ in Icc (2 * π / 2 - θ) (2 * π / 2 + θ), ENNReal.ofReal M :=
            lintegral_mono fun x => hrearr ξ hξ x
        _ = _ := setLIntegral_const _ _
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hle
  -- ε–δ assembly.
  rw [Metric.continuousWithinAt_iff]
  intro ε' hε'
  have hεpos : 0 < ε' / (2 * (2 * π + 1)) := div_pos hε' (by positivity)
  have hδ₂pos : 0 < ε' / (2 * (2 * M + 1)) := div_pos hε' (by linarith)
  have hUC := hQcomp.uniformContinuousOn_of_continuous hVcont
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hUC (ε' / (2 * (2 * π + 1))) hεpos
  refine ⟨min (min δ₁ (ε' / (2 * (2 * M + 1)))) (min (w₀.re - a) (b - w₀.re)),
    lt_min (lt_min hδ₁pos hδ₂pos) (lt_min (by linarith) (by linarith)), ?_⟩
  intro w hws hwd
  obtain ⟨-, hwim⟩ := hws
  have hre : |w.re - w₀.re| ≤ dist w w₀ := by
    rw [Complex.dist_eq, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have him : |w.im - w₀.im| ≤ dist w w₀ := by
    rw [Complex.dist_eq, ← Complex.sub_im]
    exact Complex.abs_im_le_norm _
  have hd₁ : dist w w₀ < δ₁ :=
    lt_of_lt_of_le hwd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd₂ : dist w w₀ < ε' / (2 * (2 * M + 1)) :=
    lt_of_lt_of_le hwd (le_trans (min_le_left _ _) (min_le_right _ _))
  have hd₃ : dist w w₀ < w₀.re - a :=
    lt_of_lt_of_le hwd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd₄ : dist w w₀ < b - w₀.re :=
    lt_of_lt_of_le hwd (le_trans (min_le_right _ _) (min_le_right _ _))
  have hwab : w.re ∈ Icc a b := by
    have h5 := abs_lt.mp (lt_of_le_of_lt hre hd₃)
    have h6 := abs_lt.mp (lt_of_le_of_lt hre hd₄)
    exact ⟨by linarith [h5.1], by linarith [h6.2]⟩
  -- The circle samples at radii `exp (Re w)` and `exp (Re w₀)` are uniformly close.
  have hVclose : ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      |u (p + (Real.exp w.re : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I))
        - u (p + (Real.exp w₀.re : ℂ) * Complex.exp ((φ - π : ℝ) * Complex.I))|
        < ε' / (2 * (2 * π + 1)) := by
    intro φ hφ
    have hdp : dist ((w.re, φ) : ℝ × ℝ) ((w₀.re, φ) : ℝ × ℝ) < δ₁ := by
      refine lt_of_le_of_lt (le_trans ?_ hre) hd₁
      rw [Prod.dist_eq]
      apply max_le
      · exact le_of_eq (Real.dist_eq _ _)
      · exact le_trans (le_of_eq (dist_self φ)) (abs_nonneg _)
    have hd := hδ₁ (w.re, φ) (Set.mk_mem_prod hwab hφ) (w₀.re, φ)
      (Set.mk_mem_prod hw₀ab hφ) hdp
    rwa [Real.dist_eq] at hd
  have hcomp1 : ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      g w.re φ ≤ g w₀.re φ + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) := by
    intro φ hφ
    have habs := abs_lt.mp (hVclose φ hφ)
    rw [hgV w.re φ, hgV w₀.re φ]
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith [habs.2])) ENNReal.ofReal_add_le
  have hcomp2 : ∀ φ ∈ Icc (0 : ℝ) (2 * π),
      g w₀.re φ ≤ g w.re φ + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) := by
    intro φ hφ
    have habs := abs_lt.mp (hVclose φ hφ)
    rw [hgV w.re φ, hgV w₀.re φ]
    exact le_trans (ENNReal.ofReal_le_ofReal (by linarith [habs.1])) ENNReal.ofReal_add_le
  -- Two-sided ENNReal estimate between the two star values.
  have hchain1 : starProfile (2 * π) (g w.re) w.im
      ≤ starProfile (2 * π) (g w₀.re) w₀.im
        + (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)) := by
    calc starProfile (2 * π) (g w.re) w.im
        ≤ starProfile (2 * π) (g w₀.re) w.im
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          hxi w.re w₀.re w.im hwim.1.le hwim.2.le _ hcomp1
      _ ≤ (starProfile (2 * π) (g w₀.re) w₀.im + ENNReal.ofReal (2 * M * |w.im - w₀.im|))
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          add_le_add_left (htheta w₀.re hw₀ab w₀.im w.im hw₀im.1.le hwim.1.le) _
      _ = _ := add_assoc _ _ _
  have hchain2 : starProfile (2 * π) (g w₀.re) w₀.im
      ≤ starProfile (2 * π) (g w.re) w.im
        + (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)) := by
    calc starProfile (2 * π) (g w₀.re) w₀.im
        ≤ starProfile (2 * π) (g w.re) w₀.im
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          hxi w₀.re w.re w₀.im hw₀im.1.le hw₀im.2.le _ hcomp2
      _ ≤ (starProfile (2 * π) (g w.re) w.im + ENNReal.ofReal (2 * M * |w₀.im - w.im|))
          + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π) :=
          add_le_add_left (htheta w.re hwab w.im w₀.im hwim.1.le hw₀im.1.le) _
      _ = _ := by rw [abs_sub_comm w₀.im w.im, add_assoc]
  -- Transfer to real values.
  have hCne : (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
      + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hCtR : (ENNReal.ofReal (2 * M * |w.im - w₀.im|)
      + ENNReal.ofReal (ε' / (2 * (2 * π + 1))) * ENNReal.ofReal (2 * π)).toReal
      = 2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π) := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (by linarith) (abs_nonneg _)),
      ENNReal.toReal_ofReal hεpos.le, ENNReal.toReal_ofReal (by positivity)]
  have ht1 : (starProfile (2 * π) (g w.re) w.im).toReal
      ≤ (starProfile (2 * π) (g w₀.re) w₀.im).toReal
        + (2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π)) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfin w₀.re hw₀ab w₀.im, hCne⟩) hchain1
    rwa [ENNReal.toReal_add (hfin w₀.re hw₀ab w₀.im) hCne, hCtR] at hmono
  have ht2 : (starProfile (2 * π) (g w₀.re) w₀.im).toReal
      ≤ (starProfile (2 * π) (g w.re) w.im).toReal
        + (2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π)) := by
    have hmono := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfin w.re hwab w.im, hCne⟩) hchain2
    rwa [ENNReal.toReal_add (hfin w.re hwab w.im) hCne, hCtR] at hmono
  -- The explicit bound is below `ε'`.
  have hnum : 2 * M * |w.im - w₀.im| + ε' / (2 * (2 * π + 1)) * (2 * π) < ε' := by
    have h1 : |w.im - w₀.im| < ε' / (2 * (2 * M + 1)) := lt_of_le_of_lt him hd₂
    have h2 : 2 * M * |w.im - w₀.im| ≤ 2 * M * (ε' / (2 * (2 * M + 1))) :=
      mul_le_mul_of_nonneg_left h1.le (by linarith)
    have h3 : 2 * M * (ε' / (2 * (2 * M + 1))) ≤ ε' / 2 := by
      have hstep : 2 * M * (ε' / (2 * (2 * M + 1)))
          ≤ (2 * M + 1) * (ε' / (2 * (2 * M + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) hδ₂pos.le
      have heq : (2 * M + 1) * (ε' / (2 * (2 * M + 1))) = ε' / 2 := by
        rw [← mul_div_assoc, div_eq_div_iff
          (ne_of_gt (by linarith : (0 : ℝ) < 2 * (2 * M + 1))) (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      linarith
    have h4 : ε' / (2 * (2 * π + 1)) * (2 * π) < ε' / 2 := by
      have hstep : ε' / (2 * (2 * π + 1)) * (2 * π)
          < ε' / (2 * (2 * π + 1)) * (2 * π + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hεpos
      have heq : ε' / (2 * (2 * π + 1)) * (2 * π + 1) = ε' / 2 := by
        rw [div_mul_eq_mul_div, div_eq_div_iff
          (by positivity : (2 * (2 * π + 1) : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      linarith
    linarith
  rw [hSP w, hSP w₀, Real.dist_eq, abs_sub_lt_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Small-radius sub-mean-value inequality for the star function.** At each point of the strip
the sub-mean-value inequality holds for all sufficiently small circles; the threshold reflects the
level structure of the extremal set at the centre (Baernstein's translate bound applies below the
minimal component length/gap of the extremal level set). The inputs are: continuity of `u` on the
annulus, a structured extremal attaining set for the star value at the centre (`hattain`), and
subharmonicity of every fixed-arc integral of `u` on the log-polar band (`hsub`); for `u` harmonic
these are supplied by `exists_attaining_structured` and `arcIntegral_harmonicOn`. -/
theorem starPlane_subMeanValue_small {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {w₀ : ℂ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hucont : ContinuousOn u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u)
    (hattain : ∃ (τ δ : ℝ) (F : Set ℝ), 0 < δ ∧ MeasurableSet F ∧
      F ⊆ Set.Icc (τ + δ) (τ + 2 * π - δ) ∧
      volume F = ENNReal.ofReal (2 * w₀.im) ∧
      (∃ x₀, IsLeast F x₀ ∧ Set.Icc x₀ (x₀ + δ) ⊆ F) ∧
      (∫⁻ ψ in F, ENNReal.ofReal
          ((angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp w₀.re) ψ).toReal))
        = starFunction p u (Real.exp w₀.re) w₀.im)
    (hsub : ∀ E : Set ℝ, MeasurableSet E → Bornology.IsBounded E →
      SubharmonicOn (arcIntegral p u E) {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO})
    (hw₀ : w₀ ∈ logPolarStrip rI rO) :
    ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → Metric.closedBall w₀ ρ ⊆ logPolarStrip rI rO →
      starPlane p u w₀ ≤ Real.circleAverage (starPlane p u) w₀ ρ := by
  classical
  obtain ⟨hw₀re, hw₀im⟩ := hw₀
  -- Structured extremal attaining set at the centre: window slack `δ`, leftmost full interval.
  obtain ⟨τ, δ, F, hδ, hFmeas, hFwin, hFvol, ⟨x₀, hx₀least, hx₀Icc⟩, hFint⟩ := hattain
  have hδπ : δ ≤ π := by
    have h := hFwin hx₀least.1
    linarith [h.1, h.2]
  -- The structural threshold: any radius below `δ/2` keeps the translate bound valid.
  refine ⟨δ / 2, by positivity, fun ρ hρ hρδ hball => ?_⟩
  have harcnn : ∀ (E : Set ℝ) (w : ℂ), 0 ≤ arcIntegral p u E w := by
    intro E w
    rw [arcIntegral]
    exact integral_nonneg (fun φ => hu0 _)
  -- The de-rotated extremal arc-parameter set.
  set E₀ : Set ℝ := (fun ψ' : ℝ => ψ' + (-(w₀.im + π))) '' F with hE₀def
  have hE₀meas : MeasurableSet E₀ :=
    (measurableEmbedding_addRight (-(w₀.im + π))).measurableSet_image.2 hFmeas
  have hE₀bdd : Bornology.IsBounded E₀ := by
    refine (Metric.isBounded_Icc (τ + δ + (-(w₀.im + π)))
      (τ + 2 * π - δ + (-(w₀.im + π)))).subset ?_
    rw [hE₀def]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨by linarith [(hFwin hx).1], by linarith [(hFwin hx).2]⟩
  have hE₀vol : volume E₀ = ENNReal.ofReal (2 * w₀.im) := by
    rw [hE₀def, Set.image_add_right, measure_preimage_add_right, hFvol]
  have hEfinE₀ : volume E₀ ≠ ⊤ := by rw [hE₀vol]; exact ENNReal.ofReal_ne_top
  have himg₀ : (fun φ : ℝ => φ + (w₀.im + π)) '' E₀ = F := by
    rw [hE₀def, ← Set.image_comp]
    convert Set.image_id F using 1
    apply Set.image_congr'
    intro x
    simp only [Function.comp_apply, id_eq]
    ring
  -- A uniform bound for `u` on the compact log-radius shell spanned by the closed ball.
  have hmem₁ : w₀ - (ρ : ℂ) ∈ Metric.closedBall w₀ ρ := by
    have h : dist (w₀ - (ρ : ℂ)) w₀ = ρ := by
      rw [dist_eq_norm]
      have h2 : w₀ - (ρ : ℂ) - w₀ = -(ρ : ℂ) := by ring
      rw [h2, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact Metric.mem_closedBall.mpr (le_of_eq h)
  have hmem₂ : w₀ + (ρ : ℂ) ∈ Metric.closedBall w₀ ρ := by
    have h : dist (w₀ + (ρ : ℂ)) w₀ = ρ := by
      rw [dist_eq_norm]
      have h2 : w₀ + (ρ : ℂ) - w₀ = (ρ : ℂ) := by ring
      rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact Metric.mem_closedBall.mpr (le_of_eq h)
  obtain ⟨hs₁, -⟩ := hball hmem₁
  obtain ⟨hs₂, -⟩ := hball hmem₂
  have hlo : Real.log rI < w₀.re - ρ := by
    have h := hs₁.1
    rwa [Complex.sub_re, Complex.ofReal_re] at h
  have hhi : w₀.re + ρ < Real.log rO := by
    have h := hs₂.2
    rwa [Complex.add_re, Complex.ofReal_re] at h
  set K : Set ℂ :=
    {z : ℂ | Real.exp (w₀.re - ρ) ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ Real.exp (w₀.re + ρ)} with hKdef
  have hKsub : K ⊆ {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO} := by
    rw [hKdef]
    rintro z ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
        _ < Real.exp (w₀.re - ρ) := Real.exp_lt_exp.mpr hlo
        _ ≤ ‖z - p‖ := h1
    · calc ‖z - p‖ ≤ Real.exp (w₀.re + ρ) := h2
        _ < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hhi
        _ = rO := Real.exp_log (hrI.trans hrO)
  have hKclosed : IsClosed K := by
    rw [hKdef]
    have h1 : IsClosed {z : ℂ | Real.exp (w₀.re - ρ) ≤ ‖z - p‖} :=
      isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {z : ℂ | ‖z - p‖ ≤ Real.exp (w₀.re + ρ)} :=
      isClosed_le (by fun_prop) continuous_const
    simpa [Set.setOf_and] using h1.inter h2
  have hKcompact : IsCompact K := by
    refine (isCompact_closedBall p (Real.exp (w₀.re + ρ))).of_isClosed_subset hKclosed ?_
    rw [hKdef]
    rintro z ⟨-, h2⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact h2
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn (hucont.mono hKsub)
  have hKmem : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ z : ℂ, ‖z - p‖ = Real.exp w.re → z ∈ K := by
    intro w hw z hz
    have hre : |w.re - w₀.re| ≤ ρ := by
      have h1 : |(w - w₀).re| ≤ ‖w - w₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h1
      calc |w.re - w₀.re| ≤ ‖w - w₀‖ := h1
        _ = dist w w₀ := (dist_eq_norm w w₀).symm
        _ ≤ ρ := Metric.mem_closedBall.mp hw
    rw [abs_le] at hre
    rw [hKdef]
    exact ⟨by rw [hz]; exact Real.exp_le_exp.mpr (by linarith [hre.1]),
      by rw [hz]; exact Real.exp_le_exp.mpr (by linarith [hre.2])⟩
  have hMbd : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ φ : ℝ,
      u (p + Complex.exp (w + φ * Complex.I)) ≤ M := by
    intro w hw φ
    have hz := hKmem w hw _ (norm_arcPoint_sub p w φ)
    have h := hM _ hz
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h
  have hMcirc : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ φ : ℝ,
      u (p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I)) ≤ M := by
    intro w hw φ
    have hnorm : ‖p + (Real.exp w.re : ℂ) * Complex.exp (φ * Complex.I) - p‖
        = Real.exp w.re := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have him : ((φ : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
      rw [him, Real.exp_zero, mul_one, abs_of_pos (Real.exp_pos _)]
    have hz := hKmem w hw _ hnorm
    have h := hM _ hz
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h
  -- The rotated-frame profile at log-radius `ξ`, and the arc-integral/profile-integral chain.
  set gr : ℝ → ℝ → ℝ≥0∞ := fun ξ φ' => ENNReal.ofReal
    ((angularProfile p (fun z => ENNReal.ofReal (u z)) (Real.exp ξ) φ').toReal) with hgrdef
  have hintg : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ E : Set ℝ, volume E ≠ ⊤ →
      Integrable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I)))
        ((volume : Measure ℝ).restrict E) := by
    intro w hw E hEfin
    haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict E) := isFiniteMeasure_restrict.2 hEfin
    have hfibmeas : Measurable (fun φ : ℝ => u (p + Complex.exp (w + φ * Complex.I))) := by
      apply hum.comp
      fun_prop
    refine Integrable.of_bound hfibmeas.aestronglyMeasurable M ?_
    filter_upwards with φ
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 _)]
    exact hMbd w hw φ
  have hchain : ∀ w ∈ Metric.closedBall w₀ ρ, ∀ E : Set ℝ, MeasurableSet E → volume E ≠ ⊤ →
      ENNReal.ofReal (arcIntegral p u E w)
        = ∫⁻ ψ' in (fun φ : ℝ => φ + (w.im + π)) '' E, gr w.re ψ' := by
    intro w hw E hEmeas hEfin
    rw [arcIntegral, ofReal_integral_eq_lintegral_ofReal (hintg w hw E hEfin)
      (Filter.Eventually.of_forall (fun φ => hu0 _))]
    have hpt : ∀ φ : ℝ, ENNReal.ofReal (u (p + Complex.exp (w + φ * Complex.I)))
        = gr w.re (φ + (w.im + π)) := by
      intro φ
      simp only [hgrdef]
      simp only [angularProfile]
      rw [ENNReal.toReal_ofReal (hu0 _)]
      congr 2
      have hsplit : w + (φ : ℂ) * Complex.I
          = (w.re : ℂ) + ((φ + w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext
        · simp
        · simp; ring
      rw [hsplit, Complex.exp_add]
      congr 2
      · rw [← Complex.ofReal_exp]
      · push_cast; ring_nf
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hmp : MeasurePreserving (fun φ : ℝ => φ + (w.im + π)) volume volume :=
      measurePreserving_add_right volume (w.im + π)
    have hkey := hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight (w.im + π))
      (gr w.re) ((fun φ : ℝ => φ + (w.im + π)) '' E)
    rw [Set.preimage_image_eq _ (add_left_injective (w.im + π))] at hkey
    rw [hkey]
  -- Extremality at the centre: the de-rotated attaining set reproduces the star value.
  have hw₀ball : w₀ ∈ Metric.closedBall w₀ ρ := Metric.mem_closedBall_self hρ.le
  have hext : arcIntegral p u E₀ w₀ = starPlane p u w₀ := by
    have heq : ENNReal.ofReal (arcIntegral p u E₀ w₀)
        = starFunction p u (Real.exp w₀.re) w₀.im := by
      rw [hchain w₀ hw₀ball E₀ hE₀meas hEfinE₀, himg₀]
      simp only [hgrdef]
      exact hFint
    have harc0 : (0 : ℝ) ≤ arcIntegral p u E₀ w₀ := harcnn E₀ w₀
    rw [starPlane, ← heq, ENNReal.toReal_ofReal harc0]
  -- Coordinates of the circle points.
  have hcoord : ∀ x : ℝ, (circleMap w₀ ρ x).re = w₀.re + ρ * Real.cos x
      ∧ (circleMap w₀ ρ x).im = w₀.im + ρ * Real.sin x := by
    intro x
    constructor
    · simp [circleMap, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    · simp [circleMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  -- Sjögren's paired surgery: the two opposite circle points share their radius, and the
  -- translated extremal sets are cut and re-glued into competitors of the two target apertures.
  have hpair : ∀ ψ : ℝ, 0 ≤ Real.sin ψ →
      arcIntegral p u E₀ (circleMap w₀ ρ ψ) + arcIntegral p u E₀ (circleMap w₀ ρ (-ψ))
        ≤ starPlane p u (circleMap w₀ ρ ψ) + starPlane p u (circleMap w₀ ρ (-ψ)) := by
    intro ψ hsin
    set α : ℝ := ρ * Real.sin ψ with hαdef
    have hα0 : 0 ≤ α := mul_nonneg hρ.le hsin
    have hαρ : α ≤ ρ := by
      rw [hαdef]
      calc ρ * Real.sin ψ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one ψ) hρ.le
        _ = ρ := mul_one ρ
    have h2αδ : 2 * α ≤ δ := by linarith
    set wp : ℂ := circleMap w₀ ρ ψ with hwpdef
    set wm : ℂ := circleMap w₀ ρ (-ψ) with hwmdef
    have hwpball : wp ∈ Metric.closedBall w₀ ρ := circleMap_mem_closedBall w₀ hρ.le ψ
    have hwmball : wm ∈ Metric.closedBall w₀ ρ := circleMap_mem_closedBall w₀ hρ.le (-ψ)
    obtain ⟨-, hwpim⟩ := hball hwpball
    obtain ⟨-, hwmim⟩ := hball hwmball
    have hpre : wp.re = w₀.re + ρ * Real.cos ψ := (hcoord ψ).1
    have hpim : wp.im = w₀.im + α := by rw [hαdef]; exact (hcoord ψ).2
    have hmre : wm.re = w₀.re + ρ * Real.cos ψ := by
      have h := (hcoord (-ψ)).1
      rwa [Real.cos_neg] at h
    have hmim : wm.im = w₀.im - α := by
      have h := (hcoord (-ψ)).2
      rw [Real.sin_neg, mul_neg] at h
      rw [h, hαdef]; ring
    have hrere : wm.re = wp.re := by rw [hmre, hpre]
    have hwp0 : (0 : ℝ) ≤ wp.im := hwpim.1.le
    have hwpπ : wp.im ≤ π := hwpim.2.le
    have hwm0 : (0 : ℝ) ≤ wm.im := hwmim.1.le
    have hwmπ : wm.im ≤ π := hwmim.2.le
    have hαlt : α < w₀.im := by
      have h := hwmim.1
      rw [hmim] at h
      linarith
    -- The two translates of the attaining set.
    set Ep : Set ℝ := (fun x : ℝ => x + α) '' F with hEpdef
    set Em : Set ℝ := (fun x : ℝ => x - α) '' F with hEmdef
    have hEmeq : Em = (fun x : ℝ => x + (-α)) '' F := by
      rw [hEmdef]
      apply Set.image_congr'
      intro x
      ring
    have hEpmeas : MeasurableSet Ep := by
      rw [hEpdef]; exact (measurableEmbedding_addRight α).measurableSet_image.2 hFmeas
    have hEmmeas : MeasurableSet Em := by
      rw [hEmeq]; exact (measurableEmbedding_addRight (-α)).measurableSet_image.2 hFmeas
    have hvol_img : ∀ c : ℝ, volume ((fun x : ℝ => x + c) '' F) = volume F := by
      intro c; rw [Set.image_add_right, measure_preimage_add_right]
    have hEpvol : volume Ep = ENNReal.ofReal (2 * w₀.im) := by
      rw [hEpdef, hvol_img, hFvol]
    have hEmvol : volume Em = ENNReal.ofReal (2 * w₀.im) := by
      rw [hEmeq, hvol_img, hFvol]
    have hEpsub : Ep ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) := by
      rw [hEpdef]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by linarith [(hFwin hx).1], by linarith [(hFwin hx).2]⟩
    have hEmsub : Em ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) := by
      rw [hEmdef]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨by linarith [(hFwin hx).1], by linarith [(hFwin hx).2]⟩
    have hUsub : Ep ∪ Em ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) :=
      Set.union_subset hEpsub hEmsub
    -- Baernstein's translate bound at the leftmost full interval of `F`.
    have hIvol : volume (Ep ∩ Em) ≤ ENNReal.ofReal (2 * w₀.im - 2 * α) := by
      have h := volume_translate_inter_le hx₀least hx₀Icc h2αδ
      rw [← hEpdef, ← hEmdef, hFvol,
        ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 2 * α)] at h
      exact h
    have hIfin : volume (Ep ∩ Em) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hIvol
    obtain ⟨t, htnn, hteq⟩ : ∃ t : ℝ, 0 ≤ t ∧ volume (Ep ∩ Em) = ENNReal.ofReal t :=
      ⟨(volume (Ep ∩ Em)).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hIfin).symm⟩
    have htle : t ≤ 2 * w₀.im - 2 * α := by
      rw [hteq] at hIvol
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hIvol
    have hUfin : volume (Ep ∪ Em) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_union_le Ep Em)
      rw [hEpvol, hEmvol]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    obtain ⟨ut, hutnn, huteq⟩ : ∃ s : ℝ, 0 ≤ s ∧ volume (Ep ∪ Em) = ENNReal.ofReal s :=
      ⟨(volume (Ep ∪ Em)).toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hUfin).symm⟩
    have h2θnn : (0 : ℝ) ≤ 2 * w₀.im := by linarith [hw₀im.1]
    have hut4 : ut = 4 * w₀.im - t := by
      have h := measure_union_add_inter (μ := volume) Ep hEmmeas
      rw [hEpvol, hEmvol, hteq, huteq, ← ENNReal.ofReal_add hutnn htnn,
        ← ENNReal.ofReal_add h2θnn h2θnn] at h
      have h' := (ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)).mp h
      linarith
    -- Transfer a measurable piece of prescribed measure from the union to the intersection.
    have hUImeas : MeasurableSet ((Ep ∪ Em) \ (Ep ∩ Em)) :=
      (hEpmeas.union hEmmeas).diff (hEpmeas.inter hEmmeas)
    have hab : τ + δ - α ≤ τ + 2 * π - δ + α := by linarith
    have hm0 : (0 : ℝ) ≤ 2 * w₀.im - 2 * α - t := by linarith
    have hDvol : volume ((Ep ∪ Em) \ (Ep ∩ Em)) = ENNReal.ofReal (ut - t) := by
      rw [measure_diff (Set.inter_subset_left.trans Set.subset_union_left)
        (hEpmeas.inter hEmmeas).nullMeasurableSet hIfin, hteq, huteq,
        ← ENNReal.ofReal_sub _ htnn]
    have hmD : ENNReal.ofReal (2 * w₀.im - 2 * α - t)
        ≤ volume ((Ep ∪ Em) \ (Ep ∩ Em)) := by
      rw [hDvol]
      apply ENNReal.ofReal_le_ofReal
      rw [hut4]
      linarith
    obtain ⟨C, hCsub, hCmeas, hCvol⟩ := exists_measurableSet_subset_volume hab
      ((Ep ∪ Em) \ (Ep ∩ Em)) hUImeas (fun x hx => hUsub hx.1) hm0 hmD
    have hCdisjI : Disjoint (Ep ∩ Em) C :=
      Set.disjoint_of_subset_right hCsub Set.disjoint_sdiff_right
    have hCU : C ⊆ Ep ∪ Em := hCsub.trans Set.diff_subset
    have hCfin : volume C ≠ ⊤ := by rw [hCvol]; exact ENNReal.ofReal_ne_top
    -- The re-glued competitors of the two target apertures.
    have hAvol : volume ((Ep ∩ Em) ∪ C) = ENNReal.ofReal (2 * wm.im) := by
      rw [measure_union hCdisjI hCmeas, hteq, hCvol, ← ENNReal.ofReal_add htnn hm0]
      congr 1
      rw [hmim]
      ring
    have hBvol : volume ((Ep ∪ Em) \ C) = ENNReal.ofReal (2 * wp.im) := by
      rw [measure_diff hCU hCmeas.nullMeasurableSet hCfin, huteq, hCvol,
        ← ENNReal.ofReal_sub _ hm0]
      congr 1
      rw [hut4, hpim]
      ring
    have hIccA : (Ep ∩ Em) ∪ C ⊆ Set.Icc (τ + δ - α) (τ + 2 * π - δ + α) := by
      refine Set.union_subset (fun x hx => hUsub (Set.subset_union_left hx.1)) ?_
      exact fun x hx => hUsub (hCU hx)
    -- The lintegral surgery: cut-and-glue preserves the total profile mass.
    have hsplitEm : Em = (Ep ∩ Em) ∪ (Em \ Ep) := by
      rw [Set.inter_comm Ep Em]
      exact (Set.inter_union_diff Em Ep).symm
    have hsplitU : Ep ∪ Em = Ep ∪ (Em \ Ep) := Set.union_diff_self.symm
    have hUCsplit : Ep ∪ Em = C ∪ ((Ep ∪ Em) \ C) := (Set.union_diff_cancel hCU).symm
    have hEmPmeas : MeasurableSet (Em \ Ep) := hEmmeas.diff hEpmeas
    have hdisj1 : Disjoint (Ep ∩ Em) (Em \ Ep) :=
      Set.disjoint_of_subset_left Set.inter_subset_left Set.disjoint_sdiff_right
    have hdisj2 : Disjoint Ep (Em \ Ep) := Set.disjoint_sdiff_right
    have hEmint : (∫⁻ x in Em, gr wp.re x)
        = (∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x := by
      conv_lhs => rw [hsplitEm]
      exact lintegral_union hEmPmeas hdisj1
    have hUint : (∫⁻ x in Ep ∪ Em, gr wp.re x)
        = (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x := by
      conv_lhs => rw [hsplitU]
      exact lintegral_union hEmPmeas hdisj2
    have hAint : (∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x)
        = (∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in C, gr wp.re x :=
      lintegral_union hCmeas hCdisjI
    have hUCint : (∫⁻ x in Ep ∪ Em, gr wp.re x)
        = (∫⁻ x in C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
      conv_lhs => rw [hUCsplit]
      exact lintegral_union ((hEpmeas.union hEmmeas).diff hCmeas) Set.disjoint_sdiff_right
    have hsurg : (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em, gr wp.re x
        = (∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
      have hkeyU : (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x
          = (∫⁻ x in C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
        rw [← hUint, hUCint]
      rw [hEmint, hAint]
      calc (∫⁻ x in Ep, gr wp.re x)
          + ((∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x)
          = (∫⁻ x in Ep ∩ Em, gr wp.re x)
            + ((∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em \ Ep, gr wp.re x) := by ring
        _ = (∫⁻ x in Ep ∩ Em, gr wp.re x)
            + ((∫⁻ x in C, gr wp.re x) + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x) := by rw [hkeyU]
        _ = ((∫⁻ x in Ep ∩ Em, gr wp.re x) + ∫⁻ x in C, gr wp.re x)
            + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by ring
    -- The rotated frames of the arc integrals at the two circle points.
    have himgp : (fun φ : ℝ => φ + (wp.im + π)) '' E₀ = Ep := by
      rw [hE₀def, Set.image_image, hEpdef]
      apply Set.image_congr'
      intro x
      rw [hpim]
      ring
    have himgm : (fun φ : ℝ => φ + (wm.im + π)) '' E₀ = Em := by
      rw [hE₀def, Set.image_image, hEmdef]
      apply Set.image_congr'
      intro x
      rw [hmim]
      ring
    have hch_p : ENNReal.ofReal (arcIntegral p u E₀ wp) = ∫⁻ x in Ep, gr wp.re x := by
      rw [hchain wp hwpball E₀ hE₀meas hEfinE₀, himgp]
    have hch_m : ENNReal.ofReal (arcIntegral p u E₀ wm) = ∫⁻ x in Em, gr wp.re x := by
      rw [hchain wm hwmball E₀ hE₀meas hEfinE₀, himgm, hrere]
    -- De-rotate the competitors and dominate through the windowed star-function bound.
    set EA : Set ℝ := (fun x : ℝ => x + (-(wm.im + π))) '' ((Ep ∩ Em) ∪ C) with hEAdef
    set EB : Set ℝ := (fun x : ℝ => x + (-(wp.im + π))) '' ((Ep ∪ Em) \ C) with hEBdef
    have hEAmeas : MeasurableSet EA := by
      rw [hEAdef]
      exact (measurableEmbedding_addRight _).measurableSet_image.2
        ((hEpmeas.inter hEmmeas).union hCmeas)
    have hEBmeas : MeasurableSet EB := by
      rw [hEBdef]
      exact (measurableEmbedding_addRight _).measurableSet_image.2
        ((hEpmeas.union hEmmeas).diff hCmeas)
    have hEAvol : volume EA = ENNReal.ofReal (2 * wm.im) := by
      rw [hEAdef, Set.image_add_right, measure_preimage_add_right, hAvol]
    have hEBvol : volume EB = ENNReal.ofReal (2 * wp.im) := by
      rw [hEBdef, Set.image_add_right, measure_preimage_add_right, hBvol]
    have hEAfin : volume EA ≠ ⊤ := by rw [hEAvol]; exact ENNReal.ofReal_ne_top
    have hEBfin : volume EB ≠ ⊤ := by rw [hEBvol]; exact ENNReal.ofReal_ne_top
    have himgA : (fun φ : ℝ => φ + (wm.im + π)) '' EA = (Ep ∩ Em) ∪ C := by
      rw [hEAdef, ← Set.image_comp]
      convert Set.image_id _ using 1
      apply Set.image_congr'
      intro x
      simp only [Function.comp_apply, id_eq]
      ring
    have himgB : (fun φ : ℝ => φ + (wp.im + π)) '' EB = (Ep ∪ Em) \ C := by
      rw [hEBdef, ← Set.image_comp]
      convert Set.image_id _ using 1
      apply Set.image_congr'
      intro x
      simp only [Function.comp_apply, id_eq]
      ring
    have hdomA : ENNReal.ofReal (arcIntegral p u EA wm)
        ≤ starFunction p u (Real.exp wm.re) wm.im := by
      refine arcIntegral_le_starFunction_window (τ + δ - α) hu0 hum
        (hintg wm hwmball EA hEAfin) hEAmeas hwm0 hwmπ ?_ (le_of_eq hEAvol)
      rw [himgA]
      intro x hx
      have h := hIccA hx
      exact ⟨h.1, by linarith [h.2]⟩
    have hdomB : ENNReal.ofReal (arcIntegral p u EB wp)
        ≤ starFunction p u (Real.exp wp.re) wp.im := by
      refine arcIntegral_le_starFunction_window (τ + δ - α) hu0 hum
        (hintg wp hwpball EB hEBfin) hEBmeas hwp0 hwpπ ?_ (le_of_eq hEBvol)
      rw [himgB]
      intro x hx
      have h := hUsub hx.1
      exact ⟨h.1, by linarith [h.2]⟩
    have hchA : ENNReal.ofReal (arcIntegral p u EA wm)
        = ∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x := by
      rw [hchain wm hwmball EA hEAmeas hEAfin, himgA, hrere]
    have hchB : ENNReal.ofReal (arcIntegral p u EB wp)
        = ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := by
      rw [hchain wp hwpball EB hEBmeas hEBfin, himgB]
    -- Assemble the paired inequality in `ℝ≥0∞` and descend to the reals.
    have hsfinp : starFunction p u (Real.exp wp.re) wp.im < ⊤ :=
      starFunction_lt_top hwp0 hwpπ ⟨M, fun φ => hMcirc wp hwpball φ⟩
    have hsfinm : starFunction p u (Real.exp wm.re) wm.im < ⊤ :=
      starFunction_lt_top hwm0 hwmπ ⟨M, fun φ => hMcirc wm hwmball φ⟩
    have hmain : ENNReal.ofReal (arcIntegral p u E₀ wp) + ENNReal.ofReal (arcIntegral p u E₀ wm)
        ≤ starFunction p u (Real.exp wp.re) wp.im
          + starFunction p u (Real.exp wm.re) wm.im := by
      calc ENNReal.ofReal (arcIntegral p u E₀ wp) + ENNReal.ofReal (arcIntegral p u E₀ wm)
          = (∫⁻ x in Ep, gr wp.re x) + ∫⁻ x in Em, gr wp.re x := by rw [hch_p, hch_m]
        _ = (∫⁻ x in (Ep ∩ Em) ∪ C, gr wp.re x)
            + ∫⁻ x in (Ep ∪ Em) \ C, gr wp.re x := hsurg
        _ = ENNReal.ofReal (arcIntegral p u EA wm)
            + ENNReal.ofReal (arcIntegral p u EB wp) := by rw [hchA, hchB]
        _ ≤ starFunction p u (Real.exp wm.re) wm.im
            + starFunction p u (Real.exp wp.re) wp.im := add_le_add hdomA hdomB
        _ = starFunction p u (Real.exp wp.re) wp.im
            + starFunction p u (Real.exp wm.re) wm.im := add_comm _ _
    have hofsum : ENNReal.ofReal (arcIntegral p u E₀ wp + arcIntegral p u E₀ wm)
        = ENNReal.ofReal (arcIntegral p u E₀ wp) + ENNReal.ofReal (arcIntegral p u E₀ wm) :=
      ENNReal.ofReal_add (harcnn _ _) (harcnn _ _)
    have hsum_fin : starFunction p u (Real.exp wp.re) wp.im
        + starFunction p u (Real.exp wm.re) wm.im ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hsfinp.ne, hsfinm.ne⟩
    have hmain' : ENNReal.ofReal (arcIntegral p u E₀ wp + arcIntegral p u E₀ wm)
        ≤ starFunction p u (Real.exp wp.re) wp.im
          + starFunction p u (Real.exp wm.re) wm.im := by
      rw [hofsum]
      exact hmain
    have hfinal := ENNReal.toReal_mono hsum_fin hmain'
    rw [ENNReal.toReal_ofReal (add_nonneg (harcnn _ _) (harcnn _ _)),
      ENNReal.toReal_add hsfinp.ne hsfinm.ne] at hfinal
    simp only [starPlane]
    exact hfinal
  -- Fold the pairing over the whole circle: the reflected pairs cover every angle.
  have key : ∀ ψ : ℝ,
      arcIntegral p u E₀ (circleMap w₀ ρ ψ) + arcIntegral p u E₀ (circleMap w₀ ρ (-ψ))
        ≤ starPlane p u (circleMap w₀ ρ ψ) + starPlane p u (circleMap w₀ ρ (-ψ)) := by
    intro ψ
    rcases le_or_gt 0 (Real.sin ψ) with h | h
    · exact hpair ψ h
    · have h' := hpair (-ψ) (by rw [Real.sin_neg]; linarith)
      rw [neg_neg] at h'
      linarith
  -- Continuity of the two circle profiles.
  have hHsub : SubharmonicOn (arcIntegral p u E₀)
      {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := hsub E₀ hE₀meas hE₀bdd
  have hmapS : ∀ x : ℝ,
      circleMap w₀ ρ x ∈ {w : ℂ | Real.log rI < w.re ∧ w.re < Real.log rO} := by
    intro x
    obtain ⟨h1, -⟩ := hball (circleMap_mem_closedBall w₀ hρ.le x)
    exact ⟨h1.1, h1.2⟩
  have hmapStrip : ∀ x : ℝ, circleMap w₀ ρ x ∈ logPolarStrip rI rO :=
    fun x => hball (circleMap_mem_closedBall w₀ hρ.le x)
  have hΦcont : Continuous (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ x)) :=
    hHsub.1.comp_continuous (continuous_circleMap w₀ ρ) hmapS
  have hΨcont : Continuous (fun x : ℝ => starPlane p u (circleMap w₀ ρ x)) :=
    (starPlane_continuousOn hrI hrO hucont hu0 hum).comp_continuous
      (continuous_circleMap w₀ ρ) hmapStrip
  have hΦint : IntervalIntegrable (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ x))
      volume 0 (2 * π) := hΦcont.intervalIntegrable 0 (2 * π)
  have hΦnint : IntervalIntegrable (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ (-x)))
      volume 0 (2 * π) := (hΦcont.comp continuous_neg).intervalIntegrable 0 (2 * π)
  have hΨint : IntervalIntegrable (fun x : ℝ => starPlane p u (circleMap w₀ ρ x))
      volume 0 (2 * π) := hΨcont.intervalIntegrable 0 (2 * π)
  have hΨnint : IntervalIntegrable (fun x : ℝ => starPlane p u (circleMap w₀ ρ (-x)))
      volume 0 (2 * π) := (hΨcont.comp continuous_neg).intervalIntegrable 0 (2 * π)
  -- Reflection invariance of the two circle integrals.
  have hΦper : Function.Periodic (fun x : ℝ => arcIntegral p u E₀ (circleMap w₀ ρ x)) (2 * π) :=
    fun x => congrArg (arcIntegral p u E₀) (periodic_circleMap w₀ ρ x)
  have hΨper : Function.Periodic (fun x : ℝ => starPlane p u (circleMap w₀ ρ x)) (2 * π) :=
    fun x => congrArg (starPlane p u) (periodic_circleMap w₀ ρ x)
  have hreflΦ : (∫ x in (0 : ℝ)..(2 * π), arcIntegral p u E₀ (circleMap w₀ ρ (-x)))
      = ∫ x in (0 : ℝ)..(2 * π), arcIntegral p u E₀ (circleMap w₀ ρ x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => arcIntegral p u E₀ (circleMap w₀ ρ x)),
      neg_zero]
    have h := hΦper.intervalIntegral_add_eq (-(2 * π)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  have hreflΨ : (∫ x in (0 : ℝ)..(2 * π), starPlane p u (circleMap w₀ ρ (-x)))
      = ∫ x in (0 : ℝ)..(2 * π), starPlane p u (circleMap w₀ ρ x) := by
    rw [intervalIntegral.integral_comp_neg (fun x => starPlane p u (circleMap w₀ ρ x)),
      neg_zero]
    have h := hΨper.intervalIntegral_add_eq (-(2 * π)) 0
    rw [neg_add_cancel, zero_add] at h
    exact h
  -- Integrate the pointwise pairing over one period.
  have hintsum : (∫ x in (0 : ℝ)..(2 * π),
      (arcIntegral p u E₀ (circleMap w₀ ρ x) + arcIntegral p u E₀ (circleMap w₀ ρ (-x))))
      ≤ ∫ x in (0 : ℝ)..(2 * π),
      (starPlane p u (circleMap w₀ ρ x) + starPlane p u (circleMap w₀ ρ (-x))) :=
    intervalIntegral.integral_mono_on (by positivity) (hΦint.add hΦnint) (hΨint.add hΨnint)
      (fun x _ => key x)
  rw [intervalIntegral.integral_add hΦint hΦnint, intervalIntegral.integral_add hΨint hΨnint,
    hreflΦ, hreflΨ] at hintsum
  have hint_le : (∫ x in (0 : ℝ)..(2 * π), arcIntegral p u E₀ (circleMap w₀ ρ x))
      ≤ ∫ x in (0 : ℝ)..(2 * π), starPlane p u (circleMap w₀ ρ x) := by linarith
  -- Sub-mean-value property of the subharmonic competitor, and conclusion.
  have hMVP : arcIntegral p u E₀ w₀ ≤ Real.circleAverage (arcIntegral p u E₀) w₀ ρ := by
    refine hHsub.2 w₀ ⟨hw₀re.1, hw₀re.2⟩ ρ hρ ?_
    intro w hw
    obtain ⟨h1, -⟩ := hball hw
    exact ⟨h1.1, h1.2⟩
  have hcavg : Real.circleAverage (arcIntegral p u E₀) w₀ ρ
      ≤ Real.circleAverage (starPlane p u) w₀ ρ := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hint_le (by positivity)
  calc starPlane p u w₀ = arcIntegral p u E₀ w₀ := hext.symm
    _ ≤ Real.circleAverage (arcIntegral p u E₀) w₀ ρ := hMVP
    _ ≤ Real.circleAverage (starPlane p u) w₀ ρ := hcavg

/-- **Baernstein's theorem: the star function of a nonnegative harmonic function is subharmonic**
in log-polar coordinates on the open strip. Packages the continuity and the sub-mean-value
inequality into the `SubharmonicOn` predicate. -/
theorem starPlane_subharmonicOn {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u) :
    SubharmonicOn (starPlane p u) (logPolarStrip rI rO) := by
  have hopen : IsOpen (logPolarStrip rI rO) := by
    have heq : logPolarStrip rI rO
        = Complex.re ⁻¹' Set.Ioo (Real.log rI) (Real.log rO)
          ∩ Complex.im ⁻¹' Set.Ioo (0 : ℝ) Real.pi := rfl
    rw [heq]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  refine subharmonicOn_of_locally hopen (starPlane_continuousOn hrI hrO hu.continuousOn hu0 hum)
    fun c hc => starPlane_subMeanValue_small hrI hrO hu.continuousOn hu0 hum ?_ ?_ hc
  · have hrmem : Real.exp c.re ∈ Set.Ioo rI rO := by
      constructor
      · calc rI = Real.exp (Real.log rI) := (Real.exp_log hrI).symm
          _ < Real.exp c.re := Real.exp_lt_exp.mpr hc.1.1
      · calc Real.exp c.re < Real.exp (Real.log rO) := Real.exp_lt_exp.mpr hc.1.2
          _ = rO := Real.exp_log (hrI.trans hrO)
    exact exists_attaining_structured hrI hu hu0 hum hrmem hc.2
  · exact fun E hE hEbdd =>
      HarmonicOnNhd.subharmonicOn (arcIntegral_harmonicOn hrI hrO hu hE hEbdd)

/-- **Sub-mean-value inequality for the star function** (Baernstein). For `u` harmonic and
nonnegative on the annulus `{rI < ‖z - p‖ < rO}`, the log-polar star function `starPlane p u`
satisfies the sub-mean-value inequality at every point of the open strip: its value at the centre
is at most its circle average over any circle whose closed disk lies in the strip. Specializes the
subharmonicity of the star surface (`starPlane_subharmonicOn`) to a single centre and radius. -/
theorem starPlane_subMeanValue {p : ℂ} {u : ℂ → ℝ} {rI rO : ℝ} {w₀ : ℂ} {ρ : ℝ}
    (hrI : 0 < rI) (hrO : rI < rO)
    (hu : InnerProductSpace.HarmonicOnNhd u {z : ℂ | rI < ‖z - p‖ ∧ ‖z - p‖ < rO})
    (hu0 : ∀ z, 0 ≤ u z) (hum : Measurable u)
    (hw₀ : w₀ ∈ logPolarStrip rI rO) (hρ : 0 < ρ)
    (hball : Metric.closedBall w₀ ρ ⊆ logPolarStrip rI rO) :
    starPlane p u w₀ ≤ Real.circleAverage (starPlane p u) w₀ ρ :=
  (starPlane_subharmonicOn hrI hrO hu hu0 hum).2 w₀ hw₀ ρ hρ hball

end RiemannDynamics
