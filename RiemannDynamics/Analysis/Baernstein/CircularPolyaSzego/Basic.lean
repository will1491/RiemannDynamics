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
`Analysis/Potential/Subharmonic.lean`) is built to express. Crucially `u★` is assembled from
circle integrals of the *harmonic* (hence smooth) ring potential, so it avoids the missing
gradient regularity of the raw circular rearrangement `circSymm` that obstructs the
polarization and coarea routes.

## Main definitions

* `RiemannDynamics.starProfile T g θ` — the abstract cumulative integral of the symmetric-decreasing
  rearrangement `g ♯[T]` over the centered arc `[T/2 − θ, T/2 + θ]`.
* `RiemannDynamics.starFunction p u r θ` — the Baernstein star function of `u` at half-aperture `θ`
  on the circle of radius `r` about `p`, i.e. `starProfile (2π) (angularProfile p u r) θ`.
* `RiemannDynamics.logPolarStrip`, `RiemannDynamics.starPlane` — the log-polar strip
  `{log rI < Re w < log rO, 0 < Im w < π}` and the star function read on it.
* `RiemannDynamics.arcIntegral p u E w` — the integral of `u` over the arc-parameter set `E`,
  sampled on the circle of radius `exp (Re w)` at angles `Im w + φ`, so `Im w` rotates the arc.
* `RiemannDynamics.gradC` — the holomorphic (Wirtinger) gradient `∂₁u − i ∂₂u` of a real function
  on `ℂ`.

## Main results

* `RiemannDynamics.starProfile_zero`, `RiemannDynamics.starFunction_zero` — vanishing at zero
  aperture.
* `RiemannDynamics.monotone_starProfile`, `RiemannDynamics.monotone_starFunction` — monotonicity in
  the aperture: larger arcs give larger (or equal) cumulative integrals.
* `RiemannDynamics.starProfile_le_lintegral` — for `θ ≤ T/2`, the star profile is bounded by the
  whole-circle integral of the rearranged profile.
* `RiemannDynamics.starProfile_eq_lintegral_min` — the layer-cake identity
  `starProfile T g θ = ∫ min (2θ) (distribFun T g t)`, the route to the two results below.
* `RiemannDynamics.exists_measurableSet_subset_volume` — a measurable subset of prescribed measure
  inside a bounded interval.
* `RiemannDynamics.exists_attaining_set` — for `0 < T`, measurable `g` and `0 ≤ θ ≤ T/2`, a
  measurable `E ⊆ [0, T]` of measure `2θ` whose integral attains the star profile. `E` is a genuine
  measurable set, not an arc: an arc generally does not attain.
* `RiemannDynamics.starProfile_eq_iSup_setLIntegral` — Hardy–Littlewood: under the same hypotheses,
  the centered-arc value of the rearrangement is the supremum of `∫_E g` over measurable
  `E ⊆ [0, T]` of measure `2θ`, which is the classical Baernstein definition.
* `RiemannDynamics.starFunction_lt_top` — finiteness of the star function when the profile is
  bounded above, which is what lets `starPlane` take real values.
* `RiemannDynamics.arcIntegral_harmonicOn` — for `u` harmonic on the annulus and `E` measurable and
  bounded, the arc integral is harmonic in the log-polar variable, the fact that makes the star
  surface a supremum of harmonic functions.

The development continues in `Analysis/Baernstein/CircularPolyaSzego/ArcComparison.lean`
(the star plane dominates every arc integral) and
`Analysis/Baernstein/CircularPolyaSzego/Subharmonicity.lean`
(Baernstein's theorem).
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
theorem starFunction_lt_top {p : ℂ} {u : ℂ → ℝ} {r θ : ℝ} (_hθ0 : 0 ≤ θ) (_hθπ : θ ≤ π)
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

end RiemannDynamics
