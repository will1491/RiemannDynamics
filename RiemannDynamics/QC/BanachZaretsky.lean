/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.BoundedVariation

/-!
# The Banach–Zaretsky theorem (one-dimensional, monotone core)

This file builds the **one-dimensional Banach–Zaretsky theorem** as a reusable measure-theory
fact, from Mathlib's Stieltjes-measure, Radon–Nikodym, and Lebesgue-decomposition machinery.
It is the analytic engine that, on a horizontal slice of a quasiconformal-inverse homeomorphism,
turns "continuous + monotone + Luzin (N)" into the fundamental theorem of calculus
`f b - f a = ∫ₐᵇ f'`.

## Mathematical content

For a **continuous monotone** `f : ℝ → ℝ`, Mathlib associates the **Stieltjes measure**
`μ_f := hf.stieltjesFunction.measure` with `μ_f (Ioc a b) = f b - f a`. Continuity makes it
atomless, so `μ_f (Icc a b) = μ_f (Ioc a b) = f b - f a` as well, and Mathlib shows
(`Monotone.ae_hasDerivAt`) that `f` is a.e. differentiable with
`f' = (rnDeriv μ_f volume).toReal` almost everywhere.

The **Lebesgue decomposition** `μ_f = singularPart + volume.withDensity (rnDeriv μ_f volume)`
yields, on every `Ioc a b`,
`f b - f a = μ_f (Ioc a b) = (singularPart …) (Ioc a b) + ∫_{Ioc a b} f'`.
So the FTC `f b - f a = ∫ₐᵇ f'` holds **iff** the singular part vanishes, i.e. iff `μ_f ≪ volume`.

**Banach–Zaretsky**: condition (N) (`f` carries Lebesgue-null sets to Lebesgue-null sets) makes
`μ_f ≪ volume`. The bridge is the *image* estimate `μ_f A ≤ volume (f '' A)`, valid for a
continuous monotone `f` (the Stieltjes mass of a set is controlled by the Lebesgue measure of its
image — for an interval it is the equality `f b - f a = volume (f '' Icc a b)`). Then condition (N)
gives `volume A = 0 ⟹ volume (f '' A) = 0 ⟹ μ_f A = 0`, i.e. `μ_f ≪ volume`, killing the singular
part.

## Main results

* `StieltjesFunction.measure_Icc_of_continuous` — the atomless mass formula
  `μ_f (Icc a b) = ofReal (f b - f a)` for continuous monotone `f` (PROVEN).
* `stieltjesMeasure_image_Icc` — `μ_f (Icc a b) = volume (f '' Icc a b)` for continuous monotone
  `f` (PROVEN, from `ContinuousOn.image_Icc_of_monotoneOn`).
* `stieltjesMeasure_le_volume_image` — the image estimate `μ_f A ≤ volume (f '' A)` (the genuine
  Banach–Zaretsky inequality; a precisely-stated TRUE residual, see its docstring).
* `monotone_absolutelyContinuous_of_luzinN` — condition (N) ⟹ `μ_f ≪ volume` (PROVEN modulo the
  image estimate).
* `monotone_ftc_of_luzinN` — **the 1D Banach–Zaretsky FTC**: a continuous monotone `f` with
  condition (N) satisfies `f b - f a = ∫ₐᵇ f'` (PROVEN modulo the image estimate, via the Lebesgue
  decomposition + Lebesgue differentiation of the absolutely continuous part).
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace RiemannDynamics

/-! ## The Stieltjes function of a continuous monotone function is the function itself -/

/-- For a **continuous** monotone `f`, the associated Stieltjes function (the right limit
`rightLim f`) is `f` itself. -/
theorem Monotone.stieltjesFunction_apply_of_continuous {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) (x : ℝ) : hf.stieltjesFunction x = f x := by
  rw [Monotone.stieltjesFunction_eq]
  exact (hcont.continuousWithinAt).rightLim_eq

/-! ## Atomless mass of the Stieltjes measure of a continuous monotone function -/

/-- For a **continuous** monotone `f`, the Stieltjes measure of a singleton is zero (no atoms):
the left limit equals the value. -/
theorem StieltjesFunction.measure_singleton_of_continuous {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) (a : ℝ) :
    hf.stieltjesFunction.measure {a} = 0 := by
  have hleft : leftLim hf.stieltjesFunction a = hf.stieltjesFunction a := by
    -- `hf.stieltjesFunction` is continuous (it equals `f`), hence its left limit is its value.
    apply ContinuousWithinAt.leftLim_eq
    have heq : (hf.stieltjesFunction : ℝ → ℝ) = f :=
      funext (Monotone.stieltjesFunction_apply_of_continuous hf hcont)
    rw [heq]; exact hcont.continuousWithinAt
  rw [StieltjesFunction.measure_singleton, hleft, sub_self, ENNReal.ofReal_zero]

/-- For a **continuous** monotone `f`, the Stieltjes measure gives `Icc a b` the mass `f b - f a`
(the atomless case; the same mass as `Ioc`). -/
theorem StieltjesFunction.measure_Icc_of_continuous {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) (a b : ℝ) :
    hf.stieltjesFunction.measure (Icc a b) = ENNReal.ofReal (f b - f a) := by
  rw [StieltjesFunction.measure_Icc]
  have hvalb : (hf.stieltjesFunction : ℝ → ℝ) b = f b :=
    Monotone.stieltjesFunction_apply_of_continuous hf hcont b
  have hleft : leftLim hf.stieltjesFunction a = f a := by
    have heq : (hf.stieltjesFunction : ℝ → ℝ) = f :=
      funext (Monotone.stieltjesFunction_apply_of_continuous hf hcont)
    rw [heq]; exact (hcont.continuousWithinAt).leftLim_eq
  rw [hleft, hvalb]

/-- For a **continuous** monotone `f`, the Stieltjes measure is a locally finite (indeed, on
bounded sets, finite) measure. The mass of `Icc a b` is `f b - f a < ∞`. -/
instance StieltjesFunction.measure_isLocallyFinite {f : ℝ → ℝ} (hf : Monotone f) :
    IsLocallyFiniteMeasure hf.stieltjesFunction.measure :=
  inferInstanceAs (IsLocallyFiniteMeasure (hf.stieltjesFunction).measure)

/-! ## The Stieltjes mass of an interval equals the Lebesgue measure of its image -/

/-- For a **continuous** monotone `f`, the Stieltjes mass of `Icc a b` is the Lebesgue measure of
its image: `μ_f (Icc a b) = volume (f '' Icc a b)`. (The image of `Icc a b` under a continuous
monotone map is `Icc (f a) (f b)`, of Lebesgue measure `f b - f a`.) -/
theorem stieltjesMeasure_image_Icc {f : ℝ → ℝ} (hf : Monotone f) (hcont : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    hf.stieltjesFunction.measure (Icc a b) = volume (f '' Icc a b) := by
  rw [StieltjesFunction.measure_Icc_of_continuous hf hcont]
  have himg : f '' Icc a b = Icc (f a) (f b) :=
    (hcont.continuousOn).image_Icc_of_monotoneOn hab (hf.monotoneOn _)
  rw [himg, Real.volume_Icc]

/-! ## The Banach–Zaretsky image estimate (now proven) -/

/-- For a **continuous** monotone `f`, the Stieltjes mass of `Ioo a b` equals `ofReal (f b - f a)`
(the atomless case: the left limit at `b` equals `f b`). -/
theorem StieltjesFunction.measure_Ioo_of_continuous {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) (a b : ℝ) :
    hf.stieltjesFunction.measure (Ioo a b) = ENNReal.ofReal (f b - f a) := by
  rw [StieltjesFunction.measure_Ioo]
  have hvala : (hf.stieltjesFunction : ℝ → ℝ) a = f a :=
    Monotone.stieltjesFunction_apply_of_continuous hf hcont a
  have hleftb : leftLim hf.stieltjesFunction b = f b := by
    have heq : (hf.stieltjesFunction : ℝ → ℝ) = f :=
      funext (Monotone.stieltjesFunction_apply_of_continuous hf hcont)
    rw [heq]; exact (hcont.continuousWithinAt).leftLim_eq
  rw [hleftb, hvala]

/-- For a **continuous** monotone `f`, the Lebesgue measure of the image of `Ioo a b` is
`ofReal (f b - f a)`. (The image `f '' Ioo a b` is sandwiched between `Ioo (f a) (f b)` and
`Icc (f a) (f b)`, which differ by the two null endpoints.) -/
theorem volume_image_Ioo_of_continuous {f : ℝ → ℝ} (hf : Monotone f) (hcont : Continuous f)
    (a b : ℝ) :
    volume (f '' Set.Ioo a b) = ENNReal.ofReal (f b - f a) := by
  rcases le_or_gt b a with hba | hab
  · -- `Ioo a b = ∅`, and `f b - f a ≤ 0`.
    rw [Set.Ioo_eq_empty (by simpa using hba), Set.image_empty, measure_empty]
    exact (ENNReal.ofReal_eq_zero.mpr (by linarith [hf hba])).symm
  · -- Upper bound: `f '' Ioo a b ⊆ Icc (f a) (f b)`.
    have hub : f '' Set.Ioo a b ⊆ Set.Icc (f a) (f b) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hf hx.1.le, hf hx.2.le⟩
    -- Lower bound: `Ioo (f a) (f b) ⊆ f '' Icc a b = Icc (f a) (f b)`; combine with continuity to
    -- get `Ioo (f a) (f b) ⊆ f '' Ioo a b`. We use the intermediate value theorem on `Ioo`.
    have hlb : Set.Ioo (f a) (f b) ⊆ f '' Set.Ioo a b := by
      intro v hv
      -- `f` continuous on `Icc a b`, `f a < v < f b`, IVT gives `c ∈ Ioo a b` with `f c = v`.
      have hcontOn : ContinuousOn f (Set.Icc a b) := hcont.continuousOn
      have : Set.Ioo (f a) (f b) ⊆ f '' Set.Ioo a b :=
        intermediate_value_Ioo hab.le hcontOn
      exact this hv
    -- Sandwiched: `volume (Ioo (f a)(f b)) ≤ volume (f '' Ioo a b) ≤ volume (Icc (f a)(f b))`,
    -- both ends `ofReal (f b - f a)`.
    refine le_antisymm ?_ ?_
    · calc volume (f '' Set.Ioo a b) ≤ volume (Set.Icc (f a) (f b)) := measure_mono hub
        _ = ENNReal.ofReal (f b - f a) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (f b - f a) = volume (Set.Ioo (f a) (f b)) := by rw [Real.volume_Ioo]
        _ ≤ volume (f '' Set.Ioo a b) := measure_mono hlb

/-- The continuous image of an ordConnected set is ordConnected (hence measurable). -/
theorem ordConnected_image_of_continuous {f : ℝ → ℝ} (hcont : Continuous f) {s : Set ℝ}
    (hs : Set.OrdConnected s) : Set.OrdConnected (f '' s) :=
  ((hs.isPreconnected).image f hcont.continuousOn).ordConnected

/-- **Per-component equality.** For continuous monotone `f` and a **bounded** open ordConnected set
`s`, `μ_f s = volume (f '' s)`: both equal `ofReal (f (sSup s) - f (sInf s))`, since
`Ioo (sInf s) (sSup s) ⊆ s ⊆ Icc (sInf s) (sSup s)` and the endpoints are null. -/
theorem stieltjesMeasure_image_eq_of_bdd_isOpen_ordConnected {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) {s : Set ℝ} (hsord : Set.OrdConnected s)
    (hbdd : Bornology.IsBounded s) :
    hf.stieltjesFunction.measure s = volume (f '' s) := by
  set μ := hf.stieltjesFunction.measure with hμ
  rcases s.eq_empty_or_nonempty with hse | hsne
  · simp [hse]
  -- Bounded ⟹ BddBelow and BddAbove.
  have hbb : BddBelow s := hbdd.bddBelow
  have hba : BddAbove s := hbdd.bddAbove
  set a := sInf s with ha
  set b := sSup s with hb
  have hconn : IsConnected s := ⟨hsne, hsord.isPreconnected⟩
  -- `Ioo a b ⊆ s ⊆ Icc a b`.
  have hIoo : Set.Ioo a b ⊆ s := hconn.Ioo_csInf_csSup_subset hbb hba
  have hIcc : s ⊆ Set.Icc a b := subset_Icc_csInf_csSup hbb hba
  -- `a ≤ b`.
  have hab : a ≤ b := Real.sInf_le_sSup s hbb hba
  -- μ side squeeze: both `Ioo` and `Icc` get `ofReal (f b - f a)`.
  have hμIoo : μ (Set.Ioo a b) = ENNReal.ofReal (f b - f a) :=
    StieltjesFunction.measure_Ioo_of_continuous hf hcont a b
  have hμIcc : μ (Set.Icc a b) = ENNReal.ofReal (f b - f a) :=
    StieltjesFunction.measure_Icc_of_continuous hf hcont a b
  have hμs : μ s = ENNReal.ofReal (f b - f a) :=
    le_antisymm (hμIcc ▸ measure_mono hIcc) (hμIoo ▸ measure_mono hIoo)
  -- vol side squeeze: both `f '' Ioo` and `f '' Icc` get `ofReal (f b - f a)`.
  have hvIoo : volume (f '' Set.Ioo a b) = ENNReal.ofReal (f b - f a) :=
    volume_image_Ioo_of_continuous hf hcont a b
  have hvIcc : volume (f '' Set.Icc a b) = ENNReal.ofReal (f b - f a) := by
    rw [← stieltjesMeasure_image_Icc hf hcont hab,
      StieltjesFunction.measure_Icc_of_continuous hf hcont]
  have hvs : volume (f '' s) = ENNReal.ofReal (f b - f a) :=
    le_antisymm (hvIcc ▸ measure_mono (Set.image_mono hIcc))
      (hvIoo ▸ measure_mono (Set.image_mono hIoo))
  rw [hμs, hvs]

/-- **Per-component equality (general).** For continuous monotone `f` and ANY open ordConnected set
`s`, `μ_f s = volume (f '' s)`. Reduces to the bounded case by exhausting `s` with the increasing
bounded open ordConnected sets `s ∩ Ioo (-n) n` and monotone convergence on both sides. -/
theorem stieltjesMeasure_image_eq_of_isOpen_ordConnected {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) {s : Set ℝ} (hsord : Set.OrdConnected s) :
    hf.stieltjesFunction.measure s = volume (f '' s) := by
  set μ := hf.stieltjesFunction.measure with hμ
  -- Exhaustion: `s = ⋃ₙ (s ∩ Ioo (-n) n)`, increasing, each bounded open ordConnected.
  set t : ℕ → Set ℝ := fun n => s ∩ Set.Ioo (-(n : ℝ)) n with ht
  have htord : ∀ n, Set.OrdConnected (t n) := fun n => hsord.inter Set.ordConnected_Ioo
  have htbdd : ∀ n, Bornology.IsBounded (t n) := fun n =>
    (Metric.isBounded_Ioo _ _).subset Set.inter_subset_right
  have htmono : Monotone t := by
    intro m n hmn
    apply Set.inter_subset_inter_right
    apply Set.Ioo_subset_Ioo <;> [exact neg_le_neg (by exact_mod_cast hmn);
      exact_mod_cast hmn]
  have htunion : ⋃ n, t n = s := by
    rw [ht]; rw [← Set.inter_iUnion]
    have : (⋃ n : ℕ, Set.Ioo (-(n : ℝ)) n) = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro x
      obtain ⟨n, hn⟩ := exists_nat_gt (|x|)
      rw [Set.mem_iUnion]; exact ⟨n, by rw [abs_lt] at hn; exact ⟨by linarith [hn.1], hn.2⟩⟩
    rw [this, Set.inter_univ]
  -- Per `n` equality.
  have hn_eq : ∀ n, μ (t n) = volume (f '' t n) := fun n =>
    stieltjesMeasure_image_eq_of_bdd_isOpen_ordConnected hf hcont (htord n) (htbdd n)
  -- μ continuity from below.
  have hμlim : Filter.Tendsto (fun n => μ (t n)) Filter.atTop (nhds (μ s)) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) htmono
    rwa [htunion] at this
  -- vol continuity from below: `f '' t` is monotone with union `f '' s`.
  have himg_mono : Monotone (fun n => f '' t n) := fun m n hmn => Set.image_mono (htmono hmn)
  have himg_union : ⋃ n, f '' t n = f '' s := by rw [← Set.image_iUnion, htunion]
  have hvlim : Filter.Tendsto (fun n => volume (f '' t n)) Filter.atTop
      (nhds (volume (f '' s))) := by
    have := tendsto_measure_iUnion_atTop (μ := volume) himg_mono
    rwa [himg_union] at this
  -- The two limits agree termwise, so the limits agree.
  have : Filter.Tendsto (fun n => μ (t n)) Filter.atTop (nhds (volume (f '' s))) := by
    simp_rw [hn_eq]; exact hvlim
  exact tendsto_nhds_unique hμlim this

/-- **The open-set Banach–Zaretsky equality.** For a **continuous monotone** `f` and an open set
`U`, the Stieltjes mass equals the Lebesgue measure of the image: `μ_f U = volume (f '' U)`.

Proof: decompose `U` into its (countably many, pairwise-disjoint, open) connected components, which
are open intervals. The Stieltjes mass is additive over them (`measure_iUnion`), each component `s`
contributing `μ_f s = volume (f '' s)` (`stieltjesMeasure_image_eq_of_isOpen_ordConnected`). The
images `f '' (component)` are pairwise a.e.-disjoint (monotone `f`, disjoint intervals ⟹ images meet
in at most one point), so their volumes sum to `volume (f '' U)` (`measure_iUnion₀`). -/
theorem stieltjesMeasure_eq_volume_image_of_isOpen {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) {U : Set ℝ} (hU : IsOpen U) :
    hf.stieltjesFunction.measure U = volume (f '' U) := by
  classical
  set μ := hf.stieltjesFunction.measure with hμ
  -- The connected components of `U`, indexed by representatives in `U`.
  -- Use `connectedComponentIn U x` for `x ∈ U`. These are open (ℝ locally connected) intervals.
  set C : ℝ → Set ℝ := fun x => connectedComponentIn U x with hC
  -- The set of (distinct) components.
  set 𝒞 : Set (Set ℝ) := (fun x => C x) '' U with h𝒞
  have hCsub : ∀ x ∈ U, C x ⊆ U := fun x _ => connectedComponentIn_subset U x
  have hCmem : ∀ x ∈ U, x ∈ C x := fun x hx => mem_connectedComponentIn hx
  have hCopen : ∀ x ∈ U, IsOpen (C x) := fun x _ => hU.connectedComponentIn
  have hCord : ∀ x : ℝ, Set.OrdConnected (C x) :=
    fun x => (isPreconnected_connectedComponentIn).ordConnected
  -- Each component is measurable.
  have hCmeas : ∀ x : ℝ, MeasurableSet (C x) := fun x => (hCord x).measurableSet
  -- `𝒞` is countable: the components are pairwise disjoint nonempty open sets in separable ℝ.
  have hPD : 𝒞.PairwiseDisjoint id := by
    rintro s ⟨x, hxU, rfl⟩ t ⟨y, hyU, rfl⟩ hst
    -- distinct components are disjoint.
    simp only [id, hC]
    by_contra hnd
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨z, hzx, hzy⟩ := hnd
    apply hst
    simp only [hC]
    rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]
  have h𝒞count : 𝒞.Countable := by
    refine Set.PairwiseDisjoint.countable_of_isOpen hPD ?_ ?_
    · rintro s ⟨x, hxU, rfl⟩; exact hCopen x hxU
    · rintro s ⟨x, hxU, rfl⟩; exact ⟨x, hCmem x hxU⟩
  -- `U = ⋃₀ 𝒞`.
  have hUunion : U = ⋃₀ 𝒞 := by
    apply Set.Subset.antisymm
    · intro x hx; exact ⟨C x, ⟨x, hx, rfl⟩, hCmem x hx⟩
    · rintro x ⟨s, ⟨y, hyU, rfl⟩, hxs⟩; exact hCsub y hyU hxs
  -- Index by the countable subtype `↥𝒞`.
  haveI : Countable (↥𝒞) := h𝒞count.to_subtype
  -- Each member of `𝒞` is an open ordConnected set (an interval): measurable.
  have h𝒞meas : ∀ s : 𝒞, MeasurableSet (s : Set ℝ) := by
    rintro ⟨s, ⟨x, hxU, rfl⟩⟩; exact hCmeas x
  have h𝒞ord : ∀ s : 𝒞, Set.OrdConnected (s : Set ℝ) := by
    rintro ⟨s, ⟨x, hxU, rfl⟩⟩; exact hCord x
  -- Pairwise disjoint as a family on the subtype.
  have h𝒞disj : Pairwise (Disjoint on fun s : 𝒞 => (s : Set ℝ)) := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hne
    have : s ≠ t := fun h => hne (Subtype.ext h)
    exact hPD hs ht this
  -- `⋃ s : 𝒞, ↑s = U`.
  have hiUnion : (⋃ s : 𝒞, (s : Set ℝ)) = U := by
    rw [← Set.sUnion_eq_iUnion, ← hUunion]
  -- μ side: additive over the components.
  have hμU : μ U = ∑' s : 𝒞, μ (s : Set ℝ) := by
    rw [← hiUnion, measure_iUnion h𝒞disj h𝒞meas]
  -- Each component image volume = μ-mass; the images are a.e.-disjoint, summing to vol(f''U).
  -- Per-component equality `μ s = volume (f '' s)` (each component is open ordConnected).
  have hμ_eq_vol : ∀ s : 𝒞, μ (s : Set ℝ) = volume (f '' (s : Set ℝ)) := by
    rintro ⟨s, ⟨x, hxU, rfl⟩⟩
    exact stieltjesMeasure_image_eq_of_isOpen_ordConnected hf hcont (hCord x)
  -- Image null-measurability: `f '' (ordConnected)` is ordConnected, hence measurable.
  have himg_nullmeas : ∀ s : 𝒞, NullMeasurableSet (f '' (s : Set ℝ)) volume := by
    rintro ⟨s, ⟨x, hxU, rfl⟩⟩
    exact ((ordConnected_image_of_continuous hcont (hCord x)).measurableSet).nullMeasurableSet
  -- Image a.e.-disjointness: for distinct (disjoint) components `s, t`, the images `f '' s`,
  -- `f '' t` meet in at most one point (`f` monotone, `s` left of or right of `t`), hence null.
  have himg_disj : Pairwise (AEDisjoint volume on fun s : 𝒞 => f '' (s : Set ℝ)) := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hne
    have hst : s ≠ t := fun h => hne (Subtype.ext h)
    have hdisj : Disjoint s t := hPD hs ht hst
    obtain ⟨xs, hxsU, rfl⟩ := hs
    obtain ⟨xt, hxtU, rfl⟩ := ht
    -- The two components are ordConnected and disjoint, so one lies entirely left of the other.
    have horder : (∀ u ∈ C xs, ∀ v ∈ C xt, u ≤ v) ∨ (∀ u ∈ C xs, ∀ v ∈ C xt, v ≤ u) := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      simp only [not_forall, not_le] at h1 h2
      obtain ⟨u₁, hu₁, v₁, hv₁, hlt₁⟩ := h1
      obtain ⟨u₂, hu₂, v₂, hv₂, hlt₂⟩ := h2
      -- `v₁ < u₁` and `u₂ < v₂`. A point between lands in both (ordConnected), contradiction.
      rcases le_total u₂ v₁ with h | h
      · -- `v₁` between `u₂ ∈ C xs` and `u₁ ∈ C xs`, so `v₁ ∈ C xs`; but `v₁ ∈ C xt` (disjoint).
        have hv₁s : v₁ ∈ C xs := (hCord xs).out hu₂ hu₁ ⟨h, le_of_lt hlt₁⟩
        exact (Set.disjoint_left.mp hdisj) hv₁s hv₁
      · -- `u₂` between `v₁ ∈ C xt` and `v₂ ∈ C xt`, so `u₂ ∈ C xt`; but `u₂ ∈ C xs` (disjoint).
        have hu₂t : u₂ ∈ C xt := (hCord xt).out hv₁ hv₂ ⟨h, le_of_lt hlt₂⟩
        exact (Set.disjoint_left.mp hdisj) hu₂ hu₂t
    -- In either case `f '' C xs ∩ f '' C xt` is a subsingleton, hence null.
    have hsub : (f '' C xs ∩ f '' C xt).Subsingleton := by
      rintro w ⟨⟨u, hu, rfl⟩, ⟨v, hv, hwv⟩⟩ w' ⟨⟨u', hu', rfl⟩, ⟨v', hv', hwv'⟩⟩
      rcases horder with hle | hle
      · -- goal `f u = f u'`; `f u ≤ f v' = f u'` and `f u' ≤ f v = f u`.
        have h1 : f u ≤ f v' := hf (hle u hu v' hv')
        have h2 : f u' ≤ f v := hf (hle u' hu' v hv)
        rw [hwv'] at h1; rw [hwv] at h2
        exact le_antisymm h1 h2
      · have h1 : f v' ≤ f u := hf (hle u hu v' hv')
        have h2 : f v ≤ f u' := hf (hle u' hu' v hv)
        rw [hwv'] at h1; rw [hwv] at h2
        exact le_antisymm h2 h1
    -- `AEDisjoint volume (f '' C xs) (f '' C xt)` is `volume (… ∩ …) = 0`.
    exact hsub.measure_zero volume
  -- vol side: a.e.-additive over the component images.
  have hvolU : volume (f '' U) = ∑' s : 𝒞, volume (f '' (s : Set ℝ)) := by
    rw [← hiUnion, Set.image_iUnion, measure_iUnion₀ himg_disj himg_nullmeas]
  rw [hμU, hvolU]
  exact tsum_congr hμ_eq_vol

/-- **The Banach–Zaretsky image estimate.** For a **continuous monotone** `f`, the Stieltjes mass
of *any* set `A` is bounded by the Lebesgue measure of its image: `μ_f A ≤ volume (f '' A)`.

Proof (the classical descent): by outer regularity of Lebesgue on the target, `volume (f '' A)` is
the infimum over open `V ⊇ f '' A` of `volume V`. For each such `V`, the preimage `f ⁻¹' V` is open
(continuity), contains `A`, and `f '' (f ⁻¹' V) ⊆ V`; the **open-set inequality**
`stieltjesMeasure_le_volume_image_of_isOpen` gives
`μ_f A ≤ μ_f (f ⁻¹' V) ≤ volume (f '' (f ⁻¹' V)) ≤ volume V`. Taking the infimum yields the claim.

This is the genuine Banach–Zaretsky inequality (Hencl–Koskela, *Lectures on mappings of finite
distortion*, Lemma A.32; Saks, *Theory of the Integral*, IV §6); together with condition (N) it
makes `μ_f ≪ volume` (`monotone_absolutelyContinuous_of_luzinN`). -/
theorem stieltjesMeasure_le_volume_image {f : ℝ → ℝ} (hf : Monotone f) (hcont : Continuous f)
    (A : Set ℝ) :
    hf.stieltjesFunction.measure A ≤ volume (f '' A) := by
  -- Outer regularity of Lebesgue on the target reduces to open supersets of `f '' A`.
  rw [Set.measure_eq_iInf_isOpen (f '' A) volume]
  refine le_iInf₂ fun V hVsub => le_iInf fun hVopen => ?_
  -- `U := f ⁻¹' V` is open and contains `A`.
  have hUopen : IsOpen (f ⁻¹' V) := hVopen.preimage hcont
  have hAU : A ⊆ f ⁻¹' V := by
    intro x hx; exact hVsub ⟨x, hx, rfl⟩
  calc hf.stieltjesFunction.measure A
      ≤ hf.stieltjesFunction.measure (f ⁻¹' V) := measure_mono hAU
    _ = volume (f '' (f ⁻¹' V)) := stieltjesMeasure_eq_volume_image_of_isOpen hf hcont hUopen
    _ ≤ volume V := measure_mono (Set.image_preimage_subset f V)

/-- **The reverse Banach–Zaretsky image estimate.** For a **continuous monotone** `f`, the Lebesgue
measure of the image of *any* set `A` is bounded by the Stieltjes mass: `volume (f '' A) ≤ μ_f A`.

Proof (dual descent): by outer regularity of the (locally finite Borel) Stieltjes measure `μ_f` on
the source, `μ_f A` is the infimum over open `U ⊇ A` of `μ_f U`. For each such `U`, the
**open-set equality** `stieltjesMeasure_eq_volume_image_of_isOpen` gives
`volume (f '' A) ≤ volume (f '' U) = μ_f U`. Taking the infimum yields the claim.

Together with `μ_f ≪ volume` (which holds for an *absolutely continuous* monotone `f`, e.g. a
primitive) this gives the **converse** Banach–Zaretsky direction: condition (N) for `f`. -/
theorem volume_image_le_stieltjesMeasure {f : ℝ → ℝ} (hf : Monotone f) (hcont : Continuous f)
    (A : Set ℝ) :
    volume (f '' A) ≤ hf.stieltjesFunction.measure A := by
  -- Outer regularity of the Stieltjes measure on the source reduces to open supersets of `A`.
  rw [Set.measure_eq_iInf_isOpen A hf.stieltjesFunction.measure]
  refine le_iInf₂ fun U hAU => le_iInf fun hUopen => ?_
  calc volume (f '' A)
      ≤ volume (f '' U) := measure_mono (Set.image_mono hAU)
    _ = hf.stieltjesFunction.measure U :=
        (stieltjesMeasure_eq_volume_image_of_isOpen hf hcont hUopen).symm

/-! ## Condition (N) ⟹ absolute continuity of the Stieltjes measure -/

/-- **Banach–Zaretsky: condition (N) makes the Stieltjes measure absolutely continuous.** For a
continuous monotone `f` carrying Lebesgue-null sets to Lebesgue-null sets, the Stieltjes measure
`μ_f` is absolutely continuous w.r.t. Lebesgue.

Direct from the image estimate `stieltjesMeasure_le_volume_image`: if `volume A = 0`, condition (N)
gives `volume (f '' A) = 0`, so `μ_f A ≤ volume (f '' A) = 0`. -/
theorem monotone_absolutelyContinuous_of_luzinN {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f) (hN : ∀ S : Set ℝ, volume S = 0 → volume (f '' S) = 0) :
    hf.stieltjesFunction.measure ≪ volume := by
  intro A hA
  have himg : volume (f '' A) = 0 := hN A hA
  exact le_antisymm (le_trans (stieltjesMeasure_le_volume_image hf hcont A) (le_of_eq himg))
    (zero_le _)

/-! ## The converse direction: a monotone primitive satisfies condition (N) -/

/-- **Condition (N) for a monotone primitive (the converse Banach–Zaretsky direction).** For a
nonnegative function `φ` that is interval integrable on every interval, the primitive
`p x = c + ∫₀ˣ φ` is **continuous monotone** and satisfies **Lusin's condition (N)**: it carries
Lebesgue-null sets to Lebesgue-null sets.

This is the genuine converse of `monotone_absolutelyContinuous_of_luzinN` (which produces
`μ_p ≪ volume` *from* condition (N)); here condition (N) is *produced* from absolute continuity.
The mechanism: the Stieltjes measure of the (absolutely continuous) primitive is exactly the density
measure, `μ_p = volume.withDensity (ofReal φ)` — both are locally finite and agree on every
`Ioc a b` (the FTC `p b - p a = ∫ₐᵇ φ`, with `ofReal (∫ₐᵇ φ) = ∫_{Ioc} ofReal φ`
for `φ ≥ 0`), so they coincide by `Measure.ext_of_Ioc`. As a density measure `μ_p ≪ volume`
(`withDensity_absolutelyContinuous`); combined with the reverse image estimate
`volume (p '' S) ≤ μ_p S` (`volume_image_le_stieltjesMeasure`), a null `S` has null image. -/
theorem luzinN_of_primitive {φ : ℝ → ℝ} (hφnn : 0 ≤ φ)
    (hφLI : ∀ a b, IntervalIntegrable φ volume a b) (c : ℝ)
    {S : Set ℝ} (hS : volume S = 0) :
    volume ((fun x => c + ∫ t in (0 : ℝ)..x, φ t) '' S) = 0 := by
  set p : ℝ → ℝ := fun x => c + ∫ t in (0 : ℝ)..x, φ t with hp
  -- `p` is monotone: the primitive of a nonnegative function is nondecreasing.
  have hmono : Monotone p := by
    intro x y hxy
    simp only [p, add_le_add_iff_left]
    rw [show (∫ t in (0 : ℝ)..y, φ t) = (∫ t in (0 : ℝ)..x, φ t) + ∫ t in x..y, φ t from
      (intervalIntegral.integral_add_adjacent_intervals (hφLI 0 x) (hφLI x y)).symm,
      le_add_iff_nonneg_right]
    exact intervalIntegral.integral_nonneg hxy (fun t _ => hφnn t)
  -- `p` is continuous: the primitive of a locally integrable function is continuous.
  have hcont : Continuous p :=
    Continuous.add continuous_const (intervalIntegral.continuous_primitive hφLI 0)
  -- The Stieltjes measure of `p` is the density measure `volume.withDensity (ofReal φ)`.
  have hμ : hmono.stieltjesFunction.measure
      = volume.withDensity (fun x => ENNReal.ofReal (φ x)) := by
    apply Measure.ext_of_Ioc
    intro a b hab
    rw [StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_apply_of_continuous hmono hcont b,
      Monotone.stieltjesFunction_apply_of_continuous hmono hcont a,
      withDensity_apply _ measurableSet_Ioc]
    have hpdiff : p b - p a = ∫ t in a..b, φ t := by
      simp only [p, add_sub_add_left_eq_sub]
      rw [intervalIntegral.integral_interval_sub_left (hφLI 0 b) (hφLI 0 a)]
    rw [hpdiff, intervalIntegral.integral_of_le hab.le]
    have hint : IntegrableOn φ (Ioc a b) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]; exact hφLI a b
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun x => hφnn x))]
  -- A density measure is absolutely continuous w.r.t. the base measure.
  have hac : hmono.stieltjesFunction.measure ≪ volume := by
    rw [hμ]; exact withDensity_absolutelyContinuous _ _
  -- Condition (N): `volume (p '' S) ≤ μ_p S = 0`.
  have hμS : hmono.stieltjesFunction.measure S = 0 := hac hS
  have hle := volume_image_le_stieltjesMeasure hmono hcont S
  rw [hμS] at hle
  exact le_antisymm hle (zero_le _)

/-! ## The 1D Banach–Zaretsky fundamental theorem of calculus -/

/-- The pointwise a.e. derivative of a monotone `f` equals the (real) Radon–Nikodym density of its
Stieltjes measure, as a `deriv` equation (from `Monotone.ae_hasDerivAt`). -/
theorem monotone_deriv_eq_rnDeriv {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x : ℝ, deriv f x = (hf.stieltjesFunction.measure.rnDeriv volume x).toReal := by
  filter_upwards [hf.ae_hasDerivAt] with x hx
  exact hx.deriv

/-- **The one-dimensional Banach–Zaretsky fundamental theorem of calculus.** A **continuous
monotone** `f : ℝ → ℝ` satisfying Lusin's condition (N) (it carries Lebesgue-null sets to
Lebesgue-null sets) recovers itself from its a.e. derivative by the fundamental theorem of
calculus: `f b - f a = ∫ₐᵇ deriv f`.

The proof: condition (N) makes the Stieltjes measure `μ_f` absolutely continuous w.r.t. Lebesgue
(`monotone_absolutelyContinuous_of_luzinN`), so the singular part vanishes and the increment is
purely the integral of the density `(rnDeriv μ_f volume).toReal`, which is `deriv f` a.e.
(`Monotone.ae_hasDerivAt`). Quantitatively, `setIntegral_toReal_rnDeriv` gives
`∫_{Ioc a b} (rnDeriv μ_f volume).toReal = μ_f.real (Ioc a b) = (f b - f a)` whenever `a ≤ b`.

This is the classical Banach–Zaretsky theorem in the monotone case, the analytic content that
condition (N) removes the singular part. -/
theorem monotone_ftc_of_luzinN {f : ℝ → ℝ} (hf : Monotone f) (hcont : Continuous f)
    (hN : ∀ S : Set ℝ, volume S = 0 → volume (f '' S) = 0) (a b : ℝ) :
    f b - f a = ∫ t in a..b, deriv f t := by
  -- Reduce to `a ≤ b` (the `b ≤ a` case follows by symmetry/negation).
  have hac : hf.stieltjesFunction.measure ≪ volume :=
    monotone_absolutelyContinuous_of_luzinN hf hcont hN
  set μ := hf.stieltjesFunction.measure with hμ
  -- The integrand `deriv f` equals the (real) density a.e., so the interval integrals agree.
  have hderiv : ∀ᵐ x : ℝ, deriv f x = (μ.rnDeriv volume x).toReal :=
    monotone_deriv_eq_rnDeriv hf
  -- Core identity on `Ioc a b` for `a ≤ b`.
  have key : ∀ a b : ℝ, a ≤ b → f b - f a = ∫ t in a..b, deriv f t := by
    intro a b hab
    -- Replace `deriv f` by the density under the integral.
    have hcongr : (∫ t in a..b, deriv f t) = ∫ t in a..b, (μ.rnDeriv volume t).toReal := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with x hx _ using hx
    rw [hcongr, intervalIntegral.integral_of_le hab,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    -- The density is the rnDeriv of `μ ≪ volume`, so its integral over `Icc a b` is `μ.real`.
    have hrn := MeasureTheory.Measure.setIntegral_toReal_rnDeriv (μ := μ) (ν := volume) hac
      (Icc a b)
    rw [hrn]
    -- `μ.real (Icc a b) = (μ (Icc a b)).toReal = (ofReal (f b - f a)).toReal = f b - f a`.
    rw [Measure.real, StieltjesFunction.measure_Icc_of_continuous hf hcont,
      ENNReal.toReal_ofReal (by linarith [hf hab])]
  -- Dispatch the two orderings.
  rcases le_total a b with hab | hba
  · exact key a b hab
  · have := key b a hba
    rw [intervalIntegral.integral_symm] at this
    linarith [this]

/-! ## The bounded-variation Banach–Zaretsky FTC (real-valued)

A continuous function of bounded variation that is a difference `f = p - q` of two **continuous
monotone** functions, each carrying null sets to null sets (condition (N)), satisfies the FTC.
This is the bridge from the monotone case to the general (BV) case, and is the form consumed on a
slice of the quasiconformal inverse: the real and imaginary parts of the slice are continuous BV,
and the genuine 2D area-coupling supplies condition (N) for the monotone pieces. -/

/-- **The bounded-variation Banach–Zaretsky FTC.** If a function `f = p - q` is the difference of
two **continuous monotone** functions `p`, `q : ℝ → ℝ`, each satisfying Lusin's condition (N),
then `f b - f a = ∫ₐᵇ deriv f` whenever `p` and `q` are both a.e. differentiable with
`deriv f = deriv p - deriv q` a.e. (which holds at every point where both `p` and `q` are
differentiable, i.e. almost everywhere).

This is `monotone_ftc_of_luzinN` applied to each monotone piece, recombined by linearity. The
condition-(N) hypotheses on `p` and `q` are exactly what the 2D area-coupling supplies on a slice;
no per-line condition (N) on `f` itself is needed (the decomposition routes it through the monotone
pieces). -/
theorem bv_ftc_of_monotone_diff {f p q : ℝ → ℝ}
    (hp_mono : Monotone p) (hp_cont : Continuous p)
    (hq_mono : Monotone q) (hq_cont : Continuous q)
    (hpN : ∀ S : Set ℝ, volume S = 0 → volume (p '' S) = 0)
    (hqN : ∀ S : Set ℝ, volume S = 0 → volume (q '' S) = 0)
    (hfpq : f = p - q)
    (a b : ℝ) :
    f b - f a = ∫ t in a..b, deriv f t := by
  -- The FTC for each monotone piece.
  have hpFTC := monotone_ftc_of_luzinN hp_mono hp_cont hpN a b
  have hqFTC := monotone_ftc_of_luzinN hq_mono hq_cont hqN a b
  -- `p` and `q` are a.e. differentiable; on the common differentiability set,
  -- `deriv f = deriv p - deriv q`.
  have hp_diff : ∀ᵐ x : ℝ, DifferentiableAt ℝ p x := by
    filter_upwards [hp_mono.ae_hasDerivAt] with x hx using hx.differentiableAt
  have hq_diff : ∀ᵐ x : ℝ, DifferentiableAt ℝ q x := by
    filter_upwards [hq_mono.ae_hasDerivAt] with x hx using hx.differentiableAt
  have hderiv_eq : ∀ᵐ x : ℝ, deriv f x = deriv p x - deriv q x := by
    filter_upwards [hp_diff, hq_diff] with x hxp hxq
    rw [hfpq, deriv_sub hxp hxq]
  -- Integrability of `deriv p`, `deriv q` (each equals its piece's interval increment by the FTC,
  -- hence is interval integrable — derivatives of monotone functions are locally integrable).
  have hp_intble : IntervalIntegrable (deriv p) volume a b :=
    MonotoneOn.intervalIntegrable_deriv (hp_mono.monotoneOn (uIcc a b))
  have hq_intble : IntervalIntegrable (deriv q) volume a b :=
    MonotoneOn.intervalIntegrable_deriv (hq_mono.monotoneOn (uIcc a b))
  -- Recombine.
  have hsplit : (∫ t in a..b, deriv f t) = (∫ t in a..b, deriv p t) - ∫ t in a..b, deriv q t := by
    rw [← intervalIntegral.integral_sub hp_intble hq_intble]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv_eq] with x hx _ using hx
  rw [hsplit, ← hpFTC, ← hqFTC, hfpq]
  simp only [Pi.sub_apply]
  ring

/-! ## The complex-valued Banach–Zaretsky FTC (the slice form)

For the quasiconformal-inverse keystone the slice `t ↦ g ⟨t, y⟩` is **complex**-valued. Its real
and imaginary parts are continuous of bounded variation; on a.e. slice the 2D area-coupling makes
the monotone pieces of each part satisfy condition (N). This packages the recombination of the two
real `bv_ftc_of_monotone_diff` applications into the complex FTC `s b - s a = ∫ₐᵇ s'` with `s'` the
a.e. complex derivative. -/

/-- **The complex-valued Banach–Zaretsky FTC (slice form).** Let `s : ℝ → ℂ` have real part
`s.re = pr - qr` and imaginary part `s.im = pi - qi`, each a difference of **continuous monotone**
functions satisfying Lusin's condition (N). If `s` has a.e. complex derivative `s' t` (with `s'`
interval integrable), then `s b - s a = ∫ₐᵇ s'`.

The real and imaginary FTCs are `bv_ftc_of_monotone_diff` applied to `s.re` and `s.im`; the a.e.
identities `deriv (s.re) = (s' ·).re`, `deriv (s.im) = (s' ·).im` come from the complex derivative,
and the result is recombined through `Complex.re_add_im`. This is the form consumed on a slice of
the quasiconformal inverse, where the condition-(N) hypotheses on the monotone pieces are the
output of the genuine 2D area-coupling. -/
theorem complex_bv_ftc_of_monotone_diff {s s' : ℝ → ℂ}
    {pr qr pi qi : ℝ → ℝ}
    (hpr_mono : Monotone pr) (hpr_cont : Continuous pr)
    (hqr_mono : Monotone qr) (hqr_cont : Continuous qr)
    (hpi_mono : Monotone pi) (hpi_cont : Continuous pi)
    (hqi_mono : Monotone qi) (hqi_cont : Continuous qi)
    (hprN : ∀ S : Set ℝ, volume S = 0 → volume (pr '' S) = 0)
    (hqrN : ∀ S : Set ℝ, volume S = 0 → volume (qr '' S) = 0)
    (hpiN : ∀ S : Set ℝ, volume S = 0 → volume (pi '' S) = 0)
    (hqiN : ∀ S : Set ℝ, volume S = 0 → volume (qi '' S) = 0)
    (hre : (fun t => (s t).re) = pr - qr) (him : (fun t => (s t).im) = pi - qi)
    (hderiv : ∀ᵐ t : ℝ, HasDerivAt s (s' t) t)
    (hint : ∀ a b : ℝ, IntervalIntegrable s' volume a b)
    (a b : ℝ) :
    s b - s a = ∫ t in a..b, s' t := by
  -- Real FTC on the real part.
  have hreFTC : (s b).re - (s a).re = ∫ t in a..b, deriv (fun u => (s u).re) t :=
    bv_ftc_of_monotone_diff hpr_mono hpr_cont hqr_mono hqr_cont hprN hqrN hre a b
  have himFTC : (s b).im - (s a).im = ∫ t in a..b, deriv (fun u => (s u).im) t :=
    bv_ftc_of_monotone_diff hpi_mono hpi_cont hqi_mono hqi_cont hpiN hqiN him a b
  -- Identify the part-derivatives with the components of `s'`.
  have hre_eq : ∀ᵐ t : ℝ, deriv (fun u => (s u).re) t = (s' t).re := by
    filter_upwards [hderiv] with t ht
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using this.deriv
  have him_eq : ∀ᵐ t : ℝ, deriv (fun u => (s u).im) t = (s' t).im := by
    filter_upwards [hderiv] with t ht
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa using this.deriv
  -- Rewrite the FTC integrals in terms of `(s' ·).re` / `(s' ·).im`.
  have hre_int : (s b).re - (s a).re = ∫ t in a..b, (s' t).re := by
    rw [hreFTC]; apply intervalIntegral.integral_congr_ae
    filter_upwards [hre_eq] with t ht _ using ht
  have him_int : (s b).im - (s a).im = ∫ t in a..b, (s' t).im := by
    rw [himFTC]; apply intervalIntegral.integral_congr_ae
    filter_upwards [him_eq] with t ht _ using ht
  -- Recombine `re` / `im`.
  apply Complex.ext
  · rw [Complex.sub_re]
    rw [show (∫ t in a..b, s' t).re = ∫ t in a..b, (s' t).re from ?_]
    · exact hre_int
    · have := (Complex.reCLM.intervalIntegral_comp_comm (hint a b))
      simpa [Complex.reCLM_apply] using this.symm
  · rw [Complex.sub_im]
    rw [show (∫ t in a..b, s' t).im = ∫ t in a..b, (s' t).im from ?_]
    · exact him_int
    · have := (Complex.imCLM.intervalIntegral_comp_comm (hint a b))
      simpa [Complex.imCLM_apply] using this.symm

end RiemannDynamics
