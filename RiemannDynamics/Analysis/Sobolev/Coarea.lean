/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The one-sided co-area (Eilenberg) inequality — GMT infrastructure

This file builds the **Eilenberg inequality** (the *one-sided* co-area inequality) for a Lipschitz
real-valued function on a metric space, as standalone geometric-measure-theory infrastructure. The
target inequality is, for a `K`-Lipschitz `u : X → ℝ` and a nonnegative measurable weight
`g : X → ℝ≥0∞`,

> `∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[d-1]) dc ≤ K · ∫⁻ z, g z ∂μH[d]`     (★)

(the integrated `(d−1)`-Hausdorff measure of the weighted level sets is dominated by the
`d`-dimensional weighted integral, with the Lipschitz constant). In the unweighted, planar form
`d = 2`, `g = ‖∇u‖` this is the genuine ingredient powering the length–area lower bound for the
modulus of a conjugate family of curves (see `QC/GeometricDifferentiable.lean`).

## Direction and truth

The inequality (★) is the **TRUE** one-sided direction. For a Lipschitz `u`, the level sets are
"thin" (they have `μH[d-1]`-measure controlled by the gradient), so the *left*-hand integrated
level-set measure is **bounded above** by the gradient integral. (The reverse inequality, an
*equality*, holds for `u ∈ C¹` with `|∇u| ≠ 0` — the full co-area formula — and is genuinely
deeper; it is **not** what is needed here and is **not** claimed.) The `≤` of (★) is exactly what
the length–area lower bound consumes: it lets one pass from a *gradient-energy* integral to an
*integrated-level-set* integral, which the admissible separating density then bounds below.

### Affine sanity check (`u` affine, the `f = id` degenerate case)

For `u : ℝ² → ℝ` the affine projection `u(x, y) = x` (Lipschitz constant `1`), the level sets are
the vertical lines `{x = c}`, `μH[1]`-measure of `u⁻¹{c} ∩ R` over a rectangle `R = [a,b]×[s,t]` is
`t − s`, and `‖∇u‖ = 1`, so (★) reads `∫_a^b (t − s) dc ≤ 1 · vol(R) = (b−a)(t−s)`, an
**equality**. This reproduces the plain-Fubini affine case that `lengthArea_modulus_lower_bound`
proves directly, confirming the direction.

## What is proved here

The headline result `eilenberg_coarea_grad_le` (the sharp planar co-area inequality with the
*pointwise* gradient, constant `1`) is proved **in full and axiom-clean** — Mathlib has no co-area
formula or Eilenberg inequality, so this is built from scratch. The route is the area-formula one
(the Besicovitch-differentiation shortcut is unsound here: the local co-area density is not
controlled by mere differentiability, e.g. `u(z) = |z|² sin (1/|z|)`):

* `coarea_linear_eq` — the exact affine co-area (Fubini);
* `measurable_slice_hausdorff_one` — measurability of `c ↦ μH[1] (u⁻¹{c} ∩ A)` (compact `A`), via a
  compact-image / countable-open-cover argument with `Metric.thickening`;
* `hausdorffMeasure_one_image_le` — the fiber arc-length bound `μH[1] (γ '' I) ≤ ∫ ‖γ'‖`;
* `ae_uniqueDiffWithinAt_of_measurableSet` — a.e. unique differentiability of a measurable planar
  set (density-`1` ⟹ dense tangent cone);
* `coarea_piece_le` — the IFT-free per-piece core (Lusin decomposition into approximately-linear
  injective pieces + the area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`);
* assembled over `{∇u = 0}` (`coarea_critical_le`, via the scalar Lusin partition — *not* Sard,
  which fails for Lipschitz maps) and `{∇u ≠ 0}` (`coarea_regular_le`) into the unweighted set form
  `coarea_set_sharp`, then the gradient-weighted `eilenberg_coarea_grad_le` by layer-cake.

`hausdorffMeasure_two_complex_smul_volume` records the (proportionality, not equality) normalization
`μH[2] = c • volume` on `ℂ` (the raw Hausdorff measure differs from `volume` by `4/π`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RiemannDynamics.Coarea

variable {X : Type*} [MeasurableSpace X] [EMetricSpace X] [BorelSpace X]

/-! ## Slice measurability — the gating crux of the co-area construction -/

/-- **Measurability of the level-set arc-length in the level parameter (gating crux).**

For a continuous `u : ℂ → ℝ` and a compact set `A ⊆ ℂ`, the map
`c ↦ μH[1] (u ⁻¹' {c} ∩ A)` (the `μH[1]`-measure of the level set `{u = c}` restricted to `A`) is
Borel measurable in `c`.

This is the single technical ingredient that lets the co-area set function
`A ↦ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)` be assembled into a genuine measure `ν` (via `lintegral_tsum`
for countable additivity) and is therefore the gate to the Besicovitch-differentiation localization
that proves the sharp co-area inequality `eilenberg_coarea_grad_le`. Mathlib's only parameter
measurability (`measurable_measure_prodMk_left`) covers *product* slices; the level sets of a
general continuous `u` are curves, not product fibers, so this is net-new.

## Truth and direction

**TRUE.** Proof strategy (compact `A`, separable target): write
`μH[1] (S) = ⨆ n, μH[1]_{1/n} (S)` with `μH[1]_r` the Hausdorff premeasure
(`Measure.mkMetric'.pre`), and bound each premeasure by countable open covers. For a fixed countable
cover `{Tᵢ}` (open, `diam ≤ r`), the cover is *valid for `c`* (i.e. covers `u ⁻¹' {c} ∩ A`) iff
`c ∉ u '' (A ∩ (⋃ᵢ Tᵢ)ᶜ)`; with `A` compact and the `Tᵢ` open, `A ∩ (⋃ Tᵢ)ᶜ` is compact, so its
continuous image `u '' (…)` is **compact** (Borel), making `c ↦ [valid? ∑ diam : ∞]` measurable.
A countable infimum over such covers recovers `μH[1]_{1/n}` (separability), and a countable
supremum over `n` recovers `μH[1]`. The compactness of `A` (so that `u`-images of the complement
pieces are compact = Borel) is what avoids needing the universal measurability of analytic sets. -/
theorem measurable_slice_hausdorff_one {u : ℂ → ℝ} (hu : Continuous u)
    {A : Set ℂ} (hA : IsCompact A) :
    Measurable (fun c => μH[1] (u ⁻¹' {c} ∩ A)) := by
  classical
  -- A countable dense enumeration of `ℂ`, for rational-ball centres.
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℂ, DenseRange D :=
    ⟨TopologicalSpace.denseSeq ℂ, TopologicalSpace.denseRange_denseSeq ℂ⟩
  -- Rational balls, finite unions of them (`elem`), and finite collections of those (`scover`).
  set ball' : ℕ × ℚ → Set ℂ := fun p => Metric.ball (D p.1) (p.2 : ℝ) with hball'
  have hballopen : ∀ p, IsOpen (ball' p) := fun p => Metric.isOpen_ball
  set elem : Finset (ℕ × ℚ) → Set ℂ := fun s => ⋃ p ∈ s, ball' p with helem
  have helem_open : ∀ s, IsOpen (elem s) := fun s => isOpen_biUnion (fun p _ => hballopen p)
  set scover : Finset (Finset (ℕ × ℚ)) → Set ℂ := fun S => ⋃ s ∈ S, elem s with hscover
  have hscover_open : ∀ S, IsOpen (scover S) := fun S => isOpen_biUnion (fun s _ => helem_open s)
  set scost : Finset (Finset (ℕ × ℚ)) → ℝ≥0∞ :=
    fun S => ∑ s ∈ S, ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hscost
  -- The rational-ball basis selector: any point of an open set sits in a small rational ball.
  have hsel : ∀ (z : ℂ) (O : Set ℂ), IsOpen O → z ∈ O →
      ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ball' p ⊆ O := by
    intro z O hO hz
    rw [Metric.isOpen_iff] at hO
    obtain ⟨εO, hεO, hballO⟩ := hO z hz
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show εO/3 < εO/2 by linarith)
    have hqpos : (0:ℝ) < q := by linarith
    obtain ⟨i, hi⟩ := hD.exists_dist_lt z (show (0:ℝ) < εO/3 by linarith)
    refine ⟨(i, q), ?_, ?_⟩
    · rw [hball']; simp only; rw [Metric.mem_ball, dist_comm]
      have : dist z (D i) < (q:ℝ) := by linarith
      rwa [dist_comm] at this
    · rw [hball']; simp only
      intro w hw; rw [Metric.mem_ball] at hw
      apply hballO; rw [Metric.mem_ball]
      calc dist w z ≤ dist w (D i) + dist (D i) z := dist_triangle _ _ _
        _ < q + εO/3 := by rw [dist_comm (D i) z]; linarith
        _ < εO := by linarith
  -- Per-cover validity is Borel (continuous image of a compact set): the indicator is measurable.
  have hind : ∀ {A' : Set ℂ}, IsCompact A' → ∀ (S : Finset (Finset (ℕ × ℚ))) (r : ℝ≥0∞),
      Measurable (fun c : ℝ => if u ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞)) := by
    intro A' hA' S r
    have hborel : MeasurableSet (u '' (A' ∩ (scover S)ᶜ)) :=
      (hA'.inter_right (hscover_open S).isClosed_compl |>.image hu).measurableSet
    have hpred : ∀ c : ℝ, (u ⁻¹' {c} ∩ A' ⊆ scover S) ↔ c ∈ (u '' (A' ∩ (scover S)ᶜ))ᶜ := by
      intro c; rw [mem_compl_iff]
      exact ⟨fun hsub ⟨z, ⟨hzA, hzU⟩, hcz⟩ => hzU (hsub ⟨hcz, hzA⟩),
             fun hc z hz => by by_contra hzU; exact hc ⟨z, ⟨hz.2, hzU⟩, hz.1⟩⟩
    have heq : (fun c : ℝ => if u ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞))
        = fun c : ℝ => if c ∈ (u '' (A' ∩ (scover S)ᶜ))ᶜ then r else ∞ := by
      funext c; exact if_congr (hpred c) rfl rfl
    rw [heq]; exact Measurable.ite hborel.compl measurable_const measurable_const
  -- The scale-`(k+1)⁻¹` restricted Hausdorff content over countable rational covers.
  set Gterm : ℕ → Finset (Finset (ℕ × ℚ)) → ℝ → ℝ≥0∞ :=
    fun k S c => if (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ u ⁻¹' {c} ∩ A ⊆ scover S
                 then scost S else ∞ with hGterm
  set G : ℕ → ℝ → ℝ≥0∞ := fun k c => ⨅ S, Gterm k S c with hG
  have hGmeas : ∀ k, Measurable (G k) := by
    intro k; apply Measurable.iInf; intro S
    change Measurable (fun c => Gterm k S c)
    by_cases hsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹
    · have he : (fun c => Gterm k S c)
          = fun c => if u ⁻¹' {c} ∩ A ⊆ scover S then scost S else ∞ := by
        funext c; exact if_congr (by tauto) rfl rfl
      rw [he]; exact hind hA S (scost S)
    · have he : (fun c => Gterm k S c) = fun _ => (∞ : ℝ≥0∞) := by
        funext c; simp only [hGterm]; rw [if_neg (by tauto)]
      rw [he]; exact measurable_const
  -- It now suffices to identify `μH[1] (u⁻¹{c} ∩ A)` with the measurable `⨆ k, G k c`.
  suffices hF : ∀ c, μH[(1:ℝ)] (u ⁻¹' {c} ∩ A) = ⨆ k, G k c by
    have heq : (fun c => μH[(1:ℝ)] (u ⁻¹' {c} ∩ A)) = fun c => ⨆ k, G k c := funext hF
    have hconv : (fun c => μH[1] (u ⁻¹' {c} ∩ A)) = fun c => ⨆ k, G k c := heq
    rw [hconv]; exact Measurable.iSup hGmeas
  intro c
  set K : Set ℂ := u ⁻¹' {c} ∩ A with hK_def
  have hK : IsCompact K := hA.inter_left (IsClosed.preimage hu isClosed_singleton)
  -- The unrestricted (arbitrary-cover) Hausdorff content at scale `r`.
  set content : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ (t : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) with hcontent
  have hHA : μH[(1:ℝ)] K = ⨆ (r : ℝ≥0∞) (_ : 0 < r), content r := Measure.hausdorffMeasure_apply _ _
  have hcontent_anti : ∀ r r' : ℝ≥0∞, r ≤ r' → content r' ≤ content r := by
    intro r r' hrr'; rw [hcontent]
    refine iInf_mono fun t => iInf_mono fun hcov => le_iInf fun hsmall => ?_
    exact iInf_le_of_le (fun n => (hsmall n).trans hrr') le_rfl
  -- (A)  content at scale `(k+1)⁻¹` is below `G k c`.
  have hA_dir : ∀ k : ℕ, content ((k:ℝ≥0∞)+1)⁻¹ ≤ G k c := by
    intro k
    rw [hG]; simp only
    refine le_iInf fun S => ?_
    rw [hGterm]; simp only
    by_cases hvalid : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ K ⊆ scover S
    · rw [if_pos hvalid]
      -- content ≤ scost S, by exhibiting the padded cover `t = (S.toList.map elem).getD · ∅`.
      obtain ⟨hsmall, hcov⟩ := hvalid
      set l : List (Finset (ℕ × ℚ)) := S.toList with hl
      have hlmem : ∀ x, x ∈ l ↔ x ∈ S := fun x => Finset.mem_toList
      set t : ℕ → Set ℂ := fun n => ((l.map elem).getD n ∅) with ht
      have hlen : (l.map elem).length = l.length := List.length_map _
      have htmem : ∀ n, (∃ s ∈ S, t n = elem s) ∨ t n = ∅ := by
        intro n
        rcases lt_or_ge n l.length with hlt | hge
        · left; refine ⟨l[n], (hlmem _).1 (List.getElem_mem hlt), ?_⟩
          simp only [ht]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
              Option.getD_some, List.getElem_map]
        · right; simp only [ht]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
              Option.getD_none]
      have htsmall : ∀ n, Metric.ediam (t n) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
        intro n; rcases htmem n with ⟨s, hs, hts⟩ | h0
        · rw [hts]; exact hsmall s hs
        · rw [h0]; simp
      have htcov : K ⊆ ⋃ n, t n := by
        refine hcov.trans ?_
        intro z hz; rw [hscover] at hz; simp only [mem_iUnion] at hz ⊢
        obtain ⟨s, hs, hzs⟩ := hz
        obtain ⟨i, hi⟩ := List.getElem_of_mem ((hlmem s).2 hs)
        refine ⟨i, ?_⟩
        have : t i = elem s := by
          simp only [ht]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi.1),
              Option.getD_some, List.getElem_map, hi.2]
        rw [this]; exact hzs
      have hcosteq : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = scost S := by
        set h : Finset (ℕ × ℚ) → ℝ≥0∞ :=
          fun s => ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hh
        have hFn : ∀ n,
            (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = (l.map h).getD n 0 := by
          intro n
          rcases lt_or_ge n l.length with hlt | hge
          · have htn : t n = elem (l[n]) := by
              simp only [ht]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
                  Option.getD_some, List.getElem_map]
            have hhn : (l.map h).getD n 0 = h (l[n]) := by
              rw [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem (by rw [List.length_map]; exact hlt),
                  Option.getD_some, List.getElem_map]
            rw [htn, hhn, hh]
          · have htn : t n = ∅ := by
              simp only [ht]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
                  Option.getD_none]
            have hhn : (l.map h).getD n 0 = 0 := by
              rw [List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by rw [List.length_map]; exact hge), Option.getD_none]
            rw [htn, hhn]; simp
        have htsum : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = (l.map h).sum := by
          rw [show (fun n => ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
                = fun n => (l.map h).getD n 0 from funext hFn]
          rw [tsum_eq_sum (s := Finset.range (l.map h).length) ?_]
          · rw [← Fin.sum_univ_getElem (l.map h), Finset.sum_range fun n => (l.map h).getD n 0]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
          · intro b hb; simp only [Finset.mem_range, not_lt] at hb
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hb, Option.getD_none]
        rw [htsum, hscost, hl, ← List.sum_toFinset h S.nodup_toList, Finset.toList_toFinset]
      rw [hcontent]
      calc (⨅ (t' : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, t' n) (_ : ∀ n, Metric.ediam (t' n) ≤ ((k:ℝ≥0∞)+1)⁻¹),
              ∑' n, ⨆ _ : (t' n).Nonempty, Metric.ediam (t' n) ^ (1:ℝ))
          ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) :=
            iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htsmall le_rfl))
        _ = scost S := hcosteq
    · rw [if_neg hvalid]; exact le_top
  -- (B)  `G k c` is below the content at scale `(2(k+1))⁻¹`.
  have hB_dir : ∀ k : ℕ, G k c ≤ content (2*((k:ℝ≥0∞)+1))⁻¹ := by
    intro k
    rw [hcontent]
    refine le_iInf fun t => le_iInf fun htcov => le_iInf fun htsmall => ?_
    -- It suffices to dominate by the `t`-cost plus any `ε`.
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hεpos _
    set εE : ℝ≥0∞ := (ε : ℝ≥0∞) with hεE
    have hεEpos : 0 < εE := by rw [hεE]; exact_mod_cast hεpos
    have hεEtop : εE ≠ ∞ := by rw [hεE]; exact ENNReal.coe_ne_top
    -- BUILD the rational `(k+1)⁻¹`-cover from the `t`-cover (the thickening / grouping core).
    set e : ℝ := εE.toReal with he_def
    have he : 0 < e := by rw [he_def]; exact ENNReal.toReal_pos hεEpos.ne' hεEtop
    set δ : ℕ → ℝ := fun n => min (1/(4*((k:ℝ)+1))) (e * (1/2)^(n+2)) with hδ_def
    have hkR1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hδpos : ∀ n, 0 < δ n := fun n => lt_min (by positivity) (by positivity)
    have hδle : ∀ n, δ n ≤ 1/(4*((k:ℝ)+1)) := fun n => min_le_left _ _
    have hδsum : (∑' n, ENNReal.ofReal (2 * δ n)) ≤ εE := by
      have hgeo : Summable (fun n : ℕ => ((1:ℝ)/2)^n) := summable_geometric_two
      have hsumm : Summable (fun n : ℕ => 2 * (e * (1/2)^(n+2))) := by
        have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
             = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
        rw [this]; exact hgeo.mul_left _
      have hval : (∑' n : ℕ, 2 * (e * ((1:ℝ)/2)^(n+2))) = e := by
        have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
             = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
        rw [this, tsum_mul_left, tsum_geometric_two]; ring
      calc (∑' n, ENNReal.ofReal (2 * δ n))
          ≤ ∑' n, ENNReal.ofReal (2 * (e * (1/2)^(n+2))) := by
            apply ENNReal.tsum_le_tsum; intro n; apply ENNReal.ofReal_le_ofReal
            have := min_le_right (1/(4*((k:ℝ)+1)):ℝ) (e * (1/2)^(n+2))
            rw [hδ_def]; simp only; linarith
        _ = ENNReal.ofReal (∑' n, 2 * (e * (1/2)^(n+2))) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm).symm
        _ = ENNReal.ofReal e := by rw [hval]
        _ = εE := by rw [he_def, ENNReal.ofReal_toReal hεEtop]
    set W : ℕ → Set ℂ := fun n => Metric.thickening (δ n) (t n) with hW_def
    have hWopen : ∀ n, IsOpen (W n) := fun n => Metric.isOpen_thickening
    have htsubW : ∀ n, t n ⊆ W n := fun n => Metric.self_subset_thickening (hδpos n) (t n)
    have hKW : K ⊆ ⋃ n, W n := htcov.trans (iUnion_mono (fun n => htsubW n))
    set B : ℕ → ℝ≥0∞ := fun n => Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) with hB_def
    have hWdiam : ∀ n, Metric.ediam (W n) ≤ B n := by
      intro n; apply Metric.ediam_le
      intro x hx y hy
      rw [hW_def] at hx hy; simp only [Metric.mem_thickening_iff] at hx hy
      obtain ⟨x', hx', hxx'⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hy
      have hstep : edist x y ≤ (edist x x' + edist x' y') + edist y' y := by
        refine (edist_triangle x y' y).trans ?_; gcongr; exact edist_triangle x x' y'
      refine hstep.trans ?_
      have h1 : edist x x' ≤ ENNReal.ofReal (δ n) := by
        rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hxx'.le
      have h2 : edist x' y' ≤ Metric.ediam (t n) := Metric.edist_le_ediam_of_mem hx' hy'
      have h3 : edist y' y ≤ ENNReal.ofReal (δ n) := by
        rw [edist_dist, dist_comm]; exact ENNReal.ofReal_le_ofReal hyy'.le
      rw [hB_def]; simp only
      calc (edist x x' + edist x' y') + edist y' y
          ≤ (ENNReal.ofReal (δ n) + Metric.ediam (t n)) + ENNReal.ofReal (δ n) := by gcongr
        _ = Metric.ediam (t n) + (ENNReal.ofReal (δ n) + ENNReal.ofReal (δ n)) := by ring
        _ = Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) := by
            rw [← ENNReal.ofReal_add (hδpos n).le (hδpos n).le]; ring_nf
    have hBsmall : ∀ n, B n ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
      intro n; rw [hB_def]; simp only
      have hle1 : Metric.ediam (t n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := htsmall n
      have hle2 : ENNReal.ofReal (2 * δ n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := by
        have hd : (2 * δ n) ≤ 1/(2*((k:ℝ)+1)) := by
          have := hδle n; rw [le_div_iff₀ (by positivity)] at this ⊢; nlinarith
        refine (ENNReal.ofReal_le_ofReal hd).trans ?_
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul (by norm_num)]
        rw [show ENNReal.ofReal ((k:ℝ)+1) = (k:ℝ≥0∞)+1 by
              rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; norm_num,
            show ENNReal.ofReal 2 = (2:ℝ≥0∞) by norm_num, one_div]
      calc Metric.ediam (t n) + ENNReal.ofReal (2 * δ n)
          ≤ (2*((k:ℝ≥0∞)+1))⁻¹ + (2*((k:ℝ≥0∞)+1))⁻¹ := by gcongr
        _ = ((k:ℝ≥0∞)+1)⁻¹ := by
            rw [← two_mul, ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    -- finite subcover + selection (rational balls assigned to thickenings)
    have hcovP : ∀ z ∈ K, ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ∃ n, ball' p ⊆ W n := by
      intro z hz
      obtain ⟨n, hn⟩ : ∃ n, z ∈ W n := by have := hKW hz; rwa [mem_iUnion] at this
      obtain ⟨p, hzp, hpW⟩ := hsel z (W n) (hWopen n) hn
      exact ⟨p, hzp, n, hpW⟩
    choose! pp hzpp hnpp using hcovP
    obtain ⟨T, hTsub, hTfin, hTcov⟩ := hK.elim_finite_subcover_image
      (b := K) (c := fun z => ball' (pp z)) (fun z _ => hballopen (pp z))
      (by intro z hz; rw [mem_iUnion₂]; exact ⟨z, hz, hzpp z hz⟩)
    set Tf := hTfin.toFinset with hTf
    set P : Finset (ℕ × ℚ) := Tf.image pp with hP
    have hPprop : ∀ p ∈ P, ∃ n, ball' p ⊆ W n := by
      intro p hp; rw [hP, Finset.mem_image] at hp
      obtain ⟨z, hzT, rfl⟩ := hp
      exact hnpp z (hTsub (by rw [hTf, Set.Finite.mem_toFinset] at hzT; exact hzT))
    choose! ν hν using hPprop
    have hKcovP : K ⊆ ⋃ p ∈ P, ball' p := by
      intro z hz
      have := hTcov hz; rw [mem_iUnion₂] at this
      obtain ⟨w, hwT, hzw⟩ := this
      rw [mem_iUnion₂]; refine ⟨pp w, ?_, hzw⟩
      rw [hP, Finset.mem_image]; exact ⟨w, by rw [hTf, Set.Finite.mem_toFinset]; exact hwT, rfl⟩
    have hνW : ∀ p ∈ P, ball' p ⊆ W (ν p) := fun p hp => hν p hp
    -- grouping into `S`
    set grp : ℕ → Finset (ℕ × ℚ) := fun n => P.filter (fun p => ν p = n) with hgrp
    set S : Finset (Finset (ℕ × ℚ)) := (P.image ν).image grp with hS
    have hgrpW : ∀ n, elem (grp n) ⊆ W n := by
      intro n; rw [helem]; refine iUnion₂_subset ?_; intro p hp
      rw [hgrp, Finset.mem_filter] at hp; rw [← hp.2]; exact hνW p hp.1
    have hgrpdiam : ∀ n, Metric.ediam (elem (grp n)) ≤ B n := fun n =>
      (Metric.ediam_mono (hgrpW n)).trans (hWdiam n)
    -- `S` is a valid `(k+1)⁻¹`-cover, so `G k c ≤ scost S`.
    have hScover : K ⊆ scover S := by
      rw [hscover]
      refine hKcovP.trans ?_
      intro z hz; rw [mem_iUnion₂] at hz; obtain ⟨p, hp, hzp⟩ := hz
      rw [mem_iUnion₂]; refine ⟨grp (ν p), ?_, ?_⟩
      · rw [hS, Finset.mem_image]; exact ⟨ν p, Finset.mem_image_of_mem ν hp, rfl⟩
      · rw [helem, mem_iUnion₂]; exact ⟨p, by rw [hgrp, Finset.mem_filter]; exact ⟨hp, rfl⟩, hzp⟩
    have hSsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
      intro s hs; rw [hS, Finset.mem_image] at hs
      obtain ⟨n, hn, rfl⟩ := hs; exact (hgrpdiam n).trans (hBsmall n)
    have hGle : G k c ≤ scost S := by
      rw [hG]; simp only
      refine iInf_le_of_le S ?_
      rw [hGterm]; simp only; rw [if_pos ⟨hSsmall, hScover⟩]
    refine hGle.trans ?_
    -- cost of `S` ≤ `t`-cost + ε
    have himg : scost S
        ≤ ∑ n ∈ P.image ν,
            (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) := by
      rw [hscost, hS, ← Finset.sum_fiberwise_of_maps_to (g := grp) (t := (P.image ν).image grp)
            (fun n hn => Finset.mem_image_of_mem grp hn)]
      apply Finset.sum_le_sum; intro s hs
      obtain ⟨n0, hn0T, hn0⟩ := Finset.mem_image.1 hs
      have hmem : n0 ∈ (P.image ν).filter (fun n => grp n = s) := Finset.mem_filter.2 ⟨hn0T, hn0⟩
      calc (⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ))
          = (⨆ _ : (elem (grp n0)).Nonempty, Metric.ediam (elem (grp n0)) ^ (1:ℝ)) := by rw [hn0]
        _ ≤ ∑ n ∈ (P.image ν).filter (fun n => grp n = s),
              (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) :=
            Finset.single_le_sum
              (f := fun n => ⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
              (fun _ _ => zero_le _) hmem
    have hstep2 :
        ∑ n ∈ P.image ν, (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
          ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
              + ENNReal.ofReal (2 * δ n)) := by
      apply Finset.sum_le_sum; intro n _
      have hb : (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) ≤ B n := by
        refine iSup_le (fun _ => ?_); rw [ENNReal.rpow_one]; exact hgrpdiam n
      refine hb.trans ?_
      rw [hB_def]; simp only; gcongr
      by_cases h : (t n).Nonempty
      · rw [ciSup_pos h, ENNReal.rpow_one]
      · rw [not_nonempty_iff_eq_empty] at h; rw [h]; simp
    calc scost S
        ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
            + ENNReal.ofReal (2 * δ n)) := himg.trans hstep2
      _ = (∑ n ∈ P.image ν, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)))
            + ∑ n ∈ P.image ν, ENNReal.ofReal (2 * δ n) := Finset.sum_add_distrib
      _ ≤ (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) + εE :=
            add_le_add (ENNReal.sum_le_tsum _) ((ENNReal.sum_le_tsum _).trans hδsum)
  -- Assemble:  μH[1] K = ⨆ k, G k c.
  apply le_antisymm
  · rw [hHA]; refine iSup₂_le ?_; intro r hr
    obtain ⟨k, hkr⟩ : ∃ k : ℕ, ((k:ℝ≥0∞)+1)⁻¹ ≤ r := by
      rcases eq_or_ne r ∞ with rfl | hrtop
      · exact ⟨0, le_top⟩
      · obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (a := r) hr.ne'
        exact ⟨k, (ENNReal.inv_le_inv.2 le_self_add).trans hk.le⟩
    calc content r ≤ content ((k:ℝ≥0∞)+1)⁻¹ := hcontent_anti _ _ hkr
      _ ≤ G k c := hA_dir k
      _ ≤ ⨆ k, G k c := le_iSup (fun k => G k c) k
  · refine iSup_le ?_; intro k
    calc G k c ≤ content (2*((k:ℝ≥0∞)+1))⁻¹ := hB_dir k
      _ ≤ μH[(1:ℝ)] K := by
          rw [hHA]; refine le_iSup₂_of_le (2*((k:ℝ≥0∞)+1))⁻¹ ?_ le_rfl
          rw [ENNReal.inv_pos]
          exact ENNReal.mul_ne_top (by norm_num)
            (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, by norm_num⟩)

/-- **Planar metric Eilenberg inequality on `ℂ` (unblocked by `measurable_slice_hausdorff_one`).**

For `u : ℂ → ℝ` that is `K`-Lipschitz on a compact set `A`, the integrated arc-length of the level
sets of `u` meeting `A` is bounded by `K` times the 2-dimensional Hausdorff measure of `A`:

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A`.

This is the **raw (un-normalized) metric Eilenberg inequality** specialized to the plane with the
level-arc-length weight. The constant is the (local) Lipschitz constant `K` — *not* the sharp
gradient — so on its own it carries the unavoidable `μH[2] = (4/π)·volume` mismatch; it is used in
the sharp-co-area localization only where that factor is multiplied by a vanishing quantity (the
`∇u = 0` set, where the local Lipschitz constant tends to `0`, and the `volume`-null remainder,
where `μH[2] = (4/π)·volume = 0`). The sharp leading term comes instead from `coarea_linear_eq`.

## Truth, direction, and proof

**TRUE**, one-sided `≤`, constant exactly `K` (raw Hausdorff convention). Proof: write
`μH[1] (S) = ⨆ n, μH[1]_{1/n} (S)` via the Hausdorff premeasures and pass the supremum out of the
`c`-integral by monotone convergence — legitimate because each premeasure slice
`c ↦ μH[1]_{1/n} (u ⁻¹' {c} ∩ A)` is measurable by the same compact-image / countable-open-cover
argument as `measurable_slice_hausdorff_one`. For a fixed scale and a fixed cover `{Tᵢ}` of `A` with
`diam Tᵢ ≤ 1/n`, `μH[1]_{1/n} (u ⁻¹' {c} ∩ A) ≤ ∑_{i : c ∈ u '' (A ∩ Tᵢ)} diam Tᵢ`; integrating in
`c` (dominating `𝟙[c ∈ u '' (A ∩ Tᵢ)]` by `𝟙[c ∈ Icc (sInf) (sSup)]`, whose integral is the length
`≤ K · diam Tᵢ` by the Lipschitz oscillation bound) gives `∑ᵢ diam Tᵢ · K · diam Tᵢ = K ∑ᵢ diam²`;
infimum over covers yields `K · μH[2]_{1/n} (A) ≤ K · μH[2] A`. -/
theorem eilenberg_coarea_planar_metric {u : ℂ → ℝ} {K : ℝ≥0} {A : Set ℂ}
    (hu : LipschitzOnWith K u A) (hA : IsCompact A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A := by
  classical
  -- Handle the degenerate `K = 0` case (then `u` is constant on `A`).
  rcases eq_or_ne K 0 with hK0 | hKne0
  · subst hK0
    rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero]
    rcases A.eq_empty_or_nonempty with hAe | ⟨z0, hz0⟩
    · subst hAe; simp
    · have hconst : ∀ x ∈ A, u x = u z0 := fun x hx =>
        (LipschitzOnWith.zero_iff u).1 hu x hx z0 hz0
      have hsupp : (fun c => μH[1] (u ⁻¹' {c} ∩ A))
          = Set.indicator {u z0} (fun _ => μH[1] A) := by
        funext c
        by_cases hc : c = u z0
        · subst hc
          rw [indicator_of_mem (by simp)]
          congr 1
          rw [Set.inter_eq_right]
          intro x hx
          simp only [mem_preimage, mem_singleton_iff]; exact hconst x hx
        · rw [indicator_of_notMem (by simp [hc])]
          have hemp : u ⁻¹' {c} ∩ A = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro x ⟨hxc, hxA⟩
            simp only [mem_preimage, mem_singleton_iff] at hxc
            exact hc (by rw [← hxc, hconst x hxA])
          rw [hemp, measure_empty]
      rw [hsupp, lintegral_indicator (measurableSet_singleton _), setLIntegral_const,
        Real.volume_singleton, mul_zero]
  -- Main case: `K ≠ 0`.
  obtain ⟨g, hgLip, hgEq⟩ := hu.extend_real
  have hgcont : Continuous g := hgLip.continuous
  have hslice_eq : ∀ c : ℝ, u ⁻¹' {c} ∩ A = g ⁻¹' {c} ∩ A := by
    intro c; ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [← hgEq hzA]; exact hz, hzA⟩
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [hgEq hzA]; exact hz, hzA⟩
  rw [show (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)) = ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ A) by
        apply lintegral_congr; intro c; rw [hslice_eq c]]
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℂ, DenseRange D :=
    ⟨TopologicalSpace.denseSeq ℂ, TopologicalSpace.denseRange_denseSeq ℂ⟩
  set ball' : ℕ × ℚ → Set ℂ := fun p => Metric.ball (D p.1) (p.2 : ℝ) with hball'
  have hballopen : ∀ p, IsOpen (ball' p) := fun p => Metric.isOpen_ball
  set elem : Finset (ℕ × ℚ) → Set ℂ := fun s => ⋃ p ∈ s, ball' p with helem
  have helem_open : ∀ s, IsOpen (elem s) := fun s => isOpen_biUnion (fun p _ => hballopen p)
  set scover : Finset (Finset (ℕ × ℚ)) → Set ℂ := fun S => ⋃ s ∈ S, elem s with hscover
  have hscover_open : ∀ S, IsOpen (scover S) := fun S => isOpen_biUnion (fun s _ => helem_open s)
  set scost : Finset (Finset (ℕ × ℚ)) → ℝ≥0∞ :=
    fun S => ∑ s ∈ S, ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hscost
  have hsel : ∀ (z : ℂ) (O : Set ℂ), IsOpen O → z ∈ O →
      ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ball' p ⊆ O := by
    intro z O hO hz
    rw [Metric.isOpen_iff] at hO
    obtain ⟨εO, hεO, hballO⟩ := hO z hz
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show εO/3 < εO/2 by linarith)
    have hqpos : (0:ℝ) < q := by linarith
    obtain ⟨i, hi⟩ := hD.exists_dist_lt z (show (0:ℝ) < εO/3 by linarith)
    refine ⟨(i, q), ?_, ?_⟩
    · rw [hball']; simp only; rw [Metric.mem_ball, dist_comm]
      have : dist z (D i) < (q:ℝ) := by linarith
      rwa [dist_comm] at this
    · rw [hball']; simp only
      intro w hw; rw [Metric.mem_ball] at hw
      apply hballO; rw [Metric.mem_ball]
      calc dist w z ≤ dist w (D i) + dist (D i) z := dist_triangle _ _ _
        _ < q + εO/3 := by rw [dist_comm (D i) z]; linarith
        _ < εO := by linarith
  have hind : ∀ {A' : Set ℂ}, IsCompact A' → ∀ (S : Finset (Finset (ℕ × ℚ))) (r : ℝ≥0∞),
      Measurable (fun c : ℝ => if g ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞)) := by
    intro A' hA' S r
    have hborel : MeasurableSet (g '' (A' ∩ (scover S)ᶜ)) :=
      (hA'.inter_right (hscover_open S).isClosed_compl |>.image hgcont).measurableSet
    have hpred : ∀ c : ℝ, (g ⁻¹' {c} ∩ A' ⊆ scover S) ↔ c ∈ (g '' (A' ∩ (scover S)ᶜ))ᶜ := by
      intro c; rw [mem_compl_iff]
      exact ⟨fun hsub ⟨z, ⟨hzA, hzU⟩, hcz⟩ => hzU (hsub ⟨hcz, hzA⟩),
             fun hc z hz => by by_contra hzU; exact hc ⟨z, ⟨hz.2, hzU⟩, hz.1⟩⟩
    have heq : (fun c : ℝ => if g ⁻¹' {c} ∩ A' ⊆ scover S then r else (∞ : ℝ≥0∞))
        = fun c : ℝ => if c ∈ (g '' (A' ∩ (scover S)ᶜ))ᶜ then r else ∞ := by
      funext c; exact if_congr (hpred c) rfl rfl
    rw [heq]; exact Measurable.ite hborel.compl measurable_const measurable_const
  set Gterm : ℕ → Finset (Finset (ℕ × ℚ)) → ℝ → ℝ≥0∞ :=
    fun k S c => if (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ g ⁻¹' {c} ∩ A ⊆ scover S
                 then scost S else ∞ with hGterm
  set G : ℕ → ℝ → ℝ≥0∞ := fun k c => ⨅ S, Gterm k S c with hG
  have hGmeas : ∀ k, Measurable (G k) := by
    intro k; apply Measurable.iInf; intro S
    change Measurable (fun c => Gterm k S c)
    by_cases hsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹
    · have he : (fun c => Gterm k S c)
          = fun c => if g ⁻¹' {c} ∩ A ⊆ scover S then scost S else ∞ := by
        funext c; exact if_congr (by tauto) rfl rfl
      rw [he]; exact hind hA S (scost S)
    · have he : (fun c => Gterm k S c) = fun _ => (∞ : ℝ≥0∞) := by
        funext c; simp only [hGterm]; rw [if_neg (by tauto)]
      rw [he]; exact measurable_const
  -- per-c content (dimension 1) of the slice
  set content : ℝ → ℝ≥0∞ → ℝ≥0∞ := fun c r =>
    ⨅ (t : ℕ → Set ℂ) (_ : (g ⁻¹' {c} ∩ A) ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) with hcontent
  -- For each c: the supremum identity and the B-direction.
  have hkey : ∀ c : ℝ,
      μH[(1:ℝ)] (g ⁻¹' {c} ∩ A) = ⨆ k, G k c
      ∧ ∀ k : ℕ, G k c ≤ content c (2*((k:ℝ≥0∞)+1))⁻¹ := by
    intro c
    set Kc : Set ℂ := g ⁻¹' {c} ∩ A with hK_def
    have hKc : IsCompact Kc := hA.inter_left (IsClosed.preimage hgcont isClosed_singleton)
    have hHA : μH[(1:ℝ)] Kc = ⨆ (r : ℝ≥0∞) (_ : 0 < r), content c r :=
      Measure.hausdorffMeasure_apply _ _
    have hcontent_anti : ∀ r r' : ℝ≥0∞, r ≤ r' → content c r' ≤ content c r := by
      intro r r' hrr'; rw [hcontent]
      refine iInf_mono fun t => iInf_mono fun hcov => le_iInf fun hsmall => ?_
      exact iInf_le_of_le (fun n => (hsmall n).trans hrr') le_rfl
    -- (A) content at scale (k+1)⁻¹ ≤ G k c.
    have hA_dir : ∀ k : ℕ, content c ((k:ℝ≥0∞)+1)⁻¹ ≤ G k c := by
      intro k
      rw [hG]; simp only
      refine le_iInf fun S => ?_
      rw [hGterm]; simp only
      by_cases hvalid : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹) ∧ Kc ⊆ scover S
      · rw [if_pos hvalid]
        obtain ⟨hsmall, hcov⟩ := hvalid
        set l : List (Finset (ℕ × ℚ)) := S.toList with hl
        have hlmem : ∀ x, x ∈ l ↔ x ∈ S := fun x => Finset.mem_toList
        set t : ℕ → Set ℂ := fun n => ((l.map elem).getD n ∅) with ht
        have hlen : (l.map elem).length = l.length := List.length_map _
        have htmem : ∀ n, (∃ s ∈ S, t n = elem s) ∨ t n = ∅ := by
          intro n
          rcases lt_or_ge n l.length with hlt | hge
          · left; refine ⟨l[n], (hlmem _).1 (List.getElem_mem hlt), ?_⟩
            simp only [ht]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
                Option.getD_some, List.getElem_map]
          · right; simp only [ht]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
                Option.getD_none]
        have htsmall : ∀ n, Metric.ediam (t n) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
          intro n; rcases htmem n with ⟨s, hs, hts⟩ | h0
          · rw [hts]; exact hsmall s hs
          · rw [h0]; simp
        have htcov : Kc ⊆ ⋃ n, t n := by
          refine hcov.trans ?_
          intro z hz; rw [hscover] at hz; simp only [mem_iUnion] at hz ⊢
          obtain ⟨s, hs, hzs⟩ := hz
          obtain ⟨i, hi⟩ := List.getElem_of_mem ((hlmem s).2 hs)
          refine ⟨i, ?_⟩
          have : t i = elem s := by
            simp only [ht]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi.1),
                Option.getD_some, List.getElem_map, hi.2]
          rw [this]; exact hzs
        have hcosteq : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = scost S := by
          set h : Finset (ℕ × ℚ) → ℝ≥0∞ :=
            fun s => ⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ) with hh
          have hFn : ∀ n,
              (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) = (l.map h).getD n 0 := by
            intro n
            rcases lt_or_ge n l.length with hlt | hge
            · have htn : t n = elem (l[n]) := by
                simp only [ht]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hlt),
                    Option.getD_some, List.getElem_map]
              have hhn : (l.map h).getD n 0 = h (l[n]) := by
                rw [List.getD_eq_getElem?_getD,
                    List.getElem?_eq_getElem (by rw [List.length_map]; exact hlt),
                    Option.getD_some, List.getElem_map]
              rw [htn, hhn, hh]
            · have htn : t n = ∅ := by
                simp only [ht]
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; exact hge),
                    Option.getD_none]
              have hhn : (l.map h).getD n 0 = 0 := by
                rw [List.getD_eq_getElem?_getD,
                    List.getElem?_eq_none (by rw [List.length_map]; exact hge), Option.getD_none]
              rw [htn, hhn]; simp
          have htsum : (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
              = (l.map h).sum := by
            rw [show (fun n => ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
                  = fun n => (l.map h).getD n 0 from funext hFn]
            rw [tsum_eq_sum (s := Finset.range (l.map h).length) ?_]
            · rw [← Fin.sum_univ_getElem (l.map h), Finset.sum_range fun n => (l.map h).getD n 0]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
            · intro b hb; simp only [Finset.mem_range, not_lt] at hb
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hb, Option.getD_none]
          rw [htsum, hscost, hl, ← List.sum_toFinset h S.nodup_toList, Finset.toList_toFinset]
        rw [hcontent]
        calc (⨅ (t' : ℕ → Set ℂ) (_ : Kc ⊆ ⋃ n, t' n)
                  (_ : ∀ n, Metric.ediam (t' n) ≤ ((k:ℝ≥0∞)+1)⁻¹),
                ∑' n, ⨆ _ : (t' n).Nonempty, Metric.ediam (t' n) ^ (1:ℝ))
            ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ) :=
              iInf_le_of_le t (iInf_le_of_le htcov (iInf_le_of_le htsmall le_rfl))
          _ = scost S := hcosteq
      · rw [if_neg hvalid]; exact le_top
    -- (B) G k c ≤ content at scale (2(k+1))⁻¹.
    have hB_dir : ∀ k : ℕ, G k c ≤ content c (2*((k:ℝ≥0∞)+1))⁻¹ := by
      intro k
      rw [hcontent]
      refine le_iInf fun t => le_iInf fun htcov => le_iInf fun htsmall => ?_
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hεpos _
      set εE : ℝ≥0∞ := (ε : ℝ≥0∞) with hεE
      have hεEpos : 0 < εE := by rw [hεE]; exact_mod_cast hεpos
      have hεEtop : εE ≠ ∞ := by rw [hεE]; exact ENNReal.coe_ne_top
      set e : ℝ := εE.toReal with he_def
      have he : 0 < e := by rw [he_def]; exact ENNReal.toReal_pos hεEpos.ne' hεEtop
      set δ : ℕ → ℝ := fun n => min (1/(4*((k:ℝ)+1))) (e * (1/2)^(n+2)) with hδ_def
      have hkR1 : (0:ℝ) < (k:ℝ)+1 := by positivity
      have hδpos : ∀ n, 0 < δ n := fun n => lt_min (by positivity) (by positivity)
      have hδle : ∀ n, δ n ≤ 1/(4*((k:ℝ)+1)) := fun n => min_le_left _ _
      have hδsum : (∑' n, ENNReal.ofReal (2 * δ n)) ≤ εE := by
        have hgeo : Summable (fun n : ℕ => ((1:ℝ)/2)^n) := summable_geometric_two
        have hsumm : Summable (fun n : ℕ => 2 * (e * (1/2)^(n+2))) := by
          have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
               = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
          rw [this]; exact hgeo.mul_left _
        have hval : (∑' n : ℕ, 2 * (e * ((1:ℝ)/2)^(n+2))) = e := by
          have : (fun n : ℕ => 2 * (e * ((1:ℝ)/2)^(n+2)))
               = fun n => (2 * e * ((1:ℝ)/2)^2) * (1/2)^n := by funext n; rw [pow_add]; ring
          rw [this, tsum_mul_left, tsum_geometric_two]; ring
        calc (∑' n, ENNReal.ofReal (2 * δ n))
            ≤ ∑' n, ENNReal.ofReal (2 * (e * (1/2)^(n+2))) := by
              apply ENNReal.tsum_le_tsum; intro n; apply ENNReal.ofReal_le_ofReal
              have := min_le_right (1/(4*((k:ℝ)+1)):ℝ) (e * (1/2)^(n+2))
              rw [hδ_def]; simp only; linarith
          _ = ENNReal.ofReal (∑' n, 2 * (e * (1/2)^(n+2))) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm).symm
          _ = ENNReal.ofReal e := by rw [hval]
          _ = εE := by rw [he_def, ENNReal.ofReal_toReal hεEtop]
      set W : ℕ → Set ℂ := fun n => Metric.thickening (δ n) (t n) with hW_def
      have hWopen : ∀ n, IsOpen (W n) := fun n => Metric.isOpen_thickening
      have htsubW : ∀ n, t n ⊆ W n := fun n => Metric.self_subset_thickening (hδpos n) (t n)
      have hKW : Kc ⊆ ⋃ n, W n := htcov.trans (iUnion_mono (fun n => htsubW n))
      set B : ℕ → ℝ≥0∞ := fun n => Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) with hB_def
      have hWdiam : ∀ n, Metric.ediam (W n) ≤ B n := by
        intro n; apply Metric.ediam_le
        intro x hx y hy
        rw [hW_def] at hx hy; simp only [Metric.mem_thickening_iff] at hx hy
        obtain ⟨x', hx', hxx'⟩ := hx
        obtain ⟨y', hy', hyy'⟩ := hy
        have hstep : edist x y ≤ (edist x x' + edist x' y') + edist y' y := by
          refine (edist_triangle x y' y).trans ?_; gcongr; exact edist_triangle x x' y'
        refine hstep.trans ?_
        have h1 : edist x x' ≤ ENNReal.ofReal (δ n) := by
          rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hxx'.le
        have h2 : edist x' y' ≤ Metric.ediam (t n) := Metric.edist_le_ediam_of_mem hx' hy'
        have h3 : edist y' y ≤ ENNReal.ofReal (δ n) := by
          rw [edist_dist, dist_comm]; exact ENNReal.ofReal_le_ofReal hyy'.le
        rw [hB_def]; simp only
        calc (edist x x' + edist x' y') + edist y' y
            ≤ (ENNReal.ofReal (δ n) + Metric.ediam (t n)) + ENNReal.ofReal (δ n) := by gcongr
          _ = Metric.ediam (t n) + (ENNReal.ofReal (δ n) + ENNReal.ofReal (δ n)) := by ring
          _ = Metric.ediam (t n) + ENNReal.ofReal (2 * δ n) := by
              rw [← ENNReal.ofReal_add (hδpos n).le (hδpos n).le]; ring_nf
      have hBsmall : ∀ n, B n ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
        intro n; rw [hB_def]; simp only
        have hle1 : Metric.ediam (t n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := htsmall n
        have hle2 : ENNReal.ofReal (2 * δ n) ≤ (2*((k:ℝ≥0∞)+1))⁻¹ := by
          have hd : (2 * δ n) ≤ 1/(2*((k:ℝ)+1)) := by
            have := hδle n; rw [le_div_iff₀ (by positivity)] at this ⊢; nlinarith
          refine (ENNReal.ofReal_le_ofReal hd).trans ?_
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_mul (by norm_num)]
          rw [show ENNReal.ofReal ((k:ℝ)+1) = (k:ℝ≥0∞)+1 by
                rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; norm_num,
              show ENNReal.ofReal 2 = (2:ℝ≥0∞) by norm_num, one_div]
        calc Metric.ediam (t n) + ENNReal.ofReal (2 * δ n)
            ≤ (2*((k:ℝ≥0∞)+1))⁻¹ + (2*((k:ℝ≥0∞)+1))⁻¹ := by gcongr
          _ = ((k:ℝ≥0∞)+1)⁻¹ := by
              rw [← two_mul, ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
                  ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      have hcovP : ∀ z ∈ Kc, ∃ p : ℕ × ℚ, z ∈ ball' p ∧ ∃ n, ball' p ⊆ W n := by
        intro z hz
        obtain ⟨n, hn⟩ : ∃ n, z ∈ W n := by have := hKW hz; rwa [mem_iUnion] at this
        obtain ⟨p, hzp, hpW⟩ := hsel z (W n) (hWopen n) hn
        exact ⟨p, hzp, n, hpW⟩
      choose! pp hzpp hnpp using hcovP
      obtain ⟨T, hTsub, hTfin, hTcov⟩ := hKc.elim_finite_subcover_image
        (b := Kc) (c := fun z => ball' (pp z)) (fun z _ => hballopen (pp z))
        (by intro z hz; rw [mem_iUnion₂]; exact ⟨z, hz, hzpp z hz⟩)
      set Tf := hTfin.toFinset with hTf
      set P : Finset (ℕ × ℚ) := Tf.image pp with hP
      have hPprop : ∀ p ∈ P, ∃ n, ball' p ⊆ W n := by
        intro p hp; rw [hP, Finset.mem_image] at hp
        obtain ⟨z, hzT, rfl⟩ := hp
        exact hnpp z (hTsub (by rw [hTf, Set.Finite.mem_toFinset] at hzT; exact hzT))
      choose! ν hν using hPprop
      have hKcovP : Kc ⊆ ⋃ p ∈ P, ball' p := by
        intro z hz
        have := hTcov hz; rw [mem_iUnion₂] at this
        obtain ⟨w, hwT, hzw⟩ := this
        rw [mem_iUnion₂]; refine ⟨pp w, ?_, hzw⟩
        rw [hP, Finset.mem_image]; exact ⟨w, by rw [hTf, Set.Finite.mem_toFinset]; exact hwT, rfl⟩
      have hνW : ∀ p ∈ P, ball' p ⊆ W (ν p) := fun p hp => hν p hp
      set grp : ℕ → Finset (ℕ × ℚ) := fun n => P.filter (fun p => ν p = n) with hgrp
      set S : Finset (Finset (ℕ × ℚ)) := (P.image ν).image grp with hS
      have hgrpW : ∀ n, elem (grp n) ⊆ W n := by
        intro n; rw [helem]; refine iUnion₂_subset ?_; intro p hp
        rw [hgrp, Finset.mem_filter] at hp; rw [← hp.2]; exact hνW p hp.1
      have hgrpdiam : ∀ n, Metric.ediam (elem (grp n)) ≤ B n := fun n =>
        (Metric.ediam_mono (hgrpW n)).trans (hWdiam n)
      have hScover : Kc ⊆ scover S := by
        rw [hscover]
        refine hKcovP.trans ?_
        intro z hz; rw [mem_iUnion₂] at hz; obtain ⟨p, hp, hzp⟩ := hz
        rw [mem_iUnion₂]; refine ⟨grp (ν p), ?_, ?_⟩
        · rw [hS, Finset.mem_image]; exact ⟨ν p, Finset.mem_image_of_mem ν hp, rfl⟩
        · rw [helem, mem_iUnion₂]; exact ⟨p, by rw [hgrp, Finset.mem_filter]; exact ⟨hp, rfl⟩, hzp⟩
      have hSsmall : ∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹ := by
        intro s hs; rw [hS, Finset.mem_image] at hs
        obtain ⟨n, hn, rfl⟩ := hs; exact (hgrpdiam n).trans (hBsmall n)
      have hGle : G k c ≤ scost S := by
        rw [hG]; simp only
        refine iInf_le_of_le S ?_
        rw [hGterm]; simp only; rw [if_pos ⟨hSsmall, hScover⟩]
      refine hGle.trans ?_
      have himg : scost S
          ≤ ∑ n ∈ P.image ν,
              (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) := by
        rw [hscost, hS, ← Finset.sum_fiberwise_of_maps_to (g := grp) (t := (P.image ν).image grp)
              (fun n hn => Finset.mem_image_of_mem grp hn)]
        apply Finset.sum_le_sum; intro s hs
        obtain ⟨n0, hn0T, hn0⟩ := Finset.mem_image.1 hs
        have hmem : n0 ∈ (P.image ν).filter (fun n => grp n = s) := Finset.mem_filter.2 ⟨hn0T, hn0⟩
        calc (⨆ _ : (elem s).Nonempty, Metric.ediam (elem s) ^ (1:ℝ))
            = (⨆ _ : (elem (grp n0)).Nonempty, Metric.ediam (elem (grp n0)) ^ (1:ℝ)) := by rw [hn0]
          _ ≤ ∑ n ∈ (P.image ν).filter (fun n => grp n = s),
                (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) :=
              Finset.single_le_sum
                (f := fun n => ⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
                (fun _ _ => zero_le _) hmem
      have hstep2 :
          ∑ n ∈ P.image ν, (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ))
            ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
                + ENNReal.ofReal (2 * δ n)) := by
        apply Finset.sum_le_sum; intro n _
        have hb : (⨆ _ : (elem (grp n)).Nonempty, Metric.ediam (elem (grp n)) ^ (1:ℝ)) ≤ B n := by
          refine iSup_le (fun _ => ?_); rw [ENNReal.rpow_one]; exact hgrpdiam n
        refine hb.trans ?_
        rw [hB_def]; simp only; gcongr
        by_cases h : (t n).Nonempty
        · rw [ciSup_pos h, ENNReal.rpow_one]
        · rw [not_nonempty_iff_eq_empty] at h; rw [h]; simp
      calc scost S
          ≤ ∑ n ∈ P.image ν, ((⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ))
              + ENNReal.ofReal (2 * δ n)) := himg.trans hstep2
        _ = (∑ n ∈ P.image ν, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)))
              + ∑ n ∈ P.image ν, ENNReal.ofReal (2 * δ n) := Finset.sum_add_distrib
        _ ≤ (∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (1:ℝ)) + εE :=
              add_le_add (ENNReal.sum_le_tsum _) ((ENNReal.sum_le_tsum _).trans hδsum)
    -- assemble identity
    refine ⟨le_antisymm ?_ ?_, hB_dir⟩
    · rw [hHA]; refine iSup₂_le ?_; intro r hr
      obtain ⟨k, hkr⟩ : ∃ k : ℕ, ((k:ℝ≥0∞)+1)⁻¹ ≤ r := by
        rcases eq_or_ne r ∞ with rfl | hrtop
        · exact ⟨0, le_top⟩
        · obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (a := r) hr.ne'
          exact ⟨k, (ENNReal.inv_le_inv.2 le_self_add).trans hk.le⟩
      calc content c r ≤ content c ((k:ℝ≥0∞)+1)⁻¹ := hcontent_anti _ _ hkr
        _ ≤ G k c := hA_dir k
        _ ≤ ⨆ k, G k c := le_iSup (fun k => G k c) k
    · refine iSup_le ?_; intro k
      calc G k c ≤ content c (2*((k:ℝ≥0∞)+1))⁻¹ := hB_dir k
        _ ≤ μH[(1:ℝ)] Kc := by
            rw [hHA]; refine le_iSup₂_of_le (2*((k:ℝ≥0∞)+1))⁻¹ ?_ le_rfl
            rw [ENNReal.inv_pos]
            exact ENNReal.mul_ne_top (by norm_num)
              (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, by norm_num⟩)
  -- ============================================================
  -- MCT + per-scale covering bound.
  -- ============================================================
  have hGmono : Monotone G := by
    intro k k' hkk' c
    rw [hG]; simp only
    refine le_iInf fun S => ?_
    have hkey2 : Gterm k S c ≤ Gterm k' S c := by
      rw [hGterm]; simp only
      by_cases hv' : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k':ℝ≥0∞)+1)⁻¹)
          ∧ g ⁻¹' {c} ∩ A ⊆ scover S
      · have hv : (∀ s ∈ S, Metric.ediam (elem s) ≤ ((k:ℝ≥0∞)+1)⁻¹)
            ∧ g ⁻¹' {c} ∩ A ⊆ scover S := by
          refine ⟨fun s hs => (hv'.1 s hs).trans ?_, hv'.2⟩
          apply ENNReal.inv_le_inv.2
          gcongr
        rw [if_pos hv, if_pos hv']
      · rw [if_neg hv']; exact le_top
    exact (iInf_le _ S).trans hkey2
  rw [show (fun c => μH[(1:ℝ)] (g ⁻¹' {c} ∩ A)) = fun c => ⨆ k, G k c from
        funext (fun c => (hkey c).1)]
  rw [lintegral_iSup hGmeas hGmono]
  refine iSup_le (fun k => ?_)
  set r' : ℝ≥0∞ := (2*((k:ℝ≥0∞)+1))⁻¹ with hr'_def
  have hr'pos : 0 < r' := by
    rw [hr'_def, ENNReal.inv_pos]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top k, by norm_num⟩)
  set content2f : ℝ≥0∞ → ℝ≥0∞ := fun r =>
    ⨅ t : ℕ → Set ℂ, if (A ⊆ ⋃ n, t n) ∧ (∀ n, Metric.ediam (t n) ≤ r)
      then ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (2:ℝ) else ⊤ with hcontent2f
  have hcontent2f_le : content2f r' ≤ μH[(2:ℝ)] A := by
    rw [Measure.hausdorffMeasure_apply]
    refine le_iSup₂_of_le r' hr'pos ?_
    refine le_iInf fun t => le_iInf fun htcov => le_iInf fun htsmall => ?_
    rw [hcontent2f]; simp only
    refine iInf_le_of_le t ?_
    rw [if_pos ⟨htcov, htsmall⟩]
  have hKne : (K : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hKzero : (K : ℝ≥0∞) ≠ 0 := by
    simpa only [ne_eq, ENNReal.coe_eq_zero] using hKne0
  have hbound : ∫⁻ c, G k c ≤ (K : ℝ≥0∞) * content2f r' := by
    rw [hcontent2f, ENNReal.mul_iInf_of_ne hKzero hKne]
    refine le_iInf fun t => ?_
    by_cases hcov : (A ⊆ ⋃ n, t n) ∧ (∀ n, Metric.ediam (t n) ≤ r')
    · rw [if_pos hcov]
      obtain ⟨htcov, htsmall⟩ := hcov
      set F : ℕ → ℝ → ℝ≥0∞ :=
        fun n c => (g '' (A ∩ closure (t n))).indicator (fun _ => Metric.ediam (t n)) c with hF_def
      have hAclos : ∀ n, IsCompact (A ∩ closure (t n)) := fun n => hA.inter_right isClosed_closure
      have hFimg_meas : ∀ n, MeasurableSet (g '' (A ∩ closure (t n))) :=
        fun n => ((hAclos n).image hgcont).measurableSet
      have hFmeas : ∀ n, Measurable (F n) := by
        intro n; rw [hF_def]; exact Measurable.indicator measurable_const (hFimg_meas n)
      have hptwise : ∀ c, G k c ≤ ∑' n, F n c := by
        intro c
        have hGle : G k c ≤ content c r' := (hkey c).2 k
        refine hGle.trans ?_
        rw [hcontent]
        set t'' : ℕ → Set ℂ :=
          fun n => if c ∈ g '' (A ∩ closure (t n)) then closure (t n) else ∅ with ht''_def
        have ht''cov : (g ⁻¹' {c} ∩ A) ⊆ ⋃ n, t'' n := by
          intro z hz
          obtain ⟨hzc, hzA⟩ := hz
          have hzU : z ∈ ⋃ n, t n := htcov hzA
          rw [mem_iUnion] at hzU; obtain ⟨n, hzn⟩ := hzU
          rw [mem_iUnion]; refine ⟨n, ?_⟩
          have hzclos : z ∈ closure (t n) := subset_closure hzn
          have hcimg : c ∈ g '' (A ∩ closure (t n)) := by
            refine ⟨z, ⟨hzA, hzclos⟩, ?_⟩
            simpa [mem_preimage, mem_singleton_iff] using hzc
          rw [ht''_def]; simp only; rw [if_pos hcimg]; exact hzclos
        have ht''small : ∀ n, Metric.ediam (t'' n) ≤ r' := by
          intro n; rw [ht''_def]; simp only
          by_cases hc : c ∈ g '' (A ∩ closure (t n))
          · rw [if_pos hc, Metric.ediam_closure]; exact htsmall n
          · rw [if_neg hc]; simp
        calc (⨅ (t' : ℕ → Set ℂ) (_ : (g ⁻¹' {c} ∩ A) ⊆ ⋃ n, t' n)
                  (_ : ∀ n, Metric.ediam (t' n) ≤ r'),
                ∑' n, ⨆ _ : (t' n).Nonempty, Metric.ediam (t' n) ^ (1:ℝ))
            ≤ ∑' n, ⨆ _ : (t'' n).Nonempty, Metric.ediam (t'' n) ^ (1:ℝ) :=
              iInf_le_of_le t'' (iInf_le_of_le ht''cov (iInf_le_of_le ht''small le_rfl))
          _ ≤ ∑' n, F n c := by
              apply ENNReal.tsum_le_tsum; intro n
              change (⨆ _ : (t'' n).Nonempty, Metric.ediam (t'' n) ^ (1:ℝ))
                ≤ (g '' (A ∩ closure (t n))).indicator (fun _ => Metric.ediam (t n)) c
              by_cases hc : c ∈ g '' (A ∩ closure (t n))
              · rw [indicator_of_mem hc]
                have htt : t'' n = closure (t n) := by
                  rw [ht''_def]; simp only; rw [if_pos hc]
                rw [htt, Metric.ediam_closure]
                refine iSup_le (fun _ => ?_); rw [ENNReal.rpow_one]
              · have htt : t'' n = ∅ := by
                  rw [ht''_def]; simp only; rw [if_neg hc]
                rw [htt]; simp
      calc ∫⁻ c, G k c
          ≤ ∫⁻ c, ∑' n, F n c := lintegral_mono hptwise
        _ = ∑' n, ∫⁻ c, F n c :=
            lintegral_tsum (fun n => (hFmeas n).aemeasurable)
        _ ≤ ∑' n, (K : ℝ≥0∞) * ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (2:ℝ) := by
            apply ENNReal.tsum_le_tsum; intro n
            change ∫⁻ c, (g '' (A ∩ closure (t n))).indicator (fun _ => Metric.ediam (t n)) c ≤ _
            rw [lintegral_indicator_const (hFimg_meas n)]
            have hvol : volume (g '' (A ∩ closure (t n))) ≤ (K : ℝ≥0∞) * Metric.ediam (t n) := by
              calc volume (g '' (A ∩ closure (t n)))
                  ≤ Metric.ediam (g '' (A ∩ closure (t n))) := Real.volume_le_diam _
                _ ≤ (K : ℝ≥0∞) * Metric.ediam (A ∩ closure (t n)) :=
                    hgLip.ediam_image_le _
                _ ≤ (K : ℝ≥0∞) * Metric.ediam (t n) := by
                    have hdle : Metric.ediam (A ∩ closure (t n)) ≤ Metric.ediam (t n) :=
                      (Metric.ediam_mono inter_subset_right).trans_eq (Metric.ediam_closure (t n))
                    gcongr
            by_cases hne : (t n).Nonempty
            · rw [ciSup_pos hne]
              calc Metric.ediam (t n) * volume (g '' (A ∩ closure (t n)))
                  ≤ Metric.ediam (t n) * ((K : ℝ≥0∞) * Metric.ediam (t n)) := by gcongr
                _ = (K : ℝ≥0∞) * (Metric.ediam (t n) * Metric.ediam (t n)) := by ring
                _ = (K : ℝ≥0∞) * Metric.ediam (t n) ^ (2:ℝ) := by
                    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, sq]
            · rw [not_nonempty_iff_eq_empty] at hne
              rw [hne]
              simp only [closure_empty, inter_empty, image_empty, measure_empty, mul_zero]
              exact zero_le _
        _ = (K : ℝ≥0∞) * ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (2:ℝ) :=
            ENNReal.tsum_mul_left
    · rw [if_neg hcov, ENNReal.mul_top hKzero]; exact le_top
  calc ∫⁻ c, G k c
      ≤ (K : ℝ≥0∞) * content2f r' := hbound
    _ ≤ (K : ℝ≥0∞) * μH[(2:ℝ)] A := by gcongr

/-- **`μH[2]` is a positive multiple of `volume` on `ℂ` (the TRUE normalization fact).**

The 2-dimensional Hausdorff measure on the complex plane (with its Euclidean / L2 metric) is a
strictly positive scalar multiple of the canonical planar Lebesgue measure `volume`:
`μH[2] = c • volume` for some `c : ℝ≥0`, `0 < c`.

## Truth and direction

**TRUE** (proportionality, NOT equality). Mathlib's `μH[d]` is the *raw* Hausdorff measure
(`diam ^ d`, with no normalizing constant). On `ℂ`'s Euclidean (L2) metric the raw `μH[2]` is
**not** `volume`: the exact factor is `4/π` (only the sup metric gives `μH[2] = volume`, cf.
`MeasureTheory.hausdorffMeasure_pi_real`). What *is* true and all that is needed downstream is the
**proportionality** `μH[2] = c • volume` with `c > 0`.

## Proof

`ℂ` is a 2-dimensional real inner product space (`Complex.finrank_real_complex`), and
`InnerProductSpace.euclideanHausdorffMeasure_eq_volume` gives `μHE[finrank ℝ ℂ] = volume`, i.e.
`μHE[2] = volume`. By `Measure.euclideanHausdorffMeasure_def`, `μHE[2] = k • μH[2]` where
`k := addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[2]`, which is nonzero by
`Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero`. Hence `volume = k • μH[2]`, so
`μH[2] = k⁻¹ • volume`; take `c = k⁻¹ > 0`. The exact value `c = π/4` rests on a Mathlib
`proof_wanted` (`addHaarScalarFactor_hausdorffMeasure_eq`), so only proportionality is asserted. -/
theorem hausdorffMeasure_two_complex_smul_volume :
    ∃ c : ℝ≥0, 0 < c ∧ (μH[2] : Measure ℂ) = c • volume := by
  -- `μHE[finrank ℝ ℂ] = volume` on the inner product space `ℂ`.
  have hvol : (μHE[Module.finrank ℝ ℂ] : Measure ℂ) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [Complex.finrank_real_complex] at hvol
  -- Unfold the definition `μHE[2] = k • μH[2]`.
  rw [Measure.euclideanHausdorffMeasure_def] at hvol
  set k : ℝ≥0 :=
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).addHaarScalarFactor μH[(2 : ℕ)] with hk_def
  have hk0 : k ≠ 0 := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero 2
  -- Reconcile the `ℕ`-cast index `μH[(↑2 : ℝ)]` with the statement's `μH[(2 : ℝ)]`.
  have hcast : (μH[((2 : ℕ) : ℝ)] : Measure ℂ) = (μH[(2 : ℝ)] : Measure ℂ) := by norm_num
  rw [hcast] at hvol
  -- Now `hvol : k • μH[2] = volume`; invert `k` to get `μH[2] = k⁻¹ • volume`.
  refine ⟨k⁻¹, inv_pos.mpr (pos_iff_ne_zero.mpr hk0), ?_⟩
  calc (μH[2] : Measure ℂ)
      = (1 : ℝ≥0) • (μH[2] : Measure ℂ) := (one_smul _ _).symm
    _ = (k⁻¹ * k) • (μH[2] : Measure ℂ) := by rw [inv_mul_cancel₀ hk0]
    _ = k⁻¹ • (k • (μH[2] : Measure ℂ)) := (smul_smul k⁻¹ k (μH[2] : Measure ℂ)).symm
    _ = k⁻¹ • volume := by rw [hvol]

/-! ## The gradient-weighted (sharp) planar co-area inequality

The Lipschitz-constant forms above are derived corollaries; the genuine Eilenberg inequality
replaces the constant `K` by the *pointwise* gradient norm `‖∇u‖`. This sharp form is what the
length–area lower bound consumes: it lets the eikonal bound `‖∇u‖ ≤ ρ` transfer the
gradient-energy integral `∫ ρ σ` down to the integrated level sets. -/

/-- **Linear co-area equality on ℂ (the affine model for the sharp co-area inequality).**

For a continuous `ℝ`-linear functional `L : ℂ →L[ℝ] ℝ` and a measurable set `B ⊆ ℂ`, the integrated
arc-length (`μH[1]`) of the level lines of `L` meeting `B` equals `‖L‖` times the area of `B`:

`∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B) ∂volume = (‖L‖₊ : ℝ≥0∞) * volume B`.

This is the **exact** co-area identity for the *affine* (here linear) case: the level sets
`L ⁻¹' {c}` are parallel lines, and Fubini in coordinates aligned with `L` evaluates the integral to
`‖L‖ · area`. It is the local model on which the sharp Lipschitz co-area inequality
`eilenberg_coarea_grad_le` is built by Rademacher/Besicovitch localization: on a small ball around a
point of differentiability, `u` is within `o(r)` of its linearization `L = fderiv ℝ u`, and this
identity supplies the leading term `‖L‖ · vol`.

## Truth and direction

**TRUE** (equality). For `L = 0` both sides are `0` (the left integrand is supported on the single
point `c = 0`, a `volume`-null set in `ℝ`). For `L ≠ 0`, rotate ℂ by a linear isometry sending the
unit normal of `L` to the real axis; isometries preserve `μH[1]`, `volume`, and `‖L‖`, reducing to
`L (x + i y) = ‖L‖ · x`, where `L ⁻¹' {c} ∩ B` is the vertical slice `{c/‖L‖} ×ℂ B_{c/‖L‖}`, whose
`μH[1]` is `volume` of the fiber (the vertical embedding `y ↦ ⟨c/‖L‖, y⟩` is an isometry,
`MeasureTheory.hausdorffMeasure_real`), and Fubini (`lintegral_lintegral` / `Measure.prod`) together
with the substitution `c = ‖L‖ · t` gives
`∫⁻ c, volume (fiber at c/‖L‖) = ‖L‖ · ∫⁻ t, volume (fiber at t) = ‖L‖ · volume B`. -/
theorem coarea_linear_eq (L : ℂ →L[ℝ] ℝ) {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B) = (‖L‖₊ : ℝ≥0∞) * volume B := by
  -- Case `L = 0`: the integrand is supported on the single point `c = 0`, a null set in `ℝ`.
  rcases eq_or_ne L 0 with hL0 | hL0
  · subst hL0
    rw [nnnorm_zero]
    simp only [ENNReal.coe_zero, zero_mul]
    have hint : (fun c : ℝ => μH[1] ((0 : ℂ →L[ℝ] ℝ) ⁻¹' {c} ∩ B))
        = Set.indicator {0} (fun _ => μH[1] B) := by
      ext c
      by_cases hc : c = 0
      · subst hc
        rw [indicator_of_mem (by simp)]
        congr 1
        rw [Set.inter_eq_right]
        intro z _
        simp [ContinuousLinearMap.zero_apply]
      · rw [indicator_of_notMem (by simp [hc])]
        have hempty : (0 : ℂ →L[ℝ] ℝ) ⁻¹' {c} = ∅ := by
          ext z; simp [ContinuousLinearMap.zero_apply, eq_comm, hc]
        rw [hempty, Set.empty_inter, measure_empty]
    rw [hint, lintegral_indicator (measurableSet_singleton 0), setLIntegral_const,
      Real.volume_singleton, mul_zero]
  -- Case `L ≠ 0`: rotate so `L` becomes `‖L‖ • re`, then slice and apply Fubini.
  · -- Riesz vector `v` with `L w = ⟪v, w⟫` and `‖v‖ = ‖L‖`.
    set v := (InnerProductSpace.toDual ℝ ℂ).symm L with hv_def
    have hLnorm : ‖v‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
    have hv : v ≠ 0 := by
      intro h
      apply hL0
      have hLeq : L = (InnerProductSpace.toDual ℝ ℂ) v := by
        rw [hv_def, LinearIsometryEquiv.apply_symm_apply]
      rw [hLeq, h, map_zero]
    have hLpos : 0 < ‖L‖ := by rw [← hLnorm]; positivity
    have hLne : ‖L‖ ≠ 0 := ne_of_gt hLpos
    have hriesz : ∀ z : ℂ, L z = inner ℝ v z := fun z => by
      rw [hv_def]; exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
    -- The rotation: multiplication by the unit `v / ‖v‖`.
    have hmem : v / (‖v‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm,
        div_self (by rw [Ne, norm_eq_zero]; exact hv)]
    set a : Circle := ⟨v / (‖v‖ : ℂ), hmem⟩ with ha_def
    have hrot : ∀ w : ℂ, L (rotation a w) = ‖L‖ * w.re := by
      intro w
      rw [rotation_apply]
      change L (((⟨v / (‖v‖ : ℂ), hmem⟩ : Circle) : ℂ) * w) = ‖L‖ * w.re
      rw [hriesz, Complex.inner]
      have hvn : (‖v‖ : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact hv
      have key : v * (starRingEnd ℂ) v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have heq : ((v / (‖v‖ : ℂ)) * w) * (starRingEnd ℂ) v = w * (‖v‖ : ℂ) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hvn]
        rw [show v * w * (starRingEnd ℂ) v = w * (v * (starRingEnd ℂ) v) by ring, key]
        push_cast; ring
      change (((v / (‖v‖ : ℂ)) * w) * (starRingEnd ℂ) v).re = ‖L‖ * w.re
      rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hLnorm]
      ring
    -- Replace `B` by the rotated set `B'`.
    set B' : Set ℂ := rotation a ⁻¹' B with hB'_def
    have hB'meas : MeasurableSet B' := (rotation a).continuous.measurable hB
    have hvolB : volume B' = volume B := by
      have hmp : MeasurePreserving (rotation a) (volume : Measure ℂ) volume :=
        LinearIsometryEquiv.measurePreserving (rotation a)
      exact hmp.measure_preimage hB.nullMeasurableSet
    -- Reduce each level-set measure to the rotated slice.
    have stepA : ∀ c : ℝ,
        μH[(1:ℝ)] (L ⁻¹' {c} ∩ B) = μH[1] ({w : ℂ | ‖L‖ * w.re = c} ∩ B') := by
      intro c
      have hLmeas : MeasurableSet (L ⁻¹' {c} ∩ B) :=
        ((L.continuous.measurable (measurableSet_singleton c))).inter hB
      have hmp := IsometryEquiv.measurePreserving_hausdorffMeasure
        (rotation a).toIsometryEquiv (1:ℝ)
      rw [← hmp.measure_preimage hLmeas.nullMeasurableSet]
      congr 1
      ext w
      have hcoe : (rotation a).toIsometryEquiv w = rotation a w := rfl
      simp only [mem_preimage, mem_inter_iff, mem_singleton_iff, mem_setOf_eq, hcoe, hB'_def]
      rw [hrot w]
    -- Each vertical slice's `μH[1]` is the fiber `volume`.
    have stepB : ∀ c : ℝ,
        μH[(1:ℝ)] ({w : ℂ | ‖L‖ * w.re = c} ∩ B')
          = volume {y : ℝ | Complex.mk (c / ‖L‖) y ∈ B'} := by
      intro c
      have hset : {w : ℂ | ‖L‖ * w.re = c} = {w : ℂ | w.re = c / ‖L‖} := by
        ext w; simp only [mem_setOf_eq]; rw [eq_div_iff hLne, mul_comm]
      rw [hset]
      have hiso : Isometry (fun y : ℝ => Complex.mk (c / ‖L‖) y) := by
        intro y1 y2
        simp only [edist_dist, Complex.dist_eq, Real.dist_eq]
        congr 1
        rw [Complex.norm_eq_sqrt_sq_add_sq]
        simp only [Complex.sub_re, Complex.sub_im, sub_self]
        rw [zero_pow (by norm_num), zero_add, Real.sqrt_sq_eq_abs]
      have himgeq : {w : ℂ | w.re = c / ‖L‖} ∩ B'
          = (fun y : ℝ => Complex.mk (c / ‖L‖) y) ''
            {y | Complex.mk (c / ‖L‖) y ∈ B'} := by
        ext w
        simp only [mem_inter_iff, mem_setOf_eq, mem_image]
        constructor
        · rintro ⟨hre, hBmem⟩
          refine ⟨w.im, ?_, ?_⟩
          · show Complex.mk (c / ‖L‖) w.im ∈ B'
            have hweq : Complex.mk (c / ‖L‖) w.im = w := by apply Complex.ext <;> simp [hre]
            rw [hweq]; exact hBmem
          · apply Complex.ext <;> simp [hre]
        · rintro ⟨y, hy, rfl⟩
          exact ⟨by simp, hy⟩
      rw [himgeq, hiso.hausdorffMeasure_image (Or.inl (by norm_num)),
        MeasureTheory.hausdorffMeasure_real]
    -- The fiber `volume` is measurable in the slice parameter.
    have hgmeas : Measurable (fun s : ℝ => volume {y : ℝ | Complex.mk s y ∈ B'}) := by
      have hSmeas : MeasurableSet (Complex.measurableEquivRealProd.symm ⁻¹' B') :=
        Complex.measurableEquivRealProd.symm.measurable hB'meas
      exact measurable_measure_prodMk_left (α := ℝ) (ν := (volume : Measure ℝ)) hSmeas
    -- Assemble: rewrite the integral, scale, then apply Fubini.
    calc ∫⁻ c, μH[1] (L ⁻¹' {c} ∩ B)
        = ∫⁻ c, volume {y : ℝ | Complex.mk (c / ‖L‖) y ∈ B'} := by
          apply lintegral_congr; intro c; rw [stepA c, stepB c]
      _ = ENNReal.ofReal ‖L‖ * ∫⁻ s, volume {y : ℝ | Complex.mk s y ∈ B'} := by
          set g : ℝ → ℝ≥0∞ := fun s => volume {y : ℝ | Complex.mk s y ∈ B'}
            with hg_def
          change ∫⁻ c, g (c / ‖L‖) ∂(volume : Measure ℝ)
              = ENNReal.ofReal ‖L‖ * ∫⁻ s, g s ∂volume
          have hg2 : Measurable (fun c => g (c / ‖L‖)) :=
            hgmeas.comp (measurable_id.div_const ‖L‖)
          have hmapint2 : ∫⁻ x, g (x / ‖L‖) ∂(Measure.map ((‖L‖ : ℝ) * ·) volume)
              = ∫⁻ y, g ((‖L‖ * y) / ‖L‖) ∂volume :=
            lintegral_map hg2 (measurable_const_mul ‖L‖)
          rw [Real.map_volume_mul_left hLne, lintegral_smul_measure,
            abs_of_pos (inv_pos.mpr hLpos)] at hmapint2
          have heq2 : (fun y => g ((‖L‖ * y) / ‖L‖)) = g := by
            ext y; rw [mul_comm (‖L‖) y, mul_div_assoc, div_self hLne, mul_one]
          rw [heq2, smul_eq_mul] at hmapint2
          rw [← hmapint2, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hLpos),
            mul_inv_cancel₀ hLne, ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal ‖L‖ * volume B' := by
          congr 1
          have hmp : MeasurePreserving Complex.measurableEquivRealProd
              (volume : Measure ℂ) volume :=
            Complex.volume_preserving_equiv_real_prod
          have hmps : MeasurePreserving Complex.measurableEquivRealProd.symm
              (volume : Measure (ℝ × ℝ)) volume := hmp.symm _
          have hSmeas : MeasurableSet (Complex.measurableEquivRealProd.symm ⁻¹' B') :=
            Complex.measurableEquivRealProd.symm.measurable hB'meas
          have hvolS : volume (Complex.measurableEquivRealProd.symm ⁻¹' B') = volume B' :=
            hmps.measure_preimage hB'meas.nullMeasurableSet
          rw [← hvolS, show (volume : Measure (ℝ × ℝ))
              = (volume : Measure ℝ).prod volume from Measure.volume_eq_prod ℝ ℝ,
            Measure.prod_apply hSmeas]
          apply lintegral_congr
          intro s
          congr 1
      _ = (‖L‖₊ : ℝ≥0∞) * volume B := by
          rw [hvolB]
          congr 1
          exact ((ENNReal.ofReal_coe_nnreal).symm.trans (by rw [coe_nnnorm])).symm

open scoped Pointwise in
/-- **Arc-length bound for a differentiable curve (the `≤` fiber length, area-formula route).**

For a curve `γ : ℝ → ℂ` that is differentiable on a measurable set `I` with derivative `γ'`, the
`1`-dimensional Hausdorff measure of its image is bounded by the integral of its speed:

`μH[1] (γ '' I) ≤ ∫⁻ t in I, ‖γ' t‖₊`.

This is the `≤` ("length `≤` `∫` speed") direction of the 1-D area formula — no injectivity needed.
It is the fiber-length ingredient of the area-formula proof of the sharp co-area inequality: applied
to the level-curve parametrization `γ_c = Φ⁻¹(c, ·)` of `Φ = (u, ℓ)` on an injective piece, it turns
`μH[1] (u ⁻¹' {c} ∩ S)` into a fiber integral that Fubini + the area formula
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) convert to `∫⁻ z in S, ‖∇u z‖`.

## Truth and proof

**TRUE**, `≤`. Standard: cover `I` by countably many small pieces on each of which `γ` is, up to
`o`, affine with slope `γ' t₀`, so `μH[1] (γ '' piece) ≤ (‖γ' t₀‖ + ε) · volume piece` (via
`LipschitzOnWith.hausdorffMeasure_image_le` with the local Lipschitz constant), and sum.
Equivalently `μH[1] (γ '' I) ≤ eVariationOn γ I ≤ ∫⁻ I ‖γ'‖` (image Hausdorff measure `≤` the
variation, which for a curve with derivative `γ'` is `≤ ∫ ‖γ'‖`). `γ'` is measurable as an a.e.
derivative of the continuous `γ`. -/
theorem hausdorffMeasure_one_image_le {γ γ' : ℝ → ℂ} {I : Set ℝ}
    (hI : MeasurableSet I) (hγ' : ∀ t ∈ I, HasDerivWithinAt γ (γ' t) I t) :
    μH[1] (γ '' I) ≤ ∫⁻ t in I, (‖γ' t‖₊ : ℝ≥0∞) := by
  classical
  -- The Frechet derivative associated to `deriv γ' x` is `smulRight 1 (γ' x)`, of norm `‖γ' x‖`;
  -- `HasDerivWithinAt` is definitionally `HasFDerivWithinAt` with this `f'`.
  set f' : ℝ → (ℝ →L[ℝ] ℂ) := fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (γ' x) with hf'def
  have hfd : ∀ x ∈ I, HasFDerivWithinAt γ (f' x) I x := fun x hx => hγ' x hx
  have hnorm : ∀ x, ‖f' x‖₊ = ‖γ' x‖₊ := by
    intro x
    apply NNReal.coe_injective
    simp only [hf'def, coe_nnnorm, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
  -- KEY 1: the analogue of `ApproximatesLinearOn.norm_fderiv_sub_le` for `A : ℝ →L[ℝ] ℂ`.
  -- Mathlib's lemma is stated only for square maps `E →L[ℝ] E`; its proof (Lebesgue density
  -- points + Besicovitch differentiation) is dimension-agnostic, so we replay it inline here.
  have nfsl : ∀ (A : ℝ →L[ℝ] ℂ) (δ : ℝ≥0) (s : Set ℝ),
      MeasurableSet s → ApproximatesLinearOn γ A s δ →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) →
      ∀ᵐ x ∂(volume : Measure ℝ).restrict s, ‖f' x - A‖₊ ≤ δ := by
    intro A δ s hs hf hfd_s
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) s,
      ae_restrict_mem hs]
    intro x hx xs
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
      have hT : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at hT
      apply le_of_tendsto_of_tendsto tendsto_const_nhds hT
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one (volume : Measure ℝ) s x hx _
        measurableSet_closedBall (Metric.measure_closedBall_pos (volume : Measure ℝ) z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, Metric.ball x ρ ∩ s ⊆ {y : ℝ | ‖γ y - γ x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      Metric.mem_nhdsWithin_iff.1 (((hfd_s x xs).isLittleO).def εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset Metric.isBounded_closedBall
        (Metric.ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
        ∃ r : ℝ, (s ∩ ({x} + r • Metric.closedBall z ε)).Nonempty ∧
          {x} + r • Metric.closedBall z ε ⊆ Metric.ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ Metric.closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have Iineq : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
            rw [map_smul, Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg rpos.le]
        _ = ‖γ y - γ x - A (y - x) - (γ y - γ x - (f' x) (y - x))‖ := by
            congr 1
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left,
              ContinuousLinearMap.coe_sub', Pi.sub_apply, map_smul]
            module
        _ ≤ ‖γ y - γ x - A (y - x)‖ + ‖γ y - γ x - (f' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
          congr 1
          simp only [ContinuousLinearMap.coe_sub', map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at Iineq; exact (mul_le_mul_iff_right₀ rpos).1 Iineq
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- KEY 2: a map approximated by `A` up to `δ` is `(‖A‖ + δ)`-Lipschitz, expanding `μH[1]` by
  -- at most that factor (the `d = 1` case of `LipschitzOnWith.hausdorffMeasure_image_le`).
  have expand : ∀ (A : ℝ →L[ℝ] ℂ) (δ : ℝ≥0) (t : Set ℝ),
      ApproximatesLinearOn γ A t δ →
      μH[1] (γ '' t) ≤ ((‖A‖₊ + δ : ℝ≥0) : ℝ≥0∞) * μH[1] t := by
    intro A δ t htg
    have hlip : LipschitzOnWith (‖A‖₊ + δ) γ t := by
      rw [lipschitzOnWith_iff_restrict]; exact htg.lipschitz
    calc μH[1] (γ '' t) ≤ ((‖A‖₊ + δ : ℝ≥0) : ℝ≥0∞) ^ (1 : ℝ) * μH[1] t :=
          hlip.hausdorffMeasure_image_le (by norm_num)
      _ = ((‖A‖₊ + δ : ℝ≥0) : ℝ≥0∞) * μH[1] t := by rw [ENNReal.rpow_one]
  -- On the source `ℝ`, `μH[1] = volume`.
  have hHvol : (μH[1] : Measure ℝ) = volume := hausdorffMeasure_real
  -- AUX1: the finite-error estimate, via a measurable partition on which `γ` is well approximated
  -- by linear maps (`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`).
  have aux1 : ∀ {s : Set ℝ}, MeasurableSet s →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) → ∀ {ε : ℝ≥0}, 0 < ε →
      μH[1] (γ '' s) ≤ (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * ε * (volume s) := by
    intro s hs hfds ε εpos
    obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hAy⟩ :
        ∃ (t : ℕ → Set ℝ) (A : ℕ → (ℝ →L[ℝ] ℂ)),
          Pairwise (Function.onFun Disjoint t) ∧
            (∀ n : ℕ, MeasurableSet (t n)) ∧
              (s ⊆ ⋃ n : ℕ, t n) ∧
                (∀ n : ℕ, ApproximatesLinearOn γ (A n) (s ∩ t n) ε) ∧
                  (s.Nonempty → ∀ n, ∃ y ∈ s, A n = f' y) :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt γ s f' hfds (fun _ => ε)
        (fun _ => εpos.ne')
    calc
      μH[1] (γ '' s) ≤ μH[1] (⋃ n, γ '' (s ∩ t n)) := by
        apply measure_mono
        rw [← image_iUnion, ← inter_iUnion]
        exact Set.image_mono (subset_inter Subset.rfl t_cover)
      _ ≤ ∑' n, μH[1] (γ '' (s ∩ t n)) := measure_iUnion_le _
      _ ≤ ∑' n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * μH[1] (s ∩ t n) := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        exact expand (A n) ε (s ∩ t n) (ht n)
      _ = ∑' n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) * volume (s ∩ t n) := by
        simp_rw [hHvol]
      _ = ∑' n, ∫⁻ _ in s ∩ t n, ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) := by
        simp only [setLIntegral_const]
      _ ≤ ∑' n, ∫⁻ x in s ∩ t n, ((‖γ' x‖₊ : ℝ≥0∞) + 2 * ε) := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        apply lintegral_mono_ae
        filter_upwards [nfsl (A n) ε (s ∩ t n) (hs.inter (t_meas n)) (ht n)
            (fun x hx => (hfds x hx.1).mono inter_subset_left)]
        intro x hx
        have hAle : (‖A n‖₊ : ℝ≥0) ≤ ‖γ' x‖₊ + ε := by
          calc (‖A n‖₊ : ℝ≥0) = ‖f' x - (f' x - A n)‖₊ := by rw [sub_sub_cancel]
            _ ≤ ‖f' x‖₊ + ‖f' x - A n‖₊ := nnnorm_sub_le _ _
            _ ≤ ‖f' x‖₊ + ε := by gcongr
            _ = ‖γ' x‖₊ + ε := by rw [hnorm]
        calc ((‖A n‖₊ + ε : ℝ≥0) : ℝ≥0∞) ≤ (((‖γ' x‖₊ + ε) + ε : ℝ≥0) : ℝ≥0∞) := by
              rw [ENNReal.coe_le_coe]; gcongr
          _ = (‖γ' x‖₊ : ℝ≥0∞) + 2 * ε := by push_cast; ring
      _ = ∫⁻ x in ⋃ n, s ∩ t n, ((‖γ' x‖₊ : ℝ≥0∞) + 2 * ε) := by
        rw [lintegral_iUnion (fun n => hs.inter (t_meas n))
          (pairwise_disjoint_mono t_disj fun n => inter_subset_right)]
      _ = ∫⁻ x in s, ((‖γ' x‖₊ : ℝ≥0∞) + 2 * ε) := by
        rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
      _ = (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * ε * (volume s) := by
        rw [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
  -- AUX2: let `ε → 0` for finite-measure sets.
  have aux2 : ∀ {s : Set ℝ}, MeasurableSet s → volume s ≠ ∞ →
      (∀ x ∈ s, HasFDerivWithinAt γ (f' x) s x) →
      μH[1] (γ '' s) ≤ ∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞) := by
    intro s hs hsfin hfds
    have hlim : Tendsto (fun ε : ℝ≥0 =>
        (∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * (ε : ℝ≥0∞) * (volume s)) (𝓝[>] 0)
        (𝓝 ((∫⁻ x in s, (‖γ' x‖₊ : ℝ≥0∞)) + 2 * (0 : ℝ≥0) * (volume s))) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      refine tendsto_const_nhds.add ?_
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hsfin)
      exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id) (Or.inr ENNReal.coe_ne_top)
    simp only [ENNReal.coe_zero, mul_zero, zero_mul, add_zero] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin]
    intro ε εpos
    rw [mem_Ioi] at εpos
    exact aux1 hs hfds εpos
  -- Reduce `I` to finite-measure disjoint pieces via the spanning sets of `volume`.
  set u : ℕ → Set ℝ := fun n => disjointed (spanningSets (volume : Measure ℝ)) n with hu_def
  have u_meas : ∀ n, MeasurableSet (u n) := fun n =>
    MeasurableSet.disjointed (fun i => measurableSet_spanningSets (volume : Measure ℝ) i) n
  have hIcover : I = ⋃ n, I ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    μH[1] (γ '' I) ≤ ∑' n, μH[1] (γ '' (I ∩ u n)) := by
      conv_lhs => rw [hIcover, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ x in I ∩ u n, (‖γ' x‖₊ : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum fun n => ?_
      apply aux2 (hI.inter (u_meas n)) ?_ (fun x hx => (hfd x hx.1).mono inter_subset_left)
      have : volume (u n) < ∞ :=
        lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
          (measure_spanningSets_lt_top (volume : Measure ℝ) n)
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) this)
    _ = ∫⁻ x in I, (‖γ' x‖₊ : ℝ≥0∞) := by
      rw [← lintegral_iUnion (fun n => hI.inter (u_meas n))
        (pairwise_disjoint_mono (disjoint_disjointed (spanningSets (volume : Measure ℝ)))
          (fun n => inter_subset_right)), ← hIcover]

/-- **Null sets carry no integrated level-set length (co-area absolute continuity).**

For a `K`-Lipschitz `u : ℂ → ℝ` and a `volume`-null measurable set `A`, the integrated arc-length of
the level sets meeting `A` vanishes:

`volume A = 0 → ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) = 0`.

This is the absolute-continuity ingredient of the co-area set function (`ν ≪ volume`). It is also
the "image of a null set is co-area-null" fact used to discard the non-differentiability set and to
handle the `{∇u = 0}` critical set in the area-formula proof.

## Truth and proof

**TRUE.** Cover the null `A` by an open `U ⊇ A` of small area (`volume U < ε`, outer regularity).
Write `U = ⋃ₙ Kₙ` as an increasing union of compact sets (`U` is σ-compact in ℂ); then
`μH[1] (u ⁻¹' {c} ∩ Kₙ) ↑ μH[1] (u ⁻¹' {c} ∩ U)` (continuity from below) and, each `Kₙ` being
compact, `c ↦ μH[1] (u ⁻¹' {c} ∩ Kₙ)` is measurable (`measurable_slice_hausdorff_one`), so monotone
convergence gives `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ U) = ⨆ₙ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kₙ)`. Each term is
`≤ K · μH[2] Kₙ ≤ K · μH[2] U = K · c₀ · volume U < K · c₀ · ε` by `eilenberg_coarea_planar_metric`
and `hausdorffMeasure_two_complex_smul_volume`. Hence `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ K c₀ ε` for all
`ε > 0`, so it is `0`. -/
theorem coarea_null_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) (hA0 : volume A = 0) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) = 0 := by
  classical
  have _ := hA
  have hucont : Continuous u := hu.continuous
  -- The proportionality constant `μH[2] = c₀ • volume`.
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- It suffices to bound the integral by `K * c₀ * ε` for every `ε > 0`.
  rw [← nonpos_iff_eq_zero]
  have key : ∀ ε : ℝ≥0∞, 0 < ε →
      ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * c₀ * ε := by
    intro ε εpos
    -- Outer regularity: open `U ⊇ A` with `volume U < ε`.
    obtain ⟨U, hAU, hUopen, hUvol⟩ :=
      Set.exists_isOpen_lt_of_lt A ε (by rw [hA0]; exact εpos)
    -- `U ≠ univ` since `volume U < ε < ∞` but `volume univ = ∞`.
    have hUne : U ≠ univ := by
      rintro rfl
      rw [measure_univ_of_isAddLeftInvariant] at hUvol
      exact (not_top_lt hUvol).elim
    have hUcompl_ne : (Uᶜ).Nonempty := by
      rw [nonempty_compl]; exact hUne
    -- Compact exhaustion of `U`:  Kₙ = closedBall 0 n ∩ {z | 1/(n+1) ≤ infDist z Uᶜ}.
    set Kset : ℕ → Set ℂ :=
      fun n => Metric.closedBall 0 n ∩ {z : ℂ | (1 : ℝ) / (n + 1) ≤ Metric.infDist z Uᶜ}
      with hKset_def
    have hKset_compact : ∀ n, IsCompact (Kset n) := by
      intro n
      apply (isCompact_closedBall (0 : ℂ) (n : ℝ)).of_isClosed_subset ?_ inter_subset_left
      refine (isCompact_closedBall (0 : ℂ) (n : ℝ)).isClosed.inter ?_
      exact isClosed_le continuous_const (Metric.continuous_infDist_pt Uᶜ)
    -- Each `Kₙ ⊆ U`.
    have hKset_subU : ∀ n, Kset n ⊆ U := by
      intro n z hz
      have hz2 : (1 : ℝ) / (n + 1) ≤ Metric.infDist z Uᶜ := hz.2
      by_contra hzU
      have hzc : z ∈ Uᶜ := hzU
      have h0 : Metric.infDist z Uᶜ = 0 := Metric.infDist_zero_of_mem hzc
      rw [h0] at hz2
      have : (0 : ℝ) < (1 : ℝ) / (n + 1) := by positivity
      linarith
    -- Monotone exhaustion.
    have hKset_mono : Monotone Kset := by
      intro m n hmn z hz
      refine ⟨?_, ?_⟩
      · exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn) hz.1
      · have hmn' : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (m + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
            linarith
        exact le_trans hmn' hz.2
    -- `⋃ n, Kₙ = U`.
    have hKset_union : ⋃ n, Kset n = U := by
      apply subset_antisymm
      · exact iUnion_subset hKset_subU
      · intro z hzU
        have hUcl : IsClosed Uᶜ := hUopen.isClosed_compl
        have hzNotCompl : z ∉ Uᶜ := by simpa using hzU
        have hposdist : 0 < Metric.infDist z Uᶜ :=
          (hUcl.notMem_iff_infDist_pos hUcompl_ne).mp hzNotCompl
        -- Choose `n` with `dist z 0 ≤ n` and `1/(n+1) ≤ infDist z Uᶜ`.
        obtain ⟨n₁, hn₁⟩ := exists_nat_ge (dist z 0)
        obtain ⟨n₂, hn₂⟩ := exists_nat_gt ((1 : ℝ) / Metric.infDist z Uᶜ)
        refine mem_iUnion.mpr ⟨max n₁ n₂, ?_, ?_⟩
        · rw [Metric.mem_closedBall]
          exact le_trans hn₁ (by exact_mod_cast le_max_left n₁ n₂)
        · change (1 : ℝ) / ((max n₁ n₂ : ℕ) + 1) ≤ Metric.infDist z Uᶜ
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hposdist] at hn₂
          have hle : ((n₂ : ℝ)) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ n₂
          nlinarith [Metric.infDist_nonneg (x := z) (s := Uᶜ)]
    -- Per-slice continuity from below for `μH[1]`.
    have hslice_sup : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ U) = ⨆ n, μH[1] (u ⁻¹' {c} ∩ Kset n) := by
      intro c
      have hmono : Monotone (fun n => u ⁻¹' {c} ∩ Kset n) := by
        intro m n hmn
        exact inter_subset_inter_right _ (hKset_mono hmn)
      have hunion : ⋃ n, u ⁻¹' {c} ∩ Kset n = u ⁻¹' {c} ∩ U := by
        rw [← inter_iUnion, hKset_union]
      rw [← hunion]
      exact hmono.measure_iUnion
    -- Each per-compact slice is measurable in `c`.
    have hmeas : ∀ n, Measurable (fun c => μH[1] (u ⁻¹' {c} ∩ Kset n)) :=
      fun n => measurable_slice_hausdorff_one hucont (hKset_compact n)
    -- Per-compact bound:  ∫ slice ≤ K * c₀ * ε.
    have hper : ∀ n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kset n) ≤ (K : ℝ≥0∞) * c₀ * ε := by
      intro n
      calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kset n)
          ≤ (K : ℝ≥0∞) * μH[2] (Kset n) :=
            eilenberg_coarea_planar_metric hu.lipschitzOnWith (hKset_compact n)
        _ ≤ (K : ℝ≥0∞) * μH[2] U := by
            gcongr (K : ℝ≥0∞) * ?_
            exact measure_mono (hKset_subU n)
        _ = (K : ℝ≥0∞) * c₀ * volume U := by
            rw [hc₀v]
            simp only [Measure.coe_nnreal_smul_apply]
            ring
        _ ≤ (K : ℝ≥0∞) * c₀ * ε := by gcongr
    -- Assemble: monotonicity to `U`, continuity from below, MCT, per-compact bound.
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)
        ≤ ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ U) := by
          apply lintegral_mono
          intro c
          exact measure_mono (inter_subset_inter_right _ hAU)
      _ = ∫⁻ c, ⨆ n, μH[1] (u ⁻¹' {c} ∩ Kset n) := by
          simp_rw [hslice_sup]
      _ = ⨆ n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Kset n) := by
          rw [lintegral_iSup hmeas]
          intro m n hmn c
          exact measure_mono (inter_subset_inter_right _ (hKset_mono hmn))
      _ ≤ (K : ℝ≥0∞) * c₀ * ε := iSup_le hper
  -- `≤ K c₀ ε` for all `ε > 0`  ⟹  `≤ 0`, by letting `ε → 0⁺`.
  have hlim : Tendsto (fun ε : ℝ≥0∞ => (K : ℝ≥0∞) * c₀ * ε) (𝓝[>] 0)
      (𝓝 ((K : ℝ≥0∞) * c₀ * 0)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ENNReal.Tendsto.const_mul tendsto_id
      (Or.inr (by simp [ENNReal.mul_ne_top]))
  rw [mul_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε εpos
  rw [mem_Ioi] at εpos
  exact key ε εpos

/-- **Planar metric Eilenberg inequality for a measurable set (extends the compact-set version).**

For `u` that is `K`-Lipschitz on a measurable set `A ⊆ ℂ`,
`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A`.

This drops the compactness hypothesis of `eilenberg_coarea_planar_metric`; it is the form the
area-formula assembly uses, where the Lusin pieces are measurable (not compact). It is the
absolute-continuity-style consequence of the compact version: by inner regularity write
`A = (⋃ₙ Kₙ) ∪ N` with `Kₙ` compact increasing and `volume N = 0`; the `N`-part contributes `0`
(`coarea_null_le`), and the `⋃ Kₙ` part is the monotone limit of the compact bounds
(`eilenberg_coarea_planar_metric` + `μH[2] (⋃ Kₙ) ≤ μH[2] A`). For `volume A = ∞` the right side is
`∞` (since `μH[2] = c₀ • volume` is infinite on a non-`volume`-finite set) and the bound is trivial.

**TRUE.** -/
theorem eilenberg_coarea_planar_metric_meas {u : ℂ → ℝ} {K : ℝ≥0} {A : Set ℂ}
    (hu : LipschitzOnWith K u A) (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ (K : ℝ≥0∞) * μH[2] A := by
  classical
  -- Globalize: `g` is `K`-Lipschitz on all of `ℂ`, agreeing with `u` on `A`.
  obtain ⟨g, hgLip, hgEq⟩ := hu.extend_real
  have hgcont : Continuous g := hgLip.continuous
  -- On `A` the slices for `u` and `g` coincide, so we may work with `g`.
  have hslice_eq : ∀ c : ℝ, u ⁻¹' {c} ∩ A = g ⁻¹' {c} ∩ A := by
    intro c; ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [← hgEq hzA]; exact hz, hzA⟩
    · rintro ⟨hz, hzA⟩; exact ⟨by rw [hgEq hzA]; exact hz, hzA⟩
  rw [show (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)) = ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ A) by
        apply lintegral_congr; intro c; rw [hslice_eq c]]
  -- The proportionality constant `μH[2] = c₀ • volume`.
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- Case split on whether `A` has finite area.
  rcases eq_or_ne (volume A) ∞ with hAtop | hAfin
  · -- `volume A = ∞ ⟹ μH[2] A = c₀ • volume A = ∞`, RHS is `∞`, bound trivial.
    have hH2top : μH[2] A = ∞ := by
      rw [hc₀v, Measure.coe_nnreal_smul_apply, hAtop, ENNReal.mul_top]
      exact_mod_cast (pos_iff_ne_zero.mp hc₀pos)
    rw [hH2top]
    rcases eq_or_ne (K : ℝ≥0∞) 0 with hK0 | hKne
    · -- `K = 0`: then `g` is constant on `A`, and the integral is over a single point.
      rw [hK0, zero_mul]
      rw [ENNReal.coe_eq_zero] at hK0
      subst hK0
      rcases A.eq_empty_or_nonempty with hAe | ⟨z0, hz0⟩
      · simp [hAe]
      · have hconst : ∀ x ∈ A, u x = u z0 := fun x hx =>
          (LipschitzOnWith.zero_iff u).1 hu x hx z0 hz0
        have hsupp : (fun c => μH[1] (g ⁻¹' {c} ∩ A))
            = Set.indicator {u z0} (fun _ => μH[1] A) := by
          funext c
          by_cases hc : c = u z0
          · subst hc
            rw [indicator_of_mem (by simp)]
            congr 1
            rw [Set.inter_eq_right]
            intro x hx
            simp only [mem_preimage, mem_singleton_iff]
            rw [← hgEq hx]; exact hconst x hx
          · rw [indicator_of_notMem (by simp [hc])]
            have hemp : g ⁻¹' {c} ∩ A = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro x ⟨hxc, hxA⟩
              simp only [mem_preimage, mem_singleton_iff] at hxc
              apply hc
              rw [← hxc, ← hgEq hxA, hconst x hxA]
            rw [hemp, measure_empty]
        rw [hsupp, lintegral_indicator (measurableSet_singleton _), setLIntegral_const,
          Real.volume_singleton, mul_zero]
    · rw [ENNReal.mul_top hKne]; exact le_top
  · -- Finite area: inner-regularity compact exhaustion.
    -- For each `n`, a compact `Kₙ ⊆ A` with `volume (A \ Kₙ) < 1/(n+1)`.
    have hAfin' : volume A ≠ ∞ := hAfin
    have hexc : ∀ n : ℕ, ∃ Q : Set ℂ, Q ⊆ A ∧ IsCompact Q ∧
        volume (A \ Q) < (1 : ℝ≥0∞) / (n + 1) := by
      intro n
      have hεne : ((1 : ℝ≥0∞) / (n + 1)) ≠ 0 := by
        rw [Ne, ENNReal.div_eq_zero_iff]
        rintro (h | h)
        · exact one_ne_zero h
        · exact (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩) h
      exact hA.exists_isCompact_diff_lt hAfin' hεne
    choose Q hQsub hQcomp hQdiff using hexc
    -- Monotone exhaustion `Kₙ := ⋃_{m ≤ n} Qₘ`.
    set Kset : ℕ → Set ℂ := fun n => ⋃ m ∈ Finset.range (n + 1), Q m with hKset_def
    have hKset_subA : ∀ n, Kset n ⊆ A := by
      intro n z hz
      simp only [hKset_def, mem_iUnion, Finset.mem_range] at hz
      obtain ⟨m, _, hzm⟩ := hz
      exact hQsub m hzm
    have hKset_compact : ∀ n, IsCompact (Kset n) := by
      intro n
      apply Finset.isCompact_biUnion
      intro m _; exact hQcomp m
    have hKset_mono : Monotone Kset := by
      intro p q hpq z hz
      simp only [hKset_def, mem_iUnion, Finset.mem_range] at hz ⊢
      obtain ⟨m, hm, hzm⟩ := hz
      exact ⟨m, lt_of_lt_of_le hm (by omega), hzm⟩
    -- `Qₙ ⊆ Kₙ`, so `A \ Kₙ ⊆ A \ Qₙ`.
    have hQsubK : ∀ n, Q n ⊆ Kset n := by
      intro n z hz
      simp only [hKset_def, mem_iUnion, Finset.mem_range]
      exact ⟨n, by omega, hz⟩
    set U : Set ℂ := ⋃ n, Kset n with hU_def
    have hUsubA : U ⊆ A := by
      rw [hU_def]; exact iUnion_subset hKset_subA
    have hUmeas : MeasurableSet U :=
      MeasurableSet.iUnion (fun n => (hKset_compact n).measurableSet)
    -- `N := A \ U` is measurable, `volume N = 0`, `N ⊆ A`.
    set N : Set ℂ := A \ U with hN_def
    have hNmeas : MeasurableSet N := hA.diff hUmeas
    have hNsubA : N ⊆ A := diff_subset
    have hN0 : volume N = 0 := by
      -- `volume N ≤ volume (A \ Kₙ) ≤ volume (A \ Qₙ) < 1/(n+1)` for all `n`.
      rw [← nonpos_iff_eq_zero]
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε εpos _
      -- Choose `n` with `1/(n+1) ≤ ε`.
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (ε : ℝ))
      have hNle : volume N ≤ (1 : ℝ≥0∞) / (n + 1) := by
        have h1 : N ⊆ A \ Q n := by
          rw [hN_def]
          apply diff_subset_diff_right
          calc Q n ⊆ Kset n := hQsubK n
            _ ⊆ U := subset_iUnion Kset n
        calc volume N ≤ volume (A \ Q n) := measure_mono h1
          _ ≤ (1 : ℝ≥0∞) / (n + 1) := le_of_lt (hQdiff n)
      calc volume N ≤ (1 : ℝ≥0∞) / (n + 1) := hNle
        _ ≤ (ε : ℝ≥0∞) := by
            rw [ENNReal.div_le_iff (by simp) (by simp)]
            rw [div_lt_iff₀ (by exact_mod_cast εpos)] at hn
            rw [← ENNReal.coe_one, ← ENNReal.coe_natCast, ← ENNReal.coe_add, ← ENNReal.coe_mul,
              ENNReal.coe_le_coe]
            have : (1 : ℝ) < ε * (n + 1) := by nlinarith [εpos.le]
            exact_mod_cast this.le
        _ = 0 + (ε : ℝ≥0∞) := by rw [zero_add]
    -- `A ⊆ U ∪ N`.
    have hAsub : A ⊆ U ∪ N := by
      intro z hz
      by_cases hzU : z ∈ U
      · exact Or.inl hzU
      · exact Or.inr ⟨hz, hzU⟩
    -- Slice continuity from below for `μH[1]` on the monotone `Kₙ ↑ U`.
    have hslice_sup : ∀ c : ℝ,
        μH[1] (g ⁻¹' {c} ∩ U) = ⨆ n, μH[1] (g ⁻¹' {c} ∩ Kset n) := by
      intro c
      have hmono : Monotone (fun n => g ⁻¹' {c} ∩ Kset n) := by
        intro p q hpq
        exact inter_subset_inter_right _ (hKset_mono hpq)
      have hunion : ⋃ n, g ⁻¹' {c} ∩ Kset n = g ⁻¹' {c} ∩ U := by
        rw [← inter_iUnion, hU_def]
      rw [← hunion]
      exact hmono.measure_iUnion
    -- Each per-compact slice is measurable in `c`.
    have hmeas : ∀ n, Measurable (fun c => μH[1] (g ⁻¹' {c} ∩ Kset n)) :=
      fun n => measurable_slice_hausdorff_one hgcont (hKset_compact n)
    -- The `U`-slice function is measurable (monotone sup of measurables).
    have hUslice_meas : Measurable (fun c => μH[1] (g ⁻¹' {c} ∩ U)) := by
      have : (fun c => μH[1] (g ⁻¹' {c} ∩ U))
          = (fun c => ⨆ n, μH[1] (g ⁻¹' {c} ∩ Kset n)) := by
        funext c; exact hslice_sup c
      rw [this]
      exact Measurable.iSup hmeas
    -- `∫ over U`-part as the monotone sup of compact bounds.
    have hUbound : ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U) ≤ (K : ℝ≥0∞) * μH[2] A := by
      calc ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U)
          = ∫⁻ c, ⨆ n, μH[1] (g ⁻¹' {c} ∩ Kset n) := by
            simp_rw [hslice_sup]
        _ = ⨆ n, ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ Kset n) := by
            rw [lintegral_iSup hmeas]
            intro p q hpq c
            exact measure_mono (inter_subset_inter_right _ (hKset_mono hpq))
        _ ≤ ⨆ n, (K : ℝ≥0∞) * μH[2] (Kset n) := by
            apply iSup_mono
            intro n
            exact eilenberg_coarea_planar_metric hgLip.lipschitzOnWith (hKset_compact n)
        _ = (K : ℝ≥0∞) * μH[2] U := by
            rw [← ENNReal.mul_iSup]
            congr 1
            rw [hU_def, hKset_mono.measure_iUnion]
        _ ≤ (K : ℝ≥0∞) * μH[2] A := by
            gcongr
    -- The `N`-part contributes `0`.
    have hNbound : ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ N) = 0 :=
      coarea_null_le hgLip hNmeas hN0
    -- Combine: split `A ⊆ U ∪ N`.
    calc ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ A)
        ≤ ∫⁻ c, (μH[1] (g ⁻¹' {c} ∩ U) + μH[1] (g ⁻¹' {c} ∩ N)) := by
          apply lintegral_mono
          intro c
          calc μH[1] (g ⁻¹' {c} ∩ A)
              ≤ μH[1] (g ⁻¹' {c} ∩ (U ∪ N)) := measure_mono (inter_subset_inter_right _ hAsub)
            _ = μH[1] ((g ⁻¹' {c} ∩ U) ∪ (g ⁻¹' {c} ∩ N)) := by rw [inter_union_distrib_left]
            _ ≤ μH[1] (g ⁻¹' {c} ∩ U) + μH[1] (g ⁻¹' {c} ∩ N) := measure_union_le _ _
      _ = (∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U)) + ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ N) := by
          rw [lintegral_add_left hUslice_meas]
      _ = ∫⁻ c, μH[1] (g ⁻¹' {c} ∩ U) := by rw [hNbound, add_zero]
      _ ≤ (K : ℝ≥0∞) * μH[2] A := hUbound

/-- **Almost every point of a measurable planar set is a point of unique differentiability.**

For a measurable `S ⊆ ℂ`, almost every `z ∈ S` satisfies `UniqueDiffWithinAt ℝ S z`.

This is the descriptive/measure-theoretic ingredient that lets a within-`S` derivative be identified
with the genuine `fderiv` a.e.: in `coarea_piece_le`, `u = Complex.re ∘ Ψ` holds only *on* `S`, so
the within-`S` derivative `Complex.reCLM ∘L Ψ'` equals the full `fderiv ℝ u` only at points of
unique differentiability of `S` — which, by this lemma, is a.e.

## Truth and proof

**TRUE.** Almost every `z ∈ S` is a Lebesgue density-`1` point of `S`
(`Besicovitch.ae_tangentCone`-style / `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`).
At a density-`1` point the tangent cone `tangentConeAt ℝ S z` is all of `ℂ` (a positive-density set
approaches `z` from a dense set of directions), and `uniqueDiffWithinAt_iff` then gives
`UniqueDiffWithinAt ℝ S z`.

**Mathlib gap:** Mathlib has the density-`1` a.e. theorem and `uniqueDiffWithinAt_iff` (unique diff
`=` dense tangent-cone span), but **no bridge `density-1 ⟹ tangent-cone dense`** in dimension `≥ 2`
(the
existing density→`UniqueDiffWithinAt` route, `uniqueDiffWithinAt_iff_accPt`, is `1`-D
`NormedDivisionRing`-only). This bridge is the net-new content. -/
theorem ae_uniqueDiffWithinAt_of_measurableSet {S : Set ℂ} (hS : MeasurableSet S) :
    ∀ᵐ z ∂(volume.restrict S), UniqueDiffWithinAt ℝ S z := by
  classical
  -- Off-center Lebesgue density theorem with constant `K = 4`: a.e. point of `S`
  -- is a density point.
  have hdens := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure ℂ) S 4
  have hmemS : ∀ᵐ z ∂(volume.restrict S), z ∈ S := by
    rw [ae_restrict_iff' hS]; filter_upwards with z hz using hz
  filter_upwards [hdens, hmemS] with z hz hzS
  rw [uniqueDiffWithinAt_iff]
  refine ⟨?_, subset_closure hzS⟩
  -- Reduce dense-span to span = ⊤.
  suffices hspan : Submodule.span ℝ (tangentConeAt ℝ S z) = ⊤ by
    exact hspan ▸ (Submodule.top_coe (R := ℝ) (M := ℂ) ▸ dense_univ)
  -- KEY: for any unit direction `e`, the tangent cone contains a vector within `1/4` of `e`.
  have key : ∀ e : ℂ, ‖e‖ = 1 → ∃ y ∈ tangentConeAt ℝ S z, ‖y - e‖ ≤ 1/4 := by
    intro e he_norm
    -- Centres march toward `z` along `e` at distance `(n+1)⁻¹`; radii are `(n+1)⁻¹/4`.
    set w : ℕ → ℂ := fun n => z + ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e with hw
    set δ : ℕ → ℝ := fun n => (((n : ℝ) + 1)⁻¹) / 4 with hδ
    have hδpos : ∀ n, 0 < δ n := by intro n; rw [hδ]; positivity
    have hδ0 : Tendsto δ atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa [hδ] using h1.div_const 4
      · filter_upwards with n using hδpos n
    have hdist : ∀ n, dist z (w n) = ((n : ℝ) + 1)⁻¹ := by
      intro n
      rw [hw, dist_eq_norm]
      have h0 : z - (z + (((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) * e)
          = -((((((n : ℝ) + 1)⁻¹ : ℝ)) : ℂ) * e) := by ring
      rw [h0, norm_neg, norm_mul, Complex.norm_real, he_norm, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    -- `z` lies in the enlarged ball `closedBall (w n) (4 δ n)` since `dist z (w n) = 4 δ n`.
    have hzball : ∀ n, z ∈ Metric.closedBall (w n) (4 * δ n) := by
      intro n
      rw [Metric.mem_closedBall, hdist n, hδ]
      rw [show (4 : ℝ) * (((n : ℝ) + 1)⁻¹ / 4) = ((n : ℝ) + 1)⁻¹ by ring]
    have hratio := hz w δ hδ0 (Filter.Eventually.of_forall hzball)
    -- Density `→ 1` forces the intersection to be eventually nonempty.
    have hpos : ∀ᶠ n in atTop, (0 : ℝ≥0∞) <
        volume (S ∩ Metric.closedBall (w n) (δ n)) / volume (Metric.closedBall (w n) (δ n)) :=
      hratio.eventually (Ioi_mem_nhds (by norm_num))
    have hnonempty : ∀ᶠ n in atTop, (S ∩ Metric.closedBall (w n) (δ n)).Nonempty := by
      filter_upwards [hpos] with n hn
      apply nonempty_of_measure_ne_zero (μ := volume)
      intro hzero
      rw [hzero, ENNReal.zero_div] at hn
      exact lt_irrefl _ hn
    -- Pick a point `p n ∈ S` in the small ball (junk `z` off the eventual set).
    set p : ℕ → ℂ := fun n =>
      if h : (S ∩ Metric.closedBall (w n) (δ n)).Nonempty then h.choose else z with hp
    have hp_spec : ∀ᶠ n in atTop, p n ∈ S ∩ Metric.closedBall (w n) (δ n) := by
      filter_upwards [hnonempty] with n hn
      rw [hp]; simp only [hn, dif_pos]; exact hn.choose_spec
    set d : ℕ → ℂ := fun n => p n - z with hd
    have hp_specS : ∀ᶠ n in atTop, z + d n ∈ S := by
      filter_upwards [hp_spec] with n hn
      rw [hd]; simp only [add_sub_cancel]; exact hn.1
    -- The displacement `d n` is within `δ n` of `(n+1)⁻¹ e`.
    have hr_bound : ∀ᶠ n in atTop,
        ‖d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ ≤ δ n := by
      filter_upwards [hp_spec] with n hn
      have hball : ‖p n - w n‖ ≤ δ n := by
        have := hn.2; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
      have heq : d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e = p n - w n := by rw [hd, hw]; ring
      rw [heq]; exact hball
    -- Rescale: `cseq n • d n` lives in `closedBall e (1/4)`, and `d n → 0`.
    set cseq : ℕ → ℝ := fun n => (n : ℝ) + 1 with hcseq
    set g : ℕ → ℂ := fun n => cseq n • d n with hg
    have hd0 : Tendsto d atTop (𝓝 0) := by
      have hbound : ∀ᶠ n in atTop, ‖d n‖ ≤ ((n : ℝ) + 1)⁻¹ + δ n := by
        filter_upwards [hr_bound] with n hn
        have htri : ‖d n‖ ≤ ‖d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖
            + ‖((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ := by
          have := norm_add_le (d n - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e)
            (((((n : ℝ) + 1)⁻¹ : ℝ)) * e)
          simpa using this
        have hnorm2 : ‖((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ = ((n : ℝ) + 1)⁻¹ := by
          rw [norm_mul, Complex.norm_real, he_norm, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
        rw [hnorm2] at htri; linarith [hn]
      have hto0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ + δ n) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have h2 : Tendsto δ atTop (𝓝 0) := by rw [hδ]; simpa using h1.div_const 4
        simpa using h1.add h2
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) hbound hto0
    -- abstract algebraic bound: rescaling by `(n+1)` shrinks the `δ n`-error to `1/4`.
    have halg : ∀ (n : ℕ) (dn : ℂ),
        ‖dn - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖ ≤ δ n →
        ‖(((n : ℝ) + 1 : ℝ) : ℂ) * dn - e‖ ≤ 1/4 := by
      intro n dn hbnd
      have hfact : (((n : ℝ) + 1 : ℝ) : ℂ) * dn - e
          = (((n : ℝ) + 1 : ℝ) : ℂ) * (dn - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e) := by
        rw [mul_sub]; congr 1
        rw [← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (by positivity : ((n : ℝ) + 1) ≠ 0)]
        simp
      rw [hfact, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ((n : ℝ) + 1) * ‖dn - ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * e‖
          ≤ ((n : ℝ) + 1) * δ n := mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = 1/4 := by rw [hδ]; field_simp
    have hg_ball : ∀ᶠ n in atTop, g n ∈ Metric.closedBall e (1/4) := by
      filter_upwards [hr_bound] with n hn
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hgn : g n = (((n : ℝ) + 1 : ℝ) : ℂ) * d n := by
        rw [hg]; simp only [hcseq]; exact Complex.real_smul ..
      rw [hgn]
      exact halg n (d n) hn
    -- Bolzano-Weierstrass: extract a convergent subsequence of `g`.
    -- `g` lies in the compact ball `closedBall e (1/4)` for all `n ≥ N`; shift and extract.
    rw [eventually_atTop] at hg_ball
    obtain ⟨N, hN⟩ := hg_ball
    have hmemN : ∀ n, g (n + N) ∈ Metric.closedBall e (1/4) := fun n => hN (n + N) (by omega)
    obtain ⟨y, hy_ball, ψ, hψ_mono, hψ_tendsto⟩ :=
      (isCompact_closedBall e (1/4)).tendsto_subseq hmemN
    -- the composite index `ρ n = ψ n + N` is strictly monotone.
    set ρ : ℕ → ℕ := fun n => ψ n + N with hρ
    have hρ_mono : StrictMono ρ := fun a b hab => Nat.add_lt_add_right (hψ_mono hab) N
    refine ⟨y, ?_, ?_⟩
    · refine mem_tangentConeAt_of_seq atTop (cseq ∘ ρ) (d ∘ ρ) ?_ ?_ ?_
      · exact hd0.comp hρ_mono.tendsto_atTop
      · exact hρ_mono.tendsto_atTop.eventually hp_specS
      · have hgeq : (fun n => (cseq ∘ ρ) n • (d ∘ ρ) n) = fun n => g (ψ n + N) := by
          funext n; rw [hg]; rfl
        rw [hgeq]; exact hψ_tendsto
    · rw [Metric.mem_closedBall, dist_eq_norm] at hy_ball; exact hy_ball
  -- Apply `key` to directions `1` and `I`; the two near-orthogonal vectors span `ℂ` over `ℝ`.
  obtain ⟨y1, hy1, hb1⟩ := key 1 (by simp)
  obtain ⟨y2, hy2, hb2⟩ := key Complex.I (by simp)
  set T := tangentConeAt ℝ S z with hT
  -- coordinate bounds from the `1/4` norm estimates
  have hre1 : |y1.re - 1| ≤ 1/4 := by
    have : |(y1 - 1).re| ≤ ‖y1 - 1‖ := Complex.abs_re_le_norm _
    simpa using this.trans hb1
  have him1 : |y1.im| ≤ 1/4 := by
    have : |(y1 - 1).im| ≤ ‖y1 - 1‖ := Complex.abs_im_le_norm _
    simpa using this.trans hb1
  have hre2 : |y2.re| ≤ 1/4 := by
    have : |(y2 - Complex.I).re| ≤ ‖y2 - Complex.I‖ := Complex.abs_re_le_norm _
    simpa using this.trans hb2
  have him2 : |y2.im - 1| ≤ 1/4 := by
    have : |(y2 - Complex.I).im| ≤ ‖y2 - Complex.I‖ := Complex.abs_im_le_norm _
    simpa using this.trans hb2
  have hy1re : (3:ℝ)/4 ≤ y1.re := by rw [abs_le] at hre1; linarith [hre1.1]
  have hy2im : (3:ℝ)/4 ≤ y2.im := by rw [abs_le] at him2; linarith [him2.1]
  have hy1ne : y1 ≠ 0 := by
    intro h; rw [h] at hy1re; simp at hy1re; linarith
  -- linear independence of `![y1, y2]`
  have hli : LinearIndependent ℝ ![y1, y2] := by
    rw [LinearIndependent.pair_iff' hy1ne]
    intro a hcontra
    have h2 : (a : ℂ) * y1 = y2 := by rw [← Complex.real_smul]; exact hcontra
    have hre : a * y1.re = y2.re := by
      have h := congrArg Complex.re h2; simpa using h
    have him : a * y1.im = y2.im := by
      have h := congrArg Complex.im h2; simpa using h
    have ha_bound : |a| ≤ 1/3 := by
      have hare : |a| * y1.re = |y2.re| := by
        rw [← abs_of_pos (by linarith : (0:ℝ) < y1.re), ← abs_mul, hre]
      nlinarith [abs_nonneg a, hre2, hy1re, hare]
    have hkey : a * y1.im ≤ 1/12 := by
      have hbnd : |a * y1.im| ≤ 1/12 := by
        calc |a * y1.im| = |a| * |y1.im| := abs_mul a y1.im
          _ ≤ (1/3) * (1/4) := mul_le_mul ha_bound him1 (abs_nonneg _) (by norm_num)
          _ = 1/12 := by norm_num
      linarith [(abs_le.mp hbnd).2]
    rw [him] at hkey; linarith
  -- two independent vectors span the 2-dimensional `ℝ`-space `ℂ`.
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ ℂ := by
    rw [Complex.finrank_real_complex]; rfl
  have hsp := hli.span_eq_top_of_card_eq_finrank hcard
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty] at hsp
  apply top_unique
  rw [← hsp]
  apply Submodule.span_mono
  intro x hx
  simp only [Set.union_empty, Set.union_singleton, Set.mem_insert_iff] at hx
  rcases hx with h | h
  · rw [h]; exact hy2
  · simp only [Set.mem_singleton_iff] at h; rw [h]; exact hy1

/-- **Per-piece sharp co-area bound (the IFT-free area-formula core).**

On a Lusin piece `S` where the square map `Ψ : ℂ → ℂ` (with `Ψ.re = u`) is approximately the linear
isomorphism `A` (so `Ψ` is bi-Lipschitz and `Set.InjOn` on `S`), the integrated level-set length of
`u` over `S` is bounded by the gradient integral:

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ z in S, ‖fderiv ℝ u z‖₊`.

This is the genuine core of the area-formula proof of the sharp co-area inequality. It is proved
**without the inverse function theorem** (which is unavailable for a merely differentiable `Ψ`):

* `ApproximatesLinearOn Ψ A S δ` with `δ < ‖A.symm‖₊⁻¹` makes `Ψ` `Set.InjOn S`
  (`ApproximatesLinearOn.injOn`) and **bi-Lipschitz** on `S`, so `Ψ⁻¹` is Lipschitz — so the level
  curve `u ⁻¹' {c} ∩ S = Ψ⁻¹ '' (Ψ '' S ∩ {w | w.re = c})` is a **Lipschitz** image of a segment,
  differentiable a.e. (Rademacher), with NO `C¹` / IFT hypothesis.
* The proven fiber-arc-length bound `hausdorffMeasure_one_image_le` (applied on the a.e.-diff subset
  of the segment; the Lipschitz image of the remaining null set is `μH[1]`-null) gives
  `μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ s, ‖∂_im Ψ⁻¹ (c + s·I)‖`.
* Fubini in `(c, s)` over `Ψ '' S` and the area formula
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul` for the InjOn differentiable `Ψ` convert this to
  `∫⁻ z in S, ‖(Ψ' z)⁻¹ · I‖ · |det (Ψ' z)|`, and the pointwise linear-algebra identity
  `‖(Ψ' z)⁻¹ · I‖ · |det (Ψ' z)| = ‖fderiv ℝ u z‖` (independent of the second coordinate `ℓ`;
  `fderiv ℝ u = Complex.re ∘ Ψ'`) finishes.

**TRUE.** -/
theorem coarea_piece_le {u : ℂ → ℝ} {Ψ : ℂ → ℂ} {Ψ' : ℂ → (ℂ →L[ℝ] ℂ)}
    {A : ℂ ≃L[ℝ] ℂ} {S : Set ℂ} {δ : ℝ≥0}
    (hS : MeasurableSet S) (_hSb : Bornology.IsBounded S)
    (hδ : δ < ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹)
    (hALO : ApproximatesLinearOn Ψ (A : ℂ →L[ℝ] ℂ) S δ)
    (hΨ' : ∀ z ∈ S, HasFDerivWithinAt Ψ (Ψ' z) S z)
    (hre : ∀ z ∈ S, (Ψ z).re = u z)
    (hdiff : ∀ z ∈ S, DifferentiableAt ℝ u z) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S) ≤ ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
  classical
  -- =================================================================
  -- (1)  Basic structure of `Ψ` and its inverse `g` on `T = Ψ '' S`.
  -- =================================================================
  have hinj : InjOn Ψ S := hALO.injOn (Or.inr hδ)
  set g : ℂ → ℂ := Function.invFunOn Ψ S with hg
  set T : Set ℂ := Ψ '' S with hT
  have hleft : ∀ z ∈ S, g (Ψ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hright : ∀ w ∈ T, Ψ (g w) = w := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hleft z hz]
  have hgmem : ∀ w ∈ T, g w ∈ S := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hleft z hz]; exact hz
  have hgLip : LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹) g T := by
    rw [lipschitzOnWith_iff_restrict]
    exact (hALO.antilipschitz (Or.inr hδ)).to_rightInvOn'
      (fun w hw => hgmem w hw) (fun w hw => hright w hw)
  have hgCont : ContinuousOn g T := hgLip.continuousOn
  have hTmeas : MeasurableSet T := measurable_image_of_fderivWithin hS hΨ' hinj
  -- =================================================================
  -- (2)  `det (Ψ' z) ≠ 0` a.e. on `S` (small perturbation of `A`).
  -- =================================================================
  have hAne : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊ ≠ 0 := by
    intro h0; rw [h0, inv_zero] at hδ; exact absurd hδ (not_lt.mpr (zero_le _))
  have hApos : (0 : ℝ≥0) < ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊ := pos_of_ne_zero hAne
  -- the perturbation lemma: ‖T₀ - A‖ ≤ δ ⟹ T₀.det ≠ 0
  have hdet_of_close : ∀ T₀ : ℂ →L[ℝ] ℂ, ‖T₀ - (A : ℂ →L[ℝ] ℂ)‖₊ ≤ δ → T₀.det ≠ 0 := by
    intro T₀ hT₀
    have hinjT : Function.Injective (T₀ : ℂ →ₗ[ℝ] ℂ) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      by_contra hvne
      have hvpos : (0 : ℝ≥0) < ‖v‖₊ := by rwa [nnnorm_pos]
      have hAv : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ * ‖v‖₊ ≤ ‖(A : ℂ →L[ℝ] ℂ) v‖₊ := by
        have hb := (A : ℂ →L[ℝ] ℂ).bound_of_antilipschitz A.antilipschitz v
        rw [← NNReal.coe_le_coe]; push_cast
        rw [inv_mul_le_iff₀ (by exact_mod_cast hApos)]
        rw [coe_nnnorm] at hb; exact hb
      have hTAv : ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ ≤ δ * ‖v‖₊ := by
        calc ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ ≤ ‖T₀ - (A : ℂ →L[ℝ] ℂ)‖₊ * ‖v‖₊ :=
              (T₀ - (A : ℂ →L[ℝ] ℂ)).le_opNNNorm v
          _ ≤ δ * ‖v‖₊ := by gcongr
      have hTeq : T₀ v = (A : ℂ →L[ℝ] ℂ) v + (T₀ - (A : ℂ →L[ℝ] ℂ)) v := by
        rw [ContinuousLinearMap.sub_apply]; ring
      have hTv0 : (A : ℂ →L[ℝ] ℂ) v + (T₀ - (A : ℂ →L[ℝ] ℂ)) v = 0 := by rw [← hTeq]; exact hv
      have hAvnorm : ‖(A : ℂ →L[ℝ] ℂ) v‖₊ = ‖(T₀ - (A : ℂ →L[ℝ] ℂ)) v‖₊ := by
        rw [eq_neg_of_add_eq_zero_left hTv0, nnnorm_neg]
      have hchain : ‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ * ‖v‖₊ ≤ δ * ‖v‖₊ :=
        le_trans hAv (le_trans (le_of_eq hAvnorm) hTAv)
      exact absurd (lt_of_le_of_lt (le_of_mul_le_mul_right hchain hvpos) hδ) (lt_irrefl _)
    intro hdet0
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet0) (LinearMap.ker_eq_bot.mpr hinjT)
  have hdet_ne : ∀ᵐ z ∂(volume.restrict S), (Ψ' z).det ≠ 0 := by
    filter_upwards [hALO.norm_fderiv_sub_le volume hS Ψ' hΨ'] with z hz
    exact hdet_of_close (Ψ' z) hz
  -- =================================================================
  -- (3)  The inverse derivative `Dg` and the weight `Φ`.
  -- =================================================================
  set Dg : ℂ → (ℂ →L[ℝ] ℂ) := fun w =>
    if h : (Ψ' (g w)).det ≠ 0 then
      (((Ψ' (g w)).toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) else 0 with hDg
  set Φ : ℂ → ℝ≥0∞ := fun w => (‖Dg w Complex.I‖₊ : ℝ≥0∞) with hΦ
  have hinvderiv : ∀ z ∈ S, (h : (Ψ' z).det ≠ 0) →
      HasFDerivWithinAt g
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) T (Ψ z) := by
    intro z hz h
    have hgΨz : g (Ψ z) = z := hleft z hz
    have hfd : HasFDerivWithinAt Ψ
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero h) : ℂ →L[ℝ] ℂ) S (g (Ψ z)) := by
      rw [hgΨz, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]; exact hΨ' z hz
    have htend : Filter.Tendsto g (𝓝[T] (Ψ z)) (𝓝[S] (g (Ψ z))) :=
      (hgCont _ ⟨z, hz, rfl⟩).tendsto_nhdsWithin (fun w hw => hgmem w hw)
    have hev : ∀ᶠ y in 𝓝[T] (Ψ z), Ψ (g y) = y := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hright y hy
    exact HasFDerivWithinAt.of_local_left_inverse htend hfd ⟨z, hz, rfl⟩ hev
  -- =================================================================
  -- (4)  The pointwise linear-algebra identity (`LA identity`):
  --      `ofReal |T₀.det| * ‖(T₀)⁻¹ I‖ = ‖reCLM ∘ T₀‖`  for invertible `T₀`.
  -- =================================================================
  have hLA : ∀ (T₀ : ℂ →L[ℝ] ℂ) (h : T₀.det ≠ 0),
      ENNReal.ofReal |T₀.det| *
          (‖((T₀.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞)
        = (‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞) := by
    intro T₀ h
    set Te := T₀.toContinuousLinearEquivOfDetNeZero h with hTe
    set w : ℂ := (Te.symm : ℂ →L[ℝ] ℂ) Complex.I with hw
    have hTw : T₀ w = Complex.I := by
      have : (Te : ℂ →L[ℝ] ℂ) w = Complex.I := by
        rw [hw]; exact Te.apply_symm_apply Complex.I
      rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] at this
    set a := (T₀ 1).re with ha
    set b := (T₀ 1).im with hb
    set cc := (T₀ Complex.I).re with hcc
    set d := (T₀ Complex.I).im with hd
    have hdet : T₀.det = a * d - cc * b := by
      rw [show T₀.det = LinearMap.det (T₀ : ℂ →ₗ[ℝ] ℂ) from rfl,
        show LinearMap.det (T₀ : ℂ →ₗ[ℝ] ℂ)
          = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
              (T₀ : ℂ →ₗ[ℝ] ℂ)) from (LinearMap.det_toMatrix Complex.basisOneI _).symm]
      rw [Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    have hdecomp : T₀ w = w.re • (T₀ 1) + w.im • (T₀ Complex.I) := by
      have hwd : w = w.re • (1 : ℂ) + w.im • Complex.I := by
        apply Complex.ext <;> simp [Complex.real_smul]
      conv_lhs => rw [hwd]
      rw [map_add, map_smul, map_smul]
    have hre_eq : a * w.re + cc * w.im = 0 := by
      have h1 := congrArg Complex.re hTw
      rw [hdecomp] at h1
      simp only [Complex.add_re, Complex.smul_re, Complex.I_re, smul_eq_mul] at h1
      simp only [ha, hcc]; nlinarith [h1]
    have him_eq : b * w.re + d * w.im = 1 := by
      have h1 := congrArg Complex.im hTw
      rw [hdecomp] at h1
      simp only [Complex.add_im, Complex.smul_im, Complex.I_im, smul_eq_mul] at h1
      simp only [hb, hd]; nlinarith [h1]
    have hdetre : T₀.det * w.re = -cc := by
      rw [hdet]; linear_combination d * hre_eq - cc * him_eq
    have hdetim : T₀.det * w.im = a := by
      rw [hdet]; linear_combination (-b) * hre_eq + a * him_eq
    have hLval : ‖Complex.reCLM.comp T₀‖ = Real.sqrt (a ^ 2 + cc ^ 2) := by
      set L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp T₀ with hL
      set v := (InnerProductSpace.toDual ℝ ℂ).symm L with hv
      have hLnorm : ‖v‖ = ‖L‖ := LinearIsometryEquiv.norm_map _ _
      have hriesz : ∀ z : ℂ, L z = inner ℝ v z := fun z => by
        rw [hv]; exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)).symm
      have hL1 : L 1 = a := by simp [hL, Complex.reCLM_apply, ha]
      have hLI : L Complex.I = cc := by simp [hL, Complex.reCLM_apply, hcc]
      have hvre : v.re = a := by
        have hh := (hriesz 1).symm; rw [hL1, Complex.inner] at hh; simpa using hh
      have hvim : v.im = cc := by
        have hh := (hriesz Complex.I).symm; rw [hLI, Complex.inner] at hh
        rw [Complex.mul_re] at hh; simp [Complex.conj_re, Complex.conj_im] at hh; linarith [hh]
      rw [← hLnorm, Complex.norm_eq_sqrt_sq_add_sq, hvre, hvim]
    have hprod : |T₀.det| * ‖w‖ = Real.sqrt (a ^ 2 + cc ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq w, ← Real.sqrt_sq (abs_nonneg T₀.det),
        ← Real.sqrt_mul (by positivity)]
      congr 1
      rw [sq_abs]
      have e1 : (T₀.det * w.re) ^ 2 = cc ^ 2 := by rw [hdetre, neg_pow, neg_one_sq, one_mul]
      have e2 : (T₀.det * w.im) ^ 2 = a ^ 2 := by rw [hdetim]
      nlinarith [e1, e2]
    have hwnn : ((‖(Te.symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖w‖ := by
      rw [← hw, ← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm]
    have hLnn : ((‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖Complex.reCLM.comp T₀‖ := by
      rw [← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm]
    change ENNReal.ofReal |T₀.det| * ((‖(Te.symm : ℂ →L[ℝ] ℂ) Complex.I‖₊ : ℝ≥0∞))
        = ((‖Complex.reCLM.comp T₀‖₊ : ℝ≥0∞))
    rw [hwnn, hLnn, ← ENNReal.ofReal_mul (abs_nonneg _), hprod, hLval]
  -- =================================================================
  -- (5)  a.e. on `S`:  `fderiv ℝ u z = reCLM ∘ Ψ' z`  (unique-diff points).
  -- =================================================================
  have hfderiv_eq : ∀ᵐ z ∂(volume.restrict S), fderiv ℝ u z = Complex.reCLM.comp (Ψ' z) := by
    filter_upwards [ae_uniqueDiffWithinAt_of_measurableSet hS,
      (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (fun z hz => hz))]
      with z hud hz
    have h1 : HasFDerivWithinAt (fun w => (Ψ w).re) (Complex.reCLM.comp (Ψ' z)) S z :=
      Complex.reCLM.hasFDerivAt.comp_hasFDerivWithinAt z (hΨ' z hz)
    have h2 : HasFDerivWithinAt u (Complex.reCLM.comp (Ψ' z)) S z :=
      h1.congr (fun w hw => (hre w hw).symm) (hre z hz).symm
    rw [← (hdiff z hz).fderivWithin hud, h2.fderivWithin hud]
  -- =================================================================
  -- (6)  AE-measurability of `Φ` on `T` (via the measurable embedding `Ψ|S`).
  -- =================================================================
  -- `Ψ'` is a.e.-measurable on `S`.
  have hΨ'meas : AEMeasurable Ψ' (volume.restrict S) := aemeasurable_fderivWithin volume hS hΨ'
  -- on `S`, a.e., `Φ (Ψ z) = ‖reCLM ∘ Ψ' z‖₊ / ofReal |det (Ψ' z)|`.
  have hΦΨ : ∀ᵐ z ∂(volume.restrict S),
      Φ (Ψ z) = (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞) / ENNReal.ofReal |(Ψ' z).det| := by
    filter_upwards [hdet_ne, (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall (fun z hz => hz))]
      with z hdetz hz
    have hgΨ : g (Ψ z) = z := hleft z hz
    have hDgΨ : Dg (Ψ z) =
        (((Ψ' z).toContinuousLinearEquivOfDetNeZero hdetz).symm : ℂ →L[ℝ] ℂ) := by
      rw [hDg]
      simp only [hgΨ]
      exact dif_pos hdetz
    have hΦval : Φ (Ψ z) =
        (‖(((Ψ' z).toContinuousLinearEquivOfDetNeZero hdetz).symm : ℂ →L[ℝ] ℂ)
            Complex.I‖₊ : ℝ≥0∞) := by
      rw [hΦ]; simp only [hDgΨ]
    rw [hΦval]
    have hdtop : ENNReal.ofReal |(Ψ' z).det| ≠ ⊤ := ENNReal.ofReal_ne_top
    have hd0 : ENNReal.ofReal |(Ψ' z).det| ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact hdetz
    rw [ENNReal.eq_div_iff hd0 hdtop]
    exact hLA (Ψ' z) hdetz
  -- `‖reCLM ∘ Ψ' ·‖₊ / ofReal |det Ψ' ·|` is a.e.-measurable on `S`.
  have hmeas_aux : AEMeasurable
      (fun z => (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞) / ENNReal.ofReal |(Ψ' z).det|)
      (volume.restrict S) := by
    have hcompcont : Continuous (fun M : ℂ →L[ℝ] ℂ => Complex.reCLM.comp M) := by
      have := (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).continuous
      simpa only [ContinuousLinearMap.compL_apply] using this
    have hc1 : AEMeasurable (fun z => (‖Complex.reCLM.comp (Ψ' z)‖₊ : ℝ≥0∞))
        (volume.restrict S) := by
      apply measurable_coe_nnreal_ennreal.comp_aemeasurable
      exact (continuous_nnnorm.comp hcompcont).measurable.comp_aemeasurable hΨ'meas
    have hc2 : AEMeasurable (fun z => ENNReal.ofReal |(Ψ' z).det|) (volume.restrict S) :=
      aemeasurable_ofReal_abs_det_fderivWithin volume hS hΨ'
    exact hc1.div hc2
  have hΦΨ_meas : AEMeasurable (fun z => Φ (Ψ z)) (volume.restrict S) :=
    hmeas_aux.congr (hΦΨ.mono (fun z hz => hz.symm))
  -- `Ψ` differentiable on `S`, hence images of null subsets are null.
  have hΨdiffOn : DifferentiableOn ℝ Ψ S := fun z hz => (hΨ' z hz).differentiableWithinAt
  -- `g` pushes `volume.restrict T` absolutely continuously onto `volume.restrict S`.
  have hgAC : (Measure.map g (volume.restrict T)) ≪ (volume.restrict S) := by
    have hgaem : AEMeasurable g (volume.restrict T) := hgCont.aemeasurable hTmeas
    refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
    -- volume (N ∩ S) = 0 ⟹ map g (restrict T) N = 0
    rw [Measure.restrict_apply hN] at hN0
    rw [Measure.map_apply_of_aemeasurable hgaem hN]
    -- g ⁻¹' N ∩ T ⊆ Ψ '' (N ∩ S)
    have hsub : g ⁻¹' N ∩ T ⊆ Ψ '' (N ∩ S) := by
      rintro w ⟨hwN, hwT⟩
      exact ⟨g w, ⟨hwN, hgmem w hwT⟩, hright w hwT⟩
    have himg0 : volume (Ψ '' (N ∩ S)) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (hΨdiffOn.mono inter_subset_right) hN0
    rw [Measure.restrict_apply' hTmeas]
    exact measure_mono_null hsub himg0
  -- transfer:  `Φ = (Φ ∘ Ψ) ∘ g` on `T`,  AEMeasurable via the change-of-variables.
  have hΦ_meas : AEMeasurable Φ (volume.restrict T) := by
    have hgaem : AEMeasurable g (volume.restrict T) := hgCont.aemeasurable hTmeas
    have hcomp : AEMeasurable (fun w => Φ (Ψ (g w))) (volume.restrict T) :=
      (hΦΨ_meas.mono' hgAC).comp_aemeasurable hgaem
    refine hcomp.congr ?_
    filter_upwards [(ae_restrict_iff' hTmeas).2 (Filter.Eventually.of_forall (fun w hw => hw))]
      with w hw
    rw [hright w hw]
  -- =================================================================
  -- (7)  STEP A:  `∫⁻ c, μH[1] (u⁻¹{c} ∩ S) ≤ ∫⁻ w in T, Φ w`.
  -- =================================================================
  -- A measurable null superset (within `S`) of the degenerate set, and its null image.
  obtain ⟨Z, hZsub, hZmeas, hZ0⟩ :
      ∃ Z : Set ℂ, ({z | ¬ (Ψ' z).det ≠ 0} ∩ S) ⊆ Z ∧ MeasurableSet Z ∧ volume Z = 0 := by
    have hh : volume.restrict S {z | ¬ (Ψ' z).det ≠ 0} = 0 := hdet_ne
    rw [Measure.restrict_apply₀' hS.nullMeasurableSet] at hh
    exact exists_measurable_superset_of_null hh
  -- `Ψ '' (Z ∩ S)` is `volume`-null.
  have hΨZ0 : volume (Ψ '' (Z ∩ S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hΨdiffOn.mono inter_subset_right)
      (measure_mono_null inter_subset_left hZ0)
  -- a.e. `c`, the slice `{s | mk c s ∈ Ψ '' (Z ∩ S)}` is `volume`-null.
  set W : Set ℂ := Ψ '' (Z ∩ S) with hW
  have hslicenull : ∀ᵐ c : ℝ, volume {s : ℝ | Complex.mk c s ∈ W} = 0 := by
    -- transport nullity to `ℝ × ℝ` via `measurableEquivRealProd.symm`.
    set P : Set (ℝ × ℝ) := Complex.measurableEquivRealProd.symm ⁻¹' W with hP
    have hpre : (volume : Measure (ℝ × ℝ)) P = 0 := by
      rw [hP, (Complex.volume_preserving_equiv_real_prod.symm _).measure_preimage
        (NullMeasurableSet.of_null hΨZ0)]
      exact hΨZ0
    have hprod0 : ((volume : Measure ℝ).prod (volume : Measure ℝ)) P = 0 := by
      rw [← Measure.volume_eq_prod]; exact hpre
    have hslice := MeasureTheory.Measure.measure_ae_null_of_prod_null hprod0
    filter_upwards [hslice] with c hc
    have hseteq : {s : ℝ | Complex.mk c s ∈ W} = Prod.mk c ⁻¹' P := by
      ext s
      simp only [hP, Set.mem_preimage, Complex.measurableEquivRealProd_symm_apply, mem_setOf_eq]
    rw [hseteq]; exact hc
  -- The line map `s ↦ mk c s` and its derivative `I`.
  have hline : ∀ (c s : ℝ), HasDerivWithinAt (fun t : ℝ => Complex.mk c t) Complex.I
      {t : ℝ | Complex.mk c t ∈ T} s := by
    intro c s
    have hHA : HasDerivAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) (1 * Complex.I) s :=
        (Complex.ofRealCLM.hasDerivAt).mul_const Complex.I
      have h3 := (h2.const_add (c : ℂ)); rwa [one_mul] at h3
    have hEq : (fun t : ℝ => Complex.mk c t)
        = (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
      funext t; rw [Complex.mk_eq_add_mul_I]
    rw [hEq]; exact hHA.hasDerivWithinAt
  -- the fiber slice curve and its derivative at good points.
  have hslicederiv : ∀ (c s : ℝ), Complex.mk c s ∈ T →
      (Ψ' (g (Complex.mk c s))).det ≠ 0 →
      HasDerivWithinAt (fun t : ℝ => g (Complex.mk c t)) (Dg (Complex.mk c s) Complex.I)
        {t : ℝ | Complex.mk c t ∈ T} s := by
    intro c s hsT hdetne
    obtain ⟨z, hz, hzeq⟩ := hsT
    have hgw : g (Complex.mk c s) ∈ S := hgmem _ ⟨z, hz, hzeq⟩
    have hDgval : Dg (Complex.mk c s)
        = (((Ψ' (g (Complex.mk c s))).toContinuousLinearEquivOfDetNeZero hdetne).symm
            : ℂ →L[ℝ] ℂ) := by rw [hDg]; exact dif_pos hdetne
    have hgfd : HasFDerivWithinAt g (Dg (Complex.mk c s)) T (Complex.mk c s) := by
      rw [hDgval]
      have := hinvderiv (g (Complex.mk c s)) hgw hdetne
      rwa [hright _ ⟨z, hz, hzeq⟩] at this
    exact hgfd.comp_hasDerivWithinAt s (hline c s) (fun t ht => ht)
  -- the fiber slice curve is Lipschitz on `T_c`.
  have hlineLip : ∀ c : ℝ, LipschitzOnWith 1 (fun t : ℝ => Complex.mk c t)
      {t : ℝ | Complex.mk c t ∈ T} := by
    intro c
    apply LipschitzWith.lipschitzOnWith
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [Complex.dist_eq, Complex.mk_eq_add_mul_I, NNReal.coe_one, one_mul]
    rw [show (c : ℂ) + (x : ℂ) * Complex.I - ((c : ℂ) + (y : ℂ) * Complex.I)
        = ((x : ℂ) - (y : ℂ)) * Complex.I by ring, norm_mul, Complex.norm_I, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  have hsliceLip : ∀ c : ℝ, LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹)
      (fun t : ℝ => g (Complex.mk c t)) {t : ℝ | Complex.mk c t ∈ T} := by
    intro c
    have hcomp : LipschitzOnWith ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹ * 1)
        (g ∘ (fun t : ℝ => Complex.mk c t)) {t : ℝ | Complex.mk c t ∈ T} :=
      hgLip.comp (hlineLip c) (fun t ht => ht)
    rw [mul_one] at hcomp
    exact hcomp
  -- ============================================================
  -- per-`c` slice bound (a.e. c):  μH[1](u⁻¹{c} ∩ S) ≤ ∫⁻ s in T_c, Φ(mk c s).
  -- ============================================================
  have hslicebound : ∀ᵐ c : ℝ, μH[1] (u ⁻¹' {c} ∩ S)
      ≤ ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s) := by
    filter_upwards [hslicenull] with c hcnull
    set Tc : Set ℝ := {t : ℝ | Complex.mk c t ∈ T} with hTc
    have hmkcont : Continuous (fun t : ℝ => Complex.mk c t) := by
      have : (fun t : ℝ => Complex.mk c t)
          = (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
        funext t; rw [Complex.mk_eq_add_mul_I]
      rw [this]; fun_prop
    have hTcmeas : MeasurableSet Tc := by
      rw [hTc]; exact hTmeas.preimage hmkcont.measurable
    -- a measurable null superset of the bad slice parameters.
    set B : Set ℝ := toMeasurable volume {s : ℝ | Complex.mk c s ∈ W} with hB
    have hBmeas : MeasurableSet B := measurableSet_toMeasurable _ _
    have hB0 : volume B = 0 := by rw [hB, measure_toMeasurable]; exact hcnull
    have hBsup : {s : ℝ | Complex.mk c s ∈ W} ⊆ B := subset_toMeasurable _ _
    set Tgood : Set ℝ := Tc \ B with hTgood
    set Tbad : Set ℝ := Tc ∩ B with hTbad
    have hTgood_meas : MeasurableSet Tgood := hTcmeas.diff hBmeas
    -- on `Tgood`, the determinant is nonzero.
    have hgood_det : ∀ t ∈ Tgood, (Ψ' (g (Complex.mk c t))).det ≠ 0 := by
      intro t ht
      obtain ⟨htT, htB⟩ := ht
      intro hdet0
      apply htB
      obtain ⟨z, hz, hzeq⟩ := htT
      have hgS : g (Complex.mk c t) ∈ S := hgmem _ ⟨z, hz, hzeq⟩
      have hgZ : g (Complex.mk c t) ∈ Z :=
        hZsub ⟨by simp only [mem_setOf_eq, not_not]; exact hdet0, hgS⟩
      apply hBsup
      change Complex.mk c t ∈ W
      rw [hW, ← hright _ ⟨z, hz, hzeq⟩]
      exact ⟨g (Complex.mk c t), ⟨hgZ, hgS⟩, rfl⟩
    -- fiber set equality
    have hfiber : u ⁻¹' {c} ∩ S
        = (fun s : ℝ => g (Complex.mk c s)) '' Tc := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_image, mem_setOf_eq, hTc]
      constructor
      · rintro ⟨huc, hzS⟩
        have hΨze : Complex.mk c (Ψ z).im = Ψ z := by
          apply Complex.ext
          · simp [hre z hzS, huc]
          · simp
        exact ⟨(Ψ z).im, by rw [hΨze]; exact ⟨z, hzS, rfl⟩, by rw [hΨze, hleft z hzS]⟩
      · rintro ⟨s, hsT, rfl⟩
        have hgS : g (Complex.mk c s) ∈ S := hgmem _ hsT
        refine ⟨?_, hgS⟩
        rw [← hre _ hgS, hright _ hsT]
    -- image splits  (Tc = Tgood ∪ Tbad)
    have himgsplit : (fun s : ℝ => g (Complex.mk c s)) '' Tc
        = (fun s : ℝ => g (Complex.mk c s)) '' Tgood
          ∪ (fun s : ℝ => g (Complex.mk c s)) '' Tbad := by
      rw [← image_union]
      congr 1
      rw [hTgood, hTbad, diff_union_inter]
    -- good-part Hausdorff bound via arc-length
    have hgoodbound : μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood)
        ≤ ∫⁻ s in Tc, Φ (Complex.mk c s) := by
      calc μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood)
          ≤ ∫⁻ s in Tgood, (‖Dg (Complex.mk c s) Complex.I‖₊ : ℝ≥0∞) := by
            apply hausdorffMeasure_one_image_le hTgood_meas
            intro t ht
            have hdetne := hgood_det t ht
            have htT : Complex.mk c t ∈ T := ht.1
            exact (hslicederiv c t htT hdetne).mono (fun s hs => hs.1)
        _ = ∫⁻ s in Tgood, Φ (Complex.mk c s) := rfl
        _ ≤ ∫⁻ s in Tc, Φ (Complex.mk c s) :=
            lintegral_mono_set (fun t ht => ht.1)
    -- bad-part image is null
    have hbad_null : μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tbad) = 0 := by
      have hHvol : (μH[(1:ℝ)] : Measure ℝ) = volume := hausdorffMeasure_real
      have hTbad_null : μH[1] Tbad = 0 := by
        rw [hHvol]; exact measure_mono_null inter_subset_right hB0
      have hsub : Tbad ⊆ {t : ℝ | Complex.mk c t ∈ T} := fun t ht => ht.1
      refine le_antisymm ?_ (zero_le _)
      calc μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tbad)
          ≤ ((‖(A.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ - δ)⁻¹ : ℝ≥0) ^ (1:ℝ) * μH[1] Tbad :=
            ((hsliceLip c).mono hsub).hausdorffMeasure_image_le (by norm_num)
        _ = 0 := by rw [hTbad_null, mul_zero]
    calc μH[1] (u ⁻¹' {c} ∩ S)
        = μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tc) := by rw [hfiber]
      _ ≤ μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tgood)
            + μH[1] ((fun s : ℝ => g (Complex.mk c s)) '' Tbad) := by
          rw [himgsplit]; exact measure_union_le _ _
      _ ≤ ∫⁻ s in Tc, Φ (Complex.mk c s) := by rw [hbad_null, add_zero]; exact hgoodbound
  -- ============================================================
  -- Fubini:  ∫⁻ c, ∫⁻ s in T_c, Φ(mk c s)  =  ∫⁻ w in T, Φ w.
  -- ============================================================
  have hmkmeas_all : ∀ c : ℝ, Measurable (fun t : ℝ => Complex.mk c t) := by
    intro c
    have hmcomp : Measurable (fun t : ℝ => Complex.measurableEquivRealProd.symm (c, t)) :=
      Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
    have he : (fun t : ℝ => Complex.mk c t)
        = (fun t : ℝ => Complex.measurableEquivRealProd.symm (c, t)) :=
      funext (fun t => (Complex.measurableEquivRealProd_symm_apply (c, t)).symm)
    exact he ▸ hmcomp
  have hFubini : ∫⁻ c : ℝ, ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s)
      = ∫⁻ w in T, Φ w := by
    -- rewrite each slice as a full integral of an indicator.
    have hslice_eq : ∀ c : ℝ,
        ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s)
          = ∫⁻ s : ℝ, (T.indicator Φ) (Complex.mk c s) := by
      intro c
      have hmkmeas : MeasurableSet {t : ℝ | Complex.mk c t ∈ T} :=
        hTmeas.preimage (hmkmeas_all c)
      rw [← lintegral_indicator hmkmeas]
      apply lintegral_congr
      intro s
      by_cases hmem : Complex.mk c s ∈ T
      · rw [indicator_of_mem hmem, indicator_of_mem (show s ∈ {t : ℝ | Complex.mk c t ∈ T}
          from hmem)]
      · rw [indicator_of_notMem hmem, indicator_of_notMem (show s ∉ {t : ℝ | Complex.mk c t ∈ T}
          from hmem)]
    simp_rw [hslice_eq]
    -- Tonelli through the volume-preserving equiv `ℂ ≃ᵐ ℝ × ℝ`.
    have hΦind_meas : AEMeasurable (T.indicator Φ) volume := by
      rw [aemeasurable_indicator_iff hTmeas]
      exact hΦ_meas
    have hsymm_mp : MeasurePreserving Complex.measurableEquivRealProd.symm
        (volume : Measure (ℝ × ℝ)) volume :=
      Complex.volume_preserving_equiv_real_prod.symm _
    have hcomp_meas : AEMeasurable
        (fun p : ℝ × ℝ => (T.indicator Φ) (Complex.measurableEquivRealProd.symm p))
        ((volume : Measure ℝ).prod volume) := by
      have : AEMeasurable
          (fun p : ℝ × ℝ => (T.indicator Φ) (Complex.measurableEquivRealProd.symm p))
          (volume : Measure (ℝ × ℝ)) := by
        apply AEMeasurable.comp_aemeasurable' _
          Complex.measurableEquivRealProd.symm.measurable.aemeasurable
        rw [hsymm_mp.map_eq]; exact hΦind_meas
      rwa [Measure.volume_eq_prod] at this
    calc ∫⁻ c : ℝ, ∫⁻ s : ℝ, (T.indicator Φ) (Complex.mk c s)
        = ∫⁻ p : ℝ × ℝ, (T.indicator Φ) (Complex.measurableEquivRealProd.symm p)
            ∂((volume : Measure ℝ).prod volume) := by
          rw [lintegral_prod _ hcomp_meas]
          apply lintegral_congr; intro c
          apply lintegral_congr; intro s
          rw [Complex.measurableEquivRealProd_symm_apply]
      _ = ∫⁻ w : ℂ, (T.indicator Φ) w := by
          rw [← Measure.volume_eq_prod]
          exact (Complex.volume_preserving_equiv_real_prod.symm _).lintegral_comp_emb
            Complex.measurableEquivRealProd.symm.measurableEmbedding _
      _ = ∫⁻ w in T, Φ w := lintegral_indicator hTmeas _
  -- ============================================================
  -- Area formula:  ∫⁻ w in T, Φ w  =  ∫⁻ z in S, ofReal |det Ψ'z| * Φ(Ψ z).
  -- ============================================================
  have hArea : ∫⁻ w in T, Φ w
      = ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z) := by
    rw [hT]
    exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hΨ' hinj Φ
  -- a.e. on S, the integrand equals `‖fderiv ℝ u z‖₊`.
  have hAreaInt : ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z)
      = ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    apply lintegral_congr_ae
    filter_upwards [hdet_ne, hΦΨ, hfderiv_eq] with z hdetz hΦz hfz
    rw [hΦz, hfz]
    have hdtop : ENNReal.ofReal |(Ψ' z).det| ≠ ⊤ := ENNReal.ofReal_ne_top
    have hd0 : ENNReal.ofReal |(Ψ' z).det| ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos]; exact hdetz
    rw [ENNReal.mul_div_cancel hd0 hdtop]
  -- ============================================================
  -- Combine.
  -- ============================================================
  calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ S)
      ≤ ∫⁻ c : ℝ, ∫⁻ s in {t : ℝ | Complex.mk c t ∈ T}, Φ (Complex.mk c s) :=
        lintegral_mono_ae hslicebound
    _ = ∫⁻ w in T, Φ w := hFubini
    _ = ∫⁻ z in S, ENNReal.ofReal |(Ψ' z).det| * Φ (Ψ z) := hArea
    _ = ∫⁻ z in S, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := hAreaInt

/-- **Critical part of the co-area inequality: the `{∇u = 0}` set contributes nothing.**

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0})) = 0`.

NOT via Sard (which fails for merely Lipschitz `u`). Proof: the non-differentiability set is
`volume`-null (Rademacher), contributing `0` by `coarea_null_le`. For the genuine critical points,
apply the **scalar** Lusin partition `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` to
`u` (with tolerance `δ`): every piece `tₙ` that *contains* a point `z` with `fderiv ℝ u z = 0`
satisfies `‖Aₙ‖ ≤ δ` (since `‖fderiv ℝ u z - Aₙ‖ ≤ δ` and `fderiv ℝ u z = 0`), so `u` is
`2δ`-Lipschitz on `tₙ ∩ A` and `eilenberg_coarea_planar_metric_meas` bounds its contribution by
`2δ · c₀ · volume (tₙ ∩ A)`; pieces with no critical point contribute `0` (empty level-set
intersection). Summing the disjoint pieces gives `≤ 2δ · c₀ · volume A`; let `δ → 0`. (For
`volume A = ∞`, exhaust `A` by finite-measure pieces.) -/
theorem coarea_critical_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0})) = 0 := by
  classical
  have hucont : Continuous u := hu.continuous
  -- The proportionality constant `μH[2] = c₀ • volume`.
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- ===================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets `A'`.
  --      (Dynkin on each compact ball + closed-ball exhaustion; same proof
  --      as in `coarea_set_sharp`.)
  -- ===================================================================
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- ===================================================================
  -- (1)  CORE finite-volume lemma.  For any measurable `E` contained in the
  --      DIFFERENTIABLE critical set with finite area, the level-set integral
  --      vanishes.  (Lusin partition with `Aₙ = fderiv u yₙ = 0`.)
  -- ===================================================================
  have hfin_case : ∀ {E : Set ℂ}, MeasurableSet E → volume E ≠ ∞ →
      E ⊆ {z | fderiv ℝ u z = 0} → E ⊆ {z | DifferentiableAt ℝ u z} →
      ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ E) = 0 := by
    intro E hEmeas hEfin hEcrit hEdiff
    rw [← nonpos_iff_eq_zero]
    -- It suffices to bound the integral by `c₀ * volume E * δ` for every `δ > 0`.
    have key : ∀ δ : ℝ≥0, 0 < δ →
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ E) ≤ (δ : ℝ≥0∞) * (c₀ * volume E) := by
      intro δ δpos
      -- Lusin partition of `E` (as the `s`-set) with tolerance `δ`.
      have hf' : ∀ x ∈ E, HasFDerivWithinAt u (fderiv ℝ u x) E x := by
        intro x hx
        exact (hEdiff hx).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, A, hdisj, htmeas, hsub, happrox, hAval⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
          u E (fun z => fderiv ℝ u z) hf' (fun _ => δ) (fun _ => δpos.ne')
      -- For each `n`, `u` is `δ`-Lipschitz on `E ∩ t n`.
      have hpiece_meas : ∀ n, MeasurableSet (E ∩ t n) :=
        fun n => hEmeas.inter (htmeas n)
      have hpiece_lip : ∀ n, LipschitzOnWith δ u (E ∩ t n) := by
        intro n
        rcases eq_or_ne E ∅ with hEempty | hEne
        · -- `E = ∅`: piece empty.
          rw [hEempty]; simp only [Set.empty_inter]
          exact lipschitzOnWith_empty δ u
        · -- `A n = fderiv u y n = 0` for `y n ∈ E ⊆ Crit`.
          obtain ⟨y, hyE, hAy⟩ := hAval (Set.nonempty_iff_ne_empty.2 hEne) n
          have hA0 : A n = 0 := by rw [hAy]; exact hEcrit hyE
          -- `ApproximatesLinearOn u 0 (E ∩ t n) δ` ⟹ `LipschitzOnWith δ u (E ∩ t n)`.
          have hap : ApproximatesLinearOn u (A n) (E ∩ t n) δ := happrox n
          rw [hA0] at hap
          have hlip := hap.lipschitzOnWith
          have hsub0 : (u - ⇑(0 : ℂ →L[ℝ] ℝ)) = u := by
            funext z; simp
          rwa [hsub0] at hlip
      -- Per-piece Eilenberg bound.
      have hpiece_bound : ∀ n,
          ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n))
            ≤ (δ : ℝ≥0∞) * (c₀ * volume (E ∩ t n)) := by
        intro n
        have hb := eilenberg_coarea_planar_metric_meas (hpiece_lip n) (hpiece_meas n)
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hb
        exact hb
      -- Assemble via disjoint additivity of the slice measure.
      have hslice_eq : ∀ c : ℝ,
          μH[1] (u ⁻¹' {c} ∩ E) = ∑' n, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n)) := by
        intro c
        have hcover_c : u ⁻¹' {c} ∩ E = ⋃ n, u ⁻¹' {c} ∩ (E ∩ t n) := by
          rw [← Set.inter_iUnion]
          congr 1
          apply Set.Subset.antisymm
          · intro z hz
            obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hsub hz)
            exact Set.mem_iUnion.2 ⟨n, hz, hn⟩
          · exact Set.iUnion_subset (fun n => Set.inter_subset_left)
        rw [hcover_c]
        refine measure_iUnion ?_ ?_
        · intro i j hij
          refine (hdisj hij).mono ?_ ?_ <;>
            exact fun z hz => hz.2.2
        · intro n
          exact (hucont.measurable (measurableSet_singleton c)).inter (hpiece_meas n)
      calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ E)
          = ∫⁻ c, ∑' n, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n)) := by
            apply lintegral_congr; exact hslice_eq
        _ = ∑' n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (E ∩ t n)) :=
            lintegral_tsum (fun n => slice_aemeas (hpiece_meas n))
        _ ≤ ∑' n, (δ : ℝ≥0∞) * (c₀ * volume (E ∩ t n)) :=
            ENNReal.tsum_le_tsum hpiece_bound
        _ = (δ : ℝ≥0∞) * (c₀ * ∑' n, volume (E ∩ t n)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        _ = (δ : ℝ≥0∞) * (c₀ * volume E) := by
            congr 2
            rw [← measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_right
              Set.inter_subset_right) (fun n => hpiece_meas n)]
            congr 1
            apply Set.Subset.antisymm
            · exact Set.iUnion_subset (fun n => Set.inter_subset_left)
            · intro z hz
              obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hsub hz)
              exact Set.mem_iUnion.2 ⟨n, hz, hn⟩
    -- Let `δ → 0`:  if the integral were positive, pick `δ` with `δ * C < integral`.
    have hconst_fin : c₀ * volume E ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hEfin
    by_contra hpos
    rw [nonpos_iff_eq_zero] at hpos
    obtain ⟨δ, δpos, hδlt⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt hconst_fin hpos
    exact absurd (key δ δpos) (not_le_of_gt hδlt)
  -- ===================================================================
  -- (2)  Assembly.  Split the critical set into the differentiable core `D`
  --      and the (volume-null) non-differentiable part `ND`.
  -- ===================================================================
  set Crit : Set ℂ := {z | fderiv ℝ u z = 0} with hCrit_def
  set Diff : Set ℂ := {z | DifferentiableAt ℝ u z} with hDiff_def
  have hCrit_meas : MeasurableSet Crit :=
    measurable_fderiv ℝ u (measurableSet_singleton _)
  have hDiff_meas : MeasurableSet Diff := measurableSet_of_differentiableAt ℝ u
  -- Non-differentiable part is `volume`-null (Rademacher).
  have hND0 : volume (A ∩ Diffᶜ) = 0 := by
    have hDiffc0 : volume (Diffᶜ) = 0 := by
      have hae : ∀ᵐ z, DifferentiableAt ℝ u z := hu.ae_differentiableAt
      have hae' : ∀ᵐ z, z ∉ (Diffᶜ : Set ℂ) := by
        filter_upwards [hae] with z hz
        simp only [hDiff_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
        exact hz
      have := (MeasureTheory.ae_iff).1 hae'
      simpa only [not_not, Set.setOf_mem_eq] using this
    exact measure_mono_null Set.inter_subset_right hDiffc0
  -- On `Diffᶜ`, `fderiv u = 0`, so `Diffᶜ ⊆ Crit` and `A ∩ Crit = D ∪ (A ∩ Diffᶜ)`.
  have hNDsubCrit : Diffᶜ ⊆ Crit := by
    intro z hz
    simp only [hCrit_def, Set.mem_setOf_eq]
    exact fderiv_zero_of_not_differentiableAt hz
  have hsplit : A ∩ Crit = (A ∩ Crit ∩ Diff) ∪ (A ∩ Diffᶜ) := by
    apply Set.Subset.antisymm
    · intro z ⟨hzA, hzC⟩
      by_cases hzD : z ∈ Diff
      · exact Or.inl ⟨⟨hzA, hzC⟩, hzD⟩
      · exact Or.inr ⟨hzA, hzD⟩
    · rintro z (⟨⟨hzA, hzC⟩, _⟩ | ⟨hzA, hzD⟩)
      · exact ⟨hzA, hzC⟩
      · exact ⟨hzA, hNDsubCrit hzD⟩
  -- The non-differentiable contribution vanishes.
  have hND_int : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Diffᶜ)) = 0 :=
    coarea_null_le hu (hA.inter hDiff_meas.compl) hND0
  -- The differentiable critical contribution vanishes (exhaust by balls).
  set D : Set ℂ := A ∩ Crit ∩ Diff with hD_def
  have hD_meas : MeasurableSet D := (hA.inter hCrit_meas).inter hDiff_meas
  have hD_int : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ D) = 0 := by
    -- Exhaust `D` by `Dₘ := D ∩ closedBall 0 m`, each of finite measure.
    set Dm : ℕ → Set ℂ := fun m => D ∩ Metric.closedBall (0:ℂ) m with hDm_def
    have hDm_meas : ∀ m, MeasurableSet (Dm m) :=
      fun m => hD_meas.inter measurableSet_closedBall
    have hDm_fin : ∀ m, volume (Dm m) ≠ ∞ := by
      intro m
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.inter_subset_right))
      exact (isCompact_closedBall (0:ℂ) (m:ℝ)).measure_lt_top.ne
    have hDm_crit : ∀ m, Dm m ⊆ Crit := by
      intro m z hz; exact hz.1.1.2
    have hDm_diff : ∀ m, Dm m ⊆ Diff := by
      intro m z hz; exact hz.1.2
    have hDm_zero : ∀ m, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Dm m) = 0 :=
      fun m => hfin_case (hDm_meas m) (hDm_fin m) (hDm_crit m) (hDm_diff m)
    -- `μH[1] (u⁻¹{c} ∩ D) = ⨆ m, μH[1] (u⁻¹{c} ∩ Dₘ)` (monotone union).
    have hball_mono : Monotone (fun m : ℕ => Metric.closedBall (0:ℂ) (m:ℝ)) :=
      fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    have hpt : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ D) = ⨆ m : ℕ, μH[1] (u ⁻¹' {c} ∩ Dm m) := by
      intro c
      have hmono : Monotone (fun m : ℕ => u ⁻¹' {c} ∩ Dm m) :=
        fun a b hab => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hab))
      have hunion : (⋃ m : ℕ, u ⁻¹' {c} ∩ Dm m) = u ⁻¹' {c} ∩ D := by
        apply Set.Subset.antisymm
        · refine Set.iUnion_subset (fun m => ?_)
          intro z ⟨hzc, hzD, _⟩
          exact ⟨hzc, hzD⟩
        · intro z ⟨hzc, hzD⟩
          obtain ⟨N, hN⟩ : ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
            obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
            exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
          exact Set.mem_iUnion.2 ⟨N, hzc, hzD, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ D)
        = ∫⁻ c, ⨆ m : ℕ, μH[1] (u ⁻¹' {c} ∩ Dm m) := by
          apply lintegral_congr; exact hpt
      _ = ⨆ m : ℕ, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Dm m) := by
          refine lintegral_iSup' (fun m => slice_aemeas (hDm_meas m)) ?_
          filter_upwards with c
          intro a b hab
          exact measure_mono (Set.inter_subset_inter_right _
            (Set.inter_subset_inter_right _ (hball_mono hab)))
      _ = 0 := by simp only [hDm_zero, iSup_const]
  -- Combine.  Each level slice of `A ∩ Crit` splits into the `D`-slice and the `ND`-slice.
  have hslice_split : ∀ c : ℝ, u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0})
      = (u ⁻¹' {c} ∩ D) ∪ (u ⁻¹' {c} ∩ (A ∩ Diffᶜ)) := by
    intro c
    rw [← Set.inter_union_distrib_left, ← hsplit]
  have hbound : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z = 0}))
      ≤ ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ D) + μH[1] (u ⁻¹' {c} ∩ (A ∩ Diffᶜ))) := by
    refine lintegral_mono (fun c => ?_)
    rw [hslice_split c]
    exact measure_union_le _ _
  rw [← nonpos_iff_eq_zero]
  refine le_trans hbound (le_of_eq ?_)
  -- Both slice integrals vanish, so each slice is `0` a.e., hence the sum-integral is `0`.
  have hD_ae : (fun c => μH[1] (u ⁻¹' {c} ∩ D)) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff' (slice_aemeas hD_meas)).1 hD_int
  have hND_ae : (fun c => μH[1] (u ⁻¹' {c} ∩ (A ∩ Diffᶜ))) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff' (slice_aemeas (hA.inter hDiff_meas.compl))).1 hND_int
  rw [lintegral_eq_zero_iff'
    ((slice_aemeas hD_meas).add (slice_aemeas (hA.inter hDiff_meas.compl)))]
  filter_upwards [hD_ae, hND_ae] with c hc hcn
  simp only [Pi.zero_apply] at hc hcn ⊢
  rw [hc, hcn, add_zero]

/-- **Regular part of the co-area inequality (the area-formula assembly over `{∇u ≠ 0}`).**

`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) ≤ ∫⁻ z in A, ‖fderiv ℝ u z‖₊`.

Proof: split `{∇u ≠ 0} = {∂u/∂x ≠ 0} ∪ ({∂u/∂x = 0} ∩ {∂u/∂y ≠ 0})`. On the first, the square map
`Ψ = (u, im)` has `det Ψ' = ∂u/∂x ≠ 0`; on the second use `Ψ = (u, re)`. Partition each via the
Lusin decomposition `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` of `Ψ` into
DISJOINT measurable pieces on which `Ψ` is `ApproximatesLinearOn` an invertible `Aₙ` with tolerance
`δ < ‖Aₙ.symm‖₊⁻¹`, apply `coarea_piece_le` per piece (`∫⁻ c, μH[1] (u⁻¹{c} ∩ Sₙ) ≤ ∫⁻ Sₙ ‖∇u‖`),
and sum the disjoint pieces (`lintegral_tsum`, `μH[1]` additivity) to `∫⁻ z in A, ‖∇u z‖₊` (the
integrand vanishes on `{∇u = 0}`, so integrating over `A` not `A ∩ {∇u ≠ 0}` is harmless). -/
theorem coarea_regular_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0}))
      ≤ ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
  classical
  have hucont : Continuous u := hu.continuous
  obtain ⟨c₀, hc₀pos, hc₀v⟩ := hausdorffMeasure_two_complex_smul_volume
  -- =====================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets `A'`.
  --      (Dynkin on each compact ball + closed-ball exhaustion; copied from
  --      `coarea_set_sharp` / `coarea_critical_le`.)
  -- =====================================================================
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        rw [hc₀v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- =====================================================================
  -- (1)  The per-bounded-piece coordinate engine.  Given a square map `Ψ` with
  --      global derivative `Ψ'` at differentiable points, `.re = u`, and
  --      nonzero determinant on a bounded measurable `s` of differentiability,
  --      the slice integral over `s` is bounded by `∫⁻ s ‖∇u‖`, by the Lusin
  --      partition into invertible `ApproximatesLinearOn` pieces + `coarea_piece_le`.
  -- =====================================================================
  have hcoord_core : ∀ (Ψ : ℂ → ℂ) (Ψ' : ℂ → (ℂ →L[ℝ] ℂ)),
      (∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψ (Ψ' z) z) →
      (∀ z, (Ψ z).re = u z) →
      ∀ (s : Set ℂ), MeasurableSet s → Bornology.IsBounded s →
        (∀ z ∈ s, DifferentiableAt ℝ u z) → (∀ z ∈ s, (Ψ' z).det ≠ 0) →
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ s) ≤ ∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    intro Ψ Ψ' hΨfd hΨre s hsmeas hsb hsdiff hsdet
    have hΨ'_s : ∀ z ∈ s, HasFDerivWithinAt Ψ (Ψ' z) s z :=
      fun z hz => (hΨfd z (hsdiff z hz)).hasFDerivWithinAt
    set r : (ℂ →L[ℝ] ℂ) → NNReal := fun A' =>
      if h : A'.det ≠ 0 then
        ‖((A'.toContinuousLinearEquivOfDetNeZero h).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
      else 1 with hr
    have hrpos : ∀ A', r A' ≠ 0 := by
      intro A'
      simp only [hr]
      split_ifs with h
      · set B := A'.toContinuousLinearEquivOfDetNeZero h
        have hBsymm : (B.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
          intro hz
          have h1 : B.symm (B 1) = 1 := B.symm_apply_apply 1
          rw [show B.symm (B 1) = (B.symm : ℂ →L[ℝ] ℂ) (B 1) from rfl, hz] at h1
          simp at h1
        have hnorm_pos : 0 < ‖(B.symm : ℂ →L[ℝ] ℂ)‖₊ := by
          rw [pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
        positivity
      · exact one_ne_zero
    obtain ⟨t, A, hdisj, htmeas, hsub, happrox, hAval⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
        Ψ s Ψ' hΨ'_s r (fun A' => hrpos A')
    have hpiece_meas : ∀ n, MeasurableSet (s ∩ t n) := fun n => hsmeas.inter (htmeas n)
    have hpiece_bd : ∀ n, Bornology.IsBounded (s ∩ t n) :=
      fun n => hsb.subset Set.inter_subset_left
    have hpiece_bound : ∀ n,
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) ≤ ∫⁻ z in s ∩ t n, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
      intro n
      rcases Set.eq_empty_or_nonempty (s ∩ t n) with hempty | hne
      · rw [show (fun c : ℝ => μH[1] (u ⁻¹' {c} ∩ (s ∩ t n))) = fun _ => 0 by
          funext c; rw [hempty]; simp]
        simp
      · obtain ⟨y, hy, hAy⟩ := hAval ⟨hne.choose, hne.choose_spec.1⟩ n
        have hAdet : (A n).det ≠ 0 := by rw [hAy]; exact hsdet y hy
        set Bequiv := (A n).toContinuousLinearEquivOfDetNeZero hAdet
        have hAeq : ((A n) : ℂ →L[ℝ] ℂ) = (Bequiv : ℂ →L[ℝ] ℂ) :=
          ((A n).coe_toContinuousLinearEquivOfDetNeZero hAdet).symm
        have hrlt : r (A n) < ‖(Bequiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
          simp only [hr, dif_pos hAdet]
          have hBsymm : (Bequiv.symm : ℂ →L[ℝ] ℂ) ≠ 0 := by
            intro hz
            have h1 : Bequiv.symm (Bequiv 1) = 1 := Bequiv.symm_apply_apply 1
            rw [show Bequiv.symm (Bequiv 1) = (Bequiv.symm : ℂ →L[ℝ] ℂ) (Bequiv 1) from rfl, hz]
              at h1
            simp at h1
          have hnorm_pos : (0 : NNReal) < ‖(Bequiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
            rw [inv_pos, pos_iff_ne_zero]; simpa [nnnorm_eq_zero] using hBsymm
          exact NNReal.half_lt_self (ne_of_gt hnorm_pos)
        have happrox' : ApproximatesLinearOn Ψ (Bequiv : ℂ →L[ℝ] ℂ) (s ∩ t n) (r (A n)) := by
          rw [← hAeq]; exact happrox n
        exact coarea_piece_le (hpiece_meas n) (hpiece_bd n) hrlt happrox'
          (fun z hz => (hΨfd z (hsdiff z hz.1)).hasFDerivWithinAt)
          (fun z _ => hΨre z)
          (fun z hz => hsdiff z hz.1)
    have hslice_eq : ∀ c : ℝ,
        μH[1] (u ⁻¹' {c} ∩ s) = ∑' n, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := by
      intro c
      have hcover_c : u ⁻¹' {c} ∩ s = ⋃ n, u ⁻¹' {c} ∩ (s ∩ t n) := by
        rw [← Set.inter_iUnion]
        congr 1
        apply Set.Subset.antisymm
        · intro z hz
          obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hsub hz)
          exact Set.mem_iUnion.2 ⟨n, hz, hn⟩
        · exact Set.iUnion_subset (fun n => Set.inter_subset_left)
      rw [hcover_c]
      refine measure_iUnion ?_ ?_
      · intro i j hij
        refine (hdisj hij).mono ?_ ?_ <;> exact fun z hz => hz.2.2
      · intro n
        exact (hucont.measurable (measurableSet_singleton c)).inter (hpiece_meas n)
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ s)
        = ∫⁻ c, ∑' n, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) := by
          apply lintegral_congr; exact hslice_eq
      _ = ∑' n, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (s ∩ t n)) :=
          lintegral_tsum (fun n => slice_aemeas (hpiece_meas n))
      _ ≤ ∑' n, ∫⁻ z in s ∩ t n, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
          ENNReal.tsum_le_tsum hpiece_bound
      _ = ∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
          have hcvr : s = ⋃ n, (s ∩ t n) := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.2 hsub).symm
          rw [show (∫⁻ z in s, (‖fderiv ℝ u z‖₊ : ℝ≥0∞))
              = ∫⁻ z in ⋃ n, (s ∩ t n), (‖fderiv ℝ u z‖₊ : ℝ≥0∞) from by rw [← hcvr]]
          rw [lintegral_iUnion (fun n => hpiece_meas n)
            (fun i j hij => (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)]
  -- =====================================================================
  -- (2)  The per-coordinate full bound (exhaust the unbounded `A ∩ Q` by balls,
  --      apply `hcoord_core` on each bounded piece, sum via monotone convergence).
  -- =====================================================================
  have hcoord_full : ∀ (Ψ : ℂ → ℂ) (Ψ' : ℂ → (ℂ →L[ℝ] ℂ)),
      (∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψ (Ψ' z) z) →
      (∀ z, (Ψ z).re = u z) →
      ∀ (Q : Set ℂ), MeasurableSet Q →
        (∀ z ∈ A ∩ Q, DifferentiableAt ℝ u z) → (∀ z ∈ A ∩ Q, (Ψ' z).det ≠ 0) →
        ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Q)) ≤ ∫⁻ z in A ∩ Q, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
    intro Ψ Ψ' hΨfd hΨre Q hQmeas hAQdiff hAQdet
    set R : Set ℂ := A ∩ Q with hR_def
    have hRmeas : MeasurableSet R := hA.inter hQmeas
    set Rm : ℕ → Set ℂ := fun m => R ∩ Metric.closedBall (0:ℂ) m with hRm_def
    have hRm_meas : ∀ m, MeasurableSet (Rm m) := fun m => hRmeas.inter measurableSet_closedBall
    have hRm_bd : ∀ m, Bornology.IsBounded (Rm m) :=
      fun m => (Metric.isBounded_closedBall).subset Set.inter_subset_right
    have hball_mono : Monotone (fun m : ℕ => Metric.closedBall (0:ℂ) (m:ℝ)) :=
      fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    have hRm_mono : Monotone Rm :=
      fun a b hab => Set.inter_subset_inter_right _ (hball_mono hab)
    have hRcover : (⋃ m, Rm m) = R := by
      apply Set.Subset.antisymm (Set.iUnion_subset (fun m => Set.inter_subset_left))
      intro z hz
      obtain ⟨N, hN⟩ : ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
        exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
      exact Set.mem_iUnion.2 ⟨N, hz, hN⟩
    have hRm_diff : ∀ m, ∀ z ∈ Rm m, DifferentiableAt ℝ u z :=
      fun m z hz => hAQdiff z hz.1
    have hRm_det : ∀ m, ∀ z ∈ Rm m, (Ψ' z).det ≠ 0 :=
      fun m z hz => hAQdet z hz.1
    have hLHS : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ R)
        = ⨆ m, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m) := by
      have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ R)
          = ⨆ m, μH[1] (u ⁻¹' {c} ∩ Rm m) := by
        intro c
        have hmono : Monotone (fun m : ℕ => u ⁻¹' {c} ∩ Rm m) :=
          fun a b hab => Set.inter_subset_inter_right _ (hRm_mono hab)
        have hu2 : (⋃ m, u ⁻¹' {c} ∩ Rm m) = u ⁻¹' {c} ∩ R := by
          rw [← Set.inter_iUnion, hRcover]
        rw [← hu2, hmono.measure_iUnion]
      calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ R)
          = ∫⁻ c, ⨆ m, μH[1] (u ⁻¹' {c} ∩ Rm m) := by apply lintegral_congr; exact hpt
        _ = ⨆ m, ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m) := by
            refine lintegral_iSup' (fun m => slice_aemeas (hRm_meas m)) ?_
            filter_upwards with c
            intro a b hab
            exact measure_mono (Set.inter_subset_inter_right _ (hRm_mono hab))
    rw [hLHS]
    apply iSup_le
    intro m
    calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ Rm m)
        ≤ ∫⁻ z in Rm m, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
          hcoord_core Ψ Ψ' hΨfd hΨre (Rm m) (hRm_meas m) (hRm_bd m)
            (hRm_diff m) (hRm_det m)
      _ ≤ ∫⁻ z in R, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := lintegral_mono_set Set.inter_subset_left
  -- =====================================================================
  -- (3)  Build the two coordinate maps (`Ψ_im` over `∂u/∂x ≠ 0`, `Ψ_re` over
  --      `∂u/∂x = 0 ∧ ∂u/∂y ≠ 0`) and apply `hcoord_full`.
  -- =====================================================================
  set Diff : Set ℂ := {z | DifferentiableAt ℝ u z} with hDiff_def
  have hDiff_meas : MeasurableSet Diff := measurableSet_of_differentiableAt ℝ u
  set P1 : Set ℂ := {z | (fderiv ℝ u z) (1:ℂ) ≠ 0} with hP1_def
  set P2 : Set ℂ := {z | (fderiv ℝ u z) (1:ℂ) = 0 ∧ (fderiv ℝ u z) Complex.I ≠ 0} with hP2_def
  have hP1_meas : MeasurableSet P1 :=
    (measurableSet_singleton (0:ℝ)).compl.preimage
      ((measurable_fderiv ℝ u).apply_continuousLinearMap (1:ℂ))
  have hP2_meas : MeasurableSet P2 := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton (0:ℝ)).preimage
        ((measurable_fderiv ℝ u).apply_continuousLinearMap (1:ℂ))
    · exact (measurableSet_singleton (0:ℝ)).compl.preimage
        ((measurable_fderiv ℝ u).apply_continuousLinearMap Complex.I)
  have hNECrit_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} :=
    (measurable_fderiv ℝ u) (measurableSet_singleton (0)).compl
  -- `Ψ_im z = u z • 1 + z.im • I`, derivative `(∇u).smulRight 1 + imCLM.smulRight I`,
  -- `det = ∂u/∂x = (∇u) 1`.
  set Ψim : ℂ → ℂ := fun w => (u w : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I with hΨim
  set Ψim' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I with hΨim'
  have hΨim_fd : ∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψim (Ψim' z) z := by
    intro z hu_z
    have hPG : HasFDerivAt (fun w : ℂ => u w) (fderiv ℝ u z) z := hu_z.hasFDerivAt
    set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
    have hcomp1 : HasFDerivAt (fun w : ℂ => (u w : ℝ) • (1 : ℂ))
        (LP1.comp (fderiv ℝ u z)) z := by
      have := LP1.hasFDerivAt.comp z hPG; convert this using 1
    set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
    have hcomp2 : HasFDerivAt (fun w : ℂ => (w.im : ℝ) • Complex.I)
        (LQI.comp Complex.imCLM) z := by
      have := LQI.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt; convert this using 1
    have hsum := hcomp1.add hcomp2
    rw [hΨim, hΨim']; convert hsum using 1
  have hΨim_re : ∀ z, (Ψim z).re = u z := by
    intro z; rw [hΨim]; simp [Complex.real_smul]
  have hΨim_det : ∀ z, (Ψim' z).det = (fderiv ℝ u z) (1:ℂ) := by
    intro z
    rw [hΨim']
    set D : ℂ →L[ℝ] ℂ :=
      (((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.imCLM.smulRight Complex.I) with hD
    rw [show D.det
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
      (LinearMap.det_toMatrix Complex.basisOneI _).symm]
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : D 1 = ((fderiv ℝ u z) (1:ℂ) : ℂ) := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.one_im, zero_smul,
        add_zero]
      change ((fderiv ℝ u z) (1:ℂ) : ℝ) • (1 : ℂ) = (((fderiv ℝ u z) (1:ℂ) : ℝ) : ℂ); simp
    have h2 : D Complex.I = ((fderiv ℝ u z) Complex.I : ℂ) + Complex.I := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.imCLM_apply, Complex.I_im, one_smul]
      change ((fderiv ℝ u z) Complex.I : ℝ) • (1 : ℂ) + Complex.I
        = (((fderiv ℝ u z) Complex.I : ℝ) : ℂ) + Complex.I; simp
    change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = (fderiv ℝ u z) (1:ℂ)
    rw [h1, h2]; simp
  -- `Ψ_re z = u z • 1 + z.re • I`, derivative `(∇u).smulRight 1 + reCLM.smulRight I`,
  -- `det = -∂u/∂y = -(∇u) I`.
  set Ψre : ℂ → ℂ := fun w => (u w : ℝ) • (1 : ℂ) + (w.re : ℝ) • Complex.I with hΨre_def
  set Ψre' : ℂ → (ℂ →L[ℝ] ℂ) := fun z =>
    ((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.reCLM.smulRight Complex.I with hΨre'
  have hΨre_fd : ∀ z, DifferentiableAt ℝ u z → HasFDerivAt Ψre (Ψre' z) z := by
    intro z hu_z
    have hPG : HasFDerivAt (fun w : ℂ => u w) (fderiv ℝ u z) z := hu_z.hasFDerivAt
    set LP1 : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight (1 : ℂ) with hLP1
    have hcomp1 : HasFDerivAt (fun w : ℂ => (u w : ℝ) • (1 : ℂ))
        (LP1.comp (fderiv ℝ u z)) z := by
      have := LP1.hasFDerivAt.comp z hPG; convert this using 1
    set LQI : ℝ →L[ℝ] ℂ := (1 : ℝ →L[ℝ] ℝ).smulRight Complex.I with hLQI
    have hcomp2 : HasFDerivAt (fun w : ℂ => (w.re : ℝ) • Complex.I)
        (LQI.comp Complex.reCLM) z := by
      have := LQI.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt; convert this using 1
    have hsum := hcomp1.add hcomp2
    rw [hΨre_def, hΨre']; convert hsum using 1
  have hΨre_re : ∀ z, (Ψre z).re = u z := by
    intro z; rw [hΨre_def]; simp [Complex.real_smul]
  have hΨre_det : ∀ z, (Ψre' z).det = - (fderiv ℝ u z) Complex.I := by
    intro z
    rw [hΨre']
    set D : ℂ →L[ℝ] ℂ :=
      (((fderiv ℝ u z).smulRight (1 : ℂ)) + Complex.reCLM.smulRight Complex.I) with hD
    rw [show D.det
        = Matrix.det (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (D : ℂ →ₗ[ℝ] ℂ)) from
      (LinearMap.det_toMatrix Complex.basisOneI _).symm]
    rw [Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : D 1 = ((fderiv ℝ u z) (1:ℂ) : ℂ) + Complex.I := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.one_re, one_smul]
      change ((fderiv ℝ u z) (1:ℂ) : ℝ) • (1 : ℂ) + Complex.I
        = (((fderiv ℝ u z) (1:ℂ) : ℝ) : ℂ) + Complex.I; simp
    have h2 : D Complex.I = ((fderiv ℝ u z) Complex.I : ℂ) := by
      simp only [hD, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.I_re, zero_smul, add_zero]
      change ((fderiv ℝ u z) Complex.I : ℝ) • (1 : ℂ) = (((fderiv ℝ u z) Complex.I : ℝ) : ℂ); simp
    change (D 1).re * (D Complex.I).im - (D Complex.I).re * (D 1).im = - (fderiv ℝ u z) Complex.I
    rw [h1, h2]; simp
  -- Membership in `P1`/`P2` (with nonzero partial) forces differentiability.
  have hP1diff : ∀ z ∈ A ∩ P1, DifferentiableAt ℝ u z := by
    rintro z ⟨_, hz1⟩
    by_contra hnd
    apply hz1
    rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hP2diff : ∀ z ∈ A ∩ P2, DifferentiableAt ℝ u z := by
    rintro z ⟨_, _, hz2⟩
    by_contra hnd
    apply hz2
    rw [fderiv_zero_of_not_differentiableAt hnd]; simp
  have hP1det : ∀ z ∈ A ∩ P1, (Ψim' z).det ≠ 0 := by
    rintro z ⟨_, hz1⟩; rw [hΨim_det]; exact hz1
  have hP2det : ∀ z ∈ A ∩ P2, (Ψre' z).det ≠ 0 := by
    rintro z ⟨_, _, hz2⟩
    rw [hΨre_det]
    simp only [neg_ne_zero]; exact hz2
  have hbound_P1 : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P1))
      ≤ ∫⁻ z in A ∩ P1, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
    hcoord_full Ψim Ψim' hΨim_fd hΨim_re P1 hP1_meas hP1diff hP1det
  have hbound_P2 : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P2))
      ≤ ∫⁻ z in A ∩ P2, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
    hcoord_full Ψre Ψre' hΨre_fd hΨre_re P2 hP2_meas hP2diff hP2det
  -- =====================================================================
  -- (4)  Assemble the reduction.  The non-differentiable part is `volume`-null
  --      (Rademacher) and contributes `0`; the differentiable part of `{∇u ≠ 0}`
  --      splits into the (disjoint) `P1`/`P2` pieces, each bounded above.
  -- =====================================================================
  have hND0 : volume (A ∩ Diffᶜ) = 0 := by
    have hDiffc0 : volume (Diffᶜ) = 0 := by
      have hae : ∀ᵐ z, DifferentiableAt ℝ u z := hu.ae_differentiableAt
      have hae' : ∀ᵐ z, z ∉ (Diffᶜ : Set ℂ) := by
        filter_upwards [hae] with z hz
        simp only [hDiff_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_not]; exact hz
      have := (MeasureTheory.ae_iff).1 hae'
      simpa only [not_not, Set.setOf_mem_eq] using this
    exact measure_mono_null Set.inter_subset_right hDiffc0
  have hND_int : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) = 0 := by
    apply coarea_null_le hu ((hA.inter hNECrit_meas).inter hDiff_meas.compl)
    exact measure_mono_null (by intro z hz; exact ⟨hz.1.1, hz.2⟩) hND0
  have hsplit_slice : ∀ c : ℝ,
      μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0}))
        ≤ μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
          + μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) := by
    intro c
    rw [show u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})
        = (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
          ∪ (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) from by
      rw [← Set.inter_union_distrib_left]
      congr 1
      rw [Set.inter_union_compl]]
    exact measure_union_le _ _
  have hDiffsub : ∀ c : ℝ,
      μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
        ≤ μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)) + μH[1] (u ⁻¹' {c} ∩ (A ∩ P2)) := by
    intro c
    have hsub : u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)
        ⊆ (u ⁻¹' {c} ∩ (A ∩ P1)) ∪ (u ⁻¹' {c} ∩ (A ∩ P2)) := by
      rintro z ⟨hzc, ⟨hzA, hzne⟩, hzD⟩
      by_cases hp1 : (fderiv ℝ u z) (1:ℂ) ≠ 0
      · exact Or.inl ⟨hzc, hzA, hp1⟩
      · have hp1' : (fderiv ℝ u z) (1:ℂ) = 0 := not_not.mp hp1
        have hI : (fderiv ℝ u z) Complex.I ≠ 0 := by
          intro hI0
          apply hzne
          ext w
          have hw : w = w.re • (1:ℂ) + w.im • Complex.I := by
            apply Complex.ext <;> simp [Complex.real_smul]
          rw [hw, map_add, map_smul, map_smul, hp1', hI0]; simp
        exact Or.inr ⟨hzc, hzA, hp1', hI⟩
    exact le_trans (measure_mono hsub) (measure_union_le _ _)
  have hdisjP : Disjoint (A ∩ P1) (A ∩ P2) := by
    rw [Set.disjoint_left]
    rintro z ⟨_, hz1⟩ ⟨_, hz2, _⟩
    exact hz1 hz2
  calc ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0}))
      ≤ ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff))
            + μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ))) :=
        lintegral_mono hsplit_slice
    _ = (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)))
          + ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diffᶜ)) := by
        rw [lintegral_add_left' (slice_aemeas ((hA.inter hNECrit_meas).inter hDiff_meas))]
    _ = ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0} ∩ Diff)) := by
        rw [hND_int, add_zero]
    _ ≤ ∫⁻ c, (μH[1] (u ⁻¹' {c} ∩ (A ∩ P1)) + μH[1] (u ⁻¹' {c} ∩ (A ∩ P2))) :=
        lintegral_mono hDiffsub
    _ = (∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P1))) + ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ P2)) := by
        rw [lintegral_add_left' (slice_aemeas (hA.inter hP1_meas))]
    _ ≤ (∫⁻ z in A ∩ P1, (‖fderiv ℝ u z‖₊ : ℝ≥0∞))
          + ∫⁻ z in A ∩ P2, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) :=
        add_le_add hbound_P1 hbound_P2
    _ ≤ ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) := by
        rw [← lintegral_union (hA.inter hP2_meas) hdisjP]
        apply lintegral_mono_set
        rw [← Set.inter_union_distrib_left]
        exact Set.inter_subset_left

/-- **Sharp planar co-area inequality, unweighted set form (the area-formula assembly).**

For a `K`-Lipschitz `u : ℂ → ℝ` and a measurable set `A ⊆ ℂ`,
`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ ∫⁻ z in A, ‖fderiv ℝ u z‖₊ ∂volume`.

This is the gradient-sharp co-area inequality for indicator weights; the general gradient form
`eilenberg_coarea_grad_le` follows from it by the layer-cake / monotone-class approximation of `g`.

## Truth and proof

**TRUE**, one-sided `≤`. Split `A` along `Crit = {z | fderiv ℝ u z = 0}` and `Reg = Critᶜ`. The
critical slice `c ↦ μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit))` integrates to `0` (`coarea_critical_le`) and is
`≥ 0`, hence vanishes for a.e. `c`; so for a.e. `c` the level set restricted to `A` reduces to its
regular part, and `∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) = ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Reg))`, which is
bounded by `∫⁻ z in A, ‖fderiv ℝ u z‖₊` (`coarea_regular_le`, the area-formula assembly over the
non-critical set). The Besicovitch-differentiation route is avoided: the sharp local density is not
controlled by mere differentiability (`|z|² sin (1/|z|)` is a counterexample), so the genuine proof
is the Lusin-decomposition + area-formula one carried by `coarea_piece_le`. -/
theorem coarea_set_sharp {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {A : Set ℂ} (hA : MeasurableSet A) :
    ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A)
      ≤ ∫⁻ z in A, (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume := by
  classical
  have hucont : Continuous u := hu.continuous
  -- ===================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets.
  -- Built by Dynkin (closed-set pi-system) on each compact ball, with the
  -- complement step legitimized a.e. by the finiteness of the level-length on a
  -- compact ball (`eilenberg_coarea_planar_metric`), then by the closed-ball
  -- exhaustion of `ℂ`.
  -- ===================================================================
  -- (0a)  On a fixed compact ball `B = closedBall 0 N`.
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        -- `μH[2] B = (c • volume) B = c * volume B < ∞` since `B` is compact.
        obtain ⟨c, hc, hcv⟩ := hausdorffMeasure_two_complex_smul_volume
        rw [hcv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    -- Dynkin predicate.
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · -- empty
      simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · -- basic: closed `T`, `T ∩ B` compact
      intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · -- complement (a.e. by finiteness of `gB`)
      intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · -- countable disjoint union
      intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  -- (0b)  Full measurable `A'` via the closed-ball exhaustion.
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- ===================================================================
  -- (1)  Critical / regular partition of `A`.
  -- `Crit = (fderiv u)⁻¹{0}` is measurable, `Reg = {fderiv u ≠ 0} = Critᶜ`.
  -- For each `c` the level slice splits DISJOINTLY:
  --   `u⁻¹{c} ∩ A = (u⁻¹{c} ∩ (A ∩ Crit)) ∪ (u⁻¹{c} ∩ (A ∩ Reg))`.
  -- ===================================================================
  set Crit : Set ℂ := {z | fderiv ℝ u z = 0} with hCrit_def
  have hCrit_meas : MeasurableSet Crit :=
    measurable_fderiv ℝ u (measurableSet_singleton _)
  -- The critical-slice integral vanishes (proven, axiom-clean).
  have hcrit0 : ∫⁻ c, μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit)) = 0 :=
    coarea_critical_le hu hA
  -- The critical slice is a.e. `0` (AEmeasurable via the `slice_aemeas` block above).
  have hae0 : ∀ᵐ c ∂(volume : Measure ℝ),
      μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit)) = 0 := by
    have := (lintegral_eq_zero_iff' (slice_aemeas (hA.inter hCrit_meas))).1 hcrit0
    filter_upwards [this] with c hc
    simpa only [Pi.zero_apply] using hc
  -- ===================================================================
  -- (2)  A.e. rewrite of the integrand to the regular slice.
  -- ===================================================================
  have hslice_split : ∀ c : ℝ,
      μH[1] (u ⁻¹' {c} ∩ A)
        = μH[1] (u ⁻¹' {c} ∩ (A ∩ Crit))
          + μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
    intro c
    have hsetsplit : u ⁻¹' {c} ∩ A
        = (u ⁻¹' {c} ∩ (A ∩ Crit))
          ∪ (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
      ext z
      simp only [hCrit_def, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hzc, hzA⟩
        by_cases hz : fderiv ℝ u z = 0
        · exact Or.inl ⟨hzc, hzA, hz⟩
        · exact Or.inr ⟨hzc, hzA, hz⟩
      · rintro (⟨hzc, hzA, _⟩ | ⟨hzc, hzA, _⟩) <;> exact ⟨hzc, hzA⟩
    rw [hsetsplit]
    refine measure_union ?_ ?_
    · -- `Crit` and `{∇u ≠ 0}` are disjoint, so the two slices are disjoint.
      refine Set.disjoint_left.2 ?_
      rintro z ⟨_, _, hzCrit⟩ ⟨_, _, hzReg⟩
      exact hzReg hzCrit
    · have hReg_meas : MeasurableSet {z : ℂ | fderiv ℝ u z ≠ 0} := by
        have : {z : ℂ | fderiv ℝ u z ≠ 0} = Critᶜ := by
          ext z; simp only [hCrit_def, Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [this]; exact hCrit_meas.compl
      exact (hucont.measurable (measurableSet_singleton c)).inter (hA.inter hReg_meas)
  have hcongr : (fun c => μH[1] (u ⁻¹' {c} ∩ A))
      =ᵐ[volume] fun c => μH[1] (u ⁻¹' {c} ∩ (A ∩ {z | fderiv ℝ u z ≠ 0})) := by
    filter_upwards [hae0] with c hc
    rw [hslice_split c, hc, zero_add]
  -- ===================================================================
  -- (3)  Finish:  rewrite a.e., then apply the regular co-area bound.
  -- ===================================================================
  rw [lintegral_congr_ae hcongr]
  exact coarea_regular_le hu hA

/-- **Sharp planar co-area (Eilenberg) inequality, gradient-weighted form (the isolated GMT
residual that the length–area assembly consumes).**

For a `K`-Lipschitz `u : ℂ → ℝ` (Lipschitz, hence `fderiv ℝ u` exists a.e. by Rademacher) and a
nonnegative measurable weight `g : ℂ → ℝ≥0∞`,

`∫⁻ c, (∫⁻ z in u⁻¹{c}, g z ∂μH[1]) dc ≤ ∫⁻ z, g z * ‖fderiv ℝ u z‖₊ ∂volume`.

## Truth and direction

**TRUE**, one-sided (`≤`). This is the genuine Eilenberg inequality (Evans–Gariepy §3.4.2,
Theorem 1: for Lipschitz `u : ℝⁿ → ℝ`, `∫_ℝ (∫_{u⁻¹{c}} g dμH^{n-1}) dc ≤ ∫ g |∇u| dx`; equality
is the co-area *formula*, the deeper two-sided statement, which is **not** claimed). The pointwise
gradient `‖∇u‖` is sharper than any Lipschitz-constant bound (since `‖∇u‖ ≤ K` a.e.); this is the
*primitive* co-area atom that the length–area lower bound consumes.

## Affine sanity check

For `u(z) = z.re` (so `fderiv ℝ u = reCLM`, `‖∇u‖ = 1`), the right side is `∫⁻ g dvol`; the left
side is `∫⁻ c (∫_{re = c} g dμH[1]) dc`, and co-area for the affine `u` is the Fubini equality
`∫ g = ∫_c ∫_{re=c} g`, so `≤` holds with equality — exactly the affine length–area case in
`lengthArea_modulus_lower_bound`.

## Proof

By the layer-cake (monotone simple-function approximation of `g`) this reduces to the unweighted
set form `coarea_set_sharp` (`∫⁻ c, μH[1] (u ⁻¹' {c} ∩ A) ≤ ∫⁻ z in A, ‖∇u‖₊`), which is the
area-formula assembly `coarea_critical_le + coarea_regular_le`, the latter built from the per-piece
core `coarea_piece_le` (Lusin decomposition into approximately-linear injective pieces + the area
formula + the fiber arc-length bound). The constant is the sharp `1` (Evans–Gariepy), not `K`. -/
theorem eilenberg_coarea_grad_le {u : ℂ → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ))
      ≤ ∫⁻ z, g z * (‖fderiv ℝ u z‖₊ : ℝ≥0∞) ∂volume := by
  classical
  have hucont : Continuous u := hu.continuous
  set w : ℂ → ℝ≥0∞ := fun z => (‖fderiv ℝ u z‖₊ : ℝ≥0∞) with hw_def
  have hw_meas : Measurable w := (measurable_fderiv ℝ u).nnnorm.coe_nnreal_ennreal
  -- ===================================================================
  -- (0)  Slice AEMeasurability for ARBITRARY measurable sets.
  -- Reproduced inline from `coarea_set_sharp` (Dynkin on closed sets per
  -- compact ball, legitimized a.e. by `eilenberg_coarea_planar_metric`, then
  -- the closed-ball exhaustion of `ℂ`).
  -- ===================================================================
  -- (0a)  On a fixed compact ball `B = closedBall 0 N`.
  have slice_on_ball : ∀ (N : ℕ) {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable
        (fun c => μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N))) := by
    intro N A' hA'
    set B : Set ℂ := Metric.closedBall (0:ℂ) N with hB_def
    have hBcompact : IsCompact B := isCompact_closedBall _ _
    set gB : ℝ → ℝ≥0∞ := fun c => μH[1] (u ⁻¹' {c} ∩ B) with hgB_def
    have hgB_meas : Measurable gB := measurable_slice_hausdorff_one hucont hBcompact
    have hgB_fin : ∀ᵐ c ∂(volume : Measure ℝ), gB c ≠ ∞ := by
      have hint : ∫⁻ c, gB c ≤ (K : ℝ≥0∞) * μH[2] B :=
        eilenberg_coarea_planar_metric (hu.lipschitzOnWith) hBcompact
      have hfin : ∫⁻ c, gB c ≠ ∞ := by
        refine ne_of_lt (lt_of_le_of_lt hint ?_)
        refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
        -- `μH[2] B = (c • volume) B = c * volume B < ∞` since `B` is compact.
        obtain ⟨c, hc, hcv⟩ := hausdorffMeasure_two_complex_smul_volume
        rw [hcv, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top hBcompact.measure_lt_top
      exact (ae_lt_top hgB_meas hfin).mono (fun c hc => ne_of_lt hc)
    -- Dynkin predicate.
    have hborel : (by infer_instance : MeasurableSpace ℂ) = borel ℂ :=
      BorelSpace.measurable_eq
    refine MeasurableSpace.induction_on_inter
      (C := fun t _ => AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ (t ∩ B))))
      (s := {s : Set ℂ | IsClosed s})
      (h_eq := hborel.trans borel_eq_generateFrom_isClosed)
      (h_inter := isPiSystem_isClosed) ?_ ?_ ?_ ?_ A' hA'
    · -- empty
      simp only [Set.empty_inter, Set.inter_empty, measure_empty]
      exact aemeasurable_const
    · -- basic: closed `T`, `T ∩ B` compact
      intro T hT
      have hTcl : IsClosed T := hT
      have hTBcompact : IsCompact (T ∩ B) := hBcompact.inter_left hTcl
      exact (measurable_slice_hausdorff_one hucont hTBcompact).aemeasurable
    · -- complement (a.e. by finiteness of `gB`)
      intro T hTmeas hPT
      have hmeasdiff : AEMeasurable (fun c => gB c - μH[1] (u ⁻¹' {c} ∩ (T ∩ B))) :=
        hgB_meas.aemeasurable.sub hPT
      refine hmeasdiff.congr ?_
      filter_upwards [hgB_fin] with c hc
      have hset : u ⁻¹' {c} ∩ (Tᶜ ∩ B)
          = (u ⁻¹' {c} ∩ B) \ (u ⁻¹' {c} ∩ (T ∩ B)) := by
        ext z; constructor
        · rintro ⟨hz, hzc, hzB⟩
          exact ⟨⟨hz, hzB⟩, fun ⟨_, hzT, _⟩ => hzc hzT⟩
        · rintro ⟨⟨hz, hzB⟩, hnot⟩
          exact ⟨hz, fun hzT => hnot ⟨hz, hzT, hzB⟩, hzB⟩
      rw [hset]
      have hsub : u ⁻¹' {c} ∩ (T ∩ B) ⊆ u ⁻¹' {c} ∩ B := fun z hz => ⟨hz.1, hz.2.2⟩
      have hfin' : μH[1] (u ⁻¹' {c} ∩ (T ∩ B)) ≠ ∞ :=
        ne_top_of_le_ne_top hc (measure_mono hsub)
      rw [measure_diff hsub
        ((hucont.measurable (measurableSet_singleton c)).inter
          (hTmeas.inter hBcompact.measurableSet)).nullMeasurableSet hfin']
    · -- countable disjoint union
      intro f hdisj hfmeas hPf
      refine AEMeasurable.congr (AEMeasurable.ennreal_tsum hPf) ?_
      filter_upwards with c
      have hset : u ⁻¹' {c} ∩ ((⋃ i, f i) ∩ B) = ⋃ i, (u ⁻¹' {c} ∩ (f i ∩ B)) := by
        rw [Set.iUnion_inter, Set.inter_iUnion]
      rw [hset]
      refine (measure_iUnion ?_ ?_).symm
      · intro i j hij
        refine Set.disjoint_left.2 ?_
        rintro z ⟨_, hzfi, _⟩ ⟨_, hzfj, _⟩
        exact (Set.disjoint_left.1 (hdisj hij)) hzfi hzfj
      · intro i
        exact (hucont.measurable (measurableSet_singleton c)).inter
          ((hfmeas i).inter hBcompact.measurableSet)
  -- (0b)  Full measurable `A'` via the closed-ball exhaustion.
  have slice_aemeas : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (u ⁻¹' {c} ∩ A')) := by
    intro A' hA'
    have hball_mono : Monotone (fun N : ℕ => Metric.closedBall (0:ℂ) (N:ℝ)) :=
      fun m n hmn => Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    have hcover : ∀ z : ℂ, ∃ N : ℕ, z ∈ Metric.closedBall (0:ℂ) N := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
      exact ⟨N, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hN⟩
    have hpt : ∀ c : ℝ, μH[1] (u ⁻¹' {c} ∩ A')
        = ⨆ N : ℕ, μH[1] (u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) N)) := by
      intro c
      have hmono : Monotone (fun N : ℕ =>
          u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ))) :=
        fun m n hmn => Set.inter_subset_inter_right _
          (Set.inter_subset_inter_right _ (hball_mono hmn))
      have hunion : (⋃ N : ℕ, u ⁻¹' {c} ∩ (A' ∩ Metric.closedBall (0:ℂ) (N:ℝ)))
          = u ⁻¹' {c} ∩ A' := by
        rw [← Set.inter_iUnion, ← Set.inter_iUnion]
        congr 1
        rw [Set.inter_eq_left.2]
        intro z _
        obtain ⟨N, hN⟩ := hcover z
        exact Set.mem_iUnion.2 ⟨N, hN⟩
      rw [← hunion, hmono.measure_iUnion]
    refine AEMeasurable.congr
      (AEMeasurable.iSup (fun N => slice_on_ball N hA')) ?_
    filter_upwards with c
    exact (hpt c).symm
  -- A convenience: AEMeasurability of `c ↦ μH[1] (A' ∩ u⁻¹{c})` (intersection
  -- with the roles swapped), which is how the slices appear below.
  have slice_aemeas' : ∀ {A' : Set ℂ}, MeasurableSet A' →
      AEMeasurable (fun c => μH[1] (A' ∩ u ⁻¹' {c})) := by
    intro A' hA'
    refine (slice_aemeas hA').congr ?_
    filter_upwards with c
    rw [Set.inter_comm]
  -- ===================================================================
  -- (A)  The key inequality for a SIMPLE function `s`:
  --      `∫⁻ c, (∫⁻ z in u⁻¹{c}, s z ∂μH[1]) ≤ ∫⁻ z, w z * s z`.
  -- The slice integral of a simple function is a finite range-sum, each term
  -- of which is bounded by `coarea_set_sharp`; the right side reassembles via
  -- `withDensity`.
  -- ===================================================================
  have hsimple : ∀ s : SimpleFunc ℂ ℝ≥0∞,
      ∫⁻ c, (∫⁻ z in u ⁻¹' {c}, s z ∂(μH[1] : Measure ℂ))
        ≤ ∫⁻ z, w z * s z ∂volume := by
    intro s
    -- LHS slice as a finite sum over the range of `s`.
    have hslice_sum : ∀ c : ℝ,
        (∫⁻ z in u ⁻¹' {c}, s z ∂(μH[1] : Measure ℂ))
          = ∑ x ∈ s.range, x * μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}) := by
      intro c
      rw [SimpleFunc.lintegral_eq_lintegral]
      show s.lintegral ((μH[1] : Measure ℂ).restrict (u ⁻¹' {c})) = _
      rw [SimpleFunc.lintegral]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Measure.restrict_apply (s.measurableSet_preimage {x})]
    rw [lintegral_congr hslice_sum]
    rw [lintegral_finset_sum']
    · -- Bound each term by `coarea_set_sharp`.
      have hbound : ∀ x ∈ s.range,
          (∫⁻ c, x * μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}))
            ≤ x * ∫⁻ z in s ⁻¹' {x}, w z ∂volume := by
        intro x _
        rw [lintegral_const_mul'' x (slice_aemeas' (s.measurableSet_preimage {x}))]
        refine mul_le_mul' le_rfl ?_
        have hcomm : ∀ c : ℝ,
            μH[1] (s ⁻¹' {x} ∩ u ⁻¹' {c}) = μH[1] (u ⁻¹' {c} ∩ s ⁻¹' {x}) := by
          intro c; rw [Set.inter_comm]
        rw [lintegral_congr hcomm]
        exact coarea_set_sharp hu (s.measurableSet_preimage {x})
      refine le_trans (Finset.sum_le_sum hbound) ?_
      -- Reassemble `∑ x, x * ∫⁻ in s⁻¹{x}, w = ∫⁻ z, w z * s z` via `withDensity`.
      have hRHS : ∫⁻ z, w z * s z ∂volume = ∫⁻ z, s z ∂(volume.withDensity w) := by
        rw [lintegral_withDensity_eq_lintegral_mul volume hw_meas s.measurable]
        simp only [Pi.mul_apply]
      rw [hRHS, SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
      refine Finset.sum_le_sum ?_
      intro x _
      refine mul_le_mul' le_rfl ?_
      rw [withDensity_apply w (s.measurableSet_preimage {x})]
    · -- AEMeasurability in `c` of each summand.
      intro x _
      exact (slice_aemeas' (s.measurableSet_preimage {x})).const_mul x
  -- ===================================================================
  -- (B)  Monotone convergence: `g = ⨆ n, eapprox g n`.
  -- ===================================================================
  set sn : ℕ → SimpleFunc ℂ ℝ≥0∞ := fun n => SimpleFunc.eapprox g n with hsn_def
  -- Pull the supremum out of the inner (slice) integral.
  have hLHS_pt : ∀ c : ℝ,
      (∫⁻ z in u ⁻¹' {c}, g z ∂(μH[1] : Measure ℂ))
        = ⨆ n, ∫⁻ z in u ⁻¹' {c}, sn n z ∂(μH[1] : Measure ℂ) := by
    intro c
    rw [← lintegral_iSup]
    · refine lintegral_congr fun z => ?_
      exact (SimpleFunc.iSup_eapprox_apply hg z).symm
    · intro n; exact (sn n).measurable
    · intro m n hmn z
      exact SimpleFunc.monotone_eapprox g hmn z
  rw [lintegral_congr hLHS_pt]
  -- Pull the supremum out of the outer integral (in `c`).
  rw [lintegral_iSup']
  · -- `⨆ n, ∫⁻ c, slice(sₙ) ≤ ∫⁻ z, g z * w z`.
    refine iSup_le fun n => ?_
    refine le_trans (hsimple (sn n)) ?_
    refine lintegral_mono fun z => ?_
    rw [mul_comm (g z)]
    refine mul_le_mul' le_rfl ?_
    calc (sn n) z ≤ ⨆ k, (sn k) z := le_iSup (fun k => (sn k) z) n
      _ = g z := SimpleFunc.iSup_eapprox_apply hg z
  · -- AEMeasurability in `c` of `c ↦ ∫⁻ z in u⁻¹{c}, sₙ z`.
    intro n
    have hsum : (fun c => ∫⁻ z in u ⁻¹' {c}, sn n z ∂(μH[1] : Measure ℂ))
        = (fun c => ∑ x ∈ (sn n).range, x * μH[1] ((sn n) ⁻¹' {x} ∩ u ⁻¹' {c})) := by
      funext c
      rw [SimpleFunc.lintegral_eq_lintegral]
      show (sn n).lintegral ((μH[1] : Measure ℂ).restrict (u ⁻¹' {c})) = _
      rw [SimpleFunc.lintegral]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Measure.restrict_apply ((sn n).measurableSet_preimage {x})]
    rw [hsum]
    refine Finset.aemeasurable_fun_sum _ ?_
    intro x _
    exact (slice_aemeas' ((sn n).measurableSet_preimage {x})).const_mul x
  · -- Monotonicity in `n` (everywhere, hence a.e.).
    filter_upwards with c
    intro m n hmn
    refine lintegral_mono fun z => ?_
    exact SimpleFunc.monotone_eapprox g hmn z

end RiemannDynamics.Coarea
