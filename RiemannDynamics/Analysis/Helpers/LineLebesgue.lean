/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# One-dimensional Lebesgue differentiation along a fixed direction in `ℂ`

For a locally integrable function `f : ℂ → ℝ` and a unit vector `u : ℂ`, at almost every point
`z : ℂ` the one-sided directional interval averages of `f` along the line `z + ℝ • u` converge to
`f z`:
`h⁻¹ ∫₀ʰ f (z + s • u) ds → f z` as `h ↓ 0`.

This is the one-dimensional Lebesgue differentiation theorem for the restriction of `f` to lines in
the direction `u`, lifted to almost every point of the plane. The proof pulls `f` back through the
measure-preserving orthonormal frame `Φ (a, b) = u * (a + b i)`, reduces to the interval Lebesgue
differentiation theorem on the horizontal slices via Fubini, and transports the result back.
-/

open MeasureTheory Set Filter Function Complex
open scoped Topology

noncomputable section

namespace LineLebesgue

/-! ### The orthonormal frame `Φ (a, b) = u * (a + b i)` -/

/-- The measure-preserving frame `ℝ × ℝ ≃ᵐ ℂ`, `(a, b) ↦ u * (a + b i)`, for a unit vector `u`. -/
def frame (u : ℂ) (hu : ‖u‖ = 1) : (ℝ × ℝ) ≃ᵐ ℂ :=
  Complex.measurableEquivRealProd.symm.trans
    (rotation ⟨u, mem_sphere_zero_iff_norm.2 hu⟩).toHomeomorph.toMeasurableEquiv

theorem frame_apply (u : ℂ) (hu : ‖u‖ = 1) (p : ℝ × ℝ) :
    frame u hu p = (rotation ⟨u, mem_sphere_zero_iff_norm.2 hu⟩)
      (Complex.measurableEquivRealProd.symm p) := rfl

theorem frame_measurePreserving (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (frame u hu) volume volume := by
  have h1 : MeasurePreserving (Complex.measurableEquivRealProd.symm) volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm _
  have h2 : MeasurePreserving
      (rotation ⟨u, mem_sphere_zero_iff_norm.2 hu⟩) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  exact h2.comp h1

theorem frame_continuous (u : ℂ) (hu : ‖u‖ = 1) : Continuous (frame u hu) := by
  have hmk : Continuous (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p) := by
    have heq : (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p)
        = fun p : ℝ × ℝ => Complex.equivRealProdCLM.symm p := by
      funext p
      rw [measurableEquivRealProd_symm_apply, Complex.equivRealProdCLM_symm_apply]
      apply Complex.ext <;> simp
    rw [heq]; exact Complex.equivRealProdCLM.symm.continuous
  exact (rotation ⟨u, mem_sphere_zero_iff_norm.2 hu⟩).continuous.comp hmk

/-- The frame turns a translation along `u` into a shift of the first coordinate. -/
theorem frame_shift (u : ℂ) (hu : ‖u‖ = 1) (a b s : ℝ) :
    frame u hu (a, b) + s • u = frame u hu (a + s, b) := by
  simp only [frame_apply, rotation_apply, measurableEquivRealProd_symm_apply, Complex.real_smul]
  have : (Complex.mk (a + s) b) = Complex.mk a b + (s : ℂ) := by apply Complex.ext <;> simp
  rw [this]; ring

/-! ### The interval Lebesgue differentiation theorem, one-sided -/

/-- If `x ↦ ∫ t in a..x, φ t` has derivative `v` at `a`, then the one-sided right averages of `φ`
starting at `a` converge to `v`. -/
theorem tendsto_lineAverage_of_hasDerivAt (φ : ℝ → ℝ) (a v : ℝ)
    (hd : HasDerivAt (fun x => ∫ t in a..x, φ t) v a) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, φ (a + s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds v) := by
  refine hd.tendsto_slope_zero_right.congr' ?_
  filter_upwards with h
  simp only [smul_eq_mul, intervalIntegral.integral_same, sub_zero]
  congr 1
  have := intervalIntegral.integral_comp_add_left (a := 0) (b := h) φ a
  simp only [add_zero] at this
  exact this.symm

/-! ### Fubini: almost every horizontal slice is locally integrable -/

/-- If `g : ℝ × ℝ → ℝ` is locally integrable, then for almost every `b` the horizontal slice
`a ↦ g (a, b)` is locally integrable. -/
theorem ae_locallyIntegrable_slice (g : ℝ × ℝ → ℝ)
    (hg : LocallyIntegrable g (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ b : ℝ, LocallyIntegrable (fun a => g (a, b)) volume := by
  have slice : ∀ N : ℕ, ∀ᵐ b : ℝ,
      b ∈ Icc (-(N:ℝ)) N → IntegrableOn (fun a => g (a, b)) (Icc (-(N:ℝ)) N) volume := by
    intro N
    have box : IntegrableOn g (Icc (-(N:ℝ)) N ×ˢ Icc (-(N:ℝ)) N) volume :=
      hg.integrableOn_isCompact (isCompact_Icc.prod isCompact_Icc)
    have hb : Integrable g
        ((volume.restrict (Icc (-(N:ℝ)) N)).prod (volume.restrict (Icc (-(N:ℝ)) N))) := by
      rw [Measure.prod_restrict]; exact box.integrable
    exact ae_imp_of_ae_restrict hb.prod_left_ae
  rw [← ae_all_iff] at slice
  filter_upwards [slice] with b hb
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨N, hKN, hbN⟩ : ∃ N : ℕ, K ⊆ Icc (-(N:ℝ)) N ∧ b ∈ Icc (-(N:ℝ)) N := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
    obtain ⟨N, hN⟩ := exists_nat_ge (max r |b|)
    have hrN : r ≤ N := le_trans (le_max_left _ _) hN
    have hbN' : |b| ≤ N := le_trans (le_max_right _ _) hN
    refine ⟨N, ?_, ?_⟩
    · refine hr.trans fun x hx => ?_
      rw [Real.closedBall_eq_Icc] at hx
      simp only [zero_sub, zero_add] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · exact ⟨by linarith [abs_le.1 hbN'|>.1], by linarith [abs_le.1 hbN'|>.2]⟩
  exact ((hb N) hbN).mono_set hKN

/-! ### Measurability of the convergence set (for a measurable integrand) -/

/-- The difference quotient of the horizontal primitive. -/
private def lineDQ (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (h : ℝ) : ℝ :=
  h⁻¹ * ∫ s in (0:ℝ)..h, g (p.1 + s, p.2)

/-- On `Ioi 0` the difference quotient is continuous in the step, given interval integrability. -/
private theorem continuousOn_lineDQ {g : ℝ × ℝ → ℝ} (p : ℝ × ℝ)
    (hg_int : ∀ a b : ℝ, IntervalIntegrable (fun s => g (p.1 + s, p.2)) volume a b) :
    ContinuousOn (lineDQ g p) (Set.Ioi 0) := by
  have hprim : Continuous (fun h : ℝ => ∫ s in (0:ℝ)..h, g (p.1 + s, p.2)) :=
    intervalIntegral.continuous_primitive hg_int 0
  have hinv : ContinuousOn (fun h : ℝ => h⁻¹) (Set.Ioi 0) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx; exact ne_of_gt hx
  exact hinv.mul hprim.continuousOn

/-- One-sided convergence is equivalent to a countable statement over rational steps, using
continuity of the difference quotient. -/
private theorem tendsto_iff_rat {Fp : ℝ → ℝ} {gp : ℝ}
    (hcont : ContinuousOn Fp (Set.Ioi (0 : ℝ))) :
    Tendsto Fp (𝓝[>] 0) (𝓝 gp) ↔
      ∀ k : ℕ, ∃ n : ℕ, ∀ q : ℚ, 0 < q → (q:ℝ) < 1/(n+1) →
        |Fp q - gp| ≤ 1/(k+1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro H k
    obtain ⟨δ, hδ, hδp⟩ := H (1/(k+1)) (by positivity)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, ?_⟩
    intro q hq hqn
    have hqIoi : (q:ℝ) ∈ Set.Ioi (0:ℝ) := by rw [Set.mem_Ioi]; exact_mod_cast hq
    have hdist : dist (q:ℝ) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by exact_mod_cast hq)]
      calc (q:ℝ) < 1/(n+1) := hqn
        _ < δ := hn
    have hd := hδp hqIoi hdist
    rw [Real.dist_eq] at hd
    exact le_of_lt hd
  · intro H ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨n, hn⟩ := H k
    refine ⟨1/(n+1), by positivity, ?_⟩
    intro x hx hxdist
    have hxpos : 0 < x := hx
    have hxlt : x < 1/(n+1) := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hxpos] at hxdist; exact hxdist
    have hxIoo : x ∈ Set.Ioo (0:ℝ) (1/(n+1)) := ⟨hxpos, hxlt⟩
    set δ' : ℝ := 1/(n+1) with hδ'
    set S : Set ℝ := Set.Ioo (0:ℝ) δ' ∩ Set.range ((↑):ℚ→ℝ) with hSdef
    have hbound : ∀ y ∈ S, |Fp y - gp| ≤ 1/(k+1) := by
      rintro y ⟨hyIoo, ⟨r, rfl⟩⟩
      apply hn r
      · exact_mod_cast hyIoo.1
      · exact_mod_cast hyIoo.2
    have hclos : x ∈ closure S := by
      rw [mem_closure_iff_nhds]
      intro t ht
      rw [mem_nhds_iff] at ht
      obtain ⟨U, hUt, hUopen, hhU⟩ := ht
      have hVopen : IsOpen (U ∩ Set.Ioo (0:ℝ) δ') := hUopen.inter isOpen_Ioo
      obtain ⟨rq, hqV⟩ :=
        (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open hVopen ⟨x, hhU, hxIoo⟩
      exact ⟨(rq:ℝ), hUt hqV.1, hqV.2, rq, rfl⟩
    have hneBot : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclos
    have hSsub : S ⊆ Set.Ioi (0:ℝ) := fun z hz => hz.1.1
    have hcwa : ContinuousWithinAt Fp S x := (hcont x hxpos).mono hSsub
    have htend : Tendsto (fun y => |Fp y - gp|) (𝓝[S] x) (𝓝 (|Fp x - gp|)) :=
      (hcwa.sub continuousWithinAt_const).abs
    have hle : |Fp x - gp| ≤ 1/(k+1) := by
      refine le_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with y hy using hbound y hy
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hle hk

/-- For fixed positive rational step, the difference quotient is measurable in the base point. -/
private theorem measurable_lineDQ_rat {g : ℝ × ℝ → ℝ} (hg : Measurable g) (q : ℚ) (hq : 0 < q) :
    Measurable (fun p : ℝ × ℝ => lineDQ g p (q:ℝ)) := by
  have hqle : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq.le
  unfold lineDQ
  apply Measurable.const_mul
  have hint : Measurable
      (fun p : ℝ × ℝ => ∫ s in Set.Ioc (0:ℝ) (q:ℝ), g (p.1 + s, p.2)) := by
    have hmap : Measurable (fun ps : (ℝ × ℝ) × ℝ => (ps.1.1 + ps.2, ps.1.2)) := by fun_prop
    have hjoint : StronglyMeasurable
        (fun ps : (ℝ × ℝ) × ℝ => g (ps.1.1 + ps.2, ps.1.2)) :=
      (hg.comp hmap).stronglyMeasurable
    have := hjoint.integral_prod_right' (ν := volume.restrict (Set.Ioc (0:ℝ) (q:ℝ)))
    simpa using this.measurable
  have heq : (fun p : ℝ × ℝ => ∫ s in (0:ℝ)..(q:ℝ), g (p.1 + s, p.2))
      = (fun p : ℝ × ℝ => ∫ s in Set.Ioc (0:ℝ) (q:ℝ), g (p.1 + s, p.2)) := by
    funext p; exact intervalIntegral.integral_of_le hqle
  rw [heq]; exact hint

/-- Measurability of the convergence set intersected with a measurable "good" set on which the
integrand is interval integrable along horizontal lines. -/
private theorem measurableSet_tendsto_inter {g : ℝ × ℝ → ℝ} (hg_meas : Measurable g)
    {G : Set (ℝ × ℝ)} (hG : MeasurableSet G)
    (hg_int : ∀ p ∈ G, ∀ a b : ℝ,
      IntervalIntegrable (fun s => g (p.1 + s, p.2)) volume a b) :
    MeasurableSet
      ({ p : ℝ × ℝ | Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g (p.1 + s, p.2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g p)) } ∩ G) := by
  have hinner : ∀ (k : ℕ) (q : ℚ), 0 < q → MeasurableSet
      { p : ℝ × ℝ | |lineDQ g p (q:ℝ) - g p| ≤ 1/(k+1) } := by
    intro k q hq
    have hX : Measurable (fun p : ℝ × ℝ => lineDQ g p (q:ℝ) - g p) :=
      (measurable_lineDQ_rat hg_meas q hq).sub hg_meas
    have hset : { p : ℝ × ℝ | |lineDQ g p (q:ℝ) - g p| ≤ 1/(k+1) }
        = { p | lineDQ g p (q:ℝ) - g p ≤ 1/(k+1) } ∩
          { p | -(1/(k+1)) ≤ lineDQ g p (q:ℝ) - g p } := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]; tauto
    rw [hset]
    exact (measurableSet_le hX measurable_const).inter
      (measurableSet_le measurable_const hX)
  have hcount : MeasurableSet
      (⋂ k : ℕ, ⋃ n : ℕ, ⋂ q : ℚ, ⋂ (_ : 0 < q), ⋂ (_ : (q:ℝ) < 1/(n+1)),
        { p : ℝ × ℝ | |lineDQ g p (q:ℝ) - g p| ≤ 1/(k+1) }) := by
    refine MeasurableSet.iInter (fun k => MeasurableSet.iUnion (fun n => ?_))
    refine MeasurableSet.iInter (fun q => ?_)
    by_cases hq : 0 < q
    · exact MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ => hinner k q hq))
    · exact MeasurableSet.iInter (fun hq' => absurd hq' hq)
  have hset : ({ p : ℝ × ℝ | Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g (p.1 + s, p.2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g p)) } ∩ G)
      = (⋂ k : ℕ, ⋃ n : ℕ, ⋂ q : ℚ, ⋂ (_ : 0 < q), ⋂ (_ : (q:ℝ) < 1/(n+1)),
          { p : ℝ × ℝ | |lineDQ g p (q:ℝ) - g p| ≤ 1/(k+1) }) ∩ G := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro ⟨htend, hpG⟩
      refine ⟨?_, hpG⟩
      exact ((tendsto_iff_rat (continuousOn_lineDQ p (hg_int p hpG))).mp htend)
    · rintro ⟨hc, hpG⟩
      refine ⟨?_, hpG⟩
      exact ((tendsto_iff_rat (continuousOn_lineDQ p (hg_int p hpG))).mpr hc)
  rw [hset]
  exact hcount.inter hG

/-! ### The plane statement on `ℝ × ℝ` -/

/-- The directional Lebesgue differentiation statement on `ℝ × ℝ` for a locally integrable
function, transported through Fubini and the interval Lebesgue differentiation theorem. -/
theorem ae_tendsto_lineAverage_prod (g : ℝ × ℝ → ℝ)
    (hg : LocallyIntegrable g (volume : Measure (ℝ × ℝ))) :
    ∀ᵐ p : ℝ × ℝ, Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g (p.1 + s, p.2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g p)) := by
  -- Work with a measurable representative `g₀ =ᵐ g`.
  set g₀ : ℝ × ℝ → ℝ := hg.aestronglyMeasurable.mk g with hg₀def
  have hg₀meas : Measurable g₀ := hg.aestronglyMeasurable.measurable_mk
  have hgg₀ : g =ᵐ[volume] g₀ := hg.aestronglyMeasurable.ae_eq_mk
  have hg₀ : LocallyIntegrable g₀ (volume : Measure (ℝ × ℝ)) := hg.congr hgg₀
  -- The convergence statement for `g₀`, via Fubini + interval Lebesgue differentiation.
  have h0 : ∀ᵐ p : ℝ × ℝ, Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g₀ (p.1 + s, p.2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g₀ p)) := by
    -- almost every horizontal slice is locally integrable
    obtain ⟨B, hBmem, hBmeas, hB⟩ :=
      (ae_locallyIntegrable_slice g₀ hg₀).exists_measurable_mem
    -- the "good" product set: second coordinate in `B`
    set G : Set (ℝ × ℝ) := {p | p.2 ∈ B} with hGdef
    have hGmeas : MeasurableSet G := measurable_snd hBmeas
    have hg_int : ∀ p ∈ G, ∀ a b : ℝ,
        IntervalIntegrable (fun s => g₀ (p.1 + s, p.2)) volume a b := by
      intro p hp a b
      have hloc : LocallyIntegrable (fun a => g₀ (a, p.2)) volume := hB p.2 hp
      have hII : IntervalIntegrable (fun x => g₀ (x, p.2)) volume (p.1 + a) (p.1 + b) :=
        (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
      have := hII.comp_add_left p.1
      simpa using this
    -- the a.e.-a.e. statement
    have aeae : ∀ᵐ b : ℝ, ∀ᵐ a : ℝ,
        Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g₀ (a + s, b))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (g₀ (a, b))) := by
      filter_upwards [ae_locallyIntegrable_slice g₀ hg₀] with b hb
      filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hb] with a ha
      exact tendsto_lineAverage_of_hasDerivAt (fun t => g₀ (t, b)) a (g₀ (a, b)) (ha a)
    -- swap-predicate measurability of the (convergence ∩ G) set
    set P : ℝ × ℝ → Prop := fun p =>
      Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, g₀ (p.1 + s, p.2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (g₀ p)) with hP
    have hmeas : MeasurableSet {q : ℝ × ℝ | (P (Prod.swap q)) ∧ (Prod.swap q ∈ G)} := by
      have := (measurableSet_tendsto_inter (g := g₀) hg₀meas hGmeas hg_int)
      exact this.preimage measurable_swap
    have hswap : ∀ᵐ q : ℝ × ℝ, (P (Prod.swap q)) ∧ (Prod.swap q ∈ G) := by
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
      rw [Measure.ae_prod_iff_ae_ae hmeas]
      filter_upwards [aeae, hBmem] with b hb hbB
      filter_upwards [hb] with a ha
      exact ⟨ha, hbB⟩
    -- transport swap back
    have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
      Measure.measurePreserving_swap
    have := hmp.quasiMeasurePreserving.ae hswap
    simp only [Prod.swap_swap] at this
    filter_upwards [this] with p hp using hp.1
  -- transfer from `g₀` to `g` using `g =ᵐ g₀`.
  have hslice : ∀ᵐ b : ℝ, (fun a => g (a, b)) =ᵐ[volume] (fun a => g₀ (a, b)) := by
    have hmp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
      Measure.measurePreserving_swap
    have hsw : (fun q : ℝ × ℝ => g q.swap) =ᵐ[volume] (fun q => g₀ q.swap) :=
      hmp.quasiMeasurePreserving.ae_eq_comp hgg₀
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl]
      at hsw
    exact (Measure.ae_ae_of_ae_prod hsw).mono fun b hb => hb
  have hint : ∀ᵐ p : ℝ × ℝ, ∀ h : ℝ,
      (∫ s in (0:ℝ)..h, g (p.1 + s, p.2)) = ∫ s in (0:ℝ)..h, g₀ (p.1 + s, p.2) := by
    have hlift : ∀ᵐ p : ℝ × ℝ, (fun a => g (a, p.2)) =ᵐ[volume] (fun a => g₀ (a, p.2)) := by
      have := (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae hslice
      rwa [show (volume : Measure ℝ).prod (volume : Measure ℝ)
        = (volume : Measure (ℝ × ℝ)) from rfl] at this
    filter_upwards [hlift] with p hp h
    have htr : (fun s => g (p.1 + s, p.2)) =ᵐ[volume] (fun s => g₀ (p.1 + s, p.2)) :=
      (MeasureTheory.measurePreserving_add_left (volume : Measure ℝ)
        p.1).quasiMeasurePreserving.ae_eq_comp hp
    exact intervalIntegral.integral_congr_ae (htr.mono fun s hs _ => hs)
  filter_upwards [h0, hint, hgg₀] with p h0p hintp hggp
  simp only [hintp, hggp]
  exact h0p

/-! ### The main theorem on `ℂ` -/

/-- **Directional Lebesgue differentiation on `ℂ`.** For a locally integrable `f : ℂ → ℝ` and a
unit vector `u : ℂ`, at almost every `z : ℂ` the one-sided directional interval averages of `f`
along the line `z + ℝ • u` converge to `f z`. -/
theorem ae_tendsto_lineAverage {f : ℂ → ℝ} (hf : MeasureTheory.LocallyIntegrable f)
    {u : ℂ} (hu : ‖u‖ = 1) :
    ∀ᵐ z : ℂ,
      Filter.Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, f (z + s • u))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f z)) := by
  set Φ := frame u hu with hΦ
  have hΦmp : MeasurePreserving Φ volume volume := frame_measurePreserving u hu
  -- pull back `f` through the frame
  set g : ℝ × ℝ → ℝ := f ∘ Φ with hg
  have hgloc : LocallyIntegrable g (volume : Measure (ℝ × ℝ)) := by
    rw [hg]
    rw [locallyIntegrable_iff]
    intro K hK
    have himg : IntegrableOn f (Φ '' K) volume :=
      hf.integrableOn_isCompact (hK.image (frame_continuous u hu))
    have hpre : Φ ⁻¹' (Φ '' K) = K := Φ.injective.preimage_image K
    have := (hΦmp.integrableOn_comp_preimage Φ.measurableEmbedding
      (f := f) (s := Φ '' K)).mpr himg
    rwa [hpre] at this
  -- the plane statement for `g`
  have hprod := ae_tendsto_lineAverage_prod g hgloc
  -- transport back to `ℂ`
  have hmp : MeasurePreserving Φ.symm volume volume := hΦmp.symm _
  have := hmp.quasiMeasurePreserving.ae hprod
  filter_upwards [this] with z hz
  -- rewrite `g (Φ.symm z ...) ` in terms of `f (z + s • u)`
  have hΦsymm : Φ (Φ.symm z) = z := Φ.apply_symm_apply z
  have key : ∀ h : ℝ, (∫ s in (0:ℝ)..h, g ((Φ.symm z).1 + s, (Φ.symm z).2))
      = ∫ s in (0:ℝ)..h, f (z + s • u) := by
    intro h
    apply intervalIntegral.integral_congr
    intro s _
    simp only [hg, Function.comp_apply]
    have : Φ ((Φ.symm z).1 + s, (Φ.symm z).2)
        = Φ ((Φ.symm z).1, (Φ.symm z).2) + s • u := by
      rw [hΦ]; rw [← frame_shift u hu]
    rw [show ((Φ.symm z).1, (Φ.symm z).2) = Φ.symm z from rfl] at this
    rw [this, hΦsymm]
  have hval : g (Φ.symm z) = f z := by
    simp only [hg, Function.comp_apply, hΦsymm]
  have hz' : Tendsto (fun h : ℝ => h⁻¹ * ∫ s in (0:ℝ)..h, f (z + s • u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f z)) := by
    rw [← hval]
    refine hz.congr' ?_
    filter_upwards with h
    rw [key h]
  exact hz'

end LineLebesgue

end
