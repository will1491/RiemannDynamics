/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Sphere.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Topology.Algebra.Polynomial

/-!
# Rational maps `ℂ̂ → ℂ̂`

A rational map is a ratio `P/Q` of two complex polynomials. After cancelling
the common factor `gcd(P, Q)`, the resulting coprime pair `(P', Q')` defines
a unique map `ℂ̂ → ℂ̂`:

* on a finite point `w ∈ ℂ` with `Q'(w) ≠ 0`, send `w ↦ P'(w)/Q'(w)`;
* on a finite point `w ∈ ℂ` with `Q'(w) = 0` (necessarily `P'(w) ≠ 0` since
  `P'` and `Q'` are coprime), send `w ↦ ∞`;
* at `∞`, send to the limit of `P'/Q'` as the argument grows: `0` if
  `deg P' < deg Q'`, `lc P' / lc Q'` if degrees agree, and `∞` if
  `deg P' > deg Q'`.

The degree of the resulting rational map is `max(deg P', deg Q')`. This
section defines the underlying data carrier, the extension, the predicate
`IsRational`, and the function `degreeOfRational`.
-/

open OnePoint Polynomial Filter Topology

namespace RiemannDynamics

/-- The raw data of a rational map: two complex polynomials with nonzero
denominator. We do not quotient by `(P, Q) ~ (λP, λQ)` here; downstream
results are stated invariantly. -/
structure RationalData where
  /-- Numerator polynomial. -/
  num : ℂ[X]
  /-- Denominator polynomial. -/
  den : ℂ[X]
  /-- The denominator is nonzero. -/
  den_ne_zero : den ≠ 0

namespace RationalData

variable (r : RationalData)

/-- The reduced numerator: `num` divided by `gcd(num, den)`. -/
noncomputable def numReduced : ℂ[X] := r.num / gcd r.num r.den

/-- The reduced denominator: `den` divided by `gcd(num, den)`. -/
noncomputable def denReduced : ℂ[X] := r.den / gcd r.num r.den

/-- The extension of the rational map `num/den` to `ℂ̂ → ℂ̂`. -/
noncomputable def toSphereMap : ℂ̂ → ℂ̂ := fun z =>
  match z with
  | OnePoint.some w =>
      if r.denReduced.eval w = 0 then ∞
      else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)
  | ∞ =>
      if r.numReduced.natDegree < r.denReduced.natDegree then
        ((0 : ℂ) : ℂ̂)
      else if r.numReduced.natDegree = r.denReduced.natDegree then
        ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂)
      else ∞

/-- The degree of the rational map associated with `r`, defined as the maximum
of the reduced numerator's and denominator's degrees. -/
noncomputable def degree : ℕ :=
  max r.numReduced.natDegree r.denReduced.natDegree

end RationalData

/-- A map `f : ℂ̂ → ℂ̂` is *rational* if it arises from some `RationalData`. -/
def IsRational (f : ℂ̂ → ℂ̂) : Prop :=
  ∃ r : RationalData, f = r.toSphereMap

/-- The degree of a rational map `f : ℂ̂ → ℂ̂`. If `f` is not rational, returns
`0` by convention (we never invoke `degreeOfRational` on non-rational maps in
downstream code). -/
noncomputable def degreeOfRational (f : ℂ̂ → ℂ̂) : ℕ :=
  open Classical in if h : IsRational f then h.choose.degree else 0

/-! ## Basic theorems

These are the Phase 1 statements; proofs land in a later prover pass. -/

/-- A rational map extends uniquely from its `RationalData`: any two
`RationalData` values producing the same `ℂ̂ → ℂ̂` map have equal `degree`. -/
theorem RationalData.degree_well_defined
    (r₁ r₂ : RationalData) (h : r₁.toSphereMap = r₂.toSphereMap) :
    r₁.degree = r₂.degree := by
  -- Step 1: derive cross-product polynomial identity from functional equality.
  have cross : r₁.numReduced * r₂.denReduced = r₂.numReduced * r₁.denReduced := by
    apply Polynomial.funext
    intro w
    simp only [Polynomial.eval_mul]
    have hw := congrFun h ((w : ℂ̂))
    simp only [RationalData.toSphereMap] at hw
    by_cases hd₁ : r₁.denReduced.eval w = 0
    · by_cases hd₂ : r₂.denReduced.eval w = 0
      · rw [hd₁, hd₂]; ring
      · -- r₁ side is ∞, r₂ side is finite — contradiction
        rw [if_pos hd₁, if_neg hd₂] at hw
        exact absurd hw.symm (OnePoint.coe_ne_infty _)
    · by_cases hd₂ : r₂.denReduced.eval w = 0
      · -- r₂ side is ∞, r₁ side is finite — contradiction
        rw [if_neg hd₁, if_pos hd₂] at hw
        exact absurd hw (OnePoint.coe_ne_infty _)
      · -- both denominators nonzero: extract the equality of ℂ-values
        rw [if_neg hd₁, if_neg hd₂] at hw
        have hw' : r₁.numReduced.eval w / r₁.denReduced.eval w
                 = r₂.numReduced.eval w / r₂.denReduced.eval w :=
          OnePoint.coe_eq_coe.mp hw
        field_simp at hw'
        linear_combination hw'
  -- Step 2: derive natDegree equality from cross-product + coprimality.
  -- The reduced numerator and denominator are coprime by construction (gcd divided out).
  have denR₁_ne_zero : r₁.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r₁.den = gcd r₁.num r₁.den * (r₁.den / gcd r₁.num r₁.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r₁.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r₁.den_ne_zero h1
  have denR₂_ne_zero : r₂.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r₂.den = gcd r₂.num r₂.den * (r₂.den / gcd r₂.num r₂.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r₂.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r₂.den_ne_zero h1
  have cop₁ : IsCoprime r₁.numReduced r₁.denReduced :=
    isCoprime_div_gcd_div_gcd r₁.den_ne_zero
  have cop₂ : IsCoprime r₂.numReduced r₂.denReduced :=
    isCoprime_div_gcd_div_gcd r₂.den_ne_zero
  -- From cross product `n₁ * d₂ = n₂ * d₁` and coprimality, derive Associated for d's
  have d_assoc : Associated r₁.denReduced r₂.denReduced := by
    have hd₁ : r₁.denReduced ∣ r₂.denReduced := by
      have : r₁.denReduced ∣ r₂.numReduced * r₁.denReduced := dvd_mul_left _ _
      rw [← cross] at this
      exact cop₁.symm.dvd_of_dvd_mul_left this
    have hd₂ : r₂.denReduced ∣ r₁.denReduced := by
      have : r₂.denReduced ∣ r₁.numReduced * r₂.denReduced := dvd_mul_left _ _
      rw [cross] at this
      exact cop₂.symm.dvd_of_dvd_mul_left this
    exact associated_of_dvd_dvd hd₁ hd₂
  -- For n's, two cases: both zero or both nonzero
  have n_natDeg_eq : r₁.numReduced.natDegree = r₂.numReduced.natDegree := by
    by_cases hn₁ : r₁.numReduced = 0
    · -- if n₁ = 0, then n₁ * d₂ = 0 = n₂ * d₁, and d₁ ≠ 0 so n₂ = 0
      have hn₂ : r₂.numReduced = 0 := by
        have hzero : r₂.numReduced * r₁.denReduced = 0 := by
          rw [← cross, hn₁, zero_mul]
        exact (mul_eq_zero.mp hzero).resolve_right denR₁_ne_zero
      rw [hn₁, hn₂]
    · -- if n₁ ≠ 0, derive Associated n₁ n₂
      have hn₂ : r₂.numReduced ≠ 0 := by
        intro hz
        apply hn₁
        have hzero : r₁.numReduced * r₂.denReduced = 0 := by
          rw [cross, hz, zero_mul]
        exact (mul_eq_zero.mp hzero).resolve_right denR₂_ne_zero
      have n_assoc : Associated r₁.numReduced r₂.numReduced := by
        have hn₁_dvd : r₁.numReduced ∣ r₂.numReduced := by
          have : r₁.numReduced ∣ r₂.numReduced * r₁.denReduced := by
            rw [← cross]; exact dvd_mul_right _ _
          exact cop₁.dvd_of_dvd_mul_right this
        have hn₂_dvd : r₂.numReduced ∣ r₁.numReduced := by
          have : r₂.numReduced ∣ r₁.numReduced * r₂.denReduced := by
            rw [cross]; exact dvd_mul_right _ _
          exact cop₂.dvd_of_dvd_mul_right this
        exact associated_of_dvd_dvd hn₁_dvd hn₂_dvd
      -- Associated polys over ℂ differ by a nonzero scalar, so equal natDegree
      obtain ⟨u, hu⟩ := n_assoc
      have hunatdeg : ((↑u : Polynomial ℂ)).natDegree = 0 := by
        have hu_ne_zero : (↑u : Polynomial ℂ) ≠ 0 := Units.ne_zero _
        have hu_isUnit : IsUnit (↑u : Polynomial ℂ) := Units.isUnit u
        rw [Polynomial.natDegree_eq_zero]
        rcases Polynomial.isUnit_iff.mp hu_isUnit with ⟨c, _, hc⟩
        exact ⟨c, hc⟩
      have : r₂.numReduced.natDegree = (r₁.numReduced * ↑u).natDegree := by rw [hu]
      rw [this, Polynomial.natDegree_mul hn₁ (Units.ne_zero _), hunatdeg, Nat.add_zero]
  have d_natDeg_eq : r₁.denReduced.natDegree = r₂.denReduced.natDegree := by
    obtain ⟨u, hu⟩ := d_assoc
    have hunatdeg : ((↑u : Polynomial ℂ)).natDegree = 0 := by
      have hu_isUnit : IsUnit (↑u : Polynomial ℂ) := Units.isUnit u
      rw [Polynomial.natDegree_eq_zero]
      rcases Polynomial.isUnit_iff.mp hu_isUnit with ⟨c, _, hc⟩
      exact ⟨c, hc⟩
    have : r₂.denReduced.natDegree = (r₁.denReduced * ↑u).natDegree := by rw [hu]
    rw [this, Polynomial.natDegree_mul denR₁_ne_zero (Units.ne_zero _), hunatdeg,
        Nat.add_zero]
  unfold RationalData.degree
  rw [n_natDeg_eq, d_natDeg_eq]

/-- `degreeOfRational` is consistent with `RationalData.degree` for any
witness producing the map. -/
theorem degreeOfRational_eq_of_witness
    (f : ℂ̂ → ℂ̂) (r : RationalData) (h : f = r.toSphereMap) :
    degreeOfRational f = r.degree := by
  have hf : IsRational f := ⟨r, h⟩
  unfold degreeOfRational
  rw [dif_pos hf]
  apply RationalData.degree_well_defined
  rw [← hf.choose_spec, ← h]

/-- A rational map sends `ℂ̂` into `ℂ̂` and is `Continuous` for the
one-point-compactification topology. -/
theorem RationalData.toSphereMap_continuous (r : RationalData) :
    Continuous r.toSphereMap := by
  -- Helpers used in multiple cases.
  have hcont_num : Continuous (fun w : ℂ => r.numReduced.eval w) :=
    Polynomial.continuous r.numReduced
  have hcont_den : Continuous (fun w : ℂ => r.denReduced.eval w) :=
    Polynomial.continuous r.denReduced
  have hdenR_ne_zero : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hcop : IsCoprime r.numReduced r.denReduced :=
    isCoprime_div_gcd_div_gcd r.den_ne_zero
  -- No common roots at finite points: if denReduced(w) = 0 then numReduced(w) ≠ 0.
  have hno_common : ∀ w : ℂ, r.denReduced.eval w = 0 → r.numReduced.eval w ≠ 0 := by
    intro w hdw hnw
    obtain ⟨a, b, hab⟩ := hcop
    have heval : a.eval w * r.numReduced.eval w + b.eval w * r.denReduced.eval w = 1 := by
      have := congrArg (Polynomial.eval w) hab
      simpa [Polynomial.eval_add, Polynomial.eval_mul] using this
    rw [hnw, hdw, mul_zero, mul_zero, add_zero] at heval
    exact zero_ne_one heval
  -- Eventually-nonzero of denReduced on cocompact ℂ (finitely many roots).
  have hden_cocompact : ∀ᶠ z in Filter.cocompact ℂ, r.denReduced.eval z ≠ 0 := by
    have hroots_fin : {z : ℂ | r.denReduced.eval z = 0}.Finite := by
      have hsub : {z : ℂ | r.denReduced.eval z = 0} ⊆ (r.denReduced.roots.toFinset : Set ℂ) := by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz
        simp [Multiset.mem_toFinset, Polynomial.mem_roots hdenR_ne_zero, hz, Polynomial.IsRoot]
      exact ((r.denReduced.roots.toFinset : Set ℂ).toFinite).subset hsub
    have hroots_compact : IsCompact {z : ℂ | r.denReduced.eval z = 0} :=
      hroots_fin.isCompact
    exact hroots_compact.compl_mem_cocompact
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · -- Tendsto at ∞: use the reflection identity to substitute s = 1/z.
    -- Convert from coclosedCompact to cocompact (equal for R1 spaces, hence ℂ).
    rw [Filter.coclosedCompact_eq_cocompact]
    -- Set up m = max(n, d), where n, d are the natDegrees of the reduced polys.
    set n := r.numReduced.natDegree with hn_def
    set d := r.denReduced.natDegree with hd_def
    set m := max n d with hm_def
    set numRev := Polynomial.reflect m r.numReduced with hnumRev_def
    set denRev := Polynomial.reflect m r.denReduced with hdenRev_def
    -- Numerator may be zero. Use `or_split` later.
    have hn_le_m : n ≤ m := le_max_left _ _
    have hd_le_m : d ≤ m := le_max_right _ _
    -- Identity: for z ≠ 0, num(z)/den(z) = numRev(1/z)/denRev(1/z).
    have hident_num : ∀ z : ℂ, z ≠ 0 →
        r.numReduced.eval z = z^m * numRev.eval z⁻¹ := by
      intro z hz
      have hinv : Invertible z := invertibleOfNonzero hz
      have heq : z⁻¹ = ⅟z := (invOf_eq_inv z).symm
      rw [heq, mul_comm]
      have htmp := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z m r.numReduced hn_le_m
      simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] at htmp
      exact htmp.symm
    have hident_den : ∀ z : ℂ, z ≠ 0 →
        r.denReduced.eval z = z^m * denRev.eval z⁻¹ := by
      intro z hz
      have hinv : Invertible z := invertibleOfNonzero hz
      have heq : z⁻¹ = ⅟z := (invOf_eq_inv z).symm
      rw [heq, mul_comm]
      have htmp := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z m r.denReduced hd_le_m
      simp only [Polynomial.eval₂_eq_eval_map, Polynomial.map_id] at htmp
      exact htmp.symm
    -- denRev ≠ 0 since denReduced ≠ 0 and reflection preserves nonzeroness.
    have hdenRev_ne_zero : denRev ≠ 0 := by
      intro heq
      apply hdenR_ne_zero
      -- denReduced.coeff d ≠ 0 implies reflected coeff is also nonzero
      have hcoeff_d : r.denReduced.coeff d ≠ 0 := by
        rw [hd_def]
        exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      have hrev_coeff : denRev.coeff ((Polynomial.revAt m) d) = r.denReduced.coeff d := by
        rw [hdenRev_def, Polynomial.coeff_reflect m r.denReduced (Polynomial.revAt m d),
            Polynomial.revAt_invol]
      rw [heq, Polynomial.coeff_zero] at hrev_coeff
      exact (hcoeff_d hrev_coeff.symm).elim
    -- Limits of numRev, denRev at 0.
    have hnumRev_eval_zero : numRev.eval 0 =
        if n = m then r.numReduced.leadingCoeff else 0 := by
      rw [hnumRev_def]
      rw [show (Polynomial.reflect m r.numReduced).eval 0
              = (Polynomial.reflect m r.numReduced).coeff 0 from
            Polynomial.coeff_zero_eq_eval_zero _ |>.symm,
          Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le m), Nat.sub_zero]
      by_cases hnm : n = m
      · rw [if_pos hnm]
        show r.numReduced.coeff m = r.numReduced.leadingCoeff
        rw [← hnm, hn_def]
        exact Polynomial.coeff_natDegree
      · rw [if_neg hnm]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
    have hdenRev_eval_zero : denRev.eval 0 =
        if d = m then r.denReduced.leadingCoeff else 0 := by
      rw [hdenRev_def]
      rw [show (Polynomial.reflect m r.denReduced).eval 0
              = (Polynomial.reflect m r.denReduced).coeff 0 from
            Polynomial.coeff_zero_eq_eval_zero _ |>.symm,
          Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.zero_le m), Nat.sub_zero]
      by_cases hdm : d = m
      · rw [if_pos hdm]
        show r.denReduced.coeff m = r.denReduced.leadingCoeff
        rw [← hdm, hd_def]
        exact Polynomial.coeff_natDegree
      · rw [if_neg hdm]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega
    -- 1/z tends to 0 on cocompact ℂ.
    have hinv_tendsto : Filter.Tendsto (fun z : ℂ => z⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    -- Eventually z ≠ 0 on cocompact ℂ.
    have hz_ne_cocompact : ∀ᶠ z in Filter.cocompact ℂ, z ≠ 0 := by
      have h0 : IsCompact ({(0 : ℂ)} : Set ℂ) := isCompact_singleton
      filter_upwards [h0.compl_mem_cocompact] with z hz
      intro hzz
      exact hz (by simp [hzz])
    -- Eventually denRev(1/z) ≠ 0 on cocompact: since denRev(0) might be nonzero
    -- in cases n ≤ d, or zero in case n > d; handle case-by-case below.
    -- Continuity of numRev, denRev evaluated at 1/z.
    have hnumRev_tendsto :
        Filter.Tendsto (fun z : ℂ => numRev.eval z⁻¹) (Filter.cocompact ℂ)
          (𝓝 (numRev.eval 0)) :=
      ((Polynomial.continuous numRev).continuousAt (x := 0)).tendsto.comp hinv_tendsto
    have hdenRev_tendsto :
        Filter.Tendsto (fun z : ℂ => denRev.eval z⁻¹) (Filter.cocompact ℂ)
          (𝓝 (denRev.eval 0)) :=
      ((Polynomial.continuous denRev).continuousAt (x := 0)).tendsto.comp hinv_tendsto
    -- Three cases based on n vs d.
    rcases lt_trichotomy n d with hnd | hnd | hnd
    · -- Case 1: n < d, m = d. numRev(0) = 0, denRev(0) = lc den ≠ 0. Limit = 0.
      have hm_eq_d : m = d := by simp [hm_def, hnd.le]
      have hn_ne_m : n ≠ m := by omega
      have hd_eq_m : d = m := hm_eq_d.symm
      have hnumRev0 : numRev.eval 0 = 0 := by rw [hnumRev_eval_zero, if_neg hn_ne_m]
      have hdenRev0 : denRev.eval 0 = r.denReduced.leadingCoeff := by
        rw [hdenRev_eval_zero, if_pos hd_eq_m]
      have hdenRev0_ne : denRev.eval 0 ≠ 0 := by
        rw [hdenRev0]; exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      -- r.toSphereMap ∞ = ↑0
      have hval_inf : r.toSphereMap ∞ = ((0 : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap]
        have hnd' : r.numReduced.natDegree < r.denReduced.natDegree := hnd
        rw [if_pos hnd']
      rw [hval_inf]
      -- Goal: Tendsto (fun z => r.toSphereMap ↑z) (cocompact ℂ) (𝓝 ↑0)
      -- Strategy: eventually den(z) ≠ 0 so r.toSphereMap ↑z = ↑(num/den),
      -- and num/den → 0 in ℂ.
      have hnumOdenRev_tendsto :
          Filter.Tendsto (fun z : ℂ => numRev.eval z⁻¹ / denRev.eval z⁻¹)
            (Filter.cocompact ℂ) (𝓝 0) := by
        have := hnumRev_tendsto.div hdenRev_tendsto hdenRev0_ne
        rw [hnumRev0, zero_div] at this
        exact this
      -- Combine: r.toSphereMap ↑z = ↑(num/den) eventually, and num/den = numRev(1/z)/denRev(1/z).
      have hcong : ∀ᶠ (z : ℂ) in Filter.cocompact ℂ,
          r.toSphereMap (↑z : ℂ̂) =
            ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂) := by
        filter_upwards [hden_cocompact, hz_ne_cocompact] with z hdz hzne
        have hnum := hident_num z hzne
        have hden := hident_den z hzne
        have hzm_ne : z^m ≠ 0 := pow_ne_zero _ hzne
        have : r.toSphereMap (↑z : ℂ̂) =
            ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, hdz, if_false]
        rw [this]
        congr 1
        rw [hnum, hden, mul_div_mul_left _ _ hzm_ne]
      have hcont_coe := (OnePoint.continuous_coe (X := ℂ)).continuousAt (x := (0 : ℂ))
      have : Filter.Tendsto (fun z : ℂ => ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂))
          (Filter.cocompact ℂ) (𝓝 ((0 : ℂ) : ℂ̂)) :=
        hcont_coe.tendsto.comp hnumOdenRev_tendsto
      exact this.congr' (hcong.mono fun _ h => h.symm)
    · -- Case 2: n = d, m = n = d. numRev(0) = lc num, denRev(0) = lc den.
      -- Limit = lc num / lc den.
      have hm_eq_n : m = n := by simp [hm_def, hnd.symm.le]
      have hn_eq_m : n = m := hm_eq_n.symm
      have hd_eq_m : d = m := by omega
      have hnumRev0 : numRev.eval 0 = r.numReduced.leadingCoeff := by
        rw [hnumRev_eval_zero, if_pos hn_eq_m]
      have hdenRev0 : denRev.eval 0 = r.denReduced.leadingCoeff := by
        rw [hdenRev_eval_zero, if_pos hd_eq_m]
      have hdenRev0_ne : denRev.eval 0 ≠ 0 := by
        rw [hdenRev0]; exact Polynomial.leadingCoeff_ne_zero.mpr hdenR_ne_zero
      have hval_inf : r.toSphereMap ∞ =
          ((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap]
        have hnlt : ¬ r.numReduced.natDegree < r.denReduced.natDegree := by omega
        have hneq : r.numReduced.natDegree = r.denReduced.natDegree := hnd
        rw [if_neg hnlt, if_pos hneq]
      rw [hval_inf]
      have hnumOdenRev_tendsto :
          Filter.Tendsto (fun z : ℂ => numRev.eval z⁻¹ / denRev.eval z⁻¹)
            (Filter.cocompact ℂ) (𝓝 (r.numReduced.leadingCoeff / r.denReduced.leadingCoeff)) := by
        have := hnumRev_tendsto.div hdenRev_tendsto hdenRev0_ne
        rw [hnumRev0, hdenRev0] at this
        exact this
      have hcong : ∀ᶠ (z : ℂ) in Filter.cocompact ℂ,
          r.toSphereMap (↑z : ℂ̂) =
            ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂) := by
        filter_upwards [hden_cocompact, hz_ne_cocompact] with z hdz hzne
        have hnum := hident_num z hzne
        have hden := hident_den z hzne
        have hzm_ne : z^m ≠ 0 := pow_ne_zero _ hzne
        have hval : r.toSphereMap (↑z : ℂ̂) =
            ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, hdz, if_false]
        rw [hval]
        congr 1
        rw [hnum, hden, mul_div_mul_left _ _ hzm_ne]
      have hcont_coe :=
        (OnePoint.continuous_coe (X := ℂ)).continuousAt
          (x := (r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ))
      have : Filter.Tendsto (fun z : ℂ => ((numRev.eval z⁻¹ / denRev.eval z⁻¹ : ℂ) : ℂ̂))
          (Filter.cocompact ℂ)
          (𝓝 (((r.numReduced.leadingCoeff / r.denReduced.leadingCoeff : ℂ) : ℂ̂))) :=
        hcont_coe.tendsto.comp hnumOdenRev_tendsto
      exact this.congr' (hcong.mono fun _ h => h.symm)
    · -- Case 3: n > d, m = n. numRev(0) = lc num ≠ 0, denRev(0) = 0.
      -- ‖num/den‖ → ∞.
      have hm_eq_n : m = n := by simp [hm_def, hnd.le]
      have hn_eq_m : n = m := hm_eq_n.symm
      have hd_ne_m : d ≠ m := by omega
      have hnumRev0 : numRev.eval 0 = r.numReduced.leadingCoeff := by
        rw [hnumRev_eval_zero, if_pos hn_eq_m]
      have hdenRev0 : denRev.eval 0 = 0 := by
        rw [hdenRev_eval_zero, if_neg hd_ne_m]
      -- num is nonzero (n > 0 since n > d ≥ 0)
      have hnum_ne_zero : r.numReduced ≠ 0 := by
        intro heq
        have : n = 0 := by rw [hn_def, heq, Polynomial.natDegree_zero]
        omega
      have hnumRev0_ne : numRev.eval 0 ≠ 0 := by
        rw [hnumRev0]; exact Polynomial.leadingCoeff_ne_zero.mpr hnum_ne_zero
      have hval_inf : r.toSphereMap ∞ = ∞ := by
        simp only [RationalData.toSphereMap]
        have hnlt : ¬ r.numReduced.natDegree < r.denReduced.natDegree := by omega
        have hneq : ¬ r.numReduced.natDegree = r.denReduced.natDegree := by omega
        rw [if_neg hnlt, if_neg hneq]
      rw [hval_inf]
      -- Tendsto to ∞ via OnePoint basis at infinity.
      rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).tendsto_right_iff]
      rintro K ⟨_, hK_compact⟩
      -- K is compact, get an upper bound on ‖·‖
      have hMbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖z‖ ≤ M := by
        have himg : IsCompact ((fun z : ℂ => ‖z‖) '' K) := hK_compact.image continuous_norm
        obtain ⟨M, hM⟩ := himg.bddAbove
        refine ⟨max 0 M, le_max_left _ _, fun z hz => ?_⟩
        exact le_trans (hM ⟨z, hz, rfl⟩) (le_max_right _ _)
      obtain ⟨M, hM_nn, hM⟩ := hMbd
      -- We want eventually ‖num(z)/den(z)‖ > M (or den(z) = 0, both go into the target set)
      -- Equivalent: ‖numRev(1/z)/denRev(1/z)‖ > M eventually, by hkey.
      -- Use: ‖numRev(1/z)‖ > ‖lc num‖/2 and ‖denRev(1/z)‖ < ‖lc num‖/(2(M+1)) eventually.
      have hlc_norm_pos : 0 < ‖r.numReduced.leadingCoeff‖ :=
        norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hnum_ne_zero)
      have hbound_num : ∀ᶠ z in Filter.cocompact ℂ,
          ‖r.numReduced.leadingCoeff‖ / 2 < ‖numRev.eval z⁻¹‖ := by
        have hnumRev_norm_tendsto :
            Filter.Tendsto (fun z : ℂ => ‖numRev.eval z⁻¹‖) (Filter.cocompact ℂ)
              (𝓝 (‖r.numReduced.leadingCoeff‖)) := by
          rw [← hnumRev0]
          exact hnumRev_tendsto.norm
        have hpos : ‖r.numReduced.leadingCoeff‖ / 2 < ‖r.numReduced.leadingCoeff‖ := by linarith
        exact hnumRev_norm_tendsto.eventually (eventually_gt_nhds hpos)
      have hbound_den : ∀ᶠ z in Filter.cocompact ℂ,
          ‖denRev.eval z⁻¹‖ < ‖r.numReduced.leadingCoeff‖ / (2 * (M + 1)) := by
        have hdenRev_norm_tendsto :
            Filter.Tendsto (fun z : ℂ => ‖denRev.eval z⁻¹‖) (Filter.cocompact ℂ)
              (𝓝 0) := by
          have h0 : ‖denRev.eval (0 : ℂ)‖ = 0 := by rw [hdenRev0, norm_zero]
          rw [← h0]
          exact hdenRev_tendsto.norm
        have hpos : (0 : ℝ) < ‖r.numReduced.leadingCoeff‖ / (2 * (M + 1)) := by positivity
        exact hdenRev_norm_tendsto.eventually (eventually_lt_nhds hpos)
      filter_upwards [hden_cocompact, hz_ne_cocompact, hbound_num, hbound_den]
        with z hdz hzne hwn hwd
      -- Reduce the membership goal.
      by_cases hdenZ : r.denReduced.eval z = 0
      · -- denominator zero: r.toSphereMap ↑z = ∞ ∈ {∞}
        right
        show r.toSphereMap (↑z : ℂ̂) ∈ ({∞} : Set ℂ̂)
        simp only [RationalData.toSphereMap, hdenZ, if_true, Set.mem_singleton_iff]
      · -- denominator nonzero: r.toSphereMap ↑z = ↑(num/den), ‖num/den‖ > M.
        left
        show r.toSphereMap (↑z : ℂ̂) ∈ ((↑) : ℂ → ℂ̂) '' Kᶜ
        have hval : r.toSphereMap (↑z : ℂ̂) =
            ((r.numReduced.eval z / r.denReduced.eval z : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, hdenZ, if_false]
        rw [hval]
        refine ⟨r.numReduced.eval z / r.denReduced.eval z, ?_, rfl⟩
        intro hin
        have hnorm_le : ‖r.numReduced.eval z / r.denReduced.eval z‖ ≤ M := hM _ hin
        -- Use the identity to rewrite num/den as numRev(1/z)/denRev(1/z).
        have hnum := hident_num z hzne
        have hden := hident_den z hzne
        have hzm_ne : z^m ≠ 0 := pow_ne_zero _ hzne
        have hrewrite : r.numReduced.eval z / r.denReduced.eval z =
            numRev.eval z⁻¹ / denRev.eval z⁻¹ := by
          rw [hnum, hden, mul_div_mul_left _ _ hzm_ne]
        rw [hrewrite, norm_div] at hnorm_le
        -- denRev(1/z) ≠ 0 since denReduced(z) ≠ 0 and the identity.
        have hdenRevInv_ne : denRev.eval z⁻¹ ≠ 0 := by
          intro hz0
          apply hdenZ
          rw [hden, hz0, mul_zero]
        have hdenRevInv_pos : 0 < ‖denRev.eval z⁻¹‖ := norm_pos_iff.mpr hdenRevInv_ne
        rw [div_le_iff₀ hdenRevInv_pos] at hnorm_le
        -- chain: ‖lc num‖/2 < ‖numRev(1/z)‖ ≤ M·‖denRev(1/z)‖ ≤ M·‖lc num‖/(2(M+1)) < ‖lc num‖/2.
        have hMp1_pos : (0 : ℝ) < M + 1 := by linarith
        have hkey₁ : M * ‖denRev.eval z⁻¹‖ ≤ M * (‖r.numReduced.leadingCoeff‖ / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hwd.le hM_nn
        have hkey₂ : M * (‖r.numReduced.leadingCoeff‖ / (2 * (M + 1))) <
            ‖r.numReduced.leadingCoeff‖ / 2 := by
          have hrew : ‖r.numReduced.leadingCoeff‖ / (2 * (M + 1))
              = ‖r.numReduced.leadingCoeff‖ / 2 / (M + 1) := by field_simp
          rw [hrew, ← mul_div_assoc, div_lt_iff₀ hMp1_pos]
          have : M * (‖r.numReduced.leadingCoeff‖ / 2) <
              (M + 1) * (‖r.numReduced.leadingCoeff‖ / 2) :=
            mul_lt_mul_of_pos_right (by linarith) (by linarith)
          linarith
        linarith
  · -- Continuity on finite ℂ.
    rw [continuous_iff_continuousAt]
    intro w₀
    by_cases hpole : r.denReduced.eval w₀ = 0
    · -- Pole case: r.toSphereMap (↑w₀) = ∞.
      have hval₀ : r.toSphereMap (↑w₀ : ℂ̂) = ∞ := by
        simp only [RationalData.toSphereMap, hpole, if_true]
      rw [ContinuousAt, hval₀]
      rw [(OnePoint.hasBasis_nhds_infty (X := ℂ)).tendsto_right_iff]
      rintro K ⟨hK_closed, hK_compact⟩
      -- K is compact, hence bounded; pick `M ≥ 0` bounding ‖·‖ on K.
      have hMbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ‖z‖ ≤ M := by
        have himg : IsCompact ((fun z : ℂ => ‖z‖) '' K) := hK_compact.image continuous_norm
        obtain ⟨M, hM⟩ := himg.bddAbove
        refine ⟨max 0 M, le_max_left _ _, fun z hz => ?_⟩
        exact le_trans (hM ⟨z, hz, rfl⟩) (le_max_right _ _)
      obtain ⟨M, hM_nn, hM⟩ := hMbd
      have hnum_w₀ : r.numReduced.eval w₀ ≠ 0 := hno_common w₀ hpole
      have hnum_norm_pos : 0 < ‖r.numReduced.eval w₀‖ := norm_pos_iff.mpr hnum_w₀
      -- Choose target: |num(w)/den(w)| > M
      -- In a nbhd of w₀, |num(w)| > |num(w₀)|/2 and |den(w)| < |num(w₀)|/(2(M+1)).
      -- Then |num/den| > (|num(w₀)|/2) / (|num(w₀)|/(2(M+1))) = M+1 > M.
      have hbound_num : ∀ᶠ w in nhds w₀,
          ‖r.numReduced.eval w₀‖ / 2 < ‖r.numReduced.eval w‖ := by
        have hpos : (‖r.numReduced.eval w₀‖ / 2 : ℝ) < ‖r.numReduced.eval w₀‖ := by linarith
        exact ContinuousAt.eventually_lt continuousAt_const
          hcont_num.norm.continuousAt hpos
      have hbound_den : ∀ᶠ w in nhds w₀,
          ‖r.denReduced.eval w‖ < ‖r.numReduced.eval w₀‖ / (2 * (M + 1)) := by
        have hMp1_pos : (0 : ℝ) < 2 * (M + 1) := by linarith
        have hpos : (0 : ℝ) < ‖r.numReduced.eval w₀‖ / (2 * (M + 1)) := by positivity
        have hden_z : ‖r.denReduced.eval w₀‖ = 0 := by rw [hpole, norm_zero]
        exact ContinuousAt.eventually_lt hcont_den.norm.continuousAt continuousAt_const
          (by rw [hden_z]; exact hpos)
      filter_upwards [hbound_num, hbound_den] with w hwn hwd
      by_cases h : r.denReduced.eval w = 0
      · -- denominator is zero: value is ∞ ∈ {∞}
        right
        show r.toSphereMap (↑w : ℂ̂) ∈ ({∞} : Set ℂ̂)
        simp only [RationalData.toSphereMap, h, if_true, Set.mem_singleton_iff]
      · -- denominator nonzero: value is ↑(num/den), |num/den| > M ≥ ‖z‖ for z ∈ K, so ∉ K
        left
        show r.toSphereMap (↑w : ℂ̂) ∈ ((↑) : ℂ → ℂ̂) '' Kᶜ
        have hval : r.toSphereMap (↑w : ℂ̂) =
            ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := by
          simp only [RationalData.toSphereMap, h, if_false]
        rw [hval]
        refine ⟨r.numReduced.eval w / r.denReduced.eval w, ?_, rfl⟩
        intro hin
        have hnorm_le : ‖r.numReduced.eval w / r.denReduced.eval w‖ ≤ M := hM _ hin
        have hden_pos : 0 < ‖r.denReduced.eval w‖ := norm_pos_iff.mpr h
        rw [norm_div] at hnorm_le
        have hcontra : ‖r.numReduced.eval w‖ ≤ M * ‖r.denReduced.eval w‖ := by
          rw [div_le_iff₀ hden_pos] at hnorm_le; exact hnorm_le
        -- Derive the contradiction by chaining the three inequalities:
        --   ‖num(w₀)‖/2 < ‖num(w)‖ ≤ M·‖den(w)‖ ≤ M·‖num(w₀)‖/(2(M+1)) < ‖num(w₀)‖/2.
        have hMp1_pos : (0 : ℝ) < M + 1 := by linarith
        have hkey₁ : M * ‖r.denReduced.eval w‖ ≤ M * (‖r.numReduced.eval w₀‖ / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hwd.le hM_nn
        have hkey₂ : M * (‖r.numReduced.eval w₀‖ / (2 * (M + 1))) <
            ‖r.numReduced.eval w₀‖ / 2 := by
          have hrewrite : ‖r.numReduced.eval w₀‖ / (2 * (M + 1))
              = ‖r.numReduced.eval w₀‖ / 2 / (M + 1) := by field_simp
          rw [hrewrite, ← mul_div_assoc, div_lt_iff₀ hMp1_pos]
          have : M * (‖r.numReduced.eval w₀‖ / 2) <
              (M + 1) * (‖r.numReduced.eval w₀‖ / 2) :=
            mul_lt_mul_of_pos_right (by linarith) (by linarith)
          linarith
        linarith
    · -- Non-pole case
      have h_nbhd : ∀ᶠ w in nhds w₀, r.denReduced.eval w ≠ 0 :=
        hcont_den.continuousAt.eventually_ne hpole
      have hval_eq : (fun w : ℂ => r.toSphereMap (↑w : ℂ̂)) =ᶠ[nhds w₀]
                     (fun w => ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)) := by
        filter_upwards [h_nbhd] with w hw
        simp only [RationalData.toSphereMap, hw, if_false]
      have hcont_local : ContinuousAt
          (fun w => ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂)) w₀ :=
        OnePoint.continuous_coe.continuousAt.comp
          (ContinuousAt.div hcont_num.continuousAt hcont_den.continuousAt hpole)
      have hval₀ : r.toSphereMap (↑w₀ : ℂ̂) =
          ((r.numReduced.eval w₀ / r.denReduced.eval w₀ : ℂ) : ℂ̂) := by
        simp only [RationalData.toSphereMap, hpole, if_false]
      rw [ContinuousAt, hval₀]
      have hca : ContinuousAt (fun w : ℂ => r.toSphereMap (↑w : ℂ̂)) w₀ :=
        hcont_local.congr hval_eq.symm
      rw [ContinuousAt] at hca
      rw [hval₀] at hca
      exact hca

/-- The composition of two rational maps is rational, with degree equal to
the product of the degrees (assuming both are nonconstant). -/
theorem isRational_comp {f g : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hg : IsRational g) :
    IsRational (f ∘ g) := by
  sorry

/-- Degree multiplicativity under composition for nonconstant rational maps. -/
theorem degreeOfRational_comp {f g : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hg : IsRational g)
    (hfd : 1 ≤ degreeOfRational f) (hgd : 1 ≤ degreeOfRational g) :
    degreeOfRational (f ∘ g) = degreeOfRational f * degreeOfRational g := by
  sorry

end RiemannDynamics
