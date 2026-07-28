/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.Foundations.Def
import RiemannDynamics.QC.Calculus.Compactness
import RiemannDynamics.QC.Regularity.Quasisymmetry

/-!
# The Teichmüller metric

The Teichmüller pseudodistance between two representatives `x, y` over the base `Γ₀` is
`½ log inf K`, the infimum running over the dilatations of quasiconformal plane maps matching
the boundary transition (`F (y.w t) = x.w t` for all real `t`). It is a pseudometric on
`TeichRep Γ₀`; **Teichmüller space** `Teich Γ₀` is its separation quotient, a genuine metric
space. Rigidity identifies inseparability with equality of boundary maps: the infimum is `1`
exactly when the two normalized solutions agree on the real line.

Completeness of `Teich Γ₀` is not developed here: a Cauchy sequence has representatives with
uniformly bounded dilatation, and a locally uniform limit which is again quasiconformal, but
identifying the limit coefficient as a point of `TeichRep Γ₀` requires control of coefficients
under locally uniform limits beyond the dilatation bound.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The dilatation set and the pseudodistance -/

/-- The set of dilatations of quasiconformal plane maps matching the boundary transition of
the pair `(x, y)`: those `K` with a geometrically `K`-quasiconformal `F` satisfying
`F (y.w t) = x.w t` for every real `t`. Such `F` automatically fix `0` and `1`. -/
def dilatationSet (x y : TeichRep Γ₀) : Set ℝ :=
  {K | ∃ F : ℂ → ℂ, IsQCGeometric F K ∧ ∀ t : ℝ, F (y.w t) = x.w t}

/-- The **Teichmüller pseudodistance**: `½ log` of the least dilatation of a quasiconformal
map matching the boundary transition. -/
noncomputable def teichPseudoDist (x y : TeichRep Γ₀) : ℝ :=
  (1 / 2) * Real.log (sInf (dilatationSet x y))

/-- The dilatation set is nonempty: `x.w ∘ (y.w)⁻¹` is a candidate with dilatation
`x.b.K * y.b.K`. -/
theorem dilatationSet_nonempty (x y : TeichRep Γ₀) : (dilatationSet x y).Nonempty := by
  have hxg : IsQCGeometric x.w x.b.K := x.w_isQCAnalytic.isQCGeometric_K
  have hyg : IsQCGeometric y.w y.b.K := y.w_isQCAnalytic.isQCGeometric_K
  have hinv := isQCGeometric_inv_of_isQCGeometric hyg
  refine ⟨x.b.K * y.b.K, x.w ∘ ⇑(hyg.2.1.isHomeomorph.homeomorph y.w).symm,
    hxg.comp hinv, fun t => ?_⟩
  have hcoe : y.w (t : ℂ) = (hyg.2.1.isHomeomorph.homeomorph y.w) (t : ℂ) :=
    (IsHomeomorph.homeomorph_apply y.w hyg.2.1.isHomeomorph (t : ℂ)).symm
  have hsymm : (hyg.2.1.isHomeomorph.homeomorph y.w).symm (y.w t) = (t : ℂ) := by
    rw [hcoe, Homeomorph.symm_apply_apply]
  rw [Function.comp_apply, hsymm]

/-- Every element of the dilatation set is at least `1`. -/
theorem one_le_of_mem_dilatationSet {x y : TeichRep Γ₀} {K : ℝ}
    (hK : K ∈ dilatationSet x y) : 1 ≤ K := by
  obtain ⟨F, hF, -⟩ := hK
  exact hF.1

/-- The dilatation set is bounded below. -/
theorem bddBelow_dilatationSet (x y : TeichRep Γ₀) : BddBelow (dilatationSet x y) := by
  exact ⟨1, fun _ hK => one_le_of_mem_dilatationSet hK⟩

/-- The infimum of the dilatation set is at least `1`. -/
theorem one_le_sInf_dilatationSet (x y : TeichRep Γ₀) :
    1 ≤ sInf (dilatationSet x y) := by
  exact le_csInf (dilatationSet_nonempty x y)
    fun _ hK => one_le_of_mem_dilatationSet hK

/-- The Teichmüller pseudodistance is nonnegative. -/
theorem teichPseudoDist_nonneg (x y : TeichRep Γ₀) : 0 ≤ teichPseudoDist x y := by
  have hlog : 0 ≤ Real.log (sInf (dilatationSet x y)) :=
    Real.log_nonneg (one_le_sInf_dilatationSet x y)
  unfold teichPseudoDist
  linarith

/-- Explicit upper bound for the pseudodistance through the coefficients of the two
representatives. -/
theorem teichPseudoDist_le_log_K (x y : TeichRep Γ₀) :
    teichPseudoDist x y ≤ (1 / 2) * Real.log (x.b.K * y.b.K) := by
  have hxg : IsQCGeometric x.w x.b.K := x.w_isQCAnalytic.isQCGeometric_K
  have hyg : IsQCGeometric y.w y.b.K := y.w_isQCAnalytic.isQCGeometric_K
  have hinv := isQCGeometric_inv_of_isQCGeometric hyg
  have hmem : x.b.K * y.b.K ∈ dilatationSet x y := by
    refine ⟨x.w ∘ ⇑(hyg.2.1.isHomeomorph.homeomorph y.w).symm, hxg.comp hinv, fun t => ?_⟩
    have hcoe : y.w (t : ℂ) = (hyg.2.1.isHomeomorph.homeomorph y.w) (t : ℂ) :=
      (IsHomeomorph.homeomorph_apply y.w hyg.2.1.isHomeomorph (t : ℂ)).symm
    have hsymm : (hyg.2.1.isHomeomorph.homeomorph y.w).symm (y.w t) = (t : ℂ) := by
      rw [hcoe, Homeomorph.symm_apply_apply]
    rw [Function.comp_apply, hsymm]
  have hle : sInf (dilatationSet x y) ≤ x.b.K * y.b.K :=
    csInf_le (bddBelow_dilatationSet x y) hmem
  have hpos : (0 : ℝ) < sInf (dilatationSet x y) :=
    lt_of_lt_of_le one_pos (one_le_sInf_dilatationSet x y)
  have hlog : Real.log (sInf (dilatationSet x y)) ≤ Real.log (x.b.K * y.b.K) :=
    Real.log_le_log hpos hle
  unfold teichPseudoDist
  linarith

/-- The pseudodistance from a representative to itself vanishes: the identity is a candidate
with dilatation `1`. -/
theorem teichPseudoDist_self (x : TeichRep Γ₀) : teichPseudoDist x x = 0 := by
  have hn : BeltramiCoeff.zero.normInf = 0 := by
    simp [BeltramiCoeff.normInf, BeltramiCoeff.zero]
  have hzero : BeltramiCoeff.zero.K = 1 := by
    rw [BeltramiCoeff.K, hn]
    norm_num
  have hid : IsQCGeometric id 1 := by
    have h := isQCAnalytic_id.isQCGeometric_K
    rwa [hzero] at h
  have hmem : (1 : ℝ) ∈ dilatationSet x x := ⟨id, hid, fun t => rfl⟩
  have h1 : sInf (dilatationSet x x) ≤ 1 := csInf_le (bddBelow_dilatationSet x x) hmem
  have h2 : 1 ≤ sInf (dilatationSet x x) := one_le_sInf_dilatationSet x x
  have heq : sInf (dilatationSet x x) = 1 := le_antisymm h1 h2
  unfold teichPseudoDist
  rw [heq, Real.log_one, mul_zero]

/-- The dilatation sets of a pair and its transpose coincide, by inversion of candidates. -/
theorem dilatationSet_comm (x y : TeichRep Γ₀) :
    dilatationSet x y = dilatationSet y x := by
  have key : ∀ u v : TeichRep Γ₀, dilatationSet u v ⊆ dilatationSet v u := by
    intro u v K hK
    obtain ⟨F, hF, hb⟩ := hK
    refine ⟨⇑(hF.2.1.isHomeomorph.homeomorph F).symm,
      isQCGeometric_inv_of_isQCGeometric hF, fun t => ?_⟩
    have hcoe : F (v.w t) = (hF.2.1.isHomeomorph.homeomorph F) (v.w t) :=
      (IsHomeomorph.homeomorph_apply F hF.2.1.isHomeomorph (v.w t)).symm
    rw [← hb t, hcoe, Homeomorph.symm_apply_apply]
  exact Set.Subset.antisymm (key x y) (key y x)

/-- Symmetry of the Teichmüller pseudodistance. -/
theorem teichPseudoDist_comm (x y : TeichRep Γ₀) :
    teichPseudoDist x y = teichPseudoDist y x := by
  unfold teichPseudoDist
  rw [dilatationSet_comm]

/-- Triangle inequality for the Teichmüller pseudodistance: candidates compose with
multiplying dilatations, and `log` turns the multiplicative bound into an additive one. -/
theorem teichPseudoDist_triangle (x y z : TeichRep Γ₀) :
    teichPseudoDist x z ≤ teichPseudoDist x y + teichPseudoDist y z := by
  have hcomp : ∀ K₁ ∈ dilatationSet x y, ∀ K₂ ∈ dilatationSet y z,
      K₁ * K₂ ∈ dilatationSet x z := by
    rintro K₁ ⟨F₁, hF₁, hb₁⟩ K₂ ⟨F₂, hF₂, hb₂⟩
    refine ⟨F₁ ∘ F₂, hF₁.comp hF₂, fun t => ?_⟩
    rw [Function.comp_apply, hb₂ t, hb₁ t]
  have ha1 : 1 ≤ sInf (dilatationSet x y) := one_le_sInf_dilatationSet x y
  have hb1 : 1 ≤ sInf (dilatationSet y z) := one_le_sInf_dilatationSet y z
  have hc1 : 1 ≤ sInf (dilatationSet x z) := one_le_sInf_dilatationSet x z
  have hapos : (0 : ℝ) < sInf (dilatationSet x y) := lt_of_lt_of_le one_pos ha1
  have hstep : ∀ K₂ ∈ dilatationSet y z,
      sInf (dilatationSet x z) ≤ sInf (dilatationSet x y) * K₂ := by
    intro K₂ hK₂
    have hK₂pos : (0 : ℝ) < K₂ :=
      lt_of_lt_of_le one_pos (one_le_of_mem_dilatationSet hK₂)
    have hlb : ∀ K₁ ∈ dilatationSet x y, sInf (dilatationSet x z) / K₂ ≤ K₁ := by
      intro K₁ hK₁
      have hle : sInf (dilatationSet x z) ≤ K₁ * K₂ :=
        csInf_le (bddBelow_dilatationSet x z) (hcomp K₁ hK₁ K₂ hK₂)
      exact (div_le_iff₀ hK₂pos).mpr hle
    have h := le_csInf (dilatationSet_nonempty x y) hlb
    exact (div_le_iff₀ hK₂pos).mp h
  have hprod : sInf (dilatationSet x z)
      ≤ sInf (dilatationSet x y) * sInf (dilatationSet y z) := by
    have hlb2 : ∀ K₂ ∈ dilatationSet y z, sInf (dilatationSet x z) / sInf (dilatationSet x y)
        ≤ K₂ := by
      intro K₂ hK₂
      rw [div_le_iff₀ hapos, mul_comm]
      exact hstep K₂ hK₂
    have h := le_csInf (dilatationSet_nonempty y z) hlb2
    rw [div_le_iff₀ hapos] at h
    rw [mul_comm] at h
    exact h
  have hcpos : (0 : ℝ) < sInf (dilatationSet x z) := lt_of_lt_of_le one_pos hc1
  have hane : sInf (dilatationSet x y) ≠ 0 := ne_of_gt hapos
  have hbne : sInf (dilatationSet y z) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hb1)
  have hlog : Real.log (sInf (dilatationSet x z))
      ≤ Real.log (sInf (dilatationSet x y)) + Real.log (sInf (dilatationSet y z)) := by
    have h1 : Real.log (sInf (dilatationSet x z))
        ≤ Real.log (sInf (dilatationSet x y) * sInf (dilatationSet y z)) :=
      Real.log_le_log hcpos hprod
    rwa [Real.log_mul hane hbne] at h1
  unfold teichPseudoDist
  linarith

/-- The Teichmüller pseudometric on representatives. -/
noncomputable instance : PseudoMetricSpace (TeichRep Γ₀) where
  dist := teichPseudoDist
  dist_self := teichPseudoDist_self
  dist_comm := teichPseudoDist_comm
  dist_triangle := teichPseudoDist_triangle

/-! ## Teichmüller space -/

/-- **Teichmüller space** over the base `Γ₀`: the separation quotient of the space of
representatives under the Teichmüller pseudometric. -/
def Teich (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  SeparationQuotient (TeichRep Γ₀)

/-- Teichmüller space is a metric space. -/
noncomputable instance : MetricSpace (Teich Γ₀) :=
  inferInstanceAs (MetricSpace (SeparationQuotient (TeichRep Γ₀)))

/-- The point of Teichmüller space determined by a representative. -/
noncomputable def Teich.mk (x : TeichRep Γ₀) : Teich Γ₀ := SeparationQuotient.mk x

/-- The base point of Teichmüller space: the class of the zero coefficient. -/
noncomputable def Teich.base (Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Teich Γ₀ :=
  Teich.mk (TeichRep.zero Γ₀)

instance : Nonempty (Teich Γ₀) := ⟨Teich.base Γ₀⟩

/-- The distance on Teichmüller space is computed by the pseudodistance of any two
representatives. -/
theorem Teich.dist_mk (x y : TeichRep Γ₀) :
    dist (SeparationQuotient.mk x : Teich Γ₀) (SeparationQuotient.mk y)
      = teichPseudoDist x y :=
  SeparationQuotient.dist_mk x y

/-! ## Rigidity -/

/-- A map that is geometrically `K`-quasiconformal for every `K > 1` is geometrically
`1`-quasiconformal. -/
theorem isQCGeometric_one_of_forall_gt {f : ℂ → ℂ}
    (h : ∀ K : ℝ, 1 < K → IsQCGeometric f K) : IsQCGeometric f 1 := by
  refine ⟨le_rfl, (h 2 one_lt_two).2.1, fun Q => ?_⟩
  have hofReal : Filter.Tendsto (fun K : ℝ => ENNReal.ofReal K)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (ENNReal.ofReal 1)) :=
    (ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hne : ENNReal.ofReal 1 ≠ 0 := by
    rw [ENNReal.ofReal_one]
    exact one_ne_zero
  have htend : Filter.Tendsto (fun K : ℝ => ENNReal.ofReal K * Q.modulus)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (ENNReal.ofReal 1 * Q.modulus)) :=
    ENNReal.Tendsto.mul_const hofReal (Or.inl hne)
  have hev : ∀ᶠ K in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      curveModulus (Q.imageCurveFamily f) ≤ ENNReal.ofReal K * Q.modulus :=
    eventually_nhdsWithin_of_forall fun K hK => (h K (Set.mem_Ioi.mp hK)).2.2 Q
  exact ge_of_tendsto htend hev

/-- Equal boundary maps give vanishing pseudodistance: the identity is a candidate with
dilatation `1`. -/
theorem teichPseudoDist_eq_zero_of_boundary_eq {x y : TeichRep Γ₀}
    (h : x.boundary = y.boundary) : teichPseudoDist x y = 0 := by
  have hw : ∀ t : ℝ, y.w t = x.w t := by
    intro t
    rw [y.w_ofReal t, x.w_ofReal t, h]
  have hn : BeltramiCoeff.zero.normInf = 0 := by
    simp [BeltramiCoeff.normInf, BeltramiCoeff.zero]
  have hzero : BeltramiCoeff.zero.K = 1 := by
    rw [BeltramiCoeff.K, hn]
    norm_num
  have hid : IsQCGeometric id 1 := by
    have h2 := isQCAnalytic_id.isQCGeometric_K
    rwa [hzero] at h2
  have hmem : (1 : ℝ) ∈ dilatationSet x y := ⟨id, hid, fun t => hw t⟩
  have h1 : sInf (dilatationSet x y) ≤ 1 := csInf_le (bddBelow_dilatationSet x y) hmem
  have h2 : 1 ≤ sInf (dilatationSet x y) := one_le_sInf_dilatationSet x y
  unfold teichPseudoDist
  rw [le_antisymm h1 h2, Real.log_one, mul_zero]

/-- Rigidity: vanishing pseudodistance forces the two normalized solutions to agree on the
real line. Candidates with dilatation tending to `1` subconverge locally uniformly to a
`1`-quasiconformal map fixing `0` and `1`, which is the identity. -/
theorem w_eq_on_real_of_teichPseudoDist_eq_zero {x y : TeichRep Γ₀}
    (h : teichPseudoDist x y = 0) : ∀ t : ℝ, y.w t = x.w t := by
  classical
  -- § 1. Vanishing pseudodistance forces the infimum of the dilatation set to be `1`.
  have hS1 : 1 ≤ sInf (dilatationSet x y) := one_le_sInf_dilatationSet x y
  have hpos : (0 : ℝ) < sInf (dilatationSet x y) := lt_of_lt_of_le one_pos hS1
  have hlog : Real.log (sInf (dilatationSet x y)) = 0 := by
    unfold teichPseudoDist at h
    linarith
  have hsInf : sInf (dilatationSet x y) = 1 := by
    have h2 := Real.exp_log hpos
    rw [hlog, Real.exp_zero] at h2
    exact h2.symm
  -- § 2. Candidates with dilatation below `1 + 1/(n+1)`.
  have hex : ∀ n : ℕ, ∃ K ∈ dilatationSet x y, K < 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    apply exists_lt_of_csInf_lt (dilatationSet_nonempty x y)
    rw [hsInf]
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose Kn hKmem hKlt using hex
  have hFex : ∀ n : ℕ, ∃ F : ℂ → ℂ, IsQCGeometric F (Kn n) ∧ ∀ t : ℝ, F (y.w t) = x.w t :=
    fun n => hKmem n
  choose F hFqc hFb using hFex
  -- § 3. Every candidate fixes `0` and `1`.
  have hF0 : ∀ n, F n 0 = 0 := by
    intro n
    have h0 := hFb n 0
    rwa [Complex.ofReal_zero, y.w_zero, x.w_zero] at h0
  have hF1 : ∀ n, F n 1 = 1 := by
    intro n
    have h1 := hFb n 1
    rwa [Complex.ofReal_one, y.w_one, x.w_one] at h1
  -- § 4. Uniform dilatation bound `2` and the normal-family extraction.
  have hone_div_le : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hFK2 : ∀ n, IsQCGeometric (F n) 2 := by
    intro n
    exact (hFqc n).mono (by linarith [hKlt n, hone_div_le n])
  obtain ⟨φ, g, hφ, -, hllu⟩ :=
    exists_subseq_tendstoLocallyUniformly_isQCGeometric hFK2
      (zero_ne_one : (0 : ℂ) ≠ 1) (zero_ne_one : (0 : ℂ) ≠ 1) hF0 hF1
  have hgpt : ∀ z : ℂ, Filter.Tendsto (fun k => F (φ k) z) Filter.atTop (nhds (g z)) :=
    fun z => (tendstoLocallyUniformlyOn_univ.mpr hllu).tendsto_at (Set.mem_univ z)
  -- § 5. The limit is `K`-quasiconformal for every `K > 1`: re-extract the `(1+ε)`-tail.
  have hgAll : ∀ K : ℝ, 1 < K → IsQCGeometric g K := by
    intro K hK
    have hKpos : (0 : ℝ) < K - 1 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (K - 1))
    have hNle : 1 / ((N : ℝ) + 1) ≤ K - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / (K - 1) ≤ (N : ℝ) + 1 := le_trans hN (by linarith)
      calc (1 : ℝ) = (K - 1) * (1 / (K - 1)) := (mul_one_div_cancel (ne_of_gt hKpos)).symm
        _ ≤ (K - 1) * ((N : ℝ) + 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hKpos)
    have htail : ∀ j : ℕ, IsQCGeometric (F (φ (j + N))) K := by
      intro j
      have hge : N ≤ φ (j + N) := le_trans (Nat.le_add_left N j) hφ.le_apply
      have hmono : 1 / ((φ (j + N) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hcast : ((N : ℝ)) ≤ ((φ (j + N) : ℕ) : ℝ) := Nat.cast_le.mpr hge
        linarith
      exact (hFqc (φ (j + N))).mono (by linarith [hKlt (φ (j + N))])
    have hG0 : ∀ j : ℕ, F (φ (j + N)) 0 = 0 := fun j => hF0 _
    have hG1 : ∀ j : ℕ, F (φ (j + N)) 1 = 1 := fun j => hF1 _
    obtain ⟨ψ, g', hψ, hg'K, hllu'⟩ :=
      exists_subseq_tendstoLocallyUniformly_isQCGeometric htail
        (zero_ne_one : (0 : ℂ) ≠ 1) (zero_ne_one : (0 : ℂ) ≠ 1) hG0 hG1
    -- The sub-subsequence still converges locally uniformly to `g`.
    have hidx : Filter.Tendsto (fun k => ψ k + N) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun k => Nat.le_add_right (ψ k) N) hψ.tendsto_atTop
    have hllu2 : TendstoLocallyUniformly (fun k => F (φ (ψ k + N))) g Filter.atTop := by
      intro U hU z
      obtain ⟨t, ht, hev⟩ := hllu U hU z
      exact ⟨t, ht, hidx.eventually hev⟩
    -- Locally uniform limits are pointwise limits, and limits are unique: `g' = g`.
    have hgg : g' = g := by
      funext z
      have hp1 : Filter.Tendsto (fun k => F (φ (ψ k + N)) z) Filter.atTop (nhds (g' z)) :=
        (tendstoLocallyUniformlyOn_univ.mpr hllu').tendsto_at (Set.mem_univ z)
      have hp2 : Filter.Tendsto (fun k => F (φ (ψ k + N)) z) Filter.atTop (nhds (g z)) :=
        (tendstoLocallyUniformlyOn_univ.mpr hllu2).tendsto_at (Set.mem_univ z)
      exact tendsto_nhds_unique hp1 hp2
    rw [← hgg]
    exact hg'K
  -- § 6. `g` is `1`-quasiconformal, hence conformal, affine, and the identity.
  have hg1 : IsQCGeometric g 1 := isQCGeometric_one_of_forall_gt hgAll
  obtain ⟨b₁, hbn, hbQC⟩ := isQCAnalytic_of_isQCGeometric le_rfl hg1
  have hbn0 : b₁.normInf = 0 := by
    have h0 : b₁.normInf ≤ 0 := by
      have hb := hbn
      norm_num at hb
      exact hb
    exact le_antisymm h0 b₁.normInf_nonneg
  have hbe : eLpNormEssSup b₁.μ volume = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hbn0 with h0 | htop
    · exact h0
    · exact absurd htop (ne_top_of_lt b₁.bound)
  have hmu : b₁.μ =ᵐ[volume] BeltramiCoeff.zero.μ := eLpNormEssSup_eq_zero_iff.mp hbe
  have hgz : IsQCAnalytic g BeltramiCoeff.zero := hbQC.congr_coeff hmu
  have hgdiff : Differentiable ℂ g := weyl_lemma hgz rfl
  have hginj : Function.Injective g := hgz.injective
  obtain ⟨a, c, -, hgeq⟩ := eq_affine_of_differentiable_of_injective hgdiff hginj
  have hg0 : g 0 = 0 := by
    have hp := hgpt 0
    have hconst : (fun k => F (φ k) (0 : ℂ)) = fun _ => (0 : ℂ) :=
      funext fun k => hF0 (φ k)
    rw [hconst] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds
  have hg1' : g 1 = 1 := by
    have hp := hgpt 1
    have hconst : (fun k => F (φ k) (1 : ℂ)) = fun _ => (1 : ℂ) :=
      funext fun k => hF1 (φ k)
    rw [hconst] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds
  have hc : c = 0 := by
    have h0 := hg0
    rw [hgeq] at h0
    simpa using h0
  have ha1 : a = 1 := by
    have h1 := hg1'
    rw [hgeq, hc] at h1
    simpa using h1
  -- § 7. Along the real line the candidates are constantly `x.w t`, so `g (y.w t) = x.w t`.
  intro t
  have hp := hgpt (y.w t)
  have hconst : (fun k => F (φ k) (y.w t)) = fun _ => x.w t :=
    funext fun k => hFb (φ k) t
  rw [hconst] at hp
  have hgy : g (y.w t) = x.w t := tendsto_nhds_unique hp tendsto_const_nhds
  rw [hgeq, ha1, hc] at hgy
  simpa using hgy

/-- Inseparability in the Teichmüller pseudometric is equality of the boundary values of the
normalized solutions. -/
theorem inseparable_iff_boundary_eq {x y : TeichRep Γ₀} :
    Inseparable x y ↔ ∀ t : ℝ, x.w t = y.w t := by
  rw [Metric.inseparable_iff]
  constructor
  · intro h t
    exact (w_eq_on_real_of_teichPseudoDist_eq_zero h t).symm
  · intro h
    have hb : x.boundary = y.boundary := by
      funext t
      have hwt := h t
      change (x.w t).re = (y.w t).re
      rw [hwt]
    exact teichPseudoDist_eq_zero_of_boundary_eq hb

/-- Two representatives give the same point of Teichmüller space exactly when their
normalized solutions agree on the real line. -/
theorem Teich.mk_eq_mk_iff_boundary {x y : TeichRep Γ₀} :
    (SeparationQuotient.mk x : Teich Γ₀) = SeparationQuotient.mk y ↔
      ∀ t : ℝ, x.w t = y.w t := by
  exact SeparationQuotient.mk_eq_mk.trans inseparable_iff_boundary_eq

end RiemannDynamics
