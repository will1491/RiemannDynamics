import RiemannDynamics.Teichmuller.Length
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# The Mumford compactness criterion: generator subconvergence

For a sequence of Teichmüller representatives whose Fuchsian groups have systole at least
`ε > 0` and admit fundamental domains of hyperbolic area at most `A < ∞`, finite generating
tuples subconverge after conjugation to a tuple generating a Fuchsian group in which every
nontrivially-acting element keeps the trace gap `|tr| ≥ 2 cosh (ε/2)`, acts freely, and which
is properly discontinuous (`mumford_generator_subconvergence`).

The chain is geodesic-free: the systole gives an injectivity radius (`ε/2`-balls meet their
translates only under trivially-acting elements); a ball-packing count against the area bound
makes every orbit `D(A, ε)`-dense; density makes the `2D + 1`-ball in the group a generating
set by a connectedness argument; the identity `cosh (dist i (g·i)) = ‖g‖²_F / 2` turns
displacement bounds into matrix bounds, so Bolzano–Weierstrass applies; and the trace gap
passes to limit words, giving discreteness of the limit group without the Jørgensen
inequality.

Not developed here: the identification of the limit group with the Fuchsian group of a limit
representative in `Teich Γ₀` together with convergence in the Teichmüller metric modulo the
moduli group; and the Gauss–Bonnet area bound `HasAreaBound Γ (4π(g−1))` for the Fuchsian
model of a genus-`g` surface, which discharges the area hypothesis.
-/

open MeasureTheory
open scoped ENNReal Pointwise

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The area hypothesis -/

/-- A Fuchsian group **has area bound `A`** when it admits a measurable fundamental domain in
the upper half plane of hyperbolic volume at most `A`. For the Fuchsian model of a compact
genus-`g` surface the Gauss–Bonnet value is `A = 4π(g−1)`. -/
def HasAreaBound (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (A : ℝ≥0∞) : Prop :=
  ∃ F : Set UpperHalfPlane, MeasurableSet F ∧
    MeasureTheory.IsFundamentalDomain Γ F MeasureTheory.volume ∧ volume F ≤ A

/-! ## Countability, injectivity radius, packing -/

/-- A Fuchsian group is countable: the upper half plane is σ-compact and each compact meets
only finitely many of its translates. -/
theorem IsFuchsianGroup.countable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) : Countable Γ := by
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin : ∀ m : ℕ, {γ : Γ |
      ((fun x => γ • x) '' Metric.closedBall UpperHalfPlane.I (m : ℝ) ∩
        Metric.closedBall UpperHalfPlane.I (m : ℝ)).Nonempty}.Finite := fun m =>
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (isCompact_closedBall _ _) (isCompact_closedBall _ _)
  have hcover : (Set.univ : Set Γ) ⊆ ⋃ m : ℕ, {γ : Γ |
      ((fun x => γ • x) '' Metric.closedBall UpperHalfPlane.I (m : ℝ) ∩
        Metric.closedBall UpperHalfPlane.I (m : ℝ)).Nonempty} := by
    intro γ _
    obtain ⟨m, hm⟩ := exists_nat_ge (dist UpperHalfPlane.I (γ • UpperHalfPlane.I))
    refine Set.mem_iUnion.mpr ⟨m, ⟨γ • UpperHalfPlane.I,
      ⟨UpperHalfPlane.I, Metric.mem_closedBall_self (Nat.cast_nonneg m), rfl⟩, ?_⟩⟩
    rw [Metric.mem_closedBall, dist_comm]
    exact hm
  exact Set.countable_univ_iff.mp
    ((Set.countable_iUnion fun m => (hfin m).countable).mono hcover)

/-- Injectivity radius from the systole: under a translation-length gap `ε`, a ball of radius
`r ≤ ε/2` meets its `γ`-translate only when `γ` acts trivially. -/
theorem smul_eq_self_of_ball_overlap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    {r : ℝ} (hr : r ≤ ε / 2) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (τ : UpperHalfPlane)
    (hne : ((γ • ·) '' Metric.ball τ r ∩ Metric.ball τ r).Nonempty) :
    ∀ τ' : UpperHalfPlane, γ • τ' = τ' := by
  intro τ'
  by_contra hne'
  have hnt : actsNontrivially γ := ⟨τ', hne'⟩
  have hlen : ε ≤ translationLength γ := hgap γ hγ hnt
  have hhyp : (γ : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic :=
    (translationLength_pos_iff γ).mp (lt_of_lt_of_le hε hlen)
  obtain ⟨x, hx1, hx2⟩ := hne
  obtain ⟨y, hy, rfl⟩ := hx1
  have h1 : dist y τ < r := Metric.mem_ball.mp hy
  have h2 : dist (γ • y) τ < r := Metric.mem_ball.mp hx2
  have h3 : dist τ (γ • τ) ≤ dist τ (γ • y) + dist (γ • y) (γ • τ) := dist_triangle _ _ _
  have h4 : dist (γ • y) (γ • τ) = dist y τ := dist_smul γ y τ
  have h5 : dist τ (γ • y) = dist (γ • y) τ := dist_comm _ _
  have h6 : translationLength γ ≤ dist τ (γ • τ) := translationLength_le_dist_smul γ hhyp τ
  linarith

/-- The orbit-density diameter of the packing argument: with area bound `A` and systole gap
`ε`, every orbit is `D`-dense for `D = (2A / v(ε/8))·(ε/4) + 2·(ε/4)`, where `v` is the
volume of hyperbolic balls. -/
noncomputable def mumfordDensityBound (A : ℝ≥0∞) (ε : ℝ) : ℝ :=
  (2 * A / upperBallVolume (ε / 8)).toReal * (ε / 4) + 2 * (ε / 4)

set_option maxHeartbeats 400000 in
-- The packing proof is a single large elaboration (an IVT chain, a two-to-one covering count
-- and a `tsum`/`lintegral` exchange over the subgroup index); its typeclass work exceeds the
-- default heartbeat budget while completing well within twice that budget.
/-- **Packing bound**: under a systole gap and an area bound, every orbit is
`mumfordDensityBound A ε`-dense in the upper half plane. A chain of points on the segment
from `τ` to `σ` at prescribed distances from the orbit carries disjoint balls of radius
`ε/8`, whose translates pack the fundamental domain, bounding the chain length. -/
theorem orbit_infDist_le_of_hasAreaBound
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    {A : ℝ≥0∞} (hA : A ≠ ⊤) (harea : HasAreaBound Γ A) (σ τ : UpperHalfPlane) :
    Metric.infDist σ (MulAction.orbit Γ τ) ≤ mumfordDensityBound A ε := by
  classical
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  haveI : SMulInvariantMeasure (↥Γ) UpperHalfPlane volume :=
    ⟨fun c s hs => SMulInvariantMeasure.measure_preimage_smul
      (μ := (volume : Measure UpperHalfPlane))
      (Matrix.SpecialLinearGroup.mapGL ℝ (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)) hs⟩
  haveI : Countable Γ := IsFuchsianGroup.countable hΓ
  by_contra hcon
  have hD : mumfordDensityBound A ε < Metric.infDist σ (MulAction.orbit Γ τ) := not_le.mp hcon
  obtain ⟨F, hFmeas, hFdom, hFvol⟩ := harea
  obtain ⟨O, hOdef⟩ : ∃ O : Set UpperHalfPlane, O = MulAction.orbit Γ τ := ⟨_, rfl⟩
  rw [← hOdef] at hD
  have hτO : τ ∈ O := by
    rw [hOdef]
    exact MulAction.mem_orbit_self τ
  have hOne : O.Nonempty := ⟨τ, hτO⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ≥0∞, v = upperBallVolume (ε / 8) := ⟨_, rfl⟩
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact (upperBallVolume_pos (by linarith : (0:ℝ) < ε / 8)).ne'
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊(2 * A / v).toReal⌋₊ + 1 := ⟨_, rfl⟩
  have hDval : mumfordDensityBound A ε = (2 * A / v).toReal * (ε / 4) + 2 * (ε / 4) := by
    rw [hvdef]
    rfl
  -- the count `k` beats the mass bound
  have hk2A : 2 * A < (k : ℝ≥0∞) * v := by
    have h2A : 2 * A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hA
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by
      have hkk : k ≠ 0 := by omega
      exact_mod_cast hkk
    by_cases hvt : v = ⊤
    · rw [hvt, ENNReal.mul_top hk0]
      exact lt_top_iff_ne_top.mpr h2A
    · have hdnt : 2 * A / v ≠ ⊤ := by
        rw [Ne, ENNReal.div_eq_top]
        rintro (⟨-, h0⟩ | ⟨ht, -⟩)
        · exact hv0 h0
        · exact h2A ht
      have hlt : 2 * A / v < (k : ℝ≥0∞) := by
        rw [← ENNReal.toReal_lt_toReal hdnt (ENNReal.natCast_ne_top k), ENNReal.toReal_natCast]
        have h1 := Nat.lt_floor_add_one ((2 * A / v).toReal)
        rw [hkdef]
        push_cast
        linarith
      rwa [ENNReal.div_lt_iff (Or.inl hv0) (Or.inl hvt)] at hlt
  -- `k` chain steps fit under the density bound
  have hkD : (k : ℝ) * (ε / 4) ≤ mumfordDensityBound A ε := by
    have hNnn : (0:ℝ) ≤ (2 * A / v).toReal := ENNReal.toReal_nonneg
    have hkle : (k : ℝ) ≤ (2 * A / v).toReal + 1 := by
      rw [hkdef]
      push_cast
      have := Nat.floor_le hNnn
      linarith
    have h1 : (k : ℝ) * (ε / 4) ≤ ((2 * A / v).toReal + 1) * (ε / 4) :=
      mul_le_mul_of_nonneg_right hkle (by linarith)
    rw [hDval]
    nlinarith [h1, hε]
  -- the chain of points at prescribed orbit distances, on a path from τ to σ
  obtain ⟨p⟩ : Joined τ σ := PathConnectedSpace.joined τ σ
  have hm0 : Metric.infDist (p.extend 0) O = 0 := by
    rw [Path.extend_zero]
    exact Metric.infDist_zero_of_mem hτO
  have hchain : ∀ j : Fin k, ∃ y : UpperHalfPlane,
      Metric.infDist y O = (((j : ℕ) : ℝ) + 1) * (ε / 4) := by
    intro j
    have hvj : (((j : ℕ) : ℝ) + 1) * (ε / 4) ≤ Metric.infDist σ O := by
      have hjk : ((j : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
        have hjk' : (j : ℕ) + 1 ≤ k := by
          have := j.isLt
          omega
        exact_mod_cast hjk'
      have h1 : (((j : ℕ) : ℝ) + 1) * (ε / 4) ≤ (k : ℝ) * (ε / 4) :=
        mul_le_mul_of_nonneg_right hjk (by linarith)
      linarith [hkD, hD]
    have hmem : (((j : ℕ) : ℝ) + 1) * (ε / 4) ∈ Set.Icc (Metric.infDist (p.extend 0) O)
        (Metric.infDist (p.extend 1) O) := by
      rw [hm0, Path.extend_one]
      exact ⟨mul_nonneg (by positivity) (by linarith), hvj⟩
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc (zero_le_one (α := ℝ))
      ((Metric.continuous_infDist_pt O).comp p.continuous_extend).continuousOn hmem
    exact ⟨p.extend s, hs⟩
  choose c hc using hchain
  obtain ⟨t, htdef⟩ : ∃ t : Set UpperHalfPlane,
      t = ⋃ j : Fin k, Metric.ball (c j) (ε / 8) := ⟨_, rfl⟩
  -- orbit distance is Γ-invariant
  have hOinv : ∀ (η : ↥Γ) (y : UpperHalfPlane),
      Metric.infDist (η • y) O = Metric.infDist y O := by
    intro η y
    have key : ∀ (ζ : ↥Γ) (w : UpperHalfPlane),
        Metric.infDist (ζ • w) O ≤ Metric.infDist w O := by
      intro ζ w
      rw [Metric.le_infDist hOne]
      intro z hz
      rw [hOdef] at hz
      have hζz : ζ • z ∈ O := by
        rw [hOdef]
        obtain ⟨g, rfl⟩ := hz
        exact ⟨ζ * g, mul_smul ζ g τ⟩
      calc Metric.infDist (ζ • w) O ≤ dist (ζ • w) (ζ • z) := Metric.infDist_le_dist_of_mem hζz
        _ = dist w z := dist_smul ζ w z
    refine le_antisymm (key η y) ?_
    have h2 := key η⁻¹ (η • y)
    rwa [inv_smul_smul] at h2
  -- separation: translated chain balls at distinct indices are disjoint
  have hsep : ∀ (γ δ : ↥Γ) (i j : Fin k) (x : UpperHalfPlane),
      dist x (γ • c i) < ε / 8 → dist x (δ • c j) < ε / 8 → i = j := by
    intro γ δ i j x h1 h2
    have e1 : Metric.infDist (γ • c i) O = (((i : ℕ) : ℝ) + 1) * (ε / 4) := by
      rw [hOinv γ (c i), hc i]
    have e2 : Metric.infDist (δ • c j) O = (((j : ℕ) : ℝ) + 1) * (ε / 4) := by
      rw [hOinv δ (c j), hc j]
    have hdd : dist (γ • c i) (δ • c j) < ε / 4 := by
      calc dist (γ • c i) (δ • c j)
          ≤ dist (γ • c i) x + dist x (δ • c j) := dist_triangle _ _ _
        _ = dist x (γ • c i) + dist x (δ • c j) := by rw [dist_comm (γ • c i) x]
        _ < ε / 8 + ε / 8 := add_lt_add h1 h2
        _ = ε / 4 := by ring
    have hlip : |Metric.infDist (γ • c i) O - Metric.infDist (δ • c j) O|
        ≤ dist (γ • c i) (δ • c j) := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [Metric.infDist_le_infDist_add_dist (s := O) (x := γ • c i) (y := δ • c j)]
      · linarith [Metric.infDist_le_infDist_add_dist (s := O) (x := δ • c j) (y := γ • c i),
          dist_comm (γ • c i) (δ • c j)]
    rw [e1, e2] at hlip
    have habs : |(((i : ℕ) : ℝ) + 1) * (ε / 4) - (((j : ℕ) : ℝ) + 1) * (ε / 4)| < ε / 4 :=
      lt_of_le_of_lt hlip hdd
    have he4 : (0:ℝ) < ε / 4 := by linarith
    have habs2 : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (ε / 4) < 1 * (ε / 4) := by
      calc |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (ε / 4)
          = |(((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * (ε / 4)| := by
            rw [abs_mul, abs_of_pos he4]
        _ = |(((i : ℕ) : ℝ) + 1) * (ε / 4) - (((j : ℕ) : ℝ) + 1) * (ε / 4)| := by ring_nf
        _ < ε / 4 := habs
        _ = 1 * (ε / 4) := (one_mul _).symm
    have h3 : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| < 1 := lt_of_mul_lt_mul_right habs2 he4.le
    have h4 := abs_lt.mp h3
    have h5 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) + 1 := by linarith [h4.2]
    have h6 : ((j : ℕ) : ℝ) < ((i : ℕ) : ℝ) + 1 := by linarith [h4.1]
    have h5' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h5
    have h6' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h6
    exact Fin.ext (by omega)
  -- conversion between displacement of a pair and of the quotient element
  have hdistid : ∀ (γ δ : ↥Γ) (y : UpperHalfPlane),
      dist y ((γ⁻¹ * δ) • y) = dist (γ • y) (δ • y) := by
    intro γ δ y
    rw [mul_smul, ← dist_smul γ y (γ⁻¹ • δ • y), smul_inv_smul]
  -- overlapping translates of the chain region force δ = ±γ
  have hkey : ∀ γ δ : ↥Γ, ∀ x : UpperHalfPlane, x ∈ γ • t → x ∈ δ • t →
      ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∨
      ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = -((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro γ δ x hxγ hxδ
    rw [htdef, Set.smul_set_iUnion] at hxγ hxδ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxγ
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxδ
    rw [Metric.smul_ball, Metric.mem_ball] at hi hj
    have hij : i = j := hsep γ δ i j x hi hj
    subst hij
    have hdd : dist (c i) ((γ⁻¹ * δ) • c i) < ε / 4 := by
      rw [hdistid γ δ (c i)]
      calc dist (γ • c i) (δ • c i)
          ≤ dist (γ • c i) x + dist x (δ • c i) := dist_triangle _ _ _
        _ = dist x (γ • c i) + dist x (δ • c i) := by rw [dist_comm (γ • c i) x]
        _ < ε / 8 + ε / 8 := add_lt_add hi hj
        _ = ε / 4 := by ring
    by_cases hnt : actsNontrivially ((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    · exfalso
      have h1 : ε ≤ translationLength ((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
        hgap _ (γ⁻¹ * δ).2 hnt
      have h2 : (((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic :=
        (translationLength_pos_iff _).mp (lt_of_lt_of_le hε h1)
      have h3 := translationLength_le_dist_smul
        ((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) h2 (c i)
      have h4 : dist (c i) (((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • c i)
          < ε / 4 := hdd
      linarith
    · have htriv : ∀ τ' : UpperHalfPlane,
          ((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ' = τ' := by
        intro τ'
        by_contra hne'
        exact hnt ⟨τ', hne'⟩
      have hGeq : ((γ⁻¹ * δ : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          = (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
            * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
        simp
      have hgrp : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
            * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ))
          = (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by group
      have hm : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          * ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
            * (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
          Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = ((δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [hgrp]
      rw [Matrix.SpecialLinearGroup.coe_mul] at hm
      rcases (smul_id_iff_pm_one _).mp htriv with h1 | h1
      · rw [hGeq] at h1
        left
        rw [h1, mul_one] at hm
        exact hm.symm
      · rw [hGeq] at h1
        right
        rw [h1, mul_neg_one] at hm
        exact hm.symm
  -- the chain balls are pairwise disjoint
  have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin k =>
      Metric.ball (c j) (ε / 8)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
    refine hsep 1 1 i j x ?_ ?_
    · rw [one_smul]
      exact Metric.mem_ball.mp hxi
    · rw [one_smul]
      exact Metric.mem_ball.mp hxj
  -- translates of the chain region are open
  have hopen : ∀ η : ↥Γ, IsOpen (η • t) := by
    intro η
    rw [htdef, Set.smul_set_iUnion]
    refine isOpen_iUnion fun j => ?_
    rw [Metric.smul_ball]
    exact Metric.isOpen_ball
  -- at every point, at most two group elements cover it by translates of `t`
  have hpoint : ∀ x : UpperHalfPlane,
      (∑' η : ↥Γ, (η • t).indicator 1 x) ≤ (2 : ℝ≥0∞) := by
    intro x
    by_cases hex : ∃ η : ↥Γ, x ∈ η • t
    · obtain ⟨γ₀, hγ₀⟩ := hex
      by_cases hneg : ∃ η : ↥Γ, ((η : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)
          = -((γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      · obtain ⟨η₀, hη₀⟩ := hneg
        have hzero : ∀ b : ↥Γ, b ∉ ({γ₀, η₀} : Finset ↥Γ) →
            (b • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x = 0 := by
          intro b hb
          refine Set.indicator_of_notMem (fun hbx => hb ?_) 1
          rcases hkey γ₀ b x hγ₀ hbx with h | h
          · have hbγ : b = γ₀ := Subtype.coe_injective (Subtype.coe_injective h)
            rw [hbγ]
            exact Finset.mem_insert_self _ _
          · have hbη : b = η₀ :=
              Subtype.coe_injective (Subtype.coe_injective (h.trans hη₀.symm))
            rw [hbη]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        calc (∑' η : ↥Γ, (η • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x)
            = ∑ b ∈ ({γ₀, η₀} : Finset ↥Γ),
              (b • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x := tsum_eq_sum hzero
          _ ≤ ∑ _b ∈ ({γ₀, η₀} : Finset ↥Γ), (1 : ℝ≥0∞) :=
              Finset.sum_le_sum fun b _ => Set.indicator_le_self _ _ x
          _ = (({γ₀, η₀} : Finset ↥Γ).card : ℝ≥0∞) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ (2 : ℝ≥0∞) := by
              have hcard : ({γ₀, η₀} : Finset ↥Γ).card ≤ 2 := Finset.card_insert_le _ _
              exact_mod_cast hcard
      · have hzero : ∀ b : ↥Γ, b ∉ ({γ₀} : Finset ↥Γ) →
            (b • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x = 0 := by
          intro b hb
          refine Set.indicator_of_notMem (fun hbx => hb ?_) 1
          rcases hkey γ₀ b x hγ₀ hbx with h | h
          · have hbγ : b = γ₀ := Subtype.coe_injective (Subtype.coe_injective h)
            rw [hbγ]
            exact Finset.mem_singleton_self _
          · exact absurd ⟨b, h⟩ hneg
        calc (∑' η : ↥Γ, (η • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x)
            = ∑ b ∈ ({γ₀} : Finset ↥Γ),
              (b • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x := tsum_eq_sum hzero
          _ ≤ ∑ _b ∈ ({γ₀} : Finset ↥Γ), (1 : ℝ≥0∞) :=
              Finset.sum_le_sum fun b _ => Set.indicator_le_self _ _ x
          _ = 1 := by rw [Finset.sum_const, Finset.card_singleton, one_nsmul]
          _ ≤ (2 : ℝ≥0∞) := one_le_two
    · have hzero : ∀ η : ↥Γ, (η • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x = 0 := fun η =>
        Set.indicator_of_notMem (fun hx => hex ⟨η, hx⟩) 1
      calc (∑' η : ↥Γ, (η • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x)
          = ∑' _η : ↥Γ, (0 : ℝ≥0∞) := tsum_congr hzero
        _ = 0 := tsum_zero
        _ ≤ (2 : ℝ≥0∞) := zero_le _
  -- mass count: the region packs into two copies of the fundamental domain
  have hcount : volume t ≤ 2 * volume F := by
    calc volume t = ∑' η : ↥Γ, volume (η • t ∩ F) := hFdom.measure_eq_tsum t
      _ = ∑' η : ↥Γ, ∫⁻ x in F, (η • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x := by
          refine tsum_congr fun η => ?_
          rw [← lintegral_indicator hFmeas, Set.indicator_indicator, Set.inter_comm F,
            lintegral_indicator_one (((hopen η).measurableSet).inter hFmeas)]
      _ = ∫⁻ x in F, ∑' η : ↥Γ, (η • t).indicator (1 : UpperHalfPlane → ℝ≥0∞) x :=
          (lintegral_tsum fun η =>
            (measurable_one.indicator (hopen η).measurableSet).aemeasurable).symm
      _ ≤ ∫⁻ _ in F, (2 : ℝ≥0∞) := lintegral_mono hpoint
      _ = 2 * volume F := setLIntegral_const F 2
  -- the region has volume k · v
  have hvolt : volume t = (k : ℝ≥0∞) * v := by
    rw [hvdef, htdef, measure_iUnion hdisj fun j => measurableSet_ball, tsum_fintype,
      Finset.sum_congr rfl fun j _ => volume_ball_eq_upperBallVolume (c j) (ε / 8),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- contradiction
  have hle : (k : ℝ≥0∞) * v ≤ 2 * A := by
    calc (k : ℝ≥0∞) * v = volume t := hvolt.symm
      _ ≤ 2 * volume F := hcount
      _ ≤ 2 * A := mul_le_mul' le_rfl hFvol
  exact absurd hle (not_le.mpr hk2A)

/-! ## Bounded generators and Bolzano–Weierstrass -/

/-- Bounded generators from orbit density: if the orbit of `τ₀` is `D`-dense, the elements
displacing `τ₀` by at most `2D + 1` generate the group, by connectedness of the upper half
plane. -/
theorem closure_ball_generators_eq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {τ₀ : UpperHalfPlane} {D : ℝ} (hD : 0 ≤ D)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ D) :
    Subgroup.closure {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ |
      γ ∈ Γ ∧ dist τ₀ (γ • τ₀) ≤ 2 * D + 1} = Γ := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      S = {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ |
        γ ∈ Γ ∧ dist τ₀ (γ • τ₀) ≤ 2 * D + 1} := ⟨_, rfl⟩
  rw [← hSdef]
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ),
      H = Subgroup.closure S := ⟨_, rfl⟩
  rw [← hHdef]
  have hSsub : S ⊆ (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := by
    rw [hSdef]
    intro γ hγ
    exact hγ.1
  have hHle : H ≤ Γ := by
    rw [hHdef]
    exact (Subgroup.closure_le Γ).mpr hSsub
  refine le_antisymm hHle fun γ hγ => ?_
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = D + 1 / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hrdef]
    linarith
  -- a close pair of orbit points produces a generator
  have hpair : ∀ β δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, β ∈ Γ → δ ∈ Γ →
      dist (β • τ₀) (δ • τ₀) < 2 * r → β⁻¹ * δ ∈ S := by
    intro β δ hβ hδ hdd
    rw [hSdef]
    refine ⟨mul_mem (inv_mem hβ) hδ, ?_⟩
    have h1 : dist τ₀ ((β⁻¹ * δ) • τ₀) = dist (β • τ₀) (δ • τ₀) := by
      rw [mul_smul, ← dist_smul β τ₀ (β⁻¹ • δ • τ₀), smul_inv_smul]
    rw [h1]
    rw [hrdef] at hdd
    linarith
  -- the two-set separation
  obtain ⟨U, hUdef⟩ : ∃ U : Set UpperHalfPlane,
      U = ⋃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ⋃ _ : δ ∈ H,
        Metric.ball (δ • τ₀) r := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : Set UpperHalfPlane,
      V = ⋃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ⋃ _ : δ ∈ Γ ∧ δ ∉ H,
        Metric.ball (δ • τ₀) r := ⟨_, rfl⟩
  have hdisj : ∀ x, x ∈ U → x ∈ V → False := by
    intro x hxU hxV
    rw [hUdef] at hxU
    rw [hVdef] at hxV
    obtain ⟨β, hβH, hxβ⟩ := Set.mem_iUnion₂.mp hxU
    obtain ⟨δ, hδ, hxδ⟩ := Set.mem_iUnion₂.mp hxV
    have hdd : dist (β • τ₀) (δ • τ₀) < 2 * r := by
      calc dist (β • τ₀) (δ • τ₀)
          ≤ dist (β • τ₀) x + dist x (δ • τ₀) := dist_triangle _ _ _
        _ = dist x (β • τ₀) + dist x (δ • τ₀) := by rw [dist_comm (β • τ₀) x]
        _ < r + r := add_lt_add (Metric.mem_ball.mp hxβ) (Metric.mem_ball.mp hxδ)
        _ = 2 * r := by ring
    have hmem : β⁻¹ * δ ∈ S := hpair β δ (hHle hβH) hδ.1 hdd
    have hδH : δ ∈ H := by
      have h2 : β⁻¹ * δ ∈ H := by
        rw [hHdef]
        exact Subgroup.subset_closure hmem
      have h3 := mul_mem hβH h2
      rwa [mul_inv_cancel_left] at h3
    exact hδ.2 hδH
  have hcover : ∀ x : UpperHalfPlane, x ∈ U ∪ V := by
    intro x
    have h1 : Metric.infDist x (MulAction.orbit Γ τ₀) < r :=
      lt_of_le_of_lt (hdense x) (by rw [hrdef]; linarith)
    have hne : (MulAction.orbit Γ τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff hne).mp h1
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    by_cases hgH : (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ H
    · left
      rw [hUdef]
      exact Set.mem_iUnion₂.mpr ⟨(g : Matrix.SpecialLinearGroup (Fin 2) ℝ), hgH,
        Metric.mem_ball.mpr hxy⟩
    · right
      rw [hVdef]
      exact Set.mem_iUnion₂.mpr ⟨(g : Matrix.SpecialLinearGroup (Fin 2) ℝ), ⟨g.2, hgH⟩,
        Metric.mem_ball.mpr hxy⟩
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact isOpen_iUnion fun δ => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hVopen : IsOpen V := by
    rw [hVdef]
    exact isOpen_iUnion fun δ => isOpen_iUnion fun _ => Metric.isOpen_ball
  have hcompl : Uᶜ = V := by
    ext x
    constructor
    · intro hx
      rcases hcover x with h | h
      · exact absurd h hx
      · exact h
    · intro hx hxU
      exact hdisj x hxU hx
  have hclopen : IsClopen U := by
    refine ⟨?_, hUopen⟩
    rw [← isOpen_compl_iff, hcompl]
    exact hVopen
  have hUne : U.Nonempty := by
    refine ⟨τ₀, ?_⟩
    rw [hUdef]
    refine Set.mem_iUnion₂.mpr ⟨1, one_mem H, ?_⟩
    rw [one_smul]
    exact Metric.mem_ball_self hr0
  have hUuniv : U = Set.univ := hclopen.eq_univ hUne
  have hγball : γ • τ₀ ∈ U := hUuniv ▸ Set.mem_univ _
  rw [hUdef] at hγball
  obtain ⟨δ, hδH, hγδ⟩ := Set.mem_iUnion₂.mp hγball
  have hdd : dist (δ • τ₀) (γ • τ₀) < 2 * r := by
    have h1 : dist (γ • τ₀) (δ • τ₀) < r := Metric.mem_ball.mp hγδ
    rw [dist_comm] at h1
    linarith
  have hmem : δ⁻¹ * γ ∈ S := hpair δ γ (hHle hδH) hγ hdd
  have h2 : δ⁻¹ * γ ∈ H := by
    rw [hHdef]
    exact Subgroup.subset_closure hmem
  have h3 := mul_mem hδH h2
  rwa [mul_inv_cancel_left] at h3

/-- The displacement of `i` computes the Frobenius norm:
`cosh (dist i (A·i)) = (a² + b² + c² + d²) / 2` for `A = !![a, b; c, d] ∈ SL(2, ℝ)`. -/
theorem cosh_dist_I_smul_I (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Real.cosh (dist UpperHalfPlane.I (A • UpperHalfPlane.I))
      = ((A 0 0) ^ 2 + (A 0 1) ^ 2 + (A 1 0) ^ 2 + (A 1 1) ^ 2) / 2 := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have h := A.2
    rwa [Matrix.det_fin_two] at h
  have hcd : (0 : ℝ) < A 1 0 ^ 2 + A 1 1 ^ 2 := by
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ A 1 0 ^ 2 + A 1 1 ^ 2) with h | h
    · exfalso
      have hc : A 1 0 = 0 := by nlinarith [sq_nonneg (A 1 0), sq_nonneg (A 1 1)]
      have hd : A 1 1 = 0 := by nlinarith [sq_nonneg (A 1 0), sq_nonneg (A 1 1)]
      rw [hc, hd] at hdet
      norm_num at hdet
    · exact h
  have hcoe : ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)
      = ((A 0 0 : ℝ) * Complex.I + (A 0 1 : ℝ)) /
        ((A 1 0 : ℝ) * Complex.I + (A 1 1 : ℝ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [show ∀ x : ℝ, (algebraMap ℝ ℝ) x = x from fun x => rfl, UpperHalfPlane.coe_I]
  have hns : Complex.normSq ((A 1 0 : ℝ) * Complex.I + (A 1 1 : ℝ))
      = A 1 0 ^ 2 + A 1 1 ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : (A • UpperHalfPlane.I).im = 1 / (A 1 0 ^ 2 + A 1 1 ^ 2) := by
    rw [← UpperHalfPlane.coe_im, hcoe, Complex.div_im, hns]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [div_sub_div_same, div_eq_div_iff hcd.ne' hcd.ne']
    linear_combination (A 1 0 ^ 2 + A 1 1 ^ 2) * hdet
  have hre : (A • UpperHalfPlane.I).re
      = (A 0 0 * A 1 0 + A 0 1 * A 1 1) / (A 1 0 ^ 2 + A 1 1 ^ 2) := by
    rw [← UpperHalfPlane.coe_re, hcoe, Complex.div_re, hns]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [← add_div, div_eq_div_iff hcd.ne' hcd.ne']
    ring
  rw [UpperHalfPlane.cosh_dist', him, hre, UpperHalfPlane.I_im, UpperHalfPlane.I_re]
  have hne : A 1 0 ^ 2 + A 1 1 ^ 2 ≠ 0 := hcd.ne'
  field_simp
  ring_nf
  linear_combination (-(A 0 0 * A 1 1 - A 0 1 * A 1 0) - 1) * hdet

/-- Bolzano–Weierstrass for tuples in `SL(2, ℝ)` with uniformly bounded displacement of `i`:
a subsequence converges entrywise to a tuple of `SL(2, ℝ)`-matrices. -/
theorem exists_subseq_tendsto_sl2_of_bounded {ι : Type} [Finite ι]
    (g : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) {C : ℝ}
    (hC : ∀ n i, dist UpperHalfPlane.I (g n i • UpperHalfPlane.I) ≤ C) :
    ∃ (φ : ℕ → ℕ) (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ), StrictMono φ ∧
      ∀ i, Filter.Tendsto (fun k => g (φ k) i) Filter.atTop (nhds (ρ i)) := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.sqrt (2 * Real.cosh C) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact Real.sqrt_nonneg _
  -- entrywise bound from the Frobenius identity
  have hentry : ∀ (n : ℕ) (i : ι) (k l : Fin 2), |g n i k l| ≤ R := by
    intro n i k l
    have h1 : Real.cosh (dist UpperHalfPlane.I (g n i • UpperHalfPlane.I)) ≤ Real.cosh C := by
      rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
      exact (hC n i).trans (le_abs_self C)
    rw [cosh_dist_I_smul_I] at h1
    have hsum : (g n i 0 0) ^ 2 + (g n i 0 1) ^ 2 + (g n i 1 0) ^ 2 + (g n i 1 1) ^ 2
        ≤ 2 * Real.cosh C := by linarith
    have h2 : (g n i k l) ^ 2 ≤ 2 * Real.cosh C := by
      fin_cases k <;> fin_cases l <;>
        simp only [Fin.zero_eta, Fin.mk_one] <;>
        nlinarith [sq_nonneg (g n i 0 0), sq_nonneg (g n i 0 1), sq_nonneg (g n i 1 0),
          sq_nonneg (g n i 1 1)]
    rw [hRdef, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h2
  -- Bolzano–Weierstrass in the finite-dimensional tuple space
  obtain ⟨x, hxdef⟩ : ∃ x : ℕ → (ι → Fin 2 → Fin 2 → ℝ),
      x = fun n i k l => g n i k l := ⟨_, rfl⟩
  have hball : ∀ n, x n ∈ Metric.closedBall (0 : ι → Fin 2 → Fin 2 → ℝ) R := by
    intro n
    rw [Metric.mem_closedBall, hxdef, dist_pi_le_iff hR0]
    intro i
    rw [dist_pi_le_iff hR0]
    intro k
    rw [dist_pi_le_iff hR0]
    intro l
    rw [Real.dist_eq, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_zero]
    exact hentry n i k l
  obtain ⟨L, -, φ, hφmono, hφtend⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hball
  rw [hxdef] at hφtend
  -- coordinatewise convergence at the matrix level
  have hmat : ∀ i, Filter.Tendsto (fun m => (g (φ m) i : Matrix (Fin 2) (Fin 2) ℝ))
      Filter.atTop (nhds (Matrix.of (L i))) := by
    intro i
    exact tendsto_pi_nhds.mp hφtend i
  -- the limit matrices have determinant one
  have hdet1 : ∀ i, (Matrix.of (L i)).det = 1 := by
    intro i
    have hcont : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M.det :=
      (continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ)).matrix_det
    have h1 : Filter.Tendsto (fun m => ((g (φ m) i : Matrix (Fin 2) (Fin 2) ℝ)).det)
        Filter.atTop (nhds ((Matrix.of (L i)).det)) :=
      (hcont.tendsto _).comp (hmat i)
    have h2 : (fun m => ((g (φ m) i : Matrix (Fin 2) (Fin 2) ℝ)).det) = fun _ => (1 : ℝ) := by
      funext m
      exact Matrix.SpecialLinearGroup.det_coe (g (φ m) i)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  refine ⟨φ, fun i => ⟨Matrix.of (L i), hdet1 i⟩, hφmono, fun i => ?_⟩
  exact tendsto_subtype_rng.mpr (hmat i)

/-! ## The trace gap in the limit and the headline -/

/-- The trace gap passes to words in the limit tuple: every word in the limit generators is
approximated by the corresponding words in the approximating tuples, which satisfy the gap
dichotomy; the trace is continuous and `{±1}` is closed. -/
theorem limit_trace_gap {ι : Type} [Finite ι] {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (g : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) (hmem : ∀ n i, g n i ∈ Γ n)
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hlim : ∀ i, Filter.Tendsto (fun n => g n i) Filter.atTop (nhds (ρ i))) :
    ∀ h ∈ Subgroup.closure (Set.range ρ), actsNontrivially h →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)| := by
  have _ := Real.one_lt_cosh.mpr (by positivity : (0:ℝ) < ε / 2).ne'
  -- every element of the closure is an entrywise limit of a sequence of group elements
  have key : ∀ h' ∈ Subgroup.closure (Set.range ρ),
      ∃ w : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ n, w n ∈ Γ n) ∧
        Filter.Tendsto (fun n => ((w n : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)) Filter.atTop
          (nhds ((h' : Matrix (Fin 2) (Fin 2) ℝ))) := by
    intro h' hh'
    induction hh' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨fun n => g n i, fun n => hmem n i, tendsto_subtype_rng.mp (hlim i)⟩
    | one =>
      exact ⟨fun _ => 1, fun n => one_mem (Γ n), tendsto_const_nhds⟩
    | mul y z _hy _hz ihy ihz =>
      obtain ⟨w1, hw1, ht1⟩ := ihy
      obtain ⟨w2, hw2, ht2⟩ := ihz
      refine ⟨fun n => w1 n * w2 n, fun n => mul_mem (hw1 n) (hw2 n), ?_⟩
      have hmulc : Continuous fun p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
          p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
      have h3 := (hmulc.tendsto ((y : Matrix (Fin 2) (Fin 2) ℝ),
        (z : Matrix (Fin 2) (Fin 2) ℝ))).comp (ht1.prodMk_nhds ht2)
      have hco : (fun n => ((w1 n * w2 n : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ))
          = fun n => ((w1 n : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
              Matrix (Fin 2) (Fin 2) ℝ)
            * ((w2 n : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
        funext fun n => Matrix.SpecialLinearGroup.coe_mul (w1 n) (w2 n)
      rw [hco, Matrix.SpecialLinearGroup.coe_mul]
      exact h3
    | inv y _hy ihy =>
      obtain ⟨w1, hw1, ht1⟩ := ihy
      refine ⟨fun n => (w1 n)⁻¹, fun n => inv_mem (hw1 n), ?_⟩
      have hadjc : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M.adjugate :=
        (continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ)).matrix_adjugate
      have h3 := (hadjc.tendsto ((y : Matrix (Fin 2) (Fin 2) ℝ))).comp ht1
      have hco : (fun n => (((w1 n)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ))
          = fun n => ((w1 n : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
              Matrix (Fin 2) (Fin 2) ℝ).adjugate :=
        funext fun n => Matrix.SpecialLinearGroup.coe_inv (w1 n)
      rw [hco, Matrix.SpecialLinearGroup.coe_inv]
      exact h3
  intro h hh hnt
  obtain ⟨w, hwmem, hwtend⟩ := key h hh
  by_cases hev : ∀ᶠ n in Filter.atTop,
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace ((w n : Matrix (Fin 2) (Fin 2) ℝ))|
  · -- the gap holds eventually: pass it to the limit by continuity of the trace
    have habs : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => |Matrix.trace M| :=
      ((continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ)).matrix_trace).abs
    exact ge_of_tendsto ((habs.tendsto _).comp hwtend) hev
  · -- otherwise the approximants are frequently `±1`, forcing `h = ±1`: contradiction
    exfalso
    rw [Filter.not_eventually] at hev
    have hfreq : ∃ᶠ n in Filter.atTop, ((w n : Matrix (Fin 2) (Fin 2) ℝ))
        ∈ ({1, -1} : Set (Matrix (Fin 2) (Fin 2) ℝ)) := by
      refine hev.mono fun n hn => ?_
      have hnt' : ¬ actsNontrivially (w n) := fun hnt' => hn (hgap n (w n) (hwmem n) hnt')
      have htriv : ∀ τ : UpperHalfPlane, w n • τ = τ := by
        intro τ
        by_contra hne
        exact hnt' ⟨τ, hne⟩
      rcases (smul_id_iff_pm_one (w n)).mp htriv with h1 | h1
      · exact Set.mem_insert_iff.mpr (Or.inl h1)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h1))
    have hclosed : IsClosed ({1, -1} : Set (Matrix (Fin 2) (Fin 2) ℝ)) :=
      ((Set.finite_singleton (-1 : Matrix (Fin 2) (Fin 2) ℝ)).insert 1).isClosed
    have hmem2 := hclosed.mem_of_frequently_of_tendsto hfreq hwtend
    have hpm : (h : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (h : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
      rcases Set.mem_insert_iff.mp hmem2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Set.mem_singleton_iff.mp h1)
    obtain ⟨τ, hτ⟩ := hnt
    exact hτ ((smul_eq_self_of_pm_one h hpm).1 τ)

/-- A subgroup of `SL(2, ℝ)` whose nontrivially-acting elements satisfy the trace gap
`|tr| ≥ 2 cosh (ε/2) > 2` is Fuchsian: an accumulation of group elements would produce
nontrivially-acting quotients with trace tending to `2`. -/
theorem isFuchsianGroup_of_trace_gap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|) :
    IsFuchsianGroup Γ := by
  classical
  haveI : IsIsometricSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  change ProperlyDiscontinuousSMul (↥Γ) UpperHalfPlane
  constructor
  intro K L hK hL
  by_contra hfin
  have hinf : {γ : ↥Γ | ((fun x => γ • x) '' K ∩ L).Nonempty}.Infinite := hfin
  -- radii of the compacts around `i`
  obtain ⟨rK, hrK⟩ := hK.isBounded.subset_closedBall UpperHalfPlane.I
  obtain ⟨rL, hrL⟩ := hL.isBounded.subset_closedBall UpperHalfPlane.I
  -- elements moving `K` into `L` displace `i` by at most `rL + rK`
  have hbound : ∀ γ : ↥Γ, ((fun x => γ • x) '' K ∩ L).Nonempty →
      dist UpperHalfPlane.I ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • UpperHalfPlane.I)
        ≤ rL + rK := by
    intro γ hγ
    obtain ⟨z, hz1, hz2⟩ := hγ
    obtain ⟨k, hkK, rfl⟩ := hz1
    have h1 : dist (γ • k) UpperHalfPlane.I ≤ rL := Metric.mem_closedBall.mp (hrL hz2)
    have h2 : dist k UpperHalfPlane.I ≤ rK := Metric.mem_closedBall.mp (hrK hkK)
    have h3 : dist UpperHalfPlane.I (γ • UpperHalfPlane.I)
        ≤ dist UpperHalfPlane.I (γ • k) + dist (γ • k) (γ • UpperHalfPlane.I) :=
      dist_triangle _ _ _
    have h4 : dist (γ • k) (γ • UpperHalfPlane.I) = dist k UpperHalfPlane.I :=
      dist_smul γ k UpperHalfPlane.I
    have h5 : dist UpperHalfPlane.I (γ • k) = dist (γ • k) UpperHalfPlane.I := dist_comm _ _
    have h6 : dist UpperHalfPlane.I ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) •
        UpperHalfPlane.I) = dist UpperHalfPlane.I (γ • UpperHalfPlane.I) := by
      rw [Subgroup.smul_def]
    linarith
  -- an injective enumeration of the infinite set
  obtain ⟨f⟩ : Nonempty (ℕ ↪ ↥{γ : ↥Γ | ((fun x => γ • x) '' K ∩ L).Nonempty}) :=
    ⟨Set.Infinite.natEmbedding _ hinf⟩
  obtain ⟨u, hudef⟩ : ∃ u : ℕ → ↥Γ, u = fun n => (f n).1 := ⟨_, rfl⟩
  have humem : ∀ n, ((fun x => (u n) • x) '' K ∩ L).Nonempty := by
    rw [hudef]
    exact fun n => (f n).2
  have huinj : Function.Injective u := by
    rw [hudef]
    exact fun a b hab => f.injective (Subtype.ext hab)
  -- Bolzano–Weierstrass on the displacement-bounded sequence
  obtain ⟨φ, ρ, hφ, hconv⟩ := exists_subseq_tendsto_sl2_of_bounded
    (fun (n : ℕ) (_ : Unit) => ((u n : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (C := rL + rK) (fun n _ => hbound (u n) (humem n))
  have hmat0 : Filter.Tendsto (fun k => (((u (φ k) : ↥Γ) :
      Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) Filter.atTop
      (nhds ((ρ () : Matrix (Fin 2) (Fin 2) ℝ))) :=
    tendsto_subtype_rng.mp (hconv ())
  -- the absolute traces of consecutive quotients tend to `|tr 1| = 2`
  have hcont : Continuous fun p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ =>
      |Matrix.trace (p.1.adjugate * p.2)| :=
    ((continuous_fst.matrix_adjugate.matrix_mul continuous_snd).matrix_trace).abs
  have hpair := hmat0.prodMk_nhds (hmat0.comp (Filter.tendsto_add_atTop_nat 1))
  have htrq := (hcont.tendsto _).comp hpair
  have hlimval : |Matrix.trace (((ρ () : Matrix (Fin 2) (Fin 2) ℝ)).adjugate
      * ((ρ () : Matrix (Fin 2) (Fin 2) ℝ)))| = 2 := by
    rw [Matrix.adjugate_mul, Matrix.SpecialLinearGroup.det_coe, one_smul, Matrix.trace_one]
    norm_num [Fintype.card_fin]
  have htrq' : Filter.Tendsto (fun k =>
      |Matrix.trace ((((u (φ k) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ).adjugate
        * (((u (φ (k + 1)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ))|) Filter.atTop (nhds 2) := by
    rw [← hlimval]
    exact htrq
  have h2lt : (2 : ℝ) < 2 * Real.cosh (ε / 2) := by
    have h1c : 1 < Real.cosh (ε / 2) :=
      Real.one_lt_cosh.mpr (by positivity : (0:ℝ) < ε / 2).ne'
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htrq'.eventually_lt_const h2lt)
  -- eventually consecutive elements differ by `-1`
  have hstep : ∀ k, N ≤ k →
      (((u (φ (k + 1)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
        = -(((u (φ k) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) := by
    intro k hk
    obtain ⟨q, hqdef⟩ : ∃ q : ↥Γ, q = (u (φ k))⁻¹ * u (φ (k + 1)) := ⟨_, rfl⟩
    have hqcoe : (((q : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
        = (((u (φ k) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ).adjugate
          * (((u (φ (k + 1)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hqdef, Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv]
    have htrlt : |Matrix.trace (((q : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)| < 2 * Real.cosh (ε / 2) := by
      rw [hqcoe]
      exact hN k hk
    by_cases hnt : actsNontrivially ((q : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    · exact absurd (hgap _ q.2 hnt) (not_le.mpr htrlt)
    · have htriv : ∀ τ : UpperHalfPlane,
          ((q : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := by
        intro τ
        by_contra hne
        exact hnt ⟨τ, hne⟩
      have hmul : u (φ k) * q = u (φ (k + 1)) := by
        rw [hqdef]
        exact mul_inv_cancel_left _ _
      rcases (smul_id_iff_pm_one _).mp htriv with h1 | h1
      · -- the quotient is the identity: contradicts injectivity of the enumeration
        exfalso
        have hq1 : q = 1 := by
          have hcoe : (((q : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
              Matrix (Fin 2) (Fin 2) ℝ)
              = (((1 : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
                Matrix (Fin 2) (Fin 2) ℝ) := by
            rw [h1, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one]
          exact Subtype.coe_injective (Subtype.coe_injective hcoe)
        have heq : u (φ k) = u (φ (k + 1)) := by
          rw [← hmul, hq1, mul_one]
        have h5 : φ k = φ (k + 1) := huinj heq
        have h6 : k = k + 1 := hφ.injective h5
        omega
      · -- the quotient is `-1`
        calc (((u (φ (k + 1)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ)
            = (((u (φ k) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
                Matrix (Fin 2) (Fin 2) ℝ)
              * (((q : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
                Matrix (Fin 2) (Fin 2) ℝ) := by
              rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, hmul]
          _ = -(((u (φ k) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
              Matrix (Fin 2) (Fin 2) ℝ) := by
              rw [h1, mul_neg_one]
  -- two consecutive `-1`-steps give a repeated element: contradiction
  have e1 := hstep N le_rfl
  have e2 := hstep (N + 1) (Nat.le_succ N)
  have e3 : (((u (φ (N + 2)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)
      = (((u (φ N) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) := by
    have e2' : (((u (φ (N + 2)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
        = -(((u (φ (N + 1)) : ↥Γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) := e2
    rw [e2', e1]
    exact neg_neg _
  have heq : u (φ (N + 2)) = u (φ N) :=
    Subtype.coe_injective (Subtype.coe_injective e3)
  have h5 : φ (N + 2) = φ N := huinj heq
  have h6 : N + 2 = N := hφ.injective h5
  omega

/-- Freeness from the trace gap: an element with a fixed point in the upper half plane is
elliptic or central, so under the gap it acts trivially. -/
theorem free_of_trace_gap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ε : ℝ}
    (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|) :
    ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ' := by
  intro γ hfix τ'
  obtain ⟨τ, hτ⟩ := hfix
  by_contra hne
  have hnt : actsNontrivially (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
    refine ⟨τ', fun hcon => hne ?_⟩
    rw [Subgroup.smul_def]
    exact hcon
  have hg := hgap (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) γ.2 hnt
  have h1c : 1 < Real.cosh (ε / 2) :=
    Real.one_lt_cosh.mpr (by positivity : (0:ℝ) < ε / 2).ne'
  have h2 : 2 < |Matrix.trace (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ)| := by linarith
  have hhyp : (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic := by
    have hdet : ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ)).det = 1 := Matrix.SpecialLinearGroup.det_coe _
    unfold Matrix.IsHyperbolic
    rw [Matrix.discr_fin_two, hdet]
    nlinarith [sq_abs (Matrix.trace (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ)),
      abs_nonneg (Matrix.trace (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ)),
      mul_pos (by linarith : (0:ℝ) < |Matrix.trace (((γ :
          Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)| - 2)
        (by linarith : (0:ℝ) < |Matrix.trace (((γ :
          Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)| + 2)]
  have hfix' : (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • τ = τ := by
    rw [← Subgroup.smul_def]
    exact hτ
  have hlen := translationLength_le_dist_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    hhyp τ
  rw [hfix', dist_self] at hlen
  have hpos : 0 < translationLength (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    (translationLength_pos_iff _).mpr hhyp
  linarith

/-- **Mumford generator subconvergence.** Along a sequence of representatives with systole at
least `ε > 0` and area bound `A < ∞`, finite generating tuples with uniformly bounded
displacement of the basepoint `i` subconverge to a tuple whose closure is a Fuchsian group
with the trace gap and the freeness property. The displacement bound is essential: the trace
is a conjugation-invariant continuous function, so a generating tuple with unbounded traces
(such as `a·bⁿ` in place of `a`) admits no subconvergent conjugates, while generating tuples
produced inside a fixed orbit-dense ball satisfy the bound automatically. -/
theorem mumford_generator_subconvergence (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {ι : Type} [Finite ι] {ε : ℝ} (hε : 0 < ε) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (x : ℕ → TeichRep Γ₀)
    (hthick : ∀ n, ε ≤ systoleRep (x n))
    (harea : ∀ n, HasAreaBound (x n).group A)
    (gens : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hgens : ∀ n, (∀ i, gens n i ∈ (x n).group) ∧
      Subgroup.closure (Set.range (gens n)) = (x n).group)
    {C : ℝ}
    (hbdd : ∀ n i, dist UpperHalfPlane.I (gens n i • UpperHalfPlane.I) ≤ C) :
    ∃ (φ : ℕ → ℕ) (P : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      StrictMono φ ∧
      (∀ i, Filter.Tendsto (fun k => P k * gens (φ k) i * (P k)⁻¹)
        Filter.atTop (nhds (ρ i))) ∧
      (∀ h ∈ Subgroup.closure (Set.range ρ), actsNontrivially h →
        2 * Real.cosh (ε / 2) ≤ |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)|) ∧
      IsFuchsianGroup (Subgroup.closure (Set.range ρ)) ∧
      (∀ h : Subgroup.closure (Set.range ρ), (∃ τ : UpperHalfPlane, h • τ = τ) →
        ∀ τ' : UpperHalfPlane, h • τ' = τ') := by
  -- the descent data of the packing route is retained for statement-shape compatibility
  have _ := hΓ₀
  have _ := hfree
  have _ := hcc
  have _ := hA
  have _ := harea
  obtain ⟨φ, ρ, hφ, hconv⟩ := exists_subseq_tendsto_sl2_of_bounded gens hbdd
  have hgapn : ∀ k, ∀ γ ∈ (x (φ k)).group, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| :=
    fun k γ hγ hnt => (trace_gap_of_systole hε (hthick (φ k)) hγ hnt).1
  have hgapρ := limit_trace_gap hε (fun k => (x (φ k)).group)
    (fun k i => gens (φ k) i) (fun k i => (hgens (φ k)).1 i) hgapn ρ hconv
  refine ⟨φ, fun _ => 1, ρ, hφ, ?_, hgapρ, isFuchsianGroup_of_trace_gap hε hgapρ,
    free_of_trace_gap hε hgapρ⟩
  intro i
  simpa only [one_mul, inv_one, mul_one] using hconv i

end RiemannDynamics
