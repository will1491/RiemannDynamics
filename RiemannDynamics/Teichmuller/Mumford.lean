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
open scoped ENNReal

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
  sorry

/-- Injectivity radius from the systole: under a translation-length gap `ε`, a ball of radius
`r ≤ ε/2` meets its `γ`-translate only when `γ` acts trivially. -/
theorem smul_eq_self_of_ball_overlap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ → ε ≤ translationLength γ)
    {r : ℝ} (hr : r ≤ ε / 2) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (τ : UpperHalfPlane)
    (hne : ((γ • ·) '' Metric.ball τ r ∩ Metric.ball τ r).Nonempty) :
    ∀ τ' : UpperHalfPlane, γ • τ' = τ' := by
  sorry

/-- The orbit-density diameter of the packing argument: with area bound `A` and systole gap
`ε`, every orbit is `D`-dense for `D = (2A / v(ε/8))·(ε/4) + 2·(ε/4)`, where `v` is the
volume of hyperbolic balls. -/
noncomputable def mumfordDensityBound (A : ℝ≥0∞) (ε : ℝ) : ℝ :=
  (2 * A / upperBallVolume (ε / 8)).toReal * (ε / 4) + 2 * (ε / 4)

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
  sorry

/-! ## Bounded generators and Bolzano–Weierstrass -/

/-- Bounded generators from orbit density: if the orbit of `τ₀` is `D`-dense, the elements
displacing `τ₀` by at most `2D + 1` generate the group, by connectedness of the upper half
plane. -/
theorem closure_ball_generators_eq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {τ₀ : UpperHalfPlane} {D : ℝ} (hD : 0 ≤ D)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit Γ τ₀) ≤ D) :
    Subgroup.closure {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ |
      γ ∈ Γ ∧ dist τ₀ (γ • τ₀) ≤ 2 * D + 1} = Γ := by
  sorry

/-- The displacement of `i` computes the Frobenius norm:
`cosh (dist i (A·i)) = (a² + b² + c² + d²) / 2` for `A = !![a, b; c, d] ∈ SL(2, ℝ)`. -/
theorem cosh_dist_I_smul_I (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Real.cosh (dist UpperHalfPlane.I (A • UpperHalfPlane.I))
      = ((A 0 0) ^ 2 + (A 0 1) ^ 2 + (A 1 0) ^ 2 + (A 1 1) ^ 2) / 2 := by
  sorry

/-- Bolzano–Weierstrass for tuples in `SL(2, ℝ)` with uniformly bounded displacement of `i`:
a subsequence converges entrywise to a tuple of `SL(2, ℝ)`-matrices. -/
theorem exists_subseq_tendsto_sl2_of_bounded {ι : Type} [Finite ι]
    (g : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) {C : ℝ}
    (hC : ∀ n i, dist UpperHalfPlane.I (g n i • UpperHalfPlane.I) ≤ C) :
    ∃ (φ : ℕ → ℕ) (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ), StrictMono φ ∧
      ∀ i, Filter.Tendsto (fun k => g (φ k) i) Filter.atTop (nhds (ρ i)) := by
  sorry

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
  sorry

/-- A subgroup of `SL(2, ℝ)` whose nontrivially-acting elements satisfy the trace gap
`|tr| ≥ 2 cosh (ε/2) > 2` is Fuchsian: an accumulation of group elements would produce
nontrivially-acting quotients with trace tending to `2`. -/
theorem isFuchsianGroup_of_trace_gap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|) :
    IsFuchsianGroup Γ := by
  sorry

/-- Freeness from the trace gap: an element with a fixed point in the upper half plane is
elliptic or central, so under the gap it acts trivially. -/
theorem free_of_trace_gap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {ε : ℝ}
    (hε : 0 < ε)
    (hgap : ∀ γ ∈ Γ, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|) :
    ∀ γ : Γ, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ' := by
  sorry

/-- **Mumford generator subconvergence.** Along a sequence of representatives with systole at
least `ε > 0` and area bound `A < ∞`, finite generating tuples subconverge after conjugation
to a tuple whose closure is a Fuchsian group with the trace gap and the freeness property. -/
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
      Subgroup.closure (Set.range (gens n)) = (x n).group) :
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
  sorry

end RiemannDynamics
