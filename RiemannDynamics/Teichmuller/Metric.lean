import RiemannDynamics.Teichmuller.Def
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
  sorry

/-- Every element of the dilatation set is at least `1`. -/
theorem one_le_of_mem_dilatationSet {x y : TeichRep Γ₀} {K : ℝ}
    (hK : K ∈ dilatationSet x y) : 1 ≤ K := by
  sorry

/-- The dilatation set is bounded below. -/
theorem bddBelow_dilatationSet (x y : TeichRep Γ₀) : BddBelow (dilatationSet x y) := by
  sorry

/-- The infimum of the dilatation set is at least `1`. -/
theorem one_le_sInf_dilatationSet (x y : TeichRep Γ₀) :
    1 ≤ sInf (dilatationSet x y) := by
  sorry

/-- The Teichmüller pseudodistance is nonnegative. -/
theorem teichPseudoDist_nonneg (x y : TeichRep Γ₀) : 0 ≤ teichPseudoDist x y := by
  sorry

/-- Explicit upper bound for the pseudodistance through the coefficients of the two
representatives. -/
theorem teichPseudoDist_le_log_K (x y : TeichRep Γ₀) :
    teichPseudoDist x y ≤ (1 / 2) * Real.log (x.b.K * y.b.K) := by
  sorry

/-- The pseudodistance from a representative to itself vanishes: the identity is a candidate
with dilatation `1`. -/
theorem teichPseudoDist_self (x : TeichRep Γ₀) : teichPseudoDist x x = 0 := by
  sorry

/-- The dilatation sets of a pair and its transpose coincide, by inversion of candidates. -/
theorem dilatationSet_comm (x y : TeichRep Γ₀) :
    dilatationSet x y = dilatationSet y x := by
  sorry

/-- Symmetry of the Teichmüller pseudodistance. -/
theorem teichPseudoDist_comm (x y : TeichRep Γ₀) :
    teichPseudoDist x y = teichPseudoDist y x := by
  sorry

/-- Triangle inequality for the Teichmüller pseudodistance: candidates compose with
multiplying dilatations, and `log` turns the multiplicative bound into an additive one. -/
theorem teichPseudoDist_triangle (x y z : TeichRep Γ₀) :
    teichPseudoDist x z ≤ teichPseudoDist x y + teichPseudoDist y z := by
  sorry

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
  sorry

/-- Equal boundary maps give vanishing pseudodistance: the identity is a candidate with
dilatation `1`. -/
theorem teichPseudoDist_eq_zero_of_boundary_eq {x y : TeichRep Γ₀}
    (h : x.boundary = y.boundary) : teichPseudoDist x y = 0 := by
  sorry

/-- Rigidity: vanishing pseudodistance forces the two normalized solutions to agree on the
real line. Candidates with dilatation tending to `1` subconverge locally uniformly to a
`1`-quasiconformal map fixing `0` and `1`, which is the identity. -/
theorem w_eq_on_real_of_teichPseudoDist_eq_zero {x y : TeichRep Γ₀}
    (h : teichPseudoDist x y = 0) : ∀ t : ℝ, y.w t = x.w t := by
  sorry

/-- Inseparability in the Teichmüller pseudometric is equality of the boundary values of the
normalized solutions. -/
theorem inseparable_iff_boundary_eq {x y : TeichRep Γ₀} :
    Inseparable x y ↔ ∀ t : ℝ, x.w t = y.w t := by
  sorry

/-- Two representatives give the same point of Teichmüller space exactly when their
normalized solutions agree on the real line. -/
theorem Teich.mk_eq_mk_iff_boundary {x y : TeichRep Γ₀} :
    (SeparationQuotient.mk x : Teich Γ₀) = SeparationQuotient.mk y ↔
      ∀ t : ℝ, x.w t = y.w t := by
  sorry

end RiemannDynamics
