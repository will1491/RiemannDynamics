/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction

/-!
# The bipolar Green's function and the non-hyperbolic embedding

The non-hyperbolic half of the planarity theorem. A surface without a Green's
function (or a compact surface) is exhausted by the complements of a shrinking
closed coordinate disk; each piece carries Green's functions at every pole,
and the difference of two of them — normalized through a shrink-independent
Harnack bound and the cross-symmetry bound — converges along the exhaustion to
a bipolar Green's function `G` with a positive logarithmic pole at `p₁` and a
negative one at `p₂`. The function `e^{−(G+iG^*)}`, globalized by monodromy on
the simply connected surface, is an injective holomorphic map to the sphere
with a zero at `p₁` and a pole at `p₂`, embedding the surface onto a domain
of `ℂ̂`.

## Main definitions

* `CoordDisk` — a closed coordinate disk, with `shrink`, `closedCarrier`, and
  the complementary piece `compl`;
* `pieceGreen` — the Green's function of a piece, as a function on the
  surface.

## Main statements

* `hasGreenFunction_coordDisk_compl` — every piece is hyperbolic;
* `exists_pieceGreen_symm_bound` — the shrink-uniform cross-symmetry bound
  (the symmetry wall of the classical dipole construction, isolated);
* `exists_bipolarGreen` — the dipole limit;
* `exists_bipolar_map`, `injective_bipolar_map` — the meromorphic dipole map;
* `not_bddAbove_greenFamily_of_compactSpace` — compact surfaces have no
  Green's function;
* `exists_diffeomorph_opens_of_forall_not_hasGreenFunction` — the
  non-hyperbolic case of the planarity theorem.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A closed coordinate disk on a surface: a center together with a radius
whose closed chart ball lies inside the chart target. -/
structure CoordDisk (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] where
  /-- The center of the disk. -/
  center : M
  /-- The chart radius of the disk. -/
  radius : ℝ
  radius_pos : 0 < radius
  closedBall_subset :
    closedBall (chartAt ℂ center center) radius ⊆ (chartAt ℂ center).target

namespace CoordDisk

variable (D : CoordDisk M)

/-- The closed disk on the surface: the inverse-chart image of the closed
chart ball. -/
def closedCarrier : Set M :=
  (chartAt ℂ D.center).symm '' closedBall (chartAt ℂ D.center D.center) D.radius

/-- Shrinking a coordinate disk by a factor `t ∈ (0, 1]`. -/
def shrink (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) : CoordDisk M where
  center := D.center
  radius := t * D.radius
  radius_pos := mul_pos ht D.radius_pos
  closedBall_subset :=
    (closedBall_subset_closedBall
      (by nlinarith [D.radius_pos])).trans D.closedBall_subset

theorem isCompact_closedCarrier : IsCompact D.closedCarrier :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt ℂ D.center).continuousOn_symm.mono D.closedBall_subset)

/-- The complementary piece of a coordinate disk, as an open set of the
surface. -/
def compl [T2Space M] : Opens M :=
  ⟨D.closedCarrierᶜ, D.isCompact_closedCarrier.isClosed.isOpen_compl⟩

end CoordDisk

variable [IsManifold 𝓘(ℂ) ω M]

/-- The Green's function of an open piece of the surface, read as a function
on the surface (zero when the pole or the argument leaves the piece). -/
noncomputable def pieceGreen [T2Space M] (P : Opens M) (p x : M) : ℝ :=
  open scoped Classical in
  if h : p ∈ P ∧ x ∈ P then greenEnvelope (⟨p, h.1⟩ : ↥P) ⟨x, h.2⟩ else 0

variable [T2Space M] [ConnectedSpace M]

/-! ## The pieces are hyperbolic -/

/-- Removing a closed coordinate disk keeps the surface connected. -/
theorem isConnected_coordDisk_compl (D : CoordDisk M) :
    IsConnected (D.compl : Set M) := by
  sorry

/-- The complement of a closed coordinate disk is noncompact: points near the
removed boundary circle escape every compact subset of the piece. -/
theorem noncompactSpace_coordDisk_compl (D : CoordDisk M) :
    NoncompactSpace ↥D.compl := by
  sorry

/-- **Every piece is hyperbolic**: the complement of a closed coordinate disk
carries a Green's function at every pole, by the harmonic-measure estimate on
the collar between the removed circle and a pole disk. -/
theorem hasGreenFunction_coordDisk_compl (D : CoordDisk M) (p : M)
    (hp : p ∈ D.compl) : HasGreenFunction (⟨p, hp⟩ : ↥D.compl) := by
  sorry

/-! ## The shrink-uniform bounds -/

/-- **The cross-symmetry bound** (the symmetry wall of the dipole
construction): the two cross values of the piece Green's functions differ by
a shrink-independent constant. -/
theorem exists_pieceGreen_symm_bound (D₀ : CoordDisk M) {p₁ p₂ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hne : p₁ ≠ p₂) :
    ∃ C, ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₂ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₁| ≤ C := by
  sorry

/-- **The shrink-uniform dipole bound**: away from two pole disks, the
difference of the two piece Green's functions is bounded independently of the
shrink parameter. -/
theorem exists_uniform_bipolar_bound (D₀ : CoordDisk M) {p₁ p₂ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hne : p₁ ≠ p₂) :
    ∃ C, ∃ V₁ ∈ 𝓝 p₁, ∃ V₂ ∈ 𝓝 p₂, ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      ∀ x ∈ ((D₀.shrink t ht ht1).compl : Set M) \ (V₁ ∪ V₂),
        |pieceGreen (D₀.shrink t ht ht1).compl p₁ x -
          pieceGreen (D₀.shrink t ht ht1).compl p₂ x| ≤ C := by
  sorry

/-! ## The bipolar Green's function and the dipole map -/

/-- **The bipolar Green's function**: a dipole limit of the piece Green's
function differences along the shrinking exhaustion — harmonic off the two
poles, with a positive logarithmic pole at `p₁` and a negative one at
`p₂`. -/
theorem exists_bipolarGreen [SecondCountableTopology M] (D₀ : CoordDisk M)
    {p₁ p₂ : M} (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hne : p₁ ≠ p₂) :
    ∃ G : M → ℝ, MHarmonicOn G ({p₁, p₂}ᶜ) ∧
      (∃ r > 0, ball (chartAt ℂ p₁ p₁) r ⊆ (chartAt ℂ p₁).target ∧
        ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₁ p₁) r) ∧
          ∀ w ∈ ball (chartAt ℂ p₁ p₁) r \ {chartAt ℂ p₁ p₁},
            h w = G ((chartAt ℂ p₁).symm w) + Real.log ‖w - chartAt ℂ p₁ p₁‖) ∧
      (∃ r > 0, ball (chartAt ℂ p₂ p₂) r ⊆ (chartAt ℂ p₂).target ∧
        ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₂ p₂) r) ∧
          ∀ w ∈ ball (chartAt ℂ p₂ p₂) r \ {chartAt ℂ p₂ p₂},
            h w = G ((chartAt ℂ p₂).symm w) -
              Real.log ‖w - chartAt ℂ p₂ p₂‖) := by
  sorry

/-- **The dipole map**: on a simply connected surface the bipolar Green's
function integrates to a holomorphic map to the sphere with a simple zero at
`p₁` and a pole at `p₂`, of modulus `e^{−G}` elsewhere. -/
theorem exists_bipolar_map [SimplyConnectedSpace M] [SecondCountableTopology M]
    {p₁ p₂ : M} (hne : p₁ ≠ p₂) {G : M → ℝ} (hG : MHarmonicOn G ({p₁, p₂}ᶜ))
    (hpole₁ : ∃ r > 0, ball (chartAt ℂ p₁ p₁) r ⊆ (chartAt ℂ p₁).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₁ p₁) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₁ p₁) r \ {chartAt ℂ p₁ p₁},
          h w = G ((chartAt ℂ p₁).symm w) + Real.log ‖w - chartAt ℂ p₁ p₁‖)
    (hpole₂ : ∃ r > 0, ball (chartAt ℂ p₂ p₂) r ⊆ (chartAt ℂ p₂).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₂ p₂) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₂ p₂) r \ {chartAt ℂ p₂ p₂},
          h w = G ((chartAt ℂ p₂).symm w) - Real.log ‖w - chartAt ℂ p₂ p₂‖) :
    ∃ φ : M → ℂ̂, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ ∧ φ p₁ = ((0 : ℂ) : ℂ̂) ∧
      φ p₂ = OnePoint.infty ∧
      ∀ x, x ≠ p₁ → x ≠ p₂ →
        ∃ w : ℂ, φ x = (w : ℂ̂) ∧ ‖w‖ = Real.exp (-(G x)) := by
  sorry

/-- **Injectivity of the dipole map**, by the Blaschke comparison against the
extremal property of the piece Green's functions. -/
theorem injective_bipolar_map [SimplyConnectedSpace M]
    [SecondCountableTopology M] (hnon : ∀ p₀ : M, ¬ HasGreenFunction p₀)
    {p₁ p₂ : M} (hne : p₁ ≠ p₂) {G : M → ℝ} {φ : M → ℂ̂}
    (hφ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ) (h₁ : φ p₁ = ((0 : ℂ) : ℂ̂))
    (h₂ : φ p₂ = OnePoint.infty)
    (habs : ∀ x, x ≠ p₁ → x ≠ p₂ →
      ∃ w : ℂ, φ x = (w : ℂ̂) ∧ ‖w‖ = Real.exp (-(G x))) :
    Function.Injective φ := by
  sorry

/-! ## The compact case and the non-hyperbolic assembly -/

/-- **Compact surfaces carry no Green's function**: the Perron family is
unbounded at every point distinct from the pole. -/
theorem not_bddAbove_greenFamily_of_compactSpace [CompactSpace M]
    [SecondCountableTopology M] (p₀ x : M) (hx : x ≠ p₀) :
    ¬ BddAbove ((fun v => v x) '' greenFamily p₀) := by
  sorry

/-- **The non-hyperbolic case of planarity**: a simply connected surface
without a Green's function embeds onto a domain of the Riemann sphere via the
dipole map. -/
theorem exists_diffeomorph_opens_of_forall_not_hasGreenFunction
    [SimplyConnectedSpace M] [SecondCountableTopology M]
    (hnon : ∀ p₀ : M, ¬ HasGreenFunction p₀) :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  sorry

end RiemannDynamics
