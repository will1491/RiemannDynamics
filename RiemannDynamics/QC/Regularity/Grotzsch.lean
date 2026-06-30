/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.RingModulus
import RiemannDynamics.Analysis.CircularRearrangement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Grötzsch and Teichmüller extremal estimates

This file states the **extremal length estimates** that drive all of planar quasiconformal
regularity: the Grötzsch and Teichmüller modulus inequalities. All moduli here are the
**connecting-family moduli** of `QC/Regularity/RingModulus.lean` (the `curveModulus` of the curves
joining the two boundary continua of a ring; for a round annulus `2π / log (R / r)`), so the
Grötzsch and Teichmüller configurations *minimize* the connecting modulus among rings separating two
prescribed continua — the reciprocal of the classical separating-module *maximum* property. They are
the *single hardest foundational input* of the regularity layer; everything downstream
(quasisymmetry, equicontinuity, normal families) is derived from them by `K`-quasiconformal modulus
distortion.

Each estimate below is a *true classical theorem* (Väisälä §11, Lehto–Virtanen Ch. II, Ahlfors
Ch. III). None of them holds for a bare homeomorphism: they are statements about the conformal
modulus of *concrete plane rings*, used downstream only through the inequality
`curveModulus (f-image family) ≤ K · curveModulus (family)` that defines `IsQCGeometric f K`. The
estimates here carry **no derivative control** — they are pure modulus facts about plane domains.

## Main statements (all `sorry`; the extremal theory is to be filled in)

* `grotzschModulus_monotone` — the Grötzsch connecting modulus is monotone increasing on `(0, 1)`;
* `grotzschModulus_tendsto_zero_zero` — `grotzschModulus s → 0` as `s → 0⁺`;
* `grotzschModulus_tendsto_one_atTop` — `grotzschModulus s → +∞` as `s → 1⁻`;
* `grotzschModulus_le_ringModulus` — **Grötzsch's inequality**: among rings separating a continuum
  containing `{0, s}` from the unit circle, the Grötzsch ring is extremal (minimal connecting
  modulus);
* `teichmuller_identity` — the Teichmüller identity relating the two extremal moduli;
* `teichmullerModulus_le_ringModulus_separating_two_pairs` — the **Teichmüller comparison**: a ring
  separating `{0, z₁}` from `{z₂, ∞}` has connecting modulus at least the Teichmüller modulus of
  `‖z₂‖ / ‖z₁‖`.

## References

* J. Väisälä, *Lectures on n-dimensional quasiconformal mappings*, §11 (Grötzsch and Teichmüller
  rings; the extremal property).
* O. Lehto and K. I. Virtanen, *Quasiconformal mappings in the plane*, Ch. II §1 (the module of a
  ring domain and the extremal estimates).
* L. V. Ahlfors, *Lectures on quasiconformal mappings*, Ch. III §A.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- **The Grötzsch connecting modulus is monotone increasing.** For `0 < s₁ ≤ s₂ < 1` the Grötzsch
ring with the longer slit has the larger connecting modulus:
`grotzschModulus s₁ ≤ grotzschModulus s₂`. A longer slit pushes the ring toward the fat regime
(`R / r → 1`), increasing its connecting modulus. (Monotonicity, the qualitative content needed
downstream; strict monotonicity and continuity follow from the explicit special-function formula but
are not required by the regularity layer.) -/
theorem grotzschModulus_monotone {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₁ ≤ s₂) (h₃ : s₂ < 1) :
    grotzschModulus s₁ ≤ grotzschModulus s₂ := by
  sorry

/-- **The Grötzsch connecting modulus vanishes at the inner boundary.** As the slit `[0, s]` shrinks
to the point `{0}` the Grötzsch ring approaches the punctured disk (the fat-ring degeneration
`R / r → ∞` for the *separating* family), whose connecting modulus tends to `0`:
`grotzschModulus s → 0` as `s → 0⁺`. This is the source of the logarithmic blow-up of quasiconformal
distortion near a point. -/
theorem grotzschModulus_tendsto_zero_zero :
    Tendsto grotzschModulus (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry

/-- **The Grötzsch connecting modulus blows up at the outer boundary.** As the slit `[0, s]` extends
to fill a diameter (`s → 1⁻`) the ring degenerates to the fat regime (`R / r → 1`) and its
connecting modulus tends to `+∞`: `grotzschModulus s → +∞` as `s → 1⁻`. -/
theorem grotzschModulus_tendsto_one_atTop :
    Tendsto grotzschModulus (𝓝[<] (1 : ℝ)) atTop := by
  sorry

/-- **Grötzsch's extremal inequality.** Let `E` be a continuum contained in the closed disk that
contains both `0` and the point `s` (`0 < s < 1`), and let `U ⊆ ball 0 1` be a ring separating `E`
from the unit circle. Then the connecting modulus of the family of curves joining `E` to the unit
circle inside `U` is at least the Grötzsch modulus `grotzschModulus s`:

`grotzschModulus s ≤ curveModulus (connectingCurveFamily E grotzschOuter U)`.

In words: the Grötzsch ring *minimizes* the connecting modulus among all rings separating a
continuum joining `0` to the circle `|z| = s` from the unit circle (the reciprocal of the classical
separating-module maximum). The inner slit is the extremal (smallest connecting modulus)
configuration for a continuum of given "reach" `s`. The continuum hypothesis is essential — for a
disconnected `E` (e.g. just the two points `{0, s}`) the family is larger and the connecting modulus
can exceed `grotzschModulus s`. -/
theorem grotzschModulus_le_ringModulus {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {E U : Set ℂ} (hEconn : IsConnected E) (hEdisk : E ⊆ Metric.closedBall (0 : ℂ) 1)
    (hE0 : (0 : ℂ) ∈ E) (hEs : (s : ℂ) ∈ E)
    (hUdisk : U ⊆ Metric.ball (0 : ℂ) 1) (hUsep : E ⊆ closure U) :
    grotzschModulus s ≤ curveModulus (connectingCurveFamily E grotzschOuter U) := by
  -- Abbreviations for the two connecting families.
  set Γ_U : Set (ℝ → ℂ) := connectingCurveFamily E grotzschOuter U with hΓU
  set Γ_G : Set (ℝ → ℂ) :=
    connectingCurveFamily (grotzschInner s) grotzschOuter (grotzschRing s) with hΓG
  -- ===================================================================
  -- BLOCKER (the Pólya–Szegő circular-symmetrization core).
  -- For every density `ρ` admissible for the *general* ring family `Γ_U`
  -- there is a density `ρ'` admissible for the *Grötzsch* ring family `Γ_G`
  -- whose planar `L²` energy does not exceed that of `ρ`.  This is the entire
  -- geometric content of Grötzsch's inequality and is where the continuum
  -- hypotheses `hEconn`/`hE0`/`hEs`/`hUsep` enter.  The classical
  -- construction takes `ρ'` to be the circular symmetrization of `ρ` about
  -- the origin: circular rearrangement preserves the planar `L²` energy
  -- (`lintegral_circRearrange_sq`, so the energy is in fact *equal*), and the
  -- symmetrized density is admissible for the Grötzsch ring.  The existential
  -- form is the honest atomic blocker: it commits only to the conclusion (a
  -- competitor of no larger energy), not to per-curve admissibility of any
  -- particular symmetrization, which is a global/integral fact, not a
  -- curve-by-curve one.
  -- ===================================================================
  have energy_competitor : ∀ {ρ : ℂ → ℝ≥0∞}, IsAdmissibleDensity ρ Γ_U →
      ∃ ρ' : ℂ → ℝ≥0∞, IsAdmissibleDensity ρ' Γ_G ∧
        ∫⁻ z, (ρ' z) ^ 2 ≤ ∫⁻ z, (ρ z) ^ 2 := by
    -- The classical construction takes `ρ'` to be the circular symmetrization
    -- `circRearrange c ρ` of `ρ` about the centre `c` of the configuration, with
    -- the symmetrization axis aligned to the slit.  Its energy *equals* that of
    -- `ρ` (`lintegral_circRearrange_sq`) and its measurability is
    -- `measurable_circRearrange`, so only the admissibility of the symmetrized
    -- density for `Γ_G` remains — the irreducible Pólya–Szegő core (see the
    -- decomposition notes accompanying this proof).  The existential form is kept
    -- so the blocker commits only to the existence of a competitor of no larger
    -- energy, never to per-curve admissibility of one fixed symmetrization.
    sorry
  -- ===================================================================
  -- Reduction: it suffices to bound the Grötzsch modulus by the energy of an
  -- arbitrary `Γ_U`-admissible density `ρ`.  The blocker supplies a
  -- `Γ_G`-admissible competitor `ρ'` of no larger energy, so the Grötzsch
  -- infimum is `≤ ∫ (ρ')² ≤ ∫ ρ²`.
  -- ===================================================================
  rw [show grotzschModulus s = curveModulus Γ_G from rfl]
  unfold curveModulus
  refine le_iInf₂ ?_
  rintro ρ ⟨hρmeas, hρadm⟩
  have hρ : IsAdmissibleDensity ρ Γ_U := ⟨hρmeas, hρadm⟩
  obtain ⟨ρ', hρ'adm, hρ'energy⟩ := energy_competitor hρ
  -- The Grötzsch modulus infimum is bounded by the energy of the competitor `ρ'`.
  have hinf_le : (⨅ ρ'' ∈ {ρ'' : ℂ → ℝ≥0∞ | IsAdmissibleDensity ρ'' Γ_G},
      ∫⁻ z, (ρ'' z) ^ 2) ≤ ∫⁻ z, (ρ' z) ^ 2 :=
    iInf₂_le ρ' hρ'adm
  exact le_trans hinf_le hρ'energy

/-- **The Teichmüller identity.** The Grötzsch and Teichmüller connecting moduli are two views of
the same extremal function: for `t > 0`,

`teichmullerModulus t = (1 / 2) * grotzschModulus (1 / Real.sqrt (1 + t))`.

The map `z ↦ z²` (a 2-to-1 conformal branched cover) carries the Grötzsch configuration to half of
the Teichmüller configuration, doubling the *separating* module; in the reciprocal connecting
convention the factor `2` becomes `1 / 2` (classically `τ(t) = 2 μ(1/√(1+t))` for the separating
modules `τ, μ`). This identity lets the Teichmüller comparison below be reduced to the Grötzsch
inequality. -/
theorem teichmuller_identity {t : ℝ} (ht : 0 < t) :
    teichmullerModulus t = (1 / 2) * grotzschModulus (1 / Real.sqrt (1 + t)) := by
  sorry

/-- **The Teichmüller comparison estimate.** Let `U` be a ring separating a continuum `E₁ ∋ 0, z₁`
from a continuum `E₂ ∋ z₂` and `∞` (the two complementary continua of the ring), with `z₁ ≠ 0` and
`z₂ ≠ 0`. Then the Teichmüller modulus of the ratio `‖z₂‖ / ‖z₁‖` is a lower bound for the
connecting modulus of the ring:

`teichmullerModulus (‖z₂‖ / ‖z₁‖) ≤ curveModulus (connectingCurveFamily E₁ E₂ U)`.

In the connecting convention the Teichmüller ring *minimizes* the modulus among rings separating
`{0, z₁}` from `{z₂, ∞}`, so its modulus is the extremal lower bound. This is the bound that
converts a modulus inequality into a *metric* (quasisymmetry) inequality, controlling the ratio
`‖z₂‖ / ‖z₁‖` through the modulus. It is the workhorse for the quasisymmetry estimate in
`Quasisymmetry.lean`. Both continua being *connected* and reaching `∞` (resp. containing `0`) is
essential; for finite point sets the comparison fails. -/
theorem teichmullerModulus_le_ringModulus_separating_two_pairs {z₁ z₂ : ℂ}
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    {E₁ E₂ U : Set ℂ} (hE₁conn : IsConnected E₁) (hE₂conn : IsConnected E₂)
    (hE₁0 : (0 : ℂ) ∈ E₁) (hE₁z : z₁ ∈ E₁) (hE₂z : z₂ ∈ E₂) (hE₂unbdd : ¬ Bornology.IsBounded E₂)
    (hsep₁ : E₁ ⊆ closure U) (hsep₂ : E₂ ⊆ closure U) :
    teichmullerModulus (‖z₂‖ / ‖z₁‖) ≤ curveModulus (connectingCurveFamily E₁ E₂ U) := by
  sorry

/-- **Lower bound on the Teichmüller modulus by a control function of the ratio.** There is a
function `Φ : ℝ → ℝ`, depending only on the Teichmüller modulus, with `Φ t → +∞` as `t → 0⁺`, such
that `teichmullerModulus t ≥ ENNReal.ofReal (Φ t)` for all `t > 0`. This is the half of the
Teichmüller estimate used in `Quasisymmetry.lean`: a *lower* bound on the modulus in terms of the
geometric ratio. Concretely `Φ` is (a `2π`-normalization of) the inverse Grötzsch function; only its
qualitative blow-up at `0` is consumed downstream. -/
theorem exists_teichmullerModulus_lower_bound :
    ∃ Φ : ℝ → ℝ, Tendsto Φ (𝓝[>] (0 : ℝ)) atTop ∧
      ∀ t : ℝ, 0 < t → ENNReal.ofReal (Φ t) ≤ teichmullerModulus t := by
  sorry

end RiemannDynamics
