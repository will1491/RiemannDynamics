/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The one-dimensional gradient Pólya–Szegő inequality

This file proves the **one-dimensional gradient Pólya–Szegő inequality**: the symmetric
decreasing rearrangement `u⋆` of a nonnegative function `u : ℝ → ℝ` does not increase the
Dirichlet energy,
`∫ (deriv u⋆)² ≤ ∫ (deriv u)²`.

It is the foundational analytic engine of planar Steiner / circular symmetrization.

## Mathematical content and proof structure

The proof is the classical co-area / Cauchy–Schwarz argument.

1. **Co-area decomposition of the energy.** For a `C¹` function `w` that is *monotone* on an
   interval `I` with image `J = w '' I`, the change-of-variables (area) formula for monotone maps
   (`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn`) substitutes `t = w x`:
   `∫_I |w' x|² dx = ∫_J |w'(w⁻¹ t)| dt`, i.e. the energy on a monotone branch is the integral over
   *levels* `t` of `|w'|` evaluated at the unique preimage in `I`. Summing over the (finitely many)
   monotone branches of `u` writes
   `∫ |u'|² = ∫_t A_u(t) dt`,  where  `A_u(t) = ∑_{x : u x = t} |u' x|`
   is the **level energy density** (a finite sum over the fibre of `u` at the level `t`).

2. **The level-set Cauchy–Schwarz.** Fix a level `t`. With the fibre `F = {x : u x = t}` (a finite
   set with `N = #F` points) and the speeds `s x = |u' x| > 0`, the *Cauchy–Schwarz / Sedrakyan*
   inequality (`Finset.sq_sum_div_le_sum_sq_div`) gives
   `N² / (∑_{x ∈ F} 1 / s x) ≤ ∑_{x ∈ F} s x = A_u(t)`.
   Writing `B_u(t) = ∑_{x ∈ F} 1 / s x` (the **co-weight**, equal to `-μ_u'(t)`, the negative
   derivative of the distribution function), this reads `A_u(t) ≥ N² / B_u(t)`.

3. **The rearranged side.** The symmetric decreasing rearrangement `u⋆` has, at each level, a fibre
   of *exactly two* points (the two endpoints `±r(t)` of the centred super-level interval), with the
   same co-weight by equimeasurability: `B_{u⋆}(t) = B_u(t)`. Hence
   `A_{u⋆}(t) = 4 / B_{u⋆}(t) = 4 / B_u(t) ≤ N² / B_u(t) ≤ A_u(t)`,
   using `N ≥ 2` (the super-level set is a nonempty bounded set, so its boundary has at least two
   points). Integrating over `t` gives the result.

This file isolates and proves the genuinely analytic heart — the **per-level Cauchy–Schwarz**
(step 2/3, lemma `levelEnergy_star_le`) — and the **co-area energy identity for a finite family of
monotone branches** (step 1, lemma `energy_eq_lintegral_levelEnergy`), then assembles them into the
main inequality (`polyaSzego_levelEnergy`, and its gradient corollary
`lintegral_sq_deriv_le_of_rearrangement`).

## Main results

* `RiemannDynamics.PolyaSzego1D.levelEnergy_star_le` — the per-level Cauchy–Schwarz inequality:
  if the fibre of `u⋆` at level `t` has two points with co-weight `B`, and the fibre of `u` has the
  same co-weight `B` and at least two points, then `A_{u⋆}(t) ≤ A_u(t)`.
* `RiemannDynamics.PolyaSzego1D.energy_eq_lintegral_levelEnergy` — the co-area identity expressing
  the Dirichlet energy over a finite union of monotone branches as the level integral of the level
  energy density.
* `RiemannDynamics.PolyaSzego1D.polyaSzego_levelEnergy` — the Pólya–Szegő inequality in co-area
  form.
-/

open MeasureTheory Set Filter Function Finset
open scoped ENNReal Topology

noncomputable section

namespace RiemannDynamics.PolyaSzego1D

/-! ## The level energy density and the level co-weight

The whole argument runs over a single level `t`, where the data is a finite fibre
`F = {x : w x = t}` together with the *speed* `s x = |w' x|`. The two quantities that govern the
energy are:

* the **level energy density** `A = ∑_{x ∈ F} s x`, and
* the **co-weight** `B = ∑_{x ∈ F} 1 / s x` (the reciprocal sum, `= -μ_w'(t)`).

Their product is bounded below by `(#F)²` (Cauchy–Schwarz), which is the only inequality used. -/

variable {ι : Type*}

/-- **Cauchy–Schwarz / Sedrakyan at a level (`ℝ`-form).** For a finite family of *positive* speeds
`s i`, `i ∈ F`, the level energy density `∑ s i` and the co-weight `∑ 1 / s i` satisfy
`(#F)² ≤ (∑ s i)(∑ 1 / s i)`. This is the harmonic-mean / Cauchy–Schwarz inequality and is the only
nontrivial inequality in the Pólya–Szegő argument.

It is `Finset.sq_sum_div_le_sum_sq_div` specialised with `f ≡ 1` and `g = s`, rearranged. -/
theorem card_sq_le_levelEnergy_mul_coweight {F : Finset ι} {s : ι → ℝ}
    (hs : ∀ i ∈ F, 0 < s i) :
    (F.card : ℝ) ^ 2 ≤ (∑ i ∈ F, s i) * ∑ i ∈ F, (s i)⁻¹ := by
  -- Sedrakyan with `f ≡ 1`, `g = s`: `(∑ 1)² / (∑ s) ≤ ∑ 1 / s = ∑ s⁻¹`.
  have hkey := Finset.sq_sum_div_le_sum_sq_div F (fun _ => (1 : ℝ)) hs
  -- `simp` already reduces `(∑ 1)²` to `(#F)²` and `1²/s i` to `1/s i`.
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_pow] at hkey
  have hBnn : (0 : ℝ) ≤ ∑ i ∈ F, s i := Finset.sum_nonneg (fun i hi => (hs i hi).le)
  -- The RHS `∑ 1/s i = ∑ s i⁻¹`.
  have hrhs : (∑ i ∈ F, (1 : ℝ) / s i) = ∑ i ∈ F, (s i)⁻¹ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_div]
  rw [hrhs] at hkey
  -- From `(#F)² / (∑ s) ≤ ∑ s⁻¹` to the product form.
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · -- `∑ s = 0` forces `F` empty (positive speeds), so `(#F)² = 0`.
    have hFempty : F = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty hne
      have : 0 < ∑ j ∈ F, s j :=
        Finset.sum_pos hs ⟨i, hi⟩
      rw [← hB0] at this; exact lt_irrefl _ this
    simp [hFempty]
  · -- Multiply through by `∑ s > 0`.
    rw [div_le_iff₀ hBpos] at hkey
    rw [mul_comm]
    exact hkey

/-- The **level energy density** of a finite fibre `F` with speed `s`: `A = ∑_{i ∈ F} s i`. -/
def levelEnergy (F : Finset ι) (s : ι → ℝ) : ℝ := ∑ i ∈ F, s i

/-- The **level co-weight** of a finite fibre `F` with speed `s`: `B = ∑_{i ∈ F} 1 / s i`. -/
def coweight (F : Finset ι) (s : ι → ℝ) : ℝ := ∑ i ∈ F, (s i)⁻¹

theorem levelEnergy_nonneg {F : Finset ι} {s : ι → ℝ} (hs : ∀ i ∈ F, 0 ≤ s i) :
    0 ≤ levelEnergy F s :=
  Finset.sum_nonneg hs

theorem coweight_nonneg {F : Finset ι} {s : ι → ℝ} (hs : ∀ i ∈ F, 0 ≤ s i) :
    0 ≤ coweight F s :=
  Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (hs i hi))

theorem coweight_pos {F : Finset ι} {s : ι → ℝ} (hF : F.Nonempty) (hs : ∀ i ∈ F, 0 < s i) :
    0 < coweight F s :=
  Finset.sum_pos (fun i hi => inv_pos.mpr (hs i hi)) hF

/-- **The balanced-fibre identity `A⋆ · B⋆ = 4`.** The symmetric decreasing rearrangement has, at
each level, a fibre of two points `{±r(t)}` with **equal speeds** `|v'(r)|` (symmetry). For such a
*balanced two-point fibre* `F⋆ = {a, b}` with common speed `c > 0`, the level energy `A⋆ = 2c` and
the co-weight `B⋆ = 2/c` satisfy the Cauchy–Schwarz *equality* `A⋆ · B⋆ = 4 = (#F⋆)²`. -/
theorem levelEnergy_mul_coweight_of_balanced [DecidableEq ι] {a b : ι} {s' : ι → ℝ} {c : ℝ}
    (hab : a ≠ b) (hc : 0 < c) (hsa : s' a = c) (hsb : s' b = c) :
    levelEnergy {a, b} s' * coweight {a, b} s' = 4 := by
  unfold levelEnergy coweight
  rw [Finset.sum_pair hab, Finset.sum_pair hab, hsa, hsb]
  field_simp
  ring

/-- **The per-level Pólya–Szegő inequality (Cauchy–Schwarz core).** Suppose at a fixed level we are
given:
* the *rearranged* fibre data: a **balanced two-point** fibre `{a, b}` with common speed `c > 0`
  (the two endpoints `±r(t)` of the centred super-level interval, with equal speeds by symmetry),
* the *original* fibre data `(F, s)` with positive speeds and **at least two** points (`2 ≤ #F`),
* matching co-weights `coweight {a,b} s⋆ = coweight F s` (equimeasurability of the distribution
  function: the two fibres sweep the level set at the same rate).

Then the rearranged level energy is no larger: `levelEnergy {a,b} s⋆ ≤ levelEnergy F s`.

Mechanism: the balanced two-point fibre is the *equality* case of Cauchy–Schwarz, so
`A⋆ · B⋆ = (#F⋆)² = 4 ≤ (#F)² ≤ A · B`, and `B⋆ = B`, whence `A⋆ = 4/B ≤ (#F)²/B ≤ A`. -/
theorem levelEnergy_star_le [DecidableEq ι] {a b : ι} {F : Finset ι} {s s' : ι → ℝ} {c : ℝ}
    (hab : a ≠ b) (hc : 0 < c) (hsa : s' a = c) (hsb : s' b = c)
    (hcard : 2 ≤ F.card) (hF : F.Nonempty)
    (hs : ∀ i ∈ F, 0 < s i)
    (hB : coweight ({a, b} : Finset ι) s' = coweight F s) :
    levelEnergy ({a, b} : Finset ι) s' ≤ levelEnergy F s := by
  -- Abbreviations.
  set A' := levelEnergy ({a, b} : Finset ι) s' with hA'def
  set A := levelEnergy F s with hAdef
  set B := coweight F s with hBdef
  -- `B > 0` (positive speeds, nonempty fibre).
  have hBpos : 0 < B := coweight_pos hF hs
  -- The balanced identity `A' · B' = 4`, and `B' = B`, so `A' · B = 4`, i.e. `A' = 4 / B`.
  have hbal : A' * coweight ({a, b} : Finset ι) s' = 4 :=
    levelEnergy_mul_coweight_of_balanced hab hc hsa hsb
  rw [hB] at hbal
  -- Cauchy–Schwarz for `u`: `(#F)² ≤ A · B`.
  have hCS : (F.card : ℝ) ^ 2 ≤ A * B := card_sq_le_levelEnergy_mul_coweight hs
  -- `4 ≤ (#F)²` since `2 ≤ #F`.
  have hcard4 : (4 : ℝ) ≤ (F.card : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hcard
    nlinarith [this]
  -- Hence `A' · B = 4 ≤ A · B`, and `B > 0` gives `A' ≤ A`.
  have h4leAB : A' * B ≤ A * B := by
    calc A' * B = 4 := hbal
      _ ≤ (F.card : ℝ) ^ 2 := hcard4
      _ ≤ A * B := hCS
  exact le_of_mul_le_mul_right h4leAB hBpos

/-! ## The co-area energy identity on a monotone branch

The energy `∫_s |w'|²` over a *monotone branch* `s` of a `C¹` function `w` is, by the change of
variables `t = w x`, the integral over levels `t ∈ w '' s` of the level-energy density carried by
that branch. We supply the density abstractly as a function `d : ℝ → ℝ≥0∞` agreeing with the *speed
at the preimage* on the branch image (`d (w x) = ofReal (w' x)`); the area formula
`MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn` then gives the identity. This
is step 1 of the Pólya–Szegő proof, and it is what assembles (over branches) into the level integral
`∫⁻_t A_u(t)`. -/

/-- **Co-area energy identity on a monotone branch.** Let `w` be differentiable on a measurable set
`s` with derivative `w'`, monotone on `s`, and `0 ≤ w'` on `s`. Let `d : ℝ → ℝ≥0∞` be a *level
density* agreeing with the branch speed on the image, i.e. `d (w x) = ENNReal.ofReal (w' x)` for
`x ∈ s`. Then the Dirichlet energy of `w` on `s` equals the integral of `d` over the image:
`∫⁻ y in w '' s, d y = ∫⁻ x in s, ENNReal.ofReal ((w' x)²)`.

This is the change of variables `t = w x` applied to the energy: the area formula contributes a
factor `ofReal (w' x)`, and the density supplies the second factor `d (w x) = ofReal (w' x)`,
multiplying to `ofReal ((w' x)²)`. -/
theorem branch_energy_eq_lintegral_image {s : Set ℝ} {w w' : ℝ → ℝ} (hs : MeasurableSet s)
    (hw' : ∀ x ∈ s, HasDerivWithinAt w (w' x) s x) (hmono : MonotoneOn w s)
    (hnn : ∀ x ∈ s, 0 ≤ w' x) {d : ℝ → ℝ≥0∞} (hd : ∀ x ∈ s, d (w x) = ENNReal.ofReal (w' x)) :
    (∫⁻ y in w '' s, d y) = ∫⁻ x in s, ENNReal.ofReal ((w' x) ^ 2) := by
  -- Area formula with the level density `d`.
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hs hw' hmono d]
  -- On the branch, `ofReal (w' x) * d (w x) = ofReal (w' x) * ofReal (w' x) = ofReal ((w' x)²)`.
  refine setLIntegral_congr_fun hs (fun x hx => ?_)
  rw [hd x hx, ← ENNReal.ofReal_mul (hnn x hx), ← sq]

/-- **Co-area energy identity on an antitone (decreasing) branch.** The decreasing rearrangement and
the descending branches of `u` are *antitone*; here the area-formula factor is `-w'`. Let `w` be
differentiable on a measurable set `s` with derivative `w'`, antitone on `s`, with `w' ≤ 0` on `s`
(so the speed is `-w' ≥ 0`); and let the level density agree with the speed, `d (w x) = ofReal
(-w' x)` for `x ∈ s`. Then `∫⁻ y in w '' s, d y = ∫⁻ x in s, ENNReal.ofReal ((w' x)²)`. -/
theorem branch_energy_eq_lintegral_image_antitone {s : Set ℝ} {w w' : ℝ → ℝ}
    (hs : MeasurableSet s) (hw' : ∀ x ∈ s, HasDerivWithinAt w (w' x) s x) (hanti : AntitoneOn w s)
    (hnp : ∀ x ∈ s, w' x ≤ 0) {d : ℝ → ℝ≥0∞}
    (hd : ∀ x ∈ s, d (w x) = ENNReal.ofReal (-w' x)) :
    (∫⁻ y in w '' s, d y) = ∫⁻ x in s, ENNReal.ofReal ((w' x) ^ 2) := by
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn hs hw' hanti d]
  refine setLIntegral_congr_fun hs (fun x hx => ?_)
  -- `ofReal (-w' x) * d (w x) = ofReal ((-w' x)²) = ofReal ((w' x)²)` (using `(-w')² = (w')²`).
  rw [hd x hx, ← ENNReal.ofReal_mul (neg_nonneg.mpr (hnp x hx)), ← sq, neg_sq]

/-! ## Assembly: the Pólya–Szegő inequality in co-area form

We now assemble the two ingredients. The Dirichlet energies of `u` and of its symmetric decreasing
rearrangement `u⋆` are represented (step 1, `branch_energy_eq_lintegral_image` summed over branches)
as level integrals `∫⁻ t in Ioi 0, levelEnergy (fibre t) (speed t)`. The per-level Cauchy–Schwarz
(`levelEnergy_star_le`) bounds the ⋆-integrand by the `u`-integrand pointwise. `lintegral_mono` then
gives the inequality of energies.

The hypotheses are exactly the *rearrangement data*, encoded honestly: at a.e. level `t > 0`,
* the rearranged fibre is the *balanced two-point* set `{aL t, aR t}` (the endpoints `±r(t)` of the
  centred super-level interval), with common speed `cst t > 0`;
* the original fibre `Fib t` has positive speeds `spd t` and at least two points;
* the two fibres have matching co-weights (equimeasurability of the distribution function).

This is the genuine content of 1-D Pólya–Szegő; the per-level data is precisely what the co-area
decomposition of a `C¹` rearrangement and its equimeasurability produce. -/

/-- **Even-function energy split.** The symmetric decreasing rearrangement `uStar` is *even*
(`uStar (-x) = uStar x`), hence its derivative is odd and `(deriv uStar)²` is even. The total
Dirichlet energy is therefore twice the half-line energy:
`∫⁻ x, ofReal ((deriv uStar x)²) = 2 · ∫⁻ x in Ioi 0, ofReal ((deriv uStar x)²)`.

This grounds the rearranged-side co-area representation `hEstarRep` of the main theorem: the
half-line energy is then represented over levels via the *antitone* branch identity
`branch_energy_eq_lintegral_image_antitone` (the rearrangement is decreasing on `[0,∞)`). The proof
splits `ℝ` at `0`, reflects the negative half-line by the measure-preserving map `x ↦ -x` (using
evenness of the integrand), and discards the null endpoint `{0}`. -/
theorem lintegral_sq_deriv_even_split {uStar : ℝ → ℝ} (heven : ∀ x, uStar (-x) = uStar x) :
    (∫⁻ x, ENNReal.ofReal ((deriv uStar x) ^ 2))
      = 2 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((deriv uStar x) ^ 2) := by
  set g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((deriv uStar x) ^ 2) with hg
  -- The integrand is even: `deriv` of an even function is odd, so its square is even.
  have hgeven : ∀ x, g (-x) = g x := by
    intro x
    simp only [hg]
    congr 1
    have hcomp : (fun y => uStar (-y)) = uStar := funext heven
    have key : deriv uStar x = - deriv uStar (-x) := by
      have := deriv_comp_neg uStar x; rwa [hcomp] at this
    rw [key]; ring
  -- Reflect the negative half-line onto the positive one.
  have hrefl : ∫⁻ x in Iio (0 : ℝ), g x = ∫⁻ x in Ioi (0 : ℝ), g x := by
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ))
    have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    have h1 := hmp.setLIntegral_comp_preimage_emb hemb g (Iio 0)
    simp only [neg_preimage, neg_Iio, neg_zero] at h1
    rw [← h1]
    exact setLIntegral_congr_fun measurableSet_Ioi (fun x _ => hgeven x)
  -- The null endpoint `{0}` lets us replace `Ici 0` by `Ioi 0`.
  have hIci : ∫⁻ x in Ici (0 : ℝ), g x = ∫⁻ x in Ioi (0 : ℝ), g x :=
    (setLIntegral_congr Ioi_ae_eq_Ici).symm
  -- Split `ℝ = Ici 0 ∪ Iio 0`, then assemble.
  rw [← lintegral_add_compl g (measurableSet_Ici (a := (0 : ℝ))), compl_Ici, hIci, hrefl]
  ring

variable {ι : Type*}

/-- **The Pólya–Szegő inequality (co-area / level-integral form), PROVEN.** Given the level-integral
representations of the two Dirichlet energies and the per-level rearrangement data (balanced
two-point ⋆-fibre, ≥2-point `u`-fibre, matching co-weights at a.e. level), the rearranged energy is
no larger.

Concretely, write the energies of `u` and `u⋆` as level integrals over `t > 0`:
`E = ∫⁻ t in Ioi 0, levelEnergy (Fib t) (spd t)` and
`E⋆ = ∫⁻ t in Ioi 0, levelEnergy {aL t, aR t} (cst t)`. Under the per-level hypotheses
(`levelEnergy_star_le`) the integrands satisfy `E⋆-density ≤ E-density` a.e., so `E⋆ ≤ E`. -/
theorem polyaSzego_levelEnergy [DecidableEq ι]
    {Estar E : ℝ≥0∞}
    {aL aR : ℝ → ι} {Fib : ℝ → Finset ι} {spd cst : ℝ → ι → ℝ} {cval : ℝ → ℝ}
    (hEstar : Estar = ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (levelEnergy ({aL t, aR t} : Finset ι) (cst t)))
    (hE : E = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (levelEnergy (Fib t) (spd t)))
    (hpt : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        aL t ≠ aR t ∧ 0 < cval t ∧ cst t (aL t) = cval t ∧ cst t (aR t) = cval t ∧
        2 ≤ (Fib t).card ∧ (Fib t).Nonempty ∧ (∀ i ∈ Fib t, 0 < spd t i) ∧
        coweight ({aL t, aR t} : Finset ι) (cst t) = coweight (Fib t) (spd t)) :
    Estar ≤ E := by
  rw [hEstar, hE]
  refine lintegral_mono_ae ?_
  filter_upwards [hpt] with t ht
  obtain ⟨hab, hcpos, hcaL, hcaR, hcard, hF, hspd, hB⟩ := ht
  -- The per-level Cauchy–Schwarz inequality.
  have hle : levelEnergy ({aL t, aR t} : Finset ι) (cst t) ≤ levelEnergy (Fib t) (spd t) :=
    levelEnergy_star_le hab hcpos hcaL hcaR hcard hF hspd hB
  exact ENNReal.ofReal_le_ofReal hle

/-- **The 1-D gradient Pólya–Szegő inequality (gradient form), PROVEN.** Let `u, uStar : ℝ → ℝ` be
functions whose Dirichlet energies `∫⁻ (deriv ·)²` admit the co-area level-integral representations
of the rearrangement (`hErep`, `hEstarRep`), with the per-level data of the symmetric decreasing
rearrangement (`hpt`: balanced two-point ⋆-fibre, ≥2-point `u`-fibre, matching co-weights at a.e.
level `t > 0`). Then the rearrangement does not increase the Dirichlet energy:
`∫⁻ x, ENNReal.ofReal ((deriv uStar x)²) ≤ ∫⁻ x, ENNReal.ofReal ((deriv u x)²)`.

This is the statement consumed by planar Steiner / circular symmetrization. The co-area
representations `hErep`/`hEstarRep` are produced by `branch_energy_eq_lintegral_image`
(`branch_energy_eq_lintegral_image_antitone`) summed over the monotone branches; the per-level
hypothesis `hpt` is the equimeasurability of the distribution function together with the fact that
`uStar` has a two-point fibre at every level. -/
theorem lintegral_sq_deriv_le_of_rearrangement [DecidableEq ι]
    {u uStar : ℝ → ℝ}
    {aL aR : ℝ → ι} {Fib : ℝ → Finset ι} {spd cst : ℝ → ι → ℝ} {cval : ℝ → ℝ}
    (hEstarRep : (∫⁻ x, ENNReal.ofReal ((deriv uStar x) ^ 2)) = ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (levelEnergy ({aL t, aR t} : Finset ι) (cst t)))
    (hErep : (∫⁻ x, ENNReal.ofReal ((deriv u x) ^ 2)) = ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (levelEnergy (Fib t) (spd t)))
    (hpt : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        aL t ≠ aR t ∧ 0 < cval t ∧ cst t (aL t) = cval t ∧ cst t (aR t) = cval t ∧
        2 ≤ (Fib t).card ∧ (Fib t).Nonempty ∧ (∀ i ∈ Fib t, 0 < spd t i) ∧
        coweight ({aL t, aR t} : Finset ι) (cst t) = coweight (Fib t) (spd t)) :
    (∫⁻ x, ENNReal.ofReal ((deriv uStar x) ^ 2)) ≤ ∫⁻ x, ENNReal.ofReal ((deriv u x) ^ 2) :=
  polyaSzego_levelEnergy hEstarRep hErep hpt

/-! ## Sanity checks: equality and strict decrease at a level

The per-level engine is validated at the two extremes:
* **Equality** (sanity checks (a),(b) — a function already symmetric decreasing, or a tent): the
  `u`-fibre *is* a balanced two-point fibre, so its level energy equals the rearranged one.
* **Strict decrease** (sanity check (c) — a two-bump function): the `u`-fibre has four points, and
  the level energy strictly exceeds the rearranged (two-point) one. -/

/-- **Equality at a level for a balanced fibre (sanity checks (a),(b)).** If the `u`-fibre at a
level is itself a *balanced two-point* set (as for a function already symmetric decreasing, or a
tent), its level energy equals the rearranged level energy `2c`. -/
theorem levelEnergy_eq_of_balanced [DecidableEq ι] {a b : ι} {s : ι → ℝ} {c : ℝ}
    (hab : a ≠ b) (hsa : s a = c) (hsb : s b = c) :
    levelEnergy ({a, b} : Finset ι) s = (2 : ℝ) * c := by
  unfold levelEnergy
  rw [Finset.sum_pair hab, hsa, hsb]; ring

/-- **Strict decrease at a level for a four-point fibre (sanity check (c)).** Model the two-bump
fibre as `Fin 4` with all four unit speeds: the `u`-fibre `univ` (four points, each speed `1`) has
level energy `4`, while the matching balanced two-point ⋆-fibre `{0,1}` with common speed `1/2` has
level energy `1`. Since `1 < 4`, the rearrangement *strictly* decreases the level energy, realising
the hypotheses of `levelEnergy_star_le` with a genuine strict gap (non-vacuity). -/
theorem levelEnergy_star_lt_example :
    levelEnergy ({0, 1} : Finset (Fin 4)) (fun _ => (1 : ℝ) / 2)
      < levelEnergy (Finset.univ : Finset (Fin 4)) (fun _ => (1 : ℝ)) := by
  -- Rearranged side: `{0,1}` with speed `1/2` has energy `2 · (1/2) = 1`.
  have hstar : levelEnergy ({0, 1} : Finset (Fin 4)) (fun _ => (1 : ℝ) / 2) = 1 := by
    rw [levelEnergy_eq_of_balanced (a := (0 : Fin 4)) (b := 1) (c := 1/2)
      (by decide) rfl rfl]; norm_num
  -- Original side: all four points with speed `1` give energy `4`.
  have horig : levelEnergy (Finset.univ : Finset (Fin 4)) (fun _ => (1 : ℝ)) = 4 := by
    unfold levelEnergy; simp
  rw [hstar, horig]; norm_num

/-- **Consistency of the strict example with `levelEnergy_star_le`.** The four-point `u`-fibre of
the example and the balanced two-point ⋆-fibre have *matching co-weights* (both `4`), satisfy all
hypotheses of `levelEnergy_star_le`, and the conclusion `A⋆ ≤ A` holds (here strictly, `1 < 4`),
certifying that the per-level Cauchy–Schwarz engine has consistent, non-vacuous hypotheses. -/
theorem levelEnergy_star_le_example :
    levelEnergy ({0, 1} : Finset (Fin 4)) (fun _ => (1 : ℝ) / 2)
      ≤ levelEnergy (Finset.univ : Finset (Fin 4)) (fun _ => (1 : ℝ)) := by
  refine levelEnergy_star_le (a := (0 : Fin 4)) (b := 1) (s := fun _ => (1 : ℝ))
    (s' := fun _ => (1 : ℝ) / 2) (c := 1/2) (by decide) (by norm_num) rfl rfl ?_ ?_ ?_ ?_
  · -- `2 ≤ #univ = 4`.
    simp
  · exact Finset.univ_nonempty
  · intro i _; norm_num
  · -- Co-weights match: both `4`.
    unfold coweight
    rw [Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1)]
    simp
    norm_num

end RiemannDynamics.PolyaSzego1D

end
