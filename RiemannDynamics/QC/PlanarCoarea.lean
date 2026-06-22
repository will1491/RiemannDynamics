/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import RiemannDynamics.QC.BanachZaretsky
import RiemannDynamics.QC.BanachIndicatrix
import RiemannDynamics.Analysis.Sobolev.SobolevToACL

/-!
# The planar co-area coupling: the Banach–Zaretsky packaging of slice absolute continuity

This file builds the **1-dimensional Banach–Zaretsky packaging** that the keystone slice-ACL
residual `ae_slice_ac_of_strip_setFunction_ac` (`QC/ConditionNToACL.lean`) needs in order to turn a
per-slice *continuous-monotone-with-condition-(N)* decomposition into genuine **absolute continuity
on every interval**.

## What is proven here (build-verified, axiom-clean)

The genuine *converse* Banach–Zaretsky direction, packaged for the complex slice:

* `absolutelyContinuousOnInterval_of_monotoneN` — a continuous monotone `f : ℝ → ℝ` satisfying
  Lusin's condition (N) (carries Lebesgue-null sets to Lebesgue-null sets) is **absolutely
  continuous on every interval**. This is the genuine converse Banach–Zaretsky / Hencl–Koskela A.32
  packaging: condition (N) makes the Stieltjes measure absolutely continuous
  (`monotone_absolutelyContinuous_of_luzinN`), so the FTC `f b - f a = ∫ₐᵇ deriv f` holds
  (`monotone_ftc_of_luzinN`), exhibiting `f` as `const + primitive` of an interval-integrable
  function, which is AC by `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.

* `absolutelyContinuousOnInterval_of_monotoneDecompN` — if `f = p - q` is a difference of two
  continuous monotone functions each satisfying condition (N), then `f` is absolutely continuous on
  every interval (the previous lemma, plus closure of AC under subtraction). This is exactly the
  hypothesis shape produced by the per-slice monotone decomposition of the Banach–Zaretsky engine.

* `absolutelyContinuousOnInterval_complex_of_monotoneDecompN` — the **complex slice** form: a
  function `s : ℝ → ℂ` whose real part `s.re = pr - qr` and imaginary part `s.im = pi - qi` are each
  such monotone-with-(N) differences is absolutely continuous on every interval (recombine the two
  real AC statements componentwise via `absolutelyContinuousOnInterval_of_re_im`).

## The reduction it powers

The keystone `ae_slice_ac_of_strip_setFunction_ac` asks for a.e.-slice absolute continuity. By the
complex packaging above, this is *equivalent* to the existence, for a.e. `y`, of the
continuous-monotone-with-(N) decomposition of the slice's real and imaginary parts
(`slice_monotoneDecompN_x_of_area` is the matching forward packaging in `ConditionNToACL.lean`). The
genuinely Mathlib-absent, irreducibly-two-dimensional content — the Federer/Marcus–Mizel co-area /
planar Lusin-(N) fact that *produces* the per-slice condition-(N) on the monotone pieces — is what
remains, isolated as the single residual `ae_slice_monotoneDecompN_x` below (precise TRUE `sorry`
with exact references). Every step *downstream* of that residual (the converse Banach–Zaretsky
packaging into honest absolute continuity) is fully proven here.
-/

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace RiemannDynamics

/-! ## The converse Banach–Zaretsky packaging: monotone-with-(N) ⟹ absolutely continuous -/

/-- **A continuous monotone map with condition (N) is absolutely continuous on every interval.**
This is the converse Banach–Zaretsky direction (Hencl–Koskela A.32), packaged into the
`AbsolutelyContinuousOnInterval` predicate. Condition (N) makes the Stieltjes measure absolutely
continuous (`monotone_absolutelyContinuous_of_luzinN`), so the FTC `f b - f a = ∫ₐᵇ deriv f` holds
on every interval (`monotone_ftc_of_luzinN`); thus `f` equals `f 0 + ∫₀ˣ deriv f`, the constant plus
the primitive of an interval-integrable function, which is AC. -/
theorem absolutelyContinuousOnInterval_of_monotoneN {f : ℝ → ℝ} (hf : Monotone f)
    (hcont : Continuous f)
    (hN : ∀ S : Set ℝ, volume S = 0 → volume (f '' S) = 0) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b := by
  -- `deriv f` is interval integrable (monotone derivative is interval integrable).
  have hderiv_II : ∀ a b : ℝ, IntervalIntegrable (deriv f) volume a b :=
    fun a b => MonotoneOn.intervalIntegrable_deriv (hf.monotoneOn (uIcc a b))
  -- The FTC identity from Banach–Zaretsky: `f x = f 0 + ∫₀ˣ deriv f` for all `x`.
  have hFTC : ∀ x : ℝ, f x = f 0 + ∫ t in (0 : ℝ)..x, deriv f t := by
    intro x
    have h := monotone_ftc_of_luzinN hf hcont hN 0 x
    linarith [h]
  -- The primitive `x ↦ ∫₀ˣ deriv f` is AC on every interval.
  have hprim : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, deriv f t) a b := by
    -- Enlarge to `uIcc (-n) n ⊇ {0} ∪ uIcc a b`, apply Mathlib's primitive-AC there, restrict.
    obtain ⟨n, hn⟩ := exists_nat_ge (max (|a|) (|b|))
    have h3 := le_max_left (|a|) (|b|)
    have h4 := le_max_right (|a|) (|b|)
    have ha : |a| ≤ n := by linarith
    have hb : |b| ≤ n := by linarith
    rw [abs_le] at ha hb
    have hN0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnn : -(n : ℝ) ≤ (n : ℝ) := by linarith
    have hz : (0 : ℝ) ∈ uIcc (-(n : ℝ)) n := by
      rw [Set.uIcc_of_le hnn]; exact ⟨by linarith, hN0⟩
    have hbig : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, deriv f t)
        (-(n : ℝ)) n :=
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (hderiv_II _ _) hz
    refine hbig.mono ?_
    rw [Set.uIcc_of_le hnn]
    intro t ht
    rw [Set.mem_uIcc] at ht
    rw [Set.mem_Icc]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  -- The constant `f 0` is AC.
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f 0) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    exact ⟨1, one_pos, fun E _ _ => by simpa using (by positivity : (0 : ℝ) < ε)⟩
  -- `f = const + primitive`, AC under addition.
  have heq : f = (fun _ : ℝ => f 0) + (fun x => ∫ t in (0 : ℝ)..x, deriv f t) := by
    funext x; simp [hFTC x]
  rw [heq]; exact hconst.add hprim

/-- **A difference of two continuous monotone maps with condition (N) is absolutely continuous.**
The hypothesis shape of the per-slice Jordan / Banach–Zaretsky decomposition: `f = p - q` with `p`,
`q` continuous monotone each carrying null sets to null sets. Each piece is AC
(`absolutelyContinuousOnInterval_of_monotoneN`); AC is closed under subtraction. -/
theorem absolutelyContinuousOnInterval_of_monotoneDecompN {f p q : ℝ → ℝ}
    (hp_mono : Monotone p) (hp_cont : Continuous p)
    (hq_mono : Monotone q) (hq_cont : Continuous q)
    (hpN : ∀ S : Set ℝ, volume S = 0 → volume (p '' S) = 0)
    (hqN : ∀ S : Set ℝ, volume S = 0 → volume (q '' S) = 0)
    (hfpq : f = p - q) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b := by
  have hpAC : AbsolutelyContinuousOnInterval p a b :=
    absolutelyContinuousOnInterval_of_monotoneN hp_mono hp_cont hpN a b
  have hqAC : AbsolutelyContinuousOnInterval q a b :=
    absolutelyContinuousOnInterval_of_monotoneN hq_mono hq_cont hqN a b
  rw [hfpq]; exact hpAC.sub hqAC

/-- Recombination of `re`/`im`: a `ℂ`-valued function whose real and imaginary slices are AC is AC.
(A local copy of the `ConditionNToACL` private lemma; this file is upstream of that file.) -/
private theorem absolutelyContinuousOnInterval_of_re_im {F : ℝ → ℂ} {a b : ℝ}
    (hre : AbsolutelyContinuousOnInterval (fun x => (F x).re) a b)
    (him : AbsolutelyContinuousOnInterval (fun x => (F x).im) a b) :
    AbsolutelyContinuousOnInterval F a b := by
  rw [absolutelyContinuousOnInterval_iff] at hre him ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hre (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h₂⟩ := him (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hE hlen => ?_⟩
  have hl1 : ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ₁ :=
    lt_of_lt_of_le hlen (min_le_left _ _)
  have hl2 : ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ₂ :=
    lt_of_lt_of_le hlen (min_le_right _ _)
  have k1 := h₁ E hE hl1
  have k2 := h₂ E hE hl2
  have hbound : ∀ i, dist (F (E.2 i).1) (F (E.2 i).2)
      ≤ dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
        + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
    intro i
    rw [Complex.dist_eq, Real.dist_eq, Real.dist_eq]
    calc ‖F (E.2 i).1 - F (E.2 i).2‖
        ≤ |(F (E.2 i).1 - F (E.2 i).2).re| + |(F (E.2 i).1 - F (E.2 i).2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(F (E.2 i).1).re - (F (E.2 i).2).re| + |(F (E.2 i).1).im - (F (E.2 i).2).im| := by
          rw [Complex.sub_re, Complex.sub_im]
  calc ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2)
      ≤ ∑ i ∈ Finset.range E.1, (dist ((F (E.2 i).1).re) ((F (E.2 i).2).re)
          + dist ((F (E.2 i).1).im) ((F (E.2 i).2).im)) :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).re) ((F (E.2 i).2).re))
        + ∑ i ∈ Finset.range E.1, dist ((F (E.2 i).1).im) ((F (E.2 i).2).im) := by
        rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add k1 k2
    _ = ε := by ring

/-- **The complex slice form: monotone-with-(N) decomposition of the components ⟹ absolute
continuity of the slice.** If `s : ℝ → ℂ` has `s.re = pr - qr` and `s.im = pi - qi`, each a
difference of continuous monotone functions satisfying condition (N), then `s` is absolutely
continuous on every interval. This is the exact converse Banach–Zaretsky packaging consumed by the
keystone slice-ACL residual: it transforms the per-slice decomposition (the natural output of the
co-area / Banach–Zaretsky engine) into genuine absolute continuity. -/
theorem absolutelyContinuousOnInterval_complex_of_monotoneDecompN {s : ℝ → ℂ}
    {pr qr pi qi : ℝ → ℝ}
    (hpr_mono : Monotone pr) (hpr_cont : Continuous pr)
    (hqr_mono : Monotone qr) (hqr_cont : Continuous qr)
    (hpi_mono : Monotone pi) (hpi_cont : Continuous pi)
    (hqi_mono : Monotone qi) (hqi_cont : Continuous qi)
    (hprN : ∀ S : Set ℝ, volume S = 0 → volume (pr '' S) = 0)
    (hqrN : ∀ S : Set ℝ, volume S = 0 → volume (qr '' S) = 0)
    (hpiN : ∀ S : Set ℝ, volume S = 0 → volume (pi '' S) = 0)
    (hqiN : ∀ S : Set ℝ, volume S = 0 → volume (qi '' S) = 0)
    (hre : (fun t => (s t).re) = pr - qr) (him : (fun t => (s t).im) = pi - qi)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval s a b := by
  refine absolutelyContinuousOnInterval_of_re_im ?_ ?_
  · exact absolutelyContinuousOnInterval_of_monotoneDecompN hpr_mono hpr_cont hqr_mono hqr_cont
      hprN hqrN hre a b
  · exact absolutelyContinuousOnInterval_of_monotoneDecompN hpi_mono hpi_cont hqi_mono hqi_cont
      hpiN hqiN him a b

/-! ## The slice-ACL coupling from the weak gradient (genuine `W^{1,1}` ⇒ slice AC)

The keystone slice-ACL conclusion — that for a.e. `y` the horizontal slice `t ↦ g ⟨t, y⟩` is
absolutely continuous on every interval — is the converse Sobolev embedding `W^{1,1}_loc ⇒ ACL`
(Nikodym; Evans–Gariepy §4.9.2). The genuine, load-bearing analytic input is that `gx` is the
**weak (distributional)** `x`-derivative of `g` (`HasWeakDirDeriv 1 gx g univ`), i.e. `g` is a
Sobolev map. This is **fully proven** below from that hypothesis, via Mathlib's converse-of-ACL
direction `exists_aclHorizontal_of_hasWeakDirDeriv_one` (an AC representative `g' =ᵐ g`) plus a
continuity transfer (`g` continuous, `g'`'s slice AC hence continuous, agreeing a.e. ⟹ everywhere).

### ⚠ Why the weak-derivative hypothesis is genuinely necessary (correctness fix, 2026-06-20)

This replaces a former **FALSE** residual that attempted to derive a.e.-slice AC from purely
*set-function* hypotheses about the swept area `Φ_{c,d}(I) := volume (g '' (I ×ℂ Icc c d))` (its
absolute continuity `hΦ_ac` plus the slice-Jacobian density bound `hΦ_density`) together with
injectivity and `L¹_loc` *pointwise* partials. That implication is **false**: those hypotheses
constrain only the **Jacobian / swept area**, never the off-diagonal *tangential* partial whose
distributional part may be singular. The decisive counterexample is the **area-preserving singular
shear**
`g ⟨x, y⟩ = x + i·(y + s x)`, with `s` a continuous strictly-increasing singular function (e.g.
Minkowski `?`): it is injective, continuous, a.e.-differentiable with `Dg = id` a.e., hence
**measure-preserving**, so `hΦ_ac` and `hΦ_density` both hold *with equality* and `gx = (1,0)` a.e.
is in `L¹_loc` — yet every horizontal slice's imaginary part `y + s ·` is **singular (not AC)**. The
honest extra ingredient is exactly that `gx` be the *weak* derivative (`g ∈ W^{1,1}_loc`), which the
shear fails (`∂ₓ(g.im) = ds` is a singular measure, not the a.e.-pointwise `0`). For the
quasiconformal inverse this holds genuinely via `MemW12loc` (`IsQCAnalytic.inverse_memW12loc`).

References: O. Nikodym; L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of
Functions*, §4.9; M. Marcus, V. J. Mizel, ARMA 45 (1972); S. Hencl, P. Koskela, *Lectures on
Mappings of Finite Distortion*, App. A. -/

/-- **a.e.-slice absolute continuity from the weak `x`-derivative** (`W^{1,1}_loc ⇒ ACL`,
horizontal). For a continuous map `g : ℂ → ℂ` with `L¹_loc` `x`-partial witness `gx` that is the
**weak (distributional)** `x`-derivative of `g` (`hweakx : HasWeakDirDeriv 1 gx g univ`), for almost
every `y` the horizontal slice `t ↦ g ⟨t, y⟩` is absolutely continuous on every interval.

**Fully proven**, axiom-clean: `exists_aclHorizontal_of_hasWeakDirDeriv_one` builds an AC-on-lines
representative `g' =ᵐ g`; on a.e. line `g`'s slice and `g'`'s slice are continuous and agree a.e.,
hence everywhere, so `g`'s own slice inherits the absolute continuity. The genuine analytic content
(`g ∈ W^{1,1}_loc`) is the hypothesis `hweakx`; see the section docstring for the correctness fix
(the former area-set-function residual was FALSE — refuted by the area-preserving singular
shear). -/
theorem ae_slice_ac_of_weakDirDeriv_x {g : ℂ → ℂ}
    (hgcont : Continuous g)
    {gx : ℂ → ℂ} (hgxLI : LocallyIntegrable gx)
    (hweakx : HasWeakDirDeriv 1 gx g Set.univ) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x : ℝ => g ⟨x, y⟩) a b := by
  have hgLI : LocallyIntegrable g := hgcont.locallyIntegrable
  -- An AC-on-horizontal-lines representative `g'`, equal to `g` a.e.
  obtain ⟨g', hg'ae, hg'acl⟩ :=
    exists_aclHorizontal_of_hasWeakDirDeriv_one hgLI hgxLI hweakx
  -- Continuity transfer: on a.e. line `g`'s slice and `g'`'s slice are continuous and agree a.e.,
  -- hence agree everywhere, so `g`'s slice inherits the absolute continuity.
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hae2 : (fun p : ℝ × ℝ => g' ⟨p.1, p.2⟩) =ᵐ[volume.prod volume]
      (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) := by
    rw [← Measure.volume_eq_prod]
    have := hmpsymm.quasiMeasurePreserving.ae_eq_comp hg'ae
    filter_upwards [this] with p hp
    simpa [Complex.measurableEquivRealProd_symm_apply] using hp
  have hslice_eq : ∀ᵐ y : ℝ,
      (fun x : ℝ => g' ⟨x, y⟩) =ᵐ[volume] (fun x : ℝ => g ⟨x, y⟩) := by
    have hswap : (fun p : ℝ × ℝ => g' ⟨p.2, p.1⟩) =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => g ⟨p.2, p.1⟩) := by
      have hh := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae_eq hae2
      simpa [Function.comp_def, Prod.swap] using hh
    exact Measure.ae_ae_eq_of_ae_eq_uncurry hswap
  have hsliceCont : ∀ y : ℝ, Continuous (fun x : ℝ => (⟨x, y⟩ : ℂ)) := by
    intro y
    have he : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I := by
      funext x; apply Complex.ext <;> simp
    rw [he]; exact Complex.continuous_ofReal.add continuous_const
  -- The AC-on-lines property of `g'` (discard the line-derivative half).
  have hg'ac : ∀ᵐ y : ℝ, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun x : ℝ => g' ⟨x, y⟩) a b := by
    filter_upwards [hg'acl] with y hy; exact hy.1
  filter_upwards [hg'ac, hslice_eq] with y hac' hy_eq
  set s  : ℝ → ℂ := fun x => g ⟨x, y⟩ with hs
  set s' : ℝ → ℂ := fun x => g' ⟨x, y⟩ with hs'
  have hcont_s : Continuous s := hgcont.comp (hsliceCont y)
  have hcont_s' : Continuous s' := by
    rw [continuous_iff_continuousAt]
    intro x
    have hco := (hac' (x - 1) (x + 1)).continuousOn
    rw [Set.uIcc_of_le (by linarith)] at hco
    exact (hco x ⟨by linarith, by linarith⟩).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have heq : s' = s := (hcont_s'.ae_eq_iff_eq (μ := volume) hcont_s).mp hy_eq
  intro a b; rw [← heq]; exact hac' a b

end RiemannDynamics
