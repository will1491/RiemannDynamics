/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.QC.Regularity.Grotzsch
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Quasisymmetry and equicontinuity of quasiconformal maps

This file derives the two **regularity outputs** that the curve-approximation lemma
`Quadrilateral.exists_imageCurveFamily_approx` (in `QC/LengthArea/ModulusLSC.lean`) consumes from
the quasiconformal-regularity layer:

* **(Q) Quasisymmetry**: a geometric `K`-quasiconformal map is `η`-quasisymmetric for a control
  function `η` depending only on `K`. Quantitatively, for all triples of distinct points,
  `dist (f a) (f b) / dist (f a) (f c) ≤ η (dist a b / dist a c)`.
* **(E) Equicontinuity / normal family**: a uniformly `K`-quasiconformal, suitably normalized
  family `{fₙ}` and its inverses `{fₙ⁻¹}` are equicontinuous on every compact set, with a modulus
  of continuity depending only on `K` and the set.

Both follow from the Teichmüller comparison
`teichmullerModulus_le_ringModulus_separating_two_pairs` together with the modulus-distortion
inequality that *defines* `IsQCGeometric f K`. Every statement is a true
classical theorem (Väisälä §§10–22, Lehto–Virtanen Ch. II–III, Ahlfors Ch. III) and **fails for
bare homeomorphisms** — the `IsQCGeometric`/`uniformly K-qc` hypothesis is load-bearing throughout,
and no statement assumes any derivative control.

The final lemma `exists_rectifiableConnector_uniform` is the *consumable approximation support*: in
the image set `f '' Q.image` of a uniformly `K`-quasiconformal family, any two points within `ε` are
joined by a rectifiable arc inside the set of length `≤ ω K ε`, with `ω K ε → 0` as `ε → 0`,
*uniformly in the family*. This is exactly the geometric input the absolutely-continuous-curve
construction in `exists_imageCurveFamily_approx` is built on.

## Main definitions

* `IsQuasisymmetricWith f η` — `f` is `η`-quasisymmetric with control function `η`.

## Main statements (all `sorry`)

* `exists_quasisymmetric_of_isQCGeometric` — **(Q)**: `IsQCGeometric f K` gives an `η` depending
  only on `K` with `IsQuasisymmetricWith f η`;
* `isQCGeometric_inv_of_isQCGeometric` — the inverse of a geometric `K`-qc map is geometric `K`-qc;
* `equicontinuousOn_of_uniform_isQCGeometric` — **(E)**: a normalized uniformly `K`-qc family is
  equicontinuous on compacta;
* `equicontinuousOn_inv_of_uniform_isQCGeometric` — the inverses are equicontinuous on compacta;
* `exists_rectifiableConnector_uniform` — the uniform short-rectifiable-connector lemma feeding
  `exists_imageCurveFamily_approx`.

## References

* J. Väisälä, *Lectures on n-dimensional quasiconformal mappings*, §§10 (quasisymmetry), 19–21
  (distortion and equicontinuity).
* O. Lehto and K. I. Virtanen, *Quasiconformal mappings in the plane*, Ch. II §6, Ch. III.
* L. V. Ahlfors, *Lectures on quasiconformal mappings*, Ch. III §C.
-/

open MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace RiemannDynamics

/-- A map `f : ℂ → ℂ` is **`η`-quasisymmetric** with control function `η : ℝ → ℝ` (monotone,
`η t → 0` as `t → 0`) when it distorts relative distances by `η`: for all triples `a, b, c` with
`a ≠ c`,

`dist (f a) (f b) / dist (f a) (f c) ≤ η (dist a b / dist a c)`.

This is the metric (as opposed to conformal-modulus) formulation of quasiconformality. The control
function carries the *quantitative* distortion; for the quasiconformal-regularity layer the key fact
is that `η` can be taken to depend only on the constant `K`. -/
def IsQuasisymmetricWith (f : ℂ → ℂ) (η : ℝ → ℝ) : Prop :=
  Monotone η ∧ Tendsto η (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    ∀ a b c : ℂ, a ≠ c → dist (f a) (f b) / dist (f a) (f c) ≤ η (dist a b / dist a c)

/-- **The inverse of a geometric `K`-quasiconformal map is geometric `K`-quasiconformal.** Since
`IsQCGeometric f K` is the symmetric modulus-distortion condition (the image-family modulus is used,
which for the homeomorphism `f⁻¹` recovers `M(f⁻¹(Q')) ≤ K · M(Q')` for every quadrilateral `Q'`),
the inverse homeomorphism `g = f⁻¹` is again geometric `K`-qc. Needed so that the equicontinuity of
the inverses `{fₙ⁻¹}` is an instance of the equicontinuity of a uniformly `K`-qc family. -/
theorem isQCGeometric_inv_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    IsQCGeometric (hf.2.1.isHomeomorph.homeomorph f).symm K := by
  sorry

/-- **(Q) Quasisymmetry of a geometric quasiconformal map, with `K`-only control.** A geometric
`K`-quasiconformal map `f` is `η`-quasisymmetric for some control function `η` that depends only on
`K` (not on `f`). The dependence on `K` alone is the crucial uniformity: it is what makes a
*uniformly* `K`-quasiconformal family equicontinuous.

The proof is the classical reduction to the Teichmüller comparison: given `a, b, c`, the map `f`
sends the ring separating the pair `{f a, f b}` from `{f c, ∞}` to a ring of comparable modulus
(distortion by `K`, from `IsQCGeometric`); applying
`teichmullerModulus_le_ringModulus_separating_two_pairs` and the modulus blow-up
`exists_teichmullerModulus_lower_bound` bound `dist (f a) (f b) / dist (f a) (f c)`
by a function of `K · (something in dist a b / dist a c)`. This statement is **false for a bare
homeomorphism** (no such uniform `η` exists), so the `IsQCGeometric f K` hypothesis is essential; it
asserts no derivative control. -/
theorem exists_quasisymmetric_of_isQCGeometric {f : ℂ → ℂ} {K : ℝ} (hf : IsQCGeometric f K) :
    ∃ η : ℝ → ℝ, IsQuasisymmetricWith f η ∧
      ∀ {g : ℂ → ℂ}, IsQCGeometric g K → IsQuasisymmetricWith g η := by
  sorry

/-- **(E) Equicontinuity of a normalized uniformly `K`-quasiconformal family.** Let `{fₙ}` be a
family of geometric `K`-quasiconformal maps that is *normalized* on a compact set `S`: there are
points `p ≠ q` of `S` and a constant `M` with `dist (fₙ p) (fₙ q) ≤ M` and `δ ≤ dist (fₙ p) (fₙ q)`
for all `n` (a two-point normalization bounding the family's scale above and below). Then `{fₙ}` is
equicontinuous on `S`, with a modulus of continuity depending only on `K`, `S`, `M`, `δ`.

Some normalization is unavoidable: without it `fₙ = n · id` is uniformly `1`-quasiconformal yet not
equicontinuous. Under the two-point normalization, quasisymmetry with `K`-only control function `η`
(`exists_quasisymmetric_of_isQCGeometric`) converts the fixed scale `dist (fₙ p) (fₙ q) ∈ [δ, M]`
into a uniform Hölder/modulus-of-continuity estimate on `S`. False for bare homeomorphisms; no
derivative control assumed. -/
theorem equicontinuousOn_of_uniform_isQCGeometric {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {δ M : ℝ} (hδ : 0 < δ)
    (hlb : ∀ i, δ ≤ dist (f i p) (f i q)) (hub : ∀ i, dist (f i p) (f i q) ≤ M) :
    EquicontinuousOn f S := by
  sorry

/-- **Equicontinuity of the inverses of a normalized uniformly `K`-quasiconformal family.** Under
the same two-point normalization, the inverse family `{fₙ⁻¹}` is equicontinuous on every compact set
`T` contained in the common image scale. Combined with `equicontinuousOn_of_uniform_isQCGeometric`
this is the full **normal-family bound (E)**: both the maps and their inverses are equicontinuous on
compacta, the input to extracting locally uniformly convergent subsequences with homeomorphic
limits. Proved by applying `equicontinuousOn_of_uniform_isQCGeometric` to the family of inverses,
which are geometric `K`-quasiconformal by `isQCGeometric_inv_of_isQCGeometric`. -/
theorem equicontinuousOn_inv_of_uniform_isQCGeometric {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K)
    (g : ι → ℂ → ℂ)
    (hg : ∀ i, Function.LeftInverse (g i) (f i) ∧ Function.RightInverse (g i) (f i))
    {S : Set ℂ} (hS : IsCompact S)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    {δ M : ℝ} (hδ : 0 < δ)
    (hlb : ∀ i, δ ≤ dist (f i p) (f i q)) (hub : ∀ i, dist (f i p) (f i q) ≤ M)
    {T : Set ℂ} (hT : IsCompact T) :
    EquicontinuousOn g T := by
  sorry

/-- **Uniform short-rectifiable-connector lemma (the consumable approximation support).** Let `{fₙ}`
be a family of geometric `K`-quasiconformal maps and `Q` a quadrilateral. There is a modulus
function `ω : ℝ → ℝ` with `ω ε → 0` as `ε → 0⁺`, depending only on `K` (and the geometry of `Q`),
such that for every `n` and any two points `u, v` in the image region `f n '' Q.image` with
`dist u v ≤ ε`, there is a rectifiable (finite-variation) arc inside `f n '' Q.image` joining `u` to
`v` whose total length is at most `ω ε`. The arc is realized as an absolutely continuous curve
`c : ℝ → ℂ` on `[0,1]` with `c 0 = u`, `c 1 = v`, staying in `f n '' Q.image`.

This is precisely the geometric mechanism behind `Quadrilateral.exists_imageCurveFamily_approx`: to
approximate an absolutely continuous curve in the `g`-image family by absolutely continuous curves
in the `fₙ`-image families, one replaces each chord of a fine polygonal inscription by such a short
rectifiable connector; uniform smallness of `ω` makes the approximants converge uniformly and keeps
them absolutely continuous. The uniform `K`-quasiconformality is essential — for bare
homeomorphisms the image region may contain no short rectifiable cross-cuts (an Osgood-type wild
crumpling), and the lemma is false. No derivative control is assumed: the connector is built by
quasiconformal transport
of a straight segment in the model square, controlled metrically through quasisymmetry. -/
theorem exists_rectifiableConnector_uniform {ι : Type*} {f : ι → ℂ → ℂ} {K : ℝ}
    (hfK : ∀ i, IsQCGeometric (f i) K) (Q : Quadrilateral) :
    ∃ ω : ℝ → ℝ, Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ (i : ι) (ε : ℝ), 0 < ε → ∀ u ∈ f i '' Q.image, ∀ v ∈ f i '' Q.image,
        dist u v ≤ ε →
        ∃ c : ℝ → ℂ, Continuous c ∧ AbsolutelyContinuousOnInterval c 0 1 ∧
          c 0 = u ∧ c 1 = v ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, c t ∈ f i '' Q.image) ∧
          arcLengthLineIntegral (fun _ => 1) c ≤ ENNReal.ofReal (ω ε) := by
  sorry

end RiemannDynamics
