/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Analysis.GrotzschRing.SequentialIBP.TruncatedFlux

/-!
# Planar level-set nullity and the truncated-flux keystone slope bound

This is the last of the four `SequentialIBP` files; it imports `SequentialIBP.TruncatedFlux` and
defines nothing new. Its first half shows that for `u` harmonic on an open `U ⊆ ℂ` whose holomorphic
gradient `gradC u` is nowhere locally identically zero, every level set `{z ∈ U | u z = δ}` is
planar-null, and hence that for a.e. log-radius `ξ` the angular slice of that level set is
one-dimensionally null. Its second half spends that nullity: it is what makes the radial derivative
of the windowed truncated integrand exist off the level set, so the truncated rough flux
`truncRoughFlux u U δ` — Lipschitz in `ξ`, hence absolutely continuous — satisfies a fundamental
theorem of calculus whose derivative is the superlevel-slice energy. Integrating that FTC bounds the
truncated-flux increment by the total Dirichlet energy, and letting `δ → 0` transfers the bound to
`roughFlux`, discharging the windowed-increment hypothesis of `slope_le_energy_ringPotential'` and
producing the keystone `slope_le_energy_ringPotential'''` used in `GrotzschRing.GrotzschKeystone`.

## Main results

* `RiemannDynamics.gradC_zeroSet_null` — for `u` harmonic on an open `U` whose holomorphic gradient
  `gradC u` is nowhere locally identically zero (`∀ z ∈ U, ¬ ∀ᶠ w in 𝓝 z, gradC u w = 0`), the
  critical set `{z ∈ U | gradC u z = 0}` has planar measure zero: `gradC u` is analytic on `U`, so
  by the identity principle its zero set is discrete, hence countable.
* `RiemannDynamics.levelSet_volume_zero` — under the same three hypotheses (`U` open, `u` harmonic
  on a neighbourhood of each point of `U`, `gradC u` nowhere locally zero), *every* level set
  `{z ∈ U | u z = δ}`, at every real level `δ`, has planar measure zero. The third hypothesis is
  load-bearing: were `u` constant on a nonempty open piece of `U`, one level set would be non-null.
* `RiemannDynamics.ae_angularSlice_levelSet_null` — if `{z ∈ U | u z = δ}` is measurable and
  planar-null (no harmonicity is used here), then for a.e. `ξ : ℝ` the angular slice
  `{θ ∈ (−π, π) | e^{ξ+θi} ∈ U ∧ u (e^{ξ+θi}) = δ}` is one-dimensionally null. Log-polar
  coordinates rewrite the vanishing planar integral as an iterated integral in `(ξ, θ)`.
* `RiemannDynamics.hasDerivAt_windowedTruncIntegrand_radial` — for `u` harmonic on the open `U`
  with `closure (superLevelU U u δ ∩ {e^{ζ₁} < |z| < e^{ζ₂}}) ⊆ U`, at any `ξ ∈ (ζ₁, ζ₂)` and
  `θ ∈ [−π, π]` for which `e^{ξ+θi} ∈ U` forces `u (e^{ξ+θi}) ≠ δ`, the radial line map
  `x ↦ windowedTruncIntegrand u U δ (x + θi)` is differentiable at `ξ`; the derivative is
  `(Re (expGrad u))² + (u ∘ exp − δ) · Re (deriv (expGrad u))` when `θ` is in the superlevel slice
  at `ξ`, and `0` otherwise.
* `RiemannDynamics.lipschitzOnWith_truncRoughFlux` — for `u` harmonic on the open `U`, continuous on
  `closure U` and vanishing at every point of `frontier U` of norm `< 1`, and for `0 < δ` and
  `ζ₁ ≤ ζ₂ < 0`, some constant makes `truncRoughFlux u U δ` Lipschitz on `uIcc ζ₁ ζ₂`. The
  hypotheses `δ > 0` and `ζ₂ < 0` are what confine the superlevel window compactly inside `U`.
* `RiemannDynamics.hasDerivAt_truncRoughFlux_of_slice_null` — with that same boundary data, plus
  continuity of `θ ↦ u (e^{ξ+θi})` at this `ξ`, integrability of `|expGrad u|²` on the δ-slice
  `angularSliceδ U u δ ξ`, `0 < δ`, `ζ₂ < 0`, `ξ ∈ (ζ₁, ζ₂)`, and nullity of the `ξ`-angular slice
  of `{u = δ}`, the flux `truncRoughFlux u U δ` has derivative
  `sliceEnergyU u (superLevelU U u δ) ξ` at `ξ`. That last hypothesis is exactly what
  `ae_angularSlice_levelSet_null` supplies for a.e. `ξ`.
* `RiemannDynamics.truncRoughFlux_sub_le_dirichletEnergy` — for `u` harmonic on the open `U` with
  `gradC u` nowhere locally zero, `θ ↦ u (e^{ξ+θi})` continuous for every `ξ`, `u` continuous on
  `closure U` and vanishing on `frontier U` inside the unit disc, `|expGrad u|²` integrable on every
  δ-slice, and `dirichletEnergy u U ≠ ⊤`, every `δ > 0` and window `ζ₁ ≤ ζ₂ < 0` satisfy
  `truncRoughFlux u U δ ζ₂ − truncRoughFlux u U δ ζ₁ ≤ (dirichletEnergy u U).toReal`.
* `RiemannDynamics.roughFlux_sub_le_dirichletEnergy_trunc` — adding `0 < u` on `U`, `0 ≤ u ≤ 1` on
  `U`, and integrability of `|expGrad u|²` on the *full* slice `angularSlice U ξ`, the `δ → 0` limit
  gives the untruncated bound `roughFlux u U ζ₂ − roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal`
  for all `ζ₁ ≤ ζ₂ < 0`. This is the windowed increment inequality `slope_le_energy_ringPotential'`
  asks for.
* `RiemannDynamics.slope_le_energy_ringPotential'''` — the file's only export used outside
  `SequentialIBP` (twice, in `GrotzschRing.GrotzschKeystone`). For `0 < r₀ < 1` and `u` harmonic,
  strictly positive, `0 ≤ u ≤ 1` and nowhere locally gradient-constant on the open `U`, continuous
  on `closure U`, vanishing on `frontier U` inside the unit disc, with `|expGrad u|²` integrable on
  every full slice, `dirichletEnergy u U ≠ ⊤`, the collar `{r₀ < |z| < 1}` contained in `U`, `u`
  harmonic on `RoundAnnulus 0 r₀ 1`, continuous with values in `[0, 1]` on the closed annulus
  `r₀ ≤ |z| ≤ 1`, equal to `1` on `grotzschOuter`, and `logCircleMean 0 u ξ = 2 * π + b * ξ` for
  `ξ ∈ (log r₀, 0)`, the slope satisfies `b ≤ (dirichletEnergy u U).toReal`.
-/

namespace RiemannDynamics

open MeasureTheory intervalIntegral Filter Set
open scoped Real ENNReal Topology
open Complex

/-! ### The planar level-set nullity of a nonconstant harmonic potential

For `u` harmonic on the open set `U`, its level set `{z ∈ U | u z = δ}` at any level `δ` has planar
measure zero, provided `u` is nowhere locally constant on `U` (equivalently, its holomorphic
gradient `gradC u` is nowhere locally identically zero).  The proof splits the level set at the
critical set `{gradC u = 0}`: the critical set is the zero set of the holomorphic `gradC u`, hence
discrete (its zeros are isolated by the identity principle) and countable, so null; off the critical
set one of the two partials is nonzero, so near each such point `u` is strictly monotone along a
coordinate axis and the level set meets each axis-parallel line in at most one point — a graph, null
by Fubini. -/

/-- **Nullity of the critical set of a nowhere-locally-constant harmonic potential.** For `u`
harmonic on the open set `U` with `gradC u` nowhere locally identically zero on `U`, the critical
set `{z ∈ U | gradC u z = 0}` has planar measure zero: it is the zero set of the holomorphic
`gradC u`, whose zeros are isolated (identity principle), so it is discrete, countable and null. -/
theorem gradC_zeroSet_null {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0)) :
    volume {z : ℂ | z ∈ U ∧ gradC u z = 0} = 0 := by
  set Z : Set ℂ := {z : ℂ | z ∈ U ∧ gradC u z = 0} with hZ
  have hanal : AnalyticOnNhd ℂ (gradC u) U := (gradC_differentiableOn hu).analyticOnNhd hU
  have hdisc : DiscreteTopology Z := by
    apply discreteTopology_of_noAccPts
    intro z hz hacc
    have hzU : z ∈ U := hz.1
    have hfreq : ∃ᶠ w in 𝓝[≠] z, gradC u w = 0 :=
      (accPt_iff_frequently_nhdsNE.mp hacc).mono (fun w hw => hw.2)
    rcases (hanal z hzU).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact hnc z hzU hzero
    · rcases (hne.and_frequently hfreq).exists with ⟨w, hw1, hw2⟩
      exact hw1 hw2
  have hcount : Z.Countable :=
    (HereditarilyLindelofSpace.isLindelof Z).countable hdisc
  exact hcount.measure_zero volume

/-- A measurable planar set all of whose vertical slices `{y | x + y·i ∈ S}` are subsingletons has
planar measure zero: transporting to `ℝ × ℝ` (`Complex.volume_preserving_equiv_real_prod`) and
applying `Measure.prod_apply`, each fibre has one-dimensional measure zero. -/
theorem volume_eq_zero_of_subsingleton_vertical_slice {S : Set ℂ} (hmeas : MeasurableSet S)
    (hslice : ∀ x : ℝ, {y : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S}.Subsingleton) :
    volume S = 0 := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  set S' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd '' S with hS'
  have hS'meas : MeasurableSet S' :=
    Complex.measurableEquivRealProd.measurableEmbedding.measurableSet_image.mpr hmeas
  have hvol : volume S = volume S' := by
    rw [hS', ← hmp.measure_preimage hS'meas.nullMeasurableSet,
      Set.preimage_image_eq _ Complex.measurableEquivRealProd.injective]
  rw [hvol, Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply hS'meas]
  have hz : ∀ x : ℝ, (volume : Measure ℝ) (Prod.mk x ⁻¹' S') = 0 := by
    intro x
    have hsub : (Prod.mk x ⁻¹' S') = {y : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S} := by
      ext y
      simp only [Set.mem_preimage, hS', Set.mem_image, mem_setOf_eq]
      constructor
      · rintro ⟨z, hzS, hz⟩
        have : z = (x : ℂ) + (y : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp_all [Complex.measurableEquivRealProd_apply, Prod.ext_iff]
        rwa [this] at hzS
      · intro hy
        exact ⟨(x : ℂ) + (y : ℂ) * Complex.I, hy, by simp [Complex.measurableEquivRealProd_apply]⟩
    rw [hsub]; exact (hslice x).measure_zero volume
  simp only [hz, lintegral_zero]

/-- A measurable planar set all of whose horizontal slices `{x | x + y·i ∈ S}` are subsingletons has
planar measure zero (the `Prod.swap` variant of `volume_eq_zero_of_subsingleton_vertical_slice`). -/
theorem volume_eq_zero_of_subsingleton_horizontal_slice {S : Set ℂ} (hmeas : MeasurableSet S)
    (hslice : ∀ y : ℝ, {x : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S}.Subsingleton) :
    volume S = 0 := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  set S' : Set (ℝ × ℝ) := Complex.measurableEquivRealProd '' S with hS'
  have hS'meas : MeasurableSet S' :=
    Complex.measurableEquivRealProd.measurableEmbedding.measurableSet_image.mpr hmeas
  have hvol : volume S = volume S' := by
    rw [hS', ← hmp.measure_preimage hS'meas.nullMeasurableSet,
      Set.preimage_image_eq _ Complex.measurableEquivRealProd.injective]
  rw [hvol, Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply_symm hS'meas]
  have hz : ∀ y : ℝ, (volume : Measure ℝ) ((fun x => (x, y)) ⁻¹' S') = 0 := by
    intro y
    have hsub : ((fun x => (x, y)) ⁻¹' S') = {x : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S} := by
      ext x
      simp only [Set.mem_preimage, hS', Set.mem_image, mem_setOf_eq]
      constructor
      · rintro ⟨z, hzS, hz⟩
        have : z = (x : ℂ) + (y : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp_all [Complex.measurableEquivRealProd_apply, Prod.ext_iff]
        rwa [this] at hzS
      · intro hx
        exact ⟨(x : ℂ) + (y : ℂ) * Complex.I, hx, by simp [Complex.measurableEquivRealProd_apply]⟩
    rw [hsub]; exact (hslice y).measure_zero volume
  simp only [hz, lintegral_zero]

/-- On an open rectangle `{re ∈ (a₁, a₂), im ∈ (b₁, b₂)}` on which `u` is differentiable with
nonvanishing vertical partial `(fderiv ℝ u) I`, each vertical line meets the level set `{u = δ}` in
at most one point of the rectangle: two such points would, by Rolle's theorem, force the vertical
partial to vanish between them. -/
theorem subsingleton_vertical_slice_of_deriv_ne {u : ℂ → ℝ} {δ a₁ a₂ b₁ b₂ : ℝ}
    (hdiff : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → DifferentiableAt ℝ u z)
    (hne : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → (fderiv ℝ u z) Complex.I ≠ 0)
    (x : ℝ) :
    {y : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ ∧
      ((x : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ ∧
      u ((x : ℂ) + (y : ℂ) * Complex.I) = δ}.Subsingleton := by
  have hre : ∀ s : ℝ, ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by intro s; simp
  have him : ∀ s : ℝ, ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by intro s; simp
  have hcore : ∀ y1 y2 : ℝ, y1 < y2 →
      ((x : ℂ) + (y1 : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ →
      ((x : ℂ) + (y1 : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ →
      u ((x : ℂ) + (y1 : ℂ) * Complex.I) = δ →
      ((x : ℂ) + (y2 : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ →
      u ((x : ℂ) + (y2 : ℂ) * Complex.I) = δ → False := by
    intro y1 y2 hlt hx1 hy1i hgy1 hy2i hgy2
    set g : ℝ → ℝ := fun s => u ((x : ℂ) + (s : ℂ) * Complex.I) with hg
    have hIcc : Icc y1 y2 ⊆ Ioo b₁ b₂ := by
      rw [him] at hy1i hy2i
      exact fun s hs => ⟨lt_of_lt_of_le hy1i.1 hs.1, lt_of_le_of_lt hs.2 hy2i.2⟩
    have hdg : ∀ s ∈ Icc y1 y2,
        HasDerivAt g ((fderiv ℝ u ((x : ℂ) + (s : ℂ) * Complex.I)) Complex.I) s := by
      intro s hs
      have hsre : ((x : ℂ) + (s : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by
        rw [hre]; rw [hre] at hx1; exact hx1
      have hsim : ((x : ℂ) + (s : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by rw [him]; exact hIcc hs
      have hline : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I s := by
        have h := (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
        simpa using (h.const_add (x : ℂ))
      simpa using (hdiff _ hsre hsim).hasFDerivAt.comp_hasDerivAt s hline
    have hcont : ContinuousOn g (Icc y1 y2) :=
      fun s hs => (hdg s hs).continuousAt.continuousWithinAt
    have hends : g y1 = g y2 := by rw [hg]; simp only []; rw [hgy1, hgy2]
    obtain ⟨c, hc, hderiv⟩ :=
      exists_hasDerivAt_eq_zero hlt hcont hends (fun s hs => hdg s ⟨hs.1.le, hs.2.le⟩)
    have hcre : ((x : ℂ) + (c : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by
      rw [hre]; rw [hre] at hx1; exact hx1
    have hcim : ((x : ℂ) + (c : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by
      rw [him]; exact hIcc ⟨hc.1.le, hc.2.le⟩
    exact hne _ hcre hcim hderiv
  intro y1 hy1 y2 hy2
  obtain ⟨hx1, hy1i, hgy1⟩ := hy1
  obtain ⟨hx2, hy2i, hgy2⟩ := hy2
  rcases lt_trichotomy y1 y2 with hlt | heq | hgt
  · exact absurd (hcore y1 y2 hlt hx1 hy1i hgy1 hy2i hgy2) (by simp)
  · exact heq
  · exact absurd (hcore y2 y1 hgt hx2 hy2i hgy2 hy1i hgy1) (by simp)

/-- On an open rectangle `{re ∈ (a₁, a₂), im ∈ (b₁, b₂)}` on which `u` is differentiable with
nonvanishing horizontal partial `(fderiv ℝ u) 1`, each horizontal line meets the level set `{u = δ}`
in at most one point of the rectangle. -/
theorem subsingleton_horizontal_slice_of_deriv_ne {u : ℂ → ℝ} {δ a₁ a₂ b₁ b₂ : ℝ}
    (hdiff : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → DifferentiableAt ℝ u z)
    (hne : ∀ z : ℂ, z.re ∈ Ioo a₁ a₂ → z.im ∈ Ioo b₁ b₂ → (fderiv ℝ u z) 1 ≠ 0)
    (y : ℝ) :
    {x : ℝ | ((x : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ ∧
      ((x : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ ∧
      u ((x : ℂ) + (y : ℂ) * Complex.I) = δ}.Subsingleton := by
  have hre : ∀ s : ℝ, ((s : ℂ) + (y : ℂ) * Complex.I).re = s := by intro s; simp
  have him : ∀ s : ℝ, ((s : ℂ) + (y : ℂ) * Complex.I).im = y := by intro s; simp
  have hcore : ∀ x1 x2 : ℝ, x1 < x2 →
      ((x1 : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ →
      ((x1 : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ →
      u ((x1 : ℂ) + (y : ℂ) * Complex.I) = δ →
      ((x2 : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ →
      u ((x2 : ℂ) + (y : ℂ) * Complex.I) = δ → False := by
    intro x1 x2 hlt hx1i hyi hgx1 hx2i hgx2
    set g : ℝ → ℝ := fun s => u ((s : ℂ) + (y : ℂ) * Complex.I) with hg
    have hIcc : Icc x1 x2 ⊆ Ioo a₁ a₂ := by
      rw [hre] at hx1i hx2i
      exact fun s hs => ⟨lt_of_lt_of_le hx1i.1 hs.1, lt_of_le_of_lt hs.2 hx2i.2⟩
    have hdg : ∀ s ∈ Icc x1 x2,
        HasDerivAt g ((fderiv ℝ u ((s : ℂ) + (y : ℂ) * Complex.I)) 1) s := by
      intro s hs
      have hsre : ((s : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by rw [hre]; exact hIcc hs
      have hsim : ((s : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by
        rw [him]; rw [him] at hyi; exact hyi
      have hline : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I) 1 s := by
        have h := Complex.ofRealCLM.hasDerivAt (x := s)
        simpa using (h.add_const ((y : ℂ) * Complex.I))
      simpa using (hdiff _ hsre hsim).hasFDerivAt.comp_hasDerivAt s hline
    have hcont : ContinuousOn g (Icc x1 x2) :=
      fun s hs => (hdg s hs).continuousAt.continuousWithinAt
    have hends : g x1 = g x2 := by rw [hg]; simp only []; rw [hgx1, hgx2]
    obtain ⟨c, hc, hderiv⟩ :=
      exists_hasDerivAt_eq_zero hlt hcont hends (fun s hs => hdg s ⟨hs.1.le, hs.2.le⟩)
    have hcre : ((c : ℂ) + (y : ℂ) * Complex.I).re ∈ Ioo a₁ a₂ := by
      rw [hre]; exact hIcc ⟨hc.1.le, hc.2.le⟩
    have hcim : ((c : ℂ) + (y : ℂ) * Complex.I).im ∈ Ioo b₁ b₂ := by
      rw [him]; rw [him] at hyi; exact hyi
    exact hne _ hcre hcim hderiv
  intro x1 hx1 x2 hx2
  obtain ⟨hx1i, hyi, hgx1⟩ := hx1
  obtain ⟨hx2i, _, hgx2⟩ := hx2
  rcases lt_trichotomy x1 x2 with hlt | heq | hgt
  · exact absurd (hcore x1 x2 hlt hx1i hyi hgx1 hx2i hgx2) (by simp)
  · exact heq
  · exact absurd (hcore x2 x1 hgt hx2i hyi hgx2 hx1i hgx1) (by simp)

/-- Every point of an open set has an open axis-parallel rectangle neighbourhood contained in it:
the rectangles `{re ∈ (a₁, a₂), im ∈ (b₁, b₂)}` form a neighbourhood basis of `ℂ`. -/
theorem exists_rect_subset_of_isOpen {W : Set ℂ} (hW : IsOpen W) {z0 : ℂ} (hz0 : z0 ∈ W) :
    ∃ a₁ a₂ b₁ b₂ : ℝ, z0.re ∈ Ioo a₁ a₂ ∧ z0.im ∈ Ioo b₁ b₂ ∧
      {z : ℂ | z.re ∈ Ioo a₁ a₂ ∧ z.im ∈ Ioo b₁ b₂} ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW z0 hz0
  refine ⟨z0.re - ε / 2, z0.re + ε / 2, z0.im - ε / 2, z0.im + ε / 2,
    ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  intro z hz
  apply hball
  rw [Metric.mem_ball, Complex.dist_eq]
  obtain ⟨⟨hzr1, hzr2⟩, ⟨hzi1, hzi2⟩⟩ := hz
  have hre : |z.re - z0.re| < ε / 2 := by rw [abs_lt]; constructor <;> linarith
  have him : |z.im - z0.im| < ε / 2 := by rw [abs_lt]; constructor <;> linarith
  calc ‖z - z0‖ ≤ |(z - z0).re| + |(z - z0).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - z0.re| + |z.im - z0.im| := by simp [Complex.sub_re, Complex.sub_im]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Planar level-set nullity of a nowhere-locally-constant harmonic potential.** For `u` harmonic
on the open set `U` with `gradC u` nowhere locally identically zero on `U`, every level set
`{z ∈ U | u z = δ}` has planar measure zero.  Split it at the critical set `{gradC u = 0}` (null
by `gradC_zeroSet_null`); off the critical set one partial `∂_x u` or `∂_y u` is nonzero, so on an
open rectangle around each such point (`exists_rect_subset_of_isOpen`) the level set meets each
axis-parallel line in at most one point (`subsingleton_{vertical,horizontal}_slice_of_deriv_ne`),
hence is null by Fubini (`volume_eq_zero_of_subsingleton_{vertical,horizontal}_slice`).  A countable
subcover (`TopologicalSpace.isOpen_biUnion_countable`) of these rectangles covers the off-critical
part, so it too is null. -/
theorem levelSet_volume_zero {u : ℂ → ℝ} {U : Set ℂ} {δ : ℝ} (hU : IsOpen U)
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0)) :
    volume {z : ℂ | z ∈ U ∧ u z = δ} = 0 := by
  classical
  set L : Set ℂ := {z : ℂ | z ∈ U ∧ u z = δ} with hL
  have hucont : ContinuousOn u U := hu.continuousOn
  -- L measurable
  have hLmeas : MeasurableSet L := by
    have hopen : IsOpen (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) :=
      hucont.isOpen_inter_preimage hU isOpen_ne
    have : L = U \ (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) := by
      ext z; simp only [hL, mem_setOf_eq, mem_diff, mem_inter_iff, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨hzU, hzδ⟩; exact ⟨hzU, fun h => h.2 hzδ⟩
      · rintro ⟨hzU, hne⟩; exact ⟨hzU, not_not.mp (fun h => hne ⟨hzU, h⟩)⟩
    rw [this]; exact hU.measurableSet.diff hopen.measurableSet
  -- split at critical set
  set Zc : Set ℂ := {z : ℂ | z ∈ U ∧ gradC u z = 0} with hZc
  set G : Set ℂ := {z : ℂ | z ∈ U ∧ u z = δ ∧ gradC u z ≠ 0} with hG
  have hLsplit : L ⊆ Zc ∪ G := by
    intro z hz
    obtain ⟨hzU, hzδ⟩ := hz
    by_cases hg : gradC u z = 0
    · exact Or.inl ⟨hzU, hg⟩
    · exact Or.inr ⟨hzU, hzδ, hg⟩
  have hZcnull : volume Zc = 0 := gradC_zeroSet_null hU hu hnc
  -- G is null: box cover
  have hGnull : volume G = 0 := by
    -- partials via gradC (continuous on U)
    have hgradcont : ContinuousOn (gradC u) U := (gradC_differentiableOn hu).continuousOn
    have hdiffU : ∀ z ∈ U, DifferentiableAt ℝ u z :=
      fun z hz => differentiableAt_of_harmonicOnNhd hu hz
    have hIeq : ∀ z : ℂ, (fderiv ℝ u z) Complex.I = -(gradC u z).im := by
      intro z; rw [fderiv_eq_re_gradC_mul u z Complex.I, Complex.mul_I_re]
    have hOneEq : ∀ z : ℂ, (fderiv ℝ u z) 1 = (gradC u z).re := by
      intro z; rw [fderiv_eq_re_gradC_mul u z 1, mul_one]
    -- per point z0 ∈ G, choose a rectangle
    -- the open set where the vertical partial is nonzero (within U)
    have hOpenV : IsOpen (U ∩ {z : ℂ | (gradC u z).im ≠ 0}) :=
      hgradcont.isOpen_inter_preimage hU (isOpen_ne.preimage Complex.continuous_im)
    have hOpenH : IsOpen (U ∩ {z : ℂ | (gradC u z).re ≠ 0}) :=
      hgradcont.isOpen_inter_preimage hU (isOpen_ne.preimage Complex.continuous_re)
    -- rectangle-and-direction assignment
    set rect : ℝ → ℝ → ℝ → ℝ → Set ℂ :=
      fun a₁ a₂ b₁ b₂ => {z : ℂ | z.re ∈ Ioo a₁ a₂ ∧ z.im ∈ Ioo b₁ b₂} with hrect
    have hpick : ∀ z0 ∈ G, ∃ a₁ a₂ b₁ b₂ : ℝ, z0.re ∈ Ioo a₁ a₂ ∧ z0.im ∈ Ioo b₁ b₂ ∧
        ((rect a₁ a₂ b₁ b₂ ⊆ U ∧
            ∀ z ∈ rect a₁ a₂ b₁ b₂, (fderiv ℝ u z) Complex.I ≠ 0) ∨
          (rect a₁ a₂ b₁ b₂ ⊆ U ∧
            ∀ z ∈ rect a₁ a₂ b₁ b₂, (fderiv ℝ u z) 1 ≠ 0)) := by
      intro z0 hz0
      obtain ⟨hz0U, hz0δ, hz0g⟩ := hz0
      -- gradC ≠ 0 gives im ≠ 0 or re ≠ 0
      have hdir : (gradC u z0).im ≠ 0 ∨ (gradC u z0).re ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hz0g (Complex.ext hcon.2 hcon.1)
      rcases hdir with hv | hh
      · obtain ⟨a₁, a₂, b₁, b₂, hr, hi, hsub⟩ := exists_rect_subset_of_isOpen hOpenV
          (show z0 ∈ U ∩ {z : ℂ | (gradC u z).im ≠ 0} from ⟨hz0U, hv⟩)
        refine ⟨a₁, a₂, b₁, b₂, hr, hi, Or.inl ⟨fun z hz => (hsub hz).1, fun z hz => ?_⟩⟩
        rw [hIeq]; exact fun h => (hsub hz).2 (neg_eq_zero.mp h)
      · obtain ⟨a₁, a₂, b₁, b₂, hr, hi, hsub⟩ := exists_rect_subset_of_isOpen hOpenH
          (show z0 ∈ U ∩ {z : ℂ | (gradC u z).re ≠ 0} from ⟨hz0U, hh⟩)
        refine ⟨a₁, a₂, b₁, b₂, hr, hi, Or.inr ⟨fun z hz => (hsub hz).1, fun z hz => ?_⟩⟩
        rw [hOneEq]; exact (hsub hz).2
    choose! A1 A2 B1 B2 hAr hAi hAdir using hpick
    -- rectangle set for each point
    set R : ℂ → Set ℂ := fun z0 => rect (A1 z0) (A2 z0) (B1 z0) (B2 z0) with hR
    have hRopen : ∀ z0, IsOpen (R z0) := fun z0 =>
      (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
    -- countable subcover of the open cover of G
    obtain ⟨T, hTsub, hTcount, hTU⟩ :=
      TopologicalSpace.isOpen_biUnion_countable G R (fun z0 _ => hRopen z0)
    have hGcover : G ⊆ ⋃ z0 ∈ T, R z0 := by
      intro z hz
      rw [hTU]
      exact mem_biUnion hz ⟨hAr z hz, hAi z hz⟩
    -- each L ∩ R z0 (z0 ∈ T) is null
    have hpiece : ∀ z0 ∈ T, volume (L ∩ R z0) = 0 := by
      intro z0 hz0
      have hz0G : z0 ∈ G := hTsub hz0
      have hLRmeas : MeasurableSet (L ∩ R z0) := hLmeas.inter (hRopen z0).measurableSet
      -- L ∩ R z0 = {z | z ∈ R z0 ∧ u z = δ ∧ z ∈ U} ⊆ level set on the rectangle
      rcases hAdir z0 hz0G with ⟨hrsubU, hvne⟩ | ⟨hrsubU, hhne⟩
      · -- vertical subsingleton
        apply volume_eq_zero_of_subsingleton_vertical_slice hLRmeas
        intro x
        have hsub := subsingleton_vertical_slice_of_deriv_ne
          (u := u) (δ := δ) (a₁ := A1 z0) (a₂ := A2 z0) (b₁ := B1 z0) (b₂ := B2 z0)
          (fun z hzr hzi => hdiffU z (hrsubU ⟨hzr, hzi⟩))
          (fun z hzr hzi => hvne z ⟨hzr, hzi⟩) x
        intro y1 hy1 y2 hy2
        apply hsub
        · obtain ⟨hy1L, hy1R⟩ := hy1
          exact ⟨hy1R.1, hy1R.2, hy1L.2⟩
        · obtain ⟨hy2L, hy2R⟩ := hy2
          exact ⟨hy2R.1, hy2R.2, hy2L.2⟩
      · -- horizontal subsingleton
        apply volume_eq_zero_of_subsingleton_horizontal_slice hLRmeas
        intro y
        have hsub := subsingleton_horizontal_slice_of_deriv_ne
          (u := u) (δ := δ) (a₁ := A1 z0) (a₂ := A2 z0) (b₁ := B1 z0) (b₂ := B2 z0)
          (fun z hzr hzi => hdiffU z (hrsubU ⟨hzr, hzi⟩))
          (fun z hzr hzi => hhne z ⟨hzr, hzi⟩) y
        intro x1 hx1 x2 hx2
        apply hsub
        · obtain ⟨hx1L, hx1R⟩ := hx1
          exact ⟨hx1R.1, hx1R.2, hx1L.2⟩
        · obtain ⟨hx2L, hx2R⟩ := hx2
          exact ⟨hx2R.1, hx2R.2, hx2L.2⟩
    -- assemble
    have hGsub : G ⊆ ⋃ z0 ∈ T, (L ∩ R z0) := by
      intro z hz
      obtain ⟨i, hi, hiR⟩ := mem_iUnion₂.mp (hGcover hz)
      exact mem_biUnion hi ⟨(show z ∈ L from ⟨hz.1, hz.2.1⟩), hiR⟩
    refine le_antisymm ?_ (zero_le _)
    calc volume G ≤ volume (⋃ z0 ∈ T, (L ∩ R z0)) := measure_mono hGsub
      _ = 0 := (measure_biUnion_null_iff hTcount).2 hpiece
  refine le_antisymm ?_ (zero_le _)
  calc volume L ≤ volume (Zc ∪ G) := measure_mono hLsplit
    _ ≤ volume Zc + volume G := measure_union_le _ _
    _ = 0 := by rw [hZcnull, hGnull, add_zero]

/-- **A.e.-`ξ` angular slice nullity of a planar-null level set.** If the level set
`L = {z ∈ U | u z = δ}` (measurable) has planar measure zero, then for a.e. log-radius `ξ` the
angular slice `{θ ∈ (−π, π) | e^{ξ+θi} ∈ U ∧ u(e^{ξ+θi}) = δ}` has one-dimensional measure zero.
The log-polar change of variables (`Complex.lintegral_comp_polarCoord_symm`, then the radial
substitution `r = e^ξ` with positive Jacobian) writes the vanishing planar integral of `1_L` as an
iterated integral over `(ξ, θ)`, whose inner `θ`-integral is a.e.-`ξ` zero. -/
theorem ae_angularSlice_levelSet_null {u : ℂ → ℝ} {U : Set ℂ} {δ : ℝ}
    (hLmeas : MeasurableSet {z : ℂ | z ∈ U ∧ u z = δ})
    (hLnull : volume {z : ℂ | z ∈ U ∧ u z = δ} = 0) :
    ∀ᵐ ξ : ℝ, volume {θ : ℝ | θ ∈ Ioo (-π) π ∧
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ} = 0 := by
  classical
  set L : Set ℂ := {z : ℂ | z ∈ U ∧ u z = δ} with hLdef
  -- Slice indicator abbreviations
  set S : ℝ → Set ℝ := fun ξ => {θ : ℝ | θ ∈ Ioo (-π) π ∧
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ} with hSdef
  -- the (ξ, θ)-indicator of the pulled-back level set on the log-strip box
  set g : ℝ → ℝ → ℝ≥0∞ := fun ξ θ => (Ioo (-π) π).indicator
    (fun θ' => L.indicator (fun _ => (1 : ℝ≥0∞))
      (Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I))) θ with hgdef
  -- the inner θ-integral of `g ξ` is the measure of the slice `S ξ`
  have hinner : ∀ ξ : ℝ, (∫⁻ θ, g ξ θ) = volume (S ξ) := by
    intro ξ
    have hmeasθ : MeasurableSet {θ : ℝ |
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable hLmeas
    have hSeq : S ξ = Ioo (-π) π ∩ {θ : ℝ |
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L} := by
      ext θ
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, ⟨h2, h3⟩⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    calc (∫⁻ θ, g ξ θ)
        = ∫⁻ θ, (Ioo (-π) π ∩ {θ'' : ℝ |
            Complex.exp ((ξ : ℂ) + (θ'' : ℂ) * Complex.I) ∈ L}).indicator
              (fun _ => (1 : ℝ≥0∞)) θ := by
          refine lintegral_congr fun θ => ?_
          simp only [hgdef, Set.indicator_apply, mem_inter_iff, mem_setOf_eq, mem_Ioo]
          by_cases h1 : -π < θ ∧ θ < π <;> by_cases h2 : Complex.exp
              ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L <;> simp [h1, h2]
      _ = volume (S ξ) := by
          rw [lintegral_indicator (measurableSet_Ioo.inter hmeasθ), setLIntegral_one, hSeq]
  -- log-polar change of variables: the weighted `ξ`-integral of the slice measure vanishes
  set G : ℂ → ℝ≥0∞ := L.indicator (fun _ => (1 : ℝ≥0∞)) with hGdef
  have hGmeas : Measurable G := measurable_const.indicator hLmeas
  set R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-π) π with hRdef
  have hRMeas : MeasurableSet R := measurableSet_Ioi.prod measurableSet_Ioo
  have hsymmMeas : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have heq : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ))
        = fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      funext p; rw [Complex.polarCoord_symm_apply]
    rw [heq]; exact Continuous.measurable (by fun_prop)
  -- Step 1: the polar integral equals `volume L = 0`; the target is `R`
  have hRtarget : polarCoord.target = R := Complex.polarCoord_target
  have hpolar : ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) = 0 := by
    have hcov := Complex.lintegral_comp_polarCoord_symm G
    rw [← hRtarget]
    calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)
        = ∫⁻ p in polarCoord.target,
            ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p) := by
          simp only [smul_eq_mul]
      _ = ∫⁻ z, G z := hcov
      _ = 0 := by rw [hGdef, lintegral_indicator hLmeas, setLIntegral_one, hLnull]
  -- Step 2: Tonelli on `R` and the radial substitution `r = e^ξ`
  have hintegrand_meas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hGmeas.comp hsymmMeas)
  have hTon : ∫⁻ p in R, ENNReal.ofReal p.1 * G (Complex.polarCoord.symm p)
      = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ)) := by
    have hprod : (volume : Measure (ℝ × ℝ)).restrict R
        = ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
            ((volume : Measure ℝ).restrict (Ioo (-π) π)) := by
      rw [hRdef, Measure.volume_eq_prod, Measure.prod_restrict]
    rw [hprod]; exact lintegral_prod _ hintegrand_meas.aemeasurable
  have hsub : ∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal r * G (Complex.polarCoord.symm (r, θ))
      = ∫⁻ ξ : ℝ, ENNReal.ofReal (Real.exp ξ) * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (Real.exp ξ) * G (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) := by
    have himg : Real.exp '' univ = Ioi (0 : ℝ) := by
      ext r; simp only [image_univ, mem_range, mem_Ioi]
      constructor
      · rintro ⟨x, rfl⟩; exact Real.exp_pos x
      · intro hr; exact ⟨Real.log r, Real.exp_log hr⟩
    rw [← himg,
      lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine lintegral_congr fun ξ => ?_
    rw [abs_of_pos (Real.exp_pos ξ)]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θ (_ : θ ∈ Ioo (-π) π) => ?_)
    rw [polarCoord_symm_exp]
  -- combine: `∫⁻ ξ, exp ξ · (exp ξ · (∫⁻ θ g ξ θ)) = 0`
  have hfinal : ∫⁻ ξ : ℝ, ENNReal.ofReal (Real.exp ξ)
      * (ENNReal.ofReal (Real.exp ξ) * (∫⁻ θ, g ξ θ)) = 0 := by
    rw [← hpolar, hTon, hsub]
    refine lintegral_congr fun ξ => ?_
    congr 1
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hθmeas : MeasurableSet {θ : ℝ |
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L} :=
      (by fun_prop : Continuous fun θ : ℝ =>
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)).measurable hLmeas
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun θ => ?_
    simp only [hgdef, Set.indicator_apply, hGdef]
    by_cases h1 : θ ∈ Ioo (-π) π <;>
      by_cases h2 : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ L <;> simp [h1, h2]
  -- measurability of the inner slice integral in `ξ`
  have hgjoint : Measurable (Function.uncurry g) := by
    have hexpmap : Measurable fun p : ℝ × ℝ =>
        Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).measurable
    have h1 : Measurable fun p : ℝ × ℝ => G (Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) :=
      hGmeas.comp hexpmap
    have h2 : Measurable fun p : ℝ × ℝ => (Ioo (-π) π).indicator
        (fun _ : ℝ => G (Complex.exp ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) p.2 := by
      have : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioo (-π) π} :=
        measurable_snd measurableSet_Ioo
      exact h1.indicator this
    simpa only [Function.uncurry, hgdef] using h2
  have hglint_meas : Measurable fun ξ : ℝ => ∫⁻ θ, g ξ θ := hgjoint.lintegral_prod_right
  -- conclude: a.e.-ξ the slice measure vanishes
  have hae : ∀ᵐ ξ : ℝ, ENNReal.ofReal (Real.exp ξ)
      * (ENNReal.ofReal (Real.exp ξ) * (∫⁻ θ, g ξ θ)) = 0 :=
    (lintegral_eq_zero_iff ((ENNReal.measurable_ofReal.comp Real.measurable_exp).mul
      ((ENNReal.measurable_ofReal.comp Real.measurable_exp).mul hglint_meas))).mp hfinal
  -- strip the positive `exp ξ` factors
  filter_upwards [hae] with ξ hξ
  rw [← hinner ξ]
  have hexp0 : ENNReal.ofReal (Real.exp ξ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos ξ)).ne'
  have := hξ
  rw [mul_eq_zero, mul_eq_zero] at this
  rcases this with h | h | h
  · exact absurd h hexp0
  · exact absurd h hexp0
  · exact h

/-- **Radial right-derivative of the windowed truncated integrand off the level set.** For `u`
harmonic on the open `U` with the superlevel window intersection compactly contained in `U`, at any
`(ξ, θ)` whose exponential does not lie on the level set `{u = δ}`, the radial line map
`x ↦ windowedTruncIntegrand u U δ (x + θi)` is differentiable at `ξ` with derivative the superlevel
indicator of `(Re expGrad)² + (u∘exp − δ)·Re (deriv expGrad)`.  Off the compact containment the map
is locally `0`; on the superlevel set the two smooth factors give the product rule; on the strict
sublevel set the map is locally `0` again. -/
theorem hasDerivAt_windowedTruncIntegrand_radial {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ ξ θ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hK : closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) ⊆ U)
    (hξ : ξ ∈ Ioo ζ₁ ζ₂) (hθmem : θ ∈ Icc (-π) π)
    (hne : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U →
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≠ δ) :
    HasDerivAt (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
      ({θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}.indicator
        (fun _ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
          + (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
            * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ) ξ := by
  set w₀ : ℂ := (ξ : ℂ) + (θ : ℂ) * Complex.I with hw₀
  set z₀ : ℂ := Complex.exp w₀ with hz₀
  set P : Set ℝ := {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ superLevelU U u δ}
    with hP
  have hexpline : ContinuousAt (fun x : ℝ => Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) ξ :=
    (Complex.continuous_exp.comp (by fun_prop :
      Continuous fun x : ℝ => (x : ℂ) + (θ : ℂ) * Complex.I)).continuousAt
  by_cases hzU : z₀ ∈ U
  · -- `exp w₀ ∈ U`: split on `u z₀ > δ` (superlevel) vs `u z₀ < δ` (sublevel)
    have hnhdU : {x : ℝ | Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ U} ∈ nhds ξ :=
      hexpline.preimage_mem_nhds (hU.mem_nhds hzU)
    have hcu' : ContinuousAt (fun x : ℝ => u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))) ξ :=
      (hasDerivAt_uexp_radial (θ := θ) (differentiableAt_of_harmonicOnNhd hu hzU)).continuousAt
    rcases lt_or_gt_of_ne (hne hzU) with hlt | hgt
    · -- sublevel: `(u∘exp − δ)⁺ = 0` on a neighbourhood, so the integrand is locally `0`
      have hθP : θ ∉ P := by
        simp only [hP, mem_setOf_eq, superLevelU, mem_setOf_eq, not_and]
        exact fun _ => not_lt.mpr hlt.le
      rw [Set.indicator_of_notMem hθP]
      have hloc : (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
          =ᶠ[nhds ξ] fun _ => (0 : ℝ) := by
        have hsub : {x : ℝ | u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) < δ} ∈ nhds ξ :=
          hcu'.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
        filter_upwards [hsub, hnhdU] with x hx hxU
        unfold windowedTruncIntegrand
        rw [Set.indicator_of_mem hxU,
          posPart_eq_zero.mpr (by linarith [hx]), zero_mul]
      exact (hasDerivAt_const ξ (0 : ℝ)).congr_of_eventuallyEq hloc
    · -- superlevel: product rule for `(u∘exp − δ)·Re (expGrad)`
      have hθP : θ ∈ P := ⟨hzU, hgt⟩
      rw [Set.indicator_of_mem hθP]
      have hloc : (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
          =ᶠ[nhds ξ] fun x : ℝ => (u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I)) - δ)
            * (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re := by
        have hsup : {x : ℝ | δ < u (Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I))} ∈ nhds ξ :=
          hcu'.preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)
        filter_upwards [hsup, hnhdU] with x hx hxU
        unfold windowedTruncIntegrand
        rw [Set.indicator_of_mem hxU,
          posPart_eq_self.mpr (by linarith [hx]), expGrad]
      have hu' := hasDerivAt_uexp_radial
        (θ := θ) (differentiableAt_of_harmonicOnNhd hu hzU)
      have hD := hasDerivAt_expGrad_radial (θ := θ) (expGrad_differentiableAt_open hU hu hzU)
      have hDre : HasDerivAt (fun x : ℝ => (expGrad u ((x : ℂ) + (θ : ℂ) * Complex.I)).re)
          ((deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) ξ := by
        have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt ξ hD
        simpa [Function.comp] using hcomp
      have hprod := ((hu'.sub_const δ).mul hDre)
      refine (hprod.congr_deriv ?_).congr_of_eventuallyEq hloc
      ring
  · -- `exp w₀ ∉ U ⊆ᶜ K`: the integrand vanishes on a neighbourhood of `ξ`
    have hθP : θ ∉ P := by
      simp only [hP, mem_setOf_eq, superLevelU, mem_setOf_eq, not_and]
      exact fun h => absurd h hzU
    rw [Set.indicator_of_notMem hθP]
    have hwK : z₀ ∉ closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) :=
      fun h => hzU (hK h)
    have hnhd : {x : ℝ | Complex.exp ((x : ℂ) + (θ : ℂ) * Complex.I) ∉
        closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂))} ∈ nhds ξ :=
      (Complex.continuous_exp.comp (by fun_prop :
        Continuous fun x : ℝ => (x : ℂ) + (θ : ℂ) * Complex.I)).continuousAt.preimage_mem_nhds
        (isClosed_closure.isOpen_compl.mem_nhds hwK)
    have hloc : (fun x : ℝ => windowedTruncIntegrand u U δ ((x : ℂ) + (θ : ℂ) * Complex.I))
        =ᶠ[nhds ξ] fun _ => (0 : ℝ) := by
      have hstrip : {x : ℝ | ((x : ℂ) + (θ : ℂ) * Complex.I) ∈
          stripBox ζ₁ ζ₂ (-π) π} ∈ nhds ξ :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hξ) (fun x hx => by
          simp only [stripBox, mem_setOf_eq, re_logPolar, im_logPolar]
          exact ⟨hx.1, hx.2, hθmem.1, hθmem.2⟩)
      filter_upwards [hnhd, hstrip] with x hx hxstrip
      exact windowedTruncIntegrand_eq_zero_of_notMem hxstrip hx
    exact (hasDerivAt_const ξ (0 : ℝ)).congr_of_eventuallyEq hloc

/-- **The ring product of two bounded Lipschitz functions is Lipschitz.** On a set where `f` and
`g` are `Lipschitz` with constants `Kf, Kg` and bounded in norm by `Bf, Bg`, the pointwise product
`f · g` is Lipschitz with constant `Bf·Kg + Bg·Kf`. -/
theorem lipschitzOnWith_mul_of_bounded {α : Type*} [PseudoMetricSpace α] {s : Set α}
    {f g : α → ℝ} {Kf Kg Bf Bg : NNReal}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hBf : ∀ x ∈ s, ‖f x‖ ≤ Bf) (hBg : ∀ x ∈ s, ‖g x‖ ≤ Bg) :
    LipschitzOnWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hfd := (lipschitzOnWith_iff_dist_le_mul.mp hf) x hx y hy
  have hgd := (lipschitzOnWith_iff_dist_le_mul.mp hg) x hx y hy
  have hstep : dist (f x * g x) (f y * g y)
      ≤ ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := by
    simp only [Real.dist_eq]
    calc |f x * g x - f y * g y|
        = |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
      _ ≤ |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
      _ = ‖f x‖ * |g x - g y| + ‖g y‖ * |f x - f y| := by
          rw [abs_mul, abs_mul]; simp only [Real.norm_eq_abs]; ring
  calc dist (f x * g x) (f y * g y)
      ≤ ‖f x‖ * dist (g x) (g y) + ‖g y‖ * dist (f x) (f y) := hstep
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) + (Bg : ℝ) * ((Kf : ℝ) * dist x y) := by
        gcongr
        · exact hBf x hx
        · exact hBg y hy
    _ = ((Bf * Kg + Bg * Kf : NNReal) : ℝ) * dist x y := by push_cast; ring

/-- **Local Lipschitz continuity of the windowed truncated integrand.** For `u` harmonic on the open
`U` with the superlevel window intersection compactly contained in `U`, the integrand
`windowedTruncIntegrand u U δ` is locally Lipschitz on the log-strip box `stripBox ζ₁' ζ₂' (−π) π`:
off the compact containment it is locally `0`, and near a point whose exponential lies in `U` it is
the product of the locally-Lipschitz factors `(u∘exp − δ)⁺` (Lipschitz `posPart` of a `C²` map) and
`Re (expGrad u)` (real part of a holomorphic map), both locally bounded. -/
theorem locallyLipschitzOn_windowedTruncIntegrand {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hK : closure (superLevelU U u δ ∩ RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) ⊆ U) :
    LocallyLipschitzOn (stripBox ζ₁ ζ₂ (-π) π) (windowedTruncIntegrand u U δ) := by
  intro w₀ hw₀
  by_cases hzU : Complex.exp w₀ ∈ U
  · -- near a point whose exponential lies in `U`, the integrand is a bounded Lipschitz product
    set F : ℂ → ℝ := fun w : ℂ => (u (Complex.exp w) - δ)⁺ * (expGrad u w).re with hF
    have hnhdU : Complex.exp ⁻¹' U ∈ nhds w₀ :=
      (hU.preimage Complex.continuous_exp).mem_nhds hzU
    have hHeq : ∀ w ∈ Complex.exp ⁻¹' U, windowedTruncIntegrand u U δ w = F w := by
      intro w hw
      unfold windowedTruncIntegrand
      rw [Set.indicator_of_mem (show Complex.exp w ∈ U from hw)]
      simp only [hF, expGrad]
    -- factor 1: `(u∘exp − δ)⁺` is locally Lipschitz (posPart of a `C²` map)
    have hcexp : ContDiffAt ℝ 2 Complex.exp w₀ :=
      (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt
    have hcd : ContDiffAt ℝ 2 (fun w : ℂ => u (Complex.exp w)) w₀ :=
      (hu.contDiffOn.contDiffAt (hU.mem_nhds hzU)).comp w₀ hcexp
    obtain ⟨K1, s1, hs1, hL1⟩ :=
      ((hcd.hasStrictFDerivAt (by norm_num)).sub_const δ).exists_lipschitzOnWith
    have hLpos : LipschitzOnWith K1 (fun w : ℂ => (u (Complex.exp w) - δ)⁺) s1 := by
      have := lipschitzWith_posPart.comp_lipschitzOnWith hL1
      rwa [one_mul] at this
    -- factor 2: `Re (expGrad u) = (fderiv ℝ u ∘ exp) applied to exp` is `C¹`,
    -- hence locally Lipschitz
    have hueq : (fun w : ℂ => (expGrad u w).re)
        = fun w : ℂ => (fderiv ℝ u (Complex.exp w)) (Complex.exp w) := by
      funext w; rw [expGrad, fderiv_eq_re_gradC_mul]
    have hufd : ContDiffAt ℝ 1 (fun z : ℂ => fderiv ℝ u z) (Complex.exp w₀) :=
      (hu.contDiffOn.contDiffAt (hU.mem_nhds hzU)).fderiv_right (m := 1) (by norm_num)
    have hcd2 : ContDiffAt ℝ 1 (fun w : ℂ => (expGrad u w).re) w₀ := by
      rw [hueq]
      have hpair : ContDiffAt ℝ 1
          (fun w : ℂ => (fderiv ℝ u (Complex.exp w), Complex.exp w)) w₀ :=
        (hufd.comp w₀ (hcexp.of_le (by norm_num))).prodMk (hcexp.of_le (by norm_num))
      exact (isBoundedBilinearMap_apply.contDiff.contDiffAt).comp w₀ hpair
    obtain ⟨K2, s2, hs2, hL2⟩ :=
      (hcd2.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
    -- boundedness on a neighbourhood of `w₀` (continuity)
    have hc1 : ContinuousAt (fun w : ℂ => (u (Complex.exp w) - δ)⁺) w₀ :=
      (continuous_posPart.continuousAt).comp (hcd.continuousAt.sub continuousAt_const)
    have hc2 : ContinuousAt (fun w : ℂ => (expGrad u w).re) w₀ := hcd2.continuousAt
    have hb1 : {w : ℂ | ‖(u (Complex.exp w) - δ)⁺‖ ≤ ‖(u (Complex.exp w₀) - δ)⁺‖ + 1} ∈ nhds w₀ :=
      hc1.norm.eventually_le_const (by simp : ‖(u (Complex.exp w₀) - δ)⁺‖
        < ‖(u (Complex.exp w₀) - δ)⁺‖ + 1)
    have hb2 : {w : ℂ | ‖(expGrad u w).re‖ ≤ ‖(expGrad u w₀).re‖ + 1} ∈ nhds w₀ :=
      hc2.norm.eventually_le_const (by simp : ‖(expGrad u w₀).re‖ < ‖(expGrad u w₀).re‖ + 1)
    set B1 : NNReal := (‖(u (Complex.exp w₀) - δ)⁺‖ + 1).toNNReal with hB1def
    set B2 : NNReal := (‖(expGrad u w₀).re‖ + 1).toNNReal with hB2def
    set t : Set ℂ := (Complex.exp ⁻¹' U ∩ (s1 ∩ s2)) ∩
      ({w | ‖(u (Complex.exp w) - δ)⁺‖ ≤ ‖(u (Complex.exp w₀) - δ)⁺‖ + 1} ∩
        {w | ‖(expGrad u w).re‖ ≤ ‖(expGrad u w₀).re‖ + 1}) with htdef
    have htnhd : t ∈ nhds w₀ :=
      inter_mem (inter_mem hnhdU (inter_mem hs1 hs2)) (inter_mem hb1 hb2)
    refine ⟨B1 * K2 + B2 * K1, t, nhdsWithin_le_nhds htnhd, ?_⟩
    have hprodLip : LipschitzOnWith (B1 * K2 + B2 * K1) F t := by
      refine lipschitzOnWith_mul_of_bounded
        (hLpos.mono (fun w hw => hw.1.2.1)) (hL2.mono (fun w hw => hw.1.2.2))
        (fun w hw => le_trans hw.2.1 (Real.le_coe_toNNReal _))
        (fun w hw => le_trans hw.2.2 (Real.le_coe_toNNReal _))
    intro x hx y hy
    rw [hHeq x hx.1.1, hHeq y hy.1.1]
    exact hprodLip hx hy
  · -- off `U`, `exp w₀ ∉ K`, so the integrand vanishes on a strip-box neighbourhood
    have hwK : Complex.exp w₀ ∉ closure (superLevelU U u δ ∩
        RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)) := fun h => hzU (hK h)
    have hnhd : Complex.exp ⁻¹' (closure (superLevelU U u δ ∩
        RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)))ᶜ ∈ nhds w₀ :=
      (isClosed_closure.isOpen_compl.preimage Complex.continuous_exp).mem_nhds hwK
    refine ⟨0, stripBox ζ₁ ζ₂ (-π) π ∩
      Complex.exp ⁻¹' (closure (superLevelU U u δ ∩
        RoundAnnulus 0 (Real.exp ζ₁) (Real.exp ζ₂)))ᶜ,
      inter_mem_nhdsWithin _ hnhd, ?_⟩
    intro x hx y hy
    rw [windowedTruncIntegrand_eq_zero_of_notMem hx.1 hx.2,
      windowedTruncIntegrand_eq_zero_of_notMem hy.1 hy.2]
    simp

/-- **Lipschitz continuity of the truncated rough flux.** For `u` harmonic on the open `U`,
continuous on `closure U` and vanishing on the inner frontier, the truncated rough flux
`truncRoughFlux u U δ` is Lipschitz on `[ζ₁, ζ₂]` (`ζ₂ < 0`, `δ > 0`): enlarging the window slightly
to `(ζ₁', ζ₂')` with `ζ₂' < 0`, its full-circle integrand `windowedTruncIntegrand u U δ` is globally
Lipschitz on the compact log-strip slab with constant `K₀` (local Lipschitz on a compact set), so
the `θ`-integral of the two-point radial difference is bounded by `2π·K₀·|ξ − ξ'|`. -/
theorem lipschitzOnWith_truncRoughFlux {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U)) (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hδ : 0 < δ) (h12 : ζ₁ ≤ ζ₂) (hζ₂ : ζ₂ < 0) :
    ∃ L : NNReal, LipschitzOnWith L (truncRoughFlux u U δ) (uIcc ζ₁ ζ₂) := by
  have hπ := Real.pi_pos
  -- enlarge the window: `ζ₁' < ζ₁ ≤ ζ₂ < ζ₂' < 0`
  set ζ₁' : ℝ := ζ₁ - 1 with hζ₁'
  set ζ₂' : ℝ := (ζ₂ + 0) / 2 with hζ₂'
  have hζ₂'0 : ζ₂' < 0 := by rw [hζ₂']; linarith
  have hζ₁'lt : ζ₁' < ζ₁ := by rw [hζ₁']; linarith
  have hζ₂lt : ζ₂ < ζ₂' := by rw [hζ₂']; linarith
  have hK := (closure_superLevel_window_subset (u := u) (U := U) (δ := δ)
    (ζ₁ := ζ₁') (ζ₂ := ζ₂') hucont hE0 hδ hζ₂'0).2
  -- the closed slab `[ζ₁, ζ₂] × [−π, π]` is compact and sits in the open strip `(ζ₁', ζ₂')`
  set C : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Icc ζ₁ ζ₂ ×ˢ Icc (-π) π) with hCdef
  have hCcompact : IsCompact C := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hCsub : C ⊆ stripBox ζ₁' ζ₂' (-π) π := by
    rintro w ⟨⟨x, θ⟩, ⟨hx, hθ⟩, rfl⟩
    simp only [stripBox, mem_setOf_eq, re_logPolar, im_logPolar]
    exact ⟨lt_of_lt_of_le hζ₁'lt hx.1, lt_of_le_of_lt hx.2 hζ₂lt, hθ.1, hθ.2⟩
  obtain ⟨K₀, hK₀⟩ :=
    ((locallyLipschitzOn_windowedTruncIntegrand hU hu hK).mono
      hCsub).exists_lipschitzOnWith_of_compact hCcompact
  -- per-`θ` radial two-point bound and integration over `(−π, π)`
  refine ⟨(2 * π).toNNReal * K₀, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro ξ hξ ξ' hξ'
  rw [uIcc_of_le h12] at hξ hξ'
  rw [truncRoughFlux_eq_integral_windowedTruncIntegrand,
    truncRoughFlux_eq_integral_windowedTruncIntegrand, Real.dist_eq]
  set H : ℂ → ℝ := windowedTruncIntegrand u U δ with hHdef
  -- membership of the slab
  have hmemC : ∀ x : ℝ, x ∈ Icc ζ₁ ζ₂ → ∀ θ : ℝ, θ ∈ Ioo (-π) π →
      ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ C := fun x hx θ hθ =>
    ⟨(x, θ), ⟨hx, ⟨hθ.1.le, hθ.2.le⟩⟩, by apply Complex.ext <;> simp⟩
  -- per-θ two-point Lipschitz bound from the slab Lipschitz constant
  have hptwise : ∀ θ ∈ Ioo (-π) π, ‖H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
      - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)‖ ≤ (K₀ : ℝ) * |ξ - ξ'| := by
    intro θ hθ
    have hd := (lipschitzOnWith_iff_dist_le_mul.mp hK₀) _ (hmemC ξ hξ θ hθ) _ (hmemC ξ' hξ' θ hθ)
    rw [Real.dist_eq, Complex.dist_eq] at hd
    have hdiff : ((ξ : ℂ) + (θ : ℂ) * Complex.I) - ((ξ' : ℂ) + (θ : ℂ) * Complex.I)
        = (ξ - ξ' : ℝ) := by push_cast; ring
    rw [hdiff, Complex.norm_real] at hd
    exact hd
  -- integrability of both integrand slices (continuous on the compact slab, hence on `(−π, π)`)
  have hcontH : ContinuousOn H (stripBox ζ₁' ζ₂' (-π) π) :=
    continuousOn_windowedTruncIntegrand hU hu hK
  have hslice : ∀ x : ℝ, x ∈ Icc ζ₁ ζ₂ →
      IntegrableOn (fun θ : ℝ => H ((x : ℂ) + (θ : ℂ) * Complex.I)) (Ioo (-π) π) := by
    intro x hx
    have hxstrip : ζ₁' < x ∧ x < ζ₂' := ⟨lt_of_lt_of_le hζ₁'lt hx.1, lt_of_le_of_lt hx.2 hζ₂lt⟩
    exact (continuousOn_slice_of_continuousOn_stripBox hcontH hxstrip.1
      hxstrip.2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- the difference integral is bounded by the constant integrated over `(−π, π)`
  have hdiffint : IntegrableOn (fun θ : ℝ => H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
      - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)) (Ioo (-π) π) :=
    (hslice ξ hξ).sub (hslice ξ' hξ')
  calc |(∫ θ in Ioo (-π) π, H ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        - ∫ θ in Ioo (-π) π, H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)|
      = |∫ θ in Ioo (-π) π, (H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
          - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I))| := by
        rw [integral_sub (hslice ξ hξ) (hslice ξ' hξ')]
    _ ≤ ∫ θ in Ioo (-π) π, ‖H ((ξ : ℂ) + (θ : ℂ) * Complex.I)
          - H ((ξ' : ℂ) + (θ : ℂ) * Complex.I)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ _θ in Ioo (-π) π, (K₀ : ℝ) * |ξ - ξ'| := by
        refine setIntegral_mono_on hdiffint.norm
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
          measurableSet_Ioo (fun θ hθ => hptwise θ hθ)
    _ = ((2 * π).toNNReal * K₀ : NNReal) * |ξ - ξ'| := by
        rw [setIntegral_const]
        have hvol : (volume (Ioo (-π) π)).toReal = 2 * π := by
          rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; ring
        rw [MeasureTheory.measureReal_def, hvol, smul_eq_mul]
        push_cast [Real.coe_toNNReal (2 * π) (by positivity)]
        ring

/-- **The `ξ`-derivative of the truncated rough flux is the superlevel-slice energy.** For `u`
harmonic on the open `U`, at any interior log-radius `ξ ∈ (ζ₁, ζ₂)` whose angular slice meets the
level set `{u = δ}` in a null set, the truncated rough flux `truncRoughFlux u U δ` has derivative
`sliceEnergyU u (superLevelU U u δ) ξ`.  Differentiation under the `θ`-integral of the
strip-box-Lipschitz windowed integrand (a.e.-`θ` radial product rule off the level set, dominated by
the slab Lipschitz constant) gives `∫_slice [(Re expGrad)² + (u−δ)·Re (deriv expGrad)]`, which the
branch-cut-free `θ`-IBP `setIntegral_slice_posPart_re_deriv_expGrad` rewrites to
`∫_slice |expGrad|²`. -/
theorem hasDerivAt_truncRoughFlux_of_slice_null {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ ξ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hucont : ContinuousOn u (closure U)) (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hcontR : Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hEIntδ : IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSliceδ U u δ ξ))
    (hδ : 0 < δ) (hζ₂ : ζ₂ < 0) (hξ : ξ ∈ Ioo ζ₁ ζ₂)
    (hnull : volume {θ : ℝ | θ ∈ Ioo (-π) π ∧
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
      u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ} = 0) :
    HasDerivAt (truncRoughFlux u U δ) (sliceEnergyU u (superLevelU U u δ) ξ) ξ := by
  have hπ := Real.pi_pos
  set V : Set ℂ := superLevelU U u δ with hVdef
  have hVopen : IsOpen V := isOpen_superLevelU hU hu δ
  -- enlarge the window and take the compact slab Lipschitz constant for the dominator
  set ζ₁' : ℝ := ζ₁ - 1 with hζ₁'
  set ζ₂' : ℝ := ζ₂ / 2 with hζ₂'
  have hζ₂'0 : ζ₂' < 0 := by rw [hζ₂']; linarith
  have hζ₁'lt : ζ₁' < ξ := by rw [hζ₁']; linarith [hξ.1]
  have hξlt2 : ξ < ζ₂' := by rw [hζ₂']; linarith [hξ.2]
  have hK := (closure_superLevel_window_subset (u := u) (U := U) (δ := δ)
    (ζ₁ := ζ₁') (ζ₂ := ζ₂') hucont hE0 hδ hζ₂'0).2
  -- a compact slab neighbourhood of `ξ` in the log-radius, inside the open strip `(ζ₁', ζ₂')`
  set r : ℝ := min (ξ - ζ₁') (ζ₂' - ξ) / 2 with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]; have h1 : 0 < ξ - ζ₁' := by linarith
    have h2 : 0 < ζ₂' - ξ := by linarith
    positivity
  have hrsub : Icc (ξ - r) (ξ + r) ⊆ Ioo ζ₁' ζ₂' := by
    intro y hy
    have hmin := min_le_left (ξ - ζ₁') (ζ₂' - ξ)
    have hmin' := min_le_right (ξ - ζ₁') (ζ₂' - ξ)
    exact ⟨by simp only [hrdef] at hy ⊢; linarith [hy.1],
      by simp only [hrdef] at hy ⊢; linarith [hy.2]⟩
  set C : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Icc (ξ - r) (ξ + r) ×ˢ Icc (-π) π) with hCdef
  have hCcompact : IsCompact C := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hCsub : C ⊆ stripBox ζ₁' ζ₂' (-π) π := by
    rintro w ⟨⟨x, θ⟩, ⟨hx, hθ⟩, rfl⟩
    have hxIoo := hrsub hx
    simp only [stripBox, mem_setOf_eq, re_logPolar, im_logPolar]
    exact ⟨hxIoo.1, hxIoo.2, hθ.1, hθ.2⟩
  obtain ⟨K₀, hK₀⟩ :=
    ((locallyLipschitzOn_windowedTruncIntegrand hU hu hK).mono
      hCsub).exists_lipschitzOnWith_of_compact hCcompact
  set H : ℂ → ℝ := windowedTruncIntegrand u U δ with hHdef
  -- the derivative-value slice integrand
  set F' : ℝ → ℝ := fun θ =>
    {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V}.indicator
      (fun _ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) θ with hF'def
  have hslabmem : ∀ x : ℝ, x ∈ Metric.ball ξ r → ∀ θ : ℝ, θ ∈ Icc (-π) π →
      ((x : ℂ) + (θ : ℂ) * Complex.I) ∈ C := by
    intro x hx θ hθ
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
    exact ⟨(x, θ), ⟨⟨by linarith [hx.2], by linarith [hx.1]⟩, hθ⟩, by apply Complex.ext <;> simp⟩
  -- strip-box continuity of `H` for slice integrability/measurability
  have hcontH : ContinuousOn H (stripBox ζ₁' ζ₂' (-π) π) :=
    continuousOn_windowedTruncIntegrand hU hu hK
  have hsliceIcc : ∀ x : ℝ, x ∈ Ioo ζ₁' ζ₂' →
      IntegrableOn (fun θ : ℝ => H ((x : ℂ) + (θ : ℂ) * Complex.I)) (Ioc (-π) π) := fun x hx =>
    (continuousOn_slice_of_continuousOn_stripBox hcontH hx.1 hx.2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hslice : ∀ x : ℝ, x ∈ Ioo ζ₁' ζ₂' →
      IntegrableOn (fun θ : ℝ => H ((x : ℂ) + (θ : ℂ) * Complex.I)) (Ioo (-π) π) := fun x hx =>
    (continuousOn_slice_of_continuousOn_stripBox hcontH hx.1 hx.2).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  -- a.e.-θ (within `(−π, π)`) the level set is avoided (from the null slice hypothesis)
  have hae_ne : ∀ᵐ θ : ℝ, θ ∈ Ioo (-π) π →
      (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U →
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≠ δ) := by
    have hcompl : ∀ᵐ θ : ℝ, ¬ (θ ∈ Ioo (-π) π ∧
        Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U ∧
        u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ) :=
      MeasureTheory.ae_iff.mpr (by simp only [not_not]; exact hnull)
    filter_upwards [hcompl] with θ hθ hθIoo hθU hθδ
    exact hθ ⟨hθIoo, hθU, hθδ⟩
  -- measurability of the derivative-value integrand `F'` (continuous on the open superlevel slice)
  have hPmeas : MeasurableSet {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} :=
    (hVopen.preimage (by fun_prop)).measurableSet
  have hDEGcont : ContinuousOn (deriv (expGrad u)) (Complex.exp ⁻¹' U) := by
    have hOopen : IsOpen (Complex.exp ⁻¹' U) := hU.preimage Complex.continuous_exp
    have hdiff : DifferentiableOn ℂ (expGrad u) (Complex.exp ⁻¹' U) := fun w hw =>
      (expGrad_differentiableAt_open hU hu hw).differentiableWithinAt
    exact (((hdiff.analyticOnNhd hOopen).deriv_of_isOpen hOopen).continuousOn)
  have hlinecont : Continuous fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hF'contOn : ContinuousOn (fun θ : ℝ =>
      (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re ^ 2
        + (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)
          * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
      {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} := by
    intro θ hθ
    have hmemU : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.1
    have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hmemU
    have hlineθ : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      hlinecont.continuousAt
    have hEGθ : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := expGrad u) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (expGrad_differentiableAt_open hU hu hmemU).continuousAt hlineθ
    have hEGre : ContinuousAt (fun t : ℝ => (expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      Complex.continuous_re.continuousAt.comp hEGθ
    have hexpθ : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := Complex.exp) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        Complex.continuous_exp.continuousAt hlineθ
    have hufun : ContinuousAt (fun t : ℝ => u (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))) θ :=
      ContinuousAt.comp (g := u) (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_of_harmonicOnNhd hu hmemU).continuousAt hexpθ
    have hDEGθ :
        ContinuousAt (fun t : ℝ => deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
      ContinuousAt.comp (g := deriv (expGrad u))
        (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
        (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hlineθ
    have hDEGre :
        ContinuousAt (fun t : ℝ => (deriv (expGrad u) ((ξ : ℂ) + (t : ℂ) * Complex.I)).re) θ :=
      Complex.continuous_re.continuousAt.comp hDEGθ
    exact ((hEGre.pow 2).add ((hufun.sub continuousAt_const).mul hDEGre)).continuousWithinAt
  have hF'meas : AEStronglyMeasurable F' (volume.restrict (Set.uIoc (-π) π)) :=
    ((aestronglyMeasurable_indicator_iff hPmeas).mpr
      (hF'contOn.aestronglyMeasurable hPmeas)).restrict
  -- apply the strip-box-Lipschitz DUI
  have hDUI := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (F := fun (x : ℝ) (θ : ℝ) => H ((x : ℂ) + (θ : ℂ) * Complex.I))
    (F' := F') (x₀ := ξ) (a := -π) (b := π) (bound := fun _ => (K₀ : ℝ))
    (s := Metric.ball ξ r) (Metric.ball_mem_nhds ξ hr0) ?_ ?_ ?_ ?_ ?_ ?_
  · -- rewrite both integrals: `∫_θ H = truncRoughFlux` and `∫_θ F' = sliceEnergyU`
    have hleft : (fun x : ℝ => ∫ θ in (-π)..π, H ((x : ℂ) + (θ : ℂ) * Complex.I))
        = truncRoughFlux u U δ := by
      funext x
      rw [truncRoughFlux_eq_integral_windowedTruncIntegrand,
        integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π)]
    have hright : (∫ θ in (-π)..π, F' θ) = sliceEnergyU u V ξ := by
      -- `∫_θ F' = ∫_slice[(Re expGrad)² + (u−δ)·Re(deriv expGrad)]`, then the branch-cut-free
      -- θ-IBP `setIntegral_slice_posPart_re_deriv_expGrad` turns the second term into
      -- `∫_slice(Im expGrad)²`, summing to `∫_slice |expGrad|² = sliceEnergyU`.  Its escape/bound
      -- hypotheses hold on the superlevel slice (u = δ on ∂V by continuity; expGrad, deriv bounded
      -- on the compact circle-arc `{θ | exp ∈ closure V}`, transported by 2π-periodicity).
      classical
      have hπ2 : (0 : ℝ) < 2 * π := by positivity
      set S : Set ℝ := angularSliceδ U u δ ξ with hSdef
      have hSopen : IsOpen S := isOpen_angularSliceδ hU hu δ ξ
      have hSmeas : MeasurableSet S := hSopen.measurableSet
      have hSsub : S ⊆ Ioo (-π) π := angularSliceδ_subset δ ξ
      have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono hSsub)
      set P : Set ℝ := {θ' : ℝ | Complex.exp ((ξ : ℂ) + (θ' : ℂ) * Complex.I) ∈ V} with hPdef
      have hSP : S = Ioo (-π) π ∩ P := by
        ext θ
        simp only [hSdef, angularSliceδ, hPdef, hVdef, mem_inter_iff, mem_setOf_eq]
      have hSsubP : S ⊆ P := fun θ hθ => (hSP ▸ hθ).2
      -- every log-polar point at radius `ξ` lies in the compact window annulus
      have hannmem : ∀ t : ℝ, Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)
          ∈ RoundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂') := by
        intro t
        have hdist : dist (Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) 0 = Real.exp ξ := by
          rw [dist_zero_right, Complex.norm_exp, re_logPolar]
        simp only [RoundAnnulus, mem_setOf_eq, hdist]
        exact ⟨Real.exp_lt_exp.mpr hζ₁'lt, Real.exp_lt_exp.mpr hξlt2⟩
      set gRe : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hgReD
      set gU : ℝ → ℝ := fun θ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) with hgUD
      set gDE : ℝ → ℝ := fun θ => (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re with hgDED
      set gNS : ℝ → ℝ := fun θ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I))
        with hgNSD
      set gIm : ℝ → ℝ := fun θ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im with hgImD
      -- per-reading continuity on the open slice `S`
      have hcontReadings : ∀ θ ∈ S, ContinuousAt gRe θ ∧ ContinuousAt gU θ ∧ ContinuousAt gDE θ
          ∧ ContinuousAt gNS θ ∧ ContinuousAt gIm θ := by
        intro θ hθ
        have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hθ.2.1
        have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hmem
        have hline : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
        have hEG : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := expGrad u) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (expGrad_differentiableAt_open hU hu hmem).continuousAt hline
        have hexpθ : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := Complex.exp)
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            Complex.continuous_exp.continuousAt hline
        refine ⟨Complex.continuous_re.continuousAt.comp hEG,
          ContinuousAt.comp (g := u)
            (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hexpθ,
          Complex.continuous_re.continuousAt.comp (ContinuousAt.comp (g := deriv (expGrad u))
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hline),
          Complex.continuous_normSq.continuousAt.comp hEG,
          Complex.continuous_im.continuousAt.comp hEG⟩
      -- escape hypothesis
      have hEsc : ∀ θ : ℝ,
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ closure (superLevelU U u δ) →
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∉ superLevelU U u δ →
          u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) = δ := by
        intro θ hcl hnot
        set w : ℂ := Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) with hwD
        have hclV : w ∈ closure V := by rw [hVdef]; exact hcl
        have hnotV : w ∉ V := by rw [hVdef]; exact hnot
        have hann : w ∈ RoundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂') := hannmem θ
        have hVsubU : V ⊆ U := fun z hz => hz.1
        have hwU : w ∈ U := by
          have hin := (isOpen_roundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂')).inter_closure
            (t := V) ⟨hann, hclV⟩
          rw [inter_comm] at hin
          exact hK hin
        have hge : δ ≤ u w := by
          have hmap : MapsTo u V (Ici δ) := fun z hz => le_of_lt hz.2
          have := (hmap.closure_of_continuousOn (hucont.mono (closure_mono hVsubU))) hclV
          rwa [closure_Ici, mem_Ici] at this
        exact le_antisymm (le_of_not_gt (fun h => hnotV ⟨hwU, h⟩)) hge
      -- compact-arc bound transported by 2π-periodicity
      have hgper : Function.Periodic (fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))
          (2 * π) := fun θ => by
        simp only
        rw [show ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
            = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_periodic _]
      -- the log-polar readings are `2π`-periodic in the angle
      have hExp2πI : Complex.exp (2 * (π : ℂ) * Complex.I) = 1 := by
        rw [show (2 * (π : ℂ) * Complex.I) = 2 * ↑π * Complex.I by ring]
        exact Complex.exp_two_pi_mul_I
      have hEGperC : Function.Periodic (expGrad u) (2 * (π : ℂ) * Complex.I) := by
        intro w
        simp only [expGrad]
        rw [show w + 2 * (π : ℂ) * Complex.I = w + 2 * π * Complex.I by ring, Complex.exp_add,
          hExp2πI, mul_one]
      have hloctwo : ∀ θ : ℝ, ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
          = ((ξ : ℂ) + (θ : ℂ) * Complex.I) + 2 * (π : ℂ) * Complex.I := by
        intro θ; push_cast; ring
      have hexpper : ∀ θ : ℝ, Complex.exp ((ξ : ℂ) + ((θ + 2 * π : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := fun θ => hgper θ
      have hgNSper : Function.Periodic gNS (2 * π) := fun θ => by
        rw [hgNSD]; simp only; rw [hloctwo θ, hEGperC]
      have hgUper : Function.Periodic gU (2 * π) := fun θ => by
        rw [hgUD]; simp only; rw [hexpper θ]
      have hgDEper : Function.Periodic gDE (2 * π) := fun θ => by
        rw [hgDED]; simp only
        rw [hloctwo θ, ← deriv_comp_add_const (expGrad u) (2 * (π : ℂ) * Complex.I),
          (funext fun x => hEGperC x : (fun x : ℂ => expGrad u (x + 2 * (π : ℂ) * Complex.I))
            = expGrad u)]
      set K₁ : Set ℂ := closure (V ∩ RoundAnnulus 0 (Real.exp ζ₁') (Real.exp ζ₂')) with hK₁D
      set A : Set ℝ := Icc (-π) π ∩
        (fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ⁻¹' K₁ with hAD
      have hcexp : Continuous fun θ : ℝ => Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) := by
        fun_prop
      have hAcompact : IsCompact A :=
        isCompact_Icc.inter_right (isClosed_closure.preimage hcexp)
      set bnd : ℝ → ℝ := fun θ => gNS θ + (|gDE θ| + |gU θ|) with hbndD
      have hbndcont : ContinuousOn bnd A := by
        intro θ hθ
        have hmem : Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U := hK hθ.2
        have hmemO : ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ Complex.exp ⁻¹' U := hmem
        have hline : ContinuousAt (fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ := by fun_prop
        have hEG : ContinuousAt (fun t : ℝ => expGrad u ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := expGrad u) (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (expGrad_differentiableAt_open hU hu hmem).continuousAt hline
        have hexpθ : ContinuousAt (fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I)) θ :=
          ContinuousAt.comp (g := Complex.exp)
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            Complex.continuous_exp.continuousAt hline
        have hNS : ContinuousAt gNS θ := Complex.continuous_normSq.continuousAt.comp hEG
        have hDE : ContinuousAt gDE θ :=
          Complex.continuous_re.continuousAt.comp (ContinuousAt.comp (g := deriv (expGrad u))
            (f := fun t : ℝ => ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (hDEGcont.continuousAt ((hU.preimage Complex.continuous_exp).mem_nhds hmemO)) hline)
        have hUc : ContinuousAt gU θ :=
          ContinuousAt.comp (g := u)
            (f := fun t : ℝ => Complex.exp ((ξ : ℂ) + (t : ℂ) * Complex.I))
            (differentiableAt_of_harmonicOnNhd hu hmem).continuousAt hexpθ
        exact (hNS.add (hDE.abs.add hUc.abs)).continuousWithinAt
      have hbndper : Function.Periodic bnd (2 * π) := fun θ => by
        rw [hbndD]; simp only; rw [hgNSper θ, hgDEper θ, hgUper θ]
      obtain ⟨Cb, hCb⟩ := hAcompact.bddAbove_image hbndcont
      -- transport the arc bound to every superlevel angle (combined exp + bnd periodicity)
      have hHper : Function.Periodic
          (fun θ : ℝ => (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I), bnd θ)) (2 * π) := fun θ => by
        simp only [Prod.mk.injEq]; exact ⟨hgper θ, hbndper θ⟩
      have hAllBdd : ∀ θ : ℝ,
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ →
          gNS θ ≤ Cb ∧ |gDE θ| ≤ Cb ∧ |gU θ| ≤ Cb := by
        intro θ hθV
        obtain ⟨y, hyIco, hyeq⟩ := hHper.exists_mem_Ico hπ2 θ (-π)
        rw [Prod.mk.injEq] at hyeq
        have hyIcc : y ∈ Icc (-π) π := ⟨hyIco.1, le_of_lt (by have := hyIco.2; linarith)⟩
        have hyV : Complex.exp ((ξ : ℂ) + (y : ℂ) * Complex.I) ∈ V := by
          rw [hVdef, ← hyeq.1]; exact hθV
        have hyA : y ∈ A := ⟨hyIcc, subset_closure ⟨hyV, hannmem y⟩⟩
        have hbnd_le : bnd y ≤ Cb := hCb ⟨y, hyA, rfl⟩
        have hbndθ : bnd θ ≤ Cb := hyeq.2 ▸ hbnd_le
        rw [hbndD] at hbndθ; simp only at hbndθ
        refine ⟨?_, ?_, ?_⟩
        · nlinarith [abs_nonneg (gDE θ), abs_nonneg (gU θ)]
        · nlinarith [Complex.normSq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)),
            abs_nonneg (gU θ)]
        · nlinarith [Complex.normSq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)),
            abs_nonneg (gDE θ)]
      have hbdd : ∃ C : ℝ, ∀ θ : ℝ,
          Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ superLevelU U u δ →
          Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)) ≤ C
          ∧ |(deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re| ≤ C :=
        ⟨Cb, fun θ hθV => ⟨(hAllBdd θ hθV).1, (hAllBdd θ hθV).2.1⟩⟩
      -- integrabilities on the slice `S`
      have hIntNS : IntegrableOn gNS S := hEIntδ
      have hIntRe2 : IntegrableOn (fun θ => gRe θ ^ 2) S := by
        refine Integrable.mono' hIntNS
          ((ContinuousOn.aestronglyMeasurable (fun θ hθ =>
            ((hcontReadings θ hθ).1.pow 2).continuousWithinAt) hSmeas)) ?_
        filter_upwards [ae_restrict_mem hSmeas] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hgReD, hgNSD]; simp only
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im]
      have hIntIm2 : IntegrableOn
          (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2) S := by
        refine Integrable.mono' hIntNS
          ((ContinuousOn.aestronglyMeasurable (fun θ hθ =>
            ((hcontReadings θ hθ).2.2.2.2.pow 2).continuousWithinAt) hSmeas)) ?_
        filter_upwards [ae_restrict_mem hSmeas] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hgNSD]; simp only
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re]
      have hIntProd : IntegrableOn (fun θ => (gU θ - δ) * gDE θ) S := by
        refine (integrableOn_const hSfin (C := (Cb + δ) * Cb)).mono'
          ((ContinuousOn.aestronglyMeasurable (fun θ hθ =>
            (((hcontReadings θ hθ).2.1.sub continuousAt_const).mul
              (hcontReadings θ hθ).2.2.1).continuousWithinAt) hSmeas)) ?_
        filter_upwards [ae_restrict_mem hSmeas] with θ hθ
        have hb := hAllBdd θ hθ.2
        rw [Real.norm_eq_abs, abs_mul]
        have hU1 : |gU θ - δ| ≤ Cb + δ := by
          rw [hgUD] at hb ⊢
          have := hb.2.2
          rw [abs_le] at this ⊢
          constructor <;> [linarith [this.1, hδ.le]; linarith [this.2]]
        have hD1 : |gDE θ| ≤ Cb := hb.2.1
        have hCbnn : (0 : ℝ) ≤ Cb := le_trans (abs_nonneg _) hb.2.1
        exact mul_le_mul hU1 hD1 (abs_nonneg _) (by linarith [hCbnn, hδ.le])
      -- assemble
      have hPmeas' : MeasurableSet P := (hVopen.preimage (by fun_prop)).measurableSet
      have hLHS : (∫ θ in (-π)..π, F' θ)
          = ∫ θ in S, (gRe θ ^ 2 + (gU θ - δ) * gDE θ) := by
        have hF'eq : F' = P.indicator (fun θ => gRe θ ^ 2 + (gU θ - δ) * gDE θ) := by
          funext θ; rw [hF'def]; rfl
        rw [hF'eq, ← integral_Ioo_eq_intervalIntegral (by linarith : -π ≤ π),
          setIntegral_indicator hPmeas', ← hSP]
      have hsplit : (∫ θ in S, (gRe θ ^ 2 + (gU θ - δ) * gDE θ))
          = (∫ θ in S, gRe θ ^ 2) + ∫ θ in S, (gU θ - δ) * gDE θ := by
        exact MeasureTheory.integral_add hIntRe2 hIntProd
      have hposEq : (∫ θ in S, (gU θ - δ) * gDE θ)
          = ∫ θ in angularSliceδ U u δ ξ,
            (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
              * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re := by
        rw [hSdef]
        refine setIntegral_congr_fun (isOpen_angularSliceδ hU hu δ ξ).measurableSet
          (fun θ hθ => ?_)
        rw [hgUD, hgDED]; simp only
        rw [posPart_eq_self.mpr (by linarith [hθ.2.2] : (0:ℝ)
          ≤ u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)]
      have hIBP :
          (∫ θ in angularSliceδ U u δ ξ,
              (u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I)) - δ)⁺
                * (deriv (expGrad u) ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re)
            = ∫ θ in angularSliceδ U u δ ξ,
              (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 :=
        setIntegral_slice_posPart_re_deriv_expGrad hU hu hcontR hEsc hbdd
      have hcomb : (∫ θ in S, gNS θ)
          = (∫ θ in S, gRe θ ^ 2)
            + ∫ θ in S, (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).im ^ 2 := by
        rw [← MeasureTheory.integral_add hIntRe2 hIntIm2]
        refine setIntegral_congr_fun hSmeas (fun θ _ => ?_)
        rw [hgNSD, hgReD]; simp only
        rw [Complex.normSq_apply]; ring
      rw [hLHS, hsplit, hposEq, hIBP, ← hSdef, ← hcomb, sliceEnergyU, hSdef,
        angularSliceδ_eq, hVdef]
    rw [hleft, hright] at hDUI
    exact hDUI.2
  · -- `hF_meas`
    filter_upwards [Metric.ball_mem_nhds ξ hr0] with x hx
    have hxIoo : x ∈ Ioo ζ₁' ζ₂' := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hx
      exact hrsub ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [Set.uIoc_of_le (by linarith : -π ≤ π)]
    exact ((continuousOn_slice_of_continuousOn_stripBox hcontH hxIoo.1 hxIoo.2).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · -- `hF_int` at `ξ`
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by linarith : -π ≤ π)]
    exact hsliceIcc ξ ⟨hζ₁'lt, hξlt2⟩
  · -- `hF'_meas`
    exact hF'meas
  · -- `h_lipsch`: per-θ Lipschitz in `x` on the ball, uniform in θ (from the slab constant)
    refine Eventually.of_forall (fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by linarith : -π ≤ π)] at hθ
    have hθIcc : θ ∈ Icc (-π) π := Ioc_subset_Icc_self hθ
    rw [show Real.nnabs (K₀ : ℝ) = K₀ from by
      rw [Real.nnabs_of_nonneg (NNReal.coe_nonneg K₀), Real.toNNReal_coe]]
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hd := (lipschitzOnWith_iff_dist_le_mul.mp hK₀)
      _ (hslabmem x hx θ hθIcc) _ (hslabmem y hy θ hθIcc)
    rw [Real.dist_eq, Complex.dist_eq,
      show ((x : ℂ) + (θ : ℂ) * Complex.I) - ((y : ℂ) + (θ : ℂ) * Complex.I) = (x - y : ℝ) by
        push_cast; ring, Complex.norm_real, ← Real.dist_eq] at hd
    exact hd
  · -- `bound_integrable`
    exact _root_.intervalIntegrable_const
  · -- `h_diff`: a.e.-θ radial derivative off the level set (helper 1)
    have haeπ : ∀ᵐ θ : ℝ, θ ≠ π :=
      MeasureTheory.ae_iff.mpr (by simp only [not_ne_iff, setOf_eq_eq_singleton,
        MeasureTheory.measure_singleton])
    filter_upwards [hae_ne, haeπ] with θ hθne hθπ hθΙ
    rw [Set.uIoc_of_le (by linarith : -π ≤ π)] at hθΙ
    have hθIoo : θ ∈ Ioo (-π) π := ⟨hθΙ.1, lt_of_le_of_ne hθΙ.2 hθπ⟩
    exact hasDerivAt_windowedTruncIntegrand_radial hU hu hK ⟨hζ₁'lt, hξlt2⟩
      (Ioc_subset_Icc_self hθΙ) (hθne hθIoo)

/-- **Truncated-flux increment bounded by the total energy.** For `u` harmonic on the open set `U`
with `gradC u` nowhere locally zero, with `θ ↦ u (e^{ξ+iθ})` continuous at every log-radius, `u`
continuous on `closure U` and vanishing on the part of `frontier U` inside the unit disc, with the
slice squared gradient integrable on every superlevel slice and total energy finite, every `δ > 0`
and every window `{e^{ζ₁} < |z| < e^{ζ₂}}` with `ζ₁ ≤ ζ₂ < 0` has truncated-flux increment at
most the total Dirichlet energy `D(u; U)`.  The window's superlevel intersection is then
automatically compactly contained in `U` (`closure_superLevel_window_subset`), rather than being
assumed.  The truncated flux is the fixed-window flux of the continuous truncated integrand; its
`ξ`-FTC integrates the superlevel-slice energy, which is the window energy of `{u > δ} ∩ U`,
monotone below `D(u; U)`. -/
theorem truncRoughFlux_sub_le_dirichletEnergy {u : ℂ → ℝ} {U : Set ℂ} {δ ζ₁ ζ₂ : ℝ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSliceδ U u δ ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤)
    (hδ : 0 < δ) (h12 : ζ₁ ≤ ζ₂) (hζ₂ : ζ₂ < 0) :
    truncRoughFlux u U δ ζ₂ - truncRoughFlux u U δ ζ₁ ≤ (dirichletEnergy u U).toReal := by
  set V : Set ℂ := superLevelU U u δ with hV
  have hVopen : IsOpen V := isOpen_superLevelU hU hu δ
  -- the superlevel-slice energy is the fixed-window flux derivative value
  set E : ℝ → ℝ := fun ξ => sliceEnergyU u V ξ with hE
  have hEnn : ∀ ξ, 0 ≤ E ξ := fun ξ =>
    setIntegral_nonneg (isOpen_angularSlice hVopen ξ).measurableSet
      fun θ _ => Complex.normSq_nonneg _
  -- The moving-domain flux-energy FTC for the truncated flux.
  -- Route (absolute-continuity FTC, avoiding an every-point radial derivative):
  --   (1) truncRoughFlux u U d . = the theta-integral of windowedTruncIntegrand (.+theta i) on the
  --       window (windowedTruncIntegrand is continuous on the strip box, by
  --       continuousOn_windowedTruncIntegrand, and its radial (u-d)^+ / Re expGrad factors are
  --       Lipschitz on the compact slab K = closure(V cap window) subset U), so truncRoughFlux u U
  --       d is Lipschitz, hence absolutely continuous on [z1, z2]
  --       (LipschitzOnWith.absolutelyContinuousOnInterval);
  --   (2) AbsolutelyContinuousOnInterval.integral_deriv_eq_sub gives
  --       (integral of deriv (truncRoughFlux u U d)) = truncRoughFlux .. z2 - truncRoughFlux .. z1;
  --   (3) for a.e. xi, the strip-box Lipschitz DUI
  --       (hasDerivAt_integral_of_dominated_loc_of_lip) yields
  --       HasDerivAt (truncRoughFlux u U d) (E xi) xi: its radial product rule gives
  --       (Re expGrad)^2 + (u-d)^+ * Re (deriv expGrad) on the slice and 0 off it, whose slice
  --       integral is E xi after setIntegral_slice_posPart_re_deriv_expGrad; therefore
  --       deriv (truncRoughFlux u U d) = E a.e. and (integral of deriv) = (integral of E).
  -- STEP A (LANDED): a.e.-xi angular slice nullity (`levelSet_volume_zero` +
  -- `ae_angularSlice_levelSet_null`), which needs `u` nowhere locally gradient-constant on `U`.
  -- STEP B (LANDED): `truncRoughFlux_eq_integral_windowedTruncIntegrand`.
  -- STEP C (LANDED): the branch-cut-free theta-IBP
  -- `setIntegral_slice_posPart_re_deriv_expGrad`:
  --   `int_slice (u-d)^+ Re(deriv expGrad) = int_slice (Im expGrad)^2`, valid even when `{u>d}`
  -- straddles the +-pi cut (full-circle case = periodic IBP
  -- `integral_full_posPart_re_deriv_expGrad`; proper case = rotate to a window `(a, a+2pi)` whose
  -- seam escapes `{u>d}`, arc-decompose via `setIntegral_windowSlice_posPart_re_deriv_expGrad`,
  -- transfer back by 2pi-periodicity).
  --
  -- REMAINING (DUI + AC-FTC assembly, still to be built):
  --   (i) `truncRoughFlux u U d` is Lipschitz on `[z1, z2]` (strip-box bound of the xi-partial of
  --       `windowedTruncIntegrand` on the compact slab K = closure(V cap window) subset U), hence
  --       AC (`LipschitzOnWith.absolutelyContinuousOnInterval`);
  --   (ii) at a.e. xi the strip-box Lipschitz DUI
  --       (`hasDerivAt_integral_of_dominated_loc_of_lip`) gives `HasDerivAt (truncRoughFlux u U d)`
  --       with value `int_theta [1_{u>d}(Re expGrad)^2 + (u-d)^+ Re(deriv expGrad)]` (off the null
  --       level slice from STEP A the posPart is locally smooth), which STEP C rewrites to `E xi`;
  --   (iii) so `deriv (truncRoughFlux u U d) = E` a.e., and
  --       `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` closes the FTC.
  -- STEP A needs `u` nowhere locally gradient-constant on `U`, a hypothesis absent from this
  -- theorem (it must be threaded from the ring data of `slope_le_energy_ringPotential'''`).
  have hFTC : truncRoughFlux u U δ ζ₂ - truncRoughFlux u U δ ζ₁ = ∫ ξ in ζ₁..ζ₂, E ξ := by
    -- level-set nullity: a.e.-ξ the angular slice meets `{u = δ}` in a null set
    have hLmeas : MeasurableSet {z : ℂ | z ∈ U ∧ u z = δ} := by
      have hopen : IsOpen (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) :=
        hu.continuousOn.isOpen_inter_preimage hU isOpen_ne
      have : {z : ℂ | z ∈ U ∧ u z = δ} = U \ (U ∩ u ⁻¹' {x : ℝ | x ≠ δ}) := by
        ext z; simp only [mem_setOf_eq, mem_diff, mem_inter_iff, mem_preimage, mem_setOf_eq]
        constructor
        · rintro ⟨hzU, hzδ⟩; exact ⟨hzU, fun h => h.2 hzδ⟩
        · rintro ⟨hzU, hne⟩; exact ⟨hzU, not_not.mp (fun h => hne ⟨hzU, h⟩)⟩
      rw [this]; exact hU.measurableSet.diff hopen.measurableSet
    have haeslice := ae_angularSlice_levelSet_null hLmeas (levelSet_volume_zero hU hu hnc)
    -- absolute continuity of the truncated flux on `[ζ₁, ζ₂]`
    obtain ⟨L, hL⟩ := lipschitzOnWith_truncRoughFlux hU hu hucont hE0 hδ h12 hζ₂
    have hAC : AbsolutelyContinuousOnInterval (truncRoughFlux u U δ) ζ₁ ζ₂ :=
      hL.absolutelyContinuousOnInterval
    -- a.e.-ξ (within `(ζ₁, ζ₂)`) the flux derivative is `E`
    have hderiv : ∀ᵐ ξ : ℝ, ξ ∈ Ioo ζ₁ ζ₂ →
        deriv (truncRoughFlux u U δ) ξ = E ξ := by
      filter_upwards [haeslice] with ξ hξnull hξIoo
      exact (hasDerivAt_truncRoughFlux_of_slice_null hU hu hucont hE0 (hcontR ξ) (hEInt ξ)
        hδ hζ₂ hξIoo hξnull).deriv
    -- FTC + a.e. derivative identification
    have haeζ₂ : ∀ᵐ ξ : ℝ, ξ ≠ ζ₂ :=
      MeasureTheory.ae_iff.mpr (by
        simp only [not_ne_iff, setOf_eq_eq_singleton, MeasureTheory.measure_singleton])
    rw [← hAC.integral_deriv_eq_sub]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le h12]
    filter_upwards [hderiv, haeζ₂] with ξ hξderiv hξne hξIoc
    exact hξderiv ⟨hξIoc.1, lt_of_le_of_ne hξIoc.2 hξne⟩
  rw [hFTC]
  -- the window integral of the superlevel-slice energy is bounded by the total energy
  have hIooeq : (∫ ξ in ζ₁..ζ₂, E ξ) = ∫ ξ in Ioo ζ₁ ζ₂, E ξ :=
    (integral_Ioo_eq_intervalIntegral h12 E).symm
  rw [hIooeq]
  -- `ofReal (∫_{Ioo} E) ≤ ∫⁻_{Ioo} ofReal E ≤ ∫⁻_{Iic ζ₂} ofReal E ≤ D(V) ≤ D(U)`
  have hVU : dirichletEnergy u V ≤ dirichletEnergy u U := dirichletEnergy_mono (fun z hz => hz.1)
  have htail : (∫⁻ ξ in Iic ζ₂, ENNReal.ofReal (E ξ)) ≤ dirichletEnergy u U :=
    le_trans (setLIntegral_tail_ofReal_sliceEnergyU_le hVopen ζ₂) hVU
  have hIoosub : Ioo ζ₁ ζ₂ ⊆ Iic ζ₂ := fun ξ hξ => hξ.2.le
  have hofReal : ENNReal.ofReal (∫ ξ in Ioo ζ₁ ζ₂, E ξ) ≤ dirichletEnergy u U := by
    calc ENNReal.ofReal (∫ ξ in Ioo ζ₁ ζ₂, E ξ)
        ≤ ∫⁻ ξ in Ioo ζ₁ ζ₂, ENNReal.ofReal (E ξ) :=
          ofReal_setIntegral_le_setLIntegral_ofReal measurableSet_Ioo (fun ξ _ => hEnn ξ)
      _ ≤ ∫⁻ ξ in Iic ζ₂, ENNReal.ofReal (E ξ) := lintegral_mono_set hIoosub
      _ ≤ dirichletEnergy u U := htail
  -- pull `.toReal` through the `ofReal` bound (both sides nonnegative)
  have hEint_nonneg : 0 ≤ ∫ ξ in Ioo ζ₁ ζ₂, E ξ :=
    setIntegral_nonneg measurableSet_Ioo (fun ξ _ => hEnn ξ)
  have := ENNReal.toReal_mono hDfin hofReal
  rwa [ENNReal.toReal_ofReal hEint_nonneg] at this

/-- **The windowed increment inequality from the truncated-flux increment bound.** For `u` harmonic
and strictly positive on the open set `U`, uniformly bounded by `1` on `U`, continuous on
`closure U`, vanishing on the part of `frontier U` inside the unit disc, with the slice squared
gradient integrable on every superlevel slice and finite total Dirichlet energy, the rough-flux
increment is bounded by `D(u; U)` on every window `ζ₁ ≤ ζ₂ < 0`.  The truncated-flux increment is
bounded by `D(u; U)` on each window (`truncRoughFlux_sub_le_dirichletEnergy`), and the
truncated-flux recovery of the rough flux (`roughFlux_sub_le_of_truncRoughFlux_sub_le`) passes to
`δ → 0`.  This is
the windowed increment inequality `hwin` consumed by `slope_le_energy_ringPotential'`, discharged
without the level-set δ-increment residual `hδwin`. -/
theorem roughFlux_sub_le_dirichletEnergy_trunc {u : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤) :
    ∀ ζ₁ ζ₂ : ℝ, ζ₁ ≤ ζ₂ → ζ₂ < 0 →
      roughFlux u U ζ₂ - roughFlux u U ζ₁ ≤ (dirichletEnergy u U).toReal := by
  intro ζ₁ ζ₂ h12 hζ₂
  -- the uniform `|u| ≤ 1` slice bound
  have hbdd : ∀ ξ : ℝ, ∀ θ ∈ angularSlice U ξ,
      |u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))| ≤ 1 := by
    intro ξ θ hθ
    obtain ⟨hnn, hle⟩ := hrangeU _ hθ.2
    rw [abs_of_nonneg hnn]; exact hle
  -- slice radial-derivative integrand integrable at each of the two log-radii
  have hRe : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)).re) (angularSlice U ξ) :=
    fun ξ => integrableOn_slice_re_of_normSq hU hu ξ (hEInt ξ)
  -- the superlevel-slice squared gradient integrability (restrict the full-slice one)
  have hEIntδ : ∀ δ : ℝ, ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSliceδ U u δ ξ) :=
    fun δ ξ => (hEInt ξ).mono_set (angularSliceδ_subset_angularSlice δ ξ)
  refine roughFlux_sub_le_of_truncRoughFlux_sub_le hU hu hpos (by norm_num : (0:ℝ) ≤ 1)
    (hbdd ζ₁) (hbdd ζ₂) (hRe ζ₁) (hRe ζ₂) (fun δ hδ => ?_)
  exact truncRoughFlux_sub_le_dirichletEnergy hU hu hnc hcontR hucont hE0 (hEIntδ δ) hDfin hδ h12
    hζ₂

/-- **Keystone slope bound for a ring potential (windowed increment discharged via the truncated
flux).** The `slope_le_energy_ringPotential'` slope bound `b ≤ D(u; U)` with the windowed increment
hypothesis `hwin` eliminated entirely: it is produced from the truncated-flux increment inequality
`roughFlux_sub_le_dirichletEnergy_trunc` (the fixed-window flux–energy FTC of the truncated
integrand, passed to `δ → 0`).  The remaining hypotheses are the ring-potential data together with
`u > 0` on `U`, continuity on `closure U`, and vanishing on the inner frontier. -/
theorem slope_le_energy_ringPotential''' {u : ℂ → ℝ} {U : Set ℂ} {r₀ b : ℝ}
    (h0 : 0 < r₀) (h1 : r₀ < 1)
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (hpos : ∀ z ∈ U, 0 < u z)
    (hnc : ∀ z ∈ U, ¬ (∀ᶠ w in nhds z, gradC u w = 0))
    (hcontR : ∀ ξ : ℝ, Continuous (fun θ : ℝ => u (Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I))))
    (hcollar : ∀ ξ : ℝ, Real.log r₀ < ξ → ξ < 0 → ∀ θ : ℝ,
      Complex.exp ((ξ : ℂ) + (θ : ℂ) * Complex.I) ∈ U)
    (hucollar : InnerProductSpace.HarmonicOnNhd u (RoundAnnulus 0 r₀ 1))
    (hcont : ContinuousOn u {z : ℂ | r₀ ≤ dist z 0 ∧ dist z 0 ≤ 1})
    (hone : ∀ z ∈ grotzschOuter, u z = 1)
    (hrange : ∀ z ∈ RoundAnnulus 0 r₀ 1, 0 ≤ u z ∧ u z ≤ 1)
    (hslope : ∀ ξ ∈ Ioo (Real.log r₀) 0, logCircleMean 0 u ξ = 2 * π + b * ξ)
    (hrangeU : ∀ z ∈ U, 0 ≤ u z ∧ u z ≤ 1)
    (hucont : ContinuousOn u (closure U))
    (hE0 : ∀ z ∈ frontier U, ‖z‖ < 1 → u z = 0)
    (hEInt : ∀ ξ : ℝ, IntegrableOn
      (fun θ : ℝ => Complex.normSq (expGrad u ((ξ : ℂ) + (θ : ℂ) * Complex.I)))
      (angularSlice U ξ))
    (hDfin : dirichletEnergy u U ≠ ⊤) :
    b ≤ (dirichletEnergy u U).toReal :=
  slope_le_energy_ringPotential' h0 h1 hU hu hcollar hucollar hcont hone hrange hslope hrangeU hDfin
    (roughFlux_sub_le_dirichletEnergy_trunc hU hu hpos hnc hcontR hrangeU hucont hE0 hEInt hDfin)

end RiemannDynamics
