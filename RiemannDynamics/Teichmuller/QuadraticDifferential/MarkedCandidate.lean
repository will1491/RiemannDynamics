import RiemannDynamics.Teichmuller.QuadraticDifferential.Def

/-!
# The group-marked candidate class and the intrinsic Teichmüller metric

A quasiconformal plane map matching the boundary transition of a pair of Teichmüller
representatives need not respect the group markings: `teichPseudoDist` is the universal
(boundary-value) pseudometric, and by the Poincaré theta-series contraction over a
nonamenable cover its extremal problem is strictly smaller than the equivariant one. The
intrinsic Teichmüller metric of the base is `teichDistG`, the extremal problem over
candidates carrying two-sided group compatibility. The two metrics satisfy
`teichPseudoDist ≤ teichDistG`; they are not equal.

* `IsMarkedCandidate` — boundary transition plus two-sided group compatibility on the
  upper half plane.
* `gDilatationSet`, `teichDistG` — the equivariant dilatation set and its `½ log sInf`.
* `IsTeichmullerCandidate` — a candidate of Teichmüller form in direction `q`, modulus `k`.
* `teichDistG_le_of_candidate`, `teichDistG_self`, `teichPseudoDist_le_teichDistG`,
  `teichDistG_eq_zero_iff_boundary` — the pseudometric tier and its rigidity.
* `Teich.distG` — the descended distance function on Teichmüller space.
* `mem_gDilatationSet_smulUpper`, `teichDistG_smulUpper` — re-markings act by isometries.
* `mumford_dG_subconvergence` — Mumford subconvergence in the intrinsic metric.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## The candidate class and the intrinsic distance -/

/-- A **group-marked candidate** for the pair `(x, y)`: a plane map matching the boundary
transition `F ∘ y.w = x.w` on `ℝ` and intertwining the marked Fuchsian groups on the upper
half plane, with both a forward and a backward compatibility clause. -/
def IsMarkedCandidate (x y : TeichRep Γ₀) (F : ℂ → ℂ) : Prop :=
  (∀ t : ℝ, F (y.w t) = x.w t) ∧
  (∀ W ∈ y.group, ∃ W' ∈ x.group, ∀ z : ℂ, 0 < z.im →
    F (moebiusMap W z) = moebiusMap W' (F z)) ∧
  (∀ W' ∈ x.group, ∃ W ∈ y.group, ∀ z : ℂ, 0 < z.im →
    F (moebiusMap W z) = moebiusMap W' (F z))

/-- The **equivariant dilatation set** of a pair: the dilatations of quasiconformal
group-marked candidates. -/
def gDilatationSet (x y : TeichRep Γ₀) : Set ℝ :=
  {K | ∃ F : ℂ → ℂ, IsQCGeometric F K ∧ IsMarkedCandidate x y F}

/-- The **intrinsic Teichmüller distance** of the base: `½ log` of the least dilatation of
a quasiconformal group-marked candidate. It dominates the boundary-value pseudometric
`teichPseudoDist` and is the metric in which Teichmüller extremality holds. -/
noncomputable def teichDistG (x y : TeichRep Γ₀) : ℝ :=
  (1 / 2) * Real.log (sInf (gDilatationSet x y))

/-- A **Teichmüller-form candidate** for the pair `(x, y)` in the direction of the
quadratic differential `q` on the domain group, with modulus `k`: a group-marked candidate
of dilatation `(1 + k)/(1 − k)` whose Beltrami coefficient is `k q̄/|q|` almost everywhere
on the upper half plane. -/
def IsTeichmullerCandidate (x y : TeichRep Γ₀) (q : QuadraticDifferential y.group)
    (k : ℝ) (F : ℂ → ℂ) : Prop :=
  IsMarkedCandidate x y F ∧ IsQCGeometric F ((1 + k) / (1 - k)) ∧
  ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
    dzbar F z = teichmullerCoeffFun q k z * dz F z

/-! ## The pseudometric tier -/

/-- Every marked candidate is a boundary candidate: the equivariant dilatation set sits
inside the universal one. -/
theorem mem_dilatationSet_of_mem_gDilatationSet {x y : TeichRep Γ₀} {K : ℝ}
    (hK : K ∈ gDilatationSet x y) : K ∈ dilatationSet x y := by
  obtain ⟨F, hF, hc⟩ := hK
  exact ⟨F, hF, hc.1⟩

/-- Every equivariant dilatation is at least `1`. -/
theorem one_le_of_mem_gDilatationSet {x y : TeichRep Γ₀} {K : ℝ}
    (hK : K ∈ gDilatationSet x y) : 1 ≤ K := by
  obtain ⟨F, hF, -⟩ := hK
  exact hF.1

/-- The equivariant dilatation set is bounded below by `1`. -/
theorem bddBelow_gDilatationSet (x y : TeichRep Γ₀) : BddBelow (gDilatationSet x y) :=
  ⟨1, fun _ hK => one_le_of_mem_gDilatationSet hK⟩

/-- The identity map has dilatation `1`. -/
theorem isQCGeometric_id : IsQCGeometric id 1 := by
  have hn : BeltramiCoeff.zero.normInf = 0 := by
    simp [BeltramiCoeff.normInf, BeltramiCoeff.zero]
  have hzero : BeltramiCoeff.zero.K = 1 := by
    rw [BeltramiCoeff.K, hn]
    norm_num
  have h := isQCAnalytic_id.isQCGeometric_K
  rwa [hzero] at h

/-- The identity is a marked candidate between representatives with equal boundary
values. -/
theorem isMarkedCandidate_id {x y : TeichRep Γ₀} (hxy : ∀ t : ℝ, x.w t = y.w t) :
    IsMarkedCandidate x y id := by
  have hg : x.group = y.group := TeichRep.group_eq_of_boundary_eq
    (funext fun t => by simp only [TeichRep.boundary, hxy t])
  refine ⟨fun t => (hxy t).symm, fun W hW => ⟨W, ?_, fun z _ => rfl⟩,
    fun W' hW' => ⟨W', ?_, fun z _ => rfl⟩⟩
  · rw [hg]; exact hW
  · rw [← hg]; exact hW'

/-- One marked candidate bounds the intrinsic distance. -/
theorem teichDistG_le_of_candidate {x y : TeichRep Γ₀} {F : ℂ → ℂ} {K : ℝ}
    (hF : IsQCGeometric F K) (hc : IsMarkedCandidate x y F) :
    teichDistG x y ≤ (1 / 2) * Real.log K := by
  have hmem : K ∈ gDilatationSet x y := ⟨F, hF, hc⟩
  have hle : sInf (gDilatationSet x y) ≤ K :=
    csInf_le (bddBelow_gDilatationSet x y) hmem
  have hpos : (0 : ℝ) < sInf (gDilatationSet x y) := lt_of_lt_of_le one_pos
    (le_csInf ⟨K, hmem⟩ fun _ h => one_le_of_mem_gDilatationSet h)
  have hlog : Real.log (sInf (gDilatationSet x y)) ≤ Real.log K :=
    Real.log_le_log hpos hle
  unfold teichDistG
  linarith

/-- The intrinsic distance is nonnegative. -/
theorem teichDistG_nonneg (x y : TeichRep Γ₀) : 0 ≤ teichDistG x y := by
  unfold teichDistG
  rcases (gDilatationSet x y).eq_empty_or_nonempty with he | hne
  · rw [he, Real.sInf_empty, Real.log_zero, mul_zero]
  · have h1 : 1 ≤ sInf (gDilatationSet x y) :=
      le_csInf hne fun _ hK => one_le_of_mem_gDilatationSet hK
    have h2 := Real.log_nonneg h1
    linarith

/-- The intrinsic distance from a representative to itself vanishes. -/
theorem teichDistG_self (x : TeichRep Γ₀) : teichDistG x x = 0 := by
  have hmem : (1 : ℝ) ∈ gDilatationSet x x :=
    ⟨id, isQCGeometric_id, isMarkedCandidate_id fun _ => rfl⟩
  have h1 : sInf (gDilatationSet x x) ≤ 1 :=
    csInf_le (bddBelow_gDilatationSet x x) hmem
  have h2 : 1 ≤ sInf (gDilatationSet x x) :=
    le_csInf ⟨1, hmem⟩ fun _ hK => one_le_of_mem_gDilatationSet hK
  unfold teichDistG
  rw [le_antisymm h1 h2, Real.log_one, mul_zero]

/-- A plane point with vanishing imaginary part is the coercion of its real part. -/
theorem eq_ofReal_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

/-- An orientation-preserving plane homeomorphism fixing every real point maps the open
upper half plane into itself. -/
theorem mapsTo_upper_of_fixes_real {G : ℂ → ℂ}
    (hOP : OrientationPreservingHomeo G) (hid : ∀ t : ℝ, G (t : ℂ) = (t : ℂ)) :
    ∀ z : ℂ, 0 < z.im → 0 < (G z).im := by
  have hhom : IsHomeomorph G := hOP.1
  have hcont : Continuous G := hhom.continuous
  have hinj : Function.Injective G := hhom.injective
  have hsurj : Function.Surjective G := hhom.bijective.surjective
  -- fixed real axis: the image of a point is real exactly when the point is real
  have hreal_iff : ∀ z : ℂ, (G z).im = 0 ↔ z.im = 0 := by
    intro z
    constructor
    · intro h0
      have h1 : G z = (((G z).re : ℝ) : ℂ) := eq_ofReal_of_im_eq_zero h0
      have h2 : G z = G (((G z).re : ℝ) : ℂ) := by rw [hid ((G z).re)]; exact h1
      have h3 := hinj h2
      rw [h3]
      simp
    · intro h0
      rw [eq_ofReal_of_im_eq_zero h0, hid z.re]
      simp
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hdisj : Disjoint {z : ℂ | 0 < z.im} {z : ℂ | z.im < 0} := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : 0 < z.im := hz1
    have h2 : z.im < 0 := hz2
    linarith
  have himsubU : G '' {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
    rintro u ⟨z, hzU, rfl⟩
    have hzne : z.im ≠ 0 := ne_of_gt hzU
    have hne : (G z).im ≠ 0 := fun h => hzne ((hreal_iff z).mp h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hpreU : IsPreconnected (G '' {z : ℂ | 0 < z.im}) :=
    ((convex_halfSpace_im_gt 0).isPreconnected).image _ hcont.continuousOn
  rcases hpreU.subset_or_subset hUopen hLopen hdisj himsubU with hUU | hUL
  · exact fun z hz => hUU ⟨z, hz, rfl⟩
  -- the flip branch: the upper half plane goes down, and is excluded by orientation
  exfalso
  have hneg : ∀ z : ℂ, 0 < z.im → (G z).im < 0 := fun z hz => hUL ⟨z, hz, rfl⟩
  -- the lower half plane goes up
  have hneg' : ∀ z : ℂ, z.im < 0 → 0 < (G z).im := by
    obtain ⟨ζ, hζ⟩ := hsurj Complex.I
    have hζL : ζ.im < 0 := by
      rcases lt_trichotomy ζ.im 0 with h | h | h
      · exact h
      · exfalso
        have h1 : G ζ = ζ := by
          rw [eq_ofReal_of_im_eq_zero h, hid ζ.re]
        rw [hζ] at h1
        have h2 : (Complex.I).im = ζ.im := by rw [← h1]
        simp [h] at h2
      · exfalso
        have h1 := hneg ζ h
        rw [hζ] at h1
        simp at h1
        linarith
    have himsubL : G '' {z : ℂ | z.im < 0} ⊆ {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im < 0} := by
      rintro u ⟨z, hzL, rfl⟩
      have hzne : z.im ≠ 0 := ne_of_lt hzL
      have hne : (G z).im ≠ 0 := fun h => hzne ((hreal_iff z).mp h)
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hpreL : IsPreconnected (G '' {z : ℂ | z.im < 0}) :=
      ((convex_halfSpace_im_lt 0).isPreconnected).image _ hcont.continuousOn
    rcases hpreL.subset_or_subset hUopen hLopen hdisj himsubL with hLU | hLL
    · exact fun z hz => hLU ⟨z, hz, rfl⟩
    · exfalso
      have hIm : Complex.I ∈ G '' {z : ℂ | z.im < 0} := ⟨ζ, hζL, hζ⟩
      have h1 : (Complex.I).im < 0 := hLL hIm
      simp at h1
      linarith
  have hG0 : G 0 = 0 := by
    have h := hid 0
    simpa using h
  have hG1 : G 1 = 1 := by
    have h := hid 1
    simpa using h
  -- winding-number extensionality helper
  have hwn_ext : ∀ (A B : C(unitInterval, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  -- the packaged homeomorphism and its plane chart
  set W : ℂ ≃ₜ ℂ := hhom.homeomorph G
  set E : OpenPartialHomeomorph ℂ ℂ := W.toOpenPartialHomeomorph
  have hEsrc : E.source = Set.univ := Homeomorph.toOpenPartialHomeomorph_source W
  -- the self-charted plane has an oriented atlas
  have hatlas : HasOrientedAtlas ℂ := by
    intro e1 he1 e2 he2 z hz
    rw [chartedSpaceSelf_atlas] at he1 he2
    subst he1
    subst he2
    have hEq : Set.EqOn
        ((OpenPartialHomeomorph.refl ℂ).symm.trans (OpenPartialHomeomorph.refl ℂ)) id
        Set.univ := fun w _ => rfl
    have hsrc : ((OpenPartialHomeomorph.refl ℂ).symm.trans
        (OpenPartialHomeomorph.refl ℂ)).source = Set.univ := by
      simp
    exact isOrientationPreservingAt_id hEq isOpen_univ (Set.mem_univ z)
      (fun w _ => by rw [hsrc]; trivial)
  -- source of the chart representatives
  have hhsrc : ∀ p : ℂ, (homeoChartRep W p).source = Set.univ := by
    intro p
    unfold homeoChartRep
    rw [chartAt_self_eq]
    simp [Homeomorph.toOpenPartialHomeomorph_source]
  -- a point of differentiability with positive Jacobian
  obtain ⟨z₀, hdet⟩ := hOP.2.exists
  have hdiff : DifferentiableAt ℝ G z₀ := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
    simp [ContinuousLinearMap.det] at hdet
  -- a positive radius whose image circle admits a `+2πi` logarithm lift
  have hev := (windingOne_iff_det_pos hcont hdiff (ne_of_gt hdet)).mpr hdet
  have hev' : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ((∃ L : ℝ → ℂ, Continuous L ∧
        (∀ θ : ℝ, Complex.exp (L θ)
          = G (z₀ + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - G z₀) ∧
        L (2 * Real.pi) - L 0 = 2 * (Real.pi : ℂ) * Complex.I) ∧ 0 < r) :=
    hev.and (eventually_mem_nhdsWithin.mono fun r hr => hr)
  obtain ⟨r₀, ⟨L₀, hL₀c, hL₀e, hL₀incr⟩, hr₀pos⟩ := hev'.exists
  -- the image circle of radius `r₀` about `z₀` as a loop
  have hγ₀cont : Continuous fun t : unitInterval => G (circleLoop z₀ r₀ t) :=
    hcont.comp (circleLoop z₀ r₀).continuous
  set γ₀ : C(unitInterval, ℂ) :=
    ⟨fun t => G (circleLoop z₀ r₀ t), hγ₀cont⟩
  have hcircν : ∀ t : unitInterval, circleLoop z₀ r₀ t
      = z₀ + (r₀ : ℝ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := fun t => rfl
  have hγ₀cl : γ₀ 0 = γ₀ 1 := by
    change G (circleLoop z₀ r₀ 0) = G (circleLoop z₀ r₀ 1)
    rw [hcircν 0, hcircν 1]
    norm_num [Complex.exp_two_pi_mul_I]
  have hγ₀ne : ∀ t : unitInterval, γ₀ t ≠ G z₀ := by
    intro t heq
    have h1 : circleLoop z₀ r₀ t = z₀ := hinj heq
    rw [hcircν t] at h1
    have h2 : (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (ne_of_gt hr₀pos) (Complex.ofReal_eq_zero.mp h3)
    · exact Complex.exp_ne_zero _ h3
  -- the `[0, 2π]` lift reparametrized over the unit interval
  have hMcont : Continuous fun t : unitInterval => L₀ (2 * Real.pi * (t : ℝ)) :=
    hL₀c.comp (continuous_const.mul continuous_subtype_val)
  set M : C(unitInterval, ℂ) :=
    ⟨fun t => L₀ (2 * Real.pi * (t : ℝ)), hMcont⟩
  have hM : IsLogLiftOf M (shiftedCurve γ₀ (G z₀)) := by
    intro t
    have hs : shiftedCurve γ₀ (G z₀) t = γ₀ t - G z₀ := by
      simp [shiftedCurve]
    change Complex.exp (L₀ (2 * Real.pi * (t : ℝ))) = shiftedCurve γ₀ (G z₀) t
    rw [hs, hL₀e (2 * Real.pi * (t : ℝ))]
    have harg : ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I
        = 2 * Real.pi * Complex.I * ((t : ℝ) : ℂ) := by
      push_cast
      ring
    have hpt : z₀ + (r₀ : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)
        = circleLoop z₀ r₀ t := by
      rw [hcircν t, harg]
    rw [hpt]
    rfl
  -- the winding number of the image circle about the image centre is one
  have hspec₀ := windingNumber_spec hγ₀cl hγ₀ne hM
  have hM1 : M 1 = L₀ (2 * Real.pi) := by
    change L₀ (2 * Real.pi * (((1 : unitInterval) : ℝ))) = L₀ (2 * Real.pi)
    norm_num
  have hM0 : M 0 = L₀ 0 := by
    change L₀ (2 * Real.pi * (((0 : unitInterval) : ℝ))) = L₀ 0
    norm_num
  rw [hM1, hM0, hL₀incr] at hspec₀
  have hwn₀ : windingNumber γ₀ (G z₀) = 1 := by
    have h2ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : ((windingNumber γ₀ (G z₀) : ℤ) : ℂ) = 1 := by
      field_simp at hspec₀
      exact_mod_cast hspec₀.symm
    exact_mod_cast h3
  -- orientation preservation at `z₀`, hence at the chart representative
  have hsub₀ : Metric.closedBall z₀ r₀ ⊆ E.source := by
    rw [hEsrc]
    exact Set.subset_univ _
  have hOPz₀ : IsOrientationPreservingAt E z₀ := by
    refine ⟨r₀, hr₀pos, hsub₀, ?_⟩
    unfold windingDegreeAt
    exact Eq.trans (hwn_ext _ γ₀ (G z₀) fun t => rfl) hwn₀
  have hchart : IsOrientationPreservingAt (homeoChartRep W z₀) (chartAt ℂ z₀ z₀) := by
    have hEq : Set.EqOn (⇑E) (⇑(homeoChartRep W z₀)) Set.univ := fun w _ => rfl
    exact (isOrientationPreservingAt_congr hEq isOpen_univ (Set.mem_univ z₀)
      (fun w _ => by rw [hEsrc]; trivial)
      (fun w _ => by rw [hhsrc z₀]; trivial)).mp hOPz₀
  -- global propagation to the origin
  have hglob := isOrientationPreserving_of_isOrientationPreservingAt_point hatlas W z₀ hchart
  have h0 : IsOrientationPreservingAt E 0 := by
    have hEq : Set.EqOn (⇑(homeoChartRep W 0)) (⇑E) Set.univ := fun w _ => rfl
    exact (isOrientationPreservingAt_congr hEq isOpen_univ (Set.mem_univ 0)
      (fun w _ => by rw [hhsrc 0]; trivial)
      (fun w _ => by rw [hEsrc]; trivial)).mp (hglob 0)
  -- the unit circle about the origin
  have hγcont : Continuous fun t : unitInterval => G (circleLoop 0 1 t) :=
    hcont.comp (circleLoop 0 1).continuous
  set γ : C(unitInterval, ℂ) := ⟨fun t => G (circleLoop 0 1 t), hγcont⟩
  have hcirc : ∀ t : unitInterval, circleLoop 0 1 t
      = Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro t
    have h : circleLoop 0 1 t
        = 0 + ((1 : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [h]
    norm_num
  have him : ∀ t : unitInterval,
      (circleLoop 0 1 t).im = Real.sin (2 * Real.pi * (t : ℝ)) := by
    intro t
    have harg : 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)
        = ((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hcirc t, harg, Complex.exp_ofReal_mul_I_im]
  have hc0 : circleLoop 0 1 0 = 1 := by
    rw [hcirc 0]
    norm_num
  have hc1 : circleLoop 0 1 1 = 1 := by
    rw [hcirc 1]
    have h1 : (((1 : unitInterval) : ℝ) : ℂ) = 1 := by norm_num
    rw [h1, mul_one, Complex.exp_two_pi_mul_I]
  have hγcl : γ 0 = γ 1 := by
    change G (circleLoop 0 1 0) = G (circleLoop 0 1 1)
    rw [hc0, hc1]
  have hγne : ∀ t : unitInterval, γ t ≠ 0 := by
    intro t heq
    have h0' : G (circleLoop 0 1 t) = G 0 := by
      change G (circleLoop 0 1 t) = _ at heq
      rw [heq, hG0]
    have h1 := hinj h0'
    rw [hcirc t] at h1
    exact Complex.exp_ne_zero _ h1
  -- the winding number of the image unit circle about the origin is one
  have hsub1 : Metric.closedBall (0 : ℂ) 1 ⊆ E.source := by
    rw [hEsrc]
    exact Set.subset_univ _
  have hdeg1 := ((isOrientationPreservingAt_iff_forall E 0).mp h0).2 1 one_pos hsub1
  have hwn1 : windingNumber γ (G 0) = 1 := by
    rw [← hdeg1]
    unfold windingDegreeAt
    exact (hwn_ext _ γ (G 0) fun t => rfl).symm
  rw [hG0] at hwn1
  -- logarithm lift of the image unit circle
  have hδ : ∀ t : unitInterval, shiftedCurve γ 0 t ≠ 0 := by
    intro t
    have hs : shiftedCurve γ 0 t = γ t - 0 := by
      simp [shiftedCurve]
    rw [hs, sub_zero]
    exact hγne t
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ 0) hδ
  have hLt : ∀ t : unitInterval, Complex.exp (L t) = γ t := by
    intro t
    rw [hL t]
    simp [shiftedCurve]
  have him_eq : ∀ t : unitInterval,
      (γ t).im = Real.exp ((L t).re) * Real.sin ((L t).im) := by
    intro t
    rw [← hLt t, Complex.exp_im]
  -- the lift starts on `2πiℤ` since the curve starts at `1`
  have hγ0 : γ 0 = 1 := by
    change G (circleLoop 0 1 0) = 1
    rw [hc0]
    exact hG1
  have hexpL0 : Complex.exp (L 0) = 1 := (hLt 0).trans hγ0
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexpL0
  have hL0im : (L 0).im = 2 * Real.pi * (k : ℝ) := by
    rw [hk]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  -- the lift increment is `+2πi`
  have hspecγ := windingNumber_spec hγcl hγne hL
  rw [hwn1] at hspecγ
  have hL1im : (L 1).im = 2 * Real.pi * (k : ℝ) + 2 * Real.pi := by
    have h := congrArg Complex.im hspecγ
    simp [Complex.sub_im, Complex.mul_im, Complex.mul_re] at h
    linarith [hL0im, h]
  -- the imaginary part of the lift as a real function
  set φ : ℝ → ℝ := fun s => (L (Set.projIcc (0 : ℝ) 1 zero_le_one s)).im with hφdef
  have hφcont : Continuous φ :=
    Complex.continuous_im.comp (L.continuous.comp continuous_projIcc)
  have hφIcc : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) 1), φ s = (L ⟨s, hs⟩).im := by
    intro s hs
    simp only [hφdef]
    rw [Set.projIcc_of_mem]
  have hφ0 : φ 0 = 2 * Real.pi * (k : ℝ) := by
    rw [hφIcc 0 ⟨le_rfl, zero_le_one⟩]
    exact hL0im
  have hφ1 : φ 1 = 2 * Real.pi * (k : ℝ) + 2 * Real.pi := by
    rw [hφIcc 1 ⟨zero_le_one, le_rfl⟩]
    exact hL1im
  have hπ := Real.pi_pos
  -- first intermediate value: the argument passes through `2πk + π`
  have hmid1 : 2 * Real.pi * (k : ℝ) + Real.pi ∈ Set.Icc (φ 0) (φ 1) := by
    rw [hφ0, hφ1]
    constructor <;> linarith
  obtain ⟨s, hsmem, hφs⟩ :=
    intermediate_value_Icc zero_le_one hφcont.continuousOn hmid1
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hsmem.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hφs
      rw [hφ0] at hφs
      linarith
  have hs1 : s < 1 := by
    rcases lt_or_eq_of_le hsmem.2 with h | h
    · exact h
    · exfalso
      rw [h] at hφs
      rw [hφ1] at hφs
      linarith
  have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := hsmem
  -- at that parameter the image point is real
  have hLsim : (L ⟨s, hsIcc⟩).im = 2 * Real.pi * (k : ℝ) + Real.pi :=
    (hφIcc s hsIcc).symm.trans hφs
  have hsin0 : Real.sin (2 * Real.pi * (k : ℝ) + Real.pi) = 0 := by
    rw [add_comm, mul_comm (2 * Real.pi) (k : ℝ)]
    rw [show (k : ℝ) * (2 * Real.pi) = (k : ℤ) * (2 * Real.pi) by norm_num]
    rw [Real.sin_add_int_mul_two_pi, Real.sin_pi]
  have hγsim : (γ ⟨s, hsIcc⟩).im = 0 := by
    rw [him_eq ⟨s, hsIcc⟩, hLsim, hsin0, mul_zero]
  -- the circle parameter is forced to `1/2`
  have hs_half : s = 1 / 2 := by
    rcases lt_trichotomy (Real.sin (2 * Real.pi * s)) 0 with hlt | heq0 | hgt
    · exfalso
      have h1 : (circleLoop 0 1 ⟨s, hsIcc⟩).im < 0 := by
        rw [him ⟨s, hsIcc⟩]
        exact hlt
      have h2 := hneg' _ h1
      have h3 : 0 < (γ ⟨s, hsIcc⟩).im := h2
      linarith [hγsim]
    · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp heq0
      have hn' : (n : ℝ) * Real.pi = 2 * s * Real.pi := by
        rw [hn]
        ring
      have hn2 : (n : ℝ) = 2 * s := mul_right_cancel₀ (ne_of_gt hπ) hn'
      have hb1 : (0 : ℝ) < (n : ℝ) := by
        rw [hn2]
        linarith
      have hb2 : (n : ℝ) < 2 := by
        rw [hn2]
        linarith
      have hi1 : (0 : ℤ) < n := by exact_mod_cast hb1
      have hi2 : n < 2 := by exact_mod_cast hb2
      have hn1 : n = 1 := by omega
      rw [hn1] at hn2
      norm_num at hn2
      linarith
    · exfalso
      have h1 : 0 < (circleLoop 0 1 ⟨s, hsIcc⟩).im := by
        rw [him ⟨s, hsIcc⟩]
        exact hgt
      have h2 := hneg _ h1
      have h3 : (γ ⟨s, hsIcc⟩).im < 0 := h2
      linarith [hγsim]
  -- second intermediate value: the argument passes through `2πk + π/2` before `1/2`
  have hφhalf : φ (1 / 2) = 2 * Real.pi * (k : ℝ) + Real.pi := by
    rw [← hs_half]
    exact hφs
  have hmid2 : 2 * Real.pi * (k : ℝ) + Real.pi / 2 ∈ Set.Icc (φ 0) (φ (1 / 2)) := by
    rw [hφ0, hφhalf]
    constructor <;> linarith
  obtain ⟨s', hs'mem, hφs'⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hφcont.continuousOn hmid2
  have hs'0 : 0 < s' := by
    rcases lt_or_eq_of_le hs'mem.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hφs'
      rw [hφ0] at hφs'
      linarith
  have hs'half : s' < 1 / 2 := by
    rcases lt_or_eq_of_le hs'mem.2 with h | h
    · exact h
    · exfalso
      rw [h] at hφs'
      rw [hφhalf] at hφs'
      linarith
  have hs'Icc : s' ∈ Set.Icc (0 : ℝ) 1 := ⟨hs'mem.1, by linarith⟩
  have hLs'im : (L ⟨s', hs'Icc⟩).im = 2 * Real.pi * (k : ℝ) + Real.pi / 2 := by
    have h := hφIcc s' hs'Icc
    rw [← h]
    exact hφs'
  have hsin1 : Real.sin (2 * Real.pi * (k : ℝ) + Real.pi / 2) = 1 := by
    rw [add_comm, mul_comm (2 * Real.pi) (k : ℝ)]
    rw [show (k : ℝ) * (2 * Real.pi) = (k : ℤ) * (2 * Real.pi) by norm_num]
    rw [Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
  -- the contradiction: the image of an upper point has positive imaginary part
  have h1 : 0 < (circleLoop 0 1 ⟨s', hs'Icc⟩).im := by
    rw [him ⟨s', hs'Icc⟩]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have h2 := hneg _ h1
  have h3 : (γ ⟨s', hs'Icc⟩).im < 0 := h2
  have h4 : (γ ⟨s', hs'Icc⟩).im = Real.exp ((L ⟨s', hs'Icc⟩).re) := by
    rw [him_eq ⟨s', hs'Icc⟩, hLs'im, hsin1, mul_one]
  have h5 := Real.exp_pos ((L ⟨s', hs'Icc⟩).re)
  rw [h4] at h3
  linarith

/-- Matching upper-half-plane conjugation identities of two normalized solutions along a
common base element transport to the transition map of the pair. -/
theorem transition_conj {x y : TeichRep Γ₀}
    {γ W W' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hyc : ∀ z : ℂ, 0 < z.im → y.w (moebiusMap γ z) = moebiusMap W (y.w z))
    (hxc : ∀ z : ℂ, 0 < z.im → x.w (moebiusMap γ z) = moebiusMap W' (x.w z)) :
    ∀ z : ℂ, 0 < z.im → (x.w ∘ Function.invFun y.w) (moebiusMap W z)
      = moebiusMap W' ((x.w ∘ Function.invFun y.w) z) := by
  intro z hz
  set u := Function.invFun y.w z with hu_def
  have hu : 0 < u.im := invFun_w_mapsTo y hz
  have hyu : y.w u = z :=
    Function.rightInverse_invFun y.w_isQCAnalytic.1.1.bijective.surjective z
  have hkey : Function.invFun y.w (moebiusMap W z) = moebiusMap γ u := by
    apply y.w_injective
    rw [Function.rightInverse_invFun y.w_isQCAnalytic.1.1.bijective.surjective]
    rw [hyc u hu, hyu]
  change x.w (Function.invFun y.w (moebiusMap W z))
    = moebiusMap W' (x.w (Function.invFun y.w z))
  rw [hkey, hxc u hu]

/-- A quasiconformal candidate matching the boundary transition maps the upper half plane
into itself: its restriction to `ℝ` is the increasing boundary transition, and it is
sense-preserving. -/
theorem isMarkedCandidate_mapsTo_upper {x y : TeichRep Γ₀} {F : ℂ → ℂ} {K : ℝ}
    (hF : IsQCGeometric F K) (hb : ∀ t : ℝ, F (y.w t) = x.w t) :
    ∀ z : ℂ, 0 < z.im → 0 < (F z).im := by
  have hxK : IsQCGeometric x.w x.b.K := x.w_isQCAnalytic.isQCGeometric_K
  have hyK : IsQCGeometric y.w y.b.K := y.w_isQCAnalytic.isQCGeometric_K
  have hxinv : IsQCGeometric (Function.invFun x.w) x.b.K := by
    have h := isQCGeometric_inv_of_isQCGeometric hxK
    rwa [← invFun_eq_homeoSymm hxK.2.1.isHomeomorph] at h
  have hG : IsQCGeometric (Function.invFun x.w ∘ (F ∘ y.w)) (x.b.K * (K * y.b.K)) :=
    hxinv.comp (hF.comp hyK)
  obtain ⟨bG, -, hGA⟩ := isQCAnalytic_of_isQCGeometric hG.1 hG
  have hOP : OrientationPreservingHomeo (Function.invFun x.w ∘ (F ∘ y.w)) := hGA.1
  have hid : ∀ t : ℝ, (Function.invFun x.w ∘ (F ∘ y.w)) (t : ℂ) = (t : ℂ) := by
    intro t
    change Function.invFun x.w (F (y.w (t : ℂ))) = (t : ℂ)
    rw [hb t]
    exact Function.leftInverse_invFun x.w_injective _
  have hup := mapsTo_upper_of_fixes_real hOP hid
  intro z hz
  have hu : 0 < (Function.invFun y.w z).im := invFun_w_mapsTo y hz
  have hGu := hup _ hu
  have hFz : F z = x.w ((Function.invFun x.w ∘ (F ∘ y.w)) (Function.invFun y.w z)) := by
    change F z = x.w (Function.invFun x.w (F (y.w (Function.invFun y.w z))))
    rw [Function.rightInverse_invFun y.w_isQCAnalytic.1.1.bijective.surjective z,
      Function.rightInverse_invFun x.w_isQCAnalytic.1.1.bijective.surjective]
  rw [hFz]
  exact x.w_mapsTo_upper _ hGu

/-- The equivariant dilatation set is nonempty: the transition `x.w ∘ (y.w)⁻¹` of the
normalized solutions intertwines the marked groups. -/
theorem gDilatationSet_nonempty (x y : TeichRep Γ₀) : (gDilatationSet x y).Nonempty := by
  have hxK : IsQCGeometric x.w x.b.K := x.w_isQCAnalytic.isQCGeometric_K
  have hyK : IsQCGeometric y.w y.b.K := y.w_isQCAnalytic.isQCGeometric_K
  have hyinv : IsQCGeometric (Function.invFun y.w) y.b.K := by
    have h := isQCGeometric_inv_of_isQCGeometric hyK
    rwa [← invFun_eq_homeoSymm hyK.2.1.isHomeomorph] at h
  refine ⟨x.b.K * y.b.K, x.w ∘ Function.invFun y.w, hxK.comp hyinv, ?_, ?_, ?_⟩
  · intro t
    change x.w (Function.invFun y.w (y.w (t : ℂ))) = x.w (t : ℂ)
    rw [Function.leftInverse_invFun y.w_injective]
  · intro W hW
    obtain ⟨γ, hγ, hyc⟩ := w_conj_of_mem_group y hW
    obtain ⟨W', hW', hxc⟩ := w_conj_of_mem_base x hγ
    exact ⟨W', hW', transition_conj hyc hxc⟩
  · intro W' hW'
    obtain ⟨γ, hγ, hxc⟩ := w_conj_of_mem_group x hW'
    obtain ⟨W, hW, hyc⟩ := w_conj_of_mem_base y hγ
    exact ⟨W, hW, transition_conj hyc hxc⟩

/-- The intrinsic distance is at least the boundary-value pseudodistance: every marked
candidate is a boundary candidate. -/
theorem teichPseudoDist_le_teichDistG (x y : TeichRep Γ₀) :
    teichPseudoDist x y ≤ teichDistG x y := by
  have hle : sInf (dilatationSet x y) ≤ sInf (gDilatationSet x y) :=
    csInf_le_csInf (bddBelow_dilatationSet x y) (gDilatationSet_nonempty x y)
      fun _ hK => mem_dilatationSet_of_mem_gDilatationSet hK
  have hpos : (0 : ℝ) < sInf (dilatationSet x y) :=
    lt_of_lt_of_le one_pos (one_le_sInf_dilatationSet x y)
  have hlog := Real.log_le_log hpos hle
  unfold teichPseudoDist teichDistG
  linarith

/-- The inverse of a quasiconformal marked candidate is a marked candidate of the same
dilatation for the transposed pair: the two compatibility clauses swap. -/
theorem gDilatationSet_subset_comm (x y : TeichRep Γ₀) :
    gDilatationSet x y ⊆ gDilatationSet y x := by
  rintro K ⟨F, hF, hb, hfwd, hbwd⟩
  set G : ℂ → ℂ := ⇑(hF.2.1.isHomeomorph.homeomorph F).symm with hGdef
  have hGqc : IsQCGeometric G K := isQCGeometric_inv_of_isQCGeometric hF
  have happ : ∀ z : ℂ, (hF.2.1.isHomeomorph.homeomorph F) z = F z := fun z =>
    IsHomeomorph.homeomorph_apply F hF.2.1.isHomeomorph z
  have hGF : ∀ z : ℂ, G (F z) = z := by
    intro z
    rw [← happ z]
    exact Homeomorph.symm_apply_apply _ z
  have hFG : ∀ z : ℂ, F (G z) = z := by
    intro z
    rw [← happ (G z)]
    exact (hF.2.1.isHomeomorph.homeomorph F).apply_symm_apply z
  have hGb : ∀ t : ℝ, G (x.w t) = y.w t := by
    intro t
    rw [← hb t]
    exact hGF _
  have hGup : ∀ z : ℂ, 0 < z.im → 0 < (G z).im :=
    isMarkedCandidate_mapsTo_upper hGqc hGb
  refine ⟨G, hGqc, hGb, ?_, ?_⟩
  · intro W hW
    obtain ⟨V, hV, hFc⟩ := hbwd W hW
    exact ⟨V, hV, inv_conj_of_conj hGup (fun z _ => hGF z) (fun z _ => hFG z) hFc⟩
  · intro W hW
    obtain ⟨U, hU, hFc⟩ := hfwd W hW
    exact ⟨U, hU, inv_conj_of_conj hGup (fun z _ => hGF z) (fun z _ => hFG z) hFc⟩

/-- The equivariant dilatation sets of a pair and its transpose coincide: the inverse of a
marked candidate is a marked candidate by the two-sided compatibility clauses. -/
theorem gDilatationSet_comm (x y : TeichRep Γ₀) :
    gDilatationSet x y = gDilatationSet y x := by
  exact Set.Subset.antisymm (gDilatationSet_subset_comm x y)
    (gDilatationSet_subset_comm y x)

/-- The intrinsic distance is symmetric. -/
theorem teichDistG_comm (x y : TeichRep Γ₀) : teichDistG x y = teichDistG y x := by
  unfold teichDistG
  rw [gDilatationSet_comm]

/-- Marked candidates compose with multiplying dilatations, the compatibility clauses
chained through the half-plane preservation of the inner candidate. -/
theorem mul_mem_gDilatationSet {x y z : TeichRep Γ₀} {K₁ K₂ : ℝ}
    (h₁ : K₁ ∈ gDilatationSet x y) (h₂ : K₂ ∈ gDilatationSet y z) :
    K₁ * K₂ ∈ gDilatationSet x z := by
  obtain ⟨F₁, hF₁, hb₁, hfwd₁, hbwd₁⟩ := h₁
  obtain ⟨F₂, hF₂, hb₂, hfwd₂, hbwd₂⟩ := h₂
  have hF₂up : ∀ ζ : ℂ, 0 < ζ.im → 0 < (F₂ ζ).im :=
    isMarkedCandidate_mapsTo_upper hF₂ hb₂
  refine ⟨F₁ ∘ F₂, hF₁.comp hF₂, fun t => ?_, ?_, ?_⟩
  · rw [Function.comp_apply, hb₂ t, hb₁ t]
  · intro W hW
    obtain ⟨V, hV, h2⟩ := hfwd₂ W hW
    obtain ⟨W', hW', h1⟩ := hfwd₁ V hV
    refine ⟨W', hW', fun ζ hζ => ?_⟩
    change F₁ (F₂ (moebiusMap W ζ)) = moebiusMap W' (F₁ (F₂ ζ))
    rw [h2 ζ hζ, h1 (F₂ ζ) (hF₂up ζ hζ)]
  · intro W' hW'
    obtain ⟨V, hV, h1⟩ := hbwd₁ W' hW'
    obtain ⟨W, hW, h2⟩ := hbwd₂ V hV
    refine ⟨W, hW, fun ζ hζ => ?_⟩
    change F₁ (F₂ (moebiusMap W ζ)) = moebiusMap W' (F₁ (F₂ ζ))
    rw [h2 ζ hζ, h1 (F₂ ζ) (hF₂up ζ hζ)]

/-- The triangle inequality for the intrinsic distance: marked candidates compose, with
the compatibility clauses chained through the half-plane preservation of candidates. -/
theorem teichDistG_triangle (x y z : TeichRep Γ₀) :
    teichDistG x z ≤ teichDistG x y + teichDistG y z := by
  have hcomp : ∀ K₁ ∈ gDilatationSet x y, ∀ K₂ ∈ gDilatationSet y z,
      K₁ * K₂ ∈ gDilatationSet x z := fun K₁ h₁ K₂ h₂ => mul_mem_gDilatationSet h₁ h₂
  have ha1 : 1 ≤ sInf (gDilatationSet x y) :=
    le_csInf (gDilatationSet_nonempty x y) fun _ h => one_le_of_mem_gDilatationSet h
  have hb1 : 1 ≤ sInf (gDilatationSet y z) :=
    le_csInf (gDilatationSet_nonempty y z) fun _ h => one_le_of_mem_gDilatationSet h
  have hc1 : 1 ≤ sInf (gDilatationSet x z) :=
    le_csInf (gDilatationSet_nonempty x z) fun _ h => one_le_of_mem_gDilatationSet h
  have hapos : (0 : ℝ) < sInf (gDilatationSet x y) := lt_of_lt_of_le one_pos ha1
  have hstep : ∀ K₂ ∈ gDilatationSet y z,
      sInf (gDilatationSet x z) ≤ sInf (gDilatationSet x y) * K₂ := by
    intro K₂ hK₂
    have hK₂pos : (0 : ℝ) < K₂ :=
      lt_of_lt_of_le one_pos (one_le_of_mem_gDilatationSet hK₂)
    have hlb : ∀ K₁ ∈ gDilatationSet x y, sInf (gDilatationSet x z) / K₂ ≤ K₁ := by
      intro K₁ hK₁
      have hle : sInf (gDilatationSet x z) ≤ K₁ * K₂ :=
        csInf_le (bddBelow_gDilatationSet x z) (hcomp K₁ hK₁ K₂ hK₂)
      exact (div_le_iff₀ hK₂pos).mpr hle
    have h := le_csInf (gDilatationSet_nonempty x y) hlb
    exact (div_le_iff₀ hK₂pos).mp h
  have hprod : sInf (gDilatationSet x z)
      ≤ sInf (gDilatationSet x y) * sInf (gDilatationSet y z) := by
    have hlb2 : ∀ K₂ ∈ gDilatationSet y z,
        sInf (gDilatationSet x z) / sInf (gDilatationSet x y) ≤ K₂ := by
      intro K₂ hK₂
      rw [div_le_iff₀ hapos, mul_comm]
      exact hstep K₂ hK₂
    have h := le_csInf (gDilatationSet_nonempty y z) hlb2
    rw [div_le_iff₀ hapos] at h
    rw [mul_comm] at h
    exact h
  have hcpos : (0 : ℝ) < sInf (gDilatationSet x z) := lt_of_lt_of_le one_pos hc1
  have hane : sInf (gDilatationSet x y) ≠ 0 := ne_of_gt hapos
  have hbne : sInf (gDilatationSet y z) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hb1)
  have hlog : Real.log (sInf (gDilatationSet x z))
      ≤ Real.log (sInf (gDilatationSet x y)) + Real.log (sInf (gDilatationSet y z)) := by
    have h1 : Real.log (sInf (gDilatationSet x z))
        ≤ Real.log (sInf (gDilatationSet x y) * sInf (gDilatationSet y z)) :=
      Real.log_le_log hcpos hprod
    rwa [Real.log_mul hane hbne] at h1
  unfold teichDistG
  linarith

/-! ## Rigidity and descent to Teichmüller space -/

/-- **Rigidity of the intrinsic distance**: it vanishes exactly on pairs with equal
boundary values, so it separates the same points as the boundary-value pseudometric. -/
theorem teichDistG_eq_zero_iff_boundary {x y : TeichRep Γ₀} :
    teichDistG x y = 0 ↔ ∀ t : ℝ, x.w t = y.w t := by
  constructor
  · intro h
    have hd0 : teichPseudoDist x y = 0 :=
      le_antisymm (h ▸ teichPseudoDist_le_teichDistG x y) (teichPseudoDist_nonneg x y)
    exact fun t => (w_eq_on_real_of_teichPseudoDist_eq_zero hd0 t).symm
  · intro h
    have hmem : (1 : ℝ) ∈ gDilatationSet x y :=
      ⟨id, isQCGeometric_id, isMarkedCandidate_id h⟩
    have h1 : sInf (gDilatationSet x y) ≤ 1 :=
      csInf_le (bddBelow_gDilatationSet x y) hmem
    have h2 : 1 ≤ sInf (gDilatationSet x y) :=
      le_csInf ⟨1, hmem⟩ fun _ hK => one_le_of_mem_gDilatationSet hK
    unfold teichDistG
    rw [le_antisymm h1 h2, Real.log_one, mul_zero]

/-- Membership in the equivariant dilatation set depends only on the boundary values of
the pair: the groups are boundary-determined and the boundary clause transports. -/
theorem mem_gDilatationSet_congr {x x' y y' : TeichRep Γ₀} {K : ℝ}
    (hx : ∀ t : ℝ, x.w t = x'.w t) (hy : ∀ t : ℝ, y.w t = y'.w t)
    (hK : K ∈ gDilatationSet x y) : K ∈ gDilatationSet x' y' := by
  obtain ⟨F, hF, hb, hfwd, hbwd⟩ := hK
  have hxg : x.group = x'.group := TeichRep.group_eq_of_boundary_eq
    (funext fun t => by simp only [TeichRep.boundary, hx t])
  have hyg : y.group = y'.group := TeichRep.group_eq_of_boundary_eq
    (funext fun t => by simp only [TeichRep.boundary, hy t])
  refine ⟨F, hF, fun t => ?_, ?_, ?_⟩
  · rw [← hy t, hb t, hx t]
  · rw [← hyg, ← hxg]; exact hfwd
  · rw [← hyg, ← hxg]; exact hbwd

/-- The equivariant dilatation set depends only on the boundary values of the pair. -/
theorem gDilatationSet_congr {x x' y y' : TeichRep Γ₀}
    (hx : ∀ t : ℝ, x.w t = x'.w t) (hy : ∀ t : ℝ, y.w t = y'.w t) :
    gDilatationSet x y = gDilatationSet x' y' :=
  Set.ext fun _ => ⟨fun h => mem_gDilatationSet_congr hx hy h,
    fun h => mem_gDilatationSet_congr (fun t => (hx t).symm) (fun t => (hy t).symm) h⟩

/-- The intrinsic distance depends only on the boundary values of the pair. -/
theorem teichDistG_congr {x x' y y' : TeichRep Γ₀}
    (hx : ∀ t : ℝ, x.w t = x'.w t) (hy : ∀ t : ℝ, y.w t = y'.w t) :
    teichDistG x y = teichDistG x' y' := by
  unfold teichDistG
  rw [gDilatationSet_congr hx hy]

/-- The **intrinsic Teichmüller distance on Teichmüller space**: the descent of
`teichDistG` through the separation quotient. It is a distance function, not a second
metric-space instance; the topology of `Teich Γ₀` is that of `teichPseudoDist`. -/
noncomputable def Teich.distG : Teich Γ₀ → Teich Γ₀ → ℝ :=
  SeparationQuotient.lift₂ teichDistG fun _ _ _ _ hac hbd =>
    teichDistG_congr (inseparable_iff_boundary_eq.mp hac) (inseparable_iff_boundary_eq.mp hbd)

/-- The descended distance computed on classes of representatives. -/
theorem Teich.distG_mk (x y : TeichRep Γ₀) :
    Teich.distG (Teich.mk x) (Teich.mk y) = teichDistG x y := rfl

/-- The descended distance is nonnegative. -/
theorem Teich.distG_nonneg (a b : Teich Γ₀) : 0 ≤ Teich.distG a b := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
  exact teichDistG_nonneg x y

/-- The descended distance vanishes on the diagonal. -/
theorem Teich.distG_self (a : Teich Γ₀) : Teich.distG a a = 0 := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  exact teichDistG_self x

/-- The descended distance is symmetric. -/
theorem Teich.distG_comm (a b : Teich Γ₀) : Teich.distG a b = Teich.distG b a := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
  exact teichDistG_comm x y

/-- The descended distance satisfies the triangle inequality. -/
theorem Teich.distG_triangle (a b c : Teich Γ₀) :
    Teich.distG a c ≤ Teich.distG a b + Teich.distG b c := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
  obtain ⟨z, rfl⟩ := SeparationQuotient.surjective_mk c
  exact teichDistG_triangle x y z

/-- The descended distance separates points of Teichmüller space. -/
theorem Teich.distG_eq_zero_iff {a b : Teich Γ₀} : Teich.distG a b = 0 ↔ a = b := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
  exact teichDistG_eq_zero_iff_boundary.trans Teich.mk_eq_mk_iff_boundary.symm

/-- A finite set of reals has dense complement. -/
theorem dense_compl_finite {B : Set ℝ} (hB : B.Finite) : Dense Bᶜ := by
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  have hIoo : Set.Ioo (x - ε) (x + ε) ⊆ U := fun y hy => hball (by
    rw [Real.ball_eq_Ioo]; exact hy)
  have hinf : (Set.Ioo (x - ε) (x + ε)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨y, hy1, hy2⟩ := (hinf.diff hB).nonempty
  exact ⟨y, hIoo hy1, hy2⟩

/-- Boundary limit: a continuous plane map that factors on the upper half plane as a real
Möbius map, a continuous plane map, and a real Möbius map extends the factorization to a
real boundary point off the poles. -/
theorem moebius_boundary_factor {Λ φ : ℂ → ℂ} (hΛc : Continuous Λ) (hφc : Continuous φ)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hint : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap A (φ (moebiusMap B ζ)))
    {t : ℝ} (hd1 : moebiusDenom B (t : ℂ) ≠ 0)
    (hd2 : moebiusDenom A (φ (moebiusMap B (t : ℂ))) ≠ 0) :
    Λ (t : ℂ) = moebiusMap A (φ (moebiusMap B (t : ℂ))) := by
  set z : ℕ → ℂ := fun n => (t : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hzdef
  have him' : ∀ s : ℝ, ((t : ℂ) + (s : ℂ) * Complex.I).im = s := by
    intro s
    simp [Complex.add_im, Complex.mul_im]
  have hzim : ∀ n : ℕ, 0 < (z n).im := by
    intro n
    have h1 : (z n).im = 1 / ((n : ℝ) + 1) := by
      rw [hzdef]
      exact him' (1 / ((n : ℝ) + 1))
    rw [h1]
    positivity
  have htend : Filter.Tendsto z Filter.atTop (nhds (t : ℂ)) := by
    rw [hzdef]
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (nhds ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    have h3 := (h2.mul_const Complex.I).const_add (t : ℂ)
    simpa using h3
  have hL : Filter.Tendsto (fun n => Λ (z n)) Filter.atTop (nhds (Λ (t : ℂ))) :=
    (hΛc.tendsto _).comp htend
  have hc1 : ContinuousAt (moebiusMap B) (t : ℂ) :=
    (hasDerivAt_moebiusMap B hd1).continuousAt
  have hc3 : ContinuousAt (moebiusMap A) (φ (moebiusMap B (t : ℂ))) :=
    (hasDerivAt_moebiusMap A hd2).continuousAt
  have hR : Filter.Tendsto (fun n => moebiusMap A (φ (moebiusMap B (z n))))
      Filter.atTop (nhds (moebiusMap A (φ (moebiusMap B (t : ℂ))))) := by
    have s1 : Filter.Tendsto (fun n => moebiusMap B (z n)) Filter.atTop
        (nhds (moebiusMap B (t : ℂ))) := hc1.tendsto.comp htend
    have s2 : Filter.Tendsto (fun n => φ (moebiusMap B (z n))) Filter.atTop
        (nhds (φ (moebiusMap B (t : ℂ)))) := (hφc.tendsto _).comp s1
    exact hc3.tendsto.comp s2
  have hEqn : (fun n => Λ (z n)) = fun n => moebiusMap A (φ (moebiusMap B (z n))) :=
    funext fun n => hint (z n) (hzim n)
  rw [hEqn] at hL
  exact tendsto_nhds_unique hL hR

/-- A quasiconformal plane homeomorphism preserving the upper half plane together with a
half-plane-preserving two-sided inverse restricts to an upper-half-plane quasiconformal
map with the corresponding coefficient bound. -/
theorem isQCUpper_of_qc {F G : ℂ → ℂ} {K : ℝ} (hF : IsQCGeometric F K)
    (hGcont : Continuous G)
    (hup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im) (hup' : ∀ z : ℂ, 0 < z.im → 0 < (G z).im)
    (hGF : ∀ z : ℂ, G (F z) = z) (hFG : ∀ z : ℂ, F (G z) = z) :
    IsQCUpper F G ((K - 1) / (K + 1)) := by
  obtain ⟨b, hbnd, hQCA⟩ := isQCAnalytic_of_isQCGeometric hF.1 hF
  refine ⟨hup, hup', fun z _ => hGF z, fun z _ => hFG z,
    hF.2.1.isHomeomorph.continuous.continuousOn, hGcont.continuousOn,
    MemWklocP.mono hQCA.2.1 (Set.subset_univ _),
    ae_restrict_of_ae hQCA.1.2, ?_⟩
  have hbw_ae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ b.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt b.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  refine ae_restrict_of_ae ?_
  filter_upwards [hQCA.2.2, hbw_ae] with z hbel hbw
  calc ‖dzbar F z‖ = ‖b.μ z‖ * ‖dz F z‖ := by rw [hbel, norm_mul]
    _ ≤ b.normInf * ‖dz F z‖ := mul_le_mul_of_nonneg_right hbw (norm_nonneg _)
    _ ≤ (K - 1) / (K + 1) * ‖dz F z‖ := mul_le_mul_of_nonneg_right hbnd (norm_nonneg _)

/-- Conjugation identities transport along a surjective factor of the upper half plane. -/
theorem conj_push {u : ℂ → ℂ} (R : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    {γ V W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (husurj : ∀ w : ℂ, 0 < w.im → ∃ z, 0 < z.im ∧ u z = w)
    (huconj : ∀ z : ℂ, 0 < z.im → u (moebiusMap γ z) = moebiusMap V (u z))
    (hψ : ∀ z : ℂ, 0 < z.im →
      moebiusMap R (u (moebiusMap γ z)) = moebiusMap W (moebiusMap R (u z))) :
    ∀ w : ℂ, 0 < w.im → moebiusMap R (moebiusMap V w) = moebiusMap W (moebiusMap R w) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := husurj w hw
  rw [← huconj z hz]
  exact hψ z hz

/-- A Möbius intertwining relation inverts across the conjugating Möbius factor on the
upper half plane. -/
theorem conj_pull {R V W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : ∀ w : ℂ, 0 < w.im →
      moebiusMap R (moebiusMap V w) = moebiusMap W (moebiusMap R w)) :
    ∀ ζ : ℂ, 0 < ζ.im →
      moebiusMap R⁻¹ (moebiusMap W ζ) = moebiusMap V (moebiusMap R⁻¹ ζ) := by
  intro ζ hζ
  have hw : 0 < (moebiusMap R⁻¹ ζ).im := moebiusMap_im_pos R⁻¹ hζ
  have hVw : 0 < (moebiusMap V (moebiusMap R⁻¹ ζ)).im := moebiusMap_im_pos V hw
  have hζeq : moebiusMap R (moebiusMap R⁻¹ ζ) = ζ := by
    rw [moebiusMap_mul R R⁻¹ ζ (moebiusDenom_ne_zero_of_im_ne_zero R⁻¹ (ne_of_gt hζ)),
      mul_inv_cancel, moebiusMap_one]
  calc moebiusMap R⁻¹ (moebiusMap W ζ)
      = moebiusMap R⁻¹ (moebiusMap W (moebiusMap R (moebiusMap R⁻¹ ζ))) := by rw [hζeq]
    _ = moebiusMap R⁻¹ (moebiusMap R (moebiusMap V (moebiusMap R⁻¹ ζ))) := by
        rw [← h _ hw]
    _ = moebiusMap V (moebiusMap R⁻¹ ζ) := by
        rw [moebiusMap_mul R⁻¹ R _ (moebiusDenom_ne_zero_of_im_ne_zero R (ne_of_gt hVw)),
          inv_mul_cancel, moebiusMap_one]

/-- The conjugation chain of a Möbius-sandwiched candidate: the sandwich intertwines the
transported group elements. -/
theorem conj_chain {F' F : ℂ → ℂ} {Rx Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {W W' V V' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hCh : ∀ ζ : ℂ, 0 < ζ.im → F' ζ = moebiusMap Rx (F (moebiusMap Ry⁻¹ ζ)))
    (hFup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im)
    (hVRy : ∀ ζ : ℂ, 0 < ζ.im →
      moebiusMap Ry⁻¹ (moebiusMap W ζ) = moebiusMap V (moebiusMap Ry⁻¹ ζ))
    (hFV : ∀ w : ℂ, 0 < w.im → F (moebiusMap V w) = moebiusMap V' (F w))
    (hRxV' : ∀ w : ℂ, 0 < w.im →
      moebiusMap Rx (moebiusMap V' w) = moebiusMap W' (moebiusMap Rx w)) :
    ∀ ζ : ℂ, 0 < ζ.im → F' (moebiusMap W ζ) = moebiusMap W' (F' ζ) := by
  intro ζ hζ
  have h1 : 0 < (moebiusMap W ζ).im := moebiusMap_im_pos W hζ
  have h2 : 0 < (moebiusMap Ry⁻¹ ζ).im := moebiusMap_im_pos Ry⁻¹ hζ
  rw [hCh _ h1, hVRy ζ hζ, hFV _ h2, hRxV' _ (hFup _ h2), ← hCh ζ hζ]

/-- The set of reals where the inner Möbius factor is finite but the outer denominator
vanishes after the candidate is a subsingleton. -/
theorem bad_denom_subsingleton {F : ℂ → ℂ} (hFinj : Function.Injective F)
    (A Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0
      ∧ moebiusDenom A (F (moebiusMap Ry⁻¹ (s : ℂ))) = 0}.Subsingleton := by
  intro t₁ h₁ t₂ h₂
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨h₂a, h₂b⟩ := h₂
  have hw : F (moebiusMap Ry⁻¹ ((t₁ : ℝ) : ℂ)) = F (moebiusMap Ry⁻¹ ((t₂ : ℝ) : ℂ)) :=
    moebiusDenom_zero_subsingleton A h₁b h₂b
  have hmm := hFinj hw
  have e1 : moebiusMap Ry (moebiusMap Ry⁻¹ ((t₁ : ℝ) : ℂ)) = ((t₁ : ℝ) : ℂ) := by
    rw [moebiusMap_mul Ry Ry⁻¹ _ h₁a, mul_inv_cancel, moebiusMap_one]
  have e2 : moebiusMap Ry (moebiusMap Ry⁻¹ ((t₂ : ℝ) : ℂ)) = ((t₂ : ℝ) : ℂ) := by
    rw [moebiusMap_mul Ry Ry⁻¹ _ h₂a, mul_inv_cancel, moebiusMap_one]
  have : ((t₁ : ℝ) : ℂ) = ((t₂ : ℝ) : ℂ) := by
    rw [← e1, ← e2, hmm]
  exact_mod_cast this

/-- The re-marking composite of a normalized solution maps the upper half plane onto
itself. -/
theorem wg_surj (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀) :
    ∀ w : ℂ, 0 < w.im → ∃ z, 0 < z.im ∧ x.w (P.g z) = w := by
  intro w hw
  have hzw : 0 < (Function.invFun x.w w).im := invFun_w_mapsTo x hw
  refine ⟨P.ginv (Function.invFun x.w w), P.qc.mapsTo' _ hzw, ?_⟩
  rw [P.qc.right_inv _ hzw]
  exact Function.rightInverse_invFun x.w_isQCAnalytic.1.1.bijective.surjective w

/-- Group conjugation identities of a re-marked solution transport through the Möbius
normalizer to conjugation identities between the base and re-marked group elements. -/
theorem group_transport (x : TeichRep Γ₀) (P : ModGroupUpper Γ₀)
    {Rx : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hRx : ∀ z : ℂ, 0 < z.im → (x.smulUpper P).w z = moebiusMap Rx (x.w (P.g z)))
    {γ₄ γ₃ V' W' : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hPc : ∀ z : ℂ, 0 < z.im → P.g (moebiusMap γ₄ z) = moebiusMap γ₃ (P.g z))
    (hxc : ∀ u : ℂ, 0 < u.im → x.w (moebiusMap γ₃ u) = moebiusMap V' (x.w u))
    (hxU : ∀ z : ℂ, 0 < z.im →
      (x.smulUpper P).w (moebiusMap γ₄ z) = moebiusMap W' ((x.smulUpper P).w z)) :
    ∀ w : ℂ, 0 < w.im →
      moebiusMap Rx (moebiusMap V' w) = moebiusMap W' (moebiusMap Rx w) := by
  refine conj_push (u := fun z => x.w (P.g z)) (γ := γ₄) Rx (wg_surj x P)
    (fun z hz => ?_) (fun z hz => ?_)
  · change x.w (P.g (moebiusMap γ₄ z)) = moebiusMap V' (x.w (P.g z))
    rw [hPc z hz, hxc (P.g z) (P.qc.mapsTo z hz)]
  · change moebiusMap Rx (x.w (P.g (moebiusMap γ₄ z)))
      = moebiusMap W' (moebiusMap Rx (x.w (P.g z)))
    rw [← hRx (moebiusMap γ₄ z) (moebiusMap_im_pos γ₄ hz), ← hRx z hz]
    exact hxU z hz

/-- A special linear matrix with vanishing lower-left entry acts as an affine map. -/
theorem moebius_affine {Q : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hQ10 : Q 1 0 = 0) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ w : ℂ, moebiusMap Q w = a * w + b := by
  have hdet : Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe Q
    rwa [Matrix.det_fin_two] at h
  have hd : Q 1 1 ≠ 0 := by
    intro h0
    rw [hQ10, h0] at hdet
    simp at hdet
  have h00 : Q 0 0 ≠ 0 := by
    intro h0
    rw [hQ10, h0] at hdet
    simp at hdet
  have hdC : ((Q 1 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  refine ⟨((Q 0 0 : ℝ) : ℂ) / ((Q 1 1 : ℝ) : ℂ), ((Q 0 1 : ℝ) : ℂ) / ((Q 1 1 : ℝ) : ℂ),
    div_ne_zero (Complex.ofReal_ne_zero.mpr h00) hdC, ?_⟩
  intro w
  simp only [moebiusMap, moebiusDenom, hQ10, Complex.ofReal_zero, zero_mul, zero_add]
  field_simp

/-- At a real point off the poles, a plane map factoring on the upper half plane through
the candidate and a plane map factoring through the transition are Möbius-related, the
candidate and the transition having the same boundary trace. -/
theorem real_glue {Ψ Λ F T : ℂ → ℂ} (hΨc : Continuous Ψ) (hΛc : Continuous Λ)
    (hFc : Continuous F) (hTc : Continuous T)
    (S Rx Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hΨfac : ∀ ζ : ℂ, 0 < ζ.im → Ψ ζ = moebiusMap S (F (moebiusMap Ry⁻¹ ζ)))
    (hΛfac : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap Rx (T (moebiusMap Ry⁻¹ ζ)))
    (hFT : ∀ r : ℝ, F (r : ℂ) = T (r : ℂ))
    {s : ℝ} (hd1 : moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0)
    (hd2 : moebiusDenom S (F (moebiusMap Ry⁻¹ (s : ℂ))) ≠ 0)
    (hd3 : moebiusDenom Rx (F (moebiusMap Ry⁻¹ (s : ℂ))) ≠ 0) :
    Ψ (s : ℂ) = moebiusMap (S * Rx⁻¹) (Λ (s : ℂ)) := by
  have hTF : T (moebiusMap Ry⁻¹ (s : ℂ)) = F (moebiusMap Ry⁻¹ (s : ℂ)) := by
    obtain ⟨r, hr⟩ := moebiusMap_ofReal Ry⁻¹ s
    rw [hr]
    exact (hFT r).symm
  have hd3' : moebiusDenom Rx (T (moebiusMap Ry⁻¹ (s : ℂ))) ≠ 0 := by
    rw [hTF]
    exact hd3
  have i1 := moebius_boundary_factor hΨc hFc S Ry⁻¹ hΨfac hd1 hd2
  have i2 := moebius_boundary_factor hΛc hTc Rx Ry⁻¹ hΛfac hd1 hd3'
  rw [i1, i2, hTF,
    moebiusMap_mul (S * Rx⁻¹) Rx _ hd3, mul_assoc, inv_mul_cancel, mul_one]

/-- **Sandwich representative.** An upper-half-plane quasiconformal map with coefficient
bound `κ`, pre-composed with a real Möbius map, is realized on the upper half plane by a
normalized plane solution of dilatation `(1 + κ)/(1 − κ)` up to a real Möbius factor. -/
theorem sandwich_rep {F G : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hqcU : IsQCUpper F G κ) (Ry : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ (Y : TeichRep (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)))
      (S : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      IsQCGeometric Y.w ((1 + κ) / (1 - κ)) ∧
      ∀ ζ : ℂ, 0 < ζ.im → Y.w ζ = moebiusMap S (F (moebiusMap Ry⁻¹ ζ)) := by
  obtain ⟨YF, hcoYF⟩ := flip_rep hκ1 hqcU
  obtain ⟨PF, hPF⟩ := exists_sl2_factorization_of_eq_coeff YF hκ1 hqcU hcoYF
  have hqcM := isQCUpper_moebiusMap Ry⁻¹
  have hA := YF.isQCUpper_remark (modGroupUpperBot one_pos hqcM)
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ] at hA
  have hκA1 : (max 0 0 + YF.b.normInf) / (1 + max 0 0 * YF.b.normInf) < 1 :=
    comb_lt_one (le_max_right _ _) (max_lt one_pos one_pos) YF.b.normInf_nonneg
      YF.b.normInf_lt_one
  obtain ⟨Y₂, hcoY₂⟩ := flip_rep hκA1 hA
  obtain ⟨P₂, hP₂⟩ := exists_sl2_factorization_of_eq_coeff Y₂ hκA1 hA hcoY₂
  have hfac : ∀ ζ : ℂ, 0 < ζ.im →
      Y₂.w ζ = moebiusMap (P₂ * PF) (F (moebiusMap Ry⁻¹ ζ)) := by
    intro ζ hζ
    have hRyζ : 0 < (moebiusMap Ry⁻¹ ζ).im := moebiusMap_im_pos Ry⁻¹ hζ
    have hFζ : 0 < (F (moebiusMap Ry⁻¹ ζ)).im := hqcU.mapsTo _ hRyζ
    have h2 : (YF.w ∘ moebiusMap Ry⁻¹) ζ = moebiusMap PF (F (moebiusMap Ry⁻¹ ζ)) :=
      hPF _ hRyζ
    rw [hP₂ ζ hζ, h2, moebiusMap_mul P₂ PF _
      (moebiusDenom_ne_zero_of_im_ne_zero PF (ne_of_gt hFζ))]
  exact ⟨Y₂, P₂ * PF, isQCGeometric_K_of_upper_moebius_factor Y₂.w_isQCAnalytic Y₂.w_conj
    hκ0 hκ1 hqcU (P₂ * PF) Ry⁻¹ hfac, hfac⟩

/-! ## Re-markings act by isometries -/

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: one declaration chains the inverse-candidate package, two flip
-- representatives, the Möbius boundary glue, and four group-transport chains.
/-- **Candidate transport under a re-marking**: a marked candidate for a pair conjugates,
through the Möbius renormalizers of the re-marked solutions, to a marked candidate of the
same dilatation for the re-marked pair; the conjugate fixes the point at infinity and is
quasiconformal off a removable point. -/
theorem mem_gDilatationSet_smulUpper (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {x y : TeichRep Γ₀} {K : ℝ} (P : ModGroupUpper Γ₀)
    (hK : K ∈ gDilatationSet x y) :
    K ∈ gDilatationSet (x.smulUpper P) (y.smulUpper P) := by
  classical
  -- standing assumptions of the theory, threaded uniformly through the API but not needed
  -- by this particular transport argument
  have _ := hΓ₀
  have _ := hfree
  have _ := hcc
  obtain ⟨F, hFqc, hb, hfwd, hbwd⟩ := hK
  have hK1 : 1 ≤ K := hFqc.1
  have hκ0 : (0 : ℝ) ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) (by linarith)
  have hκ1 : (K - 1) / (K + 1) < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < K + 1)]
    linarith
  have hKp : K + 1 ≠ 0 := by
    intro h0
    linarith
  have hden6 : 1 - (K - 1) / (K + 1) ≠ 0 := by
    have h : 1 - (K - 1) / (K + 1) = 2 / (K + 1) := by
      field_simp
      ring
    rw [h]
    exact div_ne_zero two_ne_zero hKp
  have hKκ : (1 + (K - 1) / (K + 1)) / (1 - (K - 1) / (K + 1)) = K := by
    rw [div_eq_iff hden6]
    field_simp
    ring
  -- the inverse candidate package
  set G : ℂ → ℂ := ⇑(hFqc.2.1.isHomeomorph.homeomorph F).symm with hGdef
  have hGqc : IsQCGeometric G K := isQCGeometric_inv_of_isQCGeometric hFqc
  have happ : ∀ z : ℂ, (hFqc.2.1.isHomeomorph.homeomorph F) z = F z := fun z =>
    IsHomeomorph.homeomorph_apply F hFqc.2.1.isHomeomorph z
  have hGF : ∀ z : ℂ, G (F z) = z := by
    intro z
    rw [← happ z]
    exact Homeomorph.symm_apply_apply _ z
  have hFG : ∀ z : ℂ, F (G z) = z := by
    intro z
    rw [← happ (G z)]
    exact (hFqc.2.1.isHomeomorph.homeomorph F).apply_symm_apply z
  have hGb : ∀ t : ℝ, G (x.w t) = y.w t := by
    intro t
    rw [← hb t]
    exact hGF _
  have hFup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im := isMarkedCandidate_mapsTo_upper hFqc hb
  have hGup : ∀ z : ℂ, 0 < z.im → 0 < (G z).im := isMarkedCandidate_mapsTo_upper hGqc hGb
  have hFinj : Function.Injective F := hFqc.2.1.isHomeomorph.injective
  have hFc : Continuous F := hFqc.2.1.isHomeomorph.continuous
  have hqcU : IsQCUpper F G ((K - 1) / (K + 1)) :=
    isQCUpper_of_qc hFqc (hFqc.2.1.isHomeomorph.homeomorph F).symm.continuous
      hFup hGup hGF hFG
  -- Möbius normalizers of the re-marked solutions and the sandwich representative
  obtain ⟨Rx, hRx⟩ := x.smulUpper_w P
  obtain ⟨Ry, hRy⟩ := y.smulUpper_w P
  obtain ⟨Y, S, hYgeo0, hYfac⟩ := sandwich_rep hκ0 hκ1 hqcU Ry
  rw [hKκ] at hYgeo0
  have hu11 : IsHomeomorph (x.smulUpper P).w := (x.smulUpper P).w_isQCAnalytic.1.1
  have hv11 : IsHomeomorph (y.smulUpper P).w := (y.smulUpper P).w_isQCAnalytic.1.1
  have hY11 : IsHomeomorph Y.w := Y.w_isQCAnalytic.1.1
  have hvsurj : Function.Surjective (y.smulUpper P).w := hv11.bijective.surjective
  have hysurj : Function.Surjective y.w := y.w_isQCAnalytic.1.1.bijective.surjective
  -- the transitions of the original and the re-marked pairs
  set T : ℂ → ℂ := x.w ∘ Function.invFun y.w with hTdef
  set Λf : ℂ → ℂ := (x.smulUpper P).w ∘ Function.invFun (y.smulUpper P).w with hΛdef
  have hTc : Continuous T :=
    x.w_isQCAnalytic.1.1.continuous.comp (continuous_invFun y.w_isQCAnalytic.1.1)
  have hΛc : Continuous Λf := hu11.continuous.comp (continuous_invFun hv11)
  have hΛfac : ∀ ζ : ℂ, 0 < ζ.im → Λf ζ = moebiusMap Rx (T (moebiusMap Ry⁻¹ ζ)) := by
    intro ζ hζ
    set zz := Function.invFun (y.smulUpper P).w ζ with hzz
    have hz : 0 < zz.im := invFun_w_mapsTo (y.smulUpper P) hζ
    have hWvz : (y.smulUpper P).w zz = ζ := Function.rightInverse_invFun hvsurj ζ
    have hPz : 0 < (P.g zz).im := P.qc.mapsTo _ hz
    have hyPz : 0 < (y.w (P.g zz)).im := y.w_mapsTo_upper _ hPz
    have hRyinv : moebiusMap Ry⁻¹ ζ = y.w (P.g zz) := by
      conv_lhs => rw [← hWvz, hRy zz hz]
      rw [moebiusMap_mul Ry⁻¹ Ry _
        (moebiusDenom_ne_zero_of_im_ne_zero Ry (ne_of_gt hyPz)),
        inv_mul_cancel, moebiusMap_one]
    rw [hΛdef, hTdef]
    simp only [Function.comp_apply]
    rw [← hzz, hRx zz hz, hRyinv, Function.leftInverse_invFun y.w_injective (P.g zz)]
  have hFT : ∀ r : ℝ, F (r : ℂ) = T (r : ℂ) := by
    intro r
    obtain ⟨t', ht'⟩ := y.boundary_surjective r
    have hyw : y.w (t' : ℂ) = (r : ℂ) := by rw [y.w_ofReal t', ht']
    calc F (r : ℂ) = F (y.w (t' : ℂ)) := by rw [hyw]
      _ = x.w (t' : ℂ) := hb t'
      _ = T (r : ℂ) := by
          rw [hTdef]
          simp only [Function.comp_apply]
          congr 1
          apply y.w_injective
          rw [Function.rightInverse_invFun hysurj, hyw]
  -- the bad set on the real line and the good-point Möbius identity
  set Bt : Set ℝ := {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) = 0}
    ∪ ({s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0
        ∧ moebiusDenom S (F (moebiusMap Ry⁻¹ (s : ℂ))) = 0}
      ∪ {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0
        ∧ moebiusDenom Rx (F (moebiusMap Ry⁻¹ (s : ℂ))) = 0}) with hBtdef
  have hB1sub : {s : ℝ | moebiusDenom Ry⁻¹ (s : ℂ) = 0}.Subsingleton := by
    intro t₁ h₁ t₂ h₂
    have h := moebiusDenom_zero_subsingleton Ry⁻¹ h₁ h₂
    exact_mod_cast h
  have hBtfin : Bt.Finite := hB1sub.finite.union
    ((bad_denom_subsingleton hFinj S Ry).finite.union
      (bad_denom_subsingleton hFinj Rx Ry).finite)
  set Q : Matrix.SpecialLinearGroup (Fin 2) ℝ := S * Rx⁻¹ with hQdef
  have hgood : ∀ s : ℝ, s ∉ Bt → Y.w (s : ℂ) = moebiusMap Q (Λf (s : ℂ)) := by
    intro s hs
    simp only [hBtdef, Set.mem_union, Set.mem_setOf_eq, not_or] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    have hd1 : moebiusDenom Ry⁻¹ (s : ℂ) ≠ 0 := h1
    have hd2 : moebiusDenom S (F (moebiusMap Ry⁻¹ (s : ℂ))) ≠ 0 := fun h => h2 ⟨h1, h⟩
    have hd3 : moebiusDenom Rx (F (moebiusMap Ry⁻¹ (s : ℂ))) ≠ 0 := fun h => h3 ⟨h1, h⟩
    rw [hQdef]
    exact real_glue hY11.continuous hΛc hFc hTc S Rx Ry hYfac hΛfac hFT hd1 hd2 hd3
  -- the Möbius correction is affine
  have hQ10 : Q 1 0 = 0 := by
    set E : ℂ ≃ₜ ℂ := (hu11.homeomorph _).symm.trans
      ((hv11.homeomorph _).trans (hY11.homeomorph _)) with hEdef
    refine sl2_lower_left_eq_zero E Q
      (hBtfin.image (fun s : ℝ => (Λf (s : ℂ)).re)) ?_
    intro σ hσ
    obtain ⟨t', ht'⟩ := (x.smulUpper P).boundary_surjective σ
    set s : ℝ := (y.smulUpper P).boundary t' with hsdef
    have hWvt : (y.smulUpper P).w (t' : ℂ) = (s : ℂ) := by
      rw [hsdef]
      exact (y.smulUpper P).w_ofReal t'
    have hWut : (x.smulUpper P).w (t' : ℂ) = (σ : ℂ) := by
      rw [(x.smulUpper P).w_ofReal t', ht']
    have hinvWv : Function.invFun (y.smulUpper P).w (s : ℂ) = (t' : ℂ) := by
      apply (y.smulUpper P).w_injective
      rw [Function.rightInverse_invFun hvsurj, hWvt]
    have hΛs : Λf (s : ℂ) = (σ : ℂ) := by
      rw [hΛdef]
      simp only [Function.comp_apply]
      rw [hinvWv, hWut]
    have hsB : s ∉ Bt := by
      intro hmem
      refine hσ ⟨s, hmem, ?_⟩
      change (Λf (s : ℂ)).re = σ
      rw [hΛs, Complex.ofReal_re]
    have hWusymm : (hu11.homeomorph ((x.smulUpper P).w)).symm (σ : ℂ) = (t' : ℂ) := by
      rw [Homeomorph.symm_apply_eq, IsHomeomorph.homeomorph_apply]
      exact hWut.symm
    rw [hEdef]
    simp only [Homeomorph.trans_apply]
    rw [hWusymm, IsHomeomorph.homeomorph_apply, IsHomeomorph.homeomorph_apply,
      hWvt, hgood s hsB, hΛs]
  -- the transported candidate: an affine renormalization of the sandwich representative
  obtain ⟨a, bb, ha, haff⟩ := moebius_affine hQ10
  set F' : ℂ → ℂ := affineMap a⁻¹ (-(bb / a)) ∘ Y.w with hF'def
  have hF'K : IsQCGeometric F' K := isQCGeometric_affine_comp hYgeo0 (inv_ne_zero ha)
  have hF'app : ∀ z : ℂ, a * F' z + bb = Y.w z := by
    intro z
    rw [hF'def]
    simp only [Function.comp_apply, affineMap_apply]
    field_simp
    ring
  have hCh : ∀ ζ : ℂ, 0 < ζ.im → F' ζ = moebiusMap Rx (F (moebiusMap Ry⁻¹ ζ)) := by
    intro ζ hζ
    have hRyζ : 0 < (moebiusMap Ry⁻¹ ζ).im := moebiusMap_im_pos Ry⁻¹ hζ
    have hu : 0 < (F (moebiusMap Ry⁻¹ ζ)).im := hFup _ hRyζ
    have hQRx : Q * Rx = S := by
      rw [hQdef, mul_assoc, inv_mul_cancel, mul_one]
    have h1 : Y.w ζ = moebiusMap Q (moebiusMap Rx (F (moebiusMap Ry⁻¹ ζ))) := by
      rw [hYfac ζ hζ,
        moebiusMap_mul Q Rx _ (moebiusDenom_ne_zero_of_im_ne_zero Rx (ne_of_gt hu)), hQRx]
    have h2 : a * F' ζ + bb = a * moebiusMap Rx (F (moebiusMap Ry⁻¹ ζ)) + bb := by
      rw [hF'app, h1, haff]
    exact mul_left_cancel₀ ha (add_right_cancel h2)
  -- the boundary clause
  have hbdry : ∀ t : ℝ, F' ((y.smulUpper P).w (t : ℂ)) = (x.smulUpper P).w (t : ℂ) := by
    have hTbfin : ((y.smulUpper P).boundary ⁻¹' Bt).Finite :=
      Set.Finite.preimage ((y.smulUpper P).boundary_strictMono.injective.injOn) hBtfin
    have hf₁ : Continuous fun t : ℝ => F' ((y.smulUpper P).w (t : ℂ)) := by
      have hF'c : Continuous F' := by
        rw [hF'def]
        exact (affineMap_continuous _ _).comp hY11.continuous
      exact hF'c.comp (hv11.continuous.comp Complex.continuous_ofReal)
    have hf₂ : Continuous fun t : ℝ => (x.smulUpper P).w (t : ℂ) :=
      hu11.continuous.comp Complex.continuous_ofReal
    have hEqOn : Set.EqOn (fun t : ℝ => F' ((y.smulUpper P).w (t : ℂ)))
        (fun t : ℝ => (x.smulUpper P).w (t : ℂ)) ((y.smulUpper P).boundary ⁻¹' Bt)ᶜ := by
      intro t ht
      have hsB : (y.smulUpper P).boundary t ∉ Bt := ht
      have hWvt : (y.smulUpper P).w (t : ℂ) = (((y.smulUpper P).boundary t : ℝ) : ℂ) :=
        (y.smulUpper P).w_ofReal t
      have hinvWv : Function.invFun (y.smulUpper P).w
          (((y.smulUpper P).boundary t : ℝ) : ℂ) = (t : ℂ) := by
        apply (y.smulUpper P).w_injective
        rw [Function.rightInverse_invFun hvsurj, hWvt]
      have hΛt : Λf (((y.smulUpper P).boundary t : ℝ) : ℂ)
          = (x.smulUpper P).w (t : ℂ) := by
        rw [hΛdef]
        simp only [Function.comp_apply]
        rw [hinvWv]
      have h1 : a * F' (((y.smulUpper P).boundary t : ℝ) : ℂ) + bb
          = a * Λf (((y.smulUpper P).boundary t : ℝ) : ℂ) + bb := by
        rw [hF'app, hgood _ hsB, haff]
      have h2 := mul_left_cancel₀ ha (add_right_cancel h1)
      change F' ((y.smulUpper P).w (t : ℂ)) = (x.smulUpper P).w (t : ℂ)
      rw [hWvt, h2, hΛt]
    have hfun := Continuous.ext_on (dense_compl_finite hTbfin) hf₁ hf₂ hEqOn
    exact fun t => congrFun hfun t
  -- the two-sided group compatibility clauses
  have hfwdC : ∀ W ∈ (y.smulUpper P).group, ∃ W' ∈ (x.smulUpper P).group,
      ∀ z : ℂ, 0 < z.im → F' (moebiusMap W z) = moebiusMap W' (F' z) := by
    intro W hW
    obtain ⟨γ, hγ, hyc⟩ := w_conj_of_mem_group (y.smulUpper P) hW
    obtain ⟨γ', hγ', hPc⟩ := P.compat γ hγ
    obtain ⟨V, hV, hyV⟩ := w_conj_of_mem_base y hγ'
    have hRyV := group_transport y P hRy hPc hyV hyc
    obtain ⟨V', hV', hFV⟩ := hfwd V hV
    obtain ⟨γ₃, hγ₃, hxc⟩ := w_conj_of_mem_group x hV'
    obtain ⟨γ₄, hγ₄, hPc'⟩ := P.compat' γ₃ hγ₃
    obtain ⟨W', hW', hxU⟩ := w_conj_of_mem_base (x.smulUpper P) hγ₄
    have hRxV' := group_transport x P hRx hPc' hxc hxU
    exact ⟨W', hW', conj_chain hCh hFup (conj_pull hRyV) hFV hRxV'⟩
  have hbwdC : ∀ W' ∈ (x.smulUpper P).group, ∃ W ∈ (y.smulUpper P).group,
      ∀ z : ℂ, 0 < z.im → F' (moebiusMap W z) = moebiusMap W' (F' z) := by
    intro W' hW'
    obtain ⟨γ₄, hγ₄, hxU⟩ := w_conj_of_mem_group (x.smulUpper P) hW'
    obtain ⟨γ₃, hγ₃, hPc'⟩ := P.compat γ₄ hγ₄
    obtain ⟨V', hV', hxc⟩ := w_conj_of_mem_base x hγ₃
    have hRxV' := group_transport x P hRx hPc' hxc hxU
    obtain ⟨V, hV, hFV⟩ := hbwd V' hV'
    obtain ⟨γ', hγ', hyV⟩ := w_conj_of_mem_group y hV
    obtain ⟨γ, hγ, hPc⟩ := P.compat' γ' hγ'
    obtain ⟨W, hW, hyc⟩ := w_conj_of_mem_base (y.smulUpper P) hγ
    have hRyV := group_transport y P hRy hPc hyV hyc
    exact ⟨W, hW, conj_chain hCh hFup (conj_pull hRyV) hFV hRxV'⟩
  exact ⟨F', hF'K, hbdry, hfwdC, hbwdC⟩

/-- A re-marking followed by a re-marking whose map cancels it on the upper half plane
returns the original boundary values: the comparison homeomorphism of the two normalized
solutions is a Möbius factor fixing `0` and `1`, hence fixes the real line. -/
theorem smulUpper_inv_boundary (x : TeichRep Γ₀) (P P' : ModGroupUpper Γ₀)
    (hcanc : ∀ z : ℂ, 0 < z.im → P.g (P'.g z) = z) :
    ∀ t : ℝ, ((x.smulUpper P).smulUpper P').w (t : ℂ) = x.w (t : ℂ) := by
  obtain ⟨Rx, hRx⟩ := x.smulUpper_w P
  obtain ⟨R₂, hR₂⟩ := (x.smulUpper P).smulUpper_w P'
  have hx11 : IsHomeomorph x.w := x.w_isQCAnalytic.1.1
  have h211 : IsHomeomorph ((x.smulUpper P).smulUpper P').w :=
    ((x.smulUpper P).smulUpper P').w_isQCAnalytic.1.1
  have hxsurj : Function.Surjective x.w := hx11.bijective.surjective
  have hfac : ∀ ζ : ℂ, 0 < ζ.im →
      ((x.smulUpper P).smulUpper P').w ζ = moebiusMap (R₂ * Rx) (x.w ζ) := by
    intro ζ hζ
    have hgz : 0 < (P'.g ζ).im := P'.qc.mapsTo ζ hζ
    have hxζ : 0 < (x.w ζ).im := x.w_mapsTo_upper ζ hζ
    have h1 : (x.smulUpper P).w (P'.g ζ) = moebiusMap Rx (x.w ζ) := by
      rw [hRx _ hgz, hcanc ζ hζ]
    rw [hR₂ ζ hζ, h1,
      moebiusMap_mul R₂ Rx _ (moebiusDenom_ne_zero_of_im_ne_zero Rx (ne_of_gt hxζ))]
  set Λ : ℂ ≃ₜ ℂ := (hx11.homeomorph _).symm.trans (h211.homeomorph _) with hΛdef
  have hΛint : ∀ ζ : ℂ, 0 < ζ.im → Λ ζ = moebiusMap (R₂ * Rx)
      (id (moebiusMap (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ ζ)) := by
    intro ζ hζ
    have hinv : Function.invFun x.w ζ = (hx11.homeomorph x.w).symm ζ := by
      rw [invFun_eq_homeoSymm hx11]
    have hzin : 0 < ((hx11.homeomorph x.w).symm ζ).im := by
      rw [← hinv]
      exact invFun_w_mapsTo x hζ
    have hxz : x.w ((hx11.homeomorph x.w).symm ζ) = ζ := by
      rw [← hinv]
      exact Function.rightInverse_invFun hxsurj ζ
    rw [hΛdef]
    simp only [Homeomorph.trans_apply]
    rw [IsHomeomorph.homeomorph_apply, hfac _ hzin, hxz, inv_one, moebiusMap_one, id_eq]
  have hsymm0 : (hx11.homeomorph x.w).symm 0 = 0 := by
    rw [Homeomorph.symm_apply_eq, IsHomeomorph.homeomorph_apply, x.w_zero]
  have hsymm1 : (hx11.homeomorph x.w).symm 1 = 1 := by
    rw [Homeomorph.symm_apply_eq, IsHomeomorph.homeomorph_apply, x.w_one]
  have h0 : Λ 0 = 0 := by
    rw [hΛdef]
    simp only [Homeomorph.trans_apply]
    rw [hsymm0, IsHomeomorph.homeomorph_apply, ((x.smulUpper P).smulUpper P').w_zero]
  have h1' : Λ 1 = 1 := by
    rw [hΛdef]
    simp only [Homeomorph.trans_apply]
    rw [hsymm1, IsHomeomorph.homeomorph_apply, ((x.smulUpper P).smulUpper P').w_one]
  have hfix := upper_factor_fix_real Λ continuous_id (fun r => rfl) (R₂ * Rx) 1 hΛint h0 h1'
  intro t
  have hxw : x.w (t : ℂ) = ((x.boundary t : ℝ) : ℂ) := x.w_ofReal t
  have hΛx : Λ (x.w (t : ℂ)) = ((x.smulUpper P).smulUpper P').w (t : ℂ) := by
    rw [hΛdef]
    simp only [Homeomorph.trans_apply]
    have hsymmt : (hx11.homeomorph x.w).symm (x.w (t : ℂ)) = (t : ℂ) := by
      rw [Homeomorph.symm_apply_eq, IsHomeomorph.homeomorph_apply]
    rw [hsymmt, IsHomeomorph.homeomorph_apply]
  calc ((x.smulUpper P).smulUpper P').w (t : ℂ) = Λ (x.w (t : ℂ)) := hΛx.symm
    _ = Λ ((x.boundary t : ℝ) : ℂ) := by rw [hxw]
    _ = ((x.boundary t : ℝ) : ℂ) := hfix (x.boundary t)
    _ = x.w (t : ℂ) := hxw.symm

/-- **Re-markings are isometries of the intrinsic distance**: candidate transport applied
to the re-marking and to its inverse re-marking. -/
theorem teichDistG_smulUpper (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (P : ModGroupUpper Γ₀) (x y : TeichRep Γ₀) :
    teichDistG (x.smulUpper P) (y.smulUpper P) = teichDistG x y := by
  classical
  obtain ⟨g₂, g₂inv, κ₃, hκ₃1, hqc₃, hg₂⟩ := isQCUpper_flip P.hκ P.qc
  have hcompat : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      g₂ (moebiusMap γ z) = moebiusMap γ' (g₂ z) := by
    intro γ hγ
    obtain ⟨δ, hδ, hPδ⟩ := P.compat' γ hγ
    have hinv := inv_conj_of_conj P.qc.mapsTo' P.qc.left_inv P.qc.right_inv hPδ
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    rw [hg₂ _ hγz, hg₂ z hz]
    exact hinv z hz
  have hcompat' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      g₂ (moebiusMap γ z) = moebiusMap γ' (g₂ z) := by
    intro γ' hγ'
    obtain ⟨δ, hδ, hPδ⟩ := P.compat γ' hγ'
    have hinv := inv_conj_of_conj P.qc.mapsTo' P.qc.left_inv P.qc.right_inv hPδ
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have hδz : 0 < (moebiusMap δ z).im := moebiusMap_im_pos δ hz
    rw [hg₂ _ hδz, hg₂ z hz]
    exact hinv z hz
  set Pinv : ModGroupUpper Γ₀ := ⟨g₂, g₂inv, κ₃, hκ₃1, hqc₃, hcompat, hcompat'⟩
    with hPinvdef
  have hcanc : ∀ z : ℂ, 0 < z.im → P.g (Pinv.g z) = z := by
    intro z hz
    change P.g (g₂ z) = z
    rw [hg₂ z hz]
    exact P.qc.right_inv z hz
  have hxb := smulUpper_inv_boundary x P Pinv hcanc
  have hyb := smulUpper_inv_boundary y P Pinv hcanc
  have hsub1 : gDilatationSet x y ⊆ gDilatationSet (x.smulUpper P) (y.smulUpper P) :=
    fun K hK => mem_gDilatationSet_smulUpper hΓ₀ hfree hcc P hK
  have hsub2 : gDilatationSet (x.smulUpper P) (y.smulUpper P) ⊆ gDilatationSet x y := by
    intro K hK
    exact mem_gDilatationSet_congr hxb hyb
      (mem_gDilatationSet_smulUpper hΓ₀ hfree hcc Pinv hK)
  have hset : gDilatationSet (x.smulUpper P) (y.smulUpper P) = gDilatationSet x y :=
    Set.Subset.antisymm hsub2 hsub1
  unfold teichDistG
  rw [hset]

/-- Re-markings act on Teichmüller space by isometries of the descended distance. -/
theorem Teich.distG_smulUpper (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (P : ModGroupUpper Γ₀) (a b : Teich Γ₀) :
    Teich.distG (P • a) (P • b) = Teich.distG a b := by
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk b
  change Teich.distG (P • Teich.mk x) (P • Teich.mk y)
    = Teich.distG (Teich.mk x) (Teich.mk y)
  rw [Teich.smulUpper_mk, Teich.smulUpper_mk]
  exact teichDistG_smulUpper hΓ₀ hfree hcc P x y

/-! ## Mumford subconvergence in the intrinsic metric -/

/-- The composite of a solution with the choice inverse of another solution is a marked
candidate: the boundary transition is the left-inverse identity, and the two compatibility
clauses conjugate the base equivariance of the two representatives through the inverse. -/
theorem isMarkedCandidate_w_comp_invFun (Z y : TeichRep Γ₀) :
    IsMarkedCandidate Z y (Z.w ∘ Function.invFun y.w) := by
  have hyinj := y.w_injective
  have hysurj : Function.Surjective y.w := y.w_isQCAnalytic.1.1.bijective.surjective
  have hinvconj : ∀ (γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ z : ℂ, 0 < z.im → y.w (moebiusMap γ z) = moebiusMap W (y.w z)) →
      ∀ z : ℂ, 0 < z.im →
        Function.invFun y.w (moebiusMap W z) = moebiusMap γ (Function.invFun y.w z) :=
    fun γ W hid => inv_conj_of_conj (fun z hz => invFun_w_mapsTo y hz)
      (fun z _ => Function.leftInverse_invFun hyinj z)
      (fun z _ => Function.rightInverse_invFun hysurj z) hid
  refine ⟨fun t => ?_, ?_, ?_⟩
  · change Z.w (Function.invFun y.w (y.w t)) = Z.w t
    rw [Function.leftInverse_invFun hyinj]
  · intro W hW
    obtain ⟨γ, hγ, hyid⟩ := w_conj_of_mem_group y hW
    obtain ⟨W', hW', hZid⟩ := w_conj_of_mem_base Z hγ
    refine ⟨W', hW', fun z hz => ?_⟩
    have hζ : 0 < (Function.invFun y.w z).im := invFun_w_mapsTo y hz
    change Z.w (Function.invFun y.w (moebiusMap W z))
      = moebiusMap W' (Z.w (Function.invFun y.w z))
    rw [hinvconj γ W hyid z hz, hZid _ hζ]
  · intro W' hW'
    obtain ⟨γ, hγ, hZid⟩ := w_conj_of_mem_group Z hW'
    obtain ⟨W, hW, hyid⟩ := w_conj_of_mem_base y hγ
    refine ⟨W, hW, fun z hz => ?_⟩
    have hζ : 0 < (Function.invFun y.w z).im := invFun_w_mapsTo y hz
    change Z.w (Function.invFun y.w (moebiusMap W z))
      = moebiusMap W' (Z.w (Function.invFun y.w z))
    rw [hinvconj γ W hyid z hz, hZid _ hζ]

/-- **Squeeze brick for the intrinsic distance.** Marked candidates with dilatations
tending to `1` give vanishing intrinsic distance in the limit. -/
theorem tendsto_teichDistG_zero_of_candidates {x : ℕ → TeichRep Γ₀} {y : TeichRep Γ₀}
    {F : ℕ → ℂ → ℂ} {K : ℕ → ℝ} (hF : ∀ n, IsQCGeometric (F n) (K n))
    (hc : ∀ n, IsMarkedCandidate (x n) y (F n))
    (hK : Filter.Tendsto K Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => teichDistG (x n) y) Filter.atTop (nhds 0) := by
  have hub : ∀ n, teichDistG (x n) y ≤ (1 / 2) * Real.log (K n) := fun n =>
    teichDistG_le_of_candidate (hF n) (hc n)
  have hlb : ∀ n, 0 ≤ teichDistG (x n) y := fun n => teichDistG_nonneg _ _
  have h1 : Filter.Tendsto (fun n => Real.log (K n)) Filter.atTop (nhds (Real.log 1)) :=
    ((Real.continuousAt_log one_ne_zero).tendsto).comp hK
  rw [Real.log_one] at h1
  have h2 : Filter.Tendsto (fun n => (1 / 2 : ℝ) * Real.log (K n)) Filter.atTop
      (nhds ((1 / 2 : ℝ) * 0)) := h1.const_mul _
  rw [mul_zero] at h2
  exact squeeze_zero hlb hub h2

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: one declaration chains two remark composites, two flip
-- representatives with their factorizations, and the pointwise Möbius identity chains.
/-- **Per-index marked candidate.** An upper-half-plane conjugacy `h` carrying the limit
tuple `ρ` to the marked generators of `X` at Beltrami bound `κ`, together with a base
conjugacy `v₀` carrying `Γ₀` to the limit group both ways and a realization `y` of `v₀`,
produces a moduli re-marking `F` of `X` and a `(1 + κ)/(1 − κ)`-quasiconformal
group-marked candidate from `y` to the re-marked representative. -/
theorem marked_candidate_of_upper_conjugacy {ι : Type}
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (X : TeichRep Γ₀)
    {gensX : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hmemX : ∀ i, gensX i ∈ X.group)
    (hclosX : Subgroup.closure (Set.range gensX) = X.group)
    {h hinv : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hqc : IsQCUpper h hinv κ)
    (hgen : ∀ i, ∀ z : ℂ, 0 < z.im → h (moebiusMap (ρ i) z) = moebiusMap (gensX i) (h z))
    {v₀ v₀inv : ℂ → ℂ} {κᵥ : ℝ} (hκᵥ1 : κᵥ < 1) (hv₀qc : IsQCUpper v₀ v₀inv κᵥ)
    (hv₀fwd : ∀ γ ∈ Γ₀, ∃ W ∈ Subgroup.closure (Set.range ρ),
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z))
    (hv₀rev : ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ γ ∈ Γ₀,
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z))
    (y : TeichRep Γ₀) (R₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hyfac : ∀ z : ℂ, 0 < z.im → y.w z = moebiusMap R₀ (v₀ z)) :
    ∃ (F : ModGroupUpper Γ₀) (C : ℂ → ℂ),
      IsQCGeometric C ((1 + κ) / (1 - κ)) ∧
      IsMarkedCandidate (X.smulUpper F) y C := by
  classical
  have hden : ∀ (V : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ), 0 < z.im →
      moebiusDenom V z ≠ 0 := fun V z hz =>
    moebiusDenom_ne_zero_of_im_ne_zero V (ne_of_gt hz)
  -- group-level upgrade of the generator equivariance and its reverse
  have hC1 := equivariant_on_closure hmemX hqc.mapsTo hqc.mapsTo' hqc.left_inv
    hqc.right_inv hgen
  have hgenInv : ∀ i, ∀ z : ℂ, 0 < z.im →
      hinv (moebiusMap (gensX i) z) = moebiusMap (ρ i) (hinv z) := fun i =>
    inv_conj_of_conj hqc.mapsTo' hqc.left_inv hqc.right_inv (hgen i)
  have hC1rev := equivariant_on_closure
    (Γ := Subgroup.closure (Set.range ρ)) (gens := ρ)
    (fun i => Subgroup.subset_closure ⟨i, rfl⟩) (ρ := gensX)
    hqc.mapsTo' hqc.mapsTo hqc.right_inv hqc.left_inv hgenInv
  rw [hclosX] at hC1rev
  -- flip representative of `h` and its Möbius normalization
  obtain ⟨Y, hcoeffY⟩ := flip_rep hκ1 hqc
  obtain ⟨P, hP⟩ := exists_sl2_factorization_of_eq_coeff Y hκ1 hqc hcoeffY
  -- the coefficient bound of `Y` on the upper half plane
  have hbndY : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖Y.b.μ z‖ ≤ κ := by
    filter_upwards [hcoeffY, hqc.jac, hqc.belt] with z hco hj hb
    have hdzne : dz h z ≠ 0 := by
      intro h0
      rw [det_fderiv_eq_wirtinger, h0] at hj
      simp only [norm_zero] at hj
      nlinarith [norm_nonneg (dzbar h z), sq_nonneg ‖dzbar h z‖]
    have hpos : 0 < ‖dz h z‖ := norm_pos_iff.mpr hdzne
    have heq : ‖Y.b.μ z‖ * ‖dz h z‖ = ‖dzbar h z‖ := by rw [← norm_mul, ← hco]
    have hle : ‖Y.b.μ z‖ * ‖dz h z‖ ≤ κ * ‖dz h z‖ := by
      rw [heq]
      exact hb
    exact le_of_mul_le_mul_right hle hpos
  have hmid : IsQCUpper Y.w (Function.invFun Y.w) κ := isQCUpper_w_of_bound Y hbndY
  -- the inner composite `Y.w ∘ v₀` and its flip representative
  have hqcA := Y.isQCUpper_remark (modGroupUpperBot hκᵥ1 hv₀qc)
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ] at hqcA
  have hκA1 : (max κᵥ 0 + Y.b.normInf) / (1 + max κᵥ 0 * Y.b.normInf) < 1 :=
    comb_lt_one (le_max_right _ _) (max_lt hκᵥ1 one_pos) Y.b.normInf_nonneg
      Y.b.normInf_lt_one
  obtain ⟨YA, hcoeffA⟩ := flip_rep hκA1 hqcA
  obtain ⟨RA, hRA⟩ := exists_sl2_factorization_of_eq_coeff YA hκA1 hqcA hcoeffA
  -- the Möbius correction and the double flip
  obtain ⟨κ₂, hκ₂1, hqc₂⟩ := isQCUpper_invW_moebius YA (P⁻¹ * RA⁻¹)⁻¹
  rw [inv_inv] at hqc₂
  obtain ⟨g₂, g₂inv, κ₃, hκ₃1, hqc₃, hg₂eq⟩ := isQCUpper_flip hκ₂1 hqc₂
  -- the outer inverse of the normalized solution of `X`
  obtain ⟨bX', hbX'⟩ := isQCAnalytic_invFun X.w_isQCAnalytic
  have hinjX := X.w_injective
  have hsurjX : Function.Surjective X.w := X.w_isQCAnalytic.1.1.bijective.surjective
  have h0X : Function.invFun X.w 0 = 0 := by
    apply hinjX
    rw [Function.rightInverse_invFun hsurjX, X.w_zero]
  have h1X : Function.invFun X.w 1 = 1 := by
    apply hinjX
    rw [Function.rightInverse_invFun hsurjX, X.w_one]
  obtain ⟨XI, hXI⟩ := teichRepBot hbX' h0X h1X
    (fun z => invFun_conj hinjX hsurjX X.w_conj z)
  have hqcF := XI.isQCUpper_remark (modGroupUpperBot hκ₃1 hqc₃)
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ,
    hXI, invFun_invFun hinjX hsurjX] at hqcF
  have hκF1 : (max κ₃ 0 + XI.b.normInf) / (1 + max κ₃ 0 * XI.b.normInf) < 1 :=
    comb_lt_one (le_max_right _ _) (max_lt hκ₃1 one_pos) XI.b.normInf_nonneg
      XI.b.normInf_lt_one
  -- pointwise identification of the re-marking composite on the upper half plane
  have hXw_g : ∀ z : ℂ, 0 < z.im →
      X.w ((Function.invFun X.w ∘ g₂) z) = h (v₀ z) := by
    intro z hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hYv : 0 < (Y.w (v₀ z)).im := Y.w_mapsTo_upper _ hv₀z
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    have e1 : X.w ((Function.invFun X.w ∘ g₂) z) = g₂ z :=
      Function.rightInverse_invFun hsurjX (g₂ z)
    have e2 : g₂ z = moebiusMap (P⁻¹ * RA⁻¹) (YA.w z) := hg₂eq z hz
    have e3 : YA.w z = moebiusMap RA (Y.w (v₀ z)) := hRA z hz
    have e4 : moebiusMap (P⁻¹ * RA⁻¹) (moebiusMap RA (Y.w (v₀ z)))
        = moebiusMap P⁻¹ (Y.w (v₀ z)) := by
      rw [moebiusMap_mul (P⁻¹ * RA⁻¹) RA _ (hden RA _ hYv), mul_assoc, inv_mul_cancel,
        mul_one]
    have e5 : Y.w (v₀ z) = moebiusMap P (h (v₀ z)) := hP _ hv₀z
    have e6 : moebiusMap P⁻¹ (Y.w (v₀ z)) = h (v₀ z) := by
      rw [e5, moebiusMap_mul P⁻¹ P _ (hden P _ hh), inv_mul_cancel, moebiusMap_one]
    rw [e1, e2, e3, e4, e6]
  have hgid : ∀ z : ℂ, 0 < z.im →
      (Function.invFun X.w ∘ g₂) z = Function.invFun X.w (h (v₀ z)) := by
    intro z hz
    have e := hXw_g z hz
    have e' : Function.invFun X.w (X.w ((Function.invFun X.w ∘ g₂) z))
        = (Function.invFun X.w ∘ g₂) z :=
      Function.leftInverse_invFun hinjX _
    rw [e] at e'
    exact e'.symm
  -- inverse equivariance of the choice inverse of the normalized solution
  have hXinvconj : ∀ (γ' W' : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      (∀ z : ℂ, 0 < z.im → X.w (moebiusMap γ' z) = moebiusMap W' (X.w z)) →
      ∀ z : ℂ, 0 < z.im →
        Function.invFun X.w (moebiusMap W' z) = moebiusMap γ' (Function.invFun X.w z) :=
    fun γ' W' hXid => inv_conj_of_conj (fun z hz => invFun_w_mapsTo X hz)
      (fun z _ => Function.leftInverse_invFun hinjX z)
      (fun z _ => Function.rightInverse_invFun hsurjX z) hXid
  -- forward compatibility of the re-marking composite
  have hcompat : ∀ γ ∈ Γ₀, ∃ γ' ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      (Function.invFun X.w ∘ g₂) (moebiusMap γ z)
        = moebiusMap γ' ((Function.invFun X.w ∘ g₂) z) := by
    intro γ hγ
    obtain ⟨W, hWmem, hWid⟩ := hv₀fwd γ hγ
    obtain ⟨W', hW'mem, hfwd', -⟩ := hC1 W hWmem
    obtain ⟨γ', hγ', hXid⟩ := w_conj_of_mem_group X hW'mem
    refine ⟨γ', hγ', fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    rw [hgid _ hγz, hWid z hz, hfwd' _ hv₀z, hXinvconj γ' W' hXid _ hh, ← hgid z hz]
  -- backward compatibility of the re-marking composite
  have hcompat' : ∀ γ' ∈ Γ₀, ∃ γ ∈ Γ₀, ∀ z : ℂ, 0 < z.im →
      (Function.invFun X.w ∘ g₂) (moebiusMap γ z)
        = moebiusMap γ' ((Function.invFun X.w ∘ g₂) z) := by
    intro γ' hγ'
    obtain ⟨W', hW'mem, hXid⟩ := w_conj_of_mem_base X hγ'
    obtain ⟨W, hWmem, -, hhid⟩ := hC1rev W' hW'mem
    obtain ⟨γ, hγ, hγid⟩ := hv₀rev W hWmem
    refine ⟨γ, hγ, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    rw [hgid _ hγz, hγid z hz, hhid _ hv₀z, hXinvconj γ' W' hXid _ hh, ← hgid z hz]
  -- the moduli re-marking
  obtain ⟨F, hFg⟩ : ∃ F : ModGroupUpper Γ₀, F.g = Function.invFun X.w ∘ g₂ :=
    ⟨⟨Function.invFun X.w ∘ g₂, g₂inv ∘ X.w,
      (max κ₃ 0 + XI.b.normInf) / (1 + max κ₃ 0 * XI.b.normInf), hκF1, hqcF,
      hcompat, hcompat'⟩, rfl⟩
  -- the re-marked representative and its Möbius factorization through `Y.w ∘ v₀`
  obtain ⟨R', hR'⟩ := X.smulUpper_w F
  have hZfac : ∀ z : ℂ, 0 < z.im →
      (X.smulUpper F).w z = moebiusMap (R' * P⁻¹) (Y.w (v₀ z)) := by
    intro z hz
    have hv₀z : 0 < (v₀ z).im := hv₀qc.mapsTo z hz
    have hh : 0 < (h (v₀ z)).im := hqc.mapsTo _ hv₀z
    have hYv : 0 < (Y.w (v₀ z)).im := Y.w_mapsTo_upper _ hv₀z
    have e0 : X.w (F.g z) = h (v₀ z) := by
      rw [hFg]
      exact hXw_g z hz
    have e5 : Y.w (v₀ z) = moebiusMap P (h (v₀ z)) := hP _ hv₀z
    have e6 : moebiusMap P⁻¹ (Y.w (v₀ z)) = h (v₀ z) := by
      rw [e5, moebiusMap_mul P⁻¹ P _ (hden P _ hh), inv_mul_cancel, moebiusMap_one]
    rw [hR' z hz, e0, ← e6, moebiusMap_mul R' P⁻¹ _ (hden P⁻¹ _ hYv)]
  -- the plane candidate
  have hyinj := y.w_injective
  have hysurj : Function.Surjective y.w := y.w_isQCAnalytic.1.1.bijective.surjective
  obtain ⟨by', hy'⟩ := isQCAnalytic_invFun y.w_isQCAnalytic
  obtain ⟨bC, -, hbC⟩ := exists_isQCAnalytic_comp (X.smulUpper F).w_isQCAnalytic hy'
  have hCsym : ∀ z : ℂ, ((X.smulUpper F).w ∘ Function.invFun y.w) (starRingEnd ℂ z)
      = starRingEnd ℂ (((X.smulUpper F).w ∘ Function.invFun y.w) z) := by
    intro z
    have e1 : Function.invFun y.w (starRingEnd ℂ z)
        = starRingEnd ℂ (Function.invFun y.w z) :=
      invFun_conj hyinj hysurj y.w_conj z
    change (X.smulUpper F).w (Function.invFun y.w (starRingEnd ℂ z))
        = starRingEnd ℂ ((X.smulUpper F).w (Function.invFun y.w z))
    rw [e1, (X.smulUpper F).w_conj]
  have hCfac : ∀ z : ℂ, 0 < z.im →
      ((X.smulUpper F).w ∘ Function.invFun y.w) z
        = moebiusMap (R' * P⁻¹) (Y.w (moebiusMap R₀⁻¹ z)) := by
    intro z hz
    have hζ : 0 < (Function.invFun y.w z).im := invFun_w_mapsTo y hz
    have hv₀ζ : 0 < (v₀ (Function.invFun y.w z)).im := hv₀qc.mapsTo _ hζ
    have hyz : y.w (Function.invFun y.w z) = z := Function.rightInverse_invFun hysurj z
    have e2 : moebiusMap R₀⁻¹ (y.w (Function.invFun y.w z))
        = v₀ (Function.invFun y.w z) := by
      rw [hyfac _ hζ, moebiusMap_mul R₀⁻¹ R₀ _ (hden R₀ _ hv₀ζ), inv_mul_cancel,
        moebiusMap_one]
    have hval : v₀ (Function.invFun y.w z) = moebiusMap R₀⁻¹ z := by
      rw [← e2, hyz]
    change (X.smulUpper F).w (Function.invFun y.w z) = _
    rw [hZfac _ hζ, hval]
  have hgeo : IsQCGeometric ((X.smulUpper F).w ∘ Function.invFun y.w)
      ((1 + κ) / (1 - κ)) :=
    isQCGeometric_K_of_upper_moebius_factor hbC hCsym hκ0 hκ1 hmid (R' * P⁻¹) R₀⁻¹ hCfac
  exact ⟨F, (X.smulUpper F).w ∘ Function.invFun y.w, hgeo,
    isMarkedCandidate_w_comp_invFun (X.smulUpper F) y⟩

set_option maxHeartbeats 400000 in
-- Heartbeat budget doubled: one declaration assembles the Mumford extraction, the Marden
-- diagonalization, the base-conjugacy flip with its two group upgrades, the realization
-- of the limit representative, and the per-index marked-candidate squeeze.
/-- **Mumford subconvergence in the intrinsic Teichmüller metric.** A thick sequence with
uniform area bound subconverges, modulo upper-half-plane re-markings, to a point of
Teichmüller space in the descended intrinsic distance: the candidates realizing the
convergence are group-marked. -/
theorem mumford_dG_subconvergence (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    {ε : ℝ} (hε : 0 < ε) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (x : ℕ → TeichRep Γ₀) (hthick : ∀ n, ε ≤ systoleRep (x n))
    (harea : ∀ n, HasAreaBound (x n).group A) :
    ∃ (φ : ℕ → ℕ) (F : ℕ → ModGroupUpper Γ₀) (y : TeichRep Γ₀), StrictMono φ ∧
      Filter.Tendsto (fun k => Teich.distG (F k • Teich.mk (x (φ k))) (Teich.mk y))
        Filter.atTop (nhds 0) := by
  classical
  -- Mumford extraction: subsequence, marked generators, and the limit tuple
  obtain ⟨φ₀, gens, ρ, hφ₀mono, hmem, hclos, hconv, hgapρ, -, -, hccρ, -⟩ :=
    mumford_subconvergence_thick hΓ₀ hfree hcc hε hA x hthick harea
  -- Marden stability along the extracted subsequence
  have hΓf : ∀ n, IsFuchsianGroup ((x (φ₀ n)).group) := fun n =>
    TeichRep.isFuchsian_group hΓ₀ hfree (x (φ₀ n))
  have hgapf : ∀ n, ∀ γ ∈ (x (φ₀ n)).group, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)| :=
    fun n γ hγ hnt => (trace_gap_of_systole hε (hthick (φ₀ n)) hγ hnt).1
  have hRS1 := exists_equivariant_upper_conjugacy_K_to_one hε
    (fun n => (x (φ₀ n)).group) hΓf hgapf gens hmem ρ hconv hgapρ hccρ
  -- diagonalization at the coefficient scales `1/(j+2)`
  have hκpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 2) := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    positivity
  have hκ1 : ∀ j : ℕ, 1 / ((j : ℝ) + 2) < 1 := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨ψ, hψmono, hψP⟩ := diag (fun j => hRS1 (1 / ((j : ℝ) + 2)) (hκpos j))
  choose h hinv hqc hgen using hψP
  -- the base conjugacy `v₀`: the flipped composite at index `0`
  obtain ⟨b₀', hb₀'⟩ := isQCAnalytic_invFun (x (φ₀ (ψ 0))).w_isQCAnalytic
  have hinj₀ := (x (φ₀ (ψ 0))).w_injective
  have hsurj₀ : Function.Surjective (x (φ₀ (ψ 0))).w :=
    (x (φ₀ (ψ 0))).w_isQCAnalytic.1.1.bijective.surjective
  have h0₀ : Function.invFun (x (φ₀ (ψ 0))).w 0 = 0 := by
    apply hinj₀
    rw [Function.rightInverse_invFun hsurj₀, (x (φ₀ (ψ 0))).w_zero]
  have h1₀ : Function.invFun (x (φ₀ (ψ 0))).w 1 = 1 := by
    apply hinj₀
    rw [Function.rightInverse_invFun hsurj₀, (x (φ₀ (ψ 0))).w_one]
  obtain ⟨W0I, hW0I⟩ := teichRepBot hb₀' h0₀ h1₀
    (fun z => invFun_conj hinj₀ hsurj₀ (x (φ₀ (ψ 0))).w_conj z)
  have hqcu₀ := W0I.isQCUpper_remark (modGroupUpperBot (hκ1 0) (hqc 0))
  rw [modGroupUpperBot_g, modGroupUpperBot_ginv, modGroupUpperBot_κ,
    hW0I, invFun_invFun hinj₀ hsurj₀] at hqcu₀
  obtain ⟨v₀, v₀i, κᵥ, hκᵥ1, hv₀qc, hv₀eq⟩ := isQCUpper_flip
    (comb_lt_one (le_max_right _ _) (max_lt (hκ1 0) one_pos)
      W0I.b.normInf_nonneg W0I.b.normInf_lt_one) hqcu₀
  -- forward and reverse group upgrades at index `0`
  have hgenInv₀ : ∀ i, ∀ z : ℂ, 0 < z.im →
      hinv 0 (moebiusMap (gens (ψ 0) i) z) = moebiusMap (ρ i) (hinv 0 z) := fun i =>
    inv_conj_of_conj (hqc 0).mapsTo' (hqc 0).left_inv (hqc 0).right_inv (hgen 0 i)
  have hC1fwd₀ := equivariant_on_closure (hmem (ψ 0)) (hqc 0).mapsTo (hqc 0).mapsTo'
    (hqc 0).left_inv (hqc 0).right_inv (hgen 0)
  have hC1rev₀ := equivariant_on_closure
    (Γ := Subgroup.closure (Set.range ρ)) (gens := ρ)
    (fun i => Subgroup.subset_closure ⟨i, rfl⟩) (ρ := gens (ψ 0))
    (hqc 0).mapsTo' (hqc 0).mapsTo (hqc 0).right_inv (hqc 0).left_inv hgenInv₀
  rw [hclos (ψ 0)] at hC1rev₀
  -- the two-sided `Γ₀`-to-limit conjugation of `v₀`
  have hv₀fwd : ∀ γ ∈ Γ₀, ∃ W ∈ Subgroup.closure (Set.range ρ),
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z) := by
    intro γ hγ
    obtain ⟨W', hW'mem, hW'id⟩ := w_conj_of_mem_base (x (φ₀ (ψ 0))) hγ
    obtain ⟨W, hWmem, hIid, -⟩ := hC1rev₀ W' hW'mem
    refine ⟨W, hWmem, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hwz : 0 < ((x (φ₀ (ψ 0))).w z).im := (x (φ₀ (ψ 0))).w_mapsTo_upper z hz
    have e1 : v₀ (moebiusMap γ z) = hinv 0 ((x (φ₀ (ψ 0))).w (moebiusMap γ z)) :=
      hv₀eq _ hγz
    have e2 : v₀ z = hinv 0 ((x (φ₀ (ψ 0))).w z) := hv₀eq z hz
    rw [e1, hW'id z hz, hIid _ hwz, ← e2]
  have hv₀rev : ∀ W ∈ Subgroup.closure (Set.range ρ), ∃ γ ∈ Γ₀,
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z) := by
    intro W hWmem
    obtain ⟨W', hW'mem, -, hIid⟩ := hC1fwd₀ W hWmem
    obtain ⟨γ, hγ, hγid⟩ := w_conj_of_mem_group (x (φ₀ (ψ 0))) hW'mem
    refine ⟨γ, hγ, fun z hz => ?_⟩
    have hγz : 0 < (moebiusMap γ z).im := moebiusMap_im_pos γ hz
    have hwz : 0 < ((x (φ₀ (ψ 0))).w z).im := (x (φ₀ (ψ 0))).w_mapsTo_upper z hz
    have e1 : v₀ (moebiusMap γ z) = hinv 0 ((x (φ₀ (ψ 0))).w (moebiusMap γ z)) :=
      hv₀eq _ hγz
    have e2 : v₀ z = hinv 0 ((x (φ₀ (ψ 0))).w z) := hv₀eq z hz
    rw [e1, hγid z hz, hIid _ hwz, ← e2]
  -- realization of the limit representative
  have hv₀conj : ∀ γ ∈ Γ₀, ∃ W : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → v₀ (moebiusMap γ z) = moebiusMap W (v₀ z) := by
    intro γ hγ
    obtain ⟨W, -, hid⟩ := hv₀fwd γ hγ
    exact ⟨W, hid⟩
  obtain ⟨y, hycoeff⟩ := exists_teichRep_ofUpper_of_conjugating hκᵥ1 hv₀qc hv₀conj
  obtain ⟨R₀, hyfac⟩ := exists_sl2_factorization_of_eq_coeff y hκᵥ1 hv₀qc hycoeff
  -- the per-index marked candidates
  have hcand : ∀ j : ℕ, ∃ (F : ModGroupUpper Γ₀) (C : ℂ → ℂ),
      IsQCGeometric C ((1 + 1 / ((j : ℝ) + 2)) / (1 - 1 / ((j : ℝ) + 2))) ∧
      IsMarkedCandidate ((x (φ₀ (ψ j))).smulUpper F) y C := fun j =>
    marked_candidate_of_upper_conjugacy (x (φ₀ (ψ j))) (hmem (ψ j)) (hclos (ψ j))
      (le_of_lt (hκpos j)) (hκ1 j) (hqc j) (hgen j) hκᵥ1 hv₀qc hv₀fwd hv₀rev y R₀ hyfac
  choose F C hgeo hmk using hcand
  -- the dilatation squeeze
  have hKlim : Filter.Tendsto
      (fun j : ℕ => (1 + 1 / ((j : ℝ) + 2)) / (1 - 1 / ((j : ℝ) + 2)))
      Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun j : ℕ => ((j : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) Filter.atTop (nhds 0) := by
      simp only [one_div]
      exact h2.inv_tendsto_atTop
    have h4 : Filter.Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 2)) Filter.atTop
        (nhds (1 + 0)) := tendsto_const_nhds.add h3
    have h5 : Filter.Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) Filter.atTop
        (nhds (1 - 0)) := tendsto_const_nhds.sub h3
    have h6 := h4.div h5 (by norm_num)
    have h7 : (1 + 0 : ℝ) / (1 - 0) = 1 := by norm_num
    rwa [h7] at h6
  have htend := tendsto_teichDistG_zero_of_candidates
    (x := fun j => (x (φ₀ (ψ j))).smulUpper (F j)) (y := y) (F := C)
    (K := fun j => (1 + 1 / ((j : ℝ) + 2)) / (1 - 1 / ((j : ℝ) + 2))) hgeo hmk hKlim
  -- packaging along the composed extraction
  refine ⟨φ₀ ∘ ψ, F, y, hφ₀mono.comp hψmono, ?_⟩
  have hpt : ∀ k : ℕ, teichDistG ((x (φ₀ (ψ k))).smulUpper (F k)) y
      = Teich.distG (F k • Teich.mk (x ((φ₀ ∘ ψ) k))) (Teich.mk y) := by
    intro k
    have h1 : F k • Teich.mk (x ((φ₀ ∘ ψ) k))
        = Teich.mk ((x (φ₀ (ψ k))).smulUpper (F k)) :=
      Teich.smulUpper_mk (F k) (x (φ₀ (ψ k)))
    rw [h1]
    exact (Teich.distG_mk _ _).symm
  exact htend.congr hpt

end RiemannDynamics
