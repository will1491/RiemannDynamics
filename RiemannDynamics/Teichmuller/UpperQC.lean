import RiemannDynamics.Teichmuller.Interpolate

/-!
# Upper-half-plane quasiconformal conjugacies and Marden stability

Quasiconformal self-maps of the open upper half plane and the generator form of Marden
stability at the level of the upper half plane: the conjugating map is a self-map of `ℍ`,
exact on the generator tuples, with Beltrami bound tending to `0`. A conjugacy of an
exactly matched marked pair of cocompact Fuchsian groups has a rigid boundary map, so it
does not in general extend to a plane homeomorphism; the upper-half-plane formulation
carries the full content of the stability statement.

* `IsQCUpper` — quasiconformal self-maps of the upper half plane with a Beltrami bound.
* `isQCUpper_of_isQCGeometric` — symmetric plane quasiconformal homeomorphisms preserving
  the upper half plane restrict to upper-half-plane quasiconformal maps.
* `exists_equivariant_upper_conjugacy_K_to_one` — **Marden stability**: along generator
  tuples converging to the tuple of a cocompact trace-gapped limit group, for every
  `κ > 0`, eventually there is an upper-half-plane quasiconformal conjugacy with Beltrami
  bound `κ` intertwining the tuples exactly.
* `exists_sl2_factorization_of_eq_coeff` — factorization: two solutions of the same
  Beltrami equation on the upper half plane differ by a real Möbius map.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-- `h` is an **upper-half-plane quasiconformal map** with coefficient bound `κ`: a
homeomorphism of the open upper half plane onto itself, recorded with a two-sided inverse
`hinv`, lying in `W^{1,2}_loc` of the open upper half plane, with almost-everywhere
positive Jacobian and Beltrami bound `‖∂̄h‖ ≤ κ ‖∂h‖` almost everywhere on the upper half
plane. -/
structure IsQCUpper (h hinv : ℂ → ℂ) (κ : ℝ) : Prop where
  mapsTo : ∀ z : ℂ, 0 < z.im → 0 < (h z).im
  mapsTo' : ∀ z : ℂ, 0 < z.im → 0 < (hinv z).im
  left_inv : ∀ z : ℂ, 0 < z.im → hinv (h z) = z
  right_inv : ∀ z : ℂ, 0 < z.im → h (hinv z) = z
  cont : ContinuousOn h {z : ℂ | 0 < z.im}
  cont' : ContinuousOn hinv {z : ℂ | 0 < z.im}
  sobolev : MemWklocP h 1 2 {z : ℂ | 0 < z.im}
  jac : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), 0 < (fderiv ℝ h z).det
  belt : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖dzbar h z‖ ≤ κ * ‖dz h z‖

/-- A conjugation-symmetric quasiconformal plane homeomorphism mapping the upper half
plane into itself restricts to an upper-half-plane quasiconformal map with the
corresponding coefficient bound: symmetry carries the half-plane preservation to the
inverse. -/
theorem isQCUpper_of_isQCGeometric {F G : ℂ → ℂ} {K : ℝ} (hF : IsQCGeometric F K)
    (hsym : ∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z))
    (hup : ∀ z : ℂ, 0 < z.im → 0 < (F z).im)
    (hGF : ∀ z : ℂ, G (F z) = z) (hFG : ∀ z : ℂ, F (G z) = z) :
    IsQCUpper F G ((K - 1) / (K + 1)) := by
  have hhomeo : IsHomeomorph F := hF.2.1.isHomeomorph
  obtain ⟨b, hbnd, hQCA⟩ := isQCAnalytic_of_isQCGeometric hF.1 hF
  -- `G` is globally continuous: it is the inverse of the open bijection `F`, so
  -- `G ⁻¹' U = F '' U` is open for every open `U`.
  have hGcont : Continuous G := by
    rw [continuous_def]
    intro U hU
    have hpre : G ⁻¹' U = F '' U := by
      ext z
      constructor
      · intro hz
        exact ⟨G z, hz, hFG z⟩
      · rintro ⟨w, hw, rfl⟩
        simpa [hGF w] using hw
    rw [hpre]
    exact hhomeo.isOpenMap U hU
  -- `G` preserves the upper half plane: conjugation symmetry of `F` forbids `G z`
  -- from lying on the real axis or in the lower half plane.
  have hmapsTo' : ∀ z : ℂ, 0 < z.im → 0 < (G z).im := by
    intro z hz
    by_contra hle
    rw [not_lt] at hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- `(G z).im = 0`: then `G z` is fixed by conjugation, hence so is `z = F (G z)`.
      have hconj : starRingEnd ℂ (G z) = G z := Complex.conj_eq_iff_im.mpr heq
      have hzfix : starRingEnd ℂ z = z := by
        calc starRingEnd ℂ z = starRingEnd ℂ (F (G z)) := by rw [hFG z]
          _ = F (starRingEnd ℂ (G z)) := (hsym (G z)).symm
          _ = F (G z) := by rw [hconj]
          _ = z := hFG z
      exact absurd (Complex.conj_eq_iff_im.mp hzfix) (ne_of_gt hz)
    · -- `(G z).im < 0`: then `conj (G z)` lies in the upper half plane, but `F` sends it
      -- to `conj z`, whose imaginary part is negative.
      have him : 0 < (starRingEnd ℂ (G z)).im := by
        rw [Complex.conj_im]; linarith
      have h1 := hup _ him
      rw [hsym (G z), hFG z, Complex.conj_im] at h1
      linarith
  refine ⟨hup, hmapsTo', fun z _ => hGF z, fun z _ => hFG z,
    hhomeo.continuous.continuousOn, hGcont.continuousOn,
    MemWklocP.mono hQCA.2.1 (Set.subset_univ _),
    ae_restrict_of_ae hQCA.1.2, ?_⟩
  -- The Beltrami bound: `‖μ‖ ≤ ‖μ‖∞ ≤ (K − 1)/(K + 1)` almost everywhere, and the
  -- Beltrami equation converts this into the dilatation inequality.
  have hbw_ae : ∀ᵐ w : ℂ, ‖b.μ w‖ ≤ b.normInf := by
    filter_upwards [enorm_ae_le_eLpNormEssSup b.μ volume] with w hw
    have h2 := ENNReal.toReal_mono (ne_top_of_lt b.bound) hw
    simpa [BeltramiCoeff.normInf, enorm_eq_nnnorm] using h2
  refine ae_restrict_of_ae ?_
  filter_upwards [hQCA.2.2, hbw_ae] with z hbel hbw
  calc ‖dzbar F z‖ = ‖b.μ z‖ * ‖dz F z‖ := by rw [hbel, norm_mul]
    _ ≤ b.normInf * ‖dz F z‖ := mul_le_mul_of_nonneg_right hbw (norm_nonneg _)
    _ ≤ (K - 1) / (K + 1) * ‖dz F z‖ := mul_le_mul_of_nonneg_right hbnd (norm_nonneg _)

/-! ## Marden stability, upper-half-plane generator form -/

/-- **Marden stability, upper-half-plane generator form.** Along generator tuples of
trace-gapped Fuchsian groups converging entrywise to the tuple of a cocompact trace-gapped
limit group, for every `κ > 0`, eventually in `n` there is an upper-half-plane
quasiconformal conjugacy with Beltrami bound `κ` intertwining the limit tuple with the
`n`-th tuple exactly on the upper half plane. -/
theorem exists_equivariant_upper_conjugacy_K_to_one
    {ι : Type} [Finite ι] {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hΓ : ∀ n, IsFuchsianGroup (Γ n))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    (gens : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) (hmem : ∀ n i, gens n i ∈ Γ n)
    (ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hlim : ∀ i, Filter.Tendsto (fun n => gens n i) Filter.atTop (nhds (ρ i)))
    (hgapρ : ∀ h ∈ Subgroup.closure (Set.range ρ), actsNontrivially h →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (h : Matrix (Fin 2) (Fin 2) ℝ)|)
    (hccρ : CompactSpace (Quotient (MulAction.orbitRel (Subgroup.closure (Set.range ρ))
      UpperHalfPlane))) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ n in Filter.atTop, ∃ h hinv : ℂ → ℂ,
      IsQCUpper h hinv κ ∧
      ∀ i, ∀ z : ℂ, 0 < z.im → h (moebiusMap (ρ i) z) = moebiusMap (gens n i) (h z) := by
  sorry

/-! ## The factorization lemma -/

/-- **Factorization.** If the normalized solution of a Teichmüller representative and an
upper-half-plane quasiconformal map solve the same Beltrami equation almost everywhere on
the upper half plane, they differ by a real Möbius map: their quotient is conformal by the
Weyl lemma and is a holomorphic self-homeomorphism of the upper half plane, hence Möbius. -/
theorem exists_sl2_factorization_of_eq_coeff
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (u : TeichRep Γ₀)
    {v vinv : ℂ → ℂ} {κ : ℝ} (hκ : κ < 1) (hv : IsQCUpper v vinv κ)
    (hcoeff : ∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}),
      dzbar v z = u.b.μ z * dz v z) :
    ∃ R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℂ, 0 < z.im → u.w z = moebiusMap R (v z) := by
  sorry

end RiemannDynamics
