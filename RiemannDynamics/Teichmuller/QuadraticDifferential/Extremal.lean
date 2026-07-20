import RiemannDynamics.Teichmuller.QuadraticDifferential.MarkedCandidate
import RiemannDynamics.Teichmuller.QuadraticDifferential.FlatMetric
import RiemannDynamics.QC.GeometricToAnalytic.Assembly
import RiemannDynamics.QC.Calculus.Compactness

/-!
# Attainment of the extremal dilatation

The infimum of the dilatation set of a pair of Teichmüller representatives is attained: a
minimizing sequence of normalized quasiconformal candidates has a locally uniformly
convergent subsequence, the boundary transition passes to the limit pointwise, the limit is
`K'`-quasiconformal for every `K'` above the infimum by tail re-extraction, and geometric
quasiconformality is closed from above in the dilatation constant. For the equivariant
class the group compatibility clauses pass to the limit through proper discontinuity: for
each deck element the conjugating witnesses meet a fixed compact set, hence range in a
finite set, and a constant-witness subsequence gives the limit identity.

* `isQCGeometric_of_forall_gt` — `IsQCGeometric` is closed from above in `K`.
* `dilatationSet_sInf_mem` — the boundary-value extremal problem is attained.
* `isMarkedCandidate_of_tendstoLocallyUniformly` — candidacy passes to limits.
* `exists_extremal_marked` — the equivariant extremal problem is attained.
* `grotzsch_square`, `grotzsch_square_unique` — the affine horizontal stretch is the
  unique extremal map of the square with its boundary values.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RiemannDynamics

variable {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## Closedness of quasiconformality in the dilatation and in the limit -/

/-- Locally uniform convergence gives pointwise convergence. -/
theorem tendsto_apply_of_tendstoLocallyUniformly {Fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly Fn f atTop) (z : ℂ) :
    Tendsto (fun n => Fn n z) atTop (𝓝 (f z)) :=
  (tendstoLocallyUniformlyOn_univ.mpr h).tendsto_at (Set.mem_univ z)

/-- Pointwise boundary conditions pass to locally uniform limits. -/
theorem boundary_eq_of_tendstoLocallyUniformly {Hn : ℕ → ℂ → ℂ} {H : ℂ → ℂ}
    (hlu : TendstoLocallyUniformly Hn H atTop)
    {w v : ℝ → ℂ} (hb : ∀ n t, Hn n (w t) = v t) (t : ℝ) : H (w t) = v t := by
  have h1 : Tendsto (fun n => Hn n (w t)) atTop (𝓝 (H (w t))) :=
    tendsto_apply_of_tendstoLocallyUniformly hlu (w t)
  have h2 : (fun n => Hn n (w t)) = fun _ => v t := funext fun n => hb n t
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- `IsQCGeometric f` is closed from above in the dilatation: a map that is
`K'`-quasiconformal for every `K' > K ≥ 1` is `K`-quasiconformal. -/
theorem isQCGeometric_of_forall_gt {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K)
    (h : ∀ K' : ℝ, K < K' → IsQCGeometric f K') : IsQCGeometric f K := by
  have hsp : SensePreserving f := (h (K + 1) (by linarith)).2.1
  refine ⟨hK, hsp, fun Q => ?_⟩
  set m := Q.modulus with hm
  by_cases hm0 : m = 0
  · have h1 := (h (K + 1) (by linarith)).2.2 Q
    rw [← hm, hm0, mul_zero] at h1
    rw [hm0, mul_zero]
    exact h1
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
    have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
    have hKne : ENNReal.ofReal K ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hKpos
    have hmtop : m ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top hKne] at hlt
      exact absurd hlt (lt_irrefl _)
    have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
    set δ : ℝ := (ε : ℝ) / m.toReal with hδ
    have hδpos : 0 < δ := div_pos (NNReal.coe_pos.mpr hε) hmr
    have h1 := (h (K + δ) (by linarith)).2.2 Q
    rw [← hm] at h1
    have hsplit : ENNReal.ofReal (K + δ) = ENNReal.ofReal K + ENNReal.ofReal δ :=
      ENNReal.ofReal_add (by linarith) hδpos.le
    have h2 : ENNReal.ofReal δ * m = (ε : ℝ≥0∞) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hmtop]
      rw [← ENNReal.ofReal_mul hδpos.le, hδ, div_mul_cancel₀ _ (ne_of_gt hmr),
        ENNReal.ofReal_coe_nnreal]
    calc curveModulus (Q.imageCurveFamily f) ≤ ENNReal.ofReal (K + δ) * m := h1
      _ = ENNReal.ofReal K * m + ENNReal.ofReal δ * m := by rw [hsplit, add_mul]
      _ = ENNReal.ofReal K * m + ε := by rw [h2]

/-- An eventual dilatation bound passes to locally uniform limits of `(0, 1)`-normalized
quasiconformal maps: re-extract from the tail and use uniqueness of locally uniform
limits. -/
theorem isQCGeometric_limit_of_eventually {Fk : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {K' : ℝ}
    (hlu : TendstoLocallyUniformly Fk G atTop)
    (hfp : ∀ k, Fk k 0 = 0) (hfq : ∀ k, Fk k 1 = 1)
    (hev : ∀ᶠ k in atTop, IsQCGeometric (Fk k) K') : IsQCGeometric G K' := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hTK : ∀ k, IsQCGeometric (Fk (k + N)) K' := fun k => hN (k + N) (Nat.le_add_left N k)
  obtain ⟨ψ, H, hψ, hHK, hluT⟩ :=
    exists_subseq_tendstoLocallyUniformly_isQCGeometric hTK
      (zero_ne_one : (0 : ℂ) ≠ 1) (zero_ne_one : (0 : ℂ) ≠ 1)
      (fun k => hfp (k + N)) (fun k => hfq (k + N))
  have hHG : H = G := by
    funext z
    have h1 : Tendsto (fun k => Fk k z) atTop (𝓝 (G z)) :=
      tendsto_apply_of_tendstoLocallyUniformly hlu z
    have h2 : Tendsto (fun j => ψ j + N) atTop atTop :=
      tendsto_atTop_mono (fun j => Nat.le_add_right (ψ j) N) hψ.tendsto_atTop
    have h3 : Tendsto (fun j => Fk (ψ j + N) z) atTop (𝓝 (G z)) := h1.comp h2
    exact tendsto_nhds_unique (tendsto_apply_of_tendstoLocallyUniformly hluT z) h3
  rw [hHG] at hHK
  exact hHK

/-! ## Attainment of the boundary-value extremal problem -/

/-- **The boundary-value dilatation infimum is attained**: a minimizing sequence of
candidates, normalized by `0 ↦ 0` and `1 ↦ 1`, subconverges locally uniformly; the limit
is a candidate of dilatation `sInf (dilatationSet x y)`. -/
theorem dilatationSet_sInf_mem (x y : TeichRep Γ₀) :
    sInf (dilatationSet x y) ∈ dilatationSet x y := by
  classical
  obtain ⟨u, hua, hut, humem⟩ :=
    exists_seq_tendsto_sInf (dilatationSet_nonempty x y) (bddBelow_dilatationSet x y)
  simp only [dilatationSet, Set.mem_setOf_eq] at humem
  choose F hFK hFb using humem
  have hfp : ∀ n, F n 0 = 0 := by
    intro n
    have h := hFb n 0
    simp only [Complex.ofReal_zero, TeichRep.w_zero] at h
    exact h
  have hfq : ∀ n, F n 1 = 1 := by
    intro n
    have h := hFb n 1
    simp only [Complex.ofReal_one, TeichRep.w_one] at h
    exact h
  have hK0 : ∀ n, IsQCGeometric (F n) (u 0) := fun n =>
    (hFK n).mono (hua (Nat.zero_le n))
  obtain ⟨φ, G, hφ, _, hlu⟩ :=
    exists_subseq_tendstoLocallyUniformly_isQCGeometric hK0
      (zero_ne_one : (0 : ℂ) ≠ 1) (zero_ne_one : (0 : ℂ) ≠ 1) hfp hfq
  have hGb : ∀ t : ℝ, G (y.w t) = x.w t := fun t =>
    boundary_eq_of_tendstoLocallyUniformly hlu (fun k s => hFb (φ k) s) t
  have hsharp : ∀ K' : ℝ, sInf (dilatationSet x y) < K' → IsQCGeometric G K' := by
    intro K' hK'
    refine isQCGeometric_limit_of_eventually hlu (fun k => hfp (φ k))
      (fun k => hfq (φ k)) ?_
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hut.eventually_lt_const hK')
    exact eventually_atTop.mpr ⟨N, fun k hk => (hFK (φ k)).mono
      (hN (φ k) (le_trans hk hφ.le_apply)).le⟩
  exact ⟨G, isQCGeometric_of_forall_gt (one_le_sInf_dilatationSet x y) hsharp, hGb⟩

/-! ## Attainment of the equivariant extremal problem -/

/-- The pole of a plane Möbius map is unique. -/
theorem moebiusDenom_zero_unique (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z₁ z₂ : ℂ}
    (h₁ : moebiusDenom γ z₁ = 0) (h₂ : moebiusDenom γ z₂ = 0) : z₁ = z₂ := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  by_cases hc : γ 1 0 = 0
  · exfalso
    have hd : γ 1 1 ≠ 0 := by
      intro h0
      rw [hc, h0] at hdet
      simp at hdet
    have h1' : (γ 1 0 : ℂ) * z₁ + (γ 1 1 : ℂ) = 0 := h₁
    rw [hc] at h1'
    push_cast at h1'
    simp only [zero_mul, zero_add] at h1'
    exact hd (by exact_mod_cast h1')
  · have hcC : (γ 1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have h1' : (γ 1 0 : ℂ) * z₁ + (γ 1 1 : ℂ) = 0 := h₁
    have h2' : (γ 1 0 : ℂ) * z₂ + (γ 1 1 : ℂ) = 0 := h₂
    have : (γ 1 0 : ℂ) * z₁ = (γ 1 0 : ℂ) * z₂ := by linear_combination h1' - h2'
    exact mul_left_cancel₀ hcC this

/-- An a.e. Möbius conjugation identity for a continuous plane map with nonreal values on
the upper half plane upgrades to a pointwise identity there. -/
theorem moebius_conj_upgrade {f : ℂ → ℂ} (hfc : Continuous f)
    (him0 : ∀ z : ℂ, 0 < z.im → (f z).im ≠ 0)
    (γ W : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hae : ∀ᵐ z : ℂ, f (moebiusMap γ z) = moebiusMap W (f z)) :
    ∀ z : ℂ, 0 < z.im → f (moebiusMap γ z) = moebiusMap W (f z) := by
  intro z hz
  have hUopen : IsOpen {w : ℂ | 0 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have h1 : ContinuousOn (fun w => f (moebiusMap γ w)) {w : ℂ | 0 < w.im} := by
    intro w hw
    have hd := moebiusDenom_ne_zero_of_im_ne_zero γ (ne_of_gt hw)
    exact (hfc.continuousAt.comp
      (hasDerivAt_moebiusMap γ hd).continuousAt).continuousWithinAt
  have h2 : ContinuousOn (fun w => moebiusMap W (f w)) {w : ℂ | 0 < w.im} := by
    intro w hw
    have hd := moebiusDenom_ne_zero_of_im_ne_zero W (him0 w hw)
    exact ((hasDerivAt_moebiusMap W hd).continuousAt.comp
      hfc.continuousAt).continuousWithinAt
  have heq : Set.EqOn (fun w => f (moebiusMap γ w)) (fun w => moebiusMap W (f w))
      {w : ℂ | 0 < w.im} := by
    refine Measure.eqOn_of_ae_eq (ae_restrict_of_ae hae) h1 h2 ?_
    rw [hUopen.interior_eq]
    exact subset_closure
  exact heq hz

/-- The upper-half-plane preimage under the normalized solution of an upper point is upper. -/
theorem w_symm_preimage_upper (y : TeichRep Γ₀) {u z : ℂ} (hz : 0 < z.im)
    (hu : y.w u = z) : 0 < u.im := by
  rcases lt_trichotomy u.im 0 with hneg | hzero | hpos
  · exfalso
    have h1 : 0 < (starRingEnd ℂ u).im := by
      rw [Complex.conj_im]
      linarith
    have h2 : 0 < (y.w (starRingEnd ℂ u)).im := y.w_mapsTo_upper _ h1
    rw [y.w_conj u, Complex.conj_im, hu] at h2
    linarith
  · exfalso
    have hur : ((u.re : ℝ) : ℂ) = u := Complex.ext (by simp) (by simp [hzero])
    have h0 : (y.w u).im = 0 := by
      rw [← hur]
      exact y.w_real u.re
    rw [hu] at h0
    linarith
  · exact hpos

/-- An injective map matching the boundary transition takes nonreal values on the upper
half plane: a real value is a boundary value, and injectivity pins its preimage to `ℝ`. -/
theorem im_ne_zero {x y : TeichRep Γ₀} {G : ℂ → ℂ} (hGi : Function.Injective G)
    (hGb : ∀ t : ℝ, G (y.w t) = x.w t) : ∀ z : ℂ, 0 < z.im → (G z).im ≠ 0 := by
  intro z hz h0
  obtain ⟨t, ht⟩ := x.boundary_surjective (G z).re
  have hxw : x.w (t : ℂ) = G z := by
    rw [x.w_ofReal t, ht]
    exact Complex.ext (by simp) (by simp [h0])
  have hGyw : G (y.w t) = G z := by rw [hGb t, hxw]
  have hyz : y.w (t : ℂ) = z := hGi hGyw
  have him : z.im = 0 := by
    rw [← hyz]
    exact y.w_real t
  linarith

/-- **Constant-witness pigeonhole.** Deck matrices of a Fuchsian group carrying one
convergent upper sequence to another meet a fixed pair of compact sets, hence range in a
finite set, so some witness recurs infinitely often. -/
theorem exists_frequently_const_witness
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsianGroup Γ)
    {V : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hVmem : ∀ n, V n ∈ Γ)
    {pn qn : ℕ → ℂ} {p q : ℂ}
    (hp : Tendsto pn atTop (𝓝 p)) (hq : Tendsto qn atTop (𝓝 q))
    (hpn : ∀ n, 0 < (pn n).im) (hqn : ∀ n, 0 < (qn n).im)
    (hpim : 0 < p.im) (hqim : 0 < q.im)
    (hiden : ∀ n, moebiusMap (V n) (pn n) = qn n) :
    ∃ V₀, V₀ ∈ Γ ∧ ∃ᶠ n in atTop, V n = V₀ := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  set P : ℕ → UpperHalfPlane := fun n => ⟨pn n, hpn n⟩ with hP
  set Q : ℕ → UpperHalfPlane := fun n => ⟨qn n, hqn n⟩ with hQ
  set Pl : UpperHalfPlane := ⟨p, hpim⟩ with hPl
  set Ql : UpperHalfPlane := ⟨q, hqim⟩ with hQl
  have hind := UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing
  have hPtend : Tendsto P atTop (𝓝 Pl) := hind.tendsto_nhds_iff.mpr hp
  have hQtend : Tendsto Q atTop (𝓝 Ql) := hind.tendsto_nhds_iff.mpr hq
  have hK : IsCompact (insert Pl (Set.range P)) := hPtend.isCompact_insert_range
  have hL : IsCompact (insert Ql (Set.range Q)) := hQtend.isCompact_insert_range
  set S : Set ↥Γ := {g : ↥Γ |
    ((fun τ => g • τ) '' insert Pl (Set.range P) ∩ insert Ql (Set.range Q)).Nonempty}
    with hS
  have hfin : S.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image hK hL
  have hgsmul : ∀ n, (⟨V n, hVmem n⟩ : ↥Γ) • P n = Q n := by
    intro n
    apply UpperHalfPlane.ext
    have hcoe : ((⟨V n, hVmem n⟩ : ↥Γ) • P n : UpperHalfPlane) = V n • P n := rfl
    rw [hcoe, coe_smul_eq_moebiusMap]
    exact hiden n
  have hgmem : ∀ n, (⟨V n, hVmem n⟩ : ↥Γ) ∈ S := by
    intro n
    refine ⟨(⟨V n, hVmem n⟩ : ↥Γ) • P n,
      Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ ⟨n, rfl⟩), ?_⟩
    rw [hgsmul n]
    exact Set.mem_insert_of_mem _ ⟨n, rfl⟩
  by_contra hno
  push Not at hno
  have hnotfreq : ∀ g : ↥Γ, ∀ᶠ n in atTop, V n ≠ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    fun g => hno (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) g.2
  have hallS : ∀ᶠ n in atTop, ∀ g ∈ S,
      V n ≠ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
    hfin.eventually_all.mpr fun g _ => hnotfreq g
  obtain ⟨n₀, hn₀⟩ := hallS.exists
  exact hn₀ ⟨V n₀, hVmem n₀⟩ (hgmem n₀) rfl

/-- Two functions agreeing on the open upper half plane and continuous at a real point
agree there: approach the point vertically. -/
theorem eq_at_real_of_eq_on_upper {F H : ℂ → ℂ} {t : ℂ} (ht : t.im = 0)
    (hF : ContinuousAt F t) (hH : ContinuousAt H t)
    (h : ∀ z : ℂ, 0 < z.im → F z = H z) : F t = H t := by
  set zk : ℕ → ℂ := fun k => t + ((1 / (k + 1) : ℝ) : ℂ) * Complex.I with hzk
  have hzkim : ∀ k, 0 < (zk k).im := by
    intro k
    have h1 : (zk k).im = t.im + ((1 / ((k : ℝ) + 1)) * 1 + 0 * 0) := by
      rw [hzk]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have h2 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    rw [h1, ht]
    linarith
  have hcont : Continuous fun r : ℝ => t + (r : ℂ) * Complex.I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hzktend : Tendsto zk atTop (𝓝 t) := by
    have h0 := (hcont.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto zk atTop (𝓝 (t + ((0 : ℝ) : ℂ) * Complex.I)) := h0
    simpa using h1
  have hFt : Tendsto (fun k => F (zk k)) atTop (𝓝 (F t)) := hF.tendsto.comp hzktend
  have hHt : Tendsto (fun k => H (zk k)) atTop (𝓝 (H t)) := hH.tendsto.comp hzktend
  have hEq : (fun k => F (zk k)) = fun k => H (zk k) :=
    funext fun k => h (zk k) (hzkim k)
  rw [hEq] at hFt
  exact tendsto_nhds_unique hFt hHt

/-- Three distinct real points avoiding four subsingleton exceptional predicates. -/
theorem exists_three_good_reals {P₁ P₂ P₃ P₄ : ℝ → Prop}
    (h₁ : ∀ s t, P₁ s → P₁ t → s = t) (h₂ : ∀ s t, P₂ s → P₂ t → s = t)
    (h₃ : ∀ s t, P₃ s → P₃ t → s = t) (h₄ : ∀ s t, P₄ s → P₄ t → s = t) :
    ∃ t₁ t₂ t₃ : ℝ, t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ ∧
      (∀ t ∈ ({t₁, t₂, t₃} : Set ℝ), ¬P₁ t ∧ ¬P₂ t ∧ ¬P₃ t ∧ ¬P₄ t) := by
  classical
  have hex : ∀ (P : ℝ → Prop), (∀ s t, P s → P t → s = t) → ∃ b : ℝ, ∀ t, P t → t = b := by
    intro P hP
    by_cases h : ∃ t, P t
    · obtain ⟨t₀, ht₀⟩ := h
      exact ⟨t₀, fun t ht => hP t t₀ ht ht₀⟩
    · exact ⟨0, fun t ht => absurd ⟨t, ht⟩ h⟩
  obtain ⟨b₁, hb₁⟩ := hex P₁ h₁
  obtain ⟨b₂, hb₂⟩ := hex P₂ h₂
  obtain ⟨b₃, hb₃⟩ := hex P₃ h₃
  obtain ⟨b₄, hb₄⟩ := hex P₄ h₄
  have hBfin : ({b₁, b₂, b₃, b₄} : Set ℝ).Finite := Set.toFinite _
  have hinf : ({b₁, b₂, b₃, b₄} : Set ℝ)ᶜ.Infinite := hBfin.infinite_compl
  obtain ⟨t₁, ht₁⟩ := hinf.nonempty
  obtain ⟨t₂, ht₂⟩ := (hinf.diff (Set.finite_singleton t₁)).nonempty
  obtain ⟨t₃, ht₃⟩ := (hinf.diff (Set.toFinite {t₁, t₂})).nonempty
  have hgood : ∀ t : ℝ, t ∈ ({b₁, b₂, b₃, b₄} : Set ℝ)ᶜ →
      ¬P₁ t ∧ ¬P₂ t ∧ ¬P₃ t ∧ ¬P₄ t := by
    intro t htc
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htc
    exact ⟨fun h => htc.1 (hb₁ t h), fun h => htc.2.1 (hb₂ t h),
      fun h => htc.2.2.1 (hb₃ t h), fun h => htc.2.2.2 (hb₄ t h)⟩
  refine ⟨t₁, t₂, t₃, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (Set.mem_diff _ |>.mp ht₂).2 (by simp [h.symm])
  · intro h
    exact (Set.mem_diff _ |>.mp ht₃).2 (by simp [h.symm])
  · intro h
    exact (Set.mem_diff _ |>.mp ht₃).2 (by simp [h.symm])
  · intro t ht
    rcases ht with rfl | rfl | rfl
    · exact hgood _ ht₁
    · exact hgood _ (Set.mem_diff _ |>.mp ht₂).1
    · exact hgood _ (Set.mem_diff _ |>.mp ht₃).1

/-- **Candidacy passes to locally uniform quasiconformal limits.** The boundary clause is
pointwise-closed; for each deck element the conjugating witnesses of the approximants carry
convergent orbits inside a compact subset of the upper half plane, so by proper
discontinuity they range in a finite set, and a constant-witness subsequence yields the
limit identity. Both compatibility clauses pass. -/
theorem isMarkedCandidate_of_tendstoLocallyUniformly (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    {x y : TeichRep Γ₀} {Fn : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {K : ℝ}
    (hG : IsQCGeometric G K)
    (hlu : TendstoLocallyUniformly Fn G atTop)
    (hcand : ∀ n, IsMarkedCandidate x y (Fn n)) : IsMarkedCandidate x y G := by
  classical
  have hGb : ∀ t : ℝ, G (y.w t) = x.w t :=
    fun t => boundary_eq_of_tendstoLocallyUniformly hlu (fun n s => (hcand n).1 s) t
  have hGi : Function.Injective G := hG.2.1.isHomeomorph.injective
  have hGc : Continuous G := hG.2.1.isHomeomorph.continuous
  have him : ∀ z : ℂ, 0 < z.im → (G z).im ≠ 0 := im_ne_zero hGi hGb
  have hxF : IsFuchsianGroup x.group := TeichRep.isFuchsian_group hΓ₀ hfree x
  have hkey : ∀ W ∈ y.group, ∃ W' ∈ x.group,
      ∀ z : ℂ, 0 < z.im → G (moebiusMap W z) = moebiusMap W' (G z) := by
    intro W hW
    have hex : ∀ n, ∃ W', W' ∈ x.group ∧ ∀ z : ℂ, 0 < z.im →
        Fn n (moebiusMap W z) = moebiusMap W' (Fn n z) := fun n => (hcand n).2.1 W hW
    choose V hVmem hViden using hex
    have hIim : (0 : ℝ) < Complex.I.im := by simp
    set z₁ : ℂ := moebiusMap W Complex.I with hz₁def
    have hz₁im : 0 < z₁.im := moebiusMap_im_pos W hIim
    have hp : Tendsto (fun n => Fn n Complex.I) atTop (𝓝 (G Complex.I)) :=
      tendsto_apply_of_tendstoLocallyUniformly hlu Complex.I
    have hq : Tendsto (fun n => Fn n z₁) atTop (𝓝 (G z₁)) :=
      tendsto_apply_of_tendstoLocallyUniformly hlu z₁
    have hiden : ∀ n, moebiusMap (V n) (Fn n Complex.I) = Fn n z₁ :=
      fun n => (hViden n Complex.I hIim).symm
    have hpim : (G Complex.I).im ≠ 0 := him _ hIim
    have hqim : (G z₁).im ≠ 0 := him _ hz₁im
    have hpseq : Tendsto (fun n => (Fn n Complex.I).im) atTop (𝓝 ((G Complex.I).im)) :=
      (Complex.continuous_im.tendsto _).comp hp
    have hqseq : Tendsto (fun n => (Fn n z₁).im) atTop (𝓝 ((G z₁).im)) :=
      (Complex.continuous_im.tendsto _).comp hq
    have hfreq : ∃ V₀, V₀ ∈ x.group ∧ ∃ᶠ n in atTop, V n = V₀ := by
      rcases lt_or_gt_of_ne hpim with hneg | hpos
      · -- the limit sends the upper half plane into the lower one: conjugate
        have hqneg : (G z₁).im < 0 := by
          rcases lt_or_gt_of_ne hqim with h | h
          · exact h
          · exfalso
            obtain ⟨n, hn1, hn2⟩ := ((hpseq.eventually_lt_const hneg).and
              (hqseq.eventually_const_lt h)).exists
            have h3 := moebiusMap_im_neg (V n) hn1
            rw [hiden n] at h3
            linarith
        obtain ⟨N, hN⟩ := eventually_atTop.mp ((hpseq.eventually_lt_const hneg).and
          (hqseq.eventually_lt_const hqneg))
        have hshift : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
        have hpc : Tendsto (fun k => starRingEnd ℂ (Fn (k + N) Complex.I)) atTop
            (𝓝 (starRingEnd ℂ (G Complex.I))) :=
          (Complex.continuous_conj.tendsto _).comp (hp.comp hshift)
        have hqc : Tendsto (fun k => starRingEnd ℂ (Fn (k + N) z₁)) atTop
            (𝓝 (starRingEnd ℂ (G z₁))) :=
          (Complex.continuous_conj.tendsto _).comp (hq.comp hshift)
        obtain ⟨V₀, hV₀, hfr⟩ := exists_frequently_const_witness hxF
          (V := fun k => V (k + N)) (fun k => hVmem (k + N)) hpc hqc
          (fun k => by
            show (0 : ℝ) < (starRingEnd ℂ (Fn (k + N) Complex.I)).im
            rw [Complex.conj_im]
            linarith [(hN (k + N) (Nat.le_add_left N k)).1])
          (fun k => by
            show (0 : ℝ) < (starRingEnd ℂ (Fn (k + N) z₁)).im
            rw [Complex.conj_im]
            linarith [(hN (k + N) (Nat.le_add_left N k)).2])
          (by rw [Complex.conj_im]; linarith)
          (by rw [Complex.conj_im]; linarith)
          (fun k => by
            show moebiusMap (V (k + N)) (starRingEnd ℂ (Fn (k + N) Complex.I))
              = starRingEnd ℂ (Fn (k + N) z₁)
            rw [moebiusMap_conj, hiden (k + N)])
        refine ⟨V₀, hV₀, ?_⟩
        rw [Filter.frequently_atTop] at hfr ⊢
        intro M
        obtain ⟨k, hk, hVk⟩ := hfr M
        exact ⟨k + N, le_trans hk (Nat.le_add_right k N), hVk⟩
      · -- the limit preserves the upper half plane
        have hqpos : 0 < (G z₁).im := by
          rcases lt_or_gt_of_ne hqim with h | h
          · exfalso
            obtain ⟨n, hn1, hn2⟩ := ((hpseq.eventually_const_lt hpos).and
              (hqseq.eventually_lt_const h)).exists
            have h3 := moebiusMap_im_pos (V n) hn1
            rw [hiden n] at h3
            linarith
          · exact h
        obtain ⟨N, hN⟩ := eventually_atTop.mp ((hpseq.eventually_const_lt hpos).and
          (hqseq.eventually_const_lt hqpos))
        have hshift : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
        have hps : Tendsto (fun k => Fn (k + N) Complex.I) atTop (𝓝 (G Complex.I)) :=
          hp.comp hshift
        have hqs : Tendsto (fun k => Fn (k + N) z₁) atTop (𝓝 (G z₁)) :=
          hq.comp hshift
        obtain ⟨V₀, hV₀, hfr⟩ := exists_frequently_const_witness hxF
          (V := fun k => V (k + N)) (fun k => hVmem (k + N)) hps hqs
          (fun k => (hN (k + N) (Nat.le_add_left N k)).1)
          (fun k => (hN (k + N) (Nat.le_add_left N k)).2)
          hpos hqpos (fun k => hiden (k + N))
        refine ⟨V₀, hV₀, ?_⟩
        rw [Filter.frequently_atTop] at hfr ⊢
        intro M
        obtain ⟨k, hk, hVk⟩ := hfr M
        exact ⟨k + N, le_trans hk (Nat.le_add_right k N), hVk⟩
    obtain ⟨V₀, hV₀mem, hfr⟩ := hfreq
    obtain ⟨φ, hφmono, hφspec⟩ := Filter.extraction_of_frequently_atTop hfr
    refine ⟨V₀, hV₀mem, fun z hz => ?_⟩
    have hφtend : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hL : Tendsto (fun j => Fn (φ j) (moebiusMap W z)) atTop
        (𝓝 (G (moebiusMap W z))) :=
      (tendsto_apply_of_tendstoLocallyUniformly hlu (moebiusMap W z)).comp hφtend
    have hd : moebiusDenom V₀ (G z) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero V₀ (him z hz)
    have hR : Tendsto (fun j => moebiusMap V₀ (Fn (φ j) z)) atTop
        (𝓝 (moebiusMap V₀ (G z))) :=
      (hasDerivAt_moebiusMap V₀ hd).continuousAt.tendsto.comp
        ((tendsto_apply_of_tendstoLocallyUniformly hlu z).comp hφtend)
    have hEq : (fun j => Fn (φ j) (moebiusMap W z)) = fun j => moebiusMap V₀ (Fn (φ j) z) :=
      funext fun j => by rw [hViden (φ j) z hz, hφspec j]
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  refine ⟨hGb, hkey, ?_⟩
  intro W' hW'
  obtain ⟨γ, hγ, hxbd⟩ := (x.mem_group_iff_boundary W').mp hW'
  obtain ⟨W, hWmem, hyae⟩ := y.mem_group_of hγ
  have hyid : ∀ z : ℂ, 0 < z.im → y.w (moebiusMap γ z) = moebiusMap W (y.w z) :=
    moebius_conj_upgrade y.w_isQCAnalytic.1.1.continuous
      (fun w hw => ne_of_gt (y.w_mapsTo_upper w hw)) γ W hyae
  obtain ⟨W'', hW''mem, hGW⟩ := hkey W hWmem
  have hagree : ∀ t : ℝ, ¬moebiusDenom γ (t : ℂ) = 0 → ¬moebiusDenom W (y.w (t : ℂ)) = 0 →
      ¬moebiusDenom W'' (x.w (t : ℂ)) = 0 →
      moebiusMap W'' (x.w (t : ℂ)) = moebiusMap W' (x.w (t : ℂ)) := by
    intro t hc1 hc2 hc3
    have hybd : y.w (moebiusMap γ (t : ℂ)) = moebiusMap W (y.w (t : ℂ)) := by
      refine eq_at_real_of_eq_on_upper (Complex.ofReal_im t) ?_ ?_ hyid
      · exact y.w_isQCAnalytic.1.1.continuous.continuousAt.comp
          (hasDerivAt_moebiusMap γ hc1).continuousAt
      · exact (hasDerivAt_moebiusMap W hc2).continuousAt.comp
          y.w_isQCAnalytic.1.1.continuous.continuousAt
    have hGr : G (moebiusMap W (y.w (t : ℂ))) = moebiusMap W'' (G (y.w (t : ℂ))) := by
      have hc3' : moebiusDenom W'' (G (y.w (t : ℂ))) ≠ 0 := by
        rw [hGb t]
        exact hc3
      refine eq_at_real_of_eq_on_upper (y.w_real t) ?_ ?_ hGW
      · exact hGc.continuousAt.comp (hasDerivAt_moebiusMap W hc2).continuousAt
      · exact (hasDerivAt_moebiusMap W'' hc3').continuousAt.comp hGc.continuousAt
    have hgim : (moebiusMap γ (t : ℂ)).im = 0 :=
      moebiusMap_im_eq_zero γ (Complex.ofReal_im t) hc1
    set s : ℝ := (moebiusMap γ (t : ℂ)).re with hs
    have hsval : ((s : ℝ) : ℂ) = moebiusMap γ (t : ℂ) :=
      Complex.ext (by simp [hs]) (by simp [hgim])
    calc moebiusMap W'' (x.w (t : ℂ))
        = moebiusMap W'' (G (y.w (t : ℂ))) := by rw [hGb t]
      _ = G (moebiusMap W (y.w (t : ℂ))) := hGr.symm
      _ = G (y.w (moebiusMap γ (t : ℂ))) := by rw [hybd]
      _ = G (y.w ((s : ℝ) : ℂ)) := by rw [hsval]
      _ = x.w ((s : ℝ) : ℂ) := hGb s
      _ = x.w (moebiusMap γ (t : ℂ)) := by rw [hsval]
      _ = moebiusMap W' (x.w (t : ℂ)) := hxbd t hc1
  obtain ⟨t₁, t₂, t₃, h12, h13, h23, hgood⟩ := exists_three_good_reals
    (P₁ := fun t => moebiusDenom γ (t : ℂ) = 0)
    (P₂ := fun t => moebiusDenom W (y.w (t : ℂ)) = 0)
    (P₃ := fun t => moebiusDenom W'' (x.w (t : ℂ)) = 0)
    (P₄ := fun t => moebiusDenom W' (x.w (t : ℂ)) = 0)
    (fun s t hs ht => Complex.ofReal_injective (moebiusDenom_zero_unique γ hs ht))
    (fun s t hs ht => Complex.ofReal_injective (y.w_injective
      (moebiusDenom_zero_unique W hs ht)))
    (fun s t hs ht => Complex.ofReal_injective (x.w_injective
      (moebiusDenom_zero_unique W'' hs ht)))
    (fun s t hs ht => Complex.ofReal_injective (x.w_injective
      (moebiusDenom_zero_unique W' hs ht)))
  have hxinj : ∀ {a b : ℝ}, x.w (a : ℂ) = x.w (b : ℂ) → a = b :=
    fun h => Complex.ofReal_injective (x.w_injective h)
  have hm1 : t₁ ∈ ({t₁, t₂, t₃} : Set ℝ) := by simp
  have hm2 : t₂ ∈ ({t₁, t₂, t₃} : Set ℝ) := by simp
  have hm3 : t₃ ∈ ({t₁, t₂, t₃} : Set ℝ) := by simp
  have hz12 : x.w (t₁ : ℂ) ≠ x.w (t₂ : ℂ) := fun h => h12 (hxinj h)
  have hz13 : x.w (t₁ : ℂ) ≠ x.w (t₃ : ℂ) := fun h => h13 (hxinj h)
  have hz23 : x.w (t₂ : ℂ) ≠ x.w (t₃ : ℂ) := fun h => h23 (hxinj h)
  have hVden : ∀ z ∈ ({x.w (t₁ : ℂ), x.w (t₂ : ℂ), x.w (t₃ : ℂ)} : Set ℂ),
      moebiusDenom W'' z ≠ 0 := by
    rintro z (rfl | rfl | rfl)
    · exact (hgood t₁ hm1).2.2.1
    · exact (hgood t₂ hm2).2.2.1
    · exact (hgood t₃ hm3).2.2.1
  have hWden : ∀ z ∈ ({x.w (t₁ : ℂ), x.w (t₂ : ℂ), x.w (t₃ : ℂ)} : Set ℂ),
      moebiusDenom W' z ≠ 0 := by
    rintro z (rfl | rfl | rfl)
    · exact (hgood t₁ hm1).2.2.2
    · exact (hgood t₂ hm2).2.2.2
    · exact (hgood t₃ hm3).2.2.2
  have hAgr : ∀ z ∈ ({x.w (t₁ : ℂ), x.w (t₂ : ℂ), x.w (t₃ : ℂ)} : Set ℂ),
      moebiusMap W'' z = moebiusMap W' z := by
    rintro z (rfl | rfl | rfl)
    · exact hagree t₁ (hgood t₁ hm1).1 (hgood t₁ hm1).2.1 (hgood t₁ hm1).2.2.1
    · exact hagree t₂ (hgood t₂ hm2).1 (hgood t₂ hm2).2.1 (hgood t₂ hm2).2.2.1
    · exact hagree t₃ (hgood t₃ hm3).1 (hgood t₃ hm3).2.1 (hgood t₃ hm3).2.2.1
  rcases moebius_ext_three hz12 hz13 hz23 hVden hWden hAgr with hmat | hmat
  · have hWeq : W'' = W' := Subtype.coe_injective hmat
    refine ⟨W, hWmem, fun z hz => ?_⟩
    rw [hGW z hz, hWeq]
  · refine ⟨W, hWmem, fun z hz => ?_⟩
    rw [hGW z hz]
    exact moebiusMap_neg_matrix hmat (G z)

/-- **The equivariant dilatation infimum is attained**: the minimizing-sequence
extraction of `dilatationSet_sInf_mem` together with the limit passage of the marked
candidacy produces an extremal marked candidate. -/
theorem exists_extremal_marked (hΓ₀ : IsFuchsianGroup Γ₀)
    (hfree : ∀ γ : Γ₀, (∃ τ : UpperHalfPlane, γ • τ = τ) →
      ∀ τ' : UpperHalfPlane, γ • τ' = τ')
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ₀ UpperHalfPlane)))
    (x y : TeichRep Γ₀) :
    sInf (gDilatationSet x y) ∈ gDilatationSet x y := by
  classical
  have _ := hcc
  obtain ⟨u, hua, hut, humem⟩ :=
    exists_seq_tendsto_sInf (gDilatationSet_nonempty x y)
      (bddBelow_gDilatationSet x y)
  simp only [gDilatationSet, Set.mem_setOf_eq] at humem
  choose F hFK hFc using humem
  have hfp : ∀ n, F n 0 = 0 := by
    intro n
    have h := (hFc n).1 0
    simp only [Complex.ofReal_zero, TeichRep.w_zero] at h
    exact h
  have hfq : ∀ n, F n 1 = 1 := by
    intro n
    have h := (hFc n).1 1
    simp only [Complex.ofReal_one, TeichRep.w_one] at h
    exact h
  have hK0 : ∀ n, IsQCGeometric (F n) (u 0) := fun n =>
    (hFK n).mono (hua (Nat.zero_le n))
  obtain ⟨φ, G, hφ, hGK, hlu⟩ :=
    exists_subseq_tendstoLocallyUniformly_isQCGeometric hK0
      (zero_ne_one : (0 : ℂ) ≠ 1) (zero_ne_one : (0 : ℂ) ≠ 1) hfp hfq
  have hGmc : IsMarkedCandidate x y G :=
    isMarkedCandidate_of_tendstoLocallyUniformly hΓ₀ hfree hGK hlu
      (fun k => hFc (φ k))
  have hsharp : ∀ K' : ℝ, sInf (gDilatationSet x y) < K' → IsQCGeometric G K' := by
    intro K' hK'
    refine isQCGeometric_limit_of_eventually hlu (fun k => hfp (φ k))
      (fun k => hfq (φ k)) ?_
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hut.eventually_lt_const hK')
    exact eventually_atTop.mpr ⟨N, fun k hk => (hFK (φ k)).mono
      (hN (φ k) (le_trans hk hφ.le_apply)).le⟩
  have h1le : 1 ≤ sInf (gDilatationSet x y) :=
    le_csInf (gDilatationSet_nonempty x y)
      fun _ hK => one_le_of_mem_gDilatationSet hK
  exact ⟨G, isQCGeometric_of_forall_gt h1le hsharp, hGmc⟩

/-! ## The square warm-up: extremality of the affine stretch -/

/-- The horizontal stretch of factor `Λ`: the affine map `x + iy ↦ Λx + iy`. -/
noncomputable def horizontalStretch (Λ : ℝ) : ℂ → ℂ :=
  fun z => (Λ * z.re : ℝ) + z.im * Complex.I

/-- The horizontal stretch in coordinates: `⟨t, y⟩ ↦ ⟨Λt, y⟩`. -/
theorem horizontalStretch_mk (Λ t y : ℝ) :
    horizontalStretch Λ (Complex.mk t y) = Complex.mk (Λ * t) y := by
  unfold horizontalStretch
  apply Complex.ext <;> simp

/-- The horizontal stretch is continuous. -/
theorem continuous_horizontalStretch (Λ : ℝ) : Continuous (horizontalStretch Λ) := by
  unfold horizontalStretch
  exact (Complex.continuous_ofReal.comp (continuous_const.mul Complex.continuous_re)).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

/-- The horizontal embedding `t ↦ ⟨t, y⟩` of a horizontal line is continuous. -/
theorem continuous_mk_left (y : ℝ) : Continuous fun t : ℝ => Complex.mk t y := by
  have h : (fun t : ℝ => Complex.mk t y)
      = fun t : ℝ => ((t : ℂ) + (y : ℝ) * Complex.I) := by
    funext t
    apply Complex.ext <;> simp
  rw [h]
  exact Complex.continuous_ofReal.add continuous_const

/-- A `1`-Lipschitz post-composition preserves absolute continuity on an interval. -/
theorem comp_ac_of_dist_le {l : ℂ → ℝ} (hl : ∀ z w : ℂ, dist (l z) (l w) ≤ dist z w)
    {ψ : ℝ → ℂ} {a b : ℝ} (h : AbsolutelyContinuousOnInterval ψ a b) :
    AbsolutelyContinuousOnInterval (fun t => l (ψ t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := h ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  calc ∑ i ∈ Finset.range E.1, dist (l (ψ (E.2 i).1)) (l (ψ (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, dist (ψ (E.2 i).1) (ψ (E.2 i).2) :=
        Finset.sum_le_sum fun i _ => hl _ _
    _ < ε := hδ' E hE hlen

/-- The real part of an absolutely continuous curve is absolutely continuous. -/
theorem re_comp_ac {ψ : ℝ → ℂ} {a b : ℝ} (h : AbsolutelyContinuousOnInterval ψ a b) :
    AbsolutelyContinuousOnInterval (fun t => (ψ t).re) a b := by
  refine comp_ac_of_dist_le (fun z w => ?_) h
  rw [Real.dist_eq, Complex.dist_eq, ← Complex.sub_re]
  exact Complex.abs_re_le_norm _

/-- The affine horizontal parametrization `t ↦ Λt` is absolutely continuous as a curve. -/
theorem affine_ac (Λ : ℝ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ((Λ * t : ℝ) : ℂ)) a b := by
  have hl : LipschitzWith ⟨|Λ|, abs_nonneg Λ⟩ (fun t : ℝ => ((Λ * t : ℝ) : ℂ)) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [Complex.dist_eq]
    have : ((Λ * s : ℝ) : ℂ) - ((Λ * t : ℝ) : ℂ) = ((Λ * s - Λ * t : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs, ← mul_sub, abs_mul]
    exact le_of_eq rfl
  exact (hl.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval

/-- The affine horizontal parametrization has derivative `Λ`. -/
theorem affine_hasDerivAt (Λ t : ℝ) :
    HasDerivAt (fun s : ℝ => ((Λ * s : ℝ) : ℂ)) (Λ : ℂ) t := by
  have h1 : HasDerivAt (fun s : ℝ => Λ * s) Λ t := by
    simpa using (hasDerivAt_id t).const_mul Λ
  simpa using h1.ofReal_comp

/-! ## The a.e. horizontal slice derivative (Fubini) -/

/-- From almost-everywhere plane differentiability, for almost every height the horizontal
slice has, at almost every parameter, derivative the plane derivative of the horizontal
direction. -/
theorem ae_slice_hasDerivAt {G : ℂ → ℂ} (hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ G z) :
    ∀ᵐ y : ℝ, ∀ᵐ x : ℝ,
      HasDerivAt (fun t : ℝ => G (Complex.mk t y)) ((fderiv ℝ G (Complex.mk x y)) 1) x := by
  have hmpsymm : MeasurePreserving Complex.measurableEquivRealProd.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have hpb : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ G (Complex.mk p.1 p.2) := by
    have := hmpsymm.quasiMeasurePreserving.ae hdiff
    filter_upwards [this] with p hp
    simpa [Complex.measurableEquivRealProd_symm_apply] using hp
  have hprod : ∀ᵐ p : ℝ × ℝ, DifferentiableAt ℝ G (Complex.mk p.2 p.1) := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hpb
    simpa [Prod.swap] using this
  have hline : ∀ᵐ y : ℝ, ∀ᵐ x : ℝ, DifferentiableAt ℝ G (Complex.mk x y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hline] with y hy
  filter_upwards [hy] with x hx
  have := hx.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_horizontalSegment y x)
  simpa using this

/-! ## The per-slice fundamental theorem of calculus -/

/-- The real-part increment of an absolutely continuous curve with almost-everywhere
derivative `D` is the integral of the real part of `D`. -/
theorem slice_re_integral {ψ D : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval ψ 0 1)
    (hder : ∀ᵐ t : ℝ, HasDerivAt ψ (D t) t) :
    ∫ t in Set.Icc (0 : ℝ) 1, (D t).re = (ψ 1).re - (ψ 0).re := by
  set φ : ℝ → ℝ := fun t => (ψ t).re with hφ
  have hφac : AbsolutelyContinuousOnInterval φ 0 1 := re_comp_ac hac
  have hφder : ∀ᵐ t : ℝ, HasDerivAt φ ((D t).re) t := by
    filter_upwards [hder] with t ht
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
    simpa [hφ] using this
  have hcongr : ∫ x in (0 : ℝ)..1, deriv φ x = ∫ x in (0 : ℝ)..1, (D x).re := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hφder] with x hx _
    exact hx.deriv
  have hftc : ∫ x in (0 : ℝ)..1, deriv φ x = φ 1 - φ 0 := hφac.integral_deriv_eq_sub
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1),
    ← hcongr, hftc]

/-- **The per-slice length bound**: the real-part increment of an absolutely continuous
curve is bounded by the flat length `∫ ‖D‖` of its almost-everywhere derivative. -/
theorem slice_lower {ψ D : ℝ → ℂ}
    (hac : AbsolutelyContinuousOnInterval ψ 0 1)
    (hder : ∀ᵐ t : ℝ, HasDerivAt ψ (D t) t) (hmeas : Measurable D) :
    ENNReal.ofReal ((ψ 1).re - (ψ 0).re) ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ := by
  by_cases htop : (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ) = ⊤
  · rw [htop]; exact le_top
  have hInt : IntegrableOn (fun t => ‖D t‖) (Set.Icc (0 : ℝ) 1) := by
    refine ⟨hmeas.norm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa [enorm_norm] using lt_top_iff_ne_top.mpr htop
  have hReInt : IntegrableOn (fun t => (D t).re) (Set.Icc (0 : ℝ) 1) := by
    refine hInt.mono' (Complex.measurable_re.comp hmeas).aestronglyMeasurable ?_
    filter_upwards with t
    exact Complex.abs_re_le_norm _
  have hle : ∫ t in Set.Icc (0 : ℝ) 1, (D t).re ≤ ∫ t in Set.Icc (0 : ℝ) 1, ‖D t‖ :=
    integral_mono hReInt hInt fun t => Complex.re_le_norm _
  calc ENNReal.ofReal ((ψ 1).re - (ψ 0).re)
      = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, (D t).re) := by
        rw [slice_re_integral hac hder]
    _ ≤ ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, ‖D t‖) := ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖D t‖ := by
        refine ofReal_integral_eq_lintegral_ofReal hInt ?_
        filter_upwards with t using norm_nonneg _
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ :=
        lintegral_congr fun t => ofReal_norm_eq_enorm _

/-! ## Fubini over a rectangle and the a.e. length–area kernel -/

/-- **Fubini for a measurable density over a rectangle**: the iterated slice integral is
the area integral over the complex rectangle. -/
theorem lintegral_slice_eq_rect {D : ℂ → ℝ≥0∞} (hD : Measurable D) (a b c d : ℝ) :
    ∫⁻ y in Set.Icc c d, ∫⁻ t in Set.Icc a b, D (Complex.mk t y)
      = ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc c d}, D z := by
  have hpre : {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc c d}
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod]
  have hstep : ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc a b ∧ z.im ∈ Set.Icc c d}, D z
      = ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
          D (Complex.measurableEquivRealProd.symm p) := by
    have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p => D (Complex.measurableEquivRealProd.symm p))
      (Set.Icc a b ×ˢ Set.Icc c d)
    simp only [MeasurableEquiv.symm_apply_apply] at h
    rw [hpre, ← h]
  have hprod : ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
      D (Complex.measurableEquivRealProd.symm p)
      = ∫⁻ y in Set.Icc c d, ∫⁻ t in Set.Icc a b, D (Complex.mk t y) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
    · simp only [Complex.measurableEquivRealProd_symm_apply]
    · exact (hD.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable
  rw [hstep, hprod]

/-- **The a.e. length–area kernel**: an almost-everywhere per-slice lower bound integrates
by Cauchy–Schwarz and Tonelli to the length–area inequality. -/
theorem lengthArea_kernel_ae {F : ℝ → ℝ → ℝ≥0∞} {a b c d : ℝ} (hab : a < b)
    (hmeas : ∀ y, Measurable fun t => F t y) {L : ℝ≥0∞}
    (hL : ∀ᵐ y : ℝ, y ∈ Set.Icc c d → L ≤ ∫⁻ t in Set.Icc a b, F t y) :
    ENNReal.ofReal (d - c) * L ^ 2
      ≤ ENNReal.ofReal (b - a)
        * ∫⁻ y in Set.Icc c d, ∫⁻ t in Set.Icc a b, (F t y) ^ 2 := by
  have hconst : ∫⁻ (_ : ℝ) in Set.Icc c d, L ^ 2 = ENNReal.ofReal (d - c) * L ^ 2 := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, mul_comm]
  calc ENNReal.ofReal (d - c) * L ^ 2
      = ∫⁻ (_ : ℝ) in Set.Icc c d, L ^ 2 := hconst.symm
    _ ≤ ∫⁻ y in Set.Icc c d,
          ENNReal.ofReal (b - a) * ∫⁻ t in Set.Icc a b, (F t y) ^ 2 := by
        refine setLIntegral_mono_ae' measurableSet_Icc ?_
        filter_upwards [hL] with y hy hyIcc
        exact sq_le_lintegral_sq_of_le_lintegral hab (hmeas y) (hy hyIcc)
    _ = ENNReal.ofReal (b - a)
          * ∫⁻ y in Set.Icc c d, ∫⁻ t in Set.Icc a b, (F t y) ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## The image of the square lies in the image rectangle -/

/-- The coordinates of the horizontal stretch. -/
theorem horizontalStretch_re (Λ : ℝ) (z : ℂ) :
    (horizontalStretch Λ z).re = Λ * z.re := by simp [horizontalStretch]

/-- The imaginary part of the horizontal stretch. -/
theorem horizontalStretch_im (Λ : ℝ) (z : ℂ) :
    (horizontalStretch Λ z).im = z.im := by simp [horizontalStretch]

/-- The complement of a closed coordinate rectangle is a union of four open half-planes
meeting in a chain, hence preconnected. -/
theorem rectCompl_preconnected (Λ : ℝ) (_hΛ : 0 < Λ) :
    IsPreconnected {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) Λ ∧ z.im ∈ Set.Icc (0 : ℝ) 1}ᶜ := by
  have hchar : {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) Λ ∧ z.im ∈ Set.Icc (0 : ℝ) 1}ᶜ
      = {c : ℂ | c.re < 0} ∪ ({c : ℂ | (1 : ℝ) < c.im}
        ∪ ({c : ℂ | Λ < c.re} ∪ {c : ℂ | c.im < 0})) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_union, not_and_or,
      not_le]
    tauto
  rw [hchar]
  have hA : IsPreconnected {c : ℂ | c.re < 0} := (convex_halfSpace_re_lt 0).isPreconnected
  have hB : IsPreconnected {c : ℂ | (1 : ℝ) < c.im} :=
    (convex_halfSpace_im_gt 1).isPreconnected
  have hC : IsPreconnected {c : ℂ | Λ < c.re} := (convex_halfSpace_re_gt Λ).isPreconnected
  have hD : IsPreconnected {c : ℂ | c.im < 0} := (convex_halfSpace_im_lt 0).isPreconnected
  have hCD : IsPreconnected ({c : ℂ | Λ < c.re} ∪ {c : ℂ | c.im < 0}) := by
    refine hC.union (Complex.mk (Λ + 1) (-1)) ?_ ?_ hD
    · simp only [Set.mem_setOf_eq]
      exact lt_add_one Λ
    · simp only [Set.mem_setOf_eq]
      norm_num
  have hBCD : IsPreconnected ({c : ℂ | (1 : ℝ) < c.im}
      ∪ ({c : ℂ | Λ < c.re} ∪ {c : ℂ | c.im < 0})) := by
    refine hB.union (Complex.mk (Λ + 1) 2) ?_ ?_ hCD
    · simp only [Set.mem_setOf_eq]
      norm_num
    · exact Or.inl (by simp only [Set.mem_setOf_eq]; exact lt_add_one Λ)
  refine hA.union (Complex.mk (-1) 2) ?_ ?_ hBCD
  · simp only [Set.mem_setOf_eq]
    norm_num
  · exact Or.inl (by simp only [Set.mem_setOf_eq]; norm_num)

/-- **The image of the unit square lies in the stretched rectangle**: a plane homeomorphism
agreeing with the horizontal stretch on the boundary of the unit square maps the square
into the closed rectangle `[0, Λ] × [0, 1]`; the open image of the interior cannot meet the
preconnected unbounded complement of the rectangle since its closure-boundary lies on the
image of the square boundary. -/
theorem image_square_subset_rect {Λ : ℝ} {G : ℂ → ℂ} (hΛ : 1 ≤ Λ)
    (hhomeo : IsHomeomorph G)
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1) → G z = horizontalStretch Λ z) :
    G '' {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1}
      ⊆ {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) Λ ∧ z.im ∈ Set.Icc (0 : ℝ) 1} := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  set h : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph with hh
  set Sq : Set ℂ := {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1} with hSqd
  set Rect : Set ℂ := {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) Λ ∧ z.im ∈ Set.Icc (0 : ℝ) 1}
    with hRectd
  have hSq : Sq = h ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := rfl
  have hSqInt : interior Sq = h ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
    rw [hSq, ← Homeomorph.preimage_interior, interior_prod_eq, interior_Icc]
  have hSqClos : closure (interior Sq) = Sq := by
    rw [hSqInt, ← Homeomorph.preimage_closure, closure_prod_eq,
      closure_Ioo one_ne_zero.symm, hSq]
  have hGc : Continuous G := hhomeo.continuous
  have hGinj : Function.Injective G := hhomeo.injective
  have hSqComp : IsCompact Sq := by
    rw [hSq, Homeomorph.isCompact_preimage]
    exact isCompact_Icc.prod isCompact_Icc
  set U : Set ℂ := G '' interior Sq with hUd
  have hUopen : IsOpen U := hhomeo.isOpenMap _ isOpen_interior
  have hclosU : closure U = G '' Sq := by
    refine Set.Subset.antisymm ?_ ?_
    · exact closure_minimal (Set.image_mono interior_subset) (hSqComp.image hGc).isClosed
    · calc G '' Sq = G '' closure (interior Sq) := by rw [hSqClos]
        _ ⊆ closure (G '' interior Sq) := image_closure_subset_closure_image hGc
  have hfront : G '' Sq \ U ⊆ Rect := by
    rw [hUd, ← Set.image_diff hGinj]
    rintro _ ⟨z, hz, rfl⟩
    have hzSq : z ∈ Sq := hz.1
    have hre : z.re ∈ Set.Icc (0 : ℝ) 1 := hzSq.1
    have him : z.im ∈ Set.Icc (0 : ℝ) 1 := hzSq.2
    have hedge : z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1 := by
      have hnot : ¬(z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) 1) := by
        intro hcon
        exact hz.2 (by rw [hSqInt]; exact ⟨hcon.1, hcon.2⟩)
      rcases not_and_or.mp hnot with hcon | hcon
      · rw [Set.mem_Ioo] at hcon
        rcases not_and_or.mp hcon with h0 | h1
        · exact Or.inl (le_antisymm (not_lt.mp h0) hre.1)
        · exact Or.inr (Or.inl (le_antisymm hre.2 (not_lt.mp h1)))
      · rw [Set.mem_Ioo] at hcon
        rcases not_and_or.mp hcon with h0 | h1
        · exact Or.inr (Or.inr (Or.inl (le_antisymm (not_lt.mp h0) him.1)))
        · exact Or.inr (Or.inr (Or.inr (le_antisymm him.2 (not_lt.mp h1))))
    rw [hb z hre him hedge]
    refine ⟨?_, ?_⟩
    · rw [horizontalStretch_re]
      exact ⟨mul_nonneg hΛ0.le hre.1, by
        calc Λ * z.re ≤ Λ * 1 := mul_le_mul_of_nonneg_left hre.2 hΛ0.le
          _ = Λ := mul_one Λ⟩
    · rw [horizontalStretch_im]
      exact him
  have hEU : Rectᶜ ∩ U = ∅ := by
    by_contra hne
    rw [← Ne, ← Set.nonempty_iff_ne_empty] at hne
    obtain ⟨x, hxE, hxU⟩ := hne
    have hbnd : Bornology.IsBounded (G '' Sq) := (hSqComp.image hGc).isBounded
    obtain ⟨r, hr⟩ := hbnd.subset_closedBall 0
    set w : ℂ := Complex.mk 0 (max r 0 + 2) with hw
    have hwE : w ∈ Rectᶜ := by
      intro hwR
      have : w.im ≤ 1 := hwR.2.2
      have him2 : w.im = max r 0 + 2 := rfl
      have : max r 0 + 2 ≤ 1 := him2 ▸ this
      have := le_max_right r 0
      linarith
    have hwnot : w ∉ closure U := by
      rw [hclosU]
      intro hwcl
      have h1 : ‖w‖ ≤ r := by
        have := hr hwcl
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      have h3 : w.im = max r 0 + 2 := rfl
      have h4 : |w.im| = max r 0 + 2 := by
        rw [h3, abs_of_nonneg (by positivity)]
      have := le_max_left r 0
      linarith
    have hsub : Rectᶜ ⊆ U ∪ (closure U)ᶜ := by
      intro e heE
      by_cases hc : e ∈ closure U
      · left
        by_contra heU
        exact heE (hfront ⟨hclosU ▸ hc, heU⟩)
      · exact Or.inr hc
    have hpre := rectCompl_preconnected Λ hΛ0
    obtain ⟨p, _, hpU, hpc⟩ := hpre U (closure U)ᶜ hUopen isClosed_closure.isOpen_compl
      hsub ⟨x, hxE, hxU⟩ ⟨w, hwE, hwnot⟩
    exact hpc (subset_closure hpU)
  intro x hx
  by_contra hxR
  by_cases hxU : x ∈ U
  · exact (Set.eq_empty_iff_forall_notMem.mp hEU x) ⟨hxR, hxU⟩
  · exact hxR (hfront ⟨hx, hxU⟩)

/-! ## The Jacobian area bound and the rectangle volume -/

/-- **The area bound**: for an injective, almost-everywhere differentiable plane map the
Jacobian integral over a measurable set is at most the measure of the image. -/
theorem area_bound {G : ℂ → ℂ} (hinj : Function.Injective G)
    (hdiff : ∀ᵐ z : ℂ, DifferentiableAt ℝ G z) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ z in S, ENNReal.ofReal ((fderiv ℝ G z).det) ≤ volume (G '' S) := by
  classical
  set s : Set ℂ := S ∩ {z : ℂ | DifferentiableAt ℝ G z} with hsd
  have hsmeas : MeasurableSet s := hS.inter (measurableSet_of_differentiableAt ℝ G)
  have hnull : volume (S \ s) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.mp hdiff)
    exact fun hdz => hz.2 ⟨hz.1, hdz⟩
  have hae : S =ᵐ[volume] s := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨hnull, ?_⟩
    rw [Set.diff_eq_empty.mpr Set.inter_subset_left]
    exact measure_empty
  calc ∫⁻ z in S, ENNReal.ofReal ((fderiv ℝ G z).det)
      = ∫⁻ z in s, ENNReal.ofReal ((fderiv ℝ G z).det) := by
        rw [Measure.restrict_congr_set hae]
    _ ≤ ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| := by
        refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ volume (G '' s) := by
        refine lintegral_abs_det_fderiv_le_addHaar_image volume hsmeas
          (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) (hinj.injOn)
    _ ≤ volume (G '' S) := measure_mono (Set.image_mono Set.inter_subset_left)

/-- The volume of the closed coordinate rectangle `[0, Λ] × [0, 1]`. -/
theorem rect_volume (Λ : ℝ) :
    volume {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) Λ ∧ z.im ∈ Set.Icc (0 : ℝ) 1}
      = ENNReal.ofReal Λ := by
  have hpre : {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) Λ ∧ z.im ∈ Set.Icc (0 : ℝ) 1}
      = Complex.measurableEquivRealProd ⁻¹' (Set.Icc (0 : ℝ) Λ ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
      Set.mem_prod]
  rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  simp

/-! ## The two half-chains of the length–area argument -/

/-- **The a.e. slice lower bound**: on almost every horizontal slice of the unit square the
flat length of the image curve is at least `Λ`, by absolute continuity on lines and the
boundary agreement pinning the endpoints. -/
theorem slice_chain {Λ K : ℝ} {G : ℂ → ℂ} (hG : IsQCGeometric G K)
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1) → G z = horizontalStretch Λ z) :
    ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      ENNReal.ofReal Λ
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ := by
  obtain ⟨gx, gy, hACx, -, -, -⟩ := hG.exists_acl_weakGradient
  have hslice := ae_slice_hasDerivAt hG.ae_differentiableAt
  filter_upwards [hACx, hslice] with y hy1 hy2 hyIcc
  have hac : AbsolutelyContinuousOnInterval (fun t : ℝ => G (Complex.mk t y)) 0 1 :=
    hy1.1 0 1
  have hmeasD : Measurable fun t : ℝ => (fderiv ℝ G (Complex.mk t y)) 1 :=
    (measurable_fderiv_apply_const ℝ G 1).comp (continuous_mk_left y).measurable
  have h0 : G (Complex.mk 0 y) = Complex.mk 0 y := by
    have heq := hb (Complex.mk 0 y) (by simp) (by simpa using hyIcc) (Or.inl rfl)
    rw [heq, horizontalStretch_mk, mul_zero]
  have h1 : G (Complex.mk 1 y) = Complex.mk Λ y := by
    have heq := hb (Complex.mk 1 y) (by simp) (by simpa using hyIcc) (Or.inr (Or.inl rfl))
    rw [heq, horizontalStretch_mk, mul_one]
  have hlow := slice_lower hac hy2 hmeasD
  rw [h1, h0] at hlow
  simpa using hlow

/-- **The area upper bound**: the square integral of the horizontal derivative over the
unit square is at most `K · Λ`, through the pointwise distortion inequality, the Jacobian
area bound, and the containment of the image in the stretched rectangle. -/
theorem area_chain {Λ K : ℝ} {G : ℂ → ℂ} (hΛ : 1 ≤ Λ) (hG : IsQCGeometric G K)
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1) → G z = horizontalStretch Λ z) :
    (∫⁻ y in Set.Icc (0 : ℝ) 1, ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2)
      ≤ ENNReal.ofReal K * ENNReal.ofReal Λ := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hG.1
  have hhomeo : IsHomeomorph G := hG.2.1.1
  have hdist := hG.reverseLengthArea_data.2.2.1
  set D : ℂ → ℝ≥0∞ := fun z => ‖(fderiv ℝ G z) 1‖ₑ ^ 2 with hD
  have hDmeas : Measurable D := ((measurable_fderiv_apply_const ℝ G 1).enorm).pow_const 2
  have hfub := lintegral_slice_eq_rect hDmeas 0 1 0 1
  have hSqmeas : MeasurableSet {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0:ℝ) 1} :=
    (measurableSet_Icc.preimage Complex.measurable_re).inter
      (measurableSet_Icc.preimage Complex.measurable_im)
  have hbound : ∀ᵐ z ∂volume,
      z ∈ {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1} →
      D z ≤ ENNReal.ofReal (K * (fderiv ℝ G z).det) := by
    filter_upwards [hdist] with z hz _
    have h1 : ‖(fderiv ℝ G z) 1‖ ≤ ‖fderiv ℝ G z‖ := by
      have := (fderiv ℝ G z).le_opNorm 1
      simpa using this
    have h2 : ‖(fderiv ℝ G z) 1‖ ^ 2 ≤ K * (fderiv ℝ G z).det := by
      nlinarith [norm_nonneg ((fderiv ℝ G z) 1), norm_nonneg (fderiv ℝ G z)]
    calc D z = ENNReal.ofReal (‖(fderiv ℝ G z) 1‖ ^ 2) := by
          simp only [hD]
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (K * (fderiv ℝ G z).det) := ENNReal.ofReal_le_ofReal h2
  calc (∫⁻ y in Set.Icc (0 : ℝ) 1, ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2)
      = ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧ z.im ∈ Set.Icc (0:ℝ) 1}, D z := hfub
    _ ≤ ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧ z.im ∈ Set.Icc (0:ℝ) 1},
          ENNReal.ofReal (K * (fderiv ℝ G z).det) := setLIntegral_mono_ae' hSqmeas hbound
    _ = ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧ z.im ∈ Set.Icc (0:ℝ) 1},
          ENNReal.ofReal K * ENNReal.ofReal ((fderiv ℝ G z).det) :=
        lintegral_congr fun z => by rw [ENNReal.ofReal_mul hK0]
    _ = ENNReal.ofReal K * ∫⁻ z in {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧
          z.im ∈ Set.Icc (0:ℝ) 1}, ENNReal.ofReal ((fderiv ℝ G z).det) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K
          * volume (G '' {z : ℂ | z.re ∈ Set.Icc (0:ℝ) 1 ∧ z.im ∈ Set.Icc (0:ℝ) 1}) :=
        mul_le_mul_right
          (area_bound hhomeo.injective hG.ae_differentiableAt hSqmeas) _
    _ ≤ ENNReal.ofReal K
          * volume {z : ℂ | z.re ∈ Set.Icc (0:ℝ) Λ ∧ z.im ∈ Set.Icc (0:ℝ) 1} :=
        mul_le_mul_right
          (measure_mono (image_square_subset_rect hΛ hhomeo hb)) _
    _ = ENNReal.ofReal K * ENNReal.ofReal Λ := by rw [rect_volume]

/-! ## The square Grötzsch inequality -/

/-- A measurable minorant with the same finite integral agrees almost everywhere. -/
theorem ae_eq_of_lintegral_le {μ : Measure ℝ} {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hgfin : (∫⁻ y, g y ∂μ) ≠ ⊤) (hle : g ≤ᵐ[μ] f)
    (hint : (∫⁻ y, f y ∂μ) ≤ ∫⁻ y, g y ∂μ) : f =ᵐ[μ] g := by
  have hsub : ∫⁻ y, (f y - g y) ∂μ = (∫⁻ y, f y ∂μ) - ∫⁻ y, g y ∂μ :=
    lintegral_sub hg hgfin hle
  have hzero : ∫⁻ y, (f y - g y) ∂μ = 0 := by
    rw [hsub]
    exact tsub_eq_zero_of_le hint
  have hae := (lintegral_eq_zero_iff (hf.sub hg)).mp hzero
  filter_upwards [hae, hle] with y h1 h2
  simp only [Pi.zero_apply] at h1
  exact le_antisymm (tsub_eq_zero_iff_le.mp h1) h2

/-- **The per-slice equality analysis**: an absolutely continuous curve with a.e.
derivative `D`, real-part increment `Λ`, flat length exactly `Λ`, and squared length
exactly `Λ²` is the affine horizontal segment: the length and Cauchy–Schwarz equalities
force `D = Λ` almost everywhere, and vanishing-derivative constancy integrates back. -/
theorem slice_eq {Λ : ℝ} {ψ D : ℝ → ℂ} (hΛ : 1 ≤ Λ)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval ψ a b)
    (hder : ∀ᵐ t : ℝ, HasDerivAt ψ (D t) t) (hmeas : Measurable D)
    (h0re : (ψ 0).re = 0) (h1re : (ψ 1).re = Λ)
    (hI1 : ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ = ENNReal.ofReal Λ)
    (hI2 : ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ ^ 2 = ENNReal.ofReal Λ ^ 2) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t = ψ 0 + ((Λ * t : ℝ) : ℂ) := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hInt : IntegrableOn (fun t => ‖D t‖) (Set.Icc (0 : ℝ) 1) := by
    refine ⟨hmeas.norm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp only [enorm_norm]
    rw [hI1]
    exact ENNReal.ofReal_lt_top
  have hIntSq : IntegrableOn (fun t => ‖D t‖ ^ 2) (Set.Icc (0 : ℝ) 1) := by
    refine ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hcong : ∀ t : ℝ, ‖(‖D t‖ ^ 2 : ℝ)‖ₑ = ‖D t‖ₑ ^ 2 := fun t => by
      rw [enorm_pow, enorm_norm]
    calc ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(‖D t‖ ^ 2 : ℝ)‖ₑ
        = ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ ^ 2 := lintegral_congr fun t => hcong t
      _ < ⊤ := by rw [hI2]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hIh : ∫ t in Set.Icc (0 : ℝ) 1, ‖D t‖ = Λ := by
    have h := ofReal_integral_eq_lintegral_ofReal hInt
      (by filter_upwards with t using norm_nonneg _)
    have h2 : ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖D t‖ = ENNReal.ofReal Λ := by
      rw [← hI1]
      exact lintegral_congr fun t => ofReal_norm_eq_enorm _
    rw [h2] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun t => norm_nonneg _) hΛ0.le).mp h
  have hIsq : ∫ t in Set.Icc (0 : ℝ) 1, ‖D t‖ ^ 2 = Λ ^ 2 := by
    have h := ofReal_integral_eq_lintegral_ofReal hIntSq
      (by filter_upwards with t using sq_nonneg _)
    have h2 : ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (‖D t‖ ^ 2)
        = ENNReal.ofReal Λ ^ 2 := by
      rw [← hI2]
      refine lintegral_congr fun t => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [h2, ← ENNReal.ofReal_pow hΛ0.le] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun t => sq_nonneg _)
      (pow_nonneg hΛ0.le 2)).mp h
  have hRe : ∫ t in Set.Icc (0 : ℝ) 1, (D t).re = Λ := by
    rw [slice_re_integral (hac 0 1) hder, h1re, h0re, sub_zero]
  have hReInt : IntegrableOn (fun t => (D t).re) (Set.Icc (0 : ℝ) 1) := by
    refine hInt.mono' (Complex.measurable_re.comp hmeas).aestronglyMeasurable ?_
    filter_upwards with t
    exact Complex.abs_re_le_norm _
  have hsubInt : IntegrableOn (fun t => ‖D t‖ - (D t).re) (Set.Icc (0 : ℝ) 1) :=
    hInt.sub hReInt
  have hae1 : (fun t => ‖D t‖ - (D t).re) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hsubInt).mp ?_
    · filter_upwards with t
      simp only [Pi.zero_apply, sub_nonneg]
      exact Complex.re_le_norm _
    · rw [integral_sub hInt hReInt, hIh, hRe, sub_self]
  have hfun : (fun t => (‖D t‖ - Λ) ^ 2)
      = fun t => ‖D t‖ ^ 2 - 2 * Λ * ‖D t‖ + Λ ^ 2 := funext fun t => by ring
  haveI hfinm : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hIntC : IntegrableOn (fun _ : ℝ => Λ ^ 2) (Set.Icc (0 : ℝ) 1) :=
    integrable_const (Λ ^ 2)
  have hmulInt : IntegrableOn (fun t => 2 * Λ * ‖D t‖) (Set.Icc (0 : ℝ) 1) :=
    hInt.const_mul (2 * Λ)
  have hsub2Int : IntegrableOn (fun t => ‖D t‖ ^ 2 - 2 * Λ * ‖D t‖) (Set.Icc (0 : ℝ) 1) :=
    hIntSq.sub hmulInt
  have hIntSq2 : IntegrableOn (fun t => (‖D t‖ - Λ) ^ 2) (Set.Icc (0 : ℝ) 1) := by
    rw [hfun]
    exact hsub2Int.add hIntC
  have hconst : ∫ t in Set.Icc (0 : ℝ) 1, (‖D t‖ - Λ) ^ 2 = 0 := by
    rw [hfun, integral_add hsub2Int hIntC, integral_sub hIntSq hmulInt, hIsq]
    have hmul : ∫ t in Set.Icc (0 : ℝ) 1, 2 * Λ * ‖D t‖ = 2 * Λ * Λ := by
      rw [integral_const_mul, hIh]
    have hcst : ∫ _ in Set.Icc (0 : ℝ) 1, Λ ^ 2 = Λ ^ 2 := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero,
        ENNReal.toReal_ofReal zero_le_one, one_smul]
    rw [hmul, hcst]
    ring
  have hae2 : (fun t => (‖D t‖ - Λ) ^ 2) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hIntSq2).mp hconst
    filter_upwards with t
    simp only [Pi.zero_apply]
    exact sq_nonneg _
  have hDae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), D t = ((Λ : ℝ) : ℂ) := by
    filter_upwards [hae1, hae2] with t h1 h2
    simp only [Pi.zero_apply] at h1 h2
    have hnorm : ‖D t‖ = Λ := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hre : (D t).re = Λ := by
      have := sub_eq_zero.mp h1
      linarith [this]
    apply Complex.ext
    · simpa using hre
    · have hsq : ‖D t‖ ^ 2 = (D t).re * (D t).re + (D t).im * (D t).im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      rw [hnorm, hre] at hsq
      have him : (D t).im * (D t).im = 0 := by nlinarith
      simpa using mul_self_eq_zero.mp him
  intro t ht
  set χ : ℝ → ℂ := fun s => ψ s - ((Λ * s : ℝ) : ℂ) with hχ
  have hχac : AbsolutelyContinuousOnInterval χ 0 1 := (hac 0 1).sub (affine_ac Λ 0 1)
  have hDae' : ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → D s = ((Λ : ℝ) : ℂ) :=
    (ae_restrict_iff' measurableSet_Icc).mp hDae
  have hχ0 : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt χ 0 s := by
    filter_upwards [hder, hDae'] with s hs1 hs2 hsIcc
    have hmem : s ∈ Set.Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at hsIcc
    have hd := hs1.sub (affine_hasDerivAt Λ s)
    rw [hs2 hmem] at hd
    simpa [hχ] using hd
  obtain ⟨C, hC⟩ := hχac.const_of_ae_hasDerivAt_zero hχ0
  have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one]
  have h0' : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨le_refl 0, zero_le_one⟩
  have hχt : χ t = χ 0 := by rw [hC t ht', hC 0 h0']
  have hχ0v : χ 0 = ψ 0 := by simp [hχ]
  calc ψ t = χ t + ((Λ * t : ℝ) : ℂ) := by simp [hχ]
    _ = ψ 0 + ((Λ * t : ℝ) : ℂ) := by rw [hχt, hχ0v]

/-! ## The continuity upgrade from a.e. slices to the full square -/

/-- A set of full measure in the unit interval is dense in it. -/
theorem dense_of_conull {S : Set ℝ}
    (hnull : volume (Set.Icc (0 : ℝ) 1 \ S) = 0) :
    Set.Icc (0 : ℝ) 1 ⊆ closure S := by
  intro y₀ hy₀
  by_contra hnot
  have hopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen y₀ hnot
  have hdisj : Metric.ball y₀ ε ∩ S = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hx2⟩
    exact hball hx1 (subset_closure hx2)
  set a : ℝ := max 0 (y₀ - ε) with ha
  set b : ℝ := min 1 (y₀ + ε) with hb
  have hab : a < b := by
    rw [ha, hb, max_lt_iff]
    constructor
    · rw [lt_min_iff]
      exact ⟨zero_lt_one, lt_of_le_of_lt hy₀.1 (by linarith)⟩
    · rw [lt_min_iff]
      exact ⟨by linarith [hy₀.2], by linarith⟩
  have hsub : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) 1 \ S := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans (le_max_left 0 (y₀ - ε)) hx.1.le
    have hx1 : x ≤ 1 := le_trans hx.2.le (min_le_left 1 (y₀ + ε))
    refine ⟨⟨hx0, hx1⟩, fun hxS => ?_⟩
    have hxball : x ∈ Metric.ball y₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · have := lt_of_lt_of_le hx.2 (min_le_right 1 (y₀ + ε))
        linarith
      · have := lt_of_le_of_lt (le_max_right 0 (y₀ - ε)) hx.1
        linarith
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj x) ⟨hxball, hxS⟩
  have hpos : (0 : ℝ≥0∞) < volume (Set.Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact absurd (le_trans (measure_mono hsub) (le_of_eq hnull)) (not_le.mpr hpos)

/-- **The continuity upgrade**: agreement with the stretch on the slices of almost every
height extends to the full closed square by density and continuity. -/
theorem eq_on_square_of_ae_slices {Λ : ℝ} {G : ℂ → ℂ} (hGc : Continuous G)
    (hae : ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      G (Complex.mk t y) = horizontalStretch Λ (Complex.mk t y)) :
    ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      G z = horizontalStretch Λ z := by
  intro z hre him
  set S : Set ℝ := {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
    G (Complex.mk t y) = horizontalStretch Λ (Complex.mk t y)} with hS
  have hnull : volume (Set.Icc (0 : ℝ) 1 \ S) = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae)
    exact fun hyP => hy.2 ⟨hy.1, hyP hy.1⟩
  have hdense := dense_of_conull hnull
  have hEq : Set.EqOn (fun y : ℝ => G (Complex.mk z.re y))
      (fun y : ℝ => horizontalStretch Λ (Complex.mk z.re y)) S := by
    intro y hy
    exact hy.2 z.re hre
  have hc1 : Continuous fun y : ℝ => G (Complex.mk z.re y) := by
    have hmk : Continuous fun y : ℝ => Complex.mk z.re y := by
      have h : (fun y : ℝ => Complex.mk z.re y)
          = fun y : ℝ => ((z.re : ℂ) + (y : ℝ) * Complex.I) := by
        funext y
        apply Complex.ext <;> simp
      rw [h]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact hGc.comp hmk
  have hc2 : Continuous fun y : ℝ => horizontalStretch Λ (Complex.mk z.re y) := by
    have hmk : Continuous fun y : ℝ => Complex.mk z.re y := by
      have h : (fun y : ℝ => Complex.mk z.re y)
          = fun y : ℝ => ((z.re : ℂ) + (y : ℝ) * Complex.I) := by
        funext y
        apply Complex.ext <;> simp
      rw [h]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact (continuous_horizontalStretch Λ).comp hmk
  have hclos := hEq.closure hc1 hc2
  have hz : z.im ∈ closure S := hdense him
  have := hclos hz
  simpa using this

/-! ## The square Grötzsch equality case -/

/-- **The square Grötzsch inequality**: a quasiconformal plane map agreeing with the
horizontal stretch of factor `Λ ≥ 1` on the boundary of the unit square has dilatation at
least `Λ`; the horizontal slices of the square are stretched by `Λ`, and the length–area
estimate bounds the stretch by the dilatation. -/
theorem grotzsch_square {Λ K : ℝ} {G : ℂ → ℂ} (hΛ : 1 ≤ Λ) (hG : IsQCGeometric G K)
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1) → G z = horizontalStretch Λ z) :
    Λ ≤ K := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hG.1
  have hkernel := lengthArea_kernel_ae (zero_lt_one (α := ℝ))
    (fun y => ((measurable_fderiv_apply_const ℝ G 1).comp
      (continuous_mk_left y).measurable).enorm) (slice_chain hG hb)
  have h1 : (ENNReal.ofReal Λ) ^ 2
      ≤ ∫⁻ y in Set.Icc (0 : ℝ) 1, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2 := by
    simpa using hkernel
  have h3 : (ENNReal.ofReal Λ) ^ 2 ≤ ENNReal.ofReal K * ENNReal.ofReal Λ :=
    le_trans h1 (area_chain hΛ hG hb)
  have hne : ENNReal.ofReal Λ ≠ 0 := (ENNReal.ofReal_pos.mpr hΛ0).ne'
  have h4 : ENNReal.ofReal Λ * ENNReal.ofReal Λ ≤ ENNReal.ofReal K * ENNReal.ofReal Λ := by
    rw [← pow_two]
    exact h3
  have h5 : ENNReal.ofReal Λ ≤ ENNReal.ofReal K :=
    (ENNReal.mul_le_mul_iff_left hne ENNReal.ofReal_ne_top).mp
      (by simpa [mul_comm] using h4)
  exact (ENNReal.ofReal_le_ofReal_iff hK0).mp h5

/-! ## Equality forcing from integral identities -/

/-- **The square Grötzsch equality case**: a plane map of dilatation exactly `Λ` agreeing
with the horizontal stretch on the boundary of the unit square is the horizontal stretch
on the square. -/
theorem grotzsch_square_unique {Λ : ℝ} {G : ℂ → ℂ} (hΛ : 1 ≤ Λ)
    (hG : IsQCGeometric G Λ)
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1) → G z = horizontalStretch Λ z) :
    ∀ z : ℂ, z.re ∈ Set.Icc (0 : ℝ) 1 → z.im ∈ Set.Icc (0 : ℝ) 1 →
      G z = horizontalStretch Λ z := by
  have hGc : Continuous G := hG.2.1.1.continuous
  have hmeasF : ∀ y : ℝ, Measurable fun t : ℝ => ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ :=
    fun y => ((measurable_fderiv_apply_const ℝ G 1).comp
      (continuous_mk_left y).measurable).enorm
  have hlow := slice_chain hG hb
  have h1 : (ENNReal.ofReal Λ) ^ 2 ≤ ∫⁻ y in Set.Icc (0 : ℝ) 1,
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2 := by
    simpa using lengthArea_kernel_ae (zero_lt_one (α := ℝ)) hmeasF hlow
  have hAeq : (∫⁻ y in Set.Icc (0 : ℝ) 1,
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2)
      = (ENNReal.ofReal Λ) ^ 2 := by
    refine le_antisymm ?_ h1
    rw [pow_two]
    exact area_chain hΛ hG hb
  have hmk2 : Measurable fun p : ℝ × ℝ => Complex.mk p.1 p.2 := by
    have hcoe : (fun p : ℝ × ℝ => Complex.mk p.1 p.2)
        = fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p := by
      funext p
      simp [Complex.measurableEquivRealProd_symm_apply]
    rw [hcoe]
    exact Complex.measurableEquivRealProd.symm.measurable
  have huncurry : Measurable (Function.uncurry
      (fun t y : ℝ => ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2)) := by
    have : Function.uncurry (fun t y : ℝ => ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2)
        = fun p : ℝ × ℝ => ‖(fderiv ℝ G (Complex.mk p.1 p.2)) 1‖ₑ ^ 2 := rfl
    rw [this]
    exact (((measurable_fderiv_apply_const ℝ G 1).comp hmk2).enorm).pow_const 2
  have hI2meas : Measurable fun y : ℝ =>
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2 :=
    Measurable.lintegral_prod_left' huncurry
  have hI2low : ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → (ENNReal.ofReal Λ) ^ 2
      ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2 := by
    filter_upwards [hlow] with y hy hyIcc
    simpa using sq_le_lintegral_sq_of_le_lintegral (zero_lt_one (α := ℝ))
      (hmeasF y) (hy hyIcc)
  have hI2eq : (fun y : ℝ =>
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] fun _ => (ENNReal.ofReal Λ) ^ 2 := by
    refine ae_eq_of_lintegral_le hI2meas measurable_const ?_ ?_ ?_
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top).ne
    · exact (ae_restrict_iff' measurableSet_Icc).mpr hI2low
    · rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_one, mul_one]
      exact le_of_eq hAeq
  have hI12 : ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ = ENNReal.ofReal Λ)
      ∧ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2
          = ENNReal.ofReal Λ ^ 2 := by
    have hI2eq' := (ae_restrict_iff' measurableSet_Icc).mp hI2eq
    filter_upwards [hlow, hI2eq'] with y hy1 hy2 hyIcc
    have hI2y := hy2 hyIcc
    refine ⟨?_, hI2y⟩
    have hcs := sq_le_lintegral_sq_of_le_lintegral (zero_lt_one (α := ℝ)) (hmeasF y)
      (le_refl (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ))
    refine le_antisymm ?_ (hy1 hyIcc)
    by_contra hlt
    rw [not_le] at hlt
    have hpow := ENNReal.pow_lt_pow_left two_ne_zero hlt
    have hchain : (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ) ^ 2
        ≤ ENNReal.ofReal Λ ^ 2 := by
      calc (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ) ^ 2
          ≤ ENNReal.ofReal (1 - 0) * ∫⁻ t in Set.Icc (0 : ℝ) 1,
              ‖(fderiv ℝ G (Complex.mk t y)) 1‖ₑ ^ 2 := hcs
        _ = ENNReal.ofReal Λ ^ 2 := by rw [hI2y, sub_zero, ENNReal.ofReal_one, one_mul]
    exact absurd (lt_of_lt_of_le hpow hchain) (lt_irrefl _)
  obtain ⟨gx, gy, hACx, -, -, -⟩ := hG.exists_acl_weakGradient
  have hslice := ae_slice_hasDerivAt hG.ae_differentiableAt
  have haefinal : ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      G (Complex.mk t y) = horizontalStretch Λ (Complex.mk t y) := by
    filter_upwards [hACx, hslice, hI12] with y hy1 hy2 hy3 hyIcc
    obtain ⟨hI1y, hI2y⟩ := hy3 hyIcc
    have h0 : G (Complex.mk 0 y) = Complex.mk 0 y := by
      have heq := hb (Complex.mk 0 y) (by simp) (by simpa using hyIcc) (Or.inl rfl)
      rw [heq, horizontalStretch_mk, mul_zero]
    have h1e : G (Complex.mk 1 y) = Complex.mk Λ y := by
      have heq := hb (Complex.mk 1 y) (by simp) (by simpa using hyIcc)
        (Or.inr (Or.inl rfl))
      rw [heq, horizontalStretch_mk, mul_one]
    have hmeasD : Measurable fun t : ℝ => (fderiv ℝ G (Complex.mk t y)) 1 :=
      (measurable_fderiv_apply_const ℝ G 1).comp (continuous_mk_left y).measurable
    have hkey := slice_eq hΛ hy1.1 hy2 hmeasD
      (by rw [h0]) (by rw [h1e]) hI1y hI2y
    intro t ht
    calc G (Complex.mk t y)
        = G (Complex.mk 0 y) + ((Λ * t : ℝ) : ℂ) := hkey t ht
      _ = Complex.mk 0 y + ((Λ * t : ℝ) : ℂ) := by rw [h0]
      _ = horizontalStretch Λ (Complex.mk t y) := by
          rw [horizontalStretch_mk]
          apply Complex.ext <;> simp
  exact eq_on_square_of_ae_slices hGc haefinal

end RiemannDynamics
