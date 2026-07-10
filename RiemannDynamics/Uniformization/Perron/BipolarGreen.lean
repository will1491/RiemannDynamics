/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.GreensFunction
import RiemannDynamics.Uniformization.Perron.Myrberg

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
* `exists_harnack_chain_const`, `exists_mharmonicOn_limit_of_locally_bounded`
  — the symmetry-free Harnack chain and harmonic normal-families bricks;
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

omit [IsManifold 𝓘(ℂ) ω M] in
/-- Removing a closed coordinate disk keeps the surface connected. -/
theorem isConnected_coordDisk_compl (D : CoordDisk M) :
    IsConnected (D.compl : Set M) := by
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center
  set c : ℂ := e D.center
  set r : ℝ := D.radius
  have hr : 0 < r := D.radius_pos
  have hsub : closedBall c r ⊆ e.target := D.closedBall_subset
  have hcarrier : D.closedCarrier = e.symm '' closedBall c r := rfl
  have hcompl : (D.compl : Set M) = D.closedCarrierᶜ := rfl
  -- A collar radius: a slightly larger open chart ball still inside the target.
  obtain ⟨δ, hδ0, hδsub⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open e.open_target hsub
  set R : ℝ := δ + r with hRdef
  have hrR : r < R := lt_add_of_pos_left r hδ0
  have hballR : ball c R ⊆ e.target := by
    rw [hRdef, ← thickening_closedBall hδ0 hr.le c]
    exact hδsub
  -- The open chart annulus is connected, via polar coordinates.
  have hann : IsConnected (ball c R \ closedBall c r) := by
    have hcont : Continuous fun p : ℝ × ℝ =>
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo r R ×ˢ (Set.univ : Set ℝ)) = ball c R \ closedBall c r := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨hrt, htR⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c R \ closedBall c r
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg (hr.le.trans hrt.le)]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htR
        · intro hmem
          rw [mem_closedBall, hd] at hmem
          exact absurd hmem (not_le.2 hrt)
      · rintro w ⟨hwb, hwc⟩
        have hrt : r < ‖w - c‖ := by
          rw [← dist_eq_norm]
          exact not_le.1 fun h => hwc (mem_closedBall.2 h)
        have htR : ‖w - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨hrt, htR⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    have hmid : (r + R) / 2 ∈ Set.Ioo r R := ⟨by linarith, by linarith⟩
    rw [← himg]
    exact ⟨Set.Nonempty.image _ ⟨((r + R) / 2, 0), hmid, Set.mem_univ _⟩,
      (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn⟩
  -- The chart-ball neighborhood of the closed disk.
  set N : Set M := e.source ∩ e ⁻¹' ball c R
  have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
  have hcN : D.closedCarrier ⊆ N := by
    intro x hx
    rw [hcarrier] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hwt : w ∈ e.target := hsub hw
    refine ⟨e.map_target hwt, ?_⟩
    rw [Set.mem_preimage, e.right_inv hwt]
    exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) hrR)
  -- The image of the annulus is `N` minus the closed disk.
  have himgA : (e.symm : ℂ → M) '' (ball c R \ closedBall c r) = N \ D.closedCarrier := by
    apply Set.Subset.antisymm
    · rintro x ⟨w, ⟨hwb, hwc⟩, rfl⟩
      have hwt : w ∈ e.target := hballR hwb
      refine ⟨⟨e.map_target hwt, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, e.right_inv hwt]; exact hwb
      · rw [hcarrier]
        rintro ⟨w', hw', hw'e⟩
        have hw't : w' ∈ e.target := hsub hw'
        have h2 : e (e.symm w') = e (e.symm w) := by rw [hw'e]
        rw [e.right_inv hw't, e.right_inv hwt] at h2
        exact hwc (h2 ▸ hw')
    · rintro x ⟨⟨hxsrc, hxb⟩, hxc⟩
      rw [Set.mem_preimage] at hxb
      refine ⟨e x, ⟨hxb, fun hmem => hxc ?_⟩, e.left_inv hxsrc⟩
      rw [hcarrier]
      exact ⟨e x, hmem, e.left_inv hxsrc⟩
  have hA : IsConnected (N \ D.closedCarrier) := by
    rw [← himgA]
    exact hann.image _ (e.continuousOn_symm.mono fun w hw => hballR hw.1)
  have hsub' : N \ D.closedCarrier ⊆ D.closedCarrierᶜ := fun z hz => hz.2
  rw [hcompl]
  have hopen : IsOpen (D.closedCarrierᶜ) := D.isCompact_closedCarrier.isClosed.isOpen_compl
  have hcenter : D.center ∈ D.closedCarrier := by
    rw [hcarrier]
    exact ⟨c, mem_closedBall_self hr.le, e.left_inv (mem_chart_source ℂ D.center)⟩
  have hne : (D.closedCarrierᶜ : Set M).Nonempty := by
    obtain ⟨z, hz⟩ := hA.nonempty
    exact ⟨z, hsub' hz⟩
  refine ⟨hne, ?_⟩
  intro u v hu hv huv hsu hsv
  -- One-sided separation lemma: if the surface annulus lies in `u'`, the
  -- separation `u', v'` of the piece extends to a separation of `M`.
  have key : ∀ u' v' : Set M, IsOpen u' → IsOpen v' → D.closedCarrierᶜ ⊆ u' ∪ v' →
      (D.closedCarrierᶜ ∩ v').Nonempty → N \ D.closedCarrier ⊆ u' →
      (D.closedCarrierᶜ ∩ (u' ∩ v')).Nonempty := by
    intro u' v' hu' hv' hcov hv'ne hNu'
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hU : IsOpen (u' ∪ N) := hu'.union hNopen
    have hV : IsOpen (v' ∩ D.closedCarrierᶜ) := hv'.inter hopen
    have hcover : (Set.univ : Set M) ⊆ (u' ∪ N) ∪ v' ∩ D.closedCarrierᶜ := by
      intro z _
      by_cases hz : z ∈ D.closedCarrier
      · exact Or.inl (Or.inr (hcN hz))
      · rcases hcov hz with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hz⟩
    obtain ⟨w, hw1, hw2⟩ := hv'ne
    obtain ⟨z, -, hz⟩ := isPreconnected_univ (u' ∪ N) (v' ∩ D.closedCarrierᶜ) hU hV hcover
      ⟨D.center, Set.mem_univ _, Or.inr (hcN hcenter)⟩ ⟨w, Set.mem_univ w, hw2, hw1⟩
    obtain ⟨hz1, hzv, hzc⟩ := hz
    have hzu : z ∈ u' := by
      rcases hz1 with h | h
      · exact h
      · exact hNu' ⟨h, hzc⟩
    have hmem : z ∈ D.closedCarrierᶜ ∩ (u' ∩ v') := ⟨hzc, hzu, hzv⟩
    rw [hcon] at hmem
    exact hmem
  -- Case split on which side of the separation the surface annulus lies.
  rcases Set.eq_empty_or_nonempty ((N \ D.closedCarrier) ∩ v) with hv0 | hv1
  · have hNu : N \ D.closedCarrier ⊆ u := by
      intro z hz
      rcases huv (hsub' hz) with h | h
      · exact h
      · exact absurd hv0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
    exact key u v hu hv huv hsv hNu
  · rcases Set.eq_empty_or_nonempty ((N \ D.closedCarrier) ∩ u) with hu0 | hu1
    · have hNv : N \ D.closedCarrier ⊆ v := by
        intro z hz
        rcases huv (hsub' hz) with h | h
        · exact absurd hu0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
        · exact h
      have h := key v u hv hu (by rw [Set.union_comm]; exact huv) hsu hNv
      rwa [Set.inter_comm v u] at h
    · obtain ⟨z, hzN, hzuv⟩ := hA.2 u v hu hv (fun z hz => huv (hsub' hz)) hu1 hv1
      exact ⟨z, hsub' hzN, hzuv⟩

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The complement of a closed coordinate disk is noncompact: points near the
removed boundary circle escape every compact subset of the piece. -/
theorem noncompactSpace_coordDisk_compl (D : CoordDisk M) :
    NoncompactSpace ↥D.compl := by
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center
  set c : ℂ := e D.center
  set r : ℝ := D.radius
  have hr : 0 < r := D.radius_pos
  have hsub : closedBall c r ⊆ e.target := D.closedBall_subset
  have hcarrier : D.closedCarrier = e.symm '' closedBall c r := rfl
  have hcompl : (D.compl : Set M) = D.closedCarrierᶜ := rfl
  -- A collar radius: a slightly larger open chart ball still inside the target.
  obtain ⟨δ, hδ0, hδsub⟩ :=
    (isCompact_closedBall c r).exists_thickening_subset_open e.open_target hsub
  set R : ℝ := δ + r with hRdef
  have hrR : r < R := lt_add_of_pos_left r hδ0
  have hballR : ball c R ⊆ e.target := by
    rw [hRdef, ← thickening_closedBall hδ0 hr.le c]
    exact hδsub
  -- A collar point of the complement, at chart radius `(r + R) / 2`.
  set w₀ : ℂ := c + (((r + R) / 2 : ℝ) : ℂ) with hw₀def
  have hd₀ : dist w₀ c = (r + R) / 2 := by
    rw [hw₀def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hw₀ball : w₀ ∈ ball c R := by rw [mem_ball, hd₀]; linarith
  have hw₀t : w₀ ∈ e.target := hballR hw₀ball
  have hx₀ : e.symm w₀ ∈ D.closedCarrierᶜ := by
    intro hmem
    rw [hcarrier] at hmem
    obtain ⟨w', hw', hw'e⟩ := hmem
    have hw't : w' ∈ e.target := hsub hw'
    have h2 : e (e.symm w') = e (e.symm w₀) := by rw [hw'e]
    rw [e.right_inv hw't, e.right_inv hw₀t] at h2
    rw [h2, mem_closedBall, hd₀] at hw'
    linarith
  -- A compact piece would be clopen and nonempty, hence the whole connected
  -- surface — but the disk center is outside the piece.
  rw [← not_compactSpace_iff]
  intro hcomp
  have hK : IsCompact (D.compl : Set M) := by
    rw [isCompact_iff_compactSpace]
    exact hcomp
  have hclopen : IsClopen (D.compl : Set M) := ⟨hK.isClosed, D.compl.isOpen⟩
  have huniv : (D.compl : Set M) = Set.univ :=
    hclopen.eq_univ ⟨e.symm w₀, by rw [hcompl]; exact hx₀⟩
  have hcenter : D.center ∈ D.closedCarrier := by
    rw [hcarrier]
    exact ⟨c, mem_closedBall_self hr.le, e.left_inv (mem_chart_source ℂ D.center)⟩
  have hmem : D.center ∈ (D.compl : Set M) := huniv ▸ Set.mem_univ D.center
  rw [hcompl] at hmem
  exact hmem hcenter

/-- **Every piece is hyperbolic**: the complement of a closed coordinate disk
carries a Green's function at every pole, by the harmonic-measure estimate on
the collar between the removed circle and a pole disk. -/
theorem hasGreenFunction_coordDisk_compl (D : CoordDisk M) (p : M)
    (hp : p ∈ D.compl) : HasGreenFunction (⟨p, hp⟩ : ↥D.compl) := by
  classical
  -- ## Instances on the piece
  haveI hconnN : ConnectedSpace ↥D.compl :=
    Subtype.connectedSpace (isConnected_coordDisk_compl D)
  haveI hncpN : NoncompactSpace ↥D.compl := noncompactSpace_coordDisk_compl D
  haveI : LocallyConnectedSpace ↥D.compl := ChartedSpace.locallyConnectedSpace ℂ ↥D.compl
  set p₀ : ↥D.compl := ⟨p, hp⟩ with hp₀def
  -- ## Generic helpers
  -- Transfer of plane subharmonicity along a pointwise equality on a subdomain.
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  -- Restriction of plane subharmonicity.
  have subMono : ∀ (F : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      SubharmonicOn F W :=
    fun F U W hF hWU =>
      ⟨hF.1.mono hWU, fun c hc ρ hρ hball => hF.2 c (hWU hc) ρ hρ (hball.trans hWU)⟩
  -- Chart images as intersections with preimages, on the piece and on the base.
  have himgN : ∀ (e : OpenPartialHomeomorph ↥D.compl ℂ) (s : Set ℂ), s ⊆ e.target →
      e.symm '' s = e.source ∩ e ⁻¹' s := by
    intro e s hs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_target (hs hz), ?_⟩
      rw [Set.mem_preimage, e.right_inv (hs hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨e y, hy2, e.left_inv hy⟩
  -- Subharmonicity at a point transfers along local equality.
  have msubCongr : ∀ (f g : ↥D.compl → ℝ) (y : ↥D.compl), MSubharmonicAt f y →
      (∀ᶠ z in 𝓝 y, f z = g z) → MSubharmonicAt g y := by
    intro f g y hf hev
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hev2 : ∀ᶠ w in 𝓝 (chartAt ℂ y y),
        f ((chartAt ℂ y).symm w) = g ((chartAt ℂ y).symm w) :=
      hcont.eventually (p := fun z => f z = g z) (by rw [hyy]; exact hev)
    obtain ⟨r2, hr2, hball2⟩ := Metric.eventually_nhds_iff_ball.mp hev2
    refine ⟨min r r2, lt_min hr hr2, (ball_subset_ball (min_le_left _ _)).trans hrsub, ?_⟩
    exact transfer _ _ _ _ hsh (ball_subset_ball (min_le_left _ _))
      (fun w hw => hball2 w (ball_subset_ball (min_le_right _ _) hw))
  -- Positive scaling preserves subharmonicity at a point.
  have msubSmul : ∀ (f : ↥D.compl → ℝ) (a : ℝ), 0 ≤ a → ∀ y : ↥D.compl,
      MSubharmonicAt f y → MSubharmonicAt (fun z => a * f z) y := by
    intro f a ha y hf
    obtain ⟨r, hr, hrsub, hsh⟩ := hf
    refine ⟨r, hr, hrsub, ?_⟩
    refine ⟨continuousOn_const.mul hsh.1, ?_⟩
    intro c hc ρ hρ hcb
    have hsph : sphere c ρ ⊆ ball (chartAt ℂ y y) r :=
      sphere_subset_closedBall.trans hcb
    have hci : CircleIntegrable (f ∘ (chartAt ℂ y).symm) c ρ :=
      (hsh.1.mono hsph).circleIntegrable hρ.le
    have h1 := hsh.2 c hc ρ hρ hcb
    have h2 : Real.circleAverage (fun w => a * (f ∘ (chartAt ℂ y).symm) w) c ρ
        = a * Real.circleAverage (f ∘ (chartAt ℂ y).symm) c ρ := by
      have := Real.circleAverage_fun_smul (a := a) (f := f ∘ (chartAt ℂ y).symm)
        (c := c) (R := ρ)
      simpa [smul_eq_mul] using this
    calc a * f ((chartAt ℂ y).symm c)
        ≤ a * Real.circleAverage (f ∘ (chartAt ℂ y).symm) c ρ :=
          mul_le_mul_of_nonneg_left h1 ha
      _ = Real.circleAverage ((fun z => a * f z) ∘ (chartAt ℂ y).symm) c ρ := by
          rw [← h2]; rfl
  -- Affine images of harmonic functions are harmonic.
  have mharmAffine : ∀ (g : ↥D.compl → ℝ) (x : ↥D.compl) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y => a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ => c) =
        (fun y => a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  -- ## Constancy propagation from an interior maximum (clopen argument).
  have propagate : ∀ (Ω : Set ↥D.compl) (w : ↥D.compl → ℝ) (xm : ↥D.compl),
      IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ x ∈ Ω, w x ≤ w xm) → ∀ x ∈ Ω, w x = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {x | x ∈ Ω ∧ w x = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hmax' : ∀ y ∈ Ω, w y ≤ w x := fun y hy => (hmax y hy).trans_eq hxw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hxΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy.trans hxw⟩
    have hto : IsOpen {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro x ⟨hxΩ, hxw⟩
      have hcont : ContinuousAt w x := (hwsub x hxΩ).continuousAt
      filter_upwards [hcont.eventually_ne hxw, hΩo.mem_nhds hxΩ] with y hy hyΩ
      exact ⟨hyΩ, hy⟩
    have hsub : Ω ⊆ {x | x ∈ Ω ∧ w x = w xm} ∪ {x | x ∈ Ω ∧ w x ≠ w xm} := by
      intro x hx
      by_cases hxw : w x = w xm
      · exact Or.inl ⟨hx, hxw⟩
      · exact Or.inr ⟨hx, hxw⟩
    have hdisj : Disjoint {x | x ∈ Ω ∧ w x = w xm} {x | x ∈ Ω ∧ w x ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro x ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun x hx => (hres hx).2
  -- ## Maximum principle on a proper open subset of the piece.
  have maxPrin : ∀ (Ω : Set ↥D.compl) (w : ↥D.compl → ℝ) (m : ℝ) (Kc : Set ↥D.compl),
      IsOpen Ω → Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ x ∈ Ω, x ∉ Kc → w x ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ x ∈ Ω, w x ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ x ∈ Ω, w x ≤ w xm := by
      intro x hx
      by_cases hxK : x ∈ Kc
      · exact hxmax ⟨subset_closure hx, hxK⟩
      · exact (hout x hx hxK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun x hx => hwsub x (hCcΩ hx)) (fun x hx => hall x (hCcΩ hx))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    haveI hne : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  -- ## The collar of the removed circle
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center with he₀
  set c₀ : ℂ := e₀ D.center with hc₀
  have hρ₀pos : 0 < D.radius := D.radius_pos
  have hsub₀ : closedBall c₀ D.radius ⊆ e₀.target := D.closedBall_subset
  -- A slightly larger closed ball still inside the chart target and avoiding `p`.
  obtain ⟨ρ₁, hρ₁gt, hρ₁sub, hρ₁p⟩ : ∃ ρ₁, D.radius < ρ₁ ∧
      closedBall c₀ ρ₁ ⊆ e₀.target ∧ (p ∈ e₀.source → ρ₁ < dist (e₀ p) c₀)
          := by
    obtain ⟨δ, hδpos, hδsub⟩ :=
      (isCompact_closedBall c₀ D.radius).exists_cthickening_subset_open
        e₀.open_target hsub₀
    have hthick : ∀ ρ', D.radius < ρ' → ρ' ≤ D.radius + δ →
        closedBall c₀ ρ' ⊆ e₀.target := by
      intro ρ' _ hρ'le
      refine (closedBall_subset_closedBall hρ'le).trans ?_
      calc closedBall c₀ (D.radius + δ)
          = closedBall c₀ (δ + D.radius) := by rw [add_comm]
        _ = cthickening δ (closedBall c₀ D.radius) :=
            (cthickening_closedBall hδpos.le hρ₀pos.le c₀).symm
        _ ⊆ e₀.target := hδsub
    by_cases hps : p ∈ e₀.source
    · have hpd : D.radius < dist (e₀ p) c₀ := by
        by_contra hle
        push Not at hle
        have hmem : p ∈ D.closedCarrier := by
          refine ⟨e₀ p, ?_, e₀.left_inv hps⟩
          rwa [mem_closedBall]
        exact hp hmem
      refine ⟨min (D.radius + δ) ((D.radius + dist (e₀ p) c₀) / 2), ?_, ?_, ?_⟩
      · exact lt_min (by linarith) (by linarith)
      · exact hthick _ (lt_min (by linarith) (by linarith)) (min_le_left _ _)
      · intro _
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    · exact ⟨D.radius + δ, by linarith, hthick _ (by linarith) le_rfl,
        fun hcon => absurd hcon hps⟩
  have hρ₁pos : 0 < ρ₁ := hρ₀pos.trans hρ₁gt
  -- The compact collar on the base surface, and its preimage on the piece.
  set Ccol : Set M := e₀.symm '' (closedBall c₀ ρ₁ \ ball c₀ D.radius) with hCcol
  have hCcolcomp : IsCompact Ccol :=
    ((isCompact_closedBall c₀ ρ₁).diff isOpen_ball).image_of_continuousOn
      (e₀.continuousOn_symm.mono (Set.diff_subset.trans hρ₁sub))
  have hpCcol : p ∉ Ccol := by
    rintro ⟨w, hw, hwp⟩
    have hwt : w ∈ e₀.target := hρ₁sub hw.1
    have hpsrc : p ∈ e₀.source := hwp ▸ e₀.map_target hwt
    have hpe : e₀ p = w := by rw [← hwp, e₀.right_inv hwt]
    have h1 := hρ₁p hpsrc
    rw [hpe] at h1
    exact absurd (mem_closedBall.1 hw.1) (not_le.2 h1)
  set Chat : Set ↥D.compl := Subtype.val ⁻¹' Ccol with hChat
  have hChatcl : IsClosed Chat := hCcolcomp.isClosed.preimage continuous_subtype_val
  have hp₀Chat : p₀ ∉ Chat := hpCcol
  -- ## The pole chart and its two circles
  set eN : OpenPartialHomeomorph ↥D.compl ℂ := chartAt ℂ p₀ with heN
  set z₀ : ℂ := eN p₀ with hz₀
  have hp₀src : p₀ ∈ eN.source := by rw [heN]; exact mem_chart_source ℂ p₀
  have heNatlas : eN ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ↥D.compl := by
    rw [heN]; exact IsManifold.chart_mem_maximalAtlas p₀
  have hz₀tgt : z₀ ∈ eN.target := by rw [hz₀]; exact eN.map_source hp₀src
  have hsymz₀ : eN.symm z₀ = p₀ := by rw [hz₀]; exact eN.left_inv hp₀src
  have hpre₀ : eN.target ∩ eN.symm ⁻¹' Chatᶜ ∈ 𝓝 z₀ := by
    have h1 : ContinuousAt eN.symm z₀ := eN.continuousAt_symm hz₀tgt
    have h3 : eN.symm ⁻¹' Chatᶜ ∈ 𝓝 z₀ :=
      h1.preimage_mem_nhds (hChatcl.isOpen_compl.mem_nhds (hsymz₀ ▸ hp₀Chat))
    exact Filter.inter_mem (eN.open_target.mem_nhds hz₀tgt) h3
  obtain ⟨R, hR, hRsub⟩ := nhds_basis_closedBall.mem_iff.1 hpre₀
  have hRtgt : closedBall z₀ R ⊆ eN.target := fun z hz => (hRsub hz).1
  have hR2tgt : closedBall (chartAt ℂ p₀ p₀) (R / 2) ⊆ (chartAt ℂ p₀).target := by
    rw [← heN, ← hz₀]
    exact (closedBall_subset_closedBall (by linarith)).trans hRtgt
  -- ## The inner coordinate disk and its complementary region
  set Dp : CoordDisk ↥D.compl := ⟨p₀, R / 2, by positivity, hR2tgt⟩ with hDp
  have hDpcar : Dp.closedCarrier = eN.symm '' closedBall z₀ (R / 2) := by
    rw [hDp]
    simp only [CoordDisk.closedCarrier]
    rw [← heN, ← hz₀]
  set Wset : Set ↥D.compl := (Dp.compl : Set ↥D.compl) with hWset
  have hWdef : Wset = Dp.closedCarrierᶜ := rfl
  have hWopen : IsOpen Wset := Dp.isCompact_closedCarrier.isClosed.isOpen_compl
  have hWconn : IsConnected Wset := isConnected_coordDisk_compl Dp
  have hp₀car : p₀ ∈ Dp.closedCarrier := by
    rw [hDpcar]
    exact ⟨z₀, mem_closedBall_self (by positivity), hsymz₀⟩
  have hp₀W : p₀ ∉ Wset := by
    rw [hWdef]
    exact fun hc => hc hp₀car
  have hWne : Wset ≠ Set.univ := by
    intro hcon
    apply hp₀W
    rw [hcon]
    trivial
  -- Points of the closed carrier read into the chart.
  have hcarmem : ∀ y ∈ Dp.closedCarrier, y ∈ eN.source ∧ dist (eN y) z₀ ≤ R / 2 := by
    intro y hy
    rw [hDpcar] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwt : w ∈ eN.target := hRtgt (closedBall_subset_closedBall (by linarith) hw)
    refine ⟨eN.map_target hwt, ?_⟩
    rw [eN.right_inv hwt]
    exact mem_closedBall.1 hw
  have hWmem : ∀ y : ↥D.compl, y ∈ eN.source → R / 2 < dist (eN y) z₀ → y ∈ Wset := by
    intro y hys hyd
    rw [hWdef]
    intro hy
    exact absurd (hcarmem y hy).2 (not_le.2 hyd)
  -- Detecting the pole through the chart.
  have hnep : ∀ y : ↥D.compl, y ∈ eN.source → eN y ≠ z₀ → y ≠ p₀ := by
    intro y hys hyne hcon
    rw [hcon] at hyne
    exact hyne hz₀.symm
  -- The piece is punctured at the pole away from the pole.
  have hWsub : Wset ⊆ ({p₀}ᶜ : Set ↥D.compl) := by
    intro y hy
    rw [Set.mem_compl_singleton_iff]
    intro hcon
    rw [hcon] at hy
    exact hp₀W hy
  -- The circles of radii `R/2` and `R`.
  set Γin : Set ↥D.compl := eN.symm '' sphere z₀ (R / 2) with hΓin
  set Γout : Set ↥D.compl := eN.symm '' sphere z₀ R with hΓout
  have hsphtgt : ∀ r' : ℝ, r' ≤ R → sphere z₀ r' ⊆ eN.target := fun r' hr' =>
    sphere_subset_closedBall.trans ((closedBall_subset_closedBall hr').trans hRtgt)
  have hΓincomp : IsCompact Γin :=
    (isCompact_sphere z₀ (R / 2)).image_of_continuousOn
      (eN.continuousOn_symm.mono (hsphtgt _ (by linarith)))
  have hΓoutcomp : IsCompact Γout :=
    (isCompact_sphere z₀ R).image_of_continuousOn
      (eN.continuousOn_symm.mono (hsphtgt _ le_rfl))
  have hΓinne : Γin.Nonempty :=
    (NormedSpace.sphere_nonempty.2 (by positivity)).image _
  have hΓoutne : Γout.Nonempty :=
    (NormedSpace.sphere_nonempty.2 hR.le).image _
  have hΓmem : ∀ r' : ℝ, r' ≤ R → ∀ y : ↥D.compl, y ∈ eN.source →
      dist (eN y) z₀ = r' → y ∈ eN.symm '' sphere z₀ r' := by
    intro r' hr' y hys hyd
    exact ⟨eN y, by rwa [mem_sphere], eN.left_inv hys⟩
  have hΓprop : ∀ r' : ℝ, 0 < r' → r' ≤ R → ∀ y ∈ eN.symm '' sphere z₀ r',
      y ∈ eN.source ∧ dist (eN y) z₀ = r' ∧ y ≠ p₀ := by
    intro r' hr'pos hr' y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwt : w ∈ eN.target := hsphtgt r' hr' hw
    have h1 : eN (eN.symm w) = w := eN.right_inv hwt
    have h2 : dist (eN (eN.symm w)) z₀ = r' := by rw [h1]; exact mem_sphere.1 hw
    have h3 : eN (eN.symm w) ≠ z₀ := by
      intro hcon
      rw [hcon, dist_self] at h2
      exact hr'pos.ne h2
    exact ⟨eN.map_target hwt, h2, hnep _ (eN.map_target hwt) h3⟩
  have hΓinW : Γin ⊆ ({p₀}ᶜ : Set ↥D.compl) := by
    intro y hy
    exact Set.mem_compl_singleton_iff.2 (hΓprop (R / 2) (by positivity) (by linarith) y hy).2.2
  have hΓoutW : Γout ⊆ Wset := by
    intro y hy
    obtain ⟨hys, hyd, -⟩ := hΓprop R hR le_rfl y hy
    exact hWmem y hys (by rw [hyd]; linarith)
  -- The witness point on the inner circle.
  set x₀ : ↥D.compl := eN.symm (z₀ + ((R / 2 : ℝ) : ℂ)) with hx₀def
  have hwsph : z₀ + ((R / 2 : ℝ) : ℂ) ∈ sphere z₀ (R / 2) := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hx₀Γin : x₀ ∈ Γin := ⟨z₀ + ((R / 2 : ℝ) : ℂ), hwsph, rfl⟩
  have hx₀ne : x₀ ≠ p₀ := (hΓprop (R / 2) (by positivity) (by linarith) x₀ hx₀Γin).2.2
  -- The collar sits inside the region.
  have hChatW : Chat ⊆ Wset := by
    intro y hy
    rw [hWdef]
    intro hyD
    rw [hDpcar] at hyD
    obtain ⟨w', hw', hwy⟩ := hyD
    have h1 := (hRsub (closedBall_subset_closedBall (by linarith) hw')).2
    rw [Set.mem_preimage, hwy] at h1
    exact h1 hy
  -- ## The harmonic-measure family and its envelope
  set Fam : Set (↥D.compl → ℝ) := {u | MSubharmonicOn u Wset ∧ (∀ y ∈ Wset, u y ≤ 1)
      ∧
    ∃ K : Set ↥D.compl, IsCompact K ∧ ∀ y ∈ Wset, y ∉ K → u y = 0} with hFam
  have h0Fam : (fun _ : ↥D.compl => (0 : ℝ)) ∈ Fam := by
    refine ⟨fun y _ => ?_, fun y _ => by norm_num, ∅, isCompact_empty, fun y _ _ => rfl⟩
    exact (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt
  set omeg : ↥D.compl → ℝ := fun y => sSup ((fun u => u y) '' Fam) with homeg
  have hFamne : ∀ y : ↥D.compl, ((fun u => u y) '' Fam).Nonempty :=
    fun y => ⟨0, (fun _ : ↥D.compl => (0 : ℝ)), h0Fam, rfl⟩
  have hFamBdd : ∀ y ∈ Wset, BddAbove ((fun u => u y) '' Fam) := by
    intro y hy
    refine ⟨1, ?_⟩
    rintro b ⟨u, hu, rfl⟩
    exact hu.2.1 y hy
  have homegle1 : ∀ y ∈ Wset, omeg y ≤ 1 := by
    intro y hy
    refine csSup_le (hFamne y) ?_
    rintro b ⟨u, hu, rfl⟩
    exact hu.2.1 y hy
  have homegge : ∀ y ∈ Wset, ∀ u ∈ Fam, u y ≤ omeg y :=
    fun y hy u hu => le_csSup (hFamBdd y hy) ⟨u, hu, rfl⟩
  have homegge0 : ∀ y ∈ Wset, 0 ≤ omeg y :=
    fun y hy => homegge y hy _ h0Fam
  -- Max-closure of the family.
  have hFammax : ∀ u₁ ∈ Fam, ∀ u₂ ∈ Fam, (fun y => max (u₁ y) (u₂ y)) ∈ Fam := by
    rintro u₁ ⟨hs₁, hb₁, K₁, hK₁, hz₁⟩ u₂ ⟨hs₂, hb₂, K₂, hK₂, hz₂⟩
    refine ⟨fun y hy => (hs₁ y hy).max (hs₂ y hy), fun y hy => max_le (hb₁ y hy) (hb₂ y
        hy),
      K₁ ∪ K₂, hK₁.union hK₂, ?_⟩
    intro y hy hyK
    change max (u₁ y) (u₂ y) = 0
    rw [hz₁ y hy (fun h => hyK (Or.inl h)), hz₂ y hy (fun h => hyK (Or.inr h))]
    exact max_self 0
  -- ## Perron: the envelope is harmonic on the region
  have homegHarm : MHarmonicOn omeg Wset := by
    intro x hx
    set ex : OpenPartialHomeomorph ↥D.compl ℂ := chartAt ℂ x with hex
    have hxsrc : x ∈ ex.source := by rw [hex]; exact mem_chart_source ℂ x
    have hexatlas : ex ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ↥D.compl := by
      rw [hex]; exact IsManifold.chart_mem_maximalAtlas x
    set cx : ℂ := ex x with hcx
    have hop : IsOpen (ex.target ∩ ex.symm ⁻¹' Wset) := ex.isOpen_inter_preimage_symm hWopen
    have hmem : cx ∈ ex.target ∩ ex.symm ⁻¹' Wset := by
      refine ⟨by rw [hcx]; exact ex.map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, hcx, ex.left_inv hxsrc]
      exact hx
    obtain ⟨ρb, hρb, hρbsub⟩ := nhds_basis_closedBall.mem_iff.1 (hop.mem_nhds hmem)
    set ρ : ℝ := ρb / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρlt : ρ < ρb := by rw [hρdef]; linarith
    have hballtgt : ball cx ρb ⊆ ex.target :=
      fun w hw => (hρbsub (ball_subset_closedBall hw)).1
    have hballW : ∀ w ∈ ball cx ρb, ex.symm w ∈ Wset := by
      intro w hw
      have := (hρbsub (ball_subset_closedBall hw)).2
      rwa [Set.mem_preimage] at this
    have hcbρ : closedBall cx ρ ⊆ ball cx ρb := closedBall_subset_ball hρlt
    have hsphρ : sphere cx ρ ⊆ ball cx ρb := sphere_subset_closedBall.trans hcbρ
    -- (P1) chart reading of a family member is subharmonic on the chart ball.
    have hread : ∀ u : ↥D.compl → ℝ, MSubharmonicOn u Wset →
        SubharmonicOn (u ∘ ex.symm) (ball cx ρb) := by
      intro u hu
      have hkey : ∀ w ∈ ball cx ρb, ∃ r' > 0,
          SubharmonicOn (u ∘ ex.symm) (ball w r') := by
        intro w hw
        have hwt : w ∈ ex.target := hballtgt hw
        have hwsrc : ex.symm w ∈ ex.source := ex.map_target hwt
        have hws : ex.symm w ∈ Wset := hballW w hw
        obtain ⟨r', hr', -, hsh⟩ :=
          (msubharmonicAt_iff_of_mem_maximalAtlas hexatlas hwsrc).mp (hu _ hws)
        rw [ex.right_inv hwt] at hsh
        exact ⟨r', hr', hsh⟩
      apply subharmonicOn_of_locally isOpen_ball
      · intro w hw
        obtain ⟨r', hr', hsh⟩ := hkey w hw
        exact (hsh.1.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr'))).continuousWithinAt
      · intro w hw
        obtain ⟨r', hr', hsh⟩ := hkey w hw
        refine ⟨r', hr', ?_⟩
        intro r hr0 hrr' _
        exact hsh.2 w (mem_ball_self hr') r hr0 (closedBall_subset_ball hrr')
    -- (P2) Poisson modification is monotone in the boundary data.
    have hpmono : ∀ pf qf : ℂ → ℝ, ContinuousOn pf (sphere cx ρ) →
        ContinuousOn qf (sphere cx ρ) → (∀ s ∈ sphere cx ρ, pf s ≤ qf s) →
        ∀ w ∈ ball cx ρ,
          RiemannDynamics.poissonModify pf cx ρ w ≤ RiemannDynamics.poissonModify qf cx ρ w :=
              by
      intro pf qf hpc hqc hpq w hw
      simp only [RiemannDynamics.poissonModify, if_pos hw, poissonIntegral]
      have hwlt : ‖w - cx‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hw
      have hkcont : ContinuousOn (fun s => poissonKernel cx w s) (sphere cx ρ) := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]
        apply Complex.continuous_re.comp_continuousOn
        rw [herglotzRieszKernel_fun_def]
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro s hs
        have hsn : ‖s - cx‖ = ρ := by
          rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hs)
        intro hcontra
        have : s - cx = w - cx := by linear_combination (norm := ring_nf) hcontra
        rw [this] at hsn; rw [hsn] at hwlt; linarith
      have hci_p : CircleIntegrable (fun s => poissonKernel cx w s * pf s) cx ρ :=
        (hkcont.mul hpc).circleIntegrable hρ.le
      have hci_q : CircleIntegrable (fun s => poissonKernel cx w s * qf s) cx ρ :=
        (hkcont.mul hqc).circleIntegrable hρ.le
      have hker_nn : ∀ s ∈ sphere cx |ρ|, 0 ≤ poissonKernel cx w s := by
        intro s hs
        rw [abs_of_pos hρ] at hs
        have hzc : ‖s - cx‖ = ρ := by
          rw [← dist_eq_norm]; simpa using (Metric.mem_sphere.1 hs)
        rw [poissonKernel_def]
        apply div_nonneg _ (by positivity)
        have : ‖w - cx‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwlt.le 2
        rw [hzc]; linarith
      apply Real.circleAverage_mono hci_p hci_q
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (hker_nn s hs)
      exact hpq s (by rwa [abs_of_pos hρ] at hs)
    -- Plane bound: the modification of data `≤ 1` stays `≤ 1` inside the disk.
    have hPMle1 : ∀ u : ↥D.compl → ℝ, MSubharmonicOn u Wset → (∀ y ∈ Wset, u y ≤ 1)
        →
        ∀ w ∈ ball cx ρ, RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ w ≤ 1 := by
      intro u husub hule w hw
      have hPMsub : SubharmonicOn
          (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ) (ball cx ρb) :=
        (hread u husub).poissonModify hρ hcbρ
      have hcont : ContinuousOn (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ)
          (closure (ball cx ρ)) := by
        rw [closure_ball cx hρ.ne']
        exact hPMsub.1.mono (closedBall_subset_ball hρlt)
      have hfr : ∀ ζ ∈ frontier (ball cx ρ),
          RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ ζ ≤ 1 := by
        intro ζ hζ
        rw [frontier_ball cx hρ.ne'] at hζ
        have hnb : ζ ∉ ball cx ρ := by
          rw [mem_ball, Metric.mem_sphere.1 hζ]; exact lt_irrefl _
        have h1 : RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ ζ = u (ex.symm ζ) := by
          simp only [RiemannDynamics.poissonModify, if_neg hnb]; rfl
        rw [h1]
        exact hule _ (hballW ζ (hsphρ hζ))
      exact (subMono _ _ _ hPMsub (ball_subset_ball hρlt.le)).le_of_frontier_le
        isOpen_ball isBounded_ball hcont hfr w hw
    -- (P3) the surface transplant of the Poisson modification.
    set Breg : Set ↥D.compl := ex.symm '' ball cx ρ with hBreg
    set Bcl : Set ↥D.compl := ex.symm '' closedBall cx ρ with hBcl
    have hcbtgt : closedBall cx ρ ⊆ ex.target := hcbρ.trans hballtgt
    have hBclcomp : IsCompact Bcl :=
      (isCompact_closedBall cx ρ).image_of_continuousOn (ex.continuousOn_symm.mono hcbtgt)
    have hBclW : Bcl ⊆ Wset := by
      rintro y ⟨w, hw, rfl⟩
      exact hballW w (hcbρ hw)
    have hBregBcl : Breg ⊆ Bcl := Set.image_mono ball_subset_closedBall
    set mdf : (↥D.compl → ℝ) → ↥D.compl → ℝ := fun u y =>
      if y ∈ ex.source ∧ ex y ∈ ball cx ρ then
        RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ (ex y) else u y with hmdf
    -- `mdf u = u` off the compact `Bcl`.
    have hmdfoff : ∀ u : ↥D.compl → ℝ, ∀ y : ↥D.compl, y ∉ Bcl → mdf u y = u y := by
      intro u y hy
      rw [hmdf]
      simp only
      rw [if_neg]
      rintro ⟨hys, hyb⟩
      exact hy ⟨ex y, ball_subset_closedBall hyb, ex.left_inv hys⟩
    -- Value of the transplant inside the modified region.
    have hmdfval : ∀ u : ↥D.compl → ℝ, ∀ w ∈ ball cx ρ,
        mdf u (ex.symm w) = RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ w := by
      intro u w hw
      have hwt : w ∈ ex.target := hballtgt (ball_subset_ball hρlt.le hw)
      have h1 : ex.symm w ∈ ex.source := ex.map_target hwt
      rw [hmdf]
      simp only
      rw [if_pos ⟨h1, by rwa [ex.right_inv hwt]⟩, ex.right_inv hwt]
    -- The transplant reading agrees with the plane modification.
    have hmdfread : ∀ u : ↥D.compl → ℝ, Set.EqOn (mdf u ∘ ex.symm)
        (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ) (ball cx ρb) := by
      intro u w hw
      have hwt : w ∈ ex.target := hballtgt hw
      have h1 : ex.symm w ∈ ex.source := ex.map_target hwt
      by_cases hwb : w ∈ ball cx ρ
      · exact hmdfval u w hwb
      · have h2 : mdf u (ex.symm w) = u (ex.symm w) := by
          rw [hmdf]
          simp only
          rw [if_neg]
          rintro ⟨-, hyb⟩
          rw [ex.right_inv hwt] at hyb
          exact hwb hyb
        have h3 : RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ w = u (ex.symm w) := by
          simp only [RiemannDynamics.poissonModify, if_neg hwb]; rfl
        rw [Function.comp_apply, h2, h3]
    -- Membership of the transplant in the family.
    have hmdfmem : ∀ u ∈ Fam, mdf u ∈ Fam := by
      rintro u ⟨husub, hule, Ku, hKu, hKuz⟩
      have hPMsub : SubharmonicOn
          (RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ) (ball cx ρb) :=
        (hread u husub).poissonModify hρ hcbρ
      refine ⟨?_, ?_, Ku ∪ Bcl, hKu.union hBclcomp, ?_⟩
      · -- subharmonicity of the transplant
        intro y hy
        by_cases hyB : y ∈ Bcl
        · obtain ⟨wy, hwy, rfl⟩ := hyB
          have hwyt : wy ∈ ex.target := hcbtgt hwy
          have hysrc : ex.symm wy ∈ ex.source := ex.map_target hwyt
          rw [msubharmonicAt_iff_of_mem_maximalAtlas hexatlas hysrc]
          have hwyb : ex (ex.symm wy) ∈ ball cx ρb := by
            rw [ex.right_inv hwyt]
            exact hcbρ hwy
          set r' : ℝ := ρb - dist (ex (ex.symm wy)) cx with hr'
          have hr'pos : 0 < r' := by
            rw [hr']
            have := mem_ball.1 hwyb
            linarith
          have hr'sub : ball (ex (ex.symm wy)) r' ⊆ ball cx ρb := by
            apply ball_subset_ball'
            rw [hr']
            ring_nf
            exact le_rfl
          refine ⟨r', hr'pos, hr'sub.trans hballtgt, ?_⟩
          exact transfer _ _ _ _ hPMsub hr'sub (fun w hw => (hmdfread u (hr'sub hw)).symm)
        · have hbase := husub y hy
          apply msubCongr u (mdf u) y hbase
          filter_upwards [hBclcomp.isClosed.isOpen_compl.mem_nhds hyB] with z hz
          exact (hmdfoff u z hz).symm
      · -- the transplant stays `≤ 1`
        intro y hy
        by_cases hyc : y ∈ ex.source ∧ ex y ∈ ball cx ρ
        · have h1 : mdf u y = RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ (ex y) := by
            rw [hmdf]; simp only; rw [if_pos hyc]
          rw [h1]
          exact hPMle1 u husub hule (ex y) hyc.2
        · have h1 : mdf u y = u y := by
            rw [hmdf]; simp only; rw [if_neg hyc]
          rw [h1]
          exact hule y hy
      · -- vanishing off a compact set
        intro y hy hyK
        rw [hmdfoff u y (fun h => hyK (Or.inr h))]
        exact hKuz y hy (fun h => hyK (Or.inl h))
    -- The transplant dominates the member.
    have hmdfge : ∀ u ∈ Fam, ∀ y ∈ Wset, u y ≤ mdf u y := by
      rintro u ⟨husub, -, -⟩ y hy
      by_cases hyc : y ∈ ex.source ∧ ex y ∈ ball cx ρ
      · have h1 : mdf u y = RiemannDynamics.poissonModify (u ∘ ex.symm) cx ρ (ex y) := by
          rw [hmdf]; simp only; rw [if_pos hyc]
        rw [h1]
        have h2 := poissonModify_ge (hread u husub) hρ hcbρ (ex y)
          (ball_subset_ball hρlt.le hyc.2)
        rwa [Function.comp_apply, ex.left_inv hyc.1] at h2
      · have h1 : mdf u y = u y := by rw [hmdf]; simp only; rw [if_neg hyc]
        rw [h1]
    -- (P4) running maxima.
    set rmax : (ℕ → ↥D.compl → ℝ) → ℕ → ↥D.compl → ℝ :=
      fun g => fun k => Nat.rec (g 0) (fun n acc => fun y => max (acc y) (g (n + 1) y)) k
      with hrmax
    have hrmax_mem : ∀ (g : ℕ → ↥D.compl → ℝ), (∀ n, g n ∈ Fam) →
        ∀ k, rmax g k ∈ Fam := by
      intro g hg k
      induction k with
      | zero => exact hg 0
      | succ n ih => exact hFammax _ ih _ (hg (n + 1))
    have hrmax_ge : ∀ (g : ℕ → ↥D.compl → ℝ) (k : ℕ) (y : ↥D.compl),
        g k y ≤ rmax g k y := by
      intro g k y
      cases k with
      | zero => simp [hrmax]
      | succ n => exact le_max_right _ _
    have hrmax_mono : ∀ (g : ℕ → ↥D.compl → ℝ) (y : ↥D.compl),
        Monotone (fun k => rmax g k y) := by
      intro g y
      apply monotone_nat_of_le_succ
      intro n
      exact le_max_left _ _
    have hrmax_data_mono : ∀ (g₁ g₂ : ℕ → ↥D.compl → ℝ), (∀ n y, g₁ n y ≤ g₂
        n y) →
        ∀ k y, rmax g₁ k y ≤ rmax g₂ k y := by
      intro g₁ g₂ hle k y
      induction k with
      | zero => exact hle 0 y
      | succ n ih => exact max_le_max ih (hle (n + 1) y)
    -- (P5) maximizing sequences.
    have hmaxseq : ∀ q ∈ Wset, ∃ s : ℕ → ↥D.compl → ℝ, (∀ n, s n ∈ Fam) ∧
        Tendsto (fun n => s n q) atTop (𝓝 (omeg q)) := by
      intro q hq
      obtain ⟨a, -, hatends, hamem⟩ :=
        exists_seq_tendsto_sSup (hFamne q) (hFamBdd q hq)
      have hchoose : ∀ n, ∃ v ∈ Fam, v q = a n := fun n => hamem n
      choose s hs hsval using hchoose
      refine ⟨s, hs, ?_⟩
      have : (fun n => s n q) = a := funext fun n => hsval n
      rw [this]
      exact hatends
    -- (P6) the harmonic limit construction on the chart disk.
    have hbuild : ∀ (g : ℕ → ↥D.compl → ℝ), (∀ n, g n ∈ Fam) →
        ∃ V : ℂ → ℝ, HarmonicOnNhd V (ball cx ρ) ∧
          (∀ y : ↥D.compl, y ∈ ex.source → ex y ∈ ball cx ρ →
            V (ex y) ≤ omeg y ∧ ∀ k, g k y ≤ V (ex y)) ∧
          V = fun w => ⨆ k, RiemannDynamics.poissonModify (rmax g k ∘ ex.symm) cx ρ w := by
      intro g hg
      set Vseq : ℕ → ℂ → ℝ :=
        fun k => RiemannDynamics.poissonModify (rmax g k ∘ ex.symm) cx ρ with hVseq
      have hrm_mem : ∀ k, rmax g k ∈ Fam := hrmax_mem g hg
      have hrm_read : ∀ k, SubharmonicOn (rmax g k ∘ ex.symm) (ball cx ρb) :=
        fun k => hread _ (hrm_mem k).1
      have hVharm : ∀ k, HarmonicOnNhd (Vseq k) (ball cx ρ) :=
        fun k => poissonModify_harmonicOn (hrm_read k) hρ hcbρ
      -- the plane value equals the surface transplant inside the disk
      have hVsurf : ∀ k, ∀ w ∈ ball cx ρ, Vseq k w = mdf (rmax g k) (ex.symm w) :=
        fun k w hw => (hmdfval (rmax g k) w hw).symm
      have hVle : ∀ k, ∀ w ∈ ball cx ρ, Vseq k w ≤ omeg (ex.symm w) := by
        intro k w hw
        rw [hVsurf k w hw]
        exact homegge _ (hballW w (ball_subset_ball hρlt.le hw)) _
          (hmdfmem _ (hrm_mem k))
      have hVmono : ∀ w ∈ ball cx ρ, Monotone (fun k => Vseq k w) := by
        intro w hw
        apply monotone_nat_of_le_succ
        intro k
        exact hpmono _ _ ((hrm_read k).1.mono hsphρ) ((hrm_read (k + 1)).1.mono hsphρ)
          (fun s _ => hrmax_mono g (ex.symm s) (Nat.le_succ k)) w hw
      have hVbdd : ∀ w ∈ ball cx ρ, BddAbove (Set.range fun k => Vseq k w) := by
        intro w hw
        exact ⟨omeg (ex.symm w), by rintro b ⟨k, rfl⟩; exact hVle k w hw⟩
      set V : ℂ → ℝ := fun w => ⨆ k, Vseq k w with hV
      have htends : ∀ w ∈ ball cx ρ, Tendsto (fun k => Vseq k w) atTop (𝓝 (V w)) :=
        fun w hw => tendsto_atTop_ciSup (hVmono w hw) (hVbdd w hw)
      have hbddV : ∀ w ∈ ball cx ρ, ∀ k, Vseq k w ≤ V w :=
        fun w hw k => le_ciSup (hVbdd w hw) k
      have hVlim : HarmonicOnNhd V (ball cx ρ) :=
        harmonicOnNhd_of_monotone_tendsto hVharm hVmono hbddV htends
      refine ⟨V, hVlim, ?_, rfl⟩
      intro y hysrc hyball
      have hywt : y = ex.symm (ex y) := (ex.left_inv hysrc).symm
      have hyW : y ∈ Wset := by
        rw [hywt]
        exact hballW _ (ball_subset_ball hρlt.le hyball)
      constructor
      · refine ciSup_le fun k => ?_
        have := hVle k (ex y) hyball
        rwa [← hywt] at this
      · intro k
        calc g k y ≤ rmax g k y := hrmax_ge g k y
          _ ≤ mdf (rmax g k) y := hmdfge _ (hrm_mem k) y hyW
          _ = Vseq k (ex y) := by rw [hVsurf k (ex y) hyball, ← hywt]
          _ ≤ V (ex y) := hbddV (ex y) hyball k
    -- assemble: the envelope agrees with a harmonic function near `x`.
    obtain ⟨g0, hg0mem, hg0t⟩ := hmaxseq x hx
    obtain ⟨V, hVharm, hVprop, hVeq⟩ := hbuild g0 hg0mem
    have hcxball : ex x ∈ ball cx ρ := by rw [← hcx]; exact mem_ball_self hρ
    have hVcx : V (ex x) = omeg x := by
      apply le_antisymm (hVprop x hxsrc hcxball).1
      refine le_of_tendsto_of_tendsto hg0t tendsto_const_nhds ?_
      filter_upwards with k using (hVprop x hxsrc hcxball).2 k
    have hVeqomeg : ∀ y : ↥D.compl, y ∈ ex.source → ex y ∈ ball cx ρ →
        V (ex y) = omeg y := by
      intro q hqsrc hqball
      rcases lt_or_eq_of_le (hVprop q hqsrc hqball).1 with hlt | heq
      · exfalso
        have hqW : q ∈ Wset := by
          have : q = ex.symm (ex q) := (ex.left_inv hqsrc).symm
          rw [this]
          exact hballW _ (ball_subset_ball hρlt.le hqball)
        obtain ⟨g1, hg1mem, hg1t⟩ := hmaxseq q hqW
        set gc : ℕ → ↥D.compl → ℝ := fun n y => max (g0 n y) (g1 n y) with hgc
        have hgcmem : ∀ n, gc n ∈ Fam := fun n => hFammax _ (hg0mem n) _ (hg1mem n)
        obtain ⟨Q, hQharm, hQprop, hQeq⟩ := hbuild gc hgcmem
        have hQcx : Q (ex x) = omeg x := by
          apply le_antisymm (hQprop x hxsrc hcxball).1
          refine le_of_tendsto_of_tendsto hg0t tendsto_const_nhds ?_
          filter_upwards with k using
            le_trans (le_max_left _ _) ((hQprop x hxsrc hcxball).2 k)
        have hQq : Q (ex q) = omeg q := by
          apply le_antisymm (hQprop q hqsrc hqball).1
          refine le_of_tendsto_of_tendsto hg1t tendsto_const_nhds ?_
          filter_upwards with k using
            le_trans (le_max_right _ _) ((hQprop q hqsrc hqball).2 k)
        have hQgeV : ∀ w ∈ ball cx ρ, V w ≤ Q w := by
          intro w hw
          rw [hVeq, hQeq]
          have hbdd2 : BddAbove (Set.range fun k =>
              RiemannDynamics.poissonModify (rmax gc k ∘ ex.symm) cx ρ w) := by
            refine ⟨omeg (ex.symm w), ?_⟩
            rintro b ⟨k, rfl⟩
            change RiemannDynamics.poissonModify (rmax gc k ∘ ex.symm) cx ρ w
              ≤ omeg (ex.symm w)
            rw [← hmdfval (rmax gc k) w hw]
            exact homegge _ (hballW w (ball_subset_ball hρlt.le hw)) _
              (hmdfmem _ (hrmax_mem gc hgcmem k))
          refine ciSup_mono hbdd2 fun k => ?_
          apply hpmono _ _ ((hread _ (hrmax_mem g0 hg0mem k).1).1.mono hsphρ)
            ((hread _ (hrmax_mem gc hgcmem k).1).1.mono hsphρ) _ w hw
          intro s _
          exact hrmax_data_mono g0 gc (fun n y => le_max_left _ _) k (ex.symm s)
        have hDharm : HarmonicOnNhd (fun w => Q w - V w) (ball cx ρ) := by
          have := hQharm.sub hVharm
          convert this using 1
        have hDnn : ∀ w ∈ ball cx ρ, 0 ≤ Q w - V w := fun w hw => by
          linarith [hQgeV w hw]
        have hD0 : Q (ex x) - V (ex x) = 0 := by rw [hQcx, hVcx, sub_self]
        have hzero := harmonic_eq_zero_of_nonneg_eq_zero isOpen_ball
          (convex_ball cx ρ).isPreconnected hDharm hDnn hcxball hD0
        have := hzero (ex q) hqball
        have hQV : Q (ex q) = V (ex q) := by linarith
        rw [← hQq, hQV] at hlt
        exact lt_irrefl _ hlt
      · exact heq
    -- transfer harmonicity to the envelope through the chart.
    have hev : V =ᶠ[𝓝 cx] (omeg ∘ ex.symm) := by
      have hb1 : ball cx ρ ∈ 𝓝 cx := isOpen_ball.mem_nhds (mem_ball_self hρ)
      filter_upwards [hb1] with w hw
      have hwt : w ∈ ex.target := hballtgt (ball_subset_ball hρlt.le hw)
      have h1 : ex.symm w ∈ ex.source := ex.map_target hwt
      have h2 : ex (ex.symm w) ∈ ball cx ρ := by rwa [ex.right_inv hwt]
      have := hVeqomeg (ex.symm w) h1 h2
      rw [ex.right_inv hwt] at this
      exact this
    have hgoal : HarmonicAt (omeg ∘ ex.symm) cx :=
      (harmonicAt_congr_nhds hev).mp (hVharm cx (mem_ball_self hρ))
    rw [hex, hcx] at hgoal
    exact hgoal
  -- ## The dip at the removed circle
  set a1 : ℝ := (Real.log ρ₁ - Real.log D.radius)⁻¹ with ha1
  have hloggap : 0 < Real.log ρ₁ - Real.log D.radius :=
    sub_pos.2 (Real.log_lt_log hρ₀pos hρ₁gt)
  have ha1pos : 0 < a1 := inv_pos.2 hloggap
  set hbar : ↥D.compl → ℝ :=
    fun q => a1 * (Real.log (dist (e₀ (q : M)) c₀) - Real.log D.radius) with hhbar
  -- The open annulus region between the removed circle and the enlarged circle.
  set Aann : Set ↥D.compl :=
    Subtype.val ⁻¹' (e₀.source ∩ e₀ ⁻¹' (ball c₀ ρ₁ \ closedBall c₀ D.radius))
        with hAann
  have hAannopen : IsOpen Aann :=
    (e₀.continuousOn.isOpen_inter_preimage e₀.open_source
      (isOpen_ball.sdiff isClosed_closedBall)).preimage continuous_subtype_val
  have hAannmem : ∀ y : ↥D.compl, y ∈ Aann ↔ (y : M) ∈ e₀.source ∧
      D.radius < dist (e₀ (y : M)) c₀ ∧ dist (e₀ (y : M)) c₀ < ρ₁ := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall] at h2
      exact ⟨h1, not_le.1 h2.2, h2.1⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_⟩
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall]
      exact ⟨h3, not_le.2 h2⟩
  have hAannChat : Aann ⊆ Chat := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := (hAannmem y).1 hy
    refine ⟨e₀ (y : M), ⟨mem_closedBall.2 h3.le, ?_⟩, e₀.left_inv h1⟩
    rw [mem_ball, not_lt]
    exact h2.le
  have hAannW : Aann ⊆ Wset := hAannChat.trans hChatW
  have hp₀Aann : p₀ ∉ Aann := fun h => hp₀Chat (hAannChat h)
  have hAannne : Aann ≠ Set.univ := by
    intro hcon
    apply hp₀Aann
    rw [hcon]
    trivial
  -- The collar points of the piece are never on the removed circle itself.
  have hcollarpts : ∀ y : ↥D.compl, (y : M) ∈ Ccol → (y : M) ∈ e₀.source ∧
      D.radius < dist (e₀ (y : M)) c₀ ∧ dist (e₀ (y : M)) c₀ ≤ ρ₁ := by
    rintro y ⟨w, ⟨hw1, hw2⟩, hwy⟩
    have hwt : w ∈ e₀.target := hρ₁sub hw1
    have hsrc : (y : M) ∈ e₀.source := hwy ▸ e₀.map_target hwt
    have hval : e₀ (y : M) = w := by rw [← hwy, e₀.right_inv hwt]
    have hne : D.radius < dist w c₀ := by
      rcases lt_or_eq_of_le (not_lt.1 (fun h => hw2 (mem_ball.2 h))) with h | h
      · exact h
      · exfalso
        have hyD : (y : M) ∈ D.closedCarrier :=
          ⟨w, mem_closedBall.2 h.symm.le, hwy⟩
        exact y.2 hyD
    exact ⟨hsrc, by rw [hval]; exact hne, by rw [hval]; exact mem_closedBall.1 hw1⟩
  -- Harmonicity of the annulus barrier on the piece.
  have hbarHarm : ∀ y ∈ Aann, MHarmonicAt hbar y := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := (hAannmem y).1 hy
    have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    -- the chart reading of the base coordinate is analytic
    have hTan : AnalyticAt ℂ
        (fun w => e₀ (((chartAt ℂ y).symm w : ↥D.compl) : M)) (chartAt ℂ y y) := by
      have hs1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y).symm (chartAt ℂ y y) :=
        contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas y) (mem_chart_target ℂ y)
      have hs2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun q : ↥D.compl => (q : M))
          ((chartAt ℂ y).symm (chartAt ℂ y y)) := contMDiff_subtype_val.contMDiffAt
      have hs3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e₀)
          ((((chartAt ℂ y).symm (chartAt ℂ y y) : ↥D.compl)) : M) := by
        apply contMDiffAt_of_mem_maximalAtlas (n := ω)
        · rw [he₀]; exact IsManifold.chart_mem_maximalAtlas D.center
        · rw [hyy]; exact h1
      have hs4 := (hs3.comp _ hs2).comp (chartAt ℂ y y) hs1
      exact (contMDiffAt_iff_contDiffAt.mp hs4).analyticAt
    have hne : e₀ (((chartAt ℂ y).symm (chartAt ℂ y y) : ↥D.compl) : M) - c₀ ≠ 0 := by
      rw [hyy, sub_ne_zero]
      intro hcon
      rw [hcon, dist_self] at h2
      exact absurd h2 (not_lt.2 hρ₀pos.le)
    have hlog : HarmonicAt (fun w =>
        Real.log ‖e₀ (((chartAt ℂ y).symm w : ↥D.compl) : M) - c₀‖) (chartAt ℂ y y) :=
      AnalyticAt.harmonicAt_log_norm (hTan.sub analyticAt_const) hne
    have haff := (hlog.sub (harmonicAt_const (Real.log D.radius))).const_smul (c := a1)
    have heq : (a1 • ((fun w =>
        Real.log ‖e₀ (((chartAt ℂ y).symm w : ↥D.compl) : M) - c₀‖) -
        fun _ => Real.log D.radius)) = hbar ∘ (chartAt ℂ y).symm := by
      funext w
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply, hhbar]
      rw [dist_eq_norm]
    rw [heq] at haff
    exact haff
  -- Continuity of the barrier at collar points.
  have hbarCont : ∀ y : ↥D.compl, (y : M) ∈ e₀.source → e₀ (y : M) ≠ c₀ →
      ContinuousAt hbar y := by
    intro y hys hyne
    have h0 : ContinuousAt (fun q : ↥D.compl => e₀ (q : M)) y :=
      (e₀.continuousAt hys).comp continuous_subtype_val.continuousAt
    have h1 : ContinuousAt (fun q : ↥D.compl => dist (e₀ (q : M)) c₀) y :=
      h0.dist continuousAt_const
    have h2 : dist (e₀ (y : M)) c₀ ≠ 0 := dist_ne_zero.2 hyne
    exact continuousAt_const.mul ((h1.log h2).sub continuousAt_const)
  -- Every family member dips below the barrier on the annulus.
  have hdipFam : ∀ u ∈ Fam, ∀ y ∈ Aann, u y ≤ hbar y := by
    rintro u ⟨husub, hule, Ku, hKu, hKuz⟩ y hy
    have hkey : ∀ z ∈ Aann, u z - hbar z ≤ 0 := by
      apply maxPrin Aann (fun z => u z - hbar z) 0 Ku hAannopen hAannne ?_ hKu ?_ ?_
      · -- subharmonicity of the difference
        intro z hz
        exact (husub z (hAannW hz)).sub_mharmonicAt (hbarHarm z hz)
      · -- off the compact support the barrier dominates
        intro z hz hzK
        obtain ⟨-, h2, -⟩ := (hAannmem z).1 hz
        have h3 : u z = 0 := hKuz z (hAannW hz) hzK
        have h4 : 0 ≤ hbar z := by
          rw [hhbar]
          apply mul_nonneg ha1pos.le
          rw [sub_nonneg]
          exact Real.log_le_log hρ₀pos h2.le
        linarith
      · -- boundary points lie on the enlarged circle where the barrier is `1`
        rintro z ⟨hzcl, hzA⟩
        have hzChat : z ∈ Chat := (hChatcl.closure_subset_iff.2 hAannChat) hzcl
        obtain ⟨hzsrc, hzgt, hzle⟩ := hcollarpts z hzChat
        have hzeq : dist (e₀ (z : M)) c₀ = ρ₁ := by
          rcases lt_or_eq_of_le hzle with h | h
          · exact absurd ((hAannmem z).2 ⟨hzsrc, hzgt, h⟩) hzA
          · exact h
        have hzW : z ∈ Wset := hChatW hzChat
        have hzne : e₀ (z : M) ≠ c₀ := by
          intro hcon
          rw [hcon, dist_self] at hzgt
          exact absurd hzgt (not_lt.2 hρ₀pos.le)
        refine ⟨((husub z hzW).continuousAt).sub (hbarCont z hzsrc hzne), ?_⟩
        have hb1 : hbar z = 1 := by
          rw [hhbar]
          simp only
          rw [hzeq, ha1]
          exact inv_mul_cancel₀ hloggap.ne'
        have := hule z hzW
        linarith
    have := hkey y hy
    linarith
  -- The midpoint of the annulus.
  set ρm : ℝ := (D.radius + ρ₁) / 2 with hρm
  have hρmgt : D.radius < ρm := by rw [hρm]; linarith
  have hρmlt : ρm < ρ₁ := by rw [hρm]; linarith
  have hρmpos : 0 < ρm := hρ₀pos.trans hρmgt
  have hmiddist : dist (c₀ + ((ρm : ℝ) : ℂ)) c₀ = ρm := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hρmpos.le]
  have hwmid : c₀ + ((ρm : ℝ) : ℂ) ∈ closedBall c₀ ρ₁ := by
    rw [mem_closedBall, hmiddist]
    exact hρmlt.le
  have hwtmid : c₀ + ((ρm : ℝ) : ℂ) ∈ e₀.target := hρ₁sub hwmid
  have hmidM : e₀.symm (c₀ + ((ρm : ℝ) : ℂ)) ∈ D.compl := by
    intro hcon
    obtain ⟨w', hw', hww⟩ := hcon
    have hwt' : w' ∈ e₀.target := hρ₁sub ((closedBall_subset_closedBall hρ₁gt.le) hw')
    have heq : w' = c₀ + ((ρm : ℝ) : ℂ) := by
      have := congrArg (⇑e₀) hww
      rwa [e₀.right_inv hwt', e₀.right_inv hwtmid] at this
    rw [heq] at hw'
    have h1 := mem_closedBall.1 hw'
    rw [hmiddist] at h1
    linarith
  set ymid : ↥D.compl := ⟨e₀.symm (c₀ + ((ρm : ℝ) : ℂ)), hmidM⟩ with hymid
  have hymidval : dist (e₀ ((ymid : ↥D.compl) : M)) c₀ = ρm := by
    rw [hymid]
    simp only
    rw [e₀.right_inv hwtmid, hmiddist]
  have hymidA : ymid ∈ Aann := by
    rw [hAannmem]
    refine ⟨?_, ?_, ?_⟩
    · rw [hymid]
      exact e₀.map_target hwtmid
    · rw [hymidval]; exact hρmgt
    · rw [hymidval]; exact hρmlt
  have hymidW : ymid ∈ Wset := hAannW hymidA
  set tmid : ℝ := a1 * (Real.log ρm - Real.log D.radius) with htmid
  have htmidlt : tmid < 1 := by
    rw [htmid, ha1]
    have h1 : Real.log ρm - Real.log D.radius < Real.log ρ₁ - Real.log D.radius := by
      have := Real.log_lt_log hρmpos hρmlt
      linarith
    calc (Real.log ρ₁ - Real.log D.radius)⁻¹ * (Real.log ρm - Real.log D.radius)
        < (Real.log ρ₁ - Real.log D.radius)⁻¹ * (Real.log ρ₁ - Real.log D.radius) :=
          mul_lt_mul_of_pos_left h1 ha1pos
      _ = 1 := inv_mul_cancel₀ hloggap.ne'
  have hbarmid : hbar ymid = tmid := by
    rw [hhbar, htmid]
    simp only
    rw [hymidval]
  have hdip : omeg ymid ≤ tmid := by
    refine csSup_le (hFamne ymid) ?_
    rintro b ⟨u, hu, rfl⟩
    have := hdipFam u hu ymid hymidA
    rwa [hbarmid] at this
  -- ## Strict bound below `1` everywhere on the region
  have homeglt1 : ∀ y ∈ Wset, omeg y < 1 := by
    intro y hy
    rcases lt_or_eq_of_le (homegle1 y hy) with hlt | heq
    · exact hlt
    exfalso
    have hmax : ∀ z ∈ Wset, omeg z ≤ omeg y := by
      intro z hz
      rw [heq]
      exact homegle1 z hz
    have hconst := propagate Wset omeg y hWopen hWconn.isPreconnected hy
      (fun z hz => (homegHarm z hz).msubharmonicAt) hmax
    have h1 : omeg ymid = omeg y := hconst ymid hymidW
    rw [heq] at h1
    have := hdip
    rw [h1] at this
    linarith
  -- The maximum of the envelope over the outer circle.
  have homegcont : ContinuousOn omeg Γout :=
    fun y hy => ((homegHarm y (hΓoutW hy)).continuousAt).continuousWithinAt
  obtain ⟨ystar, hystar, hystarmax⟩ := hΓoutcomp.exists_isMaxOn hΓoutne homegcont
  set tstar : ℝ := omeg ystar with htstar
  have htstarlt : tstar < 1 := homeglt1 ystar (hΓoutW hystar)
  set dlt : ℝ := 1 - tstar with hdlt
  have hdltpos : 0 < dlt := by rw [hdlt]; linarith
  -- ## The uniform bound on the Green family
  refine ⟨x₀, hx₀ne, ⟨max (Real.log 2 / dlt) 0, ?_⟩⟩
  rintro b ⟨v, hv, rfl⟩
  obtain ⟨hvsub, hvcont, ⟨Kv, hKvcomp, -, hKvzero⟩, Cv, hCv⟩ := hv
  -- The maxima of the candidate over the two circles.
  obtain ⟨xin, hxin, hxinmax⟩ := hΓincomp.exists_isMaxOn hΓinne
    (hvcont.mono hΓinW)
  obtain ⟨xout, hxout, hxoutmax⟩ := hΓoutcomp.exists_isMaxOn hΓoutne
    (hvcont.mono (hΓoutW.trans hWsub))
  set m : ℝ := v xin with hm
  set Mo : ℝ := v xout with hMo
  -- Continuity of the candidate at points away from the pole.
  have hvCA : ∀ y : ↥D.compl, y ≠ p₀ → ContinuousAt v y := by
    intro y hy
    exact hvcont.continuousAt
      (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hy))
  -- ### Interior bound: `v ≤ max m 0` on the region
  have hIntB : ∀ y ∈ Wset, v y ≤ max m 0 := by
    apply maxPrin Wset v (max m 0) Kv hWopen hWne (fun y hy => hvsub y (hWsub hy))
      hKvcomp
    · intro y hy hyK
      rw [hKvzero y hyK]
      exact le_max_right _ _
    · rintro y ⟨hycl, hyW⟩
      have hyD : y ∈ Dp.closedCarrier := not_not.1 (fun h => hyW h)
      obtain ⟨hysrc, hyd⟩ := hcarmem y hyD
      have hydeq : dist (eN y) z₀ = R / 2 := by
        rcases lt_or_eq_of_le hyd with h | h
        · exfalso
          have hBopen : IsOpen (eN.source ∩ eN ⁻¹' ball z₀ (R / 2)) :=
            eN.continuousOn.isOpen_inter_preimage eN.open_source isOpen_ball
          have hBsubD : eN.source ∩ eN ⁻¹' ball z₀ (R / 2) ⊆ Dp.closedCarrier := by
            rw [hDpcar, himgN eN _ ((closedBall_subset_closedBall (by linarith)).trans
              hRtgt)]
            exact Set.inter_subset_inter (subset_refl _)
              (Set.preimage_mono ball_subset_closedBall)
          have hyint : y ∈ interior Dp.closedCarrier :=
            interior_maximal hBsubD hBopen ⟨hysrc, h⟩
          rw [hWdef, closure_compl] at hycl
          exact hycl hyint
        · exact h
      have hyΓ : y ∈ Γin := hΓmem (R / 2) (by linarith) y hysrc hydeq
      have hyne : y ≠ p₀ := (hΓprop (R / 2) (by positivity) (by linarith) y hyΓ).2.2
      exact ⟨hvCA y hyne, le_trans (hxinmax hyΓ) (le_max_left _ _)⟩
  -- ### Growth estimate: `v ≤ Mo + log 2` on the inner circle
  -- The pole bound holds on a small chart ball.
  obtain ⟨Nv, hNvnhds, hNv⟩ := (eventually_nhdsWithin_iff.mp hCv).exists_mem
  have hprev : eN.target ∩ eN.symm ⁻¹' Nv ∈ 𝓝 z₀ := by
    have h1 : ContinuousAt eN.symm z₀ := eN.continuousAt_symm hz₀tgt
    have h3 : eN.symm ⁻¹' Nv ∈ 𝓝 z₀ := h1.preimage_mem_nhds (hsymz₀ ▸ hNvnhds)
    exact Filter.inter_mem (eN.open_target.mem_nhds hz₀tgt) h3
  obtain ⟨σ₀, hσ₀pos, hσ₀sub⟩ := nhds_basis_closedBall.mem_iff.1 hprev
  have hCbound : ∀ y : ↥D.compl, y ∈ eN.source → eN y ∈ closedBall z₀ σ₀ → y ≠
      p₀ →
      v y + Real.log (dist (eN y) z₀) ≤ Cv := by
    intro y hys hyball hyne
    have h3 : eN y ∈ eN.symm ⁻¹' Nv := (hσ₀sub hyball).2
    have h4 : y ∈ Nv := by rwa [Set.mem_preimage, eN.left_inv hys] at h3
    have h5 := hNv y h4 (Set.mem_compl_singleton_iff.mpr hyne)
    have h6 : ‖poleCoord p₀ y‖ = dist (eN y) z₀ := by
      simp only [poleCoord, ← heN, ← hz₀, dist_eq_norm]
    rwa [h6] at h5
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hGrow : ∀ y ∈ Γin, v y ≤ Mo + Real.log 2 := by
    intro y hyΓ
    obtain ⟨hysrc, hydist, hyne⟩ := hΓprop (R / 2) (by positivity) (by linarith) y hyΓ
    refine le_of_forall_pos_le_add ?_
    intro ε' hε'
    set ε : ℝ := ε' / Real.log 2 with hε
    have hεpos : 0 < ε := div_pos hε' hlog2
    have hεlog : ε * Real.log 2 = ε' := by
      rw [hε]
      exact div_mul_cancel₀ ε' hlog2.ne'
    -- choice of the excision radius
    set Q : ℝ := (Mo - Cv + (1 + ε) * Real.log R) / ε with hQ
    set σ : ℝ := min (min σ₀ (R / 4)) (Real.exp Q) with hσ
    have hσpos : 0 < σ := lt_min (lt_min hσ₀pos (by positivity)) (Real.exp_pos Q)
    have hσσ₀ : σ ≤ σ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hσR4 : σ ≤ R / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) :=
            Real.log_le_log hσpos (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hεQ : ε * Q = Mo - Cv + (1 + ε) * Real.log R := by
      rw [hQ, mul_comm]
      exact div_mul_cancel₀ _ hεpos.ne'
    -- the annulus region and the competitor
    set Ωσ : Set ↥D.compl := eN.symm '' (ball z₀ R \ closedBall z₀ σ) with hΩσ
    have hΩσsub : ball z₀ R \ closedBall z₀ σ ⊆ eN.target :=
      (Set.diff_subset.trans ball_subset_closedBall).trans hRtgt
    have hΩσopen : IsOpen Ωσ := by
      rw [hΩσ, himgN eN _ hΩσsub]
      exact eN.continuousOn.isOpen_inter_preimage eN.open_source
        (isOpen_ball.sdiff isClosed_closedBall)
    have hΩσmem : ∀ z ∈ Ωσ, z ∈ eN.source ∧ σ < dist (eN z) z₀ ∧ dist (eN z) z₀ <
        R := by
      intro z hz
      rw [hΩσ, himgN eN _ hΩσsub] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall] at hz2
      exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
    have hΩσmem' : ∀ z : ↥D.compl, z ∈ eN.source → σ < dist (eN z) z₀ →
        dist (eN z) z₀ < R → z ∈ Ωσ := by
      intro z hz1 hz2 hz3
      rw [hΩσ, himgN eN _ hΩσsub]
      refine ⟨hz1, ?_⟩
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall]
      exact ⟨hz3, not_le.2 hz2⟩
    have hp₀Ωσ : p₀ ∉ Ωσ := by
      intro hcon
      obtain ⟨-, h2, -⟩ := hΩσmem p₀ hcon
      rw [← hz₀, dist_self] at h2
      exact absurd h2 (not_lt.2 hσpos.le)
    have hΩσne : Ωσ ≠ Set.univ := by
      intro hcon
      apply hp₀Ωσ
      rw [hcon]
      trivial
    set Kσ : Set ↥D.compl := eN.symm '' (closedBall z₀ R \ ball z₀ σ) with hKσ
    have hKσcomp : IsCompact Kσ :=
      ((isCompact_closedBall z₀ R).diff isOpen_ball).image_of_continuousOn
        (eN.continuousOn_symm.mono (Set.diff_subset.trans hRtgt))
    have hΩσKσ : Ωσ ⊆ Kσ :=
      Set.image_mono (fun w hw => ⟨ball_subset_closedBall hw.1,
        fun h => hw.2 (ball_subset_closedBall h)⟩)
    -- harmonicity of the logarithmic barrier at annulus points
    have hbharmN : ∀ z : ↥D.compl, z ∈ eN.source → eN z ≠ z₀ →
        MHarmonicAt (fun q => Real.log (dist (eN q) z₀)) z := by
      intro z hzs hzne
      have h1 : MHarmonicAt (fun q => Real.log (dist (eN q) z₀)) z ↔
          HarmonicAt ((fun q => Real.log (dist (eN q) z₀)) ∘ eN.symm) (eN z) :=
        mharmonicAt_iff_of_mem_maximalAtlas heNatlas hzs
      rw [h1]
      have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - z₀‖) (eN z) := by
        apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - z₀)
        · exact analyticAt_id.sub analyticAt_const
        · exact sub_ne_zero.2 hzne
      have heqv : (fun w : ℂ => Real.log ‖w - z₀‖) =ᶠ[𝓝 (eN z)]
          ((fun q => Real.log (dist (eN q) z₀)) ∘ eN.symm) := by
        filter_upwards [eN.open_target.mem_nhds (eN.map_source hzs)] with w hw
        simp only [Function.comp_apply, eN.right_inv hw, dist_eq_norm]
      exact (harmonicAt_congr_nhds heqv).1 hharm
    -- continuity of the logarithmic barrier
    have hbcont : ∀ z : ↥D.compl, z ∈ eN.source → eN z ≠ z₀ →
        ContinuousAt (fun q => Real.log (dist (eN q) z₀)) z := by
      intro z hzs hzne
      have h2 : ContinuousAt eN z := eN.continuousAt hzs
      have h3 : dist (eN z) z₀ ≠ 0 := (dist_pos.2 hzne).ne'
      exact ((h2.dist continuousAt_const).log h3)
    -- the competitor and its subharmonicity
    set Wf : ↥D.compl → ℝ :=
      fun q => v q + (1 + ε) * (Real.log (dist (eN q) z₀) - Real.log R) with hWf
    have hWfsub : MSubharmonicOn Wf Ωσ := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hΩσmem z hz
      have hzne : eN z ≠ z₀ := by
        intro hcon
        rw [hcon, dist_self] at hz2
        exact absurd hz2 (not_lt.2 hσpos.le)
      have hznep : z ≠ p₀ := hnep z hz1 hzne
      have hu : MHarmonicAt
          (fun q => (-(1 + ε)) * Real.log (dist (eN q) z₀) + (1 + ε) * Real.log R) z :=
        mharmAffine _ z _ _ (hbharmN z hz1 hzne)
      have h7 := (hvsub z (Set.mem_compl_singleton_iff.mpr hznep)).sub_mharmonicAt hu
      convert h7 using 2
      rw [hWf]
      simp only
      ring
    -- boundary control
    have hWfbd : ∀ z ∈ closure Ωσ \ Ωσ, ContinuousAt Wf z ∧ Wf z ≤ Mo := by
      rintro z ⟨hzcl, hzΩ⟩
      have hzK : z ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hzcl
      obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ := hzK
      have hwt : w ∈ eN.target := hRtgt hw1
      have hzsrc : z ∈ eN.source := hwz ▸ eN.map_target hwt
      have hzval : eN z = w := by rw [← hwz, eN.right_inv hwt]
      have hzd1 : σ ≤ dist (eN z) z₀ := by
        rw [hzval]
        exact not_lt.1 (fun h => hw2 (mem_ball.2 h))
      have hzd2 : dist (eN z) z₀ ≤ R := by rw [hzval]; exact mem_closedBall.1 hw1
      have hzne : eN z ≠ z₀ := by
        intro hcon
        rw [hcon, dist_self] at hzd1
        exact absurd hzd1 (not_le.2 hσpos)
      have hznep : z ≠ p₀ := hnep z hzsrc hzne
      have hcont : ContinuousAt Wf z := by
        rw [hWf]
        exact (hvCA z hznep).add
          (continuousAt_const.mul ((hbcont z hzsrc hzne).sub continuousAt_const))
      refine ⟨hcont, ?_⟩
      have hdisj : dist (eN z) z₀ = σ ∨ dist (eN z) z₀ = R := by
        rcases lt_or_eq_of_le hzd1 with h1 | h1
        · rcases lt_or_eq_of_le hzd2 with h2 | h2
          · exact absurd (hΩσmem' z hzsrc h1 h2) hzΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hdisj with hzd | hzd
      · -- inner circle: the pole bound beats the barrier
        have hσball : eN z ∈ closedBall z₀ σ₀ := by
          rw [mem_closedBall, hzd]
          exact hσσ₀
        have hvz : v z + Real.log σ ≤ Cv := by
          have := hCbound z hzsrc hσball hznep
          rwa [hzd] at this
        rw [hWf]
        simp only
        rw [hzd]
        have h8 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hεpos.le
        rw [hεQ] at h8
        nlinarith only [hvz, h8]
      · -- outer circle: bounded by the outer maximum
        have hzΓ : z ∈ Γout := hΓmem R le_rfl z hzsrc hzd
        rw [hWf]
        simp only
        rw [hzd, sub_self, mul_zero, add_zero]
        exact hxoutmax hzΓ
    have hWfle : ∀ z ∈ Ωσ, Wf z ≤ Mo := by
      apply maxPrin Ωσ Wf Mo Kσ hΩσopen hΩσne hWfsub hKσcomp ?_ hWfbd
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    -- evaluate at the inner circle
    have hyΩσ : y ∈ Ωσ := by
      apply hΩσmem' y hysrc
      · rw [hydist]; linarith
      · rw [hydist]; linarith
    have h9 := hWfle y hyΩσ
    rw [hWf] at h9
    simp only at h9
    rw [hydist] at h9
    have h10 : Real.log (R / 2) = Real.log R - Real.log 2 :=
      Real.log_div hR.ne' two_ne_zero
    rw [h10] at h9
    have h11 : (1 + ε) * (Real.log R - Real.log 2 - Real.log R) = -(1 + ε) * Real.log 2 := by
      ring
    rw [h11] at h9
    have h12 : (1 + ε) * Real.log 2 = Real.log 2 + ε' := by
      rw [add_mul, one_mul, hεlog]
    linarith only [h9, h12]
  -- ### Assembly of the uniform bound
  have hvx₀ : v x₀ ≤ m := hxinmax hx₀Γin
  rcases le_or_gt m 0 with hm0 | hm0
  · exact le_trans hvx₀ (le_trans hm0 (le_max_right _ _))
  · -- the normalized candidate joins the harmonic-measure family
    have hmax0 : max m 0 = m := max_eq_left hm0.le
    set u : ↥D.compl → ℝ := fun y => m⁻¹ * v y with hu
    have humem : u ∈ Fam := by
      refine ⟨?_, ?_, Kv, hKvcomp, ?_⟩
      · intro y hy
        exact msubSmul v m⁻¹ (by positivity) y (hvsub y (hWsub hy))
      · intro y hy
        rw [hu]
        simp only
        calc m⁻¹ * v y ≤ m⁻¹ * m := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have := hIntB y hy
              rwa [hmax0] at this
          _ = 1 := inv_mul_cancel₀ hm0.ne'
      · intro y hy hyK
        rw [hu]
        simp only
        rw [hKvzero y hyK, mul_zero]
    have hvle : ∀ y ∈ Wset, v y ≤ m * omeg y := by
      intro y hy
      have h1 : u y ≤ omeg y := homegge y hy u humem
      have h2 : v y = m * u y := by
        rw [hu]
        simp only
        rw [← mul_assoc, mul_inv_cancel₀ hm0.ne', one_mul]
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hm0.le
    -- close the bootstrap
    have hMole : Mo ≤ m * tstar := by
      have h1 := hvle xout (hΓoutW hxout)
      have h2 : omeg xout ≤ tstar := hystarmax hxout
      calc Mo = v xout := rfl
        _ ≤ m * omeg xout := h1
        _ ≤ m * tstar := mul_le_mul_of_nonneg_left h2 hm0.le
    have hmle : m ≤ Mo + Real.log 2 := hGrow xin hxin
    have hkey : m * dlt ≤ Real.log 2 := by
      rw [hdlt]
      nlinarith only [hMole, hmle]
    have hmfin : m ≤ Real.log 2 / dlt := by
      rw [le_div_iff₀ hdltpos]
      exact hkey
    exact le_trans hvx₀ (le_trans hmfin (le_max_left _ _))

/-! ## Symmetry-free Harnack and normal-families infrastructure

The dipole limit below is normalized at a third base point, so the classical
cross-symmetry constant of the two piece Green's functions never enters: the
shrink-uniform control comes from the Harnack chain bound alone, and the limit
is extracted by the normal-families principle for harmonic functions. -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- The complement of two disjoint closed coordinate disks in a connected
surface is connected. -/
theorem isConnected_two_coordDisk_compl [T2Space M] [ConnectedSpace M]
    (D₁ D₂ : CoordDisk M)
    (hdisj : Disjoint D₁.closedCarrier D₂.closedCarrier) :
    IsConnected ((D₁.closedCarrier ∪ D₂.closedCarrier)ᶜ : Set M) := by
  classical
  -- ## Generic plane bricks
  -- The open chart annulus is connected, via polar coordinates.
  have hann : ∀ (c : ℂ) (r R : ℝ), 0 < r → r < R →
      IsConnected (ball c R \ closedBall c r) := by
    intro c r R hr hrR
    have hcont : Continuous fun p : ℝ × ℝ =>
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo r R ×ˢ (Set.univ : Set ℝ)) = ball c R \ closedBall c r := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨hrt, htR⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c R \ closedBall c r
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg (hr.le.trans hrt.le)]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htR
        · intro hmem
          rw [mem_closedBall, hd] at hmem
          exact absurd hmem (not_le.2 hrt)
      · rintro w ⟨hwb, hwc⟩
        have hrt : r < ‖w - c‖ := by
          rw [← dist_eq_norm]
          exact not_le.1 fun h => hwc (mem_closedBall.2 h)
        have htR : ‖w - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨hrt, htR⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    have hmid : (r + R) / 2 ∈ Set.Ioo r R := ⟨by linarith, by linarith⟩
    rw [← himg]
    exact ⟨Set.Nonempty.image _ ⟨((r + R) / 2, 0), hmid, Set.mem_univ _⟩,
      (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn⟩
  -- ## Per-disk collar data
  -- For a disk `D` and an open superset `T` of its closed chart ball inside the
  -- chart target, produce a collar radius `R` with the chart-ball neighborhood
  -- `N` of the closed carrier, the compact `K ⊇ N`, and the connected annulus
  -- `A = N ∖ closedCarrier`, all of whose points read back through the chart.
  have collar : ∀ (D : CoordDisk M) (S : Set M), IsClosed S →
      Disjoint D.closedCarrier S →
      ∃ N K A : Set M, IsOpen N ∧ IsCompact K ∧ N ⊆ K ∧ K ∩ S = ∅ ∧
        D.closedCarrier ⊆ N ∧ IsConnected A ∧ A = N \ D.closedCarrier ∧
        A ∩ D.closedCarrier = ∅ := by
    intro D S hScl hDS
    set e : OpenPartialHomeomorph M ℂ := chartAt ℂ D.center
    set c : ℂ := e D.center
    set r : ℝ := D.radius
    have hr : 0 < r := D.radius_pos
    have hsub : closedBall c r ⊆ e.target := D.closedBall_subset
    have hcarrier : D.closedCarrier = e.symm '' closedBall c r := rfl
    -- The open target region avoiding `S`.
    set T : Set ℂ := e.target ∩ e.symm ⁻¹' Sᶜ with hTdef
    have hTopen : IsOpen T := e.isOpen_inter_preimage_symm hScl.isOpen_compl
    have hTsub : closedBall c r ⊆ T := by
      intro w hw
      refine ⟨hsub hw, ?_⟩
      rw [Set.mem_preimage]
      have hmem : e.symm w ∈ D.closedCarrier := by
        rw [hcarrier]
        exact ⟨w, hw, rfl⟩
      exact fun hS => Set.disjoint_left.1 hDS hmem hS
    obtain ⟨δ, hδ0, hδsub⟩ :=
      (isCompact_closedBall c r).exists_thickening_subset_open hTopen hTsub
    set R : ℝ := δ + r with hRdef
    have hrR : r < R := lt_add_of_pos_left r hδ0
    have hballR : ball c R ⊆ T := by
      rw [hRdef, ← thickening_closedBall hδ0 hr.le c]
      exact hδsub
    have hballtgt : ball c R ⊆ e.target := fun w hw => (hballR hw).1
    -- The half-collar radius.
    set Rh : ℝ := (r + R) / 2 with hRhdef
    have hrRh : r < Rh := by rw [hRhdef]; linarith
    have hRhR : Rh < R := by rw [hRhdef]; linarith
    have hcbRh : closedBall c Rh ⊆ ball c R := closedBall_subset_ball hRhR
    -- The chart-ball neighborhood, its compact closure disk, and the annulus.
    set N : Set M := e.source ∩ e ⁻¹' ball c Rh with hNdef
    set K : Set M := e.symm '' closedBall c Rh with hKdef
    set A : Set M := e.symm '' (ball c Rh \ closedBall c r) with hAdef
    have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
    have hKcomp : IsCompact K :=
      (isCompact_closedBall c Rh).image_of_continuousOn
        (e.continuousOn_symm.mono (hcbRh.trans hballtgt))
    have hNK : N ⊆ K := by
      rintro y ⟨hys, hyb⟩
      exact ⟨e y, ball_subset_closedBall hyb, e.left_inv hys⟩
    have hKS : K ∩ S = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨w, hw, rfl⟩, hyS⟩
      have h1 := (hballR (hcbRh hw)).2
      rw [Set.mem_preimage] at h1
      exact h1 hyS
    have hcN : D.closedCarrier ⊆ N := by
      intro x hx
      rw [hcarrier] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [Set.mem_preimage, e.right_inv hwt]
      exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) hrRh)
    have hAconn : IsConnected A := by
      rw [hAdef]
      exact (hann c r Rh hr hrRh).image _
        (e.continuousOn_symm.mono fun w hw => (hcbRh.trans hballtgt)
          (ball_subset_closedBall hw.1))
    have hAeq : A = N \ D.closedCarrier := by
      rw [hAdef, hNdef, hcarrier]
      apply Set.Subset.antisymm
      · rintro x ⟨w, ⟨hwb, hwc⟩, rfl⟩
        have hwt : w ∈ e.target := (hcbRh.trans hballtgt) (ball_subset_closedBall hwb)
        refine ⟨⟨e.map_target hwt, ?_⟩, ?_⟩
        · rw [Set.mem_preimage, e.right_inv hwt]; exact hwb
        · rintro ⟨w', hw', hw'e⟩
          have hw't : w' ∈ e.target := hsub hw'
          have h2 : e (e.symm w') = e (e.symm w) := by rw [hw'e]
          rw [e.right_inv hw't, e.right_inv hwt] at h2
          exact hwc (h2 ▸ hw')
      · rintro x ⟨⟨hxsrc, hxb⟩, hxc⟩
        rw [Set.mem_preimage] at hxb
        refine ⟨e x, ⟨hxb, fun hmem => hxc ?_⟩, e.left_inv hxsrc⟩
        exact ⟨e x, hmem, e.left_inv hxsrc⟩
    have hAC : A ∩ D.closedCarrier = ∅ := by
      rw [hAeq, Set.eq_empty_iff_forall_notMem]
      rintro y ⟨⟨-, h2⟩, h3⟩
      exact h2 h3
    exact ⟨N, K, A, hNopen, hKcomp, hNK, hKS, hcN, hAconn, hAeq, hAC⟩
  -- ## The two collars, the second avoiding the first
  obtain ⟨N₁, K₁, A₁, hN₁o, hK₁c, hN₁K₁, hK₁C₂, hC₁N₁, hA₁conn, hA₁eq,
      hA₁C₁⟩ :=
    collar D₁ D₂.closedCarrier D₂.isCompact_closedCarrier.isClosed hdisj
  have hdisj₂ : Disjoint D₂.closedCarrier (D₁.closedCarrier ∪ K₁) := by
    rw [Set.disjoint_union_right]
    constructor
    · exact hdisj.symm
    · rw [Set.disjoint_left]
      intro y hy₂ hyK₁
      have : y ∈ K₁ ∩ D₂.closedCarrier := ⟨hyK₁, hy₂⟩
      rw [hK₁C₂] at this
      exact this
  obtain ⟨N₂, K₂, A₂, hN₂o, hK₂c, hN₂K₂, hK₂C₁K₁, hC₂N₂, hA₂conn,
      hA₂eq, hA₂C₂⟩ :=
    collar D₂ (D₁.closedCarrier ∪ K₁)
      (D₁.isCompact_closedCarrier.isClosed.union hK₁c.isClosed) hdisj₂
  -- Consequences of the avoidance choices.
  have hN₁C₂ : N₁ ∩ D₂.closedCarrier = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyN, hyC⟩
    have : y ∈ K₁ ∩ D₂.closedCarrier := ⟨hN₁K₁ hyN, hyC⟩
    rw [hK₁C₂] at this
    exact this
  have hN₂C₁ : N₂ ∩ D₁.closedCarrier = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyN, hyC⟩
    have : y ∈ K₂ ∩ (D₁.closedCarrier ∪ K₁) := ⟨hN₂K₂ hyN, Or.inl hyC⟩
    rw [hK₂C₁K₁] at this
    exact this
  have hN₁N₂ : N₁ ∩ N₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy₁, hy₂⟩
    have : y ∈ K₂ ∩ (D₁.closedCarrier ∪ K₁) := ⟨hN₂K₂ hy₂, Or.inr (hN₁K₁
        hy₁)⟩
    rw [hK₂C₁K₁] at this
    exact this
  -- ## Assembly
  set C : Set M := D₁.closedCarrier ∪ D₂.closedCarrier with hCdef
  have hCcl : IsClosed C :=
    (D₁.isCompact_closedCarrier.union D₂.isCompact_closedCarrier).isClosed
  have hΩo : IsOpen (Cᶜ : Set M) := hCcl.isOpen_compl
  -- The annuli sit inside the complement.
  have hA₁Ω : A₁ ⊆ (Cᶜ : Set M) := by
    intro y hy
    rintro (h | h)
    · rw [Set.eq_empty_iff_forall_notMem] at hA₁C₁
      exact hA₁C₁ y ⟨hy, h⟩
    · rw [Set.eq_empty_iff_forall_notMem] at hN₁C₂
      rw [hA₁eq] at hy
      exact hN₁C₂ y ⟨hy.1, h⟩
  have hA₂Ω : A₂ ⊆ (Cᶜ : Set M) := by
    intro y hy
    rintro (h | h)
    · rw [Set.eq_empty_iff_forall_notMem] at hN₂C₁
      rw [hA₂eq] at hy
      exact hN₂C₁ y ⟨hy.1, h⟩
    · rw [Set.eq_empty_iff_forall_notMem] at hA₂C₂
      exact hA₂C₂ y ⟨hy, h⟩
  -- The collar neighborhoods meet the complement only in the annuli.
  have hN₁Ω : N₁ ∩ (Cᶜ : Set M) ⊆ A₁ := by
    rintro y ⟨hyN, hyΩ⟩
    rw [hA₁eq]
    exact ⟨hyN, fun h => hyΩ (Or.inl h)⟩
  have hN₂Ω : N₂ ∩ (Cᶜ : Set M) ⊆ A₂ := by
    rintro y ⟨hyN, hyΩ⟩
    rw [hA₂eq]
    exact ⟨hyN, fun h => hyΩ (Or.inr h)⟩
  -- Nonemptiness of the complement.
  have hne : ((Cᶜ : Set M)).Nonempty := by
    obtain ⟨z, hz⟩ := hA₁conn.nonempty
    exact ⟨z, hA₁Ω hz⟩
  refine ⟨hne, ?_⟩
  intro u v hu hv huv hsu hsv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  -- Restrict the separation to the open complement.
  set u' : Set M := u ∩ Cᶜ with hu'def
  set v' : Set M := v ∩ Cᶜ with hv'def
  have hu'o : IsOpen u' := hu.inter hΩo
  have hv'o : IsOpen v' := hv.inter hΩo
  have hu'Ω : u' ⊆ (Cᶜ : Set M) := Set.inter_subset_right
  have hv'Ω : v' ⊆ (Cᶜ : Set M) := Set.inter_subset_right
  have hcov : (Cᶜ : Set M) ⊆ u' ∪ v' := by
    intro z hz
    rcases huv hz with h | h
    · exact Or.inl ⟨h, hz⟩
    · exact Or.inr ⟨h, hz⟩
  have hu'v' : u' ∩ v' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨⟨hzu, hzΩ⟩, hzv, -⟩
    have : z ∈ Cᶜ ∩ (u ∩ v) := ⟨hzΩ, hzu, hzv⟩
    rw [hcon] at this
    exact this
  have hu'ne : u'.Nonempty := by
    obtain ⟨z, hz₁, hz₂⟩ := hsu
    exact ⟨z, hz₂, hz₁⟩
  have hv'ne : v'.Nonempty := by
    obtain ⟨z, hz₁, hz₂⟩ := hsv
    exact ⟨z, hz₂, hz₁⟩
  -- Each connected annulus lies entirely on one side.
  have hside : ∀ A : Set M, IsConnected A → A ⊆ Cᶜ → A ⊆ u' ∨ A ⊆ v' := by
    intro A hAconn hAΩ
    rcases Set.eq_empty_or_nonempty (A ∩ v') with hv0 | hv1
    · left
      intro z hz
      rcases hcov (hAΩ hz) with h | h
      · exact h
      · exact absurd hv0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
    · rcases Set.eq_empty_or_nonempty (A ∩ u') with hu0 | hu1
      · right
        intro z hz
        rcases hcov (hAΩ hz) with h | h
        · exact absurd hu0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
        · exact h
      · exfalso
        obtain ⟨z, -, hzu, hzv⟩ := hAconn.2 u' v' hu'o hv'o
          (fun z hz => hcov (hAΩ hz)) hu1 hv1
        have : z ∈ u' ∩ v' := ⟨hzu, hzv⟩
        rw [hu'v'] at this
        exact this
  -- The centers of the disks lie in the carriers, hence in the collars.
  have hcen₁ : D₁.center ∈ N₁ := by
    apply hC₁N₁
    exact ⟨chartAt ℂ D₁.center D₁.center, mem_closedBall_self D₁.radius_pos.le,
      (chartAt ℂ D₁.center).left_inv (mem_chart_source ℂ D₁.center)⟩
  have hcen₂ : D₂.center ∈ N₂ := by
    apply hC₂N₂
    exact ⟨chartAt ℂ D₂.center D₂.center, mem_closedBall_self D₂.radius_pos.le,
      (chartAt ℂ D₂.center).left_inv (mem_chart_source ℂ D₂.center)⟩
  -- A two-open-set separation of the connected surface `M` is impossible.
  have hsep : ∀ P Q : Set M, IsOpen P → IsOpen Q → Set.univ ⊆ P ∪ Q →
      P ∩ Q = ∅ → P.Nonempty → Q.Nonempty → False := by
    intro P Q hP hQ hPQ hdis hPne hQne
    obtain ⟨zp, hzp⟩ := hPne
    obtain ⟨zq, hzq⟩ := hQne
    obtain ⟨z, -, hz⟩ := isPreconnected_univ P Q hP hQ hPQ
      ⟨zp, Set.mem_univ zp, hzp⟩ ⟨zq, Set.mem_univ zq, hzq⟩
    rw [hdis] at hz
    exact hz
  -- Case split on the sides of the two annuli.
  rcases hside A₁ hA₁conn hA₁Ω with h₁u | h₁v <;>
    rcases hside A₂ hA₂conn hA₂Ω with h₂u | h₂v
  · -- both annuli on the `u'` side: `v'` separates from `u' ∪ N₁ ∪ N₂`
    refine hsep (u' ∪ (N₁ ∪ N₂)) v' (hu'o.union (hN₁o.union hN₂o)) hv'o ?_ ?_ ?_ hv'ne
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inl (Or.inr (Or.inl (hC₁N₁ h)))
        · exact Or.inl (Or.inr (Or.inr (hC₂N₂ h)))
      · rcases hcov hzC with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨(hzu | hzN | hzN), hzv⟩
      · have : z ∈ u' ∩ v' := ⟨hzu, hzv⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₁ := hN₁Ω ⟨hzN, hv'Ω hzv⟩
        have : z ∈ u' ∩ v' := ⟨h₁u hzA, hzv⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₂ := hN₂Ω ⟨hzN, hv'Ω hzv⟩
        have : z ∈ u' ∩ v' := ⟨h₂u hzA, hzv⟩
        rw [hu'v'] at this
        exact this
    · exact ⟨D₁.center, Or.inr (Or.inl hcen₁)⟩
  · -- mixed: `u' ∪ N₁` against `v' ∪ N₂`
    refine hsep (u' ∪ N₁) (v' ∪ N₂) (hu'o.union hN₁o) (hv'o.union hN₂o) ?_ ?_
      ⟨D₁.center, Or.inr hcen₁⟩ ⟨D₂.center, Or.inr hcen₂⟩
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inl (Or.inr (hC₁N₁ h))
        · exact Or.inr (Or.inr (hC₂N₂ h))
      · rcases hcov hzC with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzP, hzQ⟩
      have hzu' : z ∈ u' := by
        rcases hzP with h | h
        · exact h
        · rcases hzQ with h' | h'
          · exact h₁u (hN₁Ω ⟨h, hv'Ω h'⟩)
          · have : z ∈ N₁ ∩ N₂ := ⟨h, h'⟩
            rw [hN₁N₂] at this
            exact absurd this (Set.notMem_empty z)
      have hzv' : z ∈ v' := by
        rcases hzQ with h | h
        · exact h
        · exact h₂v (hN₂Ω ⟨h, hu'Ω hzu'⟩)
      have : z ∈ u' ∩ v' := ⟨hzu', hzv'⟩
      rw [hu'v'] at this
      exact this
  · -- mixed: `u' ∪ N₂` against `v' ∪ N₁`
    refine hsep (u' ∪ N₂) (v' ∪ N₁) (hu'o.union hN₂o) (hv'o.union hN₁o) ?_ ?_
      ⟨D₂.center, Or.inr hcen₂⟩ ⟨D₁.center, Or.inr hcen₁⟩
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inr (Or.inr (hC₁N₁ h))
        · exact Or.inl (Or.inr (hC₂N₂ h))
      · rcases hcov hzC with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzP, hzQ⟩
      have hzu' : z ∈ u' := by
        rcases hzP with h | h
        · exact h
        · rcases hzQ with h' | h'
          · exact h₂u (hN₂Ω ⟨h, hv'Ω h'⟩)
          · have : z ∈ N₁ ∩ N₂ := ⟨h', h⟩
            rw [hN₁N₂] at this
            exact absurd this (Set.notMem_empty z)
      have hzv' : z ∈ v' := by
        rcases hzQ with h | h
        · exact h
        · exact h₁v (hN₁Ω ⟨h, hu'Ω hzu'⟩)
      have : z ∈ u' ∩ v' := ⟨hzu', hzv'⟩
      rw [hu'v'] at this
      exact this
  · -- both annuli on the `v'` side: `u'` separates from `v' ∪ N₁ ∪ N₂`
    refine hsep u' (v' ∪ (N₁ ∪ N₂)) hu'o (hv'o.union (hN₁o.union hN₂o)) ?_ ?_
      hu'ne ⟨D₁.center, Or.inr (Or.inl hcen₁)⟩
    · intro z _
      by_cases hzC : z ∈ C
      · rcases hzC with h | h
        · exact Or.inr (Or.inr (Or.inl (hC₁N₁ h)))
        · exact Or.inr (Or.inr (Or.inr (hC₂N₂ h)))
      · rcases hcov hzC with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzu, (hzv | hzN | hzN)⟩
      · have : z ∈ u' ∩ v' := ⟨hzu, hzv⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₁ := hN₁Ω ⟨hzN, hu'Ω hzu⟩
        have : z ∈ u' ∩ v' := ⟨hzu, h₁v hzA⟩
        rw [hu'v'] at this
        exact this
      · have hzA : z ∈ A₂ := hN₂Ω ⟨hzN, hu'Ω hzu⟩
        have : z ∈ u' ∩ v' := ⟨hzu, h₂v hzA⟩
        rw [hu'v'] at this
        exact this

omit [T2Space M] [ConnectedSpace M] in
/-- **The Harnack chain bound**: on a connected open set, positive harmonic
functions have uniformly comparable values on any compact subset, with a
constant depending only on the compact and the domain. -/
theorem exists_harnack_chain_const {Ω : Set M} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {K : Set M} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C > 0, ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ x ∈ Ω, 0 ≤ u x) →
      ∀ x ∈ K, ∀ y ∈ K, u x ≤ C * u y := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | ⟨k₀, hk₀⟩
  · refine ⟨1, one_pos, fun u _ _ x hx => ?_⟩
    rw [hKe] at hx
    exact absurd hx (Set.notMem_empty x)
  have hk₀Ω : k₀ ∈ Ω := hKΩ hk₀
  -- Step 1: every point of `Ω` has an open Harnack neighbourhood inside `Ω` on
  -- which all admissible functions are `9`-comparable, via the chart reading
  -- and the plane Harnack inequality on a concentric chart ball.
  have key : ∀ x : M, ∃ N : Set M, IsOpen N ∧ (x ∈ Ω → x ∈ N) ∧ N ⊆ Ω ∧
      ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ z ∈ Ω, 0 ≤ u z) →
        ∀ a ∈ N, ∀ b ∈ N, u a ≤ 9 * u b := by
    intro x
    by_cases hx : x ∈ Ω
    · set e := chartAt ℂ x with he
      have hxsrc : x ∈ e.source := mem_chart_source ℂ x
      have hopen : IsOpen (e.target ∩ e.symm ⁻¹' Ω) := e.isOpen_inter_preimage_symm hΩ
      have hmem : e x ∈ e.target ∩ e.symm ⁻¹' Ω := by
        refine ⟨e.map_source hxsrc, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxsrc]
        exact hx
      obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.1 hopen _ hmem
      have hr0 : 0 < ρ / 2 := by linarith
      have h2r : ball (e x) (2 * (ρ / 2)) ⊆ e.target ∩ e.symm ⁻¹' Ω := by
        rw [show 2 * (ρ / 2) = ρ by ring]
        exact hρsub
      -- The chart reading of any admissible function is harmonic on the ball.
      have htrans : ∀ u : M → ℝ, MHarmonicOn u Ω →
          ∀ w ∈ ball (e x) (2 * (ρ / 2)), HarmonicAt (u ∘ e.symm) w := by
        intro u hu w hw
        have hwt : w ∈ e.target := (h2r hw).1
        have hws : e.symm w ∈ Ω := (h2r hw).2
        have hsrc : e.symm w ∈ e.source := e.map_target hwt
        have h1 := (mharmonicAt_iff_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x) hsrc).1 (hu _ hws)
        rwa [e.right_inv hwt] at h1
      refine ⟨e.source ∩ e ⁻¹' ball (e x) (ρ / 2),
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball,
        fun _ => ⟨hxsrc, Set.mem_preimage.2 (mem_ball_self hr0)⟩, ?_, ?_⟩
      · rintro a ⟨has, hab⟩
        have h1 : e a ∈ ball (e x) (2 * (ρ / 2)) :=
          ball_subset_ball (by linarith) (Set.mem_preimage.1 hab)
        have h2 : e.symm (e a) ∈ Ω := (h2r h1).2
        rwa [e.left_inv has] at h2
      · intro u hu hupos a ha b hb
        have hh : HarmonicOnNhd (u ∘ e.symm) (ball (e x) (2 * (ρ / 2))) :=
          fun w hw => htrans u hu w hw
        have hpos : ∀ z ∈ ball (e x) (2 * (ρ / 2)), 0 ≤ (u ∘ e.symm) z :=
          fun z hz => hupos _ (h2r hz).2
        obtain ⟨-, hup_a⟩ :=
          harnack_inequality_ball hr0 hh hpos (e a) (Set.mem_preimage.1 ha.2)
        obtain ⟨hlow_b, -⟩ :=
          harnack_inequality_ball hr0 hh hpos (e b) (Set.mem_preimage.1 hb.2)
        have hca : e.symm (e a) = a := e.left_inv ha.1
        have hcb : e.symm (e b) = b := e.left_inv hb.1
        have hcx : e.symm (e x) = x := e.left_inv hxsrc
        simp only [Function.comp_apply, hca, hcb, hcx] at hup_a hlow_b
        linarith
    · exact ⟨∅, isOpen_empty, fun h => absurd h hx, Set.empty_subset _,
        fun u _ _ a ha => absurd ha (Set.notMem_empty a)⟩
  choose N hNopen hNmem hNsub hNkey using key
  -- Step 2: two-sided comparability with the base point propagates between any
  -- two points of a Harnack neighbourhood.
  have prop : ∀ y ∈ Ω, ∀ p ∈ N y, ∀ q ∈ N y,
      (∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ z ∈ Ω, 0 ≤ u z) →
        u q ≤ C * u k₀ ∧ u k₀ ≤ C * u q) →
      ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω → (∀ z ∈ Ω, 0 ≤ u z) →
        u p ≤ C * u k₀ ∧ u k₀ ≤ C * u p := by
    intro y hy p hp q hq hgq
    obtain ⟨C, hC, hCb⟩ := hgq
    refine ⟨9 * C, by linarith, fun u hu hup => ?_⟩
    obtain ⟨h1, h2⟩ := hCb u hu hup
    have h3 := hNkey y u hu hup p hp q hq
    have h4 := hNkey y u hu hup q hq p hp
    have h5 : C * u q ≤ C * (9 * u p) := mul_le_mul_of_nonneg_left h4 hC.le
    exact ⟨by linarith, by linarith⟩
  -- Step 3 (clopen argument): every point of the preconnected set `Ω` is
  -- two-sidedly comparable to the base point.
  have main : ∀ y ∈ Ω, ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
      (∀ z ∈ Ω, 0 ≤ u z) → u y ≤ C * u k₀ ∧ u k₀ ≤ C * u y := by
    set S₁ : Set M := {z | z ∈ Ω ∧ ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
      (∀ w ∈ Ω, 0 ≤ u w) → u z ≤ C * u k₀ ∧ u k₀ ≤ C * u z} with hS₁def
    set S₂ : Set M := {z | z ∈ Ω ∧ ¬∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
      (∀ w ∈ Ω, 0 ≤ u w) → u z ≤ C * u k₀ ∧ u k₀ ≤ C * u z} with hS₂def
    have hU₁o : IsOpen (⋃ y ∈ S₁, N y) := isOpen_biUnion fun y _ => hNopen y
    have hU₂o : IsOpen (⋃ y ∈ S₂, N y) := isOpen_biUnion fun y _ => hNopen y
    have hdisj : Disjoint (⋃ y ∈ S₁, N y) (⋃ y ∈ S₂, N y) := by
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      obtain ⟨y₁, hy₁, hzy₁⟩ := Set.mem_iUnion₂.1 hz₁
      obtain ⟨y₂, hy₂, hzy₂⟩ := Set.mem_iUnion₂.1 hz₂
      obtain ⟨hy₁Ω, hy₁g⟩ := hy₁
      obtain ⟨hy₂Ω, hy₂g⟩ := hy₂
      have hzg := prop y₁ hy₁Ω z hzy₁ y₁ (hNmem y₁ hy₁Ω) hy₁g
      exact hy₂g (prop y₂ hy₂Ω y₂ (hNmem y₂ hy₂Ω) z hzy₂ hzg)
    have hcover : Ω ⊆ (⋃ y ∈ S₁, N y) ∪ ⋃ y ∈ S₂, N y := by
      intro y hy
      by_cases hgy : ∃ C, 0 < C ∧ ∀ u : M → ℝ, MHarmonicOn u Ω →
          (∀ w ∈ Ω, 0 ≤ u w) → u y ≤ C * u k₀ ∧ u k₀ ≤ C * u y
      · exact Or.inl (Set.mem_biUnion ⟨hy, hgy⟩ (hNmem y hy))
      · exact Or.inr (Set.mem_biUnion ⟨hy, hgy⟩ (hNmem y hy))
    have hne : (Ω ∩ ⋃ y ∈ S₁, N y).Nonempty := by
      refine ⟨k₀, hk₀Ω, ?_⟩
      have hk₀S : k₀ ∈ S₁ :=
        ⟨hk₀Ω, 1, one_pos, fun u _ _ =>
          ⟨le_of_eq (one_mul (u k₀)).symm, le_of_eq (one_mul (u k₀)).symm⟩⟩
      exact Set.mem_biUnion hk₀S (hNmem k₀ hk₀Ω)
    have hΩU₁ : Ω ⊆ ⋃ y ∈ S₁, N y :=
      hΩc.subset_left_of_subset_union hU₁o hU₂o hdisj hcover hne
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := Set.mem_iUnion₂.1 (hΩU₁ hy)
    obtain ⟨hy'Ω, hy'g⟩ := hy'
    exact prop y' hy'Ω y hyy' y' (hNmem y' hy'Ω) hy'g
  -- Step 4: extract a uniform constant on the compact `K` from a finite
  -- subcover by Harnack neighbourhoods.
  choose! Cc hCpos hCbd using main
  have hcov : K ⊆ ⋃ i : K, N (i : M) := fun z hz =>
    Set.mem_iUnion.2 ⟨⟨z, hz⟩, hNmem z (hKΩ hz)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => N (i : M))
    (fun _ => hNopen _) hcov
  have htne : t.Nonempty := by
    obtain ⟨i, hit, -⟩ := Set.mem_iUnion₂.1 (ht hk₀)
    exact ⟨i, hit⟩
  set B : ℝ := t.sup' htne (fun i => Cc (i : M)) with hBdef
  have hBle : ∀ i ∈ t, Cc (i : M) ≤ B :=
    fun i hi => Finset.le_sup' (fun i : K => Cc (i : M)) hi
  have hBpos : 0 < B := by
    obtain ⟨i₀, hi₀⟩ := htne
    exact lt_of_lt_of_le (hCpos _ (hKΩ i₀.2)) (hBle i₀ hi₀)
  refine ⟨81 * B * B, mul_pos (mul_pos (by norm_num) hBpos) hBpos,
    fun u hu hup x hx y hy => ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
  obtain ⟨j, hjt, hyj⟩ := Set.mem_iUnion₂.1 (ht hy)
  have hiΩ : (i : M) ∈ Ω := hKΩ i.2
  have hjΩ : (j : M) ∈ Ω := hKΩ j.2
  have h1 : u x ≤ 9 * u (i : M) := hNkey (i : M) u hu hup x hxi (i : M) (hNmem _ hiΩ)
  have h2 : u (i : M) ≤ Cc (i : M) * u k₀ := (hCbd _ hiΩ u hu hup).1
  have h3 : u k₀ ≤ Cc (j : M) * u (j : M) := (hCbd _ hjΩ u hu hup).2
  have h4 : u (j : M) ≤ 9 * u y := hNkey (j : M) u hu hup (j : M) (hNmem _ hjΩ) y hyj
  have hCi : 0 < Cc (i : M) := hCpos _ hiΩ
  have hCj : 0 < Cc (j : M) := hCpos _ hjΩ
  have hy0 : 0 ≤ u y := hup y (hKΩ hy)
  have h5 : Cc (j : M) * u (j : M) ≤ Cc (j : M) * (9 * u y) :=
    mul_le_mul_of_nonneg_left h4 hCj.le
  have h6 : u k₀ ≤ 9 * Cc (j : M) * u y := by linarith
  have h7 : Cc (i : M) * u k₀ ≤ Cc (i : M) * (9 * Cc (j : M) * u y) :=
    mul_le_mul_of_nonneg_left h6 hCi.le
  have h8 : Cc (i : M) * Cc (j : M) ≤ B * B :=
    mul_le_mul (hBle i hit) (hBle j hjt) hCj.le hBpos.le
  have h9 : Cc (i : M) * Cc (j : M) * u y ≤ B * B * u y :=
    mul_le_mul_of_nonneg_right h8 hy0
  nlinarith [h1, h2, h7, h9]

-- The heartbeat limit is raised because four analytic bricks (chart transfer,
-- Poisson-kernel Lipschitz bounds, diagonal extraction, limit harmonicity)
-- elaborate within a single declaration; each individual step is fast.
set_option maxHeartbeats 400000 in
/-- **Normal families for harmonic functions**: a locally uniformly bounded
sequence of harmonic functions on an open set of a second-countable surface
has a subsequence converging locally uniformly to a harmonic function. -/
theorem exists_mharmonicOn_limit_of_locally_bounded [SecondCountableTopology M]
    {Ω : Set M} (hΩ : IsOpen Ω) {u : ℕ → M → ℝ}
    (hu : ∀ n, MHarmonicOn (u n) Ω)
    (hb : ∀ K, IsCompact K → K ⊆ Ω → ∃ B, ∀ n, ∀ x ∈ K, |u n x| ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : M → ℝ, MHarmonicOn G Ω ∧
      ∀ K, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn (fun n => u (φ n)) G Filter.atTop K := by
  classical
  -- ### Brick 0: chart transfer.  The reading in the chart at `x` of any function
  -- harmonic on `Ω` is harmonic at every plane point of the chart image of `Ω`.
  have htransfer : ∀ (x : M) (v : M → ℝ), MHarmonicOn v Ω →
      ∀ w ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω,
        HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro x v hv w hw
    obtain ⟨hwt, hwΩ⟩ := hw
    have hwΩ' : (chartAt ℂ x).symm w ∈ Ω := hwΩ
    have hyy : (chartAt ℂ x).symm w ∈ (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
      mem_chart_source ℂ ((chartAt ℂ x).symm w)
    have htrans : AnalyticAt ℂ (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ
        x).symm) w := by
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hwt
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).symm w) :=
        contMDiffAt_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas ((chartAt ℂ x).symm w)) hyy
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
    have hmh : HarmonicAt (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        ((⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w) := hv _ hwΩ'
    have hcomp := harmonicAt_comp_analyticAt hmh htrans
    have hev : (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
        v ∘ ⇑(chartAt ℂ x).symm := by
      have hS : IsOpen ((chartAt ℂ x).target ∩
          ⇑(chartAt ℂ x).symm ⁻¹' (chartAt ℂ ((chartAt ℂ x).symm w)).source) :=
        (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ x).open_target
          (chartAt ℂ ((chartAt ℂ x).symm w)).open_source
      filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with ζ hζ
      simp only [Function.comp_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hζ.2]
    exact (harmonicAt_congr_nhds hev).mp hcomp
  -- ### Brick 1: the Poisson kernel is continuous on the circle, for interior points.
  have hKcont : ∀ (c z : ℂ) (ρ : ℝ), z ∈ ball c ρ →
      ContinuousOn (poissonKernel c z) (sphere c ρ) := by
    intro c z ρ hz
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    apply Complex.continuous_re.comp_continuousOn
    rw [herglotzRieszKernel_fun_def]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro w hw
    have hwn : ‖w - c‖ = ρ := by rw [← dist_eq_norm]; simpa using (mem_sphere.1 hw)
    have hzlt : ‖z - c‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hz
    intro hcontra
    have hwz : w - c = z - c := by linear_combination (norm := ring_nf) hcontra
    rw [hwz] at hwn
    linarith
  -- ### Brick 2: circle averages of uniformly close functions are close.
  have havg_diff : ∀ (F g : ℂ → ℝ) (c : ℂ) (ρ A : ℝ), 0 < ρ →
      ContinuousOn F (sphere c ρ) → ContinuousOn g (sphere c ρ) →
      (∀ ζ ∈ sphere c ρ, |F ζ - g ζ| ≤ A) →
      |Real.circleAverage F c ρ - Real.circleAverage g c ρ| ≤ A := by
    intro F g c ρ A hρ hF hg hbd
    have hFi : CircleIntegrable F c ρ := hF.circleIntegrable hρ.le
    have hgi : CircleIntegrable g c ρ := hg.circleIntegrable hρ.le
    have habsci : CircleIntegrable (fun ζ => |F ζ - g ζ|) c ρ :=
      ((hF.sub hg).abs).circleIntegrable hρ.le
    rw [← Real.circleAverage_fun_sub hFi hgi]
    calc |Real.circleAverage (fun ζ => F ζ - g ζ) c ρ|
        ≤ Real.circleAverage |fun ζ => F ζ - g ζ| c ρ :=
          Real.abs_circleAverage_le_circleAverage_abs
      _ ≤ A := by
          apply Real.circleAverage_mono_on_of_le_circle habsci
          intro ζ hζ
          rw [abs_of_pos hρ] at hζ
          exact hbd ζ hζ
  -- ### Brick 3: interior Lipschitz bound for bounded harmonic functions on a disk,
  -- from the Poisson representation and the kernel-difference estimate.
  have hplaneLip : ∀ (c : ℂ) (ρ B : ℝ), 0 < ρ → 0 ≤ B → ∀ h : ℂ → ℝ,
      HarmonicOnNhd h (closedBall c ρ) → (∀ ζ ∈ closedBall c ρ, |h ζ| ≤ B) →
      ∀ z ∈ ball c (ρ / 2), ∀ w ∈ ball c (ρ / 2),
        |h z - h w| ≤ 52 * B / ρ * ‖z - w‖ := by
    intro c ρ B hρ hB h hh hbd z hz w hw
    have hzball : z ∈ ball c ρ := ball_subset_ball (by linarith) hz
    have hwball : w ∈ ball c ρ := ball_subset_ball (by linarith) hw
    -- Poisson representations at the two points.
    have hrz := hh.circleAverage_poissonKernel_smul hzball
    have hrw := hh.circleAverage_poissonKernel_smul hwball
    have hrz' : Real.circleAverage (fun ζ => poissonKernel c z ζ * h ζ) c ρ = h z := by
      rw [← hrz]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    have hrw' : Real.circleAverage (fun ζ => poissonKernel c w ζ * h ζ) c ρ = h w := by
      rw [← hrw]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    -- The kernel-difference bound on the circle.
    have hker : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c z ζ - poissonKernel c w ζ| ≤ 52 / ρ * ‖z - w‖ := by
      intro ζ hζ
      have hζρ : ‖ζ - c‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hζ
      have haz : ‖z - c‖ < ρ / 2 := by rw [← dist_eq_norm]; exact mem_ball.1 hz
      have haw : ‖w - c‖ < ρ / 2 := by rw [← dist_eq_norm]; exact mem_ball.1 hw
      have haz0 : 0 ≤ ‖z - c‖ := norm_nonneg _
      have haw0 : 0 ≤ ‖w - c‖ := norm_nonneg _
      have hd0 : 0 ≤ ‖z - w‖ := norm_nonneg _
      -- distance bounds from the sphere to the interior points
      have hDz_low : ρ / 2 ≤ ‖ζ - z‖ := by
        have h1 : ‖ζ - c‖ - ‖z - c‖ ≤ ‖ζ - c - (z - c)‖ := norm_sub_norm_le _ _
        have h2 : ζ - c - (z - c) = ζ - z := by ring
        rw [h2] at h1
        linarith
      have hDw_low : ρ / 2 ≤ ‖ζ - w‖ := by
        have h1 : ‖ζ - c‖ - ‖w - c‖ ≤ ‖ζ - c - (w - c)‖ := norm_sub_norm_le _ _
        have h2 : ζ - c - (w - c) = ζ - w := by ring
        rw [h2] at h1
        linarith
      have hDz_up : ‖ζ - z‖ ≤ 3 * ρ / 2 := by
        have h1 : ‖ζ - z‖ ≤ ‖ζ - c‖ + ‖c - z‖ := by
          have h2 : ζ - z = (ζ - c) + (c - z) := by ring
          rw [h2]; exact norm_add_le _ _
        have h3 : ‖c - z‖ = ‖z - c‖ := by rw [← neg_sub, norm_neg]
        rw [h3] at h1
        linarith
      have hDw_up : ‖ζ - w‖ ≤ 3 * ρ / 2 := by
        have h1 : ‖ζ - w‖ ≤ ‖ζ - c‖ + ‖c - w‖ := by
          have h2 : ζ - w = (ζ - c) + (c - w) := by ring
          rw [h2]; exact norm_add_le _ _
        have h3 : ‖c - w‖ = ‖w - c‖ := by rw [← neg_sub, norm_neg]
        rw [h3] at h1
        linarith
      have hZW : |‖ζ - w‖ - ‖ζ - z‖| ≤ ‖z - w‖ := by
        have h1 := abs_norm_sub_norm_le (ζ - w) (ζ - z)
        have h2 : ζ - w - (ζ - z) = z - w := by ring
        rwa [h2] at h1
      have hAZW : |‖w - c‖ - ‖z - c‖| ≤ ‖z - w‖ := by
        have h1 := abs_norm_sub_norm_le (w - c) (z - c)
        have h2 : w - c - (z - c) = w - z := by ring
        rw [h2, norm_sub_rev w z] at h1
        exact h1
      have hDz0 : (0 : ℝ) < ‖ζ - z‖ := lt_of_lt_of_le (by linarith) hDz_low
      have hDw0 : (0 : ℝ) < ‖ζ - w‖ := lt_of_lt_of_le (by linarith) hDw_low
      -- the two kernels in explicit form
      have hKz : poissonKernel c z ζ = (ρ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - z‖ ^ 2 := by
        rw [poissonKernel_def, hζρ]
        congr 2
        rw [show ζ - c - (z - c) = ζ - z from by ring]
      have hKw : poissonKernel c w ζ = (ρ ^ 2 - ‖w - c‖ ^ 2) / ‖ζ - w‖ ^ 2 := by
        rw [poissonKernel_def, hζρ]
        congr 2
        rw [show ζ - c - (w - c) = ζ - w from by ring]
      -- split the difference into two boundable pieces
      have hsplit : (ρ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - z‖ ^ 2 - (ρ ^ 2 - ‖w - c‖ ^ 2) /
          ‖ζ - w‖ ^ 2
          = (ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) / (‖ζ - z‖ ^ 2 *
              ‖ζ - w‖ ^ 2)
            + (‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2 := by
        field_simp
        ring
      have haz2 : ‖z - c‖ * ‖z - c‖ ≤ ρ / 2 * (ρ / 2) := mul_self_le_mul_self haz0
          haz.le
      have hDzsq : ρ / 2 * (ρ / 2) ≤ ‖ζ - z‖ * ‖ζ - z‖ :=
        mul_self_le_mul_self (by positivity) hDz_low
      have hDwsq : ρ / 2 * (ρ / 2) ≤ ‖ζ - w‖ * ‖ζ - w‖ :=
        mul_self_le_mul_self (by positivity) hDw_low
      have h1 : |(ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) /
          (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)| ≤ 48 / ρ * ‖z - w‖ := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ‖ζ - z‖ ^ 2 * ‖ζ - w‖
            ^ 2)]
        have e1 : |ρ ^ 2 - ‖z - c‖ ^ 2| ≤ ρ ^ 2 := by
          rw [abs_of_nonneg (by linarith [haz2, sq_nonneg ρ])]
          linarith [sq_nonneg ‖z - c‖]
        have e2 : |‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2| ≤ 3 * ρ * ‖z - w‖ := by
          have h3 : ‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2
              = (‖ζ - w‖ - ‖ζ - z‖) * (‖ζ - w‖ + ‖ζ - z‖) := by ring
          rw [h3, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖ζ - w‖ + ‖ζ - z‖)]
          calc |‖ζ - w‖ - ‖ζ - z‖| * (‖ζ - w‖ + ‖ζ - z‖)
              ≤ ‖z - w‖ * (3 * ρ) := by
                apply mul_le_mul hZW (by linarith) (by linarith) hd0
            _ = 3 * ρ * ‖z - w‖ := by ring
        have e3 : ρ ^ 4 / 16 ≤ ‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2 := by
          have e3a : ρ ^ 2 / 4 ≤ ‖ζ - z‖ ^ 2 := by linarith [hDzsq]
          have e3b : ρ ^ 2 / 4 ≤ ‖ζ - w‖ ^ 2 := by linarith [hDwsq]
          calc ρ ^ 4 / 16 = ρ ^ 2 / 4 * (ρ ^ 2 / 4) := by ring
            _ ≤ ‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2 :=
                mul_le_mul e3a e3b (by positivity) (by positivity)
        calc |ρ ^ 2 - ‖z - c‖ ^ 2| * |‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2| /
            (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)
            ≤ ρ ^ 2 * (3 * ρ * ‖z - w‖) / (ρ ^ 4 / 16) := by
              apply div_le_div₀ (by positivity)
                (mul_le_mul e1 e2 (abs_nonneg _) (by positivity)) (by positivity) e3
          _ = 48 / ρ * ‖z - w‖ := by
              field_simp
              ring
      have h2 : |(‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2| ≤ 4 / ρ * ‖z - w‖ :=
          by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ‖ζ - w‖ ^ 2)]
        have e5 : |‖w - c‖ ^ 2 - ‖z - c‖ ^ 2| ≤ ρ * ‖z - w‖ := by
          have h3 : ‖w - c‖ ^ 2 - ‖z - c‖ ^ 2
              = (‖w - c‖ - ‖z - c‖) * (‖w - c‖ + ‖z - c‖) := by ring
          rw [h3, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖w - c‖ + ‖z - c‖)]
          calc |‖w - c‖ - ‖z - c‖| * (‖w - c‖ + ‖z - c‖)
              ≤ ‖z - w‖ * ρ := by
                apply mul_le_mul hAZW (by linarith) (by linarith) hd0
            _ = ρ * ‖z - w‖ := by ring
        have e6 : ρ ^ 2 / 4 ≤ ‖ζ - w‖ ^ 2 := by linarith [hDwsq]
        calc |‖w - c‖ ^ 2 - ‖z - c‖ ^ 2| / ‖ζ - w‖ ^ 2
            ≤ ρ * ‖z - w‖ / (ρ ^ 2 / 4) := by
              apply div_le_div₀ (by positivity) e5 (by positivity) e6
          _ = 4 / ρ * ‖z - w‖ := by
              field_simp
      calc |poissonKernel c z ζ - poissonKernel c w ζ|
          = |(ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) /
              (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)
              + (‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2| := by
            rw [hKz, hKw, hsplit]
        _ ≤ |(ρ ^ 2 - ‖z - c‖ ^ 2) * (‖ζ - w‖ ^ 2 - ‖ζ - z‖ ^ 2) /
              (‖ζ - z‖ ^ 2 * ‖ζ - w‖ ^ 2)|
              + |(‖w - c‖ ^ 2 - ‖z - c‖ ^ 2) / ‖ζ - w‖ ^ 2| := abs_add_le _ _
        _ ≤ 48 / ρ * ‖z - w‖ + 4 / ρ * ‖z - w‖ := add_le_add h1 h2
        _ = 52 / ρ * ‖z - w‖ := by ring
    -- assemble via the circle-average difference bound
    have hhcont : ContinuousOn h (sphere c ρ) := hh.continuousOn.mono sphere_subset_closedBall
    have hFzc : ContinuousOn (fun ζ => poissonKernel c z ζ * h ζ) (sphere c ρ) :=
      (hKcont c z ρ hzball).mul hhcont
    have hFwc : ContinuousOn (fun ζ => poissonKernel c w ζ * h ζ) (sphere c ρ) :=
      (hKcont c w ρ hwball).mul hhcont
    have hptbd : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c z ζ * h ζ - poissonKernel c w ζ * h ζ|
          ≤ 52 / ρ * ‖z - w‖ * B := by
      intro ζ hζ
      have h1 : |poissonKernel c z ζ * h ζ - poissonKernel c w ζ * h ζ|
          = |poissonKernel c z ζ - poissonKernel c w ζ| * |h ζ| := by
        rw [← sub_mul, abs_mul]
      rw [h1]
      exact mul_le_mul (hker ζ hζ) (hbd ζ (sphere_subset_closedBall hζ)) (abs_nonneg _)
        (by positivity)
    have := havg_diff _ _ c ρ (52 / ρ * ‖z - w‖ * B) hρ hFzc hFwc hptbd
    rw [hrz', hrw'] at this
    calc |h z - h w| ≤ 52 / ρ * ‖z - w‖ * B := this
      _ = 52 * B / ρ * ‖z - w‖ := by ring
  -- ### Brick 4: chart-disk data at every point of `Ω`.
  have hdata : ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω
          := by
    intro x hx
    have hTopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hΩ
    have hcT : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ω := by
      refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hx
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.isOpen_iff.1 hTopen _ hcT
    exact ⟨ρ₀ / 2, by positivity,
      (closedBall_subset_ball (by linarith)).trans hρ₀sub⟩
  -- ### The empty case.
  by_cases hne : Ω = ∅
  · refine ⟨id, strictMono_id, 0, ?_, ?_⟩
    · intro x hx
      rw [hne] at hx
      exact absurd hx (Set.notMem_empty x)
    · intro K hK hKΩ
      have hKe : K = ∅ := by
        rw [hne] at hKΩ
        exact Set.subset_eq_empty hKΩ rfl
      rw [hKe]
      exact tendstoUniformlyOn_empty
  -- ### A dense sequence in `Ω`.
  have hΩne : Ω.Nonempty := Set.nonempty_iff_ne_empty.2 hne
  have : Nonempty ↥Ω := hΩne.to_subtype
  obtain ⟨dd, hdd⟩ := TopologicalSpace.exists_dense_seq ↥Ω
  have hdΩ : ∀ j : ℕ, (dd j : M) ∈ Ω := fun j => (dd j).2
  have hdense : ∀ O : Set M, IsOpen O → (O ∩ Ω).Nonempty → ∃ j : ℕ, (dd j : M) ∈ O :=
      by
    intro O hO hOne
    obtain ⟨y, hyO, hyΩ⟩ := hOne
    have hpre : IsOpen ((↑) ⁻¹' O : Set ↥Ω) := hO.preimage continuous_subtype_val
    have hprene : ((↑) ⁻¹' O : Set ↥Ω).Nonempty := ⟨⟨y, hyΩ⟩, hyO⟩
    obtain ⟨j, hj⟩ := hdd.exists_mem_open hpre hprene
    exact ⟨j, hj⟩
  -- ### Diagonal extraction at the dense sequence, via compactness of a countable
  -- product of intervals.
  have hbdj : ∀ j : ℕ, ∃ B, ∀ n, |u n (dd j : M)| ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := hb {(dd j : M)} isCompact_singleton
      (Set.singleton_subset_iff.2 (hdΩ j))
    exact ⟨B, fun n => hB n _ rfl⟩
  choose Bd hBd using hbdj
  have hScomp : IsCompact (Set.univ.pi fun j : ℕ => Set.Icc (-(Bd j)) (Bd j)) :=
    isCompact_univ_pi fun j => isCompact_Icc
  have hmemS : ∀ n, (fun j => u n (dd j : M)) ∈
      Set.univ.pi fun j : ℕ => Set.Icc (-(Bd j)) (Bd j) := by
    intro n
    rw [Set.mem_univ_pi]
    intro j
    exact abs_le.1 (hBd j n)
  obtain ⟨a, -, φ, hφmono, hφtend⟩ := hScomp.tendsto_subseq hmemS
  have hconv : ∀ j : ℕ, Tendsto (fun n => u (φ n) (dd j : M)) atTop (𝓝 (a j)) :=
    fun j => tendsto_pi_nhds.1 hφtend j
  refine ⟨φ, hφmono, ?_⟩
  -- ### The local uniform Cauchy property.
  have hlocal : ∀ x ∈ Ω, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ y ∈ V,
        |u (φ m) y - u (φ n) y| < ε := by
    intro x hx
    obtain ⟨ρ, hρ, hsub⟩ := hdata x hx
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hsubT : closedBall (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target :=
      hsub.trans Set.inter_subset_left
    -- the compact read-back of the closed chart ball
    have hKcomp : IsCompact ((chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt ℂ x).continuousOn_symm.mono hsubT)
    have hKΩ : (chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ ⊆ Ω := by
      rintro y ⟨ζ, hζ, rfl⟩
      exact (hsub hζ).2
    obtain ⟨B, hB⟩ := hb _ hKcomp hKΩ
    have hxK : x ∈ (chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ :=
      ⟨chartAt ℂ x x, mem_closedBall_self hρ.le, (chartAt ℂ x).left_inv hxsrc⟩
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 x hxK)
    -- readings are harmonic on a neighborhood of the closed ball and bounded by B
    have hread : ∀ k : ℕ, HarmonicOnNhd (u k ∘ (chartAt ℂ x).symm)
        (closedBall (chartAt ℂ x x) ρ) :=
      fun k ζ hζ => htransfer x (u k) (hu k) ζ (hsub hζ)
    have hbound : ∀ k : ℕ, ∀ ζ ∈ closedBall (chartAt ℂ x x) ρ,
        |(u k ∘ (chartAt ℂ x).symm) ζ| ≤ B :=
      fun k ζ hζ => hB k _ ⟨ζ, hζ, rfl⟩
    -- the Lipschitz constant on the half ball
    have hlip : ∀ k : ℕ, ∀ z ∈ ball (chartAt ℂ x x) (ρ / 2),
        ∀ w ∈ ball (chartAt ℂ x x) (ρ / 2),
        |u k ((chartAt ℂ x).symm z) - u k ((chartAt ℂ x).symm w)|
          ≤ 52 * B / ρ * ‖z - w‖ :=
      fun k z hz w hw =>
        hplaneLip (chartAt ℂ x x) ρ B hρ hB0 (u k ∘ (chartAt ℂ x).symm)
          (hread k) (hbound k) z hz w hw
    -- the neighborhood
    refine ⟨(chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4),
      (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
        isOpen_ball,
      ⟨hxsrc, Set.mem_preimage.2 (mem_ball_self (by positivity : (0:ℝ) < ρ / 4))⟩,
      ?_, ?_⟩
    · intro y hy
      have h1 : chartAt ℂ x y ∈ closedBall (chartAt ℂ x x) ρ :=
        ball_subset_closedBall (ball_subset_ball (by linarith) hy.2)
      have h2 : (chartAt ℂ x).symm (chartAt ℂ x y) ∈ Ω := (hsub h1).2
      rwa [(chartAt ℂ x).left_inv hy.1] at h2
    · intro ε hε
      set L : ℝ := 52 * B / ρ with hLdef
      have hL0 : 0 ≤ L := by positivity
      set δ : ℝ := ε / (4 * (L + 1)) with hδdef
      have hδ0 : 0 < δ := by positivity
      -- finite δ/2-net of the quarter ball
      obtain ⟨t, -, htcover⟩ :=
        (isCompact_closedBall (chartAt ℂ x x) (ρ / 4)).elim_nhds_subcover
          (fun ζ => ball ζ (δ / 2)) (fun ζ _ => ball_mem_nhds ζ (by positivity))
      -- representative points of the dense sequence in each net cell
      have hchoice : ∀ ζ : ℂ, ∃ j : ℕ,
          ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
            ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))).Nonempty →
          (dd j : M) ∈ (chartAt ℂ x).source ∩
            ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
            ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2)) := by
        intro ζ
        by_cases hne2 : ((chartAt ℂ x).source ∩
            ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
            ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))).Nonempty
        · have hWopen : IsOpen ((chartAt ℂ x).source ∩
              ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
              ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))) :=
            ((chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
                isOpen_ball).inter
              ((chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
                isOpen_ball)
          obtain ⟨y, hy⟩ := hne2
          have hyΩ : y ∈ Ω := by
            have h1 : chartAt ℂ x y ∈ closedBall (chartAt ℂ x x) ρ :=
              ball_subset_closedBall (ball_subset_ball (by linarith) hy.1.2)
            have h2 : (chartAt ℂ x).symm (chartAt ℂ x y) ∈ Ω := (hsub h1).2
            rwa [(chartAt ℂ x).left_inv hy.1.1] at h2
          obtain ⟨j, hj⟩ := hdense _ hWopen ⟨y, hy, hyΩ⟩
          exact ⟨j, fun _ => hj⟩
        · exact ⟨0, fun hcon => absurd hcon hne2⟩
      choose jpt hjpt using hchoice
      -- Cauchy thresholds at the finitely many representatives
      have hCau : ∀ ζ : ℂ, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
          |u (φ m) (dd (jpt ζ) : M) - u (φ n) (dd (jpt ζ) : M)| < ε / 3 := by
        intro ζ
        have hcs : CauchySeq (fun n => u (φ n) (dd (jpt ζ) : M)) :=
          (hconv (jpt ζ)).cauchySeq
        rw [Metric.cauchySeq_iff] at hcs
        obtain ⟨N, hN⟩ := hcs (ε / 3) (by positivity)
        exact ⟨N, fun m hm n hn => by
          have := hN m hm n hn
          rwa [Real.dist_eq] at this⟩
      choose Nf hNf using hCau
      refine ⟨t.sup Nf, ?_⟩
      intro m hm n hn y hy
      -- locate `y`'s chart image in the net
      have hyQ : chartAt ℂ x y ∈ closedBall (chartAt ℂ x x) (ρ / 4) :=
        ball_subset_closedBall hy.2
      obtain ⟨ζ, hζt, hyζ⟩ := Set.mem_iUnion₂.1 (htcover hyQ)
      have hWne : ((chartAt ℂ x).source ∩
          ⇑(chartAt ℂ x) ⁻¹' ball (chartAt ℂ x x) (ρ / 4) ∩
          ((chartAt ℂ x).source ∩ ⇑(chartAt ℂ x) ⁻¹' ball ζ (δ / 2))).Nonempty :=
        ⟨y, hy, hy.1, hyζ⟩
      have hdj := hjpt ζ hWne
      -- chart images of the pair lie in the half ball, at distance < δ
      have hey : chartAt ℂ x y ∈ ball (chartAt ℂ x x) (ρ / 2) :=
        ball_subset_ball (by linarith) hy.2
      have hedj : chartAt ℂ x (dd (jpt ζ) : M) ∈ ball (chartAt ℂ x x) (ρ / 2) :=
        ball_subset_ball (by linarith) hdj.1.2
      have hdist : ‖chartAt ℂ x y - chartAt ℂ x (dd (jpt ζ) : M)‖ < δ := by
        rw [← dist_eq_norm]
        calc dist (chartAt ℂ x y) (chartAt ℂ x (dd (jpt ζ) : M))
            ≤ dist (chartAt ℂ x y) ζ + dist ζ (chartAt ℂ x (dd (jpt ζ) : M)) :=
              dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := by
              apply add_lt_add (mem_ball.1 hyζ)
              rw [dist_comm]
              exact mem_ball.1 hdj.2.2
          _ = δ := by ring
      -- three-epsilon assembly
      have hyy : (chartAt ℂ x).symm (chartAt ℂ x y) = y := (chartAt ℂ x).left_inv hy.1
      have hdd' : (chartAt ℂ x).symm (chartAt ℂ x (dd (jpt ζ) : M)) = (dd (jpt ζ) : M) :=
        (chartAt ℂ x).left_inv hdj.1.1
      have hlip_m : |u (φ m) y - u (φ m) (dd (jpt ζ) : M)| ≤ L * δ := by
        have h1 := hlip (φ m) _ hey _ hedj
        rw [hyy, hdd'] at h1
        calc |u (φ m) y - u (φ m) (dd (jpt ζ) : M)|
            ≤ L * ‖chartAt ℂ x y - chartAt ℂ x (dd (jpt ζ) : M)‖ := h1
          _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist.le hL0
      have hlip_n : |u (φ n) y - u (φ n) (dd (jpt ζ) : M)| ≤ L * δ := by
        have h1 := hlip (φ n) _ hey _ hedj
        rw [hyy, hdd'] at h1
        calc |u (φ n) y - u (φ n) (dd (jpt ζ) : M)|
            ≤ L * ‖chartAt ℂ x y - chartAt ℂ x (dd (jpt ζ) : M)‖ := h1
          _ ≤ L * δ := mul_le_mul_of_nonneg_left hdist.le hL0
      have hmid : |u (φ m) (dd (jpt ζ) : M) - u (φ n) (dd (jpt ζ) : M)| < ε / 3 :=
        hNf ζ m (le_trans (Finset.le_sup hζt) hm) n (le_trans (Finset.le_sup hζt) hn)
      have hLδ : L * δ ≤ ε / 4 := by
        rw [hδdef]
        rw [div_eq_mul_inv, ← mul_assoc]
        have h1 : L * ε * (4 * (L + 1))⁻¹ ≤ (L + 1) * ε * (4 * (L + 1))⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hε.le
          linarith
        calc L * ε * (4 * (L + 1))⁻¹ ≤ (L + 1) * ε * (4 * (L + 1))⁻¹ := h1
          _ = ε / 4 := by
            field_simp
      have hlip_n' : |u (φ n) (dd (jpt ζ) : M) - u (φ n) y| ≤ L * δ := by
        rw [abs_sub_comm]
        exact hlip_n
      have htri1 := abs_sub_le (u (φ m) y) (u (φ m) (dd (jpt ζ) : M)) (u (φ n) y)
      have htri2 := abs_sub_le (u (φ m) (dd (jpt ζ) : M)) (u (φ n) (dd (jpt ζ) : M))
        (u (φ n) y)
      linarith [htri1, htri2, hlip_m, hlip_n', hmid, hLδ]
  -- ### The pointwise limit function.
  have hGex : ∀ y ∈ Ω, ∃ l : ℝ, Tendsto (fun n => u (φ n) y) atTop (𝓝 l) := by
    intro y hy
    obtain ⟨V, -, hyV, -, hVc⟩ := hlocal y hy
    have hcs : CauchySeq (fun n => u (φ n) y) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hVc ε hε
      exact ⟨N, fun m hm n hn => by
        rw [Real.dist_eq]
        exact hN m hm n hn y hyV⟩
    exact cauchySeq_tendsto_of_complete hcs
  set G : M → ℝ := fun y =>
    if h : ∃ l : ℝ, Tendsto (fun n => u (φ n) y) atTop (𝓝 l) then h.choose else 0
    with hGdef
  have hGtend : ∀ y ∈ Ω, Tendsto (fun n => u (φ n) y) atTop (𝓝 (G y)) := by
    intro y hy
    have h := hGex y hy
    have hGy : G y = h.choose := by
      rw [hGdef]
      exact dif_pos h
    rw [hGy]
    exact h.choose_spec
  -- ### Uniform convergence on each local piece.
  have hVunif : ∀ V : Set M, V ⊆ Ω →
      (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ y ∈ V,
        |u (φ m) y - u (φ n) y| < ε) →
      TendstoUniformlyOn (fun n => u (φ n)) G atTop V := by
    intro V hVΩ hVc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hVc (ε / 2) (by positivity)
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn y hy => ?_⟩
    have h1 : Tendsto (fun m => dist (u (φ m) y) (u (φ n) y)) atTop
        (𝓝 (dist (G y) (u (φ n) y))) :=
      (hGtend y (hVΩ hy)).dist tendsto_const_nhds
    have h2 : ∀ᶠ m in atTop, dist (u (φ m) y) (u (φ n) y) ≤ ε / 2 := by
      rw [Filter.eventually_atTop]
      exact ⟨N, fun m hm => by
        rw [Real.dist_eq]
        exact (hN m hm n hn y hy).le⟩
    have h3 : dist (G y) (u (φ n) y) ≤ ε / 2 := le_of_tendsto h1 h2
    linarith
  -- ### Uniform convergence on compact subsets.
  have hKunif : ∀ K, IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn (fun n => u (φ n)) G atTop K := by
    intro K hK hKΩ
    choose V hVopen hVmem hVsub hVc using hlocal
    obtain ⟨t, hts⟩ := hK.elim_nhds_subcover' (fun x hx => V x (hKΩ hx))
      (fun x hx => (hVopen x (hKΩ hx)).mem_nhds (hVmem x (hKΩ hx)))
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, ∀ z ∈ t,
        ∀ y ∈ V (z : M) (hKΩ z.2), dist (G y) (u (φ n) y) < ε := by
      rw [Filter.eventually_all_finset]
      intro z hzt
      have h1 := hVunif (V (z : M) (hKΩ z.2)) (hVsub (z : M) (hKΩ z.2))
        (hVc (z : M) (hKΩ z.2))
      rw [Metric.tendstoUniformlyOn_iff] at h1
      exact h1 ε hε
    filter_upwards [hev] with n hn y hyK
    obtain ⟨z, hzt, hyV⟩ := Set.mem_iUnion₂.1 (hts hyK)
    exact hn z hzt y hyV
  -- ### Harmonicity of the limit, via the Poisson integral on chart disks.
  refine ⟨G, ?_, hKunif⟩
  intro x hx
  obtain ⟨ρ, hρ, hsub⟩ := hdata x hx
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hsubT : closedBall (chartAt ℂ x x) ρ ⊆ (chartAt ℂ x).target :=
    hsub.trans Set.inter_subset_left
  have hKcomp : IsCompact ((chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt ℂ x).continuousOn_symm.mono hsubT)
  have hKΩ : (chartAt ℂ x).symm '' closedBall (chartAt ℂ x x) ρ ⊆ Ω := by
    rintro y ⟨ζ, hζ, rfl⟩
    exact (hsub hζ).2
  -- readings of the subsequence, harmonic on a neighborhood of the closed ball
  have hread : ∀ n : ℕ, HarmonicOnNhd (u (φ n) ∘ (chartAt ℂ x).symm)
      (closedBall (chartAt ℂ x x) ρ) :=
    fun n ζ hζ => htransfer x (u (φ n)) (hu (φ n)) ζ (hsub hζ)
  -- uniform convergence of the readings on the closed chart ball
  have hunif : TendstoUniformlyOn (fun n => u (φ n) ∘ (chartAt ℂ x).symm)
      (G ∘ (chartAt ℂ x).symm) atTop (closedBall (chartAt ℂ x x) ρ) := by
    have h1 := (hKunif _ hKcomp hKΩ).comp (chartAt ℂ x).symm
    exact h1.mono fun ζ hζ => ⟨ζ, hζ, rfl⟩
  have hcont_n : ∀ n : ℕ, ContinuousOn (u (φ n) ∘ (chartAt ℂ x).symm)
      (closedBall (chartAt ℂ x x) ρ) :=
    fun n => (hread n).continuousOn
  have hGcont : ContinuousOn (G ∘ (chartAt ℂ x).symm) (closedBall (chartAt ℂ x x) ρ) :=
    hunif.continuousOn ((Filter.Eventually.of_forall hcont_n).frequently)
  -- the limit satisfies the Poisson identity on the open ball
  have hPI : ∀ z ∈ ball (chartAt ℂ x x) ρ,
      (G ∘ (chartAt ℂ x).symm) z
        = poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z := by
    intro z hz
    have haz : ‖z - chartAt ℂ x x‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hz
    have haz0 : 0 ≤ ‖z - chartAt ℂ x x‖ := norm_nonneg _
    set Kb : ℝ := (ρ + ‖z - chartAt ℂ x x‖) / (ρ - ‖z - chartAt ℂ x x‖) with hKbdef
    have hKb0 : 0 ≤ Kb := div_nonneg (by linarith) (by linarith)
    have hKbound : ∀ ζ ∈ sphere (chartAt ℂ x x) ρ, |poissonKernel (chartAt ℂ x x) z ζ|
        ≤ Kb := by
      intro ζ hζ
      have hup : poissonKernel (chartAt ℂ x x) z ζ ≤ Kb := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        exact re_herglotzRieszKernel_le hζ hz
      have hlo : 0 ≤ poissonKernel (chartAt ℂ x x) z ζ := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        refine le_trans ?_ (le_re_herglotzRieszKernel hζ hz)
        apply div_nonneg <;> linarith
      rw [abs_of_nonneg hlo]
      exact hup
    -- reproducing identity along the sequence
    have hrep : ∀ n : ℕ, (u (φ n) ∘ (chartAt ℂ x).symm) z
        = poissonIntegral (u (φ n) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z := by
      intro n
      have h1 := (hread n).circleAverage_poissonKernel_smul hz
      rw [← h1, poissonIntegral]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    -- convergence of the Poisson integrals
    have hlimPI : Tendsto
        (fun n => poissonIntegral (u (φ n) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z)
        atTop (𝓝 (poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hsphunif := hunif.mono sphere_subset_closedBall
      rw [Metric.tendstoUniformlyOn_iff] at hsphunif
      have hev := hsphunif (ε / (2 * (Kb + 1))) (by positivity)
      rw [Filter.eventually_atTop] at hev
      obtain ⟨N, hN⟩ := hev
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq]
      have hbd : ∀ ζ ∈ sphere (chartAt ℂ x x) ρ,
          |poissonKernel (chartAt ℂ x x) z ζ * (u (φ n) ∘ (chartAt ℂ x).symm) ζ
            - poissonKernel (chartAt ℂ x x) z ζ * (G ∘ (chartAt ℂ x).symm) ζ|
            ≤ Kb * (ε / (2 * (Kb + 1))) := by
        intro ζ hζ
        have h1 : |poissonKernel (chartAt ℂ x x) z ζ * (u (φ n) ∘ (chartAt ℂ x).symm) ζ
            - poissonKernel (chartAt ℂ x x) z ζ * (G ∘ (chartAt ℂ x).symm) ζ|
            = |poissonKernel (chartAt ℂ x x) z ζ|
              * |(u (φ n) ∘ (chartAt ℂ x).symm) ζ - (G ∘ (chartAt ℂ x).symm) ζ| := by
          rw [← mul_sub, abs_mul]
        rw [h1]
        have h2 : |(u (φ n) ∘ (chartAt ℂ x).symm) ζ - (G ∘ (chartAt ℂ x).symm) ζ|
            ≤ ε / (2 * (Kb + 1)) := by
          have h3 := hN n hn ζ hζ
          rw [Real.dist_eq, abs_sub_comm] at h3
          exact h3.le
        exact mul_le_mul (hKbound ζ hζ) h2 (abs_nonneg _) hKb0
      have hcF : ContinuousOn
          (fun ζ => poissonKernel (chartAt ℂ x x) z ζ * (u (φ n) ∘ (chartAt ℂ x).symm) ζ)
          (sphere (chartAt ℂ x x) ρ) :=
        (hKcont _ z ρ hz).mul ((hcont_n n).mono sphere_subset_closedBall)
      have hcG : ContinuousOn
          (fun ζ => poissonKernel (chartAt ℂ x x) z ζ * (G ∘ (chartAt ℂ x).symm) ζ)
          (sphere (chartAt ℂ x x) ρ) :=
        (hKcont _ z ρ hz).mul (hGcont.mono sphere_subset_closedBall)
      have hkey := havg_diff _ _ (chartAt ℂ x x) ρ (Kb * (ε / (2 * (Kb + 1)))) hρ hcF hcG hbd
      have hfin : Kb * (ε / (2 * (Kb + 1))) < ε := by
        rw [div_eq_mul_inv]
        have h4 : Kb * (ε * (2 * (Kb + 1))⁻¹) ≤ (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h5 : (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) = ε / 2 := by
          field_simp
        rw [h5] at h4
        linarith
      exact lt_of_le_of_lt hkey hfin
    -- limits agree
    have hGz : Tendsto
        (fun n => poissonIntegral (u (φ n) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ z)
        atTop (𝓝 ((G ∘ (chartAt ℂ x).symm) z)) := by
      have h1 := hunif.tendsto_at (ball_subset_closedBall hz)
      exact h1.congr hrep
    exact tendsto_nhds_unique hGz hlimPI
  -- the Poisson integral of the limit data is harmonic on the ball
  have hPharm : HarmonicOnNhd
      (poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ)
      (ball (chartAt ℂ x x) ρ) :=
    poissonIntegral_harmonicOn _ _ hρ (hGcont.mono sphere_subset_closedBall)
  have hcball : chartAt ℂ x x ∈ ball (chartAt ℂ x x) ρ := mem_ball_self hρ
  have hev : (G ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 (chartAt ℂ x x)] poissonIntegral (G ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ρ
          :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hcball) hPI
  exact (harmonicAt_congr_nhds hev).mpr (hPharm _ hcball)


/-! ## The bipolar Green's function and the dipole map -/

/-- **The drift bound for the piece Green's functions**: the two piece
Green's functions with poles `p₁` and `p₂`, evaluated at the third point
`p₃`, differ by a shrink-independent constant. The interior maximum
principle bounds each piece Green's function off a pole ball by its maximum
on the pole circle, the two-constants estimate limits the growth of that
maximum across the chart annulus, and a Harnack chain on a fixed compact
containing the pole circles and `p₃` makes the same-pole two-point
oscillations uniform in the shrink parameter; the symmetry of the Green's
function of the pieces cancels the cross terms. -/
theorem pieceGreen_drift_bound_core (D₀ : CoordDisk M) {p₁ p₂ p₃ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hp₃ : p₃ ∉ D₀.closedCarrier) (hne : p₁ ≠ p₂) (h₃₁ : p₃ ≠ p₁)
    (h₃₂ : p₃ ≠ p₂)
    (hnb : ¬ BddAbove ((fun v => v p₃) '' greenFamily p₁) ∨
      ¬ BddAbove ((fun v => v p₃) '' greenFamily p₂)) :
    ∃ t₀ C₀, 0 < t₀ ∧ t₀ ≤ 1 ∧ ∀ t (ht : 0 < t) (ht1 : t ≤ 1), t ≤ t₀ →
      |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C₀ := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Plane-side helper: transfer of subharmonicity along a pointwise equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## Constancy propagation on a preconnected open set from an interior maximum. -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ z ∈ Ω, w z ≤ w xm) → ∀ z ∈ Ω, w z = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {z | z ∈ Ω ∧ w z = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hmax' : ∀ u ∈ Ω, w u ≤ w z := fun u hu => (hmax u hu).trans_eq hzw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hzΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu.trans hzw⟩
    have hto : IsOpen {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hcont : ContinuousAt w z := (hwsub z hzΩ).continuousAt
      filter_upwards [hcont.eventually_ne hzw, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu⟩
    have hsub : Ω ⊆ {z | z ∈ Ω ∧ w z = w xm} ∪ {z | z ∈ Ω ∧ w z ≠ w xm} := by
      intro z hz
      by_cases hzw : w z = w xm
      · exact Or.inl ⟨hz, hzw⟩
      · exact Or.inr ⟨hz, hzw⟩
    have hdisj : Disjoint {z | z ∈ Ω ∧ w z = w xm} {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro z ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun z hz => (hres hz).2
  /- ## Maximum principle on an open set `Ω ≠ univ` with compact exceptional set. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ z ∈ Ω, z ∉ Kc → w z ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ z ∈ Ω, w z ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ z ∈ Ω, w z ≤ w xm := by
      intro z hz
      by_cases hzK : z ∈ Kc
      · exact hxmax ⟨subset_closure hz, hzK⟩
      · exact (hout z hz hzK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun z hz => hwsub z (hCcΩ hz)) (fun z hz => hall z (hCcΩ hz))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    haveI hne2 : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz => (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz => (hf0 _ ((hρsub hz).2)).symm
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Subharmonicity at a point transfers between the surface and an open piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnety : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnety := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnety]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnety).target :=
      e'.map_subtype_source hnety hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hnety).symm)
        (e'.subtypeRestr hnety).target := e'.subtypeRestr_symm_eqOn hnety
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnety).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw => (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw => (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnety).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnety), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnety).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have mapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## Affine images of harmonic functions are harmonic. -/
  have mharmAffine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y => a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ => c) =
        (fun y => a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  have hmemSph : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      sphere c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' sphere c s ↔ z ∈ e.source ∧ dist (e z) c = s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_sphere.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_sphere.2 hzd, e.left_inv hzs⟩
  /- ## Per-candidate interior bound ([M] (18)): a compactly supported candidate is
  bounded on an open set avoiding the inner pole disk by its inner-circle maximum. -/
  have interiorBd : ∀ (p : M) (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      ∀ (Wo : Set M), IsOpen Wo →
      ∀ (vE : M → ℝ) (KE : Set M) (m : ℝ), 0 ≤ m →
        MSubharmonicOn vE {p}ᶜ → ContinuousOn vE {p}ᶜ → IsCompact KE → KE ⊆ Wo →
        (∀ y, y ∉ KE → vE y = 0) →
        (∀ z ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (rr / 2), vE z ≤ m) →
        ∀ y ∈ Wo ∩ ((chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (rr / 2))ᶜ,
          vE y ≤ m := by
    intro p rr hrr htgt Wo hWoOpen vE KE m hm0 hvsub hvcont hKE hKEW hKE0 hcirc
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    set Dh : Set M := ep.symm '' closedBall cp (rr / 2) with hDh
    have hpsrc : p ∈ ep.source := mem_chart_source ℂ p
    have hpDh : p ∈ Dh :=
      ⟨cp, mem_closedBall_self (by linarith only [hrr]), ep.left_inv hpsrc⟩
    set Ω : Set M := Wo ∩ Dhᶜ with hΩdef
    have hDhcomp : IsCompact Dh := (isCompact_closedBall _ _).image_of_continuousOn
      (ep.continuousOn_symm.mono
        ((closedBall_subset_closedBall (by linarith only [hrr])).trans htgt))
    have hΩopen : IsOpen Ω := hWoOpen.inter hDhcomp.isClosed.isOpen_compl
    have hΩne : Ω ≠ Set.univ := by
      intro hcon
      have hpΩ : p ∈ Ω := by rw [hcon]; trivial
      exact hpΩ.2 hpDh
    have hΩp : Ω ⊆ {p}ᶜ := fun z hz => Set.mem_compl_singleton_iff.2
      (fun hcon => hz.2 (hcon ▸ hpDh))
    apply maxPrin Ω vE m KE hΩopen hΩne (fun z hz => hvsub z (hΩp hz)) hKE
    · intro z hz hzK
      rw [hKE0 z hzK]
      exact hm0
    · rintro z ⟨hzcl, hzΩ⟩
      by_cases hzW : z ∈ Wo
      · -- frontier point on the inner circle
        have hzDh : z ∈ Dh := by
          by_contra hzD
          exact hzΩ ⟨hzW, hzD⟩
        obtain ⟨w, hw, hwz⟩ := hzDh
        have hwt : w ∈ ep.target :=
          ((closedBall_subset_closedBall
            (by linarith only [hrr] : rr / 2 ≤ rr)).trans htgt) hw
        have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
        have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
        have hzle : dist (ep z) cp ≤ rr / 2 := by
          rw [hzval]
          exact mem_closedBall.1 hw
        have hzd : dist (ep z) cp = rr / 2 := by
          rcases lt_or_eq_of_le hzle with h | h
          · exfalso
            set O : Set M := ep.source ∩ ep ⁻¹' ball cp (rr / 2) with hO
            have hOopen : IsOpen O := ep.isOpen_inter_preimage isOpen_ball
            have hzO : z ∈ O := ⟨hzsrc, by rw [Set.mem_preimage]; exact mem_ball.2 h⟩
            have hOD : O ⊆ Dh := by
              rintro q ⟨hq1, hq2⟩
              rw [Set.mem_preimage] at hq2
              exact ⟨ep q, ball_subset_closedBall hq2, ep.left_inv hq1⟩
            obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hzcl O hOopen hzO
            exact hqΩ.2 (hOD hqO)
          · exact h
        have hzΓ : z ∈ ep.symm '' sphere cp (rr / 2) :=
          ⟨ep z, mem_sphere.2 hzd, ep.left_inv hzsrc⟩
        have hznp : z ≠ p := by
          intro hcon
          rw [hcon] at hzd
          rw [← hcp, dist_self] at hzd
          have : (0 : ℝ) < rr / 2 := by linarith only [hrr]
          rw [← hzd] at this
          exact lt_irrefl _ this
        refine ⟨hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.2 hznp)), ?_⟩
        exact hcirc z hzΓ
      · -- frontier point off the open set: the candidate vanishes on a neighborhood
        have hzK : z ∉ KE := fun h => hzW (hKEW h)
        have hev : vE =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [hKE.isClosed.isOpen_compl.mem_nhds hzK] with q hq
          exact hKE0 q hq
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hKE0 z hzK]
        exact hm0
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dif_pos ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dif_neg]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## The zero function belongs to every piece Green family. -/
  have zeroFam : ∀ (P : Opens M) (p : M) (hp : p ∈ P),
      (fun _ : ↥P => (0 : ℝ)) ∈ greenFamily (⟨p, hp⟩ : ↥P) := by
    intro P p hp
    haveI : Nonempty ↥P := ⟨⟨p, hp⟩⟩
    refine ⟨fun z _ => (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt,
      continuousOn_const, ⟨∅, isCompact_empty, Set.empty_ne_univ, fun z _ => rfl⟩,
      ⟨0, ?_⟩⟩
    have hcont : ContinuousAt (poleCoord (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) := by
      have h1 : ContinuousAt (chartAt ℂ (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) :=
        (chartAt ℂ (⟨p, hp⟩ : ↥P)).continuousAt (mem_chart_source ℂ _)
      exact h1.sub continuousAt_const
    have h0 : poleCoord (⟨p, hp⟩ : ↥P) (⟨p, hp⟩ : ↥P) = 0 := sub_self _
    have hev : ∀ᶠ z in 𝓝 (⟨p, hp⟩ : ↥P), ‖poleCoord (⟨p, hp⟩ : ↥P) z‖ ≤ 1
        := by
      have h2 := hcont.tendsto
      rw [h0] at h2
      have h3 : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ one_pos
      filter_upwards [h2 h3] with z hz
      rw [← dist_zero_right]
      exact mem_closedBall.1 hz
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog := Real.log_nonpos (norm_nonneg _) hz
    simpa using hlog
  /- ## Zero extension of a piece candidate to the surface. -/
  have extendC : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (v : ↥P → ℝ),
      v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
      ∃ (vE : M → ℝ) (KE : Set M) (Cv : ℝ),
        (∀ z : ↥P, vE z = v z) ∧ MSubharmonicOn vE {p}ᶜ ∧ ContinuousOn vE {p}ᶜ ∧
        IsCompact KE ∧ KE ⊆ (P : Set M) ∧ (∀ y, y ∉ KE → vE y = 0) ∧
        ∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv := by
    intro P p hp v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y => if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dif_pos z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dif_pos hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dif_neg hyP]
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u => (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) = 𝓝 y :=
          hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem => hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem => hyP (hKwsub hmem)) (fun z hz => hKwzero z hz)
    refine ⟨w, Kw, C, hwval, hwsub, hwcont, hKwcomp, hKwsub, hKwzero, ?_⟩
    rw [← mapval P p hp, Filter.eventually_map]
    filter_upwards [hC] with z hz
    have hpc : poleCoord (⟨p, hp⟩ : ↥P) z = poleCoord p (z : M) := rfl
    rw [hwval z, ← hpc]
    exact hz
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    haveI := hcs
    haveI := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon => hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z => pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## Growth estimate ([M] (5)): a candidate gains at most `log 2` from the
  pole circle to the half circle, by the `ε`-excised annulus maximum principle. -/
  have growth : ∀ (p : M) (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      ∀ (vE : M → ℝ) (Cv MoV : ℝ),
        MSubharmonicOn vE {p}ᶜ → ContinuousOn vE {p}ᶜ →
        (∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv) →
        (∀ z ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr, vE z ≤ MoV) →
        ∀ y ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (rr / 2),
          vE y ≤ MoV + Real.log 2 := by
    intro p rr hrr htgt vE Cv MoV hvsub hvcont hCv hMoV y hyΓ
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    have hpsrc : p ∈ ep.source := mem_chart_source ℂ p
    have hcptgt : cp ∈ ep.target := by rw [hcp]; exact ep.map_source hpsrc
    have hsymcp : ep.symm cp = p := by rw [hcp]; exact ep.left_inv hpsrc
    have hsphtgt : ∀ ρ : ℝ, ρ ≤ rr → sphere cp ρ ⊆ ep.target := fun ρ hρ =>
      sphere_subset_closedBall.trans ((closedBall_subset_closedBall hρ).trans htgt)
    obtain ⟨wy, hwy, hwyy⟩ := hyΓ
    have hwyt : wy ∈ ep.target := hsphtgt _ (by linarith only [hrr]) hwy
    have hysrc : y ∈ ep.source := hwyy ▸ ep.map_target hwyt
    have hyval : ep y = wy := by rw [← hwyy, ep.right_inv hwyt]
    have hydist : dist (ep y) cp = rr / 2 := by rw [hyval]; exact mem_sphere.1 hwy
    have hyne : y ≠ p := by
      intro hcon
      rw [hcon, ← hcp, dist_self] at hydist
      have h0 : (0 : ℝ) < rr / 2 := by linarith only [hrr]
      rw [← hydist] at h0
      exact lt_irrefl _ h0
    -- the chart-ball pole bound
    obtain ⟨Nv, hNvnhds, hNv⟩ := (eventually_nhdsWithin_iff.mp hCv).exists_mem
    have hprev : ep.target ∩ ep.symm ⁻¹' Nv ∈ 𝓝 cp := by
      have h1 : ContinuousAt ep.symm cp := ep.continuousAt_symm hcptgt
      have h3 : ep.symm ⁻¹' Nv ∈ 𝓝 cp := h1.preimage_mem_nhds (hsymcp ▸ hNvnhds)
      exact Filter.inter_mem (ep.open_target.mem_nhds hcptgt) h3
    obtain ⟨σ₀, hσ₀pos, hσ₀sub⟩ := nhds_basis_closedBall.mem_iff.1 hprev
    have hCbound : ∀ z : M, z ∈ ep.source → ep z ∈ closedBall cp σ₀ → z ≠ p →
        vE z + Real.log (dist (ep z) cp) ≤ Cv := by
      intro z hzs hzball hzne
      have h3 : ep z ∈ ep.symm ⁻¹' Nv := (hσ₀sub hzball).2
      have h4 : z ∈ Nv := by rwa [Set.mem_preimage, ep.left_inv hzs] at h3
      have h5 := hNv z h4 (Set.mem_compl_singleton_iff.mpr hzne)
      have h6 : ‖poleCoord p z‖ = dist (ep z) cp := by
        simp only [poleCoord, ← hep, ← hcp, dist_eq_norm]
      rwa [h6] at h5
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    refine le_of_forall_pos_le_add ?_
    intro ε' hε'
    set ε : ℝ := ε' / Real.log 2 with hε
    have hεpos : 0 < ε := div_pos hε' hlog2
    have hεlog : ε * Real.log 2 = ε' := by
      rw [hε]
      exact div_mul_cancel₀ ε' hlog2.ne'
    set Q : ℝ := (MoV - Cv + (1 + ε) * Real.log rr) / ε with hQ
    set σ : ℝ := min (min σ₀ (rr / 4)) (Real.exp Q) with hσ
    have hσpos : 0 < σ :=
      lt_min (lt_min hσ₀pos (by linarith only [hrr])) (Real.exp_pos Q)
    have hσσ₀ : σ ≤ σ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hσR4 : σ ≤ rr / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) :=
            Real.log_le_log hσpos (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hεQ : ε * Q = MoV - Cv + (1 + ε) * Real.log rr := by
      rw [hQ, mul_comm]
      exact div_mul_cancel₀ _ hεpos.ne'
    -- the excised annulus region
    set Ωσ : Set M := ep.symm '' (ball cp rr \ closedBall cp σ) with hΩσ
    have hΩσsub : ball cp rr \ closedBall cp σ ⊆ ep.target :=
      (Set.diff_subset.trans ball_subset_closedBall).trans htgt
    have hΩσopen : IsOpen Ωσ := by
      rw [hΩσ, himg ep _ hΩσsub]
      exact ep.continuousOn.isOpen_inter_preimage ep.open_source
        (isOpen_ball.sdiff isClosed_closedBall)
    have hΩσmem : ∀ z ∈ Ωσ, z ∈ ep.source ∧ σ < dist (ep z) cp ∧
        dist (ep z) cp < rr := by
      intro z hz
      rw [hΩσ, himg ep _ hΩσsub] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall] at hz2
      exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
    have hΩσmem' : ∀ z : M, z ∈ ep.source → σ < dist (ep z) cp →
        dist (ep z) cp < rr → z ∈ Ωσ := by
      intro z hz1 hz2 hz3
      rw [hΩσ, himg ep _ hΩσsub]
      refine ⟨hz1, ?_⟩
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall]
      exact ⟨hz3, not_le.2 hz2⟩
    have hpΩσ : p ∉ Ωσ := by
      intro hcon
      obtain ⟨-, h2, -⟩ := hΩσmem p hcon
      rw [← hcp, dist_self] at h2
      exact absurd h2 (not_lt.2 hσpos.le)
    have hΩσne : Ωσ ≠ Set.univ := by
      intro hcon
      apply hpΩσ
      rw [hcon]
      trivial
    set Kσ : Set M := ep.symm '' (closedBall cp rr \ ball cp σ) with hKσ
    have hKσcomp : IsCompact Kσ :=
      ((isCompact_closedBall cp rr).diff isOpen_ball).image_of_continuousOn
        (ep.continuousOn_symm.mono (Set.diff_subset.trans htgt))
    have hΩσKσ : Ωσ ⊆ Kσ :=
      Set.image_mono (fun w hw => ⟨ball_subset_closedBall hw.1,
        fun h => hw.2 (ball_subset_closedBall h)⟩)
    -- harmonicity and continuity of the logarithmic barrier
    have hepatlas : ep ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
      rw [hep]
      exact IsManifold.chart_mem_maximalAtlas p
    have hbharm : ∀ z : M, z ∈ ep.source → ep z ≠ cp →
        MHarmonicAt (fun q => Real.log (dist (ep q) cp)) z := by
      intro z hzs hzne
      have h1 : MHarmonicAt (fun q => Real.log (dist (ep q) cp)) z ↔
          HarmonicAt ((fun q => Real.log (dist (ep q) cp)) ∘ ep.symm) (ep z) :=
        mharmonicAt_iff_of_mem_maximalAtlas hepatlas hzs
      rw [h1]
      have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - cp‖) (ep z) := by
        apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - cp)
        · exact analyticAt_id.sub analyticAt_const
        · exact sub_ne_zero.2 hzne
      have heqv : (fun w : ℂ => Real.log ‖w - cp‖) =ᶠ[𝓝 (ep z)]
          ((fun q => Real.log (dist (ep q) cp)) ∘ ep.symm) := by
        filter_upwards [ep.open_target.mem_nhds (ep.map_source hzs)] with w hw
        simp only [Function.comp_apply, ep.right_inv hw, dist_eq_norm]
      exact (harmonicAt_congr_nhds heqv).1 hharm
    have hbcont : ∀ z : M, z ∈ ep.source → ep z ≠ cp →
        ContinuousAt (fun q => Real.log (dist (ep q) cp)) z := by
      intro z hzs hzne
      have h2 : ContinuousAt ep z := ep.continuousAt hzs
      have h3 : dist (ep z) cp ≠ 0 := (dist_pos.2 hzne).ne'
      exact (h2.dist continuousAt_const).log h3
    have hvCA : ∀ z : M, z ≠ p → ContinuousAt vE z := fun z hz =>
      hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.2 hz))
    -- the competitor and its subharmonicity
    set Wf : M → ℝ :=
      fun q => vE q + (1 + ε) * (Real.log (dist (ep q) cp) - Real.log rr) with hWf
    have hWfsub : MSubharmonicOn Wf Ωσ := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hΩσmem z hz
      have hzne : ep z ≠ cp := by
        intro hcon
        rw [hcon, dist_self] at hz2
        exact absurd hz2 (not_lt.2 hσpos.le)
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp] at hzne
        exact hzne rfl
      have hu : MHarmonicAt
          (fun q => (-(1 + ε)) * Real.log (dist (ep q) cp) + (1 + ε) * Real.log rr)
          z := mharmAffine _ z _ _ (hbharm z hz1 hzne)
      have h7 := (hvsub z (Set.mem_compl_singleton_iff.mpr hznep)).sub_mharmonicAt hu
      have h9 : Wf = fun q => vE q -
          ((-(1 + ε)) * Real.log (dist (ep q) cp) + (1 + ε) * Real.log rr) := by
        funext q
        simp only [hWf]
        ring
      rw [h9]
      exact h7
    -- boundary control on the two circles
    have hWfbd : ∀ z ∈ closure Ωσ \ Ωσ, ContinuousAt Wf z ∧ Wf z ≤ MoV := by
      rintro z ⟨hzcl, hzΩ⟩
      have hzK : z ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hzcl
      obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ := hzK
      have hwt : w ∈ ep.target := htgt hw1
      have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
      have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
      have hzd1 : σ ≤ dist (ep z) cp := by
        rw [hzval]
        exact not_lt.1 (fun h => hw2 (mem_ball.2 h))
      have hzd2 : dist (ep z) cp ≤ rr := by rw [hzval]; exact mem_closedBall.1 hw1
      have hzne : ep z ≠ cp := by
        intro hcon
        rw [hcon, dist_self] at hzd1
        exact absurd hzd1 (not_le.2 hσpos)
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp] at hzne
        exact hzne rfl
      have hcont : ContinuousAt Wf z := by
        rw [hWf]
        exact (hvCA z hznep).add
          (continuousAt_const.mul ((hbcont z hzsrc hzne).sub continuousAt_const))
      refine ⟨hcont, ?_⟩
      have hdisj : dist (ep z) cp = σ ∨ dist (ep z) cp = rr := by
        rcases lt_or_eq_of_le hzd1 with h1 | h1
        · rcases lt_or_eq_of_le hzd2 with h2 | h2
          · exact absurd (hΩσmem' z hzsrc h1 h2) hzΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hdisj with hzd | hzd
      · have hσball : ep z ∈ closedBall cp σ₀ := by
          rw [mem_closedBall, hzd]
          exact hσσ₀
        have hvz : vE z + Real.log σ ≤ Cv := by
          have h5 := hCbound z hzsrc hσball hznep
          rwa [hzd] at h5
        rw [hWf]
        simp only
        rw [hzd]
        have h8 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hεpos.le
        rw [hεQ] at h8
        nlinarith only [hvz, h8]
      · have hzΓ : z ∈ ep.symm '' sphere cp rr :=
          ⟨ep z, mem_sphere.2 hzd, ep.left_inv hzsrc⟩
        rw [hWf]
        simp only
        rw [hzd, sub_self, mul_zero, add_zero]
        exact hMoV z hzΓ
    have hWfle : ∀ z ∈ Ωσ, Wf z ≤ MoV := by
      apply maxPrin Ωσ Wf MoV Kσ hΩσopen hΩσne hWfsub hKσcomp ?_ hWfbd
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    -- evaluate on the half circle
    have hyΩσ : y ∈ Ωσ := by
      apply hΩσmem' y hysrc
      · rw [hydist]; linarith only [hσR4, hrr]
      · rw [hydist]; linarith only [hrr]
    have h9 := hWfle y hyΩσ
    rw [hWf] at h9
    simp only at h9
    rw [hydist] at h9
    have h10 : Real.log (rr / 2) = Real.log rr - Real.log 2 :=
      Real.log_div hrr.ne' two_ne_zero
    rw [h10] at h9
    have h11 : (1 + ε) * (Real.log rr - Real.log 2 - Real.log rr) =
        -(1 + ε) * Real.log 2 := by
      ring
    rw [h11] at h9
    have h12 : (1 + ε) * Real.log 2 = Real.log 2 + ε' := by
      rw [add_mul, one_mul, hεlog]
    linarith only [h9, h12]
  /- ## The per-piece pole bound: envelope interior bound and growth estimate. -/
  have poleBound : ∀ (P : Opens M), ConnectedSpace ↥P → NoncompactSpace ↥P →
      ∀ (p : M) (hp : p ∈ P), HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      (∀ y ∈ (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) rr, y ∈ P) →
      ∃ (Nt : ℝ) (xout : M),
        xout ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr ∧
        pieceGreen P p xout = Nt ∧
        (∀ y ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr,
          pieceGreen P p y ≤ Nt) ∧
        ∀ y ∈ (P : Set M) ∩
            ((chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (rr / 2))ᶜ,
          pieceGreen P p y ≤ Nt + Real.log 2 := by
    intro P hcs hnc p hp hGF rr hrr htgt hcarP
    haveI := hcs
    haveI := hnc
    have hIB := interiorBd p rr hrr htgt (P : Set M) P.2
    have hGR := growth p rr hrr htgt
    have hBdd := (mharmonicOn_greenEnvelope hGF).2
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    -- reading points of the chart circles
    have hΓread : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → ∀ z ∈ ep.symm '' sphere cp ρ,
        z ∈ ep.source ∧ dist (ep z) cp = ρ ∧ z ≠ p ∧ z ∈ P := by
      intro ρ hρ0 hρrr z hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hwt : w ∈ ep.target :=
        (sphere_subset_closedBall.trans
          ((closedBall_subset_closedBall hρrr).trans htgt)) hw
      have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
      have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
      have hzd : dist (ep z) cp = ρ := by rw [hzval]; exact mem_sphere.1 hw
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp, dist_self] at hzd
        rw [← hzd] at hρ0
        exact lt_irrefl _ hρ0
      have hzP : z ∈ P := hcarP z
        ⟨w, closedBall_subset_closedBall hρrr (sphere_subset_closedBall hw), hwz⟩
      exact ⟨hzsrc, hzd, hznep, hzP⟩
    have hΓcomp : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → IsCompact (ep.symm '' sphere cp ρ) ∧
        (ep.symm '' sphere cp ρ).Nonempty := by
      intro ρ hρ0 hρrr
      constructor
      · exact (isCompact_sphere cp ρ).image_of_continuousOn
          (ep.continuousOn_symm.mono (sphere_subset_closedBall.trans
            ((closedBall_subset_closedBall hρrr).trans htgt)))
      · exact (NormedSpace.sphere_nonempty.2 hρ0.le).image _
    have hgcont : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr →
        ContinuousOn (pieceGreen P p) (ep.symm '' sphere cp ρ) := by
      intro ρ hρ0 hρrr z hz
      obtain ⟨-, -, hznep, hzP⟩ := hΓread ρ hρ0 hρrr z hz
      exact ((pgharm P p hp hcs hnc hGF z hzP hznep).continuousAt).continuousWithinAt
    have hΓoutC := hΓcomp rr hrr le_rfl
    have hΓinC := hΓcomp (rr / 2) (by linarith only [hrr]) (by linarith only [hrr])
    obtain ⟨xout, hxoutΓ, hxoutmax⟩ :=
      hΓoutC.1.exists_isMaxOn hΓoutC.2 (hgcont rr hrr le_rfl)
    obtain ⟨xin, hxinΓ, hxinmax⟩ :=
      hΓinC.1.exists_isMaxOn hΓinC.2
        (hgcont (rr / 2) (by linarith only [hrr]) (by linarith only [hrr]))
    set Nt : ℝ := pieceGreen P p xout with hNt
    set Mt : ℝ := pieceGreen P p xin with hMt
    have hMtpos : 0 < Mt := by
      obtain ⟨-, -, hnep2, hP2⟩ := hΓread (rr / 2) (by linarith only [hrr])
        (by linarith only [hrr]) xin hxinΓ
      rw [hMt, pgval P p hp xin hP2]
      exact greenEnvelope_pos hGF _ (fun hcon => hnep2 (congrArg Subtype.val hcon))
    -- per-candidate circle bounds against the envelope maxima
    have hcircGen : ∀ (ρ : ℝ) (hρ0 : 0 < ρ) (hρrr : ρ ≤ rr) (xm : M)
        (hxm : IsMaxOn (pieceGreen P p) (ep.symm '' sphere cp ρ) xm)
        (v : ↥P → ℝ), v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
        ∀ (vE : M → ℝ), (∀ z : ↥P, vE z = v z) →
        ∀ z ∈ ep.symm '' sphere cp ρ, vE z ≤ pieceGreen P p xm := by
      intro ρ hρ0 hρrr xm hxm v hv vE hvEval z hz
      obtain ⟨-, -, hznep, hzP⟩ := hΓread ρ hρ0 hρrr z hz
      calc vE z = v ⟨z, hzP⟩ := hvEval ⟨z, hzP⟩
        _ ≤ greenEnvelope (⟨p, hp⟩ : ↥P) ⟨z, hzP⟩ :=
            le_csSup (hBdd _ (fun hcon => hznep (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
        _ = pieceGreen P p z := (pgval P p hp z hzP).symm
        _ ≤ pieceGreen P p xm := hxm hz
    -- envelope interior bound on the piece minus the inner disk
    have hIntEnv : ∀ y ∈ (P : Set M) ∩ (ep.symm '' closedBall cp (rr / 2))ᶜ,
        pieceGreen P p y ≤ Mt := by
      intro y hy
      have hyP : y ∈ P := hy.1
      rw [pgval P p hp y hyP]
      simp only [greenEnvelope]
      refine csSup_le ⟨0, (fun _ : ↥P => (0 : ℝ)), zeroFam P p hp, rfl⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P p hp v hv
      have hgoal : vE y ≤ Mt := by
        apply hIB vE KE Mt hMtpos.le hvEsub hvEcont hKEc hKEP hKE0 ?_ y hy
        exact hcircGen (rr / 2) (by linarith only [hrr]) (by linarith only [hrr])
          xin hxinmax v hv vE hvEval
      have h1 : v ⟨y, hyP⟩ = vE y := (hvEval ⟨y, hyP⟩).symm
      rw [← h1] at hgoal
      exact hgoal
    -- envelope growth estimate on the half circle
    have hgrowEnv : ∀ y ∈ ep.symm '' sphere cp (rr / 2),
        pieceGreen P p y ≤ Nt + Real.log 2 := by
      intro y hy
      obtain ⟨-, -, hynep, hyP⟩ := hΓread (rr / 2) (by linarith only [hrr])
        (by linarith only [hrr]) y hy
      rw [pgval P p hp y hyP]
      simp only [greenEnvelope]
      refine csSup_le ⟨0, (fun _ : ↥P => (0 : ℝ)), zeroFam P p hp, rfl⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P p hp v hv
      have hgoal : vE y ≤ Nt + Real.log 2 := by
        apply hGR vE Cv Nt hvEsub hvEcont hCv ?_ y hy
        intro z hz
        have h2 := hcircGen rr hrr le_rfl xout hxoutmax v hv vE hvEval z hz
        rw [← hNt] at h2
        exact h2
      have h1 : v ⟨y, hyP⟩ = vE y := (hvEval ⟨y, hyP⟩).symm
      rw [← h1] at hgoal
      exact hgoal
    have hMtNt : Mt ≤ Nt + Real.log 2 := by
      rw [hMt]
      exact hgrowEnv xin hxinΓ
    refine ⟨Nt, xout, hxoutΓ, hNt.symm, ?_, ?_⟩
    · intro y hy
      have h3 := hxoutmax hy
      rw [← hNt] at h3
      exact h3
    · intro y hy
      exact le_trans (hIntEnv y hy) hMtNt
  /- ## The oscillation bound on a chain compact, via the per-piece pole bound. -/
  have oscBd : ∀ (pa : M) (ra : ℝ), 0 < ra →
      closedBall (chartAt ℂ pa pa) ra ⊆ (chartAt ℂ pa).target →
      ∀ (P : Opens M), ∀ hcs : ConnectedSpace ↥P, ∀ hnc : NoncompactSpace ↥P,
      ∀ hpaP : pa ∈ P, HasGreenFunction (⟨pa, hpaP⟩ : ↥P) →
      (∀ w ∈ closedBall (chartAt ℂ pa pa) ra, (chartAt ℂ pa).symm w ∈ P) →
      ∀ (KA ΩA : Set M) (CHa : ℝ),
      (∀ u : M → ℝ, MHarmonicOn u ΩA → (∀ x ∈ ΩA, 0 ≤ u x) →
        ∀ x ∈ KA, ∀ y ∈ KA, u x ≤ CHa * u y) →
      KA ⊆ ΩA → p₃ ∈ KA →
      (∀ z ∈ ΩA, z ∈ P) →
      (∀ z ∈ ΩA, z ∉ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2)) →
      ((chartAt ℂ pa).symm '' sphere (chartAt ℂ pa pa) ra ⊆ KA) →
      ∀ z ∈ KA, |pieceGreen P pa z - pieceGreen P pa p₃| ≤ CHa * Real.log 2 := by
    intro pa ra hra htgtA P hcs hnc hpaP hGFa hcarA KA ΩA CHa hCHa hKAΩ hp₃KA hΩA1
      hΩA2 hΓA z hzK
    obtain ⟨Nt, xout, hxoutΓ, hxoutval, hxoutmax, hIB⟩ :=
      poleBound P hcs hnc pa hpaP hGFa ra hra htgtA
        (by rintro y ⟨w, hw, rfl⟩; exact hcarA w hw)
    have hpahalf : pa ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2) :=
      ⟨chartAt ℂ pa pa, mem_closedBall_self (by linarith only [hra]),
        (chartAt ℂ pa).left_inv (mem_chart_source ℂ pa)⟩
    set u : M → ℝ := fun q => Nt + Real.log 2 - pieceGreen P pa q with hu
    have huharm : MHarmonicOn u ΩA := by
      intro q hq
      have hqnepa : q ≠ pa := fun hcon => hΩA2 q hq (hcon ▸ hpahalf)
      have h1 : MHarmonicAt (pieceGreen P pa) q :=
        pgharm P pa hpaP hcs hnc hGFa q (hΩA1 q hq) hqnepa
      refine mharm_congr _ _ q (Filter.Eventually.of_forall fun y => ?_)
        (mharmAffine _ q (-1) (Nt + Real.log 2) h1)
      simp only [hu]
      ring
    have hupos : ∀ x ∈ ΩA, 0 ≤ u x := by
      intro x hx
      have h2 := hIB x ⟨hΩA1 x hx, hΩA2 x hx⟩
      simp only [hu]
      linarith only [h2]
    have hxoutK : xout ∈ KA := hΓA hxoutΓ
    have huout : u xout = Real.log 2 := by
      simp only [hu]
      rw [hxoutval]
      ring
    have h3 : u z ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos z hzK xout hxoutK
      rwa [huout] at h5
    have h4 : u p₃ ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos p₃ hp₃KA xout hxoutK
      rwa [huout] at h5
    have h5 : 0 ≤ u z := hupos z (hKAΩ hzK)
    have h6 : 0 ≤ u p₃ := hupos p₃ (hKAΩ hp₃KA)
    have h7 : pieceGreen P pa z - pieceGreen P pa p₃ = u p₃ - u z := by
      simp only [hu]
      ring
    rw [h7, abs_le]
    constructor <;> linarith only [h3, h4, h5, h6]
  /- ## The pole charts and the avoidance radii. -/
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  have havoid1 : ∃ S : ℝ, 0 < S ∧ closedBall c₁ S ⊆ e₁.target ∧
      ∀ w ∈ closedBall c₁ S, e₁.symm w ∉ D₀.closedCarrier ∧ e₁.symm w ≠ p₂ ∧
        e₁.symm w ≠ p₃ := by
    have hopen : IsOpen (e₁.target ∩
        e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ ({p₂}ᶜ ∩ {p₃}ᶜ))) :=
      e₁.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter
          (isOpen_compl_singleton.inter isOpen_compl_singleton))
    have hmem : c₁ ∈ e₁.target ∩
        e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ ({p₂}ᶜ ∩ {p₃}ᶜ)) := by
      refine ⟨by rw [hc₁]; exact e₁.map_source hp₁src, ?_⟩
      rw [Set.mem_preimage, hc₁, e₁.left_inv hp₁src]
      exact ⟨hp₁, Set.mem_compl_singleton_iff.2 hne,
        Set.mem_compl_singleton_iff.2 (Ne.symm h₃₁)⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw => (hSsub hw).1, fun w hw => ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, Set.mem_compl_singleton_iff.1 h2.2.1,
      Set.mem_compl_singleton_iff.1 h2.2.2⟩
  obtain ⟨S₁, hS₁0, hS₁tgt, hS₁av⟩ := havoid1
  set r₁ : ℝ := S₁ / 2 with hr₁def
  have hr₁ : 0 < r₁ := by rw [hr₁def]; exact half_pos hS₁0
  have h2r₁ : 2 * r₁ ≤ S₁ := by rw [hr₁def]; linarith only []
  have htgt1 : closedBall c₁ (2 * r₁) ⊆ e₁.target :=
    (closedBall_subset_closedBall h2r₁).trans hS₁tgt
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  have hCar1cp : IsCompact Car1 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono htgt1)
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ ∧ z ≠ p₃ := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₁av w (closedBall_subset_closedBall h2r₁ hw)
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have havoid2 : ∃ S : ℝ, 0 < S ∧ closedBall c₂ S ⊆ e₂.target ∧
      ∀ w ∈ closedBall c₂ S, e₂.symm w ∉ D₀.closedCarrier ∧ e₂.symm w ∉ Car1 ∧
        e₂.symm w ≠ p₃ := by
    have hopen : IsOpen (e₂.target ∩
        e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ (Car1ᶜ ∩ {p₃}ᶜ))) :=
      e₂.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter
          (hCar1cp.isClosed.isOpen_compl.inter isOpen_compl_singleton))
    have hmem : c₂ ∈ e₂.target ∩
        e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ (Car1ᶜ ∩ {p₃}ᶜ)) := by
      refine ⟨by rw [hc₂]; exact e₂.map_source hp₂src, ?_⟩
      rw [Set.mem_preimage, hc₂, e₂.left_inv hp₂src]
      exact ⟨hp₂, fun hmem2 => (hCar1av p₂ hmem2).2.1 rfl,
        Set.mem_compl_singleton_iff.2 (Ne.symm h₃₂)⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw => (hSsub hw).1, fun w hw => ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, h2.2.1, Set.mem_compl_singleton_iff.1 h2.2.2⟩
  obtain ⟨S₂, hS₂0, hS₂tgt, hS₂av⟩ := havoid2
  set r₂ : ℝ := S₂ / 2 with hr₂def
  have hr₂ : 0 < r₂ := by rw [hr₂def]; exact half_pos hS₂0
  have h2r₂ : 2 * r₂ ≤ S₂ := by rw [hr₂def]; linarith only []
  have htgt2 : closedBall c₂ (2 * r₂) ⊆ e₂.target :=
    (closedBall_subset_closedBall h2r₂).trans hS₂tgt
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 ∧ z ≠ p₃ := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₂av w (closedBall_subset_closedBall h2r₂ hw)
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  /- ## The half pole disks and the Harnack chain domains. -/
  set half1 : CoordDisk M := ⟨p₁, r₁ / 2, by linarith only [hr₁],
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1⟩ with hhalf1
  set half2 : CoordDisk M := ⟨p₂, r₂ / 2, by linarith only [hr₂],
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2⟩ with hhalf2
  have hhalf1car : half1.closedCarrier = e₁.symm '' closedBall c₁ (r₁ / 2) := rfl
  have hhalf2car : half2.closedCarrier = e₂.symm '' closedBall c₂ (r₂ / 2) := rfl
  have hhalf1Car : half1.closedCarrier ⊆ Car1 := by
    rw [hhalf1car, hCar1]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
  have hhalf2Car : half2.closedCarrier ⊆ Car2 := by
    rw [hhalf2car, hCar2]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
  have hdisj1 : Disjoint D₀.closedCarrier half1.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz1
    exact (hCar1av z (hhalf1Car hz1)).1 hzQ
  have hdisj2 : Disjoint D₀.closedCarrier half2.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz2
    exact (hCar2av z (hhalf2Car hz2)).1 hzQ
  set Ω₁ : Set M := (D₀.closedCarrier ∪ half1.closedCarrier)ᶜ with hΩ₁
  set Ω₂ : Set M := (D₀.closedCarrier ∪ half2.closedCarrier)ᶜ with hΩ₂
  have hΩ₁open : IsOpen Ω₁ := (D₀.isCompact_closedCarrier.union
    half1.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₂open : IsOpen Ω₂ := (D₀.isCompact_closedCarrier.union
    half2.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₁conn : IsPreconnected Ω₁ :=
    (isConnected_two_coordDisk_compl D₀ half1 hdisj1).isPreconnected
  have hΩ₂conn : IsPreconnected Ω₂ :=
    (isConnected_two_coordDisk_compl D₀ half2 hdisj2).isPreconnected
  /- ## The chain compacts: the pole circles with the two marked points. -/
  set Γ₁ : Set M := e₁.symm '' sphere c₁ r₁ with hΓ₁
  set Γ₂ : Set M := e₂.symm '' sphere c₂ r₂ with hΓ₂
  have hsph1tgt : sphere c₁ r₁ ⊆ e₁.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hsph2tgt : sphere c₂ r₂ ⊆ e₂.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  have hΓ₁cp : IsCompact Γ₁ := (isCompact_sphere _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono hsph1tgt)
  have hΓ₂cp : IsCompact Γ₂ := (isCompact_sphere _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono hsph2tgt)
  have hΓ₁Car : Γ₁ ⊆ Car1 := by
    rw [hΓ₁, hCar1]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hΓ₂Car : Γ₂ ⊆ Car2 := by
    rw [hΓ₂, hCar2]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  have hΓ₁half : ∀ z ∈ Γ₁, z ∉ half1.closedCarrier := by
    intro z hz hmem
    rw [hhalf1car] at hmem
    obtain ⟨hzs, hzd⟩ := (hmemCB e₁ c₁ (r₁ / 2)
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1) z).1 hmem
    obtain ⟨-, hzd'⟩ := (hmemSph e₁ c₁ r₁ hsph1tgt z).1 hz
    rw [hzd'] at hzd
    linarith only [hzd, hr₁]
  have hΓ₂half : ∀ z ∈ Γ₂, z ∉ half2.closedCarrier := by
    intro z hz hmem
    rw [hhalf2car] at hmem
    obtain ⟨hzs, hzd⟩ := (hmemCB e₂ c₂ (r₂ / 2)
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2) z).1 hmem
    obtain ⟨-, hzd'⟩ := (hmemSph e₂ c₂ r₂ hsph2tgt z).1 hz
    rw [hzd'] at hzd
    linarith only [hzd, hr₂]
  set K₁ : Set M := Γ₁ ∪ {p₂} ∪ {p₃} with hK₁
  set K₂ : Set M := Γ₂ ∪ {p₁} ∪ {p₃} with hK₂
  have hK₁cp : IsCompact K₁ :=
    (hΓ₁cp.union isCompact_singleton).union isCompact_singleton
  have hK₂cp : IsCompact K₂ :=
    (hΓ₂cp.union isCompact_singleton).union isCompact_singleton
  have hp₂K₁ : p₂ ∈ K₁ := Or.inl (Or.inr rfl)
  have hp₃K₁ : p₃ ∈ K₁ := Or.inr rfl
  have hp₁K₂ : p₁ ∈ K₂ := Or.inl (Or.inr rfl)
  have hp₃K₂ : p₃ ∈ K₂ := Or.inr rfl
  have hK₁Ω₁ : K₁ ⊆ Ω₁ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar1av z (hΓ₁Car hz)).1 hmem
      · exact hΓ₁half z hz hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₂ hmem
      · exact (hCar1av z (hhalf1Car hmem)).2.1 rfl
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃ hmem
      · exact (hCar1av z (hhalf1Car hmem)).2.2 rfl
  have hK₂Ω₂ : K₂ ⊆ Ω₂ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar2av z (hΓ₂Car hz)).1 hmem
      · exact hΓ₂half z hz hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₁ hmem
      · exact (hCar2av z (hhalf2Car hmem)).2.1 hp₁Car1
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃ hmem
      · exact (hCar2av z (hhalf2Car hmem)).2.2 rfl
  obtain ⟨CH₁, hCH₁0, hCH₁⟩ := exists_harnack_chain_const hΩ₁open hΩ₁conn hK₁cp hK₁Ω₁
  obtain ⟨CH₂, hCH₂0, hCH₂⟩ := exists_harnack_chain_const hΩ₂open hΩ₂conn hK₂cp hK₂Ω₂
  /- ## The packaged bound at `t₀ = 1`. -/
  refine ⟨1, CH₁ * Real.log 2 + CH₂ * Real.log 2, one_pos, le_refl 1, ?_⟩
  intro t ht ht1 _
  set Pt : Opens M := (D₀.shrink t ht ht1).compl with hPt
  have hcarsubt : (D₀.shrink t ht ht1).closedCarrier ⊆ D₀.closedCarrier := by
    have h1 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    have h2 : D₀.closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) D₀.radius := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left D₀.radius_pos.le ht1))
  have hp₁t : p₁ ∈ Pt := fun hmem => hp₁ (hcarsubt hmem)
  have hp₂t : p₂ ∈ Pt := fun hmem => hp₂ (hcarsubt hmem)
  haveI hconnT : ConnectedSpace ↥Pt :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  haveI hncT : NoncompactSpace ↥Pt := noncompactSpace_coordDisk_compl _
  have hGF1t : HasGreenFunction (⟨p₁, hp₁t⟩ : ↥Pt) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁t
  have hGF2t : HasGreenFunction (⟨p₂, hp₂t⟩ : ↥Pt) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂t
  have hcarP1 : ∀ w ∈ closedBall c₁ r₁, e₁.symm w ∈ Pt := by
    intro w hw hmem
    exact (hS₁av w (closedBall_subset_closedBall
      (by linarith only [hr₁, h2r₁]) hw)).1 (hcarsubt hmem)
  have hcarP2 : ∀ w ∈ closedBall c₂ r₂, e₂.symm w ∈ Pt := by
    intro w hw hmem
    exact (hS₂av w (closedBall_subset_closedBall
      (by linarith only [hr₂, h2r₂]) hw)).1 (hcarsubt hmem)
  /- ## The two oscillation bounds pinned at the drift base point. -/
  have osc1 : |pieceGreen Pt p₁ p₂ - pieceGreen Pt p₁ p₃| ≤ CH₁ * Real.log 2 := by
    refine oscBd p₁ r₁ hr₁
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      Pt hconnT hncT hp₁t hGF1t hcarP1 K₁ Ω₁ CH₁ hCH₁ hK₁Ω₁ hp₃K₁ ?_ ?_ ?_ p₂ hp₂K₁
    · intro z hz hmem
      exact hz (Or.inl (hcarsubt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inl hz)
  have osc2 : |pieceGreen Pt p₂ p₁ - pieceGreen Pt p₂ p₃| ≤ CH₂ * Real.log 2 := by
    refine oscBd p₂ r₂ hr₂
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      Pt hconnT hncT hp₂t hGF2t hcarP2 K₂ Ω₂ CH₂ hCH₂ hK₂Ω₂ hp₃K₂ ?_ ?_ ?_ p₁ hp₁K₂
    · intro z hz hmem
      exact hz (Or.inl (hcarsubt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inl hz)
  /- ## Symmetry of the piece Green's function at the two poles. -/
  have hsymm : pieceGreen Pt p₁ p₂ = pieceGreen Pt p₂ p₁ := by
    rw [pgval Pt p₁ hp₁t p₂ hp₂t, pgval Pt p₂ hp₂t p₁ hp₁t]
    exact greenEnvelope_symm hGF1t (fun hcon => hne (congrArg Subtype.val hcon))
  /- ## Assembly: the cross terms cancel by symmetry. -/
  have h1 := abs_le.1 osc1
  have h2 := abs_le.1 osc2
  rw [abs_le]
  constructor
  · linarith only [h1.2, h2.1, hsymm]
  · linarith only [h1.1, h2.2, hsymm]

/-- **The drift bound** (the irreducible core of the classical cross-symmetry
of Green's functions, in its weakest sufficient form): the two piece Green's
functions, evaluated at a fixed third base point, differ by a
shrink-independent constant. -/
theorem exists_pieceGreen_drift_bound (D₀ : CoordDisk M) {p₁ p₂ p₃ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier)
    (hp₃ : p₃ ∉ D₀.closedCarrier) (hne : p₁ ≠ p₂) (h₃₁ : p₃ ≠ p₁)
    (h₃₂ : p₃ ≠ p₂) :
    ∃ C, ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C := by
  classical
  /- ## Geometry of the shrinking disks. -/
  have hcarsub : ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      (D₀.shrink t ht ht1).closedCarrier ⊆ D₀.closedCarrier := by
    intro t ht ht1
    have h1 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    have h2 : D₀.closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) D₀.radius := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left D₀.radius_pos.le ht1))
  have hcarmono : ∀ t t' (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
      (ht1' : t' ≤ 1), t' ≤ t →
      (D₀.shrink t' ht' ht1').closedCarrier ⊆
        (D₀.shrink t ht ht1).closedCarrier := by
    intro t t' ht ht1 ht' ht1' htt
    have h1 : (D₀.shrink t' ht' ht1').closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t' * D₀.radius) := rfl
    have h2 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right htt D₀.radius_pos.le))
  have hWmem : ∀ t (ht : 0 < t) (ht1 : t ≤ 1) {y : M}, y ∉ D₀.closedCarrier →
      y ∈ (D₀.shrink t ht ht1).compl := by
    intro t ht ht1 y hy hmem
    exact hy (hcarsub t ht ht1 hmem)
  have hWsub : ∀ t t' (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
      (ht1' : t' ≤ 1), t' ≤ t →
      ((D₀.shrink t ht ht1).compl : Set M) ⊆
        ((D₀.shrink t' ht' ht1').compl : Set M) := by
    intro t t' ht ht1 ht' ht1' htt y hy hmem
    exact hy (hcarmono t t' ht ht1 ht' ht1' htt hmem)
  have hqW : ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      D₀.center ∉ ((D₀.shrink t ht ht1).compl : Set M) := by
    intro t ht ht1 hmem
    exact hmem ⟨chartAt ℂ D₀.center D₀.center,
      mem_closedBall_self (mul_pos ht D₀.radius_pos).le,
      (chartAt ℂ D₀.center).left_inv (mem_chart_source ℂ D₀.center)⟩
  have hWne : ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      ((D₀.shrink t ht ht1).compl : Set M) ≠ Set.univ := by
    intro t ht ht1 hcon
    have hmem : D₀.center ∈ ((D₀.shrink t ht ht1).compl : Set M) := by
      rw [hcon]; trivial
    exact hqW t ht ht1 hmem
  /- ## Plane-side helper: transfer of subharmonicity along an equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈
        (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz => (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz => (hf0 _ ((hρsub hz).2)).symm
  /- ## Subharmonicity at a point transfers between the surface and a piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ),
      (∀ z : ↥P, f z = g z) →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnem : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnem := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnem]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnem).target :=
      e'.map_subtype_source hnem hzsrc
    have heqOn : Set.EqOn (⇑e'.symm)
        (Subtype.val ∘ ⇑(e'.subtypeRestr hnem).symm)
        (e'.subtypeRestr hnem).target := e'.subtypeRestr_symm_eqOn hnem
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnem).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnem).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈
          (e'.subtypeRestr hnem).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw => (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw => (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnem).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnem), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnem).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to that of the surface. -/
  have hmapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by
          rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne
              (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## The zero function belongs to the Green's family of a piece. -/
  have hbaseP : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      (fun _ : ↥P => (0 : ℝ)) ∈ greenFamily (⟨p, hpP⟩ : ↥P) := by
    intro P p hpP
    haveI : Nonempty ↥P := ⟨⟨p, hpP⟩⟩
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    set q₀ : ↥P := ⟨p, hpP⟩ with hq₀
    have hpc : ContinuousAt (poleCoord q₀) q₀ := by
      have h1 : ContinuousAt (chartAt ℂ q₀) q₀ :=
        (chartAt ℂ q₀).continuousAt (mem_chart_source ℂ q₀)
      exact h1.sub continuousAt_const
    have h0 : ‖poleCoord q₀ q₀‖ < 1 := by
      simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have hx1 : ‖poleCoord q₀ x‖ < 1 := hx
    have h6 : Real.log ‖poleCoord q₀ x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) hx1.le
    simpa using h6
  /- ## The zero function belongs to the Green's family of the surface. -/
  have hbaseM : ∀ p : M, (fun _ : M => (0 : ℝ)) ∈ greenFamily p := by
    intro p
    haveI : Nonempty M := ⟨p⟩
    refine ⟨fun x _ => mharmonicAt_const.msubharmonicAt, continuousOn_const,
      ⟨∅, isCompact_empty, Set.empty_ne_univ, fun x _ => rfl⟩, ⟨0, ?_⟩⟩
    have hpc : ContinuousAt (poleCoord p) p := by
      have h1 : ContinuousAt (chartAt ℂ p) p :=
        (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
      exact h1.sub continuousAt_const
    have h0 : ‖poleCoord p p‖ < 1 := by
      simp [poleCoord]
    have h5 := (hpc.norm).preimage_mem_nhds (Iio_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds h5] with x hx
    have hx1 : ‖poleCoord p x‖ < 1 := hx
    have h6 : Real.log ‖poleCoord p x‖ ≤ 0 :=
      Real.log_nonpos (norm_nonneg _) hx1.le
    simpa using h6
  /- ## Boundedness of the piece family at every point off the pole. -/
  have hEnvB : ∀ t (ht : 0 < t) (ht1 : t ≤ 1) (p : M)
      (hpW : p ∈ (D₀.shrink t ht ht1).compl)
      (z : ↥(D₀.shrink t ht ht1).compl), z ≠ ⟨p, hpW⟩ →
      BddAbove ((fun v => v z) ''
        greenFamily (⟨p, hpW⟩ : ↥(D₀.shrink t ht ht1).compl)) := by
    intro t ht ht1 p hpW z hz
    haveI : ConnectedSpace ↥(D₀.shrink t ht ht1).compl :=
      isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
    haveI : NoncompactSpace ↥(D₀.shrink t ht ht1).compl :=
      noncompactSpace_coordDisk_compl _
    exact (mharmonicOn_greenEnvelope
      (hasGreenFunction_coordDisk_compl _ p hpW)).2 z hz
  /- ## Unfolding the piece Green's function. -/
  have hPG : ∀ (P : Opens M) (p x : M) (hp' : p ∈ P) (hx' : x ∈ P),
      pieceGreen P p x = greenEnvelope (⟨p, hp'⟩ : ↥P) ⟨x, hx'⟩ := by
    intro P p x hp' hx'
    simp only [pieceGreen]
    rw [dif_pos (⟨hp', hx'⟩ : p ∈ P ∧ x ∈ P)]
  /- ## Zero extension of a piece family member into the surface family. -/
  have brickE : ∀ (P : Opens M), (P : Set M) ≠ Set.univ → ∀ (p : M) (hpP : p ∈ P)
      (v : ↥P → ℝ), v ∈ greenFamily (⟨p, hpP⟩ : ↥P) →
      ∃ w : M → ℝ, w ∈ greenFamily p ∧ (∀ z : ↥P, w z = v z) ∧
        ∃ Kw : Set M, IsCompact Kw ∧ Kw ⊆ (P : Set M) ∧ ∀ y, y ∉ Kw → w y = 0 := by
    intro P hPne p hpP v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y => if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dif_pos z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dif_pos hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dif_neg hyP]
    have hKwne : Kw ≠ Set.univ := by
      intro hcon
      apply hPne
      apply Set.eq_univ_of_univ_subset
      rw [← hcon]
      exact hKwsub
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hpP⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u => (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) =
            𝓝 y := hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem => hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hpP⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem => hyP (hKwsub hmem)) (fun z hz => hKwzero z hz)
    have hwpole : ∃ C', ∀ᶠ y' in 𝓝[≠] p,
        w y' + Real.log ‖poleCoord p y'‖ ≤ C' := by
      refine ⟨C, ?_⟩
      rw [← hmapval P p hpP, Filter.eventually_map]
      filter_upwards [hC] with z hz
      have hpc : poleCoord (⟨p, hpP⟩ : ↥P) z = poleCoord p (z : M) := rfl
      rw [hwval z]
      rw [← hpc]
      exact hz
    exact ⟨w, ⟨hwsub, hwcont, ⟨Kw, hKwcomp, hKwne, hKwzero⟩, hwpole⟩, hwval,
      Kw, hKwcomp, hKwsub, hKwzero⟩
  /- ## Restriction of a compactly supported surface member into a piece. -/
  have brickR : ∀ (P : Opens M), NoncompactSpace ↥P → ∀ (p : M) (hpP : p ∈ P)
      (w : M → ℝ) (Kw : Set M),
      MSubharmonicOn w {p}ᶜ → ContinuousOn w {p}ᶜ →
      IsCompact Kw → Kw ⊆ (P : Set M) → (∀ y, y ∉ Kw → w y = 0) →
      (∃ C, ∀ᶠ y' in 𝓝[≠] p, w y' + Real.log ‖poleCoord p y'‖ ≤ C) →
      (fun z : ↥P => w z) ∈ greenFamily (⟨p, hpP⟩ : ↥P) := by
    intro P hnc p hpP w Kw hwsub hwcont hKwcomp hKwsub hKwzero hwpole
    haveI := hnc
    have hKpre : IsCompact (Subtype.val ⁻¹' Kw : Set ↥P) := by
      haveI : CompactSpace ↥Kw := isCompact_iff_compactSpace.mp hKwcomp
      have himgK : (Subtype.val ⁻¹' Kw : Set ↥P) =
          (fun z : ↥Kw => (⟨z.1, hKwsub z.2⟩ : ↥P)) '' Set.univ := by
        ext z
        constructor
        · intro hz
          exact ⟨⟨z.1, hz⟩, Set.mem_univ _, rfl⟩
        · rintro ⟨u, -, rfl⟩
          exact u.2
      rw [himgK]
      exact isCompact_univ.image (continuous_subtype_val.subtype_mk _)
    refine ⟨?_, ?_, ⟨Subtype.val ⁻¹' Kw, hKpre, ?_, fun z hz => hKwzero z hz⟩, ?_⟩
    · intro z hz
      have hzp : (z : M) ≠ p := fun hcon =>
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      exact (msub_val P w _ (fun _ => rfl) z).mp
        (hwsub z (Set.mem_compl_singleton_iff.mpr hzp))
    · intro z hz
      have hzp : (z : M) ≠ p := fun hcon =>
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      have h1 : ContinuousAt w (z : M) :=
        hwcont.continuousAt (isOpen_compl_singleton.mem_nhds hzp)
      exact (h1.comp continuous_subtype_val.continuousAt).continuousWithinAt
    · intro hcon
      rw [hcon] at hKpre
      exact NoncompactSpace.noncompact_univ hKpre
    · obtain ⟨C, hC⟩ := hwpole
      refine ⟨C, ?_⟩
      have h2 : ∀ᶠ y' in Filter.map (Subtype.val : ↥P → M)
          (𝓝[≠] (⟨p, hpP⟩ : ↥P)), w y' + Real.log ‖poleCoord p y'‖ ≤ C := by
        rw [hmapval P p hpP]
        exact hC
      rw [Filter.eventually_map] at h2
      filter_upwards [h2] with z hz
      have hpc : poleCoord (⟨p, hpP⟩ : ↥P) z = poleCoord p (z : M) := rfl
      rw [hpc]
      exact hz
  /- ## Nonnegativity of the piece Green's function. -/
  have hPGnonneg : ∀ (p x : M), p ∉ D₀.closedCarrier → x ∉ D₀.closedCarrier →
      x ≠ p → ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      0 ≤ pieceGreen (D₀.shrink t ht ht1).compl p x := by
    intro p x hp hx hxp t ht ht1
    have hpW := hWmem t ht ht1 hp
    have hxW := hWmem t ht ht1 hx
    rw [hPG _ p x hpW hxW]
    have hzx : (⟨x, hxW⟩ : ↥(D₀.shrink t ht ht1).compl) ≠ ⟨p, hpW⟩ :=
      fun hcon => hxp (congrArg Subtype.val hcon)
    simp only [greenEnvelope]
    exact le_csSup (hEnvB t ht ht1 p hpW ⟨x, hxW⟩ hzx) ⟨_, hbaseP _ p hpW, rfl⟩
  /- ## Monotonicity of the piece Green's function under shrinking. -/
  have hPGmono : ∀ (p x : M), p ∉ D₀.closedCarrier → x ∉ D₀.closedCarrier →
      x ≠ p → ∀ t t' (ht : 0 < t) (ht1 : t ≤ 1) (ht' : 0 < t')
      (ht1' : t' ≤ 1), t' ≤ t →
      pieceGreen (D₀.shrink t ht ht1).compl p x ≤
        pieceGreen (D₀.shrink t' ht' ht1').compl p x := by
    intro p x hp hx hxp t t' ht ht1 ht' ht1' htt
    have hpW := hWmem t ht ht1 hp
    have hxW := hWmem t ht ht1 hx
    have hpW' := hWmem t' ht' ht1' hp
    have hxW' := hWmem t' ht' ht1' hx
    rw [hPG _ p x hpW hxW, hPG _ p x hpW' hxW']
    simp only [greenEnvelope]
    have hzx' : (⟨x, hxW'⟩ : ↥(D₀.shrink t' ht' ht1').compl) ≠ ⟨p, hpW'⟩ :=
      fun hcon => hxp (congrArg Subtype.val hcon)
    refine Real.sSup_le ?_ ?_
    · rintro a ⟨v, hv, rfl⟩
      obtain ⟨w, hwfam, hwval, Kw, hKwc, hKws, hKw0⟩ :=
        brickE _ (hWne t ht ht1) p hpW v hv
      have hwmem' : (fun z : ↥(D₀.shrink t' ht' ht1').compl => w z) ∈
          greenFamily (⟨p, hpW'⟩ : ↥(D₀.shrink t' ht' ht1').compl) :=
        brickR _ (noncompactSpace_coordDisk_compl _) p hpW' w Kw hwfam.1
          hwfam.2.1 hKwc (hKws.trans (hWsub t t' ht ht1 ht' ht1' htt)) hKw0
          hwfam.2.2.2
      have h4 : v ⟨x, hxW⟩ = w x := (hwval ⟨x, hxW⟩).symm
      exact (le_of_eq h4).trans
        (le_csSup (hEnvB t' ht' ht1' p hpW' ⟨x, hxW'⟩ hzx') ⟨_, hwmem', rfl⟩)
    · exact le_csSup (hEnvB t' ht' ht1' p hpW' ⟨x, hxW'⟩ hzx')
        ⟨_, hbaseP _ p hpW', rfl⟩
  /- ## Hyperbolic bound: the ambient envelope dominates every piece. -/
  have hPGle : ∀ (p x : M), p ∉ D₀.closedCarrier → x ∉ D₀.closedCarrier →
      BddAbove ((fun v => v x) '' greenFamily p) →
      ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      pieceGreen (D₀.shrink t ht ht1).compl p x ≤ greenEnvelope p x := by
    intro p x hp hx hbdd t ht ht1
    have hpW := hWmem t ht ht1 hp
    have hxW := hWmem t ht ht1 hx
    rw [hPG _ p x hpW hxW]
    simp only [greenEnvelope]
    refine Real.sSup_le ?_ ?_
    · rintro a ⟨v, hv, rfl⟩
      obtain ⟨w, hwfam, hwval, -⟩ := brickE _ (hWne t ht ht1) p hpW v hv
      have h4 : v ⟨x, hxW⟩ = w x := (hwval ⟨x, hxW⟩).symm
      exact (le_of_eq h4).trans (le_csSup hbdd ⟨w, hwfam, rfl⟩)
    · exact le_csSup hbdd ⟨_, hbaseM p, rfl⟩
  /- ## The monotone tail: a small-shrink bound propagates to all shrinks. -/
  have tail : (∃ t₀ C₀, 0 < t₀ ∧ t₀ ≤ 1 ∧ ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
      t ≤ t₀ → |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
        pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C₀) →
      ∃ C, ∀ t (ht : 0 < t) (ht1 : t ≤ 1),
        |pieceGreen (D₀.shrink t ht ht1).compl p₁ p₃ -
          pieceGreen (D₀.shrink t ht ht1).compl p₂ p₃| ≤ C := by
    rintro ⟨t₀, C₀, ht₀, ht₀1, hC₀⟩
    refine ⟨max C₀ (pieceGreen (D₀.shrink t₀ ht₀ ht₀1).compl p₁ p₃ +
      pieceGreen (D₀.shrink t₀ ht₀ ht₀1).compl p₂ p₃), fun t ht ht1 => ?_⟩
    rcases le_total t t₀ with h | h
    · exact (hC₀ t ht ht1 h).trans (le_max_left _ _)
    · have m1 := hPGmono p₁ p₃ hp₁ hp₃ h₃₁ t t₀ ht ht1 ht₀ ht₀1 h
      have m2 := hPGmono p₂ p₃ hp₂ hp₃ h₃₂ t t₀ ht ht1 ht₀ ht₀1 h
      have n1 := hPGnonneg p₁ p₃ hp₁ hp₃ h₃₁ t ht ht1
      have n2 := hPGnonneg p₂ p₃ hp₂ hp₃ h₃₂ t ht ht1
      have n1' := hPGnonneg p₁ p₃ hp₁ hp₃ h₃₁ t₀ ht₀ ht₀1
      have n2' := hPGnonneg p₂ p₃ hp₂ hp₃ h₃₂ t₀ ht₀ ht₀1
      refine le_trans ?_ (le_max_right _ _)
      rw [abs_sub_le_iff]
      constructor
      · linarith
      · linarith
  /- ## Assembly: dichotomy on the ambient boundedness at the base point. -/
  by_cases hb : BddAbove ((fun v => v p₃) '' greenFamily p₁) ∧
      BddAbove ((fun v => v p₃) '' greenFamily p₂)
  · -- Ambient-hyperbolic regime: both piece families are dominated, at the
    -- base point, by the corresponding ambient envelopes.
    refine ⟨greenEnvelope p₁ p₃ + greenEnvelope p₂ p₃, fun t ht ht1 => ?_⟩
    have h1 := hPGle p₁ p₃ hp₁ hp₃ hb.1 t ht ht1
    have h2 := hPGle p₂ p₃ hp₂ hp₃ hb.2 t ht ht1
    have h3 := hPGnonneg p₁ p₃ hp₁ hp₃ h₃₁ t ht ht1
    have h4 := hPGnonneg p₂ p₃ hp₂ hp₃ h₃₂ t ht ht1
    rw [abs_sub_le_iff]
    constructor
    · linarith
    · linarith
  · -- RESIDUAL CORE (the C-SYM wall): the ambient Perron family is unbounded
    -- at `p₃` for at least one of the two poles (the non-hyperbolic regime,
    -- covering compact `M` and ambient-parabolic noncompact `M`); both piece
    -- Green's functions then increase to `+∞` at `p₃` along the exhaustion,
    -- and the shrink-uniform boundedness of their difference for SMALL shrink
    -- parameters is the genuine content of approximate Green symmetry
    -- (`|M₁(t) − M₂(t)| = O(1)`, capacity additivity of the Robin heights).
    -- No soft (Harnack/monotonicity/per-candidate) argument can close it; it
    -- requires either a surface Green-identity (Stokes/flux on chart annuli)
    -- or the universal-cover transfer.
    exact tail (pieceGreen_drift_bound_core D₀ hp₁ hp₂ hp₃ hne h₃₁ h₃₂
      (not_and_or.mp hb))

/-- The shrink-uniform master bound: around two marked points off a closed coordinate
disk there are pole radii, with doubled closed chart balls avoiding the disk and each
other, and a constant bounding the dipole difference of the Green's functions of every
sufficiently shrunken piece outside the two pole balls — by the interior and growth
estimates, the chain Harnack comparison pinned at the drift base point, and the
one-sided extension bound. -/
private theorem bipolarGreen_aux1 (D₀ : CoordDisk M) {p₁ p₂ : M}
    (hp₁ : p₁ ∉ D₀.closedCarrier) (hp₂ : p₂ ∉ D₀.closedCarrier) (hne : p₁ ≠
        p₂) :
    ∃ r₁ r₂ C₀ : ℝ, 0 < r₁ ∧ 0 < r₂ ∧ 1 ≤ C₀ ∧
      closedBall (chartAt ℂ p₁ p₁) (2 * r₁) ⊆ (chartAt ℂ p₁).target ∧
      closedBall (chartAt ℂ p₂ p₂) (2 * r₂) ⊆ (chartAt ℂ p₂).target ∧
      (∀ w ∈ closedBall (chartAt ℂ p₁ p₁) (2 * r₁),
        (chartAt ℂ p₁).symm w ∉ D₀.closedCarrier ∧ (chartAt ℂ p₁).symm w ≠ p₂) ∧
      (∀ w ∈ closedBall (chartAt ℂ p₂ p₂) (2 * r₂),
        (chartAt ℂ p₂).symm w ∉ D₀.closedCarrier ∧
          (chartAt ℂ p₂).symm w ∉
            (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) (2 * r₁)) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht1 : t ≤ 1, t ≤ 1 / 4 → ∀ x : M,
        x ∉ (chartAt ℂ p₁).source ∩ ⇑(chartAt ℂ p₁) ⁻¹' ball (chartAt ℂ p₁
            p₁) r₁ →
        x ∉ (chartAt ℂ p₂).source ∩ ⇑(chartAt ℂ p₂) ⁻¹' ball (chartAt ℂ p₂
            p₂) r₂ →
        |pieceGreen (D₀.shrink t ht ht1).compl p₁ x -
          pieceGreen (D₀.shrink t ht ht1).compl p₂ x| ≤ C₀ := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Plane-side helper: transfer of subharmonicity along a pointwise equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## Constancy propagation on a preconnected open set from an interior maximum. -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ z ∈ Ω, w z ≤ w xm) → ∀ z ∈ Ω, w z = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {z | z ∈ Ω ∧ w z = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hmax' : ∀ u ∈ Ω, w u ≤ w z := fun u hu => (hmax u hu).trans_eq hzw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hzΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu.trans hzw⟩
    have hto : IsOpen {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hcont : ContinuousAt w z := (hwsub z hzΩ).continuousAt
      filter_upwards [hcont.eventually_ne hzw, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu⟩
    have hsub : Ω ⊆ {z | z ∈ Ω ∧ w z = w xm} ∪ {z | z ∈ Ω ∧ w z ≠ w xm} := by
      intro z hz
      by_cases hzw : w z = w xm
      · exact Or.inl ⟨hz, hzw⟩
      · exact Or.inr ⟨hz, hzw⟩
    have hdisj : Disjoint {z | z ∈ Ω ∧ w z = w xm} {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro z ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun z hz => (hres hz).2
  /- ## Maximum principle on an open set `Ω ≠ univ` with compact exceptional set. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ z ∈ Ω, z ∉ Kc → w z ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ z ∈ Ω, w z ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ z ∈ Ω, w z ≤ w xm := by
      intro z hz
      by_cases hzK : z ∈ Kc
      · exact hxmax ⟨subset_closure hz, hzK⟩
      · exact (hout z hz hzK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun z hz => hwsub z (hCcΩ hz)) (fun z hz => hall z (hCcΩ hz))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    haveI hne2 : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz => (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz => (hf0 _ ((hρsub hz).2)).symm
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Subharmonicity at a point transfers between the surface and an open piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnety : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnety := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnety]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnety).target :=
      e'.map_subtype_source hnety hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hnety).symm)
        (e'.subtypeRestr hnety).target := e'.subtypeRestr_symm_eqOn hnety
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnety).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw => (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw => (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnety).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnety), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnety).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have mapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## Affine images of harmonic functions are harmonic. -/
  have mharmAffine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y => a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ => c) =
        (fun y => a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  have hmemSph : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      sphere c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' sphere c s ↔ z ∈ e.source ∧ dist (e z) c = s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_sphere.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_sphere.2 hzd, e.left_inv hzs⟩
  /- ## Per-candidate interior bound ([M] (18)): a compactly supported candidate is
  bounded on an open set avoiding the inner pole disk by its inner-circle maximum. -/
  have interiorBd : ∀ (p : M) (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      ∀ (Wo : Set M), IsOpen Wo →
      ∀ (vE : M → ℝ) (KE : Set M) (m : ℝ), 0 ≤ m →
        MSubharmonicOn vE {p}ᶜ → ContinuousOn vE {p}ᶜ → IsCompact KE → KE ⊆ Wo →
        (∀ y, y ∉ KE → vE y = 0) →
        (∀ z ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (rr / 2), vE z ≤ m) →
        ∀ y ∈ Wo ∩ ((chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (rr / 2))ᶜ,
          vE y ≤ m := by
    intro p rr hrr htgt Wo hWoOpen vE KE m hm0 hvsub hvcont hKE hKEW hKE0 hcirc
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    set Dh : Set M := ep.symm '' closedBall cp (rr / 2) with hDh
    have hpsrc : p ∈ ep.source := mem_chart_source ℂ p
    have hpDh : p ∈ Dh :=
      ⟨cp, mem_closedBall_self (by linarith only [hrr]), ep.left_inv hpsrc⟩
    set Ω : Set M := Wo ∩ Dhᶜ with hΩdef
    have hDhcomp : IsCompact Dh := (isCompact_closedBall _ _).image_of_continuousOn
      (ep.continuousOn_symm.mono
        ((closedBall_subset_closedBall (by linarith only [hrr])).trans htgt))
    have hΩopen : IsOpen Ω := hWoOpen.inter hDhcomp.isClosed.isOpen_compl
    have hΩne : Ω ≠ Set.univ := by
      intro hcon
      have hpΩ : p ∈ Ω := by rw [hcon]; trivial
      exact hpΩ.2 hpDh
    have hΩp : Ω ⊆ {p}ᶜ := fun z hz => Set.mem_compl_singleton_iff.2
      (fun hcon => hz.2 (hcon ▸ hpDh))
    apply maxPrin Ω vE m KE hΩopen hΩne (fun z hz => hvsub z (hΩp hz)) hKE
    · intro z hz hzK
      rw [hKE0 z hzK]
      exact hm0
    · rintro z ⟨hzcl, hzΩ⟩
      by_cases hzW : z ∈ Wo
      · -- frontier point on the inner circle
        have hzDh : z ∈ Dh := by
          by_contra hzD
          exact hzΩ ⟨hzW, hzD⟩
        obtain ⟨w, hw, hwz⟩ := hzDh
        have hwt : w ∈ ep.target :=
          ((closedBall_subset_closedBall
            (by linarith only [hrr] : rr / 2 ≤ rr)).trans htgt) hw
        have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
        have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
        have hzle : dist (ep z) cp ≤ rr / 2 := by
          rw [hzval]
          exact mem_closedBall.1 hw
        have hzd : dist (ep z) cp = rr / 2 := by
          rcases lt_or_eq_of_le hzle with h | h
          · exfalso
            set O : Set M := ep.source ∩ ep ⁻¹' ball cp (rr / 2) with hO
            have hOopen : IsOpen O := ep.isOpen_inter_preimage isOpen_ball
            have hzO : z ∈ O := ⟨hzsrc, by rw [Set.mem_preimage]; exact mem_ball.2 h⟩
            have hOD : O ⊆ Dh := by
              rintro q ⟨hq1, hq2⟩
              rw [Set.mem_preimage] at hq2
              exact ⟨ep q, ball_subset_closedBall hq2, ep.left_inv hq1⟩
            obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hzcl O hOopen hzO
            exact hqΩ.2 (hOD hqO)
          · exact h
        have hzΓ : z ∈ ep.symm '' sphere cp (rr / 2) :=
          ⟨ep z, mem_sphere.2 hzd, ep.left_inv hzsrc⟩
        have hznp : z ≠ p := by
          intro hcon
          rw [hcon] at hzd
          rw [← hcp, dist_self] at hzd
          have : (0 : ℝ) < rr / 2 := by linarith only [hrr]
          rw [← hzd] at this
          exact lt_irrefl _ this
        refine ⟨hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.2 hznp)), ?_⟩
        exact hcirc z hzΓ
      · -- frontier point off the open set: the candidate vanishes on a neighborhood
        have hzK : z ∉ KE := fun h => hzW (hKEW h)
        have hev : vE =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [hKE.isClosed.isOpen_compl.mem_nhds hzK] with q hq
          exact hKE0 q hq
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hKE0 z hzK]
        exact hm0
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dif_pos ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dif_neg]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## The zero function belongs to every piece Green family. -/
  have zeroFam : ∀ (P : Opens M) (p : M) (hp : p ∈ P),
      (fun _ : ↥P => (0 : ℝ)) ∈ greenFamily (⟨p, hp⟩ : ↥P) := by
    intro P p hp
    haveI : Nonempty ↥P := ⟨⟨p, hp⟩⟩
    refine ⟨fun z _ => (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt,
      continuousOn_const, ⟨∅, isCompact_empty, Set.empty_ne_univ, fun z _ => rfl⟩,
      ⟨0, ?_⟩⟩
    have hcont : ContinuousAt (poleCoord (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) := by
      have h1 : ContinuousAt (chartAt ℂ (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) :=
        (chartAt ℂ (⟨p, hp⟩ : ↥P)).continuousAt (mem_chart_source ℂ _)
      exact h1.sub continuousAt_const
    have h0 : poleCoord (⟨p, hp⟩ : ↥P) (⟨p, hp⟩ : ↥P) = 0 := sub_self _
    have hev : ∀ᶠ z in 𝓝 (⟨p, hp⟩ : ↥P), ‖poleCoord (⟨p, hp⟩ : ↥P) z‖ ≤ 1
        := by
      have h2 := hcont.tendsto
      rw [h0] at h2
      have h3 : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ one_pos
      filter_upwards [h2 h3] with z hz
      rw [← dist_zero_right]
      exact mem_closedBall.1 hz
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog := Real.log_nonpos (norm_nonneg _) hz
    simpa using hlog
  /- ## Zero extension of a piece candidate to the surface. -/
  have extendC : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (v : ↥P → ℝ),
      v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
      ∃ (vE : M → ℝ) (KE : Set M) (Cv : ℝ),
        (∀ z : ↥P, vE z = v z) ∧ MSubharmonicOn vE {p}ᶜ ∧ ContinuousOn vE {p}ᶜ ∧
        IsCompact KE ∧ KE ⊆ (P : Set M) ∧ (∀ y, y ∉ KE → vE y = 0) ∧
        ∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv := by
    intro P p hp v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y => if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dif_pos z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dif_pos hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dif_neg hyP]
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u => (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) = 𝓝 y :=
          hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem => hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem => hyP (hKwsub hmem)) (fun z hz => hKwzero z hz)
    refine ⟨w, Kw, C, hwval, hwsub, hwcont, hKwcomp, hKwsub, hKwzero, ?_⟩
    rw [← mapval P p hp, Filter.eventually_map]
    filter_upwards [hC] with z hz
    have hpc : poleCoord (⟨p, hp⟩ : ↥P) z = poleCoord p (z : M) := rfl
    rw [hwval z, ← hpc]
    exact hz
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    haveI := hcs
    haveI := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon => hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z => pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  have pgnonneg : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ≠ p → 0 ≤ pieceGreen P p y := by
    intro P p hp hcs hnc hGF y hyp
    haveI := hcs
    haveI := hnc
    by_cases hy : y ∈ P
    · rw [pgval P p hp y hy]
      exact (greenEnvelope_pos hGF _
        (fun hcon => hyp (congrArg Subtype.val hcon))).le
    · rw [pgzero P p y hy]
  /- ## Growth estimate ([M] (5)): a candidate gains at most `log 2` from the
  pole circle to the half circle, by the `ε`-excised annulus maximum principle. -/
  have growth : ∀ (p : M) (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      ∀ (vE : M → ℝ) (Cv MoV : ℝ),
        MSubharmonicOn vE {p}ᶜ → ContinuousOn vE {p}ᶜ →
        (∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv) →
        (∀ z ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr, vE z ≤ MoV) →
        ∀ y ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) (rr / 2),
          vE y ≤ MoV + Real.log 2 := by
    intro p rr hrr htgt vE Cv MoV hvsub hvcont hCv hMoV y hyΓ
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    have hpsrc : p ∈ ep.source := mem_chart_source ℂ p
    have hcptgt : cp ∈ ep.target := by rw [hcp]; exact ep.map_source hpsrc
    have hsymcp : ep.symm cp = p := by rw [hcp]; exact ep.left_inv hpsrc
    have hsphtgt : ∀ ρ : ℝ, ρ ≤ rr → sphere cp ρ ⊆ ep.target := fun ρ hρ =>
      sphere_subset_closedBall.trans ((closedBall_subset_closedBall hρ).trans htgt)
    obtain ⟨wy, hwy, hwyy⟩ := hyΓ
    have hwyt : wy ∈ ep.target := hsphtgt _ (by linarith only [hrr]) hwy
    have hysrc : y ∈ ep.source := hwyy ▸ ep.map_target hwyt
    have hyval : ep y = wy := by rw [← hwyy, ep.right_inv hwyt]
    have hydist : dist (ep y) cp = rr / 2 := by rw [hyval]; exact mem_sphere.1 hwy
    have hyne : y ≠ p := by
      intro hcon
      rw [hcon, ← hcp, dist_self] at hydist
      have h0 : (0 : ℝ) < rr / 2 := by linarith only [hrr]
      rw [← hydist] at h0
      exact lt_irrefl _ h0
    -- the chart-ball pole bound
    obtain ⟨Nv, hNvnhds, hNv⟩ := (eventually_nhdsWithin_iff.mp hCv).exists_mem
    have hprev : ep.target ∩ ep.symm ⁻¹' Nv ∈ 𝓝 cp := by
      have h1 : ContinuousAt ep.symm cp := ep.continuousAt_symm hcptgt
      have h3 : ep.symm ⁻¹' Nv ∈ 𝓝 cp := h1.preimage_mem_nhds (hsymcp ▸ hNvnhds)
      exact Filter.inter_mem (ep.open_target.mem_nhds hcptgt) h3
    obtain ⟨σ₀, hσ₀pos, hσ₀sub⟩ := nhds_basis_closedBall.mem_iff.1 hprev
    have hCbound : ∀ z : M, z ∈ ep.source → ep z ∈ closedBall cp σ₀ → z ≠ p →
        vE z + Real.log (dist (ep z) cp) ≤ Cv := by
      intro z hzs hzball hzne
      have h3 : ep z ∈ ep.symm ⁻¹' Nv := (hσ₀sub hzball).2
      have h4 : z ∈ Nv := by rwa [Set.mem_preimage, ep.left_inv hzs] at h3
      have h5 := hNv z h4 (Set.mem_compl_singleton_iff.mpr hzne)
      have h6 : ‖poleCoord p z‖ = dist (ep z) cp := by
        simp only [poleCoord, ← hep, ← hcp, dist_eq_norm]
      rwa [h6] at h5
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    refine le_of_forall_pos_le_add ?_
    intro ε' hε'
    set ε : ℝ := ε' / Real.log 2 with hε
    have hεpos : 0 < ε := div_pos hε' hlog2
    have hεlog : ε * Real.log 2 = ε' := by
      rw [hε]
      exact div_mul_cancel₀ ε' hlog2.ne'
    set Q : ℝ := (MoV - Cv + (1 + ε) * Real.log rr) / ε with hQ
    set σ : ℝ := min (min σ₀ (rr / 4)) (Real.exp Q) with hσ
    have hσpos : 0 < σ :=
      lt_min (lt_min hσ₀pos (by linarith only [hrr])) (Real.exp_pos Q)
    have hσσ₀ : σ ≤ σ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hσR4 : σ ≤ rr / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) :=
            Real.log_le_log hσpos (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hεQ : ε * Q = MoV - Cv + (1 + ε) * Real.log rr := by
      rw [hQ, mul_comm]
      exact div_mul_cancel₀ _ hεpos.ne'
    -- the excised annulus region
    set Ωσ : Set M := ep.symm '' (ball cp rr \ closedBall cp σ) with hΩσ
    have hΩσsub : ball cp rr \ closedBall cp σ ⊆ ep.target :=
      (Set.diff_subset.trans ball_subset_closedBall).trans htgt
    have hΩσopen : IsOpen Ωσ := by
      rw [hΩσ, himg ep _ hΩσsub]
      exact ep.continuousOn.isOpen_inter_preimage ep.open_source
        (isOpen_ball.sdiff isClosed_closedBall)
    have hΩσmem : ∀ z ∈ Ωσ, z ∈ ep.source ∧ σ < dist (ep z) cp ∧
        dist (ep z) cp < rr := by
      intro z hz
      rw [hΩσ, himg ep _ hΩσsub] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall] at hz2
      exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
    have hΩσmem' : ∀ z : M, z ∈ ep.source → σ < dist (ep z) cp →
        dist (ep z) cp < rr → z ∈ Ωσ := by
      intro z hz1 hz2 hz3
      rw [hΩσ, himg ep _ hΩσsub]
      refine ⟨hz1, ?_⟩
      rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall]
      exact ⟨hz3, not_le.2 hz2⟩
    have hpΩσ : p ∉ Ωσ := by
      intro hcon
      obtain ⟨-, h2, -⟩ := hΩσmem p hcon
      rw [← hcp, dist_self] at h2
      exact absurd h2 (not_lt.2 hσpos.le)
    have hΩσne : Ωσ ≠ Set.univ := by
      intro hcon
      apply hpΩσ
      rw [hcon]
      trivial
    set Kσ : Set M := ep.symm '' (closedBall cp rr \ ball cp σ) with hKσ
    have hKσcomp : IsCompact Kσ :=
      ((isCompact_closedBall cp rr).diff isOpen_ball).image_of_continuousOn
        (ep.continuousOn_symm.mono (Set.diff_subset.trans htgt))
    have hΩσKσ : Ωσ ⊆ Kσ :=
      Set.image_mono (fun w hw => ⟨ball_subset_closedBall hw.1,
        fun h => hw.2 (ball_subset_closedBall h)⟩)
    -- harmonicity and continuity of the logarithmic barrier
    have hepatlas : ep ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
      rw [hep]
      exact IsManifold.chart_mem_maximalAtlas p
    have hbharm : ∀ z : M, z ∈ ep.source → ep z ≠ cp →
        MHarmonicAt (fun q => Real.log (dist (ep q) cp)) z := by
      intro z hzs hzne
      have h1 : MHarmonicAt (fun q => Real.log (dist (ep q) cp)) z ↔
          HarmonicAt ((fun q => Real.log (dist (ep q) cp)) ∘ ep.symm) (ep z) :=
        mharmonicAt_iff_of_mem_maximalAtlas hepatlas hzs
      rw [h1]
      have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - cp‖) (ep z) := by
        apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - cp)
        · exact analyticAt_id.sub analyticAt_const
        · exact sub_ne_zero.2 hzne
      have heqv : (fun w : ℂ => Real.log ‖w - cp‖) =ᶠ[𝓝 (ep z)]
          ((fun q => Real.log (dist (ep q) cp)) ∘ ep.symm) := by
        filter_upwards [ep.open_target.mem_nhds (ep.map_source hzs)] with w hw
        simp only [Function.comp_apply, ep.right_inv hw, dist_eq_norm]
      exact (harmonicAt_congr_nhds heqv).1 hharm
    have hbcont : ∀ z : M, z ∈ ep.source → ep z ≠ cp →
        ContinuousAt (fun q => Real.log (dist (ep q) cp)) z := by
      intro z hzs hzne
      have h2 : ContinuousAt ep z := ep.continuousAt hzs
      have h3 : dist (ep z) cp ≠ 0 := (dist_pos.2 hzne).ne'
      exact (h2.dist continuousAt_const).log h3
    have hvCA : ∀ z : M, z ≠ p → ContinuousAt vE z := fun z hz =>
      hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.2 hz))
    -- the competitor and its subharmonicity
    set Wf : M → ℝ :=
      fun q => vE q + (1 + ε) * (Real.log (dist (ep q) cp) - Real.log rr) with hWf
    have hWfsub : MSubharmonicOn Wf Ωσ := by
      intro z hz
      obtain ⟨hz1, hz2, hz3⟩ := hΩσmem z hz
      have hzne : ep z ≠ cp := by
        intro hcon
        rw [hcon, dist_self] at hz2
        exact absurd hz2 (not_lt.2 hσpos.le)
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp] at hzne
        exact hzne rfl
      have hu : MHarmonicAt
          (fun q => (-(1 + ε)) * Real.log (dist (ep q) cp) + (1 + ε) * Real.log rr)
          z := mharmAffine _ z _ _ (hbharm z hz1 hzne)
      have h7 := (hvsub z (Set.mem_compl_singleton_iff.mpr hznep)).sub_mharmonicAt hu
      have h9 : Wf = fun q => vE q -
          ((-(1 + ε)) * Real.log (dist (ep q) cp) + (1 + ε) * Real.log rr) := by
        funext q
        simp only [hWf]
        ring
      rw [h9]
      exact h7
    -- boundary control on the two circles
    have hWfbd : ∀ z ∈ closure Ωσ \ Ωσ, ContinuousAt Wf z ∧ Wf z ≤ MoV := by
      rintro z ⟨hzcl, hzΩ⟩
      have hzK : z ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hzcl
      obtain ⟨w, ⟨hw1, hw2⟩, hwz⟩ := hzK
      have hwt : w ∈ ep.target := htgt hw1
      have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
      have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
      have hzd1 : σ ≤ dist (ep z) cp := by
        rw [hzval]
        exact not_lt.1 (fun h => hw2 (mem_ball.2 h))
      have hzd2 : dist (ep z) cp ≤ rr := by rw [hzval]; exact mem_closedBall.1 hw1
      have hzne : ep z ≠ cp := by
        intro hcon
        rw [hcon, dist_self] at hzd1
        exact absurd hzd1 (not_le.2 hσpos)
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp] at hzne
        exact hzne rfl
      have hcont : ContinuousAt Wf z := by
        rw [hWf]
        exact (hvCA z hznep).add
          (continuousAt_const.mul ((hbcont z hzsrc hzne).sub continuousAt_const))
      refine ⟨hcont, ?_⟩
      have hdisj : dist (ep z) cp = σ ∨ dist (ep z) cp = rr := by
        rcases lt_or_eq_of_le hzd1 with h1 | h1
        · rcases lt_or_eq_of_le hzd2 with h2 | h2
          · exact absurd (hΩσmem' z hzsrc h1 h2) hzΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      rcases hdisj with hzd | hzd
      · have hσball : ep z ∈ closedBall cp σ₀ := by
          rw [mem_closedBall, hzd]
          exact hσσ₀
        have hvz : vE z + Real.log σ ≤ Cv := by
          have h5 := hCbound z hzsrc hσball hznep
          rwa [hzd] at h5
        rw [hWf]
        simp only
        rw [hzd]
        have h8 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hεpos.le
        rw [hεQ] at h8
        nlinarith only [hvz, h8]
      · have hzΓ : z ∈ ep.symm '' sphere cp rr :=
          ⟨ep z, mem_sphere.2 hzd, ep.left_inv hzsrc⟩
        rw [hWf]
        simp only
        rw [hzd, sub_self, mul_zero, add_zero]
        exact hMoV z hzΓ
    have hWfle : ∀ z ∈ Ωσ, Wf z ≤ MoV := by
      apply maxPrin Ωσ Wf MoV Kσ hΩσopen hΩσne hWfsub hKσcomp ?_ hWfbd
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    -- evaluate on the half circle
    have hyΩσ : y ∈ Ωσ := by
      apply hΩσmem' y hysrc
      · rw [hydist]; linarith only [hσR4, hrr]
      · rw [hydist]; linarith only [hrr]
    have h9 := hWfle y hyΩσ
    rw [hWf] at h9
    simp only at h9
    rw [hydist] at h9
    have h10 : Real.log (rr / 2) = Real.log rr - Real.log 2 :=
      Real.log_div hrr.ne' two_ne_zero
    rw [h10] at h9
    have h11 : (1 + ε) * (Real.log rr - Real.log 2 - Real.log rr) =
        -(1 + ε) * Real.log 2 := by
      ring
    rw [h11] at h9
    have h12 : (1 + ε) * Real.log 2 = Real.log 2 + ε' := by
      rw [add_mul, one_mul, hεlog]
    linarith only [h9, h12]
  /- ## The per-piece pole bound: envelope interior bound and growth estimate. -/
  have poleBound : ∀ (P : Opens M), ConnectedSpace ↥P → NoncompactSpace ↥P →
      ∀ (p : M) (hp : p ∈ P), HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ (rr : ℝ), 0 < rr →
      closedBall (chartAt ℂ p p) rr ⊆ (chartAt ℂ p).target →
      (∀ y ∈ (chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) rr, y ∈ P) →
      ∃ (Nt : ℝ) (xout : M),
        xout ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr ∧
        pieceGreen P p xout = Nt ∧
        (∀ y ∈ (chartAt ℂ p).symm '' sphere (chartAt ℂ p p) rr,
          pieceGreen P p y ≤ Nt) ∧
        ∀ y ∈ (P : Set M) ∩
            ((chartAt ℂ p).symm '' closedBall (chartAt ℂ p p) (rr / 2))ᶜ,
          pieceGreen P p y ≤ Nt + Real.log 2 := by
    intro P hcs hnc p hp hGF rr hrr htgt hcarP
    haveI := hcs
    haveI := hnc
    have hIB := interiorBd p rr hrr htgt (P : Set M) P.2
    have hGR := growth p rr hrr htgt
    have hBdd := (mharmonicOn_greenEnvelope hGF).2
    set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p with hep
    set cp : ℂ := ep p with hcp
    -- reading points of the chart circles
    have hΓread : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → ∀ z ∈ ep.symm '' sphere cp ρ,
        z ∈ ep.source ∧ dist (ep z) cp = ρ ∧ z ≠ p ∧ z ∈ P := by
      intro ρ hρ0 hρrr z hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hwt : w ∈ ep.target :=
        (sphere_subset_closedBall.trans
          ((closedBall_subset_closedBall hρrr).trans htgt)) hw
      have hzsrc : z ∈ ep.source := hwz ▸ ep.map_target hwt
      have hzval : ep z = w := by rw [← hwz, ep.right_inv hwt]
      have hzd : dist (ep z) cp = ρ := by rw [hzval]; exact mem_sphere.1 hw
      have hznep : z ≠ p := by
        intro hcon
        rw [hcon, ← hcp, dist_self] at hzd
        rw [← hzd] at hρ0
        exact lt_irrefl _ hρ0
      have hzP : z ∈ P := hcarP z
        ⟨w, closedBall_subset_closedBall hρrr (sphere_subset_closedBall hw), hwz⟩
      exact ⟨hzsrc, hzd, hznep, hzP⟩
    have hΓcomp : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr → IsCompact (ep.symm '' sphere cp ρ) ∧
        (ep.symm '' sphere cp ρ).Nonempty := by
      intro ρ hρ0 hρrr
      constructor
      · exact (isCompact_sphere cp ρ).image_of_continuousOn
          (ep.continuousOn_symm.mono (sphere_subset_closedBall.trans
            ((closedBall_subset_closedBall hρrr).trans htgt)))
      · exact (NormedSpace.sphere_nonempty.2 hρ0.le).image _
    have hgcont : ∀ ρ : ℝ, 0 < ρ → ρ ≤ rr →
        ContinuousOn (pieceGreen P p) (ep.symm '' sphere cp ρ) := by
      intro ρ hρ0 hρrr z hz
      obtain ⟨-, -, hznep, hzP⟩ := hΓread ρ hρ0 hρrr z hz
      exact ((pgharm P p hp hcs hnc hGF z hzP hznep).continuousAt).continuousWithinAt
    have hΓoutC := hΓcomp rr hrr le_rfl
    have hΓinC := hΓcomp (rr / 2) (by linarith only [hrr]) (by linarith only [hrr])
    obtain ⟨xout, hxoutΓ, hxoutmax⟩ :=
      hΓoutC.1.exists_isMaxOn hΓoutC.2 (hgcont rr hrr le_rfl)
    obtain ⟨xin, hxinΓ, hxinmax⟩ :=
      hΓinC.1.exists_isMaxOn hΓinC.2
        (hgcont (rr / 2) (by linarith only [hrr]) (by linarith only [hrr]))
    set Nt : ℝ := pieceGreen P p xout with hNt
    set Mt : ℝ := pieceGreen P p xin with hMt
    have hMtpos : 0 < Mt := by
      obtain ⟨-, -, hnep2, hP2⟩ := hΓread (rr / 2) (by linarith only [hrr])
        (by linarith only [hrr]) xin hxinΓ
      rw [hMt, pgval P p hp xin hP2]
      exact greenEnvelope_pos hGF _ (fun hcon => hnep2 (congrArg Subtype.val hcon))
    -- per-candidate circle bounds against the envelope maxima
    have hcircGen : ∀ (ρ : ℝ) (hρ0 : 0 < ρ) (hρrr : ρ ≤ rr) (xm : M)
        (hxm : IsMaxOn (pieceGreen P p) (ep.symm '' sphere cp ρ) xm)
        (v : ↥P → ℝ), v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
        ∀ (vE : M → ℝ), (∀ z : ↥P, vE z = v z) →
        ∀ z ∈ ep.symm '' sphere cp ρ, vE z ≤ pieceGreen P p xm := by
      intro ρ hρ0 hρrr xm hxm v hv vE hvEval z hz
      obtain ⟨-, -, hznep, hzP⟩ := hΓread ρ hρ0 hρrr z hz
      calc vE z = v ⟨z, hzP⟩ := hvEval ⟨z, hzP⟩
        _ ≤ greenEnvelope (⟨p, hp⟩ : ↥P) ⟨z, hzP⟩ :=
            le_csSup (hBdd _ (fun hcon => hznep (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
        _ = pieceGreen P p z := (pgval P p hp z hzP).symm
        _ ≤ pieceGreen P p xm := hxm hz
    -- envelope interior bound on the piece minus the inner disk
    have hIntEnv : ∀ y ∈ (P : Set M) ∩ (ep.symm '' closedBall cp (rr / 2))ᶜ,
        pieceGreen P p y ≤ Mt := by
      intro y hy
      have hyP : y ∈ P := hy.1
      rw [pgval P p hp y hyP]
      simp only [greenEnvelope]
      refine csSup_le ⟨0, (fun _ : ↥P => (0 : ℝ)), zeroFam P p hp, rfl⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P p hp v hv
      have hgoal : vE y ≤ Mt := by
        apply hIB vE KE Mt hMtpos.le hvEsub hvEcont hKEc hKEP hKE0 ?_ y hy
        exact hcircGen (rr / 2) (by linarith only [hrr]) (by linarith only [hrr])
          xin hxinmax v hv vE hvEval
      have h1 : v ⟨y, hyP⟩ = vE y := (hvEval ⟨y, hyP⟩).symm
      rw [← h1] at hgoal
      exact hgoal
    -- envelope growth estimate on the half circle
    have hgrowEnv : ∀ y ∈ ep.symm '' sphere cp (rr / 2),
        pieceGreen P p y ≤ Nt + Real.log 2 := by
      intro y hy
      obtain ⟨-, -, hynep, hyP⟩ := hΓread (rr / 2) (by linarith only [hrr])
        (by linarith only [hrr]) y hy
      rw [pgval P p hp y hyP]
      simp only [greenEnvelope]
      refine csSup_le ⟨0, (fun _ : ↥P => (0 : ℝ)), zeroFam P p hp, rfl⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P p hp v hv
      have hgoal : vE y ≤ Nt + Real.log 2 := by
        apply hGR vE Cv Nt hvEsub hvEcont hCv ?_ y hy
        intro z hz
        have h2 := hcircGen rr hrr le_rfl xout hxoutmax v hv vE hvEval z hz
        rw [← hNt] at h2
        exact h2
      have h1 : v ⟨y, hyP⟩ = vE y := (hvEval ⟨y, hyP⟩).symm
      rw [← h1] at hgoal
      exact hgoal
    have hMtNt : Mt ≤ Nt + Real.log 2 := by
      rw [hMt]
      exact hgrowEnv xin hxinΓ
    refine ⟨Nt, xout, hxoutΓ, hNt.symm, ?_, ?_⟩
    · intro y hy
      have h3 := hxoutmax hy
      rw [← hNt] at h3
      exact h3
    · intro y hy
      exact le_trans (hIntEnv y hy) hMtNt
  /- ## The one-sided extension bound: away from both pole disks, every candidate
  for one pole is dominated by the other Green's function plus the circle constant. -/
  have side : ∀ (P : Opens M), ConnectedSpace ↥P → NoncompactSpace ↥P →
      ∀ (pa : M) (hpa : pa ∈ P) (pb : M) (hpb : pb ∈ P),
      HasGreenFunction (⟨pa, hpa⟩ : ↥P) → HasGreenFunction (⟨pb, hpb⟩ : ↥P) →
      ∀ (ra rb Cc : ℝ), 0 < ra → 0 < rb → 0 ≤ Cc →
      closedBall (chartAt ℂ pa pa) ra ⊆ (chartAt ℂ pa).target →
      closedBall (chartAt ℂ pb pb) rb ⊆ (chartAt ℂ pb).target →
      (∀ y ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) ra, y ∈ P) →
      (∀ y ∈ (chartAt ℂ pb).symm '' closedBall (chartAt ℂ pb pb) rb, y ∈ P) →
      (∀ y ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) ra,
        y ∉ (chartAt ℂ pb).symm '' closedBall (chartAt ℂ pb pb) rb) →
      (∀ z ∈ (chartAt ℂ pa).symm '' sphere (chartAt ℂ pa pa) ra,
        pieceGreen P pa z - pieceGreen P pb z ≤ Cc) →
      ∀ x, x ∈ P →
        x ∉ (chartAt ℂ pa).source ∩ chartAt ℂ pa ⁻¹' ball (chartAt ℂ pa pa) ra →
        x ∉ (chartAt ℂ pb).source ∩ chartAt ℂ pb ⁻¹' ball (chartAt ℂ pb pb) rb →
        pieceGreen P pa x ≤ pieceGreen P pb x + Cc := by
    intro P hcs hnc pa hpa pb hpb hGa hGb ra rb Cc hra hrb hCc0 htga htgb hcarPa
      hcarPb hdisjab hcirc x hxP hxVa hxVb
    haveI := hcs
    haveI := hnc
    have hBdda := (mharmonicOn_greenEnvelope hGa).2
    set ea : OpenPartialHomeomorph M ℂ := chartAt ℂ pa with hea
    set ca : ℂ := ea pa with hca
    set eb : OpenPartialHomeomorph M ℂ := chartAt ℂ pb with heb
    set cb : ℂ := eb pb with hcb
    have hpasrc : pa ∈ ea.source := mem_chart_source ℂ pa
    have hpbsrc : pb ∈ eb.source := mem_chart_source ℂ pb
    have hpaDa : pa ∈ ea.symm '' closedBall ca ra :=
      ⟨ca, mem_closedBall_self hra.le, by rw [hca]; exact ea.left_inv hpasrc⟩
    have hpbDb : pb ∈ eb.symm '' closedBall cb rb :=
      ⟨cb, mem_closedBall_self hrb.le, by rw [hcb]; exact eb.left_inv hpbsrc⟩
    have hpanb : pa ≠ pb := fun hcon => hdisjab pa hpaDa (hcon ▸ hpbDb)
    have hgb_nonneg : ∀ z : M, z ≠ pb → 0 ≤ pieceGreen P pb z :=
      pgnonneg P pb hpb hcs hnc hGb
    have hgb_harm : ∀ z : M, z ∈ P → z ≠ pb → MHarmonicAt (pieceGreen P pb) z :=
      fun z h1 h2 => pgharm P pb hpb hcs hnc hGb z h1 h2
    have hsymcb : eb.symm cb = pb := by rw [hcb]; exact eb.left_inv hpbsrc
    -- per-candidate bound at the point `x`
    have percand : ∀ (v : ↥P → ℝ), v ∈ greenFamily (⟨pa, hpa⟩ : ↥P) →
        v ⟨x, hxP⟩ ≤ pieceGreen P pb x + Cc := by
      intro v hv
      obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
        extendC P pa hpa v hv
      -- bound for `vE` near `pb`
      have hvbCA : ContinuousAt vE pb :=
        hvEcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.2 hpanb.symm))
      set bv : ℝ := vE pb + 1 with hbv
      have hev : ∀ᶠ z in 𝓝 pb, vE z ≤ bv := by
        have h1 : vE pb < bv := by rw [hbv]; linarith only []
        filter_upwards [hvbCA (Iio_mem_nhds h1)] with z hz
        exact (Set.mem_Iio.1 hz).le
      have hcbt : cb ∈ eb.target := by rw [hcb]; exact eb.map_source hpbsrc
      have hprevb : eb.symm ⁻¹' {z | vE z ≤ bv} ∈ 𝓝 cb := by
        have h1 : ContinuousAt eb.symm cb := eb.continuousAt_symm hcbt
        exact h1.preimage_mem_nhds (hsymcb ▸ hev)
      obtain ⟨ρv, hρv, hρvsub⟩ := nhds_basis_closedBall.mem_iff.1 hprevb
      -- the harmonic extension across the pole `pb`
      obtain ⟨rP, hrP, hrPsub, h, hharm, hval⟩ := exists_harmonic_pole_extension hGb
      haveI hnety : Nonempty ↥P := ⟨⟨pb, hpb⟩⟩
      have hctb : chartAt ℂ (⟨pb, hpb⟩ : ↥P) = eb.subtypeRestr hnety :=
        Opens.chartAt_eq
      have hcenterb : chartAt ℂ (⟨pb, hpb⟩ : ↥P) (⟨pb, hpb⟩ : ↥P) = cb := by
        rw [hctb, eb.subtypeRestr_coe hnety, hcb]
        rfl
      rw [hcenterb] at hrPsub hharm hval
      have hhc : ContinuousOn h (closedBall cb (rP / 2)) :=
        hharm.continuousOn.mono (closedBall_subset_ball (by linarith only [hrP]))
      obtain ⟨wm, hwm, hwmmin⟩ := (isCompact_closedBall cb (rP / 2)).exists_isMinOn
        ⟨cb, mem_closedBall_self (by linarith only [hrP])⟩ hhc
      set mh : ℝ := h wm with hmh
      -- the excision radius
      set δ : ℝ := min (min (rP / 2) ρv) (min (rb / 2) (Real.exp (mh - bv))) with hδ
      have hδ0 : 0 < δ := lt_min (lt_min (by linarith only [hrP]) hρv)
        (lt_min (by linarith only [hrb]) (Real.exp_pos _))
      have hδrP : δ ≤ rP / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
      have hδρv : δ ≤ ρv := le_trans (min_le_left _ _) (min_le_right _ _)
      have hδrb : δ ≤ rb / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hδexp : δ ≤ Real.exp (mh - bv) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hlogδ : Real.log δ ≤ mh - bv := by
        calc Real.log δ ≤ Real.log (Real.exp (mh - bv)) := Real.log_le_log hδ0 hδexp
          _ = mh - bv := Real.log_exp _
      -- the δ-circle facts
      have hΓδ : ∀ z : M, z ∈ eb.source → dist (eb z) cb = δ →
          vE z ≤ bv ∧ bv ≤ pieceGreen P pb z ∧ z ≠ pb ∧ z ∈ P := by
        intro z hzs hzd
        have hzval : eb.symm (eb z) = z := eb.left_inv hzs
        have hznepb : z ≠ pb := by
          intro hcon
          rw [hcon, ← hcb, dist_self] at hzd
          rw [← hzd] at hδ0
          exact lt_irrefl _ hδ0
        have hzDb : z ∈ eb.symm '' closedBall cb rb :=
          ⟨eb z, mem_closedBall.2 (by rw [hzd]; linarith only [hδrb, hrb]), hzval⟩
        have hzP : z ∈ P := hcarPb z hzDb
        refine ⟨?_, ?_, hznepb, hzP⟩
        · have h1 : eb z ∈ closedBall cb ρv := by
            rw [mem_closedBall, hzd]
            exact hδρv
          have h2 := hρvsub h1
          rw [Set.mem_preimage, hzval] at h2
          exact h2
        · have hwball : eb z ∈ ball cb rP := by
            rw [mem_ball, hzd]
            linarith only [hδrP, hrP]
          have hwnc : eb z ≠ cb := by
            intro hcon
            rw [← dist_eq_zero] at hcon
            rw [hcon] at hzd
            rw [← hzd] at hδ0
            exact lt_irrefl _ hδ0
          have h2 := hval (eb z) ⟨hwball, by
            simp only [Set.mem_singleton_iff]
            exact hwnc⟩
          have hwtgt : eb z ∈ (chartAt ℂ (⟨pb, hpb⟩ : ↥P)).target := hrPsub hwball
          have hzsubval : ((chartAt ℂ (⟨pb, hpb⟩ : ↥P)).symm (eb z) : M) = z := by
            have heqO := eb.subtypeRestr_symm_eqOn hnety
            have h3 : eb.symm (eb z) =
                (Subtype.val ∘ (eb.subtypeRestr hnety).symm) (eb z) := by
              apply heqO
              rw [← hctb]
              exact hwtgt
            rw [hzval] at h3
            rw [hctb]
            exact h3.symm
          have h4 : (chartAt ℂ (⟨pb, hpb⟩ : ↥P)).symm (eb z) = (⟨z, hzP⟩ : ↥P) :=
            Subtype.ext hzsubval
          rw [h4] at h2
          have h5 : greenEnvelope (⟨pb, hpb⟩ : ↥P) ⟨z, hzP⟩ = h (eb z) - Real.log δ := by
            have h6 : ‖eb z - cb‖ = δ := by rw [← dist_eq_norm]; exact hzd
            rw [h6] at h2
            linarith only [h2]
          rw [pgval P pb hpb z hzP, h5]
          have h7 : mh ≤ h (eb z) := hwmmin (mem_closedBall.2 (by rw [hzd]; exact hδrP))
          linarith only [h7, hlogδ]
      -- the capped competitor on the excised region
      set Dδ : Set M := eb.symm '' closedBall cb δ with hDδ
      have hDδtgt : closedBall cb δ ⊆ eb.target :=
        (closedBall_subset_closedBall (by linarith only [hδrb, hrb])).trans htgb
      have hDδcomp : IsCompact Dδ := (isCompact_closedBall _ _).image_of_continuousOn
        (eb.continuousOn_symm.mono hDδtgt)
      have hpbDδ : pb ∈ Dδ := ⟨cb, mem_closedBall_self hδ0.le, hsymcb⟩
      have hDδVb : Dδ ⊆ eb.source ∩ eb ⁻¹' ball cb rb := by
        rintro z ⟨w, hw, hwz⟩
        have hwt : w ∈ eb.target := hDδtgt hw
        refine ⟨hwz ▸ eb.map_target hwt, ?_⟩
        rw [Set.mem_preimage, ← hwz, eb.right_inv hwt, mem_ball]
        have h1 := mem_closedBall.1 hw
        linarith only [h1, hδrb, hrb]
      set Da : Set M := ea.symm '' closedBall ca ra with hDa
      have hDacomp : IsCompact Da := (isCompact_closedBall _ _).image_of_continuousOn
        (ea.continuousOn_symm.mono htga)
      set Ω : Set M := (P : Set M) ∩ Daᶜ ∩ Dδᶜ with hΩdef
      have hΩopen : IsOpen Ω := (P.2.inter hDacomp.isClosed.isOpen_compl).inter
        hDδcomp.isClosed.isOpen_compl
      have hΩne : Ω ≠ Set.univ := by
        intro hcon
        have hpaΩ : pa ∈ Ω := by rw [hcon]; trivial
        exact hpaΩ.1.2 hpaDa
      set wc : M → ℝ := fun z => max (vE z - pieceGreen P pb z) 0 with hwc
      have hΩnepa : ∀ z ∈ Ω, z ≠ pa := fun z hz hcon => hz.1.2 (hcon ▸ hpaDa)
      have hΩnepb : ∀ z ∈ Ω, z ≠ pb := fun z hz hcon => hz.2 (hcon ▸ hpbDδ)
      have hwcsub : MSubharmonicOn wc Ω := by
        intro z hz
        have h1 : MSubharmonicAt (fun q => vE q - pieceGreen P pb q) z :=
          (hvEsub z (Set.mem_compl_singleton_iff.2 (hΩnepa z hz))).sub_mharmonicAt
            (hgb_harm z hz.1.1 (hΩnepb z hz))
        have h2 : MSubharmonicAt (fun _ : M => (0 : ℝ)) z :=
          (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt
        rw [hwc]
        exact h1.max h2
      have hwcout : ∀ z ∈ Ω, z ∉ KE → wc z ≤ Cc := by
        intro z hz hzK
        rw [hwc]
        simp only
        rw [hKE0 z hzK]
        have h1 : 0 ≤ pieceGreen P pb z := hgb_nonneg z (hΩnepb z hz)
        exact max_le (by linarith only [h1, hCc0]) hCc0
      have hwcfr : ∀ y ∈ closure Ω \ Ω, ContinuousAt wc y ∧ wc y ≤ Cc := by
        rintro y ⟨hycl, hyΩ⟩
        by_cases hyP : y ∈ P
        · by_cases hyDa : y ∈ Da
          · -- on the `pa` circle
            obtain ⟨w, hw, hwz⟩ := hyDa
            have hwt : w ∈ ea.target := htga hw
            have hysrc : y ∈ ea.source := hwz ▸ ea.map_target hwt
            have hyval : ea y = w := by rw [← hwz, ea.right_inv hwt]
            have hyled : dist (ea y) ca ≤ ra := by
              rw [hyval]
              exact mem_closedBall.1 hw
            have hyd : dist (ea y) ca = ra := by
              rcases lt_or_eq_of_le hyled with h1 | h1
              · exfalso
                have hOopen : IsOpen (ea.source ∩ ea ⁻¹' ball ca ra) :=
                  ea.isOpen_inter_preimage isOpen_ball
                have hyO : y ∈ ea.source ∩ ea ⁻¹' ball ca ra :=
                  ⟨hysrc, by rw [Set.mem_preimage]; exact mem_ball.2 h1⟩
                have hODa : ea.source ∩ ea ⁻¹' ball ca ra ⊆ Da := by
                  rintro q ⟨hq1, hq2⟩
                  rw [Set.mem_preimage] at hq2
                  exact ⟨ea q, ball_subset_closedBall hq2, ea.left_inv hq1⟩
                obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hycl _ hOopen hyO
                exact hqΩ.1.2 (hODa hqO)
              · exact h1
            have hyΓa : y ∈ ea.symm '' sphere ca ra :=
              ⟨ea y, mem_sphere.2 hyd, ea.left_inv hysrc⟩
            have hynepa : y ≠ pa := by
              intro hcon
              rw [hcon, ← hca, dist_self] at hyd
              rw [← hyd] at hra
              exact lt_irrefl _ hra
            have hynepb : y ≠ pb := fun hcon =>
              hdisjab y ⟨w, hw, hwz⟩ (by rw [hcon]; exact hpbDb)
            have hcg : ContinuousAt (pieceGreen P pb) y :=
              (hgb_harm y hyP hynepb).continuousAt
            have hcv : ContinuousAt vE y := hvEcont.continuousAt
              (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hynepa))
            refine ⟨by rw [hwc]; exact (hcv.sub hcg).max continuousAt_const, ?_⟩
            rw [hwc]
            simp only
            have h2 : vE y ≤ pieceGreen P pa y := by
              have h3 : v ⟨y, hyP⟩ ≤ greenEnvelope (⟨pa, hpa⟩ : ↥P) ⟨y, hyP⟩ :=
                le_csSup (hBdda _ (fun hcon => hynepa (congrArg Subtype.val hcon)))
                  ⟨v, hv, rfl⟩
              have h3' : vE y = v ⟨y, hyP⟩ := hvEval ⟨y, hyP⟩
              rw [h3', pgval P pa hpa y hyP]
              exact h3
            have h4 := hcirc y hyΓa
            exact max_le (by linarith only [h2, h4]) hCc0
          · -- on the `δ` circle
            have hyDδ : y ∈ Dδ := by
              by_contra hyD
              exact hyΩ ⟨⟨hyP, hyDa⟩, hyD⟩
            obtain ⟨w, hw, hwz⟩ := hyDδ
            have hwt : w ∈ eb.target := hDδtgt hw
            have hysrc : y ∈ eb.source := hwz ▸ eb.map_target hwt
            have hyval : eb y = w := by rw [← hwz, eb.right_inv hwt]
            have hyled : dist (eb y) cb ≤ δ := by
              rw [hyval]
              exact mem_closedBall.1 hw
            have hyd : dist (eb y) cb = δ := by
              rcases lt_or_eq_of_le hyled with h1 | h1
              · exfalso
                have hOopen : IsOpen (eb.source ∩ eb ⁻¹' ball cb δ) :=
                  eb.isOpen_inter_preimage isOpen_ball
                have hyO : y ∈ eb.source ∩ eb ⁻¹' ball cb δ :=
                  ⟨hysrc, by rw [Set.mem_preimage]; exact mem_ball.2 h1⟩
                have hODδ : eb.source ∩ eb ⁻¹' ball cb δ ⊆ Dδ := by
                  rintro q ⟨hq1, hq2⟩
                  rw [Set.mem_preimage] at hq2
                  exact ⟨eb q, ball_subset_closedBall hq2, eb.left_inv hq1⟩
                obtain ⟨q, hqO, hqΩ⟩ := mem_closure_iff.1 hycl _ hOopen hyO
                exact hqΩ.2 (hODδ hqO)
              · exact h1
            obtain ⟨hb1, hb2, hynepb, hyP'⟩ := hΓδ y hysrc hyd
            have hynepa : y ≠ pa := by
              intro hcon
              apply hdisjab pa hpaDa
              rw [← hcon]
              exact ⟨w, closedBall_subset_closedBall
                (by linarith only [hδrb, hrb]) hw, hwz⟩
            have hcg : ContinuousAt (pieceGreen P pb) y :=
              (hgb_harm y hyP hynepb).continuousAt
            have hcv : ContinuousAt vE y := hvEcont.continuousAt
              (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hynepa))
            refine ⟨by rw [hwc]; exact (hcv.sub hcg).max continuousAt_const, ?_⟩
            rw [hwc]
            simp only
            exact max_le (by linarith only [hb1, hb2, hCc0]) hCc0
        · -- off the piece: the competitor vanishes on a neighborhood
          have hyKE : y ∉ KE := fun hmem => hyP (hKEP hmem)
          have hynepb : y ≠ pb := fun hcon => hyP (by rw [hcon]; exact hpb)
          have hOn : IsOpen (KEᶜ ∩ {pb}ᶜ) := hKEc.isClosed.isOpen_compl.inter
            isOpen_compl_singleton
          have hyO : y ∈ KEᶜ ∩ {pb}ᶜ := ⟨hyKE, Set.mem_compl_singleton_iff.2 hynepb⟩
          have hev0 : wc =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
            filter_upwards [hOn.mem_nhds hyO] with q hq
            rw [hwc]
            simp only
            rw [hKE0 q hq.1]
            have h1 : 0 ≤ pieceGreen P pb q := hgb_nonneg q
              (Set.mem_compl_singleton_iff.1 hq.2)
            rw [max_eq_right (by linarith only [h1])]
          refine ⟨continuousAt_const.congr_of_eventuallyEq hev0, ?_⟩
          have h2 : wc y = 0 := hev0.eq_of_nhds
          rw [h2]
          exact hCc0
      have hwcle : ∀ z ∈ Ω, wc z ≤ Cc :=
        maxPrin Ω wc Cc KE hΩopen hΩne hwcsub hKEc hwcout hwcfr
      -- conclude at the point `x`
      by_cases hxDa : x ∈ Da
      · obtain ⟨w, hw, hwz⟩ := hxDa
        have hwt : w ∈ ea.target := htga hw
        have hxsrc : x ∈ ea.source := hwz ▸ ea.map_target hwt
        have hxval : ea x = w := by rw [← hwz, ea.right_inv hwt]
        have hxled : dist (ea x) ca ≤ ra := by
          rw [hxval]
          exact mem_closedBall.1 hw
        have hxd : dist (ea x) ca = ra := by
          rcases lt_or_eq_of_le hxled with h1 | h1
          · exact absurd ⟨hxsrc, by rw [Set.mem_preimage]; exact mem_ball.2 h1⟩ hxVa
          · exact h1
        have hxΓa : x ∈ ea.symm '' sphere ca ra :=
          ⟨ea x, mem_sphere.2 hxd, ea.left_inv hxsrc⟩
        have hxnepa : x ≠ pa := by
          intro hcon
          rw [hcon, ← hca, dist_self] at hxd
          rw [← hxd] at hra
          exact lt_irrefl _ hra
        have h3 : v ⟨x, hxP⟩ ≤ greenEnvelope (⟨pa, hpa⟩ : ↥P) ⟨x, hxP⟩ :=
          le_csSup (hBdda _ (fun hcon => hxnepa (congrArg Subtype.val hcon)))
            ⟨v, hv, rfl⟩
        have h4 := hcirc x hxΓa
        have h5 : greenEnvelope (⟨pa, hpa⟩ : ↥P) ⟨x, hxP⟩ = pieceGreen P pa x :=
          (pgval P pa hpa x hxP).symm
        rw [h5] at h3
        linarith only [h3, h4]
      · have hxDδ : x ∉ Dδ := fun hmem => hxVb (hDδVb hmem)
        have hxΩ : x ∈ Ω := ⟨⟨hxP, hxDa⟩, hxDδ⟩
        have h5 := hwcle x hxΩ
        rw [hwc] at h5
        simp only at h5
        have h6 : vE x - pieceGreen P pb x ≤ Cc := le_trans (le_max_left _ _) h5
        have h7 : v ⟨x, hxP⟩ = vE x := (hvEval ⟨x, hxP⟩).symm
        linarith only [h6, h7]
    -- close the supremum over the family
    rw [pgval P pa hpa x hxP]
    simp only [greenEnvelope]
    refine csSup_le ⟨0, (fun _ : ↥P => (0 : ℝ)), zeroFam P pa hpa, rfl⟩ ?_
    rintro b ⟨v, hv, rfl⟩
    exact percand v hv
  /- ## The center chart. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D₀.center with he₀
  set c₀ : ℂ := e₀ D₀.center with hc₀
  set r₀ : ℝ := D₀.radius with hr₀def
  have hr₀ : 0 < r₀ := D₀.radius_pos
  have hcb₀tgt : closedBall c₀ r₀ ⊆ e₀.target := D₀.closedBall_subset
  have hcar₀ : D₀.closedCarrier = e₀.symm '' closedBall c₀ r₀ := rfl
  have hcen₀src : D₀.center ∈ e₀.source := mem_chart_source ℂ D₀.center
  have hcen₀car : D₀.center ∈ D₀.closedCarrier :=
    ⟨c₀, mem_closedBall_self hr₀.le, e₀.left_inv hcen₀src⟩
  /- ## The pole charts and the avoidance radii. -/
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  have havoid1 : ∃ S : ℝ, 0 < S ∧ closedBall c₁ S ⊆ e₁.target ∧
      ∀ w ∈ closedBall c₁ S, e₁.symm w ∉ D₀.closedCarrier ∧ e₁.symm w ≠ p₂ := by
    have hopen : IsOpen (e₁.target ∩ e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ {p₂}ᶜ)) :=
      e₁.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter isOpen_compl_singleton)
    have hmem : c₁ ∈ e₁.target ∩ e₁.symm ⁻¹' (D₀.closedCarrierᶜ ∩ {p₂}ᶜ) :=
        by
      refine ⟨by rw [hc₁]; exact e₁.map_source hp₁src, ?_⟩
      rw [Set.mem_preimage, hc₁, e₁.left_inv hp₁src]
      exact ⟨hp₁, Set.mem_compl_singleton_iff.2 hne⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw => (hSsub hw).1, fun w hw => ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, Set.mem_compl_singleton_iff.1 h2.2⟩
  obtain ⟨S₁, hS₁0, hS₁tgt, hS₁av⟩ := havoid1
  set r₁ : ℝ := S₁ / 2 with hr₁def
  have hr₁ : 0 < r₁ := by rw [hr₁def]; exact half_pos hS₁0
  have h2r₁ : 2 * r₁ ≤ S₁ := by rw [hr₁def]; linarith only []
  have htgt1 : closedBall c₁ (2 * r₁) ⊆ e₁.target :=
    (closedBall_subset_closedBall h2r₁).trans hS₁tgt
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  have hCar1cp : IsCompact Car1 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono htgt1)
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₁av w (closedBall_subset_closedBall h2r₁ hw)
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have havoid2 : ∃ S : ℝ, 0 < S ∧ closedBall c₂ S ⊆ e₂.target ∧
      ∀ w ∈ closedBall c₂ S, e₂.symm w ∉ D₀.closedCarrier ∧ e₂.symm w ∉ Car1 := by
    have hopen : IsOpen (e₂.target ∩ e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ Car1ᶜ)) :=
      e₂.isOpen_inter_preimage_symm
        (D₀.isCompact_closedCarrier.isClosed.isOpen_compl.inter
          hCar1cp.isClosed.isOpen_compl)
    have hmem : c₂ ∈ e₂.target ∩ e₂.symm ⁻¹' (D₀.closedCarrierᶜ ∩ Car1ᶜ) := by
      refine ⟨by rw [hc₂]; exact e₂.map_source hp₂src, ?_⟩
      rw [Set.mem_preimage, hc₂, e₂.left_inv hp₂src]
      exact ⟨hp₂, fun hmem2 => (hCar1av p₂ hmem2).2 rfl⟩
    obtain ⟨S, hS0, hSsub⟩ := nhds_basis_closedBall.mem_iff.1 (hopen.mem_nhds hmem)
    refine ⟨S, hS0, fun w hw => (hSsub hw).1, fun w hw => ?_⟩
    have h2 := (hSsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, h2.2⟩
  obtain ⟨S₂, hS₂0, hS₂tgt, hS₂av⟩ := havoid2
  set r₂ : ℝ := S₂ / 2 with hr₂def
  have hr₂ : 0 < r₂ := by rw [hr₂def]; exact half_pos hS₂0
  have h2r₂ : 2 * r₂ ≤ S₂ := by rw [hr₂def]; linarith only []
  have htgt2 : closedBall c₂ (2 * r₂) ⊆ e₂.target :=
    (closedBall_subset_closedBall h2r₂).trans hS₂tgt
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar2cp : IsCompact Car2 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono htgt2)
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 := by
    rintro z ⟨w, hw, rfl⟩
    exact hS₂av w (closedBall_subset_closedBall h2r₂ hw)
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  have hp₁ne₂ : p₁ ∉ Car2 := fun hmem => (hCar2av p₁ hmem).2 hp₁Car1
  /- ## The interior pole balls. -/
  set B₁ : Set M := e₁.source ∩ e₁ ⁻¹' ball c₁ r₁ with hB₁
  set B₂ : Set M := e₂.source ∩ e₂ ⁻¹' ball c₂ r₂ with hB₂
  have hB₁open : IsOpen B₁ := e₁.isOpen_inter_preimage isOpen_ball
  have hB₂open : IsOpen B₂ := e₂.isOpen_inter_preimage isOpen_ball
  have hp₁B₁ : p₁ ∈ B₁ :=
    ⟨hp₁src, by rw [Set.mem_preimage, ← hc₁]; exact mem_ball_self hr₁⟩
  have hp₂B₂ : p₂ ∈ B₂ :=
    ⟨hp₂src, by rw [Set.mem_preimage, ← hc₂]; exact mem_ball_self hr₂⟩
  have hB₁img : e₁.symm '' ball c₁ r₁ = B₁ :=
    himg e₁ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1)
  have hB₂img : e₂.symm '' ball c₂ r₂ = B₂ :=
    himg e₂ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2)
  have hB₁Car : B₁ ⊆ Car1 := by
    rw [← hB₁img, hCar1]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hB₂Car : B₂ ⊆ Car2 := by
    rw [← hB₂img, hCar2]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  /- ## The auxiliary base point away from the three disks. -/
  have hp₃ex : ∃ p₃ : M, p₃ ∉ D₀.closedCarrier ∧ p₃ ∉ Car1 ∧ p₃ ∉ Car2 := by
    by_contra hcon
    push Not at hcon
    have hAopen : IsOpen D₀.closedCarrier := by
      have heq : D₀.closedCarrier = (Car1 ∪ Car2)ᶜ := by
        apply Set.Subset.antisymm
        · intro z hz
          rintro (h | h)
          · exact (hCar1av z h).1 hz
          · exact (hCar2av z h).1 hz
        · intro z hz
          by_cases h1 : z ∈ D₀.closedCarrier
          · exact h1
          by_cases h2 : z ∈ Car1
          · exact absurd (Or.inl h2) hz
          · exact absurd (Or.inr (hcon z h1 h2)) hz
      rw [heq]
      exact (hCar1cp.union hCar2cp).isClosed.isOpen_compl
    have hclopen : IsClopen D₀.closedCarrier :=
      ⟨D₀.isCompact_closedCarrier.isClosed, hAopen⟩
    have huniv := hclopen.eq_univ ⟨D₀.center, hcen₀car⟩
    apply hp₁
    rw [huniv]
    trivial
  obtain ⟨p₃, hp₃car, hp₃C1, hp₃C2⟩ := hp₃ex
  have h₃₁ : p₃ ≠ p₁ := fun hcon => hp₃C1 (hcon ▸ hp₁Car1)
  have h₃₂ : p₃ ≠ p₂ := fun hcon => hp₃C2 (hcon ▸ hp₂Car2)
  /- ## The Harnack chain domains, the chain compact and the constants. -/
  set Dq : CoordDisk M := D₀.shrink (1 / 4) (by norm_num) (by norm_num) with hDq
  have hDqcar : Dq.closedCarrier = e₀.symm '' closedBall c₀ (1 / 4 * r₀) := rfl
  have hDqsub : Dq.closedCarrier ⊆ D₀.closedCarrier := by
    rw [hDqcar, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₀]))
  set half1 : CoordDisk M := ⟨p₁, r₁ / 2, by linarith only [hr₁],
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1⟩ with hhalf1
  set half2 : CoordDisk M := ⟨p₂, r₂ / 2, by linarith only [hr₂],
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2⟩ with hhalf2
  have hhalf1car : half1.closedCarrier = e₁.symm '' closedBall c₁ (r₁ / 2) := rfl
  have hhalf2car : half2.closedCarrier = e₂.symm '' closedBall c₂ (r₂ / 2) := rfl
  have hhalf1Car : half1.closedCarrier ⊆ Car1 := by
    rw [hhalf1car, hCar1]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
  have hhalf2Car : half2.closedCarrier ⊆ Car2 := by
    rw [hhalf2car, hCar2]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
  have hp₁half : p₁ ∈ half1.closedCarrier := by
    rw [hhalf1car]
    exact ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂half : p₂ ∈ half2.closedCarrier := by
    rw [hhalf2car]
    exact ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  have hdisjQ1 : Disjoint Dq.closedCarrier half1.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz1
    exact (hCar1av z (hhalf1Car hz1)).1 (hDqsub hzQ)
  have hdisjQ2 : Disjoint Dq.closedCarrier half2.closedCarrier := by
    rw [Set.disjoint_left]
    intro z hzQ hz2
    exact (hCar2av z (hhalf2Car hz2)).1 (hDqsub hzQ)
  set Ω₁ : Set M := (Dq.closedCarrier ∪ half1.closedCarrier)ᶜ with hΩ₁
  set Ω₂ : Set M := (Dq.closedCarrier ∪ half2.closedCarrier)ᶜ with hΩ₂
  have hΩ₁open : IsOpen Ω₁ := (Dq.isCompact_closedCarrier.union
    half1.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₂open : IsOpen Ω₂ := (Dq.isCompact_closedCarrier.union
    half2.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩ₁conn : IsPreconnected Ω₁ :=
    (isConnected_two_coordDisk_compl Dq half1 hdisjQ1).isPreconnected
  have hΩ₂conn : IsPreconnected Ω₂ :=
    (isConnected_two_coordDisk_compl Dq half2 hdisjQ2).isPreconnected
  set Γ₁ : Set M := e₁.symm '' sphere c₁ r₁ with hΓ₁
  set Γ₂ : Set M := e₂.symm '' sphere c₂ r₂ with hΓ₂
  have hsph1tgt : sphere c₁ r₁ ⊆ e₁.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hsph2tgt : sphere c₂ r₂ ⊆ e₂.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  have hΓ₁cp : IsCompact Γ₁ := (isCompact_sphere _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono hsph1tgt)
  have hΓ₂cp : IsCompact Γ₂ := (isCompact_sphere _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono hsph2tgt)
  have hΓ₁Car : Γ₁ ⊆ Car1 := by
    rw [hΓ₁, hCar1]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hΓ₂Car : Γ₂ ⊆ Car2 := by
    rw [hΓ₂, hCar2]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  have hΓ₁half : ∀ z ∈ Γ₁, z ∉ half1.closedCarrier := by
    intro z hz hmem
    rw [hhalf1car] at hmem
    obtain ⟨hzs, hzd⟩ := (hmemCB e₁ c₁ (r₁ / 2)
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1) z).1 hmem
    obtain ⟨-, hzd'⟩ := (hmemSph e₁ c₁ r₁ hsph1tgt z).1 hz
    rw [hzd'] at hzd
    linarith only [hzd, hr₁]
  have hΓ₂half : ∀ z ∈ Γ₂, z ∉ half2.closedCarrier := by
    intro z hz hmem
    rw [hhalf2car] at hmem
    obtain ⟨hzs, hzd⟩ := (hmemCB e₂ c₂ (r₂ / 2)
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2) z).1 hmem
    obtain ⟨-, hzd'⟩ := (hmemSph e₂ c₂ r₂ hsph2tgt z).1 hz
    rw [hzd'] at hzd
    linarith only [hzd, hr₂]
  set K : Set M := Γ₁ ∪ Γ₂ ∪ {p₃} with hK
  have hKcp : IsCompact K := (hΓ₁cp.union hΓ₂cp).union isCompact_singleton
  have hp₃K : p₃ ∈ K := Or.inr rfl
  have hKΩ₁ : K ⊆ Ω₁ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar1av z (hΓ₁Car hz)).1 (hDqsub hmem)
      · exact hΓ₁half z hz hmem
    · rintro (hmem | hmem)
      · exact (hCar2av z (hΓ₂Car hz)).1 (hDqsub hmem)
      · exact (hCar2av z (hΓ₂Car hz)).2 (hhalf1Car hmem)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃car (hDqsub hmem)
      · exact hp₃C1 (hhalf1Car hmem)
  have hKΩ₂ : K ⊆ Ω₂ := by
    rintro z ((hz | hz) | hz)
    · rintro (hmem | hmem)
      · exact (hCar1av z (hΓ₁Car hz)).1 (hDqsub hmem)
      · exact (hCar2av z (hhalf2Car hmem)).2 (hΓ₁Car hz)
    · rintro (hmem | hmem)
      · exact (hCar2av z (hΓ₂Car hz)).1 (hDqsub hmem)
      · exact hΓ₂half z hz hmem
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rintro (hmem | hmem)
      · exact hp₃car (hDqsub hmem)
      · exact hp₃C2 (hhalf2Car hmem)
  obtain ⟨CH₁, hCH₁0, hCH₁⟩ := exists_harnack_chain_const hΩ₁open hΩ₁conn hKcp
      hKΩ₁
  obtain ⟨CH₂, hCH₂0, hCH₂⟩ := exists_harnack_chain_const hΩ₂open hΩ₂conn hKcp
      hKΩ₂
  /- ## The oscillation bound on the chain compact, via the per-piece pole bound. -/
  have oscBd : ∀ (pa : M) (ra : ℝ), 0 < ra →
      closedBall (chartAt ℂ pa pa) ra ⊆ (chartAt ℂ pa).target →
      ∀ (P : Opens M), ∀ hcs : ConnectedSpace ↥P, ∀ hnc : NoncompactSpace ↥P,
      ∀ hpaP : pa ∈ P, HasGreenFunction (⟨pa, hpaP⟩ : ↥P) →
      (∀ w ∈ closedBall (chartAt ℂ pa pa) ra, (chartAt ℂ pa).symm w ∈ P) →
      ∀ (ΩA : Set M) (CHa : ℝ),
      (∀ u : M → ℝ, MHarmonicOn u ΩA → (∀ x ∈ ΩA, 0 ≤ u x) →
        ∀ x ∈ K, ∀ y ∈ K, u x ≤ CHa * u y) →
      K ⊆ ΩA →
      (∀ z ∈ ΩA, z ∈ P) →
      (∀ z ∈ ΩA, z ∉ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2)) →
      ((chartAt ℂ pa).symm '' sphere (chartAt ℂ pa pa) ra ⊆ K) →
      ∀ z ∈ K, |pieceGreen P pa z - pieceGreen P pa p₃| ≤ CHa * Real.log 2 := by
    intro pa ra hra htgtA P hcs hnc hpaP hGFa hcarA ΩA CHa hCHa hKA hΩA1 hΩA2 hΓA z hzK
    obtain ⟨Nt, xout, hxoutΓ, hxoutval, hxoutmax, hIB⟩ :=
      poleBound P hcs hnc pa hpaP hGFa ra hra htgtA
        (by rintro y ⟨w, hw, rfl⟩; exact hcarA w hw)
    have hpahalf : pa ∈ (chartAt ℂ pa).symm '' closedBall (chartAt ℂ pa pa) (ra / 2) :=
      ⟨chartAt ℂ pa pa, mem_closedBall_self (by linarith only [hra]),
        (chartAt ℂ pa).left_inv (mem_chart_source ℂ pa)⟩
    set u : M → ℝ := fun q => Nt + Real.log 2 - pieceGreen P pa q with hu
    have huharm : MHarmonicOn u ΩA := by
      intro q hq
      have hqnepa : q ≠ pa := fun hcon => hΩA2 q hq (hcon ▸ hpahalf)
      have h1 : MHarmonicAt (pieceGreen P pa) q :=
        pgharm P pa hpaP hcs hnc hGFa q (hΩA1 q hq) hqnepa
      refine mharm_congr _ _ q (Filter.Eventually.of_forall fun y => ?_)
        (mharmAffine _ q (-1) (Nt + Real.log 2) h1)
      simp only [hu]
      ring
    have hupos : ∀ x ∈ ΩA, 0 ≤ u x := by
      intro x hx
      have h2 := hIB x ⟨hΩA1 x hx, hΩA2 x hx⟩
      simp only [hu]
      linarith only [h2]
    have hxoutK : xout ∈ K := hΓA hxoutΓ
    have huout : u xout = Real.log 2 := by
      simp only [hu]
      rw [hxoutval]
      ring
    have h3 : u z ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos z hzK xout hxoutK
      rwa [huout] at h5
    have h4 : u p₃ ≤ CHa * Real.log 2 := by
      have h5 := hCHa u huharm hupos p₃ hp₃K xout hxoutK
      rwa [huout] at h5
    have h5 : 0 ≤ u z := hupos z (hKA hzK)
    have h6 : 0 ≤ u p₃ := hupos p₃ (hKA hp₃K)
    have h7 : pieceGreen P pa z - pieceGreen P pa p₃ = u p₃ - u z := by
      simp only [hu]
      ring
    rw [h7, abs_le]
    constructor <;> linarith only [h3, h4, h5, h6]
  /- ## The drift constant and the packaged bound. -/
  obtain ⟨Cd, hCd⟩ := exists_pieceGreen_drift_bound D₀ hp₁ hp₂ hp₃car hne h₃₁
      h₃₂
  set C₀ : ℝ := max (|Cd| + (CH₁ + CH₂) * Real.log 2) 1 with hC₀def
  have hC₀1 : (1 : ℝ) ≤ C₀ := le_max_right _ _
  have hC₀0 : (0 : ℝ) ≤ C₀ := by linarith only [hC₀1]
  refine ⟨r₁, r₂, C₀, hr₁, hr₂, hC₀1, htgt1, htgt2,
    (fun w hw => hS₁av w (closedBall_subset_closedBall h2r₁ hw)),
    (fun w hw => hS₂av w (closedBall_subset_closedBall h2r₂ hw)), ?_⟩
  intro tt htt htt1 htt4 x hx1 hx2
  /- ## The piece for the given shrink parameter. -/
  set Pt : Opens M := (D₀.shrink tt htt htt1).compl with hPt
  have hcart : (D₀.shrink tt htt htt1).closedCarrier =
      e₀.symm '' closedBall c₀ (tt * r₀) := rfl
  have hcarsubt : (D₀.shrink tt htt htt1).closedCarrier ⊆ D₀.closedCarrier := by
    rw [hcart, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htt1))
  have hcarqt : (D₀.shrink tt htt htt1).closedCarrier ⊆ Dq.closedCarrier := by
    rw [hcart, hDqcar]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right htt4 hr₀.le))
  have hp₁t : p₁ ∈ Pt := fun hmem => hp₁ (hcarsubt hmem)
  have hp₂t : p₂ ∈ Pt := fun hmem => hp₂ (hcarsubt hmem)
  haveI hconnT : ConnectedSpace ↥Pt :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  haveI hncT : NoncompactSpace ↥Pt := noncompactSpace_coordDisk_compl _
  have hGF1t : HasGreenFunction (⟨p₁, hp₁t⟩ : ↥Pt) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁t
  have hGF2t : HasGreenFunction (⟨p₂, hp₂t⟩ : ↥Pt) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂t
  have hcarP1 : ∀ w ∈ closedBall c₁ r₁, e₁.symm w ∈ Pt := by
    intro w hw hmem
    exact (hS₁av w (closedBall_subset_closedBall
      (by linarith only [hr₁, h2r₁]) hw)).1 (hcarsubt hmem)
  have hcarP2 : ∀ w ∈ closedBall c₂ r₂, e₂.symm w ∈ Pt := by
    intro w hw hmem
    exact (hS₂av w (closedBall_subset_closedBall
      (by linarith only [hr₂, h2r₂]) hw)).1 (hcarsubt hmem)
  /- ## The oscillation bounds and the chain-compact bound for this piece. -/
  have osc1 : ∀ z ∈ K, |pieceGreen Pt p₁ z - pieceGreen Pt p₁ p₃|
      ≤ CH₁ * Real.log 2 := by
    refine oscBd p₁ r₁ hr₁
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      Pt hconnT hncT hp₁t hGF1t hcarP1 Ω₁ CH₁ hCH₁ hKΩ₁ ?_ ?_ ?_
    · intro z hz hmem
      exact hz (Or.inl (hcarqt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inl hz)
  have osc2 : ∀ z ∈ K, |pieceGreen Pt p₂ z - pieceGreen Pt p₂ p₃|
      ≤ CH₂ * Real.log 2 := by
    refine oscBd p₂ r₂ hr₂
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      Pt hconnT hncT hp₂t hGF2t hcarP2 Ω₂ CH₂ hCH₂ hKΩ₂ ?_ ?_ ?_
    · intro z hz hmem
      exact hz (Or.inl (hcarqt hmem))
    · intro z hz hmem
      exact hz (Or.inr hmem)
    · intro z hz
      exact Or.inl (Or.inr hz)
  have hKbd : ∀ z ∈ K, |pieceGreen Pt p₁ z - pieceGreen Pt p₂ z| ≤ C₀ := by
    intro z hz
    have h1 := osc1 z hz
    have h2 := osc2 z hz
    have h3 : |pieceGreen Pt p₁ p₃ - pieceGreen Pt p₂ p₃| ≤ Cd := hCd tt htt htt1
    have h6 : pieceGreen Pt p₁ z - pieceGreen Pt p₂ z =
        (pieceGreen Pt p₁ z - pieceGreen Pt p₁ p₃)
        + -(pieceGreen Pt p₂ z - pieceGreen Pt p₂ p₃)
        + (pieceGreen Pt p₁ p₃ - pieceGreen Pt p₂ p₃) := by
      ring
    have h5 := abs_add_three
      (pieceGreen Pt p₁ z - pieceGreen Pt p₁ p₃)
      (-(pieceGreen Pt p₂ z - pieceGreen Pt p₂ p₃))
      (pieceGreen Pt p₁ p₃ - pieceGreen Pt p₂ p₃)
    rw [abs_neg] at h5
    rw [h6]
    have h7 : Cd ≤ |Cd| := le_abs_self Cd
    have h8 : |Cd| + (CH₁ + CH₂) * Real.log 2 ≤ C₀ := le_max_left _ _
    calc |_ + _ + _| ≤ _ := h5
      _ ≤ C₀ := by linarith only [h1, h2, h3, h7, h8]
  /- ## The one-sided extension bounds close the master estimate. -/
  by_cases hxP : x ∈ Pt
  · have hs1 : ∀ z ∈ (chartAt ℂ p₁).symm '' sphere (chartAt ℂ p₁ p₁) r₁,
        pieceGreen Pt p₁ z - pieceGreen Pt p₂ z ≤ C₀ := by
      intro z hz
      have h1 := (abs_le.1 (hKbd z (Or.inl (Or.inl hz)))).2
      linarith only [h1]
    have hs2 : ∀ z ∈ (chartAt ℂ p₂).symm '' sphere (chartAt ℂ p₂ p₂) r₂,
        pieceGreen Pt p₂ z - pieceGreen Pt p₁ z ≤ C₀ := by
      intro z hz
      have h1 := (abs_le.1 (hKbd z (Or.inl (Or.inr hz)))).1
      linarith only [h1]
    have hsubCar1 : (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) r₁ ⊆ Car1 :=
        by
      rw [hCar1]
      exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
    have hsubCar2 : (chartAt ℂ p₂).symm '' closedBall (chartAt ℂ p₂ p₂) r₂ ⊆ Car2 :=
        by
      rw [hCar2]
      exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
    have hdisj12 : ∀ y ∈ (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) r₁,
        y ∉ (chartAt ℂ p₂).symm '' closedBall (chartAt ℂ p₂ p₂) r₂ := by
      intro y hy hmem
      exact (hCar2av y (hsubCar2 hmem)).2 (hsubCar1 hy)
    have hdisj21 : ∀ y ∈ (chartAt ℂ p₂).symm '' closedBall (chartAt ℂ p₂ p₂) r₂,
        y ∉ (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) r₁ := by
      intro y hy hmem
      exact (hCar2av y (hsubCar2 hy)).2 (hsubCar1 hmem)
    have hside1 := side Pt hconnT hncT p₁ hp₁t p₂ hp₂t hGF1t hGF2t r₁ r₂ C₀ hr₁
        hr₂
      hC₀0 ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP1 w hw)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP2 w hw)
      hdisj12 hs1 x hxP hx1 hx2
    have hside2 := side Pt hconnT hncT p₂ hp₂t p₁ hp₁t hGF2t hGF1t r₂ r₁ C₀ hr₂
        hr₁
      hC₀0 ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2)
      ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP2 w hw)
      (by rintro y ⟨w, hw, rfl⟩; exact hcarP1 w hw)
      hdisj21 hs2 x hxP hx2 hx1
    rw [abs_le]
    constructor
    · linarith only [hside2]
    · linarith only [hside1]
  · have h1 : pieceGreen Pt p₁ x = 0 := pgzero _ _ _ hxP
    have h2 : pieceGreen Pt p₂ x = 0 := pgzero _ _ _ hxP
    rw [h1, h2, sub_zero, abs_zero]
    exact hC₀0

/-- The pole companion of a dipole difference of piece Green's functions: after
subtracting the logarithmic pole at the first point, the difference extends to a
harmonic function on a fixed chart ball, bounded by the exterior bound plus the
logarithms of the two ball radii. -/
private theorem bipolarGreen_aux2 (D₀ : CoordDisk M) {pa pb : M} {ra rb C₀ : ℝ}
    (hra : 0 < ra) (hrb : 0 < rb)
    (htga : closedBall (chartAt ℂ pa pa) (2 * ra) ⊆ (chartAt ℂ pa).target)
    (hava : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ∉ D₀.closedCarrier ∧ (chartAt ℂ pa).symm w ≠ pb)
    (havb : ∀ w ∈ closedBall (chartAt ℂ pb pb) (2 * rb),
      (chartAt ℂ pb).symm w ∉ D₀.closedCarrier)
    (hdisj : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ∉
        (chartAt ℂ pb).symm '' closedBall (chartAt ℂ pb pb) (2 * rb))
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hbd : ∀ x : M,
      x ∉ (chartAt ℂ pa).source ∩ ⇑(chartAt ℂ pa) ⁻¹' ball (chartAt ℂ pa pa) ra →
      x ∉ (chartAt ℂ pb).source ∩ ⇑(chartAt ℂ pb) ⁻¹' ball (chartAt ℂ pb pb) rb →
      |pieceGreen (D₀.shrink t ht ht1).compl pa x -
        pieceGreen (D₀.shrink t ht ht1).compl pb x| ≤ C₀) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ pa pa) (2 * ra)) ∧
      (∀ w ∈ ball (chartAt ℂ pa pa) (2 * ra) \ {chartAt ℂ pa pa},
        h w = pieceGreen (D₀.shrink t ht ht1).compl pa ((chartAt ℂ pa).symm w) -
          pieceGreen (D₀.shrink t ht ht1).compl pb ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖) ∧
      ∀ w ∈ ball (chartAt ℂ pa pa) (2 * ra),
        |h w| ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Chart reading of a harmonic surface function is plane-harmonic. -/
  have htransfer : ∀ (x : M) (Ωt : Set M) (v : M → ℝ), MHarmonicOn v Ωt →
      ∀ w ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ωt,
        HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro x Ωt v hv w hw
    obtain ⟨hwt, hwΩ⟩ := hw
    have hwΩ' : (chartAt ℂ x).symm w ∈ Ωt := hwΩ
    have hyy : (chartAt ℂ x).symm w ∈ (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
      mem_chart_source ℂ ((chartAt ℂ x).symm w)
    have htrans : AnalyticAt ℂ
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w := by
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hwt
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).symm w) :=
        contMDiffAt_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas ((chartAt ℂ x).symm w)) hyy
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
    have hmh : HarmonicAt (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        ((⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w) := hv _ hwΩ'
    have hcomp := harmonicAt_comp_analyticAt hmh htrans
    have hev : (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
        v ∘ ⇑(chartAt ℂ x).symm := by
      have hS : IsOpen ((chartAt ℂ x).target ∩
          ⇑(chartAt ℂ x).symm ⁻¹' (chartAt ℂ ((chartAt ℂ x).symm w)).source) :=
        (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ x).open_target
          (chartAt ℂ ((chartAt ℂ x).symm w)).open_source
      filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with ζ hζ
      simp only [Function.comp_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hζ.2]
    exact (harmonicAt_congr_nhds hev).mp hcomp
  have mharmSub : ∀ (f g : M → ℝ) (z : M), MHarmonicAt f z → MHarmonicAt g z →
      MHarmonicAt (fun y => f y - g y) z := by
    intro f g z hf hg
    refine mharm_congr (f + -g) _ z (Filter.Eventually.of_forall fun y => ?_) (hf.add hg.neg)
    simp only [Pi.add_apply, Pi.neg_apply]
    exact (sub_eq_add_neg (f y) (g y)).symm
  /- ## Negation of a plane-harmonic function. -/
  have harmNeg : ∀ (h : ℂ → ℝ) (s : Set ℂ), HarmonicOnNhd h s →
      HarmonicOnNhd (fun w => -h w) s := by
    intro h s hh z hz
    have h1 := (hh z hz).const_smul (c := (-1 : ℝ))
    have hev : ((-1 : ℝ) • h) =ᶠ[𝓝 z] fun w => -h w := by
      filter_upwards with w
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact (harmonicAt_congr_nhds hev).mp h1
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dif_pos ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dif_neg]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    haveI := hcs
    haveI := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon => hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z => pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## The piece, its instances and the Green data. -/
  set P : Opens M := (D₀.shrink t ht ht1).compl with hPdef
  have hcarsub : (D₀.shrink t ht ht1).closedCarrier ⊆ D₀.closedCarrier := by
    have h1 : (D₀.shrink t ht ht1).closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) (t * D₀.radius) := rfl
    have h2 : D₀.closedCarrier =
        (chartAt ℂ D₀.center).symm ''
          closedBall (chartAt ℂ D₀.center D₀.center) D₀.radius := rfl
    rw [h1, h2]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left D₀.radius_pos.le ht1))
  have hpasrc : pa ∈ (chartAt ℂ pa).source := mem_chart_source ℂ pa
  have hpbsrc : pb ∈ (chartAt ℂ pb).source := mem_chart_source ℂ pb
  have hpaca : (chartAt ℂ pa).symm (chartAt ℂ pa pa) = pa :=
    (chartAt ℂ pa).left_inv hpasrc
  have hpbcb : (chartAt ℂ pb).symm (chartAt ℂ pb pb) = pb :=
    (chartAt ℂ pb).left_inv hpbsrc
  have hpacar : pa ∉ D₀.closedCarrier := by
    have h1 := (hava (chartAt ℂ pa pa)
      (mem_closedBall_self (by linarith only [hra]))).1
    rwa [hpaca] at h1
  have hpbcar : pb ∉ D₀.closedCarrier := by
    have h1 := havb (chartAt ℂ pb pb) (mem_closedBall_self (by linarith only [hrb]))
    rwa [hpbcb] at h1
  have hpaP : pa ∈ P := fun hmem => hpacar (hcarsub hmem)
  have hpbP : pb ∈ P := fun hmem => hpbcar (hcarsub hmem)
  haveI hPconn : ConnectedSpace ↥P :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  haveI hPnc : NoncompactSpace ↥P := noncompactSpace_coordDisk_compl _
  have hGFa : HasGreenFunction (⟨pa, hpaP⟩ : ↥P) :=
    hasGreenFunction_coordDisk_compl _ pa hpaP
  have hGFb : HasGreenFunction (⟨pb, hpbP⟩ : ↥P) :=
    hasGreenFunction_coordDisk_compl _ pb hpbP
  /- ## The own-pole boundedness in the ambient chart. -/
  have poleData : ∃ ρ B : ℝ, 0 < ρ ∧
      ball (chartAt ℂ pa pa) ρ ⊆ (chartAt ℂ pa).target ∧
      ∀ w ∈ ball (chartAt ℂ pa pa) ρ \ {chartAt ℂ pa pa},
        (chartAt ℂ pa).symm w ∈ P ∧
        |pieceGreen P pa ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖| ≤ B := by
    obtain ⟨rE, hrE0, hrEsub, hE, hEharm, hEval⟩ :=
      exists_harmonic_pole_extension hGFa
    haveI hnety : Nonempty ↥(P) := ⟨⟨pa, hpaP⟩⟩
    set ea : OpenPartialHomeomorph M ℂ := chartAt ℂ pa with hea
    have hpasrc : pa ∈ ea.source := mem_chart_source ℂ pa
    have hct : chartAt ℂ (⟨pa, hpaP⟩ : ↥P) = ea.subtypeRestr hnety :=
      Opens.chartAt_eq
    have hcenter : chartAt ℂ (⟨pa, hpaP⟩ : ↥P) (⟨pa, hpaP⟩ : ↥P)
        = ea pa := by
      rw [hct, ea.subtypeRestr_coe hnety]
      rfl
    rw [hcenter] at hrEsub hEharm hEval
    have hcont : ContinuousOn hE (closedBall (ea pa) (rE / 2)) :=
      hEharm.continuousOn.mono (closedBall_subset_ball (by linarith only [hrE0]))
    obtain ⟨BE, hBE⟩ :=
      (isCompact_closedBall (ea pa) (rE / 2)).exists_bound_of_continuousOn hcont
    have heqOn : Set.EqOn (⇑ea.symm) (Subtype.val ∘ ⇑(ea.subtypeRestr hnety).symm)
        (ea.subtypeRestr hnety).target := ea.subtypeRestr_symm_eqOn hnety
    refine ⟨rE / 2, BE, half_pos hrE0, ?_, ?_⟩
    · intro w hw
      have h1 : w ∈ (chartAt ℂ (⟨pa, hpaP⟩ : ↥P)).target := by
        apply hrEsub
        exact ball_subset_ball (by linarith only [hrE0]) hw
      rw [hct] at h1
      exact ea.subtypeRestr_target_subset hnety h1
    · intro w hw
      obtain ⟨hwball, hwne⟩ := hw
      have hwne' : w ≠ ea pa := by simpa using hwne
      have hwball' : w ∈ ball (ea pa) rE :=
        ball_subset_ball (by linarith only [hrE0]) hwball
      have hwtgt : w ∈ (ea.subtypeRestr hnety).target := by
        have h1 := hrEsub hwball'
        rwa [hct] at h1
      have hmemP : ea.symm w ∈ P := by
        rw [heqOn hwtgt]
        exact ((ea.subtypeRestr hnety).symm w).2
      refine ⟨hmemP, ?_⟩
      have h2 := hEval w ⟨hwball', by simpa using hwne'⟩
      have h4 : ((chartAt ℂ (⟨pa, hpaP⟩ : ↥P)).symm w : ↥(P))
          = ⟨ea.symm w, hmemP⟩ := by
        apply Subtype.ext
        change ((chartAt ℂ (⟨pa, hpaP⟩ : ↥P)).symm w : M) = ea.symm w
        rw [hct]
        exact (heqOn hwtgt).symm
      rw [h4, ← pgval (P) pa hpaP (ea.symm w) hmemP] at h2
      rw [← h2]
      exact hBE w (ball_subset_closedBall hwball)
  /- ## The dipole difference and its data on the piece. -/
  set Fd : M → ℝ := fun z => pieceGreen P pa z - pieceGreen P pb z with hFdd
  have hcarin : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      (chartAt ℂ pa).symm w ∈ P :=
    fun w hw hmem => (hava w hw).1 (hcarsub hmem)
  have hnp : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra), w ≠ chartAt ℂ pa pa →
      (chartAt ℂ pa).symm w ≠ pa ∧ (chartAt ℂ pa).symm w ≠ pb := by
    intro w hw hwne
    constructor
    · intro hcon
      have hwt : w ∈ (chartAt ℂ pa).target := htga hw
      have h1 : chartAt ℂ pa ((chartAt ℂ pa).symm w) = w :=
        (chartAt ℂ pa).right_inv hwt
      rw [hcon] at h1
      exact hwne h1.symm
    · exact (hava w hw).2
  have hsB : ∀ w ∈ closedBall (chartAt ℂ pa pa) (2 * ra),
      ra ≤ dist w (chartAt ℂ pa pa) →
      (chartAt ℂ pa).symm w ∉
        (chartAt ℂ pa).source ∩ ⇑(chartAt ℂ pa) ⁻¹' ball (chartAt ℂ pa pa) ra ∧
      (chartAt ℂ pa).symm w ∉
        (chartAt ℂ pb).source ∩ ⇑(chartAt ℂ pb) ⁻¹' ball (chartAt ℂ pb pb) rb := by
    intro w hw hdw
    constructor
    · intro hmem
      obtain ⟨hsrc, hpre⟩ := hmem
      rw [Set.mem_preimage] at hpre
      have hwt : w ∈ (chartAt ℂ pa).target := htga hw
      rw [(chartAt ℂ pa).right_inv hwt] at hpre
      rw [mem_ball] at hpre
      linarith only [hdw, hpre]
    · intro hmem
      obtain ⟨hsrc, hpre⟩ := hmem
      rw [Set.mem_preimage] at hpre
      refine hdisj w hw ⟨chartAt ℂ pb ((chartAt ℂ pa).symm w), ?_, ?_⟩
      · exact ball_subset_closedBall (ball_subset_ball (by linarith only [hrb]) hpre)
      · exact (chartAt ℂ pb).left_inv hsrc
  have hFharm : ∀ (z : M), z ∈ P → z ≠ pa → z ≠ pb → MHarmonicAt Fd z := by
    intro z hzP hz1 hz2
    exact mharmSub _ _ z
      (pgharm P pa hpaP hPconn hPnc hGFa z hzP hz1)
      (pgharm P pb hpbP hPconn hPnc hGFb z hzP hz2)
  have hFbd : ∀ (z : M),
      z ∉ (chartAt ℂ pa).source ∩ ⇑(chartAt ℂ pa) ⁻¹' ball (chartAt ℂ pa pa) ra →
      z ∉ (chartAt ℂ pb).source ∩ ⇑(chartAt ℂ pb) ⁻¹' ball (chartAt ℂ pb pb) rb →
      |Fd z| ≤ C₀ := fun z h1 h2 => hbd z h1 h2
  /- ## The pole structure of the difference near `pa`. -/
  have hFpole : ∃ ρ B : ℝ, 0 < ρ ∧
      ∀ w ∈ ball (chartAt ℂ pa pa) ρ \ {chartAt ℂ pa pa},
        |Fd ((chartAt ℂ pa).symm w) + Real.log ‖w - chartAt ℂ pa pa‖| ≤ B := by
    obtain ⟨ρE, BE, hρE0, hballE, hEbd⟩ := poleData
    set ρ2 : ℝ := min ρE (2 * ra) with hρ2
    have hρ20 : 0 < ρ2 := lt_min hρE0 (by linarith only [hra])
    have hcont2 : ContinuousOn (fun w => pieceGreen P pb ((chartAt ℂ pa).symm w))
        (closedBall (chartAt ℂ pa pa) ρ2) := by
      intro w hw
      have hwcb : w ∈ closedBall (chartAt ℂ pa pa) (2 * ra) :=
        closedBall_subset_closedBall (min_le_right _ _) hw
      have hwt : w ∈ (chartAt ℂ pa).target := htga hwcb
      have hHA : HarmonicAt (pieceGreen P pb ∘ ⇑(chartAt ℂ pa).symm) w := by
        refine htransfer pa ((P : Set M) ∩ {pb}ᶜ) (pieceGreen P pb) ?_ w ⟨hwt, ?_⟩
        · intro z hz
          exact pgharm P pb hpbP hPconn hPnc hGFb z hz.1
            (Set.mem_compl_singleton_iff.1 hz.2)
        · rw [Set.mem_preimage]
          exact ⟨hcarin w hwcb, Set.mem_compl_singleton_iff.2 (hava w hwcb).2⟩
      exact (hHA.1.continuousAt).continuousWithinAt
    obtain ⟨B2c, hB2c⟩ :=
      (isCompact_closedBall (chartAt ℂ pa pa) ρ2).exists_bound_of_continuousOn hcont2
    refine ⟨ρ2, BE + B2c, hρ20, ?_⟩
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwbE : w ∈ ball (chartAt ℂ pa pa) ρE \ {chartAt ℂ pa pa} :=
      ⟨ball_subset_ball (min_le_left _ _) hwb, hwne⟩
    have h1 := (hEbd w hwbE).2
    have h2 := hB2c w (ball_subset_closedBall hwb)
    rw [Real.norm_eq_abs] at h2
    have heq : Fd ((chartAt ℂ pa).symm w) + Real.log ‖w - chartAt ℂ pa pa‖ =
        (pieceGreen P pa ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖) -
          pieceGreen P pb ((chartAt ℂ pa).symm w) := by
      simp only [hFdd]
      ring
    rw [heq]
    calc |(pieceGreen P pa ((chartAt ℂ pa).symm w) +
          Real.log ‖w - chartAt ℂ pa pa‖) -
          pieceGreen P pb ((chartAt ℂ pa).symm w)|
        ≤ |pieceGreen P pa ((chartAt ℂ pa).symm w) +
            Real.log ‖w - chartAt ℂ pa pa‖| +
          |pieceGreen P pb ((chartAt ℂ pa).symm w)| := abs_sub _ _
      _ ≤ BE + B2c := add_le_add h1 h2
  /- ## The companion via removability and the disk maximum principle. -/
  set ea : OpenPartialHomeomorph M ℂ := chartAt ℂ pa with hea
  set ca : ℂ := ea pa with hca
  have hpasrc : pa ∈ ea.source := mem_chart_source ℂ pa
  set u : ℂ → ℝ := fun w => Fd (ea.symm w) + Real.log ‖w - ca‖ with hu
  have huharm : ∀ w ∈ ball ca (2 * ra) \ {ca}, HarmonicAt u w := by
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwne' : w ≠ ca := by simpa using hwne
    have hwcb : w ∈ closedBall ca (2 * ra) := ball_subset_closedBall hwb
    have hwt : w ∈ ea.target := htga hwcb
    have hnpw := hnp w hwcb hwne'
    have h1 : HarmonicAt (Fd ∘ ⇑ea.symm) w := by
      refine htransfer pa ((P : Set M) ∩ ({pa}ᶜ ∩ {pb}ᶜ)) (Fd) ?_ w ⟨hwt, ?_⟩
      · intro z hz
        exact hFharm z hz.1 (Set.mem_compl_singleton_iff.1 hz.2.1)
          (Set.mem_compl_singleton_iff.1 hz.2.2)
      · rw [Set.mem_preimage]
        exact ⟨hcarin w hwcb, Set.mem_compl_singleton_iff.2 hnpw.1,
          Set.mem_compl_singleton_iff.2 hnpw.2⟩
    have h2 : HarmonicAt (fun v : ℂ => Real.log ‖v - ca‖) w := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun v : ℂ => v - ca)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hwne'
    refine (harmonicAt_congr_nhds ?_).mp (h1.add h2)
    filter_upwards with v
    simp only [Pi.add_apply, Function.comp_apply, hu]
  obtain ⟨ρE, BE, hρE0, hEbd⟩ := hFpole
  set ρm : ℝ := min ρE ra with hρm
  have hρm0 : 0 < ρm := lt_min hρE0 hra
  have hρmra : ρm ≤ ra := min_le_right _ _
  have huharm' : HarmonicOnNhd u (ball ca ρm \ {ca}) := by
    intro w hw
    refine huharm w ⟨ball_subset_ball (by linarith only [hρmra, hra]) hw.1, hw.2⟩
  have hub : ∀ w ∈ ball ca ρm \ {ca}, |u w| ≤ BE := by
    intro w hw
    exact hEbd w ⟨ball_subset_ball (min_le_left _ _) hw.1, hw.2⟩
  obtain ⟨vloc, hvlocharm, hvloceq⟩ := exists_harmonicOnNhd_of_bounded_punctured
    hρm0 huharm' ⟨BE, hub⟩
  set hcomp : ℂ → ℝ := fun z => if z = ca then vloc ca else u z with hhc
  have hcompharm : ∀ v ∈ ball ca (2 * ra), HarmonicAt hcomp v := by
    intro v hv
    by_cases hvc : v = ca
    · have hev : vloc =ᶠ[𝓝 v] hcomp := by
        have hvm : v ∈ ball ca ρm := by rw [hvc]; exact mem_ball_self hρm0
        filter_upwards [isOpen_ball.mem_nhds hvm] with z hz
        simp only [hhc]
        by_cases hzc : z = ca
        · rw [if_pos hzc, hzc]
        · rw [if_neg hzc]
          exact hvloceq ⟨hz, hzc⟩
      have hva : HarmonicAt vloc v := by
        rw [hvc]
        exact hvlocharm ca (mem_ball_self hρm0)
      exact (harmonicAt_congr_nhds hev).mp hva
    · have hopen : IsOpen (ball ca (2 * ra) ∩ {ca}ᶜ) :=
        isOpen_ball.inter isOpen_compl_singleton
      have hev : u =ᶠ[𝓝 v] hcomp := by
        filter_upwards [hopen.mem_nhds ⟨hv, hvc⟩] with z hz
        simp only [hhc]
        rw [if_neg (Set.mem_compl_singleton_iff.1 hz.2)]
      exact (harmonicAt_congr_nhds hev).mp
        (huharm v ⟨hv, Set.mem_compl_singleton_iff.2 hvc⟩)
  have hcompval : ∀ w ∈ ball ca (2 * ra) \ {ca},
      hcomp w = Fd (⇑ea.symm w) + Real.log ‖w - ca‖ := by
    intro w hw
    have hwne' : w ≠ ca := by simpa using hw.2
    simp only [hhc]
    rw [if_neg hwne']
  have hcompbd : ∀ w ∈ ball ca (2 * ra),
      |hcomp w| ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
    intro w hw
    set ρ' : ℝ := (max (dist w ca) ra + 2 * ra) / 2 with hρ'
    have hd2 : dist w ca < 2 * ra := mem_ball.1 hw
    have hmaxlt : max (dist w ca) ra < 2 * ra := by
      rw [max_lt_iff]
      exact ⟨hd2, by linarith only [hra]⟩
    have hρ'lt : ρ' < 2 * ra := by rw [hρ']; linarith only [hmaxlt]
    have hρ'gtra : ra < ρ' := by
      rw [hρ']
      have h1 : ra ≤ max (dist w ca) ra := le_max_right _ _
      linarith only [h1, hra]
    have hρ'0 : 0 < ρ' := lt_trans hra hρ'gtra
    have hwρ' : w ∈ ball ca ρ' := by
      rw [mem_ball, hρ']
      have h1 : dist w ca ≤ max (dist w ca) ra := le_max_left _ _
      linarith only [h1, hd2, hra]
    have hsubH : HarmonicOnNhd hcomp (closedBall ca ρ') := fun v hv =>
      hcompharm v (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hv) hρ'lt))
    have hcl : ContinuousOn hcomp (closure (ball ca ρ')) := by
      rw [closure_ball ca hρ'0.ne']
      exact hsubH.continuousOn
    have hfrbd : ∀ ζ ∈ frontier (ball ca ρ'),
        |hcomp ζ| ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
      intro ζ hζ
      rw [frontier_ball ca hρ'0.ne'] at hζ
      have hζd : dist ζ ca = ρ' := mem_sphere.1 hζ
      have hζcb : ζ ∈ closedBall ca (2 * ra) := by
        rw [mem_closedBall, hζd]
        linarith only [hρ'lt]
      have hζne : ζ ≠ ca := by
        intro hcon
        rw [hcon, dist_self] at hζd
        linarith only [hζd, hρ'0]
      have hval : hcomp ζ = u ζ := by
        simp only [hhc]
        rw [if_neg hζne]
      have hBs := hsB ζ hζcb (by rw [hζd]; linarith only [hρ'gtra])
      have h1 := hFbd (ea.symm ζ) hBs.1 hBs.2
      have hlogv : |Real.log ‖ζ - ca‖| ≤ |Real.log ra| + |Real.log (2 * ra)| := by
        have hn : ‖ζ - ca‖ = ρ' := by rw [← dist_eq_norm]; exact hζd
        rw [hn]
        have hl1 : Real.log ra ≤ Real.log ρ' := Real.log_le_log hra hρ'gtra.le
        have hl2 : Real.log ρ' ≤ Real.log (2 * ra) := Real.log_le_log hρ'0 hρ'lt.le
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (Real.log ra), abs_nonneg (Real.log (2 * ra))]
        · linarith [le_abs_self (Real.log (2 * ra)), abs_nonneg (Real.log ra)]
      rw [hval, hu]
      simp only
      calc |Fd (⇑ea.symm ζ) + Real.log ‖ζ - ca‖|
          ≤ |Fd (⇑ea.symm ζ)| + |Real.log ‖ζ - ca‖| := abs_add_le _ _
        _ ≤ C₀ + (|Real.log ra| + |Real.log (2 * ra)|) := by
            linarith only [h1, hlogv]
    have hup := SubharmonicOn.le_of_frontier_le isOpen_ball isBounded_ball
      (HarmonicOnNhd.subharmonicOn
        (fun v hv => hsubH v (ball_subset_closedBall hv)))
      hcl (fun ζ hζ => le_trans (le_abs_self _) (hfrbd ζ hζ)) w hwρ'
    have hlow := SubharmonicOn.le_of_frontier_le isOpen_ball isBounded_ball
      (HarmonicOnNhd.subharmonicOn
        (harmNeg _ _ (fun v hv => hsubH v (ball_subset_closedBall hv))))
      (by
        rw [closure_ball ca hρ'0.ne']
        exact (hsubH.continuousOn).neg)
      (fun ζ hζ => le_trans (neg_le_abs _) (hfrbd ζ hζ)) w hwρ'
    rw [abs_le]
    constructor
    · linarith only [hlow]
    · exact hup
  exact ⟨hcomp, fun v hv => hcompharm v hv, hcompval, hcompbd⟩

/-- The annulus log-barrier estimate: on the annulus between a shrunken disk and the fixed
three-quarter circle of the base disk, one dipole difference of piece Green's functions
exceeds another by at most the outer-circle gap plus a logarithmic barrier whose constant
is controlled by the exterior bound. -/
private theorem bipolarGreen_aux3 (D₀ : CoordDisk M) {p₁ p₂ : M} {r₁ r₂ C₀ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hC₀1 : 1 ≤ C₀)
    (htgt1 : closedBall (chartAt ℂ p₁ p₁) (2 * r₁) ⊆ (chartAt ℂ p₁).target)
    (htgt2 : closedBall (chartAt ℂ p₂ p₂) (2 * r₂) ⊆ (chartAt ℂ p₂).target)
    (hav1 : ∀ w ∈ closedBall (chartAt ℂ p₁ p₁) (2 * r₁),
      (chartAt ℂ p₁).symm w ∉ D₀.closedCarrier ∧ (chartAt ℂ p₁).symm w ≠ p₂)
    (hav2 : ∀ w ∈ closedBall (chartAt ℂ p₂ p₂) (2 * r₂),
      (chartAt ℂ p₂).symm w ∉ D₀.closedCarrier ∧
        (chartAt ℂ p₂).symm w ∉
          (chartAt ℂ p₁).symm '' closedBall (chartAt ℂ p₁ p₁) (2 * r₁))
    {tA tC tD : ℝ} (htA : 0 < tA) (htA1 : tA ≤ 1) (htA4 : tA ≤ 1 / 4)
    (htC : 0 < tC) (htC1 : tC ≤ 1) (htD : 0 < tD) (htD1 : tD ≤ 1)
    (hCA : (D₀.shrink tC htC htC1).closedCarrier ⊆
      (D₀.shrink tA htA htA1).closedCarrier)
    (hDA : (D₀.shrink tD htD htD1).closedCarrier ⊆
      (D₀.shrink tA htA htA1).closedCarrier)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbdC : ∀ x : M,
      x ∉ (chartAt ℂ p₁).source ∩ ⇑(chartAt ℂ p₁) ⁻¹' ball (chartAt ℂ p₁ p₁)
          r₁ →
      x ∉ (chartAt ℂ p₂).source ∩ ⇑(chartAt ℂ p₂) ⁻¹' ball (chartAt ℂ p₂ p₂)
          r₂ →
      |pieceGreen (D₀.shrink tC htC htC1).compl p₁ x -
        pieceGreen (D₀.shrink tC htC htC1).compl p₂ x| ≤ C₀)
    (hbdD : ∀ x : M,
      x ∉ (chartAt ℂ p₁).source ∩ ⇑(chartAt ℂ p₁) ⁻¹' ball (chartAt ℂ p₁ p₁)
          r₁ →
      x ∉ (chartAt ℂ p₂).source ∩ ⇑(chartAt ℂ p₂) ⁻¹' ball (chartAt ℂ p₂ p₂)
          r₂ →
      |pieceGreen (D₀.shrink tD htD htD1).compl p₁ x -
        pieceGreen (D₀.shrink tD htD htD1).compl p₂ x| ≤ C₀)
    (hsph : ∀ z ∈ (chartAt ℂ D₀.center).symm ''
        sphere (chartAt ℂ D₀.center D₀.center) (3 * D₀.radius / 4),
      pieceGreen (D₀.shrink tC htC htC1).compl p₁ z -
        pieceGreen (D₀.shrink tC htC htC1).compl p₂ z -
        (pieceGreen (D₀.shrink tD htD htD1).compl p₁ z -
          pieceGreen (D₀.shrink tD htD htD1).compl p₂ z) ≤ ε) :
    ∀ x : M, x ∈ (chartAt ℂ D₀.center).source →
      tA * D₀.radius <
        dist (chartAt ℂ D₀.center x) (chartAt ℂ D₀.center D₀.center) →
      dist (chartAt ℂ D₀.center x) (chartAt ℂ D₀.center D₀.center) <
        3 * D₀.radius / 4 →
      pieceGreen (D₀.shrink tC htC htC1).compl p₁ x -
        pieceGreen (D₀.shrink tC htC htC1).compl p₂ x -
        (pieceGreen (D₀.shrink tD htD htD1).compl p₁ x -
          pieceGreen (D₀.shrink tD htD htD1).compl p₂ x) ≤
      ε + 4 * C₀ / (Real.log (3 * D₀.radius / 4) - Real.log (tA * D₀.radius)) *
        (Real.log (3 * D₀.radius / 4) -
          Real.log (dist (chartAt ℂ D₀.center x) (chartAt ℂ D₀.center D₀.center))) := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Plane-side helper: transfer of subharmonicity along a pointwise equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## Constancy propagation on a preconnected open set from an interior maximum. -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ z ∈ Ω, w z ≤ w xm) → ∀ z ∈ Ω, w z = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {z | z ∈ Ω ∧ w z = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hmax' : ∀ u ∈ Ω, w u ≤ w z := fun u hu => (hmax u hu).trans_eq hzw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hzΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu.trans hzw⟩
    have hto : IsOpen {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hcont : ContinuousAt w z := (hwsub z hzΩ).continuousAt
      filter_upwards [hcont.eventually_ne hzw, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu⟩
    have hsub : Ω ⊆ {z | z ∈ Ω ∧ w z = w xm} ∪ {z | z ∈ Ω ∧ w z ≠ w xm} := by
      intro z hz
      by_cases hzw : w z = w xm
      · exact Or.inl ⟨hz, hzw⟩
      · exact Or.inr ⟨hz, hzw⟩
    have hdisj : Disjoint {z | z ∈ Ω ∧ w z = w xm} {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro z ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun z hz => (hres hz).2
  /- ## Maximum principle on an open set `Ω ≠ univ` with compact exceptional set. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ z ∈ Ω, z ∉ Kc → w z ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ z ∈ Ω, w z ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ z ∈ Ω, w z ≤ w xm := by
      intro z hz
      by_cases hzK : z ∈ Kc
      · exact hxmax ⟨subset_closure hz, hzK⟩
      · exact (hout z hz hzK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun z hz => hwsub z (hCcΩ hz)) (fun z hz => hall z (hCcΩ hz))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    haveI hne2 : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz => (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz => (hf0 _ ((hρsub hz).2)).symm
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Subharmonicity at a point transfers between the surface and an open piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hnety : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hnety := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hnety]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hnety).target :=
      e'.map_subtype_source hnety hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hnety).symm)
        (e'.subtypeRestr hnety).target := e'.subtypeRestr_symm_eqOn hnety
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hnety).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hnety).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw => (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw => (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hnety).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hnety), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hnety).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have mapval : ∀ (P : Opens M) (p : M) (hpP : p ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p, hpP⟩ : ↥P)) = 𝓝[≠] p := by
    intro P p hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## Affine images of harmonic functions are harmonic. -/
  have mharmAffine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
      MHarmonicAt (fun y => a * g y + c) x := by
    intro g x a c hg
    have h1 : HarmonicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := hg
    have h2 := (h1.const_smul (c := a)).add (harmonicAt_const c)
    have heq2 : (a • (g ∘ (chartAt ℂ x).symm) + fun _ => c) =
        (fun y => a * g y + c) ∘ (chartAt ℂ x).symm := by
      funext w
      simp [smul_eq_mul]
    rw [heq2] at h2
    exact h2
  have mharmLin : ∀ (f g : M → ℝ) (a b : ℝ) (z : M), MHarmonicAt f z → MHarmonicAt g z →
      MHarmonicAt (fun y => a * f y + b * g y) z := by
    intro f g a b z hf hg
    have h3 := (mharmAffine f z a 0 hf).add (mharmAffine g z b 0 hg)
    refine mharm_congr _ _ z (Filter.Eventually.of_forall fun y => ?_) h3
    simp only [Pi.add_apply]
    ring
  /- ## The chart logarithm barrier: harmonicity and continuity off the singularity. -/
  have logHarm : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      MHarmonicAt (fun q => Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hzs]
    have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - c‖) (chartAt ℂ x₀ z) := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - c)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hzne
    have heqv : (fun w : ℂ => Real.log ‖w - c‖) =ᶠ[𝓝 (chartAt ℂ x₀ z)]
        ((fun q => Real.log (dist (chartAt ℂ x₀ q) c)) ∘ (chartAt ℂ x₀).symm) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hzs)] with w hw
      simp only [Function.comp_apply, (chartAt ℂ x₀).right_inv hw, dist_eq_norm]
    exact (harmonicAt_congr_nhds heqv).1 hharm
  have logCont : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      ContinuousAt (fun q => Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    have h2 : ContinuousAt (chartAt ℂ x₀) z := (chartAt ℂ x₀).continuousAt hzs
    have h3 : dist (chartAt ℂ x₀ z) c ≠ 0 := (dist_pos.2 hzne).ne'
    exact (h2.dist continuousAt_const).log h3
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dif_pos ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dif_neg]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## The zero function belongs to every piece Green family. -/
  have zeroFam : ∀ (P : Opens M) (p : M) (hp : p ∈ P),
      (fun _ : ↥P => (0 : ℝ)) ∈ greenFamily (⟨p, hp⟩ : ↥P) := by
    intro P p hp
    haveI : Nonempty ↥P := ⟨⟨p, hp⟩⟩
    refine ⟨fun z _ => (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt,
      continuousOn_const, ⟨∅, isCompact_empty, Set.empty_ne_univ, fun z _ => rfl⟩,
      ⟨0, ?_⟩⟩
    have hcont : ContinuousAt (poleCoord (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) := by
      have h1 : ContinuousAt (chartAt ℂ (⟨p, hp⟩ : ↥P)) (⟨p, hp⟩ : ↥P) :=
        (chartAt ℂ (⟨p, hp⟩ : ↥P)).continuousAt (mem_chart_source ℂ _)
      exact h1.sub continuousAt_const
    have h0 : poleCoord (⟨p, hp⟩ : ↥P) (⟨p, hp⟩ : ↥P) = 0 := sub_self _
    have hev : ∀ᶠ z in 𝓝 (⟨p, hp⟩ : ↥P), ‖poleCoord (⟨p, hp⟩ : ↥P) z‖ ≤ 1
        := by
      have h2 := hcont.tendsto
      rw [h0] at h2
      have h3 : closedBall (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ one_pos
      filter_upwards [h2 h3] with z hz
      rw [← dist_zero_right]
      exact mem_closedBall.1 hz
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    have hlog := Real.log_nonpos (norm_nonneg _) hz
    simpa using hlog
  /- ## Zero extension of a piece candidate to the surface. -/
  have extendC : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (v : ↥P → ℝ),
      v ∈ greenFamily (⟨p, hp⟩ : ↥P) →
      ∃ (vE : M → ℝ) (KE : Set M) (Cv : ℝ),
        (∀ z : ↥P, vE z = v z) ∧ MSubharmonicOn vE {p}ᶜ ∧ ContinuousOn vE {p}ᶜ ∧
        IsCompact KE ∧ KE ⊆ (P : Set M) ∧ (∀ y, y ∉ KE → vE y = 0) ∧
        ∀ᶠ y in 𝓝[≠] p, vE y + Real.log ‖poleCoord p y‖ ≤ Cv := by
    intro P p hp v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y => if h : y ∈ P then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥P, w z = v z := by
      intro z
      simp only [hwdef]
      rw [dif_pos z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (P : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ P
      · simp only [hwdef]
        rw [dif_pos hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dif_neg hyP]
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ P
      · have hoe : IsOpenEmbedding (Subtype.val : ↥P → M) :=
          P.2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥P) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥P)) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u => (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥P → M) (𝓝 (⟨y, hyP⟩ : ↥P)) = 𝓝 y :=
          hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem => hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ P
      · have hnz : (⟨y, hyP⟩ : ↥P) ≠ ⟨p, hp⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val P w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem => hyP (hKwsub hmem)) (fun z hz => hKwzero z hz)
    refine ⟨w, Kw, C, hwval, hwsub, hwcont, hKwcomp, hKwsub, hKwzero, ?_⟩
    rw [← mapval P p hp, Filter.eventually_map]
    filter_upwards [hC] with z hz
    have hpc : poleCoord (⟨p, hp⟩ : ↥P) z = poleCoord p (z : M) := rfl
    rw [hwval z, ← hpc]
    exact hz
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    haveI := hcs
    haveI := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon => hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z => pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## The center chart, the pieces and the pole-ball geometry. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D₀.center with he₀
  set c₀ : ℂ := e₀ D₀.center with hc₀
  set r₀ : ℝ := D₀.radius with hr₀def
  have hr₀ : 0 < r₀ := D₀.radius_pos
  have hcb₀tgt : closedBall c₀ r₀ ⊆ e₀.target := D₀.closedBall_subset
  have hcar₀ : D₀.closedCarrier = e₀.symm '' closedBall c₀ r₀ := rfl
  set ρs : ℝ := 3 * r₀ / 4 with hρs
  have hρs0 : 0 < ρs := by rw [hρs]; linarith only [hr₀]
  have hρsr₀ : ρs < r₀ := by rw [hρs]; linarith only [hr₀]
  set Γ₀ : Set M := e₀.symm '' sphere c₀ ρs with hΓ₀
  set PC : Opens M := (D₀.shrink tC htC htC1).compl with hPC
  set PD : Opens M := (D₀.shrink tD htD htD1).compl with hPD
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar1cp : IsCompact Car1 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₁.continuousOn_symm.mono htgt1)
  have hCar2cp : IsCompact Car2 := (isCompact_closedBall _ _).image_of_continuousOn
    (e₂.continuousOn_symm.mono htgt2)
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ := by
    rintro z ⟨w, hw, rfl⟩
    exact hav1 w hw
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 := by
    rintro z ⟨w, hw, rfl⟩
    exact hav2 w hw
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  set B₁ : Set M := e₁.source ∩ e₁ ⁻¹' ball c₁ r₁ with hB₁
  set B₂ : Set M := e₂.source ∩ e₂ ⁻¹' ball c₂ r₂ with hB₂
  have hp₁B₁ : p₁ ∈ B₁ :=
    ⟨hp₁src, by rw [Set.mem_preimage, ← hc₁]; exact mem_ball_self hr₁⟩
  have hp₂B₂ : p₂ ∈ B₂ :=
    ⟨hp₂src, by rw [Set.mem_preimage, ← hc₂]; exact mem_ball_self hr₂⟩
  have hB₁Car : B₁ ⊆ Car1 := by
    rintro x ⟨hxsrc, hxpre⟩
    rw [Set.mem_preimage] at hxpre
    exact ⟨e₁ x, ball_subset_closedBall (ball_subset_ball (by linarith only [hr₁]) hxpre),
      e₁.left_inv hxsrc⟩
  have hB₂Car : B₂ ⊆ Car2 := by
    rintro x ⟨hxsrc, hxpre⟩
    rw [Set.mem_preimage] at hxpre
    exact ⟨e₂ x, ball_subset_closedBall (ball_subset_ball (by linarith only [hr₂]) hxpre),
      e₂.left_inv hxsrc⟩
  have hp₁C : p₁ ∈ PC := fun hmem => (hCar1av p₁ hp₁Car1).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htC1))) hmem)
  have hp₂C : p₂ ∈ PC := fun hmem => (hCar2av p₂ hp₂Car2).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htC1))) hmem)
  have hp₁D : p₁ ∈ PD := fun hmem => (hCar1av p₁ hp₁Car1).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htD1))) hmem)
  have hp₂D : p₂ ∈ PD := fun hmem => (hCar2av p₂ hp₂Car2).1
    ((Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le htD1))) hmem)
  haveI hconnC : ConnectedSpace ↥PC :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  haveI hncC : NoncompactSpace ↥PC := noncompactSpace_coordDisk_compl _
  haveI hconnD : ConnectedSpace ↥PD :=
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl _)
  haveI hncD : NoncompactSpace ↥PD := noncompactSpace_coordDisk_compl _
  have hGF1C : HasGreenFunction (⟨p₁, hp₁C⟩ : ↥PC) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁C
  have hGF2C : HasGreenFunction (⟨p₂, hp₂C⟩ : ↥PC) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂C
  have hGF1D : HasGreenFunction (⟨p₁, hp₁D⟩ : ↥PD) :=
    hasGreenFunction_coordDisk_compl _ p₁ hp₁D
  have hGF2D : HasGreenFunction (⟨p₂, hp₂D⟩ : ↥PD) :=
    hasGreenFunction_coordDisk_compl _ p₂ hp₂D
  have hcbtgtA : closedBall c₀ (tA * r₀) ⊆ e₀.target :=
    (closedBall_subset_closedBall (mul_le_of_le_one_left hr₀.le htA1)).trans hcb₀tgt
  have hcarmemA : ∀ z : M, z ∈ (D₀.shrink tA htA htA1).closedCarrier ↔
      z ∈ e₀.source ∧ dist (e₀ z) c₀ ≤ tA * r₀ := by
    intro z
    have hcarA : (D₀.shrink tA htA htA1).closedCarrier =
        e₀.symm '' closedBall c₀ (tA * r₀) := rfl
    rw [hcarA]
    exact hmemCB e₀ c₀ (tA * r₀) hcbtgtA z
  have hδltA : tA * r₀ < ρs := by
    have h2 : tA * r₀ ≤ 1 / 4 * r₀ := mul_le_mul_of_nonneg_right htA4 hr₀.le
    rw [hρs]
    linarith only [h2, hr₀]
  have hdenA0 : 0 < Real.log ρs - Real.log (tA * r₀) := by
    have h1 : Real.log (tA * r₀) < Real.log ρs := by
      apply Real.log_lt_log
      · exact mul_pos htA hr₀
      · exact hδltA
    linarith only [h1]
  intro x hxsrc hxlo hxhi
  set δA : ℝ := tA * r₀ with hδA
  have hδA0 : 0 < δA := by
    rw [hδA]
    exact mul_pos htA hr₀
  have hδAρ : δA < ρs := hδltA
  have hdenA : 0 < Real.log ρs - Real.log δA := hdenA0
  set η : ℝ := 4 * C₀ / (Real.log ρs - Real.log δA) with hη
  have hη0 : 0 < η := by
    rw [hη]
    exact div_pos (by linarith only [hC₀1]) hdenA
  have hcancel : η * (Real.log ρs - Real.log δA) = 4 * C₀ := by
    rw [hη]
    exact div_mul_cancel₀ _ hdenA.ne'
  set L : M → ℝ := fun q => Real.log ρs - Real.log (dist (e₀ q) c₀) with hL
  set W : M → ℝ := fun q => pieceGreen (PC) p₂ q +
    (pieceGreen (PD) p₁ q - pieceGreen (PD) p₂ q) + (ε + η * L q) with hW
  set Ωσ : Set M := e₀.symm '' (ball c₀ ρs \ closedBall c₀ δA) with hΩσ
  have hΩσsub : ball c₀ ρs \ closedBall c₀ δA ⊆ e₀.target :=
    (Set.diff_subset.trans ball_subset_closedBall).trans
      ((closedBall_subset_closedBall hρsr₀.le).trans hcb₀tgt)
  have hΩσopen : IsOpen Ωσ := by
    rw [hΩσ, himg e₀ _ hΩσsub]
    exact e₀.isOpen_inter_preimage (isOpen_ball.sdiff isClosed_closedBall)
  have hΩσmem : ∀ z ∈ Ωσ, z ∈ e₀.source ∧ δA < dist (e₀ z) c₀ ∧
      dist (e₀ z) c₀ < ρs := by
    intro z hz
    rw [hΩσ, himg e₀ _ hΩσsub] at hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall] at hz2
    exact ⟨hz1, not_le.1 hz2.2, hz2.1⟩
  have hΩσmem' : ∀ z : M, z ∈ e₀.source → δA < dist (e₀ z) c₀ →
      dist (e₀ z) c₀ < ρs → z ∈ Ωσ := by
    intro z hz1 hz2 hz3
    rw [hΩσ, himg e₀ _ hΩσsub]
    refine ⟨hz1, ?_⟩
    rw [Set.mem_preimage, Set.mem_diff, mem_ball, mem_closedBall]
    exact ⟨hz3, not_le.2 hz2⟩
  set Kσ : Set M := e₀.symm '' (closedBall c₀ ρs \ ball c₀ δA) with hKσ
  have hKσtgt : closedBall c₀ ρs \ ball c₀ δA ⊆ e₀.target :=
    Set.diff_subset.trans ((closedBall_subset_closedBall hρsr₀.le).trans hcb₀tgt)
  have hKσcomp : IsCompact Kσ :=
    ((isCompact_closedBall c₀ ρs).diff isOpen_ball).image_of_continuousOn
      (e₀.continuousOn_symm.mono hKσtgt)
  have hΩσKσ : Ωσ ⊆ Kσ := by
    rw [hΩσ, hKσ]
    exact Set.image_mono (fun w hw => ⟨ball_subset_closedBall hw.1,
      fun h => hw.2 (ball_subset_closedBall h)⟩)
  have hcenΩσ : D₀.center ∉ Ωσ := by
    intro hcon
    obtain ⟨-, h2, -⟩ := hΩσmem _ hcon
    rw [← hc₀, dist_self] at h2
    exact absurd h2 (not_lt.2 hδA0.le)
  have hΩσne : Ωσ ≠ Set.univ := by
    intro hcon
    apply hcenΩσ
    rw [hcon]
    trivial
  have hΩσCar : ∀ z ∈ Ωσ, z ∈ D₀.closedCarrier := by
    intro z hz
    obtain ⟨hz1, -, hz3⟩ := hΩσmem z hz
    rw [hcar₀]
    exact ⟨e₀ z, mem_closedBall.2 (by linarith only [hz3, hρsr₀]), e₀.left_inv hz1⟩
  have hΩσB : ∀ z ∈ Ωσ, z ∉ B₁ ∧ z ∉ B₂ := by
    intro z hz
    constructor
    · intro hmem
      exact (hCar1av z (hB₁Car hmem)).1 (hΩσCar z hz)
    · intro hmem
      exact (hCar2av z (hB₂Car hmem)).1 (hΩσCar z hz)
  have hΩσnp : ∀ z ∈ Ωσ, z ≠ p₁ ∧ z ≠ p₂ := by
    intro z hz
    constructor
    · intro hcon
      exact (hΩσB z hz).1 (hcon ▸ hp₁B₁)
    · intro hcon
      exact (hΩσB z hz).2 (hcon ▸ hp₂B₂)
  have hΩσW : ∀ z ∈ Ωσ, z ∈ PC ∧ z ∈ PD := by
    intro z hz
    obtain ⟨hz1, hz2, -⟩ := hΩσmem z hz
    have hnotA : z ∉ (D₀.shrink tA htA htA1).closedCarrier := by
      intro hmem
      have h3 := ((hcarmemA z).1 hmem).2
      linarith only [hδA, h3, hz2]
    exact ⟨fun hmem => hnotA (hCA hmem), fun hmem => hnotA (hDA hmem)⟩
  have hWharm : ∀ z ∈ Ωσ, MHarmonicAt W z := by
    intro z hz
    obtain ⟨hzsrc, hzlo, hzhi⟩ := hΩσmem z hz
    obtain ⟨hzC, hzD⟩ := hΩσW z hz
    obtain ⟨hznp₁, hznp₂⟩ := hΩσnp z hz
    have h1 : MHarmonicAt (pieceGreen (PC) p₂) z :=
      pgharm (PC) p₂ hp₂C hconnC hncC hGF2C z hzC hznp₂
    have h2 : MHarmonicAt (pieceGreen (PD) p₁) z :=
      pgharm (PD) p₁ hp₁D hconnD hncD hGF1D z hzD hznp₁
    have h3 : MHarmonicAt (pieceGreen (PD) p₂) z :=
      pgharm (PD) p₂ hp₂D hconnD hncD hGF2D z hzD hznp₂
    have hzcne : e₀ z ≠ c₀ := by
      intro hcon
      rw [hcon, dist_self] at hzlo
      exact absurd hzlo (not_lt.2 hδA0.le)
    have h4 : MHarmonicAt (fun q => Real.log (dist (e₀ q) c₀)) z :=
      logHarm D₀.center c₀ z hzsrc hzcne
    have h5 := mharmLin _ _ 1 (-1) z h2 h3
    have h6 := mharmLin _ _ 1 1 z h1 h5
    have h7 := mharmAffine _ z (-η) (ε + η * Real.log ρs) h4
    have h8 := mharmLin _ _ 1 1 z h6 h7
    refine mharm_congr _ _ z (Filter.Eventually.of_forall fun y => ?_) h8
    simp only [hW, hL]
    ring
  have hxΩσ : x ∈ Ωσ := hΩσmem' x hxsrc (by linarith only [hδA, hxlo]) hxhi
  have hxWC : x ∈ PC := (hΩσW x hxΩσ).1
  have hbddCC := (mharmonicOn_greenEnvelope hGF1C).2
  have hkey : pieceGreen (PC) p₁ x ≤ W x := by
    rw [pgval (PC) p₁ hp₁C x hxWC]
    simp only [greenEnvelope]
    refine csSup_le
      ⟨0, (fun _ : ↥(PC) => (0 : ℝ)), zeroFam (PC) p₁ hp₁C, rfl⟩ ?_
    rintro b ⟨v, hv, rfl⟩
    obtain ⟨vE, KE, Cv, hvEval, hvEsub, hvEcont, hKEc, hKEP, hKE0, hCv⟩ :=
      extendC (PC) p₁ hp₁C v hv
    have hpairv : ∀ z : M, z ∉ B₁ → z ∉ B₂ →
        vE z - pieceGreen (PC) p₂ z ≤ C₀ := by
      intro z hz1 hz2
      have hznp₁ : z ≠ p₁ := fun hcon => hz1 (hcon ▸ hp₁B₁)
      by_cases hzP : z ∈ PC
      · have h1 : vE z ≤ pieceGreen (PC) p₁ z := by
          have h2 : v ⟨z, hzP⟩ ≤ greenEnvelope (⟨p₁, hp₁C⟩ : ↥PC) ⟨z, hzP⟩ :=
            le_csSup (hbddCC _ (fun hcon => hznp₁ (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
          rw [pgval (PC) p₁ hp₁C z hzP]
          calc vE z = v ⟨z, hzP⟩ := hvEval ⟨z, hzP⟩
            _ ≤ _ := h2
        have h3 := (abs_le.1 (hbdC z hz1 hz2)).2
        linarith only [h1, h3]
      · have h1 : vE z = 0 := hKE0 z (fun hmem => hzP (hKEP hmem))
        have h2 : pieceGreen (PC) p₂ z = 0 := pgzero _ _ _ hzP
        rw [h1, h2]
        linarith only [hC₀1]
    set wc : M → ℝ := fun z => max (vE z - W z) 0 with hwc
    have hwcsub : MSubharmonicOn wc Ωσ := by
      intro z hz
      have h1 : MSubharmonicAt (fun q => vE q - W q) z :=
        (hvEsub z (Set.mem_compl_singleton_iff.2 (hΩσnp z hz).1)).sub_mharmonicAt
          (hWharm z hz)
      have h2 : MSubharmonicAt (fun _ : M => (0 : ℝ)) z :=
        (mharmonicAt_const (a := (0 : ℝ))).msubharmonicAt
      rw [hwc]
      exact h1.max h2
    have hwcout : ∀ z ∈ Ωσ, z ∉ Kσ → wc z ≤ 0 := by
      intro z hz hzK
      exact absurd (hΩσKσ hz) hzK
    have hwcfr : ∀ y ∈ closure Ωσ \ Ωσ, ContinuousAt wc y ∧ wc y ≤ 0 := by
      rintro y ⟨hycl, hyΩ⟩
      have hyK : y ∈ Kσ := (hKσcomp.isClosed.closure_subset_iff.2 hΩσKσ) hycl
      rw [hKσ] at hyK
      obtain ⟨w, ⟨hw1, hw2⟩, hwy⟩ := hyK
      have hwt : w ∈ e₀.target := hKσtgt ⟨hw1, hw2⟩
      have hysrc : y ∈ e₀.source := hwy ▸ e₀.map_target hwt
      have hyval : e₀ y = w := by rw [← hwy, e₀.right_inv hwt]
      have hyd1 : δA ≤ dist (e₀ y) c₀ := by
        rw [hyval]
        exact not_lt.1 (fun h => hw2 (mem_ball.2 h))
      have hyd2 : dist (e₀ y) c₀ ≤ ρs := by
        rw [hyval]
        exact mem_closedBall.1 hw1
      have hyCar : y ∈ D₀.closedCarrier := by
        rw [hcar₀]
        exact ⟨e₀ y, mem_closedBall.2 (by linarith only [hyd2, hρsr₀]),
          e₀.left_inv hysrc⟩
      have hyB₁ : y ∉ B₁ := fun hmem => (hCar1av y (hB₁Car hmem)).1 hyCar
      have hyB₂ : y ∉ B₂ := fun hmem => (hCar2av y (hB₂Car hmem)).1 hyCar
      have hynp₁ : y ≠ p₁ := fun hcon => hyB₁ (hcon ▸ hp₁B₁)
      have hynp₂ : y ≠ p₂ := fun hcon => hyB₂ (hcon ▸ hp₂B₂)
      have hycne : e₀ y ≠ c₀ := by
        intro hcon
        rw [hcon, dist_self] at hyd1
        exact absurd hyd1 (not_le.2 hδA0)
      have hydisj : dist (e₀ y) c₀ = δA ∨ dist (e₀ y) c₀ = ρs := by
        rcases lt_or_eq_of_le hyd1 with h1 | h1
        · rcases lt_or_eq_of_le hyd2 with h2 | h2
          · exact absurd (hΩσmem' y hysrc h1 h2) hyΩ
          · exact Or.inr h2
        · exact Or.inl h1.symm
      have hLcont : ContinuousAt (fun q => Real.log (dist (e₀ q) c₀)) y :=
        logCont D₀.center c₀ y hysrc hycne
      rcases hydisj with hyd | hyd
      · -- the inner circle: the capped competitor vanishes on a neighbourhood
        have hcbar : ContinuousAt (fun q : M => 2 * C₀ - ε - η *
            (Real.log ρs - Real.log (dist (e₀ q) c₀))) y :=
          continuousAt_const.sub
            (continuousAt_const.mul (continuousAt_const.sub hLcont))
        have hcbarneg : 2 * C₀ - ε - η *
            (Real.log ρs - Real.log (dist (e₀ y) c₀)) < 0 := by
          rw [hyd]
          linarith only [hcancel, hε, hC₀1]
        have havoid : IsOpen ((Car1 ∪ Car2)ᶜ : Set M) :=
          (hCar1cp.union hCar2cp).isClosed.isOpen_compl
        have hyav : y ∈ ((Car1 ∪ Car2)ᶜ : Set M) := by
          rintro (h | h)
          · exact (hCar1av y h).1 hyCar
          · exact (hCar2av y h).1 hyCar
        have hev : ∀ᶠ z in 𝓝 y, wc z = 0 := by
          filter_upwards [havoid.mem_nhds hyav,
            hcbar.tendsto.eventually_lt_const hcbarneg] with z hzav hzneg
          have hz1 : z ∉ B₁ := fun hmem => hzav (Or.inl (hB₁Car hmem))
          have hz2 : z ∉ B₂ := fun hmem => hzav (Or.inr (hB₂Car hmem))
          have h1 := hpairv z hz1 hz2
          have h2 := (abs_le.1 (hbdD z hz1 hz2)).1
          have hle : vE z - W z ≤ 0 := by
            simp only [hW, hL]
            linarith only [h1, h2, hzneg]
          rw [hwc]
          simp only
          rw [max_eq_right hle]
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hev.self_of_nhds]
      · -- the outer circle: the sphere hypothesis applies
        have hyΓ₀ : y ∈ Γ₀ := by
          rw [hΓ₀]
          exact ⟨e₀ y, mem_sphere.2 hyd, e₀.left_inv hysrc⟩
        have hnotA : y ∉ (D₀.shrink tA htA htA1).closedCarrier := by
          intro hmem
          have h3 := ((hcarmemA y).1 hmem).2
          rw [hyd] at h3
          linarith only [hδA, h3, hδAρ]
        have hyWC : y ∈ PC := fun hmem => hnotA (hCA hmem)
        have hyWD : y ∈ PD := fun hmem => hnotA (hDA hmem)
        have hcv : ContinuousAt vE y := hvEcont.continuousAt
          (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hynp₁))
        have hcg1 : ContinuousAt (pieceGreen (PC) p₂) y :=
          (pgharm (PC) p₂ hp₂C hconnC hncC hGF2C
            y hyWC hynp₂).continuousAt
        have hcg2 : ContinuousAt (pieceGreen (PD) p₁) y :=
          (pgharm (PD) p₁ hp₁D hconnD hncD hGF1D
            y hyWD hynp₁).continuousAt
        have hcg3 : ContinuousAt (pieceGreen (PD) p₂) y :=
          (pgharm (PD) p₂ hp₂D hconnD hncD hGF2D
            y hyWD hynp₂).continuousAt
        have hcW : ContinuousAt W y :=
          (hcg1.add (hcg2.sub hcg3)).add
            (continuousAt_const.add
              (continuousAt_const.mul (continuousAt_const.sub hLcont)))
        have h1 : vE y ≤ pieceGreen (PC) p₁ y := by
          have h2 : v ⟨y, hyWC⟩ ≤ greenEnvelope (⟨p₁, hp₁C⟩ : ↥PC) ⟨y, hyWC⟩ :=
            le_csSup (hbddCC _ (fun hcon => hynp₁ (congrArg Subtype.val hcon)))
              ⟨v, hv, rfl⟩
          rw [pgval (PC) p₁ hp₁C y hyWC]
          calc vE y = v ⟨y, hyWC⟩ := hvEval ⟨y, hyWC⟩
            _ ≤ _ := h2
        have h2 := hsph y hyΓ₀
        refine ⟨by rw [hwc]; exact (hcv.sub hcW).max continuousAt_const, ?_⟩
        rw [hwc]
        simp only
        apply max_le _ le_rfl
        simp only [hW, hL]
        rw [hyd, sub_self, mul_zero]
        linarith only [h1, h2]
    have hwcle := maxPrin Ωσ wc 0 Kσ hΩσopen hΩσne hwcsub hKσcomp hwcout hwcfr
    have h9 := hwcle x hxΩσ
    rw [hwc] at h9
    simp only at h9
    have h10 : vE x - W x ≤ 0 := le_trans (le_max_left _ _) h9
    change v ⟨x, hxWC⟩ ≤ W x
    have h11 : v ⟨x, hxWC⟩ = vE x := (hvEval ⟨x, hxWC⟩).symm
    rw [h11]
    linarith only [h10]
  have hfin : pieceGreen PC p₁ x - pieceGreen PC p₂ x -
      (pieceGreen PD p₁ x - pieceGreen PD p₂ x) ≤ ε + η * L x := by
    simp only [hW] at hkey
    linarith only [hkey]
  simp only [hL] at hfin
  rw [hη] at hfin
  exact hfin

/-- A sequence of harmonic functions on a disk which is uniformly Cauchy on an interior
circle converges on the enclosed disk, with harmonic limit: the Poisson kernel bounds
propagate the circle oscillation inward with a two-point comparison constant. -/
private theorem bipolarGreen_aux4 {ca : ℂ} {ra : ℝ} (hs : ℕ → ℂ → ℝ) (hra : 0 < ra)
    (hharm : ∀ n, HarmonicOnNhd (hs n) (ball ca (2 * ra)))
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ sphere ca (3 * ra /
        2),
      |hs m ζ - hs n ζ| ≤ ε) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball ca (3 * ra / 2)) ∧
      ∀ w ∈ ball ca (3 * ra / 2), Tendsto (fun n => hs n w) atTop (𝓝 (H w)) := by
  classical
  /- ## The Poisson kernel is continuous on the circle, for interior points. -/
  have hKcont : ∀ (c z : ℂ) (ρ : ℝ), z ∈ ball c ρ →
      ContinuousOn (poissonKernel c z) (sphere c ρ) := by
    intro c z ρ hz
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    apply Complex.continuous_re.comp_continuousOn
    rw [herglotzRieszKernel_fun_def]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro w hw
    have hwn : ‖w - c‖ = ρ := by rw [← dist_eq_norm]; simpa using (mem_sphere.1 hw)
    have hzlt : ‖z - c‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hz
    intro hcontra
    have hwz : w - c = z - c := by linear_combination (norm := ring_nf) hcontra
    rw [hwz] at hwn
    linarith only [hwn, hzlt]
  /- ## Circle averages of uniformly close functions are close. -/
  have havg_diff : ∀ (F g : ℂ → ℝ) (c : ℂ) (ρ A : ℝ), 0 < ρ →
      ContinuousOn F (sphere c ρ) → ContinuousOn g (sphere c ρ) →
      (∀ ζ ∈ sphere c ρ, |F ζ - g ζ| ≤ A) →
      |Real.circleAverage F c ρ - Real.circleAverage g c ρ| ≤ A := by
    intro F g c ρ A hρ hF hg hbd
    have hFi : CircleIntegrable F c ρ := hF.circleIntegrable hρ.le
    have hgi : CircleIntegrable g c ρ := hg.circleIntegrable hρ.le
    have habsci : CircleIntegrable (fun ζ => |F ζ - g ζ|) c ρ :=
      ((hF.sub hg).abs).circleIntegrable hρ.le
    rw [← Real.circleAverage_fun_sub hFi hgi]
    calc |Real.circleAverage (fun ζ => F ζ - g ζ) c ρ|
        ≤ Real.circleAverage |fun ζ => F ζ - g ζ| c ρ :=
          Real.abs_circleAverage_le_circleAverage_abs
      _ ≤ A := by
          apply Real.circleAverage_mono_on_of_le_circle habsci
          intro ζ hζ
          rw [abs_of_pos hρ] at hζ
          exact hbd ζ hζ
  /- ## The Poisson comparison: two harmonic functions close on a circle are close inside. -/
  have poissonDiff : ∀ (h₁ h₂ : ℂ → ℝ) (c : ℂ) (ρ ε : ℝ), 0 < ρ → 0 ≤ ε →
      HarmonicOnNhd h₁ (closedBall c ρ) → HarmonicOnNhd h₂ (closedBall c ρ) →
      (∀ ζ ∈ sphere c ρ, |h₁ ζ - h₂ ζ| ≤ ε) →
      ∀ w ∈ ball c ρ, |h₁ w - h₂ w| ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) * ε := by
    intro h₁ h₂ c ρ ε hρ hε hh₁ hh₂ hsp w hw
    have haz : ‖w - c‖ < ρ := by rw [← dist_eq_norm]; exact mem_ball.1 hw
    have haz0 : 0 ≤ ‖w - c‖ := norm_nonneg _
    have hKb0 : 0 ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) :=
      div_nonneg (by linarith only [hρ, haz0]) (by linarith only [haz])
    have hKbound : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c w ζ| ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) := by
      intro ζ hζ
      have hup : poissonKernel c w ζ ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        exact re_herglotzRieszKernel_le hζ hw
      have hlo : 0 ≤ poissonKernel c w ζ := by
        rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
          herglotzRieszKernel_def]
        refine le_trans ?_ (le_re_herglotzRieszKernel hζ hw)
        apply div_nonneg <;> linarith only [hρ, haz0, haz]
      rw [abs_of_nonneg hlo]
      exact hup
    have hrep1 := hh₁.circleAverage_poissonKernel_smul hw
    have hrep2 := hh₂.circleAverage_poissonKernel_smul hw
    have hrep1' : Real.circleAverage (fun ζ => poissonKernel c w ζ * h₁ ζ) c ρ = h₁ w := by
      rw [← hrep1]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    have hrep2' : Real.circleAverage (fun ζ => poissonKernel c w ζ * h₂ ζ) c ρ = h₂ w := by
      rw [← hrep2]
      apply Real.circleAverage_congr_sphere
      intro ζ _
      simp [smul_eq_mul]
    have hc₁ : ContinuousOn (fun ζ => poissonKernel c w ζ * h₁ ζ) (sphere c ρ) :=
      (hKcont c w ρ hw).mul (hh₁.continuousOn.mono sphere_subset_closedBall)
    have hc₂ : ContinuousOn (fun ζ => poissonKernel c w ζ * h₂ ζ) (sphere c ρ) :=
      (hKcont c w ρ hw).mul (hh₂.continuousOn.mono sphere_subset_closedBall)
    have hptbd : ∀ ζ ∈ sphere c ρ,
        |poissonKernel c w ζ * h₁ ζ - poissonKernel c w ζ * h₂ ζ|
          ≤ (ρ + ‖w - c‖) / (ρ - ‖w - c‖) * ε := by
      intro ζ hζ
      have h1 : |poissonKernel c w ζ * h₁ ζ - poissonKernel c w ζ * h₂ ζ|
          = |poissonKernel c w ζ| * |h₁ ζ - h₂ ζ| := by
        rw [← mul_sub, abs_mul]
      rw [h1]
      exact mul_le_mul (hKbound ζ hζ) (hsp ζ hζ) (abs_nonneg _) hKb0
    have hkey := havg_diff _ _ c ρ ((ρ + ‖w - c‖) / (ρ - ‖w - c‖) * ε) hρ hc₁ hc₂
        hptbd
    rw [hrep1', hrep2'] at hkey
    exact hkey
  /- ## A locally uniform limit of plane-harmonic functions is harmonic. -/
  have planeLimitHarm : ∀ (F : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (c : ℂ) (ρ : ℝ), 0 < ρ
      →
      (∀ n, HarmonicOnNhd (F n) (closedBall c ρ)) →
      TendstoUniformlyOn F g atTop (closedBall c ρ) →
      HarmonicOnNhd g (ball c ρ) := by
    intro F g c ρ hρ hF hunif
    have hcont_n : ∀ n, ContinuousOn (F n) (closedBall c ρ) := fun n => (hF n).continuousOn
    have hGcont : ContinuousOn g (closedBall c ρ) :=
      hunif.continuousOn ((Filter.Eventually.of_forall hcont_n).frequently)
    have hPI : ∀ z ∈ ball c ρ, g z = poissonIntegral g c ρ z := by
      intro z hz
      have haz : ‖z - c‖ < ρ := by
        rw [← dist_eq_norm]
        exact mem_ball.1 hz
      have haz0 : 0 ≤ ‖z - c‖ := norm_nonneg _
      set Kb : ℝ := (ρ + ‖z - c‖) / (ρ - ‖z - c‖) with hKbdef
      have hKb0 : 0 ≤ Kb := div_nonneg (by linarith only [hρ, haz0])
        (by linarith only [haz])
      have hKbound : ∀ ζ ∈ sphere c ρ, |poissonKernel c z ζ| ≤ Kb := by
        intro ζ hζ
        have hup : poissonKernel c z ζ ≤ Kb := by
          rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
            herglotzRieszKernel_def]
          exact re_herglotzRieszKernel_le hζ hz
        have hlo : 0 ≤ poissonKernel c z ζ := by
          rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
            herglotzRieszKernel_def]
          refine le_trans ?_ (le_re_herglotzRieszKernel hζ hz)
          apply div_nonneg <;> linarith only [hρ, haz0, haz]
        rw [abs_of_nonneg hlo]
        exact hup
      have hrep : ∀ n : ℕ, F n z = poissonIntegral (F n) c ρ z := by
        intro n
        have h1 := (hF n).circleAverage_poissonKernel_smul hz
        rw [← h1, poissonIntegral]
        apply Real.circleAverage_congr_sphere
        intro ζ _
        simp [smul_eq_mul]
      have hlimPI : Tendsto (fun n => poissonIntegral (F n) c ρ z)
          atTop (𝓝 (poissonIntegral g c ρ z)) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        have hsphunif := hunif.mono sphere_subset_closedBall
        rw [Metric.tendstoUniformlyOn_iff] at hsphunif
        have hev := hsphunif (ε / (2 * (Kb + 1)))
          (div_pos hε (by linarith only [hKb0]))
        rw [Filter.eventually_atTop] at hev
        obtain ⟨N, hN⟩ := hev
        refine ⟨N, fun n hn => ?_⟩
        rw [Real.dist_eq]
        have hbd : ∀ ζ ∈ sphere c ρ,
            |poissonKernel c z ζ * F n ζ - poissonKernel c z ζ * g ζ|
              ≤ Kb * (ε / (2 * (Kb + 1))) := by
          intro ζ hζ
          have h1 : |poissonKernel c z ζ * F n ζ - poissonKernel c z ζ * g ζ|
              = |poissonKernel c z ζ| * |F n ζ - g ζ| := by
            rw [← mul_sub, abs_mul]
          rw [h1]
          have h2 : |F n ζ - g ζ| ≤ ε / (2 * (Kb + 1)) := by
            have h3 := hN n hn ζ hζ
            rw [Real.dist_eq, abs_sub_comm] at h3
            exact h3.le
          exact mul_le_mul (hKbound ζ hζ) h2 (abs_nonneg _) hKb0
        have hcF : ContinuousOn (fun ζ => poissonKernel c z ζ * F n ζ) (sphere c ρ) :=
          (hKcont c z ρ hz).mul ((hcont_n n).mono sphere_subset_closedBall)
        have hcG : ContinuousOn (fun ζ => poissonKernel c z ζ * g ζ) (sphere c ρ) :=
          (hKcont c z ρ hz).mul (hGcont.mono sphere_subset_closedBall)
        have hkey := havg_diff _ _ c ρ (Kb * (ε / (2 * (Kb + 1)))) hρ hcF hcG hbd
        have hfin : Kb * (ε / (2 * (Kb + 1))) < ε := by
          rw [div_eq_mul_inv]
          have h4 : Kb * (ε * (2 * (Kb + 1))⁻¹) ≤ (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) := by
            apply mul_le_mul_of_nonneg_right (by linarith only [])
              (mul_nonneg hε.le (inv_nonneg.2 (by linarith only [hKb0])))
          have h5 : (Kb + 1) * (ε * (2 * (Kb + 1))⁻¹) = ε / 2 := by
            field_simp
          rw [h5] at h4
          linarith only [h4, hε]
        exact lt_of_le_of_lt hkey hfin
      have hGz : Tendsto (fun n => poissonIntegral (F n) c ρ z)
          atTop (𝓝 (g z)) := by
        have h1 := hunif.tendsto_at (ball_subset_closedBall hz)
        exact h1.congr hrep
      exact tendsto_nhds_unique hGz hlimPI
    have hPharm : HarmonicOnNhd (poissonIntegral g c ρ) (ball c ρ) :=
      poissonIntegral_harmonicOn _ _ hρ (hGcont.mono sphere_subset_closedBall)
    intro w hw
    have hev : g =ᶠ[𝓝 w] poissonIntegral g c ρ :=
      eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) hPI
    exact (harmonicAt_congr_nhds hev).mpr (hPharm _ hw)
  have hkey : ∀ ρ : ℝ, 0 < ρ → ρ < 3 * ra / 2 → ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ w ∈ closedBall ca ρ,
        |hs m w - hs n w| ≤ (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) * ε := by
    intro ρ hρ0 hρlt ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun m hm n hn w hw => ?_⟩
    have hsub : closedBall ca (3 * ra / 2) ⊆ ball ca (2 * ra) :=
      closedBall_subset_ball (by linarith only [hra])
    have hwball : w ∈ ball ca (3 * ra / 2) :=
      mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hw) hρlt)
    have hcmp := poissonDiff (hs m) (hs n) ca (3 * ra / 2) ε
      (by linarith only [hra])
      hε.le (fun v hv => hharm m v (hsub hv))
      (fun v hv => hharm n v (hsub hv))
      (fun ζ hζ => hN m hm n hn ζ hζ) w hwball
    have h1 : ‖w - ca‖ ≤ ρ := by
      rw [← dist_eq_norm]
      exact mem_closedBall.1 hw
    have hwlt : ‖w - ca‖ < 3 * ra / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hwball
    have hK : (3 * ra / 2 + ‖w - ca‖) / (3 * ra / 2 - ‖w - ca‖)
        ≤ (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) := by
      have hn0 : 0 ≤ ‖w - ca‖ := norm_nonneg _
      apply div_le_div₀ (by linarith only [hn0, h1, hra, hρ0])
        (by linarith only [h1]) (by linarith only [hρlt]) (by linarith only [h1])
    calc |hs m w - hs n w|
        ≤ (3 * ra / 2 + ‖w - ca‖) / (3 * ra / 2 - ‖w - ca‖) * ε := hcmp
      _ ≤ (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) * ε :=
          mul_le_mul_of_nonneg_right hK hε.le
  have hptw : ∀ w ∈ ball ca (3 * ra / 2),
      ∃ l, Tendsto (fun n => hs n w) atTop (𝓝 l) := by
    intro w hw
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set ρ : ℝ := (dist w ca + 3 * ra / 2) / 2 with hρdef
    have hd : dist w ca < 3 * ra / 2 := mem_ball.1 hw
    have hdnn : 0 ≤ dist w ca := dist_nonneg
    have hρ0 : 0 < ρ := by rw [hρdef]; linarith only [hdnn, hra]
    have hρlt : ρ < 3 * ra / 2 := by rw [hρdef]; linarith only [hd]
    set κ : ℝ := (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) with hκ
    have hκ0 : 0 < κ := by
      rw [hκ]
      exact div_pos (by linarith only [hρ0, hra]) (by linarith only [hρlt])
    obtain ⟨N, hN⟩ := hkey ρ hρ0 hρlt (ε / (2 * κ))
      (div_pos hε (by linarith only [hκ0]))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hN m hm n hn w
      (by rw [mem_closedBall, hρdef]; linarith only [hd, hdnn])
    have h2 : κ * (ε / (2 * κ)) = ε / 2 := by
      field_simp
    calc |hs m w - hs n w| ≤ κ * (ε / (2 * κ)) := h1
      _ = ε / 2 := h2
      _ < ε := by linarith only [hε]
  set H : ℂ → ℝ := fun w => limUnder atTop (fun n => hs n w) with hH
  have hHtend : ∀ w ∈ ball ca (3 * ra / 2),
      Tendsto (fun n => hs n w) atTop (𝓝 (H w)) := by
    intro w hw
    obtain ⟨l, hl⟩ := hptw w hw
    have h1 : H w = l := hl.limUnder_eq
    rw [h1]
    exact hl
  refine ⟨H, ?_, hHtend⟩
  intro w₀ hw₀
  set ρw : ℝ := (3 * ra / 2 - dist w₀ ca) / 2 with hρw
  have hd0 : dist w₀ ca < 3 * ra / 2 := mem_ball.1 hw₀
  have hρw0 : 0 < ρw := by rw [hρw]; linarith only [hd0]
  have hsubw : closedBall w₀ ρw ⊆ ball ca (3 * ra / 2) := by
    intro v hv
    have h1 : dist v ca ≤ dist v w₀ + dist w₀ ca := dist_triangle _ _ _
    have h2 : dist v w₀ ≤ ρw := mem_closedBall.1 hv
    rw [mem_ball]
    rw [hρw] at h2
    linarith only [h1, h2, hd0]
  have hunif : TendstoUniformlyOn (fun n => hs n) H atTop (closedBall w₀ ρw) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set ρ : ℝ := dist w₀ ca + ρw with hρdef2
    have hdnn : 0 ≤ dist w₀ ca := dist_nonneg
    have hρlt : ρ < 3 * ra / 2 := by rw [hρdef2, hρw]; linarith only [hd0]
    have hρ0 : 0 < ρ := by rw [hρdef2]; linarith only [hdnn, hρw0]
    set κ : ℝ := (3 * ra / 2 + ρ) / (3 * ra / 2 - ρ) with hκ
    have hκ0 : 0 < κ := by
      rw [hκ]
      exact div_pos (by linarith only [hρ0, hra]) (by linarith only [hρlt])
    obtain ⟨N, hN⟩ := hkey ρ hρ0 hρlt (ε / (4 * κ))
      (div_pos hε (by linarith only [hκ0]))
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn v hv => ?_⟩
    have hvcb : v ∈ closedBall ca ρ := by
      rw [mem_closedBall, hρdef2]
      have h1 := dist_triangle v w₀ ca
      have h2 := mem_closedBall.1 hv
      linarith only [h1, h2]
    have h3 : ∀ m ≥ N, |hs m v - hs n v| ≤ κ * (ε / (4 * κ)) :=
      fun m hm => hN m hm n hn v hvcb
    have h4 : Tendsto (fun m => |hs m v - hs n v|) atTop
        (𝓝 |H v - hs n v|) :=
      ((hHtend v (hsubw hv)).sub tendsto_const_nhds).abs
    have h5 : |H v - hs n v| ≤ κ * (ε / (4 * κ)) := by
      apply le_of_tendsto h4
      rw [Filter.eventually_atTop]
      exact ⟨N, h3⟩
    have h6 : κ * (ε / (4 * κ)) = ε / 4 := by
      field_simp
    rw [Real.dist_eq]
    calc |H v - hs n v| ≤ ε / 4 := by rw [← h6]; exact h5
      _ < ε := by linarith only [hε]
  have hHharm := planeLimitHarm (fun n => hs n) H w₀ ρw hρw0
    (fun n v hv => hharm n v
      (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 (hsubw hv))
        (by linarith only [hra]))))
    hunif
  exact hHharm w₀ (mem_ball_self hρw0)

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
              Real.log ‖w - chartAt ℂ p₂ p₂‖) ∧
      (∃ C, ∃ V₁ ∈ 𝓝 p₁, ∃ V₂ ∈ 𝓝 p₂, IsCompact (closure V₁) ∧
        IsCompact (closure V₂) ∧ ∀ x ∉ V₁ ∪ V₂, |G x| ≤ C) := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Chart reading of a harmonic surface function is plane-harmonic. -/
  have htransfer : ∀ (x : M) (Ωt : Set M) (v : M → ℝ), MHarmonicOn v Ωt →
      ∀ w ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Ωt,
        HarmonicAt (v ∘ (chartAt ℂ x).symm) w := by
    intro x Ωt v hv w hw
    obtain ⟨hwt, hwΩ⟩ := hw
    have hwΩ' : (chartAt ℂ x).symm w ∈ Ωt := hwΩ
    have hyy : (chartAt ℂ x).symm w ∈ (chartAt ℂ ((chartAt ℂ x).symm w)).source :=
      mem_chart_source ℂ ((chartAt ℂ x).symm w)
    have htrans : AnalyticAt ℂ
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w := by
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hwt
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ ((chartAt ℂ x).symm w)))
          ((chartAt ℂ x).symm w) :=
        contMDiffAt_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas ((chartAt ℂ x).symm w)) hyy
      exact (contMDiffAt_iff_contDiffAt.mp (h2.comp w h1)).analyticAt
    have hmh : HarmonicAt (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm)
        ((⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) w) := hv _ hwΩ'
    have hcomp := harmonicAt_comp_analyticAt hmh htrans
    have hev : (v ∘ ⇑(chartAt ℂ ((chartAt ℂ x).symm w)).symm) ∘
        (⇑(chartAt ℂ ((chartAt ℂ x).symm w)) ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝 w]
        v ∘ ⇑(chartAt ℂ x).symm := by
      have hS : IsOpen ((chartAt ℂ x).target ∩
          ⇑(chartAt ℂ x).symm ⁻¹' (chartAt ℂ ((chartAt ℂ x).symm w)).source) :=
        (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage (chartAt ℂ x).open_target
          (chartAt ℂ ((chartAt ℂ x).symm w)).open_source
      filter_upwards [hS.mem_nhds ⟨hwt, hyy⟩] with ζ hζ
      simp only [Function.comp_apply]
      rw [(chartAt ℂ ((chartAt ℂ x).symm w)).left_inv hζ.2]
    exact (harmonicAt_congr_nhds hev).mp hcomp
  /- ## A plane-harmonic function reads back through a chart as surface-harmonic. -/
  have pullback : ∀ (x₀ : M) (H : ℂ → ℝ) (x : M), x ∈ (chartAt ℂ x₀).source →
      HarmonicAt H (chartAt ℂ x₀ x) → MHarmonicAt (fun y => H (chartAt ℂ x₀ y)) x := by
    intro x₀ H x hx hH
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hx]
    have hev : H =ᶠ[𝓝 (chartAt ℂ x₀ x)]
        ((fun y => H (chartAt ℂ x₀ y)) ∘ (chartAt ℂ x₀).symm) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hx)] with w hw
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x₀).right_inv hw]
    exact (harmonicAt_congr_nhds hev).mp hH
  have mharmSub : ∀ (f g : M → ℝ) (z : M), MHarmonicAt f z → MHarmonicAt g z →
      MHarmonicAt (fun y => f y - g y) z := by
    intro f g z hf hg
    refine mharm_congr (f + -g) _ z (Filter.Eventually.of_forall fun y => ?_) (hf.add hg.neg)
    simp only [Pi.add_apply, Pi.neg_apply]
    exact (sub_eq_add_neg (f y) (g y)).symm
  /- ## The chart logarithm barrier: harmonicity and continuity off the singularity. -/
  have logHarm : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      MHarmonicAt (fun q => Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hzs]
    have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - c‖) (chartAt ℂ x₀ z) := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - c)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hzne
    have heqv : (fun w : ℂ => Real.log ‖w - c‖) =ᶠ[𝓝 (chartAt ℂ x₀ z)]
        ((fun q => Real.log (dist (chartAt ℂ x₀ q) c)) ∘ (chartAt ℂ x₀).symm) := by
      filter_upwards [(chartAt ℂ x₀).open_target.mem_nhds
        ((chartAt ℂ x₀).map_source hzs)] with w hw
      simp only [Function.comp_apply, (chartAt ℂ x₀).right_inv hw, dist_eq_norm]
    exact (harmonicAt_congr_nhds heqv).1 hharm
  have logCont : ∀ (x₀ : M) (c : ℂ) (z : M), z ∈ (chartAt ℂ x₀).source →
      chartAt ℂ x₀ z ≠ c →
      ContinuousAt (fun q => Real.log (dist (chartAt ℂ x₀ q) c)) z := by
    intro x₀ c z hzs hzne
    have h2 : ContinuousAt (chartAt ℂ x₀) z := (chartAt ℂ x₀).continuousAt hzs
    have h3 : dist (chartAt ℂ x₀ z) c ≠ 0 := (dist_pos.2 hzne).ne'
    exact (h2.dist continuousAt_const).log h3
  /- ## Negation of a plane-harmonic function. -/
  have harmNeg : ∀ (h : ℂ → ℝ) (s : Set ℂ), HarmonicOnNhd h s →
      HarmonicOnNhd (fun w => -h w) s := by
    intro h s hh z hz
    have h1 := (hh z hz).const_smul (c := (-1 : ℝ))
    have hev : ((-1 : ℝ) • h) =ᶠ[𝓝 z] fun w => -h w := by
      filter_upwards with w
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    exact (harmonicAt_congr_nhds hev).mp h1
  /- ## Membership through an inverse chart: closed balls and spheres. -/
  have hmemCB : ∀ (e : OpenPartialHomeomorph M ℂ) (c : ℂ) (s : ℝ),
      closedBall c s ⊆ e.target → ∀ z : M,
      (z ∈ e.symm '' closedBall c s ↔ z ∈ e.source ∧ dist (e z) c ≤ s) := by
    intro e c s hsub z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwt : w ∈ e.target := hsub hw
      refine ⟨e.map_target hwt, ?_⟩
      rw [e.right_inv hwt]
      exact mem_closedBall.1 hw
    · rintro ⟨hzs, hzd⟩
      exact ⟨e z, mem_closedBall.2 hzd, e.left_inv hzs⟩
  /- ## Reading the piece Green's function on the surface. -/
  have pgval : ∀ (P : Opens M) (p : M) (hp : p ∈ P) (y : M) (hy : y ∈ P),
      pieceGreen P p y = greenEnvelope (⟨p, hp⟩ : ↥P) ⟨y, hy⟩ := by
    intro P p hp y hy
    simp only [pieceGreen]
    rw [dif_pos ⟨hp, hy⟩]
  have pgzero : ∀ (P : Opens M) (p : M) (y : M), y ∉ P → pieceGreen P p y = 0 := by
    intro P p y hy
    simp only [pieceGreen]
    rw [dif_neg]
    rintro ⟨-, h2⟩
    exact hy h2
  /- ## Harmonicity and nonnegativity of the piece Green reading. -/
  have pgharm : ∀ (P : Opens M) (p : M) (hp : p ∈ P), ConnectedSpace ↥P →
      NoncompactSpace ↥P → HasGreenFunction (⟨p, hp⟩ : ↥P) →
      ∀ y, y ∈ P → y ≠ p → MHarmonicAt (pieceGreen P p) y := by
    intro P p hp hcs hnc hGF y hy hyp
    haveI := hcs
    haveI := hnc
    have h1 := (mharmonicOn_greenEnvelope hGF).1
    have h2 : MHarmonicAt (greenEnvelope (⟨p, hp⟩ : ↥P)) ⟨y, hy⟩ :=
      h1 _ (Set.mem_compl_singleton_iff.mpr
        (fun hcon => hyp (congrArg Subtype.val hcon)))
    exact (mharm_val P (pieceGreen P p) (greenEnvelope (⟨p, hp⟩ : ↥P))
      (fun z => pgval P p hp z z.2) ⟨y, hy⟩).mpr h2
  /- ## The pole radii and the master bound. -/
  obtain ⟨r₁, r₂, C₀, hr₁, hr₂, hC₀1, htgt1', htgt2', hav1', hav2', hGBraw⟩ :=
    bipolarGreen_aux1 D₀ hp₁ hp₂ hne
  have hC₀0 : (0 : ℝ) ≤ C₀ := by linarith only [hC₀1]
  /- ## The center chart and the shrinking pieces. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ D₀.center with he₀
  set c₀ : ℂ := e₀ D₀.center with hc₀
  set r₀ : ℝ := D₀.radius with hr₀def
  have hr₀ : 0 < r₀ := D₀.radius_pos
  have hcb₀tgt : closedBall c₀ r₀ ⊆ e₀.target := D₀.closedBall_subset
  have hcar₀ : D₀.closedCarrier = e₀.symm '' closedBall c₀ r₀ := rfl
  have hcen₀src : D₀.center ∈ e₀.source := mem_chart_source ℂ D₀.center
  have hcen₀car : D₀.center ∈ D₀.closedCarrier :=
    ⟨c₀, mem_closedBall_self hr₀.le, e₀.left_inv hcen₀src⟩
  set t : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 2) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by rw [ht]; positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have htq : ∀ n, t n ≤ 1 / 4 := by
    intro n
    calc t n = (1 / 2 : ℝ) ^ (n + 2) := rfl
      _ ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have htanti : ∀ n m, n ≤ m → t m ≤ t n := fun n m h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htlim : ∀ δ : ℝ, 0 < δ → ∃ n, t n < δ := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn⟩
  set DN : ℕ → CoordDisk M := fun n => D₀.shrink (t n) (ht0 n) (ht1 n) with hDN
  set Wp : ℕ → Opens M := fun n => (DN n).compl with hWp
  have hcarN : ∀ n, (DN n).closedCarrier = e₀.symm '' closedBall c₀ (t n * r₀) :=
    fun n => rfl
  have hcarNsub : ∀ n, (DN n).closedCarrier ⊆ D₀.closedCarrier := by
    intro n
    rw [hcarN n, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr₀.le (ht1 n)))
  have hcarmono : ∀ n m, n ≤ m → (DN m).closedCarrier ⊆ (DN n).closedCarrier := by
    intro n m hnm
    rw [hcarN n, hcarN m]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (htanti n m hnm) hr₀.le))
  have hcbtgtN : ∀ n, closedBall c₀ (t n * r₀) ⊆ e₀.target := fun n =>
    (closedBall_subset_closedBall (mul_le_of_le_one_left hr₀.le (ht1 n))).trans hcb₀tgt
  have hcarmem : ∀ n (z : M), z ∈ (DN n).closedCarrier ↔
      z ∈ e₀.source ∧ dist (e₀ z) c₀ ≤ t n * r₀ := by
    intro n z
    rw [hcarN n]
    exact hmemCB e₀ c₀ (t n * r₀) (hcbtgtN n) z
  have hp₁W : ∀ n, p₁ ∈ Wp n := fun n hmem => hp₁ (hcarNsub n hmem)
  have hp₂W : ∀ n, p₂ ∈ Wp n := fun n hmem => hp₂ (hcarNsub n hmem)
  have hConnW : ∀ n, ConnectedSpace ↥(Wp n) := fun n =>
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl (DN n))
  have hNcW : ∀ n, NoncompactSpace ↥(Wp n) := fun n =>
    noncompactSpace_coordDisk_compl (DN n)
  have hGF1 : ∀ n, HasGreenFunction (⟨p₁, hp₁W n⟩ : ↥(Wp n)) := fun n =>
    hasGreenFunction_coordDisk_compl (DN n) p₁ (hp₁W n)
  have hGF2 : ∀ n, HasGreenFunction (⟨p₂, hp₂W n⟩ : ↥(Wp n)) := fun n =>
    hasGreenFunction_coordDisk_compl (DN n) p₂ (hp₂W n)
  set Gs : ℕ → M → ℝ :=
    fun n x => pieceGreen (Wp n) p₁ x - pieceGreen (Wp n) p₂ x with hGs
  /- ## The pole charts, the avoidance sets and the pole balls. -/
  set e₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₁
  set c₁ : ℂ := e₁ p₁ with hc₁
  have hp₁src : p₁ ∈ e₁.source := mem_chart_source ℂ p₁
  set e₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with he₂
  set c₂ : ℂ := e₂ p₂ with hc₂
  have hp₂src : p₂ ∈ e₂.source := mem_chart_source ℂ p₂
  have htgt1 : closedBall c₁ (2 * r₁) ⊆ e₁.target := htgt1'
  have htgt2 : closedBall c₂ (2 * r₂) ⊆ e₂.target := htgt2'
  have hav1 : ∀ w ∈ closedBall c₁ (2 * r₁),
      e₁.symm w ∉ D₀.closedCarrier ∧ e₁.symm w ≠ p₂ := hav1'
  have hav2 : ∀ w ∈ closedBall c₂ (2 * r₂),
      e₂.symm w ∉ D₀.closedCarrier ∧
        e₂.symm w ∉ e₁.symm '' closedBall c₁ (2 * r₁) := hav2'
  set Car1 : Set M := e₁.symm '' closedBall c₁ (2 * r₁) with hCar1
  set Car2 : Set M := e₂.symm '' closedBall c₂ (2 * r₂) with hCar2
  have hCar1av : ∀ z ∈ Car1, z ∉ D₀.closedCarrier ∧ z ≠ p₂ := by
    rintro z ⟨w, hw, rfl⟩
    exact hav1 w hw
  have hCar2av : ∀ z ∈ Car2, z ∉ D₀.closedCarrier ∧ z ∉ Car1 := by
    rintro z ⟨w, hw, rfl⟩
    exact hav2 w hw
  have hp₁Car1 : p₁ ∈ Car1 :=
    ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂Car2 : p₂ ∈ Car2 :=
    ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  set B₁ : Set M := e₁.source ∩ e₁ ⁻¹' ball c₁ r₁ with hB₁
  set B₂ : Set M := e₂.source ∩ e₂ ⁻¹' ball c₂ r₂ with hB₂
  have hB₁open : IsOpen B₁ := e₁.isOpen_inter_preimage isOpen_ball
  have hB₂open : IsOpen B₂ := e₂.isOpen_inter_preimage isOpen_ball
  have hp₁B₁ : p₁ ∈ B₁ :=
    ⟨hp₁src, by rw [Set.mem_preimage, ← hc₁]; exact mem_ball_self hr₁⟩
  have hp₂B₂ : p₂ ∈ B₂ :=
    ⟨hp₂src, by rw [Set.mem_preimage, ← hc₂]; exact mem_ball_self hr₂⟩
  have hB₁img : e₁.symm '' ball c₁ r₁ = B₁ :=
    himg e₁ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1)
  have hB₂img : e₂.symm '' ball c₂ r₂ = B₂ :=
    himg e₂ _ ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2)
  have hB₁Car : B₁ ⊆ Car1 := by
    rw [← hB₁img, hCar1]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁])))
  have hB₂Car : B₂ ⊆ Car2 := by
    rw [← hB₂img, hCar2]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂])))
  /- ## The quarter disk at the center and the half pole disks. -/
  set Dq : CoordDisk M := D₀.shrink (1 / 4) (by norm_num) (by norm_num) with hDq
  have hDqcar : Dq.closedCarrier = e₀.symm '' closedBall c₀ (1 / 4 * r₀) := rfl
  have hDqsub : Dq.closedCarrier ⊆ D₀.closedCarrier := by
    rw [hDqcar, hcar₀]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₀]))
  have hcarNq : ∀ n, (DN n).closedCarrier ⊆ Dq.closedCarrier := by
    intro n
    rw [hcarN n, hDqcar]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (htq n) hr₀.le))
  set half1 : CoordDisk M := ⟨p₁, r₁ / 2, by linarith only [hr₁],
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1⟩ with hhalf1
  set half2 : CoordDisk M := ⟨p₂, r₂ / 2, by linarith only [hr₂],
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2⟩ with hhalf2
  have hhalf1car : half1.closedCarrier = e₁.symm '' closedBall c₁ (r₁ / 2) := rfl
  have hhalf2car : half2.closedCarrier = e₂.symm '' closedBall c₂ (r₂ / 2) := rfl
  have hhalf1Car : half1.closedCarrier ⊆ Car1 := by
    rw [hhalf1car, hCar1]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₁]))
  have hhalf2Car : half2.closedCarrier ⊆ Car2 := by
    rw [hhalf2car, hCar2]
    exact Set.image_mono (closedBall_subset_closedBall (by linarith only [hr₂]))
  have hp₁half : p₁ ∈ half1.closedCarrier := by
    rw [hhalf1car]
    exact ⟨c₁, mem_closedBall_self (by linarith only [hr₁]),
      by rw [hc₁]; exact e₁.left_inv hp₁src⟩
  have hp₂half : p₂ ∈ half2.closedCarrier := by
    rw [hhalf2car]
    exact ⟨c₂, mem_closedBall_self (by linarith only [hr₂]),
      by rw [hc₂]; exact e₂.left_inv hp₂src⟩
  /- ## The master bound along the shrinking sequence. -/
  have hGB : ∀ n, ∀ x : M, x ∉ B₁ → x ∉ B₂ → |Gs n x| ≤ C₀ :=
    fun n x h1 h2 => hGBraw (t n) (ht0 n) (ht1 n) (htq n) x h1 h2
  /- ## The pole companion sequences from the per-piece companions. -/
  have hdisj12' : ∀ w ∈ closedBall c₁ (2 * r₁),
      e₁.symm w ∉ e₂.symm '' closedBall c₂ (2 * r₂) := by
    intro w hw hmem
    obtain ⟨v, hv, hveq⟩ := hmem
    have h1 := (hav2 v hv).2
    rw [hveq] at h1
    exact h1 ⟨w, hw, rfl⟩
  have hpole1 : ∀ n, ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball c₁ (2 * r₁)) ∧
      (∀ w ∈ ball c₁ (2 * r₁) \ {c₁},
        h w = Gs n (e₁.symm w) + Real.log ‖w - c₁‖) ∧
      ∀ w ∈ ball c₁ (2 * r₁), |h w| ≤ C₀ + (|Real.log r₁| + |Real.log (2 * r₁)|) :=
          by
    intro n
    obtain ⟨h, hharm, hval, hbd⟩ := bipolarGreen_aux2 D₀ hr₁ hr₂ htgt1 hav1
      (fun w hw => (hav2 w hw).1) hdisj12' (t n) (ht0 n) (ht1 n)
      (fun x h1 h2 => hGB n x h1 h2)
    exact ⟨h, hharm, fun w hw => hval w hw, hbd⟩
  have hpole2 : ∀ n, ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball c₂ (2 * r₂)) ∧
      (∀ w ∈ ball c₂ (2 * r₂) \ {c₂},
        h w = -Gs n (e₂.symm w) + Real.log ‖w - c₂‖) ∧
      ∀ w ∈ ball c₂ (2 * r₂), |h w| ≤ C₀ + (|Real.log r₂| + |Real.log (2 * r₂)|) :=
          by
    intro n
    obtain ⟨h, hharm, hval, hbd⟩ := bipolarGreen_aux2 D₀ hr₂ hr₁ htgt2
      (fun w hw => ⟨(hav2 w hw).1,
        fun hcon => (hav2 w hw).2 (hcon ▸ hp₁Car1)⟩)
      (fun w hw => (hav1 w hw).1) (fun w hw => (hav2 w hw).2) (t n) (ht0 n) (ht1 n)
      (fun x h1 h2 => by
        have h3 := hGB n x h2 h1
        have h4 := abs_sub_comm (pieceGreen (Wp n) p₁ x) (pieceGreen (Wp n) p₂ x)
        simp only [hGs] at h3
        rw [← h4]
        exact h3)
    refine ⟨h, hharm, fun w hw => ?_, hbd⟩
    have h5 := hval w hw
    simp only [hGs]
    linarith only [h5]
  choose h1s hh1harm hh1val hh1bd using hpole1
  choose h2s hh2harm hh2val hh2bd using hpole2
  have hGsharmAt : ∀ n (z : M), z ∈ Wp n → z ≠ p₁ → z ≠ p₂ → MHarmonicAt (Gs n) z
      := by
    intro n z hzP hz1 hz2
    exact mharmSub _ _ z
      (pgharm (Wp n) p₁ (hp₁W n) (hConnW n) (hNcW n) (hGF1 n) z hzP hz1)
      (pgharm (Wp n) p₂ (hp₂W n) (hConnW n) (hNcW n) (hGF2 n) z hzP hz2)
  /- ## The fixed outer circle for the center estimate. -/
  set ρs : ℝ := 3 * r₀ / 4 with hρs
  have hρs0 : 0 < ρs := by rw [hρs]; linarith only [hr₀]
  have hρsr₀ : ρs < r₀ := by rw [hρs]; linarith only [hr₀]
  have hsph0tgt : sphere c₀ ρs ⊆ e₀.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall hρsr₀.le)).trans hcb₀tgt
  set Γ₀ : Set M := e₀.symm '' sphere c₀ ρs with hΓ₀
  have hΓ₀cp : IsCompact Γ₀ := (isCompact_sphere _ _).image_of_continuousOn
    (e₀.continuousOn_symm.mono hsph0tgt)
  have hδlt : ∀ n, t n * r₀ < ρs := by
    intro n
    have h1 := htq n
    have h2 : t n * r₀ ≤ 1 / 4 * r₀ := mul_le_mul_of_nonneg_right h1 hr₀.le
    rw [hρs]
    linarith only [h2, hr₀]
  have hden : ∀ n, 0 < Real.log ρs - Real.log (t n * r₀) := by
    intro n
    have h1 : Real.log (t n * r₀) < Real.log ρs := by
      apply Real.log_lt_log
      · exact mul_pos (ht0 n) hr₀
      · exact hδlt n
    linarith only [h1]
  /- ## The absolute logarithm on a sandwiched radius. -/
  have hlogsand : ∀ (a b d : ℝ), 0 < a → a < d → d < b →
      |Real.log d| ≤ |Real.log a| + |Real.log b| := by
    intro a b d ha had hdb
    have h1 : Real.log a ≤ Real.log d := Real.log_le_log ha had.le
    have h2 : Real.log d ≤ Real.log b := Real.log_le_log (lt_trans ha had) hdb.le
    rw [abs_le]
    constructor
    · linarith only [h1, neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
    · linarith only [h2, le_abs_self (Real.log b), abs_nonneg (Real.log a)]
  /- ## The fixed extraction domain. -/
  set Ωqq : Set M := (Dq.closedCarrier ∪ half1.closedCarrier ∪ half2.closedCarrier)ᶜ
    with hΩqq
  have hΩqqopen : IsOpen Ωqq := ((Dq.isCompact_closedCarrier.union
    half1.isCompact_closedCarrier).union
      half2.isCompact_closedCarrier).isClosed.isOpen_compl
  have hΩqqW : ∀ x ∈ Ωqq, ∀ n, x ∈ Wp n := by
    intro x hx n hmem
    exact hx (Or.inl (Or.inl (hcarNq n hmem)))
  have hΩqqp₁ : ∀ x ∈ Ωqq, x ≠ p₁ := by
    intro x hx hcon
    exact hx (Or.inl (Or.inr (hcon ▸ hp₁half)))
  have hΩqqp₂ : ∀ x ∈ Ωqq, x ≠ p₂ := by
    intro x hx hcon
    exact hx (Or.inr (hcon ▸ hp₂half))
  have hGsharmΩqq : ∀ n, MHarmonicOn (Gs n) Ωqq := fun n x hx =>
    hGsharmAt n x (hΩqqW x hx n) (hΩqqp₁ x hx) (hΩqqp₂ x hx)
  /- ## The dipole differences read through the pole companions inside the balls. -/
  have hGsB₁ : ∀ n, ∀ x ∈ B₁, x ≠ p₁ →
      Gs n x = h1s n (e₁ x) - Real.log ‖e₁ x - c₁‖ := by
    intro n x hx hxne
    obtain ⟨hxsrc, hxpre⟩ := hx
    rw [Set.mem_preimage] at hxpre
    have hw : e₁ x ∈ ball c₁ (2 * r₁) :=
      ball_subset_ball (by linarith only [hr₁]) hxpre
    have hwne : e₁ x ≠ c₁ := by
      intro hcon
      have h2 := congrArg (⇑e₁.symm) hcon
      rw [e₁.left_inv hxsrc] at h2
      rw [hc₁, e₁.left_inv hp₁src] at h2
      exact hxne h2
    have hval := hh1val n (e₁ x) ⟨hw, by simpa using hwne⟩
    rw [e₁.left_inv hxsrc] at hval
    linarith only [hval]
  have hGsB₂ : ∀ n, ∀ x ∈ B₂, x ≠ p₂ →
      Gs n x = Real.log ‖e₂ x - c₂‖ - h2s n (e₂ x) := by
    intro n x hx hxne
    obtain ⟨hxsrc, hxpre⟩ := hx
    rw [Set.mem_preimage] at hxpre
    have hw : e₂ x ∈ ball c₂ (2 * r₂) :=
      ball_subset_ball (by linarith only [hr₂]) hxpre
    have hwne : e₂ x ≠ c₂ := by
      intro hcon
      have h2 := congrArg (⇑e₂.symm) hcon
      rw [e₂.left_inv hxsrc] at h2
      rw [hc₂, e₂.left_inv hp₂src] at h2
      exact hxne h2
    have hval := hh2val n (e₂ x) ⟨hw, by simpa using hwne⟩
    rw [e₂.left_inv hxsrc] at hval
    linarith only [hval]
  /- ## The uniform bound on the extraction domain. -/
  set Cq : ℝ := C₀ + (C₀ + (|Real.log r₁| + |Real.log (2 * r₁)|) +
      (|Real.log (r₁ / 2)| + |Real.log r₁|)) +
      (C₀ + (|Real.log r₂| + |Real.log (2 * r₂)|) +
      (|Real.log (r₂ / 2)| + |Real.log r₂|)) with hCq
  have hΩqqbd : ∀ n, ∀ x ∈ Ωqq, |Gs n x| ≤ Cq := by
    intro n x hx
    have hpad1 : (0 : ℝ) ≤ C₀ + (|Real.log r₁| + |Real.log (2 * r₁)|) +
        (|Real.log (r₁ / 2)| + |Real.log r₁|) :=
      add_nonneg (add_nonneg hC₀0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hpad2 : (0 : ℝ) ≤ C₀ + (|Real.log r₂| + |Real.log (2 * r₂)|) +
        (|Real.log (r₂ / 2)| + |Real.log r₂|) :=
      add_nonneg (add_nonneg hC₀0 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    by_cases hx1 : x ∈ B₁
    · have hxne : x ≠ p₁ := hΩqqp₁ x hx
      have hxnothalf : x ∉ half1.closedCarrier := fun hmem => hx (Or.inl (Or.inr hmem))
      have hcbsub1 : closedBall c₁ (r₁ / 2) ⊆ closedBall c₁ (2 * r₁) :=
        closedBall_subset_closedBall (by linarith only [hr₁])
      have hd : r₁ / 2 < dist (e₁ x) c₁ := by
        by_contra hcon
        push Not at hcon
        apply hxnothalf
        rw [hhalf1car]
        exact (hmemCB e₁ c₁ (r₁ / 2) (hcbsub1.trans htgt1) x).2 ⟨hx1.1, hcon⟩
      have hd2 : dist (e₁ x) c₁ < r₁ := by
        have h1 := hx1.2
        rw [Set.mem_preimage, mem_ball] at h1
        exact h1
      have hhalfpos : 0 < r₁ / 2 := half_pos hr₁
      have hlog : |Real.log ‖e₁ x - c₁‖| ≤ |Real.log (r₁ / 2)| + |Real.log r₁| := by
        have hn : ‖e₁ x - c₁‖ = dist (e₁ x) c₁ := (dist_eq_norm _ _).symm
        rw [hn]
        exact hlogsand (r₁ / 2) r₁ (dist (e₁ x) c₁) hhalfpos hd hd2
      have hxball : e₁ x ∈ ball c₁ (2 * r₁) := by
        rw [mem_ball]
        linarith only [hd2, hr₁]
      have hb := hh1bd n (e₁ x) hxball
      rw [hGsB₁ n x hx1 hxne]
      calc |h1s n (e₁ x) - Real.log ‖e₁ x - c₁‖|
          ≤ |h1s n (e₁ x)| + |Real.log ‖e₁ x - c₁‖| := abs_sub _ _
        _ ≤ Cq := by
            rw [hCq]
            linarith only [hb, hlog, hC₀0, hpad2]
    · by_cases hx2 : x ∈ B₂
      · have hxne : x ≠ p₂ := hΩqqp₂ x hx
        have hxnothalf : x ∉ half2.closedCarrier := fun hmem => hx (Or.inr hmem)
        have hcbsub2 : closedBall c₂ (r₂ / 2) ⊆ closedBall c₂ (2 * r₂) :=
          closedBall_subset_closedBall (by linarith only [hr₂])
        have hd : r₂ / 2 < dist (e₂ x) c₂ := by
          by_contra hcon
          push Not at hcon
          apply hxnothalf
          rw [hhalf2car]
          exact (hmemCB e₂ c₂ (r₂ / 2) (hcbsub2.trans htgt2) x).2 ⟨hx2.1, hcon⟩
        have hd2 : dist (e₂ x) c₂ < r₂ := by
          have h1 := hx2.2
          rw [Set.mem_preimage, mem_ball] at h1
          exact h1
        have hhalfpos : 0 < r₂ / 2 := half_pos hr₂
        have hlog : |Real.log ‖e₂ x - c₂‖| ≤ |Real.log (r₂ / 2)| + |Real.log r₂| := by
          have hn : ‖e₂ x - c₂‖ = dist (e₂ x) c₂ := (dist_eq_norm _ _).symm
          rw [hn]
          exact hlogsand (r₂ / 2) r₂ (dist (e₂ x) c₂) hhalfpos hd hd2
        have hxball : e₂ x ∈ ball c₂ (2 * r₂) := by
          rw [mem_ball]
          linarith only [hd2, hr₂]
        have hb := hh2bd n (e₂ x) hxball
        rw [hGsB₂ n x hx2 hxne]
        calc |Real.log ‖e₂ x - c₂‖ - h2s n (e₂ x)|
            ≤ |Real.log ‖e₂ x - c₂‖| + |h2s n (e₂ x)| := abs_sub _ _
          _ ≤ Cq := by
              rw [hCq]
              linarith only [hb, hlog, hC₀0, hpad1]
      · have h1 := hGB n x hx1 hx2
        rw [hCq]
        linarith only [h1, hpad1, hpad2]
  /- ## The normal-families extraction on the fixed domain. -/
  obtain ⟨φ, hφmono, Gout, hGoutharm, hGoutunif⟩ :=
    exists_mharmonicOn_limit_of_locally_bounded hΩqqopen hGsharmΩqq
      (fun K hK hKsub => ⟨Cq, fun n x hx => hΩqqbd n x (hKsub hx)⟩)
  /- ## Uniform Cauchy control on compact subsets of the extraction domain. -/
  have hcompCau : ∀ (T : Set M), IsCompact T → T ⊆ Ωqq → ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ z ∈ T, |Gs (φ m) z - Gs (φ n) z| ≤ ε := by
    intro T hT hTsub ε hε
    have h1 := hGoutunif T hT hTsub
    rw [Metric.tendstoUniformlyOn_iff] at h1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h1 (ε / 2) (half_pos hε))
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have hm1 := hN m hm z hz
    have hn1 := hN n hn z hz
    rw [Real.dist_eq] at hm1 hn1
    have hm2 : |Gs (φ m) z - Gout z| ≤ ε / 2 := by
      rw [abs_sub_comm]
      exact hm1.le
    calc |Gs (φ m) z - Gs (φ n) z|
        ≤ |Gs (φ m) z - Gout z| + |Gout z - Gs (φ n) z| := abs_sub_le _ _ _
      _ ≤ ε := by linarith only [hm2, hn1]
  /- ## The sphere Cauchy inputs for the two poles. -/
  have hsph1tgt' : sphere c₁ (3 * r₁ / 2) ⊆ e₁.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hsph2tgt' : sphere c₂ (3 * r₂ / 2) ⊆ e₂.target := (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  have hcau1 : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ sphere c₁ (3 *
      r₁ / 2),
      |h1s (φ m) ζ - h1s (φ n) ζ| ≤ ε := by
    intro ε hε
    have hΓcp : IsCompact (e₁.symm '' sphere c₁ (3 * r₁ / 2)) :=
      (isCompact_sphere _ _).image_of_continuousOn
        (e₁.continuousOn_symm.mono hsph1tgt')
    have hΓsub : e₁.symm '' sphere c₁ (3 * r₁ / 2) ⊆ Ωqq := by
      rintro z ⟨w, hw, rfl⟩
      have hzcar : e₁.symm w ∈ Car1 := ⟨w, sphere_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith only [hr₁])) hw, rfl⟩
      rintro ((hmem | hmem) | hmem)
      · exact (hCar1av _ hzcar).1 (hDqsub hmem)
      · rw [hhalf1car] at hmem
        obtain ⟨hsrc2, hd2⟩ := (hmemCB e₁ c₁ (r₁ / 2)
          ((closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1) _).1
          hmem
        have hd3 : dist (e₁ (e₁.symm w)) c₁ = 3 * r₁ / 2 := by
          rw [e₁.right_inv (hsph1tgt' hw)]
          exact mem_sphere.1 hw
        rw [hd3] at hd2
        linarith only [hd2, hr₁]
      · exact (hCar2av _ (hhalf2Car hmem)).2 hzcar
    obtain ⟨N, hN⟩ := hcompCau _ hΓcp hΓsub ε hε
    refine ⟨N, fun m hm n hn ζ hζ => ?_⟩
    have hz : e₁.symm ζ ∈ e₁.symm '' sphere c₁ (3 * r₁ / 2) := ⟨ζ, hζ, rfl⟩
    have hζball : ζ ∈ ball c₁ (2 * r₁) \ {c₁} := by
      have hd : dist ζ c₁ = 3 * r₁ / 2 := mem_sphere.1 hζ
      constructor
      · rw [mem_ball, hd]
        linarith only [hr₁]
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        rw [hcon, dist_self] at hd
        linarith only [hd, hr₁]
    have hvm := hh1val (φ m) ζ hζball
    have hvn := hh1val (φ n) ζ hζball
    have heq : h1s (φ m) ζ - h1s (φ n) ζ =
        Gs (φ m) (e₁.symm ζ) - Gs (φ n) (e₁.symm ζ) := by
      rw [hvm, hvn]
      ring
    rw [heq]
    exact hN m hm n hn _ hz
  have hcau2 : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ sphere c₂ (3 *
      r₂ / 2),
      |h2s (φ m) ζ - h2s (φ n) ζ| ≤ ε := by
    intro ε hε
    have hΓcp : IsCompact (e₂.symm '' sphere c₂ (3 * r₂ / 2)) :=
      (isCompact_sphere _ _).image_of_continuousOn
        (e₂.continuousOn_symm.mono hsph2tgt')
    have hΓsub : e₂.symm '' sphere c₂ (3 * r₂ / 2) ⊆ Ωqq := by
      rintro z ⟨w, hw, rfl⟩
      have hzcar : e₂.symm w ∈ Car2 := ⟨w, sphere_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith only [hr₂])) hw, rfl⟩
      rintro ((hmem | hmem) | hmem)
      · exact (hCar2av _ hzcar).1 (hDqsub hmem)
      · exact (hCar2av _ hzcar).2 (hhalf1Car hmem)
      · rw [hhalf2car] at hmem
        obtain ⟨hsrc2, hd2⟩ := (hmemCB e₂ c₂ (r₂ / 2)
          ((closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2) _).1
          hmem
        have hd3 : dist (e₂ (e₂.symm w)) c₂ = 3 * r₂ / 2 := by
          rw [e₂.right_inv (hsph2tgt' hw)]
          exact mem_sphere.1 hw
        rw [hd3] at hd2
        linarith only [hd2, hr₂]
    obtain ⟨N, hN⟩ := hcompCau _ hΓcp hΓsub ε hε
    refine ⟨N, fun m hm n hn ζ hζ => ?_⟩
    have hz : e₂.symm ζ ∈ e₂.symm '' sphere c₂ (3 * r₂ / 2) := ⟨ζ, hζ, rfl⟩
    have hζball : ζ ∈ ball c₂ (2 * r₂) \ {c₂} := by
      have hd : dist ζ c₂ = 3 * r₂ / 2 := mem_sphere.1 hζ
      constructor
      · rw [mem_ball, hd]
        linarith only [hr₂]
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        rw [hcon, dist_self] at hd
        linarith only [hd, hr₂]
    have hvm := hh2val (φ m) ζ hζball
    have hvn := hh2val (φ n) ζ hζball
    have heq : h2s (φ m) ζ - h2s (φ n) ζ =
        -(Gs (φ m) (e₂.symm ζ) - Gs (φ n) (e₂.symm ζ)) := by
      rw [hvm, hvn]
      ring
    rw [heq, abs_neg]
    exact hN m hm n hn _ hz
  obtain ⟨H1, hH1harm, hH1tend⟩ := bipolarGreen_aux4 (fun n => h1s (φ n)) hr₁
    (fun n => hh1harm (φ n)) hcau1
  obtain ⟨H2, hH2harm, hH2tend⟩ := bipolarGreen_aux4 (fun n => h2s (φ n)) hr₂
    (fun n => hh2harm (φ n)) hcau2
  /- ## The outer circle sits inside the extraction domain. -/
  have hQtgt : closedBall c₀ (1 / 4 * r₀) ⊆ e₀.target :=
    (closedBall_subset_closedBall (by linarith only [hr₀])).trans hcb₀tgt
  have hΓ₀sub : Γ₀ ⊆ Ωqq := by
    rw [hΓ₀]
    rintro z ⟨w, hw, rfl⟩
    have hwt : w ∈ e₀.target := hsph0tgt hw
    have hd : dist (e₀ (e₀.symm w)) c₀ = ρs := by
      rw [e₀.right_inv hwt]
      exact mem_sphere.1 hw
    have hcar : e₀.symm w ∈ D₀.closedCarrier := by
      rw [hcar₀]
      exact ⟨w, sphere_subset_closedBall.trans
        (closedBall_subset_closedBall hρsr₀.le) hw, rfl⟩
    rintro ((hmem | hmem) | hmem)
    · rw [hDqcar] at hmem
      obtain ⟨hsrc2, hd2⟩ := (hmemCB e₀ c₀ (1 / 4 * r₀) hQtgt _).1 hmem
      rw [hd] at hd2
      linarith only [hd2, hr₀, hρs]
    · exact (hCar1av _ (hhalf1Car hmem)).1 hcar
    · exact (hCar2av _ (hhalf2Car hmem)).1 hcar
  /- ## The barrier constant decays along the shrinking pieces. -/
  have hbarrier : ∀ (ε Lx : ℝ), 0 < ε → 0 ≤ Lx → ∃ N : ℕ, ∀ k ≥ N,
      4 * C₀ / (Real.log ρs - Real.log (t k * r₀)) * Lx ≤ ε := by
    intro ε Lx hε hLx
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hgrow : ∀ k : ℕ, Real.log ρs - Real.log (t k * r₀)
        = Real.log ρs - Real.log r₀ + ((k : ℝ) + 2) * Real.log 2 := by
      intro k
      have h1 : Real.log (t k * r₀) = Real.log (t k) + Real.log r₀ :=
        Real.log_mul (ht0 k).ne' hr₀.ne'
      have h2 : Real.log (t k) = -(((k : ℝ) + 2) * Real.log 2) := by
        have h3 : t k = (1 / 2 : ℝ) ^ (k + 2) := rfl
        rw [h3, Real.log_pow, one_div, Real.log_inv]
        push_cast
        ring
      rw [h1, h2]
      ring
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((4 * C₀ * Lx / ε - (Real.log ρs - Real.log r₀)) / Real.log 2 - 2)
    refine ⟨N, fun k hk => ?_⟩
    have hden' := hden k
    rw [div_mul_eq_mul_div, div_le_iff₀ hden']
    have hkN : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
    have h5 : (4 * C₀ * Lx / ε - (Real.log ρs - Real.log r₀)) / Real.log 2
        < (k : ℝ) + 2 := by
      linarith only [hN, hkN]
    rw [div_lt_iff₀ hlog2] at h5
    have h6 : 4 * C₀ * Lx / ε < Real.log ρs - Real.log r₀ +
        ((k : ℝ) + 2) * Real.log 2 := by
      linarith only [h5]
    rw [div_lt_iff₀ hε] at h6
    rw [hgrow k]
    have h7 : ε * (Real.log ρs - Real.log r₀ + ((k : ℝ) + 2) * Real.log 2)
        = (Real.log ρs - Real.log r₀ + ((k : ℝ) + 2) * Real.log 2) * ε :=
      mul_comm _ _
    linarith only [h6, h7]
  /- ## The uniform Cauchy estimate through the log barrier. -/
  have hcauAt : ∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∀ x : M, x ∈ e₀.source → a ≤ dist (e₀ x) c₀ → dist (e₀ x) c₀ < ρs →
      |Gs (φ m) x - Gs (φ n) x| ≤ ε := by
    intro a ha ε hε
    rcases lt_or_ge a ρs with haρ | haρ
    · have hLm0 : 0 ≤ Real.log ρs - Real.log a := by
        have h1 : Real.log a ≤ Real.log ρs := Real.log_le_log ha haρ.le
        linarith only [h1]
      obtain ⟨N₁, hN₁⟩ := hcompCau Γ₀ hΓ₀cp hΓ₀sub (ε / 3) (by linarith only
          [hε])
      obtain ⟨N₂, hN₂⟩ := hbarrier (ε / 3) (Real.log ρs - Real.log a)
        (by linarith only [hε]) hLm0
      obtain ⟨N₃, hN₃⟩ := htlim (a / r₀) (div_pos ha hr₀)
      refine ⟨max N₁ (max N₂ N₃), fun m hm n hn x hxsrc hxa hxρ => ?_⟩
      have hmn : max N₁ (max N₂ N₃) ≤ min m n := le_min hm hn
      have hAk : min m n ≤ φ (min m n) := hφmono.le_apply
      have hN₂A : N₂ ≤ φ (min m n) :=
        le_trans (le_trans (le_trans (le_max_left N₂ N₃) (le_max_right N₁ _)) hmn) hAk
      have hN₃A : N₃ ≤ φ (min m n) :=
        le_trans (le_trans (le_trans (le_max_right N₂ N₃) (le_max_right N₁ _)) hmn) hAk
      have hδsm : t (φ (min m n)) * r₀ < dist (e₀ x) c₀ := by
        have h1 : t (φ (min m n)) ≤ t N₃ := htanti N₃ _ hN₃A
        have h3 : t (φ (min m n)) * r₀ ≤ t N₃ * r₀ :=
          mul_le_mul_of_nonneg_right h1 hr₀.le
        have h4 : t N₃ * r₀ < a / r₀ * r₀ := mul_lt_mul_of_pos_right hN₃ hr₀
        have h5 : a / r₀ * r₀ = a := div_mul_cancel₀ _ hr₀.ne'
        linarith only [h3, h4, h5, hxa]
      have hsub1 : (DN (φ m)).closedCarrier ⊆ (DN (φ (min m n))).closedCarrier :=
        hcarmono _ _ (hφmono.monotone (min_le_left m n))
      have hsub2 : (DN (φ n)).closedCarrier ⊆ (DN (φ (min m n))).closedCarrier :=
        hcarmono _ _ (hφmono.monotone (min_le_right m n))
      have hN₁m : N₁ ≤ m := le_trans (le_max_left _ _) hm
      have hN₁n : N₁ ≤ n := le_trans (le_max_left _ _) hn
      have hsph1 : ∀ z ∈ Γ₀, Gs (φ m) z - Gs (φ n) z ≤ ε / 3 := by
        intro z hz
        have h1 := (abs_le.1 (hN₁ m hN₁m n hN₁n z hz)).2
        linarith only [h1]
      have hsph2 : ∀ z ∈ Γ₀, Gs (φ n) z - Gs (φ m) z ≤ ε / 3 := by
        intro z hz
        have h1 := (abs_le.1 (hN₁ m hN₁m n hN₁n z hz)).1
        linarith only [h1]
      have hbar := hN₂ (φ (min m n)) hN₂A
      have hQ0 : 0 ≤ 4 * C₀ / (Real.log ρs - Real.log (t (φ (min m n)) * r₀)) :=
        div_nonneg (by linarith only [hC₀1]) (hden (φ (min m n))).le
      have hLζ : Real.log ρs - Real.log (dist (e₀ x) c₀) ≤
          Real.log ρs - Real.log a := by
        have h1 : Real.log a ≤ Real.log (dist (e₀ x) c₀) := Real.log_le_log ha hxa
        linarith only [h1]
      have hmono := mul_le_mul_of_nonneg_left hLζ hQ0
      have he1 : Gs (φ m) x - Gs (φ n) x ≤ ε / 3 +
          4 * C₀ / (Real.log ρs - Real.log (t (φ (min m n)) * r₀)) *
          (Real.log ρs - Real.log (dist (e₀ x) c₀)) :=
        bipolarGreen_aux3 D₀ hr₁ hr₂ hC₀1 htgt1 htgt2 hav1 hav2
          (ht0 (φ (min m n))) (ht1 (φ (min m n))) (htq (φ (min m n)))
          (ht0 (φ m)) (ht1 (φ m)) (ht0 (φ n)) (ht1 (φ n)) hsub1 hsub2
          (ε := ε / 3) (by linarith only [hε])
          (fun y hy1 hy2 => hGB (φ m) y hy1 hy2)
          (fun y hy1 hy2 => hGB (φ n) y hy1 hy2) hsph1 x hxsrc hδsm hxρ
      have he2 : Gs (φ n) x - Gs (φ m) x ≤ ε / 3 +
          4 * C₀ / (Real.log ρs - Real.log (t (φ (min m n)) * r₀)) *
          (Real.log ρs - Real.log (dist (e₀ x) c₀)) :=
        bipolarGreen_aux3 D₀ hr₁ hr₂ hC₀1 htgt1 htgt2 hav1 hav2
          (ht0 (φ (min m n))) (ht1 (φ (min m n))) (htq (φ (min m n)))
          (ht0 (φ n)) (ht1 (φ n)) (ht0 (φ m)) (ht1 (φ m)) hsub2 hsub1
          (ε := ε / 3) (by linarith only [hε])
          (fun y hy1 hy2 => hGB (φ n) y hy1 hy2)
          (fun y hy1 hy2 => hGB (φ m) y hy1 hy2) hsph2 x hxsrc hδsm hxρ
      rw [abs_le]
      constructor
      · linarith only [he2, hbar, hmono, hε]
      · linarith only [he1, hbar, hmono, hε]
    · refine ⟨0, fun m _ n _ x _ hxa hxρ => ?_⟩
      exact absurd (lt_of_lt_of_le hxρ (le_trans haρ hxa)) (lt_irrefl _)
  /- ## The pointwise center limit. -/
  have hcen : ∀ x : M, x ∈ e₀.source → 0 < dist (e₀ x) c₀ → dist (e₀ x) c₀ < ρs
      →
      ∃ l, Tendsto (fun n => Gs (φ n) x) atTop (𝓝 l) := by
    intro x hxsrc hx0 hxρ
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauAt (dist (e₀ x) c₀) hx0 (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hN m hm n hn x hxsrc le_rfl hxρ
    linarith only [h1, hε]
  /- ## The limit function. -/
  set ℓs : M → ℝ := fun x => limUnder atTop (fun n => Gs (φ n) x) with hℓs
  have hhalftgt1 : closedBall c₁ (r₁ / 2) ⊆ e₁.target :=
    (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1
  have hhalftgt2 : closedBall c₂ (r₂ / 2) ⊆ e₂.target :=
    (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2
  have hρslt : 1 / 4 * r₀ < ρs := by linarith only [hr₀, hρs]
  have hℓtend : ∀ x : M, x ≠ p₁ → x ≠ p₂ → x ≠ D₀.center →
      Tendsto (fun n => Gs (φ n) x) atTop (𝓝 (ℓs x)) := by
    intro x hx1 hx2 hx0
    by_cases hΩ : x ∈ Ωqq
    · have h2 := (hGoutunif {x} isCompact_singleton
        (Set.singleton_subset_iff.2 hΩ)).tendsto_at rfl
      have h3 : ℓs x = Gout x := h2.limUnder_eq
      rw [h3]
      exact h2
    · have hx3 : x ∈ Dq.closedCarrier ∪ half1.closedCarrier ∪ half2.closedCarrier := by
        by_contra hcon
        exact hΩ hcon
      rcases hx3 with (hmem | hmem) | hmem
      · rw [hDqcar] at hmem
        obtain ⟨hsrc, hd⟩ := (hmemCB e₀ c₀ (1 / 4 * r₀) hQtgt x).1 hmem
        have hd0 : 0 < dist (e₀ x) c₀ := by
          rw [dist_pos]
          intro hcon
          apply hx0
          have h4 : e₀.symm (e₀ x) = e₀.symm c₀ := by rw [hcon]
          rw [e₀.left_inv hsrc, hc₀, e₀.left_inv hcen₀src] at h4
          exact h4
        obtain ⟨l, hl⟩ := hcen x hsrc hd0 (lt_of_le_of_lt hd hρslt)
        have h3 : ℓs x = l := hl.limUnder_eq
        rw [h3]
        exact hl
      · have hxB : x ∈ B₁ := by
          rw [hhalf1car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₁ c₁ (r₁ / 2) hhalftgt1 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₁]⟩
        have hw : e₁ x ∈ ball c₁ (3 * r₁ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₁]
        have h4 : Tendsto (fun n => h1s (φ n) (e₁ x) - Real.log ‖e₁ x - c₁‖) atTop
            (𝓝 (H1 (e₁ x) - Real.log ‖e₁ x - c₁‖)) :=
          (hH1tend (e₁ x) hw).sub tendsto_const_nhds
        have h5 : Tendsto (fun n => Gs (φ n) x) atTop
            (𝓝 (H1 (e₁ x) - Real.log ‖e₁ x - c₁‖)) :=
          h4.congr fun n => (hGsB₁ (φ n) x hxB hx1).symm
        have h6 : ℓs x = H1 (e₁ x) - Real.log ‖e₁ x - c₁‖ := h5.limUnder_eq
        rw [h6]
        exact h5
      · have hxB : x ∈ B₂ := by
          rw [hhalf2car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₂ c₂ (r₂ / 2) hhalftgt2 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₂]⟩
        have hw : e₂ x ∈ ball c₂ (3 * r₂ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₂]
        have h4 : Tendsto (fun n => Real.log ‖e₂ x - c₂‖ - h2s (φ n) (e₂ x)) atTop
            (𝓝 (Real.log ‖e₂ x - c₂‖ - H2 (e₂ x))) :=
          tendsto_const_nhds.sub (hH2tend (e₂ x) hw)
        have h5 : Tendsto (fun n => Gs (φ n) x) atTop
            (𝓝 (Real.log ‖e₂ x - c₂‖ - H2 (e₂ x))) := by
          refine h4.congr fun n => ?_
          have h7 := hh2val (φ n) (e₂ x) ?_
          · have h8 := hGsB₂ (φ n) x hxB hx2
            linarith only [h8]
          · have h1 := hxB.2
            rw [Set.mem_preimage, mem_ball] at h1
            refine ⟨by rw [mem_ball]; linarith only [h1, hr₂], ?_⟩
            intro hcon
            rw [Set.mem_singleton_iff] at hcon
            apply hx2
            have h9 : e₂.symm (e₂ x) = e₂.symm c₂ := by rw [hcon]
            rw [e₂.left_inv hxB.1, hc₂, e₂.left_inv hp₂src] at h9
            exact h9
        have h6 : ℓs x = Real.log ‖e₂ x - c₂‖ - H2 (e₂ x) := h5.limUnder_eq
        rw [h6]
        exact h5
  /- ## The plane limit near the center: harmonicity and boundedness. -/
  have hcenharm : ∀ w₀ ∈ ball c₀ ρs \ {c₀}, HarmonicAt (fun w => ℓs (e₀.symm w)) w₀
      := by
    intro w₀ hw₀
    obtain ⟨hw₀b, hw₀ne⟩ := hw₀
    have hw₀ne' : w₀ ≠ c₀ := by simpa using hw₀ne
    have hd0 : 0 < dist w₀ c₀ := dist_pos.2 hw₀ne'
    have hdρ : dist w₀ c₀ < ρs := mem_ball.1 hw₀b
    set ρw : ℝ := min (dist w₀ c₀ / 2) ((ρs - dist w₀ c₀) / 2) with hρw
    have hρw0 : 0 < ρw :=
      lt_min (by linarith only [hd0]) (by linarith only [hdρ])
    have hball : ∀ ζ ∈ closedBall w₀ ρw, ζ ∈ e₀.target ∧
        dist w₀ c₀ / 2 ≤ dist ζ c₀ ∧ dist ζ c₀ < ρs := by
      intro ζ hζ
      have h1 : dist ζ w₀ ≤ ρw := mem_closedBall.1 hζ
      have h2 : ρw ≤ dist w₀ c₀ / 2 := min_le_left _ _
      have h3 : ρw ≤ (ρs - dist w₀ c₀) / 2 := min_le_right _ _
      have h4 : dist ζ c₀ ≤ dist ζ w₀ + dist w₀ c₀ := dist_triangle _ _ _
      have h5 : dist w₀ c₀ ≤ dist w₀ ζ + dist ζ c₀ := dist_triangle _ _ _
      rw [dist_comm w₀ ζ] at h5
      have h6 : dist ζ c₀ < ρs := by linarith only [h1, h3, h4, hdρ]
      have h7 : dist w₀ c₀ / 2 ≤ dist ζ c₀ := by linarith only [h1, h2, h5]
      exact ⟨hcb₀tgt (mem_closedBall.2 (by linarith only [h6, hρsr₀])), h7, h6⟩
    have hsymm : ∀ ζ ∈ closedBall w₀ ρw, e₀.symm ζ ∈ e₀.source ∧
        dist (e₀ (e₀.symm ζ)) c₀ = dist ζ c₀ := by
      intro ζ hζ
      have h1 := (hball ζ hζ).1
      exact ⟨e₀.map_target h1, by rw [e₀.right_inv h1]⟩
    have hcarζ : ∀ ζ ∈ closedBall w₀ ρw, e₀.symm ζ ∈ D₀.closedCarrier := by
      intro ζ hζ
      rw [hcar₀]
      exact ⟨ζ, mem_closedBall.2 (by linarith only [(hball ζ hζ).2.2, hρsr₀]), rfl⟩
    have hunifC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ ζ ∈ closedBall
        w₀ ρw,
        |Gs (φ m) (e₀.symm ζ) - Gs (φ n) (e₀.symm ζ)| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hcauAt (dist w₀ c₀ / 2) (by linarith only [hd0]) ε hε
      refine ⟨N, fun m hm n hn ζ hζ => ?_⟩
      obtain ⟨hs1, hs2⟩ := hsymm ζ hζ
      obtain ⟨hb1, hb2, hb3⟩ := hball ζ hζ
      exact hN m hm n hn (e₀.symm ζ) hs1 (by rw [hs2]; exact hb2)
        (by rw [hs2]; exact hb3)
    have hptw : ∀ ζ ∈ closedBall w₀ ρw,
        Tendsto (fun n => Gs (φ n) (e₀.symm ζ)) atTop (𝓝 (ℓs (e₀.symm ζ))) := by
      intro ζ hζ
      obtain ⟨hs1, hs2⟩ := hsymm ζ hζ
      obtain ⟨hb1, hb2, hb3⟩ := hball ζ hζ
      have h1 : 0 < dist (e₀ (e₀.symm ζ)) c₀ := by
        rw [hs2]
        linarith only [hb2, hd0]
      have h2 : dist (e₀ (e₀.symm ζ)) c₀ < ρs := by
        rw [hs2]
        exact hb3
      obtain ⟨l, hl⟩ := hcen (e₀.symm ζ) hs1 h1 h2
      have h3 : ℓs (e₀.symm ζ) = l := hl.limUnder_eq
      rw [h3]
      exact hl
    obtain ⟨n₀, hn₀t⟩ := htlim (dist w₀ c₀ / 2 / r₀)
      (div_pos (by linarith only [hd0]) hr₀)
    have hshift_harm : ∀ j : ℕ,
        HarmonicOnNhd (fun w => Gs (φ (j + n₀)) (e₀.symm w))
          (ball w₀ (2 * (ρw / 2))) := by
      intro j ζ hζ
      have hζcb : ζ ∈ closedBall w₀ ρw := by
        have h1 : (2 : ℝ) * (ρw / 2) = ρw := by ring
        rw [h1] at hζ
        exact ball_subset_closedBall hζ
      obtain ⟨hs1, hs2⟩ := hsymm ζ hζcb
      obtain ⟨hb1, hb2, hb3⟩ := hball ζ hζcb
      have h1 : t (φ (j + n₀)) ≤ t n₀ :=
        htanti n₀ _ (le_trans (Nat.le_add_left n₀ j) hφmono.le_apply)
      have h3 : t n₀ * r₀ < dist w₀ c₀ / 2 := by
        have h4 : t n₀ * r₀ < dist w₀ c₀ / 2 / r₀ * r₀ :=
          mul_lt_mul_of_pos_right hn₀t hr₀
        have h5 : dist w₀ c₀ / 2 / r₀ * r₀ = dist w₀ c₀ / 2 := div_mul_cancel₀ _
            hr₀.ne'
        linarith only [h4, h5]
      have h6 : t (φ (j + n₀)) * r₀ ≤ t n₀ * r₀ :=
        mul_le_mul_of_nonneg_right h1 hr₀.le
      have hmemW : e₀.symm ζ ∈ Wp (φ (j + n₀)) := by
        intro hmem
        have h7 := ((hcarmem (φ (j + n₀)) (e₀.symm ζ)).1 hmem).2
        rw [hs2] at h7
        linarith only [h3, h6, h7, hb2]
      have hcar := hcarζ ζ hζcb
      have hnp1 : e₀.symm ζ ≠ p₁ := fun hcon =>
        (hCar1av p₁ hp₁Car1).1 (hcon ▸ hcar)
      have hnp2 : e₀.symm ζ ≠ p₂ := fun hcon =>
        (hCar2av p₂ hp₂Car2).1 (hcon ▸ hcar)
      refine htransfer D₀.center ((Wp (φ (j + n₀)) : Set M) ∩ ({p₁}ᶜ ∩ {p₂}ᶜ))
        (Gs (φ (j + n₀))) ?_ ζ ⟨hb1, ?_⟩
      · intro z hz
        exact hGsharmAt _ z hz.1 (Set.mem_compl_singleton_iff.1 hz.2.1)
          (Set.mem_compl_singleton_iff.1 hz.2.2)
      · rw [Set.mem_preimage]
        exact ⟨hmemW, Set.mem_compl_singleton_iff.2 hnp1,
          Set.mem_compl_singleton_iff.2 hnp2⟩
    have hcauw : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ∀ ζ ∈ sphere w₀ (3 * (ρw / 2) / 2),
        |Gs (φ (m + n₀)) (e₀.symm ζ) - Gs (φ (n + n₀)) (e₀.symm ζ)| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hunifC ε hε
      refine ⟨N, fun m hm n hn ζ hζ => ?_⟩
      have hζcb : ζ ∈ closedBall w₀ ρw := by
        have h1 : dist ζ w₀ = 3 * (ρw / 2) / 2 := mem_sphere.1 hζ
        rw [mem_closedBall, h1]
        linarith only [hρw0]
      exact hN (m + n₀) (le_trans hm (Nat.le_add_right m n₀)) (n + n₀)
        (le_trans hn (Nat.le_add_right n n₀)) ζ hζcb
    obtain ⟨Hw, hHwharm, hHwtend⟩ := bipolarGreen_aux4
      (fun j w => Gs (φ (j + n₀)) (e₀.symm w)) (half_pos hρw0) hshift_harm hcauw
    have hq0 : (0 : ℝ) < 3 * (ρw / 2) / 2 := by linarith only [hρw0]
    have hev : (fun w => ℓs (e₀.symm w)) =ᶠ[𝓝 w₀] Hw := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hq0)] with v hv
      have hvcb : v ∈ closedBall w₀ ρw := by
        have h1 : dist v w₀ < 3 * (ρw / 2) / 2 := mem_ball.1 hv
        rw [mem_closedBall]
        linarith only [h1, hρw0]
      have h1 := hptw v hvcb
      have h2 : Tendsto (fun j => Gs (φ (j + n₀)) (e₀.symm v)) atTop
          (𝓝 (ℓs (e₀.symm v))) := h1.comp (tendsto_add_atTop_nat n₀)
      exact tendsto_nhds_unique h2 (hHwtend v hv)
    exact (harmonicAt_congr_nhds hev).mpr (hHwharm w₀ (mem_ball_self hq0))
  have hcenbd : ∀ ζ ∈ ball c₀ ρs \ {c₀}, |ℓs (e₀.symm ζ)| ≤ C₀ := by
    intro ζ hζ
    obtain ⟨hζb, hζne⟩ := hζ
    have hζne' : ζ ≠ c₀ := by simpa using hζne
    have hζρ : dist ζ c₀ < ρs := mem_ball.1 hζb
    have hζt : ζ ∈ e₀.target :=
      hcb₀tgt (mem_closedBall.2 (by linarith only [hζρ, hρsr₀]))
    have hd1 : 0 < dist ζ c₀ := dist_pos.2 hζne'
    have hsrc := e₀.map_target hζt
    have hs2 : dist (e₀ (e₀.symm ζ)) c₀ = dist ζ c₀ := by rw [e₀.right_inv hζt]
    obtain ⟨l, hl⟩ := hcen (e₀.symm ζ) hsrc (by rw [hs2]; exact hd1)
      (by rw [hs2]; exact hζρ)
    have heq : ℓs (e₀.symm ζ) = l := hl.limUnder_eq
    have hcar : e₀.symm ζ ∈ D₀.closedCarrier := by
      rw [hcar₀]
      exact ⟨ζ, mem_closedBall.2 (by linarith only [hζρ, hρsr₀]), rfl⟩
    have hB1 : e₀.symm ζ ∉ B₁ := fun hmem => (hCar1av _ (hB₁Car hmem)).1 hcar
    have hB2 : e₀.symm ζ ∉ B₂ := fun hmem => (hCar2av _ (hB₂Car hmem)).1 hcar
    rw [heq]
    apply le_of_tendsto hl.abs
    exact Filter.Eventually.of_forall fun n => hGB (φ n) _ hB1 hB2
  obtain ⟨Hc, hHcharm, hHceq⟩ := exists_harmonicOnNhd_of_bounded_punctured hρs0
    (fun w hw => hcenharm w hw) ⟨C₀, hcenbd⟩
  /- ## Assembly of the bipolar Green's function. -/
  set Gfin : M → ℝ := fun x => if x = D₀.center then Hc c₀ else ℓs x with hGfin
  have hballtgt1 : ball c₁ (3 * r₁ / 2) ⊆ e₁.target :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₁]))).trans htgt1
  have hballtgt2 : ball c₂ (3 * r₂ / 2) ⊆ e₂.target :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith only [hr₂]))).trans htgt2
  -- the limit is the pole companion inside the enlarged pole balls
  have hval1 : ∀ w ∈ ball c₁ (3 * r₁ / 2) \ {c₁},
      e₁.symm w ≠ D₀.center ∧ ℓs (e₁.symm w) = H1 w - Real.log ‖w - c₁‖ := by
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwne' : w ≠ c₁ := by simpa using hwne
    have hwt : w ∈ e₁.target := hballtgt1 hwb
    have hcarw : e₁.symm w ∈ Car1 :=
      ⟨w, mem_closedBall.2 (by linarith only [mem_ball.1 hwb, hr₁]), rfl⟩
    have hnp1 : e₁.symm w ≠ p₁ := by
      intro hcon
      have h1 : e₁ (e₁.symm w) = w := e₁.right_inv hwt
      rw [hcon] at h1
      have h2 : c₁ = w := by rw [hc₁, h1]
      exact hwne' h2.symm
    have hnp2 : e₁.symm w ≠ p₂ := (hCar1av _ hcarw).2
    have hnc : e₁.symm w ≠ D₀.center := by
      intro hcon
      exact (hCar1av _ hcarw).1 (hcon ▸ hcen₀car)
    have h3 := hℓtend (e₁.symm w) hnp1 hnp2 hnc
    have hwball2 : w ∈ ball c₁ (2 * r₁) :=
      ball_subset_ball (by linarith only [hr₁]) hwb
    have h4 : ∀ n, Gs (φ n) (e₁.symm w) = h1s (φ n) w - Real.log ‖w - c₁‖ := by
      intro n
      have h5 := hh1val (φ n) w ⟨hwball2, by simpa using hwne'⟩
      linarith only [h5]
    have h6 : Tendsto (fun n => h1s (φ n) w - Real.log ‖w - c₁‖) atTop
        (𝓝 (H1 w - Real.log ‖w - c₁‖)) := (hH1tend w hwb).sub tendsto_const_nhds
    have h7 : Tendsto (fun n => Gs (φ n) (e₁.symm w)) atTop
        (𝓝 (H1 w - Real.log ‖w - c₁‖)) := h6.congr fun n => (h4 n).symm
    exact ⟨hnc, tendsto_nhds_unique h3 h7⟩
  have hval2 : ∀ w ∈ ball c₂ (3 * r₂ / 2) \ {c₂},
      e₂.symm w ≠ D₀.center ∧ ℓs (e₂.symm w) = Real.log ‖w - c₂‖ - H2 w := by
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have hwne' : w ≠ c₂ := by simpa using hwne
    have hwt : w ∈ e₂.target := hballtgt2 hwb
    have hcarw : e₂.symm w ∈ Car2 :=
      ⟨w, mem_closedBall.2 (by linarith only [mem_ball.1 hwb, hr₂]), rfl⟩
    have hnp2 : e₂.symm w ≠ p₂ := by
      intro hcon
      have h1 : e₂ (e₂.symm w) = w := e₂.right_inv hwt
      rw [hcon] at h1
      have h2 : c₂ = w := by rw [hc₂, h1]
      exact hwne' h2.symm
    have hnp1 : e₂.symm w ≠ p₁ := fun hcon => (hCar2av _ hcarw).2 (hcon ▸ hp₁Car1)
    have hnc : e₂.symm w ≠ D₀.center := by
      intro hcon
      exact (hCar2av _ hcarw).1 (hcon ▸ hcen₀car)
    have h3 := hℓtend (e₂.symm w) hnp1 hnp2 hnc
    have hwball2 : w ∈ ball c₂ (2 * r₂) :=
      ball_subset_ball (by linarith only [hr₂]) hwb
    have h4 : ∀ n, Gs (φ n) (e₂.symm w) = Real.log ‖w - c₂‖ - h2s (φ n) w := by
      intro n
      have h5 := hh2val (φ n) w ⟨hwball2, by simpa using hwne'⟩
      linarith only [h5]
    have h6 : Tendsto (fun n => Real.log ‖w - c₂‖ - h2s (φ n) w) atTop
        (𝓝 (Real.log ‖w - c₂‖ - H2 w)) := tendsto_const_nhds.sub (hH2tend w hwb)
    have h7 : Tendsto (fun n => Gs (φ n) (e₂.symm w)) atTop
        (𝓝 (Real.log ‖w - c₂‖ - H2 w)) := h6.congr fun n => (h4 n).symm
    exact ⟨hnc, tendsto_nhds_unique h3 h7⟩
  refine ⟨Gfin, ?_, ⟨3 * r₁ / 2, by linarith only [hr₁], hballtgt1, H1, hH1harm, ?_⟩,
    ⟨3 * r₂ / 2, by linarith only [hr₂], hballtgt2, fun w => -H2 w,
      harmNeg H2 _ hH2harm, ?_⟩, ⟨C₀, B₁, hB₁open.mem_nhds hp₁B₁, B₂,
      hB₂open.mem_nhds hp₂B₂, ?_, ?_, ?_⟩⟩
  · -- harmonicity on the doubly punctured surface
    intro x hx
    have hx1 : x ≠ p₁ := fun hcon => hx (by rw [hcon]; exact Set.mem_insert _ _)
    have hx2 : x ≠ p₂ := fun hcon => hx (by rw [hcon]; exact Set.mem_insert_of_mem _ rfl)
    by_cases hΩ : x ∈ Ωqq
    · have hev : ∀ᶠ z in 𝓝 x, Gout z = Gfin z := by
        filter_upwards [hΩqqopen.mem_nhds hΩ] with z hz
        have hz0 : z ≠ D₀.center := by
          intro hcon
          apply hz
          left; left
          rw [hcon, hDqcar]
          exact ⟨c₀, mem_closedBall_self (by linarith only [hr₀]),
            e₀.left_inv hcen₀src⟩
        have h3 := hℓtend z (hΩqqp₁ z hz) (hΩqqp₂ z hz) hz0
        have h4 := (hGoutunif {z} isCompact_singleton
          (Set.singleton_subset_iff.2 hz)).tendsto_at rfl
        have h5 : ℓs z = Gout z := tendsto_nhds_unique h3 h4
        simp only [hGfin]
        rw [if_neg hz0, h5]
      exact mharm_congr Gout Gfin x hev (hGoutharm x hΩ)
    · have hx3 : x ∈ Dq.closedCarrier ∪ half1.closedCarrier ∪ half2.closedCarrier := by
        by_contra hcon
        exact hΩ hcon
      rcases hx3 with (hmem | hmem) | hmem
      · -- across the center
        rw [hDqcar] at hmem
        obtain ⟨hxsrc, hxd⟩ := (hmemCB e₀ c₀ (1 / 4 * r₀) hQtgt x).1 hmem
        have hxball : e₀ x ∈ ball c₀ ρs := by
          rw [mem_ball]
          exact lt_of_le_of_lt hxd hρslt
        have hev : ∀ᶠ z in 𝓝 x, Hc (e₀ z) = Gfin z := by
          have hN₀open : IsOpen (e₀.source ∩ e₀ ⁻¹' ball c₀ ρs) :=
            e₀.isOpen_inter_preimage isOpen_ball
          have hxN₀ : x ∈ e₀.source ∩ e₀ ⁻¹' ball c₀ ρs :=
            ⟨hxsrc, by rw [Set.mem_preimage]; exact hxball⟩
          filter_upwards [hN₀open.mem_nhds hxN₀] with z hz
          obtain ⟨hzsrc, hzb⟩ := hz
          rw [Set.mem_preimage] at hzb
          by_cases hzc : z = D₀.center
          · simp only [hGfin]
            rw [if_pos hzc, hzc, ← hc₀]
          · have hzezc : e₀ z ≠ c₀ := by
              intro hcon
              apply hzc
              have h4 : e₀.symm (e₀ z) = e₀.symm c₀ := by rw [hcon]
              rw [e₀.left_inv hzsrc, hc₀, e₀.left_inv hcen₀src] at h4
              exact h4
            have h5 : e₀ z ∈ ball c₀ ρs \ {c₀} := ⟨hzb, by simpa using hzezc⟩
            have h6 : Hc (e₀ z) = ℓs (e₀.symm (e₀ z)) := hHceq h5
            rw [e₀.left_inv hzsrc] at h6
            simp only [hGfin]
            rw [if_neg hzc]
            exact h6
        have h7 : HarmonicAt Hc (e₀ x) := hHcharm (e₀ x) hxball
        exact mharm_congr _ _ x hev (pullback D₀.center Hc x hxsrc h7)
      · -- across the first half disk
        have hxB : x ∈ B₁ := by
          rw [hhalf1car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₁ c₁ (r₁ / 2) hhalftgt1 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₁]⟩
        have hw : e₁ x ∈ ball c₁ (3 * r₁ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₁]
        have hxcne : e₁ x ≠ c₁ := by
          intro hcon
          apply hx1
          have h4 : e₁.symm (e₁ x) = e₁.symm c₁ := by rw [hcon]
          rw [e₁.left_inv hxB.1, hc₁, e₁.left_inv hp₁src] at h4
          exact h4
        have hev : ∀ᶠ z in 𝓝 x, H1 (e₁ z) - Real.log ‖e₁ z - c₁‖ = Gfin z := by
          have hNopen : IsOpen ((e₁.source ∩ e₁ ⁻¹' ball c₁ (3 * r₁ / 2)) ∩
              {p₁}ᶜ) :=
            (e₁.isOpen_inter_preimage isOpen_ball).inter isOpen_compl_singleton
          have hxN : x ∈ (e₁.source ∩ e₁ ⁻¹' ball c₁ (3 * r₁ / 2)) ∩ {p₁}ᶜ :=
            ⟨⟨hxB.1, by rw [Set.mem_preimage]; exact hw⟩,
              Set.mem_compl_singleton_iff.2 hx1⟩
          filter_upwards [hNopen.mem_nhds hxN] with z hz
          obtain ⟨⟨hzsrc, hzb⟩, hznp⟩ := hz
          rw [Set.mem_preimage] at hzb
          have hzcne : e₁ z ≠ c₁ := by
            intro hcon
            apply Set.mem_compl_singleton_iff.1 hznp
            have h4 : e₁.symm (e₁ z) = e₁.symm c₁ := by rw [hcon]
            rw [e₁.left_inv hzsrc, hc₁, e₁.left_inv hp₁src] at h4
            exact h4
          have h5 := hval1 (e₁ z) ⟨hzb, by simpa using hzcne⟩
          rw [e₁.left_inv hzsrc] at h5
          simp only [hGfin]
          rw [if_neg h5.1]
          exact h5.2.symm
        have hharm1 : MHarmonicAt (fun z => H1 (e₁ z) -
            Real.log (dist (e₁ z) c₁)) x :=
          mharmSub _ _ x (pullback p₁ H1 x hxB.1 (hH1harm (e₁ x) hw))
            (logHarm p₁ c₁ x hxB.1 hxcne)
        have hharm2 : MHarmonicAt (fun z => H1 (e₁ z) - Real.log ‖e₁ z - c₁‖) x :=
          mharm_congr _ _ x
            (Filter.Eventually.of_forall fun z => by rw [dist_eq_norm]) hharm1
        exact mharm_congr _ _ x hev hharm2
      · -- across the second half disk
        have hxB : x ∈ B₂ := by
          rw [hhalf2car] at hmem
          obtain ⟨hsrc, hd⟩ := (hmemCB e₂ c₂ (r₂ / 2) hhalftgt2 x).1 hmem
          exact ⟨hsrc, by rw [Set.mem_preimage, mem_ball]; linarith only [hd, hr₂]⟩
        have hw : e₂ x ∈ ball c₂ (3 * r₂ / 2) := by
          have h1 := hxB.2
          rw [Set.mem_preimage, mem_ball] at h1
          rw [mem_ball]
          linarith only [h1, hr₂]
        have hxcne : e₂ x ≠ c₂ := by
          intro hcon
          apply hx2
          have h4 : e₂.symm (e₂ x) = e₂.symm c₂ := by rw [hcon]
          rw [e₂.left_inv hxB.1, hc₂, e₂.left_inv hp₂src] at h4
          exact h4
        have hev : ∀ᶠ z in 𝓝 x, Real.log ‖e₂ z - c₂‖ - H2 (e₂ z) = Gfin z := by
          have hNopen : IsOpen ((e₂.source ∩ e₂ ⁻¹' ball c₂ (3 * r₂ / 2)) ∩
              {p₂}ᶜ) :=
            (e₂.isOpen_inter_preimage isOpen_ball).inter isOpen_compl_singleton
          have hxN : x ∈ (e₂.source ∩ e₂ ⁻¹' ball c₂ (3 * r₂ / 2)) ∩ {p₂}ᶜ :=
            ⟨⟨hxB.1, by rw [Set.mem_preimage]; exact hw⟩,
              Set.mem_compl_singleton_iff.2 hx2⟩
          filter_upwards [hNopen.mem_nhds hxN] with z hz
          obtain ⟨⟨hzsrc, hzb⟩, hznp⟩ := hz
          rw [Set.mem_preimage] at hzb
          have hzcne : e₂ z ≠ c₂ := by
            intro hcon
            apply Set.mem_compl_singleton_iff.1 hznp
            have h4 : e₂.symm (e₂ z) = e₂.symm c₂ := by rw [hcon]
            rw [e₂.left_inv hzsrc, hc₂, e₂.left_inv hp₂src] at h4
            exact h4
          have h5 := hval2 (e₂ z) ⟨hzb, by simpa using hzcne⟩
          rw [e₂.left_inv hzsrc] at h5
          simp only [hGfin]
          rw [if_neg h5.1]
          exact h5.2.symm
        have hharm1 : MHarmonicAt (fun z => Real.log (dist (e₂ z) c₂) -
            H2 (e₂ z)) x :=
          mharmSub _ _ x (logHarm p₂ c₂ x hxB.1 hxcne)
            (pullback p₂ H2 x hxB.1 (hH2harm (e₂ x) hw))
        have hharm2 : MHarmonicAt (fun z => Real.log ‖e₂ z - c₂‖ - H2 (e₂ z)) x :=
          mharm_congr _ _ x
            (Filter.Eventually.of_forall fun z => by rw [dist_eq_norm]) hharm1
        exact mharm_congr _ _ x hev hharm2
  · -- the pole identity at `p₁`
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have h1 := hval1 w ⟨hwb, hwne⟩
    simp only [hGfin]
    rw [if_neg h1.1, h1.2]
    ring
  · -- the pole identity at `p₂`
    intro w hw
    obtain ⟨hwb, hwne⟩ := hw
    have h1 := hval2 w ⟨hwb, hwne⟩
    simp only [hGfin]
    rw [if_neg h1.1, h1.2]
    ring
  · -- compact closure of the first pole ball
    have htgtr₁ : closedBall c₁ r₁ ⊆ e₁.target :=
      (closedBall_subset_closedBall (by linarith only [hr₁])).trans htgt1
    have hcp : IsCompact (e₁.symm '' closedBall c₁ r₁) :=
      (isCompact_closedBall c₁ r₁).image_of_continuousOn
        (e₁.continuousOn_symm.mono htgtr₁)
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rw [← hB₁img]
    exact Set.image_mono ball_subset_closedBall
  · -- compact closure of the second pole ball
    have htgtr₂ : closedBall c₂ r₂ ⊆ e₂.target :=
      (closedBall_subset_closedBall (by linarith only [hr₂])).trans htgt2
    have hcp : IsCompact (e₂.symm '' closedBall c₂ r₂) :=
      (isCompact_closedBall c₂ r₂).image_of_continuousOn
        (e₂.continuousOn_symm.mono htgtr₂)
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rw [← hB₂img]
    exact Set.image_mono ball_subset_closedBall
  · -- the global bound off the pole balls
    intro x hx
    have hx1 : x ∉ B₁ := fun h => hx (Or.inl h)
    have hx2 : x ∉ B₂ := fun h => hx (Or.inr h)
    by_cases hxc : x = D₀.center
    · simp only [hGfin]
      rw [if_pos hxc]
      have h4 : Tendsto Hc (𝓝[≠] c₀) (𝓝 (Hc c₀)) :=
        ((hHcharm c₀ (mem_ball_self hρs0)).1.continuousAt).continuousWithinAt
      apply le_of_tendsto h4.abs
      have h5 : ball c₀ ρs ∈ 𝓝 c₀ := isOpen_ball.mem_nhds (mem_ball_self hρs0)
      filter_upwards [nhdsWithin_le_nhds h5, self_mem_nhdsWithin] with w hw1 hw2
      have hw3 : w ∈ ball c₀ ρs \ {c₀} := ⟨hw1, hw2⟩
      have h6 : Hc w = ℓs (e₀.symm w) := hHceq hw3
      rw [h6]
      exact hcenbd w hw3
    · simp only [hGfin]
      rw [if_neg hxc]
      have hxp1 : x ≠ p₁ := fun hcon => hx1 (hcon ▸ hp₁B₁)
      have hxp2 : x ≠ p₂ := fun hcon => hx2 (hcon ▸ hp₂B₂)
      apply le_of_tendsto (hℓtend x hxp1 hxp2 hxc).abs
      exact Filter.Eventually.of_forall fun n => hGB (φ n) x hx1 hx2

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
  classical
  -- ## §0 Plane bricks: punctured-ball connectivity and constant-ratio rigidity.
  have hpunc : ∀ (c : ℂ) (r : ℝ), 0 < r → IsPreconnected (ball c r \ {c}) := by
    intro c r hr
    have hcont : Continuous fun p : ℝ × ℝ =>
        c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).cexp))
    have himg : (fun p : ℝ × ℝ => c + (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
        (Set.Ioo 0 r ×ˢ (Set.univ : Set ℝ)) = ball c r \ {c} := by
      apply Set.Subset.antisymm
      · rintro w ⟨⟨t, θ⟩, ⟨⟨ht0, htr⟩, -⟩, hw⟩
        rw [← hw]
        change c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball c r \ {c}
        have hd : dist (c + (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) c = t := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
        refine ⟨?_, ?_⟩
        · rw [mem_ball, hd]; exact htr
        · intro h
          rw [Set.mem_singleton_iff] at h
          rw [h, dist_self] at hd
          exact ht0.ne hd
      · rintro w ⟨hwb, hwc⟩
        rw [Set.mem_singleton_iff] at hwc
        have ht0 : 0 < ‖w - c‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hwc)
        have htr : ‖w - c‖ < r := by rw [← dist_eq_norm]; exact mem_ball.1 hwb
        refine ⟨(‖w - c‖, (w - c).arg), ⟨⟨ht0, htr⟩, Set.mem_univ _⟩, ?_⟩
        change c + (‖w - c‖ : ℂ) * Complex.exp (((w - c).arg : ℂ) * Complex.I) = w
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    rw [← himg]
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn
  have hcore : ∀ (f g : ℂ → ℂ) (z₀ : ℂ) (ρ : ℝ), 0 < ρ →
      AnalyticOnNhd ℂ f (ball z₀ ρ) → AnalyticOnNhd ℂ g (ball z₀ ρ) →
      (∀ w ∈ ball z₀ ρ, ‖f w‖ = ‖g w‖) →
      (∀ w ∈ ball z₀ ρ, w ≠ z₀ → g w ≠ 0) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ Set.EqOn f (fun w => c * g w) (ball z₀ ρ) := by
    intro f g z₀ ρ hρ hf hg hnorm hgne
    set U : Set ℂ := ball z₀ ρ \ {z₀} with hU
    have hUopen : IsOpen U := isOpen_ball.sdiff isClosed_singleton
    have hUconn : IsPreconnected U := hpunc z₀ ρ hρ
    set z₁ : ℂ := z₀ + ((ρ / 2 : ℝ) : ℂ) with hz₁
    have hz₁U : z₁ ∈ U := by
      constructor
      · rw [mem_ball, dist_eq_norm, hz₁, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
        linarith
      · intro h
        rw [Set.mem_singleton_iff, hz₁, add_eq_left] at h
        have h2 : (ρ / 2 : ℝ) = 0 := by exact_mod_cast h
        linarith
    have hgU : ∀ w ∈ U, g w ≠ 0 := fun w hw => hgne w hw.1 hw.2
    have hr : AnalyticOnNhd ℂ (f / g) U := fun w hw =>
      (hf w hw.1).div (hg w hw.1) (hgU w hw)
    have hrnorm : ∀ w ∈ U, ‖(f / g) w‖ = 1 := by
      intro w hw
      rw [Pi.div_apply, norm_div, hnorm w hw.1,
        div_self (norm_ne_zero_iff.mpr (hgU w hw))]
    rcases (hr z₁ hz₁U).eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · -- the ratio is constant on the punctured ball
      have heq : Set.EqOn (f / g) (fun _ => (f / g) z₁) U :=
        hr.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUconn hz₁U hconst
      refine ⟨(f / g) z₁, hrnorm z₁ hz₁U, ?_⟩
      have hEqU : ∀ w ∈ U, f w = (f / g) z₁ * g w := by
        intro w hw
        have h1 := heq hw
        rw [Pi.div_apply, div_eq_iff (hgU w hw)] at h1
        exact h1
      intro w hw
      by_cases hwz : w = z₀
      · have hz₀b : z₀ ∈ ball z₀ ρ := mem_ball_self hρ
        have hfc : Filter.Tendsto f (𝓝[U] z₀) (𝓝 (f z₀)) :=
          ((hf z₀ hz₀b).continuousAt).continuousWithinAt
        have hgc : Filter.Tendsto (fun v => (f / g) z₁ * g v) (𝓝[U] z₀)
            (𝓝 ((f / g) z₁ * g z₀)) :=
          (continuousAt_const.mul (hg z₀ hz₀b).continuousAt).continuousWithinAt
        haveI : (𝓝[U] z₀).NeBot := by
          have h2 : U = {z₀}ᶜ ∩ ball z₀ ρ := by rw [hU, Set.diff_eq, Set.inter_comm]
          rw [h2,
            nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz₀b))]
          exact Module.punctured_nhds_neBot ℝ ℂ z₀
        have h5 : f =ᶠ[𝓝[U] z₀] fun v => (f / g) z₁ * g v :=
          eventually_nhdsWithin_of_forall hEqU
        have hcenter := tendsto_nhds_unique (hfc.congr' h5) hgc
        rw [hwz]
        exact hcenter
      · exact hEqU w ⟨hw, hwz⟩
    · -- open image: impossible for a map into the unit circle
      exfalso
      have hUnh : U ∈ 𝓝 z₁ := hUopen.mem_nhds hz₁U
      have himg : (f / g) '' U ∈ 𝓝 ((f / g) z₁) := hopen (Filter.image_mem_map hUnh)
      obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp himg
      have hwS : ((1 + δ / 2 : ℝ) : ℂ) * (f / g) z₁ ∈ ball ((f / g) z₁) δ := by
        rw [mem_ball, dist_eq_norm]
        have h1 : ((1 + δ / 2 : ℝ) : ℂ) * (f / g) z₁ - (f / g) z₁ =
            ((δ / 2 : ℝ) : ℂ) * (f / g) z₁ := by
          push_cast
          ring
        rw [h1, norm_mul, Complex.norm_real, hrnorm z₁ hz₁U, mul_one,
          Real.norm_of_nonneg (by linarith)]
        linarith
      obtain ⟨u, huU, huw⟩ := hball hwS
      have h6 : ‖(f / g) u‖ = 1 := hrnorm u huU
      rw [huw, norm_mul, Complex.norm_real, hrnorm z₁ hz₁U, mul_one,
        Real.norm_of_nonneg (by linarith)] at h6
      linarith
  -- ## §0b Sphere toolkit: charts, values, inverses, and Möbius scalings.
  have hpolesopen : IsOpen ({p₁, p₂}ᶜ : Set M) := by
    rw [isOpen_compl_iff, Set.insert_eq]
    exact isClosed_singleton.union isClosed_singleton
  have hpolemem : ∀ y : M, y ∈ ({p₁, p₂}ᶜ : Set M) ↔ y ≠ p₁ ∧ y ≠ p₂ := by
    intro y
    rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hfinrec : ∀ z : ℂ̂, z ≠ OnePoint.infty → z = ((sphereChartFinite z : ℂ) : ℂ̂)
      := by
    intro z hz
    cases z with
    | infty => exact absurd rfl hz
    | coe w => rw [sphereChartFinite_coe]
  have hIapp_coe : ∀ w : ℂ, w ≠ 0 → sphereChartInfty ((w : ℂ̂)) = w⁻¹ := by
    intro w hw
    rw [sphereChartInfty_apply, inversionGL_smul_coe, if_neg hw, sphereChartFinite_coe]
  have hIapp_infty : sphereChartInfty (OnePoint.infty : ℂ̂) = 0 := by
    rw [sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe]
  have hITmem : ∀ w : ℂ, w ∈ sphereChartInfty.target := by
    intro w
    have hz : (inversionGL • ((w : ℂ̂))) ∈ sphereChartInfty.source := by
      rw [sphereChartInfty_source, inversionGL_smul_coe]
      by_cases hw : w = 0
      · rw [if_pos hw]
        exact OnePoint.infty_ne_coe 0
      · rw [if_neg hw]
        intro hcon
        exact hw (by simpa [inv_eq_zero] using OnePoint.coe_eq_coe.mp hcon)
    have h2 : sphereChartInfty (inversionGL • ((w : ℂ̂))) = w := by
      rw [sphereChartInfty_apply, inversionGL_smul_smul, sphereChartFinite_coe]
    have h3 := sphereChartInfty.map_source hz
    rwa [h2] at h3
  have hISmem : ∀ z : ℂ̂, z ≠ ((0 : ℂ) : ℂ̂) → z ∈ sphereChartInfty.source := by
    intro z hz
    rw [sphereChartInfty_source]
    exact hz
  have hFmem : ∀ z : ℂ̂, z ≠ OnePoint.infty → z ∈ sphereChartFinite.source := by
    intro z hz
    rw [sphereChartFinite_source]
    exact hz
  have hatlasF : sphereChartFinite ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.subset_maximalAtlas (Set.mem_insert _ _)
  have hatlasI : sphereChartInfty ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.subset_maximalAtlas (Set.mem_insert_of_mem _ rfl)
  have hcoeSm : ∀ w : ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun v : ℂ => ((v : ℂ) : ℂ̂))
      w := by
    intro w
    have h1 : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω sphereChartFinite.symm sphereChartFinite.target :=
      contMDiffOn_symm_of_mem_maximalAtlas hatlasF
    have h2 : sphereChartFinite.target ∈ 𝓝 w := by
      rw [show sphereChartFinite.target = Set.univ from rfl]
      exact Filter.univ_mem
    refine (h1.contMDiffAt h2).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun v => (sphereChartFinite_symm_apply v).symm
  have hIsymmSm : ∀ w : ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChartInfty.symm w := by
    intro w
    exact (contMDiffOn_symm_of_mem_maximalAtlas hatlasI).contMDiffAt
      (sphereChartInfty.open_target.mem_nhds (hITmem w))
  have hFSm : ∀ z : ℂ̂, z ≠ OnePoint.infty →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChartFinite z := by
    intro z hz
    exact (contMDiffOn_of_mem_maximalAtlas hatlasF).contMDiffAt
      (sphereChartFinite.open_source.mem_nhds (hFmem z hz))
  have hISm : ∀ z : ℂ̂, z ≠ ((0 : ℂ) : ℂ̂) →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω sphereChartInfty z := by
    intro z hz
    exact (contMDiffOn_of_mem_maximalAtlas hatlasI).contMDiffAt
      (sphereChartInfty.open_source.mem_nhds (hISmem z hz))
  have hmulCex : ∀ c : ℂ, c ≠ 0 → ∃ mc : ℂ̂ → ℂ̂, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      mc ∧
      (∀ w : ℂ, mc ((w : ℂ̂)) = ((c * w : ℂ) : ℂ̂)) ∧
      mc OnePoint.infty = OnePoint.infty := by
    intro c hc
    have hdet : (!![c, 0; 0, (1 : ℂ)]).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      simpa using hc
    obtain ⟨e, he⟩ := exists_glSMul_diffeomorph
      (Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet)
    refine ⟨fun z => Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet • z,
      ?_, ?_, ?_⟩
    · rw [← he]
      exact e.contMDiff
    · intro w
      change Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet •
        ((w : ℂ̂)) = ((c * w : ℂ) : ℂ̂)
      rw [OnePoint.smul_some_eq_ite]
      norm_num
    · change Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, (1 : ℂ)] hdet •
        (OnePoint.infty : ℂ̂) = OnePoint.infty
      rw [OnePoint.smul_infty_eq_ite]
      norm_num
  choose! mulC hmulCsm hmulCco hmulCinf using hmulCex
  have hmulC1 : ∀ z : ℂ̂, mulC 1 z = z := by
    intro z
    cases z with
    | infty => exact hmulCinf 1 one_ne_zero
    | coe w => rw [hmulCco 1 one_ne_zero w, one_mul]
  -- ## §1 The pointwise element predicate and its stability.
  obtain ⟨Q, hQ⟩ : ∃ Q : (M → ℂ̂) → M → Prop, ∀ ψ x, Q ψ x ↔
      (ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ x ∧
        (x ≠ p₁ → x ≠ p₂ → ∃ w : ℂ, ψ x = ((w : ℂ) : ℂ̂) ∧
          ‖w‖ = Real.exp (-(G x))) ∧
        (x = p₁ → ψ x = ((0 : ℂ) : ℂ̂)) ∧ (x = p₂ → ψ x = OnePoint.infty)) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hfin : ∀ (ψ : M → ℂ̂) (y : M), Q ψ y → y ≠ p₂ → ψ y ≠ OnePoint.infty :=
      by
    intro ψ y hq hy2
    rw [hQ] at hq
    by_cases hy1 : y = p₁
    · rw [hq.2.2.1 hy1]
      exact OnePoint.coe_ne_infty 0
    · obtain ⟨w, hw1, -⟩ := hq.2.1 hy1 hy2
      rw [hw1]
      exact OnePoint.coe_ne_infty w
  have hne0 : ∀ (ψ : M → ℂ̂) (y : M), Q ψ y → y ≠ p₁ → ψ y ≠ ((0 : ℂ) : ℂ̂)
      := by
    intro ψ y hq hy1
    rw [hQ] at hq
    by_cases hy2 : y = p₂
    · rw [hq.2.2.2 hy2]
      exact OnePoint.infty_ne_coe 0
    · obtain ⟨w, hw1, hw2⟩ := hq.2.1 hy1 hy2
      rw [hw1]
      intro hcon
      have hw0 : w = 0 := OnePoint.coe_eq_coe.mp hcon
      rw [hw0, norm_zero] at hw2
      exact absurd hw2.symm (ne_of_gt (Real.exp_pos _))
  have hreadFin : ∀ (ψ : M → ℂ̂) (x₀ : M), ∀ z ∈ (chartAt ℂ x₀).target,
      ψ ((chartAt ℂ x₀).symm z) ≠ OnePoint.infty →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ ((chartAt ℂ x₀).symm z) →
      AnalyticAt ℂ (fun w => sphereChartFinite (ψ ((chartAt ℂ x₀).symm w))) z := by
    intro ψ x₀ z hz hnei hψ
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x₀).symm z :=
      contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x₀).open_target.mem_nhds hz)
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun w => sphereChartFinite (ψ ((chartAt ℂ x₀).symm w))) z :=
      (hFSm _ hnei).comp z (hψ.comp z hsymm)
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).analyticAt
  have hreadInf : ∀ (ψ : M → ℂ̂) (x₀ : M), ∀ z ∈ (chartAt ℂ x₀).target,
      ψ ((chartAt ℂ x₀).symm z) ≠ ((0 : ℂ) : ℂ̂) →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ ((chartAt ℂ x₀).symm z) →
      AnalyticAt ℂ (fun w => sphereChartInfty (ψ ((chartAt ℂ x₀).symm w))) z := by
    intro ψ x₀ z hz hnez hψ
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x₀).symm z :=
      contMDiffOn_chart_symm.contMDiffAt ((chartAt ℂ x₀).open_target.mem_nhds hz)
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun w => sphereChartInfty (ψ ((chartAt ℂ x₀).symm w))) z :=
      (hISm _ hnez).comp z (hψ.comp z hsymm)
    exact (contMDiffAt_iff_contDiffAt.mp hcomp).analyticAt
  have hQsmul : ∀ (c : ℂ), ‖c‖ = 1 → ∀ (ψ : M → ℂ̂) (y : M), Q ψ y →
      Q (fun z => mulC c (ψ z)) y := by
    intro c hc ψ y hq
    have hc0 : c ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hc
      exact one_ne_zero hc.symm
    rw [hQ] at hq ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hq
    refine ⟨((hmulCsm c hc0).contMDiffAt).comp y h1, ?_, ?_, ?_⟩
    · intro hy1 hy2
      obtain ⟨w, hw1, hw2⟩ := h2 hy1 hy2
      refine ⟨c * w, ?_, ?_⟩
      · rw [hw1]
        exact hmulCco c hc0 w
      · rw [norm_mul, hc, one_mul]
        exact hw2
    · intro hy
      rw [h3 hy, hmulCco c hc0 0, mul_zero]
    · intro hy
      rw [h4 hy, hmulCinf c hc0]
  have hEtrans : ∀ (ψ ψ' : M → ℂ̂) (x : M), (∀ᶠ y in 𝓝 x, Q ψ y) → ψ' =ᶠ[𝓝
      x] ψ →
      ∀ᶠ y in 𝓝 x, Q ψ' y := by
    intro ψ ψ' x hE heq
    obtain ⟨W, hWnh, hWeq⟩ := eventuallyEq_iff_exists_mem.mp heq
    obtain ⟨W', hW'sub, hW'open, hxW'⟩ := mem_nhds_iff.mp hWnh
    filter_upwards [hE, hW'open.mem_nhds hxW'] with y hy hyW'
    rw [hQ] at hy ⊢
    have heqy : ψ' =ᶠ[𝓝 y] ψ :=
      eventuallyEq_of_mem (hW'open.mem_nhds hyW') (fun z hz => hWeq (hW'sub hz))
    refine ⟨hy.1.congr_of_eventuallyEq heqy, fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩
    · obtain ⟨w, hw1, hw2⟩ := hy.2.1 h1 h2
      exact ⟨w, by rw [hWeq (hW'sub hyW')]; exact hw1, hw2⟩
    · rw [hWeq (hW'sub hyW')]
      exact hy.2.2.1 h
    · rw [hWeq (hW'sub hyW')]
      exact hy.2.2.2 h
  -- ## §2 Existence of local elements: generic, zero-pole, and infinity-pole types.
  have helt : ∀ x : M, ∃ ψ : M → ℂ̂, ∀ᶠ y in 𝓝 x, Q ψ y := by
    intro x
    by_cases hx1 : x = p₁
    · -- the zero element `(z - c₁) e^{-F z}` read through the chart at `p₁`
      subst hx1
      obtain ⟨r, hr0, hrsub, h, hharm, hhval⟩ := hpole₁
      set e := chartAt ℂ x with he
      set c₁ : ℂ := e x with hc₁
      have hxs : x ∈ e.source := mem_chart_source ℂ x
      obtain ⟨F, hFa, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
      refine ⟨fun y => (((e y - c₁) * Complex.exp (-F (e y)) : ℂ) : ℂ̂), ?_⟩
      have hVopen : IsOpen (e.source ∩ e ⁻¹' ball c₁ r ∩ {p₂}ᶜ) :=
        (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).inter
          isOpen_compl_singleton
      have hxV : x ∈ e.source ∩ e ⁻¹' ball c₁ r ∩ {p₂}ᶜ := by
        refine ⟨⟨hxs, ?_⟩, hne⟩
        rw [Set.mem_preimage, ← hc₁]
        exact mem_ball_self hr0
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      obtain ⟨⟨hys, hyb'⟩, hyp2⟩ := hy
      have hyb : e y ∈ ball c₁ r := hyb'
      have hyp2' : y ≠ p₂ := hyp2
      rw [hQ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have houter : AnalyticAt ℂ (fun w : ℂ => (w - c₁) * Complex.exp (-F w)) (e y) := by
          have h1 : AnalyticAt ℂ (fun w : ℂ => -F w) (e y) := (hFa _ hyb).neg
          have h2 : AnalyticAt ℂ (Complex.exp ∘ fun w : ℂ => -F w) (e y) := h1.cexp
          exact (analyticAt_id.sub analyticAt_const).mul h2
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
            (fun w : ℂ => (w - c₁) * Complex.exp (-F w)) (e y) :=
          contMDiffAt_iff_contDiffAt.mpr houter.contDiffAt
        have h4 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e y :=
          contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
        exact (hcoeSm _).comp y (h3.comp y h4)
      · intro hyp1 _
        have hyc : e y ≠ c₁ := by
          intro hcon
          exact hyp1 (e.injOn hys hxs (by rw [hcon, hc₁]))
        refine ⟨(e y - c₁) * Complex.exp (-F (e y)), rfl, ?_⟩
        have hval : h (e y) = G y + Real.log ‖e y - c₁‖ := by
          have h5 := hhval (e y) ⟨hyb, hyc⟩
          rw [e.left_inv hys] at h5
          exact h5
        have hpos : 0 < ‖e y - c₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyc)
        have hre0 : (F (e y)).re = h (e y) := hFre hyb
        rw [norm_mul, Complex.norm_exp, Complex.neg_re, hre0, hval, neg_add,
          Real.exp_add, Real.exp_neg (Real.log ‖e y - c₁‖), Real.exp_log hpos,
          mul_comm, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
      · intro hyp
        rw [hyp, ← hc₁, sub_self, zero_mul]
      · intro hyp
        exact absurd hyp hyp2'
    by_cases hx2 : x = p₂
    · -- the infinity element `1 / ((z - c₂) e^{f₂ z})` read through the chart at `p₂`
      subst hx2
      obtain ⟨r, hr0, hrsub, h, hharm, hhval⟩ := hpole₂
      set e := chartAt ℂ x with he
      set c₂ : ℂ := e x with hc₂
      have hxs : x ∈ e.source := mem_chart_source ℂ x
      obtain ⟨F, hFa, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
      refine ⟨fun y => sphereChartInfty.symm ((e y - c₂) * Complex.exp (F (e y))), ?_⟩
      have hVopen : IsOpen (e.source ∩ e ⁻¹' ball c₂ r ∩ {p₁}ᶜ) :=
        (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).inter
          isOpen_compl_singleton
      have hxV : x ∈ e.source ∩ e ⁻¹' ball c₂ r ∩ {p₁}ᶜ := by
        refine ⟨⟨hxs, ?_⟩, fun hcon => hne hcon.symm⟩
        rw [Set.mem_preimage, ← hc₂]
        exact mem_ball_self hr0
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      obtain ⟨⟨hys, hyb'⟩, hyp1⟩ := hy
      have hyb : e y ∈ ball c₂ r := hyb'
      have hyp1' : y ≠ p₁ := hyp1
      rw [hQ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have houter : AnalyticAt ℂ (fun w : ℂ => (w - c₂) * Complex.exp (F w)) (e y) := by
          have h2 : AnalyticAt ℂ (Complex.exp ∘ F) (e y) := (hFa _ hyb).cexp
          exact (analyticAt_id.sub analyticAt_const).mul h2
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
            (fun w : ℂ => (w - c₂) * Complex.exp (F w)) (e y) :=
          contMDiffAt_iff_contDiffAt.mpr houter.contDiffAt
        have h4 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e y :=
          contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
        exact (hIsymmSm _).comp y (h3.comp y h4)
      · intro _ hyp2
        have hyc : e y ≠ c₂ := by
          intro hcon
          exact hyp2 (e.injOn hys hxs (by rw [hcon, hc₂]))
        have hgne0 : (e y - c₂) * Complex.exp (F (e y)) ≠ 0 :=
          mul_ne_zero (sub_ne_zero.mpr hyc) (Complex.exp_ne_zero _)
        refine ⟨((e y - c₂) * Complex.exp (F (e y)))⁻¹, ?_, ?_⟩
        · change sphereChartInfty.symm ((e y - c₂) * Complex.exp (F (e y))) = _
          rw [sphereChartInfty_symm_apply, inversionGL_smul_coe, if_neg hgne0]
        · have hval : h (e y) = G y - Real.log ‖e y - c₂‖ := by
            have h5 := hhval (e y) ⟨hyb, hyc⟩
            rw [e.left_inv hys] at h5
            exact h5
          have hpos : 0 < ‖e y - c₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyc)
          have hre0 : (F (e y)).re = h (e y) := hFre hyb
          rw [norm_inv, norm_mul, Complex.norm_exp, hre0, hval, Real.exp_sub,
            Real.exp_log hpos, mul_comm, div_mul_cancel₀ _ (ne_of_gt hpos),
            ← Real.exp_neg]
      · intro hyp
        exact absurd hyp hyp1'
      · intro hyp
        rw [hyp, ← hc₂, sub_self, zero_mul, sphereChartInfty_symm_apply,
          inversionGL_smul_coe, if_pos rfl]
    · -- the generic element `e^{-F}` from a chart-ball harmonic conjugate
      set e := chartAt ℂ x with he
      have hxs : x ∈ e.source := mem_chart_source ℂ x
      have hSopen : IsOpen (e.target ∩ e.symm ⁻¹' ({p₁, p₂}ᶜ)) :=
        e.isOpen_inter_preimage_symm hpolesopen
      have hxS : e x ∈ e.target ∩ e.symm ⁻¹' ({p₁, p₂}ᶜ) := by
        refine ⟨e.map_source hxs, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxs, hpolemem]
        exact ⟨hx1, hx2⟩
      obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hSopen _ hxS
      have hharm : HarmonicOnNhd (G ∘ e.symm) (ball (e x) ρ) := by
        intro w hw
        have hwt : w ∈ e.target := (hρsub hw).1
        have hwp : e.symm w ∈ ({p₁, p₂}ᶜ : Set M) := (hρsub hw).2
        have h1 : MHarmonicAt G (e.symm w) := hG _ hwp
        have h2 := (mharmonicAt_iff_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x) (e.map_target hwt)).mp h1
        rwa [e.right_inv hwt] at h2
      obtain ⟨F, hFa, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
      refine ⟨fun y => ((Complex.exp (-F (e y)) : ℂ) : ℂ̂), ?_⟩
      have hVopen : IsOpen (e.source ∩ e ⁻¹' ball (e x) ρ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hxV : x ∈ e.source ∩ e ⁻¹' ball (e x) ρ :=
        ⟨hxs, by rw [Set.mem_preimage]; exact mem_ball_self hρ0⟩
      filter_upwards [hVopen.mem_nhds hxV] with y hy
      obtain ⟨hys, hyb'⟩ := hy
      have hyb : e y ∈ ball (e x) ρ := hyb'
      have hyp : y ≠ p₁ ∧ y ≠ p₂ := by
        have h1 := (hρsub hyb).2
        rw [Set.mem_preimage, e.left_inv hys, hpolemem] at h1
        exact h1
      rw [hQ]
      refine ⟨?_, fun _ _ => ?_, fun hcon => absurd hcon hyp.1,
        fun hcon => absurd hcon hyp.2⟩
      · have houter : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-F w)) (e y) :=
          ((hFa _ hyb).neg).cexp
        have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℂ => Complex.exp (-F w)) (e y) :=
          contMDiffAt_iff_contDiffAt.mpr houter.contDiffAt
        have h4 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e y :=
          contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hys)
        exact (hcoeSm _).comp y (h3.comp y h4)
      · refine ⟨Complex.exp (-F (e y)), rfl, ?_⟩
        have hre0 : (F (e y)).re = (G ∘ e.symm) (e y) := hFre hyb
        rw [Complex.norm_exp, Complex.neg_re, hre0]
        simp only [Function.comp_apply, e.left_inv hys]
  -- ## §3 Generic helpers: germ spreading, nearby non-pole points, path-continuity radii.
  have hOpen : ∀ (f g : M → ℂ̂) (x : M), f =ᶠ[𝓝 x] g →
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∀ z ∈ O, f =ᶠ[𝓝 z] g := by
    intro f g x heq
    obtain ⟨S, hS, hSeq⟩ := eventuallyEq_iff_exists_mem.mp heq
    obtain ⟨O, hOS, hO, hxO⟩ := mem_nhds_iff.mp hS
    exact ⟨O, hO, hxO, fun z hz => (hSeq.mono hOS).eventuallyEq_of_mem (hO.mem_nhds hz)⟩
  have hQopen : ∀ (ψ : M → ℂ̂) (x : M), (∀ᶠ y in 𝓝 x, Q ψ y) →
      ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W, Q ψ z ∧ ∀ᶠ y in 𝓝 z, Q ψ y :=
          by
    intro ψ x h
    obtain ⟨S, hSnh, hSQ⟩ := eventually_iff_exists_mem.mp h
    obtain ⟨W, hWS, hWo, hxW⟩ := mem_nhds_iff.mp hSnh
    refine ⟨W, hWo, hxW, fun z hz => ⟨hSQ z (hWS hz), ?_⟩⟩
    filter_upwards [hWo.mem_nhds hz] with y hy using hSQ y (hWS hy)
  have hnear : ∀ (x : M) (O : Set M), IsOpen O → x ∈ O →
      ∃ z ∈ O, z ≠ p₁ ∧ z ≠ p₂ := by
    intro x O hO hxO
    set e := chartAt ℂ x with he
    have hxs : x ∈ e.source := mem_chart_source ℂ x
    have hB : IsOpen (e.target ∩ e.symm ⁻¹' O) := e.isOpen_inter_preimage_symm hO
    have hxB : e x ∈ e.target ∩ e.symm ⁻¹' O :=
      ⟨e.map_source hxs, by rw [Set.mem_preimage, e.left_inv hxs]; exact hxO⟩
    obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hB _ hxB
    have hmem : ∀ t : ℝ, 0 ≤ t → t < 1 →
        e x + ((t * r : ℝ) : ℂ) ∈ e.target ∩ e.symm ⁻¹' O := by
      intro t ht0 ht1
      refine hrsub ?_
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      nlinarith
    have hOmem : ∀ t : ℝ, 0 ≤ t → t < 1 → e.symm (e x + ((t * r : ℝ) : ℂ)) ∈ O := by
      intro t ht0 ht1
      have h5 := (hmem t ht0 ht1).2
      rwa [Set.mem_preimage] at h5
    have hinj : ∀ t s : ℝ, 0 ≤ t → t < 1 → 0 ≤ s → s < 1 →
        e.symm (e x + ((t * r : ℝ) : ℂ)) = e.symm (e x + ((s * r : ℝ) : ℂ)) → t = s := by
      intro t s ht0 ht1 hs0 hs1 heq
      have hw1 : e x + ((t * r : ℝ) : ℂ) ∈ e.symm.source := by
        rw [e.symm_source]
        exact (hmem t ht0 ht1).1
      have hw2 : e x + ((s * r : ℝ) : ℂ) ∈ e.symm.source := by
        rw [e.symm_source]
        exact (hmem s hs0 hs1).1
      have h1 : e x + ((t * r : ℝ) : ℂ) = e x + ((s * r : ℝ) : ℂ) :=
        e.symm.injOn hw1 hw2 heq
      have h2 : ((t * r : ℝ) : ℂ) = ((s * r : ℝ) : ℂ) := add_left_cancel h1
      have h3 : t * r = s * r := by exact_mod_cast h2
      exact mul_right_cancel₀ (ne_of_gt hr0) h3
    have hd01 : e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠
        e.symm (e x + ((1/2 * r : ℝ) : ℂ)) := by
      intro hcon
      have h5 := hinj 0 (1/2) le_rfl one_pos (by norm_num) (by norm_num) hcon
      norm_num at h5
    have hd02 : e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠
        e.symm (e x + ((1/4 * r : ℝ) : ℂ)) := by
      intro hcon
      have h5 := hinj 0 (1/4) le_rfl one_pos (by norm_num) (by norm_num) hcon
      norm_num at h5
    have hd12 : e.symm (e x + ((1/2 * r : ℝ) : ℂ)) ≠
        e.symm (e x + ((1/4 * r : ℝ) : ℂ)) := by
      intro hcon
      have h5 := hinj (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hcon
      norm_num at h5
    by_cases h01 : e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠ p₁ ∧
        e.symm (e x + ((0 * r : ℝ) : ℂ)) ≠ p₂
    · exact ⟨_, hOmem 0 le_rfl one_pos, h01.1, h01.2⟩
    by_cases h11 : e.symm (e x + ((1/2 * r : ℝ) : ℂ)) ≠ p₁ ∧
        e.symm (e x + ((1/2 * r : ℝ) : ℂ)) ≠ p₂
    · exact ⟨_, hOmem (1/2) (by norm_num) (by norm_num), h11.1, h11.2⟩
    by_cases h21 : e.symm (e x + ((1/4 * r : ℝ) : ℂ)) ≠ p₁ ∧
        e.symm (e x + ((1/4 * r : ℝ) : ℂ)) ≠ p₂
    · exact ⟨_, hOmem (1/4) (by norm_num) (by norm_num), h21.1, h21.2⟩
    exfalso
    rw [not_and_or, not_not, not_not] at h01 h11 h21
    rcases h01 with h0 | h0 <;> rcases h11 with h1 | h1 <;> rcases h21 with h2 | h2
    all_goals first
      | exact hd01 (h0.trans h1.symm)
      | exact hd02 (h0.trans h2.symm)
      | exact hd12 (h1.trans h2.symm)
  have hγnb : ∀ (γ : ℝ → M) (S : Set ℝ) (b : ℝ), ContinuousOn γ S → b ∈ S →
      ∀ O : Set M, IsOpen O → γ b ∈ O → ∃ δ > 0, ∀ u ∈ S, |u - b| < δ → γ u ∈
          O := by
    intro γ S b hγ hbS O hO hbO
    have h1 : γ ⁻¹' O ∈ 𝓝[S] b :=
      (hγ b hbS).preimage_mem_nhdsWithin (hO.mem_nhds hbO)
    obtain ⟨δ, hδ0, hδ⟩ := mem_nhdsWithin_iff.mp h1
    refine ⟨δ, hδ0, fun u huS hub => ?_⟩
    exact hδ ⟨by rwa [mem_ball, Real.dist_eq], huS⟩
  -- ## §4 Phase rigidity: two elements at a point differ by a unimodular Möbius
  -- scaling near it, read through the finite chart away from `p₂` and through the
  -- infinity chart at `p₂`.
  have hrigid : ∀ (ψ ψ' : M → ℂ̂) (x : M), (∀ᶠ y in 𝓝 x, Q ψ y) →
      (∀ᶠ y in 𝓝 x, Q ψ' y) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ψ =ᶠ[𝓝 x] fun y => mulC c (ψ' y) := by
    intro ψ ψ' x hψ hψ'
    obtain ⟨W, hWnh, hWQ⟩ := eventually_iff_exists_mem.mp hψ
    obtain ⟨W1, hW1W, hW1o, hxW1⟩ := mem_nhds_iff.mp hWnh
    obtain ⟨W', hW'nh, hW'Q⟩ := eventually_iff_exists_mem.mp hψ'
    obtain ⟨W1', hW1'W, hW1'o, hxW1'⟩ := mem_nhds_iff.mp hW'nh
    set e := chartAt ℂ x with he
    have hxs : x ∈ e.source := mem_chart_source ℂ x
    by_cases hx2 : x = p₂
    · -- at the infinity pole: invert the readings
      have hT : IsOpen (e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ {p₁}ᶜ)) :=
        e.isOpen_inter_preimage_symm ((hW1o.inter hW1'o).inter isOpen_compl_singleton)
      have hxT : e x ∈ e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ {p₁}ᶜ) := by
        refine ⟨e.map_source hxs, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxs]
        exact ⟨⟨hxW1, hxW1'⟩, by rw [hx2]; exact fun hcon => hne hcon.symm⟩
      obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hT _ hxT
      have hmem : ∀ w ∈ ball (e x) ρ, w ∈ e.target ∧ e.symm w ∈ W1 ∧
          e.symm w ∈ W1' ∧ e.symm w ≠ p₁ := by
        intro w hw
        obtain ⟨h1, h2⟩ := hρsub hw
        rw [Set.mem_preimage] at h2
        exact ⟨h1, h2.1.1, h2.1.2, h2.2⟩
      have hQmem : ∀ w ∈ ball (e x) ρ, Q ψ (e.symm w) ∧ Q ψ' (e.symm w) := by
        intro w hw
        exact ⟨hWQ _ (hW1W (hmem w hw).2.1), hW'Q _ (hW1'W (hmem w hw).2.2.1)⟩
      have hcenter : ∀ w ∈ ball (e x) ρ, e.symm w = p₂ → w = e x := by
        intro w hw hwp
        have h9 : e.symm w = e.symm (e x) := by rw [hwp, ← hx2, e.left_inv hxs]
        have hw1 : w ∈ e.symm.source := by
          rw [e.symm_source]
          exact (hmem w hw).1
        have hw2 : e x ∈ e.symm.source := by
          rw [e.symm_source]
          exact e.map_source hxs
        exact e.symm.injOn hw1 hw2 h9
      have hfa : AnalyticOnNhd ℂ (fun z => sphereChartInfty (ψ (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).1
        have h6 : ψ (e.symm w) ≠ ((0 : ℂ) : ℂ̂) :=
          hne0 ψ (e.symm w) h5 (hmem w hw).2.2.2
        rw [hQ] at h5
        exact hreadInf ψ x w (hmem w hw).1 h6 h5.1
      have hga : AnalyticOnNhd ℂ (fun z => sphereChartInfty (ψ' (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).2
        have h6 : ψ' (e.symm w) ≠ ((0 : ℂ) : ℂ̂) :=
          hne0 ψ' (e.symm w) h5 (hmem w hw).2.2.2
        rw [hQ] at h5
        exact hreadInf ψ' x w (hmem w hw).1 h6 h5.1
      have hnorm : ∀ w ∈ ball (e x) ρ,
          ‖(fun z => sphereChartInfty (ψ (e.symm z))) w‖ =
          ‖(fun z => sphereChartInfty (ψ' (e.symm z))) w‖ := by
        intro w hw
        obtain ⟨h5, h5'⟩ := hQmem w hw
        rw [hQ] at h5 h5'
        change ‖sphereChartInfty (ψ (e.symm w))‖ = ‖sphereChartInfty (ψ' (e.symm w))‖
        by_cases h6 : e.symm w = p₂
        · rw [h5.2.2.2 h6, h5'.2.2.2 h6]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 (hmem w hw).2.2.2 h6
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 (hmem w hw).2.2.2 h6
          have hv0 : v ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv2
            exact absurd hv2.symm (ne_of_gt (Real.exp_pos _))
          have hv'0 : v' ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv'2
            exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
          rw [hv1, hv'1, hIapp_coe v hv0, hIapp_coe v' hv'0, norm_inv, norm_inv,
            hv2, hv'2]
      have hgne : ∀ w ∈ ball (e x) ρ, w ≠ e x →
          (fun z => sphereChartInfty (ψ' (e.symm z))) w ≠ 0 := by
        intro w hw hwx
        have h5' := (hQmem w hw).2
        rw [hQ] at h5'
        have h6 : e.symm w ≠ p₂ := fun hcon => hwx (hcenter w hw hcon)
        obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 (hmem w hw).2.2.2 h6
        have hv'0 : v' ≠ 0 := by
          intro hcon
          rw [hcon, norm_zero] at hv'2
          exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
        change sphereChartInfty (ψ' (e.symm w)) ≠ 0
        rw [hv'1, hIapp_coe v' hv'0]
        exact inv_ne_zero hv'0
      obtain ⟨cc, hcc1, hcceq⟩ := hcore _ _ (e x) ρ hρ0 hfa hga hnorm hgne
      have hcc0 : cc ≠ 0 := by
        intro hcon
        rw [hcon, norm_zero] at hcc1
        exact one_ne_zero hcc1.symm
      refine ⟨cc⁻¹, by rw [norm_inv, hcc1, inv_one], ?_⟩
      have hNo : IsOpen (e.source ∩ e ⁻¹' ball (e x) ρ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hxN : x ∈ e.source ∩ e ⁻¹' ball (e x) ρ :=
        ⟨hxs, by rw [Set.mem_preimage]; exact mem_ball_self hρ0⟩
      have hEq : Set.EqOn ψ (fun y => mulC cc⁻¹ (ψ' y))
          (e.source ∩ e ⁻¹' ball (e x) ρ) := by
        intro y hy
        have h1 : sphereChartInfty (ψ (e.symm (e y))) =
            cc * sphereChartInfty (ψ' (e.symm (e y))) := hcceq hy.2
        rw [e.left_inv hy.1] at h1
        have hyb : e y ∈ ball (e x) ρ := hy.2
        obtain ⟨h5, h5'⟩ := hQmem (e y) hyb
        rw [e.left_inv hy.1] at h5 h5'
        have h7 : y ≠ p₁ := by
          have h7' := (hmem (e y) hyb).2.2.2
          rwa [e.left_inv hy.1] at h7'
        rw [hQ] at h5 h5'
        by_cases h6 : y = p₂
        · change ψ y = mulC cc⁻¹ (ψ' y)
          rw [h5.2.2.2 h6, h5'.2.2.2 h6, hmulCinf cc⁻¹ (inv_ne_zero hcc0)]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 h7 h6
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h7 h6
          have hv0 : v ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv2
            exact absurd hv2.symm (ne_of_gt (Real.exp_pos _))
          have hv'0 : v' ≠ 0 := by
            intro hcon
            rw [hcon, norm_zero] at hv'2
            exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
          rw [hv1, hv'1, hIapp_coe v hv0, hIapp_coe v' hv'0] at h1
          have h8 : v = cc⁻¹ * v' := by
            have h9 : (v⁻¹)⁻¹ = (cc * v'⁻¹)⁻¹ := by rw [h1]
            rw [inv_inv, mul_inv, inv_inv] at h9
            exact h9
          change ψ y = mulC cc⁻¹ (ψ' y)
          rw [hv1, hv'1, hmulCco cc⁻¹ (inv_ne_zero hcc0) v', ← h8]
      exact hEq.eventuallyEq_of_mem (hNo.mem_nhds hxN)
    · -- away from the infinity pole: finite readings
      set X : Set M := (if x = p₁ then Set.univ else {p₁}ᶜ) ∩ {p₂}ᶜ with hX
      have hXo : IsOpen X := by
        rw [hX]
        refine IsOpen.inter ?_ isOpen_compl_singleton
        split_ifs
        exacts [isOpen_univ, isOpen_compl_singleton]
      have hxX : x ∈ X := by
        rw [hX]
        refine ⟨?_, hx2⟩
        split_ifs with hx1
        exacts [Set.mem_univ x, hx1]
      have hT : IsOpen (e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ X)) :=
        e.isOpen_inter_preimage_symm ((hW1o.inter hW1'o).inter hXo)
      have hxT : e x ∈ e.target ∩ e.symm ⁻¹' (W1 ∩ W1' ∩ X) := by
        refine ⟨e.map_source hxs, ?_⟩
        rw [Set.mem_preimage, e.left_inv hxs]
        exact ⟨⟨hxW1, hxW1'⟩, hxX⟩
      obtain ⟨ρ, hρ0, hρsub⟩ := Metric.isOpen_iff.mp hT _ hxT
      have hmem : ∀ w ∈ ball (e x) ρ, w ∈ e.target ∧ e.symm w ∈ W1 ∧
          e.symm w ∈ W1' ∧ e.symm w ≠ p₂ ∧ (x ≠ p₁ → e.symm w ≠ p₁) := by
        intro w hw
        obtain ⟨h1, h2⟩ := hρsub hw
        rw [Set.mem_preimage] at h2
        refine ⟨h1, h2.1.1, h2.1.2, ?_, ?_⟩
        · have h3 := h2.2
          rw [hX] at h3
          exact h3.2
        · intro hx1
          have h3 := h2.2
          rw [hX, if_neg hx1] at h3
          exact h3.1
      have hQmem : ∀ w ∈ ball (e x) ρ, Q ψ (e.symm w) ∧ Q ψ' (e.symm w) := by
        intro w hw
        exact ⟨hWQ _ (hW1W (hmem w hw).2.1), hW'Q _ (hW1'W (hmem w hw).2.2.1)⟩
      have hcenter : ∀ w ∈ ball (e x) ρ, e.symm w = p₁ → x = p₁ → w = e x := by
        intro w hw hwp hx1
        have h9 : e.symm w = e.symm (e x) := by rw [hwp, ← hx1, e.left_inv hxs]
        have hw1 : w ∈ e.symm.source := by
          rw [e.symm_source]
          exact (hmem w hw).1
        have hw2 : e x ∈ e.symm.source := by
          rw [e.symm_source]
          exact e.map_source hxs
        exact e.symm.injOn hw1 hw2 h9
      have hfa : AnalyticOnNhd ℂ (fun z => sphereChartFinite (ψ (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).1
        have h6 : ψ (e.symm w) ≠ OnePoint.infty :=
          hfin ψ (e.symm w) h5 (hmem w hw).2.2.2.1
        rw [hQ] at h5
        exact hreadFin ψ x w (hmem w hw).1 h6 h5.1
      have hga : AnalyticOnNhd ℂ (fun z => sphereChartFinite (ψ' (e.symm z)))
          (ball (e x) ρ) := by
        intro w hw
        have h5 := (hQmem w hw).2
        have h6 : ψ' (e.symm w) ≠ OnePoint.infty :=
          hfin ψ' (e.symm w) h5 (hmem w hw).2.2.2.1
        rw [hQ] at h5
        exact hreadFin ψ' x w (hmem w hw).1 h6 h5.1
      have hnorm : ∀ w ∈ ball (e x) ρ,
          ‖(fun z => sphereChartFinite (ψ (e.symm z))) w‖ =
          ‖(fun z => sphereChartFinite (ψ' (e.symm z))) w‖ := by
        intro w hw
        obtain ⟨h5, h5'⟩ := hQmem w hw
        rw [hQ] at h5 h5'
        change ‖sphereChartFinite (ψ (e.symm w))‖ = ‖sphereChartFinite (ψ' (e.symm w))‖
        by_cases h6 : e.symm w = p₁
        · rw [h5.2.2.1 h6, h5'.2.2.1 h6]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 h6 (hmem w hw).2.2.2.1
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h6 (hmem w hw).2.2.2.1
          rw [hv1, hv'1, sphereChartFinite_coe, sphereChartFinite_coe, hv2, hv'2]
      have hgne : ∀ w ∈ ball (e x) ρ, w ≠ e x →
          (fun z => sphereChartFinite (ψ' (e.symm z))) w ≠ 0 := by
        intro w hw hwx
        have h5' := (hQmem w hw).2
        rw [hQ] at h5'
        have h6 : e.symm w ≠ p₁ := by
          by_cases hx1 : x = p₁
          · exact fun hcon => hwx (hcenter w hw hcon hx1)
          · exact (hmem w hw).2.2.2.2 hx1
        obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h6 (hmem w hw).2.2.2.1
        have hv'0 : v' ≠ 0 := by
          intro hcon
          rw [hcon, norm_zero] at hv'2
          exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
        change sphereChartFinite (ψ' (e.symm w)) ≠ 0
        rw [hv'1, sphereChartFinite_coe]
        exact hv'0
      obtain ⟨c, hc1, hceq⟩ := hcore _ _ (e x) ρ hρ0 hfa hga hnorm hgne
      have hc0 : c ≠ 0 := by
        intro hcon
        rw [hcon, norm_zero] at hc1
        exact one_ne_zero hc1.symm
      refine ⟨c, hc1, ?_⟩
      have hNo : IsOpen (e.source ∩ e ⁻¹' ball (e x) ρ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hxN : x ∈ e.source ∩ e ⁻¹' ball (e x) ρ :=
        ⟨hxs, by rw [Set.mem_preimage]; exact mem_ball_self hρ0⟩
      have hEq : Set.EqOn ψ (fun y => mulC c (ψ' y))
          (e.source ∩ e ⁻¹' ball (e x) ρ) := by
        intro y hy
        have h1 : sphereChartFinite (ψ (e.symm (e y))) =
            c * sphereChartFinite (ψ' (e.symm (e y))) := hceq hy.2
        rw [e.left_inv hy.1] at h1
        have hyb : e y ∈ ball (e x) ρ := hy.2
        obtain ⟨h5, h5'⟩ := hQmem (e y) hyb
        rw [e.left_inv hy.1] at h5 h5'
        have h7 : y ≠ p₂ := by
          have h7' := (hmem (e y) hyb).2.2.2.1
          rwa [e.left_inv hy.1] at h7'
        rw [hQ] at h5 h5'
        by_cases h6 : y = p₁
        · change ψ y = mulC c (ψ' y)
          rw [h5.2.2.1 h6, h5'.2.2.1 h6, hmulCco c hc0 0, mul_zero]
        · obtain ⟨v, hv1, hv2⟩ := h5.2.1 h6 h7
          obtain ⟨v', hv'1, hv'2⟩ := h5'.2.1 h6 h7
          rw [hv1, hv'1, sphereChartFinite_coe, sphereChartFinite_coe] at h1
          change ψ y = mulC c (ψ' y)
          rw [hv1, hv'1, hmulCco c hc0 v', h1]
      exact hEq.eventuallyEq_of_mem (hNo.mem_nhds hxN)
  -- ## §5 Germ agreement is closed among elements: cluster equality forces equality.
  have hgermclosed : ∀ (ψ ψ' : M → ℂ̂) (x : M),
      (∀ᶠ y in 𝓝 x, Q ψ y) → (∀ᶠ y in 𝓝 x, Q ψ' y) →
      (∀ O : Set M, IsOpen O → x ∈ O → ∃ z ∈ O, ψ =ᶠ[𝓝 z] ψ') → ψ =ᶠ[𝓝 x]
          ψ' := by
    intro ψ ψ' x hψ hψ' hclu
    obtain ⟨c, hc1, hcev⟩ := hrigid ψ ψ' x hψ hψ'
    have hc0 : c ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hc1
      exact one_ne_zero hc1.symm
    obtain ⟨O₀, hO₀o, hxO₀, hO₀⟩ := hOpen ψ (fun y => mulC c (ψ' y)) x hcev
    obtain ⟨W', hW'nh, hW'Q⟩ := eventually_iff_exists_mem.mp hψ'
    obtain ⟨W1, hW1W, hW1o, hxW1⟩ := mem_nhds_iff.mp hW'nh
    obtain ⟨z, hz, hzeq⟩ := hclu (O₀ ∩ W1) (hO₀o.inter hW1o) ⟨hxO₀, hxW1⟩
    obtain ⟨O₁, hO₁o, hzO₁, hO₁⟩ := hOpen ψ ψ' z hzeq
    obtain ⟨w, hw, hwp1, hwp2⟩ := hnear z (O₀ ∩ W1 ∩ O₁)
      ((hO₀o.inter hW1o).inter hO₁o) ⟨hz, hzO₁⟩
    have h1 : ψ =ᶠ[𝓝 w] fun y => mulC c (ψ' y) := hO₀ w hw.1.1
    have h2 : ψ =ᶠ[𝓝 w] ψ' := hO₁ w hw.2
    have h3 : Q ψ' w := hW'Q w (hW1W hw.1.2)
    rw [hQ] at h3
    obtain ⟨v', hv'1, hv'2⟩ := h3.2.1 hwp1 hwp2
    have hv'0 : v' ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hv'2
      exact absurd hv'2.symm (ne_of_gt (Real.exp_pos _))
    have h5 : ψ w = mulC c (ψ' w) := h1.eq_of_nhds
    have h6 : ψ w = ψ' w := h2.eq_of_nhds
    have h7 : c = 1 := by
      rw [hv'1, hmulCco c hc0 v'] at h5
      rw [hv'1] at h6
      rw [h6] at h5
      have h8 : v' = c * v' := OnePoint.coe_eq_coe.mp h5
      have h9 : (1 : ℂ) * v' = c * v' := by
        rw [one_mul]
        exact h8
      exact (mul_right_cancel₀ hv'0 h9).symm
    have h9 : (fun y => mulC c (ψ' y)) =ᶠ[𝓝 x] ψ' := by
      refine Filter.Eventually.of_forall fun y => ?_
      change mulC c (ψ' y) = ψ' y
      rw [h7, hmulC1]
    exact hcev.trans h9
  -- ## §6 The initial element and the continuation predicate.
  obtain ⟨Ψ, hΨ⟩ := helt p₁
  obtain ⟨IsCont, hIC⟩ : ∃ P : (ℝ → M) → ℝ → (ℝ → M → ℂ̂) → Prop, ∀ γ
      b Φ, P γ b Φ ↔
      ((∀ t ∈ Set.Icc (0:ℝ) b, ∀ᶠ y in 𝓝 (γ t), Q (Φ t) y) ∧ Φ 0 =ᶠ[𝓝 p₁]
          Ψ ∧
        ∀ t ∈ Set.Icc (0:ℝ) b, ∃ ε > 0, ∀ u ∈ Set.Icc (0:ℝ) b, |u - t| < ε →
          Φ u =ᶠ[𝓝 (γ u)] Φ t) :=
    ⟨_, fun _ _ _ => Iff.rfl⟩
  -- ## §6b Real-interval induction: nonempty at the left end, closed from the left,
  -- open to the right, forces membership of the right end.
  have hind : ∀ (a b : ℝ) (A : Set ℝ), a ≤ b → (∀ x ∈ A, x ∈ Set.Icc a b) → a ∈
      A →
      (∀ c ∈ Set.Icc a b, (∀ δ > 0, ∃ x ∈ A, c - δ < x ∧ x ≤ c) → c ∈ A) →
      (∀ c ∈ A, c < b → ∃ δ > 0, ∀ x ∈ Set.Icc a b, c ≤ x → x < c + δ → x ∈ A)
          →
      b ∈ A := by
    intro a b A hab hsub haA hclosed hopen
    have hne : A.Nonempty := ⟨a, haA⟩
    have hbdd : BddAbove A := ⟨b, fun x hx => (hsub x hx).2⟩
    have hcIcc : sSup A ∈ Set.Icc a b :=
      ⟨le_csSup hbdd haA, csSup_le hne fun x hx => (hsub x hx).2⟩
    have hcA : sSup A ∈ A := by
      refine hclosed _ hcIcc ?_
      intro δ hδ0
      obtain ⟨x, hxA, hxgt⟩ := exists_lt_of_lt_csSup hne
        (by linarith : sSup A - δ < sSup A)
      exact ⟨x, hxA, hxgt, le_csSup hbdd hxA⟩
    rcases eq_or_lt_of_le hcIcc.2 with hcb | hcb
    · exact hcb ▸ hcA
    · exfalso
      obtain ⟨δ, hδ0, hδA⟩ := hopen _ hcA hcb
      have hx : min (sSup A + δ / 2) b ∈ A := by
        refine hδA _ ⟨le_min (by linarith [hcIcc.1]) hab,
          min_le_right _ _⟩ (le_min (by linarith) hcb.le) ?_
        calc min (sSup A + δ / 2) b ≤ sSup A + δ / 2 := min_le_left _ _
          _ < sSup A + δ := by linarith
      have hle : min (sSup A + δ / 2) b ≤ sSup A := le_csSup hbdd hx
      have hgt : sSup A < min (sSup A + δ / 2) b := lt_min (by linarith) hcb
      linarith
  -- ## §7 Existence of continuations.
  have hexist : ∀ γ : ℝ → M, ContinuousOn γ (Set.Icc 0 1) → γ 0 = p₁ →
      ∃ Φ, IsCont γ 1 Φ := by
    intro γ hγ hγ0
    -- one-step gluing: near any parameter c, a continuation up to a point near c
    -- extends past c using the element at γ c and phase rigidity.
    have hglue : ∀ c ∈ Set.Icc (0:ℝ) 1, ∃ δ > 0, ∀ a ∈ Set.Icc (0:ℝ) 1, |a - c| < δ
        →
        (∃ Φ, IsCont γ a Φ) → ∀ b' ∈ Set.Icc (0:ℝ) 1, a ≤ b' → |b' - c| < δ →
        ∃ Φ', IsCont γ b' Φ' := by
      intro c hc
      obtain ⟨ψ, hψev⟩ := helt (γ c)
      obtain ⟨W, hWo, hWc, hWQ⟩ := hQopen ψ (γ c) hψev
      obtain ⟨δ, hδ0, hδW⟩ := hγnb γ (Set.Icc 0 1) c hγ hc W hWo hWc
      refine ⟨δ, hδ0, ?_⟩
      rintro a ha hac ⟨Φ, hΦ⟩ b' hb' hab' hb'c
      rw [hIC] at hΦ
      obtain ⟨hΦa, hΦ0, hΦc⟩ := hΦ
      have hγaW : γ a ∈ W := hδW a ha hac
      obtain ⟨u₀, hu₀, hu₀ev⟩ := hrigid (Φ a) ψ (γ a)
        (hΦa a ⟨ha.1, le_refl a⟩) (hWQ (γ a) hγaW).2
      obtain ⟨Oa, hOao, hγaOa, hOa⟩ := hOpen (Φ a) (fun y => mulC u₀ (ψ y)) (γ a) hu₀ev
      refine ⟨fun t => if t ≤ a then Φ t else fun y => mulC u₀ (ψ y), ?_⟩
      rw [hIC]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        by_cases hta : t ≤ a
        · rw [if_pos hta]
          exact hΦa t ⟨ht.1, hta⟩
        · rw [not_le] at hta
          rw [if_neg (not_le.mpr hta)]
          have htc : |t - c| < δ := by
            rw [abs_sub_lt_iff] at hac hb'c ⊢
            constructor
            · linarith [ht.2, hb'c.1]
            · linarith [hac.2]
          have htW : γ t ∈ W := hδW t ⟨ht.1, ht.2.trans hb'.2⟩ htc
          filter_upwards [(hWQ (γ t) htW).2] with y hy using hQsmul u₀ hu₀ ψ y hy
      · rw [if_pos ha.1]
        exact hΦ0
      · intro t ht
        rcases lt_trichotomy t a with hta | hta | hta
        · obtain ⟨ε, hε0, hεp⟩ := hΦc t ⟨ht.1, hta.le⟩
          refine ⟨min ε (a - t), lt_min hε0 (by linarith), ?_⟩
          intro u hu huε
          rw [lt_min_iff] at huε
          have hua : u ≤ a := by
            have h6 := abs_sub_lt_iff.mp huε.2
            linarith [h6.1]
          rw [if_pos hua, if_pos hta.le]
          exact hεp u ⟨hu.1, hua⟩ huε.1
        · obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc a ⟨ha.1, le_refl a⟩
          obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hγnb γ (Set.Icc 0 1) a hγ ha Oa hOao hγaOa
          refine ⟨min ε₁ δ₂, lt_min hε₁0 hδ₂0, ?_⟩
          intro u hu huε
          rw [lt_min_iff] at huε
          have hut : |u - a| < ε₁ := by rw [← hta]; exact huε.1
          have hut2 : |u - a| < δ₂ := by rw [← hta]; exact huε.2
          by_cases hua : u ≤ a
          · rw [if_pos hua, if_pos hta.le, hta]
            exact hε₁p u ⟨hu.1, hua⟩ hut
          · rw [not_le] at hua
            rw [if_neg (not_le.mpr hua), if_pos hta.le, hta]
            have h3 : γ u ∈ Oa := hδ₂ u ⟨hu.1, hu.2.trans hb'.2⟩ hut2
            exact (hOa (γ u) h3).symm
        · refine ⟨t - a, by linarith, ?_⟩
          intro u hu huε
          rw [abs_sub_lt_iff] at huε
          have hua : a < u := by linarith [huε.2]
          rw [if_neg (not_le.mpr hua), if_neg (not_le.mpr hta)]
    have h1A : (1:ℝ) ∈ {b | b ∈ Set.Icc (0:ℝ) 1 ∧ ∃ Φ, IsCont γ b Φ} := by
      refine hind 0 1 _ zero_le_one (fun x hx => hx.1) ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩ ?_ ?_
      · refine ⟨fun _ => Ψ, ?_⟩
        rw [hIC]
        refine ⟨?_, Filter.EventuallyEq.refl _ _, ?_⟩
        · intro t ht
          have ht0 : t = 0 := le_antisymm ht.2 ht.1
          rw [ht0, hγ0]
          exact hΨ
        · intro t ht
          exact ⟨1, one_pos, fun u hu _ => Filter.EventuallyEq.refl _ _⟩
      · intro c hc hap
        obtain ⟨δ, hδ0, hglued⟩ := hglue c hc
        obtain ⟨x, hxA, hxgt, hxle⟩ := hap δ hδ0
        refine ⟨hc, hglued x hxA.1 ?_ hxA.2 c hc hxle ?_⟩
        · rw [abs_sub_lt_iff]
          constructor <;> linarith
        · rw [sub_self, abs_zero]
          exact hδ0
      · intro c hcA hclt
        obtain ⟨δ, hδ0, hglued⟩ := hglue c hcA.1
        refine ⟨δ, hδ0, ?_⟩
        intro x hx hcx hxδ
        refine ⟨hx, hglued c hcA.1 ?_ hcA.2 x hx hcx ?_⟩
        · rw [sub_self, abs_zero]
          exact hδ0
        · rw [abs_sub_lt_iff]
          constructor <;> linarith
    exact h1A.2
  -- ## §8 Uniqueness of continuations.
  have huniq : ∀ γ : ℝ → M, ContinuousOn γ (Set.Icc 0 1) → γ 0 = p₁ →
      ∀ Φ Φ', IsCont γ 1 Φ → IsCont γ 1 Φ' →
      ∀ t ∈ Set.Icc (0:ℝ) 1, Φ t =ᶠ[𝓝 (γ t)] Φ' t := by
    intro γ hγ hγ0 Φ Φ' hΦ hΦ'
    rw [hIC] at hΦ hΦ'
    obtain ⟨hΦa, hΦ0, hΦc⟩ := hΦ
    obtain ⟨hΦ'a, hΦ'0, hΦ'c⟩ := hΦ'
    have h1A : (1:ℝ) ∈ {b | b ∈ Set.Icc (0:ℝ) 1 ∧
        ∀ t ∈ Set.Icc (0:ℝ) b, Φ t =ᶠ[𝓝 (γ t)] Φ' t} := by
      refine hind 0 1 _ zero_le_one (fun x hx => hx.1) ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩ ?_ ?_
      · intro t ht
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        rw [ht0, hγ0]
        exact hΦ0.trans hΦ'0.symm
      · intro c hc hap
        refine ⟨hc, ?_⟩
        intro t ht
        rcases eq_or_lt_of_le ht.2 with htc | htc
        · -- t = c: germ closure via approximants
          have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, htc.le.trans hc.2⟩
          refine hgermclosed (Φ t) (Φ' t) (γ t) (hΦa t htI) (hΦ'a t htI) ?_
          intro O hOo hγtO
          obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb γ (Set.Icc 0 1) t hγ htI O hOo hγtO
          obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc t htI
          obtain ⟨ε₂, hε₂0, hε₂p⟩ := hΦ'c t htI
          have hmin0 : 0 < min δ₁ (min ε₁ ε₂) := lt_min hδ₁0 (lt_min hε₁0 hε₂0)
          obtain ⟨x, hxA, hxgt, hxle⟩ := hap (min δ₁ (min ε₁ ε₂)) hmin0
          have hxd : |x - t| < min δ₁ (min ε₁ ε₂) := by
            rw [abs_sub_lt_iff]
            constructor <;> linarith
          have hxI : x ∈ Set.Icc (0:ℝ) 1 := hxA.1
          have hd1 : |x - t| < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
          have hd2 : |x - t| < ε₁ :=
            lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_left _ _))
          have hd3 : |x - t| < ε₂ :=
            lt_of_lt_of_le hxd ((min_le_right _ _).trans (min_le_right _ _))
          refine ⟨γ x, hδ₁ x hxI hd1, ?_⟩
          have e1 : Φ x =ᶠ[𝓝 (γ x)] Φ t := hε₁p x hxI hd2
          have e2 : Φ' x =ᶠ[𝓝 (γ x)] Φ' t := hε₂p x hxI hd3
          have e3 : Φ x =ᶠ[𝓝 (γ x)] Φ' x := hxA.2 x ⟨hxI.1, le_refl x⟩
          exact e1.symm.trans (e3.trans e2)
        · -- t < c: an approximant already covers t
          obtain ⟨x, hxA, hxgt, hxle⟩ := hap (c - t) (by linarith)
          exact hxA.2 t ⟨ht.1, by linarith⟩
      · intro c hcA hclt
        obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc c hcA.1
        obtain ⟨ε₂, hε₂0, hε₂p⟩ := hΦ'c c hcA.1
        have hagr : Φ c =ᶠ[𝓝 (γ c)] Φ' c := hcA.2 c ⟨hcA.1.1, le_refl c⟩
        obtain ⟨Oc, hOco, hγcOc, hOc⟩ := hOpen (Φ c) (Φ' c) (γ c) hagr
        obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb γ (Set.Icc 0 1) c hγ hcA.1 Oc hOco hγcOc
        have hmin0 : 0 < min δ₁ (min ε₁ ε₂) := lt_min hδ₁0 (lt_min hε₁0 hε₂0)
        refine ⟨min δ₁ (min ε₁ ε₂), hmin0, ?_⟩
        intro x hx hcx hxδ
        refine ⟨hx, ?_⟩
        intro t ht
        by_cases htc : t ≤ c
        · exact hcA.2 t ⟨ht.1, htc⟩
        · rw [not_le] at htc
          have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
          have htd : |t - c| < min δ₁ (min ε₁ ε₂) := by
            rw [abs_sub_lt_iff]
            constructor
            · linarith [ht.2]
            · linarith
          have hd1 : |t - c| < δ₁ := lt_of_lt_of_le htd (min_le_left _ _)
          have hd2 : |t - c| < ε₁ :=
            lt_of_lt_of_le htd ((min_le_right _ _).trans (min_le_left _ _))
          have hd3 : |t - c| < ε₂ :=
            lt_of_lt_of_le htd ((min_le_right _ _).trans (min_le_right _ _))
          have e1 : Φ t =ᶠ[𝓝 (γ t)] Φ c := hε₁p t htI hd2
          have e2 : Φ' t =ᶠ[𝓝 (γ t)] Φ' c := hε₂p t htI hd3
          have e4 : Φ c =ᶠ[𝓝 (γ t)] Φ' c := hOc (γ t) (hδ₁ t htI hd1)
          exact e1.trans (e4.trans e2.symm)
    exact h1A.2
  -- ## §8b Transport of germ equality along a path through common element territory.
  have htransport : ∀ (ψ ψ' : M → ℂ̂) (ζ : ℝ → M) (a b : ℝ), a ≤ b →
      ContinuousOn ζ (Set.Icc a b) →
      (∀ σ ∈ Set.Icc a b, ∀ᶠ y in 𝓝 (ζ σ), Q ψ y) →
      (∀ σ ∈ Set.Icc a b, ∀ᶠ y in 𝓝 (ζ σ), Q ψ' y) →
      ψ =ᶠ[𝓝 (ζ a)] ψ' → ∀ σ ∈ Set.Icc a b, ψ =ᶠ[𝓝 (ζ σ)] ψ' := by
    intro ψ ψ' ζ a b hab hζ hQ1 hQ2 heq0
    have hbA : b ∈ {σ | σ ∈ Set.Icc a b ∧ ∀ τ ∈ Set.Icc a σ, ψ =ᶠ[𝓝 (ζ τ)]
        ψ'} := by
      refine hind a b _ hab (fun x hx => hx.1) ⟨⟨le_refl a, hab⟩, ?_⟩ ?_ ?_
      · intro τ hτ
        have hτa : τ = a := le_antisymm hτ.2 hτ.1
        rw [hτa]
        exact heq0
      · intro c hc hap
        refine ⟨hc, ?_⟩
        intro τ hτ
        rcases eq_or_lt_of_le hτ.2 with hτc | hτc
        · have hτI : τ ∈ Set.Icc a b := ⟨hτ.1, hτc.le.trans hc.2⟩
          refine hgermclosed ψ ψ' (ζ τ) (hQ1 τ hτI) (hQ2 τ hτI) ?_
          intro O hOo hζτO
          obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb ζ (Set.Icc a b) τ hζ hτI O hOo hζτO
          obtain ⟨x, hxA, hxgt, hxle⟩ := hap δ₁ hδ₁0
          have hxd : |x - τ| < δ₁ := by
            rw [abs_sub_lt_iff]
            constructor <;> linarith
          exact ⟨ζ x, hδ₁ x hxA.1 hxd, hxA.2 x ⟨hxA.1.1, le_refl x⟩⟩
        · obtain ⟨x, hxA, hxgt, hxle⟩ := hap (c - τ) (by linarith)
          exact hxA.2 τ ⟨hτ.1, by linarith⟩
      · intro c hcA hclt
        have hagr : ψ =ᶠ[𝓝 (ζ c)] ψ' := hcA.2 c ⟨hcA.1.1, le_refl c⟩
        obtain ⟨Oc, hOco, hζcOc, hOc⟩ := hOpen ψ ψ' (ζ c) hagr
        obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hγnb ζ (Set.Icc a b) c hζ hcA.1 Oc hOco hζcOc
        refine ⟨δ₁, hδ₁0, ?_⟩
        intro x hx hcx hxδ
        refine ⟨hx, ?_⟩
        intro τ hτ
        by_cases hτc : τ ≤ c
        · exact hcA.2 τ ⟨hτ.1, hτc⟩
        · rw [not_le] at hτc
          have hτI : τ ∈ Set.Icc a b := ⟨hτ.1, hτ.2.trans hx.2⟩
          have hτd : |τ - c| < δ₁ := by
            rw [abs_sub_lt_iff]
            constructor
            · linarith [hτ.2]
            · linarith
          exact hOc (ζ τ) (hδ₁ τ hτI hτd)
    exact fun σ hσ => hbA.2 σ hσ
  -- ## §9 The adjacent-path lemma (fixed endpoints).
  have hadj : ∀ (η : ℝ × ℝ → M), Continuous η → (∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 0)
      = p₁) →
      (∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 1) = η (0, 1)) →
      ∀ s₀ ∈ Set.Icc (0:ℝ) 1, ∀ Φ, IsCont (fun t => η (s₀, t)) 1 Φ →
      ∃ ε > 0, ∀ s' ∈ Set.Icc (0:ℝ) 1, |s' - s₀| < ε →
        ∃ Φ', IsCont (fun t => η (s', t)) 1 Φ' ∧ Φ' 1 =ᶠ[𝓝 (η (0, 1))] Φ 1 := by
    intro η hη hη0 hη1 s₀ hs₀ Φ hΦ
    rw [hIC] at hΦ
    obtain ⟨hΦa, hΦ0, hΦc⟩ := hΦ
    -- per-time data: an element window around the s₀-path with a stability radius
    have hdata : ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ d > 0, ∃ W : Set M, IsOpen W ∧
        (∀ z ∈ W, Q (Φ t) z) ∧
        (∀ p : ℝ × ℝ, |p.1 - s₀| < d → |p.2 - t| < d → η p ∈ W) ∧
        (∀ u ∈ Set.Icc (0:ℝ) 1, |u - t| < d → Φ u =ᶠ[𝓝 (η (s₀, u))] Φ t) := by
      intro t ht
      obtain ⟨W, hWo, hWmem, hWall⟩ := hQopen (Φ t) (η (s₀, t)) (hΦa t ht)
      obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦc t ht
      have hpre : η ⁻¹' W ∈ 𝓝 (s₀, t) :=
        hη.continuousAt.preimage_mem_nhds (hWo.mem_nhds hWmem)
      obtain ⟨r, hr0, hrsub⟩ := Metric.mem_nhds_iff.mp hpre
      refine ⟨min r ε₁, lt_min hr0 hε₁0, W, hWo, fun z hz => (hWall z hz).1, ?_, ?_⟩
      · intro p hp1 hp2
        apply hrsub
        rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (lt_of_lt_of_le hp1 (min_le_left _ _))
          (lt_of_lt_of_le hp2 (min_le_left _ _))
      · intro u hu hud
        exact hε₁p u hu (lt_of_lt_of_le hud (min_le_right _ _))
    choose! dfun hd0 W hWo hWQ hWnear hloc using hdata
    -- a uniform radius: cover [0,1] with half-windows, finite subcover, finite minimum
    have hcover : Set.Icc (0:ℝ) 1 ⊆
        ⋃ t : ↥(Set.Icc (0:ℝ) 1), ball (t : ℝ) (dfun (t : ℝ) / 2) := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self ?_⟩
      have h1 := hd0 x hx
      linarith
    obtain ⟨T, hTcov⟩ := isCompact_Icc.elim_finite_subcover
      (fun t : ↥(Set.Icc (0:ℝ) 1) => ball (t : ℝ) (dfun (t : ℝ) / 2))
      (fun _ => isOpen_ball) hcover
    have hTne : T.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h0 := hTcov (Set.left_mem_Icc.mpr zero_le_one)
      rw [hemp] at h0
      simp at h0
    have hε0 : 0 < T.inf' hTne (fun t => dfun (t : ℝ) / 2) := by
      rw [Finset.lt_inf'_iff]
      intro t htT
      have h1 := hd0 (t : ℝ) t.2
      linarith
    refine ⟨T.inf' hTne (fun t => dfun (t : ℝ) / 2), hε0, ?_⟩
    intro s' hs' hss
    -- the grid: N₀ with 1 / (N₀ + 1) below the uniform radius
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε0
    -- interval assignment: each grid interval sits inside one data window
    have hassign : ∀ i : ℕ, i ≤ N₀ → ∃ t ∈ Set.Icc (0:ℝ) 1,
        (∀ u : ℝ, (i : ℝ) / ((N₀ : ℝ) + 1) ≤ u → u ≤ ((i : ℝ) + 1) / ((N₀ : ℝ)
            + 1) →
          |u - t| < dfun t) ∧ |s' - s₀| < dfun t := by
      intro i hi
      have hgi : (i : ℝ) / ((N₀ : ℝ) + 1) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          have h1 : (i : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hi
          linarith
      have hmem := hTcov hgi
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨t, htT, hgt⟩ := hmem
      have hεle : T.inf' hTne (fun t => dfun (t : ℝ) / 2) ≤ dfun (t : ℝ) / 2 :=
        Finset.inf'_le _ htT
      have hdt0 : 0 < dfun (t : ℝ) := hd0 (t : ℝ) t.2
      have hdist : |(i : ℝ) / ((N₀ : ℝ) + 1) - (t : ℝ)| < dfun (t : ℝ) / 2 := by
        have h1 := mem_ball.mp hgt
        rwa [Real.dist_eq] at h1
      rw [abs_sub_lt_iff] at hdist
      refine ⟨(t : ℝ), t.2, ?_, ?_⟩
      · intro u hu1 hu2
        have hstep : u - (i : ℝ) / ((N₀ : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
          rw [add_div] at hu2
          linarith
        rw [abs_sub_lt_iff]
        constructor
        · linarith [hdist.1, hN₀, hεle]
        · linarith [hdist.2, hu1]
      · calc |s' - s₀| < T.inf' hTne (fun t => dfun (t : ℝ) / 2) := hss
          _ ≤ dfun (t : ℝ) / 2 := hεle
          _ < dfun (t : ℝ) := by linarith
    choose! tc htcI htcwin htcs using hassign
    -- segment membership and distance comparison
    have hsegI : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → σ ∈ Set.Icc (0:ℝ) 1 :=
        by
      intro σ h1 h2
      constructor
      · rcases le_total s₀ s' with h | h
        · rw [min_eq_left h] at h1; linarith [hs₀.1]
        · rw [min_eq_right h] at h1; linarith [hs'.1]
      · rcases le_total s₀ s' with h | h
        · rw [max_eq_right h] at h2; linarith [hs'.2]
        · rw [max_eq_left h] at h2; linarith [hs₀.2]
    have habs : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → |σ - s₀| ≤ |s' - s₀| :=
        by
      intro σ h1 h2
      rcases le_total s₀ s' with hle | hle
      · rw [min_eq_left hle] at h1
        rw [max_eq_right hle] at h2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · rw [min_eq_right hle] at h1
        rw [max_eq_left hle] at h2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    -- transport specialised to the σ-segment at a fixed height
    have hseg : ∀ (u : ℝ) (ψ ψ' : M → ℂ̂),
        (∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → ∀ᶠ y in 𝓝 (η (σ, u)), Q ψ
            y) →
        (∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → ∀ᶠ y in 𝓝 (η (σ, u)), Q ψ'
            y) →
        ψ =ᶠ[𝓝 (η (s₀, u))] ψ' → ψ =ᶠ[𝓝 (η (s', u))] ψ' := by
      intro u ψ ψ' hq1 hq2 heq
      rcases le_total s₀ s' with hle | hle
      · have hcont1 : Continuous fun σ : ℝ => η (σ, u) :=
          hη.comp (continuous_id.prodMk continuous_const)
        exact htransport ψ ψ' (fun σ => η (σ, u)) s₀ s' hle hcont1.continuousOn
          (fun σ hσ => hq1 σ (by rw [min_eq_left hle]; exact hσ.1)
            (by rw [max_eq_right hle]; exact hσ.2))
          (fun σ hσ => hq2 σ (by rw [min_eq_left hle]; exact hσ.1)
            (by rw [max_eq_right hle]; exact hσ.2))
          heq s' ⟨hle, le_refl s'⟩
      · have hcont2 : Continuous fun σ : ℝ => η (s₀ + s' - σ, u) :=
          hη.comp ((continuous_const.sub continuous_id).prodMk continuous_const)
        have h1 := htransport ψ ψ' (fun σ => η (s₀ + s' - σ, u)) s' s₀ hle
          hcont2.continuousOn
          (fun σ hσ => hq1 (s₀ + s' - σ)
            (by rw [min_eq_right hle]; linarith [hσ.2])
            (by rw [max_eq_left hle]; linarith [hσ.1]))
          (fun σ hσ => hq2 (s₀ + s' - σ)
            (by rw [min_eq_right hle]; linarith [hσ.2])
            (by rw [max_eq_left hle]; linarith [hσ.1]))
          (by
            have h2 : s₀ + s' - s' = s₀ := by ring
            simpa [h2] using heq)
          s₀ ⟨hle, le_refl s₀⟩
        have h3 : s₀ + s' - s₀ = s' := by ring
        simpa [h3] using h1
    -- grid induction: continuation along the s'-path up to each grid point,
    -- with the terminal germ locked to that of the s₀-continuation
    have hkey : ∀ i : ℕ, i ≤ N₀ + 1 →
        ∃ Φ', IsCont (fun t => η (s', t)) ((i : ℝ) / ((N₀ : ℝ) + 1)) Φ' ∧
        ∀ ψtar : M → ℂ̂,
          Φ ((i : ℝ) / ((N₀ : ℝ) + 1)) =ᶠ[𝓝 (η (s₀, (i : ℝ) / ((N₀ : ℝ) + 1)))]
              ψtar →
          (∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' →
            ∀ᶠ y in 𝓝 (η (σ, (i : ℝ) / ((N₀ : ℝ) + 1))), Q ψtar y) →
          Φ' ((i : ℝ) / ((N₀ : ℝ) + 1)) =ᶠ[𝓝 (η (s', (i : ℝ) / ((N₀ : ℝ) + 1)))]
              ψtar := by
      intro i
      induction i with
      | zero =>
        intro _
        have h00 : ((0 : ℕ) : ℝ) / ((N₀ : ℝ) + 1) = 0 := by norm_num
        rw [h00]
        have hp0' : η (s', 0) = p₁ := hη0 s' hs'
        have hp0 : η (s₀, 0) = p₁ := hη0 s₀ hs₀
        refine ⟨fun _ => Φ 0, ?_, ?_⟩
        · rw [hIC]
          refine ⟨?_, ?_, ?_⟩
          · intro t ht
            have ht0 : t = 0 := le_antisymm ht.2 ht.1
            rw [ht0, hp0']
            have h1 := hΦa 0 ⟨le_refl 0, zero_le_one⟩
            rw [hp0] at h1
            exact h1
          · exact hΦ0
          · intro t ht
            exact ⟨1, one_pos, fun u hu _ => Filter.EventuallyEq.refl _ _⟩
        · intro ψtar htar hQtar
          rw [hp0] at htar
          rw [hp0']
          exact htar
      | succ i ih =>
        intro hi1
        have hiN : i ≤ N₀ := Nat.succ_le_succ_iff.mp hi1
        obtain ⟨Φ', hΦ'IC, hΦ'germ⟩ := ih (Nat.le_succ_of_le hiN)
        have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hNR : (0:ℝ) < (N₀ : ℝ) + 1 := by positivity
        have hgiI : (i : ℝ) / ((N₀ : ℝ) + 1) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · positivity
          · rw [div_le_one hNR]
            have h1 : (i : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hiN
            linarith
        have hgi1I : ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) ∈ Set.Icc (0:ℝ) 1 := by
          constructor
          · positivity
          · rw [div_le_one hNR]
            have h1 : (i : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hiN
            linarith
        have hgilt : (i : ℝ) / ((N₀ : ℝ) + 1) < ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) := by
          have h1 : ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) - (i : ℝ) / ((N₀ : ℝ) + 1) =
              1 / ((N₀ : ℝ) + 1) := by
            rw [div_sub_div_same]
            norm_num
          have h2 : (0:ℝ) < 1 / ((N₀ : ℝ) + 1) := by positivity
          linarith
        -- window facts for interval i
        have hIci : tc i ∈ Set.Icc (0:ℝ) 1 := htcI i hiN
        have hwin := htcwin i hiN
        have hswin : |s' - s₀| < dfun (tc i) := htcs i hiN
        have hK1 : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' → ∀ u, (i : ℝ) / ((N₀ :
            ℝ) + 1) ≤ u →
            u ≤ ((i : ℝ) + 1) / ((N₀ : ℝ) + 1) → η (σ, u) ∈ W (tc i) := by
          intro σ h1 h2 u h3 h4
          refine hWnear (tc i) hIci (σ, u) ?_ (hwin u h3 h4)
          calc |σ - s₀| ≤ |s' - s₀| := habs σ h1 h2
            _ < dfun (tc i) := hswin
        have hK2 : ∀ u, (i : ℝ) / ((N₀ : ℝ) + 1) ≤ u → u ≤ ((i : ℝ) + 1) / ((N₀ :
            ℝ) + 1) →
            u ∈ Set.Icc (0:ℝ) 1 → Φ u =ᶠ[𝓝 (η (s₀, u))] Φ (tc i) := by
          intro u h1 h2 hu
          exact hloc (tc i) hIci u hu (hwin u h1 h2)
        -- junction germ at the grid point gi
        have hjunc : Φ' ((i : ℝ) / ((N₀ : ℝ) + 1))
            =ᶠ[𝓝 (η (s', (i : ℝ) / ((N₀ : ℝ) + 1)))] Φ (tc i) := by
          refine hΦ'germ (Φ (tc i)) (hK2 _ (le_refl _) hgilt.le hgiI) ?_
          intro σ hσ1 hσ2
          have hmem : η (σ, (i : ℝ) / ((N₀ : ℝ) + 1)) ∈ W (tc i) :=
            hK1 σ hσ1 hσ2 _ (le_refl _) hgilt.le
          filter_upwards [(hWo (tc i) hIci).mem_nhds hmem] with y hy using
            hWQ (tc i) hIci y hy
        refine ⟨fun u => if u ≤ (i : ℝ) / ((N₀ : ℝ) + 1) then Φ' u else Φ (tc i), ?_,
            ?_⟩
        · rw [hIC] at hΦ'IC ⊢
          obtain ⟨hpa, hp0, hpc⟩ := hΦ'IC
          refine ⟨?_, ?_, ?_⟩
          · intro t ht
            by_cases hta : t ≤ (i : ℝ) / ((N₀ : ℝ) + 1)
            · rw [if_pos hta]
              exact hpa t ⟨ht.1, hta⟩
            · rw [not_le] at hta
              rw [if_neg (not_le.mpr hta)]
              have hmem : η (s', t) ∈ W (tc i) :=
                hK1 s' (min_le_right _ _) (le_max_right _ _) t hta.le ht.2
              filter_upwards [(hWo (tc i) hIci).mem_nhds hmem] with y hy using
                hWQ (tc i) hIci y hy
          · have hnn : (0:ℝ) ≤ (i : ℝ) / ((N₀ : ℝ) + 1) := by positivity
            rw [if_pos hnn]
            exact hp0
          · intro t ht
            rcases lt_trichotomy t ((i : ℝ) / ((N₀ : ℝ) + 1)) with hta | hta | hta
            · obtain ⟨ε', hε'0, hε'p⟩ := hpc t ⟨ht.1, hta.le⟩
              refine ⟨min ε' ((i : ℝ) / ((N₀ : ℝ) + 1) - t), lt_min hε'0 (by linarith),
                  ?_⟩
              intro u hu huε
              rw [lt_min_iff] at huε
              have hua : u ≤ (i : ℝ) / ((N₀ : ℝ) + 1) := by
                have h6 := abs_sub_lt_iff.mp huε.2
                linarith [h6.1]
              rw [if_pos hua, if_pos hta.le]
              exact hε'p u ⟨hu.1, hua⟩ huε.1
            · rw [hta]
              obtain ⟨ε', hε'0, hε'p⟩ := hpc ((i : ℝ) / ((N₀ : ℝ) + 1))
                ⟨by positivity, le_refl _⟩
              obtain ⟨O₂, hO₂o, hO₂mem, hO₂⟩ := hOpen _ _ _ hjunc
              have hcont' : Continuous fun t : ℝ => η (s', t) :=
                hη.comp (continuous_const.prodMk continuous_id)
              obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hγnb (fun t => η (s', t)) (Set.Icc 0 1)
                ((i : ℝ) / ((N₀ : ℝ) + 1)) hcont'.continuousOn hgiI O₂ hO₂o hO₂mem
              refine ⟨min ε' δ₂, lt_min hε'0 hδ₂0, ?_⟩
              intro u hu huε
              rw [lt_min_iff] at huε
              have huI : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1, hu.2.trans hgi1I.2⟩
              by_cases hua : u ≤ (i : ℝ) / ((N₀ : ℝ) + 1)
              · rw [if_pos hua, if_pos (le_refl _)]
                exact hε'p u ⟨hu.1, hua⟩ huε.1
              · rw [not_le] at hua
                rw [if_neg (not_le.mpr hua), if_pos (le_refl _)]
                have hmem2 : η (s', u) ∈ O₂ := hδ₂ u huI huε.2
                exact (hO₂ (η (s', u)) hmem2).symm
            · refine ⟨t - (i : ℝ) / ((N₀ : ℝ) + 1), by linarith, ?_⟩
              intro u hu huε
              rw [abs_sub_lt_iff] at huε
              have hua : (i : ℝ) / ((N₀ : ℝ) + 1) < u := by linarith [huε.2]
              rw [if_neg (not_le.mpr hua), if_neg (not_le.mpr hta)]
        · intro ψtar htar hQtar
          have hne1 : ¬(((i : ℝ) + 1) / ((N₀ : ℝ) + 1) ≤ (i : ℝ) / ((N₀ : ℝ) + 1)) :=
            not_le.mpr hgilt
          have hval : (fun u => if u ≤ (i : ℝ) / ((N₀ : ℝ) + 1) then Φ' u else Φ (tc i))
              (((i : ℝ) + 1) / ((N₀ : ℝ) + 1)) = Φ (tc i) := if_neg hne1
          rw [hval]
          have h1 : Φ (tc i) =ᶠ[𝓝 (η (s₀, ((i : ℝ) + 1) / ((N₀ : ℝ) + 1)))] ψtar :=
            (hK2 _ hgilt.le (le_refl _) hgi1I).symm.trans htar
          refine hseg _ (Φ (tc i)) ψtar ?_ hQtar h1
          intro σ hσ1 hσ2
          have hmem : η (σ, ((i : ℝ) + 1) / ((N₀ : ℝ) + 1)) ∈ W (tc i) :=
            hK1 σ hσ1 hσ2 _ hgilt.le (le_refl _)
          filter_upwards [(hWo (tc i) hIci).mem_nhds hmem] with y hy using
            hWQ (tc i) hIci y hy
    -- conclude at the last grid point
    obtain ⟨Φ', hΦ'IC, hΦ'germ⟩ := hkey (N₀ + 1) (le_refl _)
    have hNN : ((N₀ + 1 : ℕ) : ℝ) / ((N₀ : ℝ) + 1) = 1 := by
      push_cast
      exact div_self (by positivity : (0:ℝ) < (N₀ : ℝ) + 1).ne'
    rw [hNN] at hΦ'IC hΦ'germ
    have hQ1seg : ∀ σ, min s₀ s' ≤ σ → σ ≤ max s₀ s' →
        ∀ᶠ y in 𝓝 (η (σ, 1)), Q (Φ 1) y := by
      intro σ hσ1 hσ2
      have hσI : σ ∈ Set.Icc (0:ℝ) 1 := hsegI σ hσ1 hσ2
      have h2 : η (σ, 1) = η (s₀, 1) := by rw [hη1 σ hσI, hη1 s₀ hs₀]
      rw [h2]
      exact hΦa 1 ⟨zero_le_one, le_refl 1⟩
    have hfin := hΦ'germ (Φ 1) (Filter.EventuallyEq.refl _ _) hQ1seg
    rw [hη1 s' hs'] at hfin
    exact ⟨Φ', hΦ'IC, hfin⟩
  -- ## §10 Homotopy invariance of the terminal germ.
  have hhomo : ∀ (η : ℝ × ℝ → M), Continuous η → (∀ s ∈ Set.Icc (0:ℝ) 1, η (s,
      0) = p₁) →
      (∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 1) = η (0, 1)) →
      ∀ Φ₀ Φ₁, IsCont (fun t => η (0, t)) 1 Φ₀ → IsCont (fun t => η (1, t)) 1 Φ₁
          →
        Φ₁ 1 =ᶠ[𝓝 (η (0, 1))] Φ₀ 1 := by
    intro η hη hη0 hη1 Φ₀ Φ₁ hΦ₀ hΦ₁
    have h1A : (1:ℝ) ∈ {s | s ∈ Set.Icc (0:ℝ) 1 ∧ ∃ Φ, IsCont (fun t => η (s, t)) 1 Φ
        ∧
        Φ 1 =ᶠ[𝓝 (η (0, 1))] Φ₀ 1} := by
      refine hind 0 1 _ zero_le_one (fun x hx => hx.1)
        ⟨⟨le_refl 0, zero_le_one⟩, Φ₀, hΦ₀, Filter.EventuallyEq.refl _ _⟩ ?_ ?_
      · -- closed from the left: adjacency at the limit parameter
        intro c hc hap
        have hγc : ContinuousOn (fun t => η (c, t)) (Set.Icc 0 1) :=
          (hη.comp (continuous_const.prodMk continuous_id)).continuousOn
        obtain ⟨Φc, hΦc⟩ := hexist (fun t => η (c, t)) hγc (hη0 c hc)
        obtain ⟨ε, hε0, hεadj⟩ := hadj η hη hη0 hη1 c hc Φc hΦc
        obtain ⟨x, hxA, hxgt, hxle⟩ := hap ε hε0
        obtain ⟨Φx, hΦx, hΦxeq⟩ := hxA.2
        have hxd : |x - c| < ε := by
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        obtain ⟨Φ'x, hΦ'x, hΦ'xeq⟩ := hεadj x hxA.1 hxd
        have huu := huniq (fun t => η (x, t))
          ((hη.comp (continuous_const.prodMk continuous_id)).continuousOn)
          (hη0 x hxA.1) Φx Φ'x hΦx hΦ'x 1 ⟨zero_le_one, le_refl 1⟩
        have hpt : η (x, 1) = η (0, 1) := hη1 x hxA.1
        have huu' : Φx 1 =ᶠ[𝓝 (η (0, 1))] Φ'x 1 := by
          rw [← hpt]
          exact huu
        exact ⟨hc, Φc, hΦc, hΦ'xeq.symm.trans (huu'.symm.trans hΦxeq)⟩
      · -- open to the right: adjacency from a member parameter
        intro c hcA hclt
        obtain ⟨Φc, hΦc, hΦceq⟩ := hcA.2
        obtain ⟨ε, hε0, hεadj⟩ := hadj η hη hη0 hη1 c hcA.1 Φc hΦc
        refine ⟨ε, hε0, ?_⟩
        intro x hx hcx hxδ
        have hxd : |x - c| < ε := by
          rw [abs_sub_lt_iff]
          constructor <;> linarith
        obtain ⟨Φ'x, hΦ'x, hΦ'xeq⟩ := hεadj x hx hxd
        exact ⟨hx, Φ'x, hΦ'x, hΦ'xeq.trans hΦceq⟩
    obtain ⟨-, Φ, hΦ, hΦeq⟩ := h1A
    have huu := huniq (fun t => η (1, t))
      ((hη.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (hη0 1 ⟨zero_le_one, le_refl 1⟩) Φ₁ Φ hΦ₁ hΦ 1 ⟨zero_le_one, le_refl 1⟩
    have hpt : η (1, 1) = η (0, 1) := hη1 1 ⟨zero_le_one, le_refl 1⟩
    have huu' : Φ₁ 1 =ᶠ[𝓝 (η (0, 1))] Φ 1 := by
      rw [← hpt]
      exact huu
    exact huu'.trans hΦeq
  -- ## §11 Global assembly along paths.
  have hsel : ∀ q : M,
      ∃ Φ, IsCont (fun u => (PathConnectedSpace.somePath p₁ q).extend u) 1 Φ := by
    intro q
    refine hexist _ (Path.continuous_extend _).continuousOn ?_
    exact Path.extend_zero _
  choose ΦF hΦF using hsel
  have hQq : ∀ q : M, Q (ΦF q 1) q ∧ ∀ᶠ y in 𝓝 q, Q (ΦF q 1) y := by
    intro q
    have h1 := ((hIC _ _ _).mp (hΦF q)).1 1 ⟨zero_le_one, le_refl 1⟩
    rw [Path.extend_one] at h1
    exact ⟨Eventually.self_of_nhds h1, h1⟩
  -- local agreement: near any point, every chosen terminal element realises the
  -- same germ, by comparing paths through a chart-ball concatenation.
  have hlocal : ∀ q : M, ∃ B : Set M, IsOpen B ∧ q ∈ B ∧
      ∀ q' ∈ B, ΦF q' 1 =ᶠ[𝓝 q'] ΦF q 1 := by
    intro q
    obtain ⟨W, hWo, hqW, hWall⟩ := hQopen (ΦF q 1) q (hQq q).2
    have hqs : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
    have hT : IsOpen ((chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W) :=
      (chartAt ℂ q).isOpen_inter_preimage_symm hWo
    have hqT : chartAt ℂ q q ∈ (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W := by
      refine ⟨(chartAt ℂ q).map_source hqs, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ q).left_inv hqs]
      exact hqW
    obtain ⟨r, hr0, hrsub⟩ := Metric.isOpen_iff.mp hT _ hqT
    refine ⟨(chartAt ℂ q).source ∩ chartAt ℂ q ⁻¹' ball (chartAt ℂ q q) r,
      (chartAt ℂ q).continuousOn.isOpen_inter_preimage (chartAt ℂ q).open_source
        isOpen_ball,
      ⟨hqs, by rw [Set.mem_preimage]; exact mem_ball_self hr0⟩, ?_⟩
    intro q' hq'
    have hq's : q' ∈ (chartAt ℂ q).source := hq'.1
    have hq'b : chartAt ℂ q q' ∈ ball (chartAt ℂ q q) r := hq'.2
    -- the straight chart segment from q to q' stays in the ball
    have hsegmem : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
        (1 - (σ:ℂ)) * chartAt ℂ q q + (σ:ℂ) * chartAt ℂ q q' ∈
          ball (chartAt ℂ q q) r := by
      intro σ h0 h1
      rw [mem_ball, dist_eq_norm]
      have h2 : (1 - (σ:ℂ)) * chartAt ℂ q q + (σ:ℂ) * chartAt ℂ q q' -
          chartAt ℂ q q = (σ:ℂ) * (chartAt ℂ q q' - chartAt ℂ q q) := by ring
      have h3 : ‖chartAt ℂ q q' - chartAt ℂ q q‖ < r := by
        have h4 := mem_ball.mp hq'b
        rwa [dist_eq_norm] at h4
      rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
      calc σ * ‖chartAt ℂ q q' - chartAt ℂ q q‖ ≤
          1 * ‖chartAt ℂ q q' - chartAt ℂ q q‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖chartAt ℂ q q' - chartAt ℂ q q‖ := one_mul _
        _ < r := h3
    have hinner : Continuous fun σ : ℝ =>
        (1 - (σ:ℂ)) * chartAt ℂ q q + (σ:ℂ) * chartAt ℂ q q' :=
      ((continuous_const.sub Complex.continuous_ofReal).mul continuous_const).add
        (Complex.continuous_ofReal.mul continuous_const)
    have hρc : Continuous fun σ : unitInterval => (chartAt ℂ q).symm
        ((1 - ((σ:ℝ):ℂ)) * chartAt ℂ q q + ((σ:ℝ):ℂ) * chartAt ℂ q q') := by
      refine (chartAt ℂ q).continuousOn_symm.comp_continuous
        (hinner.comp continuous_subtype_val) ?_
      intro σ
      exact (hrsub (hsegmem (σ:ℝ) σ.2.1 σ.2.2)).1
    obtain ⟨ρpath, hρW⟩ : ∃ ρ : Path q q',
        ∀ σ : ℝ, σ ∈ Set.Icc (0:ℝ) 1 → ρ.extend σ ∈ W := by
      refine ⟨{ toFun := fun σ => (chartAt ℂ q).symm
                  ((1 - ((σ:ℝ):ℂ)) * chartAt ℂ q q + ((σ:ℝ):ℂ) * chartAt ℂ q q'),
                continuous_toFun := hρc,
                source' := ?_,
                target' := ?_ }, ?_⟩
      · have h0 : (1 - (((0 : unitInterval) : ℝ) : ℂ)) * chartAt ℂ q q +
            (((0 : unitInterval) : ℝ) : ℂ) * chartAt ℂ q q' = chartAt ℂ q q := by
          norm_num
        rw [h0]
        exact (chartAt ℂ q).left_inv hqs
      · have h1 : (1 - (((1 : unitInterval) : ℝ) : ℂ)) * chartAt ℂ q q +
            (((1 : unitInterval) : ℝ) : ℂ) * chartAt ℂ q q' = chartAt ℂ q q' := by
          norm_num
        rw [h1]
        exact (chartAt ℂ q).left_inv hq's
      · intro σ hσ
        rw [Path.extend_apply _ hσ]
        change (chartAt ℂ q).symm ((1 - (σ:ℂ)) * chartAt ℂ q q +
          (σ:ℂ) * chartAt ℂ q q') ∈ W
        have h5 := (hrsub (hsegmem σ hσ.1 hσ.2)).2
        rwa [Set.mem_preimage] at h5
    -- the concatenated path realises the same terminal element as the base point
    have htrans_le : ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 → u ≤ 1/2 →
        ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend u =
          (PathConnectedSpace.somePath p₁ q).extend (2*u) := by
      intro u hu hle
      have h2u : (2*u : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hu.1], by linarith⟩
      rw [Path.extend_apply _ hu, Path.extend_apply _ h2u, Path.trans_apply]
      have hcond : ((⟨u, hu⟩ : unitInterval) : ℝ) ≤ 1/2 := hle
      rw [dif_pos hcond]
    have htrans_gt : ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 → ¬(u ≤ 1/2) →
        ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend u =
          ρpath.extend (2*u - 1) := by
      intro u hu hgt
      have h2u : (2*u - 1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · linarith [not_le.mp hgt]
        · linarith [hu.2]
      rw [Path.extend_apply _ hu, Path.extend_apply _ h2u, Path.trans_apply]
      have hcond : ¬(((⟨u, hu⟩ : unitInterval) : ℝ) ≤ 1/2) := hgt
      rw [dif_neg hcond]
    -- glued continuation along the concatenated path
    have hICτ : IsCont (fun u => ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend u)
        1 (fun u => if u ≤ 1/2 then ΦF q (2*u) else ΦF q 1) := by
      obtain ⟨hΦqa, hΦq0, hΦqc⟩ := (hIC _ _ _).mp (hΦF q)
      rw [hIC]
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        by_cases hth : t ≤ 1/2
        · rw [if_pos hth, htrans_le t ht hth]
          exact hΦqa (2*t) ⟨by linarith [ht.1], by linarith⟩
        · rw [if_neg hth, htrans_gt t ht hth]
          have hmem : ρpath.extend (2*t - 1) ∈ W := by
            refine hρW (2*t - 1) ⟨?_, ?_⟩
            · linarith [not_le.mp hth]
            · linarith [ht.2]
          filter_upwards [hWo.mem_nhds hmem] with y hy using (hWall y hy).1
      · have h012 : (0:ℝ) ≤ 1/2 := by norm_num
        rw [if_pos h012]
        have h20 : (2:ℝ) * 0 = 0 := by norm_num
        rw [h20]
        exact hΦq0
      · intro t ht
        rcases lt_trichotomy t (1/2 : ℝ) with hth | hth | hth
        · obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦqc (2*t) ⟨by linarith [ht.1], by linarith⟩
          refine ⟨min (ε₁/2) (1/2 - t), lt_min (by linarith) (by linarith), ?_⟩
          intro u hu huε
          rw [lt_min_iff] at huε
          have huh : u ≤ 1/2 := by
            have h6 := abs_sub_lt_iff.mp huε.2
            linarith [h6.1]
          have hu2 : |2*u - 2*t| < ε₁ := by
            have h6 := abs_sub_lt_iff.mp huε.1
            rw [abs_sub_lt_iff]
            constructor <;> linarith [h6.1, h6.2]
          rw [if_pos huh, if_pos hth.le, htrans_le u hu huh]
          exact hε₁p (2*u) ⟨by linarith [hu.1], by linarith⟩ hu2
        · obtain ⟨ε₁, hε₁0, hε₁p⟩ := hΦqc 1 ⟨zero_le_one, le_refl 1⟩
          refine ⟨ε₁/2, by linarith, ?_⟩
          intro u hu huε
          have h2t : (2:ℝ)*t = 1 := by rw [hth]; norm_num
          by_cases huh : u ≤ 1/2
          · rw [if_pos huh, if_pos hth.le, h2t, htrans_le u hu huh]
            have hu2 : |2*u - 1| < ε₁ := by
              have h6 := abs_sub_lt_iff.mp huε
              rw [abs_sub_lt_iff]
              constructor <;> linarith [h6.1, h6.2]
            exact hε₁p (2*u) ⟨by linarith [hu.1], by linarith⟩ hu2
          · rw [if_neg huh, if_pos hth.le, h2t]
        · refine ⟨t - 1/2, by linarith, ?_⟩
          intro u hu huε
          have huh : ¬(u ≤ 1/2) := by
            rw [abs_sub_lt_iff] at huε
            rw [not_le]
            linarith [huε.2]
          rw [if_neg huh, if_neg (not_le.mpr hth)]
    -- the homotopy between the chosen path of q' and the concatenation
    obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic
      (PathConnectedSpace.somePath p₁ q') ((PathConnectedSpace.somePath p₁ q).trans ρpath)
    obtain ⟨η, hηeq⟩ : ∃ η' : ℝ × ℝ → M, η' = fun p =>
        H (Set.projIcc 0 1 zero_le_one p.1, Set.projIcc 0 1 zero_le_one p.2) := ⟨_, rfl⟩
    have happ : ∀ a b : ℝ, η (a, b) =
        H (Set.projIcc 0 1 zero_le_one a, Set.projIcc 0 1 zero_le_one b) := by
      intro a b
      rw [hηeq]
    have h0I : Set.projIcc (0:ℝ) 1 zero_le_one (0:ℝ) = (0 : unitInterval) := by
      apply Subtype.ext
      rw [Set.coe_projIcc]
      have h1 : ((0 : unitInterval) : ℝ) = 0 := rfl
      rw [h1]
      norm_num
    have h1I : Set.projIcc (0:ℝ) 1 zero_le_one (1:ℝ) = (1 : unitInterval) := by
      apply Subtype.ext
      rw [Set.coe_projIcc]
      have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
      rw [h1]
      norm_num
    have hηc : Continuous η := by
      rw [hηeq]
      exact H.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
        (continuous_projIcc.comp continuous_snd))
    have hbdry0 : ∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 0) = p₁ := by
      intro s hs
      rw [happ, h0I]
      exact Path.Homotopy.source H _
    have hbdry1 : ∀ s ∈ Set.Icc (0:ℝ) 1, η (s, 1) = η (0, 1) := by
      intro s hs
      rw [happ s 1, happ 0 1, h1I]
      rw [Path.Homotopy.target, Path.Homotopy.target]
    have hη01 : η (0, 1) = q' := by
      rw [happ 0 1, h1I]
      exact Path.Homotopy.target H _
    have hpath0 : (fun t : ℝ => η (0, t)) =
        (fun t : ℝ => (PathConnectedSpace.somePath p₁ q').extend t) := by
      funext t
      rw [happ, h0I]
      exact ContinuousMap.HomotopyWith.apply_zero H (Set.projIcc 0 1 zero_le_one t)
    have hpath1 : (fun t : ℝ => η (1, t)) =
        (fun t : ℝ => ((PathConnectedSpace.somePath p₁ q).trans ρpath).extend t) := by
      funext t
      rw [happ, h1I]
      exact ContinuousMap.HomotopyWith.apply_one H (Set.projIcc 0 1 zero_le_one t)
    have hIC0 : IsCont (fun t => η (0, t)) 1 (ΦF q') := by
      rw [hpath0]
      exact hΦF q'
    have hIC1 : IsCont (fun t => η (1, t)) 1
        (fun u => if u ≤ 1/2 then ΦF q (2*u) else ΦF q 1) := by
      rw [hpath1]
      exact hICτ
    have hfinal := hhomo η hηc hbdry0 hbdry1 (ΦF q')
      (fun u => if u ≤ 1/2 then ΦF q (2*u) else ΦF q 1) hIC0 hIC1
    rw [hη01] at hfinal
    have hn12 : ¬((1:ℝ) ≤ 1/2) := by norm_num
    have hval1 : (fun u => if u ≤ (1:ℝ)/2 then ΦF q (2*u) else ΦF q 1) 1 = ΦF q 1 :=
      if_neg hn12
    rw [hval1] at hfinal
    exact hfinal.symm
  -- the global map and its four properties
  refine ⟨fun q => ΦF q 1 q, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨B, hBo, hqB, hBloc⟩ := hlocal q
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ΦF q 1) q := by
      have h2 := (hQq q).1
      rw [hQ] at h2
      exact h2.1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hBo.mem_nhds hqB] with q'' hq''
    exact (hBloc q'' hq'').eq_of_nhds
  · have h2 := (hQq p₁).1
    rw [hQ] at h2
    exact h2.2.2.1 rfl
  · have h2 := (hQq p₂).1
    rw [hQ] at h2
    exact h2.2.2.2 rfl
  · intro x hx1 hx2
    have h2 := (hQq x).1
    rw [hQ] at h2
    exact h2.2.1 hx1 hx2

/-- **Injectivity of the dipole map**, by the Blaschke comparison against the
extremal property of the piece Green's functions. -/
theorem injective_bipolar_map [SimplyConnectedSpace M]
    [SecondCountableTopology M] (hnon : ∀ p₀ : M, ¬ HasGreenFunction p₀)
    {p₁ p₂ : M} (hne : p₁ ≠ p₂) {G : M → ℝ} {φ : M → ℂ̂}
    (hpole₁ : ∃ r > 0, ball (chartAt ℂ p₁ p₁) r ⊆ (chartAt ℂ p₁).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₁ p₁) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₁ p₁) r \ {chartAt ℂ p₁ p₁},
          h w = G ((chartAt ℂ p₁).symm w) + Real.log ‖w - chartAt ℂ p₁ p₁‖)
    (hpole₂ : ∃ r > 0, ball (chartAt ℂ p₂ p₂) r ⊆ (chartAt ℂ p₂).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₂ p₂) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₂ p₂) r \ {chartAt ℂ p₂ p₂},
          h w = G ((chartAt ℂ p₂).symm w) - Real.log ‖w - chartAt ℂ p₂ p₂‖)
    (hbdd : ∃ C, ∃ V₁ ∈ 𝓝 p₁, ∃ V₂ ∈ 𝓝 p₂, IsCompact (closure V₁) ∧
      IsCompact (closure V₂) ∧ ∀ x ∉ V₁ ∪ V₂, |G x| ≤ C)
    (hφ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ) (h₁ : φ p₁ = ((0 : ℂ) : ℂ̂))
    (h₂ : φ p₂ = OnePoint.infty)
    (habs : ∀ x, x ≠ p₁ → x ≠ p₂ →
      ∃ w : ℂ, φ x = (w : ℂ̂) ∧ ‖w‖ = Real.exp (-(G x))) :
    Function.Injective φ := by
  classical
  /- ## Generic brick: `ContMDiffAt` from an analytic source-chart reading. -/
  have hbuild : ∀ (f : M → ℂ) (x : M),
      AnalyticAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
    intro f x hf
    have hb1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
        :=
      contMDiffAt_iff_contDiffAt.mpr hf.contDiffAt
    have hb2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x)) x :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_source ℂ x)
    refine (hb1.comp x hb2).congr_of_eventuallyEq ?_
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]
  /- ## Generic brick: reading a sphere-valued map through a target chart. -/
  have hread : ∀ f : M → ℂ̂, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ∀ e : OpenPartialHomeomorph ℂ̂ ℂ, e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ →
      ∀ (x : M) (w : ℂ), w ∈ (chartAt ℂ x).target →
      f ((chartAt ℂ x).symm w) ∈ e.source →
      AnalyticAt ℂ (fun v => e (f ((chartAt ℂ x).symm v))) w := by
    intro f hf e hemax x w hw hsrc
    have hr1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) w :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hw
    have hr3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (f ((chartAt ℂ x).symm w)) :=
      contMDiffAt_of_mem_maximalAtlas hemax hsrc
    exact (contMDiffAt_iff_contDiffAt.mp
      ((hr3.comp _ hf.contMDiffAt).comp w hr1)).analyticAt
  /- ## Sphere-chart bookkeeping. -/
  have hfinmax : sphereChartFinite ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.chart_mem_maximalAtlas ((0 : ℂ) : ℂ̂)
  have hinfmax : sphereChartInfty ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
    IsManifold.chart_mem_maximalAtlas (OnePoint.infty : ℂ̂)
  have hfinsrc : ∀ z : ℂ̂, z ≠ OnePoint.infty → z ∈ sphereChartFinite.source := by
    intro z hz
    rw [sphereChartFinite_source]
    exact hz
  have hinfsrc : ∀ z : ℂ̂, z ≠ ((0 : ℂ) : ℂ̂) → z ∈ sphereChartInfty.source := by
    intro z hz
    rw [sphereChartInfty_source]
    exact hz
  have hinfval : ∀ b : ℂ, b ≠ 0 → sphereChartInfty ((b : ℂ̂)) = b⁻¹ := by
    intro b hb
    rw [sphereChartInfty_apply, inversionGL_smul_coe, if_neg hb, sphereChartFinite_coe]
  have hinfval0 : sphereChartInfty (OnePoint.infty : ℂ̂) = 0 := by
    rw [sphereChartInfty_apply, inversionGL_smul_infty, sphereChartFinite_coe]
  /- ## Plane-level transfer of subharmonicity along a pointwise equality. -/
  have htransfer : ∀ (F₁ F₂ : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F₁ U → W ⊆ U
      →
      Set.EqOn F₁ F₂ W → SubharmonicOn F₂ W := by
    intro F₁ F₂ U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro c hc ρc hρc hb
    have ht1 : F₂ c = F₁ c := (hFG hc).symm
    have ht2 : Real.circleAverage F₁ c ρc = Real.circleAverage F₂ c ρc := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρc] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [ht1, ← ht2]
    exact hF.2 c (hWU hc) ρc hρc (hb.trans hWU)
  /- ## Surface-level: subharmonicity at a point respects equality near the point. -/
  have hcongM : ∀ (F₁ F₂ : M → ℝ) (x : M) (O : Set M), IsOpen O → x ∈ O →
      Set.EqOn F₁ F₂ O → MSubharmonicAt F₁ x → MSubharmonicAt F₂ x := by
    intro F₁ F₂ x O hO hxO hFG hF
    obtain ⟨r, hr, -, hsub⟩ := hF
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hO
    have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O := by
      refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
      exact hxO
    obtain ⟨ρc, hρc, hρsubc⟩ := Metric.isOpen_iff.1 (isOpen_ball.inter hopen)
      (chartAt ℂ x x) ⟨mem_ball_self hr, hmem⟩
    refine ⟨ρc, hρc, fun w hw => ((hρsubc hw).2).1, ?_⟩
    refine htransfer _ _ _ _ hsub (fun w hw => (hρsubc hw).1) ?_
    intro w hw
    exact hFG ((hρsubc hw).2).2
  /- ## Sums of subharmonic functions are subharmonic. -/
  have haddM : ∀ (F₁ F₂ : M → ℝ) (x : M), MSubharmonicAt F₁ x → MSubharmonicAt F₂ x
      →
      MSubharmonicAt (fun y => F₁ y + F₂ y) x := by
    intro F₁ F₂ x hF hG2
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hF
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hG2
    have hmono : ∀ (f : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn f U → V ⊆ U →
        SubharmonicOn f V := fun f U V hf hVU =>
      ⟨hf.1.mono hVU, fun c hc ρc hρc hball => hf.2 c (hVU hc) ρc hρc (hball.trans hVU)⟩
    have hs₁' := hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂))
    have hs₂' := hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂))
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_, ?_⟩
    · exact hs₁'.1.add hs₂'.1
    · intro c hc ρc hρc hb
      have hsph : sphere c ρc ⊆ ball (chartAt ℂ x x) (min r₁ r₂) :=
        sphere_subset_closedBall.trans hb
      have hci₁ : CircleIntegrable (F₁ ∘ (chartAt ℂ x).symm) c ρc :=
        (hs₁'.1.mono hsph).circleIntegrable hρc.le
      have hci₂ : CircleIntegrable (F₂ ∘ (chartAt ℂ x).symm) c ρc :=
        (hs₂'.1.mono hsph).circleIntegrable hρc.le
      have havg := Real.circleAverage_fun_add hci₁ hci₂
      have hp₁' := hs₁'.2 c hc ρc hρc hb
      have hp₂' := hs₂'.2 c hc ρc hρc hb
      calc ((fun y => F₁ y + F₂ y) ∘ (chartAt ℂ x).symm) c
          = (F₁ ∘ (chartAt ℂ x).symm) c + (F₂ ∘ (chartAt ℂ x).symm) c := rfl
        _ ≤ Real.circleAverage (F₁ ∘ (chartAt ℂ x).symm) c ρc
            + Real.circleAverage (F₂ ∘ (chartAt ℂ x).symm) c ρc := add_le_add hp₁' hp₂'
        _ = Real.circleAverage
            (fun w => (F₁ ∘ (chartAt ℂ x).symm) w + (F₂ ∘ (chartAt ℂ x).symm) w) c ρc
                :=
            havg.symm
        _ = Real.circleAverage ((fun y => F₁ y + F₂ y) ∘ (chartAt ℂ x).symm) c ρc := rfl
  /- ## The log-modulus of a nonvanishing holomorphic function is harmonic. -/
  have hlogM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      Ψ x ≠ 0 →
      MHarmonicAt (fun y => Real.log ‖Ψ y‖) x := by
    intro Ψ hΨm x hx
    have hl1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have hl2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) hl1
    have hl3 : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_iff_contDiffAt.mp hl2).analyticAt
    have hl4 : (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hx
    exact hl3.harmonicAt_log_norm hl4
  /- ## The chart reading of a holomorphic function is analytic at the center. -/
  have hreadM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
    intro Ψ hΨm x
    have hm1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have hm2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) hm1
    exact (contMDiffAt_iff_contDiffAt.mp hm2).analyticAt
  /- ## The singleton `{0}` is not open in the plane. -/
  have hnotopen0 : ¬ IsOpen ({(0 : ℂ)} : Set ℂ) := by
    intro hcon
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcon 0 rfl
    have hn1 : (↑(ε / 2) : ℂ) ∈ ball (0 : ℂ) ε := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have hn2 := hball hn1
    rw [Set.mem_singleton_iff, Complex.ofReal_eq_zero] at hn2
    linarith
  /- ## Zeros of a nonconstant holomorphic function are isolated. -/
  have hisoM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → (∃ y₀,
      Ψ y₀ ≠ 0) →
      ∀ z : M, Ψ z = 0 → ∀ᶠ y in 𝓝[≠] z, Ψ y ≠ 0 := by
    intro Ψ hΨm hex z hz
    obtain ⟨y₀, hy₀⟩ := hex
    have hzsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    rcases (hreadM Ψ hΨm z).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      have hop : IsOpenMap Ψ := by
        refine isOpenMap_of_contMDiff_of_not_const (fun y => hΨm y) ?_
        rintro ⟨c, hc⟩
        rw [hc z] at hz
        rw [hc y₀, hz] at hy₀
        exact hy₀ rfl
      have hi2 : ∀ᶠ y in 𝓝 z, Ψ y = 0 := by
        have hc : ContinuousAt (chartAt ℂ z) z := (chartAt ℂ z).continuousAt hzsrc
        filter_upwards [hc.eventually hcase,
          (chartAt ℂ z).open_source.mem_nhds hzsrc] with y h1y hsy
        have hyy : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := h1y
        rwa [(chartAt ℂ z).left_inv hsy] at hyy
      obtain ⟨O, hOsub, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp hi2
      have himg : Ψ '' O = {0} := by
        apply Set.Subset.antisymm
        · rintro w ⟨y, hy, rfl⟩
          exact hOsub hy
        · rintro w hw
          rw [Set.mem_singleton_iff] at hw
          exact ⟨z, hzO, by rw [hw, hz]⟩
      have hi3 := hop O hOopen
      rw [himg] at hi3
      exact hnotopen0 hi3
    · have htend : Tendsto (chartAt ℂ z) (𝓝[≠] z) (𝓝[≠] (chartAt ℂ z z)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · exact ((chartAt ℂ z).continuousAt hzsrc).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ z).open_source.mem_nhds hzsrc),
            self_mem_nhdsWithin] with y hys hyz
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hyz ((chartAt ℂ z).injOn hys hzsrc hcon)
      filter_upwards [htend.eventually hcase,
        nhdsWithin_le_nhds ((chartAt ℂ z).open_source.mem_nhds hzsrc)] with y h1 hys
      intro hcon
      apply h1
      have hyy : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := by
        rw [(chartAt ℂ z).left_inv hys]
        exact hcon
      exact hyy
  /- ## dslope toolkit: evaluation, punctured differentiability, nonvanishing. -/
  have hdslope_eval : ∀ (F : ℂ → ℂ) (c w : ℂ), F c = 0 → w ≠ c →
      dslope F c w = F w / (w - c) := by
    intro F c w hFc hwc
    rw [dslope_of_ne F hwc, slope_def_field, hFc, sub_zero]
  have hdslope_diff : ∀ (F : ℂ → ℂ) (c w : ℂ), F c = 0 → w ≠ c → AnalyticAt ℂ F w
      →
      DifferentiableAt ℂ (dslope F c) w := by
    intro F c w hFc hwc hFan
    have hEq : (fun v => F v / (v - c)) =ᶠ[𝓝 w] dslope F c := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hwc)] with v hv
      have hvc : v ≠ c := Set.mem_compl_singleton_iff.mp hv
      rw [dslope_of_ne F hvc, slope_def_field, hFc, sub_zero]
    have hq : DifferentiableAt ℂ (fun v => F v / (v - c)) w :=
      DifferentiableAt.div hFan.differentiableAt
        (differentiableAt_id.sub (differentiableAt_const c)) (sub_ne_zero_of_ne hwc)
    exact hq.congr_of_eventuallyEq hEq.symm
  have hdslope_ne : ∀ (F : ℂ → ℂ) (c w : ℂ), F c = 0 → w ≠ c → F w ≠ 0 →
      dslope F c w ≠ 0 := by
    intro F c w hFc hwc hFw
    rw [hdslope_eval F c w hFc hwc]
    exact div_ne_zero hFw (sub_ne_zero_of_ne hwc)
  /- ## A zero whose modulus is exactly first order has nonzero derivative. -/
  have hderiv_ne : ∀ (F : ℂ → ℂ) (c : ℂ) (rF : ℝ) (hF : ℂ → ℝ), 0 < rF → F c = 0
      →
      (∀ w ∈ ball c rF, AnalyticAt ℂ F w) → ContinuousAt hF c →
      (∀ w ∈ ball c rF, w ≠ c → ‖F w‖ = Real.exp (hF w) * ‖w - c‖) →
      deriv F c ≠ 0 := by
    intro F c rF hF hrF hFc hFan hhc hFnorm hd0
    have hdiff : DifferentiableAt ℂ F c := (hFan c (mem_ball_self hrF)).differentiableAt
    have hcont : ContinuousAt (dslope F c) c := continuousAt_dslope_same.mpr hdiff
    have hT1 : Tendsto (fun w => ‖dslope F c w‖) (𝓝[≠] c) (𝓝 0) := by
      have hu1 : Tendsto (dslope F c) (𝓝 c) (𝓝 (dslope F c c)) := hcont
      rw [dslope_same, hd0] at hu1
      have hu2 := hu1.norm
      rw [norm_zero] at hu2
      exact hu2.mono_left nhdsWithin_le_nhds
    have hT2 : Tendsto (fun w => Real.exp (hF w)) (𝓝[≠] c) (𝓝 (Real.exp (hF c))) :=
      Filter.Tendsto.mono_left (Real.continuous_exp.continuousAt.comp hhc)
        nhdsWithin_le_nhds
    have hEq : (fun w => ‖dslope F c w‖) =ᶠ[𝓝[≠] c] fun w => Real.exp (hF w) := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c hrF), self_mem_nhdsWithin]
        with w hwb hwm
      have hwc : w ≠ c := Set.mem_compl_singleton_iff.mp hwm
      rw [dslope_of_ne F hwc, slope_def_field, hFc, sub_zero, norm_div,
        hFnorm w hwb hwc, mul_div_assoc,
        div_self (norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hwc)), mul_one]
    have hun := tendsto_nhds_unique (hT1.congr' hEq) hT2
    exact (Real.exp_pos (hF c)).ne' hun.symm
  /- ## The special values `0` and `∞` are attained only at the poles. -/
  have hzero : ∀ x : M, φ x = ((0 : ℂ) : ℂ̂) → x = p₁ := by
    intro x hx
    by_contra hxp₁
    by_cases hxp₂ : x = p₂
    · rw [hxp₂, h₂] at hx
      exact OnePoint.infty_ne_coe 0 hx
    · obtain ⟨w, hw, hwn⟩ := habs x hxp₁ hxp₂
      rw [hx] at hw
      have hw0 : (0 : ℂ) = w := OnePoint.coe_eq_coe.mp hw
      rw [← hw0, norm_zero] at hwn
      exact (Real.exp_pos _).ne' hwn.symm
  have hinfty : ∀ x : M, φ x = OnePoint.infty → x = p₂ := by
    intro x hx
    by_contra hxp₂
    by_cases hxp₁ : x = p₁
    · rw [hxp₁, h₁] at hx
      exact OnePoint.coe_ne_infty 0 hx
    · obtain ⟨w, hw, -⟩ := habs x hxp₁ hxp₂
      rw [hx] at hw
      exact OnePoint.infty_ne_coe w hw
  /- ## Fix a collision and dispose of the pole values. -/
  intro q q' hcol
  by_contra hqq'
  by_cases hq0 : φ q = ((0 : ℂ) : ℂ̂)
  · have hcz : φ q' = ((0 : ℂ) : ℂ̂) := by rw [← hcol]; exact hq0
    exact hqq' ((hzero q hq0).trans (hzero q' hcz).symm)
  by_cases hqi : φ q = OnePoint.infty
  · have hci : φ q' = OnePoint.infty := by rw [← hcol]; exact hqi
    exact hqq' ((hinfty q hqi).trans (hinfty q' hci).symm)
  have hqp₁ : q ≠ p₁ := fun h => hq0 (by rw [h, h₁])
  have hqp₂ : q ≠ p₂ := fun h => hqi (by rw [h, h₂])
  obtain ⟨w₀, hφq, hw₀n⟩ := habs q hqp₁ hqp₂
  have hw₀0 : w₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw₀n
    exact (Real.exp_pos _).ne' hw₀n.symm
  have hφq' : φ q' = (w₀ : ℂ̂) := by rw [← hcol]; exact hφq
  have hq'p₁ : q' ≠ p₁ := by
    intro h
    rw [h, h₁] at hφq'
    exact hw₀0 (OnePoint.coe_eq_coe.mp hφq'.symm)
  have hq'p₂ : q' ≠ p₂ := by
    intro h
    rw [h, h₂] at hφq'
    exact OnePoint.infty_ne_coe w₀ hφq'
  /- ## A fresh coordinate disk centered at `p₁` avoiding `q'` and `p₂`. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₁ with he₀def
  have hp₁src : p₁ ∈ e₀.source := mem_chart_source ℂ p₁
  have hUopen : IsOpen (e₀.target ∩ ⇑e₀.symm ⁻¹' ({q'}ᶜ ∩ {p₂}ᶜ)) :=
    e₀.isOpen_inter_preimage_symm (isOpen_compl_singleton.inter isOpen_compl_singleton)
  have hp₁U : e₀ p₁ ∈ e₀.target ∩ ⇑e₀.symm ⁻¹' ({q'}ᶜ ∩ {p₂}ᶜ) := by
    refine ⟨e₀.map_source hp₁src, ?_⟩
    rw [Set.mem_preimage, e₀.left_inv hp₁src]
    exact ⟨Set.mem_compl_singleton_iff.mpr hq'p₁.symm,
      Set.mem_compl_singleton_iff.mpr hne⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hUopen _ hp₁U
  have hra0 : (0 : ℝ) < εa / 2 := half_pos hεa
  have hrsub : closedBall (e₀ p₁) (εa / 2) ⊆ e₀.target ∩ ⇑e₀.symm ⁻¹' ({q'}ᶜ ∩
      {p₂}ᶜ) :=
    (Metric.closedBall_subset_ball (half_lt_self hεa)).trans hballa
  set D₀ : CoordDisk M := ⟨p₁, εa / 2, hra0, fun w hw => (hrsub hw).1⟩ with hD₀def
  have hD₀avoid : ∀ y ∈ D₀.closedCarrier, y ≠ q' ∧ y ≠ p₂ := by
    rintro y ⟨w, hw, rfl⟩
    have hav := (hrsub hw).2
    rw [Set.mem_preimage] at hav
    exact ⟨Set.mem_compl_singleton_iff.mp hav.1, Set.mem_compl_singleton_iff.mp hav.2⟩
  have hq'D : q' ∉ D₀.closedCarrier := fun hmem => (hD₀avoid q' hmem).1 rfl
  have hp₂D : p₂ ∉ D₀.closedCarrier := fun hmem => (hD₀avoid p₂ hmem).2 rfl
  /- ## The second dipole at the pole pair `(q', p₂)`. -/
  obtain ⟨G', hG'h, hpole₁', hpole₂', hbdd'⟩ := exists_bipolarGreen D₀ hq'D hp₂D hq'p₂
  obtain ⟨φ', hφ', hφ'z, hφ'i, habs'⟩ := exists_bipolar_map hq'p₂ hG'h hpole₁' hpole₂'
  have hinfty' : ∀ x : M, φ' x = OnePoint.infty → x = p₂ := by
    intro x hx
    by_contra hxp₂
    by_cases hxq' : x = q'
    · rw [hxq', hφ'z] at hx
      exact OnePoint.coe_ne_infty 0 hx
    · obtain ⟨u, hu, -⟩ := habs' x hxq' hxp₂
      rw [hx] at hu
      exact OnePoint.infty_ne_coe u hu
  have hφdat : ∀ x : M, x ≠ p₁ → x ≠ p₂ → ∃ u : ℂ, φ x = (u : ℂ̂) ∧ u ≠ 0
      ∧
      ‖u‖ = Real.exp (-(G x)) := by
    intro x hx1 hx2
    obtain ⟨u, hu, hun⟩ := habs x hx1 hx2
    refine ⟨u, hu, ?_, hun⟩
    intro h
    rw [h, norm_zero] at hun
    exact (Real.exp_pos _).ne' hun.symm
  have hφ'dat : ∀ x : M, x ≠ q' → x ≠ p₂ → ∃ u : ℂ, φ' x = (u : ℂ̂) ∧ u ≠ 0
      ∧
      ‖u‖ = Real.exp (-(G' x)) := by
    intro x hx1 hx2
    obtain ⟨u, hu, hun⟩ := habs' x hx1 hx2
    refine ⟨u, hu, ?_, hun⟩
    intro h
    rw [h, norm_zero] at hun
    exact (Real.exp_pos _).ne' hun.symm
  /- ## Chart notation at the two singular points of the ratio. -/
  set χ₁ : OpenPartialHomeomorph M ℂ := chartAt ℂ q' with hχ₁def
  have hq'src : q' ∈ χ₁.source := mem_chart_source ℂ q'
  set c₁ : ℂ := χ₁ q' with hc₁def
  have hsymmc₁ : χ₁.symm c₁ = q' := χ₁.left_inv hq'src
  set χ₂ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₂ with hχ₂def
  have hp₂src : p₂ ∈ χ₂.source := mem_chart_source ℂ p₂
  set c₂ : ℂ := χ₂ p₂ with hc₂def
  have hsymmc₂ : χ₂.symm c₂ = p₂ := χ₂.left_inv hp₂src
  obtain ⟨r₁, hr₁pos, hr₁sub, ηq, hηqharm, hηqval⟩ := hpole₁'
  obtain ⟨s₁, hs₁pos, hs₁sub, ηp, hηpharm, hηpval⟩ := hpole₂
  /- ## The finite-part ratio `H = (φ − w₀)/φ'` with its removable values. -/
  obtain ⟨g, hgdef⟩ : ∃ f : ℂ → ℂ,
      f = fun w => sphereChartFinite (φ (χ₁.symm w)) - w₀ := ⟨_, rfl⟩
  obtain ⟨g', hg'def⟩ : ∃ f : ℂ → ℂ,
      f = fun w => sphereChartFinite (φ' (χ₁.symm w)) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ f : ℂ → ℂ,
      f = fun w => sphereChartInfty (φ (χ₂.symm w)) := ⟨_, rfl⟩
  obtain ⟨ρ', hρ'def⟩ : ∃ f : ℂ → ℂ,
      f = fun w => sphereChartInfty (φ' (χ₂.symm w)) := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ Hf : M → ℂ, Hf = fun x =>
      if x = q' then dslope g c₁ c₁ / dslope g' c₁ c₁
      else if x = p₂ then dslope ρ' c₂ c₂ / dslope ρ c₂ c₂
      else (sphereChartFinite (φ x) - w₀) / sphereChartFinite (φ' x) := ⟨_, rfl⟩
  /- ## The two decisive values of `H`. -/
  have hHq : H q = 0 := by
    simp only [hHdef]
    rw [if_neg hqq', if_neg hqp₂, hφq, sphereChartFinite_coe, sub_self, zero_div]
  have hHp₁ : H p₁ ≠ 0 := by
    obtain ⟨u', hu', hu'0, -⟩ := hφ'dat p₁ (Ne.symm hq'p₁) hne
    simp only [hHdef]
    rw [if_neg (Ne.symm hq'p₁), if_neg hne, h₁, sphereChartFinite_coe, hu',
      sphereChartFinite_coe, zero_sub]
    exact div_ne_zero (neg_ne_zero.mpr hw₀0) hu'0
  /- ## Holomorphy of `H` away from the two singular points. -/
  have hHsm_gen : ∀ x : M, x ≠ q' → x ≠ p₂ → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H x :=
      by
    intro x hx1 hx2
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hφfin : φ x ≠ OnePoint.infty := fun h => hx2 (hinfty x h)
    have hφ'fin : φ' x ≠ OnePoint.infty := fun h => hx2 (hinfty' x h)
    obtain ⟨u', hu', hu'0, -⟩ := hφ'dat x hx1 hx2
    have hT : IsOpen ((chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          ({q'}ᶜ ∩ {p₂}ᶜ))) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm
        (((sphereChartFinite.open_source.preimage hφ.continuous).inter
          (sphereChartFinite.open_source.preimage hφ'.continuous)).inter
          (isOpen_compl_singleton.inter isOpen_compl_singleton))
    have hxT : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          ({q'}ᶜ ∩ {p₂}ᶜ)) := by
      refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
      exact ⟨⟨hfinsrc _ hφfin, hfinsrc _ hφ'fin⟩,
        Set.mem_compl_singleton_iff.mpr hx1, Set.mem_compl_singleton_iff.mpr hx2⟩
    obtain ⟨R₀, hR₀def⟩ : ∃ f : ℂ → ℂ, f = fun v =>
        (sphereChartFinite (φ ((chartAt ℂ x).symm v)) - w₀) /
          sphereChartFinite (φ' ((chartAt ℂ x).symm v)) := ⟨_, rfl⟩
    have hnum : AnalyticAt ℂ (fun v => sphereChartFinite (φ ((chartAt ℂ x).symm v)))
        (chartAt ℂ x x) :=
      hread φ hφ sphereChartFinite hfinmax x _ ((chartAt ℂ x).map_source hxsrc)
        (by rw [(chartAt ℂ x).left_inv hxsrc]; exact hfinsrc _ hφfin)
    have hden : AnalyticAt ℂ (fun v => sphereChartFinite (φ' ((chartAt ℂ x).symm v)))
        (chartAt ℂ x x) :=
      hread φ' hφ' sphereChartFinite hfinmax x _ ((chartAt ℂ x).map_source hxsrc)
        (by rw [(chartAt ℂ x).left_inv hxsrc]; exact hfinsrc _ hφ'fin)
    have hden0 : sphereChartFinite (φ' ((chartAt ℂ x).symm (chartAt ℂ x x))) ≠ 0 := by
      rw [(chartAt ℂ x).left_inv hxsrc, hu', sphereChartFinite_coe]
      exact hu'0
    have hR₀an : AnalyticAt ℂ R₀ (chartAt ℂ x x) := by
      rw [hR₀def]
      exact (hnum.sub analyticAt_const).div hden hden0
    have hHeq : R₀ =ᶠ[𝓝 (chartAt ℂ x x)] H ∘ ⇑(chartAt ℂ x).symm := by
      filter_upwards [hT.mem_nhds hxT] with v hv
      have he1 : (chartAt ℂ x).symm v ≠ q' := Set.mem_compl_singleton_iff.mp hv.2.2.1
      have he2 : (chartAt ℂ x).symm v ≠ p₂ := Set.mem_compl_singleton_iff.mp hv.2.2.2
      simp only [hR₀def, Function.comp_apply, hHdef]
      rw [if_neg he1, if_neg he2]
    exact hbuild H x (hR₀an.congr hHeq)
  /- ## Holomorphy of `H` at `q'` (zero-over-zero removable singularity). -/
  have hHsm_q' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H q' := by
    have hOq' : IsOpen (χ₁.target ∩ ⇑χ₁.symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          {p₂}ᶜ)) :=
      χ₁.isOpen_inter_preimage_symm
        (((sphereChartFinite.open_source.preimage hφ.continuous).inter
          (sphereChartFinite.open_source.preimage hφ'.continuous)).inter
          isOpen_compl_singleton)
    have hc₁mem : c₁ ∈ χ₁.target ∩ ⇑χ₁.symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          {p₂}ᶜ) := by
      refine ⟨χ₁.map_source hq'src, ?_⟩
      rw [Set.mem_preimage, hsymmc₁]
      refine ⟨⟨hfinsrc _ ?_, hfinsrc _ ?_⟩, Set.mem_compl_singleton_iff.mpr hq'p₂⟩
      · rw [hφq']
        exact OnePoint.coe_ne_infty w₀
      · rw [hφ'z]
        exact OnePoint.coe_ne_infty 0
    obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp hOq' _ hc₁mem
    set r : ℝ := min r₁ r₂ with hrdef
    have hr : 0 < r := lt_min hr₁pos hr₂pos
    have hrb₁ : ball c₁ r ⊆ ball c₁ r₁ := ball_subset_ball (min_le_left _ _)
    have hrb₂ : ball c₁ r ⊆ χ₁.target ∩ ⇑χ₁.symm ⁻¹'
        ((φ ⁻¹' sphereChartFinite.source ∩ φ' ⁻¹' sphereChartFinite.source) ∩
          {p₂}ᶜ) := (ball_subset_ball (min_le_right _ _)).trans hr₂sub
    have hgan : ∀ w ∈ ball c₁ r, AnalyticAt ℂ g w := by
      intro w hw
      have h1 := hread φ hφ sphereChartFinite hfinmax q' w (hrb₂ hw).1 (hrb₂ hw).2.1.1
      simp only [hgdef]
      exact h1.sub analyticAt_const
    have hg'an : ∀ w ∈ ball c₁ r, AnalyticAt ℂ g' w := by
      intro w hw
      have h1 := hread φ' hφ' sphereChartFinite hfinmax q' w (hrb₂ hw).1 (hrb₂ hw).2.1.2
      simp only [hg'def]
      exact h1
    have hg0 : g c₁ = 0 := by
      simp only [hgdef]
      rw [hsymmc₁, hφq', sphereChartFinite_coe, sub_self]
    have hg'0 : g' c₁ = 0 := by
      simp only [hg'def]
      rw [hsymmc₁, hφ'z, sphereChartFinite_coe]
    have hsymm_ne₁ : ∀ w ∈ ball c₁ r, w ≠ c₁ → χ₁.symm w ≠ q' := by
      intro w hw hwc h
      have hwt : w ∈ χ₁.target := (hrb₂ hw).1
      have h2 : χ₁ (χ₁.symm w) = w := χ₁.right_inv hwt
      rw [h] at h2
      exact hwc h2.symm
    have hg'dat : ∀ w ∈ ball c₁ r, w ≠ c₁ →
        g' w ≠ 0 ∧ ‖g' w‖ = Real.exp (-(ηq w)) * ‖w - c₁‖ := by
      intro w hw hwc
      have hnq' : χ₁.symm w ≠ q' := hsymm_ne₁ w hw hwc
      have hnp₂ : χ₁.symm w ≠ p₂ := Set.mem_compl_singleton_iff.mp (hrb₂ hw).2.2
      obtain ⟨u, hu, hu0, hun⟩ := hφ'dat (χ₁.symm w) hnq' hnp₂
      have hval : g' w = u := by
        simp only [hg'def]
        rw [hu, sphereChartFinite_coe]
      have hballm : w ∈ ball c₁ r₁ \ {c₁} :=
        ⟨hrb₁ hw, fun h => hwc (Set.mem_singleton_iff.mp h)⟩
      have hη := hηqval w hballm
      have hGval : -(G' (χ₁.symm w)) = -(ηq w) + Real.log ‖w - c₁‖ := by linarith
      have hpos : 0 < ‖w - c₁‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hwc)
      refine ⟨by rw [hval]; exact hu0, ?_⟩
      rw [hval, hun, hGval, Real.exp_add, Real.exp_log hpos]
    have hg'deriv : deriv g' c₁ ≠ 0 := by
      refine hderiv_ne g' c₁ r (fun w => -(ηq w)) hr hg'0 hg'an ?_
        (fun w hw hwc => (hg'dat w hw hwc).2)
      exact (hηqharm c₁ (mem_ball_self hr₁pos)).1.continuousAt.neg
    obtain ⟨A₁, hA₁def⟩ : ∃ f : ℂ → ℂ,
        f = fun w => dslope g c₁ w / dslope g' c₁ w := ⟨_, rfl⟩
    have hA₁cont : ContinuousAt A₁ c₁ := by
      have hc1 : ContinuousAt (dslope g c₁) c₁ :=
        continuousAt_dslope_same.mpr (hgan c₁ (mem_ball_self hr)).differentiableAt
      have hc2 : ContinuousAt (dslope g' c₁) c₁ :=
        continuousAt_dslope_same.mpr (hg'an c₁ (mem_ball_self hr)).differentiableAt
      have hc3 : dslope g' c₁ c₁ ≠ 0 := by
        rw [dslope_same]
        exact hg'deriv
      simp only [hA₁def]
      exact hc1.div hc2 hc3
    have hA₁diff : ∀ᶠ w in 𝓝[≠] c₁, DifferentiableAt ℂ A₁ w := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c₁ hr), self_mem_nhdsWithin]
        with w hwb hwm
      have hwc : w ≠ c₁ := Set.mem_compl_singleton_iff.mp hwm
      have hd1 := hdslope_diff g c₁ w hg0 hwc (hgan w hwb)
      have hd2 := hdslope_diff g' c₁ w hg'0 hwc (hg'an w hwb)
      have hd3 : dslope g' c₁ w ≠ 0 :=
        hdslope_ne g' c₁ w hg'0 hwc (hg'dat w hwb hwc).1
      simp only [hA₁def]
      exact hd1.div hd2 hd3
    have hA₁an : AnalyticAt ℂ A₁ c₁ :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        hA₁diff hA₁cont
    have hHq'eq : A₁ =ᶠ[𝓝 c₁] H ∘ ⇑χ₁.symm := by
      filter_upwards [ball_mem_nhds c₁ hr] with w hwb
      by_cases hwc : w = c₁
      · subst hwc
        simp only [hA₁def, Function.comp_apply]
        rw [hsymmc₁]
        simp only [hHdef]
        rw [if_pos trivial]
      · have hnq' : χ₁.symm w ≠ q' := hsymm_ne₁ w hwb hwc
        have hnp₂ : χ₁.symm w ≠ p₂ := Set.mem_compl_singleton_iff.mp (hrb₂ hwb).2.2
        simp only [hA₁def, Function.comp_apply, hHdef]
        rw [if_neg hnq', if_neg hnp₂, hdslope_eval g c₁ w hg0 hwc,
          hdslope_eval g' c₁ w hg'0 hwc,
          div_div_div_cancel_right₀ (sub_ne_zero_of_ne hwc)]
        simp only [hgdef, hg'def]
    exact hbuild H q' (hA₁an.congr hHq'eq)
  /- ## Holomorphy of `H` at `p₂` (pole-over-pole removable singularity). -/
  have hHsm_p₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H p₂ := by
    have hOp₂ : IsOpen (χ₂.target ∩ ⇑χ₂.symm ⁻¹'
        ((φ ⁻¹' sphereChartInfty.source ∩ φ' ⁻¹' sphereChartInfty.source) ∩
          ({p₁}ᶜ ∩ {q'}ᶜ))) :=
      χ₂.isOpen_inter_preimage_symm
        (((sphereChartInfty.open_source.preimage hφ.continuous).inter
          (sphereChartInfty.open_source.preimage hφ'.continuous)).inter
          (isOpen_compl_singleton.inter isOpen_compl_singleton))
    have hc₂mem : c₂ ∈ χ₂.target ∩ ⇑χ₂.symm ⁻¹'
        ((φ ⁻¹' sphereChartInfty.source ∩ φ' ⁻¹' sphereChartInfty.source) ∩
          ({p₁}ᶜ ∩ {q'}ᶜ)) := by
      refine ⟨χ₂.map_source hp₂src, ?_⟩
      rw [Set.mem_preimage, hsymmc₂]
      refine ⟨⟨hinfsrc _ ?_, hinfsrc _ ?_⟩, Set.mem_compl_singleton_iff.mpr hne.symm,
        Set.mem_compl_singleton_iff.mpr (Ne.symm hq'p₂)⟩
      · rw [h₂]
        exact OnePoint.infty_ne_coe 0
      · rw [hφ'i]
        exact OnePoint.infty_ne_coe 0
    obtain ⟨s₂, hs₂pos, hs₂sub⟩ := Metric.isOpen_iff.mp hOp₂ _ hc₂mem
    set s : ℝ := min s₁ s₂ with hsdef
    have hs : 0 < s := lt_min hs₁pos hs₂pos
    have hsb₁ : ball c₂ s ⊆ ball c₂ s₁ := ball_subset_ball (min_le_left _ _)
    have hsb₂ : ball c₂ s ⊆ χ₂.target ∩ ⇑χ₂.symm ⁻¹'
        ((φ ⁻¹' sphereChartInfty.source ∩ φ' ⁻¹' sphereChartInfty.source) ∩
          ({p₁}ᶜ ∩ {q'}ᶜ)) := (ball_subset_ball (min_le_right _ _)).trans hs₂sub
    have hρan : ∀ w ∈ ball c₂ s, AnalyticAt ℂ ρ w := by
      intro w hw
      have h1 := hread φ hφ sphereChartInfty hinfmax p₂ w (hsb₂ hw).1 (hsb₂ hw).2.1.1
      simp only [hρdef]
      exact h1
    have hρ'an : ∀ w ∈ ball c₂ s, AnalyticAt ℂ ρ' w := by
      intro w hw
      have h1 := hread φ' hφ' sphereChartInfty hinfmax p₂ w (hsb₂ hw).1 (hsb₂ hw).2.1.2
      simp only [hρ'def]
      exact h1
    have hρ0 : ρ c₂ = 0 := by
      simp only [hρdef]
      rw [hsymmc₂, h₂, hinfval0]
    have hρ'0 : ρ' c₂ = 0 := by
      simp only [hρ'def]
      rw [hsymmc₂, hφ'i, hinfval0]
    have hsymm_ne₂ : ∀ w ∈ ball c₂ s, w ≠ c₂ → χ₂.symm w ≠ p₂ := by
      intro w hw hwc h
      have hwt : w ∈ χ₂.target := (hsb₂ hw).1
      have h2 : χ₂ (χ₂.symm w) = w := χ₂.right_inv hwt
      rw [h] at h2
      exact hwc h2.symm
    have hρdat : ∀ w ∈ ball c₂ s, w ≠ c₂ →
        ρ w ≠ 0 ∧ ‖ρ w‖ = Real.exp (ηp w) * ‖w - c₂‖ := by
      intro w hw hwc
      have hnp₁ : χ₂.symm w ≠ p₁ := Set.mem_compl_singleton_iff.mp (hsb₂ hw).2.2.1
      have hnp₂ : χ₂.symm w ≠ p₂ := hsymm_ne₂ w hw hwc
      obtain ⟨u, hu, hu0, hun⟩ := hφdat (χ₂.symm w) hnp₁ hnp₂
      have hval : ρ w = u⁻¹ := by
        simp only [hρdef]
        rw [hu, hinfval u hu0]
      have hballm : w ∈ ball c₂ s₁ \ {c₂} :=
        ⟨hsb₁ hw, fun h => hwc (Set.mem_singleton_iff.mp h)⟩
      have hη := hηpval w hballm
      have hpos : 0 < ‖w - c₂‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hwc)
      have hGx : G (χ₂.symm w) = ηp w + Real.log ‖w - c₂‖ := by linarith
      refine ⟨by rw [hval]; exact inv_ne_zero hu0, ?_⟩
      rw [hval, norm_inv, hun, ← Real.exp_neg, neg_neg, hGx, Real.exp_add,
        Real.exp_log hpos]
    have hρderiv : deriv ρ c₂ ≠ 0 := by
      refine hderiv_ne ρ c₂ s ηp hs hρ0 hρan ?_ (fun w hw hwc => (hρdat w hw hwc).2)
      exact (hηpharm c₂ (mem_ball_self hs₁pos)).1.continuousAt
    obtain ⟨A₂, hA₂def⟩ : ∃ f : ℂ → ℂ,
        f = fun w => dslope ρ' c₂ w / dslope ρ c₂ w * (1 - w₀ * ρ w) := ⟨_, rfl⟩
    have hA₂cont : ContinuousAt A₂ c₂ := by
      have hc1 : ContinuousAt (dslope ρ' c₂) c₂ :=
        continuousAt_dslope_same.mpr (hρ'an c₂ (mem_ball_self hs)).differentiableAt
      have hc2 : ContinuousAt (dslope ρ c₂) c₂ :=
        continuousAt_dslope_same.mpr (hρan c₂ (mem_ball_self hs)).differentiableAt
      have hc3 : dslope ρ c₂ c₂ ≠ 0 := by
        rw [dslope_same]
        exact hρderiv
      have hc4 : ContinuousAt (fun w => 1 - w₀ * ρ w) c₂ :=
        continuousAt_const.sub
          (continuousAt_const.mul (hρan c₂ (mem_ball_self hs)).continuousAt)
      simp only [hA₂def]
      exact (hc1.div hc2 hc3).mul hc4
    have hA₂diff : ∀ᶠ w in 𝓝[≠] c₂, DifferentiableAt ℂ A₂ w := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c₂ hs), self_mem_nhdsWithin]
        with w hwb hwm
      have hwc : w ≠ c₂ := Set.mem_compl_singleton_iff.mp hwm
      have hd1 := hdslope_diff ρ' c₂ w hρ'0 hwc (hρ'an w hwb)
      have hd2 := hdslope_diff ρ c₂ w hρ0 hwc (hρan w hwb)
      have hd3 : dslope ρ c₂ w ≠ 0 :=
        hdslope_ne ρ c₂ w hρ0 hwc (hρdat w hwb hwc).1
      have hd4 : DifferentiableAt ℂ (fun v => 1 - w₀ * ρ v) w :=
        (differentiableAt_const _).sub
          ((differentiableAt_const _).mul (hρan w hwb).differentiableAt)
      simp only [hA₂def]
      exact (hd1.div hd2 hd3).mul hd4
    have hA₂an : AnalyticAt ℂ A₂ c₂ :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        hA₂diff hA₂cont
    have hHp₂eq : A₂ =ᶠ[𝓝 c₂] H ∘ ⇑χ₂.symm := by
      filter_upwards [ball_mem_nhds c₂ hs] with w hwb
      by_cases hwc : w = c₂
      · subst hwc
        simp only [hA₂def, Function.comp_apply]
        rw [hρ0, mul_zero, sub_zero, mul_one, hsymmc₂]
        simp only [hHdef]
        rw [if_neg (Ne.symm hq'p₂), if_pos trivial]
      · have hnp₂ : χ₂.symm w ≠ p₂ := hsymm_ne₂ w hwb hwc
        have hnq' : χ₂.symm w ≠ q' := Set.mem_compl_singleton_iff.mp (hsb₂ hwb).2.2.2
        have hnp₁ : χ₂.symm w ≠ p₁ := Set.mem_compl_singleton_iff.mp (hsb₂ hwb).2.2.1
        obtain ⟨u, hu, hu0, -⟩ := hφdat (χ₂.symm w) hnp₁ hnp₂
        obtain ⟨u', hu', hu'0, -⟩ := hφ'dat (χ₂.symm w) hnq' hnp₂
        have hρw : ρ w = u⁻¹ := by
          simp only [hρdef]
          rw [hu, hinfval u hu0]
        have hρ'w : ρ' w = u'⁻¹ := by
          simp only [hρ'def]
          rw [hu', hinfval u' hu'0]
        simp only [hA₂def, Function.comp_apply, hHdef]
        rw [if_neg hnq', if_neg hnp₂, hu, hu', sphereChartFinite_coe,
          sphereChartFinite_coe, hdslope_eval ρ' c₂ w hρ'0 hwc,
          hdslope_eval ρ c₂ w hρ0 hwc,
          div_div_div_cancel_right₀ (sub_ne_zero_of_ne hwc), hρw, hρ'w]
        field_simp
    exact hbuild H p₂ (hA₂an.congr hHp₂eq)
  have hHsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H := by
    intro x
    by_cases hx1 : x = q'
    · subst hx1
      exact hHsm_q'
    by_cases hx2 : x = p₂
    · subst hx2
      exact hHsm_p₂
    exact hHsm_gen x hx1 hx2
  /- ## Endgame case split on compactness of the surface. -/
  by_cases hcpt : CompactSpace M
  · -- Compact: a nonconstant holomorphic function has clopen plane image.
    haveI := hcpt
    have hnc : ¬ ∃ cc : ℂ, ∀ x : M, H x = cc := by
      rintro ⟨cc, hcc⟩
      apply hHp₁
      rw [hcc p₁, ← hcc q]
      exact hHq
    have hopen : IsOpenMap H := isOpenMap_of_contMDiff_of_not_const hHsm hnc
    have hclopen : IsClopen (Set.range H) :=
      ⟨(isCompact_range hHsm.continuous).isClosed, hopen.isOpen_range⟩
    have hrange : Set.range H = Set.univ :=
      hclopen.eq_univ ⟨H q, Set.mem_range_self q⟩
    obtain ⟨CB, hCB⟩ := isBounded_iff_forall_norm_le.mp
      (isCompact_range hHsm.continuous).isBounded
    have hmem : ((max CB 0 + 1 : ℝ) : ℂ) ∈ Set.range H := by
      rw [hrange]
      exact Set.mem_univ _
    have hle := hCB _ hmem
    have h0C : (0 : ℝ) ≤ max CB 0 := le_max_right CB 0
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hle
    have hCle : CB ≤ max CB 0 := le_max_left CB 0
    linarith
  · -- Noncompact: the bounded-ratio comparison forces a Green's function at `q`.
    haveI hncM : NoncompactSpace M := not_compactSpace_iff.mp hcpt
    /- ## The per-candidate Blaschke-type comparison at the pole `q`. -/
    have MAIN : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) →
        (∀ y, ‖Ψ y‖ < 1) → Ψ q = 0 → (∃ y₀, Ψ y₀ ≠ 0) →
        ∀ x, x ≠ q → BddAbove ((fun v => v x) '' greenFamily q) := by
      intro Ψ hΨm hΨlt hΨq hΨex
      have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun y => (hΨm y).continuousAt
      have hqsrc : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
      have hcq : (chartAt ℂ q).symm (chartAt ℂ q q) = q := (chartAt ℂ q).left_inv hqsrc
      -- Punctured-neighborhood nonvanishing at the pole, in the chart.
      have hisoq := hisoM Ψ hΨm hΨex q hΨq
      obtain ⟨W0, hW0sub, hW0open, hqW0⟩ :=
        _root_.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hisoq)
      -- A chart ball around the pole inside the chart target whose pullback lies in `W0`.
      have hopen1 : IsOpen ((chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0) :=
        (chartAt ℂ q).isOpen_inter_preimage_symm hW0open
      have hmem1 : chartAt ℂ q q ∈ (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 :=
          by
        refine ⟨(chartAt ℂ q).map_source hqsrc, ?_⟩
        rw [Set.mem_preimage, hcq]
        exact hqW0
      obtain ⟨rr, hrr, hrrsub⟩ := Metric.isOpen_iff.1 hopen1 (chartAt ℂ q q) hmem1
      -- The small pole disk `V'` and its compact closure barrel `K'`.
      have hrr2 : 0 < rr / 2 := by linarith
      have hcbsub : closedBall (chartAt ℂ q q) (rr / 2) ⊆
          (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 :=
        (Metric.closedBall_subset_ball (by linarith)).trans hrrsub
      obtain ⟨V', hV'def⟩ : ∃ S : Set M,
          S = (chartAt ℂ q).source ∩ chartAt ℂ q ⁻¹' ball (chartAt ℂ q q) (rr / 2) :=
              ⟨_, rfl⟩
      have hV'open : IsOpen V' := by
        rw [hV'def]
        exact (chartAt ℂ q).continuousOn.isOpen_inter_preimage (chartAt ℂ q).open_source
          isOpen_ball
      have hqV' : q ∈ V' := by
        rw [hV'def]
        exact ⟨hqsrc, by rw [Set.mem_preimage]; exact mem_ball_self hrr2⟩
      -- Nonvanishing of `Ψ` on the punctured pole disk (pullback of `W0`).
      have hV'ne : ∀ y ∈ V', y ≠ q → Ψ y ≠ 0 := by
        intro y hy hyq
        rw [hV'def] at hy
        have h1 : chartAt ℂ q y ∈ ball (chartAt ℂ q q) rr :=
          ball_subset_ball (by linarith) hy.2
        have h2 : (chartAt ℂ q).symm (chartAt ℂ q y) ∈ W0 := (hrrsub h1).2
        rw [(chartAt ℂ q).left_inv hy.1] at h2
        exact hW0sub h2 hyq
      -- The compact barrel and the boundary sphere.
      obtain ⟨K', hK'def⟩ : ∃ S : Set M,
          S = (chartAt ℂ q).symm '' closedBall (chartAt ℂ q q) (rr / 2) := ⟨_, rfl⟩
      have hK'cp : IsCompact K' := by
        rw [hK'def]
        exact (isCompact_closedBall _ _).image_of_continuousOn
          ((chartAt ℂ q).continuousOn_symm.mono (hcbsub.trans Set.inter_subset_left))
      have hV'K' : V' ⊆ K' := by
        intro y hy
        rw [hV'def] at hy
        rw [hK'def]
        exact ⟨chartAt ℂ q y, ball_subset_closedBall hy.2, (chartAt ℂ q).left_inv hy.1⟩
      have hclosV' : closure V' ⊆ K' :=
        closure_minimal hV'K' hK'cp.isClosed
      -- Points of the barrel off the disk sit on the boundary sphere, where `Ψ ≠ 0`.
      have hK'edge : ∀ y ∈ K', y ∉ V' →
          y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2) := by
        intro y hy hyV'
        rw [hK'def] at hy
        obtain ⟨w, hw, rfl⟩ := hy
        have hwt : w ∈ (chartAt ℂ q).target := (hcbsub hw).1
        have hysrc : (chartAt ℂ q).symm w ∈ (chartAt ℂ q).source := (chartAt ℂ q).map_target
            hwt
        have hwch : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
        have hnb : w ∉ ball (chartAt ℂ q q) (rr / 2) := by
          intro hwb
          apply hyV'
          rw [hV'def]
          exact ⟨hysrc, by rw [Set.mem_preimage, hwch]; exact hwb⟩
        have hd : dist w (chartAt ℂ q q) = rr / 2 := by
          have h1 := mem_closedBall.1 hw
          have h2 : ¬ dist w (chartAt ℂ q q) < rr / 2 := fun h => hnb (mem_ball.2 h)
          linarith [not_lt.mp h2]
        exact ⟨w, mem_sphere.2 hd, rfl⟩
      have hedge_ne : ∀ y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2), Ψ y ≠
          0 := by
        rintro y ⟨w, hw, rfl⟩
        have hwb : w ∈ ball (chartAt ℂ q q) rr := by
          rw [mem_ball]
          rw [mem_sphere.1 hw]
          linarith
        have hwt : w ∈ (chartAt ℂ q).target := (hrrsub hwb).1
        have hW0mem : (chartAt ℂ q).symm w ∈ W0 := (hrrsub hwb).2
        have hyne : (chartAt ℂ q).symm w ≠ q := by
          intro hcon
          have h1 : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
          rw [hcon] at h1
          have h2 : dist w (chartAt ℂ q q) = rr / 2 := mem_sphere.1 hw
          rw [← h1, dist_self] at h2
          linarith
        exact hW0sub hW0mem hyne
      -- The minimum of `‖Ψ‖` on the boundary sphere is positive.
      have hS'cp : IsCompact ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2)) := by
        refine (isCompact_sphere _ _).image_of_continuousOn ?_
        refine (chartAt ℂ q).continuousOn_symm.mono ?_
        refine (sphere_subset_closedBall.trans ?_)
        exact hcbsub.trans Set.inter_subset_left
      have hS'ne : ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (rr / 2)).Nonempty :=
        Set.Nonempty.image _ (NormedSpace.sphere_nonempty.2 hrr2.le)
      obtain ⟨ym, hymS, hymmin⟩ := hS'cp.exists_isMinOn hS'ne (hΨc.norm.continuousOn)
      have hm0 : 0 < ‖Ψ ym‖ := norm_pos_iff.2 (hedge_ne ym hymS)
      -- The truncated pole-adapted logarithm family.
      obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ → M → ℝ, Λ = fun N x =>
          if x ∈ V' then Real.log ‖Ψ x‖
          else if Ψ x = 0 then -N else max (Real.log ‖Ψ x‖) (-N) := ⟨_, rfl⟩
      have hΛ1 : ∀ N (x : M), x ∈ V' → Λ N x = Real.log ‖Ψ x‖ := by
        intro N x hx
        simp only [hΛdef]
        exact if_pos hx
      have hΛ2 : ∀ N (x : M), x ∉ V' → Ψ x = 0 → Λ N x = -N := by
        intro N x hx hx0
        simp only [hΛdef]
        rw [if_neg hx, if_pos hx0]
      have hΛ3 : ∀ N (x : M), x ∉ V' → Ψ x ≠ 0 → Λ N x = max (Real.log ‖Ψ x‖) (-N)
          := by
        intro N x hx hx0
        simp only [hΛdef]
        rw [if_neg hx, if_neg hx0]
      -- The truncation is nonpositive.
      have hΛle : ∀ N, 0 < N → ∀ x : M, Λ N x ≤ 0 := by
        intro N hN x
        by_cases hx : x ∈ V'
        · rw [hΛ1 N x hx]
          exact Real.log_nonpos (norm_nonneg _) (hΨlt x).le
        · by_cases hx0 : Ψ x = 0
          · rw [hΛ2 N x hx hx0]; linarith
          · rw [hΛ3 N x hx hx0]
            refine max_le ?_ (by linarith)
            exact Real.log_nonpos (norm_nonneg _) (hΨlt x).le
      -- Subharmonicity of the truncation off the pole, for large truncation levels.
      have hΛsub : ∀ N, -Real.log (‖Ψ ym‖ / 2) ≤ N → ∀ x : M, x ≠ q →
          MSubharmonicAt (Λ N) x := by
        intro N hN x hxq
        by_cases hxV' : x ∈ V'
        · -- near the pole: the truncation is the genuine `log‖Ψ‖`, harmonic there
          have hO : IsOpen (V' ∩ {q}ᶜ) := hV'open.inter isOpen_compl_singleton
          have hxO : x ∈ V' ∩ {q}ᶜ := ⟨hxV', hxq⟩
          have hEq : Set.EqOn (fun y => Real.log ‖Ψ y‖) (Λ N) (V' ∩ {q}ᶜ) := by
            intro y hy
            exact (hΛ1 N y hy.1).symm
          exact hcongM _ _ x _ hO hxO hEq
            ((hlogM Ψ hΨm x (hV'ne x hxV' hxq)).msubharmonicAt)
        · by_cases hxm : ‖Ψ ym‖ / 2 < ‖Ψ x‖
          · -- moderate modulus: the truncation agrees with the genuine `log‖Ψ‖`
            have hO : IsOpen {y : M | ‖Ψ ym‖ / 2 < ‖Ψ y‖} :=
              isOpen_lt continuous_const hΨc.norm
            have hEq : Set.EqOn (fun y => Real.log ‖Ψ y‖) (Λ N)
                {y : M | ‖Ψ ym‖ / 2 < ‖Ψ y‖} := by
              intro y hy
              have hy' : ‖Ψ ym‖ / 2 < ‖Ψ y‖ := hy
              by_cases hyV' : y ∈ V'
              · exact (hΛ1 N y hyV').symm
              · have hy0 : Ψ y ≠ 0 := by
                  intro hcon
                  rw [hcon, norm_zero] at hy'
                  linarith
                rw [hΛ3 N y hyV' hy0]
                have h1 : -N ≤ Real.log ‖Ψ y‖ := by
                  have h2 : Real.log (‖Ψ ym‖ / 2) ≤ Real.log ‖Ψ y‖ :=
                    Real.log_le_log (by linarith) hy'.le
                  linarith
                exact (max_eq_left h1).symm
            have hx0 : Ψ x ≠ 0 := by
              intro hcon
              rw [hcon, norm_zero] at hxm
              linarith
            exact hcongM _ _ x _ hO hxm hEq ((hlogM Ψ hΨm x hx0).msubharmonicAt)
          · -- small modulus away from the pole disk: use the plain truncated form
            have hxK' : x ∉ closure V' := by
              intro hcon
              by_cases hxV2 : x ∈ V'
              · exact hxV' hxV2
              · have h1 := hK'edge x (hclosV' hcon) hxV2
                have h4 : ‖Ψ ym‖ ≤ ‖Ψ x‖ := hymmin h1
                have h5 : 0 < ‖Ψ ym‖ := hm0
                linarith [not_lt.mp hxm]
            have hOc : IsOpen ((closure V')ᶜ : Set M) := isClosed_closure.isOpen_compl
            by_cases hx0 : Ψ x = 0
            · -- constant `−N` near a zero of `Ψ`
              have hO : IsOpen ((closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N))) :=
                hOc.inter (isOpen_ball.preimage hΨc)
              have hxO : x ∈ (closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N)) := by
                refine ⟨hxK', ?_⟩
                rw [Set.mem_preimage, hx0]
                exact mem_ball_self (Real.exp_pos _)
              have hEq : Set.EqOn (fun _ : M => (-N : ℝ)) (Λ N)
                  ((closure V')ᶜ ∩ Ψ ⁻¹' ball 0 (Real.exp (-N))) := by
                rintro y ⟨hy1, hy2⟩
                have hyV' : y ∉ V' := fun hcon => hy1 (subset_closure hcon)
                by_cases hy0 : Ψ y = 0
                · exact (hΛ2 N y hyV' hy0).symm
                · rw [Set.mem_preimage, mem_ball_zero_iff] at hy2
                  have h2 : Real.log ‖Ψ y‖ ≤ -N := by
                    have h3 := Real.log_lt_log (norm_pos_iff.mpr hy0) hy2
                    rw [Real.log_exp] at h3
                    exact h3.le
                  rw [hΛ3 N y hyV' hy0]
                  exact (max_eq_right h2).symm
              exact hcongM _ _ x _ hO hxO hEq
                ((mharmonicAt_const (x := x) (a := (-N : ℝ))).msubharmonicAt)
            · -- the max of the harmonic `log‖Ψ‖` and the constant `−N`
              have hO : IsOpen ((closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ) :=
                hOc.inter (isOpen_compl_singleton.preimage hΨc)
              have hxO : x ∈ (closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ := ⟨hxK', hx0⟩
              have hEq : Set.EqOn (fun y => max (Real.log ‖Ψ y‖) (-N)) (Λ N)
                  ((closure V')ᶜ ∩ Ψ ⁻¹' {(0 : ℂ)}ᶜ) := by
                rintro y ⟨hy1, hy2⟩
                have hyV' : y ∉ V' := fun hcon => hy1 (subset_closure hcon)
                exact (hΛ3 N y hyV' hy2).symm
              have hmax : MSubharmonicAt (fun y => max (Real.log ‖Ψ y‖) (-N)) x :=
                MSubharmonicAt.max ((hlogM Ψ hΨm x hx0).msubharmonicAt)
                  ((mharmonicAt_const (x := x) (a := (-N : ℝ))).msubharmonicAt)
              exact hcongM _ _ x _ hO hxO hEq hmax
      -- The chart map sends the punctured filter at `q` into the punctured filter at `c_q`.
      have htendq : Tendsto (chartAt ℂ q) (𝓝[≠] q) (𝓝[≠] (chartAt ℂ q q)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · exact ((chartAt ℂ q).continuousAt hqsrc).tendsto.mono_left nhdsWithin_le_nhds
        · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ q).open_source.mem_nhds hqsrc),
            self_mem_nhdsWithin] with y hys hyq
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hyq ((chartAt ℂ q).injOn hys hqsrc hcon)
      -- First-order vanishing of `Ψ` at the pole: `log‖Ψ‖ ≤ C + log‖poleCoord‖` nearby.
      have hslope : ∃ Cs : ℝ, ∀ᶠ x in 𝓝[≠] q,
          Real.log ‖Ψ x‖ ≤ Cs + Real.log ‖poleCoord q x‖ := by
        have hgan : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) := hreadM Ψ hΨm
            q
        have hg0 : (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) = 0 := by
          simp only [Function.comp_apply, hcq]
          exact hΨq
        have hd : HasDerivAt (Ψ ∘ (chartAt ℂ q).symm)
            (deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)) (chartAt ℂ q q) :=
          hgan.differentiableAt.hasDerivAt
        have hsl := hasDerivAt_iff_tendsto_slope.mp hd
        have hd1 : (0 : ℝ) ≤ ‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ :=
          norm_nonneg _
        have hbnd : ∀ᶠ w in 𝓝[≠] (chartAt ℂ q q),
            ‖slope (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) w‖
              < ‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1 :=
          hsl.norm.eventually_lt_const (by linarith)
        refine ⟨Real.log (‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1), ?_⟩
        filter_upwards [htendq.eventually hbnd,
          nhdsWithin_le_nhds ((chartAt ℂ q).open_source.mem_nhds hqsrc),
          self_mem_nhdsWithin, hisoq] with x hx hxs hxq hx0
        have hxcne : chartAt ℂ q x ≠ chartAt ℂ q q := by
          intro hcon
          exact hxq ((chartAt ℂ q).injOn hxs hqsrc hcon)
        have hslval : slope (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) (chartAt ℂ q x)
            = Ψ x / (chartAt ℂ q x - chartAt ℂ q q) := by
          rw [slope_def_field, hg0, sub_zero]
          congr 1
          simp only [Function.comp_apply, (chartAt ℂ q).left_inv hxs]
        have hx' := hx
        rw [hslval] at hx'
        have hpne : chartAt ℂ q x - chartAt ℂ q q ≠ 0 := sub_ne_zero_of_ne hxcne
        have hΨbound : ‖Ψ x‖ ≤ (‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖
            + 1)
            * ‖chartAt ℂ q x - chartAt ℂ q q‖ := by
          rw [norm_div] at hx'
          have h2 : 0 < ‖chartAt ℂ q x - chartAt ℂ q q‖ := norm_pos_iff.mpr hpne
          rw [div_lt_iff₀ h2] at hx'
          exact hx'.le
        have h3 : Real.log ‖Ψ x‖ ≤
            Real.log ((‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1)
              * ‖chartAt ℂ q x - chartAt ℂ q q‖) :=
          Real.log_le_log (norm_pos_iff.mpr hx0) hΨbound
        rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hpne)] at h3
        exact h3
      obtain ⟨Cs, hCs⟩ := hslope
      -- The per-candidate comparison via the puncture-tolerant maximum principle.
      have key : ∀ N, -Real.log (‖Ψ ym‖ / 2) ≤ N → 0 < N →
          ∀ v ∈ greenFamily q, ∀ x, x ≠ q → v x + Λ N x ≤ 0 := by
        intro N hN0 hNpos v hv x hx
        obtain ⟨hvsub, -, ⟨K, hKcp, -, hK0⟩, C, hC⟩ := hv
        have h1 : MSubharmonicOn (fun y => v y + Λ N y) {q}ᶜ :=
          fun y hy => haddM v (Λ N) y (hvsub y hy) (hΛsub N hN0 y hy)
        have h2 : ∃ K' : Set M, IsCompact K' ∧ ∀ y ∉ K', v y + Λ N y ≤ 0 :=
          ⟨K, hKcp, fun y hy => by rw [hK0 y hy, zero_add]; exact hΛle N hNpos y⟩
        have h3 : ∃ C', ∀ᶠ y in 𝓝[≠] q, v y + Λ N y ≤ C' := by
          refine ⟨C + Cs, ?_⟩
          have hV'mem : ∀ᶠ y in 𝓝[≠] q, y ∈ V' :=
            nhdsWithin_le_nhds (hV'open.mem_nhds hqV')
          filter_upwards [hC, hCs, hV'mem] with y h1y h2y h3y
          rw [hΛ1 N y h3y]
          linarith
        exact msubharmonic_le_zero_of_puncture h1 h2 h3 x hx
      -- Boundedness of the family at every point off the pole.
      intro x hx
      refine ⟨-Λ (max (-Real.log (‖Ψ ym‖ / 2)) 1) x, ?_⟩
      rintro t ⟨v, hv, rfl⟩
      have h1 := key (max (-Real.log (‖Ψ ym‖ / 2)) 1) (le_max_left _ _)
        (lt_of_lt_of_le one_pos (le_max_right _ _)) v hv x hx
      have h2 : (fun v : M → ℝ => v x) v = v x := rfl
      rw [h2]
      linarith
    /- ## A global bound on `H`: off the compact closures by the two modulus
    bounds, on them by continuity. -/
    obtain ⟨CG, V₁, hV₁n, V₂, hV₂n, hV₁c, hV₂c, hGb⟩ := hbdd
    obtain ⟨CG', V₁', hV₁'n, V₂', hV₂'n, hV₁'c, hV₂'c, hG'b⟩ := hbdd'
    have hKBcp : IsCompact ((closure V₁ ∪ closure V₂) ∪ (closure V₁' ∪ closure V₂'))
        :=
      (hV₁c.union hV₂c).union (hV₁'c.union hV₂'c)
    obtain ⟨B₁, hB₁⟩ := hKBcp.exists_bound_of_continuousOn hHsm.continuous.continuousOn
    have hoff : ∀ x : M, x ∉ (closure V₁ ∪ closure V₂) ∪ (closure V₁' ∪ closure
        V₂') →
        ‖H x‖ ≤ (Real.exp CG + ‖w₀‖) * Real.exp CG' := by
      intro x hx
      have hx1 : x ∉ V₁ ∪ V₂ := by
        intro hmem
        apply hx
        rcases hmem with hm | hm
        · exact Or.inl (Or.inl (subset_closure hm))
        · exact Or.inl (Or.inr (subset_closure hm))
      have hx2 : x ∉ V₁' ∪ V₂' := by
        intro hmem
        apply hx
        rcases hmem with hm | hm
        · exact Or.inr (Or.inl (subset_closure hm))
        · exact Or.inr (Or.inr (subset_closure hm))
      have hxp₁ : x ≠ p₁ := by
        rintro rfl
        exact hx1 (Or.inl (mem_of_mem_nhds hV₁n))
      have hxp₂ : x ≠ p₂ := by
        rintro rfl
        exact hx1 (Or.inr (mem_of_mem_nhds hV₂n))
      have hxq' : x ≠ q' := by
        rintro rfl
        exact hx2 (Or.inl (mem_of_mem_nhds hV₁'n))
      obtain ⟨u, hu, hu0, hun⟩ := hφdat x hxp₁ hxp₂
      obtain ⟨u', hu', hu'0, hu'n⟩ := hφ'dat x hxq' hxp₂
      have hHval : H x = (u - w₀) / u' := by
        simp only [hHdef]
        rw [if_neg hxq', if_neg hxp₂, hu, hu', sphereChartFinite_coe,
          sphereChartFinite_coe]
      have hGx := hGb x hx1
      have hG'x := hG'b x hx2
      have hb1 : ‖u‖ ≤ Real.exp CG := by
        rw [hun]
        apply Real.exp_le_exp.mpr
        have habsle := abs_le.mp hGx
        linarith [habsle.1]
      have hb2 : Real.exp (-CG') ≤ ‖u'‖ := by
        rw [hu'n]
        apply Real.exp_le_exp.mpr
        have habsle := abs_le.mp hG'x
        linarith [habsle.2]
      have hb3 : ‖u - w₀‖ ≤ Real.exp CG + ‖w₀‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_nonneg w₀])
      rw [hHval, norm_div]
      calc ‖u - w₀‖ / ‖u'‖ ≤ (Real.exp CG + ‖w₀‖) / Real.exp (-CG') :=
            div_le_div₀ (by positivity) hb3 (Real.exp_pos _) hb2
        _ = (Real.exp CG + ‖w₀‖) * Real.exp CG' := by
            rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
    set B : ℝ := max B₁ ((Real.exp CG + ‖w₀‖) * Real.exp CG') with hBdef
    have hB : ∀ x : M, ‖H x‖ ≤ B := by
      intro x
      by_cases hx : x ∈ (closure V₁ ∪ closure V₂) ∪ (closure V₁' ∪ closure V₂')
      · exact (hB₁ x hx).trans (le_max_left _ _)
      · exact (hoff x hx).trans (le_max_right _ _)
    have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg (H q)) (hB q)
    have hD0 : (0 : ℝ) < 2 * B + 1 := by linarith
    have hDC0 : ((2 * B + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD0.ne'
    /- ## The normalized transplant `Ψ = (H − H q)/(2B + 1)`. -/
    obtain ⟨Ψ, hΨdef⟩ : ∃ f : M → ℂ,
        f = fun x => (H x - H q) / ((2 * B + 1 : ℝ) : ℂ) := ⟨_, rfl⟩
    have hΨm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y := by
      intro y
      apply hbuild
      have hm1 : AnalyticAt ℂ (H ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y y) :=
        hreadM H (fun z => hHsm z) y
      have hm2 : AnalyticAt ℂ
          (fun w => (H ((chartAt ℂ y).symm w) - H q) / ((2 * B + 1 : ℝ) : ℂ))
          (chartAt ℂ y y) := (hm1.sub analyticAt_const).div analyticAt_const hDC0
      rw [hΨdef]
      exact hm2
    have hΨlt : ∀ y, ‖Ψ y‖ < 1 := by
      intro y
      simp only [hΨdef]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0,
        div_lt_one hD0]
      have hb1 := hB y
      have hb2 := hB q
      have hb3 := norm_sub_le (H y) (H q)
      linarith
    have hΨq : Ψ q = 0 := by
      simp only [hΨdef]
      rw [sub_self, zero_div]
    have hΨex : ∃ y₀, Ψ y₀ ≠ 0 := by
      refine ⟨p₁, ?_⟩
      simp only [hΨdef]
      rw [hHq, sub_zero]
      exact div_ne_zero hHp₁ hDC0
    exact hnon q ⟨p₁, Ne.symm hqp₁, MAIN Ψ hΨm hΨlt hΨq hΨex p₁ (Ne.symm hqp₁)⟩

/-! ## The compact case and the non-hyperbolic assembly -/

/-- **Compact surfaces carry no Green's function**: the Perron family is
unbounded at every point distinct from the pole. -/
theorem not_bddAbove_greenFamily_of_compactSpace [CompactSpace M]
    [SecondCountableTopology M] (p₀ x : M) (hx : x ≠ p₀) :
    ¬ BddAbove ((fun v => v x) '' greenFamily p₀) := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  intro hbdd
  obtain ⟨s, hs⟩ := hbdd
  set B' : ℝ := max s 0 with hB'
  have hB'0 : (0 : ℝ) ≤ B' := le_max_right _ _
  /- ## Plane-side helper: transfer of subharmonicity along a pointwise equality. -/
  have transfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro a ha ρ hρ hb
    have h1 : G a = F a := (hFG ha).symm
    have h2 : Real.circleAverage F a ρ = Real.circleAverage G a ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 a (hWU ha) ρ hρ (hb.trans hWU)
  /- ## Constancy propagation on a preconnected open set from an interior maximum. -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ z ∈ Ω, w z ≤ w xm) → ∀ z ∈ Ω, w z = w
          xm := by
    intro Ω w xm hΩo hΩc hxm hwsub hmax
    have hso : IsOpen {z | z ∈ Ω ∧ w z = w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hmax' : ∀ u ∈ Ω, w u ≤ w z := fun u hu => (hmax u hu).trans_eq hzw.symm
      have hev := MSubharmonicAt.eventually_eq_of_le hΩo hzΩ hwsub hmax'
      filter_upwards [hev, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu.trans hzw⟩
    have hto : IsOpen {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzΩ, hzw⟩
      have hcont : ContinuousAt w z := (hwsub z hzΩ).continuousAt
      filter_upwards [hcont.eventually_ne hzw, hΩo.mem_nhds hzΩ] with u hu huΩ
      exact ⟨huΩ, hu⟩
    have hsub : Ω ⊆ {z | z ∈ Ω ∧ w z = w xm} ∪ {z | z ∈ Ω ∧ w z ≠ w xm} := by
      intro z hz
      by_cases hzw : w z = w xm
      · exact Or.inl ⟨hz, hzw⟩
      · exact Or.inr ⟨hz, hzw⟩
    have hdisj : Disjoint {z | z ∈ Ω ∧ w z = w xm} {z | z ∈ Ω ∧ w z ≠ w xm} := by
      rw [Set.disjoint_iff]
      rintro z ⟨⟨-, h1⟩, -, h2⟩
      exact h2 h1
    have hres := hΩc.subset_left_of_subset_union hso hto hdisj hsub ⟨xm, hxm, hxm, rfl⟩
    exact fun z hz => (hres hz).2
  /- ## Maximum principle on an open set `Ω ≠ univ` with compact exceptional set. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
      (∀ z ∈ Ω, z ∉ Kc → w z ≤ m) →
      (∀ y ∈ closure Ω \ Ω, ContinuousAt w y ∧ w y ≤ m) →
      ∀ z ∈ Ω, w z ≤ m := by
    intro Ω w m Kc hΩo hΩne hwsub hKc hout hfr
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀Ω, hx₀⟩ := hcon
    have hcontcl : ContinuousOn w (closure Ω) := by
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact ((hwsub y hyΩ).continuousAt).continuousWithinAt
      · exact ((hfr y ⟨hy, hyΩ⟩).1).continuousWithinAt
    have hB : IsCompact (closure Ω ∩ Kc) := hKc.inter_left isClosed_closure
    have hx₀B : x₀ ∈ closure Ω ∩ Kc := by
      refine ⟨subset_closure hx₀Ω, ?_⟩
      by_contra hxK
      exact absurd (hout x₀ hx₀Ω hxK) (not_le.2 hx₀)
    obtain ⟨xm, hxmB, hxmax⟩ :=
      hB.exists_isMaxOn ⟨x₀, hx₀B⟩ (hcontcl.mono Set.inter_subset_left)
    have hTgt : m < w xm := lt_of_lt_of_le hx₀ (hxmax hx₀B)
    have hxmΩ : xm ∈ Ω := by
      by_contra hxΩ
      exact absurd (hfr xm ⟨hxmB.1, hxΩ⟩).2 (not_le.2 hTgt)
    have hall : ∀ z ∈ Ω, w z ≤ w xm := by
      intro z hz
      by_cases hzK : z ∈ Kc
      · exact hxmax ⟨subset_closure hz, hzK⟩
      · exact (hout z hz hzK).trans hTgt.le
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun z hz => hwsub z (hCcΩ hz)) (fun z hz => hall z (hCcΩ hz))
    have hfrne :
        (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
      by_contra hem
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hem
      have hclopen : IsClopen (connectedComponentIn Ω xm) :=
        ⟨closure_eq_iff_isClosed.1 (Set.Subset.antisymm hem subset_closure), hCco⟩
      have huniv : connectedComponentIn Ω xm = Set.univ := hclopen.eq_univ ⟨xm, hCcx⟩
      apply hΩne
      apply Set.eq_univ_of_univ_subset
      rw [← huniv]
      exact hCcΩ
    obtain ⟨y, hycl, hyC⟩ := hfrne
    have hyΩ : y ∉ Ω := by
      intro hyΩ
      have hyC' : y ∈ connectedComponentIn Ω y := mem_connectedComponentIn hyΩ
      have hopen' : IsOpen (connectedComponentIn Ω y) := hΩo.connectedComponentIn
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hycl _ hopen' hyC'
      have he1 : connectedComponentIn Ω y = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz1
      have he2 : connectedComponentIn Ω xm = connectedComponentIn Ω z :=
        connectedComponentIn_eq hz2
      exact hyC (he2.trans he1.symm ▸ hyC')
    have hyfr : y ∈ closure Ω \ Ω := ⟨closure_mono hCcΩ hycl, hyΩ⟩
    obtain ⟨hyct, hyle⟩ := hfr y hyfr
    haveI hne : (𝓝[connectedComponentIn Ω xm] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hycl
    have h1 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w y)) :=
      hyct.continuousWithinAt
    have h2 : Tendsto w (𝓝[connectedComponentIn Ω xm] y) (𝓝 (w xm)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hconst z hz).symm
    have heq : w y = w xm := tendsto_nhds_unique h1 h2
    exact absurd hyle (not_le.2 (heq ▸ hTgt))
  /- ## Images under an inverse chart, in preimage form. -/
  have himg : ∀ (f : OpenPartialHomeomorph M ℂ) (u : Set ℂ), u ⊆ f.target →
      f.symm '' u = f.source ∩ f ⁻¹' u := by
    intro f u hu
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨f.map_target (hu hz), ?_⟩
      rw [Set.mem_preimage, f.right_inv (hu hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨f y, hy2, f.left_inv hy⟩
  /- ## A function vanishing on a neighborhood is subharmonic there. -/
  have msub_zero : ∀ (f : M → ℝ) (U : Set M) (y : M), IsOpen U → y ∈ U →
      (∀ z ∈ U, f z = 0) → MSubharmonicAt f y := by
    intro f U y hUo hyU hf0
    have hopen2 : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm hUo
    have hmem2 : chartAt ℂ y y ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' U := by
      refine ⟨mem_chart_target ℂ y, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
      exact hyU
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ y y) ρ) :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    refine ⟨ρ, hρ, fun z hz => (hρsub hz).1, ?_⟩
    exact transfer _ _ _ _ h0 subset_rfl fun z hz => (hf0 _ ((hρsub hz).2)).symm
  /- ## Harmonicity at a point respects eventual equality. -/
  have mharm_congr : ∀ (f g : M → ℝ) (y : M), (∀ᶠ z in 𝓝 y, f z = g z) →
      MHarmonicAt f y → MHarmonicAt g y := by
    intro f g y hev hf
    have hcont : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm (mem_chart_target ℂ y)
    have hval : (chartAt ℂ y).symm (chartAt ℂ y y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hev2 : (f ∘ (chartAt ℂ y).symm) =ᶠ[𝓝 (chartAt ℂ y y)]
        (g ∘ (chartAt ℂ y).symm) := by
      have h3 : Tendsto (chartAt ℂ y).symm (𝓝 (chartAt ℂ y y)) (𝓝 y) := by
        have := hcont.tendsto
        rwa [hval] at this
      exact h3.eventually hev
    have hf' : HarmonicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := hf
    exact (harmonicAt_congr_nhds hev2).mp hf'
  /- ## Harmonicity at a point transfers between the surface and an open piece. -/
  have mharm_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MHarmonicAt f (z : M) ↔ MHarmonicAt g z) := by
    intro P f g hfg z
    have hev := Opens.chartAt_subtype_val_symm_eventuallyEq (H := ℂ) P (x := z)
    have hev2 : (f ∘ (chartAt ℂ (z : M)).symm) =ᶠ[𝓝 (chartAt ℂ (z : M) (z : M))]
        (g ∘ (chartAt ℂ z).symm) := by
      filter_upwards [hev] with w hw
      simp only [Function.comp_apply]
      rw [hw, Function.comp_apply, hfg _]
    exact harmonicAt_congr_nhds hev2
  /- ## Subharmonicity at a point transfers between the surface and an open piece. -/
  have msub_val : ∀ (P : Opens M) (f : M → ℝ) (g : ↥P → ℝ), (∀ z : ↥P, f z = g z)
      →
      ∀ z : ↥P, (MSubharmonicAt f (z : M) ↔ MSubharmonicAt g z) := by
    intro P f g hfg z
    have hne : Nonempty ↥P := ⟨z⟩
    set e' : OpenPartialHomeomorph M ℂ := chartAt ℂ (z : M) with he'
    have hzsrc : (z : M) ∈ e'.source := mem_chart_source ℂ (z : M)
    have hct : chartAt ℂ z = e'.subtypeRestr hne := Opens.chartAt_eq
    have hcenter : chartAt ℂ z z = e' (z : M) := by
      rw [hct, e'.subtypeRestr_coe hne]
      rfl
    have htgt : e' (z : M) ∈ (e'.subtypeRestr hne).target := e'.map_subtype_source hne hzsrc
    have heqOn : Set.EqOn (⇑e'.symm) (Subtype.val ∘ ⇑(e'.subtypeRestr hne).symm)
        (e'.subtypeRestr hne).target := e'.subtypeRestr_symm_eqOn hne
    constructor
    · rintro ⟨r, hr, hball, hsub⟩
      have hopen2 : IsOpen ((e'.subtypeRestr hne).target ∩ ball (e' (z : M)) r) :=
        (e'.subtypeRestr hne).open_target.inter isOpen_ball
      have hmem2 : e' (z : M) ∈ (e'.subtypeRestr hne).target ∩ ball (e' (z : M)) r :=
        ⟨htgt, mem_ball_self hr⟩
      obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      refine ⟨r', hr', ?_, ?_⟩
      · rw [hcenter, hct]
        exact fun w hw => (hr'sub hw).1
      · rw [hcenter, hct]
        refine transfer _ _ _ _ hsub (fun w hw => (hr'sub hw).2) ?_
        intro w hw
        simp only [Function.comp_apply]
        rw [← hfg ((e'.subtypeRestr hne).symm w)]
        exact congrArg f (heqOn (hr'sub hw).1)
    · rintro ⟨r, hr, hball, hsub⟩
      rw [hcenter, hct] at hball hsub
      refine ⟨r, hr, hball.trans (e'.subtypeRestr_target_subset hne), ?_⟩
      refine transfer _ _ _ _ hsub subset_rfl ?_
      intro w hw
      simp only [Function.comp_apply]
      rw [← hfg ((e'.subtypeRestr hne).symm w)]
      exact (congrArg f (heqOn (hball hw))).symm
  /- ## The punctured filter of a piece maps to the punctured filter of the surface. -/
  have hmapval : ∀ (P : Opens M) (hpP : p₀ ∈ P),
      Filter.map (Subtype.val : ↥P → M) (𝓝[≠] (⟨p₀, hpP⟩ : ↥P)) = 𝓝[≠] p₀ :=
          by
    intro P hpP
    apply le_antisymm
    · intro A hA
      rw [Filter.mem_map]
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hUmem, ?_⟩
      rintro w ⟨hw1, hw2⟩
      refine hUsub ⟨hw1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hw2 (by rw [Set.mem_singleton_iff]; exact Subtype.ext hcon)
    · intro A hA
      rw [Filter.mem_map] at hA
      rw [mem_nhdsWithin] at hA ⊢
      obtain ⟨U, hUo, hUmem, hUsub⟩ := hA
      obtain ⟨U₀, hU₀o, hU₀eq⟩ := isOpen_induced_iff.mp hUo
      refine ⟨U₀ ∩ (P : Set M), hU₀o.inter P.2, ⟨?_, hpP⟩, ?_⟩
      · have h4 : (⟨p₀, hpP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀eq]; exact
          hUmem
        exact h4
      · rintro y ⟨⟨hyU₀, hyP⟩, hyne⟩
        have hz : (⟨y, hyP⟩ : ↥P) ∈ U ∩ {(⟨p₀, hpP⟩ : ↥P)}ᶜ := by
          constructor
          · have h5 : (⟨y, hyP⟩ : ↥P) ∈ Subtype.val ⁻¹' U₀ := hyU₀
            rw [hU₀eq] at h5
            exact h5
          · intro hcon
            rw [Set.mem_singleton_iff] at hcon
            exact hyne (by rw [Set.mem_singleton_iff]; exact congrArg Subtype.val hcon)
        exact hUsub hz
  /- ## An auxiliary point distinct from the pole and the test point. -/
  obtain ⟨q, hqp, hqx⟩ : ∃ q : M, q ≠ p₀ ∧ q ≠ x := by
    set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he₀
    have hsrc₀ : p₀ ∈ e₀.source := mem_chart_source ℂ p₀
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp e₀.open_target (e₀ p₀) (e₀.map_source hsrc₀)
    have hmem : ∀ t : ℝ, 0 < t → t < ε → e₀ p₀ + (t : ℂ) ∈ e₀.target := by
      intro t' ht0' htε'
      apply hball
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg ht0'.le]
      exact htε'
    have hyne : ∀ t : ℝ, 0 < t → t < ε → e₀.symm (e₀ p₀ + (t : ℂ)) ≠ p₀ := by
      intro t' ht0' htε' hcon
      have h1 : e₀ (e₀.symm (e₀ p₀ + (t' : ℂ))) = e₀ p₀ + (t' : ℂ) :=
        e₀.right_inv (hmem t' ht0' htε')
      rw [hcon] at h1
      have h2 : e₀ p₀ + (t' : ℂ) = e₀ p₀ + 0 := by rw [add_zero]; exact h1.symm
      have h3 : (t' : ℂ) = 0 := add_left_cancel h2
      rw [Complex.ofReal_eq_zero] at h3
      exact ht0'.ne' h3
    have h₁ : (0 : ℝ) < ε / 2 := by linarith
    have h₂ : ε / 2 < ε := by linarith
    have h₃ : (0 : ℝ) < ε / 4 := by linarith
    have h₄ : ε / 4 < ε := by linarith
    by_contra hcon
    have hy1 : e₀.symm (e₀ p₀ + ((ε / 2 : ℝ) : ℂ)) = x := by
      by_contra hne
      exact hcon ⟨_, hyne _ h₁ h₂, hne⟩
    have hy2 : e₀.symm (e₀ p₀ + ((ε / 4 : ℝ) : ℂ)) = x := by
      by_contra hne
      exact hcon ⟨_, hyne _ h₃ h₄, hne⟩
    have h5 := congrArg (⇑e₀) (hy1.trans hy2.symm)
    rw [e₀.right_inv (hmem _ h₁ h₂), e₀.right_inv (hmem _ h₃ h₄)] at h5
    have h6 : ((ε / 2 : ℝ) : ℂ) = ((ε / 4 : ℝ) : ℂ) := add_left_cancel h5
    rw [Complex.ofReal_inj] at h6
    linarith
  /- ## The auxiliary coordinate disk avoiding the pole and the test point. -/
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ q with he
  have hqsrc : q ∈ e.source := mem_chart_source ℂ q
  have hUopen : IsOpen (e.target ∩ e.symm ⁻¹' ({p₀}ᶜ ∩ {x}ᶜ)) :=
    e.isOpen_inter_preimage_symm (isOpen_compl_singleton.inter isOpen_compl_singleton)
  have hqU : e q ∈ e.target ∩ e.symm ⁻¹' ({p₀}ᶜ ∩ {x}ᶜ) := by
    refine ⟨e.map_source hqsrc, ?_⟩
    rw [Set.mem_preimage, e.left_inv hqsrc]
    exact ⟨Set.mem_compl_singleton_iff.mpr hqp, Set.mem_compl_singleton_iff.mpr hqx⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hUopen _ hqU
  set r : ℝ := εa / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrsub : closedBall (e q) r ⊆ e.target ∩ e.symm ⁻¹' ({p₀}ᶜ ∩ {x}ᶜ) :=
    (Metric.closedBall_subset_ball (by rw [hrdef]; linarith)).trans hballa
  set D : CoordDisk M := ⟨q, r, hr0, fun w hw => (hrsub hw).1⟩ with hD
  have hDcar : D.closedCarrier = e.symm '' closedBall (e q) r := rfl
  have hDavoid : ∀ y ∈ D.closedCarrier, y ≠ p₀ ∧ y ≠ x := by
    rintro y ⟨w, hw, rfl⟩
    have h2 := (hrsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨Set.mem_compl_singleton_iff.mp h2.1, Set.mem_compl_singleton_iff.mp h2.2⟩
  have hqD : q ∈ D.closedCarrier := ⟨e q, mem_closedBall_self hr0.le, e.left_inv hqsrc⟩
  have hxq : x ≠ q := fun hcon => (hDavoid q hqD).2 hcon.symm
  /- ## The shrinking pieces. -/
  set t : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 2) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by rw [ht]; positivity
  have ht1 : ∀ n, t n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have htq : ∀ n, t n ≤ 1 / 4 := by
    intro n
    calc t n = (1 / 2 : ℝ) ^ (n + 2) := rfl
      _ ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have htanti : ∀ n m, n ≤ m → t m ≤ t n := fun n m h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htlim : ∀ δ : ℝ, 0 < δ → ∃ n, t n < δ := by
    intro δ hδ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hn⟩
  set DN : ℕ → CoordDisk M := fun n => D.shrink (t n) (ht0 n) (ht1 n) with hDN
  set Wp : ℕ → Opens M := fun n => (DN n).compl with hWp
  have hcarN : ∀ n, (DN n).closedCarrier = e.symm '' closedBall (e q) (t n * r) :=
    fun n => rfl
  have hcarNsub : ∀ n, (DN n).closedCarrier ⊆ D.closedCarrier := by
    intro n
    rw [hcarN n, hDcar]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_of_le_one_left hr0.le (ht1 n)))
  have hcarmono : ∀ n m, n ≤ m → (DN m).closedCarrier ⊆ (DN n).closedCarrier := by
    intro n m hnm
    rw [hcarN n, hcarN m]
    exact Set.image_mono (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_right (htanti n m hnm) hr0.le))
  have hp₀W : ∀ n, p₀ ∈ Wp n := fun n hmem => (hDavoid p₀ (hcarNsub n hmem)).1 rfl
  have hxW : ∀ n, x ∈ Wp n := fun n hmem => (hDavoid x (hcarNsub n hmem)).2 rfl
  have hqW : ∀ n, q ∉ (Wp n : Set M) := by
    intro n hmem
    exact hmem ⟨e q, mem_closedBall_self (mul_pos (ht0 n) hr0).le, e.left_inv hqsrc⟩
  have hWmono : ∀ n m, n ≤ m → (Wp n : Set M) ⊆ (Wp m : Set M) :=
    fun n m hnm y hy hmem => hy (hcarmono n m hnm hmem)
  have hWexh : ∀ y : M, y ≠ q → ∃ n, y ∈ Wp n := by
    intro y hyq
    by_cases hysrc : y ∈ e.source
    · have hne2 : e y ≠ e q := fun hcon => hyq (e.injOn hysrc hqsrc hcon)
      have hd : 0 < ‖e y - e q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne2)
      obtain ⟨n, hn⟩ := htlim (‖e y - e q‖ / r) (by positivity)
      refine ⟨n, fun hmem => ?_⟩
      rw [hcarN n] at hmem
      obtain ⟨w, hw, hwy⟩ := hmem
      have hwt : w ∈ e.target := D.closedBall_subset
        (closedBall_subset_closedBall (mul_le_of_le_one_left hr0.le (ht1 n)) hw)
      have h1 : e y = w := by rw [← hwy, e.right_inv hwt]
      rw [mem_closedBall, dist_eq_norm, ← h1] at hw
      have h2 : t n * r < ‖e y - e q‖ :=
        calc t n * r < ‖e y - e q‖ / r * r := mul_lt_mul_of_pos_right hn hr0
          _ = ‖e y - e q‖ := div_mul_cancel₀ _ hr0.ne'
      linarith
    · refine ⟨0, fun hmem => hysrc ?_⟩
      rw [hcarN 0] at hmem
      obtain ⟨w, hw, hwy⟩ := hmem
      rw [← hwy]
      exact e.map_target (D.closedBall_subset
        (closedBall_subset_closedBall (mul_le_of_le_one_left hr0.le (ht1 0)) hw))
  /- ## Instances and Green data on the pieces. -/
  have hConnW : ∀ n, ConnectedSpace ↥(Wp n) := fun n =>
    isConnected_iff_connectedSpace.mp (isConnected_coordDisk_compl (DN n))
  have hNcW : ∀ n, NoncompactSpace ↥(Wp n) := fun n => noncompactSpace_coordDisk_compl (DN n)
  have hGF : ∀ n, HasGreenFunction (⟨p₀, hp₀W n⟩ : ↥(Wp n)) := fun n =>
    hasGreenFunction_coordDisk_compl (DN n) p₀ (hp₀W n)
  have hEnvH : ∀ n, MHarmonicOn (greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)))
      ({(⟨p₀, hp₀W n⟩ : ↥(Wp n))}ᶜ) ∧
      ∀ z : ↥(Wp n), z ≠ ⟨p₀, hp₀W n⟩ →
        BddAbove ((fun v => v z) '' greenFamily (⟨p₀, hp₀W n⟩ : ↥(Wp n))) := by
    intro n
    haveI := hConnW n
    haveI := hNcW n
    exact ⟨(mharmonicOn_greenEnvelope (hGF n)).1,
      fun z hz => (mharmonicOn_greenEnvelope (hGF n)).2 z hz⟩
  have hEnvPos : ∀ n (z : ↥(Wp n)), z ≠ ⟨p₀, hp₀W n⟩ →
      0 < greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)) z := by
    intro n
    haveI := hConnW n
    haveI := hNcW n
    exact greenEnvelope_pos (hGF n)
  /- ## The piece Green's functions read on the surface. -/
  set V : ℕ → M → ℝ := fun n y =>
    if h : y ∈ Wp n then greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)) ⟨y, h⟩ else 0 with
        hV
  have hVmem : ∀ n (y : M) (h : y ∈ Wp n),
      V n y = greenEnvelope (⟨p₀, hp₀W n⟩ : ↥(Wp n)) ⟨y, h⟩ := by
    intro n y h
    simp only [hV]
    rw [dif_pos h]
  have hVzero : ∀ n (y : M), y ∉ Wp n → V n y = 0 := by
    intro n y h
    simp only [hV]
    rw [dif_neg h]
  /- ## Zero extension of a piece family member into the surface family. -/
  have brickE : ∀ n (v : ↥(Wp n) → ℝ), v ∈ greenFamily (⟨p₀, hp₀W n⟩ : ↥(Wp n))
      →
      ∃ w : M → ℝ, w ∈ greenFamily p₀ ∧ (∀ z : ↥(Wp n), w z = v z) ∧
        ∃ Kw : Set M, IsCompact Kw ∧ Kw ⊆ (Wp n : Set M) ∧ ∀ y, y ∉ Kw → w y = 0 := by
    intro n v hv
    obtain ⟨hvsub, hvcont, ⟨K, hKcomp, -, hKzero⟩, ⟨C, hC⟩⟩ := hv
    set w : M → ℝ := fun y => if h : y ∈ Wp n then v ⟨y, h⟩ else 0 with hwdef
    have hwval : ∀ z : ↥(Wp n), w z = v z := by
      intro z
      simp only [hwdef]
      rw [dif_pos z.2]
    set Kw : Set M := Subtype.val '' K with hKwdef
    have hKwcomp : IsCompact Kw := hKcomp.image continuous_subtype_val
    have hKwsub : Kw ⊆ (Wp n : Set M) := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2
    have hKwzero : ∀ y, y ∉ Kw → w y = 0 := by
      intro y hy
      by_cases hyP : y ∈ Wp n
      · simp only [hwdef]
        rw [dif_pos hyP]
        apply hKzero
        intro hmem
        exact hy ⟨⟨y, hyP⟩, hmem, rfl⟩
      · simp only [hwdef]
        rw [dif_neg hyP]
    have hKwne : Kw ≠ Set.univ := by
      intro hcon
      have h1 : q ∈ Kw := by rw [hcon]; trivial
      exact hqW n (hKwsub h1)
    have hKwcl : IsClosed Kw := hKwcomp.isClosed
    have hwcont : ContinuousOn w {p₀}ᶜ := by
      intro y hy
      apply ContinuousAt.continuousWithinAt
      by_cases hyP : y ∈ Wp n
      · have hoe : IsOpenEmbedding (Subtype.val : ↥(Wp n) → M) :=
          (Wp n).2.isOpenEmbedding_subtypeVal
        have hnz : (⟨y, hyP⟩ : ↥(Wp n)) ≠ ⟨p₀, hp₀W n⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        have hvat : ContinuousAt v (⟨y, hyP⟩ : ↥(Wp n)) :=
          hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr hnz))
        have h1 : Tendsto (w ∘ Subtype.val) (𝓝 (⟨y, hyP⟩ : ↥(Wp n))) (𝓝 (w y)) := by
          have h2 : w y = v ⟨y, hyP⟩ := hwval ⟨y, hyP⟩
          rw [h2]
          exact Filter.Tendsto.congr (fun u => (hwval u).symm) hvat
        have h4 : Filter.map (Subtype.val : ↥(Wp n) → M) (𝓝 (⟨y, hyP⟩ : ↥(Wp n))) =
            𝓝 y := hoe.map_nhds_eq ⟨y, hyP⟩
        have h5 : Tendsto w (𝓝 y) (𝓝 (w y)) := by
          rw [← h4, Filter.tendsto_map'_iff]
          exact h1
        exact h5
      · have hev : w =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hKwcl.isOpen_compl.mem_nhds
            (fun hmem => hyP (hKwsub hmem))] with u hu
          exact hKwzero u hu
        exact continuousAt_const.congr_of_eventuallyEq hev
    have hwsub : MSubharmonicOn w {p₀}ᶜ := by
      intro y hy
      by_cases hyP : y ∈ Wp n
      · have hnz : (⟨y, hyP⟩ : ↥(Wp n)) ≠ ⟨p₀, hp₀W n⟩ := fun hcon =>
          (Set.mem_compl_singleton_iff.mp hy) (congrArg Subtype.val hcon)
        exact (msub_val (Wp n) w v hwval ⟨y, hyP⟩).mpr
          (hvsub ⟨y, hyP⟩ (Set.mem_compl_singleton_iff.mpr hnz))
      · exact msub_zero w Kwᶜ y hKwcl.isOpen_compl
          (fun hmem => hyP (hKwsub hmem)) (fun z hz => hKwzero z hz)
    have hwpole : ∃ C', ∀ᶠ y' in 𝓝[≠] p₀, w y' + Real.log ‖poleCoord p₀ y'‖ ≤
        C' := by
      refine ⟨C, ?_⟩
      rw [← hmapval (Wp n) (hp₀W n), Filter.eventually_map]
      filter_upwards [hC] with z hz
      have hpc : poleCoord (⟨p₀, hp₀W n⟩ : ↥(Wp n)) z = poleCoord p₀ (z : M) := rfl
      rw [hwval z]
      rw [← hpc]
      exact hz
    exact ⟨w, ⟨hwsub, hwcont, ⟨Kw, hKwcomp, hKwne, hKwzero⟩, hwpole⟩, hwval,
      Kw, hKwcomp, hKwsub, hKwzero⟩
  /- ## Restriction of a compactly supported surface member into a piece family. -/
  have brickR : ∀ m (w : M → ℝ) (Kw : Set M),
      MSubharmonicOn w {p₀}ᶜ → ContinuousOn w {p₀}ᶜ →
      IsCompact Kw → Kw ⊆ (Wp m : Set M) → (∀ y, y ∉ Kw → w y = 0) →
      (∃ C, ∀ᶠ y' in 𝓝[≠] p₀, w y' + Real.log ‖poleCoord p₀ y'‖ ≤ C) →
      (fun z : ↥(Wp m) => w z) ∈ greenFamily (⟨p₀, hp₀W m⟩ : ↥(Wp m)) := by
    intro m w Kw hwsub hwcont hKwcomp hKwsub hKwzero hwpole
    haveI := hNcW m
    have hKpre : IsCompact (Subtype.val ⁻¹' Kw : Set ↥(Wp m)) := by
      haveI : CompactSpace ↥Kw := isCompact_iff_compactSpace.mp hKwcomp
      have himgK : (Subtype.val ⁻¹' Kw : Set ↥(Wp m)) =
          (fun z : ↥Kw => (⟨z.1, hKwsub z.2⟩ : ↥(Wp m))) '' Set.univ := by
        ext z
        constructor
        · intro hz
          exact ⟨⟨z.1, hz⟩, Set.mem_univ _, rfl⟩
        · rintro ⟨u, -, rfl⟩
          exact u.2
      rw [himgK]
      exact isCompact_univ.image (continuous_subtype_val.subtype_mk _)
    refine ⟨?_, ?_, ⟨Subtype.val ⁻¹' Kw, hKpre, ?_, fun z hz => hKwzero z hz⟩, ?_⟩
    · intro z hz
      have hzp : (z : M) ≠ p₀ := fun hcon =>
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      exact (msub_val (Wp m) w _ (fun _ => rfl) z).mp
        (hwsub z (Set.mem_compl_singleton_iff.mpr hzp))
    · intro z hz
      have hzp : (z : M) ≠ p₀ := fun hcon =>
        (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      have h1 : ContinuousAt w (z : M) :=
        hwcont.continuousAt (isOpen_compl_singleton.mem_nhds hzp)
      exact (h1.comp continuous_subtype_val.continuousAt).continuousWithinAt
    · intro hcon
      rw [hcon] at hKpre
      exact NoncompactSpace.noncompact_univ hKpre
    · obtain ⟨C, hC⟩ := hwpole
      refine ⟨C, ?_⟩
      have h2 : ∀ᶠ y' in Filter.map (Subtype.val : ↥(Wp m) → M)
          (𝓝[≠] (⟨p₀, hp₀W m⟩ : ↥(Wp m))), w y' + Real.log ‖poleCoord p₀ y'‖
              ≤ C := by
        rw [hmapval (Wp m) (hp₀W m)]
        exact hC
      rw [Filter.eventually_map] at h2
      filter_upwards [h2] with z hz
      have hpc : poleCoord (⟨p₀, hp₀W m⟩ : ↥(Wp m)) z = poleCoord p₀ (z : M) := rfl
      rw [hpc]
      exact hz
  /- ## Boundedness at the test point, positivity, monotonicity of the `V n`. -/
  have hVx : ∀ n, V n x ≤ B' := by
    intro n
    rw [hVmem n x (hxW n)]
    simp only [greenEnvelope]
    refine Real.sSup_le ?_ hB'0
    rintro a ⟨v, hvmem, rfl⟩
    obtain ⟨w, hwfam, hwval, -⟩ := brickE n v hvmem
    have h1 : w x ∈ (fun v => v x) '' greenFamily p₀ := ⟨w, hwfam, rfl⟩
    have h2 : w x ≤ s := hs h1
    have h3 : w x = v ⟨x, hxW n⟩ := hwval ⟨x, hxW n⟩
    exact (le_of_eq h3.symm).trans (h2.trans (le_max_left s 0))
  have hVnonneg : ∀ n (y : M), y ≠ p₀ → 0 ≤ V n y := by
    intro n y hy
    by_cases hyP : y ∈ Wp n
    · rw [hVmem n y hyP]
      exact (hEnvPos n ⟨y, hyP⟩ (fun hcon => hy (congrArg Subtype.val hcon))).le
    · rw [hVzero n y hyP]
  have hVmono : ∀ (y : M), y ≠ p₀ → Monotone fun n => V n y := by
    intro y hy n m hnm
    simp only
    by_cases hyn : y ∈ Wp n
    · have hym : y ∈ Wp m := hWmono n m hnm hyn
      rw [hVmem n y hyn, hVmem m y hym]
      simp only [greenEnvelope]
      refine Real.sSup_le ?_ ?_
      · rintro a ⟨v, hvmem, rfl⟩
        obtain ⟨w, hwfam, hwval, Kw, hKwc, hKws, hKw0⟩ := brickE n v hvmem
        have hwmem' : (fun z : ↥(Wp m) => w z) ∈ greenFamily (⟨p₀, hp₀W m⟩ : ↥(Wp m))
            :=
          brickR m w Kw hwfam.1 hwfam.2.1 hKwc (hKws.trans (hWmono n m hnm)) hKw0
            hwfam.2.2.2
        have h4 : v ⟨y, hyn⟩ = (fun z : ↥(Wp m) => w z) ⟨y, hym⟩ := (hwval ⟨y,
            hyn⟩).symm
        exact (le_of_eq h4).trans (le_csSup ((hEnvH m).2 ⟨y, hym⟩
          (fun hcon => hy (congrArg Subtype.val hcon))) ⟨_, hwmem', rfl⟩)
      · exact (hEnvPos m ⟨y, hym⟩ (fun hcon => hy (congrArg Subtype.val hcon))).le
    · rw [hVzero n y hyn]
      exact hVnonneg m y hy
  /- ## The monotone limit is harmonic away from the pole and the auxiliary point. -/
  set gs : M → ℝ := fun y => ⨆ n, V n y with hgs
  have hblock : ∀ (n₀ : ℕ) (y : M), y ∈ Wp n₀ → y ≠ p₀ →
      MHarmonicAt gs y ∧ ∀ n, V n y ≤ gs y := by
    intro n₀
    set Ω : Opens M := ⟨(Wp n₀ : Set M) ∩ {p₀}ᶜ,
      (Wp n₀).2.inter isOpen_compl_singleton⟩ with hΩ
    haveI := hConnW n₀
    have hnt : ∃ a b : ↥(Wp n₀), a ≠ b :=
      ⟨⟨x, hxW n₀⟩, ⟨p₀, hp₀W n₀⟩, fun hcon => hx (congrArg Subtype.val hcon)⟩
    have hpcn : IsConnected ({(⟨p₀, hp₀W n₀⟩ : ↥(Wp n₀))}ᶜ : Set ↥(Wp n₀)) :=
      isConnected_compl_singleton_of_connected hnt _
    have himgc : Subtype.val '' ({(⟨p₀, hp₀W n₀⟩ : ↥(Wp n₀))}ᶜ : Set ↥(Wp n₀)) =
        (Wp n₀ : Set M) ∩ {p₀}ᶜ := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z.2, ?_⟩
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact (Set.mem_compl_singleton_iff.mp hz) (Subtype.ext hcon)
      · rintro ⟨hyP, hyne⟩
        refine ⟨⟨y, hyP⟩, ?_, rfl⟩
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact hyne (congrArg Subtype.val hcon)
    have hΩconn : IsConnected ((Wp n₀ : Set M) ∩ {p₀}ᶜ) := by
      rw [← himgc]
      exact hpcn.image _ continuous_subtype_val.continuousOn
    haveI hΩcs : ConnectedSpace ↥Ω := isConnected_iff_connectedSpace.mp hΩconn
    have hzW : ∀ (k : ℕ) (z : ↥Ω), (z : M) ∈ Wp (n₀ + k) :=
      fun k z => hWmono n₀ (n₀ + k) (Nat.le_add_right n₀ k) z.2.1
    have hznp : ∀ z : ↥Ω, (z : M) ≠ p₀ := fun z => z.2.2
    have hVharmAt : ∀ (k : ℕ) (y : M) (h1 : y ∈ Wp (n₀ + k)), y ≠ p₀ →
        MHarmonicAt (V (n₀ + k)) y := by
      intro k y h1 hyp
      have h2 : MHarmonicAt (greenEnvelope (⟨p₀, hp₀W (n₀ + k)⟩ : ↥(Wp (n₀ + k))))
          (⟨y, h1⟩ : ↥(Wp (n₀ + k))) := by
        apply (hEnvH (n₀ + k)).1
        exact Set.mem_compl_singleton_iff.mpr
          (fun hcon => hyp (congrArg Subtype.val hcon))
      exact (mharm_val (Wp (n₀ + k)) (V (n₀ + k)) _
        (fun u => hVmem (n₀ + k) u u.2) ⟨y, h1⟩).mpr h2
    have hV'harm : ∀ k, MHarmonicOn (fun z : ↥Ω => V (n₀ + k) (z : M)) Set.univ := by
      intro k z _
      exact (mharm_val Ω (V (n₀ + k)) _ (fun _ => rfl) z).mp
        (hVharmAt k z (hzW k z) (hznp z))
    have hV'mono : ∀ z : ↥Ω, Monotone fun k => V (n₀ + k) (z : M) :=
      fun z k k' hkk' => hVmono (z : M) (hznp z) (Nat.add_le_add_left hkk' n₀)
    rcases mharmonic_dichotomy_of_monotone hV'harm hV'mono with hup | hlim
    · exfalso
      have hxΩ : x ∈ (Wp n₀ : Set M) ∩ {p₀}ᶜ :=
        ⟨hxW n₀, Set.mem_compl_singleton_iff.mpr hx⟩
      have h5 := (hup ⟨x, hxΩ⟩).eventually_gt_atTop B'
      obtain ⟨k, hk⟩ := h5.exists
      exact absurd (hVx (n₀ + k)) (not_le.mpr hk)
    · obtain ⟨VL, hVLharm, hVLtend⟩ := hlim
      have hid : ∀ z : ↥Ω, gs (z : M) = VL z ∧ ∀ n, V n (z : M) ≤ VL z := by
        intro z
        have hmonoz : Monotone fun n => V n (z : M) := hVmono _ (hznp z)
        have htail : ∀ k, V (n₀ + k) (z : M) ≤ VL z :=
          fun k => (hV'mono z).ge_of_tendsto (hVLtend z) k
        have hall : ∀ n, V n (z : M) ≤ VL z := fun n =>
          (hmonoz (Nat.le_add_left n n₀)).trans (htail n)
        have hbdd2 : BddAbove (Set.range fun n => V n (z : M)) := by
          refine ⟨VL z, ?_⟩
          rintro a ⟨n, rfl⟩
          exact hall n
        have htends : Tendsto (fun n => V n (z : M)) atTop (𝓝 (⨆ n, V n (z : M))) :=
          tendsto_atTop_ciSup hmonoz hbdd2
        have hcomp : Tendsto (fun k => V (n₀ + k) (z : M)) atTop
            (𝓝 (⨆ n, V n (z : M))) := by
          have h6 : Tendsto (fun k : ℕ => k + n₀) atTop atTop := tendsto_add_atTop_nat n₀
          have h7 := htends.comp h6
          have h8 : ((fun n => V n (z : M)) ∘ fun k : ℕ => k + n₀) =
              fun k => V (n₀ + k) (z : M) := by
            funext k
            simp only [Function.comp_apply, Nat.add_comm]
          rwa [h8] at h7
        have h9 : VL z = ⨆ n, V n (z : M) := tendsto_nhds_unique (hVLtend z) hcomp
        exact ⟨h9.symm, hall⟩
      intro y hyW hyp
      have hyΩ : y ∈ (Wp n₀ : Set M) ∩ {p₀}ᶜ := ⟨hyW, Set.mem_compl_singleton_iff.mpr
          hyp⟩
      constructor
      · exact (mharm_val Ω gs VL (fun u => (hid u).1) ⟨y, hyΩ⟩).mpr
          (hVLharm ⟨y, hyΩ⟩ (Set.mem_univ _))
      · intro n
        exact le_of_le_of_eq ((hid ⟨y, hyΩ⟩).2 n) ((hid ⟨y, hyΩ⟩).1).symm
  have hgs_all : ∀ y : M, y ≠ p₀ → y ≠ q → MHarmonicAt gs y ∧ ∀ n, V n y ≤ gs y :=
      by
    intro y hyp hyq
    obtain ⟨n₀, hn₀⟩ := hWexh y hyq
    exact hblock n₀ y hn₀ hyp
  have hgs_nonneg : ∀ y : M, y ≠ p₀ → y ≠ q → 0 ≤ gs y :=
    fun y hyp hyq => (hVnonneg 0 y hyp).trans ((hgs_all y hyp hyq).2 0)
  have hgs_x : gs x ≤ B' := ciSup_le fun n => hVx n
  /- ## The uniform bound near the auxiliary point, via the annulus maximum principle. -/
  set ρ : ℝ := r / 2 with hρdef
  have hρ0 : 0 < ρ := half_pos hr0
  have hρr : ρ < r := half_lt_self hr0
  have hcballρ : closedBall (e q) ρ ⊆ e.target :=
    (closedBall_subset_closedBall hρr.le).trans D.closedBall_subset
  have hballρ : ball (e q) ρ ⊆ e.target := ball_subset_closedBall.trans hcballρ
  set Bimg : Set M := e.symm '' ball (e q) ρ with hBimg
  have hBopen : IsOpen Bimg := by
    rw [hBimg, himg e _ hballρ]
    exact e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hBsub : Bimg ⊆ D.closedCarrier := by
    rw [hBimg, hDcar]
    exact Set.image_mono (ball_subset_closedBall.trans
      (closedBall_subset_closedBall hρr.le))
  have hqB : q ∈ Bimg := ⟨e q, mem_ball_self hρ0, e.left_inv hqsrc⟩
  set Dρ : Set M := e.symm '' closedBall (e q) ρ with hDρ
  have hDρcl : IsClosed Dρ := ((isCompact_closedBall _ _).image_of_continuousOn
    (e.continuousOn_symm.mono hcballρ)).isClosed
  have hBDρ : Bimg ⊆ Dρ := by
    rw [hBimg, hDρ]
    exact Set.image_mono ball_subset_closedBall
  set S : Set M := e.symm '' sphere (e q) ρ with hSdef
  have hScomp : IsCompact S := (isCompact_sphere _ _).image_of_continuousOn
    (e.continuousOn_symm.mono (sphere_subset_closedBall.trans hcballρ))
  have hSne : S.Nonempty := (NormedSpace.sphere_nonempty.mpr hρ0.le).image _
  have hSsub : S ⊆ D.closedCarrier := by
    rw [hSdef, hDcar]
    exact Set.image_mono (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall hρr.le))
  have hSq : ∀ y ∈ S, y ≠ q := by
    rintro y ⟨w, hw, rfl⟩ hcon
    have hwt : w ∈ e.target := hcballρ (sphere_subset_closedBall hw)
    have h1 : e (e.symm w) = w := e.right_inv hwt
    rw [hcon] at h1
    rw [mem_sphere] at hw
    rw [← h1, dist_self] at hw
    exact hρ0.ne hw
  have hSp₀ : ∀ y ∈ S, y ≠ p₀ := fun y hy => (hDavoid y (hSsub hy)).1
  have hSW : ∀ n, S ⊆ (Wp n : Set M) := by
    intro n
    rintro y ⟨w, hw, rfl⟩ hmem
    rw [hcarN n] at hmem
    obtain ⟨w', hw', hww'⟩ := hmem
    have hwt : w ∈ e.target := hcballρ (sphere_subset_closedBall hw)
    have hw't : w' ∈ e.target := D.closedBall_subset
      (closedBall_subset_closedBall (mul_le_of_le_one_left hr0.le (ht1 n)) hw')
    have heq2 : w' = w := e.symm.injOn (by rw [e.symm_source]; exact hw't)
      (by rw [e.symm_source]; exact hwt) hww'
    rw [mem_sphere] at hw
    rw [mem_closedBall, heq2, hw] at hw'
    have h3 : t n * r ≤ r / 4 := by
      have := mul_le_mul_of_nonneg_right (htq n) hr0.le
      linarith
    rw [hρdef] at hw'
    linarith
  have hgsScont : ContinuousOn gs S := fun y hy =>
    ((hgs_all y (hSp₀ y hy) (hSq y hy)).1.continuousAt).continuousWithinAt
  obtain ⟨yS, hySmem, hySmax⟩ := hScomp.exists_isMaxOn hSne hgsScont
  set B₀ : ℝ := max (gs yS) 0 with hB₀
  have hB₀0 : (0 : ℝ) ≤ B₀ := le_max_right _ _
  have hVann : ∀ n (y : M), y ∈ Bimg → y ∈ Wp n → V n y ≤ B₀ := by
    intro n y₀ hy₀B hy₀W
    rw [hVmem n y₀ hy₀W]
    simp only [greenEnvelope]
    refine Real.sSup_le ?_ hB₀0
    rintro a ⟨v, hvmem, rfl⟩
    obtain ⟨w, hwfam, hwval, Kw, hKwc, hKws, hKw0⟩ := brickE n v hvmem
    set A : Set M := Bimg \ (DN n).closedCarrier with hA
    have hAopen : IsOpen A := hBopen.sdiff (DN n).isCompact_closedCarrier.isClosed
    have hAp₀ : p₀ ∉ A := fun hmem => (hDavoid p₀ (hBsub hmem.1)).1 rfl
    have hAne : A ≠ Set.univ := fun hcon => hAp₀ (hcon ▸ Set.mem_univ p₀)
    have hAsubp : A ⊆ ({p₀}ᶜ : Set M) := fun z hz =>
      Set.mem_compl_singleton_iff.mpr (hDavoid z (hBsub hz.1)).1
    have hfr : ∀ z ∈ closure A \ A, ContinuousAt w z ∧ w z ≤ B₀ := by
      rintro z ⟨hzc, hzA⟩
      have hzD : z ∈ Dρ := hDρcl.closure_subset_iff.mpr
        (fun u hu => hBDρ hu.1) hzc
      by_cases hzcar : z ∈ (DN n).closedCarrier
      · have hzKw : z ∉ Kw := fun hmem => (hKws hmem) hzcar
        have hev : w =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
          filter_upwards [hKwc.isClosed.isOpen_compl.mem_nhds hzKw] with u hu
          exact hKw0 u hu
        refine ⟨continuousAt_const.congr_of_eventuallyEq hev, ?_⟩
        rw [hKw0 z hzKw]
        exact hB₀0
      · have hzB : z ∉ Bimg := fun hmem => hzA ⟨hmem, hzcar⟩
        have hzS : z ∈ S := by
          rw [hDρ] at hzD
          obtain ⟨ζ, hζ, hζz⟩ := hzD
          rw [mem_closedBall] at hζ
          rcases lt_or_eq_of_le hζ with hlt | heqd
          · exact absurd ⟨ζ, mem_ball.mpr hlt, hζz⟩ hzB
          · exact ⟨ζ, by rw [mem_sphere]; exact heqd, hζz⟩
        have hzp : z ≠ p₀ := hSp₀ z hzS
        refine ⟨hwfam.2.1.continuousAt (isOpen_compl_singleton.mem_nhds hzp), ?_⟩
        have hzW : z ∈ Wp n := hSW n hzS
        have h1 : w z = v ⟨z, hzW⟩ := hwval ⟨z, hzW⟩
        have h2 : v ⟨z, hzW⟩ ≤ V n z := by
          rw [hVmem n z hzW]
          exact le_csSup ((hEnvH n).2 ⟨z, hzW⟩
            (fun hcon => hzp (congrArg Subtype.val hcon))) ⟨v, hvmem, rfl⟩
        have h3 : V n z ≤ gs z := (hgs_all z hzp (hSq z hzS)).2 n
        have h4 : gs z ≤ gs yS := hySmax hzS
        rw [h1]
        exact ((h2.trans h3).trans h4).trans (le_max_left _ _)
    have hwA := maxPrin A w B₀ Kw hAopen hAne
      (fun z hz => hwfam.1 z (hAsubp hz)) hKwc
      (fun z _ hzK => (hKw0 z hzK).le.trans hB₀0) hfr
    exact (le_of_eq (hwval ⟨y₀, hy₀W⟩).symm).trans (hwA y₀ ⟨hy₀B, hy₀W⟩)
  have hgsB : ∀ y ∈ Bimg, y ≠ q → gs y ≤ B₀ := by
    intro y hyB hyq
    refine ciSup_le fun n => ?_
    by_cases hyW : y ∈ Wp n
    · exact hVann n y hyB hyW
    · rw [hVzero n y hyW]
      exact hB₀0
  /- ## Removability at the auxiliary point. -/
  have hharmU : HarmonicOnNhd (fun ζ => gs (e.symm ζ)) (ball (e q) ρ \ {e q}) := by
    rintro ζ ⟨hζ, hζq⟩
    have hζt : ζ ∈ e.target := hballρ hζ
    have hysrc : e.symm ζ ∈ e.source := e.map_target hζt
    have hyq : e.symm ζ ≠ q := by
      intro hcon
      apply hζq
      rw [Set.mem_singleton_iff, ← e.right_inv hζt, hcon]
    have hyp : e.symm ζ ≠ p₀ := (hDavoid _ (hBsub ⟨ζ, hζ, rfl⟩)).1
    have hMH : MHarmonicAt gs (e.symm ζ) := (hgs_all _ hyp hyq).1
    have h1 := (mharmonicAt_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas q) hysrc).mp hMH
    rw [e.right_inv hζt] at h1
    exact h1
  have hbddU : ∀ ζ ∈ ball (e q) ρ \ {e q}, |gs (e.symm ζ)| ≤ B₀ := by
    rintro ζ ⟨hζ, hζq⟩
    have hζt : ζ ∈ e.target := hballρ hζ
    have hyq : e.symm ζ ≠ q := by
      intro hcon
      apply hζq
      rw [Set.mem_singleton_iff, ← e.right_inv hζt, hcon]
    have hyp : e.symm ζ ≠ p₀ := (hDavoid _ (hBsub ⟨ζ, hζ, rfl⟩)).1
    rw [abs_le]
    constructor
    · linarith [hgs_nonneg (e.symm ζ) hyp hyq]
    · exact hgsB _ ⟨ζ, hζ, rfl⟩ hyq
  obtain ⟨hf, hfharm, hfeq⟩ :=
    exists_harmonicOnNhd_of_bounded_punctured hρ0 hharmU ⟨B₀, hbddU⟩
  set gh : M → ℝ := fun y => if y = q then hf (e q) else gs y with hgh
  have ghq : ∀ y : M, y ≠ q → gh y = gs y := by
    intro y hy
    simp only [hgh]
    rw [if_neg hy]
  have ghqq : gh q = hf (e q) := if_pos rfl
  have hghharm : MHarmonicOn gh {p₀}ᶜ := by
    intro y hy
    have hyp : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hy
    by_cases hyq : y = q
    · have hMH : MHarmonicAt (fun z => hf (e z)) q := by
        have h2 : HarmonicAt hf (e q) := hfharm _ (mem_ball_self hρ0)
        have h3 : ((fun z => hf (e z)) ∘ (e.symm : ℂ → M)) =ᶠ[𝓝 (e q)] hf := by
          filter_upwards [e.open_target.mem_nhds (e.map_source hqsrc)] with ζ hζ
          simp only [Function.comp_apply]
          rw [e.right_inv hζ]
        exact (harmonicAt_congr_nhds h3).mpr h2
      rw [hyq]
      refine mharm_congr (fun z => hf (e z)) gh q ?_ hMH
      filter_upwards [hBopen.mem_nhds hqB] with z hz
      obtain ⟨ζ, hζ, rfl⟩ := hz
      have hζt : ζ ∈ e.target := hballρ hζ
      by_cases hzq : e.symm ζ = q
      · rw [hzq, ghqq]
      · have hζq : ζ ≠ e q := by
          intro hcon
          apply hzq
          rw [hcon]
          exact e.left_inv hqsrc
        have h4 : hf ζ = gs (e.symm ζ) := hfeq ⟨hζ, hζq⟩
        rw [e.right_inv hζt, h4, ghq _ hzq]
    · refine mharm_congr gs gh y ?_ ((hgs_all y hyp hyq).1)
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hyq)] with z hz
      exact (ghq z (Set.mem_compl_singleton_iff.mp hz)).symm
  have hghx : gh x ≤ B' := by
    rw [ghq x hxq]
    exact hgs_x
  /- ## The truncated-logarithm family member at the pole. -/
  set ep : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with hep
  have hpsrc : p₀ ∈ ep.source := mem_chart_source ℂ p₀
  set cp : ℂ := ep p₀ with hcp
  have hUp : IsOpen (ep.target ∩ ep.symm ⁻¹' (D.closedCarrierᶜ ∩ {x}ᶜ)) :=
    ep.isOpen_inter_preimage_symm
      ((D.isCompact_closedCarrier.isClosed.isOpen_compl).inter isOpen_compl_singleton)
  have hcpU : cp ∈ ep.target ∩ ep.symm ⁻¹' (D.closedCarrierᶜ ∩ {x}ᶜ) := by
    refine ⟨ep.map_source hpsrc, ?_⟩
    rw [Set.mem_preimage, hcp, ep.left_inv hpsrc]
    exact ⟨fun hmem => (hDavoid p₀ hmem).1 rfl,
      Set.mem_compl_singleton_iff.mpr (Ne.symm hx)⟩
  obtain ⟨εp, hεp, hεpsub⟩ := Metric.isOpen_iff.mp hUp _ hcpU
  set rp : ℝ := εp / 2 with hrp
  have hrp0 : 0 < rp := half_pos hεp
  have hrpsub : closedBall cp rp ⊆ ep.target ∩ ep.symm ⁻¹' (D.closedCarrierᶜ ∩ {x}ᶜ) :=
    (Metric.closedBall_subset_ball (half_lt_self hεp)).trans hεpsub
  have hrpt : closedBall cp rp ⊆ ep.target := fun w hw => (hrpsub hw).1
  set Kp : Set M := ep.symm '' closedBall cp rp with hKpdef
  have hKpcomp : IsCompact Kp := (isCompact_closedBall _ _).image_of_continuousOn
    (ep.continuousOn_symm.mono hrpt)
  have hKpavoid : ∀ y ∈ Kp, y ∉ D.closedCarrier ∧ y ≠ x := by
    rintro y ⟨w, hw, rfl⟩
    have h2 := (hrpsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨h2.1, Set.mem_compl_singleton_iff.mp h2.2⟩
  have hKpW : ∀ n, Kp ⊆ (Wp n : Set M) :=
    fun n y hy hmem => (hKpavoid y hy).1 (hcarNsub n hmem)
  have hKpsrc : Kp ⊆ ep.source := by
    rintro y ⟨w, hw, rfl⟩
    exact ep.map_target (hrpt hw)
  have hexc : ∀ y, y ∈ ep.source → y ≠ p₀ → ep y ≠ cp := by
    intro y hys hyp heq
    exact hyp (ep.injOn hys hpsrc (by rw [← hcp]; exact heq))
  set gp : ℂ → ℝ := fun z => max (Real.log rp - Real.log ‖z - cp‖) 0 with hgp
  have hgpharm : HarmonicOnNhd (fun z => Real.log rp - Real.log ‖z - cp‖) {cp}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun u : ℂ => u - cp) z := analyticAt_id.sub analyticAt_const
    have hne2 : z - cp ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log rp)).sub (hana.harmonicAt_log_norm hne2)
  have hgpsub : SubharmonicOn gp {cp}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {cp}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hgpharm) h0
  have hgpzero : ∀ z, z ∉ ball cp rp → gp z = 0 := by
    intro z hz
    have hzr : rp ≤ ‖z - cp‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hle : Real.log rp ≤ Real.log ‖z - cp‖ := Real.log_le_log hrp0 hzr
    simp only [hgp]
    exact max_eq_right (by linarith)
  set v₀ : M → ℝ := fun y => if y ∈ ep.source then gp (ep y) else 0 with hv₀def
  have hv₀zero : ∀ y, y ∉ Kp → v₀ y = 0 := by
    intro y hy
    by_cases hys : y ∈ ep.source
    · simp only [hv₀def]
      rw [if_pos hys]
      apply hgpzero
      intro hball2
      exact hy ⟨ep y, ball_subset_closedBall hball2, ep.left_inv hys⟩
    · simp only [hv₀def]
      rw [if_neg hys]
  have hv₀sub : MSubharmonicOn v₀ {p₀}ᶜ := by
    intro y hy
    have hyp : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hy
    by_cases hys : y ∈ ep.source
    · refine (msubharmonicAt_iff_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas p₀) hys).mpr ?_
      have hopen2 : IsOpen (ep.target ∩ {cp}ᶜ) :=
        ep.open_target.inter isOpen_compl_singleton
      have hmem2 : ep y ∈ ep.target ∩ {cp}ᶜ :=
        ⟨ep.map_source hys, Set.mem_compl_singleton_iff.mpr (hexc y hys hyp)⟩
      obtain ⟨ρ', hρ', hρ'sub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
      have heqon : Set.EqOn gp (v₀ ∘ ep.symm) (ball (ep y) ρ') := by
        intro z hz
        have hzt : z ∈ ep.target := (hρ'sub hz).1
        have hzs : ep.symm z ∈ ep.source := ep.map_target hzt
        simp only [Function.comp_apply, hv₀def]
        rw [if_pos hzs, ep.right_inv hzt]
      exact ⟨ρ', hρ', fun z hz => (hρ'sub hz).1,
        transfer _ _ _ _ hgpsub (fun z hz => (hρ'sub hz).2) heqon⟩
    · have hyK : y ∉ Kp := fun hmem => hys (hKpsrc hmem)
      exact msub_zero v₀ Kpᶜ y hKpcomp.isClosed.isOpen_compl hyK
        (fun z hz => hv₀zero z hz)
  have hv₀cont : ContinuousOn v₀ {p₀}ᶜ := by
    intro y hy
    have hyp : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hy
    apply ContinuousAt.continuousWithinAt
    by_cases hys : y ∈ ep.source
    · have hgc : ContinuousAt gp (ep y) := hgpsub.1.continuousAt
        (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.mpr (hexc y hys hyp)))
      refine (hgc.comp (ep.continuousAt hys)).congr_of_eventuallyEq ?_
      filter_upwards [ep.open_source.mem_nhds hys] with u hu
      simp only [Function.comp_apply, hv₀def]
      rw [if_pos hu]
    · have hyK : y ∉ Kp := fun hmem => hys (hKpsrc hmem)
      have hev : v₀ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [hKpcomp.isClosed.isOpen_compl.mem_nhds hyK] with u hu
        exact hv₀zero u hu
      exact continuousAt_const.congr_of_eventuallyEq hev
  have hv₀pole : ∀ᶠ y' in 𝓝[≠] p₀, v₀ y' + Real.log ‖poleCoord p₀ y'‖ ≤
      Real.log rp := by
    have hopen2 : IsOpen (ep.source ∩ ep ⁻¹' ball cp rp) :=
      ep.continuousOn.isOpen_inter_preimage ep.open_source isOpen_ball
    have hnb : ep.source ∩ ep ⁻¹' ball cp rp ∈ 𝓝 p₀ := by
      refine hopen2.mem_nhds ⟨hpsrc, ?_⟩
      rw [Set.mem_preimage, ← hcp]
      exact mem_ball_self hrp0
    filter_upwards [nhdsWithin_le_nhds hnb, eventually_mem_nhdsWithin] with y hy hyp
    have hysrc : y ∈ ep.source := hy.1
    have hyne : y ≠ p₀ := Set.mem_compl_singleton_iff.mp hyp
    have hpole_eq : poleCoord p₀ y = ep y - cp := by
      simp only [poleCoord, ← hep, ← hcp]
    rw [hpole_eq]
    have hpos : 0 < ‖ep y - cp‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hexc y hysrc hyne))
    have hlt : ‖ep y - cp‖ < rp := by
      have hball2 : ep y ∈ ball cp rp := hy.2
      rw [mem_ball, dist_eq_norm] at hball2
      exact hball2
    have hBA : Real.log ‖ep y - cp‖ < Real.log rp := Real.log_lt_log hpos hlt
    simp only [hv₀def]
    rw [if_pos hysrc]
    simp only [hgp]
    rw [max_eq_left (by linarith)]
    linarith
  have hv₀piece : ∀ n, (fun z : ↥(Wp n) => v₀ z) ∈
      greenFamily (⟨p₀, hp₀W n⟩ : ↥(Wp n)) := fun n =>
    brickR n v₀ Kp hv₀sub hv₀cont hKpcomp (hKpW n) hv₀zero ⟨Real.log rp, hv₀pole⟩
  have hgs_ge : ∀ y : M, y ≠ p₀ → y ∈ Kp → v₀ y ≤ gs y := by
    intro y hyp hyK
    have hyq : y ≠ q := fun hcon => (hKpavoid y hyK).1 (hcon ▸ hqD)
    have hyW : y ∈ Wp 0 := hKpW 0 hyK
    have h1 : v₀ y ≤ V 0 y := by
      rw [hVmem 0 y hyW]
      exact le_csSup ((hEnvH 0).2 ⟨y, hyW⟩
        (fun hcon => hyp (congrArg Subtype.val hcon))) ⟨_, hv₀piece 0, rfl⟩
    exact h1.trans ((hgs_all y hyp hyq).2 0)
  /- ## The endgame: minimum principle on the compact surface. -/
  set σ : ℝ := rp * Real.exp (-(B' + 1)) with hσdef
  have hσ0 : 0 < σ := mul_pos hrp0 (Real.exp_pos _)
  have hσrp : σ < rp := by
    have h1 : Real.exp (-(B' + 1)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    calc σ = rp * Real.exp (-(B' + 1)) := rfl
      _ < rp * 1 := by
        apply mul_lt_mul_of_pos_left h1 hrp0
      _ = rp := mul_one rp
  have hlogσ : Real.log σ = Real.log rp - (B' + 1) := by
    rw [hσdef, Real.log_mul hrp0.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  set τ : ℝ := rp * Real.exp (-(B' + 1 / 2)) with hτdef
  have hτ0 : 0 < τ := mul_pos hrp0 (Real.exp_pos _)
  have hστ : σ < τ := by
    apply mul_lt_mul_of_pos_left _ hrp0
    exact Real.exp_lt_exp.mpr (by linarith)
  have hτrp : τ < rp := by
    have h1 : Real.exp (-(B' + 1 / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    calc τ = rp * Real.exp (-(B' + 1 / 2)) := rfl
      _ < rp * 1 := by
        apply mul_lt_mul_of_pos_left h1 hrp0
      _ = rp := mul_one rp
  have hlogτ : Real.log τ = Real.log rp - (B' + 1 / 2) := by
    rw [hτdef, Real.log_mul hrp0.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hσt : closedBall cp σ ⊆ ep.target :=
    (closedBall_subset_closedBall hσrp.le).trans hrpt
  set Dp : CoordDisk M := ⟨p₀, σ, hσ0, hσt⟩ with hDp
  have hDpcar : Dp.closedCarrier = ep.symm '' closedBall cp σ := rfl
  set Uσ : Set M := ep.symm '' ball cp σ with hUσ
  have hUσopen : IsOpen Uσ := by
    rw [hUσ, himg ep _ (ball_subset_closedBall.trans hσt)]
    exact ep.continuousOn.isOpen_inter_preimage ep.open_source isOpen_ball
  have hp₀Uσ : p₀ ∈ Uσ := ⟨cp, mem_ball_self hσ0, by rw [hcp]; exact ep.left_inv hpsrc⟩
  have hUσC : Uσ ⊆ Dp.closedCarrier := by
    rw [hUσ, hDpcar]
    exact Set.image_mono ball_subset_closedBall
  have hCKp : Dp.closedCarrier ⊆ Kp := by
    rw [hDpcar, hKpdef]
    exact Set.image_mono (closedBall_subset_closedBall hσrp.le)
  set Kσ : Set M := Uσᶜ with hKσ
  have hKσcomp : IsCompact Kσ := hUσopen.isClosed_compl.isCompact
  have hKσp₀ : ∀ z ∈ Kσ, z ≠ p₀ := fun z hz hcon => hz (hcon ▸ hp₀Uσ)
  have hxKσ : x ∈ Kσ := fun hmem => (hKpavoid x (hCKp (hUσC hmem))).2 rfl
  have hKσcont : ContinuousOn gh Kσ := fun z hz =>
    ((hghharm z (Set.mem_compl_singleton_iff.mpr (hKσp₀ z hz))).continuousAt).continuousWithinAt
  obtain ⟨ym, hymK, hymmin⟩ := hKσcomp.exists_isMinOn ⟨x, hxKσ⟩ hKσcont
  have hymB : gh ym ≤ B' := (hymmin hxKσ).trans hghx
  have hτcb : cp + (τ : ℂ) ∈ closedBall cp rp := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg hτ0.le]
    exact hτrp.le
  set zst : M := ep.symm (cp + (τ : ℂ)) with hzst
  have hzstK : zst ∈ Kp := ⟨cp + τ, hτcb, rfl⟩
  have hzstval : ep zst = cp + τ := ep.right_inv (hrpt hτcb)
  have hzstnorm : ‖ep zst - cp‖ = τ := by
    rw [hzstval, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
  have hzstp₀ : zst ≠ p₀ := by
    intro hcon
    have h1 : ep p₀ = cp := rfl
    rw [hcon, h1, sub_self, norm_zero] at hzstnorm
    exact hτ0.ne hzstnorm
  have hzstq : zst ≠ q := fun hcon => (hKpavoid zst hzstK).1 (hcon ▸ hqD)
  have hzstCσ : zst ∉ Dp.closedCarrier := by
    rintro ⟨w, hw, hweq⟩
    have hwt : w ∈ ep.target := hσt hw
    have h1 : ep zst = w := by rw [← hweq, ep.right_inv hwt]
    rw [h1] at hzstnorm
    rw [mem_closedBall, dist_eq_norm, hzstnorm] at hw
    linarith
  have hv₀zst : B' + 1 / 2 ≤ v₀ zst := by
    have hsrc : zst ∈ ep.source := ep.map_target (hrpt hτcb)
    have h1 : v₀ zst = max (Real.log rp - Real.log ‖ep zst - cp‖) 0 := by
      simp only [hv₀def]
      rw [if_pos hsrc]
    rw [h1, hzstnorm, hlogτ]
    have h2 : Real.log rp - (Real.log rp - (B' + 1 / 2)) = B' + 1 / 2 := by ring
    rw [h2]
    exact le_max_left _ _
  have hgszst : B' + 1 / 2 ≤ gs zst := hv₀zst.trans (hgs_ge zst hzstp₀ hzstK)
  by_cases hymC : ym ∈ Dp.closedCarrier
  · -- The minimum sits on the σ-circle, where the truncated logarithm is `B' + 1`.
    obtain ⟨w, hw, hweq⟩ := hymC
    have hwt : w ∈ ep.target := hσt hw
    have hymval : ep ym = w := by rw [← hweq, ep.right_inv hwt]
    have hwnb : w ∉ ball cp σ := fun hcon => hymK ⟨w, hcon, hweq⟩
    have hwσ : ‖w - cp‖ = σ := by
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_eq_norm, not_lt] at hwnb
      linarith
    have hymp₀ : ym ≠ p₀ := hKσp₀ ym hymK
    have hymKp : ym ∈ Kp := hCKp ⟨w, hw, hweq⟩
    have hymq : ym ≠ q := fun hcon => (hKpavoid ym hymKp).1 (hcon ▸ hqD)
    have hymsrc : ym ∈ ep.source := by
      rw [← hweq]
      exact ep.map_target hwt
    have hv₀ym : v₀ ym = max (Real.log rp - Real.log σ) 0 := by
      simp only [hv₀def]
      rw [if_pos hymsrc, hymval]
      simp only [hgp]
      rw [hwσ]
    have hchain : B' + 1 ≤ gh ym := by
      rw [ghq ym hymq]
      have h2 : v₀ ym ≤ gs ym := hgs_ge ym hymp₀ hymKp
      rw [hv₀ym, hlogσ] at h2
      have h3 : Real.log rp - (Real.log rp - (B' + 1)) = B' + 1 := by ring
      rw [h3] at h2
      exact (le_max_left _ _).trans h2
    linarith
  · -- The minimum is interior: the strong minimum principle makes `gh` constant on the
    -- connected complement of the σ-disk, contradicting the growth at the witness point.
    have hymΩ : ym ∈ (Dp.compl : Set M) := hymC
    have hΩσconn : IsConnected (Dp.compl : Set M) := isConnected_coordDisk_compl Dp
    have hΩσopen : IsOpen (Dp.compl : Set M) :=
      Dp.isCompact_closedCarrier.isClosed.isOpen_compl
    have hΩσp₀ : ∀ z ∈ (Dp.compl : Set M), z ≠ p₀ := by
      intro z hz hcon
      exact hz (hcon ▸ hUσC hp₀Uσ)
    have hsubΩ : MSubharmonicOn (-gh) (Dp.compl : Set M) := fun z hz =>
      ((hghharm z (Set.mem_compl_singleton_iff.mpr (hΩσp₀ z hz))).neg).msubharmonicAt
    have hmaxΩ : ∀ z ∈ (Dp.compl : Set M), (-gh) z ≤ (-gh) ym := by
      intro z hz
      simp only [Pi.neg_apply]
      have h5 : gh ym ≤ gh z := hymmin (fun hmem => hz (hUσC hmem))
      linarith
    have hconst := propagate (Dp.compl : Set M) (-gh) ym hΩσopen
      hΩσconn.isPreconnected hymΩ hsubΩ hmaxΩ
    have h6 := hconst zst hzstCσ
    simp only [Pi.neg_apply, neg_inj] at h6
    have h7 : gh zst ≤ B' := h6 ▸ hymB
    rw [ghq zst hzstq] at h7
    linarith

/-- **The non-hyperbolic case of planarity**: a simply connected surface
without a Green's function embeds onto a domain of the Riemann sphere via the
dipole map. -/
theorem exists_diffeomorph_opens_of_forall_not_hasGreenFunction
    [SimplyConnectedSpace M] [SecondCountableTopology M]
    (hnon : ∀ p₀ : M, ¬ HasGreenFunction p₀) :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  classical
  /- ## Two distinct points and a disk center, all in one chart ball. -/
  obtain ⟨p₁⟩ : Nonempty M := inferInstance
  have hp₁src : p₁ ∈ (chartAt ℂ p₁).source := mem_chart_source ℂ p₁
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp (chartAt ℂ p₁).open_target
    (chartAt ℂ p₁ p₁) ((chartAt ℂ p₁).map_source hp₁src)
  have hmemt : ∀ t : ℝ, 0 < t → t < r₀ →
      chartAt ℂ p₁ p₁ + (t : ℂ) ∈ (chartAt ℂ p₁).target := by
    intro t ht0 htr
    apply hball₀
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
    exact htr
  have h2mem : chartAt ℂ p₁ p₁ + ((r₀ / 2 : ℝ) : ℂ) ∈ (chartAt ℂ p₁).target :=
    hmemt _ (by linarith) (by linarith)
  have h4mem : chartAt ℂ p₁ p₁ + ((r₀ / 4 : ℝ) : ℂ) ∈ (chartAt ℂ p₁).target :=
    hmemt _ (by linarith) (by linarith)
  have hsymmne : ∀ t : ℝ, 0 < t → t < r₀ →
      (chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + (t : ℂ)) ≠ p₁ := by
    intro t ht0 htr hcon
    have h1 : chartAt ℂ p₁ ((chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + (t : ℂ)))
        = chartAt ℂ p₁ p₁ + (t : ℂ) := (chartAt ℂ p₁).right_inv (hmemt t ht0 htr)
    rw [hcon] at h1
    have h2 : chartAt ℂ p₁ p₁ + (t : ℂ) = chartAt ℂ p₁ p₁ + 0 := by
      rw [add_zero]; exact h1.symm
    have h3 : (t : ℂ) = 0 := add_left_cancel h2
    rw [Complex.ofReal_eq_zero] at h3
    exact ht0.ne' h3
  set p₂ : M := (chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + ((r₀ / 2 : ℝ) : ℂ)) with
      hp₂def
  set q : M := (chartAt ℂ p₁).symm (chartAt ℂ p₁ p₁ + ((r₀ / 4 : ℝ) : ℂ)) with hqdef
  have hp₁p₂ : p₁ ≠ p₂ := fun hcon =>
    hsymmne (r₀ / 2) (by linarith) (by linarith) hcon.symm
  have hp₁q : p₁ ≠ q := fun hcon =>
    hsymmne (r₀ / 4) (by linarith) (by linarith) hcon.symm
  have hp₂q : p₂ ≠ q := by
    intro hcon
    rw [hp₂def, hqdef] at hcon
    have h1 := congrArg (⇑(chartAt ℂ p₁)) hcon
    rw [(chartAt ℂ p₁).right_inv h2mem, (chartAt ℂ p₁).right_inv h4mem] at h1
    have h2 : ((r₀ / 2 : ℝ) : ℂ) = ((r₀ / 4 : ℝ) : ℂ) := add_left_cancel h1
    rw [Complex.ofReal_inj] at h2
    linarith
  /- ## The coordinate disk at `q` avoiding both poles. -/
  set e₀ : OpenPartialHomeomorph M ℂ := chartAt ℂ q with he₀def
  have hqsrc : q ∈ e₀.source := mem_chart_source ℂ q
  have hUopen : IsOpen (e₀.target ∩ ⇑e₀.symm ⁻¹' ({p₁}ᶜ ∩ {p₂}ᶜ)) :=
    e₀.isOpen_inter_preimage_symm (isOpen_compl_singleton.inter isOpen_compl_singleton)
  have hqU : e₀ q ∈ e₀.target ∩ ⇑e₀.symm ⁻¹' ({p₁}ᶜ ∩ {p₂}ᶜ) := by
    refine ⟨e₀.map_source hqsrc, ?_⟩
    rw [Set.mem_preimage, e₀.left_inv hqsrc]
    exact ⟨Set.mem_compl_singleton_iff.mpr hp₁q.symm,
      Set.mem_compl_singleton_iff.mpr hp₂q.symm⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hUopen _ hqU
  have hra0 : (0 : ℝ) < εa / 2 := half_pos hεa
  have hrsub : closedBall (e₀ q) (εa / 2) ⊆ e₀.target ∩ ⇑e₀.symm ⁻¹' ({p₁}ᶜ ∩
      {p₂}ᶜ) :=
    (Metric.closedBall_subset_ball (half_lt_self hεa)).trans hballa
  set D₀ : CoordDisk M := ⟨q, εa / 2, hra0, fun w hw => (hrsub hw).1⟩ with hD₀def
  have hD₀car : D₀.closedCarrier = e₀.symm '' closedBall (e₀ q) (εa / 2) := rfl
  have hD₀avoid : ∀ y ∈ D₀.closedCarrier, y ≠ p₁ ∧ y ≠ p₂ := by
    rintro y ⟨w, hw, rfl⟩
    have h2 := (hrsub hw).2
    rw [Set.mem_preimage] at h2
    exact ⟨Set.mem_compl_singleton_iff.mp h2.1, Set.mem_compl_singleton_iff.mp h2.2⟩
  have hp₁D : p₁ ∉ D₀.closedCarrier := fun hmem => (hD₀avoid p₁ hmem).1 rfl
  have hp₂D : p₂ ∉ D₀.closedCarrier := fun hmem => (hD₀avoid p₂ hmem).2 rfl
  /- ## The bipolar Green's function and the injective dipole map. -/
  obtain ⟨Gb, hGb, hpole₁, hpole₂, hbdd⟩ := exists_bipolarGreen D₀ hp₁D hp₂D hp₁p₂
  obtain ⟨φ, hφ, hφ₁, hφ₂, habs⟩ := exists_bipolar_map hp₁p₂ hGb hpole₁ hpole₂
  have hinj : Function.Injective φ :=
    injective_bipolar_map hnon hp₁p₂ hpole₁ hpole₂ hbdd hφ hφ₁ hφ₂ habs
  /- ## Plane-level helpers: an injective analytic map is locally open. -/
  have keyPlane : ∀ (g : ℂ → ℂ) (T : Set ℂ), IsOpen T → (∀ w ∈ T, AnalyticAt ℂ g
      w) →
      Set.InjOn g T → ∀ w ∈ T, 𝓝 (g w) ≤ Filter.map g (𝓝 w) := by
    intro g T hTopen hgan hginjT w hw
    rcases (hgan w hw).eventually_constant_or_nhds_le_map_nhds with hconst | hle
    · exfalso
      have h1 : ∀ᶠ w' in 𝓝[≠] w, g w' = g w ∧ w' ∈ T :=
        (hconst.and (hTopen.eventually_mem hw)).filter_mono nhdsWithin_le_nhds
      obtain ⟨w', ⟨hgw', hw'T⟩, hw'ne⟩ := (h1.and eventually_mem_nhdsWithin).exists
      exact hw'ne (Set.mem_singleton_iff.mpr (hginjT hw'T hw hgw'))
    · exact hle
  have imgOpen : ∀ (g : ℂ → ℂ) (T : Set ℂ), IsOpen T → (∀ w ∈ T, AnalyticAt ℂ g w)
      →
      Set.InjOn g T → ∀ S : Set ℂ, S ⊆ T → IsOpen S → IsOpen (g '' S) := by
    intro g T hTopen hgan hginjT S hST hSopen
    rw [isOpen_iff_mem_nhds]
    rintro ζ ⟨w, hwS, rfl⟩
    exact Filter.le_def.mp (keyPlane g T hTopen hgan hginjT w (hST hwS)) _
      (Filter.image_mem_map (hSopen.mem_nhds hwS))
  /- ## The dipole map is open: read it in charts around each point. -/
  have hopenM : IsOpenMap φ := by
    rw [isOpenMap_iff_nhds_le]
    intro x
    obtain ⟨χ, hxsrc, hχmax⟩ : ∃ χ : OpenPartialHomeomorph M ℂ,
        x ∈ χ.source ∧ χ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M :=
      ⟨chartAt ℂ x, mem_chart_source ℂ x, IsManifold.chart_mem_maximalAtlas x⟩
    obtain ⟨e, hφxsrc, hemax⟩ : ∃ e : OpenPartialHomeomorph ℂ̂ ℂ,
        φ x ∈ e.source ∧ e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
      ⟨chartAt ℂ (φ x), mem_chart_source ℂ (φ x),
        IsManifold.chart_mem_maximalAtlas (φ x)⟩
    have hTopen : IsOpen (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) :=
      χ.continuousOn_symm.isOpen_inter_preimage χ.open_target
        (e.open_source.preimage hφ.continuous)
    have hχxT : χ x ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source) := by
      refine ⟨χ.map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, Set.mem_preimage, χ.left_inv hxsrc]
      exact hφxsrc
    have hgan : ∀ w ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source),
        AnalyticAt ℂ (⇑e ∘ φ ∘ ⇑χ.symm) w := by
      intro w hw
      have hw2 : φ (χ.symm w) ∈ e.source := hw.2
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑χ.symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas hχmax hw.1
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ (χ.symm w) := hφ.contMDiffAt
      have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (φ (χ.symm w)) :=
        contMDiffAt_of_mem_maximalAtlas hemax hw2
      exact (contMDiffAt_iff_contDiffAt.mp
        ((h3.comp (χ.symm w) h2).comp w h1)).analyticAt
    have hginjT : Set.InjOn (⇑e ∘ φ ∘ ⇑χ.symm)
        (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) := by
      intro w₁ h₁ w₂ h₂ hgw
      have h₁2 : φ (χ.symm w₁) ∈ e.source := h₁.2
      have h₂2 : φ (χ.symm w₂) ∈ e.source := h₂.2
      have h3 : φ (χ.symm w₁) = φ (χ.symm w₂) := e.injOn h₁2 h₂2 hgw
      have h4 : χ.symm w₁ = χ.symm w₂ := hinj h3
      have h5 := congrArg (⇑χ) h4
      rwa [χ.right_inv h₁.1, χ.right_inv h₂.1] at h5
    have hle : 𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) (χ x)) ≤
        Filter.map (⇑e ∘ φ ∘ ⇑χ.symm) (𝓝 (χ x)) :=
      keyPlane _ _ hTopen hgan hginjT (χ x) hχxT
    have hev : φ =ᶠ[𝓝 x] ⇑e.symm ∘ (⇑e ∘ φ ∘ ⇑χ.symm) ∘ ⇑χ := by
      have hnb : χ.source ∩ φ ⁻¹' e.source ∈ 𝓝 x :=
        (χ.open_source.inter (e.open_source.preimage hφ.continuous)).mem_nhds
          ⟨hxsrc, hφxsrc⟩
      filter_upwards [hnb] with y hy
      have hy2 : φ y ∈ e.source := hy.2
      simp only [Function.comp_apply, χ.left_inv hy.1]
      exact (e.left_inv hy2).symm
    have hgx : (⇑e ∘ φ ∘ ⇑χ.symm) (χ x) = e (φ x) := by
      simp only [Function.comp_apply, χ.left_inv hxsrc]
    have h6 : Filter.map φ (𝓝 x) =
        Filter.map (⇑e.symm) (Filter.map (⇑e ∘ φ ∘ ⇑χ.symm) (𝓝 (χ x))) := by
      rw [Filter.map_congr hev, ← χ.map_nhds_eq hxsrc, Filter.map_map, Filter.map_map]
      rfl
    have h7 : 𝓝 (φ x) = Filter.map (⇑e.symm) (𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) (χ x))) :=
        by
      rw [hgx, e.symm_map_nhds_eq hφxsrc]
    rw [h6, h7]
    exact Filter.map_mono hle
  /- ## The image domain and the two structure maps. -/
  let U : Opens ℂ̂ := ⟨Set.range φ, hopenM.isOpen_range⟩
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : M => (⟨φ x, Set.mem_range_self x⟩ : ↥U)) := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (Subtype.val ∘ fun x : M => (⟨φ x, Set.mem_range_self x⟩ : ↥U)) x :=
      hφ.contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  /- ## Inverse smoothness: read the inverse through the sphere chart at the
  image point and a surface chart at the preimage point, where it is the
  local inverse of an injective analytic plane map. -/
  have hGsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥U => Function.invFun φ (y : ℂ̂)) :=
      by
    intro y₀
    obtain ⟨x₀, hφx₀⟩ : ∃ x, φ x = (y₀ : ℂ̂) := y₀.2
    obtain ⟨χ, hx₀src, hχmax⟩ : ∃ χ : OpenPartialHomeomorph M ℂ,
        x₀ ∈ χ.source ∧ χ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M :=
      ⟨chartAt ℂ x₀, mem_chart_source ℂ x₀, IsManifold.chart_mem_maximalAtlas x₀⟩
    obtain ⟨e, hy₀esrc, hemax⟩ : ∃ e : OpenPartialHomeomorph ℂ̂ ℂ,
        (y₀ : ℂ̂) ∈ e.source ∧ e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω ℂ̂ :=
      ⟨chartAt ℂ ((y₀ : ℂ̂)), mem_chart_source ℂ ((y₀ : ℂ̂)),
        IsManifold.chart_mem_maximalAtlas ((y₀ : ℂ̂))⟩
    have hφx₀src : φ x₀ ∈ e.source := by rw [hφx₀]; exact hy₀esrc
    have hTopen : IsOpen (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) :=
      χ.continuousOn_symm.isOpen_inter_preimage χ.open_target
        (e.open_source.preimage hφ.continuous)
    have hχx₀T : χ x₀ ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source) := by
      refine ⟨χ.map_source hx₀src, ?_⟩
      rw [Set.mem_preimage, Set.mem_preimage, χ.left_inv hx₀src]
      exact hφx₀src
    -- The chart reading of `φ` is analytic and injective near the base point.
    have hgan : ∀ w ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source),
        AnalyticAt ℂ (⇑e ∘ φ ∘ ⇑χ.symm) w := by
      intro w hw
      have hw2 : φ (χ.symm w) ∈ e.source := hw.2
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑χ.symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas hχmax hw.1
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ (χ.symm w) := hφ.contMDiffAt
      have h3 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) (φ (χ.symm w)) :=
        contMDiffAt_of_mem_maximalAtlas hemax hw2
      exact (contMDiffAt_iff_contDiffAt.mp
        ((h3.comp (χ.symm w) h2).comp w h1)).analyticAt
    have hginjT : Set.InjOn (⇑e ∘ φ ∘ ⇑χ.symm)
        (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) := by
      intro w₁ h₁ w₂ h₂ hgw
      have h₁2 : φ (χ.symm w₁) ∈ e.source := h₁.2
      have h₂2 : φ (χ.symm w₂) ∈ e.source := h₂.2
      have h3 : φ (χ.symm w₁) = φ (χ.symm w₂) := e.injOn h₁2 h₂2 hgw
      have h4 : χ.symm w₁ = χ.symm w₂ := hinj h3
      have h5 := congrArg (⇑χ) h4
      rwa [χ.right_inv h₁.1, χ.right_inv h₂.1] at h5
    obtain ⟨r, hr, hBsub⟩ := Metric.isOpen_iff.mp hTopen (χ x₀) hχx₀T
    -- The inverse chart reading.
    let η : ℂ → ℂ := fun ζ => χ (Function.invFun φ (e.symm ζ))
    have hηg : ∀ w ∈ ball (χ x₀) r, η ((⇑e ∘ φ ∘ ⇑χ.symm) w) = w := by
      intro w hwB
      have hwT := hBsub hwB
      have hwT2 : φ (χ.symm w) ∈ e.source := hwT.2
      have h5 : Function.invFun φ (φ (χ.symm w)) = χ.symm w :=
        Function.leftInverse_invFun hinj (χ.symm w)
      change χ (Function.invFun φ (e.symm (e (φ (χ.symm w))))) = w
      rw [e.left_inv hwT2, h5]
      exact χ.right_inv hwT.1
    -- The image `W` of the coordinate ball, an open plane neighborhood.
    have hWopen : IsOpen ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r) :=
      imgOpen _ _ hTopen hgan hginjT _ hBsub isOpen_ball
    have hy₀W : e (y₀ : ℂ̂) ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r := by
      refine ⟨χ x₀, mem_ball_self hr, ?_⟩
      simp only [Function.comp_apply]
      rw [χ.left_inv hx₀src, hφx₀]
    have himg : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        ∃ w ∈ ball (χ x₀) r, (⇑e ∘ φ ∘ ⇑χ.symm) w = ζ := by
      rintro ζ ⟨w, hwB, rfl⟩
      exact ⟨w, hwB, rfl⟩
    have hgη : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ) = ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
    have hηB : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r, η ζ ∈ ball (χ
        x₀) r := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
      exact hwB
    -- Continuity of the inverse reading, from openness of the reading.
    have hηc : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r, ContinuousAt η ζ :=
        by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      have hgoal : Filter.Tendsto η (𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) w)) (𝓝 w) := by
        rw [Filter.tendsto_def]
        intro N hN
        obtain ⟨N', hN'sub, hN'open, hwN'⟩ :=
          _root_.mem_nhds_iff.mp (Filter.inter_mem hN (isOpen_ball.mem_nhds hwB))
        have hsub' : N' ⊆ ball (χ x₀) r := fun z hz => (hN'sub hz).2
        have hopenimg : IsOpen ((⇑e ∘ φ ∘ ⇑χ.symm) '' N') :=
          imgOpen _ _ hTopen hgan hginjT _ (hsub'.trans hBsub) hN'open
        have hgmem : (⇑e ∘ φ ∘ ⇑χ.symm) w ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' N' :=
          ⟨w, hwN', rfl⟩
        refine Filter.mem_of_superset (hopenimg.mem_nhds hgmem) ?_
        rintro ζ' ⟨w', hw'N', rfl⟩
        rw [Set.mem_preimage, hηg w' (hsub' hw'N')]
        exact (hN'sub hw'N').1
      have hηw : η ((⇑e ∘ φ ∘ ⇑χ.symm) w) = w := hηg w hwB
      change Filter.Tendsto η (𝓝 ((⇑e ∘ φ ∘ ⇑χ.symm) w))
        (𝓝 (η ((⇑e ∘ φ ∘ ⇑χ.symm) w)))
      rw [hηw]
      exact hgoal
    -- Differentiability of the inverse reading at noncritical values.
    have hd_nc : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        deriv (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ) ≠ 0 → DifferentiableAt ℂ η ζ := by
      intro ζ hζ hder
      have hfd : HasDerivAt (⇑e ∘ φ ∘ ⇑χ.symm)
          (deriv (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ)) (η ζ) :=
        ((hgan (η ζ) (hBsub (hηB ζ hζ))).differentiableAt).hasDerivAt
      have hev : ∀ᶠ ζ' in 𝓝 ζ, (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ') = ζ' := by
        filter_upwards [hWopen.mem_nhds hζ] with ζ' hζ' using hgη ζ' hζ'
      exact (HasDerivAt.of_local_left_inverse (hηc ζ hζ) hfd hder hev).differentiableAt
    -- Critical points of the chart reading are isolated (injectivity).
    have hganN : AnalyticOnNhd ℂ (⇑e ∘ φ ∘ ⇑χ.symm)
        (χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source)) := fun w hw => hgan w hw
    have hcrit : ∀ w ∈ χ.target ∩ ⇑χ.symm ⁻¹' (φ ⁻¹' e.source),
        ∀ᶠ w' in 𝓝[≠] w, deriv (⇑e ∘ φ ∘ ⇑χ.symm) w' ≠ 0 := by
      intro w hw
      rcases (hganN.deriv w hw).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · exfalso
        obtain ⟨ρ, hρ0, hballρ⟩ :=
          Metric.eventually_nhds_iff_ball.mp (h0.and (hTopen.eventually_mem hw))
        have hconst : ∀ w' ∈ ball w ρ,
            (⇑e ∘ φ ∘ ⇑χ.symm) w' = (⇑e ∘ φ ∘ ⇑χ.symm) w := by
          intro w' hw'
          refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball w ρ)
            (fun u hu => ((hgan u (hballρ u hu).2).differentiableAt).differentiableWithinAt)
            ?_ hw' (mem_ball_self hρ0)
          intro u hu
          rw [fderivWithin_of_isOpen isOpen_ball hu]
          refine ContinuousLinearMap.ext_ring ?_
          rw [fderiv_apply_one_eq_deriv, (hballρ u hu).1]
          simp
        have hmem : w + ((ρ / 2 : ℝ) : ℂ) ∈ ball w ρ := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith
        have heq2 : w + ((ρ / 2 : ℝ) : ℂ) = w :=
          hginjT (hballρ _ hmem).2 hw (hconst _ hmem)
        have hρ2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
          have h4 : w + ((ρ / 2 : ℝ) : ℂ) = w + 0 := by rw [add_zero]; exact heq2
          exact add_left_cancel h4
        rw [Complex.ofReal_eq_zero] at hρ2
        linarith
      · exact hne
    -- Differentiability everywhere on `W` (removable singularity at critical values).
    have hdiff : ∀ ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r,
        DifferentiableAt ℂ η ζ := by
      intro ζ hζ
      by_cases hder : deriv (⇑e ∘ φ ∘ ⇑χ.symm) (η ζ) = 0
      swap
      · exact hd_nc ζ hζ hder
      obtain ⟨ρ, hρ0, hballρ⟩ := Metric.eventually_nhds_iff_ball.mp
        ((eventually_nhdsWithin_iff.mp (hcrit (η ζ) (hBsub (hηB ζ hζ)))).and
          (isOpen_ball.eventually_mem (hηB ζ hζ)))
      have hsub' : ball (η ζ) ρ ⊆ ball (χ x₀) r := fun z hz => (hballρ z hz).2
      have hW'open : IsOpen ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ) :=
        imgOpen _ _ hTopen hgan hginjT _ (hsub'.trans hBsub) isOpen_ball
      have hζW' : ζ ∈ (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ :=
        ⟨η ζ, mem_ball_self hρ0, hgη ζ hζ⟩
      have hW'W : (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ ⊆
          (⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r :=
        Set.image_mono hsub'
      have hoff : DifferentiableOn ℂ η
          (((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ) \ {ζ}) := by
        rintro ζ' ⟨hζ'W', hζ'ne⟩
        obtain ⟨w', hw'ball, rfl⟩ := hζ'W'
        refine (hd_nc _ (hW'W ⟨w', hw'ball, rfl⟩) ?_).differentiableWithinAt
        rw [hηg w' (hsub' hw'ball)]
        refine (hballρ w' hw'ball).1 ?_
        intro hmem
        apply hζ'ne
        rw [Set.mem_singleton_iff] at hmem ⊢
        rw [hmem]
        exact hgη ζ hζ
      have hW'diff : DifferentiableOn ℂ η ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (η ζ) ρ) :=
        (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
          (hW'open.mem_nhds hζW')).mp ⟨hoff, hηc ζ hζ⟩
      exact hW'diff.differentiableAt (hW'open.mem_nhds hζW')
    -- The inverse reading is analytic at the base point; assemble the composite.
    have hWdiff : DifferentiableOn ℂ η ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r) :=
      fun ζ hζ => (hdiff ζ hζ).differentiableWithinAt
    have hηan : AnalyticAt ℂ η (e (y₀ : ℂ̂)) := (hWdiff.analyticOnNhd hWopen) _ hy₀W
    have hval : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : ↥U → ℂ̂) y₀ :=
      contMDiff_subtype_val.contMDiffAt
    have hesm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑e) ((y₀ : ℂ̂)) :=
      contMDiffAt_of_mem_maximalAtlas hemax hy₀esrc
    have hηsm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω η (e (y₀ : ℂ̂)) :=
      contMDiffAt_iff_contDiffAt.mpr hηan.contDiffAt
    have hχsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑χ.symm) (η (e (y₀ : ℂ̂))) :=
      contMDiffAt_symm_of_mem_maximalAtlas hχmax (hBsub (hηB _ hy₀W)).1
    have hcomp2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        ((⇑χ.symm ∘ η ∘ ⇑e) ∘ (Subtype.val : ↥U → ℂ̂)) y₀ :=
      ContMDiffAt.comp y₀
        (ContMDiffAt.comp ((y₀ : ℂ̂)) hχsymm
          (ContMDiffAt.comp ((y₀ : ℂ̂)) hηsm hesm)) hval
    refine hcomp2.congr_of_eventuallyEq ?_
    have hSopen : IsOpen (e.source ∩ ⇑e ⁻¹' ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀)
        r)) :=
      e.continuousOn.isOpen_inter_preimage e.open_source hWopen
    have hy₀S : (y₀ : ℂ̂) ∈
        e.source ∩ ⇑e ⁻¹' ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r) :=
      ⟨hy₀esrc, hy₀W⟩
    have hmemS : (Subtype.val : ↥U → ℂ̂) ⁻¹'
        (e.source ∩ ⇑e ⁻¹' ((⇑e ∘ φ ∘ ⇑χ.symm) '' ball (χ x₀) r)) ∈ 𝓝 y₀
            :=
      (hSopen.preimage continuous_subtype_val).mem_nhds hy₀S
    filter_upwards [hmemS] with y hy
    obtain ⟨w, hwB, hgw⟩ := himg (e (y : ℂ̂)) hy.2
    have hwT := hBsub hwB
    have hwT2 : φ (χ.symm w) ∈ e.source := hwT.2
    have h7 : (y : ℂ̂) = φ (χ.symm w) := by
      have h8 := e.left_inv hy.1
      rw [← hgw] at h8
      have h9 : e.symm ((⇑e ∘ φ ∘ ⇑χ.symm) w) = φ (χ.symm w) := by
        simp only [Function.comp_apply]
        exact e.left_inv hwT2
      rw [← h8]
      exact h9
    change Function.invFun φ (y : ℂ̂) = χ.symm (η (e (y : ℂ̂)))
    rw [← hgw, hηg w hwB, h7, Function.leftInverse_invFun hinj (χ.symm w)]
  exact ⟨U, ⟨{
    toFun := fun x => ⟨φ x, Set.mem_range_self x⟩
    invFun := fun y => Function.invFun φ (y : ℂ̂)
    left_inv := fun x => Function.leftInverse_invFun hinj x
    right_inv := fun y => Subtype.ext (Function.invFun_eq y.2)
    contMDiff_toFun := hF
    contMDiff_invFun := hGsm }⟩⟩

end RiemannDynamics
