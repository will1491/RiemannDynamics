/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Uniformization.Perron.SurfaceHarmonic
import RiemannDynamics.Uniformization.HolomorphicEquiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The Green's function of a Riemann surface

The Perron construction of the Green's function with pole `p₀` on a Riemann
surface `M`: the envelope of the family of compactly supported continuous
subharmonic functions on `M ∖ {p₀}` with logarithmic pole growth at `p₀`.
Harnack's principle forces the dichotomy — either the envelope is harmonic off
the pole (`M` is hyperbolic at `p₀`) or it is unbounded at every point.

In the hyperbolic case the envelope `G` is positive, `G + log|z|` extends
harmonically across the pole, and on a simply connected surface the function
`φ = e^{−(G+iG*)}` (built by germ continuation and the monodromy argument)
is a global injective holomorphic map into the unit disc, yielding the
embedding of `M` onto a domain of the sphere.

## Main definitions

* `greenFamily p₀` — the Perron family with logarithmic pole at `p₀`;
* `greenEnvelope p₀` — its upper envelope;
* `HasGreenFunction p₀` — boundedness of the family at some point `≠ p₀`.

## Main statements

* `isConnected_compl_singleton_of_connected` — a connected surface stays
  connected after removing a point;
* `msubharmonic_le_zero_of_puncture` — the puncture-tolerant maximum
  principle;
* `mharmonicOn_greenEnvelope` — the Perron/Harnack dichotomy, hyperbolic case;
* `greenEnvelope_pos` — positivity;
* `exists_harmonic_pole_extension` — `G + log|z|` extends across the pole;
* `exists_green_map` — the global holomorphic `φ` with `|φ| = e^{−G}`
  (monodromy globalization);
* `injective_green_map` — injectivity of `φ`;
* `exists_diffeomorph_opens_complex_of_injective` — an injective holomorphic
  function on a surface is a biholomorphism onto a plane domain;
* `exists_diffeomorph_opens_of_hasGreenFunction` — the hyperbolic case of the
  planarity theorem.
-/

open Metric InnerProductSpace Topology Filter TopologicalSpace
open scoped Manifold ContDiff

namespace RiemannDynamics

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- The local coordinate at `p₀`, translated to vanish at `p₀`. -/
noncomputable def poleCoord (p₀ : M) (x : M) : ℂ :=
  chartAt ℂ p₀ x - chartAt ℂ p₀ p₀

/-- The Green's-function Perron family at `p₀`: continuous subharmonic
functions on the punctured surface, vanishing off a compact set, with
logarithmic pole growth at `p₀`. -/
def greenFamily (p₀ : M) : Set (M → ℝ) :=
  {v | MSubharmonicOn v {p₀}ᶜ ∧ ContinuousOn v {p₀}ᶜ ∧
    (∃ K : Set M, IsCompact K ∧ K ≠ Set.univ ∧ ∀ x ∉ K, v x = 0) ∧
    ∃ C, ∀ᶠ x in 𝓝[≠] p₀, v x + Real.log ‖poleCoord p₀ x‖ ≤ C}

/-- The upper envelope of the Green's-function Perron family. -/
noncomputable def greenEnvelope (p₀ : M) (x : M) : ℝ :=
  sSup ((fun v => v x) '' greenFamily p₀)

/-- The surface is hyperbolic at `p₀`: the Perron family is bounded above at
some point distinct from the pole. -/
def HasGreenFunction (p₀ : M) : Prop :=
  ∃ x, x ≠ p₀ ∧ BddAbove ((fun v => v x) '' greenFamily p₀)

/-! ## Surface toolkit -/

omit [IsManifold 𝓘(ℂ) ω M] in
/-- A connected surface with a point removed stays connected. -/
theorem isConnected_compl_singleton_of_connected [ConnectedSpace M]
    (hnt : ∃ x y : M, x ≠ y) (p₀ : M) : IsConnected ({p₀}ᶜ : Set M) := by
  haveI : T1Space M := ChartedSpace.t1Space ℂ M
  have hopen : IsOpen ({p₀}ᶜ : Set M) := isOpen_compl_singleton
  -- Nonemptiness of the punctured surface.
  obtain ⟨x, y, hxy⟩ := hnt
  have hne : ({p₀}ᶜ : Set M).Nonempty := by
    rcases eq_or_ne x p₀ with rfl | hx
    · exact ⟨y, Set.mem_compl_singleton_iff.2 hxy.symm⟩
    · exact ⟨x, Set.mem_compl_singleton_iff.2 hx⟩
  -- A punctured ball in `ℂ` is connected, via polar coordinates.
  have hpunc : ∀ (c : ℂ) (r : ℝ), 0 < r → IsConnected (ball c r \ {c}) := by
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
    refine ⟨Set.Nonempty.image _
      ⟨(r / 2, 0), ⟨half_pos hr, half_lt_self hr⟩, Set.mem_univ _⟩, ?_⟩
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn
  -- The punctured chart neighborhood of `p₀`.
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he
  have hp₀src : p₀ ∈ e.source := by rw [he]; exact mem_chart_source ℂ p₀
  have hctgt : e p₀ ∈ e.target := by rw [he]; exact mem_chart_target ℂ p₀
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p₀) hctgt
  set N : Set M := e.source ∩ e ⁻¹' ball (e p₀) r
  have hNopen : IsOpen N := e.isOpen_inter_preimage isOpen_ball
  have hp₀N : p₀ ∈ N := ⟨hp₀src, by rw [Set.mem_preimage]; exact mem_ball_self hr0⟩
  have himg : (e.symm : ℂ → M) '' (ball (e p₀) r \ {e p₀}) = N \ {p₀} := by
    apply Set.Subset.antisymm
    · rintro z ⟨w, ⟨hwb, hwc⟩, hwz⟩
      have hwt : w ∈ e.target := hball hwb
      rw [← hwz]
      refine ⟨⟨e.map_target hwt, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, e.right_inv hwt]; exact hwb
      · intro h
        rw [Set.mem_singleton_iff] at h
        exact hwc (by rw [Set.mem_singleton_iff, ← e.right_inv hwt, h])
    · rintro z ⟨⟨hzsrc, hzb⟩, hzp⟩
      refine ⟨e z, ⟨hzb, ?_⟩, e.left_inv hzsrc⟩
      intro h
      rw [Set.mem_singleton_iff] at h
      exact hzp (Set.mem_singleton_iff.2 (e.injOn hzsrc hp₀src h))
  have hN' : IsConnected (N \ {p₀}) := by
    rw [← himg]
    exact (hpunc (e p₀) r hr0).image _
      (e.continuousOn_symm.mono fun w hw => hball hw.1)
  have hsub' : N \ {p₀} ⊆ ({p₀}ᶜ : Set M) := fun z hz => hz.2
  -- Assemble preconnectedness of the punctured surface.
  refine ⟨hne, ?_⟩
  intro u v hu hv huv hsu hsv
  -- One-sided separation lemma: if the punctured chart neighborhood lies in `u'`,
  -- the separation `u', v'` of the punctured surface extends to a separation of `M`.
  have key : ∀ u' v' : Set M, IsOpen u' → IsOpen v' → ({p₀}ᶜ : Set M) ⊆ u' ∪ v' →
      (({p₀}ᶜ : Set M) ∩ v').Nonempty → N \ {p₀} ⊆ u' →
      (({p₀}ᶜ : Set M) ∩ (u' ∩ v')).Nonempty := by
    intro u' v' hu' hv' hcov hv'ne hNu'
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hU : IsOpen (u' ∪ N) := hu'.union hNopen
    have hV : IsOpen (v' ∩ ({p₀}ᶜ : Set M)) := hv'.inter hopen
    have hcover : (Set.univ : Set M) ⊆ (u' ∪ N) ∪ v' ∩ {p₀}ᶜ := by
      intro z _
      rcases eq_or_ne z p₀ with rfl | hz
      · exact Or.inl (Or.inr hp₀N)
      · rcases hcov (Set.mem_compl_singleton_iff.2 hz) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, Set.mem_compl_singleton_iff.2 hz⟩
    obtain ⟨w, hw1, hw2⟩ := hv'ne
    obtain ⟨z, -, hz⟩ := isPreconnected_univ (u' ∪ N) (v' ∩ {p₀}ᶜ) hU hV hcover
      ⟨p₀, Set.mem_univ p₀, Or.inr hp₀N⟩ ⟨w, Set.mem_univ w, hw2, hw1⟩
    obtain ⟨hz1, hzv, hzp⟩ := hz
    have hzu : z ∈ u' := by
      rcases hz1 with h | h
      · exact h
      · exact hNu' ⟨h, Set.mem_compl_singleton_iff.1 hzp⟩
    have : z ∈ ({p₀}ᶜ : Set M) ∩ (u' ∩ v') := ⟨hzp, hzu, hzv⟩
    rw [hcon] at this
    exact this
  -- Case split on which side of the separation the punctured chart ball lies.
  rcases Set.eq_empty_or_nonempty ((N \ {p₀}) ∩ v) with hv0 | hv1
  · have hNu : N \ {p₀} ⊆ u := by
      intro z hz
      rcases huv (hsub' hz) with h | h
      · exact h
      · exact absurd hv0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
    exact key u v hu hv huv hsv hNu
  · rcases Set.eq_empty_or_nonempty ((N \ {p₀}) ∩ u) with hu0 | hu1
    · have hNv : N \ {p₀} ⊆ v := by
        intro z hz
        rcases huv (hsub' hz) with h | h
        · exact absurd hu0 (Set.Nonempty.ne_empty ⟨z, hz, h⟩)
        · exact h
      have h := key v u hv hu (by rw [Set.union_comm]; exact huv) hsu hNv
      rwa [Set.inter_comm v u] at h
    · obtain ⟨z, hzN, hzuv⟩ := hN'.2 u v hu hv (fun z hz => huv (hsub' hz)) hu1 hv1
      exact ⟨z, hsub' hzN, hzuv⟩

/-- **Puncture-tolerant maximum principle**: a subharmonic function on the
punctured surface that vanishes off a compact set and has at most logarithmic
pole growth is nonpositive. -/
theorem msubharmonic_le_zero_of_puncture [ConnectedSpace M]
    [NoncompactSpace M] [T2Space M] {p₀ : M} {v : M → ℝ}
    (hv : MSubharmonicOn v {p₀}ᶜ)
    (hsupp : ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, v x ≤ 0)
    (hpole : ∃ C, ∀ᶠ x in 𝓝[≠] p₀, v x ≤ C) :
    ∀ x ≠ p₀, v x ≤ 0 := by
  classical
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℂ M
  obtain ⟨K, hK, hKv⟩ := hsupp
  obtain ⟨C, hC⟩ := hpole
  -- The surface has at least two points, else it would be compact.
  have hnt : ∃ x y : M, x ≠ y := by
    by_contra hcon
    push Not at hcon
    haveI : Subsingleton M := ⟨fun a b => hcon a b⟩
    haveI : CompactSpace M := Finite.compactSpace
    exact NoncompactSpace.noncompact_univ (X := M) isCompact_univ
  have hconn : IsConnected ({p₀}ᶜ : Set M) :=
    isConnected_compl_singleton_of_connected hnt p₀
  -- Continuity of `v` off the pole.
  have hvcont : ∀ y : M, y ≠ p₀ → ContinuousAt v y :=
    fun y hy => (hv y (Set.mem_compl_singleton_iff.mpr hy)).continuousAt
  -- A far point outside `K ∪ {p₀}`.
  have hfar : ∃ y₀ : M, y₀ ∉ K ∪ {p₀} := by
    by_contra hcon
    push Not at hcon
    have huniv : K ∪ {p₀} = Set.univ := Set.eq_univ_of_forall hcon
    have hcomp : IsCompact (K ∪ {p₀} : Set M) := hK.union isCompact_singleton
    rw [huniv] at hcomp
    exact NoncompactSpace.noncompact_univ (X := M) hcomp
  /- ## Constancy propagation on a preconnected open set from an interior
  maximum (clopen argument). -/
  have propagate : ∀ (Ω : Set M) (w : M → ℝ) (xm : M), IsOpen Ω → IsPreconnected Ω →
      xm ∈ Ω → MSubharmonicOn w Ω → (∀ x ∈ Ω, w x ≤ w xm) → ∀ x ∈ Ω, w x = w xm := by
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
  /- ## Maximum principle on an open set `Ω ≠ univ`: a subharmonic function
  bounded by `m` off a compact set and bounded by `m` (with continuity) at
  every point of `closure Ω \ Ω` is bounded by `m` on `Ω`. -/
  have maxPrin : ∀ (Ω : Set M) (w : M → ℝ) (m : ℝ) (Kc : Set M), IsOpen Ω →
      Ω ≠ Set.univ → MSubharmonicOn w Ω → IsCompact Kc →
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
    -- Propagate the max through the connected component of `xm`.
    have hCco : IsOpen (connectedComponentIn Ω xm) := hΩo.connectedComponentIn
    have hCcx : xm ∈ connectedComponentIn Ω xm := mem_connectedComponentIn hxmΩ
    have hCcΩ : connectedComponentIn Ω xm ⊆ Ω := connectedComponentIn_subset _ _
    have hconst := propagate (connectedComponentIn Ω xm) w xm hCco
      isPreconnected_connectedComponentIn hCcx
      (fun x hx => hwsub x (hCcΩ hx)) (fun x hx => hall x (hCcΩ hx))
    -- The component has a boundary point (else it would be all of `M`).
    have hfrne : (closure (connectedComponentIn Ω xm) \ connectedComponentIn Ω xm).Nonempty := by
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
    -- The boundary point is outside `Ω` (components of open sets are open).
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
    -- Continuity forces the maximal value at the boundary point: contradiction.
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
  /- ## Chart geometry at the pole. -/
  set e := chartAt ℂ p₀ with he
  have hp₀s : p₀ ∈ e.source := mem_chart_source ℂ p₀
  set z₀ := e p₀ with hz₀
  have hz₀t : z₀ ∈ e.target := by rw [hz₀]; exact e.map_source hp₀s
  have hsymz₀ : e.symm z₀ = p₀ := by rw [hz₀]; exact e.left_inv hp₀s
  -- Images under `e.symm` of subsets of the target, in preimage form.
  have himg : ∀ s : Set ℂ, s ⊆ e.target → e.symm '' s = e.source ∩ e ⁻¹' s := by
    intro s hs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e.map_target (hs hz), ?_⟩
      rw [Set.mem_preimage, e.right_inv (hs hz)]
      exact hz
    · rintro ⟨hy, hy2⟩
      exact ⟨e y, hy2, e.left_inv hy⟩
  -- A radius `r` on which the pole bound `v ≤ C` is valid.
  obtain ⟨N, hNnhds, hN⟩ := (eventually_nhdsWithin_iff.mp hC).exists_mem
  have hpre : e.target ∩ e.symm ⁻¹' N ∈ 𝓝 z₀ := by
    have h1 : ContinuousAt e.symm z₀ := e.continuousAt_symm hz₀t
    have h3 : e.symm ⁻¹' N ∈ 𝓝 z₀ := h1.preimage_mem_nhds (hsymz₀ ▸ hNnhds)
    exact Filter.inter_mem (e.open_target.mem_nhds hz₀t) h3
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall.mem_iff).1 hpre
  have hrt : closedBall z₀ r ⊆ e.target := fun z hz => (hrsub hz).1
  -- Detecting the pole through the chart.
  have hpid : ∀ y, y ∈ e.source → e y = z₀ → y = p₀ := by
    intro y hys hyz
    rw [← e.left_inv hys, hyz]
    exact hsymz₀
  have hnep : ∀ y, y ∈ e.source → e y ≠ z₀ → y ≠ p₀ := by
    intro y hys hyne hcon
    rw [hcon] at hyne
    exact hyne hz₀.symm
  -- The pole bound, read on the surface.
  have hCbound : ∀ y, y ∈ e.source → e y ∈ closedBall z₀ r → y ≠ p₀ → v y ≤ C := by
    intro y hys hyball hyne
    have h3 : e y ∈ e.symm ⁻¹' N := (hrsub hyball).2
    have h4 : y ∈ N := by rwa [Set.mem_preimage, e.left_inv hys] at h3
    exact hN y h4 (Set.mem_compl_singleton_iff.mpr hyne)
  /- ## The circle `Γ` and its maximum `m₁`. -/
  set Γ : Set M := e.symm '' (sphere z₀ r) with hΓdef
  have hΓcomp : IsCompact Γ := (isCompact_sphere z₀ r).image_of_continuousOn
    (e.continuousOn_symm.mono (sphere_subset_closedBall.trans hrt))
  have hΓne : Γ.Nonempty := (NormedSpace.sphere_nonempty.2 hr.le).image _
  have hΓmem : ∀ y, y ∈ e.source → dist (e y) z₀ = r → y ∈ Γ := by
    intro y hys hyd
    exact ⟨e y, by rwa [mem_sphere], e.left_inv hys⟩
  have hΓp₀ : Γ ⊆ {p₀}ᶜ := by
    rintro q ⟨z, hz, rfl⟩
    rw [mem_sphere] at hz
    have hzt : z ∈ e.target := hrt (sphere_subset_closedBall (by rwa [mem_sphere]))
    have hzne : z ≠ z₀ := by
      intro hcon
      rw [hcon, dist_self] at hz
      exact hr.ne hz
    rw [Set.mem_compl_singleton_iff]
    intro hcon
    apply hzne
    have h5 := e.right_inv hzt
    rw [hcon] at h5
    rw [hz₀]
    exact h5.symm
  have hΓcont : ContinuousOn v Γ :=
    fun q hq => (hvcont q (Set.mem_compl_singleton_iff.1 (hΓp₀ hq))).continuousWithinAt
  obtain ⟨xΓ, hxΓ, hxΓmax⟩ := hΓcomp.exists_isMaxOn hΓne hΓcont
  set m₁ : ℝ := max (v xΓ) 0 with hm₁
  have hm₁0 : (0 : ℝ) ≤ m₁ := le_max_right _ _
  have hΓle : ∀ y ∈ Γ, v y ≤ m₁ := fun y hy => (hxΓmax hy).trans (le_max_left _ _)
  /- ## The closed coordinate disk `D` and the outer estimate. -/
  set D : Set M := e.symm '' (closedBall z₀ r) with hDdef
  have hDcomp : IsCompact D := (isCompact_closedBall z₀ r).image_of_continuousOn
    (e.continuousOn_symm.mono hrt)
  have hDcl : IsClosed D := hDcomp.isClosed
  have hp₀D : p₀ ∈ D := by
    rw [hDdef, himg _ hrt]
    refine ⟨hp₀s, ?_⟩
    rw [Set.mem_preimage, ← hz₀]
    exact mem_closedBall_self hr.le
  -- Maximum principle outside the disk.
  have houterAll : ∀ x ∈ (Dᶜ : Set M), v x ≤ m₁ := by
    refine maxPrin Dᶜ v m₁ K hDcl.isOpen_compl ?_ ?_ hK ?_ ?_
    · intro hcon
      have h5 : p₀ ∈ (Dᶜ : Set M) := by rw [hcon]; trivial
      exact h5 hp₀D
    · exact fun q hq =>
        hv q (Set.mem_compl_singleton_iff.mpr (fun hcon => hq (hcon ▸ hp₀D)))
    · exact fun q _ hqK => (hKv q hqK).trans hm₁0
    · rintro y ⟨hycl, hyc⟩
      have hyD : y ∈ D := not_not.1 hyc
      rw [hDdef, himg _ hrt] at hyD
      obtain ⟨hysrc, hyball⟩ := hyD
      have hynb : e y ∉ ball z₀ r := by
        intro hcon
        have hBopen : IsOpen (e.source ∩ e ⁻¹' ball z₀ r) :=
          e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
        have hBsubD : e.source ∩ e ⁻¹' ball z₀ r ⊆ D := by
          rw [hDdef, himg _ hrt]
          exact Set.inter_subset_inter (subset_refl _)
            (Set.preimage_mono ball_subset_closedBall)
        have hyint : y ∈ interior D := interior_maximal hBsubD hBopen ⟨hysrc, hcon⟩
        rw [closure_compl] at hycl
        exact hycl hyint
      have hyr : dist (e y) z₀ = r := by
        rw [mem_ball] at hynb
        rw [Set.mem_preimage, mem_closedBall] at hyball
        exact le_antisymm hyball (not_lt.1 hynb)
      have hyneza : e y ≠ z₀ := by
        intro hcon
        rw [hcon, dist_self] at hyr
        exact hr.ne hyr
      have hynep : y ≠ p₀ := hnep y hysrc hyneza
      exact ⟨hvcont y hynep, hΓle y (hΓmem y hysrc hyr)⟩
  /- ## Harmonicity of the logarithmic barrier through the chart. -/
  have hbharm : ∀ y, y ∈ e.source → e y ≠ z₀ →
      MHarmonicAt (fun q => Real.log (dist (e q) z₀)) y := by
    intro y hys hyne
    rw [mharmonicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p₀) hys]
    have hharm : HarmonicAt (fun w : ℂ => Real.log ‖w - z₀‖) (e y) := by
      apply AnalyticAt.harmonicAt_log_norm (f := fun w : ℂ => w - z₀)
      · exact analyticAt_id.sub analyticAt_const
      · exact sub_ne_zero.2 hyne
    have heqv : (fun w : ℂ => Real.log ‖w - z₀‖) =ᶠ[𝓝 (e y)]
        ((fun q => Real.log (dist (e q) z₀)) ∘ ⇑e.symm) := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hys)] with w hw
      simp only [Function.comp_apply, e.right_inv hw, dist_eq_norm]
    exact (harmonicAt_congr_nhds heqv).1 hharm
  have hbcont : ∀ y, y ∈ e.source → e y ≠ z₀ →
      ContinuousAt (fun q => Real.log (dist (e q) z₀)) y := by
    intro y hys hyne
    have h2 : ContinuousAt e y := e.continuousAt hys
    have h3 : dist (e y) z₀ ≠ 0 := (dist_pos.2 hyne).ne'
    have h4 : ContinuousAt (fun q : M => dist (e q) z₀) y := h2.dist continuousAt_const
    exact h4.log h3
  -- Affine images of `MHarmonicAt` functions are `MHarmonicAt`.
  have mharm_affine : ∀ (g : M → ℝ) (x : M) (a c : ℝ), MHarmonicAt g x →
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
  /- ## Inner estimate: the `ε·log` barrier on the punctured disk. -/
  have hinner : ∀ x ∈ D, x ≠ p₀ → v x ≤ m₁ := by
    intro x hxD hxp
    rw [hDdef, himg _ hrt] at hxD
    obtain ⟨hxsrc, hxball⟩ := hxD
    rw [Set.mem_preimage, mem_closedBall] at hxball
    have hxz : e x ≠ z₀ := fun hcon => hxp (hpid x hxsrc hcon)
    have hdx0 : 0 < dist (e x) z₀ := dist_pos.2 hxz
    rcases eq_or_lt_of_le hxball with heqr | hdxlt
    · exact hΓle x (hΓmem x hxsrc heqr)
    -- Strict interior: show `v x ≤ m₁ + δ` for every `δ > 0`.
    refine le_of_forall_pos_le_add ?_
    intro δ hδ
    set L : ℝ := Real.log r - Real.log (dist (e x) z₀) with hLdef
    have hL0 : 0 < L := sub_pos.2 (Real.log_lt_log hdx0 hdxlt)
    set ε : ℝ := δ / L with hεdef
    have hε0 : 0 < ε := div_pos hδ hL0
    have hεL : ε * L = δ := by
      rw [hεdef]
      exact div_mul_cancel₀ δ hL0.ne'
    -- Excision radius `σ`, small enough for the barrier to beat `C`.
    set Q : ℝ := (m₁ - C) / ε + Real.log r with hQdef
    set σ : ℝ := min (dist (e x) z₀ / 2) (Real.exp Q) with hσdef
    have hσ0 : 0 < σ := lt_min (half_pos hdx0) (Real.exp_pos Q)
    have hσdx : σ < dist (e x) z₀ :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hdx0)
    have hσr : σ < r := hσdx.trans hdxlt
    have hσQ : Real.log σ ≤ Q := by
      calc Real.log σ ≤ Real.log (Real.exp Q) := Real.log_le_log hσ0 (min_le_right _ _)
        _ = Q := Real.log_exp Q
    have hbarrier : C + ε * (Real.log σ - Real.log r) ≤ m₁ := by
      have h5 : ε * (Real.log σ - Real.log r) ≤ ε * ((m₁ - C) / ε) := by
        apply mul_le_mul_of_nonneg_left _ hε0.le
        rw [hQdef] at hσQ
        linarith
      have h6 : ε * ((m₁ - C) / ε) = m₁ - C := by field_simp
      linarith
    -- The annulus and the barriered competitor.
    set O : Set ℂ := ball z₀ r \ closedBall z₀ σ with hOdef
    have hOopen : IsOpen O := isOpen_ball.sdiff isClosed_closedBall
    have hOsub : O ⊆ e.target := fun z hz => hrt (ball_subset_closedBall hz.1)
    set A : Set M := e.symm '' O with hAdef
    have hAopen : IsOpen A := by
      rw [hAdef, himg _ hOsub]
      exact e.continuousOn.isOpen_inter_preimage e.open_source hOopen
    have hAD : A ⊆ D := by
      rw [hAdef, hDdef, himg _ hOsub, himg _ hrt]
      exact Set.inter_subset_inter (subset_refl _)
        (Set.preimage_mono (Set.diff_subset.trans ball_subset_closedBall))
    have hp₀clA : p₀ ∉ closure A := by
      intro hcon
      have hU : IsOpen (e.source ∩ e ⁻¹' ball z₀ σ) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hp₀U : p₀ ∈ e.source ∩ e ⁻¹' ball z₀ σ := by
        refine ⟨hp₀s, ?_⟩
        rw [Set.mem_preimage, ← hz₀]
        exact mem_ball_self hσ0
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.1 hcon _ hU hp₀U
      rw [hAdef, himg _ hOsub] at hq2
      exact hq2.2.2 (ball_subset_closedBall hq1.2)
    have hAne : A ≠ Set.univ := by
      intro hcon
      apply hp₀clA
      apply subset_closure
      rw [hcon]
      trivial
    set W : M → ℝ := fun q => v q + ε * (Real.log (dist (e q) z₀) - Real.log r) with hW
    have hWsub : MSubharmonicOn W A := by
      intro q hqA
      rw [hAdef, himg _ hOsub] at hqA
      obtain ⟨hqs, hqO⟩ := hqA
      have hqz : e q ≠ z₀ := by
        intro hcon
        apply hqO.2
        rw [hcon, mem_closedBall, dist_self]
        exact hσ0.le
      have hqp : q ∈ ({p₀}ᶜ : Set M) :=
        Set.mem_compl_singleton_iff.mpr (hnep q hqs hqz)
      have hu : MHarmonicAt
          (fun y => (-ε) * Real.log (dist (e y) z₀) + ε * Real.log r) q :=
        mharm_affine _ q _ _ (hbharm q hqs hqz)
      have h7 := (hv q hqp).sub_mharmonicAt hu
      convert h7 using 2
      simp only [hW]
      ring
    have hWfr : ∀ y ∈ closure A \ A, ContinuousAt W y ∧ W y ≤ m₁ := by
      rintro y ⟨hycl, hyA⟩
      have hyD : y ∈ D := closure_minimal hAD hDcl hycl
      rw [hDdef, himg _ hrt] at hyD
      obtain ⟨hysrc, hyball⟩ := hyD
      rw [Set.mem_preimage, mem_closedBall] at hyball
      have hyneza : e y ≠ z₀ := by
        intro hcon
        exact hp₀clA (hpid y hysrc hcon ▸ hycl)
      have hynep : y ≠ p₀ := hnep y hysrc hyneza
      have hy0 : 0 < dist (e y) z₀ := dist_pos.2 hyneza
      have hWcont : ContinuousAt W y := by
        rw [hW]
        exact (hvcont y hynep).add
          (continuousAt_const.mul ((hbcont y hysrc hyneza).sub continuousAt_const))
      have hyO : e y ∉ O := by
        intro hcon
        apply hyA
        rw [hAdef, himg _ hOsub]
        exact ⟨hysrc, hcon⟩
      refine ⟨hWcont, ?_⟩
      by_cases hyb : e y ∈ ball z₀ r
      · -- Inner circle: the barrier beats the pole bound `C`.
        have hyσ : dist (e y) z₀ ≤ σ := by
          have h8 : e y ∈ closedBall z₀ σ := by
            by_contra h9
            exact hyO ⟨hyb, h9⟩
          rwa [mem_closedBall] at h8
        have hvy : v y ≤ C := hCbound y hysrc (by rwa [mem_closedBall]) hynep
        have hlogy : Real.log (dist (e y) z₀) ≤ Real.log σ := Real.log_le_log hy0 hyσ
        have h10 : ε * (Real.log (dist (e y) z₀) - Real.log r) ≤
            ε * (Real.log σ - Real.log r) := by
          apply mul_le_mul_of_nonneg_left _ hε0.le
          linarith
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log r) ≤ m₁
        linarith
      · -- Outer circle: the barrier vanishes and `Γ` bounds `v`.
        have hyr : dist (e y) z₀ = r := by
          rw [mem_ball] at hyb
          exact le_antisymm hyball (not_lt.1 hyb)
        have hvy : v y ≤ m₁ := hΓle y (hΓmem y hysrc hyr)
        change v y + ε * (Real.log (dist (e y) z₀) - Real.log r) ≤ m₁
        rw [hyr, sub_self, mul_zero, add_zero]
        exact hvy
    have hAx : x ∈ A := by
      rw [hAdef, himg _ hOsub]
      refine ⟨hxsrc, ?_⟩
      rw [Set.mem_preimage]
      refine ⟨by rwa [mem_ball], ?_⟩
      rw [mem_closedBall]
      exact fun hcon => (not_le.mpr hσdx) hcon
    have hWx := maxPrin A W m₁ D hAopen hAne hWsub hDcomp
      (fun q hq hqD => absurd (hAD hq) hqD) hWfr x hAx
    have hWxval : v x + ε * (Real.log (dist (e x) z₀) - Real.log r) ≤ m₁ := hWx
    have hflip : ε * (Real.log (dist (e x) z₀) - Real.log r) = -(ε * L) := by
      rw [hLdef]
      ring
    rw [hflip, hεL] at hWxval
    linarith
  /- ## Global bound and conclusion. -/
  have hglobal : ∀ x, x ≠ p₀ → v x ≤ m₁ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact hinner x hxD hx
    · exact houterAll x hxD
  intro x hx
  rcases le_or_gt (v xΓ) 0 with hcase | hcase
  · have h11 : m₁ = 0 := max_eq_right hcase
    have := hglobal x hx
    rwa [h11] at this
  · -- A positive interior max propagates to the far point: contradiction.
    exfalso
    have hm₁Γ : m₁ = v xΓ := max_eq_left hcase.le
    have hmax : ∀ q ∈ ({p₀}ᶜ : Set M), v q ≤ v xΓ := by
      intro q hq
      have h12 := hglobal q (Set.mem_compl_singleton_iff.1 hq)
      rwa [hm₁Γ] at h12
    have hconst := propagate {p₀}ᶜ v xΓ isOpen_compl_singleton
      hconn.isPreconnected (hΓp₀ hxΓ) hv hmax
    obtain ⟨y₀, hy₀⟩ := hfar
    have hy₀K : y₀ ∉ K := fun h => hy₀ (Or.inl h)
    have hy₀p : y₀ ∈ ({p₀}ᶜ : Set M) := fun h => hy₀ (Or.inr h)
    have h13 : v y₀ ≤ 0 := hKv y₀ hy₀K
    have h14 : v y₀ = v xΓ := hconst y₀ hy₀p
    linarith

/-- A nonconstant holomorphic function on a connected surface is an open
map. -/
theorem isOpenMap_of_contMDiff_of_not_const [ConnectedSpace M] {f : M → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnc : ¬ ∃ c, ∀ x, f x = c) :
    IsOpenMap f := by
  -- The chart reading of `f` is analytic at every point of the chart target.
  have hread : ∀ x : M, ∀ z ∈ (chartAt ℂ x).target,
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z := by
    intro x z hz
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm z :=
      (contMDiffOn_chart_symm (x := x)).contMDiffAt
        ((chartAt ℂ x).open_target.mem_nhds hz)
    exact (contMDiffAt_iff_contDiffAt.mp
      (ContMDiffAt.comp z hf.contMDiffAt hsymm)).analyticAt
  -- `f` agrees with its chart reading near every point.
  have hloc : ∀ x : M, f =ᶠ[𝓝 x] (f ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x) := by
    intro x
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hy]
  have hfix : ∀ x : M, (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = f x := by
    intro x
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hmap : ∀ x : M,
      map f (𝓝 x) = map (f ∘ (chartAt ℂ x).symm) (𝓝 (chartAt ℂ x x)) := by
    intro x
    rw [Filter.map_congr (hloc x), ← Filter.map_map,
      (chartAt ℂ x).map_nhds_eq (mem_chart_source ℂ x)]
  -- The set where `f` is locally constant is open.
  have hSopen : IsOpen {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx' : ∀ᶠ y in 𝓝 x, f y = f x := hx
    filter_upwards [eventually_eventually_nhds.mpr hx', hx'] with y hy hyx
    exact hy.mono fun z hz => hz.trans hyx.symm
  -- ... and closed, by the identity theorem on a chart ball.
  have hSclosed : IsClosed {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
    refine isClosed_of_closure_subset fun x hx => ?_
    obtain ⟨r, hr, hball⟩ :=
      Metric.isOpen_iff.mp (chartAt ℂ x).open_target _ (mem_chart_target ℂ x)
    have hVopen :
        IsOpen ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) r) :=
      (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source isOpen_ball
    have hxV : x ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) r :=
      ⟨mem_chart_source ℂ x, mem_ball_self hr⟩
    obtain ⟨y, hyV, hyS⟩ := _root_.mem_closure_iff.mp hx _ hVopen hxV
    -- the reading is eventually the constant `f y` near `chartAt ℂ x y`
    have hcst : (f ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x y)] fun _ => f y := by
      have h1 : ∀ᶠ w in map (chartAt ℂ x).symm (𝓝 (chartAt ℂ x y)), f w = f y := by
        rw [(chartAt ℂ x).symm_map_nhds_eq hyV.1]
        exact hyS
      exact eventually_map.mp h1
    have hgB : AnalyticOnNhd ℂ (f ∘ (chartAt ℂ x).symm) (ball (chartAt ℂ x x) r) :=
      fun z hz => hread x z (hball hz)
    have heq :
        Set.EqOn (f ∘ (chartAt ℂ x).symm) (fun _ => f y) (ball (chartAt ℂ x x) r) :=
      hgB.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (convex_ball ((chartAt ℂ x) x) r).isPreconnected hyV.2 hcst
    have hconstV :
        ∀ w ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) r,
          f w = f y := by
      intro w hw
      have h1 := heq hw.2
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv hw.1] at h1
      exact h1
    have hfxy : f x = f y := hconstV x hxV
    filter_upwards [hVopen.mem_nhds hxV] with w hw
    rw [hconstV w hw, hfxy]
  rcases isClopen_iff.mp ⟨hSclosed, hSopen⟩ with hempty | huniv
  · -- no point is locally constant: every point is in the open branch of the dichotomy
    rw [isOpenMap_iff_nhds_le]
    intro x
    rcases (hread x _ (mem_chart_target ℂ x)).eventually_constant_or_nhds_le_map_nhds with
      hcst | hle
    · exfalso
      have hxS : x ∈ {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
        have h1 : ∀ᶠ y in 𝓝 x,
            (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x y)
              = (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
          have h2 := hcst
          rw [← (chartAt ℂ x).map_nhds_eq (mem_chart_source ℂ x)] at h2
          exact eventually_map.mp h2
        filter_upwards [h1, hloc x] with y h1y h2y
        rw [h2y]
        exact h1y.trans (hfix x)
      rw [hempty] at hxS
      exact hxS
    · rw [hmap x, ← hfix x]
      exact hle
  · -- `f` locally constant everywhere on a connected space: contradiction
    exfalso
    have hall : ∀ x : M, ∀ᶠ y in 𝓝 x, f y = f x := by
      intro x
      have hx : x ∈ {x : M | ∀ᶠ y in 𝓝 x, f y = f x} := by
        rw [huniv]; exact Set.mem_univ x
      exact hx
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_eventually_eq f).mpr hall
    obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
    exact hnc ⟨f x₀, fun y => congrFun (hlc.eq_const x₀) y⟩

/-! ## The dichotomy and the Green's function -/

/-- In the hyperbolic case the envelope is harmonic on the punctured surface
and the family is bounded above at every point of it. -/
theorem mharmonicOn_greenEnvelope [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    MHarmonicOn (greenEnvelope p₀) {p₀}ᶜ ∧
      ∀ x ≠ p₀, BddAbove ((fun v => v x) '' greenFamily p₀) := by
  sorry

/-- The Green's function is strictly positive off the pole. -/
theorem greenEnvelope_pos [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    ∀ x ≠ p₀, 0 < greenEnvelope p₀ x := by
  classical
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
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
  -- ### Setup: the pole chart and a small closed ball inside its target.
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he
  set c : ℂ := e p₀ with hc
  have hp₀src : p₀ ∈ e.source := by rw [he]; exact mem_chart_source ℂ p₀
  have heatlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
    rw [he]; exact IsManifold.chart_mem_maximalAtlas p₀
  have hctgt : c ∈ e.target := by rw [hc]; exact e.map_source hp₀src
  obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.mp e.open_target c hctgt
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcbsub : closedBall c r ⊆ e.target :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hballε
  have hbsub : ball c r ⊆ e.target := ball_subset_closedBall.trans hcbsub
  -- ### The plane profile: a truncated logarithm.
  set g : ℂ → ℝ := fun z => max (Real.log r - Real.log ‖z - c‖) 0 with hg
  have hgnonneg : ∀ z, 0 ≤ g z := fun z => le_max_right _ _
  have hharm : HarmonicOnNhd (fun z => Real.log r - Real.log ‖z - c‖) {c}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun t : ℂ => t - c) z := by
      exact analyticAt_id.sub analyticAt_const
    have hne : z - c ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log r)).sub (hana.harmonicAt_log_norm hne)
  have hgsub : SubharmonicOn g {c}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {c}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hharm) h0
  have hgcont : ContinuousOn g {c}ᶜ := hgsub.1
  have hgzero : ∀ z, z ∉ ball c r → g z = 0 := by
    intro z hz
    have hzr : r ≤ ‖z - c‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hle : Real.log r ≤ Real.log ‖z - c‖ := Real.log_le_log hr0 hzr
    simp only [hg]
    exact max_eq_right (by linarith)
  -- ### The family member: the truncated logarithm read through the chart.
  set v₀ : M → ℝ := fun x => if x ∈ e.source then g (e x) else 0 with hv₀
  have hv₀nonneg : ∀ x, 0 ≤ v₀ x := by
    intro x
    simp only [hv₀]
    split_ifs
    · exact hgnonneg _
    · exact le_rfl
  set K : Set M := e.symm '' closedBall c r
  have hKcompact : IsCompact K :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hcbsub)
  have hKsource : K ⊆ e.source := by
    rintro x ⟨w, hw, rfl⟩
    exact e.map_target (hcbsub hw)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hv₀zero : ∀ x, x ∉ K → v₀ x = 0 := by
    intro x hx
    by_cases hxs : x ∈ e.source
    · simp only [hv₀, if_pos hxs]
      by_contra hne
      have hball2 : e x ∈ ball c r := by
        by_contra hnb
        exact hne (hgzero _ hnb)
      exact hx ⟨e x, ball_subset_closedBall hball2, e.left_inv hxs⟩
    · simp only [hv₀, if_neg hxs]
  have hexc : ∀ x, x ∈ e.source → x ≠ p₀ → e x ≠ c := by
    intro x hxs hxp heq
    exact hxp (e.injOn hxs hp₀src (by rw [← hc]; exact heq))
  -- ### Membership in the Green's family.
  have hv₀mem : v₀ ∈ greenFamily p₀ := by
    refine ⟨?_, ?_, ⟨K, hKcompact, ?_, hv₀zero⟩, ⟨Real.log r, ?_⟩⟩
    · -- subharmonicity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      by_cases hxs : x ∈ e.source
      · -- read in the pole chart: `v₀ ∘ e.symm` agrees with `g` near `e x`
        refine (msubharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mpr ?_
        have hopen2 : IsOpen (e.target ∩ {c}ᶜ) :=
          e.open_target.inter isOpen_compl_singleton
        have hmem2 : e x ∈ e.target ∩ {c}ᶜ :=
          ⟨e.map_source hxs, Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)⟩
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqon : Set.EqOn g (v₀ ∘ e.symm) (ball (e x) ρ) := by
          intro z hz
          have hzt : z ∈ e.target := (hρsub hz).1
          have hzs : e.symm z ∈ e.source := e.map_target hzt
          simp only [Function.comp_apply, hv₀, if_pos hzs, e.right_inv hzt]
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ hgsub (fun z hz => (hρsub hz).2) heqon⟩
      · -- off the chart: `v₀` vanishes on the open complement of `K`
        have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hopen2 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ) :=
          (chartAt ℂ x).isOpen_inter_preimage_symm hKclosed.isOpen_compl
        have hmem2 : chartAt ℂ x x ∈
            (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ := by
          refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
          rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
          exact hxK
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqz : Set.EqOn (fun _ : ℂ => (0 : ℝ)) (v₀ ∘ (chartAt ℂ x).symm)
            (ball (chartAt ℂ x x) ρ) := by
          intro z hz
          exact (hv₀zero _ ((hρsub hz).2)).symm
        have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ x x) ρ) :=
          HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ h0 subset_rfl heqz⟩
    · -- continuity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      apply ContinuousAt.continuousWithinAt
      by_cases hxs : x ∈ e.source
      · have hgc : ContinuousAt g (e x) := hgcont.continuousAt
          (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)))
        refine (hgc.comp (e.continuousAt hxs)).congr_of_eventuallyEq ?_
        filter_upwards [e.open_source.mem_nhds hxs] with y hy
        simp only [Function.comp_apply, hv₀, if_pos hy]
      · have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hev : v₀ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [hKclosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hv₀zero y hy
        exact continuousAt_const.congr_of_eventuallyEq hev
    · -- the support is not everything
      intro hKuniv
      exact noncompact_univ M (hKuniv ▸ hKcompact)
    · -- logarithmic pole growth
      have hopen2 : IsOpen (e.source ∩ e ⁻¹' ball c r) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hnb : e.source ∩ e ⁻¹' ball c r ∈ 𝓝 p₀ := by
        refine hopen2.mem_nhds ⟨hp₀src, ?_⟩
        rw [Set.mem_preimage, ← hc]
        exact mem_ball_self hr0
      filter_upwards [nhdsWithin_le_nhds hnb, eventually_mem_nhdsWithin] with x hx hxp
      have hxsrc : x ∈ e.source := hx.1
      have hxne : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hxp
      have hpole_eq : poleCoord p₀ x = e x - c := by
        simp only [poleCoord, ← he, ← hc]
      rw [hpole_eq]
      have hpos : 0 < ‖e x - c‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (hexc x hxsrc hxne))
      have hlt : ‖e x - c‖ < r := by
        have hxball : e x ∈ ball c r := hx.2
        rw [mem_ball, dist_eq_norm] at hxball
        exact hxball
      have hBA : Real.log ‖e x - c‖ < Real.log r := Real.log_lt_log hpos hlt
      simp only [hv₀, if_pos hxsrc, hg]
      rw [max_eq_left (by linarith)]
      linarith
  -- ### The envelope dominates the member, hence is nonnegative off the pole.
  obtain ⟨hGh, hGbdd⟩ := mharmonicOn_greenEnvelope hG
  have hge : ∀ z, z ≠ p₀ → v₀ z ≤ greenEnvelope p₀ z := by
    intro z hz
    exact le_csSup (hGbdd z hz) ⟨v₀, hv₀mem, rfl⟩
  have hGnonneg : ∀ z, z ≠ p₀ → 0 ≤ greenEnvelope p₀ z :=
    fun z hz => (hv₀nonneg z).trans (hge z hz)
  -- ### A witness point where the envelope is strictly positive.
  set w : ℂ := c + ((r / 2 : ℝ) : ℂ) with hwdef
  have hwc : ‖w - c‖ = r / 2 := by
    rw [hwdef, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hwball : w ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, hwc]
    linarith
  have hwt : w ∈ e.target := hbsub hwball
  have hys : e.symm w ∈ e.source := e.map_target hwt
  have hyw : e (e.symm w) = w := e.right_inv hwt
  have hynp : e.symm w ≠ p₀ := by
    intro h
    have h2 := congrArg (e : M → ℂ) h
    rw [hyw] at h2
    have h0 : (0 : ℝ) = r / 2 := by
      rw [← hwc, h2, ← hc, sub_self, norm_zero]
    linarith
  have hv₀y : 0 < v₀ (e.symm w) := by
    have hlog : Real.log (r / 2) < Real.log r :=
      Real.log_lt_log (by linarith) (by linarith)
    simp only [hv₀, if_pos hys, hyw, hg, hwc]
    exact lt_max_iff.mpr (Or.inl (by linarith))
  have hGy : 0 < greenEnvelope p₀ (e.symm w) := lt_of_lt_of_le hv₀y (hge _ hynp)
  -- ### Strong-maximum propagation on the connected punctured surface.
  intro x hxp
  rcases (hGnonneg x hxp).lt_or_eq with hpos | heq0
  · exact hpos
  · exfalso
    have hxmem : x ∈ ({p₀}ᶜ : Set M) := Set.mem_compl_singleton_iff.mpr hxp
    have hsopen : IsOpen ({p₀}ᶜ : Set M) := isOpen_compl_singleton
    have hsconn : IsConnected ({p₀}ᶜ : Set M) :=
      isConnected_compl_singleton_of_connected ⟨e.symm w, p₀, hynp⟩ p₀
    have hsub : MSubharmonicOn (-(greenEnvelope p₀)) ({p₀}ᶜ : Set M) :=
      fun z hz => ((hGh z hz).neg).msubharmonicAt
    have hSopen : IsOpen {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z = 0} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzs, hz0⟩
      have hmax : ∀ a ∈ ({p₀}ᶜ : Set M),
          (-(greenEnvelope p₀)) a ≤ (-(greenEnvelope p₀)) z := by
        intro a ha
        have h1 : 0 ≤ greenEnvelope p₀ a :=
          hGnonneg a (Set.mem_compl_singleton_iff.mp ha)
        simp only [Pi.neg_apply, hz0, neg_zero]
        linarith
      have hev := MSubharmonicAt.eventually_eq_of_le hsopen hzs hsub hmax
      filter_upwards [hev, hsopen.mem_nhds hzs] with a ha has
      refine ⟨has, ?_⟩
      simp only [Pi.neg_apply, hz0, neg_zero, neg_eq_zero] at ha
      exact ha
    have hVopen : IsOpen {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z ≠ 0} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzs, hzne⟩
      have hcont : ContinuousAt (greenEnvelope p₀) z := (hGh z hzs).continuousAt
      filter_upwards [hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hzne),
        hsopen.mem_nhds hzs] with a ha has
      exact ⟨has, ha⟩
    have hdisj : Disjoint {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z = 0}
        {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z ≠ 0} := by
      rw [Set.disjoint_left]
      rintro z ⟨_, h0⟩ ⟨_, hne⟩
      exact hne h0
    have hunion : ({p₀}ᶜ : Set M) ⊆
        {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z = 0} ∪
          {z : M | z ∈ ({p₀}ᶜ : Set M) ∧ greenEnvelope p₀ z ≠ 0} := by
      intro z hz
      by_cases h : greenEnvelope p₀ z = 0
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    have hkey := IsPreconnected.subset_left_of_subset_union hSopen hVopen hdisj hunion
      ⟨x, hxmem, hxmem, heq0.symm⟩ hsconn.isPreconnected
    have hy0 : greenEnvelope p₀ (e.symm w) = 0 :=
      (hkey (Set.mem_compl_singleton_iff.mpr hynp)).2
    linarith

/-- **Pole behavior**: near the pole, `G + log|z|` extends to a harmonic
function of the local coordinate. -/
theorem exists_harmonic_pole_extension [T2Space M] [ConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    ∃ r > 0, ball (chartAt ℂ p₀ p₀) r ⊆ (chartAt ℂ p₀).target ∧
      ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball (chartAt ℂ p₀ p₀) r) ∧
        ∀ w ∈ ball (chartAt ℂ p₀ p₀) r \ {chartAt ℂ p₀ p₀},
          h w = greenEnvelope p₀ ((chartAt ℂ p₀).symm w) +
            Real.log ‖w - chartAt ℂ p₀ p₀‖ := by
  classical
  -- ### Generic plane-side helpers.
  -- Restriction of subharmonicity to a subset.
  have smono : ∀ (f : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn f U → V ⊆ U →
      SubharmonicOn f V := fun f U V hf hVU =>
    ⟨hf.1.mono hVU, fun a ha ρ hρ hb => hf.2 a (hVU ha) ρ hρ (hb.trans hVU)⟩
  -- Transfer of subharmonicity along a pointwise equality on a subdomain.
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
  -- Subharmonic plus harmonic is subharmonic.
  have subAdd : ∀ (f g : ℂ → ℝ) (U : Set ℂ), SubharmonicOn f U → HarmonicOnNhd g U →
      SubharmonicOn (fun z => f z + g z) U := by
    intro f g U hf hgh
    refine ⟨hf.1.add hgh.continuousOn, ?_⟩
    intro a ha ρ hρ hb
    have hsphere : sphere a ρ ⊆ U := sphere_subset_closedBall.trans hb
    have hfci : CircleIntegrable f a ρ := (hf.1.mono hsphere).circleIntegrable hρ.le
    have hgci : CircleIntegrable g a ρ :=
      (hgh.continuousOn.mono hsphere).circleIntegrable hρ.le
    rw [Real.circleAverage_fun_add hfci hgci]
    have hgavg : Real.circleAverage g a ρ = g a := by
      apply HarmonicOnNhd.circleAverage_eq
      rw [abs_of_pos hρ]
      exact hgh.mono hb
    have hfavg : f a ≤ Real.circleAverage f a ρ := hf.2 a ha ρ hρ hb
    rw [hgavg]
    linarith
  -- ### Setup: the pole chart and a small closed ball inside its target.
  set e : OpenPartialHomeomorph M ℂ := chartAt ℂ p₀ with he
  set c : ℂ := e p₀ with hc
  have hp₀src : p₀ ∈ e.source := by rw [he]; exact mem_chart_source ℂ p₀
  have heatlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M := by
    rw [he]; exact IsManifold.chart_mem_maximalAtlas p₀
  have hctgt : c ∈ e.target := by rw [hc]; exact e.map_source hp₀src
  obtain ⟨ε, hε, hballε⟩ := Metric.isOpen_iff.mp e.open_target c hctgt
  set r : ℝ := ε / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hcbsub : closedBall c r ⊆ e.target :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hballε
  have hbsub : ball c r ⊆ e.target := ball_subset_closedBall.trans hcbsub
  have hsymmc : e.symm c = p₀ := by rw [hc]; exact e.left_inv hp₀src
  have hexc : ∀ x, x ∈ e.source → x ≠ p₀ → e x ≠ c := by
    intro x hxs hxp heq
    exact hxp (e.injOn hxs hp₀src (by rw [← hc]; exact heq))
  have hsymm_ne : ∀ w, w ∈ e.target → w ≠ c → e.symm w ≠ p₀ := by
    intro w hwt hwne hcon
    apply hwne
    have h2 := congrArg (e : M → ℂ) hcon
    rw [e.right_inv hwt] at h2
    rw [h2, hc]
  have hsymm_src : ∀ w, w ∈ e.target → e.symm w ∈ e.source :=
    fun w hw => e.map_target hw
  have hsymm_eq : ∀ w, w ∈ e.target → e (e.symm w) = w := fun w hw => e.right_inv hw
  -- ### Envelope facts: harmonicity off the pole and pointwise boundedness.
  obtain ⟨hGh, hGbdd⟩ := mharmonicOn_greenEnvelope hG
  -- ### The plane profile: a truncated logarithm.
  set g : ℂ → ℝ := fun z => max (Real.log r - Real.log ‖z - c‖) 0 with hg
  have hgnonneg : ∀ z, 0 ≤ g z := fun z => le_max_right _ _
  have hgkharm : HarmonicOnNhd (fun z => Real.log r - Real.log ‖z - c‖) {c}ᶜ := by
    intro z hz
    have hana : AnalyticAt ℂ (fun t : ℂ => t - c) z := by
      exact analyticAt_id.sub analyticAt_const
    have hne : z - c ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    exact (harmonicAt_const (Real.log r)).sub (hana.harmonicAt_log_norm hne)
  have hgsub : SubharmonicOn g {c}ᶜ := by
    have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) {c}ᶜ :=
      HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
    exact subharmonicOn_max (HarmonicOnNhd.subharmonicOn hgkharm) h0
  have hgcont : ContinuousOn g {c}ᶜ := hgsub.1
  have hgzero : ∀ z, z ∉ ball c r → g z = 0 := by
    intro z hz
    have hzr : r ≤ ‖z - c‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hz
      exact hz
    have hle : Real.log r ≤ Real.log ‖z - c‖ := Real.log_le_log hr0 hzr
    simp only [hg]
    exact max_eq_right (by linarith)
  -- ### The family member: the truncated logarithm read through the chart.
  set v₀ : M → ℝ := fun x => if x ∈ e.source then g (e x) else 0 with hv₀
  set K : Set M := e.symm '' closedBall c r
  have hKcompact : IsCompact K :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hcbsub)
  have hKsource : K ⊆ e.source := by
    rintro x ⟨w, hw, rfl⟩
    exact e.map_target (hcbsub hw)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hv₀zero : ∀ x, x ∉ K → v₀ x = 0 := by
    intro x hx
    by_cases hxs : x ∈ e.source
    · simp only [hv₀, if_pos hxs]
      by_contra hne
      have hball2 : e x ∈ ball c r := by
        by_contra hnb
        exact hne (hgzero _ hnb)
      exact hx ⟨e x, ball_subset_closedBall hball2, e.left_inv hxs⟩
    · simp only [hv₀, if_neg hxs]
  -- ### Membership of the truncated logarithm in the Green's family.
  have hv₀mem : v₀ ∈ greenFamily p₀ := by
    refine ⟨?_, ?_, ⟨K, hKcompact, ?_, hv₀zero⟩, ⟨Real.log r, ?_⟩⟩
    · -- subharmonicity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      by_cases hxs : x ∈ e.source
      · -- read in the pole chart: `v₀ ∘ e.symm` agrees with `g` near `e x`
        refine (msubharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mpr ?_
        have hopen2 : IsOpen (e.target ∩ {c}ᶜ) :=
          e.open_target.inter isOpen_compl_singleton
        have hmem2 : e x ∈ e.target ∩ {c}ᶜ :=
          ⟨e.map_source hxs, Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)⟩
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqon : Set.EqOn g (v₀ ∘ e.symm) (ball (e x) ρ) := by
          intro z hz
          have hzt : z ∈ e.target := (hρsub hz).1
          have hzs : e.symm z ∈ e.source := e.map_target hzt
          simp only [Function.comp_apply, hv₀, if_pos hzs, e.right_inv hzt]
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ hgsub (fun z hz => (hρsub hz).2) heqon⟩
      · -- off the chart: `v₀` vanishes on the open complement of `K`
        have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hopen2 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ) :=
          (chartAt ℂ x).isOpen_inter_preimage_symm hKclosed.isOpen_compl
        have hmem2 : chartAt ℂ x x ∈
            (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Kᶜ := by
          refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
          rw [Set.mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
          exact hxK
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen2 _ hmem2
        have heqz : Set.EqOn (fun _ : ℂ => (0 : ℝ)) (v₀ ∘ (chartAt ℂ x).symm)
            (ball (chartAt ℂ x x) ρ) := by
          intro z hz
          exact (hv₀zero _ ((hρsub hz).2)).symm
        have h0 : SubharmonicOn (fun _ : ℂ => (0 : ℝ)) (ball (chartAt ℂ x x) ρ) :=
          HarmonicOnNhd.subharmonicOn fun z _ => harmonicAt_const 0
        exact ⟨ρ, hρ, fun z hz => (hρsub hz).1,
          transfer _ _ _ _ h0 subset_rfl heqz⟩
    · -- continuity on the punctured surface
      intro x hx
      have hxp : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hx
      apply ContinuousAt.continuousWithinAt
      by_cases hxs : x ∈ e.source
      · have hgc : ContinuousAt g (e x) := hgcont.continuousAt
          (isOpen_compl_singleton.mem_nhds
            (Set.mem_compl_singleton_iff.mpr (hexc x hxs hxp)))
        refine (hgc.comp (e.continuousAt hxs)).congr_of_eventuallyEq ?_
        filter_upwards [e.open_source.mem_nhds hxs] with y hy
        simp only [Function.comp_apply, hv₀, if_pos hy]
      · have hxK : x ∉ K := fun hxK => hxs (hKsource hxK)
        have hev : v₀ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [hKclosed.isOpen_compl.mem_nhds hxK] with y hy
          exact hv₀zero y hy
        exact continuousAt_const.congr_of_eventuallyEq hev
    · -- the support is not everything
      intro hKuniv
      exact noncompact_univ M (hKuniv ▸ hKcompact)
    · -- logarithmic pole growth
      have hopen2 : IsOpen (e.source ∩ e ⁻¹' ball c r) :=
        e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
      have hnb : e.source ∩ e ⁻¹' ball c r ∈ 𝓝 p₀ := by
        refine hopen2.mem_nhds ⟨hp₀src, ?_⟩
        rw [Set.mem_preimage, ← hc]
        exact mem_ball_self hr0
      filter_upwards [nhdsWithin_le_nhds hnb, eventually_mem_nhdsWithin] with x hx hxp
      have hxsrc : x ∈ e.source := hx.1
      have hxne : x ≠ p₀ := Set.mem_compl_singleton_iff.mp hxp
      have hpole_eq : poleCoord p₀ x = e x - c := by
        simp only [poleCoord, ← he, ← hc]
      rw [hpole_eq]
      have hpos : 0 < ‖e x - c‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (hexc x hxsrc hxne))
      have hlt : ‖e x - c‖ < r := by
        have hxball : e x ∈ ball c r := hx.2
        rw [mem_ball, dist_eq_norm] at hxball
        exact hxball
      have hBA : Real.log ‖e x - c‖ < Real.log r := Real.log_lt_log hpos hlt
      simp only [hv₀, if_pos hxsrc, hg]
      rw [max_eq_left (by linarith)]
      linarith
  -- ### Members lie below the envelope.
  have hmem_le : ∀ v ∈ greenFamily p₀, ∀ x : M, x ≠ p₀ → v x ≤ greenEnvelope p₀ x :=
    fun v hv x hx => le_csSup (hGbdd x hx) ⟨v, hv, rfl⟩
  -- ### The half-radius disc.
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsr : s < r := by rw [hs]; linarith
  have hssub : ball c s ⊆ e.target := (ball_subset_ball hsr.le).trans hbsub
  -- ### Readings of the envelope are harmonic on the punctured target.
  have hGread : ∀ w, w ∈ e.target → w ≠ c →
      HarmonicAt (greenEnvelope p₀ ∘ ⇑e.symm) w := by
    intro w hwt hwne
    have hxs : e.symm w ∈ e.source := hsymm_src w hwt
    have hxne : e.symm w ≠ p₀ := hsymm_ne w hwt hwne
    have hmh : MHarmonicAt (greenEnvelope p₀) (e.symm w) :=
      hGh _ (Set.mem_compl_singleton_iff.mpr hxne)
    have h2 := (mharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mp hmh
    rwa [hsymm_eq w hwt] at h2
  -- ### The logarithmic kernel is harmonic off the centre.
  have hLg : ∀ w : ℂ, w ≠ c → HarmonicAt (fun q : ℂ => Real.log ‖q - c‖) w := by
    intro w hw
    have h1 : AnalyticAt ℂ (fun q : ℂ => q - c) w := analyticAt_id.sub analyticAt_const
    exact h1.harmonicAt_log_norm (sub_ne_zero.2 hw)
  -- ### The outer circle and its envelope maximum `B`.
  have hsphsub : sphere c s ⊆ e.target := fun w hw =>
    hbsub (mem_ball.2 (lt_of_eq_of_lt (mem_sphere.1 hw) hsr))
  have hsphne : ∀ w ∈ sphere c s, w ≠ c := by
    intro w hw hcon
    have h1 := mem_sphere.1 hw
    rw [hcon, dist_self] at h1
    exact hs0.ne h1
  have hGcontS : ContinuousOn (greenEnvelope p₀ ∘ ⇑e.symm) (sphere c s) := fun w hw =>
    ((hGread w (hsphsub hw) (hsphne w hw)).1.continuousAt).continuousWithinAt
  obtain ⟨wB, -, hwBmax⟩ := (isCompact_sphere c s).exists_isMaxOn
    ((NormedSpace.sphere_nonempty).2 hs0.le) hGcontS
  set B : ℝ := (greenEnvelope p₀ ∘ ⇑e.symm) wB with hB
  have hBle : ∀ w ∈ sphere c s, greenEnvelope p₀ (e.symm w) ≤ B := fun w hw => hwBmax hw
  -- ### Per-member reading is subharmonic on the punctured disc.
  have hVsub : ∀ v ∈ greenFamily p₀,
      SubharmonicOn (v ∘ ⇑e.symm) (ball c r \ {c}) := by
    intro v hv
    obtain ⟨hvsub, hvcont, -, -⟩ := hv
    have hUopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
    apply subharmonicOn_of_locally hUopen
    · -- continuity of the reading
      intro w hw
      have hwt : w ∈ e.target := hbsub hw.1
      have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
      have h1 : ContinuousAt (⇑e.symm) w := e.continuousAt_symm hwt
      have h2 : ContinuousAt v (e.symm w) :=
        hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.mpr (hsymm_ne w hwt hwne)))
      exact (h2.comp h1).continuousWithinAt
    · -- the local sub-mean-value inequality, from the chart-independent reading
      intro w hw
      have hwt : w ∈ e.target := hbsub hw.1
      have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
      have hxs : e.symm w ∈ e.source := hsymm_src w hwt
      have hMS : MSubharmonicAt v (e.symm w) :=
        hvsub _ (Set.mem_compl_singleton_iff.mpr (hsymm_ne w hwt hwne))
      obtain ⟨ρ, hρ, -, hsub⟩ :=
        (msubharmonicAt_iff_of_mem_maximalAtlas heatlas hxs).mp hMS
      rw [hsymm_eq w hwt] at hsub
      refine ⟨ρ, hρ, ?_⟩
      intro ρ' hρ'0 hρ'lt _hcb
      exact hsub.2 w (mem_ball_self hρ) ρ' hρ'0 (Metric.closedBall_subset_ball hρ'lt)
  -- ### Per-member pole bound through the chart.
  have hpole' : ∀ v ∈ greenFamily p₀, ∃ Cv : ℝ, ∃ δ > 0,
      ∀ w ∈ ball c δ, w ≠ c → v (e.symm w) + Real.log ‖w - c‖ ≤ Cv := by
    intro v hv
    obtain ⟨-, -, -, Cv, hCv⟩ := hv
    refine ⟨Cv, ?_⟩
    have h1 : Tendsto (⇑e.symm) (𝓝 c) (𝓝 p₀) := by
      have h2 : ContinuousAt (⇑e.symm) c := e.continuousAt_symm hctgt
      rwa [ContinuousAt, hsymmc] at h2
    have h3 : ∀ᶠ x in 𝓝 p₀, x ∈ ({p₀}ᶜ : Set M) →
        v x + Real.log ‖poleCoord p₀ x‖ ≤ Cv := eventually_nhdsWithin_iff.mp hCv
    have h4 := h1.eventually h3
    have h5 : ∀ᶠ w in 𝓝 c, w ∈ e.target := e.open_target.mem_nhds hctgt
    have h6 : ∀ᶠ w in 𝓝 c, w ≠ c → v (e.symm w) + Real.log ‖w - c‖ ≤ Cv := by
      filter_upwards [h4, h5] with w h4w h5w hwne
      have hne2 : e.symm w ≠ p₀ := hsymm_ne w h5w hwne
      have hpc : poleCoord p₀ (e.symm w) = w - c := by
        simp only [poleCoord, ← he, ← hc, hsymm_eq w h5w]
      have h7 := h4w (Set.mem_compl_singleton_iff.mpr hne2)
      rwa [hpc] at h7
    rw [Metric.eventually_nhds_iff_ball] at h6
    exact h6
  -- ### The key annulus estimate, per member.
  have key : ∀ v ∈ greenFamily p₀, ∀ w₀ ∈ ball c s \ {c},
      v (e.symm w₀) + (Real.log ‖w₀ - c‖ - Real.log s) ≤ B := by
    intro v hv w₀ hw₀
    obtain ⟨Cv, δv, hδv0, hδv⟩ := hpole' v hv
    have hsubV : SubharmonicOn (v ∘ ⇑e.symm) (ball c r \ {c}) := hVsub v hv
    have hw₀ne : w₀ ≠ c := fun hcon => hw₀.2 (Set.mem_singleton_iff.2 hcon)
    have hw₀n : 0 < ‖w₀ - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hw₀ne)
    have hw₀lt : ‖w₀ - c‖ < s := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hw₀.1
    have ht0 : Real.log ‖w₀ - c‖ - Real.log s < 0 :=
      sub_neg.2 (Real.log_lt_log hw₀n hw₀lt)
    set t : ℝ := Real.log ‖w₀ - c‖ - Real.log s with htdef
    have htne : t ≠ 0 := ne_of_lt ht0
    refine le_of_forall_pos_le_add ?_
    intro η hη
    set ε : ℝ := η / (-t) with hεdef
    have hε0 : 0 < ε := div_pos hη (by linarith)
    have hεt : ε * t = -η := by
      calc ε * t = η / (-t) * t := by rw [hεdef]
        _ = -(η / t * t) := by rw [div_neg]; ring
        _ = -η := by rw [div_mul_cancel₀ η htne]
    -- The inner excision radius `σ`, small enough for the barrier to win.
    set Q : ℝ := (B - Cv + (1 + ε) * Real.log s) / ε with hQdef
    set σ : ℝ := min (min (δv / 2) (‖w₀ - c‖ / 2)) (min (s / 2) (Real.exp Q)) with hσdef
    have hσ0 : 0 < σ :=
      lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (Real.exp_pos Q))
    have hσδ : σ < δv :=
      lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    have hσw : σ < ‖w₀ - c‖ :=
      lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    have hσs : σ < s :=
      lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have hσQ : Real.log σ ≤ Q := by
      have h1 : σ ≤ Real.exp Q := (min_le_right _ _).trans (min_le_right _ _)
      calc Real.log σ ≤ Real.log (Real.exp Q) := Real.log_le_log hσ0 h1
        _ = Q := Real.log_exp Q
    have hbarrier : Cv - Real.log σ + (1 + ε) * (Real.log σ - Real.log s) ≤ B := by
      have h5 : ε * Real.log σ ≤ ε * Q := mul_le_mul_of_nonneg_left hσQ hε0.le
      have h6 : ε * Q = B - Cv + (1 + ε) * Real.log s := by
        rw [hQdef, mul_comm]
        exact div_mul_cancel₀ _ hε0.ne'
      nlinarith [h5, h6]
    -- The annulus `A` and its closure/frontier geometry.
    set A : Set ℂ := ball c s \ closedBall c σ with hAdef
    have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
    have hAbdd : Bornology.IsBounded A := isBounded_ball.subset Set.diff_subset
    have hAsub : A ⊆ ball c r \ {c} := by
      intro z hz
      refine ⟨ball_subset_ball hsr.le hz.1, ?_⟩
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      exact hz.2 (by rw [hcon]; exact mem_closedBall_self hσ0.le)
    have hclA : closure A ⊆ closedBall c s \ ball c σ := by
      intro z hz
      rw [hAdef, Set.diff_eq] at hz
      have h2 := closure_inter_subset_inter_closure (ball c s) ((closedBall c σ)ᶜ) hz
      rw [closure_ball c hs0.ne', closure_compl, interior_closedBall c hσ0.ne'] at h2
      exact ⟨h2.1, h2.2⟩
    have hfrA : frontier A ⊆ sphere c s ∪ sphere c σ := by
      intro z hz
      rw [hAdef, Set.diff_eq] at hz
      rcases frontier_inter_subset (ball c s) ((closedBall c σ)ᶜ) hz with h2 | h2
      · have h3 := h2.1
        rw [frontier_ball c hs0.ne'] at h3
        exact Or.inl h3
      · have h3 := h2.2
        rw [frontier_compl, frontier_closedBall c hσ0.ne'] at h3
        exact Or.inr h3
    have hKsub : closedBall c s \ ball c σ ⊆ ball c r \ {c} := by
      intro z hz
      constructor
      · exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz.1) hsr)
      · intro hcon
        rw [Set.mem_singleton_iff] at hcon
        apply hz.2
        rw [hcon]
        exact mem_ball_self hσ0
    -- The barriered competitor `F` is subharmonic on the annulus.
    set F : ℂ → ℝ := fun z => v (e.symm z) + (1 + ε) * (Real.log ‖z - c‖ - Real.log s)
      with hFdef
    have hFsub : SubharmonicOn F A := by
      have h1 : SubharmonicOn (v ∘ ⇑e.symm) A := smono _ _ _ hsubV hAsub
      have h2 : HarmonicOnNhd
          (fun z => (1 + ε) * (Real.log ‖z - c‖ - Real.log s)) A := by
        intro z hz
        have hzne : z ≠ c := by
          intro hcon
          exact (hAsub hz).2 (Set.mem_singleton_iff.2 hcon)
        have h3 := ((hLg z hzne).sub (harmonicAt_const (Real.log s))).const_smul
          (c := 1 + ε)
        have heq3 : (1 + ε) • ((fun q : ℂ => Real.log ‖q - c‖) - fun _ => Real.log s)
            = fun z => (1 + ε) * (Real.log ‖z - c‖ - Real.log s) := by
          funext q
          simp [smul_eq_mul]
        rw [heq3] at h3
        exact h3
      exact subAdd _ _ _ h1 h2
    -- Continuity of `F` up to the closure of the annulus.
    have hVcontK : ContinuousOn (fun z => v (e.symm z)) (closedBall c s \ ball c σ) := by
      intro z hz
      have hzt : z ∈ e.target := hbsub (hKsub hz).1
      have hzne : z ≠ c := fun hcon => (hKsub hz).2 (Set.mem_singleton_iff.2 hcon)
      obtain ⟨-, hvcont, -, -⟩ := hv
      have h1 : ContinuousAt (⇑e.symm) z := e.continuousAt_symm hzt
      have h2 : ContinuousAt v (e.symm z) :=
        hvcont.continuousAt (isOpen_compl_singleton.mem_nhds
          (Set.mem_compl_singleton_iff.mpr (hsymm_ne z hzt hzne)))
      exact (h2.comp h1).continuousWithinAt
    have hlogK : ContinuousOn (fun z : ℂ => Real.log ‖z - c‖)
        (closedBall c s \ ball c σ) := by
      apply ContinuousOn.log
      · fun_prop
      · intro z hz
        have h1 : σ ≤ dist z c := not_lt.1 fun hlt => hz.2 (mem_ball.2 hlt)
        rw [dist_eq_norm] at h1
        exact ne_of_gt (lt_of_lt_of_le hσ0 h1)
    have hFcont : ContinuousOn F (closure A) := by
      refine ContinuousOn.mono ?_ hclA
      exact hVcontK.add (continuousOn_const.mul (hlogK.sub continuousOn_const))
    -- The frontier bound `F ≤ B` on both circles.
    have hFfr : ∀ z ∈ frontier A, F z ≤ B := by
      intro z hz
      rcases hfrA hz with hzs | hzσ
      · -- outer circle: the barrier vanishes and the envelope maximum bounds `v`
        have hzn : ‖z - c‖ = s := by rw [← dist_eq_norm]; exact mem_sphere.1 hzs
        have hzt : z ∈ e.target := hsphsub hzs
        have hzne : z ≠ c := hsphne z hzs
        have h1 : v (e.symm z) ≤ greenEnvelope p₀ (e.symm z) :=
          hmem_le v hv _ (hsymm_ne z hzt hzne)
        have h2 : greenEnvelope p₀ (e.symm z) ≤ B := hBle z hzs
        simp only [hFdef]
        rw [hzn, sub_self, mul_zero, add_zero]
        linarith
      · -- inner circle: the pole bound and the barrier choice
        have hzn : ‖z - c‖ = σ := by rw [← dist_eq_norm]; exact mem_sphere.1 hzσ
        have hzne : z ≠ c := by
          intro hcon
          rw [hcon, sub_self, norm_zero] at hzn
          exact hσ0.ne' hzn.symm
        have hzball : z ∈ ball c δv := by
          rw [mem_ball, dist_eq_norm, hzn]
          exact hσδ
        have h1 : v (e.symm z) + Real.log ‖z - c‖ ≤ Cv := hδv z hzball hzne
        rw [hzn] at h1
        simp only [hFdef]
        rw [hzn]
        linarith [hbarrier]
    -- The maximum principle, evaluated at `w₀`.
    have hw₀A : w₀ ∈ A := by
      refine ⟨hw₀.1, ?_⟩
      intro hcon
      rw [mem_closedBall, dist_eq_norm] at hcon
      linarith
    have hFw₀ : F w₀ ≤ B :=
      hFsub.le_of_frontier_le hAopen hAbdd hFcont hFfr w₀ hw₀A
    simp only [hFdef] at hFw₀
    have hexp : (1 + ε) * (Real.log ‖w₀ - c‖ - Real.log s) = t + ε * t := by
      rw [htdef]; ring
    rw [hexp, hεt] at hFw₀
    linarith
  -- ### The two-sided bound on `G∘e.symm + log‖·−c‖` near the pole.
  have hup : ∀ w ∈ ball c s \ {c},
      greenEnvelope p₀ (e.symm w) + Real.log ‖w - c‖ ≤ B + Real.log s := by
    intro w hw
    have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
    have h1 : greenEnvelope p₀ (e.symm w) ≤ B - (Real.log ‖w - c‖ - Real.log s) := by
      refine csSup_le ⟨v₀ (e.symm w), ⟨v₀, hv₀mem, rfl⟩⟩ ?_
      rintro b ⟨v, hv, rfl⟩
      have h2 := key v hv w hw
      linarith
    linarith
  have hlow : ∀ w ∈ ball c s \ {c},
      Real.log r ≤ greenEnvelope p₀ (e.symm w) + Real.log ‖w - c‖ := by
    intro w hw
    have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
    have hwt : w ∈ e.target := hssub hw.1
    have hne : e.symm w ≠ p₀ := hsymm_ne w hwt hwne
    have hxs : e.symm w ∈ e.source := hsymm_src w hwt
    have h1 : v₀ (e.symm w) ≤ greenEnvelope p₀ (e.symm w) := hmem_le v₀ hv₀mem _ hne
    have h2 : Real.log r - Real.log ‖w - c‖ ≤ v₀ (e.symm w) := by
      simp only [hv₀, if_pos hxs, hg, hsymm_eq w hwt]
      exact le_max_left _ _
    linarith
  -- ### Harmonicity of `G∘e.symm + log‖·−c‖` on the punctured disc.
  set u : ℂ → ℝ := fun w => greenEnvelope p₀ (e.symm w) + Real.log ‖w - c‖ with hu
  have huharm : HarmonicOnNhd u (ball c s \ {c}) := by
    intro w hw
    have hwne : w ≠ c := fun hcon => hw.2 (Set.mem_singleton_iff.2 hcon)
    have hwt : w ∈ e.target := hssub hw.1
    have h1 := (hGread w hwt hwne).add (hLg w hwne)
    have heq2 : ((greenEnvelope p₀ ∘ ⇑e.symm) + fun q : ℂ => Real.log ‖q - c‖) = u := by
      funext q
      simp only [hu, Pi.add_apply, Function.comp_apply]
    rw [heq2] at h1
    exact h1
  have hub : ∃ C, ∀ z ∈ ball c s \ {c}, |u z| ≤ C := by
    refine ⟨max (B + Real.log s) (-Real.log r), ?_⟩
    intro z hz
    rw [abs_le]
    constructor
    · have h1 := hlow z hz
      have h2 : -Real.log r ≤ max (B + Real.log s) (-Real.log r) := le_max_right _ _
      simp only [hu]
      linarith
    · have h1 := hup z hz
      simp only [hu]
      exact h1.trans (le_max_left _ _)
  -- ### Removable singularity and packaging.
  obtain ⟨h, hharm, heqon⟩ := exists_harmonicOnNhd_of_bounded_punctured hs0 huharm hub
  refine ⟨s, hs0, hssub, h, hharm, ?_⟩
  intro w hw
  have h5 := heqon hw
  simp only [hu] at h5
  exact h5

/-! ## The global map and injectivity -/

/-- **Monodromy globalization**: on a simply connected hyperbolic surface
there is a global holomorphic function whose modulus is `e^{−G}`, vanishing
exactly at the pole. -/
theorem exists_green_map [T2Space M] [SimplyConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) :
    ∃ φ : M → ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ ∧ φ p₀ = 0 ∧
      (∀ x, x ≠ p₀ → ‖φ x‖ = Real.exp (-(greenEnvelope p₀ x))) := by
  sorry

/-- **Injectivity** of the Green's map, via the Blaschke-transplant
comparison with the extremal property of the envelope. -/
theorem injective_green_map [T2Space M] [SimplyConnectedSpace M] [NoncompactSpace M]
    {p₀ : M} (hG : HasGreenFunction p₀) {φ : M → ℂ}
    (hφ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ) (h0 : φ p₀ = 0)
    (habs : ∀ x, x ≠ p₀ → ‖φ x‖ = Real.exp (-(greenEnvelope p₀ x))) :
    Function.Injective φ := by
  classical
  -- ## Step 0: the map sends the surface into the unit disc, vanishing only at the pole.
  have hGpos := greenEnvelope_pos hG
  have hlt : ∀ x : M, ‖φ x‖ < 1 := by
    intro x
    by_cases hx : x = p₀
    · rw [hx, h0, norm_zero]; exact one_pos
    · rw [habs x hx]
      calc Real.exp (-(greenEnvelope p₀ x)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith [hGpos x hx])
        _ = 1 := Real.exp_zero
  have hne0 : ∀ x : M, x ≠ p₀ → φ x ≠ 0 := by
    intro x hx h
    have h1 := habs x hx
    rw [h, norm_zero] at h1
    exact absurd h1.symm (ne_of_gt (Real.exp_pos _))
  -- ## Step 1: fix a collision and reduce to two points distinct from the pole.
  intro q₁ q₂ hq
  by_contra hne
  have hq₁ : q₁ ≠ p₀ := by
    intro h
    have h2 : φ q₂ = 0 := by rw [← hq, h]; exact h0
    have h3 : q₂ = p₀ := by
      by_contra h4
      exact hne0 q₂ h4 h2
    exact hne (h.trans h3.symm)
  have hq₂q₁ : q₂ ≠ q₁ := fun h => hne h.symm
  -- ## Step 2: generic bricks.
  -- Plane-level transfer of subharmonicity along equality of functions.
  have htransfer : ∀ (F G : ℂ → ℝ) (U W : Set ℂ), SubharmonicOn F U → W ⊆ U →
      Set.EqOn F G W → SubharmonicOn G W := by
    intro F G U W hF hWU hFG
    refine ⟨(hF.1.mono hWU).congr hFG.symm, ?_⟩
    intro c hc ρ hρ hb
    have h1 : G c = F c := (hFG hc).symm
    have h2 : Real.circleAverage F c ρ = Real.circleAverage G c ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      rw [abs_of_pos hρ] at hz
      exact hFG (hb (sphere_subset_closedBall hz))
    rw [h1, ← h2]
    exact hF.2 c (hWU hc) ρ hρ (hb.trans hWU)
  -- Surface-level: subharmonicity at a point respects equality near the point.
  have hcongM : ∀ (F G : M → ℝ) (x : M) (O : Set M), IsOpen O → x ∈ O →
      Set.EqOn F G O → MSubharmonicAt F x → MSubharmonicAt G x := by
    intro F G x O hO hxO hFG hF
    obtain ⟨r, hr, -, hsub⟩ := hF
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hopen : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O) :=
      (chartAt ℂ x).isOpen_inter_preimage_symm hO
    have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' O := by
      refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
      rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
      exact hxO
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (isOpen_ball.inter hopen)
      (chartAt ℂ x x) ⟨mem_ball_self hr, hmem⟩
    refine ⟨ρ, hρ, fun w hw => ((hρsub hw).2).1, ?_⟩
    refine htransfer _ _ _ _ hsub (fun w hw => (hρsub hw).1) ?_
    intro w hw
    exact hFG ((hρsub hw).2).2
  -- Sums of subharmonic functions are subharmonic.
  have haddM : ∀ (F G : M → ℝ) (x : M), MSubharmonicAt F x → MSubharmonicAt G x →
      MSubharmonicAt (fun y => F y + G y) x := by
    intro F G x hF hG
    obtain ⟨r₁, hr₁, hb₁, hs₁⟩ := hF
    obtain ⟨r₂, hr₂, -, hs₂⟩ := hG
    have hmono : ∀ (f : ℂ → ℝ) (U V : Set ℂ), SubharmonicOn f U → V ⊆ U →
        SubharmonicOn f V := fun f U V hf hVU =>
      ⟨hf.1.mono hVU, fun c hc ρ hρ hball => hf.2 c (hVU hc) ρ hρ (hball.trans hVU)⟩
    have hs₁' := hmono _ _ _ hs₁ (ball_subset_ball (min_le_left r₁ r₂))
    have hs₂' := hmono _ _ _ hs₂ (ball_subset_ball (min_le_right r₁ r₂))
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (ball_subset_ball (min_le_left r₁ r₂)).trans hb₁, ?_, ?_⟩
    · exact hs₁'.1.add hs₂'.1
    · intro c hc ρ hρ hb
      have hsph : sphere c ρ ⊆ ball (chartAt ℂ x x) (min r₁ r₂) :=
        sphere_subset_closedBall.trans hb
      have hci₁ : CircleIntegrable (F ∘ (chartAt ℂ x).symm) c ρ :=
        (hs₁'.1.mono hsph).circleIntegrable hρ.le
      have hci₂ : CircleIntegrable (G ∘ (chartAt ℂ x).symm) c ρ :=
        (hs₂'.1.mono hsph).circleIntegrable hρ.le
      have havg := Real.circleAverage_fun_add hci₁ hci₂
      have h₁ := hs₁'.2 c hc ρ hρ hb
      have h₂ := hs₂'.2 c hc ρ hρ hb
      calc ((fun y => F y + G y) ∘ (chartAt ℂ x).symm) c
          = (F ∘ (chartAt ℂ x).symm) c + (G ∘ (chartAt ℂ x).symm) c := rfl
        _ ≤ Real.circleAverage (F ∘ (chartAt ℂ x).symm) c ρ
            + Real.circleAverage (G ∘ (chartAt ℂ x).symm) c ρ := add_le_add h₁ h₂
        _ = Real.circleAverage
            (fun w => (F ∘ (chartAt ℂ x).symm) w + (G ∘ (chartAt ℂ x).symm) w) c ρ :=
            havg.symm
        _ = Real.circleAverage ((fun y => F y + G y) ∘ (chartAt ℂ x).symm) c ρ := rfl
  -- The logarithm of the modulus of a nonvanishing holomorphic function is harmonic.
  have hlogM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M, Ψ x ≠ 0 →
      MHarmonicAt (fun y => Real.log ‖Ψ y‖) x := by
    intro Ψ hΨm x hx
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have h2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) h1
    have h3 : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
    have h4 : (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
      simp only [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      exact hx
    exact h3.harmonicAt_log_norm h4
  -- The chart reading of a holomorphic function is analytic at the chart image.
  have hreadM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → ∀ x : M,
      AnalyticAt ℂ (Ψ ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
    intro Ψ hΨm x
    have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm (chartAt ℂ x x) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
        (mem_chart_target ℂ x)
    have h2 := (hΨm ((chartAt ℂ x).symm (chartAt ℂ x x))).comp (chartAt ℂ x x) h1
    exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
  -- The singleton `{0}` is not open in the plane.
  have hnotopen0 : ¬ IsOpen ({(0 : ℂ)} : Set ℂ) := by
    intro hcon
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcon 0 rfl
    have h1 : (↑(ε / 2) : ℂ) ∈ ball (0 : ℂ) ε := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    have h2 := hball h1
    rw [Set.mem_singleton_iff, Complex.ofReal_eq_zero] at h2
    linarith
  -- Zeros of a nonconstant holomorphic function on the surface are isolated.
  have hisoM : ∀ Ψ : M → ℂ, (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) → (∃ y₀, Ψ y₀ ≠ 0) →
      ∀ z : M, Ψ z = 0 → ∀ᶠ y in 𝓝[≠] z, Ψ y ≠ 0 := by
    intro Ψ hΨm hex z hz
    obtain ⟨y₀, hy₀⟩ := hex
    have hzsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    rcases (hreadM Ψ hΨm z).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      -- `Ψ` would vanish on an open set, contradicting the open mapping theorem.
      have hop : IsOpenMap Ψ := by
        refine isOpenMap_of_contMDiff_of_not_const (fun y => hΨm y) ?_
        rintro ⟨c, hc⟩
        rw [hc z] at hz
        rw [hc y₀, hz] at hy₀
        exact hy₀ rfl
      have h2 : ∀ᶠ y in 𝓝 z, Ψ y = 0 := by
        have hc : ContinuousAt (chartAt ℂ z) z := (chartAt ℂ z).continuousAt hzsrc
        filter_upwards [hc.eventually hcase,
          (chartAt ℂ z).open_source.mem_nhds hzsrc] with y h1y hsy
        have : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := h1y
        rwa [(chartAt ℂ z).left_inv hsy] at this
      obtain ⟨O, hOsub, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp h2
      have himg : Ψ '' O = {0} := by
        apply Set.Subset.antisymm
        · rintro w ⟨y, hy, rfl⟩
          exact hOsub hy
        · rintro w hw
          rw [Set.mem_singleton_iff] at hw
          exact ⟨z, hzO, by rw [hw, hz]⟩
      have := hop O hOopen
      rw [himg] at this
      exact hnotopen0 this
    · -- Transfer the punctured-neighborhood nonvanishing through the chart.
      have htend : Tendsto (chartAt ℂ z) (𝓝[≠] z) (𝓝[≠] (chartAt ℂ z z)) := by
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
      have : Ψ ((chartAt ℂ z).symm (chartAt ℂ z y)) = 0 := by
        rw [(chartAt ℂ z).left_inv hys]
        exact hcon
      exact this
  -- Punctured coordinate balls are connected (polar parametrization).
  have hpunc : ∀ (c : ℂ) (r : ℝ), 0 < r → IsConnected (ball c r \ {c}) := by
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
    refine ⟨Set.Nonempty.image _
      ⟨(r / 2, 0), ⟨half_pos hr, half_lt_self hr⟩, Set.mem_univ _⟩, ?_⟩
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hcont.continuousOn
  -- Plane propagation: a nonpositive subharmonic function vanishing at one point of a
  -- preconnected open set vanishes identically.
  have hprop : ∀ (S : Set ℂ) (F : ℂ → ℝ), IsOpen S → IsPreconnected S →
      SubharmonicOn F S → (∀ w ∈ S, F w ≤ 0) → ∀ w₀ ∈ S, F w₀ = 0 → ∀ w ∈ S, F w = 0 := by
    intro S F hSopen hSpre hFsub hFle w₀ hw₀ hFw₀
    have hu : IsOpen {w : ℂ | ∀ᶠ z in 𝓝 w, F z = 0} := isOpen_setOf_eventually_nhds
    have hv : IsOpen (S ∩ F ⁻¹' {(0 : ℝ)}ᶜ) :=
      hFsub.1.isOpen_inter_preimage hSopen isOpen_compl_singleton
    have hdisj : Disjoint {w : ℂ | ∀ᶠ z in 𝓝 w, F z = 0} (S ∩ F ⁻¹' {(0 : ℝ)}ᶜ) := by
      rw [Set.disjoint_left]
      rintro w hw ⟨-, hw2⟩
      exact hw2 hw.self_of_nhds
    have hzero_mem : ∀ w ∈ S, F w = 0 → ∀ᶠ z in 𝓝 w, F z = 0 := by
      intro w hw hFw
      have hmax : ∀ z ∈ S, F z ≤ F w := by
        intro z hz
        rw [hFw]
        exact hFle z hz
      filter_upwards [SubharmonicOn.eventually_eq_of_le hSopen hFsub hw hmax] with z hz
      rw [hz, hFw]
    have hcover : S ⊆ {w : ℂ | ∀ᶠ z in 𝓝 w, F z = 0} ∪ (S ∩ F ⁻¹' {(0 : ℝ)}ᶜ) := by
      intro w hw
      by_cases hFw : F w = 0
      · exact Or.inl (hzero_mem w hw hFw)
      · exact Or.inr ⟨hw, hFw⟩
    have hkey := IsPreconnected.subset_left_of_subset_union hu hv hdisj hcover
      ⟨w₀, hw₀, hzero_mem w₀ hw₀ hFw₀⟩ hSpre
    intro w hw
    exact (hkey hw).self_of_nhds
  -- Nearby-point picker: every neighborhood of a point contains a distinct point.
  have hpick : ∀ (z : M) (A : Set M), A ∈ 𝓝 z → ∃ y ∈ A, y ≠ z := by
    intro z A hA
    obtain ⟨O, hOsub, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp hA
    have hzsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hVopen : IsOpen (O ∩ (chartAt ℂ z).source) :=
      hOopen.inter (chartAt ℂ z).open_source
    have himg : IsOpen ((chartAt ℂ z) '' (O ∩ (chartAt ℂ z).source)) :=
      (chartAt ℂ z).isOpen_image_of_subset_source hVopen Set.inter_subset_right
    obtain ⟨s, hs, hballs⟩ := Metric.isOpen_iff.mp himg (chartAt ℂ z z)
      ⟨z, ⟨hzO, hzsrc⟩, rfl⟩
    have hmem : chartAt ℂ z z + (↑(s / 2) : ℂ) ∈ ball (chartAt ℂ z z) s := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    obtain ⟨y, ⟨hyO, hysrc⟩, hyeq⟩ := hballs hmem
    refine ⟨y, hOsub hyO, ?_⟩
    intro hcon
    rw [hcon] at hyeq
    have h3 : (↑(s / 2) : ℂ) = 0 := by
      have h4 : chartAt ℂ z z + (↑(s / 2) : ℂ) = chartAt ℂ z z + 0 := by
        rw [add_zero]; exact hyeq.symm
      exact add_left_cancel h4
    rw [Complex.ofReal_eq_zero] at h3
    linarith
  -- The Blaschke transplant package: denominator, disc bound, holomorphy.
  have hBLA : ∀ (f : M → ℂ) (b : ℂ), (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y) →
      (∀ y, ‖f y‖ < 1) → ‖b‖ < 1 → ∀ y : M,
      (1 - (starRingEnd ℂ) b * f y ≠ 0) ∧
      ‖(f y - b) / (1 - (starRingEnd ℂ) b * f y)‖ < 1 ∧
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun x => (f x - b) / (1 - (starRingEnd ℂ) b * f x)) y := by
    intro f b hfm hflt hb y
    have hden : ∀ x : M, 1 - (starRingEnd ℂ) b * f x ≠ 0 := by
      intro x h
      have h1 : ‖(starRingEnd ℂ) b * f x‖ < 1 := by
        rw [norm_mul, Complex.norm_conj]
        calc ‖b‖ * ‖f x‖ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left (hflt x).le (norm_nonneg b)
          _ = ‖b‖ := mul_one _
          _ < 1 := hb
      rw [← sub_eq_zero.mp h, norm_one] at h1
      exact lt_irrefl 1 h1
    refine ⟨hden y, ?_, ?_⟩
    · rw [norm_div, div_lt_one (norm_pos_iff.mpr (hden y))]
      have hid : Complex.normSq (1 - (starRingEnd ℂ) b * f y) - Complex.normSq (f y - b)
          = (1 - Complex.normSq b) * (1 - Complex.normSq (f y)) := by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
          Complex.mul_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
        ring
      have hnb : Complex.normSq b < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg b]
      have hnz : Complex.normSq (f y) < 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg (f y), hflt y]
      have hlt2 : Complex.normSq (f y - b) < Complex.normSq (1 - (starRingEnd ℂ) b * f y) := by
        nlinarith [hid, hnb, hnz]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt2
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt2
    · have houter : ContDiffAt ℂ ω (fun z : ℂ => (z - b) / (1 - (starRingEnd ℂ) b * z))
          (f y) :=
        ContDiffAt.div (contDiffAt_id.sub contDiffAt_const)
          (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) (hden y)
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
          (fun z : ℂ => (z - b) / (1 - (starRingEnd ℂ) b * z)) (f y) :=
        contMDiffAt_iff_contDiffAt.mpr houter
      exact h1.comp y (hfm y)
  -- ## Step 3: the comparison engine (per-candidate Blaschke comparison at a pole).
  -- For a holomorphic `Ψ` into the disc vanishing at `q`, the Perron family at `q`
  -- is bounded and the envelope is dominated by `−log‖Ψ‖`.
  have MAIN : ∀ (q : M) (Ψ : M → ℂ), (∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω Ψ y) →
      (∀ y, ‖Ψ y‖ < 1) → Ψ q = 0 → (∃ y₀, Ψ y₀ ≠ 0) →
      (∀ x, x ≠ q → BddAbove ((fun v => v x) '' greenFamily q)) ∧
      ∀ x, x ≠ q → Ψ x ≠ 0 → greenEnvelope q x ≤ -Real.log ‖Ψ x‖ := by
    intro q Ψ hΨm hΨlt hΨq hΨex
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
    have hmem1 : chartAt ℂ q q ∈ (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 := by
      refine ⟨(chartAt ℂ q).map_source hqsrc, ?_⟩
      rw [Set.mem_preimage, hcq]
      exact hqW0
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen1 (chartAt ℂ q q) hmem1
    -- The small pole disk `V'` and its compact closure barrel `K'`.
    have hρ2 : 0 < ρ / 2 := by linarith
    have hcbsub : closedBall (chartAt ℂ q q) (ρ / 2) ⊆
        (chartAt ℂ q).target ∩ (chartAt ℂ q).symm ⁻¹' W0 :=
      (Metric.closedBall_subset_ball (by linarith)).trans hρsub
    obtain ⟨V', hV'def⟩ : ∃ S : Set M,
        S = (chartAt ℂ q).source ∩ chartAt ℂ q ⁻¹' ball (chartAt ℂ q q) (ρ / 2) := ⟨_, rfl⟩
    have hV'open : IsOpen V' := by
      rw [hV'def]
      exact (chartAt ℂ q).continuousOn.isOpen_inter_preimage (chartAt ℂ q).open_source
        isOpen_ball
    have hqV' : q ∈ V' := by
      rw [hV'def]
      exact ⟨hqsrc, by rw [Set.mem_preimage]; exact mem_ball_self hρ2⟩
    -- Nonvanishing of `Ψ` on the punctured pole disk (pullback of `W0`).
    have hV'ne : ∀ y ∈ V', y ≠ q → Ψ y ≠ 0 := by
      intro y hy hyq
      rw [hV'def] at hy
      have h1 : chartAt ℂ q y ∈ ball (chartAt ℂ q q) ρ :=
        ball_subset_ball (by linarith) hy.2
      have h2 : (chartAt ℂ q).symm (chartAt ℂ q y) ∈ W0 := (hρsub h1).2
      rw [(chartAt ℂ q).left_inv hy.1] at h2
      exact hW0sub h2 hyq
    -- The compact barrel and the boundary sphere.
    obtain ⟨K', hK'def⟩ : ∃ S : Set M,
        S = (chartAt ℂ q).symm '' closedBall (chartAt ℂ q q) (ρ / 2) := ⟨_, rfl⟩
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
        y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2) := by
      intro y hy hyV'
      rw [hK'def] at hy
      obtain ⟨w, hw, rfl⟩ := hy
      have hwt : w ∈ (chartAt ℂ q).target := (hcbsub hw).1
      have hysrc : (chartAt ℂ q).symm w ∈ (chartAt ℂ q).source := (chartAt ℂ q).map_target hwt
      have hwch : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
      have hnb : w ∉ ball (chartAt ℂ q q) (ρ / 2) := by
        intro hwb
        apply hyV'
        rw [hV'def]
        exact ⟨hysrc, by rw [Set.mem_preimage, hwch]; exact hwb⟩
      have hd : dist w (chartAt ℂ q q) = ρ / 2 := by
        have h1 := mem_closedBall.1 hw
        have h2 : ¬ dist w (chartAt ℂ q q) < ρ / 2 := fun h => hnb (mem_ball.2 h)
        linarith [not_lt.mp h2]
      exact ⟨w, mem_sphere.2 hd, rfl⟩
    have hedge_ne : ∀ y ∈ (chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2), Ψ y ≠ 0 := by
      rintro y ⟨w, hw, rfl⟩
      have hwb : w ∈ ball (chartAt ℂ q q) ρ := by
        rw [mem_ball]
        rw [mem_sphere.1 hw]
        linarith
      have hwt : w ∈ (chartAt ℂ q).target := (hρsub hwb).1
      have hW0mem : (chartAt ℂ q).symm w ∈ W0 := (hρsub hwb).2
      have hyne : (chartAt ℂ q).symm w ≠ q := by
        intro hcon
        have h1 : chartAt ℂ q ((chartAt ℂ q).symm w) = w := (chartAt ℂ q).right_inv hwt
        rw [hcon] at h1
        have h2 : dist w (chartAt ℂ q q) = ρ / 2 := mem_sphere.1 hw
        rw [← h1, dist_self] at h2
        linarith
      exact hW0sub hW0mem hyne
    -- The minimum of `‖Ψ‖` on the boundary sphere is positive.
    have hS'cp : IsCompact ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2)) := by
      refine (isCompact_sphere _ _).image_of_continuousOn ?_
      refine (chartAt ℂ q).continuousOn_symm.mono ?_
      refine (sphere_subset_closedBall.trans ?_)
      exact hcbsub.trans Set.inter_subset_left
    have hS'ne : ((chartAt ℂ q).symm '' sphere (chartAt ℂ q q) (ρ / 2)).Nonempty :=
      Set.Nonempty.image _ (NormedSpace.sphere_nonempty.2 hρ2.le)
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
    have hΛ3 : ∀ N (x : M), x ∉ V' → Ψ x ≠ 0 → Λ N x = max (Real.log ‖Ψ x‖) (-N) := by
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
      have hgan : AnalyticAt ℂ (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) := hreadM Ψ hΨm q
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
      have hΨbound : ‖Ψ x‖ ≤ (‖deriv (Ψ ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)‖ + 1)
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
    constructor
    · -- Boundedness of the family at every point off the pole (point-independence).
      intro x hx
      refine ⟨-Λ (max (-Real.log (‖Ψ ym‖ / 2)) 1) x, ?_⟩
      rintro t ⟨v, hv, rfl⟩
      have h1 := key (max (-Real.log (‖Ψ ym‖ / 2)) 1) (le_max_left _ _)
        (lt_of_lt_of_le one_pos (le_max_right _ _)) v hv x hx
      have h2 : (fun v : M → ℝ => v x) v = v x := rfl
      rw [h2]
      linarith
    · -- The envelope bound `greenEnvelope q ≤ −log‖Ψ‖`.
      intro x hx hx0
      have hlogneg : Real.log ‖Ψ x‖ < 0 :=
        Real.log_neg (norm_pos_iff.mpr hx0) (hΨlt x)
      have hNpos : 0 < max (max (-Real.log (‖Ψ ym‖ / 2)) 1) (-Real.log ‖Ψ x‖) :=
        lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _))
      have hΛval : Λ (max (max (-Real.log (‖Ψ ym‖ / 2)) 1) (-Real.log ‖Ψ x‖)) x
          = Real.log ‖Ψ x‖ := by
        by_cases hxV' : x ∈ V'
        · exact hΛ1 _ x hxV'
        · rw [hΛ3 _ x hxV' hx0]
          refine max_eq_left ?_
          have h1 : -Real.log ‖Ψ x‖
              ≤ max (max (-Real.log (‖Ψ ym‖ / 2)) 1) (-Real.log ‖Ψ x‖) :=
            le_max_right _ _
          linarith
      have hsup : sSup ((fun v => v x) '' greenFamily q) ≤ -Real.log ‖Ψ x‖ := by
        refine Real.sSup_le ?_ (by linarith)
        rintro t ⟨v, hv, rfl⟩
        have h1 := key _ (le_trans (le_max_left _ _) (le_max_left _ _)) hNpos v hv x hx
        rw [hΛval] at h1
        have h2 : (fun v : M → ℝ => v x) v = v x := rfl
        rw [h2]
        linarith
      exact hsup
  -- ## Step 4: instantiate the engine at the collision transplant `ψ = B_a ∘ φ`.
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = φ q₁ := ⟨_, rfl⟩
  have ha1 : ‖a‖ < 1 := by rw [ha]; exact hlt q₁
  have ha0 : a ≠ 0 := by rw [ha]; exact hne0 q₁ hq₁
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : M → ℂ,
      ψ = fun x => (φ x - a) / (1 - (starRingEnd ℂ) a * φ x) := ⟨_, rfl⟩
  have hφm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ y := fun y => hφ y
  have hψm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ y := by
    intro y
    rw [hψdef]
    exact (hBLA φ a hφm hlt ha1 y).2.2
  have hψlt : ∀ y, ‖ψ y‖ < 1 := by
    intro y
    rw [hψdef]
    exact (hBLA φ a hφm hlt ha1 y).2.1
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr fun y => (hψm y).continuousAt
  have hψq₁ : ψ q₁ = 0 := by
    simp only [hψdef]
    rw [← ha, sub_self, zero_div]
  have hψq₂ : ψ q₂ = 0 := by
    simp only [hψdef]
    have h2 : φ q₂ = a := by rw [ha, hq]
    rw [h2, sub_self, zero_div]
  have hψp₀ : ψ p₀ = -a := by
    simp only [hψdef, h0, mul_zero, sub_zero, zero_sub, div_one]
  have hψp₀ne : ψ p₀ ≠ 0 := by
    rw [hψp₀]
    exact neg_ne_zero.mpr ha0
  obtain ⟨hbdd₁, hb₁⟩ := MAIN q₁ ψ hψm hψlt hψq₁ ⟨p₀, hψp₀ne⟩
  -- Point-independence (A5b): the Green function at `q₁` exists.
  have hGF₁ : HasGreenFunction q₁ := ⟨p₀, Ne.symm hq₁, hbdd₁ p₀ (Ne.symm hq₁)⟩
  -- ## Step 5: swap the roles of the poles via the Green map at `q₁` (A6+A7 at `q₁`).
  obtain ⟨φ', hφ'sm, hφ'0, hφ'abs⟩ := exists_green_map hGF₁
  have hG₁pos := greenEnvelope_pos hGF₁
  have hφ'lt : ∀ y : M, ‖φ' y‖ < 1 := by
    intro y
    by_cases hy : y = q₁
    · rw [hy, hφ'0, norm_zero]; exact one_pos
    · rw [hφ'abs y hy]
      calc Real.exp (-(greenEnvelope q₁ y)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith [hG₁pos y hy])
        _ = 1 := Real.exp_zero
  have hφ'm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ' y := fun y => hφ'sm y
  obtain ⟨a', ha'⟩ : ∃ b : ℂ, b = φ' p₀ := ⟨_, rfl⟩
  have ha'1 : ‖a'‖ < 1 := by rw [ha']; exact hφ'lt p₀
  have ha'norm : ‖a'‖ = Real.exp (-(greenEnvelope q₁ p₀)) := by
    rw [ha']
    exact hφ'abs p₀ (Ne.symm hq₁)
  have ha'0 : a' ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha'norm
    exact absurd ha'norm.symm (ne_of_gt (Real.exp_pos _))
  obtain ⟨ψ', hψ'def⟩ : ∃ g : M → ℂ,
      g = fun x => (φ' x - a') / (1 - (starRingEnd ℂ) a' * φ' x) := ⟨_, rfl⟩
  have hψ'm : ∀ y, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ψ' y := by
    intro y
    rw [hψ'def]
    exact (hBLA φ' a' hφ'm hφ'lt ha'1 y).2.2
  have hψ'lt : ∀ y, ‖ψ' y‖ < 1 := by
    intro y
    rw [hψ'def]
    exact (hBLA φ' a' hφ'm hφ'lt ha'1 y).2.1
  have hψ'p₀ : ψ' p₀ = 0 := by
    simp only [hψ'def]
    rw [← ha', sub_self, zero_div]
  have hψ'q₁ : ψ' q₁ = -a' := by
    simp only [hψ'def, hφ'0, mul_zero, sub_zero, zero_sub, div_one]
  have hψ'q₁ne : ψ' q₁ ≠ 0 := by
    rw [hψ'q₁]
    exact neg_ne_zero.mpr ha'0
  obtain ⟨-, hb₀⟩ := MAIN p₀ ψ' hψ'm hψ'lt hψ'p₀ ⟨q₁, hψ'q₁ne⟩
  -- Evaluate the two comparisons: equality holds at the base point (symmetry byproduct).
  have hGq₁ : greenEnvelope p₀ q₁ = -Real.log ‖a‖ := by
    have h1 : ‖a‖ = Real.exp (-(greenEnvelope p₀ q₁)) := by
      rw [ha]
      exact habs q₁ hq₁
    rw [h1, Real.log_exp]
    ring
  have hswap : greenEnvelope p₀ q₁ ≤ greenEnvelope q₁ p₀ := by
    have h1 := hb₀ q₁ hq₁ hψ'q₁ne
    rw [hψ'q₁, norm_neg, ha'norm, Real.log_exp] at h1
    linarith
  have hfwd : greenEnvelope q₁ p₀ ≤ -Real.log ‖a‖ := by
    have h1 := hb₁ p₀ (Ne.symm hq₁) hψp₀ne
    rwa [hψp₀, norm_neg] at h1
  have heqp₀ : greenEnvelope q₁ p₀ + Real.log ‖ψ p₀‖ = 0 := by
    have h2 : -Real.log ‖a‖ ≤ greenEnvelope q₁ p₀ := by
      rw [← hGq₁]
      exact hswap
    have h3 : greenEnvelope q₁ p₀ = -Real.log ‖a‖ := le_antisymm hfwd h2
    rw [hψp₀, norm_neg, h3]
    ring
  -- ## Step 6: the extremality analysis — `G₁ + log‖ψ‖` vanishes identically.
  obtain ⟨u, hudef⟩ : ∃ u : M → ℝ,
      u = fun y => greenEnvelope q₁ y + Real.log ‖ψ y‖ := ⟨_, rfl⟩
  have hGE₁ := mharmonicOn_greenEnvelope hGF₁
  have huharm : ∀ x : M, ψ x ≠ 0 → MHarmonicAt u x := by
    intro x hx
    have hxq₁ : x ≠ q₁ := by
      intro hcon
      rw [hcon] at hx
      exact hx hψq₁
    have h1 : MHarmonicAt (greenEnvelope q₁) x := hGE₁.1 x hxq₁
    have h2 : MHarmonicAt (fun y => Real.log ‖ψ y‖) x := hlogM ψ hψm x hx
    have h3 := h1.add h2
    rw [hudef]
    exact h3
  have hule : ∀ x : M, ψ x ≠ 0 → u x ≤ 0 := by
    intro x hx
    have hxq₁ : x ≠ q₁ := by
      intro hcon
      rw [hcon] at hx
      exact hx hψq₁
    have h1 := hb₁ x hxq₁ hx
    rw [hudef]
    change greenEnvelope q₁ x + Real.log ‖ψ x‖ ≤ 0
    linarith
  have hup₀ : u p₀ = 0 := by
    rw [hudef]
    exact heqp₀
  -- The propagation set: `u` vanishes near the point, wherever `ψ ≠ 0`.
  obtain ⟨P, hPdef⟩ : ∃ P : Set M,
      P = {x : M | ∀ᶠ y in 𝓝 x, ψ y ≠ 0 → u y = 0} := ⟨_, rfl⟩
  have hPopen : IsOpen P := by
    rw [hPdef]
    exact isOpen_setOf_eventually_nhds
  -- The chart reading of `u` is subharmonic on plane sets avoiding the zero set.
  have hplane : ∀ (x : M) (S : Set ℂ), S ⊆ (chartAt ℂ x).target →
      (∀ w ∈ S, ψ ((chartAt ℂ x).symm w) ≠ 0) →
      SubharmonicOn (u ∘ (chartAt ℂ x).symm) S := by
    intro x S hSsub hSne
    refine HarmonicOnNhd.subharmonicOn ?_
    intro w hw
    have hwsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).map_target (hSsub hw)
    have h1 : MHarmonicAt u ((chartAt ℂ x).symm w) := huharm _ (hSne w hw)
    have h2 := (mharmonicAt_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas x) hwsrc).mp h1
    rwa [(chartAt ℂ x).right_inv (hSsub hw)] at h2
  -- `P` is closed: vanishing propagates over chart balls and across isolated zeros.
  have hPclosed : IsClosed P := by
    refine isClosed_of_closure_subset fun x hx => ?_
    by_cases hxP : x ∈ P
    · exact hxP
    have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    by_cases hx0 : ψ x = 0
    · -- an isolated zero of `ψ`: propagate over the punctured chart ball
      obtain ⟨W1, hW1sub, hW1open, hxW1⟩ := _root_.mem_nhds_iff.mp
        (eventually_nhdsWithin_iff.mp (hisoM ψ hψm ⟨p₀, hψp₀ne⟩ x hx0))
      have hopen1 : IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' W1) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm hW1open
      have hmem1 : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' W1 := by
        refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
        rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
        exact hxW1
      obtain ⟨s, hs, hssub⟩ := Metric.isOpen_iff.1 hopen1 _ hmem1
      have hSne : ∀ w ∈ ball (chartAt ℂ x x) s \ {chartAt ℂ x x},
          ψ ((chartAt ℂ x).symm w) ≠ 0 := by
        rintro w ⟨hwb, hwc⟩
        have h1 : (chartAt ℂ x).symm w ∈ W1 := (hssub hwb).2
        refine hW1sub h1 ?_
        intro hcon
        apply hwc
        rw [Set.mem_singleton_iff]
        have h2 : chartAt ℂ x ((chartAt ℂ x).symm w) = w :=
          (chartAt ℂ x).right_inv (hssub hwb).1
        rw [hcon] at h2
        exact h2.symm
      have hBopen : IsOpen
          ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s) :=
        (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
          isOpen_ball
      have hxB : x ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s :=
        ⟨hxsrc, by rw [Set.mem_preimage]; exact mem_ball_self hs⟩
      obtain ⟨p, hpB, hpP⟩ := _root_.mem_closure_iff.mp hx _ hBopen hxB
      have hpx : p ≠ x := by
        intro hcon
        rw [hcon] at hpP
        exact hxP hpP
      have hw₀S : chartAt ℂ x p ∈ ball (chartAt ℂ x x) s \ {chartAt ℂ x x} := by
        refine ⟨hpB.2, ?_⟩
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact hpx ((chartAt ℂ x).injOn hpB.1 hxsrc hcon)
      have hw₀0 : (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x p) = 0 := by
        have h1 : ψ p ≠ 0 := by
          have h2 := hSne (chartAt ℂ x p) hw₀S
          rwa [(chartAt ℂ x).left_inv hpB.1] at h2
        have hpP' : ∀ᶠ y in 𝓝 p, ψ y ≠ 0 → u y = 0 := by
          rw [hPdef] at hpP
          exact hpP
        have h3 : u p = 0 := hpP'.self_of_nhds h1
        change u ((chartAt ℂ x).symm (chartAt ℂ x p)) = 0
        rw [(chartAt ℂ x).left_inv hpB.1]
        exact h3
      have hall := hprop (ball (chartAt ℂ x x) s \ {chartAt ℂ x x})
        (u ∘ (chartAt ℂ x).symm) (isOpen_ball.sdiff isClosed_singleton)
        (hpunc (chartAt ℂ x x) s hs).isPreconnected
        (hplane x _ (fun w hw => (hssub hw.1).1) hSne)
        (fun w hw => hule _ (hSne w hw)) (chartAt ℂ x p) hw₀S hw₀0
      rw [hPdef]
      change ∀ᶠ y in 𝓝 x, ψ y ≠ 0 → u y = 0
      filter_upwards [hBopen.mem_nhds hxB] with y hy hy0
      by_cases hyx : y = x
      · exfalso
        rw [hyx] at hy0
        exact hy0 hx0
      · have h1 : chartAt ℂ x y ∈ ball (chartAt ℂ x x) s \ {chartAt ℂ x x} := by
          refine ⟨hy.2, ?_⟩
          intro hcon
          rw [Set.mem_singleton_iff] at hcon
          exact hyx ((chartAt ℂ x).injOn hy.1 hxsrc hcon)
        have h2 := hall (chartAt ℂ x y) h1
        change u ((chartAt ℂ x).symm (chartAt ℂ x y)) = 0 at h2
        rwa [(chartAt ℂ x).left_inv hy.1] at h2
    · -- a nonvanishing point of `ψ`: propagate over a full chart ball
      have hopen1 : IsOpen
          ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {y : M | ψ y ≠ 0}) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm
          (isOpen_compl_singleton.preimage hψc)
      have hmem1 : chartAt ℂ x x ∈
          (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' {y : M | ψ y ≠ 0} := by
        refine ⟨(chartAt ℂ x).map_source hxsrc, ?_⟩
        rw [Set.mem_preimage, (chartAt ℂ x).left_inv hxsrc]
        exact hx0
      obtain ⟨s, hs, hssub⟩ := Metric.isOpen_iff.1 hopen1 _ hmem1
      have hSne : ∀ w ∈ ball (chartAt ℂ x x) s, ψ ((chartAt ℂ x).symm w) ≠ 0 :=
        fun w hw => (hssub hw).2
      have hBopen : IsOpen
          ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s) :=
        (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source
          isOpen_ball
      have hxB : x ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) s :=
        ⟨hxsrc, by rw [Set.mem_preimage]; exact mem_ball_self hs⟩
      obtain ⟨p, hpB, hpP⟩ := _root_.mem_closure_iff.mp hx _ hBopen hxB
      have hw₀0 : (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x p) = 0 := by
        have h1 : ψ p ≠ 0 := by
          have h2 := hSne (chartAt ℂ x p) hpB.2
          rwa [(chartAt ℂ x).left_inv hpB.1] at h2
        have hpP' : ∀ᶠ y in 𝓝 p, ψ y ≠ 0 → u y = 0 := by
          rw [hPdef] at hpP
          exact hpP
        have h3 : u p = 0 := hpP'.self_of_nhds h1
        change u ((chartAt ℂ x).symm (chartAt ℂ x p)) = 0
        rw [(chartAt ℂ x).left_inv hpB.1]
        exact h3
      have hall := hprop (ball (chartAt ℂ x x) s) (u ∘ (chartAt ℂ x).symm)
        isOpen_ball (convex_ball _ _).isPreconnected
        (hplane x _ (fun w hw => (hssub hw).1) hSne)
        (fun w hw => hule _ (hSne w hw)) (chartAt ℂ x p) hpB.2 hw₀0
      rw [hPdef]
      change ∀ᶠ y in 𝓝 x, ψ y ≠ 0 → u y = 0
      filter_upwards [hBopen.mem_nhds hxB] with y hy hy0
      have h2 := hall (chartAt ℂ x y) hy.2
      change u ((chartAt ℂ x).symm (chartAt ℂ x y)) = 0 at h2
      rwa [(chartAt ℂ x).left_inv hy.1] at h2
  -- `P` is nonempty: the strong maximum principle at the equality point `p₀`.
  have hPuniv : P = Set.univ := by
    refine IsClopen.eq_univ ⟨hPclosed, hPopen⟩ ⟨p₀, ?_⟩
    rw [hPdef]
    change ∀ᶠ y in 𝓝 p₀, ψ y ≠ 0 → u y = 0
    have hUopen : IsOpen {y : M | ψ y ≠ 0} := isOpen_compl_singleton.preimage hψc
    have hUsub : MSubharmonicOn u {y : M | ψ y ≠ 0} :=
      fun y hy => (huharm y hy).msubharmonicAt
    have hmax : ∀ y ∈ {y : M | ψ y ≠ 0}, u y ≤ u p₀ := by
      intro y hy
      rw [hup₀]
      exact hule y hy
    have hev := MSubharmonicAt.eventually_eq_of_le hUopen hψp₀ne hUsub hmax
    filter_upwards [hev] with y hy hy0
    rw [hy]
    exact hup₀
  -- ## Step 7: contradiction at the second collision point `q₂`.
  have hq₂P : q₂ ∈ P := by rw [hPuniv]; exact Set.mem_univ q₂
  rw [hPdef] at hq₂P
  have hq₂P' : ∀ᶠ y in 𝓝 q₂, ψ y ≠ 0 → u y = 0 := hq₂P
  have hG₁cont : ContinuousAt (greenEnvelope q₁) q₂ := (hGE₁.1 q₂ hq₂q₁).continuousAt
  have hE3 : ∀ᶠ y in 𝓝 q₂, greenEnvelope q₁ y < greenEnvelope q₁ q₂ + 1 :=
    hG₁cont.tendsto.eventually_lt_const (by linarith)
  have hE4 : ∀ᶠ y in 𝓝 q₂, ‖ψ y‖ < Real.exp (-(greenEnvelope q₁ q₂ + 1)) := by
    have h1 : ContinuousAt (fun y => ‖ψ y‖) q₂ := hψc.norm.continuousAt
    have h2 : ‖ψ q₂‖ = 0 := by rw [hψq₂, norm_zero]
    have h3 := h1.tendsto
    rw [h2] at h3
    exact h3.eventually_lt_const (Real.exp_pos _)
  have hE2 : ∀ᶠ y in 𝓝 q₂, y ∈ ({q₂}ᶜ : Set M) → ψ y ≠ 0 :=
    eventually_nhdsWithin_iff.mp (hisoM ψ hψm ⟨p₀, hψp₀ne⟩ q₂ hψq₂)
  obtain ⟨z, hzE, hzne⟩ := hpick q₂ _ (hq₂P'.and (hE3.and (hE4.and hE2)))
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hzE
  have hzψ : ψ z ≠ 0 := hz4 hzne
  have hzu : u z = 0 := hz1 hzψ
  have hzlog : Real.log ‖ψ z‖ < -(greenEnvelope q₁ q₂ + 1) := by
    have h1 := Real.log_lt_log (norm_pos_iff.mpr hzψ) hz3
    rwa [Real.log_exp] at h1
  have hzu' : u z < 0 := by
    rw [hudef]
    change greenEnvelope q₁ z + Real.log ‖ψ z‖ < 0
    linarith
  rw [hzu] at hzu'
  exact lt_irrefl 0 hzu'

/-- An injective holomorphic function on a connected surface is a
biholomorphism onto a plane domain. -/
theorem exists_diffeomorph_opens_complex_of_injective [ConnectedSpace M]
    {f : M → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hinj : Function.Injective f) :
    ∃ U : Opens ℂ, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  classical
  -- `M` has at least two points: pull two points of a chart target back to `M`.
  obtain ⟨p⟩ : Nonempty M := inferInstance
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp (chartAt ℂ p).open_target (chartAt ℂ p p)
    ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have hcmem : chartAt ℂ p p + ((r₀ / 2 : ℝ) : ℂ) ∈ (chartAt ℂ p).target := by
    apply hball₀
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hpq : p ≠ (chartAt ℂ p).symm (chartAt ℂ p p + ((r₀ / 2 : ℝ) : ℂ)) := by
    intro heqp
    have h2 := congrArg (⇑(chartAt ℂ p)) heqp
    rw [(chartAt ℂ p).right_inv hcmem] at h2
    have h3 : ((r₀ / 2 : ℝ) : ℂ) = 0 := by
      have h4 : chartAt ℂ p p + ((r₀ / 2 : ℝ) : ℂ) = chartAt ℂ p p + 0 := by
        rw [add_zero]; exact h2.symm
      exact add_left_cancel h4
    rw [Complex.ofReal_eq_zero] at h3
    linarith
  -- An injective map on a space with two points is nonconstant, hence open.
  have hnc : ¬ ∃ c, ∀ x, f x = c := by
    rintro ⟨c, hc⟩
    exact hpq (hinj ((hc p).trans (hc _).symm))
  have hopen : IsOpenMap f := isOpenMap_of_contMDiff_of_not_const hf hnc
  -- The image domain and the two structure maps.
  let U : Opens ℂ := ⟨Set.range f, hopen.isOpen_range⟩
  -- Forward smoothness: the range restriction of `f`.
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : M => (⟨f x, Set.mem_range_self x⟩ : ↥U)) := by
    intro x
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (Subtype.val ∘ fun x : M => (⟨f x, Set.mem_range_self x⟩ : ↥U)) x := hf.contMDiffAt
    rw [contMDiffAt_iff_target]
    exact ⟨IsInducing.subtypeVal.continuousAt_iff.mpr hcomp.continuousAt,
      (contMDiffAt_iff_target.mp hcomp).2⟩
  -- Inverse smoothness: read the inverse in a chart around the preimage point,
  -- where it is the local inverse of the injective analytic chart reading of `f`.
  have hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥U => Function.invFun f (y : ℂ)) := by
    intro y₀
    obtain ⟨x₀, hfx₀⟩ : ∃ x, f x = (y₀ : ℂ) := y₀.2
    obtain ⟨φ, hx₀src, hmax⟩ : ∃ φ : OpenPartialHomeomorph M ℂ,
        x₀ ∈ φ.source ∧ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω M :=
      ⟨chartAt ℂ x₀, mem_chart_source ℂ x₀, IsManifold.chart_mem_maximalAtlas x₀⟩
    have hw₀tgt : φ x₀ ∈ φ.target := φ.map_source hx₀src
    -- The chart reading of `f` is analytic and injective on the chart target.
    have hgan : ∀ w ∈ φ.target, AnalyticAt ℂ (f ∘ ⇑φ.symm) w := by
      intro w hw
      have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑φ.symm) w :=
        contMDiffAt_symm_of_mem_maximalAtlas hmax hw
      have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f ∘ ⇑φ.symm) w :=
        ContMDiffAt.comp w hf.contMDiffAt h1
      exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
    have hginj : Set.InjOn (f ∘ ⇑φ.symm) φ.target := by
      intro w₁ h₁ w₂ h₂ hgw
      have h3 : φ.symm w₁ = φ.symm w₂ := hinj hgw
      have h4 := congrArg (⇑φ) h3
      rwa [φ.right_inv h₁, φ.right_inv h₂] at h4
    obtain ⟨r, hr, hBsub⟩ := Metric.isOpen_iff.mp φ.open_target (φ x₀) hw₀tgt
    -- The inverse chart reading.
    let η : ℂ → ℂ := fun ζ => φ (Function.invFun f ζ)
    have hηg : ∀ w ∈ ball (φ x₀) r, η (f (φ.symm w)) = w := by
      intro w hwB
      have h5 : Function.invFun f (f (φ.symm w)) = φ.symm w :=
        Function.leftInverse_invFun hinj (φ.symm w)
      change φ (Function.invFun f (f (φ.symm w))) = w
      rw [h5]
      exact φ.right_inv (hBsub hwB)
    -- The image `W` of the coordinate ball, an open neighborhood of `y₀`.
    have hWopen : IsOpen (f '' (⇑φ.symm '' ball (φ x₀) r)) :=
      hopen _ (φ.isOpen_image_symm_of_subset_target isOpen_ball hBsub)
    have hy₀W : (y₀ : ℂ) ∈ f '' (⇑φ.symm '' ball (φ x₀) r) :=
      ⟨x₀, ⟨φ x₀, mem_ball_self hr, φ.left_inv hx₀src⟩, hfx₀⟩
    have himg : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r),
        ∃ w ∈ ball (φ x₀) r, f (φ.symm w) = ζ := by
      rintro ζ ⟨x, ⟨w, hwB, rfl⟩, rfl⟩
      exact ⟨w, hwB, rfl⟩
    have hgη : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), f (φ.symm (η ζ)) = ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
    have hηB : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), η ζ ∈ ball (φ x₀) r := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      rw [hηg w hwB]
      exact hwB
    -- Continuity of the inverse reading, from openness of `f`.
    have hηc : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), ContinuousAt η ζ := by
      intro ζ hζ
      obtain ⟨w, hwB, rfl⟩ := himg ζ hζ
      have hgoal : Filter.Tendsto η (𝓝 (f (φ.symm w))) (𝓝 w) := by
        rw [Filter.tendsto_def]
        intro N hN
        obtain ⟨N', hN'sub, hN'open, hwN'⟩ :=
          _root_.mem_nhds_iff.mp (Filter.inter_mem hN (isOpen_ball.mem_nhds hwB))
        have hsub' : N' ⊆ φ.target := fun z hz => hBsub (hN'sub hz).2
        have hopenimg : IsOpen (f '' (⇑φ.symm '' N')) :=
          hopen _ (φ.isOpen_image_symm_of_subset_target hN'open hsub')
        have hgmem : f (φ.symm w) ∈ f '' (⇑φ.symm '' N') := ⟨φ.symm w, ⟨w, hwN', rfl⟩, rfl⟩
        refine Filter.mem_of_superset (hopenimg.mem_nhds hgmem) ?_
        rintro ζ' ⟨x', ⟨w', hw'N', rfl⟩, rfl⟩
        rw [Set.mem_preimage, hηg w' (hN'sub hw'N').2]
        exact (hN'sub hw'N').1
      have hηw : η (f (φ.symm w)) = w := hηg w hwB
      change Filter.Tendsto η (𝓝 (f (φ.symm w))) (𝓝 (η (f (φ.symm w))))
      rw [hηw]
      exact hgoal
    -- Differentiability of the inverse reading at noncritical values.
    have hd_nc : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r),
        deriv (f ∘ ⇑φ.symm) (η ζ) ≠ 0 → DifferentiableAt ℂ η ζ := by
      intro ζ hζ hder
      have hfd : HasDerivAt (f ∘ ⇑φ.symm) (deriv (f ∘ ⇑φ.symm) (η ζ)) (η ζ) :=
        ((hgan (η ζ) (hBsub (hηB ζ hζ))).differentiableAt).hasDerivAt
      have hev : ∀ᶠ ζ' in 𝓝 ζ, (f ∘ ⇑φ.symm) (η ζ') = ζ' := by
        filter_upwards [hWopen.mem_nhds hζ] with ζ' hζ' using hgη ζ' hζ'
      exact (HasDerivAt.of_local_left_inverse (hηc ζ hζ) hfd hder hev).differentiableAt
    -- Critical points of the chart reading are isolated (injectivity).
    have hganN : AnalyticOnNhd ℂ (f ∘ ⇑φ.symm) φ.target := fun w hw => hgan w hw
    have hcrit : ∀ w ∈ φ.target, ∀ᶠ w' in 𝓝[≠] w, deriv (f ∘ ⇑φ.symm) w' ≠ 0 := by
      intro w hw
      rcases (hganN.deriv w hw).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · exfalso
        obtain ⟨ρ, hρ0, hballρ⟩ :=
          Metric.eventually_nhds_iff_ball.mp (h0.and (φ.open_target.eventually_mem hw))
        have hconst : ∀ w' ∈ ball w ρ, (f ∘ ⇑φ.symm) w' = (f ∘ ⇑φ.symm) w := by
          intro w' hw'
          refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball w ρ)
            (fun q hq => ((hgan q (hballρ q hq).2).differentiableAt).differentiableWithinAt)
            ?_ hw' (mem_ball_self hρ0)
          intro q hq
          rw [fderivWithin_of_isOpen isOpen_ball hq]
          refine ContinuousLinearMap.ext_ring ?_
          rw [fderiv_apply_one_eq_deriv, (hballρ q hq).1]
          simp
        have hmem : w + ((ρ / 2 : ℝ) : ℂ) ∈ ball w ρ := by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith
        have heq2 : w + ((ρ / 2 : ℝ) : ℂ) = w :=
          hginj (hballρ _ hmem).2 hw (hconst _ hmem)
        have hρ2 : ((ρ / 2 : ℝ) : ℂ) = 0 := by
          have h4 : w + ((ρ / 2 : ℝ) : ℂ) = w + 0 := by rw [add_zero]; exact heq2
          exact add_left_cancel h4
        rw [Complex.ofReal_eq_zero] at hρ2
        linarith
      · exact hne
    -- Differentiability everywhere on `W` (removable singularity at critical values).
    have hdiff : ∀ ζ ∈ f '' (⇑φ.symm '' ball (φ x₀) r), DifferentiableAt ℂ η ζ := by
      intro ζ hζ
      by_cases hder : deriv (f ∘ ⇑φ.symm) (η ζ) = 0
      swap
      · exact hd_nc ζ hζ hder
      obtain ⟨ρ, hρ0, hballρ⟩ := Metric.eventually_nhds_iff_ball.mp
        ((eventually_nhdsWithin_iff.mp (hcrit (η ζ) (hBsub (hηB ζ hζ)))).and
          (isOpen_ball.eventually_mem (hηB ζ hζ)))
      have hsub' : ball (η ζ) ρ ⊆ φ.target := fun z hz => hBsub (hballρ z hz).2
      have hW'open : IsOpen (f '' (⇑φ.symm '' ball (η ζ) ρ)) :=
        hopen _ (φ.isOpen_image_symm_of_subset_target isOpen_ball hsub')
      have hζW' : ζ ∈ f '' (⇑φ.symm '' ball (η ζ) ρ) :=
        ⟨φ.symm (η ζ), ⟨η ζ, mem_ball_self hρ0, rfl⟩, hgη ζ hζ⟩
      have hW'W : f '' (⇑φ.symm '' ball (η ζ) ρ) ⊆ f '' (⇑φ.symm '' ball (φ x₀) r) := by
        rintro ζ' ⟨x', ⟨w', hw', rfl⟩, rfl⟩
        exact ⟨φ.symm w', ⟨w', (hballρ w' hw').2, rfl⟩, rfl⟩
      have hoff : DifferentiableOn ℂ η (f '' (⇑φ.symm '' ball (η ζ) ρ) \ {ζ}) := by
        rintro ζ' ⟨hζ'W', hζ'ne⟩
        obtain ⟨x', ⟨w', hw'ball, rfl⟩, rfl⟩ := hζ'W'
        refine (hd_nc _ (hW'W ⟨φ.symm w', ⟨w', hw'ball, rfl⟩, rfl⟩) ?_).differentiableWithinAt
        rw [hηg w' (hballρ w' hw'ball).2]
        refine (hballρ w' hw'ball).1 ?_
        intro hmem
        apply hζ'ne
        rw [Set.mem_singleton_iff] at hmem ⊢
        rw [hmem]
        exact hgη ζ hζ
      have hW'diff : DifferentiableOn ℂ η (f '' (⇑φ.symm '' ball (η ζ) ρ)) :=
        (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
          (hW'open.mem_nhds hζW')).mp ⟨hoff, hηc ζ hζ⟩
      exact hW'diff.differentiableAt (hW'open.mem_nhds hζW')
    -- The inverse reading is analytic at the base point; assemble the smooth composite.
    have hWdiff : DifferentiableOn ℂ η (f '' (⇑φ.symm '' ball (φ x₀) r)) :=
      fun ζ hζ => (hdiff ζ hζ).differentiableWithinAt
    have hηan : AnalyticAt ℂ η (y₀ : ℂ) := (hWdiff.analyticOnNhd hWopen) _ hy₀W
    have hval : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (Subtype.val : ↥U → ℂ) y₀ :=
      contMDiff_subtype_val.contMDiffAt
    have hηsm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω η ((y₀ : ℂ)) :=
      contMDiffAt_iff_contDiffAt.mpr hηan.contDiffAt
    have hφsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (⇑φ.symm) (η (y₀ : ℂ)) :=
      contMDiffAt_symm_of_mem_maximalAtlas hmax (hBsub (hηB _ hy₀W))
    have hcomp2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((⇑φ.symm ∘ η) ∘ (Subtype.val : ↥U → ℂ)) y₀ :=
      ContMDiffAt.comp y₀ (ContMDiffAt.comp ((y₀ : ℂ)) hφsymm hηsm) hval
    refine hcomp2.congr_of_eventuallyEq ?_
    have hmemW : (Subtype.val : ↥U → ℂ) ⁻¹' (f '' (⇑φ.symm '' ball (φ x₀) r)) ∈ 𝓝 y₀ :=
      (hWopen.preimage continuous_subtype_val).mem_nhds hy₀W
    filter_upwards [hmemW] with y hy
    obtain ⟨x, ⟨w, hwB, rfl⟩, hfy⟩ := hy
    change Function.invFun f (y : ℂ) = φ.symm (η (y : ℂ))
    have h6 : η (y : ℂ) = w := by
      rw [← hfy]
      exact hηg w hwB
    rw [h6, ← hfy, Function.leftInverse_invFun hinj (φ.symm w)]
  exact ⟨U, ⟨{
    toFun := fun x => ⟨f x, Set.mem_range_self x⟩
    invFun := fun y => Function.invFun f (y : ℂ)
    left_inv := fun x => Function.leftInverse_invFun hinj x
    right_inv := fun y => Subtype.ext (Function.invFun_eq y.2)
    contMDiff_toFun := hF
    contMDiff_invFun := hG }⟩⟩

/-- **The hyperbolic case of planarity**: a simply connected surface carrying
a Green's function embeds onto a domain of the Riemann sphere. -/
theorem exists_diffeomorph_opens_of_hasGreenFunction [T2Space M] [SimplyConnectedSpace M]
    [NoncompactSpace M] {p₀ : M} (hG : HasGreenFunction p₀) :
    ∃ U : Opens ℂ̂, Nonempty (M ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥U) := by
  haveI : ConnectedSpace M := PathConnectedSpace.connectedSpace
  obtain ⟨φ, hφ, h0, habs⟩ := exists_green_map hG
  have hinj : Function.Injective φ := injective_green_map hG hφ h0 habs
  obtain ⟨U, ⟨e⟩⟩ := exists_diffeomorph_opens_complex_of_injective hφ hinj
  let V : Opens ℂ̂ :=
    ⟨((↑) : ℂ → ℂ̂) '' (U : Set ℂ),
      OnePoint.isOpenEmbedding_coe.isOpenMap _ U.isOpen⟩
  have hinfty : OnePoint.infty ∉ (V : Set ℂ̂) := by
    rintro ⟨w, -, hw⟩
    exact OnePoint.coe_ne_infty w hw
  obtain ⟨W, hWimg, ⟨e₂⟩⟩ := exists_diffeomorph_opens_planar V hinfty
  have hWU : W = U := by
    apply Opens.ext
    have himg : ((↑) : ℂ → ℂ̂) '' (W : Set ℂ) = ((↑) : ℂ → ℂ̂) '' (U : Set ℂ) :=
      hWimg
    exact Set.image_injective.mpr OnePoint.coe_injective himg
  subst hWU
  exact ⟨V, ⟨e.trans e₂.symm⟩⟩

end RiemannDynamics
