/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.FatouComponents.Periodic
import RiemannDynamics.Dynamics.JuliaFatou.RepellingDensity
import RiemannDynamics.Analysis.Winding.GridPrimitives
import RMT4.Main
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Eventual injectivity on a wandering component (interface)

The normalization wall of the No Wandering Domains theorem: a wandering Fatou
component may be relabeled along its forward orbit so that, from some time
on, every iterate is injective on the component and the orbit components
avoid `∞` and the critical points of the map.

The two soft normalizations are finiteness pigeonholing: the orbit
components are pairwise disjoint, `∞` lies in at most one of them, and the
finitely many critical points of a rational map meet only finitely many of
them. The injectivity clause is the hard dichotomy: each component step
`f : Uₙ → Uₙ₊₁` is proper and critical-point-free, hence a covering of
constant fiber count `≥ 1` (`exists_fiberCount`); a step of fiber count one
over its target is injective, and cofinally many steps of fiber count at
least two are impossible (`not_cofinal_multiple_steps`) by Baker's
simple-connectivity argument: a multiple step forces a multiply connected
target (`not_isConnected_compl_of_multiple_step`, via the Riemann-mapping
bridge `simplyConnectedSpace_of_unbounded_components` and
degree-one-over-simply-connected `fiberCount_eq_one_of_simplyConnected`),
hence an essential loop about a Julia point
(`exists_essential_loop_of_multiple_step`). Either the forward readings of
that loop enclose Julia points at arbitrarily late times — impossible
because normality collapses the forward traces and the open-mapping
frontier dichotomy confines the enclosed component of a late Julia witness
(`false_of_fill_meets_julia_cofinally`) — or from some time on the fill of
the forward reading avoids the Julia set, and then the reading is
null-homotopic in a simply connected neighborhood of its fill inside its
Fatou component (`exists_simplyConnectedSpace_between`); the null homotopy
descends through the covering steps (`isChartNullHomotopyIn_of_step`) and
homotopy invariance kills the essential winding
(`windingNumber_eq_zero_of_fill_avoids_julia`).

The file also hosts the small shared lemma that the frontier of a Fatou
component lies in the Julia set, consumed by several parts of the endgame.
-/

open Function OnePoint Filter Topology

namespace RiemannDynamics

/-- The frontier of a Fatou component is contained in the Julia set: the
Fatou set is open, so a frontier point of the component that were in the
Fatou set would lie in the interior of some component meeting `U`, hence in
`U` itself — contradicting that an open set is disjoint from its own
frontier. -/
theorem IsFatouComponent.frontier_subset_juliaSet {f : ℂ̂ → ℂ̂} {U : Set ℂ̂}
    (hU : IsFatouComponent f U) :
    frontier U ⊆ JuliaSet f := by
  intro x hx
  rw [hU.isOpen.frontier_eq] at hx
  obtain ⟨hxcl, hxU⟩ := hx
  by_contra hxJ
  have hxF : x ∈ FatouSet f := by
    by_contra h
    exact hxJ h
  set W := connectedComponentIn (FatouSet f) x with hW
  have hWfc : IsFatouComponent f W := isFatouComponent_connectedComponentIn hxF
  have hxW : x ∈ W := mem_connectedComponentIn hxF
  obtain ⟨y, hyW, hyU⟩ := mem_closure_iff.mp hxcl W hWfc.isOpen hxW
  have hWU : W = U := hWfc.eq_of_mem hU hyW hyU
  exact hxU (hWU ▸ hxW)

/-- **Avoidance pigeonhole.** Along a wandering orbit the components are
pairwise disjoint, so `∞` (one point) and the critical points of `f`
(finitely many, as zeros of the wronskian reading together with the finitely
many `∞`-chart criticalities) meet only finitely many orbit components: from
some index on, every orbit component avoids `∞` and contains no critical
point of `f`. -/
theorem exists_avoidance_index {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (_hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ N : ℕ, ∀ n : ℕ,
      ∞ ∉ fcOrbit f U (N + n) ∧
      ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U (N + n)) →
        deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0 := by
  classical
  obtain ⟨r, hr⟩ := hf
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  -- The bad set on the sphere: `∞` together with the (finitely many) zeros of
  -- the wronskian and of the reduced denominator, read into `ℂ̂`.
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  obtain ⟨B, hBdef⟩ : ∃ s : Set ℂ̂,
      s = (fun x : ℂ => ((x : ℂ̂))) ''
          ({x : ℂ | r.wronskian.IsRoot x} ∪ {x : ℂ | r.denReduced.IsRoot x})
        ∪ {∞} := ⟨_, rfl⟩
  have hBfin : B.Finite := by
    rw [hBdef]
    exact (((Polynomial.finite_setOf_isRoot hWr).union
      (Polynomial.finite_setOf_isRoot hdenR)).image _).union (Set.finite_singleton _)
  -- Indices whose orbit component meets the bad set; a choice of witness.
  obtain ⟨S, hSdef⟩ : ∃ s : Set ℕ,
      s = {m : ℕ | (fcOrbit f U m ∩ B).Nonempty} := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ̂, g = fun m =>
      if h : (fcOrbit f U m ∩ B).Nonempty then h.choose else ∞ := ⟨_, rfl⟩
  have hgmem : ∀ m ∈ S, g m ∈ fcOrbit f U m ∩ B := by
    intro m hm
    have hm' : (fcOrbit f U m ∩ B).Nonempty := by rw [hSdef] at hm; exact hm
    rw [hgdef]
    change (if h : (fcOrbit f U m ∩ B).Nonempty then h.choose else ∞)
        ∈ fcOrbit f U m ∩ B
    rw [dif_pos hm']
    exact hm'.choose_spec
  -- Pairwise disjointness of the orbit makes the witness injective on `S`.
  have hinj : Set.InjOn g S := by
    intro m hm m' hm' heq
    by_contra hne
    have hdisj : Disjoint (fcOrbit f U m) (fcOrbit f U m') := hW hne
    exact Set.disjoint_left.mp hdisj (hgmem m hm).1 (heq ▸ (hgmem m' hm').1)
  have hSfin : S.Finite :=
    Set.Finite.of_finite_image
      (hBfin.subset (by rintro _ ⟨m, hm, rfl⟩; exact (hgmem m hm).2)) hinj
  obtain ⟨N₀, hN₀⟩ := hSfin.bddAbove
  refine ⟨N₀ + 1, fun n => ?_⟩
  have hnotS : N₀ + 1 + n ∉ S := by
    intro hmem
    have := hN₀ hmem
    omega
  have hempty : ∀ b : ℂ̂, b ∈ fcOrbit f U (N₀ + 1 + n) → b ∉ B := by
    intro b hb hbB
    exact hnotS (by rw [hSdef]; exact ⟨b, hb, hbB⟩)
  constructor
  · intro hinf
    exact hempty ∞ hinf (by rw [hBdef]; exact Set.mem_union_right _ rfl)
  · intro z hz
    have hzB : ((z : ℂ̂)) ∉ B := hempty _ hz
    have hWz : r.wronskian.eval z ≠ 0 := fun h0 =>
      hzB (by rw [hBdef]; exact Set.mem_union_left _ ⟨z, Or.inl h0, rfl⟩)
    have hdz : r.denReduced.eval z ≠ 0 := fun h0 =>
      hzB (by rw [hBdef]; exact Set.mem_union_left _ ⟨z, Or.inr h0, rfl⟩)
    rw [hr, r.deriv_reading hdz]
    exact div_ne_zero hWz (pow_ne_zero 2 hdz)

/-- **Component maps are surjective**: a rational map of degree at least one
sends each orbit component onto the next. The image is open (rational maps
are open) and relatively closed in the connected target component (a
boundary point of the image inside the target would be the image of a
boundary point of the source, but frontiers of Fatou components map into the
Julia set), hence clopen and nonempty. -/
theorem fcOrbit_image_eq {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ) :
    f '' fcOrbit f U n = fcOrbit f U (n + 1) := by
  have hnc := hf.ne_const hd
  have hfo : IsOpenMap f := hf.isOpenMap hnc
  have hc : Continuous f := hf.continuous
  obtain ⟨z₀, hz₀⟩ := hU.nonempty
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd hU
  have hSeq : S = connectedComponentIn (FatouSet f) (f^[n] z₀) :=
    fcOrbit_eq_connectedComponentIn n hf hd hU hz₀
  have hTeq : T = connectedComponentIn (FatouSet f) (f^[n + 1] z₀) :=
    fcOrbit_eq_connectedComponentIn (n + 1) hf hd hU hz₀
  have hiter : ∀ k : ℕ, f^[k] z₀ ∈ FatouSet f := by
    intro k
    induction k with
    | zero => simpa using hU.subset_fatouSet hz₀
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact apply_mem_fatouSet hfo ih
  have hbaseS : f^[n] z₀ ∈ S := by
    rw [hSeq]; exact mem_connectedComponentIn (hiter n)
  have hbaseT : f^[n + 1] z₀ ∈ T := by
    rw [hTeq]; exact mem_connectedComponentIn (hiter (n + 1))
  have himgBase : f^[n + 1] z₀ ∈ f '' S := by
    rw [Function.iterate_succ_apply']
    exact ⟨f^[n] z₀, hbaseS, rfl⟩
  -- the image lies inside the target component
  have hsub : f '' S ⊆ T := by
    have hpre : IsPreconnected (f '' S) :=
      (hSfc.isConnected.isPreconnected).image f hc.continuousOn
    have hFat : f '' S ⊆ FatouSet f := by
      rintro _ ⟨x, hx, rfl⟩
      exact apply_mem_fatouSet hfo (hSfc.subset_fatouSet hx)
    rw [hTeq]
    exact hpre.subset_connectedComponentIn himgBase hFat
  -- the image is open
  have hopen : IsOpen (f '' S) := hfo _ hSfc.isOpen
  -- the image is relatively closed in the target component
  have hclosed : T ∩ closure (f '' S) ⊆ f '' S := by
    have hclosSub : closure (f '' S) ⊆ f '' closure S := by
      have hcpt : IsCompact (closure S) := isClosed_closure.isCompact
      exact closure_minimal (Set.image_mono subset_closure)
        (hcpt.image hc).isClosed
    rintro w ⟨hwT, hwc⟩
    obtain ⟨x, hx, rfl⟩ := hclosSub hwc
    rw [closure_eq_interior_union_frontier, hSfc.isOpen.interior_eq] at hx
    rcases hx with hxS | hxfr
    · exact ⟨x, hxS, rfl⟩
    · exfalso
      have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
      have hfxJ : f x ∈ JuliaSet f := by
        rw [← juliaSet_preimage_eq_of_isRational hf hd] at hxJ
        exact hxJ
      exact hfxJ (hTfc.subset_fatouSet hwT)
  -- nonempty clopen subset of the connected target component
  have hTsub : T ⊆ f '' S := by
    intro w hw
    by_cases hwc : w ∈ closure (f '' S)
    · exact hclosed ⟨hw, hwc⟩
    · exfalso
      have hcover : T ⊆ f '' S ∪ (closure (f '' S))ᶜ := by
        intro y hy
        by_cases h : y ∈ closure (f '' S)
        · exact Or.inl (hclosed ⟨hy, h⟩)
        · exact Or.inr h
      obtain ⟨x, _, hxu, hxv⟩ :=
        hTfc.isConnected.isPreconnected (f '' S) (closure (f '' S))ᶜ hopen
          isClosed_closure.isOpen_compl hcover ⟨f^[n + 1] z₀, hbaseT, himgBase⟩
          ⟨w, hw, hwc⟩
      exact hxv (subset_closure hxu)
  exact Set.Subset.antisymm hsub hTsub

/-- **Properness of the component restriction, fiber form**: the fiber of
the component map over an interior point of the target component is compact
— it is the intersection of the compact global fiber with the source
component, and no boundary point of the source can map into the (Fatou)
target since frontiers map into the Julia set. -/
theorem isCompact_fiber_inter {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    {w : ℂ̂} (hw : w ∈ fcOrbit f U (n + 1)) :
    IsCompact (f ⁻¹' {w} ∩ fcOrbit f U n) := by
  set S := fcOrbit f U n with hS
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd hU
  have hwF : w ∈ FatouSet f :=
    (isFatouComponent_fcOrbit (n + 1) hf hd hU).subset_fatouSet hw
  have hkey : f ⁻¹' {w} ∩ S = f ⁻¹' {w} ∩ closure S := by
    apply Set.Subset.antisymm
    · exact Set.inter_subset_inter_right _ subset_closure
    · rintro x ⟨hxf, hxcl⟩
      refine ⟨hxf, ?_⟩
      by_contra hxS
      have hxfr : x ∈ frontier S := by
        rw [hSfc.isOpen.frontier_eq]
        exact ⟨hxcl, hxS⟩
      have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
      rw [← juliaSet_preimage_eq_of_isRational hf hd] at hxJ
      have hfw : f x = w := hxf
      rw [Set.mem_preimage, hfw] at hxJ
      exact hxJ hwF
  rw [hkey]
  exact ((IsClosed.preimage hf.continuous isClosed_singleton).inter
    isClosed_closure).isCompact

/-- **Constant fiber count**: when the source component contains neither `∞`
nor critical points, the component map is a proper local homeomorphism onto
the connected target, so its fiber cardinality is finite, positive, and the
same over every target point (stack of records: finitely many disjoint local
sheets plus the properness exclusion of stray preimages). -/
theorem exists_fiberCount {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd1 hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have himg : f '' S = T := fcOrbit_image_eq hf hd1 hU n
  have cf : ∀ t : ℂ, chartFiniteMap ((t : ℂ̂)) = t := fun _ => rfl
  have hread : ∀ t : ℂ, r.toSphereMap ((t : ℂ̂))
      = if r.denReduced.eval t = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval t / r.denReduced.eval t : ℂ) : ℂ̂) := fun _ => rfl
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  -- Stage 0: on `S` the reduced denominator does not vanish (a pole would make
  -- the finite-chart reading discontinuous, hence with zero `deriv`).
  have hden_ne : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → r.denReduced.eval x ≠ 0 := by
    intro x hxS h0
    have hcx := hcrit x hxS
    have hdiff : DifferentiableAt ℂ (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) x := by
      by_contra hnd
      exact hcx (deriv_zero_of_not_differentiableAt hnd)
    have hφx : chartFiniteMap (f ((x : ℂ̂))) = 0 := by
      rw [hr, hread x, if_pos h0]
      rfl
    -- eventually on the punctured neighbourhood the denominator is nonzero
    have hZfin : {t : ℂ | r.denReduced.IsRoot t}.Finite :=
      Polynomial.finite_setOf_isRoot hdenR
    have hclosed : IsClosed ({t : ℂ | r.denReduced.IsRoot t} \ {x}) :=
      (hZfin.subset Set.diff_subset).isClosed
    have hxmem : x ∈ ({t : ℂ | r.denReduced.IsRoot t} \ {x})ᶜ := fun h => h.2 rfl
    have hev_ne : ∀ᶠ t in 𝓝[≠] x, r.denReduced.eval t ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hxmem),
        self_mem_nhdsWithin] with t ht htx
      exact fun h0t => ht ⟨h0t, htx⟩
    -- two incompatible limits along the punctured neighbourhood
    have h1 : Tendsto (fun t : ℂ => f ((t : ℂ̂))) (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) := by
      have hc : ContinuousAt (fun t : ℂ => f ((t : ℂ̂))) x :=
        (hf.continuous.comp OnePoint.continuous_coe).continuousAt
      have hfx : f ((x : ℂ̂)) = ∞ := by rw [hr, hread x, if_pos h0]
      have h := hc.tendsto
      rw [hfx] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (((0 : ℂ) : ℂ̂))) := by
      have hφt := hdiff.continuousAt.tendsto
      rw [hφx] at hφt
      exact ((OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hφt).mono_left
        nhdsWithin_le_nhds
    have heq : (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        =ᶠ[𝓝[≠] x] fun t : ℂ => f ((t : ℂ̂)) := by
      filter_upwards [hev_ne] with t ht
      rw [hr, hread t, if_neg ht, cf]
    have h1' : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) h1
    exact OnePoint.coe_ne_infty (0 : ℂ) (tendsto_nhds_unique h2 h1')
  -- values on `S` are finite
  have hSfin : ∀ u ∈ S, f u ≠ ∞ := by
    intro u huS
    have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
    rw [hr, hread x, if_neg (hden_ne x huS)]
    exact OnePoint.coe_ne_infty _
  have hTfin : ∀ w ∈ T, ∃ y : ℂ, w = ((y : ℂ̂)) := by
    intro w hwT
    rw [← himg] at hwT
    obtain ⟨u, huS, rfl⟩ := hwT
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp (hSfin u huS)
    exact ⟨y, hy.symm⟩
  -- Stage 1: fibers over finite points are finite (they are root sets of the
  -- nonzero polynomial `num - y·den`; its vanishing would kill the Wronskian).
  have hfib_fin : ∀ y : ℂ, (f ⁻¹' {((y : ℂ̂))} ∩ S).Finite := by
    intro y
    have hq : r.numReduced - Polynomial.C y * r.denReduced ≠ 0 := by
      intro h0
      apply hWr
      have hnum : r.numReduced = Polynomial.C y * r.denReduced := sub_eq_zero.mp h0
      unfold RationalData.wronskian
      rw [hnum, Polynomial.derivative_C_mul]
      ring
    have hsub : f ⁻¹' {((y : ℂ̂))} ∩ S ⊆ (fun x : ℂ => ((x : ℂ̂))) ''
        {x : ℂ | (r.numReduced - Polynomial.C y * r.denReduced).IsRoot x} := by
      rintro u ⟨hufy, huS⟩
      have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
      obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
      have hden := hden_ne x huS
      have hfx : f ((x : ℂ̂)) = ((y : ℂ̂)) := hufy
      rw [hr, hread x, if_neg hden] at hfx
      have hdiv : r.numReduced.eval x / r.denReduced.eval x = y :=
        OnePoint.coe_eq_coe.mp hfx
      rw [div_eq_iff hden] at hdiv
      refine ⟨x, ?_, rfl⟩
      change (r.numReduced - Polynomial.C y * r.denReduced).eval x = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hdiv, sub_self]
    exact ((Polynomial.finite_setOf_isRoot hq).image _).subset hsub
  -- Local injectivity: near each finite non-critical point `f` is injective
  have hloc : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → ∃ Wc : Set ℂ, IsOpen Wc ∧ x ∈ Wc ∧
      ∀ t₁ ∈ Wc, ∀ t₂ ∈ Wc, f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) → t₁ = t₂ := by
    intro x hxS
    have hcx := hcrit x hxS
    have hden := hden_ne x hxS
    have hev : (fun t : ℂ => r.numReduced.eval t / r.denReduced.eval t)
        =ᶠ[𝓝 x] fun t : ℂ => chartFiniteMap (f ((t : ℂ̂))) := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with t ht
      rw [hr, hread t, if_neg ht, cf]
    obtain ⟨D, hstrict⟩ : ∃ D : ℂ,
        HasStrictDerivAt (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) D x :=
      ⟨_, ((r.numReduced.hasStrictDerivAt x).div
        (r.denReduced.hasStrictDerivAt x) hden).congr_of_eventuallyEq hev⟩
    have hD : D ≠ 0 := hstrict.hasDerivAt.deriv ▸ hcx
    obtain ⟨Wc, hWsub, hWopen, hxW⟩ :=
      mem_nhds_iff.mp (hstrict.eventually_left_inverse hD)
    refine ⟨Wc, hWopen, hxW, ?_⟩
    intro t₁ ht₁ t₂ ht₂ hft
    have h₁ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₁ : ℂ̂)))) = t₁ := hWsub ht₁
    have h₂ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₂ : ℂ̂)))) = t₂ := hWsub ht₂
    rw [← h₁, hft, h₂]
  -- `S` read in the finite chart is open
  have hScopen : IsOpen ((fun t : ℂ => ((t : ℂ̂))) ⁻¹' S) :=
    hSfc.isOpen.preimage OnePoint.continuous_coe
  -- Stage 2: the fiber count is locally constant on `T`
  have hlc : ∀ w₀ ∈ T, ∃ P : Set ℂ̂, P ∈ 𝓝 w₀ ∧ ∀ w ∈ P ∩ T,
      (f ⁻¹' {w} ∩ S).ncard = (f ⁻¹' {w₀} ∩ S).ncard := by
    intro w₀ hw₀T
    obtain ⟨a, rfl⟩ := hTfin w₀ hw₀T
    -- the fiber over the base point, read in the finite chart
    obtain ⟨Fc, hFcdef⟩ : ∃ s : Set ℂ,
        s = (fun t : ℂ => ((t : ℂ̂))) ⁻¹' (f ⁻¹' {((a : ℂ̂))} ∩ S) := ⟨_, rfl⟩
    have hFc_fin : Fc.Finite := by
      rw [hFcdef]
      exact (hfib_fin a).preimage OnePoint.coe_injective.injOn
    have hFC : f ⁻¹' {((a : ℂ̂))} ∩ S = (fun t : ℂ => ((t : ℂ̂))) '' Fc := by
      apply Set.Subset.antisymm
      · rintro u ⟨huf, huS⟩
        have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
        obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
        exact ⟨x, by rw [hFcdef]; exact ⟨huf, huS⟩, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [hFcdef] at hx
        exact hx
    have hFcS : ∀ x ∈ Fc, ((x : ℂ̂)) ∈ S := by
      intro x hx; rw [hFcdef] at hx; exact hx.2
    have hFcf : ∀ x ∈ Fc, f ((x : ℂ̂)) = ((a : ℂ̂)) := by
      intro x hx; rw [hFcdef] at hx; exact hx.1
    -- one local record per fiber point: a branch through it, staying in `S`,
    -- with a capture neighbourhood on which it collects all preimages
    have hrec : ∀ x : ℂ, ∃ (V : Set ℂ) (g : ℂ → ℂ) (O : Set ℂ̂), x ∈ Fc →
        (IsOpen V ∧ a ∈ V ∧ ContinuousOn g V ∧ g a = x ∧
          (∀ y ∈ V, f ((g y : ℂ̂)) = ((y : ℂ̂)) ∧ ((g y : ℂ̂)) ∈ S) ∧
          O ∈ 𝓝 ((x : ℂ̂)) ∧
          (∀ u ∈ O, ∀ y ∈ V, f u = ((y : ℂ̂)) → u = ((g y : ℂ̂)))) := by
      intro x
      by_cases hx : x ∈ Fc
      swap
      · exact ⟨∅, id, ∅, fun h => absurd h hx⟩
      have hxS : ((x : ℂ̂)) ∈ S := hFcS x hx
      obtain ⟨V₀, g, hV₀open, haV₀, hga, hgdiff, hbr⟩ :=
        exists_branch_of_deriv_ne_zero hf (hFcf x hx) (hcrit x hxS)
      obtain ⟨Wc, hWopen, hxW, hWinj⟩ := hloc x hxS
      refine ⟨V₀ ∩ g ⁻¹' (Wc ∩ (fun t : ℂ => ((t : ℂ̂))) ⁻¹' S), g,
        (fun t : ℂ => ((t : ℂ̂))) '' Wc, fun _ => ⟨?_, ⟨haV₀, ?_⟩,
          hgdiff.continuousOn.mono Set.inter_subset_left, hga, ?_, ?_, ?_⟩⟩
      · exact hgdiff.continuousOn.isOpen_inter_preimage hV₀open
          (hWopen.inter hScopen)
      · rw [Set.mem_preimage, hga]
        exact ⟨hxW, hxS⟩
      · intro y hy
        exact ⟨hbr y hy.1, hy.2.2⟩
      · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
          Set.preimage_image_eq _ OnePoint.coe_injective]
        exact hWopen.mem_nhds hxW
      · rintro _ ⟨t, htW, rfl⟩ y hyV hfu
        have hteq : f ((t : ℂ̂)) = f ((g y : ℂ̂)) := by
          rw [hfu, hbr y hyV.1]
        rw [hWinj t htW (g y) hyV.2.1 hteq]
    choose Vr gr Onb hrec using hrec
    have hVor : ∀ x ∈ Fc, IsOpen (Vr x) := fun x hx => (hrec x hx).1
    have haVr : ∀ x ∈ Fc, a ∈ Vr x := fun x hx => (hrec x hx).2.1
    have hgcr : ∀ x ∈ Fc, ContinuousOn (gr x) (Vr x) := fun x hx => (hrec x hx).2.2.1
    have hgar : ∀ x ∈ Fc, gr x a = x := fun x hx => (hrec x hx).2.2.2.1
    have hbrr : ∀ x ∈ Fc, ∀ y ∈ Vr x,
        f ((gr x y : ℂ̂)) = ((y : ℂ̂)) ∧ ((gr x y : ℂ̂)) ∈ S :=
      fun x hx => (hrec x hx).2.2.2.2.1
    have hOnr : ∀ x ∈ Fc, Onb x ∈ 𝓝 ((x : ℂ̂)) := fun x hx => (hrec x hx).2.2.2.2.2.1
    have hcapr : ∀ x ∈ Fc, ∀ u ∈ Onb x, ∀ y ∈ Vr x,
        f u = ((y : ℂ̂)) → u = ((gr x y : ℂ̂)) :=
      fun x hx => (hrec x hx).2.2.2.2.2.2
    -- stray exclusion: near `↑a` every preimage in `S` is captured by a record
    have hexcl : ∃ N ∈ 𝓝 ((a : ℂ̂)), ∀ u, f u ∈ N → u ∈ S → ∃ x ∈ Fc, u ∈ Onb x := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ℱ, hℱdef⟩ : ∃ F : Filter ℂ̂,
          F = Filter.comap f (𝓝 ((a : ℂ̂))) ⊓ 𝓟 (S \ ⋃ x ∈ Fc, Onb x) := ⟨_, rfl⟩
      have hneF : ℱ.NeBot := by
        rw [hℱdef, Filter.inf_principal_neBot_iff]
        intro Uf hUf
        obtain ⟨N, hN, hNsub⟩ := Filter.mem_comap.mp hUf
        obtain ⟨u, hfu, huS, hustray⟩ := hcon N hN
        refine ⟨u, hNsub hfu, huS, ?_⟩
        intro hmem
        obtain ⟨x, hx, hux⟩ := Set.mem_iUnion₂.mp hmem
        exact hustray x hx hux
      have hle : ℱ ≤ 𝓟 (closure S) := by
        rw [hℱdef]
        exact le_trans inf_le_right
          (Filter.principal_mono.mpr (Set.diff_subset.trans subset_closure))
      obtain ⟨u, hucl, hclust⟩ := isClosed_closure.isCompact.exists_clusterPt hle
      have hfu : f u = ((a : ℂ̂)) := by
        have ht : Tendsto f ℱ (𝓝 ((a : ℂ̂))) := by
          rw [hℱdef]
          exact Filter.tendsto_iff_comap.mpr inf_le_left
        exact eq_of_nhds_neBot (hclust.map hf.continuous.continuousAt ht)
      have huS : u ∈ S := by
        by_contra huS
        have hufr : u ∈ frontier S := by
          rw [hSfc.isOpen.frontier_eq]
          exact ⟨hucl, huS⟩
        have huJ : u ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hufr
        rw [← juliaSet_preimage_eq_of_isRational hf hd1] at huJ
        have huJ' : f u ∈ JuliaSet f := huJ
        rw [hfu] at huJ'
        exact huJ' (hTfc.subset_fatouSet hw₀T)
      have humem : u ∈ (fun t : ℂ => ((t : ℂ̂))) '' Fc := by
        rw [← hFC]
        exact ⟨hfu, huS⟩
      obtain ⟨x, hxFc, rfl⟩ := humem
      have hstray : (S \ ⋃ x ∈ Fc, Onb x) ∈ ℱ := by
        rw [hℱdef]
        exact Filter.mem_inf_of_right (Filter.mem_principal_self _)
      haveI : (𝓝 ((x : ℂ̂)) ⊓ ℱ).NeBot := hclust
      obtain ⟨v, hvO, hvS⟩ := Filter.nonempty_of_mem
        (Filter.inter_mem (Filter.mem_inf_of_left (hOnr x hxFc))
          (Filter.mem_inf_of_right hstray))
      exact hvS.2 (Set.mem_iUnion₂.mpr ⟨x, hxFc, hvO⟩)
    obtain ⟨N, hNnhds, hNcap⟩ := hexcl
    -- the final branch domain: common, with pairwise-distinct branch values,
    -- and mapping into the capture neighbourhood
    obtain ⟨Vfin, hVfindef⟩ : ∃ V : Set ℂ, V =
        ((⋂ x ∈ Fc, Vr x) ∩
          ⋂ x₁ ∈ Fc, ⋂ x₂ ∈ Fc, ite (x₁ = x₂) Set.univ
            ((Vr x₁ ∩ Vr x₂) ∩ (fun y => gr x₁ y - gr x₂ y) ⁻¹' {(0 : ℂ)}ᶜ)) ∩
          (fun t : ℂ => ((t : ℂ̂))) ⁻¹' interior N := ⟨_, rfl⟩
    have hVfin_open : IsOpen Vfin := by
      rw [hVfindef]
      refine (IsOpen.inter (hFc_fin.isOpen_biInter hVor) ?_).inter
        (isOpen_interior.preimage OnePoint.continuous_coe)
      refine hFc_fin.isOpen_biInter fun x₁ hx₁ => hFc_fin.isOpen_biInter fun x₂ hx₂ => ?_
      split_ifs with h12
      · exact isOpen_univ
      · exact ContinuousOn.isOpen_inter_preimage
          (((hgcr x₁ hx₁).mono Set.inter_subset_left).sub
            ((hgcr x₂ hx₂).mono Set.inter_subset_right))
          ((hVor x₁ hx₁).inter (hVor x₂ hx₂)) isOpen_compl_singleton
    have haVfin : a ∈ Vfin := by
      rw [hVfindef]
      refine ⟨⟨Set.mem_iInter₂.mpr haVr, ?_⟩, ?_⟩
      · refine Set.mem_iInter₂.mpr fun x₁ hx₁ => Set.mem_iInter₂.mpr fun x₂ hx₂ => ?_
        split_ifs with h12
        · trivial
        · refine ⟨⟨haVr x₁ hx₁, haVr x₂ hx₂⟩, ?_⟩
          change gr x₁ a - gr x₂ a ∉ ({(0 : ℂ)} : Set ℂ)
          rw [hgar x₁ hx₁, hgar x₂ hx₂]
          exact fun h0 => h12 (sub_eq_zero.mp h0)
      · exact mem_interior_iff_mem_nhds.mpr hNnhds
    refine ⟨(fun t : ℂ => ((t : ℂ̂))) '' Vfin, ?_, ?_⟩
    · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
        Set.preimage_image_eq _ OnePoint.coe_injective]
      exact hVfin_open.mem_nhds haVfin
    · rintro w ⟨⟨y, hyVfin, rfl⟩, hwT⟩
      rw [hVfindef] at hyVfin
      obtain ⟨⟨hyVall, hyD⟩, hyN⟩ := hyVfin
      have hyVx : ∀ x ∈ Fc, y ∈ Vr x := Set.mem_iInter₂.mp hyVall
      -- the fiber over `↑y` is exactly the set of branch values
      have himgfib : f ⁻¹' {((y : ℂ̂))} ∩ S = (fun x : ℂ => ((gr x y : ℂ̂))) '' Fc := by
        apply Set.Subset.antisymm
        · rintro u ⟨huf, huS⟩
          have hufeq : f u = ((y : ℂ̂)) := huf
          have huN : f u ∈ N := by
            rw [hufeq]
            exact interior_subset hyN
          obtain ⟨x, hxFc, hxO⟩ := hNcap u huN huS
          exact ⟨x, hxFc, (hcapr x hxFc u hxO y (hyVx x hxFc) hufeq).symm⟩
        · rintro _ ⟨x, hxFc, rfl⟩
          exact ⟨(hbrr x hxFc y (hyVx x hxFc)).1, (hbrr x hxFc y (hyVx x hxFc)).2⟩
      have hinj1 : Set.InjOn (fun x : ℂ => ((gr x y : ℂ̂))) Fc := by
        intro x₁ hx₁ x₂ hx₂ heq
        by_contra h12
        have hy12 := Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hyD x₁ hx₁) x₂ hx₂
        rw [if_neg h12] at hy12
        have hgne : gr x₁ y - gr x₂ y ∉ ({(0 : ℂ)} : Set ℂ) := hy12.2
        exact hgne (sub_eq_zero_of_eq (OnePoint.coe_eq_coe.mp heq))
      rw [himgfib, hFC, hinj1.ncard_image, (OnePoint.coe_injective.injOn).ncard_image]
  -- Stage 3: local constancy on the connected `T` gives a global count
  obtain ⟨w₀, hw₀T⟩ := hTfc.nonempty
  refine ⟨(f ⁻¹' {w₀} ∩ S).ncard, ?_, ?_⟩
  · obtain ⟨y₀, rfl⟩ := hTfin w₀ hw₀T
    have hne : (f ⁻¹' {((y₀ : ℂ̂))} ∩ S).Nonempty := by
      rw [← himg] at hw₀T
      obtain ⟨u, huS, huf⟩ := hw₀T
      exact ⟨u, huf, huS⟩
    exact (Set.ncard_pos (hfib_fin y₀)).mpr hne
  · by_contra hbad
    push Not at hbad
    obtain ⟨w₁, hw₁T, hw₁ne⟩ := hbad
    have hpatch : ∀ w : ℂ̂, ∃ P : Set ℂ̂, w ∈ T → (P ∈ 𝓝 w ∧ ∀ w' ∈ P ∩ T,
        (f ⁻¹' {w'} ∩ S).ncard = (f ⁻¹' {w} ∩ S).ncard) := by
      intro w
      by_cases hw : w ∈ T
      · obtain ⟨P, h1, h2⟩ := hlc w hw
        exact ⟨P, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨∅, fun h => absurd h hw⟩
    choose P hP using hpatch
    have hcover : T ⊆ (⋃ w ∈ {w ∈ T | (f ⁻¹' {w} ∩ S).ncard
          = (f ⁻¹' {w₀} ∩ S).ncard}, interior (P w)) ∪
        ⋃ w ∈ {w ∈ T | (f ⁻¹' {w} ∩ S).ncard ≠ (f ⁻¹' {w₀} ∩ S).ncard},
          interior (P w) := by
      intro w hw
      have hmem : w ∈ interior (P w) := mem_interior_iff_mem_nhds.mpr (hP w hw).1
      by_cases hval : (f ⁻¹' {w} ∩ S).ncard = (f ⁻¹' {w₀} ∩ S).ncard
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hval⟩, hmem⟩)
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨w, ⟨hw, hval⟩, hmem⟩)
    obtain ⟨z, hzT, hzA, hzB⟩ := hTfc.isConnected.isPreconnected _ _
      (isOpen_biUnion fun _ _ => isOpen_interior)
      (isOpen_biUnion fun _ _ => isOpen_interior) hcover
      ⟨w₀, hw₀T, Set.mem_iUnion₂.mpr ⟨w₀, ⟨hw₀T, rfl⟩,
        mem_interior_iff_mem_nhds.mpr (hP w₀ hw₀T).1⟩⟩
      ⟨w₁, hw₁T, Set.mem_iUnion₂.mpr ⟨w₁, ⟨hw₁T, hw₁ne⟩,
        mem_interior_iff_mem_nhds.mpr (hP w₁ hw₁T).1⟩⟩
    obtain ⟨wa, hwa, hza⟩ := Set.mem_iUnion₂.mp hzA
    obtain ⟨wb, hwb, hzb⟩ := Set.mem_iUnion₂.mp hzB
    have h1 : (f ⁻¹' {z} ∩ S).ncard = (f ⁻¹' {wa} ∩ S).ncard :=
      (hP wa hwa.1).2 z ⟨interior_subset hza, hzT⟩
    have h2 : (f ⁻¹' {z} ∩ S).ncard = (f ⁻¹' {wb} ∩ S).ncard :=
      (hP wb hwb.1).2 z ⟨interior_subset hzb, hzT⟩
    exact hwb.2 (by rw [← h2, h1, hwa.2])

/-- A component step with constant fiber count one is injective on the
source component. -/
theorem injOn_of_fiberCount_one {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (h1 : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = 1) :
    Set.InjOn f (fcOrbit f U n) := by
  intro x hx y hy hxy
  have hwT : f x ∈ fcOrbit f U (n + 1) := by
    rw [← fcOrbit_image_eq hf hd hU n]
    exact ⟨x, hx, rfl⟩
  have hcard := h1 (f x) hwT
  rw [Set.ncard_eq_one] at hcard
  obtain ⟨a, ha⟩ := hcard
  have hxa : x ∈ f ⁻¹' {f x} ∩ fcOrbit f U n := ⟨rfl, hx⟩
  have hya : y ∈ f ⁻¹' {f x} ∩ fcOrbit f U n := ⟨by simp [hxy], hy⟩
  rw [ha, Set.mem_singleton_iff] at hxa hya
  rw [hxa, hya]

/-- **Injectivity telescopes**: if every single component step from index
`N` on is injective, then every iterate is injective on the `N`-th
component (finite induction along the orbit, using that iterates stay in
the orbit components). -/
theorem injOn_iterate_of_tail_injective {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (N : ℕ)
    (hstep : ∀ m : ℕ, N ≤ m → Set.InjOn f (fcOrbit f U m)) :
    ∀ n : ℕ, Set.InjOn (f^[n]) (fcOrbit f U N) := by
  have hV : IsFatouComponent f (fcOrbit f U N) := isFatouComponent_fcOrbit N hf hd hU
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd)
  have hfwd : ∀ k : ℕ, ∀ w : ℂ̂, w ∈ FatouSet f → f^[k] w ∈ FatouSet f := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hfo (ih w hw)
  have hmem : ∀ n : ℕ, ∀ x ∈ fcOrbit f U N, f^[n] x ∈ fcOrbit f U (N + n) := by
    intro n x hx
    rw [fcOrbit_add N n hf hd hU,
      fcOrbit_eq_connectedComponentIn n hf hd hV hx]
    exact mem_connectedComponentIn (hfwd n x (hV.subset_fatouSet hx))
  intro n
  induction n with
  | zero =>
      intro x _ y _ hxy
      simpa using hxy
  | succ n ih =>
      intro x hx y hy hxy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hxy
      have hxn : f^[n] x ∈ fcOrbit f U (N + n) := hmem n x hx
      have hyn : f^[n] y ∈ fcOrbit f U (N + n) := hmem n y hy
      have hiter : f^[n] x = f^[n] y :=
        hstep (N + n) (Nat.le_add_right N n) hxn hyn hxy
      exact ih hx hy hiter

/-- **Simple connectivity from unbounded complementary components** (the
Riemann-mapping bridge). An open connected proper subset of the plane all of
whose complementary components are unbounded is simply connected: it has
primitives (`has_primitives_of_unbounded_components`), so the vendored
Riemann mapping theorem provides a holomorphic bijection onto the unit ball;
the open mapping theorem upgrades it to a homeomorphism; the ball is convex,
hence contractible, hence simply connected; and simple connectivity
transports along homotopy equivalences. -/
theorem simplyConnectedSpace_of_unbounded_components {T : Set ℂ}
    (hT : IsOpen T) (hconn : IsConnected T) (hne : T ≠ Set.univ)
    (hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z)) :
    SimplyConnectedSpace T := by
  -- Primitives exist on `T`, so the vendored Riemann mapping theorem applies.
  obtain ⟨f, hdf, hinj, himg⟩ :=
    RMT hT hconn hne (has_primitives_of_unbounded_components hT hcompl)
  -- `f` maps open subsets of `T` to open sets (open mapping theorem; the
  -- constant alternative contradicts injectivity on the nonempty open `T`).
  have hopen : ∀ s ⊆ T, IsOpen s → IsOpen (f '' s) := by
    rcases (hdf.analyticOnNhd hT).is_constant_or_isOpen hconn.isPreconnected with ⟨w, hw⟩ | h
    · exfalso
      obtain ⟨z₀, hz₀⟩ := hconn.nonempty
      have hmem : T ∩ {z₀}ᶜ ∈ 𝓝[≠] z₀ :=
        Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hT.mem_nhds hz₀))
          self_mem_nhdsWithin
      obtain ⟨y, hyT, hyz⟩ := Filter.nonempty_of_mem hmem
      exact Set.mem_compl_singleton_iff.mp hyz
        (hinj hyT hz₀ ((hw _ hyT).trans (hw _ hz₀).symm))
    · exact h
  -- Package `f` as a map between the subtypes `↥T` and `↥(ball 0 1)`.
  have hmemB : ∀ x : T, f x ∈ Metric.ball (0 : ℂ) 1 := fun x => by
    rw [← himg]; exact Set.mem_image_of_mem f x.2
  let F : T → Metric.ball (0 : ℂ) 1 := fun x => ⟨f x, hmemB x⟩
  have hFinj : Function.Injective F := fun x y hxy =>
    Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
  have hFsurj : Function.Surjective F := by
    rintro ⟨w, hw⟩
    rw [← himg] at hw
    obtain ⟨x, hxT, hfx⟩ := hw
    exact ⟨⟨x, hxT⟩, Subtype.ext hfx⟩
  have hFcont : Continuous F := hdf.continuousOn.restrict.subtype_mk hmemB
  have hFopen : IsOpenMap F := by
    intro V hV
    have hval : IsOpen (Subtype.val '' V) := hT.isOpenMap_subtype_val V hV
    have hsub : Subtype.val '' V ⊆ T := by rintro _ ⟨x, -, rfl⟩; exact x.2
    have h1 : IsOpen (f '' (Subtype.val '' V)) := hopen _ hsub hval
    have h2 : F '' V = Subtype.val ⁻¹' (f '' (Subtype.val '' V)) := by
      ext w
      constructor
      · rintro ⟨x, hxV, rfl⟩
        exact ⟨x, ⟨x, hxV, rfl⟩, rfl⟩
      · rintro ⟨-, ⟨x, hxV, rfl⟩, hfx⟩
        exact ⟨x, hxV, Subtype.ext hfx⟩
    rw [h2]
    exact h1.preimage continuous_subtype_val
  -- Upgrade to a homeomorphism `↥T ≃ₜ ↥(ball 0 1)`.
  have hhomeo : (T : Set ℂ) ≃ₜ (Metric.ball (0 : ℂ) 1 : Set ℂ) :=
    (Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen hFcont hFopen
  -- The ball is convex, hence contractible, hence simply connected;
  -- transport along the homotopy equivalence induced by the homeomorphism.
  haveI : ContinuousSMul ℝ ℂ := by
    refine ⟨?_⟩
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p; exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  haveI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace (Metric.nonempty_ball.mpr one_pos)
  exact hhomeo.toHomotopyEquiv.simplyConnectedSpace

/-- Transfer of complement structure to the sphere: for a Fatou-component
avoiding `∞`, disconnectedness of the sphere complement is equivalent to the
existence of a bounded complementary component of its finite part. -/
theorem exists_bounded_component_of_not_isConnected_compl {U : Set ℂ̂}
    (hU : IsOpen U) (_hUne : U.Nonempty) (hinf : ∞ ∉ U)
    (hnc : ¬IsConnected (Uᶜ : Set ℂ̂)) :
    ∃ z : ℂ, ((z : ℂ̂) ∉ U) ∧
      Bornology.IsBounded
        (connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ U} z) := by
  classical
  have hinfc : (∞ : ℂ̂) ∈ Uᶜ := hinf
  -- There is a point of `Uᶜ` outside the connected component of `∞` in `Uᶜ`.
  have hx : ∃ x ∈ (Uᶜ : Set ℂ̂), x ∉ connectedComponentIn (Uᶜ : Set ℂ̂) ∞ := by
    by_contra h
    push Not at h
    refine hnc ?_
    have heq : (Uᶜ : Set ℂ̂) = connectedComponentIn (Uᶜ : Set ℂ̂) ∞ :=
      Set.Subset.antisymm h (connectedComponentIn_subset _ _)
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hinfc
  obtain ⟨x, hxc, hxcc⟩ := hx
  induction x using OnePoint.rec with
  | infty => exact absurd (mem_connectedComponentIn hinfc) hxcc
  | coe z =>
    refine ⟨z, hxc, ?_⟩
    by_contra hub
    set C : Set ℂ := connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ U} z with hCdef
    have hzK : z ∈ {w : ℂ | (w : ℂ̂) ∉ U} := hxc
    have hCz : z ∈ C := mem_connectedComponentIn hzK
    have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCsub : C ⊆ {w : ℂ | (w : ℂ̂) ∉ U} := by
      rw [hCdef]; exact connectedComponentIn_subset _ _
    -- the image of `C` on the sphere and its closure are preconnected
    have himg : IsPreconnected ((fun w : ℂ => (w : ℂ̂)) '' C) :=
      hCpre.image _ OnePoint.continuous_coe.continuousOn
    have hclpre : IsPreconnected (closure ((fun w : ℂ => (w : ℂ̂)) '' C)) := himg.closure
    -- the closure stays inside the closed set `Uᶜ`
    have hsubUc : ((fun w : ℂ => (w : ℂ̂)) '' C) ⊆ Uᶜ := by
      rintro _ ⟨w, hwC, rfl⟩
      exact hCsub hwC
    have hclsub : closure ((fun w : ℂ => (w : ℂ̂)) '' C) ⊆ Uᶜ :=
      hU.isClosed_compl.closure_subset_iff.mpr hsubUc
    -- unboundedness of `C` forces `∞` into the closure of its image
    have hinfcl : (∞ : ℂ̂) ∈ closure ((fun w : ℂ => (w : ℂ̂)) '' C) := by
      rw [mem_closure_iff]
      intro o ho hoinf
      have hcompact : IsCompact (((fun w : ℂ => (w : ℂ̂)) ⁻¹' o)ᶜ) :=
        ((OnePoint.isOpen_iff_of_mem' hoinf).mp ho).1
      have hbdd : Bornology.IsBounded (((fun w : ℂ => (w : ℂ̂)) ⁻¹' o)ᶜ) :=
        hcompact.isBounded
      have hns : ¬ C ⊆ ((fun w : ℂ => (w : ℂ̂)) ⁻¹' o)ᶜ :=
        fun hsub => hub (hbdd.subset hsub)
      obtain ⟨w, hwC, hwo⟩ := Set.not_subset.mp hns
      rw [Set.mem_compl_iff, not_not] at hwo
      exact ⟨(w : ℂ̂), hwo, ⟨w, hwC, rfl⟩⟩
    -- maximality of the component of `∞` swallows the closure, contradiction
    have hzcc : (z : ℂ̂) ∈ connectedComponentIn (Uᶜ : Set ℂ̂) ∞ :=
      hclpre.subset_connectedComponentIn hinfcl hclsub (subset_closure ⟨z, hCz, rfl⟩)
    exact hxcc hzcc

/-- **Degree one over a simply connected target.** A component step whose
target component is simply connected has fiber count one: package the
covering records as a covering map of subtypes, lift the identity through it
(unique lifting over simply connected bases), and observe that the image of
the section is clopen in the connected source. -/
theorem fiberCount_eq_one_of_simplyConnected {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    (hsc : SimplyConnectedSpace (fcOrbit f U (n + 1) : Set ℂ̂))
    {k : ℕ} (hk : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    k = 1 := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd1 hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have himg : f '' S = T := fcOrbit_image_eq hf hd1 hU n
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
  -- ## Stage 0: the sphere is locally path-connected.
  -- Finite points have bases of coe-images of balls; `∞` has the basis of
  -- complements of closed balls, each path-connected via radial rays to `∞`.
  haveI hlpc : LocPathConnectedSpace ℂ̂ := by
    constructor
    intro x
    rw [Filter.hasBasis_self]
    induction x using OnePoint.rec with
    | infty =>
      intro t ht
      obtain ⟨s, ⟨hscl, hscpt⟩, hsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht
      obtain ⟨r0, hr0⟩ := hscpt.isBounded.subset_closedBall 0
      set R := max r0 0 with hRdef
      have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
      have hcompl : ∀ w : ℂ, R < ‖w‖ → w ∈ sᶜ := by
        intro w hw hws
        have h1 := hr0 hws
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        exact absurd (h1.trans (le_max_left _ _)) (not_le.mpr hw)
      refine ⟨(fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | R < ‖w‖} ∪ {∞}, ?_, ?_, ?_⟩
      · refine OnePoint.hasBasis_nhds_infty.mem_iff.mpr
          ⟨Metric.closedBall 0 R,
            ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 R⟩, ?_⟩
        rintro u (⟨w, hw, rfl⟩ | hu)
        · rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
          exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr hu
      · -- the annular neighborhood of `∞` is path-connected
        refine ⟨∞, Or.inr rfl, ?_⟩
        rintro u (⟨a, haR, rfl⟩ | rfl)
        swap
        · exact JoinedIn.refl (Or.inr rfl)
        have haR' : R < ‖a‖ := haR
        have hanorm : (0 : ℝ) < ‖a‖ := lt_of_le_of_lt hR0 haR'
        have hval : ∀ t : unitInterval,
            ‖((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ)‖ = ((t : ℝ))⁻¹ * ‖a‖ := by
          intro t
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr t.2.1)]
        have hmemloc : ∀ t : unitInterval, (t : ℝ) ≠ 0 →
            ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂))
              ∈ (fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | R < ‖w‖} ∪ {∞} := by
          intro t htz
          have htpos : (0 : ℝ) < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm htz)
          have h1 : (1 : ℝ) ≤ ((t : ℝ))⁻¹ := (one_le_inv₀ htpos).mpr t.2.2
          refine Or.inl ⟨_, ?_, rfl⟩
          change R < ‖((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ)‖
          rw [hval t]
          calc R < ‖a‖ := haR'
            _ ≤ ((t : ℝ))⁻¹ * ‖a‖ := le_mul_of_one_le_left (norm_nonneg a) h1
        obtain ⟨γf, hγf⟩ : ∃ g : unitInterval → ℂ̂, g = fun t : unitInterval =>
            if (t : ℝ) = 0 then (∞ : ℂ̂)
            else ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂)) := ⟨_, rfl⟩
        have hγfval : ∀ t : unitInterval, γf t
            = if (t : ℝ) = 0 then (∞ : ℂ̂)
              else ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂)) := by
          intro t
          rw [hγf]
        have hcont : Continuous γf := by
          rw [continuous_iff_continuousAt]
          intro t₀
          by_cases ht₀ : (t₀ : ℝ) = 0
          · have h0eq : γf t₀ = ∞ := by
              rw [hγfval t₀, if_pos ht₀]
            change Filter.Tendsto γf (𝓝 t₀) (𝓝 (γf t₀))
            rw [h0eq, OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
            rintro s' ⟨-, hscpt'⟩
            obtain ⟨m, hm⟩ := hscpt'.isBounded.subset_closedBall 0
            have hMpos : (0 : ℝ) < max m 0 + 1 := by positivity
            have hδ : (0 : ℝ) < ‖a‖ / (max m 0 + 1) := div_pos hanorm hMpos
            have hevlt : ∀ᶠ tt : unitInterval in 𝓝 t₀,
                (tt : ℝ) < ‖a‖ / (max m 0 + 1) := by
              have hc : Tendsto (fun tt : unitInterval => (tt : ℝ)) (𝓝 t₀)
                  (𝓝 ((t₀ : ℝ))) := continuous_subtype_val.continuousAt
              rw [ht₀] at hc
              exact hc.eventually_lt_const hδ
            filter_upwards [hevlt] with tt htt
            by_cases htz : (tt : ℝ) = 0
            · rw [hγfval tt, if_pos htz]
              exact Or.inr rfl
            · rw [hγfval tt, if_neg htz]
              have htpos : (0 : ℝ) < (tt : ℝ) := lt_of_le_of_ne tt.2.1 (Ne.symm htz)
              refine Or.inl ⟨_, ?_, rfl⟩
              intro hmem
              have hle := hm hmem
              rw [Metric.mem_closedBall, dist_zero_right, hval tt] at hle
              have h2 : (tt : ℝ) * (max m 0 + 1) < ‖a‖ := (lt_div_iff₀ hMpos).mp htt
              have h3 : max m 0 + 1 < ((tt : ℝ))⁻¹ * ‖a‖ := by
                rw [← div_eq_inv_mul]
                refine (lt_div_iff₀ htpos).mpr ?_
                rw [mul_comm]
                exact h2
              have hmax : m ≤ max m 0 := le_max_left m 0
              linarith
          · have hev : ∀ᶠ tt : unitInterval in 𝓝 t₀, (tt : ℝ) ≠ 0 :=
              continuous_subtype_val.continuousAt.eventually_ne ht₀
            have hca : ContinuousAt ((fun w : ℂ => ((w : ℂ̂))) ∘
                (fun tt : unitInterval => ((((tt : ℝ)⁻¹ : ℝ) : ℂ) * a))) t₀ := by
              refine ContinuousAt.comp ?_ ?_
              · exact OnePoint.continuous_coe.continuousAt
              · exact (Complex.continuous_ofReal.continuousAt.comp
                  (continuous_subtype_val.continuousAt.inv₀ ht₀)).mul continuousAt_const
            refine hca.congr ?_
            filter_upwards [hev] with tt htt
            rw [hγfval tt, if_neg htt]
            rfl
        refine ⟨⟨⟨γf, hcont⟩, ?_, ?_⟩, ?_⟩
        · change γf 0 = ∞
          rw [hγfval 0]
          exact if_pos rfl
        · change γf 1 = ((a : ℂ̂))
          rw [hγfval 1,
            if_neg (by exact one_ne_zero : ((1 : unitInterval) : ℝ) ≠ 0)]
          change ((((1 : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ̂) = (a : ℂ̂)
          norm_num
        · intro t
          change γf t ∈ _
          by_cases htz : (t : ℝ) = 0
          · rw [hγfval t, if_pos htz]
            exact Or.inr rfl
          · rw [hγfval t, if_neg htz]
            exact hmemloc t htz
      · rintro u (⟨w, hw, rfl⟩ | hu)
        · exact hsub (Or.inl ⟨w, hcompl w hw, rfl⟩)
        · exact hsub (Or.inr hu)
    | coe z =>
      intro t ht
      rw [OnePoint.nhds_coe_eq, Filter.mem_map] at ht
      obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_ball.mem_iff.mp ht
      refine ⟨(fun w : ℂ => ((w : ℂ̂))) '' Metric.ball z ε, ?_, ?_, ?_⟩
      · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
          Set.preimage_image_eq _ OnePoint.coe_injective]
        exact Metric.ball_mem_nhds z hε
      · exact ((convex_ball z ε).isPathConnected
          ⟨z, Metric.mem_ball_self hε⟩).image OnePoint.continuous_coe
      · exact Set.image_subset_iff.mpr hεsub
  -- ## Stage 1: analytic records mined from the `exists_fiberCount` proof.
  have cf : ∀ t : ℂ, chartFiniteMap ((t : ℂ̂)) = t := fun _ => rfl
  have hread : ∀ t : ℂ, r.toSphereMap ((t : ℂ̂))
      = if r.denReduced.eval t = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval t / r.denReduced.eval t : ℂ) : ℂ̂) := fun _ => rfl
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  -- on `S` the reduced denominator does not vanish
  have hden_ne : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → r.denReduced.eval x ≠ 0 := by
    intro x hxS h0
    have hcx := hcrit x hxS
    have hdiff : DifferentiableAt ℂ (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) x := by
      by_contra hnd
      exact hcx (deriv_zero_of_not_differentiableAt hnd)
    have hφx : chartFiniteMap (f ((x : ℂ̂))) = 0 := by
      rw [hr, hread x, if_pos h0]
      rfl
    have hZfin : {t : ℂ | r.denReduced.IsRoot t}.Finite :=
      Polynomial.finite_setOf_isRoot hdenR
    have hclosed : IsClosed ({t : ℂ | r.denReduced.IsRoot t} \ {x}) :=
      (hZfin.subset Set.diff_subset).isClosed
    have hxmem : x ∈ ({t : ℂ | r.denReduced.IsRoot t} \ {x})ᶜ := fun h => h.2 rfl
    have hev_ne : ∀ᶠ t in 𝓝[≠] x, r.denReduced.eval t ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hxmem),
        self_mem_nhdsWithin] with t ht htx
      exact fun h0t => ht ⟨h0t, htx⟩
    have h1 : Tendsto (fun t : ℂ => f ((t : ℂ̂))) (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) := by
      have hc : ContinuousAt (fun t : ℂ => f ((t : ℂ̂))) x :=
        (hf.continuous.comp OnePoint.continuous_coe).continuousAt
      have hfx : f ((x : ℂ̂)) = ∞ := by rw [hr, hread x, if_pos h0]
      have h := hc.tendsto
      rw [hfx] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (((0 : ℂ) : ℂ̂))) := by
      have hφt := hdiff.continuousAt.tendsto
      rw [hφx] at hφt
      exact ((OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hφt).mono_left
        nhdsWithin_le_nhds
    have heq : (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        =ᶠ[𝓝[≠] x] fun t : ℂ => f ((t : ℂ̂)) := by
      filter_upwards [hev_ne] with t ht
      rw [hr, hread t, if_neg ht, cf]
    have h1' : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) h1
    exact OnePoint.coe_ne_infty (0 : ℂ) (tendsto_nhds_unique h2 h1')
  -- values on `S` are finite
  have hSfin : ∀ u ∈ S, f u ≠ ∞ := by
    intro u huS
    have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
    rw [hr, hread x, if_neg (hden_ne x huS)]
    exact OnePoint.coe_ne_infty _
  have hTfin : ∀ w ∈ T, ∃ y : ℂ, w = ((y : ℂ̂)) := by
    intro w hwT
    rw [← himg] at hwT
    obtain ⟨u, huS, rfl⟩ := hwT
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp (hSfin u huS)
    exact ⟨y, hy.symm⟩
  -- fibers over finite points are finite
  have hfib_fin : ∀ y : ℂ, (f ⁻¹' {((y : ℂ̂))} ∩ S).Finite := by
    intro y
    have hq : r.numReduced - Polynomial.C y * r.denReduced ≠ 0 := by
      intro h0
      apply hWr
      have hnum : r.numReduced = Polynomial.C y * r.denReduced := sub_eq_zero.mp h0
      unfold RationalData.wronskian
      rw [hnum, Polynomial.derivative_C_mul]
      ring
    have hsub : f ⁻¹' {((y : ℂ̂))} ∩ S ⊆ (fun x : ℂ => ((x : ℂ̂))) ''
        {x : ℂ | (r.numReduced - Polynomial.C y * r.denReduced).IsRoot x} := by
      rintro u ⟨hufy, huS⟩
      have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
      obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
      have hden := hden_ne x huS
      have hfx : f ((x : ℂ̂)) = ((y : ℂ̂)) := hufy
      rw [hr, hread x, if_neg hden] at hfx
      have hdiv : r.numReduced.eval x / r.denReduced.eval x = y :=
        OnePoint.coe_eq_coe.mp hfx
      rw [div_eq_iff hden] at hdiv
      refine ⟨x, ?_, rfl⟩
      change (r.numReduced - Polynomial.C y * r.denReduced).eval x = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hdiv, sub_self]
    exact ((Polynomial.finite_setOf_isRoot hq).image _).subset hsub
  -- local injectivity near each finite non-critical point
  have hloc : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → ∃ Wc : Set ℂ, IsOpen Wc ∧ x ∈ Wc ∧
      ∀ t₁ ∈ Wc, ∀ t₂ ∈ Wc, f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) → t₁ = t₂ := by
    intro x hxS
    have hcx := hcrit x hxS
    have hden := hden_ne x hxS
    have hev : (fun t : ℂ => r.numReduced.eval t / r.denReduced.eval t)
        =ᶠ[𝓝 x] fun t : ℂ => chartFiniteMap (f ((t : ℂ̂))) := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with t ht
      rw [hr, hread t, if_neg ht, cf]
    obtain ⟨D, hstrict⟩ : ∃ D : ℂ,
        HasStrictDerivAt (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) D x :=
      ⟨_, ((r.numReduced.hasStrictDerivAt x).div
        (r.denReduced.hasStrictDerivAt x) hden).congr_of_eventuallyEq hev⟩
    have hD : D ≠ 0 := hstrict.hasDerivAt.deriv ▸ hcx
    obtain ⟨Wc, hWsub, hWopen, hxW⟩ :=
      mem_nhds_iff.mp (hstrict.eventually_left_inverse hD)
    refine ⟨Wc, hWopen, hxW, ?_⟩
    intro t₁ ht₁ t₂ ht₂ hft
    have h₁ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₁ : ℂ̂)))) = t₁ := hWsub ht₁
    have h₂ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₂ : ℂ̂)))) = t₂ := hWsub ht₂
    rw [← h₁, hft, h₂]
  -- ## Stage 2: the packaged component step between the two subtypes.
  have hmapsto : ∀ u : ℂ̂, u ∈ S → f u ∈ T := by
    intro u hu
    rw [← himg]
    exact ⟨u, hu, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ↥S → ↥T,
      F = fun u => ⟨f u.1, hmapsto u.1 u.2⟩ := ⟨_, rfl⟩
  have hFval : ∀ u : ↥S, ((F u : ℂ̂)) = f u.1 := by
    intro u
    rw [hFdef]
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Continuous.subtype_mk (hf.continuous.comp continuous_subtype_val) _
  -- the packaged map is open
  have hFopen : IsOpenMap F := by
    intro V hV
    obtain ⟨D, hD, hDV⟩ := isOpen_induced_iff.mp hV
    have himgV : F '' V = Subtype.val ⁻¹' (f '' (S ∩ D)) := by
      ext w
      constructor
      · rintro ⟨u, huV, rfl⟩
        have huD : u.1 ∈ D := by
          rw [← hDV] at huV
          exact huV
        exact ⟨u.1, ⟨u.2, huD⟩, (hFval u).symm⟩
      · rintro ⟨v, ⟨hvS, hvD⟩, hfv⟩
        refine ⟨⟨v, hvS⟩, ?_, ?_⟩
        · rw [← hDV]
          exact hvD
        · apply Subtype.ext
          rw [hFval]
          exact hfv
    rw [himgV]
    exact (hfo _ (hSfc.isOpen.inter hD)).preimage continuous_subtype_val
  -- the packaged map is closed (properness via the Julia frontier)
  have hFclosed : IsClosedMap F := by
    intro C hC
    obtain ⟨D, hD, hDC⟩ := isClosed_induced_iff.mp hC
    have hkey : F '' C = Subtype.val ⁻¹' (closure (f '' (S ∩ D))) := by
      ext w
      constructor
      · rintro ⟨u, huC, rfl⟩
        have huD : u.1 ∈ D := by
          rw [← hDC] at huC
          exact huC
        exact subset_closure ⟨u.1, ⟨u.2, huD⟩, (hFval u).symm⟩
      · intro hw
        have hcl : closure (f '' (S ∩ D)) ⊆ f '' closure (S ∩ D) := by
          apply closure_minimal (Set.image_mono subset_closure)
          exact (isClosed_closure.isCompact.image hf.continuous).isClosed
        obtain ⟨x, hxcl, hfx⟩ := hcl hw
        have hxSD : x ∈ closure S ∩ D := by
          have h1 := closure_inter_subset_inter_closure S D hxcl
          rwa [hD.closure_eq] at h1
        by_cases hxS : x ∈ S
        · refine ⟨⟨x, hxS⟩, ?_, ?_⟩
          · rw [← hDC]
            exact hxSD.2
          · apply Subtype.ext
            rw [hFval]
            exact hfx
        · exfalso
          have hxfr : x ∈ frontier S := by
            rw [hSfc.isOpen.frontier_eq]
            exact ⟨hxSD.1, hxS⟩
          have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
          rw [← juliaSet_preimage_eq_of_isRational hf hd1] at hxJ
          have hfxJ : f x ∈ JuliaSet f := hxJ
          rw [hfx] at hfxJ
          exact hfxJ (hTfc.subset_fatouSet w.2)
    rw [hkey]
    exact IsClosed.preimage continuous_subtype_val isClosed_closure
  -- fibers of the packaged map are finite
  have hFfib : ∀ w : ↥T, (F ⁻¹' {w}).Finite := by
    intro w
    obtain ⟨y, hy⟩ := hTfin w.1 w.2
    have hpre : F ⁻¹' {w} = Subtype.val ⁻¹' (f ⁻¹' {((y : ℂ̂))} ∩ S) := by
      ext u
      constructor
      · intro hu
        have h1 : F u = w := hu
        have h2 : f u.1 = ((y : ℂ̂)) := by
          have h3 := congrArg Subtype.val h1
          rw [hFval u] at h3
          rw [h3]
          exact hy
        exact ⟨h2, u.2⟩
      · intro hu
        apply Subtype.ext
        rw [hFval u, hy]
        exact hu.1
    rw [hpre]
    exact Set.Finite.preimage Subtype.coe_injective.injOn (hfib_fin y)
  -- local homeomorphism records for the packaged map
  haveI hSne : Nonempty ↥S := hSfc.nonempty.to_subtype
  have hFloc : ∀ e : ↥S, ∃ φ : OpenPartialHomeomorph ↥S ↥T,
      e ∈ φ.source ∧ ⇑φ = F := by
    intro e
    have hene : (e : ℂ̂) ≠ ∞ := fun h => hinf (h ▸ e.2)
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp hene
    have hxS : ((x : ℂ̂)) ∈ S := by
      rw [hx]
      exact e.2
    obtain ⟨Wc, hWopen, hxW, hWinj⟩ := hloc x hxS
    set src : Set ↥S := Subtype.val ⁻¹' ((fun t : ℂ => ((t : ℂ̂))) '' Wc) with hsrc
    have hsrcopen : IsOpen src :=
      (OnePoint.isOpenEmbedding_coe.isOpenMap _ hWopen).preimage
        continuous_subtype_val
    have hesrc : e ∈ src := ⟨x, hxW, hx⟩
    have hinjF : Set.InjOn F src := by
      rintro u₁ hu₁ u₂ hu₂ h12
      obtain ⟨t₁, ht₁, htv₁⟩ := hu₁
      obtain ⟨t₂, ht₂, htv₂⟩ := hu₂
      have hf12 : f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) := by
        have htv₁' : ((t₁ : ℂ̂)) = (u₁ : ℂ̂) := htv₁
        have htv₂' : ((t₂ : ℂ̂)) = (u₂ : ℂ̂) := htv₂
        rw [htv₁', htv₂']
        have h3 := congrArg Subtype.val h12
        rw [hFval, hFval] at h3
        exact h3
      have ht12 : t₁ = t₂ := hWinj t₁ ht₁ t₂ ht₂ hf12
      apply Subtype.ext
      rw [← htv₁, ← htv₂, ht12]
    refine ⟨OpenPartialHomeomorph.ofContinuousOpen
      (hinjF.toPartialEquiv F src) ?_ ?_ ?_, ?_, ?_⟩
    · exact hFcont.continuousOn
    · exact hFopen
    · exact hsrcopen
    · exact hesrc
    · rfl
  -- ## Stage 3: the packaged map is a covering map.
  have hcovOn : IsCoveringMapOn F Set.univ :=
    hFclosed.isCoveringMapOn_of_openPartialHomeomorph
      (fun w _ => hFfib w) (fun e _ => hFloc e)
  have hcov : IsCoveringMap F := isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  -- ## Stage 4: lift the identity of the simply connected target through `F`.
  haveI := hsc
  haveI : LocPathConnectedSpace ↥T := hTfc.isOpen.locPathConnectedSpace
  obtain ⟨w₀, hw₀T⟩ := hTfc.nonempty
  have hw₀' : w₀ ∈ f '' S := by
    rw [himg]
    exact hw₀T
  obtain ⟨u₀, hu₀S, hu₀f⟩ := hw₀'
  have hbase : F ⟨u₀, hu₀S⟩ = (⟨w₀, hw₀T⟩ : ↥T) := by
    apply Subtype.ext
    rw [hFval]
    exact hu₀f
  obtain ⟨σ, ⟨hσ0, hσlift⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id ↥T) ⟨w₀, hw₀T⟩ ⟨u₀, hu₀S⟩ hbase
  -- ## Stage 5: the section retracts, so the packaged map is injective.
  haveI : PreconnectedSpace ↥S :=
    Subtype.preconnectedSpace hSfc.isConnected.isPreconnected
  have hσF : ⇑σ ∘ F = id := by
    apply hcov.eq_of_comp_eq (σ.continuous.comp hFcont) continuous_id ?_
      ⟨u₀, hu₀S⟩ ?_
    · rw [← Function.comp_assoc, hσlift, ContinuousMap.coe_id,
        Function.id_comp, Function.comp_id]
    · change σ (F ⟨u₀, hu₀S⟩) = ⟨u₀, hu₀S⟩
      rw [hbase, hσ0]
  have hFinj : Function.Injective F := by
    intro u₁ u₂ h12
    have h1 := congrFun hσF u₁
    have h2 := congrFun hσF u₂
    simp only [Function.comp_apply, id_eq] at h1 h2
    rw [← h1, ← h2, h12]
  -- ## Stage 6: a fiber is a singleton, so the constant count is one.
  have hfib : f ⁻¹' {w₀} ∩ S = {u₀} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact ⟨hu₀f, hu₀S⟩
    · rintro v ⟨hvf, hvS⟩
      have hvf' : f v = w₀ := hvf
      have hFeq : F ⟨v, hvS⟩ = F ⟨u₀, hu₀S⟩ := by
        apply Subtype.ext
        rw [hFval, hFval]
        change f v = f u₀
        rw [hvf', hu₀f]
      have := hFinj hFeq
      exact congrArg Subtype.val this
  have hk₀ := hk w₀ hw₀T
  rw [hfib, Set.ncard_singleton] at hk₀
  exact hk₀.symm

/-- **The separation form of the covering dichotomy**: a component step of
fiber count at least two has a target whose sphere complement is
disconnected. Otherwise the finite part of the target would have only
unbounded complementary components, hence be simply connected by the
Riemann-mapping bridge, forcing fiber count one. -/
theorem not_isConnected_compl_of_multiple_step {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n) (hinf' : ∞ ∉ fcOrbit f U (n + 1))
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hk : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    ¬IsConnected ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) := by
  classical
  intro hcon
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  set W : Set ℂ̂ := fcOrbit f U (n + 1) with hWdef
  have hWfc : IsFatouComponent f W := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have hWopen : IsOpen W := hWfc.isOpen
  have hWconn : IsConnected W := hWfc.isConnected
  -- `W` avoids `∞`, hence lies in the range of the coercion.
  have hWrange : W ⊆ Set.range (fun w : ℂ => (w : ℂ̂)) := by
    intro w hw
    by_contra hnr
    have hweq : w = ∞ := OnePoint.notMem_range_coe_iff.mp hnr
    rw [hweq] at hw
    exact hinf' hw
  -- The finite part of the target component.
  set T : Set ℂ := (fun w : ℂ => (w : ℂ̂)) ⁻¹' W with hTdef
  have himg : (fun w : ℂ => (w : ℂ̂)) '' T = W :=
    Set.image_preimage_eq_of_subset hWrange
  have hTopen : IsOpen T := hWopen.preimage OnePoint.continuous_coe
  have hTne : T.Nonempty := by
    obtain ⟨w, hw⟩ := hWfc.nonempty
    obtain ⟨z0, rfl⟩ := hWrange hw
    exact ⟨z0, hw⟩
  have hTpre : IsPreconnected T := by
    have h1 : IsPreconnected ((fun w : ℂ => (w : ℂ̂)) '' T) := by
      rw [himg]
      exact hWconn.isPreconnected
    exact (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp h1
  have hTconn : IsConnected T := ⟨hTne, hTpre⟩
  -- The finite part is proper: the (infinite) Julia set misses `W`.
  have hTneq : T ≠ Set.univ := by
    intro hTuniv
    have hWeq : W = Set.range (fun w : ℂ => (w : ℂ̂)) := by
      rw [← himg, hTuniv, Set.image_univ]
    have hJsub : JuliaSet f ⊆ {∞} := by
      intro x hx
      have hxW : x ∉ W := fun hxW => hx (hWfc.subset_fatouSet hxW)
      rw [hWeq] at hxW
      rw [Set.mem_singleton_iff]
      exact OnePoint.notMem_range_coe_iff.mp hxW
    exact juliaSet_infinite hf hd ((Set.finite_singleton ∞).subset hJsub)
  -- Šura-Bura: every complementary component of `T` in the plane is
  -- unbounded, else a clopen separation of `Wᶜ` on the sphere appears.
  have hcompl : ∀ z ∉ T, ¬Bornology.IsBounded (connectedComponentIn Tᶜ z) := by
    intro z hzT hbdd
    have hzF : z ∈ (Tᶜ : Set ℂ) := hzT
    have hzC : z ∈ connectedComponentIn Tᶜ z := mem_connectedComponentIn hzF
    obtain ⟨R, hCR⟩ := hbdd.subset_ball (0 : ℂ)
    have hFclosed : IsClosed (Tᶜ : Set ℂ) := hTopen.isClosed_compl
    -- the compact truncation of the complement
    set K : Set ℂ := Tᶜ ∩ Metric.closedBall (0 : ℂ) R with hKdef
    have hKcomp : IsCompact K :=
      (isCompact_closedBall (0 : ℂ) R).inter_left hFclosed
    have hzK : z ∈ K := ⟨hzF, Metric.ball_subset_closedBall (hCR hzC)⟩
    have hCsubK : connectedComponentIn Tᶜ z ⊆ K := fun w hw =>
      ⟨connectedComponentIn_subset _ _ hw,
        Metric.ball_subset_closedBall (hCR hw)⟩
    -- the bounded component is a component of the truncation
    have hCeq : connectedComponentIn K z = connectedComponentIn Tᶜ z := by
      apply Set.Subset.antisymm
      · exact connectedComponentIn_mono z Set.inter_subset_left
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
          hzC hCsubK
    haveI hKcs : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcomp
    set z' : ↥K := ⟨z, hzK⟩ with hz'def
    have hcc : Subtype.val '' connectedComponent z' =
        connectedComponentIn Tᶜ z := by
      rw [hz'def, ← connectedComponentIn_eq_image hzK]
      exact hCeq
    -- the shell of the truncation, inside the subtype
    set E : Set ↥K := Subtype.val ⁻¹' (Metric.ball (0 : ℂ) R)ᶜ with hEdef
    have hEclosed : IsClosed E :=
      (Metric.isOpen_ball.isClosed_compl).preimage continuous_subtype_val
    have hEcomp : IsCompact E := hEclosed.isCompact
    -- the connected component of `z'` misses the shell
    have hccE : connectedComponent z' ∩ E = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro w ⟨hwc, hwE⟩
      have hwC : (w : ℂ) ∈ connectedComponentIn Tᶜ z := by
        rw [← hcc]
        exact ⟨w, hwc, rfl⟩
      exact hwE (hCR hwC)
    -- Šura-Bura in the compact subtype: finitely many clopen neighbourhoods
    -- of `z'` already miss the shell
    have hdisj : E ∩ ⋂ (s : {s : Set ↥K // IsClopen s ∧ z' ∈ s}),
        (s : Set ↥K) = ∅ := by
      rw [← connectedComponent_eq_iInter_isClopen z', Set.inter_comm]
      exact hccE
    obtain ⟨u, hu⟩ := hEcomp.elim_finite_subfamily_closed
      (fun s : {s : Set ↥K // IsClopen s ∧ z' ∈ s} => (s : Set ↥K))
      (fun s => s.2.1.isClosed) hdisj
    have hu' : E ∩ ⋂ s ∈ u, (s : Set ↥K) = ∅ := hu
    set A' : Set ↥K := ⋂ s ∈ u, (s : Set ↥K) with hA'def
    have hA'clopen : IsClopen A' := isClopen_biInter_finset (fun s _ => s.2.1)
    have hz'A' : z' ∈ A' := Set.mem_iInter₂.mpr (fun s _ => s.2.2)
    -- the corresponding compact subset of the plane
    have hAcomp : IsCompact (Subtype.val '' A') :=
      (hA'clopen.isClosed.isCompact).image continuous_subtype_val
    have hzA : z ∈ Subtype.val '' A' := ⟨z', hz'A', rfl⟩
    have hAball : Subtype.val '' A' ⊆ Metric.ball (0 : ℂ) R := by
      rintro _ ⟨w, hwA', rfl⟩
      by_contra hnb
      have hwEmem : w ∈ E := hnb
      have hcontra : w ∈ E ∩ A' := ⟨hwEmem, hwA'⟩
      rw [hu'] at hcontra
      exact hcontra
    -- `A` is the trace on `Tᶜ` of an open subset of the ball
    obtain ⟨O₁, hO₁open, hO₁⟩ :=
      Topology.IsInducing.subtypeVal.isOpen_iff.mp hA'clopen.isOpen
    have hAeq : Subtype.val '' A' = Tᶜ ∩ (O₁ ∩ Metric.ball (0 : ℂ) R) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨w, hwA', rfl⟩
        refine ⟨w.2.1, ?_, hAball ⟨w, hwA', rfl⟩⟩
        have hw' : w ∈ Subtype.val ⁻¹' O₁ := by rw [hO₁]; exact hwA'
        exact hw'
      · rintro a ⟨haF, haO₁, haB⟩
        have haK : a ∈ K := ⟨haF, Metric.ball_subset_closedBall haB⟩
        have haA' : (⟨a, haK⟩ : ↥K) ∈ A' := by
          rw [← hO₁]
          exact haO₁
        exact ⟨⟨a, haK⟩, haA', rfl⟩
    -- transfer the clopen trace to the sphere complement `Wᶜ`
    haveI hpc : PreconnectedSpace ↥(Wᶜ : Set ℂ̂) :=
      Subtype.preconnectedSpace hcon.isPreconnected
    have hAscomp : IsCompact ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) :=
      hAcomp.image OnePoint.continuous_coe
    have hAsubClosed : IsClosed (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) :=
      hAscomp.isClosed.preimage continuous_subtype_val
    have hOs_open : IsOpen ((fun w : ℂ => (w : ℂ̂)) ''
        (O₁ ∩ Metric.ball (0 : ℂ) R)) :=
      OnePoint.isOpenEmbedding_coe.isOpenMap _
        (hO₁open.inter Metric.isOpen_ball)
    have hAsubEq : (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) =
        Subtype.val ⁻¹'
          ((fun w : ℂ => (w : ℂ̂)) '' (O₁ ∩ Metric.ball (0 : ℂ) R)) := by
      ext x
      simp only [Set.mem_preimage]
      constructor
      · rintro ⟨a, haA, hax⟩
        rw [hAeq] at haA
        exact ⟨a, haA.2, hax⟩
      · rintro ⟨a, haO, hax⟩
        have haT : a ∈ (Tᶜ : Set ℂ) := by
          intro haT'
          have hxW : (x : ℂ̂) ∈ (Wᶜ : Set ℂ̂) := x.2
          rw [← hax] at hxW
          exact hxW haT'
        rw [hAeq]
        exact ⟨a, ⟨haT, haO⟩, hax⟩
    have hAsubOpen : IsOpen (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) := by
      rw [hAsubEq]
      exact hOs_open.preimage continuous_subtype_val
    have hclopen : IsClopen (Subtype.val ⁻¹'
        ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) :=
      ⟨hAsubClosed, hAsubOpen⟩
    -- a clopen subset of the preconnected `Wᶜ` is empty or everything;
    -- both options fail
    rcases isClopen_iff.mp hclopen with hempty | huniv
    · have hzW : ((z : ℂ̂)) ∈ (Wᶜ : Set ℂ̂) := hzF
      have hmem : (⟨(z : ℂ̂), hzW⟩ : ↥(Wᶜ : Set ℂ̂)) ∈ (Subtype.val ⁻¹'
          ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) :=
        ⟨z, hzA, rfl⟩
      rw [hempty] at hmem
      exact hmem
    · have hinfW : (∞ : ℂ̂) ∈ (Wᶜ : Set ℂ̂) := hinf'
      have hmem : (⟨∞, hinfW⟩ : ↥(Wᶜ : Set ℂ̂)) ∈ (Subtype.val ⁻¹'
          ((fun w : ℂ => (w : ℂ̂)) '' (Subtype.val '' A')) : Set ↥(Wᶜ : Set ℂ̂)) := by
        rw [huniv]
        exact Set.mem_univ _
      exact OnePoint.infty_notMem_image_coe hmem
  -- The Riemann-mapping bridge gives simple connectivity of the finite part,
  -- which transfers to the sphere component along the open embedding.
  have hsc : SimplyConnectedSpace T :=
    simplyConnectedSpace_of_unbounded_components hTopen hTconn hTneq hcompl
  have hscW : SimplyConnectedSpace (W : Set ℂ̂) := by
    have h1 : IsSimplyConnected ((fun w : ℂ => (w : ℂ̂)) '' T) :=
      (OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image).mpr hsc
    rw [himg] at h1
    exact h1.simplyConnectedSpace
  -- Degree one over a simply connected target contradicts `2 ≤ k`.
  have hk1 : k = 1 :=
    fiberCount_eq_one_of_simplyConnected hf hd hU n hinf hcrit hscW hk
  omega

/-- The Riemann sphere is locally path-connected: finite points have chart
balls, and a neighborhood basis at `∞` is given by complements of closed
balls, which are path-connected through radial rays. -/
instance instLocPathConnectedSphere : LocPathConnectedSpace ℂ̂ := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  induction x using OnePoint.rec with
  | infty =>
    intro t ht
    obtain ⟨s, ⟨hscl, hscpt⟩, hsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht
    obtain ⟨r0, hr0⟩ := hscpt.isBounded.subset_closedBall 0
    set R := max r0 0 with hRdef
    have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
    have hcompl : ∀ w : ℂ, R < ‖w‖ → w ∈ sᶜ := by
      intro w hw hws
      have h1 := hr0 hws
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact absurd (h1.trans (le_max_left _ _)) (not_le.mpr hw)
    refine ⟨(fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | R < ‖w‖} ∪ {∞}, ?_, ?_, ?_⟩
    · refine OnePoint.hasBasis_nhds_infty.mem_iff.mpr
        ⟨Metric.closedBall 0 R,
          ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 R⟩, ?_⟩
      rintro u (⟨w, hw, rfl⟩ | hu)
      · rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
        exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr hu
    · -- the annular neighborhood of `∞` is path-connected
      refine ⟨∞, Or.inr rfl, ?_⟩
      rintro u (⟨a, haR, rfl⟩ | rfl)
      swap
      · exact JoinedIn.refl (Or.inr rfl)
      have haR' : R < ‖a‖ := haR
      have hanorm : (0 : ℝ) < ‖a‖ := lt_of_le_of_lt hR0 haR'
      have hval : ∀ t : unitInterval,
          ‖((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ)‖ = ((t : ℝ))⁻¹ * ‖a‖ := by
        intro t
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr t.2.1)]
      have hmemloc : ∀ t : unitInterval, (t : ℝ) ≠ 0 →
          ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂))
            ∈ (fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | R < ‖w‖} ∪ {∞} := by
        intro t htz
        have htpos : (0 : ℝ) < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm htz)
        have h1 : (1 : ℝ) ≤ ((t : ℝ))⁻¹ := (one_le_inv₀ htpos).mpr t.2.2
        refine Or.inl ⟨_, ?_, rfl⟩
        change R < ‖((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ)‖
        rw [hval t]
        calc R < ‖a‖ := haR'
          _ ≤ ((t : ℝ))⁻¹ * ‖a‖ := le_mul_of_one_le_left (norm_nonneg a) h1
      obtain ⟨γf, hγf⟩ : ∃ g : unitInterval → ℂ̂, g = fun t : unitInterval =>
          if (t : ℝ) = 0 then (∞ : ℂ̂)
          else ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂)) := ⟨_, rfl⟩
      have hγfval : ∀ t : unitInterval, γf t
          = if (t : ℝ) = 0 then (∞ : ℂ̂)
            else ((((((t : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ) : ℂ̂)) := by
        intro t
        rw [hγf]
      have hcont : Continuous γf := by
        rw [continuous_iff_continuousAt]
        intro t₀
        by_cases ht₀ : (t₀ : ℝ) = 0
        · have h0eq : γf t₀ = ∞ := by
            rw [hγfval t₀, if_pos ht₀]
          change Filter.Tendsto γf (𝓝 t₀) (𝓝 (γf t₀))
          rw [h0eq, OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
          rintro s' ⟨-, hscpt'⟩
          obtain ⟨m, hm⟩ := hscpt'.isBounded.subset_closedBall 0
          have hMpos : (0 : ℝ) < max m 0 + 1 := by positivity
          have hδ : (0 : ℝ) < ‖a‖ / (max m 0 + 1) := div_pos hanorm hMpos
          have hevlt : ∀ᶠ tt : unitInterval in 𝓝 t₀,
              (tt : ℝ) < ‖a‖ / (max m 0 + 1) := by
            have hc : Tendsto (fun tt : unitInterval => (tt : ℝ)) (𝓝 t₀)
                (𝓝 ((t₀ : ℝ))) := continuous_subtype_val.continuousAt
            rw [ht₀] at hc
            exact hc.eventually_lt_const hδ
          filter_upwards [hevlt] with tt htt
          by_cases htz : (tt : ℝ) = 0
          · rw [hγfval tt, if_pos htz]
            exact Or.inr rfl
          · rw [hγfval tt, if_neg htz]
            have htpos : (0 : ℝ) < (tt : ℝ) := lt_of_le_of_ne tt.2.1 (Ne.symm htz)
            refine Or.inl ⟨_, ?_, rfl⟩
            intro hmem
            have hle := hm hmem
            rw [Metric.mem_closedBall, dist_zero_right, hval tt] at hle
            have h2 : (tt : ℝ) * (max m 0 + 1) < ‖a‖ := (lt_div_iff₀ hMpos).mp htt
            have h3 : max m 0 + 1 < ((tt : ℝ))⁻¹ * ‖a‖ := by
              rw [← div_eq_inv_mul]
              refine (lt_div_iff₀ htpos).mpr ?_
              rw [mul_comm]
              exact h2
            have hmax : m ≤ max m 0 := le_max_left m 0
            linarith
        · have hev : ∀ᶠ tt : unitInterval in 𝓝 t₀, (tt : ℝ) ≠ 0 :=
            continuous_subtype_val.continuousAt.eventually_ne ht₀
          have hca : ContinuousAt ((fun w : ℂ => ((w : ℂ̂))) ∘
              (fun tt : unitInterval => ((((tt : ℝ)⁻¹ : ℝ) : ℂ) * a))) t₀ := by
            refine ContinuousAt.comp ?_ ?_
            · exact OnePoint.continuous_coe.continuousAt
            · exact (Complex.continuous_ofReal.continuousAt.comp
                (continuous_subtype_val.continuousAt.inv₀ ht₀)).mul continuousAt_const
          refine hca.congr ?_
          filter_upwards [hev] with tt htt
          rw [hγfval tt, if_neg htt]
          rfl
      refine ⟨⟨⟨γf, hcont⟩, ?_, ?_⟩, ?_⟩
      · change γf 0 = ∞
        rw [hγfval 0]
        exact if_pos rfl
      · change γf 1 = ((a : ℂ̂))
        rw [hγfval 1,
          if_neg (by exact one_ne_zero : ((1 : unitInterval) : ℝ) ≠ 0)]
        change ((((1 : ℝ)⁻¹ : ℝ) : ℂ) * a : ℂ̂) = (a : ℂ̂)
        norm_num
      · intro t
        change γf t ∈ _
        by_cases htz : (t : ℝ) = 0
        · rw [hγfval t, if_pos htz]
          exact Or.inr rfl
        · rw [hγfval t, if_neg htz]
          exact hmemloc t htz
    · rintro u (⟨w, hw, rfl⟩ | hu)
      · exact hsub (Or.inl ⟨w, hcompl w hw, rfl⟩)
      · exact hsub (Or.inr hu)
  | coe z =>
    intro t ht
    rw [OnePoint.nhds_coe_eq, Filter.mem_map] at ht
    obtain ⟨ε, hε, hεsub⟩ := Metric.nhds_basis_ball.mem_iff.mp ht
    refine ⟨(fun w : ℂ => ((w : ℂ̂))) '' Metric.ball z ε, ?_, ?_, ?_⟩
    · rw [OnePoint.nhds_coe_eq, Filter.mem_map,
        Set.preimage_image_eq _ OnePoint.coe_injective]
      exact Metric.ball_mem_nhds z hε
    · exact ((convex_ball z ε).isPathConnected
        ⟨z, Metric.mem_ball_self hε⟩).image OnePoint.continuous_coe
    · exact Set.image_subset_iff.mpr hεsub

open Complex Set in
/-- **Simply connected neighborhoods of full compact sets.** A nonempty
connected compact set all of whose complementary components are unbounded
admits, inside every open superset, an open simply connected neighborhood:
filled dyadic grid hulls of the set shrink down to it, so a sufficiently
fine filled hull separates it from the complement of the open superset, and
the filled hull's interior component around the set has connected unbounded
complement, hence is simply connected by the Riemann-mapping bridge. -/
theorem exists_simplyConnectedSpace_between {K T : Set ℂ} (hK : IsCompact K)
    (hKconn : IsConnected K)
    (hKfull : ∀ z ∉ K, ¬Bornology.IsBounded (connectedComponentIn Kᶜ z))
    (hT : IsOpen T) (hKT : K ⊆ T) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ W ⊆ T ∧ SimplyConnectedSpace W := by
  classical
  -- ------------------------------------------------------------------
  -- Setup: base point, radius bound, far point `zf`, far region.
  -- ------------------------------------------------------------------
  obtain ⟨x₀, hx₀⟩ := hKconn.nonempty
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 + 3 with hRdef
  have hR3 : (3 : ℝ) ≤ R := by
    have h := le_max_right R₀ 0
    rw [hRdef]
    linarith
  have hKR : K ⊆ Metric.closedBall (0 : ℂ) (R - 3) := by
    intro z hz
    have h1 := hR₀ hz
    rw [Metric.mem_closedBall] at h1 ⊢
    have h2 : R₀ ≤ max R₀ 0 := le_max_left _ _
    rw [hRdef]
    linarith
  set zf : ℂ := (R : ℂ) with hzfdef
  have hzfnorm : ‖zf‖ = R := by
    rw [hzfdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ R)]
  have hAconn : IsConnected {z : ℂ | R - 1 < ‖z‖} := isConnected_setOf_lt_norm (R - 1)
  have hzfA : zf ∈ {z : ℂ | R - 1 < ‖z‖} := by
    rw [Set.mem_setOf_eq, hzfnorm]; linarith
  have hAunb : ¬Bornology.IsBounded {z : ℂ | R - 1 < ‖z‖} := by
    intro hb
    obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : ℂ)
    set w : ℂ := ((max r (R - 1) + 1 : ℝ) : ℂ) with hwdef
    have hw1 : R - 1 ≤ max r (R - 1) := le_max_right r (R - 1)
    have hwnorm : ‖w‖ = max r (R - 1) + 1 := by
      rw [hwdef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ max r (R - 1) + 1)]
    have hwA : w ∈ {z : ℂ | R - 1 < ‖z‖} := by
      rw [Set.mem_setOf_eq, hwnorm]; linarith
    have h2 := hr hwA
    rw [Metric.mem_closedBall, dist_zero_right, hwnorm] at h2
    have h3 : r ≤ max r (R - 1) := le_max_left r (R - 1)
    linarith
  -- ------------------------------------------------------------------
  -- Closed thickenings `N r`, unbounded components `U r`, fills `F r`.
  -- ------------------------------------------------------------------
  set N : ℝ → Set ℂ := fun r => {z : ℂ | Metric.infDist z K ≤ r} with hNdef
  set U : ℝ → Set ℂ := fun r => connectedComponentIn (N r)ᶜ zf with hUdef
  set F : ℝ → Set ℂ := fun r => (U r)ᶜ with hFdef
  have hNmem : ∀ (r : ℝ) (z : ℂ), z ∈ N r ↔ Metric.infDist z K ≤ r := fun r z => Iff.rfl
  have hFmem : ∀ (r : ℝ) (z : ℂ), z ∈ F r ↔ z ∉ U r := fun r z => Iff.rfl
  have hNclosed : ∀ r : ℝ, IsClosed (N r) := by
    intro r
    rw [hNdef]
    exact isClosed_le (Metric.continuous_infDist_pt K) continuous_const
  have hNball : ∀ r : ℝ, r ≤ 1 → N r ⊆ Metric.ball (0 : ℂ) (R - 1) := by
    intro r hr z hz
    rw [hNmem] at hz
    have h2 : Metric.infDist z K < 2 := lt_of_le_of_lt hz (by linarith)
    obtain ⟨v, hvK, hvd⟩ := (Metric.infDist_lt_iff ⟨x₀, hx₀⟩).mp h2
    have h3 := hKR hvK
    rw [Metric.mem_closedBall] at h3
    rw [Metric.mem_ball]
    calc dist z 0 ≤ dist z v + dist v 0 := dist_triangle _ _ _
      _ < 2 + (R - 3) := by linarith
      _ = R - 1 := by ring
  have hAN : ∀ r : ℝ, r ≤ 1 → {z : ℂ | R - 1 < ‖z‖} ⊆ (N r)ᶜ := by
    intro r hr z hz hzN
    have h1 := hNball r hr hzN
    rw [Metric.mem_ball, dist_zero_right] at h1
    rw [Set.mem_setOf_eq] at hz
    linarith
  have hUopen : ∀ r : ℝ, IsOpen (U r) := by
    intro r
    rw [hUdef]
    exact (hNclosed r).isOpen_compl.connectedComponentIn
  have hUsub : ∀ r : ℝ, U r ⊆ (N r)ᶜ := by
    intro r
    rw [hUdef]
    exact connectedComponentIn_subset _ _
  have hAU : ∀ r : ℝ, r ≤ 1 → {z : ℂ | R - 1 < ‖z‖} ⊆ U r := by
    intro r hr
    rw [hUdef]
    exact hAconn.isPreconnected.subset_connectedComponentIn hzfA (hAN r hr)
  have hzfU : ∀ r : ℝ, r ≤ 1 → zf ∈ U r := fun r hr => hAU r hr hzfA
  have hUpre : ∀ r : ℝ, IsPreconnected (U r) := by
    intro r
    rw [hUdef]
    exact isPreconnected_connectedComponentIn
  have hNF : ∀ r : ℝ, N r ⊆ F r := by
    intro r z hz
    rw [hFmem]
    intro hzU
    exact hUsub r hzU hz
  have hFsub : ∀ r : ℝ, r ≤ 1 → F r ⊆ Metric.closedBall (0 : ℂ) (R - 1) := by
    intro r hr z hz
    by_contra hzb
    have hzA : z ∈ {v : ℂ | R - 1 < ‖v‖} := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hzb
      exact hzb
    exact (hFmem r z).mp hz (hAU r hr hzA)
  have hUmono : ∀ r s : ℝ, r ≤ s → s ≤ 1 → U s ⊆ U r := by
    intro r s hrs hs1
    have hNrs : N r ⊆ N s := by
      intro z hz
      rw [hNmem] at hz ⊢
      linarith
    have h1 : U s ⊆ (N r)ᶜ := (hUsub s).trans (compl_subset_compl.mpr hNrs)
    rw [hUdef]
    exact (hUpre s).subset_connectedComponentIn (hzfU s hs1) h1
  have hFmono : ∀ r s : ℝ, r ≤ s → s ≤ 1 → F r ⊆ F s := by
    intro r s hrs hs1
    rw [hFdef]
    exact compl_subset_compl.mpr (hUmono r s hrs hs1)
  have hFclosed : ∀ r : ℝ, IsClosed (F r) := by
    intro r
    rw [hFdef]
    exact (hUopen r).isClosed_compl
  have hFcompact : ∀ r : ℝ, r ≤ 1 → IsCompact (F r) := fun r hr =>
    Metric.isCompact_of_isClosed_isBounded (hFclosed r)
      (Metric.isBounded_closedBall.subset (hFsub r hr))
  have hδ1 : ∀ k : ℕ, ((2:ℝ)⁻¹ ^ k) ≤ 1 := fun k =>
    pow_le_one₀ (by norm_num) (by norm_num)
  -- ------------------------------------------------------------------
  -- Escape: every point outside `K` escapes some fine fill.
  -- ------------------------------------------------------------------
  have hesc : ∀ x, x ∉ K → ∃ k : ℕ, x ∉ F ((2:ℝ)⁻¹ ^ k) := by
    intro x hxK
    -- the component of `x` in `Kᶜ` is open, connected and unbounded
    have hxKc : x ∈ Kᶜ := hxK
    have hCopen : IsOpen (connectedComponentIn Kᶜ x) :=
      hK.isClosed.isOpen_compl.connectedComponentIn
    have hCconn : IsConnected (connectedComponentIn Kᶜ x) :=
      ⟨⟨x, mem_connectedComponentIn hxKc⟩, isPreconnected_connectedComponentIn⟩
    -- pick a far point `y₀` of the component
    have hfar : ∃ y₀ ∈ connectedComponentIn Kᶜ x, R - 1 < ‖y₀‖ := by
      by_contra hno
      push Not at hno
      refine hKfull x hxK
        ((Metric.isBounded_closedBall (x := (0:ℂ)) (r := R - 1)).subset ?_)
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hno y hy
    obtain ⟨y₀, hy₀C, hy₀far⟩ := hfar
    -- a path from `x` to `y₀` inside the component
    have hCpath : IsPathConnected (connectedComponentIn Kᶜ x) :=
      hCopen.isConnected_iff_isPathConnected.mp hCconn
    obtain ⟨γ, hγ⟩ := hCpath.joinedIn x (mem_connectedComponentIn hxKc) y₀ hy₀C
    -- its image is a compact connected set avoiding `K`
    have hLcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
    have hLconn : IsConnected (Set.range γ) := isConnected_range γ.continuous
    have hLK : ∀ y ∈ Set.range γ, y ∉ K := by
      rintro y ⟨t, rfl⟩ hyK
      exact connectedComponentIn_subset Kᶜ x (hγ t) hyK
    -- uniform positive distance from the path image to `K`
    have hinf_cont : ContinuousOn (fun y : ℂ => Metric.infDist y K) (Set.range γ) :=
      (Metric.continuous_infDist_pt K).continuousOn
    obtain ⟨ymin, hyminL, hyminOn⟩ :=
      hLcompact.exists_isMinOn ⟨x, 0, γ.source⟩ hinf_cont
    have hymin : ∀ y ∈ Set.range γ, Metric.infDist ymin K ≤ Metric.infDist y K :=
      isMinOn_iff.mp hyminOn
    have hρpos : 0 < Metric.infDist ymin K := by
      rcases (Metric.infDist_nonneg (s := K) (x := ymin)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hycl : ymin ∈ closure K :=
          (Metric.mem_closure_iff_infDist_zero ⟨x₀, hx₀⟩).mpr h.symm
        rw [hK.isClosed.closure_eq] at hycl
        exact hLK ymin hyminL hycl
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hρpos (by norm_num : (2:ℝ)⁻¹ < 1)
    refine ⟨k, ?_⟩
    -- the path image avoids the thickening, hence sits in `U`
    have hLN : Set.range γ ⊆ (N ((2:ℝ)⁻¹ ^ k))ᶜ := by
      intro y hyL
      rw [Set.mem_compl_iff]
      intro hyN
      rw [hNmem] at hyN
      have h1 := hymin y hyL
      linarith
    have hy₀U : y₀ ∈ U ((2:ℝ)⁻¹ ^ k) := hAU _ (hδ1 k) hy₀far
    have hLU : Set.range γ ⊆ U ((2:ℝ)⁻¹ ^ k) := by
      have h1 : U ((2:ℝ)⁻¹ ^ k) = connectedComponentIn (N ((2:ℝ)⁻¹ ^ k))ᶜ y₀ := by
        rw [hUdef]
        exact connectedComponentIn_eq hy₀U
      rw [h1]
      exact hLconn.isPreconnected.subset_connectedComponentIn ⟨1, γ.target⟩ hLN
    have hxU : x ∈ U ((2:ℝ)⁻¹ ^ k) := hLU ⟨0, γ.source⟩
    exact fun hxF => (hFmem _ x).mp hxF hxU
  -- ------------------------------------------------------------------
  -- Selection: some fine fill separates `K` from `Tᶜ`.
  -- ------------------------------------------------------------------
  have hsel : ∃ k : ℕ, F ((2:ℝ)⁻¹ ^ k) ⊆ T := by
    by_contra hno
    push Not at hno
    have hne : ∀ k : ℕ, (F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ).Nonempty := by
      intro k
      obtain ⟨z, hzF, hzT⟩ := Set.not_subset.mp (hno k)
      exact ⟨z, hzF, hzT⟩
    have hanti : Antitone (fun k : ℕ => F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ) := by
      intro k l hkl
      exact Set.inter_subset_inter_left _
        (hFmono _ _ (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl) (hδ1 k))
    have hGcompact : ∀ k : ℕ, IsCompact (F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ) := fun k =>
      (hFcompact _ (hδ1 k)).inter_right hT.isClosed_compl
    have hGclosed : ∀ k : ℕ, IsClosed (F ((2:ℝ)⁻¹ ^ k) ∩ Tᶜ) := fun k =>
      (hFclosed _).inter hT.isClosed_compl
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      _ hanti.directed_ge hne hGcompact hGclosed
    rw [Set.mem_iInter] at hx
    have hxT : x ∈ Tᶜ := (hx 0).2
    have hxK : x ∉ K := fun hxK => hxT (hKT hxK)
    obtain ⟨k, hk⟩ := hesc x hxK
    exact hk (hx k).1
  obtain ⟨k0, hFT⟩ := hsel
  set δ : ℝ := (2:ℝ)⁻¹ ^ k0 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle1 : δ ≤ 1 := hδ1 k0
  -- ------------------------------------------------------------------
  -- The neighborhood: interior of the fill, component around `K`.
  -- ------------------------------------------------------------------
  have hKint : K ⊆ interior (F δ) := by
    intro z hz
    rw [mem_interior]
    refine ⟨Metric.ball z δ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hδpos⟩
    intro y hy
    refine hNF δ ?_
    rw [hNmem]
    rw [Metric.mem_ball] at hy
    exact le_of_lt (lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hz) hy)
  set W₀ : Set ℂ := interior (F δ) with hW₀def
  set W : Set ℂ := connectedComponentIn W₀ x₀ with hWdef
  have hW₀open : IsOpen W₀ := isOpen_interior
  have hWopen : IsOpen W := hW₀open.connectedComponentIn
  have hKW : K ⊆ W := hKconn.isPreconnected.subset_connectedComponentIn hx₀ hKint
  have hWW₀ : W ⊆ W₀ := connectedComponentIn_subset _ _
  have hW₀F : W₀ ⊆ F δ := interior_subset
  have hWT : W ⊆ T := fun z hz => hFT (hW₀F (hWW₀ hz))
  have hWconn : IsConnected W := ⟨⟨x₀, mem_connectedComponentIn (hKint hx₀)⟩,
    isPreconnected_connectedComponentIn⟩
  -- ------------------------------------------------------------------
  -- Complement analysis: `Wᶜ` is preconnected and unbounded.
  -- ------------------------------------------------------------------
  have hzfF : zf ∉ F δ := fun h => (hFmem δ zf).mp h (hzfU δ hδle1)
  have hzfW₀ : zf ∉ W₀ := fun h => hzfF (hW₀F h)
  have hzfW : zf ∉ W := fun h => hzfW₀ (hWW₀ h)
  have hFc : (F δ)ᶜ = U δ := compl_compl (U δ)
  have hW₀c : W₀ᶜ = closure (U δ) := by
    rw [hW₀def, ← closure_compl, hFc]
  have hCpre : IsPreconnected W₀ᶜ := by
    rw [hW₀c]
    exact (hUpre δ).closure
  have hzfC : zf ∈ W₀ᶜ := hzfW₀
  -- every point of `Wᶜ` lies in a preconnected subset of `Wᶜ` containing `zf`
  have hWcov : Wᶜ = ⋃₀ {E : Set ℂ | E ⊆ Wᶜ ∧ IsPreconnected E ∧ zf ∈ E} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hzW₀ : z ∈ W₀
      · -- the component `V` of `z` in `W₀`, glued with the outer part `W₀ᶜ`
        have hzV : z ∈ connectedComponentIn W₀ z := mem_connectedComponentIn hzW₀
        have hVW : ∀ v ∈ connectedComponentIn W₀ z, v ∉ W := by
          intro v hvV hvW
          have h1 : connectedComponentIn W₀ x₀ = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hvW
          have h2 : connectedComponentIn W₀ z = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hvV
          have h3 : z ∈ connectedComponentIn W₀ x₀ := by
            rw [h1, ← h2]
            exact hzV
          exact hz h3
        -- closure points of the component inside `W₀` belong to the component
        have hcloV : closure (connectedComponentIn W₀ z) ∩ W₀ ⊆
            connectedComponentIn W₀ z := by
          rintro y ⟨hycl, hyW₀⟩
          have hyy : y ∈ connectedComponentIn W₀ y := mem_connectedComponentIn hyW₀
          obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.mp hycl _
            (hW₀open.connectedComponentIn (x := y)) hyy
          have h1 : connectedComponentIn W₀ y = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hv1
          have h2 : connectedComponentIn W₀ z = connectedComponentIn W₀ v :=
            connectedComponentIn_eq hv2
          rw [h2, ← h1]
          exact hyy
        -- the closure of the component must reach the outer part
        have hfront : (closure (connectedComponentIn W₀ z) ∩ W₀ᶜ).Nonempty := by
          rcases (closure (connectedComponentIn W₀ z) ∩ W₀ᶜ).eq_empty_or_nonempty with
            hemp | hne
          · exfalso
            have hclsub : closure (connectedComponentIn W₀ z) ⊆ W₀ := by
              intro y hy
              by_contra hyW₀
              have hmem : y ∈ closure (connectedComponentIn W₀ z) ∩ W₀ᶜ := ⟨hy, hyW₀⟩
              rw [hemp] at hmem
              exact hmem
            have hVclosed : IsClosed (connectedComponentIn W₀ z) :=
              isClosed_of_closure_subset (fun y hy => hcloV ⟨hy, hclsub hy⟩)
            have hVclopen : IsClopen (connectedComponentIn W₀ z) :=
              ⟨hVclosed, hW₀open.connectedComponentIn⟩
            rcases isClopen_iff.mp hVclopen with h | h
            · rw [h] at hzV
              exact hzV
            · have hzfV : zf ∈ connectedComponentIn W₀ z := by
                rw [h]; exact Set.mem_univ zf
              exact hzfW₀ (connectedComponentIn_subset _ _ hzfV)
          · exact hne
        obtain ⟨w, hwcl, hwC⟩ := hfront
        apply Set.mem_sUnion.mpr
        refine ⟨closure (connectedComponentIn W₀ z) ∪ W₀ᶜ, ⟨?_, ?_, ?_⟩,
          Set.mem_union_left _ (subset_closure hzV)⟩
        · rintro y (hy | hy)
          · rw [Set.mem_compl_iff]
            intro hyW
            obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.mp hy W hWopen hyW
            exact hVW v hv2 hv1
          · exact compl_subset_compl.mpr hWW₀ hy
        · exact IsPreconnected.union w hwcl hwC
            isPreconnected_connectedComponentIn.closure hCpre
        · exact Set.mem_union_right _ hzfC
      · exact Set.mem_sUnion.mpr ⟨W₀ᶜ, ⟨compl_subset_compl.mpr hWW₀, hCpre, hzfC⟩, hzW₀⟩
    · rintro z ⟨E, ⟨hEW, -, -⟩, hzE⟩
      exact hEW hzE
  have hWcpre : IsPreconnected Wᶜ := by
    rw [hWcov]
    exact isPreconnected_sUnion zf _ (fun E hE => hE.2.2) (fun E hE => hE.2.1)
  have hAWc : {z : ℂ | R - 1 < ‖z‖} ⊆ Wᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzW
    exact (hFmem δ z).mp (hW₀F (hWW₀ hzW)) (hAU δ hδle1 hz)
  have hWne : W ≠ Set.univ := by
    intro h
    rw [h] at hzfW
    exact hzfW (Set.mem_univ zf)
  have hcompl : ∀ z ∉ W, ¬Bornology.IsBounded (connectedComponentIn Wᶜ z) := by
    intro z hz hbd
    have h1 : Wᶜ ⊆ connectedComponentIn Wᶜ z :=
      hWcpre.subset_connectedComponentIn hz (subset_refl _)
    exact hAunb (hbd.subset (hAWc.trans h1))
  exact ⟨W, hWopen, hKW, hWT,
    simplyConnectedSpace_of_unbounded_components hWopen hWconn hWne hcompl⟩

/-- **Essential loops at a multiple step.** A component step of fiber count
at least two admits a closed loop in the finite chart of its target
together with a Julia point about which the loop has nonzero winding
number: the target's sphere complement is disconnected, a bounded
complementary component provides a Julia-meeting continuum, and the grid
boundary construction yields the essential loop. -/
theorem exists_essential_loop_of_multiple_step {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n) (hinf' : ∞ ∉ fcOrbit f U (n + 1))
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hk : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    ∃ (γ : C(unitInterval, ℂ)) (z₁ : ℂ), γ 0 = γ 1 ∧
      (∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U (n + 1)) ∧
      ((z₁ : ℂ̂)) ∈ JuliaSet f ∧ windingNumber γ z₁ ≠ 0 := by
  classical
  have hd1 : (1 : ℕ) ≤ degreeOfRational f := le_trans one_le_two hd
  -- Step A: a compact preconnected Julia-meeting continuum in the complement
  -- of the target component's finite part.
  have hcontinuum :
      ∃ z₀ : ℂ,
        z₀ ∈ connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} z₀ ∧
        IsCompact (connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} z₀) ∧
        (∃ z ∈ connectedComponentIn {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} z₀,
          ((z : ℂ̂)) ∈ JuliaSet f) := by
    have hVfc : IsFatouComponent f (fcOrbit f U (n + 1)) :=
      isFatouComponent_fcOrbit (n + 1) hf hd1 hU
    -- the black-box separation form of the covering dichotomy
    have hnc : ¬IsConnected ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) :=
      not_isConnected_compl_of_multiple_step hf hd hU n hinf hinf'
        hcrit hk2 hk
    obtain ⟨z₀, hz₀, hbdd⟩ := exists_bounded_component_of_not_isConnected_compl
      hVfc.isOpen hVfc.nonempty hinf' hnc
    set F : Set ℂ := {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} with hFdef
    set C : Set ℂ := connectedComponentIn F z₀ with hCdef
    have hz₀F : z₀ ∈ F := hz₀
    have hz₀C : z₀ ∈ C := mem_connectedComponentIn hz₀F
    have hCsub : C ⊆ F := connectedComponentIn_subset _ _
    -- the complement set is closed in the plane
    have hFclosed : IsClosed F :=
      (hVfc.isOpen.isClosed_compl).preimage OnePoint.continuous_coe
    -- a connected component of a closed set is closed, hence compact
    have hCclosed : IsClosed C := by
      rw [hCdef, connectedComponentIn_eq_image hz₀F]
      exact hFclosed.isClosedEmbedding_subtypeVal.isClosedMap _
        isClosed_connectedComponent
    have hCcpt : IsCompact C := Metric.isCompact_of_isClosed_isBounded hCclosed hbdd
    refine ⟨z₀, hz₀C, hCcpt, ?_⟩
    -- the frontier of the bounded component is nonempty
    haveI : PreconnectedSpace ℂ := ⟨(convex_univ (𝕜 := ℝ) (E := ℂ)).isPreconnected⟩
    have hCne : C.Nonempty := ⟨z₀, hz₀C⟩
    have hfrne : (frontier C).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hopen : IsOpen C := by
        have h1 : C \ interior C = ∅ := by rw [← hCclosed.frontier_eq]; exact hemp
        have h2 : interior C = C :=
          Set.Subset.antisymm interior_subset (Set.diff_eq_empty.mp h1)
        rw [← h2]; exact isOpen_interior
      rcases isClopen_iff.mp ⟨hCclosed, hopen⟩ with h | h
      · exact hCne.ne_empty h
      · have hub : Bornology.IsBounded (Set.univ : Set ℂ) := h ▸ hbdd
        obtain ⟨R, hR⟩ := hub.subset_closedBall 0
        have := hR (Set.mem_univ ((R + 1 : ℝ) : ℂ))
        rw [Metric.mem_closedBall, dist_zero_right] at this
        simp only [Complex.norm_real, Real.norm_eq_abs] at this
        cases abs_le.mp this with
        | intro h1 h2 => nlinarith [abs_nonneg R, le_abs_self R]
    obtain ⟨x, hxfr⟩ := hfrne
    have hxC : x ∈ C := hCclosed.closure_eq ▸ frontier_subset_closure hxfr
    -- a frontier point of the component is a frontier point of the whole
    -- closed complement set (maximality of the component swallows balls)
    have hxniF : x ∉ interior F := by
      intro hxint
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      have hballF : Metric.ball x ε ⊆ F := fun y hy => interior_subset (hball hy)
      have hballC : Metric.ball x ε ⊆ C := by
        rw [hCdef, connectedComponentIn_eq hxC]
        exact (convex_ball x ε).isPreconnected.subset_connectedComponentIn
          (Metric.mem_ball_self hε) hballF
      exact hxfr.2 ((interior_maximal hballC Metric.isOpen_ball) (Metric.mem_ball_self hε))
    have hxfrF : x ∈ frontier F := ⟨subset_closure (hCsub hxC), hxniF⟩
    -- transport the frontier through the coercion into the sphere
    have hFeq : F = ((↑) : ℂ → ℂ̂) ⁻¹' ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) := rfl
    have hfrsub : ((x : ℂ̂)) ∈ frontier ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) := by
      have h1 : closure (((↑) : ℂ → ℂ̂) ⁻¹' ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂)) ⊆
          ((↑) : ℂ → ℂ̂) ⁻¹' closure ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂) :=
        OnePoint.continuous_coe.closure_preimage_subset _
      have h2 : ((↑) : ℂ → ℂ̂) ⁻¹' interior ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂)
          ⊆ interior (((↑) : ℂ → ℂ̂) ⁻¹' ((fcOrbit f U (n + 1))ᶜ : Set ℂ̂)) :=
        preimage_interior_subset_interior_preimage OnePoint.continuous_coe
      rw [hFeq] at hxfrF
      exact ⟨h1 hxfrF.1, fun hint => hxfrF.2 (h2 hint)⟩
    rw [frontier_compl] at hfrsub
    exact ⟨x, hxC, hVfc.frontier_subset_juliaSet hfrsub⟩
  have hessloop : ∀ T : Set ℂ, IsOpen T → ∀ z₀ : ℂ, z₀ ∉ T →
      Bornology.IsBounded (connectedComponentIn Tᶜ z₀) →
      ∃ lam : C(unitInterval, ℂ), lam 0 = lam 1 ∧ (∀ t : unitInterval, lam t ∈ T) ∧
        windingNumber lam z₀ ≠ 0 := by
    intro T hT z₀ hz₀T hbdd
    -- ---------------------------------------------------------------
    -- Inner grid stage: black box exists_gridLoop_winding_ne_zero
    -- (GridPrimitives.lean) — the grid boundary loop of the union of
    -- δ-squares meeting the separated compact piece A.
    -- ---------------------------------------------------------------
    have hgrid : ∀ (A : Set ℂ) (ε : ℝ), 0 < ε → IsCompact A → z₀ ∈ A → A ⊆ Tᶜ →
        (∀ w ∈ Tᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a) →
        ∃ lam : C(unitInterval, ℂ), lam 0 = lam 1 ∧ (∀ t : unitInterval, lam t ∈ T) ∧
          windingNumber lam z₀ ≠ 0 := by
      intro A ε hε hA hzA hAT hsep
      exact exists_gridLoop_winding_ne_zero hT A ε hε hA hzA hAT hsep
    -- ---------------------------------------------------------------
    -- Outer stage (Šura-Bura separation): the bounded component C of the
    -- closed complement F := Tᶜ through z₀ admits a compact piece A ⊇ C
    -- that is relatively clopen in F, hence metrically separated from
    -- F \ A.  Work in the compact subspace K := F ∩ closedBall 0 (R + 1):
    -- there the connected component of z₀ is the intersection of its
    -- clopen neighborhoods, and compactness of the boundary shell yields
    -- a single clopen neighborhood A'' avoiding the shell.
    -- ---------------------------------------------------------------
    set F : Set ℂ := Tᶜ with hFdef
    have hFclosed : IsClosed F := hT.isClosed_compl
    have hz₀F : z₀ ∈ F := hz₀T
    set C : Set ℂ := connectedComponentIn F z₀ with hCdef
    have hz₀C : z₀ ∈ C := mem_connectedComponentIn hz₀F
    have hCsub : C ⊆ F := connectedComponentIn_subset _ _
    obtain ⟨R, hRC⟩ := hbdd.subset_closedBall 0
    set K : Set ℂ := F ∩ Metric.closedBall 0 (R + 1) with hKdef
    have hKcpt : IsCompact K :=
      (isCompact_closedBall 0 (R + 1)).inter_left hFclosed
    have hCK : C ⊆ K := by
      intro x hx
      exact ⟨hCsub hx, Metric.closedBall_subset_closedBall (by linarith) (hRC hx)⟩
    have hz₀K : z₀ ∈ K := hCK hz₀C
    -- the component in K agrees with the component in F
    have hCKeq : connectedComponentIn K z₀ = C := by
      apply Set.Subset.antisymm
      · exact connectedComponentIn_mono _ (Set.inter_subset_left)
      · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hz₀C hCK
    -- the boundary shell of K, compact and missed by C
    set W : Set ℂ := K \ Metric.ball 0 (R + 1) with hWdef
    have hCW : C ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxC hxW
      apply hxW.2
      have hx := hRC hxC
      rw [Metric.mem_closedBall] at hx
      rw [Metric.mem_ball]
      linarith
    -- pass to the compact subspace K
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    set z₀' : K := ⟨z₀, hz₀K⟩ with hz₀'def
    have hccinter := connectedComponent_eq_iInter_isClopen z₀'
    have hWclosed : IsClosed W := hKcpt.isClosed.sdiff Metric.isOpen_ball
    have hW'cpt : IsCompact (Subtype.val ⁻¹' W : Set K) :=
      (hWclosed.preimage continuous_subtype_val).isCompact
    -- the shell misses every point of the component of z₀ in K
    have hdisj : (Subtype.val ⁻¹' W : Set K) ∩
        (⋂ Z : {Z : Set K // IsClopen Z ∧ z₀' ∈ Z}, (Z : Set K)) = ∅ := by
      rw [← hccinter]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxW hxcc
      have hximg : (x : ℂ) ∈ connectedComponentIn K z₀ := by
        rw [connectedComponentIn_eq_image hz₀K]
        exact ⟨x, hxcc, rfl⟩
      rw [hCKeq] at hximg
      have hmem : (x : ℂ) ∈ C ∩ W := ⟨hximg, hxW⟩
      rw [hCW] at hmem
      exact hmem
    -- compactness of the shell extracts a single clopen neighborhood
    obtain ⟨u, hu⟩ := hW'cpt.elim_finite_subfamily_closed
      (fun Z : {Z : Set K // IsClopen Z ∧ z₀' ∈ Z} => (Z : Set K))
      (fun Z => Z.2.1.isClosed) hdisj
    set A'' : Set K := ⋂ Z ∈ u, (Z : Set K) with hA''def
    have hA''clopen : IsClopen A'' := by
      apply Set.Finite.isClopen_biInter u.finite_toSet
      intro Z _
      exact Z.2.1
    have hz₀A'' : z₀' ∈ A'' := by
      rw [hA''def]
      exact Set.mem_biInter fun Z _ => Z.2.2
    -- the piece downstairs: compact, clopen in F, containing C, off the shell
    set A : Set ℂ := Subtype.val '' A'' with hAdef
    have hA''cpt : IsCompact A'' := hA''clopen.isClosed.isCompact
    have hAcpt : IsCompact A := hA''cpt.image continuous_subtype_val
    have hz₀A : z₀ ∈ A := ⟨z₀', hz₀A'', rfl⟩
    have hAK : A ⊆ K := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have hAF : A ⊆ F := fun x hx => (hAK hx).1
    have hAW : A ∩ W = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨y, hyA'', rfl⟩ hxW
      have hmem : y ∈ (Subtype.val ⁻¹' W : Set K) ∩ ⋂ Z ∈ u, (Z : Set K) :=
        ⟨hxW, hyA''⟩
      rw [hu] at hmem
      exact hmem
    -- A is relatively open in F
    obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hA''clopen.isOpen
    have hAeq : A = F ∩ (V ∩ Metric.ball 0 (R + 1)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hyA'', rfl⟩
        refine ⟨y.2.1, ?_, ?_⟩
        · rw [← hVeq] at hyA''
          exact hyA''
        · by_contra hball
          have hmem : (y : ℂ) ∈ A ∩ W := ⟨⟨y, hyA'', rfl⟩, ⟨y.2, hball⟩⟩
          rw [hAW] at hmem
          exact hmem
      · rintro x ⟨hxF, hxV, hxball⟩
        have hxK : x ∈ K := ⟨hxF, Metric.ball_subset_closedBall hxball⟩
        refine ⟨⟨x, hxK⟩, ?_, rfl⟩
        rw [← hVeq]
        exact hxV
    have hFAclosed : IsClosed (F \ A) := by
      rw [hAeq, Set.diff_self_inter]
      exact hFclosed.sdiff (hVopen.inter Metric.isOpen_ball)
    -- metric separation of the compact clopen piece from the rest
    have hdisjAB : Disjoint A (F \ A) := disjoint_sdiff_self_right
    obtain ⟨ε, hε, hthick⟩ := hdisjAB.exists_thickenings hAcpt hFAclosed
    have hsep : ∀ w ∈ Tᶜ, w ∉ A → ∀ a ∈ A, ε ≤ dist w a := by
      intro w hwF hwA a haA
      by_contra hlt
      push Not at hlt
      have hw₁ : w ∈ Metric.thickening ε A :=
        Metric.mem_thickening_iff.mpr ⟨a, haA, hlt⟩
      have hw₂ : w ∈ Metric.thickening ε (F \ A) :=
        Metric.self_subset_thickening hε _ ⟨hwF, hwA⟩
      exact (Set.disjoint_left.mp hthick hw₁) hw₂
    exact hgrid A ε hε hAcpt hz₀A hAF hsep
  obtain ⟨z₁, hz₁mem, hz₁cpt, hz₁J⟩ := hcontinuum
  set F₁ : Set ℂ := {w : ℂ | (w : ℂ̂) ∉ fcOrbit f U (n + 1)} with hF₁def
  set C₁ : Set ℂ := connectedComponentIn F₁ z₁ with hC₁def
  set T₁ : Set ℂ := {w : ℂ | (w : ℂ̂) ∈ fcOrbit f U (n + 1)} with hT₁def
  have hT₁open : IsOpen T₁ :=
    (isFatouComponent_fcOrbit (n + 1) hf hd1 hU).isOpen.preimage OnePoint.continuous_coe
  have hT₁compl : T₁ᶜ = F₁ := by
    ext w; simp [hT₁def, hF₁def]
  have hC₁sub : C₁ ⊆ F₁ := connectedComponentIn_subset _ _
  have hz₁F : z₁ ∈ F₁ := hC₁sub hz₁mem
  have hz₁T : z₁ ∉ T₁ := by
    intro h
    exact hz₁F h
  obtain ⟨lam, hlamcl, hlammem, hlamwind⟩ :=
    hessloop T₁ hT₁open z₁ hz₁T (by rw [hT₁compl]; exact hz₁cpt.isBounded)
  -- the loop trace avoids the continuum
  have hlamC₁ : ∀ t : unitInterval, lam t ∉ C₁ := fun t ht => hC₁sub ht (hlammem t)
  -- winding is constant on the preconnected continuum
  have hwconst : ∀ z ∈ C₁, windingNumber lam z = windingNumber lam z₁ := by
    intro z hz
    exact windingNumber_eq_of_preconnected hlamcl isPreconnected_connectedComponentIn
      hlamC₁ hz hz₁mem
  obtain ⟨zJ, hzJC, hzJJ⟩ := hz₁J
  refine ⟨lam, zJ, hlamcl, ?_, hzJJ, ?_⟩
  · intro t
    have h := hlammem t
    rw [hT₁def] at h
    exact h
  · rw [hwconst zJ hzJC]
    exact hlamwind

/-- Forward images of a chart loop under the iterates, read back in the
finite chart, are continuous chart loops: the orbit components avoid `∞`,
so the readings stay finite. -/
theorem exists_pushed_curve {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)}
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀) (m : ℕ) :
    ∃ Γ : C(unitInterval, ℂ),
      ∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂))) := by
  classical
  have hd1 : (1 : ℕ) ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  -- One-step transport: the forward reading of a chart curve in the next
  -- orbit component is a continuous chart curve (no poles on the trace).
  have hstep : ∀ (Γ : C(unitInterval, ℂ)) (j : ℕ),
      (∀ t : unitInterval, ((Γ t : ℂ̂)) ∈ fcOrbit f U j) →
      ∃ Γ' : C(unitInterval, ℂ),
        (∀ t : unitInterval, Γ' t = chartFiniteMap (f ((Γ t : ℂ̂)))) ∧
        (∀ t : unitInterval, ((Γ' t : ℂ̂)) ∈ fcOrbit f U (j + 1)) := by
    intro Γ j hΓmem
    -- the finite reading of the sphere map on finite points
    have hreadIf : ∀ w : ℂ, r.toSphereMap ((w : ℂ̂))
        = if r.denReduced.eval w = 0 then (∞ : ℂ̂)
          else ((r.numReduced.eval w / r.denReduced.eval w : ℂ) : ℂ̂) := fun _ => rfl
    -- the map sends the trace into the next orbit component
    have hnext : ∀ t : unitInterval, f ((Γ t : ℂ̂)) ∈ fcOrbit f U (j + 1) := by
      intro t
      rw [← fcOrbit_image_eq hf hd1 hU j]
      exact ⟨((Γ t : ℂ̂)), hΓmem t, rfl⟩
    -- no poles on the trace: a pole would map to ∞ in the next component
    have hDΓ : ∀ t : unitInterval, r.denReduced.eval (Γ t) ≠ 0 := by
      intro t h0
      have hval : f ((Γ t : ℂ̂)) = ∞ := by
        rw [hr, hreadIf (Γ t), if_pos h0]
      exact hinf (j + 1) (hval ▸ hnext t)
    -- the image points read finitely as the rational quotient
    have hread : ∀ t : unitInterval,
        f ((Γ t : ℂ̂)) = ((r.numReduced.eval (Γ t) / r.denReduced.eval (Γ t) : ℂ) : ℂ̂) := by
      intro t
      rw [hr, hreadIf (Γ t), if_neg (hDΓ t)]
    -- the pushed curve
    have hcont : Continuous fun t : unitInterval =>
        r.numReduced.eval (Γ t) / r.denReduced.eval (Γ t) :=
      (r.numReduced.continuous.comp Γ.continuous).div
        (r.denReduced.continuous.comp Γ.continuous) hDΓ
    set Γ' : C(unitInterval, ℂ) := ⟨_, hcont⟩
    have hΓ'val : ∀ t : unitInterval, Γ' t = chartFiniteMap (f ((Γ t : ℂ̂))) := by
      intro t
      rw [hread t]
      rfl
    have hΓ'mem : ∀ t : unitInterval, ((Γ' t : ℂ̂)) ∈ fcOrbit f U (j + 1) := by
      intro t
      have h := hnext t
      rw [hread t] at h
      exact h
    exact ⟨Γ', hΓ'val, hΓ'mem⟩
  -- Iterate the one-step transport, carrying orbit membership along.
  have hpush : ∀ m : ℕ, ∃ Γ : C(unitInterval, ℂ),
      (∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂)))) ∧
      (∀ t : unitInterval, ((Γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + m)) ∧
      (∀ t : unitInterval, f^[m] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + m)) := by
    intro m
    induction m with
    | zero =>
        refine ⟨γ, ?_, ?_, ?_⟩
        · intro t; simp [chartFiniteMap]
        · intro t; exact hγmem t
        · intro t; simpa using hγmem t
    | succ m ih =>
        obtain ⟨Γm, hval, hmem, hsph⟩ := ih
        obtain ⟨Γ', hΓ'val, hΓ'mem⟩ := hstep Γm (N₀ + m) hmem
        have hsph' : ∀ t : unitInterval,
            f^[m + 1] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + (m + 1)) := by
          intro t
          have h1 : f^[m + 1] ((γ t : ℂ̂)) = f (f^[m] ((γ t : ℂ̂))) :=
            Function.iterate_succ_apply' f m _
          change f^[m + 1] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + m + 1)
          rw [h1, ← fcOrbit_image_eq hf hd1 hU (N₀ + m)]
          exact ⟨_, hsph t, rfl⟩
        have hcoe : ∀ t : unitInterval,
            ((Γm t : ℂ̂)) = f^[m] ((γ t : ℂ̂)) := by
          intro t
          have hne : f^[m] ((γ t : ℂ̂)) ≠ ∞ := fun h => hinf _ (h ▸ hsph t)
          obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hne
          rw [hval t, ← hw]
          rfl
        refine ⟨Γ', ?_, ?_, hsph'⟩
        · intro t
          rw [hΓ'val t, hcoe t, ← Function.iterate_succ_apply' f m]
        · intro t
          change ((Γ' t : ℂ̂)) ∈ fcOrbit f U (N₀ + m + 1)
          exact hΓ'mem t
  obtain ⟨Γ, hΓval, -, -⟩ := hpush m
  exact ⟨Γ, hΓval⟩

/-- A chart-level null homotopy of a closed curve within a plane set: a
continuous square of loops based at the curve's initial point, starting at
the curve, ending at the constant loop, with image inside the set. -/
def IsChartNullHomotopyIn (γ : C(unitInterval, ℂ)) (T : Set ℂ) : Prop :=
  ∃ H : C(unitInterval × unitInterval, ℂ),
    (∀ s : unitInterval, H (0, s) = γ s) ∧
    (∀ s : unitInterval, H (1, s) = γ 0) ∧
    (∀ t : unitInterval, H (t, 0) = γ 0 ∧ H (t, 1) = γ 0) ∧
    (∀ p : unitInterval × unitInterval, H p ∈ T)

/-- **Null homotopies descend through a component covering step.** If the
forward reading of a chart loop in the next orbit component is chart-null-
homotopic within that component's finite part, so is the loop within its
own component's finite part: the step is a covering map of subtypes, the
homotopy square is simply connected so it lifts, and the lifted square has
constant boundary tracks by uniqueness of path lifts. -/
theorem isChartNullHomotopyIn_of_step {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (hinf : ∞ ∉ fcOrbit f U n) (hinf' : ∞ ∉ fcOrbit f U (n + 1))
    (hcrit : ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {γ Γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U n)
    (hΓ : ∀ t : unitInterval, Γ t = chartFiniteMap (f ((γ t : ℂ̂))))
    (hH : IsChartNullHomotopyIn Γ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (n + 1)}) :
    IsChartNullHomotopyIn γ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U n} := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨r, hr⟩ := id hf
  set S := fcOrbit f U n with hSdef
  set T := fcOrbit f U (n + 1) with hTdef
  have hSfc : IsFatouComponent f S := isFatouComponent_fcOrbit n hf hd1 hU
  have hTfc : IsFatouComponent f T := isFatouComponent_fcOrbit (n + 1) hf hd1 hU
  have himg : f '' S = T := fcOrbit_image_eq hf hd1 hU n
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
  -- ## Stage 1: analytic records mined from the `exists_fiberCount` proof.
  have cf : ∀ t : ℂ, chartFiniteMap ((t : ℂ̂)) = t := fun _ => rfl
  have hread : ∀ t : ℂ, r.toSphereMap ((t : ℂ̂))
      = if r.denReduced.eval t = 0 then (∞ : ℂ̂)
        else ((r.numReduced.eval t / r.denReduced.eval t : ℂ) : ℂ̂) := fun _ => rfl
  have hdenR : r.denReduced ≠ 0 := by
    unfold RationalData.denReduced
    intro hz
    have h1 : r.den = gcd r.num r.den * (r.den / gcd r.num r.den) :=
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right r.den_ne_zero)
        (gcd_dvd_right _ _)).symm
    rw [hz, mul_zero] at h1
    exact r.den_ne_zero h1
  have hrdeg : 2 ≤ r.degree := by
    rw [← degreeOfRational_eq_of_witness f r hr]; exact hd
  have hWr : r.wronskian ≠ 0 := r.wronskian_ne_zero hrdeg
  -- on `S` the reduced denominator does not vanish
  have hden_ne : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → r.denReduced.eval x ≠ 0 := by
    intro x hxS h0
    have hcx := hcrit x hxS
    have hdiff : DifferentiableAt ℂ (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) x := by
      by_contra hnd
      exact hcx (deriv_zero_of_not_differentiableAt hnd)
    have hφx : chartFiniteMap (f ((x : ℂ̂))) = 0 := by
      rw [hr, hread x, if_pos h0]
      rfl
    have hZfin : {t : ℂ | r.denReduced.IsRoot t}.Finite :=
      Polynomial.finite_setOf_isRoot hdenR
    have hclosed : IsClosed ({t : ℂ | r.denReduced.IsRoot t} \ {x}) :=
      (hZfin.subset Set.diff_subset).isClosed
    have hxmem : x ∈ ({t : ℂ | r.denReduced.IsRoot t} \ {x})ᶜ := fun h => h.2 rfl
    have hev_ne : ∀ᶠ t in 𝓝[≠] x, r.denReduced.eval t ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (hclosed.isOpen_compl.mem_nhds hxmem),
        self_mem_nhdsWithin] with t ht htx
      exact fun h0t => ht ⟨h0t, htx⟩
    have h1 : Tendsto (fun t : ℂ => f ((t : ℂ̂))) (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) := by
      have hc : ContinuousAt (fun t : ℂ => f ((t : ℂ̂))) x :=
        (hf.continuous.comp OnePoint.continuous_coe).continuousAt
      have hfx : f ((x : ℂ̂)) = ∞ := by rw [hr, hread x, if_pos h0]
      have h := hc.tendsto
      rw [hfx] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (((0 : ℂ) : ℂ̂))) := by
      have hφt := hdiff.continuousAt.tendsto
      rw [hφx] at hφt
      exact ((OnePoint.continuous_coe.tendsto (0 : ℂ)).comp hφt).mono_left
        nhdsWithin_le_nhds
    have heq : (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        =ᶠ[𝓝[≠] x] fun t : ℂ => f ((t : ℂ̂)) := by
      filter_upwards [hev_ne] with t ht
      rw [hr, hread t, if_neg ht, cf]
    have h1' : Tendsto (fun t : ℂ => ((chartFiniteMap (f ((t : ℂ̂))) : ℂ) : ℂ̂))
        (𝓝[≠] x) (𝓝 (∞ : ℂ̂)) :=
      Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) h1
    exact OnePoint.coe_ne_infty (0 : ℂ) (tendsto_nhds_unique h2 h1')
  -- values on `S` are finite
  have hSfin : ∀ u ∈ S, f u ≠ ∞ := by
    intro u huS
    have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
    rw [hr, hread x, if_neg (hden_ne x huS)]
    exact OnePoint.coe_ne_infty _
  have hTfin : ∀ w ∈ T, ∃ y : ℂ, w = ((y : ℂ̂)) := by
    intro w hwT
    rw [← himg] at hwT
    obtain ⟨u, huS, rfl⟩ := hwT
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp (hSfin u huS)
    exact ⟨y, hy.symm⟩
  -- fibers over finite points are finite
  have hfib_fin : ∀ y : ℂ, (f ⁻¹' {((y : ℂ̂))} ∩ S).Finite := by
    intro y
    have hq : r.numReduced - Polynomial.C y * r.denReduced ≠ 0 := by
      intro h0
      apply hWr
      have hnum : r.numReduced = Polynomial.C y * r.denReduced := sub_eq_zero.mp h0
      unfold RationalData.wronskian
      rw [hnum, Polynomial.derivative_C_mul]
      ring
    have hsub : f ⁻¹' {((y : ℂ̂))} ∩ S ⊆ (fun x : ℂ => ((x : ℂ̂))) ''
        {x : ℂ | (r.numReduced - Polynomial.C y * r.denReduced).IsRoot x} := by
      rintro u ⟨hufy, huS⟩
      have hune : u ≠ ∞ := fun h => hinf (h ▸ huS)
      obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hune
      have hden := hden_ne x huS
      have hfx : f ((x : ℂ̂)) = ((y : ℂ̂)) := hufy
      rw [hr, hread x, if_neg hden] at hfx
      have hdiv : r.numReduced.eval x / r.denReduced.eval x = y :=
        OnePoint.coe_eq_coe.mp hfx
      rw [div_eq_iff hden] at hdiv
      refine ⟨x, ?_, rfl⟩
      change (r.numReduced - Polynomial.C y * r.denReduced).eval x = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hdiv, sub_self]
    exact ((Polynomial.finite_setOf_isRoot hq).image _).subset hsub
  -- local injectivity near each finite non-critical point
  have hloc : ∀ x : ℂ, ((x : ℂ̂) ∈ S) → ∃ Wc : Set ℂ, IsOpen Wc ∧ x ∈ Wc ∧
      ∀ t₁ ∈ Wc, ∀ t₂ ∈ Wc, f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) → t₁ = t₂ := by
    intro x hxS
    have hcx := hcrit x hxS
    have hden := hden_ne x hxS
    have hev : (fun t : ℂ => r.numReduced.eval t / r.denReduced.eval t)
        =ᶠ[𝓝 x] fun t : ℂ => chartFiniteMap (f ((t : ℂ̂))) := by
      filter_upwards [r.denReduced.continuous.continuousAt.eventually_ne hden] with t ht
      rw [hr, hread t, if_neg ht, cf]
    obtain ⟨D, hstrict⟩ : ∃ D : ℂ,
        HasStrictDerivAt (fun t : ℂ => chartFiniteMap (f ((t : ℂ̂)))) D x :=
      ⟨_, ((r.numReduced.hasStrictDerivAt x).div
        (r.denReduced.hasStrictDerivAt x) hden).congr_of_eventuallyEq hev⟩
    have hD : D ≠ 0 := hstrict.hasDerivAt.deriv ▸ hcx
    obtain ⟨Wc, hWsub, hWopen, hxW⟩ :=
      mem_nhds_iff.mp (hstrict.eventually_left_inverse hD)
    refine ⟨Wc, hWopen, hxW, ?_⟩
    intro t₁ ht₁ t₂ ht₂ hft
    have h₁ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₁ : ℂ̂)))) = t₁ := hWsub ht₁
    have h₂ : HasStrictDerivAt.localInverse _ _ _ hstrict hD
        (chartFiniteMap (f ((t₂ : ℂ̂)))) = t₂ := hWsub ht₂
    rw [← h₁, hft, h₂]
  -- ## Stage 2: the packaged component step between the two subtypes.
  have hmapsto : ∀ u : ℂ̂, u ∈ S → f u ∈ T := by
    intro u hu
    rw [← himg]
    exact ⟨u, hu, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ↥S → ↥T,
      F = fun u => ⟨f u.1, hmapsto u.1 u.2⟩ := ⟨_, rfl⟩
  have hFval : ∀ u : ↥S, ((F u : ℂ̂)) = f u.1 := by
    intro u
    rw [hFdef]
  have hFcont : Continuous F := by
    rw [hFdef]
    exact Continuous.subtype_mk (hf.continuous.comp continuous_subtype_val) _
  -- the packaged map is open
  have hFopen : IsOpenMap F := by
    intro V hV
    obtain ⟨D, hD, hDV⟩ := isOpen_induced_iff.mp hV
    have himgV : F '' V = Subtype.val ⁻¹' (f '' (S ∩ D)) := by
      ext w
      constructor
      · rintro ⟨u, huV, rfl⟩
        have huD : u.1 ∈ D := by
          rw [← hDV] at huV
          exact huV
        exact ⟨u.1, ⟨u.2, huD⟩, (hFval u).symm⟩
      · rintro ⟨v, ⟨hvS, hvD⟩, hfv⟩
        refine ⟨⟨v, hvS⟩, ?_, ?_⟩
        · rw [← hDV]
          exact hvD
        · apply Subtype.ext
          rw [hFval]
          exact hfv
    rw [himgV]
    exact (hfo _ (hSfc.isOpen.inter hD)).preimage continuous_subtype_val
  -- the packaged map is closed (properness via the Julia frontier)
  have hFclosed : IsClosedMap F := by
    intro C hC
    obtain ⟨D, hD, hDC⟩ := isClosed_induced_iff.mp hC
    have hkey : F '' C = Subtype.val ⁻¹' (closure (f '' (S ∩ D))) := by
      ext w
      constructor
      · rintro ⟨u, huC, rfl⟩
        have huD : u.1 ∈ D := by
          rw [← hDC] at huC
          exact huC
        exact subset_closure ⟨u.1, ⟨u.2, huD⟩, (hFval u).symm⟩
      · intro hw
        have hcl : closure (f '' (S ∩ D)) ⊆ f '' closure (S ∩ D) := by
          apply closure_minimal (Set.image_mono subset_closure)
          exact (isClosed_closure.isCompact.image hf.continuous).isClosed
        obtain ⟨x, hxcl, hfx⟩ := hcl hw
        have hxSD : x ∈ closure S ∩ D := by
          have h1 := closure_inter_subset_inter_closure S D hxcl
          rwa [hD.closure_eq] at h1
        by_cases hxS : x ∈ S
        · refine ⟨⟨x, hxS⟩, ?_, ?_⟩
          · rw [← hDC]
            exact hxSD.2
          · apply Subtype.ext
            rw [hFval]
            exact hfx
        · exfalso
          have hxfr : x ∈ frontier S := by
            rw [hSfc.isOpen.frontier_eq]
            exact ⟨hxSD.1, hxS⟩
          have hxJ : x ∈ JuliaSet f := hSfc.frontier_subset_juliaSet hxfr
          rw [← juliaSet_preimage_eq_of_isRational hf hd1] at hxJ
          have hfxJ : f x ∈ JuliaSet f := hxJ
          rw [hfx] at hfxJ
          exact hfxJ (hTfc.subset_fatouSet w.2)
    rw [hkey]
    exact IsClosed.preimage continuous_subtype_val isClosed_closure
  -- fibers of the packaged map are finite
  have hFfib : ∀ w : ↥T, (F ⁻¹' {w}).Finite := by
    intro w
    obtain ⟨y, hy⟩ := hTfin w.1 w.2
    have hpre : F ⁻¹' {w} = Subtype.val ⁻¹' (f ⁻¹' {((y : ℂ̂))} ∩ S) := by
      ext u
      constructor
      · intro hu
        have h1 : F u = w := hu
        have h2 : f u.1 = ((y : ℂ̂)) := by
          have h3 := congrArg Subtype.val h1
          rw [hFval u] at h3
          rw [h3]
          exact hy
        exact ⟨h2, u.2⟩
      · intro hu
        apply Subtype.ext
        rw [hFval u, hy]
        exact hu.1
    rw [hpre]
    exact Set.Finite.preimage Subtype.coe_injective.injOn (hfib_fin y)
  -- local homeomorphism records for the packaged map
  haveI hSne : Nonempty ↥S := hSfc.nonempty.to_subtype
  have hFloc : ∀ e : ↥S, ∃ φ : OpenPartialHomeomorph ↥S ↥T,
      e ∈ φ.source ∧ ⇑φ = F := by
    intro e
    have hene : (e : ℂ̂) ≠ ∞ := fun h => hinf (h ▸ e.2)
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp hene
    have hxS : ((x : ℂ̂)) ∈ S := by
      rw [hx]
      exact e.2
    obtain ⟨Wc, hWopen, hxW, hWinj⟩ := hloc x hxS
    set src : Set ↥S := Subtype.val ⁻¹' ((fun t : ℂ => ((t : ℂ̂))) '' Wc) with hsrc
    have hsrcopen : IsOpen src :=
      (OnePoint.isOpenEmbedding_coe.isOpenMap _ hWopen).preimage
        continuous_subtype_val
    have hesrc : e ∈ src := ⟨x, hxW, hx⟩
    have hinjF : Set.InjOn F src := by
      rintro u₁ hu₁ u₂ hu₂ h12
      obtain ⟨t₁, ht₁, htv₁⟩ := hu₁
      obtain ⟨t₂, ht₂, htv₂⟩ := hu₂
      have hf12 : f ((t₁ : ℂ̂)) = f ((t₂ : ℂ̂)) := by
        have htv₁' : ((t₁ : ℂ̂)) = (u₁ : ℂ̂) := htv₁
        have htv₂' : ((t₂ : ℂ̂)) = (u₂ : ℂ̂) := htv₂
        rw [htv₁', htv₂']
        have h3 := congrArg Subtype.val h12
        rw [hFval, hFval] at h3
        exact h3
      have ht12 : t₁ = t₂ := hWinj t₁ ht₁ t₂ ht₂ hf12
      apply Subtype.ext
      rw [← htv₁, ← htv₂, ht12]
    refine ⟨OpenPartialHomeomorph.ofContinuousOpen
      (hinjF.toPartialEquiv F src) ?_ ?_ ?_, ?_, ?_⟩
    · exact hFcont.continuousOn
    · exact hFopen
    · exact hsrcopen
    · exact hesrc
    · rfl
  -- ## Stage 3: the packaged map is a covering map.
  have hcovOn : IsCoveringMapOn F Set.univ :=
    hFclosed.isCoveringMapOn_of_openPartialHomeomorph
      (fun w _ => hFfib w) (fun e _ => hFloc e)
  have hcov : IsCoveringMap F := isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  -- ## Stage 4: homotopy data and the base loop, packaged on the subtypes.
  obtain ⟨H, hHs0, hHs1, hHtr, hHmem⟩ :
      ∃ H : C(unitInterval × unitInterval, ℂ),
        (∀ s : unitInterval, H (0, s) = Γ s) ∧
        (∀ s : unitInterval, H (1, s) = Γ 0) ∧
        (∀ t : unitInterval, H (t, 0) = Γ 0 ∧ H (t, 1) = Γ 0) ∧
        (∀ p : unitInterval × unitInterval, H p ∈ {w : ℂ | ((w : ℂ̂)) ∈ T}) := hH
  obtain ⟨Hs, hHsdef⟩ : ∃ Hs : C(unitInterval × unitInterval, ↥T),
      Hs = ⟨fun p => ⟨((H p : ℂ̂)), hHmem p⟩,
        Continuous.subtype_mk (OnePoint.continuous_coe.comp H.continuous) _⟩ := ⟨_, rfl⟩
  have hHsval : ∀ p : unitInterval × unitInterval, ((Hs p : ℂ̂)) = ((H p : ℂ̂)) := by
    intro p
    rw [hHsdef]
    rfl
  obtain ⟨γs, hγsdef⟩ : ∃ γs : C(unitInterval, ↥S),
      γs = ⟨fun t => ⟨((γ t : ℂ̂)), hγmem t⟩,
        Continuous.subtype_mk (OnePoint.continuous_coe.comp γ.continuous) _⟩ := ⟨_, rfl⟩
  have hγsval : ∀ t : unitInterval, ((γs t : ℂ̂)) = ((γ t : ℂ̂)) := by
    intro t
    rw [hγsdef]
    rfl
  -- chart readings of points of the two components coerce back to themselves
  have hScoe : ∀ w : ℂ̂, w ∈ S → ((chartFiniteMap w : ℂ) : ℂ̂) = w := by
    intro w hw
    have hne : w ≠ ∞ := fun h => hinf (h ▸ hw)
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hne
    rfl
  have hTcoe : ∀ w : ℂ̂, w ∈ T → ((chartFiniteMap w : ℂ) : ℂ̂) = w := by
    intro w hw
    have hne : w ≠ ∞ := fun h => hinf' (h ▸ hw)
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hne
    rfl
  -- the forward values of the base loop land in the target component
  have hnext : ∀ t : unitInterval, f ((γ t : ℂ̂)) ∈ T := by
    intro t
    rw [← himg]
    exact ⟨_, hγmem t, rfl⟩
  have hΓsph : ∀ t : unitInterval, ((Γ t : ℂ̂)) = f ((γ t : ℂ̂)) := by
    intro t
    rw [hΓ t]
    exact hTcoe _ (hnext t)
  -- the subtype homotopy starts over the packaged image of the base loop
  have hcompat : ∀ s : unitInterval, Hs (0, s) = F (γs s) := by
    intro s
    apply Subtype.ext
    rw [hHsval (0, s), hFval, hγsval s, hHs0 s, hΓsph s]
  -- ## Stage 5: lift the homotopy square and pin its boundary tracks.
  obtain ⟨Ht, hHtdef⟩ : ∃ Ht : C(unitInterval × unitInterval, ↥S),
      Ht = hcov.liftHomotopy Hs γs hcompat := ⟨_, rfl⟩
  have hlifts : ∀ p : unitInterval × unitInterval, F (Ht p) = Hs p := by
    intro p
    rw [hHtdef]
    exact congrFun (hcov.liftHomotopy_lifts Hs γs hcompat) p
  have hzero : ∀ s : unitInterval, Ht (0, s) = γs s := by
    intro s
    rw [hHtdef]
    exact hcov.liftHomotopy_zero Hs γs hcompat s
  have hγscl : γs 1 = γs 0 := by
    apply Subtype.ext
    rw [hγsval 1, hγsval 0, hγcl]
  -- the two vertical tracks lift the constant loop at the base value,
  -- start at the lifted basepoint, hence are constant by unique lifting
  have hside0 : ∀ t : unitInterval, Ht (t, 0) = γs 0 := by
    have hkey : (fun t : unitInterval => Ht (t, 0)) = fun _ : unitInterval => γs 0 := by
      refine hcov.eq_of_comp_eq ?_ continuous_const ?_ 0 (hzero 0)
      · exact Ht.continuous.comp (continuous_id.prodMk continuous_const)
      · funext t
        change F (Ht (t, 0)) = F (γs 0)
        rw [hlifts (t, 0)]
        apply Subtype.ext
        rw [hHsval (t, 0), hFval, hγsval 0, (hHtr t).1, hΓsph 0]
    intro t
    exact congrFun hkey t
  have hside1 : ∀ t : unitInterval, Ht (t, 1) = γs 0 := by
    have hkey : (fun t : unitInterval => Ht (t, 1)) = fun _ : unitInterval => γs 0 := by
      refine hcov.eq_of_comp_eq ?_ continuous_const ?_ 0 ((hzero 1).trans hγscl)
      · exact Ht.continuous.comp (continuous_id.prodMk continuous_const)
      · funext t
        change F (Ht (t, 1)) = F (γs 0)
        rw [hlifts (t, 1)]
        apply Subtype.ext
        rw [hHsval (t, 1), hFval, hγsval 0, (hHtr t).2, hΓsph 0]
    intro t
    exact congrFun hkey t
  -- the top edge lifts the constant loop and starts at the pinned corner
  have htop : ∀ s : unitInterval, Ht (1, s) = γs 0 := by
    have hkey : (fun s : unitInterval => Ht (1, s)) = fun _ : unitInterval => γs 0 := by
      refine hcov.eq_of_comp_eq ?_ continuous_const ?_ 0 (hside0 1)
      · exact Ht.continuous.comp (continuous_const.prodMk continuous_id)
      · funext s
        change F (Ht (1, s)) = F (γs 0)
        rw [hlifts (1, s)]
        apply Subtype.ext
        rw [hHsval (1, s), hFval, hγsval 0, hHs1 s, hΓsph 0]
    intro s
    exact congrFun hkey s
  -- ## Stage 6: read the lifted square back through the finite chart.
  have hchart : ∀ w : ℂ̂, w ≠ ∞ → ContinuousAt chartFiniteMap w := by
    intro w hw
    obtain ⟨y, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hw
    rw [OnePoint.continuousAt_coe]
    exact continuousAt_id
  have hHdcont : Continuous fun p : unitInterval × unitInterval =>
      chartFiniteMap ((Ht p : ℂ̂)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have h1 : ContinuousAt (fun q : unitInterval × unitInterval => ((Ht q : ℂ̂))) p :=
      (continuous_subtype_val.comp Ht.continuous).continuousAt
    have h2 : ((Ht p : ℂ̂)) ≠ ∞ := fun h => hinf (h ▸ (Ht p).2)
    change ContinuousAt (chartFiniteMap ∘ fun q : unitInterval × unitInterval => ((Ht q : ℂ̂))) p
    exact ContinuousAt.comp (x := p)
      (f := fun q : unitInterval × unitInterval => ((Ht q : ℂ̂)))
      (g := chartFiniteMap) (hchart _ h2) h1
  change ∃ Hd : C(unitInterval × unitInterval, ℂ),
      (∀ s : unitInterval, Hd (0, s) = γ s) ∧
      (∀ s : unitInterval, Hd (1, s) = γ 0) ∧
      (∀ t : unitInterval, Hd (t, 0) = γ 0 ∧ Hd (t, 1) = γ 0) ∧
      (∀ p : unitInterval × unitInterval, Hd p ∈ {w : ℂ | ((w : ℂ̂)) ∈ S})
  refine ⟨⟨fun p => chartFiniteMap ((Ht p : ℂ̂)), hHdcont⟩, ?_, ?_, ?_, ?_⟩
  · intro s
    change chartFiniteMap ((Ht (0, s) : ℂ̂)) = γ s
    rw [hzero s, hγsval s]
    exact cf _
  · intro s
    change chartFiniteMap ((Ht (1, s) : ℂ̂)) = γ 0
    rw [htop s, hγsval 0]
    exact cf _
  · intro t
    constructor
    · change chartFiniteMap ((Ht (t, 0) : ℂ̂)) = γ 0
      rw [hside0 t, hγsval 0]
      exact cf _
    · change chartFiniteMap ((Ht (t, 1) : ℂ̂)) = γ 0
      rw [hside1 t, hγsval 0]
      exact cf _
  · intro p
    change (((chartFiniteMap ((Ht p : ℂ̂))) : ℂ̂)) ∈ S
    rw [hScoe _ (Ht p).2]
    exact (Ht p).2

/-- **Loops whose fills avoid the Julia set are winding-trivial about it.**
If at some forward time every Julia point lies in the `∞`-component of the
complement of the pushed curve's sphere trace, then the pushed curve's fill
lies in its Fatou component; a simply connected neighborhood of the fill
inside the component null-homotopes the pushed curve, the null homotopy
descends through the covering steps, and homotopy invariance kills the
winding of the original loop about every Julia point. -/
theorem windingNumber_eq_zero_of_fill_avoids_julia {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀)
    {m : ℕ} {Γ : C(unitInterval, ℂ)}
    (hΓ : ∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂))))
    (hfill : ∀ w : ℂ̂, w ∈ JuliaSet f →
      w ∈ connectedComponentIn ((Set.range fun t => ((Γ t : ℂ̂)))ᶜ) ∞) :
    ∀ z : ℂ, ((z : ℂ̂)) ∈ JuliaSet f → windingNumber γ z = 0 := by
  classical
  -- ## Stage 0: shared helpers
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hOpenMap : IsOpenMap f := hf.isOpenMap (fun c => hf.ne_const hd1 c)
  have hjf : ∀ x : ℂ̂, x ∈ FatouSet f → x ∈ JuliaSet f → False := by
    intro x h1 h2
    rw [← compl_fatouSet] at h2
    exact h2 h1
  have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
    intro p hp
    cases p with
    | infty => exact absurd rfl hp
    | coe x => rfl
  have hfatou_iter : ∀ (n : ℕ) (x : ℂ̂), x ∈ FatouSet f →
      f^[n] x ∈ FatouSet f := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hOpenMap (ih x hx)
  have hfwd : ∀ (n : ℕ) (x : ℂ̂), x ∈ fcOrbit f U N₀ →
      f^[n] x ∈ fcOrbit f U (N₀ + n) := by
    intro n x hx
    have hVfc' : IsFatouComponent f (fcOrbit f U N₀) :=
      isFatouComponent_fcOrbit N₀ hf hd1 hU
    rw [fcOrbit_add N₀ n hf hd1 hU]
    exact Set.mem_biUnion hx
      (mem_connectedComponentIn (hfatou_iter n x (hVfc'.subset_fatouSet hx)))
  -- ## Stage 1: the sphere trace of the pushed curve and the `∞`-component
  set Rsph : Set ℂ̂ := Set.range fun t => ((Γ t : ℂ̂)) with hRsphdef
  have hRcomp : IsCompact Rsph :=
    isCompact_range (OnePoint.continuous_coe.comp Γ.continuous)
  have hRc_open : IsOpen (Rsphᶜ) := hRcomp.isClosed.isOpen_compl
  have hinfR : ∞ ∈ (Rsphᶜ) := by
    intro h
    obtain ⟨t, ht⟩ := h
    exact OnePoint.coe_ne_infty (Γ t) ht
  set Uinf : Set ℂ̂ := connectedComponentIn (Rsphᶜ) ∞ with hUinfdef
  have hUinf_open : IsOpen Uinf := hRc_open.connectedComponentIn
  have hUinf_sub : Uinf ⊆ (Rsphᶜ) := connectedComponentIn_subset _ _
  have hinfUinf : ∞ ∈ Uinf := mem_connectedComponentIn hinfR
  -- ## Stage 2: the fill `K` — the chart points not in the `∞`-component
  set K : Set ℂ := {z : ℂ | ((z : ℂ̂)) ∉ Uinf} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact (hUinf_open.isClosed_compl).preimage OnePoint.continuous_coe
  have htrK : ∀ t : unitInterval, Γ t ∈ K := by
    intro t
    change ((Γ t : ℂ̂)) ∉ Uinf
    intro hmem
    exact hUinf_sub hmem ⟨t, rfl⟩
  have hKne : K.Nonempty := ⟨Γ 0, htrK 0⟩
  -- ### boundedness: a punctured neighborhood of `∞` lies in `Uinf`
  obtain ⟨R₀, hR₀⟩ := (isCompact_range Γ.continuous).isBounded.subset_closedBall 0
  have hρpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have houter : IsPreconnected {w : ℂ | max R₀ 1 < ‖w‖} := by
    have himg : {w : ℂ | max R₀ 1 < ‖w‖} =
        (fun p : ℝ × ℝ => ((p.1 : ℂ)) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
          (Set.Ioi (max R₀ 1) ×ˢ Set.univ) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
        Set.mem_univ, and_true, Prod.exists]
      constructor
      · intro hw
        exact ⟨‖w‖, Complex.arg w, hw, Complex.norm_mul_exp_arg_mul_I w⟩
      · rintro ⟨t, θ, ht, rfl⟩
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (lt_trans hρpos ht)]
        exact ht
    rw [himg]
    exact (isPreconnected_Ioi.prod isPreconnected_univ).image _
      ((Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_snd).mul
            continuous_const))).continuousOn
  have hclinf : (∞ : ℂ̂) ∈ closure
      ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖}) := by
    rw [mem_closure_iff_nhds_basis (OnePoint.hasBasis_nhds_infty (X := ℂ))]
    rintro T ⟨hTcl, hTcp⟩
    obtain ⟨R₁, hR₁⟩ := hTcp.isBounded.subset_closedBall 0
    have hbig : max R₀ 1 < ‖((max (max R₀ 1) R₁ + 1 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [le_max_left (max R₀ 1) R₁, hρpos])]
      linarith [le_max_left (max R₀ 1) R₁]
    refine ⟨((((max (max R₀ 1) R₁ + 1 : ℝ) : ℂ)) : ℂ̂),
      ⟨((max (max R₀ 1) R₁ + 1 : ℝ) : ℂ), hbig, rfl⟩, Or.inl ⟨_, fun hmem => ?_, rfl⟩⟩
    have h2 := hR₁ hmem
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (by linarith [le_max_left (max R₀ 1) R₁, hρpos])] at h2
    linarith [le_max_right (max R₀ 1) R₁]
  have hSpre : IsPreconnected
      ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖} ∪ {∞}) := by
    refine (houter.image _ OnePoint.continuous_coe.continuousOn).subset_closure
      Set.subset_union_left (Set.union_subset subset_closure ?_)
    exact Set.singleton_subset_iff.mpr hclinf
  have hSsub : ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖} ∪ {∞}) ⊆
      (Rsphᶜ) := by
    rintro x (⟨w, hw, rfl⟩ | hx)
    · intro hmem
      obtain ⟨t, ht⟩ := hmem
      have hwt : Γ t = w := OnePoint.coe_eq_coe.mp ht
      have h1 : ‖Γ t‖ ≤ R₀ := by
        have := hR₀ (Set.mem_range_self t)
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      rw [hwt] at h1
      simp only [Set.mem_setOf_eq] at hw
      have h2 : R₀ ≤ max R₀ 1 := le_max_left _ _
      linarith
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hinfR
  have hSU : ((fun w : ℂ => ((w : ℂ̂))) '' {w : ℂ | max R₀ 1 < ‖w‖} ∪ {∞}) ⊆
      Uinf :=
    hSpre.subset_connectedComponentIn (Set.mem_union_right _ rfl) hSsub
  have hKball : K ⊆ Metric.closedBall 0 (max R₀ 1) := by
    intro w hw
    by_contra hout
    have h1 : max R₀ 1 < ‖w‖ := by
      rwa [Metric.mem_closedBall, dist_zero_right, not_le] at hout
    exact hw (hSU (Set.mem_union_left _ ⟨w, h1, rfl⟩))
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) (max R₀ 1)).of_isClosed_subset hKclosed hKball
  -- ## Stage 3: fullness — complementary components of `K` are unbounded
  have hUinf_conn : IsConnected Uinf := isConnected_connectedComponentIn_iff.mpr hinfR
  have hUinf_path : IsPathConnected Uinf :=
    (hUinf_open.isConnected_iff_isPathConnected).mp hUinf_conn
  have hKfull : ∀ w ∉ K, ¬Bornology.IsBounded (connectedComponentIn (Kᶜ) w) := by
    intro w hwK hbdd
    have hwU : ((w : ℂ̂)) ∈ Uinf := by
      by_contra h
      exact hwK h
    obtain ⟨p, hp⟩ := hUinf_path.joinedIn _ hwU _ hinfUinf
    -- first hitting time of `∞` along the path
    set S : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ p.extend s = ∞} with hSdef
    have hScl : IsClosed S := by
      have hSeq : S = Set.Icc (0 : ℝ) 1 ∩ p.extend ⁻¹' {∞} := rfl
      rw [hSeq]
      exact isClosed_Icc.inter (isClosed_singleton.preimage p.continuous_extend)
    have hSne : S.Nonempty := ⟨1, ⟨zero_le_one, le_refl 1⟩, p.extend_one⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    have ht₀S : sInf S ∈ S := hScl.csInf_mem hSne hSbdd
    have ht₀pos : 0 < sInf S := by
      rcases lt_or_eq_of_le ht₀S.1.1 with h | h
      · exact h
      · exfalso
        have h0 : p.extend (sInf S) = ∞ := ht₀S.2
        rw [← h, p.extend_zero] at h0
        exact OnePoint.coe_ne_infty w h0
    have ht₀le1 : sInf S ≤ 1 := ht₀S.1.2
    -- the arc before the hitting time stays in `Uinf` and off `∞`
    have harc : ∀ s ∈ Set.Ico (0 : ℝ) (sInf S),
        p.extend s ∈ Uinf ∧ p.extend s ≠ ∞ := by
      intro s hs
      have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_trans (le_of_lt hs.2) ht₀le1⟩
      refine ⟨?_, ?_⟩
      · rw [p.extend_apply hs01]
        exact hp _
      · intro hinfty
        exact absurd (csInf_le hSbdd ⟨hs01, hinfty⟩) (not_le.mpr hs.2)
    have himgarc : IsPreconnected (p.extend '' Set.Ico 0 (sInf S)) :=
      isPreconnected_Ico.image _ p.continuous_extend.continuousOn
    have harcsub : p.extend '' Set.Ico 0 (sInf S) ⊆
        Set.range (fun w : ℂ => ((w : ℂ̂))) := by
      rintro x ⟨s, hs, rfl⟩
      cases hx : p.extend s with
      | infty => exact absurd hx (harc s hs).2
      | coe y => exact ⟨y, rfl⟩
    -- its chart reading is connected, meets `w`, and avoids `K`
    have hApre : IsPreconnected
        ((fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S))) := by
      have h1 : (fun w : ℂ => ((w : ℂ̂))) ''
          ((fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S))) =
          p.extend '' Set.Ico 0 (sInf S) :=
        Set.image_preimage_eq_of_subset harcsub
      refine (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp ?_
      rw [h1]
      exact himgarc
    have hwA : w ∈ (fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S)) :=
      ⟨0, ⟨le_refl 0, ht₀pos⟩, p.extend_zero⟩
    have hAsub : (fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S)) ⊆
        (Kᶜ) := by
      rintro x ⟨s, hs, hx⟩
      simp only [Set.mem_compl_iff]
      intro hxK
      have h1 := (harc s hs).1
      rw [hx] at h1
      exact hxK h1
    have hAC : (fun w : ℂ => ((w : ℂ̂))) ⁻¹' (p.extend '' Set.Ico 0 (sInf S)) ⊆
        connectedComponentIn (Kᶜ) w :=
      hApre.subset_connectedComponentIn hwA hAsub
    -- the arc escapes every closed ball, contradicting boundedness
    obtain ⟨M, hM⟩ := hbdd.subset_closedBall 0
    have himg_sub : p.extend '' Set.Ico 0 (sInf S) ⊆
        (fun w : ℂ => ((w : ℂ̂))) '' Metric.closedBall 0 M := by
      intro x hx
      obtain ⟨y, hy⟩ := harcsub hx
      refine ⟨y, ?_, hy⟩
      apply hM
      apply hAC
      change ((y : ℂ̂)) ∈ p.extend '' Set.Ico 0 (sInf S)
      rw [← hy] at hx
      exact hx
    have hinfcl : (∞ : ℂ̂) ∈ closure (p.extend '' Set.Ico 0 (sInf S)) := by
      have h1 : sInf S ∈ closure (Set.Ico (0 : ℝ) (sInf S)) := by
        rw [closure_Ico (ne_of_lt ht₀pos)]
        exact ⟨le_of_lt ht₀pos, le_refl _⟩
      have h2 : p.extend (sInf S) ∈ closure (p.extend '' Set.Ico 0 (sInf S)) :=
        image_closure_subset_closure_image p.continuous_extend ⟨sInf S, h1, rfl⟩
      rwa [ht₀S.2] at h2
    have hclosedimg : IsClosed ((fun w : ℂ => ((w : ℂ̂))) '' Metric.closedBall 0 M) :=
      ((isCompact_closedBall (0 : ℂ) M).image OnePoint.continuous_coe).isClosed
    have hbad : (∞ : ℂ̂) ∈ (fun w : ℂ => ((w : ℂ̂))) '' Metric.closedBall 0 M :=
      hclosedimg.closure_subset ((closure_mono himg_sub) hinfcl)
    exact OnePoint.infty_notMem_image_coe hbad
  -- ## Stage 4: connectedness of `K`
  have hKpre : IsPreconnected K := by
    have main : ∀ u v : Set ℂ, IsOpen u → IsOpen v → K ⊆ u ∪ v →
        K ∩ (u ∩ v) = ∅ → (∀ t : unitInterval, Γ t ∈ u) → K ⊆ u := by
      intro u v hu hv hKuv hdisj htr
      by_contra hKu
      obtain ⟨w₀, hw₀K, hw₀u⟩ := Set.not_subset.mp hKu
      have hBclosed : IsClosed (K \ u) := hKclosed.sdiff hu
      have hBopen : IsOpen (K \ u) := by
        rw [isOpen_iff_forall_mem_open]
        intro b hb
        have hbK : b ∈ K := hb.1
        have hbu : b ∉ u := hb.2
        -- `b` is off the trace, so its sphere component of the complement
        -- of the trace is not the `∞`-component
        have hbR : ((b : ℂ̂)) ∉ Rsph := by
          intro hmem
          obtain ⟨t, ht⟩ := hmem
          have hΓtb : Γ t = b := OnePoint.coe_eq_coe.mp ht
          exact hbu (hΓtb ▸ htr t)
        have hObmem : ((b : ℂ̂)) ∈ connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) :=
          mem_connectedComponentIn hbR
        have hOUinf : ∀ x ∈ connectedComponentIn (Rsphᶜ) ((b : ℂ̂)), x ∉ Uinf := by
          intro x hxO hxU
          have h1 : connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) =
              connectedComponentIn (Rsphᶜ) x :=
            connectedComponentIn_eq hxO
          have h2 : Uinf = connectedComponentIn (Rsphᶜ) x :=
            connectedComponentIn_eq hxU
          have hbU : ((b : ℂ̂)) ∈ Uinf := by
            rw [h2, ← h1]
            exact hObmem
          exact hbK hbU
        have hOinf : (∞ : ℂ̂) ∉ connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) :=
          fun h => hOUinf ∞ h hinfUinf
        have hO'open : IsOpen ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) :=
          (hRc_open.connectedComponentIn).preimage OnePoint.continuous_coe
        have hbO' : b ∈ (fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) := hObmem
        have hO'K : ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) ⊆ K :=
          fun x hx => hOUinf _ hx
        have hOsubrange : connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) ⊆
            Set.range (fun w : ℂ => ((w : ℂ̂))) := by
          intro x hx
          cases x with
          | infty => exact absurd hx hOinf
          | coe y => exact ⟨y, rfl⟩
        have hO'pre : IsPreconnected ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) := by
          have h1 : (fun w : ℂ => ((w : ℂ̂))) '' ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
              connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) =
              connectedComponentIn (Rsphᶜ) ((b : ℂ̂)) :=
            Set.image_preimage_eq_of_subset hOsubrange
          refine (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).mp ?_
          rw [h1]
          exact isPreconnected_connectedComponentIn
        have hO'uv : ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) ⊆ u ∪ v :=
          fun x hx => hKuv (hO'K hx)
        have hO'disj : ((fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂))) ∩ (u ∩ v) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          have hxK : x ∈ K ∩ (u ∩ v) := ⟨hO'K hx.1, hx.2⟩
          rw [hdisj] at hxK
          exact hxK
        rcases isPreconnected_iff_subset_of_disjoint.mp hO'pre u v hu hv
          hO'uv hO'disj with hsub | hsub
        · exact absurd (hsub hbO') hbu
        · refine ⟨(fun w : ℂ => ((w : ℂ̂))) ⁻¹'
            connectedComponentIn (Rsphᶜ) ((b : ℂ̂)), ?_, hO'open, hbO'⟩
          intro x hx
          refine ⟨hO'K hx, fun hxu => ?_⟩
          have hxK : x ∈ K ∩ (u ∩ v) := ⟨hO'K hx, hxu, hsub hx⟩
          rw [hdisj] at hxK
          exact hxK
      have hBne : (K \ u).Nonempty := ⟨w₀, hw₀K, hw₀u⟩
      rcases isClopen_iff.mp ⟨hBclosed, hBopen⟩ with h0 | huniv
      · rw [h0] at hBne
        exact Set.not_nonempty_empty hBne
      · have hmem : ((max R₀ 1 + 1 : ℝ) : ℂ) ∈ K \ u := by
          rw [huniv]
          exact Set.mem_univ _
        have h1 := hKball hmem.1
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith [hρpos])] at h1
        linarith
    rw [isPreconnected_iff_subset_of_disjoint]
    intro u v hu hv hKuv hdisj
    have htrpre : IsPreconnected (Set.range fun t : unitInterval => Γ t) :=
      isPreconnected_range Γ.continuous
    have h1 : (Set.range fun t : unitInterval => Γ t) ⊆ u ∪ v := by
      rintro x ⟨t, rfl⟩
      exact hKuv (htrK t)
    have h2 : (Set.range fun t : unitInterval => Γ t) ∩ (u ∩ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨t, rfl⟩, hx2⟩
      have hxK : Γ t ∈ K ∩ (u ∩ v) := ⟨htrK t, hx2⟩
      rw [hdisj] at hxK
      exact hxK
    rcases isPreconnected_iff_subset_of_disjoint.mp htrpre u v hu hv h1 h2 with
      htru | htrv
    · exact Or.inl (main u v hu hv hKuv hdisj fun t => htru ⟨t, rfl⟩)
    · refine Or.inr (main v u hv hu ?_ ?_ fun t => htrv ⟨t, rfl⟩)
      · rwa [Set.union_comm]
      · rwa [Set.inter_comm v u]
  -- ## Stage 5: the fill avoids the Julia set, hence sits in one component
  have hKFatou : ∀ x ∈ K, ((x : ℂ̂)) ∈ FatouSet f := by
    intro x hx
    by_contra hF
    have hJ : ((x : ℂ̂)) ∈ JuliaSet f := by
      rw [← compl_fatouSet]
      exact hF
    exact hx (hfill _ hJ)
  have hVfc : IsFatouComponent f (fcOrbit f U (N₀ + m)) :=
    isFatouComponent_fcOrbit (N₀ + m) hf hd1 hU
  have hp₀V : ((Γ 0 : ℂ̂)) ∈ fcOrbit f U (N₀ + m) := by
    have h1 : f^[m] ((γ 0 : ℂ̂)) ∈ fcOrbit f U (N₀ + m) := hfwd m _ (hγmem 0)
    have h2 : f^[m] ((γ 0 : ℂ̂)) ≠ ∞ := fun h => hinf (N₀ + m) (h ▸ h1)
    rw [hΓ 0, hcoe _ h2]
    exact h1
  have hSKV : ∀ x ∈ K, ((x : ℂ̂)) ∈ fcOrbit f U (N₀ + m) := by
    have hpre : IsPreconnected ((fun w : ℂ => ((w : ℂ̂))) '' K) :=
      hKpre.image _ OnePoint.continuous_coe.continuousOn
    have hmem0 : ((Γ 0 : ℂ̂)) ∈ (fun w : ℂ => ((w : ℂ̂))) '' K := ⟨Γ 0, htrK 0, rfl⟩
    have hsubF : (fun w : ℂ => ((w : ℂ̂))) '' K ⊆ FatouSet f := by
      rintro x ⟨x', hx', rfl⟩
      exact hKFatou x' hx'
    have h1 : (fun w : ℂ => ((w : ℂ̂))) '' K ⊆
        connectedComponentIn (FatouSet f) ((Γ 0 : ℂ̂)) :=
      hpre.subset_connectedComponentIn hmem0 hsubF
    obtain ⟨x₀, hx₀F, hVeq⟩ := hVfc
    have hmemx₀ : ((Γ 0 : ℂ̂)) ∈ connectedComponentIn (FatouSet f) x₀ := by
      rw [← hVeq]
      exact hp₀V
    have h2 : connectedComponentIn (FatouSet f) ((Γ 0 : ℂ̂)) =
        fcOrbit f U (N₀ + m) := by
      rw [hVeq]
      exact (connectedComponentIn_eq hmemx₀).symm
    intro x hx
    have h3 := h1 ⟨x, hx, rfl⟩
    rwa [h2] at h3
  -- ## Stage 6: a simply connected neighborhood of the fill
  have hT'open : IsOpen {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + m)} :=
    hVfc.isOpen.preimage OnePoint.continuous_coe
  have hKT' : K ⊆ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + m)} :=
    fun x hx => hSKV x hx
  obtain ⟨W, hWopen, hKW, hWT', hWsc⟩ :=
    exists_simplyConnectedSpace_between hKcomp ⟨hKne, hKpre⟩ hKfull hT'open hKT'
  -- ## Stage 7: null-homotope the pushed curve inside the neighborhood
  have hΓcl : Γ 0 = Γ 1 := by rw [hΓ 0, hΓ 1, hγcl]
  have hnullm : IsChartNullHomotopyIn Γ
      {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + m)} := by
    have hΓW : ∀ t : unitInterval, Γ t ∈ W := fun t => hKW (htrK t)
    haveI : SimplyConnectedSpace ↥W := hWsc
    let x₀ : ↥W := ⟨Γ 0, hΓW 0⟩
    let pΓ : Path x₀ x₀ :=
      { toFun := fun s => ⟨Γ s, hΓW s⟩
        continuous_toFun := Γ.continuous.subtype_mk hΓW
        source' := rfl
        target' := Subtype.ext hΓcl.symm }
    obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic pΓ (Path.refl x₀)
    exact ⟨⟨fun q => ((F q : ↥W) : ℂ), continuous_subtype_val.comp F.continuous⟩,
      fun s => congrArg Subtype.val (F.apply_zero s),
      fun s => congrArg Subtype.val (F.apply_one s),
      fun t => ⟨congrArg Subtype.val (Path.Homotopy.source F t),
        congrArg Subtype.val (Path.Homotopy.target F t)⟩,
      fun q => hWT' (F q).2⟩
  -- ## Stage 8: descend the null homotopy through the covering steps
  have descend : ∀ j : ℕ, ∀ Γ' : C(unitInterval, ℂ),
      (∀ t : unitInterval, Γ' t = chartFiniteMap (f^[j] ((γ t : ℂ̂)))) →
      IsChartNullHomotopyIn Γ' {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U (N₀ + j)} →
      IsChartNullHomotopyIn γ {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U N₀} := by
    intro j
    induction j with
    | zero =>
        intro Γ' hΓ' hnull
        have hΓ'γ : Γ' = γ := by
          ext t
          rw [hΓ' t, Function.iterate_zero_apply]
          rfl
        rw [hΓ'γ, Nat.add_zero] at hnull
        exact hnull
    | succ k ih =>
        intro Γ' hΓ' hnull
        obtain ⟨Γk, hΓk⟩ := exists_pushed_curve hf hd hU hinf hγmem k
        have hne : ∀ t : unitInterval, f^[k] ((γ t : ℂ̂)) ≠ ∞ := by
          intro t h
          exact hinf (N₀ + k) (h ▸ hfwd k _ (hγmem t))
        have hΓksph : ∀ t : unitInterval, ((Γk t : ℂ̂)) = f^[k] ((γ t : ℂ̂)) := by
          intro t
          rw [hΓk t]
          exact hcoe _ (hne t)
        have hΓkcl : Γk 0 = Γk 1 := by rw [hΓk 0, hΓk 1, hγcl]
        have hΓkmem : ∀ t : unitInterval, ((Γk t : ℂ̂)) ∈ fcOrbit f U (N₀ + k) := by
          intro t
          rw [hΓksph t]
          exact hfwd k _ (hγmem t)
        have hstepev : ∀ t : unitInterval, Γ' t = chartFiniteMap (f ((Γk t : ℂ̂))) := by
          intro t
          rw [hΓksph t, ← Function.iterate_succ_apply' f k ((γ t : ℂ̂))]
          exact hΓ' t
        have hnull' : IsChartNullHomotopyIn Γ'
            {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U ((N₀ + k) + 1)} := by
          rwa [show N₀ + (k + 1) = (N₀ + k) + 1 by omega] at hnull
        have hstep := isChartNullHomotopyIn_of_step hf hd hU (N₀ + k)
          (hinf (N₀ + k)) (hinf ((N₀ + k) + 1)) (hcrit (N₀ + k))
          hΓkcl hΓkmem hstepev hnull'
        exact ih Γk hΓk hstep
  have hnull0 : IsChartNullHomotopyIn γ
      {w : ℂ | ((w : ℂ̂)) ∈ fcOrbit f U N₀} := descend m Γ hΓ hnullm
  -- ## Stage 9: homotopy invariance kills the winding numbers
  intro z hzJ
  obtain ⟨H, hH0, hH1, hHbd, hHmem⟩ := hnull0
  have hN₀fc : IsFatouComponent f (fcOrbit f U N₀) :=
    isFatouComponent_fcOrbit N₀ hf hd1 hU
  have hγ0z : γ 0 ≠ z := by
    intro heq
    have h0 : ((γ 0 : ℂ̂)) ∈ FatouSet f := hN₀fc.subset_fatouSet (hγmem 0)
    rw [heq] at h0
    exact hjf _ h0 hzJ
  let Hrel : ContinuousMap.HomotopyRel γ
      (ContinuousMap.const unitInterval (γ 0)) {0, 1} :=
    { toFun := fun q => H q
      continuous_toFun := H.continuous
      map_zero_left := hH0
      map_one_left := fun s => hH1 s
      prop' := by
        intro t s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact (hHbd t).1
        · exact (hHbd t).2.trans hγcl }
  have havoid : ∀ (t s : unitInterval), Hrel (t, s) ≠ z := by
    intro t s heq
    have h1 : ((H (t, s) : ℂ̂)) ∈ FatouSet f :=
      hN₀fc.subset_fatouSet (hHmem (t, s))
    have heq' : H (t, s) = z := heq
    rw [heq'] at h1
    exact hjf _ h1 hzJ
  rw [windingNumber_eq_of_homotopicRel hγcl Hrel havoid]
  exact windingNumber_const (γ 0) z hγ0z

open Set unitInterval in
/-- **Normal limits on a wandering orbit are constant**: a locally uniform
subsequential limit of the iterates on a wandering Fatou component has
image of measure zero (the orbit components are pairwise disjoint, so their
spherical areas are summable), and a nonconstant holomorphic map has open
image. -/
theorem eventually_constant_limit_of_wandering {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {g : ℂ̂ → ℂ̂} {K : Set ℂ̂}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hlim : TendstoLocallyUniformlyOn (fun j => f^[φ j]) g Filter.atTop
      (interior K)) :
    ∀ x ∈ interior K, ∀ y ∈ interior K,
      connectedComponentIn (interior K) x =
        connectedComponentIn (interior K) y → g x = g y := by
  classical
  -- ## Stage 0: basic facts
  have _ := hK
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hopenK : IsOpen (interior K) := isOpen_interior
  have hcont_iter : ∀ n : ℕ, Continuous (f^[n]) := by
    intro n
    induction n with
    | zero => simpa using continuous_id
    | succ m ih =>
        rw [Function.iterate_succ]
        exact ih.comp hf.continuous
  have hgcont : ContinuousOn g (interior K) :=
    hlim.continuousOn
      (Filter.Frequently.of_forall fun j => (hcont_iter (φ j)).continuousOn)
  have hOpenMap : IsOpenMap f := hf.isOpenMap (fun c => hf.ne_const hd1 c)
  have hfatou_iter : ∀ (n : ℕ) (z : ℂ̂), z ∈ FatouSet f →
      f^[n] z ∈ FatouSet f := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        intro z hz
        rw [Function.iterate_succ_apply']
        exact apply_mem_fatouSet hOpenMap (ih z hz)
  have hmem_orbit : ∀ (n : ℕ) (z : ℂ̂), z ∈ U → f^[n] z ∈ fcOrbit f U n := by
    intro n z hz
    exact Set.mem_biUnion hz
      (mem_connectedComponentIn (hfatou_iter n z (hU.subset_fatouSet hz)))
  have hiter_rat : ∀ n : ℕ, IsRational (f^[n]) := fun n => hf.iterate hd1 n
  -- ## Stage 1: clopen propagation of local constancy on preconnected sets
  have clopen_const : ∀ S : Set ℂ̂, IsPreconnected S →
      (∀ w ∈ S, ∀ᶠ w' in 𝓝 w, g w' = g w) →
      ∀ a ∈ S, ∀ b ∈ S, g a = g b := by
    intro S hS hlc a ha b hb
    by_contra hab
    set N : ℂ̂ → Set ℂ̂ := fun w => interior {w' | g w' = g w} with hNdef
    have hNopen : ∀ w : ℂ̂, IsOpen (N w) := fun w => isOpen_interior
    have hNmem : ∀ w ∈ S, w ∈ N w := by
      intro w hw
      rw [hNdef, mem_interior_iff_mem_nhds]
      exact (hlc w hw).mono fun w' h => h
    have hNval : ∀ w : ℂ̂, ∀ u ∈ N w, g u = g w := by
      intro w u hu
      have h : u ∈ {w' | g w' = g w} := interior_subset hu
      exact h
    have hcover : S ⊆ (⋃ w ∈ {w ∈ S | g w = g a}, N w) ∪
        (⋃ w ∈ {w ∈ S | g w ≠ g a}, N w) := by
      intro w hw
      by_cases hwa : g w = g a
      · exact Or.inl (Set.mem_biUnion ⟨hw, hwa⟩ (hNmem w hw))
      · exact Or.inr (Set.mem_biUnion ⟨hw, hwa⟩ (hNmem w hw))
    have h1 : (S ∩ ⋃ w ∈ {w ∈ S | g w = g a}, N w).Nonempty :=
      ⟨a, ha, Set.mem_biUnion ⟨ha, rfl⟩ (hNmem a ha)⟩
    have h2 : (S ∩ ⋃ w ∈ {w ∈ S | g w ≠ g a}, N w).Nonempty :=
      ⟨b, hb, Set.mem_biUnion ⟨hb, fun h => hab h.symm⟩ (hNmem b hb)⟩
    obtain ⟨u, -, hu₁, hu₂⟩ := hS _ _
      (isOpen_biUnion fun w _ => hNopen w) (isOpen_biUnion fun w _ => hNopen w)
      hcover h1 h2
    obtain ⟨w₁, hw₁, hu₁'⟩ := Set.mem_iUnion₂.mp hu₁
    obtain ⟨w₂, hw₂, hu₂'⟩ := Set.mem_iUnion₂.mp hu₂
    exact hw₂.2 (by rw [← hNval w₂ u hu₂', hNval w₁ u hu₁', hw₁.2])
  -- ## Stage 2: local constancy at finite points of `interior K` (the engine)
  have key : ∀ p₀ : ℂ, ((p₀ : ℂ̂)) ∈ interior K →
      ∀ᶠ w in 𝓝 ((p₀ : ℂ̂)), g w = g ((p₀ : ℂ̂)) := by
    intro p₀ hp₀
    set c : ℂ̂ := g ((p₀ : ℂ̂)) with hcdef
    -- ### chart data around the limit value `c`
    obtain ⟨χ, Cm, s, hCm, hs, hχinj, hχcomp, hread⟩ :
        ∃ (χ : ℂ̂ → ℂ) (Cm s : ℝ), 0 < Cm ∧ 0 < s ∧
          (∀ v v' : ℂ̂, dist c v < s → dist c v' < s → χ v = χ v' → v = v') ∧
          (∀ v v' : ℂ̂, dist c v < s → dist c v' < s →
            ‖χ v - χ v'‖ ≤ Cm * dist v v') ∧
          (∀ n : ℕ, ∃ A B : Polynomial ℂ, ∀ z : ℂ,
            dist c (f^[n] ((z : ℂ̂))) < s →
              B.eval z ≠ 0 ∧ χ (f^[n] ((z : ℂ̂))) = A.eval z / B.eval z) := by
      have hcoe : ∀ p : ℂ̂, p ≠ ∞ → ((chartFiniteMap p : ℂ) : ℂ̂) = p := by
        intro p hp
        cases p with
        | infty => exact absurd rfl hp
        | coe x => rfl
      by_cases hcinf : c = ∞
      · -- infinity chart around `c = ∞`
        rw [hcinf]
        have hbound : ∀ v : ℂ̂, dist (∞ : ℂ̂) v < 1 →
            v ≠ (((0 : ℂ)) : ℂ̂) ∧ ‖chartInftyMap v‖ ≤ 1 := by
          intro v hv
          cases v with
          | infty =>
            refine ⟨(OnePoint.infty_ne_coe (0 : ℂ)), ?_⟩
            rw [show chartInftyMap (∞ : ℂ̂) = 0 from rfl, norm_zero]
            exact zero_le_one
          | coe x =>
            have hx_eq : dist (∞ : ℂ̂) ((x : ℂ̂)) =
                2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
            rw [hx_eq] at hv
            have hs0 : 0 < Real.sqrt (1 + ‖x‖ ^ 2) :=
              Real.sqrt_pos.mpr (by positivity)
            have h2 : 2 < Real.sqrt (1 + ‖x‖ ^ 2) := by
              rw [div_lt_iff₀ hs0, one_mul] at hv
              exact hv
            have h3 : (4 : ℝ) < 1 + ‖x‖ ^ 2 := by
              have := (Real.lt_sqrt (by positivity)).mp h2
              nlinarith
            have hxnorm : 1 < ‖x‖ := by nlinarith [norm_nonneg x]
            have hxne : x ≠ 0 := by
              intro h0
              rw [h0, norm_zero] at hxnorm
              linarith
            refine ⟨fun h => hxne (OnePoint.coe_eq_coe.mp h), ?_⟩
            rw [show chartInftyMap ((x : ℂ̂)) = x⁻¹ from rfl, norm_inv]
            exact inv_le_one_of_one_le₀ hxnorm.le
        have hinv_ne : ∀ v : ℂ̂, v ≠ (((0 : ℂ)) : ℂ̂) → inversionGL • v ≠ ∞ := by
          intro v hv
          cases v with
          | infty =>
            rw [inversionGL_smul_infty]
            exact OnePoint.coe_ne_infty 0
          | coe x =>
            have hx : x ≠ 0 := fun h => hv (by rw [h])
            rw [inversionGL_smul_coe, if_neg hx]
            exact OnePoint.coe_ne_infty _
        have hkeyI : ∀ p : ℂ̂, chartInftyMap p = chartFiniteMap (inversionGL • p) := by
          intro p
          cases p with
          | infty =>
            rw [show chartInftyMap (∞ : ℂ̂) = 0 from rfl, inversionGL_smul_infty]
            rfl
          | coe x =>
            by_cases hx : x = 0
            · subst hx
              rw [show chartInftyMap (((0 : ℂ)) : ℂ̂) = (0 : ℂ)⁻¹ from rfl,
                inv_zero, inversionGL_smul_coe, if_pos rfl]
              rfl
            · rw [inversionGL_smul_coe, if_neg hx]
              rfl
        refine ⟨chartInftyMap, 1, 1, one_pos, one_pos, ?_, ?_, ?_⟩
        · -- injectivity on the spherical unit ball about `∞`
          intro v v' hv hv' heq
          have h1 := inversionGL_smul_coe_chartInftyMap (hbound v hv).1
          have h2 := inversionGL_smul_coe_chartInftyMap (hbound v' hv').1
          rw [← h1, ← h2, heq]
        · -- metric comparison via the inversion isometry
          intro v v' hv hv'
          have hvne := (hbound v hv).1
          have hv'ne := (hbound v' hv').1
          have hb1 : ‖chartFiniteMap (inversionGL • v)‖ ≤ 1 := by
            rw [← hkeyI v]
            exact (hbound v hv).2
          have hb2 : ‖chartFiniteMap (inversionGL • v')‖ ≤ 1 := by
            rw [← hkeyI v']
            exact (hbound v' hv').2
          have h1 := norm_sub_le_sphericalDist_mul hb1 hb2
          have h2 : sphericalDist ((chartFiniteMap (inversionGL • v) : ℂ) : ℂ̂)
              ((chartFiniteMap (inversionGL • v') : ℂ) : ℂ̂) = dist v v' := by
            rw [hcoe _ (hinv_ne v hvne), hcoe _ (hinv_ne v' hv'ne),
              sphericalDist_inversionGL_smul v v']
            rfl
          rw [h2] at h1
          rw [hkeyI v, hkeyI v']
          calc ‖chartFiniteMap (inversionGL • v) - chartFiniteMap (inversionGL • v')‖
              ≤ (1 + 1 ^ 2) / 2 * dist v v' := h1
            _ = 1 * dist v v' := by norm_num
        · -- rational reading in the infinity chart: swap numerator/denominator
          intro n
          obtain ⟨rn, hrn⟩ := hiter_rat n
          refine ⟨rn.denReduced, rn.numReduced, fun z hz => ?_⟩
          have he : f^[n] ((z : ℂ̂)) = if rn.denReduced.eval z = 0 then ∞
              else ((rn.numReduced.eval z / rn.denReduced.eval z : ℂ) : ℂ̂) := by
            rw [hrn]
            rfl
          by_cases hden : rn.denReduced.eval z = 0
          · have hnum : rn.numReduced.eval z ≠ 0 :=
              (rn.eval_ne_zero_or z).resolve_right fun h => h hden
            refine ⟨hnum, ?_⟩
            rw [he, if_pos hden, show chartInftyMap (∞ : ℂ̂) = 0 from rfl,
              hden, zero_div]
          · have hval : f^[n] ((z : ℂ̂)) =
                ((rn.numReduced.eval z / rn.denReduced.eval z : ℂ) : ℂ̂) := by
              rw [he, if_neg hden]
            have hne0 : rn.numReduced.eval z / rn.denReduced.eval z ≠ 0 := by
              intro h0
              rw [hval, h0] at hz
              have h2 : dist (∞ : ℂ̂) (((0 : ℂ)) : ℂ̂) = 2 := by
                change (2 : ℝ) / Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 2
                simp
              rw [h2] at hz
              linarith
            have hnum : rn.numReduced.eval z ≠ 0 := fun h =>
              hne0 (by rw [h, zero_div])
            refine ⟨hnum, ?_⟩
            rw [hval, show chartInftyMap
                (((rn.numReduced.eval z / rn.denReduced.eval z : ℂ)) : ℂ̂) =
                (rn.numReduced.eval z / rn.denReduced.eval z)⁻¹ from rfl, inv_div]
      · -- finite chart around a finite `c`
        set d : ℝ := dist c (∞ : ℂ̂) with hddef
        have hd0 : 0 < d := dist_pos.mpr hcinf
        have hbound : ∀ v : ℂ̂, dist c v < d / 2 →
            v ≠ ∞ ∧ ‖chartFiniteMap v‖ ≤ 2 / (d / 2) := by
          intro v hv
          cases v with
          | infty =>
            exfalso
            rw [← hddef] at hv
            linarith
          | coe x =>
            refine ⟨OnePoint.coe_ne_infty x, ?_⟩
            have hfar : d / 2 ≤ dist ((x : ℂ̂)) (∞ : ℂ̂) := by
              have htri : d ≤ dist c ((x : ℂ̂)) + dist ((x : ℂ̂)) (∞ : ℂ̂) := by
                rw [hddef]
                exact dist_triangle _ _ _
              linarith
            have hx_eq : dist ((x : ℂ̂)) (∞ : ℂ̂) =
                2 / Real.sqrt (1 + ‖x‖ ^ 2) := rfl
            rw [hx_eq] at hfar
            have hs0 : 0 < Real.sqrt (1 + ‖x‖ ^ 2) :=
              Real.sqrt_pos.mpr (by positivity)
            have hxs : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
              calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
                _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) :=
                    Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖])
            have h2 : d / 2 * Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 := by
              rw [le_div_iff₀ hs0] at hfar
              linarith
            have h3 : Real.sqrt (1 + ‖x‖ ^ 2) ≤ 2 / (d / 2) := by
              rw [le_div_iff₀ (by positivity)]
              linarith [mul_comm (d / 2) (Real.sqrt (1 + ‖x‖ ^ 2))]
            exact (show ‖chartFiniteMap ((x : ℂ̂))‖ = ‖x‖ from rfl) ▸ hxs.trans h3
        refine ⟨chartFiniteMap, (1 + (2 / (d / 2)) ^ 2) / 2, d / 2,
          by positivity, by positivity, ?_, ?_, ?_⟩
        · -- injectivity on the ball of finite points
          intro v v' hv hv' heq
          have h1 := hcoe v (hbound v hv).1
          have h2 := hcoe v' (hbound v' hv').1
          rw [← h1, ← h2, heq]
        · -- Euclidean-vs-spherical comparison on the bounded region
          intro v v' hv hv'
          have h1 := norm_sub_le_sphericalDist_mul (hbound v hv).2 (hbound v' hv').2
          have h2 : sphericalDist ((chartFiniteMap v : ℂ) : ℂ̂)
              ((chartFiniteMap v' : ℂ) : ℂ̂) = dist v v' := by
            rw [hcoe v (hbound v hv).1, hcoe v' (hbound v' hv').1]
            rfl
          rw [h2] at h1
          exact h1
        · -- rational reading in the finite chart
          intro n
          obtain ⟨rn, hrn⟩ := hiter_rat n
          refine ⟨rn.numReduced, rn.denReduced, fun z hz => ?_⟩
          have he : f^[n] ((z : ℂ̂)) = if rn.denReduced.eval z = 0 then ∞
              else ((rn.numReduced.eval z / rn.denReduced.eval z : ℂ) : ℂ̂) := by
            rw [hrn]
            rfl
          by_cases hden : rn.denReduced.eval z = 0
          · exfalso
            rw [he, if_pos hden, ← hddef] at hz
            linarith
          · refine ⟨hden, ?_⟩
            rw [he, if_neg hden]
            rfl
    -- ### E1: a closed disk decoding into `interior K` with `g`-values near `c`
    obtain ⟨δ, hδpos, hδprop⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.closedBall p₀ δ,
        ((z : ℂ̂)) ∈ interior K ∧ dist c (g ((z : ℂ̂))) < s / 4 := by
      have h1 : interior K ∈ 𝓝 ((p₀ : ℂ̂)) := hopenK.mem_nhds hp₀
      have h2 : g ⁻¹' (Metric.ball c (s / 4)) ∈ 𝓝 ((p₀ : ℂ̂)) := by
        refine (hgcont.continuousAt h1).preimage_mem_nhds ?_
        rw [← hcdef]
        exact Metric.ball_mem_nhds _ (by positivity)
      have h3 : (fun z : ℂ => ((z : ℂ̂))) ⁻¹'
          (interior K ∩ g ⁻¹' (Metric.ball c (s / 4))) ∈ 𝓝 p₀ :=
        (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds
          (Filter.inter_mem h1 h2)
      obtain ⟨δ, hδpos, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp h3
      refine ⟨δ, hδpos, fun z hz => ?_⟩
      obtain ⟨hzK, hzg⟩ := hδsub hz
      refine ⟨hzK, ?_⟩
      rw [Set.mem_preimage, Metric.mem_ball] at hzg
      rw [dist_comm]
      exact hzg
    -- ### E2: uniform convergence on the decoded closed disk
    have hdisk_sub : (fun z : ℂ => ((z : ℂ̂))) '' Metric.closedBall p₀ δ ⊆
        interior K := by
      rintro - ⟨z, hz, rfl⟩
      exact (hδprop z hz).1
    have hTU : TendstoUniformlyOn (fun j => f^[φ j]) g atTop
        ((fun z : ℂ => ((z : ℂ̂))) '' Metric.closedBall p₀ δ) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hopenK).mp hlim _ hdisk_sub
        ((isCompact_closedBall _ _).image OnePoint.continuous_coe)
    have hev_ball : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall p₀ δ,
        dist c (f^[φ j] ((z : ℂ̂))) < s / 2 := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hTU (s / 4)
        (by positivity)] with j hj z hz
      have h1 := hj _ ⟨z, hz, rfl⟩
      have h2 := (hδprop z hz).2
      calc dist c (f^[φ j] ((z : ℂ̂)))
          ≤ dist c (g ((z : ℂ̂))) + dist (g ((z : ℂ̂))) (f^[φ j] ((z : ℂ̂))) :=
            dist_triangle _ _ _
        _ < s / 4 + s / 4 := add_lt_add h2 h1
        _ = s / 2 := by ring
    -- the chart reading of the limit
    set G : ℂ → ℂ := fun z => χ (g ((z : ℂ̂))) with hGdef
    -- ### E2': chart readings converge uniformly on the closed disk
    have hTUχ : TendstoUniformlyOn (fun j (z : ℂ) => χ (f^[φ j] ((z : ℂ̂)))) G atTop
        (Metric.closedBall p₀ δ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hev_ball, Metric.tendstoUniformlyOn_iff.mp hTU
        (min (s / 4) (ε / Cm)) (lt_min (by positivity) (by positivity))]
        with j hj₁ hj₂ z hz
      have hgb : dist c (g ((z : ℂ̂))) < s := lt_trans (hδprop z hz).2 (by linarith)
      have hfb : dist c (f^[φ j] ((z : ℂ̂))) < s := lt_trans (hj₁ z hz) (by linarith)
      have h3 := hj₂ _ ⟨z, hz, rfl⟩
      have h4 : ‖χ (g ((z : ℂ̂))) - χ (f^[φ j] ((z : ℂ̂)))‖ ≤
          Cm * dist (g ((z : ℂ̂))) (f^[φ j] ((z : ℂ̂))) := hχcomp _ _ hgb hfb
      calc dist (G z) (χ (f^[φ j] ((z : ℂ̂))))
          = ‖χ (g ((z : ℂ̂))) - χ (f^[φ j] ((z : ℂ̂)))‖ := dist_eq_norm _ _
        _ ≤ Cm * dist (g ((z : ℂ̂))) (f^[φ j] ((z : ℂ̂))) := h4
        _ < Cm * (ε / Cm) :=
            mul_lt_mul_of_pos_left (lt_of_lt_of_le h3 (min_le_right _ _)) hCm
        _ = ε := by field_simp
    -- ### E2'': eventual differentiability of the chart readings
    have hFdiff : ∀ᶠ j in atTop, DifferentiableOn ℂ
        (fun z : ℂ => χ (f^[φ j] ((z : ℂ̂)))) (Metric.ball p₀ δ) := by
      filter_upwards [hev_ball] with j hj
      obtain ⟨A, B, hAB⟩ := hread (φ j)
      have hBne : ∀ z ∈ Metric.closedBall p₀ δ, B.eval z ≠ 0 := fun z hz =>
        (hAB z (lt_trans (hj z hz) (by linarith))).1
      have hdiff : DifferentiableOn ℂ (fun z => A.eval z / B.eval z)
          (Metric.ball p₀ δ) :=
        (A.differentiable.differentiableOn).div (B.differentiable.differentiableOn)
          (fun z hz => hBne z (Metric.ball_subset_closedBall hz))
      exact hdiff.congr fun z hz =>
        (hAB z (lt_trans (hj z (Metric.ball_subset_closedBall hz)) (by linarith))).2
    -- ### E2''': the limit reading is analytic on the open disk
    have hGdiff : DifferentiableOn ℂ G (Metric.ball p₀ δ) :=
      (hTUχ.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall).differentiableOn
        hFdiff Metric.isOpen_ball
    have hGanal : AnalyticAt ℂ (fun z => G z - χ c) p₀ :=
      (hGdiff.analyticAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδpos))).sub analyticAt_const
    -- ### E3: the isolated-zeros dichotomy
    rcases hGanal.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · -- constant branch: `g = c` near `p₀`, transfer through the embedding
      have hev : ∀ᶠ z : ℂ in 𝓝 p₀, g ((z : ℂ̂)) = c := by
        have h2 : Metric.closedBall p₀ δ ∈ 𝓝 p₀ :=
          Metric.closedBall_mem_nhds _ hδpos
        filter_upwards [hzero, h2] with z h₁ h₂
        have hgb : dist c (g ((z : ℂ̂))) < s := lt_trans (hδprop z h₂).2 (by linarith)
        have hcb : dist c c < s := by rw [dist_self]; exact hs
        exact hχinj _ _ hgb hcb (sub_eq_zero.mp h₁)
      rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
      exact hev
    · -- nonconstant branch: run the attainment engine to a contradiction
      exfalso
      -- ### E4: a punctured ball where the limit reading avoids `χ c`
      obtain ⟨ε, hεpos, hεprop⟩ : ∃ ε > 0, ∀ z : ℂ, dist z p₀ < ε → z ≠ p₀ →
          G z ≠ χ c := by
        have h1 : ∀ᶠ z in 𝓝 p₀, z ∈ ({p₀}ᶜ : Set ℂ) → G z - χ c ≠ 0 :=
          eventually_nhdsWithin_iff.mp hne
        obtain ⟨ε, hε, h2⟩ := Metric.eventually_nhds_iff.mp h1
        refine ⟨ε, hε, fun z hz hzp hGz => ?_⟩
        exact h2 hz (Set.mem_compl_singleton_iff.mpr hzp) (sub_eq_zero.mpr hGz)
      -- the circle radius
      set r : ℝ := min (ε / 2) (δ / 2) with hrdef
      have hrpos : 0 < r := lt_min (by linarith) (by linarith)
      have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      -- ### E4': the circle curve
      have hcirc_cont : Continuous (fun t : I => p₀ + (r : ℂ) *
          Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        refine continuous_const.add (continuous_const.mul
          (Complex.continuous_exp.comp ?_))
        exact (Complex.continuous_ofReal.comp
          (continuous_const.mul continuous_subtype_val)).mul continuous_const
      set cir : C(I, ℂ) := ⟨fun t : I => p₀ + (r : ℂ) *
          Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I),
          hcirc_cont⟩ with hcirdef
      have hcir_apply : ∀ t : I, cir t = p₀ + (r : ℂ) *
          Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) :=
        fun t => rfl
      have hcir_dist : ∀ t : I, dist (cir t) p₀ = r := by
        intro t
        rw [hcir_apply t, dist_eq_norm, add_sub_cancel_left, norm_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hrpos]
      have hcir_cl : cir 0 = cir 1 := by
        rw [hcir_apply, hcir_apply]
        have h0 : ((0 : I) : ℝ) = 0 := rfl
        have h1 : ((1 : I) : ℝ) = 1 := rfl
        rw [h0, h1, mul_zero, mul_one]
        push_cast
        rw [zero_mul, Complex.exp_zero, Complex.exp_two_pi_mul_I]
      have hcir_ne : ∀ t : I, cir t ≠ p₀ := by
        intro t h0
        have h1 := hcir_dist t
        rw [h0, dist_self] at h1
        exact (ne_of_gt hrpos) h1.symm
      have hcir_mem_ball : ∀ t : I, cir t ∈ Metric.ball p₀ δ := by
        intro t
        rw [Metric.mem_ball, hcir_dist]
        exact hrδ
      have hcir_mem_cball : ∀ t : I, cir t ∈ Metric.closedBall p₀ δ :=
        fun t => Metric.ball_subset_closedBall (hcir_mem_ball t)
      -- ### E4'': every point of the circle is a value of `cir`
      have hcir_surj : ∀ w : ℂ, dist w p₀ = r → ∃ t : I, cir t = w := by
        intro w hw
        have hwn : ‖w - p₀‖ = r := by rwa [dist_eq_norm] at hw
        set θ := Complex.arg (w - p₀) with hθdef
        have hθlow : -Real.pi < θ := Complex.neg_pi_lt_arg _
        have hθhigh : θ ≤ Real.pi := Complex.arg_le_pi _
        have hπpos := Real.pi_pos
        have hval : ((r : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)
            = w - p₀ := by
          have h1 := Complex.norm_mul_exp_arg_mul_I (w - p₀)
          rw [← hθdef, hwn] at h1
          exact h1
        by_cases hθ0 : 0 ≤ θ
        · refine ⟨⟨θ / (2 * Real.pi), ⟨by positivity, ?_⟩⟩, ?_⟩
          · rw [div_le_one (by positivity)]
            linarith
          · rw [hcir_apply]
            have harg : (2 * Real.pi * (θ / (2 * Real.pi)) : ℝ) = θ := by
              field_simp
            rw [show ((⟨θ / (2 * Real.pi), _⟩ : I) : ℝ) = θ / (2 * Real.pi) from rfl,
              harg]
            linear_combination hval
        · refine ⟨⟨θ / (2 * Real.pi) + 1, ⟨?_, ?_⟩⟩, ?_⟩
          · have h1 : (-1 : ℝ) ≤ θ / (2 * Real.pi) :=
              (le_div_iff₀ (by positivity)).mpr (by linarith)
            linarith
          · have h1 : θ / (2 * Real.pi) ≤ 0 :=
              div_nonpos_iff.mpr (Or.inr ⟨le_of_not_ge hθ0, by positivity⟩)
            linarith
          · rw [hcir_apply]
            rw [show ((⟨θ / (2 * Real.pi) + 1, _⟩ : I) : ℝ)
                = θ / (2 * Real.pi) + 1 from rfl]
            have harg : (2 * Real.pi * (θ / (2 * Real.pi) + 1) : ℝ)
                = θ + 2 * Real.pi := by
              field_simp
            rw [harg]
            have hsplit : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
                = ((θ : ℝ) : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by
              push_cast
              ring
            rw [hsplit, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
            linear_combination hval
      -- ### E5: the limit reading is uniformly far from `χ c` on the circle
      have hGcont : ContinuousOn G (Metric.ball p₀ δ) := hGdiff.continuousOn
      have hGcir_cont : Continuous fun t : I => ‖G (cir t) - χ c‖ :=
        ((hGcont.comp_continuous cir.continuous hcir_mem_ball).sub
          continuous_const).norm
      obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn
        Set.univ_nonempty hGcir_cont.continuousOn
      set ρ : ℝ := ‖G (cir t₀) - χ c‖ / 4 with hρdef
      have hρpos : 0 < ρ := by
        have hne0 : G (cir t₀) ≠ χ c := by
          apply hεprop
          · rw [hcir_dist t₀]
            exact hrε
          · exact hcir_ne t₀
        have h1 : 0 < ‖G (cir t₀) - χ c‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr hne0)
        rw [hρdef]
        linarith
      have hGfar : ∀ t : I, 4 * ρ ≤ ‖G (cir t) - χ c‖ := by
        intro t
        have h1 := isMinOn_iff.mp ht₀ t (Set.mem_univ t)
        rw [hρdef]
        linarith
      -- ### E5': winding numbers of the circle about test points
      have windKey : ∀ (γ : C(I, ℂ)) (ζ : ℂ),
          windingNumber (shiftedCurve γ ζ) 0 = windingNumber γ ζ := by
        intro γ ζ
        have h : shiftedCurve (shiftedCurve γ ζ) 0 = shiftedCurve γ ζ := by
          ext t
          simp [shiftedCurve]
        unfold windingNumber
        rw [h]
      have hwind_center : windingNumber cir p₀ = 1 := by
        have hLcont : Continuous fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I := by
          refine continuous_const.add ?_
          exact (Complex.continuous_ofReal.comp
            (continuous_const.mul continuous_subtype_val)).mul continuous_const
        have hL : IsLogLiftOf ⟨fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, hLcont⟩
            (shiftedCurve cir p₀) := by
          intro t
          have h2 : shiftedCurve cir p₀ t = cir t - p₀ := rfl
          change Complex.exp (((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I) = _
          rw [Complex.exp_add, h2, hcir_apply]
          have h1 : Complex.exp (((Real.log r : ℝ)) : ℂ) = ((r : ℝ) : ℂ) := by
            rw [← Complex.ofReal_exp, Real.exp_log hrpos]
          rw [h1]
          ring
        have hspec := windingNumber_spec hcir_cl hcir_ne hL
        have hincr : (⟨fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, hLcont⟩ : C(I, ℂ)) 1 -
            (⟨fun t : I => ((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * (t : ℝ) : ℝ)) : ℂ) * Complex.I, hLcont⟩ : C(I, ℂ)) 0 =
            2 * (Real.pi : ℂ) * Complex.I := by
          change (((Real.log r : ℝ) : ℂ) + (((2 * Real.pi * ((1 : I) : ℝ) : ℝ)) : ℂ) *
            Complex.I) - (((Real.log r : ℝ) : ℂ) +
            (((2 * Real.pi * ((0 : I) : ℝ) : ℝ)) : ℂ) * Complex.I) = _
          rw [show ((1 : I) : ℝ) = 1 from rfl, show ((0 : I) : ℝ) = 0 from rfl]
          push_cast
          ring
        rw [hincr] at hspec
        have hcast : (2 * (Real.pi : ℂ) * Complex.I) * 1 =
            (2 * (Real.pi : ℂ) * Complex.I) * ((windingNumber cir p₀ : ℤ) : ℂ) := by
          rw [mul_one]
          exact hspec
        have := mul_left_cancel₀ Complex.two_pi_I_ne_zero hcast
        exact_mod_cast this.symm
      have hwind_in : ∀ ζ : ℂ, dist ζ p₀ < r → windingNumber cir ζ = 1 := by
        intro ζ hζ
        have hζn : ‖ζ - p₀‖ < r := by rwa [dist_eq_norm] at hζ
        have hC : IsPreconnected
            ((fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1) :=
          isPreconnected_Icc.image _
            (continuous_const.add
              (Complex.continuous_ofReal.mul continuous_const)).continuousOn
        have hdisj : ∀ t : I,
            cir t ∉ (fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1 := by
          rintro t ⟨θ, hθ, hteq⟩
          have h1 := hcir_dist t
          rw [← hteq, dist_eq_norm, add_sub_cancel_left, norm_mul,
            Complex.norm_real, Real.norm_eq_abs] at h1
          have habs : |θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
          nlinarith [norm_nonneg (ζ - p₀), abs_nonneg θ]
        have hζC : ζ ∈ (fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1 :=
          ⟨1, ⟨zero_le_one, le_refl 1⟩,
            by change p₀ + ((1 : ℝ) : ℂ) * (ζ - p₀) = ζ; push_cast; ring⟩
        have hp₀C : p₀ ∈ (fun θ : ℝ => p₀ + (θ : ℂ) * (ζ - p₀)) '' Set.Icc 0 1 :=
          ⟨0, ⟨le_refl 0, zero_le_one⟩,
            by change p₀ + ((0 : ℝ) : ℂ) * (ζ - p₀) = p₀; push_cast; ring⟩
        rw [windingNumber_eq_of_preconnected hcir_cl hC hdisj hζC hp₀C]
        exact hwind_center
      have hwind_out : ∀ ζ : ℂ, r < dist ζ p₀ → windingNumber cir ζ = 0 := by
        intro ζ hζ
        refine windingNumber_eq_zero_of_ball (c := p₀) (r := dist ζ p₀)
          hcir_cl (fun t => ?_) (fun h => ?_)
        · rw [Metric.mem_ball, hcir_dist]
          exact hζ
        · rw [Metric.mem_ball] at h
          exact lt_irrefl _ h
      -- ### E6: two indices with the uniform estimates
      have hev_close : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall p₀ δ,
          dist (G z) (χ (f^[φ j] ((z : ℂ̂)))) < ρ :=
        Metric.tendstoUniformlyOn_iff.mp hTUχ ρ hρpos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev_ball.and hev_close)
      -- ### E7: the attainment step at each large index
      have attain : ∀ j, N ≤ j →
          ∃ zₐ : ℂ, dist zₐ p₀ < r ∧ f^[φ j] ((zₐ : ℂ̂)) = c := by
        intro j hj
        obtain ⟨hjball, hjclose⟩ := hN j hj
        obtain ⟨A, B, hAB⟩ := hread (φ j)
        have hBne : ∀ z ∈ Metric.closedBall p₀ δ, B.eval z ≠ 0 := fun z hz =>
          (hAB z (lt_trans (hjball z hz) (by linarith))).1
        have hFeq : ∀ z ∈ Metric.closedBall p₀ δ,
            χ (f^[φ j] ((z : ℂ̂))) = A.eval z / B.eval z := fun z hz =>
          (hAB z (lt_trans (hjball z hz) (by linarith))).2
        have hp₀cb : p₀ ∈ Metric.closedBall p₀ δ :=
          Metric.mem_closedBall_self hδpos.le
        -- the reading at the center and its closeness to `χ c`
        set q₀ : ℂ := A.eval p₀ / B.eval p₀ with hq₀def
        have hq₀close : ‖q₀ - χ c‖ < ρ := by
          have h1 := hjclose p₀ hp₀cb
          rw [dist_eq_norm] at h1
          have h2 : G p₀ = χ c := by simp only [hGdef, hcdef]
          rw [h2, hFeq p₀ hp₀cb] at h1
          rw [norm_sub_rev] at h1
          exact h1
        -- the reading curve over the circle
        have hΓcont : Continuous fun t : I => A.eval (cir t) / B.eval (cir t) :=
          (A.continuous.comp cir.continuous).div
            (B.continuous.comp cir.continuous)
            (fun t => hBne (cir t) (hcir_mem_cball t))
        set Γ : C(I, ℂ) := ⟨fun t => A.eval (cir t) / B.eval (cir t), hΓcont⟩
          with hΓdef
        have hΓ_apply : ∀ t : I, Γ t = A.eval (cir t) / B.eval (cir t) :=
          fun t => rfl
        have hΓ_read : ∀ t : I, Γ t = χ (f^[φ j] (((cir t) : ℂ̂))) :=
          fun t => (hFeq (cir t) (hcir_mem_cball t)).symm
        have hΓcl : Γ 0 = Γ 1 := by
          rw [hΓ_apply, hΓ_apply, hcir_cl]
        -- distance estimates for the reading curve
        have hΓfar : ∀ t : I, 3 * ρ < ‖Γ t - χ c‖ := by
          intro t
          have h2 := hGfar t
          have h3 : ‖G (cir t) - χ c‖ ≤ ‖G (cir t) - Γ t‖ + ‖Γ t - χ c‖ := by
            have h0 := dist_triangle (G (cir t)) (Γ t) (χ c)
            rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h0
            exact h0
          have h4 : ‖G (cir t) - Γ t‖ < ρ := by
            have h5 := hjclose (cir t) (hcir_mem_cball t)
            rw [dist_eq_norm] at h5
            rw [← hΓ_read t] at h5
            exact h5
          linarith
        have hΓq₀far : ∀ t : I, 2 * ρ < ‖Γ t - q₀‖ := by
          intro t
          have h1 := hΓfar t
          have h3 : ‖Γ t - χ c‖ ≤ ‖Γ t - q₀‖ + ‖q₀ - χ c‖ := by
            have h0 := dist_triangle (Γ t) q₀ (χ c)
            rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h0
            exact h0
          linarith [hq₀close]
        -- winding of composed polynomial curves over the circle
        have hpoly_wind : ∀ P : Polynomial ℂ, (∀ t : I, P.eval (cir t) ≠ 0) →
            windingNumber ⟨fun t => P.eval (cir t),
              P.continuous.comp cir.continuous⟩ 0 =
              (P.roots.map fun ζ => windingNumber cir ζ).sum := by
          intro P hP
          have hPne : P ≠ 0 := by
            intro h0
            apply hP 0
            rw [h0]
            simp
          exact windingNumber_polynomial_comp P hPne cir hcir_cl hP
        have hBcirc_ne : ∀ t : I, B.eval (cir t) ≠ 0 :=
          fun t => hBne (cir t) (hcir_mem_cball t)
        have hBwind : windingNumber ⟨fun t => B.eval (cir t),
            B.continuous.comp cir.continuous⟩ 0 = 0 := by
          rw [hpoly_wind B hBcirc_ne]
          refine Multiset.sum_eq_zero ?_
          intro x hx
          obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
          apply hwind_out
          by_contra hle
          push Not at hle
          exact hBne ζ (Metric.mem_closedBall.mpr (le_trans hle hrδ.le))
            (Polynomial.isRoot_of_mem_roots hζ)
        -- generic facts about the shifted polynomials `A - q·B`
        have hTeval : ∀ (q : ℂ) (t : I), (A - Polynomial.C q * B).eval (cir t)
            = (Γ t - q) * B.eval (cir t) := by
          intro q t
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
          rw [hΓ_apply t, sub_mul, div_mul_cancel₀ _ (hBcirc_ne t)]
        have hTcirc_ne : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            ∀ t : I, (A - Polynomial.C q * B).eval (cir t) ≠ 0 := by
          intro q hq t
          rw [hTeval q t]
          exact mul_ne_zero (sub_ne_zero.mpr (hq t)) (hBcirc_ne t)
        have hTne : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            A - Polynomial.C q * B ≠ 0 := by
          intro q hq h0
          exact hTcirc_ne q hq 0 (by rw [h0]; simp)
        have hroots_ne_r : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            ∀ ζ ∈ (A - Polynomial.C q * B).roots, dist ζ p₀ ≠ r := by
          intro q hq ζ hζ heq
          obtain ⟨t, rfl⟩ := hcir_surj ζ heq
          exact hTcirc_ne q hq t (Polynomial.isRoot_of_mem_roots hζ)
        -- the master winding identity for the reading curve
        have hwindΓ : ∀ (q : ℂ), (∀ t : I, Γ t ≠ q) →
            windingNumber Γ q =
              ((A - Polynomial.C q * B).roots.map
                fun ζ => windingNumber cir ζ).sum := by
          intro q hq
          have hcl₁ : (shiftedCurve Γ q) 0 = (shiftedCurve Γ q) 1 := by
            change Γ 0 - q = Γ 1 - q
            rw [hΓcl]
          have h₁ : ∀ t : I, (shiftedCurve Γ q) t ≠ 0 := by
            intro t
            change Γ t - q ≠ 0
            exact sub_ne_zero.mpr (hq t)
          have hcl₂ : (⟨fun t => B.eval (cir t),
              B.continuous.comp cir.continuous⟩ : C(I, ℂ)) 0 =
              (⟨fun t => B.eval (cir t),
              B.continuous.comp cir.continuous⟩ : C(I, ℂ)) 1 := by
            change B.eval (cir 0) = B.eval (cir 1)
            rw [hcir_cl]
          have h₂ : ∀ t : I, (⟨fun t => B.eval (cir t),
              B.continuous.comp cir.continuous⟩ : C(I, ℂ)) t ≠ 0 := hBcirc_ne
          have hmul := windingNumber_mul (shiftedCurve Γ q)
            ⟨fun t => B.eval (cir t), B.continuous.comp cir.continuous⟩
            hcl₁ hcl₂ h₁ h₂
          have hprodeq : (⟨fun t => (A - Polynomial.C q * B).eval (cir t),
              (A - Polynomial.C q * B).continuous.comp cir.continuous⟩ :
                C(I, ℂ)) =
              shiftedCurve Γ q * ⟨fun t => B.eval (cir t),
                B.continuous.comp cir.continuous⟩ := by
            ext t
            change (A - Polynomial.C q * B).eval (cir t) =
              (Γ t - q) * B.eval (cir t)
            exact hTeval q t
          rw [← hpoly_wind (A - Polynomial.C q * B) (hTcirc_ne q hq), hprodeq,
            hmul, windKey Γ q, hBwind, add_zero]
        -- the curve avoids both test points
        have hq₀ne : ∀ t : I, Γ t ≠ q₀ := by
          intro t h0
          have h1 := hΓq₀far t
          rw [h0, sub_self, norm_zero] at h1
          linarith
        have hχcne : ∀ t : I, Γ t ≠ χ c := by
          intro t h0
          have h1 := hΓfar t
          rw [h0, sub_self, norm_zero] at h1
          linarith
        -- winding about the center reading is at least one
        have hone : (1 : ℤ) ≤ windingNumber Γ q₀ := by
          rw [hwindΓ q₀ hq₀ne]
          have hmem : p₀ ∈ (A - Polynomial.C q₀ * B).roots := by
            rw [Polynomial.mem_roots']
            refine ⟨hTne q₀ hq₀ne, ?_⟩
            change (A - Polynomial.C q₀ * B).eval p₀ = 0
            simp only [Polynomial.eval_sub, Polynomial.eval_mul,
              Polynomial.eval_C]
            rw [hq₀def, div_mul_cancel₀ _ (hBne p₀ hp₀cb), sub_self]
          have hmem1 : (1 : ℤ) ∈ (A - Polynomial.C q₀ * B).roots.map
              fun ζ => windingNumber cir ζ := by
            rw [← hwind_in p₀ (by rw [dist_self]; exact hrpos)]
            exact Multiset.mem_map_of_mem _ hmem
          refine Multiset.single_le_sum ?_ _ hmem1
          intro x hx
          obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
          rcases lt_trichotomy (dist ζ p₀) r with hlt | heq | hgt
          · rw [hwind_in ζ hlt]
            exact zero_le_one
          · exact absurd heq (hroots_ne_r q₀ hq₀ne ζ hζ)
          · rw [hwind_out ζ hgt]
        -- transfer the lower bound to the limit reading `χ c`
        have htrans : windingNumber Γ (χ c) = windingNumber Γ q₀ := by
          have hC : IsPreconnected
              ((fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1) :=
            isPreconnected_Icc.image _
              (continuous_const.add
                (Complex.continuous_ofReal.mul continuous_const)).continuousOn
          have hdisj : ∀ t : I, Γ t ∉
              (fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1 := by
            rintro t ⟨θ, hθ, hteq⟩
            have h1 := hΓfar t
            rw [← hteq, add_sub_cancel_left, norm_mul, Complex.norm_real,
              Real.norm_eq_abs] at h1
            have habs : |θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
            nlinarith [norm_nonneg (q₀ - χ c), abs_nonneg θ, hq₀close, hρpos]
          have hq₁C : χ c ∈
              (fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1 :=
            ⟨0, ⟨le_refl 0, zero_le_one⟩,
              by change χ c + ((0 : ℝ) : ℂ) * (q₀ - χ c) = χ c; push_cast; ring⟩
          have hq₂C : q₀ ∈
              (fun θ : ℝ => χ c + (θ : ℂ) * (q₀ - χ c)) '' Set.Icc 0 1 :=
            ⟨1, ⟨zero_le_one, le_refl 1⟩,
              by change χ c + ((1 : ℝ) : ℂ) * (q₀ - χ c) = q₀; push_cast; ring⟩
          exact windingNumber_eq_of_preconnected hΓcl hC hdisj hq₁C hq₂C
        -- a root of `A - χ c · B` inside the open disk
        obtain ⟨ζ, hζroot, hζin⟩ : ∃ ζ ∈ (A - Polynomial.C (χ c) * B).roots,
            dist ζ p₀ < r := by
          by_contra hnone
          push Not at hnone
          have honeχ : (1 : ℤ) ≤ windingNumber Γ (χ c) := by
            rw [htrans]
            exact hone
          have hzero : ((A - Polynomial.C (χ c) * B).roots.map
              fun ζ => windingNumber cir ζ).sum = 0 := by
            refine Multiset.sum_eq_zero ?_
            intro x hx
            obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
            rcases lt_trichotomy (dist ζ p₀) r with hlt | heq | hgt
            · exact absurd hlt (not_lt.mpr (hnone ζ hζ))
            · exact absurd heq (hroots_ne_r (χ c) hχcne ζ hζ)
            · exact hwind_out ζ hgt
          rw [hwindΓ (χ c) hχcne, hzero] at honeχ
          exact absurd honeχ (by norm_num)
        -- decode the root into an attainment of `c`
        refine ⟨ζ, hζin, ?_⟩
        have hζcb : ζ ∈ Metric.closedBall p₀ δ :=
          Metric.mem_closedBall.mpr (le_trans hζin.le hrδ.le)
        have hζval : dist c (f^[φ j] ((ζ : ℂ̂))) < s :=
          lt_trans (hjball ζ hζcb) (by linarith)
        have hroot : (A - Polynomial.C (χ c) * B).eval ζ = 0 :=
          Polynomial.isRoot_of_mem_roots hζroot
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C] at hroot
        have hBζ := (hAB ζ hζval).1
        have hχeq : χ (f^[φ j] ((ζ : ℂ̂))) = χ c := by
          rw [(hAB ζ hζval).2, div_eq_iff hBζ]
          linear_combination hroot
        exact hχinj _ _ hζval (by rw [dist_self]; exact hs) hχeq
      -- ### E8: two attainments contradict the wandering disjointness
      obtain ⟨z₁, hz₁r, hz₁⟩ := attain N (le_refl N)
      obtain ⟨z₂, hz₂r, hz₂⟩ := attain (N + 1) (Nat.le_succ N)
      have hz₁U : ((z₁ : ℂ̂)) ∈ U :=
        hKU (interior_subset (hδprop z₁
          (Metric.mem_closedBall.mpr (le_trans hz₁r.le hrδ.le))).1)
      have hz₂U : ((z₂ : ℂ̂)) ∈ U :=
        hKU (interior_subset (hδprop z₂
          (Metric.mem_closedBall.mpr (le_trans hz₂r.le hrδ.le))).1)
      have hmem₁ : c ∈ fcOrbit f U (φ N) := by
        rw [← hz₁]
        exact hmem_orbit (φ N) _ hz₁U
      have hmem₂ : c ∈ fcOrbit f U (φ (N + 1)) := by
        rw [← hz₂]
        exact hmem_orbit (φ (N + 1)) _ hz₂U
      have hneq : φ N ≠ φ (N + 1) := ne_of_lt (hφ (Nat.lt_succ_self N))
      exact Set.disjoint_left.mp (hW hneq) hmem₁ hmem₂
  -- ## Stage 3: local constancy everywhere on `interior K` (∞ via puncturing)
  have hloc : ∀ w ∈ interior K, ∀ᶠ w' in 𝓝 w, g w' = g w := by
    intro w hw
    cases w with
    | coe p₀ => exact key p₀ hw
    | infty =>
      obtain ⟨S₀, ⟨hS₀cl, hS₀cp⟩, hS₀sub⟩ :=
        (OnePoint.hasBasis_nhds_infty (X := ℂ)).mem_iff.mp (hopenK.mem_nhds hw)
      obtain ⟨R₀, hR₀⟩ := hS₀cp.isBounded.subset_closedBall 0
      have hR1 : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
      have hRpos : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos hR1
      set R : ℝ := max R₀ 1 with hRdef
      -- large-norm points decode into `interior K`
      have hWK : ∀ z : ℂ, R < ‖z‖ → ((z : ℂ̂)) ∈ interior K := by
        intro z hz
        apply hS₀sub
        refine Or.inl ⟨z, fun hzS₀ => ?_, rfl⟩
        have h1 : ‖z‖ ≤ R₀ := by
          have h2 := hR₀ hzS₀
          rwa [Metric.mem_closedBall, dist_zero_right] at h2
        exact absurd hz (not_lt.mpr (h1.trans (le_max_left _ _)))
      -- the punctured plane neighborhood is preconnected
      have hWpre : IsPreconnected {z : ℂ | R < ‖z‖} := by
        have himg : {z : ℂ | R < ‖z‖} =
            (fun p : ℝ × ℝ => ((p.1 : ℂ)) * Complex.exp ((p.2 : ℂ) * Complex.I)) ''
              (Set.Ioi R ×ˢ Set.univ) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
            Set.mem_univ, and_true, Prod.exists]
          constructor
          · intro hz
            exact ⟨‖z‖, Complex.arg z, hz, Complex.norm_mul_exp_arg_mul_I z⟩
          · rintro ⟨t, θ, ht, rfl⟩
            rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (lt_trans hRpos ht)]
            exact ht
        rw [himg]
        exact (isPreconnected_Ioi.prod isPreconnected_univ).image _
          ((Complex.continuous_ofReal.comp continuous_fst).mul
            (Complex.continuous_exp.comp
              ((Complex.continuous_ofReal.comp continuous_snd).mul
                continuous_const))).continuousOn
      have hW'pre : IsPreconnected
          ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) :=
        hWpre.image _ OnePoint.continuous_coe.continuousOn
      have hz₀W : R < ‖((2 * R : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      -- constancy on the decoded punctured neighborhood
      have hconst : ∀ z : ℂ, R < ‖z‖ →
          g ((z : ℂ̂)) = g ((((2 * R : ℝ) : ℂ) : ℂ̂)) := by
        intro z hz
        refine clopen_const _ hW'pre ?_ _ ⟨z, hz, rfl⟩ _
          ⟨((2 * R : ℝ) : ℂ), hz₀W, rfl⟩
        rintro u ⟨zu, hzu, rfl⟩
        exact key zu (hWK zu hzu)
      -- `∞` lies in the closure of the decoded punctured neighborhood
      have hclinf : (∞ : ℂ̂) ∈ closure
          ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) := by
        rw [mem_closure_iff_nhds_basis (OnePoint.hasBasis_nhds_infty (X := ℂ))]
        rintro T ⟨hTcl, hTcp⟩
        obtain ⟨R₁, hR₁⟩ := hTcp.isBounded.subset_closedBall 0
        have hbig : R < ‖((max R R₁ + 1 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith [le_max_left R R₁])]
          linarith [le_max_left R R₁]
        refine ⟨((((max R R₁ + 1 : ℝ) : ℂ)) : ℂ̂),
          ⟨((max R R₁ + 1 : ℝ) : ℂ), hbig, rfl⟩, Or.inl ⟨_, fun hmem => ?_, rfl⟩⟩
        have h2 := hR₁ hmem
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith [le_max_left R R₁])] at h2
        linarith [le_max_right R R₁]
      -- `g ∞` agrees with the constant value
      have hginf : g (∞ : ℂ̂) = g ((((2 * R : ℝ) : ℂ) : ℂ̂)) := by
        have hcw : ContinuousWithinAt g
            ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) ∞ :=
          (hgcont.continuousAt (hopenK.mem_nhds hw)).continuousWithinAt
        have h1 := hcw.mem_closure_image hclinf
        have h2 : g '' ((fun z : ℂ => ((z : ℂ̂))) '' {z : ℂ | R < ‖z‖}) ⊆
            {g ((((2 * R : ℝ) : ℂ) : ℂ̂))} := by
          rintro - ⟨-, ⟨zu, hzu, rfl⟩, rfl⟩
          exact hconst zu hzu
        have h3 := closure_mono h2 h1
        rwa [closure_singleton, Set.mem_singleton_iff] at h3
      -- conclude the eventual equality at `∞`
      have hnbhd : ((fun z : ℂ => ((z : ℂ̂))) '' (Metric.closedBall (0 : ℂ) R)ᶜ ∪
          {∞}) ∈ 𝓝 (∞ : ℂ̂) :=
        (OnePoint.hasBasis_nhds_infty (X := ℂ)).mem_of_mem
          ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩
      filter_upwards [hnbhd] with w' hw'
      rcases hw' with ⟨zw, hzw, rfl⟩ | hw'
      · have hzwn : R < ‖zw‖ := by
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hzw
          exact hzw
        rw [hconst zw hzwn, hginf]
      · rw [Set.mem_singleton_iff] at hw'
        rw [hw']
  -- ## Stage 4: finale
  intro x hx y hy hVeq
  have hyV : y ∈ connectedComponentIn (interior K) x := by
    rw [hVeq]
    exact mem_connectedComponentIn hy
  exact clopen_const _ isPreconnected_connectedComponentIn
    (fun w hw => hloc w (connectedComponentIn_subset _ _ hw))
    x (mem_connectedComponentIn hx) y hyV

set_option maxHeartbeats 400000 in
-- The collapse/confinement contradiction elaborates as one large declaration whose
-- nested winding-growth and continuum `have` chains exceed the default budget.
/-- **Collapse and confinement contradiction.** Unbounded winding growth of
the iterated image curves about Julia-meeting continua is impossible:
normality of the iterates on the loop's compact trace makes subsequential
limits constant on the wandering orbit, winding stability then collapses the
continua and the curves to a common point, the maximum principle confines
the enclosed regions along the forward orbit, and normality at a boundary
Julia point of a confined region contradicts membership in the Julia set. -/
theorem not_winding_growth {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀)
    (hgrow : ∀ B : ℤ, ∃ m : ℕ, ∃ C : Set ℂ,
      C.Nonempty ∧ IsPreconnected C ∧ IsCompact C ∧
      (∃ z ∈ C, ((z : ℂ̂)) ∈ JuliaSet f) ∧
      (∀ z ∈ C, ((z : ℂ̂)) ∉ fcOrbit f U (N₀ + m)) ∧
      (∀ t : unitInterval, ((chartFiniteMap (f^[m] ((γ t : ℂ̂))) : ℂ)) ∉ C) ∧
      ∃ Γ : C(unitInterval, ℂ), (∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂)))) ∧
        ∀ z ∈ C, B ≤ |windingNumber Γ z|) :
    False := by
  classical
  -- ===== Stage 0: basic dynamical facts =====
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hcf : Continuous f := hf.continuous
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
  have hcont_iter : ∀ k : ℕ, Continuous (f^[k]) := fun k => hcf.iterate k
  have hopen_iter : ∀ k : ℕ, IsOpenMap (f^[k]) := by
    intro k
    induction k with
    | zero => exact IsOpenMap.id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hfo.comp ih
  have hcoe_cont : Continuous ((↑) : ℂ → ℂ̂) := OnePoint.continuous_coe
  have hcoe_open : IsOpenMap ((↑) : ℂ → ℂ̂) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap
  have hcoe_chart : ∀ x : ℂ̂, x ≠ ∞ → ((chartFiniteMap x : ℂ) : ℂ̂) = x := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe w => rfl
  -- every subset of the (compact) sphere is bounded
  have hbdd : ∀ s : Set ℂ̂, Bornology.IsBounded s := fun s =>
    (isCompact_univ.isBounded).subset (Set.subset_univ s)
  -- orbit membership of the iterated curve
  have himg : ∀ n : ℕ, f^[n] '' (fcOrbit f U N₀) = fcOrbit f U (N₀ + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ', Set.image_comp, ih,
          fcOrbit_image_eq hf hd1 hU (N₀ + n), Nat.add_assoc]
  have hmem : ∀ (n : ℕ) (t : unitInterval),
      f^[n] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + n) := by
    intro n t
    rw [← himg n]
    exact Set.mem_image_of_mem _ (hγmem t)
  have hne_inf : ∀ (n : ℕ) (t : unitInterval), f^[n] ((γ t : ℂ̂)) ≠ ∞ := by
    intro n t h
    exact hinf (N₀ + n) (h ▸ hmem n t)
  have hVfc : IsFatouComponent f (fcOrbit f U N₀) :=
    isFatouComponent_fcOrbit N₀ hf hd1 hU
  have hVopen : IsOpen (fcOrbit f U N₀) := hVfc.isOpen
  have hVFat : ∀ n : ℕ, fcOrbit f U (N₀ + n) ⊆ FatouSet f := fun n =>
    (isFatouComponent_fcOrbit (N₀ + n) hf hd1 hU).subset_fatouSet
  -- ===== the sphere traces of the iterated curve =====
  set T : ℕ → Set ℂ̂ := fun ν => Set.range (fun t : unitInterval => f^[ν] ((γ t : ℂ̂)))
    with hTdef
  have hTcont : ∀ ν : ℕ, Continuous (fun t : unitInterval => f^[ν] ((γ t : ℂ̂))) :=
    fun ν => (hcont_iter ν).comp (hcoe_cont.comp γ.continuous)
  have hTcompact : ∀ ν : ℕ, IsCompact (T ν) := fun ν => isCompact_range (hTcont ν)
  set yy : ℕ → ℂ̂ := fun ν => f^[ν] ((γ 0 : ℂ̂)) with hyydef
  have hyT : ∀ ν : ℕ, yy ν ∈ T ν := fun ν => ⟨0, rfl⟩
  have hTsubB : ∀ ν : ℕ, T ν ⊆ Metric.closedBall (yy ν) (Metric.diam (T ν)) := by
    intro ν x hx
    exact Metric.mem_closedBall.mpr (Metric.dist_le_diam_of_mem (hbdd _) hx (hyT ν))
  have hfT : ∀ ν : ℕ, f '' T ν = T (ν + 1) := by
    intro ν
    rw [hTdef]
    rw [← Set.range_comp]
    congr 1
    funext t
    exact (Function.iterate_succ_apply' f ν _).symm
  have hTinf : ∀ ν : ℕ, ∞ ∉ T ν := by
    rintro ν ⟨t, ht⟩
    exact hne_inf ν t ht
  have hTFat : ∀ ν : ℕ, T ν ⊆ FatouSet f := by
    rintro ν _ ⟨t, rfl⟩
    exact hVFat ν (hmem ν t)
  -- ===== Stage 0': data extraction from the growth hypothesis =====
  have hgrow' : ∀ j : ℕ, ∃ mm : ℕ, ∃ C : Set ℂ,
      C.Nonempty ∧ IsPreconnected C ∧ IsCompact C ∧
      (∃ z ∈ C, ((z : ℂ̂)) ∈ JuliaSet f) ∧
      (∀ z ∈ C, ((z : ℂ̂)) ∉ fcOrbit f U (N₀ + mm)) ∧
      (∀ t : unitInterval, ((chartFiniteMap (f^[mm] ((γ t : ℂ̂))) : ℂ)) ∉ C) ∧
      ∃ Γ : C(unitInterval, ℂ),
        (∀ t : unitInterval, Γ t = chartFiniteMap (f^[mm] ((γ t : ℂ̂)))) ∧
        ∀ z ∈ C, (j : ℤ) + 1 ≤ |windingNumber Γ z| :=
    fun j => hgrow ((j : ℤ) + 1)
  choose m Cc hCne hCpre hCcomp hCJ hCav hcav Γf hΓeq hwind using hgrow'
  have hΓcl : ∀ j : ℕ, Γf j 0 = Γf j 1 := by
    intro j
    rw [hΓeq j 0, hΓeq j 1, hγcl]
  have hΓsphere : ∀ (j : ℕ) (t : unitInterval),
      ((Γf j t : ℂ) : ℂ̂) = f^[m j] ((γ t : ℂ̂)) := by
    intro j t
    rw [hΓeq]
    exact hcoe_chart _ (hne_inf (m j) t)
  have hΓrange : ∀ j : ℕ,
      (fun z : ℂ => (z : ℂ̂)) '' (Set.range ⇑(Γf j)) = T (m j) := by
    intro j
    rw [hTdef, ← Set.range_comp]
    congr 1
    funext t
    exact hΓsphere j t
  -- the Julia witness of `Cc j` is not on the curve, and has nonzero winding
  have hznr : ∀ (j : ℕ) (z : ℂ), z ∈ Cc j → z ∉ Set.range ⇑(Γf j) := by
    rintro j z hz ⟨t, ht⟩
    have := hcav j t
    rw [← hΓeq j t, ht] at this
    exact this hz
  have hzw : ∀ (j : ℕ) (z : ℂ), z ∈ Cc j → windingNumber (Γf j) z ≠ 0 := by
    intro j z hz h0
    have h1 := hwind j z hz
    rw [h0] at h1
    simp at h1
    omega
  -- ===== small topological toolkit =====
  -- (E) two-set dichotomy for a preconnected set avoiding the frontier
  have hdichot : ∀ (G A : Set ℂ̂), IsOpen G → IsPreconnected A →
      (A ∩ frontier G = ∅) → A ⊆ G ∨ A ∩ G = ∅ := by
    intro G A hG hA hAF
    by_cases hAG : A ∩ G = ∅
    · exact Or.inr hAG
    · left
      have hcover : A ⊆ G ∪ (closure G)ᶜ := by
        intro a ha
        by_cases haG : a ∈ G
        · exact Or.inl haG
        · refine Or.inr fun hacl => ?_
          have : a ∈ A ∩ frontier G := ⟨ha, hacl, fun hi => haG (interior_subset hi)⟩
          rw [hAF] at this
          exact this
      by_cases hA2 : A ∩ (closure G)ᶜ = ∅
      · intro a ha
        rcases hcover ha with h | h
        · exact h
        · exact absurd (Set.mem_inter ha h) (by rw [hA2]; exact fun h => h)
      · exfalso
        obtain ⟨a₁, ha₁⟩ := Set.nonempty_iff_ne_empty.mpr hAG
        obtain ⟨a₂, ha₂⟩ := Set.nonempty_iff_ne_empty.mpr hA2
        obtain ⟨x, hx⟩ := hA G (closure G)ᶜ hG isClosed_closure.isOpen_compl
          hcover ⟨a₁, ha₁.1, ha₁.2⟩ ⟨a₂, ha₂.1, ha₂.2⟩
        exact hx.2.2 (subset_closure hx.2.1)
  -- (B) frontier of an image under the (continuous, open) map `f`
  have hfrontier_image : ∀ G : Set ℂ̂, IsOpen G →
      frontier (f '' G) ⊆ f '' frontier G := by
    intro G hG x hx
    have hopen : IsOpen (f '' G) := hfo _ hG
    have hxcl : x ∈ closure (f '' G) := hx.1
    have hxni : x ∉ f '' G := by
      intro hmem
      exact hx.2 (by rw [hopen.interior_eq]; exact hmem)
    have hclos : closure (f '' G) ⊆ f '' closure G := by
      apply closure_minimal (Set.image_mono subset_closure)
      exact ((isClosed_closure.isCompact).image hcf).isClosed
    obtain ⟨d, hd', rfl⟩ := hclos hxcl
    have hdG : d ∉ G := fun hdG => hxni ⟨d, hdG, rfl⟩
    exact ⟨d, ⟨hd', fun hi => hdG (hG.interior_eq ▸ hi)⟩, rfl⟩
  -- (C) frontier of the sphere reading of a bounded open plane set
  have hfrontier_coe : ∀ S : Set ℂ, IsOpen S → Bornology.IsBounded S →
      frontier ((fun z : ℂ => (z : ℂ̂)) '' S) ⊆
        (fun z : ℂ => (z : ℂ̂)) '' frontier S := by
    intro S hSo hSb x hx
    have hopen : IsOpen ((fun z : ℂ => (z : ℂ̂)) '' S) := hcoe_open _ hSo
    have hxcl : x ∈ closure ((fun z : ℂ => (z : ℂ̂)) '' S) := hx.1
    have hxni : x ∉ (fun z : ℂ => (z : ℂ̂)) '' S := by
      intro hmem
      exact hx.2 (by rw [hopen.interior_eq]; exact hmem)
    have hclos : closure ((fun z : ℂ => (z : ℂ̂)) '' S) ⊆
        (fun z : ℂ => (z : ℂ̂)) '' closure S := by
      apply closure_minimal (Set.image_mono subset_closure)
      exact ((hSb.isCompact_closure).image hcoe_cont).isClosed
    obtain ⟨d, hd', rfl⟩ := hclos hxcl
    have hdS : d ∉ S := fun hdS => hxni ⟨d, hdS, rfl⟩
    exact ⟨d, ⟨hd', fun hi => hdS (hSo.interior_eq ▸ hi)⟩, rfl⟩
  -- (A) complements of closed balls in the sphere are preconnected
  have hcompl_ball_conn : ∀ (y : ℂ̂) (r : ℝ), 0 ≤ r →
      IsPreconnected ((Metric.closedBall y r)ᶜ : Set ℂ̂) := by
    intro y r hr
    -- helper: exteriors (in the squared-norm form) are preconnected in ℂ
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact_mod_cast (by norm_num : (1:ℕ) < 2)
    have hext : ∀ (mid : ℂ) (ρ : ℝ), IsPreconnected {z : ℂ | ρ < ‖z - mid‖^2} := by
      intro mid ρ
      rcases lt_trichotomy ρ 0 with hρ | hρ | hρ
      · have huniv : {z : ℂ | ρ < ‖z - mid‖^2} = Set.univ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          nlinarith [sq_nonneg ‖z - mid‖]
        rw [huniv]
        exact isPreconnected_univ
      · subst hρ
        have hpunct : {z : ℂ | (0:ℝ) < ‖z - mid‖^2} = {mid}ᶜ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
          constructor
          · intro h he
            rw [he] at h
            simp at h
          · intro h
            have hz : z - mid ≠ 0 := sub_ne_zero.mpr h
            positivity
        rw [hpunct]
        exact (isConnected_compl_singleton_of_one_lt_rank hrank mid).isPreconnected
      · have hsq : ∀ z : ℂ, (ρ < ‖z - mid‖^2 ↔ Real.sqrt ρ < ‖z - mid‖) := by
          intro z
          rw [show (Real.sqrt ρ < ‖z - mid‖) ↔ ((Real.sqrt ρ)^2 < ‖z - mid‖^2) from
            (sq_lt_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).symm,
            Real.sq_sqrt hρ.le]
        have hs' : {z : ℂ | ρ < ‖z - mid‖^2} =
            (fun p : ℝ × ℂ => mid + (p.1 : ℂ) * p.2) ''
              ((Set.Ioi (Real.sqrt ρ)) ×ˢ (Metric.sphere (0:ℂ) 1)) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
            Metric.mem_sphere, dist_zero_right, hsq z]
          constructor
          · intro hz
            have hzpos : 0 < ‖z - mid‖ := lt_of_le_of_lt (Real.sqrt_nonneg _) hz
            have hzne : (‖z - mid‖ : ℂ) ≠ 0 := by
              exact_mod_cast (ne_of_gt hzpos)
            refine ⟨(‖z - mid‖, (‖z - mid‖ : ℂ)⁻¹ * (z - mid)), ⟨hz, ?_⟩, ?_⟩
            · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hzpos, inv_mul_cancel₀ hzpos.ne']
            · change mid + (‖z - mid‖ : ℂ) * ((‖z - mid‖ : ℂ)⁻¹ * (z - mid)) = z
              rw [← mul_assoc, mul_inv_cancel₀ hzne, one_mul]
              ring
          · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
            have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
            change Real.sqrt ρ < ‖mid + (t : ℂ) * u - mid‖
            rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos htpos, hu, mul_one]
            exact ht
        rw [hs']
        apply IsPreconnected.image
        · exact isPreconnected_Ioi.prod
            (isConnected_sphere hrank 0 zero_le_one).isPreconnected
        · exact (continuous_const.add
            ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd)).continuousOn
    -- describe the complement of the ball via the spherical distance
    have hset : ((Metric.closedBall y r)ᶜ : Set ℂ̂) = {w : ℂ̂ | r < sphericalDist y w} := by
      ext w
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, Set.mem_setOf_eq, not_le]
      rw [show dist w y = sphericalDist w y from rfl, sphericalDist_comm]
    rw [hset]
    induction y using OnePoint.rec with
    | infty =>
        -- the complement is the sphere reading of a plane convex set
        have hshape : {w : ℂ̂ | r < sphericalDist ∞ w} =
            (fun z : ℂ => (z : ℂ̂)) '' {z : ℂ | r < chordalDistInfty z} := by
          ext w
          induction w using OnePoint.rec with
          | infty =>
              simp only [Set.mem_setOf_eq]
              constructor
              · intro h
                rw [show sphericalDist ∞ ∞ = (0:ℝ) from rfl] at h
                exact absurd h (not_lt.mpr hr)
              · rintro ⟨z, _, hcontra⟩
                exact absurd hcontra (OnePoint.coe_ne_infty z)
          | coe z =>
              simp only [Set.mem_setOf_eq]
              rw [show sphericalDist ∞ ((z:ℂ̂)) = chordalDistInfty z from rfl]
              constructor
              · intro h
                exact ⟨z, h, rfl⟩
              · rintro ⟨z', hz', heq⟩
                rwa [← OnePoint.coe_eq_coe.mp heq]
        rw [hshape]
        have hEconv : Convex ℝ {z : ℂ | r < chordalDistInfty z} := by
          have hEeq : {z : ℂ | r < chordalDistInfty z} =
              {z : ℂ | r^2 * (1+‖z‖^2) < 4} := by
            ext z
            simp only [Set.mem_setOf_eq]
            unfold chordalDistInfty
            have hX : (0:ℝ) < 1 + ‖z‖^2 := by positivity
            have hsX : (0:ℝ) < Real.sqrt (1+‖z‖^2) := Real.sqrt_pos.mpr hX
            rw [lt_div_iff₀ hsX]
            constructor
            · intro h
              have h2 : (r * Real.sqrt (1+‖z‖^2))^2 < 2^2 :=
                (sq_lt_sq₀ (by positivity) (by norm_num)).mpr h
              rw [mul_pow, Real.sq_sqrt hX.le] at h2
              linarith
            · intro h
              have h2 : (r * Real.sqrt (1+‖z‖^2))^2 < 2^2 := by
                rw [mul_pow, Real.sq_sqrt hX.le]
                linarith
              exact (sq_lt_sq₀ (by positivity) (by norm_num)).mp h2
          rw [hEeq]
          rcases eq_or_lt_of_le hr with h0 | hrpos
          · have huniv : {z : ℂ | r^2 * (1+‖z‖^2) < 4} = Set.univ := by
              ext z
              simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, ← h0]
              norm_num
            rw [huniv]
            exact convex_univ
          · by_cases hbig : (4:ℝ) ≤ r^2
            · have hempty : {z : ℂ | r^2 * (1+‖z‖^2) < 4} = ∅ := by
                ext z
                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                nlinarith [sq_nonneg ‖z‖]
              rw [hempty]
              exact convex_empty
            · push Not at hbig
              have hr2 : (0:ℝ) < r^2 := by positivity
              have hball : {z : ℂ | r^2 * (1+‖z‖^2) < 4} =
                  Metric.ball (0:ℂ) (Real.sqrt (4/r^2 - 1)) := by
                ext z
                simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
                rw [show (‖z‖ < Real.sqrt (4/r^2-1)) ↔ (‖z‖^2 < 4/r^2 - 1) from
                  Real.lt_sqrt (norm_nonneg z)]
                constructor
                · intro h
                  rw [lt_sub_iff_add_lt, lt_div_iff₀ hr2]
                  nlinarith
                · intro h
                  rw [lt_sub_iff_add_lt, lt_div_iff₀ hr2] at h
                  nlinarith
              rw [hball]
              exact convex_ball 0 _
        exact hEconv.isPreconnected.image _ (OnePoint.continuous_coe.continuousOn)
    | coe a =>
        have hA2pos : (0:ℝ) < 1 + ‖a‖^2 := by positivity
        -- finite-point characterization
        have hfin : ∀ z : ℂ, (r < sphericalDist ((a:ℂ̂)) ((z:ℂ̂)) ↔
            r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2) := by
          intro z
          rw [sphericalDist_coe_coe]
          unfold chordalDist
          have hX : (0:ℝ) < 1 + ‖z‖^2 := by positivity
          have hsA : (0:ℝ) < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr hA2pos
          have hsX : (0:ℝ) < Real.sqrt (1 + ‖z‖^2) := Real.sqrt_pos.mpr hX
          rw [lt_div_iff₀ (mul_pos hsA hsX), norm_sub_rev a z]
          constructor
          · intro h
            have h2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
            rw [mul_pow, mul_pow, Real.sq_sqrt hA2pos.le, Real.sq_sqrt hX.le,
              mul_pow] at h2
            nlinarith [h2]
          · intro h
            apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
            rw [mul_pow, mul_pow, Real.sq_sqrt hA2pos.le, Real.sq_sqrt hX.le,
              mul_pow]
            nlinarith [h]
        -- infinity characterization
        have hinfc : (r < sphericalDist ((a:ℂ̂)) ∞ ↔ r^2 * (1 + ‖a‖^2) < 4) := by
          rw [show sphericalDist ((a:ℂ̂)) ∞ = chordalDistInfty a from rfl]
          unfold chordalDistInfty
          have hsA : (0:ℝ) < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr hA2pos
          rw [lt_div_iff₀ hsA]
          constructor
          · intro h
            have h2 := (sq_lt_sq₀ (by positivity) (by norm_num)).mpr h
            rw [mul_pow, Real.sq_sqrt hA2pos.le] at h2
            linarith
          · intro h
            apply (sq_lt_sq₀ (by positivity) (by norm_num)).mp
            rw [mul_pow, Real.sq_sqrt hA2pos.le]
            linarith
        -- expansion of the recentered norm, for any nonzero scale factor
        have hmidexp : ∀ (β : ℝ), β ≠ 0 → ∀ z : ℂ,
            ‖z - ((4/β : ℝ) : ℂ) * a‖^2 =
              ‖z‖^2 - 2*((4/β))*(z * (starRingEnd ℂ) a).re + (4/β)^2*‖a‖^2 := by
          intro β hβne z
          have hconjmid : (starRingEnd ℂ) (((4/β : ℝ) : ℂ) * a) =
              ((4/β : ℝ) : ℂ) * (starRingEnd ℂ) a := by
            rw [map_mul, Complex.conj_ofReal]
          have hre : (z * (starRingEnd ℂ) (((4/β : ℝ) : ℂ) * a)).re =
              (4/β) * (z * (starRingEnd ℂ) a).re := by
            rw [hconjmid, show z * (((4/β:ℝ):ℂ) * (starRingEnd ℂ) a)
                = ((4/β:ℝ):ℂ) * (z * (starRingEnd ℂ) a) from by ring]
            simp [Complex.mul_re]
          have hnm : ‖((4/β : ℝ) : ℂ) * a‖^2 = (4/β)^2 * ‖a‖^2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm,
            ← Complex.sq_norm, hre, hnm]
          ring
        have hsubexp : ∀ z : ℂ, ‖z - a‖^2 =
            ‖z‖^2 - 2*(z * (starRingEnd ℂ) a).re + ‖a‖^2 := by
          intro z
          rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm]
          ring
        by_cases hβ : (0:ℝ) < 4 - r^2 * (1 + ‖a‖^2)
        · -- the ball misses ∞: exterior shape plus the point ∞
          have hβne0 : (4 - r^2 * (1 + ‖a‖^2)) ≠ 0 := ne_of_gt hβ
          obtain ⟨β, hβeq⟩ : ∃ b : ℝ, b = 4 - r^2 * (1 + ‖a‖^2) := ⟨_, rfl⟩
          have hβpos : 0 < β := hβeq ▸ hβ
          have hβne : β ≠ 0 := hβeq ▸ hβne0
          obtain ⟨mid, hmiddef⟩ : ∃ c : ℂ, c = ((4/β : ℝ) : ℂ) * a := ⟨_, rfl⟩
          obtain ⟨ρ, hρdef⟩ : ∃ p : ℝ,
            p = (16*‖a‖^2 - β*(4*‖a‖^2 - r^2*(1 + ‖a‖^2)))/β^2 := ⟨_, rfl⟩
          have hkey : ∀ z : ℂ, β^2 * (‖z - mid‖^2 - ρ) =
              β * (4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2)) := by
            intro z
            rw [hmiddef, hmidexp β hβne z, hsubexp z, hρdef, hβeq]
            field_simp
            ring
          have hEeq : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
              ρ < ‖z - mid‖^2) := by
            intro z
            constructor
            · intro h
              by_contra hno
              push Not at hno
              have hle : β^2*(‖z - mid‖^2 - ρ) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) (by linarith)
              rw [hkey z] at hle
              linarith [mul_pos hβpos
                (by linarith : (0:ℝ) < 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2))]
            · intro h
              by_contra hno
              push Not at hno
              have hge : 0 < β^2*(‖z - mid‖^2 - ρ) :=
                mul_pos (pow_pos hβpos 2) (by linarith)
              rw [hkey z] at hge
              linarith [mul_nonpos_of_nonneg_of_nonpos hβpos.le
                (by linarith : 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2) ≤ 0)]
          have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
              (fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ρ < ‖z - mid‖^2} ∪ {∞} := by
            ext w
            induction w using OnePoint.rec with
            | infty =>
                simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
                constructor
                · intro _
                  exact Or.inr trivial
                · intro _
                  exact hinfc.mpr (by linarith)
            | coe z =>
                simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
                rw [hfin z, hEeq z]
                constructor
                · intro h
                  exact Or.inl ⟨z, h, rfl⟩
                · rintro (⟨z', hz', heq⟩ | hbad)
                  · rwa [← OnePoint.coe_eq_coe.mp heq]
                  · exact absurd hbad (OnePoint.coe_ne_infty z)
          rw [hSet2]
          have hEimg : IsPreconnected
              ((fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ρ < ‖z - mid‖^2}) :=
            (hext mid ρ).image _ (OnePoint.continuous_coe.continuousOn)
          apply hEimg.subset_closure Set.subset_union_left
          intro w hw
          rcases hw with hw | hw
          · exact subset_closure hw
          · rw [Set.mem_singleton_iff] at hw
            subst hw
            rw [Metric.mem_closure_iff]
            intro ε hε
            set Rb : ℝ := max (Real.sqrt (max ρ 0) + 1) (2/ε + 1) with hRb
            have hRb1 : Real.sqrt (max ρ 0) + 1 ≤ Rb := le_max_left _ _
            have hRb2 : 2/ε + 1 ≤ Rb := le_max_right _ _
            have hRbpos : 0 < Rb :=
              lt_of_lt_of_le (by positivity) hRb1
            refine ⟨(((mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) : ℂ) : ℂ̂), ?_, ?_⟩
            · refine ⟨mid + ((Rb + ‖mid‖ : ℝ) : ℂ), ?_, rfl⟩
              simp only [Set.mem_setOf_eq, add_sub_cancel_left]
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (by positivity : (0:ℝ) < Rb + ‖mid‖)]
              have h1 : Real.sqrt (max ρ 0) < Rb + ‖mid‖ := by
                have := norm_nonneg mid
                linarith
              have h2 : max ρ 0 < (Rb + ‖mid‖)^2 := by
                rw [← Real.sq_sqrt (le_max_right ρ 0)]
                exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr h1
              exact lt_of_le_of_lt (le_max_left ρ 0) h2
            · have hznorm : Rb ≤ ‖mid + ((Rb + ‖mid‖ : ℝ) : ℂ)‖ := by
                have h1 : ‖(mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) - mid‖ = Rb + ‖mid‖ := by
                  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_pos (by positivity)]
                have h2 : ‖(mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) - mid‖ ≤
                    ‖mid + ((Rb + ‖mid‖ : ℝ) : ℂ)‖ + ‖mid‖ := norm_sub_le _ _
                linarith
              rw [show dist (∞ : ℂ̂) (((mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) : ℂ̂))
                = chordalDistInfty (mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) from rfl]
              unfold chordalDistInfty
              set z : ℂ := mid + ((Rb + ‖mid‖ : ℝ) : ℂ)
              have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRbpos hznorm
              have hs1 : ‖z‖ < Real.sqrt (1 + ‖z‖^2) := by
                rw [show ‖z‖ = Real.sqrt (‖z‖^2) from (Real.sqrt_sq (norm_nonneg z)).symm]
                apply Real.sqrt_lt_sqrt (by positivity)
                rw [Real.sq_sqrt (sq_nonneg ‖z‖)]
                linarith
              have hs2 : (0:ℝ) < Real.sqrt (1 + ‖z‖^2) := lt_trans hzpos hs1
              rw [div_lt_iff₀ hs2]
              have hεRb : 2 < ε * Rb := by
                have h3 : ε * (2/ε + 1) = 2 + ε := by field_simp
                nlinarith [hRb2, hε]
              calc (2:ℝ) < ε * Rb := hεRb
                _ ≤ ε * ‖z‖ := by nlinarith [hznorm, hε]
                _ ≤ ε * Real.sqrt (1 + ‖z‖^2) := by nlinarith [hs1, hε]
        · -- the ball engulfs ∞: plane convex shape only
          push Not at hβ
          have hnoinf : (∞ : ℂ̂) ∉ {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} := by
            intro h
            have h1 := hinfc.mp h
            linarith
          rcases eq_or_lt_of_le hβ with hβ0 | hβneg
          · -- halfplane case: r²(1+‖a‖²) = 4
            have hr2A : r^2 * (1 + ‖a‖^2) = 4 := by linarith
            have hEeq0 : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
                8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4) := by
              intro z
              rw [hsubexp z, hr2A]
              constructor
              · intro h
                nlinarith
              · intro h
                nlinarith
            have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
                (fun z : ℂ => (z:ℂ̂)) ''
                  {z : ℂ | 8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4} := by
              ext w
              induction w using OnePoint.rec with
              | infty =>
                  simp only [Set.mem_setOf_eq]
                  constructor
                  · intro h
                    exact absurd h hnoinf
                  · rintro ⟨z', _, heq⟩
                    exact absurd heq (OnePoint.coe_ne_infty z')
              | coe z =>
                  simp only [Set.mem_setOf_eq]
                  rw [hfin z, hEeq0 z]
                  constructor
                  · intro h
                    exact ⟨z, h, rfl⟩
                  · rintro ⟨z', hz', heq⟩
                    rwa [← OnePoint.coe_eq_coe.mp heq]
            rw [hSet2]
            have hlin : IsLinearMap ℝ
                (⇑(((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ))) :=
              LinearMap.isLinear _
            have hconv0 : Convex ℝ {z : ℂ |
                (((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ)) z <
                  4*‖a‖^2 - 4} :=
              convex_halfSpace_lt hlin _
            have hseteq : {z : ℂ | 8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4} =
                {z : ℂ | (((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ)) z <
                  4*‖a‖^2 - 4} := by
              ext z
              simp only [Set.mem_setOf_eq, LinearMap.add_apply, LinearMap.smul_apply,
                Complex.reLm_coe, Complex.imLm_coe, smul_eq_mul, Complex.mul_re,
                Complex.conj_re, Complex.conj_im]
              constructor <;> intro h <;> nlinarith [h]
            rw [hseteq]
            exact (hconv0.isPreconnected).image _ (OnePoint.continuous_coe.continuousOn)
          · -- disk case: β < 0
            have hβne0 : (4 - r^2 * (1 + ‖a‖^2)) ≠ 0 := ne_of_lt hβneg
            obtain ⟨β, hβeq⟩ : ∃ b : ℝ, b = 4 - r^2 * (1 + ‖a‖^2) := ⟨_, rfl⟩
            have hβnegβ : β < 0 := hβeq ▸ hβneg
            have hβne : β ≠ 0 := hβeq ▸ hβne0
            have hβsq : 0 < β^2 := by
              have h1 : 0 < β * β := mul_pos_of_neg_of_neg hβnegβ hβnegβ
              nlinarith [h1]
            obtain ⟨mid, hmiddef⟩ : ∃ c : ℂ, c = ((4/β : ℝ) : ℂ) * a := ⟨_, rfl⟩
            obtain ⟨ρ, hρdef⟩ : ∃ p : ℝ,
              p = (16*‖a‖^2 - β*(4*‖a‖^2 - r^2*(1 + ‖a‖^2)))/β^2 := ⟨_, rfl⟩
            have hkey : ∀ z : ℂ, β^2 * (‖z - mid‖^2 - ρ) =
                β * (4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2)) := by
              intro z
              rw [hmiddef, hmidexp β hβne z, hsubexp z, hρdef, hβeq]
              field_simp
              ring
            have hEeq : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
                ‖z - mid‖^2 < ρ) := by
              intro z
              constructor
              · intro h
                by_contra hno
                push Not at hno
                have hge : 0 ≤ β^2*(‖z - mid‖^2 - ρ) :=
                  mul_nonneg (sq_nonneg β) (by linarith)
                rw [hkey z] at hge
                linarith [mul_neg_of_neg_of_pos hβnegβ
                  (by linarith : (0:ℝ) < 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2))]
              · intro h
                by_contra hno
                push Not at hno
                have hlt : β^2*(‖z - mid‖^2 - ρ) < 0 :=
                  mul_neg_of_pos_of_neg hβsq (by linarith)
                rw [hkey z] at hlt
                nlinarith [hlt, hβnegβ.le,
                  (by linarith : 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2) ≤ 0)]
            have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
                (fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ‖z - mid‖^2 < ρ} := by
              ext w
              induction w using OnePoint.rec with
              | infty =>
                  simp only [Set.mem_setOf_eq]
                  constructor
                  · intro h
                    exact absurd h hnoinf
                  · rintro ⟨z', _, heq⟩
                    exact absurd heq (OnePoint.coe_ne_infty z')
              | coe z =>
                  simp only [Set.mem_setOf_eq]
                  rw [hfin z, hEeq z]
                  constructor
                  · intro h
                    exact ⟨z, h, rfl⟩
                  · rintro ⟨z', hz', heq⟩
                    rwa [← OnePoint.coe_eq_coe.mp heq]
            rw [hSet2]
            have hconv : Convex ℝ {z : ℂ | ‖z - mid‖^2 < ρ} := by
              by_cases hρpos : 0 < ρ
              · have hball : {z : ℂ | ‖z - mid‖^2 < ρ} =
                    Metric.ball mid (Real.sqrt ρ) := by
                  ext z
                  simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
                  exact (Real.lt_sqrt (norm_nonneg _)).symm
                rw [hball]
                exact convex_ball mid _
              · have hempty : {z : ℂ | ‖z - mid‖^2 < ρ} = ∅ := by
                  ext z
                  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                  push Not at hρpos
                  nlinarith [sq_nonneg ‖z - mid‖]
                rw [hempty]
                exact convex_empty
            exact (hconv.isPreconnected).image _ (OnePoint.continuous_coe.continuousOn)
  -- distances between the three reference points 0, 1, ∞
  have hd0i : (5/4 : ℝ) ≤ dist (((0 : ℂ) : ℂ̂)) (∞ : ℂ̂) := by
    have : dist (((0 : ℂ) : ℂ̂)) (∞ : ℂ̂) = chordalDistInfty 0 := rfl
    rw [this]
    unfold chordalDistInfty
    simp
    norm_num
  have hd1i : (5/4 : ℝ) ≤ dist (((1 : ℂ) : ℂ̂)) (∞ : ℂ̂) := by
    have h1 : dist (((1 : ℂ) : ℂ̂)) (∞ : ℂ̂) = chordalDistInfty 1 := rfl
    rw [h1]
    unfold chordalDistInfty
    have hs : Real.sqrt (1 + ‖(1 : ℂ)‖ ^ 2) = Real.sqrt 2 := by norm_num
    rw [hs]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [le_div_iff₀ h2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hd01 : (5/4 : ℝ) ≤ dist (((0 : ℂ) : ℂ̂)) (((1 : ℂ) : ℂ̂)) := by
    have h1 : dist (((0 : ℂ) : ℂ̂)) (((1 : ℂ) : ℂ̂)) = chordalDist 0 1 := rfl
    rw [h1]
    unfold chordalDist
    have hs0 : Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 1 := by norm_num
    have hs : Real.sqrt (1 + ‖(1 : ℂ)‖ ^ 2) = Real.sqrt 2 := by norm_num
    rw [hs0, hs]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : ‖(0 : ℂ) - 1‖ = 1 := by norm_num
    rw [h3, one_mul, le_div_iff₀ h2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  -- two of the three reference points lie outside any small closed ball
  have htwo : ∀ (y : ℂ̂) (r : ℝ), r ≤ 1/2 →
      ∃ p q : ℂ̂, p ∉ Metric.closedBall y r ∧ q ∉ Metric.closedBall y r ∧
        (5/4 : ℝ) ≤ dist p q := by
    intro y r hr
    by_cases h0 : (((0 : ℂ) : ℂ̂)) ∈ Metric.closedBall y r
    · refine ⟨(((1 : ℂ) : ℂ̂)), (∞ : ℂ̂), ?_, ?_, hd1i⟩
      · intro h1
        rw [Metric.mem_closedBall] at h0 h1
        have := dist_triangle (((0 : ℂ) : ℂ̂)) y (((1 : ℂ) : ℂ̂))
        rw [dist_comm y _] at this
        linarith [hd01]
      · intro h1
        rw [Metric.mem_closedBall] at h0 h1
        have := dist_triangle (((0 : ℂ) : ℂ̂)) y (∞ : ℂ̂)
        rw [dist_comm y _] at this
        linarith [hd0i]
    · by_cases h1 : (((1 : ℂ) : ℂ̂)) ∈ Metric.closedBall y r
      · refine ⟨(((0 : ℂ) : ℂ̂)), (∞ : ℂ̂), h0, ?_, hd0i⟩
        intro h2
        rw [Metric.mem_closedBall] at h1 h2
        have := dist_triangle (((1 : ℂ) : ℂ̂)) y (∞ : ℂ̂)
        rw [dist_comm y _] at this
        linarith [hd1i]
      · exact ⟨(((0 : ℂ) : ℂ̂)), (((1 : ℂ) : ℂ̂)), h0, h1, hd01⟩
  -- ===== main case split on the multiplicities =====
  by_cases hrec : ∃ v : ℕ, {j : ℕ | m j = v}.Infinite
  · -- ===== CASE I: one iterate time recurs; elementary winding contradiction =====
    obtain ⟨v, hv⟩ := hrec
    obtain ⟨ψ, hψmono, hψmem⟩ := Filter.extraction_of_frequently_atTop
      (Nat.frequently_atTop_iff_infinite.mpr hv)
    -- all the extracted curves coincide with the one at index `ψ 0`
    have hΓfix : ∀ k : ℕ, Γf (ψ k) = Γf (ψ 0) := by
      intro k
      ext t
      have h1 : m (ψ k) = v := hψmem k
      have h2 : m (ψ 0) = v := hψmem 0
      rw [hΓeq, hΓeq, h1, h2]
    -- select the Julia witnesses
    have hzsel : ∀ k : ℕ, ∃ z ∈ Cc (ψ k), ((z:ℂ̂)) ∈ JuliaSet f := fun k => hCJ (ψ k)
    choose zJ hzJC hzJJ using hzsel
    -- the witnesses lie in the bounded winding region of the fixed curve
    have hreg : ∀ k : ℕ, zJ k ∈ {q : ℂ | q ∉ Set.range ⇑(Γf (ψ 0)) ∧
        windingNumber (Γf (ψ 0)) q ≠ 0} := by
      intro k
      constructor
      · rw [← hΓfix k]
        exact hznr (ψ k) _ (hzJC k)
      · rw [← hΓfix k]
        exact hzw (ψ k) _ (hzJC k)
    obtain ⟨R, hRball⟩ := (isBounded_windingRegion (hΓcl (ψ 0))).subset_closedBall 0
    have hzJball : ∀ k, zJ k ∈ Metric.closedBall (0:ℂ) R := fun k => hRball (hreg k)
    obtain ⟨zst, _, χ, hχmono, hχtend⟩ :=
      (isCompact_closedBall (0:ℂ) R).tendsto_subseq hzJball
    -- the limit reads as a Julia point on the sphere
    have hzstJ : ((zst:ℂ̂)) ∈ JuliaSet f := by
      apply (isClosed_juliaSet f).mem_of_tendsto ((hcoe_cont.tendsto zst).comp hχtend)
      exact Filter.Eventually.of_forall (fun k => hzJJ (χ k))
    -- the limit avoids the (Fatou) curve trace
    have hzstnr : zst ∉ Set.range ⇑(Γf (ψ 0)) := by
      rintro ⟨t, ht⟩
      apply hzstJ
      rw [← ht, hΓsphere (ψ 0) t]
      exact hVFat (m (ψ 0)) (hmem (m (ψ 0)) t)
    have hRcomp : IsCompact (Set.range ⇑(Γf (ψ 0))) :=
      isCompact_range (Γf (ψ 0)).continuous
    have hd0 : 0 < Metric.infDist zst (Set.range ⇑(Γf (ψ 0))) :=
      (hRcomp.isClosed.notMem_iff_infDist_pos
        ⟨Γf (ψ 0) 0, Set.mem_range_self 0⟩).mp hzstnr
    -- the winding number is constant on the ball around the limit
    have hballdisj : ∀ t : unitInterval, Γf (ψ 0) t ∉
        Metric.ball zst (Metric.infDist zst (Set.range ⇑(Γf (ψ 0)))) := by
      intro t hmem'
      rw [Metric.mem_ball] at hmem'
      have h1 := Metric.infDist_le_dist_of_mem (x := zst)
        (Set.mem_range_self t : Γf (ψ 0) t ∈ Set.range ⇑(Γf (ψ 0)))
      rw [dist_comm] at h1
      linarith
    have hconstw : ∀ q ∈ Metric.ball zst (Metric.infDist zst (Set.range ⇑(Γf (ψ 0)))),
        windingNumber (Γf (ψ 0)) q = windingNumber (Γf (ψ 0)) zst := by
      intro q hq
      exact windingNumber_eq_of_preconnected (hΓcl (ψ 0))
        (convex_ball _ _).isPreconnected hballdisj hq (Metric.mem_ball_self hd0)
    -- the extracted points eventually lie in that ball
    have hev : ∀ᶠ k in Filter.atTop,
        dist (zJ (χ k)) zst < Metric.infDist zst (Set.range ⇑(Γf (ψ 0))) :=
      (Metric.tendsto_nhds.mp hχtend) _ hd0
    rw [Filter.eventually_atTop] at hev
    obtain ⟨K₀, hK₀⟩ := hev
    -- unbounded winding at a single point: contradiction
    set kk : ℕ := max K₀ (windingNumber (Γf (ψ 0)) zst).natAbs with hkk
    have h1 := hwind (ψ (χ kk)) _ (hzJC (χ kk))
    rw [hΓfix (χ kk)] at h1
    have h2 : windingNumber (Γf (ψ 0)) (zJ (χ kk)) = windingNumber (Γf (ψ 0)) zst :=
      hconstw _ (Metric.mem_ball.mpr (hK₀ kk (le_max_left _ _)))
    rw [h2] at h1
    have h3 : kk ≤ ψ (χ kk) := le_trans (hχmono.le_apply) (hψmono.le_apply)
    have h4 : |windingNumber (Γf (ψ 0)) zst| =
        ((windingNumber (Γf (ψ 0)) zst).natAbs : ℤ) := Int.abs_eq_natAbs _
    rw [h4] at h1
    have h5 : (windingNumber (Γf (ψ 0)) zst).natAbs ≤ kk := le_max_right _ _
    omega
  · -- ===== CASE II: iterate times are unbounded; confinement contradiction =====
    -- unboundedness of the m-values
    have hunb : ∀ V : ℕ, ∃ j : ℕ, V ≤ m j := by
      intro V
      by_contra hcon
      push Not at hcon
      apply hrec
      obtain ⟨v, hv⟩ :=
        Finite.exists_infinite_fiber (fun j : ℕ => (⟨m j, hcon j⟩ : Fin V))
      refine ⟨(v : ℕ), (Set.infinite_coe_iff.mp hv).mono fun j hj => ?_⟩
      simpa [Fin.ext_iff] using hj
    -- normality of the iterate family on an open set W around the base trace
    obtain ⟨W, hWopen, hWsub, hKγW, hWnorm⟩ : ∃ W : Set ℂ̂, IsOpen W ∧
        W ⊆ fcOrbit f U N₀ ∧ T 0 ⊆ W ∧
        IsNormal (Set.range fun n : ℕ => f^[n]) W := by
      -- each trace point has an open normality neighborhood inside the component
      have hnb : ∀ x : ↥(T 0), ∃ V : Set ℂ̂, IsOpen V ∧ (x:ℂ̂) ∈ V ∧
          V ⊆ fcOrbit f U N₀ ∧ IsNormal (Set.range fun n : ℕ => f^[n]) V := by
        rintro ⟨x, hx⟩
        have hxV : x ∈ fcOrbit f U N₀ := by
          obtain ⟨t, ht⟩ := hx
          rw [← ht]
          simpa using hmem 0 t
        have hxF : x ∈ FatouSet f := hVfc.subset_fatouSet hxV
        obtain ⟨Ux, hUxn, hUxN⟩ := mem_fatouSet_iff.mp hxF
        exact ⟨interior Ux ∩ fcOrbit f U N₀,
          isOpen_interior.inter hVopen,
          ⟨mem_interior_iff_mem_nhds.mpr hUxn, hxV⟩,
          Set.inter_subset_right,
          hUxN.mono (fun y hy => interior_subset hy.1)⟩
      choose Vx hVo hVx hVsub hVn using hnb
      obtain ⟨s, hs⟩ := (hTcompact 0).elim_finite_subcover Vx hVo
        (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
      have hUnorm : ∀ s : Finset ↥(T 0),
          IsNormal (Set.range fun n : ℕ => f^[n]) (⋃ i ∈ s, Vx i) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            intro seq
            refine ⟨id, strictMono_id, (seq 0 : ℂ̂ → ℂ̂), ?_⟩
            intro u hu x hx
            simp at hx
        | insert x s hxs ih =>
            rw [Finset.set_biUnion_insert]
            exact IsNormal.union (hVo x) (isOpen_biUnion fun i _ => hVo i) (hVn x) ih
      exact ⟨⋃ i ∈ s, Vx i, isOpen_biUnion fun i _ => hVo i,
        Set.iUnion₂_subset fun i _ => hVsub i, hs, hUnorm s⟩
    -- compact thickening K of the base trace inside W
    obtain ⟨rK, hrKpos, hrKsub⟩ :=
      (hTcompact 0).exists_cthickening_subset_open hWopen hKγW
    set K : Set ℂ̂ := Metric.cthickening rK (T 0) with hKdef
    have hKcomp : IsCompact K := Metric.isClosed_cthickening.isCompact
    have hKsubW : K ⊆ W := hrKsub
    have hKγint : T 0 ⊆ interior K := by
      intro x hx
      have h1 : x ∈ Metric.thickening rK (T 0) :=
        Metric.self_subset_thickening hrKpos _ hx
      exact interior_maximal (Metric.thickening_subset_cthickening _ _)
        Metric.isOpen_thickening h1
    -- STEP B: full-sequence collapse of the trace diameters
    have hdiam : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν →
        Metric.diam (T ν) ≤ ε := by
      intro ε hε
      by_contra hcon
      push Not at hcon
      have hfreq : ∃ᶠ ν in Filter.atTop, ε < Metric.diam (T ν) := by
        rw [Filter.frequently_atTop]
        intro N
        obtain ⟨ν, h1, h2⟩ := hcon N
        exact ⟨ν, h1, h2⟩
      obtain ⟨ψ, hψmono, hψd⟩ := Filter.extraction_of_frequently_atTop hfreq
      obtain ⟨ρ, hρmono, g, hg⟩ := hWnorm (fun k => ⟨f^[ψ k], ⟨ψ k, rfl⟩⟩)
      have hφmono : StrictMono (fun k => ψ (ρ k)) := hψmono.comp hρmono
      have hglim : TendstoLocallyUniformlyOn (fun k => f^[ψ (ρ k)]) g Filter.atTop
          (interior K) := hg.mono (interior_subset.trans hKsubW)
      -- the base component wanders
      have hWand : IsWandering f (fcOrbit f U N₀) := by
        intro i j hij
        change Disjoint (fcOrbit f (fcOrbit f U N₀) i) (fcOrbit f (fcOrbit f U N₀) j)
        rw [← fcOrbit_add N₀ i hf hd1 hU, ← fcOrbit_add N₀ j hf hd1 hU]
        exact hW (by omega)
      have hconst := eventually_constant_limit_of_wandering hf hd hVfc hWand hφmono
        hKcomp (hKsubW.trans hWsub) hglim
      -- the limit is constant on the connected base trace
      have hT0conn : IsPreconnected (T 0) := (isConnected_range (hTcont 0)).isPreconnected
      have hcc : ∀ t : unitInterval, g ((γ t : ℂ̂)) = g ((γ 0 : ℂ̂)) := by
        intro t
        have hsubcc : T 0 ⊆ connectedComponentIn (interior K) ((γ 0 : ℂ̂)) :=
          hT0conn.subset_connectedComponentIn ⟨0, rfl⟩ hKγint
        have hcompeq : connectedComponentIn (interior K) ((γ t : ℂ̂)) =
            connectedComponentIn (interior K) ((γ 0 : ℂ̂)) :=
          (connectedComponentIn_eq (hsubcc ⟨t, rfl⟩)).symm
        exact hconst _ (hKγint ⟨t, rfl⟩) _ (hKγint ⟨0, rfl⟩) hcompeq
      -- uniform convergence on the compact trace
      have hUnif : TendstoUniformlyOn (fun k => f^[ψ (ρ k)]) g Filter.atTop (T 0) :=
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior).mp
          hglim) (T 0) hKγint (hTcompact 0)
      rw [Metric.tendstoUniformlyOn_iff] at hUnif
      obtain ⟨k, hk⟩ := (hUnif (ε/4) (by positivity)).exists
      -- diameter bound at time ψ (ρ k), contradicting the frequent lower bound
      have hdle : Metric.diam (T (ψ (ρ k))) ≤ ε/2 := by
        apply Metric.diam_le_of_forall_dist_le (by positivity)
        rintro x ⟨t, rfl⟩ y ⟨t', rfl⟩
        have e1 : dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t : ℂ̂))) < ε/4 :=
          hk ((γ t : ℂ̂)) ⟨t, rfl⟩
        have e2 : dist (g ((γ t' : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) < ε/4 :=
          hk ((γ t' : ℂ̂)) ⟨t', rfl⟩
        have e3 : g ((γ t : ℂ̂)) = g ((γ t' : ℂ̂)) := by
          rw [hcc t, hcc t']
        calc dist (f^[ψ (ρ k)] ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂)))
            ≤ dist (f^[ψ (ρ k)] ((γ t : ℂ̂))) (g ((γ t : ℂ̂))) +
              dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) := dist_triangle _ _ _
          _ = dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t : ℂ̂))) +
              dist (g ((γ t' : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) := by
                rw [dist_comm, e3]
          _ ≤ ε/2 := by linarith
      linarith [hψd (ρ k)]
    -- ===== fixed constants =====
    obtain ⟨sB, hsBpos, hsB⟩ : ∃ s : ℝ, 0 < s ∧ (∞ ∈ FatouSet f →
        Metric.ball (∞ : ℂ̂) s ⊆ connectedComponentIn (FatouSet f) ∞) := by
      by_cases hFinf : ∞ ∈ FatouSet f
      · have hopen : IsOpen (connectedComponentIn (FatouSet f) ∞) :=
          (isFatouComponent_connectedComponentIn hFinf).isOpen
        obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.mp hopen ∞
          (mem_connectedComponentIn hFinf)
        exact ⟨s, hs, fun _ => hsub⟩
      · exact ⟨1, one_pos, fun h => absurd h hFinf⟩
    obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ u v : ℂ̂, dist u v < η →
        dist (f u) (f v) < 1/8 := by
      have huc : UniformContinuous f :=
        CompactSpace.uniformContinuous_of_continuous hcf
      obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp huc (1/8) (by norm_num)
      exact ⟨η, hη, fun u v huv => h huv⟩
    set δ : ℝ := min (min (η/5) (1/100)) (sB/3) with hδdef
    have hδpos : 0 < δ := by
      apply lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
    have hδη : 4 * δ < η := by
      have h1 : δ ≤ η/5 := le_trans (min_le_left _ _) (min_le_left _ _)
      linarith
    have hδsmall : δ ≤ 1/100 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδsB : 3 * δ ≤ sB := by
      have h1 : δ ≤ sB/3 := min_le_right _ _
      linarith
    obtain ⟨N, hN⟩ := hdiam δ hδpos
    obtain ⟨j₀, hj₀⟩ := hunb N
    set n : ℕ := m j₀ with hndef
    have hnN : N ≤ n := hj₀
    have hdT : ∀ k : ℕ, Metric.diam (T (n + k)) ≤ δ := fun k =>
      hN (n + k) (le_trans hnN (Nat.le_add_right n k))
    -- ===== base stage: a small open set with Julia point and frontier on the trace =====
    obtain ⟨O, ζ, hOopen, hζO, hζJ, hOfr, hOsub⟩ : ∃ (O : Set ℂ̂) (ζ : ℂ̂),
        IsOpen O ∧ ζ ∈ O ∧ ζ ∈ JuliaSet f ∧ frontier O ⊆ T n ∧
        O ⊆ Metric.closedBall (yy n) (2 * Metric.diam (T n)) := by
      -- winding-region data at index j₀ (time n = m j₀)
      obtain ⟨zJ, hzJC, hzJJ⟩ := hCJ j₀
      set Dreg : Set ℂ := {q : ℂ | q ∉ Set.range ⇑(Γf j₀) ∧ windingNumber (Γf j₀) q ≠ 0}
        with hDregdef
      have hDopen : IsOpen Dreg := isOpen_windingRegion (hΓcl j₀)
      have hDbdd : Bornology.IsBounded Dreg := isBounded_windingRegion (hΓcl j₀)
      have hDfr : frontier Dreg ⊆ Set.range ⇑(Γf j₀) :=
        frontier_windingRegion_subset (hΓcl j₀)
      have hzD : zJ ∈ Dreg := ⟨hznr j₀ _ hzJC, hzw j₀ _ hzJC⟩
      -- the sphere reading of the winding region
      set Dh : Set ℂ̂ := (fun z : ℂ => (z : ℂ̂)) '' Dreg with hDhdef
      have hDhopen : IsOpen Dh := hcoe_open _ hDopen
      have hDhfr : frontier Dh ⊆ T n := by
        intro x hx
        obtain ⟨d', hd', rfl⟩ := hfrontier_coe Dreg hDopen hDbdd hx
        have h1 : d' ∈ Set.range ⇑(Γf j₀) := hDfr hd'
        rw [hndef, ← hΓrange j₀]
        exact ⟨d', h1, rfl⟩
      -- diameter data
      set d₀ : ℝ := Metric.diam (T n) with hd₀def
      have hd₀nn : (0:ℝ) ≤ d₀ := Metric.diam_nonneg
      have hd₀δ : d₀ ≤ δ := by
        rw [hd₀def]
        have := hdT 0
        rwa [Nat.add_zero] at this
      -- dichotomy against the complement of the doubled trace ball
      have hAconn : IsPreconnected ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) :=
        hcompl_ball_conn (yy n) (2*d₀) (by linarith)
      have hAdisj : ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩ frontier Dh = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hx1, hx2⟩
        have h1 : x ∈ T n := hDhfr hx2
        have h2 : dist x (yy n) ≤ d₀ := Metric.mem_closedBall.mp (hTsubB n h1)
        exact hx1 (Metric.mem_closedBall.mpr (by linarith))
      rcases hdichot Dh ((Metric.closedBall (yy n) (2*d₀))ᶜ) hDhopen hAconn hAdisj
        with hsub | hdisj2
      · -- the complement of the ball sits inside the winding region: trace near ∞
        have hyinf : dist (∞ : ℂ̂) (yy n) ≤ 2*d₀ := by
          by_contra hfar
          push Not at hfar
          have hinfA : (∞:ℂ̂) ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) := by
            intro hball
            exact absurd (Metric.mem_closedBall.mp hball) (not_le.mpr hfar)
          obtain ⟨d', _, hbad⟩ := hsub hinfA
          exact (OnePoint.coe_ne_infty d') hbad
        by_cases hFinf : ∞ ∈ FatouSet f
        · -- ∞ is a Fatou point: its component would swallow the orbit component
          exfalso
          have hyy : yy n ∈ Metric.ball (∞:ℂ̂) sB := by
            rw [Metric.mem_ball, dist_comm]
            have h1 : (2:ℝ)*d₀ ≤ 2*δ := by linarith
            have h2 : (2:ℝ)*δ < 3*δ := by linarith
            linarith [hδsB, hyinf]
          have hyyV : yy n ∈ fcOrbit f U (N₀ + n) := hmem n 0
          have hVeq : fcOrbit f U (N₀ + n) = connectedComponentIn (FatouSet f) ∞ :=
            (isFatouComponent_fcOrbit (N₀+n) hf hd1 hU).eq_of_mem
              (isFatouComponent_connectedComponentIn hFinf) hyyV (hsB hFinf hyy)
          exact hinf (N₀ + n) (by rw [hVeq]; exact mem_connectedComponentIn hFinf)
        · -- ∞ is a Julia point: confine the outside of the winding region
          have hζJ' : (∞:ℂ̂) ∈ JuliaSet f := hFinf
          refine ⟨(closure Dh)ᶜ, ∞, isClosed_closure.isOpen_compl, ?_, hζJ', ?_, ?_⟩
          · simp only [Set.mem_compl_iff]
            intro hmem'
            rw [closure_eq_self_union_frontier] at hmem'
            rcases hmem' with h | h
            · obtain ⟨d', _, hbad⟩ := h
              exact (OnePoint.coe_ne_infty d') hbad
            · exact hTinf n (hDhfr h)
          · calc frontier ((closure Dh)ᶜ) = frontier (closure Dh) := frontier_compl _
              _ ⊆ frontier Dh := frontier_closure_subset
              _ ⊆ T n := hDhfr
          · intro x hx
            by_contra hxout
            have hxA : x ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) := hxout
            exact hx (subset_closure (hsub hxA))
      · -- the winding region is confined to the doubled trace ball
        refine ⟨Dh, ((zJ:ℂ̂)), hDhopen, ⟨zJ, hzD, rfl⟩, hzJJ, hDhfr, ?_⟩
        intro x hx
        by_contra hxout
        have hmemint : x ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩ Dh :=
          ⟨hxout, hx⟩
        rw [hdisj2] at hmemint
        exact hmemint
    -- ===== confinement induction =====
    have hR : ∀ k : ℕ, frontier (f^[k] '' O) ⊆ T (n + k) ∧
        f^[k] '' O ⊆ Metric.closedBall (yy (n + k)) (2 * Metric.diam (T (n + k))) := by
      intro k
      induction k with
      | zero =>
          constructor
          · simp only [Function.iterate_zero, Set.image_id, Nat.add_zero]
            exact hOfr
          · simp only [Function.iterate_zero, Set.image_id, Nat.add_zero]
            exact hOsub
      | succ k ih =>
          obtain ⟨ihf, ihb⟩ := ih
          have himg1 : f^[k+1] '' O = f '' (f^[k] '' O) := by
            rw [Function.iterate_succ', Set.image_comp]
          -- (i) the frontier of the next image lies on the next trace
          have hfr1 : frontier (f^[k+1] '' O) ⊆ T (n + (k+1)) := by
            rw [himg1]
            intro x hx
            obtain ⟨u, hu, rfl⟩ := hfrontier_image (f^[k] '' O)
              (hopen_iter k _ hOopen) hx
            have h1 : u ∈ T (n + k) := ihf hu
            have h2 : f u ∈ f '' T (n+k) := Set.mem_image_of_mem f h1
            rw [hfT (n+k)] at h2
            rwa [show n + (k+1) = (n + k) + 1 from by omega]
          -- (ii) uniform continuity keeps the next image below the safe scale
          have hsmall : ∀ u' v' : ℂ̂, u' ∈ f^[k+1] '' O → v' ∈ f^[k+1] '' O →
              dist u' v' < 1/8 := by
            intro u' v' hu' hv'
            rw [himg1] at hu' hv'
            obtain ⟨u, hu, rfl⟩ := hu'
            obtain ⟨v, hv, rfl⟩ := hv'
            apply hη
            have h1 := Metric.mem_closedBall.mp (ihb hu)
            have h2 := Metric.mem_closedBall.mp (ihb hv)
            have h3 : Metric.diam (T (n+k)) ≤ δ := hdT k
            calc dist u v ≤ dist u (yy (n+k)) + dist (yy (n+k)) v := dist_triangle _ _ _
              _ ≤ 2*Metric.diam (T (n+k)) + 2*Metric.diam (T (n+k)) := by
                  rw [dist_comm (yy (n+k)) v]
                  linarith
              _ ≤ 4*δ := by linarith
              _ < η := hδη
          refine ⟨hfr1, ?_⟩
          -- (iii) dichotomy at the next time pins the image in the small ball
          set d1 : ℝ := Metric.diam (T (n + (k+1))) with hd1def
          have hd1nn : (0:ℝ) ≤ d1 := Metric.diam_nonneg
          have hAconn : IsPreconnected
              ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) :=
            hcompl_ball_conn _ _ (by linarith)
          have hAdisj : ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) ∩
              frontier (f^[k+1] '' O) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro x ⟨hx1, hx2⟩
            have h1 : x ∈ T (n+(k+1)) := hfr1 hx2
            have h2 : dist x (yy (n+(k+1))) ≤ d1 :=
              Metric.mem_closedBall.mp (hTsubB _ h1)
            exact hx1 (Metric.mem_closedBall.mpr (by linarith))
          have hopenG : IsOpen (f^[k+1] '' O) := hopen_iter (k+1) _ hOopen
          rcases hdichot (f^[k+1] '' O) _ hopenG hAconn hAdisj with hsubA | hdisjA
          · -- impossible: the huge ball complement cannot fit in a tiny image
            exfalso
            have hd1δ : d1 ≤ δ := hdT (k+1)
            obtain ⟨p, q, hp, hq, hpq⟩ := htwo (yy (n+(k+1))) (2*d1)
              (by linarith [hδsmall])
            have hpG : p ∈ f^[k+1] '' O := hsubA hp
            have hqG : q ∈ f^[k+1] '' O := hsubA hq
            have := hsmall p q hpG hqG
            linarith
          · intro x hx
            by_contra hxout
            have hmemint : x ∈ ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) ∩
                (f^[k+1] '' O) := ⟨hxout, hx⟩
            rw [hdisjA] at hmemint
            exact hmemint
    -- pairwise distance bound on the forward images
    have hconf : ∀ (k : ℕ) (u v : ℂ̂), u ∈ f^[k] '' O → v ∈ f^[k] '' O →
        dist u v ≤ 4 * Metric.diam (T (n + k)) := by
      intro k u v hu hv
      have h1 := Metric.mem_closedBall.mp ((hR k).2 hu)
      have h2 := Metric.mem_closedBall.mp ((hR k).2 hv)
      calc dist u v ≤ dist u (yy (n + k)) + dist (yy (n + k)) v := dist_triangle _ _ _
        _ ≤ 2 * Metric.diam (T (n + k)) + 2 * Metric.diam (T (n + k)) := by
            rw [dist_comm (yy (n + k)) v]; linarith
        _ = 4 * Metric.diam (T (n + k)) := by ring
    -- ===== final stage: normality at the Julia point ζ =====
    have hζF : ζ ∈ FatouSet f := by
      refine mem_fatouSet_iff.mpr ⟨O, hOopen.mem_nhds hζO, ?_⟩
      intro seq
      choose e he using fun k => (seq k).2
      by_cases hbdd : ∃ M : ℕ, ∀ k : ℕ, e k ≤ M
      · -- bounded exponents: pigeonhole a constant subsequence
        obtain ⟨M, hM⟩ := hbdd
        obtain ⟨v', hv'⟩ := Finite.exists_infinite_fiber
          (fun k : ℕ => (⟨e k, Nat.lt_succ_of_le (hM k)⟩ : Fin (M + 1)))
        have hinfv : {k : ℕ | e k = (v' : ℕ)}.Infinite := by
          refine (Set.infinite_coe_iff.mp hv').mono fun k hk => ?_
          simpa [Fin.ext_iff] using hk
        obtain ⟨ψ, hψ, hψe⟩ := Filter.extraction_of_frequently_atTop
          (Nat.frequently_atTop_iff_infinite.mpr hinfv)
        have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => f^[(v' : ℕ)])
            f^[(v' : ℕ)] Filter.atTop O := by
          intro u hu w _
          exact ⟨O, self_mem_nhdsWithin,
            Filter.Eventually.of_forall fun k y _ => refl_mem_uniformity hu⟩
        refine ⟨ψ, hψ, f^[(v' : ℕ)], hbase.congr fun j y _ => ?_⟩
        have h1 : (seq (ψ j) : ℂ̂ → ℂ̂) y = f^[e (ψ j)] y :=
          (congrFun (he (ψ j)) y).symm
        rw [h1, hψe j]
      · -- unbounded exponents: the confined images force a constant limit
        push Not at hbdd
        have hfreq : ∀ j : ℕ, ∃ᶠ k in Filter.atTop, j ≤ e k := by
          intro j
          rw [Nat.frequently_atTop_iff_infinite]
          by_contra hfin
          rw [Set.not_infinite] at hfin
          obtain ⟨M₀, hM₀⟩ := (hfin.image e).bddAbove
          obtain ⟨k, hk⟩ := hbdd (max M₀ j)
          have hjk : j ≤ e k := le_of_lt (lt_of_le_of_lt (le_max_right M₀ j) hk)
          have h1 : e k ≤ M₀ := hM₀ (Set.mem_image_of_mem e hjk)
          exact absurd hk (not_lt.mpr (h1.trans (le_max_left M₀ j)))
        obtain ⟨ψ, hψ, hψe⟩ := Filter.extraction_forall_of_frequently hfreq
        obtain ⟨q, _, χ, hχ, hχtend⟩ := isCompact_univ.tendsto_subseq
          (x := fun k => f^[e (ψ k)] ζ) (fun k => Set.mem_univ _)
        have htu : TendstoUniformlyOn (fun i => f^[e (ψ (χ i))]) (fun _ => q)
            Filter.atTop O := by
          rw [Metric.tendstoUniformlyOn_iff]
          intro ε hε
          obtain ⟨N₁, hN₁⟩ := hdiam (ε/16) (by positivity)
          have hev1 : ∀ᶠ i in Filter.atTop, dist (f^[e (ψ (χ i))] ζ) q < ε/4 :=
            (Metric.tendsto_nhds.mp hχtend) _ (by positivity)
          have hev2 : ∀ᶠ i in Filter.atTop, N₁ ≤ i := Filter.eventually_ge_atTop N₁
          filter_upwards [hev1, hev2] with i hi1 hi2
          intro x hx
          have hEbig : N₁ ≤ e (ψ (χ i)) := by
            have h1 : i ≤ χ i := hχ.le_apply
            have h2 : χ i ≤ e (ψ (χ i)) := hψe (χ i)
            omega
          have hdE : Metric.diam (T (n + e (ψ (χ i)))) ≤ ε/16 :=
            hN₁ _ (le_trans hEbig (Nat.le_add_left _ _))
          have hζim : f^[e (ψ (χ i))] ζ ∈ f^[e (ψ (χ i))] '' O :=
            Set.mem_image_of_mem _ hζO
          have hxim : f^[e (ψ (χ i))] x ∈ f^[e (ψ (χ i))] '' O :=
            Set.mem_image_of_mem _ hx
          have hpair := hconf (e (ψ (χ i))) _ _ hζim hxim
          calc dist ((fun _ => q) x) (f^[e (ψ (χ i))] x)
              ≤ dist q (f^[e (ψ (χ i))] ζ) +
                dist (f^[e (ψ (χ i))] ζ) (f^[e (ψ (χ i))] x) := dist_triangle _ _ _
            _ ≤ ε/4 + 4 * Metric.diam (T (n + e (ψ (χ i)))) := by
                rw [dist_comm q _]
                exact add_le_add (le_of_lt hi1) hpair
            _ ≤ ε/4 + 4 * (ε/16) := by linarith
            _ < ε := by linarith
        refine ⟨fun i => ψ (χ i), hψ.comp hχ, fun _ => q,
          (htu.tendstoLocallyUniformlyOn).congr fun i y _ => ?_⟩
        exact congrFun (he (ψ (χ i))) y
    exact hζJ hζF

set_option maxHeartbeats 400000 in
-- This enclosure-impossibility proof elaborates as one large declaration whose nested
-- winding/enclosure `have` chains exceed the default heartbeat budget.
/-- **Cofinally enclosed Julia points are impossible.** If the forward
readings of a fixed chart loop enclose Julia points — points off the
`∞`-component of the sphere complement of the trace — at arbitrarily late
times, then normality of the iterates on the loop's trace collapses the
forward traces, the enclosed component of a late Julia witness is confined
under further iteration by the open-mapping frontier dichotomy, and the
shrinking images force normality at the witness, contradicting its
membership in the Julia set. -/
theorem false_of_fill_meets_julia_cofinally {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    {N₀ : ℕ} {γ : C(unitInterval, ℂ)} (hγcl : γ 0 = γ 1)
    (hγmem : ∀ t : unitInterval, ((γ t : ℂ̂)) ∈ fcOrbit f U N₀)
    (hyes : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ ∃ Γ : C(unitInterval, ℂ),
      (∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂)))) ∧
      ∃ w : ℂ̂, w ∈ JuliaSet f ∧
        w ∉ Set.range (fun t => ((Γ t : ℂ̂))) ∧
        w ∉ connectedComponentIn ((Set.range fun t => ((Γ t : ℂ̂)))ᶜ) ∞) :
    False := by
  classical
  have _ := hγcl
  -- ===== Stage 0: basic dynamical facts =====
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  have hcf : Continuous f := hf.continuous
  have hfo : IsOpenMap f := hf.isOpenMap (hf.ne_const hd1)
  have hcont_iter : ∀ k : ℕ, Continuous (f^[k]) := fun k => hcf.iterate k
  have hopen_iter : ∀ k : ℕ, IsOpenMap (f^[k]) := by
    intro k
    induction k with
    | zero => exact IsOpenMap.id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hfo.comp ih
  have hcoe_cont : Continuous ((↑) : ℂ → ℂ̂) := OnePoint.continuous_coe
  have hcoe_chart : ∀ x : ℂ̂, x ≠ ∞ → ((chartFiniteMap x : ℂ) : ℂ̂) = x := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe w => rfl
  -- every subset of the (compact) sphere is bounded
  have hbdd : ∀ s : Set ℂ̂, Bornology.IsBounded s := fun s =>
    (isCompact_univ.isBounded).subset (Set.subset_univ s)
  -- orbit membership of the iterated curve
  have himg : ∀ n : ℕ, f^[n] '' (fcOrbit f U N₀) = fcOrbit f U (N₀ + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ', Set.image_comp, ih,
          fcOrbit_image_eq hf hd1 hU (N₀ + n), Nat.add_assoc]
  have hmem : ∀ (n : ℕ) (t : unitInterval),
      f^[n] ((γ t : ℂ̂)) ∈ fcOrbit f U (N₀ + n) := by
    intro n t
    rw [← himg n]
    exact Set.mem_image_of_mem _ (hγmem t)
  have hne_inf : ∀ (n : ℕ) (t : unitInterval), f^[n] ((γ t : ℂ̂)) ≠ ∞ := by
    intro n t h
    exact hinf (N₀ + n) (h ▸ hmem n t)
  have hVfc : IsFatouComponent f (fcOrbit f U N₀) :=
    isFatouComponent_fcOrbit N₀ hf hd1 hU
  have hVopen : IsOpen (fcOrbit f U N₀) := hVfc.isOpen
  -- ===== the sphere traces of the iterated curve =====
  set T : ℕ → Set ℂ̂ := fun ν => Set.range (fun t : unitInterval => f^[ν] ((γ t : ℂ̂)))
    with hTdef
  have hTcont : ∀ ν : ℕ, Continuous (fun t : unitInterval => f^[ν] ((γ t : ℂ̂))) :=
    fun ν => (hcont_iter ν).comp (hcoe_cont.comp γ.continuous)
  have hTcompact : ∀ ν : ℕ, IsCompact (T ν) := fun ν => isCompact_range (hTcont ν)
  set yy : ℕ → ℂ̂ := fun ν => f^[ν] ((γ 0 : ℂ̂)) with hyydef
  have hyT : ∀ ν : ℕ, yy ν ∈ T ν := fun ν => ⟨0, rfl⟩
  have hTsubB : ∀ ν : ℕ, T ν ⊆ Metric.closedBall (yy ν) (Metric.diam (T ν)) := by
    intro ν x hx
    exact Metric.mem_closedBall.mpr (Metric.dist_le_diam_of_mem (hbdd _) hx (hyT ν))
  have hfT : ∀ ν : ℕ, f '' T ν = T (ν + 1) := by
    intro ν
    rw [hTdef]
    rw [← Set.range_comp]
    congr 1
    funext t
    exact (Function.iterate_succ_apply' f ν _).symm
  have hTinf : ∀ ν : ℕ, ∞ ∉ T ν := by
    rintro ν ⟨t, ht⟩
    exact hne_inf ν t ht
  -- ===== small topological toolkit =====
  -- (E) two-set dichotomy for a preconnected set avoiding the frontier
  have hdichot : ∀ (G A : Set ℂ̂), IsOpen G → IsPreconnected A →
      (A ∩ frontier G = ∅) → A ⊆ G ∨ A ∩ G = ∅ := by
    intro G A hG hA hAF
    by_cases hAG : A ∩ G = ∅
    · exact Or.inr hAG
    · left
      have hcover : A ⊆ G ∪ (closure G)ᶜ := by
        intro a ha
        by_cases haG : a ∈ G
        · exact Or.inl haG
        · refine Or.inr fun hacl => ?_
          have : a ∈ A ∩ frontier G := ⟨ha, hacl, fun hi => haG (interior_subset hi)⟩
          rw [hAF] at this
          exact this
      by_cases hA2 : A ∩ (closure G)ᶜ = ∅
      · intro a ha
        rcases hcover ha with h | h
        · exact h
        · exact absurd (Set.mem_inter ha h) (by rw [hA2]; exact fun h => h)
      · exfalso
        obtain ⟨a₁, ha₁⟩ := Set.nonempty_iff_ne_empty.mpr hAG
        obtain ⟨a₂, ha₂⟩ := Set.nonempty_iff_ne_empty.mpr hA2
        obtain ⟨x, hx⟩ := hA G (closure G)ᶜ hG isClosed_closure.isOpen_compl
          hcover ⟨a₁, ha₁.1, ha₁.2⟩ ⟨a₂, ha₂.1, ha₂.2⟩
        exact hx.2.2 (subset_closure hx.2.1)
  -- (B) frontier of an image under the (continuous, open) map `f`
  have hfrontier_image : ∀ G : Set ℂ̂, IsOpen G →
      frontier (f '' G) ⊆ f '' frontier G := by
    intro G hG x hx
    have hopen : IsOpen (f '' G) := hfo _ hG
    have hxcl : x ∈ closure (f '' G) := hx.1
    have hxni : x ∉ f '' G := by
      intro hmem
      exact hx.2 (by rw [hopen.interior_eq]; exact hmem)
    have hclos : closure (f '' G) ⊆ f '' closure G := by
      apply closure_minimal (Set.image_mono subset_closure)
      exact ((isClosed_closure.isCompact).image hcf).isClosed
    obtain ⟨d, hd', rfl⟩ := hclos hxcl
    have hdG : d ∉ G := fun hdG => hxni ⟨d, hdG, rfl⟩
    exact ⟨d, ⟨hd', fun hi => hdG (hG.interior_eq ▸ hi)⟩, rfl⟩
  -- (A) complements of closed balls in the sphere are preconnected
  have hcompl_ball_conn : ∀ (y : ℂ̂) (r : ℝ), 0 ≤ r →
      IsPreconnected ((Metric.closedBall y r)ᶜ : Set ℂ̂) := by
    intro y r hr
    -- helper: exteriors (in the squared-norm form) are preconnected in ℂ
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact_mod_cast (by norm_num : (1:ℕ) < 2)
    have hext : ∀ (mid : ℂ) (ρ : ℝ), IsPreconnected {z : ℂ | ρ < ‖z - mid‖^2} := by
      intro mid ρ
      rcases lt_trichotomy ρ 0 with hρ | hρ | hρ
      · have huniv : {z : ℂ | ρ < ‖z - mid‖^2} = Set.univ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          nlinarith [sq_nonneg ‖z - mid‖]
        rw [huniv]
        exact isPreconnected_univ
      · subst hρ
        have hpunct : {z : ℂ | (0:ℝ) < ‖z - mid‖^2} = {mid}ᶜ := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
          constructor
          · intro h he
            rw [he] at h
            simp at h
          · intro h
            have hz : z - mid ≠ 0 := sub_ne_zero.mpr h
            positivity
        rw [hpunct]
        exact (isConnected_compl_singleton_of_one_lt_rank hrank mid).isPreconnected
      · have hsq : ∀ z : ℂ, (ρ < ‖z - mid‖^2 ↔ Real.sqrt ρ < ‖z - mid‖) := by
          intro z
          rw [show (Real.sqrt ρ < ‖z - mid‖) ↔ ((Real.sqrt ρ)^2 < ‖z - mid‖^2) from
            (sq_lt_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).symm,
            Real.sq_sqrt hρ.le]
        have hs' : {z : ℂ | ρ < ‖z - mid‖^2} =
            (fun p : ℝ × ℂ => mid + (p.1 : ℂ) * p.2) ''
              ((Set.Ioi (Real.sqrt ρ)) ×ˢ (Metric.sphere (0:ℂ) 1)) := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioi,
            Metric.mem_sphere, dist_zero_right, hsq z]
          constructor
          · intro hz
            have hzpos : 0 < ‖z - mid‖ := lt_of_le_of_lt (Real.sqrt_nonneg _) hz
            have hzne : (‖z - mid‖ : ℂ) ≠ 0 := by
              exact_mod_cast (ne_of_gt hzpos)
            refine ⟨(‖z - mid‖, (‖z - mid‖ : ℂ)⁻¹ * (z - mid)), ⟨hz, ?_⟩, ?_⟩
            · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hzpos, inv_mul_cancel₀ hzpos.ne']
            · change mid + (‖z - mid‖ : ℂ) * ((‖z - mid‖ : ℂ)⁻¹ * (z - mid)) = z
              rw [← mul_assoc, mul_inv_cancel₀ hzne, one_mul]
              ring
          · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
            have htpos : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
            change Real.sqrt ρ < ‖mid + (t : ℂ) * u - mid‖
            rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos htpos, hu, mul_one]
            exact ht
        rw [hs']
        apply IsPreconnected.image
        · exact isPreconnected_Ioi.prod
            (isConnected_sphere hrank 0 zero_le_one).isPreconnected
        · exact (continuous_const.add
            ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd)).continuousOn
    -- describe the complement of the ball via the spherical distance
    have hset : ((Metric.closedBall y r)ᶜ : Set ℂ̂) = {w : ℂ̂ | r < sphericalDist y w} := by
      ext w
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, Set.mem_setOf_eq, not_le]
      rw [show dist w y = sphericalDist w y from rfl, sphericalDist_comm]
    rw [hset]
    induction y using OnePoint.rec with
    | infty =>
        -- the complement is the sphere reading of a plane convex set
        have hshape : {w : ℂ̂ | r < sphericalDist ∞ w} =
            (fun z : ℂ => (z : ℂ̂)) '' {z : ℂ | r < chordalDistInfty z} := by
          ext w
          induction w using OnePoint.rec with
          | infty =>
              simp only [Set.mem_setOf_eq]
              constructor
              · intro h
                rw [show sphericalDist ∞ ∞ = (0:ℝ) from rfl] at h
                exact absurd h (not_lt.mpr hr)
              · rintro ⟨z, _, hcontra⟩
                exact absurd hcontra (OnePoint.coe_ne_infty z)
          | coe z =>
              simp only [Set.mem_setOf_eq]
              rw [show sphericalDist ∞ ((z:ℂ̂)) = chordalDistInfty z from rfl]
              constructor
              · intro h
                exact ⟨z, h, rfl⟩
              · rintro ⟨z', hz', heq⟩
                rwa [← OnePoint.coe_eq_coe.mp heq]
        rw [hshape]
        have hEconv : Convex ℝ {z : ℂ | r < chordalDistInfty z} := by
          have hEeq : {z : ℂ | r < chordalDistInfty z} =
              {z : ℂ | r^2 * (1+‖z‖^2) < 4} := by
            ext z
            simp only [Set.mem_setOf_eq]
            unfold chordalDistInfty
            have hX : (0:ℝ) < 1 + ‖z‖^2 := by positivity
            have hsX : (0:ℝ) < Real.sqrt (1+‖z‖^2) := Real.sqrt_pos.mpr hX
            rw [lt_div_iff₀ hsX]
            constructor
            · intro h
              have h2 : (r * Real.sqrt (1+‖z‖^2))^2 < 2^2 :=
                (sq_lt_sq₀ (by positivity) (by norm_num)).mpr h
              rw [mul_pow, Real.sq_sqrt hX.le] at h2
              linarith
            · intro h
              have h2 : (r * Real.sqrt (1+‖z‖^2))^2 < 2^2 := by
                rw [mul_pow, Real.sq_sqrt hX.le]
                linarith
              exact (sq_lt_sq₀ (by positivity) (by norm_num)).mp h2
          rw [hEeq]
          rcases eq_or_lt_of_le hr with h0 | hrpos
          · have huniv : {z : ℂ | r^2 * (1+‖z‖^2) < 4} = Set.univ := by
              ext z
              simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, ← h0]
              norm_num
            rw [huniv]
            exact convex_univ
          · by_cases hbig : (4:ℝ) ≤ r^2
            · have hempty : {z : ℂ | r^2 * (1+‖z‖^2) < 4} = ∅ := by
                ext z
                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                nlinarith [sq_nonneg ‖z‖]
              rw [hempty]
              exact convex_empty
            · push Not at hbig
              have hr2 : (0:ℝ) < r^2 := by positivity
              have hball : {z : ℂ | r^2 * (1+‖z‖^2) < 4} =
                  Metric.ball (0:ℂ) (Real.sqrt (4/r^2 - 1)) := by
                ext z
                simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
                rw [show (‖z‖ < Real.sqrt (4/r^2-1)) ↔ (‖z‖^2 < 4/r^2 - 1) from
                  Real.lt_sqrt (norm_nonneg z)]
                constructor
                · intro h
                  rw [lt_sub_iff_add_lt, lt_div_iff₀ hr2]
                  nlinarith
                · intro h
                  rw [lt_sub_iff_add_lt, lt_div_iff₀ hr2] at h
                  nlinarith
              rw [hball]
              exact convex_ball 0 _
        exact hEconv.isPreconnected.image _ (OnePoint.continuous_coe.continuousOn)
    | coe a =>
        have hA2pos : (0:ℝ) < 1 + ‖a‖^2 := by positivity
        -- finite-point characterization
        have hfin : ∀ z : ℂ, (r < sphericalDist ((a:ℂ̂)) ((z:ℂ̂)) ↔
            r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2) := by
          intro z
          rw [sphericalDist_coe_coe]
          unfold chordalDist
          have hX : (0:ℝ) < 1 + ‖z‖^2 := by positivity
          have hsA : (0:ℝ) < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr hA2pos
          have hsX : (0:ℝ) < Real.sqrt (1 + ‖z‖^2) := Real.sqrt_pos.mpr hX
          rw [lt_div_iff₀ (mul_pos hsA hsX), norm_sub_rev a z]
          constructor
          · intro h
            have h2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
            rw [mul_pow, mul_pow, Real.sq_sqrt hA2pos.le, Real.sq_sqrt hX.le,
              mul_pow] at h2
            nlinarith [h2]
          · intro h
            apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
            rw [mul_pow, mul_pow, Real.sq_sqrt hA2pos.le, Real.sq_sqrt hX.le,
              mul_pow]
            nlinarith [h]
        -- infinity characterization
        have hinfc : (r < sphericalDist ((a:ℂ̂)) ∞ ↔ r^2 * (1 + ‖a‖^2) < 4) := by
          rw [show sphericalDist ((a:ℂ̂)) ∞ = chordalDistInfty a from rfl]
          unfold chordalDistInfty
          have hsA : (0:ℝ) < Real.sqrt (1 + ‖a‖^2) := Real.sqrt_pos.mpr hA2pos
          rw [lt_div_iff₀ hsA]
          constructor
          · intro h
            have h2 := (sq_lt_sq₀ (by positivity) (by norm_num)).mpr h
            rw [mul_pow, Real.sq_sqrt hA2pos.le] at h2
            linarith
          · intro h
            apply (sq_lt_sq₀ (by positivity) (by norm_num)).mp
            rw [mul_pow, Real.sq_sqrt hA2pos.le]
            linarith
        -- expansion of the recentered norm, for any nonzero scale factor
        have hmidexp : ∀ (β : ℝ), β ≠ 0 → ∀ z : ℂ,
            ‖z - ((4/β : ℝ) : ℂ) * a‖^2 =
              ‖z‖^2 - 2*((4/β))*(z * (starRingEnd ℂ) a).re + (4/β)^2*‖a‖^2 := by
          intro β hβne z
          have hconjmid : (starRingEnd ℂ) (((4/β : ℝ) : ℂ) * a) =
              ((4/β : ℝ) : ℂ) * (starRingEnd ℂ) a := by
            rw [map_mul, Complex.conj_ofReal]
          have hre : (z * (starRingEnd ℂ) (((4/β : ℝ) : ℂ) * a)).re =
              (4/β) * (z * (starRingEnd ℂ) a).re := by
            rw [hconjmid, show z * (((4/β:ℝ):ℂ) * (starRingEnd ℂ) a)
                = ((4/β:ℝ):ℂ) * (z * (starRingEnd ℂ) a) from by ring]
            simp [Complex.mul_re]
          have hnm : ‖((4/β : ℝ) : ℂ) * a‖^2 = (4/β)^2 * ‖a‖^2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm,
            ← Complex.sq_norm, hre, hnm]
          ring
        have hsubexp : ∀ z : ℂ, ‖z - a‖^2 =
            ‖z‖^2 - 2*(z * (starRingEnd ℂ) a).re + ‖a‖^2 := by
          intro z
          rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm]
          ring
        by_cases hβ : (0:ℝ) < 4 - r^2 * (1 + ‖a‖^2)
        · -- the ball misses ∞: exterior shape plus the point ∞
          have hβne0 : (4 - r^2 * (1 + ‖a‖^2)) ≠ 0 := ne_of_gt hβ
          obtain ⟨β, hβeq⟩ : ∃ b : ℝ, b = 4 - r^2 * (1 + ‖a‖^2) := ⟨_, rfl⟩
          have hβpos : 0 < β := hβeq ▸ hβ
          have hβne : β ≠ 0 := hβeq ▸ hβne0
          obtain ⟨mid, hmiddef⟩ : ∃ c : ℂ, c = ((4/β : ℝ) : ℂ) * a := ⟨_, rfl⟩
          obtain ⟨ρ, hρdef⟩ : ∃ p : ℝ,
            p = (16*‖a‖^2 - β*(4*‖a‖^2 - r^2*(1 + ‖a‖^2)))/β^2 := ⟨_, rfl⟩
          have hkey : ∀ z : ℂ, β^2 * (‖z - mid‖^2 - ρ) =
              β * (4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2)) := by
            intro z
            rw [hmiddef, hmidexp β hβne z, hsubexp z, hρdef, hβeq]
            field_simp
            ring
          have hEeq : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
              ρ < ‖z - mid‖^2) := by
            intro z
            constructor
            · intro h
              by_contra hno
              push Not at hno
              have hle : β^2*(‖z - mid‖^2 - ρ) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) (by linarith)
              rw [hkey z] at hle
              linarith [mul_pos hβpos
                (by linarith : (0:ℝ) < 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2))]
            · intro h
              by_contra hno
              push Not at hno
              have hge : 0 < β^2*(‖z - mid‖^2 - ρ) :=
                mul_pos (pow_pos hβpos 2) (by linarith)
              rw [hkey z] at hge
              linarith [mul_nonpos_of_nonneg_of_nonpos hβpos.le
                (by linarith : 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2) ≤ 0)]
          have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
              (fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ρ < ‖z - mid‖^2} ∪ {∞} := by
            ext w
            induction w using OnePoint.rec with
            | infty =>
                simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
                constructor
                · intro _
                  exact Or.inr trivial
                · intro _
                  exact hinfc.mpr (by linarith)
            | coe z =>
                simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
                rw [hfin z, hEeq z]
                constructor
                · intro h
                  exact Or.inl ⟨z, h, rfl⟩
                · rintro (⟨z', hz', heq⟩ | hbad)
                  · rwa [← OnePoint.coe_eq_coe.mp heq]
                  · exact absurd hbad (OnePoint.coe_ne_infty z)
          rw [hSet2]
          have hEimg : IsPreconnected
              ((fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ρ < ‖z - mid‖^2}) :=
            (hext mid ρ).image _ (OnePoint.continuous_coe.continuousOn)
          apply hEimg.subset_closure Set.subset_union_left
          intro w hw
          rcases hw with hw | hw
          · exact subset_closure hw
          · rw [Set.mem_singleton_iff] at hw
            subst hw
            rw [Metric.mem_closure_iff]
            intro ε hε
            set Rb : ℝ := max (Real.sqrt (max ρ 0) + 1) (2/ε + 1) with hRb
            have hRb1 : Real.sqrt (max ρ 0) + 1 ≤ Rb := le_max_left _ _
            have hRb2 : 2/ε + 1 ≤ Rb := le_max_right _ _
            have hRbpos : 0 < Rb :=
              lt_of_lt_of_le (by positivity) hRb1
            refine ⟨(((mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) : ℂ) : ℂ̂), ?_, ?_⟩
            · refine ⟨mid + ((Rb + ‖mid‖ : ℝ) : ℂ), ?_, rfl⟩
              simp only [Set.mem_setOf_eq, add_sub_cancel_left]
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (by positivity : (0:ℝ) < Rb + ‖mid‖)]
              have h1 : Real.sqrt (max ρ 0) < Rb + ‖mid‖ := by
                have := norm_nonneg mid
                linarith
              have h2 : max ρ 0 < (Rb + ‖mid‖)^2 := by
                rw [← Real.sq_sqrt (le_max_right ρ 0)]
                exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr h1
              exact lt_of_le_of_lt (le_max_left ρ 0) h2
            · have hznorm : Rb ≤ ‖mid + ((Rb + ‖mid‖ : ℝ) : ℂ)‖ := by
                have h1 : ‖(mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) - mid‖ = Rb + ‖mid‖ := by
                  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_pos (by positivity)]
                have h2 : ‖(mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) - mid‖ ≤
                    ‖mid + ((Rb + ‖mid‖ : ℝ) : ℂ)‖ + ‖mid‖ := norm_sub_le _ _
                linarith
              rw [show dist (∞ : ℂ̂) (((mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) : ℂ̂))
                = chordalDistInfty (mid + ((Rb + ‖mid‖ : ℝ) : ℂ)) from rfl]
              unfold chordalDistInfty
              set z : ℂ := mid + ((Rb + ‖mid‖ : ℝ) : ℂ)
              have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRbpos hznorm
              have hs1 : ‖z‖ < Real.sqrt (1 + ‖z‖^2) := by
                rw [show ‖z‖ = Real.sqrt (‖z‖^2) from (Real.sqrt_sq (norm_nonneg z)).symm]
                apply Real.sqrt_lt_sqrt (by positivity)
                rw [Real.sq_sqrt (sq_nonneg ‖z‖)]
                linarith
              have hs2 : (0:ℝ) < Real.sqrt (1 + ‖z‖^2) := lt_trans hzpos hs1
              rw [div_lt_iff₀ hs2]
              have hεRb : 2 < ε * Rb := by
                have h3 : ε * (2/ε + 1) = 2 + ε := by field_simp
                nlinarith [hRb2, hε]
              calc (2:ℝ) < ε * Rb := hεRb
                _ ≤ ε * ‖z‖ := by nlinarith [hznorm, hε]
                _ ≤ ε * Real.sqrt (1 + ‖z‖^2) := by nlinarith [hs1, hε]
        · -- the ball engulfs ∞: plane convex shape only
          push Not at hβ
          have hnoinf : (∞ : ℂ̂) ∉ {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} := by
            intro h
            have h1 := hinfc.mp h
            linarith
          rcases eq_or_lt_of_le hβ with hβ0 | hβneg
          · -- halfplane case: r²(1+‖a‖²) = 4
            have hr2A : r^2 * (1 + ‖a‖^2) = 4 := by linarith
            have hEeq0 : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
                8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4) := by
              intro z
              rw [hsubexp z, hr2A]
              constructor
              · intro h
                nlinarith
              · intro h
                nlinarith
            have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
                (fun z : ℂ => (z:ℂ̂)) ''
                  {z : ℂ | 8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4} := by
              ext w
              induction w using OnePoint.rec with
              | infty =>
                  simp only [Set.mem_setOf_eq]
                  constructor
                  · intro h
                    exact absurd h hnoinf
                  · rintro ⟨z', _, heq⟩
                    exact absurd heq (OnePoint.coe_ne_infty z')
              | coe z =>
                  simp only [Set.mem_setOf_eq]
                  rw [hfin z, hEeq0 z]
                  constructor
                  · intro h
                    exact ⟨z, h, rfl⟩
                  · rintro ⟨z', hz', heq⟩
                    rwa [← OnePoint.coe_eq_coe.mp heq]
            rw [hSet2]
            have hlin : IsLinearMap ℝ
                (⇑(((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ))) :=
              LinearMap.isLinear _
            have hconv0 : Convex ℝ {z : ℂ |
                (((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ)) z <
                  4*‖a‖^2 - 4} :=
              convex_halfSpace_lt hlin _
            have hseteq : {z : ℂ | 8*((z * (starRingEnd ℂ) a).re) < 4*‖a‖^2 - 4} =
                {z : ℂ | (((8*a.re) • Complex.reLm + (8*a.im) • Complex.imLm : ℂ →ₗ[ℝ] ℝ)) z <
                  4*‖a‖^2 - 4} := by
              ext z
              simp only [Set.mem_setOf_eq, LinearMap.add_apply, LinearMap.smul_apply,
                Complex.reLm_coe, Complex.imLm_coe, smul_eq_mul, Complex.mul_re,
                Complex.conj_re, Complex.conj_im]
              constructor <;> intro h <;> nlinarith [h]
            rw [hseteq]
            exact (hconv0.isPreconnected).image _ (OnePoint.continuous_coe.continuousOn)
          · -- disk case: β < 0
            have hβne0 : (4 - r^2 * (1 + ‖a‖^2)) ≠ 0 := ne_of_lt hβneg
            obtain ⟨β, hβeq⟩ : ∃ b : ℝ, b = 4 - r^2 * (1 + ‖a‖^2) := ⟨_, rfl⟩
            have hβnegβ : β < 0 := hβeq ▸ hβneg
            have hβne : β ≠ 0 := hβeq ▸ hβne0
            have hβsq : 0 < β^2 := by
              have h1 : 0 < β * β := mul_pos_of_neg_of_neg hβnegβ hβnegβ
              nlinarith [h1]
            obtain ⟨mid, hmiddef⟩ : ∃ c : ℂ, c = ((4/β : ℝ) : ℂ) * a := ⟨_, rfl⟩
            obtain ⟨ρ, hρdef⟩ : ∃ p : ℝ,
              p = (16*‖a‖^2 - β*(4*‖a‖^2 - r^2*(1 + ‖a‖^2)))/β^2 := ⟨_, rfl⟩
            have hkey : ∀ z : ℂ, β^2 * (‖z - mid‖^2 - ρ) =
                β * (4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2)) := by
              intro z
              rw [hmiddef, hmidexp β hβne z, hsubexp z, hρdef, hβeq]
              field_simp
              ring
            have hEeq : ∀ z : ℂ, (r^2 * (1 + ‖a‖^2) * (1+‖z‖^2) < 4 * ‖z - a‖^2 ↔
                ‖z - mid‖^2 < ρ) := by
              intro z
              constructor
              · intro h
                by_contra hno
                push Not at hno
                have hge : 0 ≤ β^2*(‖z - mid‖^2 - ρ) :=
                  mul_nonneg (sq_nonneg β) (by linarith)
                rw [hkey z] at hge
                linarith [mul_neg_of_neg_of_pos hβnegβ
                  (by linarith : (0:ℝ) < 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2))]
              · intro h
                by_contra hno
                push Not at hno
                have hlt : β^2*(‖z - mid‖^2 - ρ) < 0 :=
                  mul_neg_of_pos_of_neg hβsq (by linarith)
                rw [hkey z] at hlt
                nlinarith [hlt, hβnegβ.le,
                  (by linarith : 4*‖z - a‖^2 - r^2*(1 + ‖a‖^2)*(1+‖z‖^2) ≤ 0)]
            have hSet2 : {w : ℂ̂ | r < sphericalDist ((a:ℂ̂)) w} =
                (fun z : ℂ => (z:ℂ̂)) '' {z : ℂ | ‖z - mid‖^2 < ρ} := by
              ext w
              induction w using OnePoint.rec with
              | infty =>
                  simp only [Set.mem_setOf_eq]
                  constructor
                  · intro h
                    exact absurd h hnoinf
                  · rintro ⟨z', _, heq⟩
                    exact absurd heq (OnePoint.coe_ne_infty z')
              | coe z =>
                  simp only [Set.mem_setOf_eq]
                  rw [hfin z, hEeq z]
                  constructor
                  · intro h
                    exact ⟨z, h, rfl⟩
                  · rintro ⟨z', hz', heq⟩
                    rwa [← OnePoint.coe_eq_coe.mp heq]
            rw [hSet2]
            have hconv : Convex ℝ {z : ℂ | ‖z - mid‖^2 < ρ} := by
              by_cases hρpos : 0 < ρ
              · have hball : {z : ℂ | ‖z - mid‖^2 < ρ} =
                    Metric.ball mid (Real.sqrt ρ) := by
                  ext z
                  simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
                  exact (Real.lt_sqrt (norm_nonneg _)).symm
                rw [hball]
                exact convex_ball mid _
              · have hempty : {z : ℂ | ‖z - mid‖^2 < ρ} = ∅ := by
                  ext z
                  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
                  push Not at hρpos
                  nlinarith [sq_nonneg ‖z - mid‖]
                rw [hempty]
                exact convex_empty
            exact (hconv.isPreconnected).image _ (OnePoint.continuous_coe.continuousOn)
  -- distances between the three reference points 0, 1, ∞
  have hd0i : (5/4 : ℝ) ≤ dist (((0 : ℂ) : ℂ̂)) (∞ : ℂ̂) := by
    have : dist (((0 : ℂ) : ℂ̂)) (∞ : ℂ̂) = chordalDistInfty 0 := rfl
    rw [this]
    unfold chordalDistInfty
    simp
    norm_num
  have hd1i : (5/4 : ℝ) ≤ dist (((1 : ℂ) : ℂ̂)) (∞ : ℂ̂) := by
    have h1 : dist (((1 : ℂ) : ℂ̂)) (∞ : ℂ̂) = chordalDistInfty 1 := rfl
    rw [h1]
    unfold chordalDistInfty
    have hs : Real.sqrt (1 + ‖(1 : ℂ)‖ ^ 2) = Real.sqrt 2 := by norm_num
    rw [hs]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [le_div_iff₀ h2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hd01 : (5/4 : ℝ) ≤ dist (((0 : ℂ) : ℂ̂)) (((1 : ℂ) : ℂ̂)) := by
    have h1 : dist (((0 : ℂ) : ℂ̂)) (((1 : ℂ) : ℂ̂)) = chordalDist 0 1 := rfl
    rw [h1]
    unfold chordalDist
    have hs0 : Real.sqrt (1 + ‖(0 : ℂ)‖ ^ 2) = 1 := by norm_num
    have hs : Real.sqrt (1 + ‖(1 : ℂ)‖ ^ 2) = Real.sqrt 2 := by norm_num
    rw [hs0, hs]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : ‖(0 : ℂ) - 1‖ = 1 := by norm_num
    rw [h3, one_mul, le_div_iff₀ h2]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  -- two of the three reference points lie outside any small closed ball
  have htwo : ∀ (y : ℂ̂) (r : ℝ), r ≤ 1/2 →
      ∃ p q : ℂ̂, p ∉ Metric.closedBall y r ∧ q ∉ Metric.closedBall y r ∧
        (5/4 : ℝ) ≤ dist p q := by
    intro y r hr
    by_cases h0 : (((0 : ℂ) : ℂ̂)) ∈ Metric.closedBall y r
    · refine ⟨(((1 : ℂ) : ℂ̂)), (∞ : ℂ̂), ?_, ?_, hd1i⟩
      · intro h1
        rw [Metric.mem_closedBall] at h0 h1
        have := dist_triangle (((0 : ℂ) : ℂ̂)) y (((1 : ℂ) : ℂ̂))
        rw [dist_comm y _] at this
        linarith [hd01]
      · intro h1
        rw [Metric.mem_closedBall] at h0 h1
        have := dist_triangle (((0 : ℂ) : ℂ̂)) y (∞ : ℂ̂)
        rw [dist_comm y _] at this
        linarith [hd0i]
    · by_cases h1 : (((1 : ℂ) : ℂ̂)) ∈ Metric.closedBall y r
      · refine ⟨(((0 : ℂ) : ℂ̂)), (∞ : ℂ̂), h0, ?_, hd0i⟩
        intro h2
        rw [Metric.mem_closedBall] at h1 h2
        have := dist_triangle (((1 : ℂ) : ℂ̂)) y (∞ : ℂ̂)
        rw [dist_comm y _] at this
        linarith [hd1i]
      · exact ⟨(((0 : ℂ) : ℂ̂)), (((1 : ℂ) : ℂ̂)), h0, h1, hd01⟩
  -- normality of the iterate family on an open set W around the base trace
  obtain ⟨W, hWopen, hWsub, hKγW, hWnorm⟩ : ∃ W : Set ℂ̂, IsOpen W ∧
      W ⊆ fcOrbit f U N₀ ∧ T 0 ⊆ W ∧
      IsNormal (Set.range fun n : ℕ => f^[n]) W := by
    -- each trace point has an open normality neighborhood inside the component
    have hnb : ∀ x : ↥(T 0), ∃ V : Set ℂ̂, IsOpen V ∧ (x:ℂ̂) ∈ V ∧
        V ⊆ fcOrbit f U N₀ ∧ IsNormal (Set.range fun n : ℕ => f^[n]) V := by
      rintro ⟨x, hx⟩
      have hxV : x ∈ fcOrbit f U N₀ := by
        obtain ⟨t, ht⟩ := hx
        rw [← ht]
        simpa using hmem 0 t
      have hxF : x ∈ FatouSet f := hVfc.subset_fatouSet hxV
      obtain ⟨Ux, hUxn, hUxN⟩ := mem_fatouSet_iff.mp hxF
      exact ⟨interior Ux ∩ fcOrbit f U N₀,
        isOpen_interior.inter hVopen,
        ⟨mem_interior_iff_mem_nhds.mpr hUxn, hxV⟩,
        Set.inter_subset_right,
        hUxN.mono (fun y hy => interior_subset hy.1)⟩
    choose Vx hVo hVx hVsub hVn using hnb
    obtain ⟨s, hs⟩ := (hTcompact 0).elim_finite_subcover Vx hVo
      (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hVx ⟨x, hx⟩⟩)
    have hUnorm : ∀ s : Finset ↥(T 0),
        IsNormal (Set.range fun n : ℕ => f^[n]) (⋃ i ∈ s, Vx i) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro seq
          refine ⟨id, strictMono_id, (seq 0 : ℂ̂ → ℂ̂), ?_⟩
          intro u hu x hx
          simp at hx
      | insert x s hxs ih =>
          rw [Finset.set_biUnion_insert]
          exact IsNormal.union (hVo x) (isOpen_biUnion fun i _ => hVo i) (hVn x) ih
    exact ⟨⋃ i ∈ s, Vx i, isOpen_biUnion fun i _ => hVo i,
      Set.iUnion₂_subset fun i _ => hVsub i, hs, hUnorm s⟩
  -- compact thickening K of the base trace inside W
  obtain ⟨rK, hrKpos, hrKsub⟩ :=
    (hTcompact 0).exists_cthickening_subset_open hWopen hKγW
  set K : Set ℂ̂ := Metric.cthickening rK (T 0) with hKdef
  have hKcomp : IsCompact K := Metric.isClosed_cthickening.isCompact
  have hKsubW : K ⊆ W := hrKsub
  have hKγint : T 0 ⊆ interior K := by
    intro x hx
    have h1 : x ∈ Metric.thickening rK (T 0) :=
      Metric.self_subset_thickening hrKpos _ hx
    exact interior_maximal (Metric.thickening_subset_cthickening _ _)
      Metric.isOpen_thickening h1
  -- STEP B: full-sequence collapse of the trace diameters
  have hdiam : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν →
      Metric.diam (T ν) ≤ ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hfreq : ∃ᶠ ν in Filter.atTop, ε < Metric.diam (T ν) := by
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨ν, h1, h2⟩ := hcon N
      exact ⟨ν, h1, h2⟩
    obtain ⟨ψ, hψmono, hψd⟩ := Filter.extraction_of_frequently_atTop hfreq
    obtain ⟨ρ, hρmono, g, hg⟩ := hWnorm (fun k => ⟨f^[ψ k], ⟨ψ k, rfl⟩⟩)
    have hφmono : StrictMono (fun k => ψ (ρ k)) := hψmono.comp hρmono
    have hglim : TendstoLocallyUniformlyOn (fun k => f^[ψ (ρ k)]) g Filter.atTop
        (interior K) := hg.mono (interior_subset.trans hKsubW)
    -- the base component wanders
    have hWand : IsWandering f (fcOrbit f U N₀) := by
      intro i j hij
      change Disjoint (fcOrbit f (fcOrbit f U N₀) i) (fcOrbit f (fcOrbit f U N₀) j)
      rw [← fcOrbit_add N₀ i hf hd1 hU, ← fcOrbit_add N₀ j hf hd1 hU]
      exact hW (by omega)
    have hconst := eventually_constant_limit_of_wandering hf hd hVfc hWand hφmono
      hKcomp (hKsubW.trans hWsub) hglim
    -- the limit is constant on the connected base trace
    have hT0conn : IsPreconnected (T 0) := (isConnected_range (hTcont 0)).isPreconnected
    have hcc : ∀ t : unitInterval, g ((γ t : ℂ̂)) = g ((γ 0 : ℂ̂)) := by
      intro t
      have hsubcc : T 0 ⊆ connectedComponentIn (interior K) ((γ 0 : ℂ̂)) :=
        hT0conn.subset_connectedComponentIn ⟨0, rfl⟩ hKγint
      have hcompeq : connectedComponentIn (interior K) ((γ t : ℂ̂)) =
          connectedComponentIn (interior K) ((γ 0 : ℂ̂)) :=
        (connectedComponentIn_eq (hsubcc ⟨t, rfl⟩)).symm
      exact hconst _ (hKγint ⟨t, rfl⟩) _ (hKγint ⟨0, rfl⟩) hcompeq
    -- uniform convergence on the compact trace
    have hUnif : TendstoUniformlyOn (fun k => f^[ψ (ρ k)]) g Filter.atTop (T 0) :=
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior).mp
        hglim) (T 0) hKγint (hTcompact 0)
    rw [Metric.tendstoUniformlyOn_iff] at hUnif
    obtain ⟨k, hk⟩ := (hUnif (ε/4) (by positivity)).exists
    -- diameter bound at time ψ (ρ k), contradicting the frequent lower bound
    have hdle : Metric.diam (T (ψ (ρ k))) ≤ ε/2 := by
      apply Metric.diam_le_of_forall_dist_le (by positivity)
      rintro x ⟨t, rfl⟩ y ⟨t', rfl⟩
      have e1 : dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t : ℂ̂))) < ε/4 :=
        hk ((γ t : ℂ̂)) ⟨t, rfl⟩
      have e2 : dist (g ((γ t' : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) < ε/4 :=
        hk ((γ t' : ℂ̂)) ⟨t', rfl⟩
      have e3 : g ((γ t : ℂ̂)) = g ((γ t' : ℂ̂)) := by
        rw [hcc t, hcc t']
      calc dist (f^[ψ (ρ k)] ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂)))
          ≤ dist (f^[ψ (ρ k)] ((γ t : ℂ̂))) (g ((γ t : ℂ̂))) +
            dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) := dist_triangle _ _ _
        _ = dist (g ((γ t : ℂ̂))) (f^[ψ (ρ k)] ((γ t : ℂ̂))) +
            dist (g ((γ t' : ℂ̂))) (f^[ψ (ρ k)] ((γ t' : ℂ̂))) := by
              rw [dist_comm, e3]
        _ ≤ ε/2 := by linarith
    linarith [hψd (ρ k)]
  -- ===== fixed constants =====
  obtain ⟨sB, hsBpos, hsB⟩ : ∃ s : ℝ, 0 < s ∧ (∞ ∈ FatouSet f →
      Metric.ball (∞ : ℂ̂) s ⊆ connectedComponentIn (FatouSet f) ∞) := by
    by_cases hFinf : ∞ ∈ FatouSet f
    · have hopen : IsOpen (connectedComponentIn (FatouSet f) ∞) :=
        (isFatouComponent_connectedComponentIn hFinf).isOpen
      obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.mp hopen ∞
        (mem_connectedComponentIn hFinf)
      exact ⟨s, hs, fun _ => hsub⟩
    · exact ⟨1, one_pos, fun h => absurd h hFinf⟩
  obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ u v : ℂ̂, dist u v < η →
      dist (f u) (f v) < 1/8 := by
    have huc : UniformContinuous f :=
      CompactSpace.uniformContinuous_of_continuous hcf
    obtain ⟨η, hη, h⟩ := Metric.uniformContinuous_iff.mp huc (1/8) (by norm_num)
    exact ⟨η, hη, fun u v huv => h huv⟩
  set δ : ℝ := min (min (η/5) (1/100)) (sB/3) with hδdef
  have hδpos : 0 < δ := by
    apply lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hδη : 4 * δ < η := by
    have h1 : δ ≤ η/5 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδsmall : δ ≤ 1/100 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδsB : 3 * δ ≤ sB := by
    have h1 : δ ≤ sB/3 := min_le_right _ _
    linarith
  obtain ⟨N, hN⟩ := hdiam δ hδpos
  -- ===== witness selection: a late enclosed Julia point =====
  obtain ⟨n, hnN, Γ, hΓeq, w, hwJ, hwtr, hwinf⟩ := hyes N
  have hdT : ∀ k : ℕ, Metric.diam (T (n + k)) ≤ δ := fun k =>
    hN (n + k) (le_trans hnN (Nat.le_add_right n k))
  -- the sphere trace of the selected reading is the forward trace at time `n`
  have hΓsph : ∀ t : unitInterval, ((Γ t : ℂ) : ℂ̂) = f^[n] ((γ t : ℂ̂)) := by
    intro t
    rw [hΓeq t]
    exact hcoe_chart _ (hne_inf n t)
  have hTrange : (Set.range fun t : unitInterval => ((Γ t : ℂ̂))) = T n :=
    congrArg Set.range (funext hΓsph)
  have hwtr' : w ∉ T n := by rw [← hTrange]; exact hwtr
  have hwinf' : w ∉ connectedComponentIn ((T n)ᶜ) ∞ := by
    rw [← hTrange]; exact hwinf
  -- ===== base stage: a small open set with Julia point and frontier on the trace =====
  obtain ⟨O, ζ, hOopen, hζO, hζJ, hOfr, hOsub⟩ : ∃ (O : Set ℂ̂) (ζ : ℂ̂),
      IsOpen O ∧ ζ ∈ O ∧ ζ ∈ JuliaSet f ∧ frontier O ⊆ T n ∧
      O ⊆ Metric.closedBall (yy n) (2 * Metric.diam (T n)) := by
    -- the trace complement is open; its components are open with frontier on
    -- the trace
    set F : Set ℂ̂ := (T n)ᶜ with hFdef
    have hFopen : IsOpen F := (hTcompact n).isClosed.isOpen_compl
    have hwF : w ∈ F := hwtr'
    have hinfF : (∞ : ℂ̂) ∈ F := hTinf n
    have hfrCC : ∀ p : ℂ̂, frontier (connectedComponentIn F p) ⊆ T n := by
      intro p x hx
      by_contra hxT
      have hxF : x ∈ F := hxT
      have hCopen : IsOpen (connectedComponentIn F p) := hFopen.connectedComponentIn
      have hxnC : x ∉ connectedComponentIn F p := fun h =>
        hx.2 (by rw [hCopen.interior_eq]; exact h)
      have hxx : x ∈ connectedComponentIn F x := mem_connectedComponentIn hxF
      obtain ⟨y, hyx, hyC⟩ :=
        mem_closure_iff.mp hx.1 _ hFopen.connectedComponentIn hxx
      exact hxnC (by
        rw [connectedComponentIn_eq hyC, ← connectedComponentIn_eq hyx]
        exact hxx)
    -- `∞` is not in the witness component
    have hinfO : (∞ : ℂ̂) ∉ connectedComponentIn F w := by
      intro h
      apply hwinf'
      rw [← connectedComponentIn_eq h]
      exact mem_connectedComponentIn hwF
    -- diameter data
    set d₀ : ℝ := Metric.diam (T n) with hd₀def
    have hd₀nn : (0:ℝ) ≤ d₀ := Metric.diam_nonneg
    have hd₀δ : d₀ ≤ δ := by
      rw [hd₀def]
      have := hdT 0
      rwa [Nat.add_zero] at this
    -- dichotomy of the components against the complement of the doubled
    -- trace ball
    have hAconn : IsPreconnected ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) :=
      hcompl_ball_conn (yy n) (2*d₀) (by linarith)
    have hAdisj : ∀ p : ℂ̂, ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩
        frontier (connectedComponentIn F p) = ∅ := by
      intro p
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx1, hx2⟩
      have h1 : x ∈ T n := hfrCC p hx2
      have h2 : dist x (yy n) ≤ d₀ := Metric.mem_closedBall.mp (hTsubB n h1)
      exact hx1 (Metric.mem_closedBall.mpr (by linarith))
    rcases hdichot (connectedComponentIn F w) ((Metric.closedBall (yy n) (2*d₀))ᶜ)
        hFopen.connectedComponentIn hAconn (hAdisj w) with hsub | hdisj2
    · -- the ball complement sits inside the witness component; the trace is
      -- chordally near `∞`
      have hyinf : dist (∞ : ℂ̂) (yy n) ≤ 2*d₀ := by
        by_contra hfar
        push Not at hfar
        have hinfA : (∞:ℂ̂) ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) := by
          intro hball
          exact absurd (Metric.mem_closedBall.mp hball) (not_le.mpr hfar)
        exact hinfO (hsub hinfA)
      by_cases hFinf : ∞ ∈ FatouSet f
      · -- `∞` is a Fatou point: its component would swallow the orbit component
        exfalso
        have hyy : yy n ∈ Metric.ball (∞:ℂ̂) sB := by
          rw [Metric.mem_ball, dist_comm]
          have h1 : (2:ℝ)*d₀ ≤ 2*δ := by linarith
          have h2 : (2:ℝ)*δ < 3*δ := by linarith
          linarith [hδsB, hyinf]
        have hyyV : yy n ∈ fcOrbit f U (N₀ + n) := hmem n 0
        have hVeq : fcOrbit f U (N₀ + n) = connectedComponentIn (FatouSet f) ∞ :=
          (isFatouComponent_fcOrbit (N₀+n) hf hd1 hU).eq_of_mem
            (isFatouComponent_connectedComponentIn hFinf) hyyV (hsB hFinf hyy)
        exact hinf (N₀ + n) (by rw [hVeq]; exact mem_connectedComponentIn hFinf)
      · -- `∞` is a Julia point: its own component is confined instead
        have hζJ' : (∞:ℂ̂) ∈ JuliaSet f := hFinf
        refine ⟨connectedComponentIn F ∞, ∞, hFopen.connectedComponentIn,
          mem_connectedComponentIn hinfF, hζJ', hfrCC ∞, ?_⟩
        rcases hdichot (connectedComponentIn F ∞) ((Metric.closedBall (yy n) (2*d₀))ᶜ)
            hFopen.connectedComponentIn hAconn (hAdisj ∞) with hsub2 | hdisj3
        · -- impossible: the witness component and the `∞`-component would
          -- share the (nonempty) ball complement
          exfalso
          obtain ⟨p, -, hp, -, -⟩ := htwo (yy n) (2*d₀) (by linarith)
          have hpA : p ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) := hp
          apply hwinf'
          rw [connectedComponentIn_eq (hsub2 hpA),
            ← connectedComponentIn_eq (hsub hpA)]
          exact mem_connectedComponentIn hwF
        · intro x hx
          by_contra hxout
          have hmemint : x ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩
              connectedComponentIn F ∞ := ⟨hxout, hx⟩
          rw [hdisj3] at hmemint
          exact hmemint
    · -- the witness component is confined to the doubled trace ball
      refine ⟨connectedComponentIn F w, w, hFopen.connectedComponentIn,
        mem_connectedComponentIn hwF, hwJ, hfrCC w, ?_⟩
      intro x hx
      by_contra hxout
      have hmemint : x ∈ ((Metric.closedBall (yy n) (2*d₀))ᶜ : Set ℂ̂) ∩
          connectedComponentIn F w := ⟨hxout, hx⟩
      rw [hdisj2] at hmemint
      exact hmemint
  -- ===== confinement induction =====
  have hR : ∀ k : ℕ, frontier (f^[k] '' O) ⊆ T (n + k) ∧
      f^[k] '' O ⊆ Metric.closedBall (yy (n + k)) (2 * Metric.diam (T (n + k))) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp only [Function.iterate_zero, Set.image_id, Nat.add_zero]
          exact hOfr
        · simp only [Function.iterate_zero, Set.image_id, Nat.add_zero]
          exact hOsub
    | succ k ih =>
        obtain ⟨ihf, ihb⟩ := ih
        have himg1 : f^[k+1] '' O = f '' (f^[k] '' O) := by
          rw [Function.iterate_succ', Set.image_comp]
        -- (i) the frontier of the next image lies on the next trace
        have hfr1 : frontier (f^[k+1] '' O) ⊆ T (n + (k+1)) := by
          rw [himg1]
          intro x hx
          obtain ⟨u, hu, rfl⟩ := hfrontier_image (f^[k] '' O)
            (hopen_iter k _ hOopen) hx
          have h1 : u ∈ T (n + k) := ihf hu
          have h2 : f u ∈ f '' T (n+k) := Set.mem_image_of_mem f h1
          rw [hfT (n+k)] at h2
          rwa [show n + (k+1) = (n + k) + 1 from by omega]
        -- (ii) uniform continuity keeps the next image below the safe scale
        have hsmall : ∀ u' v' : ℂ̂, u' ∈ f^[k+1] '' O → v' ∈ f^[k+1] '' O →
            dist u' v' < 1/8 := by
          intro u' v' hu' hv'
          rw [himg1] at hu' hv'
          obtain ⟨u, hu, rfl⟩ := hu'
          obtain ⟨v, hv, rfl⟩ := hv'
          apply hη
          have h1 := Metric.mem_closedBall.mp (ihb hu)
          have h2 := Metric.mem_closedBall.mp (ihb hv)
          have h3 : Metric.diam (T (n+k)) ≤ δ := hdT k
          calc dist u v ≤ dist u (yy (n+k)) + dist (yy (n+k)) v := dist_triangle _ _ _
            _ ≤ 2*Metric.diam (T (n+k)) + 2*Metric.diam (T (n+k)) := by
                rw [dist_comm (yy (n+k)) v]
                linarith
            _ ≤ 4*δ := by linarith
            _ < η := hδη
        refine ⟨hfr1, ?_⟩
        -- (iii) dichotomy at the next time pins the image in the small ball
        set d1 : ℝ := Metric.diam (T (n + (k+1))) with hd1def
        have hd1nn : (0:ℝ) ≤ d1 := Metric.diam_nonneg
        have hAconn : IsPreconnected
            ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) :=
          hcompl_ball_conn _ _ (by linarith)
        have hAdisj : ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) ∩
            frontier (f^[k+1] '' O) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro x ⟨hx1, hx2⟩
          have h1 : x ∈ T (n+(k+1)) := hfr1 hx2
          have h2 : dist x (yy (n+(k+1))) ≤ d1 :=
            Metric.mem_closedBall.mp (hTsubB _ h1)
          exact hx1 (Metric.mem_closedBall.mpr (by linarith))
        have hopenG : IsOpen (f^[k+1] '' O) := hopen_iter (k+1) _ hOopen
        rcases hdichot (f^[k+1] '' O) _ hopenG hAconn hAdisj with hsubA | hdisjA
        · -- impossible: the huge ball complement cannot fit in a tiny image
          exfalso
          have hd1δ : d1 ≤ δ := hdT (k+1)
          obtain ⟨p, q, hp, hq, hpq⟩ := htwo (yy (n+(k+1))) (2*d1)
            (by linarith [hδsmall])
          have hpG : p ∈ f^[k+1] '' O := hsubA hp
          have hqG : q ∈ f^[k+1] '' O := hsubA hq
          have := hsmall p q hpG hqG
          linarith
        · intro x hx
          by_contra hxout
          have hmemint : x ∈ ((Metric.closedBall (yy (n+(k+1))) (2*d1))ᶜ : Set ℂ̂) ∩
              (f^[k+1] '' O) := ⟨hxout, hx⟩
          rw [hdisjA] at hmemint
          exact hmemint
  -- pairwise distance bound on the forward images
  have hconf : ∀ (k : ℕ) (u v : ℂ̂), u ∈ f^[k] '' O → v ∈ f^[k] '' O →
      dist u v ≤ 4 * Metric.diam (T (n + k)) := by
    intro k u v hu hv
    have h1 := Metric.mem_closedBall.mp ((hR k).2 hu)
    have h2 := Metric.mem_closedBall.mp ((hR k).2 hv)
    calc dist u v ≤ dist u (yy (n + k)) + dist (yy (n + k)) v := dist_triangle _ _ _
      _ ≤ 2 * Metric.diam (T (n + k)) + 2 * Metric.diam (T (n + k)) := by
          rw [dist_comm (yy (n + k)) v]; linarith
      _ = 4 * Metric.diam (T (n + k)) := by ring
  -- ===== final stage: normality at the Julia point ζ =====
  have hζF : ζ ∈ FatouSet f := by
    refine mem_fatouSet_iff.mpr ⟨O, hOopen.mem_nhds hζO, ?_⟩
    intro seq
    choose e he using fun k => (seq k).2
    by_cases hbdd : ∃ M : ℕ, ∀ k : ℕ, e k ≤ M
    · -- bounded exponents: pigeonhole a constant subsequence
      obtain ⟨M, hM⟩ := hbdd
      obtain ⟨v', hv'⟩ := Finite.exists_infinite_fiber
        (fun k : ℕ => (⟨e k, Nat.lt_succ_of_le (hM k)⟩ : Fin (M + 1)))
      have hinfv : {k : ℕ | e k = (v' : ℕ)}.Infinite := by
        refine (Set.infinite_coe_iff.mp hv').mono fun k hk => ?_
        simpa [Fin.ext_iff] using hk
      obtain ⟨ψ, hψ, hψe⟩ := Filter.extraction_of_frequently_atTop
        (Nat.frequently_atTop_iff_infinite.mpr hinfv)
      have hbase : TendstoLocallyUniformlyOn (fun _ : ℕ => f^[(v' : ℕ)])
          f^[(v' : ℕ)] Filter.atTop O := by
        intro u hu w _
        exact ⟨O, self_mem_nhdsWithin,
          Filter.Eventually.of_forall fun k y _ => refl_mem_uniformity hu⟩
      refine ⟨ψ, hψ, f^[(v' : ℕ)], hbase.congr fun j y _ => ?_⟩
      have h1 : (seq (ψ j) : ℂ̂ → ℂ̂) y = f^[e (ψ j)] y :=
        (congrFun (he (ψ j)) y).symm
      rw [h1, hψe j]
    · -- unbounded exponents: the confined images force a constant limit
      push Not at hbdd
      have hfreq : ∀ j : ℕ, ∃ᶠ k in Filter.atTop, j ≤ e k := by
        intro j
        rw [Nat.frequently_atTop_iff_infinite]
        by_contra hfin
        rw [Set.not_infinite] at hfin
        obtain ⟨M₀, hM₀⟩ := (hfin.image e).bddAbove
        obtain ⟨k, hk⟩ := hbdd (max M₀ j)
        have hjk : j ≤ e k := le_of_lt (lt_of_le_of_lt (le_max_right M₀ j) hk)
        have h1 : e k ≤ M₀ := hM₀ (Set.mem_image_of_mem e hjk)
        exact absurd hk (not_lt.mpr (h1.trans (le_max_left M₀ j)))
      obtain ⟨ψ, hψ, hψe⟩ := Filter.extraction_forall_of_frequently hfreq
      obtain ⟨q, _, χ, hχ, hχtend⟩ := isCompact_univ.tendsto_subseq
        (x := fun k => f^[e (ψ k)] ζ) (fun k => Set.mem_univ _)
      have htu : TendstoUniformlyOn (fun i => f^[e (ψ (χ i))]) (fun _ => q)
          Filter.atTop O := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        obtain ⟨N₁, hN₁⟩ := hdiam (ε/16) (by positivity)
        have hev1 : ∀ᶠ i in Filter.atTop, dist (f^[e (ψ (χ i))] ζ) q < ε/4 :=
          (Metric.tendsto_nhds.mp hχtend) _ (by positivity)
        have hev2 : ∀ᶠ i in Filter.atTop, N₁ ≤ i := Filter.eventually_ge_atTop N₁
        filter_upwards [hev1, hev2] with i hi1 hi2
        intro x hx
        have hEbig : N₁ ≤ e (ψ (χ i)) := by
          have h1 : i ≤ χ i := hχ.le_apply
          have h2 : χ i ≤ e (ψ (χ i)) := hψe (χ i)
          omega
        have hdE : Metric.diam (T (n + e (ψ (χ i)))) ≤ ε/16 :=
          hN₁ _ (le_trans hEbig (Nat.le_add_left _ _))
        have hζim : f^[e (ψ (χ i))] ζ ∈ f^[e (ψ (χ i))] '' O :=
          Set.mem_image_of_mem _ hζO
        have hxim : f^[e (ψ (χ i))] x ∈ f^[e (ψ (χ i))] '' O :=
          Set.mem_image_of_mem _ hx
        have hpair := hconf (e (ψ (χ i))) _ _ hζim hxim
        calc dist ((fun _ => q) x) (f^[e (ψ (χ i))] x)
            ≤ dist q (f^[e (ψ (χ i))] ζ) +
              dist (f^[e (ψ (χ i))] ζ) (f^[e (ψ (χ i))] x) := dist_triangle _ _ _
          _ ≤ ε/4 + 4 * Metric.diam (T (n + e (ψ (χ i)))) := by
              rw [dist_comm q _]
              exact add_le_add (le_of_lt hi1) hpair
          _ ≤ ε/4 + 4 * (ε/16) := by linarith
          _ < ε := by linarith
      refine ⟨fun i => ψ (χ i), hψ.comp hχ, fun _ => q,
        (htu.tendstoLocallyUniformlyOn).congr fun i y _ => ?_⟩
      exact congrFun (he (ψ (χ i))) y
  exact hζJ hζF

/-- **The hard branch of the dichotomy**: a wandering orbit cannot have
covering steps of fiber count at least two cofinally often. A multiple step
produces an essential loop around a Julia point
(`exists_essential_loop_of_multiple_step`). Either the forward readings of
that loop enclose Julia points at arbitrarily late times — impossible by
the collapse-and-confinement argument
(`false_of_fill_meets_julia_cofinally`) — or from some time on the fill of
the forward reading avoids the Julia set entirely, and then the reading is
null-homotopic in a simply connected neighborhood of its fill inside its
Fatou component; the null homotopy descends through the covering steps and
kills the original winding (`windingNumber_eq_zero_of_fill_avoids_julia`),
a contradiction. This is Baker's simple-connectivity argument, replacing
Sullivan's annulus-specific winding growth. -/
theorem not_cofinal_multiple_steps {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U)
    (hinf : ∀ n : ℕ, ∞ ∉ fcOrbit f U n)
    (hcrit : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f U n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0)
    (hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ k : ℕ, 2 ≤ k ∧
      ∀ w ∈ fcOrbit f U (n + 1),
        (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = k) :
    False := by
  classical
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  -- Seed: an essential loop about a Julia point at the target of one
  -- multiple step.
  obtain ⟨n, -, k, hk2, hk⟩ := hbad 0
  obtain ⟨γ, z₁, hγcl, hγmem, hz₁J, hz₁w⟩ :=
    exists_essential_loop_of_multiple_step hf hd hU n (hinf n) (hinf (n + 1))
      (hcrit n) hk2 hk
  -- Dichotomy on late-time enclosure of Julia points by the forward
  -- readings.
  by_cases hyes : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ ∃ Γ : C(unitInterval, ℂ),
      (∀ t : unitInterval, Γ t = chartFiniteMap (f^[m] ((γ t : ℂ̂)))) ∧
      ∃ w : ℂ̂, w ∈ JuliaSet f ∧
        w ∉ Set.range (fun t => ((Γ t : ℂ̂))) ∧
        w ∉ connectedComponentIn ((Set.range fun t => ((Γ t : ℂ̂)))ᶜ) ∞
  · exact false_of_fill_meets_julia_cofinally hf hd hU hW hinf hγcl hγmem hyes
  · -- From some time on, every Julia point lies in the `∞`-component of
    -- the trace complement, so the winding of the seed loop about its
    -- Julia point vanishes — contradiction.
    push Not at hyes
    obtain ⟨M, hM⟩ := hyes
    obtain ⟨Γ, hΓ⟩ := exists_pushed_curve hf hd hU hinf hγmem M
    -- Forward iterates of points of an orbit component land in the later
    -- orbit components (image structure of the component orbit).
    have hforward : ∀ (m : ℕ) (x : ℂ̂), x ∈ fcOrbit f U (n + 1) →
        f^[m] x ∈ fcOrbit f U (n + 1 + m) := by
      intro m
      induction m with
      | zero => intro x hx; simpa using hx
      | succ m ih =>
          intro x hx
          have h2 : f (f^[m] x) ∈ f '' fcOrbit f U (n + 1 + m) :=
            Set.mem_image_of_mem f (ih x hx)
          rw [fcOrbit_image_eq hf hd1 hU (n + 1 + m)] at h2
          rw [Function.iterate_succ_apply']
          exact h2
    have hfill : ∀ w : ℂ̂, w ∈ JuliaSet f →
        w ∈ connectedComponentIn ((Set.range fun t => ((Γ t : ℂ̂)))ᶜ) ∞ := by
      intro w hw
      have hnot := hM M le_rfl Γ hΓ w hw
      -- Julia points never lie on the trace: the trace consists of finite
      -- readings of Fatou points.
      have hwtr : w ∉ Set.range (fun t => ((Γ t : ℂ̂))) := by
        rintro ⟨t, rfl⟩
        -- the read value comes from a point of the `(n + 1 + M)`-th orbit
        -- component, which avoids `∞`, so the chart reading round-trips
        have hmem : f^[M] ((γ t : ℂ̂)) ∈ fcOrbit f U (n + 1 + M) :=
          hforward M _ (hγmem t)
        have hne : f^[M] ((γ t : ℂ̂)) ≠ ∞ := by
          intro h
          exact hinf (n + 1 + M) (h ▸ hmem)
        obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hne
        have htr : ((Γ t : ℂ̂)) = f^[M] ((γ t : ℂ̂)) := by
          rw [hΓ t, ← hv]
          rfl
        -- hence the trace point is a Fatou point, contradicting Julia
        -- membership
        have hwF : ((Γ t : ℂ̂)) ∈ FatouSet f := by
          rw [htr]
          exact (isFatouComponent_fcOrbit (n + 1 + M) hf hd1 hU).subset_fatouSet
            hmem
        exact Set.disjoint_left.mp (disjoint_fatouSet_juliaSet f) hwF hw
      exact hnot hwtr
    exact hz₁w (windingNumber_eq_zero_of_fill_avoids_julia hf hd hU hinf hcrit
      hγcl hγmem hΓ hfill z₁ hz₁J)

/-- **Eventual injectivity package** for a wandering component. A wandering
Fatou component of a rational map of degree at least two may be replaced by
a later component of its own orbit (`fcOrbit f U N`, again a wandering Fatou
component) on which

* every iterate of `f` is injective,
* no orbit component contains `∞`, and
* no orbit component contains a critical point of `f` (phrased through the
  finite-chart derivative at finite points — orbit components avoid `∞`, so
  this is the full critical-avoidance statement).

This is exactly the hypothesis package consumed by the spreading
construction (`Spreading.lean`) and the endgame
(`NoWanderingDomains.lean`). -/
theorem exists_wandering_injective_package {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 2 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U) :
    ∃ N : ℕ,
      IsFatouComponent f (fcOrbit f U N) ∧
      IsWandering f (fcOrbit f U N) ∧
      (∀ n : ℕ, Set.InjOn (f^[n]) (fcOrbit f U N)) ∧
      (∀ n : ℕ, ∞ ∉ fcOrbit f (fcOrbit f U N) n) ∧
      (∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f (fcOrbit f U N) n) →
        deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0) := by
  have hd1 : 1 ≤ degreeOfRational f := le_trans one_le_two hd
  obtain ⟨N₀, havoid⟩ := exists_avoidance_index hf hd hU hW
  have hV : IsFatouComponent f (fcOrbit f U N₀) := isFatouComponent_fcOrbit N₀ hf hd1 hU
  -- Re-indexing: the orbit of the relabeled component is the shifted orbit.
  have hreidx : ∀ n : ℕ, fcOrbit f (fcOrbit f U N₀) n = fcOrbit f U (N₀ + n) := by
    intro n
    exact (fcOrbit_add N₀ n hf hd1 hU).symm
  -- The relabeled component still wanders.
  have hWV : IsWandering f (fcOrbit f U N₀) := by
    rw [isWandering_iff]
    intro m n hmn
    rw [hreidx m, hreidx n]
    exact isWandering_iff.mp hW _ _ (by omega)
  -- Avoidance transferred to the relabeled orbit.
  have hinfV : ∀ n : ℕ, ∞ ∉ fcOrbit f (fcOrbit f U N₀) n := by
    intro n
    rw [hreidx n]
    exact (havoid n).1
  have hcritV : ∀ n : ℕ, ∀ z : ℂ, ((z : ℂ̂) ∈ fcOrbit f (fcOrbit f U N₀) n) →
      deriv (fun x : ℂ => chartFiniteMap (f ((x : ℂ̂)))) z ≠ 0 := by
    intro n z hz
    rw [hreidx n] at hz
    exact (havoid n).2 z hz
  -- Dichotomy: either the step fiber counts are eventually one, or steps of
  -- count at least two occur cofinally often.
  by_cases hgood : ∃ N₁ : ℕ, ∀ m : ℕ, N₁ ≤ m →
      ∀ w ∈ fcOrbit f (fcOrbit f U N₀) (m + 1),
        (f ⁻¹' {w} ∩ fcOrbit f (fcOrbit f U N₀) m).ncard = 1
  · obtain ⟨N₁, hone⟩ := hgood
    have hstep : ∀ m : ℕ, N₁ ≤ m →
        Set.InjOn f (fcOrbit f (fcOrbit f U N₀) m) := by
      intro m hm
      exact injOn_of_fiberCount_one hf hd1 hV m (hone m hm)
    have hiter : ∀ n : ℕ, Set.InjOn (f^[n]) (fcOrbit f (fcOrbit f U N₀) N₁) :=
      injOn_iterate_of_tail_injective hf hd1 hV N₁ hstep
    have hNeq : fcOrbit f U (N₀ + N₁) = fcOrbit f (fcOrbit f U N₀) N₁ :=
      fcOrbit_add N₀ N₁ hf hd1 hU
    have hreidx2 : ∀ n : ℕ,
        fcOrbit f (fcOrbit f U (N₀ + N₁)) n = fcOrbit f U (N₀ + N₁ + n) := by
      intro n
      exact (fcOrbit_add (N₀ + N₁) n hf hd1 hU).symm
    refine ⟨N₀ + N₁, isFatouComponent_fcOrbit (N₀ + N₁) hf hd1 hU, ?_, ?_, ?_, ?_⟩
    · rw [isWandering_iff]
      intro m n hmn
      rw [hreidx2 m, hreidx2 n]
      exact isWandering_iff.mp hW _ _ (by omega)
    · intro n
      rw [hNeq]
      exact hiter n
    · intro n
      rw [hreidx2 n, Nat.add_assoc]
      exact (havoid (N₁ + n)).1
    · intro n z hz
      rw [hreidx2 n, Nat.add_assoc] at hz
      exact (havoid (N₁ + n)).2 z hz
  · push Not at hgood
    have hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ k : ℕ, 2 ≤ k ∧
        ∀ w ∈ fcOrbit f (fcOrbit f U N₀) (n + 1),
          (f ⁻¹' {w} ∩ fcOrbit f (fcOrbit f U N₀) n).ncard = k := by
      intro N₁
      obtain ⟨m, hm, w, hw, hne⟩ := hgood N₁
      obtain ⟨k, hk1, hconst⟩ :=
        exists_fiberCount hf hd hV m (hinfV m) (hcritV m)
      have hkne : k ≠ 1 := by
        intro hk
        exact hne ((hconst w hw).trans hk)
      exact ⟨m, hm, k, by omega, hconst⟩
    exact (not_cofinal_multiple_steps hf hd hV hWV hinfV hcritV hbad).elim

end RiemannDynamics
