/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Dynamics.FatouComponents.Periodic
import RiemannDynamics.Dynamics.JuliaFatou.RepellingDensity

/-!
# Eventual injectivity on a wandering component (interface)

The normalization wall of the No Wandering Domains theorem: a wandering Fatou
component may be relabeled along its forward orbit so that, from some time
on, every iterate is injective on the component and the orbit components
avoid `∞` and the critical points of the map.

This file states the *interface only*. The two soft normalizations are
finiteness pigeonholing: the orbit components are pairwise disjoint, `∞`
lies in at most one of them, and the finitely many critical points of a
rational map meet only finitely many of them. The injectivity clause is the
hard dichotomy: each component step `f : Uₙ → Uₙ₊₁` is proper and eventually
critical-point-free, hence a covering of some degree `≥ 1`; if infinitely
many steps had degree `≥ 2`, the moduli of a suitable separating curve
family would grow without bound through the orbit, producing essential
annuli of arbitrarily large modulus separating the (uniformly perfect) Julia
set — a contradiction. The internal development of this dichotomy is a later
sub-architecture; downstream files consume only the statement below.

The file also hosts the small shared lemma that the frontier of a Fatou
component lies in the Julia set, consumed by several parts of the endgame.
-/

open Function OnePoint

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
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (hW : IsWandering f U) :
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
    show (if h : (fcOrbit f U m ∩ B).Nonempty then h.choose else ∞)
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
  sorry

/-- A component step with constant fiber count one is injective on the
source component. -/
theorem injOn_of_fiberCount_one {f : ℂ̂ → ℂ̂}
    (hf : IsRational f) (hd : 1 ≤ degreeOfRational f)
    {U : Set ℂ̂} (hU : IsFatouComponent f U) (n : ℕ)
    (h1 : ∀ w ∈ fcOrbit f U (n + 1),
      (f ⁻¹' {w} ∩ fcOrbit f U n).ncard = 1) :
    Set.InjOn f (fcOrbit f U n) := by
  sorry

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

/-- **The hard branch of the dichotomy**: a wandering orbit cannot have
covering steps of fiber count at least two cofinally often. Each such step
multiplies the modulus of a separating curve family of the (multiply
connected) target component by the fiber count, and homeomorphic steps
preserve it, so cofinally many multiple steps drive the modulus of an
essential separating configuration in the Fatou set beyond every bound —
producing essential annuli of arbitrarily large modulus separating the
Julia set, which contradicts the uniform-perfectness-type bound obtained
from the definite-size Montel expansion at Julia points. -/
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
  sorry

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
