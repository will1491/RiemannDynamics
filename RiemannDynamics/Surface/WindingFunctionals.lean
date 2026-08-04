/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.GenusSurface.Manifold
import RiemannDynamics.Analysis.Winding.Basic

/-!
# Winding functionals of the genus surface

A nonvanishing continuous complex function on a space induces a `ℤ`-valued functional on
homotopy classes of loops, the winding number about `0` of the image loop (`loopWinding`),
additive under concatenation (`loopWinding_trans`). A loop of nonzero winding forces
infinitely many loop classes at the basepoint
(`infinite_loopClasses_of_loopWinding_ne_zero`).

On the genus-`g` surface, `2 ≤ g`, the boundary arcs of the `4g`-gon descend to loops at
the vertex class (`edgeLoop`), and three nonvanishing functionals built from integer side
weights compose with the first three edge-pair loops to the identity matrix of windings
(`exists_winding_functionals`); consequently the loop classes at the vertex surject onto
`ℤ³` by a concatenation-additive map (`exists_pi1_surjection_zpow3`).
-/

open scoped unitInterval

namespace RiemannDynamics

/-! ## The winding functional on loop classes -/

variable {M : Type*} [TopologicalSpace M]

/-- The winding number about `0` of the image of a loop under a nonvanishing continuous
function, descended to homotopy classes of loops. -/
noncomputable def loopWinding (x₀ : M) {w : M → ℂ} (hw : Continuous w)
    (hw0 : ∀ x, w x ≠ 0) : Path.Homotopic.Quotient x₀ x₀ → ℤ :=
  Quotient.lift (fun p : Path x₀ x₀ => windingNumber ((p.map hw).toContinuousMap) 0)
    (by
      intro p q hpq
      obtain ⟨F⟩ := hpq
      have hcl : ((p.map hw).toContinuousMap : C(I, ℂ)) 0
          = ((p.map hw).toContinuousMap : C(I, ℂ)) 1 := by
        simp
      refine windingNumber_eq_of_homotopicRel hcl (F.map ⟨w, hw⟩) ?_
      intro t s
      have hval : (F.map ⟨w, hw⟩) (t, s) = w (F (t, s)) := rfl
      rw [hval]
      exact hw0 _)

/-- The winding functional computed on a representative loop. -/
theorem loopWinding_mk (x₀ : M) {w : M → ℂ} (hw : Continuous w)
    (hw0 : ∀ x, w x ≠ 0) (p : Path x₀ x₀) :
    loopWinding x₀ hw hw0 ⟦p⟧ = windingNumber ((p.map hw).toContinuousMap) 0 := rfl

/-- The winding functional is additive under concatenation of loop classes. -/
theorem loopWinding_trans (x₀ : M) {w : M → ℂ} (hw : Continuous w)
    (hw0 : ∀ x, w x ≠ 0) (γ δ : Path.Homotopic.Quotient x₀ x₀) :
    loopWinding x₀ hw hw0 (γ.trans δ)
      = loopWinding x₀ hw hw0 γ + loopWinding x₀ hw hw0 δ := by
  refine Quotient.inductionOn₂ γ δ fun p q => ?_
  have h1 : (Path.Homotopic.Quotient.trans ⟦p⟧ ⟦q⟧ :
      Path.Homotopic.Quotient x₀ x₀) = ⟦p.trans q⟧ := rfl
  rw [h1, loopWinding_mk, loopWinding_mk, loopWinding_mk, Path.map_trans]
  exact windingNumber_trans (p.map hw) (q.map hw)
    (fun t => by simp only [Path.map_coe, Function.comp_apply]; exact hw0 _)
    (fun t => by simp only [Path.map_coe, Function.comp_apply]; exact hw0 _)

/-- A single loop with nonvanishing winding functional forces infinitely many loop
classes at the basepoint. -/
theorem infinite_loopClasses_of_loopWinding_ne_zero (x₀ : M) {w : M → ℂ}
    (hw : Continuous w) (hw0 : ∀ x, w x ≠ 0) (γ₀ : Path.Homotopic.Quotient x₀ x₀)
    (hγ₀ : loopWinding x₀ hw hw0 γ₀ ≠ 0) :
    Infinite (Path.Homotopic.Quotient x₀ x₀) := by
  set d := loopWinding x₀ hw hw0 γ₀ with hd
  let pow : ℕ → Path.Homotopic.Quotient x₀ x₀ := fun n =>
    Nat.recAux γ₀ (fun _ ih => ih.trans γ₀) n
  have hpow : ∀ n : ℕ, loopWinding x₀ hw hw0 (pow n) = ((n : ℤ) + 1) * d := by
    intro n
    induction n with
    | zero => simpa [pow] using hd.symm
    | succ k ih =>
        have hstep : pow (k + 1) = (pow k).trans γ₀ := rfl
        rw [hstep, loopWinding_trans, ih]
        push_cast
        ring
  have hinj : Function.Injective pow := by
    intro m n hmn
    have hm := hpow m
    rw [hmn, hpow n] at hm
    have hmn' : ((m : ℤ) + 1) = ((n : ℤ) + 1) := mul_right_cancel₀ hγ₀ hm.symm
    omega
  exact Infinite.of_injective pow hinj

/-! ## Edge loops of the `4g`-gon -/

/-- Arc points lie on the unit circle. -/
theorem norm_arcPoint (g : ℕ) (k : ℤ) (t : ℝ) : ‖arcPoint g k t‖ = 1 := by
  unfold arcPoint
  rw [show (Real.pi * ((k : ℂ) + (t : ℂ)) * Complex.I / (2 * (g : ℂ)))
      = ((Real.pi * ((k : ℝ) + t) / (2 * (g : ℝ)) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A `genusRel`-invariant function descends to the surface. -/
noncomputable def descendToGenus {g : ℕ} [NeZero g] {α : Type*} (W : ClosedDisc → α)
    (hW : ∀ z w : ClosedDisc, genusRel g z w → W z = W w) : GenusSurface g → α :=
  Quotient.lift W hW

/-- A `genusRel`-invariant continuous function descends continuously to the surface. -/
theorem continuous_descendToGenus {g : ℕ} [NeZero g] {α : Type*} [TopologicalSpace α]
    {W : ClosedDisc → α} (hWc : Continuous W)
    (hW : ∀ z w : ClosedDisc, genusRel g z w → W z = W w) :
    Continuous (descendToGenus W hW) :=
  continuous_quot_lift _ hWc

/-- **The `k`-th edge loop of the `4g`-gon**, as a loop in the genus surface based at
the vertex class: all vertices are identified, so each boundary arc closes up. -/
noncomputable def edgeLoop (g : ℕ) [NeZero g] (k : ℤ) :
    Path (vertexPoint g) (vertexPoint g) where
  toFun t := Quotient.mk (genusSetoid g)
    ⟨arcPoint g k t, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_arcPoint]⟩
  continuous_toFun := by
    refine continuous_quot_mk.comp (Continuous.subtype_mk ?_ _)
    unfold arcPoint
    fun_prop
  source' := by
    refine Quotient.sound (Or.inr (Or.inr ⟨⟨k, ?_⟩, ⟨0, rfl⟩⟩))
    change arcPoint g k ((0 : I) : ℝ) = polyVertex g k
    rw [Set.Icc.coe_zero, arcPoint_zero]
  target' := by
    refine Quotient.sound (Or.inr (Or.inr ⟨⟨k + 1, ?_⟩, ⟨0, rfl⟩⟩))
    change arcPoint g k ((1 : I) : ℝ) = polyVertex g (k + 1)
    rw [Set.Icc.coe_one, arcPoint_one]

/-! ## The winding functionals of the `4g`-gon -/

/-- **Winding functionals of the `4g`-gon**: for `2 ≤ g`, three nonvanishing continuous
complex functionals on the genus surface whose windings about `0` along the first three
edge-pair loops form the identity matrix. Edge-pair representatives: sides `0, 1, 4`
(pairs `{k, k+2}`, `k % 4 ∈ {0,1}`; `4g ≥ 8` sides for `g ≥ 2`). -/
theorem exists_winding_functionals (g : ℕ) [NeZero g] (hg : 2 ≤ g) :
    ∃ w : Fin 3 → GenusSurface g → ℂ, ∃ hw : ∀ j, Continuous (w j),
      ∃ hw0 : ∀ j x, w j x ≠ 0,
      ∀ j j' : Fin 3,
        loopWinding (vertexPoint g) (hw j) (fun x => hw0 j x) ⟦edgeLoop g (![0, 1, 4] j')⟧
          = if j = j' then 1 else 0 := by
  -- numeric groundwork
  have hg2 : (2 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have h2g : (0 : ℝ) < 2 * (g : ℝ) := by linarith
  have hgne : (g : ℝ) ≠ 0 := by positivity
  have h2gne : 2 * (g : ℝ) ≠ 0 := ne_of_gt h2g
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  -- the boundary-phase data: trapezoid bump, rotation constants, phase, functional
  set bump : ℤ → ℝ → ℝ :=
    fun s x => max 0 (min (min (x - (s : ℝ)) 1) ((s : ℝ) + 3 - x)) with hbumpdef
  have hbapp : ∀ (s : ℤ) (x : ℝ),
      bump s x = max 0 (min (min (x - (s : ℝ)) 1) ((s : ℝ) + 3 - x)) := fun s x => rfl
  set cS : ℤ → ℂ := fun s =>
    Complex.exp (-((Real.pi * ((s : ℝ) + 3 / 2) / (2 * (g : ℝ)) : ℝ) : ℂ) * Complex.I)
    with hcSdef
  have hcapp : ∀ s : ℤ, cS s =
      Complex.exp (-((Real.pi * ((s : ℝ) + 3 / 2) / (2 * (g : ℝ)) : ℝ) : ℂ) * Complex.I) :=
    fun s => rfl
  set Fp : ℤ → ℂ → ℝ := fun s z =>
    bump s (2 * (g : ℝ) / Real.pi * (z * cS s).arg + ((s : ℝ) + 3 / 2)) with hFpdef
  have hFapp : ∀ (s : ℤ) (z : ℂ),
      Fp s z = bump s (2 * (g : ℝ) / Real.pi * (z * cS s).arg + ((s : ℝ) + 3 / 2)) :=
    fun s z => rfl
  set Wp : ℤ → ℂ → ℂ := fun s z =>
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((‖z‖ * Fp s z : ℝ) : ℂ)) with hWpdef
  have hWapp : ∀ (s : ℤ) (z : ℂ),
      Wp s z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((‖z‖ * Fp s z : ℝ) : ℂ)) :=
    fun s z => rfl
  -- the phase takes values in [0, 1]
  have hFbd : ∀ (s : ℤ) (z : ℂ), 0 ≤ Fp s z ∧ Fp s z ≤ 1 := by
    intro s z
    rw [hFapp, hbapp]
    exact ⟨le_max_left 0 _,
      max_le zero_le_one ((min_le_left _ _).trans (min_le_right _ _))⟩
  -- VALUES: the phase along the boundary arcs
  have hFarc : ∀ (s k : ℤ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      Fp s (arcPoint g k t) =
        if (k - s) % (4 * (g : ℤ)) = 0 then t
        else if (k - s) % (4 * (g : ℤ)) = 1 then 1
        else if (k - s) % (4 * (g : ℤ)) = 2 then 1 - t
        else 0 := by
    intro s k t ht0 ht1
    set r : ℤ := (k - s) % (4 * (g : ℤ)) with hrdef
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
    have hr4 : r < 4 * (g : ℤ) := Int.emod_lt_of_pos _ (by omega)
    have hrR0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hrR4 : (r : ℝ) ≤ 4 * (g : ℝ) - 1 := by
      exact_mod_cast (by omega : r ≤ 4 * (g : ℤ) - 1)
    have harc : arcPoint g k t = arcPoint g (s + r) t := by
      rw [arcPoint_eq_iff]
      refine ⟨(k - s) / (4 * (g : ℤ)), ?_⟩
      have h := Int.mul_ediv_add_emod (k - s) (4 * (g : ℤ))
      rw [← hrdef] at h
      have hR : 4 * (g : ℝ) * (((k - s) / (4 * (g : ℤ)) : ℤ) : ℝ) + (r : ℝ)
          = (k : ℝ) - (s : ℝ) := by exact_mod_cast h
      push_cast
      linarith
    rw [harc, hFapp]
    set y : ℝ := Real.pi * ((r : ℝ) + t - 3 / 2) / (2 * (g : ℝ)) with hydef
    have hprod : arcPoint g (s + r) t * cS s = Complex.exp ((y : ℂ) * Complex.I) := by
      rw [hcapp s]
      unfold arcPoint
      rw [← Complex.exp_add]
      congr 1
      rw [hydef]
      push_cast
      field_simp
      ring
    rw [hprod]
    have hbeval : ∀ u : ℝ, bump s ((s : ℝ) + u) = max 0 (min (min u 1) (3 - u)) := by
      intro u
      rw [hbapp, show (s : ℝ) + u - (s : ℝ) = u by ring,
        show (s : ℝ) + 3 - ((s : ℝ) + u) = 3 - u by ring]
    rcases le_or_gt ((r : ℝ) + t - 3 / 2) (2 * (g : ℝ)) with hA | hB
    · -- principal branch of the argument
      have hmem : y ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        constructor
        · rw [hydef, lt_div_iff₀ h2g]
          nlinarith [mul_pos hπ (show (0 : ℝ) < (r : ℝ) + t - 3 / 2 + 2 * (g : ℝ) by linarith)]
        · have hy : y ≤ Real.pi := by
            rw [hydef, div_le_iff₀ h2g]
            nlinarith [mul_nonneg hπ.le
              (show (0 : ℝ) ≤ 2 * (g : ℝ) - ((r : ℝ) + t - 3 / 2) by linarith)]
          linarith
      have hyx : 2 * (g : ℝ) / Real.pi * y = (r : ℝ) + t - 3 / 2 := by
        rw [hydef]
        field_simp
      rw [Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).mpr hmem, hyx,
        show (r : ℝ) + t - 3 / 2 + ((s : ℝ) + 3 / 2) = (s : ℝ) + ((r : ℝ) + t) by ring,
        hbeval ((r : ℝ) + t)]
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ 3 ≤ r) with hc | hc | hc | hc
      · rw [hc, if_pos rfl, show ((0 : ℤ) : ℝ) + t = t by push_cast; ring,
          min_eq_left ht1, min_eq_left (by linarith : t ≤ 3 - t), max_eq_right ht0]
      · rw [hc, if_neg (by norm_num : ¬(1 : ℤ) = 0), if_pos rfl,
          show ((1 : ℤ) : ℝ) + t = 1 + t by push_cast; ring,
          min_eq_right (by linarith : (1 : ℝ) ≤ 1 + t),
          show (3 : ℝ) - (1 + t) = 2 - t by ring,
          min_eq_left (by linarith : (1 : ℝ) ≤ 2 - t), max_eq_right zero_le_one]
      · rw [hc, if_neg (by norm_num : ¬(2 : ℤ) = 0), if_neg (by norm_num : ¬(2 : ℤ) = 1),
          if_pos rfl, show ((2 : ℤ) : ℝ) + t = 2 + t by push_cast; ring,
          min_eq_right (by linarith : (1 : ℝ) ≤ 2 + t),
          show (3 : ℝ) - (2 + t) = 1 - t by ring,
          min_eq_right (by linarith : 1 - t ≤ 1),
          max_eq_right (by linarith : (0 : ℝ) ≤ 1 - t)]
      · have hr3R : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hc
        rw [if_neg (by omega : ¬r = 0), if_neg (by omega : ¬r = 1), if_neg (by omega : ¬r = 2),
          max_eq_left ((min_le_right _ _).trans (by linarith : 3 - ((r : ℝ) + t) ≤ 0))]
    · -- wrapped branch of the argument
      have h4r : (4 : ℤ) < r := by
        have h4R : (4 : ℝ) < (r : ℝ) := by linarith
        exact_mod_cast h4R
      have hexp2 : Complex.exp ((y : ℂ) * Complex.I)
          = Complex.exp (((y - 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.exp_eq_exp_iff_exists_int]
        exact ⟨1, by push_cast; ring⟩
      have hmem : y - 2 * Real.pi ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        constructor
        · have hylo : Real.pi < y := by
            rw [hydef, lt_div_iff₀ h2g]
            nlinarith [mul_pos hπ
              (show (0 : ℝ) < (r : ℝ) + t - 3 / 2 - 2 * (g : ℝ) by linarith)]
          linarith
        · have hyhi : y ≤ 3 * Real.pi := by
            rw [hydef, div_le_iff₀ h2g]
            nlinarith [mul_nonneg hπ.le
              (show (0 : ℝ) ≤ 6 * (g : ℝ) - ((r : ℝ) + t - 3 / 2) by linarith)]
          linarith
      have hyx : 2 * (g : ℝ) / Real.pi * (y - 2 * Real.pi)
          = (r : ℝ) + t - 3 / 2 - 4 * (g : ℝ) := by
        rw [hydef]
        field_simp
        ring
      rw [hexp2, Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).mpr hmem, hyx,
        show (r : ℝ) + t - 3 / 2 - 4 * (g : ℝ) + ((s : ℝ) + 3 / 2)
          = (s : ℝ) + ((r : ℝ) + t - 4 * (g : ℝ)) by ring,
        hbeval ((r : ℝ) + t - 4 * (g : ℝ))]
      have hu0 : (r : ℝ) + t - 4 * (g : ℝ) ≤ 0 := by linarith
      rw [if_neg (by omega : ¬r = 0), if_neg (by omega : ¬r = 1), if_neg (by omega : ¬r = 2),
        max_eq_left ((min_le_left _ _).trans ((min_le_left _ _).trans hu0))]
  -- boundary values of the functional
  have hWarc : ∀ (s k : ℤ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      Wp s (arcPoint g k t) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((if (k - s) % (4 * (g : ℤ)) = 0 then t
          else if (k - s) % (4 * (g : ℤ)) = 1 then 1
          else if (k - s) % (4 * (g : ℤ)) = 2 then 1 - t
          else 0 : ℝ) : ℂ)) := by
    intro s k t ht0 ht1
    rw [hWapp, norm_arcPoint, one_mul, hFarc s k t ht0 ht1]
  -- side-pairing invariance
  have hpair : ∀ s : ℤ, s = 0 ∨ s = 1 ∨ s = 4 → ∀ k : ℤ, k % 4 = 0 ∨ k % 4 = 1 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Wp s (arcPoint g k t) = Wp s (arcPoint g (k + 2) (1 - t)) := by
    intro s hs k hk4 t ht0 ht1
    rw [hWarc s k t ht0 ht1, hWarc s (k + 2) (1 - t) (by linarith) (by linarith)]
    set r : ℤ := (k - s) % (4 * (g : ℤ)) with hrdef
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
    have hr4 : r < 4 * (g : ℤ) := Int.emod_lt_of_pos _ (by omega)
    obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, k - s = 4 * Q + r := by
      refine ⟨(g : ℤ) * ((k - s) / (4 * (g : ℤ))), ?_⟩
      have h := Int.mul_ediv_add_emod (k - s) (4 * (g : ℤ))
      rw [← hrdef] at h
      linear_combination -h
    have hr2eq : (k + 2 - s) % (4 * (g : ℤ)) = (r + 2) % (4 * (g : ℤ)) := by
      rw [show k + 2 - s = k - s + 2 by ring, Int.add_emod, ← hrdef,
        Int.emod_eq_of_lt (by norm_num : (0 : ℤ) ≤ 2) (by omega : (2 : ℤ) < 4 * (g : ℤ))]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ (3 ≤ r ∧ r + 2 < 4 * (g : ℤ))
        ∨ r = 4 * (g : ℤ) - 2 ∨ r = 4 * (g : ℤ) - 1) with hc | hc | hc | ⟨hc3, hcu⟩ | hc | hc
    · -- r = 0 : t versus 1 - (1 - t)
      have h2 : (k + 2 - s) % (4 * (g : ℤ)) = 2 := by
        rw [hr2eq, hc, show (0 : ℤ) + 2 = 2 by norm_num]
        exact Int.emod_eq_of_lt (by norm_num) (by omega)
      rw [hc, h2]
      norm_num
    · -- r = 1 : 1 versus 0
      have h2 : (k + 2 - s) % (4 * (g : ℤ)) = 3 := by
        rw [hr2eq, hc, show (1 : ℤ) + 2 = 3 by norm_num]
        exact Int.emod_eq_of_lt (by norm_num) (by omega)
      rw [hc, h2, if_neg (by norm_num : ¬(1 : ℤ) = 0), if_pos rfl,
        if_neg (by norm_num : ¬(3 : ℤ) = 0), if_neg (by norm_num : ¬(3 : ℤ) = 1),
        if_neg (by norm_num : ¬(3 : ℤ) = 2), Complex.ofReal_one, mul_one,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      exact Complex.exp_two_pi_mul_I
    · -- r = 2 : impossible for a source side
      exfalso
      omega
    · -- middle range : 0 versus 0
      have h2 : (k + 2 - s) % (4 * (g : ℤ)) = r + 2 :=
        hr2eq.trans (Int.emod_eq_of_lt (by omega) hcu)
      rw [h2, if_neg (by omega : ¬r = 0), if_neg (by omega : ¬r = 1),
        if_neg (by omega : ¬r = 2), if_neg (by omega : ¬r + 2 = 0),
        if_neg (by omega : ¬r + 2 = 1), if_neg (by omega : ¬r + 2 = 2)]
    · -- r = 4g - 2 : impossible for a source side
      exfalso
      omega
    · -- r = 4g - 1 : 0 versus 1
      have h2 : (k + 2 - s) % (4 * (g : ℤ)) = 1 := by
        rw [hr2eq, hc, show 4 * (g : ℤ) - 1 + 2 = 1 + 4 * (g : ℤ) * 1 by ring,
          Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by norm_num) (by omega)
      rw [hc, h2, if_neg (by omega : ¬4 * (g : ℤ) - 1 = 0),
        if_neg (by omega : ¬4 * (g : ℤ) - 1 = 1), if_neg (by omega : ¬4 * (g : ℤ) - 1 = 2),
        if_neg (by norm_num : ¬(1 : ℤ) = 0), if_pos rfl, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, Complex.ofReal_one, mul_one]
      exact Complex.exp_two_pi_mul_I.symm
  -- all vertices carry the value 1
  have hvert : ∀ s m : ℤ, Wp s (polyVertex g m) = 1 := by
    intro s m
    rw [← arcPoint_zero g m, hWarc s m 0 le_rfl zero_le_one]
    split_ifs
    · rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    · rw [Complex.ofReal_one, mul_one]
      exact Complex.exp_two_pi_mul_I
    · rw [show (1 : ℝ) - 0 = 1 by norm_num, Complex.ofReal_one, mul_one]
      exact Complex.exp_two_pi_mul_I
    · rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  -- full gluing invariance
  have hinv : ∀ s : ℤ, s = 0 ∨ s = 1 ∨ s = 4 →
      ∀ z w : ClosedDisc, genusRel g z w → Wp s z.1 = Wp s w.1 := by
    intro s hs z w hzw
    have hzw' : z = w ∨ (∃ k : ℤ, (k % 4 = 0 ∨ k % 4 = 1) ∧
        ((z.1, w.1) ∈ pairGraph g k ∨ (w.1, z.1) ∈ pairGraph g k))
        ∨ (IsPolyVertex g z.1 ∧ IsPolyVertex g w.1) := hzw
    rcases hzw' with heq | ⟨k, hk4, hpg | hpg⟩ | ⟨⟨m, hm⟩, ⟨m', hm'⟩⟩
    · rw [heq]
    · obtain ⟨t, -, ht⟩ := hpg
      have h1 : arcPoint g k (t : ℝ) = z.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k + 2) (1 - (t : ℝ)) = w.1 := congrArg Prod.snd ht
      rw [← h1, ← h2]
      exact hpair s hs k hk4 (t : ℝ) t.2.1 t.2.2
    · obtain ⟨t, -, ht⟩ := hpg
      have h1 : arcPoint g k (t : ℝ) = w.1 := congrArg Prod.fst ht
      have h2 : arcPoint g (k + 2) (1 - (t : ℝ)) = z.1 := congrArg Prod.snd ht
      rw [← h1, ← h2]
      exact (hpair s hs k hk4 (t : ℝ) t.2.1 t.2.2).symm
    · rw [hm, hm', hvert s m, hvert s m']
  -- continuity of the radially damped functional
  have hbc : ∀ s : ℤ, Continuous fun x : ℝ => bump s x := by
    intro s
    change Continuous fun x : ℝ => max 0 (min (min (x - (s : ℝ)) 1) ((s : ℝ) + 3 - x))
    exact continuous_const.max (((continuous_id.sub continuous_const).min
      continuous_const).min (continuous_const.sub continuous_id))
  have hGcont : ∀ s : ℤ, Continuous fun z : ℂ => ‖z‖ * Fp s z := by
    intro s
    rw [continuous_iff_continuousAt]
    intro z₀
    rcases eq_or_ne z₀ 0 with rfl | hz0
    · -- radial damping forces continuity at the center
      have h00 : (fun z : ℂ => ‖z‖ * Fp s z) 0 = 0 := by
        simp only [norm_zero, zero_mul]
      have hb : ∀ z : ℂ, ‖‖z‖ * Fp s z‖ ≤ ‖z‖ := by
        intro z
        rw [Real.norm_eq_abs, abs_mul, abs_norm]
        have h01 := hFbd s z
        have habs : |Fp s z| ≤ 1 := abs_le.mpr ⟨by linarith [h01.1], h01.2⟩
        calc ‖z‖ * |Fp s z| ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left habs (norm_nonneg z)
          _ = ‖z‖ := mul_one _
      unfold ContinuousAt
      rw [h00]
      exact squeeze_zero_norm hb tendsto_norm_zero
    · by_cases hslit : z₀ * cS s ∈ Complex.slitPlane
      · -- away from the cut: composition of continuous maps
        have h1 : ContinuousAt (fun z : ℂ => z * cS s) z₀ :=
          (continuous_mul_const (cS s)).continuousAt
        have h2 : ContinuousAt Complex.arg (z₀ * cS s) := Complex.continuousAt_arg hslit
        have h3 : ContinuousAt (fun z : ℂ => (z * cS s).arg) z₀ := by
          change ContinuousAt (Complex.arg ∘ fun z : ℂ => z * cS s) z₀
          exact ContinuousAt.comp (f := fun z : ℂ => z * cS s) (x := z₀) h2 h1
        have h4 : ContinuousAt
            (fun z : ℂ => 2 * (g : ℝ) / Real.pi * (z * cS s).arg + ((s : ℝ) + 3 / 2)) z₀ :=
          (h3.const_mul _).add continuousAt_const
        have h5 : ContinuousAt (fun z : ℂ => Fp s z) z₀ := by
          change ContinuousAt (fun z : ℂ =>
            bump s (2 * (g : ℝ) / Real.pi * (z * cS s).arg + ((s : ℝ) + 3 / 2))) z₀
          exact (hbc s).continuousAt.comp h4
        exact continuous_norm.continuousAt.mul h5
      · -- on the cut: the phase vanishes on a neighborhood
        have hcne : cS s ≠ 0 := by
          rw [hcapp s]
          exact Complex.exp_ne_zero _
        have hzcne : z₀ * cS s ≠ 0 := mul_ne_zero hz0 hcne
        have hre : (z₀ * cS s).re < 0 := by
          rw [Complex.mem_slitPlane_iff] at hslit
          have hre_le : (z₀ * cS s).re ≤ 0 := not_lt.mp fun hc => hslit (Or.inl hc)
          have him : (z₀ * cS s).im = 0 := by
            by_contra hc
            exact hslit (Or.inr hc)
          rcases lt_or_eq_of_le hre_le with h | h
          · exact h
          · exact absurd (Complex.ext (by rw [Complex.zero_re]; exact h)
              (by rw [Complex.zero_im]; exact him)) hzcne
        have hU : IsOpen {z : ℂ | (z * cS s).re < 0} :=
          isOpen_lt (Complex.continuous_re.comp (continuous_mul_const (cS s))) continuous_const
        have hvan : Set.EqOn (fun z : ℂ => ‖z‖ * Fp s z) (fun _ => (0 : ℝ))
            {z : ℂ | (z * cS s).re < 0} := by
          intro z hz
          have hz' : (z * cS s).re < 0 := hz
          have hzc : z * cS s ≠ 0 := by
            intro h0
            rw [h0, Complex.zero_re] at hz'
            exact lt_irrefl 0 hz'
          have hbig : Real.pi / 2 ≤ |(z * cS s).arg| := by
            by_contra hlt
            rcases Complex.abs_arg_lt_pi_div_two_iff.mp (not_le.mp hlt) with hpos | h0
            · linarith
            · exact hzc h0
          have hF0 : Fp s z = 0 := by
            rw [hFapp, hbapp]
            rcases le_abs.mp hbig with hup | hdown
            · -- the argument is at least π/2 : the trapezoid sits right of its support
              have hmul : (g : ℝ) ≤ 2 * (g : ℝ) / Real.pi * (z * cS s).arg := by
                rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
                nlinarith [mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) by linarith)
                  (show (0 : ℝ) ≤ 2 * (z * cS s).arg - Real.pi by linarith)]
              refine max_eq_left ((min_le_right _ _).trans ?_)
              linarith
            · -- the argument is at most -π/2 : the trapezoid sits left of its support
              have hmul : 2 * (g : ℝ) / Real.pi * (z * cS s).arg ≤ -(g : ℝ) := by
                rw [div_mul_eq_mul_div, div_le_iff₀ hπ]
                nlinarith [mul_nonneg (show (0 : ℝ) ≤ (g : ℝ) by linarith)
                  (show (0 : ℝ) ≤ -Real.pi - 2 * (z * cS s).arg by linarith)]
              refine max_eq_left ((min_le_left _ _).trans ((min_le_left _ _).trans ?_))
              linarith
          change ‖z‖ * Fp s z = 0
          rw [hF0, mul_zero]
        exact Filter.EventuallyEq.continuousAt
          (Filter.eventuallyEq_of_mem (hU.mem_nhds hre) hvan)
  have hWcont : ∀ s : ℤ, Continuous (Wp s) := by
    intro s
    change Continuous fun z : ℂ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((‖z‖ * Fp s z : ℝ) : ℂ))
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hGcont s)))
  have hWne : ∀ (s : ℤ) (z : ℂ), Wp s z ≠ 0 := by
    intro s z
    rw [hWapp]
    exact Complex.exp_ne_zero _
  -- descent to the genus surface
  have hj3 : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  have hSmem : ∀ j : Fin 3, (![0, 1, 4] : Fin 3 → ℤ) j = 0 ∨ (![0, 1, 4] : Fin 3 → ℤ) j = 1
      ∨ (![0, 1, 4] : Fin 3 → ℤ) j = 4 := by
    intro j
    rcases hj3 j with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  set wD : Fin 3 → GenusSurface g → ℂ := fun j =>
    descendToGenus (fun z : ClosedDisc => Wp (![0, 1, 4] j) z.1)
      (fun z w' h => hinv (![0, 1, 4] j) (hSmem j) z w' h) with hwDdef
  have hwDcont : ∀ j, Continuous (wD j) := fun j =>
    continuous_descendToGenus ((hWcont _).comp continuous_subtype_val) _
  have hwDne : ∀ (j : Fin 3) (x : GenusSurface g), wD j x ≠ 0 := fun j x =>
    Quotient.inductionOn x fun z => hWne _ z.1
  -- the winding computation along an edge loop with affine phase
  have hwind : ∀ (j : Fin 3) (k : ℤ) (a : ℝ) (n : ℤ),
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → Fp (![0, 1, 4] j) (arcPoint g k t) = a + (n : ℝ) * t) →
      loopWinding (vertexPoint g) (hwDcont j) (fun x => hwDne j x) ⟦edgeLoop g k⟧ = n := by
    intro j k a n haff
    rw [loopWinding_mk]
    have hγ : ∀ t : I, ((edgeLoop g k).map (hwDcont j)).toContinuousMap t
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a + (n : ℝ) * (t : ℝ) : ℝ) : ℂ)) := by
      intro t
      have h2 : ((edgeLoop g k).map (hwDcont j)).toContinuousMap t
          = Wp (![0, 1, 4] j) (arcPoint g k (t : ℝ)) := rfl
      rw [h2, hWapp, norm_arcPoint, one_mul, haff (t : ℝ) t.2.1 t.2.2]
    have hcl : ((edgeLoop g k).map (hwDcont j)).toContinuousMap 0
        = ((edgeLoop g k).map (hwDcont j)).toContinuousMap 1 := by
      rw [hγ 0, hγ 1, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, add_zero, mul_one,
        show ((a + (n : ℝ) : ℝ) : ℂ) = (a : ℂ) + (n : ℂ) by push_cast; ring, mul_add,
        Complex.exp_add,
        show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
          = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hq : ∀ t : I, ((edgeLoop g k).map (hwDcont j)).toContinuousMap t ≠ (0 : ℂ) := by
      intro t
      rw [hγ t]
      exact Complex.exp_ne_zero _
    have hLc : Continuous fun t : I =>
        2 * (Real.pi : ℂ) * Complex.I * ((a + (n : ℝ) * (t : ℝ) : ℝ) : ℂ) := by
      fun_prop
    set L : C(I, ℂ) := ⟨fun t : I =>
      2 * (Real.pi : ℂ) * Complex.I * ((a + (n : ℝ) * (t : ℝ) : ℝ) : ℂ), hLc⟩ with hLdef
    have hlift : IsLogLiftOf L
        (shiftedCurve (((edgeLoop g k).map (hwDcont j)).toContinuousMap) 0) := by
      intro t
      have hsc : shiftedCurve (((edgeLoop g k).map (hwDcont j)).toContinuousMap) 0 t
          = ((edgeLoop g k).map (hwDcont j)).toContinuousMap t := by
        simp [shiftedCurve]
      rw [hsc, hγ t]
      rfl
    have hspec := windingNumber_spec hcl hq hlift
    have hLval : L 1 - L 0 = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
      change 2 * (Real.pi : ℂ) * Complex.I * ((a + (n : ℝ) * ((1 : I) : ℝ) : ℝ) : ℂ)
          - 2 * (Real.pi : ℂ) * Complex.I * ((a + (n : ℝ) * ((0 : I) : ℝ) : ℝ) : ℂ)
          = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
      rw [Set.Icc.coe_one, Set.Icc.coe_zero]
      push_cast
      ring
    rw [hLval] at hspec
    have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    have hfin := mul_left_cancel₀ h2πi hspec
    exact_mod_cast hfin.symm
  -- the matrix of windings
  have hM0 : (![0, 1, 4] : Fin 3 → ℤ) 0 = 0 := rfl
  have hM1 : (![0, 1, 4] : Fin 3 → ℤ) 1 = 1 := rfl
  have hM2 : (![0, 1, 4] : Fin 3 → ℤ) 2 = 4 := rfl
  have hmat : ∀ j j' : Fin 3,
      loopWinding (vertexPoint g) (hwDcont j) (fun x => hwDne j x)
        ⟦edgeLoop g (![0, 1, 4] j')⟧ = if j = j' then 1 else 0 := by
    intro j j'
    rcases hj3 j with rfl | rfl | rfl <;> rcases hj3 j' with rfl | rfl | rfl
    · rw [if_pos rfl]
      refine hwind 0 _ 0 1 ?_
      intro t ht0 ht1
      rw [hM0, hFarc 0 0 t ht0 ht1,
        show ((0 : ℤ) - 0) % (4 * (g : ℤ)) = 0 by rw [sub_zero]; exact Int.zero_emod _,
        if_pos rfl]
      push_cast
      ring
    · rw [if_neg (by decide : ¬(0 : Fin 3) = 1)]
      refine hwind 0 _ 1 0 ?_
      intro t ht0 ht1
      rw [hM0, hM1, hFarc 0 1 t ht0 ht1,
        show ((1 : ℤ) - 0) % (4 * (g : ℤ)) = 1 by
          rw [sub_zero]; exact Int.emod_eq_of_lt (by norm_num) (by omega),
        if_neg (by norm_num : ¬(1 : ℤ) = 0), if_pos rfl]
      push_cast
      ring
    · rw [if_neg (by decide : ¬(0 : Fin 3) = 2)]
      refine hwind 0 _ 0 0 ?_
      intro t ht0 ht1
      rw [hM0, hM2, hFarc 0 4 t ht0 ht1,
        show ((4 : ℤ) - 0) % (4 * (g : ℤ)) = 4 by
          rw [sub_zero]; exact Int.emod_eq_of_lt (by norm_num) (by omega),
        if_neg (by norm_num : ¬(4 : ℤ) = 0), if_neg (by norm_num : ¬(4 : ℤ) = 1),
        if_neg (by norm_num : ¬(4 : ℤ) = 2)]
      push_cast
      ring
    · rw [if_neg (by decide : ¬(1 : Fin 3) = 0)]
      refine hwind 1 _ 0 0 ?_
      intro t ht0 ht1
      rw [hM1, hM0, hFarc 1 0 t ht0 ht1,
        show ((0 : ℤ) - 1) % (4 * (g : ℤ)) = 4 * (g : ℤ) - 1 by
          rw [show (0 : ℤ) - 1 = 4 * (g : ℤ) - 1 + 4 * (g : ℤ) * (-1) by ring,
            Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt (by omega) (by omega),
        if_neg (by omega : ¬4 * (g : ℤ) - 1 = 0), if_neg (by omega : ¬4 * (g : ℤ) - 1 = 1),
        if_neg (by omega : ¬4 * (g : ℤ) - 1 = 2)]
      push_cast
      ring
    · rw [if_pos rfl]
      refine hwind 1 _ 0 1 ?_
      intro t ht0 ht1
      rw [hM1, hFarc 1 1 t ht0 ht1,
        show ((1 : ℤ) - 1) % (4 * (g : ℤ)) = 0 by rw [sub_self]; exact Int.zero_emod _,
        if_pos rfl]
      push_cast
      ring
    · rw [if_neg (by decide : ¬(1 : Fin 3) = 2)]
      refine hwind 1 _ 0 0 ?_
      intro t ht0 ht1
      rw [hM1, hM2, hFarc 1 4 t ht0 ht1,
        show ((4 : ℤ) - 1) % (4 * (g : ℤ)) = 3 by
          rw [show (4 : ℤ) - 1 = 3 by norm_num]
          exact Int.emod_eq_of_lt (by norm_num) (by omega),
        if_neg (by norm_num : ¬(3 : ℤ) = 0), if_neg (by norm_num : ¬(3 : ℤ) = 1),
        if_neg (by norm_num : ¬(3 : ℤ) = 2)]
      push_cast
      ring
    · rw [if_neg (by decide : ¬(2 : Fin 3) = 0)]
      refine hwind 2 _ 0 0 ?_
      intro t ht0 ht1
      rw [hM2, hM0, hFarc 4 0 t ht0 ht1,
        show ((0 : ℤ) - 4) % (4 * (g : ℤ)) = 4 * (g : ℤ) - 4 by
          rw [show (0 : ℤ) - 4 = 4 * (g : ℤ) - 4 + 4 * (g : ℤ) * (-1) by ring,
            Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt (by omega) (by omega),
        if_neg (by omega : ¬4 * (g : ℤ) - 4 = 0), if_neg (by omega : ¬4 * (g : ℤ) - 4 = 1),
        if_neg (by omega : ¬4 * (g : ℤ) - 4 = 2)]
      push_cast
      ring
    · rw [if_neg (by decide : ¬(2 : Fin 3) = 1)]
      refine hwind 2 _ 0 0 ?_
      intro t ht0 ht1
      rw [hM2, hM1, hFarc 4 1 t ht0 ht1,
        show ((1 : ℤ) - 4) % (4 * (g : ℤ)) = 4 * (g : ℤ) - 3 by
          rw [show (1 : ℤ) - 4 = 4 * (g : ℤ) - 3 + 4 * (g : ℤ) * (-1) by ring,
            Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt (by omega) (by omega),
        if_neg (by omega : ¬4 * (g : ℤ) - 3 = 0), if_neg (by omega : ¬4 * (g : ℤ) - 3 = 1),
        if_neg (by omega : ¬4 * (g : ℤ) - 3 = 2)]
      push_cast
      ring
    · rw [if_pos rfl]
      refine hwind 2 _ 0 1 ?_
      intro t ht0 ht1
      rw [hM2, hFarc 4 4 t ht0 ht1,
        show ((4 : ℤ) - 4) % (4 * (g : ℤ)) = 0 by rw [sub_self]; exact Int.zero_emod _,
        if_pos rfl]
      push_cast
      ring
  exact ⟨wD, hwDcont, hwDne, hmat⟩

/-- **Surjection onto `ℤ³`**: the joint winding character of the three functionals is a
concatenation-additive surjection of the loop classes at the vertex onto `ℤ³`. -/
theorem exists_pi1_surjection_zpow3 (g : ℕ) [NeZero g] (hg : 2 ≤ g) :
    ∃ μ : Path.Homotopic.Quotient (vertexPoint g) (vertexPoint g) → (Fin 3 → ℤ),
      (∀ a b, μ (a.trans b) = μ a + μ b) ∧ Function.Surjective μ := by
  obtain ⟨w, hw, hw0, hmat⟩ := exists_winding_functionals g hg
  set μ : Path.Homotopic.Quotient (vertexPoint g) (vertexPoint g) → (Fin 3 → ℤ) :=
    fun γ j => loopWinding (vertexPoint g) (hw j) (fun x => hw0 j x) γ with hμdef
  have hadd : ∀ a b, μ (a.trans b) = μ a + μ b := by
    intro a b
    funext j
    change loopWinding (vertexPoint g) (hw j) (fun x => hw0 j x) (a.trans b)
      = loopWinding (vertexPoint g) (hw j) (fun x => hw0 j x) a
        + loopWinding (vertexPoint g) (hw j) (fun x => hw0 j x) b
    exact loopWinding_trans (vertexPoint g) (hw j) (fun x => hw0 j x) a b
  have hrefl : ∀ j : Fin 3, μ ⟦Path.refl (vertexPoint g)⟧ j = 0 := by
    intro j
    change windingNumber (((Path.refl (vertexPoint g)).map (hw j)).toContinuousMap) 0 = 0
    have hconst : ((Path.refl (vertexPoint g)).map (hw j)).toContinuousMap
        = ContinuousMap.const I (w j (vertexPoint g)) := by
      ext t
      rfl
    rw [hconst]
    exact windingNumber_const _ _ (hw0 j (vertexPoint g))
  have hsymm : ∀ (p : Path (vertexPoint g) (vertexPoint g)) (j : Fin 3),
      μ ⟦p.symm⟧ j = -μ ⟦p⟧ j := by
    intro p j
    change windingNumber ((p.symm.map (hw j)).toContinuousMap) 0
      = -windingNumber ((p.map (hw j)).toContinuousMap) 0
    rw [← Path.map_symm]
    exact windingNumber_symm (p.map (hw j)) fun t => hw0 j (p t)
  have hpow : ∀ (p : Path (vertexPoint g) (vertexPoint g)) (m : ℕ),
      ∃ γ, ∀ j : Fin 3, μ γ j = (m : ℤ) * μ ⟦p⟧ j := by
    intro p m
    induction m with
    | zero =>
        refine ⟨⟦Path.refl (vertexPoint g)⟧, fun j => ?_⟩
        rw [hrefl j]
        push_cast
        ring
    | succ i ih =>
        obtain ⟨γ, hγ⟩ := ih
        refine ⟨γ.trans ⟦p⟧, fun j => ?_⟩
        have h1 := congrFun (hadd γ ⟦p⟧) j
        rw [Pi.add_apply] at h1
        rw [h1, hγ j]
        push_cast
        ring
  have hzpow : ∀ (p : Path (vertexPoint g) (vertexPoint g)) (z : ℤ),
      ∃ γ, ∀ j : Fin 3, μ γ j = z * μ ⟦p⟧ j := by
    intro p z
    rcases le_or_gt 0 z with hz | hz
    · obtain ⟨γ, hγ⟩ := hpow p z.toNat
      refine ⟨γ, fun j => ?_⟩
      rw [hγ j, Int.toNat_of_nonneg hz]
    · obtain ⟨γ, hγ⟩ := hpow p.symm (-z).toNat
      refine ⟨γ, fun j => ?_⟩
      rw [hγ j, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -z), hsymm p j]
      ring
  refine ⟨μ, hadd, ?_⟩
  intro v
  obtain ⟨γ₀, h₀⟩ := hzpow (edgeLoop g (![0, 1, 4] 0)) (v 0)
  obtain ⟨γ₁, h₁⟩ := hzpow (edgeLoop g (![0, 1, 4] 1)) (v 1)
  obtain ⟨γ₂, h₂⟩ := hzpow (edgeLoop g (![0, 1, 4] 2)) (v 2)
  refine ⟨γ₀.trans (γ₁.trans γ₂), ?_⟩
  funext j
  have ha1 := congrFun (hadd γ₀ (γ₁.trans γ₂)) j
  have ha2 := congrFun (hadd γ₁ γ₂) j
  rw [Pi.add_apply] at ha1 ha2
  have hgen0 : μ ⟦edgeLoop g (![0, 1, 4] 0)⟧ j = if j = 0 then 1 else 0 := hmat j 0
  have hgen1 : μ ⟦edgeLoop g (![0, 1, 4] 1)⟧ j = if j = 1 then 1 else 0 := hmat j 1
  have hgen2 : μ ⟦edgeLoop g (![0, 1, 4] 2)⟧ j = if j = 2 then 1 else 0 := hmat j 2
  rw [ha1, ha2, h₀ j, h₁ j, h₂ j, hgen0, hgen1, hgen2]
  have hj3 : ∀ jj : Fin 3, jj = 0 ∨ jj = 1 ∨ jj = 2 := by decide
  rcases hj3 j with rfl | rfl | rfl
  · rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 3) = 1),
      if_neg (by decide : ¬(0 : Fin 3) = 2)]
    ring
  · rw [if_neg (by decide : ¬(1 : Fin 3) = 0), if_pos rfl,
      if_neg (by decide : ¬(1 : Fin 3) = 2)]
    ring
  · rw [if_neg (by decide : ¬(2 : Fin 3) = 0), if_neg (by decide : ¬(2 : Fin 3) = 1),
      if_pos rfl]
    ring

end RiemannDynamics
