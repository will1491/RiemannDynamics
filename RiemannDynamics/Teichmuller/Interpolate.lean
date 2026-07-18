import RiemannDynamics.Teichmuller.Dirichlet
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-!
# Equivariant interpolation along converging generator tuples

The interpolation engine for Marden stability: words in the generators, relation killing
under a trace gap, near-identity correction paths in `SL(2, ℝ)`, collar transition maps
with small Beltrami coefficient, and the development of the corrected tile maps into a
global equivariant self-map of the upper half plane.

* `wordEval` — evaluation of a word in a generator tuple; membership, closure extraction,
  and entrywise convergence along converging tuples.
* `eventually_eq_pm_one_of_tendsto_pm_one` — relation killing: under a trace gap, elements
  converging to `±1` are eventually `±1`.
* `eventually_eq_up_to_sign_of_tendsto` — two elements of trace-gapped groups converging to
  a common limit are eventually equal up to sign.
* `correctionPath` — the determinant-normalized linear path from `1` to a matrix near `1`,
  with entrywise smoothness and size bounds.
* `matMoebius` — the Möbius map of a real `2 × 2` matrix.
* `collar_correction_estimate` — the transition map of a cutoff correction along a collar
  is differentiable with Beltrami coefficient controlled by the distance of the correction
  matrix to `1`, and is injective on a convex collar patch.
* `exists_developed_interpolation` — the development of the corrected tile maps: a global
  self-map of the upper half plane, with two-sided inverse, locally Sobolev, with positive
  Jacobian and Beltrami coefficient at most `κ`, intertwining the generator tuples exactly.
-/

open MeasureTheory
open scoped ENNReal

namespace RiemannDynamics

/-! ## Words in a generator tuple -/

/-- Evaluation of a word: the product of the generators and inverse generators listed by the
letters of the word. -/
def wordEval {ι : Type} (g : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (l : List (ι × Bool)) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  (l.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod

/-- A word in elements of a subgroup evaluates into the subgroup. -/
theorem wordEval_mem {ι : Type} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {g : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : ∀ i, g i ∈ Γ)
    (l : List (ι × Bool)) : wordEval g l ∈ Γ := by
  rw [wordEval]
  refine Subgroup.list_prod_mem Γ ?_
  intro x hx
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hx
  by_cases hbp : p.2
  · simpa [hbp] using hg p.1
  · simpa [hbp] using inv_mem (hg p.1)

/-- Every element of the closure of the range of a tuple is the value of a word. -/
theorem exists_wordEval_eq_of_mem_closure {ι : Type}
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Subgroup.closure (Set.range ρ)) :
    ∃ l : List (ι × Bool), wordEval ρ l = δ := by
  have happend : ∀ l₁ l₂ : List (ι × Bool),
      wordEval ρ (l₁ ++ l₂) = wordEval ρ l₁ * wordEval ρ l₂ := by
    intro l₁ l₂
    simp [wordEval]
  have hcons : ∀ (q : ι × Bool) (l' : List (ι × Bool)),
      wordEval ρ (q :: l') = (if q.2 then ρ q.1 else (ρ q.1)⁻¹) * wordEval ρ l' := by
    intro q l'
    simp [wordEval]
  have hinv : ∀ l : List (ι × Bool),
      wordEval ρ (l.reverse.map fun p => (p.1, !p.2)) = (wordEval ρ l)⁻¹ := by
    intro l
    induction l with
    | nil => simp [wordEval]
    | cons p l ih =>
      have hsingle : wordEval ρ ([p].map fun q => (q.1, !q.2))
          = (if p.2 then ρ p.1 else (ρ p.1)⁻¹)⁻¹ := by
        by_cases hbp : p.2 <;> simp [wordEval, hbp]
      rw [List.reverse_cons, List.map_append, happend, ih, hsingle, hcons, mul_inv_rev]
  induction hδ using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨[(i, true)], by simp [wordEval]⟩
  | one => exact ⟨[], by simp [wordEval]⟩
  | mul y z _hy _hz ihy ihz =>
    obtain ⟨l₁, h₁⟩ := ihy
    obtain ⟨l₂, h₂⟩ := ihz
    exact ⟨l₁ ++ l₂, by rw [happend, h₁, h₂]⟩
  | inv y _hy ihy =>
    obtain ⟨l, h⟩ := ihy
    exact ⟨l.reverse.map fun p => (p.1, !p.2), by rw [hinv, h]⟩

/-- Word values converge along entrywise-converging generator tuples: finite products of
convergent sequences converge. -/
theorem tendsto_wordEval {ι : Type} {gens : ℕ → ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    {ρ : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hlim : ∀ i, Filter.Tendsto (fun n => gens n i) Filter.atTop (nhds (ρ i)))
    (l : List (ι × Bool)) :
    Filter.Tendsto (fun n => wordEval (gens n) l) Filter.atTop (nhds (wordEval ρ l)) := by
  induction l with
  | nil =>
    have h1 : ∀ g : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ, wordEval g [] = 1 := fun g => rfl
    simp only [h1]
    exact tendsto_const_nhds
  | cons p l ih =>
    have hcons : ∀ g : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ,
        wordEval g (p :: l) = (if p.2 then g p.1 else (g p.1)⁻¹) * wordEval g l := by
      intro g
      simp [wordEval]
    have hp : Filter.Tendsto (fun n => if p.2 then gens n p.1 else (gens n p.1)⁻¹)
        Filter.atTop (nhds (if p.2 then ρ p.1 else (ρ p.1)⁻¹)) := by
      by_cases hbp : p.2
      · simpa [hbp] using hlim p.1
      · simpa [hbp] using (hlim p.1).inv
    simp only [hcons]
    exact hp.mul ih

/-! ## Relation killing under a trace gap -/

/-- **Relation killing**: in a sequence of trace-gapped groups, elements converging to `±1`
are eventually `±1`. The trace converges to `2`, so it eventually violates the gap, forcing
the elements to act trivially, and trivially-acting elements are `±1`. -/
theorem eventually_eq_pm_one_of_tendsto_pm_one {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    {V : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hmem : ∀ n, V n ∈ Γ n)
    {W : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (W : Matrix (Fin 2) (Fin 2) ℝ) = -1)
    (hlim : Filter.Tendsto V Filter.atTop (nhds W)) :
    ∀ᶠ n in Filter.atTop, (V n : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨
      (V n : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  have hone : (1 : ℝ) < Real.cosh (ε / 2) :=
    Real.one_lt_cosh.mpr (by positivity : (0:ℝ) < ε / 2).ne'
  have habs : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => |Matrix.trace M| :=
    ((continuous_id (X := Matrix (Fin 2) (Fin 2) ℝ)).matrix_trace).abs
  have hmat : Filter.Tendsto (fun n => ((V n : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)) Filter.atTop
      (nhds ((W : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :=
    tendsto_subtype_rng.mp hlim
  have htr : Filter.Tendsto (fun n => |Matrix.trace ((V n : Matrix (Fin 2) (Fin 2) ℝ))|)
      Filter.atTop (nhds |Matrix.trace ((W : Matrix (Fin 2) (Fin 2) ℝ))|) :=
    (habs.tendsto _).comp hmat
  have htrW : |Matrix.trace ((W : Matrix (Fin 2) (Fin 2) ℝ))| = 2 := by
    rcases hW with h | h <;> rw [h]
    · rw [Matrix.trace_one]
      norm_num [Fintype.card_fin]
    · rw [Matrix.trace_neg, Matrix.trace_one]
      norm_num [Fintype.card_fin]
  rw [htrW] at htr
  have h2lt : (2 : ℝ) < 2 * Real.cosh (ε / 2) := by linarith
  have hev : ∀ᶠ n in Filter.atTop,
      |Matrix.trace ((V n : Matrix (Fin 2) (Fin 2) ℝ))| < 2 * Real.cosh (ε / 2) :=
    htr.eventually_lt_const h2lt
  filter_upwards [hev] with n hn
  have hnt : ¬ actsNontrivially (V n) := fun hnt =>
    absurd (hgap n (V n) (hmem n) hnt) (not_le.mpr hn)
  have htriv : ∀ τ : UpperHalfPlane, V n • τ = τ := by
    intro τ
    by_contra hne
    exact hnt ⟨τ, hne⟩
  exact (smul_id_iff_pm_one (V n)).mp htriv

/-- Two elements of trace-gapped groups converging to a common limit are eventually equal up
to sign: their quotient converges to `1` and is eventually `±1`. -/
theorem eventually_eq_up_to_sign_of_tendsto {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    {a b : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (ha : ∀ n, a n ∈ Γ n) (hb : ∀ n, b n ∈ Γ n)
    {L : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hla : Filter.Tendsto a Filter.atTop (nhds L))
    (hlb : Filter.Tendsto b Filter.atTop (nhds L)) :
    ∀ᶠ n in Filter.atTop, a n = b n ∨
      (a n : Matrix (Fin 2) (Fin 2) ℝ) = -(b n : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hmemV : ∀ n, a n * (b n)⁻¹ ∈ Γ n := fun n => mul_mem (ha n) (inv_mem (hb n))
  have hlimV : Filter.Tendsto (fun n => a n * (b n)⁻¹) Filter.atTop (nhds 1) := by
    have h := hla.mul hlb.inv
    rwa [mul_inv_cancel] at h
  have hW : ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨
      ((1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -1 :=
    Or.inl (Matrix.SpecialLinearGroup.coe_one)
  have hev := eventually_eq_pm_one_of_tendsto_pm_one hε Γ hgap
    (V := fun n => a n * (b n)⁻¹) hmemV hW hlimV
  filter_upwards [hev] with n hn
  rcases hn with h1 | h1
  · left
    have h1' : a n * (b n)⁻¹ = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact h1)
    exact mul_inv_eq_one.mp h1'
  · right
    have hm : (a n : Matrix (Fin 2) (Fin 2) ℝ) *
        (((b n)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      exact h1
    have hleft : (((b n)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (b n : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc (a n : Matrix (Fin 2) (Fin 2) ℝ)
        = (a n : Matrix (Fin 2) (Fin 2) ℝ) *
          ((((b n)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
            (b n : Matrix (Fin 2) (Fin 2) ℝ)) := by rw [hleft, mul_one]
      _ = ((a n : Matrix (Fin 2) (Fin 2) ℝ) *
            (((b n)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) *
          (b n : Matrix (Fin 2) (Fin 2) ℝ) := by rw [mul_assoc]
      _ = (-1) * (b n : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hm]
      _ = -(b n : Matrix (Fin 2) (Fin 2) ℝ) := by rw [neg_one_mul]

/-! ## Near-identity correction paths -/

/-- The entrywise sup distance between two real `2 × 2` matrices. -/
noncomputable def entrywiseDist (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  max (max |A 0 0 - B 0 0| |A 0 1 - B 0 1|) (max |A 1 0 - B 1 0| |A 1 1 - B 1 1|)

/-- The determinant-normalized linear path from `1` to `A`:
`u ↦ det(1 + u(A − 1))^{−1/2} · (1 + u(A − 1))`. -/
noncomputable def correctionPath (A : Matrix (Fin 2) (Fin 2) ℝ) (u : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt (1 + u • (A - 1)).det)⁻¹ • (1 + u • (A - 1))

/-- The correction path starts at the identity. -/
theorem correctionPath_zero (A : Matrix (Fin 2) (Fin 2) ℝ) : correctionPath A 0 = 1 := by
  simp [correctionPath]

/-- The correction path of a determinant-one matrix ends at the matrix. -/
theorem correctionPath_one {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) :
    correctionPath A 1 = A := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 : ℝ) • (A - 1) = A := by
    rw [one_smul]; abel
  rw [correctionPath, h1, hA, Real.sqrt_one, inv_one, one_smul]

set_option maxHeartbeats 400000 in
-- The determinant-normalized path derivative chain (polynomial, square root, inverse,
-- product) elaborates as one large term; the bound extraction exceeds the default
-- heartbeat budget.
/-- **Bounds for the correction path**: for matrices near `1`, the interpolated determinant
is positive, the path stays on determinant one, and its entrywise distance to `1` and its
entrywise `u`-derivative are linearly controlled by the entrywise distance of the endpoint
to `1`, uniformly on the parameter interval. -/
theorem correctionPath_bounds :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ A : Matrix (Fin 2) (Fin 2) ℝ, entrywiseDist A 1 ≤ c₀ →
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          0 < (1 + u • (A - 1)).det ∧
          (A.det = 1 → (correctionPath A u).det = 1) ∧
          entrywiseDist (correctionPath A u) 1 ≤ C * entrywiseDist A 1 ∧
          (∀ i j : Fin 2,
            HasDerivAt (fun v : ℝ => correctionPath A v i j)
              (deriv (fun v : ℝ => correctionPath A v i j) u) u ∧
            |deriv (fun v : ℝ => correctionPath A v i j) u| ≤ C * entrywiseDist A 1) := by
  refine ⟨1 / 8, 20, by norm_num, by norm_num, ?_⟩
  have brickD : ∀ a b cc f dd : ℝ, |a| ≤ dd → |b| ≤ dd → |cc| ≤ dd → |f| ≤ dd → dd ≤ 1 / 8 →
      1 / 2 ≤ (1 + a) * (1 + b) - cc * f ∧ (1 + a) * (1 + b) - cc * f ≤ 3 / 2 ∧
        |(1 + a) * (1 + b) - cc * f - 1| ≤ 3 * dd := by
    intro a b cc f dd ha hb hc hf hdd8
    have hd0 : 0 ≤ dd := le_trans (abs_nonneg _) ha
    obtain ⟨ha1, ha2⟩ := abs_le.mp ha
    obtain ⟨hb1, hb2⟩ := abs_le.mp hb
    have hab : |a * b| ≤ dd * dd := by
      rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hd0
    have hcf : |cc * f| ≤ dd * dd := by
      rw [abs_mul]; exact mul_le_mul hc hf (abs_nonneg _) hd0
    obtain ⟨hab1, hab2⟩ := abs_le.mp hab
    obtain ⟨hcf1, hcf2⟩ := abs_le.mp hcf
    have hdd2 : dd * dd ≤ 1 / 8 * dd := mul_le_mul_of_nonneg_right hdd8 hd0
    refine ⟨by nlinarith [hab1, hcf2], by nlinarith [hab2, hcf1], ?_⟩
    rw [abs_le]
    exact ⟨by nlinarith [hab1, hcf2], by nlinarith [hab2, hcf1]⟩
  have brickS : ∀ s D dd : ℝ, s ^ 2 = D → 0 < s → 1 / 2 ≤ D → D ≤ 3 / 2 →
      |D - 1| ≤ 3 * dd → 0 ≤ dd → 7 / 10 ≤ s ∧ s ≤ 13 / 10 ∧ |1 - s| ≤ 2 * dd := by
    intro s D dd hs2 hsp hlo hhi hD1 hd0
    obtain ⟨h1, h2⟩ := abs_le.mp hD1
    have hslb : 7 / 10 ≤ s := by
      by_contra hcon
      push Not at hcon
      have hss : s * s < (7 / 10) * (7 / 10) :=
        mul_lt_mul' hcon.le hcon hsp.le (by norm_num)
      have hD49 : D < 49 / 100 := by rw [← hs2, pow_two]; linarith
      linarith
    have hsub : s ≤ 13 / 10 := by
      by_contra hcon
      push Not at hcon
      have hss : (13 / 10) * (13 / 10) < s * s :=
        mul_lt_mul' hcon.le hcon (by norm_num) hsp
      have hD169 : 169 / 100 < D := by rw [← hs2, pow_two]; linarith
      linarith
    have hid : (1 - s) * (1 + s) = 1 - D := by linear_combination -hs2
    have hid' : (s - 1) * (1 + s) = D - 1 := by linear_combination hs2
    have hsum : (17 : ℝ) / 10 ≤ 1 + s := by linarith
    refine ⟨hslb, hsub, ?_⟩
    rw [abs_le]
    constructor
    · by_contra hcon
      push Not at hcon
      have hp : 2 * dd * (17 / 10) < (s - 1) * (1 + s) :=
        mul_lt_mul (by linarith) hsum (by norm_num) (by linarith)
      linarith
    · by_contra hcon
      push Not at hcon
      have hp : 2 * dd * (17 / 10) < (1 - s) * (1 + s) :=
        mul_lt_mul (by linarith) hsum (by norm_num) (by linarith)
      linarith
  have brickE : ∀ s dd dl w : ℝ, 0 < s → 7 / 10 ≤ s → |1 - s| ≤ 2 * dd → 0 ≤ dd →
      0 ≤ dl → dl ≤ 1 → |w| ≤ dd → |s⁻¹ * (dl + w) - dl| ≤ 20 * dd := by
    intro s dd dl w hsp hslb h1s hd0 hdl0 hdl1 hw
    have hkey : s⁻¹ * (dl + w) - dl = (w + dl * (1 - s)) / s := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
    have h1 := abs_add_le w (dl * (1 - s))
    have h2 : |dl * (1 - s)| ≤ 2 * dd := by
      rw [abs_mul, abs_of_nonneg hdl0]
      calc dl * |1 - s| ≤ 1 * |1 - s| := mul_le_mul_of_nonneg_right hdl1 (abs_nonneg _)
        _ = |1 - s| := one_mul _
        _ ≤ 2 * dd := h1s
    have h3 : 20 * dd * (7 / 10) ≤ 20 * dd * s :=
      mul_le_mul_of_nonneg_left hslb (by linarith)
    linarith [h1, hw]
  intro A hA u hu
  obtain ⟨hu0, hu1⟩ := hu
  have hE : ∀ i j : Fin 2, |(A - 1) i j| ≤ entrywiseDist A 1 := by
    intro i j
    unfold entrywiseDist
    rw [Matrix.sub_apply]
    fin_cases i <;> fin_cases j
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hd0 : 0 ≤ entrywiseDist A 1 := le_trans (abs_nonneg _) (hE 0 0)
  have hue : ∀ i j : Fin 2, |u * (A - 1) i j| ≤ entrywiseDist A 1 := by
    intro i j
    rw [abs_mul, abs_of_nonneg hu0]
    calc u * |(A - 1) i j| ≤ 1 * entrywiseDist A 1 :=
          mul_le_mul hu1 (hE i j) (abs_nonneg _) (by norm_num)
      _ = entrywiseDist A 1 := one_mul _
  have hDfun : ∀ v : ℝ, (1 + v • (A - 1)).det
      = (1 + v * (A - 1) 0 0) * (1 + v * (A - 1) 1 1)
        - (v * (A - 1) 0 1) * (v * (A - 1) 1 0) := by
    intro v
    rw [Matrix.det_fin_two]
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  obtain ⟨hDlo, hDhi, hD1⟩ := brickD (u * (A - 1) 0 0) (u * (A - 1) 1 1) (u * (A - 1) 0 1)
    (u * (A - 1) 1 0) (entrywiseDist A 1) (hue 0 0) (hue 1 1) (hue 0 1) (hue 1 0) hA
  rw [← hDfun u] at hDlo hDhi hD1
  have hDpos : 0 < (1 + u • (A - 1)).det := lt_of_lt_of_le (by norm_num) hDlo
  have hdet1 : A.det = 1 → (correctionPath A u).det = 1 := by
    intro _
    rw [correctionPath, Matrix.det_smul, Fintype.card_fin, inv_pow,
      Real.sq_sqrt hDpos.le, inv_mul_cancel₀ (ne_of_gt hDpos)]
  have hs2 : Real.sqrt ((1 + u • (A - 1)).det) ^ 2 = (1 + u • (A - 1)).det :=
    Real.sq_sqrt hDpos.le
  have hspos : 0 < Real.sqrt ((1 + u • (A - 1)).det) := Real.sqrt_pos.mpr hDpos
  obtain ⟨hs_lb, hs_ub, h1s⟩ := brickS (Real.sqrt ((1 + u • (A - 1)).det))
    ((1 + u • (A - 1)).det) (entrywiseDist A 1) hs2 hspos hDlo hDhi hD1 hd0
  have hgen : ∀ i j : Fin 2,
      |correctionPath A u i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|
        ≤ 20 * entrywiseDist A 1 := by
    intro i j
    have hcp : correctionPath A u i j = (Real.sqrt ((1 + u • (A - 1)).det))⁻¹
        * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j + u * (A - 1) i j) := by
      rw [correctionPath, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, smul_eq_mul]
    have hδ01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = 0
        ∨ (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = 1 := by
      by_cases h : i = j
      · right; rw [h, Matrix.one_apply_eq]
      · left; rw [Matrix.one_apply_ne h]
    have hδ0 : 0 ≤ (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
      rcases hδ01 with h | h <;> simp [h]
    have hδ1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j ≤ 1 := by
      rcases hδ01 with h | h <;> simp [h]
    rw [hcp]
    exact brickE _ _ _ _ hspos hs_lb h1s hd0 hδ0 hδ1 (hue i j)
  have hpart3 : entrywiseDist (correctionPath A u) 1 ≤ 20 * entrywiseDist A 1 := by
    unfold entrywiseDist
    exact max_le (max_le (hgen 0 0) (hgen 0 1)) (max_le (hgen 1 0) (hgen 1 1))
  refine ⟨hDpos, hdet1, hpart3, ?_⟩
  intro i j
  have ht2 : |(A - 1) 0 0 + (A - 1) 1 1| ≤ 2 * entrywiseDist A 1 := by
    calc |(A - 1) 0 0 + (A - 1) 1 1| ≤ |(A - 1) 0 0| + |(A - 1) 1 1| := abs_add_le _ _
      _ ≤ entrywiseDist A 1 + entrywiseDist A 1 := add_le_add (hE 0 0) (hE 1 1)
      _ = 2 * entrywiseDist A 1 := by ring
  have hq2 : |(A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0|
      ≤ 2 * (entrywiseDist A 1 * entrywiseDist A 1) := by
    calc |(A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0|
        ≤ |(A - 1) 0 0 * (A - 1) 1 1| + |(A - 1) 0 1 * (A - 1) 1 0| := abs_sub _ _
      _ ≤ entrywiseDist A 1 * entrywiseDist A 1 + entrywiseDist A 1 * entrywiseDist A 1 := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hE 0 0) (hE 1 1) (abs_nonneg _) hd0)
            (mul_le_mul (hE 0 1) (hE 1 0) (abs_nonneg _) hd0)
      _ = 2 * (entrywiseDist A 1 * entrywiseDist A 1) := by ring
  have hδ01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = 0
      ∨ (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = 1 := by
    by_cases h : i = j
    · right; rw [h, Matrix.one_apply_eq]
    · left; rw [Matrix.one_apply_ne h]
  have hδ0 : 0 ≤ (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rcases hδ01 with h | h <;> simp [h]
  have hδ1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j ≤ 1 := by
    rcases hδ01 with h | h <;> simp [h]
  have hDfun' : ∀ v : ℝ, (1 + v • (A - 1)).det
      = 1 + (((A - 1) 0 0 + (A - 1) 1 1) * v
        + ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * v ^ 2) := by
    intro v
    rw [hDfun v]; ring
  have hpoly : HasDerivAt (fun v : ℝ => 1 + (((A - 1) 0 0 + (A - 1) 1 1) * v
      + ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * v ^ 2))
      (((A - 1) 0 0 + (A - 1) 1 1) * 1
        + ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * ((2 : ℕ) * u ^ (2 - 1))) u :=
    (((hasDerivAt_id u).const_mul ((A - 1) 0 0 + (A - 1) 1 1)).add
      ((hasDerivAt_pow 2 u).const_mul
        ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0))).const_add 1
  have hDD : HasDerivAt (fun v : ℝ => (1 + v • (A - 1)).det)
      (((A - 1) 0 0 + (A - 1) 1 1)
        + 2 * ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * u) u := by
    rw [show (fun v : ℝ => (1 + v • (A - 1)).det)
      = fun v : ℝ => 1 + (((A - 1) 0 0 + (A - 1) 1 1) * v
        + ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * v ^ 2) from funext hDfun']
    convert hpoly using 1
    push_cast
    ring
  have hsq : HasDerivAt (fun v : ℝ => Real.sqrt ((1 + v • (A - 1)).det))
      ((((A - 1) 0 0 + (A - 1) 1 1)
          + 2 * ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * u)
        / (2 * Real.sqrt ((1 + u • (A - 1)).det))) u :=
    hDD.sqrt (ne_of_gt hDpos)
  have hinv : HasDerivAt (fun v : ℝ => (Real.sqrt ((1 + v • (A - 1)).det))⁻¹)
      (-((((A - 1) 0 0 + (A - 1) 1 1)
            + 2 * ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * u)
          / (2 * Real.sqrt ((1 + u • (A - 1)).det)))
        / Real.sqrt ((1 + u • (A - 1)).det) ^ 2) u :=
    hsq.inv (ne_of_gt hspos)
  have hlin : HasDerivAt (fun v : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + v * (A - 1) i j)
      (1 * (A - 1) i j) u :=
    ((hasDerivAt_id u).mul_const ((A - 1) i j)).const_add ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
  have hprod : HasDerivAt (fun v : ℝ => (Real.sqrt ((1 + v • (A - 1)).det))⁻¹
      * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j + v * (A - 1) i j))
      (-((((A - 1) 0 0 + (A - 1) 1 1)
            + 2 * ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * u)
          / (2 * Real.sqrt ((1 + u • (A - 1)).det)))
        / Real.sqrt ((1 + u • (A - 1)).det) ^ 2
        * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j + u * (A - 1) i j)
        + (Real.sqrt ((1 + u • (A - 1)).det))⁻¹ * (1 * (A - 1) i j)) u :=
    hinv.mul hlin
  have hfun_eq : (fun v : ℝ => correctionPath A v i j)
      = fun v : ℝ => (Real.sqrt ((1 + v • (A - 1)).det))⁻¹
        * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j + v * (A - 1) i j) := by
    funext v
    rw [correctionPath, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, smul_eq_mul]
  have hF : HasDerivAt (fun v : ℝ => correctionPath A v i j)
      (-((((A - 1) 0 0 + (A - 1) 1 1)
            + 2 * ((A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0) * u)
          / (2 * Real.sqrt ((1 + u • (A - 1)).det)))
        / Real.sqrt ((1 + u • (A - 1)).det) ^ 2
        * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j + u * (A - 1) i j)
        + (Real.sqrt ((1 + u • (A - 1)).det))⁻¹ * (1 * (A - 1) i j)) u := by
    rw [hfun_eq]
    exact hprod
  refine ⟨by rw [hF.deriv]; exact hF, ?_⟩
  rw [hF.deriv]
  obtain ⟨t, ht_def⟩ : ∃ x : ℝ, (A - 1) 0 0 + (A - 1) 1 1 = x := ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ x : ℝ,
      (A - 1) 0 0 * (A - 1) 1 1 - (A - 1) 0 1 * (A - 1) 1 0 = x := ⟨_, rfl⟩
  obtain ⟨e, he_def⟩ : ∃ x : ℝ, (A - 1) i j = x := ⟨_, rfl⟩
  obtain ⟨dl, hdl_def⟩ : ∃ x : ℝ, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = x := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ x : ℝ, Real.sqrt ((1 + u • (A - 1)).det) = x := ⟨_, rfl⟩
  obtain ⟨D, hD_def⟩ : ∃ x : ℝ, (1 + u • (A - 1)).det = x := ⟨_, rfl⟩
  obtain ⟨d, hd_def⟩ : ∃ x : ℝ, entrywiseDist A 1 = x := ⟨_, rfl⟩
  rw [ht_def, hq_def, he_def, hdl_def, hs_def, hd_def]
  rw [ht_def, hd_def] at ht2
  rw [hq_def, hd_def] at hq2
  have hE' : |e| ≤ d := by rw [← he_def, ← hd_def]; exact hE i j
  rw [hdl_def] at hδ0 hδ1
  rw [hs_def] at hs2 hspos hs_lb
  rw [hD_def] at hs2 hDhi hDpos
  rw [hd_def] at hd0
  have hd8 : d ≤ 1 / 8 := by rw [← hd_def]; exact hA
  have hdd : d * d ≤ 1 / 8 * d := mul_le_mul_of_nonneg_right hd8 hd0
  have h2s3 : (0 : ℝ) < 2 * s ^ 3 := by
    have := pow_pos hspos 3
    linarith
  have hLid : -((t + 2 * q * u) / (2 * s)) / s ^ 2 * (dl + u * e) + s⁻¹ * (1 * e)
      = (-(t + 2 * q * u) * (dl + u * e) + 2 * s ^ 2 * e) / (2 * s ^ 3) := by
    field_simp
  rw [hLid, abs_div, abs_of_pos h2s3, div_le_iff₀ h2s3]
  have hu' : |u| ≤ 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have hD'b : |t + 2 * q * u| ≤ 3 * d := by
    have h1 := abs_add_le t (2 * q * u)
    have h2 : |2 * q * u| ≤ 4 * (d * d) := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |q| * |u| ≤ 2 * |q| * 1 :=
            mul_le_mul_of_nonneg_left hu' (by linarith [abs_nonneg q])
        _ = 2 * |q| := mul_one _
        _ ≤ 4 * (d * d) := by linarith [hq2]
    linarith [ht2, hdd]
  have hm : |dl + u * e| ≤ 1 + d := by
    have h1 := abs_add_le dl (u * e)
    have h2 : |u * e| ≤ d := by
      rw [abs_mul]
      calc |u| * |e| ≤ 1 * |e| := mul_le_mul_of_nonneg_right hu' (abs_nonneg _)
        _ = |e| := one_mul _
        _ ≤ d := hE'
    rw [abs_of_nonneg hδ0] at h1
    linarith
  have hnum : |-(t + 2 * q * u) * (dl + u * e) + 2 * s ^ 2 * e| ≤ 3 * d * (1 + d) + 3 * d := by
    have h1 := abs_add_le (-(t + 2 * q * u) * (dl + u * e)) (2 * s ^ 2 * e)
    have h2 : |-(t + 2 * q * u) * (dl + u * e)| ≤ 3 * d * (1 + d) := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul hD'b hm (abs_nonneg _) (by linarith)
    have h3 : |2 * s ^ 2 * e| ≤ 3 * d := by
      rw [hs2, abs_mul, abs_mul, abs_two, abs_of_pos hDpos]
      calc 2 * D * |e| ≤ 3 * |e| :=
            mul_le_mul_of_nonneg_right (by linarith [hDhi]) (abs_nonneg e)
        _ ≤ 3 * d := by linarith [hE']
    linarith
  have hs3 : 343 / 1000 ≤ s ^ 3 := by
    have h1 : ((7 : ℝ) / 10) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs_lb 3
    norm_num at h1
    linarith
  have hup : 3 * d * (1 + d) + 3 * d ≤ 7 * d := by nlinarith [hdd, hd0]
  have hlow : 7 * d ≤ 20 * d * (2 * s ^ 3) := by
    have h1 : 40 * d * (343 / 1000) ≤ 40 * d * s ^ 3 :=
      mul_le_mul_of_nonneg_left hs3 (by linarith)
    nlinarith [h1, hd0]
  linarith [hnum]

/-! ## The Möbius map of a matrix and the collar transition estimate -/

/-- The Möbius map of a real `2 × 2` matrix, totalized with junk value `0` at the pole. -/
noncomputable def matMoebius (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * z + (M 0 1 : ℂ)) / ((M 1 0 : ℂ) * z + (M 1 1 : ℂ))

/-- On elements of `SL(2, ℝ)` the matrix Möbius map is the plane Möbius map. -/
theorem matMoebius_coe (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    matMoebius (γ : Matrix (Fin 2) (Fin 2) ℝ) z = moebiusMap γ z := rfl

set_option maxHeartbeats 400000 in
-- The per-point Wirtinger package of the correction map combines the path bounds with
-- the Beltrami quotient estimate in a single elaboration exceeding the default budget.
/-- **Collar transition estimate.** Along a `C¹` signed collar coordinate `sd` and a `C¹`
cutoff `η` with values in `[0, 1]`, the transition map
`z ↦ matMoebius (correctionPath c (η (sd z))) z` of a correction matrix `c` near `1` is,
on a compact subset `S` of the upper half plane, differentiable with conjugate-linear
derivative part controlled by `entrywiseDist c 1` relative to its complex-linear part, and
is injective on `S` when `S` is convex, uniformly for `c` close enough to `1`. -/
theorem collar_correction_estimate {sd : ℂ → ℝ} {η : ℝ → ℝ} {S : Set ℂ}
    (hS : IsCompact S) (hSim : S ⊆ {z : ℂ | 0 < z.im}) (hSconv : Convex ℝ S)
    (hsd : ContDiffOn ℝ 1 sd {z : ℂ | 0 < z.im})
    (hη : ContDiff ℝ 1 η) (hη01 : ∀ t : ℝ, η t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ c : Matrix (Fin 2) (Fin 2) ℝ, c.det = 1 → entrywiseDist c 1 ≤ c₀ →
        (∀ z ∈ S,
          DifferentiableAt ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) z ∧
          ‖dzbar (fun w => matMoebius (correctionPath c (η (sd w))) w) z‖
            ≤ C * entrywiseDist c 1 *
              ‖dz (fun w => matMoebius (correctionPath c (η (sd w))) w) z‖) ∧
        Set.InjOn (fun w => matMoebius (correctionPath c (η (sd w))) w) S := by
  obtain ⟨c₀', C', hc₀'pos, hC'pos, hbnd⟩ := correctionPath_bounds
  haveI hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have huu : ContDiffOn ℝ 1 (fun w => η (sd w)) {z : ℂ | 0 < z.im} := hη.comp_contDiffOn hsd
  have hfdcont : ContinuousOn (fderiv ℝ (fun w => η (sd w))) {z : ℂ | 0 < z.im} :=
    huu.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn (hfdcont.mono hSim)
  obtain ⟨R₀, hR₀⟩ := hS.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨M, hM_def⟩ : ∃ x : ℝ, max M₀ 1 = x := ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ x : ℝ, max R₀ 1 = x := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := by rw [← hM_def]; exact le_max_right _ _
  have hR1 : (1 : ℝ) ≤ R := by rw [← hR_def]; exact le_max_right _ _
  have hMb : ∀ z ∈ S, ‖fderiv ℝ (fun w => η (sd w)) z‖ ≤ M := by
    intro z hz
    rw [← hM_def]
    exact le_trans (hM₀ z hz) (le_max_left _ _)
  have hRb : ∀ z ∈ S, ‖z‖ ≤ R := by
    intro z hz
    rw [← hR_def]
    exact le_trans (hR₀ z hz) (le_max_left _ _)
  have hGpos : (0 : ℝ) < 10 + 4 * (R + 3) * M := by
    have h1 : (0 : ℝ) < 4 * (R + 3) * M :=
      mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    linarith
  have hPpos : (0 : ℝ) < C' * (R + 1) := mul_pos hC'pos (by linarith)
  have h9pos : (0 : ℝ) < 9 * (10 + 4 * (R + 3) * M) * (C' * (R + 1)) :=
    mul_pos (mul_pos (by norm_num) hGpos) hPpos
  refine ⟨min c₀' (1 / (9 * (10 + 4 * (R + 3) * M) * (C' * (R + 1)))),
    3 * (4 * C' * (R + 1) * (R + 3)) * M + 1, lt_min hc₀'pos (one_div_pos.mpr h9pos), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 3 * (4 * C' * (R + 1) * (R + 3)) * M :=
      mul_pos (mul_pos (by norm_num)
        (mul_pos (mul_pos (mul_pos (by norm_num) hC'pos) (by linarith)) (by linarith)))
        (by linarith)
    linarith
  intro c hcdet hc
  have hdc₀' : entrywiseDist c 1 ≤ c₀' := le_trans hc (min_le_left _ _)
  have hdd0 : 0 ≤ entrywiseDist c 1 := by
    have h : |c 0 0 - (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0| ≤ entrywiseDist c 1 := by
      unfold entrywiseDist
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact le_trans (abs_nonneg _) h
  have hmaster : 9 * ((10 + 4 * (R + 3) * M) * (C' * (R + 1) * entrywiseDist c 1)) ≤ 1 := by
    have h2 := le_trans hc (min_le_right _ _)
    rw [le_div_iff₀ h9pos] at h2
    linarith [h2]
  obtain ⟨ee, hee⟩ : ∃ x : ℝ, C' * (R + 1) * entrywiseDist c 1 = x := ⟨_, rfl⟩
  obtain ⟨e1, he1⟩ : ∃ x : ℝ, C' * entrywiseDist c 1 = x := ⟨_, rfl⟩
  obtain ⟨GG, hGG⟩ : ∃ x : ℝ, 10 + 4 * (R + 3) * M = x := ⟨_, rfl⟩
  rw [hee, hGG] at hmaster
  have he0 : 0 ≤ ee := by rw [← hee]; exact mul_nonneg hPpos.le hdd0
  have he10 : 0 ≤ e1 := by rw [← he1]; exact mul_nonneg hC'pos.le hdd0
  have heee : e1 * (R + 1) = ee := by rw [← hee, ← he1]; ring
  have hGG10 : 10 ≤ GG := by
    rw [← hGG]
    have h1 : (0 : ℝ) ≤ 4 * (R + 3) * M :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    linarith
  have hGGe : 0 ≤ (GG - 10) * ee := mul_nonneg (by linarith) he0
  have hsm1a : ee ≤ 1 / 90 := by linarith [hmaster, hGGe]
  have hsm2a : (GG - 10) * ee ≤ 1 / 9 := by linarith [hmaster, he0]
  have hsm2b : 4 * ee * (R + 3) * M ≤ 1 / 9 := by
    rw [← hGG] at hsm2a
    linarith [hsm2a]
  -- ==== the per-point derivative package ====
  have key : ∀ z ∈ S,
      DifferentiableAt ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) z ∧
      ∃ Sw Su : ℂ,
        (∀ v : ℂ, fderiv ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) z v
          = Sw * v + Su * ((fderiv ℝ (fun w => η (sd w)) z) v : ℂ)) ∧
        ‖Sw - 1‖ ≤ 10 * ee ∧ ‖Su‖ ≤ 4 * ee * (R + 3) ∧ (4 / 9 : ℝ) ≤ ‖Sw‖ := by
    intro z hz
    have hzU : z ∈ {z : ℂ | 0 < z.im} := hSim hz
    obtain ⟨hDpos, hdet1, hdist, hderivs⟩ := hbnd c hdc₀' (η (sd z)) (hη01 (sd z))
    have hex : ∀ i j : Fin 2, |correctionPath c (η (sd z)) i j
        - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ e1 := by
      intro i j
      rw [← he1]
      refine le_trans ?_ hdist
      unfold entrywiseDist
      fin_cases i <;> fin_cases j
      · exact le_trans (le_max_left _ _) (le_max_left _ _)
      · exact le_trans (le_max_right _ _) (le_max_left _ _)
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hcd : ContDiffAt ℝ 1 (fun w => η (sd w)) z := huu.contDiffAt (hU.mem_nhds hzU)
    have hdiffuu : DifferentiableAt ℝ (fun w => η (sd w)) z :=
      hcd.differentiableAt one_ne_zero
    obtain ⟨Du, hDu_def⟩ : ∃ D : ℂ →L[ℝ] ℝ, fderiv ℝ (fun w => η (sd w)) z = D := ⟨_, rfl⟩
    have hDu : HasFDerivAt (fun w => η (sd w)) Du z := by
      rw [← hDu_def]; exact hdiffuu.hasFDerivAt
    obtain ⟨p00, hp00⟩ : ∃ x : ℝ, correctionPath c (η (sd z)) 0 0 = x := ⟨_, rfl⟩
    obtain ⟨p01, hp01⟩ : ∃ x : ℝ, correctionPath c (η (sd z)) 0 1 = x := ⟨_, rfl⟩
    obtain ⟨p10, hp10⟩ : ∃ x : ℝ, correctionPath c (η (sd z)) 1 0 = x := ⟨_, rfl⟩
    obtain ⟨p11, hp11⟩ : ∃ x : ℝ, correctionPath c (η (sd z)) 1 1 = x := ⟨_, rfl⟩
    obtain ⟨r00, hr00⟩ : ∃ x : ℝ,
      deriv (fun v : ℝ => correctionPath c v 0 0) (η (sd z)) = x := ⟨_, rfl⟩
    obtain ⟨r01, hr01⟩ : ∃ x : ℝ,
      deriv (fun v : ℝ => correctionPath c v 0 1) (η (sd z)) = x := ⟨_, rfl⟩
    obtain ⟨r10, hr10⟩ : ∃ x : ℝ,
      deriv (fun v : ℝ => correctionPath c v 1 0) (η (sd z)) = x := ⟨_, rfl⟩
    obtain ⟨r11, hr11⟩ : ∃ x : ℝ,
      deriv (fun v : ℝ => correctionPath c v 1 1) (η (sd z)) = x := ⟨_, rfl⟩
    have hb00 : |p00 - 1| ≤ e1 := by
      have h := hex 0 0
      rwa [Matrix.one_apply_eq, hp00] at h
    have hb01 : |p01| ≤ e1 := by
      have h := hex 0 1
      rwa [Matrix.one_apply_ne (by decide), sub_zero, hp01] at h
    have hb10 : |p10| ≤ e1 := by
      have h := hex 1 0
      rwa [Matrix.one_apply_ne (by decide), sub_zero, hp10] at h
    have hb11 : |p11 - 1| ≤ e1 := by
      have h := hex 1 1
      rwa [Matrix.one_apply_eq, hp11] at h
    have hq00 : HasDerivAt (fun v : ℝ => correctionPath c v 0 0) r00 (η (sd z)) := by
      have h := (hderivs 0 0).1
      rwa [hr00] at h
    have hq01 : HasDerivAt (fun v : ℝ => correctionPath c v 0 1) r01 (η (sd z)) := by
      have h := (hderivs 0 1).1
      rwa [hr01] at h
    have hq10 : HasDerivAt (fun v : ℝ => correctionPath c v 1 0) r10 (η (sd z)) := by
      have h := (hderivs 1 0).1
      rwa [hr10] at h
    have hq11 : HasDerivAt (fun v : ℝ => correctionPath c v 1 1) r11 (η (sd z)) := by
      have h := (hderivs 1 1).1
      rwa [hr11] at h
    have hr00b : |r00| ≤ e1 := by
      have h := (hderivs 0 0).2
      rwa [hr00, he1] at h
    have hr01b : |r01| ≤ e1 := by
      have h := (hderivs 0 1).2
      rwa [hr01, he1] at h
    have hr10b : |r10| ≤ e1 := by
      have h := (hderivs 1 0).2
      rwa [hr10, he1] at h
    have hr11b : |r11| ≤ e1 := by
      have h := (hderivs 1 1).2
      rwa [hr11, he1] at h
    have hdetC : (p00 : ℂ) * (p11 : ℂ) - (p01 : ℂ) * (p10 : ℂ) = 1 := by
      have h := hdet1 hcdet
      rw [Matrix.det_fin_two, hp00, hp01, hp10, hp11] at h
      have h2 := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at h2
      exact h2
    have hzR : ‖z‖ ≤ R := hRb z hz
    have hDD1 : ‖((p10 : ℂ) * z + (p11 : ℂ)) - 1‖ ≤ ee := by
      have hrw : ((p10 : ℂ) * z + (p11 : ℂ)) - 1 = (p10 : ℂ) * z + ((p11 - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hrw]
      calc ‖(p10 : ℂ) * z + ((p11 - 1 : ℝ) : ℂ)‖
          ≤ ‖(p10 : ℂ) * z‖ + ‖((p11 - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |p10| * ‖z‖ + |p11 - 1| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ e1 * R + e1 := by
            have h1 : |p10| * ‖z‖ ≤ e1 * R := mul_le_mul hb10 hzR (norm_nonneg z) he10
            linarith [hb11]
        _ ≤ ee := by linarith [heee]
    have hDDlb : (1 : ℝ) / 2 ≤ ‖(p10 : ℂ) * z + (p11 : ℂ)‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) ((p10 : ℂ) * z + (p11 : ℂ))
      rw [norm_one, norm_sub_rev] at h1
      linarith [hDD1, hsm1a]
    have hDDub : ‖(p10 : ℂ) * z + (p11 : ℂ)‖ ≤ 3 / 2 := by
      have h0 : (((p10 : ℂ) * z + (p11 : ℂ)) - 1) + 1 = (p10 : ℂ) * z + (p11 : ℂ) := by ring
      have h1 := norm_add_le (((p10 : ℂ) * z + (p11 : ℂ)) - 1) (1 : ℂ)
      rw [h0, norm_one] at h1
      linarith [hDD1, hsm1a]
    have hDDne : ((p10 : ℂ) * z + (p11 : ℂ)) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hDDlb
      linarith
    have hDDne' : ((correctionPath c (η (sd z)) 1 0 : ℝ) : ℂ) * z
        + ((correctionPath c (η (sd z)) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hp10, hp11]
      exact hDDne
    have hfeq : (fun w => matMoebius (correctionPath c (η (sd w))) w)
        = fun w => (((correctionPath c (η (sd w)) 0 0 : ℝ) : ℂ) * w
            + ((correctionPath c (η (sd w)) 0 1 : ℝ) : ℂ))
          * (((correctionPath c (η (sd w)) 1 0 : ℝ) : ℂ) * w
            + ((correctionPath c (η (sd w)) 1 1 : ℝ) : ℂ))⁻¹ := by
      funext w
      rw [matMoebius, div_eq_mul_inv]
    have hchain := (((Complex.ofRealCLM.hasFDerivAt.comp z
        (hq00.comp_hasFDerivAt z hDu)).mul (hasFDerivAt_id z)).add
        (Complex.ofRealCLM.hasFDerivAt.comp z (hq01.comp_hasFDerivAt z hDu))).mul
      ((hasDerivAt_inv hDDne').comp_hasFDerivAt z
        (((Complex.ofRealCLM.hasFDerivAt.comp z
            (hq10.comp_hasFDerivAt z hDu)).mul (hasFDerivAt_id z)).add
          (Complex.ofRealCLM.hasFDerivAt.comp z (hq11.comp_hasFDerivAt z hDu))))
    have hφe : HasFDerivAt (fun w => (((correctionPath c (η (sd w)) 0 0 : ℝ) : ℂ) * w
          + ((correctionPath c (η (sd w)) 0 1 : ℝ) : ℂ))
        * (((correctionPath c (η (sd w)) 1 0 : ℝ) : ℂ) * w
          + ((correctionPath c (η (sd w)) 1 1 : ℝ) : ℂ))⁻¹) _ z := hchain
    have hdiff : DifferentiableAt ℝ
        (fun w => matMoebius (correctionPath c (η (sd w))) w) z := by
      rw [hfeq]
      exact hφe.differentiableAt
    have hfd0 : fderiv ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) z
        = fderiv ℝ (fun w => (((correctionPath c (η (sd w)) 0 0 : ℝ) : ℂ) * w
            + ((correctionPath c (η (sd w)) 0 1 : ℝ) : ℂ))
          * (((correctionPath c (η (sd w)) 1 0 : ℝ) : ℂ) * w
            + ((correctionPath c (η (sd w)) 1 1 : ℝ) : ℂ))⁻¹) z := by
      rw [hfeq]
    have hφex : HasFDerivAt (fun w => (((correctionPath c (η (sd w)) 0 0 : ℝ) : ℂ) * w
          + ((correctionPath c (η (sd w)) 0 1 : ℝ) : ℂ))
        * (((correctionPath c (η (sd w)) 1 0 : ℝ) : ℂ) * w
          + ((correctionPath c (η (sd w)) 1 1 : ℝ) : ℂ))⁻¹)
        ((((correctionPath c (η (sd z)) 0 0 : ℝ) : ℂ) * z
            + ((correctionPath c (η (sd z)) 0 1 : ℝ) : ℂ))
          • ((-((((correctionPath c (η (sd z)) 1 0 : ℝ) : ℂ) * z
              + ((correctionPath c (η (sd z)) 1 1 : ℝ) : ℂ)) ^ 2)⁻¹)
            • (((correctionPath c (η (sd z)) 1 0 : ℝ) : ℂ) • ContinuousLinearMap.id ℝ ℂ
              + z • Complex.ofRealCLM.comp (r10 • Du)
              + Complex.ofRealCLM.comp (r11 • Du)))
        + ((((correctionPath c (η (sd z)) 1 0 : ℝ) : ℂ) * z
            + ((correctionPath c (η (sd z)) 1 1 : ℝ) : ℂ))⁻¹
          • (((correctionPath c (η (sd z)) 0 0 : ℝ) : ℂ) • ContinuousLinearMap.id ℝ ℂ
            + z • Complex.ofRealCLM.comp (r00 • Du)
            + Complex.ofRealCLM.comp (r01 • Du)))) z := hchain
    have hfd1 := hφex.differentiableAt.hasFDerivAt.unique hφex
    have hsqpos : (0 : ℝ) < ‖(p10 : ℂ) * z + (p11 : ℂ)‖ ^ 2 :=
      pow_pos (lt_of_lt_of_le (by norm_num) hDDlb) 2
    refine ⟨hdiff,
      ((p00 : ℂ) * (p11 : ℂ) - (p01 : ℂ) * (p10 : ℂ)) / ((p10 : ℂ) * z + (p11 : ℂ)) ^ 2,
      (((r00 : ℂ) * z + (r01 : ℂ)) * ((p10 : ℂ) * z + (p11 : ℂ))
        - ((p00 : ℂ) * z + (p01 : ℂ)) * ((r10 : ℂ) * z + (r11 : ℂ)))
        / ((p10 : ℂ) * z + (p11 : ℂ)) ^ 2, ?_, ?_, ?_, ?_⟩
    · intro v
      rw [hfd0, hfd1, hDu_def, hp00, hp01, hp10, hp11]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        Complex.ofRealCLM_apply, smul_eq_mul]
      push_cast
      field_simp
      ring
    · have hSw1 : ((p00 : ℂ) * (p11 : ℂ) - (p01 : ℂ) * (p10 : ℂ))
          / ((p10 : ℂ) * z + (p11 : ℂ)) ^ 2 - 1
          = ((1 - ((p10 : ℂ) * z + (p11 : ℂ))) * (1 + ((p10 : ℂ) * z + (p11 : ℂ))))
            / ((p10 : ℂ) * z + (p11 : ℂ)) ^ 2 := by
        rw [hdetC]
        field_simp
        ring
      rw [hSw1, norm_div, norm_mul, norm_pow, div_le_iff₀ hsqpos]
      have h1p : ‖(1 : ℂ) + ((p10 : ℂ) * z + (p11 : ℂ))‖ ≤ 5 / 2 := by
        have h := norm_add_le (1 : ℂ) ((p10 : ℂ) * z + (p11 : ℂ))
        rw [norm_one] at h
        linarith [hDDub]
      have h1m : ‖(1 : ℂ) - ((p10 : ℂ) * z + (p11 : ℂ))‖ ≤ ee := by
        rw [norm_sub_rev]
        exact hDD1
      have hprod : ‖(1 : ℂ) - ((p10 : ℂ) * z + (p11 : ℂ))‖
            * ‖(1 : ℂ) + ((p10 : ℂ) * z + (p11 : ℂ))‖ ≤ ee * (5 / 2) :=
        mul_le_mul h1m h1p (norm_nonneg _) he0
      have hq : (1 : ℝ) / 4 ≤ ‖(p10 : ℂ) * z + (p11 : ℂ)‖ ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hDDlb 2
        norm_num at h
        linarith [h]
      have hRHS : 10 * ee * (1 / 4) ≤ 10 * ee * ‖(p10 : ℂ) * z + (p11 : ℂ)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      linarith [hprod, hRHS]
    · rw [norm_div, norm_pow, div_le_iff₀ hsqpos]
      have hra : ‖(r00 : ℂ) * z + (r01 : ℂ)‖ ≤ ee := by
        calc ‖(r00 : ℂ) * z + (r01 : ℂ)‖ ≤ ‖(r00 : ℂ) * z‖ + ‖((r01 : ℝ) : ℂ)‖ :=
              norm_add_le _ _
          _ = |r00| * ‖z‖ + |r01| := by
              rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
          _ ≤ e1 * R + e1 := by
              have h1 : |r00| * ‖z‖ ≤ e1 * R := mul_le_mul hr00b hzR (norm_nonneg z) he10
              linarith [hr01b]
          _ ≤ ee := by linarith [heee]
      have hrb : ‖(r10 : ℂ) * z + (r11 : ℂ)‖ ≤ ee := by
        calc ‖(r10 : ℂ) * z + (r11 : ℂ)‖ ≤ ‖(r10 : ℂ) * z‖ + ‖((r11 : ℝ) : ℂ)‖ :=
              norm_add_le _ _
          _ = |r10| * ‖z‖ + |r11| := by
              rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
          _ ≤ e1 * R + e1 := by
              have h1 : |r10| * ‖z‖ ≤ e1 * R := mul_le_mul hr10b hzR (norm_nonneg z) he10
              linarith [hr11b]
          _ ≤ ee := by linarith [heee]
      have hp00abs : |p00| ≤ 1 + e1 := by
        have h := abs_add_le (p00 - 1) 1
        have h0 : p00 - 1 + 1 = p00 := by ring
        rw [h0, abs_one] at h
        linarith [hb00]
      have hNNb : ‖(p00 : ℂ) * z + (p01 : ℂ)‖ ≤ R + 1 := by
        calc ‖(p00 : ℂ) * z + (p01 : ℂ)‖ ≤ ‖(p00 : ℂ) * z‖ + ‖((p01 : ℝ) : ℂ)‖ :=
              norm_add_le _ _
          _ = |p00| * ‖z‖ + |p01| := by
              rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
                Real.norm_eq_abs]
          _ ≤ (1 + e1) * R + e1 := by
              have h1 : |p00| * ‖z‖ ≤ (1 + e1) * R :=
                mul_le_mul hp00abs hzR (norm_nonneg z) (by linarith)
              linarith [hb01]
          _ ≤ R + 1 := by linarith [heee, hsm1a]
      have hnum : ‖((r00 : ℂ) * z + (r01 : ℂ)) * ((p10 : ℂ) * z + (p11 : ℂ))
            - ((p00 : ℂ) * z + (p01 : ℂ)) * ((r10 : ℂ) * z + (r11 : ℂ))‖
          ≤ ee * (3 / 2) + (R + 1) * ee := by
        have h1 := norm_sub_le (((r00 : ℂ) * z + (r01 : ℂ)) * ((p10 : ℂ) * z + (p11 : ℂ)))
          (((p00 : ℂ) * z + (p01 : ℂ)) * ((r10 : ℂ) * z + (r11 : ℂ)))
        rw [norm_mul, norm_mul] at h1
        have h2 : ‖(r00 : ℂ) * z + (r01 : ℂ)‖ * ‖(p10 : ℂ) * z + (p11 : ℂ)‖
            ≤ ee * (3 / 2) := mul_le_mul hra hDDub (norm_nonneg _) he0
        have h3 : ‖(p00 : ℂ) * z + (p01 : ℂ)‖ * ‖(r10 : ℂ) * z + (r11 : ℂ)‖
            ≤ (R + 1) * ee := mul_le_mul hNNb hrb (norm_nonneg _) (by linarith)
        linarith
      have hq : (1 : ℝ) / 4 ≤ ‖(p10 : ℂ) * z + (p11 : ℂ)‖ ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hDDlb 2
        norm_num at h
        linarith [h]
      have hRHS : 4 * ee * (R + 3) * (1 / 4)
          ≤ 4 * ee * (R + 3) * ‖(p10 : ℂ) * z + (p11 : ℂ)‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left hq ?_
        have h4 : (0 : ℝ) ≤ 4 * ee * (R + 3) :=
          mul_nonneg (mul_nonneg (by norm_num) he0) (by linarith)
        linarith
      linarith [hnum, hRHS, he0]
    · rw [hdetC, norm_div, norm_one, norm_pow, le_div_iff₀ hsqpos]
      have h := pow_le_pow_left₀ (norm_nonneg ((p10 : ℂ) * z + (p11 : ℂ))) hDDub 2
      norm_num at h
      linarith [h]
  -- ==== part (a) and injectivity from the package ====
  constructor
  · intro z hz
    obtain ⟨hdiff, Sw, Su, hLv, hSw1b, hSub, hSwlb⟩ := key z hz
    refine ⟨hdiff, ?_⟩
    have hα := hLv 1
    have hβ := hLv Complex.I
    have hdzbar : dzbar (fun w => matMoebius (correctionPath c (η (sd w))) w) z
        = (1 / 2 : ℂ) * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
          + Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ))) := by
      rw [dzbar, hα, hβ]
      linear_combination (Sw / 2) * Complex.I_mul_I
    have hdz : dz (fun w => matMoebius (correctionPath c (η (sd w))) w) z
        = Sw + (1 / 2 : ℂ) * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
          - Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ))) := by
      rw [dz, hα, hβ]
      linear_combination (-(Sw / 2)) * Complex.I_mul_I
    have hX1 : ‖(((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
      have h := (fderiv ℝ (fun w => η (sd w)) z).le_opNorm 1
      rw [norm_one, mul_one] at h
      exact le_trans h (hMb z hz)
    have hXI : ‖(((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
      have h := (fderiv ℝ (fun w => η (sd w)) z).le_opNorm Complex.I
      rw [Complex.norm_I, mul_one] at h
      exact le_trans h (hMb z hz)
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    have hplus : ‖(((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ)
        + Complex.I * (((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ)‖ ≤ 2 * M := by
      have h := norm_add_le ((((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ))
        (Complex.I * (((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ))
      rw [norm_mul, Complex.norm_I, one_mul] at h
      linarith [hX1, hXI]
    have hminus : ‖(((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ)
        - Complex.I * (((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ)‖ ≤ 2 * M := by
      have h := norm_sub_le ((((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ))
        (Complex.I * (((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ))
      rw [norm_mul, Complex.norm_I, one_mul] at h
      linarith [hX1, hXI]
    have hnb : ‖dzbar (fun w => matMoebius (correctionPath c (η (sd w))) w) z‖
        ≤ ‖Su‖ * M := by
      rw [hdzbar, norm_mul, norm_mul, hhalf]
      have h1 : ‖Su‖ * ‖(((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ)
          + Complex.I * (((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ)‖
          ≤ ‖Su‖ * (2 * M) := mul_le_mul_of_nonneg_left hplus (norm_nonneg Su)
      linarith [h1]
    have hSub' : ‖Su‖ * M ≤ 4 * ee * (R + 3) * M :=
      mul_le_mul_of_nonneg_right hSub (by linarith)
    have hSuM : ‖Su‖ * M ≤ 1 / 9 := by linarith [hSub', hsm2b]
    have hdzlb : (1 / 3 : ℝ)
        ≤ ‖dz (fun w => matMoebius (correctionPath c (η (sd w))) w) z‖ := by
      rw [hdz]
      have hT : ‖(1 / 2 : ℂ) * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
          - Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ)))‖
          ≤ ‖Su‖ * M := by
        rw [norm_mul, norm_mul, hhalf]
        have h1 : ‖Su‖ * ‖(((fderiv ℝ (fun w => η (sd w)) z) 1 : ℝ) : ℂ)
            - Complex.I * (((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℝ) : ℂ)‖
            ≤ ‖Su‖ * (2 * M) := mul_le_mul_of_nonneg_left hminus (norm_nonneg Su)
        linarith [h1]
      have h0 : Sw + (1 / 2 : ℂ) * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
            - Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ)))
            - (1 / 2 : ℂ) * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
            - Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ))) = Sw := by
        ring
      have h := norm_sub_le (Sw + (1 / 2 : ℂ)
        * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
          - Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ))))
        ((1 / 2 : ℂ) * (Su * (((fderiv ℝ (fun w => η (sd w)) z) 1 : ℂ)
          - Complex.I * ((fderiv ℝ (fun w => η (sd w)) z) Complex.I : ℂ))))
      rw [h0] at h
      linarith [hSwlb, hT, hSuM]
    have hCd : (3 * (4 * C' * (R + 1) * (R + 3)) * M + 1) * entrywiseDist c 1
        = 12 * ee * (R + 3) * M + entrywiseDist c 1 := by
      rw [← hee]
      ring
    rw [hCd]
    have hnn : (0 : ℝ) ≤ 12 * ee * (R + 3) * M :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) he0) (by linarith)) (by linarith)
    have hchain2 : (12 * ee * (R + 3) * M + entrywiseDist c 1) * (1 / 3)
        ≤ (12 * ee * (R + 3) * M + entrywiseDist c 1)
          * ‖dz (fun w => matMoebius (correctionPath c (η (sd w))) w) z‖ :=
      mul_le_mul_of_nonneg_left hdzlb (by linarith)
    linarith [hnb, hSub', hchain2, hdd0]
  · intro a ha b hb hab
    have hbound : ∀ x ∈ S,
        ‖fderiv ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) x
          - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2 := by
      intro x hx
      obtain ⟨hdiff, Sw, Su, hLv, hSw1b, hSub, hSwlb⟩ := key x hx
      refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
      intro v
      have hev : (fderiv ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) x
          - ContinuousLinearMap.id ℝ ℂ) v
          = (Sw - 1) * v + Su * ((fderiv ℝ (fun w => η (sd w)) x) v : ℂ) := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hLv v]
        ring
      rw [hev]
      have h1 := norm_add_le ((Sw - 1) * v)
        (Su * (((fderiv ℝ (fun w => η (sd w)) x) v : ℝ) : ℂ))
      rw [norm_mul, norm_mul] at h1
      have hXv : ‖(((fderiv ℝ (fun w => η (sd w)) x) v : ℝ) : ℂ)‖ ≤ M * ‖v‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
        have h := (fderiv ℝ (fun w => η (sd w)) x).le_opNorm v
        have h2 : ‖fderiv ℝ (fun w => η (sd w)) x‖ * ‖v‖ ≤ M * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hMb x hx) (norm_nonneg v)
        linarith
      have h2 : ‖Sw - 1‖ * ‖v‖ ≤ 10 * ee * ‖v‖ :=
        mul_le_mul_of_nonneg_right hSw1b (norm_nonneg v)
      have h3 : ‖Su‖ * ‖(((fderiv ℝ (fun w => η (sd w)) x) v : ℝ) : ℂ)‖
          ≤ 4 * ee * (R + 3) * (M * ‖v‖) := by
        refine mul_le_mul hSub hXv (norm_nonneg _) ?_
        exact mul_nonneg (mul_nonneg (by norm_num) he0) (by linarith)
      have h5 : 10 * ee + 4 * ee * (R + 3) * M ≤ 1 / 2 := by
        linarith [hsm1a, hsm2b]
      have h6 := mul_le_mul_of_nonneg_right h5 (norm_nonneg v)
      linarith [h1, h2, h3, h6]
    have hmean : ‖((fun w => matMoebius (correctionPath c (η (sd w))) w) b - b)
        - ((fun w => matMoebius (correctionPath c (η (sd w))) w) a - a)‖
        ≤ 1 / 2 * ‖b - a‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun w => matMoebius (correctionPath c (η (sd w))) w - w)
        (f' := fun x => fderiv ℝ (fun w => matMoebius (correctionPath c (η (sd w))) w) x
          - ContinuousLinearMap.id ℝ ℂ) (fun x hx => ?_) (fun x hx => hbound x hx)
        hSconv ha hb
      have hdiff := (key x hx).1
      exact ((hdiff.hasFDerivAt).sub (hasFDerivAt_id x)).hasFDerivWithinAt
    have h3 : ((fun w => matMoebius (correctionPath c (η (sd w))) w) b - b)
        - ((fun w => matMoebius (correctionPath c (η (sd w))) w) a - a) = a - b := by
      have hab' : (fun w => matMoebius (correctionPath c (η (sd w))) w) a
          = (fun w => matMoebius (correctionPath c (η (sd w))) w) b := hab
      rw [← hab']
      ring
    rw [h3, norm_sub_rev b a] at hmean
    have h4 : ‖a - b‖ ≤ 0 := by linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h4)

/-! ## The development of the corrected tile maps -/

/-! Auxiliary lemmas for the development of the corrected tile maps. -/

/-- Euclidean-disc characterization of hyperbolic balls. -/
private lemma zz_ball (w : UpperHalfPlane) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    z ∈ Metric.ball ((((w : ℂ).re : ℝ) : ℂ) + ((w.im * Real.cosh r : ℝ) : ℂ) * Complex.I)
      (w.im * Real.sinh r) ↔
    ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) w < r := by
  have hwim : 0 < w.im := w.im_pos
  have hsinh : 0 < Real.sinh r := by positivity
  have hch : Real.cosh r ^ 2 - Real.sinh r ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq r
  have hcosh1 : 1 < Real.cosh r := by
    nlinarith [hsinh, Real.cosh_pos r]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ,
      c = (((w : ℂ).re : ℝ) : ℂ) + ((w.im * Real.cosh r : ℝ) : ℂ) * Complex.I := ⟨_, rfl⟩
  have hcre : c.re = (w : ℂ).re := by
    rw [hcdef]
    simp [Complex.add_re, Complex.mul_re]
  have hcim : c.im = w.im * Real.cosh r := by
    rw [hcdef]
    simp [Complex.add_im, Complex.mul_im]
  have hnormsq : ∀ u v : ℂ, dist u v ^ 2 = (u.re - v.re) ^ 2 + (u.im - v.im) ^ 2 := by
    intro u v
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  -- membership in the euclidean ball as an inequality of squares
  have hmem_iff : z ∈ Metric.ball c (w.im * Real.sinh r) ↔
      (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im * Real.cosh r) ^ 2
        < (w.im * Real.sinh r) ^ 2 := by
    rw [Metric.mem_ball]
    constructor
    · intro h
      have h2 : dist z c ^ 2 < (w.im * Real.sinh r) ^ 2 := by
        have hd0 : 0 ≤ dist z c := dist_nonneg
        nlinarith [h]
      rw [hnormsq z c, hcre, hcim] at h2
      exact h2
    · intro h
      have h2 : dist z c ^ 2 < (w.im * Real.sinh r) ^ 2 := by
        rw [hnormsq z c, hcre, hcim]
        exact h
      have hd0 : 0 ≤ dist z c := dist_nonneg
      have hrp : 0 < w.im * Real.sinh r := mul_pos hwim hsinh
      nlinarith [h2]
  rw [← hcdef, hmem_iff]
  constructor
  · intro h
    -- positivity of the imaginary part
    have him2 : (z.im - w.im * Real.cosh r) ^ 2 < (w.im * Real.sinh r) ^ 2 := by
      nlinarith [sq_nonneg (z.re - (w : ℂ).re)]
    have hzim : 0 < z.im := by
      by_contra hcon
      push Not at hcon
      have hwc : (w.im * Real.cosh r) ^ 2 - (w.im * Real.sinh r) ^ 2 = w.im ^ 2 := by
        linear_combination w.im ^ 2 * hch
      have h1 : 0 ≤ -z.im * (w.im * Real.cosh r) := by
        refine mul_nonneg (by linarith) ?_
        positivity
      nlinarith [him2, hwc, h1, sq_nonneg z.im, sq_nonneg w.im, hwim]
    refine ⟨hzim, ?_⟩
    -- convert to the cosh comparison
    have hcd := UpperHalfPlane.cosh_dist (⟨z, hzim⟩ : UpperHalfPlane) w
    have him_eq : ((⟨z, hzim⟩ : UpperHalfPlane) : ℂ) = z := rfl
    have himz : (⟨z, hzim⟩ : UpperHalfPlane).im = z.im := rfl
    rw [him_eq, himz] at hcd
    have hdd : dist (z : ℂ) (w : ℂ) ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [hnormsq]
      simp [UpperHalfPlane.coe_im]
    have hden : 0 < 2 * z.im * w.im := by positivity
    have hkey : Real.cosh (dist (⟨z, hzim⟩ : UpperHalfPlane) w) < Real.cosh r := by
      rw [hcd, hdd]
      have hlt : (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2
          < (Real.cosh r - 1) * (2 * z.im * w.im) := by
        nlinarith [h, hch, sq_nonneg w.im]
      have h2 := (div_lt_iff₀ hden).mpr hlt
      linarith
    have h3 := Real.cosh_lt_cosh.mp hkey
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hr.le] at h3
  · rintro ⟨hz, h⟩
    have hcd := UpperHalfPlane.cosh_dist (⟨z, hz⟩ : UpperHalfPlane) w
    have him_eq : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
    have himz : (⟨z, hz⟩ : UpperHalfPlane).im = z.im := rfl
    rw [him_eq, himz] at hcd
    have hkey : Real.cosh (dist (⟨z, hz⟩ : UpperHalfPlane) w) < Real.cosh r :=
      Real.cosh_lt_cosh.mpr (by rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg hr.le])
    rw [hcd] at hkey
    have hdd : dist (z : ℂ) (w : ℂ) ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [hnormsq]
      simp [UpperHalfPlane.coe_im]
    rw [hdd] at hkey
    have hden : 0 < 2 * z.im * w.im := by positivity
    have hkey2 : (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2
        < (Real.cosh r - 1) * (2 * z.im * w.im) := by
      have h2 : ((z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2) / (2 * z.im * w.im)
          < Real.cosh r - 1 := by linarith
      exact (div_lt_iff₀ hden).mp h2
    nlinarith [hkey2, hch, sq_nonneg w.im]

/-- Packing finiteness for a Fuchsian group. -/
private lemma zz_fin {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) (τ τ₀ : UpperHalfPlane) (r : ℝ) :
    {γ : ↥Γ | dist τ (γ • τ₀) ≤ r}.Finite := by
  classical
  haveI hPD : ProperlyDiscontinuousSMul Γ UpperHalfPlane := hΓ
  have hfin1 : {γ : ↥Γ | ((fun x => γ • x) '' {τ₀} ∩
      Metric.closedBall τ r).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image isCompact_singleton
      (isCompact_closedBall _ _)
  refine hfin1.subset ?_
  intro γ hγ
  refine ⟨γ • τ₀, ⟨τ₀, rfl, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact hγ

/-- General composition law for matrix Möbius maps, with denominator hypotheses. -/
private lemma zz_matmul (M N : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hN : (N 1 0 : ℂ) * z + (N 1 1 : ℂ) ≠ 0)
    (_hMN : ((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ) ≠ 0) :
    matMoebius (M * N) z = matMoebius M (matMoebius N z) := by
  have hnum : ∀ i : Fin 2, ((M * N) i 0 : ℂ) * z + ((M * N) i 1 : ℂ)
      = (M i 0 : ℂ) * ((N 0 0 : ℂ) * z + (N 0 1 : ℂ))
        + (M i 1 : ℂ) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ)) := by
    intro i
    have h0 : (M * N) i 0 = M i 0 * N 0 0 + M i 1 * N 1 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : (M * N) i 1 = M i 0 * N 0 1 + M i 1 * N 1 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h0, h1]
    push_cast
    ring
  have hu : matMoebius N z * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = (N 0 0 : ℂ) * z + (N 0 1 : ℂ) := by
    rw [matMoebius, div_mul_cancel₀ _ hN]
  have hd : ((M 1 0 : ℂ) * matMoebius N z + (M 1 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = ((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ) := by
    rw [hnum 1, add_mul, mul_assoc, hu]
  have hn : ((M 0 0 : ℂ) * matMoebius N z + (M 0 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = ((M * N) 0 0 : ℂ) * z + ((M * N) 0 1 : ℂ) := by
    rw [hnum 0, add_mul, mul_assoc, hu]
  calc matMoebius (M * N) z
      = (((M * N) 0 0 : ℂ) * z + ((M * N) 0 1 : ℂ))
        / (((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ)) := rfl
    _ = (((M 0 0 : ℂ) * matMoebius N z + (M 0 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ)))
        / (((M 1 0 : ℂ) * matMoebius N z + (M 1 1 : ℂ)) * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))) := by
        rw [hn, hd]
    _ = matMoebius M (matMoebius N z) := by
        rw [mul_div_mul_right _ _ hN]
        rfl

/-- The cosh-distance formula as a plane expression. -/
private lemma zz_cd_bridge (τ w : UpperHalfPlane) :
    1 + Complex.normSq ((τ : ℂ) - (w : ℂ)) / (2 * (τ : ℂ).im * (w : ℂ).im)
      = Real.cosh (dist τ w) := by
  have h := UpperHalfPlane.cosh_dist τ w
  have hd : dist (τ : ℂ) (w : ℂ) ^ 2 = Complex.normSq ((τ : ℂ) - (w : ℂ)) := by
    rw [dist_eq_norm, Complex.sq_norm]
  rw [h, hd, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]

/-- Differentiability of the cosh-distance expression on the upper half plane. -/
private lemma zz_cd_contDiffAt (w : ℂ) (hw : 0 < w.im) (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    ContDiffAt ℝ 1 (fun z => 1 + Complex.normSq (z - w) / (2 * z.im * w.im)) z₀ := by
  have hre : ContDiff ℝ 1 (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ 1 (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hns : (fun z : ℂ => Complex.normSq (z - w))
      = fun z : ℂ => (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    funext z
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hnum : ContDiffAt ℝ 1 (fun z : ℂ => Complex.normSq (z - w)) z₀ := by
    rw [hns]
    exact (((hre.sub contDiff_const).pow 2).add
      ((him.sub contDiff_const).pow 2)).contDiffAt
  have hden : ContDiffAt ℝ 1 (fun z : ℂ => 2 * z.im * w.im) z₀ :=
    ((contDiff_const.mul him).mul contDiff_const).contDiffAt
  have hden0 : 2 * z₀.im * w.im ≠ 0 := by positivity
  exact (contDiffAt_const.add (hnum.div hden hden0))

/-- The elementary triple move for chain values. -/
private lemma zz_step {G : Type} [Group G] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b))
    (a b c : ↥Γ) (w : ℂ) (hwa : w ∈ V a) (hwb : w ∈ V b) (hwc : w ∈ V c) :
    f (a⁻¹ * b) * f (b⁻¹ * c) = f (a⁻¹ * c) := by
  have h1 : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V 1 := by
    have h := hVtrans a⁻¹ a w hwa
    rwa [inv_mul_cancel] at h
  have h2 : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V (a⁻¹ * b) := hVtrans a⁻¹ b w hwb
  have h3 : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V (a⁻¹ * c) := hVtrans a⁻¹ c w hwc
  have hmul : (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c := by group
  have h3' : moebiusMap (↑(a⁻¹ : ↥Γ)) w ∈ V ((a⁻¹ * b) * (b⁻¹ * c)) := by
    rwa [hmul]
  rw [htrip (a⁻¹ * b) (b⁻¹ * c) ⟨moebiusMap (↑(a⁻¹ : ↥Γ)) w, ⟨h1, h2⟩, h3'⟩, hmul]

/-- **Same-grid chain comparison**: two chains subordinate to the same path on the same
uniform grid have the same value. Induction on the grid size along a reparametrized path. -/
private lemma zz_compare {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b)) :
    ∀ (N : ℕ), 0 < N → ∀ (α : ℝ → ℂ) (γt : ↥Γ) (g g' : ℕ → ↥Γ),
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k)) →
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g' k)) →
      α 0 ∈ V 1 → α 1 ∈ V γt →
      f (g' 0) * ((List.range (N - 1)).map fun k => f ((g' k)⁻¹ * g' (k + 1))).prod
          * f ((g' (N - 1))⁻¹ * γt)
        = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
          * f ((g (N - 1))⁻¹ * γt) := by
  have hstep := zz_step V f hVtrans htrip
  intro N
  induction N with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ N ih =>
    intro _ α γt g g' hs hs' hb ht
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- base case: a single slot
      subst hN0
      simp only [List.range_zero, List.map_nil, List.prod_nil, mul_one, Nat.sub_self]
      have h00 : α 0 ∈ V (g 0) := by
        refine hs 0 (by norm_num) 0 (by norm_num) ?_
        norm_num
      have h00' : α 0 ∈ V (g' 0) := by
        refine hs' 0 (by norm_num) 0 (by norm_num) ?_
        norm_num
      have h10 : α 1 ∈ V (g 0) := by
        refine hs 0 (by norm_num) 1 (by norm_num) ?_
        norm_num
      have h10' : α 1 ∈ V (g' 0) := by
        refine hs' 0 (by norm_num) 1 (by norm_num) ?_
        norm_num
      -- head move at α 0 and junction move at α 1
      have hA : f ((g' 0)⁻¹ * g 0) * f ((g 0)⁻¹ * γt) = f ((g' 0)⁻¹ * γt) :=
        hstep (g' 0) (g 0) γt (α 1) h10' h10 ht
      have hB : f ((1 : ↥Γ)⁻¹ * g' 0) * f ((g' 0)⁻¹ * g 0) = f ((1 : ↥Γ)⁻¹ * g 0) :=
        hstep 1 (g' 0) (g 0) (α 0) hb h00' h00
      rw [inv_one, one_mul, one_mul] at hB
      calc f (g' 0) * f ((g' 0)⁻¹ * γt)
          = f (g' 0) * (f ((g' 0)⁻¹ * g 0) * f ((g 0)⁻¹ * γt)) := by rw [hA]
        _ = (f (g' 0) * f ((g' 0)⁻¹ * g 0)) * f ((g 0)⁻¹ * γt) := by rw [mul_assoc]
        _ = f (g 0) * f ((g 0)⁻¹ * γt) := by rw [hB]
    · -- inductive step: peel the last slot
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hM2r : (0 : ℝ) < (M : ℝ) + 2 := by positivity
      have hM1r : (0 : ℝ) < (M : ℝ) + 1 := by positivity
      obtain ⟨β, hβdef⟩ : ∃ β : ℝ → ℂ,
          β = fun t => α (t * ((M : ℝ) + 1) / ((M : ℝ) + 2)) := ⟨_, rfl⟩
      have hβval : ∀ t : ℝ, β t = α (t * ((M : ℝ) + 1) / ((M : ℝ) + 2)) := by
        intro t
        rw [hβdef]
      have hcast2 : ((M + 1 + 1 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
      have hcast1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      -- grid transfer for the reparametrized path
      have htransfer : ∀ (h : ℕ → ↥Γ),
          (∀ k < M + 1 + 1, ∀ t : ℝ, (k : ℝ) / (M + 1 + 1 : ℕ) ≤ t →
            t ≤ ((k : ℝ) + 1) / (M + 1 + 1 : ℕ) → α t ∈ V (h k)) →
          ∀ k < M + 1, ∀ t : ℝ, (k : ℝ) / (M + 1 : ℕ) ≤ t →
            t ≤ ((k : ℝ) + 1) / (M + 1 : ℕ) → β t ∈ V (h k) := by
        intro h hsub k hk t ht1 ht2
        rw [hβval]
        rw [hcast1] at ht1 ht2
        refine hsub k (by omega) (t * ((M : ℝ) + 1) / ((M : ℝ) + 2)) ?_ ?_
        · rw [hcast2, div_le_div_iff_of_pos_right hM2r]
          rw [div_le_iff₀ hM1r] at ht1
          linarith
        · rw [hcast2, div_le_div_iff_of_pos_right hM2r]
          rw [le_div_iff₀ hM1r] at ht2
          linarith
      -- junction memberships at the peeling point
      have hqN : α (((M : ℝ) + 1) / ((M : ℝ) + 2)) ∈ V (g (M + 1)) := by
        refine hs (M + 1) (by omega) _ ?_ ?_
        · rw [hcast2, hcast1]
        · rw [hcast2, hcast1]
          rw [div_le_div_iff_of_pos_right hM2r]
          linarith
      have hq'N : α (((M : ℝ) + 1) / ((M : ℝ) + 2)) ∈ V (g' (M + 1)) := by
        refine hs' (M + 1) (by omega) _ ?_ ?_
        · rw [hcast2, hcast1]
        · rw [hcast2, hcast1]
          rw [div_le_div_iff_of_pos_right hM2r]
          linarith
      have hq'M : α (((M : ℝ) + 1) / ((M : ℝ) + 2)) ∈ V (g' M) := by
        refine hs' M (by omega) _ ?_ ?_
        · rw [hcast2]
          rw [div_le_div_iff_of_pos_right hM2r]
          linarith
        · rw [hcast2]
      -- endpoint memberships
      have heN : α 1 ∈ V (g (M + 1)) := by
        refine hs (M + 1) (by omega) 1 ?_ ?_
        · rw [hcast2, hcast1, div_le_one hM2r]
          linarith
        · rw [hcast2, hcast1, le_div_iff₀ hM2r]
          linarith
      have he'N : α 1 ∈ V (g' (M + 1)) := by
        refine hs' (M + 1) (by omega) 1 ?_ ?_
        · rw [hcast2, hcast1, div_le_one hM2r]
          linarith
        · rw [hcast2, hcast1, le_div_iff₀ hM2r]
          linarith
      -- endpoint conditions for the reparametrized path
      have hbβ : β 0 ∈ V 1 := by
        rw [hβval]
        rw [show (0 : ℝ) * ((M : ℝ) + 1) / ((M : ℝ) + 2) = 0 by rw [zero_mul, zero_div]]
        exact hb
      have htβ : β 1 ∈ V (g (M + 1)) := by
        rw [hβval]
        rw [show (1 : ℝ) * ((M : ℝ) + 1) / ((M : ℝ) + 2)
          = ((M : ℝ) + 1) / ((M : ℝ) + 2) by rw [one_mul]]
        exact hqN
      -- the two junction moves
      have hA : f ((g' (M + 1))⁻¹ * g (M + 1)) * f ((g (M + 1))⁻¹ * γt)
          = f ((g' (M + 1))⁻¹ * γt) :=
        hstep (g' (M + 1)) (g (M + 1)) γt (α 1) he'N heN ht
      have hB : f ((g' M)⁻¹ * g' (M + 1)) * f ((g' (M + 1))⁻¹ * g (M + 1))
          = f ((g' M)⁻¹ * g (M + 1)) :=
        hstep (g' M) (g' (M + 1)) (g (M + 1)) (α (((M : ℝ) + 1) / ((M : ℝ) + 2)))
          hq'M hq'N hqN
      -- the induction hypothesis for the peeled path
      have hIH := ih (by omega) β (g (M + 1)) g g' (htransfer g hs) (htransfer g' hs')
        hbβ htβ
      -- reassemble: split off the last factor of the products
      simp only [Nat.add_sub_cancel] at hIH ⊢
      rw [List.range_succ]
      simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
      rw [← hA]
      simp only [← mul_assoc]
      rw [mul_assoc _ (f ((g' M)⁻¹ * g' (M + 1))) (f ((g' (M + 1))⁻¹ * g (M + 1))), hB, hIH]

/-- **Refinement invariance of chain values**: refining every slot `m + 1`-fold does not
change the value. Pure algebra, by induction on the number of coarse slots. -/
private lemma zz_refine_val {G H : Type} [Group G] [Group H] (f : H → G) (hf1 : f 1 = 1)
    (mm : ℕ) :
    ∀ (A : ℕ) (g : ℕ → H) (γt : H),
      f (g 0) * ((List.range (A * (mm + 1) + mm)).map
          fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod
        * f ((g ((A * (mm + 1) + mm) / (mm + 1)))⁻¹ * γt)
      = f (g 0) * ((List.range A).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
        * f ((g A)⁻¹ * γt) := by
  have hdivA : ∀ A : ℕ, (A * (mm + 1) + mm) / (mm + 1) = A := by
    intro A
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hdivlow : ∀ A j : ℕ, j ≤ mm → (A * (mm + 1) + j) / (mm + 1) = A := by
    intro A j hj
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  intro A
  induction A with
  | zero =>
    intro g γt
    have hprod : ((List.range mm).map
        fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod = 1 := by
      refine List.prod_eq_one ?_
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      have hk' : k < mm := List.mem_range.mp hk
      have h1 : k / (mm + 1) = 0 := Nat.div_eq_of_lt (by omega)
      have h2 : (k + 1) / (mm + 1) = 0 := Nat.div_eq_of_lt (by omega)
      rw [h1, h2, inv_mul_cancel, hf1]
    have hmm0 : mm / (mm + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp only [Nat.zero_mul, Nat.zero_add, hmm0, hprod, List.range_zero, List.map_nil,
      List.prod_nil]
  | succ A ih =>
    intro g γt
    have harg : (A + 1) * (mm + 1) + mm = (A * (mm + 1) + mm) + (mm + 1) := by ring
    rw [harg, List.range_add, List.map_append, List.prod_append]
    -- the new block of factors
    have hr1 : List.range (mm + 1) = [0] ++ List.map (fun x => 1 + x) (List.range mm) := by
      rw [← List.range_one, ← List.range_add, Nat.add_comm mm 1]
    have hblock : (((List.range (mm + 1)).map fun x => A * (mm + 1) + mm + x).map
        fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod
        = f ((g A)⁻¹ * g (A + 1)) := by
      rw [hr1, List.map_append, List.map_append, List.prod_append]
      have hsingle : ((([0] : List ℕ).map fun x => A * (mm + 1) + mm + x).map
          fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod
          = f ((g A)⁻¹ * g (A + 1)) := by
        simp only [List.map_singleton, List.prod_singleton, Nat.add_zero]
        rw [hdivA A]
        rw [show A * (mm + 1) + mm + 1 = (A + 1) * (mm + 1) from by ring,
          Nat.mul_div_cancel _ (by omega : 0 < mm + 1)]
      have hrest : ((((List.range mm).map fun x => 1 + x).map
          fun x => A * (mm + 1) + mm + x).map
          fun k => f ((g (k / (mm + 1)))⁻¹ * g ((k + 1) / (mm + 1)))).prod = 1 := by
        refine List.prod_eq_one ?_
        intro y hy
        obtain ⟨k1, hk1, rfl⟩ := List.mem_map.mp hy
        obtain ⟨k2, hk2, rfl⟩ := List.mem_map.mp hk1
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk2
        have hx' : x < mm := List.mem_range.mp hx
        have ha : A * (mm + 1) + mm + (1 + x) = (A + 1) * (mm + 1) + x := by ring
        rw [ha, hdivlow (A + 1) x (by omega),
          show (A + 1) * (mm + 1) + x + 1 = (A + 1) * (mm + 1) + (x + 1) from by ring,
          hdivlow (A + 1) (x + 1) (by omega), inv_mul_cancel, hf1]
      rw [hsingle, hrest, mul_one]
    have htail : ((A * (mm + 1) + mm) + (mm + 1)) / (mm + 1) = A + 1 := by
      rw [show (A * (mm + 1) + mm) + (mm + 1) = (A + 1) * (mm + 1) + mm from by ring]
      exact hdivA (A + 1)
    rw [hblock, htail]
    -- reassemble with the induction hypothesis at target `g (A + 1)`
    have hIH := ih g (g (A + 1))
    rw [hdivA A] at hIH
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
    simp only [← mul_assoc]
    rw [hIH]

/-- **Refinement transfer of subordination**: a chain subordinate on the coarse grid is
subordinate on the refined grid through slot division. -/
private lemma zz_refine_sub {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (α : ℝ → ℂ) (g : ℕ → ↥Γ)
    (hs : ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k)) :
    ∀ k < N * m, ∀ t : ℝ, (k : ℝ) / (N * m : ℕ) ≤ t → t ≤ ((k : ℝ) + 1) / (N * m : ℕ) →
      α t ∈ V (g (k / m)) := by
  intro k hk t ht1 ht2
  have hq : k / m < N := Nat.div_lt_iff_lt_mul hm |>.mpr hk
  obtain ⟨q, hq_def⟩ : ∃ q, q = k / m := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r, r = k % m := ⟨_, rfl⟩
  have hkqr : k = m * q + r := by
    rw [hq_def, hr_def]
    exact (Nat.div_add_mod k m).symm
  have hrm : r < m := by
    rw [hr_def]
    exact Nat.mod_lt _ hm
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNmr : (0 : ℝ) < ((N * m : ℕ) : ℝ) := by
    push_cast
    positivity
  rw [← hq_def]
  refine hs q (by rw [hq_def]; exact hq) t ?_ ?_
  · -- (q : ℝ) / N ≤ t
    refine le_trans ?_ ht1
    rw [div_le_div_iff₀ hNr hNmr]
    have h1 : (q : ℝ) * m ≤ (k : ℝ) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) hkqr
      push_cast at hc
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      nlinarith [hc, hr0]
    have h2 := mul_le_mul_of_nonneg_right h1 hNr.le
    push_cast
    nlinarith [h2]
  · -- t ≤ ((q : ℝ) + 1) / N
    refine le_trans ht2 ?_
    rw [div_le_div_iff₀ hNmr hNr]
    have hk1 : k + 1 ≤ m * (q + 1) := by
      have hmq : m * (q + 1) = m * q + m := by ring
      omega
    have h1 : (k : ℝ) + 1 ≤ (m : ℝ) * ((q : ℝ) + 1) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.le.dest hk1).choose_spec
      exact_mod_cast Nat.cast_le.mpr hk1
    have h2 := mul_le_mul_of_nonneg_right h1 hNr.le
    push_cast
    nlinarith [h2]

/-- **Cross-grid chain comparison**: chains along the same path on different uniform grids
have the same value, via refinement to a common grid. -/
private lemma zz_anychain {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b))
    (hf1 : f 1 = 1) :
    ∀ (N N' : ℕ), 0 < N → 0 < N' → ∀ (α : ℝ → ℂ) (γt : ↥Γ) (g h : ℕ → ↥Γ),
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k)) →
      (∀ k < N', ∀ t : ℝ, (k : ℝ) / N' ≤ t → t ≤ ((k : ℝ) + 1) / N' → α t ∈ V (h k)) →
      α 0 ∈ V 1 → α 1 ∈ V γt →
      f (h 0) * ((List.range (N' - 1)).map fun k => f ((h k)⁻¹ * h (k + 1))).prod
          * f ((h (N' - 1))⁻¹ * γt)
        = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
          * f ((g (N - 1))⁻¹ * γt) := by
  intro N N' hN hN' α γt g h hsg hsh hb ht
  obtain ⟨nn, rfl⟩ : ∃ nn, N = nn + 1 := ⟨N - 1, by omega⟩
  obtain ⟨mm, rfl⟩ : ∃ mm, N' = mm + 1 := ⟨N' - 1, by omega⟩
  -- refine both chains to the common grid (nn + 1) * (mm + 1)
  have hsub_g' := zz_refine_sub V (nn + 1) (mm + 1) (by omega) (by omega) α g hsg
  have hsub_h' := zz_refine_sub V (mm + 1) (nn + 1) (by omega) (by omega) α h hsh
  rw [Nat.mul_comm (mm + 1) (nn + 1)] at hsub_h'
  have hcmp := zz_compare V f hVtrans htrip ((nn + 1) * (mm + 1)) (by positivity) α γt
    (fun k => g (k / (mm + 1))) (fun k => h (k / (nn + 1))) hsub_g' hsub_h' hb ht
  have hval_g := zz_refine_val f hf1 mm nn g γt
  have hval_h := zz_refine_val f hf1 nn mm h γt
  -- align the grid arithmetic
  have hP1 : (nn + 1) * (mm + 1) - 1 = nn * (mm + 1) + mm := by
    have hx : (nn + 1) * (mm + 1) = nn * (mm + 1) + mm + 1 := by ring
    omega
  have hP2 : mm * (nn + 1) + nn = nn * (mm + 1) + mm := by ring
  rw [hP1] at hcmp
  rw [hP2] at hval_h
  have hdivg : (nn * (mm + 1) + mm) / (mm + 1) = nn := by
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have hdivh : (nn * (mm + 1) + mm) / (nn + 1) = mm := by
    rw [← hP2]
    refine Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [hdivg] at hval_g
  rw [hdivh] at hval_h
  simp only [] at hcmp
  simp only [Nat.zero_div] at hcmp
  rw [hdivg, hdivh] at hcmp
  simp only [Nat.add_sub_cancel]
  rw [← hval_g, ← hval_h]
  exact hcmp

/-- Every parameter in `[0, 1]` lies in some slot of the uniform grid. -/
private lemma zz_findpiece (N : ℕ) (hN : 0 < N) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ k < N, (k : ℝ) / N ≤ s ∧ s ≤ ((k : ℝ) + 1) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hfl : ⌊s * N⌋₊ < N
  · refine ⟨⌊s * N⌋₊, hfl, ?_, ?_⟩
    · rw [div_le_iff₀ hNr]
      exact Nat.floor_le (by positivity)
    · rw [le_div_iff₀ hNr]
      have := Nat.lt_floor_add_one (s * N)
      linarith
  · push Not at hfl
    have hsN : (N : ℝ) ≤ s * N := by
      have h := Nat.le_floor_iff (α := ℝ) (by positivity : (0 : ℝ) ≤ s * N) |>.mp hfl
      exact h
    have hs1' : s = 1 := by
      have h2 : s * N ≤ N := by nlinarith
      have h3 : s * N = N := le_antisymm h2 hsN
      have := mul_right_cancel₀ hNr.ne' (by rw [h3, one_mul] : s * (N : ℝ) = 1 * N)
      exact this
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ N := hN
      push_cast [Nat.cast_sub h1]
      ring
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · rw [hcast, hs1', div_le_one hNr]
      linarith
    · rw [hcast, hs1', le_div_iff₀ hNr]
      linarith

/-- **Chain existence** along a continuous path through an open cover by translates. -/
private lemma zz_chain_exists {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (hVopen : ∀ γ, IsOpen (V γ)) (α : ℝ → ℂ) (hαc : Continuous α)
    (hcov : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ γ, α t ∈ V γ) :
    ∃ (N : ℕ) (g : ℕ → ↥Γ), 0 < N ∧
      ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k) := by
  have hopen : ∀ γ : ↥Γ, IsOpen (α ⁻¹' (V γ)) := fun γ => (hVopen γ).preimage hαc
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ ⋃ γ : ↥Γ, α ⁻¹' (V γ) := by
    intro t ht
    obtain ⟨γ, hγ⟩ := hcov t ht.1 ht.2
    exact Set.mem_iUnion.mpr ⟨γ, hγ⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hsub
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    have h0 : (0 : ℝ) < 1 / δ := by positivity
    have : (0 : ℝ) < N := lt_trans h0 hN
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1N : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδpos] at hN
    nlinarith
  have hpick : ∀ k : ℕ, ∃ γ : ↥Γ, k < N → Metric.ball ((k : ℝ) / N) δ ⊆ α ⁻¹' (V γ) := by
    intro k
    by_cases hk : k < N
    · have hmem : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one hNr]
          exact_mod_cast hk.le
      obtain ⟨γ, hγ⟩ := hδ ((k : ℝ) / N) hmem
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose g hg using hpick
  refine ⟨N, g, hNpos, ?_⟩
  intro k hk t ht1 ht2
  refine hg k hk ?_
  rw [Metric.mem_ball, Real.dist_eq]
  have hsplit : ((k : ℝ) + 1) / N = (k : ℝ) / N + 1 / N := by ring
  rw [abs_of_nonneg (by linarith)]
  rw [hsplit] at ht2
  linarith

/-- **Homotopy invariance of chain values** for paths with the same endpoints, via the
straight-line homotopy and a Lebesgue grid of squares. -/
private lemma zz_homotopy {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (f : ↥Γ → G)
    (hVsub : ∀ γ, V γ ⊆ {z : ℂ | 0 < z.im})
    (hVopen : ∀ γ, IsOpen (V γ))
    (hVcov : ∀ z : ℂ, 0 < z.im → ∃ γ, z ∈ V γ)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b))
    (hf1 : f 1 = 1)
    (α β : ℝ → ℂ) (hαc : Continuous α) (hβc : Continuous β)
    (h0 : α 0 = β 0) (h1 : α 1 = β 1)
    (γt : ↥Γ) (N N' : ℕ) (g h : ℕ → ↥Γ) (hN : 0 < N) (hN' : 0 < N')
    (hsg : ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → α t ∈ V (g k))
    (hsh : ∀ k < N', ∀ t : ℝ, (k : ℝ) / N' ≤ t → t ≤ ((k : ℝ) + 1) / N' → β t ∈ V (h k))
    (hb : α 0 ∈ V 1) (ht : α 1 ∈ V γt) :
    f (h 0) * ((List.range (N' - 1)).map fun k => f ((h k)⁻¹ * h (k + 1))).prod
        * f ((h (N' - 1))⁻¹ * γt)
      = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
        * f ((g (N - 1))⁻¹ * γt) := by
  -- imaginary-part positivity along both paths
  have himα : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < (α s).im := by
    intro s hs0 hs1
    obtain ⟨k, hk, hk1, hk2⟩ := zz_findpiece N hN s hs0 hs1
    exact hVsub (g k) (hsg k hk s hk1 hk2)
  have himβ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < (β s).im := by
    intro s hs0 hs1
    obtain ⟨k, hk, hk1, hk2⟩ := zz_findpiece N' hN' s hs0 hs1
    exact hVsub (h k) (hsh k hk s hk1 hk2)
  -- the straight-line homotopy
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × ℝ → ℂ,
      H = fun p => ((1 - p.2 : ℝ) : ℂ) * α p.1 + ((p.2 : ℝ) : ℂ) * β p.1 := ⟨_, rfl⟩
  have hHval : ∀ s t : ℝ, H (s, t) = ((1 - t : ℝ) : ℂ) * α s + ((t : ℝ) : ℂ) * β s := by
    intro s t
    rw [hHdef]
  have hHc : Continuous H := by
    rw [hHdef]
    refine Continuous.add ?_ ?_
    · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)).mul
        (hαc.comp continuous_fst)
    · exact (Complex.continuous_ofReal.comp continuous_snd).mul (hβc.comp continuous_fst)
  have hHim : ∀ p : ℝ × ℝ, p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 → 0 < (H p).im := by
    rintro ⟨s, t⟩ ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩
    rw [hHval]
    have h1 := himα s hs0 hs1
    have h2 := himβ s hs0 hs1
    have him : (((1 - t : ℝ) : ℂ) * α s + ((t : ℝ) : ℂ) * β s).im
        = (1 - t) * (α s).im + t * (β s).im := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]
    rcases le_or_gt t (1 / 2) with hc | hc
    · nlinarith
    · nlinarith
  -- Lebesgue number for the square
  have hopen : ∀ γ : ↥Γ, IsOpen (H ⁻¹' (V γ)) := fun γ => (hVopen γ).preimage hHc
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ ⋃ γ : ↥Γ, H ⁻¹' (V γ) := by
    intro p hp
    obtain ⟨γ, hγ⟩ := hVcov (H p) (hHim p hp)
    exact Set.mem_iUnion.mpr ⟨γ, hγ⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc.prod isCompact_Icc) hopen hsub
  obtain ⟨P, hP⟩ := exists_nat_gt (1 / δ)
  have hPpos : 0 < P := by
    have h0' : (0 : ℝ) < 1 / δ := by positivity
    have : (0 : ℝ) < P := lt_trans h0' hP
    exact_mod_cast this
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have h1P : 1 / (P : ℝ) < δ := by
    rw [div_lt_iff₀ hPr]
    rw [div_lt_iff₀ hδpos] at hP
    nlinarith
  -- square choices
  have hpick : ∀ ij : ℕ × ℕ, ∃ γ : ↥Γ, ij.1 < P → ij.2 < P →
      Metric.ball (((ij.1 : ℝ) / P, (ij.2 : ℝ) / P) : ℝ × ℝ) δ ⊆ H ⁻¹' (V γ) := by
    rintro ⟨i, j⟩
    by_cases hij : i < P ∧ j < P
    · have hmem : (((i : ℝ) / P, (j : ℝ) / P) : ℝ × ℝ)
          ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
        constructor
        · constructor
          · positivity
          · rw [div_le_one hPr]
            exact_mod_cast hij.1.le
        · constructor
          · positivity
          · rw [div_le_one hPr]
            exact_mod_cast hij.2.le
      obtain ⟨γ, hγ⟩ := hδ _ hmem
      exact ⟨γ, fun _ _ => hγ⟩
    · exact ⟨1, fun hi hj => absurd ⟨hi, hj⟩ hij⟩
  choose w hw using hpick
  -- the two subordination properties of a square row
  have hrow1 : ∀ j : ℕ, j < P → ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      H (s, (j : ℝ) / P) ∈ V (w (i, j)) := by
    intro j hj i hi s hs1 hs2
    refine hw (i, j) hi hj ?_
    rw [Metric.mem_ball]
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    have hsplit : ((i : ℝ) + 1) / P = (i : ℝ) / P + 1 / P := by ring
    rw [hsplit] at hs2
    have habs1 : |s - (i : ℝ) / P| < δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have habs2 : |(j : ℝ) / P - (j : ℝ) / P| < δ := by
      rw [sub_self, abs_zero]
      exact hδpos
    exact max_lt habs1 habs2
  have hrow2 : ∀ j : ℕ, j < P → ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      H (s, ((j : ℝ) + 1) / P) ∈ V (w (i, j)) := by
    intro j hj i hi s hs1 hs2
    refine hw (i, j) hi hj ?_
    rw [Metric.mem_ball]
    rw [Prod.dist_eq]
    simp only [Real.dist_eq]
    have hsplit : ((i : ℝ) + 1) / P = (i : ℝ) / P + 1 / P := by ring
    rw [hsplit] at hs2
    have habs1 : |s - (i : ℝ) / P| < δ := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have habs2 : |((j : ℝ) + 1) / P - (j : ℝ) / P| < δ := by
      rw [show ((j : ℝ) + 1) / P - (j : ℝ) / P = 1 / P by ring]
      rw [abs_of_nonneg (by positivity)]
      exact h1P
    exact max_lt habs1 habs2
  -- row endpoints
  have hrowa : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → H (0, t) = α 0 := by
    intro t _ _
    rw [hHval, h0]
    push_cast
    ring
  have hrowb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → H (1, t) = α 1 := by
    intro t _ _
    rw [hHval, h1]
    push_cast
    ring
  have htbound : ∀ j : ℕ, j < P → 0 ≤ (j : ℝ) / P ∧ (j : ℝ) / P ≤ 1 := by
    intro j hj
    constructor
    · positivity
    · rw [div_le_one hPr]
      exact_mod_cast hj.le
  have htbound1 : ∀ j : ℕ, j < P → 0 ≤ ((j : ℝ) + 1) / P ∧ ((j : ℝ) + 1) / P ≤ 1 := by
    intro j hj
    constructor
    · positivity
    · rw [div_le_one hPr]
      have : (j : ℝ) + 1 ≤ P := by exact_mod_cast hj
      linarith
  -- the row-invariance induction
  have hind : ∀ j : ℕ, j < P →
      f (w (0, j)) * ((List.range (P - 1)).map
          fun k => f ((w (k, j))⁻¹ * w (k + 1, j))).prod * f ((w (P - 1, j))⁻¹ * γt)
      = f (w (0, 0)) * ((List.range (P - 1)).map
          fun k => f ((w (k, 0))⁻¹ * w (k + 1, 0))).prod * f ((w (P - 1, 0))⁻¹ * γt) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ihj =>
      intro hj1
      have hj : j < P := by omega
      -- both row chains are subordinate to the row path at height (j + 1) / P
      have hpath0 : H (0, ((j : ℝ) + 1) / P) ∈ V 1 := by
        rw [hrowa _ (htbound1 j hj).1 (htbound1 j hj).2]
        exact hb
      have hpath1 : H (1, ((j : ℝ) + 1) / P) ∈ V γt := by
        rw [hrowb _ (htbound1 j hj).1 (htbound1 j hj).2]
        exact ht
      have hsubj : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
          (fun s => H (s, ((j : ℝ) + 1) / P)) s ∈ V ((fun i => w (i, j)) i) :=
        fun i hi s hs1 hs2 => hrow2 j hj i hi s hs1 hs2
      have hsubj1 : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
          (fun s => H (s, ((j : ℝ) + 1) / P)) s ∈ V ((fun i => w (i, j + 1)) i) := by
        intro i hi s hs1 hs2
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        have := hrow1 (j + 1) hj1 i hi s hs1 hs2
        rwa [hcast] at this
      have hcmp := zz_compare V f hVtrans htrip P hPpos
        (fun s => H (s, ((j : ℝ) + 1) / P)) γt
        (fun i => w (i, j)) (fun i => w (i, j + 1)) hsubj hsubj1 hpath0 hpath1
      simp only [] at hcmp
      rw [hcmp]
      exact ihj hj
  -- compare the given chains with the extreme rows
  have hrow0α : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      α s ∈ V ((fun i => w (i, 0)) i) := by
    intro i hi s hs1 hs2
    have := hrow1 0 hPpos i hi s hs1 hs2
    have hz : ((0 : ℕ) : ℝ) / P = 0 := by
      rw [Nat.cast_zero, zero_div]
    rw [hz] at this
    have hHα : H (s, 0) = α s := by
      rw [hHval]
      push_cast
      ring
    rwa [hHα] at this
  have hrowPβ : ∀ i < P, ∀ s : ℝ, (i : ℝ) / P ≤ s → s ≤ ((i : ℝ) + 1) / P →
      β s ∈ V ((fun i => w (i, P - 1)) i) := by
    intro i hi s hs1 hs2
    have hlt : P - 1 < P := by omega
    have := hrow2 (P - 1) hlt i hi s hs1 hs2
    have hcast : ((P - 1 : ℕ) : ℝ) + 1 = (P : ℝ) := by
      have h1' : (1 : ℕ) ≤ P := hPpos
      push_cast [Nat.cast_sub h1']
      ring
    rw [hcast, div_self hPr.ne'] at this
    have hHβ : H (s, 1) = β s := by
      rw [hHval]
      push_cast
      ring
    rwa [hHβ] at this
  have hbβ : β 0 ∈ V 1 := by
    rw [← h0]
    exact hb
  have htβ : β 1 ∈ V γt := by
    rw [← h1]
    exact ht
  have hα0 := zz_anychain V f hVtrans htrip hf1 N P hN hPpos α γt g
    (fun i => w (i, 0)) hsg hrow0α hb ht
  have hβP := zz_anychain V f hVtrans htrip hf1 N' P hN' hPpos β γt h
    (fun i => w (i, P - 1)) hsh hrowPβ hbβ htβ
  simp only [] at hα0 hβP
  rw [← hα0, ← hβP]
  have hfin := hind (P - 1) (by omega)
  simp only [] at hfin
  rw [hfin]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The monodromy extension develops chain values along paths, concatenations and homotopies
-- in a single declaration; the default heartbeat budget does not cover its elaboration.
/-- **Monodromy extension of a local multiplicative datum**: a function on a group of
Möbius translates satisfying the triple cocycle condition on an open covering family of the
upper half plane by translates of a convex base extends to a homomorphism computed by chain
values along paths from the base point. -/
private lemma zz_mfunc {G : Type} [Group G]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (V : ↥Γ → Set ℂ) (i₀ : ℂ)
    (hVsub : ∀ γ, V γ ⊆ {z : ℂ | 0 < z.im})
    (hVopen : ∀ γ, IsOpen (V γ))
    (hVcov : ∀ z : ℂ, 0 < z.im → ∃ γ, z ∈ V γ)
    (hVtrans : ∀ (β γ : ↥Γ) (z : ℂ), z ∈ V γ → moebiusMap (↑β) z ∈ V (β * γ))
    (hi₀ : i₀ ∈ V 1) (hV1conv : Convex ℝ (V 1))
    (f : ↥Γ → G)
    (htrip : ∀ a b : ↥Γ, (V 1 ∩ V a ∩ V (a * b)).Nonempty → f a * f b = f (a * b)) :
    ∃ θ : ↥Γ → G,
      (∀ γ δ : ↥Γ, θ (γ * δ) = θ γ * θ δ) ∧
      (∀ γ : ↥Γ, (V 1 ∩ V γ).Nonempty → θ γ = f γ) ∧
      (∀ S : Subgroup G, (∀ x, f x ∈ S) → ∀ γ, θ γ ∈ S) ∧
      (∀ (γ : ↥Γ) (αp : ℝ → ℂ) (N : ℕ) (g : ℕ → ↥Γ), Continuous αp →
        αp 0 = i₀ → αp 1 = moebiusMap (↑γ) i₀ → 0 < N →
        (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → αp t ∈ V (g k)) →
        θ γ = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
          * f ((g (N - 1))⁻¹ * γ)) := by
  classical
  have hi₀im : 0 < i₀.im := hVsub 1 hi₀
  have hf1 : f 1 = 1 := by
    have hmem : (V 1 ∩ V 1 ∩ V ((1 : ↥Γ) * 1)).Nonempty := by
      refine ⟨i₀, ⟨hi₀, hi₀⟩, ?_⟩
      rw [mul_one]
      exact hi₀
    have h := htrip 1 1 hmem
    rw [mul_one] at h
    exact mul_right_cancel (h.trans (one_mul (f 1)).symm)
  have hqmem : ∀ γ : ↥Γ, moebiusMap (↑γ) i₀ ∈ V γ := by
    intro γ
    have h := hVtrans γ 1 i₀ hi₀
    rwa [mul_one] at h
  have hqim : ∀ γ : ↥Γ, 0 < (moebiusMap (↑γ) i₀).im := fun γ => hVsub γ (hqmem γ)
  -- continuity of Möbius maps on the upper half plane
  have hmoebc : ∀ (γ : ↥Γ) (α : ℝ → ℂ), Continuous α → (∀ t : ℝ, 0 < (α t).im) →
      Continuous (fun t => moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (α t)) := by
    intro γ α hαc hαim
    have hcOn : ContinuousOn (moebiusMap (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        {z : ℂ | 0 < z.im} := by
      intro z hz
      exact ((hasDerivAt_moebiusMap (↑γ) (moebiusDenom_ne_zero_of_im_ne_zero (↑γ)
        (ne_of_gt hz))).continuousAt).continuousWithinAt
    exact hcOn.comp_continuous hαc hαim
  -- the canonical straight path to the translate of the base point
  obtain ⟨Pc, hPcdef⟩ : ∃ Pc : ↥Γ → ℝ → ℂ,
      Pc = fun (γ : ↥Γ) (t : ℝ) => i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀) :=
    ⟨fun (γ : ↥Γ) (t : ℝ) => i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀), rfl⟩
  have hPcval : ∀ γ t, Pc γ t = i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀) := by
    intro γ t
    rw [hPcdef]
  have hPccont : ∀ γ, Continuous (Pc γ) := by
    intro γ
    rw [hPcdef]
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hPc0 : ∀ γ, Pc γ 0 = i₀ := by
    intro γ
    rw [hPcval]
    push_cast
    ring
  have hPc1 : ∀ γ, Pc γ 1 = moebiusMap (↑γ) i₀ := by
    intro γ
    rw [hPcval]
    push_cast
    ring
  have hPcim : ∀ γ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < (Pc γ t).im := by
    intro γ t ht0 ht1
    rw [hPcval]
    have h1 := hi₀im
    have h2 := hqim γ
    have him : (i₀ + (t : ℂ) * (moebiusMap (↑γ) i₀ - i₀)).im
        = (1 - t) * i₀.im + t * (moebiusMap (↑γ) i₀).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, zero_mul, add_zero]
      ring
    rw [him]
    rcases le_or_gt t (1 / 2) with hc | hc
    · nlinarith
    · nlinarith
  -- chains along the canonical paths
  have hch : ∀ γ : ↥Γ, ∃ (N : ℕ) (g : ℕ → ↥Γ), 0 < N ∧
      ∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → Pc γ t ∈ V (g k) :=
    fun γ => zz_chain_exists V hVopen (Pc γ) (hPccont γ)
      (fun t ht0 ht1 => hVcov _ (hPcim γ t ht0 ht1))
  choose Nc gc hNc hsc using hch
  obtain ⟨θ, hθdef⟩ : ∃ θ : ↥Γ → G, θ = fun γ =>
      f (gc γ 0) * ((List.range (Nc γ - 1)).map
        fun k => f ((gc γ k)⁻¹ * gc γ (k + 1))).prod * f ((gc γ (Nc γ - 1))⁻¹ * γ) :=
    ⟨_, rfl⟩
  -- the chain-value export
  have hθval : ∀ (γ : ↥Γ) (αp : ℝ → ℂ) (N : ℕ) (g : ℕ → ↥Γ), Continuous αp →
      αp 0 = i₀ → αp 1 = moebiusMap (↑γ) i₀ → 0 < N →
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N → αp t ∈ V (g k)) →
      θ γ = f (g 0) * ((List.range (N - 1)).map fun k => f ((g k)⁻¹ * g (k + 1))).prod
        * f ((g (N - 1))⁻¹ * γ) := by
    intro γ αp N g hαc hα0 hα1 hN hsub
    rw [hθdef]
    refine (zz_homotopy V f hVsub hVopen hVcov hVtrans htrip hf1 (Pc γ) αp (hPccont γ) hαc
      ?_ ?_ γ (Nc γ) N (gc γ) g (hNc γ) hN (hsc γ) hsub ?_ ?_).symm
    · rw [hPc0, hα0]
    · rw [hPc1, hα1]
    · rw [hPc0]
      exact hi₀
    · rw [hPc1]
      exact hqmem γ
  -- the clamp to the unit interval
  obtain ⟨cl, hcldef⟩ : ∃ cl : ℝ → ℝ, cl = fun t => max 0 (min 1 t) := ⟨_, rfl⟩
  have hclval : ∀ t, cl t = max 0 (min 1 t) := fun t => by rw [hcldef]
  have hclcont : Continuous cl := by
    rw [hcldef]
    exact continuous_const.max (continuous_const.min continuous_id)
  have hcl01 : ∀ t, 0 ≤ cl t ∧ cl t ≤ 1 := by
    intro t
    rw [hclval]
    constructor
    · exact le_max_left _ _
    · rcases le_total 1 t with h | h
      · rw [min_eq_left h]
        exact max_le zero_le_one le_rfl
      · rcases le_total 0 t with h2 | h2
        · rw [min_eq_right h]
          exact max_le zero_le_one h
        · rw [max_eq_left]
          · exact zero_le_one
          · rw [min_eq_right h]
            exact h2
  have hclid : ∀ t, 0 ≤ t → t ≤ 1 → cl t = t := by
    intro t ht0 ht1
    rw [hclval, min_eq_right ht1, max_eq_right ht0]
  refine ⟨θ, ?_, ?_, ?_, hθval⟩
  · -- multiplicativity via the concatenated path
    intro γ δ
    obtain ⟨NN, hNNdef⟩ : ∃ NN : ℕ, NN = Nc γ * Nc δ := ⟨_, rfl⟩
    have hNNpos : 0 < NN := by
      rw [hNNdef]
      exact Nat.mul_pos (hNc γ) (hNc δ)
    -- refine both canonical chains to the common grid
    obtain ⟨g1, hg1def⟩ : ∃ g1 : ℕ → ↥Γ, g1 = fun k => gc γ (k / Nc δ) := ⟨_, rfl⟩
    obtain ⟨h1, hh1def⟩ : ∃ h1 : ℕ → ↥Γ, h1 = fun k => gc δ (k / Nc γ) := ⟨_, rfl⟩
    have hsubg1 : ∀ k < NN, ∀ t : ℝ, (k : ℝ) / NN ≤ t → t ≤ ((k : ℝ) + 1) / NN →
        Pc γ t ∈ V (g1 k) := by
      intro k hk t ht1 ht2
      rw [hg1def]
      rw [hNNdef] at hk ht1 ht2
      exact zz_refine_sub V (Nc γ) (Nc δ) (hNc γ) (hNc δ) (Pc γ) (gc γ) (hsc γ) k hk t ht1 ht2
    have hsubh1 : ∀ k < NN, ∀ t : ℝ, (k : ℝ) / NN ≤ t → t ≤ ((k : ℝ) + 1) / NN →
        Pc δ t ∈ V (h1 k) := by
      intro k hk t ht1 ht2
      rw [hh1def]
      have h := zz_refine_sub V (Nc δ) (Nc γ) (hNc δ) (hNc γ) (Pc δ) (gc δ) (hsc δ)
      rw [Nat.mul_comm (Nc δ) (Nc γ), ← hNNdef] at h
      exact h k hk t ht1 ht2
    -- the concatenated path
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ → ℂ, Q = fun s => if s ≤ 1 / 2 then Pc γ (cl (2 * s))
        else moebiusMap (↑γ) (Pc δ (cl (2 * s - 1))) := ⟨_, rfl⟩
    have hQval : ∀ s, Q s = if s ≤ 1 / 2 then Pc γ (cl (2 * s))
        else moebiusMap (↑γ) (Pc δ (cl (2 * s - 1))) := fun s => by rw [hQdef]
    have hQcont : Continuous Q := by
      rw [hQdef]
      refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact (hPccont γ).comp (hclcont.comp (continuous_const.mul continuous_id))
      · refine hmoebc γ _ ?_ ?_
        · exact (hPccont δ).comp (hclcont.comp ((continuous_const.mul continuous_id).sub
            continuous_const))
        · intro t
          exact hPcim δ _ (hcl01 _).1 (hcl01 _).2
      · intro s hs
        subst hs
        norm_num
        rw [hclid 1 zero_le_one le_rfl, hclid 0 le_rfl zero_le_one, hPc1, hPc0]
    have hQ0 : Q 0 = i₀ := by
      rw [hQval]
      rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 0 = 0 by ring, hclid 0 le_rfl zero_le_one, hPc0]
    have hQ1 : Q 1 = moebiusMap (↑(γ * δ)) i₀ := by
      rw [hQval]
      rw [if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 1 - 1 = 1 by ring, hclid 1 zero_le_one le_rfl, hPc1]
      have hden : moebiusDenom (↑δ) i₀ ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero (↑δ) (ne_of_gt hi₀im)
      have h := moebiusMap_mul (↑γ) (↑δ) i₀ hden
      rw [h]
      rfl
    -- the concatenated chain
    obtain ⟨cch, hcchdef⟩ : ∃ c : ℕ → ↥Γ, c = fun k => if k < NN then g1 k
        else γ * h1 (k - NN) := ⟨_, rfl⟩
    have hcchval : ∀ k, cch k = if k < NN then g1 k else γ * h1 (k - NN) :=
      fun k => by rw [hcchdef]
    have hNN2r : (0 : ℝ) < ((2 * NN : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) < (NN : ℝ) := by exact_mod_cast hNNpos
      linarith
    have hNNr : (0 : ℝ) < (NN : ℝ) := by exact_mod_cast hNNpos
    -- subordination of the concatenated chain on the doubled grid
    have hsubc : ∀ k < 2 * NN, ∀ t : ℝ, (k : ℝ) / (2 * NN : ℕ) ≤ t →
        t ≤ ((k : ℝ) + 1) / (2 * NN : ℕ) → Q t ∈ V (cch k) := by
      intro k hk t ht1 ht2
      by_cases hkN : k < NN
      · -- first half
        rw [hcchval, if_pos hkN]
        have ht2' : t ≤ 1 / 2 := by
          have h1 : ((k : ℝ) + 1) / (2 * NN : ℕ) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hNN2r (by norm_num : (0 : ℝ) < 2)]
            push_cast
            have : (k : ℝ) + 1 ≤ NN := by exact_mod_cast hkN
            nlinarith
          linarith
        rw [hQval, if_pos ht2']
        have ht0 : 0 ≤ t := le_trans (by positivity) ht1
        have h2t : cl (2 * t) = 2 * t := hclid _ (by linarith) (by linarith)
        rw [h2t]
        refine hsubg1 k hkN (2 * t) ?_ ?_
        · rw [div_le_iff₀ hNNr]
          rw [div_le_iff₀ hNN2r] at ht1
          push_cast at ht1
          linarith
        · rw [le_div_iff₀ hNNr]
          rw [le_div_iff₀ hNN2r] at ht2
          push_cast at ht2
          linarith
      · -- second half
        rw [hcchval, if_neg hkN]
        have hkN' : NN ≤ k := by omega
        have ht1' : 1 / 2 ≤ t := by
          have h1 : (1 : ℝ) / 2 ≤ (k : ℝ) / (2 * NN : ℕ) := by
            rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hNN2r]
            push_cast
            have : (NN : ℝ) ≤ k := by exact_mod_cast hkN'
            nlinarith
          linarith
        have hcast : ((k - NN : ℕ) : ℝ) = (k : ℝ) - NN := by
          push_cast [Nat.cast_sub hkN']
          ring
        have hmem : Pc δ (cl (2 * t - 1)) ∈ V (h1 (k - NN)) := by
          have h2t : cl (2 * t - 1) = 2 * t - 1 := by
            refine hclid _ ?_ ?_
            · linarith
            · have h2 : t ≤ ((k : ℝ) + 1) / (2 * NN : ℕ) := ht2
              have h3 : ((k : ℝ) + 1) / (2 * NN : ℕ) ≤ 1 := by
                rw [div_le_one hNN2r]
                push_cast
                have : (k : ℝ) + 1 ≤ 2 * NN := by exact_mod_cast hk
                linarith
              linarith
          rw [h2t]
          refine hsubh1 (k - NN) (by omega) (2 * t - 1) ?_ ?_
          · rw [hcast, div_le_iff₀ hNNr]
            rw [div_le_iff₀ hNN2r] at ht1
            push_cast at ht1
            linarith
          · rw [hcast, le_div_iff₀ hNNr]
            rw [le_div_iff₀ hNN2r] at ht2
            push_cast at ht2
            linarith
        have htrans := hVtrans γ (h1 (k - NN)) _ hmem
        by_cases hthalf : t ≤ 1 / 2
        · -- the boundary point: both branches have the same value
          have hteq : t = 1 / 2 := le_antisymm hthalf ht1'
          rw [hQval, if_pos hthalf]
          have hveq : Pc γ (cl (2 * t)) = moebiusMap (↑γ) (Pc δ (cl (2 * t - 1))) := by
            rw [hteq]
            norm_num
            rw [hclid 1 zero_le_one le_rfl, hclid 0 le_rfl zero_le_one, hPc1, hPc0]
          rw [hveq]
          exact htrans
        · rw [hQval, if_neg hthalf]
          exact htrans
    -- the three chain values
    have hval_gd := hθval (γ * δ) Q (2 * NN) cch hQcont hQ0 hQ1 (by omega) hsubc
    have hval_g := hθval γ (Pc γ) NN g1 (hPccont γ) (hPc0 γ) (hPc1 γ) hNNpos hsubg1
    have hval_h := hθval δ (Pc δ) NN h1 (hPccont δ) (hPc0 δ) (hPc1 δ) hNNpos hsubh1
    rw [hval_gd, hval_g, hval_h]
    -- endpoints of the concatenated chain
    obtain ⟨MM, hMM⟩ : ∃ MM, NN = MM + 1 := ⟨NN - 1, by omega⟩
    -- split the middle product
    have hsplit : (2 * NN - 1) = MM + (1 + MM) := by omega
    have hc0 : cch 0 = g1 0 := by
      rw [hcchval, if_pos hNNpos]
    have hclast : cch (MM + (1 + MM)) = γ * h1 MM := by
      rw [hcchval, if_neg (by omega)]
      congr 1
      congr 1
      omega
    have hcfirst : ∀ k, k < MM → cch k = g1 k ∧ cch (k + 1) = g1 (k + 1) := by
      intro k hkM
      constructor
      · rw [hcchval, if_pos (by omega)]
      · rw [hcchval, if_pos (by omega)]
    have hcmid : cch MM = g1 MM ∧ cch (MM + 1) = γ * h1 0 := by
      constructor
      · rw [hcchval, if_pos (by omega)]
      · rw [hcchval, if_neg (by omega)]
        congr 1
        congr 1
        omega
    have hcsecond : ∀ x, x < MM →
        cch (MM + (1 + x)) = γ * h1 x ∧ cch (MM + (1 + x) + 1) = γ * h1 (x + 1) := by
      intro x hxM
      constructor
      · rw [hcchval, if_neg (by omega)]
        congr 1
        congr 1
        omega
      · rw [hcchval, if_neg (by omega)]
        congr 1
        congr 1
        omega
    -- the product over the concatenated chain
    rw [hsplit, List.range_add, List.map_append, List.prod_append]
    have hprod1 : ((List.range MM).map fun k => f ((cch k)⁻¹ * cch (k + 1))).prod
        = ((List.range MM).map fun k => f ((g1 k)⁻¹ * g1 (k + 1))).prod := by
      refine congrArg List.prod (List.map_congr_left ?_)
      intro k hk
      have hkM := List.mem_range.mp hk
      rw [(hcfirst k hkM).1, (hcfirst k hkM).2]
    have hprod2 : ((List.map (fun k => f ((cch k)⁻¹ * cch (k + 1)))
        (List.map (fun x => MM + x) (List.range (1 + MM))))).prod
        = f ((g1 MM)⁻¹ * (γ * h1 0))
          * ((List.range MM).map fun k => f ((h1 k)⁻¹ * h1 (k + 1))).prod := by
      rw [show (1 + MM) = 1 + MM from rfl, List.range_add, List.map_append, List.map_append,
        List.prod_append, List.range_one]
      congr 1
      · simp only [List.map_singleton, List.prod_singleton, Nat.add_zero]
        rw [hcmid.1, hcmid.2]
      · refine congrArg List.prod ?_
        rw [List.map_map, List.map_map]
        refine List.map_congr_left ?_
        intro x hx
        have hxM := List.mem_range.mp hx
        simp only [Function.comp_apply]
        rw [(hcsecond x hxM).1, (hcsecond x hxM).2]
        rw [show (γ * h1 x)⁻¹ * (γ * h1 (x + 1)) = (h1 x)⁻¹ * h1 (x + 1) by group]
    rw [hprod1, hprod2, hc0, hclast]
    -- the junction identity
    have hjunc : f ((g1 MM)⁻¹ * (γ * h1 0)) = f ((g1 MM)⁻¹ * γ) * f (h1 0) := by
      have hmem1 : moebiusMap (↑γ) i₀ ∈ V (g1 MM) := by
        have hle1 : ((MM : ℝ)) / (NN : ℕ) ≤ 1 := by
          rw [div_le_one hNNr]
          have : (MM : ℝ) + 1 = NN := by exact_mod_cast hMM.symm
          linarith
        have hle2 : (1 : ℝ) ≤ ((MM : ℝ) + 1) / (NN : ℕ) := by
          rw [le_div_iff₀ hNNr]
          have : (MM : ℝ) + 1 = NN := by exact_mod_cast hMM.symm
          linarith
        have h := hsubg1 MM (by omega) 1 hle1 hle2
        rwa [hPc1] at h
      have hmem2 : moebiusMap (↑γ) i₀ ∈ V γ := hqmem γ
      have hmem3 : moebiusMap (↑γ) i₀ ∈ V (γ * h1 0) := by
        have h0m : Pc δ 0 ∈ V (h1 0) := by
          refine hsubh1 0 (by omega) 0 ?_ ?_
          · rw [Nat.cast_zero, zero_div]
          · rw [Nat.cast_zero, zero_add, le_div_iff₀ hNNr]
            linarith
        rw [hPc0] at h0m
        exact hVtrans γ (h1 0) i₀ h0m
      have h := zz_step V f hVtrans htrip (g1 MM) γ (γ * h1 0) (moebiusMap (↑γ) i₀)
        hmem1 hmem2 hmem3
      rw [show γ⁻¹ * (γ * h1 0) = h1 0 by group] at h
      exact h.symm
    rw [show (γ * h1 MM)⁻¹ * (γ * δ) = (h1 MM)⁻¹ * δ by group]
    rw [hjunc]
    -- final regrouping
    rw [show NN - 1 = MM by omega]
    simp only [← mul_assoc]
  · -- agreement with `f` on overlapping translates
    intro γ ⟨q, hq1, hqγ⟩
    have hqim' : 0 < q.im := hVsub 1 hq1
    have hq'mem : moebiusMap (↑(γ⁻¹ : ↥Γ)) q ∈ V 1 := by
      have h := hVtrans γ⁻¹ γ q hqγ
      rwa [inv_mul_cancel] at h
    -- two-leg path through the common point
    obtain ⟨L1, hL1def⟩ : ∃ L : ℝ → ℂ, L = fun (u : ℝ) => i₀ + (u : ℂ) * (q - i₀) :=
      ⟨fun (u : ℝ) => i₀ + (u : ℂ) * (q - i₀), rfl⟩
    obtain ⟨L2, hL2def⟩ : ∃ L : ℝ → ℂ,
        L = fun (u : ℝ) => moebiusMap (↑(γ⁻¹ : ↥Γ)) q
          + (u : ℂ) * (i₀ - moebiusMap (↑(γ⁻¹ : ↥Γ)) q) :=
      ⟨fun (u : ℝ) => moebiusMap (↑(γ⁻¹ : ↥Γ)) q
        + (u : ℂ) * (i₀ - moebiusMap (↑(γ⁻¹ : ↥Γ)) q), rfl⟩
    have hL1mem : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → L1 u ∈ V 1 := by
      intro u hu0 hu1
      rw [hL1def]
      have h := hV1conv hi₀ hq1 (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
      have heq : (1 - u) • i₀ + u • q = i₀ + (u : ℂ) * (q - i₀) := by
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rwa [heq] at h
    have hL2mem : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → L2 u ∈ V 1 := by
      intro u hu0 hu1
      rw [hL2def]
      have h := hV1conv hq'mem hi₀ (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
      have heq : (1 - u) • moebiusMap (↑(γ⁻¹ : ↥Γ)) q + u • i₀
          = moebiusMap (↑(γ⁻¹ : ↥Γ)) q + (u : ℂ) * (i₀ - moebiusMap (↑(γ⁻¹ : ↥Γ)) q) := by
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring
      rwa [heq] at h
    have hL1cont : Continuous L1 := by
      rw [hL1def]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hL2cont : Continuous L2 := by
      rw [hL2def]
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ → ℂ, Q = fun s => if s ≤ 1 / 2 then L1 (cl (2 * s))
        else moebiusMap (↑γ) (L2 (cl (2 * s - 1))) := ⟨_, rfl⟩
    have hQval : ∀ s, Q s = if s ≤ 1 / 2 then L1 (cl (2 * s))
        else moebiusMap (↑γ) (L2 (cl (2 * s - 1))) := fun s => by rw [hQdef]
    have hL10 : L1 0 = i₀ := by
      rw [hL1def]
      push_cast
      ring
    have hL11 : L1 1 = q := by
      rw [hL1def]
      push_cast
      ring
    have hL20 : L2 0 = moebiusMap (↑(γ⁻¹ : ↥Γ)) q := by
      rw [hL2def]
      push_cast
      ring
    have hL21 : L2 1 = i₀ := by
      rw [hL2def]
      push_cast
      ring
    have hglue : moebiusMap (↑γ) (L2 0) = q := by
      rw [hL20]
      have hden : moebiusDenom (↑(γ⁻¹ : ↥Γ)) q ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hqim')
      have h := moebiusMap_mul (↑γ) (↑(γ⁻¹ : ↥Γ)) q hden
      have hcoe : (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (↑(γ⁻¹ : ↥Γ)) = 1 := by
        push_cast
        group
      rw [hcoe] at h
      rw [h, moebiusMap_one]
    have hQcont : Continuous Q := by
      rw [hQdef]
      refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact hL1cont.comp (hclcont.comp (continuous_const.mul continuous_id))
      · refine hmoebc γ _ ?_ ?_
        · exact hL2cont.comp (hclcont.comp ((continuous_const.mul continuous_id).sub
            continuous_const))
        · intro t
          exact hVsub 1 (hL2mem _ (hcl01 _).1 (hcl01 _).2)
      · intro s hs
        subst hs
        norm_num
        rw [hclid 1 zero_le_one le_rfl, hclid 0 le_rfl zero_le_one, hL11, hglue]
    have hQ0 : Q 0 = i₀ := by
      rw [hQval, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 0 = 0 by ring, hclid 0 le_rfl zero_le_one, hL10]
    have hQ1 : Q 1 = moebiusMap (↑γ) i₀ := by
      rw [hQval, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
      rw [show (2 : ℝ) * 1 - 1 = 1 by ring, hclid 1 zero_le_one le_rfl, hL21]
    -- the two-slot chain
    obtain ⟨g2, hg2def⟩ : ∃ g : ℕ → ↥Γ, g = fun k => if k = 0 then 1 else γ := ⟨_, rfl⟩
    have hsub2 : ∀ k : ℕ, k < 2 → ∀ t : ℝ, (k : ℝ) / ((2 : ℕ) : ℝ) ≤ t →
        t ≤ ((k : ℝ) + 1) / ((2 : ℕ) : ℝ) → Q t ∈ V (g2 k) := by
      intro k hk t ht1 ht2
      have h20 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h20] at ht1 ht2
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [hg2def]
        simp only [reduceIte]
        push_cast at ht1 ht2
        have ht2' : t ≤ 1 / 2 := by linarith
        rw [hQval, if_pos ht2']
        exact hL1mem _ (hcl01 _).1 (hcl01 _).2
      · rw [hg2def]
        simp only [if_neg (by omega : ¬ (1 : ℕ) = 0)]
        push_cast at ht1 ht2
        by_cases hthalf : t ≤ 1 / 2
        · have hteq : t = 1 / 2 := le_antisymm hthalf (by linarith)
          rw [hQval, if_pos hthalf, hteq]
          norm_num
          rw [hclid 1 zero_le_one le_rfl, hL11]
          exact hqγ
        · rw [hQval, if_neg hthalf]
          have h := hL2mem (cl (2 * t - 1)) (hcl01 _).1 (hcl01 _).2
          have htr := hVtrans γ 1 _ h
          rwa [mul_one] at htr
    have hval := hθval γ Q 2 g2 hQcont hQ0 hQ1 (by omega) hsub2
    rw [hval, hg2def]
    norm_num
    rw [hf1, one_mul, mul_one]
  · -- membership
    intro S hfS γ
    rw [hθdef]
    refine mul_mem (mul_mem (hfS _) ?_) (hfS _)
    refine Subgroup.list_prod_mem S ?_
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hfS _

/-- Chain values of a group homomorphism telescope to the target. -/
private lemma zz_telescope {H K : Type} [Group H] [Group K] (c : H →* K)
    (N : ℕ) (hN : 0 < N) (g : ℕ → H) (γt : H) :
    c (g 0) * ((List.range (N - 1)).map fun k => c ((g k)⁻¹ * g (k + 1))).prod
      * c ((g (N - 1))⁻¹ * γt) = c γt := by
  have key : ∀ M : ℕ, c (g 0) * ((List.range M).map fun k => c ((g k)⁻¹ * g (k + 1))).prod
      = c (g M) := by
    intro M
    induction M with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.prod_nil, mul_one]
    | succ M ih =>
      rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, ← mul_assoc, ih, ← map_mul]
      congr 1
      group
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [key M, ← map_mul]
  congr 1
  group

/-- Two sequences in trace-gapped groups converging to a common limit in
`SL(2, ℝ)` are eventually equal: they are eventually equal up to sign, and the sign is
excluded by convergence at a nonvanishing entry of the limit. -/
private lemma zz_ev_eq {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hgap : ∀ n, ∀ γ ∈ Γ n, actsNontrivially γ →
      2 * Real.cosh (ε / 2) ≤ |Matrix.trace (γ : Matrix (Fin 2) (Fin 2) ℝ)|)
    {a b : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (ha : ∀ n, a n ∈ Γ n) (hb : ∀ n, b n ∈ Γ n)
    {L : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hla : Filter.Tendsto a Filter.atTop (nhds L))
    (hlb : Filter.Tendsto b Filter.atTop (nhds L)) :
    ∀ᶠ n in Filter.atTop, a n = b n := by
  -- a nonvanishing entry of the limit
  have hLne : ∃ i j : Fin 2, (L : Matrix (Fin 2) (Fin 2) ℝ) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hdet : (L : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := Matrix.SpecialLinearGroup.det_coe L
    rw [Matrix.det_fin_two, hcon 0 0, hcon 0 1] at hdet
    norm_num at hdet
  obtain ⟨i, j, hij⟩ := hLne
  have hev := eventually_eq_up_to_sign_of_tendsto hε Γ hgap ha hb hla hlb
  -- entrywise convergence at the distinguished entry
  have hentry : ∀ (c : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      Filter.Tendsto c Filter.atTop (nhds L) →
      ∀ᶠ n in Filter.atTop,
        |(c n : Matrix (Fin 2) (Fin 2) ℝ) i j - (L : Matrix (Fin 2) (Fin 2) ℝ) i j|
          < |(L : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
    intro c hc
    have hmat : Filter.Tendsto (fun n => (c n : Matrix (Fin 2) (Fin 2) ℝ)) Filter.atTop
        (nhds (L : Matrix (Fin 2) (Fin 2) ℝ)) := tendsto_subtype_rng.mp hc
    have hent : Filter.Tendsto (fun n => (c n : Matrix (Fin 2) (Fin 2) ℝ) i j) Filter.atTop
        (nhds ((L : Matrix (Fin 2) (Fin 2) ℝ) i j)) := by
      have hcontinuous : Continuous fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j :=
        continuous_apply_apply i j
      exact (hcontinuous.tendsto _).comp hmat
    have habs : Filter.Tendsto (fun n =>
        |(c n : Matrix (Fin 2) (Fin 2) ℝ) i j - (L : Matrix (Fin 2) (Fin 2) ℝ) i j|)
        Filter.atTop (nhds 0) := by
      have h := hent.sub (tendsto_const_nhds
        (x := (L : Matrix (Fin 2) (Fin 2) ℝ) i j) (f := Filter.atTop))
      rw [sub_self] at h
      have habs0 : |(0 : ℝ)| = 0 := abs_zero
      exact habs0 ▸ h.abs
    exact habs.eventually_lt_const (abs_pos.mpr hij)
  filter_upwards [hev, hentry a hla, hentry b hlb] with n hn hna hnb
  rcases hn with h | h
  · exact h
  · exfalso
    have hbij := congrFun (congrFun h i) j
    rw [Matrix.neg_apply] at hbij
    rcases lt_or_gt_of_ne hij with hL | hL
    · rw [abs_of_neg hL] at hna hnb
      have h1 := abs_lt.mp hna
      have h2 := abs_lt.mp hnb
      linarith [h1.1, h1.2, h2.1, h2.2, hbij]
    · rw [abs_of_pos hL] at hna hnb
      have h1 := abs_lt.mp hna
      have h2 := abs_lt.mp hnb
      linarith [h1.1, h1.2, h2.1, h2.2, hbij]

/-- Chain values converge entrywise along converging local data. -/
private lemma zz_val_tendsto {H : Type} [Group H]
    (t : ℕ → H → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (c : H → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hconv : ∀ x : H, Filter.Tendsto (fun n => t n x) Filter.atTop (nhds (c x)))
    (N : ℕ) (g : ℕ → H) (γt : H) :
    Filter.Tendsto (fun n => t n (g 0) * ((List.range (N - 1)).map
        fun k => t n ((g k)⁻¹ * g (k + 1))).prod * t n ((g (N - 1))⁻¹ * γt))
      Filter.atTop (nhds (c (g 0) * ((List.range (N - 1)).map
        fun k => c ((g k)⁻¹ * g (k + 1))).prod * c ((g (N - 1))⁻¹ * γt))) := by
  have hprod : ∀ M : ℕ, Filter.Tendsto (fun n => ((List.range M).map
      fun k => t n ((g k)⁻¹ * g (k + 1))).prod) Filter.atTop
      (nhds (((List.range M).map fun k => c ((g k)⁻¹ * g (k + 1))).prod)) := by
    intro M
    induction M with
    | zero =>
      simp only [List.range_zero, List.map_nil, List.prod_nil]
      exact tendsto_const_nhds
    | succ M ih =>
      simp only [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton]
      exact ih.mul (hconv _)
  exact ((hconv (g 0)).mul (hprod (N - 1))).mul (hconv _)

/-- The bump atom at a hyperbolic center: value, bridge, and differentiability. -/
private lemma zz_atom_bridge (gb : ℝ → ℝ) (w : UpperHalfPlane) (τ : UpperHalfPlane) :
    gb (1 + Complex.normSq ((τ : ℂ) - (w : ℂ)) / (2 * (τ : ℂ).im * (w : ℂ).im))
      = gb (Real.cosh (dist τ w)) := by
  rw [zz_cd_bridge]

/-- Differentiability of the bump atom on the upper half plane. -/
private lemma zz_atom_contDiffAt (gb : ℝ → ℝ) (hgb : ContDiff ℝ 1 gb)
    (w : UpperHalfPlane) (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    ContDiffAt ℝ 1 (fun z : ℂ =>
      gb (1 + Complex.normSq (z - (w : ℂ)) / (2 * z.im * (w : ℂ).im))) z₀ := by
  have hwim : 0 < (w : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    exact w.im_pos
  exact hgb.contDiffAt.comp z₀ (zz_cd_contDiffAt (w : ℂ) hwim z₀ hz₀)

/-- Vanishing of the bump atom away from its center, for a profile vanishing above
`cosh (R + 1)`. -/
private lemma zz_atom_vanish (gb : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hgb0 : ∀ t : ℝ, Real.cosh (R + 1) ≤ t → gb t = 0)
    (w τ : UpperHalfPlane) (hfar : R + 1 ≤ dist τ w) :
    gb (1 + Complex.normSq ((τ : ℂ) - (w : ℂ)) / (2 * (τ : ℂ).im * (w : ℂ).im)) = 0 := by
  rw [zz_atom_bridge gb w τ]
  refine hgb0 _ ?_
  have h1 : |R + 1| ≤ |dist τ w| := by
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1)]
    exact hfar
  exact Real.cosh_le_cosh.mpr h1

/-- **Local finiteness of the bump family**: around each point of the upper half plane there
is a Euclidean ball on which all but finitely many atoms vanish identically. -/
private lemma zz_locfin {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsianGroup Γ) (τ₀ : UpperHalfPlane) (R : ℝ)
    (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Set ↥Γ, F.Finite ∧
      (∀ z ∈ Metric.ball z₀ r, 0 < z.im) ∧
      ∀ z ∈ Metric.ball z₀ r, ∀ hz : 0 < z.im, ∀ γ : ↥Γ, γ ∉ F →
        R + 1 ≤ dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by
  classical
  -- the hyperbolic unit ball about `z₀` is an open Euclidean ball containing `z₀`
  obtain ⟨τz, hτz⟩ : ∃ τz : UpperHalfPlane, (τz : ℂ) = z₀ := ⟨⟨z₀, hz₀⟩, rfl⟩
  have hz₀mem : z₀ ∈ Metric.ball ((((τz : ℂ).re : ℝ) : ℂ)
      + ((τz.im * Real.cosh 1 : ℝ) : ℂ) * Complex.I) (τz.im * Real.sinh 1) := by
    rw [zz_ball τz 1 one_pos z₀]
    refine ⟨hz₀, ?_⟩
    have : (⟨z₀, hz₀⟩ : UpperHalfPlane) = τz := by
      ext
      rw [hτz]
    rw [this]
    rw [dist_self]
    norm_num
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r > 0, Metric.ball z₀ r ⊆ Metric.ball ((((τz : ℂ).re : ℝ) : ℂ)
      + ((τz.im * Real.cosh 1 : ℝ) : ℂ) * Complex.I) (τz.im * Real.sinh 1) :=
    Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hz₀mem)
  refine ⟨r, hrpos, {γ : ↥Γ | dist τz (γ • τ₀) ≤ R + 2}, zz_fin hΓ τz τ₀ (R + 2), ?_, ?_⟩
  · intro z hz
    have hzE := hrsub hz
    rw [zz_ball τz 1 one_pos z] at hzE
    obtain ⟨hzim, _⟩ := hzE
    exact hzim
  · intro z hz hzim γ hγF
    by_contra hcon
    push Not at hcon
    have hzE := hrsub hz
    rw [zz_ball τz 1 one_pos z] at hzE
    obtain ⟨hzim', hzd⟩ := hzE
    apply hγF
    have htri : dist τz (γ • τ₀) ≤ dist τz (⟨z, hzim'⟩ : UpperHalfPlane)
        + dist (⟨z, hzim'⟩ : UpperHalfPlane) (γ • τ₀) := dist_triangle _ _ _
    have heq : dist (⟨z, hzim'⟩ : UpperHalfPlane) (γ • τ₀)
        = dist (⟨z, hzim⟩ : UpperHalfPlane) (γ • τ₀) := rfl
    have hd1 : dist τz (⟨z, hzim'⟩ : UpperHalfPlane) < 1 := by
      rw [dist_comm]
      exact hzd
    simp only [Set.mem_setOf_eq]
    rw [heq] at htri
    linarith

/-- Wirtinger bounds from a split of the derivative into a near-identity complex-linear part
and small error values in the two coordinate directions. -/
private lemma zz_wirt (F : ℂ → ℂ) (z : ℂ) (Sw e1 eI : ℂ) (Cb : ℝ)
    (hα : fderiv ℝ F z 1 = Sw + e1) (hβ : fderiv ℝ F z Complex.I = Sw * Complex.I + eI)
    (hSw1 : ‖Sw - 1‖ ≤ Cb) (he1 : ‖e1‖ ≤ Cb) (heI : ‖eI‖ ≤ Cb) (hCb : 0 ≤ Cb)
    (hsm : Cb ≤ 1 / 6) :
    ‖dzbar F z‖ ≤ Cb ∧ (1 : ℝ) / 2 ≤ ‖dz F z‖ ∧ 0 < (fderiv ℝ F z).det := by
  have hdzbar_eq : dzbar F z = (1 / 2 : ℂ) * (e1 + Complex.I * eI) := by
    rw [dzbar, hα, hβ]
    linear_combination (Sw / 2) * Complex.I_mul_I
  have hdz_eq : dz F z = Sw + (1 / 2 : ℂ) * (e1 - Complex.I * eI) := by
    rw [dz, hα, hβ]
    linear_combination (-(Sw / 2)) * Complex.I_mul_I
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  have hIeI : ‖Complex.I * eI‖ = ‖eI‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hbar : ‖dzbar F z‖ ≤ Cb := by
    rw [hdzbar_eq, norm_mul, hhalf]
    have h1 := norm_add_le e1 (Complex.I * eI)
    rw [hIeI] at h1
    have h2 : ‖e1 + Complex.I * eI‖ ≤ 2 * Cb := by linarith only [h1, he1, heI]
    linarith only [h2, norm_nonneg (e1 + Complex.I * eI), hCb]
  have hSlb : 1 - Cb ≤ ‖Sw‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) Sw
    rw [norm_one, norm_sub_rev] at h1
    linarith only [h1, hSw1]
  have hzlb : (1 : ℝ) / 2 ≤ ‖dz F z‖ := by
    rw [hdz_eq]
    have h1 := norm_sub_norm_le Sw (-((1 / 2 : ℂ) * (e1 - Complex.I * eI)))
    rw [sub_neg_eq_add, norm_neg, norm_mul, hhalf] at h1
    have h2 := norm_sub_le e1 (Complex.I * eI)
    rw [hIeI] at h2
    have h3 : ‖e1 - Complex.I * eI‖ ≤ 2 * Cb := by linarith only [h2, he1, heI]
    have h4 : 1 / 2 * ‖e1 - Complex.I * eI‖ ≤ Cb := by
      linarith only [h3, norm_nonneg (e1 - Complex.I * eI), hCb]
    have h5 : Cb + Cb ≤ 1 / 3 := by linarith only [hsm]
    linarith only [h1, h4, hSlb, h5]
  refine ⟨hbar, hzlb, ?_⟩
  rw [det_fderiv_eq_wirtinger]
  have h6 : ‖dzbar F z‖ ^ 2 ≤ Cb ^ 2 := by
    have := mul_le_mul hbar hbar (norm_nonneg _) hCb
    nlinarith [this]
  have h7 : (1 : ℝ) / 4 ≤ ‖dz F z‖ ^ 2 := by
    have := mul_le_mul hzlb hzlb (by norm_num) (le_trans (by norm_num) hzlb)
    nlinarith [this]
  have h8 : Cb ^ 2 ≤ 1 / 36 := by nlinarith [hsm, hCb]
  nlinarith [h6, h7, h8]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The derivative chain of the coefficient Möbius quotient elaborates one large product and
-- inverse rule; the default heartbeat budget does not cover it.
/-- Fréchet differentiability and the derivative formula for a Möbius quotient with `C¹`
real coefficient fields, off the zero set of the denominator. -/
private lemma zz_moeb_core
    (b00 b01 b10 b11 : ℂ → ℝ) (D00 D01 D10 D11 : ℂ →L[ℝ] ℝ) (z : ℂ)
    (hD00 : HasFDerivAt b00 D00 z) (hD01 : HasFDerivAt b01 D01 z)
    (hD10 : HasFDerivAt b10 D10 z) (hD11 : HasFDerivAt b11 D11 z)
    (hdenne' : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) ≠ 0) :
    DifferentiableAt ℝ
        (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z ∧
      ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
        = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ)
            / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 * v
          + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))
                * (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ))
              - (((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
                * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ)))
            / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 := by
  haveI hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  -- the derivative chain, following the collar-estimate pattern
  have h00 : HasFDerivAt (fun w : ℂ => ((b00 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D00) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD00
  have h01 : HasFDerivAt (fun w : ℂ => ((b01 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D01) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD01
  have h10 : HasFDerivAt (fun w : ℂ => ((b10 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D10) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD10
  have h11 : HasFDerivAt (fun w : ℂ => ((b11 w : ℝ) : ℂ)) (Complex.ofRealCLM.comp D11) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hD11
  have hchain := ((h00.mul (hasFDerivAt_id z)).add h01).mul
    ((hasDerivAt_inv hdenne').comp_hasFDerivAt z ((h10.mul (hasFDerivAt_id z)).add h11))
  have hfeq : (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ)))
      = fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        * ((((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))⁻¹) := by
    funext w
    rw [div_eq_mul_inv]
  have hφex : HasFDerivAt (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        * ((((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))⁻¹))
      ((((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ)) •
          ((-((((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2)⁻¹) •
            (((b10 z : ℝ) : ℂ) • ContinuousLinearMap.id ℝ ℂ
              + z • Complex.ofRealCLM.comp D10 + Complex.ofRealCLM.comp D11))
        + (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ))⁻¹ •
            (((b00 z : ℝ) : ℂ) • ContinuousLinearMap.id ℝ ℂ
              + z • Complex.ofRealCLM.comp D00 + Complex.ofRealCLM.comp D01)) z := hchain
  have hdiff : DifferentiableAt ℝ
      (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z := by
    rw [hfeq]
    exact hφex.differentiableAt
  have hfd0 : fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z
      = fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
        * ((((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))⁻¹)) z := by
    rw [hfeq]
  have hfd1 := hφex.differentiableAt.hasFDerivAt.unique hφex
  -- the linear-map value of the derivative
  have hLv : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ)
          / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 * v
        + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))
              * (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ))
            - (((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
              * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ)))
          / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) ^ 2 := by
    intro v
    rw [hfd0, hfd1]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    field_simp
    push_cast
    ring
  exact ⟨hdiff, hLv⟩

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The per-point value and operator-norm package elaborates one large derivative chain;
-- the default heartbeat budget does not cover it.
/-- **Value and derivative closeness to the identity for a Möbius map with near-identity
`C¹` coefficient field**, with explicit polynomial constants. -/
private lemma zz_moeb_packA
    (b00 b01 b10 b11 : ℂ → ℝ) (D00 D01 D10 D11 : ℂ →L[ℝ] ℝ) (z : ℂ)
    (Rz ε : ℝ) (hRz : 1 ≤ Rz) (hzR : ‖z‖ ≤ Rz)
    (hD00 : HasFDerivAt b00 D00 z) (hD01 : HasFDerivAt b01 D01 z)
    (hD10 : HasFDerivAt b10 D10 z) (hD11 : HasFDerivAt b11 D11 z)
    (hε : 0 ≤ ε)
    (hb00 : |b00 z - 1| ≤ ε) (hb01 : |b01 z| ≤ ε)
    (hb10 : |b10 z| ≤ ε) (hb11 : |b11 z - 1| ≤ ε)
    (hn00 : ‖D00‖ ≤ ε) (hn01 : ‖D01‖ ≤ ε) (hn10 : ‖D10‖ ≤ ε) (hn11 : ‖D11‖ ≤ ε)
    (hsmall : ε * Rz ^ 2 ≤ 1 / 1000) :
    DifferentiableAt ℝ
        (fun wq => (((b00 wq : ℝ) : ℂ) * wq + ((b01 wq : ℝ) : ℂ))
          / (((b10 wq : ℝ) : ℂ) * wq + ((b11 wq : ℝ) : ℂ))) z ∧
      ‖(((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
          / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) - z‖ ≤ 8 * Rz ^ 2 * ε ∧
      ‖fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z
        - ContinuousLinearMap.id ℝ ℂ‖ ≤ 64 * Rz ^ 2 * ε := by
  haveI hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  have hεRz : ε * Rz ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (mul_nonneg
      (by linarith : (0 : ℝ) ≤ Rz - 1) (by linarith : (0 : ℝ) ≤ Rz))]
  have hε1 : ε ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (by nlinarith : (0 : ℝ) ≤ Rz ^ 2 - 1)]
  have hRz0 : (0 : ℝ) < Rz := by linarith
  -- basic denominator and numerator bounds
  obtain ⟨den, hden_def⟩ : ∃ x : ℂ, ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  obtain ⟨num, hnum_def⟩ : ∃ x : ℂ, ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  have hden1 : ‖den - 1‖ ≤ 2 * ε * Rz := by
    rw [← hden_def]
    have h1 : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) - 1
        = ((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ)‖
        ≤ ‖((b10 z : ℝ) : ℂ) * z‖ + ‖((b11 z - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b10 z| * ‖z‖ + |b11 z - 1| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb10 hzR (norm_nonneg z) hε) ?_
          calc |b11 z - 1| ≤ ε := hb11
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hdenlb : (1 : ℝ) / 2 ≤ ‖den‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) den
    rw [norm_one, norm_sub_rev] at h1
    nlinarith [hden1, hεRz]
  have hdenub : ‖den‖ ≤ 3 / 2 := by
    have h1 := norm_add_le (den - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    nlinarith [hden1, hεRz]
  have hdenne : den ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenlb
    linarith
  have hdenne' : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) ≠ 0 := by
    rw [hden_def]
    exact hdenne
  have hnumz : ‖num - z‖ ≤ 2 * ε * Rz := by
    rw [← hnum_def]
    have h1 : ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) - z
        = ((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ)‖
        ≤ ‖((b00 z - 1 : ℝ) : ℂ) * z‖ + ‖((b01 z : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b00 z - 1| * ‖z‖ + |b01 z| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb00 hzR (norm_nonneg z) hε) ?_
          calc |b01 z| ≤ ε := hb01
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hnumub : ‖num‖ ≤ 2 * Rz := by
    have h1 := norm_add_le (num - z) z
    rw [sub_add_cancel] at h1
    nlinarith [hnumz, hεRz, hzR]
  obtain ⟨hdiff, hLvraw⟩ := zz_moeb_core b00 b01 b10 b11 D00 D01 D10 D11 z
    hD00 hD01 hD10 hD11 hdenne'
  have hLv : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 * v
        + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
            - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
    intro v
    rw [hLvraw v, hden_def, hnum_def]
  clear hLvraw hD00 hD01 hD10 hD11
  -- bounds for the two parts  -- bounds for the two parts
  obtain ⟨Sw, hSw_def⟩ : ∃ x : ℂ, ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 = x :=
    ⟨_, rfl⟩
  have hdet1 : |b00 z * b11 z - b01 z * b10 z - 1| ≤ 4 * ε := by
    have e1 : b00 z * b11 z - b01 z * b10 z - 1
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z := by ring
    rw [e1]
    have h1 : |(b00 z - 1) * (b11 z - 1)| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb00 hb11 (abs_nonneg _) hε
    have h2 : |b01 z * b10 z| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb01 hb10 (abs_nonneg _) hε
    have h3 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1))
      (-(b01 z * b10 z))
    rw [abs_neg] at h3
    have h4 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1)) (b11 z - 1)
    have h5 := abs_add_le ((b00 z - 1) * (b11 z - 1)) (b00 z - 1)
    have hee : ε * ε ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (by linarith only [hε1] : ε ≤ 1) hε
      linarith only [h]
    have hgoal : (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z) := by
      ring
    rw [hgoal]
    calc |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z)|
        ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1)| + |b01 z * b10 z| := h3
      _ ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1)| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h4]
      _ ≤ |(b00 z - 1) * (b11 z - 1)| + |b00 z - 1| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h5]
      _ ≤ ε * ε + ε + ε + ε * ε := by linarith [h1, h2, hb00, hb11]
      _ ≤ 4 * ε := by linarith [hee]
  have hden2lb : (1 : ℝ) / 4 ≤ ‖den ^ 2‖ := by
    rw [norm_pow]
    nlinarith [hdenlb, norm_nonneg den]
  have hden2ne : den ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
  have hSw1 : ‖Sw - 1‖ ≤ 36 * ε * Rz := by
    rw [← hSw_def]
    have e1 : ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 - 1
        = (((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)) / den ^ 2 := by
      field_simp
      push_cast
      ring
    rw [e1, norm_div]
    have h1 : ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
        ≤ 4 * ε + 5 * ε * Rz := by
      have h2 : ‖den ^ 2 - 1‖ ≤ 5 * ε * Rz := by
        have e2 : den ^ 2 - 1 = (den - 1) * (den + 1) := by ring
        rw [e2, norm_mul]
        have h3 : ‖den + 1‖ ≤ 5 / 2 := by
          have := norm_add_le den (1 : ℂ)
          rw [norm_one] at this
          linarith [hdenub]
        calc ‖den - 1‖ * ‖den + 1‖ ≤ (2 * ε * Rz) * (5 / 2) :=
              mul_le_mul hden1 h3 (norm_nonneg _) (by positivity)
          _ = 5 * ε * Rz := by ring
      calc ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
          ≤ ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ)‖ + ‖den ^ 2 - 1‖ :=
            norm_sub_le _ _
        _ ≤ 4 * ε + 5 * ε * Rz := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            linarith [hdet1, h2]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h4 : 36 * ε * Rz * (1 / 4) ≤ 36 * ε * Rz * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    have h5 : 4 * ε + 5 * ε * Rz ≤ 9 * ε * Rz := by nlinarith
    linarith
  -- the error part of the derivative
  have hEbound : ∀ v : ℂ, ‖((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
      - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖
      ≤ 28 * Rz ^ 2 * ε * ‖v‖ := by
    intro v
    have hDnum : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖
          ≤ ‖((D00 v : ℝ) : ℂ) * z‖ + ‖((D01 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D00 v| * ‖z‖ + |D01 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D00 v| ≤ ‖D00‖ * ‖v‖ := D00.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn00 (norm_nonneg v)
            · calc |D01 v| ≤ ‖D01‖ * ‖v‖ := D01.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn01 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    have hDden : ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖((D10 v : ℝ) : ℂ) * z‖ + ‖((D11 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D10 v| * ‖z‖ + |D11 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D10 v| ≤ ‖D10‖ * ‖v‖ := D10.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn10 (norm_nonneg v)
            · calc |D11 v| ≤ ‖D11‖ * ‖v‖ := D11.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn11 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    rw [norm_div]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h1 : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
        ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den‖
            + ‖num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
            rw [norm_mul, norm_mul]
            refine add_le_add ?_ ?_
            · exact mul_le_mul hDnum hdenub (norm_nonneg _) (by positivity)
            · exact mul_le_mul hnumub hDden (norm_nonneg _) (by positivity)
    have h2 : 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖)
        ≤ 7 * ε * Rz ^ 2 * ‖v‖ := by
      nlinarith [norm_nonneg v, hε, hRz0,
        mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz ^ 2 - Rz))
          (norm_nonneg v)]
    have h3 : 28 * Rz ^ 2 * ε * ‖v‖ * (1 / 4) ≤ 28 * Rz ^ 2 * ε * ‖v‖ * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    obtain ⟨X, hX⟩ : ∃ x : ℝ, ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ = x := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ x : ℝ, ‖v‖ = x := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ x : ℝ, ‖den ^ 2‖ = x := ⟨_, rfl⟩
    rw [hX] at h1 ⊢
    rw [hY] at h1 h2 h3 ⊢
    rw [hDq] at h3 ⊢
    linarith [h1, h2, h3]
  -- rewrite the scalar part
  have hLv' : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = Sw * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
    intro v
    rw [hLv v, ← hSw_def]
  -- value bound
  have hval : ‖(((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ))
      / (((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ)) - z‖ ≤ 8 * Rz ^ 2 * ε := by
    rw [hnum_def, hden_def]
    have e1 : num / den - z = (num - z * den) / den := by
      field_simp
    rw [e1, norm_div]
    have h1 : ‖num - z * den‖ ≤ 4 * ε * Rz ^ 2 := by
      have e2 : num - z * den = (num - z) - z * (den - 1) := by ring
      rw [e2]
      calc ‖(num - z) - z * (den - 1)‖ ≤ ‖num - z‖ + ‖z * (den - 1)‖ := norm_sub_le _ _
        _ ≤ 2 * ε * Rz + Rz * (2 * ε * Rz) := by
            rw [norm_mul]
            exact add_le_add hnumz (mul_le_mul hzR hden1 (norm_nonneg _) (by positivity))
        _ ≤ 4 * ε * Rz ^ 2 := by
            nlinarith [mul_nonneg hε (mul_nonneg
              (by linarith : (0 : ℝ) ≤ Rz - 1) (by linarith : (0 : ℝ) ≤ Rz))]
    rw [div_le_iff₀ (by linarith [hdenlb] : (0 : ℝ) < ‖den‖)]
    have h2 : 8 * Rz ^ 2 * ε * (1 / 2) ≤ 8 * Rz ^ 2 * ε * ‖den‖ := by
      refine mul_le_mul_of_nonneg_left hdenlb ?_
      positivity
    linarith [h1, h2]
  -- operator-norm bound for the difference to the identity
  have hopn : ‖fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z
      - ContinuousLinearMap.id ℝ ℂ‖ ≤ 64 * Rz ^ 2 * ε := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro v
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hLv' v]
    have e1 : Sw * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 - v
        = (Sw - 1) * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
      ring
    rw [e1]
    calc ‖(Sw - 1) * v + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖
        ≤ ‖(Sw - 1) * v‖ + ‖((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖ := norm_add_le _ _
      _ ≤ 36 * ε * Rz * ‖v‖ + 28 * Rz ^ 2 * ε * ‖v‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hSw1 (norm_nonneg v)) (hEbound v)
      _ ≤ 64 * Rz ^ 2 * ε * ‖v‖ := by
          obtain ⟨Y, hY⟩ : ∃ x : ℝ, ‖v‖ = x := ⟨_, rfl⟩
          have hY0 : 0 ≤ Y := hY ▸ norm_nonneg v
          rw [hY]
          have hRz2 : (0 : ℝ) ≤ Rz ^ 2 - Rz := by
            have h := mul_nonneg (by linarith only [hRz] : (0 : ℝ) ≤ Rz - 1)
              (by linarith only [hRz] : (0 : ℝ) ≤ Rz)
            nlinarith [h]
          have hprod : 0 ≤ ε * (Rz ^ 2 - Rz) * Y := mul_nonneg (mul_nonneg hε hRz2) hY0
          nlinarith [hprod]
  exact ⟨hdiff, hval, hopn⟩

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The per-point Wirtinger bounds elaborate one large derivative chain; the default
-- heartbeat budget does not cover it.
/-- **Wirtinger bounds for a Möbius map with near-identity `C¹` coefficient field**: an
upper bound for the conjugate-linear part, a lower bound for the complex-linear part, and
positivity of the Jacobian, with explicit polynomial constants. -/
private lemma zz_moeb_packB
    (b00 b01 b10 b11 : ℂ → ℝ) (D00 D01 D10 D11 : ℂ →L[ℝ] ℝ) (z : ℂ)
    (Rz ε : ℝ) (hRz : 1 ≤ Rz) (hzR : ‖z‖ ≤ Rz)
    (hD00 : HasFDerivAt b00 D00 z) (hD01 : HasFDerivAt b01 D01 z)
    (hD10 : HasFDerivAt b10 D10 z) (hD11 : HasFDerivAt b11 D11 z)
    (hε : 0 ≤ ε)
    (hb00 : |b00 z - 1| ≤ ε) (hb01 : |b01 z| ≤ ε)
    (hb10 : |b10 z| ≤ ε) (hb11 : |b11 z - 1| ≤ ε)
    (hn00 : ‖D00‖ ≤ ε) (hn01 : ‖D01‖ ≤ ε) (hn10 : ‖D10‖ ≤ ε) (hn11 : ‖D11‖ ≤ ε)
    (hsmall : ε * Rz ^ 2 ≤ 1 / 1000) :
    ‖dzbar (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z‖ ≤ 64 * Rz ^ 2 * ε ∧
      (1 : ℝ) / 2 ≤ ‖dz (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z‖ ∧
      0 < (fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
          / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z).det := by
  haveI hCSRC : ContinuousSMul ℝ ℂ := ⟨by
    have h : (fun p : ℝ × ℂ => p.1 • p.2) = fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 := by
      funext p
      exact Complex.real_smul
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
  have hεRz : ε * Rz ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (mul_nonneg
      (by linarith : (0 : ℝ) ≤ Rz - 1) (by linarith : (0 : ℝ) ≤ Rz))]
  have hε1 : ε ≤ 1 / 128 := by
    nlinarith [hsmall, mul_nonneg hε (by nlinarith : (0 : ℝ) ≤ Rz ^ 2 - 1)]
  have hRz0 : (0 : ℝ) < Rz := by linarith
  -- basic denominator and numerator bounds
  obtain ⟨den, hden_def⟩ : ∃ x : ℂ, ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  obtain ⟨num, hnum_def⟩ : ∃ x : ℂ, ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) = x := ⟨_, rfl⟩
  have hden1 : ‖den - 1‖ ≤ 2 * ε * Rz := by
    rw [← hden_def]
    have h1 : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) - 1
        = ((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b10 z : ℝ) : ℂ) * z + ((b11 z - 1 : ℝ) : ℂ)‖
        ≤ ‖((b10 z : ℝ) : ℂ) * z‖ + ‖((b11 z - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b10 z| * ‖z‖ + |b11 z - 1| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb10 hzR (norm_nonneg z) hε) ?_
          calc |b11 z - 1| ≤ ε := hb11
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hdenlb : (1 : ℝ) / 2 ≤ ‖den‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) den
    rw [norm_one, norm_sub_rev] at h1
    nlinarith [hden1, hεRz]
  have hdenub : ‖den‖ ≤ 3 / 2 := by
    have h1 := norm_add_le (den - 1) 1
    rw [sub_add_cancel, norm_one] at h1
    nlinarith [hden1, hεRz]
  have hdenne : den ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdenlb
    linarith
  have hdenne' : ((b10 z : ℝ) : ℂ) * z + ((b11 z : ℝ) : ℂ) ≠ 0 := by
    rw [hden_def]
    exact hdenne
  have hnumz : ‖num - z‖ ≤ 2 * ε * Rz := by
    rw [← hnum_def]
    have h1 : ((b00 z : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) - z
        = ((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1]
    calc ‖((b00 z - 1 : ℝ) : ℂ) * z + ((b01 z : ℝ) : ℂ)‖
        ≤ ‖((b00 z - 1 : ℝ) : ℂ) * z‖ + ‖((b01 z : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |b00 z - 1| * ‖z‖ + |b01 z| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε * Rz + ε * 1 := by
          refine add_le_add (mul_le_mul hb00 hzR (norm_nonneg z) hε) ?_
          calc |b01 z| ≤ ε := hb01
            _ = ε * 1 := (mul_one ε).symm
      _ ≤ 2 * ε * Rz := by nlinarith [mul_le_mul_of_nonneg_left hRz hε]
  have hnumub : ‖num‖ ≤ 2 * Rz := by
    have h1 := norm_add_le (num - z) z
    rw [sub_add_cancel] at h1
    nlinarith [hnumz, hεRz, hzR]
  obtain ⟨hdiff, hLvraw⟩ := zz_moeb_core b00 b01 b10 b11 D00 D01 D10 D11 z
    hD00 hD01 hD10 hD11 hdenne'
  have hLv : ∀ v : ℂ, fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z v
      = ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 * v
        + ((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
            - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2 := by
    intro v
    rw [hLvraw v, hden_def, hnum_def]
  clear hLvraw hD00 hD01 hD10 hD11
  -- bounds for the two parts  -- bounds for the two parts
  obtain ⟨Sw, hSw_def⟩ : ∃ x : ℂ, ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 = x :=
    ⟨_, rfl⟩
  have hdet1 : |b00 z * b11 z - b01 z * b10 z - 1| ≤ 4 * ε := by
    have e1 : b00 z * b11 z - b01 z * b10 z - 1
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z := by ring
    rw [e1]
    have h1 : |(b00 z - 1) * (b11 z - 1)| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb00 hb11 (abs_nonneg _) hε
    have h2 : |b01 z * b10 z| ≤ ε * ε := by
      rw [abs_mul]
      exact mul_le_mul hb01 hb10 (abs_nonneg _) hε
    have h3 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1))
      (-(b01 z * b10 z))
    rw [abs_neg] at h3
    have h4 := abs_add_le ((b00 z - 1) * (b11 z - 1) + (b00 z - 1)) (b11 z - 1)
    have h5 := abs_add_le ((b00 z - 1) * (b11 z - 1)) (b00 z - 1)
    have hee : ε * ε ≤ ε := by
      have h := mul_le_mul_of_nonneg_left (by linarith only [hε1] : ε ≤ 1) hε
      linarith only [h]
    have hgoal : (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) - b01 z * b10 z
        = (b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z) := by
      ring
    rw [hgoal]
    calc |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1) + -(b01 z * b10 z)|
        ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1) + (b11 z - 1)| + |b01 z * b10 z| := h3
      _ ≤ |(b00 z - 1) * (b11 z - 1) + (b00 z - 1)| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h4]
      _ ≤ |(b00 z - 1) * (b11 z - 1)| + |b00 z - 1| + |b11 z - 1| + |b01 z * b10 z| := by
          linarith [h5]
      _ ≤ ε * ε + ε + ε + ε * ε := by linarith [h1, h2, hb00, hb11]
      _ ≤ 4 * ε := by linarith [hee]
  have hden2lb : (1 : ℝ) / 4 ≤ ‖den ^ 2‖ := by
    rw [norm_pow]
    nlinarith [hdenlb, norm_nonneg den]
  have hden2ne : den ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
  have hSw1 : ‖Sw - 1‖ ≤ 36 * ε * Rz := by
    rw [← hSw_def]
    have e1 : ((b00 z * b11 z - b01 z * b10 z : ℝ) : ℂ) / den ^ 2 - 1
        = (((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)) / den ^ 2 := by
      field_simp
      push_cast
      ring
    rw [e1, norm_div]
    have h1 : ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
        ≤ 4 * ε + 5 * ε * Rz := by
      have h2 : ‖den ^ 2 - 1‖ ≤ 5 * ε * Rz := by
        have e2 : den ^ 2 - 1 = (den - 1) * (den + 1) := by ring
        rw [e2, norm_mul]
        have h3 : ‖den + 1‖ ≤ 5 / 2 := by
          have := norm_add_le den (1 : ℂ)
          rw [norm_one] at this
          linarith [hdenub]
        calc ‖den - 1‖ * ‖den + 1‖ ≤ (2 * ε * Rz) * (5 / 2) :=
              mul_le_mul hden1 h3 (norm_nonneg _) (by positivity)
          _ = 5 * ε * Rz := by ring
      calc ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ) - (den ^ 2 - 1)‖
          ≤ ‖((b00 z * b11 z - b01 z * b10 z - 1 : ℝ) : ℂ)‖ + ‖den ^ 2 - 1‖ :=
            norm_sub_le _ _
        _ ≤ 4 * ε + 5 * ε * Rz := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            linarith [hdet1, h2]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h4 : 36 * ε * Rz * (1 / 4) ≤ 36 * ε * Rz * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    have h5 : 4 * ε + 5 * ε * Rz ≤ 9 * ε * Rz := by nlinarith
    linarith
  -- the error part of the derivative
  have hEbound : ∀ v : ℂ, ‖((((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
      - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))) / den ^ 2‖
      ≤ 28 * Rz ^ 2 * ε * ‖v‖ := by
    intro v
    have hDnum : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ))‖
          ≤ ‖((D00 v : ℝ) : ℂ) * z‖ + ‖((D01 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D00 v| * ‖z‖ + |D01 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D00 v| ≤ ‖D00‖ * ‖v‖ := D00.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn00 (norm_nonneg v)
            · calc |D01 v| ≤ ‖D01‖ * ‖v‖ := D01.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn01 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    have hDden : ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ ≤ 2 * ε * Rz * ‖v‖ := by
      calc ‖(((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖((D10 v : ℝ) : ℂ) * z‖ + ‖((D11 v : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |D10 v| * ‖z‖ + |D11 v| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε * ‖v‖ * Rz + ε * ‖v‖ := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ hzR (norm_nonneg z) (by positivity)
              calc |D10 v| ≤ ‖D10‖ * ‖v‖ := D10.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn10 (norm_nonneg v)
            · calc |D11 v| ≤ ‖D11‖ * ‖v‖ := D11.le_opNorm v
                _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right hn11 (norm_nonneg v)
        _ ≤ 2 * ε * Rz * ‖v‖ := by
          nlinarith [norm_nonneg v, hε,
            mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz - 1))
              (norm_nonneg v)]
    rw [norm_div]
    rw [div_le_iff₀ (by linarith [hden2lb] : (0 : ℝ) < ‖den ^ 2‖)]
    have h1 : ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
        ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
      calc ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
          - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖
          ≤ ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den‖
            + ‖num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ ≤ 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖) := by
            rw [norm_mul, norm_mul]
            refine add_le_add ?_ ?_
            · exact mul_le_mul hDnum hdenub (norm_nonneg _) (by positivity)
            · exact mul_le_mul hnumub hDden (norm_nonneg _) (by positivity)
    have h2 : 2 * ε * Rz * ‖v‖ * (3 / 2) + 2 * Rz * (2 * ε * Rz * ‖v‖)
        ≤ 7 * ε * Rz ^ 2 * ‖v‖ := by
      nlinarith [norm_nonneg v, hε, hRz0,
        mul_nonneg (mul_nonneg hε (by nlinarith [hRz] : (0 : ℝ) ≤ Rz ^ 2 - Rz))
          (norm_nonneg v)]
    have h3 : 28 * Rz ^ 2 * ε * ‖v‖ * (1 / 4) ≤ 28 * Rz ^ 2 * ε * ‖v‖ * ‖den ^ 2‖ := by
      refine mul_le_mul_of_nonneg_left hden2lb ?_
      positivity
    obtain ⟨X, hX⟩ : ∃ x : ℝ, ‖(((D00 v : ℝ) : ℂ) * z + ((D01 v : ℝ) : ℂ)) * den
        - num * (((D10 v : ℝ) : ℂ) * z + ((D11 v : ℝ) : ℂ))‖ = x := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ x : ℝ, ‖v‖ = x := ⟨_, rfl⟩
    obtain ⟨Dq, hDq⟩ : ∃ x : ℝ, ‖den ^ 2‖ = x := ⟨_, rfl⟩
    rw [hX] at h1 ⊢
    rw [hY] at h1 h2 h3 ⊢
    rw [hDq] at h3 ⊢
    linarith [h1, h2, h3]
  -- Wirtinger parts via the split of the derivative
  have hα : fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z 1
      = Sw + ((((D00 1 : ℝ) : ℂ) * z + ((D01 1 : ℝ) : ℂ)) * den
          - num * (((D10 1 : ℝ) : ℂ) * z + ((D11 1 : ℝ) : ℂ))) / den ^ 2 := by
    rw [hLv 1, ← hSw_def, mul_one]
  have hβ : fderiv ℝ (fun w => (((b00 w : ℝ) : ℂ) * w + ((b01 w : ℝ) : ℂ))
      / (((b10 w : ℝ) : ℂ) * w + ((b11 w : ℝ) : ℂ))) z Complex.I
      = Sw * Complex.I + ((((D00 Complex.I : ℝ) : ℂ) * z + ((D01 Complex.I : ℝ) : ℂ)) * den
          - num * (((D10 Complex.I : ℝ) : ℂ) * z
            + ((D11 Complex.I : ℝ) : ℂ))) / den ^ 2 := by
    rw [hLv Complex.I, ← hSw_def]
  have hE1 := hEbound 1
  have hEI := hEbound Complex.I
  rw [norm_one, mul_one] at hE1
  rw [Complex.norm_I, mul_one] at hEI
  have hCb0 : (0 : ℝ) ≤ 64 * Rz ^ 2 * ε := by positivity
  have hSw64 : ‖Sw - 1‖ ≤ 64 * Rz ^ 2 * ε := by
    refine le_trans hSw1 ?_
    have hRz2 : (0 : ℝ) ≤ Rz ^ 2 - Rz := by
      have h := mul_nonneg (by linarith only [hRz] : (0 : ℝ) ≤ Rz - 1)
        (by linarith only [hRz] : (0 : ℝ) ≤ Rz)
      nlinarith [h]
    nlinarith [mul_nonneg hε hRz2]
  have hE164 : ‖((((D00 1 : ℝ) : ℂ) * z + ((D01 1 : ℝ) : ℂ)) * den
      - num * (((D10 1 : ℝ) : ℂ) * z + ((D11 1 : ℝ) : ℂ))) / den ^ 2‖
      ≤ 64 * Rz ^ 2 * ε := by
    refine le_trans hE1 ?_
    nlinarith [mul_nonneg (mul_nonneg hε (sq_nonneg Rz)) (by norm_num : (0:ℝ) ≤ 36)]
  have hEI64 : ‖((((D00 Complex.I : ℝ) : ℂ) * z + ((D01 Complex.I : ℝ) : ℂ)) * den
      - num * (((D10 Complex.I : ℝ) : ℂ) * z + ((D11 Complex.I : ℝ) : ℂ))) / den ^ 2‖
      ≤ 64 * Rz ^ 2 * ε := by
    refine le_trans hEI ?_
    nlinarith [mul_nonneg (mul_nonneg hε (sq_nonneg Rz)) (by norm_num : (0:ℝ) ≤ 36)]
  have hsm6 : 64 * Rz ^ 2 * ε ≤ 1 / 6 := by nlinarith [hsmall]
  obtain ⟨hbar, hzlb, hdet⟩ := zz_wirt _ z Sw _ _ (64 * Rz ^ 2 * ε) hα hβ hSw64 hE164 hEI64
    hCb0 hsm6
  exact ⟨hbar, hzlb, hdet⟩

/-- Continuous functions are locally `Lᵖ`. -/
private lemma zz_memlp (f : ℂ → ℂ) (p : ℝ≥0∞) (Ω : Set ℂ) (hf : ContinuousOn f Ω) :
    MemLpLocOn f p Ω := by
  intro K hKΩ hK
  haveI : Fact (volume K < ⊤) := ⟨hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKΩ)
  refine MemLp.of_bound ((hf.mono hKΩ).aestronglyMeasurable hK.measurableSet) C ?_
  rw [MeasureTheory.ae_restrict_iff' hK.measurableSet]
  exact Filter.Eventually.of_forall hC

/-- A `C¹` function on an open set lies in `W^{1,2}_loc` there. -/
private lemma zz_sobolev (f : ℂ → ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 f Ω) : MemWklocP f 1 2 Ω := by
  have hfc : ContinuousOn f Ω := hf.continuousOn
  have hgc : ContinuousOn (fderiv ℝ f) Ω := hf.continuousOn_fderiv_of_isOpen hΩ le_rfl
  refine ⟨zz_memlp f 2 Ω hfc, fun z => (fderiv ℝ f z) 1, fun z => (fderiv ℝ f z) Complex.I,
    ⟨HasWeakDirDeriv.of_contDiffOn hΩ hf, HasWeakDirDeriv.of_contDiffOn hΩ hf⟩, ?_, ?_⟩
  · exact zz_memlp _ 2 Ω (hgc.clm_apply continuousOn_const)
  · exact zz_memlp _ 2 Ω (hgc.clm_apply continuousOn_const)

/-- **Quantitative inverse mapping on a ball**: a map whose derivative stays within `1/2`
of the identity on a closed ball is injective there and covers the quarter-radius ball
around the image of the center. -/
private lemma zz_surj (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x ∈ Metric.closedBall c r, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ Metric.closedBall c r,
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    Set.InjOn F (Metric.closedBall c r) ∧
      ∀ y ∈ Metric.closedBall (F c) (r / 4), ∃ x ∈ Metric.closedBall c r, F x = y := by
  have hconv : Convex ℝ (Metric.closedBall c r) := convex_closedBall c r
  have hlip : ∀ a ∈ Metric.closedBall c r, ∀ b ∈ Metric.closedBall c r,
      ‖(F b - b) - (F a - a)‖ ≤ 1 / 2 * ‖b - a‖ := by
    intro a ha b hb'
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun w => F w - w)
      (f' := fun x => fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ)
      (fun x hx => (((hd x hx).hasFDerivAt).sub (hasFDerivAt_id x)).hasFDerivWithinAt)
      (fun x hx => hb x hx) hconv ha hb'
  constructor
  · intro a ha b hb' hab
    have h1 := hlip a ha b hb'
    have h2 : (F b - b) - (F a - a) = a - b := by
      rw [hab]
      ring
    rw [h2] at h1
    have h3 : ‖a - b‖ = ‖b - a‖ := by
      rw [← neg_sub b a, norm_neg]
    rw [h3] at h1
    have h4 : ‖b - a‖ ≤ 0 := by linarith [h1]
    have h5 : b - a = 0 := norm_le_zero_iff.mp h4
    have h6 : b = a := by
      have := sub_eq_zero.mp h5
      exact this
    exact h6.symm
  · intro y hy
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm] at hy
    -- the update map is a contraction of the closed ball
    haveI : Nonempty (Metric.closedBall c r) := ⟨⟨c, Metric.mem_closedBall_self hr.le⟩⟩
    have hmaps : ∀ x ∈ Metric.closedBall c r, x - F x + y ∈ Metric.closedBall c r := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : x - F x + y - c = ((F c - c) - (F x - x)) + (y - F c) := by ring
      rw [h1]
      have h2 := hlip x hx c (Metric.mem_closedBall_self hr.le)
      have h3 : ‖x - c‖ ≤ r := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hx
      have h4 := norm_add_le ((F c - c) - (F x - x)) (y - F c)
      have h5 : ‖c - x‖ = ‖x - c‖ := by
        rw [← neg_sub x c, norm_neg]
      rw [h5] at h2
      have h6 : ‖y - F c‖ = ‖F c - y‖ := by
        rw [← neg_sub (F c) y, norm_neg]
      linarith [h2, h3, h4, hy, h6]
    obtain ⟨T, hTdef⟩ : ∃ T : Metric.closedBall c r → Metric.closedBall c r,
        T = fun x => ⟨(x : ℂ) - F x + y, hmaps x x.2⟩ := ⟨_, rfl⟩
    have hLip : LipschitzWith (1 / 2 : NNReal) T := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro a b
      rw [hTdef]
      have hab := hlip a a.2 b b.2
      rw [Subtype.dist_eq, Subtype.dist_eq]
      simp only [dist_eq_norm]
      have he : ((a : ℂ) - F a + y) - ((b : ℂ) - F b + y)
          = (F b - b) - (F a - a) := by ring
      rw [he]
      have hcoe : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
      rw [hcoe]
      have h3 : ‖(a : ℂ) - b‖ = ‖(b : ℂ) - a‖ := by
        rw [← neg_sub (b : ℂ) a, norm_neg]
      rw [h3]
      exact hab
    have hcontract : ContractingWith (1 / 2 : NNReal) T := ⟨by norm_num, hLip⟩
    haveI : CompleteSpace (Metric.closedBall c r) :=
      (Metric.isClosed_closedBall (x := c) (ε := r)).completeSpace_coe
    obtain ⟨x, hxfix⟩ : ∃ x : Metric.closedBall c r, T x = x :=
      ⟨ContractingWith.fixedPoint T hcontract, hcontract.fixedPoint_isFixedPt⟩
    refine ⟨x, x.2, ?_⟩
    have h1 : (T x : ℂ) = x := by
      rw [hxfix]
    rw [hTdef] at h1
    simp only at h1
    have h2 : (x : ℂ) - F x + y = x := h1
    have h3 : F (x : ℂ) = y := by linear_combination -h2
    exact h3

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The nested square estimates for the hyperbolic-Euclidean ball comparison exceed the
-- default heartbeat budget.
/-- **Euclidean sandwich for small hyperbolic balls**: for radius `s ≤ 1/2` the hyperbolic
ball nests between the Euclidean balls of radii `im · s / 2` and `2 · im · s` about the
center. -/
private lemma zz_ballcomp (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 1 / 2) :
    (∀ z : ℂ, z ∈ Metric.ball (w : ℂ) (w.im * s / 2) →
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) w < s) ∧
    (∀ z : ℂ, ∀ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) w < s →
      z ∈ Metric.ball (w : ℂ) (2 * w.im * s)) := by
  have hwim : 0 < w.im := w.im_pos
  have hsinh : 0 < Real.sinh s := by positivity
  have hcosh1 : 1 ≤ Real.cosh s := Real.one_le_cosh s
  have hcs : Real.cosh s - Real.sinh s = Real.exp (-s) := Real.cosh_sub_sinh s
  have hca : Real.cosh s + Real.sinh s = Real.exp s := Real.cosh_add_sinh s
  -- the two elementary exponential estimates
  have hlow : s / 2 ≤ Real.sinh s - (Real.cosh s - 1) := by
    have h1 : (-s) + 1 ≤ Real.exp (-s) := Real.add_one_le_exp (-s)
    have h2 : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
    have h3 : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : Real.exp (-s) ≤ 1 / (1 + s) := by
      rw [div_eq_inv_mul, mul_one, le_inv_comm₀ (Real.exp_pos _) (by linarith)]
      calc (1 + s : ℝ) = s + 1 := by ring
        _ ≤ Real.exp s := h2
        _ = (Real.exp (-s))⁻¹ := by
            rw [← Real.exp_neg, neg_neg]
    have h5 : 1 / (1 + s) ≤ 1 - s / 2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + s)]
      nlinarith [hs, hs2]
    have h6 : Real.exp (-s) ≤ 1 - s / 2 := le_trans h4 h5
    linarith [hcs, h6]
  have hhigh : Real.sinh s + (Real.cosh s - 1) ≤ 2 * s := by
    have h1 : 1 - s ≤ Real.exp (-s) := by
      have := Real.add_one_le_exp (-s)
      linarith
    have h2 : Real.exp s ≤ 1 / (1 - s) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - s)]
      calc Real.exp s * (1 - s) ≤ Real.exp s * Real.exp (-s) := by
            refine mul_le_mul_of_nonneg_left h1 (Real.exp_pos s).le
        _ = 1 := by
            rw [← Real.exp_add]
            simp
    have h3 : 1 / (1 - s) ≤ 1 + 2 * s := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - s)]
      nlinarith [hs, hs2]
    have h4 : Real.exp s ≤ 1 + 2 * s := le_trans h2 h3
    linarith [hca, h4]
  have hcen : ∀ z : ℂ, dist z ((((w : ℂ).re : ℝ) : ℂ)
      + ((w.im * Real.cosh s : ℝ) : ℂ) * Complex.I) ^ 2
      = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im * Real.cosh s) ^ 2 := by
    intro z
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have hchar : ∀ (z : ℂ) (hz : 0 < z.im), dist (⟨z, hz⟩ : UpperHalfPlane) w < s ↔
      (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im * Real.cosh s) ^ 2
        < (w.im * Real.sinh s) ^ 2 := by
    intro z hz
    constructor
    · intro h
      have hm := (zz_ball w s hs z).mpr ⟨hz, h⟩
      rw [Metric.mem_ball] at hm
      have h2 := mul_self_lt_mul_self dist_nonneg hm
      rw [← hcen z]
      nlinarith [h2]
    · intro h
      have h0 : dist z ((((w : ℂ).re : ℝ) : ℂ)
          + ((w.im * Real.cosh s : ℝ) : ℂ) * Complex.I) ^ 2
          < (w.im * Real.sinh s) ^ 2 := by
        rw [hcen z]
        exact h
      have hlt : dist z ((((w : ℂ).re : ℝ) : ℂ)
          + ((w.im * Real.cosh s : ℝ) : ℂ) * Complex.I) < w.im * Real.sinh s := by
        by_contra hcon
        push Not at hcon
        have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ w.im * Real.sinh s) hcon
        nlinarith [h0, hsq]
      obtain ⟨hz', hdd⟩ := (zz_ball w s hs z).mp (Metric.mem_ball.mpr hlt)
      exact hdd
  constructor
  · -- inner inclusion
    intro z hzball
    rw [Metric.mem_ball, dist_eq_norm] at hzball
    have hnormsq : ‖z - (w : ℂ)‖ ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im]
      ring
    have hE2 : (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 < (w.im * s / 2) ^ 2 := by
      rw [← hnormsq]
      have h := mul_self_lt_mul_self (norm_nonneg (z - (w : ℂ))) hzball
      nlinarith [h]
    have hzim : 0 < z.im := by
      have hb2 : (z.im - w.im) ^ 2 < (w.im * s / 2) ^ 2 := by
        nlinarith [hE2, sq_nonneg (z.re - (w : ℂ).re)]
      have hr : 0 < w.im * s / 2 := by positivity
      have habs : |z.im - w.im| < w.im * s / 2 := by
        by_contra hcon
        push Not at hcon
        have hsq := mul_self_le_mul_self hr.le hcon
        nlinarith [sq_abs (z.im - w.im), hb2, hsq]
      have h1 : -(w.im * s / 2) < z.im - w.im := (abs_lt.mp habs).1
      have h2 : 0 < w.im * (1 - s / 2) := mul_pos hwim (by linarith)
      nlinarith [h1, h2]
    refine ⟨hzim, ?_⟩
    rw [hchar z hzim]
    have hK0 : 0 ≤ w.im * (Real.cosh s - 1) :=
      mul_nonneg hwim.le (by linarith [hcosh1])
    have hkey : w.im * s / 2 + w.im * (Real.cosh s - 1) ≤ w.im * Real.sinh s := by
      have h := mul_le_mul_of_nonneg_left hlow hwim.le
      nlinarith [h]
    have hb2 : (z.im - w.im) ^ 2 < (w.im * s / 2) ^ 2 := by
      nlinarith [hE2, sq_nonneg (z.re - (w : ℂ).re)]
    have hbabs : |z.im - w.im| < w.im * s / 2 := by
      by_contra hcon
      push Not at hcon
      have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ w.im * s / 2) hcon
      nlinarith [sq_abs (z.im - w.im), hb2, hsq]
    have hsplit : z.im - w.im * Real.cosh s = (z.im - w.im) - w.im * (Real.cosh s - 1) := by
      ring
    rw [hsplit]
    nlinarith [hE2, hbabs, hK0, hkey, sq_abs (z.im - w.im), abs_nonneg (z.im - w.im),
      neg_abs_le (z.im - w.im), le_abs_self (z.im - w.im),
      mul_pos hwim hsinh]
  · -- outer inclusion
    intro z hz hlt
    rw [hchar z hz] at hlt
    rw [Metric.mem_ball, dist_eq_norm]
    have hnormsq : ‖z - (w : ℂ)‖ ^ 2 = (z.re - (w : ℂ).re) ^ 2 + (z.im - w.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im]
      ring
    have hK0 : 0 ≤ w.im * (Real.cosh s - 1) :=
      mul_nonneg hwim.le (by linarith [hcosh1])
    have hSp : 0 < w.im * Real.sinh s := by positivity
    have hbabs : |z.im - w.im * Real.cosh s| < w.im * Real.sinh s := by
      by_contra hcon
      push Not at hcon
      have hsq := mul_self_le_mul_self hSp.le hcon
      nlinarith [sq_abs (z.im - w.im * Real.cosh s), hlt, hsq,
        sq_nonneg (z.re - (w : ℂ).re)]
    have hkey : w.im * Real.sinh s + w.im * (Real.cosh s - 1) ≤ 2 * w.im * s := by
      have h := mul_le_mul_of_nonneg_left hhigh hwim.le
      nlinarith [h]
    have hfin : ‖z - (w : ℂ)‖ ^ 2 < (2 * w.im * s) ^ 2 := by
      rw [hnormsq]
      have hsplit : z.im - w.im = (z.im - w.im * Real.cosh s) + w.im * (Real.cosh s - 1) := by
        ring
      rw [hsplit]
      nlinarith [hlt, hbabs, hK0, hkey, sq_abs (z.im - w.im * Real.cosh s),
        le_abs_self (z.im - w.im * Real.cosh s), neg_abs_le (z.im - w.im * Real.cosh s),
        hSp]
    nlinarith [hfin, norm_nonneg (z - (w : ℂ)), mul_pos (mul_pos two_pos hwim) hs]

/-- Multiplicativity of the Möbius denominator of a matrix product. -/
private lemma zz_matden (M N : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hN : (N 1 0 : ℂ) * z + (N 1 1 : ℂ) ≠ 0) :
    ((M * N) 1 0 : ℂ) * z + ((M * N) 1 1 : ℂ)
      = ((M 1 0 : ℂ) * matMoebius N z + (M 1 1 : ℂ))
        * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ)) := by
  have h0 : (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hu : matMoebius N z * ((N 1 0 : ℂ) * z + (N 1 1 : ℂ))
      = (N 0 0 : ℂ) * z + (N 0 1 : ℂ) := by
    rw [matMoebius, div_mul_cancel₀ _ hN]
  rw [h0, h1, add_mul, mul_assoc, hu]
  push_cast
  ring

/-- Injectivity of a near-identity `C¹` map on a convex set. -/
private lemma zz_inj (F : ℂ → ℂ) (S : Set ℂ) (hconv : Convex ℝ S)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ S, ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    Set.InjOn F S := by
  have hlip : ∀ a ∈ S, ∀ b ∈ S, ‖(F b - b) - (F a - a)‖ ≤ 1 / 2 * ‖b - a‖ := by
    intro a ha b hb'
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun w => F w - w)
      (f' := fun x => fderiv ℝ F x - ContinuousLinearMap.id ℝ ℂ)
      (fun x hx => (((hd x hx).hasFDerivAt).sub (hasFDerivAt_id x)).hasFDerivWithinAt)
      (fun x hx => hb x hx) hconv ha hb'
  intro a ha b hb' hab
  have h1 := hlip a ha b hb'
  have h2 : (F b - b) - (F a - a) = a - b := by
    rw [hab]
    ring
  rw [h2] at h1
  have h3 : ‖a - b‖ = ‖b - a‖ := by
    rw [← neg_sub b a, norm_neg]
  rw [h3] at h1
  have h4 : ‖b - a‖ ≤ 0 := by linarith [h1]
  have h5 : b - a = 0 := norm_le_zero_iff.mp h4
  exact (sub_eq_zero.mp h5).symm

/-- Möbius maps of `SL(2, ℝ)` are `C¹` off the real axis. -/
private lemma zz_moeb_cdiff (gm : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ)
    (hz : 0 < z.im) : ContDiffAt ℝ 1 (moebiusMap gm) z := by
  have hden : (gm 1 0 : ℂ) * z + (gm 1 1 : ℂ) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero gm (ne_of_gt hz)
  have hfeq : moebiusMap gm = fun w => ((gm 0 0 : ℂ) * w + (gm 0 1 : ℂ))
      * (((gm 1 0 : ℂ) * w + (gm 1 1 : ℂ))⁻¹) := by
    funext w
    rw [moebiusMap, div_eq_mul_inv]
    rfl
  rw [hfeq]
  have hnum : ContDiffAt ℝ 1 (fun w : ℂ => (gm 0 0 : ℂ) * w + (gm 0 1 : ℂ)) z :=
    ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffAt
  have hde : ContDiffAt ℝ 1 (fun w : ℂ => (gm 1 0 : ℂ) * w + (gm 1 1 : ℂ)) z :=
    ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffAt
  exact hnum.mul (hde.inv hden)

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The averaged-field bounds sum convex combinations of near-identity matrices and their
-- derivatives; the default heartbeat budget does not cover the elaboration.
/-- **Bounds for a convex matrix average**: a field given on an open set by a finite convex
combination of near-identity constant matrices with `C¹` weights has entries `ε`-close to
the identity, differentiable entries with controlled derivative, and nonvanishing Möbius
denominator. -/
private lemma zz_field {ι' : Type} (U : Set ℂ) (hUopen : IsOpen U)
    (K : Set ℂ) (_hKU : K ⊆ U)
    (F : Finset ι') (u : ι' → ℂ → ℝ) (c : ι' → Matrix (Fin 2) (Fin 2) ℝ)
    (Rz ε₂ Mu : ℝ) (hε₂0 : 0 < ε₂)
    (hRzU : ∀ z ∈ U, ‖z‖ ≤ Rz)
    (hu01 : ∀ (γ : ι') (z : ℂ), z ∈ U → 0 ≤ u γ z ∧ u γ z ≤ 1)
    (husm : ∀ γ : ι', ContDiffOn ℝ 1 (u γ) U)
    (huD : ∀ γ ∈ F, ∀ z ∈ K, ‖fderiv ℝ (u γ) z‖ ≤ Mu)
    (hsum1 : ∀ z ∈ U, ∑ γ ∈ F, u γ z = 1)
    (hcclose : ∀ γ ∈ F, ∀ i j : Fin 2,
      |c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂)
    (B : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hBrep : ∀ z ∈ U, B z = ∑ γ ∈ F, u γ z • c γ)
    (hsmall : ε₂ * Rz + ε₂ ≤ 1 / 2) :
    (∀ z ∈ U, ∀ i j : Fin 2, |B z i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂) ∧
    (∀ z ∈ U, ∀ i j : Fin 2, HasFDerivAt (fun w => B w i j)
      (∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) • fderiv ℝ (u γ) z) z) ∧
    (∀ z ∈ K, ∀ i j : Fin 2, ‖∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
      • fderiv ℝ (u γ) z‖ ≤ (F.card : ℝ) * Mu * ε₂) ∧
    (∀ z ∈ U, ((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 : ℝ) : ℂ) ≠ 0) := by
  have hBfun : ∀ i j : Fin 2, ∀ z ∈ U, B z i j
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
        + ∑ γ ∈ F, u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    intro i j z hz
    rw [hBrep z hz, Matrix.sum_apply]
    have he : ∀ γ ∈ F, (u γ z • c γ) i j = u γ z * c γ i j := by
      intro γ _
      rw [Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl he]
    have hsub : ∑ γ ∈ F, u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
        = (∑ γ ∈ F, u γ z * c γ i j)
          - (∑ γ ∈ F, u γ z) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro γ _
      ring
    rw [hsub, hsum1 z hz, one_mul]
    ring
  have hBentry : ∀ z ∈ U, ∀ i j : Fin 2,
      |B z i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
    intro z hz i j
    rw [hBfun i j z hz, add_sub_cancel_left]
    calc |∑ γ ∈ F, u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)|
        ≤ ∑ γ ∈ F, |u γ z * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ ∈ F, u γ z * ε₂ := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [abs_mul, abs_of_nonneg (hu01 γ z hz).1]
          exact mul_le_mul_of_nonneg_left (hcclose γ hγ i j) (hu01 γ z hz).1
      _ = ε₂ := by
          rw [← Finset.sum_mul, hsum1 z hz, one_mul]
  have hBD : ∀ z ∈ U, ∀ i j : Fin 2,
      HasFDerivAt (fun w => B w i j)
        (∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
          • fderiv ℝ (u γ) z) z := by
    intro z hz i j
    have hUnhds : U ∈ nhds z := hUopen.mem_nhds hz
    have hDγ : ∀ γ ∈ F, HasFDerivAt (fun w => u γ w
        * (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
        ((c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) • fderiv ℝ (u γ) z) z := by
      intro γ _
      have hdiff : DifferentiableAt ℝ (u γ) z :=
        (((husm γ) z hz).contDiffAt hUnhds).differentiableAt one_ne_zero
      exact hdiff.hasFDerivAt.mul_const _
    have hsum0 := (HasFDerivAt.sum hDγ).const_add ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
    refine hsum0.congr_of_eventuallyEq ?_
    filter_upwards [hUnhds] with w hw
    rw [hBfun i j w hw, Finset.sum_apply]
  refine ⟨hBentry, hBD, ?_, ?_⟩
  · intro z hz i j
    calc ‖∑ γ ∈ F, (c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
        • fderiv ℝ (u γ) z‖
        ≤ ∑ γ ∈ F, ‖(c γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
          • fderiv ℝ (u γ) z‖ := norm_sum_le _ _
      _ ≤ ∑ _γ ∈ F, ε₂ * Mu := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hcclose γ hγ i j) (huD γ hγ z hz) (norm_nonneg _) hε₂0.le
      _ = (F.card : ℝ) * (ε₂ * Mu) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (F.card : ℝ) * Mu * ε₂ := by ring
  · intro z hz
    have h10 := hBentry z hz 1 0
    have h11 := hBentry z hz 1 1
    rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h10
    rw [Matrix.one_apply_eq] at h11
    intro h0
    have he : ((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 : ℝ) : ℂ) - 1
        = ((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 - 1 : ℝ) : ℂ) := by
      push_cast
      ring
    have hb : ‖((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 - 1 : ℝ) : ℂ)‖ ≤ ε₂ * Rz + ε₂ := by
      calc ‖((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 - 1 : ℝ) : ℂ)‖
          ≤ ‖((B z 1 0 : ℝ) : ℂ) * z‖ + ‖((B z 1 1 - 1 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = |B z 1 0| * ‖z‖ + |B z 1 1 - 1| := by
            rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
        _ ≤ ε₂ * Rz + ε₂ := by
            refine add_le_add (mul_le_mul h10 (hRzU z hz) (norm_nonneg z) hε₂0.le) h11
    have h1 : ‖((B z 1 0 : ℝ) : ℂ) * z + ((B z 1 1 : ℝ) : ℂ) - 1‖ = 1 := by
      rw [h0]
      simp
    rw [he] at h1
    linarith [hb, h1.symm.le, hsmall]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The transport computation chains three Wirtinger factorizations; the default heartbeat
-- budget does not cover the elaboration.
/-- **Möbius transport of Wirtinger data**: if `F` agrees on the upper half plane with a
conjugate `𝔪A ∘ F ∘ 𝔪G`, then differentiability, upper-half-plane values and the two
Wirtinger derivatives at `z` are carried by a single nonzero complex factor from those at
the transported point. -/
private lemma zz_transport (A G : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (F : ℂ → ℂ) (z w : ℂ) (hz : 0 < z.im) (_hw : 0 < w.im)
    (hwz : w = moebiusMap G z)
    (hEE : ∀ x : ℂ, 0 < x.im → F x = moebiusMap A (F (moebiusMap G x)))
    (hFd : DifferentiableAt ℝ F w) (hFim : 0 < (F w).im) :
    DifferentiableAt ℝ F z ∧ 0 < (F z).im ∧
      ∃ q₁ q₂ : ℂ, q₁ ≠ 0 ∧ ‖q₁‖ = ‖q₂‖ ∧ dz F z = q₁ * dz F w
        ∧ dzbar F z = q₂ * dzbar F w := by
  have hopen : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdenG : moebiusDenom G z ≠ 0 := moebiusDenom_ne_zero_of_im_ne_zero G (ne_of_gt hz)
  have hGd : DifferentiableAt ℂ (moebiusMap G) z :=
    (hasDerivAt_moebiusMap G hdenG).differentiableAt
  have hGderiv : deriv (moebiusMap G) z = ((moebiusDenom G z) ^ 2)⁻¹ :=
    (hasDerivAt_moebiusMap G hdenG).deriv
  have hFdw : DifferentiableAt ℝ F (moebiusMap G z) := by
    rw [← hwz]
    exact hFd
  -- the inner composite
  have hinner_dz : dz (F ∘ moebiusMap G) z = dz F w * deriv (moebiusMap G) z := by
    rw [dz_comp_of_holomorphicAt hGd hFdw, ← hwz]
  have hinner_dzbar : dzbar (F ∘ moebiusMap G) z
      = dzbar F w * starRingEnd ℂ (deriv (moebiusMap G) z) := by
    rw [dzbar_comp_of_holomorphicAt hGd hFdw, ← hwz]
  have hinner_d : DifferentiableAt ℝ (F ∘ moebiusMap G) z :=
    hFdw.comp z (differentiableAt_complex_iff_differentiableAt_real.mp hGd).1
  -- the outer Möbius factor
  have hFGim : 0 < (F (moebiusMap G z)).im := by
    rw [← hwz]
    exact hFim
  have hdenA : moebiusDenom A (F (moebiusMap G z)) ≠ 0 :=
    moebiusDenom_ne_zero_of_im_ne_zero A (ne_of_gt hFGim)
  have hAd : DifferentiableAt ℂ (moebiusMap A) (F (moebiusMap G z)) :=
    (hasDerivAt_moebiusMap A hdenA).differentiableAt
  have hAderiv : deriv (moebiusMap A) (F (moebiusMap G z))
      = ((moebiusDenom A (F (moebiusMap G z))) ^ 2)⁻¹ :=
    (hasDerivAt_moebiusMap A hdenA).deriv
  have hAdr : DifferentiableAt ℝ (moebiusMap A) ((F ∘ moebiusMap G) z) :=
    (differentiableAt_complex_iff_differentiableAt_real.mp hAd).1
  -- the composite and its Wirtinger data
  have hcomp_dz : dz (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z
      = deriv (moebiusMap A) (F (moebiusMap G z)) * dz (F ∘ moebiusMap G) z := by
    rw [dz_comp hinner_d hAdr]
    rw [show (F ∘ moebiusMap G) z = F (moebiusMap G z) from rfl]
    rw [dzbar_eq_zero_of_differentiableAt hAd, dz_eq_deriv_of_differentiableAt hAd]
    ring
  have hcomp_dzbar : dzbar (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z
      = deriv (moebiusMap A) (F (moebiusMap G z)) * dzbar (F ∘ moebiusMap G) z := by
    rw [dzbar_comp hinner_d hAdr]
    rw [show (F ∘ moebiusMap G) z = F (moebiusMap G z) from rfl]
    rw [dzbar_eq_zero_of_differentiableAt hAd, dz_eq_deriv_of_differentiableAt hAd]
    ring
  have hcomp_d : DifferentiableAt ℝ (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z :=
    hAdr.comp z hinner_d
  -- transfer along the eventual identity
  have hEEq : F =ᶠ[nhds z] fun x => moebiusMap A ((F ∘ moebiusMap G) x) := by
    filter_upwards [hopen.mem_nhds hz] with x hx
    exact hEE x hx
  have hFdz : DifferentiableAt ℝ F z := hcomp_d.congr_of_eventuallyEq hEEq
  have hfdeq : fderiv ℝ F z = fderiv ℝ (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z :=
    hEEq.fderiv_eq
  have hdz_eq : dz F z = dz (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z := by
    rw [dz, dz, hfdeq]
  have hdzbar_eq : dzbar F z = dzbar (fun x => moebiusMap A ((F ∘ moebiusMap G) x)) z := by
    rw [dzbar, dzbar, hfdeq]
  refine ⟨hFdz, ?_, ?_⟩
  · rw [hEE z hz]
    exact moebiusMap_im_pos A hFGim
  · refine ⟨deriv (moebiusMap A) (F (moebiusMap G z)) * deriv (moebiusMap G) z,
      deriv (moebiusMap A) (F (moebiusMap G z))
        * starRingEnd ℂ (deriv (moebiusMap G) z), ?_, ?_, ?_, ?_⟩
    · refine mul_ne_zero ?_ ?_
      · rw [hAderiv]
        exact inv_ne_zero (pow_ne_zero 2 hdenA)
      · rw [hGderiv]
        exact inv_ne_zero (pow_ne_zero 2 hdenG)
    · rw [norm_mul, norm_mul, Complex.norm_conj]
    · rw [hdz_eq, hcomp_dz, hinner_dz]
      ring
    · rw [hdzbar_eq, hcomp_dzbar, hinner_dzbar]
      ring

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The weight-field construction sums bump atoms over the group with compactness bounds;
-- the default heartbeat budget does not cover the elaboration.
/-- **The equivariant partition of unity subordinate to the orbit**: from an orbit-density
radius, a family of `C¹` weights on a euclidean-ball neighborhood of the base orbit ball,
summing to one over a finite active set, vanishing off it, with uniform derivative bounds
on an inner ball, and exactly equivariant under the Möbius action. -/
private lemma zz_weights {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ'fuchs : IsFuchsianGroup Γ') (τ₀ : UpperHalfPlane) (R : ℝ) (hRpos : 0 < R)
    (hdense : ∀ σ : UpperHalfPlane, Metric.infDist σ (MulAction.orbit (↥Γ') τ₀) ≤ R) :
    ∃ (UK UKb : Set ℂ) (SACT : Finset ↥Γ') (uψ : ↥Γ' → ℂ → ℝ) (Mψ Rz imK : ℝ),
      IsOpen UK ∧ UK ⊆ {z : ℂ | 0 < z.im} ∧ IsOpen UKb ∧ Convex ℝ UKb ∧ UKb ⊆ UK ∧
      (∀ (z : ℂ) (hz : 0 < z.im),
        dist (⟨z, hz⟩ : UpperHalfPlane) τ₀ < R + 3 / 2 → z ∈ UKb) ∧
      1 ≤ Rz ∧ (∀ z ∈ UK, ‖z‖ ≤ Rz) ∧ 0 ≤ Mψ ∧ 0 < imK ∧ (∀ z ∈ UK, imK < z.im) ∧
      (∀ (γ : ↥Γ') (z : ℂ), z ∈ UK → 0 ≤ uψ γ z ∧ uψ γ z ≤ 1) ∧
      (∀ γ : ↥Γ', ContDiffOn ℝ 1 (uψ γ) UK) ∧
      (∀ γ ∈ SACT, ∀ z ∈ UKb, ‖fderiv ℝ (uψ γ) z‖ ≤ Mψ) ∧
      (∀ z ∈ UK, ∑ γ ∈ SACT, uψ γ z = 1) ∧
      (∀ z ∈ UK, ∀ γ : ↥Γ', γ ∉ SACT → uψ γ z = 0) ∧
      (∀ γ ∈ SACT, dist τ₀ (γ • τ₀) ≤ 2 * R + 4) ∧
      (∀ (β γ : ↥Γ') (z : ℂ), 0 < z.im →
        uψ (β * γ) (moebiusMap (↑β) z) = uψ γ z) ∧
      (∀ z : ℂ, 0 < z.im → ∃ Fz : Finset ↥Γ', ∀ γ : ↥Γ', γ ∉ Fz → uψ γ z = 0) := by
  classical
  haveI : IsIsometricSMul (↥Γ') UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  have hτ₀im : 0 < τ₀.im := τ₀.im_pos
  have hSfin : ∀ r : ℝ, {γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ r}.Finite :=
    fun r => zz_fin hΓ'fuchs τ₀ τ₀ r
  -- the bump profile
  obtain ⟨gb, hgbdef⟩ : ∃ g : ℝ → ℝ, g = fun t =>
      Real.smoothTransition ((Real.cosh (R + 1) - t)
        / (Real.cosh (R + 1) - Real.cosh (R + 1 / 2))) := ⟨_, rfl⟩
  have hcoshRlt : Real.cosh (R + 1 / 2) < Real.cosh (R + 1) := by
    rw [Real.cosh_lt_cosh]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1 / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1)]
    linarith
  have hgbsm : ContDiff ℝ 1 gb := by
    rw [hgbdef]
    refine Real.smoothTransition.contDiff.comp ?_
    refine ContDiff.div_const ?_ _
    exact contDiff_const.sub contDiff_id
  have hgb01 : ∀ t : ℝ, 0 ≤ gb t ∧ gb t ≤ 1 := by
    intro t
    rw [hgbdef]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hgb1 : ∀ t : ℝ, t ≤ Real.cosh (R + 1 / 2) → gb t = 1 := by
    intro t ht
    rw [hgbdef]
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hgb0 : ∀ t : ℝ, Real.cosh (R + 1) ≤ t → gb t = 0 := by
    intro t ht
    rw [hgbdef]
    refine Real.smoothTransition.zero_of_nonpos ?_
    have h1 : Real.cosh (R + 1) - t ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h1 (by linarith)
  -- the atoms
  obtain ⟨aψ, haψdef⟩ : ∃ a : ↥Γ' → ℂ → ℝ, a = fun γ z =>
      gb (1 + Complex.normSq (z - ((γ • τ₀ : UpperHalfPlane) : ℂ))
        / (2 * z.im * ((γ • τ₀ : UpperHalfPlane) : ℂ).im)) := ⟨_, rfl⟩
  have haψbridge : ∀ (γ : ↥Γ') (τ : UpperHalfPlane),
      aψ γ (τ : ℂ) = gb (Real.cosh (dist τ (γ • τ₀))) := by
    intro γ τ
    rw [haψdef]
    exact zz_atom_bridge gb (γ • τ₀) τ
  have haψ01 : ∀ (γ : ↥Γ') (z : ℂ), 0 ≤ aψ γ z ∧ aψ γ z ≤ 1 := by
    intro γ z
    rw [haψdef]
    exact hgb01 _
  have haψvanish : ∀ (γ : ↥Γ') (τ : UpperHalfPlane), R + 1 ≤ dist τ (γ • τ₀) →
      aψ γ (τ : ℂ) = 0 := by
    intro γ τ hfar
    rw [haψdef]
    exact zz_atom_vanish gb R hRpos.le hgb0 (γ • τ₀) τ hfar
  have haψplateau : ∀ (γ : ↥Γ') (τ : UpperHalfPlane), dist τ (γ • τ₀) ≤ R + 1 / 2 →
      aψ γ (τ : ℂ) = 1 := by
    intro γ τ hnear
    rw [haψbridge]
    refine hgb1 _ ?_
    have h1 : |dist τ (γ • τ₀)| ≤ |R + 1 / 2| := by
      rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R + 1 / 2)]
      exact hnear
    exact Real.cosh_le_cosh.mpr h1
  have haψsm : ∀ (γ : ↥Γ') (z₀ : ℂ), 0 < z₀.im → ContDiffAt ℝ 1 (aψ γ) z₀ := by
    intro γ z₀ hz₀
    rw [haψdef]
    exact zz_atom_contDiffAt gb hgbsm (γ • τ₀) z₀ hz₀
  obtain ⟨Ψs, hΨdef⟩ : ∃ P : ℂ → ℝ, P = fun z => ∑' γ : ↥Γ', aψ γ z := ⟨_, rfl⟩
  have hrep : ∀ z₀ : ℂ, 0 < z₀.im → ∃ r : ℝ, 0 < r ∧ ∃ F : Finset ↥Γ',
      (∀ z ∈ Metric.ball z₀ r, 0 < z.im) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ γ : ↥Γ', γ ∉ F → aψ γ z = 0) := by
    intro z₀ hz₀
    obtain ⟨r, hr, F, hFfin, hball, hvan⟩ := zz_locfin hΓ'fuchs τ₀ R z₀ hz₀
    refine ⟨r, hr, hFfin.toFinset, hball, ?_⟩
    intro z hz γ hγ
    have hzim := hball z hz
    have hfar := hvan z hz hzim γ (by
      intro hmem'
      exact hγ (hFfin.mem_toFinset.mpr hmem'))
    exact haψvanish γ ⟨z, hzim⟩ hfar
  have hΨrep : ∀ z₀ : ℂ, 0 < z₀.im → ∃ r : ℝ, 0 < r ∧ ∃ F : Finset ↥Γ',
      (∀ z ∈ Metric.ball z₀ r, 0 < z.im) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ γ : ↥Γ', γ ∉ F → aψ γ z = 0) ∧
      ∀ z ∈ Metric.ball z₀ r, Ψs z = ∑ γ ∈ F, aψ γ z := by
    intro z₀ hz₀
    obtain ⟨r, hr, F, hball, hvan⟩ := hrep z₀ hz₀
    refine ⟨r, hr, F, hball, hvan, ?_⟩
    intro z hz
    rw [hΨdef]
    exact tsum_eq_sum (fun γ hγ => hvan z hz γ hγ)
  have hΨge1 : ∀ z : ℂ, 0 < z.im → 1 ≤ Ψs z := by
    intro z hz
    obtain ⟨r, hr, F, hball, hvan, hsum⟩ := hΨrep z hz
    have hzmem : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    rw [hsum z hzmem]
    have h1 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀) ≤ R :=
      hdense _
    have hne : (MulAction.orbit (↥Γ') τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    obtain ⟨y, hymem, hylt⟩ := (Metric.infDist_lt_iff hne).mp
      (lt_of_le_of_lt h1 (by linarith : R < R + 1 / 2))
    obtain ⟨γd, rfl⟩ := MulAction.mem_orbit_iff.mp hymem
    have hone : aψ γd z = 1 := haψplateau γd ⟨z, hz⟩ hylt.le
    have hγdF : γd ∈ F := by
      by_contra hγd
      have h0 := hvan z hzmem γd hγd
      rw [h0] at hone
      norm_num at hone
    calc (1 : ℝ) = aψ γd z := hone.symm
      _ ≤ ∑ γ ∈ F, aψ γ z :=
          Finset.single_le_sum (fun γ _ => (haψ01 γ z).1) hγdF
  -- the regions
  obtain ⟨UK, hUKdef⟩ : ∃ U : Set ℂ, U = Metric.ball ((((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
      (τ₀.im * Real.sinh (R + 2)) := ⟨_, rfl⟩
  have hUKchar : ∀ z : ℂ, z ∈ UK ↔
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) τ₀ < R + 2 := by
    intro z
    rw [hUKdef]
    exact zz_ball τ₀ (R + 2) (by linarith) z
  have hUKopen : IsOpen UK := by
    rw [hUKdef]
    exact Metric.isOpen_ball
  have hUKsub : UK ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    obtain ⟨hzim, _⟩ := (hUKchar z).mp hz
    exact hzim
  obtain ⟨UKb, hUKbdef⟩ : ∃ U : Set ℂ, U = Metric.ball ((((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
      (τ₀.im * Real.sinh (R + 3 / 2)) := ⟨_, rfl⟩
  have hUKbchar : ∀ z : ℂ, z ∈ UKb ↔
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) τ₀ < R + 3 / 2 := by
    intro z
    rw [hUKbdef]
    exact zz_ball τ₀ (R + 3 / 2) (by linarith) z
  have hUKbopen : IsOpen UKb := by
    rw [hUKbdef]
    exact Metric.isOpen_ball
  have hUKbconv : Convex ℝ UKb := by
    rw [hUKbdef]
    exact convex_ball _ _
  have hUKbUK : UKb ⊆ UK := by
    intro z hz
    obtain ⟨hzim, hd⟩ := (hUKbchar z).mp hz
    exact (hUKchar z).mpr ⟨hzim, by linarith⟩
  -- the closed inner region for the compactness bound
  obtain ⟨K1c, hK1cdef⟩ : ∃ K : Set ℂ, K = Metric.closedBall ((((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
      (τ₀.im * Real.sinh (R + 3 / 2)) := ⟨_, rfl⟩
  have hK1ccomp : IsCompact K1c := by
    rw [hK1cdef]
    exact isCompact_closedBall _ _
  have hUKbK1c : UKb ⊆ K1c := by
    rw [hUKbdef, hK1cdef]
    exact Metric.ball_subset_closedBall
  have hK1cUK : K1c ⊆ UK := by
    rw [hK1cdef, hUKdef]
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have hcd : dist ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
        ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
        = τ₀.im * Real.cosh (R + 2) - τ₀.im * Real.cosh (R + 3 / 2) := by
      rw [dist_eq_norm]
      have he : ((((τ₀ : ℂ).re : ℝ) : ℂ)
          + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
          - ((((τ₀ : ℂ).re : ℝ) : ℂ)
          + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
          = ((τ₀.im * Real.cosh (R + 3 / 2) - τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ)
            * Complex.I := by
        push_cast
        ring
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos ?_]
      · ring
      · have hmn : Real.cosh (R + 3 / 2) ≤ Real.cosh (R + 2) := by
          rw [Real.cosh_le_cosh, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        nlinarith [hmn, hτ₀im]
    have htri := dist_triangle z ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 3 / 2) : ℝ) : ℂ) * Complex.I)
        ((((τ₀ : ℂ).re : ℝ) : ℂ) + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
    rw [hcd] at htri
    have hkey : τ₀.im * Real.sinh (R + 3 / 2) + τ₀.im * Real.cosh (R + 2)
        - τ₀.im * Real.cosh (R + 3 / 2) < τ₀.im * Real.sinh (R + 2) := by
      have h1 : Real.cosh (R + 2) - Real.sinh (R + 2)
          < Real.cosh (R + 3 / 2) - Real.sinh (R + 3 / 2) := by
        rw [Real.cosh_sub_sinh, Real.cosh_sub_sinh]
        refine Real.exp_lt_exp.mpr ?_
        linarith
      nlinarith [h1, hτ₀im]
    linarith
  -- the active set
  obtain ⟨SACT, hSACTdef⟩ : ∃ S : Finset ↥Γ',
      S = (hSfin (2 * R + 4)).toFinset := ⟨_, rfl⟩
  have hSACTmem : ∀ γ : ↥Γ', γ ∈ SACT ↔ dist τ₀ (γ • τ₀) ≤ 2 * R + 4 := by
    intro γ
    rw [hSACTdef, Set.Finite.mem_toFinset]
    rfl
  have hSACTvan : ∀ z ∈ UK, ∀ γ : ↥Γ', γ ∉ SACT → aψ γ z = 0 := by
    intro z hz γ hγ
    obtain ⟨hzim, hzd⟩ := (hUKchar z).mp hz
    rw [hSACTmem] at hγ
    push Not at hγ
    refine haψvanish γ ⟨z, hzim⟩ ?_
    have htri := dist_triangle τ₀ (⟨z, hzim⟩ : UpperHalfPlane) (γ • τ₀)
    have hcomm : dist τ₀ (⟨z, hzim⟩ : UpperHalfPlane)
        = dist (⟨z, hzim⟩ : UpperHalfPlane) τ₀ := dist_comm _ _
    linarith
  have hΨrepUK : ∀ z ∈ UK, Ψs z = ∑ γ ∈ SACT, aψ γ z := by
    intro z hz
    rw [hΨdef]
    exact tsum_eq_sum (fun γ hγ => hSACTvan z hz γ hγ)
  have hΨsmUK : ContDiffOn ℝ 1 Ψs UK := by
    intro z hz
    have hsumsm : ContDiffWithinAt ℝ 1 (fun w => ∑ γ ∈ SACT, aψ γ w) UK z := by
      refine ContDiffWithinAt.sum ?_
      intro γ _
      exact ((haψsm γ z (hUKsub hz)).contDiffWithinAt)
    refine hsumsm.congr_of_eventuallyEq ?_ (hΨrepUK z hz)
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hΨrepUK w hw
  obtain ⟨uψ, huψdef⟩ : ∃ u : ↥Γ' → ℂ → ℝ, u = fun γ z => aψ γ z / Ψs z := ⟨_, rfl⟩
  have hΨne : ∀ z ∈ UK, Ψs z ≠ 0 := by
    intro z hz
    have := hΨge1 z (hUKsub hz)
    linarith
  have huψsm : ∀ γ : ↥Γ', ContDiffOn ℝ 1 (uψ γ) UK := by
    intro γ
    rw [huψdef]
    refine ContDiffOn.div ?_ hΨsmUK hΨne
    intro z hz
    exact (haψsm γ z (hUKsub hz)).contDiffWithinAt
  have hsum1 : ∀ z ∈ UK, ∑ γ ∈ SACT, uψ γ z = 1 := by
    intro z hz
    rw [huψdef]
    simp only
    rw [← Finset.sum_div, ← hΨrepUK z hz, div_self (hΨne z hz)]
  have huψ01 : ∀ (γ : ↥Γ') (z : ℂ), z ∈ UK → 0 ≤ uψ γ z ∧ uψ γ z ≤ 1 := by
    intro γ z hz
    rw [huψdef]
    have h1 := hΨge1 z (hUKsub hz)
    have h2 := haψ01 γ z
    constructor
    · exact div_nonneg h2.1 (by linarith)
    · rw [div_le_one (by linarith)]
      calc aψ γ z ≤ 1 := h2.2
        _ ≤ Ψs z := h1
  -- derivative bounds on the inner ball, from compactness of its closure
  have hBg : ∀ γ : ↥Γ', ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K1c, ‖fderiv ℝ (uψ γ) z‖ ≤ C := by
    intro γ
    have hcont : ContinuousOn (fun z => ‖fderiv ℝ (uψ γ) z‖) K1c := by
      refine ContinuousOn.norm ?_
      refine ((huψsm γ).continuousOn_fderiv_of_isOpen hUKopen le_rfl).mono hK1cUK
    obtain ⟨C, hC⟩ := hK1ccomp.exists_bound_of_continuousOn hcont
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro z hz
    have := hC z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
    exact le_trans this (le_max_left _ _)
  choose CB hCB0 hCBle using hBg
  have hSACTne : (SACT : Finset ↥Γ').Nonempty := by
    refine ⟨1, ?_⟩
    rw [hSACTmem]
    rw [show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _, dist_self]
    linarith
  obtain ⟨Mψ, hMψdef⟩ : ∃ M : ℝ, M = SACT.sup' hSACTne CB := ⟨_, rfl⟩
  have hMψle : ∀ γ ∈ SACT, CB γ ≤ Mψ := by
    intro γ hγ
    rw [hMψdef]
    exact Finset.le_sup' CB hγ
  have hMψ0 : 0 ≤ Mψ := by
    obtain ⟨γ0, hγ0⟩ := hSACTne
    exact le_trans (hCB0 γ0) (hMψle γ0 hγ0)
  -- the euclidean size and the imaginary-part floor
  obtain ⟨Rz, hRzdef⟩ : ∃ x : ℝ, x = max (‖(((τ₀ : ℂ).re : ℝ) : ℂ)
      + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I‖
      + τ₀.im * Real.sinh (R + 2)) 1 := ⟨_, rfl⟩
  have hRz1 : 1 ≤ Rz := by
    rw [hRzdef]
    exact le_max_right _ _
  have hRzUK : ∀ z ∈ UK, ‖z‖ ≤ Rz := by
    intro z hz
    rw [hUKdef, Metric.mem_ball] at hz
    have h1 := norm_sub_norm_le z ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)
    rw [← dist_eq_norm] at h1
    rw [hRzdef]
    refine le_trans ?_ (le_max_left _ _)
    linarith
  obtain ⟨imK, himKdef⟩ : ∃ x : ℝ, x = τ₀.im * Real.exp (-(R + 2)) := ⟨_, rfl⟩
  have himK0 : 0 < imK := by
    rw [himKdef]
    positivity
  have himUK : ∀ z ∈ UK, imK < z.im := by
    intro z hz
    rw [hUKdef, Metric.mem_ball] at hz
    have hcim : ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I).im
        = τ₀.im * Real.cosh (R + 2) := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero, zero_add]
    have h1 : |(z - ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)).im|
        ≤ ‖z - ((((τ₀ : ℂ).re : ℝ) : ℂ)
        + ((τ₀.im * Real.cosh (R + 2) : ℝ) : ℂ) * Complex.I)‖ :=
      Complex.abs_im_le_norm _
    rw [Complex.sub_im, hcim, ← dist_eq_norm] at h1
    have h2 := (abs_le.mp h1).1
    have h3 : Real.cosh (R + 2) - Real.sinh (R + 2) = Real.exp (-(R + 2)) :=
      Real.cosh_sub_sinh (R + 2)
    rw [himKdef]
    nlinarith [hz, hτ₀im, h3]
  -- equivariance of the weights
  have hcoesmul : ∀ (β : ↥Γ') (τ : UpperHalfPlane),
      ((β • τ : UpperHalfPlane) : ℂ) = moebiusMap (↑β) (τ : ℂ) :=
    fun β τ => coe_smul_eq_moebiusMap (↑β) τ
  have haψequi : ∀ (β γ : ↥Γ') (z : ℂ), 0 < z.im →
      aψ (β * γ) (moebiusMap (↑β) z) = aψ γ z := by
    intro β γ z hz
    have him : 0 < (moebiusMap (↑β) z).im := moebiusMap_im_pos _ hz
    have hpt : (⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane) = β • ⟨z, hz⟩ := by
      ext
      rw [hcoesmul β ⟨z, hz⟩]
    have h1 := haψbridge (β * γ) (⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane)
    have h2 := haψbridge γ (⟨z, hz⟩ : UpperHalfPlane)
    have hd : dist (⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane) ((β * γ) • τ₀)
        = dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by
      rw [hpt, mul_smul]
      exact dist_smul β _ _
    have hcoe1 : ((⟨moebiusMap (↑β) z, him⟩ : UpperHalfPlane) : ℂ)
        = moebiusMap (↑β) z := rfl
    have hcoe2 : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
    rw [hcoe1] at h1
    rw [hcoe2] at h2
    rw [h1, h2, hd]
  have hΨequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      Ψs (moebiusMap (↑β) z) = Ψs z := by
    intro β z hz
    rw [hΨdef]
    simp only
    rw [← Equiv.tsum_eq (Equiv.mulLeft β) (fun γ => aψ γ (moebiusMap (↑β) z))]
    refine tsum_congr ?_
    intro δ
    simp only [Equiv.coe_mulLeft]
    exact haψequi β δ z hz
  refine ⟨UK, UKb, SACT, uψ, Mψ, Rz, imK, hUKopen, hUKsub, hUKbopen, hUKbconv, hUKbUK,
    ?_, hRz1, hRzUK, hMψ0, himK0, himUK, huψ01, huψsm, ?_, hsum1, ?_, ?_, ?_, ?_⟩
  · intro z hz hd
    exact (hUKbchar z).mpr ⟨hz, hd⟩
  · intro γ hγ z hz
    exact le_trans (hCBle γ z (hUKbK1c hz)) (hMψle γ hγ)
  · intro z hz γ hγ
    rw [huψdef]
    simp only
    rw [hSACTvan z hz γ hγ, zero_div]
  · intro γ hγ
    rw [← hSACTmem]
    exact hγ
  · intro β γ z hz
    rw [huψdef]
    simp only
    rw [haψequi β γ z hz, hΨequi β z hz]
  · intro z hz
    obtain ⟨r, hr, F, hball, hvan⟩ := hrep z hz
    refine ⟨F, ?_⟩
    intro γ hγ
    rw [huψdef]
    simp only
    rw [hvan z (Metric.mem_ball_self hr) γ hγ, zero_div]

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The conjugation-and-regularity package chains matrix Möbius factorizations at every
-- point; the default heartbeat budget does not cover the elaboration.
/-- **Globalization of the developed map**: from the twisted equivariance of the
coefficient field, transport of base points into the analyzed region and the pointwise
package there, the map `z ↦ 𝔪(B z) z` has nonvanishing denominator, upper-half-plane
values, exact `θ`-equivariance, `C¹` regularity, positive Jacobian and Beltrami quotient
at most `κ` on the whole upper half plane. -/
private lemma zz_conjreg {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (θ : ↥Γ' → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (Bf : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (UK UKb : Set ℂ)
    (hUKopen : IsOpen UK) (hUKbUK : UKb ⊆ UK)
    (κ Cb : ℝ) (hκ : 0 < κ) (hCbκ : 2 * Cb ≤ κ)
    (htransport : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ), 0 < w.im ∧ w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w)
    (hBequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im → Bf (moebiusMap (↑β) z)
      = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * Bf z * ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (hdenUK : ∀ z ∈ UK, ((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0)
    (hsmUK : ContDiffOn ℝ 1 (fun z => matMoebius (Bf z) z) UK)
    (hpk : ∀ w ∈ UKb, DifferentiableAt ℝ (fun z => matMoebius (Bf z) z) w ∧
      0 < ((fun z => matMoebius (Bf z) z) w).im ∧
      ‖dzbar (fun z => matMoebius (Bf z) z) w‖ ≤ Cb ∧
      (1 : ℝ) / 2 ≤ ‖dz (fun z => matMoebius (Bf z) z) w‖ ∧
      0 < (fderiv ℝ (fun z => matMoebius (Bf z) z) w).det) :
    (∀ z : ℂ, 0 < z.im →
      ((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0) ∧
    (∀ z : ℂ, 0 < z.im → 0 < ((fun z => matMoebius (Bf z) z) z).im) ∧
    (∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      (fun z => matMoebius (Bf z) z) (moebiusMap (↑β) z)
        = moebiusMap (θ β) ((fun z => matMoebius (Bf z) z) z)) ∧
    (∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 1 (fun z => matMoebius (Bf z) z) z) ∧
    (∀ z : ℂ, 0 < z.im → 0 < (fderiv ℝ (fun z => matMoebius (Bf z) z) z).det ∧
      ‖dzbar (fun z => matMoebius (Bf z) z) z‖
        ≤ κ * ‖dz (fun z => matMoebius (Bf z) z) z‖) := by
  obtain ⟨hm, hhdef⟩ : ∃ h : ℂ → ℂ, h = fun z => matMoebius (Bf z) z := ⟨_, rfl⟩
  have hopenH : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have himhm : ∀ w ∈ UKb, 0 < (hm w).im := by
    intro w hw
    have h := (hpk w hw).2.1
    rw [hhdef]
    exact h
  have hdUKb : ∀ w ∈ UKb, DifferentiableAt ℝ hm w := by
    intro w hw
    have h := (hpk w hw).1
    rw [hhdef]
    exact h
  have hmsmUK : ContDiffOn ℝ 1 hm UK := by
    rw [hhdef]
    exact hsmUK
  have hglob : ∀ z : ℂ, 0 < z.im →
      (((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0) ∧ 0 < (hm z).im := by
    intro z hz
    obtain ⟨γ, w, hwim, hwUKb, hwdef, hzw⟩ := htransport z hz
    obtain ⟨Am, hAm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((θ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨_, rfl⟩
    obtain ⟨Cm, hCm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
    have hBz : Bf z = Am * (Bf w * Cm) := by
      conv_lhs => rw [hzw]
      rw [hBequi γ w hwim, Matrix.mul_assoc, hAm, hCm]
    have hdenCm : ((Cm 1 0 : ℝ) : ℂ) * z + ((Cm 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hCm]
      exact moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hz)
    have hmCz : matMoebius Cm z = w := by
      rw [hCm, matMoebius_coe, hwdef]
      rfl
    have hdenBC : (((Bf w * Cm) 1 0 : ℝ) : ℂ) * z + (((Bf w * Cm) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden (Bf w) Cm z hdenCm]
      refine mul_ne_zero ?_ hdenCm
      rw [hmCz]
      exact hdenUK w (hUKbUK hwUKb)
    have hmBCz : matMoebius (Bf w * Cm) z = matMoebius (Bf w) w := by
      rw [zz_matmul (Bf w) Cm z hdenCm hdenBC, hmCz]
    have hdenθ : moebiusDenom (θ γ) (hm w) ≠ 0 :=
      moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt (himhm w hwUKb))
    have hdenθ' : ((Am 1 0 : ℝ) : ℂ) * matMoebius (Bf w * Cm) z
        + ((Am 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hmBCz, hAm]
      have hh : matMoebius (Bf w) w = hm w := by
        rw [hhdef]
      rw [hh]
      exact hdenθ
    have hdenABC : (((Am * (Bf w * Cm)) 1 0 : ℝ) : ℂ) * z
        + (((Am * (Bf w * Cm)) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden Am (Bf w * Cm) z hdenBC]
      exact mul_ne_zero hdenθ' hdenBC
    constructor
    · rw [hBz]
      exact hdenABC
    · have hval : matMoebius (Bf z) z = moebiusMap (θ γ) (matMoebius (Bf w) w) := by
        rw [hBz, zz_matmul Am (Bf w * Cm) z hdenBC hdenABC, hmBCz, hAm, matMoebius_coe]
      have hgoal : hm z = moebiusMap (θ γ) (hm w) := by
        rw [hhdef]
        exact hval
      rw [hgoal]
      exact moebiusMap_im_pos _ (himhm w hwUKb)
  have hdenglobal : ∀ z : ℂ, 0 < z.im →
      ((Bf z 1 0 : ℝ) : ℂ) * z + ((Bf z 1 1 : ℝ) : ℂ) ≠ 0 := fun z hz => (hglob z hz).1
  have himglobal : ∀ z : ℂ, 0 < z.im → 0 < (hm z).im := fun z hz => (hglob z hz).2
  have hequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      hm (moebiusMap (↑β) z) = moebiusMap (θ β) (hm z) := by
    intro β z hz
    have hzim' : 0 < (moebiusMap (↑β) z).im := moebiusMap_im_pos _ hz
    obtain ⟨Am, hAm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
      ⟨_, rfl⟩
    obtain ⟨Cm, hCm⟩ : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        X = ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
    have hBz : Bf (moebiusMap (↑β) z) = Am * (Bf z * Cm) := by
      rw [hBequi β z hz, Matrix.mul_assoc, hAm, hCm]
    have hdenCm : ((Cm 1 0 : ℝ) : ℂ) * (moebiusMap (↑β) z) + ((Cm 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [hCm]
      exact moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hzim')
    have hmCz : matMoebius Cm (moebiusMap (↑β) z) = z := by
      rw [hCm, matMoebius_coe]
      rw [moebiusMap_mul ((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ (↑β) z
        (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hz))]
      rw [inv_mul_cancel, moebiusMap_one]
    have hdenBC : (((Bf z * Cm) 1 0 : ℝ) : ℂ) * (moebiusMap (↑β) z)
        + (((Bf z * Cm) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden (Bf z) Cm _ hdenCm]
      refine mul_ne_zero ?_ hdenCm
      rw [hmCz]
      exact hdenglobal z hz
    have hmBC : matMoebius (Bf z * Cm) (moebiusMap (↑β) z) = matMoebius (Bf z) z := by
      rw [zz_matmul (Bf z) Cm _ hdenCm hdenBC, hmCz]
    have hdenABC : (((Am * (Bf z * Cm)) 1 0 : ℝ) : ℂ) * (moebiusMap (↑β) z)
        + (((Am * (Bf z * Cm)) 1 1 : ℝ) : ℂ) ≠ 0 := by
      rw [zz_matden Am (Bf z * Cm) _ hdenBC]
      refine mul_ne_zero ?_ hdenBC
      rw [hmBC, hAm]
      have hh : matMoebius (Bf z) z = hm z := by
        rw [hhdef]
      rw [hh]
      exact moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt (himglobal z hz))
    have hval : matMoebius (Bf (moebiusMap (↑β) z)) (moebiusMap (↑β) z)
        = moebiusMap (θ β) (matMoebius (Bf z) z) := by
      rw [hBz, zz_matmul Am (Bf z * Cm) _ hdenBC hdenABC, hmBC, hAm, matMoebius_coe]
    rw [hhdef]
    exact hval
  have hEEglob : ∀ (γ : ↥Γ') (x : ℂ), 0 < x.im →
      hm x = moebiusMap (θ γ) (hm (moebiusMap (↑(γ⁻¹ : ↥Γ')) x)) := by
    intro γ x hx
    have hxin : 0 < (moebiusMap (↑(γ⁻¹ : ↥Γ')) x).im := moebiusMap_im_pos _ hx
    have h := hequi γ (moebiusMap (↑(γ⁻¹ : ↥Γ')) x) hxin
    have hcancel : moebiusMap (↑γ) (moebiusMap (↑(γ⁻¹ : ↥Γ')) x) = x := by
      rw [moebiusMap_mul (↑γ) (↑(γ⁻¹ : ↥Γ')) x
        (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hx))]
      have hone : (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (↑(γ⁻¹ : ↥Γ')) = 1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
      rw [hone, moebiusMap_one]
    rwa [hcancel] at h
  have hmC1 : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 1 hm z := by
    intro z hz
    obtain ⟨γ, w, hwim, hwUKb, hwdef, hzw⟩ := htransport z hz
    have hinner : ContDiffAt ℝ 1 (moebiusMap (↑(γ⁻¹ : ↥Γ'))) z :=
      zz_moeb_cdiff _ z hz
    have hmid : ContDiffAt ℝ 1 hm (moebiusMap (↑(γ⁻¹ : ↥Γ')) z) := by
      rw [← hwdef]
      exact (hmsmUK w (hUKbUK hwUKb)).contDiffAt (hUKopen.mem_nhds (hUKbUK hwUKb))
    have houter : ContDiffAt ℝ 1 (moebiusMap (θ γ))
        (hm (moebiusMap (↑(γ⁻¹ : ↥Γ')) z)) := by
      refine zz_moeb_cdiff _ _ ?_
      rw [← hwdef]
      exact himhm w hwUKb
    refine ((ContDiffAt.comp z houter (ContDiffAt.comp z hmid hinner)).congr_of_eventuallyEq
      ?_)
    filter_upwards [hopenH.mem_nhds hz] with x hx
    exact hEEglob γ x hx
  have hjb : ∀ z : ℂ, 0 < z.im →
      0 < (fderiv ℝ hm z).det ∧ ‖dzbar hm z‖ ≤ κ * ‖dz hm z‖ := by
    intro z hz
    obtain ⟨γ, w, hwim, hwUKb, hwdef, hzw⟩ := htransport z hz
    obtain ⟨hdw0, _, hbarw0, hdzw0, hdetw0⟩ := hpk w hwUKb
    have hdw : DifferentiableAt ℝ hm w := by
      rw [hhdef]
      exact hdw0
    have hbarw : ‖dzbar hm w‖ ≤ Cb := by
      rw [hhdef]
      exact hbarw0
    have hdzw : (1 : ℝ) / 2 ≤ ‖dz hm w‖ := by
      rw [hhdef]
      exact hdzw0
    have hdetw : 0 < (fderiv ℝ hm w).det := by
      rw [hhdef]
      exact hdetw0
    obtain ⟨hdz', him', q₁, q₂, hq1ne, hqeq, hdzq, hdzbarq⟩ :=
      zz_transport (θ γ) (↑(γ⁻¹ : ↥Γ')) hm z w hz hwim hwdef (hEEglob γ) hdw
        (himhm w hwUKb)
    have hq1pos : 0 < ‖q₁‖ := norm_pos_iff.mpr hq1ne
    have hbase : ‖dzbar hm w‖ ≤ κ * ‖dz hm w‖ := by
      have h2 : κ / 2 ≤ κ * ‖dz hm w‖ := by
        have h3 := mul_le_mul_of_nonneg_left hdzw hκ.le
        linarith [h3]
      linarith [hbarw, hCbκ, h2]
    constructor
    · rw [det_fderiv_eq_wirtinger, hdzq, hdzbarq, norm_mul, norm_mul, ← hqeq]
      have hdet2 : 0 < ‖dz hm w‖ ^ 2 - ‖dzbar hm w‖ ^ 2 := by
        rw [← det_fderiv_eq_wirtinger]
        exact hdetw
      have h4 : 0 < ‖q₁‖ ^ 2 * (‖dz hm w‖ ^ 2 - ‖dzbar hm w‖ ^ 2) :=
        mul_pos (pow_pos hq1pos 2) hdet2
      nlinarith [h4]
    · rw [hdzq, hdzbarq, norm_mul, norm_mul, ← hqeq]
      calc ‖q₁‖ * ‖dzbar hm w‖ ≤ ‖q₁‖ * (κ * ‖dz hm w‖) :=
            mul_le_mul_of_nonneg_left hbase hq1pos.le
        _ = κ * (‖q₁‖ * ‖dz hm w‖) := by ring
  refine ⟨hdenglobal, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h := himglobal z hz
    rwa [hhdef] at h
  · intro β z hz
    have h := hequi β z hz
    rwa [hhdef] at h
  · intro z hz
    have h := hmC1 z hz
    rwa [hhdef] at h
  · intro z hz
    have h := hjb z hz
    rwa [hhdef] at h

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The uniform ball estimates transport the contraction data through hyperbolic isometries;
-- the default heartbeat budget does not cover the elaboration.
/-- **Uniform two-sided ball bounds for the developed map**: exact equivariance, transport
of base points into the analyzed region and the near-identity derivative bounds there give
injectivity on hyperbolic quarter-balls and surjectivity onto hyperbolic balls of a fixed
radius around image points, at every point of the upper half plane. -/
private lemma zz_uniform {Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (θ : ↥Γ' → Matrix.SpecialLinearGroup (Fin 2) ℝ) (F : ℂ → ℂ) (UKb : Set ℂ)
    (Cv : ℝ)
    (htr : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ) (hw : 0 < w.im), w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w ∧
      ∀ (x : ℂ) (hx : 0 < x.im),
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 → x ∈ UKb)
    (hequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      F (moebiusMap (↑β) z) = moebiusMap (θ β) (F z))
    (hFim : ∀ z : ℂ, 0 < z.im → 0 < (F z).im)
    (hd : ∀ w ∈ UKb, DifferentiableAt ℝ F w)
    (hop : ∀ w ∈ UKb, ‖fderiv ℝ F w - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hval : ∀ w ∈ UKb, ‖F w - w‖ ≤ Cv)
    (hCvim : ∀ w : ℂ, w ∈ UKb → Cv ≤ w.im)
    (hUKbsub : UKb ⊆ {x : ℂ | 0 < x.im}) :
    (∀ (z a b : ℂ) (hz : 0 < z.im) (ha : 0 < a.im) (hb : 0 < b.im),
      dist (⟨a, ha⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) < 1 / 4 →
      dist (⟨b, hb⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) < 1 / 4 →
      F a = F b → a = b) ∧
    (∀ (z ξ : ℂ) (hz : 0 < z.im) (hξ : 0 < ξ.im) (hFz : 0 < (F z).im),
      dist (⟨ξ, hξ⟩ : UpperHalfPlane) (⟨F z, hFz⟩ : UpperHalfPlane) < 1 / 2048 →
      ∃ (x : ℂ) (hx : 0 < x.im),
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨z, hz⟩ : UpperHalfPlane) < 1 / 32 ∧ F x = ξ) := by
  -- Möbius maps are injective on the upper half plane
  have hinvmoe : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x y : ℂ),
      0 < x.im → 0 < y.im → moebiusMap g x = moebiusMap g y → x = y := by
    intro g x y hx hy hxy
    have hcanc : ∀ u : ℂ, 0 < u.im → moebiusMap g⁻¹ (moebiusMap g u) = u := by
      intro u hu
      rw [moebiusMap_mul g⁻¹ g u (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hu)),
        inv_mul_cancel, moebiusMap_one]
    calc x = moebiusMap g⁻¹ (moebiusMap g x) := (hcanc x hx).symm
      _ = moebiusMap g⁻¹ (moebiusMap g y) := by rw [hxy]
      _ = y := hcanc y hy
  have hcanc : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (u : ℂ), 0 < u.im →
      moebiusMap g (moebiusMap g⁻¹ u) = u := by
    intro g u hu
    rw [moebiusMap_mul g g⁻¹ u (moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hu)),
      mul_inv_cancel, moebiusMap_one]
  -- transported points and distances
  have hmk : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : ℂ) (hx : 0 < x.im),
      (⟨moebiusMap g x, moebiusMap_im_pos g hx⟩ : UpperHalfPlane)
        = g • (⟨x, hx⟩ : UpperHalfPlane) := by
    intro g x hx
    ext
    change moebiusMap g x = ((g • (⟨x, hx⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
    rw [coe_smul_eq_moebiusMap g (⟨x, hx⟩ : UpperHalfPlane)]
  have hdsmul : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x y : ℂ)
      (hx : 0 < x.im) (hy : 0 < y.im),
      dist (⟨moebiusMap g x, moebiusMap_im_pos g hx⟩ : UpperHalfPlane)
        (⟨moebiusMap g y, moebiusMap_im_pos g hy⟩ : UpperHalfPlane)
        = dist (⟨x, hx⟩ : UpperHalfPlane) (⟨y, hy⟩ : UpperHalfPlane) := by
    intro g x y hx hy
    rw [hmk g x hx, hmk g y hy]
    exact (isometry_smul UpperHalfPlane g).dist_eq _ _
  constructor
  · -- injectivity on hyperbolic quarter-balls
    intro z a b hz ha hb hda hdb hFab
    obtain ⟨γ, w, hw, hwUKb, hwdef, hzw, hball⟩ := htr z hz
    obtain ⟨a', ha'def⟩ : ∃ x : ℂ, x = moebiusMap (↑(γ⁻¹ : ↥Γ')) a := ⟨_, rfl⟩
    obtain ⟨b', hb'def⟩ : ∃ x : ℂ, x = moebiusMap (↑(γ⁻¹ : ↥Γ')) b := ⟨_, rfl⟩
    have ha'im : 0 < a'.im := by
      rw [ha'def]
      exact moebiusMap_im_pos _ ha
    have hb'im : 0 < b'.im := by
      rw [hb'def]
      exact moebiusMap_im_pos _ hb
    have hda' : dist (⟨a', ha'im⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 := by
      have h1 : (⟨a', ha'im⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) a, moebiusMap_im_pos _ ha⟩ : UpperHalfPlane) := by
        ext
        change a' = moebiusMap (↑(γ⁻¹ : ↥Γ')) a
        exact ha'def
      have h2 : (⟨w, hw⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) z, moebiusMap_im_pos _ hz⟩ : UpperHalfPlane) := by
        ext
        change w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z
        exact hwdef
      rw [h1, h2, hdsmul (↑(γ⁻¹ : ↥Γ')) a z ha hz]
      exact hda
    have hdb' : dist (⟨b', hb'im⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 := by
      have h1 : (⟨b', hb'im⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) b, moebiusMap_im_pos _ hb⟩ : UpperHalfPlane) := by
        ext
        change b' = moebiusMap (↑(γ⁻¹ : ↥Γ')) b
        exact hb'def
      have h2 : (⟨w, hw⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑(γ⁻¹ : ↥Γ')) z, moebiusMap_im_pos _ hz⟩ : UpperHalfPlane) := by
        ext
        change w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z
        exact hwdef
      rw [h1, h2, hdsmul (↑(γ⁻¹ : ↥Γ')) b z hb hz]
      exact hdb
    -- the euclidean form of the quarter-ball
    obtain ⟨S, hSdef⟩ : ∃ S : Set ℂ, S = Metric.ball
        ((((((⟨w, hw⟩ : UpperHalfPlane) : ℂ)).re : ℝ) : ℂ)
          + (((⟨w, hw⟩ : UpperHalfPlane).im * Real.cosh (1 / 4) : ℝ) : ℂ) * Complex.I)
        ((⟨w, hw⟩ : UpperHalfPlane).im * Real.sinh (1 / 4)) := ⟨_, rfl⟩
    have hSmem : ∀ x : ℂ, x ∈ S ↔ ∃ hx : 0 < x.im,
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 := by
      intro x
      rw [hSdef]
      exact zz_ball (⟨w, hw⟩ : UpperHalfPlane) (1 / 4) (by norm_num) x
    have hSsub : S ⊆ UKb := by
      intro x hx
      obtain ⟨hxim, hxd⟩ := (hSmem x).mp hx
      exact hball x hxim hxd
    have hSconv : Convex ℝ S := by
      rw [hSdef]
      exact convex_ball _ _
    have hinjS : Set.InjOn F S :=
      zz_inj F S hSconv (fun x hx => hd x (hSsub hx)) (fun x hx => hop x (hSsub hx))
    -- pulled equality of values
    have haeq : a = moebiusMap (↑γ) a' := by
      rw [ha'def]
      rw [show ((↑(γ⁻¹ : ↥Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        = ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ from rfl]
      exact (hcanc (↑γ) a ha).symm
    have hbeq : b = moebiusMap (↑γ) b' := by
      rw [hb'def]
      rw [show ((↑(γ⁻¹ : ↥Γ') : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        = ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹ from rfl]
      exact (hcanc (↑γ) b hb).symm
    have hFa'b' : F a' = F b' := by
      have h1 : F a = moebiusMap (θ γ) (F a') := by
        rw [haeq]
        exact hequi γ a' ha'im
      have h2 : F b = moebiusMap (θ γ) (F b') := by
        rw [hbeq]
        exact hequi γ b' hb'im
      rw [h1, h2] at hFab
      exact hinvmoe (θ γ) (F a') (F b') (hFim a' ha'im) (hFim b' hb'im) hFab
    have ha'b' : a' = b' :=
      hinjS ((hSmem a').mpr ⟨ha'im, hda'⟩) ((hSmem b').mpr ⟨hb'im, hdb'⟩) hFa'b'
    rw [haeq, hbeq, ha'b']
  · -- surjectivity onto fixed hyperbolic balls around image points
    intro z ξ hz hξ hFz hdist
    obtain ⟨γ, w, hw, hwUKb, hwdef, hzw, hball⟩ := htr z hz
    have hwim := hw
    -- the closed base ball lies in the analyzed region
    have hcBsub : Metric.closedBall w (w.im / 128) ⊆ UKb := by
      intro x hx
      rw [Metric.mem_closedBall] at hx
      have hxball : x ∈ Metric.ball ((⟨w, hw⟩ : UpperHalfPlane) : ℂ)
          ((⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2) := by
        rw [Metric.mem_ball]
        change dist x w < (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2
        have h64 : (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2 = w.im / 64 := by
          change w.im * (1 / 32) / 2 = w.im / 64
          ring
        rw [h64]
        have hwpos : 0 < w.im := hw
        linarith
      obtain ⟨hxim, hxd⟩ := (zz_ballcomp (⟨w, hw⟩ : UpperHalfPlane) (1 / 32)
        (by norm_num) (by norm_num)).1 x hxball
      exact hball x hxim (lt_trans hxd (by norm_num))
    have hr128 : 0 < w.im / 128 := by
      have hwpos : 0 < w.im := hw
      positivity
    obtain ⟨hinjcB, hsurjcB⟩ := zz_surj F w (w.im / 128) hr128
      (fun x hx => hd x (hcBsub hx)) (fun x hx => hop x (hcBsub hx))
    obtain ⟨ξ', hξ'def⟩ : ∃ x : ℂ, x = moebiusMap (θ γ)⁻¹ ξ := ⟨_, rfl⟩
    have hξ'im : 0 < ξ'.im := by
      rw [hξ'def]
      exact moebiusMap_im_pos _ hξ
    have hFweq : F z = moebiusMap (θ γ) (F w) := by
      conv_lhs => rw [hzw]
      exact hequi γ w hw
    have hFwim : 0 < (F w).im := hFim w hw
    have hdξ' : dist (⟨ξ', hξ'im⟩ : UpperHalfPlane) (⟨F w, hFwim⟩ : UpperHalfPlane)
        < 1 / 2048 := by
      have h1 : (⟨ξ, hξ⟩ : UpperHalfPlane)
          = (⟨moebiusMap (θ γ) ξ', moebiusMap_im_pos _ hξ'im⟩ : UpperHalfPlane) := by
        ext
        change ξ = moebiusMap (θ γ) ξ'
        rw [hξ'def]
        exact (hcanc (θ γ) ξ hξ).symm
      have h2 : (⟨F z, hFz⟩ : UpperHalfPlane)
          = (⟨moebiusMap (θ γ) (F w), moebiusMap_im_pos _ hFwim⟩ : UpperHalfPlane) := by
        ext
        change F z = moebiusMap (θ γ) (F w)
        exact hFweq
      rw [h1, h2, hdsmul (θ γ) ξ' (F w) hξ'im hFwim] at hdist
      exact hdist
    have himFw : (F w).im ≤ 2 * w.im := by
      have h1 : |(F w - w).im| ≤ ‖F w - w‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 := hval w hwUKb
      have h3 := hCvim w hwUKb
      have h4 := (abs_le.mp h1).2
      linarith
    have hξ'E : ξ' ∈ Metric.closedBall (F w) (w.im / 128 / 4) := by
      have h1 := (zz_ballcomp (⟨F w, hFwim⟩ : UpperHalfPlane) (1 / 2048)
        (by norm_num) (by norm_num)).2 ξ' hξ'im hdξ'
      rw [Metric.mem_ball] at h1
      have hcoe : dist ξ' ((⟨F w, hFwim⟩ : UpperHalfPlane) : ℂ) = dist ξ' (F w) := rfl
      have himeq : 2 * (⟨F w, hFwim⟩ : UpperHalfPlane).im * (1 / 2048)
          = 2 * (F w).im * (1 / 2048) := rfl
      rw [hcoe, himeq] at h1
      rw [Metric.mem_closedBall]
      have h2 : 2 * (F w).im * (1 / 2048) ≤ w.im / 128 / 4 := by
        have hwpos : 0 < w.im := hw
        nlinarith [himFw]
      linarith
    obtain ⟨x, hxcB, hFx⟩ := hsurjcB ξ' hξ'E
    have hxUKb := hcBsub hxcB
    have hxim : 0 < x.im := hUKbsub hxUKb
    have hxE64 : x ∈ Metric.ball ((⟨w, hw⟩ : UpperHalfPlane) : ℂ)
        ((⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2) := by
      rw [Metric.mem_ball]
      change dist x w < (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2
      have h64 : (⟨w, hw⟩ : UpperHalfPlane).im * (1 / 32) / 2 = w.im / 64 := by
        change w.im * (1 / 32) / 2 = w.im / 64
        ring
      rw [h64]
      rw [Metric.mem_closedBall] at hxcB
      have hwpos : 0 < w.im := hw
      linarith
    obtain ⟨hxim', hxd⟩ := (zz_ballcomp (⟨w, hw⟩ : UpperHalfPlane) (1 / 32)
      (by norm_num) (by norm_num)).1 x hxE64
    obtain ⟨X, hXdef⟩ : ∃ X : ℂ, X = moebiusMap (↑γ) x := ⟨_, rfl⟩
    have hXim : 0 < X.im := by
      rw [hXdef]
      exact moebiusMap_im_pos _ hxim'
    refine ⟨X, hXim, ?_, ?_⟩
    · have h1 : (⟨X, hXim⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑γ) x, moebiusMap_im_pos _ hxim'⟩ : UpperHalfPlane) := by
        ext
        change X = moebiusMap (↑γ) x
        exact hXdef
      have h2 : (⟨z, hz⟩ : UpperHalfPlane)
          = (⟨moebiusMap (↑γ) w, moebiusMap_im_pos _ hw⟩ : UpperHalfPlane) := by
        ext
        change z = moebiusMap (↑γ) w
        exact hzw
      rw [h1, h2, hdsmul (↑γ) x w hxim' hw]
      exact hxd
    · rw [hXdef]
      have h1 : F (moebiusMap (↑γ) x) = moebiusMap (θ γ) (F x) := hequi γ x hxim'
      rw [h1, hFx, hξ'def]
      exact hcanc (θ γ) ξ hξ

-- The proof below is a single large compound estimate/assembly; elaboration exceeds the
-- default heartbeat budget, so it is raised to the campaign cap of 400000.
set_option maxHeartbeats 400000 in
-- The covering-space construction assembles trivializations from the uniform ball bounds;
-- the default heartbeat budget does not cover the elaboration.
/-- **Bijectivity of a uniformly balanced self-map of the upper half plane**: a continuous
open map with uniform ball injectivity and uniform ball surjectivity is a covering map of
the simply connected upper half plane, hence bijective. -/
private lemma zz_homeo (p : UpperHalfPlane → UpperHalfPlane)
    (hpc : Continuous p)
    (hopen : IsOpenMap p)
    (hinj : ∀ z a b : UpperHalfPlane, dist a z < 1 / 4 → dist b z < 1 / 4 →
      p a = p b → a = b)
    (hsurj : ∀ z ξ : UpperHalfPlane, dist ξ (p z) < 1 / 2048 →
      ∃ x : UpperHalfPlane, dist x z < 1 / 32 ∧ p x = ξ) :
    Function.Bijective p := by
  -- ==== surjectivity: the range is clopen in a preconnected space ====
  have hsurj_glob : Function.Surjective p := by
    have hropen : IsOpen (Set.range p) := by
      rw [show Set.range p = p '' Set.univ from (Set.image_univ).symm]
      exact hopen _ isOpen_univ
    have hrclosed : IsClosed (Set.range p) := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro ξ hξ
      rw [Metric.mem_nhds_iff]
      refine ⟨1 / 2048, by norm_num, ?_⟩
      intro η hη
      rw [Metric.mem_ball] at hη
      intro hmem
      obtain ⟨z, hz⟩ := hmem
      refine hξ ?_
      obtain ⟨x, _, hxp⟩ := hsurj z ξ (by
        rw [hz]
        rwa [dist_comm] at hη)
      exact ⟨x, hxp⟩
    have hne : (Set.range p).Nonempty := ⟨p UpperHalfPlane.I, ⟨UpperHalfPlane.I, rfl⟩⟩
    have huniv : Set.range p = Set.univ := IsClopen.eq_univ ⟨hrclosed, hropen⟩ hne
    exact Set.range_eq_univ.mp huniv
  -- ==== the covering structure ====
  have hcov : IsCoveringMap p := by
    intro ξ
    -- discreteness of the fiber
    haveI hdisc : DiscreteTopology ↥(p ⁻¹' {ξ}) := by
      rw [discreteTopology_iff_isOpen_singleton]
      rintro ⟨e, he⟩
      have hset : ({(⟨e, he⟩ : ↥(p ⁻¹' {ξ}))} : Set ↥(p ⁻¹' {ξ}))
          = Subtype.val ⁻¹' (Metric.ball e (1 / 4)) := by
        ext ⟨x, hx⟩
        simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball,
          Subtype.mk.injEq]
        constructor
        · rintro rfl
          rw [dist_self]
          norm_num
        · intro hdx
          have hpe : p x = p e := by
            rw [Set.mem_preimage, Set.mem_singleton_iff] at hx he
            rw [hx, he]
          exact hinj x x e (by rw [dist_self]; norm_num)
            (by rw [dist_comm]; exact hdx) hpe
      rw [hset]
      exact (Metric.isOpen_ball).preimage continuous_subtype_val
    -- the trivializing data
    have hsheet : ∀ z : ↥(p ⁻¹' Metric.ball ξ (1 / 2048)), ∃ e : ↥(p ⁻¹' {ξ}),
        dist (z : UpperHalfPlane) (e : UpperHalfPlane) < 1 / 32 := by
      rintro ⟨z, hz⟩
      rw [Set.mem_preimage, Metric.mem_ball] at hz
      obtain ⟨x, hxd, hxp⟩ := hsurj z ξ (by rwa [dist_comm] at hz)
      refine ⟨⟨x, ?_⟩, ?_⟩
      · rw [Set.mem_preimage, Set.mem_singleton_iff]
        exact hxp
      · rw [dist_comm] at hxd
        exact hxd
    choose sh hsh using hsheet
    have hshuniq : ∀ (z : ↥(p ⁻¹' Metric.ball ξ (1 / 2048))) (e : ↥(p ⁻¹' {ξ})),
        dist (z : UpperHalfPlane) (e : UpperHalfPlane) < 1 / 8 → e = sh z := by
      intro z e hd
      have h1 := hsh z
      have hpe : p (e : UpperHalfPlane) = p (sh z : UpperHalfPlane) := by
        have he' := (e : ↥(p ⁻¹' {ξ})).2
        have hs' := (sh z).2
        rw [Set.mem_preimage, Set.mem_singleton_iff] at he' hs'
        rw [he', hs']
      refine Subtype.ext ?_
      refine hinj (z : UpperHalfPlane) (e : UpperHalfPlane) ((sh z : UpperHalfPlane))
        ?_ ?_ hpe
      · calc dist (e : UpperHalfPlane) (z : UpperHalfPlane)
            = dist (z : UpperHalfPlane) (e : UpperHalfPlane) := dist_comm _ _
          _ < 1 / 8 := hd
          _ < 1 / 4 := by norm_num
      · calc dist ((sh z : UpperHalfPlane)) (z : UpperHalfPlane)
            = dist (z : UpperHalfPlane) ((sh z : UpperHalfPlane)) := dist_comm _ _
          _ < 1 / 32 := h1
          _ < 1 / 4 := by norm_num
    have hsec : ∀ (u : ↥(Metric.ball ξ (1 / 2048))) (e : ↥(p ⁻¹' {ξ})),
        ∃ x : UpperHalfPlane, dist x (e : UpperHalfPlane) < 1 / 32
          ∧ p x = (u : UpperHalfPlane) := by
      rintro ⟨u, hu⟩ ⟨e, he⟩
      rw [Metric.mem_ball] at hu
      rw [Set.mem_preimage, Set.mem_singleton_iff] at he
      obtain ⟨x, hxd, hxp⟩ := hsurj e u (by rw [he]; exact hu)
      exact ⟨x, hxd, hxp⟩
    choose sec hsecd hsecp using hsec
    -- assemble the trivializing homeomorphism
    refine ⟨hdisc, Metric.ball ξ (1 / 2048), Metric.mem_ball_self (by norm_num),
      Metric.isOpen_ball, Metric.isOpen_ball.preimage hpc, ?_, ?_⟩
    · refine ⟨⟨fun z => (⟨p (z : UpperHalfPlane), z.2⟩, sh z),
        fun ue => ⟨sec ue.1 ue.2, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      · rw [Set.mem_preimage, hsecp ue.1 ue.2]
        exact ue.1.2
      · -- left inverse
        intro z
        refine Subtype.ext ?_
        have h1 := hsecd (⟨p (z : UpperHalfPlane), z.2⟩ : ↥(Metric.ball ξ (1 / 2048))) (sh z)
        have h2 := hsecp (⟨p (z : UpperHalfPlane), z.2⟩ : ↥(Metric.ball ξ (1 / 2048))) (sh z)
        have h3 := hsh z
        refine hinj ((sh z : UpperHalfPlane))
          (sec (⟨p (z : UpperHalfPlane), z.2⟩ : ↥(Metric.ball ξ (1 / 2048))) (sh z))
          (z : UpperHalfPlane) ?_ ?_ ?_
        · calc dist (sec _ (sh z)) ((sh z : UpperHalfPlane)) < 1 / 32 := h1
            _ < 1 / 4 := by norm_num
        · calc dist (z : UpperHalfPlane) ((sh z : UpperHalfPlane)) < 1 / 32 := h3
            _ < 1 / 4 := by norm_num
        · rw [h2]
      · -- right inverse
        rintro ⟨u, e⟩
        refine Prod.ext ?_ ?_
        · refine Subtype.ext ?_
          exact hsecp u e
        · refine (hshuniq _ e ?_).symm
          calc dist ((sec u e : UpperHalfPlane)) ((e : UpperHalfPlane)) < 1 / 32 :=
              hsecd u e
            _ < 1 / 8 := by norm_num
      · -- continuity of the forward map
        refine Continuous.prodMk ?_ ?_
        · exact Continuous.subtype_mk (hpc.comp continuous_subtype_val) _
        · rw [continuous_discrete_rng]
          intro e
          have hset : (fun z : ↥(p ⁻¹' Metric.ball ξ (1 / 2048)) => sh z) ⁻¹' {e}
              = Subtype.val ⁻¹' (Metric.ball (e : UpperHalfPlane) (1 / 8)) := by
            ext z
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball]
            constructor
            · intro hze
              rw [← hze]
              have := hsh z
              rw [dist_comm] at this
              calc dist ((z : UpperHalfPlane)) ((sh z : UpperHalfPlane)) < 1 / 32 := hsh z
                _ < 1 / 8 := by norm_num
            · intro hd
              exact (hshuniq z e hd).symm
          rw [hset]
          exact (Metric.isOpen_ball).preimage continuous_subtype_val
      · -- continuity of the inverse map
        rw [continuous_iff_continuousAt]
        rintro ⟨u, e⟩
        have hslice : ∀ᶠ v : ↥(Metric.ball ξ (1 / 2048)) × ↥(p ⁻¹' {ξ})
            in nhds (u, e), v.2 = e := by
          have h1 : ({e} : Set ↥(p ⁻¹' {ξ})) ∈ nhds e := by
            rw [nhds_discrete]
            exact Set.mem_singleton e
          have h2 : (Set.univ ×ˢ ({e} : Set ↥(p ⁻¹' {ξ}))) ∈ nhds ((u, e)) := by
            rw [nhds_prod_eq]
            exact Filter.prod_mem_prod Filter.univ_mem h1
          filter_upwards [h2] with v hv
          exact hv.2
        -- continuity of the fixed-sheet section
        have hseccont : Continuous fun u' : ↥(Metric.ball ξ (1 / 2048)) => sec u' e := by
          rw [continuous_iff_continuousAt]
          intro u'
          rw [ContinuousAt, Filter.tendsto_iff_forall_eventually_mem]
          intro W hW
          rw [Metric.mem_nhds_iff] at hW
          obtain ⟨r, hr, hrW⟩ := hW
          obtain ⟨r', hr'def⟩ : ∃ x : ℝ, x = min r (1 / 48) := ⟨_, rfl⟩
          have hr'0 : 0 < r' := by
            rw [hr'def]
            exact lt_min hr (by norm_num)
          have hT : IsOpen (p '' Metric.ball (sec u' e) r') := hopen _ Metric.isOpen_ball
          have hTmem : (u' : UpperHalfPlane) ∈ p '' Metric.ball (sec u' e) r' := by
            refine ⟨sec u' e, Metric.mem_ball_self hr'0, hsecp u' e⟩
          have hnb : Subtype.val ⁻¹' (p '' Metric.ball (sec u' e) r')
              ∈ nhds u' := by
            refine (hT.preimage continuous_subtype_val).mem_nhds ?_
            exact hTmem
          filter_upwards [hnb] with u'' hu''
          rw [Set.mem_preimage] at hu''
          obtain ⟨y, hyball, hyp⟩ := hu''
          rw [Metric.mem_ball] at hyball
          -- the section value at u'' equals y
          have hyeq : sec u'' e = y := by
            refine hinj ((e : UpperHalfPlane)) (sec u'' e) y ?_ ?_ ?_
            · calc dist (sec u'' e) ((e : UpperHalfPlane)) < 1 / 32 := hsecd u'' e
                _ < 1 / 4 := by norm_num
            · have hd1 : dist y (sec u' e) < 1 / 48 := by
                refine lt_of_lt_of_le hyball ?_
                rw [hr'def]
                exact min_le_right _ _
              have hd2 : dist (sec u' e) ((e : UpperHalfPlane)) < 1 / 32 := hsecd u' e
              calc dist y ((e : UpperHalfPlane))
                  ≤ dist y (sec u' e) + dist (sec u' e) ((e : UpperHalfPlane)) :=
                    dist_triangle _ _ _
                _ < 1 / 48 + 1 / 32 := by exact add_lt_add hd1 hd2
                _ < 1 / 4 := by norm_num
            · rw [hsecp u'' e, hyp]
          rw [hyeq]
          refine hrW ?_
          rw [Metric.mem_ball]
          refine lt_of_lt_of_le hyball ?_
          rw [hr'def]
          exact min_le_left _ _
        -- combine along the constant-sheet slice
        have hcomb0 : Continuous (fun v : ↥(Metric.ball ξ (1 / 2048))
            × ↥(p ⁻¹' {ξ}) => (⟨sec v.1 e, by
              rw [Set.mem_preimage, hsecp v.1 e]
              exact v.1.2⟩ : ↥(p ⁻¹' Metric.ball ξ (1 / 2048)))) := by
          refine Continuous.subtype_mk ?_ _
          exact hseccont.fst'
        have hcombined := hcomb0.continuousAt (x := (u, e))
        refine hcombined.congr ?_
        filter_upwards [hslice] with v hv
        rw [← hv]
    · intro z
      rfl
  -- ==== injectivity via monodromy over the simply connected plane ====
  refine ⟨?_, hsurj_glob⟩
  intro a b hab
  symm
  obtain ⟨γq⟩ := PathConnectedSpace.joined a b
  obtain ⟨σ, hσdef⟩ : ∃ σ : Path (p a) (p a), σ = (γq.map hpc).cast rfl hab :=
    ⟨_, rfl⟩
  have hhom : σ.Homotopic (Path.refl (p a)) := SimplyConnectedSpace.paths_homotopic _ _
  obtain ⟨H⟩ := hhom
  have hend := hcov.liftPath_apply_one_eq_of_homotopicRel
    (γ₀ := σ.toContinuousMap) (γ₁ := (Path.refl (p a)).toContinuousMap) ⟨H⟩ a
    (by simp) (by simp)
  -- the given path is the lift of `σ`
  have hlift : (γq.toContinuousMap : C(unitInterval, UpperHalfPlane))
      = hcov.liftPath σ.toContinuousMap a (by simp) := by
    rw [IsCoveringMap.eq_liftPath_iff']
    constructor
    · funext t
      rw [hσdef]
      rfl
    · simp
  have hconst : hcov.liftPath (Path.refl (p a)).toContinuousMap a (by simp)
      = ContinuousMap.const _ a := by
    have h := hcov.liftPath_const (e := a) (x := p a) rfl
    convert h using 2
  calc b = γq.toContinuousMap 1 := by simp
    _ = hcov.liftPath σ.toContinuousMap a (by simp) 1 := by rw [hlift]
    _ = hcov.liftPath (Path.refl (p a)).toContinuousMap a (by simp) 1 := hend
    _ = a := by rw [hconst]; rfl

set_option maxHeartbeats 400000 in
-- The development assembles the monodromy homomorphism, the averaged coefficient field and
-- the covering endgame in one declaration; the default heartbeat budget does not cover it.
/-- **Development of the interpolation.** Along a generator tuple converging to the tuple of
a cocompact, trace-gapped limit group, the corrected tile maps of the Dirichlet tiling
develop, for every `κ > 0` and eventually in `n`, into a self-map `h` of the upper half
plane with two-sided inverse `hinv`, continuous with continuous inverse, locally Sobolev,
with almost-everywhere positive Jacobian and Beltrami quotient at most `κ`, and intertwining
the generator tuples exactly on the upper half plane. -/
theorem exists_developed_interpolation
    {ι : Type} [Finite ι] {ε : ℝ} (hε : 0 < ε)
    (Γ : ℕ → Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (_hΓ : ∀ n, IsFuchsianGroup (Γ n))
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
      (∀ z : ℂ, 0 < z.im → 0 < (h z).im) ∧
      (∀ z : ℂ, 0 < z.im → 0 < (hinv z).im) ∧
      (∀ z : ℂ, 0 < z.im → hinv (h z) = z) ∧
      (∀ z : ℂ, 0 < z.im → h (hinv z) = z) ∧
      ContinuousOn h {z : ℂ | 0 < z.im} ∧
      ContinuousOn hinv {z : ℂ | 0 < z.im} ∧
      MemWklocP h 1 2 {z : ℂ | 0 < z.im} ∧
      (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), 0 < (fderiv ℝ h z).det) ∧
      (∀ᵐ z ∂(volume.restrict {z : ℂ | 0 < z.im}), ‖dzbar h z‖ ≤ κ * ‖dz h z‖) ∧
      ∀ i, ∀ z : ℂ, 0 < z.im → h (moebiusMap (ρ i) z) = moebiusMap (gens n i) (h z) := by
  classical
  intro κ hκ
  -- ==== §0 the limit group and the orbit-density radius ====
  obtain ⟨Γ', hΓ'⟩ : ∃ X, X = Subgroup.closure (Set.range ρ) := ⟨_, rfl⟩
  rw [← hΓ'] at hgapρ hccρ
  have hΓ'fuchs : IsFuchsianGroup Γ' := by
    rw [hΓ']
    rw [hΓ'] at hgapρ
    exact isFuchsianGroup_of_trace_gap hε hgapρ
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ : UpperHalfPlane, τ = UpperHalfPlane.I := ⟨_, rfl⟩
  obtain ⟨R, hRpos, hdense⟩ := exists_orbit_density_bound hΓ'fuchs hε hgapρ hccρ τ₀
  haveI : IsIsometricSMul (↥Γ') UpperHalfPlane :=
    ⟨fun c => isometry_smul UpperHalfPlane (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)⟩
  -- ==== §1 the covering family of hyperbolic balls, as euclidean balls ====
  obtain ⟨RV, hRVdef⟩ : ∃ x : ℝ, x = 2 * R + 5 := ⟨_, rfl⟩
  have hRV0 : 0 < RV := by rw [hRVdef]; linarith
  obtain ⟨VV, hVVdef⟩ : ∃ V : ↥Γ' → Set ℂ, V = fun γ => Metric.ball
      (((((γ • τ₀ : UpperHalfPlane) : ℂ).re : ℝ) : ℂ)
        + (((γ • τ₀ : UpperHalfPlane).im * Real.cosh RV : ℝ) : ℂ) * Complex.I)
      ((γ • τ₀ : UpperHalfPlane).im * Real.sinh RV) := ⟨_, rfl⟩
  have hVmem : ∀ (γ : ↥Γ') (z : ℂ), z ∈ VV γ ↔
      ∃ hz : 0 < z.im, dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) < RV := by
    intro γ z
    rw [hVVdef]
    exact zz_ball (γ • τ₀) RV hRV0 z
  have hVsub : ∀ γ : ↥Γ', VV γ ⊆ {z : ℂ | 0 < z.im} := by
    intro γ z hz
    obtain ⟨hzim, _⟩ := (hVmem γ z).mp hz
    exact hzim
  have hVopen : ∀ γ : ↥Γ', IsOpen (VV γ) := by
    intro γ
    rw [hVVdef]
    exact Metric.isOpen_ball
  have hVcov : ∀ z : ℂ, 0 < z.im → ∃ γ : ↥Γ', z ∈ VV γ := by
    intro z hz
    have h1 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀) ≤ R :=
      hdense _
    have hne : (MulAction.orbit (↥Γ') τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    have h2 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀)
        < R + 1 := by linarith
    obtain ⟨y, hymem, hylt⟩ := (Metric.infDist_lt_iff hne).mp h2
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hymem
    refine ⟨γ, (hVmem γ z).mpr ⟨hz, ?_⟩⟩
    rw [hRVdef]
    linarith
  have hcoesmul : ∀ (β : ↥Γ') (τ : UpperHalfPlane),
      ((β • τ : UpperHalfPlane) : ℂ) = moebiusMap (↑β) (τ : ℂ) :=
    fun β τ => coe_smul_eq_moebiusMap (↑β) τ
  have hVtrans : ∀ (β γ : ↥Γ') (z : ℂ), z ∈ VV γ → moebiusMap (↑β) z ∈ VV (β * γ) := by
    intro β γ z hz
    obtain ⟨hzim, hd⟩ := (hVmem γ z).mp hz
    have hzim' : 0 < (moebiusMap (↑β) z).im := moebiusMap_im_pos (↑β) hzim
    refine (hVmem (β * γ) (moebiusMap (↑β) z)).mpr ⟨hzim', ?_⟩
    have hpt : (⟨moebiusMap (↑β) z, hzim'⟩ : UpperHalfPlane)
        = β • (⟨z, hzim⟩ : UpperHalfPlane) := by
      ext
      rw [hcoesmul β ⟨z, hzim⟩]
    rw [hpt, mul_smul]
    rw [show dist (β • (⟨z, hzim⟩ : UpperHalfPlane)) (β • γ • τ₀)
      = dist (⟨z, hzim⟩ : UpperHalfPlane) (γ • τ₀) from dist_smul β _ _]
    exact hd
  have hi₀ : ((τ₀ : ℂ)) ∈ VV 1 := by
    refine (hVmem 1 (τ₀ : ℂ)).mpr ⟨?_, ?_⟩
    · rw [UpperHalfPlane.coe_im]
      exact τ₀.im_pos
    · have hτeq : (⟨(τ₀ : ℂ), by rw [UpperHalfPlane.coe_im]; exact τ₀.im_pos⟩
          : UpperHalfPlane) = τ₀ := by
        ext
        rfl
      rw [hτeq, show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _, dist_self]
      exact hRV0
  have hV1conv : Convex ℝ (VV 1) := by
    rw [hVVdef]
    exact convex_ball _ _
  -- ==== §2 words and the local datum ====
  have hword : ∀ γ : ↥Γ', ∃ l : List (ι × Bool), wordEval ρ l = ↑γ := by
    intro γ
    refine exists_wordEval_eq_of_mem_closure ?_
    rw [← hΓ']
    exact γ.2
  choose wrd hwrd using hword
  obtain ⟨tmap, htmapdef⟩ : ∃ t : ℕ → ↥Γ' → Matrix.SpecialLinearGroup (Fin 2) ℝ,
      t = fun n γ => wordEval (gens n) (wrd γ) := ⟨_, rfl⟩
  have htmem : ∀ (n : ℕ) (γ : ↥Γ'), tmap n γ ∈ Γ n := by
    intro n γ
    rw [htmapdef]
    exact wordEval_mem (hmem n) (wrd γ)
  have htconv : ∀ γ : ↥Γ',
      Filter.Tendsto (fun n => tmap n γ) Filter.atTop (nhds (↑γ)) := by
    intro γ
    rw [htmapdef]
    have h := tendsto_wordEval hlim (wrd γ)
    rwa [hwrd γ] at h
  -- ==== §3 finite interaction sets ====
  have hSfin : ∀ r : ℝ, {γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ r}.Finite :=
    fun r => zz_fin hΓ'fuchs τ₀ τ₀ r
  have hOlap : ∀ γ : ↥Γ', (VV 1 ∩ VV γ).Nonempty → dist τ₀ (γ • τ₀) ≤ 2 * RV := by
    rintro γ ⟨q, hq1, hqγ⟩
    obtain ⟨hqim, hd1⟩ := (hVmem 1 q).mp hq1
    obtain ⟨hqim', hdγ⟩ := (hVmem γ q).mp hqγ
    rw [show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _] at hd1
    have htri := dist_triangle τ₀ (⟨q, hqim⟩ : UpperHalfPlane) (γ • τ₀)
    rw [dist_comm τ₀ (⟨q, hqim⟩ : UpperHalfPlane)] at htri
    linarith
  have hStriple : {p : ↥Γ' × ↥Γ' | (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}.Finite := by
    have hinj : Set.InjOn (fun p : ↥Γ' × ↥Γ' => (p.1, p.1 * p.2)) Set.univ := by
      intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      obtain ⟨h1', h2'⟩ := hpq
      rw [h1'] at h2'
      exact Prod.ext h1' (mul_left_cancel h2')
    have hsub : {p : ↥Γ' × ↥Γ' | (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}
        ⊆ (fun p : ↥Γ' × ↥Γ' => (p.1, p.1 * p.2)) ⁻¹'
          ({γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ 2 * RV} ×ˢ
            {γ : ↥Γ' | dist τ₀ (γ • τ₀) ≤ 2 * RV}) := by
      rintro ⟨a, b⟩ hp
      obtain ⟨q, ⟨hq1, hqa⟩, hqab⟩ := hp
      constructor
      · exact hOlap a ⟨q, hq1, hqa⟩
      · exact hOlap (a * b) ⟨q, hq1, hqab⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.preimage (hinj.mono (Set.subset_univ _)) ?_
    exact (hSfin (2 * RV)).prod (hSfin (2 * RV))
  -- ==== §4 anchor chains for the generators ====
  have hgen_mem : ∀ i : ι, ρ i ∈ Γ' := by
    intro i
    rw [hΓ']
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨ri, hridef⟩ : ∃ r : ι → ↥Γ', r = fun i => ⟨ρ i, hgen_mem i⟩ := ⟨_, rfl⟩
  have hri : ∀ i, (↑(ri i) : Matrix.SpecialLinearGroup (Fin 2) ℝ) = ρ i := by
    intro i
    rw [hridef]
  have hanchor : ∀ i : ι, ∃ (N : ℕ) (g : ℕ → ↥Γ'), 0 < N ∧
      (∀ k < N, ∀ t : ℝ, (k : ℝ) / N ≤ t → t ≤ ((k : ℝ) + 1) / N →
        ((τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))) ∈ VV (g k)) := by
    intro i
    have hτim : 0 < (τ₀ : ℂ).im := by
      rw [UpperHalfPlane.coe_im]
      exact τ₀.im_pos
    have hqim : 0 < (moebiusMap (↑(ri i)) (τ₀ : ℂ)).im := moebiusMap_im_pos _ hτim
    refine zz_chain_exists VV hVopen _ ?_ ?_
    · exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    · intro t ht0 ht1
      refine hVcov _ ?_
      have him : ((τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))).im
          = (1 - t) * (τ₀ : ℂ).im + t * (moebiusMap (↑(ri i)) (τ₀ : ℂ)).im := by
        simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.sub_re, zero_mul, add_zero]
        ring
      rw [him]
      rcases le_or_gt t (1 / 2) with hc | hc
      · nlinarith
      · nlinarith
  choose Nanc ganc hNanc hsanc using hanchor
  -- the coe of chain values telescopes to the target
  have hsubty : ∀ (N : ℕ) (g : ℕ → ↥Γ') (γt : ↥Γ'), 0 < N →
      ((↑(g 0) : Matrix.SpecialLinearGroup (Fin 2) ℝ) * ((List.range (N - 1)).map
        fun k => (↑((g k)⁻¹ * g (k + 1)) : Matrix.SpecialLinearGroup (Fin 2) ℝ)).prod
        * (↑((g (N - 1))⁻¹ * γt) : Matrix.SpecialLinearGroup (Fin 2) ℝ)) = ↑γt := by
    intro N g γt hN
    exact zz_telescope (Γ'.subtype) N hN g γt
  -- ==== §5 the eventual conditions ====
  have hE1 : ∀ᶠ n in Filter.atTop, ∀ a b : ↥Γ',
      (VV 1 ∩ VV a ∩ VV (a * b)).Nonempty → tmap n a * tmap n b = tmap n (a * b) := by
    have hcond : ∀ p : ↥Γ' × ↥Γ', (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty →
        ∀ᶠ n in Filter.atTop, tmap n p.1 * tmap n p.2 = tmap n (p.1 * p.2) := by
      rintro ⟨a, b⟩ _
      refine zz_ev_eq hε Γ hgap (a := fun n => tmap n a * tmap n b)
        (b := fun n => tmap n (a * b)) (fun n => mul_mem (htmem n a) (htmem n b))
        (fun n => htmem n (a * b)) (L := ↑(a * b)) ?_ (htconv (a * b))
      have h := (htconv a).mul (htconv b)
      rwa [← Subgroup.coe_mul] at h
    -- reduce to the finite triple set
    have hfin := hStriple
    have hsubty' : ∀ᶠ n in Filter.atTop, ∀ p : ↥({p : ↥Γ' × ↥Γ' |
        (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}), tmap n (p : ↥Γ' × ↥Γ').1
          * tmap n (p : ↥Γ' × ↥Γ').2 = tmap n ((p : ↥Γ' × ↥Γ').1 * (p : ↥Γ' × ↥Γ').2) := by
      haveI : Finite ↥({p : ↥Γ' × ↥Γ' | (VV 1 ∩ VV p.1 ∩ VV (p.1 * p.2)).Nonempty}) :=
        hfin.to_subtype
      rw [Filter.eventually_all]
      intro p
      exact hcond (p : ↥Γ' × ↥Γ') p.2
    filter_upwards [hsubty'] with n hn a b hab
    exact hn ⟨(a, b), hab⟩
  have hE2 : ∀ᶠ n in Filter.atTop, ∀ i : ι,
      tmap n (ganc i 0) * ((List.range (Nanc i - 1)).map
        fun k => tmap n ((ganc i k)⁻¹ * ganc i (k + 1))).prod
        * tmap n ((ganc i (Nanc i - 1))⁻¹ * ri i) = gens n i := by
    rw [Filter.eventually_all]
    intro i
    refine zz_ev_eq hε Γ hgap
      (a := fun n => tmap n (ganc i 0) * ((List.range (Nanc i - 1)).map
        fun k => tmap n ((ganc i k)⁻¹ * ganc i (k + 1))).prod
        * tmap n ((ganc i (Nanc i - 1))⁻¹ * ri i))
      (b := fun n => gens n i) ?_ (fun n => hmem n i) (L := ρ i) ?_ (hlim i)
    · intro n
      refine mul_mem (mul_mem (htmem n _) ?_) (htmem n _)
      refine Subgroup.list_prod_mem _ ?_
      intro x hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      exact htmem n _
    · have h := zz_val_tendsto tmap (fun γ : ↥Γ' => (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ))
        htconv (Nanc i) (ganc i) (ri i)
      rw [hsubty (Nanc i) (ganc i) (ri i) (hNanc i), hri i] at h
      exact h
  -- ==== §6 the equivariant weight family ====
  obtain ⟨UK, UKb, SACT, uψ, Mψ, Rz, imK, hUKopen, hUKsub, hUKbopen, hUKbconv, hUKbUK,
    hUKbmem, hRz1, hRzUK, hMψ0, himK0, himUK, huψ01, huψsm, huψD, hsum1, huψvanUK,
    hSACTdist, huψequi, hFz⟩ := zz_weights hΓ'fuchs τ₀ R hRpos hdense
  -- ==== §8 the smallness threshold and eventual closeness ====
  obtain ⟨CM, hCMdef⟩ : ∃ x : ℝ, x = 1 + (SACT.card : ℝ) * Mψ := ⟨_, rfl⟩
  have hCM1 : 1 ≤ CM := by
    rw [hCMdef]
    have h1 : (0 : ℝ) ≤ (SACT.card : ℝ) * Mψ := mul_nonneg (by positivity) hMψ0
    linarith
  have hCM0 : 0 < CM := by linarith
  obtain ⟨ε₂, hε₂def⟩ : ∃ x : ℝ, x = min (min (1 / (1000 * CM * Rz ^ 2))
      (κ / (128 * CM * Rz ^ 2))) (imK / (100 * CM * Rz ^ 2)) := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by
    rw [hε₂def]
    have hRz0 : (0 : ℝ) < Rz := by linarith
    refine lt_min (lt_min ?_ ?_) ?_ <;> positivity
  have hsm1 : CM * ε₂ * Rz ^ 2 ≤ 1 / 1000 := by
    have h := le_trans (le_of_eq hε₂def)
      (le_trans (min_le_left _ _) (min_le_left _ _))
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1000 * CM * Rz ^ 2)] at h
    nlinarith [h]
  have hsm2 : 128 * (CM * ε₂) * Rz ^ 2 ≤ κ := by
    have h := le_trans (le_of_eq hε₂def)
      (le_trans (min_le_left _ _) (min_le_right _ _))
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 128 * CM * Rz ^ 2)] at h
    nlinarith [h]
  have hsm3 : 100 * (CM * ε₂) * Rz ^ 2 ≤ imK := by
    have h := le_trans (le_of_eq hε₂def) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 * CM * Rz ^ 2)] at h
    nlinarith [h]
  have hE3 : ∀ᶠ n in Filter.atTop, ∀ γ ∈ SACT, ∀ i j : Fin 2,
      |((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
          : Matrix (Fin 2) (Fin 2) ℝ) i j
        - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
    have hper : ∀ γ : ↥Γ', ∀ᶠ n in Filter.atTop, ∀ i j : Fin 2,
        |((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            : Matrix (Fin 2) (Fin 2) ℝ) i j
          - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
      intro γ
      have hconv : Filter.Tendsto (fun n => tmap n γ * (↑γ)⁻¹) Filter.atTop
          (nhds ((↑γ) * (↑γ)⁻¹)) := (htconv γ).mul tendsto_const_nhds
      rw [mul_inv_cancel] at hconv
      have hmat := tendsto_subtype_rng.mp hconv
      rw [Matrix.SpecialLinearGroup.coe_one] at hmat
      refine Filter.eventually_all.mpr ?_
      intro i
      refine Filter.eventually_all.mpr ?_
      intro j
      have hent : Filter.Tendsto (fun n =>
          ((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            : Matrix (Fin 2) (Fin 2) ℝ) i j) Filter.atTop
          (nhds ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)) :=
        ((continuous_apply_apply i j).tendsto _).comp hmat
      have habs : Filter.Tendsto (fun n =>
          |((tmap n γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
              : Matrix (Fin 2) (Fin 2) ℝ) i j
            - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|) Filter.atTop (nhds 0) := by
        have h := hent.sub (tendsto_const_nhds
          (x := (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (f := Filter.atTop))
        rw [sub_self] at h
        have habs0 : |(0 : ℝ)| = 0 := abs_zero
        exact habs0 ▸ h.abs
      exact (habs.eventually_lt_const hε₂0).mono (fun n h => h.le)
    have hall : ∀ᶠ n in Filter.atTop, ∀ γ : {x // x ∈ SACT}, ∀ i j : Fin 2,
        |((tmap n (γ : ↥Γ') * (↑(γ : ↥Γ'))⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
            : Matrix (Fin 2) (Fin 2) ℝ) i j
          - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ :=
      Filter.eventually_all.mpr (fun γ => hper (γ : ↥Γ'))
    filter_upwards [hall] with n hn γ hγ
    exact hn ⟨γ, hγ⟩
  -- ==== §9 the developed map, for large n ====
  filter_upwards [hE1, hE2, hE3] with n htrip' hanc' hclose'
  obtain ⟨θ, hθmul, hθf, hθmemS, hθval⟩ := zz_mfunc VV ((τ₀ : ℂ)) hVsub hVopen hVcov
    hVtrans hi₀ hV1conv (tmap n) htrip'
  have hθΓn : ∀ γ : ↥Γ', θ γ ∈ Γ n := hθmemS (Γ n) (htmem n)
  have hθgen : ∀ i : ι, θ (ri i) = gens n i := by
    intro i
    have hcont : Continuous (fun t : ℝ =>
        (τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have h0 : (τ₀ : ℂ) + ((0 : ℝ) : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))
        = (τ₀ : ℂ) := by
      push_cast
      ring
    have h1 : (τ₀ : ℂ) + ((1 : ℝ) : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ))
        = moebiusMap (↑(ri i)) (τ₀ : ℂ) := by
      push_cast
      ring
    have h := hθval (ri i) (fun t : ℝ =>
        (τ₀ : ℂ) + (t : ℂ) * (moebiusMap (↑(ri i)) (τ₀ : ℂ) - (τ₀ : ℂ)))
      (Nanc i) (ganc i) hcont h0 h1 (hNanc i) (hsanc i)
    rw [h]
    exact hanc' i
  have hθact : ∀ γ ∈ SACT, θ γ = tmap n γ := by
    intro γ hγ
    have hγ' := hSACTdist γ hγ
    have him : 0 < ((γ • τ₀ : UpperHalfPlane) : ℂ).im := by
      rw [UpperHalfPlane.coe_im]
      exact (γ • τ₀).im_pos
    have hpt : (⟨((γ • τ₀ : UpperHalfPlane) : ℂ), him⟩ : UpperHalfPlane) = γ • τ₀ := by
      ext
      rfl
    refine hθf γ ⟨((γ • τ₀ : UpperHalfPlane) : ℂ), ⟨?_, ?_⟩⟩
    · refine (hVmem 1 _).mpr ⟨him, ?_⟩
      rw [hpt, show ((1 : ↥Γ') • τ₀) = τ₀ from one_smul _ _, dist_comm]
      rw [hRVdef]
      linarith [hγ']
    · refine (hVmem γ _).mpr ⟨him, ?_⟩
      rw [hpt, dist_self]
      exact hRV0
  -- the coefficient matrices and their closeness to the identity
  obtain ⟨cmt, hcmtdef⟩ : ∃ c : ↥Γ' → Matrix (Fin 2) (Fin 2) ℝ,
      c = fun γ => ((θ γ * (↑γ)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
        : Matrix (Fin 2) (Fin 2) ℝ) := ⟨_, rfl⟩
  have hcmclose : ∀ γ ∈ SACT, ∀ i j : Fin 2,
      |cmt γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ ε₂ := by
    intro γ hγ i j
    rw [hcmtdef]
    simp only
    rw [hθact γ hγ]
    exact hclose' γ hγ i j
  have hcmdet : ∀ γ : ↥Γ', (cmt γ).det = 1 := by
    intro γ
    rw [hcmtdef]
    exact Matrix.SpecialLinearGroup.det_coe _
  -- the averaged coefficient field
  obtain ⟨Bf, hBdef⟩ : ∃ B : ℂ → Matrix (Fin 2) (Fin 2) ℝ,
      B = fun z => ∑' γ : ↥Γ', uψ γ z • cmt γ := ⟨_, rfl⟩
  have hBrep : ∀ z : ℂ, 0 < z.im → ∀ (F : Finset ↥Γ'),
      (∀ γ : ↥Γ', γ ∉ F → uψ γ z = 0) → Bf z = ∑ γ ∈ F, uψ γ z • cmt γ := by
    intro z hz F hvan
    rw [hBdef]
    refine tsum_eq_sum ?_
    intro γ hγ
    rw [hvan γ hγ, zero_smul]
  have hcmequi : ∀ β γ : ↥Γ', cmt (β * γ)
      = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        * cmt γ * ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
          : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro β γ
    rw [hcmtdef]
    simp only
    rw [hθmul β γ]
    rw [show ((↑(β * γ) : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
      = (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
        * (↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ from by
        rw [Subgroup.coe_mul, mul_inv_rev]]
    rw [show θ β * θ γ * ((↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹
        * (↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹)
      = θ β * (θ γ * (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹)
        * (↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ from by group]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  -- equivariance of the field
  have hBequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      Bf (moebiusMap (↑β) z)
        = ((θ β : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          * Bf z * ((((↑β : Matrix.SpecialLinearGroup (Fin 2) ℝ))⁻¹
            : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro β z hz
    obtain ⟨F, hvanz⟩ := hFz z hz
    have hvanβ : ∀ γ : ↥Γ', γ ∉ F.image (fun δ => β * δ) →
        uψ γ (moebiusMap (↑β) z) = 0 := by
      intro γ hγ
      have hne : β⁻¹ * γ ∉ F := by
        intro hmem'
        exact hγ (Finset.mem_image.mpr ⟨β⁻¹ * γ, hmem', by group⟩)
      have h := huψequi β (β⁻¹ * γ) z hz
      rw [show β * (β⁻¹ * γ) = γ from by group] at h
      rw [h]
      exact hvanz _ hne
    rw [hBrep _ (moebiusMap_im_pos _ hz) _ hvanβ, hBrep z hz F hvanz]
    rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel h)]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro δ hδ
    rw [huψequi β δ z hz, hcmequi β δ]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  -- ==== §10 the developed map and the pointwise package on the inner region ====
  obtain ⟨hm, hhdef⟩ : ∃ h : ℂ → ℂ, h = fun z => matMoebius (Bf z) z := ⟨_, rfl⟩
  have hεRzsmall : ε₂ * Rz + ε₂ ≤ 1 / 2 := by
    have ha : 0 ≤ ε₂ * Rz * (Rz - 1) :=
      mul_nonneg (mul_nonneg hε₂0.le (by linarith [hRz1] : (0 : ℝ) ≤ Rz))
        (by linarith [hRz1] : (0 : ℝ) ≤ Rz - 1)
    have hb : 0 ≤ (CM - 1) * (ε₂ * Rz ^ 2) :=
      mul_nonneg (by linarith [hCM1] : (0 : ℝ) ≤ CM - 1)
        (mul_nonneg hε₂0.le (sq_nonneg Rz))
    have hc : 0 ≤ ε₂ * (Rz ^ 2 - 1) :=
      mul_nonneg hε₂0.le (by nlinarith [hRz1] : (0 : ℝ) ≤ Rz ^ 2 - 1)
    nlinarith [hsm1, ha, hb, hc]
  obtain ⟨hBentry, hBD, hBDb, hdenUK⟩ := zz_field UK hUKopen UKb hUKbUK SACT uψ cmt
    Rz ε₂ Mψ hε₂0 hRzUK (fun γ z hz => huψ01 γ z hz) huψsm
    huψD hsum1 hcmclose Bf
    (fun z hz => hBrep z (hUKsub hz) SACT (fun γ hγ => huψvanUK z hz γ hγ)) hεRzsmall
  obtain ⟨εP, hεPdef⟩ : ∃ x : ℝ, x = CM * ε₂ := ⟨_, rfl⟩
  have hεP0 : 0 < εP := by
    rw [hεPdef]
    positivity
  have hεPsmall : εP * Rz ^ 2 ≤ 1 / 1000 := by
    rw [hεPdef]
    nlinarith [hsm1]
  have hε₂εP : ε₂ ≤ εP := by
    rw [hεPdef]
    nlinarith [hε₂0, hCM1]
  have hBDb' : ∀ z ∈ UKb, ∀ i j : Fin 2,
      ‖∑ γ ∈ SACT, (cmt γ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
        • fderiv ℝ (uψ γ) z‖ ≤ εP := by
    intro z hz i j
    refine le_trans (hBDb z hz i j) ?_
    rw [hεPdef, hCMdef]
    nlinarith [hε₂0, hMψ0, Nat.cast_nonneg (α := ℝ) SACT.card]
  have hBentry' : ∀ z ∈ UK, ∀ i j : Fin 2,
      |Bf z i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ εP := by
    intro z hz i j
    exact le_trans (hBentry z hz i j) hε₂εP
  have hpack : ∀ z ∈ UKb,
      DifferentiableAt ℝ hm z ∧ ‖hm z - z‖ ≤ 8 * Rz ^ 2 * εP ∧
      ‖dzbar hm z‖ ≤ 64 * Rz ^ 2 * εP ∧ (1 : ℝ) / 2 ≤ ‖dz hm z‖ ∧
      ‖fderiv ℝ hm z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 64 * Rz ^ 2 * εP ∧
      0 < (fderiv ℝ hm z).det := by
    intro z hz
    have hzUK := hUKbUK hz
    have hb00 : |Bf z 0 0 - 1| ≤ εP := by
      have h := hBentry' z hzUK 0 0
      rwa [Matrix.one_apply_eq] at h
    have hb01 : |Bf z 0 1| ≤ εP := by
      have h := hBentry' z hzUK 0 1
      rwa [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero] at h
    have hb10 : |Bf z 1 0| ≤ εP := by
      have h := hBentry' z hzUK 1 0
      rwa [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h
    have hb11 : |Bf z 1 1 - 1| ≤ εP := by
      have h := hBentry' z hzUK 1 1
      rwa [Matrix.one_apply_eq] at h
    obtain ⟨hdA, hvA, hoA⟩ := zz_moeb_packA
      (fun w => Bf w 0 0) (fun w => Bf w 0 1) (fun w => Bf w 1 0) (fun w => Bf w 1 1)
      _ _ _ _ z Rz εP hRz1 (hRzUK z hzUK)
      (hBD z hzUK 0 0) (hBD z hzUK 0 1) (hBD z hzUK 1 0) (hBD z hzUK 1 1)
      hεP0.le hb00 hb01 hb10 hb11
      (hBDb' z hz 0 0) (hBDb' z hz 0 1) (hBDb' z hz 1 0) (hBDb' z hz 1 1) hεPsmall
    obtain ⟨hbB, hzB, hdetB⟩ := zz_moeb_packB
      (fun w => Bf w 0 0) (fun w => Bf w 0 1) (fun w => Bf w 1 0) (fun w => Bf w 1 1)
      _ _ _ _ z Rz εP hRz1 (hRzUK z hzUK)
      (hBD z hzUK 0 0) (hBD z hzUK 0 1) (hBD z hzUK 1 0) (hBD z hzUK 1 1)
      hεP0.le hb00 hb01 hb10 hb11
      (hBDb' z hz 0 0) (hBDb' z hz 0 1) (hBDb' z hz 1 0) (hBDb' z hz 1 1) hεPsmall
    rw [hhdef]
    exact ⟨hdA, hvA, hbB, hzB, hoA, hdetB⟩
  -- ==== §11 conjugation and regularity via the globalization package ====
  have htransport0 : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ) (hw : 0 < w.im), w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w ∧
      ∀ (x : ℂ) (hx : 0 < x.im),
        dist (⟨x, hx⟩ : UpperHalfPlane) (⟨w, hw⟩ : UpperHalfPlane) < 1 / 4 → x ∈ UKb := by
    intro z hz
    have h1 : Metric.infDist (⟨z, hz⟩ : UpperHalfPlane) (MulAction.orbit (↥Γ') τ₀) ≤ R :=
      hdense _
    have hne : (MulAction.orbit (↥Γ') τ₀).Nonempty := ⟨τ₀, MulAction.mem_orbit_self τ₀⟩
    obtain ⟨y, hymem, hylt⟩ := (Metric.infDist_lt_iff hne).mp
      (lt_of_le_of_lt h1 (by linarith : R < R + 1))
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hymem
    obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z := ⟨_, rfl⟩
    have hwim : 0 < w.im := by
      rw [hwdef]
      exact moebiusMap_im_pos _ hz
    have hwdist : dist (⟨w, hwim⟩ : UpperHalfPlane) τ₀ < R + 1 := by
      have hpt : (⟨w, hwim⟩ : UpperHalfPlane) = γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane) := by
        ext
        change w = ((γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ)
        rw [hcoesmul γ⁻¹ (⟨z, hz⟩ : UpperHalfPlane), hwdef]
      rw [hpt]
      have hd : dist (γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane)) τ₀
          = dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by
        calc dist (γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane)) τ₀
            = dist (γ • γ⁻¹ • (⟨z, hz⟩ : UpperHalfPlane)) (γ • τ₀) :=
              (dist_smul γ _ _).symm
          _ = dist (⟨z, hz⟩ : UpperHalfPlane) (γ • τ₀) := by rw [smul_inv_smul]
      rw [hd]
      exact hylt
    refine ⟨γ, w, hwim, hUKbmem w hwim (by linarith), hwdef, ?_, ?_⟩
    · rw [hwdef]
      have hden : moebiusDenom (↑(γ⁻¹ : ↥Γ')) z ≠ 0 :=
        moebiusDenom_ne_zero_of_im_ne_zero _ (ne_of_gt hz)
      rw [moebiusMap_mul (↑γ) (↑(γ⁻¹ : ↥Γ')) z hden]
      have hone : (↑γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) * (↑(γ⁻¹ : ↥Γ')) = 1 := by
        rw [← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
      rw [hone, moebiusMap_one]
    · intro x hx hxd
      refine hUKbmem x hx ?_
      have htri := dist_triangle (⟨x, hx⟩ : UpperHalfPlane)
        (⟨w, hwim⟩ : UpperHalfPlane) τ₀
      linarith
  have htransport : ∀ z : ℂ, 0 < z.im → ∃ (γ : ↥Γ') (w : ℂ), 0 < w.im ∧ w ∈ UKb ∧
      w = moebiusMap (↑(γ⁻¹ : ↥Γ')) z ∧ z = moebiusMap (↑γ) w := by
    intro z hz
    obtain ⟨γ, w, hw, h1, h2, h3, _⟩ := htransport0 z hz
    exact ⟨γ, w, hw, h1, h2, h3⟩
  have hBijsm : ∀ i j : Fin 2, ContDiffOn ℝ 1 (fun w => Bf w i j) UK := by
    intro i j z hz
    have hsumsm : ContDiffWithinAt ℝ 1 (fun w => ∑ γ ∈ SACT, uψ γ w * cmt γ i j) UK z := by
      refine ContDiffWithinAt.sum ?_
      intro γ _
      exact ((huψsm γ) z hz).mul contDiffWithinAt_const
    refine hsumsm.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hBrep w (hUKsub hw) SACT (fun γ hγ => huψvanUK w hw γ hγ), Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro γ _
      rw [Matrix.smul_apply, smul_eq_mul]
    · rw [hBrep z (hUKsub hz) SACT (fun γ hγ => huψvanUK z hz γ hγ), Matrix.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro γ _
      rw [Matrix.smul_apply, smul_eq_mul]
  have hmsmUK : ContDiffOn ℝ 1 hm UK := by
    have hnum : ContDiffOn ℝ 1 (fun w => ((Bf w 0 0 : ℝ) : ℂ) * w
        + ((Bf w 0 1 : ℝ) : ℂ)) UK := by
      refine ContDiffOn.add ?_ ?_
      · refine ContDiffOn.mul ?_ contDiffOn_id
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 0 0)
      · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 0 1)
    have hden : ContDiffOn ℝ 1 (fun w => ((Bf w 1 0 : ℝ) : ℂ) * w
        + ((Bf w 1 1 : ℝ) : ℂ)) UK := by
      refine ContDiffOn.add ?_ ?_
      · refine ContDiffOn.mul ?_ contDiffOn_id
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 1 0)
      · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hBijsm 1 1)
    have hq : ContDiffOn ℝ 1 (fun w => (((Bf w 0 0 : ℝ) : ℂ) * w + ((Bf w 0 1 : ℝ) : ℂ))
        * ((((Bf w 1 0 : ℝ) : ℂ) * w + ((Bf w 1 1 : ℝ) : ℂ))⁻¹)) UK :=
      hnum.mul (hden.inv hdenUK)
    refine hq.congr ?_
    intro w hw
    rw [hhdef]
    simp only
    rw [matMoebius, div_eq_mul_inv]
  have hpk0 : ∀ w ∈ UKb, DifferentiableAt ℝ (fun z => matMoebius (Bf z) z) w ∧
      0 < ((fun z => matMoebius (Bf z) z) w).im ∧
      ‖dzbar (fun z => matMoebius (Bf z) z) w‖ ≤ 64 * Rz ^ 2 * εP ∧
      (1 : ℝ) / 2 ≤ ‖dz (fun z => matMoebius (Bf z) z) w‖ ∧
      0 < (fderiv ℝ (fun z => matMoebius (Bf z) z) w).det := by
    intro w hw
    obtain ⟨hd, hval, hbar, hdzl, hop, hdet⟩ := hpack w hw
    have him : 0 < (hm w).im := by
      have h1 : |(hm w - w).im| ≤ ‖hm w - w‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im] at h1
      have h2 := himUK w (hUKbUK hw)
      have h3 : 8 * Rz ^ 2 * εP ≤ 8 / 100 * imK := by
        rw [hεPdef]
        nlinarith [hsm3]
      nlinarith [(abs_le.mp h1).1, hval, h2, himK0, h3]
    exact ⟨by rw [← hhdef]; exact hd, by rw [← hhdef]; exact him,
      by rw [← hhdef]; exact hbar, by rw [← hhdef]; exact hdzl,
      by rw [← hhdef]; exact hdet⟩
  have hCbκ : 2 * (64 * Rz ^ 2 * εP) ≤ κ := by
    rw [hεPdef]
    nlinarith [hsm2]
  have hsm0 : ContDiffOn ℝ 1 (fun z => matMoebius (Bf z) z) UK := by
    rw [← hhdef]
    exact hmsmUK
  obtain ⟨hdenglobal0, himglobal0, hequi0, hmC10, hjb0⟩ := zz_conjreg θ Bf UK UKb hUKopen
    hUKbUK κ (64 * Rz ^ 2 * εP) hκ hCbκ htransport hBequi hdenUK hsm0 hpk0
  have himglobal : ∀ z : ℂ, 0 < z.im → 0 < (hm z).im := by
    intro z hz
    have h := himglobal0 z hz
    rwa [← hhdef] at h
  have hequi : ∀ (β : ↥Γ') (z : ℂ), 0 < z.im →
      hm (moebiusMap (↑β) z) = moebiusMap (θ β) (hm z) := by
    intro β z hz
    have h := hequi0 β z hz
    rwa [← hhdef] at h
  have hmC1 : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 1 hm z := by
    intro z hz
    have h := hmC10 z hz
    rwa [← hhdef] at h
  have hjb : ∀ z : ℂ, 0 < z.im →
      0 < (fderiv ℝ hm z).det ∧ ‖dzbar hm z‖ ≤ κ * ‖dz hm z‖ := by
    intro z hz
    have h := hjb0 z hz
    rwa [← hhdef] at h
  have hopenH : IsOpen {x : ℂ | 0 < x.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcont : ContinuousOn hm {x : ℂ | 0 < x.im} :=
    fun z hz => ((hmC1 z hz).continuousAt).continuousWithinAt
  have hSob : MemWklocP hm 1 2 {x : ℂ | 0 < x.im} :=
    zz_sobolev hm _ hopenH (fun z hz => (hmC1 z hz).contDiffWithinAt)
  have hmeasH : MeasurableSet {x : ℂ | 0 < x.im} := hopenH.measurableSet
  have hjac_ae : ∀ᵐ z ∂(volume.restrict {x : ℂ | 0 < x.im}), 0 < (fderiv ℝ hm z).det :=
    (MeasureTheory.ae_restrict_iff' hmeasH).mpr
      (Filter.Eventually.of_forall (fun z hz => (hjb z hz).1))
  have hbelt_ae : ∀ᵐ z ∂(volume.restrict {x : ℂ | 0 < x.im}),
      ‖dzbar hm z‖ ≤ κ * ‖dz hm z‖ :=
    (MeasureTheory.ae_restrict_iff' hmeasH).mpr
      (Filter.Eventually.of_forall (fun z hz => (hjb z hz).2))
  have hgenequi : ∀ i : ι, ∀ z : ℂ, 0 < z.im →
      hm (moebiusMap (ρ i) z) = moebiusMap (gens n i) (hm z) := by
    intro i z hz
    have h := hequi (ri i) z hz
    rw [hri i, hθgen i] at h
    exact h
  -- ==== §13 the homeomorphism package and the assembly ====
  have hhomeo : ∃ hinv : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → 0 < (hinv z).im) ∧
      (∀ z : ℂ, 0 < z.im → hinv (hm z) = z) ∧
      (∀ z : ℂ, 0 < z.im → hm (hinv z) = z) ∧
      ContinuousOn hinv {x : ℂ | 0 < x.im} := by
    -- uniform local injectivity/surjectivity at the ℂ-level
    obtain ⟨hinjU, hsurjU⟩ := zz_uniform θ hm UKb (8 * Rz ^ 2 * εP) htransport0 hequi
      himglobal (fun w hw => (hpack w hw).1)
      (fun w hw => le_trans (hpack w hw).2.2.2.2.1 (by rw [hεPdef]; nlinarith [hsm1]))
      (fun w hw => (hpack w hw).2.1)
      (fun w hw => by
        have h2 := himUK w (hUKbUK hw)
        rw [hεPdef]
        nlinarith [hsm3, himK0])
      (fun w hw => hUKsub (hUKbUK hw))
    -- the upper-half-plane self-map
    obtain ⟨pH, hpHdef⟩ : ∃ pH : UpperHalfPlane → UpperHalfPlane,
        pH = fun τ : UpperHalfPlane =>
          (⟨hm ↑τ, himglobal ↑τ τ.coe_im_pos⟩ : UpperHalfPlane) := ⟨_, rfl⟩
    have hpHcoe : ∀ τ : UpperHalfPlane, (pH τ : ℂ) = hm ↑τ := by
      intro τ
      rw [hpHdef]
    have hpHc : Continuous pH := by
      rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
      have h1 : Continuous fun τ : UpperHalfPlane => hm ↑τ :=
        hcont.comp_continuous UpperHalfPlane.continuous_coe (fun τ => τ.coe_im_pos)
      refine h1.congr ?_
      intro τ
      exact (hpHcoe τ).symm
    -- ℂ-level openness of hm on the upper half plane
    have hmapnh : ∀ z : ℂ, 0 < z.im → Filter.map hm (nhds z) = nhds (hm z) := by
      intro z hz
      have hsd : HasStrictFDerivAt hm (fderiv ℝ hm z) z :=
        (hmC1 z hz).hasStrictFDerivAt one_ne_zero
      have hdet : (fderiv ℝ hm z).det ≠ 0 := ne_of_gt (hjb z hz).1
      have hcoe : ((LinearMap.equivOfDetNeZero (fderiv ℝ hm z).toLinearMap
          hdet).toContinuousLinearEquiv : ℂ →L[ℝ] ℂ) = fderiv ℝ hm z := by
        ext x
        rfl
      have hsd' : HasStrictFDerivAt hm
          (((LinearMap.equivOfDetNeZero (fderiv ℝ hm z).toLinearMap
            hdet).toContinuousLinearEquiv : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z := by
        rw [hcoe]
        exact hsd
      exact hsd'.map_nhds_eq_of_equiv
    have himgopen : ∀ V : Set ℂ, IsOpen V → V ⊆ {x : ℂ | 0 < x.im} →
        IsOpen (hm '' V) := by
      intro V hV hVsub
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨z, hzV, rfl⟩
      rw [← hmapnh z (hVsub hzV)]
      exact Filter.image_mem_map (hV.mem_nhds hzV)
    have hpHopen : IsOpenMap pH := by
      intro U hU
      rw [UpperHalfPlane.isOpenEmbedding_coe.isOpen_iff_image_isOpen]
      have himg : ((↑) : UpperHalfPlane → ℂ) '' (pH '' U)
          = hm '' (((↑) : UpperHalfPlane → ℂ) '' U) := by
        ext y
        constructor
        · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
          exact ⟨↑τ, ⟨τ, hτ, rfl⟩, (hpHcoe τ).symm⟩
        · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
          exact ⟨pH τ, ⟨τ, hτ, rfl⟩, hpHcoe τ⟩
      rw [himg]
      refine himgopen _ (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU) ?_
      rintro y ⟨τ, _, rfl⟩
      exact τ.coe_im_pos
    -- ℍ-level uniform local injectivity and surjectivity
    have hinjH : ∀ z a b : UpperHalfPlane, dist a z < 1 / 4 → dist b z < 1 / 4 →
        pH a = pH b → a = b := by
      intro z a b hda hdb hab
      have hab' : hm ↑a = hm ↑b := by
        rw [← hpHcoe a, hab, hpHcoe b]
      exact UpperHalfPlane.ext
        (hinjU ↑z ↑a ↑b z.coe_im_pos a.coe_im_pos b.coe_im_pos hda hdb hab')
    have hsurjH : ∀ z ξ : UpperHalfPlane, dist ξ (pH z) < 1 / 2048 →
        ∃ x : UpperHalfPlane, dist x z < 1 / 32 ∧ pH x = ξ := by
      intro z ξ hd
      rw [hpHdef] at hd
      obtain ⟨x, hx, hxd, hxp⟩ := hsurjU ↑z ↑ξ z.coe_im_pos ξ.coe_im_pos
        (himglobal ↑z z.coe_im_pos) hd
      refine ⟨⟨x, hx⟩, hxd, ?_⟩
      refine UpperHalfPlane.ext ?_
      rw [hpHcoe]
      exact hxp
    -- the global bijection and its homeomorphism upgrade
    have hbij := zz_homeo pH hpHc hpHopen hinjH hsurjH
    obtain ⟨eH, heHdef⟩ : ∃ e : UpperHalfPlane ≃ UpperHalfPlane,
        e = Equiv.ofBijective pH hbij := ⟨_, rfl⟩
    have heHap : ∀ τ : UpperHalfPlane, eH τ = pH τ := by
      intro τ
      rw [heHdef]
      rfl
    have heHc : Continuous (⇑eH) := by
      rw [heHdef]
      exact hpHc
    have heHo : IsOpenMap (⇑eH) := by
      rw [heHdef]
      exact hpHopen
    obtain ⟨HH, hHHdef⟩ : ∃ H : UpperHalfPlane ≃ₜ UpperHalfPlane,
        H = Equiv.toHomeomorphOfContinuousOpen eH heHc heHo := ⟨_, rfl⟩
    have hsymc : Continuous (⇑eH.symm) := by
      have h := HH.symm.continuous
      rw [hHHdef] at h
      exact h
    -- the inverse map and its four clauses
    obtain ⟨hminv0, hminv0def⟩ : ∃ f : ℂ → ℂ,
        f = fun z => if hz : 0 < z.im then (↑(eH.symm ⟨z, hz⟩) : ℂ) else (0 : ℂ) := ⟨_, rfl⟩
    have hminv0eq : ∀ (z : ℂ) (hz : 0 < z.im), hminv0 z = ↑(eH.symm ⟨z, hz⟩) := by
      intro z hz
      rw [hminv0def]
      exact dif_pos hz
    refine ⟨hminv0, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [hminv0eq z hz]
      exact (eH.symm ⟨z, hz⟩).coe_im_pos
    · intro z hz
      rw [hminv0eq (hm z) (himglobal z hz)]
      have hkey : (⟨hm z, himglobal z hz⟩ : UpperHalfPlane) = eH ⟨z, hz⟩ := by
        rw [heHap]
        refine UpperHalfPlane.ext ?_
        change hm z = ↑(pH (⟨z, hz⟩ : UpperHalfPlane))
        rw [hpHcoe]
      rw [hkey, Equiv.symm_apply_apply]
    · intro z hz
      rw [hminv0eq z hz, ← hpHcoe (eH.symm ⟨z, hz⟩), ← heHap, Equiv.apply_symm_apply]
    · rw [continuousOn_iff_continuous_restrict]
      have hfun : ({x : ℂ | 0 < x.im}.restrict hminv0)
          = fun τ : ↥{x : ℂ | 0 < x.im} => (↑(eH.symm ⟨↑τ, τ.2⟩) : ℂ) := by
        funext τ
        exact hminv0eq ↑τ τ.2
      rw [hfun]
      have hin : Continuous fun τ : ↥{x : ℂ | 0 < x.im} =>
          (⟨↑τ, τ.2⟩ : UpperHalfPlane) := by
        rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
        exact continuous_subtype_val
      exact UpperHalfPlane.continuous_coe.comp (hsymc.comp hin)
  obtain ⟨hminv, hinvim, hleft, hright, hinvcont⟩ := hhomeo
  exact ⟨hm, hminv, himglobal, hinvim, hleft, hright, hcont, hinvcont, hSob,
    hjac_ae, hbelt_ae, hgenequi⟩

end RiemannDynamics
