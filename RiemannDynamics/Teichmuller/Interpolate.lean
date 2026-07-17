import RiemannDynamics.Teichmuller.Dirichlet

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

-- The determinant-normalized path derivative chain (polynomial, square root, inverse,
-- product) elaborates as one large term; the bound extraction exceeds the default
-- heartbeat budget.
set_option maxHeartbeats 400000 in
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

-- The per-point Wirtinger package of the correction map combines the path bounds with
-- the Beltrami quotient estimate in a single elaboration exceeding the default budget.
set_option maxHeartbeats 400000 in
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

/-- **Development of the interpolation.** Along a generator tuple converging to the tuple of
a cocompact, trace-gapped limit group, the corrected tile maps of the Dirichlet tiling
develop, for every `κ > 0` and eventually in `n`, into a self-map `h` of the upper half
plane with two-sided inverse `hinv`, continuous with continuous inverse, locally Sobolev,
with almost-everywhere positive Jacobian and Beltrami quotient at most `κ`, and intertwining
the generator tuples exactly on the upper half plane. -/
theorem exists_developed_interpolation
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
  sorry

end RiemannDynamics
