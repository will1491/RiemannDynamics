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
  sorry

/-- The correction path of a determinant-one matrix ends at the matrix. -/
theorem correctionPath_one {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) :
    correctionPath A 1 = A := by
  sorry

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
  sorry

/-! ## The Möbius map of a matrix and the collar transition estimate -/

/-- The Möbius map of a real `2 × 2` matrix, totalized with junk value `0` at the pole. -/
noncomputable def matMoebius (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * z + (M 0 1 : ℂ)) / ((M 1 0 : ℂ) * z + (M 1 1 : ℂ))

/-- On elements of `SL(2, ℝ)` the matrix Möbius map is the plane Möbius map. -/
theorem matMoebius_coe (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) :
    matMoebius (γ : Matrix (Fin 2) (Fin 2) ℝ) z = moebiusMap γ z := by
  sorry

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
  sorry

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
