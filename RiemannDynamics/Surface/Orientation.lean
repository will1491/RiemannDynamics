/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Surface.GenusSurface.Manifold

/-!
# Orientation of plane and surface homeomorphisms via winding numbers

Orientation-preservation is defined by local winding degree: a partial plane
homeomorphism `e` preserves orientation at `z₀` when the image of a small
circle around `z₀` winds exactly once around `e z₀`. The degree is
radius-independent (interpolation of circles), multiplicative under
composition (loops in a punctured disc are freely homotopic to standard
circles traversed `windingNumber` times, by straight-line interpolation of
logarithm lifts), invertible (`deg e · deg e.symm = 1`), local, and equal to
`1` for maps agreeing with an analytic function of nonvanishing derivative.

On a charted surface `S`, a self-homeomorphism preserves orientation when
its chart representatives do at every point. Composition and identity laws
hold unconditionally; inversion and constancy-from-one-point hold on spaces
with an oriented atlas (all transitions of winding degree `1`), which the
genus surface has since its transitions are analytic with nonvanishing
derivative.
-/

open Complex Metric Set Topology Filter TopologicalSpace unitInterval

namespace RiemannDynamics

/-! ## Standard loops and their winding numbers -/

/-- The circle of radius `r` about `z₀`, traversed once counterclockwise. -/
noncomputable def circleLoop (z₀ : ℂ) (r : ℝ) : C(I, ℂ) :=
  ⟨fun t => z₀ + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)),
    by fun_prop⟩

/-- The circle of radius `r` about `z₀`, traversed `n` times. -/
noncomputable def nfoldLoop (z₀ : ℂ) (r : ℝ) (n : ℤ) : C(I, ℂ) :=
  ⟨fun t => z₀ + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n * (t : ℝ))),
    by fun_prop⟩

/-- A once-traversed circle winds once around its center. -/
theorem windingNumber_circleLoop {z₀ : ℂ} {r : ℝ} (hr : 0 < r) :
    windingNumber (circleLoop z₀ r) z₀ = 1 := by
  have happ : ∀ t : I, circleLoop z₀ r t =
      z₀ + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := fun t => rfl
  have hne : ∀ t : I, circleLoop z₀ r t ≠ z₀ := by
    intro t h
    rw [happ t] at h
    have h0 : (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) = 0 := by
      linear_combination h
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _) h0
  have hcl : circleLoop z₀ r 0 = circleLoop z₀ r 1 := by
    rw [happ 0, happ 1]
    norm_num [Complex.exp_two_pi_mul_I]
  obtain ⟨L, hLapp⟩ : ∃ L : C(I, ℂ), ∀ t : I,
      L t = (Real.log r : ℂ) + 2 * Real.pi * Complex.I * (t : ℝ) :=
    ⟨⟨fun t => (Real.log r : ℂ) + 2 * Real.pi * Complex.I * (t : ℝ), by fun_prop⟩,
      fun t => rfl⟩
  have hlift : IsLogLiftOf L (shiftedCurve (circleLoop z₀ r) z₀) := by
    intro t
    have hsh : shiftedCurve (circleLoop z₀ r) z₀ t = circleLoop z₀ r t - z₀ := rfl
    rw [hLapp t, hsh, happ t, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
    ring
  have hspec := windingNumber_spec hcl hne hlift
  have hincr : L 1 - L 0 = 2 * Real.pi * Complex.I := by
    rw [hLapp 1, hLapp 0]
    norm_num
  rw [hincr] at hspec
  have h1 : (2 * (Real.pi : ℂ) * Complex.I) * 1 =
      2 * Real.pi * Complex.I * (windingNumber (circleLoop z₀ r) z₀ : ℂ) := by
    rw [mul_one]; exact hspec
  have h2 := mul_left_cancel₀ Complex.two_pi_I_ne_zero h1
  exact_mod_cast h2.symm

/-- An `n`-fold circle winds `n` times around its center. -/
theorem windingNumber_nfoldLoop {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (n : ℤ) :
    windingNumber (nfoldLoop z₀ r n) z₀ = n := by
  have happ : ∀ t : I, nfoldLoop z₀ r n t =
      z₀ + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n * (t : ℝ))) := fun t => rfl
  have hne : ∀ t : I, nfoldLoop z₀ r n t ≠ z₀ := by
    intro t h
    rw [happ t] at h
    have h0 : (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n * (t : ℝ))) = 0 := by
      linear_combination h
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _) h0
  have hcl : nfoldLoop z₀ r n 0 = nfoldLoop z₀ r n 1 := by
    rw [happ 0, happ 1]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (n * (((1 : I) : ℝ) : ℂ))) = 1 := by
      have : 2 * (Real.pi : ℂ) * Complex.I * (n * (((1 : I) : ℝ) : ℂ)) =
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
        norm_num; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (2 * Real.pi * Complex.I * (n * (((0 : I) : ℝ) : ℂ))) = 1 := by
      norm_num
    rw [h0, h1]
  obtain ⟨L, hLapp⟩ : ∃ L : C(I, ℂ), ∀ t : I,
      L t = (Real.log r : ℂ) + 2 * Real.pi * Complex.I * (n * (t : ℝ)) :=
    ⟨⟨fun t => (Real.log r : ℂ) + 2 * Real.pi * Complex.I * (n * (t : ℝ)), by fun_prop⟩,
      fun t => rfl⟩
  have hlift : IsLogLiftOf L (shiftedCurve (nfoldLoop z₀ r n) z₀) := by
    intro t
    have hsh : shiftedCurve (nfoldLoop z₀ r n) z₀ t = nfoldLoop z₀ r n t - z₀ := rfl
    rw [hLapp t, hsh, happ t, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
    ring
  have hspec := windingNumber_spec hcl hne hlift
  have hincr : L 1 - L 0 = 2 * Real.pi * Complex.I * (n : ℂ) := by
    rw [hLapp 1, hLapp 0]
    norm_num
  rw [hincr] at hspec
  have h2 := mul_left_cancel₀ Complex.two_pi_I_ne_zero hspec
  exact_mod_cast h2.symm

/-- Free-loop homotopy invariance of the winding number: a homotopy through
closed loops avoiding `q` preserves the winding about `q`. -/
theorem windingNumber_eq_of_loopHomotopy {q : ℂ} (H : C(I × I, ℂ))
    (hcl : ∀ s, H (s, 0) = H (s, 1)) (hq : ∀ s t, H (s, t) ≠ q) :
    windingNumber ⟨fun t => H (0, t), by fun_prop⟩ q =
      windingNumber ⟨fun t => H (1, t), by fun_prop⟩ q := by
  obtain ⟨G, hGapp⟩ : ∃ G : I → C(I, ℂ), ∀ s t : I, G s t = H (s, t) :=
    ⟨fun s => ⟨fun t => H (s, t), by fun_prop⟩, fun s t => rfl⟩
  have hGcl : ∀ s : I, G s 0 = G s 1 := by
    intro s
    rw [hGapp s 0, hGapp s 1]
    exact hcl s
  have hGne : ∀ s t : I, G s t ≠ q := by
    intro s t
    rw [hGapp s t]
    exact hq s t
  have hloc : ∀ s₀ : I, ∀ᶠ s in nhds s₀,
      windingNumber (G s) q = windingNumber (G s₀) q := by
    intro s₀
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      (Continuous.continuousOn (((G s₀).continuous.sub continuous_const).norm) :
        ContinuousOn (fun t : I => ‖G s₀ t - q‖) Set.univ)
    have hε : 0 < ‖G s₀ t₀ - q‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hGne s₀ t₀))
    have hUopen : IsOpen {p : I × I | ‖H p - G s₀ p.2‖ < ‖G s₀ t₀ - q‖} :=
      isOpen_lt (Continuous.norm ((map_continuous H).sub
        ((map_continuous (G s₀)).comp continuous_snd))) continuous_const
    have hsub : ({s₀} : Set I) ×ˢ (Set.univ : Set I) ⊆
        {p : I × I | ‖H p - G s₀ p.2‖ < ‖G s₀ t₀ - q‖} := by
      rintro ⟨s, t⟩ ⟨hs, -⟩
      rw [Set.mem_singleton_iff] at hs
      subst hs
      change ‖H (s, t) - G s t‖ < ‖G s t₀ - q‖
      rw [← hGapp s t, sub_self, norm_zero]
      exact hε
    obtain ⟨V, W, hVopen, -, hV, hW, hVW⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ hUopen hsub
    have hs₀V : s₀ ∈ V := hV rfl
    filter_upwards [hVopen.mem_nhds hs₀V] with s hs
    refine (windingNumber_eq_of_dist_lt (hGcl s₀) (hGcl s) fun t => ?_).symm
    have hmem : (s, t) ∈ {p : I × I | ‖H p - G s₀ p.2‖ < ‖G s₀ t₀ - q‖} :=
      hVW (Set.mem_prod.mpr ⟨hs, hW (Set.mem_univ t)⟩)
    have hmem' : ‖H (s, t) - G s₀ t‖ < ‖G s₀ t₀ - q‖ := hmem
    rw [hGapp s t]
    exact lt_of_lt_of_le hmem' (isMinOn_iff.mp ht₀ t (Set.mem_univ t))
  have hAopen : IsOpen {s : I |
      windingNumber (G s) q = windingNumber (G 0) q} := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have hs₀' : windingNumber (G s₀) q = windingNumber (G 0) q := hs₀
    exact Filter.mem_of_superset (hloc s₀)
      fun s (hs : windingNumber (G s) q = windingNumber (G s₀) q) =>
        show windingNumber (G s) q = windingNumber (G 0) q from hs.trans hs₀'
  have hBopen : IsOpen {s : I |
      ¬ windingNumber (G s) q = windingNumber (G 0) q} := by
    rw [isOpen_iff_mem_nhds]
    intro s₀ hs₀
    have hs₀' : ¬ windingNumber (G s₀) q = windingNumber (G 0) q := hs₀
    exact Filter.mem_of_superset (hloc s₀)
      fun s (hs : windingNumber (G s) q = windingNumber (G s₀) q) =>
        show ¬ windingNumber (G s) q = windingNumber (G 0) q from
          fun h => hs₀' (hs ▸ h)
  have hclopen : IsClopen {s : I |
      windingNumber (G s) q = windingNumber (G 0) q} := by
    constructor
    · rw [← isOpen_compl_iff]
      exact hBopen
    · exact hAopen
  have huniv := hclopen.eq_univ ⟨0, rfl⟩
  have hconst : windingNumber (G 1) q = windingNumber (G 0) q := by
    have h1A : (1 : I) ∈ {s : I |
        windingNumber (G s) q = windingNumber (G 0) q} := by
      rw [huniv]
      exact Set.mem_univ 1
    exact h1A
  have hG0 : (⟨fun t => H (0, t), by fun_prop⟩ : C(I, ℂ)) = G 0 := by
    ext t
    exact (hGapp 0 t).symm
  have hG1 : (⟨fun t => H (1, t), by fun_prop⟩ : C(I, ℂ)) = G 1 := by
    ext t
    exact (hGapp 1 t).symm
  rw [hG0, hG1]
  exact hconst.symm

/-- Classification of loops in a punctured disc: every closed loop in
`B(w₀, ρ) ∖ {w₀}` is freely homotopic, within the punctured disc, to the
standard circle of any smaller radius traversed `windingNumber γ w₀` times.
The homotopy is the straight-line interpolation of logarithm lifts. -/
theorem exists_loopHomotopy_nfoldLoop {γ : C(I, ℂ)} {w₀ : ℂ} {ρ : ℝ}
    (hcl : γ 0 = γ 1) (hγ : ∀ t, γ t ∈ Metric.ball w₀ ρ \ {w₀})
    {r₀ : ℝ} (h₀ : 0 < r₀) (hρ : r₀ < ρ) :
    ∃ H : C(I × I, ℂ), (∀ s t, H (s, t) ∈ Metric.ball w₀ ρ \ {w₀}) ∧
      (∀ s, H (s, 0) = H (s, 1)) ∧ (∀ t, H (0, t) = γ t) ∧
      (∀ t, H (1, t) = nfoldLoop w₀ r₀ (windingNumber γ w₀) t) := by
  have hρpos : 0 < ρ := h₀.trans hρ
  have hne : ∀ t : I, γ t ≠ w₀ := by
    intro t h
    exact (hγ t).2 (Set.mem_singleton_iff.mpr h)
  have hnorm_lt : ∀ t : I, ‖γ t - w₀‖ < ρ := by
    intro t
    have h1 := (hγ t).1
    rwa [Metric.mem_ball, dist_eq_norm] at h1
  have hsub_ne : ∀ t : I, shiftedCurve γ w₀ t ≠ 0 :=
    fun t => sub_ne_zero.mpr (hne t)
  obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ w₀) hsub_ne
  have hL' : ∀ t : I, Complex.exp (L t) = γ t - w₀ := fun t => hL t
  set n := windingNumber γ w₀ with hn
  have hspec : L 1 - L 0 = 2 * Real.pi * Complex.I * n :=
    windingNumber_spec hcl hne hL
  obtain ⟨M, hMapp⟩ : ∃ M : C(I, ℂ), ∀ t : I,
      M t = (Real.log r₀ : ℂ) + 2 * Real.pi * Complex.I * (n * (t : ℝ)) :=
    ⟨⟨fun t => (Real.log r₀ : ℂ) + 2 * Real.pi * Complex.I * (n * (t : ℝ)),
      by fun_prop⟩, fun t => rfl⟩
  have hM' : ∀ t : I, Complex.exp (M t) = nfoldLoop w₀ r₀ n t - w₀ := by
    intro t
    have happ : nfoldLoop w₀ r₀ n t =
        w₀ + (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (n * (t : ℝ))) := rfl
    rw [hMapp t, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log h₀, happ]
    ring
  have hMincr : M 1 - M 0 = 2 * Real.pi * Complex.I * n := by
    rw [hMapp 1, hMapp 0]
    norm_num
  have hcont : Continuous fun p : I × I =>
      w₀ + Complex.exp ((1 - ((p.1 : ℝ) : ℂ)) * L p.2 + ((p.1 : ℝ) : ℂ) * M p.2) := by
    fun_prop
  refine ⟨⟨fun p =>
    w₀ + Complex.exp ((1 - ((p.1 : ℝ) : ℂ)) * L p.2 + ((p.1 : ℝ) : ℂ) * M p.2), hcont⟩,
    ?_, ?_, ?_, ?_⟩
  · intro s t
    have hLre : (L t).re < Real.log ρ := by
      rw [Real.lt_log_iff_exp_lt hρpos, ← Complex.norm_exp, hL' t]
      exact hnorm_lt t
    have hMre : (M t).re < Real.log ρ := by
      have h1 : (M t).re = Real.log r₀ := by
        rw [hMapp t]
        simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [h1]
      exact Real.log_lt_log h₀ hρ
    have hcast : (1 - ((s : ℝ) : ℂ)) = (((1 - (s : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    have hAre : ((1 - ((s : ℝ) : ℂ)) * L t + ((s : ℝ) : ℂ) * M t).re =
        (1 - (s : ℝ)) * (L t).re + (s : ℝ) * (M t).re := by
      rw [hcast, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hmax : max ((L t).re) ((M t).re) < Real.log ρ := max_lt hLre hMre
    have hp1 : (1 - (s : ℝ)) * (L t).re ≤ (1 - (s : ℝ)) * max ((L t).re) ((M t).re) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    have hp2 : (s : ℝ) * (M t).re ≤ (s : ℝ) * max ((L t).re) ((M t).re) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hs0
    have hsum : (1 - (s : ℝ)) * max ((L t).re) ((M t).re) +
        (s : ℝ) * max ((L t).re) ((M t).re) = max ((L t).re) ((M t).re) := by ring
    have hcomb : (1 - (s : ℝ)) * (L t).re + (s : ℝ) * (M t).re < Real.log ρ := by
      linarith
    constructor
    · rw [Metric.mem_ball, dist_eq_norm]
      change ‖w₀ + Complex.exp ((1 - ((s : ℝ) : ℂ)) * L t + ((s : ℝ) : ℂ) * M t)
        - w₀‖ < ρ
      rw [add_sub_cancel_left, Complex.norm_exp, hAre]
      calc Real.exp ((1 - (s : ℝ)) * (L t).re + (s : ℝ) * (M t).re)
          < Real.exp (Real.log ρ) := Real.exp_lt_exp.mpr hcomb
        _ = ρ := Real.exp_log hρpos
    · intro hmem
      rw [Set.mem_singleton_iff] at hmem
      have hmem' : w₀ + Complex.exp ((1 - ((s : ℝ) : ℂ)) * L t
          + ((s : ℝ) : ℂ) * M t) = w₀ := hmem
      have h0 : Complex.exp ((1 - ((s : ℝ) : ℂ)) * L t + ((s : ℝ) : ℂ) * M t) = 0 := by
        linear_combination hmem'
      exact Complex.exp_ne_zero _ h0
  · intro s
    change w₀ + Complex.exp ((1 - ((s : ℝ) : ℂ)) * L 0 + ((s : ℝ) : ℂ) * M 0) =
      w₀ + Complex.exp ((1 - ((s : ℝ) : ℂ)) * L 1 + ((s : ℝ) : ℂ) * M 1)
    congr 1
    have hA : (1 - ((s : ℝ) : ℂ)) * L 1 + ((s : ℝ) : ℂ) * M 1 =
        ((1 - ((s : ℝ) : ℂ)) * L 0 + ((s : ℝ) : ℂ) * M 0) +
          (n : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (1 - ((s : ℝ) : ℂ)) * hspec + ((s : ℝ) : ℂ) * hMincr
    rw [hA]
    conv_rhs => rw [Complex.exp_add]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro t
    change w₀ + Complex.exp ((1 - (((0 : I) : ℝ) : ℂ)) * L t
      + (((0 : I) : ℝ) : ℂ) * M t) = γ t
    have hA0 : (1 - (((0 : I) : ℝ) : ℂ)) * L t + (((0 : I) : ℝ) : ℂ) * M t = L t := by
      norm_num
    rw [hA0, hL' t]
    ring
  · intro t
    change w₀ + Complex.exp ((1 - (((1 : I) : ℝ) : ℂ)) * L t
      + (((1 : I) : ℝ) : ℂ) * M t) = nfoldLoop w₀ r₀ n t
    have hA1 : (1 - (((1 : I) : ℝ) : ℂ)) * L t + (((1 : I) : ℝ) : ℂ) * M t = M t := by
      norm_num
    rw [hA1, hM' t]
    ring

/-! ## The winding degree of a plane homeomorphism -/

/-- The image of a circle inside the source of a partial homeomorphism is a
continuous loop. -/
theorem continuous_windingDegreeAt_loop (e : OpenPartialHomeomorph ℂ ℂ)
    (z₀ : ℂ) (r : ℝ) (h : Metric.closedBall z₀ r ⊆ e.source) (hr : 0 ≤ r) :
    Continuous fun t : I => e (circleLoop z₀ r t) := by
  have hmem : ∀ t : I, circleLoop z₀ r t ∈ e.source := by
    intro t
    apply h
    have hsub : circleLoop z₀ r t - z₀ =
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z₀ r t = z₀ +
          (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [Metric.mem_closedBall, dist_eq_norm, hsub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_nonneg hr]
  exact e.continuousOn.comp_continuous (circleLoop z₀ r).continuous hmem

/-- The winding degree of `e` at `z₀` with radius `r`: the winding number of
the image of the circle of radius `r` about `e z₀`. -/
noncomputable def windingDegreeAt (e : OpenPartialHomeomorph ℂ ℂ) (z₀ : ℂ)
    (r : ℝ) (h : Metric.closedBall z₀ r ⊆ e.source) (hr : 0 < r) : ℤ :=
  windingNumber
    ⟨fun t => e (circleLoop z₀ r t), continuous_windingDegreeAt_loop e z₀ r h hr.le⟩
    (e z₀)

/-- Radius independence of the winding degree: interpolate the circles and
apply free-loop homotopy invariance. -/
theorem windingDegreeAt_eq_of_radius (e : OpenPartialHomeomorph ℂ ℂ) {z₀ : ℂ}
    {r₁ r₂ : ℝ} (h₁ : Metric.closedBall z₀ r₁ ⊆ e.source)
    (h₂ : Metric.closedBall z₀ r₂ ⊆ e.source) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    windingDegreeAt e z₀ r₁ h₁ hr₁ = windingDegreeAt e z₀ r₂ h₂ hr₂ := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  have hnorm : ∀ (c : ℝ) (t : I), ‖circleLoop z₀ c t - z₀‖ = |c| := by
    intro c t
    have hsub : circleLoop z₀ c t - z₀ =
        (c : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z₀ c t =
          z₀ + (c : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one]
  have hcirc_cl : ∀ c : ℝ, circleLoop z₀ c 0 = circleLoop z₀ c 1 := by
    intro c
    have h0 : circleLoop z₀ c 0 =
        z₀ + (c : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z₀ c 1 =
        z₀ + (c : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  have key : ∀ (a b : ℝ) (ha : Metric.closedBall z₀ a ⊆ e.source)
      (hb : Metric.closedBall z₀ b ⊆ e.source) (hra : 0 < a) (hrb : 0 < b),
      a ≤ b → windingDegreeAt e z₀ a ha hra = windingDegreeAt e z₀ b hb hrb := by
    intro a b ha hb hra hrb hab
    have hrs_pos : ∀ s : I, 0 < (1 - (s : ℝ)) * a + (s : ℝ) * b := by
      intro s
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      nlinarith
    have hrs_le : ∀ s : I, (1 - (s : ℝ)) * a + (s : ℝ) * b ≤ b := by
      intro s
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      nlinarith
    have hmem : ∀ s t : I,
        circleLoop z₀ ((1 - (s : ℝ)) * a + (s : ℝ) * b) t ∈ e.source := by
      intro s t
      apply hb
      rw [Metric.mem_closedBall, dist_eq_norm, hnorm _ t,
        abs_of_pos (hrs_pos s)]
      exact hrs_le s
    have hinner : Continuous fun p : I × I =>
        circleLoop z₀ ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b) p.2 := by
      change Continuous fun p : I × I =>
        z₀ + (((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℝ))
      fun_prop
    have hcont : Continuous fun p : I × I =>
        e (circleLoop z₀ ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b) p.2) :=
      e.continuousOn.comp_continuous hinner fun p => hmem p.1 p.2
    have hz₀ : z₀ ∈ e.source := hb (Metric.mem_closedBall_self hrb.le)
    have hne : ∀ s t : I,
        (⟨fun p : I × I =>
          e (circleLoop z₀ ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b) p.2), hcont⟩ :
            C(I × I, ℂ)) (s, t) ≠ e z₀ := by
      intro s t heq
      have heq' : e (circleLoop z₀ ((1 - (s : ℝ)) * a + (s : ℝ) * b) t) = e z₀ := heq
      have hcirc_ne : circleLoop z₀ ((1 - (s : ℝ)) * a + (s : ℝ) * b) t ≠ z₀ := by
        intro h0
        have h1 := hnorm ((1 - (s : ℝ)) * a + (s : ℝ) * b) t
        rw [h0, sub_self, norm_zero, abs_of_pos (hrs_pos s)] at h1
        exact absurd h1.symm (ne_of_gt (hrs_pos s))
      exact hcirc_ne (e.injOn (hmem s t) hz₀ heq')
    have hclose : ∀ s : I,
        (⟨fun p : I × I =>
          e (circleLoop z₀ ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b) p.2), hcont⟩ :
            C(I × I, ℂ)) (s, 0) =
        (⟨fun p : I × I =>
          e (circleLoop z₀ ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b) p.2), hcont⟩ :
            C(I × I, ℂ)) (s, 1) := by
      intro s
      change e (circleLoop z₀ ((1 - (s : ℝ)) * a + (s : ℝ) * b) 0) =
        e (circleLoop z₀ ((1 - (s : ℝ)) * a + (s : ℝ) * b) 1)
      rw [hcirc_cl]
    have hkey := windingNumber_eq_of_loopHomotopy (q := e z₀)
      ⟨fun p : I × I =>
        e (circleLoop z₀ ((1 - (p.1 : ℝ)) * a + (p.1 : ℝ) * b) p.2), hcont⟩
      hclose hne
    unfold windingDegreeAt
    refine Eq.trans (hwn_ext _ _ _ fun t => ?_)
      (Eq.trans hkey (hwn_ext _ _ _ fun t => ?_))
    · change e (circleLoop z₀ a t) =
        e (circleLoop z₀ ((1 - (((0 : I) : ℝ))) * a + ((0 : I) : ℝ) * b) t)
      norm_num
    · change e (circleLoop z₀ ((1 - (((1 : I) : ℝ))) * a + ((1 : I) : ℝ) * b) t) =
        e (circleLoop z₀ b t)
      norm_num
  rcases le_total r₁ r₂ with h | h
  · exact key r₁ r₂ h₁ h₂ hr₁ hr₂ h
  · exact (key r₂ r₁ h₂ h₁ hr₂ hr₁ h).symm

/-- `e` preserves orientation at `z₀`: some admissible radius has winding
degree `1`. -/
def IsOrientationPreservingAt (e : OpenPartialHomeomorph ℂ ℂ) (z₀ : ℂ) : Prop :=
  ∃ (r : ℝ) (hr : 0 < r) (h : Metric.closedBall z₀ r ⊆ e.source),
    windingDegreeAt e z₀ r h hr = 1

/-- Orientation-preservation at a point upgrades from one admissible radius
to all of them. -/
theorem isOrientationPreservingAt_iff_forall (e : OpenPartialHomeomorph ℂ ℂ)
    (z₀ : ℂ) :
    IsOrientationPreservingAt e z₀ ↔
      (∃ r : ℝ, 0 < r ∧ Metric.closedBall z₀ r ⊆ e.source) ∧
        ∀ (r : ℝ) (hr : 0 < r) (h : Metric.closedBall z₀ r ⊆ e.source),
          windingDegreeAt e z₀ r h hr = 1 := by
  constructor
  · rintro ⟨r, hr, h, hdeg⟩
    refine ⟨⟨r, hr, h⟩, fun r' hr' h' => ?_⟩
    rw [windingDegreeAt_eq_of_radius e h' h hr' hr]
    exact hdeg
  · rintro ⟨⟨r, hr, h⟩, hall⟩
    exact ⟨r, hr, h, hall r hr h⟩

/-- Locality of the winding degree: two partial homeomorphisms agreeing on
an open set have equal degrees at its points, for radii inside it. -/
theorem windingDegreeAt_congr {e e' : OpenPartialHomeomorph ℂ ℂ} {U : Set ℂ}
    (hs : Set.EqOn e e' U) (hU : IsOpen U) {z₀ : ℂ} (hz : z₀ ∈ U) {r : ℝ}
    (hr : 0 < r) (hrU : Metric.closedBall z₀ r ⊆ U)
    (h : Metric.closedBall z₀ r ⊆ e.source)
    (h' : Metric.closedBall z₀ r ⊆ e'.source) :
    windingDegreeAt e z₀ r h hr = windingDegreeAt e' z₀ r h' hr := by
  have _ := hU
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  have hnorm : ∀ t : I, ‖circleLoop z₀ r t - z₀‖ = |r| := by
    intro t
    have hsub : circleLoop z₀ r t - z₀ =
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z₀ r t =
          z₀ + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one]
  have hmemU : ∀ t : I, circleLoop z₀ r t ∈ U := by
    intro t
    apply hrU
    rw [Metric.mem_closedBall, dist_eq_norm, hnorm t, abs_of_pos hr]
  unfold windingDegreeAt
  have hpt : e z₀ = e' z₀ := hs hz
  rw [hpt]
  exact hwn_ext _ _ _ fun t => hs (hmemU t)

/-- Orientation-preservation at a point depends only on the germ of the map
near the point. -/
theorem isOrientationPreservingAt_congr {e e' : OpenPartialHomeomorph ℂ ℂ}
    {U : Set ℂ} (hs : Set.EqOn e e' U) (hU : IsOpen U) {z₀ : ℂ} (hz : z₀ ∈ U)
    (hUe : U ⊆ e.source) (hUe' : U ⊆ e'.source) :
    IsOrientationPreservingAt e z₀ ↔ IsOrientationPreservingAt e' z₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz
  have hr : 0 < ε / 2 := by positivity
  have hrU : Metric.closedBall z₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hsub : Metric.closedBall z₀ (ε / 2) ⊆ e.source := hrU.trans hUe
  have hsub' : Metric.closedBall z₀ (ε / 2) ⊆ e'.source := hrU.trans hUe'
  constructor
  · rintro ⟨r₁, hr₁, h₁, hdeg⟩
    refine ⟨ε / 2, hr, hsub', ?_⟩
    rw [← windingDegreeAt_congr hs hU hz hr hrU hsub hsub',
      windingDegreeAt_eq_of_radius e hsub h₁ hr hr₁]
    exact hdeg
  · rintro ⟨r₁, hr₁, h₁, hdeg⟩
    refine ⟨ε / 2, hr, hsub, ?_⟩
    rw [windingDegreeAt_congr hs hU hz hr hrU hsub hsub',
      windingDegreeAt_eq_of_radius e' hsub' h₁ hr hr₁]
    exact hdeg

/-- A partial homeomorphism agreeing with the identity near a point
preserves orientation there. -/
theorem isOrientationPreservingAt_id {e : OpenPartialHomeomorph ℂ ℂ}
    {U : Set ℂ} (hs : Set.EqOn e id U) (hU : IsOpen U) {z₀ : ℂ} (hz : z₀ ∈ U)
    (hUe : U ⊆ e.source) : IsOrientationPreservingAt e z₀ := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz
  have hr : 0 < ε / 2 := by positivity
  have hrU : Metric.closedBall z₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hsub : Metric.closedBall z₀ (ε / 2) ⊆ e.source := hrU.trans hUe
  have hnorm : ∀ t : I, ‖circleLoop z₀ (ε / 2) t - z₀‖ = |ε / 2| := by
    intro t
    have hsubeq : circleLoop z₀ (ε / 2) t - z₀ =
        ((ε / 2 : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z₀ (ε / 2) t =
          z₀ + ((ε / 2 : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [hsubeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one]
  have hmemU : ∀ t : I, circleLoop z₀ (ε / 2) t ∈ U := by
    intro t
    apply hrU
    rw [Metric.mem_closedBall, dist_eq_norm, hnorm t, abs_of_pos hr]
  refine ⟨ε / 2, hr, hsub, ?_⟩
  unfold windingDegreeAt
  have hpt : e z₀ = z₀ := hs hz
  rw [hpt]
  exact Eq.trans (hwn_ext _ _ _ fun t => hs (hmemU t))
    (windingNumber_circleLoop hr)

/-- A partial homeomorphism agreeing near `z₀` with an analytic function of
nonvanishing derivative has winding degree `1` there: for small radii the
image circle stays within `o(r)` of the affine loop
`t ↦ f z₀ + deriv f z₀ · (circleLoop z₀ r t - z₀)`, which winds once. -/
theorem isOrientationPreservingAt_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hd : deriv f z₀ ≠ 0)
    {e : OpenPartialHomeomorph ℂ ℂ} {U : Set ℂ} (he : Set.EqOn e f U)
    (hU : IsOpen U) (hz : z₀ ∈ U) (hUe : U ⊆ e.source) :
    IsOrientationPreservingAt e z₀ := by
  set d := deriv f z₀ with hd_def
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hder : HasDerivAt f d z₀ := hf.differentiableAt.hasDerivAt
  have hlo := hasDerivAt_iff_isLittleO.mp hder
  have hbound := (Asymptotics.isLittleO_iff.mp hlo) (half_pos hdpos)
  rw [Metric.eventually_nhds_iff] at hbound
  obtain ⟨ε, hε, hball⟩ := hbound
  obtain ⟨ε', hε', hball'⟩ := Metric.isOpen_iff.mp hU z₀ hz
  set r := min ε ε' / 2 with hr_def
  have hr : 0 < r := by
    rw [hr_def]
    have h1 := lt_min hε hε'
    positivity
  have hrε : r < ε := by
    have h1 := min_le_left ε ε'
    rw [hr_def]
    linarith
  have hrε' : r < ε' := by
    have h1 := min_le_right ε ε'
    rw [hr_def]
    linarith
  have hrU : Metric.closedBall z₀ r ⊆ U :=
    (Metric.closedBall_subset_ball hrε').trans hball'
  have hsub : Metric.closedBall z₀ r ⊆ e.source := hrU.trans hUe
  refine ⟨r, hr, hsub, ?_⟩
  have hcirc_sub : ∀ t : I, circleLoop z₀ r t - z₀ =
      (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro t
    have happ : circleLoop z₀ r t =
        z₀ + (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [happ]
    ring
  have hnorm : ∀ t : I, ‖circleLoop z₀ r t - z₀‖ = r := by
    intro t
    rw [hcirc_sub t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr]
  have hmemU : ∀ t : I, circleLoop z₀ r t ∈ U := by
    intro t
    apply hrU
    rw [Metric.mem_closedBall, dist_eq_norm, hnorm t]
  have hmem_ball : ∀ t : I, dist (circleLoop z₀ r t) z₀ < ε := by
    intro t
    rw [dist_eq_norm, hnorm t]
    exact hrε
  obtain ⟨A, hAapp⟩ : ∃ A : C(I, ℂ), ∀ t : I, A t =
      f z₀ + d * ((r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) :=
    ⟨⟨fun t =>
      f z₀ + d * ((r : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)),
      by fun_prop⟩, fun t => rfl⟩
  have hdr_ne : d * ((r : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hd (Complex.ofReal_ne_zero.mpr hr.ne')
  have hAcl : A 0 = A 1 := by
    rw [hAapp 0, hAapp 1]
    norm_num [Complex.exp_two_pi_mul_I]
  have hAne : ∀ t : I, A t ≠ f z₀ := by
    intro t h
    rw [hAapp t] at h
    have h0 : d * ((r : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) = 0 := by
      linear_combination h
    exact mul_ne_zero hdr_ne (Complex.exp_ne_zero _) h0
  have hAwn : windingNumber A (f z₀) = 1 := by
    obtain ⟨L, hLapp⟩ : ∃ L : C(I, ℂ), ∀ t : I, L t =
        Complex.log (d * ((r : ℝ) : ℂ)) + 2 * Real.pi * Complex.I * (t : ℝ) :=
      ⟨⟨fun t =>
        Complex.log (d * ((r : ℝ) : ℂ)) + 2 * Real.pi * Complex.I * (t : ℝ),
        by fun_prop⟩, fun t => rfl⟩
    have hlift : IsLogLiftOf L (shiftedCurve A (f z₀)) := by
      intro t
      have hsh : shiftedCurve A (f z₀) t = A t - f z₀ := rfl
      rw [hLapp t, hsh, hAapp t, Complex.exp_add, Complex.exp_log hdr_ne]
      ring
    have hspec := windingNumber_spec hAcl hAne hlift
    have hincr : L 1 - L 0 = 2 * Real.pi * Complex.I := by
      rw [hLapp 1, hLapp 0]
      norm_num
    rw [hincr] at hspec
    have h1 : (2 * (Real.pi : ℂ) * Complex.I) * 1 =
        2 * Real.pi * Complex.I * (windingNumber A (f z₀) : ℂ) := by
      rw [mul_one]
      exact hspec
    exact_mod_cast (mul_left_cancel₀ Complex.two_pi_I_ne_zero h1).symm
  unfold windingDegreeAt
  have hpt : e z₀ = f z₀ := he hz
  rw [hpt]
  refine Eq.trans (windingNumber_eq_of_dist_lt hAcl ?_ ?_).symm hAwn
  · change e (circleLoop z₀ r 0) = e (circleLoop z₀ r 1)
    have hc : circleLoop z₀ r 0 = circleLoop z₀ r 1 := by
      have h0 : circleLoop z₀ r 0 = z₀ +
          (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
      have h1 : circleLoop z₀ r 1 = z₀ +
          (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
      rw [h0, h1]
      norm_num [Complex.exp_two_pi_mul_I]
    rw [hc]
  · intro t
    change ‖e (circleLoop z₀ r t) - A t‖ < ‖A t - f z₀‖
    rw [he (hmemU t)]
    have hAt : A t = f z₀ + (circleLoop z₀ r t - z₀) * d := by
      rw [hAapp t, hcirc_sub t]
      ring
    have hb := hball (hmem_ball t)
    have hb' : ‖f (circleLoop z₀ r t) - f z₀ - (circleLoop z₀ r t - z₀) * d‖ ≤
        ‖d‖ / 2 * ‖circleLoop z₀ r t - z₀‖ := by
      have hsm : (circleLoop z₀ r t - z₀) • d = (circleLoop z₀ r t - z₀) * d :=
        smul_eq_mul _ _
      rw [← hsm]
      exact hb
    have hdiff : f (circleLoop z₀ r t) - A t =
        f (circleLoop z₀ r t) - f z₀ - (circleLoop z₀ r t - z₀) * d := by
      rw [hAt]
      ring
    have hAd : A t - f z₀ = (circleLoop z₀ r t - z₀) * d := by
      rw [hAt]
      ring
    rw [hdiff, hAd, norm_mul, hnorm t]
    calc ‖f (circleLoop z₀ r t) - f z₀ - (circleLoop z₀ r t - z₀) * d‖
        ≤ ‖d‖ / 2 * ‖circleLoop z₀ r t - z₀‖ := hb'
      _ = ‖d‖ / 2 * r := by rw [hnorm t]
      _ < r * ‖d‖ := by nlinarith

/-- The image of a loop in a punctured ball inside the source of a partial
homeomorphism is a continuous loop. -/
theorem continuous_comp_of_ball {h : OpenPartialHomeomorph ℂ ℂ} {γ : C(I, ℂ)}
    {w₀ : ℂ} {ρ : ℝ} (hball : Metric.closedBall w₀ ρ ⊆ h.source)
    (hγ : ∀ t, γ t ∈ Metric.ball w₀ ρ \ {w₀}) :
    Continuous fun t : I => h (γ t) := by
  have hmem : ∀ t : I, γ t ∈ h.source := fun t =>
    hball (Metric.ball_subset_closedBall (hγ t).1)
  exact h.continuousOn.comp_continuous γ.continuous hmem

/-- Composition formula: pushing a loop of a punctured ball through a
partial homeomorphism multiplies its winding number by the winding degree.
Homotope the loop to a standard `n`-fold circle, push the homotopy through,
and expand the `n`-fold image circle by concatenation additivity. -/
theorem windingNumber_comp_of_ball {h : OpenPartialHomeomorph ℂ ℂ}
    {γ : C(I, ℂ)} {w₀ : ℂ} {ρ : ℝ}
    (hball : Metric.closedBall w₀ ρ ⊆ h.source) (hρ : 0 < ρ)
    (hγ : ∀ t, γ t ∈ Metric.ball w₀ ρ \ {w₀}) (hcl : γ 0 = γ 1) :
    windingNumber ⟨fun t => h (γ t), continuous_comp_of_ball hball hγ⟩ (h w₀) =
      windingNumber γ w₀ * windingDegreeAt h w₀ ρ hball hρ := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  set r₀ := ρ / 2 with hr₀_def
  have hr₀ : 0 < r₀ := by rw [hr₀_def]; positivity
  have hr₀ρ : r₀ < ρ := by rw [hr₀_def]; exact half_lt_self hρ
  have hw₀ : w₀ ∈ h.source := hball (Metric.mem_closedBall_self hρ.le)
  -- `n`-fold loop plumbing at radius `r₀`
  have hnfold_sub : ∀ (k : ℤ) (t : I), nfoldLoop w₀ r₀ k t - w₀ =
      (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k * (t : ℝ))) := by
    intro k t
    have happ : nfoldLoop w₀ r₀ k t = w₀ +
        (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k * (t : ℝ))) := rfl
    rw [happ]
    ring
  have hnfold_norm : ∀ (k : ℤ) (t : I), ‖nfoldLoop w₀ r₀ k t - w₀‖ = r₀ := by
    intro k t
    rw [hnfold_sub k t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((k : ℂ) * ((t : ℝ) : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr₀]
  have hnfold_memball : ∀ (k : ℤ) (t : I),
      nfoldLoop w₀ r₀ k t ∈ Metric.ball w₀ ρ := by
    intro k t
    rw [Metric.mem_ball, dist_eq_norm, hnfold_norm k t]
    exact hr₀ρ
  have hnfold_mem : ∀ (k : ℤ) (t : I), nfoldLoop w₀ r₀ k t ∈ h.source := fun k t =>
    hball (Metric.ball_subset_closedBall (hnfold_memball k t))
  have hnfold_ne : ∀ (k : ℤ) (t : I), nfoldLoop w₀ r₀ k t ≠ w₀ := by
    intro k t heq
    have h1 := hnfold_norm k t
    rw [heq, sub_self, norm_zero] at h1
    exact hr₀.ne h1
  have hnfold_cont : ∀ k : ℤ, Continuous fun t : I => h (nfoldLoop w₀ r₀ k t) := by
    intro k
    exact h.continuousOn.comp_continuous (nfoldLoop w₀ r₀ k).continuous
      fun t => hnfold_mem k t
  have hHne : ∀ (k : ℤ) (t : I), h (nfoldLoop w₀ r₀ k t) ≠ h w₀ := by
    intro k t heq
    exact hnfold_ne k t (h.injOn (hnfold_mem k t) hw₀ heq)
  -- circle loop plumbing at radius `r₀`
  have hcirc_sub : ∀ t : I, circleLoop w₀ r₀ t - w₀ =
      (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro t
    have happ : circleLoop w₀ r₀ t = w₀ +
        (r₀ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [happ]
    ring
  have hcirc_norm : ∀ t : I, ‖circleLoop w₀ r₀ t - w₀‖ = r₀ := by
    intro t
    rw [hcirc_sub t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr₀]
  have hcirc_memball : ∀ t : I, circleLoop w₀ r₀ t ∈ Metric.ball w₀ ρ := by
    intro t
    rw [Metric.mem_ball, dist_eq_norm, hcirc_norm t]
    exact hr₀ρ
  have hcirc_mem : ∀ t : I, circleLoop w₀ r₀ t ∈ h.source := fun t =>
    hball (Metric.ball_subset_closedBall (hcirc_memball t))
  have hcirc_ne : ∀ t : I, circleLoop w₀ r₀ t ≠ w₀ := by
    intro t heq
    have h1 := hcirc_norm t
    rw [heq, sub_self, norm_zero] at h1
    exact hr₀.ne h1
  have hcirc_cont : Continuous fun t : I => h (circleLoop w₀ r₀ t) :=
    h.continuousOn.comp_continuous (circleLoop w₀ r₀).continuous fun t => hcirc_mem t
  have hHcirc_ne : ∀ t : I, h (circleLoop w₀ r₀ t) ≠ h w₀ := by
    intro t heq
    exact hcirc_ne t (h.injOn (hcirc_mem t) hw₀ heq)
  -- endpoint values
  have hnfold_zero : ∀ k : ℤ, nfoldLoop w₀ r₀ k 0 = w₀ + (r₀ : ℂ) := by
    intro k
    have h1 := hnfold_sub k 0
    have h2 : Complex.exp (2 * Real.pi * Complex.I *
        ((k : ℂ) * (((0 : I) : ℝ) : ℂ))) = 1 := by
      norm_num
    rw [h2, mul_one] at h1
    linear_combination h1
  have hnfold_one : ∀ k : ℤ, nfoldLoop w₀ r₀ k 1 = w₀ + (r₀ : ℂ) := by
    intro k
    have h1 := hnfold_sub k 1
    have harg : 2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) * (((1 : I) : ℝ) : ℂ)) =
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
      norm_num
      ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I, mul_one] at h1
    linear_combination h1
  have hcirc_zero : circleLoop w₀ r₀ 0 = w₀ + (r₀ : ℂ) := by
    have h1 := hcirc_sub 0
    have h2 : Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) = 1 := by
      norm_num
    rw [h2, mul_one] at h1
    linear_combination h1
  have hcirc_one : circleLoop w₀ r₀ 1 = w₀ + (r₀ : ℂ) := by
    have h1 := hcirc_sub 1
    have h2 : Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) = 1 := by
      norm_num [Complex.exp_two_pi_mul_I]
    rw [h2, mul_one] at h1
    linear_combination h1
  -- the degree at radius `r₀`, as a plain winding number
  set dd := windingNumber
    (⟨fun t => h (circleLoop w₀ r₀ t), hcirc_cont⟩ : C(I, ℂ)) (h w₀) with hdd_def
  -- winding of the image of the `m`-fold loop, natural exponents
  have key : ∀ m : ℕ, windingNumber
      (⟨fun t => h (nfoldLoop w₀ r₀ (m : ℤ) t), hnfold_cont (m : ℤ)⟩ : C(I, ℂ))
      (h w₀) = (m : ℤ) * dd := by
    intro m
    induction m with
    | zero =>
      have hne0 : h (w₀ + (r₀ : ℂ)) ≠ h w₀ := by
        have heq0 := hnfold_zero ((0 : ℕ) : ℤ)
        rw [← heq0]
        exact hHne ((0 : ℕ) : ℤ) 0
      have hconst : (⟨fun t => h (nfoldLoop w₀ r₀ ((0 : ℕ) : ℤ) t),
          hnfold_cont ((0 : ℕ) : ℤ)⟩ : C(I, ℂ)) =
          ContinuousMap.const I (h (w₀ + (r₀ : ℂ))) := by
        ext t
        change h (nfoldLoop w₀ r₀ ((0 : ℕ) : ℤ) t) = h (w₀ + (r₀ : ℂ))
        have hpt : nfoldLoop w₀ r₀ ((0 : ℕ) : ℤ) t = w₀ + (r₀ : ℂ) := by
          have h1 := hnfold_sub ((0 : ℕ) : ℤ) t
          have h2 : Complex.exp (2 * Real.pi * Complex.I *
              ((((0 : ℕ) : ℤ) : ℂ) * ((t : ℝ) : ℂ))) = 1 := by
            norm_num
          rw [h2, mul_one] at h1
          linear_combination h1
        rw [hpt]
      rw [hconst, windingNumber_const _ _ hne0]
      norm_num
    | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      set P : Path (w₀ + (r₀ : ℂ)) (w₀ + (r₀ : ℂ)) :=
        ⟨nfoldLoop w₀ r₀ (k : ℤ), hnfold_zero _, hnfold_one _⟩ with hP_def
      set Q : Path (w₀ + (r₀ : ℂ)) (w₀ + (r₀ : ℂ)) :=
        ⟨circleLoop w₀ r₀, hcirc_zero, hcirc_one⟩ with hQ_def
      have hPapp : ∀ t : I, P t = nfoldLoop w₀ r₀ (k : ℤ) t := fun t => rfl
      have hQapp : ∀ t : I, Q t = circleLoop w₀ r₀ t := fun t => rfl
      have hδmem : ∀ t, (P.trans Q).toContinuousMap t ∈ Metric.ball w₀ ρ \ {w₀} := by
        intro t
        change (P.trans Q) t ∈ _
        rw [Path.trans_apply]
        split_ifs with ht
        · rw [hPapp]
          exact ⟨hnfold_memball _ _, fun hc =>
            hnfold_ne _ _ (Set.mem_singleton_iff.mp hc)⟩
        · rw [hQapp]
          exact ⟨hcirc_memball _, fun hc =>
            hcirc_ne _ (Set.mem_singleton_iff.mp hc)⟩
      have hδcl : (P.trans Q).toContinuousMap 0 = (P.trans Q).toContinuousMap 1 := by
        change (P.trans Q) 0 = (P.trans Q) 1
        rw [Path.source, Path.target]
      have hδwn : windingNumber (P.trans Q).toContinuousMap w₀ = (k : ℤ) + 1 := by
        have havP : ∀ t : I, P t ≠ w₀ := by
          intro t
          rw [hPapp]
          exact hnfold_ne _ t
        have havQ : ∀ t : I, Q t ≠ w₀ := by
          intro t
          rw [hQapp]
          exact hcirc_ne t
        rw [windingNumber_trans P Q havP havQ]
        have h1 : windingNumber P.toContinuousMap w₀ = (k : ℤ) := by
          have hPcm : P.toContinuousMap = nfoldLoop w₀ r₀ (k : ℤ) := rfl
          rw [hPcm]
          exact windingNumber_nfoldLoop hr₀ (k : ℤ)
        have h2 : windingNumber Q.toContinuousMap w₀ = 1 := by
          have hQcm : Q.toContinuousMap = circleLoop w₀ r₀ := rfl
          rw [hQcm]
          exact windingNumber_circleLoop hr₀
        rw [h1, h2]
      obtain ⟨H₀, hH₀mem, hH₀cl, hH₀0, hH₀1⟩ :=
        exists_loopHomotopy_nfoldLoop hδcl hδmem hr₀ hr₀ρ
      rw [hδwn] at hH₀1
      have hH₀src : ∀ p : I × I, H₀ p ∈ h.source := fun p =>
        hball (Metric.ball_subset_closedBall (hH₀mem p.1 p.2).1)
      have hHcont : Continuous fun p : I × I => h (H₀ p) :=
        h.continuousOn.comp_continuous H₀.continuous hH₀src
      have hHclose : ∀ s : I,
          (⟨fun p : I × I => h (H₀ p), hHcont⟩ : C(I × I, ℂ)) (s, 0) =
          (⟨fun p : I × I => h (H₀ p), hHcont⟩ : C(I × I, ℂ)) (s, 1) := by
        intro s
        change h (H₀ (s, 0)) = h (H₀ (s, 1))
        rw [hH₀cl s]
      have hHavoid : ∀ s t : I,
          (⟨fun p : I × I => h (H₀ p), hHcont⟩ : C(I × I, ℂ)) (s, t) ≠ h w₀ := by
        intro s t heq
        have heq' : h (H₀ (s, t)) = h w₀ := heq
        have hne' : H₀ (s, t) ≠ w₀ := fun hc =>
          (hH₀mem s t).2 (Set.mem_singleton_iff.mpr hc)
        exact hne' (h.injOn (hH₀src (s, t)) hw₀ heq')
      have hkey := windingNumber_eq_of_loopHomotopy (q := h w₀)
        ⟨fun p : I × I => h (H₀ p), hHcont⟩ hHclose hHavoid
      have hc0 : Continuous fun t : I => h (H₀ (0, t)) :=
        hHcont.comp (continuous_const.prodMk continuous_id)
      have hc1 : Continuous fun t : I => h (H₀ (1, t)) :=
        hHcont.comp (continuous_const.prodMk continuous_id)
      have hPh0 : h (nfoldLoop w₀ r₀ (k : ℤ) 0) = h (w₀ + (r₀ : ℂ)) := by
        rw [hnfold_zero]
      have hPh1 : h (nfoldLoop w₀ r₀ (k : ℤ) 1) = h (w₀ + (r₀ : ℂ)) := by
        rw [hnfold_one]
      have hQh0 : h (circleLoop w₀ r₀ 0) = h (w₀ + (r₀ : ℂ)) := by rw [hcirc_zero]
      have hQh1 : h (circleLoop w₀ r₀ 1) = h (w₀ + (r₀ : ℂ)) := by rw [hcirc_one]
      set Ph : Path (h (w₀ + (r₀ : ℂ))) (h (w₀ + (r₀ : ℂ))) :=
        ⟨⟨fun t => h (nfoldLoop w₀ r₀ (k : ℤ) t), hnfold_cont (k : ℤ)⟩,
          hPh0, hPh1⟩ with hPh_def
      set Qh : Path (h (w₀ + (r₀ : ℂ))) (h (w₀ + (r₀ : ℂ))) :=
        ⟨⟨fun t => h (circleLoop w₀ r₀ t), hcirc_cont⟩, hQh0, hQh1⟩ with hQh_def
      have havPh : ∀ t : I, Ph t ≠ h w₀ := fun t => hHne (k : ℤ) t
      have havQh : ∀ t : I, Qh t ≠ h w₀ := fun t => hHcirc_ne t
      calc windingNumber (⟨fun t => h (nfoldLoop w₀ r₀ ((k : ℤ) + 1) t),
              hnfold_cont ((k : ℤ) + 1)⟩ : C(I, ℂ)) (h w₀)
          = windingNumber (⟨fun t => h (H₀ (1, t)), hc1⟩ : C(I, ℂ)) (h w₀) := by
            apply hwn_ext
            intro t
            change h (nfoldLoop w₀ r₀ ((k : ℤ) + 1) t) = h (H₀ (1, t))
            rw [hH₀1 t]
        _ = windingNumber (⟨fun t => h (H₀ (0, t)), hc0⟩ : C(I, ℂ)) (h w₀) :=
            hkey.symm
        _ = windingNumber (Ph.trans Qh).toContinuousMap (h w₀) := by
            apply hwn_ext
            intro t
            change h (H₀ (0, t)) = (Ph.trans Qh) t
            rw [hH₀0 t]
            change h ((P.trans Q) t) = (Ph.trans Qh) t
            rw [Path.trans_apply, Path.trans_apply]
            split_ifs with ht
            · rfl
            · rfl
        _ = windingNumber Ph.toContinuousMap (h w₀) +
              windingNumber Qh.toContinuousMap (h w₀) :=
            windingNumber_trans Ph Qh havPh havQh
        _ = (k : ℤ) * dd + dd := by
            have h1 : windingNumber Ph.toContinuousMap (h w₀) = (k : ℤ) * dd := ih
            have h2 : windingNumber Qh.toContinuousMap (h w₀) = dd := hdd_def.symm
            rw [h1, h2]
        _ = ((k : ℤ) + 1) * dd := by ring
  -- winding of the image of the `k`-fold loop, all integer exponents
  have keyZ : ∀ k : ℤ, windingNumber
      (⟨fun t => h (nfoldLoop w₀ r₀ k t), hnfold_cont k⟩ : C(I, ℂ)) (h w₀) =
      k * dd := by
    intro k
    rcases k with m | m
    · exact key m
    · have hidx : (Int.negSucc m) = -(((m + 1 : ℕ)) : ℤ) := by
        rw [Int.negSucc_eq]
        push_cast
        ring
      rw [hidx]
      have hPk0 : h (nfoldLoop w₀ r₀ (((m + 1 : ℕ)) : ℤ) 0) = h (w₀ + (r₀ : ℂ)) := by
        rw [hnfold_zero]
      have hPk1 : h (nfoldLoop w₀ r₀ (((m + 1 : ℕ)) : ℤ) 1) = h (w₀ + (r₀ : ℂ)) := by
        rw [hnfold_one]
      set Pk : Path (h (w₀ + (r₀ : ℂ))) (h (w₀ + (r₀ : ℂ))) :=
        ⟨⟨fun t => h (nfoldLoop w₀ r₀ (((m + 1 : ℕ)) : ℤ) t),
            hnfold_cont (((m + 1 : ℕ)) : ℤ)⟩, hPk0, hPk1⟩ with hPk_def
      have havPk : ∀ t : I, Pk t ≠ h w₀ := fun t => hHne (((m + 1 : ℕ)) : ℤ) t
      have hrev : ∀ t : I, nfoldLoop w₀ r₀ (-(((m + 1 : ℕ)) : ℤ)) t =
          nfoldLoop w₀ r₀ (((m + 1 : ℕ)) : ℤ) (σ t) := by
        intro t
        have h1 := hnfold_sub (-(((m + 1 : ℕ)) : ℤ)) t
        have h2 := hnfold_sub (((m + 1 : ℕ)) : ℤ) (σ t)
        have hσ : ((σ t : I) : ℝ) = 1 - (t : ℝ) := unitInterval.coe_symm_eq t
        have h3 : nfoldLoop w₀ r₀ (-(((m + 1 : ℕ)) : ℤ)) t - w₀ =
            nfoldLoop w₀ r₀ (((m + 1 : ℕ)) : ℤ) (σ t) - w₀ := by
          rw [h1, h2]
          congr 1
          rw [Complex.exp_eq_exp_iff_exists_int]
          refine ⟨-(((m + 1 : ℕ)) : ℤ), ?_⟩
          rw [hσ]
          push_cast
          ring
        linear_combination h3
      have hsymm := windingNumber_symm Pk havPk
      calc windingNumber (⟨fun t => h (nfoldLoop w₀ r₀ (-(((m + 1 : ℕ)) : ℤ)) t),
              hnfold_cont (-(((m + 1 : ℕ)) : ℤ))⟩ : C(I, ℂ)) (h w₀)
          = windingNumber Pk.symm.toContinuousMap (h w₀) := by
            apply hwn_ext
            intro t
            change h (nfoldLoop w₀ r₀ (-(((m + 1 : ℕ)) : ℤ)) t) = Pk (σ t)
            rw [hrev t]
            rfl
        _ = -windingNumber Pk.toContinuousMap (h w₀) := hsymm
        _ = -((((m + 1 : ℕ)) : ℤ) * dd) := by
            have h1 : windingNumber Pk.toContinuousMap (h w₀) =
                (((m + 1 : ℕ)) : ℤ) * dd := key (m + 1)
            rw [h1]
        _ = -(((m + 1 : ℕ)) : ℤ) * dd := by ring
  -- homotope `γ` to the standard loop and push the homotopy through `h`
  obtain ⟨H₁, hH₁mem, hH₁cl, hH₁0, hH₁1⟩ :=
    exists_loopHomotopy_nfoldLoop hcl hγ hr₀ hr₀ρ
  have hH₁src : ∀ p : I × I, H₁ p ∈ h.source := fun p =>
    hball (Metric.ball_subset_closedBall (hH₁mem p.1 p.2).1)
  have hH₁cont : Continuous fun p : I × I => h (H₁ p) :=
    h.continuousOn.comp_continuous H₁.continuous hH₁src
  have hH₁close : ∀ s : I,
      (⟨fun p : I × I => h (H₁ p), hH₁cont⟩ : C(I × I, ℂ)) (s, 0) =
      (⟨fun p : I × I => h (H₁ p), hH₁cont⟩ : C(I × I, ℂ)) (s, 1) := by
    intro s
    change h (H₁ (s, 0)) = h (H₁ (s, 1))
    rw [hH₁cl s]
  have hH₁avoid : ∀ s t : I,
      (⟨fun p : I × I => h (H₁ p), hH₁cont⟩ : C(I × I, ℂ)) (s, t) ≠ h w₀ := by
    intro s t heq
    have heq' : h (H₁ (s, t)) = h w₀ := heq
    have hne' : H₁ (s, t) ≠ w₀ := fun hc =>
      (hH₁mem s t).2 (Set.mem_singleton_iff.mpr hc)
    exact hne' (h.injOn (hH₁src (s, t)) hw₀ heq')
  have hkey₁ := windingNumber_eq_of_loopHomotopy (q := h w₀)
    ⟨fun p : I × I => h (H₁ p), hH₁cont⟩ hH₁close hH₁avoid
  have hc0 : Continuous fun t : I => h (H₁ (0, t)) :=
    hH₁cont.comp (continuous_const.prodMk continuous_id)
  have hc1 : Continuous fun t : I => h (H₁ (1, t)) :=
    hH₁cont.comp (continuous_const.prodMk continuous_id)
  have hball₀ : Metric.closedBall w₀ r₀ ⊆ h.source :=
    (Metric.closedBall_subset_ball hr₀ρ).trans
      (Metric.ball_subset_closedBall.trans hball)
  have hdeg : windingDegreeAt h w₀ ρ hball hρ = dd := by
    rw [← windingDegreeAt_eq_of_radius h hball₀ hball hr₀ hρ, hdd_def]
    unfold windingDegreeAt
    exact hwn_ext _ _ _ fun t => rfl
  calc windingNumber ⟨fun t => h (γ t), continuous_comp_of_ball hball hγ⟩ (h w₀)
      = windingNumber (⟨fun t => h (H₁ (0, t)), hc0⟩ : C(I, ℂ)) (h w₀) := by
        apply hwn_ext
        intro t
        change h (γ t) = h (H₁ (0, t))
        rw [hH₁0 t]
    _ = windingNumber (⟨fun t => h (H₁ (1, t)), hc1⟩ : C(I, ℂ)) (h w₀) := hkey₁
    _ = windingNumber (⟨fun t => h (nfoldLoop w₀ r₀ (windingNumber γ w₀) t),
          hnfold_cont (windingNumber γ w₀)⟩ : C(I, ℂ)) (h w₀) := by
        apply hwn_ext
        intro t
        change h (H₁ (1, t)) = h (nfoldLoop w₀ r₀ (windingNumber γ w₀) t)
        rw [hH₁1 t]
    _ = windingNumber γ w₀ * dd := keyZ (windingNumber γ w₀)
    _ = windingNumber γ w₀ * windingDegreeAt h w₀ ρ hball hρ := by rw [hdeg]

/-- Orientation-preservation composes. -/
theorem isOrientationPreservingAt_trans {e₁ e₂ : OpenPartialHomeomorph ℂ ℂ}
    {z₀ : ℂ} (h₁ : IsOrientationPreservingAt e₁ z₀)
    (h₂ : IsOrientationPreservingAt e₂ (e₁ z₀)) :
    IsOrientationPreservingAt (e₁.trans e₂) z₀ := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  obtain ⟨ρ, hρ, hball₂, hdeg₂⟩ := h₂
  obtain ⟨r₁, hr₁, hb₁, hd₁⟩ := h₁
  have hz₀src : z₀ ∈ e₁.source := hb₁ (Metric.mem_closedBall_self hr₁.le)
  have hVopen : IsOpen (e₁.source ∩ e₁ ⁻¹' Metric.ball (e₁ z₀) ρ) :=
    e₁.continuousOn.isOpen_inter_preimage e₁.open_source Metric.isOpen_ball
  have hz₀V : z₀ ∈ e₁.source ∩ e₁ ⁻¹' Metric.ball (e₁ z₀) ρ :=
    ⟨hz₀src, Metric.mem_ball_self hρ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen z₀ hz₀V
  set r := ε / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hrV : Metric.closedBall z₀ r ⊆ e₁.source ∩ e₁ ⁻¹' Metric.ball (e₁ z₀) ρ :=
    (Metric.closedBall_subset_ball (by rw [hr_def]; exact half_lt_self hε)).trans hball
  have hcirc_sub : ∀ t : I, circleLoop z₀ r t - z₀ =
      (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro t
    have happ : circleLoop z₀ r t = z₀ +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [happ]
    ring
  have hcirc_norm : ∀ t : I, ‖circleLoop z₀ r t - z₀‖ = r := by
    intro t
    rw [hcirc_sub t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr]
  have hcircV : ∀ t : I,
      circleLoop z₀ r t ∈ e₁.source ∩ e₁ ⁻¹' Metric.ball (e₁ z₀) ρ := by
    intro t
    apply hrV
    rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm t]
  have hcirc_ne : ∀ t : I, circleLoop z₀ r t ≠ z₀ := by
    intro t heq
    have h1 := hcirc_norm t
    rw [heq, sub_self, norm_zero] at h1
    exact hr.ne h1
  have hcirc_cl : circleLoop z₀ r 0 = circleLoop z₀ r 1 := by
    have h0 : circleLoop z₀ r 0 = z₀ +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z₀ r 1 = z₀ +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  have hsub : Metric.closedBall z₀ r ⊆ (e₁.trans e₂).source := by
    intro x hx
    rw [OpenPartialHomeomorph.trans_source]
    have hxV := hrV hx
    exact ⟨hxV.1, hball₂ (Metric.ball_subset_closedBall hxV.2)⟩
  refine ⟨r, hr, hsub, ?_⟩
  have hγcont : Continuous fun t : I => e₁ (circleLoop z₀ r t) :=
    e₁.continuousOn.comp_continuous (circleLoop z₀ r).continuous
      fun t => (hcircV t).1
  have hγmem : ∀ t, (⟨fun t => e₁ (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) t ∈
      Metric.ball (e₁ z₀) ρ \ {e₁ z₀} := by
    intro t
    constructor
    · exact (hcircV t).2
    · intro hc
      have hc' : e₁ (circleLoop z₀ r t) = e₁ z₀ := Set.mem_singleton_iff.mp hc
      exact hcirc_ne t (e₁.injOn (hcircV t).1 hz₀src hc')
  have hγcl : (⟨fun t => e₁ (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) 0 =
      (⟨fun t => e₁ (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) 1 := by
    change e₁ (circleLoop z₀ r 0) = e₁ (circleLoop z₀ r 1)
    rw [hcirc_cl]
  have hcomp := windingNumber_comp_of_ball (h := e₂) hball₂ hρ hγmem hγcl
  have hb₁' : Metric.closedBall z₀ r ⊆ e₁.source := fun x hx => (hrV hx).1
  have hall₁ := (isOrientationPreservingAt_iff_forall e₁ z₀).mp
    ⟨r₁, hr₁, hb₁, hd₁⟩
  have hfac1 : windingNumber
      (⟨fun t => e₁ (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) (e₁ z₀) = 1 := by
    have heq : windingNumber
        (⟨fun t => e₁ (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) (e₁ z₀) =
        windingDegreeAt e₁ z₀ r hb₁' hr := by
      unfold windingDegreeAt
      exact hwn_ext _ _ _ fun t => rfl
    rw [heq]
    exact hall₁.2 r hr hb₁'
  unfold windingDegreeAt
  refine Eq.trans (hwn_ext _ _ _ fun t => ?_) (Eq.trans hcomp ?_)
  · change (e₁.trans e₂) (circleLoop z₀ r t) = e₂ (e₁ (circleLoop z₀ r t))
    rw [OpenPartialHomeomorph.trans_apply]
  · rw [hfac1, hdeg₂, one_mul]

/-- Orientation-preservation passes to the inverse:
`deg e · deg e.symm = deg id = 1` in `ℤ`. -/
theorem isOrientationPreservingAt_symm {e : OpenPartialHomeomorph ℂ ℂ} {z₀ : ℂ}
    (h : IsOrientationPreservingAt e z₀) :
    IsOrientationPreservingAt e.symm (e z₀) := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  obtain ⟨r₁, hr₁, hb₁, hd₁⟩ := h
  have hz₀src : z₀ ∈ e.source := hb₁ (Metric.mem_closedBall_self hr₁.le)
  have hz₀tgt : e z₀ ∈ e.target := e.map_source hz₀src
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp e.open_target (e z₀) hz₀tgt
  set ρ := ε₂ / 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  have hbρ : Metric.closedBall (e z₀) ρ ⊆ e.symm.source := by
    rw [OpenPartialHomeomorph.symm_source]
    exact (Metric.closedBall_subset_ball
      (by rw [hρ_def]; exact half_lt_self hε₂)).trans hball₂
  have hVopen : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ) :=
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hz₀V : z₀ ∈ e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ :=
    ⟨hz₀src, Metric.mem_ball_self hρ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen z₀ hz₀V
  set r := ε / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hrV : Metric.closedBall z₀ r ⊆ e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ :=
    (Metric.closedBall_subset_ball (by rw [hr_def]; exact half_lt_self hε)).trans hball
  have hcirc_sub : ∀ t : I, circleLoop z₀ r t - z₀ =
      (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro t
    have happ : circleLoop z₀ r t = z₀ +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [happ]
    ring
  have hcirc_norm : ∀ t : I, ‖circleLoop z₀ r t - z₀‖ = r := by
    intro t
    rw [hcirc_sub t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr]
  have hcircV : ∀ t : I,
      circleLoop z₀ r t ∈ e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ := by
    intro t
    apply hrV
    rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm t]
  have hcirc_ne : ∀ t : I, circleLoop z₀ r t ≠ z₀ := by
    intro t heq
    have h1 := hcirc_norm t
    rw [heq, sub_self, norm_zero] at h1
    exact hr.ne h1
  have hcirc_cl : circleLoop z₀ r 0 = circleLoop z₀ r 1 := by
    have h0 : circleLoop z₀ r 0 = z₀ +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z₀ r 1 = z₀ +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  have hγcont : Continuous fun t : I => e (circleLoop z₀ r t) :=
    e.continuousOn.comp_continuous (circleLoop z₀ r).continuous
      fun t => (hcircV t).1
  have hγmem : ∀ t, (⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) t ∈
      Metric.ball (e z₀) ρ \ {e z₀} := by
    intro t
    constructor
    · exact (hcircV t).2
    · intro hc
      have hc' : e (circleLoop z₀ r t) = e z₀ := Set.mem_singleton_iff.mp hc
      exact hcirc_ne t (e.injOn (hcircV t).1 hz₀src hc')
  have hγcl : (⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) 0 =
      (⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) 1 := by
    change e (circleLoop z₀ r 0) = e (circleLoop z₀ r 1)
    rw [hcirc_cl]
  have hcomp := windingNumber_comp_of_ball (h := e.symm) hbρ hρ hγmem hγcl
  have hleft : windingNumber ⟨fun t =>
      e.symm ((⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) t),
      continuous_comp_of_ball hbρ hγmem⟩ (e.symm (e z₀)) = 1 := by
    have hz : e.symm (e z₀) = z₀ := e.left_inv hz₀src
    rw [hz]
    calc windingNumber ⟨fun t =>
          e.symm ((⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) t),
          continuous_comp_of_ball hbρ hγmem⟩ z₀
        = windingNumber (circleLoop z₀ r) z₀ := by
          apply hwn_ext
          intro t
          change e.symm (e (circleLoop z₀ r t)) = circleLoop z₀ r t
          exact e.left_inv (hcircV t).1
      _ = 1 := windingNumber_circleLoop hr
  have hb₁' : Metric.closedBall z₀ r ⊆ e.source := fun x hx => (hrV hx).1
  have hall₁ := (isOrientationPreservingAt_iff_forall e z₀).mp
    ⟨r₁, hr₁, hb₁, hd₁⟩
  have hfac : windingNumber
      (⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) (e z₀) = 1 := by
    have heq : windingNumber
        (⟨fun t => e (circleLoop z₀ r t), hγcont⟩ : C(I, ℂ)) (e z₀) =
        windingDegreeAt e z₀ r hb₁' hr := by
      unfold windingDegreeAt
      exact hwn_ext _ _ _ fun t => rfl
    rw [heq]
    exact hall₁.2 r hr hb₁'
  rw [hfac, one_mul] at hcomp
  refine ⟨ρ, hρ, hbρ, ?_⟩
  rw [← hcomp]
  exact hleft

/-- Local constancy in the base point: orientation-preservation at `z₀`
spreads to a neighborhood, by moving first the circle and then the base
point through sets avoiding it. -/
theorem isOrientationPreservingAt_eventually {e : OpenPartialHomeomorph ℂ ℂ}
    {z₀ : ℂ} (h : IsOrientationPreservingAt e z₀) :
    ∀ᶠ z in 𝓝 z₀, IsOrientationPreservingAt e z := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  obtain ⟨r₁, hr₁, hb₁, hd₁⟩ := h
  have hall := (isOrientationPreservingAt_iff_forall e z₀).mp
    ⟨r₁, hr₁, hb₁, hd₁⟩
  have hz₀src : z₀ ∈ e.source := hb₁ (Metric.mem_closedBall_self hr₁.le)
  set r := r₁ / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hrr₁ : r < r₁ := by rw [hr_def]; exact half_lt_self hr₁
  -- generic circle geometry, arbitrary center
  have hcirc_sub : ∀ (c : ℂ) (t : I), circleLoop c r t - c =
      (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro c t
    have happ : circleLoop c r t = c +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [happ]
    ring
  have hcirc_norm : ∀ (c : ℂ) (t : I), ‖circleLoop c r t - c‖ = r := by
    intro c t
    rw [hcirc_sub c t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr]
  have hcirc_ne : ∀ (c : ℂ) (t : I), circleLoop c r t ≠ c := by
    intro c t heq
    have h1 := hcirc_norm c t
    rw [heq, sub_self, norm_zero] at h1
    exact hr.ne h1
  have hcirc_cl : ∀ c : ℂ, circleLoop c r 0 = circleLoop c r 1 := by
    intro c
    have h0 : circleLoop c r 0 = c +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop c r 1 = c +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  have hcirc_dist : ∀ (c c' : ℂ) (t : I), circleLoop c r t - circleLoop c' r t =
      c - c' := by
    intro c c' t
    have h1 : circleLoop c r t = c +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    have h2 : circleLoop c' r t = c' +
        (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [h1, h2]
    ring
  -- circle about `z₀` lies deep inside the closed ball of radius `r₁`
  have hcirc₀K : ∀ t : I, circleLoop z₀ r t ∈ Metric.closedBall z₀ r₁ := by
    intro t
    rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm z₀ t]
    exact hrr₁.le
  have hcirc₀src : ∀ t : I, circleLoop z₀ r t ∈ e.source := fun t =>
    hb₁ (hcirc₀K t)
  have hA₀cont : Continuous fun t : I => e (circleLoop z₀ r t) :=
    e.continuousOn.comp_continuous (circleLoop z₀ r).continuous hcirc₀src
  have hA₀ne : ∀ t : I, e (circleLoop z₀ r t) ≠ e z₀ := by
    intro t heq
    exact hcirc_ne z₀ t (e.injOn (hcirc₀src t) hz₀src heq)
  -- minimum distance from the image circle to `e z₀`
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (Continuous.continuousOn ((hA₀cont.sub continuous_const).norm) :
      ContinuousOn (fun t : I => ‖e (circleLoop z₀ r t) - e z₀‖) Set.univ)
  set m := ‖e (circleLoop z₀ r t₀) - e z₀‖ with hm_def
  have hm : 0 < m := norm_pos_iff.mpr (sub_ne_zero.mpr (hA₀ne t₀))
  have hmin : ∀ t : I, m ≤ ‖e (circleLoop z₀ r t) - e z₀‖ := fun t =>
    isMinOn_iff.mp ht₀ t (Set.mem_univ t)
  -- uniform continuity on the compact ball
  have huc : UniformContinuousOn e (Metric.closedBall z₀ r₁) :=
    (isCompact_closedBall z₀ r₁).uniformContinuousOn_of_continuous
      (e.continuousOn.mono hb₁)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀, hucball⟩ := huc (m / 2) (by positivity)
  have hδpos : 0 < min δ₀ r := lt_min hδ₀ hr
  filter_upwards [Metric.ball_mem_nhds z₀ hδpos] with z hz
  have hzz₀ : dist z z₀ < min δ₀ r := Metric.mem_ball.mp hz
  have hzK : z ∈ Metric.closedBall z₀ r₁ := by
    rw [Metric.mem_closedBall]
    have h1 : dist z z₀ < r := lt_of_lt_of_le hzz₀ (min_le_right _ _)
    linarith [hrr₁]
  have hz₀K : z₀ ∈ Metric.closedBall z₀ r₁ := Metric.mem_closedBall_self hr₁.le
  have hsubz : Metric.closedBall z r ⊆ Metric.closedBall z₀ r₁ := by
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    have h1 := dist_triangle x z z₀
    have h2 : dist z z₀ < r := lt_of_lt_of_le hzz₀ (min_le_right _ _)
    have h3 : r + r = r₁ := by rw [hr_def]; ring
    linarith
  have hsubz_src : Metric.closedBall z r ⊆ e.source := hsubz.trans hb₁
  refine ⟨r, hr, hsubz_src, ?_⟩
  have hcirczK : ∀ t : I, circleLoop z r t ∈ Metric.closedBall z₀ r₁ := by
    intro t
    apply hsubz
    rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm z t]
  have hcircz_src : ∀ t : I, circleLoop z r t ∈ e.source := fun t =>
    hb₁ (hcirczK t)
  have hAzcont : Continuous fun t : I => e (circleLoop z r t) :=
    e.continuousOn.comp_continuous (circleLoop z r).continuous hcircz_src
  have hA₀cl : (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) 0 =
      (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) 1 := by
    change e (circleLoop z₀ r 0) = e (circleLoop z₀ r 1)
    rw [hcirc_cl z₀]
  have hAzcl : (⟨fun t => e (circleLoop z r t), hAzcont⟩ : C(I, ℂ)) 0 =
      (⟨fun t => e (circleLoop z r t), hAzcont⟩ : C(I, ℂ)) 1 := by
    change e (circleLoop z r 0) = e (circleLoop z r 1)
    rw [hcirc_cl z]
  -- the base point moves within a small ball avoiding the image circle
  have hez : dist (e z) (e z₀) < m / 2 :=
    hucball z hzK z₀ hz₀K (lt_of_lt_of_le hzz₀ (min_le_left _ _))
  have hbase : windingNumber
      (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) (e z₀) =
      windingNumber
      (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) (e z) := by
    apply windingNumber_eq_of_preconnected hA₀cl
      (convex_ball (e z₀) (m / 2)).isPreconnected
    · intro t hmem
      rw [Metric.mem_ball] at hmem
      have hmem' : dist (e (circleLoop z₀ r t)) (e z₀) < m / 2 := hmem
      rw [dist_eq_norm] at hmem'
      have h2 := hmin t
      linarith
    · exact Metric.mem_ball_self (by positivity)
    · rw [Metric.mem_ball]
      exact hez
  -- the circle moves by less than its distance to the new base point
  have hcurve : windingNumber
      (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) (e z) =
      windingNumber
      (⟨fun t => e (circleLoop z r t), hAzcont⟩ : C(I, ℂ)) (e z) := by
    apply windingNumber_eq_of_dist_lt hA₀cl hAzcl
    intro t
    have hLHS : ‖e (circleLoop z r t) - e (circleLoop z₀ r t)‖ < m / 2 := by
      have hd : dist (circleLoop z r t) (circleLoop z₀ r t) < δ₀ := by
        rw [dist_eq_norm, hcirc_dist z z₀ t, ← dist_eq_norm]
        exact lt_of_lt_of_le hzz₀ (min_le_left _ _)
      have := hucball (circleLoop z r t) (hcirczK t)
        (circleLoop z₀ r t) (hcirc₀K t) hd
      rwa [dist_eq_norm] at this
    have hRHS : m / 2 < ‖e (circleLoop z₀ r t) - e z‖ := by
      have h1 := hmin t
      have h2 : ‖e z - e z₀‖ < m / 2 := by
        rw [← dist_eq_norm]
        exact hez
      have h3 : ‖e (circleLoop z₀ r t) - e z₀‖ ≤
          ‖e (circleLoop z₀ r t) - e z‖ + ‖e z - e z₀‖ := by
        have heq : e (circleLoop z₀ r t) - e z₀ =
            (e (circleLoop z₀ r t) - e z) + (e z - e z₀) := by ring
        rw [heq]
        exact norm_add_le _ _
      linarith
    change ‖e (circleLoop z r t) - e (circleLoop z₀ r t)‖ <
      ‖e (circleLoop z₀ r t) - e z‖
    linarith
  -- conclude: the degree at `z` is the degree at `z₀`
  have hb₀' : Metric.closedBall z₀ r ⊆ e.source := fun x hx =>
    hb₁ ((Metric.closedBall_subset_closedBall hrr₁.le) hx)
  have hdeg₀ : windingNumber
      (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) (e z₀) = 1 := by
    have heq : windingNumber
        (⟨fun t => e (circleLoop z₀ r t), hA₀cont⟩ : C(I, ℂ)) (e z₀) =
        windingDegreeAt e z₀ r hb₀' hr := by
      unfold windingDegreeAt
      exact hwn_ext _ _ _ fun t => rfl
    rw [heq]
    exact hall.2 r hr hb₀'
  unfold windingDegreeAt
  exact Eq.trans (hwn_ext _ _ _ fun t => rfl)
    (Eq.trans hcurve.symm (Eq.trans hbase.symm hdeg₀))

/-- Degree dichotomy: the winding degree of a plane homeomorphism is `±1`,
since `deg e · deg e.symm = 1` in `ℤ`. -/
theorem windingDegreeAt_eq_one_or_neg_one (e : OpenPartialHomeomorph ℂ ℂ)
    {z₀ : ℂ} {r : ℝ} (h : Metric.closedBall z₀ r ⊆ e.source) (hr : 0 < r) :
    windingDegreeAt e z₀ r h hr = 1 ∨ windingDegreeAt e z₀ r h hr = -1 := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  have hz₀src : z₀ ∈ e.source := h (Metric.mem_closedBall_self hr.le)
  have hz₀tgt : e z₀ ∈ e.target := e.map_source hz₀src
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp e.open_target (e z₀) hz₀tgt
  set ρ := ε₂ / 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  have hbρ : Metric.closedBall (e z₀) ρ ⊆ e.symm.source := by
    rw [OpenPartialHomeomorph.symm_source]
    exact (Metric.closedBall_subset_ball
      (by rw [hρ_def]; exact half_lt_self hε₂)).trans hball₂
  have hVopen : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ) :=
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hz₀V : z₀ ∈ e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ :=
    ⟨hz₀src, Metric.mem_ball_self hρ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen z₀ hz₀V
  set r' := ε / 2 with hr'_def
  have hr' : 0 < r' := by rw [hr'_def]; positivity
  have hrV : Metric.closedBall z₀ r' ⊆ e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ :=
    (Metric.closedBall_subset_ball (by rw [hr'_def]; exact half_lt_self hε)).trans
      hball
  have hcirc_sub : ∀ t : I, circleLoop z₀ r' t - z₀ =
      (r' : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
    intro t
    have happ : circleLoop z₀ r' t = z₀ +
        (r' : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
    rw [happ]
    ring
  have hcirc_norm : ∀ t : I, ‖circleLoop z₀ r' t - z₀‖ = r' := by
    intro t
    rw [hcirc_sub t, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hr']
  have hcircV : ∀ t : I,
      circleLoop z₀ r' t ∈ e.source ∩ e ⁻¹' Metric.ball (e z₀) ρ := by
    intro t
    apply hrV
    rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm t]
  have hcirc_ne : ∀ t : I, circleLoop z₀ r' t ≠ z₀ := by
    intro t heq
    have h1 := hcirc_norm t
    rw [heq, sub_self, norm_zero] at h1
    exact hr'.ne h1
  have hcirc_cl : circleLoop z₀ r' 0 = circleLoop z₀ r' 1 := by
    have h0 : circleLoop z₀ r' 0 = z₀ +
        (r' : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z₀ r' 1 = z₀ +
        (r' : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  have hγcont : Continuous fun t : I => e (circleLoop z₀ r' t) :=
    e.continuousOn.comp_continuous (circleLoop z₀ r').continuous
      fun t => (hcircV t).1
  have hγmem : ∀ t, (⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) t ∈
      Metric.ball (e z₀) ρ \ {e z₀} := by
    intro t
    constructor
    · exact (hcircV t).2
    · intro hc
      have hc' : e (circleLoop z₀ r' t) = e z₀ := Set.mem_singleton_iff.mp hc
      exact hcirc_ne t (e.injOn (hcircV t).1 hz₀src hc')
  have hγcl : (⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) 0 =
      (⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) 1 := by
    change e (circleLoop z₀ r' 0) = e (circleLoop z₀ r' 1)
    rw [hcirc_cl]
  have hcomp := windingNumber_comp_of_ball (h := e.symm) hbρ hρ hγmem hγcl
  have hleft : windingNumber ⟨fun t =>
      e.symm ((⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) t),
      continuous_comp_of_ball hbρ hγmem⟩ (e.symm (e z₀)) = 1 := by
    have hz : e.symm (e z₀) = z₀ := e.left_inv hz₀src
    rw [hz]
    calc windingNumber ⟨fun t =>
          e.symm ((⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) t),
          continuous_comp_of_ball hbρ hγmem⟩ z₀
        = windingNumber (circleLoop z₀ r') z₀ := by
          apply hwn_ext
          intro t
          change e.symm (e (circleLoop z₀ r' t)) = circleLoop z₀ r' t
          exact e.left_inv (hcircV t).1
      _ = 1 := windingNumber_circleLoop hr'
  have hb' : Metric.closedBall z₀ r' ⊆ e.source := fun x hx => (hrV hx).1
  have hfac : windingNumber
      (⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) (e z₀) =
      windingDegreeAt e z₀ r h hr := by
    have heq : windingNumber
        (⟨fun t => e (circleLoop z₀ r' t), hγcont⟩ : C(I, ℂ)) (e z₀) =
        windingDegreeAt e z₀ r' hb' hr' := by
      unfold windingDegreeAt
      exact hwn_ext _ _ _ fun t => rfl
    rw [heq]
    exact windingDegreeAt_eq_of_radius e hb' h hr' hr
  rw [hfac, hleft] at hcomp
  have hunit : IsUnit (windingDegreeAt e z₀ r h hr) :=
    IsUnit.of_mul_eq_one _ hcomp.symm
  exact Int.isUnit_iff.mp hunit

/-! ## Orientation on charted surfaces -/

/-- The chart representative of a surface self-homeomorphism at a point:
read `f` in the preferred charts at `p` and `f p`. -/
noncomputable def homeoChartRep {S : Type*} [TopologicalSpace S]
    [ChartedSpace ℂ S] (f : S ≃ₜ S) (p : S) : OpenPartialHomeomorph ℂ ℂ :=
  (chartAt ℂ p).symm.trans
    ((Homeomorph.toOpenPartialHomeomorph f).trans (chartAt ℂ (f p)))

/-- A surface self-homeomorphism preserves orientation when each chart
representative does, at every point. -/
def _root_.Homeomorph.IsOrientationPreserving {S : Type*} [TopologicalSpace S]
    [ChartedSpace ℂ S] (f : S ≃ₜ S) : Prop :=
  ∀ p : S, IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p)

/-- A charted space has an oriented atlas when every atlas transition
preserves orientation at every point of its source. -/
def HasOrientedAtlas (S : Type*) [TopologicalSpace S] [ChartedSpace ℂ S] : Prop :=
  ∀ e ∈ atlas ℂ S, ∀ e' ∈ atlas ℂ S, ∀ z ∈ (e.symm.trans e').source,
    IsOrientationPreservingAt (e.symm.trans e') z

/-- The identity preserves orientation. -/
theorem _root_.Homeomorph.IsOrientationPreserving.refl (S : Type*) [TopologicalSpace S]
    [ChartedSpace ℂ S] : (Homeomorph.refl S).IsOrientationPreserving := by
  intro p
  have hsrcE : ∀ (F : S ≃ₜ S) (a : S) (w : ℂ),
      w ∈ (homeoChartRep F a).source ↔
        w ∈ (chartAt ℂ a).target ∧ F ((chartAt ℂ a).symm w) ∈ (chartAt ℂ (F a)).source := by
    intro F a w
    unfold homeoChartRep
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hEq : Set.EqOn (homeoChartRep (Homeomorph.refl S) p) id
      (homeoChartRep (Homeomorph.refl S) p).source := by
    intro w hw
    have h1 := ((hsrcE (Homeomorph.refl S) p w).mp hw).1
    exact (chartAt ℂ p).right_inv h1
  have hmem : chartAt ℂ p p ∈ (homeoChartRep (Homeomorph.refl S) p).source := by
    rw [hsrcE]
    refine ⟨(chartAt ℂ p).map_source (mem_chart_source ℂ p), ?_⟩
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact mem_chart_source ℂ p
  exact isOrientationPreservingAt_id hEq
    (homeoChartRep (Homeomorph.refl S) p).open_source hmem subset_rfl

/-- Orientation-preservation is closed under composition: the chart
representative of `f.trans g` at `p` agrees near the point with the
composite of the representatives of `f` at `p` and `g` at `f p`, which share
the middle chart. -/
theorem _root_.Homeomorph.IsOrientationPreserving.trans {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] {f g : S ≃ₜ S}
    (hf : f.IsOrientationPreserving) (hg : g.IsOrientationPreserving) :
    (f.trans g).IsOrientationPreserving := by
  intro p
  have hsrcE : ∀ (F : S ≃ₜ S) (a : S) (w : ℂ),
      w ∈ (homeoChartRep F a).source ↔
        w ∈ (chartAt ℂ a).target ∧ F ((chartAt ℂ a).symm w) ∈ (chartAt ℂ (F a)).source := by
    intro F a w
    unfold homeoChartRep
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (F : S ≃ₜ S) (a : S),
      chartAt ℂ a a ∈ (homeoChartRep F a).source := by
    intro F a
    rw [hsrcE]
    refine ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), ?_⟩
    rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
    exact mem_chart_source ℂ (F a)
  have h1 := hf p
  have h2 := hg (f p)
  have hpt : homeoChartRep f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
    change chartAt ℂ (f p) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) = chartAt ℂ (f p) (f p)
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  rw [← hpt] at h2
  have h12 := isOrientationPreservingAt_trans h1 h2
  have hUopen : IsOpen (((homeoChartRep f p).trans (homeoChartRep g (f p))).source ∩
      (homeoChartRep (f.trans g) p).source) :=
    ((homeoChartRep f p).trans (homeoChartRep g (f p))).open_source.inter
      (homeoChartRep (f.trans g) p).open_source
  have hEq : Set.EqOn ((homeoChartRep f p).trans (homeoChartRep g (f p)))
      (homeoChartRep (f.trans g) p)
      (((homeoChartRep f p).trans (homeoChartRep g (f p))).source ∩
        (homeoChartRep (f.trans g) p).source) := by
    intro w hw
    obtain ⟨hwC, -⟩ := hw
    rw [OpenPartialHomeomorph.trans_source] at hwC
    obtain ⟨hw1, -⟩ := hwC
    have hx : f ((chartAt ℂ p).symm w) ∈ (chartAt ℂ (f p)).source :=
      ((hsrcE f p w).mp hw1).2
    change chartAt ℂ (g (f p)) (g ((chartAt ℂ (f p)).symm
        (chartAt ℂ (f p) (f ((chartAt ℂ p).symm w))))) =
      chartAt ℂ ((f.trans g) p) ((f.trans g) ((chartAt ℂ p).symm w))
    rw [(chartAt ℂ (f p)).left_inv hx]
    rfl
  have hz : chartAt ℂ p p ∈
      (((homeoChartRep f p).trans (homeoChartRep g (f p))).source ∩
        (homeoChartRep (f.trans g) p).source) := by
    constructor
    · rw [OpenPartialHomeomorph.trans_source]
      refine ⟨hbase f p, ?_⟩
      rw [Set.mem_preimage, hpt]
      exact hbase g (f p)
    · exact hbase (f.trans g) p
  exact (isOrientationPreservingAt_congr hEq hUopen hz
    Set.inter_subset_left Set.inter_subset_right).mp h12

/-- On a surface with an oriented atlas, orientation-preservation is closed
under inversion. -/
theorem _root_.Homeomorph.IsOrientationPreserving.symm {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] (hS : HasOrientedAtlas S)
    {f : S ≃ₜ S} (hf : f.IsOrientationPreserving) :
    f.symm.IsOrientationPreserving := by
  have _ := hS
  intro q
  have hsrcE : ∀ (F : S ≃ₜ S) (a : S) (w : ℂ),
      w ∈ (homeoChartRep F a).source ↔
        w ∈ (chartAt ℂ a).target ∧ F ((chartAt ℂ a).symm w) ∈ (chartAt ℂ (F a)).source := by
    intro F a w
    unfold homeoChartRep
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (F : S ≃ₜ S) (a : S),
      chartAt ℂ a a ∈ (homeoChartRep F a).source := by
    intro F a
    rw [hsrcE]
    refine ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), ?_⟩
    rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
    exact mem_chart_source ℂ (F a)
  have h1 := hf (f.symm q)
  have h2 := isOrientationPreservingAt_symm h1
  have hfp : f (f.symm q) = q := f.apply_symm_apply q
  have hpt : homeoChartRep f (f.symm q) (chartAt ℂ (f.symm q) (f.symm q)) =
      chartAt ℂ q q := by
    change chartAt ℂ (f (f.symm q))
      (f ((chartAt ℂ (f.symm q)).symm (chartAt ℂ (f.symm q) (f.symm q)))) = chartAt ℂ q q
    rw [(chartAt ℂ (f.symm q)).left_inv (mem_chart_source ℂ (f.symm q)), hfp]
  rw [hpt] at h2
  have hchart : chartAt ℂ (f (f.symm q)) = chartAt ℂ q := by rw [hfp]
  have hUopen : IsOpen ((homeoChartRep f (f.symm q)).symm.source ∩
      (homeoChartRep f.symm q).source) :=
    (homeoChartRep f (f.symm q)).symm.open_source.inter
      (homeoChartRep f.symm q).open_source
  have hEq : Set.EqOn (homeoChartRep f (f.symm q)).symm (homeoChartRep f.symm q)
      ((homeoChartRep f (f.symm q)).symm.source ∩ (homeoChartRep f.symm q).source) := by
    intro w _
    change chartAt ℂ (f.symm q) (f.symm ((chartAt ℂ (f (f.symm q))).symm w)) =
      chartAt ℂ (f.symm q) (f.symm ((chartAt ℂ q).symm w))
    rw [hchart]
  have hz : chartAt ℂ q q ∈
      ((homeoChartRep f (f.symm q)).symm.source ∩ (homeoChartRep f.symm q).source) := by
    constructor
    · rw [OpenPartialHomeomorph.symm_source, ← hpt]
      exact (homeoChartRep f (f.symm q)).map_source (hbase f (f.symm q))
    · exact hbase f.symm q
  exact (isOrientationPreservingAt_congr hEq hUopen hz
    Set.inter_subset_left Set.inter_subset_right).mp h2

/-- The genus surface has an oriented atlas: its transitions are analytic
with nonvanishing derivative, hence of winding degree `1`. -/
theorem hasOrientedAtlas_genusSurface (g : ℕ) [NeZero g] :
    HasOrientedAtlas (GenusSurface g) := by
  intro e he e' he' z hz
  obtain ⟨hA, hd⟩ := transition_analyticAt g e he e' he' z hz
  exact isOrientationPreservingAt_of_analyticAt hA hd (fun w _ => rfl)
    (e.symm.trans e').open_source hz subset_rfl

/-- On a connected surface with oriented atlas, orientation-preservation at
one point propagates to all points: the locus of orientation-preservation
and its complement are both open. -/
theorem isOrientationPreserving_of_isOrientationPreservingAt_point {S : Type*}
    [TopologicalSpace S] [ChartedSpace ℂ S] [ConnectedSpace S]
    (h : HasOrientedAtlas S) (f : S ≃ₜ S) (p₀ : S)
    (hp : IsOrientationPreservingAt (homeoChartRep f p₀) (chartAt ℂ p₀ p₀)) :
    f.IsOrientationPreserving := by
  have hwn_ext : ∀ (A B : C(I, ℂ)) (q : ℂ), (∀ t, A t = B t) →
      windingNumber A q = windingNumber B q := by
    intro A B q hAB
    rw [ContinuousMap.ext hAB]
  -- source membership characterizations
  have hsrcT : ∀ (a b : OpenPartialHomeomorph S ℂ) (w : ℂ),
      w ∈ (a.symm.trans b).source ↔ w ∈ a.target ∧ a.symm w ∈ b.source := by
    intro a b w
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact Iff.rfl
  have hsrcE : ∀ (c d : OpenPartialHomeomorph S ℂ) (w : ℂ),
      w ∈ (c.symm.trans (f.toOpenPartialHomeomorph.trans d)).source ↔
        w ∈ c.target ∧ f (c.symm w) ∈ d.source := by
    intro c d w
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    simp only [Set.univ_inter, Set.mem_inter_iff, Set.mem_preimage]
    exact Iff.rfl
  have hbase : ∀ (a : S), chartAt ℂ a a ∈ (homeoChartRep f a).source := by
    intro a
    exact (hsrcE (chartAt ℂ a) (chartAt ℂ (f a)) (chartAt ℂ a a)).mpr
      ⟨(chartAt ℂ a).map_source (mem_chart_source ℂ a), by
        rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]
        exact mem_chart_source ℂ (f a)⟩
  -- one-sided chart transport through oriented transitions
  have hmove : ∀ c c' d d' : OpenPartialHomeomorph S ℂ, c ∈ atlas ℂ S → c' ∈ atlas ℂ S →
      d ∈ atlas ℂ S → d' ∈ atlas ℂ S → ∀ q : S, q ∈ c.source → q ∈ c'.source →
      f q ∈ d.source → f q ∈ d'.source →
      IsOrientationPreservingAt (c.symm.trans (f.toOpenPartialHomeomorph.trans d)) (c q) →
      IsOrientationPreservingAt (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')) (c' q) := by
    intro c c' d d' hc hc' hd hd' q hqc hqc' hfd hfd' hE
    have hτ₁mem : c' q ∈ (c'.symm.trans c).source := by
      rw [hsrcT]
      refine ⟨c'.map_source hqc', ?_⟩
      rw [c'.left_inv hqc']
      exact hqc
    have hτ₁ : IsOrientationPreservingAt (c'.symm.trans c) (c' q) := h c' hc' c hc _ hτ₁mem
    have hτ₁val : (c'.symm.trans c) (c' q) = c q := by
      change c (c'.symm (c' q)) = c q
      rw [c'.left_inv hqc']
    rw [← hτ₁val] at hE
    have hstep1 := isOrientationPreservingAt_trans hτ₁ hE
    have hτ₂mem : d (f q) ∈ (d.symm.trans d').source := by
      rw [hsrcT]
      refine ⟨d.map_source hfd, ?_⟩
      rw [d.left_inv hfd]
      exact hfd'
    have hτ₂ : IsOrientationPreservingAt (d.symm.trans d') (d (f q)) := h d hd d' hd' _ hτ₂mem
    have hval2 : ((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))) (c' q) = d (f q) := by
      change (c.symm.trans (f.toOpenPartialHomeomorph.trans d)) ((c'.symm.trans c) (c' q))
        = d (f q)
      rw [hτ₁val]
      change d (f (c.symm (c q))) = d (f q)
      rw [c.left_inv hqc]
    rw [← hval2] at hτ₂
    have hstep2 := isOrientationPreservingAt_trans hstep1 hτ₂
    have hUopen : IsOpen ((((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).source) :=
      (((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans
          (d.symm.trans d')).open_source.inter
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).open_source
    have hEq : Set.EqOn (((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d'))
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d'))
        ((((c'.symm.trans c).trans
          (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
          (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).source) := by
      intro w hw
      obtain ⟨hwC, -⟩ := hw
      rw [OpenPartialHomeomorph.trans_source] at hwC
      obtain ⟨hwC1, -⟩ := hwC
      rw [OpenPartialHomeomorph.trans_source] at hwC1
      obtain ⟨hw1, hw2⟩ := hwC1
      have hw1' := (hsrcT c' c w).mp hw1
      have hw2' : (c'.symm.trans c) w
          ∈ (c.symm.trans (f.toOpenPartialHomeomorph.trans d)).source := hw2
      have hw2'' := (hsrcE c d _).mp hw2'
      have hcan : c.symm ((c'.symm.trans c) w) = c'.symm w := by
        change c.symm (c (c'.symm w)) = c'.symm w
        exact c.left_inv hw1'.2
      have hfd2 : f (c'.symm w) ∈ d.source := by
        rw [← hcan]
        exact hw2''.2
      change d' (d.symm (d (f (c.symm (c (c'.symm w)))))) = d' (f (c'.symm w))
      rw [c.left_inv hw1'.2, d.left_inv hfd2]
    have hzmem : c' q ∈ ((((c'.symm.trans c).trans
        (c.symm.trans (f.toOpenPartialHomeomorph.trans d))).trans (d.symm.trans d')).source ∩
        (c'.symm.trans (f.toOpenPartialHomeomorph.trans d')).source) := by
      constructor
      · rw [OpenPartialHomeomorph.trans_source]
        constructor
        · rw [OpenPartialHomeomorph.trans_source]
          refine ⟨hτ₁mem, ?_⟩
          rw [Set.mem_preimage, hτ₁val, hsrcE]
          refine ⟨c.map_source hqc, ?_⟩
          rw [c.left_inv hqc]
          exact hfd
        · rw [Set.mem_preimage, hval2]
          exact hτ₂mem
      · rw [hsrcE]
        refine ⟨c'.map_source hqc', ?_⟩
        rw [c'.left_inv hqc']
        exact hfd'
    exact (isOrientationPreservingAt_congr hEq hUopen hzmem
      Set.inter_subset_left Set.inter_subset_right).mp hstep2
  -- winding number of the conjugated curve
  have hconj : ∀ (γ γc : C(I, ℂ)) (q : ℂ), γ 0 = γ 1 → (∀ t, γ t ≠ q) →
      (∀ t, γc t = (starRingEnd ℂ) (γ t)) →
      windingNumber γc ((starRingEnd ℂ) q) = - windingNumber γ q := by
    intro γ γc q hcl hne hcapp
    have hsub_ne : ∀ t : I, shiftedCurve γ q t ≠ 0 := by
      intro t
      have happ : shiftedCurve γ q t = γ t - q := by simp [shiftedCurve]
      rw [happ]
      exact sub_ne_zero.mpr (hne t)
    obtain ⟨L, hL⟩ := exists_isLogLiftOf (shiftedCurve γ q) hsub_ne
    have hspec := windingNumber_spec hcl hne hL
    obtain ⟨Lc, hLcapp⟩ : ∃ Lc : C(I, ℂ), ∀ t : I, Lc t = (starRingEnd ℂ) (L t) :=
      ⟨⟨fun t => (starRingEnd ℂ) (L t), by fun_prop⟩, fun t => rfl⟩
    have hclc : γc 0 = γc 1 := by rw [hcapp 0, hcapp 1, hcl]
    have hnec : ∀ t : I, γc t ≠ (starRingEnd ℂ) q := by
      intro t hct
      rw [hcapp t] at hct
      exact hne t (star_injective hct)
    have hliftc : IsLogLiftOf Lc (shiftedCurve γc ((starRingEnd ℂ) q)) := by
      intro t
      have happc : shiftedCurve γc ((starRingEnd ℂ) q) t = γc t - (starRingEnd ℂ) q := by
        simp [shiftedCurve]
      rw [hLcapp t, Complex.exp_conj, hL t, happc, hcapp t]
      have happ : shiftedCurve γ q t = γ t - q := by simp [shiftedCurve]
      rw [happ, map_sub]
    have hspecc := windingNumber_spec hclc hnec hliftc
    have hincr : Lc 1 - Lc 0 = 2 * Real.pi * Complex.I *
        ((- windingNumber γ q : ℤ) : ℂ) := by
      rw [hLcapp 1, hLcapp 0, ← map_sub, hspec]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
      push_cast
      ring
    rw [hincr] at hspecc
    have h2 := mul_left_cancel₀ Complex.two_pi_I_ne_zero hspecc
    exact_mod_cast h2.symm
  -- circle plumbing
  have hcirc_norm : ∀ (z : ℂ) (ρ : ℝ) (t : I), 0 < ρ → ‖circleLoop z ρ t - z‖ = ρ := by
    intro z ρ t hρ
    have hsub : circleLoop z ρ t - z =
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
      have happ : circleLoop z ρ t = z +
          (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := rfl
      rw [happ]
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, mul_one, abs_of_pos hρ]
  have hcirc_cl : ∀ (z : ℂ) (ρ : ℝ), circleLoop z ρ 0 = circleLoop z ρ 1 := by
    intro z ρ
    have h0 : circleLoop z ρ 0 = z +
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((0 : I) : ℝ) : ℂ)) := rfl
    have h1 : circleLoop z ρ 1 = z +
        (ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (((1 : I) : ℝ) : ℂ)) := rfl
    rw [h0, h1]
    norm_num [Complex.exp_two_pi_mul_I]
  -- eventual constancy of degree −1 via the conjugation reflection
  have hnege : ∀ (e : OpenPartialHomeomorph ℂ ℂ) (z₀ : ℂ) (r : ℝ)
      (hb : Metric.closedBall z₀ r ⊆ e.source) (hr : 0 < r),
      windingDegreeAt e z₀ r hb hr = -1 →
      ∀ᶠ z in 𝓝 z₀, ∀ (r' : ℝ) (hb' : Metric.closedBall z r' ⊆ e.source) (hr' : 0 < r'),
        windingDegreeAt e z r' hb' hr' = -1 := by
    intro e z₀ r hb hr hdeg
    have hRsrc : (Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source = Set.univ :=
      Homeomorph.toOpenPartialHomeomorph_source _
    have hsrc' : (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source
        = e.source := by
      rw [OpenPartialHomeomorph.trans_source, hRsrc, Set.preimage_univ, Set.inter_univ]
    have hdeg' : ∀ (z : ℂ) (ρ : ℝ) (hb₁ : Metric.closedBall z ρ ⊆ e.source)
        (hb₂ : Metric.closedBall z ρ ⊆
          (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source)
        (hρ : 0 < ρ),
        windingDegreeAt (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph)
          z ρ hb₂ hρ = - windingDegreeAt e z ρ hb₁ hρ := by
      intro z ρ hb₁ hb₂ hρ
      have hmem : ∀ t : I, circleLoop z ρ t ∈ e.source := by
        intro t
        apply hb₁
        rw [Metric.mem_closedBall, dist_eq_norm, hcirc_norm z ρ t hρ]
      have hzsrc : z ∈ e.source := hb₁ (Metric.mem_closedBall_self hρ.le)
      have hγcont : Continuous fun t : I => e (circleLoop z ρ t) :=
        e.continuousOn.comp_continuous (circleLoop z ρ).continuous hmem
      have hγcl : (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ)) 0 =
          (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ)) 1 := by
        change e (circleLoop z ρ 0) = e (circleLoop z ρ 1)
        rw [hcirc_cl]
      have hγne : ∀ t : I,
          (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ)) t ≠ e z := by
        intro t heq
        have heq' : e (circleLoop z ρ t) = e z := heq
        have hcne : circleLoop z ρ t ≠ z := by
          intro h0
          have h1 := hcirc_norm z ρ t hρ
          rw [h0, sub_self, norm_zero] at h1
          exact hρ.ne h1
        exact hcne (e.injOn (hmem t) hzsrc heq')
      have hcalc := hconj (⟨fun t => e (circleLoop z ρ t), hγcont⟩ : C(I, ℂ))
        (⟨fun t => (starRingEnd ℂ) (e (circleLoop z ρ t)),
          by exact Continuous.comp continuous_star hγcont⟩ : C(I, ℂ))
        (e z) hγcl hγne (fun t => rfl)
      unfold windingDegreeAt
      have hpt : (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph) z
          = (starRingEnd ℂ) (e z) := rfl
      rw [hpt]
      exact Eq.trans (hwn_ext _ _ _ (fun t => rfl)) hcalc
    have hb₂ : Metric.closedBall z₀ r ⊆
        (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source := by
      rw [hsrc']
      exact hb
    have hpos : IsOrientationPreservingAt
        (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph) z₀ := by
      refine ⟨r, hr, hb₂, ?_⟩
      rw [hdeg' z₀ r hb hb₂ hr, hdeg]
      norm_num
    have hEv := isOrientationPreservingAt_eventually hpos
    filter_upwards [hEv] with z hz
    intro r' hb' hr'
    have hb₂' : Metric.closedBall z r' ⊆
        (e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph).source := by
      rw [hsrc']
      exact hb'
    have hall := (isOrientationPreservingAt_iff_forall _ z).mp hz
    have h1 := hall.2 r' hr' hb₂'
    have h2 := hdeg' z r' hb' hb₂' hr'
    rw [h1] at h2
    omega
  -- the locus of orientation-preservation is open
  have hAopen : IsOpen {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} := by
    rw [isOpen_iff_mem_nhds]
    intro p hpA
    have hpA' : IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p) := hpA
    have hEv := isOrientationPreservingAt_eventually hpA'
    have hcont : ContinuousAt (chartAt ℂ p) p :=
      (chartAt ℂ p).continuousOn.continuousAt
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hEv2 : ∀ᶠ p' in 𝓝 p, IsOrientationPreservingAt (homeoChartRep f p)
        (chartAt ℂ p p') := hcont.eventually hEv
    have hN1 : ∀ᶠ p' in 𝓝 p, p' ∈ (chartAt ℂ p).source :=
      (chartAt ℂ p).open_source.eventually_mem (mem_chart_source ℂ p)
    have hN2 : ∀ᶠ p' in 𝓝 p, f p' ∈ (chartAt ℂ (f p)).source :=
      f.continuous.continuousAt.eventually
        ((chartAt ℂ (f p)).open_source.eventually_mem (mem_chart_source ℂ (f p)))
    have hfinal : ∀ᶠ p' in 𝓝 p, p' ∈ {a : S |
        IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} := by
      filter_upwards [hEv2, hN1, hN2] with p' h1' h2' h3'
      exact hmove (chartAt ℂ p) (chartAt ℂ p') (chartAt ℂ (f p)) (chartAt ℂ (f p'))
        (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ p') (chart_mem_atlas ℂ (f p))
        (chart_mem_atlas ℂ (f p')) p' h2' (mem_chart_source ℂ p') h3'
        (mem_chart_source ℂ (f p')) h1'
    rwa [Filter.eventually_iff, Set.setOf_mem_eq] at hfinal
  -- the complement is open
  have hAcopen : IsOpen {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)}ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro p hpA
    have hpA' : ¬ IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p) := hpA
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (homeoChartRep f p).open_source _ (hbase p)
    have hr : 0 < ε / 2 := by positivity
    have hb : Metric.closedBall (chartAt ℂ p p) (ε / 2) ⊆ (homeoChartRep f p).source :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    have hdeg : windingDegreeAt (homeoChartRep f p) (chartAt ℂ p p) (ε / 2) hb hr = -1 := by
      rcases windingDegreeAt_eq_one_or_neg_one (homeoChartRep f p) hb hr with h1 | h1
      · exact absurd ⟨ε / 2, hr, hb, h1⟩ hpA'
      · exact h1
    have hEv := hnege (homeoChartRep f p) (chartAt ℂ p p) (ε / 2) hb hr hdeg
    have hcont : ContinuousAt (chartAt ℂ p) p :=
      (chartAt ℂ p).continuousOn.continuousAt
        ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
    have hEv2 : ∀ᶠ p' in 𝓝 p, ∀ (r' : ℝ)
        (hb' : Metric.closedBall (chartAt ℂ p p') r' ⊆ (homeoChartRep f p).source)
        (hr' : 0 < r'),
        windingDegreeAt (homeoChartRep f p) (chartAt ℂ p p') r' hb' hr' = -1 :=
      hcont.eventually hEv
    have hN1 : ∀ᶠ p' in 𝓝 p, p' ∈ (chartAt ℂ p).source :=
      (chartAt ℂ p).open_source.eventually_mem (mem_chart_source ℂ p)
    have hN2 : ∀ᶠ p' in 𝓝 p, f p' ∈ (chartAt ℂ (f p)).source :=
      f.continuous.continuousAt.eventually
        ((chartAt ℂ (f p)).open_source.eventually_mem (mem_chart_source ℂ (f p)))
    have hfinal : ∀ᶠ p' in 𝓝 p, p' ∈ {a : S |
        IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)}ᶜ := by
      filter_upwards [hEv2, hN1, hN2] with p' h1' h2' h3'
      intro hcontra
      have hcontra' : IsOrientationPreservingAt (homeoChartRep f p')
          (chartAt ℂ p' p') := hcontra
      have hAtP : IsOrientationPreservingAt (homeoChartRep f p) (chartAt ℂ p p') :=
        hmove (chartAt ℂ p') (chartAt ℂ p) (chartAt ℂ (f p')) (chartAt ℂ (f p))
          (chart_mem_atlas ℂ p') (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ (f p'))
          (chart_mem_atlas ℂ (f p)) p' (mem_chart_source ℂ p') h2'
          (mem_chart_source ℂ (f p')) h3' hcontra'
      obtain ⟨r', hr', hb', hdeg1⟩ := hAtP
      have hneg := h1' r' hb' hr'
      omega
    rwa [Filter.eventually_iff, Set.setOf_mem_eq] at hfinal
  -- clopen plus nonempty gives everything
  have hclopen : IsClopen {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} :=
    ⟨isOpen_compl_iff.mp hAcopen, hAopen⟩
  have huniv := hclopen.eq_univ ⟨p₀, hp⟩
  intro p
  have hmemA : p ∈ {a : S |
      IsOrientationPreservingAt (homeoChartRep f a) (chartAt ℂ a a)} := by
    rw [huniv]
    exact Set.mem_univ p
  exact hmemA

end RiemannDynamics
