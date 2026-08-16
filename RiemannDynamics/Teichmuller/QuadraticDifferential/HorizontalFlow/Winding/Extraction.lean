/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/
import RiemannDynamics.Teichmuller.QuadraticDifferential.HorizontalFlow.Winding.TangentWinding

/-!
# Rounded corners and the extraction of a bigon

The corner pullback and its geometry, the cubic ramp reparametrization, and the
extraction of a monogon or bigon from a self-intersecting trajectory pair.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace RiemannDynamics

section WindingBricks

open unitInterval

/-- The second-quarter evaluation of the four-piece concatenation. -/
theorem quarterPW_eval₁ {f₀ f₁ f₂ f₃ : ℝ → ℂ} {t : ℝ} (h1 : ¬ t ≤ 1/4)
    (h2 : t ≤ 1 / 2) : quarterPW f₀ f₁ f₂ f₃ t = f₁ (4*t - 1) := by
  unfold quarterPW
  rw [if_neg h1, if_pos h2]

/-- The third-quarter evaluation of the four-piece concatenation. -/
theorem quarterPW_eval₂ {f₀ f₁ f₂ f₃ : ℝ → ℂ} {t : ℝ} (h1 : ¬ t ≤ 1/4)
    (h2 : ¬ t ≤ 1/2) (h3 : t ≤ 3 / 4) :
    quarterPW f₀ f₁ f₂ f₃ t = f₂ (4*t - 2) := by
  unfold quarterPW
  rw [if_neg h1, if_neg h2, if_pos h3]

/-- The last-quarter evaluation of the four-piece concatenation. -/
theorem quarterPW_eval₃ {f₀ f₁ f₂ f₃ : ℝ → ℂ} {t : ℝ} (h1 : ¬ t ≤ 1/4)
    (h2 : ¬ t ≤ 1/2) (h3 : ¬ t ≤ 3/4) :
    quarterPW f₀ f₁ f₂ f₃ t = f₃ (4*t - 3) := by
  unfold quarterPW
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- The quarter-schedule concatenation of continuous junction-matched pieces is
continuous. -/
theorem quarterPW_continuous {f₀ f₁ f₂ f₃ : ℝ → ℂ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous f₃)
    (hv01 : f₀ 1 = f₁ 0) (hv12 : f₁ 1 = f₂ 0) (hv23 : f₂ 1 = f₃ 0) :
    Continuous (quarterPW f₀ f₁ f₂ f₃) := by
  unfold quarterPW
  have haff : ∀ c : ℝ, Continuous fun t : ℝ => 4*t - c := by
    intro c
    exact (continuous_const.mul continuous_id).sub continuous_const
  refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
  · exact h₀.comp (continuous_const.mul continuous_id)
  · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · exact h₁.comp (haff 1)
    · refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
      · exact h₂.comp (haff 2)
      · exact h₃.comp (haff 3)
      · intro t ht
        have ht' : t = 3/4 := ht
        subst ht'
        norm_num
        exact hv23
    · intro t ht
      have ht' : t = 1/2 := ht
      subst ht'
      norm_num
      exact hv12
  · intro t ht
    have ht' : t = 1/4 := ht
    subst ht'
    norm_num
    exact hv01

/-- Pointwise relations on the pieces over the unit range transfer to the
quarter-schedule concatenations over the unit range. -/
theorem quarterPW_rel_Icc {P : ℂ → ℂ → ℂ → Prop}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ : ℝ → ℂ}
    (h₀ : ∀ u ∈ Set.Icc (0 : ℝ) 1, P (a₀ u) (b₀ u) (c₀ u))
    (h₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1, P (a₁ u) (b₁ u) (c₁ u))
    (h₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, P (a₂ u) (b₂ u) (c₂ u))
    (h₃ : ∀ u ∈ Set.Icc (0 : ℝ) 1, P (a₃ u) (b₃ u) (c₃ u))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    P (quarterPW a₀ a₁ a₂ a₃ t) (quarterPW b₀ b₁ b₂ b₃ t)
      (quarterPW c₀ c₁ c₂ c₃ t) := by
  unfold quarterPW
  split_ifs with hA hB hC
  · exact h₀ _ ⟨by linarith [ht.1], by linarith⟩
  · exact h₁ _ ⟨by linarith [not_le.mp hA], by linarith⟩
  · exact h₂ _ ⟨by linarith [not_le.mp hB], by linarith⟩
  · exact h₃ _ ⟨by linarith [not_le.mp hC], by linarith [ht.2]⟩

/-- **The exponent count for a quartered loop**: a loop assembled on the quarter
schedule whose values against the squared velocity field are exponentially presented
by matched continuous exponent pieces satisfies the product count, the winding of the
value loop plus twice the winding of the velocity loop being the exponent increment
in whole turns. -/
theorem rounded_count {q : ℂ → ℂ}
    {p₀ p₁ p₂ p₃ g₀ g₁ g₂ g₃ L₀ L₁ L₂ L₃ : ℝ → ℂ} {m : ℤ}
    (hgc₀ : Continuous g₀) (hgc₁ : Continuous g₁) (hgc₂ : Continuous g₂)
    (hgc₃ : Continuous g₃)
    (hLc₀ : Continuous L₀) (hLc₁ : Continuous L₁) (hLc₂ : Continuous L₂)
    (hLc₃ : Continuous L₃)
    (hv30 : p₃ 1 = p₀ 0)
    (hg01 : g₀ 1 = g₁ 0) (hg12 : g₁ 1 = g₂ 0) (hg23 : g₂ 1 = g₃ 0)
    (hg30 : g₃ 1 = g₀ 0)
    (hL01 : L₀ 1 = L₁ 0) (hL12 : L₁ 1 = L₂ 0) (hL23 : L₂ 1 = L₃ 0)
    (hLm : L₃ 1 - L₀ 0 = 2 * Real.pi * Complex.I * m)
    (hexp₀ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₀ u) * g₀ u ^ 2 = Complex.exp (L₀ u))
    (hexp₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₁ u) * g₁ u ^ 2 = Complex.exp (L₁ u))
    (hexp₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₂ u) * g₂ u ^ 2 = Complex.exp (L₂ u))
    (hexp₃ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₃ u) * g₃ u ^ 2 = Complex.exp (L₃ u))
    (hqc : Continuous fun t : I => q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ)))) :
    windingNumber ⟨fun t : I => q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ))), hqc⟩ 0
      + 2 * windingNumber ⟨fun t : I => 4 * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)),
          continuous_const.mul ((quarterPW_continuous hgc₀ hgc₁ hgc₂ hgc₃
            hg01 hg12 hg23).comp continuous_subtype_val)⟩ 0 = m := by
  have hq0 : ∀ F₀ F₁ F₂ F₃ : ℝ → ℂ, quarterPW F₀ F₁ F₂ F₃ 0 = F₀ 0 := by
    intro F₀ F₁ F₂ F₃
    rw [quarterPW_eval₀ (by norm_num)]
    norm_num
  have hq1 : ∀ F₀ F₁ F₂ F₃ : ℝ → ℂ, quarterPW F₀ F₁ F₂ F₃ 1 = F₃ 1 := by
    intro F₀ F₁ F₂ F₃
    rw [quarterPW_eval₃ (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hcoe0 : (((0 : I) : ℝ)) = 0 := rfl
  have hcoe1 : (((1 : I) : ℝ)) = 1 := rfl
  have hexpAll : ∀ t : I,
      q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ)))
        * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)) ^ 2
      = Complex.exp (quarterPW L₀ L₁ L₂ L₃ ((t : ℝ))) := by
    intro t
    exact quarterPW_rel_Icc
      (P := fun a b c => q a * b ^ 2 = Complex.exp c)
      hexp₀ hexp₁ hexp₂ hexp₃ t.2
  have h16 : Complex.exp (((Real.log 16 : ℝ)) : ℂ) = 16 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 16)]
    norm_num
  set Lt : C(I, ℂ) := ⟨fun t : I => quarterPW L₀ L₁ L₂ L₃ ((t : ℝ))
      + ((Real.log 16 : ℝ) : ℂ),
    ((quarterPW_continuous hLc₀ hLc₁ hLc₂ hLc₃ hL01 hL12 hL23).comp
      continuous_subtype_val).add continuous_const⟩ with hLtdef
  set Acur : C(I, ℂ) :=
    ⟨fun t : I => q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ))), hqc⟩ with hAdef
  set dcur : C(I, ℂ) := ⟨fun t : I => 4 * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)),
    continuous_const.mul ((quarterPW_continuous hgc₀ hgc₁ hgc₂ hgc₃
      hg01 hg12 hg23).comp continuous_subtype_val)⟩ with hddef
  have hexpF : ∀ t : I, Acur t * dcur t ^ 2 = Complex.exp (Lt t) := by
    intro t
    change q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ)))
        * (4 * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ))) ^ 2
      = Complex.exp (quarterPW L₀ L₁ L₂ L₃ ((t : ℝ)) + ((Real.log 16 : ℝ) : ℂ))
    rw [Complex.exp_add, h16, ← hexpAll t]
    ring
  have hAcl : Acur 0 = Acur 1 := by
    change q (quarterPW p₀ p₁ p₂ p₃ (((0:I) : ℝ)))
      = q (quarterPW p₀ p₁ p₂ p₃ (((1:I) : ℝ)))
    rw [hcoe0, hcoe1, hq0, hq1, hv30]
  have hdcl : dcur 0 = dcur 1 := by
    change 4 * quarterPW g₀ g₁ g₂ g₃ (((0:I) : ℝ))
      = 4 * quarterPW g₀ g₁ g₂ g₃ (((1:I) : ℝ))
    rw [hcoe0, hcoe1, hq0, hq1, hg30]
  have hAne : ∀ t : I, Acur t ≠ 0 := by
    intro t h0
    have h1 := hexpAll t
    have h2 : q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ))) = 0 := h0
    rw [h2, zero_mul] at h1
    exact Complex.exp_ne_zero _ h1.symm
  have hdne : ∀ t : I, dcur t ≠ 0 := by
    intro t h0
    have h1 := hexpAll t
    have h2 : (4 : ℂ) * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)) = 0 := h0
    have h3 : quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact h
    rw [h3] at h1
    norm_num at h1
    exact Complex.exp_ne_zero _ h1.symm
  have hLtm : Lt 1 - Lt 0 = 2 * Real.pi * Complex.I * m := by
    change (quarterPW L₀ L₁ L₂ L₃ (((1:I) : ℝ)) + ((Real.log 16 : ℝ) : ℂ))
        - (quarterPW L₀ L₁ L₂ L₃ (((0:I) : ℝ)) + ((Real.log 16 : ℝ) : ℂ))
      = 2 * Real.pi * Complex.I * m
    rw [hcoe0, hcoe1, hq0, hq1]
    rw [show ∀ a b c : ℂ, (a + c) - (b + c) = a - b from fun a b c => by ring]
    exact hLm
  exact winding_product_exp hAcl hdcl hAne hdne hexpF hLtm

/-- **The free-basepoint tangent winding**: the tangent loop of a simple closed
continuously differentiable curve winds exactly once, in one of the two senses. -/
theorem tangent_winding_free {γ g : ℝ → ℂ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (g t) t)
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hcl : γ 0 = γ 1) (hgcl : g 1 = g 0)
    (hinj : Set.InjOn γ (Set.Ico 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0) :
    windingNumber ⟨fun t : I => g ((t : ℝ)),
        hg.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = 1
      ∨ windingNumber ⟨fun t : I => g ((t : ℝ)),
        hg.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = -1 := by
  classical
  have hγc : ContinuousOn γ (Set.Icc 0 1) :=
    fun v hv => (hd v hv).continuousAt.continuousWithinAt
  obtain ⟨c₀, hc₀mem, hc₀min⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr zero_le_one)
    (Complex.continuous_im.comp_continuousOn hγc)
  have hmin₀ : ∀ t ∈ Set.Icc (0:ℝ) 1, (γ c₀).im ≤ (γ t).im :=
    fun t ht => isMinOn_iff.mp hc₀min t ht
  -- normalize the endpoint minimum to the start
  set c : ℝ := if c₀ = 1 then 0 else c₀ with hcdef
  have hcmem : c ∈ Set.Icc (0:ℝ) 1 := by
    rw [hcdef]
    split_ifs
    · norm_num
    · exact hc₀mem
  have hclt : c < 1 := by
    rw [hcdef]
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne hc₀mem.2 h
  have hmin : ∀ t ∈ Set.Icc (0:ℝ) 1, (γ c).im ≤ (γ t).im := by
    intro t ht
    rw [hcdef]
    split_ifs with h
    · rw [hcl, ← h]
      exact hmin₀ t ht
    · exact hmin₀ t ht
  -- the sign dichotomy at a minimum basepoint, for any admissible data
  have hbase : ∀ γ' g' : ℝ → ℂ,
      (∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γ' (g' t) t) →
      ∀ hg' : ContinuousOn g' (Set.Icc 0 1),
      γ' 0 = γ' 1 → g' 1 = g' 0 → Set.InjOn γ' (Set.Ico 0 1) →
      (∀ u ∈ Set.Icc (0:ℝ) 1, g' u ≠ 0) →
      (∀ t ∈ Set.Icc (0:ℝ) 1, (γ' 0).im ≤ (γ' t).im) →
      windingNumber ⟨fun t : I => g' ((t : ℝ)),
          hg'.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = 1
        ∨ windingNumber ⟨fun t : I => g' ((t : ℝ)),
          hg'.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = -1 := by
    intro γ' g' hd' hg' hcl' hgcl' hinj' hgne' hmin'
    have him0 : (g' 0).im = 0 := min_im_deriv_zero hd' hcl' hgcl' hmin'
    have hne0 : g' 0 ≠ 0 := hgne' 0 (by norm_num)
    have hre0 : (g' 0).re ≠ 0 := by
      intro h0
      exact hne0 (Complex.ext h0 him0)
    rcases lt_or_gt_of_ne hre0 with h | h
    · exact Or.inr (tangent_winding_neg hd' hg' hcl' hgcl' hinj' hgne' hmin' h)
    · exact Or.inl (tangent_winding_pos hd' hg' hcl' hgcl' hinj' hgne' hmin' h)
  rcases eq_or_lt_of_le hcmem.1 with hc0 | hc0
  · -- the minimum is already at the start
    refine hbase γ g hd hg hcl hgcl hinj hgne ?_
    intro t ht
    rw [hc0]
    exact hmin t ht
  · -- rotate the parametrization to start at the minimum
    set γc : ℝ → ℂ := fun u => if u + c ≤ 1 then γ (u + c) else γ (u + c - 1)
      with hγcdef
    set gc : ℝ → ℂ := fun u => if u + c ≤ 1 then g (u + c) else g (u + c - 1)
      with hgcdef
    have hmem1 : ∀ u : ℝ, 0 ≤ u → u + c ≤ 1 → u + c ∈ Set.Icc (0:ℝ) 1 :=
      fun u h1 h2 => ⟨by linarith [hc0.le], h2⟩
    have hmem2 : ∀ u : ℝ, u ≤ 1 → 1 < u + c → u + c - 1 ∈ Set.Icc (0:ℝ) 1 :=
      fun u h1 h2 => ⟨by linarith, by linarith [hclt.le]⟩
    have hshift1 : ∀ t : ℝ, t + c ∈ Set.Icc (0:ℝ) 1 →
        HasDerivAt (fun u => γ (u + c)) (g (t + c)) t := by
      intro t ht
      have h1 := HasDerivAt.scomp t (hd (t + c) ht) ((hasDerivAt_id t).add_const c)
      simpa using! h1
    have hshift2 : ∀ t : ℝ, t + c - 1 ∈ Set.Icc (0:ℝ) 1 →
        HasDerivAt (fun u => γ (u + c - 1)) (g (t + c - 1)) t := by
      intro t ht
      have h1 := HasDerivAt.scomp t (hd (t + c - 1) ht)
        (((hasDerivAt_id t).add_const c).sub_const 1)
      simpa using! h1
    have hdc : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt γc (gc t) t := by
      intro t ht
      rcases lt_trichotomy (t + c) 1 with hlt | heq | hgt
      · have hval : gc t = g (t + c) := if_pos hlt.le
        rw [hval]
        refine open_congr (O := {u : ℝ | u + c < 1})
          (isOpen_lt (continuous_id.add continuous_const) continuous_const) hlt
          (hshift1 t (hmem1 t ht.1 hlt.le)) ?_
        intro u hu
        exact if_pos (le_of_lt hu)
      · have hval : gc t = g (t + c) := if_pos heq.le
        rw [hval, heq]
        have hL : HasDerivAt (fun u => γ (u + c)) (g 1) t := by
          have h1 := hshift1 t (by rw [heq]; norm_num)
          rwa [heq] at h1
        have hR : HasDerivAt (fun u => γ (u + c - 1)) (g 0) t := by
          have h1 := hshift2 t (by rw [show t + c - 1 = 0 by linarith]; norm_num)
          rwa [show t + c - 1 = 0 by linarith] at h1
        refine seam_glue (a := t - 1) (b := t + 1) (by linarith) (by linarith)
          hL hR hgcl ?_ ?_
        · intro u hu
          exact if_pos (by linarith [hu.2])
        · intro u hu
          rcases eq_or_lt_of_le hu.1 with he | hlt'
          · rw [← he]
            change (if t + c ≤ 1 then γ (t + c) else γ (t + c - 1)) = γ (t + c - 1)
            rw [if_pos heq.le, heq]
            norm_num
            exact hcl.symm
          · exact if_neg (by linarith)
      · have hval : gc t = g (t + c - 1) := if_neg (by linarith)
        rw [hval]
        refine open_congr (O := {u : ℝ | 1 < u + c})
          (isOpen_lt continuous_const (continuous_id.add continuous_const)) hgt
          (hshift2 t (hmem2 t ht.2 hgt)) ?_
        intro u hu
        exact if_neg (by simp only [Set.mem_ofPred_eq] at hu; linarith)
    have hgcc : ContinuousOn gc (Set.Icc 0 1) := by
      intro t ht
      rcases lt_trichotomy (t + c) 1 with hlt | heq | hgt
      · rw [← continuousWithinAt_inter
          (IsOpen.mem_nhds (show IsOpen {u : ℝ | u + c < 1} from
            isOpen_lt (continuous_id.add continuous_const) continuous_const) hlt)]
        refine ContinuousWithinAt.congr
          (f := fun u => g (u + c)) ?_ ?_ (if_pos hlt.le)
        · refine ContinuousWithinAt.comp (hg (t + c) (hmem1 t ht.1 hlt.le))
            ((continuous_id.add continuous_const).continuousWithinAt) ?_
          rintro u ⟨hu1, hu2⟩
          exact hmem1 u hu1.1 (le_of_lt hu2)
        · rintro u ⟨hu1, hu2⟩
          exact if_pos (le_of_lt hu2)
      · have hIic : ContinuousWithinAt gc (Set.Icc 0 1 ∩ Set.Iic t) t := by
          refine ContinuousWithinAt.congr
            (f := fun u => g (u + c)) ?_ ?_ (if_pos heq.le)
          · refine ContinuousWithinAt.comp (hg (t + c) (by rw [heq]; norm_num))
              ((continuous_id.add continuous_const).continuousWithinAt) ?_
            rintro u ⟨hu1, hu2⟩
            exact hmem1 u hu1.1 (by simp only [Set.mem_Iic] at hu2; linarith)
          · rintro u ⟨hu1, hu2⟩
            exact if_pos (by simp only [Set.mem_Iic] at hu2; linarith)
        have hIci : ContinuousWithinAt gc (Set.Icc 0 1 ∩ Set.Ici t) t := by
          refine ContinuousWithinAt.congr
            (f := fun u => g (u + c - 1)) ?_ ?_ ?_
          · refine ContinuousWithinAt.comp
              (hg (t + c - 1) (by rw [show t + c - 1 = 0 by linarith]; norm_num))
              (((continuous_id.add continuous_const).sub
                continuous_const).continuousWithinAt) ?_
            rintro u ⟨hu1, hu2⟩
            simp only [Set.mem_Ici] at hu2
            rcases eq_or_lt_of_le hu2 with he | hlt'
            · rw [← he]
              change t + c - 1 ∈ Set.Icc (0:ℝ) 1
              rw [show t + c - 1 = 0 by linarith]
              norm_num
            · exact hmem2 u hu1.2 (by linarith)
          · rintro u ⟨hu1, hu2⟩
            simp only [Set.mem_Ici] at hu2
            rcases eq_or_lt_of_le hu2 with he | hlt'
            · rw [← he]
              change (if t + c ≤ 1 then g (t + c) else g (t + c - 1)) = g (t + c - 1)
              rw [if_pos heq.le, heq]
              norm_num
              exact hgcl
            · exact if_neg (by linarith)
          · change (if t + c ≤ 1 then g (t + c) else g (t + c - 1)) = g (t + c - 1)
            rw [if_pos heq.le, heq]
            norm_num
            exact hgcl
        have hunion := hIic.union hIci
        rwa [← Set.inter_union_distrib_left, Set.Iic_union_Ici,
          Set.inter_univ] at hunion
      · rw [← continuousWithinAt_inter
          (IsOpen.mem_nhds (show IsOpen {u : ℝ | 1 < u + c} from
            isOpen_lt continuous_const (continuous_id.add continuous_const)) hgt)]
        refine ContinuousWithinAt.congr
          (f := fun u => g (u + c - 1)) ?_ ?_ (if_neg (by linarith))
        · refine ContinuousWithinAt.comp (hg (t + c - 1) (hmem2 t ht.2 hgt))
            (((continuous_id.add continuous_const).sub
              continuous_const).continuousWithinAt) ?_
          rintro u ⟨hu1, hu2⟩
          simp only [Set.mem_ofPred_eq] at hu2
          exact hmem2 u hu1.2 hu2
        · rintro u ⟨hu1, hu2⟩
          simp only [Set.mem_ofPred_eq] at hu2
          exact if_neg (by linarith)
    have hclc : γc 0 = γc 1 := by
      change (if (0:ℝ) + c ≤ 1 then γ ((0:ℝ) + c) else γ ((0:ℝ) + c - 1))
        = (if (1:ℝ) + c ≤ 1 then γ ((1:ℝ) + c) else γ ((1:ℝ) + c - 1))
      rw [if_pos (by linarith), if_neg (by linarith : ¬ (1:ℝ) + c ≤ 1)]
      norm_num
    have hgclc : gc 1 = gc 0 := by
      change (if (1:ℝ) + c ≤ 1 then g ((1:ℝ) + c) else g ((1:ℝ) + c - 1))
        = (if (0:ℝ) + c ≤ 1 then g ((0:ℝ) + c) else g ((0:ℝ) + c - 1))
      rw [if_neg (by linarith : ¬ (1:ℝ) + c ≤ 1), if_pos (by linarith)]
      norm_num
    have hgnec : ∀ u ∈ Set.Icc (0:ℝ) 1, gc u ≠ 0 := by
      intro u hu
      change (if u + c ≤ 1 then g (u + c) else g (u + c - 1)) ≠ 0
      split_ifs with h
      · exact hgne _ (hmem1 u hu.1 h)
      · exact hgne _ (hmem2 u hu.2 (not_le.mp h))
    have hminc : ∀ t ∈ Set.Icc (0:ℝ) 1, (γc 0).im ≤ (γc t).im := by
      intro t ht
      have h0 : γc 0 = γ c := by
        change (if (0:ℝ) + c ≤ 1 then γ ((0:ℝ) + c) else γ ((0:ℝ) + c - 1)) = γ c
        rw [if_pos (by linarith)]
        norm_num
      rw [h0]
      change (γ c).im ≤ (if t + c ≤ 1 then γ (t + c) else γ (t + c - 1)).im
      split_ifs with h
      · exact hmin _ (hmem1 t ht.1 h)
      · exact hmin _ (hmem2 t ht.2 (not_le.mp h))
    have hinjc : Set.InjOn γc (Set.Ico 0 1) := by
      intro x hx y hy hxy
      have hxv : γc x = if x + c ≤ 1 then γ (x + c) else γ (x + c - 1) := rfl
      have hyv : γc y = if y + c ≤ 1 then γ (y + c) else γ (y + c - 1) := rfl
      rw [hxv, hyv] at hxy
      by_cases hxb : x + c ≤ 1 <;> by_cases hyb : y + c ≤ 1
      · rw [if_pos hxb, if_pos hyb] at hxy
        rcases eq_or_lt_of_le hxb with hx1 | hx1 <;>
          rcases eq_or_lt_of_le hyb with hy1 | hy1
        · linarith
        · exfalso
          rw [hx1, ← hcl] at hxy
          have h3 := hinj (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Set.Ico 0 1)
            ⟨by linarith [hy.1, hc0.le], hy1⟩ hxy
          linarith [hy.1]
        · exfalso
          rw [hy1, ← hcl] at hxy
          have h3 := hinj ⟨by linarith [hx.1, hc0.le], hx1⟩
            (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Set.Ico 0 1) hxy
          linarith [hx.1]
        · have h3 := hinj ⟨by linarith [hx.1, hc0.le], hx1⟩
            ⟨by linarith [hy.1, hc0.le], hy1⟩ hxy
          linarith
      · rw [if_pos hxb, if_neg hyb] at hxy
        have hyb' := not_le.mp hyb
        rcases eq_or_lt_of_le hxb with hx1 | hx1
        · exfalso
          rw [hx1, ← hcl] at hxy
          have h3 := hinj (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Set.Ico 0 1)
            ⟨by linarith, by linarith [hy.2, hclt]⟩ hxy
          linarith
        · exfalso
          have h3 := hinj ⟨by linarith [hx.1, hc0.le], hx1⟩
            ⟨by linarith, by linarith [hy.2, hclt]⟩ hxy
          linarith [hx.1, hy.2]
      · rw [if_neg hxb, if_pos hyb] at hxy
        have hxb' := not_le.mp hxb
        rcases eq_or_lt_of_le hyb with hy1 | hy1
        · exfalso
          rw [hy1, ← hcl] at hxy
          have h3 := hinj ⟨by linarith, by linarith [hx.2, hclt]⟩
            (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Set.Ico 0 1) hxy
          linarith
        · exfalso
          have h3 := hinj ⟨by linarith, by linarith [hx.2, hclt]⟩
            ⟨by linarith [hy.1, hc0.le], hy1⟩ hxy
          linarith [hy.1, hx.2]
      · rw [if_neg hxb, if_neg hyb] at hxy
        have h3 := hinj ⟨by linarith [not_le.mp hxb], by linarith [hclt, hx.2]⟩
          ⟨by linarith [not_le.mp hyb], by linarith [hclt, hy.2]⟩ hxy
        linarith
    have hrot := hbase γc gc hdc hgcc hclc hgclc hinjc hgnec hminc
    set G : C(I, ℂ) := ⟨fun t : I => g ((t : ℝ)),
      hg.comp_continuous continuous_subtype_val fun t => t.2⟩ with hGdef
    have hGcl : G 0 = G 1 := by
      change g (((0:I) : ℝ)) = g (((1:I) : ℝ))
      rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
      exact hgcl.symm
    have hGne : ∀ t : I, G t ≠ 0 := fun t => hgne _ t.2
    have hident : (⟨fun t : I => gc ((t : ℝ)),
        hgcc.comp_continuous continuous_subtype_val fun t => t.2⟩ : C(I, ℂ))
        = ⟨fun t : I => rotateLoop G c ((t : ℝ)),
          (rotateLoop_continuous G hGcl).comp continuous_subtype_val⟩ := by
      ext t
      change gc ((t : ℝ)) = rotateLoop G c ((t : ℝ))
      rcases le_or_gt (((t : ℝ)) + c) 1 with h | h
      · rw [rotateLoop_apply_le G h]
        change (if ((t:ℝ)) + c ≤ 1 then g (((t:ℝ)) + c) else g (((t:ℝ)) + c - 1))
          = G (Set.projIcc 0 1 zero_le_one (((t:ℝ)) + c))
        rw [if_pos h]
        change g (((t:ℝ)) + c)
          = g ((Set.projIcc 0 1 zero_le_one (((t:ℝ)) + c) : I) : ℝ)
        congr 1
        rw [Set.projIcc_of_mem zero_le_one (hmem1 _ t.2.1 h)]
      · rw [rotateLoop_apply_gt G (not_le.mpr h)]
        change (if ((t:ℝ)) + c ≤ 1 then g (((t:ℝ)) + c) else g (((t:ℝ)) + c - 1))
          = G (Set.projIcc 0 1 zero_le_one (((t:ℝ)) + c - 1))
        rw [if_neg (not_le.mpr h)]
        change g (((t:ℝ)) + c - 1)
          = g ((Set.projIcc 0 1 zero_le_one (((t:ℝ)) + c - 1) : I) : ℝ)
        congr 1
        rw [Set.projIcc_of_mem zero_le_one (hmem2 _ t.2.2 h)]
    rw [hident] at hrot
    have hwr := winding_rotate (γ := G) (q := 0) hGcl hGne hcmem
    rw [hwr] at hrot
    exact hrot

/-- **The bigon exclusion core**: a simple closed continuously differentiable loop in
a convex subset of the upper half plane, avoiding the zeros of the differential, whose
value loop against the squared tangent carries an index count with corner defect in
`{-1, 0, 1}`, contradicts the nonnegativity of point windings supplied for the
positively oriented parametrization among the loop and its reverse. -/
theorem no_bigon_loop {q : ℂ → ℂ} {U : Set ℂ} (hUconv : Convex ℝ U)
    (hUH : U ⊆ {z : ℂ | 0 < z.im})
    (hq : DifferentiableOn ℂ q {z : ℂ | 0 < z.im})
    (hq0 : ∃ z₀ : ℂ, 0 < z₀.im ∧ q z₀ ≠ 0)
    (hfin : {z ∈ U | q z = 0}.Finite)
    {ρ g : ℝ → ℂ} {m : ℤ}
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ρ (g t) t)
    (hgc : ContinuousOn g (Set.Icc 0 1))
    (hcl : ρ 0 = ρ 1) (hgcl : g 1 = g 0)
    (hinj : Set.InjOn ρ (Set.Ico 0 1))
    (hgne : ∀ u ∈ Set.Icc (0 : ℝ) 1, g u ≠ 0)
    (htr : ∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u ∈ U)
    (hqne : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (ρ u) ≠ 0)
    (hqρc : Continuous fun t : I => q (ρ ((t : ℝ))))
    (hcount : windingNumber ⟨fun t : I => q (ρ ((t : ℝ))), hqρc⟩ 0
        + 2 * windingNumber ⟨fun t : I => g ((t : ℝ)),
          hgc.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = m)
    (hm3 : m = -1 ∨ m = 0 ∨ m = 1)
    (hnnP : windingNumber ⟨fun t : I => g ((t : ℝ)),
          hgc.comp_continuous continuous_subtype_val fun t => t.2⟩ 0 = 1 →
        ∀ hc' : Continuous fun t : I => ρ ((t : ℝ)),
        ∀ ζ : ℂ, (∀ t : I, ρ ((t : ℝ)) ≠ ζ) →
        0 ≤ windingNumber ⟨fun t : I => ρ ((t : ℝ)), hc'⟩ ζ)
    (hnnR : ∀ hc : Continuous fun t : I => -(g (1 - ((t : ℝ)))),
        windingNumber ⟨fun t : I => -(g (1 - ((t : ℝ)))), hc⟩ 0 = 1 →
        ∀ hc' : Continuous fun t : I => ρ (1 - ((t : ℝ))),
        ∀ ζ : ℂ, (∀ t : I, ρ (1 - ((t : ℝ))) ≠ ζ) →
        0 ≤ windingNumber ⟨fun t : I => ρ (1 - ((t : ℝ))), hc'⟩ ζ) :
    False := by
  classical
  have hρc : ContinuousOn ρ (Set.Icc 0 1) :=
    fun v hv => (hd v hv).continuousAt.continuousWithinAt
  set G : C(I, ℂ) := ⟨fun t : I => g ((t : ℝ)),
    hgc.comp_continuous continuous_subtype_val fun t => t.2⟩ with hGdef
  set P : C(I, ℂ) := ⟨fun t : I => ρ ((t : ℝ)),
    hρc.comp_continuous continuous_subtype_val fun t => t.2⟩ with hPdef
  have hdich := tangent_winding_free hd hgc hcl hgcl hinj hgne
  have hPcl : P 0 = P 1 := by
    change ρ (((0:I) : ℝ)) = ρ (((1:I) : ℝ))
    rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
    exact hcl
  have hPtr : ∀ t : I, P t ∈ U := fun t => htr _ t.2
  have hPqne : ∀ t : I, q (P t) ≠ 0 := fun t => hqne _ t.2
  rcases hdich with h1 | h1
  · -- positively oriented: direct contradiction
    have hnn := hnnP h1 (hρc.comp_continuous continuous_subtype_val fun t => t.2)
    have hq1 := winding_holo_nonneg hUconv hUH hq hq0 hfin P hPcl hPtr hPqne hnn
    have hcurve : (⟨fun t : I => q (P t),
        hq.continuousOn.comp_continuous P.continuous fun t => hUH (hPtr t)⟩
        : C(I, ℂ)) = ⟨fun t : I => q (ρ ((t : ℝ))), hqρc⟩ :=
      ContinuousMap.ext fun t => rfl
    rw [hcurve] at hq1
    rw [h1] at hcount
    rcases hm3 with h | h | h <;> omega
  · -- negatively oriented: reverse and contradict
    have hrevc : Continuous fun t : I => ρ (1 - ((t : ℝ))) := by
      refine hρc.comp_continuous
        (continuous_const.sub continuous_subtype_val) ?_
      intro t
      exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    have hgrevc : Continuous fun t : I => -(g (1 - ((t : ℝ)))) := by
      refine Continuous.neg (hgc.comp_continuous
        (continuous_const.sub continuous_subtype_val) ?_)
      intro t
      exact ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    -- the reversed tangent loop winds positively
    have hGcl : G 0 = G 1 := by
      change g (((0:I) : ℝ)) = g (((1:I) : ℝ))
      rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
      exact hgcl.symm
    have hGne : ∀ t : I, G t ≠ 0 := fun t => hgne _ t.2
    have hidg : (⟨fun t : I => -(g (1 - ((t : ℝ)))), hgrevc⟩ : C(I, ℂ))
        = -(G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) := by
      ext t
      change -(g (1 - ((t : ℝ)))) = -(g ((unitInterval.symm t : ℝ)))
      rw [unitInterval.coe_symm_eq]
    have hRcl : (G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) 0
        = (G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) 1 := by
      change G (unitInterval.symm 0) = G (unitInterval.symm 1)
      rw [unitInterval.symm_zero, unitInterval.symm_one, hGcl]
    have hRne : ∀ t : I,
        (G.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩) t ≠ 0 :=
      fun t => hGne _
    have hWgrev : windingNumber
        (⟨fun t : I => -(g (1 - ((t : ℝ)))), hgrevc⟩ : C(I, ℂ)) 0 = 1 := by
      rw [hidg, winding_neg hRcl hRne, winding_reverse hGcl hGne, h1]
      norm_num
    -- the reversed value loop winds oppositely
    have hqPcl : (⟨fun t : I => q (ρ ((t : ℝ))), hqρc⟩ : C(I, ℂ)) 0
        = (⟨fun t : I => q (ρ ((t : ℝ))), hqρc⟩ : C(I, ℂ)) 1 := by
      change q (ρ (((0:I) : ℝ))) = q (ρ (((1:I) : ℝ)))
      rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl, hcl]
    have hqPne : ∀ t : I,
        (⟨fun t : I => q (ρ ((t : ℝ))), hqρc⟩ : C(I, ℂ)) t ≠ 0 :=
      fun t => hqne _ t.2
    -- nonnegativity for the reversed loop
    have hnn := hnnR hgrevc hWgrev hrevc
    -- assemble the reversed loop data for the holomorphic winding bound
    set Prev : C(I, ℂ) := ⟨fun t : I => ρ (1 - ((t : ℝ))), hrevc⟩ with hPrevdef
    have hPrevcl : Prev 0 = Prev 1 := by
      change ρ (1 - (((0:I) : ℝ))) = ρ (1 - (((1:I) : ℝ)))
      rw [show (((0:I) : ℝ)) = 0 from rfl, show (((1:I) : ℝ)) = 1 from rfl]
      norm_num
      exact hcl.symm
    have hPrevtr : ∀ t : I, Prev t ∈ U := by
      intro t
      exact htr _ ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    have hPrevqne : ∀ t : I, q (Prev t) ≠ 0 := by
      intro t
      exact hqne _ ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
    have hq2 := winding_holo_nonneg hUconv hUH hq hq0 hfin Prev hPrevcl
      hPrevtr hPrevqne hnn
    -- the reversed value winding is the negative of the original
    have hidq : (⟨fun t : I => q (Prev t),
        hq.continuousOn.comp_continuous Prev.continuous
          fun t => hUH (hPrevtr t)⟩ : C(I, ℂ))
        = (⟨fun t : I => q (ρ ((t : ℝ))), hqρc⟩ : C(I, ℂ)).comp
            ⟨unitInterval.symm, unitInterval.continuous_symm⟩ := by
      ext t
      change q (ρ (1 - ((t : ℝ)))) = q (ρ ((unitInterval.symm t : ℝ)))
      rw [unitInterval.coe_symm_eq]
    rw [hidq, winding_reverse hqPcl hqPne] at hq2
    rw [h1] at hcount
    rcases hm3 with h | h | h <;> omega

/-- **The pulled-back corner arc**: through an injective natural chart whose image
contains a circle, the pullback of the circle parametrization lies in the chart
domain, develops to the circle, differentiates to the rotated tangent over the chart
derivative, and its squared-velocity value is the exponential of an explicit affine
exponent. -/
theorem corner_pullback {q Φ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hΦ : DifferentiableOn ℂ Φ S) (hinj : Set.InjOn Φ S)
    (hsq : ∀ z ∈ S, deriv Φ z ^ 2 = -q z) (hqne : ∀ z ∈ S, q z ≠ 0)
    {c : ℂ} {r α ω : ℝ} (hr : 0 < r) (hω : ω ≠ 0)
    (htr : ∀ u : ℝ, c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      ∈ Φ '' S) (u : ℝ) :
    Function.invFunOn Φ S (c + (r : ℂ)
        * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))) ∈ S
    ∧ Φ (Function.invFunOn Φ S (c + (r : ℂ)
        * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))))
      = c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))
    ∧ HasDerivAt (fun v : ℝ => Function.invFunOn Φ S
        (c + (r : ℂ) * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * (v : ℂ)))))
      (((r : ℂ) * Complex.I * (ω : ℂ)
          * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)))
        / deriv Φ (Function.invFunOn Φ S (c + (r : ℂ)
          * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))))) u
    ∧ q (Function.invFunOn Φ S (c + (r : ℂ)
          * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))))
        * (((r : ℂ) * Complex.I * (ω : ℂ)
            * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)))
          / deriv Φ (Function.invFunOn Φ S (c + (r : ℂ)
            * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))))) ^ 2
      = Complex.exp (((Real.log (r^2 * ω^2) : ℝ) : ℂ)
          + 2 * Complex.I * ((α : ℂ) + (ω : ℂ) * u)) := by
  obtain ⟨hmem, hdev⟩ := chart_pullback_dev (Φ := Φ) (S := S) (htr u)
  have hder : deriv Φ (Function.invFunOn Φ S (c + (r : ℂ)
      * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)))) ≠ 0 := by
    intro h0
    have h1 := hsq _ hmem
    rw [h0] at h1
    exact hqne _ hmem (by simpa using h1.symm)
  have hcirc := circle_hasDerivAt c r α ω u
  have hpull := chart_pullback_hasDerivAt hS hΦ hinj hcirc
    (Filter.Eventually.of_forall htr) hder
  refine ⟨hmem, hdev, hpull, ?_⟩
  have hchain : deriv Φ (Function.invFunOn Φ S (c + (r : ℂ)
        * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u))))
      * (((r : ℂ) * Complex.I * (ω : ℂ)
          * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)))
        / deriv Φ (Function.invFunOn Φ S (c + (r : ℂ)
          * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)))))
      = (r : ℂ) * Complex.I * (ω : ℂ)
          * Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)) :=
    mul_div_cancel₀ _ hder
  have hphase := pullback_phase hsq hmem hchain
  rw [hphase]
  -- `-(riω e^{iθ})² = r²ω² e^{2iθ} = exp(log(r²ω²) + 2iθ)`
  rw [Complex.exp_add]
  have h1 : Complex.exp (((Real.log (r^2 * ω^2) : ℝ) : ℂ)) = ((r^2 * ω^2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
  have h2 : Complex.exp (2 * Complex.I * ((α : ℂ) + (ω : ℂ) * u))
      = Complex.exp (Complex.I * ((α : ℂ) + (ω : ℂ) * u)) ^ 2 := by
    rw [sq, ← Complex.exp_add]
    congr 1
    ring
  rw [h1, h2]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The corner geometry**: for direction signs `εh, εv`, start angle `α = -εv·π/2`,
sweep `ω = εh·εv·π/2`, and center at the inner corner, the quarter circle joins the
truncated endpoints with matching tangent directions, sweeps a signed half turn of
exponent, and stays within three radii of the corner. -/
theorem corner_geometry {εh εv : ℝ} (hεh : εh = 1 ∨ εh = -1)
    (hεv : εv = 1 ∨ εv = -1) {r α ω : ℝ} (hr : 0 < r)
    (hα : α = -εv * (Real.pi / 2)) (hω : ω = εh * εv * (Real.pi / 2)) (w : ℂ) :
    ((w - (εh:ℂ)*r + Complex.I*(εv:ℂ)*r)
        + (r:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*(0:ℝ)))
      = w - (εh:ℂ)*r)
    ∧ ((w - (εh:ℂ)*r + Complex.I*(εv:ℂ)*r)
        + (r:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*(1:ℝ)))
      = w + Complex.I*(εv:ℂ)*r)
    ∧ ((r:ℂ) * Complex.I * (ω:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*(0:ℝ)))
      = ((r * (Real.pi/2) : ℝ):ℂ) * (εh:ℂ))
    ∧ ((r:ℂ) * Complex.I * (ω:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*(1:ℝ)))
      = ((r * (Real.pi/2) : ℝ):ℂ) * Complex.I * (εv:ℂ))
    ∧ ((((Real.log (r^2*ω^2) : ℝ):ℂ) + 2*Complex.I*((α:ℂ) + (ω:ℂ)*(1:ℝ)))
        - ((((Real.log (r^2*ω^2) : ℝ):ℂ) + 2*Complex.I*((α:ℂ) + (ω:ℂ)*(0:ℝ))))
      = Complex.I * (εh:ℂ) * (εv:ℂ) * Real.pi)
    ∧ (∀ u : ℝ, dist ((w - (εh:ℂ)*r + Complex.I*(εv:ℂ)*r)
        + (r:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*u))) w ≤ 3*r) := by
  have hv2 : (εv:ℂ)^2 = 1 := by
    rcases hεv with h | h <;> rw [h] <;> norm_num
  have hh2 : (εh:ℂ)^2 = 1 := by
    rcases hεh with h | h <;> rw [h] <;> norm_num
  have hvabs : |εv| = 1 := by
    rcases hεv with h | h <;> rw [h] <;> norm_num
  have hhabs : |εh| = 1 := by
    rcases hεh with h | h <;> rw [h] <;> norm_num
  have hεneg : -εv = 1 ∨ -εv = -1 := by
    rcases hεv with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  have hea : Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*(0:ℝ)))
      = -((εv:ℂ) * Complex.I) := by
    rw [hα]
    push_cast
    rw [show Complex.I * (-(εv:ℂ) * (((Real.pi:ℂ))/2) + (ω:ℂ) * 0)
      = Complex.I * ((-εv : ℝ):ℂ) * (((Real.pi:ℂ))/2) by push_cast; ring]
    rw [exp_quarter hεneg]
    push_cast
    ring
  have heb : Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*(1:ℝ))) = (εh:ℂ) := by
    rw [hα, hω]
    rcases hεh with h | h
    · rw [h]
      rw [show Complex.I * ((((-εv * (Real.pi/2) : ℝ)):ℂ)
          + (((1 * εv * (Real.pi/2) : ℝ)):ℂ)*(1:ℝ)) = 0 by push_cast; ring]
      rw [Complex.exp_zero]
      norm_num
    · rw [h]
      rcases hεv with h2 | h2 <;> rw [h2]
      · rw [show Complex.I * ((((-(1:ℝ) * (Real.pi/2) : ℝ)):ℂ)
            + (((-1 * (1:ℝ) * (Real.pi/2) : ℝ)):ℂ)*(1:ℝ))
          = -((Real.pi:ℂ) * Complex.I) by push_cast; ring]
        rw [Complex.exp_neg, Complex.exp_pi_mul_I]
        norm_num
      · rw [show Complex.I * ((((-(-1:ℝ) * (Real.pi/2) : ℝ)):ℂ)
            + (((-1 * (-1:ℝ) * (Real.pi/2) : ℝ)):ℂ)*(1:ℝ))
          = (Real.pi:ℂ) * Complex.I by push_cast; ring]
        rw [Complex.exp_pi_mul_I]
        norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hea]
    ring
  · rw [heb]
    ring
  · rw [hea, hω]
    push_cast
    linear_combination (-(r:ℂ)*(εh:ℂ)*(εv:ℂ)^2*((Real.pi:ℂ)/2)) * Complex.I_sq
      + ((r:ℂ)*(εh:ℂ)*((Real.pi:ℂ)/2)) * hv2
  · rw [heb, hω]
    push_cast
    linear_combination (r:ℂ) * (Real.pi/2) * Complex.I * (εv:ℂ) * hh2
  · rw [hω]
    push_cast
    ring
  · intro u
    rw [dist_eq_norm]
    have h1 : (w - (εh:ℂ)*r + Complex.I*(εv:ℂ)*r)
        + (r:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*u)) - w
        = (-((εh:ℂ)*r) + Complex.I*(εv:ℂ)*r)
          + (r:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*u)) := by
      ring
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖(r:ℂ) * Complex.exp (Complex.I * ((α:ℂ) + (ω:ℂ)*u))‖ = r := by
      rw [norm_mul, Complex.norm_exp]
      have h3 : (Complex.I * ((α:ℂ) + (ω:ℂ)*u)).re = 0 := by
        rw [Complex.mul_re, Complex.I_re, Complex.I_im]
        simp
      rw [h3, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
    have h4 : ‖(-((εh:ℂ)*r) + Complex.I*(εv:ℂ)*r)‖ ≤ 2*r := by
      refine le_trans (norm_add_le _ _) ?_
      have h5 : ‖-((εh:ℂ)*r)‖ = r := by
        rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, hhabs, one_mul, abs_of_pos hr]
      have h6 : ‖Complex.I*(εv:ℂ)*r‖ = r := by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hvabs, one_mul,
          abs_of_pos hr]
      rw [h5, h6]
      linarith
    rw [h2]
    linarith

/-- The cubic ramp from `a` with endpoint speed `v` and total displacement `L`. -/
noncomputable def cubicRamp (a v L : ℝ) : ℝ → ℝ := fun u =>
  a + v*u + 6*(L - v)*(u^2/2 - u^3/3)

/-- The speed of the cubic ramp. -/
noncomputable def cubicRampSpeed (v L : ℝ) : ℝ → ℝ := fun u =>
  v + 6*(L - v)*(u*(1 - u))

/-- The cubic ramp differentiates to its speed. -/
theorem cubicRamp_hasDerivAt (a v L u : ℝ) :
    HasDerivAt (cubicRamp a v L) (cubicRampSpeed v L u) u := by
  unfold cubicRamp cubicRampSpeed
  have h1 : HasDerivAt (fun u : ℝ => a + v*u + 6*(L - v)*(u^2/2 - u^3/3))
      (0 + v*1 + 6*(L - v)*((2*u^1)/2 - (3*u^2)/3)) u := by
    refine HasDerivAt.add (HasDerivAt.add (hasDerivAt_const u a) ?_) ?_
    · simpa using (hasDerivAt_id u).const_mul v
    · refine HasDerivAt.const_mul _ (HasDerivAt.sub ?_ ?_)
      · simpa using (hasDerivAt_pow 2 u).div_const 2
      · simpa using (hasDerivAt_pow 3 u).div_const 3
  convert h1 using 1
  ring

/-- The cubic ramp starts at its base point. -/
theorem cubicRamp_zero (a v L : ℝ) : cubicRamp a v L 0 = a := by
  unfold cubicRamp
  ring

/-- The cubic ramp ends at the base point shifted by the ramp length. -/
theorem cubicRamp_one (a v L : ℝ) : cubicRamp a v L 1 = a + L := by
  unfold cubicRamp
  ring

/-- The ramp speed starts at the initial velocity. -/
theorem cubicRampSpeed_zero (v L : ℝ) : cubicRampSpeed v L 0 = v := by
  unfold cubicRampSpeed
  ring

/-- The ramp speed returns to the initial velocity at time one. -/
theorem cubicRampSpeed_one (v L : ℝ) : cubicRampSpeed v L 1 = v := by
  unfold cubicRampSpeed
  ring

/-- The ramp speed is continuous. -/
theorem cubicRampSpeed_continuous (v L : ℝ) : Continuous (cubicRampSpeed v L) := by
  unfold cubicRampSpeed
  fun_prop

/-- The ramp speed is positive when the initial velocity is below three times the
length. -/
theorem cubicRampSpeed_pos {v L : ℝ} (hv : 0 < v) (h3 : v < 3 * L) :
    ∀ u ∈ Set.Icc (0:ℝ) 1, 0 < cubicRampSpeed v L u := by
  intro u hu
  unfold cubicRampSpeed
  have h4 : u*(1 - u) ≤ 1/4 := by nlinarith [sq_nonneg (u - 1/2)]
  have h5 : 0 ≤ u*(1 - u) := mul_nonneg hu.1 (by linarith [hu.2])
  rcases le_total v L with h | h
  · nlinarith
  · nlinarith

/-- The cubic ramp is strictly increasing on the unit interval. -/
theorem cubicRamp_strictMono {a v L : ℝ} (hv : 0 < v) (h3 : v < 3 * L) :
    StrictMonoOn (cubicRamp a v L) (Set.Icc 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) ?_ ?_
  · exact Continuous.continuousOn (by unfold cubicRamp; fun_prop)
  · intro u hu
    rw [interior_Icc] at hu
    rw [(cubicRamp_hasDerivAt a v L u).deriv]
    exact cubicRampSpeed_pos hv h3 u ⟨hu.1.le, hu.2.le⟩

/-- The ramp maps the unit interval onto `[a, a + L]`. -/
theorem cubicRamp_mapsTo {a v L : ℝ} (hv : 0 < v) (h3 : v < 3 * L) :
    ∀ u ∈ Set.Icc (0:ℝ) 1, cubicRamp a v L u ∈ Set.Icc a (a + L) := by
  intro u hu
  have hmono := cubicRamp_strictMono (a := a) hv h3
  constructor
  · rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h, cubicRamp_zero]
    · have h2 := (hmono (Set.left_mem_Icc.mpr zero_le_one) hu h).le
      rwa [cubicRamp_zero] at h2
  · rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h, cubicRamp_one]
    · have h2 := (hmono hu (Set.right_mem_Icc.mpr zero_le_one) h).le
      rwa [cubicRamp_one] at h2

/-- Pointwise affine quarter-speed chain rule. -/
theorem affine_chain_at {f g : ℝ → ℂ} {c t : ℝ}
    (hd : HasDerivAt f (g (4 * t - c)) (4 * t - c)) :
    HasDerivAt (fun u => f (4*u - c)) (4 * g (4*t - c)) t := by
  have hin : HasDerivAt (fun u : ℝ => 4*u - c) 4 t := by
    simpa using ((hasDerivAt_id t).const_mul (4:ℝ)).sub_const c
  have hcomp := HasDerivAt.scomp t hd hin
  convert! hcomp using 1

/-- **Quarter-schedule differentiability from unit-interval data**: pieces
differentiable on the closed unit interval with matching junction values and
velocities concatenate to a curve differentiable at every point of the closed unit
interval. -/
theorem quarterPW_hasDerivAt_Icc {f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ : ℝ → ℂ}
    (hd₀ : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₀ (g₀ u) u)
    (hd₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₁ (g₁ u) u)
    (hd₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₂ (g₂ u) u)
    (hd₃ : ∀ u ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₃ (g₃ u) u)
    (hv01 : f₀ 1 = f₁ 0) (hv12 : f₁ 1 = f₂ 0) (hv23 : f₂ 1 = f₃ 0)
    (hg01 : g₀ 1 = g₁ 0) (hg12 : g₁ 1 = g₂ 0) (hg23 : g₂ 1 = g₃ 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (quarterPW f₀ f₁ f₂ f₃)
      (4 * quarterPW g₀ g₁ g₂ g₃ t) t := by
  intro t ht
  have hc₀ : ∀ s : ℝ, 4*s ∈ Set.Icc (0:ℝ) 1 →
      HasDerivAt (fun u => f₀ (4*u)) (4 * g₀ (4*s)) s := by
    intro s hs
    have h := affine_chain_at (c := 0) (t := s)
      (by rw [show 4*s - 0 = 4*s by ring]; exact hd₀ _ hs)
    simpa using h
  have hc₁ : ∀ s : ℝ, 4*s - 1 ∈ Set.Icc (0:ℝ) 1 →
      HasDerivAt (fun u => f₁ (4*u - 1)) (4 * g₁ (4*s - 1)) s :=
    fun s hs => affine_chain_at (hd₁ _ hs)
  have hc₂ : ∀ s : ℝ, 4*s - 2 ∈ Set.Icc (0:ℝ) 1 →
      HasDerivAt (fun u => f₂ (4*u - 2)) (4 * g₂ (4*s - 2)) s :=
    fun s hs => affine_chain_at (hd₂ _ hs)
  have hc₃ : ∀ s : ℝ, 4*s - 3 ∈ Set.Icc (0:ℝ) 1 →
      HasDerivAt (fun u => f₃ (4*u - 3)) (4 * g₃ (4*s - 3)) s :=
    fun s hs => affine_chain_at (hd₃ _ hs)
  rcases lt_trichotomy t (1/4) with h1 | h1 | h1
  · rw [quarterPW_eval₀ (le_of_lt h1)]
    refine open_congr (O := Set.Ioo (-1 : ℝ) (1/4)) isOpen_Ioo
      ⟨by linarith [ht.1], h1⟩
      (hc₀ t ⟨by linarith [ht.1], by linarith⟩) ?_
    intro u hu
    exact quarterPW_eval₀ (le_of_lt hu.2)
  · subst h1
    rw [quarterPW_eval₀ le_rfl, show (4:ℝ)*(1/4) = 1 by norm_num]
    have hL' : HasDerivAt (fun u => f₀ (4*u)) (4 * g₀ 1) (1/4) := by
      have h := hc₀ (1/4) (by norm_num)
      rwa [show (4:ℝ)*(1/4) = 1 by norm_num] at h
    have hR' : HasDerivAt (fun u => f₁ (4*u - 1)) (4 * g₁ 0) (1/4) := by
      have h := hc₁ (1/4) (by norm_num)
      rwa [show (4:ℝ)*(1/4) - 1 = 0 by norm_num] at h
    refine seam_glue (a := 0) (b := 1/2) (by norm_num) (by norm_num)
      hL' hR' (by rw [hg01]) ?_ ?_
    · intro u hu
      exact quarterPW_eval₀ hu.2
    · intro u hu
      rcases eq_or_lt_of_le hu.1 with he | hlt
      · rw [← he, quarterPW_eval₀ le_rfl]
        norm_num
        exact hv01
      · exact quarterPW_eval₁ (not_le.mpr hlt) (le_of_lt hu.2)
  · rcases lt_trichotomy t (1/2) with h2 | h2 | h2
    · rw [quarterPW_eval₁ (not_le.mpr h1) (le_of_lt h2)]
      refine open_congr (isOpen_Ioo (a := 1/4) (b := 1/2)) ⟨h1, h2⟩
        (hc₁ t ⟨by linarith, by linarith⟩) ?_
      intro u hu
      exact quarterPW_eval₁ (not_le.mpr hu.1) (le_of_lt hu.2)
    · subst h2
      rw [quarterPW_eval₁ (not_le.mpr h1) le_rfl,
        show (4:ℝ)*(1/2) - 1 = 1 by norm_num]
      have hL' : HasDerivAt (fun u => f₁ (4*u - 1)) (4 * g₁ 1) (1/2) := by
        have h := hc₁ (1/2) (by norm_num)
        rwa [show (4:ℝ)*(1/2) - 1 = 1 by norm_num] at h
      have hR' : HasDerivAt (fun u => f₂ (4*u - 2)) (4 * g₂ 0) (1/2) := by
        have h := hc₂ (1/2) (by norm_num)
        rwa [show (4:ℝ)*(1/2) - 2 = 0 by norm_num] at h
      refine seam_glue (a := 1/4) (b := 3/4) (by norm_num) (by norm_num)
        hL' hR' (by rw [hg12]) ?_ ?_
      · intro u hu
        exact quarterPW_eval₁ (not_le.mpr hu.1) hu.2
      · intro u hu
        rcases eq_or_lt_of_le hu.1 with he | hlt
        · rw [← he, quarterPW_eval₁ (not_le.mpr h1) le_rfl]
          norm_num
          exact hv12
        · refine quarterPW_eval₂ (not_le.mpr ?_) (not_le.mpr hlt) (le_of_lt hu.2)
          linarith
    · rcases lt_trichotomy t (3/4) with h3 | h3 | h3
      · rw [quarterPW_eval₂ (not_le.mpr (by linarith)) (not_le.mpr h2)
          (le_of_lt h3)]
        refine open_congr (isOpen_Ioo (a := 1/2) (b := 3/4)) ⟨h2, h3⟩
          (hc₂ t ⟨by linarith, by linarith⟩) ?_
        intro u hu
        exact quarterPW_eval₂ (not_le.mpr (by linarith [hu.1]))
          (not_le.mpr hu.1) (le_of_lt hu.2)
      · subst h3
        rw [quarterPW_eval₂ (not_le.mpr (by norm_num)) (not_le.mpr h2) le_rfl,
          show (4:ℝ)*(3/4) - 2 = 1 by norm_num]
        have hL' : HasDerivAt (fun u => f₂ (4*u - 2)) (4 * g₂ 1) (3/4) := by
          have h := hc₂ (3/4) (by norm_num)
          rwa [show (4:ℝ)*(3/4) - 2 = 1 by norm_num] at h
        have hR' : HasDerivAt (fun u => f₃ (4*u - 3)) (4 * g₃ 0) (3/4) := by
          have h := hc₃ (3/4) (by norm_num)
          rwa [show (4:ℝ)*(3/4) - 3 = 0 by norm_num] at h
        refine seam_glue (a := 1/2) (b := 1) (by norm_num) (by norm_num)
          hL' hR' (by rw [hg23]) ?_ ?_
        · intro u hu
          exact quarterPW_eval₂ (not_le.mpr (by linarith [hu.1]))
            (not_le.mpr hu.1) hu.2
        · intro u hu
          rcases eq_or_lt_of_le hu.1 with he | hlt
          · rw [← he, quarterPW_eval₂ (not_le.mpr (by norm_num))
              (not_le.mpr h2) le_rfl]
            norm_num
            exact hv23
          · exact quarterPW_eval₃ (not_le.mpr (by linarith))
              (not_le.mpr (by linarith)) (not_le.mpr hlt)
      · rw [quarterPW_eval₃ (not_le.mpr (by linarith)) (not_le.mpr (by linarith))
          (not_le.mpr h3)]
        refine open_congr (isOpen_Ioo (a := 3/4) (b := 2)) ⟨h3, by linarith [ht.2]⟩
          (hc₃ t ⟨by linarith, by linarith [ht.2]⟩) ?_
        intro u hu
        exact quarterPW_eval₃ (not_le.mpr (by linarith [hu.1]))
          (not_le.mpr (by linarith [hu.1])) (not_le.mpr hu.1)

/-- On the unit interval the unclamped quarter schedule agrees with the clamped
concatenation of the restricted pieces. -/
theorem quarterPW_eq_concat {f₀ f₁ f₂ f₃ : ℝ → ℂ}
    (h₀ : ContinuousOn f₀ (Set.Icc 0 1)) (h₁ : ContinuousOn f₁ (Set.Icc 0 1))
    (h₂ : ContinuousOn f₂ (Set.Icc 0 1)) (h₃ : ContinuousOn f₃ (Set.Icc 0 1)) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, quarterPW f₀ f₁ f₂ f₃ t
      = quarterConcat ⟨fun x : I => f₀ ((x : ℝ)),
          h₀.comp_continuous continuous_subtype_val fun x => x.2⟩
        ⟨fun x : I => f₁ ((x : ℝ)),
          h₁.comp_continuous continuous_subtype_val fun x => x.2⟩
        ⟨fun x : I => f₂ ((x : ℝ)),
          h₂.comp_continuous continuous_subtype_val fun x => x.2⟩
        ⟨fun x : I => f₃ ((x : ℝ)),
          h₃.comp_continuous continuous_subtype_val fun x => x.2⟩ t := by
  intro t ht
  unfold quarterPW quarterConcat
  split_ifs with hA hB hC
  · change f₀ (4*t) = f₀ ((Set.projIcc 0 1 zero_le_one (4*t) : I) : ℝ)
    congr 1
    rw [Set.projIcc_of_mem zero_le_one ⟨by linarith [ht.1], by linarith⟩]
  · change f₁ (4*t - 1) = f₁ ((Set.projIcc 0 1 zero_le_one (4*t - 1) : I) : ℝ)
    congr 1
    rw [Set.projIcc_of_mem zero_le_one ⟨by linarith [not_le.mp hA], by linarith⟩]
  · change f₂ (4*t - 2) = f₂ ((Set.projIcc 0 1 zero_le_one (4*t - 2) : I) : ℝ)
    congr 1
    rw [Set.projIcc_of_mem zero_le_one ⟨by linarith [not_le.mp hB], by linarith⟩]
  · change f₃ (4*t - 3) = f₃ ((Set.projIcc 0 1 zero_le_one (4*t - 3) : I) : ℝ)
    congr 1
    rw [Set.projIcc_of_mem zero_le_one
      ⟨by linarith [not_le.mp hC], by linarith [ht.2]⟩]

/-- **Unit-interval continuity of the quarter schedule** from unit-interval-continuous
junction-matched pieces. -/
theorem quarterPW_continuousOn_Icc {f₀ f₁ f₂ f₃ : ℝ → ℂ}
    (h₀ : ContinuousOn f₀ (Set.Icc 0 1)) (h₁ : ContinuousOn f₁ (Set.Icc 0 1))
    (h₂ : ContinuousOn f₂ (Set.Icc 0 1)) (h₃ : ContinuousOn f₃ (Set.Icc 0 1))
    (hv01 : f₀ 1 = f₁ 0) (hv12 : f₁ 1 = f₂ 0) (hv23 : f₂ 1 = f₃ 0) :
    ContinuousOn (quarterPW f₀ f₁ f₂ f₃) (Set.Icc 0 1) := by
  have hcc := quarterConcat_continuous
    ⟨fun x : I => f₀ ((x : ℝ)), h₀.comp_continuous continuous_subtype_val fun x => x.2⟩
    ⟨fun x : I => f₁ ((x : ℝ)), h₁.comp_continuous continuous_subtype_val fun x => x.2⟩
    ⟨fun x : I => f₂ ((x : ℝ)), h₂.comp_continuous continuous_subtype_val fun x => x.2⟩
    ⟨fun x : I => f₃ ((x : ℝ)), h₃.comp_continuous continuous_subtype_val fun x => x.2⟩
    (by change f₀ (((1:I) : ℝ)) = f₁ (((0:I) : ℝ)); simpa using hv01)
    (by change f₁ (((1:I) : ℝ)) = f₂ (((0:I) : ℝ)); simpa using hv12)
    (by change f₂ (((1:I) : ℝ)) = f₃ (((0:I) : ℝ)); simpa using hv23)
  exact (hcc.continuousOn).congr (quarterPW_eq_concat h₀ h₁ h₂ h₃)

/-- **The arc piece of the rounded bigon**: a trajectory arc with exponentially
presented squared velocity, reparametrized by the cubic ramp, carries the scomp
derivative on the unit interval, endpoint positions and velocities at the truncation
data, an exponential presentation with clamped-speed modulus, and a continuous
exponent. -/
theorem arc_piece {q : ℂ → ℂ} {f df : ℝ → ℂ} {a L v : ℝ} {E : ℂ}
    (hv : 0 < v) (h3 : v < 3 * L)
    (hd : ∀ w ∈ Set.Icc a (a + L), HasDerivAt f (df w) w)
    (hdc : ContinuousOn df (Set.Icc a (a + L)))
    (hE : ∀ w ∈ Set.Icc a (a + L), q (f w) * df w ^ 2 = Complex.exp E) :
    (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun x => f (cubicRamp a v L x))
      (((cubicRampSpeed v L u : ℝ) : ℂ) * df (cubicRamp a v L u)) u)
    ∧ f (cubicRamp a v L 0) = f a ∧ f (cubicRamp a v L 1) = f (a + L)
    ∧ ((cubicRampSpeed v L 0 : ℝ) : ℂ) * df (cubicRamp a v L 0)
        = ((v : ℝ) : ℂ) * df a
    ∧ ((cubicRampSpeed v L 1 : ℝ) : ℂ) * df (cubicRamp a v L 1)
        = ((v : ℝ) : ℂ) * df (a + L)
    ∧ (∀ u ∈ Set.Icc (0:ℝ) 1,
        q (f (cubicRamp a v L u))
          * (((cubicRampSpeed v L u : ℝ) : ℂ) * df (cubicRamp a v L u)) ^ 2
        = Complex.exp
          (((Real.log ((cubicRampSpeed v L (max 0 (min 1 u)))^2) : ℝ) : ℂ) + E))
    ∧ ContinuousOn (fun u => ((cubicRampSpeed v L u : ℝ) : ℂ)
        * df (cubicRamp a v L u)) (Set.Icc 0 1)
    ∧ Continuous (fun u : ℝ =>
        ((Real.log ((cubicRampSpeed v L (max 0 (min 1 u)))^2) : ℝ) : ℂ) + E) := by
  have hmaps := cubicRamp_mapsTo (a := a) hv h3
  have hclamp : ∀ u : ℝ, max 0 (min 1 u) ∈ Set.Icc (0:ℝ) 1 := by
    intro u
    constructor
    · exact le_max_left 0 _
    · rcases le_total u 1 with h | h
      · rw [min_eq_right h]
        exact max_le zero_le_one h
      · rw [min_eq_left h]
        norm_num
  have hspos : ∀ u : ℝ, 0 < cubicRampSpeed v L (max 0 (min 1 u)) :=
    fun u => cubicRampSpeed_pos hv h3 _ (hclamp u)
  refine ⟨?_, by rw [cubicRamp_zero], by rw [cubicRamp_one],
    by rw [cubicRampSpeed_zero, cubicRamp_zero],
    by rw [cubicRampSpeed_one, cubicRamp_one], ?_, ?_, ?_⟩
  · intro u hu
    have h1 := HasDerivAt.scomp u (hd _ (hmaps u hu)) (cubicRamp_hasDerivAt a v L u)
    convert! h1 using 1
  · intro u hu
    have hcl : max 0 (min 1 u) = u := by
      rw [min_eq_right hu.2, max_eq_right hu.1]
    rw [hcl]
    have h1 := hE _ (hmaps u hu)
    have hpos : (0:ℝ) < cubicRampSpeed v L u := cubicRampSpeed_pos hv h3 u hu
    rw [Complex.exp_add,
      show Complex.exp (((Real.log ((cubicRampSpeed v L u)^2) : ℝ) : ℂ))
        = (((cubicRampSpeed v L u)^2 : ℝ) : ℂ) by
          rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]]
    push_cast
    linear_combination ((cubicRampSpeed v L u : ℝ) : ℂ)^2 * h1
  · refine ContinuousOn.mul ?_ (hdc.comp ?_ hmaps)
    · exact (Complex.continuous_ofReal.comp
        (cubicRampSpeed_continuous v L)).continuousOn
    · refine Continuous.continuousOn ?_
      exact continuous_iff_continuousAt.mpr
        fun u => (cubicRamp_hasDerivAt a v L u).continuousAt
  · have hclampc : Continuous fun u : ℝ => max 0 (min 1 u) :=
      continuous_const.max (continuous_const.min continuous_id)
    refine Continuous.add ?_ continuous_const
    refine Complex.continuous_ofReal.comp ?_
    refine Continuous.log ?_ ?_
    · exact ((cubicRampSpeed_continuous v L).comp hclampc).pow 2
    · intro u
      have := hspos u
      positivity

/-- **Seam identification**: through an injective chart, the pullback of the
development of a domain point is that point. -/
theorem seam_match {Φ : ℂ → ℂ} {S : Set ℂ} (hinj : Set.InjOn Φ S)
    {x : ℂ} (hx : x ∈ S) {w : ℂ} (hdev : Φ x = w) :
    Function.invFunOn Φ S w = x := by
  have hw : w ∈ Φ '' S := ⟨x, hx, hdev⟩
  obtain ⟨hmem, hdev'⟩ := chart_pullback_dev (Φ := Φ) (S := S) hw
  exact hinj hmem hx (by rw [hdev', hdev])

/-- **The exponent count from unit-interval data**: the quartered-loop count holds
with velocity and exponent pieces continuous on the unit interval only. -/
theorem rounded_count_Icc {q : ℂ → ℂ}
    {p₀ p₁ p₂ p₃ g₀ g₁ g₂ g₃ L₀ L₁ L₂ L₃ : ℝ → ℂ} {m : ℤ}
    (hgc₀ : ContinuousOn g₀ (Set.Icc 0 1)) (hgc₁ : ContinuousOn g₁ (Set.Icc 0 1))
    (hgc₂ : ContinuousOn g₂ (Set.Icc 0 1)) (hgc₃ : ContinuousOn g₃ (Set.Icc 0 1))
    (hLc₀ : ContinuousOn L₀ (Set.Icc 0 1)) (hLc₁ : ContinuousOn L₁ (Set.Icc 0 1))
    (hLc₂ : ContinuousOn L₂ (Set.Icc 0 1)) (hLc₃ : ContinuousOn L₃ (Set.Icc 0 1))
    (hv30 : p₃ 1 = p₀ 0)
    (hg01 : g₀ 1 = g₁ 0) (hg12 : g₁ 1 = g₂ 0) (hg23 : g₂ 1 = g₃ 0)
    (hg30 : g₃ 1 = g₀ 0)
    (hL01 : L₀ 1 = L₁ 0) (hL12 : L₁ 1 = L₂ 0) (hL23 : L₂ 1 = L₃ 0)
    (hLm : L₃ 1 - L₀ 0 = 2 * Real.pi * Complex.I * m)
    (hexp₀ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₀ u) * g₀ u ^ 2 = Complex.exp (L₀ u))
    (hexp₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₁ u) * g₁ u ^ 2 = Complex.exp (L₁ u))
    (hexp₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₂ u) * g₂ u ^ 2 = Complex.exp (L₂ u))
    (hexp₃ : ∀ u ∈ Set.Icc (0 : ℝ) 1, q (p₃ u) * g₃ u ^ 2 = Complex.exp (L₃ u))
    (hqc : Continuous fun t : I => q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ)))) :
    windingNumber ⟨fun t : I => q (quarterPW p₀ p₁ p₂ p₃ ((t : ℝ))), hqc⟩ 0
      + 2 * windingNumber ⟨fun t : I => 4 * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)),
          continuous_const.mul
            ((quarterPW_continuousOn_Icc hgc₀ hgc₁ hgc₂ hgc₃
              hg01 hg12 hg23).comp_continuous
                continuous_subtype_val fun t => t.2)⟩ 0 = m := by
  classical
  set cl : ℝ → ℝ := fun u => max 0 (min 1 u) with hcldef
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hclid : ∀ u ∈ Set.Icc (0:ℝ) 1, cl u = u := by
    intro u hu
    rw [hcldef]
    change max 0 (min 1 u) = u
    rw [min_eq_right hu.2, max_eq_right hu.1]
  have hclmem : ∀ u : ℝ, cl u ∈ Set.Icc (0:ℝ) 1 := by
    intro u
    constructor
    · exact le_max_left 0 _
    · rcases le_total u 1 with h | h
      · rw [hcldef]
        change max 0 (min 1 u) ≤ 1
        rw [min_eq_right h]
        exact max_le zero_le_one h
      · rw [hcldef]
        change max 0 (min 1 u) ≤ 1
        rw [min_eq_left h]
        norm_num
  have hcl0 : cl 0 = 0 := hclid 0 (by norm_num)
  have hcl1 : cl 1 = 1 := hclid 1 (by norm_num)
  have hcount := rounded_count (q := q) (p₀ := p₀) (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
    (g₀ := g₀ ∘ cl) (g₁ := g₁ ∘ cl) (g₂ := g₂ ∘ cl) (g₃ := g₃ ∘ cl)
    (L₀ := L₀ ∘ cl) (L₁ := L₁ ∘ cl) (L₂ := L₂ ∘ cl) (L₃ := L₃ ∘ cl) (m := m)
    (hgc₀.comp_continuous hclc hclmem) (hgc₁.comp_continuous hclc hclmem)
    (hgc₂.comp_continuous hclc hclmem) (hgc₃.comp_continuous hclc hclmem)
    (hLc₀.comp_continuous hclc hclmem) (hLc₁.comp_continuous hclc hclmem)
    (hLc₂.comp_continuous hclc hclmem) (hLc₃.comp_continuous hclc hclmem)
    hv30
    (by change g₀ (cl 1) = g₁ (cl 0); rw [hcl0, hcl1, hg01])
    (by change g₁ (cl 1) = g₂ (cl 0); rw [hcl0, hcl1, hg12])
    (by change g₂ (cl 1) = g₃ (cl 0); rw [hcl0, hcl1, hg23])
    (by change g₃ (cl 1) = g₀ (cl 0); rw [hcl0, hcl1, hg30])
    (by change L₀ (cl 1) = L₁ (cl 0); rw [hcl0, hcl1, hL01])
    (by change L₁ (cl 1) = L₂ (cl 0); rw [hcl0, hcl1, hL12])
    (by change L₂ (cl 1) = L₃ (cl 0); rw [hcl0, hcl1, hL23])
    (by change L₃ (cl 1) - L₀ (cl 0) = _; rw [hcl0, hcl1]; exact hLm)
    (by intro u hu; change q (p₀ u) * g₀ (cl u) ^ 2 = Complex.exp (L₀ (cl u))
        rw [hclid u hu]; exact hexp₀ u hu)
    (by intro u hu; change q (p₁ u) * g₁ (cl u) ^ 2 = Complex.exp (L₁ (cl u))
        rw [hclid u hu]; exact hexp₁ u hu)
    (by intro u hu; change q (p₂ u) * g₂ (cl u) ^ 2 = Complex.exp (L₂ (cl u))
        rw [hclid u hu]; exact hexp₂ u hu)
    (by intro u hu; change q (p₃ u) * g₃ (cl u) ^ 2 = Complex.exp (L₃ (cl u))
        rw [hclid u hu]; exact hexp₃ u hu)
    hqc
  have hident : (⟨fun t : I => 4 * quarterPW (g₀ ∘ cl) (g₁ ∘ cl) (g₂ ∘ cl)
        (g₃ ∘ cl) ((t : ℝ)),
      continuous_const.mul (((quarterPW_continuousOn_Icc
        (hgc₀.comp_continuous hclc hclmem).continuousOn
        (hgc₁.comp_continuous hclc hclmem).continuousOn
        (hgc₂.comp_continuous hclc hclmem).continuousOn
        (hgc₃.comp_continuous hclc hclmem).continuousOn
        (by change g₀ (cl 1) = g₁ (cl 0); rw [hcl0, hcl1, hg01])
        (by change g₁ (cl 1) = g₂ (cl 0); rw [hcl0, hcl1, hg12])
        (by change g₂ (cl 1) = g₃ (cl 0); rw [hcl0, hcl1, hg23]))).comp_continuous
          continuous_subtype_val fun t => t.2)⟩ : C(I, ℂ))
      = ⟨fun t : I => 4 * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ)),
          continuous_const.mul
            ((quarterPW_continuousOn_Icc hgc₀ hgc₁ hgc₂ hgc₃
              hg01 hg12 hg23).comp_continuous
                continuous_subtype_val fun t => t.2)⟩ := by
    ext t
    change 4 * quarterPW (g₀ ∘ cl) (g₁ ∘ cl) (g₂ ∘ cl) (g₃ ∘ cl) ((t : ℝ))
      = 4 * quarterPW g₀ g₁ g₂ g₃ ((t : ℝ))
    congr 1
    refine quarterPW_rel_Icc (P := fun a b _ => a = b)
      (c₀ := g₀) (c₁ := g₁) (c₂ := g₂) (c₃ := g₃)
      ?_ ?_ ?_ ?_ t.2
    · intro u hu
      change g₀ (cl u) = g₀ u
      rw [hclid u hu]
    · intro u hu
      change g₁ (cl u) = g₁ u
      rw [hclid u hu]
    · intro u hu
      change g₂ (cl u) = g₂ u
      rw [hclid u hu]
    · intro u hu
      change g₃ (cl u) = g₃ u
      rw [hclid u hu]
  rw [← hident]
  convert hcount using 3

/-- **First-return extraction**: a continuous curve on a closed interval, locally
injective and returning to an earlier value, has an innermost return pair: two times
with equal values such that the curve is injective on the half-open interval between
them. -/
theorem first_return {f : ℝ → ℂ} {A B : ℝ} (hAB : A < B)
    (hfc : ContinuousOn f (Set.Icc A B))
    (hloc : ∀ t ∈ Set.Icc A B, ∃ δ > 0,
      Set.InjOn f (Set.Icc (t - δ) (t + δ) ∩ Set.Icc A B))
    (hret : f A = f B) :
    ∃ t₀ t₁, A ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ B ∧ f t₀ = f t₁ ∧
      Set.InjOn f (Set.Ico t₀ t₁) := by
  classical
  set U : Set ℝ := {u | u ∈ Set.Icc A B ∧ ∃ t, A ≤ t ∧ t < u ∧ f t = f u} with hUdef
  have hBU : B ∈ U := ⟨⟨hAB.le, le_refl B⟩, A, le_refl A, hAB, hret⟩
  have hUne : U.Nonempty := ⟨B, hBU⟩
  have hUbdd : BddBelow U := ⟨A, fun u hu => hu.1.1⟩
  set t₁ : ℝ := sInf U with ht₁def
  have ht₁A : A ≤ t₁ := le_csInf hUne fun u hu => hu.1.1
  have ht₁B : t₁ ≤ B := csInf_le hUbdd hBU
  have ht₁mem : t₁ ∈ Set.Icc A B := ⟨ht₁A, ht₁B⟩
  obtain ⟨δ₁, hδ₁, hinj₁⟩ := hloc t₁ ht₁mem
  -- a sequence in U approaching the infimum, with its witnesses
  have hseq : ∀ n : ℕ, ∃ u, u ∈ U ∧ u < t₁ + 1/(n+1) := by
    intro n
    obtain ⟨u, huU, hu⟩ := exists_lt_of_csInf_lt hUne
      (show t₁ < t₁ + 1/((n:ℝ)+1) by
        have h0 : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
        linarith)
    exact ⟨u, huU, hu⟩
  choose us hUs hus using hseq
  have husge : ∀ n, t₁ ≤ us n := fun n => csInf_le hUbdd (hUs n)
  have hustend : Filter.Tendsto us Filter.atTop (nhds t₁) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds) ?_ husge (fun n => (hus n).le)
    have h1 : Filter.Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := Filter.Tendsto.add (tendsto_const_nhds (x := t₁)) h1
    simpa using h2
  choose ts htsA htslt hfts using fun n => (hUs n).2
  have htsB : ∀ n, ts n ∈ Set.Icc A B :=
    fun n => ⟨htsA n, (htslt n).le.trans (hUs n).1.2⟩
  obtain ⟨tstar, htstarmem, φ, hφmono, hφtend⟩ :=
    isCompact_Icc.tendsto_subseq htsB
  -- the limit witness has the same value as the infimum time
  have hfeq : f tstar = f t₁ := by
    have h1 : Filter.Tendsto (fun n => f (ts (φ n))) Filter.atTop (nhds (f tstar)) := by
      refine ((hfc tstar htstarmem).tendsto).comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφtend ?_
      exact Filter.Eventually.of_forall fun n => htsB (φ n)
    have h2 : Filter.Tendsto (fun n => f (ts (φ n))) Filter.atTop (nhds (f t₁)) := by
      have h3 : ∀ n, f (ts (φ n)) = f (us (φ n)) := fun n => hfts (φ n)
      rw [show (fun n => f (ts (φ n))) = fun n => f (us (φ n)) from funext h3]
      refine ((hfc t₁ ht₁mem).tendsto).comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hustend.comp hφmono.tendsto_atTop) ?_
      exact Filter.Eventually.of_forall fun n => (hUs (φ n)).1
    exact tendsto_nhds_unique h1 h2
  have htstarle : tstar ≤ t₁ := by
    have h4 : Filter.Tendsto (fun n => us (φ n)) Filter.atTop (nhds t₁) :=
      hustend.comp hφmono.tendsto_atTop
    exact le_of_tendsto_of_tendsto' hφtend h4 fun n => (htslt (φ n)).le
  -- the collapsing case is excluded by local injectivity
  have htstarlt : tstar < t₁ := by
    rcases lt_or_eq_of_le htstarle with h | h
    · exact h
    · exfalso
      have h4 : Filter.Tendsto (fun n => us (φ n)) Filter.atTop (nhds t₁) :=
        hustend.comp hφmono.tendsto_atTop
      have h5 : Filter.Tendsto (fun n => ts (φ n)) Filter.atTop (nhds t₁) := by
        rw [h] at hφtend
        exact hφtend
      have h6 : ∀ᶠ n in Filter.atTop, |us (φ n) - t₁| < δ₁ := by
        have := Metric.tendsto_nhds.mp h4 δ₁ hδ₁
        simpa [Real.dist_eq] using this
      have h7 : ∀ᶠ n in Filter.atTop, |ts (φ n) - t₁| < δ₁ := by
        have := Metric.tendsto_nhds.mp h5 δ₁ hδ₁
        simpa [Real.dist_eq] using this
      obtain ⟨n, hn6, hn7⟩ := (h6.and h7).exists
      have habs6 := abs_lt.mp hn6
      have habs7 := abs_lt.mp hn7
      have hwin1 : ts (φ n) ∈ Set.Icc (t₁ - δ₁) (t₁ + δ₁) ∩ Set.Icc A B :=
        ⟨⟨by linarith [habs7.1], by linarith [habs7.2]⟩, htsB (φ n)⟩
      have hwin2 : us (φ n) ∈ Set.Icc (t₁ - δ₁) (t₁ + δ₁) ∩ Set.Icc A B :=
        ⟨⟨by linarith [habs6.1], by linarith [habs6.2]⟩, (hUs (φ n)).1⟩
      exact absurd (hinj₁ hwin1 hwin2 (hfts (φ n))) (ne_of_lt (htslt (φ n)))
  -- hence the infimum time is attained as a genuine return
  have ht₁U : t₁ ∈ U := ⟨ht₁mem, tstar, htstarmem.1, htstarlt, hfeq⟩
  -- the last previous visit of the return value
  set V : Set ℝ := {t | A ≤ t ∧ t < t₁ ∧ f t = f t₁} with hVdef
  have hVne : V.Nonempty := ⟨tstar, htstarmem.1, htstarlt, hfeq⟩
  have hVbdd : BddAbove V := ⟨t₁, fun v hv => hv.2.1.le⟩
  set t₀ : ℝ := sSup V with ht₀def
  have htstarV : tstar ∈ V := ⟨htstarmem.1, htstarlt, hfeq⟩
  have ht₀A : A ≤ t₀ := le_trans htstarmem.1 (le_csSup hVbdd htstarV)
  have ht₀le : t₀ ≤ t₁ := csSup_le hVne fun v hv => hv.2.1.le
  -- a sequence in V approaching the supremum
  have hseqV : ∀ n : ℕ, ∃ v, v ∈ V ∧ t₀ - 1/(n+1) < v := by
    intro n
    obtain ⟨v, hvV, hv⟩ := exists_lt_of_lt_csSup hVne
      (show t₀ - 1/((n:ℝ)+1) < t₀ by
        have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
        linarith)
    exact ⟨v, hvV, hv⟩
  choose vs hVs hvs using hseqV
  have hvsle : ∀ n, vs n ≤ t₀ := fun n => le_csSup hVbdd (hVs n)
  have hvstend : Filter.Tendsto vs Filter.atTop (nhds t₀) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      ?_ tendsto_const_nhds (fun n => (hvs n).le) hvsle
    have h1 : Filter.Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := Filter.Tendsto.sub (tendsto_const_nhds (x := t₀)) h1
    simpa using h2
  have hvsmem : ∀ n, vs n ∈ Set.Icc A B :=
    fun n => ⟨(hVs n).1, (hVs n).2.1.le.trans ht₁B⟩
  have ht₀mem : t₀ ∈ Set.Icc A B :=
    ⟨ht₀A, ht₀le.trans ht₁B⟩
  have hft₀ : f t₀ = f t₁ := by
    have h1 : Filter.Tendsto (fun n => f (vs n)) Filter.atTop (nhds (f t₀)) := by
      refine ((hfc t₀ ht₀mem).tendsto).comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hvstend ?_
      exact Filter.Eventually.of_forall hvsmem
    have h2 : Filter.Tendsto (fun n => f (vs n)) Filter.atTop (nhds (f t₁)) := by
      rw [show (fun n => f (vs n)) = fun _ => f t₁ from funext fun n => (hVs n).2.2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have ht₀lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₀le with h | h
    · exact h
    · exfalso
      have h5 : Filter.Tendsto vs Filter.atTop (nhds t₁) := h ▸ hvstend
      have h7 : ∀ᶠ n in Filter.atTop, |vs n - t₁| < δ₁ := by
        have := Metric.tendsto_nhds.mp h5 δ₁ hδ₁
        simpa [Real.dist_eq] using this
      obtain ⟨n, hn⟩ := h7.exists
      have habs := abs_lt.mp hn
      have hwin1 : vs n ∈ Set.Icc (t₁ - δ₁) (t₁ + δ₁) ∩ Set.Icc A B :=
        ⟨⟨by linarith [habs.1], by linarith [habs.2]⟩, hvsmem n⟩
      have hwin2 : t₁ ∈ Set.Icc (t₁ - δ₁) (t₁ + δ₁) ∩ Set.Icc A B :=
        ⟨⟨by linarith, by linarith⟩, ht₁mem⟩
      exact absurd (hinj₁ hwin1 hwin2 (hVs n).2.2) (ne_of_lt (hVs n).2.1)
  refine ⟨t₀, t₁, ht₀A, ht₀lt, ht₁B, hft₀, ?_⟩
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exfalso
    have hyU : y ∈ U := ⟨⟨ht₀A.trans hy.1, hy.2.le.trans ht₁B⟩, x,
      ht₀A.trans hx.1, h, hxy⟩
    exact absurd (csInf_le hUbdd hyU) (not_le.mpr hy.2)
  · exact h
  · exfalso
    have hxU : x ∈ U := ⟨⟨ht₀A.trans hx.1, hx.2.le.trans ht₁B⟩, y,
      ht₀A.trans hy.1, h, hxy.symm⟩
    exact absurd (csInf_le hUbdd hxU) (not_le.mpr hx.2)

/-- **Local injectivity of trajectories**: around every time of its domain, a
trajectory is injective on a metric window intersected with the domain, by the affine
chart development. -/
theorem traj_locally_injective {q : ℂ → ℂ} {γ : ℝ → ℂ} {s : Set ℝ}
    (hγ : IsTrajOn q γ s) :
    ∀ t ∈ s, ∃ δ > 0, Set.InjOn γ (Set.Icc (t - δ) (t + δ) ∩ s) := by
  intro t ht
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hγ.chart t ht
  rw [Filter.eventually_iff] at hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨ε / 2, by positivity, ?_⟩
  intro u hu u' hu' heq
  have hmem : ∀ v : ℝ, v ∈ Set.Icc (t - ε/2) (t + ε/2) ∩ s →
      γ v ∈ U ∧ Φ (γ v) = Φ (γ t) + ((v - t : ℝ) : ℂ) := by
    intro v hv
    refine hball ⟨?_, hv.2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hv.1.1]
    · linarith [hv.1.2]
  have h1 := (hmem u hu).2
  have h2 := (hmem u' hu').2
  rw [heq] at h1
  rw [h1] at h2
  have h3 : ((u - t : ℝ) : ℂ) = ((u' - t : ℝ) : ℂ) := add_left_cancel h2
  have h4 : u - t = u' - t := by exact_mod_cast h3
  linarith

/-- **Local corner disjointness**: near a perpendicular corner where a horizontal
trajectory ends and a transverse leaf begins, the two arcs meet only at the corner:
in the corner chart one develops horizontally and the other vertically. -/
theorem corner_locally_disjoint {q : ℂ → ℂ} {γ τ : ℝ → ℂ} {sγ sτ : Set ℝ}
    {T η₀ : ℝ} (hγ : IsTrajOn q γ sγ) (hT : T ∈ sγ)
    (hτ : IsTrajOn (fun z => -q z) τ sτ) (hη₀ : 0 < η₀)
    (hsub : Set.Icc (-η₀) η₀ ⊆ sτ)
    (hcorner : τ 0 = γ T) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (T - δ) (T + δ) ∩ sγ, ∀ u ∈ Set.Icc (-δ) δ,
      γ t = τ u → t = T ∧ u = 0 := by
  obtain ⟨U, hUo, hpU, hUH, hUne, Φ, hΦd, hΦinj, hΦsq, hev⟩ := hγ.chart T hT
  rw [Filter.eventually_iff] at hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  -- a symmetric window on which the leaf stays in the chart
  have hτc : ContinuousWithinAt τ sτ 0 := hτ.cont 0 (hsub ⟨by linarith, hη₀.le⟩)
  have hτ0U : τ 0 ∈ U := by
    rw [hcorner]
    exact hpU
  obtain ⟨η₁, hη₁, hballτ⟩ := Metric.mem_nhdsWithin_iff.mp (hτc (hUo.mem_nhds hτ0U))
  set η : ℝ := min (min (η₁ / 2) η₀) 1 with hηdef
  have hη : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min (by positivity) hη₀) one_pos
  have hηη₀ : η ≤ η₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hηsub : Set.Icc (-η) η ⊆ sτ :=
    fun u hu => hsub ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have htrackU : ∀ u ∈ Set.Icc (-η) η, τ u ∈ U := by
    intro u hu
    refine hballτ ⟨?_, hηsub hu⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 : η ≤ η₁ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    constructor
    · linarith [hu.1]
    · linarith [hu.2]
  -- the leaf development on the window
  have hre := horizontal_re_const hUo hΦd hΦsq hτ
    (by linarith : -η ≤ η) hηsub htrackU
  obtain ⟨εs, hεs, him⟩ := horizontal_im_advance hUo hΦd hΦsq hτ
    (by linarith : -η ≤ η) hηsub htrackU
  have h0win : (0:ℝ) ∈ Set.Icc (-η) η := ⟨by linarith, hη.le⟩
  refine ⟨min η (ε / 2), lt_min hη (by positivity), ?_⟩
  rintro t ⟨htw, hts⟩ u huw heq
  have hδη : min η (ε / 2) ≤ η := min_le_left _ _
  have hδε : min η (ε / 2) ≤ ε / 2 := min_le_right _ _
  have huη : u ∈ Set.Icc (-η) η :=
    ⟨by linarith [huw.1], by linarith [huw.2]⟩
  -- the arc development at t
  have hσdev : γ t ∈ U ∧ Φ (γ t) = Φ (γ T) + ((t - T : ℝ) : ℂ) := by
    refine hball ⟨?_, hts⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [htw.1]
    · linarith [htw.2]
  -- compare the developments through the corner value
  have hΦeq : Φ (γ t) = Φ (τ u) := by rw [heq]
  have hre_u := hre u huη
  have hre_0 := hre 0 h0win
  have him_u := him u huη
  have him_0 := him 0 h0win
  -- real parts pin the arc time
  have hret : (Φ (γ t)).re = (Φ (γ T)).re := by
    rw [hΦeq, hre_u, ← hre_0, hcorner]
  have ht_eq : t = T := by
    have h1 : (Φ (γ T) + ((t - T : ℝ) : ℂ)).re = (Φ (γ T)).re + (t - T) := by
      rw [Complex.add_re, Complex.ofReal_re]
    rw [hσdev.2, h1] at hret
    linarith
  -- imaginary parts pin the leaf time
  have himt : (Φ (γ t)).im = (Φ (γ T)).im := by
    have h1 : (Φ (γ T) + ((t - T : ℝ) : ℂ)).im = (Φ (γ T)).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
    rw [hσdev.2, h1]
  have hu_eq : u = 0 := by
    have h2 : (Φ (τ u)).im = (Φ (τ 0)).im := by
      rw [← hΦeq, himt, hcorner]
    rw [him_u, him_0] at h2
    have hεne : εs ≠ 0 := by
      rcases hεs with h | h <;> rw [h] <;> norm_num
    have h3 : εs * (u - -η) = εs * (0 - -η) := by linarith
    have h4 := mul_left_cancel₀ hεne h3
    linarith
  exact ⟨ht_eq, hu_eq⟩

/-- The concatenated bigon loop: the horizontal arc, then the shifted transverse
arc. -/
noncomputable def bigonLoop (γ τ : ℝ → ℂ) (T : ℝ) : ℝ → ℂ := fun x =>
  if x ≤ T then γ x else τ (x - T)

/-- Values of the concatenated loop on and beyond the junction agree with the shifted
transverse arc, given the corner identification. -/
theorem bigonLoop_ge {γ τ : ℝ → ℂ} {T : ℝ} (hcorner : τ 0 = γ T)
    {x : ℝ} (hx : T ≤ x) : bigonLoop γ τ T x = τ (x - T) := by
  unfold bigonLoop
  rcases eq_or_lt_of_le hx with h | h
  · rw [if_pos h.symm.le, ← h, sub_self, hcorner]
  · rw [if_neg (not_le.mpr h)]

end WindingBricks

end RiemannDynamics
