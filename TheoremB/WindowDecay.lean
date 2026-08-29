/-
# The window-decay iteration (Tier 7, wave W-R2b)

The engine Tier 7 needs and Mathlib does not have: exponential decay
extracted from a WINDOW INTEGRAL INEQUALITY, with no differentiability
anywhere.

Three routes were checked before this one (rung9 blueprint, design fact
3). A decaying sibling of `gronwall_const_source` fails: its
integrating-factor step needs FTC on the source's primitive, hence
continuity of the source, and this campaign only ever proves its tail
sources INTEGRABLE, deliberately. The Phi-trick of `theorem_B_unique`
fails: it works because the integral enters with a `+` sign, and at a
negative rate an upper bound on the primitive is useless. What survives
is discrete: subdivide the window, use the inequality on each step, and
close with `(1 + x/n)^n → exp x`.

The mechanism, on one step `[s, u]` of length `Δ`:
* the window inequality plus `e ≥ 0` gives near-monotonicity,
  `e u ≤ e r + A·Δ` for every `r` in the step;
* so the integral is bounded below by `Δ·(e u − A·Δ)`, a constant
  minorant - this is the step that needs no derivative;
* feeding that back gives `e u ≤ e s/(1 + cΔ) + A·Δ`, and the induction
  `a_i ≤ a_0/(1+cΔ)^i + A(1+cΔ)/c` closes with EQUALITY in its
  algebraic side condition, which is why no slack accumulates.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace TheoremB

open Set

/-- **W-R2b.** A nonnegative function obeying the window inequality
`e t + c·∫_{t₀}^{t} e ≤ e t₀ + A·(t − t₀)` on every subwindow decays
exponentially at rate `c` down to the floor `A/c`.

No differentiability, no continuity: interval integrability on
subwindows is the only regularity used.

`_hT` is retained for interface stability and is not consumed: when
`T < 0` the window `Icc 0 T` is empty and the conclusion is vacuous, so
the hypothesis only weakens the lemma. Same situation the Tier-5 audit
recorded for `mode_equation_of_weak`. -/
theorem decay_of_window_integral_ineq {e : ℝ → ℝ} {c A T : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (_hT : 0 ≤ T)
    (hnn : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ e t)
    (hint : ∀ t₀ ∈ Icc (0:ℝ) T, ∀ t ∈ Icc t₀ T,
      IntervalIntegrable e MeasureTheory.volume t₀ t)
    (hwin : ∀ t₀ ∈ Icc (0:ℝ) T, ∀ t ∈ Icc t₀ T,
      e t + c * (∫ s in t₀..t, e s) ≤ e t₀ + A * (t - t₀)) :
    ∀ t ∈ Icc (0:ℝ) T, e t ≤ e 0 * Real.exp (-(c * t)) + A / c := by
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have hAc : 0 ≤ A / c := div_nonneg hA hc.le
  -- STEP 1: near-monotonicity, from nonnegativity of the integral
  have hmono : ∀ s ∈ Icc (0:ℝ) T, ∀ u ∈ Icc s T, e u ≤ e s + A * (u - s) := by
    intro s hs u hu
    have hsu : s ≤ u := hu.1
    have hint0 : (0:ℝ) ≤ ∫ r in s..u, e r := by
      refine intervalIntegral.integral_nonneg hsu fun r hr => ?_
      exact hnn r ⟨le_trans hs.1 hr.1, le_trans hr.2 hu.2⟩
    have h := hwin s hs u hu
    nlinarith
  -- STEP 2: one step of the iteration
  have hstep : ∀ s ∈ Icc (0:ℝ) T, ∀ u ∈ Icc s T,
      e u ≤ e s / (1 + c * (u - s)) + A * (u - s) := by
    intro s hs u hu
    have hsu : s ≤ u := hu.1
    have hd : (0:ℝ) ≤ u - s := by linarith
    have hpos : 0 < 1 + c * (u - s) := by nlinarith
    -- the constant minorant on the step
    have hlow : ∀ r ∈ Icc s u, e u - A * (u - s) ≤ e r := by
      intro r hr
      have hrIcc : r ∈ Icc (0:ℝ) T :=
        ⟨le_trans hs.1 hr.1, le_trans hr.2 hu.2⟩
      have h := hmono r hrIcc u ⟨hr.2, hu.2⟩
      have : A * (u - r) ≤ A * (u - s) :=
        mul_le_mul_of_nonneg_left (by linarith [hr.1]) hA
      linarith
    have hIconst : IntervalIntegrable (fun _ : ℝ => e u - A * (u - s))
        MeasureTheory.volume s u := intervalIntegrable_const
    have hIe : IntervalIntegrable e MeasureTheory.volume s u := hint s hs u hu
    have hge : (u - s) * (e u - A * (u - s)) ≤ ∫ r in s..u, e r := by
      have hmi := intervalIntegral.integral_mono_on hsu hIconst hIe hlow
      rwa [intervalIntegral.integral_const, smul_eq_mul] at hmi
    have h := hwin s hs u hu
    -- e u * (1 + cΔ) ≤ e s + AΔ(1 + cΔ)
    have hkey : e u * (1 + c * (u - s)) ≤ e s + A * (u - s) * (1 + c * (u - s)) := by
      nlinarith
    rw [div_add' _ _ _ (ne_of_gt hpos), le_div_iff₀ hpos]
    nlinarith
  -- STEP 3: the n-step induction, at grid spacing Δ = t/n
  have hgrid : ∀ n : ℕ, 0 < n →
      e t ≤ e 0 / (1 + c * (t / (n:ℝ))) ^ n + A * (1 + c * (t / (n:ℝ))) / c := by
    intro n hn
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    set Δ : ℝ := t / (n:ℝ) with hΔ
    have hΔ0 : 0 ≤ Δ := div_nonneg ht0 hnR.le
    have hpos : 0 < 1 + c * Δ := by nlinarith
    set B : ℝ := A * (1 + c * Δ) / c with hB
    have hB0 : 0 ≤ B := by positivity
    -- the grid points stay inside the window
    have hmem : ∀ i : ℕ, i ≤ n → (i:ℝ) * Δ ∈ Icc (0:ℝ) T := by
      intro i hi
      refine ⟨by positivity, ?_⟩
      have h1 : (i:ℝ) ≤ (n:ℝ) := by exact_mod_cast hi
      have h2 : (i:ℝ) * Δ ≤ (n:ℝ) * Δ := mul_le_mul_of_nonneg_right h1 hΔ0
      have h3 : (n:ℝ) * Δ = t := by
        rw [hΔ]; field_simp
      linarith [h3 ▸ h2]
    -- the induction
    have hind : ∀ i : ℕ, i ≤ n →
        e ((i:ℝ) * Δ) ≤ e 0 / (1 + c * Δ) ^ i + B := by
      intro i
      induction i with
      | zero =>
        intro _
        simp only [Nat.cast_zero, zero_mul, pow_zero, div_one]
        linarith
      | succ j ih =>
        intro hj
        have hjn : j ≤ n := Nat.le_of_succ_le hj
        have hIH := ih hjn
        have hjmem := hmem j hjn
        have hj1mem := hmem (j + 1) hj
        have hle : (j:ℝ) * Δ ≤ ((j:ℝ) + 1) * Δ := by nlinarith
        have hstep' := hstep ((j:ℝ) * Δ) hjmem (((j:ℝ) + 1) * Δ)
          ⟨hle, by push_cast at hj1mem; linarith [hj1mem.2]⟩
        have hdiff : ((j:ℝ) + 1) * Δ - (j:ℝ) * Δ = Δ := by ring
        rw [hdiff] at hstep'
        have hcast : ((j + 1 : ℕ) : ℝ) * Δ = ((j:ℝ) + 1) * Δ := by push_cast; ring
        rw [hcast]
        -- a_{j+1} ≤ a_j/(1+cΔ) + AΔ ≤ e0/(1+cΔ)^{j+1} + B
        have hdiv : e ((j:ℝ) * Δ) / (1 + c * Δ) ≤
            (e 0 / (1 + c * Δ) ^ j + B) / (1 + c * Δ) :=
          div_le_div_of_nonneg_right hIH hpos.le
        have hexp : (e 0 / (1 + c * Δ) ^ j + B) / (1 + c * Δ) =
            e 0 / (1 + c * Δ) ^ (j + 1) + B / (1 + c * Δ) := by
          field_simp
          ring
        have hBstep : B / (1 + c * Δ) + A * Δ = B := by
          have hcne : c ≠ 0 := ne_of_gt hc
          have hpne : (1 + c * Δ) ≠ 0 := ne_of_gt hpos
          rw [hB]
          field_simp
        calc e (((j:ℝ) + 1) * Δ)
            ≤ e ((j:ℝ) * Δ) / (1 + c * Δ) + A * Δ := hstep'
          _ ≤ (e 0 / (1 + c * Δ) ^ j + B) / (1 + c * Δ) + A * Δ := by linarith
          _ = e 0 / (1 + c * Δ) ^ (j + 1) + (B / (1 + c * Δ) + A * Δ) := by
              rw [hexp]; ring
          _ ≤ e 0 / (1 + c * Δ) ^ (j + 1) + B := by linarith
    have hfin := hind n le_rfl
    have hnΔ : (n:ℝ) * Δ = t := by rw [hΔ]; field_simp
    rwa [hnΔ] at hfin
  -- STEP 4: pass to the limit in n
  have hlim : Filter.Tendsto
      (fun n : ℕ => e 0 / (1 + c * t / (n:ℝ)) ^ n + A * (1 + c * t / (n:ℝ)) / c)
      Filter.atTop (nhds (e 0 * Real.exp (-(c * t)) + A / c)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 + c * t / (n:ℝ)) ^ n)
        Filter.atTop (nhds (Real.exp (c * t))) :=
      Real.tendsto_one_add_div_pow_exp (c * t)
    have h2 : Filter.Tendsto (fun n : ℕ => e 0 / (1 + c * t / (n:ℝ)) ^ n)
        Filter.atTop (nhds (e 0 / Real.exp (c * t))) :=
      Filter.Tendsto.div tendsto_const_nhds h1 (Real.exp_ne_zero _)
    have h3 : Filter.Tendsto (fun n : ℕ => c * t / (n:ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h4 : Filter.Tendsto (fun n : ℕ => A * (1 + c * t / (n:ℝ)) / c)
        Filter.atTop (nhds (A / c)) := by
      have h5 : Filter.Tendsto (fun n : ℕ => A * (1 + c * t / (n:ℝ)) / c)
          Filter.atTop (nhds (A * (1 + 0) / c)) :=
        ((tendsto_const_nhds.mul (tendsto_const_nhds.add h3)).div_const c)
      simpa using h5
    have h6 : e 0 / Real.exp (c * t) = e 0 * Real.exp (-(c * t)) := by
      rw [Real.exp_neg]
      field_simp
    rw [← h6]
    exact h2.add h4
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h := hgrid n hn
  have hrw : c * (t / (n:ℝ)) = c * t / (n:ℝ) := by ring
  rwa [hrw] at h

end TheoremB
