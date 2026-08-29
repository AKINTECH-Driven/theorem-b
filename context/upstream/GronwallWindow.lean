/-
Copyright (c) 2026 Konstantinos Tsantakos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Konstantinos Tsantakos
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A derivative-free Grönwall inequality at a negative rate

`le_gronwallBound_of_window_integral_le` states that a nonnegative `f : ℝ → ℝ`
satisfying the *window* inequality

  `f y + c * ∫ t in x..y, f t ≤ f x + A * (y - x)`   for all `0 ≤ x ≤ y ≤ b`

obeys `f x ≤ gronwallBound (f 0) (-c) A x`, i.e. it decays exponentially at rate
`c > 0` down to the floor `A / c`.

Unlike the existing Grönwall family in `Mathlib/Analysis/ODE/Gronwall.lean`, this
needs **no differentiability of `f` at all** — only interval integrability on
subwindows. It is therefore applicable when `f` arises as a limit of smooth
approximants and only an integrated inequality survives the limit, which is the
typical situation for energy functionals of PDE.

This addresses, from a different angle, the TODO recorded in
`Mathlib/Analysis/ODE/Gronwall.lean`: it is a Grönwall bound at a rate of
arbitrary sign (here strictly negative), and it dispenses with the derivative
hypothesis entirely rather than weakening it to a `liminf`.

## Proof

Discrete. On one step `[x, y]` of length `Δ`, nonnegativity of `f` turns the
window inequality into the near-monotonicity `f y ≤ f t + A * Δ` for every `t` in
the step, so the integral has the *constant* minorant `Δ * (f y - A * Δ)` — the
step that would otherwise need a derivative. Feeding that back gives
`f y ≤ f x / (1 + c * Δ) + A * Δ`, and the induction

  `f (i * Δ) ≤ f 0 / (1 + c * Δ) ^ i + B * (1 - 1 / (1 + c * Δ) ^ i)`,
  `B := A * (1 + c * Δ) / c`

closes with *equality* in its algebraic side condition `B / (1 + c * Δ) + A * Δ = B`,
so no slack accumulates over the `n` steps. Letting `Δ = x / n` and `n → ∞`,
`(1 + c * x / n) ^ n → exp (c * x)` gives the bound.
-/

open Set MeasureTheory
open scoped Topology

/-- A nonnegative function obeying a window integral inequality with rate `c > 0`
and source `A ≥ 0` is bounded by `gronwallBound (f 0) (-c) A`: it decays
exponentially at rate `c` down to the floor `A / c`.

No differentiability is assumed; interval integrability on subwindows is the only
regularity used. -/
theorem le_gronwallBound_of_window_integral_le {f : ℝ → ℝ} {c A b : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A)
    (hf : ∀ x ∈ Icc (0:ℝ) b, 0 ≤ f x)
    (hint : ∀ x ∈ Icc (0:ℝ) b, ∀ y ∈ Icc x b, IntervalIntegrable f volume x y)
    (hle : ∀ x ∈ Icc (0:ℝ) b, ∀ y ∈ Icc x b,
      f y + c * (∫ t in x..y, f t) ≤ f x + A * (y - x)) :
    ∀ x ∈ Icc (0:ℝ) b, f x ≤ gronwallBound (f 0) (-c) A x := by
  intro x hx
  obtain ⟨hx0, hxb⟩ := hx
  have hcne : (-c) ≠ 0 := by simpa using ne_of_gt hc
  rw [gronwallBound_of_K_ne_0 hcne]
  -- near-monotonicity, from nonnegativity of the integral
  have hmono : ∀ u ∈ Icc (0:ℝ) b, ∀ v ∈ Icc u b, f v ≤ f u + A * (v - u) := by
    intro u hu v hv
    have hint0 : (0:ℝ) ≤ ∫ t in u..v, f t := by
      refine intervalIntegral.integral_nonneg hv.1 fun t ht => ?_
      exact hf t ⟨le_trans hu.1 ht.1, le_trans ht.2 hv.2⟩
    have h := hle u hu v hv
    nlinarith
  -- one step of the iteration
  have hstep : ∀ u ∈ Icc (0:ℝ) b, ∀ v ∈ Icc u b,
      f v ≤ f u / (1 + c * (v - u)) + A * (v - u) := by
    intro u hu v hv
    have huv : u ≤ v := hv.1
    have hd : (0:ℝ) ≤ v - u := by linarith
    have hpos : 0 < 1 + c * (v - u) := by nlinarith
    have hlow : ∀ t ∈ Icc u v, f v - A * (v - u) ≤ f t := by
      intro t ht
      have htIcc : t ∈ Icc (0:ℝ) b := ⟨le_trans hu.1 ht.1, le_trans ht.2 hv.2⟩
      have h := hmono t htIcc v ⟨ht.2, hv.2⟩
      have hA' : A * (v - t) ≤ A * (v - u) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.1]) hA
      linarith
    have hge : (v - u) * (f v - A * (v - u)) ≤ ∫ t in u..v, f t := by
      have hmi := intervalIntegral.integral_mono_on huv intervalIntegrable_const
        (hint u hu v hv) hlow
      rwa [intervalIntegral.integral_const, smul_eq_mul] at hmi
    have h := hle u hu v hv
    rw [div_add' _ _ _ (ne_of_gt hpos), le_div_iff₀ hpos]
    nlinarith
  -- the n-step induction at grid spacing Δ = x / n
  have hgrid : ∀ n : ℕ, 0 < n →
      f x ≤ f 0 / (1 + c * (x / (n:ℝ))) ^ n +
        A * (1 + c * (x / (n:ℝ))) / c *
          (1 - 1 / (1 + c * (x / (n:ℝ))) ^ n) := by
    intro n hn
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    set Δ : ℝ := x / (n:ℝ) with hΔ
    have hΔ0 : 0 ≤ Δ := div_nonneg hx0 hnR.le
    have hpos : 0 < 1 + c * Δ := by nlinarith
    set B : ℝ := A * (1 + c * Δ) / c with hB
    have hBstep : B / (1 + c * Δ) + A * Δ = B := by
      have hcne' : c ≠ 0 := ne_of_gt hc
      have hpne : (1 + c * Δ) ≠ 0 := ne_of_gt hpos
      rw [hB]
      field_simp
    have hmem : ∀ i : ℕ, i ≤ n → (i:ℝ) * Δ ∈ Icc (0:ℝ) b := by
      intro i hi
      refine ⟨by positivity, ?_⟩
      have h1 : (i:ℝ) ≤ (n:ℝ) := by exact_mod_cast hi
      have h2 : (i:ℝ) * Δ ≤ (n:ℝ) * Δ := mul_le_mul_of_nonneg_right h1 hΔ0
      have h3 : (n:ℝ) * Δ = x := by rw [hΔ]; field_simp
      rw [h3] at h2
      linarith
    have hind : ∀ i : ℕ, i ≤ n →
        f ((i:ℝ) * Δ) ≤ f 0 / (1 + c * Δ) ^ i + B * (1 - 1 / (1 + c * Δ) ^ i) := by
      intro i
      induction i with
      | zero =>
        intro _
        simp only [Nat.cast_zero, zero_mul, pow_zero, div_one]
        norm_num
      | succ j ih =>
        intro hj
        have hjn : j ≤ n := Nat.le_of_succ_le hj
        have hIH := ih hjn
        have hjmem := hmem j hjn
        have hj1mem := hmem (j + 1) hj
        have hle' : (j:ℝ) * Δ ≤ ((j:ℝ) + 1) * Δ := by nlinarith
        have hstep' := hstep ((j:ℝ) * Δ) hjmem (((j:ℝ) + 1) * Δ)
          ⟨hle', by push_cast at hj1mem; linarith [hj1mem.2]⟩
        have hdiff : ((j:ℝ) + 1) * Δ - (j:ℝ) * Δ = Δ := by ring
        rw [hdiff] at hstep'
        have hcast : ((j + 1 : ℕ) : ℝ) * Δ = ((j:ℝ) + 1) * Δ := by push_cast; ring
        rw [hcast]
        have hdiv : f ((j:ℝ) * Δ) / (1 + c * Δ) ≤
            (f 0 / (1 + c * Δ) ^ j + B * (1 - 1 / (1 + c * Δ) ^ j)) / (1 + c * Δ) :=
          div_le_div_of_nonneg_right hIH hpos.le
        have hexp : (f 0 / (1 + c * Δ) ^ j + B * (1 - 1 / (1 + c * Δ) ^ j))
              / (1 + c * Δ)
            = f 0 / (1 + c * Δ) ^ (j + 1) +
              (B / (1 + c * Δ) - B / (1 + c * Δ) ^ (j + 1)) := by
          have hpne : (1 + c * Δ) ≠ 0 := ne_of_gt hpos
          field_simp
          ring
        calc f (((j:ℝ) + 1) * Δ)
            ≤ f ((j:ℝ) * Δ) / (1 + c * Δ) + A * Δ := hstep'
          _ ≤ (f 0 / (1 + c * Δ) ^ j + B * (1 - 1 / (1 + c * Δ) ^ j)) / (1 + c * Δ)
                + A * Δ := by linarith
          _ = f 0 / (1 + c * Δ) ^ (j + 1) +
                ((B / (1 + c * Δ) + A * Δ) - B / (1 + c * Δ) ^ (j + 1)) := by
              rw [hexp]; ring
          _ = f 0 / (1 + c * Δ) ^ (j + 1) +
                B * (1 - 1 / (1 + c * Δ) ^ (j + 1)) := by
              rw [hBstep]
              have hpne : (1 + c * Δ) ≠ 0 := ne_of_gt hpos
              field_simp
    have hfin := hind n le_rfl
    have hnΔ : (n:ℝ) * Δ = x := by rw [hΔ]; field_simp
    rwa [hnΔ] at hfin
  -- pass to the limit
  have hP : Filter.Tendsto (fun n : ℕ => (1 + c * x / (n:ℝ)) ^ n)
      Filter.atTop (𝓝 (Real.exp (c * x))) := Real.tendsto_one_add_div_pow_exp (c * x)
  have hPne : Real.exp (c * x) ≠ 0 := Real.exp_ne_zero _
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / (1 + c * x / (n:ℝ)) ^ n)
      Filter.atTop (𝓝 (1 / Real.exp (c * x))) :=
    Filter.Tendsto.div tendsto_const_nhds hP hPne
  have hd0 : Filter.Tendsto (fun n : ℕ => c * x / (n:ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim : Filter.Tendsto
      (fun n : ℕ => f 0 / (1 + c * x / (n:ℝ)) ^ n +
        A * (1 + c * x / (n:ℝ)) / c * (1 - 1 / (1 + c * x / (n:ℝ)) ^ n))
      Filter.atTop
      (𝓝 (f 0 * Real.exp (-c * x) + A / (-c) * (Real.exp (-c * x) - 1))) := by
    have h1 : Filter.Tendsto (fun n : ℕ => f 0 / (1 + c * x / (n:ℝ)) ^ n)
        Filter.atTop (𝓝 (f 0 / Real.exp (c * x))) :=
      Filter.Tendsto.div tendsto_const_nhds hP hPne
    have h2 : Filter.Tendsto (fun n : ℕ => A * (1 + c * x / (n:ℝ)) / c)
        Filter.atTop (𝓝 (A / c)) := by
      have h3 : Filter.Tendsto (fun n : ℕ => A * (1 + c * x / (n:ℝ)) / c)
          Filter.atTop (𝓝 (A * (1 + 0) / c)) :=
        ((tendsto_const_nhds.mul (tendsto_const_nhds.add hd0)).div_const c)
      simpa using h3
    have h4 : Filter.Tendsto (fun n : ℕ => 1 - 1 / (1 + c * x / (n:ℝ)) ^ n)
        Filter.atTop (𝓝 (1 - 1 / Real.exp (c * x))) :=
      tendsto_const_nhds.sub hinv
    have h5 := h1.add (h2.mul h4)
    have heq : f 0 / Real.exp (c * x) + A / c * (1 - 1 / Real.exp (c * x))
        = f 0 * Real.exp (-c * x) + A / (-c) * (Real.exp (-c * x) - 1) := by
      rw [show (-c * x) = -(c * x) by ring, Real.exp_neg]
      field_simp
      ring
    rwa [heq] at h5
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h := hgrid n hn
  have hrw : c * (x / (n:ℝ)) = c * x / (n:ℝ) := by ring
  rwa [hrw] at h
