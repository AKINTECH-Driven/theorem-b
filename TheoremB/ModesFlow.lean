/-
# Determining modes along the eternal flows (Tier 7, wave W-R5)

`ns_full_global_flow_modes`: the sentence "the small-data trap dissolves
the 3D conditionality of determining modes", compiled.

`theorem_B_modes` is stated on an abstract class: two flows on a window
`[0, T]` with energy and enstrophy budgets `(E, Z)`, mean-zero,
divergence-free, solving the integral equation. Its hypotheses are the
CONDITIONAL part of the classical 3D determining-modes theory (enstrophy
bounded along the flow is exactly what 3D regularity would give). The
small-data trap of `ns_full_global_flow` supplies those bounds for free
and forever: the eternal flow of every small datum stays in
`en ≤ en c₀`, `ens ≤ ens c₀` on the whole half line. So two small data,
each with its OWN smallness, give two eternal flows that inhabit the
class on EVERY window at the budgets `E := max (en c₀) (en c₀')`,
`Z := max (ens c₀) (ens c₀')`, and the determining-modes estimate holds
between them with no conditional hypothesis left.

Read the quantifier order. `K` is obtained ONCE, from `theorem_B_modes`
at `(ν, E, Z)`, BEFORE the flows are extracted and before any horizon,
tolerance, or mode count is chosen: the statement reads `∃ K` ahead of
`∃ c c'` and ahead of `∀ T`. It is one constant for the pair of data,
uniform across horizons, depending only on `(ν, E, Z)`.

`theorem_B_modes` needs `c t 0 = 0` at every time, which
`ns_full_global_flow` does NOT export. It is derived here
(`mean_zero_along_flow`), not assumed: the `k = 0` integral equation has
a vanishing source, since the full convection annihilates the zero mode
of a divergence-free field, `freq 0 = 0`, and the Leray projection fixes
`0`. The clause is exported for both flows.

Every clause of `ns_full_global_flow` is quoted verbatim for both flows,
so the statement is self-contained: the pair it speaks about is
recognisably THE pair of eternal flows, and nothing is abbreviated.
-/
import TheoremB.DeterminingModes

namespace TheoremB

open Set

/-- The zero lattice point has zero frequency. -/
private lemma freq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [freq]

/-- **Mean-zero propagates along any flow of `ns_full_global_flow`'s
class.** The `k = 0` integral equation has a vanishing source: the full
convection annihilates the zero mode of a divergence-free field
(`convFull_zero_of_divFree`), `freq 0 = 0` kills the dissipation, and
the Leray projection fixes `0`. `ns_full_global_flow` does not export
this clause; it is derived, not assumed. -/
theorem mean_zero_along_flow {ν : ℝ} {c₀ : (Fin 3 → ℤ) → Vel}
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hmean0 : c₀ 0 = 0)
    (hcdiv : ∀ t ∈ Ici (0:ℝ), DivFree (c t))
    (hinteq : ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) :
    ∀ t ∈ Ici (0:ℝ), c t 0 = 0 := by
  intro t ht
  have hEqOn : EqOn (fun s => (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0
      + lerayProj (0 : Fin 3 → ℤ) (convFull (c s) 0)) (fun _ => (0 : Vel))
      (uIcc (0:ℝ) t) := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have hs0 : s ∈ Ici (0:ℝ) := hs.1
    -- the beta-redex must be exposed before `rw` can see the source
    show (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0
      + lerayProj (0 : Fin 3 → ℤ) (convFull (c s) 0) = 0
    rw [convFull_zero_of_divFree (hcdiv s hs0), freq_zero]
    simp [lerayProj, dotR]
  have h := hinteq t ht 0
  rw [intervalIntegral.integral_congr hEqOn] at h
  simpa [hmean0] using h

/-- **W-R5: determining modes along two eternal flows with different
data.** Two data, each small in its own right, give (by
`ns_full_global_flow`) two eternal flows; every clause of that theorem
is quoted for each, plus the derived mean-zero clause. Between the two
flows, on EVERY window `[0, T]`, for every tolerance `δ` and every mode
count `N` past the threshold `2ν + K < ν·N²`: if the defect carries at
most `δ` in the modes below `N` on the window, the defect energy
synchronises at rate `ν·N² − K` down to the floor
`ν·N²/(ν·N² − K)·δ`.

`K` is obtained ONCE from `theorem_B_modes` at the budgets
`E := max (en c₀) (en c₀')`, `Z := max (ens c₀) (ens c₀')`, before the
flows, the horizon, the tolerance, or `N` are chosen: it is uniform
across horizons and depends only on `(ν, E, Z)`. The trap supplies the
enstrophy bound that the classical 3D theory has to assume; that is the
whole content of "the small-data trap dissolves the 3D conditionality of
determining modes". Initial data are NOT assumed equal or close. -/
theorem ns_full_global_flow_modes :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ c₀' : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      Summable (fun l => ‖c₀' l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀' l‖ ^ 2) →
      c₀' 0 = 0 → RealField c₀' → DivFree c₀' → κ * en c₀' * ens c₀' < ν ^ 4 →
      ∃ K, 0 < K ∧ ∃ c c' : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        (∀ t ∈ Ici (0:ℝ), c t 0 = 0) ∧
        c' 0 = c₀' ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c' t) ∧ DivFree (c' t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c' t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c' t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c' s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c' t k = c₀' k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c' s k + lerayProj k (convFull (c' s) k))) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c' s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c' t k + lerayProj k (convFull (c' t) k)) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c' t) ≤ en c₀' ∧ ens (c' t) ≤ ens c₀' ∧
          κ * en (c' t) * ens (c' t) < ν ^ 4) ∧
        (∀ t ∈ Ici (0:ℝ), c' t 0 = 0) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ δ : ℝ, 0 ≤ δ →
          ∀ N : ℕ, 2 * ν + K < ν * (N:ℝ) ^ 2 →
          (∀ s ∈ Icc (0:ℝ) T,
            (∑ k ∈ insert 0 (boxS N), ‖c s k - c' s k‖ ^ 2) ≤ δ) →
          ∀ t ∈ Icc (0:ℝ) T,
            en (fun l => c t l - c' t l)
              ≤ en (fun l => c₀ l - c₀' l) *
                  Real.exp (-((ν * (N:ℝ) ^ 2 - K) * t))
                + ν * (N:ℝ) ^ 2 / (ν * (N:ℝ) ^ 2 - K) * δ := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ c₀' hE hZ hm hr hd hs hE' hZ' hm' hr' hd' hs'
  -- the class budgets: max of the two data, nonneg as tsums of squares
  have hE0 : 0 ≤ max (en c₀) (en c₀') :=
    le_max_of_le_left (tsum_nonneg fun l => sq_nonneg _)
  have hZ0 : 0 ≤ max (ens c₀) (ens c₀') :=
    le_max_of_le_left (tsum_nonneg fun l => by positivity)
  -- K is fixed HERE: once, from (ν, E, Z), before any flow or horizon
  obtain ⟨K, hK, hmodes⟩ := theorem_B_modes
    (E := max (en c₀) (en c₀')) (Z := max (ens c₀) (ens c₀')) hν hE0 hZ0
  refine ⟨K, hK, ?_⟩
  -- the two eternal flows, one per datum
  obtain ⟨c, hc0, hstr, hsum, hcont, hinteq, hode, htrap⟩ :=
    hflow hν hE hZ hm hr hd hs
  obtain ⟨c', hc0', hstr', hsum', hcont', hinteq', hode', htrap'⟩ :=
    hflow hν hE' hZ' hm' hr' hd' hs'
  have hcdiv : ∀ t ∈ Ici (0:ℝ), DivFree (c t) := fun t ht => (hstr t ht).2
  have hcdiv' : ∀ t ∈ Ici (0:ℝ), DivFree (c' t) := fun t ht => (hstr' t ht).2
  -- mean-zero along each flow, derived (not exported upstream)
  have hmean := mean_zero_along_flow hm hcdiv hinteq
  have hmean' := mean_zero_along_flow hm' hcdiv' hinteq'
  refine ⟨c, c', hc0, hstr, hsum, hcont, hinteq, hode, htrap, hmean,
    hc0', hstr', hsum', hcont', hinteq', hode', htrap', hmean', ?_⟩
  intro T hT δ hδ N hN hlow t ht
  have hsub : Icc (0:ℝ) T ⊆ Ici (0:ℝ) := Icc_subset_Ici_self
  -- every hypothesis of the inner statement, discharged from the trap
  have h := hmodes hT hδ
    (fun k => (hcont k).mono hsub) (fun k => (hcont' k).mono hsub)
    (fun t ht => hsum t (hsub ht)) (fun t ht => hsum' t (hsub ht))
    (fun t ht => ⟨le_trans (htrap t (hsub ht)).1 (le_max_left _ _),
      le_trans (htrap t (hsub ht)).2.1 (le_max_left _ _)⟩)
    (fun t ht => ⟨le_trans (htrap' t (hsub ht)).1 (le_max_right _ _),
      le_trans (htrap' t (hsub ht)).2.1 (le_max_right _ _)⟩)
    (fun t ht => hcdiv t (hsub ht)) (fun t ht => hcdiv' t (hsub ht))
    (fun t ht => hmean t (hsub ht)) (fun t ht => hmean' t (hsub ht))
    (fun t ht k => by rw [hc0]; exact hinteq t (hsub ht) k)
    (fun t ht k => by rw [hc0']; exact hinteq' t (hsub ht) k)
    N hN hlow t ht
  simp only [hc0, hc0'] at h
  exact h

end TheoremB
