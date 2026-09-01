/-
# The bandwidth of the flow (Tier 7, wave W-R1)

`theorem_B_bandwidth`: along the eternal small-data flow, the energy
living OUTSIDE the sup-norm cube `‖k‖_∞ ≤ N` (a subset of the Euclidean
tail `|k| > N`, so this is the weaker-looking, honest object) never
exceeds `Z₀/N²`, at every time and for every `N`. Equivalently: the flow
stays within `Z₀/N²` in energy of its cube-`N` truncation, forever.

This is the "rendering resolution" half of Tier 7 (rung9 blueprint, R1).
It is the uniform-in-time finite-bandwidth statement, and it needs no
smallness beyond the trap that `ns_full_global_flow` already exports:
the enstrophy budget is conserved downward by the trap, and the tail
Poincare inequality converts an enstrophy budget into an energy tail
bound at every radius.

The bandwidth clause is stated in `tail_en_lt`'s own shape - the full
sum minus a finite section - deliberately, so that no new truncation
definition enters the statement.
-/
import TheoremB.FullUnique

namespace TheoremB

open Set

/-- **W-R1, the Tier-7 bandwidth capstone.** The eternal flow of
`ns_full_global_flow`, with ALL SEVEN of its clauses quoted verbatim
(datum, reality and divergence-freeness, summability, mode continuity,
the integral equation, the mode ODE on `t > 0`, and the full trap
including the `κ`-smallness), additionally satisfies: for every box
radius `N > 0` and every time `t ≥ 0`, the energy outside the sup-norm
cube `‖k‖_∞ ≤ N` is at most `ens c₀ / N²`.

Uniform in time, and with the initial enstrophy as the only input.

AUDIT RECORD (2 Sep 2026). The statement as first tagged
(`t7-bandwidth-green`) quoted only THREE of the seven flow clauses and
was therefore VACUOUS: the constant function `c t := c₀` proved it from
`tail_en_lt` alone (compiled probe, two independent auditors). The
missing clauses were always available in the proof — obtained and
discarded — and are now exported. No new mathematics; the `refine`
gained four names. -/
theorem theorem_B_bandwidth :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
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
        (∀ N : ℕ, 0 < N → ∀ t ∈ Ici (0:ℝ),
          en (c t) - (∑ k ∈ insert 0 (boxS N), ‖c t k‖ ^ 2)
            ≤ ens c₀ / (N:ℝ) ^ 2) := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0
  obtain ⟨c, hc0, hstr, hsum, hcont, hinteq, hode, htrap⟩ :=
    hflow hν hE hZ hmean hreal hdiv h0
  refine ⟨c, hc0, hstr, hsum, hcont, hinteq, hode, htrap, ?_⟩
  intro N hN t ht
  exact tail_en_lt (Z := ens c₀) N hN (hsum t ht).1 (hsum t ht).2
    (htrap t ht).2.1

end TheoremB
