/-
# The bandwidth of the flow (Tier 7, wave W-R1)

`theorem_B_bandwidth`: along the eternal small-data flow, the energy
living above frequency `N` never exceeds `Z₀/N²`, at every time and for
every `N`. Equivalently: the flow stays within `Z₀/N²` in energy of its
`N`-mode truncation, forever.

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
`ns_full_global_flow`, with its datum, summability and trap clauses
quoted, additionally satisfies: for every box radius `N > 0` and every
time `t ≥ 0`, the energy outside the box is at most `ens c₀ / N²`.

Uniform in time, and with the initial enstrophy as the only input. -/
theorem theorem_B_bandwidth :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀) ∧
        (∀ N : ℕ, 0 < N → ∀ t ∈ Ici (0:ℝ),
          en (c t) - (∑ k ∈ insert 0 (boxS N), ‖c t k‖ ^ 2)
            ≤ ens c₀ / (N:ℝ) ^ 2) := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0
  obtain ⟨c, hc0, hstr, hsum, hcont, hinteq, hode, htrap⟩ :=
    hflow hν hE hZ hmean hreal hdiv h0
  refine ⟨c, hc0, hsum, fun t ht => ⟨(htrap t ht).1, (htrap t ht).2.1⟩, ?_⟩
  intro N hN t ht
  exact tail_en_lt (Z := ens c₀) N hN (hsum t ht).1 (hsum t ht).2
    (htrap t ht).2.1

end TheoremB
