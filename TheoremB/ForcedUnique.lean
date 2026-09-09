/-
  TheoremB/ForcedUnique.lean
  Tier 8a, wave F4 of the Theorem B campaign (9 Sep 2026).

  THE COEFFICIENT-LANGUAGE BREAKDOWN COROLLARY of the forced Theorem B.  In
  the campaign's own vocabulary (spectral coefficients `c : ℝ → (Fin 3 → ℤ)
  → Vel`, energy `en`, enstrophy `ens`, the mode-wise Leray projection, the
  inline forced right-hand side of ForcedTheoremB.lean): if the forced
  periodic system started from trap-class data admits NO flow of the class
  that stays inside a box `(Es, Zs)` on `[0, T]`, then at some time the
  force is outside the box's force thresholds.  Read contrapositively: a
  flow from trap-class data that leaves the box, or fails to exist in the
  class on some horizon, does so only if the force budget is violated at
  some time, or the data are outside the trap (`κ·Es·Zs ≤ ν⁴` is a
  hypothesis; when no admissible box exists the statement is vacuous, the
  unforced trap's own boundary).

  What the file delivers:

  * `forced_breakdown_threshold` (box form): the contrapositive of
    `theorem_B_forced` at the budget `G := min (ν²·Es) (ν²·Zs/8)`.  The
    hypothesis is "no flow confined to the box" — WEAKER than
    non-existence (a regular flow that exits the box satisfies it), so the
    theorem IMPLIES a breakdown reading rather than being one.

  * `forced_breakdown_threshold'` (natural box `(en c₀, ens c₀)`): the box
    form at the datum's own energy and enstrophy.  Requires `0 < ens c₀`
    (the natural box must be an admissible box); the datum `c₀ = 0` is
    covered by the box form with any `Zs > 0`.

  The two `∃ κ` are unlinked by statement (the house pattern): "κ" here is
  the κ of `theorem_B_forced` by PROOF, not by statement.  `κ_forced = 8·K`
  is of explicit form up to the lattice-kernel sum `C_K`, exported as a
  compiled existential; the force thresholds `ν²·Es`, `ν²·Zs/8` are
  literal expressions.  No numeric value of any constant is claimed.

  WHAT THIS IS NOT (binding for every downstream claim).  This is the
  "Comparator-adjacent corollary, coefficient language".  It is NOT the
  community's `navier_stokes_breakdown_periodic`, NOT its negation, and NOT
  a real-space statement: no velocity field, no pressure, no smoothness
  class, no time-derivative of the physical field appears — only the
  campaign's coefficient class (real, divergence-free, ℓ²/H¹-summable,
  mode-continuous, the forced integral equation and the forced mode ODE).
  The force here is mean-zero, real, divergence-free, ℓ² and per-mode
  continuous, with only its energy (squared ℓ² norm) entering the
  thresholds; a force outside that class is outside the statement.  At
  `g = 0` the forced chain is NOT a strengthening of the unforced one
  (`κ_forced = 8·K ≠ K`, non-strict `≤`, the box a hypothesis rather than
  the datum's energy and enstrophy), and must never be described as one.
  No priority is claimed: the small-Grashof forced small-data theory is
  textbook (Temam, Navier-Stokes Equations: Theory and Numerical Analysis,
  Ch. III; Robinson-Rodrigo-Sadowski, The Three-Dimensional Navier-Stokes
  Equations, Ch. 6-7; Constantin-Foias, Navier-Stokes Equations, Ch. 10;
  Foias-Manley-Rosa-Temam, Navier-Stokes Equations and Turbulence, Ch. II;
  named as references, theorem numbers unverified), and the corollary is
  a ~20-line contrapositive of a compiled theorem.  Nothing here is new
  mathematics.

  PLACEMENT NOTE: the blueprint's F4 block also freezes
  `theorem_B_unique_forced` and `ns_full_global_flow_forced`; both were
  delivered early, byte-identical, in TheoremB/ForcedTheoremB.lean (the
  eternal splice needs the uniqueness) and are NOT restated here.

  CONTRACT: the theorem STATEMENTS marked **F4** are frozen (rung10 Tier-8
  blueprint, section 4a, wave F4) and transcribed byte-for-byte.  If a
  statement cannot be proved as written, do not silently repair it: keep
  it, add a sibling, and report.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.ForcedTheoremB

namespace TheoremB

open Set

/-! ## The corollary, box form -/

/-- **F4 (frozen).**  Box form of the coefficient-language breakdown
corollary.  From mean-zero, real, divergence-free, finite-energy,
finite-enstrophy data inside an admissible box `(Es, Zs)` (`κ·Es·Zs ≤ ν⁴`),
under a mean-zero, real, divergence-free, ℓ², per-mode-continuous force: if
NO flow of the class stays inside the box on `[0, T]`, then at some time
`t ≥ 0` the force's energy exceeds `ν²·Es` or eight times it exceeds
`ν²·Zs`.  Contrapositive of `theorem_B_forced` at the budget
`G := min (ν²·Es) (ν²·Zs/8)`.  The hypothesis is "no flow confined to the
box", weaker than non-existence.  Coefficient vocabulary only; not the
community's breakdown statement, its negation, or a real-space statement.
When `κ·en c₀·ens c₀ > ν⁴` no admissible box exists and the statement is
vacuous — the unforced trap's own boundary.

Audit notes (F4 readers, 9 Sep 2026). (1) The contrapositive reading "a flow that leaves the box does so only if the force budget is violated" passes through uniqueness: "a flow leaves the box" gives "no confined flow of the class exists" only via `theorem_B_unique_forced`, not from this statement alone. (2) The conclusion's time is not localised to the horizon: it reads `∃ t ∈ Ici 0`, inherited from the global force budget of `theorem_B_forced`; the force may exceed a threshold after `T`. (3) At `T = 0` the antecedent is always false (a constant flow is confined), so the corollary is vacuous there and `T = 0` is never to be cited. -/
theorem forced_breakdown_threshold :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) → (∀ t ∈ Ici (0:ℝ), DivFree (g t)) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) →
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) →
      ∀ {Es Zs : ℝ}, 0 ≤ Es → 0 < Zs → κ * Es * Zs ≤ ν ^ 4 →
      en c₀ ≤ Es → ens c₀ ≤ Zs →
      ∀ T : ℝ, 0 ≤ T →
      (¬ ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)) →
      ∃ t ∈ Ici (0:ℝ), ν ^ 2 * Es < en (g t) ∨ ν ^ 2 * Zs < 8 * en (g t) := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_forced
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ g hs1 hs2 hc0 hreal hdiv hg0 hgreal hgdiv hgsum hgc Es Zs hEs hZs hκE hE hZ
    T hT hno
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_lt] at hcon
  apply hno
  have hmin1 : min (ν ^ 2 * Es) (ν ^ 2 * Zs / 8) ≤ ν ^ 2 * Es := min_le_left _ _
  have hmin2 : min (ν ^ 2 * Es) (ν ^ 2 * Zs / 8) ≤ ν ^ 2 * Zs / 8 := min_le_right _ _
  exact H (G := min (ν ^ 2 * Es) (ν ^ 2 * Zs / 8)) hν hEs hZs hκE hmin1 (by linarith)
    hs1 hs2 hc0 hreal hdiv hE hZ hg0 hgreal hgdiv hgsum
    (fun t ht => le_min (hcon t ht).1 (by linarith [(hcon t ht).2])) hgc T hT

/-! ## The corollary at the natural box -/

/-- **F4 (frozen).**  The corollary at the natural box `(en c₀, ens c₀)`:
the box form with `Es := en c₀`, `Zs := ens c₀`.  Requires `0 < ens c₀` so
that the natural box is admissible (the datum `c₀ = 0` is covered by the box
form with any `Zs > 0`).  Hypothesis wording: "no flow confined to the
natural box".  Coefficient vocabulary only, as above. -/
theorem forced_breakdown_threshold' :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) → (∀ t ∈ Ici (0:ℝ), DivFree (g t)) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) →
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) →
      0 < ens c₀ → κ * en c₀ * ens c₀ ≤ ν ^ 4 →
      ∀ T : ℝ, 0 ≤ T →
      (¬ ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀)) →
      ∃ t ∈ Ici (0:ℝ), ν ^ 2 * en c₀ < en (g t) ∨ ν ^ 2 * ens c₀ < 8 * en (g t) := by
  obtain ⟨κ, hκ, H⟩ := forced_breakdown_threshold
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ g hs1 hs2 hc0 hreal hdiv hg0 hgreal hgdiv hgsum hgc hens hκE T hT hno
  have hen : 0 ≤ en c₀ := tsum_nonneg fun k => sq_nonneg _
  exact H hν hs1 hs2 hc0 hreal hdiv hg0 hgreal hgdiv hgsum hgc hen hens hκE le_rfl le_rfl
    T hT hno

end TheoremB
