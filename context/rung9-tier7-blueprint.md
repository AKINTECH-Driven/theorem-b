# Rung 9 — Tier 7 blueprint: the bandwidth of the flow

Status: route PROPOSED, 29 Aug 2026, at tag `t6-smooth-green`. **No recon
fleet has been run and NOTHING here is compile-verified.** Every existing
lemma cited below was read from source in this tree (file:line given);
every Mathlib name is a guess under contract clause 3 and must be
confirmed on-machine before use. Contract otherwise unchanged: kernel +
gate judge; statements freeze at declaration; adversarial audit before
tags.

Provenance: proposed as "Rung R" in `rth-nse-rosetta.md` (Millennium
Expedition, Session 2 addendum), the single row of that table graded
Rung — work we can do ourselves in the campaign's honest regime. This
blueprint is that row converted into a route, with two corrections to
its wording that the source reading forced (see §2).

## 1. The goal

**How many degrees of freedom does a trapped Navier-Stokes flow have?**
Answer it with a number: an explicit `N₀(ν, E₀, Z₀)` such that the flow
below frequency `N₀` determines the whole flow. Two capstones.

- **`theorem_B_bandwidth` (R1, uniform approximation).** Along the eternal
  flow, the energy above frequency `N` never exceeds `Z₀/N²`, for every
  `N` and every `t ≥ 0`. The flow is within `Z₀/N²` of its `N`-mode
  truncation, forever, with no smallness needed beyond the trap that
  `ns_full_global_flow` already exports.
- **`theorem_B_modes` (R2, determination with an error floor).** There is
  `N₀` of explicit form such that for `N ≥ N₀`, any two flows in the trap
  class whose modes below `N` agree to within `δ` on a window satisfy
  `en(c₁ t − c₂ t) ≤ en(c₁ 0 − c₂ 0)·exp(−(νN² − K)t) + (νN²/(νN² − K))·δ`.
  Exact low-mode agreement (`δ = 0`) gives exponential lock-on at rate
  `νN² − K`; imperfect knowledge degrades gracefully to a floor of
  essentially `δ`. This is the Foias-Prodi determining-modes count, made
  unconditional in 3D by the small-data trap and explicit by our own
  constants.

Both are strict reuse. R1 is a composition. R2 is the `theorem_B_unique`
proof with one term kept instead of discarded, plus one new elementary
lemma. No new analysis is introduced at this tier.

## 2. The two corrections to the Rosetta's wording (load-bearing)

**Correction 1: the asymptotic statement is VACUOUS here; the tier must
be quantitative.** The Rosetta proposes "agreement on N modes forces
agreement of the whole flow". In our regime every solution already decays
to zero on its own: the energy pairing is exactly zero
(`convGal_energy_pairing`, NSGalerkin.lean:288) and mean-zero data give
`ens ≥ en` through `one_le_norm_freq` (SpectralNorms.lean:36), so
`en(c t) ≤ en c₀·exp(−2νt)` unconditionally. Any two trapped flows
therefore agree asymptotically for free, with zero modes transmitted.
A determining-modes theorem stated asymptotically would be true and
empty. **The deliverable is the RATE and the FLOOR, never the limit.**
Non-vacuity condition to state and check: `νN² − K > 2ν`, i.e. the
transmitted bandwidth buys lock-on strictly faster than the ambient
decay. `N₀` is defined by that inequality, not by `νN² > K`.

Recorded corollary, cheap and independently useful, not a capstone:
`theorem_B_decay`, `en (c t) ≤ en c₀ * Real.exp (-(2*ν*t))`, by the
Galerkin+Fatou route already used at Tier 3 (`en_limit_le`). Prove it
first; R2's honesty depends on it being on the record.

**Correction 2: exact agreement would make R2 content-free.** With `δ = 0`
the hypothesis "two trap-class flows whose low-N modes agree identically
on a window" is plausibly satisfied only by `c₁ = c₂`, which would make
the theorem non-vacuous in the register's sense (the zero datum inhabits
it) but empty in content. The `δ`-relaxed statement is the real theorem
and is the standard data-assimilation form; it is also no harder to
prove, since `δ` enters as one extra constant source. **Freeze R2 with
`δ`.** An audit probe exhibiting a non-trivial pair for some `δ > 0` is
part of W-R4.

## 3. The decisive design facts (source-read, not compile-verified)

1. **The count is already in the tree.** `pairing_absorbed`
   (PairingBound.lean:253) returns `K` as a closed formula in
   `(ν, E, Z, C_K)` at PairingBound.lean:263-267: three Young terms
   scaling like `ν⁻⁷` and `ν⁻¹⁵`, plus 1. `N₀` is the least `N` with
   `ν·N² − K > 2ν`. Nothing new is computed; the tier reads off a
   constant the campaign already owns.
2. **`theorem_B_unique` throws the count away, in one identifiable
   step.** At FullUnique.lean:562-575 the section derivative is bounded
   `g_R ≤ −2ν·SEC + (ν·ens d + K·en d) = −ν·SEC + ν·σ_R + K·en d`, and
   then `−ν·SEC` is DISCARDED via `hprod2 : 0 ≤ ν * SEC`
   (FullUnique.lean:573). R2 keeps it. If `d` vanishes below `N`, every
   surviving mode of the section has `‖freq k‖ > N` by `boxS_compl_freq`
   (TailBounds.lean:67), so `SEC ≥ N²·φ_R` and the same Gronwall closes
   with a negative rate instead of a vanishing source. **That single
   substitution is the mathematical content of this tier.**
3. **The Gronwall must NOT be differential.** Three routes were checked
   and two fail. (a) A decay sibling of `gronwall_const_source` with the
   non-constant source `σ_R` fails: the integrating-factor step needs
   FTC on `∫ σ_R`, hence continuity of `σ_R`, and the campaign only ever
   proves `σ_R` INTEGRABLE (`tail_integrable`, TailBounds.lean:198),
   deliberately. (b) The Phi-trick of FullUnique fails: it works because
   the integral enters with a `+` sign; at a negative rate an upper
   bound on the primitive is useless. (c) **The route that works**: take
   `R → ∞` FIRST, on the integrated section inequality over an arbitrary
   subwindow, then run a discrete iteration on the resulting window
   inequality. See §4.
4. **`a 0 = b 0` in `pairing_absorbed` is the ZERO MODE, not time zero.**
   `a b : (Fin 3 → ℤ) → Vel`, so `0 : Fin 3 → ℤ` is the zero frequency.
   FullUnique discharges it from zero-mode constancy (`hzero`), not from
   shared data. This is why R2 may take flows with DIFFERENT initial
   data while `theorem_B_unique` may not, and it is the reason R2 is a
   new theorem rather than a corollary. Misreading this collapses the
   tier; it is the first trap in §7.
5. **`tail_en_lt` is already general enough for the Poincare step.** Its
   `Z` is a hypothesis-bounded budget (`hZle : ens d ≤ Z`), so
   instantiating `Z := ens d` by `le_rfl` yields `en d − Σ_box ≤ ens d/R²`
   with no new lemma. R1 instantiates the same lemma at `Z := ens c₀`
   through the trap clause.

## 4. The R2 derivation, in the order it must be formalized

Let `d s := c₁ s − c₂ s`, `c := νN² − K`, `φ_R`, `SEC_R`, `σ_R` exactly as
FullUnique.lean:429-434 defines them, `N ≤ R`, and let the low-mode
hypothesis be `∀ s, Σ_{k ∈ insert 0 (boxS N)} ‖d s k‖² ≤ δ`.

1. Section derivative, verbatim FullUnique with `hprod2` replaced:
   `SEC_R ≥ N²·(φ_R − δ)` by `boxS_compl_freq` at radius `N`, giving
   `g_R(s) ≤ −c·φ_R(s) + [ν·σ_R(s) + 4KZ/R² + νN²δ]`.
2. FTC on the section over an arbitrary subwindow `[t₀, t] ⊆ [0, T]`
   (`hftc` pattern, FullUnique.lean:597):
   `φ_R(t) + c∫_{t₀}^{t} φ_R ≤ φ_R(t₀) + S_R + νN²δ(t − t₀)`,
   with `S_R := ν∫_0^T σ_R + 4KZT/R²`.
3. Sandwich to the full energy with `tail_en_lt` on both sides
   (`φ_R ≤ en d` and `en d ≤ φ_R + 4Z/R²`), then `R → ∞` using
   `tail_source` (TailBounds.lean:220). Every error term is additive and
   vanishes. Result, the **window inequality**, for all
   `0 ≤ t₀ ≤ t ≤ T`:
   `en(d t) + c∫_{t₀}^{t} en(d s) ds ≤ en(d t₀) + νN²δ(t − t₀)`.
4. Iteration (the new lemma, §5): `en(d ·)` is nonincreasing up to the
   `δ` term, so `∫_{t₀}^{t} en(d s) ds ≥ (t − t₀)·en(d t)`; one step
   gives `en(d t)(1 + cΔ) ≤ en(d t₀) + νN²δΔ`; `n` steps of size `t/n`
   and `(1 + ct/n)^n ↑ exp(ct)` give the capstone.

Note the limit in step 3 is taken on an INEQUALITY, never inside a
derivative. This is what keeps the tier free of the a.e./continuity
machinery the campaign does not have.

## 5. Waves

- **W-R0a — the Galerkin half. LANDED, gate-green (29 Aug 2026).**
  `TheoremB/EnergyDecay.lean`: `en_le_ens` (spectral Poincare, three
  rewrites off `sob_le_sob` at levels 0 and 1 — the lemma Tier 6 added
  for its own majorant already IS this inequality) and
  `galerkin_energy_decay`, `en (c t) ≤ en (c 0)·exp(−2νt)` on the
  window. Hypotheses are exactly `galerkin_conditional_trap`'s
  energy-side ones, so every existing consumer discharges them
  unchanged; the conclusion strengthens its `en (c t) ≤ en (c 0)`
  clause to a rate. Risk was LOW and proved LOW.
- **W-R0b — the transfer to the eternal flow. NOT LANDED; BLOCKED at
  trap level, and the block is measured, not guessed (29 Aug 2026).**
  Recon correction: this blueprint's first draft graded all of W-R0 LOW,
  which was wrong, and its route (β) is now known to be unavailable in
  the class the capstone lives in.
  Why the transfer cannot be a corollary: `en_limit_le` needs a uniform
  finite-subsum bound AT the extraction, and `theorem_B` does not export
  one, so the decay clause cannot be read off the exported clauses.
  Why route (β) is blocked: proving `convFull_energy_pairing` (the
  full-level twin of `convGal_energy_pairing`) by limit from the
  Galerkin identity needs absolute summability of
  `k ↦ ⟪convFull c k, c k⟫`, and EVERY available route to it wants ℓ¹:
  `summable_norm_convFull` (TimeLayer.lean:184) takes
  `Summable (‖c k‖)` and `Summable (‖freq k‖·‖c k‖)` as hypotheses, and
  `triMaj_le` (SpectralNorms.lean:933) takes `hSa : Summable a` with
  `a = ‖c‖`. The trap gives ℓ² and weighted ℓ², never ℓ¹: `spec1` is
  controlled ONLY through the sharp Agmon bound
  `exists_spec1_pow_four_le_ens_mul_dis` (SpectralNorms.lean:824),
  `spec1 c ^ 4 ≤ C·(ens c · dis c)`, which needs the DISSIPATION `dis`
  — and `dis` is not bounded pointwise in time by `(E, Z)`.
  Why the weaker fallback is not worth taking: running the section
  argument with `pairing_absorbed` at `b := 0` instead of the vanishing
  identity replaces the exact rate `2ν` by `ν − K`, positive only when
  `K < ν`. Since `K ≥ 1` and carries `ν^(−15)`, that is a
  large-viscosity/small-budget subregime — precisely the v2 item the
  Tier-6 audit register already recorded. It would weaken W-R0a's
  Galerkin-level `2ν`, not extend it.
  **Route (γ) — superseded, see below.** Doing the transfer in the
  SMOOTH class would work (`theorem_B_smooth` exports weighted ℓ¹ at
  every order, TheoremBSmooth.lean:137/239/400), but it buys a
  scoping clause that is not needed.
  **Route (α) IS THE ROUTE, and routes (β)/(γ) were solving the wrong
  problem (correction, 29 Aug 2026).** The transfer never needed the
  full-level pairing identity at all. The decay is proved at the
  GALERKIN level — where `convGal_energy_pairing` already gives the
  energy pairing EXACTLY zero over a finite sum, with no summability
  question — and Fatou (`en_limit_le`) carries a per-time bound through
  the extraction like any other trap clause. No ℓ¹ enters anywhere. So
  W-R0b is achievable in the TRAP class at the sharp rate `2ν`,
  strictly better than route (γ)'s smooth-class scoping. The ℓ¹
  obstruction recorded above is real, but it blocks a lemma the
  transfer does not use.
  Remaining work, MED and mechanical: replay `theorem_B_cont`'s
  assembly (FullUnique.lean:100-312, ~210 lines) carrying the extra
  per-time clause `en (c t) ≤ en c₀ · exp(−2νt)`, exactly as Tier 6's
  W4 replayed it for the Sobolev clause, then identify the witness with
  `ns_full_global_flow`'s flow via `theorem_B_unique`.

  **Self-audit finding (W-R0a), fixed 29 Aug 2026.** `galerkin_energy_decay`
  was frozen with `hODE : ∀ t k, HasDerivAt …` — on ALL of `ℝ`, copied
  from `galerkin_conditional_trap`. No producer in this campaign exports
  that: `galerkin_family` gives the ODE on `Icc 0 T`,
  `ns_galerkin_global_flow` on `Ici 0`. As frozen, the lemma could not
  be composed with anything. Hypothesis weakened to `Icc 0 T`, which
  strengthens the theorem and breaks no consumer (there were none).
  This is the campaign's recurring composition-gap failure mode, the one
  the register says to catch with a compiled probe at every tier — and
  W-R0a shipped without such a probe. It surfaced only when the
  composition was attempted for W-R0b. **Rule for the next rung: no wave
  ships without a compiled composition probe against a real producer,
  not merely a type-correct statement.**
- **W-R1 — `theorem_B_bandwidth`.** `tail_en_lt` at `Z := ens c₀`
  composed with `ns_full_global_flow`'s summability and trap clauses.
  Risk LOW. Tag `t7-bandwidth-green` here; this rung is independently
  publishable and independently honest.
- **W-R2a — integrability of the energy history. LANDED, gate-green
  (29 Aug 2026), VIA THE FALLBACK.** `TheoremB/EnergyIntegrable.lean`.
  The wave was specified as `continuousOn_en_defect` with measurability
  as a fallback; the fallback is what shipped, and on inspection it is
  the RIGHT statement, not a concession:
  `decay_of_window_integral_ineq` consumes `IntervalIntegrable` and
  nothing stronger, so continuity was never needed. Continuity is also
  not cheaply available - the Weierstrass route (`continuousOn_tsum`)
  wants a summable uniform majorant, and the only candidate here is
  `‖d s k‖² ≤ Z/‖freq k‖²`, whose sum `Σ‖k‖^(−2)` DIVERGES over ℤ³.
  That is the campaign's standing obstruction (announcement draft,
  long-form note on the ε/3 tail method), and it would have cost the
  whole `TendstoUniformlyOn` apparatus to route around.
  Delivered: `box_tendsto_atTop` (public re-derivation of TailBounds'
  private `b4_box_tendsto`, from the public `exists_boxS`),
  `en_sec_tendsto`, `en_sec_contOn`, `aestronglyMeasurable_en`,
  `intervalIntegrable_en` - the `en` twins of the private `b4_*`
  machinery `tail_integrable` already runs for `ens`. Risk was LOW-MED;
  landed first try.
- **W-R2b — `decay_of_window_integral_ineq`. LANDED, gate-green
  (29 Aug 2026).** `TheoremB/WindowDecay.lean`. Risk was LOW-MED and
  proved LOW-MED: two iterations to green. Name corrections against the
  guesses: the limit is `Real.tendsto_one_add_div_pow_exp`
  (Analysis/SpecialFunctions/Complex/LogBounds.lean:441, ℕ-pow form in
  `namespace Real`) — `tendsto_one_plus_div_pow_exp` does NOT exist at
  the pin; `intervalIntegral.integral_mono_on` and
  `intervalIntegral.integral_nonneg` are both real, with the signatures
  guessed. `div_le_div_of_nonneg_right` wants `0 ≤` on the denominator,
  not `0 <`.
  Audit note: `hT : 0 ≤ T` is NOT consumed — when `T < 0` the window is
  empty and the conclusion is vacuous, so the hypothesis only weakens
  the lemma. Retained for interface stability and renamed `_hT`
  (identical type). Precedent: the Tier-5 audit's finding on
  `mode_equation_of_weak`.
  The file imports Mathlib ONLY, no campaign module — so it is a clean
  standalone PR candidate, see §8.
- **W-R3 — the section rerun. LANDED, gate-green (29 Aug 2026).**
  `TheoremB/ModesWindow.lean`, `modes_window_ineq`. 452 lines, four
  compile iterations; the bet on line-isomorphism to FullUnique paid.
  Traps hit, both mechanical: `intervalIntegral.integral_neg` will not
  fire on `-(c * φ s)`, so the rate is carried as `(-(c)) * φ s` and
  every piece stays a `const_mul` (then `rw [neg_mul]` before the final
  `linarith`, so both sides share the atom `c * ∫φ`); and `linarith`
  cannot scale a hypothesis by `ν`, so `ν·∫σ ≤ ν·∫_0^T σ` must be
  supplied pre-multiplied.
- **W-R4 — `theorem_B_modes`. LANDED, gate-green (29 Aug 2026).**
  `TheoremB/DeterminingModes.lean`; probes in `TheoremB/ModesProbe.lean`.
  The composition is two waves and one line: W-R3's window inequality is
  EXACTLY the shape W-R2b consumes, by construction.
  Audit probe 1, COMPILED (`modes_hypotheses_consistent`): the zero flow
  discharges every hypothesis for every `ν > 0` and horizon, so the
  hypothesis set is consistent.
  Audit probe 2, RESOLVED and recorded in the probe file: the low-mode
  hypothesis is implied by `en (d s) ≤ δ`, and every defect in the class
  obeys `en (d s) ≤ 4E`; so at `δ := 4E` it holds for EVERY pair of
  flows in the class, with nothing assumed relating them. The theorem is
  therefore inhabited by genuinely distinct flows, not only by
  `c₁ = c₂`. That instance buys little (its floor exceeds the trivial
  bound `4E`) — which IS Correction 2's content: the force lives at
  small `δ`, and the statement degrades gracefully instead of going
  vacuous as `δ` grows.
- **W-R-cap — DROPPED, deliberately.** `N₀` as a packaged definition was
  dropped: `theorem_B_modes` already quantifies over every `N` past
  `2ν + K < ν·N²`, so a named `N₀` would add a definition without adding
  content. The arithmetic mode count stays a docstring remark, trap 4.

## 6. Frozen interfaces (statements freeze here)

W-R1 file `TheoremB/Bandwidth.lean`:

```
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
            ≤ ens c₀ / (N:ℝ) ^ 2)
```

The flow clauses are quoted from `ns_full_global_flow`; only the last is
new. State the bandwidth clause in `tail_en_lt`'s own shape (full sum
minus finite section), NOT via a new truncation definition.

W-R2b file `TheoremB/WindowDecay.lean`:

```
theorem decay_of_window_integral_ineq {e : ℝ → ℝ} {c A T : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hnn : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ e t)
    (hint : ∀ t₀ ∈ Icc (0:ℝ) T, ∀ t ∈ Icc t₀ T,
      IntervalIntegrable e MeasureTheory.volume t₀ t)
    (hwin : ∀ t₀ ∈ Icc (0:ℝ) T, ∀ t ∈ Icc t₀ T,
      e t + c * (∫ s in t₀..t, e s) ≤ e t₀ + A * (t - t₀)) :
    ∀ t ∈ Icc (0:ℝ) T, e t ≤ e 0 * Real.exp (-(c * t)) + A / c
```

W-R4 file `TheoremB/DeterminingModes.lean`:

```
theorem theorem_B_modes :
    ∀ {ν E Z T δ : ℝ}, 0 < ν → 0 ≤ T → 0 ≤ δ →
    ∀ {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel},
    (∀ k, ContinuousOn (fun s => c₁ s k) (Icc (0:ℝ) T)) →
    (∀ k, ContinuousOn (fun s => c₂ s k) (Icc (0:ℝ) T)) →
    (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2)) →
    (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₂ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2)) →
    (∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E ∧ ens (c₁ t) ≤ Z) →
    (∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E ∧ ens (c₂ t) ≤ Z) →
    (∀ t ∈ Icc (0:ℝ) T, DivFree (c₁ t)) →
    (∀ t ∈ Icc (0:ℝ) T, DivFree (c₂ t)) →
    (∀ t ∈ Icc (0:ℝ) T, c₁ t 0 = 0) → (∀ t ∈ Icc (0:ℝ) T, c₂ t 0 = 0) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₁ 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k))) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₂ 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) →
    ∃ K, 0 < K ∧ ∀ N : ℕ, 2 * ν + K < ν * (N:ℝ) ^ 2 →
      (∀ t ∈ Icc (0:ℝ) T,
        (∑ k ∈ insert 0 (boxS N), ‖c₁ t k - c₂ t k‖ ^ 2) ≤ δ) →
      ∀ t ∈ Icc (0:ℝ) T,
        en (fun l => c₁ t l - c₂ t l)
          ≤ en (fun l => c₁ 0 l - c₂ 0 l) *
              Real.exp (-((ν * (N:ℝ) ^ 2 - K) * t))
            + ν * (N:ℝ) ^ 2 / (ν * (N:ℝ) ^ 2 - K) * δ
```

Deliberate statement decisions, each with its reason:

- `K` is existential and quantified BEFORE `N`, mirroring
  `pairing_absorbed`; the caller picks any `N` past the threshold.
- The threshold is written `2ν + K < νN²`, not `K < νN²`: the ambient
  decay of Correction 1 is built into the frozen statement so no
  outward description can overstate the result.
- No `RealField`, matching `theorem_B_unique`, which assumes none.
- Mean-zero is a hypothesis (`c t 0 = 0`), not derived, because the
  `pairing_absorbed` zero-mode side condition needs it and the flows do
  not share a datum here (design fact 4).
- Initial data are NOT assumed equal. That is the point of the tier.

Fallback ladder, each rung independently taggable and honest:
v1 = `t7-bandwidth-green` (W-R0 + W-R1, cheap, publishable alone);
v2 = + `decay_of_window_integral_ineq` and the window inequality, stated
as a standalone lemma without the capstone;
v3 = `t7-modes-green` (full `theorem_B_modes`).

## 7. Traps carried forward

1. **`a 0 = b 0` is the zero FREQUENCY** (design fact 4). Reading it as
   "same initial data" collapses R2 into `theorem_B_unique` and wastes
   the tier.
2. **Do not write a decay `gronwall_const_source`.** Design fact 3(a):
   the source is integrable, never continuous, by deliberate campaign
   choice. The iteration lemma exists to avoid exactly this.
3. **`boxS` is a SUP-NORM box minus the origin** (NSFull.lean:225-226),
   so `insert 0 (boxS N)` has `(2N+1)³` sites. `boxS_compl_freq` gives
   the EUCLIDEAN bound `N < ‖freq k‖` outside it; the mismatch is safe
   in the direction we need but must not be inverted.
4. **The mode count is arithmetic, not a theorem.** `(2N₀+1)³ − 1`
   lattice sites; after reality pairing and the divergence-free
   constraint, roughly `2((2N₀+1)³ − 1)` real numbers. Put this in a
   docstring as an arithmetic remark. Do NOT state it as a formal
   clause and do NOT call it a dimension count in any outward text.
5. **Claim-wording rule 1 (rung8 audit register) binds here.** `K` is a
   constant OF EXPLICIT FORM up to the convergent lattice-kernel sum
   `Σ‖k‖^(−7/2)` (`C_K`, `kernel_sum_le`, LatticeKernel.lean:75). Therefore `N₀` is an
   explicit formula, never a printable integer, until someone bounds
   `C_K` numerically. Bounding `C_K` is a well-defined optional
   sub-task; until it lands, never write "N₀ = <number>".
6. **`K` carries `ν⁻¹⁵`, so `N₀` is astronomically large.** Say so in
   the announcement text before a reader assumes otherwise. The result
   is a finiteness statement with an explicit form, not a small number.
7. Interval localization (announcement long-form note (a)): state the
   whole chain on `Icc`, never `∀t`.
8. Junk-tsum discipline: `en`/`ens` summability travels in the
   statement, as everywhere else in this campaign.

## 8. Upstreaming note

`decay_of_window_integral_ineq` belongs in Unit 3 of
`upstreaming-dossier.md` alongside `gronwall_const_source`: Mathlib's
Gronwall family is differential and left-endpoint-bound, and a
derivative-free window-integral form is strictly more applicable.
W-R2b has landed, so this is now actionable. It is the campaign's most
PR-ready artifact to date: `TheoremB/WindowDecay.lean` imports Mathlib
only and depends on no campaign definition, so it can be lifted
verbatim. Generalization before PR: none needed for ℝ; the natural
extension is a `[LinearOrderedField]`-valued or Bochner-valued form.
Acting on it is outward-facing and therefore the user's call.

## 9. Honesty ledger for this rung

| Grade | Items |
|---|---|
| Verified from source (this tree, by reading) | The discarded `−ν·SEC` at FullUnique.lean:573; `K`'s closed form at PairingBound.lean:263-267; `tail_en_lt`'s budget hypothesis; `boxS_compl_freq`; the zero-MODE reading of `pairing_absorbed`'s side condition; `boxS` as a sup-norm box; the absence of any `ContinuousOn (en ∘ ·)` lemma in the tree |
| Derived here, NOT compiled | The §4 chain in full; the vacuity of the asymptotic statement (Correction 1); the `δ`-relaxation (Correction 2); the failure of routes 3(a) and 3(b) |
| Guessed (contract clause 3) | Every Mathlib name: `intervalIntegral.integral_mono_on`, `tendsto_one_plus_div_pow_exp`, `measurable_of_tendsto'` |
| Cited, not ours | Foias-Prodi determining modes (2D unconditional, 3D conditional); Azouani-Olson-Titi nudging. Our contribution is explicitness, the unconditional 3D small-data regime, and machine-checking. Not novel in principle |
| Refused | Nothing this rung required refusing |

SUMMIT REACHED 29 Aug 2026, tag `t7-modes-green`. W-R0a, W-R1, W-R2a,
W-R2b, W-R3, W-R4 all landed and gate-green; 176 audited theorems. The
one wave NOT done is W-R0b, the transfer of ambient decay from the
Galerkin flows to the eternal flow — a scoping result for Correction 1,
not a dependency of the capstone; route (β) stays the way in.

Smallest next move: W-R0b by route (α) — replay `theorem_B_cont`'s
assembly carrying `en (c t) ≤ en c₀·exp(−2νt)`, then identify via
`theorem_B_unique`. Trap class, sharp rate, no ℓ¹. Routes (β) and (γ)
are recorded above as closed and superseded respectively. The Mathlib PR
for `WindowDecay.lean` is drafted and compile-verified at
`context/upstream/`, awaiting the user's call on submission.
