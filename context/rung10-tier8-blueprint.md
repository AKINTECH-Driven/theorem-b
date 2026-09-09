# Rung 10 — Tier 8 blueprint: the forced trap (8a) and the community class inhabited (8b)

Status: PLANNING (9 Sep 2026) — **nothing built; gate untouched at
`82a9ab6`** (HEAD `b45ce9e` is prose-only on top of it;
`scripts/check_axioms.sh` NOT run by this pass; the "GREEN 186/186"
figure is the campaign record from the 2 Sep audit, not re-measured here).
Working tree: `git status` was clean when this pass began; this pass wrote
ONLY this file. At its end `git status` also showed
`context/announcement-draft.md` modified and `README.md` untracked — changes
made by ANOTHER session during this pass, not read and not touched here.
Nothing in this file claims that any Tier-8 declaration exists in the
tree. What exists: two designs (8a forced trap, 8b time-smoothness to the
community class), four critiques (statement-shape and feasibility lens on
each), and their probes under
`scratchpad/tier8/` (`design-a/`, `design-b/`, `feas-b/`, `audit-shape/`,
and the architect's `final/`). Every interface in §4 is marked COMPILED
(statement elaborates, exit 0 at the pin, `sorry` body unless PROVED is
said) or SKELETON (not compiled). The critics' required changes are
APPLIED in §4 and were re-compiled by this pass in
`scratchpad/tier8/final/{TimeSmoothFinal,JointSmoothFinal,CommunityClassFinal,ForcedFinal}.lean`
(all exit 0; 21/13/15/5 `sorry` declarations respectively; the composition
proof of `theorem_B_community_periodic` and `force_zero_spelling_rfl` and
`coeff_shift_forced` are PROVED there). Contract unchanged: kernel + gate
judge; statements freeze at declaration; independent adversarial reader
BEFORE any tag (the rule Tier 7 did not meet; it binds here).

**EVIDENCE STATE, corrected 9 Sep 2026 (later the same day, by the
orchestrator).** The session scratchpad that held every probe this file
cites (`scratchpad/tier8/…`, including `design-a/DesignA_F0_ForcedTrap.lean`
with its four PROVED declarations, `final/*.lean`, and the RECON/feas/audit
probes) was WIPED without notice at 13:14, before any copy was taken. Every
COMPILED / PROVED mark below therefore rests on the builders' reports, not on
a surviving artifact, and every PROVED proof is LOST and must be re-proved.
What survives, and what was then re-verified independently: the statements
in §4 were extracted from this file verbatim into two recompile files kept
outside the scratchpad
(`~/.claude/projects/…/audit-2026-09-02/tier8-recheck/Recheck8a_Forced.lean`,
`Recheck8b_TimeSmooth.lean`) and elaborated at the pin with `lake env lean`:
8a — 29 declarations, exit 0, no errors; 8b — 59 declarations plus the §2
community definitions and the twenty classical clauses spliced verbatim from
`ClassicalEquation.lean` in place of the `[clauses 1–20]` placeholder, exit 0,
no errors. So "COMPILED" is now re-established for all 88 frozen statements;
"PROVED" is not. The smallest next move stands, re-worded: wave F0 must be
RE-PROVED against the frozen statements (one builder session was launched for
it at 13:2x under the doctrine below), not transcribed.

**BUILD LOG.** 9 Sep 2026, wave F0 BUILT: `TheoremB/ForcedTrap.lean` (318
lines; the four frozen declarations re-proved from the route notes, statements
byte-identical to §4a F0), registered in `TheoremB.lean` and `AxiomCheck.lean`,
gate GREEN 190/190 (builder, both readers, and the orchestrator each ran it),
two independent readers CLEAN (0 blockers, 0 majors; minors were wording and
observations). Reader observation carried forward to F3/F4: the force carries
no summability certificate at F0, so a non-ℓ² force has junk `en (g t) = 0`
and meets any budget — the capstones MUST export `Summable` for `g` (the
Tier-3 lesson, again). Probes persisted under
`audit-2026-09-02/tier8-build-f0/`. No tag until F1 (ladder §5a).

9 Sep 2026, wave F1 BUILT: `TheoremB/ForcedGalerkin.lean` (826 lines): the
seven frozen F1 statements byte-identical to §4a F1 (both readers and the
orchestrator checked), plus the SKELETON Ico engine form
`ns_galerkin_forced_trap_on` now compiled with the same clauses, and the
composition probe `probe_forced_zero_feeds_frozen` (the forced ODE clause at
`g = 0` reduces to the frozen unforced clause; the only compiled direction
between the chains, NOT a strengthening). Gate GREEN 199/199 (builder, both
readers, orchestrator). Two readers CLEAN (0 blockers, 0 majors). The §6a
"MUST INHABIT JOINTLY" skeleton is discharged at the Galerkin level by the
shape reader's probe (nonzero datum AND nonzero force inside the thresholds,
non-constant flow; `audit-2026-09-02/tier8-build-f1/audit-shape/`); the
capstone-level form stays with F5. Tag `t8a-forced-trap-green` laid on this
commit per the ladder.

Pin: Lean `4.31.0-rc2`, Mathlib `15a89b24`. Where the two critics of a
design disagreed, this file takes the more conservative reading and says
why (§5, §7).

Provenance: 8a is RECON 3's forced chain, 8b is RECON 1/2/4's route to
the OpenAI Comparator / Formal-Conjectures periodic solution class. The
external target is reproduced verbatim in §2. Nothing here is new
mathematics; the deliverable is machine-checking, in the small-data
regime, with constants whose status is stated per constant (§7, rule 1).

## 1. Goals and non-goals

### 1a. Tier 8a — the forced trap

**Goal.** Small data under a small mean-zero, divergence-free, real,
per-mode-continuous spectral force `g` stays trapped in a BOX for all
time: `en (c t) ≤ Es`, `ens (c t) ≤ Zs` whenever `κ·Es·Zs ≤ ν⁴`,
`G ≤ ν²·Es`, `8·G ≤ ν²·Zs`, and `en (g t) ≤ G`. Only the L² size of the
force enters (the enstrophy-side force pairing is taken against the
DISSIPATION and Young-split, so no H¹ bound on `g` is needed). Capstones:
`theorem_B_forced` (horizon form), `theorem_B_unique_forced`,
`ns_full_global_flow_forced` (eternal), and the coefficient-language
corollaries `forced_breakdown_threshold` / `forced_breakdown_threshold'`.
The route is the classical forced small-data (small-Grashof) theory
transplanted into the campaign's Galerkin chain as pure siblings — no
frozen statement is edited.

**The one new analysis brick** is a barrier lemma (a level is never
crossed if the derivative is nonpositive on a strip just above it),
replacing the unforced first-exit bootstrap because neither `E` nor `Z`
is monotone under forcing. It is already PROVED in the F0 design probe
(`barrier_forward_invariance`), together with the forced conditional
trap with witness `κ := 8·K`.

**Non-goals (8a).** No forced sibling of the Sobolev / smooth / classical
layers (that is 8b/8c territory). No H¹ or sup-norm bound on the force at
the capstone level. No decay-in-time of the force, no attractor. Forces
are per-mode CONTINUOUS in time (Picard-Lindelöf at the pin needs it);
L¹/measurable forcing is out of scope. The corollary is in the campaign's
coefficient vocabulary only — it is NOT the community's
`navier_stokes_breakdown_periodic`, not its negation, and not in real-space
form. At `g = 0` the forced capstones are NOT a strengthening of the
unforced ones (`κ_forced = 8K ≠ K`, non-strict `≤`), and must never be
described as one.

### 1b. Tier 8b — time-smoothness, then the community class inhabited

**Goal.** Close the two known gaps of the classical layer — joint `C^∞`
in `(x, t)` on the CLOSED slab `ℝ³ × [0, ∞)`, and the right derivative at
`t = 0` within `Ici 0` — and then read the flow back as a real-valued
velocity/pressure pair in the community's clock, so that the class
`NavierStokesExistenceAndSmoothnessPeriodic ν' u₀ 0 v p` is inhabited for
every `ν' > 0` and every datum in the campaign's trap class at
`ν = 2π·ν'`. Capstones: `theorem_B_time_smooth` (W1),
`theorem_B_joint_smooth` (W2), `theorem_B_community_periodic_flow` (W4,
pinned to the flow by the twenty classical clauses), and
`theorem_B_community_periodic` (W4, the community's own shape).

The route is the textbook bootstrap (differentiate the mode ODE; the
`n`-th derivative satisfies a Leibniz recurrence; window-uniform weighted
ℓ¹ at every order closes under the three operations), then a Weierstrass
M-test for `ContDiffOn` on a convex set with unique differentials, then a
real-part / clock bridge. The within-convex tsum engine is ABSENT from
Mathlib at the pin (grep-verified by two independent readers); it is not
new mathematics. Its first-order half is PROVED in
`feas-b/F1_WithinEngine.lean` (exit 0, no `sorry`, `import Mathlib` only).

**Non-goals (8b).** Analyticity in space or time (their `∞` is
`((⊤ : ℕ∞) : WithTop ℕ∞)`, not `ω`; `ProbeF_InftyOmega` read). Any bearing
on `navier_stokes_breakdown_periodic` or on the positive statement
`navier_stokes_existence_and_smoothness_periodic` for GENERAL data: the
tier delivers the latter's conclusion restricted to the trap class of data
with `f = 0` and says nothing beyond it. Forced data (`f ≠ 0`; 8a is the
prerequisite and is a separate design). Any numeric constant. Any
priority claim (§7).

## 2. The external target

### 2a. The community class, verbatim

The file `scratchpad/ProbeOpenAIStatement.lean` reproduces the community
wording (OpenAI's `ComparatorChallenges/NavierStokes.lean`, adapted from
google-deepmind/formal-conjectures; the upstream copy is
`scratchpad/fc-upstream-NavierStokes.lean`) and COMPILES at our pin
(exit 0), including the example that the rest state `(v, p) = (0, 0)`
inhabits the class at `u₀ = 0`. The six definitions the tier copies into
`TheoremB.Community` are, verbatim:

```
noncomputable
def divergence (v : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ := (fderiv ℝ v x).trace ℝ (ℝ^n)

local notation "∇⬝" => divergence

def IsOnePeriodic {α : Sort*} (f : ℝ^n → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

structure InitialVelocityCondition (u₀ : ℝ^n → ℝ^n) : Prop where
  div_free : ∀ x, ∇⬝ u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

structure InitialVelocityConditionPeriodic (u₀ : ℝ^n → ℝ^n) : Prop extends
    InitialVelocityCondition u₀ where
  isOnePeriodic : IsOnePeriodic u₀

structure ForceCondition (f : ℝ^n → ℝ → ℝ^n) : Prop where
  smooth : ContDiffOn ℝ ∞ (↿f) (Set.univ ×ˢ Set.Ici 0)

structure ForceConditionPeriodic (f : ℝ^n → ℝ → ℝ^n) : Prop extends ForceCondition f where
  isOnePeriodic : ∀ t ≥ 0, IsOnePeriodic (f · t)
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
    ‖iteratedFDerivWithin ℝ m (↿f) (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K

structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ^n → ℝ^n) (f : ℝ^n → ℝ → ℝ^n)
    (v : ℝ^n → ℝ → ℝ^n) (p : ℝ^n → ℝ → ℝ) : Prop
  extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)
```

Here `ℝ^n` is `EuclideanSpace ℝ (Fin n)`, `v : ℝ³ → ℝ → ℝ³` is
REAL-valued with position before time, `Δ` is Mathlib's
`InnerProductSpace` Laplacian (`open scoped Laplacian`), `gradient` is
Mathlib's, and `∞` is the smooth `(⊤ : ℕ∞)` because upstream has
`open ContDiff` (read).

**Diff record (house rule).** Decl-by-decl, comments/docstrings stripped:
this pass's `final/CommunityClassFinal.lean` block vs
`ProbeOpenAIStatement.lean` — IDENTICAL (re-run 9 Sep). Both vs the
upstream file — IDENTICAL except TWO lines, per the statement critic's
decl-by-decl diff (read, and the first difference confirmed by this
pass's re-run): the namespace (`NavierStokes` upstream, `TheoremB.Community`
ours) and the divergence notation (`@[inherit_doc] notation "∇⬝"` global
upstream, `local notation` in the copy). "Only the namespace line differs"
is therefore NOT exactly true and must not be written. The inhabitation
theorem is about OUR copy; the external file cannot be imported into the
gated tree, and the announcement must say so and carry this diff.

**Both upstream statements must be named.** The upstream file carries (a)
the positive statement
`navier_stokes_existence_and_smoothness_periodic (nu) (hnu : nu > 0) (u₀)
(hu₀ : InitialVelocityConditionPeriodic u₀) : ∃ v p,
NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (f := 0) v p` and (b)
the breakdown statement `navier_stokes_breakdown_periodic (nu) (hnu) :
∃ u₀ f, InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
¬ ∃ v p, …`. Our bare capstone `theorem_B_community_periodic` is literally
(a)'s conclusion restricted to data `u₀ = u₀Real c₀` with
`κ·en c₀·ens c₀ < (2πν')⁴` (f = 0, `ν' > 0` arbitrary). It says nothing
about (a) for general data and nothing about (b). Both upstream `sorry`s
are untouched. The upstream docstrings use resolution-prize language; ours
do not (§7).

### 2b. Coefficient and clock reconciliation

Our lift `u(x, t) = Σ_k c_k(t) e^{2πi k·x}` (period 1, `freq k` the raw
lattice vector) satisfies, by clause 20 of `theorem_B_smooth_classical_eq`,
`∂_t u = (ν/(2π)²) Δu − (1/2π)(u·∇)u − ∇p` with pressure from
`pressureCoeff`. In the clock `τ = t/(2π)` (Calibration ledger
`(λ, μ) = (1, 2π)`: `d(τ) = c(2πτ)`, i.e. `∂_τ = 2π ∂_t`) every term is
multiplied by `2π`: viscosity `ν/(2π)`, convection coefficient `1`,
pressure `2π·p`. Hence

- `nu' = ν/(2π)`; the smallness hypothesis becomes
  `κ·en c₀·ens c₀ < (2π·ν')⁴`;
- `vReal c x τ := toLp 2 (fun j => (uLift j (c (2π·τ)) x).re)`;
- `pReal c x τ := 2π · (pLift (c (2π·τ)) x).re`;
- `f = 0`, spelled `(f := 0)` (Pi zero) as upstream does; the design's
  `(fun _ _ => 0)` is the same term by `rfl`
  (`force_zero_spelling_rfl`, PROVED in `final/CommunityClassFinal.lean`;
  also `audit-shape/ForceZeroShape.lean`, exit 0).

The **real-part bridge**: our lift is ℂ-valued; `RealField c` makes it
real (`im_uLift_eq_zero`, PROVED in RECON 1's probe), so `Re` is the
identity on the values and the operators (their `fderiv`, `Δ`, `gradient`,
trace-divergence) are identified with our fiber/character series through
ONE first-order Fréchet bridge lemma (`fderiv_uLift_single`) applied once
or twice; `Complex.reCLM` transports both derivative kinds. The `2π`
arithmetic (`2π·ν/(2π)² = ν/(2π)`, `2π·(1/(2π)) = 1`, `2π·0 = 0`) is the
only computation.

## 3. Gap table (merged from RECON 1–4 and the critiques)

| # | Gap | Where it bites | Closed by (wave) | Status |
|---|---|---|---|---|
| G1 | Joint `C^∞` in `(x, t)` on the CLOSED slab `univ ×ˢ Ici 0` (tree: `C^p` in `x` at each `t`, `C¹` in `t` on `t > 0` only) | `velocity_smooth`, `pressure_smooth` | W1 time chain + W2 within-convex M-test | first-order engine PROVED (feas-b/F1); iterated half unprobed |
| G2 | `derivWithin (v x ·) (Ici 0) t` at `t = 0` (tree engine is `Ioo`-only) | `navier_stokes` at `t = 0` | W2 `hasDerivWithinAt_tsum_of_convex` at `E = ℝ` + W4 `hasDerivWithinAt_charSum_zero`; endpoint tool `hasDerivWithinAt_Ici_of_tendsto_deriv` (Extend.lean:108, read) | engine PROVED; assembly unbuilt |
| G3 | No `fderiv`/`HasFDerivAt` statement about `uLift` in the tree | their `fderiv v x (v x t)`, `Δ`, `gradient`, divergence | W3 `fderiv_uLift_single`, `laplacian_uLift`, `fderiv_pLift_single`; Mathlib-side reductions compiled (RECON 2 Probes A–C) | COMPILED statements |
| G4 | No reality of `convFull` / `pressureCoeff` in the tree (grep: 0 hits) | `pReal` real-valued | W3 `convFull_neg_of_realField`, `pressureCoeff_neg_of_realField`, `im_pLift_eq_zero` | COMPILED statements |
| G5 | No time-derivative of `convFull` in the tree (the TheoremBSmooth/ClassicalEquation headers say so) | the whole time bootstrap | W1 `hasDerivAt_convBil_flow` | PROVED (RECON 4 probe, re-run by the feasibility critic: exit 0, no sorry) — spec-drift to record when landed |
| G6 | Pressure has only ℓ¹ and weighted-ℓ¹ order 1 in the tree | `pressure_smooth` | W2 `summable_freq_pow_pressureCoeff` (+ `one_le_norm_freq` at `p = 0`) | COMPILED statement |
| G7 | `ns_full_global_flow_sobolev` quantifies `∀ m` OUTSIDE `∃ c` | the base case of the window class needs ALL orders for ONE flow | W1 `sobolev_growth_all_m` (per-`m` identification by `theorem_B_unique`, `flow_agree_Ici` recipe) | COMPILED statement (new, critic-required) |
| G8 | `weighted_convMaj_le` is POINTWISE in `k`, not ℓ¹ | `WindowL1.convBil` | W1 `tsum_weighted_convBil_le` (order `p+4` / `quarticKernel`), `WindowL1.majorant` | COMPILED statements (new, critic-required) |
| G9 | Slab lemma's `hA` is on `iteratedDerivWithin`; the chain gives `HasDerivAt` facts | W2 `contDiffOn_lift_slab` | `iteratedDerivWithin_eq_chain`, `exists_mode_majorant_of_windowBound` | COMPILED statements (new, critic-required); inductive step compiled in feas-b/F2 |
| G10 | Under forcing `E`, `Z` are not monotone; the Riccati first-exit bootstrap fails | 8a analysis core | F0 `barrier_forward_invariance` | PROVED (design-a/F0) |
| G11 | `trap_forward_invariance` / `conditional_trap` / Galerkin trap / PL / gluing / limit / uniqueness all quantify UNFORCED equations | every 8a level | F0–F4 siblings | statements COMPILED; F0 PROVED |
| G12 | The seam-gluing step uses the TWO-SIDED `ns_galerkin_unique_around` (GalerkinFlow.lean:804) on shifted flows via the PRIVATE `coeff_shift` | F2 | `ns_galerkin_unique_around_forced` + `coeff_shift_forced` | statement COMPILED; clone PROVED (final/ForcedFinal) — missing from the design, found by the feasibility critic |
| G13 | The FIELD-agent bounds behind Picard-Lindelöf are fourteen PRIVATE declarations (GalerkinFlow.lean:78-340) | F2 | public clones `gfield_norm_le_ball`, `gfield_lip_ball` (+ helpers, ~260 lines) | statements COMPILED; PL construction itself PROVED with the bounds abstract (Audit_ProbeB) |
| G14 | `Finset.inner_mul_le_norm_mul_norm` does not exist at the pin | F1 Cauchy-Schwarz | `real_inner_le_norm` + `Finset.sum_mul_sq_le_sq_mul_sq` | both lemmas PROVED (Audit_ProbeA) |
| G15 | `weighted_tsum_eq_sum` & co. live in `SobolevNorms`, not imported by GalerkinLocal/GalerkinFlow/FullUnique | F1 import | explicit `import TheoremB.SobolevNorms` | recorded |

## 4. Frozen interfaces (statements freeze here)

Conventions. COMPILED = the statement elaborates against the built oleans
at the pin (`lake env lean`, exit 0) with a `sorry` body; PROVED = no
`sorry`; SKELETON = not compiled by anyone. Probe paths are relative to
`scratchpad/tier8/`. The critics' required changes are applied; where a
statement changed, it was re-compiled in `final/`.

### 4b. Tier 8b

#### W1 — `TheoremB/TimeSmooth.lean` (probe `final/TimeSmoothFinal.lean`, exit 0, 21 `sorry` decls)

```
noncomputable def convBil (a b : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : Vel :=
  -(∑' l, (Complex.I * dotR (a l) (freq (k - l))) • b (k - l))

theorem convBil_self (c : (Fin 3 → ℤ) → Vel) : convBil c c = convFull c := rfl
```
COMPILED; `convBil_self` PROVED by `rfl`. The product rule needs the two
convection factors separated; `rfl`-agreement with `convFull` means no
rewriting at the ODE clause.

```
theorem hasDerivAt_convBil_flow {a a' b b' : ℝ → (Fin 3 → ℤ) → Vel} {t₀ t₁ : ℝ}
    (ha : ∀ t ∈ Ioo t₀ t₁, ∀ l, HasDerivAt (fun s => a s l) (a' t l) t)
    (hb : ∀ t ∈ Ioo t₀ t₁, ∀ l, HasDerivAt (fun s => b s l) (b' t l) t)
    {A A' B B' : (Fin 3 → ℤ) → ℝ}
    (hAmaj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖a t l‖ ≤ A l)
    (hA'maj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖a' t l‖ ≤ A' l)
    (hBmaj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖b t l‖ ≤ B l)
    (hB'maj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖b' t l‖ ≤ B' l)
    (hA : Summable A) (hA' : Summable A')
    (hB1 : Summable fun l => ‖freq l‖ * B l)
    (hB'1 : Summable fun l => ‖freq l‖ * B' l)
    {t : ℝ} (ht : t ∈ Ioo t₀ t₁) (k : Fin 3 → ℤ) :
    HasDerivAt (fun s => convBil (a s) (b s) k)
      (convBil (a t) (b' t) k + convBil (a' t) (b t) k) t
```
COMPILED here; the PROOF is closed, no `sorry`, in
`ProbeConvBilDerivFull.lean` (RECON 4; re-run by the feasibility critic,
exit 0) and lands verbatim. Reuses `hasDerivAt_tsum_of_isPreconnected`,
the `innerSL`/`restrictScalars` idiom, and a public clone of TimeLayer's
private `conv_l1_summable_le`. Majorants are on `Ioo`; restriction from
`WindowL1`'s `Icc` is trivial (`WindowL1.majorant`).

```
theorem lerayProj_add (k : Fin 3 → ℤ) (v w : Vel) :
    lerayProj k (v + w) = lerayProj k v + lerayProj k w

theorem lerayProj_smul (k : Fin 3 → ℤ) (a : ℂ) (v : Vel) :
    lerayProj k (a • v) = a • lerayProj k v

theorem HasDerivAt.lerayProj {f : ℝ → Vel} {f' : Vel} {t : ℝ} (k : Fin 3 → ℤ)
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => lerayProj k (f s)) (lerayProj k f') t
```
COMPILED. The tree has only `lerayProj_sub` / `lerayProj_continuous`
(LimitHelpers.lean:32,37). Builder may instead package `lerayProj` as a
ℂ-CLM.

```
def WindowL1 (a b : ℝ) (f : ℝ → (Fin 3 → ℤ) → Vel) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, ∀ t ∈ Icc a b,
    (Summable fun l => ‖freq l‖ ^ p * ‖f t l‖) ∧ (∑' l, ‖freq l‖ ^ p * ‖f t l‖) ≤ C
```
COMPILED. Stated on the CLOSED window `Icc` (RECON 4 used `Ioo`) because
the bounds hold at `t = 0` and the endpoint derivatives need them there.
Audit note: trivially true on an empty window (`b < a`); harmless under
`∀ b`, but `∀ n b, WindowL1 0 b (D n)` says nothing at negative `b`.

```
theorem weighted_convMaj_le₂ {p : ℕ} (hp : 1 ≤ p) {a b : (Fin 3 → ℤ) → Vel}
    (ha0 : Summable fun l => ‖a l‖)
    (haP : Summable fun l => ‖freq l‖ ^ p * ‖a l‖)
    (hb1 : Summable fun l => ‖freq l‖ * ‖b l‖)
    (hbP1 : Summable fun l => ‖freq l‖ ^ (p + 1) * ‖b l‖)
    (k : Fin 3 → ℤ) :
    ‖freq k‖ ^ p * (∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖))
      ≤ 2 ^ (p - 1) * ((∑' l, ‖freq l‖ ^ p * ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
          + (∑' l, ‖a l‖) * ∑' l, ‖freq l‖ ^ (p + 1) * ‖b l‖)

theorem norm_convBil_le {a b : (Fin 3 → ℤ) → Vel}
    (ha0 : Summable fun l => ‖a l‖)
    (hb1 : Summable fun l => ‖freq l‖ * ‖b l‖) (k : Fin 3 → ℤ) :
    ‖convBil a b k‖ ≤ ∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖)
```
COMPILED. Two-sequence forms of `weighted_convMaj_le` (TimeLayer.lean:275,
whose proof is already two-sequence inside) and `norm_convFull_le`. Both
are POINTWISE in `k`.

```
theorem tsum_weighted_convBil_le (p : ℕ) {a b : (Fin 3 → ℤ) → Vel}
    (ha : ∀ q : ℕ, Summable fun l => ‖freq l‖ ^ q * ‖a l‖)
    (hb : ∀ q : ℕ, Summable fun l => ‖freq l‖ ^ q * ‖b l‖) :
    (Summable fun k => ‖freq k‖ ^ p * ‖convBil a b k‖) ∧
    (∑' k, ‖freq k‖ ^ p * ‖convBil a b k‖)
      ≤ (∑' l, ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
        + 2 ^ (p + 3) * quarticKernel *
          ((∑' l, ‖freq l‖ ^ (p + 4) * ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
            + (∑' l, ‖a l‖) * ∑' l, ‖freq l‖ ^ (p + 5) * ‖b l‖)
```
COMPILED (new, feasibility critic). The ℓ¹ closure: pointwise bound at
order `p + 4` (`weighted_convMaj_le₂`), divide by `‖freq k‖⁴`, sum with
`summable_inv_freq_pow_four` / `quarticKernel` (TimeLayer.lean:52),
`k = 0` by the order-0 bound — the `exists_summable_nsRHS_maj`
(TimeLayer.lean:374-414) recipe. This is why `WindowL1` must carry ALL
orders. The constant `2 ^ (p + 3)` is the builder's to sharpen; any
explicit expression is acceptable at freeze so long as the conclusion is
a weighted-ℓ¹ bound by weighted sums of `a` and `b` and `quarticKernel`.

```
theorem WindowL1.majorant {a b : ℝ} {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    ∃ A : (Fin 3 → ℤ) → ℝ, Summable A ∧ (Summable fun l => ‖freq l‖ * A l) ∧
      ∀ t ∈ Icc a b, ∀ l, ‖f t l‖ ≤ A l
```
COMPILED (new, feasibility critic). Orders 4 and 5 via `le_tsum`, `k = 0`
from order 0; consumed by `WindowL1.convBil`, `hasDerivAt_convBil_flow`,
`continuousOn_convBil`.

```
theorem WindowL1.convBil {a b : ℝ} {f g : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) (hg : WindowL1 a b g) :
    WindowL1 a b (fun t => convBil (f t) (g t))

theorem WindowL1.visc {a b : ℝ} (ν : ℝ) {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    WindowL1 a b (fun t k => (-(ν * ‖freq k‖ ^ 2)) • f t k)

theorem WindowL1.lerayProj {a b : ℝ} {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    WindowL1 a b (fun t k => lerayProj k (f t k))

theorem WindowL1.add {a b : ℝ} {f g : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) (hg : WindowL1 a b g) :
    WindowL1 a b (fun t k => f t k + g t k)

theorem WindowL1.nsmul {a b : ℝ} (n : ℕ) {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    WindowL1 a b (fun t k => n • f t k)
```
COMPILED. Closure of the window class under the three operations of the
Leibniz recurrence (`norm_lerayProj_le`, NSFull.lean:139;
`tsum_weighted_convBil_le`). NOT "line-isomorphic" to the single-sequence
lemmas (the critic's correction): `WindowL1.convBil` goes through the ℓ¹
closure lemma, ~80 extra lines.

```
theorem sobolev_growth_all_m :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      c 0 = c₀ →
      (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
        Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) →
      (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀) →
      (∀ t ∈ Ici (0:ℝ), DivFree (c t)) →
      (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) →
      ∀ m : ℕ, 1 ≤ m → ∃ K, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
        Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * t))
```
COMPILED (new, feasibility critic). The producer of the ∀-`m` growth
hypothesis for ONE flow: `ns_full_global_flow_sobolev`
(TheoremBSobolev.lean:324-344, read) quantifies `∀ m` OUTSIDE `∃ c`, so
each level's witness is identified with the given flow by
`theorem_B_unique` (the `flow_agree_Ici` recipe of
TheoremBSmooth.lean:74-104, read). The capstone combines this theorem's
`κ` with its own by `max`, as `ns_full_global_flow_decay` did. The `m = 0`
case of `windowL1_of_sobolev_all`'s hypothesis is the energy clause.

```
theorem windowL1_of_sobolev_all {c : ℝ → (Fin 3 → ℤ) → Vel} {b : ℝ}
    (hsob : ∀ m : ℕ, ∃ B : ℝ, ∀ t ∈ Icc (0:ℝ) b,
      (Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
      (∑' l, ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ≤ B)
    (hzero : ∀ t ∈ Icc (0:ℝ) b, c t 0 = 0) :
    WindowL1 0 b c
```
COMPILED. Base case of the induction (`tsum_weighted_norm_le_of_bound`,
TimeLayer.lean:107; bounds valid at `t = 0` included).

```
theorem hasDerivWithinAt_mode_zero {ν : ℝ} {c : ℝ → (Fin 3 → ℤ) → Vel}
    {c₀ : (Fin 3 → ℤ) → Vel} {T : ℝ} (hT : 0 < T)
    (hinteq : ∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
    (hRHS : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k
      + lerayProj k (convFull (c s) k)) (Icc (0:ℝ) T))
    (k : Fin 3 → ℤ) :
    HasDerivWithinAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c 0 k + lerayProj k (convFull (c 0) k)) (Ici (0:ℝ)) 0
```
COMPILED. **Critics disagreed; conservative reading taken.** The
feasibility critic asked to drop it or reprove it as the `n = 0` instance
of `hasDerivWithinAt_Ici_of_tendsto_deriv` (Extend.lean:108, read: takes
`DifferentiableOn ℝ f s`, `ContinuousWithinAt f s a`, `s ∈ 𝓝[>] a`,
`Tendsto (deriv f) (𝓝[>] a) (𝓝 e)`, so `s := Ioi 0` covers `n = 0` once
`D 1 = RHS(c)` is continuous on `Ici 0`). The statement-shape critic did
not object to the interface. Decision: the STATEMENT stays frozen as
written (it removes no content and is a consumer-ready shape), but its
PROOF ROUTE is the endpoint tool, not
`intervalIntegral.integral_hasDerivWithinAt_right`'s `FTCFilter` instance
at `𝓝[Ici 0] 0`; the FTC route is an optional independent cross-check.
One endpoint tool for all orders `n ≥ 0`.

```
theorem continuousOn_convBil {a b : ℝ → (Fin 3 → ℤ) → Vel} {t₀ t₁ : ℝ}
    (ha : ∀ l, ContinuousOn (fun s => a s l) (Icc t₀ t₁))
    (hb : ∀ l, ContinuousOn (fun s => b s l) (Icc t₀ t₁))
    {A B : (Fin 3 → ℤ) → ℝ}
    (hAmaj : ∀ t ∈ Icc t₀ t₁, ∀ l, ‖a t l‖ ≤ A l)
    (hBmaj : ∀ t ∈ Icc t₀ t₁, ∀ l, ‖b t l‖ ≤ B l)
    (hA : Summable A) (hB1 : Summable fun l => ‖freq l‖ * B l) (k : Fin 3 → ℤ) :
    ContinuousOn (fun s => convBil (a s) (b s) k) (Icc t₀ t₁)
```
COMPILED. `continuousOn_tsum`, the `innerSL` idiom for `dotR`, and the
public fiber summability.

```
theorem contDiffOn_infty_of_hasDerivAt_chain {s : Set ℝ} (hs : IsOpen s)
    {g : ℕ → ℝ → Vel}
    (hchain : ∀ i, ∀ t ∈ s, HasDerivAt (g i) (g (i + 1) t) t) :
    ContDiffOn ℝ ∞ (g 0) s

theorem contDiffOn_infty_Ici_of_chain {g : ℕ → ℝ → Vel}
    (hchain : ∀ i, ∀ t ∈ Ioi (0:ℝ), HasDerivAt (g i) (g (i + 1) t) t)
    (hzero : ∀ i, HasDerivWithinAt (g i) (g (i + 1) 0) (Ici (0:ℝ)) 0)
    (hcont : ∀ i, ContinuousOn (g i) (Ici (0:ℝ))) :
    ContDiffOn ℝ ∞ (g 0) (Ici (0:ℝ))
```
COMPILED; the open-set form is PROVED, no `sorry`, in
`ProbeConvBilDeriv.lean:111-137` (RECON 4). The `Ici` form is the
boundary-inclusive version via `contDiffOn_succ_iff_derivWithin`
(carries an `n = ω → AnalyticOn` clause, closed as in the open-set proof)
and `uniqueDiffOn_Ici`.

```
theorem hasDerivAt_leibnizSum {D : ℕ → ℝ → (Fin 3 → ℤ) → Vel} (n : ℕ)
    (hchain : ∀ i, i ≤ n + 1 → ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => D i s k) (D (i + 1) t k) t)
    (hwin : ∀ i, i ≤ n + 1 → ∀ b : ℝ, WindowL1 0 b (D i))
    {t : ℝ} (ht : t ∈ Ioi (0:ℝ)) (k : Fin 3 → ℤ) :
    HasDerivAt
      (fun s => ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • convBil (D ij.1 s) (D ij.2 s) k)
      (∑ ij ∈ Finset.antidiagonal (n + 1),
        (n + 1).choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k) t
```
COMPILED (new, feasibility critic; `Finset.sum_antidiagonal_choose_succ_nsmul`
+ `Nat.choose_symm_of_eq_add`, reindexing compiled in feas-b/F4). One
generic lemma consumed by BOTH the velocity chain and the pressure chain.
**Critics offered "export `S` OR a standalone lemma"; conservative reading:
both** — the capstone exports `S` (below) AND this lemma exists, so W2's
pressure chain re-derives nothing.

W1 capstone (all 20 classical clauses spliced verbatim from
`ClassicalEquation.lean` — diffed IDENTICAL, comments stripped, 61/61
lines, by this pass; clause 21 re-frozen with `S`):

```
theorem theorem_B_time_smooth :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
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
        (∀ (m : ℕ), ∀ t ∈ Ici (0:ℝ),
          Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        (∀ t ∈ Ici (0:ℝ), c t 0 = 0) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖c t l‖) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (p : ℕ),
          ContDiff ℝ (p : ℕ∞) (uLift j (c t))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (g : Fin 3 → ℤ)
            (x : EuclideanSpace ℝ (Fin 3)),
          uLift j (c t) (x + freq g) = uLift j (c t) x) ∧
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c t k
              + lerayProj k (convFull (c t) k)) j * mFourier k x) t) ∧
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          ContinuousOn (fun s => ∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c s k
            + lerayProj k (convFull (c s) k)) j * mFourier k x) (Ioi (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (i j : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ),
          HasDerivAt
            (fun r : ℝ => ∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) * c t k j) •
              mFourier k (i.insertNth (↑r : UnitAddCircle) y))
            (∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) •
              mFourier k (i.insertNth (↑s : UnitAddCircle) y)) s) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (z : UnitAddTorus (Fin 3)),
          (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) • mFourier k z)
            = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
              (∑ i : Fin 3, ∑' k,
                ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k z)) ∧
        (∀ t ∈ Ici (0:ℝ), (Summable fun k => ‖pressureCoeff (c t) k‖) ∧
          Summable fun k => ‖freq k‖ * ‖pressureCoeff (c t) k‖) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (k : Fin 3 → ℤ) (j : Fin 3),
          (lerayProj k (convFull (c t) k)) j
            = convFull (c t) k j
              - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
              (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                * mFourier m x))
            = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull (c t) k j * mFourier k x) ∧
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
                (∑ i : Fin 3, ∑' k,
                  ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k x)
              - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
                  (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                    * mFourier m x))
              - ∑' k, (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k
                  * mFourier k x) t) ∧
        -- 21. THE TIME-DERIVATIVE CHAIN, with the Leibniz convection sum `S`
        -- exported alongside `D` (critic-required, so the pressure chain of W2
        -- does not re-derive the antidiagonal bookkeeping).  `S` is pinned to
        -- `D` by its defining clause; `D` is pinned to `c` by `D 0 = c` and the
        -- derivative clauses (`chain_unique`, compiled).
        (∃ D S : ℕ → ℝ → (Fin 3 → ℤ) → Vel,
          D 0 = c ∧
          (∀ (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ),
            S n t k = ∑ ij ∈ Finset.antidiagonal n,
              n.choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k) ∧
          (∀ n : ℕ, ∀ t ∈ Ici (0:ℝ), ∀ k,
            D (n + 1) t k = (-(ν * ‖freq k‖ ^ 2)) • D n t k + lerayProj k (S n t k)) ∧
          (∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
            HasDerivAt (fun s => D n s k) (D (n + 1) t k) t) ∧
          (∀ n : ℕ, ∀ k,
            HasDerivWithinAt (fun s => D n s k) (D (n + 1) 0 k) (Ici (0:ℝ)) 0) ∧
          (∀ n : ℕ, ∀ k, ContinuousOn (fun s => D n s k) (Ici (0:ℝ))) ∧
          (∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (D n)) ∧
          (∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
            HasDerivAt (fun s => S n s k) (S (n + 1) t k) t) ∧
          (∀ n : ℕ, ∀ k, ContinuousOn (fun s => S n s k) (Ici (0:ℝ))) ∧
          (∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (S n))) ∧
        -- 22. every mode is C^∞ in time on `Ici 0`
        (∀ k, ContDiffOn ℝ ∞ (fun s => c s k) (Ici (0:ℝ)))
```
COMPILED (`final/TimeSmoothFinal.lean`). The chain is existential but
pinned: `D 0 = c` and the derivative clauses determine `D` on `Ioi 0`
(`chain_unique`, PROVED in `design-b/VacuityIfc.lean`); `S` is pinned to
`D` by its defining clause; the recurrence clause says what the
derivatives are. Mean-zero / `RealField` / `DivFree` of `D n` are
deliberately NOT exported (derivable inside, consumed by nothing). Do
NOT freeze a `def nsChain` (it would fix an encoding without adding
content); feas-b/F4 shows the WF recursion over
`(Finset.antidiagonal n).attach` elaborates and yields the recurrence
clause verbatim, so the builder's encoding is free.

#### W2 — `TheoremB/JointSmooth.lean` + Mathlib-only `TheoremB/WithinSeries.lean` (probe `final/JointSmoothFinal.lean`, exit 0, 13 `sorry` decls)

Engine (Mathlib-only; recommended split into `TheoremB/WithinSeries.lean`,
a PR candidate like `WindowDecay.lean`):

```
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem summable_of_summable_hasFDerivWithinAt_of_convex {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ n, ∀ x ∈ s, HasFDerivWithinAt (f n) (f' n x) s x)
    (hf' : ∀ n, ∀ x ∈ s, ‖f' n x‖ ≤ u n)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    {x : E} (hx : x ∈ s) :
    Summable fun n => f n x

theorem hasFDerivWithinAt_tsum_of_convex {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ n, ∀ x ∈ s, HasFDerivWithinAt (f n) (f' n x) s x)
    (hf' : ∀ n, ∀ x ∈ s, ‖f' n x‖ ≤ u n)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => ∑' n, f n y) (∑' n, f' n x) s x

theorem hasDerivWithinAt_tsum_of_convex {s : Set ℝ} (hs : Convex ℝ s)
    {f : ι → ℝ → F} {f' : ι → ℝ → F} {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ n, ∀ x ∈ s, HasDerivWithinAt (f n) (f' n x) s x)
    (hf' : ∀ n, ∀ x ∈ s, ‖f' n x‖ ≤ u n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivWithinAt (fun y => ∑' n, f n y) (∑' n, f' n x) s x
```
**PROVED** (all three) in `feas-b/F1_WithinEngine.lean` (exit 0, no
`sorry`, `import Mathlib`, ~90 lines): direct ε/3 argument with
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`,
`tendsto_tsum_compl_atTop_zero`, `Summable.sum_add_tsum_compl`,
`HasFDerivWithinAt.fun_sum`, `hasFDerivWithinAt_iff_isLittleO`,
`smulRightL.map_tsum` for the 1-D form. Mathlib's own uniform-limit step
`hasFDerivAt_of_tendstoUniformlyOn` is OPEN-SET ONLY (UniformLimitsDeriv.lean:420;
no `Within` variant at the pin, grep by two readers). Land verbatim.

```
theorem iteratedFDerivWithin_tsum_apply_of_convex {s : Set E} (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s) {f : ι → E → F} {N : ℕ∞} {v : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : ι), ∀ x ∈ s, (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) {x : E} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ k (fun y => ∑' i, f i y) s x
      = ∑' i, iteratedFDerivWithin ℝ k (f i) s x

theorem contDiffOn_tsum_of_convex {s : Set E} (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s) {f : ι → E → F} {N : ℕ∞} {v : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : ι), ∀ x ∈ s, (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i) :
    ContDiffOn ℝ N (fun x => ∑' i, f i x) s

theorem contDiff_tsum_of_convex_univ {f : ι → E → F} {N : ℕ∞} {v : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiff ℝ N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : ι) (x : E), (k : ℕ∞) ≤ N →
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ContDiff ℝ N (fun x => ∑' i, f i x)
```
COMPILED (the third is new: the must-hold sanity corollary — at `s = univ`
the engine recovers Mathlib's `contDiff_tsum`; `convex_univ`,
`uniqueDiffOn_univ`, `iteratedFDerivWithin_univ`). Mirror of
SmoothSeries.lean:190-226 through `contDiffOn_iff_continuousOn_differentiableOn`
(stated at `n : ℕ∞`, matches `N : ℕ∞`);
`norm_fderivWithin_iteratedFDerivWithin`, `iteratedFDerivWithin_succ_eq_comp_left`,
`ContDiffOn.differentiableOn_iteratedFDerivWithin` exist (read). The
induction needs `HasFDerivWithinAt.congr` on `EqOn s` (the IH is only
pointwise ON `s`) and `ContinuousLinearEquiv.map_tsum` of the curry-left
equivalence. Instantiate `(N := ⊤)` for the challenge's `∞`.

```
noncomputable def pLift (c : (Fin 3 → ℤ) → Vel) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => ∑' k : Fin 3 → ℤ,
    pressureCoeff c k * ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))

noncomputable def pressureBil (a b : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : ℂ :=
  dotR (convBil a b k) (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ) / (2 * Real.pi * Complex.I)

theorem pressureBil_self (c : (Fin 3 → ℤ) → Vel) : pressureBil c c = pressureCoeff c := rfl

theorem summable_freq_pow_pressureCoeff {c : (Fin 3 → ℤ) → Vel}
    (hc : ∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖c l‖) (p : ℕ) :
    Summable fun k => ‖freq k‖ ^ p * ‖pressureCoeff c k‖

theorem hasDerivAt_pressureBil_flow {a a' b b' : ℝ → (Fin 3 → ℤ) → Vel} {t₀ t₁ : ℝ}
    (ha : ∀ t ∈ Ioo t₀ t₁, ∀ l, HasDerivAt (fun s => a s l) (a' t l) t)
    (hb : ∀ t ∈ Ioo t₀ t₁, ∀ l, HasDerivAt (fun s => b s l) (b' t l) t)
    {A A' B B' : (Fin 3 → ℤ) → ℝ}
    (hAmaj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖a t l‖ ≤ A l)
    (hA'maj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖a' t l‖ ≤ A' l)
    (hBmaj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖b t l‖ ≤ B l)
    (hB'maj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖b' t l‖ ≤ B' l)
    (hA : Summable A) (hA' : Summable A')
    (hB1 : Summable fun l => ‖freq l‖ * B l)
    (hB'1 : Summable fun l => ‖freq l‖ * B' l)
    {t : ℝ} (ht : t ∈ Ioo t₀ t₁) (k : Fin 3 → ℤ) :
    HasDerivAt (fun s => pressureBil (a s) (b s) k)
      (pressureBil (a t) (b' t) k + pressureBil (a' t) (b t) k) t
```
COMPILED; `pressureBil_self` PROVED by `rfl`. Spatial orders from
`‖k‖^p‖p̂_k‖ ≤ ‖k‖^(p−1)‖B_k‖/(2π)`; at `p = 0` the step DOES need
`one_le_norm_freq` (the design's "no `‖k‖ ≥ 1` needed" was wrong there;
the lemma exists). The pressure chain `P n = Q_k (S n)` with `Q_k` the
linear functional `dotR(·, freq k)/‖freq k‖²/(2πi)` consumes the exported
`S` from clause 21 and `hasDerivAt_leibnizSum`.

```
theorem norm_iteratedFDerivWithin_liftTerm_le (k : Fin 3 → ℤ) {a : ℝ → ℂ} {b : ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ico (0:ℝ) b)) {A : ℕ → ℝ}
    (hA : ∀ n : ℕ, ∀ t ∈ Ico (0:ℝ) b, ‖iteratedDerivWithin n a (Ico (0:ℝ) b) t‖ ≤ A n)
    (m : ℕ) {q : EuclideanSpace ℝ (Fin 3) × ℝ} (hq : q ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :
    ‖iteratedFDerivWithin ℝ m
        (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
          a q.2 • ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
        ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) q‖
      ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * A i * (2 * Real.pi * ‖freq k‖) ^ (m - i)
```
COMPILED. `norm_iteratedFDerivWithin_smul_le` (ContDiff/Bounds.lean:243),
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` along `fst`/`snd`
(the snd-factor bound is PROVED in feas-b/F2 as
`norm_iteratedFDerivWithin_comp_snd_le`, with `‖snd‖ ≤ 1` by
`opNorm_le_bound` — there is no `ContinuousLinearMap.norm_snd_le` at the
pin), `norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin`, and public
clones of PeriodicLift's private `norm_iteratedFDeriv_term_le` (:311) and
`hasDerivAt_cexp_mul_real` (:250).

```
theorem iteratedDerivWithin_eq_chain {a : ℝ → ℂ} {D : ℕ → ℝ → ℂ} {b : ℝ}
    (hD0 : D 0 = a)
    (hchain : ∀ n, ∀ t ∈ Ioi (0:ℝ), HasDerivAt (D n) (D (n + 1) t) t)
    (hzero : ∀ n, HasDerivWithinAt (D n) (D (n + 1) 0) (Ici (0:ℝ)) 0)
    (n : ℕ) :
    ∀ t ∈ Ico (0:ℝ) b, iteratedDerivWithin n a (Ico (0:ℝ) b) t = D n t

theorem exists_mode_majorant_of_windowBound {D : ℝ → (Fin 3 → ℤ) → ℂ} {b C₀ C₄ : ℝ}
    (h0 : ∀ t ∈ Icc (0:ℝ) b, (Summable fun l => ‖D t l‖) ∧ (∑' l, ‖D t l‖) ≤ C₀)
    (h4 : ∀ t ∈ Icc (0:ℝ) b, (Summable fun l => ‖freq l‖ ^ 4 * ‖D t l‖) ∧
      (∑' l, ‖freq l‖ ^ 4 * ‖D t l‖) ≤ C₄) :
    ∀ t ∈ Icc (0:ℝ) b, ∀ k : Fin 3 → ℤ,
      ‖D t k‖ ≤ if k = 0 then C₀ else C₄ * (‖freq k‖ ^ 4)⁻¹
```
COMPILED (both new, feasibility critic). The first identifies the scalar
chain with `iteratedDerivWithin` on the window (`iteratedDerivWithin_succ`,
`HasDerivWithinAt.congr` on `Ico`, `uniqueDiffOn_Ico`; inductive step
compiled in feas-b/F2). The second is the per-mode summable majorant the
slab lemma needs at every mixed order.

```
theorem contDiffOn_lift_slab {a : ℝ → (Fin 3 → ℤ) → ℂ} {D : ℕ → ℝ → (Fin 3 → ℤ) → ℂ}
    (hD0 : D 0 = a)
    (hchain : ∀ n, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => D n s k) (D (n + 1) t k) t)
    (hzero : ∀ n k, HasDerivWithinAt (fun s => D n s k) (D (n + 1) 0 k) (Ici (0:ℝ)) 0)
    (hcont : ∀ n k, ContinuousOn (fun s => D n s k) (Ici (0:ℝ)))
    (hbound : ∀ (n p : ℕ) (b : ℝ), ∃ C : ℝ, ∀ t ∈ Icc (0:ℝ) b,
      (Summable fun l => ‖freq l‖ ^ p * ‖D n t l‖) ∧
      (∑' l, ‖freq l‖ ^ p * ‖D n t l‖) ≤ C) :
    ContDiffOn ℝ ∞
      (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        ∑' k : Fin 3 → ℤ, a q.2 k • ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
      ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ))
```
COMPILED. Localisation to `univ ×ˢ Ico 0 b` (`Convex.prod convex_univ
(convex_Ico 0 b)`; `uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 b)`; window
identity `(univ ×ˢ Ici 0) ∩ (univ ×ˢ Iio b) = univ ×ˢ Ico 0 b` by
`Set.prod_inter_prod`, `Set.univ_inter`, `Set.Ici_inter_Iio`;
`contDiffOn_of_locally_contDiffOn` to glue — ALL PROVED in feas-b/F2).
Generic in the coefficient chain: velocity (`a := fun t k => c t k j`) and
pressure (`a := fun t k => pressureCoeff (c t) k`) both feed it.

W2 capstone (clauses 1–20: the identical block as in `theorem_B_time_smooth`,
diffed IDENTICAL by this pass; written out in full in
`final/JointSmoothFinal.lean`; clause 21 identical to W1's re-frozen chain
with `S`; clause 22 as W1). New clauses:

```
        -- 23. the pressure has every weighted ℓ¹ order
        (∀ t ∈ Ici (0:ℝ), ∀ p : ℕ,
          Summable fun k => ‖freq k‖ ^ p * ‖pressureCoeff (c t) k‖) ∧
        -- 24. JOINT C^∞ of the velocity lift on the closed slab
        (∀ j : Fin 3, ContDiffOn ℝ ∞
          (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => uLift j (c q.2) q.1)
          ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ))) ∧
        -- 25. JOINT C^∞ of the pressure lift on the closed slab
        ContDiffOn ℝ ∞
          (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => pLift (c q.2) q.1)
          ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ))
```
`theorem theorem_B_joint_smooth` — COMPILED (`final/JointSmoothFinal.lean`).
Clause 24 composed with `Complex.reCLM` and the clock CLM gives their
`velocity_smooth` shape verbatim (PROVED in feas-b/F3).

#### W3/W4 — `TheoremB/CommunityClass.lean` (probe `final/CommunityClassFinal.lean`, exit 0, 15 `sorry` decls; composition proof and `force_zero_spelling_rfl` PROVED)

`namespace TheoremB.Community` carries the six definitions of §2a
verbatim (diff record in §2a). Bridge objects:

```
noncomputable def vReal (c : ℝ → (Fin 3 → ℤ) → Vel) (x : ℝ³) (τ : ℝ) : ℝ³ :=
  WithLp.toLp 2 fun j : Fin 3 => (uLift j (c (2 * Real.pi * τ)) x).re

noncomputable def pReal (c : ℝ → (Fin 3 → ℤ) → Vel) (x : ℝ³) (τ : ℝ) : ℝ :=
  (2 * Real.pi) * (pLift (c (2 * Real.pi * τ)) x).re

noncomputable def u₀Real (c₀ : (Fin 3 → ℤ) → Vel) : ℝ³ → ℝ³ :=
  fun x => WithLp.toLp 2 fun j : Fin 3 => (uLift j c₀ x).re
```
COMPILED. Position before time, as their class; the `2π` on the pressure
is the clock change.

```
theorem fderiv_uLift_single (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (x : ℝ³) :
    fderiv ℝ (uLift j c) x (EuclideanSpace.single i 1)
      = ∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * c k j
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))

theorem laplacian_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖)
    (h2 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ 2 * ‖c k‖) (x : ℝ³) :
    Δ (uLift j c) x
      = ∑' k : Fin 3 → ℤ, (((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2)) : ℝ) : ℂ) * c k j
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))

theorem fderiv_pLift_single (i : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖pressureCoeff c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖pressureCoeff c k‖) (x : ℝ³) :
    fderiv ℝ (pLift c) x (EuclideanSpace.single i 1)
      = ∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * pressureCoeff c k
          * ∏ l : Fin 3, fourier (k l) ((x l : ℝ) : AddCircle (1 : ℝ))
```
COMPILED (`open scoped Laplacian`; `Δ` is `InnerProductSpace.instLaplacian`
at `F = ℂ`, as in RECON 2 Probe G4). The feasibility critic's cheaper
route is preferred: `contDiff_uLift` (PeriodicLift.lean:396) gives
`DifferentiableAt`, and `fderiv f x (single i 1)` is the derivative along
the coordinate line — clause 15's twisted series — via one line-derivative
lemma (`HasFDerivAt.comp_hasDerivAt` with `s ↦ x + s • single i 1`;
PeriodicLift's private `term_hasDerivAt` :149 and `norm_deriv_smul_le` :119
are the per-term facts). The Laplacian by
`laplacian_eq_iteratedFDeriv_orthonormalBasis` + `iteratedFDeriv_two_apply`
+ `fderiv_clm_apply` (RECON 2 Probe A, compiled) with
`EuclideanSpace.basisFun`, and `laplacian_symbol` (Calibration.lean:186).

```
theorem convFull_neg_of_realField {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (k : Fin 3 → ℤ) :
    convFull c (-k) = conjVel (convFull c k)

theorem pressureCoeff_neg_of_realField {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (k : Fin 3 → ℤ) :
    pressureCoeff c (-k) = (starRingEnd ℂ) (pressureCoeff c k)

theorem im_uLift_eq_zero {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖) (j : Fin 3) (x : ℝ³) :
    (uLift j c x).im = 0

theorem im_pLift_eq_zero {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (x : ℝ³) :
    (pLift c x).im = 0

theorem isOnePeriodic_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) :
    IsOnePeriodic (uLift j c)

theorem isOnePeriodic_pLift (c : (Fin 3 → ℤ) → Vel) :
    IsOnePeriodic (pLift c)

theorem divergence_uReal_eq_zero {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (hdiv : DivFree c)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) (x : ℝ³) :
    Community.divergence (fun y : ℝ³ => (WithLp.toLp 2 fun j : Fin 3 => (uLift j c y).re : ℝ³)) x
      = 0
```
COMPILED; `im_uLift_eq_zero` and `isOnePeriodic_uLift` are PROVED in
RECON 1's `ProbeRealAndTime.lean` / `ProbePeriodic.lean` (exit 0, per
their reports). Reality of `convFull`/`pressureCoeff` is new (tsum
reindexing `l ↦ −l` with `freq_neg` and `conjVel`). Divergence via RECON 2's
`divergence_eq_sum` (`LinearMap.trace_eq_sum_inner` + `EuclideanSpace.basisFun`),
the first-order bridge, and `DivFree`.

```
theorem initialVelocityConditionPeriodic_u₀Real {c₀ : (Fin 3 → ℤ) → Vel}
    (hsob : ∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2)
    (h0 : c₀ 0 = 0) (hreal : RealField c₀) (hdiv : DivFree c₀) :
    InitialVelocityConditionPeriodic (n := 3) (u₀Real c₀)

theorem forceConditionPeriodic_zero :
    ForceConditionPeriodic (n := 3) (f := 0)
```
COMPILED, with the force spelled `(f := 0)` (statement critic; the
re-compile confirms the named-argument form elaborates on the structure).
`contDiff_uLift` + `summable_weighted_norm` (SobolevNorms.lean:220) +
`contDiff_infty` / `contDiff_euclidean` (RECON 2 Probes G1/G2);
`contDiffOn_const` and `iteratedFDerivWithin` of a constant (`C := 0`
works for every `m`, `K`).

```
theorem hasDerivWithinAt_charSum_zero {ν : ℝ} {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hzero : ∀ k, HasDerivWithinAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c 0 k + lerayProj k (convFull (c 0) k)) (Ici (0:ℝ)) 0)
    (hchain : ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t)
    {b : ℝ} (hb : 0 < b) {u : (Fin 3 → ℤ) → ℝ} (hu : Summable u)
    (hmaj : ∀ t ∈ Icc (0:ℝ) b, ∀ k,
      ‖(-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)‖ ≤ u k)
    (hs₀ : Summable fun k => ‖c 0 k‖) (j : Fin 3) (x : UnitAddTorus (Fin 3)) :
    HasDerivWithinAt (fun s => ∑' k, c s k j * mFourier k x)
      (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c 0 k
        + lerayProj k (convFull (c 0) k)) j * mFourier k x) (Ici (0:ℝ)) 0

theorem derivWithin_vReal_Ici {c : ℝ → (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hpos : ∀ (j : Fin 3) (x : ℝ³), ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun s => uLift j (c s) x) (uLift j (g t) x) t)
    (hzero : ∀ (j : Fin 3) (x : ℝ³),
      HasDerivWithinAt (fun s => uLift j (c s) x) (uLift j (g 0) x) (Ici (0:ℝ)) 0)
    (x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    derivWithin (vReal c x ·) (Ici (0:ℝ)) τ
      = WithLp.toLp 2 fun j : Fin 3 =>
          (2 * Real.pi) * (uLift j (g (2 * Real.pi * τ)) x).re
```
COMPILED. The first is `hasDerivWithinAt_tsum_of_convex` at `E = ℝ`,
`s = Ico 0 b`, then `HasDerivWithinAt.mono_of_mem_nhdsWithin` to `Ici 0`;
`D 1 0 k = RHS(c₀) k` from clause 21's recurrence at `n = 0`
(`antidiagonal 0 = {(0,0)}`, `choose 0 0 = 1`, `convBil_self`); the
per-mode majorant from `WindowL1 0 b (D 1)` via `WindowL1.majorant`. The
second: `derivWithin_of_mem_nhds` (`Ici_mem_nhds`) for `τ > 0`;
`HasDerivWithinAt.derivWithin` (`uniqueDiffWithinAt_Ici`) at `τ = 0`;
`HasDerivWithinAt.scomp_of_eq` for the clock (its point is the FIRST
explicit argument — pin trap, feas-b/F3); `Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt`
(instance-path trap, §7); component packing through
`PiLp.continuousLinearEquiv` / `hasDerivWithinAt_pi`. Clock-transported
one-sided derivative with real part PROVED in feas-b/F3.

W4 capstones (clauses 1–20: the identical block, diffed IDENTICAL by this
pass, written out in full in `final/CommunityClassFinal.lean`):

```
theorem theorem_B_community_periodic_flow :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        [clauses 1–20 of theorem_B_smooth_classical_eq, VERBATIM] ∧
        -- 21. THE COMMUNITY CLASS, inhabited by this flow
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) (ν / (2 * Real.pi))
          (u₀Real c₀) (f := 0) (vReal c) (pReal c)
```
COMPILED (`(f := 0)` spelling applied and re-compiled). Docstring (statement
critic, applied in the probe): "the rest state is not a witness for
nonzero data (`exists_nonzero_admissible_datum`, compiled); at `c₀ = 0` it
is, as it must be. The class carries no uniqueness clause: uniqueness of
the coefficient flow behind `vReal c` is `theorem_B_unique`, whose
hypothesis set is exactly clauses 1–7 (FullUnique.lean:327-345, read)."

```
theorem theorem_B_community_periodic :
    ∃ κ, 0 < κ ∧ ∀ {ν' : ℝ}, 0 < ν' → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      κ * en c₀ * ens c₀ < (2 * Real.pi * ν') ^ 4 →
      InitialVelocityConditionPeriodic (n := 3) (u₀Real c₀) ∧
      ForceConditionPeriodic (n := 3) (f := 0) ∧
      ∃ (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
        NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (u₀Real c₀)
          (f := 0) v p
```
COMPILED — and PROVED from the (sorry'd) pinned capstone plus
`initialVelocityConditionPeriodic_u₀Real` and `forceConditionPeriodic_zero`
at `ν := 2π·ν'` (the composition probe; only `mul_div_cancel_left₀` for
`(2π·ν')/(2π) = ν'`). Their `navier_stokes` clause carries a trailing
`+ 0` with `f := 0`; the assembly rewrites it (`add_zero`), it is not
restated. The `∃ v p` is existence only (the class has no uniqueness
clause).

```
theorem force_zero_spelling_rfl :
    (fun (_ : ℝ³) (_ : ℝ) => (0 : ℝ³)) = (0 : ℝ³ → ℝ → ℝ³) := rfl
```
PROVED (`final/CommunityClassFinal.lean`; also `audit-shape/ForceZeroShape.lean`).

### 4a. Tier 8a

#### F0 — `TheoremB/ForcedTrap.lean` (probe `design-a/DesignA_F0_ForcedTrap.lean`, exit 0, NO `sorry`; imports RiccatiTrap + SpectralNorms + EnergyDecay)

```
theorem barrier_forward_invariance {T M M' : ℝ} (hMM' : M < M') {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ico 0 T)) (hd : DifferentiableOn ℝ f (Ioo 0 T))
    (h0 : f 0 ≤ M)
    (h' : ∀ t ∈ Ioo (0:ℝ) T, M < f t → f t < M' → deriv f t ≤ 0) :
    ∀ t ∈ Ico (0:ℝ) T, f t ≤ M
```
PROVED (~70 lines; `le_of_deriv_nonpos` RiccatiTrap.lean:54,
`IsClosed.csInf_mem`/`csSup_mem`). Pin trap: `push_neg` is deprecated at
4.31.0-rc2 (warning); land with `push Not`.

```
theorem forced_trap_forward_invariance {T Es Zs : ℝ} (hZs : 0 < Zs)
    {E Z : ℝ → ℝ}
    (hEc : ContinuousOn E (Ico 0 T)) (hZc : ContinuousOn Z (Ico 0 T))
    (hEd : DifferentiableOn ℝ E (Ioo 0 T)) (hZd : DifferentiableOn ℝ Z (Ioo 0 T))
    (hE' : ∀ t ∈ Ioo (0:ℝ) T, Es ≤ E t → deriv E t ≤ 0)
    (hZ' : ∀ t ∈ Ioo (0:ℝ) T, E t ≤ Es → Zs ≤ Z t → Z t ≤ 2 * Zs → deriv Z t ≤ 0)
    (h0E : E 0 ≤ Es) (h0Z : Z 0 ≤ Zs) :
    ∀ t ∈ Ico (0:ℝ) T, E t ≤ Es ∧ Z t ≤ Zs
```
PROVED (two applications of the barrier lemma: energy first, then
enstrophy on the strip `Zs ≤ Z ≤ 2Zs` using the energy bound; `0 < Zs`
makes the strip nonempty).

```
theorem forced_conditional_trap :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Ico (0:ℝ) T, c t 0 = 0) →
      (∀ t ∈ Ico (0:ℝ) T, Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) →
      (∀ t ∈ Ico (0:ℝ) T, en (g t) ≤ G) →
      ContinuousOn (fun t => en (c t)) (Ico 0 T) →
      ContinuousOn (fun t => ens (c t)) (Ico 0 T) →
      DifferentiableOn ℝ (fun t => en (c t)) (Ioo 0 T) →
      DifferentiableOn ℝ (fun t => ens (c t)) (Ioo 0 T) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => en (c s)) t ≤
        -(2 * ν) * ens (c t) + 2 * Real.sqrt (en (c t)) * Real.sqrt (en (g t))) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
        -(2 * ν) * dis (c t) +
          2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
            (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) +
          2 * Real.sqrt (dis (c t)) * Real.sqrt (en (g t))) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Ico (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs
```
PROVED (~75 lines; witness `κ := 8·K` from `master_inequality`
SpectralNorms.lean:964; `en_le_ens` EnergyDecay.lean:34 (Vel-only, hence
the theorem is stated for `Vel`), `ens_sq_le_en_mul_dis` :144, `ens_le_dis`
:595, Young by `nlinarith`). Non-strict `κ·Es·Zs ≤ ν⁴` (barriers never need
strictness). Only `en (g t)` enters.

```
theorem forced_thresholds_inhabited {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ Es Zs G : ℝ, 0 < G ∧ 0 ≤ Es ∧ 0 < Zs ∧
      κ * Es * Zs ≤ ν ^ 4 ∧ G ≤ ν ^ 2 * Es ∧ 8 * G ≤ ν ^ 2 * Zs
```
PROVED (witness `Es := ν²`, `Zs := ν²/κ`, `G := ν⁴/(8κ+8)`).

#### F1 — `TheoremB/ForcedGalerkin.lean` (imports GalerkinLocal + ForcedTrap + **SobolevNorms explicitly**; probe `design-a/DesignA_F1_F4_Interfaces.lean`, exit 0, 18 `sorry` decls; the two pairing lemmas re-stated in `final/ForcedFinal.lean`, exit 0)

```
theorem force_energy_pairing_le {S : Finset (Fin 3 → ℤ)} {c g : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hgsupp : ∀ k, k ∉ S → g k = 0) :
    (∑ k ∈ S, 2 * inner ℝ (g k) (c k)) ≤
      2 * Real.sqrt (en c) * Real.sqrt (en g)

theorem force_enstrophy_pairing_le {S : Finset (Fin 3 → ℤ)} {c g : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hgsupp : ∀ k, k ∉ S → g k = 0) :
    (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (g k) (c k))) ≤
      2 * Real.sqrt (dis c) * Real.sqrt (en g)
```
COMPILED as statements; both PROVED in `Audit_ProbeA_CS_Extend.lean`
(28 + 35 lines) with `real_inner_le_norm` (InnerProductSpace/Basic.lean:472)
+ `Finset.sum_mul_sq_le_sq_mul_sq` (Algebra/Order/BigOperators/Ring/Finset.lean:159)
+ `Real.sqrt_le_sqrt`/`sqrt_sq`/`sqrt_mul`; the design's
`Finset.inner_mul_le_norm_mul_norm` does NOT exist at the pin (grep).

```
theorem galerkin_forced_trap_on :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)}, (0 : Fin 3 → ℤ) ∉ S →
      ∀ {c F g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, en (g t) ≤ G) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + F t k) t) →
      (∀ t ∈ Ioo (0:ℝ) T, (∑ k ∈ S, 2 * inner ℝ (F t k) (c t k)) ≤
        2 * Real.sqrt (en (c t)) * Real.sqrt (en (g t))) →
      (∀ t ∈ Ioo (0:ℝ) T,
        (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k))) ≤
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) +
        2 * Real.sqrt (dis (c t)) * Real.sqrt (en (g t))) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Ico (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs
```
COMPILED. Sibling of `galerkin_conditional_trap_on` (GalerkinLocal.lean:755;
its pairing hypotheses are already in the Cauchy-Schwarzed finite-sum form
quoted here). `Icc`-window form only. `g` enters only through `en (g t)`
inside the pairing hypotheses (a non-ℓ² `g` weakens the hypotheses; no
vacuity). Reuses `hasDerivAt_weighted_finset_sum_sq` (SobolevNorms.lean:69),
`weighted_tsum_eq_sum` (:55), `summable_weighted_of_support` (:61).

```
theorem divFree_propagates_on_forced {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    {c g : ℝ → (Fin 3 → ℤ) → Vel}
    (hgdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (g t))
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t)
    (h0 : DivFree (c 0)) : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t)

theorem realField_propagates_on_forced {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    (hSsym : ∀ k ∈ S, -k ∈ S) {c g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0)
    (hgreal : ∀ t ∈ Icc (0:ℝ) T, RealField (g t))
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t)
    (h0real : RealField (c 0)) : ∀ t ∈ Icc (0:ℝ) T, RealField (c t)
```
COMPILED. Replays of `divFree_propagates_on` (:235, ~105 lines) and
`realField_propagates_on` (:354, ~120 lines + its three private `pp*`
conjVel helpers, ~15 lines, to clone) with `defect_vanishes_on'` (:146),
`dotR_lerayProj_freq` (NSGalerkin.lean:579).

```
theorem ns_galerkin_forced_trap_icc :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) →
      ∀ {c g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → g t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, RealField (g t)) →
      (∀ t ∈ Icc (0:ℝ) T, DivFree (g t)) →
      (∀ t ∈ Icc (0:ℝ) T, en (g t) ≤ G) →
      RealField (c 0) → DivFree (c 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs
```
COMPILED. Sibling of `ns_galerkin_trap_zero_data_icc` (GalerkinFlow.lean:623,
~107-line endpoint replay, not ~40). An `Ico` engine form
`ns_galerkin_forced_trap_on` (sibling of GalerkinLocal.lean:984) precedes
it — SKELETON (not compiled as a separate statement; same clauses on
`Ico`). RHS spelled INLINE as `… + g t k` (no `galRHSForced` def) so that
`simpa` converts it to the frozen ODE at `g = 0`
(`probe_forced_zero_feeds_frozen`, PROVED). Reuses `convGal_energy_pairing`
(NSGalerkin.lean:288), `convGal_enstrophy_pairing` (:467),
`inner_lerayProj_of_divFree` (:528).

```
theorem ns_galerkin_unique_on_forced {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    {c₁ c₂ g : ℝ → (Fin 3 → ℤ) → Vel}
    (hs₁ : ∀ (t : ℝ) k, k ∉ S → c₁ t k = 0)
    (hs₂ : ∀ (t : ℝ) k, k ∉ S → c₂ t k = 0)
    (hODE₁ : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convGal S (c₁ t) k) + g t k) t)
    (hODE₂ : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convGal S (c₂ t) k) + g t k) t)
    (h0 : ∀ k, c₁ 0 k = c₂ 0 k) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₂ t k
```
COMPILED. Replay of `ns_galerkin_unique_on` (GalerkinLocal.lean:885, ~100
lines; uses only the public `defect_vanishes_on'` and
`two_flow_forcing_bound` :541). The force cancels (`probeB_force_cancels`,
PROVED: `rw [smul_sub]; abel`), so NO hypothesis on `g`.

#### F2 — `TheoremB/ForcedGalerkinFlow.lean` (imports GalerkinFlow + ForcedGalerkin; probes `design-a/DesignA_F1_F4_Interfaces.lean`, `Audit_ProbeB_PL_Forced.lean`, `final/ForcedFinal.lean`)

```
noncomputable def gfieldForced (ν : ℝ) (S : Finset (Fin 3 → ℤ))
    (g : ℝ → (Fin 3 → ℤ) → Vel) (t : ℝ) (x : GState S) : GState S :=
  gfield ν S x + gres S (g t)
```
COMPILED (the tier's only new definition; `gres` is GalerkinFlow.lean:35,
`gfield` :40 — the design had them swapped).

```
theorem gfield_norm_le_ball {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (M : ℝ) (hM : 0 ≤ M) (x : GState S) (hx : ‖x‖ ≤ M) :
    ‖gfield ν S x‖ ≤ ν * fldFRQ S * M + 2 * (S.card : ℝ) * fldFB S * M ^ 2

theorem gfield_lip_ball {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (M : ℝ) (hM : 0 ≤ M) (x y : GState S) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖gfield ν S x - gfield ν S y‖ ≤
      (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * M) * ‖x - y‖
```
COMPILED (new, feasibility critic): the PUBLIC clones of the private
`fldGfield_norm_le` (:273) / `fldGfield_lip` (:310), stated with the public
`fldFRQ` / `fldFB` (:71, :75). Their fourteen private helpers
(`fldFRQ_nonneg` … `fldConv_sub_le`, GalerkinFlow.lean:78-340) must be
cloned public too (~260 lines; do NOT drop `private` in the frozen file —
the SobolevNorms public-clone pattern is the precedent).

```
theorem gflow_local_exists_forced {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (B Gs : ℝ) (hB : 0 ≤ B) (hGs : 0 ≤ Gs)
    {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hgc : ∀ k, Continuous fun t => g t k)
    (hgb : ∀ t k, ‖g t k‖ ≤ Gs) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x₀ : GState S), ‖x₀‖ ≤ B → ∀ t₀ : ℝ,
      ∃ α : ℝ → GState S, α t₀ = x₀ ∧
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt α (gfieldForced ν S g t (α t)) (Icc (t₀ - ε) (t₀ + ε)) t
```
COMPILED. The PL construction itself is PROVED in
`Audit_ProbeB_PL_Forced.lean` (`probeB_PL_forced`, ~55 lines) with the
field bounds abstract: the pin's time-dependent `IsPicardLindelof`
(PicardLindelof.lean:79-88, four fields `lipschitzOnWith` /
`continuousOn` / `norm_le` / `mul_max_le`, read) by the anonymous
constructor — `continuousOn := (continuous_const.add (continuous_pi fun s
=> hgc s.val)).continuousOn`, `norm_le` by `norm_add_le` +
`pi_norm_le_iff_of_nonneg` for `‖gres S (g t)‖ ≤ Gs`, `L := L₀ + Gs + 1`,
`r = 0` — then `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`
(#check confirmed). Force on ALL of `ℝ` here by design (PL windows may
leave `[0, T]`).

```
theorem gflow_to_coeff_forced {ν : ℝ} {S : Finset (Fin 3 → ℤ)}
    {g : ℝ → (Fin 3 → ℤ) → Vel} (hgsupp : ∀ (t : ℝ) k, k ∉ S → g t k = 0)
    {α : ℝ → GState S} {a b : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (gfieldForced ν S g t (α t)) (Icc a b) t) :
    (∀ (t : ℝ) k, k ∉ S → gext S (α t) k = 0) ∧
    (∀ t ∈ Ioo a b, ∀ k, HasDerivAt (fun s => gext S (α s) k)
      ((-(ν * ‖freq k‖ ^ 2)) • gext S (α t) k +
        lerayProj k (convGal S (gext S (α t)) k) + g t k) t)
```
COMPILED; PROVED in `Audit_ProbeB_PL_Forced.lean` (`probeB_gflow_to_coeff_forced`;
off-box case needs `lerayProj_sub` from LimitHelpers since `brLerayProj_zero`
:434 is private — hence `import TheoremB.FullUnique` or LimitHelpers).

```
theorem ns_galerkin_local_existence_forced {ν : ℝ} (hν : 0 < ν)
    (S : Finset (Fin 3 → ℤ)) (B Gs : ℝ) (hB : 0 ≤ B) (hGs : 0 ≤ Gs)
    {g : ℝ → (Fin 3 → ℤ) → Vel} (hgsupp : ∀ (t : ℝ) k, k ∉ S → g t k = 0)
    (hgc : ∀ k, Continuous fun t => g t k) (hgb : ∀ t k, ‖g t k‖ ≤ Gs) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ k, k ∉ S → c₀ k = 0) → (∀ k, ‖c₀ k‖ ≤ B) → ∀ t₀ : ℝ,
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c t₀ = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t
```
COMPILED (~30 lines of glue; `gext_gres` :53).

```
theorem coeff_shift_forced {c : ℝ → (Fin 3 → ℤ) → Vel} {v : Vel}
    {k : Fin 3 → ℤ} {τ t : ℝ}
    (h : HasDerivAt (fun s => c s k) v (τ + t)) :
    HasDerivAt (fun s => c (τ + s) k) v t
```
PROVED (`final/ForcedFinal.lean`; clone of the private `coeff_shift` :486).

```
theorem ns_galerkin_unique_around_forced {ν a b : ℝ} (hν : 0 ≤ ν) (ha : a ≤ 0)
    (hb : 0 ≤ b) {S : Finset (Fin 3 → ℤ)}
    {c₁ c₂ g : ℝ → (Fin 3 → ℤ) → Vel}
    (hs₁ : ∀ (t : ℝ) k, k ∉ S → c₁ t k = 0)
    (hs₂ : ∀ (t : ℝ) k, k ∉ S → c₂ t k = 0)
    (hODE₁ : ∀ t ∈ Icc a b, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convGal S (c₁ t) k) + g t k) t)
    (hODE₂ : ∀ t ∈ Icc a b, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convGal S (c₂ t) k) + g t k) t)
    (h0 : ∀ k, c₁ 0 k = c₂ 0 k) :
    ∀ t ∈ Icc a b, ∀ k, c₁ t k = c₂ t k
```
COMPILED (new; the interface the design MISSED, found by the feasibility
critic): the seam-gluing induction of `ns_galerkin_global_wellposed`
(GalerkinFlow.lean:804) applies the TWO-SIDED `ns_galerkin_unique_around`
(:522, ~93-line clean replay) to the SHIFTED flows `c (Tn + ·)`, whose
force is `g (Tn + ·)`; no hypothesis on `g`.

```
theorem ns_galerkin_global_wellposed_forced :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) →
      ∀ {g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ (t : ℝ) k, k ∉ S → g t k = 0) → (∀ t, RealField (g t)) → (∀ t, DivFree (g t)) →
      (∀ t, en (g t) ≤ G) → (∀ k, Continuous fun t => g t k) →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel}, (∀ k, k ∉ S → c₀ k = 0) →
      RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      ∀ T : ℝ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs) ∧
        (∀ c' : ℝ → (Fin 3 → ℤ) → Vel, (∀ (t : ℝ) k, k ∉ S → c' t k = 0) →
          (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c' s k)
            ((-(ν * ‖freq k‖ ^ 2)) • c' t k + lerayProj k (convGal S (c' t) k) + g t k) t) →
          c' 0 = c₀ → ∀ t ∈ Icc (0:ℝ) T, ∀ k, c' t k = c t k)
```
COMPILED. Replay of `ns_galerkin_global_wellposed` (:730, ~200 lines) with
seam bound `√Es` from the box and force sup bound `Gs := √G`
(`coeff_le_sqrt_en` :475 on the truncated force).

```
theorem ns_galerkin_global_flow_forced :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) →
      ∀ {g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ (t : ℝ) k, k ∉ S → g t k = 0) → (∀ t, RealField (g t)) → (∀ t, DivFree (g t)) →
      (∀ t, en (g t) ≤ G) → (∀ k, Continuous fun t => g t k) →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel}, (∀ k, k ∉ S → c₀ k = 0) →
      RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs) ∧
        (∀ T : ℝ, ∀ c' : ℝ → (Fin 3 → ℤ) → Vel,
          (∀ (t : ℝ) k, k ∉ S → c' t k = 0) →
          (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c' s k)
            ((-(ν * ‖freq k‖ ^ 2)) • c' t k + lerayProj k (convGal S (c' t) k) + g t k) t) →
          c' 0 = c₀ → ∀ t ∈ Icc (0:ℝ) T, ∀ k, c' t k = c t k)
```
COMPILED. Replay of `ns_galerkin_global_flow` (:928, ~150 lines; parity
with the unforced chain; not strictly required by F3).

#### F3 — `TheoremB/ForcedTheoremB.lean` (imports FullUnique + TheoremBGlobal + FlowBounds + ForcedGalerkinFlow)

```
theorem flow_mode_mem_modeSet_forced {ν E Z Gs T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E)
    (hZ0 : 0 ≤ Z) (hGs : 0 ≤ Gs)
    {S : Finset (Fin 3 → ℤ)} {c g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ (t : ℝ) k, k ∉ S → c t k = 0)
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t)
    (hen : ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ E)
    (hens : ∀ t ∈ Icc (0:ℝ) T, ens (c t) ≤ Z)
    (hg : ∀ t ∈ Icc (0:ℝ) T, ∀ k, ‖g t k‖ ≤ Gs) (k : Fin 3 → ℤ) :
    ∃ f : C(Icc (0:ℝ) T, Vel), (∀ t : Icc (0:ℝ) T, f t = c t.val k) ∧
      f ∈ modeSet T (Real.sqrt E) (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
        2 * (Real.sqrt E * Real.sqrt Z) + Gs))
```
COMPILED (~60 lines; `galRHS_norm_le` FlowBounds.lean:29 + `norm_add_le`;
`flow_mode_mem_modeSet` :86).

```
theorem integral_equation_limit_forced {ν E Z Gs T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E)
    (hZ0 : 0 ≤ Z) (hGs : 0 ≤ Gs) (hT : 0 ≤ T)
    {S : ℕ → Finset (Fin 3 → ℤ)} {F : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    {u g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ n (t : ℝ) k, k ∉ S n → F n t k = 0)
    (hODE : ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => F n s k)
      ((-(ν * ‖freq k‖ ^ 2)) • F n t k + lerayProj k (convGal (S n) (F n t) k) +
        truncate (S n) (g t) k) t)
    (hEn : ∀ n, ∀ t ∈ Icc (0:ℝ) T, en (F n t) ≤ E)
    (hZn : ∀ n, ∀ t ∈ Icc (0:ℝ) T, ens (F n t) ≤ Z)
    (hbox : ∀ k : Fin 3 → ℤ, k ≠ 0 → ∀ᶠ n in Filter.atTop, k ∈ S n)
    (hu : ∀ l, TendstoUniformlyOn (fun n t => F n t l) (fun t => u t l)
      Filter.atTop (Icc (0:ℝ) T))
    (hgc : ∀ k, ContinuousOn (fun s => g s k) (Icc (0:ℝ) T))
    (hgb : ∀ t ∈ Icc (0:ℝ) T, ∀ k, ‖g t k‖ ≤ Gs) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k : Fin 3 → ℤ, k ≠ 0 →
      u t k = u 0 k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • u s k + lerayProj k (convFull (u s) k) + g s k)
```
COMPILED (~110 lines; `integral_equation_limit` TheoremBGlobal.lean:16
replayed; `truncate_eq_of_mem` NSFull.lean:262 + `hbox` for the
eventually-equal force; dominated-convergence majorant gains `Gs`;
per-mode continuity of `g` gives measurability; `hasDerivAt_of_integral_eq`
LimitPassage.lean:300 wants `ContinuousOn` of the integrand on `Icc 0 T`,
which per-mode continuity of `g` supplies).

```
theorem galerkin_family_forced :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      (∀ t, RealField (g t)) → (∀ t, DivFree (g t)) →
      (∀ t, Summable (fun l => ‖g t l‖ ^ 2)) → (∀ t, en (g t) ≤ G) →
      (∀ k, Continuous fun t => g t k) →
      ∀ (R : ℕ) (T : ℝ), ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = truncate (boxS R) c₀ ∧
        (∀ (t : ℝ) k, k ∉ boxS R → c t k = 0) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k +
            lerayProj k (convGal (boxS R) (c t) k) + truncate (boxS R) (g t) k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)
```
COMPILED (~70 lines; `en_truncate_le` NSFull.lean:274 makes the thresholds
uniform in `R`; `ens_truncate_le`, `realField_truncate`, `divFree_truncate`
:288,302,319). THE COMPOSITION PROBE of F2 against a real producer — to be
compiled at the END of F2, after the FIELD clone lands (critic).

```
theorem theorem_B_forced :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) → (∀ t ∈ Ici (0:ℝ), DivFree (g t)) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) →
      (∀ t ∈ Ici (0:ℝ), en (g t) ≤ G) →
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) →
      ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)
```
COMPILED. Clause-list diff against `theorem_B_cont` (FullUnique.lean:100)
by reading AND by the compiled `probe_frozen_flow_inhabits_forced_clauses`:
all seven clauses present, `+ g` in the integral equation and the mode
ODE, box replaces descent + κ-trap. Force hypotheses on `Ici 0`
(physically honest); the Galerkin layer takes `ℝ` — bridged by
`g̃ t := g (max t 0)` in ~10 lines (`probeA_extend`, PROVED:
`(hgc k).comp_continuous (continuous_id.max continuous_const) (fun t =>
le_max_right t 0)`, agreement on `Ici 0` by `max_eq_left`). F3 checklist
(critic): (i) `‖g t k‖ ≤ √G` from `Summable.le_tsum` (5 lines;
`coeff_le_sqrt_en` needs finite support, so it applies to the truncated
force, not `g`); (ii) per-mode continuity of `truncate (boxS R) (g̃ t) k`
by cases on membership; (iii) the `g̃ → g` swap in the integral clause by
`intervalIntegral.integral_congr` on `uIcc 0 t`. Mean-zero of `g` IS
needed here (the `k = 0` clause, `convFull_zero_of_divFree`).

#### F4 — `TheoremB/ForcedUnique.lean` (imports ForcedTheoremB)

```
theorem theorem_B_unique_forced :
    ∀ {ν E Z T : ℝ}, 0 < ν → 0 ≤ T →
    ∀ {c₀ : (Fin 3 → ℤ) → Vel} {c₁ c₂ g : ℝ → (Fin 3 → ℤ) → Vel},
    (∀ k, ContinuousOn (fun s => g s k) (Icc (0:ℝ) T)) →
    c₁ 0 = c₀ → c₂ 0 = c₀ →
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
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k) + g s k)) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k) + g s k)) →
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₂ t k
```
COMPILED. Sibling required at the STATEMENT level (verified by reading
FullUnique.lean:327-360: the frozen `theorem_B_unique` quantifies over
UNFORCED integral-equation flows) though the mathematics is unchanged: the
force cancels at the section derivative (:475 `h4`, one `rw [smul_sub];
abel`); the frozen `hzero` (:397-421) is replaced by equal zero-mode
integrals `c t 0 = c₀ 0 + ∫ g s 0` (`probeA_forced_zero_mode`, PROVED;
~12 lines, not ~5) so `pairing_absorbed`'s zero-MODE side condition
`a 0 = b 0` (PairingBound.lean:253) holds for the difference; NO mean-zero
hypothesis on `g`. Hypothesis list = the frozen one plus per-mode
continuity of `g` (parity). ~440-line replay.

```
theorem ns_full_global_flow_forced :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) → (∀ t ∈ Ici (0:ℝ), DivFree (g t)) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) →
      (∀ t ∈ Ici (0:ℝ), en (g t) ≤ G) →
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs)
```
COMPILED (~157-line replay of `ns_full_global_flow` :766; parity: the
frozen statement carries no uniqueness clause either). The derived clause
`κ·en·ens ≤ ν⁴` is deliberately NOT restated (`κ_forced = 8K ≠ K`).

```
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
      ∃ t ∈ Ici (0:ℝ), ν ^ 2 * Es < en (g t) ∨ ν ^ 2 * Zs < 8 * en (g t)
```
COMPILED — and PROVED from the (sorry'd) `theorem_B_forced` (`by_contra`
+ `push Not`, `G := min (ν²Es) (ν²Zs/8)`, ~20 lines of glue).
**Docstring corrected (statement critic, applied):** the hypothesis is
"the forced periodic system from trap-class data admits NO flow in the
class that STAYS INSIDE THE BOX `(Es, Zs)` on `[0, T]`" — weaker than
non-existence (a regular flow that exits the box satisfies it), so the
theorem IMPLIES the breakdown reading rather than being it. Call it the
"Comparator-adjacent corollary, coefficient language" in prose. When
`κ·en c₀·ens c₀ > ν⁴` no admissible box exists and the statement is
vacuous — the unforced trap's own boundary, a docstring remark, not a
formal disjunct.

```
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
      ∃ t ∈ Ici (0:ℝ), ν ^ 2 * en c₀ < en (g t) ∨ ν ^ 2 * ens c₀ < 8 * en (g t)
```
COMPILED — PROVED from the box form at the natural box (4 lines). Requires
`0 < ens c₀` (excludes `c₀ = 0`; the box form covers that case with any
`Zs > 0` — one docstring line). Same docstring correction ("no flow
confined to the natural box").

#### F5 — `TheoremB/ForcedProbe.lean` (gated like `ModesProbe.lean`)

Transcriptions of the compiled probes listed in §6 (8a): the four design
probes, the two shape-audit files, and the joint nonzero inhabitation
(SKELETON — see §6).

## 5. Wave plan (estimates re-based on the feasibility critics' measured replay sizes; where design and critic disagreed the LARGER figure is taken)

Campaign average is ≈2000 lines per wave; every wave ships with a
compiled composition probe against a real producer (Tier-7 rule), and no
tag is laid before an independent adversarial reader (Tier-7 lesson).
8a and 8b touch disjoint files and may be built in separate sessions;
they must not be built in the same chat.

### 5a. Tier 8a — order F0 → F1 → F2 → F3 → F4 → F5 (≈3,300 lines, 8–9 sessions)

| Wave | File | Delivers (reuses) | Risk | Lines / sessions |
|---|---|---|---|---|
| F0 | `ForcedTrap.lean` | `barrier_forward_invariance`, `forced_trap_forward_invariance`, `forced_conditional_trap` (κ := 8K; `master_inequality`, `en_le_ens`, `ens_sq_le_en_mul_dis`, `ens_le_dis`, `le_of_deriv_nonpos`), `forced_thresholds_inhabited` — ALL already PROVED in the probe; transcription + `push Not` + gate | LOW | ~260 / 1 |
| F1 | `ForcedGalerkin.lean` | the two Cauchy-Schwarz lemmas (PROVED in Audit_ProbeA; `real_inner_le_norm`, `Finset.sum_mul_sq_le_sq_mul_sq`), `galerkin_forced_trap_on` (replay of `galerkin_conditional_trap_on`), `divFree_propagates_on_forced` (105), `realField_propagates_on_forced` (120 + 3 private `pp*` helpers), `ns_galerkin_forced_trap_on` + `_icc` (107-line endpoint replay of GalerkinFlow:623-730), `ns_galerkin_unique_on_forced` (100); composition probe `probe_forced_zero_feeds_frozen` in-tree; explicit `import TheoremB.SobolevNorms` | LOW-MED | ~700 / 1–2 |
| F2 | `ForcedGalerkinFlow.lean` (+ optional `GalerkinFieldBounds.lean`) | public FIELD clone (~260: fourteen helpers → `gfield_norm_le_ball`, `gfield_lip_ball`), `gfieldForced`, `gflow_local_exists_forced` (PL by the 4-field constructor as in `probeB_PL_forced`), `gflow_to_coeff_forced` (PROVED in probe), `ns_galerkin_local_existence_forced`, `coeff_shift_forced` (PROVED), **`ns_galerkin_unique_around_forced`** (~95, replay of GalerkinFlow:522-615), `ns_galerkin_global_wellposed_forced` (200, seam bound √Es), `ns_galerkin_global_flow_forced` (150); composition probe = `galerkin_family_forced`'s Galerkin input, compiled at the END of the wave | MED — densest wave, two sessions with no slack | ~950 / 2 |
| F3 | `ForcedTheoremB.lean` | `flow_mode_mem_modeSet_forced` (60), `integral_equation_limit_forced` (110), `galerkin_family_forced` (70; THE composition probe of F2), `theorem_B_forced` (≈230 replay of `theorem_B_cont` + the checklist glue ≈60: `√G` from `Summable.le_tsum`, truncated-force continuity, `integral_congr` swap; Ici→ℝ bridge ≈10), in-tree `probe_frozen_flow_inhabits_forced_clauses` | MED | ~620 / 2 |
| F4 | `ForcedUnique.lean` | `theorem_B_unique_forced` (440-line replay of FullUnique:327-766; ~12 lines differ: `h1ode`/`h2ode` with the `+g` integrand, the `(A+g)−(B+g)` cancellation in `h4`, the zero-mode equality), `ns_full_global_flow_forced` (157), `forced_breakdown_threshold` + `'` (glue PROVED in probe); audit line `κ_forced = 8K` | MED (size only) | ~650 / 2 |
| F5 | `ForcedProbe.lean` + prose | §6 (8a) transcriptions incl. `ShapeAudit_*`; the joint nonzero inhabitation (needs `en probeForce = 2`, `ens probeForce = 2`, ~40 lines, uncompiled); tags `t8a-forced-trap-green` (F0–F1), `t8a-forced-B-green` (F3), `t8a-complete` — each only after an independent reader | LOW | ~150 / 1 |

### 5b. Tier 8b — order W1 → W2 → W3 → W4 (≈4,300 lines, 11–14 sessions)

| Wave | File | Delivers (reuses) | Risk | Lines / sessions |
|---|---|---|---|---|
| W1 | `TimeSmooth.lean` | `convBil`/`convBil_self`; `hasDerivAt_convBil_flow` (RECON 4 probe, ~120, PROVED); `lerayProj_add/smul`, `HasDerivAt.lerayProj` (40); `WindowL1`, `weighted_convMaj_le₂`, `norm_convBil_le`, **`tsum_weighted_convBil_le`** (ℓ¹ closure via order p+4 / `quarticKernel`, the `exists_summable_nsRHS_maj` recipe, ~80), **`WindowL1.majorant`** (50), the five closure lemmas (public clone of TimeLayer's private `conv_l1_summable_le`; ~250); **`sobolev_growth_all_m`** (per-`m` identification by `theorem_B_unique`, `flow_agree_Ici` recipe; ~150); `windowL1_of_sobolev_all` (120; `tsum_weighted_norm_le_of_bound`); `hasDerivWithinAt_mode_zero` (via `hasDerivWithinAt_Ici_of_tendsto_deriv`, 60), `continuousOn_convBil` (60); `contDiffOn_infty_of_hasDerivAt_chain` (PROVED, RECON 4) + `_Ici_of_chain` (60); **`hasDerivAt_leibnizSum`**; the chain construction (WF recursion over `(antidiagonal n).attach`, `decreasing_by` via `Finset.antidiagonal.fst_le/snd_le`, feas-b/F4; endpoint derivatives for `n ≥ 1` by the endpoint tool; ~300); `theorem_B_time_smooth` (150); composition probe: clause 21 discharges `contDiffOn_lift_slab`'s hypotheses; prose: strike the "no time-derivative of convFull" sentence from the TheoremBSmooth/ClassicalEquation headers (spec-drift) | LOW-MED (pin trap: `convert … using 1` on Vel-valued `HasDerivAt` yields a `WithLp` goal — use `HasDerivAt.congr_deriv`) | ~1300 / 3 |
| W2 | `WithinSeries.lean` (Mathlib-only) + `JointSmooth.lean` | first-order engine (PROVED, feas-b/F1, land verbatim, ~90); `iteratedFDerivWithin_tsum_apply_of_convex`, `contDiffOn_tsum_of_convex`, `contDiff_tsum_of_convex_univ` (~150; `contDiffOn_iff_continuousOn_differentiableOn`, `HasFDerivWithinAt.congr`, `ContinuousLinearEquiv.map_tsum`); `pLift`, `pressureBil`, `summable_freq_pow_pressureCoeff`, `hasDerivAt_pressureBil_flow`, the pressure chain via exported `S` (~250); `norm_iteratedFDerivWithin_liftTerm_le` (~250; clones of PeriodicLift's private term lemmas); **`iteratedDerivWithin_eq_chain`**, **`exists_mode_majorant_of_windowBound`** (~60); `contDiffOn_lift_slab` (~300; localisation PROVED in feas-b/F2); `theorem_B_joint_smooth` (150); composition probe: clause 24 ∘ `reCLM` ∘ clock CLM = their `velocity_smooth` (PROVED, feas-b/F3) | **MED** — critics disagreed (design MED-HIGH, feasibility LOW-MED because the first-order engine is proved); conservative reading: the ITERATED half (`contDiffOn_tsum_of_convex`) is unprobed, so the wave stays MED, not LOW-MED. Fallback rung if it stalls: joint `C^∞` on the OPEN slab via the open-set mirror, honestly labelled — a ladder rung, NOT a substitute (their `ContDiffOn` is on the closed slab) | ~1300 / 3 |
| W3 | `CommunityClass.lean` part 1 | `TheoremB.Community` (six defs, byte-copied; diff record §2a); `vReal`/`pReal`/`u₀Real`; `fderiv_uLift_single`, `laplacian_uLift`, `fderiv_pLift_single` (~250; line-derivative route); `convFull_neg_of_realField`, `pressureCoeff_neg_of_realField`, `im_uLift_eq_zero` (PROVED), `im_pLift_eq_zero` (~120); `isOnePeriodic_uLift` (PROVED) / `_pLift` (20); `divergence_uReal_eq_zero` (60); `initialVelocityConditionPeriodic_u₀Real` (60), `forceConditionPeriodic_zero` (40); audit probe `u₀Real (testDatum ε) ≠ 0` (PROVED, CheapWitness) | LOW-MED | ~700 / 2 |
| W4 | `CommunityClass.lean` part 2 | `hasDerivWithinAt_charSum_zero` (80), `derivWithin_vReal_Ici` (120; feas-b/F3 traps), `theorem_B_community_periodic_flow` (~600: per-component `navier_stokes` composes three operator bridges, the torus↔ℝ³ transport `uLift_eq_charSum` PeriodicLift.lean:231 / `exists_fiber`, real parts of products via `im_uLift_eq_zero` + `Complex.re_ofReal_mul`, RECON 2's `convection_component` / `gradient_apply_eq_fderiv_single` / `laplacian_apply_component`, the `2π` arithmetic; `div_free`, `initial_condition` (`2π·0 = 0`), `velocity_smooth`/`pressure_smooth` from clauses 24/25 ∘ `reCLM` ∘ clock CLM, periodicity), `theorem_B_community_periodic` (15; composition PROVED); §6 (8b) probes in-tree; diff the three 20-clause blocks against ClassicalEquation.lean:104-170 AND the six defs against `ProbeOpenAIStatement.lean`; independent adversarial reader BEFORE the tag | MED (assembly scale) | ~1000 / 3 |

Fallback ladder (each rung taggable and honest): 8b-v1 = W1
(`t8b-time-smooth-green`); 8b-v2 = + W2 (`t8b-joint-smooth-green`);
8b-v3 = W3 + W4 (`t8b-community-green`). 8a: `t8a-forced-trap-green`
(F0–F1), `t8a-forced-B-green` (F3), `t8a-complete`.

## 6. Vacuity / must-fail probe register

### 6b. Tier 8b

- MUST INHABIT — PROVED (`design-b/VacuityIfc.lean`, exit 0, no `sorry`;
  re-read by both critics): `exists_nonzero_admissible_datum` — for every
  `κ, ν > 0` the shear datum `testDatum ε = ε·e₂` on modes `±e₁` with
  `ε = ν/√(2(κ+1))` is nonzero, all Sobolev levels summable, mean-zero,
  real, div-free, and `κ·en·ens = κν⁴/(κ+1)² < ν⁴`. Every 8b capstone's
  hypothesis set is satisfied by a NONZERO datum.
- MUST INHABIT, NON-CONSTANT — PROVED (`shear_flow_ode`): `convFull
  (testDatum ε) = 0` identically and `c t := exp(−νt) • testDatum ε`
  satisfies the mode ODE clause with `c 0 ≠ 0` and `c` non-constant.
- MUST FAIL — PROVED as compiled NEGATIONS (`audit-shape/CheapWitness.lean`,
  exit 0, no `sorry`; the statement critic's replacement for "attempt and
  watch it fail"): `const_flow_fails_ode` (the constant witness violates
  clause 6 on `testDatum ε`, `ε ≠ 0`, `ν > 0`), `uLift_testDatum_zero`
  (`uLift 1 (testDatum ε) 0 = 2ε`), `u₀Real_testDatum_ne_zero`,
  `rest_pair_fails_class` (`v := 0` fails `initial_condition` for every
  `nu, f, p`). Land these in W3/W4's probe file.
- CHAIN PINNED — PROVED (`chain_unique`): two chains with `D 0 = E 0 = c`
  agree on `Ioi 0` at every order; the `∃ D S` in clauses 21 has at most
  one `D` on `t > 0`, and `S` is defined by `D`.
- CONSISTENCY — PROVED (`rest_state_chain`): the zero flow with the zero
  chain satisfies the recurrence/derivative/right-derivative/continuity
  clauses (the clause set is satisfiable).
- COMPOSITION — PROVED (`final/CommunityClassFinal.lean`,
  `theorem_B_community_periodic`): the bare capstone follows from the
  pinned one + the two datum-side lemmas at `ν := 2π·ν'`.
- SLICE GENUINENESS — PROVED (`CheapWitness.lean`,
  `differentiableWithinAt_slice_of_velocity_smooth`,
  `differentiableAt_space_slice_of_velocity_smooth`): under
  `velocity_smooth` the class's `derivWithin` and `fderiv` are genuine
  derivatives, so the clause cannot be gamed by a non-differentiable `v`
  with junk-valued `0` derivatives.
- MUST HOLD (W2 audit, SKELETON): `contDiff_tsum_of_convex_univ` — the
  engine at `s = univ` recovers `contDiff_tsum`; and dropping `hs`/`hs'`
  from `contDiffOn_tsum_of_convex` must NOT be provable (prose check).
- BYTE-IDENTITY — re-run by this pass: the 20-clause blocks of the three
  8b capstones in `final/` are IDENTICAL to ClassicalEquation.lean's block
  with comments stripped (61/61 lines each). **Critics differed on whether
  comment lines count; conservative reading: they do** — the three dropped
  comment lines ("every Sobolev level survives…", "the flow stays
  mean-zero", "weighted ℓ¹ at every order") are restored at freeze so the
  block is character-identical. The six community definitions vs
  `ProbeOpenAIStatement.lean`: IDENTICAL (re-run); vs upstream: §2a.
- NOT PROBED (unverified): a time-constant NONZERO witness
  `v x t := u₀Real c₀ x` for the BARE class on the shear datum; ruling it
  out needs the Laplacian bridge. The pinned form excludes it via clause 6.
- KNOWN (from `ProbeOpenAIStatement.lean`): the rest state inhabits the
  class at `u₀ = 0`, so a capstone stated only for `u₀ = 0` would be
  empty; the frozen capstones quantify over an arbitrary admissible datum.

### 6a. Tier 8a

- MUST INHABIT — PROVED (`design-a/DesignA_F0_ForcedTrap.lean`):
  `forced_thresholds_inhabited` — a strictly positive force budget exists
  for every `κ, ν > 0`.
- MUST INHABIT — PROVED (`design-a/DesignA_Vacuity_NonzeroForce.lean`, exit
  0): `probe_nonzero_force_admissible` — the pair-mode force `probeForce`
  (modes `±e₁` carrying `EuclideanSpace.single 1 1`) is mean-zero,
  `RealField`, `DivFree`, ℓ², per-mode continuous, and `≠ 0`.
- MUST INHABIT — PROVED (`DesignA_F1_F4_Interfaces.lean`):
  `probe_frozen_flow_inhabits_forced_clauses` (the frozen `theorem_B_cont`
  witness satisfies the forced seven-clause list at `g = 0` for every box
  containing the data — the 2 Sep house rule discharged by compilation),
  `probe_forced_zero_feeds_frozen`, `probe_constant_force_admissible`.
- MUST FAIL — **reworded (statement critic) and PROVED**
  (`audit-shape/ShapeAudit_ConstantWitness.lean`, exit 0, no `sorry`): each
  of the two equation clauses INDEPENDENTLY refutes the constant witness
  (`constant_witness_fails_integral_clause`: at `t = 1`, `k = e₁` the
  integral of the constant force is `auditV ≠ 0`;
  `constant_witness_fails_ode_clause`: `HasDerivAt.unique` against
  `hasDerivAt_const`), while it PASSES all five non-equation clauses for
  every `Es ≥ 0`, `Zs ≥ 0`, `T` (`constant_witness_passes_nonequation_clauses`).
  Removing BOTH, and only both, equation clauses makes it provable. The
  design's "removing EITHER clause must make the constant witness provable"
  was mis-specified and is withdrawn.
- MUST FAIL at `g = 0` — PROVED (`audit-shape/ShapeAudit_UnforcedConstantWitness.lean`):
  `constant_witness_fails_ode_clause_unforced` — for every `ν > 0` the
  constant witness `c t := auditForce` (real shear pair, `convFull
  auditForce = 0`, `‖freq e₁‖² = 1`) violates the mode-ODE clause.
- CONSISTENCY (design-level, recorded): at `g = 0` the forced capstone
  with box `(en c₀, ens c₀)` needs `8K·en c₀·ens c₀ ≤ ν⁴` while the frozen
  trap needs `K·en c₀·ens c₀ < ν⁴`; the forced results must never be
  described as implying or strengthening the unforced ones. The compiled
  direction is frozen ⇒ forced clause list (`probe_frozen_flow_inhabits_forced_clauses`).
- MUST INHABIT JOINTLY — SKELETON (F5, uncompiled): small nonzero data AND
  nonzero force inside the thresholds, `c₀ := ε·probeForce`,
  `g := δ·probeForce` with explicit `ε, δ` (needs `en probeForce = 2`,
  `ens probeForce = 2`; `auditForce_cases`, `norm_freq_auditE1_sq` are
  reusable). Until it lands the 8a hypotheses are known inhabited
  separately (thresholds; force) and jointly only at `g = 0`.

## 7. Audit register

Claim-wording rules (binding on every docstring, header, tag message and
announcement sentence of this tier):

1. **Constants.** Never the bare two-word phrase (the adjective "explicit"
   directly before "constants"); always say of what form and how exported. 8b: "`κ` and the
   inherited Sobolev growth constants are of explicit form, exported as
   compiled existentials; the window constants of the time-derivative
   chain (`WindowL1`, `hbound`, the `u`-majorants) are UNTRACKED
   existentials produced by the Leibniz induction" — the design's blanket
   phrase overclaimed and is withdrawn. 8a: "`κ_forced = 8·K` is of
   explicit form up to the lattice-kernel sum `C_K`, exported as a compiled
   existential; the force thresholds `G ≤ ν²·Es`, `8·G ≤ ν²·Zs` are literal
   expressions". No numeric value of any constant anywhere.
2. **No resolution-prize language** (neither the prize's name nor the
   institute's, no verb of resolution, no priority superlatives — no claim of
   being the first to machine-check anything), even though the upstream
   docstrings use such language. The statement critic's grep of the design probes for the
   banned-word list (its report carries the list; it covers the bare
   constants phrase, the prize and institute names, the priority
   superlatives, and claims of newness) returned no hits. Re-grep before
   every tag; this file is written to return no hits itself.
3. **Priority hedged and named**: leray-hopf, HeliCorgi, Miller; OpenAI and
   Alpöge-Buckmaster now too. Nothing here is new mathematics: the
   bootstrap, the M-test, the real-part bridge, the barrier lemma and the
   small-Grashof regime are textbook. The within-convex tsum engine is
   "absent from Mathlib at the pin (grep-verified), not new mathematics" —
   never "genuinely new".
4. **Name both upstream statements** (§2a) and position the 8b result as
   the POSITIVE statement's conclusion restricted to the trap class with
   `f = 0`; say it touches neither upstream `sorry`. The 8a corollary is
   "Comparator-adjacent, coefficient language", with the corrected
   hypothesis wording ("no flow confined to the box", §4a F4).
5. **Existence only** for `theorem_B_community_periodic` (the class has no
   uniqueness clause); point to `theorem_B_unique` via clauses 1–7 of the
   pinned form.
6. **Proposed announcement sentence (user's call, and NOT before W4
   ships):** "for data in the campaign's small class, OUR copy of the
   community's periodic solution class
   `NavierStokesExistenceAndSmoothnessPeriodic (ν/(2π)) u₀ 0 v p` is
   inhabited by the eternal flow (compiled); this is the conclusion of
   the upstream positive statement restricted to that data class with
   `f = 0`; both upstream statements are untouched."

Textbook sources (cited, not ours; NO copy on this machine; theorem
numbers UNVERIFIED and to be filled by a reader with the books, hedged
until then): Temam, *Navier-Stokes Equations: Theory and Numerical
Analysis*, Ch. III (strong solutions; small data with forcing);
Robinson-Rodrigo-Sadowski, *The Three-Dimensional Navier-Stokes Equations*
(CUP 2016), Ch. 6–7 (strong solutions, small data, smoothness of strong
solutions) and the forced/attractor chapters; Constantin-Foias,
*Navier-Stokes Equations*, Ch. 10; Foias-Manley-Rosa-Temam, *Navier-Stokes
Equations and Turbulence* (CUP 2001), Ch. II (Grashof number).

Statement-shape facts to carry:

- The ten `∃ κ` of the 8a chain (and the three of 8b) are unlinked by
  statement — each theorem re-chooses its own, the house pattern; "κ" in
  the corollaries means "the κ of `theorem_B_forced`" by proof, not by
  statement.
- The 8a integral-equation clause is non-degenerate ONLY because per-mode
  continuity of `g` is a hypothesis (a non-integrable integrand makes
  Mathlib's `∫` vanish and the clause collapse to `c t k = c₀ k`). If a
  later tier weakens the force to measurable/L¹-in-time, the clause list
  must gain an explicit `IntervalIntegrable` clause or the constant-witness
  check must be re-run.
- `galerkin_forced_trap_on`'s `g` is a phantom (enters only via `en (g t)`
  in hypotheses); the capstones' `Summable (‖g t l‖²)` is what keeps
  `en (g t) ≤ G` from being trivially true.
- `WindowL1 a b f` is trivially true on an empty window.
- Byte-identity rule extended: it covers the INSTANTIATION too (`(f := 0)`
  spelling, the compiled `rfl` bridge), and comment lines (conservative
  reading, §6b).
- Spec-drift to record when W1 lands: the TheoremBSmooth / ClassicalEquation
  headers' sentence "the campaign does not have a time-derivative of
  convFull" becomes false; strike it in the same commit.
- Deliberate 8a statement decisions: force hypotheses on `Ici 0` in the
  capstones, `ℝ` in the Galerkin layer (bridge ~10 lines) — KEEP;
  `0 < Zs` — KEEP (degenerate box buys nothing); non-strict
  `κ·Es·Zs ≤ ν⁴` — KEEP (stronger theorem); derived clause
  `κ·en (c t)·ens (c t) ≤ ν⁴` — NOT exported (no silently strengthened
  constant); `Vel`-only statements (because `en_le_ens` is `Vel`-only) —
  KEEP, only `Vel` consumers exist.

Pin traps measured in this tier's probes (carry into every builder brief):

- `le_or_lt` gone; `pow_le_pow_left₀/right₀`; `Summable.tsum_finsetSum`;
  protected `Summable.tsum_*`; `abs_add → abs_add_le`; on ℂ
  `Summable.mul_norm` and `tsum_mul_right` LOOP at whnf (use
  `Summable.mul_of_nonneg` over ℝ and `tsum_mul_left`); `Equiv.tsum_eq`
  needs its function pinned; `ContinuousLinearMap.map_tsum` for components;
  the component-derivative idiom `((EuclideanSpace.proj (𝕜 := ℂ)
  j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt`; `set_option … in`
  BEFORE the docstring; check exit codes, not output.
- `i ≤ ∞` side goals with `∞ = ((⊤:ℕ∞):WithTop ℕ∞)` in
  `iteratedFDerivWithin_comp_right` / `ContDiffAt.of_le` /
  `norm_iteratedFDerivWithin_smul_le` are NOT closed by `simp`;
  `exact_mod_cast le_top` closes all three (feas-b/F2).
- `Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt` + `simpa` fails on ℝ
  with an `RCLike.toInnerProductSpaceReal.toModule` vs `Semiring.toModule`
  path: state the target with `Complex.reCLM` applied explicitly, rewrite
  the value, close by `exact` (feas-b/F3).
- `contDiff_uLift`'s `ContDiff ℝ (p : ℕ∞)` vs the `2 : WithTop ℕ∞` literal
  `ContDiffAt.laplacian_CLM_comp_left` expects: `exact_mod_cast`.
- `HasDerivWithinAt.scomp_of_eq` takes the point as its FIRST explicit
  argument.
- WF recursion over `(antidiagonal n).attach`: after `simp_wf` the
  `decreasing_by` goals are `ij.1 ≤ n` / `ij.2 ≤ n`, closed by
  `Finset.antidiagonal.fst_le/snd_le ij.2`; `rw [nsChain]` leaves a
  beta-redex — `dsimp only` before `congr 2`, then `Finset.sum_attach`.
- `tendsto_tsum_compl_atTop_zero` uses the subtype `{x // x ∉ s}` while
  `Summable.sum_add_tsum_compl` uses `↑(↑s)ᶜ` — defeq, `exact` bridges.
- `convert … using 1` on Vel-valued `HasDerivAt` produces a `WithLp`
  instance goal — use `HasDerivAt.congr_deriv`; `HasDerivAt.fun_sum` on
  `Vel` elaborates.
- `push_neg` deprecated (warning) — `push Not`. `EuclideanSpace.single_apply`
  deprecated — `PiLp.single_apply`.
- `Finset.inner_mul_le_norm_mul_norm` does not exist; `real_inner_le_norm`
  + `Finset.sum_mul_sq_le_sq_mul_sq` do.
- `weighted_tsum_eq_sum` / `summable_weighted_of_support` /
  `hasDerivAt_weighted_finset_sum_sq` need `import TheoremB.SobolevNorms`;
  `lerayProj_sub` needs LimitHelpers (via FullUnique).
- Line-number slips in the designs, corrected: `gres` :35 / `gfield` :40;
  `fldGfield_norm_le` :273; `fldGfield_lip` :310.
- Private declarations that must be CLONED, never un-privated: GalerkinFlow
  `fldFRQ_nonneg … fldGfield_lip` (14), `brDotR_zero_left`, `brLerayProj_zero`,
  `coeff_shift`, `ep_tsum_eq_sum`; GalerkinLocal `l_weighted_tsum_eq_sum`,
  `l_summable_weighted`, `l_hasDerivAt_weighted_sum`, `ppConjVel_*`, `tf*`;
  TimeLayer `conv_l1_summable_le`; PeriodicLift `term_eq_comp` :282,
  `term_hasDerivAt` :149, `norm_deriv_smul_le` :119,
  `norm_iteratedFDeriv_term_le` :311, `hasDerivAt_cexp_mul_real` :250;
  TheoremBSmooth `flow_agree_Ici` :78.

Honesty ledger for this pass:

| Grade | Items |
|---|---|
| Compiled by THIS pass (exit 0) | `final/TimeSmoothFinal.lean` (21 sorry decls), `final/JointSmoothFinal.lean` (13), `final/CommunityClassFinal.lean` (15; composition proof + `force_zero_spelling_rfl` PROVED), `final/ForcedFinal.lean` (5; `coeff_shift_forced` PROVED); the 20-clause and six-definition diffs (Python, comments stripped) |
| Read by this pass, not re-compiled | every `.out`/`.log` of `design-a/`, `design-b/`, `feas-b/`, `audit-shape/`, `ProbeA.out`, `ProbeB.out` (exit lines and `sorry` counts as the critics reported); `ProbeOpenAIStatement.lean`; the upstream file's positive statement (:275-278); TheoremBSobolev.lean:300-350, GalerkinFlow.lean:268-330, TheoremBSmooth.lean:70-106, ClassicalEquation.lean:88-104, TimeLayer's `weighted_convMaj_le` / `exists_summable_nsRHS_maj` statements |
| Reported by the critics, not verified here | every Mathlib signature and line number they cite; the RECON probes' exit codes; the decl-by-decl upstream diff beyond its first differing line |
| Derived, not compiled | the effort re-estimates; the wording rules; the SKELETON items |
| Cited, not ours | the textbook sources above (theorem numbers unverified) |
| Not run | `scripts/check_axioms.sh`; no tracked `.lean` file or script touched by this pass (`git status --short` was empty at its start; the two later working-tree changes belong to another session, see the status header) |

## 8. Open blockers

None blocks the first wave. Open items, each with the decision this
blueprint takes and what remains the user's call:

1. **Announcement wording** (rule 6 of §7) — user's call; not before W4.
   Whether to quote the upstream file's commit hash alongside the prose
   diff — user's call (the diff itself is mandatory).
2. **Chain encoding in W1** — builder's call at build time (WF recursion
   over the antidiagonal, compiled in feas-b/F4, or a prefix-vector
   recursion); no `def nsChain` is frozen.
3. **W2 engine file split** — decided: the Mathlib-only
   `TheoremB/WithinSeries.lean` (PR candidate; record the within-uniform-limit
   generalisation of `UniformLimitsDeriv` in `upstreaming-dossier.md` only).
4. **`hasDerivWithinAt_mode_zero`** — decided: keep the statement, prove
   via the endpoint tool (§4b W1).
5. **Comment lines in byte-identity** — decided: restore them at freeze.
6. **Joint nonzero inhabitation of the 8a hypotheses** — SKELETON, F5.
7. **A generic "difference-flow" uniqueness engine** (one engine consumed by
   both the frozen and the forced uniqueness) — deferred: a NEW engine
   sibling costing the same lines once; pays only if a forced smooth layer
   (8c) also needs uniqueness.
8. **Textbook theorem numbers** — need a reader with the books.
9. **Order of 8a vs 8b** — independent files; the smallest next move is
   8a F0 (`TheoremB/ForcedTrap.lean`: four declarations already PROVED in
   the probe; one session; gate-checkable immediately). 8b W1 may start in
   a SEPARATE session. Neither in the same chat.
10. **Mean-zero / RealField / DivFree of `D n`** — not exported; add only
    if the pressure chain or an audit wants reality of `D n`.

Smallest next move: 8a wave F0 — transcribe
`design-a/DesignA_F0_ForcedTrap.lean` into `TheoremB/ForcedTrap.lean`
(`push Not` for the deprecated `push_neg`), run the gate, and hand it to
an independent reader before any tag.
