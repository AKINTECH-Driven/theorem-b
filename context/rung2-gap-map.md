# Rung 2 Reconnaissance: the road to a formal Theorem B

Session of 26 August 2026 (second session). Konstantinos (command), Claude (execution).
Discipline in force: decompose until something passes, grade every claim, counterfeit nothing.
Companion artifact: `NSSkeleton.lean` v2 (quantitative discrete Theorem A, kernel-checked,
empty axiom set, sha256 `05fe4f73e715ed3d0f3db5c769c1af65c167c4ac038091b8ca720b64ac26f5e4`).

---

## 1. The landscape, verified from source today

**uda-lab/leray-hopf @ `e704400`** (cloned, read; 112 Lean files, 46,630 lines;
toolchain `leanprover/lean4:v4.31.0-rc2`, Mathlib pinned to master `15a89b24`).
Four capstone theorems: Leray-Hopf weak existence, finite-horizon and global-in-time,
on both the torus and whole space (`exists_lerayHopf_torus3`, `exists_lerayHopf_r3`,
`exists_global_lerayHopf_torus3`, `exists_global_lerayHopf_r3`). The project's own
scope document states both capstone cones are kernel-only (standard axioms
`propext` / `Classical.choice` / `Quot.sound`, zero project axioms, no `sorryAx`),
pinned by a deterministic guard script `scripts/check-axioms-live.sh`. The 173+
textual `sorry`s in the tree live in `Experimental` and scaffolding files outside
both capstone cones, tracked in `docs/STATUS.md`. Explicit non-claims, in their own
words: no smoothness or higher regularity beyond energy-class properties, no
uniqueness, no non-uniqueness. **The regularity half of the theory is open by the
project's own declaration.**

Infrastructure inside the capstone cones that a regularity campaign can lean on:
Galerkin ODE solver, Rellich-Kondrachov spatial compactness, Aubin-Lions time
diagonalization, Helmholtz/curl density via a Fourier route, Parseval layer,
trace-energy (energy inequality) machinery, proof-carrying trilinear convection
forms, Mazur weak-limit closure.

Method note, verified from `CLAUDE.md` / `AGENTS.md` / `docs/agent-roles.md`: the
repo is built by an orchestrated Claude Code agent team (`lean-architect` →
`lean-planner` → `lean-coder` → `lean-prover`, read-only reviewers fanned out in
parallel, adversarial Codex review, preflight script before any change is reported
done, campaign doctrine binding the orchestrator). Deterministic gates before model
judgment, rulebook as data. The frontier of NSE formalization is being pushed with
exactly the architecture we already run for proposals.

**lean-dojo/LeanMillenniumPrizeProblems @ `fd52071`** (cloned, read).
`MillenniumNavierStokes.ClayNavierStokes : Prop` formalizes Fefferman's Clay
statement as the disjunction of the four accepted cases (A)-(D), each formalized
separately, with elimination and introduction lemmas and the literal comment:
replace the placeholder proof with a proof of any one accepted Clay case.
Statement only; the repo's own README lists "the analytic
existence/uniqueness/regularity theory itself" as missing. **The formal finish line
exists as a typed proposition with a hole.**

**Precedent (cited):** the 56,000-line Lean 4 formalization of De Giorgi-Nash-Moser
elliptic regularity theory (Armstrong & Kempe, LLM-assisted under close human
supervision). Hard PDE regularity at scale is now a demonstrated genre.

**This sandbox (verified by experiment):** core Lean 4.15.0 works (NSSkeleton v2
compiled today, all four theorems, empty axiom set). Mathlib cache and Lean release
hosts are blocked by the egress proxy (`403`, `x-deny-reason: host_not_allowed` on
`lakecache.blob.core.windows.net`, `reservoir.lean-lang.org`,
`releases.lean-lang.org`). GitHub itself is reachable (both repos cloned). So: no
Mathlib builds here by default. Option: allowlisting those hosts in Claude's
network settings would open it up, with the honest caveat that 1 vCPU / 3.9 GiB is
marginal for elaborating heavy analysis imports. Default venue for Mathlib-backed
work: Claude Code on K's machine.

## 2. The target, stated precisely

Theorem B, continuous form, real function spaces, torus first: for smooth
divergence-free data on the 3-torus with E₀ · Z₀ < ν⁴/κ, energy and enstrophy are
nonincreasing and the smooth solution is global. The Fujita-Kato-class small-data
result, our elementary cousin, machine-checked. Nobody has this, in any proof
assistant, as of today's reconnaissance.

Decomposition into tiers, each with a deterministic acceptance gate
(builds + `#print axioms` ⊆ the standard three):

- **Tier 0, the ODE layer (pure Mathlib, no PDE).** The continuous trap and
  Riccati comparison over ℝ: (i) any C¹ history obeying Ż ≤ (κ/ν³)Z³ is dominated
  by the exact Riccati orbit up to its blow-up time (safety window with explicit
  constant, the continuous twin of `safety_window` proved today over Nat);
  (ii) the invariance of the region {κEZ < ν⁴} under coupled monotone descent
  (the trap, continuous twin of `trap_concrete`). Mathlib's ODE/Gronwall
  comparison machinery is the expected engine; exact lemma names to be confirmed
  on-machine, not assumed here.
- **Tier 1, the master inequality on the torus.** For smooth fields:
  Ż ≤ -ν‖Δu‖² + (C/ν³)Z³ from Hölder (6,3,2), Sobolev H¹ → L⁶ on the torus,
  interpolation, Young. First with an abstract constant C > 0 (structure first,
  constants later); the sharp-constant torus transfer, our old flagged asterisk,
  becomes a named formal task instead of a footnote.
- **Tier 2, conditional Theorem B.** Tier 0 + Tier 1 composed: on any interval
  where a smooth solution exists, smallness E₀Z₀ < ν⁴/C forces Z nonincreasing.
  A machine-checked a priori estimate for 3D Navier-Stokes. Already a
  publishable, announceable first at this tier.
- **Tier 3, continuation.** Bounded enstrophy implies extension: local
  well-posedness in H¹ plus the blow-up criterion. The genuinely hard classical
  layer, the months-scale campaign, DGNM-style agent teamwork.
- **Tier 4, interface.** Plug into Uda's `LerayHopfSolutionFull` for weak-strong
  statements. Optional, later, and the reason to stay toolchain-compatible.

## 3. Gap ledger

| Ingredient | Status | Where |
|---|---|---|
| Formal Clay statement to aim at | EXISTS | lean-dojo repo, `ClayNavierStokes` |
| L²/Bochner/measure backbone | EXISTS | Mathlib (Uda uses heavily: 88 Analysis, 52 MeasureTheory imports) |
| Fourier/Parseval on the torus | EXISTS (project) | `LerayHopf/Analysis/FourierParseval.lean` |
| Divergence-free machinery, Helmholtz | EXISTS (project) | `LerayHopf/R3/CurlDensity.lean` and kin |
| Energy inequality machinery | EXISTS (project) | `LerayHopf/Torus/TraceEnergy.lean` |
| ODE comparison / Gronwall | EXPECTED in Mathlib | confirm exact lemmas on-machine (M1 step 1) |
| Sobolev H¹ → L⁶ with constant, on 𝕋³ | MISSING | Tier 1 task (ℝ³ version expected in Mathlib; torus transfer is ours) |
| Enstrophy dynamics for smooth solutions | MISSING | Tier 1-2, the campaign core |
| Local H¹ well-posedness + continuation | MISSING | Tier 3, the hard layer |
| Small-data global regularity (any assistant) | MISSING | the goal of this campaign |

## 4. Venue and toolchain decisions

1. Heavy Mathlib work runs in Claude Code on K's machine. New repo (working name
   `theorem-b`), pinned to Uda's exact toolchain (`v4.31.0-rc2`) and Mathlib rev
   (`15a89b24`) for future interop at Tier 4.
2. Adopt the Uda guard pattern from day one: an axiom-check script that fails on
   any unexpected axiom or `sorryAx`. Grant-guard for mathematics; we already
   live this doctrine.
3. This sandbox remains the venue for core-Lean skeletons, source reconnaissance,
   planning documents, and drafting. Optionally unlock Mathlib here by
   allowlisting the three hosts above in network settings; treat as convenience,
   not the main line.

## 5. Milestones

- **M0, done today.** NSSkeleton v2: quantitative discrete Theorem A
  (`safety_window`, `safety_concrete`), kernel-accepted, empty axiom set, hash
  frozen. Ratchet re-verified from a cold sandbox.
- **M1, days.** The M1 pack: `RiccatiTrap.lean` draft (Tier 0 statements over ℝ),
  the Claude Code handoff prompt, the axiom-guard script, the repo scaffold.
  Gate: builds on K's machine, axioms ⊆ standard three.
- **M2, one to two weeks.** Tier 1 master inequality with abstract constant.
- **M3.** Tier 2 conditional Theorem B; announcement write-up (Zulip / short
  paper) once green.
- **M4, campaign scale.** Tier 3 continuation, then full small-data global
  regularity. Agent-team route, Uda-style, our orchestration doctrine.

## 6. Honesty ledger for this rung

| Grade | Items |
|---|---|
| Verified | NSSkeleton v2 kernel acceptance with empty axiom set (this sandbox, Lean 4.15.0); cache-host denial (403 `host_not_allowed`, three hosts) |
| Textually verified | leray-hopf contents, scope claims, agent workflow, import profile (clone @ `e704400`, read); ClayNavierStokes statement (clone @ `fd52071`, read); kernel re-verification of Uda's capstones deferred to K's machine |
| Cited | DGNM 56k-line formalization; Uda's kernel-only capstone claim (their scope doc and guard script, not independently re-run) |
| Refused | Nothing this rung required refusing |

Smallest next move: draft the M1 pack.

*End of Rung 2 report.*
