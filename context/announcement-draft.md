# DRAFT: A machine-checked conditional Theorem B for 3D Navier-Stokes

Status: DRAFT for Konstantinos's review. Not published. Tone targets a Zulip
post (short form) with the bones of a short paper (long form). Every claim
below is scoped to what the kernel accepted; nothing is claimed beyond it.

## Short form (Zulip)

We have kernel-checked, in Lean 4 over Mathlib (pin `15a89b24`, toolchain
`v4.31.0-rc2`), a *conditional* small-data enstrophy control for the 3D
incompressible Navier-Stokes equations, in spectral form on the frequency
lattice of the 3-torus.

Precisely: for a time-parametrized coefficient field `c : ℝ → (ℤ³ → V)`
(mean-zero, dissipation-summable), with energy `E`, enstrophy `Z`, and
dissipation `D` defined as weighted `tsum`s, we prove there is a uniform
constant `κ` such that IF the trajectory satisfies the enstrophy-balance
inequality

    Z' ≤ -2νD + 2B,     B := the ℓ¹×ℓ²×ℓ² trilinear majorant,

and `E' ≤ 0`, THEN small data `κ·E₀·Z₀ < ν⁴` traps the orbit: the smallness
persists and `E`, `Z` never exceed their initial values, for the whole
lifespan (`conditional_trap`). A companion result gives the quantitative
Riccati safety window `Z(t)² ≤ Z₀²/(1 − 2(K/ν³)Z₀²t)` under positivity
(`conditional_safety_window`).

The proof composes three independently checked layers:
1. Tier 0, an ODE layer: forward invariance of `{κEZ < ν⁴}` by a first-exit
   argument, and the Riccati comparison, both for abstract scalar histories.
2. Tier 1, the spectral estimates: the interpolation `Z² ≤ E·D`
   (Cauchy-Schwarz), a sharp Agmon bound `S⁴ ≤ C·Z·D` for the ℓ¹ norm of the
   coefficients (low/high frequency split with lattice shell counts), the
   trilinear majorant bound `B ≤ S·√Z·√E'`, and the master inequality
   `2B ≤ νD + (K/ν³)Z³`.
3. Tier 2, the composition above.

Everything is stated on squares and fourth powers; no real root appears in
any statement, and the Young step in the master inequality is closed by the
polynomial identity `27(p+q)⁴ − 256p³q = (p−3q)² (27p² + 14pq + 3q²)`
rather than by fractional powers.

What is NOT claimed: no existence theory, no PDE solutions, and no
unconditional theorem. The single hypothesis left open is the balance
inequality itself, which for smooth solutions is the classical enstrophy
identity plus the domination of the convection pairing by the majorant.
Discharging it (the derivative-to-frequency layer on the torus, and the
concrete pairing's summability) is the next campaign tier.

Verification discipline: a deterministic gate script accepts the build only
if `#print axioms` for all ten capstone theorems reports at most
`propext, Classical.choice, Quot.sound` and no `sorryAx`. Statements were
frozen before proving; each milestone was audited by an independent
adversarial pass (statement-freeze byte comparison, gate reproduction,
non-vacuity checks; the trajectory class provably contains the spectral heat
flow) before its commit was tagged.

Repository layout, tags `m1-green`, `m2-complete`, `m3-conditional-green`.
Related work: uda-lab/leray-hopf provides the kernel-checked existence side
(Leray-Hopf weak solutions on the same toolchain and Mathlib pin, chosen
deliberately for future interop); our contribution is on the regularity-
estimates side. As of our 26 Aug 2026 reconnaissance we found no prior
machine-checked statement of this small-data enstrophy trap in any proof
assistant; corrections welcome.

## Notes for the long form (not yet written)

- The convention-free majorant design: Tier 1 never fixes a Fourier
  normalization; all `2π` factors price into the uniform constants at the
  Tier 2/3 bridge. This is what lets the estimate layer stay independent of
  any particular convection-form convention.
- The `sorry`-outside-the-audit-cone discipline for declared-but-open
  targets (W4 between the two M2 commits), mirroring leray-hopf's
  release-cone practice.
- Credits: Konstantinos Tsantakos (command, architecture); Claude (Fable 5,
  Anthropic) as the proving engine under an orchestrated multi-agent
  workflow with adversarial verification; Mathlib community, especially the
  AddCircleMulti and ZLattice.Summable layers this build stands on.
- Venue thought: Lean Zulip #maths first; then decide on arXiv note vs
  waiting for the unconditional Tier 3 result.
