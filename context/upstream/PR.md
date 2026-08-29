# PR draft — a derivative-free Grönwall inequality at a negative rate

**Status: DRAFTED, NOT SUBMITTED.** Nothing has been pushed, forked, or
sent anywhere. Opening the PR is outward-facing and remains the user's
call, per the standing rule in `upstreaming-dossier.md`.

Artifact: `context/upstream/GronwallWindow.lean`, compile-verified at the
campaign's pin (toolchain `v4.31.0-rc2`, Mathlib `15a89b24`).

## Proposed title

`feat(Analysis/ODE/Gronwall): derivative-free Grönwall bound at a negative rate`

## Placement

Append to `Mathlib/Analysis/ODE/Gronwall.lean`. It needs two imports that
file does not currently carry:
`Mathlib.Analysis.SpecialFunctions.Complex.LogBounds` (for
`Real.tendsto_one_add_div_pow_exp`) and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`. If the import
weight is objected to — Gronwall.lean is currently light, importing only
`ExpDeriv` — the fallback is a new file
`Mathlib/Analysis/ODE/GronwallWindow.lean` importing Gronwall.lean.
**Flag this to the reviewer up front**; it is the one structural
decision in the PR.

## What it adds

```
theorem le_gronwallBound_of_window_integral_le {f : ℝ → ℝ} {c A b : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A)
    (hf : ∀ x ∈ Icc (0:ℝ) b, 0 ≤ f x)
    (hint : ∀ x ∈ Icc (0:ℝ) b, ∀ y ∈ Icc x b, IntervalIntegrable f volume x y)
    (hle : ∀ x ∈ Icc (0:ℝ) b, ∀ y ∈ Icc x b,
      f y + c * (∫ t in x..y, f t) ≤ f x + A * (y - x)) :
    ∀ x ∈ Icc (0:ℝ) b, f x ≤ gronwallBound (f 0) (-c) A x
```

## Why Mathlib wants it

1. **It answers the file's own TODO, from a direction the TODO did not
   anticipate.** `Gronwall.lean` records: *"prove an inequality for a
   function satisfying `‖f' x‖ ≤ K x * ‖f x‖ + ε`, or more generally
   `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign of
   `K x` and `f x`."* This is a bound at a rate of arbitrary sign (here
   strictly negative), and it does not weaken the derivative hypothesis
   to a `liminf` — it **removes it entirely**.
2. **The existing family is unusable on limits.** Every current Grönwall
   lemma needs pointwise derivative information. A function obtained as a
   limit of smooth approximants generally keeps only an *integrated*
   inequality: differentiability does not survive the limit, and the
   integrated form does. This is the standard situation for energy
   functionals of PDE, and it is exactly why this lemma had to be
   written rather than found.
3. **It fits the existing API.** The conclusion is stated in terms of
   `gronwallBound`, so it composes with `gronwallBound_of_K_ne_0`,
   `gronwallBound_mono` and the rest of the file's algebra with no new
   vocabulary.

## Naming

`le_gronwallBound_of_window_integral_le`, following the file's
`le_gronwallBound_of_liminf_deriv_right_le` and
`norm_le_gronwallBound_of_norm_deriv_right_le`: conclusion first,
hypothesis after `of_`. "window" names the two-point quantification
`∀ x ≤ y`, which is what distinguishes it from a one-point derivative
hypothesis.

## Proof, in one paragraph

Discrete, and deliberately so. On one step `[x, y]` of length `Δ`,
nonnegativity turns the window inequality into `f y ≤ f t + A·Δ` for
every `t` in the step, so the integral admits the *constant* minorant
`Δ·(f y − A·Δ)` — this is the step that would otherwise require a
derivative. Feeding it back gives `f y ≤ f x/(1 + cΔ) + A·Δ`, and the
induction `f(iΔ) ≤ f 0/(1+cΔ)^i + B(1 − 1/(1+cΔ)^i)` with
`B := A(1+cΔ)/c` closes with **equality** in its side condition
`B/(1+cΔ) + A·Δ = B`, so no slack accumulates across the `n` steps.
Taking `Δ = x/n` and `n → ∞`, `Real.tendsto_one_add_div_pow_exp` gives
the bound. The `gronwallBound` form is the exact limit, not a weakening:
the geometric sum is summed, not bounded.

## Anticipated review questions

- *Why not derive it from the existing differential Grönwall?* Because
  the hypothesis is strictly weaker: `f` need not be differentiable,
  continuous, or even Borel beyond interval integrability on subwindows.
  There is no intermediate object to differentiate.
- *Is `hint` needed, or does the window inequality imply it?* Needed.
  The inequality constrains integrals that must first be known to exist.
- *Generality.* Stated on `[0, b]` with base point `0` to match
  `gronwallBound`'s normalization. A general base point is a translation
  and can be added if a reviewer prefers it. A Bochner-valued or
  `‖f‖`-valued variant is plausible future work; the proof uses order
  completeness of `ℝ` in the minorant step, so it is not immediate.
- *`b < 0`.* Then `Icc 0 b` is empty and the statement is vacuous; no
  hypothesis `0 ≤ b` is needed, and none is taken.

## Provenance

Extracted from `TheoremB/WindowDecay.lean` in the Theorem B campaign,
where it is `decay_of_window_integral_ineq` and supplies the decay engine
for a machine-checked determining-modes theorem for 3D Navier–Stokes
(tag `t7-modes-green`). The campaign file imports Mathlib only and
depends on no campaign definition, which is what makes this liftable
verbatim. The upstream draft here is **sharper** than the campaign's
version: the campaign bounds the geometric sum by `A/c`, while this sums
it exactly and lands on `gronwallBound`.

## Checklist before submitting

- [ ] Re-verify against current Mathlib master, not the campaign pin
      `15a89b24`. `Real.tendsto_one_add_div_pow_exp` lives in
      `Analysis/SpecialFunctions/Complex/LogBounds.lean` at the pin;
      confirm it has not moved or been renamed.
- [ ] Note the new Lean module system: Gronwall.lean at the pin uses
      `module` / `public import` / `@[expose] public section`. Match the
      surrounding file's conventions at the time of submission.
- [ ] Decide placement (append vs new file) and say so in the PR body.
- [ ] Add the author line and sign the CLA.
- [ ] Consider adding the campaign's Navier–Stokes application as a
      motivating one-liner in the PR body, not in the module docstring.
