# PR draft: a derivative-free Grönwall inequality at a negative rate

**Status: DRAFTED, NOT SUBMITTED.** Nothing has been pushed, forked, or
sent anywhere. Opening the PR is outward-facing and remains the user's
call, per the standing rule in `upstreaming-dossier.md`.

This file is an agent-written private fact sheet, not text to post. The PR
body and every Zulip or GitHub comment must be written by the owner in his
own words.

Artifact: `context/upstream/GronwallWindow.lean`, written against the
campaign's pin (toolchain `v4.31.0-rc2`, Mathlib `15a89b24`). It is not part
of the lake build and this repository keeps no compile record for it; it must
be built on Mathlib master before any submission.

## Proposed title

`feat(Analysis/ODE): derivative-free Grönwall bound at a negative rate`

The scope `Analysis/ODE` is the one used for a new file by Mathlib pull
request #39871 (see "Related pull requests on master" below).

## Placement

A new file, chosen up front: `Mathlib/Analysis/ODE/GronwallWindow.lean`,
with

```
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

(`LogBounds` is for `Real.tendsto_one_add_div_pow_exp`), plus an entry in
`Mathlib.lean`. Reason, as checked on 11 Nov 2026: #38829, which added an
interval-integral import to `Gronwall.lean` itself, was closed unmerged on
19 May 2026 (it carried the large-import label before that, per the audit
of 20 Sep 2026), and #39871 went the new-file route (it adds
`Mathlib/Analysis/ODE/UniformGronwall.lean`). Whether the new file or an
append is preferred is a question for the Zulip thread, not for the PR
(first checklist item).

## Related pull requests on master (as checked on 11 Nov 2026)

- #38829, "feat(Analysis/ODE/Gronwall): added gronwall-bellman inequality":
  opened 2 May 2026, closed without merging on 19 May 2026 over
  AI-use standards. Bellman form.
- #39871, "feat(Analysis/ODE): Uniform Gronwall inequality": open, not
  merged, opened 26 May 2026; labels awaiting-author, LLM-generated,
  new-contributor, t-analysis. A uniform Grönwall inequality in a new file.
- #45443, "feat(Analysis/ODE): add variable-coefficient integral Grönwall":
  open, opened 28 Oct 2026; labels LLM-generated, new-contributor,
  t-analysis. Linked from #38829 and #39871.

None of the three states the derivative-free window form drafted here, as
far as the audit of 20 Sep 2026 and the 11 Nov 2026 check of titles and
labels show; the check did not read the diffs of #45443. Mathlib master is
on `v4.36.0-rc2` as checked on 11 Nov 2026, so the draft needs a port from
the campaign's `v4.31.0-rc2` toolchain before it can be built there.

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
   to a `liminf`: it **removes it entirely**.
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
`Δ·(f y − A·Δ)`; this is the step that would otherwise require a
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
where it is `decay_of_window_integral_ineq` and is used in a
determining-modes result for the 3D Navier-Stokes system (tag
`t7-modes-green`); no mathematical priority is claimed for it. The campaign file imports Mathlib only and
depends on no campaign definition, which is what makes this liftable
verbatim. The upstream draft here is **sharper** than the campaign's
version: the campaign bounds the geometric sum by `A/c`, while this sums
it exactly and lands on `gronwallBound`.

## Checklist before submitting

- [ ] Open a Zulip thread (in your own words, as Mathlib's contribution
      rules require) proposing the statement, mentioning #39871, and asking
      about placement; wait for a reaction before opening the PR.
- [x] `Real.tendsto_one_add_div_pow_exp` is still in
      `Analysis/SpecialFunctions/Complex/LogBounds.lean` on master (checked
      20 Sep 2026; not re-checked on 11 Nov 2026).
- [ ] Re-verify the rest against current Mathlib master, not the campaign
      pin `15a89b24`; master is on `v4.36.0-rc2` as checked on 11 Nov 2026.
      The draft has not been built against master.
- [ ] Note the new Lean module system: Gronwall.lean at the pin uses
      `module` / `public import` / `@[expose] public section`. The new file
      should use `module` and `public import` as in the placement section.
- [ ] Say in the PR body that the file is new and why (see "Placement").
- [ ] PR description names the tools used (Claude Code agents: Opus 5, Fable 5,
      Fable 5.1) and how; post the comment LLM-generated.
- [ ] Check the author line in the file header is the one the owner wants on
      Mathlib.
- [ ] Consider adding the campaign's Navier-Stokes application as a
      motivating one-liner in the PR body, not in the module docstring.
