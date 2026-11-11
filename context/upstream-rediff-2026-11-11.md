# Upstream re-diff of the copied community class, 11 Nov 2026

`TheoremB/CommunityClass.lean` copies two definitions, six structures and one notation from the
Navier-Stokes file of google-deepmind/formal-conjectures as it stood at commit
`b9fc95eb75b048b195f3d01af4315ad3437ab157` (11 Sep 2026). Upstream has committed to that file
three times since. This record says what those commits changed and how the copy compares with
the upstream file as fetched on 11 Nov 2026. The comparison is textual: nothing upstream was
compiled here.

## Result

- Upstream's own text of the nine copied items is unchanged. Inside the file's `namespace NavierStokes`
  block, the copied commit and the file fetched on 11 Nov 2026 are identical line for line,
  docstrings included, except for two added option lines, one before each breakdown statement.
- With comments, docstrings and blank lines removed from both sides, the copied section (from
  `namespace Community` to `end Community`) differs from the nine items as they stand in the file
  fetched on 11 Nov 2026 in the same two places as on 13 Sep 2026 and nowhere else: the namespace (`NavierStokes` upstream,
  `TheoremB.Community` here) and the divergence notation (a global `@[inherit_doc] notation`
  upstream, a `local notation` here). The copy carries no docstrings and none of the file's
  other declarations.
- The four problem statements keep their categories, their link and their `sorry` bodies: the
  two existence-and-smoothness statements carry `category research open`, the two breakdown
  statements carry `category research solved` with the link to commit `8937a8f4` of
  openai/NavierStokesAndEuler, and all four bodies are `sorry`. Each breakdown statement gained
  one option line before its docstring.

The nine items: `divergence`, the notation `∇⬝`, `IsOnePeriodic`, `InitialVelocityCondition`,
`InitialVelocityConditionPeriodic`, `ForceCondition`, `ForceConditionPeriodic`,
`NavierStokesExistenceAndSmoothness` and `NavierStokesExistenceAndSmoothnessPeriodic`.

## Versions compared

| upstream commit | date | what it is | bytes | lines | sha256 of the file |
|---|---|---|---|---|---|
| `b9fc95eb75b048b195f3d01af4315ad3437ab157` | 2026-09-11 | the copied commit | 14,426 | 311 | `7b5bb2a5e2c3bcbd398e72bd7c9ba612b882efac4ea499e61412a6c270750ca4` |
| `bc1d2bc0df6edcbc6bfa43d0b4b1018ccdbdb627` | 2026-09-12 | the file moved (directory renamed), same bytes | 14,426 | 311 | `7b5bb2a5e2c3bcbd398e72bd7c9ba612b882efac4ea499e61412a6c270750ca4` |
| `6fbb54f24ccc2e64dcfaffc28c58950e377110d2` | 2026-09-18 | PR #4688, Lean module conversion | 14,466 | 314 | `0bdd5a8203726fab205c983c6633dc7b688bbc853397271214c06e119c6a5c76` |
| `d9f6ffa8dd7fc2b8b597dd1f7a824d27b12b88af` | 2026-10-29 | PR #7631, a linter option before each breakdown statement | 14,574 | 316 | `7897169c73dcdd7c709264bbc17970e3c609d6f28a116bdd2fb41a76c66efa17` |
| `e4e4a9b0b6031c663a293de43a0f29a379ae03e0` | 2026-11-11 | repository head when fetched; the newest commit on the file is the 29 Oct 2026 one | 14,574 | 316 | `7897169c73dcdd7c709264bbc17970e3c609d6f28a116bdd2fb41a76c66efa17` |

Each version was fetched by commit id from raw.githubusercontent.com on 11 Nov 2026. The file's
full path is not written in this tree; it is that repository's Navier-Stokes file. The sha256
values are of the file bytes as served, not git object ids. A copy fetched on
13 Sep 2026 and kept outside this repository has the same sha256 as the file fetched on
11 Nov 2026 at the copied commit.

## Every changed line, copied commit to 11 Nov 2026

```diff
@@ -15,0 +16 @@
+module
@@ -17 +18 @@
-import FormalConjecturesUtil
+public import FormalConjecturesUtil
@@ -59,0 +61,2 @@
+@[expose] public section
+
@@ -282,0 +286 @@
+set_option linter.style.formal_proof_palomar false in
@@ -296,0 +301 @@
+set_option linter.style.formal_proof_palomar false in
```

- `6fbb54f2` (PR #4688, "chore: modulize FormalConjectures/"): the `module` line, `import` turned into
  `public import`, and `@[expose] public section` followed by one blank line. The pull request
  converts the repository's remaining files to Lean modules.
- `d9f6ffa8` (PR #7631, "feat: add linter to enforce Palomar submissions"): the two option lines. The
  pull request adds a check (`linter.style.formal_proof_palomar`) that the formal-proof link of a
  `research solved` statement has the form of an entry address of the Palomar registry
  (palomar-registry.org); by its own documentation it checks the form of the link, not that the
  entry exists. It switches that check off, declaration by declaration, for the existing links
  that are not of that form (by its own count 1,096 annotations on 1,070 declarations in 734
  files). The two breakdown statements are among them; their category,
  their link and their bodies are unchanged.

## What this does not check

- Identical text is not shown to be identical meaning: elaborated terms were not compared, and
  of the files the upstream file depends on only the one that defines `ℝ^n` was fetched again.
- Nothing upstream was compiled. Upstream pins Lean `v4.33.1` and Mathlib `0df444a360ea`
  (the same on 13 Sep 2026 and on 11 Nov 2026); this repository pins Lean `v4.31.0-rc2` and Mathlib
  `15a89b2468bc`. Identical text is therefore elaborated against different library versions, as it
  already was on 13 Sep 2026.
- The 18 Sep 2026 commit converts the file to a Lean module. What that changes for files that
  import the upstream file was not examined. This repository does not import that file, so the
  conversion does not reach the copy.
- The copy sits in a different context. Upstream has `open ContDiff Set InnerProductSpace MeasureTheory EuclideanGeometry`
  and `open scoped Laplacian`; `TheoremB/CommunityClass.lean` has
  `open Set Filter Topology MeasureTheory InnerProductSpace UnitAddTorus` and
  `open scoped ContDiff Laplacian`, and declares its `ℝ^` notation locally (next item).
- The `ℝ^n` notation used by the copied text is declared in upstream's support library as
  `scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)`
  (the same text on 13 Sep 2026 and on 11 Nov 2026), and the upstream file opens
  `EuclideanGeometry`; the import chain from the upstream file to that declaration was not
  traced. This repository declares the same right-hand side as a `local notation` in
  `TheoremB/CommunityClass.lean`.
- Upstream's open pull requests and issues were searched on 11 Nov 2026 with GitHub's issue
  search, restricted to that repository: `is:pr is:open Navier` and `is:pr is:open NavierStokes`
  returned nothing; `is:issue is:open Navier` returned one issue and `is:issue is:open
  NavierStokes` two. Neither issue proposes a change to the file's definitions or statements.
  Open pull requests were not listed by the files they touch, so one that changes the file
  without those words would have been missed.
- This record says nothing about whether the upstream statements are faithful to the published
  problem. No human domain expert has reviewed the statements (see the README).
- The upstream branch moves. `e4e4a9b0` was its head when the file was fetched on 11 Nov 2026;
  later commits are not covered.

## To repeat

In a clone of the upstream repository, find the file's path at a commit with
`git ls-tree -r --name-only <commit> | grep NavierStokes.lean` (the directory was renamed at
`bc1d2bc0`, so the first row has another path than the rest), print its hash with
`git show <commit>:<path> | shasum -a 256`, and compare with the table. Then compare the
`namespace NavierStokes` block of the first and the last version. To compare with the copy,
remove comments, docstrings and blank lines from both sides first.
