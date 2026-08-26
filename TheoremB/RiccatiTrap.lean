/-
  TheoremB/RiccatiTrap.lean
  Tier 0 of the Theorem B campaign (M1 draft, 26 Aug 2026).

  Lineage: continuous twins of the kernel-checked discrete skeletons in
  NSSkeleton.lean v2 (trap_concrete, safety_window).  See rung2-gap-map.md
  for the campaign map and M1-HANDOFF.md for the working contract.

  STATUS: PROVED (M1 complete, 27 Aug 2026).  S1..S4 are closed.  On the
  target machine scripts/check_axioms.sh reports GATE: GREEN, with both
  audited theorems depending on exactly [propext, Classical.choice,
  Quot.sound] and no sorryAx.

  CONTRACT: the four theorem STATEMENTS are frozen.  If a statement cannot
  be proved as written (a missing hypothesis, a wrong constant), do not
  silently repair it: stop and report.  Route decisions are architect calls.

  Mathematical content:

  * `trap_forward_invariance` (continuous Theorem B heart): on [0, T), if
    energy E can only descend, enstrophy Z can only descend while
    kappa * E * Z < nu4, and the initial data is inside that region, then
    the orbit never leaves the region and both quantities stay below their
    initial values.  Proof route: first-exit bootstrap.  The bad set
    {t | nu4 <= kappa * E t * Z t} is closed in [0, T) by continuity; if
    nonempty, its infimum t* is a bad point with t* > 0; but on [0, t*)
    the region condition holds, so E and Z are nonincreasing there, so by
    continuity kappa * E t* * Z t* <= kappa * E 0 * Z 0 < nu4, a
    contradiction.

  * `riccati_window` (continuous Theorem A heart): a positive history with
    Z' <= a * Z^3 obeys Z t ^ 2 <= Z 0 ^ 2 / (1 - 2 a Z0^2 t) inside the
    window 2 a Z0^2 t < 1.  Proof route: linearize.  phi := (Z ^ 2)⁻¹ has
    phi' = -2 Z' / Z^3 >= -2a, so the mean value inequality gives
    phi t >= phi 0 - 2 a t, and the bound follows by algebra.  Stated on
    squares to avoid Real.sqrt plumbing entirely.
-/
import Mathlib

namespace TheoremB

open Set

/-! ## Helper targets -/

/-- **S1.**  Endpoint monotonicity from a nonpositive derivative: a function
continuous on `[x, y]` and differentiable with nonpositive derivative on
`(x, y)` does not increase from `x` to `y`.

Blueprint: wrap `Convex.antitoneOn_of_deriv_nonpos` (candidate name, in
`Mathlib.Analysis.Calculus.MeanValue`) applied to `D = Icc x y`, whose
interior is `Ioo x y`; confirm the exact name and signature with `exact?`
or Loogle before hand-rolling anything. -/
theorem le_of_deriv_nonpos {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hc : ContinuousOn f (Icc x y))
    (hd : DifferentiableOn ℝ f (Ioo x y))
    (h' : ∀ t ∈ Ioo x y, deriv f t ≤ 0) :
    f y ≤ f x := by
  have h := antitoneOn_of_deriv_nonpos (convex_Icc x y) hc
    (by rwa [interior_Icc]) (by rwa [interior_Icc])
  exact h (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

/-- **S3.**  The linearized Riccati slope: for a positive history with
`Z' ≤ a * Z ^ 3` on `(0, T)`, the reciprocal square obeys
`(Z 0 ^ 2)⁻¹ - 2 * a * t ≤ (Z t ^ 2)⁻¹` for every `t ∈ [0, T)`.

Blueprint: let `phi t := (Z t ^ 2)⁻¹`.  On `(0, t)` the chain rule
(`HasDerivAt.inv`, `HasDerivAt.pow`, or `deriv_inv` composition lemmas)
gives `deriv phi s = -2 * deriv Z s / Z s ^ 3`; the hypothesis and
positivity give `deriv phi s ≥ -2 * a`.  Apply the mean value inequality
(candidate: `Convex.mul_sub_le_image_sub_of_le_deriv` with `C = -2 * a` on
`Icc 0 t`; continuity of `phi` from `hZc`, `hpos`) and rearrange.  If the
mean-value-with-lower-bound spelling is awkward, apply the S1-style upper
bound to `fun s => -(phi s)` instead. -/
theorem inv_sq_slope {T a : ℝ} (ha : 0 < a) {Z : ℝ → ℝ}
    (hZc : ContinuousOn Z (Ico 0 T))
    (hZd : DifferentiableOn ℝ Z (Ioo 0 T))
    (hpos : ∀ t ∈ Ico (0 : ℝ) T, 0 < Z t)
    (hZ' : ∀ t ∈ Ioo (0 : ℝ) T, deriv Z t ≤ a * Z t ^ 3) :
    ∀ t ∈ Ico (0 : ℝ) T, (Z 0 ^ 2)⁻¹ - 2 * a * t ≤ (Z t ^ 2)⁻¹ := by
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have hsub : Icc (0 : ℝ) t ⊆ Ico 0 T := Icc_subset_Ico_right htT
  have hsub' : Ioo (0 : ℝ) t ⊆ Ioo 0 T := Ioo_subset_Ioo_right htT.le
  have hphic : ContinuousOn (fun u => (Z u ^ 2)⁻¹) (Icc 0 t) :=
    ((hZc.mono hsub).pow 2).inv₀
      (fun s hs => pow_ne_zero 2 (hpos s (hsub hs)).ne')
  -- pointwise on (0, t): phi is differentiable with slope ≥ -2a
  have hstep : ∀ s ∈ Ioo (0 : ℝ) t,
      DifferentiableAt ℝ (fun u => (Z u ^ 2)⁻¹) s ∧
      -(2 * a) ≤ deriv (fun u => (Z u ^ 2)⁻¹) s := by
    intro s hs
    have hsT : s ∈ Ioo (0 : ℝ) T := hsub' hs
    have hZs : 0 < Z s := hpos s ⟨hsT.1.le, hsT.2⟩
    have hZds : DifferentiableAt ℝ Z s :=
      hZd.differentiableAt (isOpen_Ioo.mem_nhds hsT)
    have h1 : HasDerivAt (fun u => Z u ^ 2) (2 * Z s * deriv Z s) s := by
      simpa using hZds.hasDerivAt.fun_pow 2
    have h2 : HasDerivAt (fun u => (Z u ^ 2)⁻¹)
        (-(2 * Z s * deriv Z s) / (Z s ^ 2) ^ 2) s :=
      h1.fun_inv (pow_ne_zero 2 hZs.ne')
    refine ⟨h2.differentiableAt, ?_⟩
    rw [h2.deriv]
    have hZ's : deriv Z s ≤ a * Z s ^ 3 := hZ' s hsT
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hZ's (by positivity : (0 : ℝ) ≤ 2 * Z s)]
  have hdiff : DifferentiableOn ℝ (fun u => (Z u ^ 2)⁻¹) (interior (Icc 0 t)) := by
    rw [interior_Icc]
    exact fun s hs => (hstep s hs).1.differentiableWithinAt
  have hbound : ∀ s ∈ interior (Icc (0 : ℝ) t),
      -(2 * a) ≤ deriv (fun u => (Z u ^ 2)⁻¹) s := by
    rw [interior_Icc]
    exact fun s hs => (hstep s hs).2
  have hmvt : -(2 * a) * (t - 0) ≤ (Z t ^ 2)⁻¹ - (Z 0 ^ 2)⁻¹ :=
    (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv hphic hdiff hbound
      0 (left_mem_Icc.mpr ht0) t (right_mem_Icc.mpr ht0) ht0
  linarith

/-! ## Main targets -/

/-- **S2.  Continuous trap (Theorem B heart, forward invariance).**
On `[0, T)`: if `E` can only descend, `Z` can only descend while
`κ * E * Z < ν4`, both stay nonnegative, and the initial data lies inside
the region `κ * E 0 * Z 0 < ν4`, then the orbit stays in the region for
all time and neither quantity ever exceeds its initial value.

Blueprint (first-exit bootstrap):
1. Let `B := {t ∈ Ico 0 T | ν4 ≤ κ * E t * Z t}`.  From `hEc`, `hZc` the
   map `t ↦ κ * E t * Z t` is continuous on `Ico 0 T`
   (`ContinuousOn.mul`), so `B` is closed in the subspace `Ico 0 T`.
2. Suppose `B` is nonempty; put `t* := sInf B`.  `B` is bounded below
   by `0`, so `t*` is well defined; `t* ∈ Ico 0 T` since some element of
   `B` is `< T`; `t* ∈ B` because `t* ∈ closure B` (`csInf_mem_closure`)
   and `B` is closed in `Ico 0 T`.  `t* ≠ 0` by `h0`, so `0 < t*`.
3. Every `t ∈ Ico 0 t*` satisfies `κ * E t * Z t < ν4` (it is below the
   infimum of `B`), so `hZ'cond` gives `deriv Z ≤ 0` on `Ioo 0 t*`, and
   `hE'` gives `deriv E ≤ 0` there.  Apply S1 on `Icc 0 t*` (continuity
   restricts from `Ico 0 T` since `t* < T`) to get `E t* ≤ E 0` and
   `Z t* ≤ Z 0`.
4. Multiply the two inequalities (`mul_le_mul`, using `hκ.le`, `hEnn`,
   `hZnn`) to get `κ * E t* * Z t* ≤ κ * E 0 * Z 0 < ν4`, contradicting
   `t* ∈ B`.  So `B = ∅`.
5. `B = ∅` gives the region condition at every `t`; then `hZ'cond` is
   unconditional on `Ioo 0 t` for each `t`, and S1 on `Icc 0 t` delivers
   `Z t ≤ Z 0` and `E t ≤ E 0`. -/
theorem trap_forward_invariance {T : ℝ} {E Z : ℝ → ℝ} {κ ν4 : ℝ}
    (hκ : 0 < κ) (hν4 : 0 < ν4)
    (hEc : ContinuousOn E (Ico 0 T)) (hZc : ContinuousOn Z (Ico 0 T))
    (hEd : DifferentiableOn ℝ E (Ioo 0 T))
    (hZd : DifferentiableOn ℝ Z (Ioo 0 T))
    (hEnn : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ E t)
    (hZnn : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ Z t)
    (hE' : ∀ t ∈ Ioo (0 : ℝ) T, deriv E t ≤ 0)
    (hZ'cond : ∀ t ∈ Ioo (0 : ℝ) T, κ * E t * Z t < ν4 → deriv Z t ≤ 0)
    (h0 : κ * E 0 * Z 0 < ν4) :
    ∀ t ∈ Ico (0 : ℝ) T,
      κ * E t * Z t < ν4 ∧ Z t ≤ Z 0 ∧ E t ≤ E 0 := by
  -- Step A: the region condition holds everywhere (first-exit bootstrap).
  have hregion : ∀ t ∈ Ico (0 : ℝ) T, κ * E t * Z t < ν4 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨b, hbmem, hbge⟩ := hcon
    set B : Set ℝ := {s | s ∈ Icc 0 b ∧ ν4 ≤ κ * E s * Z s} with hBdef
    have hbB : b ∈ B := ⟨right_mem_Icc.mpr hbmem.1, hbge⟩
    have hBne : B.Nonempty := ⟨b, hbB⟩
    have hBbdd : BddBelow B := ⟨0, fun s hs => hs.1.1⟩
    have hsubIco : Icc (0 : ℝ) b ⊆ Ico 0 T := Icc_subset_Ico_right hbmem.2
    have hfc : ContinuousOn (fun s => κ * E s * Z s) (Icc 0 b) :=
      (continuousOn_const.mul (hEc.mono hsubIco)).mul (hZc.mono hsubIco)
    have hBclosed : IsClosed B := by
      have hBeq : B = Icc 0 b ∩ (fun s => κ * E s * Z s) ⁻¹' Ici ν4 := by
        ext s
        simp only [hBdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ici]
      rw [hBeq]
      exact hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hcB : sInf B ∈ B := hBclosed.csInf_mem hBne hBbdd
    set c := sInf B with hcdef
    have hc0 : 0 ≤ c := hcB.1.1
    have hcb : c ≤ b := csInf_le hBbdd hbB
    have hcT : c < T := lt_of_le_of_lt hcb hbmem.2
    have hcIco : c ∈ Ico (0 : ℝ) T := ⟨hc0, hcT⟩
    -- strictly below the infimum the region condition holds
    have hbelow : ∀ s ∈ Ico (0 : ℝ) c, κ * E s * Z s < ν4 := by
      intro s hs
      by_contra hbad
      push_neg at hbad
      have hsB : s ∈ B := ⟨⟨hs.1, hs.2.le.trans hcb⟩, hbad⟩
      exact absurd (csInf_le hBbdd hsB) (not_le.mpr hs.2)
    -- S1 on [0, c] for E and Z
    have hsubc : Icc (0 : ℝ) c ⊆ Ico 0 T := Icc_subset_Ico_right hcT
    have hsubc' : Ioo (0 : ℝ) c ⊆ Ioo 0 T := Ioo_subset_Ioo_right hcT.le
    have hE1 : E c ≤ E 0 :=
      le_of_deriv_nonpos hc0 (hEc.mono hsubc) (hEd.mono hsubc')
        (fun s hs => hE' s (hsubc' hs))
    have hZ1 : Z c ≤ Z 0 :=
      le_of_deriv_nonpos hc0 (hZc.mono hsubc) (hZd.mono hsubc')
        (fun s hs => hZ'cond s (hsubc' hs) (hbelow s ⟨hs.1.le, hs.2⟩))
    -- multiply and contradict c ∈ B
    have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) T := ⟨le_refl 0, lt_of_le_of_lt hc0 hcT⟩
    have step1 : κ * E c * Z c ≤ κ * E 0 * Z c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE1 hκ.le)
        (hZnn c hcIco)
    have step2 : κ * E 0 * Z c ≤ κ * E 0 * Z 0 :=
      mul_le_mul_of_nonneg_left hZ1 (mul_nonneg hκ.le (hEnn 0 h0mem))
    linarith [hcB.2]
  -- Step B: with the region unconditional, S1 delivers both descents.
  intro t ht
  have hsubt : Icc (0 : ℝ) t ⊆ Ico 0 T := Icc_subset_Ico_right ht.2
  have hsubt' : Ioo (0 : ℝ) t ⊆ Ioo 0 T := Ioo_subset_Ioo_right ht.2.le
  refine ⟨hregion t ht, ?_, ?_⟩
  · exact le_of_deriv_nonpos ht.1 (hZc.mono hsubt) (hZd.mono hsubt')
      (fun s hs => hZ'cond s (hsubt' hs)
        (hregion s ⟨(hsubt' hs).1.le, (hsubt' hs).2⟩))
  · exact le_of_deriv_nonpos ht.1 (hEc.mono hsubt) (hEd.mono hsubt')
      (fun s hs => hE' s (hsubt' hs))

/-- **S4.  Continuous safety window (Theorem A heart, quantitative).**
A positive history obeying the Riccati differential inequality
`Z' ≤ a * Z ^ 3` satisfies the exact Riccati-orbit bound on squares,
`Z t ^ 2 ≤ Z 0 ^ 2 / (1 - 2 * a * Z 0 ^ 2 * t)`, for every `t` inside
the window `2 * a * Z 0 ^ 2 * t < 1`.  This is the continuous twin of
`NSSkeleton.safety_window`, now with the sharp constant 2 instead of the
crude discrete 8.

Blueprint: from S3, `(Z t ^ 2)⁻¹ ≥ (Z 0 ^ 2)⁻¹ - 2 * a * t`.  The window
`hwin` and `hpos 0` make the right side positive:
`(Z 0 ^ 2)⁻¹ - 2 * a * t = (1 - 2 * a * Z 0 ^ 2 * t) / Z 0 ^ 2 > 0`.
Invert both sides (`one_div_le_one_div_iff` family / `inv_le_inv` on
positives, or `div_le_div_iff` after `field_simp`) and rearrange.  Note
`t = 0` is immediate.  Positivity of `Z t ^ 2` comes from `hpos`. -/
theorem riccati_window {T a : ℝ} (ha : 0 < a) {Z : ℝ → ℝ}
    (hZc : ContinuousOn Z (Ico 0 T))
    (hZd : DifferentiableOn ℝ Z (Ioo 0 T))
    (hpos : ∀ t ∈ Ico (0 : ℝ) T, 0 < Z t)
    (hZ' : ∀ t ∈ Ioo (0 : ℝ) T, deriv Z t ≤ a * Z t ^ 3)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (hwin : 2 * a * Z 0 ^ 2 * t < 1) :
    Z t ^ 2 ≤ Z 0 ^ 2 / (1 - 2 * a * Z 0 ^ 2 * t) := by
  obtain ⟨ht0, htT⟩ := ht
  have hT0 : (0 : ℝ) < T := lt_of_le_of_lt ht0 htT
  have hZ0 : 0 < Z 0 := hpos 0 ⟨le_refl 0, hT0⟩
  have hZ0sq : 0 < Z 0 ^ 2 := by positivity
  have hZtsq : 0 < Z t ^ 2 := pow_pos (hpos t ⟨ht0, htT⟩) 2
  have hP : 0 < 1 - 2 * a * Z 0 ^ 2 * t := by linarith
  have key : (Z 0 ^ 2)⁻¹ - 2 * a * t ≤ (Z t ^ 2)⁻¹ :=
    inv_sq_slope ha hZc hZd hpos hZ' t ⟨ht0, htT⟩
  have h2 : (1 - 2 * a * Z 0 ^ 2 * t) / Z 0 ^ 2 ≤ (Z t ^ 2)⁻¹ := by
    have e : (1 - 2 * a * Z 0 ^ 2 * t) / Z 0 ^ 2 = (Z 0 ^ 2)⁻¹ - 2 * a * t := by
      field_simp
    rw [e]
    exact key
  calc Z t ^ 2 = ((Z t ^ 2)⁻¹)⁻¹ := (inv_inv _).symm
    _ ≤ ((1 - 2 * a * Z 0 ^ 2 * t) / Z 0 ^ 2)⁻¹ :=
        inv_anti₀ (div_pos hP hZ0sq) h2
    _ = Z 0 ^ 2 / (1 - 2 * a * Z 0 ^ 2 * t) := by rw [inv_div]

end TheoremB
