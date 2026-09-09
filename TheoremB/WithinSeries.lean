/-
# Series of functions on a convex set: differentiability and smoothness within the set
(Tier 8b, wave W2, the Mathlib-only engine)

This file delivers the within-set versions of Mathlib's `SmoothSeries.lean`,
on a convex set `s` with unique differentials:

1. `summable_of_summable_hasFDerivWithinAt_of_convex`: if the derivatives
   within `s` of a series of functions carry a summable uniform bound and the
   series converges at one point of `s`, it converges at every point of `s`.
2. `hasFDerivWithinAt_tsum_of_convex` and its 1-D form
   `hasDerivWithinAt_tsum_of_convex`: the sum is differentiable within `s`
   with derivative the sum of the derivatives.
3. `iteratedFDerivWithin_tsum_apply_of_convex` and `contDiffOn_tsum_of_convex`:
   the Weierstrass M-test for `ContDiffOn ℝ N` within `s`, from summable
   uniform bounds on the iterated derivatives within `s` at every order
   `≤ N` (`N : ℕ∞`; instantiate `(N := ⊤)` for `C^∞`, which is the
   `(⊤ : ℕ∞)` cast into `WithTop ℕ∞`, not `ω`: no analyticity).
4. `contDiff_tsum_of_convex_univ`, the must-hold sanity corollary: at
   `s = univ` the engine recovers Mathlib's `contDiff_tsum`.

Why it exists.  Mathlib's uniform-limit step for derivatives,
`hasFDerivAt_of_tendstoUniformlyOn`, is stated on an OPEN set only, and at
the pin (Lean 4.31.0-rc2, Mathlib 15a89b24) there is no `Within` variant of
it, of `contDiff_tsum`, or of `hasFDerivAt_tsum` (grep-verified by two
independent readers; `contDiffOn_tsum`, `hasFDerivWithinAt_tsum` and
`fderivWithin_tsum` are absent).  The first-order half here is therefore a
direct `ε/3` argument: the tail of the series is controlled by the mean
value inequality on the convex set
(`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`), the finite part is
differentiable within `s` (`HasFDerivWithinAt.fun_sum`), and the tail of the
bound series is small (`tendsto_tsum_compl_atTop_zero`,
`Summable.sum_add_tsum_compl`).  The iterated half mirrors
`SmoothSeries.lean` through `contDiffOn_iff_continuousOn_differentiableOn`,
`norm_fderivWithin_iteratedFDerivWithin`,
`iteratedFDerivWithin_succ_eq_comp_left` and the curry-left equivalence's
`map_tsum`, with `fderivWithin_congr` transporting the induction hypothesis
that holds only pointwise ON `s`.

Honest scope.  The within-convex engine is absent from Mathlib at the pin,
grep-verified, not new mathematics: the M-test on a convex set is textbook.
The file imports `Mathlib` only and is a PR candidate (the
within-uniform-limit generalisation of `UniformLimitsDeriv` is recorded in
the upstreaming dossier, not here).  Nothing in it mentions the flow; the
consumer is `TheoremB/JointSmooth.lean`.  No priority is claimed for it: the
within-set form of a uniform-limit derivative theorem is standard, and the
campaign's own priority statements live in the README and the announcement.  Landed verbatim from the W2
reconnaissance probe (exit 0, one reader clean); only this header was added.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import Mathlib

/-!
# Differentiability and smoothness of series on a convex set

Within-set versions of Mathlib's `SmoothSeries.lean`: on a convex set `s`, a series of
functions with a summable uniform bound on the derivatives is differentiable within `s`
(derivative = sum of the derivatives), and `C^N` within `s` when the iterated derivatives
within `s` carry summable uniform bounds. Mathlib's `hasFDerivAt_of_tendstoUniformlyOn` is
open-set only; the first-order half here is a direct `ε/3` argument through the mean value
inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`.
-/

open Set Filter Topology Asymptotics
open scoped ContDiff Topology

noncomputable section

namespace TheoremB

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem summable_of_summable_hasFDerivWithinAt_of_convex {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ n, ∀ x ∈ s, HasFDerivWithinAt (f n) (f' n x) s x)
    (hf' : ∀ n, ∀ x ∈ s, ‖f' n x‖ ≤ u n)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    {x : E} (hx : x ∈ s) :
    Summable fun n => f n x := by
  have h1 : Summable fun n => f n x - f n x₀ := by
    refine Summable.of_norm_bounded (hu.mul_right ‖x - x₀‖) fun n => ?_
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (hf n) (hf' n) hs hx₀ hx
  simpa using h1.add hf0

theorem hasFDerivWithinAt_tsum_of_convex {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ n, ∀ x ∈ s, HasFDerivWithinAt (f n) (f' n x) s x)
    (hf' : ∀ n, ∀ x ∈ s, ‖f' n x‖ ≤ u n)
    {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => ∑' n, f n y) (∑' n, f' n x) s x := by
  classical
  have hsum : ∀ y ∈ s, Summable fun n => f n y := fun y hy =>
    summable_of_summable_hasFDerivWithinAt_of_convex hs hu hf hf' hx₀ hf0 hy
  have hsum' : Summable fun n => f' n x := .of_norm_bounded hu fun n => hf' n x hx
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hc3 : (0 : ℝ) < c / 3 := by positivity
  -- a finite set `T` outside of which the bound series is small
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, ∑' n : {n // n ∉ T}, u n < c / 3 :=
    ((tendsto_tsum_compl_atTop_zero u).eventually (gt_mem_nhds hc3)).exists
  have hT' : ∑' n : ↥((↑T : Set ι)ᶜ), u n < c / 3 := hT
  have hL : ‖∑' n : ↥((↑T : Set ι)ᶜ), f' n x‖ ≤ ∑' n : ↥((↑T : Set ι)ᶜ), u n :=
    tsum_of_norm_bounded (hu.subtype ((↑T : Set ι)ᶜ)).hasSum fun n => hf' n x hx
  -- the finite part is differentiable
  have hfin : HasFDerivWithinAt (fun y => ∑ n ∈ T, f n y) (∑ n ∈ T, f' n x) s x :=
    HasFDerivWithinAt.fun_sum fun n _ => hf n x hx
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff] at hfin
  filter_upwards [hfin hc3, self_mem_nhdsWithin] with y hy1 hy2
  have hy := hsum y hy2
  -- the tail is controlled by the mean value inequality
  have hB : ‖(∑' n : ↥((↑T : Set ι)ᶜ), f n y) - ∑' n : ↥((↑T : Set ι)ᶜ), f n x‖
      ≤ (∑' n : ↥((↑T : Set ι)ᶜ), u n) * ‖y - x‖ := by
    have h1 : Summable fun n : ↥((↑T : Set ι)ᶜ) => f n y := hy.subtype _
    have h2 : Summable fun n : ↥((↑T : Set ι)ᶜ) => f n x := (hsum x hx).subtype _
    rw [← h1.tsum_sub h2]
    refine tsum_of_norm_bounded ((hu.subtype ((↑T : Set ι)ᶜ)).hasSum.mul_right ‖y - x‖)
      fun n => ?_
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (hf n) (hf' n) hs hx hy2
  have key : ∀ (a b a' b' : F) (L M : E →L[ℝ] F) (h : E),
      (a + b) - (a' + b') - (L + M) h = (a - a' - L h) + (b - b' - M h) := by
    intro a b a' b' L M h
    rw [ContinuousLinearMap.add_apply]
    abel
  rw [← hy.sum_add_tsum_compl (s := T), ← (hsum x hx).sum_add_tsum_compl (s := T),
    ← hsum'.sum_add_tsum_compl (s := T), key]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hy1 (norm_sub_le _ _)).trans ?_
  refine (add_le_add le_rfl (add_le_add hB (ContinuousLinearMap.le_opNorm _ _))).trans ?_
  have h3 := mul_le_mul_of_nonneg_right hT'.le (norm_nonneg (y - x))
  have h4 := mul_le_mul_of_nonneg_right (hL.trans hT'.le) (norm_nonneg (y - x))
  linarith

theorem hasDerivWithinAt_tsum_of_convex {s : Set ℝ} (hs : Convex ℝ s)
    {f : ι → ℝ → F} {f' : ι → ℝ → F} {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ n, ∀ x ∈ s, HasDerivWithinAt (f n) (f' n x) s x)
    (hf' : ∀ n, ∀ x ∈ s, ‖f' n x‖ ≤ u n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivWithinAt (fun y => ∑' n, f n y) (∑' n, f' n x) s x := by
  simp_rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at hf ⊢
  convert! hasFDerivWithinAt_tsum_of_convex hs hu hf ?_ hx₀ hf0 hx
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ F 1).map_tsum <|
      .of_norm_bounded hu fun n ↦ hf' n x hx
  · simpa

theorem iteratedFDerivWithin_tsum_apply_of_convex {s : Set E} (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s) {f : ι → E → F} {N : ℕ∞} {v : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : ι), ∀ x ∈ s, (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) {x : E} (hx : x ∈ s) :
    iteratedFDerivWithin ℝ k (fun y => ∑' i, f i y) s x
      = ∑' i, iteratedFDerivWithin ℝ k (f i) s x := by
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDerivWithin_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hk
    have IH' : ∀ y ∈ s, iteratedFDerivWithin ℝ k (fun y => ∑' i, f i y) s y
        = ∑' i, iteratedFDerivWithin ℝ k (f i) s y := fun y hy => IH h'k.le hy
    have A : Summable fun i => iteratedFDerivWithin ℝ k (f i) s x :=
      .of_norm_bounded (hv k h'k.le) fun i => h'f k i x hx h'k.le
    have hg : ∀ i, ∀ y ∈ s, HasFDerivWithinAt (iteratedFDerivWithin ℝ k (f i) s)
        (fderivWithin ℝ (iteratedFDerivWithin ℝ k (f i) s) s y) s y := fun i y hy =>
      ((hf i).differentiableOn_iteratedFDerivWithin (by exact_mod_cast h'k) hs' y
        hy).hasFDerivWithinAt
    have hg' : ∀ i, ∀ y ∈ s,
        ‖fderivWithin ℝ (iteratedFDerivWithin ℝ k (f i) s) s y‖ ≤ v (k + 1) i := by
      intro i y hy
      rw [norm_fderivWithin_iteratedFDerivWithin]
      exact h'f (k + 1) i y hy hk
    have hD : fderivWithin ℝ (fun y => ∑' i, iteratedFDerivWithin ℝ k (f i) s y) s x
        = ∑' i, fderivWithin ℝ (iteratedFDerivWithin ℝ k (f i) s) s x :=
      (hasFDerivWithinAt_tsum_of_convex hs (hv (k + 1) hk) hg hg' hx A hx).fderivWithin
        (hs' x hx)
    simp_rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply]
    rw [fderivWithin_congr (fun y hy => IH' y hy) (IH' x hx), hD]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E)
      F).symm.toContinuousLinearEquiv.map_tsum

theorem contDiffOn_tsum_of_convex {s : Set E} (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s) {f : ι → E → F} {N : ℕ∞} {v : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiffOn ℝ N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : ι), ∀ x ∈ s, (k : ℕ∞) ≤ N →
      ‖iteratedFDerivWithin ℝ k (f i) s x‖ ≤ v k i) :
    ContDiffOn ℝ N (fun x => ∑' i, f i x) s := by
  rw [contDiffOn_iff_continuousOn_differentiableOn hs']
  constructor
  · intro m hm
    refine ContinuousOn.congr (f := fun x => ∑' i, iteratedFDerivWithin ℝ m (f i) s x) ?_
      fun x hx => iteratedFDerivWithin_tsum_apply_of_convex hs hs' hf hv h'f hm hx
    refine continuousOn_tsum (fun i => ?_) (hv m hm) fun i x hx => h'f m i x hx hm
    exact (hf i).continuousOn_iteratedFDerivWithin (mod_cast hm) hs'
  · intro m hm
    have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.coe_add, ENat.coe_one] using Order.add_one_le_of_lt hm
    refine DifferentiableOn.congr (f := fun x => ∑' i, iteratedFDerivWithin ℝ m (f i) s x) ?_
      fun x hx => iteratedFDerivWithin_tsum_apply_of_convex hs hs' hf hv h'f hm.le hx
    intro x hx
    have A : Summable fun i => iteratedFDerivWithin ℝ m (f i) s x :=
      .of_norm_bounded (hv m hm.le) fun i => h'f m i x hx hm.le
    have hg : ∀ i, ∀ y ∈ s, HasFDerivWithinAt (iteratedFDerivWithin ℝ m (f i) s)
        (fderivWithin ℝ (iteratedFDerivWithin ℝ m (f i) s) s y) s y := fun i y hy =>
      ((hf i).differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm) hs' y
        hy).hasFDerivWithinAt
    have hg' : ∀ i, ∀ y ∈ s,
        ‖fderivWithin ℝ (iteratedFDerivWithin ℝ m (f i) s) s y‖ ≤ v (m + 1) i := by
      intro i y hy
      rw [norm_fderivWithin_iteratedFDerivWithin]
      exact h'f (m + 1) i y hy h'm
    exact (hasFDerivWithinAt_tsum_of_convex hs (hv (m + 1) h'm) hg hg' hx A
      hx).differentiableWithinAt

theorem contDiff_tsum_of_convex_univ {f : ι → E → F} {N : ℕ∞} {v : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiff ℝ N (f i))
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : ι) (x : E), (k : ℕ∞) ≤ N →
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i) :
    ContDiff ℝ N (fun x => ∑' i, f i x) := by
  rw [← contDiffOn_univ]
  refine contDiffOn_tsum_of_convex convex_univ uniqueDiffOn_univ (fun i => (hf i).contDiffOn)
    hv fun k i x _ hk => ?_
  rw [iteratedFDerivWithin_univ]
  exact h'f k i x hk

end TheoremB
