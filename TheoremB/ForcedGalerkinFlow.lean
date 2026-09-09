/-
  TheoremB/ForcedGalerkinFlow.lean
  Tier 8a, wave F2 of the Theorem B campaign (9 Sep 2026).

  Global existence for the FORCED Galerkin Navier-Stokes system, as pure
  siblings of GalerkinFlow.lean: no frozen statement is edited.  The forced
  right-hand side is spelled INLINE, exactly as in ForcedGalerkin.lean,

      (-(nu * ‖freq k‖^2)) • c t k + lerayProj k (convGal S (c t) k) + g t k

  so that at g = 0 a `simpa` converts the forced ODE clause into the frozen
  unforced one (`probe_forced_zero_feeds_frozen`, wave F1).

  What the file delivers:

  * The PUBLIC field clone `gfield_norm_le_ball` / `gfield_lip_ball`: the
    Galerkin vector field `gfield` is bounded and Lipschitz on every ball,
    with constants depending only on the viscosity, the box constants
    `fldFRQ S`, `fldFB S`, the box cardinality and the radius.  These are
    fresh declarations re-proving the PRIVATE `fldGfield_norm_le` /
    `fldGfield_lip` of GalerkinFlow.lean (with their private helpers cloned
    here); the frozen file is not touched — the SobolevNorms public-clone
    pattern is the precedent.

  * `gfieldForced`: the tier's only new definition — the Galerkin field with
    the restriction of the force to the box added, as a time-DEPENDENT
    vector field on the state space `GState S`.

  * `gflow_local_exists_forced`: local existence for the forced field by
    Picard-Lindelof in its time-dependent form (the four-field
    `IsPicardLindelof` structure at the pin: Lipschitz in space uniformly in
    time, continuous in time on the ball, bounded, and the step condition).
    The step depends only on the viscosity, the box, the norm bound `B` of
    the initial state and the sup bound `Gs` of the force — not on the
    initial state or the centre time.  Per-mode CONTINUITY of the force in
    time is what the pin's Picard-Lindelof needs; the force is taken on ALL
    of `ℝ` because the Picard-Lindelof windows may leave `[0, T]`.

  * `gflow_to_coeff_forced`: the coefficient bridge — a state-space solution,
    extended by zero off the box, solves the forced coefficient ODE at every
    interior time (the force is supported on the box, so off-box modes stay
    zero).

  * `ns_galerkin_local_existence_forced`: the uniform-step local existence
    in coefficient language.

  * `coeff_shift_forced`, `ns_galerkin_unique_around_forced`: the time shift
    and the TWO-SIDED uniqueness around time 0 that the seam-gluing
    induction applies to the shifted flows `c (Tn + ·)`, whose force is
    `g (Tn + ·)`.  The force cancels in the difference, so no hypothesis on
    `g` is needed.

  * `ns_galerkin_global_wellposed_forced`: the seam-gluing induction of
    `ns_galerkin_global_wellposed` with the FORCED trap
    (`ns_galerkin_forced_trap_icc`, wave F1) re-securing the seam bound: on
    the achieved window the trap keeps `en (c Tn) ≤ Es`, so every seam datum
    has coefficients bounded by `√Es`, and the same uniform step serves
    every seam.  The force sup bound is `Gs := √G` (`coeff_le_sqrt_en` on the
    supported force).  Existence, the box, and uniqueness on every horizon.

  * `ns_galerkin_global_flow_forced`: ONE forced flow per box serving every
    horizon at once, spliced along integer segments from the per-horizon
    flows; the uniqueness clause makes the splice seamless.

  CAVEAT (binding for every downstream claim): at g = 0 this chain is NOT a
  strengthening of the unforced chain.  The trap constant is kappa = 8 K
  (not K), the smallness is non-strict, and the box `(Es, Zs)` is a
  hypothesis rather than the energy/enstrophy of the datum.  The forced
  results must never be described as implying or improving the unforced
  ones; the only compiled direction is that the forced ODE clause at g = 0
  is the frozen one.

  Nothing here is new mathematics: this is the classical forced small-data
  Galerkin theory (Picard-Lindelof continuation under an a-priori bound).
  Textbook sources, named as references and NOT verified against by this
  file: Temam, Navier-Stokes Equations, Ch. III; Robinson-Rodrigo-Sadowski,
  The Three-Dimensional Navier-Stokes Equations, Ch. 6; Constantin-Foias,
  Navier-Stokes Equations, Ch. 6; Hale, Ordinary Differential Equations,
  Ch. I (Picard-Lindelof and continuation).

  CONTRACT: the nine theorem STATEMENTS and the one definition marked **F2**
  are frozen (rung10 Tier-8 blueprint, section 4a, wave F2).  If a statement
  cannot be proved as written, do not silently repair it: keep it, add a
  sibling, and report.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.GalerkinFlow
import TheoremB.ForcedGalerkin

namespace TheoremB

open Set

/-! ## The public field clone: box constants and algebra helpers

Fresh declarations mirroring the private `fld*` helpers of GalerkinFlow.lean
(78-340).  They are private here as well — nothing downstream needs them —
but the two capstones `gfield_norm_le_ball` / `gfield_lip_ball` are public. -/

private lemma ffdFRQ_nonneg (S : Finset (Fin 3 → ℤ)) : 0 ≤ fldFRQ S := by
  have h : 0 ≤ ∑ j ∈ S, ‖freq j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  unfold fldFRQ
  linarith

private lemma ffdFB_nonneg (S : Finset (Fin 3 → ℤ)) : 0 ≤ fldFB S := by
  have h : 0 ≤ ∑ j ∈ S, ‖freq j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  unfold fldFB
  linarith

private lemma ffdFreq_sq_le (S : Finset (Fin 3 → ℤ)) (s : ↥S) :
    ‖freq s.val‖ ^ 2 ≤ fldFRQ S := by
  have h := Finset.single_le_sum (f := fun j => ‖freq j‖ ^ 2)
    (fun j _ => sq_nonneg _) s.property
  unfold fldFRQ
  linarith

private lemma ffdFreqBound (S : Finset (Fin 3 → ℤ)) {x y : Fin 3 → ℤ}
    (hx : x ∈ S) (hy : y ∈ S) : ‖freq (x - y)‖ ≤ fldFB S := by
  have h1 : ‖freq x‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hx
  have h2 : ‖freq y‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hy
  rw [freq_sub]
  have h3 : ‖freq x - freq y‖ ≤ ‖freq x‖ + ‖freq y‖ := norm_sub_le _ _
  unfold fldFB
  linarith

private lemma ffdDotR_sub_left (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (v - w) r = dotR v r - dotR w r := by
  simp only [dotR, WithLp.ofLp_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma ffdCastCV_zero : castCV 0 = 0 := by
  ext j
  simp [castCV]

private lemma ffdFreq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext j
  simp [freq]

private lemma ffdLerayProj_sub (k : Fin 3 → ℤ) (v w : Vel) :
    lerayProj k (v - w) = lerayProj k v - lerayProj k w := by
  simp only [lerayProj, ffdDotR_sub_left, sub_div, sub_smul]
  abel

private lemma ffdLerayProj_zero (k : Fin 3 → ℤ) : lerayProj k 0 = 0 := by
  simp [lerayProj, dotR]

private lemma ffdNorm_lerayProj_le (k : Fin 3 → ℤ) (w : Vel) :
    ‖lerayProj k w‖ ≤ 2 * ‖w‖ := by
  by_cases hk : k = 0
  · subst hk
    simp only [lerayProj, ffdFreq_zero, ffdCastCV_zero, smul_zero, sub_zero]
    linarith [norm_nonneg w]
  · have h1 : (1 : ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    have hpos : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos h1
    have hstep : ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ ≤ ‖w‖ := by
      rw [norm_smul, norm_div, norm_castCV]
      have hcast : ‖((‖freq k‖ ^ 2 : ℝ) : ℂ)‖ = ‖freq k‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      rw [hcast, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖freq k‖ ^ 2)]
      calc ‖dotR w (freq k)‖ * ‖freq k‖
          ≤ (‖freq k‖ * ‖w‖) * ‖freq k‖ :=
            mul_le_mul_of_nonneg_right (norm_dotR_le w (freq k)) (norm_nonneg _)
        _ = ‖w‖ * ‖freq k‖ ^ 2 := by ring
    have htri : ‖lerayProj k w‖
        ≤ ‖w‖ + ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ := by
      simp only [lerayProj]
      exact norm_sub_le _ _
    linarith

private lemma ffdGext_sub_norm (S : Finset (Fin 3 → ℤ)) (x y : GState S)
    (l : Fin 3 → ℤ) : ‖gext S x l - gext S y l‖ ≤ ‖x - y‖ := by
  by_cases hl : l ∈ S
  · rw [gext_mem S x hl, gext_mem S y hl]
    exact norm_le_pi_norm (x - y) ⟨l, hl⟩
  · rw [gext_not_mem S x hl, gext_not_mem S y hl]
    simp

private lemma ffdConv_le (S : Finset (Fin 3 → ℤ)) (x : GState S) (k : Fin 3 → ℤ) :
    ‖convGal S (gext S x) k‖ ≤ (S.card : ℝ) * fldFB S * ‖x‖ ^ 2 := by
  by_cases hk : k ∈ S
  · have hxk : convGal S (gext S x) k =
        -∑ l ∈ S, (Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l) := by
      simp [convGal, hk]
    have hterm : ∀ l ∈ S,
        ‖(Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l)‖ ≤
          fldFB S * ‖x‖ ^ 2 := by
      intro l hl
      rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
      calc ‖dotR (gext S x l) (freq (k - l))‖ * ‖gext S x (k - l)‖
          ≤ (fldFB S * ‖x‖) * ‖x‖ := by
            apply mul_le_mul _ (norm_gext_le S x (k - l)) (norm_nonneg _)
              (mul_nonneg (ffdFB_nonneg S) (norm_nonneg _))
            calc ‖dotR (gext S x l) (freq (k - l))‖
                ≤ ‖freq (k - l)‖ * ‖gext S x l‖ := norm_dotR_le _ _
              _ ≤ fldFB S * ‖x‖ :=
                  mul_le_mul (ffdFreqBound S hk hl) (norm_gext_le S x l)
                    (norm_nonneg _) (ffdFB_nonneg S)
        _ = fldFB S * ‖x‖ ^ 2 := by ring
    rw [hxk, norm_neg]
    calc ‖∑ l ∈ S, (Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l)‖
        ≤ ∑ l ∈ S, ‖(Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l)‖ :=
          norm_sum_le _ _
      _ ≤ S.card • (fldFB S * ‖x‖ ^ 2) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (S.card : ℝ) * (fldFB S * ‖x‖ ^ 2) := nsmul_eq_mul _ _
      _ = (S.card : ℝ) * fldFB S * ‖x‖ ^ 2 := by ring
  · have h0 : convGal S (gext S x) k = 0 := by simp [convGal, hk]
    rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ffdFB_nonneg S)) (sq_nonneg _)

private lemma ffdConv_sub_le (S : Finset (Fin 3 → ℤ)) (M : ℝ) (hM : 0 ≤ M)
    (x y : GState S) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (k : Fin 3 → ℤ) :
    ‖convGal S (gext S x) k - convGal S (gext S y) k‖ ≤
      2 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ := by
  by_cases hk : k ∈ S
  · have hxk : convGal S (gext S x) k =
        -∑ l ∈ S, (Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l) := by
      simp [convGal, hk]
    have hyk : convGal S (gext S y) k =
        -∑ l ∈ S, (Complex.I * dotR (gext S y l) (freq (k - l))) • gext S y (k - l) := by
      simp [convGal, hk]
    have key : ‖(∑ l ∈ S, (Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l)) -
        ∑ l ∈ S, (Complex.I * dotR (gext S y l) (freq (k - l))) • gext S y (k - l)‖ ≤
        2 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ l ∈ S,
          ‖(Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l) -
            (Complex.I * dotR (gext S y l) (freq (k - l))) • gext S y (k - l)‖ ≤
          2 * (fldFB S * M * ‖x - y‖) := by
        intro l hl
        set a₁ : ℂ := Complex.I * dotR (gext S x l) (freq (k - l)) with ha₁
        set a₂ : ℂ := Complex.I * dotR (gext S y l) (freq (k - l)) with ha₂
        have hdecomp : a₁ • gext S x (k - l) - a₂ • gext S y (k - l) =
            (a₁ - a₂) • gext S x (k - l) +
              a₂ • (gext S x (k - l) - gext S y (k - l)) := by
          rw [sub_smul, smul_sub]
          abel
        rw [hdecomp]
        have h1 : ‖(a₁ - a₂) • gext S x (k - l)‖ ≤ (fldFB S * ‖x - y‖) * M := by
          rw [norm_smul]
          have ha : ‖a₁ - a₂‖ ≤ fldFB S * ‖x - y‖ := by
            have hd : a₁ - a₂ =
                Complex.I * dotR (gext S x l - gext S y l) (freq (k - l)) := by
              rw [ha₁, ha₂, ffdDotR_sub_left, mul_sub]
            rw [hd, norm_mul, Complex.norm_I, one_mul]
            calc ‖dotR (gext S x l - gext S y l) (freq (k - l))‖
                ≤ ‖freq (k - l)‖ * ‖gext S x l - gext S y l‖ := norm_dotR_le _ _
              _ ≤ fldFB S * ‖x - y‖ :=
                  mul_le_mul (ffdFreqBound S hk hl) (ffdGext_sub_norm S x y l)
                    (norm_nonneg _) (ffdFB_nonneg S)
          have hA : ‖gext S x (k - l)‖ ≤ M := le_trans (norm_gext_le S x _) hx
          exact mul_le_mul ha hA (norm_nonneg _)
            (mul_nonneg (ffdFB_nonneg S) (norm_nonneg _))
        have h2 : ‖a₂ • (gext S x (k - l) - gext S y (k - l))‖ ≤
            (fldFB S * M) * ‖x - y‖ := by
          rw [norm_smul]
          have ha : ‖a₂‖ ≤ fldFB S * M := by
            rw [ha₂, norm_mul, Complex.norm_I, one_mul]
            calc ‖dotR (gext S y l) (freq (k - l))‖
                ≤ ‖freq (k - l)‖ * ‖gext S y l‖ := norm_dotR_le _ _
              _ ≤ fldFB S * M :=
                  mul_le_mul (ffdFreqBound S hk hl) (le_trans (norm_gext_le S y l) hy)
                    (norm_nonneg _) (ffdFB_nonneg S)
          exact mul_le_mul ha (ffdGext_sub_norm S x y (k - l)) (norm_nonneg _)
            (mul_nonneg (ffdFB_nonneg S) hM)
        calc ‖(a₁ - a₂) • gext S x (k - l) +
              a₂ • (gext S x (k - l) - gext S y (k - l))‖
            ≤ ‖(a₁ - a₂) • gext S x (k - l)‖ +
                ‖a₂ • (gext S x (k - l) - gext S y (k - l))‖ := norm_add_le _ _
          _ ≤ (fldFB S * ‖x - y‖) * M + (fldFB S * M) * ‖x - y‖ := add_le_add h1 h2
          _ = 2 * (fldFB S * M * ‖x - y‖) := by ring
      calc ‖∑ l ∈ S,
            ((Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l) -
              (Complex.I * dotR (gext S y l) (freq (k - l))) • gext S y (k - l))‖
          ≤ ∑ l ∈ S,
              ‖(Complex.I * dotR (gext S x l) (freq (k - l))) • gext S x (k - l) -
                (Complex.I * dotR (gext S y l) (freq (k - l))) • gext S y (k - l)‖ :=
            norm_sum_le _ _
        _ ≤ S.card • (2 * (fldFB S * M * ‖x - y‖)) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = (S.card : ℝ) * (2 * (fldFB S * M * ‖x - y‖)) := nsmul_eq_mul _ _
        _ = 2 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ := by ring
    rw [hxk, hyk, neg_sub_neg, norm_sub_rev]
    exact key
  · have hx0 : convGal S (gext S x) k = 0 := by simp [convGal, hk]
    have hy0 : convGal S (gext S y) k = 0 := by simp [convGal, hk]
    rw [hx0, hy0, sub_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (ffdFB_nonneg S)) hM) (norm_nonneg _)

/-! ## The public field clone: the two capstones -/

/-- **F2, public field bound.**  The Galerkin vector field is bounded on
every ball, with a constant depending only on the viscosity, the box
constants and the radius.  Public clone of the private
`fldGfield_norm_le` of GalerkinFlow.lean. -/
theorem gfield_norm_le_ball {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (M : ℝ) (hM : 0 ≤ M) (x : GState S) (hx : ‖x‖ ≤ M) :
    ‖gfield ν S x‖ ≤ ν * fldFRQ S * M + 2 * (S.card : ℝ) * fldFB S * M ^ 2 := by
  have hnn1 : 0 ≤ ν * fldFRQ S * M := mul_nonneg (mul_nonneg hν.le (ffdFRQ_nonneg S)) hM
  have hnn2 : 0 ≤ 2 * (S.card : ℝ) * fldFB S * M ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (ffdFB_nonneg S))
      (sq_nonneg _)
  rw [pi_norm_le_iff_of_nonneg (by linarith)]
  intro s
  have hxs : ‖x s‖ ≤ M := le_trans (norm_le_pi_norm x s) hx
  have hsq : ‖x‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg x]
  have h1 : ‖(-(ν * ‖freq s.val‖ ^ 2)) • x s‖ ≤ ν * fldFRQ S * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg hν.le (sq_nonneg _))]
    calc ν * ‖freq s.val‖ ^ 2 * ‖x s‖
        ≤ ν * fldFRQ S * ‖x s‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (ffdFreq_sq_le S s) hν.le) (norm_nonneg _)
      _ ≤ ν * fldFRQ S * M :=
          mul_le_mul_of_nonneg_left hxs (mul_nonneg hν.le (ffdFRQ_nonneg S))
  have h2 : ‖lerayProj s.val (convGal S (gext S x) s.val)‖ ≤
      2 * (S.card : ℝ) * fldFB S * M ^ 2 := by
    calc ‖lerayProj s.val (convGal S (gext S x) s.val)‖
        ≤ 2 * ‖convGal S (gext S x) s.val‖ := ffdNorm_lerayProj_le _ _
      _ ≤ 2 * ((S.card : ℝ) * fldFB S * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (ffdConv_le S x s.val) (by norm_num)
      _ ≤ 2 * ((S.card : ℝ) * fldFB S * M ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hsq
            (mul_nonneg (Nat.cast_nonneg _) (ffdFB_nonneg S))
      _ = 2 * (S.card : ℝ) * fldFB S * M ^ 2 := by ring
  calc ‖gfield ν S x s‖
      = ‖(-(ν * ‖freq s.val‖ ^ 2)) • x s + lerayProj s.val (convGal S (gext S x) s.val)‖ :=
        rfl
    _ ≤ ‖(-(ν * ‖freq s.val‖ ^ 2)) • x s‖ +
          ‖lerayProj s.val (convGal S (gext S x) s.val)‖ := norm_add_le _ _
    _ ≤ ν * fldFRQ S * M + 2 * (S.card : ℝ) * fldFB S * M ^ 2 := add_le_add h1 h2

/-- **F2, public Lipschitz bound.**  The Galerkin vector field is Lipschitz
on every ball, with a constant depending only on the viscosity, the box
constants and the radius.  Public clone of the private `fldGfield_lip` of
GalerkinFlow.lean. -/
theorem gfield_lip_ball {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (M : ℝ) (hM : 0 ≤ M) (x y : GState S) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖gfield ν S x - gfield ν S y‖ ≤
      (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * M) * ‖x - y‖ := by
  have hnn1 : 0 ≤ ν * fldFRQ S := mul_nonneg hν.le (ffdFRQ_nonneg S)
  have hnn2 : 0 ≤ 4 * (S.card : ℝ) * fldFB S * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (ffdFB_nonneg S)) hM
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _))]
  intro s
  have hcoord : (gfield ν S x - gfield ν S y) s =
      (-(ν * ‖freq s.val‖ ^ 2)) • (x s - y s) +
        (lerayProj s.val (convGal S (gext S x) s.val) -
          lerayProj s.val (convGal S (gext S y) s.val)) := by
    show ((-(ν * ‖freq s.val‖ ^ 2)) • x s + lerayProj s.val (convGal S (gext S x) s.val)) -
        ((-(ν * ‖freq s.val‖ ^ 2)) • y s + lerayProj s.val (convGal S (gext S y) s.val)) = _
    rw [smul_sub]
    abel
  have h1 : ‖(-(ν * ‖freq s.val‖ ^ 2)) • (x s - y s)‖ ≤ ν * fldFRQ S * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg hν.le (sq_nonneg _))]
    have hxy : ‖x s - y s‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) s
    calc ν * ‖freq s.val‖ ^ 2 * ‖x s - y s‖
        ≤ ν * fldFRQ S * ‖x s - y s‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (ffdFreq_sq_le S s) hν.le) (norm_nonneg _)
      _ ≤ ν * fldFRQ S * ‖x - y‖ := mul_le_mul_of_nonneg_left hxy hnn1
  have h2 : ‖lerayProj s.val (convGal S (gext S x) s.val) -
      lerayProj s.val (convGal S (gext S y) s.val)‖ ≤
      4 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ := by
    rw [← ffdLerayProj_sub]
    calc ‖lerayProj s.val (convGal S (gext S x) s.val - convGal S (gext S y) s.val)‖
        ≤ 2 * ‖convGal S (gext S x) s.val - convGal S (gext S y) s.val‖ :=
          ffdNorm_lerayProj_le _ _
      _ ≤ 2 * (2 * (S.card : ℝ) * fldFB S * M * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (ffdConv_sub_le S M hM x y hx hy s.val) (by norm_num)
      _ = 4 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ := by ring
  calc ‖(gfield ν S x - gfield ν S y) s‖
      = ‖(-(ν * ‖freq s.val‖ ^ 2)) • (x s - y s) +
          (lerayProj s.val (convGal S (gext S x) s.val) -
            lerayProj s.val (convGal S (gext S y) s.val))‖ := by rw [hcoord]
    _ ≤ ‖(-(ν * ‖freq s.val‖ ^ 2)) • (x s - y s)‖ +
          ‖lerayProj s.val (convGal S (gext S x) s.val) -
            lerayProj s.val (convGal S (gext S y) s.val)‖ := norm_add_le _ _
    _ ≤ ν * fldFRQ S * ‖x - y‖ + 4 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ :=
        add_le_add h1 h2
    _ = (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * M) * ‖x - y‖ := by ring

/-! ## The forced field and forced local existence -/

/-- **F2, the forced Galerkin vector field** on the state space: the
Galerkin field with the restriction of the force to the box added — a
time-DEPENDENT vector field. -/
noncomputable def gfieldForced (ν : ℝ) (S : Finset (Fin 3 → ℤ))
    (g : ℝ → (Fin 3 → ℤ) → Vel) (t : ℝ) (x : GState S) : GState S :=
  gfield ν S x + gres S (g t)

/-- **F2, local existence for the forced Galerkin field, with a step uniform
in the initial bound and the force bound.**  Picard-Lindelof in the pin's
time-dependent form; the step `ε` depends only on `ν`, the box `S`, the
norm bound `B` and the force sup bound `Gs` — not on the initial state, the
centre time, or the force itself.  Per-mode continuity of the force in
time is the continuity field of `IsPicardLindelof`. -/
theorem gflow_local_exists_forced {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (B Gs : ℝ) (hB : 0 ≤ B) (hGs : 0 ≤ Gs)
    {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hgc : ∀ k, Continuous fun t => g t k)
    (hgb : ∀ t k, ‖g t k‖ ≤ Gs) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x₀ : GState S), ‖x₀‖ ≤ B → ∀ t₀ : ℝ,
      ∃ α : ℝ → GState S, α t₀ = x₀ ∧
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt α (gfieldForced ν S g t (α t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  classical
  set L₀ : ℝ := ν * fldFRQ S * (B + 1) + 2 * (S.card : ℝ) * fldFB S * (B + 1) ^ 2
    with hL₀def
  set K₀ : ℝ := ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * (B + 1) + 1 with hK₀def
  have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
  have hL₀ : 0 ≤ L₀ := by
    rw [hL₀def]
    have h1 : 0 ≤ ν * fldFRQ S * (B + 1) :=
      mul_nonneg (mul_nonneg hν.le (ffdFRQ_nonneg S)) hB1
    have h2 : 0 ≤ 2 * (S.card : ℝ) * fldFB S * (B + 1) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (ffdFB_nonneg S))
        (sq_nonneg _)
    linarith
  set L₁ : ℝ := L₀ + Gs + 1 with hL₁def
  have hL₁ : (0 : ℝ) < L₁ := by rw [hL₁def]; linarith
  have hK₀ : 0 ≤ K₀ := by
    rw [hK₀def]
    have h1 : 0 ≤ ν * fldFRQ S := mul_nonneg hν.le (ffdFRQ_nonneg S)
    have h2 : 0 ≤ 4 * (S.card : ℝ) * fldFB S * (B + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (ffdFB_nonneg S))
        hB1
    linarith
  refine ⟨1 / L₁, div_pos one_pos hL₁, ?_⟩
  intro x₀ hx₀ t₀
  set ε : ℝ := 1 / L₁ with hεdef
  have hε : 0 < ε := div_pos one_pos hL₁
  have ht₀mem : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith
  have hballnorm : ∀ z : GState S,
      z ∈ Metric.closedBall x₀ ((1 : NNReal) : ℝ) → ‖z‖ ≤ B + 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, NNReal.coe_one] at hz
    have h := norm_sub_norm_le z x₀
    linarith
  have hgres : ∀ t : ℝ, ‖gres S (g t)‖ ≤ Gs := by
    intro t
    rw [pi_norm_le_iff_of_nonneg hGs]
    exact fun s => hgb t s.val
  have hPL : IsPicardLindelof (gfieldForced ν S g)
      (⟨t₀, ht₀mem⟩ : ↥(Icc (t₀ - ε) (t₀ + ε))) x₀ 1 0
      (Real.toNNReal L₁) (Real.toNNReal K₀) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in space, uniformly in time: the force is a constant shift
      intro t _
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro z hz w hw
      have hz1 : ‖z‖ ≤ B + 1 := hballnorm z hz
      have hw1 : ‖w‖ ≤ B + 1 := hballnorm w hw
      have hlip := gfield_lip_ball hν S (B + 1) hB1 z w hz1 hw1
      have hsub : gfieldForced ν S g t z - gfieldForced ν S g t w =
          gfield ν S z - gfield ν S w := by
        simp only [gfieldForced]
        abel
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK₀, hK₀def, hsub]
      have hfac : (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * (B + 1)) * ‖z - w‖ ≤
          (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * (B + 1) + 1) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith
    · -- continuity in time on the ball: per-mode continuity of the force
      intro x _
      refine (continuous_const.add (continuous_pi fun s => ?_)).continuousOn
      exact hgc s.val
    · -- the norm bound: field bound plus force bound
      intro t _ z hz
      have hz1 : ‖z‖ ≤ B + 1 := hballnorm z hz
      have hb := gfield_norm_le_ball hν S (B + 1) hB1 z hz1
      rw [Real.coe_toNNReal _ hL₁.le]
      calc ‖gfieldForced ν S g t z‖
          = ‖gfield ν S z + gres S (g t)‖ := rfl
        _ ≤ ‖gfield ν S z‖ + ‖gres S (g t)‖ := norm_add_le _ _
        _ ≤ L₀ + Gs := add_le_add (by rw [hL₀def]; exact hb) (hgres t)
        _ ≤ L₁ := by rw [hL₁def]; linarith
    · -- the step condition
      show ((Real.toNNReal L₁ : NNReal) : ℝ) *
          max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) ≤ ((1 : NNReal) : ℝ) - ((0 : NNReal) : ℝ)
      rw [Real.coe_toNNReal _ hL₁.le, NNReal.coe_one, NNReal.coe_zero, sub_zero]
      have h1 : t₀ + ε - t₀ = ε := by ring
      have h2 : t₀ - (t₀ - ε) = ε := by ring
      rw [h1, h2, max_self, hεdef]
      exact le_of_eq (mul_one_div_cancel (ne_of_gt hL₁))
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht => hαd t ht⟩

/-! ## The coefficient bridge under forcing -/

/-- **F2, the coefficient bridge.**  A state-space solution of the forced
field, extended by zero off the box, solves the forced coefficient ODE at
every interior time.  Off the box the force vanishes by hypothesis, so the
zero extension is consistent. -/
theorem gflow_to_coeff_forced {ν : ℝ} {S : Finset (Fin 3 → ℤ)}
    {g : ℝ → (Fin 3 → ℤ) → Vel} (hgsupp : ∀ (t : ℝ) k, k ∉ S → g t k = 0)
    {α : ℝ → GState S} {a b : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (gfieldForced ν S g t (α t)) (Icc a b) t) :
    (∀ (t : ℝ) k, k ∉ S → gext S (α t) k = 0) ∧
    (∀ t ∈ Ioo a b, ∀ k, HasDerivAt (fun s => gext S (α s) k)
      ((-(ν * ‖freq k‖ ^ 2)) • gext S (α t) k +
        lerayProj k (convGal S (gext S (α t)) k) + g t k) t) := by
  constructor
  · intro t k hk
    exact gext_not_mem S (α t) hk
  · intro t ht k
    have hmem : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hD : HasDerivAt α (gfieldForced ν S g t (α t)) t :=
      (hα t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
    by_cases hk : k ∈ S
    · have hfun : (fun s => gext S (α s) k) = fun s => α s ⟨k, hk⟩ := by
        funext s
        exact gext_mem S (α s) hk
      have hcoord : HasDerivAt (fun s => α s ⟨k, hk⟩)
          (gfieldForced ν S g t (α t) ⟨k, hk⟩) t :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ↥S => Vel)
          (⟨k, hk⟩ : ↥S)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hD
      have hval : gfieldForced ν S g t (α t) ⟨k, hk⟩ =
          (-(ν * ‖freq k‖ ^ 2)) • α t ⟨k, hk⟩ +
            lerayProj k (convGal S (gext S (α t)) k) + g t k := rfl
      rw [hfun, gext_mem S (α t) hk, ← hval]
      exact hcoord
    · have hfun : (fun s => gext S (α s) k) = fun _ => (0 : Vel) := by
        funext s
        exact gext_not_mem S (α s) hk
      have hconv : convGal S (gext S (α t)) k = 0 := by
        simp [convGal, hk]
      rw [hfun, gext_not_mem S (α t) hk, hconv, smul_zero, ffdLerayProj_zero,
        add_zero, hgsupp t k hk, add_zero]
      exact hasDerivAt_const t 0

/-- **F2, uniform-step local existence in coefficient language, under
forcing.**  From any supported datum with coefficients bounded by `B`, at
any centre time, a coefficient flow of the forced Galerkin system exists on
the open window of half-width `ε`, and `ε` depends only on `(ν, S, B, Gs)`. -/
theorem ns_galerkin_local_existence_forced {ν : ℝ} (hν : 0 < ν)
    (S : Finset (Fin 3 → ℤ)) (B Gs : ℝ) (hB : 0 ≤ B) (hGs : 0 ≤ Gs)
    {g : ℝ → (Fin 3 → ℤ) → Vel} (hgsupp : ∀ (t : ℝ) k, k ∉ S → g t k = 0)
    (hgc : ∀ k, Continuous fun t => g t k) (hgb : ∀ t k, ‖g t k‖ ≤ Gs) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ k, k ∉ S → c₀ k = 0) → (∀ k, ‖c₀ k‖ ≤ B) → ∀ t₀ : ℝ,
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c t₀ = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t := by
  obtain ⟨ε, hε, hex⟩ := gflow_local_exists_forced hν S B Gs hB hGs hgc hgb
  refine ⟨ε, hε, ?_⟩
  intro c₀ hsupp₀ hb t₀
  have hx₀ : ‖gres S c₀‖ ≤ B := by
    rw [pi_norm_le_iff_of_nonneg hB]
    exact fun s => hb s.val
  obtain ⟨α, hα0, hαODE⟩ := hex (gres S c₀) hx₀ t₀
  obtain ⟨hsupp, hODE⟩ := gflow_to_coeff_forced hgsupp hαODE
  refine ⟨fun t => gext S (α t), ?_, hsupp, hODE⟩
  show gext S (α t₀) = c₀
  rw [hα0, gext_gres S hsupp₀]

/-! ## Time shift and two-sided uniqueness -/

/-- **F2, the time shift.**  Public clone of the private `coeff_shift` of
GalerkinFlow.lean: a derivative at `τ + t` is a derivative of the shifted
flow at `t`. -/
theorem coeff_shift_forced {c : ℝ → (Fin 3 → ℤ) → Vel} {v : Vel}
    {k : Fin 3 → ℤ} {τ t : ℝ}
    (h : HasDerivAt (fun s => c s k) v (τ + t)) :
    HasDerivAt (fun s => c (τ + s) k) v t := by
  have hid : HasDerivAt (fun s : ℝ => τ + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add τ
  have h2 := HasDerivAt.scomp t h hid
  rw [one_smul] at h2
  exact h2

/-- **F2, two-sided uniqueness of forced Galerkin flows around time `0`** —
the window form the seam-gluing induction needs.  Replay of
`ns_galerkin_unique_around`: the force cancels in the difference, so the
defect obeys the unforced defect ODE and NO hypothesis on `g` is needed. -/
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
    ∀ t ∈ Icc a b, ∀ k, c₁ t k = c₂ t k := by
  -- the defect
  set d : ℝ → (Fin 3 → ℤ) → Vel := fun t k => c₁ t k - c₂ t k with hd
  set R : ℝ → (Fin 3 → ℤ) → Vel := fun t k =>
    lerayProj k (convGal S (c₁ t) k) - lerayProj k (convGal S (c₂ t) k) with hR
  set lam : (Fin 3 → ℤ) → ℝ := fun k => ν * ‖freq k‖ ^ 2 with hlam
  have hlamnn : ∀ k, 0 ≤ lam k := fun k => by positivity
  have hdderiv : ∀ s ∈ Icc a b, ∀ k, HasDerivAt (fun u => d u k)
      ((-(lam k)) • d s k + R s k) s := by
    intro s hs k
    have h3 := (hODE₁ s hs k).sub (hODE₂ s hs k)
    have hval : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convGal S (c₁ s) k)
          + g s k) -
        ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convGal S (c₂ s) k) + g s k) =
        (-(lam k)) • d s k + R s k := by
      rw [hlam, hd, hR]
      simp only [smul_sub]
      abel
    rw [hval] at h3
    exact h3
  have hdsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0 := by
    intro s k hk
    rw [hd]
    simp only
    rw [hs₁ s k hk, hs₂ s k hk, sub_self]
  have hd0 : ∀ k, d 0 k = 0 := by
    intro k
    rw [hd]
    simp only
    rw [h0 k, sub_self]
  -- bound both fields on the window
  obtain ⟨M, hM0, hMb⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc a b,
      (∀ j, ‖c₁ s j‖ ≤ M) ∧ (∀ j, ‖c₂ s j‖ ≤ M) := by
    have hmode : ∀ j, ContinuousOn (fun s : ℝ => c₁ s j) (Icc a b) := fun j t ht =>
      (hODE₁ t ht j).continuousAt.continuousWithinAt
    have hmode₂ : ∀ j, ContinuousOn (fun s : ℝ => c₂ s j) (Icc a b) := fun j t ht =>
      (hODE₂ t ht j).continuousAt.continuousWithinAt
    have hcont : ContinuousOn
        (fun s : ℝ => (∑ j ∈ S, ‖c₁ s j‖) + ∑ j ∈ S, ‖c₂ s j‖) (Icc a b) := by
      apply ContinuousOn.add
      · exact continuousOn_finsetSum S fun j _ => (hmode j).norm
      · exact continuousOn_finsetSum S fun j _ => (hmode₂ j).norm
    have hne : (Icc a b).Nonempty := ⟨0, ha, hb⟩
    obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
    refine ⟨(∑ j ∈ S, ‖c₁ s₀ j‖) + ∑ j ∈ S, ‖c₂ s₀ j‖, by positivity, ?_⟩
    intro s hs
    have hsum1 : 0 ≤ ∑ j ∈ S, ‖c₁ s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    have hsum2 : 0 ≤ ∑ j ∈ S, ‖c₂ s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    constructor
    · intro j
      by_cases hj : j ∈ S
      · calc ‖c₁ s j‖ ≤ ∑ i ∈ S, ‖c₁ s i‖ :=
              Finset.single_le_sum (f := fun i => ‖c₁ s i‖)
                (fun i _ => norm_nonneg _) hj
          _ ≤ (∑ i ∈ S, ‖c₁ s i‖) + ∑ i ∈ S, ‖c₂ s i‖ := by linarith
          _ ≤ _ := hmax hs
      · rw [hs₁ s j hj]
        simp only [norm_zero]
        have := hmax hs
        positivity
    · intro j
      by_cases hj : j ∈ S
      · calc ‖c₂ s j‖ ≤ ∑ i ∈ S, ‖c₂ s i‖ :=
              Finset.single_le_sum (f := fun i => ‖c₂ s i‖)
                (fun i _ => norm_nonneg _) hj
          _ ≤ (∑ i ∈ S, ‖c₁ s i‖) + ∑ i ∈ S, ‖c₂ s i‖ := by linarith
          _ ≤ _ := hmax hs
      · rw [hs₂ s j hj]
        simp only [norm_zero]
        have := hmax hs
        positivity
  obtain ⟨C, hC0, hCb⟩ := two_flow_forcing_bound (S := S)
  have hRb : ∀ s ∈ Icc a b, ∀ j ∈ S,
      ‖R s j‖ ^ 2 ≤ (C * M ^ 2) * (∑ i ∈ S, ‖d s i‖ ^ 2) := by
    intro s hs j _
    have := hCb (hs₁ s) (hs₂ s) hM0 (hMb s hs).1 (hMb s hs).2 j
    simpa [hR, hd] using this
  intro t ht k
  have hz := defect_vanishes_on' (mul_nonneg hC0 (by positivity)) ha hb
    hlamnn hdderiv hdsupp hRb hd0 t ht k
  have : c₁ t k - c₂ t k = 0 := hz
  exact sub_eq_zero.mp this

/-! ## The seam-gluing induction under forcing -/

/-- **F2, global well-posedness of the forced Galerkin system inside the
box.**  Under the forced thresholds, for every symmetric zero-free box `S`,
every supported, real, divergence-free, per-mode continuous force of L2
size at most `G`, and every supported real divergence-free datum inside the
box `(Es, Zs)`: on EVERY horizon `[0, T]` a coefficient flow of the forced
Galerkin system exists, stays inside the box, and is the UNIQUE such flow.
Existence is by seam-gluing induction on uniform-step local solutions
(`ns_galerkin_local_existence_forced`); the forced trap
(`ns_galerkin_forced_trap_icc`) re-secures the seam bound `√Es` at every
seam, and the force sup bound is `√G`. -/
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
          c' 0 = c₀ → ∀ t ∈ Icc (0:ℝ) T, ∀ k, c' t k = c t k) := by
  obtain ⟨κ, hκ, htrap⟩ := ns_galerkin_forced_trap_icc
  refine ⟨κ, hκ, ?_⟩
  intro ν Es Zs G hν hEs hZs hκE hGE hGZ S hS0 hSsym g hgsupp hgreal hgdiv hgen hgc
    c₀ hsupp₀ hreal₀ hdiv₀ h0E h0Z T
  -- the seam bound and the force sup bound
  set B := Real.sqrt Es with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set Gs := Real.sqrt G with hGsdef
  have hGs0 : 0 ≤ Gs := Real.sqrt_nonneg _
  have hgb : ∀ (t : ℝ) k, ‖g t k‖ ≤ Gs := fun t k =>
    (coeff_le_sqrt_en (hgsupp t) k).trans (Real.sqrt_le_sqrt (hgen t))
  obtain ⟨ε, hε, hloc⟩ :=
    ns_galerkin_local_existence_forced hν S B Gs hB0 hGs0 hgsupp hgc hgb
  -- the forced trap, instantiated on the data
  have htrap' : ∀ {T' : ℝ} {c : ℝ → (Fin 3 → ℤ) → Vel}, c 0 = c₀ →
      (∀ (t : ℝ) k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T', ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) →
      ∀ t ∈ Icc (0:ℝ) T', en (c t) ≤ Es ∧ ens (c t) ≤ Zs := by
    intro T' c hc0 hcs hcODE
    have hreal : RealField (c 0) := by rw [hc0]; exact hreal₀
    have hdiv : DivFree (c 0) := by rw [hc0]; exact hdiv₀
    have hE : en (c 0) ≤ Es := by rw [hc0]; exact h0E
    have hZ : ens (c 0) ≤ Zs := by rw [hc0]; exact h0Z
    exact htrap hν hEs hZs hκE hGE hGZ hS0 hSsym (fun t _ k hk => hcs t k hk)
      (fun t _ k hk => hgsupp t k hk) (fun t _ => hgreal t) (fun t _ => hgdiv t)
      (fun t _ => hgen t) hreal hdiv hcODE hE hZ
  -- the inductive construction: a flow with the ODE on [0, n·(ε/2)]
  have key : ∀ n : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
      ∀ t ∈ Icc (0:ℝ) ((n : ℝ) * (ε / 2)), ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t := by
    intro n
    induction n with
    | zero =>
      have hb₀ : ∀ k, ‖c₀ k‖ ≤ B := fun k =>
        (coeff_le_sqrt_en hsupp₀ k).trans (Real.sqrt_le_sqrt h0E)
      obtain ⟨c, hc0, hcs, hcODE⟩ := hloc hsupp₀ hb₀ 0
      refine ⟨c, hc0, hcs, ?_⟩
      intro t ht k
      have ht0 : t = 0 := by
        have := ht.2
        simp only [Nat.cast_zero, zero_mul] at this
        exact le_antisymm this ht.1
      subst ht0
      exact hcODE 0 ⟨by linarith, by linarith⟩ k
    | succ n ih =>
      obtain ⟨c, hc0, hcs, hcODE⟩ := ih
      set Tn : ℝ := (n : ℝ) * (ε / 2) with hTn
      have hTn0 : 0 ≤ Tn := by positivity
      -- the forced trap on the achieved window gives the seam bound
      have htrapn := htrap' hc0 hcs hcODE
      have henTn : en (c Tn) ≤ Es := (htrapn Tn ⟨hTn0, le_refl Tn⟩).1
      have hbTn : ∀ k, ‖c Tn k‖ ≤ B := fun k =>
        (coeff_le_sqrt_en (fun j hj => hcs Tn j hj) k).trans
          (Real.sqrt_le_sqrt henTn)
      -- local solve centred at the seam
      obtain ⟨d, hdTn, hds, hdODE⟩ := hloc (fun j hj => hcs Tn j hj) hbTn Tn
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · -- first step: the local solution alone covers [0, ε/2]
        subst hn0
        have hTn0' : Tn = 0 := by simp [hTn]
        refine ⟨d, ?_, hds, ?_⟩
        · rw [← hTn0', hdTn, hTn0', hc0]
        · intro t ht k
          have h2 : t ≤ ε / 2 := by
            have := ht.2
            push_cast at this
            linarith
          have htlt : t < Tn + ε := by rw [hTn0']; linarith
          have htgt : Tn - ε < t := by rw [hTn0']; linarith [ht.1]
          exact hdODE t ⟨htgt, htlt⟩ k
      · -- general step: glue at the seam using overlap uniqueness
        have hTnge : ε / 2 ≤ Tn := by
          rw [hTn]
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnpos
          nlinarith [hε]
        -- overlap agreement via the shifted flows (whose force is `g (Tn + ·)`)
        have hagree : ∀ s ∈ Icc (-(ε/2)) (0:ℝ), ∀ k, c (Tn + s) k = d (Tn + s) k := by
          have h1 := ns_galerkin_unique_around_forced (ν := ν) (a := -(ε/2)) (b := 0)
            hν.le (by linarith) (le_refl 0)
            (c₁ := fun s => c (Tn + s)) (c₂ := fun s => d (Tn + s))
            (g := fun s => g (Tn + s))
            (fun t k hk => hcs (Tn + t) k hk) (fun t k hk => hds (Tn + t) k hk)
            ?_ ?_ ?_
          · exact fun s hs k => h1 s hs k
          · intro s hs k
            have hmem : Tn + s ∈ Icc (0:ℝ) Tn := by
              constructor
              · linarith [hs.1, hTnge]
              · linarith [hs.2]
            have hmem' : Tn + s ∈ Icc (0:ℝ) ((n:ℝ) * (ε/2)) := by
              rw [← hTn]; exact hmem
            exact coeff_shift_forced (hcODE (Tn + s) hmem' k)
          · intro s hs k
            have hmem : Tn + s ∈ Ioo (Tn - ε) (Tn + ε) := by
              constructor
              · linarith [hs.1, hε]
              · linarith [hs.2, hε]
            exact coeff_shift_forced (hdODE (Tn + s) hmem k)
          · intro k
            show c (Tn + 0) k = d (Tn + 0) k
            rw [add_zero, hdTn]
        -- the glued flow
        refine ⟨fun t => if t ≤ Tn then c t else d t, ?_, ?_, ?_⟩
        · simp only [if_pos hTn0]
          exact hc0
        · intro t k hk
          by_cases htn : t ≤ Tn
          · simp only [if_pos htn]; exact hcs t k hk
          · simp only [if_neg htn]; exact hds t k hk
        · intro t ht k
          have htub : t ≤ Tn + ε / 2 := by
            have h2 : t ≤ ((n:ℝ) + 1) * (ε / 2) := by exact_mod_cast ht.2
            rw [hTn]; linarith
          rcases lt_trichotomy t Tn with hlt | heq | hgt
          · -- left of the seam: transfer from c
            have hev : (fun s => (if s ≤ Tn then c s else d s) k) =ᶠ[nhds t]
                (fun s => c s k) :=
              Filter.eventuallyEq_of_mem (Iio_mem_nhds hlt)
                (fun s hs => by rw [if_pos (le_of_lt (mem_Iio.mp hs))])
            have hval : (if t ≤ Tn then c t else d t) = c t := if_pos hlt.le
            show HasDerivAt (fun s => (if s ≤ Tn then c s else d s) k)
              ((-(ν * ‖freq k‖ ^ 2)) • (if t ≤ Tn then c t else d t) k +
                lerayProj k (convGal S (if t ≤ Tn then c t else d t) k) + g t k) t
            rw [hval]
            exact (hcODE t ⟨ht.1, hlt.le⟩ k).congr_of_eventuallyEq hev
          · -- at the seam: transfer from d; the value matches by construction
            have hev : (fun s => (if s ≤ Tn then c s else d s) k) =ᶠ[nhds t]
                (fun s => d s k) := by
              refine Filter.eventuallyEq_of_mem
                (Ioo_mem_nhds (show t - ε/2 < t by linarith)
                  (show t < t + ε/2 by linarith))
                (fun s hs => ?_)
              by_cases hstn : s ≤ Tn
              · simp only [if_pos hstn]
                have hs' : s - Tn ∈ Icc (-(ε/2)) (0:ℝ) := by
                  constructor
                  · have := hs.1
                    rw [heq] at this
                    linarith
                  · linarith [hstn]
                have h := hagree (s - Tn) hs' k
                rwa [add_sub_cancel] at h
              · simp only [if_neg hstn]
            have hval : (if t ≤ Tn then c t else d t) = c t := if_pos heq.le
            have hcd : c t = d t := by rw [heq, ← hdTn]
            show HasDerivAt (fun s => (if s ≤ Tn then c s else d s) k)
              ((-(ν * ‖freq k‖ ^ 2)) • (if t ≤ Tn then c t else d t) k +
                lerayProj k (convGal S (if t ≤ Tn then c t else d t) k) + g t k) t
            rw [hval, hcd]
            have hODEd := hdODE t
              ⟨by rw [heq]; linarith [hε, hTnge],
               by rw [heq]; linarith [hε]⟩ k
            exact hODEd.congr_of_eventuallyEq hev
          · -- right of the seam: transfer from d
            have hev : (fun s => (if s ≤ Tn then c s else d s) k) =ᶠ[nhds t]
                (fun s => d s k) :=
              Filter.eventuallyEq_of_mem (Ioi_mem_nhds hgt)
                (fun s hs => by rw [if_neg (not_le.mpr (mem_Ioi.mp hs))])
            have hval : (if t ≤ Tn then c t else d t) = d t := if_neg (not_le.mpr hgt)
            show HasDerivAt (fun s => (if s ≤ Tn then c s else d s) k)
              ((-(ν * ‖freq k‖ ^ 2)) • (if t ≤ Tn then c t else d t) k +
                lerayProj k (convGal S (if t ≤ Tn then c t else d t) k) + g t k) t
            rw [hval]
            exact (hdODE t ⟨by linarith [hTnge, hε], by linarith [hε]⟩ k
              ).congr_of_eventuallyEq hev
  -- assemble at an arbitrary horizon
  by_cases hT : (0:ℝ) ≤ T
  · obtain ⟨m, hm⟩ := exists_nat_ge (T / (ε / 2))
    have hTm : T ≤ (m : ℝ) * (ε / 2) := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ε / 2)] at hm
      linarith
    obtain ⟨c, hc0, hcs, hcODE⟩ := key m
    have hODET : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t :=
      fun t ht k => hcODE t ⟨ht.1, ht.2.trans hTm⟩ k
    have htrapT := htrap' hc0 hcs hODET
    refine ⟨c, hc0, hcs, hODET, htrapT, ?_⟩
    intro c' hcs' hODE' hc0'
    have hmatch : ∀ k, c' 0 k = c 0 k := fun k => by rw [hc0', hc0]
    exact fun t ht k => ns_galerkin_unique_around_forced hν.le (le_refl 0) hT hcs'
      (fun t k hk => hcs t k hk) hODE' hODET hmatch t ht k
  · refine ⟨fun _ => c₀, rfl, fun t k hk => hsupp₀ k hk, ?_, ?_, ?_⟩
    · intro t ht
      exact absurd (ht.1.trans ht.2) hT
    · intro t ht
      exact absurd (ht.1.trans ht.2) hT
    · intro c' _ _ _ t ht
      exact absurd (ht.1.trans ht.2) hT

/-! ## The forced eternal Galerkin flow -/

/-- **F2, the forced eternal Galerkin flow** — ONE flow per box serving EVERY
horizon at once.  It solves the forced Galerkin ODE two-sidedly at every
`t ≥ 0`, stays inside the box forever, and on every window `[0, T]` any
competitor with the same datum agrees with it.  Built by splicing the
per-horizon flows of `ns_galerkin_global_wellposed_forced` along integer
segments; the uniqueness clause makes the splice seamless. -/
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
          c' 0 = c₀ → ∀ t ∈ Icc (0:ℝ) T, ∀ k, c' t k = c t k) := by
  obtain ⟨κ, hκ, hwp⟩ := ns_galerkin_global_wellposed_forced
  refine ⟨κ, hκ, ?_⟩
  intro ν Es Zs G hν hEs hZs hκE hGE hGZ S hS0 hSsym g hgsupp hgreal hgdiv hgen hgc
    c₀ hsupp₀ hreal₀ hdiv₀ h0E h0Z
  have hinst := hwp hν hEs hZs hκE hGE hGZ hS0 hSsym hgsupp hgreal hgdiv hgen hgc
    hsupp₀ hreal₀ hdiv₀ h0E h0Z
  -- one chosen flow per natural horizon
  have hex : ∀ n : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs) ∧
      (∀ c' : ℝ → (Fin 3 → ℤ) → Vel, (∀ (t : ℝ) k, k ∉ S → c' t k = 0) →
        (∀ t ∈ Icc (0:ℝ) (n:ℝ), ∀ k, HasDerivAt (fun s => c' s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c' t k + lerayProj k (convGal S (c' t) k) + g t k) t) →
        c' 0 = c₀ → ∀ t ∈ Icc (0:ℝ) (n:ℝ), ∀ k, c' t k = c t k) :=
    fun n => hinst (n : ℝ)
  choose F hF0 hFsupp hFODE hFtrap hFuniq using hex
  -- pairwise agreement of the chosen flows on overlapping horizons
  have hA : ∀ m n : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ (m:ℝ) → s ≤ (n:ℝ) →
      ∀ k, F m s k = F n s k := by
    intro m n s hs0 hsm hsn k
    have hmin_m : ((min m n : ℕ) : ℝ) ≤ (m:ℝ) := by
      exact_mod_cast min_le_left m n
    have hmin_n : ((min m n : ℕ) : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast min_le_right m n
    have hsmin : s ≤ ((min m n : ℕ) : ℝ) := by
      rw [Nat.cast_min]
      exact le_min hsm hsn
    have hm := hFuniq (min m n) (F m) (hFsupp m)
      (fun t ht j => hFODE m t ⟨ht.1, ht.2.trans hmin_m⟩ j) (hF0 m)
      s ⟨hs0, hsmin⟩ k
    have hn := hFuniq (min m n) (F n) (hFsupp n)
      (fun t ht j => hFODE n t ⟨ht.1, ht.2.trans hmin_n⟩ j) (hF0 n)
      s ⟨hs0, hsmin⟩ k
    rw [hm, hn]
  -- the eternal flow: spliced along integer segments
  set nseg : ℝ → ℕ := fun s => if s ≤ 1 then 2 else Nat.floor s + 2 with hnseg
  set c : ℝ → (Fin 3 → ℤ) → Vel := fun s => F (nseg s) s with hcdef
  -- basic segment facts
  have hseg_ge : ∀ s : ℝ, 0 ≤ s → s ≤ (nseg s : ℝ) := by
    intro s hs
    rw [hnseg]
    by_cases h1 : s ≤ 1
    · simp only [if_pos h1]
      norm_num
      linarith
    · simp only [if_neg h1]
      push_cast
      have := Nat.lt_floor_add_one s
      linarith
  have hcval : ∀ s : ℝ, c s = F (nseg s) s := fun s => rfl
  -- the ODE on the half line
  have hODE : ∀ t ∈ Ici (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t := by
    intro t ht k
    by_cases htc : t < 1/2
    · -- near the origin the splice is uniformly the horizon-2 flow
      have hev : (fun s => c s k) =ᶠ[nhds t] (fun s => F 2 s k) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (show t - 1/2 < t by linarith)
            (show t < t + 1/2 by linarith)) (fun s hs => ?_)
        have hs1 : s ≤ 1 := by
          have := hs.2
          linarith
        show F (nseg s) s k = F 2 s k
        rw [hnseg]
        simp only [if_pos hs1]
      have hval : c t = F 2 t := by
        rw [hcval, hnseg]
        have ht1 : t ≤ 1 := by linarith
        simp only [if_pos ht1]
      rw [hval]
      have hODE2 := hFODE 2 t ⟨ht, by push_cast; linarith⟩ k
      exact hODE2.congr_of_eventuallyEq hev
    · -- away from the origin: everything near t agrees with one big horizon
      rw [not_lt] at htc
      set N : ℕ := Nat.floor t + 3 with hN
      have htN : t + 2 < (N:ℝ) + 1 := by
        rw [hN]
        push_cast
        have := Nat.lt_floor_add_one t
        linarith
      have hagree : ∀ s ∈ Ioo (t - 1/2) (t + 1/2), ∀ j, c s j = F N s j := by
        intro s hs j
        have hs0 : (0:ℝ) ≤ s := by
          have := hs.1
          linarith
        have hsseg : s ≤ (nseg s : ℝ) := hseg_ge s hs0
        have hsN : s ≤ (N:ℝ) := by
          have := hs.2
          linarith
        exact hA (nseg s) N s hs0 hsseg hsN j
      have hev : (fun s => c s k) =ᶠ[nhds t] (fun s => F N s k) :=
        Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (show t - 1/2 < t by linarith)
            (show t < t + 1/2 by linarith))
          (fun s hs => hagree s hs k)
      have hval : c t = F N t := by
        funext j
        exact hagree t ⟨by linarith, by linarith⟩ j
      rw [hval]
      have hODEN := hFODE N t ⟨ht, by linarith⟩ k
      exact hODEN.congr_of_eventuallyEq hev
  refine ⟨c, ?_, ?_, hODE, ?_, ?_⟩
  · -- initial value
    show F (nseg 0) 0 = c₀
    rw [hnseg]
    simp only [if_pos (by norm_num : (0:ℝ) ≤ 1)]
    exact hF0 2
  · -- support
    intro t k hk
    exact hFsupp (nseg t) t k hk
  · -- the box on the half line
    intro t ht
    have := hFtrap (nseg t) t ⟨ht, hseg_ge t ht⟩
    rw [hcval]
    exact this
  · -- uniqueness against every horizon
    intro T c' hsupp' hODE' h0'
    by_cases hT : (0:ℝ) ≤ T
    · obtain ⟨cT, hcT0, hcTsupp, hcTODE, _, hcTuniq⟩ := hinst T
      have h1 : ∀ t ∈ Icc (0:ℝ) T, ∀ k, c' t k = cT t k :=
        hcTuniq c' hsupp' hODE' h0'
      have h2 : ∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = cT t k :=
        hcTuniq c (fun t k hk => hFsupp (nseg t) t k hk)
          (fun t ht k => hODE t ht.1 k)
          (by show F (nseg 0) 0 = c₀
              rw [hnseg]
              simp only [if_pos (by norm_num : (0:ℝ) ≤ 1)]
              exact hF0 2)
      intro t ht k
      rw [h1 t ht k, ← h2 t ht k]
    · intro t ht
      exact absurd (ht.1.trans ht.2) hT

end TheoremB
