/-
# Global existence for the Galerkin Navier-Stokes system

The M5 summit file. Three layers:

1. **The state-space flow** (`gflow_local_exists`): the Galerkin vector field
   on the finite product `↥S → Vel` is bounded and Lipschitz on balls, with
   constants depending only on `(ν, S, B)`; Picard-Lindelöf then gives a
   local solution with a step size UNIFORM in all initial data of norm `≤ B`
   and in the center time — the key to gluing.
2. **The coefficient bridge** (`gflow_to_coeff`): a state-space solution,
   extended by zero off the box, solves the coefficient ODE of
   `TheoremB.NSGalerkin` at every interior time.
3. **The seam-gluing induction** (`ns_galerkin_global_wellposed`): the trap
   (`ns_galerkin_trap_zero_data_icc`, closed-endpoint form) re-secures the
   uniform bound at every seam, local solutions overlap, uniqueness
   (`ns_galerkin_unique_around`) makes them agree on overlaps, and the glued
   flow solves globally. Existence, descent, and uniqueness on every horizon.
-/
import TheoremB.GalerkinLocal

namespace TheoremB

open Set

/-- The Galerkin state space: coefficients on the box, as a finite product. -/
abbrev GState (S : Finset (Fin 3 → ℤ)) := ↥S → Vel

/-- Extend a state to a coefficient field (zero off the box). -/
noncomputable def gext (S : Finset (Fin 3 → ℤ)) (x : GState S) :
    (Fin 3 → ℤ) → Vel :=
  fun k => if h : k ∈ S then x ⟨k, h⟩ else 0

/-- Restrict a coefficient field to a state. -/
noncomputable def gres (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel) :
    GState S :=
  fun s => c s.val

/-- The Galerkin Navier-Stokes vector field on the state space. -/
noncomputable def gfield (ν : ℝ) (S : Finset (Fin 3 → ℤ)) (x : GState S) :
    GState S :=
  fun s => (-(ν * ‖freq s.val‖ ^ 2)) • x s +
    lerayProj s.val (convGal S (gext S x) s.val)

lemma gext_mem (S : Finset (Fin 3 → ℤ)) (x : GState S) {k : Fin 3 → ℤ}
    (hk : k ∈ S) : gext S x k = x ⟨k, hk⟩ := by
  simp [gext, hk]

lemma gext_not_mem (S : Finset (Fin 3 → ℤ)) (x : GState S) {k : Fin 3 → ℤ}
    (hk : k ∉ S) : gext S x k = 0 := by
  simp [gext, hk]

lemma gext_gres (S : Finset (Fin 3 → ℤ)) {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) : gext S (gres S c) = c := by
  funext k
  by_cases hk : k ∈ S
  · simp [gext, gres, hk]
  · rw [gext_not_mem S _ hk, hsupp k hk]

lemma norm_gext_le (S : Finset (Fin 3 → ℤ)) (x : GState S) (k : Fin 3 → ℤ) :
    ‖gext S x k‖ ≤ ‖x‖ := by
  by_cases hk : k ∈ S
  · rw [gext_mem S x hk]
    exact norm_le_pi_norm x ⟨k, hk⟩
  · rw [gext_not_mem S x hk]
    simp [norm_nonneg]

/-! ### Agent FIELD: box constants -/

/-- Frequency-square bound over the box (`≥ 1` by construction). -/
noncomputable def fldFRQ (S : Finset (Fin 3 → ℤ)) : ℝ :=
  1 + ∑ j ∈ S, ‖freq j‖ ^ 2

/-- Frequency-difference bound over the box (`≥ 1` by construction). -/
noncomputable def fldFB (S : Finset (Fin 3 → ℤ)) : ℝ :=
  1 + 2 * ∑ j ∈ S, ‖freq j‖

private lemma fldFRQ_nonneg (S : Finset (Fin 3 → ℤ)) : 0 ≤ fldFRQ S := by
  have h : 0 ≤ ∑ j ∈ S, ‖freq j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  unfold fldFRQ
  linarith

private lemma fldFB_nonneg (S : Finset (Fin 3 → ℤ)) : 0 ≤ fldFB S := by
  have h : 0 ≤ ∑ j ∈ S, ‖freq j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  unfold fldFB
  linarith

private lemma fldFreq_sq_le (S : Finset (Fin 3 → ℤ)) (s : ↥S) :
    ‖freq s.val‖ ^ 2 ≤ fldFRQ S := by
  have h := Finset.single_le_sum (f := fun j => ‖freq j‖ ^ 2)
    (fun j _ => sq_nonneg _) s.property
  unfold fldFRQ
  linarith

private lemma fldFreqBound (S : Finset (Fin 3 → ℤ)) {x y : Fin 3 → ℤ}
    (hx : x ∈ S) (hy : y ∈ S) : ‖freq (x - y)‖ ≤ fldFB S := by
  have h1 : ‖freq x‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hx
  have h2 : ‖freq y‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hy
  rw [freq_sub]
  have h3 : ‖freq x - freq y‖ ≤ ‖freq x‖ + ‖freq y‖ := norm_sub_le _ _
  unfold fldFB
  linarith

/-! ### Agent FIELD: algebra transplants -/

private lemma fldDotR_sub_left (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (v - w) r = dotR v r - dotR w r := by
  simp only [dotR, WithLp.ofLp_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma fldCastCV_zero : castCV 0 = 0 := by
  ext j
  simp [castCV]

private lemma fldFreq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext j
  simp [freq]

private lemma fldLerayProj_sub (k : Fin 3 → ℤ) (v w : Vel) :
    lerayProj k (v - w) = lerayProj k v - lerayProj k w := by
  simp only [lerayProj, fldDotR_sub_left, sub_div, sub_smul]
  abel

private lemma fldNorm_lerayProj_le (k : Fin 3 → ℤ) (w : Vel) :
    ‖lerayProj k w‖ ≤ 2 * ‖w‖ := by
  by_cases hk : k = 0
  · subst hk
    simp only [lerayProj, fldFreq_zero, fldCastCV_zero, smul_zero, sub_zero]
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

/-! ### Agent FIELD: gext difference and convection bounds -/

private lemma fldGext_sub_norm (S : Finset (Fin 3 → ℤ)) (x y : GState S)
    (l : Fin 3 → ℤ) : ‖gext S x l - gext S y l‖ ≤ ‖x - y‖ := by
  by_cases hl : l ∈ S
  · rw [gext_mem S x hl, gext_mem S y hl]
    exact norm_le_pi_norm (x - y) ⟨l, hl⟩
  · rw [gext_not_mem S x hl, gext_not_mem S y hl]
    simp

private lemma fldConv_le (S : Finset (Fin 3 → ℤ)) (x : GState S) (k : Fin 3 → ℤ) :
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
              (mul_nonneg (fldFB_nonneg S) (norm_nonneg _))
            calc ‖dotR (gext S x l) (freq (k - l))‖
                ≤ ‖freq (k - l)‖ * ‖gext S x l‖ := norm_dotR_le _ _
              _ ≤ fldFB S * ‖x‖ :=
                  mul_le_mul (fldFreqBound S hk hl) (norm_gext_le S x l)
                    (norm_nonneg _) (fldFB_nonneg S)
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
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (fldFB_nonneg S)) (sq_nonneg _)

private lemma fldConv_sub_le (S : Finset (Fin 3 → ℤ)) (M : ℝ) (hM : 0 ≤ M)
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
              rw [ha₁, ha₂, fldDotR_sub_left, mul_sub]
            rw [hd, norm_mul, Complex.norm_I, one_mul]
            calc ‖dotR (gext S x l - gext S y l) (freq (k - l))‖
                ≤ ‖freq (k - l)‖ * ‖gext S x l - gext S y l‖ := norm_dotR_le _ _
              _ ≤ fldFB S * ‖x - y‖ :=
                  mul_le_mul (fldFreqBound S hk hl) (fldGext_sub_norm S x y l)
                    (norm_nonneg _) (fldFB_nonneg S)
          have hA : ‖gext S x (k - l)‖ ≤ M := le_trans (norm_gext_le S x _) hx
          exact mul_le_mul ha hA (norm_nonneg _)
            (mul_nonneg (fldFB_nonneg S) (norm_nonneg _))
        have h2 : ‖a₂ • (gext S x (k - l) - gext S y (k - l))‖ ≤
            (fldFB S * M) * ‖x - y‖ := by
          rw [norm_smul]
          have ha : ‖a₂‖ ≤ fldFB S * M := by
            rw [ha₂, norm_mul, Complex.norm_I, one_mul]
            calc ‖dotR (gext S y l) (freq (k - l))‖
                ≤ ‖freq (k - l)‖ * ‖gext S y l‖ := norm_dotR_le _ _
              _ ≤ fldFB S * M :=
                  mul_le_mul (fldFreqBound S hk hl) (le_trans (norm_gext_le S y l) hy)
                    (norm_nonneg _) (fldFB_nonneg S)
          exact mul_le_mul ha (fldGext_sub_norm S x y (k - l)) (norm_nonneg _)
            (mul_nonneg (fldFB_nonneg S) hM)
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
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fldFB_nonneg S)) hM) (norm_nonneg _)

/-! ### Agent FIELD: field bound and Lipschitz bound on a ball -/

private lemma fldGfield_norm_le {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (M : ℝ) (hM : 0 ≤ M) (x : GState S) (hx : ‖x‖ ≤ M) :
    ‖gfield ν S x‖ ≤ ν * fldFRQ S * M + 2 * (S.card : ℝ) * fldFB S * M ^ 2 := by
  have hnn1 : 0 ≤ ν * fldFRQ S * M := mul_nonneg (mul_nonneg hν.le (fldFRQ_nonneg S)) hM
  have hnn2 : 0 ≤ 2 * (S.card : ℝ) * fldFB S * M ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fldFB_nonneg S))
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
            (mul_le_mul_of_nonneg_left (fldFreq_sq_le S s) hν.le) (norm_nonneg _)
      _ ≤ ν * fldFRQ S * M :=
          mul_le_mul_of_nonneg_left hxs (mul_nonneg hν.le (fldFRQ_nonneg S))
  have h2 : ‖lerayProj s.val (convGal S (gext S x) s.val)‖ ≤
      2 * (S.card : ℝ) * fldFB S * M ^ 2 := by
    calc ‖lerayProj s.val (convGal S (gext S x) s.val)‖
        ≤ 2 * ‖convGal S (gext S x) s.val‖ := fldNorm_lerayProj_le _ _
      _ ≤ 2 * ((S.card : ℝ) * fldFB S * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (fldConv_le S x s.val) (by norm_num)
      _ ≤ 2 * ((S.card : ℝ) * fldFB S * M ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hsq
            (mul_nonneg (Nat.cast_nonneg _) (fldFB_nonneg S))
      _ = 2 * (S.card : ℝ) * fldFB S * M ^ 2 := by ring
  calc ‖gfield ν S x s‖
      = ‖(-(ν * ‖freq s.val‖ ^ 2)) • x s + lerayProj s.val (convGal S (gext S x) s.val)‖ :=
        rfl
    _ ≤ ‖(-(ν * ‖freq s.val‖ ^ 2)) • x s‖ +
          ‖lerayProj s.val (convGal S (gext S x) s.val)‖ := norm_add_le _ _
    _ ≤ ν * fldFRQ S * M + 2 * (S.card : ℝ) * fldFB S * M ^ 2 := add_le_add h1 h2

private lemma fldGfield_lip {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (M : ℝ) (hM : 0 ≤ M) (x y : GState S) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖gfield ν S x - gfield ν S y‖ ≤
      (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * M) * ‖x - y‖ := by
  have hnn1 : 0 ≤ ν * fldFRQ S := mul_nonneg hν.le (fldFRQ_nonneg S)
  have hnn2 : 0 ≤ 4 * (S.card : ℝ) * fldFB S * M :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fldFB_nonneg S)) hM
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
            (mul_le_mul_of_nonneg_left (fldFreq_sq_le S s) hν.le) (norm_nonneg _)
      _ ≤ ν * fldFRQ S * ‖x - y‖ := mul_le_mul_of_nonneg_left hxy hnn1
  have h2 : ‖lerayProj s.val (convGal S (gext S x) s.val) -
      lerayProj s.val (convGal S (gext S y) s.val)‖ ≤
      4 * (S.card : ℝ) * fldFB S * M * ‖x - y‖ := by
    rw [← fldLerayProj_sub]
    calc ‖lerayProj s.val (convGal S (gext S x) s.val - convGal S (gext S y) s.val)‖
        ≤ 2 * ‖convGal S (gext S x) s.val - convGal S (gext S y) s.val‖ :=
          fldNorm_lerayProj_le _ _
      _ ≤ 2 * (2 * (S.card : ℝ) * fldFB S * M * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (fldConv_sub_le S M hM x y hx hy s.val) (by norm_num)
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

/-! ### Agent FIELD: the capstone -/

/-- **Local existence for the Galerkin field, with a step uniform in the
initial bound.**  The step `ε` depends only on `ν`, the box `S`, and the
norm bound `B` — not on the initial state or the initial time. -/
theorem gflow_local_exists {ν : ℝ} (hν : 0 < ν) (S : Finset (Fin 3 → ℤ))
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x₀ : GState S), ‖x₀‖ ≤ B → ∀ t₀ : ℝ,
      ∃ α : ℝ → GState S, α t₀ = x₀ ∧
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt α (gfield ν S (α t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  classical
  set L₀ : ℝ := ν * fldFRQ S * (B + 1) + 2 * (S.card : ℝ) * fldFB S * (B + 1) ^ 2
    with hL₀def
  set K₀ : ℝ := ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * (B + 1) + 1 with hK₀def
  have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
  have hL₀ : 0 ≤ L₀ := by
    rw [hL₀def]
    have h1 : 0 ≤ ν * fldFRQ S * (B + 1) :=
      mul_nonneg (mul_nonneg hν.le (fldFRQ_nonneg S)) hB1
    have h2 : 0 ≤ 2 * (S.card : ℝ) * fldFB S * (B + 1) ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fldFB_nonneg S))
        (sq_nonneg _)
    linarith
  have hL₁ : (0 : ℝ) < L₀ + 1 := by linarith
  have hK₀ : 0 ≤ K₀ := by
    rw [hK₀def]
    have h1 : 0 ≤ ν * fldFRQ S := mul_nonneg hν.le (fldFRQ_nonneg S)
    have h2 : 0 ≤ 4 * (S.card : ℝ) * fldFB S * (B + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fldFB_nonneg S))
        hB1
    linarith
  refine ⟨1 / (L₀ + 1), div_pos one_pos hL₁, ?_⟩
  intro x₀ hx₀ t₀
  set ε : ℝ := 1 / (L₀ + 1) with hεdef
  have hε : 0 < ε := div_pos one_pos hL₁
  have ht₀mem : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith
  have hballnorm : ∀ z : GState S,
      z ∈ Metric.closedBall x₀ ((1 : NNReal) : ℝ) → ‖z‖ ≤ B + 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, NNReal.coe_one] at hz
    have h := norm_sub_norm_le z x₀
    linarith
  have hPL : IsPicardLindelof (fun _ : ℝ => gfield ν S)
      (⟨t₀, ht₀mem⟩ : ↥(Icc (t₀ - ε) (t₀ + ε))) x₀ 1 0
      (Real.toNNReal (L₀ + 1)) (Real.toNNReal K₀) := by
    refine IsPicardLindelof.of_time_independent ?_ ?_ ?_
    · intro z hz
      have hz1 : ‖z‖ ≤ B + 1 := hballnorm z hz
      have hb := fldGfield_norm_le hν S (B + 1) hB1 z hz1
      rw [Real.coe_toNNReal _ (le_of_lt hL₁), hL₀def]
      linarith
    · refine LipschitzOnWith.of_dist_le_mul ?_
      intro z hz w hw
      have hz1 : ‖z‖ ≤ B + 1 := hballnorm z hz
      have hw1 : ‖w‖ ≤ B + 1 := hballnorm w hw
      have hlip := fldGfield_lip hν S (B + 1) hB1 z w hz1 hw1
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK₀, hK₀def]
      have hfac : (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * (B + 1)) * ‖z - w‖ ≤
          (ν * fldFRQ S + 4 * (S.card : ℝ) * fldFB S * (B + 1) + 1) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith
    · show ((Real.toNNReal (L₀ + 1) : NNReal) : ℝ) *
          max ((t₀ + ε) - t₀) (t₀ - (t₀ - ε)) ≤ ((1 : NNReal) : ℝ) - ((0 : NNReal) : ℝ)
      rw [Real.coe_toNNReal _ (le_of_lt hL₁), NNReal.coe_one, NNReal.coe_zero, sub_zero]
      have h1 : t₀ + ε - t₀ = ε := by ring
      have h2 : t₀ - (t₀ - ε) = ε := by ring
      rw [h1, h2, max_self, hεdef]
      exact le_of_eq (mul_one_div_cancel (ne_of_gt hL₁))
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, hα0, fun t ht => hαd t ht⟩

-- ==================== Agent BRIDGE: transplanted private helpers ====================

private lemma brDotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

private lemma brLerayProj_zero (k : Fin 3 → ℤ) : lerayProj k 0 = 0 := by
  simp [lerayProj, brDotR_zero_left]

-- ==================== Agent BRIDGE: main theorem ====================

theorem gflow_to_coeff {ν : ℝ} {S : Finset (Fin 3 → ℤ)} {α : ℝ → GState S} {a b : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (gfield ν S (α t)) (Icc a b) t) :
    (∀ (t : ℝ) k, k ∉ S → gext S (α t) k = 0) ∧
    (∀ t ∈ Ioo a b, ∀ k, HasDerivAt (fun s => gext S (α s) k)
      ((-(ν * ‖freq k‖ ^ 2)) • gext S (α t) k +
        lerayProj k (convGal S (gext S (α t)) k)) t) := by
  constructor
  · intro t k hk
    exact gext_not_mem S (α t) hk
  · intro t ht k
    have hmem : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hD : HasDerivAt α (gfield ν S (α t)) t :=
      (hα t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
    by_cases hk : k ∈ S
    · have hfun : (fun s => gext S (α s) k) = fun s => α s ⟨k, hk⟩ := by
        funext s
        exact gext_mem S (α s) hk
      have hcoord : HasDerivAt (fun s => α s ⟨k, hk⟩)
          (gfield ν S (α t) ⟨k, hk⟩) t :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ↥S => Vel)
          (⟨k, hk⟩ : ↥S)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hD
      have hval : gfield ν S (α t) ⟨k, hk⟩ =
          (-(ν * ‖freq k‖ ^ 2)) • α t ⟨k, hk⟩ +
            lerayProj k (convGal S (gext S (α t)) k) := rfl
      rw [hfun, gext_mem S (α t) hk, ← hval]
      exact hcoord
    · have hfun : (fun s => gext S (α s) k) = fun _ => (0 : Vel) := by
        funext s
        exact gext_not_mem S (α s) hk
      have hconv : convGal S (gext S (α t)) k = 0 := by
        simp [convGal, hk]
      rw [hfun, gext_not_mem S (α t) hk, hconv, smul_zero, brLerayProj_zero,
        add_zero]
      exact hasDerivAt_const t 0

/-- Every coefficient is bounded by the square root of the energy. -/
lemma coeff_le_sqrt_en {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (k : Fin 3 → ℤ) :
    ‖c k‖ ≤ Real.sqrt (en c) := by
  have hsum : Summable fun j => ‖c j‖ ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
  have hle : ‖c k‖ ^ 2 ≤ en c := by
    have := hsum.le_tsum k (fun j _ => sq_nonneg _)
    simpa [en] using this
  calc ‖c k‖ = Real.sqrt (‖c k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (en c) := Real.sqrt_le_sqrt hle

private lemma coeff_shift {c : ℝ → (Fin 3 → ℤ) → Vel} {v : Vel}
    {k : Fin 3 → ℤ} {τ t : ℝ}
    (h : HasDerivAt (fun s => c s k) v (τ + t)) :
    HasDerivAt (fun s => c (τ + s) k) v t := by
  have hid : HasDerivAt (fun s : ℝ => τ + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add τ
  have h2 := HasDerivAt.scomp t h hid
  rw [one_smul] at h2
  exact h2

/-- **Uniform-step local existence in coefficient language**: for each
viscosity, box and bound `B` there is a single step size `ε` such that from
ANY supported initial datum with coefficients bounded by `B`, at ANY center
time, a coefficient flow exists solving the Galerkin ODE on the open window. -/
theorem ns_galerkin_local_existence {ν : ℝ} (hν : 0 < ν)
    (S : Finset (Fin 3 → ℤ)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ k, k ∉ S → c₀ k = 0) → (∀ k, ‖c₀ k‖ ≤ B) → ∀ t₀ : ℝ,
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c t₀ = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t := by
  obtain ⟨ε, hε, hex⟩ := gflow_local_exists hν S B hB
  refine ⟨ε, hε, ?_⟩
  intro c₀ hsupp₀ hb t₀
  have hx₀ : ‖gres S c₀‖ ≤ B := by
    rw [pi_norm_le_iff_of_nonneg hB]
    exact fun s => hb s.val
  obtain ⟨α, hα0, hαODE⟩ := hex (gres S c₀) hx₀ t₀
  obtain ⟨hsupp, hODE⟩ := gflow_to_coeff hαODE
  refine ⟨fun t => gext S (α t), ?_, hsupp, hODE⟩
  show gext S (α t₀) = c₀
  rw [hα0, gext_gres S hsupp₀]

/-- **Two-sided uniqueness of Galerkin flows around time `0`** — the window
form the seam-gluing induction needs. -/
theorem ns_galerkin_unique_around {ν a b : ℝ} (hν : 0 ≤ ν) (ha : a ≤ 0)
    (hb : 0 ≤ b) {S : Finset (Fin 3 → ℤ)}
    {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel}
    (hs₁ : ∀ (t : ℝ) k, k ∉ S → c₁ t k = 0)
    (hs₂ : ∀ (t : ℝ) k, k ∉ S → c₂ t k = 0)
    (hODE₁ : ∀ t ∈ Icc a b, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convGal S (c₁ t) k)) t)
    (hODE₂ : ∀ t ∈ Icc a b, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convGal S (c₂ t) k)) t)
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
    have hval : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convGal S (c₁ s) k)) -
        ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convGal S (c₂ s) k)) =
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

private lemma ep_tsum_eq_sum (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → Vel} (hsupp : ∀ k, k ∉ S → c k = 0) :
    ∑' k, w k * ‖c k‖ ^ 2 = ∑ k ∈ S, w k * ‖c k‖ ^ 2 :=
  tsum_eq_sum fun k hk => by rw [hsupp k hk]; simp

/-- **Closed-endpoint form of the localized zero-data trap**: the descent
bounds and the strict smallness hold on the CLOSED window `Icc 0 T` — the
seam-restart lemma for the gluing induction. -/
theorem ns_galerkin_trap_zero_data_icc :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      RealField (c 0) → DivFree (c 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Icc (0:ℝ) T,
        en (c t) ≤ en (c 0) ∧ ens (c t) ≤ ens (c 0) ∧
          κ * en (c t) * ens (c t) < ν ^ 4 := by
  obtain ⟨κ, hκ, htrap⟩ := ns_galerkin_trap_zero_data_on
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 hSsym c hsupp h0real h0div hODE h0
  have hIco := htrap hν hS0 hSsym hsupp h0real h0div hODE h0
  -- nonnegativity of the tsum quantities
  have hen_nn : ∀ s : ℝ, 0 ≤ en (c s) := fun s =>
    tsum_nonneg fun k => sq_nonneg _
  have hens_nn : ∀ s : ℝ, 0 ≤ ens (c s) := fun s =>
    tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  -- descent bounds on the closed window
  have hdescent : ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en (c 0) ∧ ens (c t) ≤ ens (c 0) := by
    intro t ht
    by_cases htT : t < T
    · exact ⟨(hIco t ⟨ht.1, htT⟩).2.2, (hIco t ⟨ht.1, htT⟩).2.1⟩
    · -- t = T (the endpoint); T > 0 or the window is degenerate
      have htT' : T = t := (le_antisymm ht.2 (not_lt.mp htT)).symm
      subst htT'
      by_cases hT0 : 0 < T
      · -- continuity limit from the open side
        -- finite-sum surrogates are continuous on the window
        have hmode : ∀ k, ContinuousOn (fun s : ℝ => c s k) (Icc 0 T) :=
          fun k s hs => (hODE s hs k).continuousAt.continuousWithinAt
        have hEfc : ContinuousOn (fun s : ℝ => ∑ k ∈ S, ‖c s k‖ ^ 2) (Icc 0 T) := by
          refine continuousOn_finsetSum S fun k _ => ?_
          exact ((hmode k).norm).pow 2
        have hZfc : ContinuousOn
            (fun s : ℝ => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) (Icc 0 T) := by
          refine continuousOn_finsetSum S fun k _ => ?_
          exact continuousOn_const.mul (((hmode k).norm).pow 2)
        have hagreeE : ∀ s ∈ Icc (0:ℝ) T,
            en (c s) = ∑ k ∈ S, ‖c s k‖ ^ 2 := by
          intro s hs
          have h := ep_tsum_eq_sum (fun _ => (1:ℝ)) (hsupp s hs)
          simpa [en] using h
        have hagreeZ : ∀ s ∈ Icc (0:ℝ) T,
            ens (c s) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 := fun s hs =>
          ep_tsum_eq_sum _ (hsupp s hs)
        -- the filter 𝓝[Ico 0 T] T is nontrivial
        have hTmem : T ∈ closure (Ico (0:ℝ) T) := by
          rw [closure_Ico (ne_of_lt hT0)]
          exact ⟨hT0.le, le_refl T⟩
        have hne : (nhdsWithin T (Ico (0:ℝ) T)).NeBot :=
          mem_closure_iff_nhdsWithin_neBot.mp hTmem
        constructor
        · -- en (c T) ≤ en (c 0) via the limit
          have htend : Filter.Tendsto (fun s => ∑ k ∈ S, ‖c s k‖ ^ 2)
              (nhdsWithin T (Ico (0:ℝ) T)) (nhds (∑ k ∈ S, ‖c T k‖ ^ 2)) := by
            have h1 := (hEfc T ⟨hT0.le, le_refl T⟩).tendsto
            exact h1.mono_left (nhdsWithin_mono T Ico_subset_Icc_self)
          have hev : ∀ᶠ s in nhdsWithin T (Ico (0:ℝ) T),
              (∑ k ∈ S, ‖c s k‖ ^ 2) ≤ en (c 0) := by
            refine Filter.eventually_iff_exists_mem.mpr
              ⟨Ico (0:ℝ) T, self_mem_nhdsWithin, fun s hs => ?_⟩
            rw [← hagreeE s (Ico_subset_Icc_self hs)]
            exact (hIco s hs).2.2
          have hlim := le_of_tendsto htend hev
          rw [hagreeE T ⟨hT0.le, le_refl T⟩]
          exact hlim
        · have htend : Filter.Tendsto
              (fun s => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2)
              (nhdsWithin T (Ico (0:ℝ) T))
              (nhds (∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c T k‖ ^ 2)) := by
            have h1 := (hZfc T ⟨hT0.le, le_refl T⟩).tendsto
            exact h1.mono_left (nhdsWithin_mono T Ico_subset_Icc_self)
          have hev : ∀ᶠ s in nhdsWithin T (Ico (0:ℝ) T),
              (∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) ≤ ens (c 0) := by
            refine Filter.eventually_iff_exists_mem.mpr
              ⟨Ico (0:ℝ) T, self_mem_nhdsWithin, fun s hs => ?_⟩
            rw [← hagreeZ s (Ico_subset_Icc_self hs)]
            exact (hIco s hs).2.1
          have hlim := le_of_tendsto htend hev
          rw [hagreeZ T ⟨hT0.le, le_refl T⟩]
          exact hlim
      · -- T = 0: the endpoint IS the initial time
        have hT0' : T = 0 := le_antisymm (not_lt.mp hT0) ht.1
        subst hT0'
        exact ⟨le_refl _, le_refl _⟩
  intro t ht
  obtain ⟨hE, hZ⟩ := hdescent t ht
  refine ⟨hE, hZ, ?_⟩
  have h1 : κ * en (c t) * ens (c t) ≤ κ * en (c 0) * ens (c t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hκ.le) (hens_nn t)
  have h2 : κ * en (c 0) * ens (c t) ≤ κ * en (c 0) * ens (c 0) :=
    mul_le_mul_of_nonneg_left hZ (mul_nonneg hκ.le (hen_nn 0))
  linarith

/-- **GRAND CAPSTONE — global well-posedness of the trapped Galerkin
Navier-Stokes system.** There is a universal constant `κ > 0` such that for
every viscosity `ν > 0`, every symmetric zero-free box `S`, and every real,
divergence-free initial datum `c₀` supported on the box and satisfying the
smallness condition `κ · E₀ · Z₀ < ν⁴`: on EVERY horizon `[0, T]` a
coefficient flow exists solving the Galerkin Navier-Stokes ODE, it stays
trapped (energy and enstrophy descend, strict smallness propagates), and it
is the UNIQUE such flow. Existence is by seam-gluing induction on
uniform-step local solutions; the trap powers the induction by re-securing
the uniform coefficient bound at every seam. -/
theorem ns_galerkin_global_wellposed :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel}, (∀ k, k ∉ S → c₀ k = 0) →
      RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ T : ℝ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        (∀ c' : ℝ → (Fin 3 → ℤ) → Vel, (∀ (t : ℝ) k, k ∉ S → c' t k = 0) →
          (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c' s k)
            ((-(ν * ‖freq k‖ ^ 2)) • c' t k + lerayProj k (convGal S (c' t) k)) t) →
          c' 0 = c₀ → ∀ t ∈ Icc (0:ℝ) T, ∀ k, c' t k = c t k) := by
  obtain ⟨κ, hκ, htrap⟩ := ns_galerkin_trap_zero_data_icc
  refine ⟨κ, hκ, ?_⟩
  intro ν hν S hS0 hSsym c₀ hsupp₀ hreal₀ hdiv₀ h0 T
  set B := Real.sqrt (en c₀) with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  obtain ⟨ε, hε, hloc⟩ := ns_galerkin_local_existence hν S B hB0
  -- the inductive construction: a flow with the ODE on [0, n·(ε/2)]
  have key : ∀ n : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = c₀ ∧ (∀ (t : ℝ) k, k ∉ S → c t k = 0) ∧
      ∀ t ∈ Icc (0:ℝ) ((n : ℝ) * (ε / 2)), ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t := by
    intro n
    induction n with
    | zero =>
      obtain ⟨c, hc0, hcs, hcODE⟩ := hloc hsupp₀ (coeff_le_sqrt_en hsupp₀) 0
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
      -- trap on the achieved window gives the seam bound
      have htrapn := htrap hν hS0 hSsym (fun t ht k hk => hcs t k hk)
        (hc0 ▸ hreal₀) (hc0 ▸ hdiv₀) hcODE (by rw [hc0]; exact h0)
      have henTn : en (c Tn) ≤ en c₀ := by
        have := (htrapn Tn ⟨hTn0, le_refl Tn⟩).1
        rwa [hc0] at this
      have hbTn : ∀ k, ‖c Tn k‖ ≤ B := fun k =>
        (coeff_le_sqrt_en (fun j hj => hcs Tn j hj) k).trans
          (Real.sqrt_le_sqrt henTn)
      -- local solve centered at the seam
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
        -- overlap agreement via the shifted flows
        have hagree : ∀ s ∈ Icc (-(ε/2)) (0:ℝ), ∀ k, c (Tn + s) k = d (Tn + s) k := by
          have h1 := ns_galerkin_unique_around (ν := ν) (a := -(ε/2)) (b := 0) hν.le
            (by linarith) (le_refl 0)
            (c₁ := fun s => c (Tn + s)) (c₂ := fun s => d (Tn + s))
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
            exact coeff_shift (hcODE (Tn + s) hmem' k)
          · intro s hs k
            have hmem : Tn + s ∈ Ioo (Tn - ε) (Tn + ε) := by
              constructor
              · linarith [hs.1, hε]
              · linarith [hs.2, hε]
            exact coeff_shift (hdODE (Tn + s) hmem k)
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
                lerayProj k (convGal S (if t ≤ Tn then c t else d t) k)) t
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
                lerayProj k (convGal S (if t ≤ Tn then c t else d t) k)) t
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
                lerayProj k (convGal S (if t ≤ Tn then c t else d t) k)) t
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
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t :=
      fun t ht k => hcODE t ⟨ht.1, ht.2.trans hTm⟩ k
    have htrapT := htrap hν hS0 hSsym (fun t ht k hk => hcs t k hk)
      (hc0 ▸ hreal₀) (hc0 ▸ hdiv₀) hODET (by rw [hc0]; exact h0)
    refine ⟨c, hc0, hcs, hODET, ?_, ?_⟩
    · intro t ht
      have h := htrapT t ht
      rwa [hc0] at h
    · intro c' hcs' hODE' hc0'
      have hmatch : ∀ k, c' 0 k = c 0 k := fun k => by rw [hc0', hc0]
      exact fun t ht k => ns_galerkin_unique_around hν.le (le_refl 0) hT hcs'
        (fun t k hk => hcs t k hk) hODE' hODET hmatch t ht k
  · refine ⟨fun _ => c₀, rfl, fun t k hk => hsupp₀ k hk, ?_, ?_, ?_⟩
    · intro t ht
      exact absurd (ht.1.trans ht.2) hT
    · intro t ht
      exact absurd (ht.1.trans ht.2) hT
    · intro c' _ _ _ t ht
      exact absurd (ht.1.trans ht.2) hT

end TheoremB