/-
# Defect calculus (Tier 4, wave U3)

Two-field convection majorants, defect summability, the convection
difference telescope, the Leray pairing drop on divergence-free modes, and
the finite-section energy derivative.
-/
import TheoremB.TheoremBGlobal

namespace TheoremB

open Set

/-! ### Mixed (two-field) Cauchy-Schwarz majorants -/

/-- Two-field generalization of `summable_convMaj`: `u` in the ℓ² slot, the
shifted `v`-family in the weighted slot. -/
theorem mixed_summable_convMaj {u v : (Fin 3 → ℤ) → Vel}
    (hEu : Summable fun l => ‖u l‖ ^ 2)
    (hZv : Summable fun l => ‖freq l‖ ^ 2 * ‖v l‖ ^ 2) (k : Fin 3 → ℤ) :
    Summable fun l => ‖u l‖ * (‖freq (k - l)‖ * ‖v (k - l)‖) := by
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hf2 : Summable fun l => ‖u l‖ ^ (2 : ℝ) := hEu.congr fun l => h2 _
  have hZk : Summable fun l => ‖freq (k - l)‖ ^ 2 * ‖v (k - l)‖ ^ 2 := by
    have h := ((Equiv.subLeft k).summable_iff
      (f := fun m => ‖freq m‖ ^ 2 * ‖v m‖ ^ 2)).mpr hZv
    exact h.congr fun l => by simp [Function.comp]
  have hg2 : Summable fun l => (‖freq (k - l)‖ * ‖v (k - l)‖) ^ (2 : ℝ) :=
    hZk.congr fun l => by rw [← h2]; ring
  exact Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun l => norm_nonneg _) (fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hf2 hg2

/-- Two-field generalization of `convMaj_le`:
`∑' l, ‖u l‖·‖freq (k−l)‖·‖v (k−l)‖ ≤ √(en u)·√(ens v)`. -/
theorem mixed_convMaj_le {u v : (Fin 3 → ℤ) → Vel}
    (hEu : Summable fun l => ‖u l‖ ^ 2)
    (hZv : Summable fun l => ‖freq l‖ ^ 2 * ‖v l‖ ^ 2) (k : Fin 3 → ℤ) :
    (∑' l, ‖u l‖ * (‖freq (k - l)‖ * ‖v (k - l)‖)) ≤
      Real.sqrt (en u) * Real.sqrt (ens v) := by
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hf2 : Summable fun l => ‖u l‖ ^ (2 : ℝ) := hEu.congr fun l => h2 _
  have hZk : Summable fun l => ‖freq (k - l)‖ ^ 2 * ‖v (k - l)‖ ^ 2 := by
    have h := ((Equiv.subLeft k).summable_iff
      (f := fun m => ‖freq m‖ ^ 2 * ‖v m‖ ^ 2)).mpr hZv
    exact h.congr fun l => by simp [Function.comp]
  have hg2 : Summable fun l => (‖freq (k - l)‖ * ‖v (k - l)‖) ^ (2 : ℝ) :=
    hZk.congr fun l => by rw [← h2]; ring
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun l => ‖u l‖) (g := fun l => ‖freq (k - l)‖ * ‖v (k - l)‖)
    (fun l => norm_nonneg _) (fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hf2 hg2
  have rf : (∑' l, ‖u l‖ ^ (2 : ℝ)) = en u := tsum_congr fun l => (h2 _).symm
  have rg : (∑' l, (‖freq (k - l)‖ * ‖v (k - l)‖) ^ (2 : ℝ)) = ens v := by
    have e1 : (∑' l, (‖freq (k - l)‖ * ‖v (k - l)‖) ^ (2 : ℝ)) =
        ∑' l, ‖freq (k - l)‖ ^ 2 * ‖v (k - l)‖ ^ 2 :=
      tsum_congr fun l => by rw [← h2]; ring
    have hens : (∑' m : Fin 3 → ℤ, ‖freq m‖ ^ 2 * ‖v m‖ ^ 2) = ens v := rfl
    rw [e1, ← hens]
    have h := (Equiv.subLeft k).tsum_eq (f := fun m => ‖freq m‖ ^ 2 * ‖v m‖ ^ 2)
    simp only [Equiv.subLeft_apply] at h
    exact h
  rw [rf, rg] at cs
  calc (∑' l, ‖u l‖ * (‖freq (k - l)‖ * ‖v (k - l)‖))
      ≤ en u ^ (1 / (2:ℝ)) * ens v ^ (1 / (2:ℝ)) := cs
    _ = Real.sqrt (en u) * Real.sqrt (ens v) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-! ### Summability of differences -/

/-- ℓ² summability survives differences: `‖a−b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem summable_sq_sub {a b : (Fin 3 → ℤ) → Vel}
    (hEa : Summable fun l => ‖a l‖ ^ 2) (hEb : Summable fun l => ‖b l‖ ^ 2) :
    Summable fun l => ‖a l - b l‖ ^ 2 := by
  have hmaj : Summable fun l => 2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2 :=
    (hEa.mul_left 2).add (hEb.mul_left 2)
  refine hmaj.of_nonneg_of_le (fun l => sq_nonneg _) fun l => ?_
  have htri : ‖a l - b l‖ ≤ ‖a l‖ + ‖b l‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (a l - b l), norm_nonneg (a l), norm_nonneg (b l),
    sq_nonneg (‖a l‖ - ‖b l‖)]

/-- Weighted ℓ² summability survives differences. -/
theorem summable_wsq_sub {a b : (Fin 3 → ℤ) → Vel}
    (hZa : Summable fun l => ‖freq l‖ ^ 2 * ‖a l‖ ^ 2)
    (hZb : Summable fun l => ‖freq l‖ ^ 2 * ‖b l‖ ^ 2) :
    Summable fun l => ‖freq l‖ ^ 2 * ‖a l - b l‖ ^ 2 := by
  have hmaj : Summable fun l =>
      2 * (‖freq l‖ ^ 2 * ‖a l‖ ^ 2) + 2 * (‖freq l‖ ^ 2 * ‖b l‖ ^ 2) :=
    (hZa.mul_left 2).add (hZb.mul_left 2)
  refine hmaj.of_nonneg_of_le (fun l => by positivity) fun l => ?_
  have htri : ‖a l - b l‖ ≤ ‖a l‖ + ‖b l‖ := norm_sub_le _ _
  have hsq : ‖a l - b l‖ ^ 2 ≤ 2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2 := by
    nlinarith [norm_nonneg (a l - b l), norm_nonneg (a l), norm_nonneg (b l),
      sq_nonneg (‖a l‖ - ‖b l‖)]
  nlinarith [sq_nonneg ‖freq l‖]

/-! ### The convection defect telescope -/

/-- Term-norm Cauchy-Schwarz bound, mixed-field form. -/
private lemma b3_term_norm_le (x y : (Fin 3 → ℤ) → Vel) (k l : Fin 3 → ℤ) :
    ‖(Complex.I * dotR (x l) (freq (k - l))) • y (k - l)‖ ≤
      ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖) := by
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotR (x l) (freq (k - l))‖ * ‖y (k - l)‖
      ≤ (‖freq (k - l)‖ * ‖x l‖) * ‖y (k - l)‖ :=
        mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
    _ = ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖) := by ring

/-- A convection term-family is (vector) summable once its CS majorant is. -/
private lemma b3_summable_term {x y : (Fin 3 → ℤ) → Vel} {k : Fin 3 → ℤ}
    (hmaj : Summable fun l => ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖)) :
    Summable fun l => (Complex.I * dotR (x l) (freq (k - l))) • y (k - l) := by
  have hn : Summable fun l =>
      ‖(Complex.I * dotR (x l) (freq (k - l))) • y (k - l)‖ :=
    hmaj.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => b3_term_norm_le x y k l)
  exact hn.of_norm

/-- The convection defect splits into the two mixed telescoping pieces. -/
theorem convFull_sub {a b : (Fin 3 → ℤ) → Vel}
    (hEa : Summable fun l => ‖a l‖ ^ 2) (hZa : Summable fun l => ‖freq l‖ ^ 2 * ‖a l‖ ^ 2)
    (hEb : Summable fun l => ‖b l‖ ^ 2) (hZb : Summable fun l => ‖freq l‖ ^ 2 * ‖b l‖ ^ 2)
    (k : Fin 3 → ℤ) :
    convFull a k - convFull b k =
      (-(∑' l, (Complex.I * dotR (a l - b l) (freq (k - l))) • a (k - l))) +
      (-(∑' l, (Complex.I * dotR (b l) (freq (k - l))) • (a (k - l) - b (k - l)))) := by
  have hta : Summable fun l => (Complex.I * dotR (a l) (freq (k - l))) • a (k - l) :=
    b3_summable_term (summable_convMaj hEa hZa k)
  have htb : Summable fun l => (Complex.I * dotR (b l) (freq (k - l))) • b (k - l) :=
    b3_summable_term (summable_convMaj hEb hZb k)
  have hr1 : Summable fun l =>
      (Complex.I * dotR (a l - b l) (freq (k - l))) • a (k - l) :=
    b3_summable_term (x := fun l => a l - b l) (y := a)
      (mixed_summable_convMaj (summable_sq_sub hEa hEb) hZa k)
  have hr2 : Summable fun l =>
      (Complex.I * dotR (b l) (freq (k - l))) • (a (k - l) - b (k - l)) :=
    b3_summable_term (x := b) (y := fun l => a l - b l)
      (mixed_summable_convMaj hEb (summable_wsq_sub hZa hZb) k)
  have hterm : ∀ l : Fin 3 → ℤ,
      (Complex.I * dotR (a l) (freq (k - l))) • a (k - l) -
        (Complex.I * dotR (b l) (freq (k - l))) • b (k - l) =
      (Complex.I * dotR (a l - b l) (freq (k - l))) • a (k - l) +
        (Complex.I * dotR (b l) (freq (k - l))) • (a (k - l) - b (k - l)) := by
    intro l
    rw [dotR_sub_left', mul_sub, sub_smul, smul_sub]
    abel
  calc convFull a k - convFull b k
      = -((∑' l, (Complex.I * dotR (a l) (freq (k - l))) • a (k - l)) -
          (∑' l, (Complex.I * dotR (b l) (freq (k - l))) • b (k - l))) := by
        simp only [convFull]; abel
    _ = -(∑' l, ((Complex.I * dotR (a l) (freq (k - l))) • a (k - l) -
          (Complex.I * dotR (b l) (freq (k - l))) • b (k - l))) := by
        rw [hta.tsum_sub htb]
    _ = -(∑' l, ((Complex.I * dotR (a l - b l) (freq (k - l))) • a (k - l) +
          (Complex.I * dotR (b l) (freq (k - l))) • (a (k - l) - b (k - l)))) := by
        rw [tsum_congr hterm]
    _ = -((∑' l, (Complex.I * dotR (a l - b l) (freq (k - l))) • a (k - l)) +
          (∑' l, (Complex.I * dotR (b l) (freq (k - l))) • (a (k - l) - b (k - l)))) := by
        rw [hr1.tsum_add hr2]
    _ = (-(∑' l, (Complex.I * dotR (a l - b l) (freq (k - l))) • a (k - l))) +
          (-(∑' l, (Complex.I * dotR (b l) (freq (k - l))) • (a (k - l) - b (k - l)))) := by
        abel

/-! ### The Leray projection against a divergence-free vector -/

/-- Paired against any single divergence-free vector `v`, the Leray projection
of the left argument is invisible. -/
theorem inner_lerayProj_left {k : Fin 3 → ℤ} {v w : Vel}
    (hv : dotR v (freq k) = 0) :
    inner ℝ (lerayProj k w) v = inner ℝ w v := by
  have hker : inner ℂ (castCV (freq k)) v = 0 := by
    rw [← dotR_eq_inner]
    exact hv
  have hC : inner ℂ (lerayProj k w) v = inner ℂ w v := by
    rw [lerayProj, inner_sub_left, inner_smul_left, hker, mul_zero, sub_zero]
  have e1 : inner ℝ (lerayProj k w) v = (inner ℂ (lerayProj k w) v).re :=
    (real_inner_eq_re_inner ℂ _ _).trans RCLike.re_to_complex
  have e2 : inner ℝ w v = (inner ℂ w v).re :=
    (real_inner_eq_re_inner ℂ _ _).trans RCLike.re_to_complex
  rw [e1, e2, hC]

/-! ### Derivative of a finite energy sum -/

/-- Coefficient-wise product rule for a finite sum of squared norms, with the
derivative hypothesis needed only on the modes of `F`. -/
theorem hasDerivAt_finset_sum_sq {c : ℝ → (Fin 3 → ℤ) → Vel}
    {c' : (Fin 3 → ℤ) → Vel} {t : ℝ} (F : Finset (Fin 3 → ℤ))
    (h : ∀ k ∈ F, HasDerivAt (fun s => c s k) (c' k) t) :
    HasDerivAt (fun s => ∑ k ∈ F, ‖c s k‖ ^ 2)
      (∑ k ∈ F, 2 * inner ℝ (c t k) (c' k)) t := by
  have hterm : ∀ k ∈ F, HasDerivAt (fun s : ℝ => ‖c s k‖ ^ 2)
      (2 * inner ℝ (c t k) (c' k)) t := by
    intro k hk
    have h1 : HasDerivAt (fun s : ℝ => inner ℝ (c s k) (c s k))
        (inner ℝ (c t k) (c' k) + inner ℝ (c' k) (c t k)) t :=
      (h k hk).inner ℝ (h k hk)
    have h2 : (fun s : ℝ => ‖c s k‖ ^ 2) = fun s : ℝ => inner ℝ (c s k) (c s k) := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (c t k) (c' k) + inner ℝ (c' k) (c t k) =
        2 * inner ℝ (c t k) (c' k) := by
      rw [real_inner_comm (c' k) (c t k)]; ring
    rw [h2, ← h4]
    exact h1
  have hsum := HasDerivAt.sum hterm
  have heq : (∑ i ∈ F, fun s : ℝ => ‖c s i‖ ^ 2) =
      fun s : ℝ => ∑ k ∈ F, ‖c s k‖ ^ 2 := by
    funext s
    simp [Finset.sum_apply]
  rwa [heq] at hsum

end TheoremB
