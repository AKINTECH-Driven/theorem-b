/-
# The lattice kernel and the weighted interpolation (Tier 4, wave U1)

The convolution kernel at exponent 7/4 is summable with a shift-uniform
bound (the 3D window: 7/2 > 3), and the 7/4-weighted energy interpolates
between energy and enstrophy at exponents (1/8, 7/8).
-/
import TheoremB.TheoremBGlobal

namespace TheoremB

open Set

/-! ### BRAVO-1: lattice kernel + interpolation -/

/-- The lattice weight `‖k‖^(−7/2)` is summable over ℤ³ (`k = 0` contributes
`0 ^ (−7/2) = 0` by the rpow junk convention). -/
theorem summable_freq_rpow_neg :
    Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ (-(7:ℝ)/2) :=
  summable_norm_freq_rpow (by norm_num)

private lemma b1_norm_freq_zero : ‖freq (0 : Fin 3 → ℤ)‖ = 0 := by
  rw [norm_freq]
  simp

private lemma b1_inv_rpow_sq {y : ℝ} (hy : 0 < y) :
    (y ^ ((7:ℝ)/4))⁻¹ * (y ^ ((7:ℝ)/4))⁻¹ = y ^ (-(7:ℝ)/2) := by
  rw [← mul_inv, ← Real.rpow_add hy,
    show (7:ℝ)/4 + (7:ℝ)/4 = (7:ℝ)/2 by norm_num,
    ← Real.rpow_neg hy.le, neg_div]

/-- Pointwise kernel bound: the product of the two inverse `7/4`-powers is
dominated by the sum of the two `−7/2`-powers.  The degenerate lattice
points `k = 0` and `k = m` vanish via the junk conventions. -/
private lemma b1_kernel_pointwise (m k : Fin 3 → ℤ) :
    (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ ≤
      ‖freq k‖ ^ (-(7:ℝ)/2) + ‖freq (k - m)‖ ^ (-(7:ℝ)/2) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [b1_norm_freq_zero, Real.zero_rpow (by norm_num : ((7:ℝ)/4) ≠ 0),
      inv_zero, zero_mul]
    positivity
  rcases eq_or_ne (k - m) 0 with hkm | hkm
  · rw [hkm, b1_norm_freq_zero, Real.zero_rpow (by norm_num : ((7:ℝ)/4) ≠ 0),
      inv_zero, mul_zero]
    positivity
  · have ha1 : (1:ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    have hb1 : (1:ℝ) ≤ ‖freq (k - m)‖ := one_le_norm_freq hkm
    have ha0 : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos ha1
    have hb0 : (0:ℝ) < ‖freq (k - m)‖ := lt_of_lt_of_le one_pos hb1
    rcases le_total ‖freq k‖ ‖freq (k - m)‖ with hab | hab
    · have h1 : ‖freq k‖ ^ ((7:ℝ)/4) ≤ ‖freq (k - m)‖ ^ ((7:ℝ)/4) :=
        Real.rpow_le_rpow ha0.le hab (by norm_num)
      have h2 : (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ ≤ (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos ha0 _) h1
      calc (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹
          ≤ (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = ‖freq k‖ ^ (-(7:ℝ)/2) := b1_inv_rpow_sq ha0
        _ ≤ ‖freq k‖ ^ (-(7:ℝ)/2) + ‖freq (k - m)‖ ^ (-(7:ℝ)/2) :=
            le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)
    · have h1 : ‖freq (k - m)‖ ^ ((7:ℝ)/4) ≤ ‖freq k‖ ^ ((7:ℝ)/4) :=
        Real.rpow_le_rpow hb0.le hab (by norm_num)
      have h2 : (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ ≤ (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hb0 _) h1
      calc (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹
          ≤ (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖freq (k - m)‖ ^ (-(7:ℝ)/2) := b1_inv_rpow_sq hb0
        _ ≤ ‖freq k‖ ^ (-(7:ℝ)/2) + ‖freq (k - m)‖ ^ (-(7:ℝ)/2) :=
            le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- **Kernel bound.**  The convolution kernel
`k ↦ (‖k‖^(7/4))⁻¹ · (‖k−m‖^(7/4))⁻¹` is summable, with a bound uniform in
the shift `m`. -/
theorem kernel_sum_le : ∃ C_K : ℝ, 0 < C_K ∧
    (∀ m : Fin 3 → ℤ, Summable fun k : Fin 3 → ℤ =>
      (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) ∧
    ∀ m : Fin 3 → ℤ,
      (∑' k : Fin 3 → ℤ, (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) ≤ C_K := by
  have hSnn : (0:ℝ) ≤ ∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2) :=
    tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _
  have hshiftSum : ∀ m : Fin 3 → ℤ,
      Summable fun k : Fin 3 → ℤ => ‖freq (k - m)‖ ^ (-(7:ℝ)/2) := by
    intro m
    have h := ((Equiv.subRight m).summable_iff
      (f := fun j : Fin 3 → ℤ => ‖freq j‖ ^ (-(7:ℝ)/2))).mpr summable_freq_rpow_neg
    exact h.congr fun k => by simp [Function.comp]
  have hshiftTsum : ∀ m : Fin 3 → ℤ,
      (∑' k : Fin 3 → ℤ, ‖freq (k - m)‖ ^ (-(7:ℝ)/2))
        = ∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2) := by
    intro m
    have h := (Equiv.subRight m).tsum_eq (f := fun j : Fin 3 → ℤ => ‖freq j‖ ^ (-(7:ℝ)/2))
    simp only [Equiv.subRight_apply] at h
    exact h
  have hbound : ∀ m : Fin 3 → ℤ, Summable fun k : Fin 3 → ℤ =>
      ‖freq k‖ ^ (-(7:ℝ)/2) + ‖freq (k - m)‖ ^ (-(7:ℝ)/2) :=
    fun m => summable_freq_rpow_neg.add (hshiftSum m)
  have hprod : ∀ m : Fin 3 → ℤ, Summable fun k : Fin 3 → ℤ =>
      (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ :=
    fun m => (hbound m).of_nonneg_of_le (fun k => by positivity)
      (fun k => b1_kernel_pointwise m k)
  refine ⟨2 * (∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2)) + 1, by linarith, hprod, ?_⟩
  intro m
  calc (∑' k : Fin 3 → ℤ, (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹)
      ≤ ∑' k : Fin 3 → ℤ, (‖freq k‖ ^ (-(7:ℝ)/2) + ‖freq (k - m)‖ ^ (-(7:ℝ)/2)) :=
        (hprod m).tsum_le_tsum (fun k => b1_kernel_pointwise m k) (hbound m)
    _ = (∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2))
        + ∑' k : Fin 3 → ℤ, ‖freq (k - m)‖ ^ (-(7:ℝ)/2) :=
        summable_freq_rpow_neg.tsum_add (hshiftSum m)
    _ = (∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2))
        + ∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2) := by rw [hshiftTsum m]
    _ ≤ 2 * (∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (-(7:ℝ)/2)) + 1 := by linarith

private lemma b1_rpow_inv8 (t : ℝ) (ht : 0 ≤ t) : (t ^ ((1:ℝ)/8)) ^ (8:ℝ) = t := by
  rw [← Real.rpow_mul ht]
  norm_num

private lemma b1_rpow_inv87 (t : ℝ) (ht : 0 ≤ t) : (t ^ ((7:ℝ)/8)) ^ ((8:ℝ)/7) = t := by
  rw [← Real.rpow_mul ht]
  norm_num

/-- Hölder splitting of the interpolation summand:
`B^(1/8) · (A²B)^(7/8) = A^(7/4) · B` for nonnegative `A, B`. -/
private lemma b1_split {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    B ^ ((1:ℝ)/8) * (A ^ 2 * B) ^ ((7:ℝ)/8) = A ^ ((7:ℝ)/4) * B := by
  have h1 : (A ^ 2 * B) ^ ((7:ℝ)/8) = A ^ ((7:ℝ)/4) * B ^ ((7:ℝ)/8) := by
    rw [Real.mul_rpow (sq_nonneg A) hB]
    congr 1
    rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hA]
    norm_num
  have h2 : B ^ ((1:ℝ)/8) * B ^ ((7:ℝ)/8) = B := by
    rw [← Real.rpow_add' hB (by norm_num : (1:ℝ)/8 + (7:ℝ)/8 ≠ 0),
      show (1:ℝ)/8 + (7:ℝ)/8 = 1 by norm_num, Real.rpow_one]
  rw [h1, ← mul_assoc, mul_comm (B ^ ((1:ℝ)/8)) (A ^ ((7:ℝ)/4)), mul_assoc, h2]

/-- **Weighted interpolation** (Hölder at exponents `(8, 8/7)`):
`Σ ‖k‖^(7/4) x²  ≤  (Σ x²)^(1/8) · (Σ ‖k‖² x²)^(7/8)`. -/
theorem weighted_interp {x : (Fin 3 → ℤ) → ℝ} (hx : ∀ k, 0 ≤ x k)
    (hE : Summable fun k => x k ^ 2)
    (hZ : Summable fun k => ‖freq k‖ ^ 2 * x k ^ 2) :
    (Summable fun k => ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) ∧
    (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) ≤
      (∑' k, x k ^ 2) ^ ((1:ℝ)/8) * (∑' k, ‖freq k‖ ^ 2 * x k ^ 2) ^ ((7:ℝ)/8) := by
  -- summability, by crude pointwise domination
  have hdom : ∀ k, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2
      ≤ x k ^ 2 + ‖freq k‖ ^ 2 * x k ^ 2 := by
    intro k
    have hxk : (0:ℝ) ≤ x k ^ 2 := sq_nonneg _
    have hw : (0:ℝ) ≤ ‖freq k‖ := norm_nonneg _
    rcases le_total ‖freq k‖ 1 with h1 | h1
    · have h2 : ‖freq k‖ ^ ((7:ℝ)/4) ≤ 1 := Real.rpow_le_one hw h1 (by norm_num)
      have h3 : ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2 ≤ 1 * x k ^ 2 :=
        mul_le_mul_of_nonneg_right h2 hxk
      have h4 : (0:ℝ) ≤ ‖freq k‖ ^ 2 * x k ^ 2 := mul_nonneg (sq_nonneg _) hxk
      linarith
    · have h2 : ‖freq k‖ ^ ((7:ℝ)/4) ≤ ‖freq k‖ ^ (2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      have h2' : ‖freq k‖ ^ (2:ℝ) = ‖freq k‖ ^ 2 := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      have h3 : ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2 ≤ ‖freq k‖ ^ 2 * x k ^ 2 :=
        mul_le_mul_of_nonneg_right (h2.trans_eq h2') hxk
      linarith
  have hsum : Summable fun k => ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2 :=
    (hE.add hZ).of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)) hdom
  -- Hölder at (8, 8/7)
  have hpq : Real.HolderConjugate 8 (8/7) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf8 : Summable fun k => ((x k ^ 2) ^ ((1:ℝ)/8)) ^ (8:ℝ) :=
    hE.congr fun k => (b1_rpow_inv8 _ (sq_nonneg _)).symm
  have hg87 : Summable fun k => ((‖freq k‖ ^ 2 * x k ^ 2) ^ ((7:ℝ)/8)) ^ ((8:ℝ)/7) :=
    hZ.congr fun k => (b1_rpow_inv87 _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
    (f := fun k => (x k ^ 2) ^ ((1:ℝ)/8))
    (g := fun k => (‖freq k‖ ^ 2 * x k ^ 2) ^ ((7:ℝ)/8))
    (fun k => Real.rpow_nonneg (sq_nonneg _) _)
    (fun k => Real.rpow_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) _)
    hf8 hg87
  have hkey : (∑' k, ((x k ^ 2) ^ ((1:ℝ)/8)) * ((‖freq k‖ ^ 2 * x k ^ 2) ^ ((7:ℝ)/8)))
      = ∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2 :=
    tsum_congr fun k => b1_split (norm_nonneg _) (sq_nonneg _)
  have hfeq : (∑' k, ((x k ^ 2) ^ ((1:ℝ)/8)) ^ (8:ℝ)) = ∑' k, x k ^ 2 :=
    tsum_congr fun k => b1_rpow_inv8 _ (sq_nonneg _)
  have hgeq : (∑' k, ((‖freq k‖ ^ 2 * x k ^ 2) ^ ((7:ℝ)/8)) ^ ((8:ℝ)/7))
      = ∑' k, ‖freq k‖ ^ 2 * x k ^ 2 :=
    tsum_congr fun k => b1_rpow_inv87 _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hkey, hfeq, hgeq, show (1:ℝ)/(8/7) = (7:ℝ)/8 by norm_num] at cs
  exact ⟨hsum, cs⟩

end TheoremB
