/-
# The absorbed pairing bound (Tier 4, wave U2)

The correlation-square bound through the 7/4-kernel and the fully absorbed
defect pairing: `2|pairing| <= nu*ens(d) + K*en(d)` with `K` explicit in
`(nu, E, Z)` and no box anywhere.
-/
import TheoremB.LatticeKernel
import TheoremB.DefectCalculus

namespace TheoremB

open Set

/-! ### BRAVO-2 private helpers -/

private lemma b2_sq_rpow (t : ℝ) : t ^ 2 = t ^ (2:ℝ) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

private lemma b2_Xsq (x : (Fin 3 → ℤ) → ℝ) (j : Fin 3 → ℤ) :
    (‖freq j‖ ^ ((7:ℝ)/8) * x j) ^ 2 = ‖freq j‖ ^ ((7:ℝ)/4) * x j ^ 2 := by
  have h : (‖freq j‖ ^ ((7:ℝ)/8)) ^ 2 = ‖freq j‖ ^ ((7:ℝ)/4) := by
    rw [b2_sq_rpow, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [mul_pow, h]

private lemma b2_cancel {t : ℝ} (ht : 0 < t) (u : ℝ) :
    Real.sqrt ((t ^ ((7:ℝ)/4))⁻¹) * (t ^ ((7:ℝ)/8) * u) = u := by
  rw [← Real.rpow_neg ht.le, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, ← mul_assoc,
    ← Real.rpow_add ht, show -((7:ℝ)/4) * (1/2) + (7:ℝ)/8 = 0 by norm_num,
    Real.rpow_zero, one_mul]

/-- Pointwise kernel factorization: `x k · y (k−m) = √(w k · w (k−m)) · (X k · Y (k−m))`. -/
private lemma b2_pointwise {x y : (Fin 3 → ℤ) → ℝ} (hx0 : x 0 = 0) (hy0 : y 0 = 0)
    (m k : Fin 3 → ℤ) :
    x k * y (k - m) =
      Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) *
        ((‖freq k‖ ^ ((7:ℝ)/8) * x k) * (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m))) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [hx0]; ring
  rcases eq_or_ne (k - m) 0 with hkm | hkm
  · rw [hkm, hy0]; ring
  · have ha0 : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have hb0 : (0:ℝ) < ‖freq (k - m)‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hkm)
    rw [Real.sqrt_mul (by positivity)]
    calc x k * y (k - m)
        = (Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹) * (‖freq k‖ ^ ((7:ℝ)/8) * x k)) *
          (Real.sqrt ((‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) *
            (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m))) := by
          rw [b2_cancel ha0, b2_cancel hb0]
      _ = _ := by ring

/-- **L4, the correlation-square bound.** -/
theorem conv_corr_sq_le {x y : (Fin 3 → ℤ) → ℝ} (hx : ∀ k, 0 ≤ x k) (hy : ∀ k, 0 ≤ y k)
    (hx0 : x 0 = 0) (hy0 : y 0 = 0)
    (hxE : Summable fun k => x k ^ 2) (hxZ : Summable fun k => ‖freq k‖ ^ 2 * x k ^ 2)
    (hyE : Summable fun k => y k ^ 2) (hyZ : Summable fun k => ‖freq k‖ ^ 2 * y k ^ 2)
    (C_K : ℝ) (hCK : 0 < C_K)
    (hker : (∀ m : Fin 3 → ℤ, Summable fun k : Fin 3 → ℤ =>
      (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) ∧
      ∀ m : Fin 3 → ℤ, (∑' k : Fin 3 → ℤ,
        (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) ≤ C_K)
    (F : Finset (Fin 3 → ℤ)) :
    (Summable fun m => (∑ k ∈ F, x k * y (k - m)) ^ 2) ∧
    (∑' m, (∑ k ∈ F, x k * y (k - m)) ^ 2) ≤
      C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * y k ^ 2) := by
  obtain ⟨hkerS, hkerB⟩ := hker
  obtain ⟨hPxS, hPxB⟩ := weighted_interp hx hxE hxZ
  obtain ⟨hPyS, hPyB⟩ := weighted_interp hy hyE hyZ
  -- Step 1: the per-shift Cauchy–Schwarz bound
  have hstep : ∀ m : Fin 3 → ℤ, (∑ k ∈ F, x k * y (k - m)) ^ 2 ≤
      C_K * ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
        (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) := by
    intro m
    have hrw : (∑ k ∈ F, x k * y (k - m)) = ∑ k ∈ F,
        Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) *
          ((‖freq k‖ ^ ((7:ℝ)/8) * x k) * (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m))) :=
      Finset.sum_congr rfl fun k _ => b2_pointwise hx0 hy0 m k
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq F
      (fun k => Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹))
      (fun k => (‖freq k‖ ^ ((7:ℝ)/8) * x k) * (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m)))
    have hsqrw : (∑ k ∈ F,
        (Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹)) ^ 2)
        = ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹ :=
      Finset.sum_congr rfl fun k _ => Real.sq_sqrt (by positivity)
    have hXYrw : (∑ k ∈ F,
        ((‖freq k‖ ^ ((7:ℝ)/8) * x k) * (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m))) ^ 2)
        = ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
            (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) :=
      Finset.sum_congr rfl fun k _ => by rw [mul_pow, b2_Xsq x k, b2_Xsq y (k - m)]
    have hkersum : (∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) ≤ C_K :=
      le_trans ((hkerS m).sum_le_tsum F (fun k _ => by positivity)) (hkerB m)
    calc (∑ k ∈ F, x k * y (k - m)) ^ 2
        = (∑ k ∈ F,
            Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) *
              ((‖freq k‖ ^ ((7:ℝ)/8) * x k) * (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m)))) ^ 2 := by
          rw [hrw]
      _ ≤ (∑ k ∈ F,
            (Real.sqrt ((‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹)) ^ 2) *
          (∑ k ∈ F,
            ((‖freq k‖ ^ ((7:ℝ)/8) * x k) * (‖freq (k - m)‖ ^ ((7:ℝ)/8) * y (k - m))) ^ 2) := hcs
      _ = (∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4))⁻¹ * (‖freq (k - m)‖ ^ ((7:ℝ)/4))⁻¹) *
          (∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
            (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2)) := by
          rw [hsqrw, hXYrw]
      _ ≤ C_K * ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
            (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) :=
          mul_le_mul_of_nonneg_right hkersum (Finset.sum_nonneg fun k _ => by positivity)
  -- Step 2: summability of the majorant in the shift variable
  have hshift : ∀ k : Fin 3 → ℤ,
      Summable fun m => ‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2 := by
    intro k
    have h := ((Equiv.subLeft k).summable_iff
      (f := fun j => ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2)).mpr hPyS
    exact h.congr fun m => by simp [Function.comp]
  have hshiftT : ∀ k : Fin 3 → ℤ,
      (∑' m, ‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2)
        = ∑' j, ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2 := by
    intro k
    have h := (Equiv.subLeft k).tsum_eq (f := fun j => ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2)
    simp only [Equiv.subLeft_apply] at h
    exact h
  have hinner : ∀ k ∈ F, Summable fun m => (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
      (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) :=
    fun k _ => (hshift k).mul_left _
  have hmajS : Summable fun m => C_K * ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
      (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) :=
    (summable_sum hinner).mul_left _
  have hsummable : Summable fun m => (∑ k ∈ F, x k * y (k - m)) ^ 2 :=
    hmajS.of_nonneg_of_le (fun m => sq_nonneg _) hstep
  refine ⟨hsummable, ?_⟩
  have hPynn : (0:ℝ) ≤ ∑' j, ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2 :=
    tsum_nonneg fun j => by positivity
  calc (∑' m, (∑ k ∈ F, x k * y (k - m)) ^ 2)
      ≤ ∑' m, C_K * ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
          (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) :=
        hsummable.tsum_le_tsum hstep hmajS
    _ = C_K * ∑' m, ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
          (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) := tsum_mul_left
    _ = C_K * ∑ k ∈ F, ∑' m, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
          (‖freq (k - m)‖ ^ ((7:ℝ)/4) * y (k - m) ^ 2) := by
        rw [Summable.tsum_finsetSum hinner]
    _ = C_K * ∑ k ∈ F, (‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
          (∑' j, ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2) := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [tsum_mul_left, hshiftT k]
    _ = C_K * (∑' j, ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2) *
          ∑ k ∈ F, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2 := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ C_K * (∑' j, ‖freq j‖ ^ ((7:ℝ)/4) * y j ^ 2) *
          ∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hPxS.sum_le_tsum F (fun k _ => by positivity)
    _ = C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * x k ^ 2) *
          (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * y k ^ 2) := by ring

/-! ### Helpers for the pairing absorption -/

private lemma b2_l2_mul_summable {f g : (Fin 3 → ℤ) → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hg : ∀ k, 0 ≤ g k) (hf2 : Summable fun k => f k ^ 2)
    (hg2 : Summable fun k => g k ^ 2) : Summable fun k => f k * g k :=
  Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two hf hg
    (hf2.congr fun _ => b2_sq_rpow _) (hg2.congr fun _ => b2_sq_rpow _)

private lemma b2_tsum_mul_le {f g : (Fin 3 → ℤ) → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hg : ∀ k, 0 ≤ g k) (hf2 : Summable fun k => f k ^ 2)
    (hg2 : Summable fun k => g k ^ 2) :
    (∑' k, f k * g k) ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf hg
    (hf2.congr fun k => b2_sq_rpow _) (hg2.congr fun k => b2_sq_rpow _)
  have e1 : (∑' k, f k ^ (2:ℝ)) = ∑' k, f k ^ 2 := tsum_congr fun k => (b2_sq_rpow _).symm
  have e2 : (∑' k, g k ^ (2:ℝ)) = ∑' k, g k ^ 2 := tsum_congr fun k => (b2_sq_rpow _).symm
  rw [e1, e2] at cs
  calc (∑' k, f k * g k)
      ≤ (∑' k, f k ^ 2) ^ (1/(2:ℝ)) * (∑' k, g k ^ 2) ^ (1/(2:ℝ)) := cs
    _ = Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

private lemma b2_young8 {B lam e s : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam)
    (he : 0 ≤ e) (hs : 0 ≤ s) :
    B * (e ^ ((1:ℝ)/8) * s ^ ((7:ℝ)/8)) ≤
      (1/8) * (B ^ (8:ℝ) * lam ^ (-(7:ℝ)) * e) + (7/8) * (lam * s) := by
  have hp1 : (0:ℝ) ≤ B ^ (8:ℝ) * lam ^ (-(7:ℝ)) * e := by positivity
  have hp2 : (0:ℝ) ≤ lam * s := by positivity
  have gm := Real.geom_mean_le_arith_mean2_weighted (w₁ := (1:ℝ)/8) (w₂ := (7:ℝ)/8)
    (by norm_num) (by norm_num) hp1 hp2 (by norm_num)
  have e1 : (B ^ (8:ℝ)) ^ ((1:ℝ)/8) = B := by
    rw [← Real.rpow_mul hB, show (8:ℝ) * ((1:ℝ)/8) = 1 by norm_num, Real.rpow_one]
  have e2 : (lam ^ (-(7:ℝ))) ^ ((1:ℝ)/8) = lam ^ (-((7:ℝ)/8)) := by
    rw [← Real.rpow_mul hlam.le, show -(7:ℝ) * ((1:ℝ)/8) = -((7:ℝ)/8) by norm_num]
  have hcancel : lam ^ (-((7:ℝ)/8)) * lam ^ ((7:ℝ)/8) = 1 := by
    rw [← Real.rpow_add hlam, show -((7:ℝ)/8) + (7:ℝ)/8 = 0 by norm_num, Real.rpow_zero]
  have key : (B ^ (8:ℝ) * lam ^ (-(7:ℝ)) * e) ^ ((1:ℝ)/8) * (lam * s) ^ ((7:ℝ)/8)
      = B * (e ^ ((1:ℝ)/8) * s ^ ((7:ℝ)/8)) * (lam ^ (-((7:ℝ)/8)) * lam ^ ((7:ℝ)/8)) := by
    rw [Real.mul_rpow (by positivity) he, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hlam.le hs, e1, e2]
    ring
  calc B * (e ^ ((1:ℝ)/8) * s ^ ((7:ℝ)/8))
      = (B ^ (8:ℝ) * lam ^ (-(7:ℝ)) * e) ^ ((1:ℝ)/8) * (lam * s) ^ ((7:ℝ)/8) := by
        rw [key, hcancel, mul_one]
    _ ≤ (1/8) * (B ^ (8:ℝ) * lam ^ (-(7:ℝ)) * e) + (7/8) * (lam * s) := gm

private lemma b2_young16 {B lam e s : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam)
    (he : 0 ≤ e) (hs : 0 ≤ s) :
    B * (e ^ ((1:ℝ)/16) * s ^ ((15:ℝ)/16)) ≤
      (1/16) * (B ^ (16:ℝ) * lam ^ (-(15:ℝ)) * e) + (15/16) * (lam * s) := by
  have hp1 : (0:ℝ) ≤ B ^ (16:ℝ) * lam ^ (-(15:ℝ)) * e := by positivity
  have hp2 : (0:ℝ) ≤ lam * s := by positivity
  have gm := Real.geom_mean_le_arith_mean2_weighted (w₁ := (1:ℝ)/16) (w₂ := (15:ℝ)/16)
    (by norm_num) (by norm_num) hp1 hp2 (by norm_num)
  have e1 : (B ^ (16:ℝ)) ^ ((1:ℝ)/16) = B := by
    rw [← Real.rpow_mul hB, show (16:ℝ) * ((1:ℝ)/16) = 1 by norm_num, Real.rpow_one]
  have e2 : (lam ^ (-(15:ℝ))) ^ ((1:ℝ)/16) = lam ^ (-((15:ℝ)/16)) := by
    rw [← Real.rpow_mul hlam.le, show -(15:ℝ) * ((1:ℝ)/16) = -((15:ℝ)/16) by norm_num]
  have hcancel : lam ^ (-((15:ℝ)/16)) * lam ^ ((15:ℝ)/16) = 1 := by
    rw [← Real.rpow_add hlam, show -((15:ℝ)/16) + (15:ℝ)/16 = 0 by norm_num, Real.rpow_zero]
  have key : (B ^ (16:ℝ) * lam ^ (-(15:ℝ)) * e) ^ ((1:ℝ)/16) * (lam * s) ^ ((15:ℝ)/16)
      = B * (e ^ ((1:ℝ)/16) * s ^ ((15:ℝ)/16)) * (lam ^ (-((15:ℝ)/16)) * lam ^ ((15:ℝ)/16)) := by
    rw [Real.mul_rpow (by positivity) he, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hlam.le hs, e1, e2]
    ring
  calc B * (e ^ ((1:ℝ)/16) * s ^ ((15:ℝ)/16))
      = (B ^ (16:ℝ) * lam ^ (-(15:ℝ)) * e) ^ ((1:ℝ)/16) * (lam * s) ^ ((15:ℝ)/16) := by
        rw [key, hcancel, mul_one]
    _ ≤ (1/16) * (B ^ (16:ℝ) * lam ^ (-(15:ℝ)) * e) + (15/16) * (lam * s) := gm

private lemma b2_young2 {A u v ε : ℝ} (_hA : 0 ≤ A) (hε : 0 < ε) :
    A * u * v ≤ ε * u ^ 2 + A ^ 2 / (4 * ε) * v ^ 2 := by
  have hc : 4 * ε * (A ^ 2 / (4 * ε)) = A ^ 2 := by field_simp
  nlinarith [sq_nonneg (2 * ε * u - A * v), hε, sq_nonneg (A * v)]

private lemma b2_young_sqrt {A e s ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (he : 0 ≤ e) (hs : 0 ≤ s) :
    A * (Real.sqrt s * Real.sqrt e) ≤ ε * s + A ^ 2 / (4 * ε) * e := by
  have h1 := b2_young2 (A := A) (u := Real.sqrt s) (v := Real.sqrt e) hA hε
  rw [Real.sq_sqrt hs, Real.sq_sqrt he] at h1
  calc A * (Real.sqrt s * Real.sqrt e) = A * Real.sqrt s * Real.sqrt e := by ring
    _ ≤ ε * s + A ^ 2 / (4 * ε) * e := h1

private lemma b2_term_norm_le (x y : (Fin 3 → ℤ) → Vel) (k l : Fin 3 → ℤ) :
    ‖(Complex.I * dotR (x l) (freq (k - l))) • y (k - l)‖ ≤
      ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖) := by
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotR (x l) (freq (k - l))‖ * ‖y (k - l)‖
      ≤ (‖freq (k - l)‖ * ‖x l‖) * ‖y (k - l)‖ :=
        mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
    _ = ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖) := by ring

set_option maxHeartbeats 1000000 in
/-- **L5, the absorbed pairing bound.** -/
theorem pairing_absorbed : ∀ {ν E Z : ℝ}, 0 < ν → 0 ≤ E → 0 ≤ Z → ∃ K, 0 < K ∧
    ∀ {a b : (Fin 3 → ℤ) → Vel},
    Summable (fun l => ‖a l‖ ^ 2) → Summable (fun l => ‖freq l‖ ^ 2 * ‖a l‖ ^ 2) →
    Summable (fun l => ‖b l‖ ^ 2) → Summable (fun l => ‖freq l‖ ^ 2 * ‖b l‖ ^ 2) →
    en a ≤ E → ens a ≤ Z → en b ≤ E → ens b ≤ Z → a 0 = b 0 →
    ∀ (F : Finset (Fin 3 → ℤ)),
    2 * |∑ k ∈ F, inner ℝ (convFull a k - convFull b k) (a k - b k)| ≤
      ν * ens (fun l => a l - b l) + K * en (fun l => a l - b l) := by
  intro ν E Z hν hE0 hZ0
  obtain ⟨C_K, hCK, hkerS, hkerB⟩ := kernel_sum_le
  refine ⟨(1/8) * ((2 * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (8 * ν / 21) ^ (-(7:ℝ)))
      + (2 * Real.sqrt E) ^ 2 / (4 * (ν / 3))
      + (1/16) * ((2 * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
          * (16 * ν / 45) ^ (-(15:ℝ)))
      + 1, by positivity, ?_⟩
  intro a b hEa hZa hEb hZb henA hensA henB hensB h0 F
  set d : (Fin 3 → ℤ) → Vel := fun l => a l - b l with hd
  have hdk : ∀ k, a k - b k = d k := fun _ => rfl
  have hEd : Summable fun l => ‖d l‖ ^ 2 := summable_sq_sub hEa hEb
  have hZd : Summable fun l => ‖freq l‖ ^ 2 * ‖d l‖ ^ 2 := summable_wsq_sub hZa hZb
  have hd0 : d 0 = 0 := sub_eq_zero_of_eq h0
  have hx : ∀ k, (0:ℝ) ≤ ‖d k‖ := fun k => norm_nonneg _
  have hx0 : ‖d 0‖ = 0 := by rw [hd0, norm_zero]
  have he0 : (0:ℝ) ≤ en d := tsum_nonneg fun l => sq_nonneg _
  have hs0 : (0:ℝ) ≤ ens d := tsum_nonneg fun l => by positivity
  -- interpolation for the defect
  obtain ⟨hPxS, hPxB⟩ := weighted_interp (x := fun k => ‖d k‖) hx hEd hZd
  have hPxB' : (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2) ≤
      en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8) := hPxB
  have hPxnn : (0:ℝ) ≤ ∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2 :=
    tsum_nonneg fun k => by positivity
  -- majorants for the two telescope pieces
  have hmaj1 : ∀ k, Summable fun l => ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖) :=
    fun k => mixed_summable_convMaj hEd hZa k
  have hmaj2 : ∀ k, Summable fun l => ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖) :=
    fun k => mixed_summable_convMaj hEb hZd k
  -- pointwise pairing bound
  have hpair : ∀ k, |inner ℝ (convFull a k - convFull b k) (d k)| ≤
      ((∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) +
       (∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖))) * ‖d k‖ := by
    intro k
    rw [convFull_sub hEa hZa hEb hZb k]
    simp only [hdk]
    have hn1 : Summable fun l => ‖(Complex.I * dotR (d l) (freq (k - l))) • a (k - l)‖ :=
      (hmaj1 k).of_nonneg_of_le (fun l => norm_nonneg _) (fun l => b2_term_norm_le d a k l)
    have hn2 : Summable fun l => ‖(Complex.I * dotR (b l) (freq (k - l))) • d (k - l)‖ :=
      (hmaj2 k).of_nonneg_of_le (fun l => norm_nonneg _) (fun l => b2_term_norm_le b d k l)
    have hb1 : ‖∑' l, (Complex.I * dotR (d l) (freq (k - l))) • a (k - l)‖ ≤
        ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖) :=
      (norm_tsum_le_tsum_norm hn1).trans
        (hn1.tsum_le_tsum (fun l => b2_term_norm_le d a k l) (hmaj1 k))
    have hb2 : ‖∑' l, (Complex.I * dotR (b l) (freq (k - l))) • d (k - l)‖ ≤
        ∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖) :=
      (norm_tsum_le_tsum_norm hn2).trans
        (hn2.tsum_le_tsum (fun l => b2_term_norm_le b d k l) (hmaj2 k))
    calc |inner ℝ ((-(∑' l, (Complex.I * dotR (d l) (freq (k - l))) • a (k - l))) +
          (-(∑' l, (Complex.I * dotR (b l) (freq (k - l))) • d (k - l)))) (d k)|
        ≤ |inner ℝ (-(∑' l, (Complex.I * dotR (d l) (freq (k - l))) • a (k - l))) (d k)| +
          |inner ℝ (-(∑' l, (Complex.I * dotR (b l) (freq (k - l))) • d (k - l))) (d k)| := by
          rw [inner_add_left]
          exact abs_add_le _ _
      _ ≤ ‖-(∑' l, (Complex.I * dotR (d l) (freq (k - l))) • a (k - l))‖ * ‖d k‖ +
          ‖-(∑' l, (Complex.I * dotR (b l) (freq (k - l))) • d (k - l))‖ * ‖d k‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ = ‖∑' l, (Complex.I * dotR (d l) (freq (k - l))) • a (k - l)‖ * ‖d k‖ +
          ‖∑' l, (Complex.I * dotR (b l) (freq (k - l))) • d (k - l)‖ * ‖d k‖ := by
          rw [norm_neg, norm_neg]
      _ ≤ (∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) * ‖d k‖ +
          (∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖)) * ‖d k‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hb2 (norm_nonneg _))
      _ = ((∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) +
           (∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖))) * ‖d k‖ := by ring
  -- sum over F
  have hsumF : 2 * |∑ k ∈ F, inner ℝ (convFull a k - convFull b k) (d k)| ≤
      2 * ((∑ k ∈ F, ‖d k‖ * ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) +
           (∑ k ∈ F, ‖d k‖ * ∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖))) := by
    have h1 : |∑ k ∈ F, inner ℝ (convFull a k - convFull b k) (d k)| ≤
        ∑ k ∈ F, |inner ℝ (convFull a k - convFull b k) (d k)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ k ∈ F, |inner ℝ (convFull a k - convFull b k) (d k)|) ≤
        ∑ k ∈ F, ((∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) +
          (∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖))) * ‖d k‖ :=
      Finset.sum_le_sum fun k _ => hpair k
    have h3 : (∑ k ∈ F, ((∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) +
          (∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖))) * ‖d k‖) =
        (∑ k ∈ F, ‖d k‖ * ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) +
        (∑ k ∈ F, ‖d k‖ * ∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith
  -- === T1 : the a-slot telescope term ===
  have hM1 : ∀ k : Fin 3 → ℤ, (∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) =
      ∑' m, (‖freq m‖ * ‖a m‖) * ‖d (k - m)‖ := by
    intro k
    have h := (Equiv.subLeft k).tsum_eq (f := fun m => (‖freq m‖ * ‖a m‖) * ‖d (k - m)‖)
    simp only [Equiv.subLeft_apply] at h
    rw [← h]
    exact tsum_congr fun l => by rw [sub_sub_cancel]; ring
  have hea2 : Summable fun m => (‖freq m‖ * ‖a m‖) ^ 2 := hZa.congr fun m => by ring
  have hxshift : ∀ k : Fin 3 → ℤ, Summable fun m => ‖d (k - m)‖ ^ 2 := by
    intro k
    have h := ((Equiv.subLeft k).summable_iff (f := fun j => ‖d j‖ ^ 2)).mpr hEd
    exact h.congr fun m => by simp [Function.comp]
  have hprod1 : ∀ k : Fin 3 → ℤ, Summable fun m => (‖freq m‖ * ‖a m‖) * ‖d (k - m)‖ :=
    fun k => b2_l2_mul_summable (fun m => by positivity) (fun m => norm_nonneg _)
      hea2 (hxshift k)
  have hswap1 : (∑ k ∈ F, ‖d k‖ * ∑' m, (‖freq m‖ * ‖a m‖) * ‖d (k - m)‖) =
      ∑' m, (‖freq m‖ * ‖a m‖) * ∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖ := by
    have h1 : ∀ k ∈ F, Summable fun m => ‖d k‖ * ((‖freq m‖ * ‖a m‖) * ‖d (k - m)‖) :=
      fun k _ => (hprod1 k).mul_left _
    calc (∑ k ∈ F, ‖d k‖ * ∑' m, (‖freq m‖ * ‖a m‖) * ‖d (k - m)‖)
        = ∑ k ∈ F, ∑' m, ‖d k‖ * ((‖freq m‖ * ‖a m‖) * ‖d (k - m)‖) :=
          Finset.sum_congr rfl fun k _ => tsum_mul_left.symm
      _ = ∑' m, ∑ k ∈ F, ‖d k‖ * ((‖freq m‖ * ‖a m‖) * ‖d (k - m)‖) :=
          (Summable.tsum_finsetSum h1).symm
      _ = ∑' m, (‖freq m‖ * ‖a m‖) * ∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖ := by
          refine tsum_congr fun m => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hcc := conv_corr_sq_le (x := fun k => ‖d k‖) (y := fun k => ‖d k‖) hx hx hx0 hx0
    hEd hZd hEd hZd C_K hCK ⟨hkerS, hkerB⟩ F
  have hCnn : ∀ m, (0:ℝ) ≤ ∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖ :=
    fun m => Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hT1cs : (∑' m, (‖freq m‖ * ‖a m‖) * ∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖) ≤
      Real.sqrt (∑' m, (‖freq m‖ * ‖a m‖) ^ 2) *
        Real.sqrt (∑' m, (∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖) ^ 2) :=
    b2_tsum_mul_le (fun m => by positivity) hCnn hea2 hcc.1
  have hsq1 : Real.sqrt (∑' m, (‖freq m‖ * ‖a m‖) ^ 2) ≤ Real.sqrt Z := by
    refine Real.sqrt_le_sqrt ?_
    calc (∑' m, (‖freq m‖ * ‖a m‖) ^ 2) = ∑' m, ‖freq m‖ ^ 2 * ‖a m‖ ^ 2 :=
          tsum_congr fun m => by ring
      _ ≤ Z := hensA
  have hsq2 : Real.sqrt (∑' m, (∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖) ^ 2) ≤
      Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2) := by
    calc Real.sqrt (∑' m, (∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖) ^ 2)
        ≤ Real.sqrt (C_K * ((∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2) *
            (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2))) :=
          Real.sqrt_le_sqrt (by rw [← mul_assoc]; exact hcc.2)
      _ = Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2) := by
          rw [Real.sqrt_mul hCK.le, Real.sqrt_mul_self hPxnn]
  have hT1 : (∑ k ∈ F, ‖d k‖ * ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) ≤
      Real.sqrt (C_K * Z) * (en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) := by
    have heq : (∑ k ∈ F, ‖d k‖ * ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) =
        ∑' m, (‖freq m‖ * ‖a m‖) * ∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖ := by
      rw [← hswap1]
      exact Finset.sum_congr rfl fun k _ => by rw [hM1 k]
    rw [heq]
    refine hT1cs.trans ?_
    have h2 : Real.sqrt (∑' m, (‖freq m‖ * ‖a m‖) ^ 2) *
        Real.sqrt (∑' m, (∑ k ∈ F, ‖d k‖ * ‖d (k - m)‖) ^ 2) ≤
        Real.sqrt Z * (Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2)) :=
      mul_le_mul hsq1 hsq2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine h2.trans ?_
    calc Real.sqrt Z * (Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2))
        = Real.sqrt (C_K * Z) * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖d k‖ ^ 2) := by
          rw [Real.sqrt_mul hCK.le]; ring
      _ ≤ Real.sqrt (C_K * Z) * (en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) :=
          mul_le_mul_of_nonneg_left hPxB' (Real.sqrt_nonneg _)
  have h2T1 : 2 * (∑ k ∈ F, ‖d k‖ * ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖)) ≤
      (1/8) * ((2 * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (8 * ν / 21) ^ (-(7:ℝ))) * en d
        + (ν/3) * ens d := by
    have hyoungA := b2_young8 (B := 2 * Real.sqrt (C_K * Z)) (lam := 8 * ν / 21)
      (by positivity) (by positivity) he0 hs0
    calc 2 * (∑ k ∈ F, ‖d k‖ * ∑' l, ‖d l‖ * (‖freq (k - l)‖ * ‖a (k - l)‖))
        ≤ (2 * Real.sqrt (C_K * Z)) * (en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) := by
          linarith [hT1]
      _ ≤ (1/8) * ((2 * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (8 * ν / 21) ^ (-(7:ℝ)) * en d)
            + (7/8) * ((8 * ν / 21) * ens d) := hyoungA
      _ = (1/8) * ((2 * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (8 * ν / 21) ^ (-(7:ℝ))) * en d
            + (ν/3) * ens d := by ring
  -- === T2 : the b-slot telescope term, split at the zero mode ===
  have hytnn : ∀ j : Fin 3 → ℤ, (0:ℝ) ≤ if j = 0 then (0:ℝ) else ‖b j‖ := by
    intro j
    by_cases hj : j = 0
    · rw [if_pos hj]
    · rw [if_neg hj]; exact norm_nonneg _
  have hyt0 : (fun j : Fin 3 → ℤ => if j = 0 then (0:ℝ) else ‖b j‖) 0 = 0 := by simp
  have hytle : ∀ l, (if l = 0 then (0:ℝ) else ‖b l‖) ^ 2 ≤ ‖b l‖ ^ 2 := by
    intro l
    by_cases hl : l = 0
    · rw [if_pos hl]; simp
    · rw [if_neg hl]
  have hytE : Summable fun l => (if l = 0 then (0:ℝ) else ‖b l‖) ^ 2 :=
    hEb.of_nonneg_of_le (fun l => sq_nonneg _) hytle
  have hytZle : ∀ l, ‖freq l‖ ^ 2 * (if l = 0 then (0:ℝ) else ‖b l‖) ^ 2 ≤
      ‖freq l‖ ^ 2 * ‖b l‖ ^ 2 := fun l =>
    mul_le_mul_of_nonneg_left (hytle l) (sq_nonneg _)
  have hytZ : Summable fun l => ‖freq l‖ ^ 2 * (if l = 0 then (0:ℝ) else ‖b l‖) ^ 2 :=
    hZb.of_nonneg_of_le (fun l => by positivity) hytZle
  -- split of the b-majorant at l = 0
  have hsplit2 : ∀ k : Fin 3 → ℤ, (∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖)) =
      ‖b 0‖ * (‖freq k‖ * ‖d k‖) +
      ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖) := by
    intro k
    have h := (hmaj2 k).tsum_eq_add_tsum_ite 0
    rw [h, sub_zero]
    congr 1
    refine tsum_congr fun l => ?_
    by_cases hl : l = 0
    · simp [hl]
    · simp [hl]
  have hT2split : (∑ k ∈ F, ‖d k‖ * ∑' l, ‖b l‖ * (‖freq (k - l)‖ * ‖d (k - l)‖)) =
      (∑ k ∈ F, ‖d k‖ * (‖b 0‖ * (‖freq k‖ * ‖d k‖))) +
      (∑ k ∈ F, ‖d k‖ *
        ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsplit2 k, mul_add]
  -- --- T2a : the zero-mode piece ---
  have hb0E : ‖b 0‖ ≤ Real.sqrt E := by
    have h1 : ‖b 0‖ ^ 2 ≤ en b := hEb.le_tsum 0 (fun j _ => sq_nonneg _)
    calc ‖b 0‖ = Real.sqrt (‖b 0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt E := Real.sqrt_le_sqrt (h1.trans henB)
  have hT2a : (∑ k ∈ F, ‖d k‖ * (‖b 0‖ * (‖freq k‖ * ‖d k‖))) ≤
      Real.sqrt E * (Real.sqrt (ens d) * Real.sqrt (en d)) := by
    have h3 : (0:ℝ) ≤ ∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖ :=
      Finset.sum_nonneg fun k _ => by positivity
    have hfin : (∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖) ≤
        Real.sqrt (ens d) * Real.sqrt (en d) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun k => ‖freq k‖ * ‖d k‖)
        (fun k => ‖d k‖)
      have h1 : (∑ k ∈ F, (‖freq k‖ * ‖d k‖) ^ 2) ≤ ens d := by
        calc (∑ k ∈ F, (‖freq k‖ * ‖d k‖) ^ 2) = ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖d k‖ ^ 2 :=
              Finset.sum_congr rfl fun k _ => by ring
          _ ≤ ens d := hZd.sum_le_tsum F (fun k _ => by positivity)
      have h2 : (∑ k ∈ F, ‖d k‖ ^ 2) ≤ en d := hEd.sum_le_tsum F (fun k _ => sq_nonneg _)
      have h4 : (∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖) ^ 2 ≤ ens d * en d := by
        calc (∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖) ^ 2
            ≤ (∑ k ∈ F, (‖freq k‖ * ‖d k‖) ^ 2) * ∑ k ∈ F, ‖d k‖ ^ 2 := hcs
          _ ≤ ens d * en d :=
              mul_le_mul h1 h2 (Finset.sum_nonneg fun k _ => sq_nonneg _) hs0
      calc (∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖)
          = Real.sqrt ((∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖) ^ 2) := (Real.sqrt_sq h3).symm
        _ ≤ Real.sqrt (ens d * en d) := Real.sqrt_le_sqrt h4
        _ = Real.sqrt (ens d) * Real.sqrt (en d) := Real.sqrt_mul hs0 _
    calc (∑ k ∈ F, ‖d k‖ * (‖b 0‖ * (‖freq k‖ * ‖d k‖)))
        = ‖b 0‖ * ∑ k ∈ F, ‖freq k‖ * ‖d k‖ * ‖d k‖ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ Real.sqrt E * (Real.sqrt (ens d) * Real.sqrt (en d)) :=
          mul_le_mul hb0E hfin h3 (Real.sqrt_nonneg _)
  have h2T2a : 2 * (∑ k ∈ F, ‖d k‖ * (‖b 0‖ * (‖freq k‖ * ‖d k‖))) ≤
      (ν/3) * ens d + (2 * Real.sqrt E) ^ 2 / (4 * (ν / 3)) * en d := by
    have hys := b2_young_sqrt (A := 2 * Real.sqrt E) (ε := ν/3)
      (by positivity) (by positivity) he0 hs0
    nlinarith [hT2a, hys]
  -- --- T2b : the punctured piece, via the correlation bound ---
  have hM2 : ∀ k : Fin 3 → ℤ,
      (∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖)) =
      ∑' m, (‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) := by
    intro k
    have h := (Equiv.subLeft k).tsum_eq
      (f := fun m => (‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖))
    simp only [Equiv.subLeft_apply] at h
    rw [← h]
    refine tsum_congr fun l => ?_
    rw [sub_sub_cancel]
    ring
  have hgd2 : Summable fun m => (‖freq m‖ * ‖d m‖) ^ 2 := hZd.congr fun m => by ring
  have hprod2 : ∀ k : Fin 3 → ℤ,
      Summable fun m => (‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) := by
    intro k
    have hyshift : Summable fun m => (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) ^ 2 := by
      have h := ((Equiv.subLeft k).summable_iff
        (f := fun j => (if j = 0 then (0:ℝ) else ‖b j‖) ^ 2)).mpr hytE
      exact h.congr fun m => by simp [Function.comp]
    exact b2_l2_mul_summable (fun m => by positivity) (fun m => hytnn _) hgd2 hyshift
  have hswap2 : (∑ k ∈ F, ‖d k‖ *
      ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖)) =
      ∑' m, (‖freq m‖ * ‖d m‖) *
        ∑ k ∈ F, ‖d k‖ * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) := by
    have h1 : ∀ k ∈ F, Summable fun m =>
        ‖d k‖ * ((‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖)) :=
      fun k _ => (hprod2 k).mul_left _
    calc (∑ k ∈ F, ‖d k‖ *
          ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖))
        = ∑ k ∈ F, ‖d k‖ *
            ∑' m, (‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) :=
          Finset.sum_congr rfl fun k _ => by rw [hM2 k]
      _ = ∑ k ∈ F, ∑' m, ‖d k‖ *
            ((‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖)) :=
          Finset.sum_congr rfl fun k _ => tsum_mul_left.symm
      _ = ∑' m, ∑ k ∈ F, ‖d k‖ *
            ((‖freq m‖ * ‖d m‖) * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖)) :=
          (Summable.tsum_finsetSum h1).symm
      _ = ∑' m, (‖freq m‖ * ‖d m‖) *
            ∑ k ∈ F, ‖d k‖ * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) := by
          refine tsum_congr fun m => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hcc2 := conv_corr_sq_le (x := fun k => ‖d k‖)
    (y := fun j => if j = 0 then (0:ℝ) else ‖b j‖) hx hytnn hx0 hyt0
    hEd hZd hytE hytZ C_K hCK ⟨hkerS, hkerB⟩ F
  have hDnn : ∀ m, (0:ℝ) ≤ ∑ k ∈ F, ‖d k‖ * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖) :=
    fun m => Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hytnn _)
  have hT2bcs : (∑' m, (‖freq m‖ * ‖d m‖) *
      ∑ k ∈ F, ‖d k‖ * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖)) ≤
      Real.sqrt (∑' m, (‖freq m‖ * ‖d m‖) ^ 2) *
        Real.sqrt (∑' m,
          (∑ k ∈ F, ‖d k‖ * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖)) ^ 2) :=
    b2_tsum_mul_le (fun m => by positivity) hDnn hgd2 hcc2.1
  have hgd_eq : (∑' m, (‖freq m‖ * ‖d m‖) ^ 2) = ens d := tsum_congr fun m => by ring
  -- interpolation for the punctured b-family
  have hPyt : (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (if k = 0 then (0:ℝ) else ‖b k‖) ^ 2) ≤
      E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8) := by
    obtain ⟨hS, hB⟩ := weighted_interp
      (x := fun j => if j = 0 then (0:ℝ) else ‖b j‖) hytnn hytE hytZ
    refine hB.trans ?_
    have h1 : (∑' k, (if k = 0 then (0:ℝ) else ‖b k‖) ^ 2) ≤ E :=
      (hytE.tsum_le_tsum hytle hEb).trans henB
    have h2 : (∑' k, ‖freq k‖ ^ 2 * (if k = 0 then (0:ℝ) else ‖b k‖) ^ 2) ≤ Z :=
      (hytZ.tsum_le_tsum hytZle hZb).trans hensB
    have h1nn : (0:ℝ) ≤ ∑' k, (if k = 0 then (0:ℝ) else ‖b k‖) ^ 2 :=
      tsum_nonneg fun k => sq_nonneg _
    have h2nn : (0:ℝ) ≤ ∑' k, ‖freq k‖ ^ 2 * (if k = 0 then (0:ℝ) else ‖b k‖) ^ 2 :=
      tsum_nonneg fun k => by positivity
    exact mul_le_mul (Real.rpow_le_rpow h1nn h1 (by norm_num))
      (Real.rpow_le_rpow h2nn h2 (by norm_num))
      (Real.rpow_nonneg h2nn _) (Real.rpow_nonneg hE0 _)
  have hPytnn : (0:ℝ) ≤ ∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (if k = 0 then (0:ℝ) else ‖b k‖) ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have hPnn : (0:ℝ) ≤ en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8) :=
    mul_nonneg (Real.rpow_nonneg he0 _) (Real.rpow_nonneg hs0 _)
  have hsqD : Real.sqrt (∑' m,
      (∑ k ∈ F, ‖d k‖ * (if k - m = 0 then (0:ℝ) else ‖b (k - m)‖)) ^ 2) ≤
      Real.sqrt (C_K * ((en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) *
        (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) := by
    refine Real.sqrt_le_sqrt ?_
    refine hcc2.2.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCK.le
    exact mul_le_mul hPxB' hPyt hPytnn hPnn
  have hsqrtP : Real.sqrt (en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) =
      en d ^ ((1:ℝ)/16) * ens d ^ ((7:ℝ)/16) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg he0 _) (Real.rpow_nonneg hs0 _),
      ← Real.rpow_mul he0, ← Real.rpow_mul hs0]
    norm_num
  have hsplits : Real.sqrt (ens d) * ens d ^ ((7:ℝ)/16) = ens d ^ ((15:ℝ)/16) := by
    rw [Real.sqrt_eq_rpow, show (15:ℝ)/16 = 1/2 + 7/16 by norm_num,
      Real.rpow_add' hs0 (by norm_num)]
  have hT2b : (∑ k ∈ F, ‖d k‖ *
      ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖)) ≤
      (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
        (en d ^ ((1:ℝ)/16) * ens d ^ ((15:ℝ)/16)) := by
    rw [hswap2]
    refine hT2bcs.trans ?_
    rw [hgd_eq]
    refine (mul_le_mul_of_nonneg_left hsqD (Real.sqrt_nonneg _)).trans ?_
    have hQnn : (0:ℝ) ≤ E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8) :=
      mul_nonneg (Real.rpow_nonneg hE0 _) (Real.rpow_nonneg hZ0 _)
    calc Real.sqrt (ens d) * Real.sqrt (C_K * ((en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) *
          (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))))
        = Real.sqrt (ens d) * (Real.sqrt C_K *
            (Real.sqrt (en d ^ ((1:ℝ)/8) * ens d ^ ((7:ℝ)/8)) *
              Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) := by
          rw [Real.sqrt_mul hCK.le, Real.sqrt_mul hPnn]
      _ = (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
            (en d ^ ((1:ℝ)/16) * (Real.sqrt (ens d) * ens d ^ ((7:ℝ)/16))) := by
          rw [hsqrtP]; ring
      _ = (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
            (en d ^ ((1:ℝ)/16) * ens d ^ ((15:ℝ)/16)) := by rw [hsplits]
      _ ≤ (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
            (en d ^ ((1:ℝ)/16) * ens d ^ ((15:ℝ)/16)) := le_rfl
  have h2T2b : 2 * (∑ k ∈ F, ‖d k‖ *
      ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖)) ≤
      (1/16) * ((2 * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
          * (16 * ν / 45) ^ (-(15:ℝ))) * en d
        + (ν/3) * ens d := by
    have hyoungB := b2_young16
      (B := 2 * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))))
      (lam := 16 * ν / 45) (by positivity) (by positivity) he0 hs0
    calc 2 * (∑ k ∈ F, ‖d k‖ *
          ∑' l, (if l = 0 then (0:ℝ) else ‖b l‖) * (‖freq (k - l)‖ * ‖d (k - l)‖))
        ≤ (2 * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) *
            (en d ^ ((1:ℝ)/16) * ens d ^ ((15:ℝ)/16)) := by
          linarith [hT2b]
      _ ≤ (1/16) * ((2 * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
              * (16 * ν / 45) ^ (-(15:ℝ)) * en d)
            + (15/16) * ((16 * ν / 45) * ens d) := hyoungB
      _ = (1/16) * ((2 * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
              * (16 * ν / 45) ^ (-(15:ℝ))) * en d
            + (ν/3) * ens d := by ring
  -- === final assembly ===
  simp only [hdk]
  refine hsumF.trans ?_
  rw [hT2split]
  linarith [h2T1, h2T2a, h2T2b, he0]

end TheoremB
