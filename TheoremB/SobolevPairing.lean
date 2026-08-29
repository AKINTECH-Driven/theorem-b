/-
# The level-m absorbed pairing (Tier 6, wave 2)

The graded convection pairing, fully absorbed at every Sobolev level:
`2 |Σ_{k∈S} ‖k‖^(2m) ⟪convGal S c k, c k⟫| ≤ ν·sob (m+1) c + K·sob m c`
with `K` of explicit form in the proof witness — a closed formula in
`(m, ν, E, Z)` and the lattice-kernel constant `C_K` — exported formally
as a compiled existence statement (`∃ K, 0 < K`).

The route is the HALF-WEIGHT SPLIT: `‖k‖^(2m) = ‖k‖^m · ‖k‖^m`; one factor
joins the pairing slot, lifting it to `z k = ‖k‖^m ‖c k‖` (whose ℓ² mass is
`sob m` — the level being estimated, allowed linearly); only the other
`‖k‖^m` is split across the convolution pair by the frequency triangle and
the `2^(m-1)` two-power inequality.  The two resulting pieces are
line-isomorphic ports of PairingBound's compiled T1 and T2b blocks under
`(en, ens) → (sob m, sob (m+1))`, with the SAME 7/4-kernel correlation
bound `conv_corr_sq_le` and the SAME `(1/8, 7/8)` interpolation
`weighted_interp`, applied to the lifted sequence.

Junk-tsum discipline: every tsum carries its Summable certificate; here all
of them are finite-support-trivial (`0 ∉ S` and `c` vanishes off `S`), so
no zero-mode piece exists and no convergence analysis is needed.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.SobolevNorms
import TheoremB.PairingBound

namespace TheoremB

open Set

/-! ### Private helpers (clones of the PairingBound privates, unchanged) -/

private lemma sp_sq_rpow (t : ℝ) : t ^ 2 = t ^ (2:ℝ) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

private lemma sp_tsum_mul_le {f g : (Fin 3 → ℤ) → ℝ} (hf : ∀ k, 0 ≤ f k)
    (hg : ∀ k, 0 ≤ g k) (hf2 : Summable fun k => f k ^ 2)
    (hg2 : Summable fun k => g k ^ 2) :
    (∑' k, f k * g k) ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf hg
    (hf2.congr fun k => sp_sq_rpow _) (hg2.congr fun k => sp_sq_rpow _)
  have e1 : (∑' k, f k ^ (2:ℝ)) = ∑' k, f k ^ 2 := tsum_congr fun k => (sp_sq_rpow _).symm
  have e2 : (∑' k, g k ^ (2:ℝ)) = ∑' k, g k ^ 2 := tsum_congr fun k => (sp_sq_rpow _).symm
  rw [e1, e2] at cs
  calc (∑' k, f k * g k)
      ≤ (∑' k, f k ^ 2) ^ (1/(2:ℝ)) * (∑' k, g k ^ 2) ^ (1/(2:ℝ)) := cs
    _ = Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

private lemma sp_young8 {B lam e s : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam)
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

private lemma sp_young16 {B lam e s : ℝ} (hB : 0 ≤ B) (hlam : 0 < lam)
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

private lemma sp_term_norm_le (x y : (Fin 3 → ℤ) → Vel) (k l : Fin 3 → ℤ) :
    ‖(Complex.I * dotR (x l) (freq (k - l))) • y (k - l)‖ ≤
      ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖) := by
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotR (x l) (freq (k - l))‖ * ‖y (k - l)‖
      ≤ (‖freq (k - l)‖ * ‖x l‖) * ‖y (k - l)‖ :=
        mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
    _ = ‖x l‖ * (‖freq (k - l)‖ * ‖y (k - l)‖) := by ring

set_option maxHeartbeats 1000000 in
/-- **W2 capstone: the level-`m` absorbed pairing.**  For finitely supported
fields avoiding the zero mode, with trapped energy and enstrophy budgets, the
`‖k‖^(2m)`-weighted convection pairing is absorbed: a `ν`-budget piece into
the dissipation level `sob (m+1)`, the rest into `K · sob m` with `K` of
explicit form in the proof witness (exported as `∃ K`). -/
theorem sobolev_pairing_absorbed {ν E Z : ℝ} (hν : 0 < ν) (hE : 0 ≤ E)
    (hZ : 0 ≤ Z) (m : ℕ) (hm : 1 ≤ m) :
    ∃ K, 0 < K ∧ ∀ {S : Finset (Fin 3 → ℤ)}, (0 : Fin 3 → ℤ) ∉ S →
      ∀ {c : (Fin 3 → ℤ) → Vel}, (∀ k ∉ S, c k = 0) →
        en c ≤ E → ens c ≤ Z →
        2 * |∑ k ∈ S, ‖freq k‖ ^ (2*m) * inner ℝ (convGal S c k) (c k)| ≤
          ν * sob (m+1) c + K * sob m c := by
  obtain ⟨C_K, hCK, hkerS, hkerB⟩ := kernel_sum_le
  refine ⟨(1/8) * ((2 * 2 ^ (m - 1) * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (4 * ν / 7) ^ (-(7:ℝ)))
      + (1/16) * ((2 * 2 ^ (m - 1) *
            (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
          * (8 * ν / 15) ^ (-(15:ℝ)))
      + 1, by positivity, ?_⟩
  intro S h0S c hsupp henE hensZ
  -- basic facts about the field
  have hc0 : c 0 = 0 := hsupp 0 h0S
  have hcnn : ∀ k, (0:ℝ) ≤ ‖c k‖ := fun k => norm_nonneg _
  have hznn : ∀ k, (0:ℝ) ≤ ‖freq k‖ ^ m * ‖c k‖ := fun k => by positivity
  have hy0 : ‖c (0 : Fin 3 → ℤ)‖ = 0 := by rw [hc0, norm_zero]
  have hz0 : ‖freq (0 : Fin 3 → ℤ)‖ ^ m * ‖c 0‖ = 0 := by rw [hc0, norm_zero, mul_zero]
  -- summability certificates: all finite-support-trivial
  have hcE : Summable fun k => ‖c k‖ ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp
  have hcZ : Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp
  have hzE : Summable fun k => (‖freq k‖ ^ m * ‖c k‖) ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp
  have hzZ : Summable fun k => ‖freq k‖ ^ 2 * (‖freq k‖ ^ m * ‖c k‖) ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp
  have hyaE : Summable fun j => (‖freq j‖ * ‖c j‖) ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
  have hybE : Summable fun j => (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
  -- Sobolev-mass identifications for the lifted sequence
  have hsobm : (∑' k, (‖freq k‖ ^ m * ‖c k‖) ^ 2) = sob m c := by
    have hdef : sob m c = ∑' k, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 := rfl
    rw [hdef]
    exact tsum_congr fun k => sq_norm_pow_mul k ‖c k‖ m
  have hsobm1 : (∑' k, ‖freq k‖ ^ 2 * (‖freq k‖ ^ m * ‖c k‖) ^ 2) = sob (m + 1) c := by
    have hdef : sob (m + 1) c = ∑' k, ‖freq k‖ ^ (2 * (m + 1)) * ‖c k‖ ^ 2 := rfl
    rw [hdef]
    refine tsum_congr fun k => ?_
    rw [sq_norm_pow_mul, ← mul_assoc, norm_sq_mul_pow]
  have hsm0 : (0:ℝ) ≤ sob m c := sob_nonneg m c
  have hsm10 : (0:ℝ) ≤ sob (m + 1) c := sob_nonneg (m + 1) c
  -- interpolation for the lifted sequence: P_m ≤ (sob m)^(1/8) (sob (m+1))^(7/8)
  obtain ⟨hPzS, hPzB⟩ := weighted_interp (x := fun k => ‖freq k‖ ^ m * ‖c k‖) hznn hzE hzZ
  have hPzB' : (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2) ≤
      sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8) := by
    have h : (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2) ≤
        (∑' k, (‖freq k‖ ^ m * ‖c k‖) ^ 2) ^ ((1:ℝ)/8) *
          (∑' k, ‖freq k‖ ^ 2 * (‖freq k‖ ^ m * ‖c k‖) ^ 2) ^ ((7:ℝ)/8) := hPzB
    rw [hsobm, hsobm1] at h
    exact h
  have hPznn : (0:ℝ) ≤ ∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2 :=
    tsum_nonneg fun k => by positivity
  have hintnn : (0:ℝ) ≤ sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8) :=
    mul_nonneg (Real.rpow_nonneg hsm0 _) (Real.rpow_nonneg hsm10 _)
  -- interpolation for the plain sequence against the (E, Z) budgets
  obtain ⟨hPcS, hPcB⟩ := weighted_interp (x := fun k => ‖c k‖) hcnn hcE hcZ
  have hPcB' : (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖c k‖ ^ 2) ≤
      E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8) := by
    have h : (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖c k‖ ^ 2) ≤
        (∑' k, ‖c k‖ ^ 2) ^ ((1:ℝ)/8) *
          (∑' k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2) ^ ((7:ℝ)/8) := hPcB
    refine h.trans ?_
    have h1 : (∑' k, ‖c k‖ ^ 2) ≤ E := henE
    have h2 : (∑' k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2) ≤ Z := hensZ
    have h1nn : (0:ℝ) ≤ ∑' k, ‖c k‖ ^ 2 := tsum_nonneg fun k => sq_nonneg _
    have h2nn : (0:ℝ) ≤ ∑' k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 := tsum_nonneg fun k => by positivity
    exact mul_le_mul (Real.rpow_le_rpow h1nn h1 (by norm_num))
      (Real.rpow_le_rpow h2nn h2 (by norm_num))
      (Real.rpow_nonneg h2nn _) (Real.rpow_nonneg hE _)
  have hPcnn : (0:ℝ) ≤ ∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * ‖c k‖ ^ 2 :=
    tsum_nonneg fun k => by positivity
  -- the two correlation-square bounds
  have hccA := conv_corr_sq_le (x := fun k => ‖freq k‖ ^ m * ‖c k‖)
    (y := fun k => ‖freq k‖ ^ m * ‖c k‖) hznn hznn hz0 hz0 hzE hzZ hzE hzZ
    C_K hCK ⟨hkerS, hkerB⟩ S
  have hccB := conv_corr_sq_le (x := fun k => ‖freq k‖ ^ m * ‖c k‖)
    (y := fun k => ‖c k‖) hznn hcnn hz0 hy0 hzE hzZ hcE hcZ
    C_K hCK ⟨hkerS, hkerB⟩ S
  -- === the pointwise weighted bound, half-weight split ===
  have hptw : ∀ k ∈ S, ‖freq k‖ ^ (2 * m) * |inner ℝ (convGal S c k) (c k)| ≤
      2 ^ (m - 1) *
        ((‖freq k‖ ^ m * ‖c k‖) *
            ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) +
         (‖freq k‖ ^ m * ‖c k‖) *
            ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) := by
    intro k hk
    have h1 : |inner ℝ (convGal S c k) (c k)| ≤
        (∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) * ‖c k‖ := by
      have hcg : convGal S c k =
          -∑ l ∈ S, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) := by
        unfold convGal
        rw [if_pos hk]
      calc |inner ℝ (convGal S c k) (c k)|
          ≤ ‖convGal S c k‖ * ‖c k‖ := abs_real_inner_le_norm _ _
        _ ≤ (∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) * ‖c k‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [hcg, norm_neg]
            exact (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun l _ => sp_term_norm_le c c k l)
    refine (mul_le_mul_of_nonneg_left h1
      (by positivity : (0:ℝ) ≤ ‖freq k‖ ^ (2 * m))).trans ?_
    have h3 : ‖freq k‖ ^ (2 * m) *
        ((∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) * ‖c k‖) =
        (∑ l ∈ S, ‖freq k‖ ^ m * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))) *
          (‖freq k‖ ^ m * ‖c k‖) := by
      rw [two_mul, pow_add, ← Finset.mul_sum]
      ring
    rw [h3]
    have h4 : (∑ l ∈ S, ‖freq k‖ ^ m * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))) ≤
        ∑ l ∈ S, 2 ^ (m - 1) *
          ((‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) +
           ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) := by
      refine Finset.sum_le_sum fun l _ => ?_
      calc ‖freq k‖ ^ m * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
          ≤ (2 ^ (m - 1) * (‖freq l‖ ^ m + ‖freq (k - l)‖ ^ m)) *
              (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) :=
            mul_le_mul_of_nonneg_right (norm_freq_pow_split k l hm) (by positivity)
        _ = 2 ^ (m - 1) *
              ((‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) +
               ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) := by ring
    calc (∑ l ∈ S, ‖freq k‖ ^ m * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))) *
          (‖freq k‖ ^ m * ‖c k‖)
        ≤ (∑ l ∈ S, 2 ^ (m - 1) *
            ((‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) +
             ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖)))) *
          (‖freq k‖ ^ m * ‖c k‖) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = 2 ^ (m - 1) *
            ((‖freq k‖ ^ m * ‖c k‖) *
                ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) +
             (‖freq k‖ ^ m * ‖c k‖) *
                ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          ring
  -- === sum over S ===
  have habs : |∑ k ∈ S, ‖freq k‖ ^ (2 * m) * inner ℝ (convGal S c k) (c k)| ≤
      ∑ k ∈ S, ‖freq k‖ ^ (2 * m) * |inner ℝ (convGal S c k) (c k)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun k _ => le_of_eq ?_
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ ‖freq k‖ ^ (2 * m) by positivity)]
  have hsum_ptw : (∑ k ∈ S, ‖freq k‖ ^ (2 * m) * |inner ℝ (convGal S c k) (c k)|) ≤
      2 ^ (m - 1) *
        ((∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
            ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) +
         (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
            ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖)))) := by
    calc (∑ k ∈ S, ‖freq k‖ ^ (2 * m) * |inner ℝ (convGal S c k) (c k)|)
        ≤ ∑ k ∈ S, 2 ^ (m - 1) *
            ((‖freq k‖ ^ m * ‖c k‖) *
                ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) +
             (‖freq k‖ ^ m * ‖c k‖) *
                ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) :=
          Finset.sum_le_sum hptw
      _ = 2 ^ (m - 1) *
            ((∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
                ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) +
             (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
                ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hsumS : 2 * |∑ k ∈ S, ‖freq k‖ ^ (2 * m) * inner ℝ (convGal S c k) (c k)| ≤
      2 * 2 ^ (m - 1) *
          (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
            ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) +
      2 * 2 ^ (m - 1) *
          (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
            ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) := by
    have h := habs.trans hsum_ptw
    linarith [h]
  -- === piece A' : the sob-m-weighted low slot (T1 clone) ===
  have hM1A : ∀ k : Fin 3 → ℤ,
      (∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) =
      ∑' j, (‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖) := by
    intro k
    have hext : (∑' l, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) =
        ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖) :=
      tsum_eq_sum fun l hl => by rw [hsupp l hl]; simp
    rw [← hext]
    have h := (Equiv.subLeft k).tsum_eq
      (f := fun j => (‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖))
    simp only [Equiv.subLeft_apply] at h
    rw [← h]
    exact tsum_congr fun l => by rw [sub_sub_cancel]; ring
  have hswapA : (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
      ∑' j, (‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) =
      ∑' j, (‖freq j‖ * ‖c j‖) *
        ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖) := by
    have h1 : ∀ k ∈ S, Summable fun j => (‖freq k‖ ^ m * ‖c k‖) *
        ((‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) :=
      fun k _ => summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
    calc (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
          ∑' j, (‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖))
        = ∑ k ∈ S, ∑' j, (‖freq k‖ ^ m * ‖c k‖) *
            ((‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) :=
          Finset.sum_congr rfl fun k _ => tsum_mul_left.symm
      _ = ∑' j, ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
            ((‖freq j‖ * ‖c j‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) :=
          (Summable.tsum_finsetSum h1).symm
      _ = ∑' j, (‖freq j‖ * ‖c j‖) *
            ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖) := by
          refine tsum_congr fun j => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have heqA : (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
      ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) =
      ∑' j, (‖freq j‖ * ‖c j‖) *
        ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖) := by
    rw [← hswapA]
    exact Finset.sum_congr rfl fun k _ => by rw [hM1A k]
  have hCnnA : ∀ j, (0:ℝ) ≤
      ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖) :=
    fun j => Finset.sum_nonneg fun k _ => by positivity
  have hT1csA : (∑' j, (‖freq j‖ * ‖c j‖) *
      ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) ≤
      Real.sqrt (∑' j, (‖freq j‖ * ‖c j‖) ^ 2) *
        Real.sqrt (∑' j,
          (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) ^ 2) :=
    sp_tsum_mul_le (fun j => by positivity) hCnnA hyaE hccA.1
  have hsq1A : Real.sqrt (∑' j, (‖freq j‖ * ‖c j‖) ^ 2) ≤ Real.sqrt Z := by
    refine Real.sqrt_le_sqrt ?_
    calc (∑' j, (‖freq j‖ * ‖c j‖) ^ 2) = ∑' j, ‖freq j‖ ^ 2 * ‖c j‖ ^ 2 :=
          tsum_congr fun j => by ring
      _ ≤ Z := hensZ
  have hsq2A : Real.sqrt (∑' j,
      (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) ^ 2) ≤
      Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2) := by
    calc Real.sqrt (∑' j,
        (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) ^ 2)
        ≤ Real.sqrt (C_K * ((∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2) *
            (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2))) :=
          Real.sqrt_le_sqrt (by rw [← mul_assoc]; exact hccA.2)
      _ = Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2) := by
          rw [Real.sqrt_mul hCK.le, Real.sqrt_mul_self hPznn]
  have hT1 : (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
      ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) ≤
      Real.sqrt (C_K * Z) * (sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) := by
    rw [heqA]
    refine hT1csA.trans ?_
    have h2 : Real.sqrt (∑' j, (‖freq j‖ * ‖c j‖) ^ 2) *
        Real.sqrt (∑' j,
          (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * (‖freq (k - j)‖ ^ m * ‖c (k - j)‖)) ^ 2) ≤
        Real.sqrt Z *
          (Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2)) :=
      mul_le_mul hsq1A hsq2A (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine h2.trans ?_
    calc Real.sqrt Z *
        (Real.sqrt C_K * (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2))
        = Real.sqrt (C_K * Z) *
            (∑' k, ‖freq k‖ ^ ((7:ℝ)/4) * (‖freq k‖ ^ m * ‖c k‖) ^ 2) := by
          rw [Real.sqrt_mul hCK.le]; ring
      _ ≤ Real.sqrt (C_K * Z) * (sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) :=
          mul_le_mul_of_nonneg_left hPzB' (Real.sqrt_nonneg _)
  have h2T1 : 2 * 2 ^ (m - 1) *
      (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
        ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)) ≤
      (1/8) * ((2 * 2 ^ (m - 1) * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (4 * ν / 7) ^ (-(7:ℝ)))
          * sob m c
        + ν / 2 * sob (m + 1) c := by
    have h2mnn : (0:ℝ) ≤ 2 * 2 ^ (m - 1) := by positivity
    have hyoungA := sp_young8 (B := 2 * 2 ^ (m - 1) * Real.sqrt (C_K * Z))
      (lam := 4 * ν / 7) (by positivity) (by positivity) hsm0 hsm10
    calc 2 * 2 ^ (m - 1) *
        (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
          ∑ l ∈ S, (‖freq l‖ ^ m * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖))
        ≤ 2 * 2 ^ (m - 1) *
            (Real.sqrt (C_K * Z) * (sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8))) :=
          mul_le_mul_of_nonneg_left hT1 h2mnn
      _ = (2 * 2 ^ (m - 1) * Real.sqrt (C_K * Z)) *
            (sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) := by ring
      _ ≤ (1/8) * ((2 * 2 ^ (m - 1) * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (4 * ν / 7) ^ (-(7:ℝ))
              * sob m c)
            + (7/8) * ((4 * ν / 7) * sob (m + 1) c) := hyoungA
      _ = (1/8) * ((2 * 2 ^ (m - 1) * Real.sqrt (C_K * Z)) ^ (8:ℝ) * (4 * ν / 7) ^ (-(7:ℝ)))
              * sob m c
            + ν / 2 * sob (m + 1) c := by ring
  -- === piece B' : the sob-(m+1)-weighted derivative slot (T2b clone) ===
  have hM1B : ∀ k : Fin 3 → ℤ,
      (∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) =
      ∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖ := by
    intro k
    have hext : (∑' l, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) =
        ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖)) :=
      tsum_eq_sum fun l hl => by rw [hsupp l hl]; simp
    rw [← hext]
    have h := (Equiv.subLeft k).tsum_eq
      (f := fun j => (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖)
    simp only [Equiv.subLeft_apply] at h
    rw [← h]
    exact tsum_congr fun l => by rw [sub_sub_cancel]; ring
  have hswapB : (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
      ∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖) =
      ∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) *
        ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖ := by
    have h1 : ∀ k ∈ S, Summable fun j => (‖freq k‖ ^ m * ‖c k‖) *
        ((‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖) :=
      fun k _ => summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
    calc (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
          ∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖)
        = ∑ k ∈ S, ∑' j, (‖freq k‖ ^ m * ‖c k‖) *
            ((‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖) :=
          Finset.sum_congr rfl fun k _ => tsum_mul_left.symm
      _ = ∑' j, ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
            ((‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) * ‖c (k - j)‖) :=
          (Summable.tsum_finsetSum h1).symm
      _ = ∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) *
            ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖ := by
          refine tsum_congr fun j => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have heqB : (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
      ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) =
      ∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) *
        ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖ := by
    rw [← hswapB]
    exact Finset.sum_congr rfl fun k _ => by rw [hM1B k]
  have hDnnB : ∀ j, (0:ℝ) ≤ ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖ :=
    fun j => Finset.sum_nonneg fun k _ => by positivity
  have hT2csB : (∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) *
      ∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖) ≤
      Real.sqrt (∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) ^ 2) *
        Real.sqrt (∑' j, (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖) ^ 2) :=
    sp_tsum_mul_le (fun j => by positivity) hDnnB hybE hccB.1
  have hgd_eqB : (∑' j, (‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖)) ^ 2) = sob (m + 1) c := by
    have hdef : sob (m + 1) c = ∑' k, ‖freq k‖ ^ (2 * (m + 1)) * ‖c k‖ ^ 2 := rfl
    rw [hdef]
    refine tsum_congr fun j => ?_
    have e1 : ‖freq j‖ * (‖freq j‖ ^ m * ‖c j‖) = ‖freq j‖ ^ (m + 1) * ‖c j‖ := by
      rw [pow_succ]; ring
    rw [e1, sq_norm_pow_mul]
  have hsqD : Real.sqrt (∑' j, (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) * ‖c (k - j)‖) ^ 2) ≤
      Real.sqrt (C_K * ((sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) *
        (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) := by
    refine Real.sqrt_le_sqrt ?_
    refine hccB.2.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCK.le
    exact mul_le_mul hPzB' hPcB' hPcnn hintnn
  have hsqrtP : Real.sqrt (sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) =
      sob m c ^ ((1:ℝ)/16) * sob (m + 1) c ^ ((7:ℝ)/16) := by
    rw [Real.sqrt_eq_rpow,
      Real.mul_rpow (Real.rpow_nonneg hsm0 _) (Real.rpow_nonneg hsm10 _),
      ← Real.rpow_mul hsm0, ← Real.rpow_mul hsm10]
    norm_num
  have hsplits : Real.sqrt (sob (m + 1) c) * sob (m + 1) c ^ ((7:ℝ)/16) =
      sob (m + 1) c ^ ((15:ℝ)/16) := by
    rw [Real.sqrt_eq_rpow, show (15:ℝ)/16 = 1/2 + 7/16 by norm_num,
      Real.rpow_add' hsm10 (by norm_num)]
  have hT2b : (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
      ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) ≤
      (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
        (sob m c ^ ((1:ℝ)/16) * sob (m + 1) c ^ ((15:ℝ)/16)) := by
    rw [heqB]
    refine hT2csB.trans ?_
    rw [hgd_eqB]
    refine (mul_le_mul_of_nonneg_left hsqD (Real.sqrt_nonneg _)).trans ?_
    calc Real.sqrt (sob (m + 1) c) *
        Real.sqrt (C_K * ((sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) *
          (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))))
        = Real.sqrt (sob (m + 1) c) * (Real.sqrt C_K *
            (Real.sqrt (sob m c ^ ((1:ℝ)/8) * sob (m + 1) c ^ ((7:ℝ)/8)) *
              Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) := by
          rw [Real.sqrt_mul hCK.le, Real.sqrt_mul hintnn]
      _ = (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
            (sob m c ^ ((1:ℝ)/16) *
              (Real.sqrt (sob (m + 1) c) * sob (m + 1) c ^ ((7:ℝ)/16))) := by
          rw [hsqrtP]; ring
      _ = (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
            (sob m c ^ ((1:ℝ)/16) * sob (m + 1) c ^ ((15:ℝ)/16)) := by rw [hsplits]
      _ ≤ (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
            (sob m c ^ ((1:ℝ)/16) * sob (m + 1) c ^ ((15:ℝ)/16)) := le_rfl
  have h2T2b : 2 * 2 ^ (m - 1) *
      (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
        ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖))) ≤
      (1/16) * ((2 * 2 ^ (m - 1) *
            (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
          * (8 * ν / 15) ^ (-(15:ℝ))) * sob m c
        + ν / 2 * sob (m + 1) c := by
    have h2mnn : (0:ℝ) ≤ 2 * 2 ^ (m - 1) := by positivity
    have hyoungB := sp_young16 (B := 2 * 2 ^ (m - 1) *
        (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))))
      (lam := 8 * ν / 15) (by positivity) (by positivity) hsm0 hsm10
    calc 2 * 2 ^ (m - 1) *
        (∑ k ∈ S, (‖freq k‖ ^ m * ‖c k‖) *
          ∑ l ∈ S, ‖c l‖ * (‖freq (k - l)‖ * (‖freq (k - l)‖ ^ m * ‖c (k - l)‖)))
        ≤ 2 * 2 ^ (m - 1) *
            ((Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8))) *
              (sob m c ^ ((1:ℝ)/16) * sob (m + 1) c ^ ((15:ℝ)/16))) :=
          mul_le_mul_of_nonneg_left hT2b h2mnn
      _ = (2 * 2 ^ (m - 1) * (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) *
            (sob m c ^ ((1:ℝ)/16) * sob (m + 1) c ^ ((15:ℝ)/16)) := by ring
      _ ≤ (1/16) * ((2 * 2 ^ (m - 1) *
              (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
            * (8 * ν / 15) ^ (-(15:ℝ)) * sob m c)
            + (15/16) * ((8 * ν / 15) * sob (m + 1) c) := hyoungB
      _ = (1/16) * ((2 * 2 ^ (m - 1) *
              (Real.sqrt C_K * Real.sqrt (E ^ ((1:ℝ)/8) * Z ^ ((7:ℝ)/8)))) ^ (16:ℝ)
            * (8 * ν / 15) ^ (-(15:ℝ))) * sob m c
            + ν / 2 * sob (m + 1) c := by ring
  -- === final assembly ===
  refine hsumS.trans ?_
  linarith [h2T1, h2T2b, hsm0]

end TheoremB
