/-
# The Sobolev vocabulary (Tier 6, wave 1)

The graded spectral Sobolev mass `sob m c = Σ ‖k‖^(2m) ‖c k‖²` together with
the weight-generic machinery the higher-regularity ladder needs: public
weighted collapse/summability/derivative lemmas (the GalerkinTrap privates,
made weight-public), the weighted truncation and mode-wise-limit bounds,
the pow-arithmetic lift identities, the frequency triangle inequality and
its 2^(m-1) splitting corollary, the summability ladder down the scale, and
the weighted ℓ¹ export for the classical layer.

Junk-tsum discipline: every tsum statement carries the Summable certificate
it needs; on finite support, summability comes via the support lemmas.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.NSFull
import TheoremB.LimitHelpers

namespace TheoremB

open Set

/-! ## The graded Sobolev mass -/

/-- The spectral Sobolev mass of order `m`: `Σ ‖k‖^(2m) ‖c k‖²`. -/
noncomputable def sob (m : ℕ) (c : (Fin 3 → ℤ) → Vel) : ℝ :=
  ∑' k : Fin 3 → ℤ, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2

lemma sob_zero_eq_en (c : (Fin 3 → ℤ) → Vel) : sob 0 c = en c := by
  have h1 : sob 0 c = ∑' k, ‖freq k‖ ^ (2 * 0) * ‖c k‖ ^ 2 := rfl
  have h2 : en c = ∑' k, ‖c k‖ ^ 2 := rfl
  rw [h1, h2]
  exact tsum_congr fun k => by norm_num

lemma sob_one_eq_ens (c : (Fin 3 → ℤ) → Vel) : sob 1 c = ens c := by
  have h1 : sob 1 c = ∑' k, ‖freq k‖ ^ (2 * 1) * ‖c k‖ ^ 2 := rfl
  have h2 : ens c = ∑' k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 := rfl
  rw [h1, h2]

lemma sob_nonneg (m : ℕ) (c : (Fin 3 → ℤ) → Vel) : 0 ≤ sob m c := by
  have h : sob m c = ∑' k, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 := rfl
  rw [h]
  exact tsum_nonneg fun k => by positivity

/-! ## Weight-generic collapse, summability, and derivative lemmas
(public versions of the GalerkinTrap privates) -/

section WeightedClones

variable {V : Type*} [NormedAddCommGroup V]

/-- Weighted spectral sums collapse to finite sums on finitely supported fields. -/
lemma weighted_tsum_eq_sum (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → V} (hsupp : ∀ k, k ∉ S → c k = 0) :
    ∑' k, w k * ‖c k‖ ^ 2 = ∑ k ∈ S, w k * ‖c k‖ ^ 2 :=
  tsum_eq_sum fun k hk => by rw [hsupp k hk]; simp

/-- Weighted spectral sums over finitely supported fields are summable. -/
lemma summable_weighted_of_support (w : (Fin 3 → ℤ) → ℝ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → V} (hsupp : ∀ k, k ∉ S → c k = 0) :
    Summable fun k => w k * ‖c k‖ ^ 2 :=
  summable_of_ne_finset_zero (s := S) fun k hk => by rw [hsupp k hk]; simp

variable [InnerProductSpace ℝ V]

/-- Coefficient-wise product rule for a weighted Sobolev-type sum along a flow. -/
lemma hasDerivAt_weighted_finset_sum_sq (w : (Fin 3 → ℤ) → ℝ) (S : Finset (Fin 3 → ℤ))
    {c c' : ℝ → (Fin 3 → ℤ) → V} {t : ℝ}
    (hderiv : ∀ k, HasDerivAt (fun s => c s k) (c' t k) t) :
    HasDerivAt (fun s => ∑ k ∈ S, w k * ‖c s k‖ ^ 2)
      (∑ k ∈ S, w k * (2 * inner ℝ (c' t k) (c t k))) t := by
  have hterm : ∀ k ∈ S, HasDerivAt (fun s => w k * ‖c s k‖ ^ 2)
      (w k * (2 * inner ℝ (c' t k) (c t k))) t := by
    intro k _
    have h1 : HasDerivAt (fun s => inner ℝ (c s k) (c s k))
        (inner ℝ (c t k) (c' t k) + inner ℝ (c' t k) (c t k)) t :=
      (hderiv k).inner ℝ (hderiv k)
    have h2 : (fun s => ‖c s k‖ ^ 2) = fun s => inner ℝ (c s k) (c s k) := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (c t k) (c' t k) + inner ℝ (c' t k) (c t k) =
        2 * inner ℝ (c' t k) (c t k) := by
      rw [real_inner_comm (c t k) (c' t k)]; ring
    have h3 : HasDerivAt (fun s => ‖c s k‖ ^ 2)
        (2 * inner ℝ (c' t k) (c t k)) t := by
      rw [h2, ← h4]; exact h1
    exact h3.const_mul (w k)
  have h := HasDerivAt.sum hterm
  have heq : (∑ i ∈ S, fun s => w i * ‖c s i‖ ^ 2) =
      fun s => ∑ k ∈ S, w k * ‖c s k‖ ^ 2 := by
    funext s
    simp [Finset.sum_apply]
  rwa [heq] at h

end WeightedClones

/-! ## Truncation only decreases weighted mass -/

/-- Truncation only decreases any nonnegatively weighted spectral mass. -/
lemma weighted_truncate_le {w : (Fin 3 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k)
    {c : (Fin 3 → ℤ) → Vel}
    (hsum : Summable fun l => w l * ‖c l‖ ^ 2) (S : Finset (Fin 3 → ℤ)) :
    (∑' l, w l * ‖truncate S c l‖ ^ 2) ≤ ∑' l, w l * ‖c l‖ ^ 2 := by
  have hle : ∀ l, w l * ‖truncate S c l‖ ^ 2 ≤ w l * ‖c l‖ ^ 2 := by
    intro l
    have h1 := truncate_norm_le S c l
    have h2 : ‖truncate S c l‖ ^ 2 ≤ ‖c l‖ ^ 2 := by
      nlinarith [norm_nonneg (truncate S c l)]
    exact mul_le_mul_of_nonneg_left h2 (hw l)
  have hsum' : Summable fun l => w l * ‖truncate S c l‖ ^ 2 :=
    hsum.of_nonneg_of_le (fun l => mul_nonneg (hw l) (sq_nonneg _)) hle
  exact hsum'.tsum_le_tsum hle hsum

/-- Truncation only decreases the Sobolev mass at every order. -/
lemma sob_truncate_le {m : ℕ} {c : (Fin 3 → ℤ) → Vel}
    (h : Summable fun k => ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2) (S : Finset (Fin 3 → ℤ)) :
    sob m (truncate S c) ≤ sob m c := by
  have h1 : sob m (truncate S c) = ∑' k, ‖freq k‖ ^ (2 * m) * ‖truncate S c k‖ ^ 2 := rfl
  have h2 : sob m c = ∑' k, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 := rfl
  rw [h1, h2]
  exact weighted_truncate_le (fun k => by positivity) h S

/-! ## Weighted bounds survive the mode-wise limit -/

/-- Weighted mass bound and summability in the limit, from uniform finite-sum
bounds, for any nonnegative weight. -/
lemma weighted_limit_le {w : (Fin 3 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) {E : ℝ}
    {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hEn : ∀ n (F : Finset (Fin 3 → ℤ)), ∑ l ∈ F, w l * ‖c n l‖ ^ 2 ≤ E)
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l))) :
    (∑' l, w l * ‖g l‖ ^ 2) ≤ E ∧ Summable fun l => w l * ‖g l‖ ^ 2 := by
  have hF : ∀ F : Finset (Fin 3 → ℤ), ∑ l ∈ F, w l * ‖g l‖ ^ 2 ≤ E := by
    intro F
    have htend : Filter.Tendsto (fun n => ∑ l ∈ F, w l * ‖c n l‖ ^ 2) Filter.atTop
        (nhds (∑ l ∈ F, w l * ‖g l‖ ^ 2)) := by
      refine tendsto_finsetSum F fun l _ => ?_
      exact Filter.Tendsto.const_mul _ (((hpt l).norm).pow 2)
    exact le_of_tendsto' htend fun n => hEn n F
  exact ⟨Real.tsum_le_of_sum_le (fun l => mul_nonneg (hw l) (sq_nonneg _)) hF,
    summable_of_sum_le (fun l => mul_nonneg (hw l) (sq_nonneg _)) hF⟩

/-! ## Lift identities (pure pow arithmetic) -/

lemma sq_norm_pow_mul (k : Fin 3 → ℤ) (x : ℝ) (m : ℕ) :
    (‖freq k‖ ^ m * x) ^ 2 = ‖freq k‖ ^ (2 * m) * x ^ 2 := by
  rw [mul_pow, ← pow_mul, mul_comm m 2]

lemma norm_sq_mul_pow (k : Fin 3 → ℤ) (m : ℕ) :
    ‖freq k‖ ^ 2 * ‖freq k‖ ^ (2 * m) = ‖freq k‖ ^ (2 * (m + 1)) := by
  rw [← pow_add]
  congr 1
  omega

/-! ## The frequency triangle inequality and the 2^(m-1) split -/

lemma freq_triangle (k l : Fin 3 → ℤ) : ‖freq k‖ ≤ ‖freq l‖ + ‖freq (k - l)‖ := by
  rw [freq_sub]
  have h : freq k = freq l + (freq k - freq l) := by abel
  calc ‖freq k‖ = ‖freq l + (freq k - freq l)‖ := by rw [← h]
    _ ≤ ‖freq l‖ + ‖freq k - freq l‖ := norm_add_le _ _

/-- The two-power splitting inequality `(a+b)^m ≤ 2^(m-1)(a^m + b^m)`. -/
lemma two_pow_split {a b : ℝ} {m : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hm : 1 ≤ m) :
    (a + b) ^ m ≤ 2 ^ (m - 1) * (a ^ m + b ^ m) :=
  add_pow_le ha hb m

/-- Splitting a frequency power across a convolution pair. -/
lemma norm_freq_pow_split (k l : Fin 3 → ℤ) {m : ℕ} (hm : 1 ≤ m) :
    ‖freq k‖ ^ m ≤ 2 ^ (m - 1) * (‖freq l‖ ^ m + ‖freq (k - l)‖ ^ m) := by
  calc ‖freq k‖ ^ m ≤ (‖freq l‖ + ‖freq (k - l)‖) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) (freq_triangle k l) m
    _ ≤ 2 ^ (m - 1) * (‖freq l‖ ^ m + ‖freq (k - l)‖ ^ m) :=
        two_pow_split (norm_nonneg _) (norm_nonneg _) hm

/-! ## The summability ladder down the Sobolev scale -/

/-- Level-`m` Sobolev summability controls every lower level (mean-zero fields). -/
lemma sob_summable_of_le {j m : ℕ} (hjm : j ≤ m) {c : (Fin 3 → ℤ) → Vel}
    (hc0 : c 0 = 0)
    (hm : Summable fun k => ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2) :
    Summable fun k => ‖freq k‖ ^ (2 * j) * ‖c k‖ ^ 2 := by
  refine hm.of_nonneg_of_le (fun k => by positivity) fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hc0]
  · have h1 := one_le_norm_freq hk
    have hpow : ‖freq k‖ ^ (2 * j) ≤ ‖freq k‖ ^ (2 * m) :=
      pow_le_pow_right₀ h1 (by omega)
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)

/-! ## The weighted ℓ¹ export for the classical layer -/

/-- Two orders of extra Sobolev regularity buy a weighted ℓ¹ bound:
`Σ ‖k‖^(2(p+2)) ‖c k‖²` summable forces `Σ ‖k‖^p ‖c k‖` summable
(mean-zero fields).  AM-GM against the summable lattice weight `(‖k‖⁴)⁻¹`. -/
lemma summable_weighted_norm {p : ℕ} {c : (Fin 3 → ℤ) → Vel} (hc0 : c 0 = 0)
    (h : Summable fun k => ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) :
    Summable fun k => ‖freq k‖ ^ p * ‖c k‖ := by
  refine (summable_inv_freq_pow_four.add h).of_nonneg_of_le
    (fun k => by positivity) (fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [hc0, norm_zero, mul_zero]
    positivity
  · have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have key : ‖freq k‖ ^ p * ‖c k‖ =
        (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ (p + 2) * ‖c k‖) := by
      rw [pow_add]
      field_simp
    have e1 : ((‖freq k‖ ^ 2)⁻¹) ^ 2 = (‖freq k‖ ^ 4)⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have e2 := sq_norm_pow_mul k ‖c k‖ (p + 2)
    calc ‖freq k‖ ^ p * ‖c k‖
        = (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ (p + 2) * ‖c k‖) := key
      _ ≤ (((‖freq k‖ ^ 2)⁻¹) ^ 2 + (‖freq k‖ ^ (p + 2) * ‖c k‖) ^ 2) / 2 := by
          nlinarith [sq_nonneg ((‖freq k‖ ^ 2)⁻¹ - ‖freq k‖ ^ (p + 2) * ‖c k‖)]
      _ = ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
          rw [e1, e2]
      _ ≤ (‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2 := by
          have h1 : (0 : ℝ) ≤ (‖freq k‖ ^ 4)⁻¹ := by positivity
          have h2 : (0 : ℝ) ≤ ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2 := by positivity
          linarith

end TheoremB
