/-
# Limit passage core (Tier 3, wave 4)

The epsilon/3 Tannery argument with uniform enstrophy tails: mode-wise
convergence of budgeted fields passes through the full convection `convFull`
(a plain dominated-convergence majorant does not exist — the natural
sup-majorant fails because `Σ 1/|l|²` diverges over `ℤ³`). Plus the FTC
wrappers: ODE to integral equation on the window, limits under the interval
integral via uniform convergence, and integral equation back to `HasDerivAt`
at interior times.
-/
import TheoremB.NSFull
import TheoremB.ModeExtraction
import TheoremB.GalerkinFlow

namespace TheoremB

open Set

/-! ### Fleet-B private helpers: continuity of the convection term in the coefficients -/

private lemma flB_dotR_continuous (r : EuclideanSpace ℝ (Fin 3)) :
    Continuous fun v : Vel => dotR v r := by
  have h : (fun v : Vel => dotR v r) = fun v => inner ℂ (castCV r) v :=
    funext fun v => dotR_eq_inner v r
  rw [h]
  exact continuous_const.inner continuous_id

private lemma flB_term_tendsto {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l)))
    (k l : Fin 3 → ℤ) :
    Filter.Tendsto (fun n => (Complex.I * dotR (c n l) (freq (k - l))) • c n (k - l))
      Filter.atTop
      (nhds ((Complex.I * dotR (g l) (freq (k - l))) • g (k - l))) := by
  have hdot : Filter.Tendsto (fun n => dotR (c n l) (freq (k - l))) Filter.atTop
      (nhds (dotR (g l) (freq (k - l)))) :=
    ((flB_dotR_continuous (freq (k - l))).tendsto (g l)).comp (hpt l)
  exact (tendsto_const_nhds.mul hdot).smul (hpt (k - l))

/-- The full-convection term family is (vector-valued) summable under finite
energy and enstrophy. -/
private lemma flB_summable_T {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    Summable fun l => (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) := by
  have hmaj := summable_convMaj hE hZ k
  have hterm : ∀ l, ‖(Complex.I * dotR (c l) (freq (k - l))) • c (k - l)‖ ≤
      ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by
    intro l
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    calc ‖dotR (c l) (freq (k - l))‖ * ‖c (k - l)‖
        ≤ (‖freq (k - l)‖ * ‖c l‖) * ‖c (k - l)‖ :=
          mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
      _ = ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by ring
  exact Summable.of_norm (hmaj.of_nonneg_of_le (fun l => norm_nonneg _) hterm)

/-- Cauchy-Schwarz tail bound for the convection majorant over any set of
frequencies beyond `M`: the tail is at most `√Z/M · √Z`. Uniform in the field —
only the energy/enstrophy bounds enter. -/
private lemma flB_tail_maj_le {c : (Fin 3 → ℤ) → Vel} {Z M : ℝ} (hZ0 : 0 ≤ Z) (hM : 0 < M)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (hZle : ens c ≤ Z) (k : Fin 3 → ℤ)
    {s : Set (Fin 3 → ℤ)} (hs : ∀ l ∈ s, M < ‖freq l‖) :
    (∑' l : s, ‖c l.val‖ * (‖freq (k - l.val)‖ * ‖c (k - l.val)‖)) ≤
      Real.sqrt Z / M * Real.sqrt Z := by
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hZk : Summable fun l => ‖freq (k - l)‖ ^ 2 * ‖c (k - l)‖ ^ 2 := by
    have h := ((Equiv.subLeft k).summable_iff
      (f := fun m => ‖freq m‖ ^ 2 * ‖c m‖ ^ 2)).mpr hZ
    exact h.congr fun l => by simp [Function.comp]
  have hf2' : Summable fun l : s => ‖c l.val‖ ^ 2 := hE.subtype _
  have hf2 : Summable fun l : s => ‖c l.val‖ ^ (2 : ℝ) := hf2'.congr fun l => h2 _
  have hg2' : Summable fun l : s => ‖freq (k - l.val)‖ ^ 2 * ‖c (k - l.val)‖ ^ 2 :=
    hZk.subtype _
  have hg2 : Summable fun l : s => (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) ^ (2 : ℝ) :=
    hg2'.congr fun l => by rw [← h2]; ring
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun l : s => ‖c l.val‖)
    (g := fun l : s => ‖freq (k - l.val)‖ * ‖c (k - l.val)‖)
    (fun l => norm_nonneg _) (fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hf2 hg2
  have hA : (∑' l : s, ‖c l.val‖ ^ (2 : ℝ)) = ∑' l : s, ‖c l.val‖ ^ 2 :=
    tsum_congr fun l => (h2 _).symm
  rw [hA] at cs
  have hZs : Summable fun l : s => ‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2 := hZ.subtype _
  have hterm : ∀ l : s, ‖c l.val‖ ^ 2 ≤ M⁻¹ ^ 2 * (‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2) := by
    intro l
    have h1 : M ^ 2 ≤ ‖freq l.val‖ ^ 2 := by nlinarith [hs l.val l.property, hM]
    have hp : (0 : ℝ) < M ^ 2 := by positivity
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hp]
    nlinarith [sq_nonneg ‖c l.val‖]
  have htail : (∑' l : s, ‖c l.val‖ ^ 2) ≤ Z / M ^ 2 := by
    calc (∑' l : s, ‖c l.val‖ ^ 2)
        ≤ ∑' l : s, M⁻¹ ^ 2 * (‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2) :=
          hf2'.tsum_le_tsum hterm (hZs.mul_left (M⁻¹ ^ 2))
      _ = M⁻¹ ^ 2 * ∑' l : s, ‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2 := tsum_mul_left
      _ ≤ M⁻¹ ^ 2 * ens c := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hZ.tsum_subtype_le _ _ (fun l => by positivity)
      _ ≤ M⁻¹ ^ 2 * Z := mul_le_mul_of_nonneg_left hZle (by positivity)
      _ = Z / M ^ 2 := by rw [inv_pow, ← div_eq_inv_mul]
  have hB : (∑' l : s, (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) ^ (2 : ℝ)) ≤ Z := by
    have e1 : (∑' l : s, (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) ^ (2 : ℝ)) =
        ∑' l : s, ‖freq (k - l.val)‖ ^ 2 * ‖c (k - l.val)‖ ^ 2 :=
      tsum_congr fun l => by rw [← h2]; ring
    rw [e1]
    calc (∑' l : s, ‖freq (k - l.val)‖ ^ 2 * ‖c (k - l.val)‖ ^ 2)
        ≤ ∑' l, ‖freq (k - l)‖ ^ 2 * ‖c (k - l)‖ ^ 2 :=
          hZk.tsum_subtype_le _ _ (fun l => by positivity)
      _ = ens c := by
          have h := (Equiv.subLeft k).tsum_eq (f := fun m => ‖freq m‖ ^ 2 * ‖c m‖ ^ 2)
          simp only [Equiv.subLeft_apply] at h
          exact h
      _ ≤ Z := hZle
  calc (∑' l : s, ‖c l.val‖ * (‖freq (k - l.val)‖ * ‖c (k - l.val)‖))
      ≤ (∑' l : s, ‖c l.val‖ ^ 2) ^ (1 / (2:ℝ)) *
        (∑' l : s, (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) ^ (2:ℝ)) ^ (1 / (2:ℝ)) := cs
    _ = Real.sqrt (∑' l : s, ‖c l.val‖ ^ 2) *
        Real.sqrt (∑' l : s, (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) ^ (2:ℝ)) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (Z / M ^ 2) * Real.sqrt Z :=
        mul_le_mul (Real.sqrt_le_sqrt htail) (Real.sqrt_le_sqrt hB)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt Z / M * Real.sqrt Z := by
        rw [Real.sqrt_div hZ0, Real.sqrt_sq hM.le]

/-- Norm of the convection tail over frequencies beyond `M`: at most `Z/M`,
uniformly in the coefficient field. -/
private lemma flB_tail_norm {c : (Fin 3 → ℤ) → Vel} {Z M : ℝ} (hZ0 : 0 ≤ Z) (hM : 0 < M)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (hZle : ens c ≤ Z) (k : Fin 3 → ℤ)
    {s : Set (Fin 3 → ℤ)} (hs : ∀ l ∈ s, M < ‖freq l‖) :
    ‖∑' l : s, (Complex.I * dotR (c l.val) (freq (k - l.val))) • c (k - l.val)‖ ≤ Z / M := by
  have hmaj : Summable fun l : s => ‖c l.val‖ * (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) :=
    (summable_convMaj hE hZ k).subtype _
  have hterm : ∀ l : s, ‖(Complex.I * dotR (c l.val) (freq (k - l.val))) • c (k - l.val)‖ ≤
      ‖c l.val‖ * (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) := by
    intro l
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    calc ‖dotR (c l.val) (freq (k - l.val))‖ * ‖c (k - l.val)‖
        ≤ (‖freq (k - l.val)‖ * ‖c l.val‖) * ‖c (k - l.val)‖ :=
          mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
      _ = ‖c l.val‖ * (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) := by ring
  have hnorm : Summable fun l : s =>
      ‖(Complex.I * dotR (c l.val) (freq (k - l.val))) • c (k - l.val)‖ :=
    hmaj.of_nonneg_of_le (fun l => norm_nonneg _) hterm
  calc ‖∑' l : s, (Complex.I * dotR (c l.val) (freq (k - l.val))) • c (k - l.val)‖
      ≤ ∑' l : s, ‖(Complex.I * dotR (c l.val) (freq (k - l.val))) • c (k - l.val)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' l : s, ‖c l.val‖ * (‖freq (k - l.val)‖ * ‖c (k - l.val)‖) :=
        hnorm.tsum_le_tsum hterm hmaj
    _ ≤ Real.sqrt Z / M * Real.sqrt Z := flB_tail_maj_le hZ0 hM hE hZ hZle k hs
    _ = Z / M := by rw [div_mul_eq_mul_div, Real.mul_self_sqrt hZ0]

/-- Difference of full convections of two fields: bounded by the finite-box
difference plus two uniform tails. -/
private lemma flB_convFull_diff_le {a b : (Fin 3 → ℤ) → Vel} {Z M : ℝ}
    (hZ0 : 0 ≤ Z) (hM : 0 < M)
    (hEa : Summable fun l => ‖a l‖ ^ 2) (hZa : Summable fun l => ‖freq l‖ ^ 2 * ‖a l‖ ^ 2)
    (hEb : Summable fun l => ‖b l‖ ^ 2) (hZb : Summable fun l => ‖freq l‖ ^ 2 * ‖b l‖ ^ 2)
    (hZa' : ens a ≤ Z) (hZb' : ens b ≤ Z) (k : Fin 3 → ℤ)
    {F : Finset (Fin 3 → ℤ)} (hsF : ∀ l ∈ (↑F : Set (Fin 3 → ℤ))ᶜ, M < ‖freq l‖) :
    ‖convFull a k - convFull b k‖ ≤
      ‖∑ l ∈ F, ((Complex.I * dotR (a l) (freq (k - l))) • a (k - l) -
        (Complex.I * dotR (b l) (freq (k - l))) • b (k - l))‖ + (Z / M + Z / M) := by
  have hTa : Summable fun l => (Complex.I * dotR (a l) (freq (k - l))) • a (k - l) :=
    flB_summable_T hEa hZa k
  have hTb : Summable fun l => (Complex.I * dotR (b l) (freq (k - l))) • b (k - l) :=
    flB_summable_T hEb hZb k
  have hTsub : Summable fun l =>
      (Complex.I * dotR (a l) (freq (k - l))) • a (k - l) -
      (Complex.I * dotR (b l) (freq (k - l))) • b (k - l) := hTa.sub hTb
  have hsplit := hTsub.sum_add_tsum_compl (s := F)
  have e1 : convFull a k - convFull b k =
      -(∑' l, ((Complex.I * dotR (a l) (freq (k - l))) • a (k - l) -
        (Complex.I * dotR (b l) (freq (k - l))) • b (k - l))) := by
    rw [convFull, convFull, hTa.tsum_sub hTb]
    abel
  have htail_eq : (∑' (l : ↑((↑F : Set (Fin 3 → ℤ))ᶜ)),
        ((Complex.I * dotR (a l.val) (freq (k - l.val))) • a (k - l.val) -
         (Complex.I * dotR (b l.val) (freq (k - l.val))) • b (k - l.val))) =
      (∑' (l : ↑((↑F : Set (Fin 3 → ℤ))ᶜ)),
        (Complex.I * dotR (a l.val) (freq (k - l.val))) • a (k - l.val)) -
      ∑' (l : ↑((↑F : Set (Fin 3 → ℤ))ᶜ)),
        (Complex.I * dotR (b l.val) (freq (k - l.val))) • b (k - l.val) :=
    (hTa.subtype _).tsum_sub (hTb.subtype _)
  have htail_le : ‖∑' (l : ↑((↑F : Set (Fin 3 → ℤ))ᶜ)),
      ((Complex.I * dotR (a l.val) (freq (k - l.val))) • a (k - l.val) -
       (Complex.I * dotR (b l.val) (freq (k - l.val))) • b (k - l.val))‖ ≤
      Z / M + Z / M := by
    rw [htail_eq]
    exact (norm_sub_le _ _).trans
      (add_le_add (flB_tail_norm hZ0 hM hEa hZa hZa' k hsF)
        (flB_tail_norm hZ0 hM hEb hZb hZb' k hsF))
  rw [e1, norm_neg, ← hsplit]
  exact (norm_add_le _ _).trans (add_le_add_right htail_le _)

/-! ### The limit passage for the convection -/

/-- **Tannery with uniform tails**: if a sequence of coefficient fields has
uniformly bounded energy and enstrophy (as finite-sum bounds) and converges
mode-wise, then the full convection converges mode-wise to that of the limit. -/
theorem tendsto_convFull_of_modes {E Z : ℝ} (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hEn : ∀ n (F : Finset (Fin 3 → ℤ)), ∑ l ∈ F, ‖c n l‖ ^ 2 ≤ E)
    (hZn : ∀ n (F : Finset (Fin 3 → ℤ)), ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c n l‖ ^ 2 ≤ Z)
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l))) (k : Fin 3 → ℤ) :
    Filter.Tendsto (fun n => convFull (c n) k) Filter.atTop (nhds (convFull g k)) := by
  have hEsum : ∀ n, Summable fun l => ‖c n l‖ ^ 2 := fun n =>
    summable_of_sum_le (fun l => sq_nonneg _) (hEn n)
  have hZsum : ∀ n, Summable fun l => ‖freq l‖ ^ 2 * ‖c n l‖ ^ 2 := fun n =>
    summable_of_sum_le (fun l => by positivity) (hZn n)
  have hgE : ∀ F : Finset (Fin 3 → ℤ), ∑ l ∈ F, ‖g l‖ ^ 2 ≤ E := by
    intro F
    have ht := tendsto_finsetSum (f := fun l n => ‖c n l‖ ^ 2)
      (a := fun l => ‖g l‖ ^ 2) F (fun l _ => ((hpt l).norm).pow 2)
    exact le_of_tendsto' ht fun n => hEn n F
  have hgZ : ∀ F : Finset (Fin 3 → ℤ), ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖g l‖ ^ 2 ≤ Z := by
    intro F
    have ht := tendsto_finsetSum (f := fun l n => ‖freq l‖ ^ 2 * ‖c n l‖ ^ 2)
      (a := fun l => ‖freq l‖ ^ 2 * ‖g l‖ ^ 2) F
      (fun l _ => tendsto_const_nhds.mul (((hpt l).norm).pow 2))
    exact le_of_tendsto' ht fun n => hZn n F
  have hgEsum : Summable fun l => ‖g l‖ ^ 2 :=
    summable_of_sum_le (fun l => sq_nonneg _) hgE
  have hgZsum : Summable fun l => ‖freq l‖ ^ 2 * ‖g l‖ ^ 2 :=
    summable_of_sum_le (fun l => by positivity) hgZ
  have hensn : ∀ n, ens (c n) ≤ Z := fun n =>
    Real.tsum_le_of_sum_le (fun l => by positivity) (hZn n)
  have hensg : ens g ≤ Z :=
    Real.tsum_le_of_sum_le (fun l => by positivity) hgZ
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hMpos, hMtail⟩ : ∃ M : ℝ, 0 < M ∧ Z / M + Z / M ≤ ε / 2 := by
    have h4 : 0 ≤ 4 * Z / ε := div_nonneg (by linarith) hε.le
    have hMp : (0 : ℝ) < 4 * Z / ε + 1 := by linarith
    refine ⟨4 * Z / ε + 1, hMp, ?_⟩
    rw [← add_div, div_le_iff₀ hMp]
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hexp : ε / 2 * (4 * Z / ε + 1) = 2 * Z + ε / 2 := by
      field_simp
      ring
    rw [hexp]
    linarith
  obtain ⟨F, hsF⟩ : ∃ F : Finset (Fin 3 → ℤ),
      ∀ l ∈ (↑F : Set (Fin 3 → ℤ))ᶜ, M < ‖freq l‖ := by
    refine ⟨(finite_freq_le M).toFinset, fun l hl => ?_⟩
    simp only [Set.mem_compl_iff, Finset.mem_coe, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le] at hl
    exact hl
  have hfin : Filter.Tendsto (fun n => ∑ l ∈ F,
      ((Complex.I * dotR (c n l) (freq (k - l))) • c n (k - l) -
        (Complex.I * dotR (g l) (freq (k - l))) • g (k - l)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum
      (f := fun l n => (Complex.I * dotR (c n l) (freq (k - l))) • c n (k - l) -
        (Complex.I * dotR (g l) (freq (k - l))) • g (k - l))
      (a := fun l => (Complex.I * dotR (g l) (freq (k - l))) • g (k - l) -
        (Complex.I * dotR (g l) (freq (k - l))) • g (k - l)) F
      (fun l _ => (flB_term_tendsto hpt k l).sub tendsto_const_nhds)
    simpa using h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hfin (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hdist := hN n hn
  rw [dist_zero_right] at hdist
  rw [dist_eq_norm]
  have hbound := flB_convFull_diff_le hZ0 hMpos (hEsum n) (hZsum n) hgEsum hgZsum
    (hensn n) hensg k hsF
  calc ‖convFull (c n) k - convFull g k‖
      ≤ ‖∑ l ∈ F, ((Complex.I * dotR (c n l) (freq (k - l))) • c n (k - l) -
          (Complex.I * dotR (g l) (freq (k - l))) • g (k - l))‖ + (Z / M + Z / M) := hbound
    _ < ε / 2 + (Z / M + Z / M) := add_lt_add_left hdist _
    _ ≤ ε / 2 + ε / 2 := add_le_add_right hMtail _
    _ = ε := add_halves ε

/-! ### The two directions of the fundamental theorem of calculus on the window -/

/-- FTC on `[0,T]`: a `Vel`-valued function with continuous derivative on the
window is the integral of that derivative. -/
theorem integral_eq_of_hasDerivAt_Icc {f : ℝ → Vel} {f' : ℝ → Vel} {T : ℝ} (hT : 0 ≤ T)
    (hderiv : ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt f (f' t) t)
    (hcont : ContinuousOn f' (Set.Icc (0:ℝ) T)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t = f 0 + ∫ s in (0:ℝ)..t, f' s := by
  intro t ht
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc (0:ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) t, HasDerivAt f (f' s) s := by
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    exact hderiv s (hsub hs)
  have hint : IntervalIntegrable f' MeasureTheory.volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hcont.mono hsub)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [h]
  abel

/-- Converse FTC on the open window: a function given by a constant plus the
integral of a continuous integrand differentiates back to the integrand. -/
theorem hasDerivAt_of_integral_eq {f g : ℝ → Vel} {T : ℝ}
    (hg : ContinuousOn g (Set.Icc (0:ℝ) T))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) T, f t = f 0 + ∫ s in (0:ℝ)..t, g s) :
    ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt f (g t) t := by
  intro t ht
  have hint : IntervalIntegrable g MeasureTheory.volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1.le
      (hg.mono (Set.Icc_subset_Icc le_rfl ht.2.le))
  have hmeas : StronglyMeasurableAtFilter g (nhds t) MeasureTheory.volume :=
    (hg.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hct : ContinuousAt g t := hg.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hF : HasDerivAt (fun u => f 0 + ∫ s in (0:ℝ)..u, g s) (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right hint hmeas hct).const_add (f 0)
  have heq : f =ᶠ[nhds t] fun u => f 0 + ∫ s in (0:ℝ)..u, g s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hf s (Set.Ioo_subset_Icc_self hs)
  exact hF.congr_of_eventuallyEq heq

/-- Uniform convergence on the window passes through the interval integral. -/
theorem tendsto_intervalIntegral_of_tendstoUniformlyOn {F : ℕ → ℝ → Vel} {G : ℝ → Vel}
    {T t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T)
    (hu : TendstoUniformlyOn F G Filter.atTop (Set.Icc (0:ℝ) T))
    (hFc : ∀ n, ContinuousOn (F n) (Set.Icc (0:ℝ) T)) :
    Filter.Tendsto (fun n => ∫ s in (0:ℝ)..t, F n s) Filter.atTop
      (nhds (∫ s in (0:ℝ)..t, G s)) := by
  have hsub : Set.uIcc (0:ℝ) t ⊆ Set.Icc (0:ℝ) T := by
    rw [Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc le_rfl ht.2
  exact (hu.mono hsub).tendsto_intervalIntegral_of_continuousOn
    (Filter.Eventually.of_forall fun n => (hFc n).mono hsub)

end TheoremB
