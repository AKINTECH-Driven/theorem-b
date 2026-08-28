/-
# Uniform convection convergence and continuity (Tier 3, FLEET-C)

The epsilon/3 tail argument made uniform in time: mode-wise uniform
convergence of budgeted fields passes through `convFull` uniformly on the
window, and the full convection of a mode-continuous budgeted field is
continuous — the two facts the FTC step of the limit passage consumes.
-/
import TheoremB.LimitHelpers

namespace TheoremB

open Set

/-! ### Fleet-C private helpers (reproducing FLEET-B's flB_* recipe) -/

private lemma flc_dotR_continuous (r : EuclideanSpace ℝ (Fin 3)) :
    Continuous fun v : Vel => dotR v r := by
  have h : (fun v : Vel => dotR v r) = fun v => inner ℂ (castCV r) v :=
    funext fun v => dotR_eq_inner v r
  rw [h]
  exact continuous_const.inner continuous_id

/-- The full-convection term family is (vector-valued) summable under finite
energy and enstrophy. -/
private lemma flc_summable_T {c : (Fin 3 → ℤ) → Vel}
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
private lemma flc_tail_maj_le {c : (Fin 3 → ℤ) → Vel} {Z M : ℝ} (hZ0 : 0 ≤ Z) (hM : 0 < M)
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
private lemma flc_tail_norm {c : (Fin 3 → ℤ) → Vel} {Z M : ℝ} (hZ0 : 0 ≤ Z) (hM : 0 < M)
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
    _ ≤ Real.sqrt Z / M * Real.sqrt Z := flc_tail_maj_le hZ0 hM hE hZ hZle k hs
    _ = Z / M := by rw [div_mul_eq_mul_div, Real.mul_self_sqrt hZ0]

/-- Difference of full convections of two fields: bounded by the finite-box
difference plus two uniform tails. -/
private lemma flc_convFull_diff_le {a b : (Fin 3 → ℤ) → Vel} {Z M : ℝ}
    (hZ0 : 0 ≤ Z) (hM : 0 < M)
    (hEa : Summable fun l => ‖a l‖ ^ 2) (hZa : Summable fun l => ‖freq l‖ ^ 2 * ‖a l‖ ^ 2)
    (hEb : Summable fun l => ‖b l‖ ^ 2) (hZb : Summable fun l => ‖freq l‖ ^ 2 * ‖b l‖ ^ 2)
    (hZa' : ens a ≤ Z) (hZb' : ens b ≤ Z) (k : Fin 3 → ℤ)
    {F : Finset (Fin 3 → ℤ)} (hsF : ∀ l ∈ (↑F : Set (Fin 3 → ℤ))ᶜ, M < ‖freq l‖) :
    ‖convFull a k - convFull b k‖ ≤
      ‖∑ l ∈ F, ((Complex.I * dotR (a l) (freq (k - l))) • a (k - l) -
        (Complex.I * dotR (b l) (freq (k - l))) • b (k - l))‖ + (Z / M + Z / M) := by
  have hTa : Summable fun l => (Complex.I * dotR (a l) (freq (k - l))) • a (k - l) :=
    flc_summable_T hEa hZa k
  have hTb : Summable fun l => (Complex.I * dotR (b l) (freq (k - l))) • b (k - l) :=
    flc_summable_T hEb hZb k
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
      (add_le_add (flc_tail_norm hZ0 hM hEa hZa hZa' k hsF)
        (flc_tail_norm hZ0 hM hEb hZb hZb' k hsF))
  rw [e1, norm_neg, ← hsplit]
  exact (norm_add_le _ _).trans (add_le_add_right htail_le _)

/-- Single-mode bound from the finite-sum energy bound (take `F = {l}`). -/
private lemma flc_mode_le {a : (Fin 3 → ℤ) → Vel} {E : ℝ}
    (hE : ∀ F : Finset (Fin 3 → ℤ), ∑ l ∈ F, ‖a l‖ ^ 2 ≤ E) (l : Fin 3 → ℤ) :
    ‖a l‖ ≤ Real.sqrt E := by
  have h := hE {l}
  rw [Finset.sum_singleton] at h
  calc ‖a l‖ = Real.sqrt (‖a l‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt E := Real.sqrt_le_sqrt h

/-- Telescoped add/sub bound for the difference of two convection summands:
`a•x − b•y = (a−b)•x + b•(x−y)` with `dotR` linear in its vector slot. -/
private lemma flc_term_diff_le (x y u v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    ‖(Complex.I * dotR x r) • u - (Complex.I * dotR y r) • v‖ ≤
      ‖r‖ * ‖x - y‖ * ‖u‖ + ‖r‖ * ‖y‖ * ‖u - v‖ := by
  have hxy : dotR (x - y) r = dotR x r - dotR y r := by
    rw [dotR_eq_inner, dotR_eq_inner, dotR_eq_inner, inner_sub_right]
  have hsplit : (Complex.I * dotR x r) • u - (Complex.I * dotR y r) • v =
      (Complex.I * dotR (x - y) r) • u + (Complex.I * dotR y r) • (u - v) := by
    rw [hxy, mul_sub, sub_smul, smul_sub]
    abel
  rw [hsplit]
  calc ‖(Complex.I * dotR (x - y) r) • u + (Complex.I * dotR y r) • (u - v)‖
      ≤ ‖(Complex.I * dotR (x - y) r) • u‖ + ‖(Complex.I * dotR y r) • (u - v)‖ :=
        norm_add_le _ _
    _ = ‖dotR (x - y) r‖ * ‖u‖ + ‖dotR y r‖ * ‖u - v‖ := by
        rw [norm_smul, norm_smul, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
    _ ≤ ‖r‖ * ‖x - y‖ * ‖u‖ + ‖r‖ * ‖y‖ * ‖u - v‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _))

/-! ### Uniform-in-time limit passage for the convection -/

/-- **Uniform Tannery on the window**: uniformly bounded energy and enstrophy
plus mode-wise uniform convergence on `[0,T]` pass through the full convection,
uniformly on `[0,T]`. -/
theorem tendsto_convFull_uniformlyOn {E Z T : ℝ} (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {c : ℕ → ℝ → (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hEn : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖c n t l‖ ^ 2 ≤ E)
    (hZn : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c n t l‖ ^ 2 ≤ Z)
    (hu : ∀ l, TendstoUniformlyOn (fun n t => c n t l) (fun t => g t l)
      Filter.atTop (Set.Icc (0:ℝ) T)) (k : Fin 3 → ℤ) :
    TendstoUniformlyOn (fun n t => convFull (c n t) k) (fun t => convFull (g t) k)
      Filter.atTop (Set.Icc (0:ℝ) T) := by
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ l,
      Filter.Tendsto (fun n => c n t l) Filter.atTop (nhds (g t l)) :=
    fun t ht l => (hu l).tendsto_at ht
  have hgE : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset (Fin 3 → ℤ),
      ∑ l ∈ F, ‖g t l‖ ^ 2 ≤ E := by
    intro t ht F
    have hlim := tendsto_finsetSum (f := fun l n => ‖c n t l‖ ^ 2)
      (a := fun l => ‖g t l‖ ^ 2) F (fun l _ => ((hpt t ht l).norm).pow 2)
    exact le_of_tendsto' hlim fun n => hEn n t ht F
  have hgZ : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ F : Finset (Fin 3 → ℤ),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖g t l‖ ^ 2 ≤ Z := by
    intro t ht F
    have hlim := tendsto_finsetSum (f := fun l n => ‖freq l‖ ^ 2 * ‖c n t l‖ ^ 2)
      (a := fun l => ‖freq l‖ ^ 2 * ‖g t l‖ ^ 2) F
      (fun l _ => tendsto_const_nhds.mul (((hpt t ht l).norm).pow 2))
    exact le_of_tendsto' hlim fun n => hZn n t ht F
  have hEsum : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, Summable fun l => ‖c n t l‖ ^ 2 :=
    fun n t ht => summable_of_sum_le (fun l => sq_nonneg _) (hEn n t ht)
  have hZsum : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T,
      Summable fun l => ‖freq l‖ ^ 2 * ‖c n t l‖ ^ 2 :=
    fun n t ht => summable_of_sum_le (fun l => by positivity) (hZn n t ht)
  have hgEsum : ∀ t ∈ Set.Icc (0:ℝ) T, Summable fun l => ‖g t l‖ ^ 2 :=
    fun t ht => summable_of_sum_le (fun l => sq_nonneg _) (hgE t ht)
  have hgZsum : ∀ t ∈ Set.Icc (0:ℝ) T,
      Summable fun l => ‖freq l‖ ^ 2 * ‖g t l‖ ^ 2 :=
    fun t ht => summable_of_sum_le (fun l => by positivity) (hgZ t ht)
  have hensn : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, ens (c n t) ≤ Z :=
    fun n t ht => Real.tsum_le_of_sum_le (fun l => by positivity) (hZn n t ht)
  have hensg : ∀ t ∈ Set.Icc (0:ℝ) T, ens (g t) ≤ Z :=
    fun t ht => Real.tsum_le_of_sum_le (fun l => by positivity) (hgZ t ht)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hMpos, hMtail⟩ : ∃ M : ℝ, 0 < M ∧ Z / M + Z / M ≤ ε / 2 := by
    have h4 : 0 ≤ 4 * Z / ε := div_nonneg (by linarith) hε.le
    have hMp : (0 : ℝ) < 4 * Z / ε + 1 := by linarith
    refine ⟨4 * Z / ε + 1, hMp, ?_⟩
    rw [← add_div, div_le_iff₀ hMp]
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
  set B : ℝ := ∑ l ∈ F, ‖freq (k - l)‖ * Real.sqrt E with hBdef
  have hB0 : 0 ≤ B :=
    Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨δ, hδpos, hδB⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * δ * B < ε / 2 := by
    have hB1 : (0:ℝ) < 4 * (B + 1) := by linarith
    refine ⟨ε / (4 * (B + 1)), div_pos hε hB1, ?_⟩
    have hq : ε / (4 * (B + 1)) * (4 * (B + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt hB1)
    have hqpos : 0 < ε / (4 * (B + 1)) := div_pos hε hB1
    nlinarith [hq, hqpos, hB0]
  have hev : ∀ᶠ n in Filter.atTop, ∀ l ∈ F ∪ F.image (fun l => k - l),
      ∀ t ∈ Set.Icc (0:ℝ) T, dist (g t l) (c n t l) < δ := by
    rw [Filter.eventually_all_finset]
    exact fun l _ => Metric.tendstoUniformlyOn_iff.mp (hu l) δ hδpos
  filter_upwards [hev] with n hn
  intro t ht
  have hd : ∀ l ∈ F ∪ F.image (fun l => k - l), ‖c n t l - g t l‖ ≤ δ := by
    intro l hl
    have h := hn l hl t ht
    rw [dist_comm, dist_eq_norm] at h
    exact h.le
  have hterm : ∀ l ∈ F,
      ‖(Complex.I * dotR (c n t l) (freq (k - l))) • c n t (k - l) -
        (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l)‖ ≤
      ‖freq (k - l)‖ * Real.sqrt E * δ + ‖freq (k - l)‖ * Real.sqrt E * δ := by
    intro l hl
    have hbase := flc_term_diff_le (c n t l) (g t l) (c n t (k - l)) (g t (k - l))
      (freq (k - l))
    have hxy : ‖c n t l - g t l‖ ≤ δ := hd l (Finset.mem_union_left _ hl)
    have huv : ‖c n t (k - l) - g t (k - l)‖ ≤ δ :=
      hd (k - l) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl))
    have hcE : ‖c n t (k - l)‖ ≤ Real.sqrt E := flc_mode_le (hEn n t ht) (k - l)
    have hgE' : ‖g t l‖ ≤ Real.sqrt E := flc_mode_le (hgE t ht) l
    refine hbase.trans (add_le_add ?_ ?_)
    · calc ‖freq (k - l)‖ * ‖c n t l - g t l‖ * ‖c n t (k - l)‖
          ≤ ‖freq (k - l)‖ * δ * Real.sqrt E :=
            mul_le_mul (mul_le_mul_of_nonneg_left hxy (norm_nonneg _)) hcE
              (norm_nonneg _) (mul_nonneg (norm_nonneg _) hδpos.le)
        _ = ‖freq (k - l)‖ * Real.sqrt E * δ := by ring
    · exact mul_le_mul (mul_le_mul_of_nonneg_left hgE' (norm_nonneg _)) huv
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hfin : ‖∑ l ∈ F,
      ((Complex.I * dotR (c n t l) (freq (k - l))) • c n t (k - l) -
        (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l))‖ < ε / 2 := by
    calc ‖∑ l ∈ F,
        ((Complex.I * dotR (c n t l) (freq (k - l))) • c n t (k - l) -
          (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l))‖
        ≤ ∑ l ∈ F, ‖(Complex.I * dotR (c n t l) (freq (k - l))) • c n t (k - l) -
            (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ l ∈ F, (‖freq (k - l)‖ * Real.sqrt E * δ +
            ‖freq (k - l)‖ * Real.sqrt E * δ) := Finset.sum_le_sum hterm
      _ = 2 * δ * B := by
          rw [hBdef, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ < ε / 2 := hδB
  rw [dist_eq_norm, norm_sub_rev]
  have hbound := flc_convFull_diff_le hZ0 hMpos (hEsum n t ht) (hZsum n t ht)
    (hgEsum t ht) (hgZsum t ht) (hensn n t ht) (hensg t ht) k hsF
  calc ‖convFull (c n t) k - convFull (g t) k‖
      ≤ ‖∑ l ∈ F, ((Complex.I * dotR (c n t l) (freq (k - l))) • c n t (k - l) -
          (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l))‖ + (Z / M + Z / M) :=
        hbound
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hfin hMtail
    _ = ε := add_halves ε

/-- **Continuity of the convection in time**: uniform energy/enstrophy bounds
plus mode-wise continuity on the window give continuity of `convFull` on the
window — the growing-ball partial sums are continuous and converge uniformly by
the enstrophy tail bound. -/
theorem continuousOn_convFull {E Z T : ℝ} (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hEg : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖g t l‖ ^ 2 ≤ E)
    (hZg : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖g t l‖ ^ 2 ≤ Z)
    (hg : ∀ l, ContinuousOn (fun t => g t l) (Set.Icc (0:ℝ) T)) (k : Fin 3 → ℤ) :
    ContinuousOn (fun t => convFull (g t) k) (Set.Icc (0:ℝ) T) := by
  have hEsum : ∀ t ∈ Set.Icc (0:ℝ) T, Summable fun l => ‖g t l‖ ^ 2 :=
    fun t ht => summable_of_sum_le (fun l => sq_nonneg _) (hEg t ht)
  have hZsum : ∀ t ∈ Set.Icc (0:ℝ) T,
      Summable fun l => ‖freq l‖ ^ 2 * ‖g t l‖ ^ 2 :=
    fun t ht => summable_of_sum_le (fun l => by positivity) (hZg t ht)
  have hens : ∀ t ∈ Set.Icc (0:ℝ) T, ens (g t) ≤ Z :=
    fun t ht => Real.tsum_le_of_sum_le (fun l => by positivity) (hZg t ht)
  have hcont : ∀ n : ℕ, ContinuousOn (fun t =>
      -(∑ l ∈ (finite_freq_le ((n : ℝ) + 1)).toFinset,
        (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l)))
      (Set.Icc (0:ℝ) T) := by
    intro n
    refine ContinuousOn.neg ?_
    refine continuousOn_finsetSum _ fun l _ => ?_
    have hdot : ContinuousOn (fun t => dotR (g t l) (freq (k - l)))
        (Set.Icc (0:ℝ) T) :=
      (flc_dotR_continuous (freq (k - l))).comp_continuousOn (hg l)
    exact (continuousOn_const.mul hdot).smul (hg (k - l))
  have htu : TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) =>
      -(∑ l ∈ (finite_freq_le ((n : ℝ) + 1)).toFinset,
        (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l)))
      (fun t => convFull (g t) k) Filter.atTop (Set.Icc (0:ℝ) T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (Z / ε)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    intro t ht
    have hMpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hsF : ∀ l ∈ (↑(finite_freq_le ((n : ℝ) + 1)).toFinset :
        Set (Fin 3 → ℤ))ᶜ, (n : ℝ) + 1 < ‖freq l‖ := by
      intro l hl
      simp only [Set.mem_compl_iff, Finset.mem_coe, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq, not_le] at hl
      exact hl
    have hT : Summable fun l =>
        (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l) :=
      flc_summable_T (hEsum t ht) (hZsum t ht) k
    have hsplit := hT.sum_add_tsum_compl (s := (finite_freq_le ((n : ℝ) + 1)).toFinset)
    have hkey : convFull (g t) k -
        -(∑ l ∈ (finite_freq_le ((n : ℝ) + 1)).toFinset,
          (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l)) =
        -(∑' l : ↑(↑(finite_freq_le ((n : ℝ) + 1)).toFinset : Set (Fin 3 → ℤ))ᶜ,
          (Complex.I * dotR (g t l.val) (freq (k - l.val))) • g t (k - l.val)) := by
      rw [convFull, ← hsplit]
      abel
    have htail := flc_tail_norm (c := g t) hZ0 hMpos (hEsum t ht) (hZsum t ht)
      (hens t ht) k hsF
    show dist (convFull (g t) k)
      (-(∑ l ∈ (finite_freq_le ((n : ℝ) + 1)).toFinset,
        (Complex.I * dotR (g t l) (freq (k - l))) • g t (k - l))) < ε
    rw [dist_eq_norm, hkey, norm_neg]
    refine lt_of_le_of_lt htail ?_
    rw [div_lt_iff₀ hMpos]
    have h1 : Z / ε < (n : ℝ) + 1 := by
      have h2 : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith [hN]
    rw [div_lt_iff₀ hε] at h1
    nlinarith [h1]
  exact htu.continuousOn ((Filter.Eventually.of_forall hcont).frequently)

end TheoremB
