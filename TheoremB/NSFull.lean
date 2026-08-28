/-
# The full Navier-Stokes coefficient system (Tier 3, wave 1)

The infinite (untruncated) spectral convection `convFull`, its Cauchy-Schwarz
majorant `‖convFull c k‖ ≤ √(en c)·√(ens c)`, compatibility with the Galerkin
convection `convGal` on box-supported fields, the enstrophy tail bound
(energy beyond frequency `M` is at most `ens/M²`), finiteness of frequency
balls, and the box/truncation machinery for the Galerkin exhaustion.

Every `tsum` here carries explicit summability hypotheses — a non-summable
`tsum` silently returns `0` (the campaign's triMaj trap), so nothing below
is stated without them.
-/
import TheoremB.NSGalerkin

namespace TheoremB

open Set

/-! ### The full convection -/

/-- The full (untruncated) spectral convection. Prefactor and slot conventions
are copied verbatim from `convGal` (whose body is
`if k ∈ S then -∑ l ∈ S, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) else 0`). -/
noncomputable def convFull (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : Vel :=
  -(∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l))

private lemma nf_dotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

/-- For `c` supported on `S`, `convFull` agrees with `convGal` on box modes.
(Off the box `convGal` is `0` by fiat while `convFull` need not be — that
asymmetry is the Galerkin projection error and is treated explicitly in the
limit tier, never swept into a global function equality.) -/
lemma convFull_eq_convGal {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) {k : Fin 3 → ℤ} (hk : k ∈ S) :
    convFull c k = convGal S c k := by
  unfold convFull convGal
  rw [if_pos hk]
  congr 1
  refine tsum_eq_sum fun l hl => ?_
  rw [hsupp l hl, nf_dotR_zero_left, mul_zero, zero_smul]

/-- The Cauchy-Schwarz majorant family of the full convection is summable,
given finite energy and enstrophy. -/
lemma summable_convMaj {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    Summable fun l => ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hf2 : Summable fun l => ‖c l‖ ^ (2 : ℝ) := hE.congr fun l => h2 _
  have hZk : Summable fun l => ‖freq (k - l)‖ ^ 2 * ‖c (k - l)‖ ^ 2 := by
    have h := ((Equiv.subLeft k).summable_iff
      (f := fun m => ‖freq m‖ ^ 2 * ‖c m‖ ^ 2)).mpr hZ
    exact h.congr fun l => by simp [Function.comp]
  have hg2 : Summable fun l => (‖freq (k - l)‖ * ‖c (k - l)‖) ^ (2 : ℝ) :=
    hZk.congr fun l => by rw [← h2]; ring
  exact Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun l => norm_nonneg _) (fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hf2 hg2

/-- Cauchy-Schwarz: `∑' l, ‖c l‖·‖freq (k−l)‖·‖c (k−l)‖ ≤ √(en c)·√(ens c)`. -/
lemma convMaj_le {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    (∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) ≤
      Real.sqrt (en c) * Real.sqrt (ens c) := by
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hf2 : Summable fun l => ‖c l‖ ^ (2 : ℝ) := hE.congr fun l => h2 _
  have hZk : Summable fun l => ‖freq (k - l)‖ ^ 2 * ‖c (k - l)‖ ^ 2 := by
    have h := ((Equiv.subLeft k).summable_iff
      (f := fun m => ‖freq m‖ ^ 2 * ‖c m‖ ^ 2)).mpr hZ
    exact h.congr fun l => by simp [Function.comp]
  have hg2 : Summable fun l => (‖freq (k - l)‖ * ‖c (k - l)‖) ^ (2 : ℝ) :=
    hZk.congr fun l => by rw [← h2]; ring
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun l => ‖c l‖) (g := fun l => ‖freq (k - l)‖ * ‖c (k - l)‖)
    (fun l => norm_nonneg _) (fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hf2 hg2
  have rf : (∑' l, ‖c l‖ ^ (2 : ℝ)) = en c := tsum_congr fun l => (h2 _).symm
  have rg : (∑' l, (‖freq (k - l)‖ * ‖c (k - l)‖) ^ (2 : ℝ)) = ens c := by
    have e1 : (∑' l, (‖freq (k - l)‖ * ‖c (k - l)‖) ^ (2 : ℝ)) =
        ∑' l, ‖freq (k - l)‖ ^ 2 * ‖c (k - l)‖ ^ 2 :=
      tsum_congr fun l => by rw [← h2]; ring
    have hens : (∑' m : Fin 3 → ℤ, ‖freq m‖ ^ 2 * ‖c m‖ ^ 2) = ens c := rfl
    rw [e1, ← hens]
    have h := (Equiv.subLeft k).tsum_eq (f := fun m => ‖freq m‖ ^ 2 * ‖c m‖ ^ 2)
    simp only [Equiv.subLeft_apply] at h
    exact h
  rw [rf, rg] at cs
  calc (∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
      ≤ en c ^ (1 / (2:ℝ)) * ens c ^ (1 / (2:ℝ)) := cs
    _ = Real.sqrt (en c) * Real.sqrt (ens c) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- The norm of the full convection is dominated by its CS majorant. -/
lemma norm_convFull_le {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    ‖convFull c k‖ ≤ ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by
  have hmaj := summable_convMaj hE hZ k
  have hterm : ∀ l, ‖(Complex.I * dotR (c l) (freq (k - l))) • c (k - l)‖ ≤
      ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by
    intro l
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    calc ‖dotR (c l) (freq (k - l))‖ * ‖c (k - l)‖
        ≤ (‖freq (k - l)‖ * ‖c l‖) * ‖c (k - l)‖ :=
          mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
      _ = ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by ring
  have hnorm_sum : Summable fun l =>
      ‖(Complex.I * dotR (c l) (freq (k - l))) • c (k - l)‖ :=
    hmaj.of_nonneg_of_le (fun l => norm_nonneg _) hterm
  calc ‖convFull c k‖
      = ‖∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l)‖ := by
        rw [convFull, norm_neg]
    _ ≤ ∑' l, ‖(Complex.I * dotR (c l) (freq (k - l))) • c (k - l)‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) :=
        hnorm_sum.tsum_le_tsum hterm hmaj

/-- `‖convFull c k‖ ≤ √(en c)·√(ens c)`. -/
lemma norm_convFull_le_sqrt {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    ‖convFull c k‖ ≤ Real.sqrt (en c) * Real.sqrt (ens c) :=
  (norm_convFull_le hE hZ k).trans (convMaj_le hE hZ k)

/-! ### The Leray projection is 2-Lipschitz (public form) -/

private lemma nf_castCV_zero : castCV 0 = 0 := by
  ext j
  simp [castCV]

private lemma nf_freq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext j
  simp [freq]

/-- The mode-wise Leray projection never more than doubles the norm. -/
lemma norm_lerayProj_le (k : Fin 3 → ℤ) (w : Vel) :
    ‖lerayProj k w‖ ≤ 2 * ‖w‖ := by
  by_cases hk : k = 0
  · subst hk
    simp only [lerayProj, nf_freq_zero, nf_castCV_zero, smul_zero, sub_zero]
    linarith [norm_nonneg w]
  · have h1 : (1 : ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    have hstep : ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ ≤ ‖w‖ := by
      rw [norm_smul, norm_div, norm_castCV]
      have hcast : ‖((‖freq k‖ ^ 2 : ℝ) : ℂ)‖ = ‖freq k‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      rw [hcast, div_mul_eq_mul_div,
        div_le_iff₀ (by positivity : (0 : ℝ) < ‖freq k‖ ^ 2)]
      calc ‖dotR w (freq k)‖ * ‖freq k‖
          ≤ (‖freq k‖ * ‖w‖) * ‖freq k‖ :=
            mul_le_mul_of_nonneg_right (norm_dotR_le w (freq k)) (norm_nonneg _)
        _ = ‖w‖ * ‖freq k‖ ^ 2 := by ring
    have htri : ‖lerayProj k w‖
        ≤ ‖w‖ + ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ := by
      simp only [lerayProj]
      exact norm_sub_le _ _
    linarith

/-! ### The enstrophy tail bound -/

/-- Energy beyond frequency `M` is controlled by the enstrophy: the tail
`∑ over {l : M < ‖freq l‖}` of `‖c l‖²` is at most `(∑' l, ‖freq l‖²‖c l‖²)/M²`. -/
lemma tail_en_le_ens {c : (Fin 3 → ℤ) → Vel} {M : ℝ} (hM : 0 < M)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) :
    (∑' l : {l : Fin 3 → ℤ // M < ‖freq l‖}, ‖c l.val‖ ^ 2) ≤ ens c / M ^ 2 := by
  have hZs : Summable fun l : {l : Fin 3 → ℤ // M < ‖freq l‖} =>
      ‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2 := hZ.subtype _
  have hterm : ∀ l : {l : Fin 3 → ℤ // M < ‖freq l‖},
      ‖c l.val‖ ^ 2 ≤ M⁻¹ ^ 2 * (‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2) := by
    intro l
    have h1 : M ^ 2 ≤ ‖freq l.val‖ ^ 2 := by nlinarith [l.property, hM]
    have h2 : (0:ℝ) < M ^ 2 := by positivity
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ h2]
    nlinarith [sq_nonneg ‖c l.val‖]
  have hsub : Summable fun l : {l : Fin 3 → ℤ // M < ‖freq l‖} => ‖c l.val‖ ^ 2 :=
    (hZs.mul_left (M⁻¹ ^ 2)).of_nonneg_of_le (fun l => sq_nonneg _) hterm
  calc (∑' l : {l : Fin 3 → ℤ // M < ‖freq l‖}, ‖c l.val‖ ^ 2)
      ≤ ∑' l : {l : Fin 3 → ℤ // M < ‖freq l‖},
          M⁻¹ ^ 2 * (‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2) :=
        hsub.tsum_le_tsum hterm (hZs.mul_left _)
    _ = M⁻¹ ^ 2 * ∑' l : {l : Fin 3 → ℤ // M < ‖freq l‖},
          ‖freq l.val‖ ^ 2 * ‖c l.val‖ ^ 2 := tsum_mul_left
    _ ≤ M⁻¹ ^ 2 * ens c := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hZ.tsum_subtype_le _ _ (fun l => by positivity)
    _ = ens c / M ^ 2 := by
        rw [inv_pow, ← div_eq_inv_mul]

/-- Frequency balls are finite: only finitely many modes have `‖freq l‖ ≤ M`. -/
lemma finite_freq_le (M : ℝ) : {l : Fin 3 → ℤ | ‖freq l‖ ≤ M}.Finite := by
  by_cases hM : 0 ≤ M
  · have hsub : {l : Fin 3 → ℤ | ‖freq l‖ ≤ M} ⊆
        {l : Fin 3 → ℤ | ∀ i, l i ∈ Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)} := by
      intro l hl i
      have h1 : ((natMax l : ℕ) : ℝ) ≤ M := (natMax_cast_le_norm_freq l).trans hl
      have h2 : natMax l ≤ ⌈M⌉₊ := by
        exact_mod_cast h1.trans (Nat.le_ceil M)
      have h3 : (l i).natAbs ≤ natMax l :=
        Finset.le_sup (f := fun j => (l j).natAbs) (Finset.mem_univ i)
      have h4 : (l i).natAbs ≤ ⌈M⌉₊ := h3.trans h2
      rw [Finset.mem_Icc]
      omega
    refine Set.Finite.subset ?_ hsub
    have : {l : Fin 3 → ℤ | ∀ i, l i ∈ Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)} =
        ↑(Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(⌈M⌉₊ : ℤ)) (⌈M⌉₊ : ℤ)) := by
      ext l
      simp [Fintype.mem_piFinset, Finset.mem_Icc, Pi.le_def, forall_and]
    rw [this]
    exact (Fintype.piFinset _).finite_toSet
  · have : {l : Fin 3 → ℤ | ‖freq l‖ ≤ M} = ∅ := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have := norm_nonneg (freq l)
      linarith [not_le.mp hM]
    rw [this]
    exact Set.finite_empty

/-! ### Boxes and truncation -/

/-- The symmetric zero-free cube of side radius `R`. -/
noncomputable def boxS (R : ℕ) : Finset (Fin 3 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(R:ℤ)) R).erase 0

lemma boxS_zero_not_mem (R : ℕ) : (0 : Fin 3 → ℤ) ∉ boxS R :=
  Finset.notMem_erase 0 _

lemma mem_boxS {R : ℕ} {k : Fin 3 → ℤ} :
    k ∈ boxS R ↔ k ≠ 0 ∧ ∀ i, -(R:ℤ) ≤ k i ∧ k i ≤ R := by
  rw [boxS, Finset.mem_erase, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]

lemma boxS_symm (R : ℕ) : ∀ k ∈ boxS R, -k ∈ boxS R := by
  intro k hk
  rw [mem_boxS] at hk ⊢
  refine ⟨fun h0 => hk.1 ?_, fun i => ?_⟩
  · have h := congrArg Neg.neg h0
    simpa using h
  · have h := hk.2 i
    simp only [Pi.neg_apply]
    omega

/-- Every nonzero mode lands in every large enough box. -/
lemma exists_boxS (k : Fin 3 → ℤ) (hk : k ≠ 0) : ∃ R : ℕ, ∀ R', R ≤ R' → k ∈ boxS R' := by
  refine ⟨natMax k, fun R' hR' => mem_boxS.mpr ⟨hk, fun i => ?_⟩⟩
  have h : (k i).natAbs ≤ natMax k :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ i)
  have h2 : (k i).natAbs ≤ R' := h.trans hR'
  omega

/-- Truncation of a coefficient field to a box. -/
noncomputable def truncate (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel) :
    (Fin 3 → ℤ) → Vel :=
  fun k => if k ∈ S then c k else 0

lemma truncate_supp (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel) :
    ∀ k, k ∉ S → truncate S c k = 0 := fun k hk => if_neg hk

lemma truncate_eq_of_mem (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel)
    {k : Fin 3 → ℤ} (hk : k ∈ S) : truncate S c k = c k := if_pos hk

lemma truncate_norm_le (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) :
    ‖truncate S c k‖ ≤ ‖c k‖ := by
  unfold truncate
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [if_neg hk, norm_zero]
    exact norm_nonneg _

/-- Truncation only decreases the energy. -/
lemma en_truncate_le {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2) (S : Finset (Fin 3 → ℤ)) :
    en (truncate S c) ≤ en c := by
  have hsum : Summable fun l => ‖truncate S c l‖ ^ 2 :=
    hE.of_nonneg_of_le (fun l => sq_nonneg _)
      (fun l => by
        have := truncate_norm_le S c l
        nlinarith [norm_nonneg (truncate S c l)])
  exact hsum.tsum_le_tsum
    (fun l => by
      have := truncate_norm_le S c l
      nlinarith [norm_nonneg (truncate S c l)]) hE

/-- Truncation only decreases the enstrophy. -/
lemma ens_truncate_le {c : (Fin 3 → ℤ) → Vel}
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (S : Finset (Fin 3 → ℤ)) :
    ens (truncate S c) ≤ ens c := by
  have hle : ∀ l, ‖freq l‖ ^ 2 * ‖truncate S c l‖ ^ 2 ≤ ‖freq l‖ ^ 2 * ‖c l‖ ^ 2 := by
    intro l
    have := truncate_norm_le S c l
    have h2 : ‖truncate S c l‖ ^ 2 ≤ ‖c l‖ ^ 2 := by
      nlinarith [norm_nonneg (truncate S c l)]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hsum : Summable fun l => ‖freq l‖ ^ 2 * ‖truncate S c l‖ ^ 2 :=
    hZ.of_nonneg_of_le (fun l => by positivity) hle
  exact hsum.tsum_le_tsum hle hZ

/-- Truncation to a symmetric box preserves reality. -/
lemma realField_truncate {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    {S : Finset (Fin 3 → ℤ)} (hSsym : ∀ k ∈ S, -k ∈ S) :
    RealField (truncate S c) := by
  intro k
  unfold truncate
  by_cases hk : k ∈ S
  · have hnk : -k ∈ S := hSsym k hk
    rw [if_pos hk, if_pos hnk]
    exact hreal k
  · have hnk : -k ∉ S := fun h => hk (by simpa using hSsym _ h)
    rw [if_neg hk, if_neg hnk]
    have hc0 : conjVel (0 : Vel) = 0 := by
      ext j
      simp [conjVel]
    rw [hc0]

/-- Truncation preserves divergence-freeness. -/
lemma divFree_truncate {c : (Fin 3 → ℤ) → Vel} (hdiv : DivFree c)
    (S : Finset (Fin 3 → ℤ)) : DivFree (truncate S c) := by
  intro k
  unfold truncate
  by_cases hk : k ∈ S
  · rw [if_pos hk]
    exact hdiv k
  · rw [if_neg hk]
    exact nf_dotR_zero_left _

-- Consumers use only the abstract lemmas above; keeping these reducible makes
-- downstream elaboration whnf-unfold the piFinset structure and time out.
attribute [irreducible] boxS truncate

end TheoremB
