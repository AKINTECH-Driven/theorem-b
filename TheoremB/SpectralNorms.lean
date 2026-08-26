/-
  TheoremB/SpectralNorms.lean
  Tier 1 of the Theorem B campaign (M2 wave 1, 27 Aug 2026).

  The spectral (Fourier-side) layer for the enstrophy master inequality on
  the 3-torus: a velocity field is its coefficient family over the frequency
  lattice ℤ³, and energy `en`, enstrophy `ens`, dissipation `dis`, and the
  sup-norm majorant `spec1` are weighted sums.  Weights are BARE Euclidean
  ‖k‖; the (2π)-factors of any particular Fourier convention are absorbed by
  the abstract constants at the Tier-2 bridge (see rung3-tier1-blueprint.md).

  FROZEN (M2): wave 1 = summable_inv_freq_pow_four (W1), ens_sq_le_en_mul_dis
  (W2), exists_spec1_sq_le_dis (W3), exists_spec1_pow_four_le_ens_mul_dis
  (W4); wave 2 = triMaj_le (M2.5) and master_inequality (M2.6).  All are
  proved below; the shell machinery, the low/high split, and the trilinear
  majorant layer are the prover's internal decomposition.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import Mathlib

namespace TheoremB

open Set

/-! ## The frequency lattice -/

/-- The Euclidean embedding of a lattice frequency. -/
noncomputable def freq (k : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i => (k i : ℝ)

lemma norm_freq (k : Fin 3 → ℤ) : ‖freq k‖ = Real.sqrt (∑ i, (k i : ℝ) ^ 2) := by
  simp [freq, EuclideanSpace.norm_eq]

lemma one_le_norm_freq {k : Fin 3 → ℤ} (hk : k ≠ 0) : 1 ≤ ‖freq k‖ := by
  rw [norm_freq]
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hk (funext h)
  have h1 : (1 : ℝ) ≤ (k i : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    have h2 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast this
    nlinarith [abs_nonneg ((k i : ℝ)), sq_abs ((k i : ℝ))]
  have h2 : (k i : ℝ) ^ 2 ≤ ∑ j, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((k j : ℝ) ^ 2))
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ j, (k j : ℝ) ^ 2) := Real.sqrt_le_sqrt (by linarith)

/-! ### ℤ³ as a lattice in Euclidean space (bridge to `ZLattice`) -/

noncomputable def eBasis : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

noncomputable def zLat : Submodule ℤ (EuclideanSpace ℝ (Fin 3)) :=
  Submodule.span ℤ (Set.range ⇑eBasis)

instance : DiscreteTopology zLat :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range ⇑eBasis)))

noncomputable def zBasis : Module.Basis (Fin 3) ℤ zLat :=
  eBasis.restrictScalars ℤ

noncomputable def zEquiv : (Fin 3 → ℤ) ≃ zLat :=
  zBasis.equivFun.toEquiv.symm

lemma coe_zEquiv (k : Fin 3 → ℤ) :
    ((zEquiv k : zLat) : EuclideanSpace ℝ (Fin 3)) = freq k := by
  have hb : ∀ x, ((zBasis x : zLat) : EuclideanSpace ℝ (Fin 3)) = eBasis x := fun x =>
    Module.Basis.restrictScalars_apply ℤ eBasis x
  simp only [zEquiv, LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe]
  rw [Module.Basis.equivFun_symm_apply]
  ext i
  simp [hb, eBasis, freq, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single, Pi.single_apply,
    Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, mul_one, mul_zero]

lemma summable_norm_freq_rpow {r : ℝ} (hr : r < -3) :
    Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ r := by
  have h3 : Module.finrank ℤ zLat = 3 := by
    rw [Module.finrank_eq_card_basis zBasis, Fintype.card_fin]
  have h := ZLattice.summable_norm_rpow zLat r (by rw [h3]; exact_mod_cast hr)
  have h' := (zEquiv.summable_iff
    (f := fun z : zLat => ‖z‖ ^ r)).mpr h
  refine h'.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [show ‖zEquiv k‖ = ‖((zEquiv k : zLat) : EuclideanSpace ℝ (Fin 3))‖ from rfl,
    coe_zEquiv]

/-- **W1.** The lattice weight `(‖k‖⁴)⁻¹` is summable over ℤ³ (the `k = 0`
term is `0⁻¹ = 0`). -/
theorem summable_inv_freq_pow_four :
    Summable fun k : Fin 3 → ℤ => (‖freq k‖ ^ 4)⁻¹ := by
  refine (summable_norm_freq_rpow (r := -4) (by norm_num)).congr fun k => ?_
  rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg _),
    Real.rpow_natCast]

/-! ## The spectral quantities -/

variable {V : Type*} [NormedAddCommGroup V]

/-- Spectral energy `E = Σ ‖c k‖²`. -/
noncomputable def en (c : (Fin 3 → ℤ) → V) : ℝ := ∑' k, ‖c k‖ ^ 2

/-- Spectral enstrophy `Z = Σ ‖k‖² ‖c k‖²`. -/
noncomputable def ens (c : (Fin 3 → ℤ) → V) : ℝ := ∑' k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2

/-- Spectral dissipation `D = Σ ‖k‖⁴ ‖c k‖²`. -/
noncomputable def dis (c : (Fin 3 → ℤ) → V) : ℝ := ∑' k, ‖freq k‖ ^ 4 * ‖c k‖ ^ 2

/-- The ℓ¹ sup-norm majorant `S = Σ ‖c k‖`. -/
noncomputable def spec1 (c : (Fin 3 → ℤ) → V) : ℝ := ∑' k, ‖c k‖

/-! ### Summability cascade: `D`-summability controls everything below it -/

lemma summable_en {c : (Fin 3 → ℤ) → V} (hc0 : c 0 = 0)
    (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) :
    Summable fun k => ‖c k‖ ^ 2 := by
  refine hD.of_nonneg_of_le (fun k => sq_nonneg _) fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hc0]
  · have h1 := one_le_norm_freq hk
    nlinarith [sq_nonneg (‖c k‖), sq_nonneg (‖freq k‖ - 1),
      sq_nonneg (‖freq k‖ ^ 2 - 1)]

lemma summable_ens {c : (Fin 3 → ℤ) → V} (hc0 : c 0 = 0)
    (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) :
    Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 := by
  refine hD.of_nonneg_of_le
    (fun k => mul_nonneg (by positivity) (sq_nonneg _)) fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp [hc0]
  · have h1 := one_le_norm_freq hk
    nlinarith [sq_nonneg (‖c k‖), mul_nonneg (sq_nonneg (‖freq k‖)) (sq_nonneg (‖c k‖)),
      sq_nonneg (‖freq k‖ - 1), sq_nonneg (‖freq k‖ + 1)]

private lemma rpow_two_of_pow {x : ℝ} : x ^ 2 = x ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **W2 (interpolation, pure Cauchy–Schwarz).**  `Z² ≤ E · D`, the spectral
form of `‖∇u‖² ≤ ‖u‖ ‖Δu‖`. -/
theorem ens_sq_le_en_mul_dis {c : (Fin 3 → ℤ) → V} (hc0 : c 0 = 0)
    (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) :
    ens c ^ 2 ≤ en c * dis c := by
  have hE := summable_en hc0 hD
  have hf2 : Summable fun k => ‖c k‖ ^ (2 : ℝ) :=
    hE.congr fun k => rpow_two_of_pow
  have hg2 : Summable fun k => (‖freq k‖ ^ 2 * ‖c k‖) ^ (2 : ℝ) :=
    hD.congr fun k => by rw [← rpow_two_of_pow]; ring
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two
    (f := fun k => ‖c k‖) (g := fun k => ‖freq k‖ ^ 2 * ‖c k‖)
    (fun k => norm_nonneg _)
    (fun k => mul_nonneg (by positivity) (norm_nonneg _)) hf2 hg2
  have lhs_eq : ∑' k, ‖c k‖ * (‖freq k‖ ^ 2 * ‖c k‖) = ens c :=
    tsum_congr fun k => by ring
  have rf : ∑' k, ‖c k‖ ^ (2 : ℝ) = en c :=
    tsum_congr fun k => rpow_two_of_pow.symm
  have rg : ∑' k, (‖freq k‖ ^ 2 * ‖c k‖) ^ (2 : ℝ) = dis c :=
    tsum_congr fun k => by rw [← rpow_two_of_pow]; ring
  rw [lhs_eq, rf, rg] at cs
  have hen : 0 ≤ en c := tsum_nonneg fun k => sq_nonneg _
  have hdis : 0 ≤ dis c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hsq : en c ^ (1 / 2 : ℝ) * dis c ^ (1 / 2 : ℝ) = Real.sqrt (en c) * Real.sqrt (dis c) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hsq] at cs
  have hnn : 0 ≤ ens c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  calc ens c ^ 2 = ens c * ens c := pow_two _
    _ ≤ (Real.sqrt (en c) * Real.sqrt (dis c)) * (Real.sqrt (en c) * Real.sqrt (dis c)) :=
        mul_self_le_mul_self hnn cs
    _ = en c * dis c := by
        rw [← pow_two, mul_pow, Real.sq_sqrt hen, Real.sq_sqrt hdis]

/-- **W3 (crude Agmon, on squares).**  `S² ≤ C · D` uniformly over
mean-zero fields: a single Cauchy–Schwarz against the summable lattice
weight W1. -/
theorem exists_spec1_sq_le_dis :
    ∃ C, 0 < C ∧ ∀ (c : (Fin 3 → ℤ) → V), c 0 = 0 →
      (Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) →
      spec1 c ^ 2 ≤ C * dis c := by
  set A : ℝ := ∑' k : Fin 3 → ℤ, (‖freq k‖ ^ 4)⁻¹ with hA
  have hAnn : 0 ≤ A := tsum_nonneg fun k => by positivity
  refine ⟨A + 1, by linarith, ?_⟩
  intro c hc0 hD
  have key : ∀ k, ‖c k‖ = (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ 2 * ‖c k‖) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hc0]
    · have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
      field_simp
  have hf2 : Summable fun k => ((‖freq k‖ ^ 2)⁻¹) ^ (2 : ℝ) :=
    summable_inv_freq_pow_four.congr fun k => by
      rw [← rpow_two_of_pow]; ring
  have hg2 : Summable fun k => (‖freq k‖ ^ 2 * ‖c k‖) ^ (2 : ℝ) :=
    hD.congr fun k => by rw [← rpow_two_of_pow]; ring
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two
    (f := fun k => (‖freq k‖ ^ 2)⁻¹) (g := fun k => ‖freq k‖ ^ 2 * ‖c k‖)
    (fun k => by positivity)
    (fun k => mul_nonneg (by positivity) (norm_nonneg _)) hf2 hg2
  have lhs_eq : ∑' k, (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ 2 * ‖c k‖) = spec1 c :=
    (tsum_congr key).symm
  have rf : ∑' k, ((‖freq k‖ ^ 2)⁻¹) ^ (2 : ℝ) = A :=
    tsum_congr fun k => by rw [← rpow_two_of_pow]; ring
  have rg : ∑' k, (‖freq k‖ ^ 2 * ‖c k‖) ^ (2 : ℝ) = dis c :=
    tsum_congr fun k => by rw [← rpow_two_of_pow]; ring
  rw [lhs_eq, rf, rg] at cs
  have hsq : A ^ (1 / 2 : ℝ) * dis c ^ (1 / 2 : ℝ) = Real.sqrt A * Real.sqrt (dis c) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hsq] at cs
  have hdis : 0 ≤ dis c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hs1 : 0 ≤ spec1 c := tsum_nonneg fun k => norm_nonneg _
  calc spec1 c ^ 2 = spec1 c * spec1 c := pow_two _
    _ ≤ (Real.sqrt A * Real.sqrt (dis c)) * (Real.sqrt A * Real.sqrt (dis c)) :=
        mul_self_le_mul_self hs1 cs
    _ = A * dis c := by rw [← pow_two, mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hdis]
    _ ≤ (A + 1) * dis c := by nlinarith

/-! ### Shell machinery for the sharp Agmon bound (lattice combinatorics) -/

/-! ## Agent SHELLS: lattice shell bounds -/

def natMax (k : Fin 3 → ℤ) : ℕ := Finset.univ.sup fun i => (k i).natAbs

private lemma natAbs_cast_eq_abs (a : ℤ) : ((a.natAbs : ℝ)) = |(a : ℝ)| := by
  calc ((a.natAbs : ℝ)) = (((a.natAbs : ℤ) : ℝ)) := by simp only [Int.cast_natCast]
    _ = |(a : ℝ)| := by simp only [Int.natCast_natAbs, Int.cast_abs]

private lemma sq_natAbs_cast (a : ℤ) : ((a.natAbs : ℝ)) ^ 2 = (a : ℝ) ^ 2 := by
  rw [natAbs_cast_eq_abs, sq_abs]

lemma natMax_cast_le_norm_freq (k : Fin 3 → ℤ) : (natMax k : ℝ) ≤ ‖freq k‖ := by
  obtain ⟨i, -, hsup⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3)) Finset.univ_nonempty
      (fun j => (k j).natAbs)
  have hsup' : natMax k = (k i).natAbs := hsup
  rw [norm_freq, hsup']
  calc ((k i).natAbs : ℝ)
      = Real.sqrt (((k i).natAbs : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ = Real.sqrt ((k i : ℝ) ^ 2) := by rw [sq_natAbs_cast]
    _ ≤ Real.sqrt (∑ j, (k j : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (k j : ℝ) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i))

lemma norm_freq_le_sqrt3_mul_natMax (k : Fin 3 → ℤ) : ‖freq k‖ ≤ Real.sqrt 3 * natMax k := by
  rw [norm_freq]
  have hbound : ∀ j : Fin 3, (k j : ℝ) ^ 2 ≤ ((natMax k : ℝ)) ^ 2 := by
    intro j
    have h1 : (k j).natAbs ≤ natMax k :=
      Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ j)
    have h2 : ((k j).natAbs : ℝ) ≤ (natMax k : ℝ) := by exact_mod_cast h1
    have h3 := sq_natAbs_cast (k j)
    rw [← h3]
    have ha : (0:ℝ) ≤ ((k j).natAbs : ℝ) := by positivity
    have hb : (0:ℝ) ≤ ((natMax k : ℕ) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_right h2 hb]
  have hsum : (∑ j, (k j : ℝ) ^ 2) ≤ 3 * ((natMax k : ℝ)) ^ 2 := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j => (k j : ℝ) ^ 2) (g := fun _ => ((natMax k : ℝ)) ^ 2)
      (fun j _ => hbound j)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    exact_mod_cast h
  calc Real.sqrt (∑ j, (k j : ℝ) ^ 2)
      ≤ Real.sqrt (3 * ((natMax k : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * Real.sqrt (((natMax k : ℝ)) ^ 2) :=
        Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 3 * (natMax k : ℝ) := by rw [Real.sqrt_sq (by positivity)]

private lemma eq_zero_of_natMax_eq_zero {k : Fin 3 → ℤ} (h : natMax k = 0) : k = 0 := by
  funext i
  have h1 : (k i).natAbs ≤ natMax k :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ i)
  have h2 : (k i).natAbs = 0 := by omega
  have h3 : k i = 0 := Int.natAbs_eq_zero.mp h2
  simpa using h3

private noncomputable def intBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ)

private lemma mem_intBox (n : ℕ) (k : Fin 3 → ℤ) : k ∈ intBox n ↔ natMax k ≤ n := by
  simp only [intBox, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h
    show Finset.univ.sup (fun i => (k i).natAbs) ≤ n
    apply Finset.sup_le
    intro i _
    have h1 := h i
    omega
  · intro h i
    have h1 : (k i).natAbs ≤ natMax k :=
      Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ i)
    have h2 : (k i).natAbs ≤ n := le_trans h1 h
    omega

private lemma card_intBox (n : ℕ) : (intBox n).card = (2 * n + 1) ^ 3 := by
  simp only [intBox]
  rw [Fintype.card_piFinset_const]
  congr 1
  rw [Int.card_Icc]
  omega

private lemma card_filter_natMax_le (s : Finset (Fin 3 → ℤ)) {m : ℕ} (hm : 0 < m) :
    (s.filter fun k => natMax k = m).card ≤ 26 * m ^ 2 := by
  have hmono : intBox (m - 1) ⊆ intBox m := by
    intro k hk
    rw [mem_intBox] at hk ⊢
    omega
  have hsub : (s.filter fun k => natMax k = m) ⊆ intBox m \ intBox (m - 1) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨-, hkm⟩ := hk
    rw [Finset.mem_sdiff, mem_intBox, mem_intBox]
    omega
  calc (s.filter fun k => natMax k = m).card
      ≤ (intBox m \ intBox (m - 1)).card := Finset.card_le_card hsub
    _ = (intBox m).card - (intBox (m - 1)).card := Finset.card_sdiff_of_subset hmono
    _ = (2 * m + 1) ^ 3 - (2 * (m - 1) + 1) ^ 3 := by rw [card_intBox, card_intBox]
    _ ≤ 26 * m ^ 2 := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        have h1 : 2 * (n + 1 - 1) + 1 = 2 * n + 1 := by omega
        rw [h1, Nat.sub_le_iff_le_add]
        have expand1 : (2 * (n + 1) + 1) ^ 3 = 8 * n ^ 3 + 36 * n ^ 2 + 54 * n + 27 := by ring
        have expand2 : (2 * n + 1) ^ 3 = 8 * n ^ 3 + 12 * n ^ 2 + 6 * n + 1 := by ring
        have expand3 : 26 * (n + 1) ^ 2 = 26 * n ^ 2 + 52 * n + 26 := by ring
        rw [expand1, expand2, expand3]
        generalize n ^ 3 = a
        generalize n ^ 2 = b
        omega

lemma bulk_shell_bound {R : ℝ} (hR : 1 ≤ R) :
    (∑' k : Fin 3 → ℤ, if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) ≤ 100 * R := by
  have hR0 : (0:ℝ) ≤ R := by linarith
  set N : ℕ := ⌊R⌋₊ with hNdef
  have hsupp : ∀ k ∉ intBox N,
      (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) = 0 := by
    intro k hk
    have hcond : ¬(k ≠ 0 ∧ ‖freq k‖ ≤ R) := by
      rintro ⟨-, hkR⟩
      apply hk
      rw [mem_intBox, hNdef]
      exact Nat.le_floor ((natMax_cast_le_norm_freq k).trans hkR)
    exact if_neg hcond
  have hmap : ∀ k ∈ intBox N, natMax k ∈ Finset.range (N + 1) := by
    intro k hk
    rw [mem_intBox] at hk
    rw [Finset.mem_range]
    omega
  have hfiber : ∀ m ∈ Finset.range (N + 1),
      (∑ k ∈ (intBox N).filter fun k => natMax k = m,
        if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) ≤ (26:ℝ) := by
    intro m _hmem
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · refine le_trans (le_of_eq (Finset.sum_eq_zero ?_)) (by norm_num)
      intro k hk
      rw [Finset.mem_filter] at hk
      have hcond : ¬(k ≠ 0 ∧ ‖freq k‖ ≤ R) := by
        rintro ⟨h0, -⟩
        exact h0 (eq_zero_of_natMax_eq_zero hk.2)
      exact if_neg hcond
    · have hm1n : 1 ≤ m := hmpos
      have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1n
      have hmR : (0:ℝ) < (m:ℝ) := by linarith
      have hm2 : ((m:ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hmR)
      have hterm : ∀ k ∈ (intBox N).filter fun k => natMax k = m,
          (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) ≤ ((m:ℝ) ^ 2)⁻¹ := by
        intro k hk
        rw [Finset.mem_filter] at hk
        split_ifs with h
        · have h4 : (m:ℝ) ≤ ‖freq k‖ := by
            rw [← hk.2]
            exact natMax_cast_le_norm_freq k
          have hsq : (m:ℝ) ^ 2 ≤ ‖freq k‖ ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left h4 hmR.le,
              mul_le_mul_of_nonneg_right h4 ((hmR.trans_le h4).le)]
          exact inv_anti₀ (pow_pos hmR 2) hsq
        · positivity
      calc (∑ k ∈ (intBox N).filter fun k => natMax k = m,
            if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0)
          ≤ ((intBox N).filter fun k => natMax k = m).card • ((m:ℝ) ^ 2)⁻¹ :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = (((intBox N).filter fun k => natMax k = m).card : ℝ) * ((m:ℝ) ^ 2)⁻¹ := by
            rw [nsmul_eq_mul]
        _ ≤ ((26 * m ^ 2 : ℕ) : ℝ) * ((m:ℝ) ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast card_filter_natMax_le (intBox N) hmpos
        _ = 26 := by
            push_cast
            rw [mul_assoc, mul_inv_cancel₀ hm2, mul_one]
  calc (∑' k : Fin 3 → ℤ, if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0)
      = ∑ k ∈ intBox N, (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) :=
        tsum_eq_sum hsupp
    _ = ∑ m ∈ Finset.range (N + 1), ∑ k ∈ (intBox N).filter fun k => natMax k = m,
          (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) :=
        (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ m ∈ Finset.range (N + 1), (26:ℝ) := Finset.sum_le_sum hfiber
    _ = ((N + 1 : ℕ) : ℝ) * 26 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 100 * R := by
        have hNle : (N:ℝ) ≤ R := by
          rw [hNdef]
          exact Nat.floor_le hR0
        push_cast
        linarith

lemma tail_shell_bound {R : ℝ} (hR : 1 ≤ R) :
    (∑' k : Fin 3 → ℤ, if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) ≤ 1000 / R := by
  have hR0 : (0:ℝ) < R := by linarith
  have hs3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs3le : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hnn : ∀ k : Fin 3 → ℤ, 0 ≤ (if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) := by
    intro k
    split_ifs
    · positivity
    · exact le_refl 0
  have hle : ∀ k : Fin 3 → ℤ,
      (if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) ≤ (‖freq k‖ ^ 4)⁻¹ := by
    intro k
    split_ifs
    · exact le_refl _
    · positivity
  have hsummable :
      Summable fun k : Fin 3 → ℤ => if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0 :=
    summable_inv_freq_pow_four.of_nonneg_of_le hnn hle
  refine hsummable.tsum_le_of_sum_le fun s => ?_
  set m₀ : ℕ := ⌈R / Real.sqrt 3⌉₊ with hm₀def
  have hm₀pos : 0 < m₀ := by
    rw [hm₀def]
    exact Nat.ceil_pos.mpr (div_pos hR0 hs3)
  have hm₀n : 1 ≤ m₀ := hm₀pos
  have hm₀1 : (1:ℝ) ≤ (m₀:ℝ) := by exact_mod_cast hm₀n
  have hm₀ceil : R / Real.sqrt 3 ≤ (m₀:ℝ) := by
    rw [hm₀def]
    exact Nat.le_ceil _
  set s' : Finset (Fin 3 → ℤ) := s.filter fun k => R < ‖freq k‖ with hs'def
  have heq : (∑ k ∈ s, if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0)
      = ∑ k ∈ s', if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0 := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hk'
    simp only [Finset.mem_filter] at hk'
    have hcond : ¬ R < ‖freq k‖ := fun hc => hk' ⟨hk, hc⟩
    exact if_neg hcond
  have hm₀le : ∀ k ∈ s', m₀ ≤ natMax k := by
    intro k hk
    simp only [hs'def, Finset.mem_filter] at hk
    have h1 : R ≤ Real.sqrt 3 * (natMax k : ℝ) :=
      (le_of_lt hk.2).trans (norm_freq_le_sqrt3_mul_natMax k)
    rw [hm₀def]
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hs3]
    linarith [h1]
  set M : ℕ := s'.sup natMax with hMdef
  have hmap : ∀ k ∈ s', natMax k ∈ Finset.Ioo (m₀ - 1) (M + 1) := by
    intro k hk
    rw [Finset.mem_Ioo]
    have h1 := hm₀le k hk
    have h2 : natMax k ≤ M := by
      rw [hMdef]
      exact Finset.le_sup hk
    omega
  have hfiber : ∀ m ∈ Finset.Ioo (m₀ - 1) (M + 1),
      (∑ k ∈ s'.filter fun k => natMax k = m,
        if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) ≤ 26 * ((m:ℝ) ^ 2)⁻¹ := by
    intro m hm
    rw [Finset.mem_Ioo] at hm
    have hmposn : 0 < m := by omega
    have hm1n : 1 ≤ m := hmposn
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1n
    have hmR : (0:ℝ) < (m:ℝ) := by linarith
    have hm2 : ((m:ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt hmR)
    have hterm : ∀ k ∈ s'.filter fun k => natMax k = m,
        (if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) ≤ ((m:ℝ) ^ 4)⁻¹ := by
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨hks', hkm⟩ := hk
      have hcond : R < ‖freq k‖ := by
        simp only [hs'def, Finset.mem_filter] at hks'
        exact hks'.2
      rw [if_pos hcond]
      have h4 : (m:ℝ) ≤ ‖freq k‖ := by
        rw [← hkm]
        exact natMax_cast_le_norm_freq k
      have hsq : (m:ℝ) ^ 2 ≤ ‖freq k‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h4 hmR.le,
          mul_le_mul_of_nonneg_right h4 ((hmR.trans_le h4).le)]
      have hq : (m:ℝ) ^ 4 ≤ ‖freq k‖ ^ 4 := by
        nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (m:ℝ)),
          mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖freq k‖)]
      exact inv_anti₀ (pow_pos hmR 4) hq
    calc (∑ k ∈ s'.filter fun k => natMax k = m,
          if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0)
        ≤ (s'.filter fun k => natMax k = m).card • ((m:ℝ) ^ 4)⁻¹ :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((s'.filter fun k => natMax k = m).card : ℝ) * ((m:ℝ) ^ 4)⁻¹ := by
          rw [nsmul_eq_mul]
      _ ≤ ((26 * m ^ 2 : ℕ) : ℝ) * ((m:ℝ) ^ 4)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_filter_natMax_le s' hmposn
      _ = 26 * ((m:ℝ) ^ 2)⁻¹ := by
          push_cast
          rw [show ((m:ℝ) ^ 4)⁻¹ = ((m:ℝ) ^ 2)⁻¹ * ((m:ℝ) ^ 2)⁻¹ by
            rw [show (4:ℕ) = 2 + 2 from rfl, pow_add, mul_inv]]
          rw [mul_assoc, ← mul_assoc ((m:ℝ) ^ 2), mul_inv_cancel₀ hm2, one_mul]
  calc (∑ k ∈ s, if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0)
      = ∑ k ∈ s', if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0 := heq
    _ = ∑ m ∈ Finset.Ioo (m₀ - 1) (M + 1), ∑ k ∈ s'.filter fun k => natMax k = m,
          if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0 :=
        (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ m ∈ Finset.Ioo (m₀ - 1) (M + 1), 26 * ((m:ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hfiber
    _ = 26 * ∑ m ∈ Finset.Ioo (m₀ - 1) (M + 1), ((m:ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 26 * (2 / (((m₀ - 1 : ℕ) : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le _ _) (by norm_num)
    _ = 52 / (m₀ : ℝ) := by
        have hc : ((m₀ - 1 : ℕ) : ℝ) + 1 = (m₀ : ℝ) := by
          have h1 : m₀ - 1 + 1 = m₀ := by omega
          exact_mod_cast h1
        rw [hc]
        ring
    _ ≤ 1000 / R := by
        rw [div_le_div_iff₀ (by linarith : (0:ℝ) < (m₀:ℝ)) hR0]
        have h1 : R ≤ (m₀:ℝ) * Real.sqrt 3 := by
          rw [div_le_iff₀ hs3] at hm₀ceil
          linarith [hm₀ceil]
        nlinarith [mul_nonneg (sub_nonneg.mpr hs3le) (le_trans zero_le_one hm₀1)]

/-! ### The low/high split layer -/

/-! ### Private helpers (Agent SPLIT) -/

private lemma pow_two_rpow (x : ℝ) : x ^ 2 = x ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private lemma inv_sq_eq {x : ℝ} (hx : x ≠ 0) :
    (x⁻¹) ^ 2 = x ^ 2 * (x ^ 4)⁻¹ := by
  rw [inv_pow, show (4 : ℕ) = 2 + 2 from rfl, pow_add, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 2 hx), one_mul]

/-- Cauchy–Schwarz on squares for tsums of nonnegative reals, in the exact
shape needed for the low/high shell bounds. -/
private lemma tsum_mul_sq_le {ι : Type*} {g h : ι → ℝ} (hg : ∀ k, 0 ≤ g k)
    (hh : ∀ k, 0 ≤ h k) (hg2 : Summable fun k => g k ^ 2)
    (hh2 : Summable fun k => h k ^ 2) :
    (∑' k, g k * h k) ^ 2 ≤ (∑' k, g k ^ 2) * ∑' k, h k ^ 2 := by
  have hgr : Summable fun k => g k ^ (2 : ℝ) := hg2.congr fun k => pow_two_rpow _
  have hhr : Summable fun k => h k ^ (2 : ℝ) := hh2.congr fun k => pow_two_rpow _
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := g) (g := h) hg hh hgr hhr
  have rf : ∑' k, g k ^ (2 : ℝ) = ∑' k, g k ^ 2 :=
    tsum_congr fun k => (pow_two_rpow _).symm
  have rg : ∑' k, h k ^ (2 : ℝ) = ∑' k, h k ^ 2 :=
    tsum_congr fun k => (pow_two_rpow _).symm
  rw [rf, rg] at cs
  have hG : 0 ≤ ∑' k, g k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hH : 0 ≤ ∑' k, h k ^ 2 := tsum_nonneg fun k => sq_nonneg _
  have hsq : (∑' k, g k ^ 2) ^ (1 / 2 : ℝ) * (∑' k, h k ^ 2) ^ (1 / 2 : ℝ)
      = Real.sqrt (∑' k, g k ^ 2) * Real.sqrt (∑' k, h k ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hsq] at cs
  have hnn : 0 ≤ ∑' k, g k * h k := tsum_nonneg fun k => mul_nonneg (hg k) (hh k)
  calc (∑' k, g k * h k) ^ 2 = (∑' k, g k * h k) * (∑' k, g k * h k) := pow_two _
    _ ≤ (Real.sqrt (∑' k, g k ^ 2) * Real.sqrt (∑' k, h k ^ 2)) *
        (Real.sqrt (∑' k, g k ^ 2) * Real.sqrt (∑' k, h k ^ 2)) :=
        mul_self_le_mul_self hnn cs
    _ = (∑' k, g k ^ 2) * ∑' k, h k ^ 2 := by
        rw [← pow_two, mul_pow, Real.sq_sqrt hG, Real.sq_sqrt hH]

/-! ### The summability export -/

lemma summable_norm_coeff {V : Type*} [NormedAddCommGroup V] {c : (Fin 3 → ℤ) → V}
    (hc0 : c 0 = 0) (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) :
    Summable fun k => ‖c k‖ := by
  refine (summable_inv_freq_pow_four.add hD).of_nonneg_of_le
    (fun k => norm_nonneg _) (fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [hc0, norm_zero]
    positivity
  · have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have key : ‖c k‖ = (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ 2 * ‖c k‖) := by
      field_simp
    calc ‖c k‖ = (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ 2 * ‖c k‖) := key
      _ ≤ (((‖freq k‖ ^ 2)⁻¹) ^ 2 + (‖freq k‖ ^ 2 * ‖c k‖) ^ 2) / 2 := by
          nlinarith [sq_nonneg ((‖freq k‖ ^ 2)⁻¹ - ‖freq k‖ ^ 2 * ‖c k‖)]
      _ = ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) / 2 := by ring
      _ ≤ (‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ 4 * ‖c k‖ ^ 2 := by
          have h1 : (0 : ℝ) ≤ (‖freq k‖ ^ 4)⁻¹ := by positivity
          have h2 : (0 : ℝ) ≤ ‖freq k‖ ^ 4 * ‖c k‖ ^ 2 := by positivity
          linarith

/-! ### Enstrophy is controlled by dissipation -/

lemma ens_le_dis {V : Type*} [NormedAddCommGroup V] {c : (Fin 3 → ℤ) → V}
    (hc0 : c 0 = 0) (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) :
    ens c ≤ dis c := by
  have hZ := summable_ens hc0 hD
  have hpt : ∀ k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 ≤ ‖freq k‖ ^ 4 * ‖c k‖ ^ 2 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hc0]
    · have h1 := one_le_norm_freq hk
      have hx : (0 : ℝ) ≤ ‖freq k‖ ^ 2 - 1 := by
        nlinarith [sq_nonneg (‖freq k‖ - 1)]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (‖freq k‖)) (sq_nonneg (‖c k‖))) hx]
  exact hZ.tsum_le_tsum hpt hD

/-! ### Vanishing enstrophy kills the sup-norm majorant -/

lemma spec1_eq_zero_of_ens_eq_zero {V : Type*} [NormedAddCommGroup V]
    {c : (Fin 3 → ℤ) → V} (hc0 : c 0 = 0)
    (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) (h : ens c = 0) :
    spec1 c = 0 := by
  have hZ : Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 := summable_ens hc0 hD
  have h0 : (∑' k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2) = 0 := h
  have hterm : ∀ k, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 = 0 := by
    intro k
    have hle : ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 ≤ ∑' j, ‖freq j‖ ^ 2 * ‖c j‖ ^ 2 :=
      hZ.le_tsum k fun j _ => mul_nonneg (by positivity) (sq_nonneg _)
    have hnn : (0 : ℝ) ≤ ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    rw [h0] at hle
    linarith
  have hall : ∀ k, ‖c k‖ = (0 : ℝ) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hc0]
    · have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
      have h2 : (0 : ℝ) < ‖freq k‖ ^ 2 := pow_pos hw 2
      have hsq : ‖c k‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp (hterm k) with h' | h'
        · exact absurd h' (ne_of_gt h2)
        · exact h'
      exact sq_eq_zero_iff.mp hsq
  have hfinal : spec1 c = ∑' _ : Fin 3 → ℤ, (0 : ℝ) := tsum_congr hall
  rw [hfinal]
  exact tsum_zero

/-! ### The low/high shell split -/

lemma spec1_sq_le_of_shell {V : Type*} [NormedAddCommGroup V] {bulk tail R : ℝ}
    (hbulk : (∑' k : Fin 3 → ℤ, if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) ≤ bulk)
    (htail : (∑' k : Fin 3 → ℤ, if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) ≤ tail)
    {c : (Fin 3 → ℤ) → V} (hc0 : c 0 = 0)
    (hD : Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) :
    spec1 c ^ 2 ≤ 2 * (bulk * ens c + tail * dis c) := by
  have hS : Summable fun k => ‖c k‖ := summable_norm_coeff hc0 hD
  have hZ : Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2 := summable_ens hc0 hD
  have hZnn : (0 : ℝ) ≤ ens c :=
    tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hDnn : (0 : ℝ) ≤ dis c :=
    tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  -- summability of the two ℓ¹ shell pieces
  have hSlowSum : Summable fun k => (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ) := by
    have hnn : ∀ k : Fin 3 → ℤ, (0 : ℝ) ≤ if ‖freq k‖ ≤ R then ‖c k‖ else 0 := fun k => by
      by_cases hcase : ‖freq k‖ ≤ R
      · rw [if_pos hcase]; exact norm_nonneg _
      · rw [if_neg hcase]
    have hle : ∀ k : Fin 3 → ℤ, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ) ≤ ‖c k‖ := fun k => by
      by_cases hcase : ‖freq k‖ ≤ R
      · rw [if_pos hcase]
      · rw [if_neg hcase]; exact norm_nonneg _
    exact hS.of_nonneg_of_le hnn hle
  have hShighSum : Summable fun k => (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ) := by
    have hnn : ∀ k : Fin 3 → ℤ, (0 : ℝ) ≤ if R < ‖freq k‖ then ‖c k‖ else 0 := fun k => by
      by_cases hcase : R < ‖freq k‖
      · rw [if_pos hcase]; exact norm_nonneg _
      · rw [if_neg hcase]
    have hle : ∀ k : Fin 3 → ℤ, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ) ≤ ‖c k‖ := fun k => by
      by_cases hcase : R < ‖freq k‖
      · rw [if_pos hcase]
      · rw [if_neg hcase]; exact norm_nonneg _
    exact hS.of_nonneg_of_le hnn hle
  -- the split of the ℓ¹ sum into complementary shells
  have hsplit : spec1 c = (∑' k, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ))
      + ∑' k, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ) := by
    have h1 : spec1 c = ∑' k, ((if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ)
        + if R < ‖freq k‖ then ‖c k‖ else 0) :=
      tsum_congr fun k => by
        by_cases hle : ‖freq k‖ ≤ R
        · rw [if_pos hle, if_neg (not_lt.mpr hle), add_zero]
        · rw [if_neg hle, if_pos (not_le.mp hle), zero_add]
    rw [h1]
    exact hSlowSum.tsum_add hShighSum
  -- low-shell Cauchy–Schwarz data
  have hgLnn : ∀ k : Fin 3 → ℤ,
      (0 : ℝ) ≤ if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 := fun k => by
    by_cases hcond : k ≠ 0 ∧ ‖freq k‖ ≤ R
    · rw [if_pos hcond]; positivity
    · rw [if_neg hcond]
  have hhLnn : ∀ k : Fin 3 → ℤ, (0 : ℝ) ≤ ‖freq k‖ * ‖c k‖ := fun k =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgL2 : Summable fun k => (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ) ^ 2 := by
    have hle2 : ∀ k : Fin 3 → ℤ,
        ((if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ)) ^ 2
          ≤ R ^ 2 * (‖freq k‖ ^ 4)⁻¹ := fun k => by
      by_cases hcond : k ≠ 0 ∧ ‖freq k‖ ≤ R
      · rw [if_pos hcond]
        obtain ⟨hk, hle⟩ := hcond
        have h1 : (1 : ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
        have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos h1
        have hR2 : ‖freq k‖ ^ 2 ≤ R ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hle)
            (by linarith : (0 : ℝ) ≤ R + ‖freq k‖)]
        rw [inv_sq_eq (ne_of_gt hw)]
        exact mul_le_mul_of_nonneg_right hR2 (by positivity)
      · rw [if_neg hcond]
        have h0 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
        rw [h0]
        positivity
    exact (summable_inv_freq_pow_four.mul_left (R ^ 2)).of_nonneg_of_le
      (fun k => sq_nonneg _) hle2
  -- high-shell Cauchy–Schwarz data
  have hgHnn : ∀ k : Fin 3 → ℤ,
      (0 : ℝ) ≤ if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 := fun k => by
    by_cases hcond : R < ‖freq k‖
    · rw [if_pos hcond]; positivity
    · rw [if_neg hcond]
  have hhHnn : ∀ k : Fin 3 → ℤ, (0 : ℝ) ≤ ‖freq k‖ ^ 2 * ‖c k‖ := fun k =>
    mul_nonneg (by positivity) (norm_nonneg _)
  have hgH2 : Summable fun k => (if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ) ^ 2 := by
    have hle2 : ∀ k : Fin 3 → ℤ,
        ((if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ)) ^ 2
          ≤ (‖freq k‖ ^ 4)⁻¹ := fun k => by
      by_cases hcond : R < ‖freq k‖
      · rw [if_pos hcond]
        exact le_of_eq (by ring)
      · rw [if_neg hcond]
        have h0 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
        rw [h0]
        positivity
    exact summable_inv_freq_pow_four.of_nonneg_of_le (fun k => sq_nonneg _) hle2
  -- pointwise product identities for the two shells
  have hlowpt : ∀ k : Fin 3 → ℤ, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ) =
      (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0) * (‖freq k‖ * ‖c k‖) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hc0]
    · by_cases hle : ‖freq k‖ ≤ R
      · rw [if_pos hle, if_pos ⟨hk, hle⟩]
        have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
        have hne : ‖freq k‖ ≠ 0 := ne_of_gt hw
        field_simp
      · rw [if_neg hle, if_neg (fun hcon => hle hcon.2), zero_mul]
  have hhighpt : ∀ k : Fin 3 → ℤ, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ) =
      (if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0) * (‖freq k‖ ^ 2 * ‖c k‖) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [hc0]
    · by_cases hlt : R < ‖freq k‖
      · rw [if_pos hlt, if_pos hlt]
        have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
        have hne : ‖freq k‖ ≠ 0 := ne_of_gt hw
        field_simp
      · rw [if_neg hlt, if_neg hlt, zero_mul]
  -- squares of the weight functions
  have hgL_sq : ∀ k : Fin 3 → ℤ,
      ((if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ)) ^ 2 =
      (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) := by
    intro k
    by_cases hcond : k ≠ 0 ∧ ‖freq k‖ ≤ R
    · rw [if_pos hcond, if_pos hcond, inv_pow]
    · rw [if_neg hcond, if_neg hcond]
      norm_num
  have hgH_sq : ∀ k : Fin 3 → ℤ,
      ((if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ)) ^ 2 =
      (if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) := by
    intro k
    by_cases hcond : R < ‖freq k‖
    · rw [if_pos hcond, if_pos hcond]
      ring
    · rw [if_neg hcond, if_neg hcond]
      norm_num
  -- low-shell bound: Slow² ≤ bulk · ens c
  have hlow : (∑' k, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ)) ^ 2 ≤ bulk * ens c := by
    have hhL2 : Summable fun k => (‖freq k‖ * ‖c k‖) ^ 2 := hZ.congr fun k => by ring
    have hcs : (∑' k, (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ)
          * (‖freq k‖ * ‖c k‖)) ^ 2
        ≤ (∑' k, ((if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ)) ^ 2)
          * ∑' k, (‖freq k‖ * ‖c k‖) ^ 2 :=
      tsum_mul_sq_le hgLnn hhLnn hgL2 hhL2
    have e1 : (∑' k, (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ)
          * (‖freq k‖ * ‖c k‖))
        = ∑' k, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ) := (tsum_congr hlowpt).symm
    have e2 : (∑' k, ((if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖)⁻¹ else 0 : ℝ)) ^ 2)
        = ∑' k : Fin 3 → ℤ, (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0) :=
      tsum_congr hgL_sq
    have e3 : (∑' k, (‖freq k‖ * ‖c k‖) ^ 2) = ens c := tsum_congr fun k => by ring
    rw [e1, e2, e3] at hcs
    calc (∑' k, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ)) ^ 2
        ≤ (∑' k : Fin 3 → ℤ, (if k ≠ 0 ∧ ‖freq k‖ ≤ R then (‖freq k‖ ^ 2)⁻¹ else 0))
          * ens c := hcs
      _ ≤ bulk * ens c := mul_le_mul_of_nonneg_right hbulk hZnn
  -- high-shell bound: Shigh² ≤ tail · dis c
  have hhigh : (∑' k, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ)) ^ 2 ≤ tail * dis c := by
    have hhH2 : Summable fun k => (‖freq k‖ ^ 2 * ‖c k‖) ^ 2 := hD.congr fun k => by ring
    have hcs : (∑' k, (if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ)
          * (‖freq k‖ ^ 2 * ‖c k‖)) ^ 2
        ≤ (∑' k, ((if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ)) ^ 2)
          * ∑' k, (‖freq k‖ ^ 2 * ‖c k‖) ^ 2 :=
      tsum_mul_sq_le hgHnn hhHnn hgH2 hhH2
    have e1 : (∑' k, (if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ)
          * (‖freq k‖ ^ 2 * ‖c k‖))
        = ∑' k, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ) := (tsum_congr hhighpt).symm
    have e2 : (∑' k, ((if R < ‖freq k‖ then (‖freq k‖ ^ 2)⁻¹ else 0 : ℝ)) ^ 2)
        = ∑' k : Fin 3 → ℤ, (if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0) :=
      tsum_congr hgH_sq
    have e3 : (∑' k, (‖freq k‖ ^ 2 * ‖c k‖) ^ 2) = dis c := tsum_congr fun k => by ring
    rw [e1, e2, e3] at hcs
    calc (∑' k, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ)) ^ 2
        ≤ (∑' k : Fin 3 → ℤ, (if R < ‖freq k‖ then (‖freq k‖ ^ 4)⁻¹ else 0))
          * dis c := hcs
      _ ≤ tail * dis c := mul_le_mul_of_nonneg_right htail hDnn
  -- compose: (Slow + Shigh)² ≤ 2(Slow² + Shigh²) ≤ 2(bulk·Z + tail·D)
  rw [hsplit]
  nlinarith [hlow, hhigh,
    sq_nonneg ((∑' k, (if ‖freq k‖ ≤ R then ‖c k‖ else 0 : ℝ))
      - ∑' k, (if R < ‖freq k‖ then ‖c k‖ else 0 : ℝ))]

/-- **W4 (sharp Agmon, on fourth powers).**  `S⁴ ≤ C · Z · D`: the
scale-critical sup-norm bound via the low/high frequency split at
`R = √(D/Z)`, composed from the shell bounds and the split lemma above. -/
theorem exists_spec1_pow_four_le_ens_mul_dis :
    ∃ C, 0 < C ∧ ∀ (c : (Fin 3 → ℤ) → V), c 0 = 0 →
      (Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) →
      spec1 c ^ 4 ≤ C * (ens c * dis c) := by
  refine ⟨2200 ^ 2, by norm_num, ?_⟩
  intro c hc0 hD
  have hensnn : 0 ≤ ens c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hdisnn : 0 ≤ dis c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  rcases eq_or_lt_of_le hensnn with hZ0 | hZpos
  · have hs0 : spec1 c = 0 := spec1_eq_zero_of_ens_eq_zero hc0 hD hZ0.symm
    rw [hs0, ← hZ0]
    norm_num
  · have hZD : ens c ≤ dis c := ens_le_dis hc0 hD
    have hdpos : 0 < dis c := lt_of_lt_of_le hZpos hZD
    set R : ℝ := Real.sqrt (dis c / ens c) with hRdef
    have hR1 : 1 ≤ R := by
      rw [hRdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hZpos]
      linarith
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
    have key := spec1_sq_le_of_shell (bulk_shell_bound hR1) (tail_shell_bound hR1) hc0 hD
    have hRsq : R ^ 2 = dis c / ens c := by
      rw [hRdef, Real.sq_sqrt (by positivity)]
    have hRZ : R * ens c = Real.sqrt (dis c * ens c) := by
      have h1 : (R * ens c) ^ 2 = dis c * ens c := by
        rw [mul_pow, hRsq]
        field_simp
        all_goals ring
      rw [← h1, Real.sqrt_sq (by positivity)]
    have hDR : dis c / R = Real.sqrt (dis c * ens c) := by
      have h1 : (dis c / R) ^ 2 = dis c * ens c := by
        rw [div_pow, hRsq, div_div_eq_mul_div, div_eq_iff hdpos.ne']
        ring
      rw [← h1, Real.sqrt_sq (by positivity)]
    have key2 : spec1 c ^ 2 ≤ 2200 * Real.sqrt (dis c * ens c) := by
      calc spec1 c ^ 2 ≤ 2 * (100 * R * ens c + 1000 / R * dis c) := key
        _ = 200 * (R * ens c) + 2000 * (dis c / R) := by ring
        _ = 2200 * Real.sqrt (dis c * ens c) := by rw [hRZ, hDR]; ring
    have hs2nn : 0 ≤ spec1 c ^ 2 := sq_nonneg _
    calc spec1 c ^ 4 = spec1 c ^ 2 * spec1 c ^ 2 := by ring
      _ ≤ (2200 * Real.sqrt (dis c * ens c)) * (2200 * Real.sqrt (dis c * ens c)) :=
          mul_self_le_mul_self hs2nn key2
      _ = 2200 ^ 2 * (ens c * dis c) := by
          rw [show (2200 * Real.sqrt (dis c * ens c)) * (2200 * Real.sqrt (dis c * ens c))
              = 2200 ^ 2 * (Real.sqrt (dis c * ens c) * Real.sqrt (dis c * ens c)) by ring,
            Real.mul_self_sqrt (by positivity)]
          ring

/-! ## M2.5: the trilinear majorant and its ℓ¹×ℓ²×ℓ² bound

The majorant is convention-free: any concrete convection pairing (leray-hopf's
`galerkinConvection`, the PDE's `∫(u·∇)v·w`) is pointwise dominated by it via
the triangle inequality, with its (2π)-factors absorbed into constants at the
Tier-2 bridge. -/

noncomputable def triMaj (a v w : (Fin 3 → ℤ) → ℝ) : ℝ :=
  ∑' k, a k * ∑' l, ‖freq l‖ * v l * w (-(k + l))

private lemma rpw2 (x : ℝ) : x ^ 2 = x ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private def shiftNeg (k : Fin 3 → ℤ) : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) :=
  (Equiv.addLeft k).trans (Equiv.neg _)

private lemma shiftNeg_apply (k l : Fin 3 → ℤ) : shiftNeg k l = -(k + l) := rfl

private lemma shift_tsum_sq (w : (Fin 3 → ℤ) → ℝ) (k : Fin 3 → ℤ) :
    ∑' l, w (-(k + l)) ^ 2 = ∑' m, w m ^ 2 := by
  have h := (shiftNeg k).tsum_eq (f := fun m => w m ^ 2)
  simp only [shiftNeg_apply] at h
  exact h

private lemma shift_summable_sq {w : (Fin 3 → ℤ) → ℝ}
    (hEw : Summable fun m => w m ^ 2) (k : Fin 3 → ℤ) :
    Summable fun l => w (-(k + l)) ^ 2 := by
  have h := ((shiftNeg k).summable_iff (f := fun m => w m ^ 2)).mpr hEw
  refine h.congr fun l => ?_
  simp only [Function.comp_apply, shiftNeg_apply]

private lemma inner_bound {v w : (Fin 3 → ℤ) → ℝ}
    (hv : ∀ l, 0 ≤ v l) (hw : ∀ m, 0 ≤ w m)
    (hZv : Summable fun l => ‖freq l‖ ^ 2 * v l ^ 2)
    (hEw : Summable fun m => w m ^ 2) (k : Fin 3 → ℤ) :
    (∑' l, ‖freq l‖ * v l * w (-(k + l))) ≤
      Real.sqrt (∑' l, ‖freq l‖ ^ 2 * v l ^ 2) * Real.sqrt (∑' m, w m ^ 2) := by
  have hf2 : Summable fun l => (‖freq l‖ * v l) ^ (2 : ℝ) :=
    hZv.congr fun l => by rw [← rpw2]; ring
  have hg2 : Summable fun l => (w (-(k + l))) ^ (2 : ℝ) :=
    (shift_summable_sq hEw k).congr fun l => by rw [← rpw2]
  have cs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two
    (f := fun l => ‖freq l‖ * v l) (g := fun l => w (-(k + l)))
    (fun l => mul_nonneg (norm_nonneg _) (hv l)) (fun l => hw _) hf2 hg2
  have rf : ∑' l, (‖freq l‖ * v l) ^ (2 : ℝ) = ∑' l, ‖freq l‖ ^ 2 * v l ^ 2 :=
    tsum_congr fun l => by rw [← rpw2]; ring
  have rg : ∑' l, (w (-(k + l))) ^ (2 : ℝ) = ∑' m, w m ^ 2 := by
    rw [show (∑' l, (w (-(k + l))) ^ (2 : ℝ)) = ∑' l, (w (-(k + l))) ^ 2 from
      tsum_congr fun l => by rw [← rpw2]]
    exact shift_tsum_sq w k
  rw [rf, rg] at cs
  calc (∑' l, ‖freq l‖ * v l * w (-(k + l)))
      ≤ (∑' l, ‖freq l‖ ^ 2 * v l ^ 2) ^ (1 / (2:ℝ)) * (∑' m, w m ^ 2) ^ (1 / (2:ℝ)) := cs
    _ = Real.sqrt (∑' l, ‖freq l‖ ^ 2 * v l ^ 2) * Real.sqrt (∑' m, w m ^ 2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **M2.5 (trilinear majorant bound).**  The convention-free ℓ¹×ℓ²×ℓ²
estimate: inner Cauchy–Schwarz in `l` with the `w`-slot reindexed along the
involution `l ↦ -(k+l)` of ℤ³, then the outer sum against the constant. -/
theorem triMaj_le {a v w : (Fin 3 → ℤ) → ℝ}
    (ha : ∀ k, 0 ≤ a k) (hv : ∀ l, 0 ≤ v l) (hw : ∀ m, 0 ≤ w m)
    (hSa : Summable a)
    (hZv : Summable fun l => ‖freq l‖ ^ 2 * v l ^ 2)
    (hEw : Summable fun m => w m ^ 2) :
    triMaj a v w ≤
      (∑' k, a k) * Real.sqrt (∑' l, ‖freq l‖ ^ 2 * v l ^ 2) *
        Real.sqrt (∑' m, w m ^ 2) := by
  set ZS := Real.sqrt (∑' l, ‖freq l‖ ^ 2 * v l ^ 2) with hZS
  set ES := Real.sqrt (∑' m, w m ^ 2) with hES
  have hinner : ∀ k, (∑' l, ‖freq l‖ * v l * w (-(k + l))) ≤ ZS * ES :=
    fun k => inner_bound hv hw hZv hEw k
  have hinner_nn : ∀ k, 0 ≤ ∑' l, ‖freq l‖ * v l * w (-(k + l)) :=
    fun k => tsum_nonneg fun l => mul_nonneg (mul_nonneg (norm_nonneg _) (hv l)) (hw _)
  have hle : ∀ k, a k * (∑' l, ‖freq l‖ * v l * w (-(k + l))) ≤ a k * (ZS * ES) :=
    fun k => mul_le_mul_of_nonneg_left (hinner k) (ha k)
  have hsum_right : Summable fun k => a k * (ZS * ES) := hSa.mul_right _
  have hsum_left : Summable fun k => a k * (∑' l, ‖freq l‖ * v l * w (-(k + l))) :=
    hsum_right.of_nonneg_of_le (fun k => mul_nonneg (ha k) (hinner_nn k)) hle
  calc triMaj a v w ≤ ∑' k, a k * (ZS * ES) :=
        Summable.tsum_le_tsum hle hsum_left hsum_right
    _ = (∑' k, a k) * (ZS * ES) := tsum_mul_right
    _ = (∑' k, a k) * ZS * ES := by ring

/-! ## M2.6: the master inequality (spectral majorant form)

`2·B ≤ ν·D + (K/ν³)·Z³` — the spectral form of `Ż ≤ -ν‖Δu‖² + (C/ν³)Z³`
(the `-2νD` term and the sign conventions live on the Tier-2 side of the
interface).  The Young step is closed by the pure-polynomial SOS certificate
`27(p+q)⁴ - 256·p³q = (p-3q)²·(27p² + 14pq + 3q²) ≥ 0`, so no real root ever
appears in a statement. -/
theorem master_inequality :
    ∃ K, 0 < K ∧ ∀ (c : (Fin 3 → ℤ) → V), c 0 = 0 →
      (Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) → ∀ ν : ℝ, 0 < ν →
      2 * triMaj (fun k => ‖c k‖) (fun l => ‖c l‖) (fun m => ‖freq m‖ ^ 2 * ‖c m‖) ≤
        ν * dis c + K / ν ^ 3 * ens c ^ 3 := by
  obtain ⟨C, hC, hW4⟩ := exists_spec1_pow_four_le_ens_mul_dis (V := V)
  refine ⟨27 * C / 16 + 1, by positivity, ?_⟩
  intro c hc0 hD ν hν
  have hensnn : 0 ≤ ens c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hdisnn : 0 ≤ dis c := tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
  set B := triMaj (fun k => ‖c k‖) (fun l => ‖c l‖) (fun m => ‖freq m‖ ^ 2 * ‖c m‖) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef, triMaj]
    refine tsum_nonneg fun k => mul_nonneg (norm_nonneg _) (tsum_nonneg fun l => ?_)
    positivity
  have hZv : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2 := summable_ens hc0 hD
  have hEw : Summable fun m => (‖freq m‖ ^ 2 * ‖c m‖) ^ 2 :=
    hD.congr fun m => by ring
  have h1 : B ≤ spec1 c * Real.sqrt (ens c) * Real.sqrt (dis c) := by
    have h := triMaj_le (a := fun k => ‖c k‖) (v := fun l => ‖c l‖)
      (w := fun m => ‖freq m‖ ^ 2 * ‖c m‖)
      (fun k => norm_nonneg _) (fun l => norm_nonneg _) (fun m => by positivity)
      (summable_norm_coeff hc0 hD) hZv hEw
    have e1 : (∑' l, ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) = ens c := rfl
    have e2 : (∑' m, (‖freq m‖ ^ 2 * ‖c m‖) ^ 2) = dis c :=
      tsum_congr fun m => by ring
    rw [e1, e2] at h
    exact h
  have h2 : B ^ 4 ≤ C * (ens c ^ 3 * dis c ^ 3) := by
    have hs4 := hW4 c hc0 hD
    have hsq1 : B * B ≤ (spec1 c * Real.sqrt (ens c) * Real.sqrt (dis c)) *
        (spec1 c * Real.sqrt (ens c) * Real.sqrt (dis c)) := mul_self_le_mul_self hBnn h1
    have hsq2 : B ^ 2 ≤ spec1 c ^ 2 * ens c * dis c := by
      calc B ^ 2 = B * B := by ring
        _ ≤ (spec1 c * Real.sqrt (ens c) * Real.sqrt (dis c)) *
            (spec1 c * Real.sqrt (ens c) * Real.sqrt (dis c)) := hsq1
        _ = spec1 c ^ 2 * (Real.sqrt (ens c) * Real.sqrt (ens c)) *
            (Real.sqrt (dis c) * Real.sqrt (dis c)) := by ring
        _ = spec1 c ^ 2 * ens c * dis c := by
            rw [Real.mul_self_sqrt hensnn, Real.mul_self_sqrt hdisnn]
    have hsq2nn : 0 ≤ B ^ 2 := sq_nonneg _
    have hsq3 : B ^ 4 ≤ (spec1 c ^ 2 * ens c * dis c) ^ 2 := by
      calc B ^ 4 = B ^ 2 * B ^ 2 := by ring
        _ ≤ (spec1 c ^ 2 * ens c * dis c) * (spec1 c ^ 2 * ens c * dis c) :=
            mul_self_le_mul_self hsq2nn hsq2
        _ = (spec1 c ^ 2 * ens c * dis c) ^ 2 := by ring
    calc B ^ 4 ≤ (spec1 c ^ 2 * ens c * dis c) ^ 2 := hsq3
      _ = spec1 c ^ 4 * (ens c ^ 2 * dis c ^ 2) := by ring
      _ ≤ C * (ens c * dis c) * (ens c ^ 2 * dis c ^ 2) := by
          have hnn : 0 ≤ ens c ^ 2 * dis c ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right hs4 hnn
      _ = C * (ens c ^ 3 * dis c ^ 3) := by ring
  set p := ν * dis c with hp
  set q := (27 * C / 16 + 1) / ν ^ 3 * ens c ^ 3 with hq
  have hpnn : 0 ≤ p := by positivity
  have hqnn : 0 ≤ q := by positivity
  have hp3q : 27 / 16 * B ^ 4 ≤ p ^ 3 * q := by
    have hexp : p ^ 3 * q = (27 * C / 16 + 1) * (ens c ^ 3 * dis c ^ 3) := by
      rw [hp, hq]
      field_simp
      all_goals ring
    rw [hexp]
    nlinarith [h2, mul_nonneg (mul_nonneg (pow_nonneg hensnn 3) (pow_nonneg hdisnn 3)) hC.le,
      mul_nonneg (pow_nonneg hensnn 3) (pow_nonneg hdisnn 3)]
  have hsum4 : (2 * B) ^ 4 ≤ (p + q) ^ 4 := by
    nlinarith [hp3q,
      mul_nonneg (sq_nonneg (p - 3 * q))
        (by positivity : (0:ℝ) ≤ 27 * p ^ 2 + 14 * p * q + 3 * q ^ 2),
      hpnn, hqnn, sq_nonneg B]
  have h2Bnn : 0 ≤ 2 * B := by linarith
  have hpqnn : 0 ≤ p + q := by linarith
  have hfinal : 2 * B ≤ p + q := by
    by_contra hcon
    push_neg at hcon
    have h1' : (p + q) * (p + q) < (2 * B) * (2 * B) :=
      mul_self_lt_mul_self hpqnn hcon
    have h2' : (p + q) ^ 2 < (2 * B) ^ 2 := by nlinarith
    have h3' : (p + q) ^ 2 * (p + q) ^ 2 < (2 * B) ^ 2 * (2 * B) ^ 2 :=
      mul_self_lt_mul_self (by positivity) h2'
    nlinarith [hsum4]
  linarith

end TheoremB
