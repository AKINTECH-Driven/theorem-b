/-
  TheoremB/SpectralNorms.lean
  Tier 1 of the Theorem B campaign (M2 wave 1, 27 Aug 2026).

  The spectral (Fourier-side) layer for the enstrophy master inequality on
  the 3-torus: a velocity field is its coefficient family over the frequency
  lattice ℤ³, and energy `en`, enstrophy `ens`, dissipation `dis`, and the
  sup-norm majorant `spec1` are weighted sums.  Weights are BARE Euclidean
  ‖k‖; the (2π)-factors of any particular Fourier convention are absorbed by
  the abstract constants at the Tier-2 bridge (see rung3-tier1-blueprint.md).

  FROZEN (M2 wave 1): summable_inv_freq_pow_four (W1), ens_sq_le_en_mul_dis
  (W2), exists_spec1_sq_le_dis (W3), exists_spec1_pow_four_le_ens_mul_dis
  (W4).  W1-W3 are proved below; W4 (sharp Agmon) is the declared open
  target and carries a sorry — it is NOT in the axiom audit until closed.

  STATUS: W1-W3 claimed only insofar as scripts/check_axioms.sh reports
  GREEN for them on the target machine.
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

/-- **W4 (sharp Agmon, on fourth powers).**  `S⁴ ≤ C · Z · D`: the
scale-critical sup-norm bound via the low/high frequency split.  DECLARED
TARGET, still open — kept OUT of the axiom audit until closed. -/
theorem exists_spec1_pow_four_le_ens_mul_dis :
    ∃ C, 0 < C ∧ ∀ (c : (Fin 3 → ℤ) → V), c 0 = 0 →
      (Summable fun k => ‖freq k‖ ^ 4 * ‖c k‖ ^ 2) →
      spec1 c ^ 4 ≤ C * (ens c * dis c) := by
  sorry

end TheoremB
