/-
# Uniform flow estimates (Tier 3, wave 2)

The Galerkin right-hand side is bounded by the energy/enstrophy budgets
uniformly in the box, so every mode curve of a budgeted flow is Lipschitz
with a box-independent constant and lives in the Arzela-Ascoli candidate
set of `TheoremB.ModeExtraction`.
-/
import TheoremB.NSFull
import TheoremB.ModeExtraction
import TheoremB.GalerkinFlow

namespace TheoremB

open Set

-- ==================== Agent FLEET-A: private helpers ====================

private lemma flaDotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

private lemma flaLerayProj_zero (k : Fin 3 → ℤ) : lerayProj k 0 = 0 := by
  simp [lerayProj, flaDotR_zero_left]

-- ==================== Agent FLEET-A: uniform flow estimates ====================

/-- The Galerkin right-hand side is uniformly bounded by the energy and
enstrophy budgets: `‖-ν‖k‖²·c k + P_k(convGal)‖ ≤ ν‖k‖²√E + 2√E√Z`. -/
theorem galRHS_norm_le {ν E Z : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hen : en c ≤ E) (hens : ens c ≤ Z)
    (k : Fin 3 → ℤ) :
    ‖(-(ν * ‖freq k‖ ^ 2)) • c k + lerayProj k (convGal S c k)‖ ≤
      ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z) := by
  have hνk : 0 ≤ ν * ‖freq k‖ ^ 2 := by positivity
  have hEs : Real.sqrt (en c) ≤ Real.sqrt E := Real.sqrt_le_sqrt hen
  have hcE : ‖c k‖ ≤ Real.sqrt E := (coeff_le_sqrt_en hsupp k).trans hEs
  have h1 : ‖(-(ν * ‖freq k‖ ^ 2)) • c k‖ ≤ ν * ‖freq k‖ ^ 2 * Real.sqrt E := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hνk]
    exact mul_le_mul_of_nonneg_left hcE hνk
  have h2 : ‖lerayProj k (convGal S c k)‖ ≤ 2 * (Real.sqrt E * Real.sqrt Z) := by
    by_cases hk : k ∈ S
    · have hE' : Summable fun l => ‖c l‖ ^ 2 :=
        summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
      have hZ' : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2 :=
        summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
      rw [← convFull_eq_convGal hsupp hk]
      calc ‖lerayProj k (convFull c k)‖
          ≤ 2 * ‖convFull c k‖ := norm_lerayProj_le k _
        _ ≤ 2 * (Real.sqrt (en c) * Real.sqrt (ens c)) := by
            have := norm_convFull_le_sqrt hE' hZ' k
            linarith
        _ ≤ 2 * (Real.sqrt E * Real.sqrt Z) := by
            have h := mul_le_mul hEs (Real.sqrt_le_sqrt hens)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            linarith
    · have hg : convGal S c k = 0 := by simp [convGal, hk]
      rw [hg, flaLerayProj_zero, norm_zero]
      positivity
  calc ‖(-(ν * ‖freq k‖ ^ 2)) • c k + lerayProj k (convGal S c k)‖
      ≤ ‖(-(ν * ‖freq k‖ ^ 2)) • c k‖ + ‖lerayProj k (convGal S c k)‖ :=
        norm_add_le _ _
    _ ≤ ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z) :=
        add_le_add h1 h2

/-- Along an energy/enstrophy-budgeted Galerkin flow, every mode curve is
Lipschitz on the window with the uniform RHS constant. -/
theorem flow_mode_lipschitzOnWith {ν E Z T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {S : Finset (Fin 3 → ℤ)} {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ (t : ℝ) k, k ∉ S → c t k = 0)
    (hODE : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t)
    (hen : ∀ t ∈ Set.Icc (0:ℝ) T, en (c t) ≤ E)
    (hens : ∀ t ∈ Set.Icc (0:ℝ) T, ens (c t) ≤ Z) (k : Fin 3 → ℤ) :
    LipschitzOnWith (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
      2 * (Real.sqrt E * Real.sqrt Z))) (fun t => c t k) (Set.Icc (0:ℝ) T) := by
  refine (convex_Icc (0:ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun t => (-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k))
    (fun t ht => (hODE t ht k).hasDerivWithinAt) (fun t ht => ?_)
  rw [← norm_toNNReal]
  exact Real.toNNReal_mono
    (galRHS_norm_le hν hE0 hZ0 (hsupp t) (hen t ht) (hens t ht) k)

/-- Each mode curve of a budgeted Galerkin flow lives in the Arzela-Ascoli
candidate set `modeSet T √E L(k)` as a continuous map on the window. -/
theorem flow_mode_mem_modeSet {ν E Z T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {S : Finset (Fin 3 → ℤ)} {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ (t : ℝ) k, k ∉ S → c t k = 0)
    (hODE : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t)
    (hen : ∀ t ∈ Set.Icc (0:ℝ) T, en (c t) ≤ E)
    (hens : ∀ t ∈ Set.Icc (0:ℝ) T, ens (c t) ≤ Z) (k : Fin 3 → ℤ) :
    ∃ f : C(Set.Icc (0:ℝ) T, Vel), (∀ t : Set.Icc (0:ℝ) T, f t = c t.val k) ∧
      f ∈ modeSet T (Real.sqrt E) (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
        2 * (Real.sqrt E * Real.sqrt Z))) := by
  have hlip := flow_mode_lipschitzOnWith hν hE0 hZ0 hsupp hODE hen hens k
  have hlipR : LipschitzWith (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
      2 * (Real.sqrt E * Real.sqrt Z)))
      ((Set.Icc (0:ℝ) T).restrict fun t => c t k) :=
    lipschitzOnWith_iff_restrict.1 hlip
  refine ⟨⟨fun t => c t.val k, hlipR.continuous⟩, fun t => rfl, hlipR, fun t => ?_⟩
  rw [mem_closedBall_zero_iff]
  show ‖c t.val k‖ ≤ Real.sqrt E
  exact (coeff_le_sqrt_en (hsupp t.val) k).trans (Real.sqrt_le_sqrt (hen t.val t.2))

end TheoremB
