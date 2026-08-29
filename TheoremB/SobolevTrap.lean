/-
# Galerkin Sobolev propagation (Tier 6, wave 3)

The per-level finite Groenwall on Galerkin flows: consuming the frozen W2
absorbed-pairing conclusion as an explicit HYPOTHESIS (the sibling wave's
capstone, deliberately not imported), the order-m Sobolev mass of a finitely
supported Leray-projected Galerkin trajectory grows at most by the factor
(1 + e^{KT}) on the window, with a box-free constant.

Route (every move has a compiled twin): finite collapse FIRST (the
GalerkinTrap hen_deriv pattern), coefficient-wise product rule
(hasDerivAt_weighted_finset_sum_sq), DivFree propagation along the flow
(divFree_propagates_on) drops the Leray projection
(inner_lerayProj_of_divFree), the absorbed pairing eats half the
dissipation kept as an equality until the last step, and the
constant-source Groenwall (gronwall_const_source) with the shift trick
f := sob m (c t) - sob m (c 0), A := K * sob m (c 0) closes.

The merge glue deriving the frozen `galerkin_sobolev_bound` from
`sobolev_pairing_absorbed` + this file's theorem sits in the comment block
at the end, for the orchestrator to compile at merge.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.SobolevNorms
import TheoremB.SobolevPairing
import TheoremB.GalerkinLocal
import TheoremB.FullUnique

namespace TheoremB

open Set

/-! ## The m = 0 remark: level zero is the energy budget itself -/

/-- The `m = 0` rung of the Sobolev ladder needs no Groenwall: `sob 0 = en`
is bounded by the trap's energy budget directly. -/
lemma sob_zero_bound {E : ℝ} {c : (Fin 3 → ℤ) → Vel} (h : en c ≤ E) :
    sob 0 c ≤ E := by
  rw [sob_zero_eq_en]
  exact h

/-! ## The finite collapse -/

/-- The Sobolev mass of a finitely supported field collapses to the box sum. -/
private lemma sob_eq_finset_sum (m : ℕ) {S : Finset (Fin 3 → ℤ)}
    {c : (Fin 3 → ℤ) → Vel} (hsupp : ∀ k ∉ S, c k = 0) :
    sob m c = ∑ k ∈ S, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 := by
  have h : sob m c = ∑' k, ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 := rfl
  rw [h]
  exact weighted_tsum_eq_sum (fun k => ‖freq k‖ ^ (2 * m)) hsupp

/-! ## The weighted pairing split: dissipation kept as an equality -/

/-- Per-box split of the weighted ODE pairing: the viscous part is EXACTLY
`-2ν` times the collapsed level-`(m+1)` Sobolev mass (T4 audit lesson: never
absorb dissipation early), the forcing part is the raw weighted pairing. -/
private lemma weighted_split {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (ν : ℝ) (m : ℕ) (S : Finset (Fin 3 → ℤ))
    (c F : (Fin 3 → ℤ) → V) :
    (∑ k ∈ S, ‖freq k‖ ^ (2 * m) *
        (2 * inner ℝ ((-(ν * ‖freq k‖ ^ 2)) • c k + F k) (c k))) =
      -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ (2 * (m + 1)) * ‖c k‖ ^ 2) +
        2 * ∑ k ∈ S, ‖freq k‖ ^ (2 * m) * inner ℝ (F k) (c k) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hterm : 2 * inner ℝ ((-(ν * ‖freq k‖ ^ 2)) • c k + F k) (c k) =
      -(2 * (ν * ‖freq k‖ ^ 2) * ‖c k‖ ^ 2) + 2 * inner ℝ (F k) (c k) := by
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [hterm, ← norm_sq_mul_pow k m]
  ring

/-! ## The W3 capstone, conditional on the frozen W2 pairing -/

set_option linter.unusedVariables false in
/-- **Galerkin Sobolev propagation, pairing-conditional form.** The `hpair`
hypothesis is EXACTLY the frozen W2 conclusion `sobolev_pairing_absorbed`
for this `(ν, E, Z, m)` with its `K` given; the merge glue at the end of
this file discharges it. Finite collapse first, product rule, DivFree
propagation drops the Leray projection, the absorbed pairing eats half the
dissipation, constant-source Groenwall with the shift trick.
(`hE`, `hZ`, `hm` are carried by the frozen interface — the budgets and the
level bound are consumed by W2 in DERIVING `hpair`, not here.) -/
theorem galerkin_sobolev_bound_of_pairing {ν E Z : ℝ} (hν : 0 < ν) (hE : 0 ≤ E) (hZ : 0 ≤ Z) (m : ℕ) (hm : 1 ≤ m)
    (K : ℝ) (hK : 0 < K)
    (hpair : ∀ {S : Finset (Fin 3 → ℤ)}, (0 : Fin 3 → ℤ) ∉ S →
      ∀ {c : (Fin 3 → ℤ) → Vel}, (∀ k ∉ S, c k = 0) → en c ≤ E → ens c ≤ Z →
        2 * |∑ k ∈ S, ‖freq k‖ ^ (2*m) * inner ℝ (convGal S c k) (c k)| ≤
          ν * sob (m+1) c + K * sob m c) :
    ∀ {T : ℝ} {S : Finset (Fin 3 → ℤ)}, (0 : Fin 3 → ℤ) ∉ S →
      ∀ {c : ℝ → (Fin 3 → ℤ) → Vel}, (∀ t, ∀ k ∉ S, c t k = 0) → DivFree (c 0) →
      (∀ t ∈ Set.Icc 0 T, ∀ k, HasDerivAt (fun s => c s k)
        (-(ν * ‖freq k‖^2) • c t k + lerayProj k (convGal S (c t) k)) t) →
      (∀ t ∈ Set.Icc 0 T, en (c t) ≤ E ∧ ens (c t) ≤ Z) →
      ∀ t ∈ Set.Icc 0 T, sob m (c t) ≤ sob m (c 0) * (1 + Real.exp (K * T)) := by
  intro T S hS0 c hsupp hdiv0 hODE hbud t ht
  -- divergence-freeness propagates along the flow on the window
  have hdiv : ∀ s ∈ Icc (0:ℝ) T, DivFree (c s) :=
    divFree_propagates_on hν.le hODE hdiv0
  -- the ODE right-hand side
  set cd : ℝ → (Fin 3 → ℤ) → Vel := fun s k =>
    (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convGal S (c s) k) with hcd
  -- collapse identities (support is global in time, so these hold at every s)
  have hsob_eq : ∀ s, sob m (c s) =
      ∑ k ∈ S, ‖freq k‖ ^ (2 * m) * ‖c s k‖ ^ 2 :=
    fun s => sob_eq_finset_sum m (hsupp s)
  have hsob1_eq : ∀ s, sob (m + 1) (c s) =
      ∑ k ∈ S, ‖freq k‖ ^ (2 * (m + 1)) * ‖c s k‖ ^ 2 :=
    fun s => sob_eq_finset_sum (m + 1) (hsupp s)
  -- derivative of the Sobolev history via the finite collapse (hen_deriv pattern)
  have hderiv : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt (fun u => sob m (c u))
      (∑ k ∈ S, ‖freq k‖ ^ (2 * m) * (2 * inner ℝ (cd s k) (c s k))) s := by
    intro s hs
    have h := hasDerivAt_weighted_finset_sum_sq (fun k => ‖freq k‖ ^ (2 * m)) S
      (c' := cd) (fun k => hODE s hs k)
    have heq : (fun u => ∑ k ∈ S, ‖freq k‖ ^ (2 * m) * ‖c u k‖ ^ 2) =
        fun u => sob m (c u) := by
      funext u
      rw [hsob_eq u]
    rw [heq] at h
    exact h
  -- the differential inequality on the interior
  have hdbound : ∀ s ∈ Ioo (0:ℝ) T,
      (∑ k ∈ S, ‖freq k‖ ^ (2 * m) * (2 * inner ℝ (cd s k) (c s k))) ≤
        K * sob m (c s) := by
    intro s hs
    have hsIcc : s ∈ Icc (0:ℝ) T := Ioo_subset_Icc_self hs
    -- dissipation split, kept as an equality
    have hsplit : (∑ k ∈ S, ‖freq k‖ ^ (2 * m) * (2 * inner ℝ (cd s k) (c s k))) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ (2 * (m + 1)) * ‖c s k‖ ^ 2) +
          2 * ∑ k ∈ S, ‖freq k‖ ^ (2 * m) *
            inner ℝ (lerayProj k (convGal S (c s) k)) (c s k) :=
      weighted_split ν m S (c s) fun k => lerayProj k (convGal S (c s) k)
    -- the Leray projection is invisible against the divergence-free flow
    have hproj_sum : (∑ k ∈ S, ‖freq k‖ ^ (2 * m) *
        inner ℝ (lerayProj k (convGal S (c s) k)) (c s k)) =
        ∑ k ∈ S, ‖freq k‖ ^ (2 * m) * inner ℝ (convGal S (c s) k) (c s k) :=
      Finset.sum_congr rfl fun k _ => by
        rw [inner_lerayProj_of_divFree (hdiv s hsIcc) k]
    -- the frozen pairing at this instant, budgets from the trap hypothesis
    have hp := hpair hS0 (hsupp s) (hbud s hsIcc).1 (hbud s hsIcc).2
    rw [hsob1_eq s] at hp
    have habs := le_abs_self
      (∑ k ∈ S, ‖freq k‖ ^ (2 * m) * inner ℝ (convGal S (c s) k) (c s k))
    have hsig : (0:ℝ) ≤ ∑ k ∈ S, ‖freq k‖ ^ (2 * (m + 1)) * ‖c s k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (sq_nonneg _)
    have hνsig : (0:ℝ) ≤ ν * ∑ k ∈ S, ‖freq k‖ ^ (2 * (m + 1)) * ‖c s k‖ ^ 2 :=
      mul_nonneg hν.le hsig
    rw [hsplit, hproj_sum]
    linarith
  -- continuity of the Sobolev history on the closed window
  have hcont : ContinuousOn (fun u => sob m (c u)) (Icc 0 T) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  -- Groenwall with the shift trick: f := sob m (c t) - sob m (c 0)
  have hA : 0 ≤ K * sob m (c 0) := mul_nonneg hK.le (sob_nonneg m (c 0))
  have hfc : ContinuousOn (fun u => sob m (c u) - sob m (c 0)) (Icc 0 T) :=
    hcont.sub continuousOn_const
  have hf0 : sob m (c 0) - sob m (c 0) = 0 := sub_self _
  have hfd : ∀ s ∈ Ioo (0:ℝ) T, ∃ f',
      HasDerivAt (fun u => sob m (c u) - sob m (c 0)) f' s ∧
      f' ≤ K * (sob m (c s) - sob m (c 0)) + K * sob m (c 0) := by
    intro s hs
    refine ⟨∑ k ∈ S, ‖freq k‖ ^ (2 * m) * (2 * inner ℝ (cd s k) (c s k)),
      (hderiv s (Ioo_subset_Icc_self hs)).sub_const _, ?_⟩
    have hb := hdbound s hs
    linarith
  have hG : sob m (c t) - sob m (c 0) ≤
      K * sob m (c 0) / K * Real.exp (K * T) :=
    gronwall_const_source hK hA hfc hf0 hfd t ht
  have hKne : K ≠ 0 := ne_of_gt hK
  have hcancel : K * sob m (c 0) / K = sob m (c 0) := by
    rw [mul_comm, mul_div_assoc, div_self hKne, mul_one]
  rw [hcancel] at hG
  have hexpand : sob m (c 0) * (1 + Real.exp (K * T)) =
      sob m (c 0) + sob m (c 0) * Real.exp (K * T) := by ring
  rw [hexpand]
  linarith

/-- **Galerkin Sobolev propagation** (the frozen W3 capstone): on any window,
a finitely supported Leray-projected Galerkin trajectory with divergence-free
datum and trapped energy/enstrophy budgets keeps every Sobolev level, with a
box-free constant: `sob m (c t) ≤ sob m (c 0) · (1 + e^{KT})`. The pairing
hypothesis is discharged by `sobolev_pairing_absorbed`. -/
theorem galerkin_sobolev_bound {ν : ℝ} (hν : 0 < ν) (E Z : ℝ)
    (hE : 0 ≤ E) (hZ : 0 ≤ Z) (m : ℕ) (hm : 1 ≤ m) :
    ∃ K, 0 < K ∧ ∀ {T : ℝ} {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t, ∀ k ∉ S, c t k = 0) → DivFree (c 0) →
      (∀ t ∈ Set.Icc 0 T, ∀ k, HasDerivAt (fun s => c s k)
        (-(ν * ‖freq k‖^2) • c t k + lerayProj k (convGal S (c t) k)) t) →
      (∀ t ∈ Set.Icc 0 T, en (c t) ≤ E ∧ ens (c t) ≤ Z) →
      ∀ t ∈ Set.Icc 0 T, sob m (c t) ≤ sob m (c 0) * (1 + Real.exp (K * T)) := by
  obtain ⟨K, hK, hpair⟩ := sobolev_pairing_absorbed hν hE hZ m hm
  refine ⟨K, hK, ?_⟩
  intro T S hS0 c hsupp hdiv0 hODE hbud
  exact galerkin_sobolev_bound_of_pairing hν hE hZ m hm K hK hpair
    hS0 hsupp hdiv0 hODE hbud

end TheoremB
