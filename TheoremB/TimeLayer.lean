/-
# The time layer engine (Tier 6, wave W5c)

Abstract spectral-side engine lemmas for the classical layer's time
direction. DELIVERED HERE (wave W5c, part 1 of the planned engine — the
build was interrupted, see the pending list below):

1. `quarticKernel` — the lattice weight `Σ' k, (‖freq k‖⁴)⁻¹`, certified
   summable by `summable_inv_freq_pow_four`.
2. `tsum_weighted_norm_le` — the QUANTITATIVE weighted ℓ¹ bound (the
   uniform-in-time workhorse; `summable_weighted_norm` in SobolevNorms is
   its qualitative twin): `Σ ‖k‖^p ‖c k‖ ≤ (quarticKernel + Σ ‖k‖^(2(p+2)) ‖c k‖²)/2`
   by AM-GM against `(‖k‖⁴)⁻¹`.
3. `tsum_weighted_norm_le_of_bound` — its window form: a Sobolev-summand
   bound `B` at level `p+2` caps the weighted ℓ¹ mass by
   `(quarticKernel + B)/2`, uniformly in whatever parameter carries `B`
   (this is what turns the per-time `sob` bounds of
   `ns_full_global_flow_sobolev` into t-uniform ℓ¹ majorants on windows).

PENDING (specified in context/rung8-tier6-blueprint.md, not yet built):
the discrete-Young ℓ¹ convolution majorant on ℤ³ and its
`convFull` corollary; term-wise time differentiation of weighted mode
sums via `hasDerivAt_tsum_of_isPreconnected` on open slabs; continuity of
the derivative sum; and the canonical-flow package assembling those into
`∂_t u` for the Navier-Stokes right-hand side.

Junk-tsum discipline: every tsum statement carries its Summable
certificate as a hypothesis; `quarticKernel`'s defining tsum is certified
by `summable_inv_freq_pow_four`.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.SobolevNorms

namespace TheoremB

open Set

/-! ## The quartic lattice kernel -/

/-- The quartic lattice kernel `Σ' k, (‖freq k‖⁴)⁻¹` (the `k = 0` term is
`0⁻¹ = 0`).  Summability certificate: `summable_inv_freq_pow_four`. -/
noncomputable def quarticKernel : ℝ := ∑' k : Fin 3 → ℤ, (‖freq k‖ ^ 4)⁻¹

lemma quarticKernel_nonneg : 0 ≤ quarticKernel :=
  tsum_nonneg fun k => by positivity

/-! ## 1. The quantitative weighted ℓ¹ bound -/

/-- **The uniform-in-time workhorse.**  Two orders of extra Sobolev
regularity buy a QUANTITATIVE weighted ℓ¹ bound:
`Σ ‖k‖^p ‖c k‖ ≤ (quarticKernel + Σ ‖k‖^(2(p+2)) ‖c k‖²)/2`
(mean-zero fields; AM-GM against the lattice weight `(‖k‖⁴)⁻¹`, exactly the
`summable_weighted_norm` skeleton with the bound kept). -/
theorem tsum_weighted_norm_le {p : ℕ} {c : (Fin 3 → ℤ) → Vel} (hc0 : c 0 = 0)
    (h : Summable fun k => ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) :
    (∑' k, ‖freq k‖ ^ p * ‖c k‖) ≤
      (quarticKernel + ∑' k, ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
  have hL : Summable fun k => ‖freq k‖ ^ p * ‖c k‖ := summable_weighted_norm hc0 h
  have hpt : ∀ k, ‖freq k‖ ^ p * ‖c k‖ ≤
      ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
    intro k
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
  have hR : Summable fun k =>
      ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 :=
    (summable_inv_freq_pow_four.add h).div_const 2
  calc (∑' k, ‖freq k‖ ^ p * ‖c k‖)
      ≤ ∑' k, ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 :=
        hL.tsum_le_tsum hpt hR
    _ = (quarticKernel + ∑' k, ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
        have e3 : ∀ k : Fin 3 → ℤ,
            ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 =
            ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) * (2:ℝ)⁻¹ :=
          fun k => div_eq_mul_inv _ _
        rw [tsum_congr e3, tsum_mul_right,
          summable_inv_freq_pow_four.tsum_add h]
        have hq : (∑' k : Fin 3 → ℤ, (‖freq k‖ ^ 4)⁻¹) = quarticKernel := rfl
        rw [hq, div_eq_mul_inv]

/-- Window form of `tsum_weighted_norm_le`: a bound on the level-`(p+2)`
Sobolev summand bounds the weighted ℓ¹ mass, uniformly. -/
theorem tsum_weighted_norm_le_of_bound {p : ℕ} {c : (Fin 3 → ℤ) → Vel} {B : ℝ}
    (hc0 : c 0 = 0)
    (h : Summable fun k => ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2)
    (hB : (∑' k, ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) ≤ B) :
    (∑' k, ‖freq k‖ ^ p * ‖c k‖) ≤ (quarticKernel + B) / 2 :=
  (tsum_weighted_norm_le hc0 h).trans (by linarith)

end TheoremB
