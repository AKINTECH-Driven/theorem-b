/-
# Ambient decay for the exhaustion family (Tier 7, wave W-R0b, step 1)

W-R0a proves exponential energy decay for a Galerkin flow whose forcing
has nonpositive energy pairing. This file discharges that hypothesis for
the actual Navier-Stokes Galerkin system - Leray-projected, as the
campaign runs it - and then COMPOSES the result with `galerkin_family`,
the exhaustion the Tier-3 limit is built from.

That composition is the point. The Tier-6 audit register requires a
compiled composition probe against a REAL producer at every tier, and
W-R0a shipped without one: its `hODE` was frozen on all of `ℝ`, which no
producer in this campaign exports, so it was type-correct and composable
with nothing. `galerkin_family_decay` below is that probe, now passing.

With it, route (α) for the eternal-flow transfer is unblocked: the decay
is a per-time bound on every member of the exhaustion family, uniform in
the box radius, which is exactly the shape `en_limit_le` carries through
the Tier-3 extraction. No ℓ¹ is needed anywhere - the energy pairing
vanishes EXACTLY at the Galerkin level, over a finite sum.
-/
import TheoremB.TheoremBGlobal
import TheoremB.GalerkinLocal
import TheoremB.EnergyDecay

namespace TheoremB

open Set

/-- **The Leray-projected Galerkin system decays at least at rate `2ν`.** The
sibling of `ns_galerkin_trap_leray`, with its `en (c t) ≤ en (c 0)`
clause strengthened to an explicit rate.

The Leray projection is invisible to the energy pairing on a
divergence-free field (`inner_lerayProj_of_divFree`), so
`convGal_energy_pairing` discharges W-R0a's hypothesis exactly, with no
inequality slack. -/
theorem ns_galerkin_decay_leray {ν T : ℝ} (hν : 0 < ν)
    {S : Finset (Fin 3 → ℤ)} (hS0 : (0 : Fin 3 → ℤ) ∉ S)
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ t k, k ∉ S → c t k = 0)
    (hreal : ∀ t ∈ Icc (0:ℝ) T, RealField (c t))
    (hdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t))
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) :
    ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en (c 0) * Real.exp (-(2 * ν * t)) := by
  refine galerkin_energy_decay hν hS0 hsupp hODE ?_
  intro t ht
  have htIcc : t ∈ Icc (0:ℝ) T := Ioo_subset_Icc_self ht
  have hpair : ∀ k, inner ℝ (lerayProj k (convGal S (c t) k)) (c t k) =
      inner ℝ (convGal S (c t) k) (c t k) := fun k =>
    inner_lerayProj_of_divFree (hdiv t htIcc) k _
  have h := convGal_energy_pairing (fun k hk => hsupp t k hk)
    (hreal t htIcc) (hdiv t htIcc)
  calc (∑ k ∈ S, 2 * inner ℝ (lerayProj k (convGal S (c t) k)) (c t k))
      = ∑ k ∈ S, 2 * inner ℝ (convGal S (c t) k) (c t k) :=
        Finset.sum_congr rfl fun k _ => by rw [hpair k]
    _ ≤ 0 := le_of_eq h

/-- **W-R0b step 1: the composition probe.** Every member of the
exhaustion family `galerkin_family` builds decays at least at rate `2ν` from the
FULL datum's energy, uniformly in the box radius `R`.

Uniformity in `R` is what matters: the bound on the right is
`en c₀ · exp(−2νt)`, not `en (truncate (boxS R) c₀) · exp(−2νt)`, so it
survives the Tier-3 box exhaustion unchanged and can be carried to the
limit by `en_limit_le` exactly as the trap clauses are. -/
theorem galerkin_family_decay :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ (R : ℕ) (T : ℝ), ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = truncate (boxS R) c₀ ∧
        (∀ (t : ℝ) k, k ∉ boxS R → c t k = 0) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k +
            lerayProj k (convGal (boxS R) (c t) k)) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ * Real.exp (-(2 * ν * t))) := by
  obtain ⟨κ, hκ, hfam⟩ := galerkin_family
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hreal hdiv h0 R T
  obtain ⟨c, hc0, hcs, hcODE, hctrap⟩ := hfam hν hE hZ hreal hdiv h0 R T
  refine ⟨c, hc0, hcs, hcODE, hctrap, ?_⟩
  -- reality and divergence-freeness along the flow, from the data
  have hdiv0 : DivFree (c 0) := by
    rw [hc0]; exact divFree_truncate hdiv _
  have hreal0 : RealField (c 0) := by
    rw [hc0]; exact realField_truncate hreal (boxS_symm R)
  have hdivt : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) :=
    divFree_propagates_on hν.le hcODE hdiv0
  have hrealt : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) :=
    realField_propagates_on (S := boxS R) hν.le (boxS_symm R)
      (fun t _ k hk => hcs t k hk) hcODE hreal0
  -- decay from the initial energy of the truncation, then relax to en c₀
  have hdec := ns_galerkin_decay_leray hν (boxS_zero_not_mem R) hcs
    hrealt hdivt hcODE
  intro t ht
  have hen0 : en (c 0) ≤ en c₀ := by
    rw [hc0]; exact en_truncate_le hE _
  have hexp : (0:ℝ) ≤ Real.exp (-(2 * ν * t)) := (Real.exp_pos _).le
  calc en (c t) ≤ en (c 0) * Real.exp (-(2 * ν * t)) := hdec t ht
    _ ≤ en c₀ * Real.exp (-(2 * ν * t)) :=
        mul_le_mul_of_nonneg_right hen0 hexp

end TheoremB
