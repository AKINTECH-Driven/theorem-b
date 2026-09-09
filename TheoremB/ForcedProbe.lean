/-
# Audit probes for Tier 8a (the forced chain, wave F5)

The register requires that a capstone be shown NON-VACUOUS before it is
tagged, and that every hypothesis it carries be shown LOAD-BEARING: a
theorem whose hypotheses cannot be jointly satisfied is true and empty,
and a hypothesis that nothing ever fails is decoration. Every probe in
this file is a compiled declaration; nothing below is asserted in prose
only. The frozen forced files (ForcedTrap, ForcedGalerkin,
ForcedGalerkinFlow, ForcedTheoremB, ForcedUnique) are consumed, never
edited. Nothing here is new mathematics: the forced small-data theory
is textbook (Temam, NSE, Ch. III; Robinson, Rodrigo and Sadowski;
Foias, Manley, Rosa and Temam; chapter numbers unverified), and every
witness below except the line force of Probe 2 is a two-mode real shear
field on `{e₁, -e₁}`, the cheapest field with vanishing full convection.

**Probe 1 (`probe_forced_joint_hypotheses_strict`,
`probe_forced_capstones_fire_jointly`).** JOINT inhabitation at the
capstone level. For every `κ > 0` and `ν > 0` there is a NONZERO datum
and a NONZERO ℓ² time-dependent force sitting STRICTLY inside the four
box and force thresholds of `theorem_B_forced` (`en c₀ < Es`,
`ens c₀ < Zs`, `en (g t) ≤ G < ν²·Es`, `8·G < ν²·Zs`) and inside the
smallness threshold (`κ·Es·Zs ≤ ν⁴`, exported non-strictly), satisfying
every hypothesis of the capstone; and, for every `ν > 0`, a pair of this
kind on which both `theorem_B_forced` (every horizon) and
`ns_full_global_flow_forced` (the eternal flow) fire (Probe 1b invokes
Probe 1a at `max κ κ'` over the two compiled constants). Until this
probe the tree and the ledger carried the 8a hypotheses inhabited only
separately (thresholds; force) and jointly only at `g = 0`; the joint
inhabitation was first compiled in the persisted F3 audit-shape probe
`C_JointInhabitation.lean`, the source of Probe 1. The datum is the pair shear at radius `s/2`, the force the
pair shear at amplitude `(ν s/8)·cos t`, for a radius `s` with
`4κs⁴ ≤ ν⁴`.

**Probe 2 (`probe_line_force_fails_only_certificate`).** The
SUMMABILITY CERTIFICATE on the force is load-bearing. The line force
(the unit shear on every mode `(n, 0, 0)`, `n ≠ 0`) is mean-zero, real,
divergence-free, per-mode continuous, nonzero, and meets EVERY energy
budget `G ≥ 0` because its `en` is the junk value `0` of a
non-summable `tsum`; it is rejected by the certificate alone, at every
time. So the certificate is the single hypothesis standing between the
forced statements and non-ℓ² forces.

**Probe 3 (`probe_constant_witness_fails_equation_clauses`,
`probe_constant_witness_fails_ode_unforced`).** The two EQUATION
clauses are what tie a witness to the force. Under a constant nonzero
admissible force the constant zero witness passes four of the five
non-equation clauses of `theorem_B_forced` (real and divergence-free,
summability, continuity, box; the initial-condition clause is not
stated, holding trivially for the zero witness with `c₀ := 0`) for
every `Es ≥ 0`, `Zs ≥ 0` and every horizon, and INDEPENDENTLY fails the integral clause
(at `t = 1`, `k = e₁` the integral of the force is the shear vector)
and the mode-ODE clause (`HasDerivAt.unique` against
`hasDerivAt_const`). Removing both, and only both, equation clauses
would admit it. At `g = 0` the constant shear witness fails the
mode-ODE clause for every `ν > 0`: dissipation alone moves it.

**Probe 4 (`probe_no_confined_flow_inhabited`,
`forced_breakdown_threshold_without_budget_fails`).** The FORCE
DISJUNCT in the conclusion of `forced_breakdown_threshold` is
load-bearing. The corollary with its conclusion weakened to `False`
("trap-class data under an admissible force always admit a flow
confined to an admissible box") is refuted for EVERY candidate `κ > 0`:
at `ν = 1`, the pair shear datum of radius `r/2` under the CONSTANT
pair shear force of radius `4r` (outside the box's force thresholds, a
fact of the witness that no registered statement of this file carries),
with the box `(r², r²)`, `κr⁴ ≤ 1`, and the horizon `T = 1`, admits no
flow of the class confined to the box. The proof is
`theorem_B_unique_forced` against the explicit profile
`φ(t) = (r/2)e^{-t} + 4r(1 - e^{-t})` on the pair modes (the forced
equation is linear there): any confined flow agrees with it on
`[0, 1]`, and at `t = 1` its energy `2φ(1)² ≥ 8r²` exceeds `r²`. The
same witness shows the corollary's FULL hypothesis list, "no confined
flow" included, is inhabited by a nonzero datum and a nonzero ℓ² force.

**Probe 5 (`eternal_forced_flows_agree`,
`eternal_forced_witnesses_agree`).** The F3-to-F4 seam. Any two flows
carrying six of the seven clauses exported by `ns_full_global_flow_forced`
(the mode-ODE clause is not needed), under per-mode continuity of the
force (a capstone hypothesis, not an exported clause; same datum, same
force; the boxes may differ) agree at every `t ≥ 0` and
every mode, by restricting the exported clauses to `[0, t]` and
applying `theorem_B_unique_forced` at the box `(max Es Es', max Zs Zs')`.
This is the compiled form of the sentence "the exported clauses place
every restriction inside the forced uniqueness class"; the composition
states uniqueness of the eternal flow as a corollary of what it
exports, not as a clause.

**The `g = 0` direction is already in the tree** and is not duplicated
here: `probe_forced_zero_feeds_frozen` (ForcedGalerkin.lean; the forced
Galerkin ODE clause at `g = 0` IS the frozen one by `simpa`) and
`probe_frozen_flow_inhabits_forced_clauses` (ForcedTheoremB.lean; the
frozen `theorem_B_cont` witness satisfies the forced seven-clause list
at `g = 0` for every box containing the data). That is the ONLY
compiled direction between the two chains. At `g = 0` the forced chain
is NOT a strengthening of the unforced one: `κ_forced = 8K` (of
explicit form up to the lattice-kernel sum, exported as a compiled
existential), the smallness is non-strict, and the box `(Es, Zs)` is a
stronger energy hypothesis than the frozen `κ·en c₀·ens c₀ < ν⁴`.

The two-mode machinery (`pe1`, `pBox`, `probeVec`, `pairDatum`, the
time-dependent pair force `gF`, the line force, the explicit profile
`mfPhi`) is private to this file: it appears in no registered
statement, only in the witnesses, and needs no ledger line.
-/
import TheoremB.ForcedUnique

namespace TheoremB

open Set

noncomputable section

/-! ## The pair-mode machinery (private) -/

/-- The lattice mode `e₁`. -/
private def pe1 : Fin 3 → ℤ := ![1, 0, 0]

private lemma pe1_ne_zero : pe1 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [pe1] at this

private lemma neg_pe1_ne_zero : -pe1 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [pe1] at this

private lemma pe1_ne_neg : pe1 ≠ -pe1 := by
  intro h
  have := congrFun h 0
  simp [pe1] at this

private lemma norm_freq_pe1 : ‖freq pe1‖ = 1 := by
  rw [norm_freq]
  simp [pe1, Fin.sum_univ_three]

private lemma norm_freq_neg_pe1 : ‖freq (-pe1)‖ = 1 := by
  rw [norm_freq]
  simp [pe1, Fin.sum_univ_three]

/-- The two-mode support `{e₁, -e₁}`. -/
private def pBox : Finset (Fin 3 → ℤ) := {pe1, -pe1}

private lemma zero_not_mem_pBox : (0 : Fin 3 → ℤ) ∉ pBox := by
  simp [pBox, pe1_ne_zero.symm, neg_pe1_ne_zero.symm]

private lemma pBox_symm : ∀ k ∈ pBox, -k ∈ pBox := by
  intro k hk
  simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hk ⊢
  rcases hk with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg _)

/-- The real shear vector `r · e₂`. -/
private def probeVec (r : ℝ) : Vel := EuclideanSpace.single 1 (r : ℂ)

private lemma norm_probeVec (r : ℝ) : ‖probeVec r‖ = |r| := by
  rw [probeVec, PiLp.norm_single, Complex.norm_real, Real.norm_eq_abs]

private lemma conjVel_probeVec (r : ℝ) : conjVel (probeVec r) = probeVec r := by
  ext j
  simp only [conjVel, probeVec, WithLp.ofLp_toLp, PiLp.single_apply]
  split_ifs <;> simp

private lemma dotR_probeVec_pe1 (r : ℝ) : dotR (probeVec r) (freq pe1) = 0 := by
  simp [dotR, probeVec, freq, pe1]

private lemma dotR_probeVec_neg_pe1 (r : ℝ) : dotR (probeVec r) (freq (-pe1)) = 0 := by
  simp [dotR, probeVec, freq, pe1]

private lemma probeVec_one_ne_zero : probeVec 1 ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [norm_probeVec, norm_zero] at this
  norm_num at this

/-- `probeVec` is real-scalar linear in its radius (as a complex scalar). -/
private lemma probeVec_eq_smul (x : ℝ) : probeVec x = (x : ℂ) • probeVec 1 := by
  ext j
  simp [probeVec]

/-- The pair-mode field: `v` on `±e₁`, zero elsewhere. -/
private def pairDatum (v : Vel) : (Fin 3 → ℤ) → Vel :=
  fun k => if k = pe1 ∨ k = -pe1 then v else 0

private lemma pairDatum_eq_zero {v : Vel} {k : Fin 3 → ℤ} (hk : k ∉ pBox) :
    pairDatum v k = 0 := by
  simp only [pBox, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [pairDatum, hk.1, hk.2]

private lemma pairDatum_pe1 (v : Vel) : pairDatum v pe1 = v := by
  simp [pairDatum]

private lemma pairDatum_in (v : Vel) {k : Fin 3 → ℤ} (hk : k = pe1 ∨ k = -pe1) :
    pairDatum v k = v := by
  simp [pairDatum, hk]

private lemma pairDatum_zero_mode (v : Vel) : pairDatum v 0 = 0 :=
  pairDatum_eq_zero zero_not_mem_pBox

/-- Weighted energy of the pair field: only the two modes contribute. -/
private lemma pair_tsum (w : (Fin 3 → ℤ) → ℝ) (v : Vel) :
    ∑' k, w k * ‖pairDatum v k‖ ^ 2 = (w pe1 + w (-pe1)) * ‖v‖ ^ 2 := by
  have hsupp : ∀ k ∉ pBox, w k * ‖pairDatum v k‖ ^ 2 = 0 := by
    intro k hk
    simp [pairDatum_eq_zero hk]
  rw [tsum_eq_sum hsupp]
  simp only [pBox]
  rw [Finset.sum_pair pe1_ne_neg]
  simp [pairDatum, pe1_ne_neg, pe1_ne_neg.symm]
  ring

private lemma en_pairDatum (v : Vel) : en (pairDatum v) = 2 * ‖v‖ ^ 2 := by
  have h := pair_tsum (fun _ => 1) v
  simp only [one_mul] at h
  show ∑' k, ‖pairDatum v k‖ ^ 2 = _
  rw [h]
  ring

private lemma ens_pairDatum (v : Vel) : ens (pairDatum v) = 2 * ‖v‖ ^ 2 := by
  have h := pair_tsum (fun k => ‖freq k‖ ^ 2) v
  show ∑' k, ‖freq k‖ ^ 2 * ‖pairDatum v k‖ ^ 2 = _
  rw [h, norm_freq_pe1, norm_freq_neg_pe1]
  norm_num

private lemma summable_sq_pairDatum (v : Vel) : Summable fun l => ‖pairDatum v l‖ ^ 2 :=
  summable_of_ne_finset_zero (s := pBox) fun k hk => by rw [pairDatum_eq_zero hk]; simp

private lemma summable_wsq_pairDatum (v : Vel) :
    Summable fun l => ‖freq l‖ ^ 2 * ‖pairDatum v l‖ ^ 2 :=
  summable_of_ne_finset_zero (s := pBox) fun k hk => by rw [pairDatum_eq_zero hk]; simp

private lemma realField_pairDatum_probeVec (r : ℝ) : RealField (pairDatum (probeVec r)) := by
  intro k
  by_cases hk : k ∈ pBox
  · have hnk : -k ∈ pBox := pBox_symm k hk
    simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hk hnk
    simp only [pairDatum]
    rw [if_pos hnk, if_pos hk, conjVel_probeVec]
  · have hnk : -k ∉ pBox := by
      intro h
      exact hk (by simpa using pBox_symm (-k) h)
    rw [pairDatum_eq_zero hk, pairDatum_eq_zero hnk]
    ext j
    simp [conjVel]

private lemma divFree_pairDatum_probeVec (r : ℝ) : DivFree (pairDatum (probeVec r)) := by
  intro k
  by_cases hk : k ∈ pBox
  · simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hk
    simp only [pairDatum]
    rw [if_pos hk]
    rcases hk with rfl | rfl
    · exact dotR_probeVec_pe1 r
    · exact dotR_probeVec_neg_pe1 r
  · rw [pairDatum_eq_zero hk]
    simp [dotR]

private lemma pairDatum_probeVec_ne_zero {r : ℝ} (hr : r ≠ 0) :
    pairDatum (probeVec r) ≠ 0 := by
  intro h
  have := congrFun h pe1
  simp only [pairDatum, true_or, if_true, Pi.zero_apply] at this
  have hn := congrArg norm this
  rw [norm_probeVec, norm_zero] at hn
  exact hr (abs_eq_zero.mp hn)

/-- The pair shear field has vanishing full convection on EVERY mode: the
shear direction is orthogonal to every frequency the field can see. -/
private lemma convFull_pairDatum_probeVec (r : ℝ) (k : Fin 3 → ℤ) :
    convFull (pairDatum (probeVec r)) k = 0 := by
  unfold convFull
  have hterm : ∀ l : Fin 3 → ℤ,
      (Complex.I * dotR (pairDatum (probeVec r) l) (freq (k - l))) •
        pairDatum (probeVec r) (k - l) = 0 := by
    intro l
    by_cases hkl : k - l ∈ pBox
    · have hdot : dotR (pairDatum (probeVec r) l) (freq (k - l)) = 0 := by
        simp only [pBox, Finset.mem_insert, Finset.mem_singleton] at hkl
        by_cases hl : l = pe1 ∨ l = -pe1
        · simp only [pairDatum, if_pos hl]
          rcases hkl with h | h
          · rw [h]; exact dotR_probeVec_pe1 r
          · rw [h]; exact dotR_probeVec_neg_pe1 r
        · simp only [pairDatum, if_neg hl]
          simp [dotR]
      rw [hdot, mul_zero, zero_smul]
    · rw [pairDatum_eq_zero hkl, smul_zero]
  rw [tsum_congr hterm]
  simp

/-- The Leray projection annihilates zero. -/
private lemma lerayProj_zero_vec (k : Fin 3 → ℤ) : lerayProj k (0 : Vel) = 0 := by
  have h := lerayProj_sub k (0 : Vel) 0
  rw [sub_self, sub_self] at h
  exact h

/-- The full convection annihilates the zero field. -/
private lemma convFull_zero_field (k : Fin 3 → ℤ) :
    convFull (fun (_ : Fin 3 → ℤ) => (0 : Vel)) k = 0 := by
  unfold convFull
  simp

/-- A positive radius small enough for the box thresholds always exists. -/
private lemma exists_small_r {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ r : ℝ, 0 < r ∧ 4 * κ * r ^ 4 ≤ ν ^ 4 := by
  have hpos : 0 < ν / (κ + 2) := by positivity
  refine ⟨ν / (κ + 2), hpos, ?_⟩
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have h1 : 4 * κ ≤ (κ + 2) ^ 2 := by nlinarith [sq_nonneg κ]
  have h2 : (κ + 2) ^ 2 ≤ (κ + 2) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : 0 ≤ ν ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) h3]

/-- The time-dependent pair force of amplitude `ρ · cos t`. -/
private def gF (ρ : ℝ) : ℝ → (Fin 3 → ℤ) → Vel :=
  fun t => pairDatum (probeVec (ρ * Real.cos t))

private lemma gF_real (ρ : ℝ) : ∀ t, RealField (gF ρ t) :=
  fun t => realField_pairDatum_probeVec (ρ * Real.cos t)

private lemma gF_div (ρ : ℝ) : ∀ t, DivFree (gF ρ t) :=
  fun t => divFree_pairDatum_probeVec (ρ * Real.cos t)

private lemma gF_en (ρ : ℝ) : ∀ t, en (gF ρ t) ≤ 2 * ρ ^ 2 := by
  intro t
  show en (pairDatum (probeVec (ρ * Real.cos t))) ≤ _
  rw [en_pairDatum, norm_probeVec, sq_abs, mul_pow]
  have hc : Real.cos t ^ 2 ≤ 1 := by
    have := Real.cos_sq_le_one t
    linarith
  nlinarith [sq_nonneg ρ]

private lemma gF_cont (ρ : ℝ) : ∀ k, Continuous fun t => gF ρ t k := by
  intro k
  by_cases hk : k = pe1 ∨ k = -pe1
  · have : (fun t => gF ρ t k) = fun t => ((ρ * Real.cos t : ℝ) : ℂ) • probeVec 1 := by
      funext t
      simp only [gF, pairDatum, if_pos hk]
      exact probeVec_eq_smul _
    rw [this]
    exact (Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_cos)).smul
      continuous_const
  · have : (fun t => gF ρ t k) = fun _ => (0 : Vel) := by
      funext t
      simp only [gF, pairDatum, if_neg hk]
    rw [this]
    exact continuous_const

private lemma gF_zero_ne_zero {ρ : ℝ} (hρ : ρ ≠ 0) : gF ρ 0 ≠ 0 := by
  show pairDatum (probeVec (ρ * Real.cos 0)) ≠ 0
  rw [Real.cos_zero, mul_one]
  exact pairDatum_probeVec_ne_zero hρ

private lemma gF_summable (ρ : ℝ) : ∀ t, Summable fun l => ‖gF ρ t l‖ ^ 2 :=
  fun _ => summable_sq_pairDatum _

private lemma gF_mean_zero (ρ : ℝ) : ∀ t, gF ρ t 0 = 0 :=
  fun _ => pairDatum_zero_mode _

/-! ## Probe 1: joint inhabitation at the capstone level -/

/-- **Probe 1a: every hypothesis of `theorem_B_forced` is met JOINTLY by a
nonzero datum and a nonzero ℓ² force STRICTLY inside the four box and force
thresholds and inside the smallness threshold** (the last exported
non-strictly, `κ·Es·Zs ≤ ν⁴`), for every `κ > 0` and `ν > 0`. The datum is the pair shear at radius `s/2`, the
force the pair shear at amplitude `(ν s/8)·cos t`, with `4κs⁴ ≤ ν⁴`; the box
is `(2s², 2s²)` and the force budget `2(νs/8)²`. -/
theorem probe_forced_joint_hypotheses_strict {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ (c₀ : (Fin 3 → ℤ) → Vel) (g : ℝ → (Fin 3 → ℤ) → Vel) (Es Zs G : ℝ),
      c₀ ≠ 0 ∧ g 0 ≠ 0 ∧ 0 < G ∧ 0 ≤ Es ∧ 0 < Zs ∧
      κ * Es * Zs ≤ ν ^ 4 ∧ G < ν ^ 2 * Es ∧ 8 * G < ν ^ 2 * Zs ∧
      en c₀ < Es ∧ ens c₀ < Zs ∧
      Summable (fun l => ‖c₀ l‖ ^ 2) ∧ Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) ∧
      c₀ 0 = 0 ∧ RealField c₀ ∧ DivFree c₀ ∧ en c₀ ≤ Es ∧ ens c₀ ≤ Zs ∧
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) ∧
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) ∧ (∀ t ∈ Ici (0:ℝ), DivFree (g t)) ∧
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) ∧
      (∀ t ∈ Ici (0:ℝ), en (g t) ≤ G) ∧
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) := by
  obtain ⟨s, hs, hsmall⟩ := exists_small_r hκ hν
  have hnv : ‖probeVec (s / 2)‖ = s / 2 := by rw [norm_probeVec, abs_of_pos (by positivity)]
  set ρ : ℝ := ν * s / 8 with hρdef
  have hρ : ρ ≠ 0 := by rw [hρdef]; positivity
  refine ⟨pairDatum (probeVec (s / 2)), gF ρ, 2 * s ^ 2, 2 * s ^ 2, 2 * ρ ^ 2,
    pairDatum_probeVec_ne_zero (by positivity), gF_zero_ne_zero hρ, by positivity,
    by positivity, by positivity, ?_, ?_, ?_, ?_, ?_,
    summable_sq_pairDatum _, summable_wsq_pairDatum _, pairDatum_zero_mode _,
    realField_pairDatum_probeVec _, divFree_pairDatum_probeVec _, ?_, ?_,
    fun t _ => gF_mean_zero ρ t, fun t _ => gF_real ρ t, fun t _ => gF_div ρ t,
    fun t _ => gF_summable ρ t, fun t _ => gF_en ρ t, fun k => (gF_cont ρ k).continuousOn⟩
  · have e : κ * (2 * s ^ 2) * (2 * s ^ 2) = 4 * κ * s ^ 4 := by ring
    rw [e]; exact hsmall
  · rw [hρdef]; nlinarith [mul_pos (mul_pos hν hν) (mul_pos hs hs)]
  · rw [hρdef]; nlinarith [mul_pos (mul_pos hν hν) (mul_pos hs hs)]
  · rw [en_pairDatum, hnv]; nlinarith [mul_pos hs hs]
  · rw [ens_pairDatum, hnv]; nlinarith [mul_pos hs hs]
  · rw [en_pairDatum, hnv]; nlinarith [mul_pos hs hs]
  · rw [ens_pairDatum, hnv]; nlinarith [mul_pos hs hs]

/-- **Probe 1b: both capstones FIRE on the joint data.** For every `ν > 0`
there are a nonzero datum and a nonzero force on which `theorem_B_forced`
yields a confined flow on every horizon and `ns_full_global_flow_forced`
yields the eternal flow; Probe 1a is invoked at `max κ κ'` so that one pair
is small enough for both compiled constants. -/
theorem probe_forced_capstones_fire_jointly {ν : ℝ} (hν : 0 < ν) :
    ∃ (c₀ : (Fin 3 → ℤ) → Vel) (g : ℝ → (Fin 3 → ℤ) → Vel) (Es Zs : ℝ),
      c₀ ≠ 0 ∧ g 0 ≠ 0 ∧
      (∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel, c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)) ∧
      (∃ c : ℝ → (Fin 3 → ℤ) → Vel, c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs)) := by
  obtain ⟨κ, hκ, HB⟩ := theorem_B_forced
  obtain ⟨κ', hκ', HG⟩ := ns_full_global_flow_forced
  obtain ⟨c₀, g, Es, Zs, G, hc₀, hg0, _, hEs, hZs, h1, h2, h3, _, _, hE, hZ, hmean, hreal,
    hdiv, h0E, h0Z, hgmean, hgreal, hgdiv, hgsum, hgen, hgc⟩ :=
    probe_forced_joint_hypotheses_strict (lt_max_iff.mpr (Or.inl hκ) : 0 < max κ κ') hν
  have h1B : κ * Es * Zs ≤ ν ^ 4 := by
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hEs) hZs.le
  have h1G : κ' * Es * Zs ≤ ν ^ 4 := by
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hEs) hZs.le
  refine ⟨c₀, g, Es, Zs, hc₀, hg0, fun T hT => ?_, ?_⟩
  · obtain ⟨c, hc0, _, _, _, heq, _, htrap⟩ :=
      HB hν hEs hZs h1B h2.le h3.le hE hZ hmean hreal hdiv h0E h0Z hgmean hgreal hgdiv hgsum
        hgen hgc T hT
    exact ⟨c, hc0, heq, htrap⟩
  · obtain ⟨c, hc0, _, _, _, heq, hode, htrap⟩ :=
      HG hν hEs hZs h1G h2.le h3.le hE hZ hmean hreal hdiv h0E h0Z hgmean hgreal hgdiv hgsum
        hgen hgc
    exact ⟨c, hc0, heq, hode, htrap⟩

/-! ## Probe 2: the summability certificate is load-bearing -/

/-- The line of modes `(n, 0, 0)`, `n ≠ 0`. -/
private def onLine (k : Fin 3 → ℤ) : Prop := k 0 ≠ 0 ∧ k 1 = 0 ∧ k 2 = 0

private instance : DecidablePred onLine := fun k => by unfold onLine; infer_instance

/-- The line force: the unit shear `e₂` on every line mode, `0` elsewhere. -/
private def lineForce : ℝ → (Fin 3 → ℤ) → Vel :=
  fun _ k => if onLine k then probeVec 1 else 0

private lemma onLine_neg (k : Fin 3 → ℤ) : onLine (-k) ↔ onLine k := by
  simp [onLine]

private lemma lineForce_apply (t : ℝ) (k : Fin 3 → ℤ) :
    lineForce t k = if onLine k then probeVec 1 else 0 := rfl

private lemma line_mean_zero : ∀ t ∈ Ici (0:ℝ), lineForce t 0 = 0 := by
  intro t _
  rw [lineForce_apply, if_neg]
  simp [onLine]

private lemma line_real : ∀ t ∈ Ici (0:ℝ), RealField (lineForce t) := by
  intro t _ k
  rw [lineForce_apply, lineForce_apply]
  by_cases hk : onLine k
  · rw [if_pos ((onLine_neg k).mpr hk), if_pos hk, conjVel_probeVec]
  · rw [if_neg (fun h => hk ((onLine_neg k).mp h)), if_neg hk]
    ext j
    simp [conjVel]

private lemma line_divFree : ∀ t ∈ Ici (0:ℝ), DivFree (lineForce t) := by
  intro t _ k
  rw [lineForce_apply]
  by_cases hk : onLine k
  · rw [if_pos hk]
    simp [dotR, probeVec, freq, hk.2.1]
  · rw [if_neg hk]
    simp [dotR]

private lemma line_ne_zero : lineForce 0 ≠ 0 := by
  intro h
  have h1 := congrFun h pe1
  rw [lineForce_apply, if_pos (by simp [onLine, pe1])] at h1
  exact probeVec_one_ne_zero h1

/-- The line carries infinitely many unit modes, so it is not ℓ². -/
private lemma line_not_summable (t : ℝ) : ¬ Summable (fun l => ‖lineForce t l‖ ^ 2) := by
  intro hs
  have ht := hs.tendsto_cofinite_zero
  have hev : ∀ᶠ l in Filter.cofinite, ‖lineForce t l‖ ^ 2 < 1 / 2 :=
    ht.eventually_lt_const (by norm_num)
  rw [Filter.eventually_cofinite] at hev
  refine (Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (![(n : ℤ) + 1, 0, 0] : Fin 3 → ℤ)) ?_ ?_) hev
  · intro a b hab
    have := congrFun hab 0
    simpa using this
  · intro n
    simp only [Set.mem_setOf_eq, not_lt]
    have hon : onLine ![(n : ℤ) + 1, 0, 0] := by
      simp [onLine]
      omega
    rw [lineForce_apply, if_pos hon, norm_probeVec]
    norm_num

/-- `en` of the line force is the junk value `0` of a non-summable `tsum`. -/
private lemma line_en_zero (t : ℝ) : en (lineForce t) = 0 := by
  unfold en
  exact tsum_eq_zero_of_not_summable (line_not_summable t)

/-- **Probe 2: the summability certificate is the single load-bearing
hypothesis against non-ℓ² forces.** There is a nonzero force that is
mean-zero, real, divergence-free and per-mode continuous on `[0, ∞)`, and
meets EVERY energy budget `G ≥ 0` (its `en` is the junk value `0` of a
non-summable series), yet fails the certificate at every time; so the
certificate hypothesis of `theorem_B_forced` / `ns_full_global_flow_forced`,
as written, rejects it, and nothing else does. -/
theorem probe_line_force_fails_only_certificate :
    ∃ g : ℝ → (Fin 3 → ℤ) → Vel,
      g 0 ≠ 0 ∧
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) ∧
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) ∧
      (∀ t ∈ Ici (0:ℝ), DivFree (g t)) ∧
      (∀ G : ℝ, 0 ≤ G → ∀ t ∈ Ici (0:ℝ), en (g t) ≤ G) ∧
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) ∧
      (∀ t ∈ Ici (0:ℝ), ¬ Summable (fun l => ‖g t l‖ ^ 2)) ∧
      ¬ (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) :=
  ⟨lineForce, line_ne_zero, line_mean_zero, line_real, line_divFree,
    fun G hG t _ => by rw [line_en_zero]; exact hG,
    fun _ => continuousOn_const,
    fun t _ => line_not_summable t,
    fun h => line_not_summable 0 (h 0 (Set.mem_Ici.mpr (le_refl 0)))⟩

/-! ## Probe 3: the equation clauses pin the witness to the force -/

/-- The unit shear vector `e₂` and the constant shear-pair field. -/
private def auditV : Vel := probeVec 1

private def auditForce : (Fin 3 → ℤ) → Vel := pairDatum auditV

private lemma auditV_ne_zero : auditV ≠ 0 := probeVec_one_ne_zero

private lemma auditForce_pe1 : auditForce pe1 = auditV := pairDatum_pe1 _

private lemma convFull_auditForce (k : Fin 3 → ℤ) : convFull auditForce k = 0 :=
  convFull_pairDatum_probeVec 1 k

/-- The constant zero witness and the constant nonzero force. -/
private def cZero : ℝ → (Fin 3 → ℤ) → Vel := fun _ _ => 0

private def gConst : ℝ → (Fin 3 → ℤ) → Vel := fun _ => auditForce

private lemma convFull_cZero (s : ℝ) (k : Fin 3 → ℤ) : convFull (cZero s) k = 0 :=
  convFull_zero_field k

/-- Under the constant nonzero force the constant zero witness violates the
forced INTEGRAL clause on `[0, 1]`: at `t = 1`, `k = e₁` the integral of the
constant force is `auditV ≠ 0`. Holds for every `ν`. -/
private lemma constant_witness_fails_integral_clause (ν : ℝ) :
    ¬ (∀ t ∈ Icc (0:ℝ) 1, ∀ k, cZero t k = cZero 0 k +
        ∫ s in (0:ℝ)..t, ((-(ν * ‖freq k‖ ^ 2)) • cZero s k +
          lerayProj k (convFull (cZero s) k) + gConst s k)) := by
  intro h
  have h1 := h 1 ⟨by norm_num, le_refl 1⟩ pe1
  have hint : (fun s : ℝ => (-(ν * ‖freq pe1‖ ^ 2)) • cZero s pe1 +
      lerayProj pe1 (convFull (cZero s) pe1) + gConst s pe1) = fun _ => auditV := by
    funext s
    simp only [cZero, gConst, smul_zero, zero_add]
    rw [convFull_cZero, lerayProj_zero_vec, zero_add, auditForce_pe1]
  rw [hint, intervalIntegral.integral_const] at h1
  simp only [cZero, zero_add, sub_zero, one_smul] at h1
  exact auditV_ne_zero h1.symm

/-- The same witness violates the forced MODE-ODE clause on `(0, 1)`: the
derivative of a constant is `0`, the forced right-hand side at `k = e₁` is
`auditV ≠ 0`. -/
private lemma constant_witness_fails_ode_clause (ν : ℝ) :
    ¬ (∀ t ∈ Ioo (0:ℝ) 1, ∀ k, HasDerivAt (fun s => cZero s k)
        ((-(ν * ‖freq k‖ ^ 2)) • cZero t k + lerayProj k (convFull (cZero t) k) +
          gConst t k) t) := by
  intro h
  have h1 := h (1/2) ⟨by norm_num, by norm_num⟩ pe1
  have hrhs : (-(ν * ‖freq pe1‖ ^ 2)) • cZero (1/2) pe1 +
      lerayProj pe1 (convFull (cZero (1/2)) pe1) + gConst (1/2) pe1 = auditV := by
    simp only [cZero, gConst, smul_zero, zero_add]
    rw [convFull_cZero, lerayProj_zero_vec, zero_add, auditForce_pe1]
  rw [hrhs] at h1
  have h2 : HasDerivAt (fun s : ℝ => cZero s pe1) 0 (1/2) := hasDerivAt_const _ _
  exact auditV_ne_zero (h1.unique h2)

/-- **Probe 3a: the two equation clauses, and only they, refute the constant
zero witness.** There is a constant, nonzero, admissible force (mean-zero,
real, divergence-free, ℓ², per-mode continuous) under which the constant
zero witness passes four of the five non-equation clauses of
`theorem_B_forced` (real and divergence-free, summability, continuity,
box; the initial-condition clause `c 0 = c₀` is not stated) for every
`Es ≥ 0`, `Zs ≥ 0` and every horizon, and fails the integral
clause on `[0, 1]` and the mode-ODE clause on `(0, 1)` INDEPENDENTLY, for
every `ν`. -/
theorem probe_constant_witness_fails_equation_clauses (ν : ℝ) :
    ∃ (c g : ℝ → (Fin 3 → ℤ) → Vel),
      (∀ t k, c t k = 0) ∧ (∀ t, g t = g 0) ∧ g 0 ≠ 0 ∧
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) ∧
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) ∧ (∀ t ∈ Ici (0:ℝ), DivFree (g t)) ∧
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) ∧
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) ∧
      (∀ Es Zs : ℝ, 0 ≤ Es → 0 ≤ Zs → ∀ T : ℝ,
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)) ∧
      ¬ (∀ t ∈ Icc (0:ℝ) 1, ∀ k, c t k = c 0 k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
      ¬ (∀ t ∈ Ioo (0:ℝ) 1, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) := by
  refine ⟨cZero, gConst, fun _ _ => rfl, fun _ => rfl, pairDatum_probeVec_ne_zero one_ne_zero,
    fun _ _ => pairDatum_zero_mode auditV, fun _ _ => realField_pairDatum_probeVec 1,
    fun _ _ => divFree_pairDatum_probeVec 1, fun _ _ => summable_sq_pairDatum _,
    fun _ => continuousOn_const, ?_,
    constant_witness_fails_integral_clause ν, constant_witness_fails_ode_clause ν⟩
  intro Es Zs hEs hZs T
  refine ⟨fun t _ => ⟨?_, ?_⟩, fun t _ => ⟨?_, ?_⟩, fun k => continuousOn_const,
    fun t _ => ⟨?_, ?_⟩⟩
  · intro k; ext j; simp [cZero, conjVel]
  · intro k; simp [cZero, dotR]
  · simp [cZero]
  · simp [cZero]
  · simpa [cZero, en] using hEs
  · simpa [cZero, ens] using hZs

/-- The constant shear witness `c t := auditForce`. -/
private def cShear : ℝ → (Fin 3 → ℤ) → Vel := fun _ => auditForce

/-- **Probe 3b: at `g = 0` the constant shear witness fails the mode-ODE
clause for every `ν > 0`.** `convFull auditForce = 0` and `‖freq e₁‖² = 1`,
so the right-hand side at `e₁` is `-ν • auditV ≠ 0` while the derivative of
a constant is `0`: dissipation alone moves a nonzero steady state. The
witness is nonzero, mean-zero, real and divergence-free. -/
theorem probe_constant_witness_fails_ode_unforced :
    ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      (∀ t, c t = c 0) ∧ c 0 ≠ 0 ∧ c 0 0 = 0 ∧ RealField (c 0) ∧ DivFree (c 0) ∧
      ∀ ν : ℝ, 0 < ν →
        ¬ (∀ t ∈ Ioo (0:ℝ) 1, ∀ k, HasDerivAt (fun s => c s k)
            ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) +
              (fun (_ : ℝ) (_ : Fin 3 → ℤ) => (0 : Vel)) t k) t) := by
  refine ⟨cShear, fun _ => rfl, pairDatum_probeVec_ne_zero one_ne_zero,
    pairDatum_zero_mode auditV, realField_pairDatum_probeVec 1, divFree_pairDatum_probeVec 1,
    fun ν hν h => ?_⟩
  have h1 := h (1/2) ⟨by norm_num, by norm_num⟩ pe1
  have hrhs : (-(ν * ‖freq pe1‖ ^ 2)) • cShear (1/2) pe1 +
      lerayProj pe1 (convFull (cShear (1/2)) pe1) +
      (fun (_ : ℝ) (_ : Fin 3 → ℤ) => (0 : Vel)) (1/2) pe1 = (-ν) • auditV := by
    simp only [cShear, add_zero]
    rw [convFull_auditForce, lerayProj_zero_vec, add_zero, auditForce_pe1, norm_freq_pe1]
    norm_num
  rw [hrhs] at h1
  have h2 : HasDerivAt (fun s : ℝ => cShear s pe1) 0 (1/2) := hasDerivAt_const _ _
  have h3 : (-ν) • auditV = 0 := h1.unique h2
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact absurd (neg_eq_zero.mp h4) hν.ne'
  · exact auditV_ne_zero h4

/-! ## Probe 4: the force disjunct of the breakdown corollary is load-bearing -/

/-- The explicit pair-mode profile under the constant force `4r` from the
datum `r/2` at `ν = 1`. -/
private def mfPhi (r t : ℝ) : ℝ := r / 2 * Real.exp (-t) + 4 * r * (1 - Real.exp (-t))

private lemma mfPhi_zero (r : ℝ) : mfPhi r 0 = r / 2 := by simp [mfPhi]

private lemma hasDerivAt_mfPhi (r t : ℝ) :
    HasDerivAt (mfPhi r) (-(mfPhi r t) + 4 * r) t := by
  have he : HasDerivAt (fun s => Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  have h := (he.const_mul (r / 2)).add ((he.const_sub 1).const_mul (4 * r))
  refine h.congr_deriv ?_
  simp only [mfPhi]
  ring

private lemma continuous_mfPhi (r : ℝ) : Continuous (mfPhi r) := by
  unfold mfPhi
  fun_prop

private lemma mfPhi_bounds {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ mfPhi r t ∧ mfPhi r t ≤ 4 * r := by
  unfold mfPhi
  have h1 := Real.exp_pos (-t)
  have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  constructor <;> nlinarith [mul_nonneg hr.le h1.le, mul_nonneg hr.le (sub_nonneg.mpr h2)]

private lemma mfPhi_one_ge {r : ℝ} (hr : 0 < r) : 2 * r ≤ mfPhi r 1 := by
  unfold mfPhi
  have h1 := Real.exp_pos (-1)
  have h2 : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    simp
  have he : Real.exp (-1) ≤ 1 / 2 := by nlinarith
  nlinarith [mul_nonneg hr.le h1.le, mul_nonneg hr.le (sub_nonneg.mpr he)]

/-- The explicit flow, the constant force, the datum. -/
private def mfFlow (r : ℝ) : ℝ → (Fin 3 → ℤ) → Vel := fun t => pairDatum (probeVec (mfPhi r t))
private def mfForce (r : ℝ) : ℝ → (Fin 3 → ℤ) → Vel := fun _ => pairDatum (probeVec (4 * r))
private def mfDatum (r : ℝ) : (Fin 3 → ℤ) → Vel := pairDatum (probeVec (r / 2))

private lemma mfFlow_zero (r : ℝ) : mfFlow r 0 = mfDatum r := by
  show pairDatum (probeVec (mfPhi r 0)) = pairDatum (probeVec (r / 2))
  rw [mfPhi_zero]

private lemma mfFlow_cont (r : ℝ) (k : Fin 3 → ℤ) : Continuous fun t => mfFlow r t k := by
  by_cases hk : k = pe1 ∨ k = -pe1
  · have : (fun t => mfFlow r t k) = fun t => ((mfPhi r t : ℝ) : ℂ) • probeVec 1 := by
      funext t
      show pairDatum (probeVec (mfPhi r t)) k = _
      rw [pairDatum_in _ hk]
      exact probeVec_eq_smul _
    rw [this]
    exact (Complex.continuous_ofReal.comp (continuous_mfPhi r)).smul continuous_const
  · have hk' : k ∉ pBox := by simpa [pBox] using hk
    have : (fun t => mfFlow r t k) = fun _ => (0 : Vel) := by
      funext t
      exact pairDatum_eq_zero hk'
    rw [this]
    exact continuous_const

private lemma mfFlow_bounds {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    en (mfFlow r t) ≤ 32 * r ^ 2 ∧ ens (mfFlow r t) ≤ 32 * r ^ 2 := by
  obtain ⟨h0, h4⟩ := mfPhi_bounds hr ht
  have hen : en (mfFlow r t) = 2 * (mfPhi r t) ^ 2 := by
    show en (pairDatum (probeVec (mfPhi r t))) = _
    rw [en_pairDatum, norm_probeVec, sq_abs]
  have hens : ens (mfFlow r t) = 2 * (mfPhi r t) ^ 2 := by
    show ens (pairDatum (probeVec (mfPhi r t))) = _
    rw [ens_pairDatum, norm_probeVec, sq_abs]
  rw [hen, hens]
  constructor <;> nlinarith

/-- The forced integrand of the explicit flow on a pair mode. -/
private lemma mf_integrand_in (r s : ℝ) {k : Fin 3 → ℤ} (hk : k = pe1 ∨ k = -pe1) :
    (-(1 * ‖freq k‖ ^ 2)) • mfFlow r s k + lerayProj k (convFull (mfFlow r s) k) + mfForce r s k
      = probeVec (-(mfPhi r s) + 4 * r) := by
  have hk1 : ‖freq k‖ = 1 := by
    rcases hk with rfl | rfl
    · exact norm_freq_pe1
    · exact norm_freq_neg_pe1
  rw [show convFull (mfFlow r s) k = 0 from convFull_pairDatum_probeVec _ _, lerayProj_zero_vec,
    add_zero]
  show (-(1 * ‖freq k‖ ^ 2)) • pairDatum (probeVec (mfPhi r s)) k
      + pairDatum (probeVec (4 * r)) k = _
  rw [pairDatum_in _ hk, pairDatum_in _ hk, hk1]
  ext j
  simp only [probeVec, PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply]
  split_ifs
  · push_cast
    simp
  · simp

/-- The forced integrand of the explicit flow off the pair modes. -/
private lemma mf_integrand_out (r s : ℝ) {k : Fin 3 → ℤ} (hk : k ∉ pBox) :
    (-(1 * ‖freq k‖ ^ 2)) • mfFlow r s k + lerayProj k (convFull (mfFlow r s) k) + mfForce r s k
      = 0 := by
  rw [show convFull (mfFlow r s) k = 0 from convFull_pairDatum_probeVec _ _, lerayProj_zero_vec,
    add_zero]
  show (-(1 * ‖freq k‖ ^ 2)) • pairDatum (probeVec (mfPhi r s)) k
      + pairDatum (probeVec (4 * r)) k = 0
  rw [pairDatum_eq_zero hk, pairDatum_eq_zero hk, smul_zero, add_zero]

private lemma hasDerivAt_mfVec (r s : ℝ) :
    HasDerivAt (fun u => probeVec (mfPhi r u)) (probeVec (-(mfPhi r s) + 4 * r)) s := by
  have hfun : (fun u => probeVec (mfPhi r u)) = fun u => ((mfPhi r u : ℝ) : ℂ) • probeVec 1 :=
    funext fun u => probeVec_eq_smul _
  rw [hfun, probeVec_eq_smul (-(mfPhi r s) + 4 * r)]
  exact ((hasDerivAt_mfPhi r s).ofReal_comp).smul_const _

private lemma mf_integral (r t : ℝ) :
    ∫ s in (0:ℝ)..t, probeVec (-(mfPhi r s) + 4 * r)
      = probeVec (mfPhi r t) - probeVec (mfPhi r 0) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => probeVec (mfPhi r u))
    (fun s _ => hasDerivAt_mfVec r s) ?_
  have hc : Continuous fun s => probeVec (-(mfPhi r s) + 4 * r) := by
    have hfun : (fun s => probeVec (-(mfPhi r s) + 4 * r))
        = fun s => (((-(mfPhi r s) + 4 * r : ℝ)) : ℂ) • probeVec 1 :=
      funext fun s => probeVec_eq_smul _
    rw [hfun]
    exact (Complex.continuous_ofReal.comp
      ((continuous_mfPhi r).neg.add continuous_const)).smul continuous_const
  exact hc.intervalIntegrable _ _

/-- The explicit flow satisfies the forced integral equation at `ν = 1`. -/
private lemma mf_integral_clause (r t : ℝ) (k : Fin 3 → ℤ) :
    mfFlow r t k = mfDatum r k + ∫ s in (0:ℝ)..t,
      ((-(1 * ‖freq k‖ ^ 2)) • mfFlow r s k + lerayProj k (convFull (mfFlow r s) k)
        + mfForce r s k) := by
  by_cases hk : k = pe1 ∨ k = -pe1
  · have hI : ∫ s in (0:ℝ)..t,
        ((-(1 * ‖freq k‖ ^ 2)) • mfFlow r s k + lerayProj k (convFull (mfFlow r s) k)
          + mfForce r s k)
        = ∫ s in (0:ℝ)..t, probeVec (-(mfPhi r s) + 4 * r) :=
      intervalIntegral.integral_congr fun s _ => mf_integrand_in r s hk
    rw [hI, mf_integral, mfPhi_zero]
    show pairDatum (probeVec (mfPhi r t)) k = pairDatum (probeVec (r / 2)) k + _
    rw [pairDatum_in _ hk, pairDatum_in _ hk]
    abel
  · have hk' : k ∉ pBox := by simpa [pBox] using hk
    have hI : ∫ s in (0:ℝ)..t,
        ((-(1 * ‖freq k‖ ^ 2)) • mfFlow r s k + lerayProj k (convFull (mfFlow r s) k)
          + mfForce r s k)
        = ∫ s in (0:ℝ)..t, (0 : Vel) :=
      intervalIntegral.integral_congr fun s _ => mf_integrand_out r s hk'
    rw [hI, intervalIntegral.integral_zero]
    show pairDatum (probeVec (mfPhi r t)) k = pairDatum (probeVec (r / 2)) k + 0
    rw [pairDatum_eq_zero hk', pairDatum_eq_zero hk', add_zero]

/-- No confined flow under the large constant force: for `κr⁴ ≤ 1`, `r > 0`,
at `ν = 1`, on `[0, 1]`, no flow of the class from `mfDatum r` under
`mfForce r` stays inside the box `(r², r²)`; any such flow agrees with the
explicit profile by `theorem_B_unique_forced`, whose energy at `t = 1`
exceeds the box. -/
private lemma mf_no_confined_flow {r : ℝ} (hr : 0 < r) :
    ¬ ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = mfDatum r ∧
        (∀ t ∈ Icc (0:ℝ) 1, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) 1, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) 1)) ∧
        (∀ t ∈ Icc (0:ℝ) 1, ∀ k, c t k = mfDatum r k + ∫ s in (0:ℝ)..t,
          ((-(1 * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + mfForce r s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) 1, ∀ k, HasDerivAt (fun s => c s k)
          ((-(1 * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + mfForce r t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) 1, en (c t) ≤ r ^ 2 ∧ ens (c t) ≤ r ^ 2) := by
  rintro ⟨c, hc0, hstr, hsum, hcont, heq, -, htrap⟩
  have hgc : ∀ k, ContinuousOn (fun s => mfForce r s k) (Icc (0:ℝ) 1) :=
    fun k => continuousOn_const
  have hr2 : r ^ 2 ≤ 32 * r ^ 2 := by nlinarith [sq_nonneg r]
  have huniq := theorem_B_unique_forced (ν := 1) (E := 32 * r ^ 2) (Z := 32 * r ^ 2) (T := 1)
    one_pos zero_le_one (c₀ := mfDatum r) (c₁ := c) (c₂ := mfFlow r) (g := mfForce r)
    hgc hc0 (mfFlow_zero r) hcont (fun k => (mfFlow_cont r k).continuousOn)
    hsum (fun t _ => ⟨summable_sq_pairDatum _, summable_wsq_pairDatum _⟩)
    (fun t ht => ⟨(htrap t ht).1.trans hr2, (htrap t ht).2.trans hr2⟩)
    (fun t ht => mfFlow_bounds hr ht.1)
    (fun t ht => (hstr t ht).2) (fun t _ => divFree_pairDatum_probeVec _)
    heq (fun t _ k => mf_integral_clause r t k)
  have h1 : c 1 = mfFlow r 1 := funext fun k => huniq 1 ⟨zero_le_one, le_rfl⟩ k
  have hen := (htrap 1 ⟨zero_le_one, le_rfl⟩).1
  rw [h1] at hen
  have hE : en (mfFlow r 1) = 2 * (mfPhi r 1) ^ 2 := by
    show en (pairDatum (probeVec (mfPhi r 1))) = _
    rw [en_pairDatum, norm_probeVec, sq_abs]
  have hφ := mfPhi_one_ge hr
  rw [hE] at hen
  nlinarith

/-- **Probe 4a: the FULL hypothesis list of `forced_breakdown_threshold`,
"no flow confined to the box" included, is inhabited for every `κ > 0` by a
NONZERO datum and a NONZERO ℓ² force** (the witness force, the pair shear
of radius `4r`, lies outside the box's force thresholds; that is a fact of
the witness, not a clause of this registered statement). -/
theorem probe_no_confined_flow_inhabited {κ : ℝ} (hκ : 0 < κ) :
    ∃ (ν : ℝ) (c₀ : (Fin 3 → ℤ) → Vel) (g : ℝ → (Fin 3 → ℤ) → Vel) (Es Zs T : ℝ),
      0 < ν ∧ c₀ ≠ 0 ∧ g 0 ≠ 0 ∧
      Summable (fun l => ‖c₀ l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) ∧
      c₀ 0 = 0 ∧ RealField c₀ ∧ DivFree c₀ ∧
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) ∧
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) ∧ (∀ t ∈ Ici (0:ℝ), DivFree (g t)) ∧
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) ∧
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) ∧
      0 ≤ Es ∧ 0 < Zs ∧ κ * Es * Zs ≤ ν ^ 4 ∧
      en c₀ ≤ Es ∧ ens c₀ ≤ Zs ∧
      0 ≤ T ∧
      (¬ ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)) := by
  obtain ⟨r, hr, hsmall⟩ := exists_small_r hκ one_pos
  have hr2 : 0 < r / 2 := by positivity
  have hnv : ‖probeVec (r / 2)‖ = r / 2 := by rw [norm_probeVec, abs_of_pos hr2]
  refine ⟨1, mfDatum r, mfForce r, r ^ 2, r ^ 2, 1, one_pos,
    pairDatum_probeVec_ne_zero hr2.ne', pairDatum_probeVec_ne_zero (by positivity),
    summable_sq_pairDatum _, summable_wsq_pairDatum _, pairDatum_zero_mode _,
    realField_pairDatum_probeVec _, divFree_pairDatum_probeVec _,
    fun _ _ => pairDatum_zero_mode _, fun _ _ => realField_pairDatum_probeVec _,
    fun _ _ => divFree_pairDatum_probeVec _, fun _ _ => summable_sq_pairDatum _,
    fun _ => continuousOn_const, by positivity, by positivity, ?_, ?_, ?_, zero_le_one,
    mf_no_confined_flow hr⟩
  · have e : κ * r ^ 2 * r ^ 2 = κ * r ^ 4 := by ring
    rw [e]
    have h0 : 0 ≤ κ * r ^ 4 := by positivity
    norm_num at hsmall ⊢
    linarith
  · show en (pairDatum (probeVec (r / 2))) ≤ r ^ 2
    rw [en_pairDatum, hnv]
    nlinarith [sq_nonneg r]
  · show ens (pairDatum (probeVec (r / 2))) ≤ r ^ 2
    rw [ens_pairDatum, hnv]
    nlinarith [sq_nonneg r]

/-- **Probe 4b (compiled must-fail): the force disjunct of
`forced_breakdown_threshold` is load-bearing.** The corollary with its
conclusion weakened to `False` (i.e. "no trap-class datum under an
admissible force ever lacks a flow confined to an admissible box") is FALSE
for every candidate `κ`. The statement below is the frozen one with only its
last line changed. It is a must-fail of the CONCLUSION clause only,
equivalent to Probe 4a's inhabitation and proved from it: it certifies that
the corollary's conclusion is not vacuous, not that any single hypothesis of
the corollary is load-bearing; no hypothesis-drop must-fail for the
corollary is in the tree. -/
theorem forced_breakdown_threshold_without_budget_fails :
    ¬ (∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ →
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) → (∀ t ∈ Ici (0:ℝ), DivFree (g t)) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) →
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) →
      ∀ {Es Zs : ℝ}, 0 ≤ Es → 0 < Zs → κ * Es * Zs ≤ ν ^ 4 →
      en c₀ ≤ Es → ens c₀ ≤ Zs →
      ∀ T : ℝ, 0 ≤ T →
      (¬ ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs)) →
      False) := by
  rintro ⟨κ, hκ, H⟩
  obtain ⟨ν, c₀, g, Es, Zs, T, hν, -, -, hs1, hs2, hc0, hreal, hdiv, hg0, hgreal, hgdiv, hgsum,
    hgc, hEs, hZs, hκE, hE, hZ, hT, hno⟩ := probe_no_confined_flow_inhabited hκ
  exact H hν hs1 hs2 hc0 hreal hdiv hg0 hgreal hgdiv hgsum hgc hEs hZs hκE hE hZ T hT hno

/-! ## Probe 5: the F3-to-F4 seam -/

/-- **Probe 5a: two eternal forced flows with the exported clauses agree on
every horizon.** Any two flows carrying six of the seven clauses exported
by `ns_full_global_flow_forced` (the mode-ODE clause is not needed), under
per-mode continuity of the force (a capstone hypothesis, not an exported
clause; same datum, same force; the boxes may differ) agree at every
`t ≥ 0` and every mode: restrict the exported clauses to
`[0, t]` and apply `theorem_B_unique_forced` at the box
`(max Es Es', max Zs Zs')`. -/
theorem eternal_forced_flows_agree {ν Es Zs Es' Zs' : ℝ} (hν : 0 < ν)
    {c₀ : (Fin 3 → ℤ) → Vel} {c c' g : ℝ → (Fin 3 → ℤ) → Vel}
    (hgc : ∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ)))
    (h0 : c 0 = c₀)
    (hrd : ∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t))
    (hsum : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2))
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ)))
    (heq : ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k))
    (htrap : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs)
    (h0' : c' 0 = c₀)
    (hrd' : ∀ t ∈ Ici (0:ℝ), RealField (c' t) ∧ DivFree (c' t))
    (hsum' : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c' t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c' t l‖ ^ 2))
    (hcont' : ∀ k, ContinuousOn (fun s => c' s k) (Ici (0:ℝ)))
    (heq' : ∀ t ∈ Ici (0:ℝ), ∀ k, c' t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c' s k + lerayProj k (convFull (c' s) k) + g s k))
    (htrap' : ∀ t ∈ Ici (0:ℝ), en (c' t) ≤ Es' ∧ ens (c' t) ≤ Zs') :
    ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c' t k := by
  intro t ht k
  have hsub : Icc (0:ℝ) t ⊆ Ici (0:ℝ) := Icc_subset_Ici_self
  exact theorem_B_unique_forced (E := max Es Es') (Z := max Zs Zs') hν (Set.mem_Ici.mp ht)
    (fun k => (hgc k).mono hsub) h0 h0'
    (fun k => (hcont k).mono hsub) (fun k => (hcont' k).mono hsub)
    (fun s hs => hsum s (hsub hs)) (fun s hs => hsum' s (hsub hs))
    (fun s hs => ⟨(htrap s (hsub hs)).1.trans (le_max_left _ _),
      (htrap s (hsub hs)).2.trans (le_max_left _ _)⟩)
    (fun s hs => ⟨(htrap' s (hsub hs)).1.trans (le_max_right _ _),
      (htrap' s (hsub hs)).2.trans (le_max_right _ _)⟩)
    (fun s hs => (hrd s (hsub hs)).2) (fun s hs => (hrd' s (hsub hs)).2)
    (fun s hs => heq s (hsub hs)) (fun s hs => heq' s (hsub hs))
    t ⟨Set.mem_Ici.mp ht, le_refl t⟩ k

/-- **Probe 5b (composition): any two witnesses of the clause list of
`ns_full_global_flow_forced` for the same data agree on the half line.**
Uniqueness of the eternal flow as a corollary of what it exports, not as a
clause. -/
theorem eternal_forced_witnesses_agree :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      (∀ t ∈ Ici (0:ℝ), g t 0 = 0) →
      (∀ t ∈ Ici (0:ℝ), RealField (g t)) → (∀ t ∈ Ici (0:ℝ), DivFree (g t)) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖g t l‖ ^ 2)) →
      (∀ t ∈ Ici (0:ℝ), en (g t) ≤ G) →
      (∀ k, ContinuousOn (fun t => g t k) (Ici (0:ℝ))) →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ c' : ℝ → (Fin 3 → ℤ) → Vel, c' 0 = c₀ →
          (∀ t ∈ Ici (0:ℝ), RealField (c' t) ∧ DivFree (c' t)) →
          (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c' t l‖ ^ 2) ∧
            Summable (fun l => ‖freq l‖ ^ 2 * ‖c' t l‖ ^ 2)) →
          (∀ k, ContinuousOn (fun s => c' s k) (Ici (0:ℝ))) →
          (∀ t ∈ Ici (0:ℝ), ∀ k, c' t k = c₀ k + ∫ s in (0:ℝ)..t,
            ((-(ν * ‖freq k‖ ^ 2)) • c' s k + lerayProj k (convFull (c' s) k) + g s k)) →
          (∀ t ∈ Ici (0:ℝ), en (c' t) ≤ Es ∧ ens (c' t) ≤ Zs) →
          ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c' t k) := by
  obtain ⟨κ, hκ, H⟩ := ns_full_global_flow_forced
  refine ⟨κ, hκ, ?_⟩
  intro ν Es Zs G hν hEs hZs hκE hGE hGZ c₀ g hE hZ hmean hreal hdiv h0E h0Z hgmean hgreal
    hgdiv hgsum hgen hgc
  obtain ⟨c, hc0, hrd, hsum, hcont, heq, _, htrap⟩ :=
    H hν hEs hZs hκE hGE hGZ hE hZ hmean hreal hdiv h0E h0Z hgmean hgreal hgdiv hgsum hgen hgc
  refine ⟨c, hc0, heq, fun c' h0' hrd' hsum' hcont' heq' htrap' => ?_⟩
  exact eternal_forced_flows_agree hν hgc hc0 hrd hsum hcont heq htrap h0' hrd' hsum' hcont'
    heq' htrap'

end

end TheoremB
