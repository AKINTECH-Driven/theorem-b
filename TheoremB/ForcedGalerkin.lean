/-
  TheoremB/ForcedGalerkin.lean
  Tier 8a, wave F1 of the Theorem B campaign (9 Sep 2026).

  The FORCED Galerkin system, as pure siblings of the unforced chain
  (NSGalerkin / GalerkinLocal / GalerkinFlow): no frozen statement is
  edited.  The forced right-hand side is the Galerkin field with a spectral
  force `g` added mode by mode, spelled INLINE as

      (-(nu * ‖freq k‖^2)) • c t k + lerayProj k (convGal S (c t) k) + g t k

  (no `galRHSForced` definition), so that at `g = 0` a `simpa` converts the
  forced ODE clause into the frozen unforced one
  (`probe_forced_zero_feeds_frozen`, the in-tree composition probe).

  What the file delivers:

  * `force_energy_pairing_le`, `force_enstrophy_pairing_le`: the two
    Cauchy-Schwarz lemmas that bound the force pairings on a finite box by
    2 sqrt(en c) sqrt(en g) and by 2 sqrt(dis c) sqrt(en g) — the enstrophy
    side is paired against the DISSIPATION, so only the L2 size of the
    force ever enters (`real_inner_le_norm` + `Finset.sum_mul_sq_le_sq_mul_sq`;
    the design's `Finset.inner_mul_le_norm_mul_norm` does not exist at the pin).

  * `galerkin_forced_trap_on`: the forced conditional trap on the window,
    sibling of `galerkin_conditional_trap_on`.  The finite-sum surrogates
    of energy and enstrophy have genuine derivatives on `Icc 0 T`; their
    derivatives split into the dissipative part and the pairing part, and
    the two Cauchy-Schwarzed pairing hypotheses feed the forced energy and
    enstrophy identities into `forced_conditional_trap` (ForcedTrap.lean,
    witness kappa := 8 K).

  * `divFree_propagates_on_forced`, `realField_propagates_on_forced`:
    replays of the unforced propagation lemmas under a divergence-free,
    real force.  The divergence component of the force vanishes
    (`DivFree (g t)`), so the divergence component of `c` still obeys the
    homogeneous decay; the conjugation defect of the force vanishes
    (`RealField (g t)`), so the defect ODE of `c` is unchanged.

  * `ns_galerkin_forced_trap_on` (the `Ico` engine form) and
    `ns_galerkin_forced_trap_icc` (the closed-endpoint form, the seam-restart
    lemma for wave F2): the forced Galerkin Navier-Stokes system under a
    supported, real, divergence-free force of L2 size at most `G` keeps a
    real divergence-free datum inside the box {en <= Es, ens <= Zs} whenever
    kappa * Es * Zs <= nu^4, G <= nu^2 * Es, 8 * G <= nu^2 * Zs.  Reuses
    `convGal_energy_pairing`, `convGal_enstrophy_pairing`,
    `inner_lerayProj_of_divFree` (NSGalerkin.lean).

  * `ns_galerkin_unique_on_forced`: two supported flows of the forced
    system with the same datum coincide on the window.  The force cancels
    in the difference, so NO hypothesis on `g` is needed.

  CAVEAT (binding for every downstream claim): at g = 0 this chain is NOT a
  strengthening of the unforced chain.  The trap constant is kappa = 8 K
  (not K), the smallness is non-strict, and the box is a hypothesis rather
  than the energy/enstrophy of the datum.  The forced results must never be
  described as implying or improving the unforced ones; the only compiled
  direction is that the forced ODE clause at g = 0 is the frozen one.

  Nothing here is new mathematics: this is the classical forced small-data
  (small-Grashof) Galerkin energy method.  Textbook sources, named as
  references and NOT verified against by this file: Temam, Navier-Stokes
  Equations, Ch. III; Robinson-Rodrigo-Sadowski, The Three-Dimensional
  Navier-Stokes Equations, Ch. 6; Constantin-Foias, Navier-Stokes
  Equations, Ch. 6.

  CONTRACT: the seven theorem STATEMENTS marked **F1** are frozen (rung10
  Tier-8 blueprint, section 4a, wave F1); `ns_galerkin_forced_trap_on` is
  the blueprint's SKELETON `Ico` engine form (same clauses on `Ico`, not
  byte-frozen).  If a statement cannot be proved as written, do not
  silently repair it: keep it, add a sibling, and report.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.GalerkinLocal
import TheoremB.ForcedTrap
import TheoremB.SobolevNorms

namespace TheoremB

open Set

/-! ## The two Cauchy-Schwarz lemmas for the force pairings -/

/-- Finite Cauchy-Schwarz in square-root form: `∑ aᵢ bᵢ ≤ √(∑ aᵢ²) √(∑ bᵢ²)`
for nonnegative `a`. -/
private lemma fgCS_sqrt {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ i ∈ s, a i * b i) ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) := by
  have hX : 0 ≤ ∑ i ∈ s, a i * b i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (hb i hi)
  have hA : 0 ≤ ∑ i ∈ s, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s a b
  calc (∑ i ∈ s, a i * b i)
      = Real.sqrt ((∑ i ∈ s, a i * b i) ^ 2) := (Real.sqrt_sq hX).symm
    _ ≤ Real.sqrt ((∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) :=
        Real.sqrt_mul hA _

/-- **F1, force energy pairing.**  On a finite box the energy pairing of the
force against the field is bounded by `2 √(en c) √(en g)`. -/
theorem force_energy_pairing_le {S : Finset (Fin 3 → ℤ)} {c g : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hgsupp : ∀ k, k ∉ S → g k = 0) :
    (∑ k ∈ S, 2 * inner ℝ (g k) (c k)) ≤
      2 * Real.sqrt (en c) * Real.sqrt (en g) := by
  have hen_c : en c = ∑ k ∈ S, ‖c k‖ ^ 2 := by
    have h := weighted_tsum_eq_sum (fun _ => (1:ℝ)) hsupp
    simpa [en] using h
  have hen_g : en g = ∑ k ∈ S, ‖g k‖ ^ 2 := by
    have h := weighted_tsum_eq_sum (fun _ => (1:ℝ)) hgsupp
    simpa [en] using h
  have h1 : (∑ k ∈ S, 2 * inner ℝ (g k) (c k)) ≤ 2 * ∑ k ∈ S, ‖g k‖ * ‖c k‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by norm_num)
  have h2 : (∑ k ∈ S, ‖g k‖ * ‖c k‖) ≤
      Real.sqrt (∑ k ∈ S, ‖g k‖ ^ 2) * Real.sqrt (∑ k ∈ S, ‖c k‖ ^ 2) :=
    fgCS_sqrt S _ _ (fun k _ => norm_nonneg _) (fun k _ => norm_nonneg _)
  rw [hen_c, hen_g]
  linarith

/-- **F1, force enstrophy pairing.**  On a finite box the enstrophy pairing
of the force against the field is bounded by `2 √(dis c) √(en g)`: the
weight `‖freq k‖²` is moved onto the field, so only the L² size of the force
enters. -/
theorem force_enstrophy_pairing_le {S : Finset (Fin 3 → ℤ)} {c g : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hgsupp : ∀ k, k ∉ S → g k = 0) :
    (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (g k) (c k))) ≤
      2 * Real.sqrt (dis c) * Real.sqrt (en g) := by
  have hdis_c : dis c = ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c k‖ ^ 2 :=
    weighted_tsum_eq_sum _ hsupp
  have hen_g : en g = ∑ k ∈ S, ‖g k‖ ^ 2 := by
    have h := weighted_tsum_eq_sum (fun _ => (1:ℝ)) hgsupp
    simpa [en] using h
  have h1 : (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (g k) (c k))) ≤
      2 * ∑ k ∈ S, ‖g k‖ * (‖freq k‖ ^ 2 * ‖c k‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hw : (0:ℝ) ≤ ‖freq k‖ ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left (real_inner_le_norm (g k) (c k)) hw
    nlinarith
  have h2 : (∑ k ∈ S, ‖g k‖ * (‖freq k‖ ^ 2 * ‖c k‖)) ≤
      Real.sqrt (∑ k ∈ S, ‖g k‖ ^ 2) *
        Real.sqrt (∑ k ∈ S, (‖freq k‖ ^ 2 * ‖c k‖) ^ 2) :=
    fgCS_sqrt S _ _ (fun k _ => norm_nonneg _) (fun k _ => by positivity)
  have h3 : (∑ k ∈ S, (‖freq k‖ ^ 2 * ‖c k‖) ^ 2) = ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c k‖ ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [h3] at h2
  rw [hdis_c, hen_g]
  linarith

/-! ## The forced conditional trap on the window -/

/-- **F1, forced conditional Galerkin trap on the window.**  Sibling of
`galerkin_conditional_trap_on`: the coefficient ODE, the support, and the
force budget live on `Icc 0 T` only, the two pairing hypotheses are already
in Cauchy-Schwarzed finite-sum form, and the conclusion is the box.  The
force `g` enters only through `en (g t)` inside the pairing hypotheses.  At
`g = 0` this is NOT a strengthening of the unforced trap (see the header). -/
theorem galerkin_forced_trap_on :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)}, (0 : Fin 3 → ℤ) ∉ S →
      ∀ {c F g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, en (g t) ≤ G) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + F t k) t) →
      (∀ t ∈ Ioo (0:ℝ) T, (∑ k ∈ S, 2 * inner ℝ (F t k) (c t k)) ≤
        2 * Real.sqrt (en (c t)) * Real.sqrt (en (g t))) →
      (∀ t ∈ Ioo (0:ℝ) T,
        (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k))) ≤
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) +
        2 * Real.sqrt (dis (c t)) * Real.sqrt (en (g t))) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Ico (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs := by
  obtain ⟨κ, hκ, htrap⟩ := forced_conditional_trap
  refine ⟨κ, hκ, ?_⟩
  intro T ν Es Zs G hν hEs hZs hκb hG hG8 S hS0 c F g hsupp hg hODE hEpair hZpair h0E h0Z
  set cd : ℝ → (Fin 3 → ℤ) → Vel :=
    fun t k => (-(ν * ‖freq k‖ ^ 2)) • c t k + F t k with hcd
  have hIcoIcc : Ico (0:ℝ) T ⊆ Icc 0 T := Ico_subset_Icc_self
  have hIooIcc : Ioo (0:ℝ) T ⊆ Icc 0 T := Ioo_subset_Icc_self
  have hmean : ∀ t ∈ Ico (0:ℝ) T, c t 0 = 0 := fun t ht =>
    hsupp t (hIcoIcc ht) 0 hS0
  have hDsum : ∀ t ∈ Ico (0:ℝ) T,
      Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t ht =>
    summable_weighted_of_support _ (hsupp t (hIcoIcc ht))
  have hgIco : ∀ t ∈ Ico (0:ℝ) T, en (g t) ≤ G := fun t ht => hg t (hIcoIcc ht)
  have hens_eq : ∀ t ∈ Icc (0:ℝ) T,
      ens (c t) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2 := fun t ht =>
    weighted_tsum_eq_sum _ (hsupp t ht)
  have hdis_eq : ∀ t ∈ Icc (0:ℝ) T,
      dis (c t) = ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2 := fun t ht =>
    weighted_tsum_eq_sum _ (hsupp t ht)
  have hen_eq : ∀ t ∈ Icc (0:ℝ) T, en (c t) = ∑ k ∈ S, ‖c t k‖ ^ 2 := by
    intro t ht
    have h := weighted_tsum_eq_sum (fun _ => (1:ℝ)) (hsupp t ht)
    simpa [en] using h
  -- finite-sum surrogates with genuine derivatives on the interval
  set Ef : ℝ → ℝ := fun s => ∑ k ∈ S, ‖c s k‖ ^ 2 with hEf
  set Zf : ℝ → ℝ := fun s => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 with hZf
  have hEfd : ∀ t ∈ Icc (0:ℝ) T,
      HasDerivAt Ef (∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k)) t := by
    intro t ht
    have h := hasDerivAt_weighted_finset_sum_sq (fun _ => (1:ℝ)) S (c' := cd)
      (fun k => hODE t ht k)
    have he : (fun s => ∑ k ∈ S, (1:ℝ) * ‖c s k‖ ^ 2) = Ef := by
      funext s
      simp [hEf]
    have hv : (∑ k ∈ S, (1:ℝ) * (2 * inner ℝ (cd t k) (c t k))) =
        ∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k) := by
      simp
    rw [he, hv] at h
    exact h
  have hZfd : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt Zf
      (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) t := fun t ht =>
    hasDerivAt_weighted_finset_sum_sq (fun k => ‖freq k‖ ^ 2) S (c' := cd)
      (fun k => hODE t ht k)
  -- agreement with the tsum quantities on the interval
  have hEagree : EqOn (fun s => en (c s)) Ef (Icc 0 T) := fun t ht => hen_eq t ht
  have hZagree : EqOn (fun s => ens (c s)) Zf (Icc 0 T) := fun t ht => hens_eq t ht
  have hEev : ∀ t ∈ Ioo (0:ℝ) T, (fun s => en (c s)) =ᶠ[nhds t] Ef := fun t ht =>
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
      (fun s hs => hEagree (hIooIcc hs))
  have hZev : ∀ t ∈ Ioo (0:ℝ) T, (fun s => ens (c s)) =ᶠ[nhds t] Zf := fun t ht =>
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
      (fun s hs => hZagree (hIooIcc hs))
  -- per-mode pairing split
  have hterm : ∀ t k, 2 * inner ℝ (cd t k) (c t k) =
      -(2 * (ν * ‖freq k‖ ^ 2) * ‖c t k‖ ^ 2) + 2 * inner ℝ (F t k) (c t k) := by
    intro t k
    rw [hcd]
    simp only [inner_add_left, real_inner_smul_left]
    rw [real_inner_self_eq_norm_sq]
    ring
  -- the forced_conditional_trap interface
  have hEcf : ContinuousOn Ef (Ico 0 T) := fun t ht =>
    (hEfd t (hIcoIcc ht)).continuousAt.continuousWithinAt
  have hZcf : ContinuousOn Zf (Ico 0 T) := fun t ht =>
    (hZfd t (hIcoIcc ht)).continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun s => en (c s)) (Ico 0 T) :=
    hEcf.congr (fun t ht => hEagree (hIcoIcc ht))
  have hZc : ContinuousOn (fun s => ens (c s)) (Ico 0 T) :=
    hZcf.congr (fun t ht => hZagree (hIcoIcc ht))
  have hEd : DifferentiableOn ℝ (fun s => en (c s)) (Ioo 0 T) := by
    intro t ht
    exact (((hEev t ht).differentiableAt_iff).mpr
      (hEfd t (hIooIcc ht)).differentiableAt).differentiableWithinAt
  have hZd : DifferentiableOn ℝ (fun s => ens (c s)) (Ioo 0 T) := by
    intro t ht
    exact (((hZev t ht).differentiableAt_iff).mpr
      (hZfd t (hIooIcc ht)).differentiableAt).differentiableWithinAt
  -- forced energy identity
  have hEbal : ∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => en (c s)) t ≤
      -(2 * ν) * ens (c t) + 2 * Real.sqrt (en (c t)) * Real.sqrt (en (g t)) := by
    intro t ht
    rw [(hEev t ht).deriv_eq, (hEfd t (hIooIcc ht)).deriv]
    have hsplit : (∑ k ∈ S, 2 * inner ℝ (cd t k) (c t k)) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c t k‖ ^ 2) +
          ∑ k ∈ S, 2 * inner ℝ (F t k) (c t k) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm t k]
      ring
    rw [hsplit, ← hens_eq t (hIooIcc ht)]
    have h2 := hEpair t ht
    linarith
  -- forced enstrophy identity
  have hZbal : ∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
      -(2 * ν) * dis (c t) +
        2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) +
        2 * Real.sqrt (dis (c t)) * Real.sqrt (en (g t)) := by
    intro t ht
    rw [(hZev t ht).deriv_eq, (hZfd t (hIooIcc ht)).deriv]
    have hsplit : (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (cd t k) (c t k))) =
        -(2 * ν * ∑ k ∈ S, ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) +
          ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (F t k) (c t k)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm t k]
      ring
    rw [hsplit, ← hdis_eq t (hIooIcc ht)]
    have h2 := hZpair t ht
    linarith
  exact htrap hν hEs hZs hκb hG hG8 hmean hDsum hgIco hEc hZc hEd hZd hEbal hZbal h0E h0Z

/-! ## Forward propagation under a divergence-free, real force -/

/-- **F1, divergence-freeness propagates under a divergence-free force.**
The divergence component of the force vanishes, so the divergence component
of the field still obeys the homogeneous linear decay of
`divFree_propagates_on`. -/
theorem divFree_propagates_on_forced {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    {c g : ℝ → (Fin 3 → ℤ) → Vel}
    (hgdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (g t))
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t)
    (h0 : DivFree (c 0)) : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) := by
  intro t htm k
  set lam : ℝ := ν * ‖freq k‖ ^ 2 with hlamdf
  have hlamnn : (0:ℝ) ≤ lam := by
    rw [hlamdf]
    exact mul_nonneg hν (sq_nonneg _)
  set y : ℝ → ℂ := fun s => dotR (c s k) (freq k) with hy
  -- dotR (·, freq k) is linear; transport the derivative componentwise
  have hdotlin : ∀ (a : Vel) (b : Vel),
      dotR (a + b) (freq k) = dotR a (freq k) + dotR b (freq k) := by
    intro a b
    simp [dotR, Finset.sum_add_distrib, add_mul]
  have hdotsmul : ∀ (z : ℝ) (a : Vel),
      dotR (z • a) (freq k) = (z : ℂ) * dotR a (freq k) := by
    intro z a
    simp [dotR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hyderiv : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt y (-(lam : ℂ) * y s) s := by
    intro s hs
    have h := hODE s hs k
    have hco : ∀ j : Fin 3, HasDerivAt (fun u => (c u k).ofLp j)
        (((-(lam)) • c s k + lerayProj k (convGal S (c s) k) + g s k).ofLp j) s := by
      intro j
      exact ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h
    have hterm : ∀ j : Fin 3, HasDerivAt
        (fun u => (c u k).ofLp j * (((freq k).ofLp j : ℝ) : ℂ))
        ((((-(lam)) • c s k + lerayProj k (convGal S (c s) k) + g s k).ofLp j) *
          (((freq k).ofLp j : ℝ) : ℂ)) s := fun j => (hco j).mul_const _
    have hsum := HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    have heq1 : (∑ j ∈ Finset.univ, fun u => (c u k).ofLp j *
        (((freq k).ofLp j : ℝ) : ℂ)) = y := by
      funext u
      simp [hy, dotR, Finset.sum_apply]
    rw [heq1] at hsum
    have heq2 : (∑ j, (((-(lam)) • c s k +
        lerayProj k (convGal S (c s) k) + g s k).ofLp j) * (((freq k).ofLp j : ℝ) : ℂ)) =
        -(lam : ℂ) * y s := by
      have hdd : (∑ j, (((-(lam)) • c s k +
          lerayProj k (convGal S (c s) k) + g s k).ofLp j) * (((freq k).ofLp j : ℝ) : ℂ)) =
          dotR ((-(lam)) • c s k + lerayProj k (convGal S (c s) k) + g s k) (freq k) := rfl
      rw [hdd, hdotlin, hdotlin, hdotsmul, dotR_lerayProj_freq, hgdiv s hs k, add_zero,
        add_zero, hy]
      push_cast
      ring
    rw [heq2] at hsum
    exact hsum
  -- convert the derivative value to real-smul form
  have hyderiv' : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt y ((-lam) • y s) s := by
    intro s hs
    have h := hyderiv s hs
    have hv : -(lam : ℂ) * y s = (-lam) • y s := by
      rw [Complex.real_smul]
      push_cast
      ring
    rwa [hv] at h
  -- the squared norm of the divergence component decays
  have hφd : ∀ s ∈ Icc (0:ℝ) T, HasDerivAt (fun u : ℝ => ‖y u‖ ^ 2)
      (2 * inner ℝ ((-lam) • y s) (y s)) s := by
    intro s hs
    have hyd := hyderiv' s hs
    have h1 : HasDerivAt (fun u : ℝ => inner ℝ (y u) (y u))
        (inner ℝ (y s) ((-lam) • y s) + inner ℝ ((-lam) • y s) (y s)) s :=
      hyd.inner ℝ hyd
    have h2 : (fun u : ℝ => ‖y u‖ ^ 2) = fun u : ℝ => inner ℝ (y u) (y u) := by
      funext u
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (y s) ((-lam) • y s) + inner ℝ ((-lam) • y s) (y s) =
        2 * inner ℝ ((-lam) • y s) (y s) := by
      rw [real_inner_comm (y s) ((-lam) • y s)]; ring
    rw [h2, ← h4]
    exact h1
  have ht0 : (0:ℝ) ≤ t := htm.1
  have hsubI : ∀ s ∈ Icc (0:ℝ) t, s ∈ Icc (0:ℝ) T := fun s hs =>
    ⟨hs.1, le_trans hs.2 htm.2⟩
  have hnonpos : ∀ s ∈ Ioo (0:ℝ) t, deriv (fun u : ℝ => ‖y u‖ ^ 2) s ≤ 0 := by
    intro s hs
    have hsm : s ∈ Icc (0:ℝ) T := hsubI s ⟨hs.1.le, hs.2.le⟩
    rw [(hφd s hsm).deriv]
    have hv : (2:ℝ) * inner ℝ ((-lam) • y s) (y s) = -(2 * lam) * ‖y s‖ ^ 2 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      ring
    rw [hv]
    have h1 : (0:ℝ) ≤ 2 * lam * ‖y s‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hlamnn) (sq_nonneg _)
    linarith
  have hcont : ContinuousOn (fun u : ℝ => ‖y u‖ ^ 2) (Icc 0 t) :=
    fun s hs => (hφd s (hsubI s hs)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => ‖y u‖ ^ 2) (Ioo 0 t) :=
    fun s hs => (hφd s (hsubI s ⟨hs.1.le, hs.2.le⟩)).differentiableAt.differentiableWithinAt
  have hle : ‖y t‖ ^ 2 ≤ ‖y 0‖ ^ 2 := le_of_deriv_nonpos ht0 hcont hdiff hnonpos
  have hy0 : y 0 = 0 := h0 k
  have hz : ‖y t‖ ^ 2 = 0 := by
    have h00 : ‖y 0‖ ^ 2 = 0 := by rw [hy0, norm_zero]; norm_num
    have hnn : (0:ℝ) ≤ ‖y t‖ ^ 2 := sq_nonneg _
    linarith
  have hyt : y t = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  exact hyt

private lemma fgConjVel_zero : conjVel 0 = 0 := by
  ext j
  simp [conjVel]

private lemma fgConjVel_real_smul (r : ℝ) (v : Vel) :
    conjVel (r • v) = r • conjVel v :=
  conjVelL.map_smul r v

private lemma fgConjVel_add (a b : Vel) : conjVel (a + b) = conjVel a + conjVel b :=
  conjVelL.map_add a b

/-- **F1, reality propagates under a real force.**  The conjugation defect
of the force vanishes (`RealField (g t)`), so the mode-clamped conjugation
defect of the field obeys the same damped linear system as in
`realField_propagates_on`, and the interval Gronwall kills it. -/
theorem realField_propagates_on_forced {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    (hSsym : ∀ k ∈ S, -k ∈ S) {c g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0)
    (hgreal : ∀ t ∈ Icc (0:ℝ) T, RealField (g t))
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t)
    (h0real : RealField (c 0)) : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) := by
  classical
  by_cases hT : (0:ℝ) ≤ T
  · -- main case: the window is nonempty
    -- the mode-clamped conjugation defect (clamping restores GLOBAL support)
    set d : ℝ → (Fin 3 → ℤ) → Vel :=
      fun t k => if k ∈ S then c t (-k) - conjVel (c t k) else 0 with hdDef
    set R : ℝ → (Fin 3 → ℤ) → Vel :=
      fun t k => if k ∈ S then lerayProj (-k) (convGal S (c t) (-k)) -
        conjVel (lerayProj k (convGal S (c t) k)) else 0 with hRDef
    set lam : (Fin 3 → ℤ) → ℝ := fun k => ν * ‖freq k‖ ^ 2 with hlamDef
    have hlamnn : ∀ k, 0 ≤ lam k := by
      intro k
      simp only [hlamDef]
      exact mul_nonneg hν (sq_nonneg _)
    have hSnot : ∀ k, k ∉ S → -k ∉ S := by
      intro k hk hnk
      exact hk (by simpa using hSsym (-k) hnk)
    -- the clamped defect ODE at points of the window (the force cancels by reality)
    have hdderiv : ∀ s ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun u => d u k)
        ((-(lam k)) • d s k + R s k) s := by
      intro s hs k
      by_cases hk : k ∈ S
      · have h1 : HasDerivAt (fun u => c u (-k))
            ((-(ν * ‖freq (-k)‖ ^ 2)) • c s (-k) +
              lerayProj (-k) (convGal S (c s) (-k)) + g s (-k)) s := hODE s hs (-k)
        have hfneg : ‖freq (-k)‖ = ‖freq k‖ := by rw [freq_neg, norm_neg]
        rw [hfneg, hgreal s hs k] at h1
        have h2 : HasDerivAt (fun u => conjVel (c u k))
            (conjVel ((-(ν * ‖freq k‖ ^ 2)) • c s k +
              lerayProj k (convGal S (c s) k) + g s k)) s := by
          have := (conjVelL.hasFDerivAt (x := c s k)).comp_hasDerivAt s (hODE s hs k)
          exact this
        have h2' : HasDerivAt (fun u => conjVel (c u k))
            ((-(ν * ‖freq k‖ ^ 2)) • conjVel (c s k) +
              conjVel (lerayProj k (convGal S (c s) k)) + conjVel (g s k)) s := by
          rwa [fgConjVel_add, fgConjVel_add, fgConjVel_real_smul] at h2
        have h3 := h1.sub h2'
        have hfun : ((fun u => c u (-k)) - fun u => conjVel (c u k)) = fun u => d u k := by
          funext u
          simp only [Pi.sub_apply, hdDef, if_pos hk]
        have hval : ((-(ν * ‖freq k‖ ^ 2)) • c s (-k) +
              lerayProj (-k) (convGal S (c s) (-k)) + conjVel (g s k)) -
            ((-(ν * ‖freq k‖ ^ 2)) • conjVel (c s k) +
              conjVel (lerayProj k (convGal S (c s) k)) + conjVel (g s k)) =
            (-(lam k)) • d s k + R s k := by
          simp only [hlamDef, hdDef, hRDef, if_pos hk, smul_sub]
          abel
        rw [hfun, hval] at h3
        exact h3
      · have hzero : (fun u => d u k) = fun _ : ℝ => (0 : Vel) := by
          funext u
          simp only [hdDef, if_neg hk]
        have hval : (-(lam k)) • d s k + R s k = 0 := by
          simp only [hdDef, hRDef, if_neg hk, smul_zero, add_zero]
        rw [hzero, hval]
        exact hasDerivAt_const s 0
    have hdsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0 := by
      intro s k hk
      simp only [hdDef, if_neg hk]
    have hd0 : ∀ k, d 0 k = 0 := by
      intro k
      by_cases hk : k ∈ S
      · simp only [hdDef, if_pos hk]
        rw [h0real k, sub_self]
      · simp only [hdDef, if_neg hk]
    -- bound the field on the compact window
    have hne : (Icc (0:ℝ) T).Nonempty := ⟨0, le_refl 0, hT⟩
    obtain ⟨M, hM0, hMb⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0:ℝ) T, ∀ j, ‖c s j‖ ≤ M := by
      have hmode : ∀ j, ContinuousOn (fun s : ℝ => c s j) (Icc (0:ℝ) T) :=
        fun j s hs => ((hODE s hs j).continuousAt).continuousWithinAt
      have hcont : ContinuousOn (fun s : ℝ => ∑ j ∈ S, ‖c s j‖) (Icc (0:ℝ) T) :=
        continuousOn_finsetSum S fun j _ => (hmode j).norm
      obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
      refine ⟨∑ j ∈ S, ‖c s₀ j‖,
        Finset.sum_nonneg fun j _ => norm_nonneg _, ?_⟩
      intro s hs j
      by_cases hj : j ∈ S
      · calc ‖c s j‖ ≤ ∑ i ∈ S, ‖c s i‖ :=
              Finset.single_le_sum (f := fun i => ‖c s i‖)
                (fun i _ => norm_nonneg _) hj
          _ ≤ ∑ i ∈ S, ‖c s₀ i‖ := hmax hs
      · rw [hsupp s hs j hj]
        simp only [norm_zero]
        exact Finset.sum_nonneg fun i _ => norm_nonneg _
    -- the Lipschitz constant from the forcing bound
    obtain ⟨C, hC0, hCb⟩ := defect_forcing_bound hSsym
    have hRb : ∀ s ∈ Icc (0:ℝ) T, ∀ j ∈ S,
        ‖R s j‖ ^ 2 ≤ (C * M ^ 2) * (∑ i ∈ S, ‖d s i‖ ^ 2) := by
      intro s hs j hj
      have hb := hCb (c := c s) (hsupp s hs) hM0 (fun i => hMb s hs i) j
      have hRj : R s j = lerayProj (-j) (convGal S (c s) (-j)) -
          conjVel (lerayProj j (convGal S (c s) j)) := by
        simp only [hRDef, if_pos hj]
      have hsum : (∑ i ∈ S, ‖d s i‖ ^ 2) = ∑ i ∈ S, ‖c s (-i) - conjVel (c s i)‖ ^ 2 :=
        Finset.sum_congr rfl fun i hi => by simp only [hdDef, if_pos hi]
      rw [hRj, hsum]
      exact hb
    -- the interval Gronwall
    have hvan : ∀ t ∈ Icc (0:ℝ) T, ∀ k, d t k = 0 :=
      defect_vanishes_on' (mul_nonneg hC0 (sq_nonneg M)) (le_refl (0:ℝ)) hT hlamnn
        hdderiv hdsupp hRb hd0
    -- unfold the defect vanishing into the reality statement
    intro t ht k
    by_cases hk : k ∈ S
    · have hz := hvan t ht k
      simp only [hdDef, if_pos hk] at hz
      exact sub_eq_zero.mp hz
    · rw [hsupp t ht (-k) (hSnot k hk), hsupp t ht k hk, fgConjVel_zero]
  · -- ¬ 0 ≤ T: the window is empty, the statement is vacuous
    intro t ht
    exact absurd (ht.1.trans ht.2) hT

/-! ## The forced Galerkin Navier-Stokes trap -/

/-- **F1, the forced Galerkin trap (engine form on `Ico`).**  The blueprint's
SKELETON `Ico` form of `ns_galerkin_forced_trap_icc`: same clauses, box
conclusion on `Ico 0 T`.  Reality and divergence-freeness propagate under
the real divergence-free force; the Leray projection is invisible against
a divergence-free field; the convection pairings are the unforced ones and
the force pairings are the two Cauchy-Schwarz lemmas. -/
theorem ns_galerkin_forced_trap_on :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) →
      ∀ {c g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → g t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, RealField (g t)) →
      (∀ t ∈ Icc (0:ℝ) T, DivFree (g t)) →
      (∀ t ∈ Icc (0:ℝ) T, en (g t) ≤ G) →
      RealField (c 0) → DivFree (c 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Ico (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs := by
  obtain ⟨κ, hκ, htrap⟩ := galerkin_forced_trap_on
  refine ⟨κ, hκ, ?_⟩
  intro T ν Es Zs G hν hEs hZs hκb hG hG8 S hS0 hSsym c g hsupp hgsupp hgreal hgdiv hg
    h0real h0div hODE h0E h0Z
  have hIooIcc : Ioo (0:ℝ) T ⊆ Icc 0 T := Ioo_subset_Icc_self
  have hreal : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) :=
    realField_propagates_on_forced hν.le hSsym hsupp hgreal hODE h0real
  have hdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) :=
    divFree_propagates_on_forced hν.le hgdiv hODE h0div
  have hpair : ∀ t ∈ Icc (0:ℝ) T, ∀ k,
      inner ℝ (lerayProj k (convGal S (c t) k)) (c t k) =
        inner ℝ (convGal S (c t) k) (c t k) := fun t ht k =>
    inner_lerayProj_of_divFree (hdiv t ht) k _
  -- the forced RHS re-associated to the abstract trap's `F`
  have hODE' : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k +
        (lerayProj k (convGal S (c t) k) + g t k)) t := fun t ht k =>
    (hODE t ht k).congr_deriv (add_assoc _ _ _)
  refine htrap hν hEs hZs hκb hG hG8 hS0
    (F := fun t k => lerayProj k (convGal S (c t) k) + g t k) hsupp hg hODE' ?_ ?_ h0E h0Z
  · intro t ht
    have htI := hIooIcc ht
    have hE := convGal_energy_pairing (hsupp t htI) (hreal t htI) (hdiv t htI)
    have hF := force_energy_pairing_le (hsupp t htI) (hgsupp t htI)
    have hsplit : (∑ k ∈ S, 2 * inner ℝ (lerayProj k (convGal S (c t) k) + g t k) (c t k)) =
        (∑ k ∈ S, 2 * inner ℝ (convGal S (c t) k) (c t k)) +
          ∑ k ∈ S, 2 * inner ℝ (g t k) (c t k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_add_left, hpair t htI k]
      ring
    show (∑ k ∈ S, 2 * inner ℝ (lerayProj k (convGal S (c t) k) + g t k) (c t k)) ≤
      2 * Real.sqrt (en (c t)) * Real.sqrt (en (g t))
    rw [hsplit, hE, zero_add]
    exact hF
  · intro t ht
    have htI := hIooIcc ht
    have hZ := convGal_enstrophy_pairing (hsupp t htI) (hreal t htI)
    have hF := force_enstrophy_pairing_le (hsupp t htI) (hgsupp t htI)
    have hsplit : (∑ k ∈ S, ‖freq k‖ ^ 2 *
          (2 * inner ℝ (lerayProj k (convGal S (c t) k) + g t k) (c t k))) =
        (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S (c t) k) (c t k))) +
          ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (g t k) (c t k)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_add_left, hpair t htI k]
      ring
    show (∑ k ∈ S, ‖freq k‖ ^ 2 *
          (2 * inner ℝ (lerayProj k (convGal S (c t) k) + g t k) (c t k))) ≤
      2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
          (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) +
        2 * Real.sqrt (dis (c t)) * Real.sqrt (en (g t))
    rw [hsplit]
    linarith

/-- **F1, the forced Galerkin trap (closed-endpoint form).**  Sibling of
`ns_galerkin_trap_zero_data_icc`: the box holds on the CLOSED window
`Icc 0 T` — the seam-restart lemma for the forced gluing induction of wave
F2.  The endpoint is reached by continuity of the finite-sum surrogates from
the open side. -/
theorem ns_galerkin_forced_trap_icc :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) →
      ∀ {c g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → c t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, k ∉ S → g t k = 0) →
      (∀ t ∈ Icc (0:ℝ) T, RealField (g t)) →
      (∀ t ∈ Icc (0:ℝ) T, DivFree (g t)) →
      (∀ t ∈ Icc (0:ℝ) T, en (g t) ≤ G) →
      RealField (c 0) → DivFree (c 0) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs := by
  obtain ⟨κ, hκ, htrap⟩ := ns_galerkin_forced_trap_on
  refine ⟨κ, hκ, ?_⟩
  intro T ν Es Zs G hν hEs hZs hκb hG hG8 S hS0 hSsym c g hsupp hgsupp hgreal hgdiv hg
    h0real h0div hODE h0E h0Z
  have hIco := htrap hν hEs hZs hκb hG hG8 hS0 hSsym hsupp hgsupp hgreal hgdiv hg
    h0real h0div hODE h0E h0Z
  intro t ht
  by_cases htT : t < T
  · exact hIco t ⟨ht.1, htT⟩
  · -- t = T (the endpoint); T > 0 or the window is degenerate
    have htT' : T = t := (le_antisymm ht.2 (not_lt.mp htT)).symm
    subst htT'
    by_cases hT0 : 0 < T
    · -- continuity limit from the open side
      have hmode : ∀ k, ContinuousOn (fun s : ℝ => c s k) (Icc 0 T) :=
        fun k s hs => (hODE s hs k).continuousAt.continuousWithinAt
      have hEfc : ContinuousOn (fun s : ℝ => ∑ k ∈ S, ‖c s k‖ ^ 2) (Icc 0 T) := by
        refine continuousOn_finsetSum S fun k _ => ?_
        exact ((hmode k).norm).pow 2
      have hZfc : ContinuousOn
          (fun s : ℝ => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) (Icc 0 T) := by
        refine continuousOn_finsetSum S fun k _ => ?_
        exact continuousOn_const.mul (((hmode k).norm).pow 2)
      have hagreeE : ∀ s ∈ Icc (0:ℝ) T,
          en (c s) = ∑ k ∈ S, ‖c s k‖ ^ 2 := by
        intro s hs
        have h := weighted_tsum_eq_sum (fun _ => (1:ℝ)) (hsupp s hs)
        simpa [en] using h
      have hagreeZ : ∀ s ∈ Icc (0:ℝ) T,
          ens (c s) = ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2 := fun s hs =>
        weighted_tsum_eq_sum _ (hsupp s hs)
      -- the filter 𝓝[Ico 0 T] T is nontrivial
      have hTmem : T ∈ closure (Ico (0:ℝ) T) := by
        rw [closure_Ico (ne_of_lt hT0)]
        exact ⟨hT0.le, le_refl T⟩
      have hne : (nhdsWithin T (Ico (0:ℝ) T)).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp hTmem
      constructor
      · have htend : Filter.Tendsto (fun s => ∑ k ∈ S, ‖c s k‖ ^ 2)
            (nhdsWithin T (Ico (0:ℝ) T)) (nhds (∑ k ∈ S, ‖c T k‖ ^ 2)) := by
          have h1 := (hEfc T ⟨hT0.le, le_refl T⟩).tendsto
          exact h1.mono_left (nhdsWithin_mono T Ico_subset_Icc_self)
        have hev : ∀ᶠ s in nhdsWithin T (Ico (0:ℝ) T),
            (∑ k ∈ S, ‖c s k‖ ^ 2) ≤ Es := by
          refine Filter.eventually_iff_exists_mem.mpr
            ⟨Ico (0:ℝ) T, self_mem_nhdsWithin, fun s hs => ?_⟩
          rw [← hagreeE s (Ico_subset_Icc_self hs)]
          exact (hIco s hs).1
        have hlim := le_of_tendsto htend hev
        rw [hagreeE T ⟨hT0.le, le_refl T⟩]
        exact hlim
      · have htend : Filter.Tendsto
            (fun s => ∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2)
            (nhdsWithin T (Ico (0:ℝ) T))
            (nhds (∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c T k‖ ^ 2)) := by
          have h1 := (hZfc T ⟨hT0.le, le_refl T⟩).tendsto
          exact h1.mono_left (nhdsWithin_mono T Ico_subset_Icc_self)
        have hev : ∀ᶠ s in nhdsWithin T (Ico (0:ℝ) T),
            (∑ k ∈ S, ‖freq k‖ ^ 2 * ‖c s k‖ ^ 2) ≤ Zs := by
          refine Filter.eventually_iff_exists_mem.mpr
            ⟨Ico (0:ℝ) T, self_mem_nhdsWithin, fun s hs => ?_⟩
          rw [← hagreeZ s (Ico_subset_Icc_self hs)]
          exact (hIco s hs).2
        have hlim := le_of_tendsto htend hev
        rw [hagreeZ T ⟨hT0.le, le_refl T⟩]
        exact hlim
    · -- T = 0: the endpoint IS the initial time
      have hT0' : T = 0 := le_antisymm (not_lt.mp hT0) ht.1
      subst hT0'
      exact ⟨h0E, h0Z⟩

/-! ## Uniqueness under forcing -/

/-- **F1, uniqueness of forced Galerkin flows on the window.**  Replay of
`ns_galerkin_unique_on`: the difference of two flows of the forced system
satisfies the SAME defect ODE as in the unforced case because the force
cancels, so NO hypothesis on `g` is needed. -/
theorem ns_galerkin_unique_on_forced {ν T : ℝ} (hν : 0 ≤ ν) {S : Finset (Fin 3 → ℤ)}
    {c₁ c₂ g : ℝ → (Fin 3 → ℤ) → Vel}
    (hs₁ : ∀ (t : ℝ) k, k ∉ S → c₁ t k = 0)
    (hs₂ : ∀ (t : ℝ) k, k ∉ S → c₂ t k = 0)
    (hODE₁ : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convGal S (c₁ t) k) + g t k) t)
    (hODE₂ : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convGal S (c₂ t) k) + g t k) t)
    (h0 : ∀ k, c₁ 0 k = c₂ 0 k) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₂ t k := by
  by_cases hT : (0:ℝ) ≤ T
  · -- the defect
    set d : ℝ → (Fin 3 → ℤ) → Vel := fun t k => c₁ t k - c₂ t k with hd
    set R : ℝ → (Fin 3 → ℤ) → Vel := fun t k =>
      lerayProj k (convGal S (c₁ t) k) - lerayProj k (convGal S (c₂ t) k) with hR
    set lam : (Fin 3 → ℤ) → ℝ := fun k => ν * ‖freq k‖ ^ 2 with hlam
    have hlamnn : ∀ k, 0 ≤ lam k := fun k => by positivity
    have hdderiv : ∀ s ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun u => d u k)
        ((-(lam k)) • d s k + R s k) s := by
      intro s hs k
      have h3 := (hODE₁ s hs k).sub (hODE₂ s hs k)
      have hval : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convGal S (c₁ s) k)
            + g s k) -
          ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convGal S (c₂ s) k) + g s k) =
          (-(lam k)) • d s k + R s k := by
        rw [hlam, hd, hR]
        simp only [smul_sub]
        abel
      rw [hval] at h3
      exact h3
    have hdsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0 := by
      intro s k hk
      rw [hd]
      simp only
      rw [hs₁ s k hk, hs₂ s k hk, sub_self]
    have hd0 : ∀ k, d 0 k = 0 := by
      intro k
      rw [hd]
      simp only
      rw [h0 k, sub_self]
    -- bound both fields on the window
    obtain ⟨M, hM0, hMb⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (0:ℝ) T,
        (∀ j, ‖c₁ s j‖ ≤ M) ∧ (∀ j, ‖c₂ s j‖ ≤ M) := by
      have hmode : ∀ j, ContinuousOn (fun s : ℝ => c₁ s j) (Icc 0 T) := fun j t ht =>
        (hODE₁ t ht j).continuousAt.continuousWithinAt
      have hmode₂ : ∀ j, ContinuousOn (fun s : ℝ => c₂ s j) (Icc 0 T) := fun j t ht =>
        (hODE₂ t ht j).continuousAt.continuousWithinAt
      have hcont : ContinuousOn
          (fun s : ℝ => (∑ j ∈ S, ‖c₁ s j‖) + ∑ j ∈ S, ‖c₂ s j‖) (Icc 0 T) := by
        apply ContinuousOn.add
        · exact continuousOn_finsetSum S fun j _ => (hmode j).norm
        · exact continuousOn_finsetSum S fun j _ => (hmode₂ j).norm
      have hne : (Icc (0:ℝ) T).Nonempty := ⟨0, le_refl 0, hT⟩
      obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
      refine ⟨(∑ j ∈ S, ‖c₁ s₀ j‖) + ∑ j ∈ S, ‖c₂ s₀ j‖, by positivity, ?_⟩
      intro s hs
      have hsum1 : 0 ≤ ∑ j ∈ S, ‖c₁ s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      have hsum2 : 0 ≤ ∑ j ∈ S, ‖c₂ s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      constructor
      · intro j
        by_cases hj : j ∈ S
        · calc ‖c₁ s j‖ ≤ ∑ i ∈ S, ‖c₁ s i‖ :=
                Finset.single_le_sum (f := fun i => ‖c₁ s i‖)
                  (fun i _ => norm_nonneg _) hj
            _ ≤ (∑ i ∈ S, ‖c₁ s i‖) + ∑ i ∈ S, ‖c₂ s i‖ := by linarith
            _ ≤ _ := hmax hs
        · rw [hs₁ s j hj]
          simp only [norm_zero]
          have := hmax hs
          positivity
      · intro j
        by_cases hj : j ∈ S
        · calc ‖c₂ s j‖ ≤ ∑ i ∈ S, ‖c₂ s i‖ :=
                Finset.single_le_sum (f := fun i => ‖c₂ s i‖)
                  (fun i _ => norm_nonneg _) hj
            _ ≤ (∑ i ∈ S, ‖c₁ s i‖) + ∑ i ∈ S, ‖c₂ s i‖ := by linarith
            _ ≤ _ := hmax hs
        · rw [hs₂ s j hj]
          simp only [norm_zero]
          have := hmax hs
          positivity
    obtain ⟨C, hC0, hCb⟩ := two_flow_forcing_bound (S := S)
    have hRb : ∀ s ∈ Icc (0:ℝ) T, ∀ j ∈ S,
        ‖R s j‖ ^ 2 ≤ (C * M ^ 2) * (∑ i ∈ S, ‖d s i‖ ^ 2) := by
      intro s hs j _
      have := hCb (hs₁ s) (hs₂ s) hM0 (hMb s hs).1 (hMb s hs).2 j
      simpa [hR, hd] using this
    intro t ht k
    have hz := defect_vanishes_on' (mul_nonneg hC0 (by positivity)) (le_refl 0) hT
      hlamnn hdderiv hdsupp hRb hd0 t ht k
    have : c₁ t k - c₂ t k = 0 := hz
    exact sub_eq_zero.mp this
  · intro t ht
    exact absurd (ht.1.trans ht.2) hT

/-! ## In-tree composition probe -/

/-- **F1 composition probe: the forced ODE clause at `g = 0` IS the frozen
unforced clause.**  Because the forced right-hand side is spelled inline
(`… + g t k`), substituting the zero force reduces it to the ODE hypothesis
of `ns_galerkin_trap_zero_data_icc` / `ns_galerkin_unique_on` by `simpa`.
This is the only compiled direction between the two chains; it is NOT a
strengthening claim (see the file header). -/
theorem probe_forced_zero_feeds_frozen {ν T : ℝ} {S : Finset (Fin 3 → ℤ)}
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) +
        (fun (_ : ℝ) (_ : Fin 3 → ℤ) => (0 : Vel)) t k) t) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t := by
  intro t ht k
  simpa using hODE t ht k

end TheoremB
