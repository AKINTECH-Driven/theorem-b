/-
  TheoremB/ForcedTrap.lean
  Tier 8a, wave F0 of the Theorem B campaign (9 Sep 2026).

  The forced trap: the Tier-2 conditional trap (ConditionalTheoremB.lean)
  transplanted to a trajectory driven by a spectral force `g`.  Under a
  force whose L2 size stays below a budget `G`, small data stays inside a
  BOX  {en <= Es, ens <= Zs}  for the whole lifespan, whenever

      kappa_forced * Es * Zs <= nu^4,   G <= nu^2 * Es,   8 * G <= nu^2 * Zs,

  with witness kappa_forced := 8 * K, K the master-inequality constant of
  SpectralNorms.lean.  Only `en (g t)` (the L2 size of the force) enters:
  the enstrophy-side force pairing is taken against the DISSIPATION and
  Young-split, so no H1 bound on the force is needed.  As in Tier 2, the
  two differential inequalities are the standing conditional hypotheses;
  discharging them from the forced Galerkin ODE is wave F1's job.

  Nothing here is new mathematics: this is the classical forced small-data
  (small-Grashof) argument.  Textbook sources, named as references and NOT
  verified against by this file: Temam, Navier-Stokes Equations, Ch. III;
  Robinson-Rodrigo-Sadowski, The Three-Dimensional Navier-Stokes Equations,
  Ch. 6; Foias-Manley-Rosa-Temam, Navier-Stokes Equations and Turbulence,
  Ch. II.

  Mathematical content:

  * `barrier_forward_invariance` (the one analysis brick not already in the repo): a function
    continuous on [0, T) and differentiable on (0, T), starting at or
    below a level M, whose derivative is nonpositive on a strip
    M < f < M' just above the level, never crosses M.  Under forcing
    neither energy nor enstrophy is monotone, so the first-exit bootstrap
    of RiccatiTrap.lean does not apply; the barrier replaces it.  Proof:
    if f b > M, let a be the LAST time in [0, b] at or below M and c the
    FIRST time in [a, b] at or above an intermediate level L in
    (M, min M' (f b)); on (a, c) the strip condition holds, so
    `le_of_deriv_nonpos` gives f c <= f a <= M < L <= f c.

  * `forced_trap_forward_invariance`: the box is forward-invariant under
    the two gated derivative bounds (energy gated at Es; enstrophy gated on
    the strip Zs <= Z <= 2 Zs given E <= Es).  Two barrier applications.

  * `forced_conditional_trap`: the box trap for spectral trajectories with
    kappa := 8 K.  Energy gate: sqrt(E) sqrt(g) <= nu E <= nu Z by
    `en_le_ens` (EnergyDecay.lean; Vel-only, hence the Vel statement).
    Enstrophy gate: `master_inequality` absorbs the convection term into
    nu D + (K / nu^3) Z^3, Young splits 2 sqrt(D) sqrt(g) into
    (nu/2) D + (2/nu) g, the force budget and `ens_le_dis` give
    (2/nu) g <= (nu/4) D, and `ens_sq_le_en_mul_dis` with the box gives
    (K/nu^3) Z^3 <= (nu/4) D.  All bounds are non-strict; barriers never
    need strictness.

  * `forced_thresholds_inhabited`: for every kappa, nu > 0 the three
    thresholds admit a strictly positive force budget.

  CAVEAT (binding for every downstream claim): at g = 0 this is NOT a
  strengthening of the unforced trap.  kappa_forced = 8 K, not K, the
  smallness is non-strict, and the energy clause asked for here is the
  full dissipative inequality  E' <= -2 nu Z + ...  rather than the bare
  E' <= 0 of `conditional_trap`.  The forced results must never be
  described as implying or improving the unforced ones.

  CONTRACT: the four theorem STATEMENTS are frozen (rung10 Tier-8
  blueprint, section 4a, wave F0).  If a statement cannot be proved as
  written, do not silently repair it: keep it, add a sibling, and report.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.RiccatiTrap
import TheoremB.SpectralNorms
import TheoremB.EnergyDecay

namespace TheoremB

open Set

/-- **F0, barrier lemma.**  A function continuous on `[0, T)`, differentiable
on `(0, T)`, starting at or below the level `M`, whose derivative is
nonpositive wherever it sits in the strip `M < f < M'`, never rises above
`M` on `[0, T)`.  This replaces the first-exit bootstrap of
`trap_forward_invariance`, which needs monotone descent inside the region
and is unavailable under forcing. -/
theorem barrier_forward_invariance {T M M' : ℝ} (hMM' : M < M') {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ico 0 T)) (hd : DifferentiableOn ℝ f (Ioo 0 T))
    (h0 : f 0 ≤ M)
    (h' : ∀ t ∈ Ioo (0:ℝ) T, M < f t → f t < M' → deriv f t ≤ 0) :
    ∀ t ∈ Ico (0:ℝ) T, f t ≤ M := by
  intro b hb
  by_contra hbad
  have hfb : M < f b := lt_of_not_ge hbad
  have hsubb : Icc (0:ℝ) b ⊆ Ico 0 T := Icc_subset_Ico_right hb.2
  have hfcb : ContinuousOn f (Icc 0 b) := hc.mono hsubb
  -- A: the points of [0, b] at or below the level; its supremum a is the last one.
  set A : Set ℝ := {s | s ∈ Icc 0 b ∧ f s ≤ M} with hAdef
  have h0A : (0:ℝ) ∈ A := ⟨left_mem_Icc.mpr hb.1, h0⟩
  have hAne : A.Nonempty := ⟨0, h0A⟩
  have hAbdd : BddAbove A := ⟨b, fun s hs => hs.1.2⟩
  have hAclosed : IsClosed A := by
    have hAeq : A = Icc 0 b ∩ f ⁻¹' Iic M := by
      ext s
      simp only [hAdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Iic]
    rw [hAeq]
    exact hfcb.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set a := sSup A with hadef
  have haA : a ∈ A := hAclosed.csSup_mem hAne hAbdd
  have ha0 : 0 ≤ a := haA.1.1
  have hab : a ≤ b := haA.1.2
  have hfa : f a ≤ M := haA.2
  -- strictly above a (up to b) the function is above the level
  have habove : ∀ s ∈ Ioc a b, M < f s := by
    intro s hs
    by_contra hle
    have hsA : s ∈ A := ⟨⟨ha0.trans hs.1.le, hs.2⟩, le_of_not_gt hle⟩
    exact absurd (le_csSup hAbdd hsA) (not_le.mpr hs.1)
  -- L: an intermediate level, strictly between M and both M' and f b
  set L : ℝ := (M + min M' (f b)) / 2 with hLdef
  have hminM : M < min M' (f b) := lt_min hMM' hfb
  have hML : M < L := by rw [hLdef]; linarith
  have hLM' : L < M' := by
    have := min_le_left M' (f b); rw [hLdef]; linarith
  have hLfb : L < f b := by
    have := min_le_right M' (f b); rw [hLdef]; linarith
  -- B: the points of [a, b] at or above L; its infimum c is the first one.
  set B : Set ℝ := {s | s ∈ Icc a b ∧ L ≤ f s} with hBdef
  have hbB : b ∈ B := ⟨right_mem_Icc.mpr hab, hLfb.le⟩
  have hBne : B.Nonempty := ⟨b, hbB⟩
  have hBbdd : BddBelow B := ⟨a, fun s hs => hs.1.1⟩
  have hBclosed : IsClosed B := by
    have hBeq : B = Icc a b ∩ f ⁻¹' Ici L := by
      ext s
      simp only [hBdef, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ici]
    rw [hBeq]
    exact (hfcb.mono (Icc_subset_Icc_left ha0)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici
  set c := sInf B with hcdef
  have hcB : c ∈ B := hBclosed.csInf_mem hBne hBbdd
  have hac : a ≤ c := hcB.1.1
  have hcb : c ≤ b := hcB.1.2
  have hLc : L ≤ f c := hcB.2
  -- strictly below c (from a) the function is below L
  have hbelow : ∀ s ∈ Ico a c, f s < L := by
    intro s hs
    by_contra hge
    have hsB : s ∈ B := ⟨⟨hs.1, hs.2.le.trans hcb⟩, le_of_not_gt hge⟩
    exact absurd (csInf_le hBbdd hsB) (not_le.mpr hs.2)
  -- on (a, c) the strip condition holds, so the derivative is nonpositive
  have hsubc : Icc a c ⊆ Ico 0 T :=
    fun s hs => ⟨ha0.trans hs.1, lt_of_le_of_lt (hs.2.trans hcb) hb.2⟩
  have hsubc' : Ioo a c ⊆ Ioo 0 T :=
    fun s hs => ⟨lt_of_le_of_lt ha0 hs.1, lt_of_lt_of_le hs.2 (hcb.trans hb.2.le)⟩
  have hfc1 : f c ≤ f a :=
    le_of_deriv_nonpos hac (hc.mono hsubc) (hd.mono hsubc')
      (fun s hs => h' s (hsubc' hs)
        (habove s ⟨hs.1, hs.2.le.trans hcb⟩)
        (lt_trans (hbelow s ⟨hs.1.le, hs.2⟩) hLM'))
  linarith

/-- **F0, box forward invariance.**  Energy gated at `Es` and enstrophy gated
on the strip `Zs ≤ Z ≤ 2·Zs` (given `E ≤ Es`) keep the orbit inside the box
`{E ≤ Es, Z ≤ Zs}` for the whole lifespan.  Two applications of the barrier
lemma: energy first, then enstrophy on the strip using the energy bound;
`0 < Zs` makes the strip nonempty. -/
theorem forced_trap_forward_invariance {T Es Zs : ℝ} (hZs : 0 < Zs)
    {E Z : ℝ → ℝ}
    (hEc : ContinuousOn E (Ico 0 T)) (hZc : ContinuousOn Z (Ico 0 T))
    (hEd : DifferentiableOn ℝ E (Ioo 0 T)) (hZd : DifferentiableOn ℝ Z (Ioo 0 T))
    (hE' : ∀ t ∈ Ioo (0:ℝ) T, Es ≤ E t → deriv E t ≤ 0)
    (hZ' : ∀ t ∈ Ioo (0:ℝ) T, E t ≤ Es → Zs ≤ Z t → Z t ≤ 2 * Zs → deriv Z t ≤ 0)
    (h0E : E 0 ≤ Es) (h0Z : Z 0 ≤ Zs) :
    ∀ t ∈ Ico (0:ℝ) T, E t ≤ Es ∧ Z t ≤ Zs := by
  have hE : ∀ t ∈ Ico (0:ℝ) T, E t ≤ Es :=
    barrier_forward_invariance (M' := Es + 1) (by linarith) hEc hEd h0E
      (fun t ht h1 _ => hE' t ht h1.le)
  have hZ : ∀ t ∈ Ico (0:ℝ) T, Z t ≤ Zs :=
    barrier_forward_invariance (M' := 2 * Zs) (by linarith) hZc hZd h0Z
      (fun t ht h1 h2 => hZ' t ht (hE t ⟨ht.1.le, ht.2⟩) h1.le h2.le)
  exact fun t ht => ⟨hE t ht, hZ t ht⟩

/-- **F0, forced conditional trap (box form).**  There is a uniform constant
`κ` (witness `8·K`, `K` the master-inequality constant) such that under the
forced energy and enstrophy differential inequalities, with the force's L²
size bounded by `G`, data inside a box obeying
`κ·Es·Zs ≤ ν⁴`, `G ≤ ν²·Es`, `8·G ≤ ν²·Zs` stays inside that box for the
whole lifespan.  Only `en (g t)` enters.  At `g = 0` this is NOT a
strengthening of `conditional_trap` (see the file header). -/
theorem forced_conditional_trap :
    ∃ κ, 0 < κ ∧ ∀ {T ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c g : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t ∈ Ico (0:ℝ) T, c t 0 = 0) →
      (∀ t ∈ Ico (0:ℝ) T, Summable fun k => ‖freq k‖ ^ 4 * ‖c t k‖ ^ 2) →
      (∀ t ∈ Ico (0:ℝ) T, en (g t) ≤ G) →
      ContinuousOn (fun t => en (c t)) (Ico 0 T) →
      ContinuousOn (fun t => ens (c t)) (Ico 0 T) →
      DifferentiableOn ℝ (fun t => en (c t)) (Ioo 0 T) →
      DifferentiableOn ℝ (fun t => ens (c t)) (Ioo 0 T) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => en (c s)) t ≤
        -(2 * ν) * ens (c t) + 2 * Real.sqrt (en (c t)) * Real.sqrt (en (g t))) →
      (∀ t ∈ Ioo (0:ℝ) T, deriv (fun s => ens (c s)) t ≤
        -(2 * ν) * dis (c t) +
          2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
            (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) +
          2 * Real.sqrt (dis (c t)) * Real.sqrt (en (g t))) →
      en (c 0) ≤ Es → ens (c 0) ≤ Zs →
      ∀ t ∈ Ico (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs := by
  obtain ⟨K, hK, hmaster⟩ := master_inequality (V := Vel)
  refine ⟨8 * K, by positivity, ?_⟩
  intro T ν Es Zs G hν hEs hZs hκ hG hG8 c g hmean hDsum hg hEc hZc hEd hZd hEbal hZbal h0E h0Z
  -- energy gate: at or above Es the energy cannot rise
  have hE' : ∀ t ∈ Ioo (0:ℝ) T, Es ≤ en (c t) → deriv (fun s => en (c s)) t ≤ 0 := by
    intro t ht hEs'
    have htI : t ∈ Ico (0:ℝ) T := ⟨ht.1.le, ht.2⟩
    have hm := hmean t htI
    have hs := hDsum t htI
    have hEZ : en (c t) ≤ ens (c t) := en_le_ens hm (summable_ens hm hs)
    have hEnn : 0 ≤ en (c t) := tsum_nonneg fun k => sq_nonneg _
    have hgnn : 0 ≤ en (g t) := tsum_nonneg fun k => sq_nonneg _
    have hgE : en (g t) ≤ ν ^ 2 * en (c t) :=
      (hg t htI).trans (hG.trans (mul_le_mul_of_nonneg_left hEs' (sq_nonneg ν)))
    have hsq : Real.sqrt (en (g t)) ≤ ν * Real.sqrt (en (c t)) := by
      have h1 := Real.sqrt_le_sqrt hgE
      rwa [Real.sqrt_mul (sq_nonneg ν), Real.sqrt_sq hν.le] at h1
    have hsE : 0 ≤ Real.sqrt (en (c t)) := Real.sqrt_nonneg _
    have hprod : Real.sqrt (en (c t)) * Real.sqrt (en (g t)) ≤ ν * en (c t) := by
      calc Real.sqrt (en (c t)) * Real.sqrt (en (g t))
          ≤ Real.sqrt (en (c t)) * (ν * Real.sqrt (en (c t))) :=
            mul_le_mul_of_nonneg_left hsq hsE
        _ = ν * (Real.sqrt (en (c t)) * Real.sqrt (en (c t))) := by ring
        _ = ν * en (c t) := by rw [Real.mul_self_sqrt hEnn]
    have hb := hEbal t ht
    nlinarith [mul_le_mul_of_nonneg_left hEZ hν.le]
  -- enstrophy gate: inside the box strip the enstrophy cannot rise
  have hZ' : ∀ t ∈ Ioo (0:ℝ) T, en (c t) ≤ Es → Zs ≤ ens (c t) → ens (c t) ≤ 2 * Zs →
      deriv (fun s => ens (c s)) t ≤ 0 := by
    intro t ht hEle hZge hZle
    have htI : t ∈ Ico (0:ℝ) T := ⟨ht.1.le, ht.2⟩
    have hm := hmean t htI
    have hs := hDsum t htI
    have hW2 := ens_sq_le_en_mul_dis hm hs
    have hZD : ens (c t) ≤ dis (c t) := ens_le_dis hm hs
    have hM := hmaster (c t) hm hs ν hν
    have hDnn : 0 ≤ dis (c t) :=
      tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
    have hEnn : 0 ≤ en (c t) := tsum_nonneg fun k => sq_nonneg _
    have hZnn : 0 ≤ ens (c t) :=
      tsum_nonneg fun k => mul_nonneg (by positivity) (sq_nonneg _)
    have hgnn : 0 ≤ en (g t) := tsum_nonneg fun k => sq_nonneg _
    set D := dis (c t) with hDdef
    set Z := ens (c t) with hZdef
    set E := en (c t) with hEdef
    set gt := en (g t) with hgdef
    -- Young: 2 √D √g ≤ (ν/2) D + (2/ν) g
    have hyoung : 2 * Real.sqrt D * Real.sqrt gt ≤ ν / 2 * D + 2 / ν * gt := by
      have hsD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDnn
      have hsg : Real.sqrt gt ^ 2 = gt := Real.sq_sqrt hgnn
      have hrhs : ν * (ν / 2 * D + 2 / ν * gt) =
          ν ^ 2 / 2 * Real.sqrt D ^ 2 + 2 * Real.sqrt gt ^ 2 := by
        rw [hsD, hsg]
        field_simp
      have hkey : ν * (2 * Real.sqrt D * Real.sqrt gt) ≤
          ν ^ 2 / 2 * Real.sqrt D ^ 2 + 2 * Real.sqrt gt ^ 2 := by
        nlinarith [sq_nonneg (ν * Real.sqrt D - 2 * Real.sqrt gt)]
      rw [← hrhs] at hkey
      exact le_of_mul_le_mul_left hkey hν
    -- force budget: (2/ν) g ≤ (ν/4) Zs ≤ (ν/4) Z ≤ (ν/4) D
    have hforce : 2 / ν * gt ≤ ν / 4 * D := by
      have h1 : gt ≤ G := hg t htI
      have h2 : 8 * gt ≤ ν ^ 2 * D := by
        have : ν ^ 2 * Zs ≤ ν ^ 2 * D :=
          mul_le_mul_of_nonneg_left (hZge.trans hZD) (sq_nonneg ν)
        linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hν]
      nlinarith
    -- cubic term: (K/ν³) Z³ ≤ (ν/4) D from Z² ≤ E D and the box thresholds
    have hcubic : K / ν ^ 3 * Z ^ 3 ≤ ν / 4 * D := by
      have h1 : Z ^ 3 ≤ Z * (E * D) := by
        have : Z ^ 3 = Z * Z ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hW2 hZnn
      have h2 : Z * (E * D) ≤ (2 * Zs) * (Es * D) := by
        apply mul_le_mul hZle (mul_le_mul_of_nonneg_right hEle hDnn)
          (mul_nonneg hEnn hDnn) (by linarith)
      have h3 : K * Z ^ 3 ≤ (8 * K * Es * Zs) * D / 4 := by
        have : K * Z ^ 3 ≤ K * ((2 * Zs) * (Es * D)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hK.le
        linarith
      have h4 : (8 * K * Es * Zs) * D / 4 ≤ ν ^ 4 * D / 4 := by
        have := mul_le_mul_of_nonneg_right hκ hDnn
        linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < ν ^ 3)]
      nlinarith
    have hb := hZbal t ht
    linarith
  exact forced_trap_forward_invariance hZs hEc hZc hEd hZd hE' hZ' h0E h0Z

/-- **F0, thresholds inhabited.**  For every `κ, ν > 0` the three box
thresholds are jointly satisfiable with a strictly positive force budget:
witness `Es := ν²`, `Zs := ν²/κ`, `G := ν⁴/(8κ+8)`. -/
theorem forced_thresholds_inhabited {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ Es Zs G : ℝ, 0 < G ∧ 0 ≤ Es ∧ 0 < Zs ∧
      κ * Es * Zs ≤ ν ^ 4 ∧ G ≤ ν ^ 2 * Es ∧ 8 * G ≤ ν ^ 2 * Zs := by
  refine ⟨ν ^ 2, ν ^ 2 / κ, ν ^ 4 / (8 * κ + 8), by positivity, by positivity,
    by positivity, ?_, ?_, ?_⟩
  · rw [mul_div_assoc', div_le_iff₀ hκ]
    ring_nf
    exact le_refl _
  · rw [div_le_iff₀ (by positivity)]
    have : (0:ℝ) ≤ ν ^ 4 := by positivity
    nlinarith
  · have e1 : 8 * (ν ^ 4 / (8 * κ + 8)) = ν ^ 4 / (κ + 1) := by
      field_simp
    have e2 : ν ^ 2 * (ν ^ 2 / κ) = ν ^ 4 / κ := by
      field_simp
    rw [e1, e2, div_le_div_iff₀ (by positivity) hκ]
    nlinarith [pow_nonneg hν.le 4]

end TheoremB
