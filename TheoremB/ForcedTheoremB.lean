/-
  TheoremB/ForcedTheoremB.lean
  Tier 8a, wave F3 of the Theorem B campaign (9 Sep 2026).

  THEOREM B UNDER A SMALL FORCE: the box-exhaustion limit of the forced
  Galerkin chain (waves F0-F2), as pure siblings of TheoremBGlobal.lean and
  FullUnique.lean.  No frozen statement is edited.  The forced right-hand
  side is spelled INLINE throughout,

      (-(nu * ‖freq k‖^2)) • c t k + lerayProj k (convFull (c t) k) + g t k

  (Galerkin layer: `convGal`, force truncated to the box), so that at g = 0
  a `simpa` converts each forced equation clause into the frozen unforced one
  (`probe_frozen_flow_inhabits_forced_clauses`, this file).

  What the file delivers:

  * `flow_mode_mem_modeSet_forced`: the mode bounds feeding Arzela-Ascoli
    with a bounded force.  A per-mode sup bound `Gs` on the force adds to the
    Lipschitz constant of every mode curve (`galRHS_norm_le` + `norm_add_le`);
    the curve lives in the candidate set `modeSet T √E (… + Gs)` of
    ModeExtraction.lean.

  * `integral_equation_limit_forced`: the limit passage through each mode
    equation WITH the force.  The prelimit force is `truncate (S n) (g t) k`,
    which is EVENTUALLY equal to `g t k` on every nonzero mode (the boxes
    exhaust the lattice), so the force term passes through the limit
    trivially; the convection passes by the house epsilon/3 tail method
    (`tendsto_convFull_of_modes`, LimitPassage.lean) exactly as in the
    unforced `integral_equation_limit`; the dominated-convergence majorant
    gains the constant `Gs`.  Per-mode CONTINUITY of the force is what makes
    the integrand continuous (so the interval integral is honest, not the
    junk value of a non-integrable integrand).

  * `galerkin_family_forced`: the forced Galerkin exhaustion family — for
    every box radius `R` and horizon `T`, a forced Galerkin flow on `boxS R`
    from the truncated datum, driven by the truncated force, trapped in the
    box `(Es, Zs)` uniformly in `R` (the thresholds are hypotheses, and
    truncation only lowers energy and enstrophy of the datum and of the
    force).  THE composition probe of wave F2 against a real producer.

  * `theorem_B_forced`: existence on every horizon with the box trap —
    from mean-zero, real, divergence-free, finite-energy, finite-enstrophy
    data inside a box `(Es, Zs)` with `κ·Es·Zs ≤ ν⁴`, under a mean-zero,
    real, divergence-free, per-mode-continuous force with SUMMABLE energy
    series bounded by `G ≤ ν²·Es`, `8·G ≤ ν²·Zs`: on every `[0, T]` a
    coefficient flow that starts at the datum, is real and divergence-free,
    has honestly summable energy and enstrophy series (the summability of
    the FORCE's energy series is a hypothesis: without it `en (g t)` is a
    tsum that a non-ℓ² force makes vanish, and `en (g t) ≤ G` would be met
    for free), is mode-continuous, satisfies the full forced integral
    equation on the closed window and the forced mode ODE at every interior
    time, and never leaves the box.  The force hypotheses are on `Ici 0`
    (physically honest); the Galerkin layer takes a force on all of `ℝ`, and
    the bridge is the clamp `g (max t 0)`.

  * `theorem_B_unique_forced`: uniqueness in the enstrophy-bounded class for
    the FORCED integral equation — the finite-section energy method of
    `theorem_B_unique` replayed; the force cancels in the difference of two
    flows, so the only change is that the zero mode of each flow is the same
    integral of the force rather than a constant.

  * `ns_full_global_flow_forced`: the eternal forced flow — ONE flow on the
    half line serving every horizon, spliced from the `theorem_B_forced`
    witnesses along integer segments, seamless by `theorem_B_unique_forced`.
    It exports the clauses (mode continuity, summability, the integral
    equation) that re-admit each restriction to the uniqueness class.

  CAVEAT (binding for every downstream claim): at g = 0 the forced chain is
  NOT a strengthening of the unforced one.  The trap constant is κ = 8·K
  (not K), the smallness is non-strict, and the box `(Es, Zs)` is a
  hypothesis rather than the energy/enstrophy of the datum.  The forced
  results must never be described as implying or improving the unforced
  ones; the only compiled direction is frozen ⇒ forced clause list
  (`probe_frozen_flow_inhabits_forced_clauses`).  The `κ` of each theorem is
  its own compiled existential: `κ_forced = 8·K` is of explicit form up to
  the lattice-kernel sum `C_K`, exported as a compiled existential; the force
  thresholds `G ≤ ν²·Es`, `8·G ≤ ν²·Zs` are literal expressions.

  Nothing here is new mathematics: this is the classical forced small-data
  theory (small Grashof number) carried through a Galerkin approximation,
  Arzela-Ascoli, and dominated convergence.  Textbook sources, named as
  references and NOT verified against by this file (theorem numbers
  unverified): Temam, Navier-Stokes Equations: Theory and Numerical
  Analysis, Ch. III; Robinson-Rodrigo-Sadowski, The Three-Dimensional
  Navier-Stokes Equations, Ch. 6-7; Constantin-Foias, Navier-Stokes
  Equations, Ch. 10; Foias-Manley-Rosa-Temam, Navier-Stokes Equations and
  Turbulence, Ch. II.

  CONTRACT: the theorem STATEMENTS marked **F3** are frozen (rung10 Tier-8
  blueprint, section 4a, wave F3); the two marked **F4 (delivered early)**
  are frozen in section 4a, wave F4, and are transcribed byte-for-byte here
  because the eternal flow needs the uniqueness.  If a statement cannot be
  proved as written, do not silently repair it: keep it, add a sibling, and
  report.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.FullUnique
import TheoremB.TheoremBGlobal
import TheoremB.FlowBounds
import TheoremB.ForcedGalerkinFlow

namespace TheoremB

open Set

/-! ## Mode bounds with a bounded force -/

/-- **F3, mode curves of a forced Galerkin flow live in the Arzela-Ascoli
candidate set.**  The per-mode sup bound `Gs` of the force adds to the
Lipschitz constant of `flow_mode_mem_modeSet`. -/
theorem flow_mode_mem_modeSet_forced {ν E Z Gs T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E)
    (hZ0 : 0 ≤ Z) (hGs : 0 ≤ Gs)
    {S : Finset (Fin 3 → ℤ)} {c g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ (t : ℝ) k, k ∉ S → c t k = 0)
    (hODE : ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k) t)
    (hen : ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ E)
    (hens : ∀ t ∈ Icc (0:ℝ) T, ens (c t) ≤ Z)
    (hg : ∀ t ∈ Icc (0:ℝ) T, ∀ k, ‖g t k‖ ≤ Gs) (k : Fin 3 → ℤ) :
    ∃ f : C(Icc (0:ℝ) T, Vel), (∀ t : Icc (0:ℝ) T, f t = c t.val k) ∧
      f ∈ modeSet T (Real.sqrt E) (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
        2 * (Real.sqrt E * Real.sqrt Z) + Gs)) := by
  have _hGs := hGs
  have hlip : LipschitzOnWith (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
      2 * (Real.sqrt E * Real.sqrt Z) + Gs)) (fun t => c t k) (Icc (0:ℝ) T) := by
    refine (convex_Icc (0:ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun t => (-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) +
        g t k)
      (fun t ht => (hODE t ht k).hasDerivWithinAt) (fun t ht => ?_)
    rw [← norm_toNNReal]
    refine Real.toNNReal_mono ?_
    calc ‖(-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k) + g t k‖
        ≤ ‖(-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)‖ + ‖g t k‖ :=
          norm_add_le _ _
      _ ≤ ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z) + Gs :=
          add_le_add (galRHS_norm_le hν hE0 hZ0 (hsupp t) (hen t ht) (hens t ht) k)
            (hg t ht k)
  have hlipR : LipschitzWith (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt E +
      2 * (Real.sqrt E * Real.sqrt Z) + Gs))
      ((Icc (0:ℝ) T).restrict fun t => c t k) :=
    lipschitzOnWith_iff_restrict.1 hlip
  refine ⟨⟨fun t => c t.val k, hlipR.continuous⟩, fun t => rfl, hlipR, fun t => ?_⟩
  rw [mem_closedBall_zero_iff]
  show ‖c t.val k‖ ≤ Real.sqrt E
  exact (coeff_le_sqrt_en (hsupp t.val) k).trans (Real.sqrt_le_sqrt (hen t.val t.2))

/-! ## The limit passage through each mode equation, with the force -/

/-- **F3, the forced limit passage on a fixed nonzero mode.**  A uniform
limit of budgeted forced Galerkin flows (force truncated to the box)
satisfies the full-convection forced integral equation on `[0, T]`.  The
force term is eventually box-independent on every nonzero mode, so it passes
through the limit as a constant; the convection passes by the epsilon/3
tail method; the majorant of dominated convergence gains `Gs`. -/
theorem integral_equation_limit_forced {ν E Z Gs T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E)
    (hZ0 : 0 ≤ Z) (hGs : 0 ≤ Gs) (hT : 0 ≤ T)
    {S : ℕ → Finset (Fin 3 → ℤ)} {F : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    {u g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ n (t : ℝ) k, k ∉ S n → F n t k = 0)
    (hODE : ∀ n, ∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => F n s k)
      ((-(ν * ‖freq k‖ ^ 2)) • F n t k + lerayProj k (convGal (S n) (F n t) k) +
        truncate (S n) (g t) k) t)
    (hEn : ∀ n, ∀ t ∈ Icc (0:ℝ) T, en (F n t) ≤ E)
    (hZn : ∀ n, ∀ t ∈ Icc (0:ℝ) T, ens (F n t) ≤ Z)
    (hbox : ∀ k : Fin 3 → ℤ, k ≠ 0 → ∀ᶠ n in Filter.atTop, k ∈ S n)
    (hu : ∀ l, TendstoUniformlyOn (fun n t => F n t l) (fun t => u t l)
      Filter.atTop (Icc (0:ℝ) T))
    (hgc : ∀ k, ContinuousOn (fun s => g s k) (Icc (0:ℝ) T))
    (hgb : ∀ t ∈ Icc (0:ℝ) T, ∀ k, ‖g t k‖ ≤ Gs) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k : Fin 3 → ℤ, k ≠ 0 →
      u t k = u 0 k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • u s k + lerayProj k (convFull (u s) k) + g s k) := by
  have _hGs := hGs
  intro t ht k hk
  -- every mode curve of every prelimit flow is continuous on the window
  have hcontMode : ∀ n l, ContinuousOn (fun s => F n s l) (Icc (0:ℝ) T) := by
    intro n l s hs
    exact (hODE n s hs l).continuousAt.continuousWithinAt
  -- the truncated force is continuous on the window, mode by mode
  have hcontTr : ∀ n, ContinuousOn (fun s => truncate (S n) (g s) k) (Icc (0:ℝ) T) := by
    intro n
    by_cases hkS : k ∈ S n
    · have e : (fun s => truncate (S n) (g s) k) = fun s => g s k :=
        funext fun s => truncate_eq_of_mem _ _ hkS
      rw [e]
      exact hgc k
    · have e : (fun s => truncate (S n) (g s) k) = fun _ => (0 : Vel) :=
        funext fun s => truncate_supp _ _ k hkS
      rw [e]
      exact continuousOn_const
  -- the prelimit right-hand sides are continuous on the window
  have hcontRHS : ∀ n, ContinuousOn
      (fun s => (-(ν * ‖freq k‖ ^ 2)) • F n s k
        + lerayProj k (convGal (S n) (F n s) k) + truncate (S n) (g s) k) (Icc (0:ℝ) T) := by
    intro n
    have h2 : ContinuousOn (fun s => lerayProj k (convGal (S n) (F n s) k))
        (Icc (0:ℝ) T) :=
      (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convGal (fun l => hcontMode n l) k)
    exact (((hcontMode n k).const_smul _).add h2).add (hcontTr n)
  -- prelimit integral equations at the fixed time t
  have hpre : ∀ n, F n t k = F n 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k) +
        truncate (S n) (g s) k) := by
    intro n
    exact integral_eq_of_hasDerivAt_Icc hT (fun s hs => hODE n s hs k) (hcontRHS n) t ht
  -- the integration interval sits inside the window
  have hsubset : uIoc (0:ℝ) t ⊆ Icc (0:ℝ) T := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
  -- the uniform majorant, with the force sup bound
  have hbound : ∀ n, ∀ s ∈ uIoc (0:ℝ) t,
      ‖(-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k) +
        truncate (S n) (g s) k‖ ≤
      ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z) + Gs := by
    intro n s hs
    have hsI : s ∈ Icc (0:ℝ) T := hsubset hs
    calc ‖(-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k) +
          truncate (S n) (g s) k‖
        ≤ ‖(-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k)‖ +
          ‖truncate (S n) (g s) k‖ := norm_add_le _ _
      _ ≤ ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z) + Gs :=
          add_le_add
            (galRHS_norm_le hν hE0 hZ0 (hsupp n s) (hEn n s hsI) (hZn n s hsI) k)
            ((truncate_norm_le _ _ _).trans (hgb s hsI k))
  -- dominated convergence of the prelimit integrals to the full-convection one
  have hlim_int : Filter.Tendsto
      (fun n => ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k) +
          truncate (S n) (g s) k))
      Filter.atTop
      (nhds (∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • u s k + lerayProj k (convFull (u s) k) + g s k))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z) + Gs)
      (Filter.Eventually.of_forall fun n =>
        ((hcontRHS n).mono hsubset).aestronglyMeasurable measurableSet_uIoc)
      (Filter.Eventually.of_forall fun n =>
        Filter.Eventually.of_forall fun s hs => hbound n s hs)
      _root_.intervalIntegrable_const
      (Filter.Eventually.of_forall fun s hs => ?_)
    -- pointwise limit of the integrands at s ∈ uIoc 0 t
    have hsIcc : s ∈ Icc (0:ℝ) T := hsubset hs
    have hpt : ∀ l, Filter.Tendsto (fun n => F n s l) Filter.atTop (nhds (u s l)) :=
      fun l => (hu l).tendsto_at hsIcc
    have hEnF : ∀ n (Fs : Finset (Fin 3 → ℤ)), ∑ l ∈ Fs, ‖F n s l‖ ^ 2 ≤ E :=
      fun n Fs => (sum_sq_le_en (hsupp n s) Fs).trans (hEn n s hsIcc)
    have hZnF : ∀ n (Fs : Finset (Fin 3 → ℤ)),
        ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖F n s l‖ ^ 2 ≤ Z :=
      fun n Fs => (sum_wsq_le_ens (hsupp n s) Fs).trans (hZn n s hsIcc)
    have hconv : Filter.Tendsto (fun n => lerayProj k (convFull (F n s) k))
        Filter.atTop (nhds (lerayProj k (convFull (u s) k))) :=
      ((lerayProj_continuous k).tendsto _).comp
        (tendsto_convFull_of_modes hE0 hZ0 hEnF hZnF hpt k)
    have heq : (fun n => lerayProj k (convFull (F n s) k)) =ᶠ[Filter.atTop]
        (fun n => lerayProj k (convGal (S n) (F n s) k)) :=
      (hbox k hk).mono fun n hmem =>
        congrArg (lerayProj k) (convFull_eq_convGal (hsupp n s) hmem)
    -- the force term is eventually the untruncated one
    have hforce : (fun _ : ℕ => g s k) =ᶠ[Filter.atTop]
        (fun n => truncate (S n) (g s) k) :=
      (hbox k hk).mono fun n hmem => (truncate_eq_of_mem _ _ hmem).symm
    exact (((hpt k).const_smul _).add (hconv.congr' heq)).add
      ((tendsto_const_nhds (x := g s k)).congr' hforce)
  -- take the limit of the prelimit integral equations
  have hL1 : Filter.Tendsto (fun n => F n t k) Filter.atTop (nhds (u t k)) :=
    (hu k).tendsto_at ht
  have hL0 : Filter.Tendsto (fun n => F n 0 k) Filter.atTop (nhds (u 0 k)) :=
    (hu k).tendsto_at (Set.mem_Icc.mpr ⟨le_refl (0:ℝ), hT⟩)
  have hL2 : Filter.Tendsto (fun n => F n t k) Filter.atTop
      (nhds (u 0 k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • u s k + lerayProj k (convFull (u s) k) + g s k))) :=
    (hL0.add hlim_int).congr fun n => (hpre n).symm
  exact tendsto_nhds_unique hL1 hL2

/-! ## The forced Galerkin exhaustion family -/

/-- **F3, the forced Galerkin exhaustion family.**  For every box radius `R`
and horizon `T`, a forced Galerkin flow on `boxS R` starting from the
truncated datum and driven by the truncated force, trapped in the box
`(Es, Zs)` uniformly in `R`.  The composition of wave F2's
`ns_galerkin_global_wellposed_forced` with a real producer: truncation
preserves reality and divergence-freeness and only lowers the energy of the
datum and of the force, so the thresholds are inherited. -/
theorem galerkin_family_forced :
    ∃ κ, 0 < κ ∧ ∀ {ν Es Zs G : ℝ}, 0 < ν → 0 ≤ Es → 0 < Zs →
      κ * Es * Zs ≤ ν ^ 4 → G ≤ ν ^ 2 * Es → 8 * G ≤ ν ^ 2 * Zs →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel} {g : ℝ → (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      RealField c₀ → DivFree c₀ → en c₀ ≤ Es → ens c₀ ≤ Zs →
      (∀ t, RealField (g t)) → (∀ t, DivFree (g t)) →
      (∀ t, Summable (fun l => ‖g t l‖ ^ 2)) → (∀ t, en (g t) ≤ G) →
      (∀ k, Continuous fun t => g t k) →
      ∀ (R : ℕ) (T : ℝ), ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = truncate (boxS R) c₀ ∧
        (∀ (t : ℝ) k, k ∉ boxS R → c t k = 0) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k +
            lerayProj k (convGal (boxS R) (c t) k) + truncate (boxS R) (g t) k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs) := by
  obtain ⟨κ, hκ, hwp⟩ := ns_galerkin_global_wellposed_forced
  refine ⟨κ, hκ, ?_⟩
  intro ν Es Zs G hν hEs hZs hκE hGE hGZ c₀ g hE hZ hreal hdiv h0E h0Z hgreal hgdiv hgsum
    hgen hgc R T
  -- per-mode continuity of the truncated force
  have hgc' : ∀ k, Continuous fun t => truncate (boxS R) (g t) k := by
    intro k
    by_cases hk : k ∈ boxS R
    · have e : (fun t => truncate (boxS R) (g t) k) = fun t => g t k :=
        funext fun t => truncate_eq_of_mem _ _ hk
      rw [e]
      exact hgc k
    · have e : (fun t => truncate (boxS R) (g t) k) = fun _ => (0 : Vel) :=
        funext fun t => truncate_supp _ _ k hk
      rw [e]
      exact continuous_const
  obtain ⟨c, hc0, hcs, hcODE, hctrap, _⟩ :=
    hwp hν hEs hZs hκE hGE hGZ (boxS_zero_not_mem R) (boxS_symm R)
      (g := fun t => truncate (boxS R) (g t))
      (fun t k hk => truncate_supp _ _ k hk)
      (fun t => realField_truncate (hgreal t) (boxS_symm R))
      (fun t => divFree_truncate (hgdiv t) _)
      (fun t => (en_truncate_le (hgsum t) _).trans (hgen t))
      hgc'
      (truncate_supp (boxS R) c₀)
      (realField_truncate hreal (boxS_symm R))
      (divFree_truncate hdiv (boxS R))
      ((en_truncate_le hE _).trans h0E)
      ((ens_truncate_le hZ _).trans h0Z) T
  exact ⟨c, hc0, hcs, hcODE, hctrap⟩

/-! ## Theorem B under a small force -/

/-- **F3, THEOREM B UNDER A SMALL FORCE — existence on every finite horizon
with the box trap.**  There is a constant `κ > 0` (of explicit form up to
the lattice-kernel sum, exported as a compiled existential) such that for
every viscosity `ν > 0`, every box `(Es, Zs)` with `κ·Es·Zs ≤ ν⁴`, every
force budget `G` with `G ≤ ν²·Es` and `8·G ≤ ν²·Zs`, every mean-zero, real,
divergence-free datum with summable energy and enstrophy series inside the
box, and every mean-zero, real, divergence-free, per-mode-continuous force on
`[0, ∞)` whose energy series is SUMMABLE at every time and bounded by `G`:
on every horizon `[0, T]` there is a coefficient flow which starts at the
datum, is real and divergence-free throughout, has honestly summable energy
and enstrophy series at every time of the window, is mode-continuous on the
closed window, satisfies the FULL forced Navier-Stokes integral equation at
every time of the closed window and the forced differential equation at
every interior time, and stays inside the box.  PER-HORIZON: the witness may
depend on `T`.  The summability certificate on the force is load-bearing:
`en (g t)` is a `tsum`, and a non-ℓ² force would meet any budget with the
junk value `0`.  At `g = 0` this is NOT a strengthening of `theorem_B_cont`
(`κ` here is `8·K`, the smallness is non-strict, the box is a hypothesis). -/
theorem theorem_B_forced :
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
      ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs) := by
  obtain ⟨κ, hκ, hfam⟩ := galerkin_family_forced
  refine ⟨κ, hκ, ?_⟩
  intro ν Es Zs G hν hEs hZs hκE hGE hGZ c₀ g hE hZ hmean hreal hdiv h0E h0Z
    hgmean hgreal hgdiv hgsum hgen hgc T hT
  -- the force, extended to all of ℝ by clamping the time at 0
  set gt : ℝ → (Fin 3 → ℤ) → Vel := fun t => g (max t 0) with hgtdef
  have hmax : ∀ t : ℝ, max t 0 ∈ Ici (0:ℝ) := fun t => le_max_right t 0
  have hgt_eq : ∀ t ∈ Ici (0:ℝ), gt t = g t := by
    intro t ht
    show g (max t 0) = g t
    rw [max_eq_left ht]
  have hgtreal : ∀ t, RealField (gt t) := fun t => hgreal _ (hmax t)
  have hgtdiv : ∀ t, DivFree (gt t) := fun t => hgdiv _ (hmax t)
  have hgtsum : ∀ t, Summable (fun l => ‖gt t l‖ ^ 2) := fun t => hgsum _ (hmax t)
  have hgten : ∀ t, en (gt t) ≤ G := fun t => hgen _ (hmax t)
  have hgtc : ∀ k, Continuous fun t => gt t k := fun k =>
    (hgc k).comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 0)
  -- the per-mode sup bound of the force from its summable energy series
  have hgtb : ∀ (t : ℝ) (k : Fin 3 → ℤ), ‖gt t k‖ ≤ Real.sqrt G := by
    intro t k
    have h1 : ‖gt t k‖ ^ 2 ≤ en (gt t) := by
      have := (hgtsum t).le_tsum k (fun j _ => sq_nonneg _)
      simpa [en] using this
    calc ‖gt t k‖ = Real.sqrt (‖gt t k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt G := Real.sqrt_le_sqrt (h1.trans (hgten t))
  have hsqG : 0 ≤ Real.sqrt G := Real.sqrt_nonneg G
  -- the exhaustion family on this horizon
  have hfamI : ∀ R : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = truncate (boxS R) c₀ ∧
      (∀ (t : ℝ) k, k ∉ boxS R → c t k = 0) ∧
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k +
          lerayProj k (convGal (boxS R) (c t) k) + truncate (boxS R) (gt t) k) t) ∧
      (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs) :=
    fun R => hfam hν hEs hZs hκE hGE hGZ hE hZ hreal hdiv h0E h0Z hgtreal hgtdiv hgtsum
      hgten hgtc R T
  choose F hF0 hFs hFODE hFtrap using hfamI
  -- every mode curve lives in the Arzela-Ascoli candidate set
  have hmm : ∀ (R : ℕ) (k : Fin 3 → ℤ),
      ∃ f : C(Icc (0:ℝ) T, Vel), (∀ t : Icc (0:ℝ) T, f t = F R t.val k) ∧
        f ∈ modeSet T (Real.sqrt Es)
          (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt Es +
            2 * (Real.sqrt Es * Real.sqrt Zs) + Real.sqrt G)) :=
    fun R k => flow_mode_mem_modeSet_forced hν.le hEs hZs.le hsqG
      (g := fun t => truncate (boxS R) (gt t)) (hFs R) (hFODE R)
      (fun t ht => (hFtrap R t ht).1) (fun t ht => (hFtrap R t ht).2)
      (fun t _ k => (truncate_norm_le _ _ _).trans (hgtb t k)) k
  choose u hueq humem using hmm
  -- ONE subsequence for all modes
  obtain ⟨f, hfmem, φ, hφ, hconv⟩ := mode_extraction T (Real.sqrt Es)
    (fun k => Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt Es +
      2 * (Real.sqrt Es * Real.sqrt Zs) + Real.sqrt G)) u (fun R k => humem R k)
  -- the limit flow, extended to all of ℝ by clamping
  set c : ℝ → (Fin 3 → ℤ) → Vel :=
    fun t k => Set.IccExtend hT (⇑(f k)) t with hcdef
  have hc_mem : ∀ (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (k : Fin 3 → ℤ),
      c t k = f k ⟨t, ht⟩ := fun t ht k => Set.IccExtend_of_mem hT (⇑(f k)) ht
  -- mode-wise uniform convergence along the subsequence
  have hu : ∀ k, TendstoUniformlyOn (fun n t => F (φ n) t k) (fun t => c t k)
      Filter.atTop (Icc (0:ℝ) T) := by
    intro k
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have h1 := modeTendstoUniformly (hconv k)
    have e1 : (fun n (t : ↥(Icc (0:ℝ) T)) => F (φ n) t.val k) =
        fun n (t : ↥(Icc (0:ℝ) T)) => u (φ n) k t :=
      funext fun n => funext fun t => (hueq (φ n) k t).symm
    have e2 : ((fun t => c t k) ∘ (Subtype.val : ↥(Icc (0:ℝ) T) → ℝ)) = ⇑(f k) := by
      funext t
      show c t.val k = f k t
      rw [hc_mem t.val t.2 k]
    show TendstoUniformly (fun n (t : ↥(Icc (0:ℝ) T)) => F (φ n) t.val k) _ _
    rw [e1, e2]
    exact h1
  have hpt : ∀ t ∈ Icc (0:ℝ) T, ∀ k,
      Filter.Tendsto (fun n => F (φ n) t k) Filter.atTop (nhds (c t k)) :=
    fun t ht k => (hu k).tendsto_at ht
  -- the zero mode is identically zero
  have hczero : ∀ s : ℝ, c s 0 = 0 := by
    intro s
    have hx : ∀ x : ↥(Icc (0:ℝ) T), f 0 x = 0 := by
      intro x
      have h1 := (modeTendstoUniformly (hconv 0)).tendsto_at x
      have h2 : (fun n => u (φ n) 0 x) = fun _ => (0 : Vel) := by
        funext n
        rw [hueq (φ n) 0 x, hFs (φ n) x.val 0 (boxS_zero_not_mem (φ n))]
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    show Set.IccExtend hT (⇑(f 0)) s = 0
    exact hx _
  -- the whole flow factors through the clamp
  have hclamp : ∀ s : ℝ, c s = c (Set.projIcc 0 T hT s).val := by
    intro s
    funext k
    show Set.IccExtend hT (⇑(f k)) s = c (Set.projIcc 0 T hT s).val k
    rw [hc_mem _ (Set.projIcc 0 T hT s).2 k]
    rfl
  -- initial value
  have hc0 : c 0 = c₀ := by
    funext k
    by_cases hk0 : k = (0 : Fin 3 → ℤ)
    · rw [hk0, hczero 0, hmean]
    · have h1 := hpt 0 ⟨le_refl 0, hT⟩ k
      obtain ⟨R₀, hR₀⟩ := exists_boxS k hk0
      have h2 : ∀ᶠ n in Filter.atTop, F (φ n) 0 k = c₀ k := by
        refine Filter.eventually_atTop.mpr ⟨R₀, fun n hn => ?_⟩
        have hmem : k ∈ boxS (φ n) := hR₀ (φ n) (hn.trans hφ.le_apply)
        rw [hF0 (φ n)]
        exact truncate_eq_of_mem _ _ hmem
      have h3 : Filter.Tendsto (fun n => F (φ n) 0 k) Filter.atTop (nhds (c₀ k)) :=
        Filter.Tendsto.congr' (Filter.EventuallyEq.symm h2) tendsto_const_nhds
      exact tendsto_nhds_unique h1 h3
  -- structure of the prelimit flows (propagated under the truncated force)
  have hFdiv : ∀ R, ∀ t ∈ Icc (0:ℝ) T, DivFree (F R t) := fun R =>
    divFree_propagates_on_forced hν.le (g := fun t => truncate (boxS R) (gt t))
      (fun t _ => divFree_truncate (hgtdiv t) _) (hFODE R)
      (by rw [hF0]; exact divFree_truncate hdiv _)
  have hFreal : ∀ R, ∀ t ∈ Icc (0:ℝ) T, RealField (F R t) := fun R =>
    realField_propagates_on_forced hν.le (boxS_symm R)
      (g := fun t => truncate (boxS R) (gt t))
      (fun t _ k hk => hFs R t k hk)
      (fun t _ => realField_truncate (hgtreal t) (boxS_symm R)) (hFODE R)
      (by rw [hF0]; exact realField_truncate hreal (boxS_symm R))
  -- structure of the limit
  have hcdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) := fun t ht =>
    divFree_limit (fun n => hFdiv (φ n) t ht) (fun l => hpt t ht l)
  have hcreal : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) := fun t ht =>
    realField_limit (fun n => hFreal (φ n) t ht) (fun l => hpt t ht l)
  -- bounds in the limit
  have hEnF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖F (φ n) t l‖ ^ 2 ≤ Es := fun t ht n Fs =>
    (sum_sq_le_en (fun k hk => hFs (φ n) t k hk) Fs).trans (hFtrap (φ n) t ht).1
  have hZnF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖F (φ n) t l‖ ^ 2 ≤ Zs := fun t ht n Fs =>
    (sum_wsq_le_ens (fun k hk => hFs (φ n) t k hk) Fs).trans (hFtrap (φ n) t ht).2
  have hcen : ∀ t ∈ Icc (0:ℝ) T,
      en (c t) ≤ Es ∧ Summable fun l => ‖c t l‖ ^ 2 := fun t ht =>
    en_limit_le (fun n Fs => hEnF t ht n Fs) (fun l => hpt t ht l)
  have hcens : ∀ t ∈ Icc (0:ℝ) T,
      ens (c t) ≤ Zs ∧ Summable fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 := fun t ht =>
    ens_limit_le (fun n Fs => hZnF t ht n Fs) (fun l => hpt t ht l)
  have htrap : ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs :=
    fun t ht => ⟨(hcen t ht).1, (hcens t ht).1⟩
  -- mode continuity of the limit
  have hccont : ∀ l, ContinuousOn (fun s => c s l) (Icc (0:ℝ) T) := by
    intro l
    have h1 : Continuous fun s => c s l := by
      show Continuous fun s => Set.IccExtend hT (⇑(f l)) s
      exact (f l).continuous.comp continuous_projIcc
    exact h1.continuousOn
  -- finite-sum bounds for the limit (feeding the convection continuity)
  have hEnLim : ∀ t ∈ Icc (0:ℝ) T, ∀ (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖c t l‖ ^ 2 ≤ Es := fun t ht Fs =>
    ((hcen t ht).2.sum_le_tsum Fs (fun l _ => sq_nonneg _)).trans (hcen t ht).1
  have hZnLim : ∀ t ∈ Icc (0:ℝ) T, ∀ (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 ≤ Zs := fun t ht Fs =>
    ((hcens t ht).2.sum_le_tsum Fs (fun l _ => by positivity)).trans (hcens t ht).1
  -- lerayProj kills zero
  have hP0 : ∀ k : Fin 3 → ℤ, lerayProj k 0 = 0 := by
    intro k
    have h : lerayProj k ((0:Vel) - 0) = lerayProj k 0 - lerayProj k 0 :=
      lerayProj_sub k 0 0
    rw [sub_self, sub_self] at h
    exact h
  -- the integral equation
  have hinteq : ∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k) := by
    intro t ht k
    by_cases hk0 : k = (0 : Fin 3 → ℤ)
    · subst hk0
      -- the zero-mode integrand vanishes on the integration interval
      have hint : EqOn (fun s => (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
          lerayProj 0 (convFull (c s) 0) + g s 0) (fun _ => (0 : Vel)) (uIcc (0:ℝ) t) := by
        intro s hs
        have hs' : s ∈ Icc (0:ℝ) t := by rwa [uIcc_of_le ht.1] at hs
        have hdivs : DivFree (c s) := by
          rw [hclamp s]
          exact hcdiv _ (Set.projIcc 0 T hT s).2
        show (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
          lerayProj 0 (convFull (c s) 0) + g s 0 = 0
        rw [hczero s, smul_zero, convFull_zero_of_divFree hdivs, hP0 0, add_zero,
          hgmean s hs'.1, add_zero]
      rw [hczero t, hmean, intervalIntegral.integral_congr hint]
      simp
    · have h := integral_equation_limit_forced hν.le hEs hZs.le hsqG hT
        (S := fun n => boxS (φ n)) (F := fun n => F (φ n)) (u := c) (g := gt)
        (fun n t' k' hk' => hFs (φ n) t' k' hk')
        (fun n => hFODE (φ n))
        (fun n t' ht' => (hFtrap (φ n) t' ht').1)
        (fun n t' ht' => (hFtrap (φ n) t' ht').2)
        (fun k' hk' => by
          obtain ⟨R₀, hR₀⟩ := exists_boxS k' hk'
          exact Filter.eventually_atTop.mpr
            ⟨R₀, fun n hn => hR₀ (φ n) (hn.trans hφ.le_apply)⟩)
        hu (fun k' => (hgtc k').continuousOn) (fun t' _ k' => hgtb t' k') t ht k hk0
      rw [h, hc0]
      -- swap the clamped force for the given one on the integration interval
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' : s ∈ Icc (0:ℝ) t := by rwa [uIcc_of_le ht.1] at hs
      show (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + gt s k =
        (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k
      rw [hgt_eq s hs'.1]
  -- continuity of the limit right-hand side
  have hgcont : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k +
      lerayProj k (convFull (c s) k) + g s k) (Icc (0:ℝ) T) := by
    intro k
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact continuousOn_const.smul (hccont k)
    · exact (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hEs hZs.le hEnLim hZnLim hccont k)
    · exact (hgc k).mono Icc_subset_Ici_self
  -- the derivative on the interior
  have hderiv : ∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t := by
    intro t ht k
    refine hasDerivAt_of_integral_eq (hgcont k) ?_ t ht
    intro t' ht'
    show c t' k = c 0 k + ∫ s in (0:ℝ)..t',
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)
    rw [hc0]
    exact hinteq t' ht' k
  exact ⟨c, hc0, fun t ht => ⟨hcreal t ht, hcdiv t ht⟩,
    fun t ht => ⟨(hcen t ht).2, (hcens t ht).2⟩, hccont, hinteq, hderiv, htrap⟩

/-! ## In-tree composition probe: frozen ⇒ forced clause list at `g = 0` -/

/-- **F3 composition probe: the frozen `theorem_B_cont` witness satisfies the
forced seven-clause list at `g = 0`, for every box containing the data.**
Because the forced right-hand sides are spelled inline (`… + g s k`),
substituting the zero force reduces each forced equation clause to the
frozen one by `simpa`.  This is the only compiled direction between the two
chains (the `κ` here is the frozen one, and the smallness is the frozen
strict one); it is NOT a strengthening claim in either direction. -/
theorem probe_frozen_flow_inhabits_forced_clauses :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ {Es Zs : ℝ}, en c₀ ≤ Es → ens c₀ ≤ Zs →
      ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) +
            (fun (_ : ℝ) (_ : Fin 3 → ℤ) => (0 : Vel)) s k)) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) +
            (fun (_ : ℝ) (_ : Fin 3 → ℤ) => (0 : Vel)) t k) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ Es ∧ ens (c t) ≤ Zs) := by
  obtain ⟨κ, hκ, hB⟩ := theorem_B_cont
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0 Es Zs hEs hZs T hT
  obtain ⟨c, hc0, hstr, hsum, hcont, heq, hode, htrap⟩ :=
    hB hν hE hZ hmean hreal hdiv h0 T hT
  refine ⟨c, hc0, hstr, hsum, hcont, ?_, ?_, ?_⟩
  · intro t ht k
    simpa using heq t ht k
  · intro t ht k
    simpa using hode t ht k
  · intro t ht
    exact ⟨(htrap t ht).1.trans hEs, (htrap t ht).2.1.trans hZs⟩

/-! ## Uniqueness for the forced integral equation -/

/-- **F4 (delivered early), uniqueness for the forced full system in the
enstrophy-bounded class.**  Two mode-continuous flows on `[0, T]` with the
same datum, summable energy and enstrophy series bounded by budgets `E, Z`,
divergence-free, satisfying the forced full-convolution integral equation
under the same per-mode-continuous force, agree at every time and mode.  The
finite-section energy method of `theorem_B_unique` replayed: the force
cancels in the difference of the two mode ODEs, and the zero mode of each
flow is the same integral of the force (so the pairing bound's zero-mode
side condition holds for the difference).  No smallness, no reality, and no
mean-zero hypothesis on the force. -/
theorem theorem_B_unique_forced :
    ∀ {ν E Z T : ℝ}, 0 < ν → 0 ≤ T →
    ∀ {c₀ : (Fin 3 → ℤ) → Vel} {c₁ c₂ g : ℝ → (Fin 3 → ℤ) → Vel},
    (∀ k, ContinuousOn (fun s => g s k) (Icc (0:ℝ) T)) →
    c₁ 0 = c₀ → c₂ 0 = c₀ →
    (∀ k, ContinuousOn (fun s => c₁ s k) (Icc (0:ℝ) T)) →
    (∀ k, ContinuousOn (fun s => c₂ s k) (Icc (0:ℝ) T)) →
    (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2)) →
    (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₂ t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2)) →
    (∀ t ∈ Icc (0:ℝ) T, en (c₁ t) ≤ E ∧ ens (c₁ t) ≤ Z) →
    (∀ t ∈ Icc (0:ℝ) T, en (c₂ t) ≤ E ∧ ens (c₂ t) ≤ Z) →
    (∀ t ∈ Icc (0:ℝ) T, DivFree (c₁ t)) →
    (∀ t ∈ Icc (0:ℝ) T, DivFree (c₂ t)) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k) + g s k)) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k) + g s k)) →
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₂ t k := by
  intro ν E Z T hν hT c₀ c₁ c₂ g hgc h10 h20 h1cont h2cont h1sum h2sum h1b h2b
    h1div h2div h1eq h2eq
  -- nonnegativity of the budgets (from nonempty window membership at 0)
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_refl 0, hT⟩
  have hE0 : 0 ≤ E := le_trans (tsum_nonneg fun l => sq_nonneg _) (h1b 0 h0mem).1
  have hZ0 : 0 ≤ Z := le_trans (tsum_nonneg fun l => by positivity) (h1b 0 h0mem).2
  -- finite-sum bound forms for continuity of the convection
  have h1enF : ∀ t ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖c₁ t l‖ ^ 2 ≤ E := fun t ht F =>
    ((h1sum t ht).1.sum_le_tsum F (fun l _ => sq_nonneg _)).trans (h1b t ht).1
  have h1ensF : ∀ t ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c₁ t l‖ ^ 2 ≤ Z := fun t ht F =>
    ((h1sum t ht).2.sum_le_tsum F (fun l _ => by positivity)).trans (h1b t ht).2
  have h2enF : ∀ t ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖c₂ t l‖ ^ 2 ≤ E := fun t ht F =>
    ((h2sum t ht).1.sum_le_tsum F (fun l _ => sq_nonneg _)).trans (h2b t ht).1
  have h2ensF : ∀ t ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c₂ t l‖ ^ 2 ≤ Z := fun t ht F =>
    ((h2sum t ht).2.sum_le_tsum F (fun l _ => by positivity)).trans (h2b t ht).2
  -- the continuous right-hand sides (the force is per-mode continuous)
  have h1g : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c₁ s k +
      lerayProj k (convFull (c₁ s) k) + g s k) (Icc (0:ℝ) T) := fun k =>
    ((continuousOn_const.smul (h1cont k)).add
      ((lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h1enF h1ensF h1cont k))).add (hgc k)
  have h2g : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c₂ s k +
      lerayProj k (convFull (c₂ s) k) + g s k) (Icc (0:ℝ) T) := fun k =>
    ((continuousOn_const.smul (h2cont k)).add
      ((lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h2enF h2ensF h2cont k))).add (hgc k)
  -- interior mode ODEs from the integral equations
  have h1ode : ∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convFull (c₁ t) k) + g t k) t := by
    intro t ht k
    refine hasDerivAt_of_integral_eq (h1g k) ?_ t ht
    intro t' ht'
    show c₁ t' k = c₁ 0 k + _
    rw [h10]
    exact h1eq t' ht' k
  have h2ode : ∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convFull (c₂ t) k) + g t k) t := by
    intro t ht k
    refine hasDerivAt_of_integral_eq (h2g k) ?_ t ht
    intro t' ht'
    show c₂ t' k = c₂ 0 k + _
    rw [h20]
    exact h2eq t' ht' k
  -- the zero mode of each flow is the integral of the zero mode of the force
  have hfreq0 : freq (0 : Fin 3 → ℤ) = 0 := by
    have h := freq_sub 0 0
    simpa using h
  have hP0 : lerayProj 0 (0 : Vel) = 0 := by
    have h := lerayProj_sub 0 (0 : Vel) 0
    rw [sub_self, sub_self] at h
    exact h
  have hzero : ∀ c : ℝ → (Fin 3 → ℤ) → Vel,
      (∀ t ∈ Icc (0:ℝ) T, DivFree (c t)) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) →
      ∀ t ∈ Icc (0:ℝ) T, c t 0 = c₀ 0 + ∫ s in (0:ℝ)..t, g s 0 := by
    intro c hdiv heq t ht
    have h1 := heq t ht 0
    have h2 : EqOn (fun s => (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
          lerayProj 0 (convFull (c s) 0) + g s 0) (fun s => g s 0) (uIcc (0:ℝ) t) := by
      intro s hs
      have hsIcc : s ∈ Icc (0:ℝ) T := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      show (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
        lerayProj 0 (convFull (c s) 0) + g s 0 = g s 0
      rw [hfreq0, convFull_zero_of_divFree (hdiv s hsIcc), hP0, add_zero]
      simp
    rw [intervalIntegral.integral_congr h2] at h1
    exact h1
  have h1zero := hzero c₁ (fun t ht => h1div t ht) h1eq
  have h2zero := hzero c₂ (fun t ht => h2div t ht) h2eq
  -- the pairing constant
  obtain ⟨K, hK, hpair⟩ := pairing_absorbed (E := E) (Z := Z) hν hE0 hZ0
  -- the defect and its finite sections
  intro t ht
  -- the section energy over F_R := insert 0 (boxS R)
  set φ : ℕ → ℝ → ℝ := fun R s => ∑ k ∈ insert 0 (boxS R), ‖c₁ s k - c₂ s k‖ ^ 2
    with hφdef
  -- source: the enstrophy section defect of the defect flow
  set σ : ℕ → ℝ → ℝ := fun R s => ens (fun l => c₁ s l - c₂ s l) -
    ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 with hσdef
  -- defect facts on the window
  have hdsum : ∀ s ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ s l - c₂ s l‖ ^ 2) :=
    fun s hs => summable_sq_sub (h1sum s hs).1 (h2sum s hs).1
  have hdwsum : ∀ s ∈ Icc (0:ℝ) T,
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ s l - c₂ s l‖ ^ 2) :=
    fun s hs => summable_wsq_sub (h1sum s hs).2 (h2sum s hs).2
  have hdens : ∀ s ∈ Icc (0:ℝ) T, ens (fun l => c₁ s l - c₂ s l) ≤ 4 * Z := by
    intro s hs
    have h := ens_sub_le (h1sum s hs).2 (h2sum s hs).2
    have h1 := (h1b s hs).2
    have h2 := (h2b s hs).2
    linarith
  have hdcont : ∀ k, ContinuousOn (fun s => c₁ s k - c₂ s k) (Icc (0:ℝ) T) :=
    fun k => (h1cont k).sub (h2cont k)
  have hσnn : ∀ R, ∀ s ∈ Icc (0:ℝ) T, 0 ≤ σ R s := fun R s hs =>
    tail_nonneg (hdwsum s hs) _
  have hσint : ∀ R, IntervalIntegrable (σ R) MeasureTheory.volume 0 T := fun R =>
    tail_integrable (by positivity) hT hdcont hdwsum hdens _
  -- φ facts
  have hφcont : ∀ R, ContinuousOn (φ R) (Icc (0:ℝ) T) := by
    intro R
    refine continuousOn_finsetSum _ fun k _ => ?_
    exact ((hdcont k).norm).pow 2
  have hφ0 : ∀ R, φ R 0 = 0 := by
    intro R
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h10, h20, sub_self]
    simp
  have hφnn : ∀ R s, 0 ≤ φ R s :=
    fun R s => Finset.sum_nonneg fun k _ => sq_nonneg _
  -- the section-energy derivative formula (the force cancels in the difference)
  set gR : ℕ → ℝ → ℝ := fun R s => ∑ k ∈ insert 0 (boxS R),
    2 * inner ℝ (c₁ s k - c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k) +
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k))) with hgdef
  have hφderiv : ∀ R, ∀ s ∈ Ioo (0:ℝ) T, HasDerivAt (φ R) (gR R s) s := by
    intro R s hs
    refine hasDerivAt_finset_sum_sq _ fun k _ => ?_
    have h1 := h1ode s hs k
    have h2 := h2ode s hs k
    have h3 := h1.sub h2
    have h4 : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k) + g s k) -
        ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k) + g s k) =
        (-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k) +
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) := by
      rw [smul_sub]
      abel
    rw [h4] at h3
    exact h3
  have hgcont : ∀ R, ContinuousOn (gR R) (Icc (0:ℝ) T) := by
    intro R
    refine continuousOn_finsetSum _ fun k _ => ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inner (hdcont k) ?_
    refine ContinuousOn.add (continuousOn_const.smul (hdcont k)) ?_
    refine ContinuousOn.sub ?_ ?_
    · exact (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h1enF h1ensF h1cont k)
    · exact (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h2enF h2ensF h2cont k)
  -- the derivative bound
  have hgle : ∀ R : ℕ, 0 < R → ∀ s ∈ Icc (0:ℝ) T,
      gR R s ≤ K * φ R s + (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2)) := by
    intro R hR s hs
    have hsIcc : s ∈ Icc (0:ℝ) T := hs
    -- split the inner product
    have hsplit : gR R s = (∑ k ∈ insert 0 (boxS R),
        2 * inner ℝ (c₁ s k - c₂ s k) ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k))) +
        ∑ k ∈ insert 0 (boxS R), 2 * inner ℝ (c₁ s k - c₂ s k)
          (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) := by
      rw [hgdef]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_add_right]
      ring
    -- dissipation part exactly
    have hdiss : (∑ k ∈ insert 0 (boxS R),
        2 * inner ℝ (c₁ s k - c₂ s k) ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k))) =
        -2 * ν * ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    -- the pairing part via the Leray drop and the absorbed bound
    have hdivd : ∀ k, dotR (c₁ s k - c₂ s k) (freq k) = 0 := by
      intro k
      rw [dotR_sub_left', h1div s hsIcc k, h2div s hsIcc k, sub_self]
    have hpairpart : (∑ k ∈ insert 0 (boxS R), 2 * inner ℝ (c₁ s k - c₂ s k)
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k))) ≤
        ν * ens (fun l => c₁ s l - c₂ s l) + K * en (fun l => c₁ s l - c₂ s l) := by
      have hre : ∀ k, inner ℝ (c₁ s k - c₂ s k)
          (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) =
          inner ℝ (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k) := by
        intro k
        rw [← lerayProj_sub]
        rw [real_inner_comm]
        exact inner_lerayProj_left (hdivd k)
      calc (∑ k ∈ insert 0 (boxS R), 2 * inner ℝ (c₁ s k - c₂ s k)
            (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)))
          = 2 * ∑ k ∈ insert 0 (boxS R), inner ℝ
            (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by rw [hre k]
        _ ≤ 2 * |∑ k ∈ insert 0 (boxS R), inner ℝ
            (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k)| := by
            have := le_abs_self (∑ k ∈ insert 0 (boxS R), inner ℝ
              (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k))
            linarith
        _ ≤ ν * ens (fun l => c₁ s l - c₂ s l) + K * en (fun l => c₁ s l - c₂ s l) := by
            have h0eq : c₁ s 0 = c₂ s 0 := by
              rw [h1zero s hsIcc, h2zero s hsIcc]
            exact hpair (h1sum s hsIcc).1 (h1sum s hsIcc).2
              (h2sum s hsIcc).1 (h2sum s hsIcc).2
              (h1b s hsIcc).1 (h1b s hsIcc).2 (h2b s hsIcc).1 (h2b s hsIcc).2
              h0eq _
    -- assemble: ens of the defect ≥ its section, en ≤ section + tail
    have htail := tail_en_lt (Z := 4 * Z) R hR (hdsum s hsIcc) (hdwsum s hsIcc)
      (hdens s hsIcc)
    have hens_split : ens (fun l => c₁ s l - c₂ s l) =
        (∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2) + σ R s := by
      rw [hσdef]
      ring
    have hensF_nn : 0 ≤ ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => by positivity
    have hen_le : en (fun l => c₁ s l - c₂ s l) ≤ φ R s + 4 * Z / (R:ℝ) ^ 2 := by
      have := htail
      rw [hφdef]
      simp only
      linarith
    calc gR R s ≤ (-2 * ν * ∑ k ∈ insert 0 (boxS R),
          ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2) +
          (ν * ens (fun l => c₁ s l - c₂ s l) +
            K * en (fun l => c₁ s l - c₂ s l)) := by
          rw [hsplit, hdiss]
          exact add_le_add le_rfl hpairpart
      _ ≤ ν * σ R s + K * (φ R s + 4 * Z / (R:ℝ) ^ 2) := by
          rw [hens_split]
          have hK' := hK.le
          have hprod := mul_le_mul_of_nonneg_left hen_le hK'
          have hprod2 : 0 ≤ ν * (∑ k ∈ insert 0 (boxS R),
              ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2) :=
            mul_nonneg hν.le hensF_nn
          nlinarith [hprod, hprod2]
      _ = K * φ R s + (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2)) := by ring
  -- FTC on the sections
  have hφint : ∀ R, ∀ t' ∈ Icc (0:ℝ) T,
      IntervalIntegrable (φ R) MeasureTheory.volume 0 t' := by
    intro R t' ht'
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht'.1]
    exact (hφcont R).mono (Icc_subset_Icc le_rfl ht'.2)
  have hgint : ∀ R, ∀ t' ∈ Icc (0:ℝ) T,
      IntervalIntegrable (gR R) MeasureTheory.volume 0 t' := by
    intro R t' ht'
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht'.1]
    exact (hgcont R).mono (Icc_subset_Icc le_rfl ht'.2)
  have hσint' : ∀ R, ∀ t' ∈ Icc (0:ℝ) T,
      IntervalIntegrable (σ R) MeasureTheory.volume 0 t' := by
    intro R t' ht'
    refine (hσint R).mono_set ?_
    rw [uIcc_of_le ht'.1, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht'.2
  have hftc : ∀ R, ∀ t' ∈ Icc (0:ℝ) T, φ R t' = ∫ s in (0:ℝ)..t', gR R s := by
    intro R t' ht'
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht'.1
      ((hφcont R).mono (Icc_subset_Icc le_rfl ht'.2))
      (fun s hs => hφderiv R s ⟨hs.1, lt_of_lt_of_le hs.2 ht'.2⟩)
      (hgint R t' ht')
    rw [h, hφ0 R, sub_zero]
  -- the integral inequality
  have hσ_glob : ∀ R, ∀ t' ∈ Icc (0:ℝ) T,
      (∫ s in (0:ℝ)..t', σ R s) ≤ ∫ s in (0:ℝ)..T, σ R s := by
    intro R t' ht'
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hσint' R t' ht') ((hσint R).mono_set (by
        rw [uIcc_of_le ht'.2, uIcc_of_le hT]
        exact Icc_subset_Icc ht'.1 le_rfl))
    have hnn : 0 ≤ ∫ s in t'..T, σ R s := by
      refine intervalIntegral.integral_nonneg ht'.2 fun s hs => ?_
      exact hσnn R s ⟨ht'.1.trans hs.1, hs.2⟩
    linarith [hsplit.symm.le, hsplit.symm.ge]
  set S : ℕ → ℝ := fun R => ν * (∫ s in (0:ℝ)..T, σ R s) + K * (4 * Z / (R:ℝ) ^ 2) * T
    with hSdef
  have hSnn : ∀ R : ℕ, 0 ≤ S R := by
    intro R
    have h1 : 0 ≤ ∫ s in (0:ℝ)..T, σ R s :=
      intervalIntegral.integral_nonneg hT fun s hs => hσnn R s hs
    have h2 : (0:ℝ) ≤ 4 * Z / (R:ℝ) ^ 2 := by positivity
    have h3 : (0:ℝ) ≤ K * (4 * Z / (R:ℝ) ^ 2) * T := by positivity
    positivity
  have hkey : ∀ R : ℕ, 0 < R → ∀ t' ∈ Icc (0:ℝ) T,
      φ R t' ≤ K * (∫ s in (0:ℝ)..t', φ R s) + S R := by
    intro R hR t' ht'
    have hBint : IntervalIntegrable
        (fun s => K * φ R s + (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2)))
        MeasureTheory.volume 0 t' :=
      ((hφint R t' ht').const_mul K).add
        (((hσint' R t' ht').const_mul ν).add intervalIntegrable_const)
    have hmono : (∫ s in (0:ℝ)..t', gR R s) ≤
        ∫ s in (0:ℝ)..t', (K * φ R s + (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2))) := by
      refine intervalIntegral.integral_mono_on ht'.1 (hgint R t' ht') hBint ?_
      intro s hs
      exact hgle R hR s ⟨hs.1, hs.2.trans ht'.2⟩
    have hsplit : (∫ s in (0:ℝ)..t',
        (K * φ R s + (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2)))) =
        K * (∫ s in (0:ℝ)..t', φ R s) + (ν * (∫ s in (0:ℝ)..t', σ R s) +
          K * (4 * Z / (R:ℝ) ^ 2) * t') := by
      rw [intervalIntegral.integral_add ((hφint R t' ht').const_mul K)
        (((hσint' R t' ht').const_mul ν).add intervalIntegrable_const),
        intervalIntegral.integral_add ((hσint' R t' ht').const_mul ν)
          intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      ring
    have hσle := hσ_glob R t' ht'
    have htle : t' ≤ T := ht'.2
    have hc : (0:ℝ) ≤ K * (4 * Z / (R:ℝ) ^ 2) := by positivity
    calc φ R t' = ∫ s in (0:ℝ)..t', gR R s := hftc R t' ht'
      _ ≤ K * (∫ s in (0:ℝ)..t', φ R s) + (ν * (∫ s in (0:ℝ)..t', σ R s) +
          K * (4 * Z / (R:ℝ) ^ 2) * t') := by rw [← hsplit]; exact hmono
      _ ≤ K * (∫ s in (0:ℝ)..t', φ R s) + S R := by
          rw [hSdef]
          have h1 : ν * (∫ s in (0:ℝ)..t', σ R s) ≤ ν * ∫ s in (0:ℝ)..T, σ R s :=
            mul_le_mul_of_nonneg_left hσle hν.le
          have h2 : K * (4 * Z / (R:ℝ) ^ 2) * t' ≤ K * (4 * Z / (R:ℝ) ^ 2) * T :=
            mul_le_mul_of_nonneg_left htle hc
          simp only
          linarith
  -- the Φ-trick: Gronwall on the primitive
  have hΨ : ∀ R : ℕ, 0 < R → ∀ t' ∈ Icc (0:ℝ) T,
      φ R t' ≤ S R * (Real.exp (K * T) + 1) := by
    intro R hR t' ht'
    set Ψ : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, φ R s with hΨdef
    have hΨcont : ContinuousOn Ψ (Icc 0 T) := by
      have hint : MeasureTheory.IntegrableOn (φ R) (uIcc (0:ℝ) T)
          MeasureTheory.volume := by
        rw [uIcc_of_le hT]
        exact (hφcont R).integrableOn_Icc
      have h := intervalIntegral.continuousOn_primitive_interval hint
      rwa [uIcc_of_le hT] at h
    have hΨ0 : Ψ 0 = 0 := intervalIntegral.integral_same
    have hΨderiv : ∀ u ∈ Ioo (0:ℝ) T, ∃ f', HasDerivAt Ψ f' u ∧
        f' ≤ K * Ψ u + S R := by
      intro u hu
      refine ⟨φ R u, ?_, ?_⟩
      · refine intervalIntegral.integral_hasDerivAt_right
          (hφint R u ⟨hu.1.le, hu.2.le⟩) ?_ ?_
        · exact ((hφcont R).mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter
            isOpen_Ioo u hu
        · exact ((hφcont R).continuousAt (Icc_mem_nhds hu.1 hu.2))
      · exact hkey R hR u ⟨hu.1.le, hu.2.le⟩
    have hG := gronwall_const_source hK (hSnn R) hΨcont hΨ0 hΨderiv t' ht'
    have h2 := hkey R hR t' ht'
    have h3 : K * Ψ t' ≤ K * (S R / K * Real.exp (K * T)) :=
      mul_le_mul_of_nonneg_left hG hK.le
    have h4 : K * (S R / K * Real.exp (K * T)) = S R * Real.exp (K * T) := by
      field_simp
    have h5 : K * Ψ t' ≤ S R * Real.exp (K * T) := h3.trans_eq h4
    calc φ R t' ≤ K * Ψ t' + S R := h2
      _ ≤ S R * Real.exp (K * T) + S R := by linarith
      _ = S R * (Real.exp (K * T) + 1) := by ring
  -- the squeeze in R
  have hsqueeze : ∀ R : ℕ, 0 < R →
      en (fun l => c₁ t l - c₂ t l) ≤ S R * (Real.exp (K * T) + 1) +
        4 * Z / (R:ℝ) ^ 2 := by
    intro R hR
    have htail := tail_en_lt (Z := 4 * Z) R hR (hdsum t ht) (hdwsum t ht) (hdens t ht)
    have hφb := hΨ R hR t ht
    rw [hφdef] at hφb
    simp only at htail hφb ⊢
    linarith
  -- the tail source vanishes
  have hS0 : Filter.Tendsto S Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℕ => ∫ s in (0:ℝ)..T, σ R s)
        Filter.atTop (nhds 0) := tail_source (by positivity) hT hdcont hdwsum hdens
    have h2 : Filter.Tendsto (fun R : ℕ => (R:ℝ) ^ 2) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun R => ?_)
        tendsto_natCast_atTop_atTop
      have hR : R ≤ R ^ 2 := Nat.le_self_pow (by norm_num) R
      exact_mod_cast hR
    have h3 : Filter.Tendsto (fun R : ℕ => 4 * Z / (R:ℝ) ^ 2)
        Filter.atTop (nhds 0) := by
      have h4 := h2.inv_tendsto_atTop
      have h5 := h4.const_mul (4 * Z)
      simpa [div_eq_mul_inv] using h5
    have h6 := (h1.const_mul ν).add ((h3.const_mul K).mul_const T)
    simpa [hSdef] using h6
  have hA0 : Filter.Tendsto (fun R : ℕ => S R * (Real.exp (K * T) + 1) +
      4 * Z / (R:ℝ) ^ 2) Filter.atTop (nhds 0) := by
    have h1 := hS0.mul_const (Real.exp (K * T) + 1)
    have h2 : Filter.Tendsto (fun R : ℕ => (R:ℝ) ^ 2) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun R => ?_)
        tendsto_natCast_atTop_atTop
      have hR : R ≤ R ^ 2 := Nat.le_self_pow (by norm_num) R
      exact_mod_cast hR
    have h3 : Filter.Tendsto (fun R : ℕ => 4 * Z / (R:ℝ) ^ 2)
        Filter.atTop (nhds 0) := by
      have h4 := h2.inv_tendsto_atTop
      have h5 := h4.const_mul (4 * Z)
      simpa [div_eq_mul_inv] using h5
    have h6 := h1.add h3
    simpa using h6
  -- energy of the defect vanishes
  have hen0 : en (fun l => c₁ t l - c₂ t l) = 0 := by
    have hle : en (fun l => c₁ t l - c₂ t l) ≤ 0 := by
      refine le_of_tendsto_of_tendsto tendsto_const_nhds hA0 ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with R hR
      exact hsqueeze R hR
    have hge : 0 ≤ en (fun l => c₁ t l - c₂ t l) := tsum_nonneg fun l => sq_nonneg _
    linarith
  -- every mode vanishes
  intro k
  have hk : ‖c₁ t k - c₂ t k‖ ^ 2 ≤ en (fun l => c₁ t l - c₂ t l) := by
    have h := (hdsum t ht).le_tsum k (fun j _ => sq_nonneg _)
    simpa [en] using h
  rw [hen0] at hk
  have hnorm : ‖c₁ t k - c₂ t k‖ = 0 := by
    nlinarith [sq_nonneg ‖c₁ t k - c₂ t k‖, norm_nonneg (c₁ t k - c₂ t k)]
  have hzero' : c₁ t k - c₂ t k = 0 := norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hzero'

/-! ## The eternal forced flow -/

/-- **F4 (delivered early), the eternal solution of the forced full
system.**  ONE flow on the half line serving every horizon: it starts at the
datum, is real, divergence-free, with honestly summable energy and
enstrophy series at every time, is mode-continuous on `[0, ∞)`, satisfies
the forced full-convolution integral equation at every `t ≥ 0` and the
forced differential equation at every `t > 0`, and stays inside the box
forever.  Built by splicing the per-horizon `theorem_B_forced` witnesses
along integer segments; `theorem_B_unique_forced` makes the splice
seamless.  Uniqueness of the eternal flow ITSELF is not part of this
statement; the exported mode continuity, summability and integral-equation
clauses place every restriction of this flow inside the forced uniqueness
class, so any two eternal flows with these clauses agree on every horizon by
`theorem_B_unique_forced`.  The derived bound `κ·en (c t)·ens (c t) ≤ ν⁴` is
deliberately NOT exported (the `κ` here is `8·K`, not the frozen `K`). -/
theorem ns_full_global_flow_forced :
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
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs) := by
  obtain ⟨κ, hκ, hB⟩ := theorem_B_forced
  refine ⟨κ, hκ, ?_⟩
  intro ν Es Zs G hν hEs hZs hκE hGE hGZ c₀ g hE hZ hmean hreal hdiv h0E h0Z
    hgmean hgreal hgdiv hgsum hgen hgc
  -- one witness per natural horizon
  have hex : ∀ n : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = c₀ ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
        Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
      (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) (n:ℝ))) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k) + g s k)) ∧
      (∀ t ∈ Ioo (0:ℝ) (n:ℝ), ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k) + g t k) t) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), en (c t) ≤ Es ∧ ens (c t) ≤ Zs) :=
    fun n => hB hν hEs hZs hκE hGE hGZ hE hZ hmean hreal hdiv h0E h0Z hgmean hgreal hgdiv
      hgsum hgen hgc (n:ℝ) (Nat.cast_nonneg n)
  choose F hF0 hFstr hFsum hFcont hFeq hFode hFtrap using hex
  -- pairwise agreement on overlapping horizons via uniqueness at the min
  have hA : ∀ m n : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ (m:ℝ) → s ≤ (n:ℝ) →
      ∀ k, F m s k = F n s k := by
    intro m n s hs0 hsm hsn k
    have hminm : ((min m n : ℕ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast min_le_left m n
    have hminn : ((min m n : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast min_le_right m n
    have hsmin : s ≤ ((min m n : ℕ) : ℝ) := by
      rw [Nat.cast_min]
      exact le_min hsm hsn
    -- restrict the horizon-j data to the min window
    have hsub : ∀ j : ℕ, ((min m n : ℕ) : ℝ) ≤ (j:ℝ) →
        Icc (0:ℝ) ((min m n : ℕ) : ℝ) ⊆ Icc (0:ℝ) (j:ℝ) :=
      fun j hj => Icc_subset_Icc le_rfl hj
    exact theorem_B_unique_forced (E := Es) (Z := Zs) hν
      (Nat.cast_nonneg _) (fun k' => (hgc k').mono Icc_subset_Ici_self) (hF0 m) (hF0 n)
      (fun k' => (hFcont m k').mono (hsub m hminm))
      (fun k' => (hFcont n k').mono (hsub n hminn))
      (fun t ht => hFsum m t (hsub m hminm ht))
      (fun t ht => hFsum n t (hsub n hminn ht))
      (fun t ht => hFtrap m t (hsub m hminm ht))
      (fun t ht => hFtrap n t (hsub n hminn ht))
      (fun t ht => (hFstr m t (hsub m hminm ht)).2)
      (fun t ht => (hFstr n t (hsub n hminn ht)).2)
      (fun t ht => hFeq m t (hsub m hminm ht))
      (fun t ht => hFeq n t (hsub n hminn ht))
      s ⟨hs0, hsmin⟩ k
  -- the spliced eternal flow
  set nseg : ℝ → ℕ := fun s => if s ≤ 1 then 2 else Nat.floor s + 2 with hnseg
  set c : ℝ → (Fin 3 → ℤ) → Vel := fun s => F (nseg s) s with hcdef
  have hseg_ge : ∀ s : ℝ, 0 ≤ s → s ≤ (nseg s : ℝ) := by
    intro s hs
    rw [hnseg]
    by_cases h1 : s ≤ 1
    · simp only [if_pos h1]
      norm_num
      linarith
    · simp only [if_neg h1]
      push_cast
      have := Nat.lt_floor_add_one s
      linarith
  -- the value of the splice against any large horizon
  have hval : ∀ s : ℝ, 0 ≤ s → ∀ N : ℕ, s ≤ (N:ℝ) → ∀ k, c s k = F N s k := by
    intro s hs N hsN k
    exact hA (nseg s) N s hs (hseg_ge s hs) hsN k
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- initial value
    show F (nseg 0) 0 = c₀
    exact hF0 _
  · -- structure
    intro t ht
    have h := hFstr (nseg t) t ⟨ht, hseg_ge t ht⟩
    exact h
  · -- summability
    intro t ht
    exact hFsum (nseg t) t ⟨ht, hseg_ge t ht⟩
  · -- mode continuity on the half line
    intro k t ht
    set N : ℕ := Nat.floor t + 2 with hNc
    have htN : t < (N:ℝ) := by
      rw [hNc]
      push_cast
      have := Nat.lt_floor_add_one t
      linarith
    have hcongr : ContinuousOn (fun s => c s k) (Icc (0:ℝ) (N:ℝ)) := by
      refine (hFcont N k).congr fun s hs => ?_
      exact hval s hs.1 N hs.2 k
    have h1 : ContinuousWithinAt (fun s => c s k) (Icc (0:ℝ) (N:ℝ)) t :=
      hcongr t ⟨ht, htN.le⟩
    refine h1.mono_of_mem_nhdsWithin ?_
    have hmem : Ici (0:ℝ) ∩ Iio ((N:ℕ):ℝ) ∈ nhdsWithin t (Ici (0:ℝ)) :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htN))
    refine Filter.mem_of_superset hmem ?_
    intro s hs
    exact ⟨hs.1, hs.2.le⟩
  · -- the integral equation
    intro t ht k
    have hN : t ≤ ((nseg t : ℕ) : ℝ) := hseg_ge t ht
    have h := hFeq (nseg t) t ⟨ht, hN⟩ k
    -- rewrite the integrand: on [0, t] the splice agrees with F (nseg t)
    have hcong : EqOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k +
        lerayProj k (convFull (c s) k) + g s k)
        (fun s => (-(ν * ‖freq k‖ ^ 2)) • F (nseg t) s k +
          lerayProj k (convFull (F (nseg t) s) k) + g s k) (uIcc (0:ℝ) t) := by
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) t := by rwa [uIcc_of_le ht] at hs
      have hsN : s ≤ ((nseg t : ℕ) : ℝ) := hs'.2.trans hN
      have hfields : c s = F (nseg t) s := funext fun j => hval s hs'.1 _ hsN j
      simp only [hfields]
    rw [show c t k = F (nseg t) t k from hval t ht _ hN k,
      intervalIntegral.integral_congr hcong]
    exact h
  · -- the derivative at interior times
    intro t ht k
    set N : ℕ := Nat.floor t + 2 with hN
    have htN : t < (N:ℝ) := by
      rw [hN]
      push_cast
      have := Nat.lt_floor_add_one t
      linarith
    have hode := hFode N t ⟨ht, htN⟩ k
    -- transfer along local agreement with F N
    have hev : (fun s => c s k) =ᶠ[nhds t] (fun s => F N s k) := by
      refine Filter.eventuallyEq_of_mem
        (Ioo_mem_nhds (show max 0 (t - 1/2) < t by
          by_cases h : 0 ≤ t - 1/2
          · rw [max_eq_right h]; linarith [ht]
          · rw [max_eq_left (not_le.mp h).le]; exact ht) htN) (fun s hs => ?_)
      have hs0 : 0 ≤ s := le_trans (le_max_left 0 _) hs.1.le
      exact hval s hs0 N hs.2.le k
    have hvt' : c t = F N t := funext fun j => hval t ht.le N htN.le j
    rw [hvt']
    exact hode.congr_of_eventuallyEq hev
  · -- the box
    intro t ht
    exact hFtrap (nseg t) t ⟨ht, hseg_ge t ht⟩

end TheoremB
