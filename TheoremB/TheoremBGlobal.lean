/-
# THEOREM B (Tier 3 summit)

The Galerkin exhaustion family, the per-mode limit passage, and the
unconditional Theorem B for the full Navier-Stokes coefficient system.
-/
import TheoremB.LimitHelpers
import TheoremB.ConvContinuity

namespace TheoremB

open Set

/-- Tier-3 limit passage on a fixed nonzero mode: a uniform limit of budgeted
Galerkin flows satisfies the full-convection integral equation on `[0, T]`. -/
theorem integral_equation_limit {ν E Z T : ℝ} (hν : 0 ≤ ν) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    (hT : 0 ≤ T) {S : ℕ → Finset (Fin 3 → ℤ)} {F : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    {g : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ n (t : ℝ) k, k ∉ S n → F n t k = 0)
    (hODE : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => F n s k)
      ((-(ν * ‖freq k‖ ^ 2)) • F n t k + lerayProj k (convGal (S n) (F n t) k)) t)
    (hEn : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, en (F n t) ≤ E)
    (hZn : ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, ens (F n t) ≤ Z)
    (hbox : ∀ k : Fin 3 → ℤ, k ≠ 0 → ∀ᶠ n in Filter.atTop, k ∈ S n)
    (hu : ∀ l, TendstoUniformlyOn (fun n t => F n t l) (fun t => g t l)
      Filter.atTop (Set.Icc (0:ℝ) T)) :
    ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k : Fin 3 → ℤ, k ≠ 0 →
      g t k = g 0 k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • g s k + lerayProj k (convFull (g s) k)) := by
  intro t ht k hk
  -- every mode curve of every prelimit flow is continuous on the window
  have hcontMode : ∀ n l, ContinuousOn (fun s => F n s l) (Icc (0:ℝ) T) := by
    intro n l s hs
    exact (hODE n s hs l).continuousAt.continuousWithinAt
  -- the prelimit right-hand sides are continuous on the window
  have hcontRHS : ∀ n, ContinuousOn
      (fun s => (-(ν * ‖freq k‖ ^ 2)) • F n s k
        + lerayProj k (convGal (S n) (F n s) k)) (Icc (0:ℝ) T) := by
    intro n
    have h2 : ContinuousOn (fun s => lerayProj k (convGal (S n) (F n s) k))
        (Icc (0:ℝ) T) :=
      (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convGal (fun l => hcontMode n l) k)
    exact ((hcontMode n k).const_smul _).add h2
  -- prelimit integral equations at the fixed time t
  have hpre : ∀ n, F n t k = F n 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k)) := by
    intro n
    exact integral_eq_of_hasDerivAt_Icc hT (fun s hs => hODE n s hs k) (hcontRHS n) t ht
  -- the integration interval sits inside the window
  have hsubset : uIoc (0:ℝ) t ⊆ Icc (0:ℝ) T := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
  -- dominated convergence of the prelimit integrals to the full-convection one
  have hlim_int : Filter.Tendsto
      (fun n => ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • F n s k + lerayProj k (convGal (S n) (F n s) k)))
      Filter.atTop
      (nhds (∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • g s k + lerayProj k (convFull (g s) k)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ν * ‖freq k‖ ^ 2 * Real.sqrt E + 2 * (Real.sqrt E * Real.sqrt Z))
      (Filter.Eventually.of_forall fun n =>
        ((hcontRHS n).mono hsubset).aestronglyMeasurable measurableSet_uIoc)
      (Filter.Eventually.of_forall fun n =>
        Filter.Eventually.of_forall fun s hs =>
          galRHS_norm_le hν hE0 hZ0 (hsupp n s) (hEn n s (hsubset hs))
            (hZn n s (hsubset hs)) k)
      _root_.intervalIntegrable_const
      (Filter.Eventually.of_forall fun s hs => ?_)
    -- pointwise limit of the integrands at s ∈ uIoc 0 t
    have hsIcc : s ∈ Icc (0:ℝ) T := hsubset hs
    have hpt : ∀ l, Filter.Tendsto (fun n => F n s l) Filter.atTop (nhds (g s l)) :=
      fun l => (hu l).tendsto_at hsIcc
    have hEnF : ∀ n (Fs : Finset (Fin 3 → ℤ)), ∑ l ∈ Fs, ‖F n s l‖ ^ 2 ≤ E :=
      fun n Fs => (sum_sq_le_en (hsupp n s) Fs).trans (hEn n s hsIcc)
    have hZnF : ∀ n (Fs : Finset (Fin 3 → ℤ)),
        ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖F n s l‖ ^ 2 ≤ Z :=
      fun n Fs => (sum_wsq_le_ens (hsupp n s) Fs).trans (hZn n s hsIcc)
    have hconv : Filter.Tendsto (fun n => lerayProj k (convFull (F n s) k))
        Filter.atTop (nhds (lerayProj k (convFull (g s) k))) :=
      ((lerayProj_continuous k).tendsto _).comp
        (tendsto_convFull_of_modes hE0 hZ0 hEnF hZnF hpt k)
    have heq : (fun n => lerayProj k (convFull (F n s) k)) =ᶠ[Filter.atTop]
        (fun n => lerayProj k (convGal (S n) (F n s) k)) :=
      (hbox k hk).mono fun n hmem =>
        congrArg (lerayProj k) (convFull_eq_convGal (hsupp n s) hmem)
    exact ((hpt k).const_smul _).add (hconv.congr' heq)
  -- take the limit of the prelimit integral equations
  have hL1 : Filter.Tendsto (fun n => F n t k) Filter.atTop (nhds (g t k)) :=
    (hu k).tendsto_at ht
  have hL0 : Filter.Tendsto (fun n => F n 0 k) Filter.atTop (nhds (g 0 k)) :=
    (hu k).tendsto_at (Set.mem_Icc.mpr ⟨le_refl (0:ℝ), hT⟩)
  have hL2 : Filter.Tendsto (fun n => F n t k) Filter.atTop
      (nhds (g 0 k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • g s k + lerayProj k (convFull (g s) k)))) :=
    (hL0.add hlim_int).congr fun n => (hpre n).symm
  exact tendsto_nhds_unique hL1 hL2

/-- The Galerkin exhaustion family: for every box radius `R` and horizon `T`,
a Galerkin flow on `boxS R` starting from the truncated datum, trapped by the
ORIGINAL datum's energy and enstrophy (uniformly in `R`). -/
theorem galerkin_family : ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν →
    ∀ {c₀ : (Fin 3 → ℤ) → Vel},
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
        κ * en (c t) * ens (c t) < ν ^ 4) := by
  obtain ⟨κ, hκ, hwp⟩ := ns_galerkin_global_wellposed
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hreal hdiv h0 R T
  have hen_tr : en (truncate (boxS R) c₀) ≤ en c₀ := en_truncate_le hE _
  have hens_tr : ens (truncate (boxS R) c₀) ≤ ens c₀ := ens_truncate_le hZ _
  have hen_tr0 : 0 ≤ en (truncate (boxS R) c₀) := tsum_nonneg fun l => sq_nonneg _
  have hens_tr0 : 0 ≤ ens (truncate (boxS R) c₀) :=
    tsum_nonneg fun l => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsmall : κ * en (truncate (boxS R) c₀) * ens (truncate (boxS R) c₀) < ν ^ 4 := by
    have h1 : κ * en (truncate (boxS R) c₀) * ens (truncate (boxS R) c₀) ≤
        κ * en c₀ * ens c₀ := by
      have ha : κ * en (truncate (boxS R) c₀) ≤ κ * en c₀ :=
        mul_le_mul_of_nonneg_left hen_tr hκ.le
      have hb : κ * en (truncate (boxS R) c₀) * ens (truncate (boxS R) c₀) ≤
          κ * en c₀ * ens (truncate (boxS R) c₀) :=
        mul_le_mul_of_nonneg_right ha hens_tr0
      have hc : κ * en c₀ * ens (truncate (boxS R) c₀) ≤ κ * en c₀ * ens c₀ := by
        refine mul_le_mul_of_nonneg_left hens_tr ?_
        have : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
        positivity
      linarith
    linarith
  obtain ⟨c, hc0, hcs, hcODE, hctrap, _⟩ :=
    hwp hν (boxS_zero_not_mem R) (boxS_symm R)
      (truncate_supp (boxS R) c₀)
      (realField_truncate hreal (boxS_symm R))
      (divFree_truncate hdiv (boxS R)) hsmall T
  refine ⟨c, hc0, hcs, hcODE, ?_⟩
  intro t ht
  obtain ⟨h1, h2, h3⟩ := hctrap t ht
  exact ⟨h1.trans hen_tr, h2.trans hens_tr, h3⟩

/-- **THEOREM B — unconditional small-data existence on every finite horizon
for the full Navier-Stokes coefficient system on `ℤ³`.** There is a universal
constant `κ > 0` such that for every viscosity `ν > 0` and every mean-zero,
real, divergence-free initial coefficient field with finite energy `E₀` and
enstrophy `Z₀` satisfying `κ·E₀·Z₀ < ν⁴`: on every horizon `[0, T]` there is
a coefficient flow which starts at the datum, is real and divergence-free
throughout, has genuinely summable energy and enstrophy series at every time
of the window (exported explicitly, so every `tsum` in this statement — the
trap bounds AND the convection inside the integral equation — is an honest
sum, never the junk value of a divergent series), satisfies the FULL
(infinite-convolution) Navier-Stokes integral equation at every time of the
closed window and the differential equation at every interior time, and
stays trapped — energy and enstrophy never exceed their initial values and
the strict smallness inequality survives. PER-HORIZON: the witness flow may
depend on `T`; uniqueness for the full system — and with it a single eternal
flow — is deliberately not claimed here. Obtained as the Galerkin
box-exhaustion limit of the M5 flows: uniform trap bounds feed a
product-space Arzela-Ascoli extraction, dominated convergence passes each
mode's integral equation to the limit, and the zero mode's equation holds
because divergence-freeness survives the limit and annihilates the zero-mode
convection. -/
theorem theorem_B :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) := by
  obtain ⟨κ, hκ, hfam⟩ := galerkin_family
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0 T hT
  have hE₀0 : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
  have hZ₀0 : 0 ≤ ens c₀ := tsum_nonneg fun l => by positivity
  -- the exhaustion family on this horizon
  have hfamI : ∀ R : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = truncate (boxS R) c₀ ∧
      (∀ (t : ℝ) k, k ∉ boxS R → c t k = 0) ∧
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k +
          lerayProj k (convGal (boxS R) (c t) k)) t) ∧
      (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
        κ * en (c t) * ens (c t) < ν ^ 4) :=
    fun R => hfam hν hE hZ hreal hdiv h0 R T
  choose F hF0 hFs hFODE hFtrap using hfamI
  -- every mode curve lives in the Arzela-Ascoli candidate set
  have hmm : ∀ (R : ℕ) (k : Fin 3 → ℤ),
      ∃ f : C(Set.Icc (0:ℝ) T, Vel), (∀ t : Set.Icc (0:ℝ) T, f t = F R t.val k) ∧
        f ∈ modeSet T (Real.sqrt (en c₀))
          (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt (en c₀) +
            2 * (Real.sqrt (en c₀) * Real.sqrt (ens c₀)))) :=
    fun R k => flow_mode_mem_modeSet hν.le hE₀0 hZ₀0 (hFs R) (hFODE R)
      (fun t ht => (hFtrap R t ht).1) (fun t ht => (hFtrap R t ht).2.1) k
  choose u hueq humem using hmm
  -- ONE subsequence for all modes
  obtain ⟨f, hfmem, φ, hφ, hconv⟩ := mode_extraction T (Real.sqrt (en c₀))
    (fun k => Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt (en c₀) +
      2 * (Real.sqrt (en c₀) * Real.sqrt (ens c₀)))) u (fun R k => humem R k)
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
  -- structure of the prelimit flows
  have hFdiv : ∀ R, ∀ t ∈ Icc (0:ℝ) T, DivFree (F R t) := fun R =>
    divFree_propagates_on hν.le (hFODE R)
      (by rw [hF0]; exact divFree_truncate hdiv _)
  have hFreal : ∀ R, ∀ t ∈ Icc (0:ℝ) T, RealField (F R t) := fun R =>
    realField_propagates_on hν.le (boxS_symm R)
      (fun t _ k hk => hFs R t k hk) (hFODE R)
      (by rw [hF0]; exact realField_truncate hreal (boxS_symm R))
  -- structure of the limit
  have hcdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) := fun t ht =>
    divFree_limit (fun n => hFdiv (φ n) t ht) (fun l => hpt t ht l)
  have hcreal : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) := fun t ht =>
    realField_limit (fun n => hFreal (φ n) t ht) (fun l => hpt t ht l)
  -- bounds in the limit
  have hEnF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖F (φ n) t l‖ ^ 2 ≤ en c₀ := fun t ht n Fs =>
    (sum_sq_le_en (fun k hk => hFs (φ n) t k hk) Fs).trans (hFtrap (φ n) t ht).1
  have hZnF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖F (φ n) t l‖ ^ 2 ≤ ens c₀ := fun t ht n Fs =>
    (sum_wsq_le_ens (fun k hk => hFs (φ n) t k hk) Fs).trans (hFtrap (φ n) t ht).2.1
  have hcen : ∀ t ∈ Icc (0:ℝ) T,
      en (c t) ≤ en c₀ ∧ Summable fun l => ‖c t l‖ ^ 2 := fun t ht =>
    en_limit_le (fun n Fs => hEnF t ht n Fs) (fun l => hpt t ht l)
  have hcens : ∀ t ∈ Icc (0:ℝ) T,
      ens (c t) ≤ ens c₀ ∧ Summable fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 := fun t ht =>
    ens_limit_le (fun n Fs => hZnF t ht n Fs) (fun l => hpt t ht l)
  have htrap : ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
      κ * en (c t) * ens (c t) < ν ^ 4 := by
    intro t ht
    obtain ⟨h1, _⟩ := hcen t ht
    obtain ⟨h2, _⟩ := hcens t ht
    refine ⟨h1, h2, ?_⟩
    have hcen0 : 0 ≤ en (c t) := tsum_nonneg fun l => sq_nonneg _
    have hcens0 : 0 ≤ ens (c t) := tsum_nonneg fun l => by positivity
    have ha : κ * en (c t) * ens (c t) ≤ κ * en c₀ * ens (c t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hκ.le) hcens0
    have hb : κ * en c₀ * ens (c t) ≤ κ * en c₀ * ens c₀ := by
      refine mul_le_mul_of_nonneg_left h2 ?_
      positivity
    linarith
  -- mode continuity of the limit
  have hccont : ∀ l, ContinuousOn (fun s => c s l) (Icc (0:ℝ) T) := by
    intro l
    have h1 : Continuous fun s => c s l := by
      show Continuous fun s => Set.IccExtend hT (⇑(f l)) s
      exact (f l).continuous.comp continuous_projIcc
    exact h1.continuousOn
  -- finite-sum bounds for the limit (feeding FLEET-C continuity)
  have hEnLim : ∀ t ∈ Icc (0:ℝ) T, ∀ (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖c t l‖ ^ 2 ≤ en c₀ := fun t ht Fs =>
    ((hcen t ht).2.sum_le_tsum Fs (fun l _ => sq_nonneg _)).trans (hcen t ht).1
  have hZnLim : ∀ t ∈ Icc (0:ℝ) T, ∀ (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 ≤ ens c₀ := fun t ht Fs =>
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
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) := by
    intro t ht k
    by_cases hk0 : k = (0 : Fin 3 → ℤ)
    · subst hk0
      have hint : (fun s => (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
          lerayProj 0 (convFull (c s) 0)) = fun _ => (0 : Vel) := by
        funext s
        have hdivs : DivFree (c s) := by
          rw [hclamp s]
          exact hcdiv _ (Set.projIcc 0 T hT s).2
        rw [hczero s, smul_zero, convFull_zero_of_divFree hdivs, hP0 0, add_zero]
      rw [hczero t, hmean, hint]
      simp
    · have h := integral_equation_limit hν.le hE₀0 hZ₀0 hT
        (S := fun n => boxS (φ n)) (F := fun n => F (φ n)) (g := c)
        (fun n t' k' hk' => hFs (φ n) t' k' hk')
        (fun n => hFODE (φ n))
        (fun n t' ht' => (hFtrap (φ n) t' ht').1)
        (fun n t' ht' => (hFtrap (φ n) t' ht').2.1)
        (fun k' hk' => by
          obtain ⟨R₀, hR₀⟩ := exists_boxS k' hk'
          exact Filter.eventually_atTop.mpr
            ⟨R₀, fun n hn => hR₀ (φ n) (hn.trans hφ.le_apply)⟩)
        hu t ht k hk0
      rw [h, hc0]
  -- continuity of the limit right-hand side
  have hgcont : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k +
      lerayProj k (convFull (c s) k)) (Icc (0:ℝ) T) := by
    intro k
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.smul (hccont k)
    · exact (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE₀0 hZ₀0 hEnLim hZnLim hccont k)
  -- the derivative on the interior
  have hderiv : ∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t := by
    intro t ht k
    refine hasDerivAt_of_integral_eq (hgcont k) ?_ t ht
    intro t' ht'
    show c t' k = c 0 k + ∫ s in (0:ℝ)..t',
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))
    rw [hc0]
    exact hinteq t' ht' k
  exact ⟨c, hc0, fun t ht => ⟨hcreal t ht, hcdiv t ht⟩,
    fun t ht => ⟨(hcen t ht).2, (hcens t ht).2⟩, hinteq, hderiv, htrap⟩

end TheoremB
