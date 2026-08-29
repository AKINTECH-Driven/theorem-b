/-
# The Sobolev limit passage and the eternal transfer (Tier 6, wave 4)

Route: `theorem_B_sobolev` is a fresh replay of `theorem_B_cont` with two
insertions — (1) the box-free Galerkin Sobolev constant
(`galerkin_sobolev_bound`) obtained BEFORE the horizon, giving every
exhaustion flow the box-uniform bound
`sob m (F R t) ≤ sob m c₀ · (1 + e^{KT})` via `sob_truncate_le`; and
(2) the weighted Fatou (`weighted_limit_le`) carrying that bound and its
level-`m` summability through the mode-wise limit.  Everything else is the
compiled `theorem_B_cont` assembly verbatim.  The transfer
`ns_full_global_flow_sobolev` replays the eternal splice on
`theorem_B_sobolev`'s per-horizon witnesses (so the trap carries THIS κ),
and gets the eternal Sobolev clause by identification: at each `t ≥ 0` a
fresh horizon-`t` witness shares the datum, the budgets `(en c₀, ens c₀)`,
and the Tier-4 uniqueness class, so `theorem_B_unique` pins the splice to
it at time `t` and the endpoint bound `sob m c₀ · (1 + e^{Kt})` transfers
verbatim; `K` is horizon-uniform because `theorem_B_sobolev` exports it
before quantifying over the window.

Junk-tsum discipline: every tsum bound below carries the Summable
certificate it needs — from box support before the limit
(`summable_weighted_of_support`), from `weighted_limit_le` after it.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.SobolevTrap

namespace TheoremB

open Set

/-- **The W4 capstone: Theorem B with Sobolev persistence.** `theorem_B_cont`
strengthened by the level-`m` clause: for level-`m` summable data the witness
flow keeps `sob m (c t) ≤ sob m c₀ · (1 + e^{KT})` with per-time level-`m`
summability, for a constant `K` uniform across horizons (it depends only on
`(ν, m, en c₀, ens c₀)`).  The frozen Tier-6 statement; the proof replays the
Tier-4 assembly with the per-box Sobolev bound and the weighted Fatou
inserted. -/
theorem theorem_B_sobolev :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ (m : ℕ), 1 ≤ m →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ K, 0 < K ∧ ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Icc (0:ℝ) T, RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) T)) ∧
        (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        (∀ t ∈ Icc (0:ℝ) T,
          Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
          sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * T))) := by
  obtain ⟨κ, hκ, hfam⟩ := galerkin_family
  refine ⟨κ, hκ, ?_⟩
  intro ν hν m hm c₀ hE hZ hSm hmean hreal hdiv h0
  have hE₀0 : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
  have hZ₀0 : 0 ≤ ens c₀ := tsum_nonneg fun l => by positivity
  -- W4 insertion (1a): the box-free Sobolev constant, BEFORE the horizon
  obtain ⟨K, hK, hsobG⟩ :=
    galerkin_sobolev_bound hν (en c₀) (ens c₀) hE₀0 hZ₀0 m hm
  refine ⟨K, hK, ?_⟩
  intro T hT
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
  -- W4 insertion (1b): the per-box Sobolev bound, uniform over the box
  have hFsob : ∀ R : ℕ, ∀ t ∈ Icc (0:ℝ) T,
      sob m (F R t) ≤ sob m c₀ * (1 + Real.exp (K * T)) := by
    intro R t ht
    have hdiv0 : DivFree (F R 0) := by
      rw [hF0]
      exact divFree_truncate hdiv _
    have hbud : ∀ s ∈ Icc (0:ℝ) T, en (F R s) ≤ en c₀ ∧ ens (F R s) ≤ ens c₀ :=
      fun s hs => ⟨(hFtrap R s hs).1, (hFtrap R s hs).2.1⟩
    have h1 : sob m (F R t) ≤ sob m (F R 0) * (1 + Real.exp (K * T)) :=
      hsobG (boxS_zero_not_mem R) (hFs R) hdiv0 (hFODE R) hbud t ht
    have h2 : sob m (F R 0) ≤ sob m c₀ := by
      rw [hF0]
      exact sob_truncate_le hSm _
    have hexp : (0:ℝ) ≤ 1 + Real.exp (K * T) := by positivity
    calc sob m (F R t) ≤ sob m (F R 0) * (1 + Real.exp (K * T)) := h1
      _ ≤ sob m c₀ * (1 + Real.exp (K * T)) :=
          mul_le_mul_of_nonneg_right h2 hexp
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
  -- W4 insertion (2): the weighted Fatou — the Sobolev bound and its
  -- summability survive the mode-wise limit
  have hSobF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ (2 * m) * ‖F (φ n) t l‖ ^ 2 ≤
        sob m c₀ * (1 + Real.exp (K * T)) := by
    intro t ht n Fs
    have hsum : Summable fun l => ‖freq l‖ ^ (2 * m) * ‖F (φ n) t l‖ ^ 2 :=
      summable_weighted_of_support (fun l => ‖freq l‖ ^ (2 * m))
        (fun k hk => hFs (φ n) t k hk)
    calc ∑ l ∈ Fs, ‖freq l‖ ^ (2 * m) * ‖F (φ n) t l‖ ^ 2
        ≤ sob m (F (φ n) t) := hsum.sum_le_tsum Fs (fun l _ => by positivity)
      _ ≤ sob m c₀ * (1 + Real.exp (K * T)) := hFsob (φ n) t ht
  have hcsob : ∀ t ∈ Icc (0:ℝ) T,
      (∑' l, ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ≤
        sob m c₀ * (1 + Real.exp (K * T)) ∧
      Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2 := fun t ht =>
    weighted_limit_le (w := fun l => ‖freq l‖ ^ (2 * m)) (fun k => by positivity)
      (fun n Fs => hSobF t ht n Fs) (fun l => hpt t ht l)
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
  -- the level-m clause, in the frozen order (Summable first, bound second)
  have hsobfinal : ∀ t ∈ Icc (0:ℝ) T,
      Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
      sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * T)) := by
    intro t ht
    refine ⟨(hcsob t ht).2, ?_⟩
    have hs : sob m (c t) = ∑' l, ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2 := rfl
    rw [hs]
    exact (hcsob t ht).1
  exact ⟨c, hc0, fun t ht => ⟨hcreal t ht, hcdiv t ht⟩,
    fun t ht => ⟨(hcen t ht).2, (hcens t ht).2⟩, hccont, hinteq, hderiv, htrap,
    hsobfinal⟩

/-- **The eternal Sobolev flow** (the W4 transfer): `ns_full_global_flow`'s
statement with the level-`m` datum summability added and the eternal Sobolev
clause appended — for each fixed `m ≥ 1`, the witness flow keeps every
conclusion of the original and additionally `sob m (c t) ≤ sob m c₀ ·
(1 + e^{Kt})` with per-time level-`m` summability, for a single
horizon-uniform `K`.  (The statement is per-`m`; that all levels hold for
the SAME flow is the meta-corollary through `theorem_B_unique`, which pins
every per-`m` witness to the one canonical flow.)  The splice is rebuilt from
`theorem_B_sobolev`'s per-horizon witnesses (so the trap clause carries THIS
theorem's κ); at each `t ≥ 0` a fresh horizon-`t` witness is identified with
the splice on `Icc 0 t` by `theorem_B_unique` (budgets exactly
`(en c₀, ens c₀)`), and its endpoint bound transfers. -/
theorem ns_full_global_flow_sobolev :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ (m : ℕ), 1 ≤ m →
      ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
        c 0 = c₀ ∧
        (∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
        (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
          Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
        (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
        (∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
          ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) ∧
        (∃ K, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
          Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
          sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * t))) := by
  obtain ⟨κ, hκ, hB⟩ := theorem_B_sobolev
  refine ⟨κ, hκ, ?_⟩
  intro ν hν m hm c₀ hE hZ hSm hmean hreal hdiv h0
  have hE₀0 : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
  have hZ₀0 : 0 ≤ ens c₀ := tsum_nonneg fun l => by positivity
  -- ONE Sobolev constant for this datum, uniform across horizons
  obtain ⟨K, hK, hBT⟩ := hB hν m hm hE hZ hSm hmean hreal hdiv h0
  -- one witness per natural horizon
  have hex : ∀ n : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = c₀ ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), RealField (c t) ∧ DivFree (c t)) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
        Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) ∧
      (∀ k, ContinuousOn (fun s => c s k) (Icc (0:ℝ) (n:ℝ))) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) ∧
      (∀ t ∈ Ioo (0:ℝ) (n:ℝ), ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
        κ * en (c t) * ens (c t) < ν ^ 4) ∧
      (∀ t ∈ Icc (0:ℝ) (n:ℝ),
        Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * (n:ℝ)))) :=
    fun n => hBT (n:ℝ) (Nat.cast_nonneg n)
  choose F hF0 hFstr hFsum hFcont hFeq hFode hFtrap _hFsob using hex
  -- pairwise agreement on overlapping horizons via uniqueness at the min
  have hA : ∀ i j : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ (i:ℝ) → s ≤ (j:ℝ) →
      ∀ k, F i s k = F j s k := by
    intro i j s hs0 hsi hsj k
    have hmini : ((min i j : ℕ) : ℝ) ≤ (i:ℝ) := by exact_mod_cast min_le_left i j
    have hminj : ((min i j : ℕ) : ℝ) ≤ (j:ℝ) := by exact_mod_cast min_le_right i j
    have hsmin : s ≤ ((min i j : ℕ) : ℝ) := by
      rw [Nat.cast_min]
      exact le_min hsi hsj
    -- restrict the horizon data to the min window
    have hsub : ∀ jj : ℕ, ((min i j : ℕ) : ℝ) ≤ (jj:ℝ) →
        Icc (0:ℝ) ((min i j : ℕ) : ℝ) ⊆ Icc (0:ℝ) (jj:ℝ) :=
      fun jj hjj => Icc_subset_Icc le_rfl hjj
    exact theorem_B_unique (E := en c₀) (Z := ens c₀) hν
      (Nat.cast_nonneg _) (hF0 i) (hF0 j)
      (fun k' => (hFcont i k').mono (hsub i hmini))
      (fun k' => (hFcont j k').mono (hsub j hminj))
      (fun t ht => hFsum i t (hsub i hmini ht))
      (fun t ht => hFsum j t (hsub j hminj ht))
      (fun t ht => ⟨(hFtrap i t (hsub i hmini ht)).1, (hFtrap i t (hsub i hmini ht)).2.1⟩)
      (fun t ht => ⟨(hFtrap j t (hsub j hminj ht)).1, (hFtrap j t (hsub j hminj ht)).2.1⟩)
      (fun t ht => (hFstr i t (hsub i hmini ht)).2)
      (fun t ht => (hFstr j t (hsub j hminj ht)).2)
      (fun t ht => hFeq i t (hsub i hmini ht))
      (fun t ht => hFeq j t (hsub j hminj ht))
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
  -- initial value
  have hc0 : c 0 = c₀ := by
    show F (nseg 0) 0 = c₀
    exact hF0 _
  -- structure
  have hcstr : ∀ t ∈ Ici (0:ℝ), RealField (c t) ∧ DivFree (c t) := by
    intro t ht
    have h := hFstr (nseg t) t ⟨ht, hseg_ge t ht⟩
    exact h
  -- summability
  have hcsum : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2) := by
    intro t ht
    exact hFsum (nseg t) t ⟨ht, hseg_ge t ht⟩
  -- mode continuity on the half line
  have hccont : ∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ)) := by
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
  -- the integral equation
  have hceq : ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) := by
    intro t ht k
    have hN : t ≤ ((nseg t : ℕ) : ℝ) := hseg_ge t ht
    have h := hFeq (nseg t) t ⟨ht, hN⟩ k
    -- rewrite the integrand: on [0, t] the splice agrees with F (nseg t)
    have hcong : EqOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k +
        lerayProj k (convFull (c s) k))
        (fun s => (-(ν * ‖freq k‖ ^ 2)) • F (nseg t) s k +
          lerayProj k (convFull (F (nseg t) s) k)) (uIcc (0:ℝ) t) := by
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) t := by rwa [uIcc_of_le ht] at hs
      have hsN : s ≤ ((nseg t : ℕ) : ℝ) := hs'.2.trans hN
      have hfields : c s = F (nseg t) s := funext fun j => hval s hs'.1 _ hsN j
      simp only [hfields]
    rw [show c t k = F (nseg t) t k from hval t ht _ hN k,
      intervalIntegral.integral_congr hcong]
    exact h
  -- the derivative at interior times
  have hcode : ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t := by
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
    have hvt : c t k = F N t k := hval t ht.le N htN.le k
    have hvt' : c t = F N t := funext fun j => hval t ht.le N htN.le j
    rw [hvt']
    exact hode.congr_of_eventuallyEq hev
  -- the trap
  have hctrap : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
      κ * en (c t) * ens (c t) < ν ^ 4 := by
    intro t ht
    exact hFtrap (nseg t) t ⟨ht, hseg_ge t ht⟩
  -- the eternal Sobolev clause: identify with a fresh horizon-t witness
  have hsob : ∀ t : ℝ, 0 ≤ t →
      Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
      sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * t)) := by
    intro t ht
    obtain ⟨d, hd0, hdstr, hdsum, hdcont, hdeq, hdode, hdtrap, hdsob⟩ := hBT t ht
    have hsub : Icc (0:ℝ) t ⊆ Ici (0:ℝ) := Icc_subset_Ici_self
    have huniq := theorem_B_unique (E := en c₀) (Z := ens c₀) hν ht hc0 hd0
      (fun k => (hccont k).mono hsub)
      hdcont
      (fun s hs => hcsum s (hsub hs))
      hdsum
      (fun s hs => ⟨(hctrap s (hsub hs)).1, (hctrap s (hsub hs)).2.1⟩)
      (fun s hs => ⟨(hdtrap s hs).1, (hdtrap s hs).2.1⟩)
      (fun s hs => (hcstr s (hsub hs)).2)
      (fun s hs => (hdstr s hs).2)
      (fun s hs => hceq s (hsub hs))
      hdeq
    have hct : c t = d t := funext (huniq t ⟨ht, le_refl t⟩)
    rw [hct]
    exact hdsob t ⟨ht, le_refl t⟩
  exact ⟨c, hc0, hcstr, hcsum, hccont, hceq, hcode, hctrap, K, hK, hsob⟩

end TheoremB
