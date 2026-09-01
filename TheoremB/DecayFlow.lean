/-
# Ambient decay for the eternal flow (Tier 7, wave W-R0b, step 2)

Route (α). The energy pairing vanishes EXACTLY at the Galerkin level
(`convGal_energy_pairing`, a finite sum), so `galerkin_family_decay`
gives every member of the exhaustion the bound
`en (F_R t) ≤ en c₀ · exp(−2νt)`, UNIFORMLY in the box radius. A uniform
per-time energy budget is precisely what `en_limit_le` carries through
the Tier-3 extraction — the same Fatou step that already carries the
trap. So the decay reaches the limit flow with no new analysis, and in
particular with no ℓ¹ hypothesis anywhere.

This is why routes (β) and (γ) were the wrong problem: the full-level
identity `convFull_energy_pairing`, which does need ℓ¹, is never used.

`theorem_B_decay_cont` replays `theorem_B_cont` (FullUnique.lean:100-312)
with the extra clause threaded through; `ns_full_global_flow_decay` then
identifies the witness with the eternal flow by `theorem_B_unique`, the
`ns_full_global_flow_sobolev` pattern.
-/
import TheoremB.FullUnique
import TheoremB.GalerkinDecay

namespace TheoremB

open Set

/-- **`theorem_B_cont` with the decay clause.** Same witness class, plus
`en (c t) ≤ en c₀ · exp(−2νt)` on the window. -/
theorem theorem_B_decay_cont :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ T : ℝ, 0 ≤ T → ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
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
        (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ * Real.exp (-(2 * ν * t))) := by
  obtain ⟨κ, hκ, hfam⟩ := galerkin_family_decay
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0 T hT
  have hE₀0 : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
  have hZ₀0 : 0 ≤ ens c₀ := tsum_nonneg fun l => by positivity
  have hfamI : ∀ R : ℕ, ∃ c : ℝ → (Fin 3 → ℤ) → Vel,
      c 0 = truncate (boxS R) c₀ ∧
      (∀ (t : ℝ) k, k ∉ boxS R → c t k = 0) ∧
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k +
          lerayProj k (convGal (boxS R) (c t) k)) t) ∧
      (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
        κ * en (c t) * ens (c t) < ν ^ 4) ∧
      (∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ * Real.exp (-(2 * ν * t))) :=
    fun R => hfam hν hE hZ hreal hdiv h0 R T
  choose F hF0 hFs hFODE hFtrap hFdec using hfamI
  have hmm : ∀ (R : ℕ) (k : Fin 3 → ℤ),
      ∃ f : C(Set.Icc (0:ℝ) T, Vel), (∀ t : Set.Icc (0:ℝ) T, f t = F R t.val k) ∧
        f ∈ modeSet T (Real.sqrt (en c₀))
          (Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt (en c₀) +
            2 * (Real.sqrt (en c₀) * Real.sqrt (ens c₀)))) :=
    fun R k => flow_mode_mem_modeSet hν.le hE₀0 hZ₀0 (hFs R) (hFODE R)
      (fun t ht => (hFtrap R t ht).1) (fun t ht => (hFtrap R t ht).2.1) k
  choose u hueq humem using hmm
  obtain ⟨f, hfmem, φ, hφ, hconv⟩ := mode_extraction T (Real.sqrt (en c₀))
    (fun k => Real.toNNReal (ν * ‖freq k‖ ^ 2 * Real.sqrt (en c₀) +
      2 * (Real.sqrt (en c₀) * Real.sqrt (ens c₀)))) u (fun R k => humem R k)
  set c : ℝ → (Fin 3 → ℤ) → Vel :=
    fun t k => Set.IccExtend hT (⇑(f k)) t with hcdef
  have hc_mem : ∀ (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (k : Fin 3 → ℤ),
      c t k = f k ⟨t, ht⟩ := fun t ht k => Set.IccExtend_of_mem hT (⇑(f k)) ht
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
  have hclamp : ∀ s : ℝ, c s = c (Set.projIcc 0 T hT s).val := by
    intro s
    funext k
    show Set.IccExtend hT (⇑(f k)) s = c (Set.projIcc 0 T hT s).val k
    rw [hc_mem _ (Set.projIcc 0 T hT s).2 k]
    rfl
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
  have hFdiv : ∀ R, ∀ t ∈ Icc (0:ℝ) T, DivFree (F R t) := fun R =>
    divFree_propagates_on hν.le (hFODE R)
      (by rw [hF0]; exact divFree_truncate hdiv _)
  have hFreal : ∀ R, ∀ t ∈ Icc (0:ℝ) T, RealField (F R t) := fun R =>
    realField_propagates_on hν.le (boxS_symm R)
      (fun t _ k hk => hFs R t k hk) (hFODE R)
      (by rw [hF0]; exact realField_truncate hreal (boxS_symm R))
  have hcdiv : ∀ t ∈ Icc (0:ℝ) T, DivFree (c t) := fun t ht =>
    divFree_limit (fun n => hFdiv (φ n) t ht) (fun l => hpt t ht l)
  have hcreal : ∀ t ∈ Icc (0:ℝ) T, RealField (c t) := fun t ht =>
    realField_limit (fun n => hFreal (φ n) t ht) (fun l => hpt t ht l)
  have hEnF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖F (φ n) t l‖ ^ 2 ≤ en c₀ := fun t ht n Fs =>
    (sum_sq_le_en (fun k hk => hFs (φ n) t k hk) Fs).trans (hFtrap (φ n) t ht).1
  have hZnF : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖F (φ n) t l‖ ^ 2 ≤ ens c₀ := fun t ht n Fs =>
    (sum_wsq_le_ens (fun k hk => hFs (φ n) t k hk) Fs).trans (hFtrap (φ n) t ht).2.1
  -- THE NEW STEP: the same Fatou, at the decaying budget
  have hEnFdec : ∀ t ∈ Icc (0:ℝ) T, ∀ n (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖F (φ n) t l‖ ^ 2 ≤ en c₀ * Real.exp (-(2 * ν * t)) :=
    fun t ht n Fs =>
      (sum_sq_le_en (fun k hk => hFs (φ n) t k hk) Fs).trans (hFdec (φ n) t ht)
  have hcdec : ∀ t ∈ Icc (0:ℝ) T, en (c t) ≤ en c₀ * Real.exp (-(2 * ν * t)) :=
    fun t ht => (en_limit_le (fun n Fs => hEnFdec t ht n Fs) (fun l => hpt t ht l)).1
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
  have hccont : ∀ l, ContinuousOn (fun s => c s l) (Icc (0:ℝ) T) := by
    intro l
    have h1 : Continuous fun s => c s l := by
      show Continuous fun s => Set.IccExtend hT (⇑(f l)) s
      exact (f l).continuous.comp continuous_projIcc
    exact h1.continuousOn
  have hEnLim : ∀ t ∈ Icc (0:ℝ) T, ∀ (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖c t l‖ ^ 2 ≤ en c₀ := fun t ht Fs =>
    ((hcen t ht).2.sum_le_tsum Fs (fun l _ => sq_nonneg _)).trans (hcen t ht).1
  have hZnLim : ∀ t ∈ Icc (0:ℝ) T, ∀ (Fs : Finset (Fin 3 → ℤ)),
      ∑ l ∈ Fs, ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 ≤ ens c₀ := fun t ht Fs =>
    ((hcens t ht).2.sum_le_tsum Fs (fun l _ => by positivity)).trans (hcens t ht).1
  have hP0 : ∀ k : Fin 3 → ℤ, lerayProj k 0 = 0 := by
    intro k
    have h : lerayProj k ((0:Vel) - 0) = lerayProj k 0 - lerayProj k 0 :=
      lerayProj_sub k 0 0
    rw [sub_self, sub_self] at h
    exact h
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
  have hgcont : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k +
      lerayProj k (convFull (c s) k)) (Icc (0:ℝ) T) := by
    intro k
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.smul (hccont k)
    · exact (lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE₀0 hZ₀0 hEnLim hZnLim hccont k)
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
    fun t ht => ⟨(hcen t ht).2, (hcens t ht).2⟩, hccont, hinteq, hderiv, htrap, hcdec⟩

/-- **W-R0b, the capstone: the eternal flow decays at least at rate `2ν`.**

The flow of `ns_full_global_flow`, with its clauses quoted, additionally
satisfies `en (c t) ≤ en c₀ · exp(−2νt)` for every `t ≥ 0`.

What is compiled is the UPPER bound. Its sharpness — that `2ν` is
attained — is true on paper (a single-mode datum `±k₁` with `|k₁| = 1`
and amplitude `a ⊥ k₁` has `convFull ≡ 0`, so `c(t) = e^{−νt}c₀` exactly,
and it sits in the trap class for small amplitude) but is NOT a compiled
statement of this campaign (2 Sep 2026 audit, minor).

Obtained per-time: on the horizon `[0, t]`, `theorem_B_decay_cont`'s
witness carries the decay and inhabits the Tier-4 uniqueness class, so
`theorem_B_unique` pins it to the eternal flow and the clause transfers.
The smallness constant is `max` of the two tiers' constants; the
`κ`-smallness clause itself is deliberately not restated here (it is
`ns_full_global_flow`'s, at ITS constant), so no constant is silently
strengthened. -/
theorem ns_full_global_flow_decay :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      Summable (fun l => ‖c₀ l‖ ^ 2) →
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2) →
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
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀) ∧
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ * Real.exp (-(2 * ν * t))) := by
  obtain ⟨κ₁, hκ₁, hEt⟩ := ns_full_global_flow
  obtain ⟨κ₂, hκ₂, hDec⟩ := theorem_B_decay_cont
  refine ⟨max κ₁ κ₂, lt_of_lt_of_le hκ₁ (le_max_left _ _), ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0
  have hE₀0 : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
  have hZ₀0 : 0 ≤ ens c₀ := tsum_nonneg fun l => by positivity
  have h1 : κ₁ * en c₀ * ens c₀ < ν ^ 4 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left κ₁ κ₂) hE₀0) hZ₀0) h0
  have h2 : κ₂ * en c₀ * ens c₀ < ν ^ 4 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right κ₁ κ₂) hE₀0) hZ₀0) h0
  obtain ⟨c, hc0, hstr, hsum, hcont, hinteq, hode, htrap⟩ :=
    hEt hν hE hZ hmean hreal hdiv h1
  refine ⟨c, hc0, hstr, hsum, hcont, hinteq, hode,
    fun t ht => ⟨(htrap t ht).1, (htrap t ht).2.1⟩, ?_⟩
  intro t ht
  have ht0 : (0:ℝ) ≤ t := ht
  have hsubI : Icc (0:ℝ) t ⊆ Ici (0:ℝ) := Icc_subset_Ici_self
  obtain ⟨c', hc'0, hc'str, hc'sum, hc'cont, hc'eq, hc'ode, hc'trap, hc'dec⟩ :=
    hDec hν hE hZ hmean hreal hdiv h2 t ht0
  have hagree := theorem_B_unique (E := en c₀) (Z := ens c₀) hν ht0
    hc0 hc'0
    (fun k => (hcont k).mono hsubI) hc'cont
    (fun s hs => hsum s (hsubI hs)) hc'sum
    (fun s hs => ⟨(htrap s (hsubI hs)).1, (htrap s (hsubI hs)).2.1⟩)
    (fun s hs => ⟨(hc'trap s hs).1, (hc'trap s hs).2.1⟩)
    (fun s hs => (hstr s (hsubI hs)).2)
    (fun s hs => (hc'str s hs).2)
    (fun s hs => hinteq s (hsubI hs))
    hc'eq
    t ⟨ht0, le_rfl⟩
  have heq : c t = c' t := funext hagree
  rw [heq]
  exact hc'dec t ⟨ht0, le_rfl⟩

end TheoremB
