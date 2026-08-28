/-
# Uniqueness and the eternal flow (Tier 4 summit)

The constant-source Gronwall, the continuity-strengthened Theorem B, the
unconditional uniqueness theorem for the full Navier-Stokes coefficient
system in the enstrophy-bounded class, and the eternal flow.
-/
import TheoremB.PairingBound
import TheoremB.TailBounds

namespace TheoremB

open Set

/-- Constant-source Gronwall on a window, endpoint-free: continuity on the
closed window, a derivative bound only on the open interior, zero initial
value, and `f' ≤ K·f + A` give `f ≤ (A/K)·e^{KT}` throughout. -/
theorem gronwall_const_source {f : ℝ → ℝ} {K A T : ℝ} (hK : 0 < K) (hA : 0 ≤ A)
    (hcont : ContinuousOn f (Icc 0 T)) (hf0 : f 0 = 0)
    (hderiv : ∀ t ∈ Ioo (0:ℝ) T, ∃ f', HasDerivAt f f' t ∧ f' ≤ K * f t + A) :
    ∀ t ∈ Icc (0:ℝ) T, f t ≤ A / K * Real.exp (K * T) := by
  intro t ht
  by_cases hT0 : T ≤ 0
  · have ht0 : t = 0 := le_antisymm (ht.2.trans hT0) ht.1
    rw [ht0, hf0]
    positivity
  · push_neg at hT0
    -- the exponential-factor auxiliary
    set g : ℝ → ℝ := fun s => (f s + A / K) * Real.exp (-(K * s)) with hg
    have hgd : ∀ s ∈ Ioo (0:ℝ) t, HasDerivAt g
        ((deriv f s - K * f s - A) * Real.exp (-(K * s))) s ∧
        deriv f s ≤ K * f s + A := by
      intro s hs
      have hsT : s ∈ Ioo (0:ℝ) T := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
      obtain ⟨f', hf', hle⟩ := hderiv s hsT
      have hde : deriv f s = f' := hf'.deriv
      constructor
      · have h1 : HasDerivAt (fun u => f u + A / K) f' s := hf'.add_const _
        have h2 : HasDerivAt (fun u => Real.exp (-(K * u)))
            (Real.exp (-(K * s)) * (-K)) s := by
          have h3 : HasDerivAt (fun u : ℝ => -(K * u)) (-K) s := by
            have h : HasDerivAt (fun u : ℝ => (-K) * u) (-K) s := by
              simpa using (hasDerivAt_id s).const_mul (-K)
            refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
            ring
          exact (Real.hasDerivAt_exp _).comp s h3
        have h4 := h1.mul h2
        have h5 : f' * Real.exp (-(K * s)) +
            (f s + A / K) * (Real.exp (-(K * s)) * (-K)) =
            (deriv f s - K * f s - A) * Real.exp (-(K * s)) := by
          rw [hde]
          field_simp
          ring
        rw [← h5]
        exact h4
      · rw [hde]; exact hle
    have hgc : ContinuousOn g (Icc 0 t) := by
      refine ContinuousOn.mul ?_ ?_
      · exact (hcont.mono (Icc_subset_Icc le_rfl ht.2)).add continuousOn_const
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
          ).continuousOn
    have hgdiff : DifferentiableOn ℝ g (Ioo 0 t) := fun s hs =>
      ((hgd s hs).1.differentiableAt).differentiableWithinAt
    have hgderiv : ∀ s ∈ Ioo (0:ℝ) t, deriv g s ≤ 0 := by
      intro s hs
      obtain ⟨hgds, hle⟩ := hgd s hs
      rw [hgds.deriv]
      have hexp : 0 < Real.exp (-(K * s)) := Real.exp_pos _
      nlinarith
    have hmono := le_of_deriv_nonpos ht.1 hgc hgdiff hgderiv
    -- g t ≤ g 0 = A/K
    have hg0 : g 0 = A / K := by
      rw [hg]
      simp [hf0]
    rw [hg0] at hmono
    -- unfold and rearrange
    have hgt : (f t + A / K) * Real.exp (-(K * t)) ≤ A / K := hmono
    have hexp_pos : 0 < Real.exp (-(K * t)) := Real.exp_pos _
    have hme : Real.exp (-(K * t)) * Real.exp (K * t) = 1 := by
      rw [← Real.exp_add]
      simp
    have h7 := mul_le_mul_of_nonneg_right hgt (Real.exp_pos (K * t)).le
    have h6 : f t + A / K ≤ A / K * Real.exp (K * t) := by
      calc f t + A / K
          = (f t + A / K) * (Real.exp (-(K * t)) * Real.exp (K * t)) := by
            rw [hme]; ring
        _ = (f t + A / K) * Real.exp (-(K * t)) * Real.exp (K * t) := by ring
        _ ≤ A / K * Real.exp (K * t) := h7
    have h8 : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2, hK])
    have hAK : 0 ≤ A / K := by positivity
    calc f t ≤ A / K * Real.exp (K * t) - A / K := by linarith
      _ ≤ A / K * Real.exp (K * T) := by nlinarith [Real.exp_pos (K * t)]

/-- `theorem_B`, strengthened with the mode-continuity clause: the witness
flow's every mode curve is continuous on the closed window. A NEW stronger
sibling — the frozen `theorem_B` stands untouched; the proof replays the
Tier-3 assembly, which established continuity internally all along. This is
the clause that places the witness inside the Tier-4 uniqueness class. -/
theorem theorem_B_cont :
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
    fun t ht => ⟨(hcen t ht).2, (hcens t ht).2⟩, hccont, hinteq, hderiv, htrap⟩

/-- **The Tier-4 capstone: uniqueness for the full Navier-Stokes coefficient
system, unconditional in the enstrophy-bounded class.** Two flows on `[0, T]`
with the same initial datum, each mode-continuous, with summable energy and
enstrophy series bounded by any budgets `E, Z`, divergence-free, and
satisfying the full-convolution integral equation, agree at every time and
every mode. No smallness, no dissipation hypothesis, and no reality are
assumed. The proof is the finite-section energy method: the section energy's
derivative is exactly `-2nu*ens_F` plus a pairing that the absorbed bound
splits into `nu*ens(d) + K*en(d)`, the dissipation eats the section part,
the Phi-trick Gronwall closes each section with a tail source, and the
sources vanish along the box exhaustion because the class's summability
hypotheses (supplied for the canonical witness by `theorem_B`'s exported
certificates) make every tail an honest convergent series. -/
theorem theorem_B_unique :
    ∀ {ν E Z T : ℝ}, 0 < ν → 0 ≤ T →
    ∀ {c₀ : (Fin 3 → ℤ) → Vel} {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel},
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
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k))) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) →
    ∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₂ t k := by
  intro ν E Z T hν hT c₀ c₁ c₂ h10 h20 h1cont h2cont h1sum h2sum h1b h2b
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
  -- the continuous right-hand sides
  have h1g : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c₁ s k +
      lerayProj k (convFull (c₁ s) k)) (Icc (0:ℝ) T) := fun k =>
    (continuousOn_const.smul (h1cont k)).add
      ((lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h1enF h1ensF h1cont k))
  have h2g : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c₂ s k +
      lerayProj k (convFull (c₂ s) k)) (Icc (0:ℝ) T) := fun k =>
    (continuousOn_const.smul (h2cont k)).add
      ((lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h2enF h2ensF h2cont k))
  -- interior mode ODEs from the integral equations
  have h1ode : ∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₁ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ t k + lerayProj k (convFull (c₁ t) k)) t := by
    intro t ht k
    refine hasDerivAt_of_integral_eq (h1g k) ?_ t ht
    intro t' ht'
    show c₁ t' k = c₁ 0 k + _
    rw [h10]
    exact h1eq t' ht' k
  have h2ode : ∀ t ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun s => c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ t k + lerayProj k (convFull (c₂ t) k)) t := by
    intro t ht k
    refine hasDerivAt_of_integral_eq (h2g k) ?_ t ht
    intro t' ht'
    show c₂ t' k = c₂ 0 k + _
    rw [h20]
    exact h2eq t' ht' k
  -- zero-mode constancy of both flows
  have hfreq0 : freq (0 : Fin 3 → ℤ) = 0 := by
    have h := freq_sub 0 0
    simpa using h
  have hzero : ∀ c : ℝ → (Fin 3 → ℤ) → Vel,
      (∀ t ∈ Icc (0:ℝ) T, DivFree (c t)) →
      (∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) →
      ∀ t ∈ Icc (0:ℝ) T, c t 0 = c₀ 0 := by
    intro c hdiv heq t ht
    have h1 := heq t ht 0
    have h2 : ∀ s ∈ uIcc (0:ℝ) t,
        ((-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0 +
          lerayProj 0 (convFull (c s) 0)) = 0 := by
      intro s hs
      have hsIcc : s ∈ Icc (0:ℝ) T := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      rw [hfreq0]
      simp only [norm_zero]
      rw [convFull_zero_of_divFree (hdiv s hsIcc)]
      have hP0 : lerayProj 0 (0 : Vel) = 0 := by
        have h := lerayProj_sub 0 (0 : Vel) 0
        rw [sub_self, sub_self] at h
        exact h
      rw [hP0, add_zero]
      norm_num
    rw [intervalIntegral.integral_congr h2] at h1
    simpa using h1
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
  -- the section-energy derivative formula
  set g : ℕ → ℝ → ℝ := fun R s => ∑ k ∈ insert 0 (boxS R),
    2 * inner ℝ (c₁ s k - c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k) +
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k))) with hgdef
  have hφderiv : ∀ R, ∀ s ∈ Ioo (0:ℝ) T, HasDerivAt (φ R) (g R s) s := by
    intro R s hs
    refine hasDerivAt_finset_sum_sq _ fun k _ => ?_
    have h1 := h1ode s hs k
    have h2 := h2ode s hs k
    have h3 := h1.sub h2
    have h4 : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k)) -
        ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k)) =
        (-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k) +
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) := by
      rw [smul_sub]
      abel
    rw [h4] at h3
    exact h3
  have hgcont : ∀ R, ContinuousOn (g R) (Icc (0:ℝ) T) := by
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
      g R s ≤ K * φ R s + (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2)) := by
    intro R hR s hs
    have hsIcc : s ∈ Icc (0:ℝ) T := hs
    -- split the inner product
    have hsplit : g R s = (∑ k ∈ insert 0 (boxS R),
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
    calc g R s ≤ (-2 * ν * ∑ k ∈ insert 0 (boxS R),
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
      IntervalIntegrable (g R) MeasureTheory.volume 0 t' := by
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
  have hftc : ∀ R, ∀ t' ∈ Icc (0:ℝ) T, φ R t' = ∫ s in (0:ℝ)..t', g R s := by
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
    have hmono : (∫ s in (0:ℝ)..t', g R s) ≤
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
    calc φ R t' = ∫ s in (0:ℝ)..t', g R s := hftc R t' ht'
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
  have hnorm : ‖c₁ t k - c₂ t k‖ = 0 := by nlinarith [sq_nonneg ‖c₁ t k - c₂ t k‖, norm_nonneg (c₁ t k - c₂ t k)]
  have hzero' : c₁ t k - c₂ t k = 0 := norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hzero'

/-- **The eternal solution of the full Navier-Stokes coefficient system.**
ONE flow on the half line serving every horizon: it starts at the datum, is
real, divergence-free, with honestly summable energy and enstrophy at every
time, satisfies the full-convolution integral equation at every `t >= 0` and
the differential equation at every `t > 0`, and stays trapped forever.
Built by splicing the per-horizon `theorem_B_cont` witnesses along integer
segments; `theorem_B_unique` makes the splice seamless. Uniqueness of the
eternal flow ITSELF is not part of this statement; but the exported mode
continuity places every restriction of this flow inside the Tier-4
uniqueness class, so any two eternal flows with these clauses agree on
every horizon by `theorem_B_unique`. -/
theorem ns_full_global_flow :
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
        (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
          κ * en (c t) * ens (c t) < ν ^ 4) := by
  obtain ⟨κ, hκ, hB⟩ := theorem_B_cont
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hE hZ hmean hreal hdiv h0
  have hE₀0 : 0 ≤ en c₀ := tsum_nonneg fun l => sq_nonneg _
  have hZ₀0 : 0 ≤ ens c₀ := tsum_nonneg fun l => by positivity
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
        κ * en (c t) * ens (c t) < ν ^ 4) :=
    fun n => hB hν hE hZ hmean hreal hdiv h0 (n:ℝ) (Nat.cast_nonneg n)
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
    have hres : ∀ j : ℕ, ((min m n : ℕ) : ℝ) ≤ (j:ℝ) →
        ∀ P : ∀ t ∈ Icc (0:ℝ) (j:ℝ), Prop, True := fun _ _ _ => trivial
    -- restrict the horizon-j data to the min window
    have hsub : ∀ j : ℕ, ((min m n : ℕ) : ℝ) ≤ (j:ℝ) →
        Icc (0:ℝ) ((min m n : ℕ) : ℝ) ⊆ Icc (0:ℝ) (j:ℝ) :=
      fun j hj => Icc_subset_Icc le_rfl hj
    exact theorem_B_unique (E := en c₀) (Z := ens c₀) hν
      (Nat.cast_nonneg _) (hF0 m) (hF0 n)
      (fun k' => (hFcont m k').mono (hsub m hminm))
      (fun k' => (hFcont n k').mono (hsub n hminn))
      (fun t ht => hFsum m t (hsub m hminm ht))
      (fun t ht => hFsum n t (hsub n hminn ht))
      (fun t ht => ⟨(hFtrap m t (hsub m hminm ht)).1, (hFtrap m t (hsub m hminm ht)).2.1⟩)
      (fun t ht => ⟨(hFtrap n t (hsub n hminn ht)).1, (hFtrap n t (hsub n hminn ht)).2.1⟩)
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
    have hvt : c t k = F N t k := hval t ht.le N htN.le k
    have hvt' : c t = F N t := funext fun j => hval t ht.le N htN.le j
    rw [hvt']
    exact hode.congr_of_eventuallyEq hev
  · -- the trap
    intro t ht
    exact hFtrap (nseg t) t ⟨ht, hseg_ge t ht⟩

end TheoremB
