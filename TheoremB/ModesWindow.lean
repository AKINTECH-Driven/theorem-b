/-
# The determining-modes window inequality (Tier 7, wave W-R3)

The mathematical content of Tier 7, in one substitution.

`theorem_B_unique` bounds the section-energy derivative of a defect by
`g_R ≤ −2ν·SEC + (ν·ens d + K·en d) = −ν·SEC + ν·σ_R + K·en d` and then
DISCARDS `−ν·SEC` (FullUnique.lean:573, via `hprod2 : 0 ≤ ν * SEC`),
because an additive source that vanishes along the exhaustion is all
uniqueness needs. Here we keep it. If the defect's modes below `N`
carry at most `δ`, every surviving mode of the section has
`‖freq k‖ > N` by `boxS_compl_freq`, so `SEC ≥ N²·(φ_R − δ)` and the
same Gronwall closes with a NEGATIVE rate instead of a vanishing source.

The limit in `R` is taken on the INTEGRATED subwindow inequality, never
inside a derivative - which is what keeps this tier clear of the
a.e.-differentiability machinery the campaign does not have. The output
is a window integral inequality, exactly the shape
`decay_of_window_integral_ineq` consumes.
-/
import TheoremB.FullUnique
import TheoremB.EnergyIntegrable

namespace TheoremB

open Set

/-- The boxes are monotone in the radius. -/
lemma box_subset {m n : ℕ} (h : m ≤ n) :
    insert 0 (boxS m) ⊆ insert 0 (boxS n) := by
  refine Finset.insert_subset_insert _ fun k hk => ?_
  rw [mem_boxS] at hk ⊢
  refine ⟨hk.1, fun i => ?_⟩
  have := hk.2 i
  omega

/-- **W-R3, the determining-modes window inequality.** Two flows in the
enstrophy-bounded class whose defect carries at most `δ` in the modes
below `N` obey, on every subwindow, an energy inequality with rate
`ν·N² − K` and source `ν·N²·δ`.

`K` is obtained from `pairing_absorbed` at the class budgets `(ν, E, Z)`
BEFORE any horizon, tolerance, or flow is chosen: the statement quantifies
`∃ K` ahead of `∀ {T δ}` and `∀ {c₁ c₂}`, exactly as `pairing_absorbed`
quantifies `∃ K` ahead of `∀ {a b}`. So `K` is box-free, horizon-free,
and pair-free - one constant for the whole class, of explicit form up to
the lattice-kernel constant (`kernel_sum_le`), exported as a compiled
existential. No sign condition on `ν·N² − K` is needed here; the
threshold enters only when this is fed to
`decay_of_window_integral_ineq`. -/
theorem modes_window_ineq :
    ∀ {ν E Z : ℝ}, 0 < ν → 0 ≤ E → 0 ≤ Z → ∃ K, 0 < K ∧
    ∀ {T δ : ℝ}, 0 ≤ T → 0 ≤ δ →
    ∀ {c₁ c₂ : ℝ → (Fin 3 → ℤ) → Vel},
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
    (∀ t ∈ Icc (0:ℝ) T, c₁ t 0 = 0) →
    (∀ t ∈ Icc (0:ℝ) T, c₂ t 0 = 0) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₁ t k = c₁ 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k))) →
    (∀ t ∈ Icc (0:ℝ) T, ∀ k, c₂ t k = c₂ 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k))) →
    ∀ N : ℕ, 0 < N →
      (∀ s ∈ Icc (0:ℝ) T,
        (∑ k ∈ insert 0 (boxS N), ‖c₁ s k - c₂ s k‖ ^ 2) ≤ δ) →
      ∀ t₀ ∈ Icc (0:ℝ) T, ∀ t ∈ Icc t₀ T,
        en (fun l => c₁ t l - c₂ t l) +
            (ν * (N:ℝ) ^ 2 - K) *
              (∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l))
          ≤ en (fun l => c₁ t₀ l - c₂ t₀ l) + ν * (N:ℝ) ^ 2 * δ * (t - t₀) := by
  intro ν E Z hν hE0 hZ0
  -- K is fixed HERE, before any horizon, tolerance, or flow is chosen
  obtain ⟨K, hK, hpair⟩ := pairing_absorbed (E := E) (Z := Z) hν hE0 hZ0
  refine ⟨K, hK, ?_⟩
  intro T δ hT hδ c₁ c₂ h1cont h2cont h1sum h2sum h1b h2b
    h1div h2div h1zero h2zero h1eq h2eq N hN hlow t₀ ht₀ t ht
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have ht0T : t ≤ T := ht.2
  have ht₀0 : 0 ≤ t₀ := ht₀.1
  have ht₀t : t₀ ≤ t := ht.1
  -- finite-sum bound forms, for the convection continuity
  have h1enF : ∀ s ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖c₁ s l‖ ^ 2 ≤ E := fun s hs F =>
    ((h1sum s hs).1.sum_le_tsum F (fun l _ => sq_nonneg _)).trans (h1b s hs).1
  have h1ensF : ∀ s ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c₁ s l‖ ^ 2 ≤ Z := fun s hs F =>
    ((h1sum s hs).2.sum_le_tsum F (fun l _ => by positivity)).trans (h1b s hs).2
  have h2enF : ∀ s ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖c₂ s l‖ ^ 2 ≤ E := fun s hs F =>
    ((h2sum s hs).1.sum_le_tsum F (fun l _ => sq_nonneg _)).trans (h2b s hs).1
  have h2ensF : ∀ s ∈ Icc (0:ℝ) T, ∀ (F : Finset (Fin 3 → ℤ)),
      ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c₂ s l‖ ^ 2 ≤ Z := fun s hs F =>
    ((h2sum s hs).2.sum_le_tsum F (fun l _ => by positivity)).trans (h2b s hs).2
  -- continuous right-hand sides, then the interior mode ODEs
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
  have h1ode : ∀ s ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun r => c₁ r k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k)) s := by
    intro s hs k
    exact hasDerivAt_of_integral_eq (h1g k) (fun t' ht' => h1eq t' ht' k) s hs
  have h2ode : ∀ s ∈ Ioo (0:ℝ) T, ∀ k, HasDerivAt (fun r => c₂ r k)
      ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k)) s := by
    intro s hs k
    exact hasDerivAt_of_integral_eq (h2g k) (fun t' ht' => h2eq t' ht' k) s hs
  -- defect facts
  have hdsum : ∀ s ∈ Icc (0:ℝ) T, Summable (fun l => ‖c₁ s l - c₂ s l‖ ^ 2) :=
    fun s hs => summable_sq_sub (h1sum s hs).1 (h2sum s hs).1
  have hdwsum : ∀ s ∈ Icc (0:ℝ) T,
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c₁ s l - c₂ s l‖ ^ 2) :=
    fun s hs => summable_wsq_sub (h1sum s hs).2 (h2sum s hs).2
  have hdens : ∀ s ∈ Icc (0:ℝ) T, ens (fun l => c₁ s l - c₂ s l) ≤ 4 * Z := by
    intro s hs
    have h := ens_sub_le (h1sum s hs).2 (h2sum s hs).2
    linarith [(h1b s hs).2, (h2b s hs).2]
  have hdenE : ∀ s ∈ Icc (0:ℝ) T, en (fun l => c₁ s l - c₂ s l) ≤ 4 * E := by
    intro s hs
    have h := en_sub_le (h1sum s hs).1 (h2sum s hs).1
    linarith [(h1b s hs).1, (h2b s hs).1]
  have hdcont : ∀ k, ContinuousOn (fun s => c₁ s k - c₂ s k) (Icc (0:ℝ) T) :=
    fun k => (h1cont k).sub (h2cont k)
  have hdnn : ∀ s, (0:ℝ) ≤ en (fun l => c₁ s l - c₂ s l) :=
    fun s => tsum_nonneg fun l => sq_nonneg _
  -- the energy history is integrable (W-R2a)
  have hEint0T : IntervalIntegrable (fun s => en (fun l => c₁ s l - c₂ s l))
      MeasureTheory.volume 0 T :=
    intervalIntegrable_en (by positivity) hT hdcont hdsum hdenE
  have hEint : IntervalIntegrable (fun s => en (fun l => c₁ s l - c₂ s l))
      MeasureTheory.volume t₀ t := by
    refine hEint0T.mono_set ?_
    rw [uIcc_of_le ht₀t, uIcc_of_le hT]
    exact Icc_subset_Icc ht₀0 ht0T
  -- sections
  set φ : ℕ → ℝ → ℝ := fun R s => ∑ k ∈ insert 0 (boxS R), ‖c₁ s k - c₂ s k‖ ^ 2
    with hφdef
  set σ : ℕ → ℝ → ℝ := fun R s => ens (fun l => c₁ s l - c₂ s l) -
    ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 with hσdef
  have hσnn : ∀ R, ∀ s ∈ Icc (0:ℝ) T, 0 ≤ σ R s := fun R s hs =>
    tail_nonneg (hdwsum s hs) _
  have hσint : ∀ R, IntervalIntegrable (σ R) MeasureTheory.volume 0 T := fun R =>
    tail_integrable (by positivity) hT hdcont hdwsum hdens _
  have hφcont : ∀ R, ContinuousOn (φ R) (Icc (0:ℝ) T) := fun R =>
    en_sec_contOn hdcont _
  have hφnn : ∀ R s, 0 ≤ φ R s := fun R s => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hφint : ∀ R, IntervalIntegrable (φ R) MeasureTheory.volume t₀ t := fun R =>
    ((hφcont R).mono (by
      rw [uIcc_of_le ht₀t]; exact Icc_subset_Icc ht₀0 ht0T)).intervalIntegrable
  -- the section-energy derivative
  set g : ℕ → ℝ → ℝ := fun R s => ∑ k ∈ insert 0 (boxS R),
    2 * inner ℝ (c₁ s k - c₂ s k)
      ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k) +
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)))
    with hgdef
  have hφderiv : ∀ R, ∀ s ∈ Ioo (0:ℝ) T, HasDerivAt (φ R) (g R s) s := by
    intro R s hs
    refine hasDerivAt_finset_sum_sq _ fun k _ => ?_
    have h3 := (h1ode s hs k).sub (h2ode s hs k)
    have h4 : ((-(ν * ‖freq k‖ ^ 2)) • c₁ s k + lerayProj k (convFull (c₁ s) k)) -
        ((-(ν * ‖freq k‖ ^ 2)) • c₂ s k + lerayProj k (convFull (c₂ s) k)) =
        (-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k) +
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) := by
      rw [smul_sub]; abel
    rw [h4] at h3
    exact h3
  have hgcont : ∀ R, ContinuousOn (g R) (Icc (0:ℝ) T) := by
    intro R
    refine continuousOn_finsetSum _ fun k _ => ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inner (hdcont k) ?_
    refine ContinuousOn.add (continuousOn_const.smul (hdcont k)) ?_
    exact ((lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h1enF h1ensF h1cont k)).sub
      ((lerayProj_continuous k).comp_continuousOn
        (continuousOn_convFull hE0 hZ0 h2enF h2ensF h2cont k))
  have hgint : ∀ R, IntervalIntegrable (g R) MeasureTheory.volume t₀ t := fun R =>
    ((hgcont R).mono (by
      rw [uIcc_of_le ht₀t]; exact Icc_subset_Icc ht₀0 ht0T)).intervalIntegrable
  -- THE SUBSTITUTION: the dissipation is kept, not discarded
  have hgle : ∀ R : ℕ, N ≤ R → ∀ s ∈ Icc (0:ℝ) T,
      g R s ≤ (-(ν * (N:ℝ) ^ 2 - K)) * φ R s +
        (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2) + ν * (N:ℝ) ^ 2 * δ) := by
    intro R hNR' s hs
    have hsplit : g R s = (∑ k ∈ insert 0 (boxS R),
        2 * inner ℝ (c₁ s k - c₂ s k) ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k))) +
        ∑ k ∈ insert 0 (boxS R), 2 * inner ℝ (c₁ s k - c₂ s k)
          (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) := by
      rw [hgdef, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_add_right]; ring
    have hdiss : (∑ k ∈ insert 0 (boxS R),
        2 * inner ℝ (c₁ s k - c₂ s k) ((-(ν * ‖freq k‖ ^ 2)) • (c₁ s k - c₂ s k))) =
        -2 * ν * ∑ k ∈ insert 0 (boxS R),
          ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    have hdivd : ∀ k, dotR (c₁ s k - c₂ s k) (freq k) = 0 := by
      intro k
      rw [dotR_sub_left', h1div s hs k, h2div s hs k, sub_self]
    have hpairpart : (∑ k ∈ insert 0 (boxS R), 2 * inner ℝ (c₁ s k - c₂ s k)
        (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k))) ≤
        ν * ens (fun l => c₁ s l - c₂ s l) + K * en (fun l => c₁ s l - c₂ s l) := by
      have hre : ∀ k, inner ℝ (c₁ s k - c₂ s k)
          (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k)) =
          inner ℝ (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k) := by
        intro k
        rw [← lerayProj_sub, real_inner_comm]
        exact inner_lerayProj_left (hdivd k)
      have hsum' : (∑ k ∈ insert 0 (boxS R), 2 * inner ℝ (c₁ s k - c₂ s k)
          (lerayProj k (convFull (c₁ s) k) - lerayProj k (convFull (c₂ s) k))) =
          ∑ k ∈ insert 0 (boxS R),
            2 * inner ℝ (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k) :=
        Finset.sum_congr rfl fun k _ => by rw [hre k]
      rw [hsum']
      have h0eq : c₁ s 0 = c₂ s 0 := by rw [h1zero s hs, h2zero s hs]
      have habs := hpair (h1sum s hs).1 (h1sum s hs).2 (h2sum s hs).1 (h2sum s hs).2
        (h1b s hs).1 (h1b s hs).2 (h2b s hs).1 (h2b s hs).2 h0eq
        (insert 0 (boxS R))
      have hle := le_abs_self (∑ k ∈ insert 0 (boxS R),
        inner ℝ (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k))
      have hfac : (∑ k ∈ insert 0 (boxS R),
          2 * inner ℝ (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k)) =
          2 * ∑ k ∈ insert 0 (boxS R),
            inner ℝ (convFull (c₁ s) k - convFull (c₂ s) k) (c₁ s k - c₂ s k) := by
        rw [Finset.mul_sum]
      rw [hfac]
      nlinarith [habs, hle]
    -- the Poincare step: every surviving mode of the section is above N
    have hsub : insert 0 (boxS N) ⊆ insert 0 (boxS R) := box_subset hNR'
    have hdiff : ∀ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
        (N:ℝ) ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 ≤
          ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 := by
      intro k hk
      have hkn : k ∉ insert 0 (boxS N) := (Finset.mem_sdiff.mp hk).2
      have hlt := boxS_compl_freq N k hkn
      have : (N:ℝ) ^ 2 ≤ ‖freq k‖ ^ 2 := by nlinarith [norm_nonneg (freq k)]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hsec : (N:ℝ) ^ 2 * (φ R s - δ) ≤
        ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 := by
      have hsplit1 : ∑ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
            ‖c₁ s k - c₂ s k‖ ^ 2
          = φ R s - ∑ k ∈ insert 0 (boxS N), ‖c₁ s k - c₂ s k‖ ^ 2 := by
        rw [hφdef]
        simp only
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff hsub]
      have hmono1 : ∑ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
            (N:ℝ) ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2
          ≤ ∑ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
            ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 :=
        Finset.sum_le_sum hdiff
      have hmono2 : ∑ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
            ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2
          ≤ ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun k _ _ => by positivity)
      have hfac : ∑ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
            (N:ℝ) ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2
          = (N:ℝ) ^ 2 * ∑ k ∈ insert 0 (boxS R) \ insert 0 (boxS N),
            ‖c₁ s k - c₂ s k‖ ^ 2 := by rw [Finset.mul_sum]
      have hlowS := hlow s hs
      have hNsq : (0:ℝ) ≤ (N:ℝ) ^ 2 := by positivity
      nlinarith [hmono1, hmono2, hfac, hsplit1, hlowS, hNsq]
    -- assemble
    have htail := tail_en_lt (Z := 4 * Z) R (lt_of_lt_of_le hN hNR')
      (hdsum s hs) (hdwsum s hs) (hdens s hs)
    have hens_split : ens (fun l => c₁ s l - c₂ s l) =
        (∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2) + σ R s := by
      rw [hσdef]; ring
    have hen_le : en (fun l => c₁ s l - c₂ s l) ≤ φ R s + 4 * Z / (R:ℝ) ^ 2 := by
      rw [hφdef]; simp only; linarith
    calc g R s
        ≤ (-2 * ν * ∑ k ∈ insert 0 (boxS R),
            ‖freq k‖ ^ 2 * ‖c₁ s k - c₂ s k‖ ^ 2) +
            (ν * ens (fun l => c₁ s l - c₂ s l) +
              K * en (fun l => c₁ s l - c₂ s l)) := by
          rw [hsplit, hdiss]; exact add_le_add le_rfl hpairpart
      _ ≤ (-(ν * (N:ℝ) ^ 2 - K)) * φ R s +
            (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2) + ν * (N:ℝ) ^ 2 * δ) := by
          rw [hens_split]
          nlinarith [hsec, hen_le, hK.le, hν.le, hδ]
  -- FTC on the subwindow, then integrate the bound
  have hkey : ∀ R : ℕ, N ≤ R →
      en (fun l => c₁ t l - c₂ t l) +
          (ν * (N:ℝ) ^ 2 - K) * (∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l))
        ≤ en (fun l => c₁ t₀ l - c₂ t₀ l) + ν * (N:ℝ) ^ 2 * δ * (t - t₀) +
          (ν * (∫ s in (0:ℝ)..T, σ R s) +
            (K * (4 * Z / (R:ℝ) ^ 2)) * (t - t₀) +
            4 * Z / (R:ℝ) ^ 2 +
            |ν * (N:ℝ) ^ 2 - K| * (4 * Z / (R:ℝ) ^ 2) * (t - t₀)) := by
    intro R hNR'
    have hRpos : 0 < R := lt_of_lt_of_le hN hNR'
    have hsubw : Icc t₀ t ⊆ Icc (0:ℝ) T := Icc_subset_Icc ht₀0 ht0T
    have htIcc : t ∈ Icc (0:ℝ) T := ⟨le_trans ht₀0 ht₀t, ht0T⟩
    -- FTC
    have hftc : φ R t - φ R t₀ = ∫ s in t₀..t, g R s := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht₀t
        ((hφcont R).mono hsubw)
        (fun s hs => hφderiv R s ⟨lt_of_le_of_lt ht₀0 hs.1, lt_of_lt_of_le hs.2 ht0T⟩)
        (hgint R)
      linarith [h]
    -- integrate the derivative bound
    have hBint : IntervalIntegrable
        (fun s => (-(ν * (N:ℝ) ^ 2 - K)) * φ R s +
          (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2) + ν * (N:ℝ) ^ 2 * δ))
        MeasureTheory.volume t₀ t := by
      refine ((hφint R).const_mul (-(ν * (N:ℝ) ^ 2 - K))).add ?_
      refine ((((hσint R).mono_set (by
        rw [uIcc_of_le ht₀t, uIcc_of_le hT]
        exact Icc_subset_Icc ht₀0 ht0T)).const_mul ν).add
        intervalIntegrable_const).add intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on ht₀t (hgint R) hBint
      (fun s hs => hgle R hNR' s (hsubw hs))
    have hsplitint : (∫ s in t₀..t,
        ((-(ν * (N:ℝ) ^ 2 - K)) * φ R s +
          (ν * σ R s + K * (4 * Z / (R:ℝ) ^ 2) + ν * (N:ℝ) ^ 2 * δ))) =
        (-(ν * (N:ℝ) ^ 2 - K)) * (∫ s in t₀..t, φ R s) +
          (ν * (∫ s in t₀..t, σ R s) +
            K * (4 * Z / (R:ℝ) ^ 2) * (t - t₀) + ν * (N:ℝ) ^ 2 * δ * (t - t₀)) := by
      have hσsub : IntervalIntegrable (σ R) MeasureTheory.volume t₀ t :=
        (hσint R).mono_set (by
          rw [uIcc_of_le ht₀t, uIcc_of_le hT]
          exact Icc_subset_Icc ht₀0 ht0T)
      rw [intervalIntegral.integral_add
          ((hφint R).const_mul (-(ν * (N:ℝ) ^ 2 - K)))
          (((hσsub.const_mul ν).add intervalIntegrable_const).add
            intervalIntegrable_const),
        intervalIntegral.integral_add ((hσsub.const_mul ν).add intervalIntegrable_const)
          intervalIntegrable_const,
        intervalIntegral.integral_add (hσsub.const_mul ν) intervalIntegrable_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
        intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsplitint] at hmono
    -- sandwich the sections against the true energies
    have htailt := tail_en_lt (Z := 4 * Z) R hRpos (hdsum t htIcc)
      (hdwsum t htIcc) (hdens t htIcc)
    have hφt₀le : φ R t₀ ≤ en (fun l => c₁ t₀ l - c₂ t₀ l) := by
      rw [hφdef]
      exact (hdsum t₀ ht₀).sum_le_tsum _ (fun l _ => sq_nonneg _)
    have hφsec : ∀ s ∈ Icc t₀ t, φ R s ≤ en (fun l => c₁ s l - c₂ s l) := by
      intro s hs
      rw [hφdef]
      exact (hdsum s (hsubw hs)).sum_le_tsum _ (fun l _ => sq_nonneg _)
    have hφlow : ∀ s ∈ Icc t₀ t,
        en (fun l => c₁ s l - c₂ s l) - 4 * Z / (R:ℝ) ^ 2 ≤ φ R s := by
      intro s hs
      have h := tail_en_lt (Z := 4 * Z) R hRpos (hdsum s (hsubw hs))
        (hdwsum s (hsubw hs)) (hdens s (hsubw hs))
      rw [hφdef]; simp only; linarith
    -- compare the two integrals
    have hIφ : |(∫ s in t₀..t, φ R s) - ∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l)|
        ≤ 4 * Z / (R:ℝ) ^ 2 * (t - t₀) := by
      have hd1 : (∫ s in t₀..t, φ R s) ≤ ∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l) :=
        intervalIntegral.integral_mono_on ht₀t (hφint R) hEint hφsec
      have hd2 : (∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l)) -
          4 * Z / (R:ℝ) ^ 2 * (t - t₀) ≤ ∫ s in t₀..t, φ R s := by
        have hconst : IntervalIntegrable
            (fun s => en (fun l => c₁ s l - c₂ s l) - 4 * Z / (R:ℝ) ^ 2)
            MeasureTheory.volume t₀ t := hEint.sub intervalIntegrable_const
        have h := intervalIntegral.integral_mono_on ht₀t hconst (hφint R) hφlow
        rw [intervalIntegral.integral_sub hEint intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul] at h
        linarith
      rw [abs_le]
      constructor <;> linarith
    -- σ over the subwindow is at most σ over the whole window
    have hσglob : (∫ s in t₀..t, σ R s) ≤ ∫ s in (0:ℝ)..T, σ R s := by
      have hσ0T : IntervalIntegrable (σ R) MeasureTheory.volume 0 T := hσint R
      have hnn0 : ∀ u ∈ Icc (0:ℝ) T, 0 ≤ σ R u := fun u hu => hσnn R u hu
      have h1 : (∫ s in t₀..t, σ R s) ≤ ∫ s in t₀..T, σ R s := by
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hσ0T.mono_set (by
            rw [uIcc_of_le ht₀t, uIcc_of_le hT]; exact Icc_subset_Icc ht₀0 ht0T))
          (hσ0T.mono_set (by
            rw [uIcc_of_le ht0T, uIcc_of_le hT]
            exact Icc_subset_Icc htIcc.1 le_rfl))
        have hnn : 0 ≤ ∫ s in t..T, σ R s :=
          intervalIntegral.integral_nonneg ht0T fun u hu =>
            hnn0 u ⟨le_trans (le_trans ht₀0 ht₀t) hu.1, hu.2⟩
        linarith [hsplit.symm.le, hsplit.symm.ge]
      have h2 : (∫ s in t₀..T, σ R s) ≤ ∫ s in (0:ℝ)..T, σ R s := by
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hσ0T.mono_set (by
            rw [uIcc_of_le ht₀0, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht₀.2))
          (hσ0T.mono_set (by
            rw [uIcc_of_le ht₀.2, uIcc_of_le hT]; exact Icc_subset_Icc ht₀0 le_rfl))
        have hnn : 0 ≤ ∫ s in (0:ℝ)..t₀, σ R s :=
          intervalIntegral.integral_nonneg ht₀0 fun u hu =>
            hnn0 u ⟨hu.1, le_trans hu.2 ht₀.2⟩
        linarith [hsplit.symm.le, hsplit.symm.ge]
      linarith
    -- put it together
    have habs := abs_le.mp hIφ
    have hen_t : en (fun l => c₁ t l - c₂ t l) ≤ φ R t + 4 * Z / (R:ℝ) ^ 2 := by
      rw [hφdef]; simp only; linarith [htailt]
    have hcoef : (ν * (N:ℝ) ^ 2 - K) *
          (∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l))
        - (ν * (N:ℝ) ^ 2 - K) * (∫ s in t₀..t, φ R s)
        ≤ |ν * (N:ℝ) ^ 2 - K| * (4 * Z / (R:ℝ) ^ 2) * (t - t₀) := by
      have hEq : (ν * (N:ℝ) ^ 2 - K) *
            (∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l))
          - (ν * (N:ℝ) ^ 2 - K) * (∫ s in t₀..t, φ R s)
          = (ν * (N:ℝ) ^ 2 - K) *
            ((∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l)) -
              ∫ s in t₀..t, φ R s) := by ring
      rw [hEq]
      calc (ν * (N:ℝ) ^ 2 - K) *
            ((∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l)) - ∫ s in t₀..t, φ R s)
          ≤ |(ν * (N:ℝ) ^ 2 - K) *
              ((∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l)) -
                ∫ s in t₀..t, φ R s)| := le_abs_self _
        _ = |ν * (N:ℝ) ^ 2 - K| *
              |(∫ s in t₀..t, en (fun l => c₁ s l - c₂ s l)) -
                ∫ s in t₀..t, φ R s| := abs_mul _ _
        _ ≤ |ν * (N:ℝ) ^ 2 - K| * (4 * Z / (R:ℝ) ^ 2 * (t - t₀)) :=
              mul_le_mul_of_nonneg_left
                (by rw [abs_sub_comm]; exact hIφ) (abs_nonneg _)
        _ = |ν * (N:ℝ) ^ 2 - K| * (4 * Z / (R:ℝ) ^ 2) * (t - t₀) := by ring
    rw [neg_mul] at hmono
    have hσν : ν * (∫ s in t₀..t, σ R s) ≤ ν * ∫ s in (0:ℝ)..T, σ R s :=
      mul_le_mul_of_nonneg_left hσglob hν.le
    linarith [hftc, hmono, hen_t, hφt₀le, hcoef, hσν]
  -- STEP: let R → ∞; every error term vanishes
  have hRsq : Filter.Tendsto (fun R : ℕ => 4 * Z / (R:ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun R : ℕ => (R:ℝ) ^ 2) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun R => ?_) tendsto_natCast_atTop_atTop
      have hR : R ≤ R ^ 2 := Nat.le_self_pow (by norm_num) R
      exact_mod_cast hR
    have h4 := h2.inv_tendsto_atTop
    have h5 := h4.const_mul (4 * Z)
    simpa [div_eq_mul_inv] using h5
  have hErr : Filter.Tendsto
      (fun R : ℕ => en (fun l => c₁ t₀ l - c₂ t₀ l) + ν * (N:ℝ) ^ 2 * δ * (t - t₀) +
        (ν * (∫ s in (0:ℝ)..T, σ R s) +
          (K * (4 * Z / (R:ℝ) ^ 2)) * (t - t₀) +
          4 * Z / (R:ℝ) ^ 2 +
          |ν * (N:ℝ) ^ 2 - K| * (4 * Z / (R:ℝ) ^ 2) * (t - t₀)))
      Filter.atTop
      (nhds (en (fun l => c₁ t₀ l - c₂ t₀ l) + ν * (N:ℝ) ^ 2 * δ * (t - t₀))) := by
    have h1 : Filter.Tendsto (fun R : ℕ => ∫ s in (0:ℝ)..T, σ R s)
        Filter.atTop (nhds 0) := tail_source (by positivity) hT hdcont hdwsum hdens
    have h6 := (((h1.const_mul ν).add
      (((hRsq.const_mul K).mul_const (t - t₀)))).add hRsq).add
      ((hRsq.const_mul |ν * (N:ℝ) ^ 2 - K|).mul_const (t - t₀))
    have h7 := (tendsto_const_nhds (x := en (fun l => c₁ t₀ l - c₂ t₀ l) +
      ν * (N:ℝ) ^ 2 * δ * (t - t₀)) (f := Filter.atTop (α := ℕ))).add h6
    simpa using h7
  refine ge_of_tendsto hErr ?_
  filter_upwards [Filter.eventually_ge_atTop N] with R hR
  exact hkey R hR

end TheoremB
