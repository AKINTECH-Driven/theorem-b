/-
# DELTA-1: the spectral-weak evolution identity
-/
import TheoremB.TorusStructure

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance sw_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance sw_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance sw_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### DELTA-1: pairing transfer and the spectral-weak evolution identity -/

/-- ℂ-inner drop lemma: paired on the left against a mode orthogonal to its
frequency, the Leray projection in the right slot is invisible.  (The ℂ-inner
sibling of `inner_lerayProj_left`; conjugation lands on the `v` slot, where
`⟪v, castCV (freq k)⟫ = conj (dotR v (freq k)) = 0`.) -/
lemma d1_inner_lerayProj {k : Fin 3 → ℤ} {v u : Vel}
    (hv : dotR v (freq k) = 0) :
    inner ℂ v (lerayProj k u) = inner ℂ v u := by
  have hker : inner ℂ v (castCV (freq k)) = 0 := by
    rw [← inner_conj_symm, ← dotR_eq_inner, hv, map_zero]
  rw [lerayProj, inner_sub_right, inner_smul_right, hker, mul_zero, sub_zero]

/-- **Pairing transfer**: the physical L² pairing of two synthesized fields is
the spectral pairing of their coefficients, truncating to the (finite) support
of the test field. -/
theorem pairing_transfer {w c : (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    (hw : ∀ k, k ∉ F → w k = 0) (hwsum : Summable fun k => ‖w k‖ ^ 2)
    (hcsum : Summable fun k => ‖c k‖ ^ 2) :
    (∑ j : Fin 3, inner ℂ (synthT j w) (synthT j c)) =
      ∑ k ∈ F, inner ℂ (w k) (c k) := by
  have hj : ∀ j : Fin 3,
      inner ℂ (synthT j w) (synthT j c) = ∑ k ∈ F, conj (w k j) * (c k j) := by
    intro j
    rw [synthT_eq j hwsum, synthT_eq j hcsum]
    unfold synth
    rw [LinearIsometryEquiv.inner_map_map, lp.inner_eq_tsum]
    have hterm : ∀ k : Fin 3 → ℤ,
        (inner ℂ ((velSeq j w hwsum : (Fin 3 → ℤ) → ℂ) k)
          ((velSeq j c hcsum : (Fin 3 → ℤ) → ℂ) k) : ℂ) =
          conj (w k j) * (c k j) := by
      intro k
      rw [velSeq_apply, velSeq_apply, RCLike.inner_apply']
    refine (tsum_congr hterm).trans (tsum_eq_sum ?_)
    intro k hk
    rw [hw k hk]
    simp
  calc (∑ j : Fin 3, inner ℂ (synthT j w) (synthT j c))
      = ∑ j : Fin 3, ∑ k ∈ F, conj (w k j) * (c k j) :=
        Finset.sum_congr rfl fun j _ => hj j
    _ = ∑ k ∈ F, ∑ j : Fin 3, conj (w k j) * (c k j) := Finset.sum_comm
    _ = ∑ k ∈ F, inner ℂ (w k) (c k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [PiLp.inner_apply]
        exact Finset.sum_congr rfl fun j _ => (RCLike.inner_apply' _ _).symm

/-- **The spectral-weak evolution identity**: pairing a finitely supported
divergence-free test field against a coefficient flow satisfying the full
integral equation yields the weak-form evolution identity — the Leray
projection is invisible against the div-free test modes, so the convection
appears unprojected.  The bounds `hb`/`hwb` are the flow's exported
energy/enstrophy budgets, needed for interval integrability of the
convection term. -/
theorem spectral_weak_equation {ν : ℝ} {c₀ : (Fin 3 → ℤ) → Vel}
    {c : ℝ → (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    {w : (Fin 3 → ℤ) → Vel} {E Z : ℝ} (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    (hsum : ∀ t ∈ Set.Ici (0:ℝ), Summable fun l => ‖c t l‖ ^ 2)
    (hb : ∀ t ∈ Set.Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
      ∑ l ∈ G, ‖c t l‖ ^ 2 ≤ E)
    (hwb : ∀ t ∈ Set.Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
      ∑ l ∈ G, ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 ≤ Z)
    (hw : ∀ k, k ∉ F → w k = 0)
    (hwdiv : DivFree w)
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Set.Ici (0:ℝ)))
    (heq : ∀ t ∈ Set.Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) :
    ∀ t ∈ Set.Ici (0:ℝ),
      (∑ k ∈ F, inner ℂ (w k) (c t k)) =
        (∑ k ∈ F, inner ℂ (w k) (c₀ k)) + ∫ s in (0:ℝ)..t,
          (∑ k ∈ F, ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
            + inner ℂ (w k) (convFull (c s) k))) := by
  intro t ht
  have ht0 : (0:ℝ) ≤ t := ht
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Ici (0:ℝ) := fun s hs => hs.1
  -- continuity of the per-mode flow and convection on the window
  have hck : ∀ k, ContinuousOn (fun s => c s k) (Set.Icc (0:ℝ) t) :=
    fun k => (hcont k).mono hsub
  have hconvOn : ∀ k, ContinuousOn (fun s => convFull (c s) k) (Set.Icc (0:ℝ) t) :=
    fun k => continuousOn_convFull hE0 hZ0
      (fun s hs G => hb s (hsub hs) G)
      (fun s hs G => hwb s (hsub hs) G)
      (fun l => (hcont l).mono hsub) k
  -- interval integrability of the vector integrand
  have hfc : ∀ k, ContinuousOn (fun s =>
      (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))
      (Set.Icc (0:ℝ) t) := by
    intro k
    exact (continuousOn_const.smul (hck k)).add
      ((lerayProj_continuous k).comp_continuousOn (hconvOn k))
  have hfi : ∀ k, IntervalIntegrable (fun s =>
      (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))
      volume 0 t :=
    fun k => (hfc k).intervalIntegrable_of_Icc ht0
  -- the div-free drop: the scalar integrand loses its Leray projection
  have hscal : ∀ (k : Fin 3 → ℤ) (s : ℝ),
      inner ℂ (w k) ((-(ν * ‖freq k‖ ^ 2)) • c s k
        + lerayProj k (convFull (c s) k)) =
      (-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
        + inner ℂ (w k) (convFull (c s) k) := by
    intro k s
    have hsm : inner ℂ (w k) ((-(ν * ‖freq k‖ ^ 2)) • c s k) =
        (-(ν * ‖freq k‖ ^ 2)) • inner ℂ (w k) (c s k) :=
      LinearMapClass.map_smul_of_tower (innerSL ℂ (w k)) _ _
    rw [inner_add_right, d1_inner_lerayProj (hwdiv k), hsm, Complex.real_smul]
    push_cast
    ring
  -- interval integrability of the scalar integrand
  have hgc : ∀ k, ContinuousOn (fun s =>
      (-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
        + inner ℂ (w k) (convFull (c s) k)) (Set.Icc (0:ℝ) t) := by
    intro k
    exact (continuousOn_const.mul
        ((continuous_const.inner continuous_id).comp_continuousOn (hck k))).add
      ((continuous_const.inner continuous_id).comp_continuousOn (hconvOn k))
  have hgi : ∀ k ∈ F, IntervalIntegrable (fun s =>
      (-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
        + inner ℂ (w k) (convFull (c s) k)) volume 0 t :=
    fun k _ => (hgc k).intervalIntegrable_of_Icc ht0
  -- the per-mode weak identity
  have key : ∀ k ∈ F, inner ℂ (w k) (c t k) =
      inner ℂ (w k) (c₀ k) + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
          + inner ℂ (w k) (convFull (c s) k)) := by
    intro k _
    have h1 : inner ℂ (w k) (c t k) = inner ℂ (w k) (c₀ k) +
        inner ℂ (w k) (∫ s in (0:ℝ)..t, ((-(ν * ‖freq k‖ ^ 2)) • c s k
          + lerayProj k (convFull (c s) k))) := by
      rw [← inner_add_right, ← heq t ht k]
    have h2 : inner ℂ (w k) (∫ s in (0:ℝ)..t, ((-(ν * ‖freq k‖ ^ 2)) • c s k
        + lerayProj k (convFull (c s) k))) =
        ∫ s in (0:ℝ)..t, inner ℂ (w k) ((-(ν * ‖freq k‖ ^ 2)) • c s k
          + lerayProj k (convFull (c s) k)) := by
      have h := (innerSL ℂ (w k)).intervalIntegral_comp_comm (hfi k)
      simpa only [innerSL_apply_apply] using h.symm
    rw [h1, h2]
    congr 1
    exact intervalIntegral.integral_congr fun s _ => hscal k s
  -- sum over the support and swap the finite sum with the interval integral
  calc (∑ k ∈ F, inner ℂ (w k) (c t k))
      = ∑ k ∈ F, (inner ℂ (w k) (c₀ k) + ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
            + inner ℂ (w k) (convFull (c s) k))) :=
        Finset.sum_congr rfl key
    _ = (∑ k ∈ F, inner ℂ (w k) (c₀ k)) + ∑ k ∈ F, ∫ s in (0:ℝ)..t,
          ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
            + inner ℂ (w k) (convFull (c s) k)) := Finset.sum_add_distrib
    _ = (∑ k ∈ F, inner ℂ (w k) (c₀ k)) + ∫ s in (0:ℝ)..t,
          (∑ k ∈ F, ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
            + inner ℂ (w k) (convFull (c s) k))) := by
        rw [intervalIntegral.integral_finsetSum hgi]


/-! ### ECHO-1: weak-to-mode equation recovery -/

/-- `dotR` kills the zero vector. -/
private lemma e1_dotR_zero (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

/-- `dotR` is additive in the velocity slot. -/
private lemma e1_dotR_add_left (a b : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (a + b) r = dotR a r + dotR b r := by
  simp only [dotR_eq_inner, inner_add_right]

/-- A real scalar acting on `Vel` is the complex-cast scalar acting on `Vel`. -/
private lemma e1_real_smul (a : ℝ) (v : Vel) : a • v = ((a : ℂ)) • v := by
  rw [← smul_one_smul ℂ a v, Complex.real_smul, mul_one]

/-- `dotR` pulls a real scalar out as a complex cast. -/
private lemma e1_dotR_real_smul (a : ℝ) (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (a • v) r = (a : ℂ) * dotR v r := by
  rw [e1_real_smul, dotR_eq_inner, dotR_eq_inner, inner_smul_right]

/-- The complex inner product against a fixed vector commutes with the
interval integral. -/
private lemma e1_inner_intervalIntegral (x : Vel) {f : ℝ → Vel} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    inner ℂ x (∫ s in a..b, f s) = ∫ s in a..b, inner ℂ x (f s) := by
  have h := (innerSL ℂ x).intervalIntegral_comp_comm hf
  simp only [innerSL_apply_apply] at h
  exact h.symm

/-- `dotR` against a fixed real vector commutes with the interval integral. -/
private lemma e1_dotR_intervalIntegral (r : EuclideanSpace ℝ (Fin 3)) {f : ℝ → Vel} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    dotR (∫ s in a..b, f s) r = ∫ s in a..b, dotR (f s) r := by
  rw [dotR_eq_inner, e1_inner_intervalIntegral (castCV r) hf]
  congr 1
  funext s
  exact (dotR_eq_inner _ _).symm

set_option linter.unusedVariables false in
/-- **ECHO-1**: a weakly-formulated coefficient flow with the standard
energy/enstrophy budgets satisfies the mode-wise Leray-projected integral
equation.  The defect vector is its own admissible test vector. -/
theorem mode_equation_of_weak {ν E Z : ℝ} (hν : 0 < ν) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z)
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Set.Ici (0:ℝ)))
    (hsum : ∀ t ∈ Set.Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2))
    (hb : ∀ t ∈ Set.Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
      ∑ l ∈ G, ‖c t l‖ ^ 2 ≤ E)
    (hwb : ∀ t ∈ Set.Ici (0:ℝ), ∀ (G : Finset (Fin 3 → ℤ)),
      ∑ l ∈ G, ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2 ≤ Z)
    (hdiv : ∀ t ∈ Set.Ici (0:ℝ), DivFree (c t))
    (hzero : ∀ t ∈ Set.Ici (0:ℝ), c t 0 = 0)
    (hweak : ∀ (F : Finset (Fin 3 → ℤ)) (w : (Fin 3 → ℤ) → Vel),
      (∀ k, k ∉ F → w k = 0) → DivFree w → ∀ t ∈ Set.Ici (0:ℝ),
      (∑ k ∈ F, inner ℂ (w k) (c t k)) =
        (∑ k ∈ F, inner ℂ (w k) (c 0 k)) + ∫ s in (0:ℝ)..t,
          (∑ k ∈ F, ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (w k) (c s k)
            + inner ℂ (w k) (convFull (c s) k)))) :
    ∀ t ∈ Set.Ici (0:ℝ), ∀ k, c t k = c 0 k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) := by
  intro t ht k
  have ht0 : (0:ℝ) ≤ t := ht
  have hIcc : Set.Icc (0:ℝ) t ⊆ Set.Ici (0:ℝ) := fun s hs => hs.1
  -- continuity of the vector integrand on the window
  have hcontc : ∀ l, ContinuousOn (fun s => c s l) (Set.Icc (0:ℝ) t) :=
    fun l => (hcont l).mono hIcc
  have hconv : ContinuousOn (fun s => convFull (c s) k) (Set.Icc (0:ℝ) t) :=
    continuousOn_convFull hE0 hZ0
      (fun s hs => hb s (hIcc hs)) (fun s hs => hwb s (hIcc hs)) hcontc k
  have hcontF : ContinuousOn
      (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))
      (Set.Icc (0:ℝ) t) :=
    (continuousOn_const.smul (hcontc k)).add
      ((lerayProj_continuous k).comp_continuousOn hconv)
  have hInt : IntervalIntegrable
      (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))
      volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht0 hcontF
  set I : Vel := ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) with hIdef
  -- dotR of the integral vanishes
  have hIdot : dotR I (freq k) = 0 := by
    rw [hIdef, e1_dotR_intervalIntegral _ hInt]
    rw [intervalIntegral.integral_congr
      (g := fun _ => (0:ℂ)) ?_, intervalIntegral.integral_zero]
    intro s hs
    rw [Set.uIcc_of_le ht0] at hs
    have hs0 : s ∈ Set.Ici (0:ℝ) := hs.1
    show dotR _ _ = 0
    rw [e1_dotR_add_left, e1_dotR_real_smul, hdiv s hs0 k, dotR_lerayProj_freq,
      mul_zero, add_zero]
  -- Step 1: the defect is an admissible test vector
  have hstep1 : dotR (c t k - (c 0 k + I)) (freq k) = 0 := by
    rw [dotR_sub_left', e1_dotR_add_left, hdiv t ht k, hdiv 0 Set.self_mem_Ici k, hIdot]
    ring
  -- the inner product against the defect drops the Leray correction
  have hcast : inner ℂ (c t k - (c 0 k + I)) (castCV (freq k)) = 0 := by
    rw [← inner_conj_symm, ← dotR_eq_inner, hstep1, map_zero]
  -- inner-of-integral commutation for the defect
  have hIcomm : inner ℂ (c t k - (c 0 k + I)) I = ∫ s in (0:ℝ)..t,
      inner ℂ (c t k - (c 0 k + I))
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)) := by
    conv_lhs => rw [hIdef]
    exact e1_inner_intervalIntegral _ hInt
  -- Step 3: the right-hand side of the collapsed weak identity is inner (D) (c 0 k + I)
  have hR : inner ℂ (c t k - (c 0 k + I)) (c 0 k + I) =
      inner ℂ (c t k - (c 0 k + I)) (c 0 k) + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) * inner ℂ (c t k - (c 0 k + I)) (c s k)
          + inner ℂ (c t k - (c 0 k + I)) (convFull (c s) k)) := by
    rw [inner_add_right, hIcomm]
    congr 1
    congr 1
    funext s
    rw [inner_add_right]
    congr 1
    · rw [e1_real_smul, inner_smul_right]
      push_cast
      ring
    · simp only [lerayProj]
      rw [inner_sub_right, inner_smul_right, hcast, mul_zero, sub_zero]
  -- Step 2: instantiate the weak identity with the defect as its own test vector
  have hsupp : ∀ m, m ∉ ({k} : Finset (Fin 3 → ℤ)) →
      (fun m => if m = k then c t k - (c 0 k + I) else 0) m = 0 := by
    intro m hm
    exact if_neg (fun h => hm (Finset.mem_singleton.mpr h))
  have hdivw : DivFree (fun m => if m = k then c t k - (c 0 k + I) else 0) := by
    intro m
    rcases eq_or_ne m k with rfl | hmk
    · simpa using hstep1
    · simp [hmk, e1_dotR_zero]
  have hw := hweak {k} (fun m => if m = k then c t k - (c 0 k + I) else 0)
    hsupp hdivw t ht
  simp only [Finset.sum_singleton, if_true] at hw
  -- assemble: inner D D = 0, hence D = 0
  have h1 : inner ℂ (c t k - (c 0 k + I)) (c t k) =
      inner ℂ (c t k - (c 0 k + I)) (c 0 k + I) := hw.trans hR.symm
  have h2 : inner ℂ (c t k - (c 0 k + I)) (c t k - (c 0 k + I)) = (0:ℂ) := by
    rw [inner_sub_right, h1, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h2)

end

end TheoremB
