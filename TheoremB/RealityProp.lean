/-
  TheoremB/RealityProp.lean
  M4 wave 4 of the Theorem B campaign (27 Aug 2026).

  Reality propagation, and the zero-data capstone: for the standard
  divergence-free spectral Galerkin Navier-Stokes ODE, BOTH structural field
  properties (reality and divergence-freeness) propagate from t = 0, so the
  trap needs its dynamical hypotheses at the initial instant only.

  Mechanism: the conjugation defect d(t,k) = c(t,-k) - conjVel(c(t,k))
  obeys a damped linear system d' = -nu|k|^2 d + R where R telescopes
  through the conjugation-equivariance of the convection and the Leray
  projection (lerayProj(-k) = lerayProj k); the forcing is square-dominated
  by the defect energy with a constant from the compact-window field bound,
  and a root-free two-sided interval Gronwall (exponential integrating
  factors, closed by the campaign's own le_of_deriv_nonpos) kills it.

  Existence of the flow remains quantified-over (Picard-Lindelof is the
  natural next wave).

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.NSGalerkin

namespace TheoremB

open Set

/-! ### Local algebra helpers (wave-3 privates re-proved locally) -/

private lemma fDotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

private lemma fDotR_neg_right (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR v (-r) = -dotR v r := by
  simp [dotR, mul_neg, Finset.sum_neg_distrib]

private lemma fDotR_sub_left (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (v - w) r = dotR v r - dotR w r := by
  simp only [dotR, WithLp.ofLp_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma fConj_dotR (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (dotR v r) = dotR (conjVel v) r := by
  simp only [dotR]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1

private lemma fConjVel_zero : conjVel 0 = 0 := by
  ext j
  simp [conjVel]

private lemma fConjVel_add (v w : Vel) : conjVel (v + w) = conjVel v + conjVel w := by
  ext j
  simp [conjVel]

private lemma fConjVel_sub (v w : Vel) : conjVel (v - w) = conjVel v - conjVel w := by
  ext j
  simp [conjVel]

private lemma fConjVel_neg (v : Vel) : conjVel (-v) = -conjVel v := by
  ext j
  simp [conjVel]

private lemma fConjVel_smul (z : ℂ) (v : Vel) :
    conjVel (z • v) = (starRingEnd ℂ) z • conjVel v := by
  ext j
  simp [conjVel]

private lemma fConjVel_sum {ι : Type*} (s : Finset ι) (f : ι → Vel) :
    conjVel (∑ i ∈ s, f i) = ∑ i ∈ s, conjVel (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fConjVel_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fConjVel_add, ih]

private lemma fCastCV_zero : castCV 0 = 0 := by
  ext j
  simp [castCV]

private lemma fCastCV_neg (r : EuclideanSpace ℝ (Fin 3)) : castCV (-r) = -castCV r := by
  ext j
  simp [castCV]

private lemma fConjVel_castCV (r : EuclideanSpace ℝ (Fin 3)) :
    conjVel (castCV r) = castCV r := by
  ext j
  simp [conjVel, castCV]

private lemma fFreq_zero : freq (0 : Fin 3 → ℤ) = 0 := by
  ext j
  simp [freq]

/-! ### lerayProj helpers -/

private lemma fLerayProj_neg (k : Fin 3 → ℤ) (v : Vel) :
    lerayProj (-k) v = lerayProj k v := by
  simp only [lerayProj, freq_neg, fDotR_neg_right, norm_neg, fCastCV_neg, neg_div, neg_smul,
    smul_neg, neg_neg]

private lemma fConjVel_lerayProj (k : Fin 3 → ℤ) (v : Vel) :
    conjVel (lerayProj k v) = lerayProj k (conjVel v) := by
  simp only [lerayProj]
  rw [fConjVel_sub, fConjVel_smul, fConjVel_castCV, map_div₀, fConj_dotR, Complex.conj_ofReal]

private lemma fLerayProj_sub (k : Fin 3 → ℤ) (v w : Vel) :
    lerayProj k (v - w) = lerayProj k v - lerayProj k w := by
  simp only [lerayProj, fDotR_sub_left, sub_div, sub_smul]
  abel

private lemma fLerayProj_zero (k : Fin 3 → ℤ) : lerayProj k 0 = 0 := by
  simp [lerayProj, fDotR_zero_left]

private lemma fNorm_lerayProj_le (k : Fin 3 → ℤ) (w : Vel) :
    ‖lerayProj k w‖ ≤ 2 * ‖w‖ := by
  by_cases hk : k = 0
  · subst hk
    simp only [lerayProj, fFreq_zero, fCastCV_zero, smul_zero, sub_zero]
    linarith [norm_nonneg w]
  · have h1 : (1 : ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    have hpos : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos h1
    have hstep : ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ ≤ ‖w‖ := by
      rw [norm_smul, norm_div, norm_castCV]
      have hcast : ‖((‖freq k‖ ^ 2 : ℝ) : ℂ)‖ = ‖freq k‖ ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (sq_nonneg _)
      rw [hcast, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖freq k‖ ^ 2)]
      calc ‖dotR w (freq k)‖ * ‖freq k‖
          ≤ (‖freq k‖ * ‖w‖) * ‖freq k‖ :=
            mul_le_mul_of_nonneg_right (norm_dotR_le w (freq k)) (norm_nonneg _)
        _ = ‖w‖ * ‖freq k‖ ^ 2 := by ring
    have htri : ‖lerayProj k w‖
        ≤ ‖w‖ + ‖(dotR w (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)‖ := by
      simp only [lerayProj]
      exact norm_sub_le _ _
    linarith

/-! ### Finite frequency bound and elementary Cauchy–Schwarz -/

private lemma fFreqBound (S : Finset (Fin 3 → ℤ)) :
    ∀ x ∈ S, ∀ y ∈ S, ‖freq (x - y)‖ ≤ 2 * ∑ j ∈ S, ‖freq j‖ := by
  intro x hx y hy
  have h1 : ‖freq x‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hx
  have h2 : ‖freq y‖ ≤ ∑ j ∈ S, ‖freq j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) hy
  rw [freq_sub]
  calc ‖freq x - freq y‖ ≤ ‖freq x‖ + ‖freq y‖ := norm_sub_le _ _
    _ ≤ 2 * ∑ j ∈ S, ‖freq j‖ := by linarith

private lemma fSq_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

/-! ### The conjugation-defect forcing bound -/

theorem defect_forcing_bound {S : Finset (Fin 3 → ℤ)} (hSsym : ∀ k ∈ S, -k ∈ S) :
    ∃ C, 0 ≤ C ∧ ∀ {c : (Fin 3 → ℤ) → Vel}, (∀ k, k ∉ S → c k = 0) →
      ∀ {M : ℝ}, 0 ≤ M → (∀ k, ‖c k‖ ≤ M) →
      ∀ k, ‖lerayProj (-k) (convGal S c (-k)) -
          conjVel (lerayProj k (convGal S c k))‖ ^ 2 ≤
        C * M ^ 2 * (∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2) := by
  classical
  obtain ⟨FB, hFB0, hFBb⟩ : ∃ FB : ℝ, 0 ≤ FB ∧ ∀ x ∈ S, ∀ y ∈ S, ‖freq (x - y)‖ ≤ FB :=
    ⟨2 * ∑ j ∈ S, ‖freq j‖,
      by
        have := Finset.sum_nonneg (fun j (_ : j ∈ S) => norm_nonneg (freq j))
        linarith,
      fFreqBound S⟩
  refine ⟨16 * FB ^ 2 * S.card, by positivity, ?_⟩
  intro c hc M hM0 hMle k
  have hL : lerayProj (-k) (convGal S c (-k)) - conjVel (lerayProj k (convGal S c k))
      = lerayProj k (convGal S c (-k) - conjVel (convGal S c k)) := by
    rw [fLerayProj_neg, fConjVel_lerayProj, fLerayProj_sub]
  by_cases hkS : k ∈ S
  · -- main case: k ∈ S
    have hnkS : -k ∈ S := hSsym k hkS
    have hd0 : ∀ j, j ∉ S → c (-j) - conjVel (c j) = 0 := by
      intro j hj
      have h2 : c (-j) = 0 := hc (-j) fun h => hj (by simpa using hSsym _ h)
      rw [hc j hj, h2, fConjVel_zero, sub_zero]
    -- expand convGal S c (-k) by the reindex l ↦ -l
    have hA : convGal S c (-k)
        = ∑ l ∈ S, (Complex.I * dotR (c (-l)) (freq (k - l))) • c (-(k - l)) := by
      have h0 : convGal S c (-k)
          = -∑ l ∈ S, (Complex.I * dotR (c l) (freq (-k - l))) • c (-k - l) := by
        simp [convGal, hnkS]
      have hre : ∑ l ∈ S, (Complex.I * dotR (c l) (freq (-k - l))) • c (-k - l)
          = ∑ l ∈ S, -((Complex.I * dotR (c (-l)) (freq (k - l))) • c (-(k - l))) := by
        refine Finset.sum_nbij' (fun l => -l) (fun l => -l)
          (fun a ha => hSsym a ha) (fun a ha => hSsym a ha)
          (fun a _ => neg_neg a) (fun a _ => neg_neg a) ?_
        intro a ha
        have e1 : -k - a = -(k + a) := by abel
        rw [e1, freq_neg, fDotR_neg_right]
        simp [sub_neg_eq_add, mul_neg, neg_smul]
      rw [h0, hre, Finset.sum_neg_distrib, neg_neg]
    -- push conjVel through convGal S c k
    have hB : conjVel (convGal S c k)
        = ∑ l ∈ S, (Complex.I * dotR (conjVel (c l)) (freq (k - l))) • conjVel (c (k - l)) := by
      have h0 : convGal S c k
          = -∑ l ∈ S, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) := by
        simp [convGal, hkS]
      have hpt : ∀ l ∈ S, conjVel ((Complex.I * dotR (c l) (freq (k - l))) • c (k - l))
          = -((Complex.I * dotR (conjVel (c l)) (freq (k - l))) • conjVel (c (k - l))) := by
        intro l _
        rw [fConjVel_smul, map_mul, Complex.conj_I, fConj_dotR, neg_mul, neg_smul]
      calc conjVel (convGal S c k)
          = conjVel (-∑ l ∈ S, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l)) := by
            rw [h0]
        _ = -conjVel (∑ l ∈ S, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l)) :=
            fConjVel_neg _
        _ = -∑ l ∈ S, conjVel ((Complex.I * dotR (c l) (freq (k - l))) • c (k - l)) := by
            rw [fConjVel_sum]
        _ = -∑ l ∈ S,
              -((Complex.I * dotR (conjVel (c l)) (freq (k - l))) • conjVel (c (k - l))) := by
            rw [Finset.sum_congr rfl hpt]
        _ = ∑ l ∈ S, (Complex.I * dotR (conjVel (c l)) (freq (k - l))) • conjVel (c (k - l)) := by
            rw [Finset.sum_neg_distrib, neg_neg]
    -- the telescope
    have hdiff : convGal S c (-k) - conjVel (convGal S c k)
        = ∑ l ∈ S, ((Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))
            + (Complex.I * dotR (conjVel (c l)) (freq (k - l)))
              • (c (-(k - l)) - conjVel (c (k - l)))) := by
      rw [hA, hB, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [fDotR_sub_left]
      simp only [mul_sub, sub_smul, smul_sub]
      abel
    -- termwise bound
    have hterm : ∀ l ∈ S,
        ‖(Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))
          + (Complex.I * dotR (conjVel (c l)) (freq (k - l)))
            • (c (-(k - l)) - conjVel (c (k - l)))‖
        ≤ FB * M * (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) := by
      intro l hl
      have hfb : ‖freq (k - l)‖ ≤ FB := hFBb k hkS l hl
      have h1 : ‖(Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))‖
          ≤ FB * M * ‖c (-l) - conjVel (c l)‖ := by
        rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
        calc ‖dotR (c (-l) - conjVel (c l)) (freq (k - l))‖ * ‖c (-(k - l))‖
            ≤ (‖freq (k - l)‖ * ‖c (-l) - conjVel (c l)‖) * M := by
              refine mul_le_mul (norm_dotR_le _ _) (hMle _) (norm_nonneg _) ?_
              positivity
          _ ≤ (FB * ‖c (-l) - conjVel (c l)‖) * M := by
              have hmm := mul_le_mul_of_nonneg_right hfb
                (norm_nonneg (c (-l) - conjVel (c l)))
              exact mul_le_mul_of_nonneg_right hmm hM0
          _ = FB * M * ‖c (-l) - conjVel (c l)‖ := by ring
      have h2 : ‖(Complex.I * dotR (conjVel (c l)) (freq (k - l)))
            • (c (-(k - l)) - conjVel (c (k - l)))‖
          ≤ FB * M * ‖c (-(k - l)) - conjVel (c (k - l))‖ := by
        rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
        have hcm : ‖conjVel (c l)‖ ≤ M := by rw [norm_conjVel]; exact hMle l
        calc ‖dotR (conjVel (c l)) (freq (k - l))‖ * ‖c (-(k - l)) - conjVel (c (k - l))‖
            ≤ (‖freq (k - l)‖ * ‖conjVel (c l)‖) * ‖c (-(k - l)) - conjVel (c (k - l))‖ :=
              mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
          _ ≤ (FB * M) * ‖c (-(k - l)) - conjVel (c (k - l))‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              exact mul_le_mul hfb hcm (norm_nonneg _) hFB0
          _ = FB * M * ‖c (-(k - l)) - conjVel (c (k - l))‖ := by ring
      calc ‖(Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))
            + (Complex.I * dotR (conjVel (c l)) (freq (k - l)))
              • (c (-(k - l)) - conjVel (c (k - l)))‖
          ≤ ‖(Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))‖
            + ‖(Complex.I * dotR (conjVel (c l)) (freq (k - l)))
                • (c (-(k - l)) - conjVel (c (k - l)))‖ := norm_add_le _ _
        _ ≤ FB * M * ‖c (-l) - conjVel (c l)‖
            + FB * M * ‖c (-(k - l)) - conjVel (c (k - l))‖ := add_le_add h1 h2
        _ = FB * M * (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) := by
            ring
    -- sum bound
    have hsum : ‖convGal S c (-k) - conjVel (convGal S c k)‖
        ≤ FB * M * ∑ l ∈ S,
            (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) := by
      rw [hdiff]
      calc ‖∑ l ∈ S, ((Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))
              + (Complex.I * dotR (conjVel (c l)) (freq (k - l)))
                • (c (-(k - l)) - conjVel (c (k - l))))‖
          ≤ ∑ l ∈ S, ‖(Complex.I * dotR (c (-l) - conjVel (c l)) (freq (k - l))) • c (-(k - l))
              + (Complex.I * dotR (conjVel (c l)) (freq (k - l)))
                • (c (-(k - l)) - conjVel (c (k - l)))‖ := norm_sum_le _ _
        _ ≤ ∑ l ∈ S, FB * M *
              (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) :=
            Finset.sum_le_sum hterm
        _ = FB * M * ∑ l ∈ S,
              (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) :=
            (Finset.mul_sum _ _ _).symm
    -- the shifted-index sum bound
    have hshift : ∑ l ∈ S, ‖c (-(k - l)) - conjVel (c (k - l))‖ ^ 2
        ≤ ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2 := by
      have hinj : Set.InjOn (fun l => k - l) ↑S := by
        intro a _ b _ hab
        have hab' : k - a = k - b := hab
        exact sub_right_inj.mp hab'
      have himg : ∑ l ∈ S, ‖c (-(k - l)) - conjVel (c (k - l))‖ ^ 2
          = ∑ j ∈ Finset.image (fun l => k - l) S, ‖c (-j) - conjVel (c j)‖ ^ 2 :=
        (Finset.sum_image (f := fun j => ‖c (-j) - conjVel (c j)‖ ^ 2) hinj).symm
      have hfil : ∑ j ∈ (Finset.image (fun l => k - l) S).filter (fun j => j ∈ S),
            ‖c (-j) - conjVel (c j)‖ ^ 2
          = ∑ j ∈ Finset.image (fun l => k - l) S, ‖c (-j) - conjVel (c j)‖ ^ 2 := by
        apply Finset.sum_filter_of_ne
        intro x _ hne
        by_contra hxS
        exact hne (by rw [hd0 x hxS, norm_zero]; norm_num)
      have hsub : (Finset.image (fun l => k - l) S).filter (fun j => j ∈ S) ⊆ S := by
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      calc ∑ l ∈ S, ‖c (-(k - l)) - conjVel (c (k - l))‖ ^ 2
          = ∑ j ∈ Finset.image (fun l => k - l) S, ‖c (-j) - conjVel (c j)‖ ^ 2 := himg
        _ = ∑ j ∈ (Finset.image (fun l => k - l) S).filter (fun j => j ∈ S),
              ‖c (-j) - conjVel (c j)‖ ^ 2 := hfil.symm
        _ ≤ ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
    -- split of the squared sum
    have hsplit : ∑ l ∈ S,
          (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) ^ 2
        ≤ 4 * ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2 := by
      have h1 : ∀ l ∈ S,
          (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) ^ 2
          ≤ 2 * ‖c (-l) - conjVel (c l)‖ ^ 2
            + 2 * ‖c (-(k - l)) - conjVel (c (k - l))‖ ^ 2 := fun l _ => by
        nlinarith [sq_nonneg (‖c (-l) - conjVel (c l)‖ - ‖c (-(k - l)) - conjVel (c (k - l))‖)]
      calc ∑ l ∈ S, (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) ^ 2
          ≤ ∑ l ∈ S, (2 * ‖c (-l) - conjVel (c l)‖ ^ 2
              + 2 * ‖c (-(k - l)) - conjVel (c (k - l))‖ ^ 2) := Finset.sum_le_sum h1
        _ = 2 * (∑ l ∈ S, ‖c (-l) - conjVel (c l)‖ ^ 2)
            + 2 * (∑ l ∈ S, ‖c (-(k - l)) - conjVel (c (k - l))‖ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ 2 * (∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2)
            + 2 * (∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2) := by
            have h2 : ∑ l ∈ S, ‖c (-l) - conjVel (c l)‖ ^ 2
                = ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2 := rfl
            linarith [hshift]
        _ = 4 * ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2 := by ring
    -- Cauchy–Schwarz
    have hT2 : (∑ l ∈ S, (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖)) ^ 2
        ≤ (S.card : ℝ) * (4 * ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2) := by
      calc (∑ l ∈ S, (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖)) ^ 2
          ≤ (S.card : ℝ) * ∑ l ∈ S,
              (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖) ^ 2 :=
            fSq_sum_le S _
        _ ≤ (S.card : ℝ) * (4 * ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg _)
    -- assemble
    rw [hL]
    have hX : ‖lerayProj k (convGal S c (-k) - conjVel (convGal S c k))‖
        ≤ 2 * (FB * M * ∑ l ∈ S,
            (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖)) := by
      calc ‖lerayProj k (convGal S c (-k) - conjVel (convGal S c k))‖
          ≤ 2 * ‖convGal S c (-k) - conjVel (convGal S c k)‖ := fNorm_lerayProj_le k _
        _ ≤ 2 * (FB * M * ∑ l ∈ S,
              (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖)) := by
            linarith [hsum]
    have hXsq : ‖lerayProj k (convGal S c (-k) - conjVel (convGal S c k))‖ ^ 2
        ≤ (2 * (FB * M * ∑ l ∈ S,
            (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖))) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) hX
    calc ‖lerayProj k (convGal S c (-k) - conjVel (convGal S c k))‖ ^ 2
        ≤ (2 * (FB * M * ∑ l ∈ S,
            (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖))) ^ 2 := hXsq
      _ = 4 * FB ^ 2 * M ^ 2 * (∑ l ∈ S,
            (‖c (-l) - conjVel (c l)‖ + ‖c (-(k - l)) - conjVel (c (k - l))‖)) ^ 2 := by
          ring
      _ ≤ 4 * FB ^ 2 * M ^ 2
            * ((S.card : ℝ) * (4 * ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left hT2 ?_
          positivity
      _ = 16 * FB ^ 2 * (S.card : ℝ) * M ^ 2 * ∑ j ∈ S, ‖c (-j) - conjVel (c j)‖ ^ 2 := by
          ring
  · -- k ∉ S : both convGal terms vanish
    have hnk : -k ∉ S := fun h => hkS (by simpa using hSsym _ h)
    have h1 : convGal S c k = 0 := by simp [convGal, hkS]
    have h2 : convGal S c (-k) = 0 := by simp [convGal, hnk]
    rw [hL, h1, h2, fConjVel_zero, sub_zero, fLerayProj_zero, norm_zero]
    have h0 : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [h0]
    positivity

/-! ## The interval Gronwall layer -/

/-- Coefficient-wise product rule for the plain (weight-1) energy sum along a
flow: local replica of GalerkinTrap's private `hasDerivAt_weighted_sum`. -/
private lemma hasDerivAt_sum_sq {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {S : Finset (Fin 3 → ℤ)}
    {c : ℝ → (Fin 3 → ℤ) → W} {c' : (Fin 3 → ℤ) → W} {t : ℝ}
    (hderiv : ∀ k, HasDerivAt (fun s : ℝ => c s k) (c' k) t) :
    HasDerivAt (fun s : ℝ => ∑ k ∈ S, ‖c s k‖ ^ 2)
      (∑ k ∈ S, 2 * inner ℝ (c' k) (c t k)) t := by
  have hterm : ∀ k ∈ S, HasDerivAt (fun s : ℝ => ‖c s k‖ ^ 2)
      (2 * inner ℝ (c' k) (c t k)) t := by
    intro k _
    have h1 : HasDerivAt (fun s : ℝ => inner ℝ (c s k) (c s k))
        (inner ℝ (c t k) (c' k) + inner ℝ (c' k) (c t k)) t :=
      (hderiv k).inner ℝ (hderiv k)
    have h2 : (fun s : ℝ => ‖c s k‖ ^ 2) = fun s : ℝ => inner ℝ (c s k) (c s k) := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    have h4 : inner ℝ (c t k) (c' k) + inner ℝ (c' k) (c t k) =
        2 * inner ℝ (c' k) (c t k) := by
      rw [real_inner_comm (c t k) (c' k)]; ring
    rw [h2, ← h4]; exact h1
  have h := HasDerivAt.sum hterm
  have heq : (∑ i ∈ S, fun s : ℝ => ‖c s i‖ ^ 2) =
      fun s : ℝ => ∑ k ∈ S, ‖c s k‖ ^ 2 := by
    funext s
    simp [Finset.sum_apply]
  rwa [heq] at h

/-- Mirror of the public `le_of_deriv_nonpos`, backward monotone direction. -/
private lemma ge_of_deriv_nonneg' {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hc : ContinuousOn f (Icc x y))
    (hd : DifferentiableOn ℝ f (Ioo x y))
    (h' : ∀ t ∈ Ioo x y, 0 ≤ deriv f t) :
    f x ≤ f y := by
  have h := monotoneOn_of_deriv_nonneg (convex_Icc x y) hc
    (by rwa [interior_Icc]) (by rwa [interior_Icc])
  exact h (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

/-- Root-free two-sided Gronwall on an interval containing `0`. -/
private lemma vanish_of_deriv_bounds_on {φ D : ℝ → ℝ} {A B a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hd : ∀ s : ℝ, HasDerivAt φ (D s) s)
    (hub : ∀ s ∈ Icc a b, D s ≤ A * φ s)
    (hlb : ∀ s ∈ Icc a b, (-B) * φ s ≤ D s)
    (hnn : ∀ s : ℝ, 0 ≤ φ s) (h0 : φ 0 = 0) :
    ∀ t ∈ Icc a b, φ t = 0 := by
  intro t htm
  rcases le_total 0 t with ht | ht
  · have hψd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Real.exp (-A * u) * φ u)
        (Real.exp (-A * s) * (-A) * φ s + Real.exp (-A * s) * D s) s := by
      intro s
      have hlin : HasDerivAt (fun u : ℝ => -A * u) (-A) s := by
        simpa using (hasDerivAt_id s).const_mul (-A)
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-A * u))
          (Real.exp (-A * s) * (-A)) s := hlin.exp
      exact hexp.mul (hd s)
    have hnonpos : ∀ s ∈ Ioo (0 : ℝ) t,
        deriv (fun u : ℝ => Real.exp (-A * u) * φ u) s ≤ 0 := by
      intro s hs
      have hsm : s ∈ Icc a b := ⟨le_trans ha hs.1.le, le_trans hs.2.le htm.2⟩
      rw [(hψd s).deriv]
      nlinarith [mul_le_mul_of_nonneg_left (hub s hsm) (Real.exp_pos (-A * s)).le]
    have hcont : ContinuousOn (fun u : ℝ => Real.exp (-A * u) * φ u) (Icc 0 t) :=
      fun s _ => (hψd s).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun u : ℝ => Real.exp (-A * u) * φ u) (Ioo 0 t) :=
      fun s _ => (hψd s).differentiableAt.differentiableWithinAt
    have hle : Real.exp (-A * t) * φ t ≤ Real.exp (-A * 0) * φ 0 :=
      le_of_deriv_nonpos ht hcont hdiff hnonpos
    have h00 : Real.exp (-A * 0) * φ 0 = 0 := by rw [h0]; ring
    have hψ0 : Real.exp (-A * t) * φ t = 0 :=
      le_antisymm (h00 ▸ hle) (mul_nonneg (Real.exp_pos (-A * t)).le (hnn t))
    rcases mul_eq_zero.mp hψ0 with h | h
    · exact absurd h (Real.exp_ne_zero _)
    · exact h
  · have hχd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Real.exp (B * u) * φ u)
        (Real.exp (B * s) * B * φ s + Real.exp (B * s) * D s) s := by
      intro s
      have hlin : HasDerivAt (fun u : ℝ => B * u) B s := by
        simpa using (hasDerivAt_id s).const_mul B
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (B * u))
          (Real.exp (B * s) * B) s := hlin.exp
      exact hexp.mul (hd s)
    have hnonneg : ∀ s ∈ Ioo t (0 : ℝ),
        0 ≤ deriv (fun u : ℝ => Real.exp (B * u) * φ u) s := by
      intro s hs
      have hsm : s ∈ Icc a b := ⟨le_trans htm.1 hs.1.le, le_trans hs.2.le hb⟩
      rw [(hχd s).deriv]
      nlinarith [mul_le_mul_of_nonneg_left (hlb s hsm) (Real.exp_pos (B * s)).le]
    have hcont : ContinuousOn (fun u : ℝ => Real.exp (B * u) * φ u) (Icc t 0) :=
      fun s _ => (hχd s).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun u : ℝ => Real.exp (B * u) * φ u) (Ioo t 0) :=
      fun s _ => (hχd s).differentiableAt.differentiableWithinAt
    have hle : Real.exp (B * t) * φ t ≤ Real.exp (B * 0) * φ 0 :=
      ge_of_deriv_nonneg' ht hcont hdiff hnonneg
    have h00 : Real.exp (B * 0) * φ 0 = 0 := by rw [h0]; ring
    have hχ0 : Real.exp (B * t) * φ t = 0 :=
      le_antisymm (h00 ▸ hle) (mul_nonneg (Real.exp_pos (B * t)).le (hnn t))
    rcases mul_eq_zero.mp hχ0 with h | h
    · exact absurd h (Real.exp_ne_zero _)
    · exact h

/-- **Two-sided defect vanishing on an interval containing `0`** (the Lipschitz
constant only needs to be valid on the window). -/
theorem defect_vanishes_on {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {S : Finset (Fin 3 → ℤ)} {d : ℝ → (Fin 3 → ℤ) → V} {lam : (Fin 3 → ℤ) → ℝ}
    {R : ℝ → (Fin 3 → ℤ) → V} {L a b : ℝ}
    (hL : 0 ≤ L) (ha : a ≤ 0) (hb : 0 ≤ b) (hlam : ∀ k, 0 ≤ lam k)
    (hderiv : ∀ (s : ℝ) k, HasDerivAt (fun u => d u k) ((-(lam k)) • d s k + R s k) s)
    (hsupp : ∀ (s : ℝ) k, k ∉ S → d s k = 0)
    (hR : ∀ s ∈ Icc a b, ∀ k ∈ S, ‖R s k‖ ^ 2 ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2))
    (h0 : ∀ k, d 0 k = 0) : ∀ t ∈ Icc a b, ∀ k, d t k = 0 := by
  classical
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, ∀ k ∈ S, lam k ≤ Λ :=
    ⟨∑ k ∈ S, lam k, fun k hk => Finset.single_le_sum (fun j _ => hlam j) hk⟩
  have hΦd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => ∑ j ∈ S, ‖d u j‖ ^ 2)
      (∑ k ∈ S, 2 * inner ℝ ((-(lam k)) • d s k + R s k) (d s k)) s :=
    fun s => hasDerivAt_sum_sq (fun k => hderiv s k)
  have hpair : ∀ (s : ℝ) (k : Fin 3 → ℤ),
      (2 : ℝ) * inner ℝ ((-(lam k)) • d s k + R s k) (d s k)
        = -(2 * lam k * ‖d s k‖ ^ 2) + 2 * inner ℝ (R s k) (d s k) := by
    intro s k
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hub : ∀ s ∈ Icc a b, ∀ k ∈ S,
      (2 : ℝ) * inner ℝ ((-(lam k)) • d s k + R s k) (d s k)
        ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2 := by
    intro s hs k hk
    rw [hpair s k]
    have h1 : |inner ℝ (R s k) (d s k)| ≤ ‖R s k‖ * ‖d s k‖ :=
      abs_real_inner_le_norm _ _
    have h2 : 2 * (‖R s k‖ * ‖d s k‖) ≤ ‖R s k‖ ^ 2 + ‖d s k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖R s k‖ - ‖d s k‖)]
    have h3 : ‖R s k‖ ^ 2 ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2) := hR s hs k hk
    have h4 : (0 : ℝ) ≤ 2 * lam k * ‖d s k‖ ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (hlam k)) (sq_nonneg _)
    have h5 : inner ℝ (R s k) (d s k) ≤ |inner ℝ (R s k) (d s k)| := le_abs_self _
    linarith
  have hlb : ∀ s ∈ Icc a b, ∀ k ∈ S,
      (-(2 * Λ)) * ‖d s k‖ ^ 2 - (L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2)
        ≤ (2 : ℝ) * inner ℝ ((-(lam k)) • d s k + R s k) (d s k) := by
    intro s hs k hk
    rw [hpair s k]
    have h1 : |inner ℝ (R s k) (d s k)| ≤ ‖R s k‖ * ‖d s k‖ :=
      abs_real_inner_le_norm _ _
    have h2 : 2 * (‖R s k‖ * ‖d s k‖) ≤ ‖R s k‖ ^ 2 + ‖d s k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖R s k‖ - ‖d s k‖)]
    have h3 : ‖R s k‖ ^ 2 ≤ L * (∑ j ∈ S, ‖d s j‖ ^ 2) := hR s hs k hk
    have h5 : -|inner ℝ (R s k) (d s k)| ≤ inner ℝ (R s k) (d s k) := neg_abs_le _
    have h6 : 2 * lam k * ‖d s k‖ ^ 2 ≤ 2 * Λ * ‖d s k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hΛ k hk]) (sq_nonneg _)
    linarith
  have hDub : ∀ s ∈ Icc a b,
      (∑ k ∈ S, 2 * inner ℝ ((-(lam k)) • d s k + R s k) (d s k))
        ≤ ((S.card : ℝ) * L + 1) * (∑ j ∈ S, ‖d s j‖ ^ 2) := by
    intro s hs
    have h := Finset.sum_le_sum (hub s hs)
    have hsum : ∑ k ∈ S, (L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2)
        = (S.card : ℝ) * (L * (∑ j ∈ S, ‖d s j‖ ^ 2)) + (∑ j ∈ S, ‖d s j‖ ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at h
    linarith
  have hDlb : ∀ s ∈ Icc a b,
      (-(2 * Λ + (S.card : ℝ) * L + 1)) * (∑ j ∈ S, ‖d s j‖ ^ 2)
        ≤ ∑ k ∈ S, 2 * inner ℝ ((-(lam k)) • d s k + R s k) (d s k) := by
    intro s hs
    have h := Finset.sum_le_sum (hlb s hs)
    have hsum : ∑ k ∈ S,
        ((-(2 * Λ)) * ‖d s k‖ ^ 2 - (L * (∑ j ∈ S, ‖d s j‖ ^ 2) + ‖d s k‖ ^ 2))
        = (-(2 * Λ)) * (∑ j ∈ S, ‖d s j‖ ^ 2)
          - ((S.card : ℝ) * (L * (∑ j ∈ S, ‖d s j‖ ^ 2)) + (∑ j ∈ S, ‖d s j‖ ^ 2)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at h
    linarith
  have hΦnn : ∀ s : ℝ, (0 : ℝ) ≤ ∑ j ∈ S, ‖d s j‖ ^ 2 :=
    fun s => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hΦ0 : (∑ j ∈ S, ‖d 0 j‖ ^ 2) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [h0 j]; simp
  have hΦ : ∀ t ∈ Icc a b, (∑ j ∈ S, ‖d t j‖ ^ 2) = 0 :=
    vanish_of_deriv_bounds_on ha hb hΦd hDub hDlb hΦnn hΦ0
  intro t htm k
  by_cases hk : k ∈ S
  · have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ‖d t j‖)).mp (hΦ t htm) k hk
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)
  · exact hsupp t k hk


/-! ## Reality propagation and the zero-data capstone -/

/-- Componentwise conjugation as an ℝ-continuous-linear map. -/
noncomputable def conjVelL : Vel →L[ℝ] Vel :=
  LinearMap.toContinuousLinearMap
    { toFun := conjVel
      map_add' := by
        intro a b
        ext j
        simp [conjVel]
      map_smul' := by
        intro r v
        ext j
        simp only [conjVel, WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply,
          RingHom.id_apply]
        rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal] }

lemma conjVelL_apply (v : Vel) : conjVelL v = conjVel v := rfl

private lemma conjVel_zero : conjVel 0 = 0 := by
  ext j
  simp [conjVel]

private lemma conjVel_real_smul (r : ℝ) (v : Vel) :
    conjVel (r • v) = r • conjVel v :=
  conjVelL.map_smul r v

private lemma conjVel_add (a b : Vel) : conjVel (a + b) = conjVel a + conjVel b :=
  conjVelL.map_add a b

/-- **Reality propagates under the Leray-projected Galerkin ODE**: the
conjugation defect obeys a damped linear system whose forcing telescopes
through the convection's conjugation-equivariance, and vanishes by the
interval Gronwall. -/
theorem realField_propagates {ν : ℝ} (hν : 0 < ν) {S : Finset (Fin 3 → ℤ)} (hSsym : ∀ k ∈ S, -k ∈ S)
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ t k, k ∉ S → c t k = 0)
    (hODE : ∀ t k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t)
    (h0real : RealField (c 0)) :
    ∀ t, RealField (c t) := by
  -- the conjugation defect
  set d : ℝ → (Fin 3 → ℤ) → Vel :=
    fun t k => c t (-k) - conjVel (c t k) with hd
  set R : ℝ → (Fin 3 → ℤ) → Vel :=
    fun t k => lerayProj (-k) (convGal S (c t) (-k)) -
      conjVel (lerayProj k (convGal S (c t) k)) with hR
  set lam : (Fin 3 → ℤ) → ℝ := fun k => ν * ‖freq k‖ ^ 2 with hlam
  have hlamnn : ∀ k, 0 ≤ lam k := fun k => by positivity
  have hSnot : ∀ k, k ∉ S → -k ∉ S := by
    intro k hk hnk
    exact hk (by simpa using hSsym (-k) hnk)
  -- the defect ODE
  have hdderiv : ∀ (s : ℝ) k, HasDerivAt (fun u => d u k)
      ((-(lam k)) • d s k + R s k) s := by
    intro s k
    have h1 : HasDerivAt (fun u => c u (-k))
        ((-(ν * ‖freq (-k)‖ ^ 2)) • c s (-k) +
          lerayProj (-k) (convGal S (c s) (-k))) s := hODE s (-k)
    have hfneg : ‖freq (-k)‖ = ‖freq k‖ := by rw [freq_neg, norm_neg]
    rw [hfneg] at h1
    have h2 : HasDerivAt (fun u => conjVel (c u k))
        (conjVel ((-(ν * ‖freq k‖ ^ 2)) • c s k +
          lerayProj k (convGal S (c s) k))) s := by
      have := (conjVelL.hasFDerivAt (x := c s k)).comp_hasDerivAt s (hODE s k)
      exact this
    have h2' : HasDerivAt (fun u => conjVel (c u k))
        ((-(ν * ‖freq k‖ ^ 2)) • conjVel (c s k) +
          conjVel (lerayProj k (convGal S (c s) k))) s := by
      rwa [conjVel_add, conjVel_real_smul] at h2
    have h3 := h1.sub h2'
    have hval : ((-(ν * ‖freq k‖ ^ 2)) • c s (-k) +
          lerayProj (-k) (convGal S (c s) (-k))) -
        ((-(ν * ‖freq k‖ ^ 2)) • conjVel (c s k) +
          conjVel (lerayProj k (convGal S (c s) k))) =
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
    rw [hsupp s (-k) (hSnot k hk), hsupp s k hk, conjVel_zero, sub_zero]
  have hd0 : ∀ k, d 0 k = 0 := by
    intro k
    rw [hd]
    simp only
    rw [h0real k, sub_self]
  -- per-target-time interval argument
  intro t k
  have hle : -|t| ≤ 0 := neg_nonpos.mpr (abs_nonneg t)
  have hge : (0:ℝ) ≤ |t| := abs_nonneg t
  have htmem : t ∈ Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  -- bound the field on the compact window
  obtain ⟨M, hM0, hMb⟩ : ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc (-|t|) (|t|), ∀ j, ‖c s j‖ ≤ M := by
    have hmode : ∀ j, Continuous fun s : ℝ => c s j := fun j =>
      continuous_iff_continuousAt.mpr fun s => (hODE s j).continuousAt
    have hcont : Continuous fun s : ℝ => ∑ j ∈ S, ‖c s j‖ :=
      continuous_finsetSum S fun j _ => (hmode j).norm
    have hne : (Icc (-|t|) (|t|)).Nonempty := ⟨0, hle, hge⟩
    obtain ⟨s₀, hs₀, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn hne hcont.continuousOn
    refine ⟨∑ j ∈ S, ‖c s₀ j‖,
      Finset.sum_nonneg fun j _ => norm_nonneg _, ?_⟩
    intro s hs j
    by_cases hj : j ∈ S
    · calc ‖c s j‖ ≤ ∑ i ∈ S, ‖c s i‖ :=
            Finset.single_le_sum (f := fun i => ‖c s i‖)
              (fun i _ => norm_nonneg _) hj
        _ ≤ ∑ i ∈ S, ‖c s₀ i‖ := hmax hs
    · rw [hsupp s j hj]
      simp only [norm_zero]
      exact Finset.sum_nonneg fun i _ => norm_nonneg _
  -- the Lipschitz constant from the forcing bound
  obtain ⟨C, hC0, hCb⟩ := defect_forcing_bound hSsym
  have hRb : ∀ s ∈ Icc (-|t|) (|t|), ∀ j ∈ S,
      ‖R s j‖ ^ 2 ≤ (C * M ^ 2) * (∑ i ∈ S, ‖d s i‖ ^ 2) := by
    intro s hs j _
    have := hCb (c := c s) (hsupp s) hM0 (fun i => hMb s hs i) j
    simpa [hR, hd] using this
  have := defect_vanishes_on (mul_nonneg hC0 (by positivity)) hle hge hlamnn
    hdderiv hdsupp hRb hd0 t htmem k
  -- unfold the defect vanishing into the reality statement
  have hz : c t (-k) - conjVel (c t k) = 0 := this
  exact sub_eq_zero.mp hz


/-- **M4 wave-4 capstone: the finite-mode Navier-Stokes trap with ALL
dynamical hypotheses at time zero.**  Real, divergence-free, small initial
data; the standard divergence-free spectral Galerkin ODE; reality and
divergence-freeness both PROPAGATE. -/
theorem ns_galerkin_trap_zero_data :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → (∀ k ∈ S, -k ∈ S) → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t k, k ∉ S → c t k = 0) →
      RealField (c 0) → DivFree (c 0) →
      (∀ t k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨κ, hκ, htrap⟩ := ns_galerkin_trap_leray'
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 hSsym c hsupp h0real h0div hODE h0
  exact htrap hν hS0 hsupp
    (realField_propagates hν hSsym hsupp hODE h0real) h0div hODE h0

end TheoremB
