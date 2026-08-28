/-
# Assembly helpers for the Galerkin limit (Tier 3)

Continuity and algebra of `dotR`/`lerayProj`/`convGal`, the vanishing of the
full convection's zero mode on divergence-free fields, finite-subsum energy
bounds, and the persistence of bounds, divergence-freeness, and reality
through mode-wise limits.
-/
import TheoremB.NSFull
import TheoremB.FlowBounds
import TheoremB.LimitPassage
import TheoremB.RealityProp

namespace TheoremB

open Set

/-! ### P1: continuity and algebra helpers for the assembly -/

lemma dotR_continuous (r : EuclideanSpace ℝ (Fin 3)) :
    Continuous fun v : Vel => dotR v r := by
  have h : (fun v : Vel => dotR v r) = fun v => inner ℂ (castCV r) v := by
    funext v
    exact dotR_eq_inner v r
  rw [h]
  exact continuous_const.inner continuous_id

lemma dotR_sub_left' (a b : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (a - b) r = dotR a r - dotR b r := by
  simp only [dotR, WithLp.ofLp_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma lerayProj_sub (k : Fin 3 → ℤ) (a b : Vel) :
    lerayProj k (a - b) = lerayProj k a - lerayProj k b := by
  simp only [lerayProj, dotR_sub_left', sub_div, sub_smul]
  abel

lemma lerayProj_continuous (k : Fin 3 → ℤ) : Continuous (lerayProj k) := by
  unfold lerayProj
  exact continuous_id.sub
    (((dotR_continuous (freq k)).div_const _).smul continuous_const)

/-- The zero mode of the full convection vanishes on divergence-free fields. -/
lemma convFull_zero_of_divFree {c : (Fin 3 → ℤ) → Vel} (hdiv : DivFree c) :
    convFull c 0 = 0 := by
  unfold convFull
  have hterm : ∀ l : Fin 3 → ℤ,
      (Complex.I * dotR (c l) (freq ((0:Fin 3 → ℤ) - l))) • c ((0:Fin 3 → ℤ) - l) = 0 := by
    intro l
    have h1 : freq ((0:Fin 3 → ℤ) - l) = -freq l := by
      rw [zero_sub, freq_neg]
    have h2 : dotR (c l) (freq ((0:Fin 3 → ℤ) - l)) = 0 := by
      rw [h1]
      have h3 : dotR (c l) (-freq l) = -dotR (c l) (freq l) := by
        simp only [dotR]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have : (-freq l).ofLp j = -(freq l).ofLp j := rfl
        rw [this]
        push_cast
        ring
      rw [h3, hdiv l, neg_zero]
    rw [h2, mul_zero, zero_smul]
  rw [tsum_congr hterm]
  simp

/-- The Galerkin convection is continuous along mode-continuous flows. -/
lemma continuousOn_convGal {T : ℝ} {S : Finset (Fin 3 → ℤ)}
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hc : ∀ l, ContinuousOn (fun s => c s l) (Icc (0:ℝ) T)) (k : Fin 3 → ℤ) :
    ContinuousOn (fun s => convGal S (c s) k) (Icc (0:ℝ) T) := by
  unfold convGal
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    refine ContinuousOn.neg ?_
    refine continuousOn_finsetSum S fun l _ => ?_
    refine ContinuousOn.smul ?_ (hc (k - l))
    refine ContinuousOn.mul continuousOn_const ?_
    exact ((dotR_continuous (freq (k - l))).comp_continuousOn (hc l))
  · simp only [if_neg hk]
    exact continuousOn_const

/-- Finite subsums of the energy are below the energy for supported fields. -/
lemma sum_sq_le_en {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (F : Finset (Fin 3 → ℤ)) :
    ∑ l ∈ F, ‖c l‖ ^ 2 ≤ en c := by
  have hsum : Summable fun l => ‖c l‖ ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
  exact hsum.sum_le_tsum F (fun l _ => sq_nonneg _)

lemma sum_wsq_le_ens {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (F : Finset (Fin 3 → ℤ)) :
    ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c l‖ ^ 2 ≤ ens c := by
  have hsum : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2 :=
    summable_of_ne_finset_zero (s := S) fun j hj => by rw [hsupp j hj]; simp
  exact hsum.sum_le_tsum F (fun l _ => by positivity)

/-! ### P2: bounds and structure survive the mode-wise limit -/

/-- Energy bound and summability in the limit, from uniform finite-sum bounds. -/
lemma en_limit_le {E : ℝ} {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hEn : ∀ n (F : Finset (Fin 3 → ℤ)), ∑ l ∈ F, ‖c n l‖ ^ 2 ≤ E)
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l))) :
    en g ≤ E ∧ Summable fun l => ‖g l‖ ^ 2 := by
  have hF : ∀ F : Finset (Fin 3 → ℤ), ∑ l ∈ F, ‖g l‖ ^ 2 ≤ E := by
    intro F
    have htend : Filter.Tendsto (fun n => ∑ l ∈ F, ‖c n l‖ ^ 2) Filter.atTop
        (nhds (∑ l ∈ F, ‖g l‖ ^ 2)) := by
      refine tendsto_finsetSum F fun l _ => ?_
      exact ((hpt l).norm).pow 2
    exact le_of_tendsto' htend fun n => hEn n F
  exact ⟨Real.tsum_le_of_sum_le (fun l => sq_nonneg _) hF,
    summable_of_sum_le (fun l => sq_nonneg _) hF⟩

/-- Enstrophy bound and summability in the limit. -/
lemma ens_limit_le {Z : ℝ} {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hZn : ∀ n (F : Finset (Fin 3 → ℤ)), ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c n l‖ ^ 2 ≤ Z)
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l))) :
    ens g ≤ Z ∧ Summable fun l => ‖freq l‖ ^ 2 * ‖g l‖ ^ 2 := by
  have hF : ∀ F : Finset (Fin 3 → ℤ), ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖g l‖ ^ 2 ≤ Z := by
    intro F
    have htend : Filter.Tendsto (fun n => ∑ l ∈ F, ‖freq l‖ ^ 2 * ‖c n l‖ ^ 2)
        Filter.atTop (nhds (∑ l ∈ F, ‖freq l‖ ^ 2 * ‖g l‖ ^ 2)) := by
      refine tendsto_finsetSum F fun l _ => ?_
      exact Filter.Tendsto.const_mul _ (((hpt l).norm).pow 2)
    exact le_of_tendsto' htend fun n => hZn n F
  exact ⟨Real.tsum_le_of_sum_le (fun l => by positivity) hF,
    summable_of_sum_le (fun l => by positivity) hF⟩

/-- Divergence-freeness survives mode-wise limits. -/
lemma divFree_limit {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hdiv : ∀ n, DivFree (c n))
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l))) :
    DivFree g := by
  intro k
  have htend : Filter.Tendsto (fun n => dotR (c n k) (freq k)) Filter.atTop
      (nhds (dotR (g k) (freq k))) :=
    ((dotR_continuous (freq k)).tendsto _).comp (hpt k)
  have hconst : (fun n => dotR (c n k) (freq k)) = fun _ => (0:ℂ) :=
    funext fun n => hdiv n k
  rw [hconst] at htend
  exact (tendsto_nhds_unique tendsto_const_nhds htend).symm

/-- Reality survives mode-wise limits. -/
lemma realField_limit {c : ℕ → (Fin 3 → ℤ) → Vel} {g : (Fin 3 → ℤ) → Vel}
    (hreal : ∀ n, RealField (c n))
    (hpt : ∀ l, Filter.Tendsto (fun n => c n l) Filter.atTop (nhds (g l))) :
    RealField g := by
  intro k
  have htend : Filter.Tendsto (fun n => conjVel (c n k)) Filter.atTop
      (nhds (conjVel (g k))) := by
    have hc : Continuous conjVel := by
      have : (conjVel : Vel → Vel) = fun v => conjVelL v := by
        funext v
        exact (conjVelL_apply v).symm
      rw [this]
      exact conjVelL.continuous
    exact (hc.tendsto _).comp (hpt k)
  have htend' : Filter.Tendsto (fun n => c n (-k)) Filter.atTop
      (nhds (conjVel (g k))) := by
    refine htend.congr fun n => ?_
    exact (hreal n k).symm
  exact tendsto_nhds_unique (hpt (-k)) htend'

end TheoremB
