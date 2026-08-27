/-
  TheoremB/NSGalerkin.lean
  M4 wave 3 of the Theorem B campaign (27 Aug 2026).

  THE CONCRETE CONVECTION, and the campaign's first unconditional dynamical
  statements: small-data enstrophy traps for finite-mode Navier-Stokes
  dynamics, in three forms of increasing physical fidelity (see below).

  Value space Vel = EuclideanSpace C (Fin 3).  The projected spectral
  convection convGal keeps the prefactor -I (the 2*pi is a positive scalar
  absorbed by nondimensionalization; the I must stay -- with an I-free
  normalization the energy pairing vanishes WITHOUT divergence-freeness,
  i.e., it is a different, unphysical trilinear form).

  convGal_energy_pairing: for real divergence-free finitely supported
  fields, the energy pairing of the convection vanishes EXACTLY (the proof
  shows the full complex sum is 0: bilinear reduction via reality, the
  shear and twist reindexes of the pair lattice, p-q symmetrization, and
  incompressibility at -(p+q)).

  convGal_enstrophy_pairing: the vortex-stretching pairing is dominated by
  2 * triMaj with constant exactly 2 (re <= norm, Cauchy-Schwarz twice,
  and the (k,l) -> (l, k-l) bijection matching the majorant termwise).

  ns_galerkin_trap: composing both through galerkin_conditional_trap --
  for flows with support in a box S (0 not in S), real and divergence-free
  at every time, obeying c' = -nu*|k|^2*c + convGal S c: there is a
  UNIFORM constant kappa with: small data kappa*E0*Z0 < nu^4 implies the
  smallness persists and E, Z never exceed their initial values, on the
  whole lifespan.  No conditional hypotheses remain at the Galerkin level.
  THREE CAPSTONES (audit-calibrated scoping):
  - ns_galerkin_trap: the PRESSURELESS truncation.  Its ODE omits the
    per-mode Leray projector, so divergence-freeness is hypothesized along
    the flow rather than propagated; jointly with the ODE this restricts to
    the zero-Galerkin-pressure trajectories (a nonempty class: linear decay
    witnesses; nonlinearly active members are not constructed here).
  - ns_galerkin_trap_leray: the Leray-projected (pressure-carrying) system,
    divergence-freeness still hypothesized along the flow.
  - ns_galerkin_trap_leray': the physically honest form.  The standard
    divergence-free spectral Galerkin ODE, with div-freeness assumed ONLY
    at t = 0 and PROVED to propagate (divFree_propagates: each mode's
    divergence component obeys a homogeneous linear scalar ODE, killed by
    an exponential integrating factor).
  In all three, existence of the flow is quantified over, not constructed
  (the Galerkin ODE is Picard-Lindelof-solvable, but that is outside this
  file's scope).  Physical units: this system is verbatim the Galerkin-NS
  dynamics on the side-2*pi torus in the e^{i k.x} convention (same nu, no
  rescaling); equivalently, unit-torus physical NS after the time rescaling
  tau = 2*pi*t with nu-tilde = 2*pi*nu, legal since kappa is uniform in nu.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.GalerkinTrap

namespace TheoremB

open Set

-- the concrete velocity-coefficient space
abbrev Vel := EuclideanSpace ℂ (Fin 3)


/-- Componentwise complex conjugation on velocity values. -/
def conjVel (v : Vel) : Vel := WithLp.toLp 2 fun j => (starRingEnd ℂ) (v.ofLp j)

/-- The ℝ-vector cast into `Vel`. -/
noncomputable def castCV (r : EuclideanSpace ℝ (Fin 3)) : Vel :=
  WithLp.toLp 2 fun j => (r.ofLp j : ℂ)

/-- Pairing of a velocity value against a real frequency vector (bilinear, no conj). -/
noncomputable def dotR (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∑ j, v.ofLp j * (r.ofLp j : ℂ)

lemma norm_conjVel (v : Vel) : ‖conjVel v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [conjVel]

lemma conjVel_conjVel (v : Vel) : conjVel (conjVel v) = v := by
  ext j
  simp [conjVel]

lemma norm_castCV (r : EuclideanSpace ℝ (Fin 3)) : ‖castCV r‖ = ‖r‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [castCV]

lemma dotR_eq_inner (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR v r = inner ℂ (castCV r) v := by
  simp only [dotR, castCV, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Complex.conj_ofReal, mul_comm]

lemma norm_dotR_le (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    ‖dotR v r‖ ≤ ‖r‖ * ‖v‖ := by
  rw [dotR_eq_inner, ← norm_castCV r]
  exact norm_inner_le_norm (𝕜 := ℂ) _ _

/-- `freq` is additive-negation compatible. -/
lemma freq_neg (k : Fin 3 → ℤ) : freq (-k) = -freq k := by
  ext j
  simp [freq]

lemma freq_sub (k l : Fin 3 → ℤ) : freq (k - l) = freq k - freq l := by
  ext j
  simp [freq]

/-! ## The projected spectral convection and the physical field classes -/

/-- The Galerkin-projected spectral convection of a coefficient field. -/
noncomputable def convGal (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel)
    (k : Fin 3 → ℤ) : Vel :=
  if k ∈ S then -∑ l ∈ S, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) else 0

/-- Reality: the coefficient field of a real velocity field. -/
def RealField (c : (Fin 3 → ℤ) → Vel) : Prop := ∀ k, c (-k) = conjVel (c k)

/-- Spectral divergence-freeness. -/
def DivFree (c : (Fin 3 → ℤ) → Vel) : Prop := ∀ k, dotR (c k) (freq k) = 0

-- ==================== Agent ENERGY: energy-pairing vanishing ====================

/-- `freq` is additive. -/
private lemma freq_add (k l : Fin 3 → ℤ) : freq (k + l) = freq k + freq l := by
  ext j
  simp [freq]

/-- `dotR` kills the zero velocity. -/
private lemma eDotR_zero_left (r : EuclideanSpace ℝ (Fin 3)) : dotR 0 r = 0 := by
  simp [dotR]

/-- `dotR` is odd in the real slot. -/
private lemma eDotR_neg_right (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR v (-r) = -dotR v r := by
  simp [dotR, mul_neg, Finset.sum_neg_distrib]

/-- `dotR` is additive in the real slot. -/
private lemma eDotR_add_right (v : Vel) (r s : EuclideanSpace ℝ (Fin 3)) :
    dotR v (r + s) = dotR v r + dotR v s := by
  simp [dotR, mul_add, Finset.sum_add_distrib]

/-- Conjugating `dotR` against a real vector conjugates the velocity slot. -/
private lemma eConj_dotR (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (dotR v r) = dotR (conjVel v) r := by
  simp only [dotR]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1

/-- The real inner product on `Vel` is the real part of the complex one. -/
private lemma eRealInner_eq_re (x y : Vel) :
    inner ℝ x y = (inner ℂ x y).re :=
  (real_inner_eq_re_inner ℂ x y).trans RCLike.re_to_complex

/-- The complex inner product on `Vel`, written out componentwise. -/
private lemma eInner_apply (v w : Vel) :
    inner ℂ v w = ∑ j, (starRingEnd ℂ) (v.ofLp j) * w.ofLp j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, mul_comm]

/-- The conjugation-free bilinear pairing of two coefficients. -/
private noncomputable def eBform (c : (Fin 3 → ℤ) → Vel) (x y : Fin 3 → ℤ) : ℂ :=
  ∑ j, (c x).ofLp j * (c y).ofLp j

private lemma eBform_comm (c : (Fin 3 → ℤ) → Vel) (x y : Fin 3 → ℤ) :
    eBform c x y = eBform c y x := by
  simp only [eBform]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private lemma eBform_zero_left {c : (Fin 3 → ℤ) → Vel} {x : Fin 3 → ℤ}
    (hx : c x = 0) (y : Fin 3 → ℤ) : eBform c x y = 0 := by
  simp [eBform, hx]

private lemma eBform_zero_right {c : (Fin 3 → ℤ) → Vel} {y : Fin 3 → ℤ}
    (hy : c y = 0) (x : Fin 3 → ℤ) : eBform c x y = 0 := by
  simp [eBform, hy]

/-- For a real field, the sesquilinear inner product is the bilinear form at a negated index. -/
private lemma eInner_eq_Bform {c : (Fin 3 → ℤ) → Vel} (hreal : RealField c)
    (x y : Fin 3 → ℤ) : inner ℂ (c x) (c y) = eBform c (-x) y := by
  rw [eInner_apply]
  simp [eBform, hreal x, conjVel]

-- ==================== reindexing bijections of the pair lattice ====================

private def eShear : ((Fin 3 → ℤ) × (Fin 3 → ℤ)) ≃ ((Fin 3 → ℤ) × (Fin 3 → ℤ)) where
  toFun q := (q.1 + q.2, q.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv := fun ⟨a, b⟩ => by
    show (a, a + b - a) = (a, b)
    rw [add_sub_cancel_left]
  right_inv := fun ⟨a, b⟩ => by
    show (b + (a - b), b) = (a, b)
    congr 1
    abel

private lemma eShear_apply (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    eShear q = (q.1 + q.2, q.1) := rfl

private def eNegFst : ((Fin 3 → ℤ) × (Fin 3 → ℤ)) ≃ ((Fin 3 → ℤ) × (Fin 3 → ℤ)) where
  toFun q := (-q.1, q.2)
  invFun q := (-q.1, q.2)
  left_inv := fun ⟨a, b⟩ => by
    show (-(-a), b) = (a, b)
    rw [neg_neg]
  right_inv := fun ⟨a, b⟩ => by
    show (-(-a), b) = (a, b)
    rw [neg_neg]

private lemma eNegFst_apply (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    eNegFst q = (-q.1, q.2) := rfl

private def eTwist : ((Fin 3 → ℤ) × (Fin 3 → ℤ)) ≃ ((Fin 3 → ℤ) × (Fin 3 → ℤ)) where
  toFun q := (-(q.1 + q.2), -q.1)
  invFun q := (-q.2, q.2 - q.1)
  left_inv := fun ⟨a, b⟩ => by
    show (-(-a), -a - -(a + b)) = (a, b)
    congr 1 <;> abel
  right_inv := fun ⟨a, b⟩ => by
    show (-(-b + (b - a)), -(-b)) = (a, b)
    congr 1 <;> abel

private lemma eTwist_apply (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    eTwist q = (-(q.1 + q.2), -q.1) := rfl

private def eSwap : ((Fin 3 → ℤ) × (Fin 3 → ℤ)) ≃ ((Fin 3 → ℤ) × (Fin 3 → ℤ)) where
  toFun q := (q.2, q.1)
  invFun q := (q.2, q.1)
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

private lemma eSwap_apply (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    eSwap q = (q.2, q.1) := rfl

-- ==================== the pairing kernels along the reindexing chain ====================

/-- Raw kernel: term `(k, l)` of the expanded energy pairing. -/
private noncomputable def eGker (c : (Fin 3 → ℤ) → Vel)
    (p : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : ℂ :=
  (starRingEnd ℂ) (Complex.I * dotR (c p.2) (freq (p.1 - p.2))) *
    inner ℂ (c (p.1 - p.2)) (c p.1)

/-- Kernel after the shear `(l, m) ↦ (l + m, l)`. -/
private noncomputable def eF0 (c : (Fin 3 → ℤ) → Vel)
    (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : ℂ :=
  (starRingEnd ℂ) (Complex.I * dotR (c q.1) (freq q.2)) *
    inner ℂ (c q.2) (c (q.1 + q.2))

/-- Kernel after negating the first index and applying the reality rewrites. -/
private noncomputable def eGmid (c : (Fin 3 → ℤ) → Vel)
    (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : ℂ :=
  (-Complex.I * dotR (c q.1) (freq q.2)) * eBform c (-q.2) (q.2 - q.1)

/-- Kernel after the twist `(p, q) ↦ (-(p+q), -p)`. -/
private noncomputable def eH1 (c : (Fin 3 → ℤ) → Vel)
    (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : ℂ :=
  (Complex.I * dotR (c (-(q.1 + q.2))) (freq q.1)) * eBform c q.1 q.2

/-- The swap partner of `eH1`. -/
private noncomputable def eH2 (c : (Fin 3 → ℤ) → Vel)
    (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : ℂ :=
  (Complex.I * dotR (c (-(q.1 + q.2))) (freq q.2)) * eBform c q.1 q.2

/-- Incompressibility kills each combined pair term. -/
private lemma ePairCancel {c : (Fin 3 → ℤ) → Vel} (hdiv : DivFree c)
    (q : (Fin 3 → ℤ) × (Fin 3 → ℤ)) : eH1 c q + eH2 c q = 0 := by
  have h0 : dotR (c (-(q.1 + q.2))) (freq (q.1 + q.2)) = 0 := by
    have h := hdiv (-(q.1 + q.2))
    rw [freq_neg, eDotR_neg_right, neg_eq_zero] at h
    exact h
  have hsum : dotR (c (-(q.1 + q.2))) (freq q.1) + dotR (c (-(q.1 + q.2))) (freq q.2) = 0 := by
    rw [← eDotR_add_right, ← freq_add]
    exact h0
  simp only [eH1, eH2]
  calc (Complex.I * dotR (c (-(q.1 + q.2))) (freq q.1)) * eBform c q.1 q.2
        + (Complex.I * dotR (c (-(q.1 + q.2))) (freq q.2)) * eBform c q.1 q.2
      = Complex.I * ((dotR (c (-(q.1 + q.2))) (freq q.1)
          + dotR (c (-(q.1 + q.2))) (freq q.2)) * eBform c q.1 q.2) := by ring
    _ = 0 := by rw [hsum, zero_mul, mul_zero]

-- ==================== the energy-pairing vanishing ====================

theorem convGal_energy_pairing {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hreal : RealField c) (hdiv : DivFree c) :
    (∑ k ∈ S, 2 * inner ℝ (convGal S c k) (c k)) = 0 := by
  -- expand the Galerkin convolution inside the pairing
  have hstep : ∀ k ∈ S, inner ℂ (convGal S c k) (c k) = -∑ l ∈ S, eGker c (k, l) := by
    intro k hk
    simp only [convGal]
    rw [if_pos hk, inner_neg_left, sum_inner, neg_inj]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left]
    rfl
  have h1 : (∑ k ∈ S, inner ℂ (convGal S c k) (c k)) = -∑ p ∈ S ×ˢ S, eGker c p := by
    rw [Finset.sum_product, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hstep
  -- vanishing off the support square
  have hg0 : ∀ p ∉ S ×ˢ S, eGker c p = 0 := by
    intro p hp
    by_cases hp1 : p.1 ∈ S
    · have hp2 : p.2 ∉ S := fun h2 => hp (Finset.mem_product.mpr ⟨hp1, h2⟩)
      simp [eGker, hsupp p.2 hp2, eDotR_zero_left]
    · simp [eGker, hsupp p.1 hp1]
  have hH10 : ∀ p ∉ S ×ˢ S, eH1 c p = 0 := by
    intro p hp
    by_cases hp1 : p.1 ∈ S
    · have hp2 : p.2 ∉ S := fun h2 => hp (Finset.mem_product.mpr ⟨hp1, h2⟩)
      simp [eH1, eBform_zero_right (hsupp p.2 hp2)]
    · simp [eH1, eBform_zero_left (hsupp p.1 hp1)]
  have hH20 : ∀ p ∉ S ×ˢ S, eH2 c p = 0 := by
    intro p hp
    by_cases hp1 : p.1 ∈ S
    · have hp2 : p.2 ∉ S := fun h2 => hp (Finset.mem_product.mpr ⟨hp1, h2⟩)
      simp [eH2, eBform_zero_right (hsupp p.2 hp2)]
    · simp [eH2, eBform_zero_left (hsupp p.1 hp1)]
  -- finite sum = tsum
  have e0 : (∑' p, eGker c p) = ∑ p ∈ S ×ˢ S, eGker c p := tsum_eq_sum hg0
  -- shear reindex (k, l) ↦ (l, m)
  have e1 : (∑' p, eGker c p) = ∑' q, eF0 c q := by
    rw [← eShear.tsum_eq (eGker c)]
    refine tsum_congr fun q => ?_
    rw [eShear_apply]
    simp only [eGker, eF0, add_sub_cancel_left]
  -- negate the first index and apply the reality rewrites
  have e2 : (∑' q, eF0 c q) = ∑' q, eGmid c q := by
    rw [← eNegFst.tsum_eq (eF0 c)]
    refine tsum_congr fun q => ?_
    rw [eNegFst_apply]
    simp only [eF0, eGmid]
    rw [map_mul, Complex.conj_I, eConj_dotR, hreal q.1, conjVel_conjVel,
      eInner_eq_Bform hreal, neg_add_eq_sub]
  -- twist reindex (l, m) ↦ (-(l+m), -l)
  have e3 : (∑' q, eGmid c q) = ∑' q, eH1 c q := by
    rw [← eTwist.tsum_eq (eGmid c)]
    refine tsum_congr fun q => ?_
    rw [eTwist_apply]
    simp only [eGmid, eH1]
    rw [freq_neg, eDotR_neg_right, neg_neg,
      show (-q.1) - (-(q.1 + q.2)) = q.2 from by abel]
    ring
  -- swap the two indices
  have e4 : (∑' q, eH1 c q) = ∑' q, eH2 c q := by
    rw [← eSwap.tsum_eq (eH1 c)]
    refine tsum_congr fun q => ?_
    rw [eSwap_apply]
    simp only [eH1, eH2]
    rw [add_comm q.2 q.1, eBform_comm c q.2 q.1]
  -- combine the two copies and cancel by incompressibility
  have hadd : (∑' q, (eH1 c q + eH2 c q)) = (∑' q, eH1 c q) + (∑' q, eH2 c q) :=
    Summable.tsum_add (summable_of_ne_finset_zero hH10) (summable_of_ne_finset_zero hH20)
  have hzero : (∑' q, (eH1 c q + eH2 c q)) = 0 := by
    calc (∑' q, (eH1 c q + eH2 c q))
        = ∑' (_ : (Fin 3 → ℤ) × (Fin 3 → ℤ)), (0 : ℂ) := tsum_congr (ePairCancel hdiv)
      _ = 0 := tsum_zero
  have hT : (∑' q, eH1 c q) = 0 := by
    have h : (∑' q, eH1 c q) + (∑' q, eH2 c q) = 0 := by rw [← hadd, hzero]
    rw [← e4] at h
    exact add_self_eq_zero.mp h
  -- the whole complex pairing sum vanishes
  have hZ : (∑ k ∈ S, inner ℂ (convGal S c k) (c k)) = 0 := by
    rw [h1, ← e0, e1, e2, e3, hT, neg_zero]
  -- pass to the real pairing
  calc (∑ k ∈ S, 2 * inner ℝ (convGal S c k) (c k))
      = ∑ k ∈ S, 2 * (inner ℂ (convGal S c k) (c k)).re := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [eRealInner_eq_re]
    _ = 2 * (∑ k ∈ S, inner ℂ (convGal S c k) (c k)).re := by
        rw [← Finset.mul_sum, Complex.re_sum]
    _ = 0 := by rw [hZ, Complex.zero_re, mul_zero]

/-! ## Agent DOMIN: the enstrophy-pairing domination -/

/-- The generic summand of the collapsed majorant, indexed the triMaj way:
`a` is the outer (ℓ¹) mode, `b` the inner (gradient) mode, `a + b` the output mode. -/
private noncomputable def galG (c : (Fin 3 → ℤ) → Vel) (a b : Fin 3 → ℤ) : ℝ :=
  ‖c a‖ * (‖freq b‖ * ‖c b‖ * (‖freq (a + b)‖ ^ 2 * ‖c (a + b)‖))

private lemma galG_nonneg (c : (Fin 3 → ℤ) → Vel) (a b : Fin 3 → ℤ) : 0 ≤ galG c a b := by
  unfold galG; positivity

/-- The change of variables `(k, l) ↦ (l, k - l)` on the summand. -/
private lemma galG_shift (c : (Fin 3 → ℤ) → Vel) (k l : Fin 3 → ℤ) :
    galG c l (k - l) = ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖ * (‖freq k‖ ^ 2 * ‖c k‖)) := by
  unfold galG
  rw [show l + (k - l) = k by ring]

/-- Triangle-inequality bound on the Galerkin convection coefficient. -/
private lemma norm_convGal_le (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel)
    (k : Fin 3 → ℤ) :
    ‖convGal S c k‖ ≤ ∑ l ∈ S, ‖freq (k - l)‖ * ‖c l‖ * ‖c (k - l)‖ := by
  unfold convGal
  by_cases hk : k ∈ S
  · rw [if_pos hk, norm_neg]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
  · rw [if_neg hk, norm_zero]
    positivity

/-- Per-mode Cauchy–Schwarz bound on the convection pairing. -/
private lemma inner_convGal_le (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → Vel)
    (k : Fin 3 → ℤ) :
    inner ℝ (convGal S c k) (c k) ≤
      ∑ l ∈ S, ‖freq (k - l)‖ * ‖c l‖ * ‖c (k - l)‖ * ‖c k‖ := by
  calc inner ℝ (convGal S c k) (c k) ≤ ‖convGal S c k‖ * ‖c k‖ := real_inner_le_norm _ _
    _ ≤ (∑ l ∈ S, ‖freq (k - l)‖ * ‖c l‖ * ‖c (k - l)‖) * ‖c k‖ :=
        mul_le_mul_of_nonneg_right (norm_convGal_le S c k) (norm_nonneg _)
    _ = ∑ l ∈ S, ‖freq (k - l)‖ * ‖c l‖ * ‖c (k - l)‖ * ‖c k‖ := Finset.sum_mul _ _ _

/-- The `k ↦ k - l` reindexing is dominated by the untranslated sum: the translated
image sum only has nonzero terms where `c` lives, and there it sits inside `S`. -/
private lemma shift_sum_le {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (l : Fin 3 → ℤ) :
    (∑ k ∈ S, galG c l (k - l)) ≤ ∑ b ∈ S, galG c l b := by
  classical
  have himg : ∑ b ∈ Finset.image (fun k => k - l) S, galG c l b
      = ∑ k ∈ S, galG c l (k - l) :=
    Finset.sum_image fun x _ y _ h => sub_left_inj.mp h
  have hfil : ∑ b ∈ (Finset.image (fun k => k - l) S).filter (fun b => c b ≠ 0), galG c l b
      = ∑ b ∈ Finset.image (fun k => k - l) S, galG c l b := by
    refine Finset.sum_filter_of_ne fun b _ hgb => ?_
    intro hc
    exact hgb (by simp [galG, hc])
  have hsub : (Finset.image (fun k => k - l) S).filter (fun b => c b ≠ 0) ⊆ S := by
    intro b hb
    have hcb : c b ≠ 0 := (Finset.mem_filter.mp hb).2
    by_contra hbS
    exact hcb (hsupp b hbS)
  calc ∑ k ∈ S, galG c l (k - l)
      = ∑ b ∈ Finset.image (fun k => k - l) S, galG c l b := himg.symm
    _ = ∑ b ∈ (Finset.image (fun k => k - l) S).filter (fun b => c b ≠ 0), galG c l b :=
        hfil.symm
    _ ≤ ∑ b ∈ S, galG c l b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => galG_nonneg c l b

/-- Both tsums of the majorant collapse onto `S` (support of `c`), and reality
folds the `-(a+b)` mode onto `a+b`. -/
private lemma triMaj_collapse {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hreal : RealField c) :
    triMaj (fun k => ‖c k‖) (fun l => ‖c l‖) (fun m => ‖freq m‖ ^ 2 * ‖c m‖) =
      ∑ a ∈ S, ∑ b ∈ S, galG c a b := by
  have hcz : ∀ k, k ∉ S → ‖c k‖ = (0 : ℝ) := fun k hk => by rw [hsupp k hk, norm_zero]
  have hinner : ∀ a : Fin 3 → ℤ,
      (∑' l, ‖freq l‖ * ‖c l‖ * (‖freq (-(a + l))‖ ^ 2 * ‖c (-(a + l))‖)) =
        ∑ b ∈ S, ‖freq b‖ * ‖c b‖ * (‖freq (-(a + b))‖ ^ 2 * ‖c (-(a + b))‖) :=
    fun a => tsum_eq_sum fun l hl => by rw [hcz l hl, mul_zero, zero_mul]
  have houter :
      (∑' k, ‖c k‖ * ∑' l, ‖freq l‖ * ‖c l‖ * (‖freq (-(k + l))‖ ^ 2 * ‖c (-(k + l))‖)) =
        ∑ a ∈ S, ‖c a‖ * ∑' l, ‖freq l‖ * ‖c l‖ * (‖freq (-(a + l))‖ ^ 2 * ‖c (-(a + l))‖) :=
    tsum_eq_sum fun k hk => by rw [hcz k hk, zero_mul]
  calc triMaj (fun k => ‖c k‖) (fun l => ‖c l‖) (fun m => ‖freq m‖ ^ 2 * ‖c m‖)
      = ∑' k, ‖c k‖ * ∑' l, ‖freq l‖ * ‖c l‖ * (‖freq (-(k + l))‖ ^ 2 * ‖c (-(k + l))‖) := rfl
    _ = ∑ a ∈ S, ‖c a‖ * ∑' l, ‖freq l‖ * ‖c l‖ * (‖freq (-(a + l))‖ ^ 2 * ‖c (-(a + l))‖) :=
        houter
    _ = ∑ a ∈ S, ∑ b ∈ S, galG c a b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hinner a, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hreal (a + b), norm_conjVel, freq_neg, norm_neg]
        rfl

theorem convGal_enstrophy_pairing {S : Finset (Fin 3 → ℤ)} {c : (Fin 3 → ℤ) → Vel}
    (hsupp : ∀ k, k ∉ S → c k = 0) (hreal : RealField c) :
    (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S c k) (c k))) ≤
      2 * triMaj (fun k => ‖c k‖) (fun l => ‖c l‖) (fun m => ‖freq m‖ ^ 2 * ‖c m‖) := by
  have hstep : ∀ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S c k) (c k)) ≤
      2 * ∑ l ∈ S, galG c l (k - l) := by
    intro k _
    calc ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S c k) (c k))
        ≤ ‖freq k‖ ^ 2 * (2 * ∑ l ∈ S, ‖freq (k - l)‖ * ‖c l‖ * ‖c (k - l)‖ * ‖c k‖) := by
          have h2 : (2 : ℝ) * inner ℝ (convGal S c k) (c k)
              ≤ 2 * ∑ l ∈ S, ‖freq (k - l)‖ * ‖c l‖ * ‖c (k - l)‖ * ‖c k‖ :=
            mul_le_mul_of_nonneg_left (inner_convGal_le S c k) (by norm_num)
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * ∑ l ∈ S, galG c l (k - l) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [galG_shift]
          ring
  calc (∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S c k) (c k)))
      ≤ ∑ k ∈ S, 2 * ∑ l ∈ S, galG c l (k - l) := Finset.sum_le_sum hstep
    _ = 2 * ∑ l ∈ S, ∑ k ∈ S, galG c l (k - l) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * ∑ l ∈ S, ∑ b ∈ S, galG c l b :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun l _ => shift_sum_le hsupp l) (by norm_num)
    _ = 2 * triMaj (fun k => ‖c k‖) (fun l => ‖c l‖) (fun m => ‖freq m‖ ^ 2 * ‖c m‖) := by
        rw [triMaj_collapse hsupp hreal]

/-! ## The capstone: the finite-mode Navier-Stokes trap -/

/-- **M4 wave-3 capstone (pressureless form): the small-data enstrophy trap
for the pressureless spectral truncation.**  Divergence-freeness along the
flow is a hypothesis here (with the unprojected ODE it selects the
zero-Galerkin-pressure trajectories); see `ns_galerkin_trap_leray'` for the
pressure-carrying form with div-freeness assumed only at time zero. -/
theorem ns_galerkin_trap :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t k, k ∉ S → c t k = 0) →
      (∀ t, RealField (c t)) → (∀ t, DivFree (c t)) →
      (∀ t k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + convGal S (c t) k) t) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨κ, hκ, htrap⟩ := galerkin_conditional_trap (V := Vel)
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 c hsupp hreal hdiv hODE h0
  exact htrap hν hS0 hsupp hODE
    (fun t _ => le_of_eq (convGal_energy_pairing (hsupp t) (hreal t) (hdiv t)))
    (fun t _ => convGal_enstrophy_pairing (hsupp t) (hreal t))
    h0

/-! ## The Leray projection: pressure, and the physically honest capstones -/

/-- The mode-wise Leray projection: remove the component along the frequency. -/
noncomputable def lerayProj (k : Fin 3 → ℤ) (v : Vel) : Vel :=
  v - ((dotR v (freq k)) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) • castCV (freq k)

/-- Paired against a divergence-free mode, the Leray projection is invisible. -/
lemma inner_lerayProj_of_divFree {c : (Fin 3 → ℤ) → Vel} (hdiv : DivFree c)
    (k : Fin 3 → ℤ) (v : Vel) :
    inner ℝ (lerayProj k v) (c k) = inner ℝ v (c k) := by
  have hker : inner ℂ (castCV (freq k)) (c k) = 0 := by
    rw [← dotR_eq_inner]
    exact hdiv k
  have hC : inner ℂ (lerayProj k v) (c k) = inner ℂ v (c k) := by
    rw [lerayProj, inner_sub_left, inner_smul_left, hker, mul_zero, sub_zero]
  have e1 : inner ℝ (lerayProj k v) (c k) = (inner ℂ (lerayProj k v) (c k)).re :=
    (real_inner_eq_re_inner ℂ _ _).trans RCLike.re_to_complex
  have e2 : inner ℝ v (c k) = (inner ℂ v (c k)).re :=
    (real_inner_eq_re_inner ℂ _ _).trans RCLike.re_to_complex
  rw [e1, e2, hC]

/-- **The Leray-projected finite-mode Navier-Stokes trap.**  Same conclusion
as `ns_galerkin_trap`, for the pressure-carrying (Leray-projected) Galerkin
system — the standard divergence-free spectral formulation. -/
theorem ns_galerkin_trap_leray :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t k, k ∉ S → c t k = 0) →
      (∀ t, RealField (c t)) → (∀ t, DivFree (c t)) →
      (∀ t k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨κ, hκ, htrap⟩ := galerkin_conditional_trap (V := Vel)
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 c hsupp hreal hdiv hODE h0
  have hpair : ∀ t k, inner ℝ (lerayProj k (convGal S (c t) k)) (c t k) =
      inner ℝ (convGal S (c t) k) (c t k) := fun t k =>
    inner_lerayProj_of_divFree (hdiv t) k _
  refine htrap hν hS0 hsupp hODE ?_ ?_ h0
  · intro t ht
    have h := convGal_energy_pairing (hsupp t) (hreal t) (hdiv t)
    calc (∑ k ∈ S, 2 * inner ℝ (lerayProj k (convGal S (c t) k)) (c t k))
        = ∑ k ∈ S, 2 * inner ℝ (convGal S (c t) k) (c t k) :=
          Finset.sum_congr rfl fun k _ => by rw [hpair t k]
      _ ≤ 0 := le_of_eq h
  · intro t ht
    have h := convGal_enstrophy_pairing (hsupp t) (hreal t)
    calc (∑ k ∈ S, ‖freq k‖ ^ 2 *
          (2 * inner ℝ (lerayProj k (convGal S (c t) k)) (c t k)))
        = ∑ k ∈ S, ‖freq k‖ ^ 2 * (2 * inner ℝ (convGal S (c t) k) (c t k)) :=
          Finset.sum_congr rfl fun k _ => by rw [hpair t k]
      _ ≤ 2 * triMaj (fun k => ‖c t k‖) (fun l => ‖c t l‖)
            (fun m => ‖freq m‖ ^ 2 * ‖c t m‖) := h

/-- The Leray projection kills the frequency component of anything. -/
lemma dotR_lerayProj_freq (k : Fin 3 → ℤ) (v : Vel) :
    dotR (lerayProj k v) (freq k) = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · have h0 : freq (0 : Fin 3 → ℤ) = 0 := by
      ext j
      simp [freq]
    rw [h0]
    simp [dotR]
  · have hfk : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have hcast : dotR (castCV (freq k)) (freq k) = ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
      have h1 : ‖freq k‖ ^ 2 = ∑ j, ((freq k).ofLp j) ^ 2 := by
        rw [norm_freq, Real.sq_sqrt (by positivity)]
        rfl
      rw [dotR]
      push_cast [h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [castCV]
      ring
    have hlin_sub : ∀ q : ℂ, dotR (v - q • castCV (freq k)) (freq k) =
        dotR v (freq k) - q * dotR (castCV (freq k)) (freq k) := by
      intro q
      simp only [dotR, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    have hne : ((‖freq k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    rw [lerayProj, hlin_sub _, hcast, div_mul_cancel₀ _ hne, sub_self]

/-- **Divergence-freeness propagates under the Leray-projected ODE**: each
mode's divergence component solves a homogeneous scalar linear ODE, so it
stays zero if it starts zero. -/
lemma divFree_propagates {ν : ℝ} {S : Finset (Fin 3 → ℤ)}
    {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hODE : ∀ t k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t)
    (h0 : DivFree (c 0)) : ∀ t, DivFree (c t) := by
  intro t k
  -- the divergence component as a scalar history
  set lam : ℝ := ν * ‖freq k‖ ^ 2 with hlam
  set y : ℝ → ℂ := fun s => dotR (c s k) (freq k) with hy
  -- dotR (·, freq k) is ℂ-linear and continuous; transport the derivative
  have hdotlin : ∀ (a : Vel) (b : Vel),
      dotR (a + b) (freq k) = dotR a (freq k) + dotR b (freq k) := by
    intro a b
    simp [dotR, Finset.sum_add_distrib, add_mul]
  have hdotsmul : ∀ (z : ℝ) (a : Vel),
      dotR (z • a) (freq k) = (z : ℂ) * dotR a (freq k) := by
    intro z a
    simp [dotR, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hyderiv : ∀ s, HasDerivAt y (-(lam : ℂ) * y s) s := by
    intro s
    have h := hODE s k
    -- componentwise: y s = Σ_j (c s k)_j * r_j
    have hco : ∀ j : Fin 3, HasDerivAt (fun u => (c u k).ofLp j)
        (((-(lam)) • c s k + lerayProj k (convGal S (c s) k)).ofLp j) s := by
      intro j
      exact ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h
    have hterm : ∀ j : Fin 3, HasDerivAt
        (fun u => (c u k).ofLp j * (((freq k).ofLp j : ℝ) : ℂ))
        ((((-(lam)) • c s k + lerayProj k (convGal S (c s) k)).ofLp j) *
          (((freq k).ofLp j : ℝ) : ℂ)) s := fun j => (hco j).mul_const _
    have hsum := HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    have heq1 : (∑ j ∈ Finset.univ, fun u => (c u k).ofLp j *
        (((freq k).ofLp j : ℝ) : ℂ)) = y := by
      funext u
      simp [hy, dotR, Finset.sum_apply]
    rw [heq1] at hsum
    have heq2 : (∑ j, (((-(lam)) • c s k +
        lerayProj k (convGal S (c s) k)).ofLp j) * (((freq k).ofLp j : ℝ) : ℂ)) =
        -(lam : ℂ) * y s := by
      have : (∑ j, (((-(lam)) • c s k +
          lerayProj k (convGal S (c s) k)).ofLp j) * (((freq k).ofLp j : ℝ) : ℂ)) =
          dotR ((-(lam)) • c s k + lerayProj k (convGal S (c s) k)) (freq k) := rfl
      rw [this, hdotlin, hdotsmul, dotR_lerayProj_freq, add_zero, hy]
      push_cast
      ring
    rw [heq2] at hsum
    exact hsum
  -- exponential integrating factor: g := exp(lam·s) · y s is constant
  have hg : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Complex.exp ((lam : ℂ) * u) * y u) 0 s := by
    intro s
    have hexp : HasDerivAt (fun u : ℝ => Complex.exp ((lam : ℂ) * u))
        ((lam : ℂ) * Complex.exp ((lam : ℂ) * s)) s := by
      have hin : HasDerivAt (fun u : ℝ => ((lam : ℂ) * u)) (lam : ℂ) s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (lam : ℂ)
      have hout := Complex.hasDerivAt_exp ((lam : ℂ) * (s : ℝ))
      have hcomp := HasDerivAt.scomp s hout hin
      have hfun : (Complex.exp ∘ fun u : ℝ => ((lam : ℂ) * u)) =
          fun u : ℝ => Complex.exp ((lam : ℂ) * u) := rfl
      have hval : ((lam : ℂ)) • Complex.exp ((lam : ℂ) * (s : ℝ)) =
          (lam : ℂ) * Complex.exp ((lam : ℂ) * s) := smul_eq_mul _ _
      rw [hfun, hval] at hcomp
      exact hcomp
    have := hexp.mul (hyderiv s)
    have hz : (lam : ℂ) * Complex.exp ((lam : ℂ) * s) * y s +
        Complex.exp ((lam : ℂ) * s) * (-(lam : ℂ) * y s) = 0 := by ring
    rwa [hz] at this
  have hconst : ∀ s : ℝ, Complex.exp ((lam : ℂ) * s) * y s =
      Complex.exp ((lam : ℂ) * (0:ℝ)) * y 0 := by
    intro s
    have hdiff : ∀ u : ℝ, DifferentiableAt ℝ
        (fun u : ℝ => Complex.exp ((lam : ℂ) * u) * y u) u :=
      fun u => (hg u).differentiableAt
    exact is_const_of_deriv_eq_zero (fun u => hdiff u)
      (fun u => (hg u).deriv) s 0
  have hy0 : y 0 = 0 := h0 k
  have := hconst t
  rw [hy0, mul_zero] at this
  have hexp_ne : Complex.exp ((lam : ℂ) * t) ≠ 0 := Complex.exp_ne_zero _
  exact (mul_eq_zero.mp this).resolve_left hexp_ne

/-- **The physically honest capstone: the finite-mode Navier-Stokes trap
with pressure, divergence-freeness assumed only at time zero.** -/
theorem ns_galerkin_trap_leray' :
    ∃ κ, 0 < κ ∧ ∀ {T ν : ℝ}, 0 < ν → ∀ {S : Finset (Fin 3 → ℤ)},
      (0 : Fin 3 → ℤ) ∉ S → ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      (∀ t k, k ∉ S → c t k = 0) →
      (∀ t, RealField (c t)) → DivFree (c 0) →
      (∀ t k, HasDerivAt (fun s => c s k)
        ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convGal S (c t) k)) t) →
      κ * en (c 0) * ens (c 0) < ν ^ 4 →
      ∀ t ∈ Ico (0:ℝ) T,
        κ * en (c t) * ens (c t) < ν ^ 4 ∧
          ens (c t) ≤ ens (c 0) ∧ en (c t) ≤ en (c 0) := by
  obtain ⟨κ, hκ, htrap⟩ := ns_galerkin_trap_leray
  refine ⟨κ, hκ, ?_⟩
  intro T ν hν S hS0 c hsupp hreal hdiv0 hODE h0
  exact htrap hν hS0 hsupp hreal (divFree_propagates hODE hdiv0) hODE h0

end TheoremB
