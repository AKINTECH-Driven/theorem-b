/-
# The physical calibration of the viscous term (Tier 6, wave W6)

The capstone `theorem_B_smooth` states the equation with its right-hand side
in synthesized spectral form.  This file makes the VISCOUS half genuinely
classical: the second fiber derivatives of the velocity field exist, their
sum over the three coordinate directions is the Laplacian, and the campaign's
viscous term is exactly

  `-(ν‖k‖²)`-weighted sum  =  `(ν / (2π)²) · Δu`,

so the physical viscosity of the lifted field is `ν_phys = ν / (2π)²`.

CAREFUL — this is NOT numerically the same factor Tier 5 records for the
weak form.  There the calibration is computed for a RESCALED family (a time
rescale `μ = 2π` alongside the space scaling), and the factors displayed
there reflect that rescaling.  Here the lift carries the campaign's own time
variable with no rescaling at all, and the constant is read directly off the
pointwise spatial derivatives.  The two are calibrations of two different
objects and must not be conflated or quoted interchangeably.

Route: the frequency twist `twistFreq i c k = (2πi·kᵢ)·c k` is again a
`Vel`-valued family, so PeriodicLift's first-derivative brick
`hasDerivAt_charSum_insertNth` applies to it AGAIN — the second derivative
is the first derivative of the twisted family, with no new analysis.  The
coefficient identity `∑ᵢ (2πi·kᵢ)² = -(2π)²‖freq k‖²` is what turns three
directional second derivatives into one Laplacian.

SCOPE: this file calibrates the VISCOUS term only.  The nonlinear term stays
in Leray-projected spectral form; the Leray projection is nonlocal, and
writing it classically requires constructing the pressure, which is NOT done
here and is NOT claimed anywhere.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.PeriodicLift
import TheoremB.TimeLayer

namespace TheoremB

open Set UnitAddTorus

noncomputable section

/-! ## The frequency twist -/

/-- Multiplication of a coefficient family by the `i`-th derivative symbol
`2πi·kᵢ`.  Crucially this is again a `Vel`-valued family, so the
first-derivative brick can be applied to it a second time. -/
def twistFreq (i : Fin 3) (c : (Fin 3 → ℤ) → Vel) : (Fin 3 → ℤ) → Vel :=
  fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • c k

lemma twistFreq_apply (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) :
    (twistFreq i c) k j = (2 * Real.pi * Complex.I * (k i : ℂ)) * c k j := rfl

/-- The coordinate bound `|kᵢ| ≤ ‖freq k‖` on the Euclidean lattice. -/
lemma abs_coord_le_norm_freq (k : Fin 3 → ℤ) (i : Fin 3) :
    |(k i : ℝ)| ≤ ‖freq k‖ := by
  have h := PiLp.norm_apply_le (freq k) i
  have h2 : ‖freq k i‖ = |(k i : ℝ)| := rfl
  rw [h2] at h
  exact h

lemma norm_twistFreq_le (i : Fin 3) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) :
    ‖twistFreq i c k‖ ≤ 2 * Real.pi * (‖freq k‖ * ‖c k‖) := by
  have hπ : (0:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have hnorm : ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ = 2 * Real.pi * |(k i : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
    have e1 : ‖(2 : ℂ)‖ = 2 := by simp
    have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
    have e4 : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by simp
    rw [e1, e2, e4]
    ring
  calc ‖twistFreq i c k‖ = ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ * ‖c k‖ := norm_smul _ _
    _ = 2 * Real.pi * |(k i : ℝ)| * ‖c k‖ := by rw [hnorm]
    _ ≤ 2 * Real.pi * ‖freq k‖ * ‖c k‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_coord_le_norm_freq k i) hπ) (norm_nonneg _)
    _ = 2 * Real.pi * (‖freq k‖ * ‖c k‖) := by ring

/-- The twist costs exactly one weighted ℓ¹ order. -/
lemma summable_twistFreq {q : ℕ} (i : Fin 3) {c : (Fin 3 → ℤ) → Vel}
    (h : Summable fun k => ‖freq k‖ ^ (q + 1) * ‖c k‖) :
    Summable fun k => ‖freq k‖ ^ q * ‖twistFreq i c k‖ := by
  refine (h.mul_left (2 * Real.pi)).of_nonneg_of_le (fun k => by positivity) fun k => ?_
  calc ‖freq k‖ ^ q * ‖twistFreq i c k‖
      ≤ ‖freq k‖ ^ q * (2 * Real.pi * (‖freq k‖ * ‖c k‖)) :=
        mul_le_mul_of_nonneg_left (norm_twistFreq_le i c k) (by positivity)
    _ = 2 * Real.pi * (‖freq k‖ ^ (q + 1) * ‖c k‖) := by rw [pow_succ]; ring

/-! ## The Laplacian coefficient identity -/

lemma norm_freq_sq (k : Fin 3 → ℤ) : ‖freq k‖ ^ 2 = ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  rw [norm_freq, Real.sq_sqrt (by positivity)]

/-- **The three derivative symbols square to the Laplacian symbol**:
`∑ᵢ (2πi·kᵢ)² = -(2π)²‖freq k‖²`.  This is the whole content of "the sum of
the second coordinate derivatives is the Laplacian". -/
lemma laplacian_symbol (k : Fin 3 → ℤ) :
    (∑ i : Fin 3, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2)
      = ((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2) : ℝ) : ℂ) := by
  have hre : ((‖freq k‖ ^ 2 : ℝ) : ℂ) = ∑ i : Fin 3, ((k i : ℂ)) ^ 2 := by
    rw [norm_freq_sq]
    push_cast
    rfl
  calc (∑ i : Fin 3, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2)
      = ∑ i : Fin 3, ((2 * (Real.pi : ℂ)) ^ 2 * Complex.I ^ 2) * ((k i : ℂ)) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ((2 * (Real.pi : ℂ)) ^ 2 * Complex.I ^ 2) * ∑ i : Fin 3, ((k i : ℂ)) ^ 2 := by
        rw [Finset.mul_sum]
    _ = ((2 * (Real.pi : ℂ)) ^ 2 * Complex.I ^ 2) * ((‖freq k‖ ^ 2 : ℝ) : ℂ) := by
        rw [hre]
    _ = ((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2) : ℝ) : ℂ) := by
        rw [Complex.I_sq]
        push_cast
        ring

/-! ## The second fiber derivative -/

/-- **The second fiber derivative of the velocity field.**  The first
derivative of the character sum is the `twistFreq`-twisted character sum
(PeriodicLift's brick); applying that brick AGAIN to the twisted family gives
the second derivative, with symbol `(2πi·kᵢ)²`.  Two weighted ℓ¹ orders are
what it costs. -/
theorem hasDerivAt_charSum_insertNth_second (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖)
    (hc2 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ 2 * ‖c k‖) :
    ∀ (y : UnitAddTorus (Fin 2)) (t : ℝ),
      HasDerivAt
        (fun s : ℝ => ∑' k : Fin 3 → ℤ,
          ((2 * Real.pi * Complex.I * (k i : ℂ)) * c k j) •
            mFourier k (i.insertNth (↑s : UnitAddCircle) y))
        (∑' k : Fin 3 → ℤ,
          ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c k j) •
            mFourier k (i.insertNth (↑t : UnitAddCircle) y)) t := by
  intro y t
  -- the twisted family carries one order less
  have ht0 : Summable fun k : Fin 3 → ℤ => ‖twistFreq i c k‖ := by
    have := summable_twistFreq (q := 0) i (by simpa using hc1)
    simpa using this
  have ht1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖twistFreq i c k‖ := by
    have := summable_twistFreq (q := 1) i (by simpa using hc2)
    simpa using this
  have h := hasDerivAt_charSum_insertNth i j (twistFreq i c) ht1 ht0 y t
  -- rewrite both series through `twistFreq_apply`
  have e1 : (fun s : ℝ => ∑' k : Fin 3 → ℤ,
      (twistFreq i c) k j • mFourier k (i.insertNth (↑s : UnitAddCircle) y))
      = fun s : ℝ => ∑' k : Fin 3 → ℤ,
        ((2 * Real.pi * Complex.I * (k i : ℂ)) * c k j) •
          mFourier k (i.insertNth (↑s : UnitAddCircle) y) := by
    funext s
    exact tsum_congr fun k => by rw [twistFreq_apply]
  have e2 : (∑' k : Fin 3 → ℤ,
      ((2 * Real.pi * Complex.I * (k i : ℂ)) * (twistFreq i c) k j) •
        mFourier k (i.insertNth (↑t : UnitAddCircle) y))
      = ∑' k : Fin 3 → ℤ,
        ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c k j) •
          mFourier k (i.insertNth (↑t : UnitAddCircle) y) :=
    tsum_congr fun k => by rw [twistFreq_apply]; ring_nf
  rw [e1, e2] at h
  exact h

/-! ## The Laplacian, and the calibration of the viscous term -/

/-- **Summing the three second derivatives gives the Laplacian.**  The
directional symbols `(2πi·kᵢ)²` add up to `-(2π)²‖freq k‖²`, so the sum over
the coordinate directions of the second-derivative series is the Laplacian
series. -/
theorem laplacian_charSum (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc2 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ 2 * ‖c k‖)
    (z : UnitAddTorus (Fin 3)) :
    (∑ i : Fin 3, ∑' k : Fin 3 → ℤ,
        ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c k j) • mFourier k z)
      = ∑' k : Fin 3 → ℤ,
        (((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c k j) • mFourier k z := by
  have hsum : ∀ i : Fin 3, Summable fun k : Fin 3 → ℤ =>
      ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c k j) • mFourier k z := by
    intro i
    refine Summable.of_norm ((hc2.mul_left ((2 * Real.pi) ^ 2)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_)
    have hnormtw : ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ = 2 * Real.pi * |(k i : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
      have e1 : ‖(2 : ℂ)‖ = 2 := by simp
      have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
      have e4 : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by simp
      rw [e1, e2, e4]
      ring
    have h1 : ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ ≤ 2 * Real.pi * ‖freq k‖ := by
      rw [hnormtw]
      exact mul_le_mul_of_nonneg_left (abs_coord_le_norm_freq k i)
        (by linarith [Real.pi_pos])
    have h2 : ‖c k j‖ ≤ ‖c k‖ := PiLp.norm_apply_le (c k) j
    rw [norm_smul, norm_mFourier_apply, mul_one, norm_mul, norm_pow]
    calc ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ ^ 2 * ‖c k j‖
        ≤ (2 * Real.pi * ‖freq k‖) ^ 2 * ‖c k‖ :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2
            (norm_nonneg _) (by positivity)
      _ = (2 * Real.pi) ^ 2 * (‖freq k‖ ^ 2 * ‖c k‖) := by ring
  rw [← Summable.tsum_finsetSum (fun i _ => hsum i)]
  refine tsum_congr fun k => ?_
  rw [← Finset.sum_smul, ← Finset.sum_mul, laplacian_symbol k]

/-- **The calibration.**  The campaign's viscous term is the classical
Laplacian scaled by `ν / (2π)²`: the lifted field solves the equation with
PHYSICAL viscosity `ν_phys = ν / (2π)²`.  (Equivalently: to realise physical
viscosity `ν_phys`, run the spectral system at `ν = (2π)²·ν_phys`.) -/
theorem viscous_eq_laplacian (ν : ℝ) (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc2 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ 2 * ‖c k‖)
    (z : UnitAddTorus (Fin 3)) :
    (∑' k : Fin 3 → ℤ, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c k j) • mFourier k z)
      = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
        (∑ i : Fin 3, ∑' k : Fin 3 → ℤ,
          ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c k j) • mFourier k z) := by
  rw [laplacian_charSum j c hc2 z, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hcoef : ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ)
        * ((-((2 * Real.pi) ^ 2 * ‖freq k‖ ^ 2) : ℝ) : ℂ)
      = ((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    have hπ : ((2 * Real.pi) ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp
    try ring
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, hcoef]

end

end TheoremB
