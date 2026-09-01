/-
# The classical equation, compiled (audit landing, 2026-09-02)

`theorem_B_smooth_classical` exports nineteen clauses from which the classical
Navier-Stokes equation

    ∂ₜ u_j(t,x) = (ν/(2π)²)·(Δu)_j(t,x) − (1/2π)·((u·∇)u)_j(t,x) − (∂_j p)(t,x)

follows by an ASSEMBLY: split the spectral right-hand side (clause 13) into
its viscous, convective and pressure pieces and identify each with clauses
16, 19 and 18.  The audit of 2026-09-02 found that this assembly lived only
in prose.  This file lands it as compiled statements:

* `hasDerivAt_pressure_insertNth` — the pressure series
  `p(x) = ∑' k, pressureCoeff c k * mFourier k x` is differentiable along
  every coordinate fiber `i`, with derivative the gradient series
  `∑' k, (2πi·kᵢ)·pressureCoeff c k * mFourier k x`, under exactly the two
  certificates clause 17 exports.  This is what makes `∇p` a compiled object
  (a derivative, not a name for a series).  Proof: embed the scalar family
  into `Vel` along `EuclideanSpace.single 0 1` and read component `0` of
  `PeriodicLift.hasDerivAt_charSum_insertNth`.

* `theorem_B_smooth_classical_eq` — the capstone's flow, re-exporting all
  nineteen clauses verbatim, plus a twentieth: at every `j`, every torus
  point `x` and every `t > 0`, the velocity component is time-differentiable
  with derivative the three-piece classical right-hand side, written out in
  full (no local abbreviations, so the statement is self-contained and
  freezable).

The only non-clause inputs of the equation are `summable_norm_convFull`
(TimeLayer), `abs_coord_le_norm_freq` (Calibration), `norm_mFourier_apply`
(PeriodicLift) and Mathlib; nothing about the flow's construction is used.
The scope caveats of `TheoremBSmooth` (no analyticity, no `C^∞` in time,
campaign normalisation of the constants) apply unchanged.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.TheoremBSmooth

namespace TheoremB

open Set UnitAddTorus

/-! ## The pressure gradient is a derivative -/

/-- **The pressure gradient.**  For a pressure family that is ℓ¹ with one
weighted ℓ¹ order (exactly what clause 17 of `theorem_B_smooth_classical`
exports), the pressure series `∑' k, pressureCoeff c k * mFourier k x` is
differentiable along every coordinate fiber `i`, with derivative the
`2πi·kᵢ`-twisted series — the `i`-th component of `∇p`.

The scalar family is lifted to `Vel` along `EuclideanSpace.single 0 1` so
that the PeriodicLift brick `hasDerivAt_charSum_insertNth` applies verbatim;
component `0` of the lift is the pressure coefficient. -/
theorem hasDerivAt_pressure_insertNth (i : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (h0 : Summable fun k : Fin 3 → ℤ => ‖pressureCoeff c k‖)
    (h1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖pressureCoeff c k‖) :
    ∀ (y : UnitAddTorus (Fin 2)) (t : ℝ),
      HasDerivAt
        (fun r : ℝ => ∑' k : Fin 3 → ℤ,
          pressureCoeff c k * mFourier k (i.insertNth (↑r : UnitAddCircle) y))
        (∑' k : Fin 3 → ℤ, (2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * pressureCoeff c k *
          mFourier k (i.insertNth (↑t : UnitAddCircle) y)) t := by
  intro y t
  -- embed the scalar pressure family into `Vel` so the Vel-valued brick applies
  set P : (Fin 3 → ℤ) → Vel :=
    fun k => pressureCoeff c k • EuclideanSpace.single (0 : Fin 3) (1 : ℂ) with hP
  have hP0 : ∀ k, P k 0 = pressureCoeff c k := by
    intro k; simp [hP]
  have hPn : ∀ k, ‖P k‖ = ‖pressureCoeff c k‖ := by
    intro k; simp [hP, norm_smul]
  have hc0 : Summable fun k => ‖P k‖ := h0.congr fun k => (hPn k).symm
  have hc1 : Summable fun k => ‖freq k‖ * ‖P k‖ := h1.congr fun k => by rw [hPn]
  have hb := hasDerivAt_charSum_insertNth i 0 P hc1 hc0 y t
  simp only [hP0, smul_eq_mul] at hb
  exact hb

/-! ## The classical equation, as a theorem about the capstone's flow -/

/-- **Theorem B, classical equation.**  The flow of `theorem_B_smooth_classical`
(all nineteen of its clauses re-exported verbatim) satisfies, at every
component `j`, every torus point `x` and every `t > 0`, the classical
Navier-Stokes equation POINTWISE:

    ∂ₜ u_j = (ν/(2π)²)·(∑ᵢ ∂ᵢ²u)_j − (1/2π)·(∑ᵢ uᵢ ∂ᵢu_j) − ∂_j p

where each piece is the capstone's own spelling: the Laplacian is the sum of
the second fiber-derivative series (clauses 15/16), the convection is
`∑ᵢ uᵢ ∂ᵢuⱼ` with `∂ᵢuⱼ` the twisted series (clause 19), and the pressure
gradient is the series `hasDerivAt_pressure_insertNth` identifies as `∂_j p`
(clauses 17/18).  The right-hand side is written out in full so the
statement is self-contained.

See `TheoremBSmooth` for the honest scope. -/
theorem theorem_B_smooth_classical_eq :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
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
        -- every Sobolev level survives, for THIS one flow
        (∀ (m : ℕ), ∀ t ∈ Ici (0:ℝ),
          Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        -- the flow stays mean-zero
        (∀ t ∈ Ici (0:ℝ), c t 0 = 0) ∧
        -- weighted ℓ¹ at every order
        (∀ t ∈ Ici (0:ℝ), ∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖c t l‖) ∧
        -- SPACE: the periodic lift is C^p for every p, and ℤ³-periodic
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (p : ℕ),
          ContDiff ℝ (p : ℕ∞) (uLift j (c t))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (g : Fin 3 → ℤ)
            (x : EuclideanSpace ℝ (Fin 3)),
          uLift j (c t) (x + freq g) = uLift j (c t) x) ∧
        -- TIME: the spectral Navier-Stokes equation, pointwise on the torus
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c t k
              + lerayProj k (convFull (c t) k)) j * mFourier k x) t) ∧
        -- C¹ IN TIME: that derivative is itself continuous on `t > 0`
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          ContinuousOn (fun s => ∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c s k
            + lerayProj k (convFull (c s) k)) j * mFourier k x) (Ioi (0:ℝ))) ∧
        -- the SECOND spatial fiber derivatives exist, with symbol (2πi·kᵢ)²
        (∀ t ∈ Ici (0:ℝ), ∀ (i j : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ),
          HasDerivAt
            (fun r : ℝ => ∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) * c t k j) •
              mFourier k (i.insertNth (↑r : UnitAddCircle) y))
            (∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) •
              mFourier k (i.insertNth (↑s : UnitAddCircle) y)) s) ∧
        -- CALIBRATION: the viscous term IS the Laplacian, scaled by ν/(2π)²
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (z : UnitAddTorus (Fin 3)),
          (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) • mFourier k z)
            = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
              (∑ i : Fin 3, ∑' k,
                ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k z)) ∧
        -- the PRESSURE is ℓ¹ (continuous) AND has one weighted order, so
        -- its gradient ∇p is a genuine object
        (∀ t ∈ Ici (0:ℝ), (Summable fun k => ‖pressureCoeff (c t) k‖) ∧
          Summable fun k => ‖freq k‖ * ‖pressureCoeff (c t) k‖) ∧
        -- the Leray projection is the convection MINUS a pressure gradient
        (∀ t ∈ Ici (0:ℝ), ∀ (k : Fin 3 → ℤ) (j : Fin 3),
          (lerayProj k (convFull (c t) k)) j
            = convFull (c t) k j
              - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k) ∧
        -- and the convection itself IS the classical (u·∇)u
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
              (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                * mFourier m x))
            = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull (c t) k j * mFourier k x) ∧
        -- THE CLASSICAL EQUATION, pointwise:
        --   ∂ₜu_j = (ν/(2π)²)·(Δu)_j − (1/2π)·((u·∇)u)_j − ∂_j p
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
                (∑ i : Fin 3, ∑' k,
                  ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k x)
              - ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
                  (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                    * mFourier m x))
              - ∑' k, (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k
                  * mFourier k x) t) := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_smooth_classical
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hall hmean0 hreal hdiv hsmall
  -- all 19 conjuncts of the capstone, one anonymous constructor, one `c`
  obtain ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl⟩ :=
    H hν hall hmean0 hreal hdiv hsmall
  -- re-export the 19 clauses verbatim; only the 20th remains
  refine ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, ?_⟩
  intro j x t ht
  have ht0 : t ∈ Ici (0:ℝ) := Ioi_subset_Ici_self ht
  -- the exported time clause (13)
  have hD := htime j x t ht
  refine hD.congr_deriv ?_
  -- ℓ¹ certificates from clause 10
  have h0 : Summable fun k => ‖c t k‖ := by simpa using hl1 t ht0 0
  have h1 : Summable fun k => ‖freq k‖ * ‖c t k‖ := by simpa using hl1 t ht0 1
  have h2 : Summable fun k => ‖freq k‖ ^ 2 * ‖c t k‖ := hl1 t ht0 2
  -- the three pieces are each summable
  have hV : Summable fun k =>
      (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) * mFourier k x := by
    refine Summable.of_norm ((h2.mul_left ν).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_)
    have hr : ‖(((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ))‖ = ν * ‖freq k‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    rw [norm_mul, norm_mFourier_apply, mul_one, norm_mul, hr]
    calc ν * ‖freq k‖ ^ 2 * ‖c t k j‖ ≤ ν * ‖freq k‖ ^ 2 * ‖c t k‖ := by
          gcongr; exact PiLp.norm_apply_le (c t k) j
      _ = ν * (‖freq k‖ ^ 2 * ‖c t k‖) := by ring
  have hC : Summable fun k => convFull (c t) k j * mFourier k x := by
    refine Summable.of_norm ((summable_norm_convFull (hsum t ht0).1 (hsum t ht0).2 h0 h1)
      |>.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_)
    rw [norm_mul, norm_mFourier_apply, mul_one]
    exact PiLp.norm_apply_le (convFull (c t) k) j
  have hG : Summable fun k =>
      (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k * mFourier k x := by
    refine Summable.of_norm (((hpress t ht0).2.mul_left (2 * Real.pi)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_)
    have e : ‖(2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ))‖ = 2 * Real.pi * |(k j : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
      have e1 : ‖(2 : ℂ)‖ = 2 := by simp
      have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
      have e4 : ‖((k j : ℤ) : ℂ)‖ = |(k j : ℝ)| := by simp
      rw [e1, e2, e4]; ring
    rw [norm_mul, norm_mFourier_apply, mul_one, norm_mul, e]
    calc 2 * Real.pi * |(k j : ℝ)| * ‖pressureCoeff (c t) k‖
        ≤ 2 * Real.pi * ‖freq k‖ * ‖pressureCoeff (c t) k‖ := by
          gcongr; exact abs_coord_le_norm_freq k j
      _ = 2 * Real.pi * (‖freq k‖ * ‖pressureCoeff (c t) k‖) := by ring
  -- term-wise decomposition of the spectral right-hand side (clause 18)
  have hterm : ∀ k, ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) j
        * mFourier k x
      = (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) * mFourier k x
        + convFull (c t) k j * mFourier k x
        - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k * mFourier k x := by
    intro k
    rw [PiLp.add_apply, PiLp.smul_apply, hleray t ht0 k j, Complex.real_smul]
    ring
  -- split the tsum into its three summable pieces
  rw [tsum_congr hterm, Summable.tsum_sub (hV.add hC) hG, Summable.tsum_add hV hC]
  -- viscous piece ↦ calibration (clause 16)
  have hVc : (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) * mFourier k x)
      = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          (∑ i : Fin 3, ∑' k,
            ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k x) := by
    rw [← hcalib t ht0 j x]
    exact tsum_congr fun k => (smul_eq_mul _ _).symm
  -- convection piece ↦ clause 19
  have hCc : (∑' k, convFull (c t) k j * mFourier k x)
      = - (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
            (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
              * mFourier m x))) := by
    have h19 := hnl t ht0 j x
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hcoef : ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((-(2 * Real.pi) : ℝ) : ℂ) = -1 := by
      push_cast
      field_simp
      try ring
    rw [h19, ← mul_assoc, hcoef]
    ring
  rw [hVc, hCc]
  ring

end TheoremB
