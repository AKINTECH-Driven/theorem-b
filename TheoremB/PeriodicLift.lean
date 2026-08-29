/-
  TheoremB/PeriodicLift.lean
  W5b of the Tier-6 smoothness wave (Theorem B campaign, 29 Aug 2026).

  The ℤ³-periodic lift of a coefficient family and its spatial regularity:
  the honest classical object of the campaign (mission C verdict — no
  manifold structure on the torus exists at this Mathlib pin, so the
  differential apparatus is the ℝ-lift throughout).

  Contents:
  * `uLift` — the lifted Fourier series on `EuclideanSpace ℝ (Fin 3)`
    (total definition; junk tsum off the ℓ¹ class is harmless — every
    regularity lemma below carries its own `Summable` certificate);
  * `uLift_periodic` — ℤ³-periodicity (the lattice shift is `x + freq g`,
    the `WithLp`-image of the integer vector; per-coordinate integer
    shifts die on the circle);
  * `contDiff_uLift_term` — every term is `C^∞` on ℝ³;
  * `norm_mFourier_apply`, `continuous_charSum`, `continuous_charSum_deriv`,
    `hasDerivAt_charSum_insertNth` — the torus-side character sums: sup-norm
    continuity, and the fiberwise `insertNth`-format first derivative in
    exactly the shape `mFourierCoeff_deriv` (M4 capstone) consumes;
  * `contDiff_uLift` — `C^p` in space for every fixed `p`, from weighted
    ℓ¹ summability of the coefficients (`contDiff_tsum` with the
    `(2π‖freq k‖)^q · ‖c k‖` derivative majorants);
  * `uLift_eq_charSum` — the lift descends to the torus character sum.

  The three local MeasureSpace instances replicate Mathlib's AddCircleMulti
  preamble VERBATIM (as TheoremB/FourierDeriv.lean and TorusSynthesis.lean
  do), with explicitly named instances prefixed `pl_`.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.TorusSynthesis
import TheoremB.FourierDeriv

namespace TheoremB

open Set MeasureTheory UnitAddTorus

noncomputable section

local instance pl_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance pl_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance pl_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The ℤ³-periodic lift -/

/-- **The ℤ³-periodic lift** of the `j`-th component of a coefficient family:
the Fourier character series read on `ℝ³` through the quotient map to the unit
torus, coordinate by coordinate.  Total definition — off the ℓ¹ class the tsum
junk-defaults to `0`; every regularity statement below carries its own
`Summable` certificate. -/
def uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => ∑' k : Fin 3 → ℤ, c k j • ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))

/-- Integer coordinates die on the unit circle. -/
private lemma coe_int_addCircle (g : ℤ) : ((g : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨g, by simp [zsmul_eq_mul]⟩

/-- **ℤ³-periodicity of the lift**: shifting by the Euclidean image `freq g`
of any integer vector `g : Fin 3 → ℤ` leaves `uLift` unchanged.  (At this pin
`freq g` is definitionally `WithLp.toLp 2 fun i => (g i : ℝ)`, and PiLp
addition is coordinatewise by `rfl`.)  No summability is needed: the two
series agree term by term. -/
theorem uLift_periodic (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (g : Fin 3 → ℤ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    uLift j c (x + freq g) = uLift j c x := by
  have hcoord : ∀ i : Fin 3,
      (((x + freq g) i : ℝ) : AddCircle (1 : ℝ)) = ((x i : ℝ) : AddCircle (1 : ℝ)) := by
    intro i
    have h1 : ((x + freq g) i : ℝ) = x i + (g i : ℝ) := rfl
    rw [h1, AddCircle.coe_add, coe_int_addCircle (g i), add_zero]
  show (∑' k : Fin 3 → ℤ, c k j • ∏ i : Fin 3, fourier (k i) (((x + freq g) i : ℝ) : AddCircle (1 : ℝ)))
      = ∑' k : Fin 3 → ℤ, c k j • ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))
  exact tsum_congr fun k =>
    congrArg (c k j • ·)
      (Finset.prod_congr rfl fun i _ => congrArg (fourier (k i)) (hcoord i))

/-! ## Term smoothness -/

/-- Every term of the lifted series is `C^∞` on ℝ³ (the compiled-probe
incantation: `fourier_coe_apply` + `Complex.contDiff_exp` + coordinate
projections, plus a constant smul). -/
theorem contDiff_uLift_term (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : EuclideanSpace ℝ (Fin 3) =>
      c k j • ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)) := by
  refine ContDiff.const_smul (c k j) ?_
  refine contDiff_prod (t := Finset.univ) fun i _ => ?_
  have h : (fun x : EuclideanSpace ℝ (Fin 3) => fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
      = (fun t : ℝ => fourier (k i) (t : AddCircle (1 : ℝ))) ∘ (fun x => x i) := rfl
  rw [h]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => fourier (k i) (t : AddCircle (1 : ℝ)) := by
    have hh : (fun t : ℝ => fourier (k i) (t : AddCircle (1 : ℝ)))
        = fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (k i) * t / 1) :=
      funext fun t => fourier_coe_apply
    rw [hh]
    have : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (t : ℂ) := Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp (by fun_prop)
  exact h1.comp (EuclideanSpace.proj (𝕜 := ℝ) (i : Fin 3)).contDiff

/-! ## The torus-side character sums: pointwise norms, continuity, and the
`insertNth`-format fiber derivative (the capstone-critical brick) -/

/-- The character monomials have unit modulus at every point.  (Public: the
capstone uses the characters as the bounded weight family of the time
engine's `hw : ∀ k, ‖w k‖ ≤ 1`.) -/
theorem norm_mFourier_apply (n : Fin 3 → ℤ) (z : UnitAddTorus (Fin 3)) :
    ‖mFourier n z‖ = 1 := by
  simp [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply]

/-- The derivative-series coefficient bound: `‖(2πI·kᵢ·c k j) • mFourier k z‖ ≤
2π‖freq k‖‖c k‖` (coordinate bound `|kᵢ| ≤ ‖freq k‖` on the Euclidean lattice). -/
private lemma norm_deriv_smul_le (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ)
    (z : UnitAddTorus (Fin 3)) :
    ‖((2 * Real.pi * Complex.I * (k i)) * c k j) • mFourier k z‖
      ≤ 2 * Real.pi * (‖freq k‖ * ‖c k‖) := by
  rw [norm_smul, norm_mFourier_apply, mul_one]
  have h1 : |(k i : ℝ)| ≤ ‖freq k‖ := by
    have h := PiLp.norm_apply_le (freq k) i
    have h2 : ‖freq k i‖ = |(k i : ℝ)| := rfl
    rw [h2] at h
    exact h
  have h2 : ‖c k j‖ ≤ ‖c k‖ := PiLp.norm_apply_le (c k) j
  have h3 : ‖(2 * Real.pi * Complex.I * (k i) * c k j : ℂ)‖
      = 2 * Real.pi * (|(k i : ℝ)| * ‖c k j‖) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I]
    have e1 : ‖(2 : ℂ)‖ = 2 := by simp
    have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
    have e4 : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by simp
    rw [e1, e2, e4]
    ring
  rw [h3]
  have h4 : |(k i : ℝ)| * ‖c k j‖ ≤ ‖freq k‖ * ‖c k‖ :=
    mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  have h5 : (0 : ℝ) ≤ 2 * Real.pi := by
    have hπ := Real.pi_pos
    linarith
  exact mul_le_mul_of_nonneg_left h4 h5

/-- Per-term fiber derivative of the character sum along the `i`-th coordinate,
in the `insertNth` format: the `mFourier_insertNth` factorization splits off the
`i`-th `fourier` factor, `hasDerivAt_fourier` differentiates it. -/
private lemma term_hasDerivAt (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ)
    (y : UnitAddTorus (Fin 2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => c k j • mFourier k (i.insertNth (↑s : UnitAddCircle) y))
      (((2 * Real.pi * Complex.I * (k i)) * c k j) •
        mFourier k (i.insertNth (↑t : UnitAddCircle) y)) t := by
  have hbase : HasDerivAt (fun s : ℝ => fourier (k i) (↑s : AddCircle (1 : ℝ)))
      (2 * Real.pi * Complex.I * (k i) / 1 * fourier (k i) (↑t : AddCircle (1 : ℝ))) t := by
    simpa using hasDerivAt_fourier 1 (k i) t
  have hsmul := (hbase.mul_const (mFourier (fun l => k (i.succAbove l)) y)).const_smul (c k j)
  have hfun : (fun s : ℝ => c k j • mFourier k (i.insertNth (↑s : UnitAddCircle) y))
      = fun s : ℝ => c k j • (fourier (k i) (↑s : AddCircle (1 : ℝ)) *
          mFourier (fun l => k (i.succAbove l)) y) := by
    funext s
    rw [mFourier_insertNth i k (↑s : UnitAddCircle) y]
  have hval : (((2 * Real.pi * Complex.I * (k i)) * c k j) •
        mFourier k (i.insertNth (↑t : UnitAddCircle) y))
      = c k j • (2 * Real.pi * Complex.I * (k i) / 1 *
          fourier (k i) (↑t : AddCircle (1 : ℝ)) *
          mFourier (fun l => k (i.succAbove l)) y) := by
    rw [mFourier_insertNth i k (↑t : UnitAddCircle) y]
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [hfun, hval]
  exact hsmul

/-- **The PDE brick (W5b): the `insertNth`-format fiber derivative of the
character sum.**  For an ℓ¹ family with one weighted ℓ¹ order, the character
sum is differentiable along every coordinate fiber, with derivative the
`2πI·kᵢ`-twisted character sum — exactly the input format of the M4 capstone
`mFourierCoeff_deriv`.  The majorant `2π‖freq k‖‖c k‖` is `x`-independent, so
the global-bound `hasDerivAt_tsum` applies. -/
theorem hasDerivAt_charSum_insertNth (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖)
    (hc0 : Summable fun k : Fin 3 → ℤ => ‖c k‖) :
    ∀ (y : UnitAddTorus (Fin 2)) (t : ℝ),
      HasDerivAt
        (fun s : ℝ => ∑' k : Fin 3 → ℤ,
          c k j • mFourier k (i.insertNth (↑s : UnitAddCircle) y))
        (∑' k : Fin 3 → ℤ, ((2 * Real.pi * Complex.I * (k i)) * c k j) •
          mFourier k (i.insertNth (↑t : UnitAddCircle) y)) t := by
  intro y t
  have hsum0 : Summable fun k : Fin 3 → ℤ =>
      c k j • mFourier k (i.insertNth (((0 : ℝ) : ℝ) : UnitAddCircle) y) := by
    -- (the ℝ-lift evaluated at the base point 0; any point works, the majorant is global)
    refine Summable.of_norm ?_
    refine hc0.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    rw [norm_smul, norm_mFourier_apply, mul_one]
    exact PiLp.norm_apply_le (c k) j
  exact hasDerivAt_tsum (hc1.mul_left (2 * Real.pi))
    (fun k s => term_hasDerivAt i j c k y s)
    (fun k s => norm_deriv_smul_le i j c k (i.insertNth (↑s : UnitAddCircle) y))
    hsum0 t

/-- **Sup-norm continuity of the character sum** on the whole torus, from ℓ¹
coefficients (`continuous_tsum` with the unit-modulus majorant).  This is the
`Continuous f` hypothesis of `mFourierCoeff_deriv`. -/
theorem continuous_charSum (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc0 : Summable fun k : Fin 3 → ℤ => ‖c k‖) :
    Continuous fun z : T3 => ∑' k : Fin 3 → ℤ, c k j • mFourier k z := by
  refine continuous_tsum (u := fun k : Fin 3 → ℤ => ‖c k‖)
    (fun k => ((mFourier k).continuous.const_smul (c k j))) hc0 (fun k z => ?_)
  rw [norm_smul, norm_mFourier_apply, mul_one]
  exact PiLp.norm_apply_le (c k) j

/-- **Sup-norm continuity of the derivative character sum** on the whole torus,
from one weighted ℓ¹ order.  Restricted to any coordinate fiber this is the
continuity of the fiber derivative; as a `T3`-function it is the
`Continuous f'` hypothesis of `mFourierCoeff_deriv`. -/
theorem continuous_charSum_deriv (i j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (hc1 : Summable fun k : Fin 3 → ℤ => ‖freq k‖ * ‖c k‖) :
    Continuous fun z : T3 => ∑' k : Fin 3 → ℤ,
      ((2 * Real.pi * Complex.I * (k i)) * c k j) • mFourier k z := by
  refine continuous_tsum (u := fun k : Fin 3 → ℤ => 2 * Real.pi * (‖freq k‖ * ‖c k‖))
    (fun k => ((mFourier k).continuous.const_smul _)) (hc1.mul_left (2 * Real.pi))
    (fun k z => norm_deriv_smul_le i j c k z)

/-! ## Descent to the torus character sum -/

/-- **The lift descends**: at any point `x : ℝ³`, `uLift` agrees with the
torus character sum evaluated at the coordinatewise image of `x` on the
torus (the value of `mFourier` at a point is definitionally the product of
`fourier` values). -/
theorem uLift_eq_charSum (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (x : EuclideanSpace ℝ (Fin 3)) :
    uLift j c x = ∑' k : Fin 3 → ℤ,
      c k j • mFourier k (fun i : Fin 3 => ((x i : ℝ) : AddCircle (1 : ℝ))) :=
  tsum_congr fun _ => rfl

/-! ## Spatial regularity: `C^p` for every fixed `p`

The route (mission C dossier, 'term smoothness of lifted monomials'): each term
is `c k j • cexp ∘ L_k` for the real continuous linear functional
`L_k := innerSL ℝ (freq k)` composed with the 1-D exponential
`t ↦ cexp(2πI·t)`.  `ContinuousLinearMap.iteratedFDeriv_comp_right` transports
the 1-D iterated derivative `(2πI)^q · cexp(2πI·t)` (an induction over `q`
with `HasDerivAt.comp_ofReal`), so the `q`-th Fréchet derivative is bounded by
`(2π)^q‖freq k‖^q‖c k‖` — no factorial — and `contDiff_tsum` closes against the
weighted ℓ¹ hypotheses. -/

/-- 1-D: derivative of `t ↦ cexp (a·t)` along ℝ (via `HasDerivAt.comp_ofReal`,
the pin's canonical ℝ-restriction of a holomorphic derivative). -/
private lemma hasDerivAt_cexp_mul_real (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (a * s)) (a * Complex.exp (a * t)) t := by
  have hin : HasDerivAt (fun w : ℂ => a * w) a (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul a
  have h := (Complex.hasDerivAt_exp (a * (t : ℂ))).comp (t : ℂ) hin
  simpa [mul_comm] using h.comp_ofReal

/-- 1-D: the `q`-th iterated derivative of `t ↦ cexp (a·t)` along ℝ is
`a^q · cexp (a·t)`. -/
private lemma iteratedDeriv_cexp_mul_real (a : ℂ) (q : ℕ) :
    iteratedDeriv q (fun s : ℝ => Complex.exp (a * s)) =
      fun t : ℝ => a ^ q * Complex.exp (a * t) := by
  induction q with
  | zero => funext t; simp
  | succ q ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have h := ((hasDerivAt_cexp_mul_real a t).const_mul (a ^ q)).deriv
      rw [h]
      ring

/-- 1-D: `t ↦ cexp (a·t)` is `C^∞` along ℝ. -/
private lemma contDiff_cexp_mul_real (a : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => Complex.exp (a * t) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (t : ℂ) := Complex.ofRealCLM.contDiff
  have hlin : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => a * (t : ℂ) :=
    (contDiff_const (c := a)).mul h
  exact Complex.contDiff_exp.comp hlin

/-- Each lifted term is the constant `c k j` times the composition of the 1-D
exponential with the inner-product functional `innerSL ℝ (freq k)`
(`∏ᵢ cexp(2πI kᵢxᵢ) = cexp(2πI⟨freq k, x⟩)`). -/
private lemma term_eq_comp (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        c k j • ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
      = fun x => c k j •
          (((fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
            (innerSL ℝ (freq k))) x) := by
  funext x
  have hAB : (∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
      = ((fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
          (innerSL ℝ (freq k))) x := by
    show (∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
        = Complex.exp ((2 * Real.pi * Complex.I) * ((inner ℝ (freq k) x : ℝ) : ℂ))
    have hinner : inner ℝ (freq k) x = ∑ i, (k i : ℝ) * x i := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
    rw [hinner]
    have h1 : ∀ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)) =
        Complex.exp (2 * Real.pi * Complex.I * (k i) * (x i) / 1) := fun i =>
      fourier_coe_apply
    rw [Finset.prod_congr rfl fun i _ => h1 i, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact congrArg (c k j • ·) hAB

/-- The clean factorial-free derivative bound: the `q`-th Fréchet derivative of
each lifted term has norm at most `(2π)^q‖freq k‖^q‖c k‖`, globally in `x`. -/
private lemma norm_iteratedFDeriv_term_le (j : Fin 3) (c : (Fin 3 → ℤ) → Vel)
    (k : Fin 3 → ℤ) (q : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ q
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          c k j • ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))) x‖
      ≤ (2 * Real.pi) ^ q * (‖freq k‖ ^ q * ‖c k‖) := by
  have hgsm : ContDiff ℝ (⊤ : ℕ∞)
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) :=
    contDiff_cexp_mul_real (2 * Real.pi * Complex.I)
  have hpull : iteratedFDeriv ℝ q
      (fun x : EuclideanSpace ℝ (Fin 3) => c k j •
        (((fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
          (innerSL ℝ (freq k))) x)) x
      = c k j • iteratedFDeriv ℝ q
          (((fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
            (innerSL ℝ (freq k)))) x :=
    iteratedFDeriv_const_smul_apply'
      (((hgsm.comp (innerSL ℝ (freq k)).contDiff).of_le
        (by exact_mod_cast le_top)).contDiffAt)
  have hstep : iteratedFDeriv ℝ q
      (((fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
        (innerSL ℝ (freq k)))) x
      = (iteratedFDeriv ℝ q
          (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
          ((innerSL ℝ (freq k)) x)).compContinuousLinearMap
            fun _ : Fin q => innerSL ℝ (freq k) :=
    (innerSL ℝ (freq k)).iteratedFDeriv_comp_right hgsm x (by exact_mod_cast le_top)
  rw [term_eq_comp j c k, hpull, norm_smul, hstep]
  have hcomp : ‖(iteratedFDeriv ℝ q
        (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
        ((innerSL ℝ (freq k)) x)).compContinuousLinearMap
          fun _ : Fin q => innerSL ℝ (freq k)‖
      ≤ ‖iteratedFDeriv ℝ q
          (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
          ((innerSL ℝ (freq k)) x)‖ * ∏ _i : Fin q, ‖innerSL ℝ (freq k)‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
  have h1d : ‖iteratedFDeriv ℝ q
      (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
      ((innerSL ℝ (freq k)) x)‖ = (2 * Real.pi) ^ q := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hv : iteratedDeriv q
        (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
        ((innerSL ℝ (freq k)) x)
        = (2 * Real.pi * Complex.I) ^ q *
          Complex.exp ((2 * Real.pi * Complex.I) * (((innerSL ℝ (freq k)) x : ℝ) : ℂ)) :=
      congrFun (iteratedDeriv_cexp_mul_real (2 * Real.pi * Complex.I) q) _
    rw [hv, norm_mul, norm_pow]
    have e5 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I]
      have e1 : ‖(2 : ℂ)‖ = 2 := by simp
      have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
      rw [e1, e2]
      ring
    have e6 : ‖Complex.exp ((2 * Real.pi * Complex.I) *
        (((innerSL ℝ (freq k)) x : ℝ) : ℂ))‖ = 1 := by
      rw [show ((2 * Real.pi * Complex.I) * (((innerSL ℝ (freq k)) x : ℝ) : ℂ) : ℂ)
          = ((2 * Real.pi * ((innerSL ℝ (freq k)) x) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [e5, e6, mul_one]
  have hLnorm : ‖innerSL ℝ (freq k)‖ = ‖freq k‖ := innerSL_apply_norm (𝕜 := ℝ) (freq k)
  have hprod : (∏ _i : Fin q, ‖innerSL ℝ (freq k)‖) = ‖freq k‖ ^ q := by
    rw [Finset.prod_const, hLnorm, Finset.card_univ, Fintype.card_fin]
  rw [h1d, hprod] at hcomp
  have hnn : (0 : ℝ) ≤ (2 * Real.pi) ^ q * ‖freq k‖ ^ q := by
    have hπ := Real.pi_pos
    have h2π : (0 : ℝ) ≤ 2 * Real.pi := by linarith
    exact mul_nonneg (pow_nonneg h2π q) (pow_nonneg (norm_nonneg _) q)
  calc ‖c k j‖ * ‖(iteratedFDeriv ℝ q
          (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
          ((innerSL ℝ (freq k)) x)).compContinuousLinearMap
            fun _ : Fin q => innerSL ℝ (freq k)‖
      ≤ ‖c k j‖ * ((2 * Real.pi) ^ q * ‖freq k‖ ^ q) :=
        mul_le_mul_of_nonneg_left hcomp (norm_nonneg _)
    _ ≤ ‖c k‖ * ((2 * Real.pi) ^ q * ‖freq k‖ ^ q) :=
        mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (c k) j) hnn
    _ = (2 * Real.pi) ^ q * (‖freq k‖ ^ q * ‖c k‖) := by ring

/-- **Spatial `C^p` regularity of the lift, for every fixed `p`** (deliverable
W5b.4): if the coefficients carry weighted ℓ¹ summability at every order
`q ≤ p`, the lift is `p` times continuously differentiable on ℝ³.
(`contDiff_tsum` against the factorial-free `(2π‖freq k‖)^q‖c k‖` majorants;
the capstone feeds these hypotheses from `summable_weighted_norm` along the
eternal Sobolev flow.) -/
theorem contDiff_uLift (j : Fin 3) (c : (Fin 3 → ℤ) → Vel) (p : ℕ)
    (hc : ∀ q : ℕ, q ≤ p → Summable fun k : Fin 3 → ℤ => ‖freq k‖ ^ q * ‖c k‖) :
    ContDiff ℝ (p : ℕ∞) (uLift j c) := by
  show ContDiff ℝ ((p : ℕ∞) : WithTop ℕ∞) fun x : EuclideanSpace ℝ (Fin 3) =>
    ∑' k : Fin 3 → ℤ, c k j • ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))
  refine contDiff_tsum
    (v := fun q k => (2 * Real.pi) ^ q * (‖freq k‖ ^ q * ‖c k‖))
    (fun k => (contDiff_uLift_term j c k).of_le (by exact_mod_cast le_top))
    (fun q hq => ?_) (fun q k x _ => norm_iteratedFDeriv_term_le j c k q x)
  have hq' : q ≤ p := by exact_mod_cast hq
  exact ((hc q hq').mul_left ((2 * Real.pi) ^ q))

end

end TheoremB
