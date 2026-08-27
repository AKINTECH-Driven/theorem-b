/-
  TheoremB/FourierDeriv.lean
  M4 wave 1 of the Theorem B campaign (27 Aug 2026, morning session).

  The derivative-to-frequency bridge on the 3-torus: absent from both the
  pinned Mathlib (whose Fourier-derivative theory is 1-D interval-based)
  and leray-hopf (whose only multiplier identity is whole-space Schwartz).
  This is the interpretation layer tying the campaign spectral statements
  to classical partial derivatives; the Tier-3 Galerkin route needs it only
  as glue, per context/rung3-tier1-blueprint.md rung 4.

  Contents: the 1-D periodic identity fourierCoeff_hasDerivAt (ALL n : ℤ,
  including 0), the coordinate-peeling integral_insertNth, the monomial
  factorization mFourier_insertNth, and the capstone mFourierCoeff_deriv.

  The local MeasureSpace instances replicate Mathlib AddCircleMulti
  preamble VERBATIM so every integral lands on the measure mFourierCoeff
  was compiled against.

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import Mathlib

namespace TheoremB

open Set MeasureTheory UnitAddTorus

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The 1-D periodic derivative-coefficient identity -/


/-- The `Ioc`-lift of the ℝ-lift of a genuine `AddCircle` function is that function. -/
private theorem liftIoc_comp_coe {T : ℝ} [hT : Fact (0 < T)] (g : AddCircle T → ℂ) (a : ℝ) :
    AddCircle.liftIoc T a (fun x : ℝ => g ↑x) = g := by
  funext y
  simp only [AddCircle.liftIoc, Function.comp_apply, Set.restrict_apply, AddCircle.coe_equivIoc]

/-- Bridge: the Fourier coefficient of a circle function equals the `fourierCoeffOn` of its
ℝ-lift over `[0, 0 + T]`. -/
private theorem fourierCoeff_eq_fourierCoeffOn_coe {T : ℝ} [hT : Fact (0 < T)]
    (g : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff g n =
      fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT.out) (fun x : ℝ => g ↑x) n := by
  calc fourierCoeff g n
      = fourierCoeff (AddCircle.liftIoc T 0 (fun x : ℝ => g ↑x)) n := by
        rw [liftIoc_comp_coe]
    _ = fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) hT.out) (fun x : ℝ => g ↑x) n :=
        fourierCoeff_liftIoc_eq (fun x : ℝ => g ↑x) n

theorem fourierCoeff_hasDerivAt {T : ℝ} [hT : Fact (0 < T)] {f f' : AddCircle T → ℂ}
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f ↑y) (f' ↑x) x)
    (hf' : Continuous f') (n : ℤ) :
    fourierCoeff f' n = (2 * Real.pi * Complex.I * n / T) * fourierCoeff f n := by
  have hcont' : Continuous fun x : ℝ => f' ↑x := hf'.comp (AddCircle.continuous_mk' T)
  have hint' : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => f' ↑x) volume a b := fun a b =>
    hcont'.intervalIntegrable a b
  rcases eq_or_ne n 0 with rfl | hn
  · -- n = 0 : the coefficient of the derivative is the integral of the derivative over one
    -- period, which vanishes by periodicity; the right-hand side carries a factor `(0 : ℤ)`.
    rw [fourierCoeff_eq_intervalIntegral f' 0 0]
    simp only [neg_zero, fourier_zero, one_smul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hint' 0 (0 + T))]
    simp only [AddCircle.coe_add_period T 0, sub_self, smul_zero, Int.cast_zero, mul_zero,
      zero_div, zero_mul]
  · -- n ≠ 0 : integrate by parts via `fourierCoeffOn_of_hasDerivAt` on `[0, 0 + T]`.
    have key := fourierCoeffOn_of_hasDerivAt (lt_add_of_pos_right (0 : ℝ) hT.out) hn
      (fun x _ => hf x) (hint' 0 (0 + T))
    rw [← fourierCoeff_eq_fourierCoeffOn_coe f n, ← fourierCoeff_eq_fourierCoeffOn_coe f' n]
      at key
    simp only [AddCircle.coe_add_period T 0, sub_self, mul_zero, zero_sub] at key
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnz : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hTz : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.out.ne'
    rw [key]
    push_cast
    field_simp
    ring

/-! ## Coordinate peeling on the torus -/


lemma integral_insertNth {m : ℕ} (i : Fin (m + 1)) {g : UnitAddTorus (Fin (m + 1)) → ℂ}
    (hg : Continuous g) :
    ∫ x : UnitAddTorus (Fin (m + 1)), g x =
      ∫ y : UnitAddTorus (Fin m), ∫ t : UnitAddCircle, g (i.insertNth t y) := by
  have hins : Continuous fun z : UnitAddCircle × UnitAddTorus (Fin m) =>
      (i.insertNth z.1 z.2 : UnitAddTorus (Fin (m + 1))) :=
    Continuous.finInsertNth (A := fun _ : Fin (m + 1) => UnitAddCircle) i
      continuous_fst continuous_snd
  have hcont : Continuous fun z : UnitAddCircle × UnitAddTorus (Fin m) =>
      g (i.insertNth z.1 z.2) := hg.comp hins
  have hint : Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin m) =>
      g (i.insertNth z.1 z.2)) ((volume : Measure UnitAddCircle).prod volume) :=
    hcont.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  calc
    ∫ x : UnitAddTorus (Fin (m + 1)), g x
        = ∫ z : UnitAddCircle × UnitAddTorus (Fin m),
            g ((MeasurableEquiv.piFinSuccAbove (fun _ => UnitAddCircle) i).symm z) :=
      ((MeasureTheory.volume_preserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => UnitAddCircle) i).symm.integral_comp' g).symm
    _ = ∫ z : UnitAddCircle × UnitAddTorus (Fin m), g (i.insertNth z.1 z.2) := rfl
    _ = ∫ y : UnitAddTorus (Fin m), ∫ t : UnitAddCircle, g (i.insertNth t y) :=
      MeasureTheory.integral_prod_symm _ hint

lemma mFourier_insertNth {m : ℕ} (i : Fin (m + 1)) (n : Fin (m + 1) → ℤ)
    (t : UnitAddCircle) (y : UnitAddTorus (Fin m)) :
    UnitAddTorus.mFourier n (i.insertNth t y) =
      fourier (n i) t * UnitAddTorus.mFourier (fun j => n (i.succAbove j)) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  refine (Fin.prod_univ_succAbove _ i).trans ?_
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-! ## The capstone -/

/-- **M4 capstone: the derivative-to-frequency identity on the 3-torus.**
For `f, f' : UnitAddTorus (Fin 3) → ℂ` with `f'` the `i`-th partial derivative
of `f` along every fiber (in `insertNth` form) and both continuous:
`mFourierCoeff f' n = (2π·I·nᵢ) · mFourierCoeff f n`. -/
theorem mFourierCoeff_deriv (i : Fin 3) {f f' : UnitAddTorus (Fin 3) → ℂ}
    (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ (y : UnitAddTorus (Fin 2)) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (i.insertNth (↑s : UnitAddCircle) y))
        (f' (i.insertNth (↑t : UnitAddCircle) y)) t)
    (n : Fin 3 → ℤ) :
    mFourierCoeff f' n = (2 * Real.pi * Complex.I * (n i)) * mFourierCoeff f n := by
  haveI : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  -- the reusable unfold-peel-refold chain
  have key : ∀ (g : UnitAddTorus (Fin 3) → ℂ), Continuous g →
      mFourierCoeff g n = ∫ y : UnitAddTorus (Fin 2),
        mFourier (fun j => (-n) (i.succAbove j)) y *
          fourierCoeff (fun t : UnitAddCircle => g (i.insertNth t y)) (n i) := by
    intro g hg
    have h0 : mFourierCoeff g n = ∫ x : UnitAddTorus (Fin 3), mFourier (-n) x • g x := rfl
    have hcont : Continuous fun x : UnitAddTorus (Fin 3) => mFourier (-n) x • g x :=
      (mFourier (-n)).continuous.smul hg
    rw [h0, integral_insertNth i hcont]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hpt : ∀ t : UnitAddCircle,
        mFourier (-n) (i.insertNth t y) • g (i.insertNth t y) =
          mFourier (fun j => (-n) (i.succAbove j)) y *
            (fourier (-(n i)) t • g (i.insertNth t y)) := by
      intro t
      rw [mFourier_insertNth i (-n) t y]
      have : (-n) i = -(n i) := rfl
      rw [this]
      simp only [smul_eq_mul]
      ring
    calc (∫ t : UnitAddCircle, mFourier (-n) (i.insertNth t y) • g (i.insertNth t y))
        = ∫ t : UnitAddCircle, mFourier (fun j => (-n) (i.succAbove j)) y *
            (fourier (-(n i)) t • g (i.insertNth t y)) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = mFourier (fun j => (-n) (i.succAbove j)) y *
            ∫ t : UnitAddCircle, fourier (-(n i)) t • g (i.insertNth t y) :=
          MeasureTheory.integral_const_mul _ _
      _ = mFourier (fun j => (-n) (i.succAbove j)) y *
            fourierCoeff (fun t : UnitAddCircle => g (i.insertNth t y)) (n i) := rfl
  -- per-fiber 1-D identity
  have hfiber : ∀ y : UnitAddTorus (Fin 2),
      fourierCoeff (fun t : UnitAddCircle => f' (i.insertNth t y)) (n i) =
        (2 * Real.pi * Complex.I * (n i)) *
          fourierCoeff (fun t : UnitAddCircle => f (i.insertNth t y)) (n i) := by
    intro y
    have h := fourierCoeff_hasDerivAt (T := (1:ℝ))
      (f := fun t : UnitAddCircle => f (i.insertNth t y))
      (f' := fun t : UnitAddCircle => f' (i.insertNth t y))
      (fun x => hderiv y x)
      (hf'.comp (Continuous.finInsertNth (A := fun _ : Fin 3 => UnitAddCircle) i
        continuous_id continuous_const)) (n i)
    rw [h]
    norm_num
  -- assemble
  rw [key f' hf', key f hf]
  calc (∫ y : UnitAddTorus (Fin 2),
        mFourier (fun j => (-n) (i.succAbove j)) y *
          fourierCoeff (fun t : UnitAddCircle => f' (i.insertNth t y)) (n i))
      = ∫ y : UnitAddTorus (Fin 2),
          (2 * Real.pi * Complex.I * (n i)) *
            (mFourier (fun j => (-n) (i.succAbove j)) y *
              fourierCoeff (fun t : UnitAddCircle => f (i.insertNth t y)) (n i)) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hfiber y]
        ring
    _ = (2 * Real.pi * Complex.I * (n i)) *
          ∫ y : UnitAddTorus (Fin 2),
            mFourier (fun j => (-n) (i.succAbove j)) y *
              fourierCoeff (fun t : UnitAddCircle => f (i.insertNth t y)) (n i) :=
        MeasureTheory.integral_const_mul _ _

end

end TheoremB
