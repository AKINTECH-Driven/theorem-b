/-
# Physical faces of the weak equation (Tier 5 polish)

The capstone's weak evolution identity phrases both pairing slots
spectrally. This file wires their physical faces: the linear slot is the
genuine L² pairing of the synthesized fields (`linear_pairing_physical`),
and the convection slot is the classical convection integral
(`convection_pairing_physical`) — equal to `+∫ u ⊗ u : ∇w̄` when written
with a literal (2π-free) gradient, since the spectral gradient-test
multiplier `f1_gradTest` plays the role of `−∂ᵢ` — with divergence-freeness
of the flow as exactly the classical hypothesis making the integration by
parts exact.
-/
import TheoremB.TheoremBTorus

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance f1_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance f1_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance f1_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### FOXTROT-1: physical faces of the weak equation's pairing slots

The capstone's weak evolution identity phrases both its pairing slots
spectrally.  `linear_pairing_physical` names the physical face of the linear
slot (the L² pairing of the synthesized fields), and
`convection_pairing_physical` gives the convection slot its physical face:
paired against a finitely supported test family, `convFull` is the classical
convection integral — `+∫ u ⊗ u : ∇w̄` in literal (`2π`-free) gradient
notation, since the gradient test multiplier `f1_gradTest` plays the role
of `−∂ᵢ`.  Divergence-freeness of the flow is exactly the classical
hypothesis making the integration by parts exact. -/

/-- **Linear pairing, physical face**: the spectral pairing over the test
support is the physical L² pairing of the synthesized fields.  (The named
public corollary of `pairing_transfer`, wiring the capstone's linear slot.) -/
theorem linear_pairing_physical {w : (Fin 3 → ℤ) → Vel} {c : (Fin 3 → ℤ) → Vel}
    {F : Finset (Fin 3 → ℤ)} (hw : ∀ k, k ∉ F → w k = 0)
    (hwsum : Summable fun k => ‖w k‖ ^ 2) (hcsum : Summable fun k => ‖c k‖ ^ 2) :
    (∑ k ∈ F, inner ℂ (w k) (c k)) =
      ∑ j : Fin 3, inner ℂ (synthT j w) (synthT j c) :=
  (pairing_transfer hw hwsum hcsum).symm

/-- The spectral gradient-test multiplier: mode `k` of the test family is
scaled by `−(i·kᵢ)` — the (2π-free) spectral symbol of `−∂ᵢ`, conjugate-
matched so that the convection pairing identity holds exactly. -/
def f1_gradTest (i : Fin 3) (w : (Fin 3 → ℤ) → Vel) : (Fin 3 → ℤ) → Vel :=
  fun k => (-(Complex.I * ((k i : ℝ) : ℂ))) • w k

/-- Componentwise formula for the gradient test. -/
lemma f1_gradTest_apply (i : Fin 3) (w : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ)
    (j : Fin 3) :
    f1_gradTest i w k j = -(Complex.I * ((k i : ℝ) : ℂ)) * w k j := by
  simp [f1_gradTest]

/-- Conjugated componentwise formula: the conjugate multiplier is `+i·kᵢ`. -/
lemma f1_conj_gradTest_apply (i : Fin 3) (w : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ)
    (j : Fin 3) :
    conj (f1_gradTest i w k j) =
      Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) := by
  rw [f1_gradTest_apply, map_mul, map_neg, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring

/-- The gradient test inherits the test family's finite support. -/
lemma f1_gradTest_support {i : Fin 3} {w : (Fin 3 → ℤ) → Vel}
    {F : Finset (Fin 3 → ℤ)} (hw : ∀ k, k ∉ F → w k = 0) :
    ∀ k, k ∉ F → f1_gradTest i w k = 0 := by
  intro k hk
  simp [f1_gradTest, hw k hk]

/-- Finitely supported coefficient families are square-summable. -/
lemma f1_summable_of_support {v : (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    (hv : ∀ k, k ∉ F → v k = 0) : Summable fun k => ‖v k‖ ^ 2 :=
  summable_of_ne_finset_zero (s := F) fun k hk => by rw [hv k hk]; simp

/-- ℓ²·ℓ² Cauchy–Schwarz summability of the unweighted shifted product. -/
private lemma f1_summable_shift_mul {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    Summable fun l => ‖c l‖ * ‖c (k - l)‖ := by
  have h2 : ∀ x : ℝ, x ^ 2 = x ^ (2 : ℝ) := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hf2 : Summable fun l => ‖c l‖ ^ (2 : ℝ) := hE.congr fun l => h2 _
  have hEk : Summable fun l => ‖c (k - l)‖ ^ 2 := by
    have h := ((Equiv.subLeft k).summable_iff (f := fun m => ‖c m‖ ^ 2)).mpr hE
    exact h.congr fun l => by simp [Function.comp]
  have hg2 : Summable fun l => ‖c (k - l)‖ ^ (2 : ℝ) := hEk.congr fun l => h2 _
  exact Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun l => norm_nonneg _) (fun l => norm_nonneg _) hf2 hg2

/-- Componentwise summability of the shifted coefficient product. -/
private lemma f1_summable_comp_mul {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2) (k : Fin 3 → ℤ) (i j : Fin 3) :
    Summable fun l => c l i * c (k - l) j := by
  refine Summable.of_norm ((f1_summable_shift_mul hE k).of_nonneg_of_le
    (fun l => norm_nonneg _) fun l => ?_)
  rw [norm_mul]
  exact mul_le_mul (PiLp.norm_apply_le (c l) i) (PiLp.norm_apply_le (c (k - l)) j)
    (norm_nonneg _) (norm_nonneg _)

/-- `castCV` is subtractive. -/
private lemma f1_castCV_sub (r s : EuclideanSpace ℝ (Fin 3)) :
    castCV (r - s) = castCV r - castCV s := by
  ext j
  simp [castCV]

/-- **The div-free frequency transfer**: against a divergence-free family the
shifted frequency in the convection symbol may be replaced by the unshifted
one — the spectral face of the classical `div u = 0` integration by parts. -/
private lemma f1_dotR_freq_of_divFree {c : (Fin 3 → ℤ) → Vel} (hdiv : DivFree c)
    (k l : Fin 3 → ℤ) :
    dotR (c l) (freq (k - l)) = dotR (c l) (freq k) := by
  rw [freq_sub, dotR_eq_inner, f1_castCV_sub, inner_sub_left, ← dotR_eq_inner,
    ← dotR_eq_inner, hdiv l, sub_zero]

/-- Componentwise expansion of `dotR` against a lattice frequency. -/
private lemma f1_dotR_freq_apply (v : Vel) (k : Fin 3 → ℤ) :
    dotR v (freq k) = ∑ i : Fin 3, v i * ((k i : ℝ) : ℂ) := by
  unfold dotR freq
  rfl

/-- Componentwise expansion of the `Vel` inner product. -/
private lemma f1_inner_apply (a b : Vel) :
    inner ℂ a b = ∑ j : Fin 3, conj (a j) * b j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => RCLike.inner_apply' _ _

/-- The inner product against `convFull` passes through the defining `tsum`. -/
private lemma f1_inner_convFull {c : (Fin 3 → ℤ) → Vel} (u : Vel)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    inner ℂ u (convFull c k) =
      -∑' l, (Complex.I * dotR (c l) (freq (k - l))) * inner ℂ u (c (k - l)) := by
  have hmaj := summable_convMaj hE hZ k
  have hterm : ∀ l, ‖(Complex.I * dotR (c l) (freq (k - l))) • c (k - l)‖ ≤
      ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by
    intro l
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    calc ‖dotR (c l) (freq (k - l))‖ * ‖c (k - l)‖
        ≤ (‖freq (k - l)‖ * ‖c l‖) * ‖c (k - l)‖ :=
          mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
      _ = ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by ring
  have hsum : Summable fun l => (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) :=
    Summable.of_norm (hmaj.of_nonneg_of_le (fun l => norm_nonneg _) hterm)
  have hmap := ((innerSL ℂ u).hasSum hsum.hasSum).tsum_eq
  simp only [innerSL_apply_apply] at hmap
  rw [convFull, inner_neg_right]
  congr 1
  rw [← hmap]
  exact tsum_congr fun l => inner_smul_right _ _ _

/-- **The per-mode convection pairing**, fully component-expanded: with the
div-free frequency transfer applied, mode `k`'s pairing against `convFull` is
the `(i,j)`-indexed family of shifted coefficient convolutions weighted by the
gradient-test symbols. -/
private lemma f1_convFull_pairing_mode {w c : (Fin 3 → ℤ) → Vel}
    (hdiv : DivFree c)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    inner ℂ (w k) (convFull c k) =
      -∑ i : Fin 3, ∑ j : Fin 3,
        Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j := by
  rw [f1_inner_convFull (w k) hE hZ k]
  congr 1
  have hstep : ∀ l : Fin 3 → ℤ,
      (Complex.I * dotR (c l) (freq (k - l))) * inner ℂ (w k) (c (k - l)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * (c l i * c (k - l) j) := by
    intro l
    rw [f1_dotR_freq_of_divFree hdiv k l, f1_dotR_freq_apply, f1_inner_apply]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsummand : ∀ i j : Fin 3, Summable fun l =>
      Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * (c l i * c (k - l) j) :=
    fun i j => (f1_summable_comp_mul hE k i j).mul_left _
  calc ∑' l, (Complex.I * dotR (c l) (freq (k - l))) * inner ℂ (w k) (c (k - l))
      = ∑' l, ∑ i : Fin 3, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * (c l i * c (k - l) j) :=
        tsum_congr hstep
    _ = ∑ i : Fin 3, ∑' l, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * (c l i * c (k - l) j) :=
        Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsummand i j
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑' l,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * (c l i * c (k - l) j) :=
        Finset.sum_congr rfl fun i _ =>
          Summable.tsum_finsetSum fun j _ => hsummand i j
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => tsum_mul_left

/-- **The left leg**: the spectral convection pairing over the test support,
component-expanded, with the mode sum pulled inside. -/
private lemma f1_left_leg {w c : (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    (hdiv : DivFree c)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) :
    (∑ k ∈ F, inner ℂ (w k) (convFull c k)) =
      -∑ i : Fin 3, ∑ j : Fin 3, ∑ k ∈ F,
        Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j := by
  calc (∑ k ∈ F, inner ℂ (w k) (convFull c k))
      = ∑ k ∈ F, -∑ i : Fin 3, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j :=
        Finset.sum_congr rfl fun k _ => f1_convFull_pairing_mode hdiv hE hZ k
    _ = -∑ k ∈ F, ∑ i : Fin 3, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j :=
        Finset.sum_neg_distrib _
    _ = -∑ i : Fin 3, ∑ k ∈ F, ∑ j : Fin 3,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j := by
        rw [Finset.sum_comm]
    _ = -∑ i : Fin 3, ∑ j : Fin 3, ∑ k ∈ F,
          Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) * ∑' l, c l i * c (k - l) j := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- Band-limited synthesis is the finite sum of Fourier monomials, at the
`Lp` level. -/
private lemma f1_synthT_band {v : (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    (hv : ∀ k, k ∉ F → v k = 0) (j : Fin 3) :
    synthT j v = ∑ m ∈ F, v m j • (mFourierLp (d := Fin 3) 2 m) := by
  have hvs : Summable fun k => ‖v k‖ ^ 2 := f1_summable_of_support hv
  rw [synthT_eq j hvs]
  have h1 := hasSum_synth j v hvs
  have h2 : HasSum (fun k => v k j • (mFourierBasis (d := Fin 3)) k)
      (∑ m ∈ F, v m j • (mFourierBasis (d := Fin 3)) m) :=
    hasSum_sum_of_ne_finset_zero fun k hk => by rw [hv k hk]; simp
  rw [h1.unique h2]
  simp only [coe_mFourierBasis]

/-- The a.e. representative of a finite `Lp` sum is the sum of the
representatives. -/
private lemma f1_coeFn_sum (s : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → L2T3) :
    ((∑ m ∈ s, g m : L2T3) : T3 → ℂ) =ᵐ[(volume : Measure T3)]
      fun x => ∑ m ∈ s, (g m : T3 → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : ((0 : L2T3) : T3 → ℂ) =ᵐ[(volume : Measure T3)] 0 :=
        MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure T3)
      filter_upwards [h0] with x hx
      exact hx
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [MeasureTheory.Lp.coeFn_add (g a) (∑ m ∈ s, g m), ih]
        with x hadd hs
      simp only [hadd, Pi.add_apply, hs]

/-- **Band-limited synthesis is a trigonometric polynomial a.e.** -/
private lemma f1_synthT_band_ae {v : (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    (hv : ∀ k, k ∉ F → v k = 0) (j : Fin 3) :
    ((synthT j v : L2T3) : T3 → ℂ) =ᵐ[(volume : Measure T3)]
      fun x => ∑ m ∈ F, v m j • mFourier m x := by
  rw [f1_synthT_band hv j]
  refine (f1_coeFn_sum F fun m => v m j • (mFourierLp (d := Fin 3) 2 m)).trans ?_
  have h2 : ∀ m ∈ F, ((v m j • (mFourierLp (d := Fin 3) 2 m) : L2T3) : T3 → ℂ)
      =ᵐ[(volume : Measure T3)] fun x => v m j • mFourier m x := by
    intro m _
    filter_upwards [MeasureTheory.Lp.coeFn_smul (v m j) (mFourierLp (d := Fin 3) 2 m),
      coeFn_mFourierLp (d := Fin 3) 2 m] with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2]
  have h3 : ∀ᵐ x ∂(volume : Measure T3), ∀ m ∈ F,
      ((v m j • (mFourierLp (d := Fin 3) 2 m) : L2T3) : T3 → ℂ) x =
        v m j • mFourier m x :=
    (Filter.eventually_all_finset F).mpr h2
  filter_upwards [h3] with x hx
  exact Finset.sum_congr rfl fun m hm => hx m hm

/-- Every `mFourier` monomial has unit modulus pointwise (local copy of the
`private` sibling in `CoeffExtract`). -/
private lemma f1_norm_mFourier (m : Fin 3 → ℤ) (x : T3) : ‖mFourier m x‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod,
    Circle.norm_coe, Finset.prod_const_one]

/-- The pointwise product of two `L²` representatives is integrable. -/
private lemma f1_integrable_mul (f g : L2T3) :
    Integrable (fun x => (f : T3 → ℂ) x * (g : T3 → ℂ) x)
      (volume : Measure T3) := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (star f) g).congr ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star f] with x hx
  rw [RCLike.inner_apply', hx, Pi.star_apply, starRingEnd_apply, star_star]

/-- **The band-limited pairing integral**: integrating an `L²·L²` product
against the conjugate of a band-limited synthesized test collapses to the
finite sum of the product's Fourier coefficients weighted by the conjugated
test coefficients. -/
private lemma f1_integral_pair {u₁ u₂ : L2T3} {v : (Fin 3 → ℤ) → Vel}
    {F : Finset (Fin 3 → ℤ)} (hv : ∀ k, k ∉ F → v k = 0) (j : Fin 3) :
    (∫ x : T3, ((u₁ : T3 → ℂ) x * (u₂ : T3 → ℂ) x) *
        (starRingEnd ℂ) ((synthT j v : T3 → ℂ) x)) =
      ∑ m ∈ F, conj (v m j) *
        mFourierCoeff (fun x : T3 => (u₁ : T3 → ℂ) x * (u₂ : T3 → ℂ) x) m := by
  have hstep1 : (∫ x : T3, ((u₁ : T3 → ℂ) x * (u₂ : T3 → ℂ) x) *
      (starRingEnd ℂ) ((synthT j v : T3 → ℂ) x)) =
      ∫ x : T3, ∑ m ∈ F, conj (v m j) *
        (((u₁ : T3 → ℂ) x * (u₂ : T3 → ℂ) x) * conj (mFourier m x)) := by
    refine integral_congr_ae ?_
    filter_upwards [f1_synthT_band_ae hv j] with x hx
    rw [hx, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_eq_mul, map_mul]
    ring
  have hint : ∀ m ∈ F, Integrable (fun x : T3 => conj (v m j) *
      (((u₁ : T3 → ℂ) x * (u₂ : T3 → ℂ) x) * conj (mFourier m x)))
      (volume : Measure T3) := by
    intro m _
    refine Integrable.const_mul ?_ _
    refine (f1_integrable_mul u₁ u₂).mul_bdd (c := 1)
      (RCLike.continuous_conj.comp_aestronglyMeasurable
        (mFourier m).continuous.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [RCLike.norm_conj, f1_norm_mFourier]
  rw [hstep1, MeasureTheory.integral_finsetSum F hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_const_mul]
  congr 1
  unfold mFourierCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, mFourier_neg]
  ring

/-- **The right leg**: each `(i,j)` convection integral against the gradient
test evaluates to the mode sum of weighted coefficient convolutions. -/
private lemma f1_right_leg {w c : (Fin 3 → ℤ) → Vel} {F : Finset (Fin 3 → ℤ)}
    (hw : ∀ k, k ∉ F → w k = 0)
    (hE : Summable fun k => ‖c k‖ ^ 2)
    (hZ : Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2) (i j : Fin 3) :
    (∫ x : T3, ((synthT i c : T3 → ℂ) x * (synthT j c : T3 → ℂ) x) *
        (starRingEnd ℂ) ((synthT j (f1_gradTest i w) : T3 → ℂ) x)) =
      ∑ k ∈ F, Complex.I * ((k i : ℝ) : ℂ) * conj (w k j) *
        ∑' l, c l i * c (k - l) j := by
  rw [f1_integral_pair (f1_gradTest_support (i := i) hw) j]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [convFull_pairing_physical hE hZ hE hZ i j, f1_conj_gradTest_apply]

set_option linter.unusedVariables false in
/-- **Convection pairing, physical face**: against a finitely supported test
family and a divergence-free, energy- and enstrophy-summable coefficient
field, the spectral pairing with `convFull` is the classical convection
integral `−∫ uᵢuⱼ · conj(Gᵢⱼ)` with `Gᵢⱼ` the synthesized gradient test.
Divergence-freeness is the classical hypothesis: it converts the shifted
frequency of the convection symbol into the full test frequency, which is
what the product coefficients see. -/
theorem convection_pairing_physical {w c : (Fin 3 → ℤ) → Vel}
    {F : Finset (Fin 3 → ℤ)} (hw : ∀ k, k ∉ F → w k = 0)
    (hwsum : Summable fun k => ‖w k‖ ^ 2)
    (hdiv : DivFree c)
    (hE : Summable fun k => ‖c k‖ ^ 2)
    (hZ : Summable fun k => ‖freq k‖ ^ 2 * ‖c k‖ ^ 2) :
    (∑ k ∈ F, inner ℂ (w k) (convFull c k)) =
      -(∑ i : Fin 3, ∑ j : Fin 3, ∫ x : T3,
        ((synthT i c : T3 → ℂ) x * (synthT j c : T3 → ℂ) x) *
          (starRingEnd ℂ) ((synthT j (f1_gradTest i w) : T3 → ℂ) x)) := by
  rw [f1_left_leg hdiv hE hZ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (f1_right_leg hw hE hZ i j).symm

end

end TheoremB
