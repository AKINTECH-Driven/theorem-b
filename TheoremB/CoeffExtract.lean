/-
# Coefficient extraction and the product-coefficient identity (Tier 5)

The inverse of the synthesis: extracting the coefficient flow from a torus
field, with Parseval faces and Lipschitz mode evaluation — the machinery
that lets `theorem_B_unique` reach function-space solutions. Plus the
round-trip lemmas, and DELTA-3's `convFull_pairing_physical`: the Fourier
coefficient of a pointwise product of synthesized fields IS the coefficient
convolution — the bridge from `convFull` to the physical convection, proved
entirely inside L² by the twist trick.
-/
import TheoremB.TorusStructure

namespace TheoremB

open Set MeasureTheory UnitAddTorus
open scoped lp ComplexConjugate ENNReal

noncomputable section

local instance ce_ms : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance ce_haar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance ce_prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### DELTA-2: coefficient extraction

The inverse direction of the synthesis layer: from a component triple
`u : Fin 3 → L2T3` back to a `Vel`-valued coefficient family, with the
recovery identity on synthesized fields, square-summability, the Parseval
energy identity, and the per-mode Lipschitz bound. -/

/-- **Coefficient extraction**: the `Vel`-valued Fourier coefficient family
of a component triple `u : Fin 3 → L2T3`. -/
def extractCoeff (u : Fin 3 → L2T3) : (Fin 3 → ℤ) → Vel :=
  fun k => (WithLp.toLp 2 fun j => mFourierCoeff ((u j : L2T3) : T3 → ℂ) k)

@[simp] lemma d2_extractCoeff_apply (u : Fin 3 → L2T3) (k : Fin 3 → ℤ) (j : Fin 3) :
    extractCoeff u k j = mFourierCoeff ((u j : L2T3) : T3 → ℂ) k := rfl

/-- **Extraction inverts synthesis** on the square-summable class. -/
theorem extractCoeff_synthT {c : (Fin 3 → ℤ) → Vel}
    (hc : Summable fun k => ‖c k‖ ^ 2) :
    extractCoeff (fun j => synthT j c) = c := by
  funext k
  refine PiLp.ext fun j => ?_
  show mFourierCoeff ((synthT j c : L2T3) : T3 → ℂ) k = c k j
  exact mFourierCoeff_synthT j hc k

/-- The scalar coefficient family of any `L2T3` element is square-summable
(ℓ² membership of the `mFourierBasis` representation). -/
lemma d2_summable_coeff (f : L2T3) :
    Summable fun k : Fin 3 → ℤ => ‖mFourierCoeff (f : T3 → ℂ) k‖ ^ 2 := by
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  have hsum := (lp.memℓp ((mFourierBasis (d := Fin 3)).repr f)).summable
    (by rw [h2]; norm_num)
  refine hsum.congr fun k => ?_
  rw [mFourierBasis_repr, h2, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- The `Vel`-norm square of an extracted coefficient splits into the three
component coefficient squares. -/
lemma d2_norm_sq_extractCoeff (u : Fin 3 → L2T3) (k : Fin 3 → ℤ) :
    ‖extractCoeff u k‖ ^ 2
      = ∑ j : Fin 3, ‖mFourierCoeff ((u j : L2T3) : T3 → ℂ) k‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, d2_extractCoeff_apply]

/-- **Square-summability of extraction**: every component triple extracts to
a square-summable coefficient family. -/
theorem summable_extractCoeff (u : Fin 3 → L2T3) :
    Summable fun k => ‖extractCoeff u k‖ ^ 2 := by
  have hsum : Summable fun k : Fin 3 → ℤ =>
      ∑ j : Fin 3, ‖mFourierCoeff ((u j : L2T3) : T3 → ℂ) k‖ ^ 2 :=
    summable_sum fun j _ => d2_summable_coeff (u j)
  exact hsum.congr fun k => (d2_norm_sq_extractCoeff u k).symm

/-- Scalar Parseval for one component: the coefficient square sum is the
squared L² norm. -/
lemma d2_tsum_coeff_sq (f : L2T3) :
    ∑' k : Fin 3 → ℤ, ‖mFourierCoeff (f : T3 → ℂ) k‖ ^ 2 = ‖f‖ ^ (2:ℝ) := by
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  have h := lp.norm_rpow_eq_tsum (p := 2)
    (E := fun _ : (Fin 3 → ℤ) => ℂ) (by norm_num) ((mFourierBasis (d := Fin 3)).repr f)
  simp only [h2] at h
  have hn : ‖(mFourierBasis (d := Fin 3)).repr f‖ = ‖f‖ :=
    LinearIsometryEquiv.norm_map _ f
  rw [hn] at h
  rw [h]
  exact tsum_congr fun k => by
    rw [mFourierBasis_repr, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- **Parseval for extraction**: the coefficient energy of the extracted
family is the total component L² energy. -/
theorem en_extractCoeff (u : Fin 3 → L2T3) :
    en (extractCoeff u) = ∑ j : Fin 3, ‖u j‖ ^ (2:ℝ) := by
  have hen : en (extractCoeff u) = ∑' k, ‖extractCoeff u k‖ ^ 2 := rfl
  rw [hen, tsum_congr fun k => d2_norm_sq_extractCoeff u k,
    Summable.tsum_finsetSum fun j _ => d2_summable_coeff (u j)]
  exact Finset.sum_congr rfl fun j _ => d2_tsum_coeff_sq (u j)

/-- Each scalar coefficient defect is dominated by the component L² defect. -/
lemma d2_coeff_sub_le (f g : L2T3) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff (f : T3 → ℂ) k - mFourierCoeff (g : T3 → ℂ) k‖ ≤ ‖f - g‖ := by
  have h1 : mFourierCoeff (f : T3 → ℂ) k - mFourierCoeff (g : T3 → ℂ) k
      = ((mFourierBasis (d := Fin 3)).repr (f - g) : (Fin 3 → ℤ) → ℂ) k := by
    rw [← mFourierBasis_repr, ← mFourierBasis_repr, map_sub, lp.coeFn_sub, Pi.sub_apply]
  rw [h1]
  calc ‖((mFourierBasis (d := Fin 3)).repr (f - g) : (Fin 3 → ℤ) → ℂ) k‖
      ≤ ‖(mFourierBasis (d := Fin 3)).repr (f - g)‖ :=
        lp.norm_apply_le_norm (by norm_num) _ k
    _ = ‖f - g‖ := LinearIsometryEquiv.norm_map _ _

/-- **Per-mode Lipschitz bound for extraction**: each coefficient defect
square is dominated by the total component L² defect energy. -/
theorem extractCoeff_lipschitz (u v : Fin 3 → L2T3) (k : Fin 3 → ℤ) :
    ‖extractCoeff u k - extractCoeff v k‖ ^ 2 ≤
      ∑ j : Fin 3, ‖u j - v j‖ ^ (2:ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun j _ => ?_
  have happ : (extractCoeff u k - extractCoeff v k) j
      = mFourierCoeff ((u j : L2T3) : T3 → ℂ) k
        - mFourierCoeff ((v j : L2T3) : T3 → ℂ) k := by
    rw [PiLp.sub_apply, d2_extractCoeff_apply, d2_extractCoeff_apply]
  rw [happ, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  exact pow_le_pow_left₀ (norm_nonneg _) (d2_coeff_sub_le (u j) (v j) k) 2

/-- Two L² functions on the torus with the same Fourier coefficients agree. -/
lemma L2_ext_of_coeff {f g : L2T3}
    (h : ∀ k, mFourierCoeff (f : T3 → ℂ) k = mFourierCoeff (g : T3 → ℂ) k) :
    f = g := by
  have hrepr : (mFourierBasis (d := Fin 3)).repr f =
      (mFourierBasis (d := Fin 3)).repr g := by
    apply lp.ext
    funext k
    rw [mFourierBasis_repr, mFourierBasis_repr]
    exact h k
  exact (mFourierBasis (d := Fin 3)).repr.injective hrepr

lemma extractCoeff_apply (u : Fin 3 → L2T3) (k : Fin 3 → ℤ) (j : Fin 3) :
    extractCoeff u k j = mFourierCoeff ((u j : L2T3) : T3 → ℂ) k := rfl

/-- Synthesis of the extraction recovers the field. -/
lemma synthT_extractCoeff (u : Fin 3 → L2T3)
    (hc : Summable fun k => ‖extractCoeff u k‖ ^ 2) (j : Fin 3) :
    synthT j (extractCoeff u) = u j := by
  apply L2_ext_of_coeff
  intro k
  rw [mFourierCoeff_synthT j hc k]
  rfl

/-- The component lemma for `conjVel`. -/
lemma conjVel_apply' (v : Vel) (j : Fin 3) :
    conjVel v j = (starRingEnd ℂ) (v j) := rfl

/-! ### DELTA-3: the physical convection identification

The Fourier coefficient of a pointwise product of two synthesized components
is the coefficient convolution.  The route is the twist trick: for `F, G ∈ L²`,

  `mFourierCoeff (F·G) m = ∫ mFourier(−m)·F·G = ∫ conj(mFourier m · conj F) · G`,

and `mFourier m · conj F` is again an `L²` element (unit-modulus multiplier),
so Parseval for inner products (`hasSum_prod_mFourierCoeff`) turns the right
side into the absolutely convergent coefficient pairing — no truncation, no
`L¹` Hölder machinery. -/

/-- Every `mFourier` monomial has unit modulus pointwise. -/
private lemma d3_norm_mFourier (m : Fin 3 → ℤ) (x : T3) : ‖mFourier m x‖ = 1 := by
  simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
    Finset.prod_const_one]

/-- **The twist is `L²`**: multiplying the conjugate of an `L²` field by a
Fourier monomial lands back in `L²`. -/
private lemma d3_memLp_twist (m : Fin 3 → ℤ) (F : L2T3) :
    MemLp (fun x : T3 => mFourier m x * conj ((F : T3 → ℂ) x)) 2 (volume : Measure T3) := by
  refine MemLp.of_le (MeasureTheory.Lp.memLp F) ?_ ?_
  · exact ((mFourier m).continuous.aestronglyMeasurable).mul
      (RCLike.continuous_conj.comp_aestronglyMeasurable
        (MeasureTheory.Lp.aestronglyMeasurable F))
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, RCLike.norm_conj, d3_norm_mFourier, one_mul]

/-- Fourier coefficients only see the a.e. class: the `toLp` of the twist has
the twist's coefficients. -/
private lemma d3_mFourierCoeff_congr_ae {f g : T3 → ℂ}
    (h : f =ᵐ[(volume : Measure T3)] g) (k : Fin 3 → ℤ) :
    mFourierCoeff f k = mFourierCoeff g k := by
  unfold mFourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

/-- **The twist coefficient identity**: the `k`-th coefficient of
`mFourier m · conj F` is the conjugated `(m−k)`-th coefficient of `F`. -/
private lemma d3_mFourierCoeff_twist (m k : Fin 3 → ℤ) (F : T3 → ℂ) :
    mFourierCoeff (fun x : T3 => mFourier m x * conj (F x)) k =
      conj (mFourierCoeff F (m - k)) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  calc mFourier (-k) x • (mFourier m x * conj (F x))
      = (mFourier (-k) x * mFourier m x) * conj (F x) := by
        rw [smul_eq_mul, mul_assoc]
    _ = mFourier (m - k) x * conj (F x) := by
        rw [← mFourier_add, neg_add_eq_sub]
    _ = conj (mFourier (-(m - k)) x • F x) := by
        rw [smul_eq_mul, map_mul, mFourier_neg, Complex.conj_conj]

/-- **The abstract product-pairing**: for `F, G ∈ L²(T³)`, the `m`-th Fourier
coefficient of the pointwise product is the (absolutely convergent) coefficient
convolution, as a `HasSum`. -/
private lemma d3_hasSum_pairing (m : Fin 3 → ℤ) (F G : L2T3) :
    HasSum
      (fun k => mFourierCoeff (F : T3 → ℂ) (m - k) * mFourierCoeff (G : T3 → ℂ) k)
      (mFourierCoeff (fun x : T3 => (F : T3 → ℂ) x * (G : T3 → ℂ) x) m) := by
  have hφ : MemLp (fun x : T3 => mFourier m x * conj ((F : T3 → ℂ) x)) 2
      (volume : Measure T3) := d3_memLp_twist m F
  have h := hasSum_prod_mFourierCoeff (hφ.toLp _) G
  have hcoeff : ∀ k : Fin 3 → ℤ,
      conj (mFourierCoeff ((hφ.toLp _ : L2T3) : T3 → ℂ) k) =
        mFourierCoeff (F : T3 → ℂ) (m - k) := by
    intro k
    rw [d3_mFourierCoeff_congr_ae hφ.coeFn_toLp k, d3_mFourierCoeff_twist m k,
      Complex.conj_conj]
  have hint : (∫ t, conj ((hφ.toLp _ : L2T3) t) * (G : T3 → ℂ) t) =
      mFourierCoeff (fun x : T3 => (F : T3 → ℂ) x * (G : T3 → ℂ) x) m := by
    unfold mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp] with x hx
    rw [hx, map_mul, Complex.conj_conj, ← mFourier_neg, smul_eq_mul, mul_assoc]
  rw [hint] at h
  exact h.congr_fun fun k => by rw [hcoeff k]

/-- **DELTA-3, the physical convection identification**: the Fourier
coefficient of the pointwise product of two synthesized components is the
coefficient convolution — the bridge between `convFull` and the physical
`(u·∇)u` pairing. -/
theorem convFull_pairing_physical {a b : (Fin 3 → ℤ) → Vel} {m : Fin 3 → ℤ}
    (haE : Summable fun k => ‖a k‖ ^ 2) (haZ : Summable fun k => ‖freq k‖ ^ 2 * ‖a k‖ ^ 2)
    (hbE : Summable fun k => ‖b k‖ ^ 2) (hbZ : Summable fun k => ‖freq k‖ ^ 2 * ‖b k‖ ^ 2)
    (i j : Fin 3) :
    mFourierCoeff (fun x : T3 => (synthT i a : T3 → ℂ) x * (synthT j b : T3 → ℂ) x) m =
      ∑' k, a k i * b (m - k) j := by
  have h := d3_hasSum_pairing m (synthT i a) (synthT j b)
  have h2 : HasSum (fun k => a (m - k) i * b k j)
      (mFourierCoeff
        (fun x : T3 => (synthT i a : T3 → ℂ) x * (synthT j b : T3 → ℂ) x) m) := by
    refine h.congr_fun fun k => ?_
    rw [mFourierCoeff_synthT i haE (m - k), mFourierCoeff_synthT j hbE k]
  rw [← h2.tsum_eq]
  have h3 := (Equiv.subLeft m).tsum_eq (f := fun k => a k i * b (m - k) j)
  simp only [Equiv.subLeft_apply, sub_sub_cancel] at h3
  exact h3

end

end TheoremB
