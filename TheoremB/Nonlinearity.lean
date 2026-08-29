/-
# The nonlinearity in classical form (Tier 6, wave W7)

The last gap of the classical layer.  `Calibration.lean` made the VISCOUS
term classical; the convection term resisted because the Leray projection is
NONLOCAL — there is no pointwise formula for it.  The classical route is the
one physics uses: split the projection into "the convection itself" minus
"a pressure gradient", and identify each piece separately.

* `pressureCoeff` — the spectral pressure `p̂ₖ`, read off the divergence part
  of the convection.  `lerayProj_convFull_apply` is the decomposition
  `P(B)ⱼ = Bⱼ − (2πi·kⱼ)·p̂ₖ`: the projection is the convection minus a
  gradient, exactly as `-∇p` enters Navier-Stokes.  `summable_pressureCoeff`
  makes the pressure a genuine ℓ¹ (hence continuous) function.
* `tsum_char_mul` — the Cauchy product for absolutely convergent character
  series: the product of two Fourier series is the convolution series.  The
  same shear that decoupled the convolution indices in TimeLayer does it
  again here.
* `convection_classical` — the payoff: the synthesized convection IS the
  classical `(u·∇)u`, up to the campaign's `2π`:
  `∑ᵢ uᵢ·∂ᵢuⱼ = −2π · ∑ₖ (convFull c k)ⱼ eₖ`.

Together with `Calibration.viscous_eq_laplacian` this turns the capstone's
spectral right-hand side into `ν_phys·Δu − (1/2π)·(u·∇)u − ∇p`.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.Calibration

namespace TheoremB

open Set UnitAddTorus

noncomputable section

/-! ## Characters multiply by adding frequencies -/

lemma mFourier_mul_apply (l m : Fin 3 → ℤ) (x : UnitAddTorus (Fin 3)) :
    mFourier l x * mFourier m x = mFourier (l + m) x := by
  rw [← UnitAddTorus.mFourier_add]

/-! ## The Cauchy product for ℓ¹ character series -/

set_option maxHeartbeats 1000000 in
/-- **The product of two absolutely convergent Fourier series is the
convolution series.**  (Cauchy product on `ℤ³`: `tsum_mul_tsum_of_summable_norm`
to decouple, then the shear to refiber over `k = l + m`.) -/
theorem tsum_char_mul {a b : (Fin 3 → ℤ) → ℂ}
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖)
    (x : UnitAddTorus (Fin 3)) :
    (∑' l, a l * mFourier l x) * (∑' m, b m * mFourier m x)
      = ∑' k, (∑' l, a l * b (k - l)) * mFourier k x := by
  have hfa : Summable fun l => ‖a l * mFourier l x‖ :=
    ha.congr fun l => by rw [norm_mul, norm_mFourier_apply, mul_one]
  have hfb : Summable fun m => ‖b m * mFourier m x‖ :=
    hb.congr fun m => by rw [norm_mul, norm_mFourier_apply, mul_one]
  rw [tsum_mul_tsum_of_summable_norm hfa hfb]
  -- the decoupled family and its sheared form
  have hprod : Summable (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ‖a p.1‖ * ‖b p.2‖) :=
    ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hFsum : Summable (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      (a p.1 * mFourier p.1 x) * (b p.2 * mFourier p.2 x)) := by
    refine Summable.of_norm (hprod.congr fun p => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mFourier_apply, norm_mFourier_apply,
      mul_one, mul_one]
  have hcomp : ∀ p : (Fin 3 → ℤ) × (Fin 3 → ℤ),
      (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
        (a q.2 * b (q.1 - q.2)) * mFourier q.1 x) (shearEquiv p)
        = (a p.1 * mFourier p.1 x) * (b p.2 * mFourier p.2 x) := by
    rintro ⟨l, m⟩
    have hsub : l + m - l = m := by abel
    show (a l * b (l + m - l)) * mFourier (l + m) x
        = (a l * mFourier l x) * (b m * mFourier m x)
    rw [hsub, ← mFourier_mul_apply]
    ring
  have hGsum : Summable (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      (a q.2 * b (q.1 - q.2)) * mFourier q.1 x) := by
    refine (shearEquiv.summable_iff).mp ?_
    exact hFsum.congr fun p => (hcomp p).symm
  have hGtsum : (∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        (a p.1 * mFourier p.1 x) * (b p.2 * mFourier p.2 x))
      = ∑' q : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        (a q.2 * b (q.1 - q.2)) * mFourier q.1 x := by
    rw [← shearEquiv.tsum_eq (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      (a q.2 * b (q.1 - q.2)) * mFourier q.1 x)]
    exact tsum_congr fun p => (hcomp p).symm
  rw [hGtsum, hGsum.tsum_prod' (fun k => hGsum.prod_factor k)]
  refine tsum_congr fun k => ?_
  calc (∑' l, (a l * b (k - l)) * mFourier k x)
      = ∑' l, mFourier k x * (a l * b (k - l)) := tsum_congr fun l => by ring
    _ = mFourier k x * ∑' l, a l * b (k - l) := tsum_mul_left
    _ = (∑' l, a l * b (k - l)) * mFourier k x := by ring

/-! ## The pressure -/

/-- **The spectral pressure.**  Read off the divergence part of the
convection: `p̂ₖ = ⟪B_k, k⟫ / (‖k‖²·2πi)`.  At `k = 0` the junk convention
gives `0`, which is exactly right — the pressure is defined up to a constant
and its zero mode never enters a gradient. -/
def pressureCoeff (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : ℂ :=
  dotR (convFull c k) (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ) / (2 * Real.pi * Complex.I)

lemma lerayProj_apply (k : Fin 3 → ℤ) (v : Vel) (j : Fin 3) :
    (lerayProj k v) j
      = v j - (dotR v (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ)) * (((k j : ℤ) : ℝ) : ℂ) := rfl

/-- **The Leray projection is the convection minus a pressure gradient.**
`(2πi·kⱼ)·p̂ₖ` is precisely the `j`-th Fourier coefficient of `∂ⱼp`, so this
identity is the spectral form of `P(B) = B − ∇p`. -/
theorem lerayProj_convFull_apply (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ)
    (j : Fin 3) :
    (lerayProj k (convFull c k)) j
      = convFull c k j
        - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff c k := by
  rw [lerayProj_apply, pressureCoeff]
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    simp [hπ, Complex.I_ne_zero]
  have hcast : (((k j : ℤ) : ℝ) : ℂ) = ((k j : ℤ) : ℂ) := by push_cast; ring
  rw [hcast]
  congr 1
  field_simp
  try push_cast
  try ring

/-- The pressure is `ℓ¹`, hence synthesizes to a continuous function. -/
theorem summable_pressureCoeff {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (h0 : Summable fun k => ‖c k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c k‖) :
    Summable fun k => ‖pressureCoeff c k‖ := by
  have hconv := summable_norm_convFull hE hZ h0 h1
  refine (hconv.mul_left (2 * Real.pi)⁻¹).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · have hz : ‖freq (0 : Fin 3 → ℤ)‖ = 0 := by
      have : freq (0 : Fin 3 → ℤ) = 0 := by ext i; simp [freq]
      rw [this, norm_zero]
    have : pressureCoeff c 0 = 0 := by
      rw [pressureCoeff, hz]
      norm_num
    rw [this, norm_zero]
    positivity
  · have hpos : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have hπ : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    have hnorm : ‖pressureCoeff c k‖
        = ‖dotR (convFull c k) (freq k)‖ / ‖freq k‖ ^ 2 / (2 * Real.pi) := by
      rw [pressureCoeff, norm_div, norm_div]
      congr 1
      · congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        have e1 : ‖(2 : ℂ)‖ = 2 := by simp
        have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
        rw [e1, e2]
    rw [hnorm]
    have hd : ‖dotR (convFull c k) (freq k)‖ ≤ ‖freq k‖ * ‖convFull c k‖ :=
      norm_dotR_le _ _
    have hstep : ‖dotR (convFull c k) (freq k)‖ / ‖freq k‖ ^ 2
        ≤ ‖convFull c k‖ := by
      rw [div_le_iff₀ (by positivity)]
      calc ‖dotR (convFull c k) (freq k)‖
          ≤ ‖freq k‖ * ‖convFull c k‖ := hd
        _ ≤ ‖convFull c k‖ * ‖freq k‖ ^ 2 := by
            have hone : (1:ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
            have hsq : ‖freq k‖ ≤ ‖freq k‖ ^ 2 := by nlinarith [hone]
            calc ‖freq k‖ * ‖convFull c k‖
                = ‖convFull c k‖ * ‖freq k‖ := by ring
              _ ≤ ‖convFull c k‖ * ‖freq k‖ ^ 2 :=
                  mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
    calc ‖dotR (convFull c k) (freq k)‖ / ‖freq k‖ ^ 2 / (2 * Real.pi)
        ≤ ‖convFull c k‖ / (2 * Real.pi) := by gcongr
      _ = (2 * Real.pi)⁻¹ * ‖convFull c k‖ := by rw [div_eq_inv_mul]

/-- **The pressure has a gradient.**  One weighted ℓ¹ order for `p̂` — which is
what `hasDerivAt_charSum_insertNth` needs to differentiate the pressure series
— comes for free from the same bound, and does NOT need `‖freq k‖ ≥ 1`:
`‖k‖·‖p̂ₖ‖ ≤ ‖Bₖ‖/2π` exactly. So `∇p` is a genuine object, not a formal
symbol. -/
theorem summable_freq_pressureCoeff {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (h0 : Summable fun k => ‖c k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c k‖) :
    Summable fun k => ‖freq k‖ * ‖pressureCoeff c k‖ := by
  have hconv := summable_norm_convFull hE hZ h0 h1
  refine (hconv.mul_left (2 * Real.pi)⁻¹).of_nonneg_of_le
    (fun _ => by positivity) fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · have hz : ‖freq (0 : Fin 3 → ℤ)‖ = 0 := by
      have h : freq (0 : Fin 3 → ℤ) = 0 := by ext i; simp [freq]
      rw [h, norm_zero]
    rw [hz, zero_mul]
    positivity
  · have hpos : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have hπ : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    have hnorm : ‖pressureCoeff c k‖
        = ‖dotR (convFull c k) (freq k)‖ / ‖freq k‖ ^ 2 / (2 * Real.pi) := by
      rw [pressureCoeff, norm_div, norm_div]
      congr 1
      · congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        have e1 : ‖(2 : ℂ)‖ = 2 := by simp
        have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
        rw [e1, e2]
    rw [hnorm]
    have key : ‖freq k‖ * (‖dotR (convFull c k) (freq k)‖ / ‖freq k‖ ^ 2 / (2 * Real.pi))
        = (‖dotR (convFull c k) (freq k)‖ / ‖freq k‖) / (2 * Real.pi) := by
      field_simp
      try ring
    rw [key, inv_mul_eq_div]
    gcongr
    rw [div_le_iff₀ hpos]
    calc ‖dotR (convFull c k) (freq k)‖
        ≤ ‖freq k‖ * ‖convFull c k‖ := norm_dotR_le _ _
      _ = ‖convFull c k‖ * ‖freq k‖ := by ring

/-- **Every torus point is a coordinate-fiber point.**  So the twisted series
appearing in `convection_classical` really is the spatial derivative `∂ᵢuⱼ`
AT EVERY POINT, via `PeriodicLift.hasDerivAt_charSum_insertNth`: there is no
gap between "derivative along a fiber" and "derivative at `x`". -/
theorem exists_fiber (i : Fin 3) (z : UnitAddTorus (Fin 3)) :
    ∃ (y : UnitAddTorus (Fin 2)) (t : ℝ),
      i.insertNth ((t : ℝ) : UnitAddCircle) y = z := by
  obtain ⟨t, ht⟩ := (QuotientAddGroup.mk_surjective (z i) :
    ∃ t : ℝ, (QuotientAddGroup.mk t : UnitAddCircle) = z i)
  exact ⟨i.removeNth z, t, by rw [show ((t : ℝ) : UnitAddCircle) = z i from ht,
    Fin.insertNth_self_removeNth]⟩

/-! ## The convection is the classical `(u·∇)u` -/

/-- The `j`-th component of the full convection, as a scalar series. -/
theorem convFull_apply (c : (Fin 3 → ℤ) → Vel)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (k : Fin 3 → ℤ) (j : Fin 3) :
    convFull c k j = -∑' l, (Complex.I * dotR (c l) (freq (k - l))) * c (k - l) j := by
  have hsum : Summable fun l => (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) := by
    refine Summable.of_norm ((summable_convMaj hE hZ k).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun l => ?_)
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    calc ‖dotR (c l) (freq (k - l))‖ * ‖c (k - l)‖
        ≤ (‖freq (k - l)‖ * ‖c l‖) * ‖c (k - l)‖ :=
          mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
      _ = ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by ring
  have hcomp : (∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) : Vel) j
      = ∑' l, (Complex.I * dotR (c l) (freq (k - l))) * c (k - l) j :=
    ContinuousLinearMap.map_tsum (EuclideanSpace.proj (𝕜 := ℂ) j) hsum
  show (-(∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) : Vel)) j = _
  rw [show ((-(∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l)) : Vel)) j
      = -((∑' l, (Complex.I * dotR (c l) (freq (k - l))) • c (k - l) : Vel) j) from rfl,
    hcomp]

private lemma norm_intCast_C (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := by simp

/-- The per-term bound feeding every summability certificate below. -/
private lemma nl_term_le (c : (Fin 3 → ℤ) → Vel) (i j : Fin 3) (k l : Fin 3 → ℤ) :
    ‖c l i * ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j)‖
      ≤ 2 * Real.pi * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) := by
  have hπ : (0:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have e : ‖(2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ))‖
      = 2 * Real.pi * |((k - l) i : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
    have e1 : ‖(2 : ℂ)‖ = 2 := by simp
    have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
    have e4 := norm_intCast_C ((k - l) i)
    rw [e1, e2, e4]; ring
  calc ‖c l i * ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j)‖
      = ‖c l i‖ * (2 * Real.pi * |((k - l) i : ℝ)|) * ‖c (k - l) j‖ := by
        rw [norm_mul, norm_mul, e]; ring
    _ ≤ ‖c l‖ * (2 * Real.pi * ‖freq (k - l)‖) * ‖c (k - l)‖ := by
        refine mul_le_mul (mul_le_mul (PiLp.norm_apply_le (c l) i) ?_ (by positivity)
          (norm_nonneg _)) (PiLp.norm_apply_le (c (k - l)) j) (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left (abs_coord_le_norm_freq (k - l) i) hπ
    _ = 2 * Real.pi * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) := by ring

set_option maxHeartbeats 1000000 in
/-- **The convection term is the classical `(u·∇)u`.**  With `u` the velocity
field and `∂ᵢuⱼ` its spatial derivatives (whose coefficients are the
`2πi·kᵢ`-twisted ones, by `PeriodicLift.hasDerivAt_charSum_insertNth`),

  `∑ᵢ uᵢ · ∂ᵢuⱼ  =  −2π · ∑ₖ (convFull c k)ⱼ · eₖ`.

So the campaign's spectral convection IS the classical nonlinearity, carrying
the factor `−1/(2π)`.  This is what makes the Leray-projected right-hand side
classical: combined with `lerayProj_convFull_apply`, the equation's nonlinear
part is `−(1/2π)(u·∇)u − ∇p`. -/
theorem convection_classical (c : (Fin 3 → ℤ) → Vel) (j : Fin 3)
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (h0 : Summable fun k => ‖c k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c k‖)
    (x : UnitAddTorus (Fin 3)) :
    (∑ i : Fin 3, (∑' l, c l i * mFourier l x) *
        (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c m j * mFourier m x))
      = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull c k j * mFourier k x := by
  have hπ : (0:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  -- component and twisted summability
  have hai : ∀ i : Fin 3, Summable fun l => ‖c l i‖ := fun i =>
    h0.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => PiLp.norm_apply_le (c l) i)
  have hbi : ∀ i : Fin 3, Summable fun m =>
      ‖(2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c m j‖ := by
    intro i
    refine (h1.mul_left (2 * Real.pi)).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
    have e : ‖(2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ))‖
        = 2 * Real.pi * |(m i : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
      have e1 : ‖(2 : ℂ)‖ = 2 := by simp
      have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
      have e4 := norm_intCast_C (m i)
      rw [e1, e2, e4]; ring
    rw [norm_mul, e]
    calc 2 * Real.pi * |(m i : ℝ)| * ‖c m j‖
        ≤ 2 * Real.pi * ‖freq m‖ * ‖c m‖ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left
            (abs_coord_le_norm_freq m i) hπ) (PiLp.norm_apply_le (c m) j)
            (norm_nonneg _) (by positivity)
      _ = 2 * Real.pi * (‖freq m‖ * ‖c m‖) := by ring
  -- the inner l-series is absolutely convergent, uniformly usable
  have hinnerSum : ∀ (i : Fin 3) (k : Fin 3 → ℤ), Summable fun l =>
      ‖c l i * ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j)‖ :=
    fun i k => ((summable_convMaj hE hZ k).mul_left (2 * Real.pi)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun l => nl_term_le c i j k l)
  -- per-i, the Cauchy product
  have hprod : ∀ i : Fin 3,
      (∑' l, c l i * mFourier l x) *
          (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c m j * mFourier m x)
        = ∑' k, (∑' l, c l i *
            ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j))
              * mFourier k x := fun i => tsum_char_mul (hai i) (hbi i) x
  -- each k-family is summable
  have hFsum : ∀ i : Fin 3, Summable fun k => (∑' l, c l i *
      ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j))
        * mFourier k x := by
    intro i
    refine Summable.of_norm ((((summable_convMaj_l1 h0 h1).1).mul_left
      (2 * Real.pi)).of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_)
    rw [norm_mul, norm_mFourier_apply, mul_one]
    refine (norm_tsum_le_tsum_norm (hinnerSum i k)).trans ?_
    calc (∑' l, ‖c l i * ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j)‖)
        ≤ ∑' l, 2 * Real.pi * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) :=
          (hinnerSum i k).tsum_le_tsum (fun l => nl_term_le c i j k l)
            ((summable_convMaj hE hZ k).mul_left (2 * Real.pi))
      _ = 2 * Real.pi * ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := tsum_mul_left
  -- assemble
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hprod i),
    ← Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) => hFsum i)]
  have hconvSum : Summable fun k => convFull c k j * mFourier k x := by
    refine Summable.of_norm ((summable_norm_convFull hE hZ h0 h1).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_)
    rw [norm_mul, norm_mFourier_apply, mul_one]
    exact PiLp.norm_apply_le (convFull c k) j
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  -- pointwise in k: the three directions rebuild dotR, and convFull appears
  have hswap : (∑ i : Fin 3, (∑' l, c l i *
        ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j))
          * mFourier k x)
      = (∑' l, ∑ i : Fin 3, c l i *
          ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j))
            * mFourier k x := by
    rw [← Finset.sum_mul]
    congr 1
    exact (Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) =>
      Summable.of_norm (hinnerSum i k))).symm
  rw [hswap]
  have hdot : ∀ l : Fin 3 → ℤ, (∑ i : Fin 3, c l i *
      ((2 * Real.pi * Complex.I * (((k - l) i : ℤ) : ℂ)) * c (k - l) j))
      = ((2 * Real.pi : ℝ) : ℂ) *
        ((Complex.I * dotR (c l) (freq (k - l))) * c (k - l) j) := by
    intro l
    rw [dotR, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ((freq (k - l)) i : ℝ) = (((k - l) i : ℤ) : ℝ) := rfl
    rw [hc]
    push_cast
    ring
  rw [tsum_congr hdot, tsum_mul_left, convFull_apply c hE hZ k j]
  push_cast
  ring

end

end TheoremB
