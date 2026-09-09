/-
# Joint smoothness of the eternal flow on the closed slab (Tier 8b, wave W2)

The eternal small-data flow of `theorem_B_time_smooth` lifts to a velocity
field and a pressure field that are jointly `C^∞` in `(x, t)` on the CLOSED
slab `ℝ³ × [0, ∞)`.  This file delivers:

1. `pLift`, the ℤ³-periodic lift of the pressure (the character series of
   `pressureCoeff`), and `pressureBil`, the pressure read off the BILINEAR
   convection (`pressureBil c c = pressureCoeff c` definitionally,
   `pressureBil_self`); `summable_freq_pow_pressureCoeff` gives the pressure
   every weighted ℓ¹ order from the velocity's, through the pointwise bound
   `‖p̂_k‖ ≤ ‖B_k‖` (`norm_pressureFun_le`, with `one_le_norm_freq` for
   `k ≠ 0` and the junk value `0` at `k = 0`) and the ℓ¹ closure
   `tsum_weighted_convBil_le`; `hasDerivAt_pressureBil_flow` is the time
   derivative of the pressure along two differentiable coefficient flows
   (the linear functional `pressureFun` applied to `hasDerivAt_convBil_flow`).
2. `iteratedDerivWithin_eq_chain`: on the window `Ico 0 b` the iterated
   within-derivative of a scalar mode is the derivative chain, order by
   order; `exists_mode_majorant_of_windowBound` (and its general-order
   sibling `exists_mode_majorant_of_windowBound'`): a window bound at orders
   `0` and `p` gives the per-mode majorant `C₀·[k = 0] + C_p·‖k‖⁻ᵖ`.
3. `norm_iteratedFDerivWithin_liftTerm_le`: the mixed-order bound on one
   term of the lift on the slab `univ ×ˢ Ico 0 b` (the Leibniz rule
   `norm_iteratedFDerivWithin_smul_le`; the time factor through
   `ContinuousLinearMap.iteratedFDerivWithin_comp_right` along `snd` with
   `‖snd‖ ≤ 1`; the character through `iteratedFDerivWithin_eq_iteratedFDeriv`
   and `ContinuousLinearMap.iteratedFDeriv_comp_right` along `fst`, bounded
   by `(2π‖freq k‖)^q` without factorials).
4. `contDiffOn_lift_slab`: the Weierstrass M-test of `WithinSeries.lean`
   (`contDiffOn_tsum_of_convex` at `N = ⊤`) on every window slab
   `univ ×ˢ Ico 0 b`, with the majorant at mixed order `m` built from the
   per-mode majorants of the `i`-th time derivative at window order
   `m - i + 4` (so the `k`-sum converges against `summable_inv_freq_pow_four`),
   then glued to the closed slab by `contDiffOn_of_locally_contDiffOn`.
   Generic in the coefficient chain: the velocity components and the
   pressure both feed it.
5. `theorem_B_joint_smooth`, the capstone: the twenty-two clauses of
   `theorem_B_time_smooth` re-exported verbatim, plus every weighted ℓ¹ order
   of the pressure (clause 23), joint `C^∞` of every velocity component's
   lift on the closed slab (clause 24, the slab lemma at the component chain
   of clause 21) and joint `C^∞` of the pressure lift on the closed slab
   (clause 25, the slab lemma at the pressure chain
   `P n = pressureFun (S n)`, whose base is `pressureCoeff` by
   `convBil_self` at the Leibniz sum of order `0`, whose derivatives come
   from the exported `S`-derivatives through the linear functional, whose
   endpoint derivative at `t = 0` comes from the endpoint tool
   `hasDerivWithinAt_Ici_of_tendsto_deriv`, and whose windows are the
   windows of `S n` through `‖P n t k‖ ≤ ‖S n t k‖`).

Honest scope.  `∞` is `(⊤ : ℕ∞)` cast into `WithTop ℕ∞`, NOT `ω`: no
analyticity in space or time is claimed.  Smoothness is on the CLOSED slab
`univ ×ˢ Ici 0`, with one-sided derivatives at `t = 0` within the slab.
The constant `κ` and the inherited Sobolev growth constants are of explicit
form, exported as compiled existentials; the window constants of the chain
and the majorants of the slab lemma are UNTRACKED existentials.  Nothing
here is new mathematics: the M-test on a convex set and the bootstrap are
textbook (Temam, *Navier-Stokes Equations*, Ch. III;
Robinson-Rodrigo-Sadowski, *The Three-Dimensional Navier-Stokes
Equations*, Ch. 6-7; Constantin-Foias, *Navier-Stokes Equations*, Ch. 10;
chapter numbers unverified); the within-convex tsum engine it consumes is
absent from Mathlib at the pin, grep-verified, not new mathematics.
Priority is not claimed for anything.  The machine-checked Navier-Stokes
work this file sits beside is named in the announcement and the README
(uda-lab/leray-hopf, HeliCorgi's ns-mns2-flowmap-bridge, Miller, OpenAI's
forced-breakdown certificate, Alpöge and Buckmaster); none of it is
composed with, reproduced by, or superseded by anything here.

Cloned private declarations (never un-privated): PeriodicLift's
`hasDerivAt_cexp_mul_real`, `iteratedDeriv_cexp_mul_real`,
`contDiff_cexp_mul_real`, `term_eq_comp` (here `char_eq_comp`, the bare
character) and `norm_iteratedFDeriv_term_le` (here
`norm_iteratedFDeriv_char_le`, the bare character); TimeSmooth's
`dotR_add_left` and `freq_zero_eq'`.

Statement observations (not drift; every frozen statement is proved as
written).  The frozen order-4 majorant `exists_mode_majorant_of_windowBound`
is an instance of the general-order sibling, and the slab lemma needs the
general order: at mixed order `m` with `i` time derivatives the `k`-sum
converges only from window order `m - i + 4`.  The blueprint's route note
for `summable_freq_pow_pressureCoeff` bounds `‖k‖^p‖p̂_k‖` by
`‖k‖^(p-1)‖B_k‖/(2π)`; the coarser `‖p̂_k‖ ≤ ‖B_k‖` suffices for
summability and is what is proved.

Junk-tsum discipline: every tsum statement carries its Summable certificate
as a hypothesis or exports it.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.TimeSmooth
import TheoremB.WithinSeries

namespace TheoremB

open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ContDiff

/-! ## 1. The pressure lift and the bilinear pressure -/

/-- **The ℤ³-periodic lift of the pressure**: the character series of the
spectral pressure `pressureCoeff c`, read on ℝ³ through the quotient map to
the unit torus.  Total definition; every regularity statement carries its own
`Summable` certificate. -/
noncomputable def pLift (c : (Fin 3 → ℤ) → Vel) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => ∑' k : Fin 3 → ℤ,
    pressureCoeff c k * ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))

/-- The pressure read off the BILINEAR convection: `⟪convBil a b k, k⟫ / (‖k‖²·2πi)`.
At `a = b` it is `pressureCoeff` definitionally (`pressureBil_self`). -/
noncomputable def pressureBil (a b : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : ℂ :=
  dotR (convBil a b k) (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ) / (2 * Real.pi * Complex.I)

/-- The diagonal of the bilinear pressure is the spectral pressure, by `rfl`. -/
theorem pressureBil_self (c : (Fin 3 → ℤ) → Vel) : pressureBil c c = pressureCoeff c := rfl

/-! ## 2. The pressure functional (non-frozen)

`pressureFun v k = ⟪v, k⟫ / (‖k‖²·2πi)` is the linear functional through which
both `pressureBil` and `pressureCoeff` are read (`pressureBil a b k =
pressureFun (convBil a b k) k` and `pressureCoeff c k = pressureFun (convFull c k) k`,
both by `rfl`).  It is additive, continuous, differentiates along a
differentiable `Vel`-valued function (with and without a set), and is bounded
by the norm of its argument. -/

/-- The pressure functional. -/
noncomputable def pressureFun (v : Vel) (k : Fin 3 → ℤ) : ℂ :=
  dotR v (freq k) / ((‖freq k‖ ^ 2 : ℝ) : ℂ) / (2 * Real.pi * Complex.I)

private lemma freq_zero_eq'' : freq (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [freq]

private lemma dotR_add_left' (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (v + w) r = dotR v r + dotR w r := by
  simp only [dotR, WithLp.ofLp_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `pressureCoeff` is the pressure functional of the full convection, by `rfl`. -/
theorem pressureCoeff_eq_pressureFun (c : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) :
    pressureCoeff c k = pressureFun (convFull c k) k := rfl

/-- The pressure functional is additive. -/
theorem pressureFun_add (v w : Vel) (k : Fin 3 → ℤ) :
    pressureFun (v + w) k = pressureFun v k + pressureFun w k := by
  simp only [pressureFun, dotR_add_left', add_div]

/-- The pressure functional differentiates along a differentiable `Vel`-valued
function (components through `EuclideanSpace.proj … restrictScalars ℝ`, the
pairing as a finite sum of products, then two divisions by constants). -/
theorem HasDerivAt.pressureFun {f : ℝ → Vel} {f' : Vel} {t : ℝ} (k : Fin 3 → ℤ)
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => pressureFun (f s) k) (pressureFun f' k) t := by
  have hcomp : ∀ j : Fin 3, HasDerivAt (fun s => (f s) j) (f' j) t := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf
  have hd : HasDerivAt (fun s => dotR (f s) (freq k)) (dotR f' (freq k)) t := by
    unfold dotR
    exact HasDerivAt.fun_sum fun j _ => (hcomp j).mul_const _
  unfold TheoremB.pressureFun
  exact (hd.div_const _).div_const _

/-- The within-set twin of `HasDerivAt.pressureFun`. -/
theorem HasDerivWithinAt.pressureFun {f : ℝ → Vel} {f' : Vel} {s : Set ℝ} {t : ℝ}
    (k : Fin 3 → ℤ) (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun s => pressureFun (f s) k) (pressureFun f' k) s t := by
  have hcomp : ∀ j : Fin 3, HasDerivWithinAt (fun s => (f s) j) (f' j) s t := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hf
  have hd : HasDerivWithinAt (fun s => dotR (f s) (freq k)) (dotR f' (freq k)) s t := by
    unfold dotR
    exact HasDerivWithinAt.fun_sum fun j _ => (hcomp j).mul_const _
  unfold TheoremB.pressureFun
  exact (hd.div_const _).div_const _

/-- The pressure functional is continuous. -/
theorem continuous_pressureFun (k : Fin 3 → ℤ) : Continuous fun v : Vel => pressureFun v k := by
  have hd : Continuous fun v : Vel => dotR v (freq k) := by
    unfold dotR
    exact continuous_finsetSum _ fun j _ =>
      (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.mul continuous_const
  unfold TheoremB.pressureFun
  exact (hd.div_const _).div_const _

/-- At the zero mode the pressure functional is the junk value `0`. -/
theorem pressureFun_zero (v : Vel) : pressureFun v 0 = 0 := by
  rw [pressureFun, freq_zero_eq'']
  simp

/-- **The pressure functional is bounded by its argument**: `‖p̂‖ ≤ ‖v‖`
(`norm_dotR_le`, `‖k‖ ≥ 1` for `k ≠ 0`, and `2π ≥ 1`). -/
theorem norm_pressureFun_le (v : Vel) (k : Fin 3 → ℤ) : ‖pressureFun v k‖ ≤ ‖v‖ := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [pressureFun_zero, norm_zero]; exact norm_nonneg _
  · have hone : (1:ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    have hpos : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos hone
    have hπ : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hnorm : ‖pressureFun v k‖
        = ‖dotR v (freq k)‖ / ‖freq k‖ ^ 2 / (2 * Real.pi) := by
      rw [pressureFun, norm_div, norm_div]
      congr 1
      · congr 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
        have e1 : ‖(2 : ℂ)‖ = 2 := by simp
        have e2 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by simp [Real.pi_nonneg]
        rw [e1, e2]
    rw [hnorm]
    have hd : ‖dotR v (freq k)‖ ≤ ‖freq k‖ * ‖v‖ := norm_dotR_le _ _
    calc ‖dotR v (freq k)‖ / ‖freq k‖ ^ 2 / (2 * Real.pi)
        ≤ ‖dotR v (freq k)‖ / ‖freq k‖ ^ 2 := div_le_self (by positivity) hπ
      _ ≤ ‖v‖ := by
          rw [div_le_iff₀ (by positivity)]
          calc ‖dotR v (freq k)‖ ≤ ‖freq k‖ * ‖v‖ := hd
            _ ≤ ‖v‖ * ‖freq k‖ ^ 2 := by
                have := mul_nonneg (norm_nonneg v) (mul_nonneg hpos.le (sub_nonneg.mpr hone))
                nlinarith

/-! ## 3. The pressure has every weighted ℓ¹ order -/

/-- **Every weighted ℓ¹ order of the pressure** from every weighted ℓ¹ order
of the velocity: `‖k‖^p‖p̂_k‖ ≤ ‖k‖^p‖B_k‖` termwise (`norm_pressureFun_le`),
and the convection has every order by `tsum_weighted_convBil_le` at `a = b = c`
(`convBil_self`). -/
theorem summable_freq_pow_pressureCoeff {c : (Fin 3 → ℤ) → Vel}
    (hc : ∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖c l‖) (p : ℕ) :
    Summable fun k => ‖freq k‖ ^ p * ‖pressureCoeff c k‖ := by
  have h := (tsum_weighted_convBil_le p hc hc).1
  rw [convBil_self] at h
  refine h.of_nonneg_of_le (fun _ => by positivity) fun k => ?_
  exact mul_le_mul_of_nonneg_left (norm_pressureFun_le (convFull c k) k) (by positivity)

/-! ## 4. The time derivative of the bilinear pressure along a flow -/

/-- **The time derivative of the bilinear pressure** along two differentiable
coefficient flows with summable window majorants: the linear functional
`pressureFun` applied to `hasDerivAt_convBil_flow`, then `pressureFun_add`. -/
theorem hasDerivAt_pressureBil_flow {a a' b b' : ℝ → (Fin 3 → ℤ) → Vel} {t₀ t₁ : ℝ}
    (ha : ∀ t ∈ Ioo t₀ t₁, ∀ l, HasDerivAt (fun s => a s l) (a' t l) t)
    (hb : ∀ t ∈ Ioo t₀ t₁, ∀ l, HasDerivAt (fun s => b s l) (b' t l) t)
    {A A' B B' : (Fin 3 → ℤ) → ℝ}
    (hAmaj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖a t l‖ ≤ A l)
    (hA'maj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖a' t l‖ ≤ A' l)
    (hBmaj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖b t l‖ ≤ B l)
    (hB'maj : ∀ t ∈ Ioo t₀ t₁, ∀ l, ‖b' t l‖ ≤ B' l)
    (hA : Summable A) (hA' : Summable A')
    (hB1 : Summable fun l => ‖freq l‖ * B l)
    (hB'1 : Summable fun l => ‖freq l‖ * B' l)
    {t : ℝ} (ht : t ∈ Ioo t₀ t₁) (k : Fin 3 → ℤ) :
    HasDerivAt (fun s => pressureBil (a s) (b s) k)
      (pressureBil (a t) (b' t) k + pressureBil (a' t) (b t) k) t := by
  have h := hasDerivAt_convBil_flow ha hb hAmaj hA'maj hBmaj hB'maj hA hA' hB1 hB'1 ht k
  have h2 := HasDerivAt.pressureFun k h
  rw [pressureFun_add] at h2
  exact h2

/-! ## 5. The scalar chain on a window: iterated derivatives and per-mode majorants -/

/-- **The iterated within-derivative on the window is the chain**: with the
derivatives on `Ioi 0` and the right derivative at `0`, the `n`-th
`iteratedDerivWithin` of `a` on `Ico 0 b` is `D n` (induction on `n`;
`iteratedDerivWithin_succ`, `derivWithin_congr`, `uniqueDiffOn_Ico`). -/
theorem iteratedDerivWithin_eq_chain {a : ℝ → ℂ} {D : ℕ → ℝ → ℂ} {b : ℝ}
    (hD0 : D 0 = a)
    (hchain : ∀ n, ∀ t ∈ Ioi (0:ℝ), HasDerivAt (D n) (D (n + 1) t) t)
    (hzero : ∀ n, HasDerivWithinAt (D n) (D (n + 1) 0) (Ici (0:ℝ)) 0)
    (n : ℕ) :
    ∀ t ∈ Ico (0:ℝ) b, iteratedDerivWithin n a (Ico (0:ℝ) b) t = D n t := by
  have hdw : ∀ n, ∀ t ∈ Ico (0:ℝ) b, HasDerivWithinAt (D n) (D (n + 1) t) (Ico (0:ℝ) b) t := by
    intro n t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; exact (hzero n).mono Ico_subset_Ici_self
    · exact (hchain n t h).hasDerivWithinAt
  induction n with
  | zero => intro t _; rw [iteratedDerivWithin_zero, hD0]
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    have hcongr : derivWithin (iteratedDerivWithin n a (Ico (0:ℝ) b)) (Ico (0:ℝ) b) t
        = derivWithin (D n) (Ico (0:ℝ) b) t :=
      derivWithin_congr (fun s hs => ih s hs) (ih t ht)
    rw [hcongr]
    exact (hdw n t ht).derivWithin (uniqueDiffOn_Ico 0 b t ht)

/-- **The per-mode majorant at a general order** (non-frozen): a window bound
at orders `0` and `p` gives `‖D t k‖ ≤ C₀·[k = 0] + C_p·‖k‖⁻ᵖ` on the window
(`Summable.le_tsum`, `one_le_norm_freq`).  The slab lemma consumes this at
order `m - i + 4`. -/
theorem exists_mode_majorant_of_windowBound' {D : ℝ → (Fin 3 → ℤ) → ℂ} {b C₀ Cp : ℝ} (p : ℕ)
    (h0 : ∀ t ∈ Icc (0:ℝ) b, (Summable fun l => ‖D t l‖) ∧ (∑' l, ‖D t l‖) ≤ C₀)
    (hp : ∀ t ∈ Icc (0:ℝ) b, (Summable fun l => ‖freq l‖ ^ p * ‖D t l‖) ∧
      (∑' l, ‖freq l‖ ^ p * ‖D t l‖) ≤ Cp) :
    ∀ t ∈ Icc (0:ℝ) b, ∀ k : Fin 3 → ℤ,
      ‖D t k‖ ≤ if k = 0 then C₀ else Cp * (‖freq k‖ ^ p)⁻¹ := by
  intro t ht k
  split_ifs with hk
  · subst hk
    exact ((h0 t ht).1.le_tsum 0 fun j _ => norm_nonneg _).trans (h0 t ht).2
  · have hpos : (0:ℝ) < ‖freq k‖ ^ p := by
      have := one_le_norm_freq hk
      positivity
    have hterm : ‖freq k‖ ^ p * ‖D t k‖ ≤ Cp :=
      ((hp t ht).1.le_tsum k fun j _ => by positivity).trans (hp t ht).2
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖D t k‖ * ‖freq k‖ ^ p = ‖freq k‖ ^ p * ‖D t k‖ := mul_comm _ _
      _ ≤ Cp := hterm

/-- **The per-mode majorant at order `4`** (the instance `p := 4` of
`exists_mode_majorant_of_windowBound'`). -/
theorem exists_mode_majorant_of_windowBound {D : ℝ → (Fin 3 → ℤ) → ℂ} {b C₀ C₄ : ℝ}
    (h0 : ∀ t ∈ Icc (0:ℝ) b, (Summable fun l => ‖D t l‖) ∧ (∑' l, ‖D t l‖) ≤ C₀)
    (h4 : ∀ t ∈ Icc (0:ℝ) b, (Summable fun l => ‖freq l‖ ^ 4 * ‖D t l‖) ∧
      (∑' l, ‖freq l‖ ^ 4 * ‖D t l‖) ≤ C₄) :
    ∀ t ∈ Icc (0:ℝ) b, ∀ k : Fin 3 → ℤ,
      ‖D t k‖ ≤ if k = 0 then C₀ else C₄ * (‖freq k‖ ^ 4)⁻¹ :=
  exists_mode_majorant_of_windowBound' 4 h0 h4

/-! ## 6. The character and the two factors of a lift term on the slab

The character `x ↦ ∏ᵢ cexp(2πI kᵢxᵢ)` is `cexp(2πI⟨freq k, ·⟩)`, so its `q`-th
Fréchet derivative is bounded by `(2π‖freq k‖)^q` (clones of PeriodicLift's
private term lemmas, at the bare character). -/

private lemma char_eq_comp (k : Fin 3 → ℤ) :
    (fun x : EuclideanSpace ℝ (Fin 3) =>
        ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)))
      = (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
          (innerSL ℝ (freq k)) := by
  funext x
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

private lemma hasDerivAt_cexp_mul_real' (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (a * s)) (a * Complex.exp (a * t)) t := by
  have hin : HasDerivAt (fun w : ℂ => a * w) a (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul a
  have h := (Complex.hasDerivAt_exp (a * (t : ℂ))).comp (t : ℂ) hin
  simpa [mul_comm] using h.comp_ofReal

private lemma iteratedDeriv_cexp_mul_real' (a : ℂ) (q : ℕ) :
    iteratedDeriv q (fun s : ℝ => Complex.exp (a * s)) =
      fun t : ℝ => a ^ q * Complex.exp (a * t) := by
  induction q with
  | zero => funext t; simp
  | succ q ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have h := ((hasDerivAt_cexp_mul_real' a t).const_mul (a ^ q)).deriv
      rw [h]
      ring

private lemma contDiff_cexp_mul_real' (a : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => Complex.exp (a * t) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => (t : ℂ) := Complex.ofRealCLM.contDiff
  have hlin : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => a * (t : ℂ) :=
    (contDiff_const (c := a)).mul h
  exact Complex.contDiff_exp.comp hlin

/-- The character is `C^∞` on ℝ³. -/
theorem contDiff_char (k : Fin 3 → ℤ) :
    ContDiff ℝ ∞ fun x : EuclideanSpace ℝ (Fin 3) =>
      ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ)) := by
  rw [char_eq_comp]
  exact (contDiff_cexp_mul_real' _).comp (innerSL ℝ (freq k)).contDiff

/-- The factorial-free derivative bound of the character:
`‖D^q char‖ ≤ (2π‖freq k‖)^q` (clone of PeriodicLift's `norm_iteratedFDeriv_term_le`
at the bare character). -/
theorem norm_iteratedFDeriv_char_le (k : Fin 3 → ℤ) (q : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ q
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))) x‖
      ≤ (2 * Real.pi * ‖freq k‖) ^ q := by
  have hgsm : ContDiff ℝ (⊤ : ℕ∞)
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) :=
    contDiff_cexp_mul_real' (2 * Real.pi * Complex.I)
  have hstep : iteratedFDeriv ℝ q
      (((fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) ∘
        (innerSL ℝ (freq k)))) x
      = (iteratedFDeriv ℝ q
          (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
          ((innerSL ℝ (freq k)) x)).compContinuousLinearMap
            fun _ : Fin q => innerSL ℝ (freq k) :=
    (innerSL ℝ (freq k)).iteratedFDeriv_comp_right hgsm x (by exact_mod_cast le_top)
  rw [char_eq_comp, hstep]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1d : ‖iteratedFDeriv ℝ q
      (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
      ((innerSL ℝ (freq k)) x)‖ = (2 * Real.pi) ^ q := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hv : iteratedDeriv q
        (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)))
        ((innerSL ℝ (freq k)) x)
        = (2 * Real.pi * Complex.I) ^ q *
          Complex.exp ((2 * Real.pi * Complex.I) * (((innerSL ℝ (freq k)) x : ℝ) : ℂ)) :=
      congrFun (iteratedDeriv_cexp_mul_real' (2 * Real.pi * Complex.I) q) _
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
  rw [h1d, hprod, ← mul_pow]

/-- **The time factor on the slab**: the iterated within-derivative of
`q ↦ a q.2` on `univ ×ˢ Ico 0 b` is bounded by the iterated within-derivative
of `a` on `Ico 0 b` (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`
along `snd`, whose preimage of the window is the slab, and `‖snd‖ ≤ 1`). -/
theorem norm_iteratedFDerivWithin_comp_snd_le {a : ℝ → ℂ} {b : ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ico (0:ℝ) b)) (m : ℕ)
    {q : EuclideanSpace ℝ (Fin 3) × ℝ}
    (hq : q ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :
    ‖iteratedFDerivWithin ℝ m (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => a q.2)
        ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) q‖
      ≤ ‖iteratedDerivWithin m a (Ico (0:ℝ) b) q.2‖ := by
  set L := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 3)) ℝ with hL
  have hpre : (L ⁻¹' Ico (0:ℝ) b) = (univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b := by
    ext q; simp [hL]
  have hU : UniqueDiffOn ℝ (L ⁻¹' Ico (0:ℝ) b) := by
    rw [hpre]; exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 b)
  have hqL : L q ∈ Ico (0:ℝ) b := hq.2
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right L ha (uniqueDiffOn_Ico 0 b) hU
    hqL (i := m) (by exact_mod_cast le_top)
  have hfun : (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => a q.2) = a ∘ L := rfl
  rw [hfun, ← hpre, hcomp, ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hsnd : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact norm_snd_le x
  have hprod : (∏ _i : Fin m, ‖L‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hsnd)
  calc ‖iteratedFDerivWithin ℝ m a (Ico (0:ℝ) b) (L q)‖ * ∏ _i : Fin m, ‖L‖
      ≤ ‖iteratedFDerivWithin ℝ m a (Ico (0:ℝ) b) (L q)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDerivWithin ℝ m a (Ico (0:ℝ) b) q.2‖ := by rw [mul_one]; rfl

/-- **The character factor on the slab**: the character composed with `fst`
is `C^∞` on the whole product, so on the slab (unique differentials) its
within-derivative is the full one (`iteratedFDerivWithin_eq_iteratedFDeriv`),
transported along `fst` (`ContinuousLinearMap.iteratedFDeriv_comp_right`,
`‖fst‖ ≤ 1`) and bounded by `norm_iteratedFDeriv_char_le`. -/
theorem norm_iteratedFDerivWithin_char_fst_le (k : Fin 3 → ℤ) {b : ℝ} (j : ℕ)
    {q : EuclideanSpace ℝ (Fin 3) × ℝ}
    (hq : q ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :
    ‖iteratedFDerivWithin ℝ j
        (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
          ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
        ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) q‖
      ≤ (2 * Real.pi * ‖freq k‖) ^ j := by
  set L := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 3)) ℝ with hL
  have hfun : (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
      = (fun x : EuclideanSpace ℝ (Fin 3) =>
          ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))) ∘ L := rfl
  have hsm : ContDiff ℝ ∞ ((fun x : EuclideanSpace ℝ (Fin 3) =>
      ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))) ∘ L) :=
    (contDiff_char k).comp L.contDiff
  rw [hfun, iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 b))
    ((hsm.of_le (by exact_mod_cast le_top)).contDiffAt) hq,
    L.iteratedFDeriv_comp_right (contDiff_char k) q (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hfst : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact norm_fst_le x
  have hprod : (∏ _i : Fin j, ‖L‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hfst)
  calc ‖iteratedFDeriv ℝ j (fun x : EuclideanSpace ℝ (Fin 3) =>
          ∏ i : Fin 3, fourier (k i) ((x i : ℝ) : AddCircle (1 : ℝ))) (L q)‖ * ∏ _i : Fin j, ‖L‖
      ≤ (2 * Real.pi * ‖freq k‖) ^ j * 1 :=
        mul_le_mul (norm_iteratedFDeriv_char_le k j (L q)) hprod
          (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = (2 * Real.pi * ‖freq k‖) ^ j := mul_one _

/-- **The mixed-order bound on one lift term on the slab**: the Leibniz rule
`norm_iteratedFDerivWithin_smul_le` for `(a ∘ snd) • (char ∘ fst)`, the time
factor by `norm_iteratedFDerivWithin_comp_snd_le` and `hA`, the character
factor by `norm_iteratedFDerivWithin_char_fst_le`. -/
theorem norm_iteratedFDerivWithin_liftTerm_le (k : Fin 3 → ℤ) {a : ℝ → ℂ} {b : ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ico (0:ℝ) b)) {A : ℕ → ℝ}
    (hA : ∀ n : ℕ, ∀ t ∈ Ico (0:ℝ) b, ‖iteratedDerivWithin n a (Ico (0:ℝ) b) t‖ ≤ A n)
    (m : ℕ) {q : EuclideanSpace ℝ (Fin 3) × ℝ} (hq : q ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :
    ‖iteratedFDerivWithin ℝ m
        (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
          a q.2 • ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
        ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) q‖
      ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * A i * (2 * Real.pi * ‖freq k‖) ^ (m - i) := by
  have hU : UniqueDiffOn ℝ ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 b)
  have hf : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => a q.2)
      ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :=
    ha.comp contDiff_snd.contDiffOn fun q hq => hq.2
  have hg : ContDiffOn ℝ ∞ (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
      ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
      ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :=
    ((contDiff_char k).comp contDiff_fst).contDiffOn
  refine (norm_iteratedFDerivWithin_smul_le hf hg hU hq (n := m)
    (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := (norm_iteratedFDerivWithin_comp_snd_le ha i hq).trans (hA i q.2 hq.2)
  have h2 := norm_iteratedFDerivWithin_char_fst_le k (b := b) (m - i) hq
  have hAnn : 0 ≤ A i := (norm_nonneg _).trans h1
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hAnn)

/-! ## 7. The slab: localisation, gluing, and the M-test -/

/-- The window slab is the closed slab cut by an open half-space. -/
theorem slab_inter (b : ℝ) :
    ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ)) ∩ (univ ×ˢ Iio b)
      = (univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b := by
  rw [Set.prod_inter_prod, Set.univ_inter, Set.Ici_inter_Iio]

/-- The window slab is convex. -/
theorem slab_convex (b : ℝ) :
    Convex ℝ ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :=
  convex_univ.prod (convex_Ico 0 b)

/-- The window slab has unique differentials. -/
theorem slab_uniqueDiff (b : ℝ) :
    UniqueDiffOn ℝ ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b) :=
  uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 b)

/-- **Gluing**: `C^∞` on every window slab gives `C^∞` on the closed slab
(`contDiffOn_of_locally_contDiffOn` with the open half-space `Iio (t + 1)`). -/
theorem slab_glue {f : EuclideanSpace ℝ (Fin 3) × ℝ → ℂ}
    (h : ∀ b : ℝ, ContDiffOn ℝ ∞ f ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ico (0:ℝ) b)) :
    ContDiffOn ℝ ∞ f ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ)) := by
  refine contDiffOn_of_locally_contDiffOn fun q _ => ?_
  refine ⟨univ ×ˢ Iio (q.2 + 1), isOpen_univ.prod isOpen_Iio,
    ⟨mem_univ _, Set.mem_Iio.mpr (lt_add_one _)⟩, ?_⟩
  rw [slab_inter]
  exact h (q.2 + 1)

/-- The codomain-generic form of `contDiffOn_infty_Ici_of_chain`: a derivative
chain on `Ioi 0` with right derivatives at `0` and continuity on `Ici 0` is
`C^∞` on `Ici 0`. -/
theorem contDiffOn_infty_Ici_of_chain' {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℕ → ℝ → F}
    (hchain : ∀ i, ∀ t ∈ Ioi (0:ℝ), HasDerivAt (g i) (g (i + 1) t) t)
    (hzero : ∀ i, HasDerivWithinAt (g i) (g (i + 1) 0) (Ici (0:ℝ)) 0)
    (hcont : ∀ i, ContinuousOn (g i) (Ici (0:ℝ))) :
    ContDiffOn ℝ ∞ (g 0) (Ici (0:ℝ)) := by
  have hdw : ∀ i, ∀ t ∈ Ici (0:ℝ), HasDerivWithinAt (g i) (g (i + 1) t) (Ici (0:ℝ)) t := by
    intro i t ht
    rcases eq_or_lt_of_le (mem_Ici.mp ht) with h | h
    · subst h; exact hzero i
    · exact (hchain i t h).hasDerivWithinAt
  have hderiv : ∀ i, ∀ t ∈ Ici (0:ℝ), derivWithin (g i) (Ici (0:ℝ)) t = g (i + 1) t :=
    fun i t ht => (hdw i t ht).derivWithin (uniqueDiffOn_Ici 0 t ht)
  have key : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (g i) (Ici (0:ℝ)) := by
    intro n
    induction n with
    | zero => intro i; exact contDiffOn_zero.mpr (hcont i)
    | succ n ih =>
      intro i
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
      refine ⟨fun t ht => (hdw i t ht).differentiableWithinAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · exact (ih (i + 1)).congr (hderiv i)
  exact contDiffOn_infty.mpr fun n => key n 0

/-- A ℂ-valued derivative chain is `C^∞` on every window `Ico 0 b`. -/
theorem contDiffOn_Ico_of_chain {g : ℕ → ℝ → ℂ} {b : ℝ}
    (hchain : ∀ i, ∀ t ∈ Ioi (0:ℝ), HasDerivAt (g i) (g (i + 1) t) t)
    (hzero : ∀ i, HasDerivWithinAt (g i) (g (i + 1) 0) (Ici (0:ℝ)) 0)
    (hcont : ∀ i, ContinuousOn (g i) (Ici (0:ℝ))) :
    ContDiffOn ℝ ∞ (g 0) (Ico (0:ℝ) b) :=
  (contDiffOn_infty_Ici_of_chain' hchain hzero hcont).mono Ico_subset_Ici_self

/-- The lattice majorant shape `x·[k = 0] + y·‖k‖⁻⁴` is summable
(`summable_inv_freq_pow_four`; the zero mode carries `‖freq 0‖ = 0`). -/
theorem summable_ite_zero_add_inv_pow_four (x y : ℝ) :
    Summable fun k : Fin 3 → ℤ => if k = 0 then x else y * (‖freq k‖ ^ 4)⁻¹ := by
  have h := ((hasSum_ite_eq (0 : Fin 3 → ℤ) x).summable).add
    (summable_inv_freq_pow_four.mul_left y)
  refine h.congr fun k => ?_
  by_cases hk : k = 0
  · subst hk; simp [freq_zero_eq'']
  · simp [hk]

/-- **Joint `C^∞` of a lift on the closed slab** from a coefficient chain with
window bounds at every order: on every window slab `univ ×ˢ Ico 0 b` the
M-test `contDiffOn_tsum_of_convex` at `N = ⊤` with the majorant
`v m k = Σ_{i ≤ m} C(m,i)·A_{m,i}(k)·(2π‖freq k‖)^(m-i)`, where `A_{m,i}` is the
per-mode majorant of the `i`-th time derivative at window order `m - i + 4`
(`exists_mode_majorant_of_windowBound'` fed by `hbound`, identified with the
iterated within-derivative by `iteratedDerivWithin_eq_chain`), each term
`C^∞` on the slab and bounded by `norm_iteratedFDerivWithin_liftTerm_le`, the
`k`-sum of the majorant converging by `summable_ite_zero_add_inv_pow_four`;
then `slab_glue`. -/
theorem contDiffOn_lift_slab {a : ℝ → (Fin 3 → ℤ) → ℂ} {D : ℕ → ℝ → (Fin 3 → ℤ) → ℂ}
    (hD0 : D 0 = a)
    (hchain : ∀ n, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => D n s k) (D (n + 1) t k) t)
    (hzero : ∀ n k, HasDerivWithinAt (fun s => D n s k) (D (n + 1) 0 k) (Ici (0:ℝ)) 0)
    (hcont : ∀ n k, ContinuousOn (fun s => D n s k) (Ici (0:ℝ)))
    (hbound : ∀ (n p : ℕ) (b : ℝ), ∃ C : ℝ, ∀ t ∈ Icc (0:ℝ) b,
      (Summable fun l => ‖freq l‖ ^ p * ‖D n t l‖) ∧
      (∑' l, ‖freq l‖ ^ p * ‖D n t l‖) ≤ C) :
    ContDiffOn ℝ ∞
      (fun q : EuclideanSpace ℝ (Fin 3) × ℝ =>
        ∑' k : Fin 3 → ℤ, a q.2 k • ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
      ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ)) := by
  choose C hC using hbound
  have hD0' : ∀ k, (fun t => D 0 t k) = fun t => a t k := fun k => by
    funext t; exact congrFun (congrFun hD0 t) k
  -- each mode is `C^∞` in time on every window
  have hmode : ∀ (b : ℝ) (k : Fin 3 → ℤ), ContDiffOn ℝ ∞ (fun t => a t k) (Ico (0:ℝ) b) := by
    intro b k
    have h := contDiffOn_Ico_of_chain (g := fun n t => D n t k) (b := b)
      (fun n t ht => hchain n t ht k) (fun n => hzero n k) (fun n => hcont n k)
    rw [hD0' k] at h
    exact h
  refine slab_glue fun b => ?_
  -- the per-mode majorant of the `n`-th time derivative at window order `m - n + 4`
  set Amaj : ℕ → ℕ → (Fin 3 → ℤ) → ℝ := fun m n k =>
    if k = 0 then C n 0 b else C n (m - n + 4) b * (‖freq k‖ ^ (m - n + 4))⁻¹ with hAmaj
  have hA : ∀ (m : ℕ) (k : Fin 3 → ℤ) (n : ℕ), ∀ t ∈ Ico (0:ℝ) b,
      ‖iteratedDerivWithin n (fun t => a t k) (Ico (0:ℝ) b) t‖ ≤ Amaj m n k := by
    intro m k n t ht
    rw [iteratedDerivWithin_eq_chain (D := fun n t => D n t k) (hD0' k)
      (fun n t ht => hchain n t ht k) (fun n => hzero n k) n t ht]
    exact exists_mode_majorant_of_windowBound' (m - n + 4)
      (fun t ht => by simpa using hC n 0 b t ht) (hC n (m - n + 4) b) t
      (Ico_subset_Icc_self ht) k
  refine contDiffOn_tsum_of_convex (slab_convex b) (slab_uniqueDiff b) (N := ⊤)
    (f := fun k (q : EuclideanSpace ℝ (Fin 3) × ℝ) =>
      a q.2 k • ∏ i : Fin 3, fourier (k i) ((q.1 i : ℝ) : AddCircle (1 : ℝ)))
    (v := fun m k => ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) * Amaj m i k * (2 * Real.pi * ‖freq k‖) ^ (m - i))
    (fun k => ?_) (fun m _ => ?_)
    (fun m k q hq _ => norm_iteratedFDerivWithin_liftTerm_le k (hmode b k) (hA m k) m hq)
  · -- every term is `C^∞` on the window slab
    exact ((hmode b k).comp contDiff_snd.contDiffOn fun q hq => hq.2).smul
      ((contDiff_char k).comp contDiff_fst).contDiffOn
  · -- the majorant is summable at every order
    refine summable_sum fun i _ => ?_
    have heq : (fun k : Fin 3 → ℤ =>
        (m.choose i : ℝ) * Amaj m i k * (2 * Real.pi * ‖freq k‖) ^ (m - i))
        = fun k => if k = 0
            then (m.choose i : ℝ) * C i 0 b * (2 * Real.pi * ‖freq 0‖) ^ (m - i)
            else ((m.choose i : ℝ) * C i (m - i + 4) b * (2 * Real.pi) ^ (m - i))
              * (‖freq k‖ ^ 4)⁻¹ := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp [hAmaj]
      · simp only [hAmaj, if_neg hk]
        have hne : ‖freq k‖ ≠ 0 := (lt_of_lt_of_le one_pos (one_le_norm_freq hk)).ne'
        rw [mul_pow, pow_add]
        field_simp
        try ring
    rw [heq]
    exact summable_ite_zero_add_inv_pow_four _ _

/-! ## 8. The capstone -/

/-- **The endpoint tool** on a `Vel`-valued function: derivatives on `Ioi 0`
whose values extend continuously to `Ici 0`, and continuity of the function
itself on `Ici 0`, give the right derivative at `0` within `Ici 0`
(`hasDerivWithinAt_Ici_of_tendsto_deriv`). -/
theorem hasDerivWithinAt_Ici_zero_of_deriv {f g : ℝ → Vel}
    (hder : ∀ t ∈ Ioi (0:ℝ), HasDerivAt f (g t) t)
    (hf : ContinuousOn f (Ici (0:ℝ))) (hg : ContinuousOn g (Ici (0:ℝ))) :
    HasDerivWithinAt f (g 0) (Ici (0:ℝ)) 0 := by
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
  · intro t ht
    exact (hder t ht).differentiableAt.differentiableWithinAt
  · exact (hf 0 self_mem_Ici).mono Ioi_subset_Ici_self
  · have hlim : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      (hg 0 self_mem_Ici).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    refine hlim.congr' ?_
    exact eventually_nhdsWithin_of_forall fun t ht => ((hder t ht).deriv).symm

/-- A window bound transfers along a pointwise norm bound (`‖E t l‖ ≤ ‖F t l‖`)
from a `Vel`-valued window-class member to a ℂ-valued family. -/
theorem windowBound_of_norm_le {F : ℝ → (Fin 3 → ℤ) → Vel} {E : ℝ → (Fin 3 → ℤ) → ℂ}
    (hle : ∀ t l, ‖E t l‖ ≤ ‖F t l‖) {b : ℝ} (hF : WindowL1 0 b F) (p : ℕ) :
    ∃ C : ℝ, ∀ t ∈ Icc (0:ℝ) b,
      (Summable fun l => ‖freq l‖ ^ p * ‖E t l‖) ∧
      (∑' l, ‖freq l‖ ^ p * ‖E t l‖) ≤ C := by
  obtain ⟨C, hC⟩ := hF p
  refine ⟨C, fun t ht => ?_⟩
  have hpt : ∀ l, ‖freq l‖ ^ p * ‖E t l‖ ≤ ‖freq l‖ ^ p * ‖F t l‖ := fun l =>
    mul_le_mul_of_nonneg_left (hle t l) (by positivity)
  have hs : Summable fun l => ‖freq l‖ ^ p * ‖E t l‖ :=
    (hC t ht).1.of_nonneg_of_le (fun _ => by positivity) hpt
  exact ⟨hs, (hs.tsum_le_tsum hpt (hC t ht).1).trans (hC t ht).2⟩

/-- **Joint smoothness of the eternal flow on the closed slab.**  Clauses 1-22
are those of `theorem_B_time_smooth`, re-exported verbatim; clause 23 is every
weighted ℓ¹ order of the pressure (`summable_freq_pow_pressureCoeff` on
clause 10); clause 24 is joint `C^∞` in `(x, t)` of every component's velocity
lift on the CLOSED slab `univ ×ˢ Ici 0` (`contDiffOn_lift_slab` at the
component chain of clause 21, whose windows are the windows of `D n` through
`‖v j‖ ≤ ‖v‖`); clause 25 is joint `C^∞` of the pressure lift on the closed
slab (`contDiffOn_lift_slab` at the pressure chain `pressureFun (S n · k) k`,
whose base is `pressureCoeff` by `convBil_self` at the order-`0` Leibniz sum,
whose derivatives on `Ioi 0` are the exported `S`-derivatives through the
functional, whose endpoint derivative at `0` is the endpoint tool on `S n`,
and whose windows are the windows of `S n` through `norm_pressureFun_le`).
`∞` is `(⊤ : ℕ∞)`, not `ω`: no analyticity is claimed.

`κ` is that of `theorem_B_time_smooth`, of explicit form and exported as a
compiled existential; the window constants of the chain and the majorants
of the slab lemma are untracked existentials. -/
theorem theorem_B_joint_smooth :
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
        (∀ (m : ℕ), ∀ t ∈ Ici (0:ℝ),
          Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        (∀ t ∈ Ici (0:ℝ), c t 0 = 0) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ p : ℕ, Summable fun l => ‖freq l‖ ^ p * ‖c t l‖) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (p : ℕ),
          ContDiff ℝ (p : ℕ∞) (uLift j (c t))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (g : Fin 3 → ℤ)
            (x : EuclideanSpace ℝ (Fin 3)),
          uLift j (c t) (x + freq g) = uLift j (c t) x) ∧
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
          HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
            (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c t k
              + lerayProj k (convFull (c t) k)) j * mFourier k x) t) ∧
        (∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          ContinuousOn (fun s => ∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c s k
            + lerayProj k (convFull (c s) k)) j * mFourier k x) (Ioi (0:ℝ))) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (i j : Fin 3) (y : UnitAddTorus (Fin 2)) (s : ℝ),
          HasDerivAt
            (fun r : ℝ => ∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) * c t k j) •
              mFourier k (i.insertNth (↑r : UnitAddCircle) y))
            (∑' k, ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) •
              mFourier k (i.insertNth (↑s : UnitAddCircle) y)) s) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (z : UnitAddTorus (Fin 3)),
          (∑' k, (((-(ν * ‖freq k‖ ^ 2) : ℝ) : ℂ) * c t k j) • mFourier k z)
            = ((ν / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
              (∑ i : Fin 3, ∑' k,
                ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 * c t k j) • mFourier k z)) ∧
        (∀ t ∈ Ici (0:ℝ), (Summable fun k => ‖pressureCoeff (c t) k‖) ∧
          Summable fun k => ‖freq k‖ * ‖pressureCoeff (c t) k‖) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (k : Fin 3 → ℤ) (j : Fin 3),
          (lerayProj k (convFull (c t) k)) j
            = convFull (c t) k j
              - (2 * Real.pi * Complex.I * ((k j : ℤ) : ℂ)) * pressureCoeff (c t) k) ∧
        (∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)),
          (∑ i : Fin 3, (∑' l, c t l i * mFourier l x) *
              (∑' m, (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)) * c t m j
                * mFourier m x))
            = ((-(2 * Real.pi) : ℝ) : ℂ) * ∑' k, convFull (c t) k j * mFourier k x) ∧
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
                  * mFourier k x) t) ∧
        -- 21. THE TIME-DERIVATIVE CHAIN, with the Leibniz convection sum `S`
        -- exported alongside `D` (critic-required, so the pressure chain of W2
        -- does not re-derive the antidiagonal bookkeeping).  `S` is pinned to
        -- `D` by its defining clause; `D` is pinned to `c` by `D 0 = c` and the
        -- derivative clauses (`chain_unique`, compiled).
        (∃ D S : ℕ → ℝ → (Fin 3 → ℤ) → Vel,
          D 0 = c ∧
          (∀ (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ),
            S n t k = ∑ ij ∈ Finset.antidiagonal n,
              n.choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k) ∧
          (∀ n : ℕ, ∀ t ∈ Ici (0:ℝ), ∀ k,
            D (n + 1) t k = (-(ν * ‖freq k‖ ^ 2)) • D n t k + lerayProj k (S n t k)) ∧
          (∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
            HasDerivAt (fun s => D n s k) (D (n + 1) t k) t) ∧
          (∀ n : ℕ, ∀ k,
            HasDerivWithinAt (fun s => D n s k) (D (n + 1) 0 k) (Ici (0:ℝ)) 0) ∧
          (∀ n : ℕ, ∀ k, ContinuousOn (fun s => D n s k) (Ici (0:ℝ))) ∧
          (∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (D n)) ∧
          (∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
            HasDerivAt (fun s => S n s k) (S (n + 1) t k) t) ∧
          (∀ n : ℕ, ∀ k, ContinuousOn (fun s => S n s k) (Ici (0:ℝ))) ∧
          (∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (S n))) ∧
        -- 22. every mode is C^∞ in time on `Ici 0`
        (∀ k, ContDiffOn ℝ ∞ (fun s => c s k) (Ici (0:ℝ))) ∧
        -- 23. the pressure has every weighted ℓ¹ order
        (∀ t ∈ Ici (0:ℝ), ∀ p : ℕ,
          Summable fun k => ‖freq k‖ ^ p * ‖pressureCoeff (c t) k‖) ∧
        -- 24. JOINT C^∞ of the velocity lift on the closed slab
        (∀ j : Fin 3, ContDiffOn ℝ ∞
          (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => uLift j (c q.2) q.1)
          ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ))) ∧
        -- 25. JOINT C^∞ of the pressure lift on the closed slab
        ContDiffOn ℝ ∞
          (fun q : EuclideanSpace ℝ (Fin 3) × ℝ => pLift (c q.2) q.1)
          ((univ : Set (EuclideanSpace ℝ (Fin 3))) ×ˢ Ici (0:ℝ))
 := by
  obtain ⟨κ, hκ, H⟩ := theorem_B_time_smooth
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hall hmean0 hreal hdiv hsmall
  obtain ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, hclassical,
    hchain21, hCinf⟩ := H hν hall hmean0 hreal hdiv hsmall
  obtain ⟨D, S, hD0, hSdef, hDrec, hDder, hDzero, hDcont, hDwin, hSder, hScont, hSwin⟩ :=
    hchain21
  refine ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, hclassical,
    ⟨D, S, hD0, hSdef, hDrec, hDder, hDzero, hDcont, hDwin, hSder, hScont, hSwin⟩, hCinf,
    ?_, ?_, ?_⟩
  · -- 23. every weighted ℓ¹ order of the pressure
    intro t ht p
    exact summable_freq_pow_pressureCoeff (hl1 t ht) p
  · -- 24. joint C^∞ of the velocity lift, component by component
    intro j
    have h := contDiffOn_lift_slab (a := fun t k => c t k j) (D := fun n t k => D n t k j)
      (by funext t k; show D 0 t k j = c t k j; rw [hD0])
      (fun n t ht k => ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        t (hDder n t ht k))
      (fun n k => ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
        0 (hDzero n k))
      (fun n k => ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).continuous.comp_continuousOn
        (hDcont n k))
      (fun n p b => windowBound_of_norm_le (fun t l => PiLp.norm_apply_le _ _) (hDwin n b) p)
    exact h
  · -- 25. joint C^∞ of the pressure lift, through the pressure chain
    have hP0 : (fun n t k => pressureFun (S n t k) k) 0 = fun t k => pressureCoeff (c t) k := by
      funext t k
      have h := hSdef 0 t k
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Nat.choose_self, one_smul,
        hD0, convBil_self] at h
      show pressureFun (S 0 t k) k = pressureFun (convFull (c t) k) k
      rw [h]
    have hSzero : ∀ n k, HasDerivWithinAt (fun s => S n s k) (S (n + 1) 0 k) (Ici (0:ℝ)) 0 :=
      fun n k => hasDerivWithinAt_Ici_zero_of_deriv (fun t ht => hSder n t ht k) (hScont n k)
        (hScont (n + 1) k)
    have h := contDiffOn_lift_slab (a := fun t k => pressureCoeff (c t) k)
      (D := fun n t k => pressureFun (S n t k) k) hP0
      (fun n t ht k => HasDerivAt.pressureFun k (hSder n t ht k))
      (fun n k => HasDerivWithinAt.pressureFun k (hSzero n k))
      (fun n k => (continuous_pressureFun k).comp_continuousOn (hScont n k))
      (fun n p b => windowBound_of_norm_le (fun t l => norm_pressureFun_le _ _) (hSwin n b) p)
    exact h

end TheoremB
