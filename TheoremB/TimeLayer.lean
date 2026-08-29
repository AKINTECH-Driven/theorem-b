/-
# The time layer engine (Tier 6, wave W5c)

Abstract spectral-side engine lemmas for the classical layer's time
direction — COMPLETE:

1. `quarticKernel` — the lattice weight `Σ' k, (‖freq k‖⁴)⁻¹`, certified
   summable by `summable_inv_freq_pow_four`.
2. `tsum_weighted_norm_le` — the QUANTITATIVE weighted ℓ¹ bound (the
   uniform-in-time workhorse; `summable_weighted_norm` in SobolevNorms is
   its qualitative twin): `Σ ‖k‖^p ‖c k‖ ≤ (quarticKernel + Σ ‖k‖^(2(p+2)) ‖c k‖²)/2`
   by AM-GM against `(‖k‖⁴)⁻¹` — with the window form
   `tsum_weighted_norm_le_of_bound` that turns the per-time `sob` bounds
   of `ns_full_global_flow_sobolev` into t-uniform ℓ¹ majorants.
3. `summable_convMaj_l1` — discrete Young on ℤ³ (`ℓ¹ ∗ ℓ¹ ⊆ ℓ¹`): the
   convection majorant's `k`-marginals are summable with total mass at
   most the product of the two ℓ¹ masses (the shear `shearEquiv`
   decouples the indices; `HasSum.prod_fiberwise` gives marginal
   summability and value at once).  Corollary `summable_norm_convFull`.
4. `hasDerivAt_weighted_tsum_flow` — term-wise time differentiation of
   `t ↦ Σ' k, c t k j · w k` against any weight family of modulus ≤ 1,
   via `hasDerivAt_tsum_of_isPreconnected` on open intervals; and
   `continuousOn_weighted_tsum` for the continuity of the derivative sum.
5. `weighted_convMaj_le` — the convection envelope DECAYS like `‖k‖^{-p}`
   (W1's half-weight split `norm_freq_pow_split` again; a bare
   Cauchy-Schwarz bound is constant in `k`, hence useless as a majorant);
   `norm_mode_le_of_sob` — per-mode decay `‖c k‖ ≤ √B/‖k‖^m` from a
   level-`m` Sobolev-mass bound, the bridge from the campaign's
   tsum-level bounds to per-mode estimates; `norm_nsRHS_le` — the
   pointwise Navier-Stokes right-hand-side bound; and the capstone-facing
   `exists_summable_nsRHS_maj`, which assembles them into a SUMMABLE
   time-uniform majorant `(νB + 32B²)·(‖k‖⁴)⁻¹` from order-six weighted
   ℓ¹ window bounds — exactly the hypothesis items 4 need.

Junk-tsum discipline: every tsum statement carries its Summable
certificate as a hypothesis or exports it; `quarticKernel`'s defining
tsum is certified by `summable_inv_freq_pow_four`.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.SobolevNorms

namespace TheoremB

open Set

/-! ## The quartic lattice kernel -/

/-- The quartic lattice kernel `Σ' k, (‖freq k‖⁴)⁻¹` (the `k = 0` term is
`0⁻¹ = 0`).  Summability certificate: `summable_inv_freq_pow_four`. -/
noncomputable def quarticKernel : ℝ := ∑' k : Fin 3 → ℤ, (‖freq k‖ ^ 4)⁻¹

lemma quarticKernel_nonneg : 0 ≤ quarticKernel :=
  tsum_nonneg fun k => by positivity

/-! ## 1. The quantitative weighted ℓ¹ bound -/

/-- **The uniform-in-time workhorse.**  Two orders of extra Sobolev
regularity buy a QUANTITATIVE weighted ℓ¹ bound:
`Σ ‖k‖^p ‖c k‖ ≤ (quarticKernel + Σ ‖k‖^(2(p+2)) ‖c k‖²)/2`
(mean-zero fields; AM-GM against the lattice weight `(‖k‖⁴)⁻¹`, exactly the
`summable_weighted_norm` skeleton with the bound kept). -/
theorem tsum_weighted_norm_le {p : ℕ} {c : (Fin 3 → ℤ) → Vel} (hc0 : c 0 = 0)
    (h : Summable fun k => ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) :
    (∑' k, ‖freq k‖ ^ p * ‖c k‖) ≤
      (quarticKernel + ∑' k, ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
  have hL : Summable fun k => ‖freq k‖ ^ p * ‖c k‖ := summable_weighted_norm hc0 h
  have hpt : ∀ k, ‖freq k‖ ^ p * ‖c k‖ ≤
      ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [hc0, norm_zero, mul_zero]
      positivity
    · have hw : (0 : ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
      have key : ‖freq k‖ ^ p * ‖c k‖ =
          (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ (p + 2) * ‖c k‖) := by
        rw [pow_add]
        field_simp
      have e1 : ((‖freq k‖ ^ 2)⁻¹) ^ 2 = (‖freq k‖ ^ 4)⁻¹ := by
        rw [inv_pow, ← pow_mul]
      have e2 := sq_norm_pow_mul k ‖c k‖ (p + 2)
      calc ‖freq k‖ ^ p * ‖c k‖
          = (‖freq k‖ ^ 2)⁻¹ * (‖freq k‖ ^ (p + 2) * ‖c k‖) := key
        _ ≤ (((‖freq k‖ ^ 2)⁻¹) ^ 2 + (‖freq k‖ ^ (p + 2) * ‖c k‖) ^ 2) / 2 := by
            nlinarith [sq_nonneg ((‖freq k‖ ^ 2)⁻¹ - ‖freq k‖ ^ (p + 2) * ‖c k‖)]
        _ = ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
            rw [e1, e2]
  have hR : Summable fun k =>
      ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 :=
    (summable_inv_freq_pow_four.add h).div_const 2
  calc (∑' k, ‖freq k‖ ^ p * ‖c k‖)
      ≤ ∑' k, ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 :=
        hL.tsum_le_tsum hpt hR
    _ = (quarticKernel + ∑' k, ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 := by
        have e3 : ∀ k : Fin 3 → ℤ,
            ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) / 2 =
            ((‖freq k‖ ^ 4)⁻¹ + ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) * (2:ℝ)⁻¹ :=
          fun k => div_eq_mul_inv _ _
        rw [tsum_congr e3, tsum_mul_right,
          summable_inv_freq_pow_four.tsum_add h]
        have hq : (∑' k : Fin 3 → ℤ, (‖freq k‖ ^ 4)⁻¹) = quarticKernel := rfl
        rw [hq, div_eq_mul_inv]

/-- Window form of `tsum_weighted_norm_le`: a bound on the level-`(p+2)`
Sobolev summand bounds the weighted ℓ¹ mass, uniformly. -/
theorem tsum_weighted_norm_le_of_bound {p : ℕ} {c : (Fin 3 → ℤ) → Vel} {B : ℝ}
    (hc0 : c 0 = 0)
    (h : Summable fun k => ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2)
    (hB : (∑' k, ‖freq k‖ ^ (2 * (p + 2)) * ‖c k‖ ^ 2) ≤ B) :
    (∑' k, ‖freq k‖ ^ p * ‖c k‖) ≤ (quarticKernel + B) / 2 :=
  (tsum_weighted_norm_le hc0 h).trans (by linarith)

/-! ## 2. The discrete Young ℓ¹ convolution majorant on ℤ³ -/

/-- The shear `(k, l) ↦ (l, k - l)` on `ℤ³ × ℤ³`: it turns the convolution
index pair into an independent pair, which is what makes `ℓ¹ ∗ ℓ¹ ⊆ ℓ¹`
a product-summability statement. -/
private def shearEquiv :
    ((Fin 3 → ℤ) × (Fin 3 → ℤ)) ≃ ((Fin 3 → ℤ) × (Fin 3 → ℤ)) where
  toFun p := (p.1 + p.2, p.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv := by rintro ⟨l, m⟩; simp
  right_inv := by rintro ⟨k, l⟩; simp

/-- **Discrete Young on ℤ³ (`ℓ¹ ∗ ℓ¹ ⊆ ℓ¹`).**  For an ℓ¹ family with one
weighted ℓ¹ order, the convection majorant's `k`-marginals are summable and
their total mass is at most the product of the two ℓ¹ masses.  (The shear
`shearEquiv` decouples the indices; `HasSum.prod_fiberwise` delivers the
marginal summability and the value simultaneously.) -/
theorem summable_convMaj_l1 {c : (Fin 3 → ℤ) → Vel}
    (h0 : Summable fun k => ‖c k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c k‖) :
    (Summable fun k => ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) ∧
      (∑' k, ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
        ≤ (∑' k, ‖c k‖) * (∑' k, ‖freq k‖ * ‖c k‖) := by
  have hfnn : ∀ l : Fin 3 → ℤ, (0:ℝ) ≤ ‖c l‖ := fun _ => norm_nonneg _
  have hgnn : ∀ m : Fin 3 → ℤ, (0:ℝ) ≤ ‖freq m‖ * ‖c m‖ := fun _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- the decoupled product family on ℤ³ × ℤ³
  have hF : Summable (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      ‖c q.1‖ * (‖freq q.2‖ * ‖c q.2‖)) :=
    h0.mul_of_nonneg h1 hfnn hgnn
  -- its total mass is the product of the two ℓ¹ masses
  have hFtsum : (∑' q : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        ‖c q.1‖ * (‖freq q.2‖ * ‖c q.2‖))
      = (∑' l, ‖c l‖) * (∑' m, ‖freq m‖ * ‖c m‖) := by
    rw [hF.tsum_prod' (fun l => h1.mul_left ‖c l‖)]
    calc (∑' (l : Fin 3 → ℤ) (m : Fin 3 → ℤ), ‖c l‖ * (‖freq m‖ * ‖c m‖))
        = ∑' l : Fin 3 → ℤ, ‖c l‖ * ∑' m, ‖freq m‖ * ‖c m‖ :=
          tsum_congr fun _ => tsum_mul_left
      _ = (∑' l, ‖c l‖) * ∑' m, ‖freq m‖ * ‖c m‖ := tsum_mul_right
  -- pull it back along the shear to the convolution family
  have hcomp : ∀ p : (Fin 3 → ℤ) × (Fin 3 → ℤ),
      (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
          ‖c q.2‖ * (‖freq (q.1 - q.2)‖ * ‖c (q.1 - q.2)‖)) (shearEquiv p)
        = ‖c p.1‖ * (‖freq p.2‖ * ‖c p.2‖) := by
    rintro ⟨l, m⟩
    have hsub : l + m - l = m := by abel
    show ‖c l‖ * (‖freq (l + m - l)‖ * ‖c (l + m - l)‖)
        = ‖c l‖ * (‖freq m‖ * ‖c m‖)
    rw [hsub]
  have hGsum : Summable (fun q : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      ‖c q.2‖ * (‖freq (q.1 - q.2)‖ * ‖c (q.1 - q.2)‖)) := by
    refine (shearEquiv.summable_iff).mp ?_
    exact hF.congr fun p => (hcomp p).symm
  have hGtsum : (∑' q : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        ‖c q.2‖ * (‖freq (q.1 - q.2)‖ * ‖c (q.1 - q.2)‖))
      = (∑' l, ‖c l‖) * ∑' m, ‖freq m‖ * ‖c m‖ := by
    rw [← hFtsum, ← shearEquiv.tsum_eq]
    exact tsum_congr hcomp
  -- fiberwise: the k-marginals sum to the total
  have hmarg : HasSum
      (fun k => ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
      (∑' q : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        ‖c q.2‖ * (‖freq (q.1 - q.2)‖ * ‖c (q.1 - q.2)‖)) :=
    hGsum.hasSum.prod_fiberwise fun k => (hGsum.prod_factor k).hasSum
  refine ⟨hmarg.summable, ?_⟩
  rw [hmarg.tsum_eq, hGtsum]

/-- The full convection is ℓ¹ in the mode index, given ℓ¹ and one weighted
ℓ¹ order (plus the ℓ² certificates `convFull`'s own pointwise bound needs). -/
theorem summable_norm_convFull {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2)
    (h0 : Summable fun k => ‖c k‖)
    (h1 : Summable fun k => ‖freq k‖ * ‖c k‖) :
    Summable fun k => ‖convFull c k‖ :=
  (summable_convMaj_l1 h0 h1).1.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_convFull_le hE hZ k)

/-! ## 3. Term-wise time differentiation of weighted mode sums -/

/-- Component bound: a weight of modulus at most one never increases the
mode norm. -/
private lemma norm_component_mul_le {v : Vel} {z : ℂ} (hz : ‖z‖ ≤ 1) (j : Fin 3) :
    ‖v j * z‖ ≤ ‖v‖ := by
  calc ‖v j * z‖ = ‖v j‖ * ‖z‖ := norm_mul _ _
    _ ≤ ‖v‖ * 1 :=
        mul_le_mul (PiLp.norm_apply_le v j) hz (norm_nonneg _) (norm_nonneg _)
    _ = ‖v‖ := mul_one _

/-- **The time-derivative engine.**  Along any coefficient flow whose modes
satisfy an ODE on an open interval, with a summable time-uniform majorant for
the mode derivatives, the weighted mode sum `t ↦ Σ' k, c t k j · w k` may be
differentiated term by term, for any weight family of modulus at most one
(the Fourier characters are the intended weights).  Via
`hasDerivAt_tsum_of_isPreconnected`: `Ioo a b` is open and preconnected. -/
theorem hasDerivAt_weighted_tsum_flow {c c' : ℝ → (Fin 3 → ℤ) → Vel} {j : Fin 3}
    {w : (Fin 3 → ℤ) → ℂ} (hw : ∀ k, ‖w k‖ ≤ 1) {a b : ℝ}
    (hODE : ∀ t ∈ Ioo a b, ∀ k, HasDerivAt (fun s => c s k) (c' t k) t)
    {u : (Fin 3 → ℤ) → ℝ} (hu : Summable u)
    (hmaj : ∀ t ∈ Ioo a b, ∀ k, ‖c' t k‖ ≤ u k)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hs₀ : Summable fun k => ‖c t₀ k‖) :
    ∀ t ∈ Ioo a b, HasDerivAt (fun s => ∑' k, c s k j * w k)
      (∑' k, c' t k j * w k) t := by
  intro t ht
  have hproj : ∀ (k : Fin 3 → ℤ), ∀ s ∈ Ioo a b,
      HasDerivAt (fun z => c z k j * w k) (c' s k j * w k) s := by
    intro k s hs
    have hp : HasDerivAt (fun z => (c z k) j) ((c' s k) j) s :=
      ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        (hODE s hs k)
    exact hp.mul_const (w k)
  have hbd : ∀ (k : Fin 3 → ℤ), ∀ s ∈ Ioo a b, ‖c' s k j * w k‖ ≤ u k := fun k s hs =>
    (norm_component_mul_le (hw k) j).trans (hmaj s hs k)
  have hsum₀ : Summable fun k => c t₀ k j * w k :=
    Summable.of_norm (hs₀.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => norm_component_mul_le (hw k) j))
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hproj hbd ht₀ hsum₀ ht

/-! ## 4. Continuity of the derivative sum -/

/-- **Continuity of the weighted mode sum** from mode-wise continuity plus the
same summable time-uniform majorant (`continuousOn_tsum`).  Applied to the
mode derivatives this is the continuity of `∂_t u`. -/
theorem continuousOn_weighted_tsum {c' : ℝ → (Fin 3 → ℤ) → Vel} {j : Fin 3}
    {w : (Fin 3 → ℤ) → ℂ} (hw : ∀ k, ‖w k‖ ≤ 1) {a b : ℝ}
    (hcont : ∀ k, ContinuousOn (fun t => c' t k) (Ioo a b))
    {u : (Fin 3 → ℤ) → ℝ} (hu : Summable u)
    (hmaj : ∀ t ∈ Ioo a b, ∀ k, ‖c' t k‖ ≤ u k) :
    ContinuousOn (fun t => ∑' k, c' t k j * w k) (Ioo a b) := by
  refine continuousOn_tsum (u := u) (fun k => ?_) hu
    (fun k t ht => (norm_component_mul_le (hw k) j).trans (hmaj t ht k))
  exact (((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).continuous.comp_continuousOn
    (hcont k)).mul continuousOn_const

/-! ## 5. The Navier-Stokes right-hand side: decay and majorants -/

/-- One fiber of a nonnegative ℓ¹ convolution is bounded by the product of
the two ℓ¹ masses (and is summable). -/
private lemma conv_l1_summable_le {F G : (Fin 3 → ℤ) → ℝ}
    (hF : Summable F) (hG : Summable G)
    (hFnn : ∀ l, 0 ≤ F l) (hGnn : ∀ l, 0 ≤ G l) (k : Fin 3 → ℤ) :
    (Summable fun l => F l * G (k - l)) ∧
      (∑' l, F l * G (k - l)) ≤ (∑' l, F l) * (∑' l, G l) := by
  have hGle : ∀ m, G m ≤ ∑' l, G l := fun m => hG.le_tsum m fun j _ => hGnn j
  have hmaj : Summable fun _l : Fin 3 → ℤ => F _l * (∑' l, G l) := hF.mul_right _
  have hle : ∀ l, F l * G (k - l) ≤ F l * ∑' l, G l := fun l =>
    mul_le_mul_of_nonneg_left (hGle _) (hFnn l)
  have hsum : Summable fun l => F l * G (k - l) :=
    hmaj.of_nonneg_of_le (fun l => mul_nonneg (hFnn l) (hGnn _)) hle
  refine ⟨hsum, ?_⟩
  calc (∑' l, F l * G (k - l)) ≤ ∑' l, F l * ∑' l, G l := hsum.tsum_le_tsum hle hmaj
    _ = (∑' l, F l) * ∑' l, G l := tsum_mul_right

/-- **The convection envelope decays.**  The half-weight split of W1
(`norm_freq_pow_split`) turns weighted ℓ¹ control of the coefficients into
`‖k‖^{-p}` decay of the convection majorant — this is what makes a
summable, time-uniform majorant for the Navier-Stokes right-hand side
possible at all (a bare Cauchy-Schwarz bound is constant in `k`, hence not
summable). -/
theorem weighted_convMaj_le {p : ℕ} (hp : 1 ≤ p) {c : (Fin 3 → ℤ) → Vel}
    (h0 : Summable fun l => ‖c l‖)
    (h1 : Summable fun l => ‖freq l‖ * ‖c l‖)
    (hWp : Summable fun l => ‖freq l‖ ^ p * ‖c l‖)
    (hWp1 : Summable fun l => ‖freq l‖ ^ (p + 1) * ‖c l‖)
    (k : Fin 3 → ℤ) :
    ‖freq k‖ ^ p * (∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
      ≤ 2 ^ (p - 1) * ((∑' l, ‖freq l‖ ^ p * ‖c l‖) * (∑' l, ‖freq l‖ * ‖c l‖)
          + (∑' l, ‖c l‖) * ∑' l, ‖freq l‖ ^ (p + 1) * ‖c l‖) := by
  obtain ⟨hs1, hb1⟩ := conv_l1_summable_le hWp h1 (fun _ => by positivity)
    (fun _ => by positivity) k
  obtain ⟨hs2, hb2⟩ := conv_l1_summable_le h0 hWp1 (fun _ => norm_nonneg _)
    (fun _ => by positivity) k
  obtain ⟨hs0, -⟩ := conv_l1_summable_le h0 h1 (fun _ => norm_nonneg _)
    (fun _ => by positivity) k
  have hpt : ∀ l, ‖freq k‖ ^ p * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
      ≤ 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)
          + ‖c l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖c (k - l)‖)) := by
    intro l
    have hnn : (0:ℝ) ≤ ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by positivity
    calc ‖freq k‖ ^ p * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
        ≤ (2 ^ (p - 1) * (‖freq l‖ ^ p + ‖freq (k - l)‖ ^ p)) *
            (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) :=
          mul_le_mul_of_nonneg_right (norm_freq_pow_split k l hp) hnn
      _ = 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)
            + ‖c l‖ * ((‖freq (k - l)‖ ^ p * ‖freq (k - l)‖) * ‖c (k - l)‖)) := by
          ring
      _ = 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)
            + ‖c l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖c (k - l)‖)) := by
          rw [← pow_succ]
  have hmajsum : Summable fun l =>
      2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)
        + ‖c l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖c (k - l)‖)) := (hs1.add hs2).mul_left _
  calc ‖freq k‖ ^ p * (∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖))
      = ∑' l, ‖freq k‖ ^ p * (‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖)) :=
        tsum_mul_left.symm
    _ ≤ ∑' l, 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖)
          + ‖c l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖c (k - l)‖)) :=
        (hs0.mul_left _).tsum_le_tsum hpt hmajsum
    _ = 2 ^ (p - 1) * ((∑' l, (‖freq l‖ ^ p * ‖c l‖) * (‖freq (k - l)‖ * ‖c (k - l)‖))
          + ∑' l, ‖c l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖c (k - l)‖)) := by
        rw [tsum_mul_left, hs1.tsum_add hs2]
    _ ≤ 2 ^ (p - 1) * ((∑' l, ‖freq l‖ ^ p * ‖c l‖) * (∑' l, ‖freq l‖ * ‖c l‖)
          + (∑' l, ‖c l‖) * ∑' l, ‖freq l‖ ^ (p + 1) * ‖c l‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by positivity)

/-- **Per-mode decay from a Sobolev-mass bound**: a bound on the level-`m`
Sobolev mass forces every individual mode to decay like `‖k‖^{-m}`.  This is
the bridge from the campaign's tsum-level bounds (which is all
`ns_full_global_flow_sobolev` gives) to the per-mode estimates a
time-uniform majorant needs. -/
theorem norm_mode_le_of_sob {m : ℕ} {c : (Fin 3 → ℤ) → Vel} {B : ℝ}
    (hsum : Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c l‖ ^ 2)
    (hB : (∑' l, ‖freq l‖ ^ (2 * m) * ‖c l‖ ^ 2) ≤ B)
    {k : Fin 3 → ℤ} (hk : k ≠ 0) :
    ‖c k‖ ≤ Real.sqrt B / ‖freq k‖ ^ m := by
  have hpos : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
  have hterm : ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 ≤ B :=
    (hsum.le_tsum k fun j _ => by positivity).trans hB
  have hsq : (‖freq k‖ ^ m) ^ 2 = ‖freq k‖ ^ (2 * m) := by
    rw [← pow_mul, mul_comm m 2]
  rw [le_div_iff₀ (by positivity)]
  have hkey : (‖c k‖ * ‖freq k‖ ^ m) ^ 2 ≤ B := by
    rw [mul_pow, hsq]
    calc ‖c k‖ ^ 2 * ‖freq k‖ ^ (2 * m)
        = ‖freq k‖ ^ (2 * m) * ‖c k‖ ^ 2 := by ring
      _ ≤ B := hterm
  calc ‖c k‖ * ‖freq k‖ ^ m
      = Real.sqrt ((‖c k‖ * ‖freq k‖ ^ m) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hkey

/-- **The Navier-Stokes right-hand side, bounded pointwise in the mode**:
viscous part plus twice the convection majorant (the factor two is the Leray
projection's Lipschitz constant, `norm_lerayProj_le`). -/
theorem norm_nsRHS_le {ν : ℝ} (hν : 0 ≤ ν) {c : (Fin 3 → ℤ) → Vel}
    (hE : Summable fun l => ‖c l‖ ^ 2)
    (hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) (k : Fin 3 → ℤ) :
    ‖(-(ν * ‖freq k‖ ^ 2)) • c k + lerayProj k (convFull c k)‖
      ≤ ν * (‖freq k‖ ^ 2 * ‖c k‖)
        + 2 * ∑' l, ‖c l‖ * (‖freq (k - l)‖ * ‖c (k - l)‖) := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    have hs : ‖(-(ν * ‖freq k‖ ^ 2) : ℝ)‖ = ν * ‖freq k‖ ^ 2 := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hs, mul_assoc]
  · exact (norm_lerayProj_le k _).trans
      (mul_le_mul_of_nonneg_left (norm_convFull_le hE hZ k) (by norm_num))

/-- **The canonical-flow majorant.**  Time-uniform weighted ℓ¹ window bounds
(through order six) produce a SUMMABLE, time-uniform majorant
`(νB + 32B²)·(‖k‖⁴)⁻¹` for the Navier-Stokes right-hand side — the exact
hypothesis `hasDerivAt_weighted_tsum_flow` and `continuousOn_weighted_tsum`
need.  Order six is what the viscous term costs: `‖k‖²‖c k‖ ≤ B·‖k‖⁻⁴`
requires control of `‖k‖⁶‖c k‖`, and `weighted_convMaj_le` at `p = 4`
supplies the matching decay for the convection.  The zero mode is handled by
the mean-zero and divergence-free clauses, which the campaign's flows carry.

Both hypothesis families are discharged from `ns_full_global_flow_sobolev`'s
per-time Sobolev clauses via `tsum_weighted_norm_le_of_bound`. -/
theorem exists_summable_nsRHS_maj {ν : ℝ} (hν : 0 ≤ ν) {a b : ℝ}
    {c : ℝ → (Fin 3 → ℤ) → Vel} {B : ℝ} (hB : 0 ≤ B)
    (hmean : ∀ t ∈ Ioo a b, c t 0 = 0)
    (hczero : ∀ t ∈ Ioo a b, convFull (c t) 0 = 0)
    (hE : ∀ t ∈ Ioo a b, Summable fun l => ‖c t l‖ ^ 2)
    (hZ : ∀ t ∈ Ioo a b, Summable fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)
    (hWs : ∀ t ∈ Ioo a b, ∀ q : ℕ, q ≤ 6 → Summable fun l => ‖freq l‖ ^ q * ‖c t l‖)
    (hWB : ∀ t ∈ Ioo a b, ∀ q : ℕ, q ≤ 6 → (∑' l, ‖freq l‖ ^ q * ‖c t l‖) ≤ B) :
    ∃ u : (Fin 3 → ℤ) → ℝ, Summable u ∧
      ∀ t ∈ Ioo a b, ∀ k, ‖(-(ν * ‖freq k‖ ^ 2)) • c t k
          + lerayProj k (convFull (c t) k)‖ ≤ u k := by
  refine ⟨fun k => (ν * B + 32 * B ^ 2) * (‖freq k‖ ^ 4)⁻¹,
    summable_inv_freq_pow_four.mul_left _, ?_⟩
  intro t ht k
  have hCnn : (0:ℝ) ≤ ν * B + 32 * B ^ 2 := by positivity
  rcases eq_or_ne k 0 with rfl | hk
  · -- the zero mode carries no dynamics: mean-zero data, div-free convection
    have hz : ‖(-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c t 0
        + lerayProj 0 (convFull (c t) 0)‖ ≤ 0 := by
      rw [hmean t ht, hczero t ht, smul_zero, zero_add]
      simpa using norm_lerayProj_le (0 : Fin 3 → ℤ) 0
    exact hz.trans (by positivity)
  · have hpos : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
    have h4 : (0:ℝ) < ‖freq k‖ ^ 4 := by positivity
    -- the viscous term, paid for by the order-six window bound
    have hvisc : ν * (‖freq k‖ ^ 2 * ‖c t k‖) ≤ ν * B * (‖freq k‖ ^ 4)⁻¹ := by
      have h6 : ‖freq k‖ ^ 6 * ‖c t k‖ ≤ B :=
        ((hWs t ht 6 le_rfl).le_tsum k fun j _ => by positivity).trans (hWB t ht 6 le_rfl)
      have hstep : ‖freq k‖ ^ 2 * ‖c t k‖ ≤ B * (‖freq k‖ ^ 4)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ h4]
        calc ‖freq k‖ ^ 2 * ‖c t k‖ * ‖freq k‖ ^ 4
            = ‖freq k‖ ^ 6 * ‖c t k‖ := by ring
          _ ≤ B := h6
      calc ν * (‖freq k‖ ^ 2 * ‖c t k‖) ≤ ν * (B * (‖freq k‖ ^ 4)⁻¹) :=
            mul_le_mul_of_nonneg_left hstep hν
        _ = ν * B * (‖freq k‖ ^ 4)⁻¹ := by ring
    -- the convection term, paid for by the p = 4 decay envelope
    have hconv : 2 * (∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖))
        ≤ 32 * B ^ 2 * (‖freq k‖ ^ 4)⁻¹ := by
      have hw := weighted_convMaj_le (p := 4) (by norm_num)
        (by simpa using hWs t ht 0 (by norm_num)) (by simpa using hWs t ht 1 (by norm_num))
        (hWs t ht 4 (by norm_num)) (hWs t ht 5 (by norm_num)) k
      have hprod : (∑' l, ‖freq l‖ ^ 4 * ‖c t l‖) * (∑' l, ‖freq l‖ * ‖c t l‖)
            + (∑' l, ‖c t l‖) * (∑' l, ‖freq l‖ ^ 5 * ‖c t l‖) ≤ B * B + B * B := by
        have e1 : (∑' l, ‖freq l‖ * ‖c t l‖) ≤ B := by
          simpa using hWB t ht 1 (by norm_num)
        have e0 : (∑' l, ‖c t l‖) ≤ B := by simpa using hWB t ht 0 (by norm_num)
        refine add_le_add (mul_le_mul (hWB t ht 4 (by norm_num)) e1
          (tsum_nonneg fun _ => by positivity) hB)
          (mul_le_mul e0 (hWB t ht 5 (by norm_num))
            (tsum_nonneg fun _ => by positivity) hB)
      have hkey : ‖freq k‖ ^ 4 * (∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖))
          ≤ 16 * B ^ 2 := by
        refine hw.trans ?_
        calc (2:ℝ) ^ (4 - 1) * ((∑' l, ‖freq l‖ ^ 4 * ‖c t l‖) * (∑' l, ‖freq l‖ * ‖c t l‖)
              + (∑' l, ‖c t l‖) * ∑' l, ‖freq l‖ ^ 5 * ‖c t l‖)
            ≤ (2:ℝ) ^ (4 - 1) * (B * B + B * B) :=
              mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ = 16 * B ^ 2 := by norm_num; ring
      have hmaj : (∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖))
          ≤ 16 * B ^ 2 * (‖freq k‖ ^ 4)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ h4]
        calc (∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖)) * ‖freq k‖ ^ 4
            = ‖freq k‖ ^ 4 * ∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖) := by ring
          _ ≤ 16 * B ^ 2 := hkey
      calc 2 * (∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖))
          ≤ 2 * (16 * B ^ 2 * (‖freq k‖ ^ 4)⁻¹) :=
            mul_le_mul_of_nonneg_left hmaj (by norm_num)
        _ = 32 * B ^ 2 * (‖freq k‖ ^ 4)⁻¹ := by ring
    calc ‖(-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)‖
        ≤ ν * (‖freq k‖ ^ 2 * ‖c t k‖)
            + 2 * ∑' l, ‖c t l‖ * (‖freq (k - l)‖ * ‖c t (k - l)‖) :=
          norm_nsRHS_le hν (hE t ht) (hZ t ht) k
      _ ≤ ν * B * (‖freq k‖ ^ 4)⁻¹ + 32 * B ^ 2 * (‖freq k‖ ^ 4)⁻¹ :=
          add_le_add hvisc hconv
      _ = (ν * B + 32 * B ^ 2) * (‖freq k‖ ^ 4)⁻¹ := by ring

end TheoremB
