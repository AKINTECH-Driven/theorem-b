/-
# Time-smoothness of the eternal flow (Tier 8b, wave W1)

The eternal small-data flow of `theorem_B_smooth_classical_eq` is `C^∞` in
time on the CLOSED half-line, mode by mode, with the right derivative at
`t = 0` within `Ici 0`.  This file delivers the textbook bootstrap:

1. `convBil`, the convection as a BILINEAR form in its two arguments
   (`convBil c c = convFull c` definitionally, `convBil_self`), so the
   product rule can separate the two factors; `hasDerivAt_convBil_flow` is
   the time-derivative of the convection along two differentiable
   coefficient flows (term-wise differentiation of the convolution series
   under summable window majorants, `hasDerivAt_tsum_of_isPreconnected`);
   `continuousOn_convBil` is its continuity twin.
2. The Leray projection is additive, ℂ-homogeneous and differentiates
   (`lerayProj_add`, `lerayProj_smul`, `HasDerivAt.lerayProj`).
3. `WindowL1 a b f`, the class of coefficient flows carrying, on the
   closed window `Icc a b`, a time-uniform weighted ℓ¹ bound at EVERY
   order.  It is closed under the three operations of the Leibniz
   recurrence (`WindowL1.convBil` through the ℓ¹ closure
   `tsum_weighted_convBil_le`, whose route is the `exists_summable_nsRHS_maj`
   recipe of TimeLayer: pointwise decay at order `p + 4` divided by
   `‖k‖⁴` and summed against `quarticKernel`; `WindowL1.visc`;
   `WindowL1.lerayProj`; `WindowL1.add`; `WindowL1.nsmul`), and it produces
   the summable time-uniform majorants the differentiation engine needs
   (`WindowL1.majorant`).
4. `sobolev_growth_all_m`, the level-`m` growth bound of
   `ns_full_global_flow_sobolev` transferred to ONE given flow at every
   `m ≥ 1` (each level's witness is identified with the given flow by
   `theorem_B_unique`, the `flow_agree_Ici` recipe); `windowL1_of_sobolev_all`
   turns the per-window Sobolev bounds into the base case of the window
   class.
5. The chain: `D 0 = c`, `D (n+1) = -ν‖k‖²·D n + P_k (S n)` with `S n` the
   Leibniz convection sum `Σ_{i+j=n} C(n,i)·convBil (D i) (D j)`.  By
   induction (windows first, then derivatives on `Ioi 0`, then continuity
   on `Ici 0`, then the endpoint derivative at `0` by the endpoint tool
   `hasDerivWithinAt_Ici_of_tendsto_deriv`): `D n` differentiates to
   `D (n+1)` on `t > 0`, has the right derivative `D (n+1) 0` within
   `Ici 0`, is continuous on `Ici 0`, and lies in every window class; the
   same for `S n`.  `hasDerivAt_leibnizSum` is the generic Leibniz step;
   `hasDerivWithinAt_mode_zero` the endpoint derivative of the mode ODE at
   `t = 0`; `contDiffOn_infty_of_hasDerivAt_chain` and
   `contDiffOn_infty_Ici_of_chain` read a derivative chain as `C^∞`.
6. `theorem_B_time_smooth`, the capstone: the twenty clauses of
   `theorem_B_smooth_classical_eq` re-exported verbatim, plus the chain
   (clause 21, `D` and `S` exported together) and `C^∞` in time of every
   mode on `Ici 0` (clause 22).
7. Audit probes, compiled in the tree and registered (non-frozen):
   `chain_unique`, `chain_unique_Ici`, `clause21_pinned`.  Two chains with
   the same base flow and the derivative clauses agree at every order on
   `Ioi 0`; with the continuity clauses they agree on `Ici 0`; hence the
   `∃ D S` of clause 21 admits at most one `D` on `Ici 0` for a given flow,
   and `S` is determined by `D` through its defining clause.  This is the
   `chain_unique` that the frozen comment of clause 21 cites (the probe of
   the blueprint's design-b register, re-proved by the W1 statement-shape
   reader and landed here).

Honest scope.  `∞` is `(⊤ : ℕ∞)` cast into `WithTop ℕ∞`, NOT `ω`: no
analyticity in time is claimed.  Smoothness here is in TIME, mode by mode;
joint smoothness in `(x, t)` is the next wave.  The constant `κ` and the
inherited Sobolev growth constants are of explicit form, exported as
compiled existentials; the window constants of the chain (`WindowL1`, the
majorants of `WindowL1.majorant`) are UNTRACKED existentials produced by
the Leibniz induction.  Nothing here is new mathematics: the bootstrap
(differentiate the mode equation, the `n`-th derivative satisfies a
Leibniz recurrence, weighted ℓ¹ closes under the three operations) is
textbook (Temam, *Navier-Stokes Equations*, Ch. III;
Robinson-Rodrigo-Sadowski, *The Three-Dimensional Navier-Stokes
Equations*, Ch. 6-7; Constantin-Foias, *Navier-Stokes Equations*, Ch. 10;
chapter numbers unverified).  Priority is not claimed for anything.  The
machine-checked Navier-Stokes work this file sits beside is named in the
announcement and the README (uda-lab/leray-hopf, HeliCorgi's
ns-mns2-flowmap-bridge, Miller, OpenAI's forced-breakdown certificate,
Alpöge and Buckmaster); none of it is composed with, reproduced by, or
superseded by anything here.

Spec drift recorded.  The headers of `TheoremBSmooth` and
`ClassicalEquation` say the campaign has no time-derivative of `convFull`;
after this file that sentence is superseded (`hasDerivAt_convBil_flow` at
`a = b`).  Those files are frozen and are not edited here; the drift is
recorded for the orchestrator.

Statement observation (not drift).  The frozen `hasDerivAt_leibnizSum`
takes derivative hypotheses for `i ≤ n + 1`; its derivative needs them only
for `i ≤ n` (windows ARE needed up to `n + 1`).  The chain induction runs on
the non-frozen sibling `hasDerivAt_leibnizSum'` with `i ≤ n`, and the frozen
form is its weakening.

Junk-tsum discipline: every tsum statement carries its Summable certificate
as a hypothesis or exports it.

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.ClassicalEquation

namespace TheoremB

open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ContDiff

/-! ## 1. The bilinear convection -/

/-- The convection as a bilinear form: `convBil a b k = -Σ' l, (i·(a l · (k-l))) • b (k-l)`.
At `a = b` it is `convFull` definitionally (`convBil_self`). -/
noncomputable def convBil (a b : (Fin 3 → ℤ) → Vel) (k : Fin 3 → ℤ) : Vel :=
  -(∑' l, (Complex.I * dotR (a l) (freq (k - l))) • b (k - l))

/-- The diagonal of the bilinear convection is the full convection, by `rfl`. -/
theorem convBil_self (c : (Fin 3 → ℤ) → Vel) : convBil c c = convFull c := rfl

/-! ## 2. The Leray projection: additive, homogeneous, differentiable -/

private lemma dotR_add_left (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (v + w) r = dotR v r + dotR w r := by
  simp only [dotR, WithLp.ofLp_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dotR_smul_left (a : ℂ) (v : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    dotR (a • v) r = a * dotR v r := by
  simp only [dotR, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The Leray projection is additive. -/
theorem lerayProj_add (k : Fin 3 → ℤ) (v w : Vel) :
    lerayProj k (v + w) = lerayProj k v + lerayProj k w := by
  simp only [lerayProj, dotR_add_left, add_div, add_smul]
  abel

/-- The Leray projection is ℂ-homogeneous. -/
theorem lerayProj_smul (k : Fin 3 → ℤ) (a : ℂ) (v : Vel) :
    lerayProj k (a • v) = a • lerayProj k v := by
  simp only [lerayProj, dotR_smul_left, mul_div_assoc, mul_smul, smul_sub]

/-- The Leray projection differentiates: components through
`EuclideanSpace.proj … restrictScalars ℝ`, the pairing `dotR` as a finite
sum of products, then the defining difference. -/
theorem HasDerivAt.lerayProj {f : ℝ → Vel} {f' : Vel} {t : ℝ} (k : Fin 3 → ℤ)
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => lerayProj k (f s)) (lerayProj k f') t := by
  have hcomp : ∀ j : Fin 3, HasDerivAt (fun s => (f s) j) (f' j) t := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf
  have hd : HasDerivAt (fun s => dotR (f s) (freq k)) (dotR f' (freq k)) t := by
    unfold dotR
    exact HasDerivAt.fun_sum fun j _ => (hcomp j).mul_const _
  unfold TheoremB.lerayProj
  exact hf.sub ((hd.div_const _).smul_const _)

/-! ## 3. Pointwise bounds on the bilinear convection -/

/-- One convolution term is dominated by the product of the three norms. -/
private lemma norm_convTerm_le (v w : Vel) (r : EuclideanSpace ℝ (Fin 3)) :
    ‖(Complex.I * dotR v r) • w‖ ≤ ‖v‖ * (‖r‖ * ‖w‖) := by
  rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
  calc ‖dotR v r‖ * ‖w‖ ≤ (‖r‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (norm_dotR_le _ _) (norm_nonneg _)
    _ = ‖v‖ * (‖r‖ * ‖w‖) := by ring

/-- One fiber of a nonnegative ℓ¹ convolution is bounded by the product of
the two ℓ¹ masses (and is summable).  Public clone of TimeLayer's private
`conv_l1_summable_le`. -/
theorem conv_l1_summable_le' {F G : (Fin 3 → ℤ) → ℝ}
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

/-- The bilinear convection is dominated by the ℓ¹ convolution majorant
(two-sequence form of `norm_convFull_le`). -/
theorem norm_convBil_le {a b : (Fin 3 → ℤ) → Vel}
    (ha0 : Summable fun l => ‖a l‖)
    (hb1 : Summable fun l => ‖freq l‖ * ‖b l‖) (k : Fin 3 → ℤ) :
    ‖convBil a b k‖ ≤ ∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖) := by
  obtain ⟨hmaj, -⟩ := conv_l1_summable_le' ha0 hb1 (fun _ => norm_nonneg _)
    (fun _ => by positivity) k
  have hterm : ∀ l, ‖(Complex.I * dotR (a l) (freq (k - l))) • b (k - l)‖ ≤
      ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖) := fun l => norm_convTerm_le _ _ _
  have hnorm_sum : Summable fun l =>
      ‖(Complex.I * dotR (a l) (freq (k - l))) • b (k - l)‖ :=
    hmaj.of_nonneg_of_le (fun l => norm_nonneg _) hterm
  calc ‖convBil a b k‖
      = ‖∑' l, (Complex.I * dotR (a l) (freq (k - l))) • b (k - l)‖ := by
        rw [convBil, norm_neg]
    _ ≤ ∑' l, ‖(Complex.I * dotR (a l) (freq (k - l))) • b (k - l)‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ ∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖) :=
        hnorm_sum.tsum_le_tsum hterm hmaj

/-- **The convection envelope decays, two-sequence form** of
`weighted_convMaj_le` (TimeLayer): the half-weight split
`norm_freq_pow_split` turns weighted ℓ¹ control of the two factors into
`‖k‖^{-p}` decay of the convolution majorant. -/
theorem weighted_convMaj_le₂ {p : ℕ} (hp : 1 ≤ p) {a b : (Fin 3 → ℤ) → Vel}
    (ha0 : Summable fun l => ‖a l‖)
    (haP : Summable fun l => ‖freq l‖ ^ p * ‖a l‖)
    (hb1 : Summable fun l => ‖freq l‖ * ‖b l‖)
    (hbP1 : Summable fun l => ‖freq l‖ ^ (p + 1) * ‖b l‖)
    (k : Fin 3 → ℤ) :
    ‖freq k‖ ^ p * (∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖))
      ≤ 2 ^ (p - 1) * ((∑' l, ‖freq l‖ ^ p * ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
          + (∑' l, ‖a l‖) * ∑' l, ‖freq l‖ ^ (p + 1) * ‖b l‖) := by
  obtain ⟨hs1, hb1'⟩ := conv_l1_summable_le' haP hb1 (fun _ => by positivity)
    (fun _ => by positivity) k
  obtain ⟨hs2, hb2'⟩ := conv_l1_summable_le' ha0 hbP1 (fun _ => norm_nonneg _)
    (fun _ => by positivity) k
  obtain ⟨hs0, -⟩ := conv_l1_summable_le' ha0 hb1 (fun _ => norm_nonneg _)
    (fun _ => by positivity) k
  have hpt : ∀ l, ‖freq k‖ ^ p * (‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖))
      ≤ 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖a l‖) * (‖freq (k - l)‖ * ‖b (k - l)‖)
          + ‖a l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖b (k - l)‖)) := by
    intro l
    have hnn : (0:ℝ) ≤ ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖) := by positivity
    calc ‖freq k‖ ^ p * (‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖))
        ≤ (2 ^ (p - 1) * (‖freq l‖ ^ p + ‖freq (k - l)‖ ^ p)) *
            (‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖)) :=
          mul_le_mul_of_nonneg_right (norm_freq_pow_split k l hp) hnn
      _ = 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖a l‖) * (‖freq (k - l)‖ * ‖b (k - l)‖)
            + ‖a l‖ * ((‖freq (k - l)‖ ^ p * ‖freq (k - l)‖) * ‖b (k - l)‖)) := by
          ring
      _ = 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖a l‖) * (‖freq (k - l)‖ * ‖b (k - l)‖)
            + ‖a l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖b (k - l)‖)) := by
          rw [← pow_succ]
  have hmajsum : Summable fun l =>
      2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖a l‖) * (‖freq (k - l)‖ * ‖b (k - l)‖)
        + ‖a l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖b (k - l)‖)) := (hs1.add hs2).mul_left _
  calc ‖freq k‖ ^ p * (∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖))
      = ∑' l, ‖freq k‖ ^ p * (‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖)) :=
        tsum_mul_left.symm
    _ ≤ ∑' l, 2 ^ (p - 1) * ((‖freq l‖ ^ p * ‖a l‖) * (‖freq (k - l)‖ * ‖b (k - l)‖)
          + ‖a l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖b (k - l)‖)) :=
        (hs0.mul_left _).tsum_le_tsum hpt hmajsum
    _ = 2 ^ (p - 1) * ((∑' l, (‖freq l‖ ^ p * ‖a l‖) * (‖freq (k - l)‖ * ‖b (k - l)‖))
          + ∑' l, ‖a l‖ * (‖freq (k - l)‖ ^ (p + 1) * ‖b (k - l)‖)) := by
        rw [tsum_mul_left, hs1.tsum_add hs2]
    _ ≤ 2 ^ (p - 1) * ((∑' l, ‖freq l‖ ^ p * ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
          + (∑' l, ‖a l‖) * ∑' l, ‖freq l‖ ^ (p + 1) * ‖b l‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1' hb2') (by positivity)


/-! ## 4. The ℓ¹ closure of the bilinear convection -/

private lemma freq_zero_eq' : freq (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [freq]

/-- **The weighted ℓ¹ closure of the bilinear convection.**  Weighted ℓ¹
control of both factors at every order gives weighted ℓ¹ control of the
convection at every order: for `k ≠ 0` the order-`(p+4)` decay of the
envelope (`weighted_convMaj_le₂`) is divided by `‖k‖⁴` and summed against
`quarticKernel`; the `k = 0` term is the order-0 bound.  (The
`exists_summable_nsRHS_maj` recipe of TimeLayer, at every order.) -/
theorem tsum_weighted_convBil_le (p : ℕ) {a b : (Fin 3 → ℤ) → Vel}
    (ha : ∀ q : ℕ, Summable fun l => ‖freq l‖ ^ q * ‖a l‖)
    (hb : ∀ q : ℕ, Summable fun l => ‖freq l‖ ^ q * ‖b l‖) :
    (Summable fun k => ‖freq k‖ ^ p * ‖convBil a b k‖) ∧
    (∑' k, ‖freq k‖ ^ p * ‖convBil a b k‖)
      ≤ (∑' l, ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
        + 2 ^ (p + 3) * quarticKernel *
          ((∑' l, ‖freq l‖ ^ (p + 4) * ‖a l‖) * (∑' l, ‖freq l‖ * ‖b l‖)
            + (∑' l, ‖a l‖) * ∑' l, ‖freq l‖ ^ (p + 5) * ‖b l‖) := by
  have ha0 : Summable fun l => ‖a l‖ := by simpa using ha 0
  have hb1 : Summable fun l => ‖freq l‖ * ‖b l‖ := by simpa using hb 1
  set A0 : ℝ := ∑' l, ‖a l‖ with hA0
  set B1 : ℝ := ∑' l, ‖freq l‖ * ‖b l‖ with hB1
  set M : ℝ := (∑' l, ‖freq l‖ ^ (p + 4) * ‖a l‖) * B1
      + A0 * ∑' l, ‖freq l‖ ^ (p + 5) * ‖b l‖ with hM
  -- the pointwise bound by a summable majorant
  have hpt : ∀ k, ‖freq k‖ ^ p * ‖convBil a b k‖ ≤
      (if k = 0 then A0 * B1 else 0) + 2 ^ (p + 3) * M * (‖freq k‖ ^ 4)⁻¹ := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · -- the zero mode: the order-0 bound
      rw [if_pos rfl, freq_zero_eq', norm_zero]
      have h0p : (0:ℝ) ^ p ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      have hc : ‖convBil a b 0‖ ≤ A0 * B1 :=
        (norm_convBil_le ha0 hb1 0).trans
          (conv_l1_summable_le' ha0 hb1 (fun _ => norm_nonneg _) (fun _ => by positivity) 0).2
      calc (0:ℝ) ^ p * ‖convBil a b 0‖ ≤ 1 * ‖convBil a b 0‖ :=
            mul_le_mul_of_nonneg_right h0p (norm_nonneg _)
        _ = ‖convBil a b 0‖ := one_mul _
        _ ≤ A0 * B1 := hc
        _ = A0 * B1 + 2 ^ (p + 3) * M * ((0:ℝ) ^ 4)⁻¹ := by norm_num
    · -- a nonzero mode: order-(p+4) decay divided by ‖k‖⁴
      rw [if_neg hk, zero_add]
      have hpos : (0:ℝ) < ‖freq k‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hk)
      have h4 : ‖freq k‖ ^ 4 * (‖freq k‖ ^ 4)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
      have hw := weighted_convMaj_le₂ (p := p + 4) (by omega) ha0 (ha (p + 4)) hb1
        (hb (p + 4 + 1)) k
      have e1 : p + 4 - 1 = p + 3 := by omega
      rw [e1] at hw
      have hkey : ‖freq k‖ ^ (p + 4) * (∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖))
          ≤ 2 ^ (p + 3) * M := hw
      have hcb := norm_convBil_le ha0 hb1 k
      have hinv : (0:ℝ) ≤ (‖freq k‖ ^ 4)⁻¹ := by positivity
      calc ‖freq k‖ ^ p * ‖convBil a b k‖
          = (‖freq k‖ ^ (p + 4) * ‖convBil a b k‖) * (‖freq k‖ ^ 4)⁻¹ := by
            calc ‖freq k‖ ^ p * ‖convBil a b k‖
                = ‖freq k‖ ^ p * ‖convBil a b k‖ * (‖freq k‖ ^ 4 * (‖freq k‖ ^ 4)⁻¹) := by
                  rw [h4, mul_one]
              _ = (‖freq k‖ ^ (p + 4) * ‖convBil a b k‖) * (‖freq k‖ ^ 4)⁻¹ := by ring
        _ ≤ (‖freq k‖ ^ (p + 4) * (∑' l, ‖a l‖ * (‖freq (k - l)‖ * ‖b (k - l)‖)))
              * (‖freq k‖ ^ 4)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb (by positivity)) hinv
        _ ≤ (2 ^ (p + 3) * M) * (‖freq k‖ ^ 4)⁻¹ := mul_le_mul_of_nonneg_right hkey hinv
  have hu : Summable fun k : Fin 3 → ℤ =>
      (if k = 0 then A0 * B1 else 0) + 2 ^ (p + 3) * M * (‖freq k‖ ^ 4)⁻¹ :=
    (hasSum_ite_eq (0 : Fin 3 → ℤ) (A0 * B1)).summable.add
      (summable_inv_freq_pow_four.mul_left _)
  have hsum : Summable fun k => ‖freq k‖ ^ p * ‖convBil a b k‖ :=
    hu.of_nonneg_of_le (fun _ => by positivity) hpt
  refine ⟨hsum, ?_⟩
  calc (∑' k, ‖freq k‖ ^ p * ‖convBil a b k‖)
      ≤ ∑' k : Fin 3 → ℤ,
          ((if k = 0 then A0 * B1 else 0) + 2 ^ (p + 3) * M * (‖freq k‖ ^ 4)⁻¹) :=
        hsum.tsum_le_tsum hpt hu
    _ = A0 * B1 + 2 ^ (p + 3) * M * quarticKernel := by
        rw [(hasSum_ite_eq (0 : Fin 3 → ℤ) (A0 * B1)).summable.tsum_add
          (summable_inv_freq_pow_four.mul_left _),
          (hasSum_ite_eq (0 : Fin 3 → ℤ) (A0 * B1)).tsum_eq, tsum_mul_left]
        rfl
    _ = A0 * B1 + 2 ^ (p + 3) * quarticKernel * M := by ring

/-! ## 5. The window class and its closure -/

/-- The window class: a coefficient flow carrying, on the closed window
`Icc a b`, a time-uniform weighted ℓ¹ bound at EVERY order `p` (the
constant is an untracked existential per order).  Trivially true on an
empty window. -/
def WindowL1 (a b : ℝ) (f : ℝ → (Fin 3 → ℤ) → Vel) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, ∀ t ∈ Icc a b,
    (Summable fun l => ‖freq l‖ ^ p * ‖f t l‖) ∧ (∑' l, ‖freq l‖ ^ p * ‖f t l‖) ≤ C

/-- The quintic lattice weight is summable (dominated by the quartic one). -/
private lemma summable_inv_freq_pow_five :
    Summable fun k : Fin 3 → ℤ => (‖freq k‖ ^ 5)⁻¹ := by
  refine summable_inv_freq_pow_four.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · rw [freq_zero_eq', norm_zero]; norm_num
  · have h1 : (1:ℝ) ≤ ‖freq k‖ := one_le_norm_freq hk
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by norm_num))

/-- **A window class member has a summable time-uniform majorant** with one
weighted order: orders 0 and 5 of the window bound give
`‖f t l‖ ≤ C₀·[l = 0] + C₅·‖l‖⁻⁵`, and both `A` and `‖l‖·A` are summable. -/
theorem WindowL1.majorant {a b : ℝ} {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    ∃ A : (Fin 3 → ℤ) → ℝ, Summable A ∧ (Summable fun l => ‖freq l‖ * A l) ∧
      ∀ t ∈ Icc a b, ∀ l, ‖f t l‖ ≤ A l := by
  obtain ⟨C0, hC0⟩ := hf 0
  obtain ⟨C5, hC5⟩ := hf 5
  refine ⟨fun l => max C0 0 * (if l = 0 then 1 else 0) + max C5 0 * (‖freq l‖ ^ 5)⁻¹,
    ?_, ?_, ?_⟩
  · exact ((hasSum_ite_eq (0 : Fin 3 → ℤ) (1:ℝ)).summable.mul_left _).add
      (summable_inv_freq_pow_five.mul_left _)
  · refine (summable_inv_freq_pow_four.mul_left (max C5 0)).of_nonneg_of_le
      (fun l => mul_nonneg (norm_nonneg _) (add_nonneg
        (mul_nonneg (le_max_right _ _) (by split_ifs <;> norm_num))
        (mul_nonneg (le_max_right _ _) (by positivity)))) (fun l => ?_)
    show ‖freq l‖ * (max C0 0 * (if l = 0 then 1 else 0) + max C5 0 * (‖freq l‖ ^ 5)⁻¹)
      ≤ max C5 0 * (‖freq l‖ ^ 4)⁻¹
    rcases eq_or_ne l 0 with rfl | hl
    · rw [freq_zero_eq', norm_zero]; norm_num
    · rw [if_neg hl, mul_zero, zero_add]
      have hne : ‖freq l‖ ≠ 0 := (lt_of_lt_of_le one_pos (one_le_norm_freq hl)).ne'
      have e : ‖freq l‖ * (max C5 0 * (‖freq l‖ ^ 5)⁻¹) = max C5 0 * (‖freq l‖ ^ 4)⁻¹ := by
        field_simp
      exact e.le
  · intro t ht l
    show ‖f t l‖ ≤ max C0 0 * (if l = 0 then 1 else 0) + max C5 0 * (‖freq l‖ ^ 5)⁻¹
    rcases eq_or_ne l 0 with rfl | hl
    · have h0 : ‖f t 0‖ ≤ C0 := by
        have h := ((hC0 t ht).1.le_tsum 0 fun j _ => by positivity).trans (hC0 t ht).2
        simpa using h
      have h5 : ((0:ℝ) ^ 5)⁻¹ = 0 := by norm_num
      rw [if_pos rfl, freq_zero_eq', norm_zero, h5, mul_one, mul_zero, add_zero]
      exact h0.trans (le_max_left _ _)
    · rw [if_neg hl, mul_zero, zero_add]
      have h5 : ‖freq l‖ ^ 5 * ‖f t l‖ ≤ max C5 0 :=
        ((hC5 t ht).1.le_tsum l fun j _ => by positivity).trans
          ((hC5 t ht).2.trans (le_max_left _ _))
      have hpos : (0:ℝ) < ‖freq l‖ := lt_of_lt_of_le one_pos (one_le_norm_freq hl)
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖f t l‖ * ‖freq l‖ ^ 5 = ‖freq l‖ ^ 5 * ‖f t l‖ := mul_comm _ _
        _ ≤ max C5 0 := h5

/-- **Closure under the bilinear convection** (through the ℓ¹ closure
`tsum_weighted_convBil_le`; orders `0`, `p + 4` of the first factor and
`1`, `p + 5` of the second feed the window constant). -/
theorem WindowL1.convBil {a b : ℝ} {f g : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) (hg : WindowL1 a b g) :
    WindowL1 a b (fun t => convBil (f t) (g t)) := by
  intro p
  obtain ⟨F0, hF0⟩ := hf 0
  obtain ⟨F4, hF4⟩ := hf (p + 4)
  obtain ⟨G1, hG1⟩ := hg 1
  obtain ⟨G5, hG5⟩ := hg (p + 5)
  refine ⟨max F0 0 * max G1 0 + 2 ^ (p + 3) * quarticKernel *
    (max F4 0 * max G1 0 + max F0 0 * max G5 0), fun t ht => ?_⟩
  have hfa : ∀ q : ℕ, Summable fun l => ‖freq l‖ ^ q * ‖f t l‖ :=
    fun q => ((hf q).choose_spec t ht).1
  have hgb : ∀ q : ℕ, Summable fun l => ‖freq l‖ ^ q * ‖g t l‖ :=
    fun q => ((hg q).choose_spec t ht).1
  obtain ⟨hsum, hle⟩ := tsum_weighted_convBil_le p hfa hgb
  refine ⟨hsum, hle.trans ?_⟩
  have e0 : (∑' l, ‖f t l‖) ≤ max F0 0 := by
    have := (hF0 t ht).2
    simp only [pow_zero, one_mul] at this
    exact this.trans (le_max_left _ _)
  have e1 : (∑' l, ‖freq l‖ * ‖g t l‖) ≤ max G1 0 := by
    have := (hG1 t ht).2
    simp only [pow_one] at this
    exact this.trans (le_max_left _ _)
  have e4 : (∑' l, ‖freq l‖ ^ (p + 4) * ‖f t l‖) ≤ max F4 0 :=
    (hF4 t ht).2.trans (le_max_left _ _)
  have e5 : (∑' l, ‖freq l‖ ^ (p + 5) * ‖g t l‖) ≤ max G5 0 :=
    (hG5 t ht).2.trans (le_max_left _ _)
  have n0 : 0 ≤ ∑' l, ‖f t l‖ := tsum_nonneg fun _ => norm_nonneg _
  have n1 : 0 ≤ ∑' l, ‖freq l‖ * ‖g t l‖ := tsum_nonneg fun _ => by positivity
  have n5 : 0 ≤ ∑' l, ‖freq l‖ ^ (p + 5) * ‖g t l‖ := tsum_nonneg fun _ => by positivity
  refine add_le_add (mul_le_mul e0 e1 n1 (le_max_right _ _)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) quarticKernel_nonneg)
  exact add_le_add (mul_le_mul e4 e1 n1 (le_max_right _ _))
    (mul_le_mul e0 e5 n5 (le_max_right _ _))

/-- Closure under the viscous multiplier `-ν‖k‖²` (two orders up). -/
theorem WindowL1.visc {a b : ℝ} (ν : ℝ) {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    WindowL1 a b (fun t k => (-(ν * ‖freq k‖ ^ 2)) • f t k) := by
  intro p
  obtain ⟨C, hC⟩ := hf (p + 2)
  refine ⟨|ν| * C, fun t ht => ?_⟩
  have e : ∀ k, ‖freq k‖ ^ p * ‖(-(ν * ‖freq k‖ ^ 2)) • f t k‖
      = |ν| * (‖freq k‖ ^ (p + 2) * ‖f t k‖) := by
    intro k
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖freq k‖ ^ 2), pow_add]
    ring
  refine ⟨((hC t ht).1.mul_left |ν|).congr fun k => (e k).symm, ?_⟩
  calc (∑' k, ‖freq k‖ ^ p * ‖(-(ν * ‖freq k‖ ^ 2)) • f t k‖)
      = |ν| * ∑' k, ‖freq k‖ ^ (p + 2) * ‖f t k‖ := by rw [tsum_congr e, tsum_mul_left]
    _ ≤ |ν| * C := mul_le_mul_of_nonneg_left (hC t ht).2 (abs_nonneg _)

/-- Closure under the Leray projection (`norm_lerayProj_le`, factor two). -/
theorem WindowL1.lerayProj {a b : ℝ} {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    WindowL1 a b (fun t k => lerayProj k (f t k)) := by
  intro p
  obtain ⟨C, hC⟩ := hf p
  refine ⟨2 * C, fun t ht => ?_⟩
  have hle : ∀ k, ‖freq k‖ ^ p * ‖TheoremB.lerayProj k (f t k)‖
      ≤ 2 * (‖freq k‖ ^ p * ‖f t k‖) := by
    intro k
    calc ‖freq k‖ ^ p * ‖TheoremB.lerayProj k (f t k)‖ ≤ ‖freq k‖ ^ p * (2 * ‖f t k‖) :=
          mul_le_mul_of_nonneg_left (norm_lerayProj_le k _) (by positivity)
      _ = 2 * (‖freq k‖ ^ p * ‖f t k‖) := by ring
  have hmaj : Summable fun k => 2 * (‖freq k‖ ^ p * ‖f t k‖) := (hC t ht).1.mul_left 2
  have hsum : Summable fun k => ‖freq k‖ ^ p * ‖TheoremB.lerayProj k (f t k)‖ :=
    hmaj.of_nonneg_of_le (fun _ => by positivity) hle
  refine ⟨hsum, ?_⟩
  calc (∑' k, ‖freq k‖ ^ p * ‖TheoremB.lerayProj k (f t k)‖)
      ≤ ∑' k, 2 * (‖freq k‖ ^ p * ‖f t k‖) := hsum.tsum_le_tsum hle hmaj
    _ = 2 * ∑' k, ‖freq k‖ ^ p * ‖f t k‖ := tsum_mul_left
    _ ≤ 2 * C := mul_le_mul_of_nonneg_left (hC t ht).2 (by norm_num)

/-- Closure under addition. -/
theorem WindowL1.add {a b : ℝ} {f g : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) (hg : WindowL1 a b g) :
    WindowL1 a b (fun t k => f t k + g t k) := by
  intro p
  obtain ⟨C, hC⟩ := hf p
  obtain ⟨D, hD⟩ := hg p
  refine ⟨C + D, fun t ht => ?_⟩
  have hle : ∀ k, ‖freq k‖ ^ p * ‖f t k + g t k‖
      ≤ ‖freq k‖ ^ p * ‖f t k‖ + ‖freq k‖ ^ p * ‖g t k‖ := by
    intro k
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  have hmaj : Summable fun k => ‖freq k‖ ^ p * ‖f t k‖ + ‖freq k‖ ^ p * ‖g t k‖ :=
    (hC t ht).1.add (hD t ht).1
  have hsum : Summable fun k => ‖freq k‖ ^ p * ‖f t k + g t k‖ :=
    hmaj.of_nonneg_of_le (fun _ => by positivity) hle
  refine ⟨hsum, ?_⟩
  calc (∑' k, ‖freq k‖ ^ p * ‖f t k + g t k‖)
      ≤ ∑' k, (‖freq k‖ ^ p * ‖f t k‖ + ‖freq k‖ ^ p * ‖g t k‖) :=
        hsum.tsum_le_tsum hle hmaj
    _ = (∑' k, ‖freq k‖ ^ p * ‖f t k‖) + ∑' k, ‖freq k‖ ^ p * ‖g t k‖ :=
        (hC t ht).1.tsum_add (hD t ht).1
    _ ≤ C + D := add_le_add (hC t ht).2 (hD t ht).2

/-- Closure under the natural-number multiples of the Leibniz coefficients. -/
theorem WindowL1.nsmul {a b : ℝ} (n : ℕ) {f : ℝ → (Fin 3 → ℤ) → Vel}
    (hf : WindowL1 a b f) :
    WindowL1 a b (fun t k => n • f t k) := by
  intro p
  obtain ⟨C, hC⟩ := hf p
  refine ⟨n * C, fun t ht => ?_⟩
  have hle : ∀ k, ‖freq k‖ ^ p * ‖n • f t k‖ ≤ n * (‖freq k‖ ^ p * ‖f t k‖) := by
    intro k
    calc ‖freq k‖ ^ p * ‖n • f t k‖ ≤ ‖freq k‖ ^ p * (n * ‖f t k‖) :=
          mul_le_mul_of_nonneg_left norm_nsmul_le (by positivity)
      _ = n * (‖freq k‖ ^ p * ‖f t k‖) := by ring
  have hmaj : Summable fun k => (n : ℝ) * (‖freq k‖ ^ p * ‖f t k‖) := (hC t ht).1.mul_left _
  have hsum : Summable fun k => ‖freq k‖ ^ p * ‖n • f t k‖ :=
    hmaj.of_nonneg_of_le (fun _ => by positivity) hle
  refine ⟨hsum, ?_⟩
  calc (∑' k, ‖freq k‖ ^ p * ‖n • f t k‖)
      ≤ ∑' k, (n : ℝ) * (‖freq k‖ ^ p * ‖f t k‖) := hsum.tsum_le_tsum hle hmaj
    _ = n * ∑' k, ‖freq k‖ ^ p * ‖f t k‖ := tsum_mul_left
    _ ≤ n * C := mul_le_mul_of_nonneg_left (hC t ht).2 (Nat.cast_nonneg n)

/-- The zero flow is in every window class (non-frozen helper). -/
theorem WindowL1.zero {a b : ℝ} : WindowL1 a b (fun _ _ => (0 : Vel)) := by
  intro p
  refine ⟨0, fun t _ => ?_⟩
  simp

/-- Closure under finite sums (non-frozen helper for the antidiagonal sums). -/
theorem WindowL1.finset_sum {a b : ℝ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → ℝ → (Fin 3 → ℤ) → Vel) (h : ∀ i ∈ s, WindowL1 a b (F i)) :
    WindowL1 a b (fun t k => ∑ i ∈ s, F i t k) := by
  induction s using Finset.induction_on with
  | empty => simpa using (WindowL1.zero (a := a) (b := b))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact WindowL1.add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ## 6. Every Sobolev level for ONE flow, and the base window -/

/-- Two eternal flows with the same datum, both in `theorem_B_unique`'s class
with the same budgets, agree everywhere on `[0, ∞)`.  Public clone of
TheoremBSmooth's private `flow_agree_Ici`. -/
theorem flow_agree_Ici' {ν : ℝ} (hν : 0 < ν) {c₀ : (Fin 3 → ℤ) → Vel}
    {c d : ℝ → (Fin 3 → ℤ) → Vel}
    (hc0 : c 0 = c₀) (hd0 : d 0 = c₀)
    (hccont : ∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ)))
    (hdcont : ∀ k, ContinuousOn (fun s => d s k) (Ici (0:ℝ)))
    (hcsum : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2))
    (hdsum : ∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖d t l‖ ^ 2) ∧
      Summable (fun l => ‖freq l‖ ^ 2 * ‖d t l‖ ^ 2))
    (hcb : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀)
    (hdb : ∀ t ∈ Ici (0:ℝ), en (d t) ≤ en c₀ ∧ ens (d t) ≤ ens c₀)
    (hcdiv : ∀ t ∈ Ici (0:ℝ), DivFree (c t))
    (hddiv : ∀ t ∈ Ici (0:ℝ), DivFree (d t))
    (hceq : ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
    (hdeq : ∀ t ∈ Ici (0:ℝ), ∀ k, d t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • d s k + lerayProj k (convFull (d s) k))) :
    ∀ t ∈ Ici (0:ℝ), ∀ k, c t k = d t k := by
  intro t ht k
  have hsub : Icc (0:ℝ) t ⊆ Ici (0:ℝ) := Icc_subset_Ici_self
  exact theorem_B_unique hν ht hc0 hd0
    (fun k => (hccont k).mono hsub) (fun k => (hdcont k).mono hsub)
    (fun s hs => hcsum s (hsub hs)) (fun s hs => hdsum s (hsub hs))
    (fun s hs => hcb s (hsub hs)) (fun s hs => hdb s (hsub hs))
    (fun s hs => hcdiv s (hsub hs)) (fun s hs => hddiv s (hsub hs))
    (fun s hs => hceq s (hsub hs)) (fun s hs => hdeq s (hsub hs))
    t ⟨ht, le_refl t⟩ k

/-- **Every Sobolev level grows at most exponentially, for ONE given flow.**
`ns_full_global_flow_sobolev` quantifies `∀ m` OUTSIDE `∃ c`; here each
level's witness is identified with the given flow (which is in the
uniqueness class: exactly the seven clauses taken as hypotheses) by
`theorem_B_unique`, and its level-`m` clause transfers.  The growth constant
`K` is of explicit form, exported as a compiled existential. -/
theorem sobolev_growth_all_m :
    ∃ κ, 0 < κ ∧ ∀ {ν : ℝ}, 0 < ν → ∀ {c₀ : (Fin 3 → ℤ) → Vel},
      (∀ m : ℕ, Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c₀ l‖ ^ 2) →
      c₀ 0 = 0 → RealField c₀ → DivFree c₀ → κ * en c₀ * ens c₀ < ν ^ 4 →
      ∀ {c : ℝ → (Fin 3 → ℤ) → Vel},
      c 0 = c₀ →
      (∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ))) →
      (∀ t ∈ Ici (0:ℝ), Summable (fun l => ‖c t l‖ ^ 2) ∧
        Summable (fun l => ‖freq l‖ ^ 2 * ‖c t l‖ ^ 2)) →
      (∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀) →
      (∀ t ∈ Ici (0:ℝ), DivFree (c t)) →
      (∀ t ∈ Ici (0:ℝ), ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
        ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k))) →
      ∀ m : ℕ, 1 ≤ m → ∃ K, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
        Summable (fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
        sob m (c t) ≤ sob m c₀ * (1 + Real.exp (K * t)) := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow_sobolev
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hall hmean0 hreal hdiv hsmall c hc0 hccont hcsum hcb hcdiv hceq m hm
  have hE : Summable fun l => ‖c₀ l‖ ^ 2 := by simpa using hall 0
  have hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2 := by simpa using hall 1
  obtain ⟨d, hd0, hdstruct, hdsum, hdcont, hdinteq, -, hdtrap, K, hK, hdsob⟩ :=
    hflow hν m hm hE hZ (hall m) hmean0 hreal hdiv hsmall
  have hag := flow_agree_Ici' hν hc0 hd0 hccont hdcont hcsum hdsum hcb
    (fun s hs => ⟨(hdtrap s hs).1, (hdtrap s hs).2.1⟩) hcdiv
    (fun s hs => (hdstruct s hs).2) hceq hdinteq
  refine ⟨K, hK, fun t ht => ?_⟩
  have hct : c t = d t := funext (hag t ht)
  rw [hct]
  exact hdsob t ht

/-- **The base window**: per-window Sobolev bounds at every level (with
mean-zero) put a flow in the window class (`tsum_weighted_norm_le_of_bound`
at level `p + 2`). -/
theorem windowL1_of_sobolev_all {c : ℝ → (Fin 3 → ℤ) → Vel} {b : ℝ}
    (hsob : ∀ m : ℕ, ∃ B : ℝ, ∀ t ∈ Icc (0:ℝ) b,
      (Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ∧
      (∑' l, ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) ≤ B)
    (hzero : ∀ t ∈ Icc (0:ℝ) b, c t 0 = 0) :
    WindowL1 0 b c := by
  intro p
  obtain ⟨B, hB⟩ := hsob (p + 2)
  refine ⟨(quarticKernel + B) / 2, fun t ht => ?_⟩
  exact ⟨summable_weighted_norm (hzero t ht) (hB t ht).1,
    tsum_weighted_norm_le_of_bound (hzero t ht) (hB t ht).1 (hB t ht).2⟩


/-! ## 7. The endpoint derivative of the mode ODE -/

/-- **The right derivative at `t = 0`** of a mode of the integral equation,
within `Ici 0`: the endpoint tool `hasDerivWithinAt_Ici_of_tendsto_deriv`
on `s := Ioo 0 T`, with differentiability inside from the converse FTC
(`hasDerivAt_of_integral_eq`), continuity at `0` from the primitive, and
the derivative limit from the continuity of the right-hand side. -/
theorem hasDerivWithinAt_mode_zero {ν : ℝ} {c : ℝ → (Fin 3 → ℤ) → Vel}
    {c₀ : (Fin 3 → ℤ) → Vel} {T : ℝ} (hT : 0 < T)
    (hinteq : ∀ t ∈ Icc (0:ℝ) T, ∀ k, c t k = c₀ k + ∫ s in (0:ℝ)..t,
      ((-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)))
    (hRHS : ∀ k, ContinuousOn (fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k
      + lerayProj k (convFull (c s) k)) (Icc (0:ℝ) T))
    (k : Fin 3 → ℤ) :
    HasDerivWithinAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c 0 k + lerayProj k (convFull (c 0) k)) (Ici (0:ℝ)) 0 := by
  set g : ℝ → Vel := fun s => (-(ν * ‖freq k‖ ^ 2)) • c s k + lerayProj k (convFull (c s) k)
    with hg
  have hgc : ContinuousOn g (Icc (0:ℝ) T) := hRHS k
  -- the integral equation in the shape of the converse FTC
  have hc00 : c 0 k = c₀ k := by
    have h := hinteq 0 ⟨le_rfl, hT.le⟩ k
    rwa [intervalIntegral.integral_same, add_zero] at h
  have hf : ∀ t ∈ Icc (0:ℝ) T, c t k = c 0 k + ∫ s in (0:ℝ)..t, g s := by
    intro t ht
    rw [hc00]
    exact hinteq t ht k
  have hd : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt (fun s => c s k) (g t) t :=
    hasDerivAt_of_integral_eq hgc hf
  -- continuity of the mode on the closed window, from the primitive
  have hprim : ContinuousOn (fun t => ∫ s in (0:ℝ)..t, g s) (Icc (0:ℝ) T) := by
    have hint : IntervalIntegrable g volume 0 T := hgc.intervalIntegrable_of_Icc hT.le
    have h := intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    rwa [uIcc_of_le hT.le] at h
  have hcont : ContinuousOn (fun s => c s k) (Icc (0:ℝ) T) :=
    (continuousOn_const.add hprim).congr hf
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 T) ?_ ?_ (Ioo_mem_nhdsGT hT) ?_
  · intro t ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · exact (hcont 0 ⟨le_rfl, hT.le⟩).mono Ioo_subset_Icc_self
  · have hlim : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      ((hgc 0 ⟨le_rfl, hT.le⟩).tendsto).mono_left
        (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self))
    refine hlim.congr' ?_
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hT) fun t ht => ((hd t ht).deriv).symm

/-! ## 8. The bilinear convection along a flow: continuity and derivative -/

/-- **Continuity of the bilinear convection** along two flows with
mode-wise continuity and summable window majorants (`continuousOn_tsum`).
The window may be empty, so absolute values of the majorants are used. -/
theorem continuousOn_convBil {a b : ℝ → (Fin 3 → ℤ) → Vel} {t₀ t₁ : ℝ}
    (ha : ∀ l, ContinuousOn (fun s => a s l) (Icc t₀ t₁))
    (hb : ∀ l, ContinuousOn (fun s => b s l) (Icc t₀ t₁))
    {A B : (Fin 3 → ℤ) → ℝ}
    (hAmaj : ∀ t ∈ Icc t₀ t₁, ∀ l, ‖a t l‖ ≤ A l)
    (hBmaj : ∀ t ∈ Icc t₀ t₁, ∀ l, ‖b t l‖ ≤ B l)
    (hA : Summable A) (hB1 : Summable fun l => ‖freq l‖ * B l) (k : Fin 3 → ℤ) :
    ContinuousOn (fun s => convBil (a s) (b s) k) (Icc t₀ t₁) := by
  have hAabs : Summable fun l => |A l| := hA.abs
  have hBabs : Summable fun l => ‖freq l‖ * |B l| :=
    hB1.abs.congr fun l => by rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨hu, -⟩ := conv_l1_summable_le' hAabs hBabs (fun _ => abs_nonneg _)
    (fun _ => by positivity) k
  have hbd : ∀ l, ∀ s ∈ Icc t₀ t₁,
      ‖(Complex.I * dotR (a s l) (freq (k - l))) • b s (k - l)‖
        ≤ |A l| * (‖freq (k - l)‖ * |B (k - l)|) := by
    intro l s hs
    exact (norm_convTerm_le _ _ _).trans (mul_le_mul ((hAmaj s hs l).trans (le_abs_self _))
      (mul_le_mul_of_nonneg_left ((hBmaj s hs _).trans (le_abs_self _)) (norm_nonneg _))
      (by positivity) (abs_nonneg _))
  show ContinuousOn (fun s => -(∑' l, (Complex.I * dotR (a s l) (freq (k - l))) • b s (k - l)))
    (Icc t₀ t₁)
  refine ContinuousOn.neg (continuousOn_tsum (fun l => ?_) hu hbd)
  exact (continuousOn_const.mul ((dotR_continuous (freq (k - l))).comp_continuousOn (ha l))).smul
    (hb (k - l))

/-- **The time-derivative of the bilinear convection** along two
differentiable coefficient flows, on an open window carrying summable
majorants: the product rule term by term (the `dotR` pairing differentiates
through `EuclideanSpace.proj … restrictScalars ℝ`), then
`hasDerivAt_tsum_of_isPreconnected` on `Ioo t₀ t₁`, and the derivative sum
splits into the two half-convections.  At `a = b` this is the
time-derivative of `convFull` the campaign did not previously have. -/
theorem hasDerivAt_convBil_flow {a a' b b' : ℝ → (Fin 3 → ℤ) → Vel} {t₀ t₁ : ℝ}
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
    HasDerivAt (fun s => convBil (a s) (b s) k)
      (convBil (a t) (b' t) k + convBil (a' t) (b t) k) t := by
  -- the window is inhabited by `t`, so the majorants are nonnegative
  have hAnn : ∀ l, 0 ≤ A l := fun l => (norm_nonneg _).trans (hAmaj t ht l)
  have hA'nn : ∀ l, 0 ≤ A' l := fun l => (norm_nonneg _).trans (hA'maj t ht l)
  have hBnn : ∀ l, 0 ≤ ‖freq l‖ * B l := fun l =>
    mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hBmaj t ht l))
  have hB'nn : ∀ l, 0 ≤ ‖freq l‖ * B' l := fun l =>
    mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hB'maj t ht l))
  -- one convolution term, for any pair of factors dominated on the window
  have hterm : ∀ (x y : ℝ → (Fin 3 → ℤ) → Vel) (X Y : (Fin 3 → ℤ) → ℝ),
      (∀ s ∈ Ioo t₀ t₁, ∀ l, ‖x s l‖ ≤ X l) → (∀ s ∈ Ioo t₀ t₁, ∀ l, ‖y s l‖ ≤ Y l) →
      (∀ l, 0 ≤ X l) →
      ∀ s ∈ Ioo t₀ t₁, ∀ l, ‖(Complex.I * dotR (x s l) (freq (k - l))) • y s (k - l)‖
        ≤ X l * (‖freq (k - l)‖ * Y (k - l)) := by
    intro x y X Y hx hy hXnn s hs l
    exact (norm_convTerm_le _ _ _).trans (mul_le_mul (hx s hs l)
      (mul_le_mul_of_nonneg_left (hy s hs _) (norm_nonneg _)) (by positivity) (hXnn l))
  obtain ⟨hu1, -⟩ := conv_l1_summable_le' hA hB'1 hAnn hB'nn k
  obtain ⟨hu2, -⟩ := conv_l1_summable_le' hA' hB1 hA'nn hBnn k
  obtain ⟨hu0, -⟩ := conv_l1_summable_le' hA hB1 hAnn hBnn k
  -- term-wise derivatives on the window: the product rule
  have hderiv : ∀ l, ∀ s ∈ Ioo t₀ t₁,
      HasDerivAt (fun z => (Complex.I * dotR (a z l) (freq (k - l))) • b z (k - l))
        ((Complex.I * dotR (a s l) (freq (k - l))) • b' s (k - l)
          + (Complex.I * dotR (a' s l) (freq (k - l))) • b s (k - l)) s := by
    intro l s hs
    have hcomp : ∀ j : Fin 3, HasDerivAt (fun z => (a z l) j) ((a' s l) j) s := fun j =>
      ((EuclideanSpace.proj (𝕜 := ℂ) j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        (ha s hs l)
    have hd : HasDerivAt (fun z => dotR (a z l) (freq (k - l)))
        (dotR (a' s l) (freq (k - l))) s := by
      unfold dotR
      exact HasDerivAt.fun_sum fun j _ => (hcomp j).mul_const _
    exact (hd.const_mul Complex.I).smul (hb s hs (k - l))
  -- the derivative family is dominated on the window
  have hbound : ∀ l, ∀ s ∈ Ioo t₀ t₁,
      ‖(Complex.I * dotR (a s l) (freq (k - l))) • b' s (k - l)
          + (Complex.I * dotR (a' s l) (freq (k - l))) • b s (k - l)‖
        ≤ A l * (‖freq (k - l)‖ * B' (k - l)) + A' l * (‖freq (k - l)‖ * B (k - l)) :=
    fun l s hs => (norm_add_le _ _).trans (add_le_add
      (hterm a b' A B' hAmaj hB'maj hAnn s hs l) (hterm a' b A' B hA'maj hBmaj hA'nn s hs l))
  -- the series converges at `t`
  have hg0 : Summable fun l => (Complex.I * dotR (a t l) (freq (k - l))) • b t (k - l) :=
    Summable.of_norm (hu0.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun l => hterm a b A B hAmaj hBmaj hAnn t ht l)
  have hsum := hasDerivAt_tsum_of_isPreconnected (hu1.add hu2) isOpen_Ioo isPreconnected_Ioo
    hderiv hbound ht hg0 ht
  -- identify the derivative with the two half-convections
  have h1 : Summable fun l => (Complex.I * dotR (a t l) (freq (k - l))) • b' t (k - l) :=
    Summable.of_norm (hu1.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun l => hterm a b' A B' hAmaj hB'maj hAnn t ht l)
  have h2 : Summable fun l => (Complex.I * dotR (a' t l) (freq (k - l))) • b t (k - l) :=
    Summable.of_norm (hu2.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun l => hterm a' b A' B hA'maj hBmaj hA'nn t ht l)
  have hid : -(∑' l, ((Complex.I * dotR (a t l) (freq (k - l))) • b' t (k - l)
        + (Complex.I * dotR (a' t l) (freq (k - l))) • b t (k - l)))
      = convBil (a t) (b' t) k + convBil (a' t) (b t) k := by
    rw [h1.tsum_add h2, neg_add]
    rfl
  exact hsum.neg.congr_deriv hid

/-! ## 9. Reading a derivative chain as `C^∞` -/

/-- A chain of derivatives on an open set is `C^∞` there
(`contDiffOn_succ_iff_derivWithin` with `IsOpen.uniqueDiffOn`). -/
theorem contDiffOn_infty_of_hasDerivAt_chain {s : Set ℝ} (hs : IsOpen s)
    {g : ℕ → ℝ → Vel}
    (hchain : ∀ i, ∀ t ∈ s, HasDerivAt (g i) (g (i + 1) t) t) :
    ContDiffOn ℝ ∞ (g 0) s := by
  have hdw : ∀ i, ∀ t ∈ s, HasDerivWithinAt (g i) (g (i + 1) t) s t :=
    fun i t ht => (hchain i t ht).hasDerivWithinAt
  have hderiv : ∀ i, ∀ t ∈ s, derivWithin (g i) s t = g (i + 1) t :=
    fun i t ht => (hdw i t ht).derivWithin (hs.uniqueDiffOn t ht)
  have hcont : ∀ i, ContinuousOn (g i) s :=
    fun i t ht => (hchain i t ht).continuousAt.continuousWithinAt
  have key : ∀ n : ℕ, ∀ i, ContDiffOn ℝ n (g i) s := by
    intro n
    induction n with
    | zero => intro i; exact contDiffOn_zero.mpr (hcont i)
    | succ n ih =>
      intro i
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
      refine ⟨fun t ht => (hdw i t ht).differentiableWithinAt, ?_, ?_⟩
      · intro h; exact absurd h (by simp)
      · exact (ih (i + 1)).congr (hderiv i)
  exact contDiffOn_infty.mpr fun n => key n 0

/-- A chain of derivatives on `Ioi 0`, with right derivatives at `0` within
`Ici 0` and continuity on `Ici 0`, is `C^∞` on the CLOSED half-line
(`contDiffOn_succ_iff_derivWithin` with `uniqueDiffOn_Ici`). -/
theorem contDiffOn_infty_Ici_of_chain {g : ℕ → ℝ → Vel}
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

/-! ## 10. The Leibniz step -/

/-- The Leibniz reindexing on the antidiagonal (non-frozen helper):
`Σ_{i+j=n+1} C(n+1,i)·f i j = Σ_{i+j=n} C(n,i)·(f i (j+1) + f (i+1) j)`. -/
theorem leibniz_reindex (f : ℕ → ℕ → Vel) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal (n + 1), (n + 1).choose ij.1 • f ij.1 ij.2) =
      ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 • (f ij.1 (ij.2 + 1) + f (ij.1 + 1) ij.2) := by
  rw [Finset.sum_antidiagonal_choose_succ_nsmul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [smul_add, ← Nat.choose_symm_of_eq_add hij.symm]

/-- **The Leibniz step, sibling form** (non-frozen): the derivative of the
`n`-th Leibniz convection sum needs the derivatives of the chain only up to
order `n` (windows up to `n + 1`).  This is the form the chain induction
runs on; the frozen `hasDerivAt_leibnizSum` is its weakening. -/
theorem hasDerivAt_leibnizSum' {D : ℕ → ℝ → (Fin 3 → ℤ) → Vel} (n : ℕ)
    (hchain : ∀ i, i ≤ n → ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => D i s k) (D (i + 1) t k) t)
    (hwin : ∀ i, i ≤ n + 1 → ∀ b : ℝ, WindowL1 0 b (D i))
    {t : ℝ} (ht : t ∈ Ioi (0:ℝ)) (k : Fin 3 → ℤ) :
    HasDerivAt
      (fun s => ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • convBil (D ij.1 s) (D ij.2 s) k)
      (∑ ij ∈ Finset.antidiagonal (n + 1),
        (n + 1).choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k) t := by
  have ht' : t ∈ Ioo (0:ℝ) (t + 1) := ⟨ht, lt_add_one t⟩
  -- majorants of every chain element up to `n + 1` on the window `Ioo 0 (t+1)`
  have hmaj : ∀ i, i ≤ n + 1 → ∃ A : (Fin 3 → ℤ) → ℝ, Summable A ∧
      (Summable fun l => ‖freq l‖ * A l) ∧
      ∀ s ∈ Ioo (0:ℝ) (t + 1), ∀ l, ‖D i s l‖ ≤ A l := by
    intro i hi
    obtain ⟨A, hA, hA1, hAm⟩ := WindowL1.majorant (hwin i hi (t + 1))
    exact ⟨A, hA, hA1, fun s hs l => hAm s (Ioo_subset_Icc_self hs) l⟩
  have hterm : ∀ ij ∈ Finset.antidiagonal n,
      HasDerivAt (fun s => n.choose ij.1 • convBil (D ij.1 s) (D ij.2 s) k)
        (n.choose ij.1 • (convBil (D ij.1 t) (D (ij.2 + 1) t) k
          + convBil (D (ij.1 + 1) t) (D ij.2 t) k)) t := by
    intro ij hij
    have hi : ij.1 ≤ n := Finset.antidiagonal.fst_le hij
    have hj : ij.2 ≤ n := Finset.antidiagonal.snd_le hij
    obtain ⟨A, hA, -, hAm⟩ := hmaj ij.1 (Nat.le_succ_of_le hi)
    obtain ⟨A', hA', -, hA'm⟩ := hmaj (ij.1 + 1) (Nat.succ_le_succ hi)
    obtain ⟨B, -, hB1, hBm⟩ := hmaj ij.2 (Nat.le_succ_of_le hj)
    obtain ⟨B', -, hB'1, hB'm⟩ := hmaj (ij.2 + 1) (Nat.succ_le_succ hj)
    refine HasDerivAt.const_smul (n.choose ij.1) ?_
    exact hasDerivAt_convBil_flow
      (fun s hs l => hchain ij.1 hi s (Ioo_subset_Ioi_self hs) l)
      (fun s hs l => hchain ij.2 hj s (Ioo_subset_Ioi_self hs) l)
      hAm hA'm hBm hB'm hA hA' hB1 hB'1 ht' k
  refine (HasDerivAt.fun_sum hterm).congr_deriv ?_
  exact (leibniz_reindex (fun i j => convBil (D i t) (D j t) k) n).symm

/-- **The Leibniz step** (frozen form, derivative hypotheses up to `n + 1`;
the weakening of `hasDerivAt_leibnizSum'`).  One generic lemma for both the
velocity chain and, in the next wave, the pressure chain. -/
theorem hasDerivAt_leibnizSum {D : ℕ → ℝ → (Fin 3 → ℤ) → Vel} (n : ℕ)
    (hchain : ∀ i, i ≤ n + 1 → ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => D i s k) (D (i + 1) t k) t)
    (hwin : ∀ i, i ≤ n + 1 → ∀ b : ℝ, WindowL1 0 b (D i))
    {t : ℝ} (ht : t ∈ Ioi (0:ℝ)) (k : Fin 3 → ℤ) :
    HasDerivAt
      (fun s => ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • convBil (D ij.1 s) (D ij.2 s) k)
      (∑ ij ∈ Finset.antidiagonal (n + 1),
        (n + 1).choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k) t :=
  hasDerivAt_leibnizSum' n (fun i hi => hchain i (Nat.le_succ_of_le hi)) hwin ht k


/-! ## 11. The chain -/

/-- Continuity on `Ici 0` from continuity on every closed window `Icc 0 b`
(non-frozen helper; `Icc 0 (t+1)` is a `𝓝[Ici 0] t`-neighbourhood). -/
theorem continuousOn_Ici_of_Icc {f : ℝ → Vel} (h : ∀ b : ℝ, ContinuousOn f (Icc 0 b)) :
    ContinuousOn f (Ici (0:ℝ)) := by
  intro t ht
  have hmem : Icc (0:ℝ) (t + 1) ∈ 𝓝[Ici (0:ℝ)] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (lt_add_one t))
  exact (h (t + 1) t ⟨ht, (lt_add_one t).le⟩).mono_of_mem_nhdsWithin hmem

/-- The time-derivative chain of a coefficient flow (non-frozen encoding;
the capstone exports it existentially): `nsChain ν c 0 = c`, and
`nsChain ν c (n+1) t k = -ν‖k‖²·nsChain ν c n t k + P_k (Σ_{i+j=n} C(n,i)·convBil (D i t) (D j t) k)`,
by well-founded recursion over the attached antidiagonal. -/
noncomputable def nsChain (ν : ℝ) (c : ℝ → (Fin 3 → ℤ) → Vel) :
    ℕ → ℝ → (Fin 3 → ℤ) → Vel
  | 0 => c
  | n + 1 => fun t k =>
      (-(ν * ‖freq k‖ ^ 2)) • nsChain ν c n t k
        + lerayProj k (∑ ij ∈ (Finset.antidiagonal n).attach,
            n.choose ij.1.1 • convBil (nsChain ν c ij.1.1 t) (nsChain ν c ij.1.2 t) k)
  decreasing_by
    all_goals simp_wf
    · exact Finset.antidiagonal.fst_le ij.2
    · exact Finset.antidiagonal.snd_le ij.2

/-- The Leibniz convection sum of the chain (non-frozen). -/
noncomputable def nsLeib (ν : ℝ) (c : ℝ → (Fin 3 → ℤ) → Vel) (n : ℕ) (t : ℝ)
    (k : Fin 3 → ℤ) : Vel :=
  ∑ ij ∈ Finset.antidiagonal n,
    n.choose ij.1 • convBil (nsChain ν c ij.1 t) (nsChain ν c ij.2 t) k

theorem nsChain_zero (ν : ℝ) (c : ℝ → (Fin 3 → ℤ) → Vel) : nsChain ν c 0 = c := by
  rw [nsChain]

theorem nsChain_succ (ν : ℝ) (c : ℝ → (Fin 3 → ℤ) → Vel) (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ) :
    nsChain ν c (n + 1) t k =
      (-(ν * ‖freq k‖ ^ 2)) • nsChain ν c n t k + lerayProj k (nsLeib ν c n t k) := by
  rw [nsChain]
  dsimp only
  rw [Finset.sum_attach (Finset.antidiagonal n)
    (fun ij => n.choose ij.1 • convBil (nsChain ν c ij.1 t) (nsChain ν c ij.2 t) k)]
  rfl

theorem nsChain_succ_fun (ν : ℝ) (c : ℝ → (Fin 3 → ℤ) → Vel) (n : ℕ) (k : Fin 3 → ℤ) :
    (fun s => nsChain ν c (n + 1) s k) =
      fun s => (-(ν * ‖freq k‖ ^ 2)) • nsChain ν c n s k + lerayProj k (nsLeib ν c n s k) :=
  funext fun s => nsChain_succ ν c n s k

theorem nsLeib_zero (ν : ℝ) (c : ℝ → (Fin 3 → ℤ) → Vel) (t : ℝ) (k : Fin 3 → ℤ) :
    nsLeib ν c 0 t k = convBil (c t) (c t) k := by
  unfold nsLeib
  simp only [Finset.antidiagonal_zero, Finset.sum_singleton, Nat.choose_self, one_smul,
    nsChain_zero]

/-- **The chain package** (non-frozen).  From the base flow's continuity on
`Ici 0`, its mode ODE on `Ioi 0` and its membership in every window class:
every chain element and every Leibniz sum carries the window, derivative,
continuity and endpoint clauses of the capstone.  Order of the induction:
windows first (recurrence and closure, no derivatives), then derivatives on
`Ioi 0` (the sibling Leibniz step), then continuity on `Ici 0`, then the
endpoint derivative by the endpoint tool. -/
theorem nsChain_package (ν : ℝ) {c : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => c s k) (Ici (0:ℝ)))
    (hode : ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => c s k)
      ((-(ν * ‖freq k‖ ^ 2)) • c t k + lerayProj k (convFull (c t) k)) t)
    (hwin0 : ∀ b : ℝ, WindowL1 0 b c) :
    (∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (nsChain ν c n)) ∧
    (∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (nsLeib ν c n)) ∧
    (∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => nsChain ν c n s k) (nsChain ν c (n + 1) t k) t) ∧
    (∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => nsLeib ν c n s k) (nsLeib ν c (n + 1) t k) t) ∧
    (∀ n : ℕ, ∀ k, ContinuousOn (fun s => nsChain ν c n s k) (Ici (0:ℝ))) ∧
    (∀ n : ℕ, ∀ k, ContinuousOn (fun s => nsLeib ν c n s k) (Ici (0:ℝ))) ∧
    (∀ n : ℕ, ∀ k,
      HasDerivWithinAt (fun s => nsChain ν c n s k) (nsChain ν c (n + 1) 0 k)
        (Ici (0:ℝ)) 0) := by
  -- (i) windows: the Leibniz sum from the chain elements up to `n`
  have hwinLeib : ∀ n : ℕ, (∀ i, i ≤ n → ∀ b : ℝ, WindowL1 0 b (nsChain ν c i)) →
      ∀ b : ℝ, WindowL1 0 b (nsLeib ν c n) := by
    intro n hD b
    show WindowL1 0 b (fun t k => ∑ ij ∈ Finset.antidiagonal n,
      n.choose ij.1 • convBil (nsChain ν c ij.1 t) (nsChain ν c ij.2 t) k)
    refine WindowL1.finset_sum (Finset.antidiagonal n)
      (fun ij t k => n.choose ij.1 • convBil (nsChain ν c ij.1 t) (nsChain ν c ij.2 t) k)
      (fun ij hij => ?_)
    exact WindowL1.nsmul _ (WindowL1.convBil (hD ij.1 (Finset.antidiagonal.fst_le hij) b)
      (hD ij.2 (Finset.antidiagonal.snd_le hij) b))
  -- windows of every chain element, all orders at once
  have hwinAll : ∀ n : ℕ, ∀ i, i ≤ n → ∀ b : ℝ, WindowL1 0 b (nsChain ν c i) := by
    intro n
    induction n with
    | zero =>
      intro i hi b
      rw [Nat.le_zero.mp hi, nsChain_zero]
      exact hwin0 b
    | succ n ih =>
      intro i hi b
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact ih i (Nat.lt_succ_iff.mp h) b
      · rw [le_antisymm hi h]
        have e : nsChain ν c (n + 1) = fun t k =>
            (-(ν * ‖freq k‖ ^ 2)) • nsChain ν c n t k + lerayProj k (nsLeib ν c n t k) :=
          funext fun t => funext fun k => nsChain_succ ν c n t k
        rw [e]
        exact WindowL1.add (WindowL1.visc ν (ih n le_rfl b))
          (WindowL1.lerayProj (hwinLeib n ih b))
  have hDall : ∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (nsChain ν c n) := fun n => hwinAll n n le_rfl
  have hwinL : ∀ n : ℕ, ∀ b : ℝ, WindowL1 0 b (nsLeib ν c n) :=
    fun n => hwinLeib n (fun i _ => hDall i)
  -- (ii) derivatives on `Ioi 0`
  have hderAll : ∀ n : ℕ, ∀ i, i ≤ n → ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => nsChain ν c i s k) (nsChain ν c (i + 1) t k) t := by
    intro n
    induction n with
    | zero =>
      intro i hi t ht k
      rw [Nat.le_zero.mp hi, nsChain_succ, nsLeib_zero, convBil_self, nsChain_zero]
      exact hode t ht k
    | succ n ih =>
      intro i hi t ht k
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact ih i (Nat.lt_succ_iff.mp h) t ht k
      · rw [le_antisymm hi h, nsChain_succ_fun ν c n k, nsChain_succ ν c (n + 1) t k]
        refine HasDerivAt.add ?_ (HasDerivAt.lerayProj k ?_)
        · exact (ih n le_rfl t ht k).const_smul (-(ν * ‖freq k‖ ^ 2))
        · exact hasDerivAt_leibnizSum' n (fun j hj => ih j hj) (fun j _ => hDall j) ht k
  have hDder : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k,
      HasDerivAt (fun s => nsChain ν c n s k) (nsChain ν c (n + 1) t k) t :=
    fun n => hderAll n n le_rfl
  -- (iii) continuity on `Ici 0`: the Leibniz sum from the chain elements up to `n`
  have hcontLeib : ∀ n : ℕ,
      (∀ i, i ≤ n → ∀ k, ContinuousOn (fun s => nsChain ν c i s k) (Ici (0:ℝ))) →
      ∀ k, ContinuousOn (fun s => nsLeib ν c n s k) (Ici (0:ℝ)) := by
    intro n hD k
    refine continuousOn_Ici_of_Icc fun b => ?_
    show ContinuousOn (fun s => ∑ ij ∈ Finset.antidiagonal n,
      n.choose ij.1 • convBil (nsChain ν c ij.1 s) (nsChain ν c ij.2 s) k) (Icc 0 b)
    refine continuousOn_finsetSum _ fun ij hij => ?_
    refine ContinuousOn.const_smul ?_ (n.choose ij.1)
    obtain ⟨A, hA, -, hAm⟩ := WindowL1.majorant (hDall ij.1 b)
    obtain ⟨B, -, hB1, hBm⟩ := WindowL1.majorant (hDall ij.2 b)
    exact continuousOn_convBil
      (fun l => (hD ij.1 (Finset.antidiagonal.fst_le hij) l).mono Icc_subset_Ici_self)
      (fun l => (hD ij.2 (Finset.antidiagonal.snd_le hij) l).mono Icc_subset_Ici_self)
      hAm hBm hA hB1 k
  have hcontAll : ∀ n : ℕ, ∀ i, i ≤ n → ∀ k,
      ContinuousOn (fun s => nsChain ν c i s k) (Ici (0:ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro i hi k
      rw [Nat.le_zero.mp hi, nsChain_zero]
      exact hcont k
    | succ n ih =>
      intro i hi k
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact ih i (Nat.lt_succ_iff.mp h) k
      · rw [le_antisymm hi h, nsChain_succ_fun ν c n k]
        exact ((ih n le_rfl k).const_smul _).add
          ((lerayProj_continuous k).comp_continuousOn (hcontLeib n ih k))
  have hDcont : ∀ n : ℕ, ∀ k, ContinuousOn (fun s => nsChain ν c n s k) (Ici (0:ℝ)) :=
    fun n => hcontAll n n le_rfl
  -- (iv) the endpoint derivative at `0`, by the endpoint tool
  have hzero : ∀ n : ℕ, ∀ k,
      HasDerivWithinAt (fun s => nsChain ν c n s k) (nsChain ν c (n + 1) 0 k) (Ici (0:ℝ)) 0 := by
    intro n k
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0) ?_ ?_ self_mem_nhdsWithin ?_
    · intro t ht
      exact (hDder n t ht k).differentiableAt.differentiableWithinAt
    · exact (hDcont n k 0 self_mem_Ici).mono Ioi_subset_Ici_self
    · have hlim : Tendsto (fun s => nsChain ν c (n + 1) s k) (𝓝[>] 0)
          (𝓝 (nsChain ν c (n + 1) 0 k)) :=
        ((hDcont (n + 1) k 0 self_mem_Ici).tendsto).mono_left
          (nhdsWithin_mono _ Ioi_subset_Ici_self)
      refine hlim.congr' ?_
      exact eventually_nhdsWithin_of_forall fun t ht => ((hDder n t ht k).deriv).symm
  exact ⟨hDall, hwinL, hDder,
    fun n t ht k => hasDerivAt_leibnizSum' n (fun i _ => hDder i) (fun i _ => hDall i) ht k,
    hDcont, fun n => hcontLeib n (fun i _ => hDcont i), hzero⟩

/-! ## 12. The capstone -/

/-- **Theorem B, time-smooth.**  The flow of `theorem_B_smooth_classical_eq`
(all twenty of its clauses re-exported verbatim; the trap clause at the
combined `κ`) carries a time-derivative chain `D` with its Leibniz
convection sums `S` (clause 21: `D 0 = c`, `S` defined from `D`, the
recurrence `D (n+1) = -ν‖k‖²·D n + P_k (S n)` on `Ici 0`, derivatives on
`Ioi 0`, right derivatives at `0` within `Ici 0`, continuity on `Ici 0`, and
every window class, for `D n` and for `S n`), and every mode of the flow is
`C^∞` in time on the closed half-line (clause 22).  `∞` is `(⊤ : ℕ∞)`, not
`ω`: no analyticity is claimed.

`κ` is the maximum of the classical layer's and `sobolev_growth_all_m`'s
constants, both of explicit form and exported as compiled existentials; the
window constants of the chain are untracked existentials produced by the
Leibniz induction. -/
theorem theorem_B_time_smooth :
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
        (∀ k, ContDiffOn ℝ ∞ (fun s => c s k) (Ici (0:ℝ))) := by
  obtain ⟨κ₁, hκ₁, H⟩ := theorem_B_smooth_classical_eq
  obtain ⟨κ₂, hκ₂, G⟩ := sobolev_growth_all_m
  refine ⟨max κ₁ κ₂, lt_of_lt_of_le hκ₁ (le_max_left _ _), ?_⟩
  intro ν hν c₀ hall hmean0 hreal hdiv hsmall
  have hE0 : 0 ≤ en c₀ := tsum_nonneg fun _ => sq_nonneg _
  have hZ0 : 0 ≤ ens c₀ := tsum_nonneg fun _ => by positivity
  have hsmall₁ : κ₁ * en c₀ * ens c₀ < ν ^ 4 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left κ₁ κ₂) hE0) hZ0) hsmall
  have hsmall₂ : κ₂ * en c₀ * ens c₀ < ν ^ 4 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right κ₁ κ₂) hE0) hZ0) hsmall
  -- the twenty clauses of the classical equation, one flow
  obtain ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, hclassical⟩ :=
    H hν hall hmean0 hreal hdiv hsmall₁
  -- the trap clause at the combined κ
  have hκnn : 0 ≤ max κ₁ κ₂ := le_trans hκ₁.le (le_max_left _ _)
  have htrap' : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ ∧
      max κ₁ κ₂ * en (c t) * ens (c t) < ν ^ 4 := by
    intro t ht
    refine ⟨(htrap t ht).1, (htrap t ht).2.1, lt_of_le_of_lt ?_ hsmall⟩
    have hZt : 0 ≤ ens (c t) := tsum_nonneg fun _ => by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left (htrap t ht).1 hκnn) (htrap t ht).2.1 hZt
      (mul_nonneg hκnn hE0)
  -- every Sobolev level grows at most exponentially, for THIS flow
  have hgrow := G hν hall hmean0 hreal hdiv hsmall₂ hc0 hcont hsum
    (fun t ht => ⟨(htrap t ht).1, (htrap t ht).2.1⟩) (fun t ht => (hstruct t ht).2) hinteq
  -- the base window class on every closed window `[0, b]`
  have hwin0 : ∀ b : ℝ, WindowL1 0 b c := by
    intro b
    refine windowL1_of_sobolev_all (fun m => ?_) (fun t ht => hmean t ht.1)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨en c₀, fun t ht => ⟨hlevel 0 t ht.1, ?_⟩⟩
      have e : (∑' l, ‖freq l‖ ^ (2 * 0) * ‖c t l‖ ^ 2) = sob 0 (c t) := rfl
      rw [e, sob_zero_eq_en]
      exact (htrap t ht.1).1
    · obtain ⟨K, hK, hsob⟩ := hgrow m hm
      refine ⟨sob m c₀ * (1 + Real.exp (K * b)), fun t ht => ⟨(hsob t ht.1).1, ?_⟩⟩
      have e : (∑' l, ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2) = sob m (c t) := rfl
      rw [e]
      refine (hsob t ht.1).2.trans ?_
      have hs0 : 0 ≤ sob m c₀ := tsum_nonneg fun _ => by positivity
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK.le))) hs0
  -- the chain
  obtain ⟨hDwin, hSwin, hDder, hSder, hDcont, hScont, hDzero⟩ :=
    nsChain_package ν hcont hode hwin0
  refine ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap', hlevel, hmean, hl1,
    hspace, hper, htime, htimecont, hsecond, hcalib, hpress, hleray, hnl, hclassical, ?_, ?_⟩
  · -- 21. the chain, with the Leibniz sums
    exact ⟨nsChain ν c, nsLeib ν c, nsChain_zero ν c, fun n t k => rfl,
      fun n t _ k => nsChain_succ ν c n t k, hDder, hDzero, hDcont, hDwin, hSder, hScont, hSwin⟩
  · -- 22. every mode is C^∞ in time on `Ici 0`
    intro k
    have h : ContDiffOn ℝ ∞ (fun s => nsChain ν c 0 s k) (Ici (0:ℝ)) :=
      contDiffOn_infty_Ici_of_chain (g := fun i s => nsChain ν c i s k)
        (fun i t ht => hDder i t ht k) (fun i => hDzero i k) (fun i => hDcont i k)
    rw [nsChain_zero] at h
    exact h

/-! ## 7. Audit probes: the chain of clause 21 is pinned

Register entry CHAIN PINNED of the blueprint (section 6b), compiled in the
tree.  The `∃ D S` of clause 21 is not a free existential: `D 0 = c` and the
derivative clauses determine `D` on `Ioi 0` (`chain_unique`), the
continuity clauses extend the agreement to `Ici 0` (`chain_unique_Ici`),
and `S` is determined by `D` through its defining clause
(`clause21_pinned`).  Proofs by the W1 statement-shape reader, landed
verbatim. -/

/-- Two derivative chains with the same base agree at every order on `t > 0`
(induction on the order; `HasDerivAt.unique` after transporting the
derivative along the eventual equality on `Ioi 0`). -/
theorem chain_unique {D E : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    (h0 : D 0 = E 0)
    (hD : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => D n s k) (D (n + 1) t k) t)
    (hE : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => E n s k) (E (n + 1) t k) t) :
    ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, D n t k = E n t k := by
  intro n
  induction n with
  | zero => intro t _ k; rw [h0]
  | succ n ih =>
    intro t ht k
    have heq : (fun s => D n s k) =ᶠ[𝓝 t] (fun s => E n s k) :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => ih s hs k
    exact (hD n t ht k).unique ((hE n t ht k).congr_of_eventuallyEq heq)

/-- With the continuity clauses the agreement extends to `t = 0` (limits within
`Ici 0` along `𝓝[>] 0`, which is `NeBot`). -/
theorem chain_unique_Ici {D E : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    (h0 : D 0 = E 0)
    (hD : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => D n s k) (D (n + 1) t k) t)
    (hE : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => E n s k) (E (n + 1) t k) t)
    (hDc : ∀ n : ℕ, ∀ k, ContinuousOn (fun s => D n s k) (Ici (0:ℝ)))
    (hEc : ∀ n : ℕ, ∀ k, ContinuousOn (fun s => E n s k) (Ici (0:ℝ))) :
    ∀ n : ℕ, ∀ t ∈ Ici (0:ℝ), ∀ k, D n t k = E n t k := by
  intro n t ht k
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with h | h
  · subst h
    have hDt : Tendsto (fun s => D n s k) (𝓝[>] 0) (𝓝 (D n 0 k)) :=
      ((hDc n k 0 self_mem_Ici).tendsto).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hEt : Tendsto (fun s => E n s k) (𝓝[>] 0) (𝓝 (E n 0 k)) :=
      ((hEc n k 0 self_mem_Ici).tendsto).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    exact tendsto_nhds_unique_of_eventuallyEq hDt hEt
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun s hs => chain_unique h0 hD hE n s hs k)
  · exact chain_unique h0 hD hE n t h k

/-- Clause 21 of `theorem_B_time_smooth` admits at most one `D` on `Ici 0` for a
given flow `c`, and `S` is determined by `D` (its defining clause).  Only the
`D 0 = c`, `S`-definition, derivative and continuity clauses are used. -/
theorem clause21_pinned {c : ℝ → (Fin 3 → ℤ) → Vel}
    {D S D' S' : ℕ → ℝ → (Fin 3 → ℤ) → Vel}
    (hD0 : D 0 = c) (hD'0 : D' 0 = c)
    (hS : ∀ (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ),
      S n t k = ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • convBil (D ij.1 t) (D ij.2 t) k)
    (hS' : ∀ (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ),
      S' n t k = ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • convBil (D' ij.1 t) (D' ij.2 t) k)
    (hDd : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => D n s k) (D (n + 1) t k) t)
    (hD'd : ∀ n : ℕ, ∀ t ∈ Ioi (0:ℝ), ∀ k, HasDerivAt (fun s => D' n s k) (D' (n + 1) t k) t)
    (hDc : ∀ n : ℕ, ∀ k, ContinuousOn (fun s => D n s k) (Ici (0:ℝ)))
    (hD'c : ∀ n : ℕ, ∀ k, ContinuousOn (fun s => D' n s k) (Ici (0:ℝ))) :
    (∀ n : ℕ, ∀ t ∈ Ici (0:ℝ), ∀ k, D n t k = D' n t k) ∧
    (∀ n : ℕ, ∀ t ∈ Ici (0:ℝ), ∀ k, S n t k = S' n t k) := by
  have hpin := chain_unique_Ici (hD0.trans hD'0.symm) hDd hD'd hDc hD'c
  refine ⟨hpin, fun n t ht k => ?_⟩
  have hfun : ∀ i, D i t = D' i t := fun i => funext (hpin i t ht)
  rw [hS, hS']
  exact Finset.sum_congr rfl fun ij _ => by rw [hfun ij.1, hfun ij.2]

end TheoremB
