# Rung 6 — Tier 4 blueprint: uniqueness and the eternal flow

Status: route FIXED by the t4-recon fleet (28 Aug 2026); this document records
the frozen design. Contract unchanged: kernel + gate judge; statements freeze
at declaration; adversarial audit before every tag.

## The result

**`theorem_B_unique`**: uniqueness for the full NS coefficient system,
UNCONDITIONAL within the honest class — no smallness, no dissipation
hypothesis, no reality needed. The class 𝒰(ν, T, c₀, E, Z):

  (i)   c 0 = c₀;
  (ii)  ∀ k, ContinuousOn (fun t => c t k) (Icc 0 T)   [keeps the integral
        equation honest — bars junk-integral members];
  (iii) ∀ t ∈ Icc, Summable en- and ens-families, en (c t) ≤ E,
        ens (c t) ≤ Z;
  (iv)  ∀ t ∈ Icc, DivFree (c t);
  (v)   the convFull integral equation ∀ t ∈ Icc, ∀ k.

Any two members (even with different budgets — take maxima) agree on
Icc 0 T. Then **`ns_full_global_flow`**: one eternal flow serving every
horizon (M5-splice pattern powered by the new uniqueness; leray-hopf-style
diagonal extraction recorded as fallback — they built a global curve without
uniqueness, and uniqueness only upgrades it to THE curve).

## Why the two obstacles dissolve

1. **Differentiating en(d t) (an infinite sum)**: never done. Only finite
   sections φ_F = Σ_{k∈F}‖d_k‖² are differentiated (house pattern). The
   Grönwall runs with TAIL SOURCES, and the sources die in the F↑ limit by
   dominated convergence — the pointwise vanishing of the enstrophy tail at
   each time is exactly what theorem_B's EXPORTED Summable clause provides
   (the clause the Tier-3 audit forced; it now carries Tier 4).
2. **The box-free pairing**: no triMaj (its ℓ¹ slot needs spec1/dissipation
   — unavailable in the class), no naive ℓ² (provably fails in 3D). Instead
   a weighted convolution bound at interpolation exponent 7/8 ∈ (3/4, 1):
   the window where 4s > 3 makes the lattice kernel Σ‖k‖^{−7/2} summable
   AND s < 1 leaves an en(d)-power for Young absorption.

## The estimate chain (frozen)

d := c¹ − c², x_k := ‖d_k‖; d₀ = 0, zero mode ≡ 0, DivFree, en(d) ≤ 4E,
ens(d) ≤ 4Z.

- S2: φ_F' = −2ν·ens_F(d) + 2Σ_{k∈F}⟪convDiff k, d_k⟫ — the Leray
  projector DROPS against div-free d_k (L6), no lost factor.
- S3–S4: pairing ≤ T_A + T_B; reindex m = k−l:
  T_A = Σ'_m e_m·C_m (e_m = ‖freq m‖‖c¹_m‖, C_m = Σ_{k∈F} x_k x_{k−m}),
  T_B = Σ'_m g_m·D_m (g_m = ‖freq m‖x_m, D_m = Σ_{k∈F} x_k y_{k−m}).
- S5 (L1, kernel): w_k := (‖freq k‖^{7/4})⁻¹ (junk-zero at 0):
  ∀ m, Σ'_k w_k w_{k−m} ≤ C_K := 2·Σ'_k ‖freq k‖^{−7/2} < ∞ (min/max split,
  one_le_norm_freq, summable at −7/2 < −3).
- S6 (L4): C_m² ≤ C_K·Σ_{k∈F}X_k²X_{k−m}² with X_k := ‖freq k‖^{7/8}x_k;
  Σ'_m C_m² ≤ C_K·‖X·1_F‖₂²·‖X‖₂².
- S7 (L3, interpolation): Σ'‖freq k‖^{7/4}x_k² ≤ en(d)^{1/8}·ens(d)^{7/8}
  (Hölder 8–8/7 on (x²)^{1/8}(‖k‖²x²)^{7/8}).
- S8–S9 (L5): T_A ≤ √(C_K Z)·en^{1/8}ens^{7/8}, T_B ≤ √C_K·E^{1/16}Z^{7/16}
  ·en^{1/16}ens^{15/16}; Young (8/7,8) and (16/15,16):
  2|pairing| ≤ ν·ens(d) + K(ν,E,Z)·en(d), K explicit.
- S10–S11 (L9): φ_F' ≤ K·φ_F + (ν·tailens_F + 4KZ/R²); the Φ-trick
  (Φ := ∫φ_F, constant-source exponential-factor Grönwall on Φ — the house
  vanish pattern) gives φ_F ≤ S_F·e^{KT}.
- S12: en(d t) ≤ e^{KT}S_{boxS R} + 4Z/R² → 0 (DCT with constant bound 8Z;
  pointwise tail vanishing from the exported Summable via
  tendsto_tsum_compl_atTop_zero ∘ Filter.tendsto_atTop_finset_of_monotone
  along the boxS exhaustion). en(d) ≡ 0 ⇒ modes vanish ⇒ agreement. ∎

## New lemmas (interfaces freeze at wave launch)

L1 kernel_sum_le · L2 mixed convMaj (two-field √(en u)·√(ens v)) ·
L3 weighted_interp · L4 conv_corr_sq_le · L5 pairing_absorbed ·
L6 leray_pairing_drop · L7 defect calculus · L8 public
hasDerivAt_finset_sum_sq · L9 gronwall_const_source · L10 tail/measurability
pack · L11 theorem_B_cont (theorem_B's conclusion + the mode-continuity
clause; proof replays the T3 assembly — the statement is a NEW stronger
sibling, the frozen theorem_B stands untouched).

## Waves

U1 (L1, L3 — pure lattice/tsum) ∥ U3 (L6, L7, L8 — defect calculus) →
U2 (L2, L4, L5 — the bilinear heart) → U4 (L9, L10 + capstone
theorem_B_unique) → U5 (theorem_B_cont + ns_full_global_flow).

## Risk register (honest)

No genuinely new hard analysis anywhere; the two nontrivial ingredients
(L1, L4) compiled as skeletons during recon. Residual: rpow/pow coercion
gymnastics at 7/4, 7/8, 1/8, 1/16; the S11–S12 measurability/integrability
plumbing (budget generously); Summable.sum_add_tsum_compl name unverified
at pin (fallback exists); SummationFilter noise in error messages.
leray-hopf has NO uniqueness of any kind — if U4 lands, this appears to be
the first machine-checked uniqueness statement for 3D NS in any generality,
in any proof assistant (recon 28 Aug; corrections welcome).
