/-
# The classical layer capstone (Tier 6, wave W5-cap)

`theorem_B_smooth`: for small data whose spectrum is summable at EVERY
Sobolev level, the eternal Navier-Stokes flow of `ns_full_global_flow`
admits a genuinely classical representative.

What is delivered, for ONE flow (the all-levels statement is the meta-
corollary of the per-level `ns_full_global_flow_sobolev`, compiled here by
identifying every level's witness with the base flow through
`theorem_B_unique`):

* every clause of `ns_full_global_flow` — reality, divergence-freeness,
  summability, mode continuity, the integral equation, the mode ODE on
  `t > 0`, and the energy/enstrophy trap;
* every Sobolev level survives for all time, and the flow stays mean-zero;
* weighted ℓ¹ control at every order (`summable_weighted_norm`), the fuel
  of the classical layer;
* SPACE: the ℤ³-periodic lift `uLift` is `ContDiff ℝ p` for every `p` and
  is genuinely `ℤ³`-periodic;
* TIME: at every point of the torus the character-weighted mode sum — the
  velocity field's value — is differentiable in time on `t > 0`, with
  derivative the synthesized Navier-Stokes right-hand side.  This is the
  spectral form of the equation, holding POINTWISE rather than weakly.

  The object being differentiated really is the velocity field: for an ℓ¹
  family, `∑' k, c k j * mFourier k x = uCont j c hc x` (`uCont_apply`
  plus `smul_eq_mul`), i.e. the value at `x` of the continuous
  representative whose `L²` class is the campaign's `synthT`
  (`toLp_uCont`).  The tsum spelling is used in the statement only to
  avoid carrying a per-time summability certificate inside it.

HONEST SCOPE. The time clause states the equation with its right-hand side
in synthesized spectral form; rewriting that right-hand side in classical
notation (the Laplacian as second spatial derivatives, the nonlinearity as
a Leray-projected product) is the remaining step, and is NOT claimed here.
Nothing is asserted about analyticity (`contDiff_tsum` caps at `ℕ∞`) or
about `C^∞` in time (that needs a time-derivative of `convFull`, which the
campaign does not have).

STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
the target machine.
-/
import TheoremB.TheoremBSobolev
import TheoremB.ContinuousRep
import TheoremB.PeriodicLift
import TheoremB.TimeLayer

namespace TheoremB

open Set UnitAddTorus

/-! ## Identifying two flows of the uniqueness class on the half-line -/

/-- Two eternal flows with the same datum, both in `theorem_B_unique`'s class
with the same budgets, agree everywhere on `[0, ∞)`.  (Applied at horizon
`T := t` for each `t`; the class hypotheses are exactly what
`ns_full_global_flow_sobolev` exports, so no bridging is needed.) -/
private lemma flow_agree_Ici {ν : ℝ} (hν : 0 < ν) {c₀ : (Fin 3 → ℤ) → Vel}
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

/-! ## The zero frequency -/

private lemma freq_zero_eq : freq (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [freq]

/-! ## The capstone -/

/-- **Theorem B, smooth form.**  Small data with spectrum summable at every
Sobolev level generates an eternal Navier-Stokes flow that is classically
regular in space — its `ℤ³`-periodic lift is `C^p` for every `p` — and whose
value at every point of the torus is differentiable in time for `t > 0`,
with derivative the synthesized Navier-Stokes right-hand side.

See the file header for the honest scope: the time clause carries the
equation's right-hand side in synthesized spectral form, not yet rewritten
in classical Laplacian-plus-nonlinearity notation. -/
theorem theorem_B_smooth :
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
              + lerayProj k (convFull (c t) k)) j * mFourier k x) t) := by
  obtain ⟨κ, hκ, hflow⟩ := ns_full_global_flow_sobolev
  refine ⟨κ, hκ, ?_⟩
  intro ν hν c₀ hall hmean0 hreal hdiv hsmall
  have hE : Summable fun l => ‖c₀ l‖ ^ 2 := by simpa using hall 0
  have hZ : Summable fun l => ‖freq l‖ ^ 2 * ‖c₀ l‖ ^ 2 := by simpa using hall 1
  obtain ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, -⟩ :=
    hflow hν 1 le_rfl hE hZ (by simpa using hall 1) hmean0 hreal hdiv hsmall
  -- the flow's own class data, in the shape `flow_agree_Ici` wants
  have hcdiv : ∀ t ∈ Ici (0:ℝ), DivFree (c t) := fun t ht => (hstruct t ht).2
  have hcb : ∀ t ∈ Ici (0:ℝ), en (c t) ≤ en c₀ ∧ ens (c t) ≤ ens c₀ :=
    fun t ht => ⟨(htrap t ht).1, (htrap t ht).2.1⟩
  -- EVERY Sobolev level, transferred to this flow by uniqueness
  have hlevel : ∀ (m : ℕ), ∀ t ∈ Ici (0:ℝ),
      Summable fun l => ‖freq l‖ ^ (2 * m) * ‖c t l‖ ^ 2 := by
    intro m t ht
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using (hsum t ht).1
    · obtain ⟨d, hd0, hdstruct, hdsum, hdcont, hdinteq, -, hdtrap, hdlev⟩ :=
        hflow hν m hm hE hZ (hall m) hmean0 hreal hdiv hsmall
      obtain ⟨_K, _hK, hdsob⟩ := hdlev
      have hag := flow_agree_Ici hν hc0 hd0 hcont hdcont hsum hdsum hcb
        (fun s hs => ⟨(hdtrap s hs).1, (hdtrap s hs).2.1⟩) hcdiv
        (fun s hs => (hdstruct s hs).2) hinteq hdinteq
      exact ((hdsob t ht).1).congr fun l => by rw [hag t ht l]
  -- the level-8 growth bound, transferred the same way (the window constant)
  have hsob8 : ∃ K, 0 < K ∧ ∀ t ∈ Ici (0:ℝ),
      sob 8 (c t) ≤ sob 8 c₀ * (1 + Real.exp (K * t)) := by
    obtain ⟨d, hd0, hdstruct, hdsum, hdcont, hdinteq, -, hdtrap, hdlev⟩ :=
      hflow hν 8 (by norm_num) hE hZ (hall 8) hmean0 hreal hdiv hsmall
    obtain ⟨K, hK, hdsob⟩ := hdlev
    have hag := flow_agree_Ici hν hc0 hd0 hcont hdcont hsum hdsum hcb
      (fun s hs => ⟨(hdtrap s hs).1, (hdtrap s hs).2.1⟩) hcdiv
      (fun s hs => (hdstruct s hs).2) hinteq hdinteq
    refine ⟨K, hK, fun t ht => ?_⟩
    have he : sob 8 (c t) = sob 8 (d t) := by
      have e1 : sob 8 (c t) = ∑' l, ‖freq l‖ ^ (2 * 8) * ‖c t l‖ ^ 2 := rfl
      have e2 : sob 8 (d t) = ∑' l, ‖freq l‖ ^ (2 * 8) * ‖d t l‖ ^ 2 := rfl
      rw [e1, e2]
      exact tsum_congr fun l => by rw [hag t ht l]
    rw [he]
    exact (hdsob t ht).2
  -- the flow stays mean-zero: the zero mode's equation has a vanishing source
  have hmean : ∀ t ∈ Ici (0:ℝ), c t 0 = 0 := by
    intro t ht
    have hEqOn : EqOn (fun s => (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0
        + lerayProj (0 : Fin 3 → ℤ) (convFull (c s) 0)) (fun _ => (0 : Vel))
        (uIcc (0:ℝ) t) := by
      intro s hs
      rw [uIcc_of_le ht] at hs
      have hs0 : s ∈ Ici (0:ℝ) := hs.1
      show (-(ν * ‖freq (0 : Fin 3 → ℤ)‖ ^ 2)) • c s 0
        + lerayProj (0 : Fin 3 → ℤ) (convFull (c s) 0) = 0
      rw [convFull_zero_of_divFree (hcdiv s hs0), freq_zero_eq]
      simp [lerayProj, dotR]
    have h := hinteq t ht 0
    rw [intervalIntegral.integral_congr hEqOn] at h
    simpa [hmean0] using h
  -- weighted ℓ¹ at every order, from two extra Sobolev levels
  have hl1 : ∀ t ∈ Ici (0:ℝ), ∀ p : ℕ,
      Summable fun l => ‖freq l‖ ^ p * ‖c t l‖ := fun t ht p =>
    summable_weighted_norm (hmean t ht) (hlevel (p + 2) t ht)
  -- SPACE
  have hspace : ∀ t ∈ Ici (0:ℝ), ∀ (j : Fin 3) (p : ℕ),
      ContDiff ℝ (p : ℕ∞) (uLift j (c t)) := fun t ht j p =>
    contDiff_uLift j (c t) p (fun q _ => hl1 t ht q)
  -- TIME
  have htime : ∀ (j : Fin 3) (x : UnitAddTorus (Fin 3)), ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (fun s => ∑' k, c s k j * mFourier k x)
        (∑' k, ((-(ν * ‖freq k‖ ^ 2)) • c t k
          + lerayProj k (convFull (c t) k)) j * mFourier k x) t := by
    intro j x t ht
    obtain ⟨K, hK, hgrow⟩ := hsob8
    have htpos : (0:ℝ) < t := ht
    -- a window around t, inside the open half-line
    set a : ℝ := t / 2 with ha
    set b : ℝ := t + 1 with hb
    have hwin : ∀ s ∈ Ioo a b, s ∈ Ici (0:ℝ) := by
      intro s hs
      exact le_of_lt (lt_trans (by positivity) hs.1)
    have hwinI : ∀ s ∈ Ioo a b, s ∈ Ioi (0:ℝ) := by
      intro s hs
      exact lt_trans (by positivity) hs.1
    -- the window constant, uniform in time by the level-8 growth bound
    set B : ℝ := (quarticKernel + sob 8 c₀ * (1 + Real.exp (K * b))) / 2 with hBdef
    have hs8nn : 0 ≤ sob 8 c₀ := sob_nonneg 8 c₀
    have hBnn : 0 ≤ B := by
      have := quarticKernel_nonneg
      have hx : 0 ≤ sob 8 c₀ * (1 + Real.exp (K * b)) := by positivity
      rw [hBdef]; linarith
    have hWB : ∀ s ∈ Ioo a b, ∀ q : ℕ, q ≤ 6 →
        (∑' l, ‖freq l‖ ^ q * ‖c s l‖) ≤ B := by
      intro s hs q hq
      have hsI := hwin s hs
      -- the level-(q+2) mass is capped by the level-8 mass, which grows at
      -- most by (1 + e^{K b}) on the window
      have hqle : sob (q + 2) (c s) ≤ sob 8 (c s) :=
        sob_le_sob (by omega) (hmean s hsI) (hlevel 8 s hsI)
      have hgs : sob 8 (c s) ≤ sob 8 c₀ * (1 + Real.exp (K * b)) := by
        refine (hgrow s hsI).trans ?_
        have hmono : Real.exp (K * s) ≤ Real.exp (K * b) :=
          Real.exp_le_exp.mpr (by nlinarith [hs.2, hK, hs.1, htpos])
        nlinarith [Real.exp_pos (K * s), Real.exp_pos (K * b)]
      have hmass : (∑' l, ‖freq l‖ ^ (2 * (q + 2)) * ‖c s l‖ ^ 2)
          ≤ sob 8 c₀ * (1 + Real.exp (K * b)) := by
        have e : sob (q + 2) (c s) = ∑' l, ‖freq l‖ ^ (2 * (q + 2)) * ‖c s l‖ ^ 2 := rfl
        rw [← e]
        exact hqle.trans hgs
      exact tsum_weighted_norm_le_of_bound (hmean s hsI) (hlevel (q + 2) s hsI) hmass
    -- the summable time-uniform majorant
    obtain ⟨u, hu, hmaj⟩ := exists_summable_nsRHS_maj (ν := ν) hν.le (B := B) hBnn
      (fun s hs => hmean s (hwin s hs))
      (fun s hs => convFull_zero_of_divFree (hcdiv s (hwin s hs)))
      (fun s hs => (hsum s (hwin s hs)).1) (fun s hs => (hsum s (hwin s hs)).2)
      (fun s hs q _ => hl1 s (hwin s hs) q) hWB
    have htmem : t ∈ Ioo a b := ⟨by rw [ha]; linarith, by rw [hb]; linarith⟩
    exact hasDerivAt_weighted_tsum_flow
      (fun k => le_of_eq (norm_mFourier_apply k x))
      (fun s hs k => hode s (hwinI s hs) k) hu
      (fun s hs k => hmaj s hs k) htmem
      (by simpa using hl1 t (le_of_lt htpos) 0) t htmem
  exact ⟨c, hc0, hstruct, hsum, hcont, hinteq, hode, htrap, hlevel, hmean, hl1,
    hspace, fun t _ j g x => uLift_periodic j (c t) g x, htime⟩

end TheoremB
