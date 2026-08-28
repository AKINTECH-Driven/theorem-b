/-
# Tail bounds and the vanishing source (Tier 4, wave U4a)

Defect energy/enstrophy bounds, the box-complement frequency bound, the
energy tail beyond the box, and the enstrophy-tail source integral that
vanishes along the exhaustion - powered by the summability certificates
theorem_B exports.
-/
import TheoremB.LatticeKernel
import TheoremB.DefectCalculus

namespace TheoremB

open Set

/-! ### BRAVO-4: the tail pack -/

/-- Energy of a difference: `en (a − b) ≤ 2 en a + 2 en b`. -/
theorem en_sub_le {a b : (Fin 3 → ℤ) → Vel}
    (hEa : Summable fun l => ‖a l‖ ^ 2) (hEb : Summable fun l => ‖b l‖ ^ 2) :
    en (fun l => a l - b l) ≤ 2 * en a + 2 * en b := by
  have hterm : ∀ l, ‖a l - b l‖ ^ 2 ≤ 2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2 := by
    intro l
    have htri : ‖a l - b l‖ ≤ ‖a l‖ + ‖b l‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (a l - b l), norm_nonneg (a l), norm_nonneg (b l),
      sq_nonneg (‖a l‖ - ‖b l‖)]
  have hmaj : Summable fun l => 2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2 :=
    (hEa.mul_left 2).add (hEb.mul_left 2)
  have h1 : (∑' l, ‖a l - b l‖ ^ 2) ≤ ∑' l, (2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2) :=
    (summable_sq_sub hEa hEb).tsum_le_tsum hterm hmaj
  have h2 : (∑' l, (2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2))
      = 2 * (∑' l, ‖a l‖ ^ 2) + 2 * (∑' l, ‖b l‖ ^ 2) := by
    rw [Summable.tsum_add (hEa.mul_left 2) (hEb.mul_left 2), tsum_mul_left, tsum_mul_left]
  have hen : en (fun l => a l - b l) = ∑' l, ‖a l - b l‖ ^ 2 := rfl
  have hena : en a = ∑' l, ‖a l‖ ^ 2 := rfl
  have henb : en b = ∑' l, ‖b l‖ ^ 2 := rfl
  linarith

/-- Enstrophy of a difference: `ens (a − b) ≤ 2 ens a + 2 ens b`. -/
theorem ens_sub_le {a b : (Fin 3 → ℤ) → Vel}
    (hZa : Summable fun l => ‖freq l‖ ^ 2 * ‖a l‖ ^ 2)
    (hZb : Summable fun l => ‖freq l‖ ^ 2 * ‖b l‖ ^ 2) :
    ens (fun l => a l - b l) ≤ 2 * ens a + 2 * ens b := by
  have hterm : ∀ l, ‖freq l‖ ^ 2 * ‖a l - b l‖ ^ 2
      ≤ 2 * (‖freq l‖ ^ 2 * ‖a l‖ ^ 2) + 2 * (‖freq l‖ ^ 2 * ‖b l‖ ^ 2) := by
    intro l
    have htri : ‖a l - b l‖ ≤ ‖a l‖ + ‖b l‖ := norm_sub_le _ _
    have hsq : ‖a l - b l‖ ^ 2 ≤ 2 * ‖a l‖ ^ 2 + 2 * ‖b l‖ ^ 2 := by
      nlinarith [norm_nonneg (a l - b l), norm_nonneg (a l), norm_nonneg (b l),
        sq_nonneg (‖a l‖ - ‖b l‖)]
    nlinarith [sq_nonneg ‖freq l‖]
  have hmaj : Summable fun l =>
      2 * (‖freq l‖ ^ 2 * ‖a l‖ ^ 2) + 2 * (‖freq l‖ ^ 2 * ‖b l‖ ^ 2) :=
    (hZa.mul_left 2).add (hZb.mul_left 2)
  have h1 : (∑' l, ‖freq l‖ ^ 2 * ‖a l - b l‖ ^ 2)
      ≤ ∑' l, (2 * (‖freq l‖ ^ 2 * ‖a l‖ ^ 2) + 2 * (‖freq l‖ ^ 2 * ‖b l‖ ^ 2)) :=
    (summable_wsq_sub hZa hZb).tsum_le_tsum hterm hmaj
  have h2 : (∑' l, (2 * (‖freq l‖ ^ 2 * ‖a l‖ ^ 2) + 2 * (‖freq l‖ ^ 2 * ‖b l‖ ^ 2)))
      = 2 * (∑' l, ‖freq l‖ ^ 2 * ‖a l‖ ^ 2) + 2 * (∑' l, ‖freq l‖ ^ 2 * ‖b l‖ ^ 2) := by
    rw [Summable.tsum_add (hZa.mul_left 2) (hZb.mul_left 2), tsum_mul_left, tsum_mul_left]
  have hen : ens (fun l => a l - b l) = ∑' l, ‖freq l‖ ^ 2 * ‖a l - b l‖ ^ 2 := rfl
  have hena : ens a = ∑' l, ‖freq l‖ ^ 2 * ‖a l‖ ^ 2 := rfl
  have henb : ens b = ∑' l, ‖freq l‖ ^ 2 * ‖b l‖ ^ 2 := rfl
  linarith

/-- Outside the box `insert 0 (boxS R)`, frequencies exceed `R`. -/
theorem boxS_compl_freq (R : ℕ) (k : Fin 3 → ℤ) (hk : k ∉ insert 0 (boxS R)) :
    (R:ℝ) < ‖freq k‖ := by
  have hk0 : k ≠ 0 := by
    intro h
    subst h
    exact hk (Finset.mem_insert_self 0 _)
  have hkb : k ∉ boxS R := fun h => hk (Finset.mem_insert_of_mem h)
  have hex : ∃ i, ¬(-(R:ℤ) ≤ k i ∧ k i ≤ R) := by
    by_contra h
    push Not at h
    exact hkb (mem_boxS.mpr ⟨hk0, fun i => h i⟩)
  obtain ⟨i, hi⟩ := hex
  have hnat : R + 1 ≤ (k i).natAbs := by omega
  have hsup : (k i).natAbs ≤ natMax k :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ i)
  have h2 : R + 1 ≤ natMax k := hnat.trans hsup
  have h3 : ((R:ℝ) + 1) ≤ (natMax k : ℝ) := by exact_mod_cast h2
  linarith [natMax_cast_le_norm_freq k]

/-- The energy outside a box of radius `R` is at most `Z / R²`. -/
theorem tail_en_lt {d : (Fin 3 → ℤ) → Vel} {Z : ℝ} (R : ℕ) (hR : 0 < R)
    (hE : Summable fun l => ‖d l‖ ^ 2)
    (hZsum : Summable fun l => ‖freq l‖ ^ 2 * ‖d l‖ ^ 2) (hZle : ens d ≤ Z) :
    en d - (∑ k ∈ insert 0 (boxS R), ‖d k‖ ^ 2) ≤ Z / (R:ℝ) ^ 2 := by
  have hsplit := hE.sum_add_tsum_compl (s := insert 0 (boxS R))
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR
  have hcompl : ∀ l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ), (R:ℝ) < ‖freq l.val‖ := by
    intro l
    refine boxS_compl_freq R l.val fun hmem => ?_
    exact (Set.mem_compl_iff _ _).mp l.property (Finset.mem_coe.mpr hmem)
  have hZs : Summable fun l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ) =>
      ‖freq l.val‖ ^ 2 * ‖d l.val‖ ^ 2 := hZsum.subtype _
  have hterm : ∀ l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ),
      ‖d l.val‖ ^ 2 ≤ ((R:ℝ) ^ 2)⁻¹ * (‖freq l.val‖ ^ 2 * ‖d l.val‖ ^ 2) := by
    intro l
    have h1 : (R:ℝ) ^ 2 ≤ ‖freq l.val‖ ^ 2 := by nlinarith [hcompl l]
    have h2 : (0:ℝ) < (R:ℝ) ^ 2 := by positivity
    rw [← div_eq_inv_mul, le_div_iff₀ h2]
    nlinarith [sq_nonneg ‖d l.val‖]
  have hsub : Summable fun l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ) =>
      ‖d l.val‖ ^ 2 :=
    (hZs.mul_left _).of_nonneg_of_le (fun l => sq_nonneg _) hterm
  have htail : (∑' l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ), ‖d l.val‖ ^ 2)
      ≤ Z / (R:ℝ) ^ 2 := by
    have hZ0 : (0:ℝ) ≤ ((R:ℝ) ^ 2)⁻¹ := by positivity
    calc (∑' l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ), ‖d l.val‖ ^ 2)
        ≤ ∑' l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ),
            ((R:ℝ) ^ 2)⁻¹ * (‖freq l.val‖ ^ 2 * ‖d l.val‖ ^ 2) :=
          hsub.tsum_le_tsum hterm (hZs.mul_left _)
      _ = ((R:ℝ) ^ 2)⁻¹ * ∑' l : ↥((↑(insert 0 (boxS R)) : Set (Fin 3 → ℤ))ᶜ),
            ‖freq l.val‖ ^ 2 * ‖d l.val‖ ^ 2 := tsum_mul_left
      _ ≤ ((R:ℝ) ^ 2)⁻¹ * ens d := by
          refine mul_le_mul_of_nonneg_left ?_ hZ0
          exact hZsum.tsum_subtype_le _ _ (fun l => by positivity)
      _ ≤ ((R:ℝ) ^ 2)⁻¹ * Z := mul_le_mul_of_nonneg_left hZle hZ0
      _ = Z / (R:ℝ) ^ 2 := (div_eq_inv_mul Z ((R:ℝ) ^ 2)).symm
  have hen : en d = ∑' k, ‖d k‖ ^ 2 := rfl
  linarith

/-- Any finite section of the enstrophy sum stays below the full sum. -/
theorem tail_nonneg {d : (Fin 3 → ℤ) → Vel}
    (hZsum : Summable fun l => ‖freq l‖ ^ 2 * ‖d l‖ ^ 2) (F : Finset (Fin 3 → ℤ)) :
    0 ≤ ens d - ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖d k‖ ^ 2 := by
  have h := Summable.sum_le_tsum F (fun i _ => by positivity) hZsum
  have hens : ens d = ∑' k, ‖freq k‖ ^ 2 * ‖d k‖ ^ 2 := rfl
  linarith

/-! ### Private machinery for the two measure-theoretic tail lemmas -/

/-- The boxes `insert 0 (boxS R)` grow monotonically. -/
private lemma b4_box_mono : Monotone fun R : ℕ => insert 0 (boxS R) := by
  intro m n hmn
  refine Finset.insert_subset_insert _ fun k hk => ?_
  rw [mem_boxS] at hk ⊢
  refine ⟨hk.1, fun i => ?_⟩
  have := hk.2 i
  omega

/-- The boxes `insert 0 (boxS R)` exhaust the lattice. -/
private lemma b4_box_tendsto :
    Filter.Tendsto (fun R : ℕ => insert 0 (boxS R)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone b4_box_mono fun k => ?_
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨0, Finset.mem_insert_self _ _⟩
  · obtain ⟨R, hR⟩ := exists_boxS k hk
    exact ⟨R, Finset.mem_insert_of_mem (hR R le_rfl)⟩

/-- Box sections of the enstrophy sum converge to the enstrophy. -/
private lemma b4_sec_tendsto {c : (Fin 3 → ℤ) → Vel}
    (hs : Summable fun l => ‖freq l‖ ^ 2 * ‖c l‖ ^ 2) :
    Filter.Tendsto (fun R : ℕ => ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖c k‖ ^ 2)
      Filter.atTop (nhds (ens c)) := by
  have h1 : Filter.Tendsto
      (fun F : Finset (Fin 3 → ℤ) => ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖c k‖ ^ 2)
      Filter.atTop (nhds (ens c)) := hs.hasSum
  exact h1.comp b4_box_tendsto

/-- Finite sections of the enstrophy sum are continuous in time. -/
private lemma b4_sec_contOn {T : ℝ} {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T)) (F : Finset (Fin 3 → ℤ)) :
    ContinuousOn (fun s => ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2) (Icc (0:ℝ) T) := by
  refine continuousOn_finsetSum F fun k _ => ?_
  exact continuousOn_const.mul (((hcont k).norm).pow 2)

/-- `s ↦ ens (d s)` is a.e. strongly measurable on `[0, T]`, as the pointwise
limit of the continuous box sections. -/
private lemma b4_meas_ens {T : ℝ} {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (hsum : ∀ t ∈ Icc (0:ℝ) T, Summable fun l => ‖freq l‖ ^ 2 * ‖d t l‖ ^ 2) :
    MeasureTheory.AEStronglyMeasurable (fun s => ens (d s))
      (MeasureTheory.volume.restrict (Icc (0:ℝ) T)) := by
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun (n : ℕ) (s : ℝ) => ∑ k ∈ insert 0 (boxS n), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
    (fun n => ?_) ?_
  · exact (b4_sec_contOn hcont _).aestronglyMeasurable measurableSet_Icc
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun s hs => b4_sec_tendsto (hsum s hs)

/-- The tail integrand is a.e. strongly measurable on `[0, T]`. -/
private lemma b4_meas_integrand {T : ℝ} {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (hsum : ∀ t ∈ Icc (0:ℝ) T, Summable fun l => ‖freq l‖ ^ 2 * ‖d t l‖ ^ 2)
    (F : Finset (Fin 3 → ℤ)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s => ens (d s) - ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
      (MeasureTheory.volume.restrict (Icc (0:ℝ) T)) :=
  (b4_meas_ens hcont hsum).sub
    ((b4_sec_contOn hcont F).aestronglyMeasurable measurableSet_Icc)

/-- The enstrophy tail is interval integrable: it is bounded between `0` and `Z`
and a.e. strongly measurable. -/
theorem tail_integrable {Z T : ℝ} (hZ0 : 0 ≤ Z) (hT : 0 ≤ T)
    {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (hsum : ∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖freq l‖ ^ 2 * ‖d t l‖ ^ 2))
    (hbound : ∀ t ∈ Icc (0:ℝ) T, ens (d t) ≤ Z) (F : Finset (Fin 3 → ℤ)) :
    IntervalIntegrable (fun s => ens (d s) - ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
      MeasureTheory.volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine MeasureTheory.Integrable.mono' (g := fun _ => Z)
    (MeasureTheory.integrableOn_const measure_Icc_lt_top.ne)
    (b4_meas_integrand hcont hsum F) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun s hs => ?_
  have h1 := tail_nonneg (hsum s hs) F
  have h2 : (0:ℝ) ≤ ∑ k ∈ F, ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  have h3 := hbound s hs
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Dominated convergence: the integrated enstrophy tail vanishes as the box
radius grows. -/
theorem tail_source {Z T : ℝ} (hZ0 : 0 ≤ Z) (hT : 0 ≤ T)
    {d : ℝ → (Fin 3 → ℤ) → Vel}
    (hcont : ∀ k, ContinuousOn (fun s => d s k) (Icc (0:ℝ) T))
    (hsum : ∀ t ∈ Icc (0:ℝ) T, Summable (fun l => ‖freq l‖ ^ 2 * ‖d t l‖ ^ 2))
    (hbound : ∀ t ∈ Icc (0:ℝ) T, ens (d t) ≤ Z) :
    Filter.Tendsto (fun R : ℕ => ∫ s in (0:ℝ)..T,
      (ens (d s) - ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2))
      Filter.atTop (nhds 0) := by
  have hmem : ∀ s ∈ uIoc (0:ℝ) T, s ∈ Icc (0:ℝ) T := by
    intro s hs
    rw [uIoc_of_le hT] at hs
    exact Ioc_subset_Icc_self hs
  have hres : MeasureTheory.volume.restrict (uIoc (0:ℝ) T)
      ≤ MeasureTheory.volume.restrict (Icc (0:ℝ) T) := by
    refine MeasureTheory.Measure.restrict_mono ?_ le_rfl
    intro s hs
    exact hmem s hs
  have hF_meas : ∀ᶠ R : ℕ in Filter.atTop, MeasureTheory.AEStronglyMeasurable
      (fun s => ens (d s) - ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
      (MeasureTheory.volume.restrict (uIoc (0:ℝ) T)) :=
    Filter.Eventually.of_forall fun R =>
      (b4_meas_integrand hcont hsum _).mono_measure hres
  have h_bound : ∀ᶠ R : ℕ in Filter.atTop, ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ uIoc (0:ℝ) T →
      ‖ens (d s) - ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2‖ ≤ Z := by
    refine Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun s hs => ?_
    have hs' := hmem s hs
    have h1 := tail_nonneg (hsum s hs') (insert 0 (boxS R))
    have h2 : (0:ℝ) ≤ ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => by positivity
    have h3 := hbound s hs'
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  have h_lim : ∀ᵐ s ∂MeasureTheory.volume, s ∈ uIoc (0:ℝ) T →
      Filter.Tendsto (fun R : ℕ =>
        ens (d s) - ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
        Filter.atTop (nhds 0) := by
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hs' := hmem s hs
    have h2 : Filter.Tendsto (fun R : ℕ =>
        ens (d s) - ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
        Filter.atTop (nhds (ens (d s) - ens (d s))) :=
      Filter.Tendsto.sub tendsto_const_nhds (b4_sec_tendsto (hsum s hs'))
    simpa using h2
  have h := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := T)
    (f := fun _ : ℝ => (0:ℝ))
    (F := fun (R : ℕ) (s : ℝ) =>
      ens (d s) - ∑ k ∈ insert 0 (boxS R), ‖freq k‖ ^ 2 * ‖d s k‖ ^ 2)
    (fun _ => Z) hF_meas h_bound intervalIntegrable_const h_lim
  simpa using h

end TheoremB
