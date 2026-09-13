/-
  TheoremB/Galilean.lean
  Tier 9, wave W2 (Theorem B campaign, 13 Sep 2026): the Galilean change of
  frame on the closed slab as a class-level fact: a member of OUR COPY of the
  community solution class at datum `w₀` and force `0`, boosted by a constant
  velocity `m`, is a member at datum `m + w₀`.  Transcribed from section C of
  the design probe `audit-tier9/design/final/Tier9Final.lean` (session
  directory, never a tracked file; compiled there at the pin, exit 0; section C
  is the reconnaissance probe `recon/R4/ReconR4.lean` verbatim in every
  declaration and proof, the design pass having reworded section comments
  and docstrings only (measured by diff), and has no declaration with a
  placeholder proof, the probe's only two being the W3
  candidates of its section F, not transcribed); the frozen statements are
  those of `context/rung11-tier9-blueprint.md` section 4b (the Galilean
  block), byte-identical, and the proofs are the probe's.

  WHAT IS DELIVERED HERE.
  * The boosted pair and the frame change (C1): `galV m w x τ := m + w (x - τ • m) τ`,
    `galP m q x τ := q (x - τ • m) τ`, the closed slab `slab := univ ×ˢ Ici 0`
    (an `abbrev`, so that it unifies with the class's literal), and the affine
    map `galΦ m (x, τ) := (x - τ • m, τ)`.
  * Smoothness transfer and the translation identities (C2): `contDiffOn_galV`,
    `contDiffOn_galP` (joint `C^∞` on the closed slab passes through `galΦ`,
    which is `C^∞` and maps the slab to itself), `contDiff_space_slice` (a
    jointly `C^∞` field on the slab has a `C^∞` space slice at every `τ ≥ 0`),
    and the translation identities `laplacian_translate` (any codomain, no
    differentiability hypothesis: `iteratedFDeriv_comp_sub` is unconditional
    at the pin), `gradient_translate`, `divergence_translate`, and
    `divergence_const_add`.
  * The joint within-derivative decomposition and the boosted operators (C3):
    the class's time derivative of the boosted field `derivWithin_galV_time`
    (the within-derivative on `Ici 0` along the curve `σ ↦ (x - σ • m, σ)`,
    through `fderivWithin` of the uncurried field on the slab), the space
    derivative `fderiv_galV_space`, the convection identity `convection_galV`
    (`(v·∇)v` at the boosted point is a drift term plus `(w·∇)w` at the moved
    point), the Laplacian `laplacian_galV_space`, the pressure gradient
    `gradient_galP_space`, the initial value `galV_zero`, and the periodicity
    and divergence transfer `isOnePeriodic_galV`, `isOnePeriodic_galP`,
    `divergence_galV`.
  * THE CLASS TRANSFER `galilean_class` (C4): the seven fields of
    `NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun x => m + w₀ x)
    (f := 0) (galV m w) (galP m q)` from those of `(w₀, w, q)`; the
    `navier_stokes` field by the four rewrites above and `abel` (the drift term
    of the time derivative cancels the drift term of the convection).

  HONEST SCOPE.
  * Nothing here is new mathematics: the Galilean invariance of Navier-Stokes
    under a constant boost is textbook (the opening chapter of any
    Navier-Stokes text); the deliverable is the machine-checked transfer of
    the class's seven fields, in the class's own `derivWithin` / `fderiv` /
    `Δ` / `gradient` vocabulary on the closed slab.
  * No constant is introduced here; no numeric value of any constant is
    claimed; there is no smallness hypothesis and no viscosity hypothesis
    (`ν'` is an arbitrary real, as in the class).
  * This file consumes Mathlib and the `Community` definitions only
    (CommunityClass.lean, our copy of the class): no coefficient-side fact, no
    torus integral, hence NO local measure instance (measured standalone by
    the feasibility critic, `critique/feasibility/FeasGalilean.lean`, exit 0).
  * The boost is for force `0` only; the boost for `f ≠ 0` is out of scope
    (left open by R4, not needed).  At drift `0` the pair is unchanged
    (`galV 0 w = w`, `galP 0 q = q`: compiled in the statement critic's
    `critique/shape/ShapeProbe.lean` as `galV_zero_drift`, `galP_zero_drift`,
    not carried here).
  * This file states nothing about either upstream statement (the upstream
    file carries the positive statement
    `navier_stokes_existence_and_smoothness_periodic` and the breakdown
    statement `navier_stokes_breakdown_periodic`; CommunityClass.lean copies
    the class, not those statements); both are untouched.  Priority is not
    claimed for anything.
  * This file edits no earlier file of the tree and clones no private lemma:
    every declaration consumed here is public in its file (CommunityClass,
    Mathlib).  The fourteen helper lemmas (`contDiff_galΦ`, `mapsTo_galΦ`,
    `uncurry_galV_eq`, `uncurry_galP_eq`, `fderiv_translate`,
    `hasFDerivWithinAt_uncurry`, `hasFDerivAt_space_slice`,
    `fderiv_space_slice`, `hasDerivWithinAt_time_slice`,
    `derivWithin_time_slice`, `hasDerivWithinAt_galCurve`, `mapsTo_galCurve`,
    `hasDerivWithinAt_galV_time`, `clm_neg_one`) are shipped public and carry
    no ledger line.

  PIN TRAPS recorded in the probe and binding here (statement-neutral):
  `HasFDerivWithinAt.comp_hasFDerivAt` / `.comp_hasDerivWithinAt` take the
  point FIRST and the curve needs the `_of_eq` variant with `rfl`;
  `(2 : WithTop ℕ∞) ≤ ∞` closes by `WithTop.coe_le_coe.2 le_top`;
  `ContDiffAt.laplacian_add` wants an explicit `(… : ℝ³ → ℝ³)` ascription;
  `laplacian_const` is function-level; `fderiv_comp_sub` is not a bare `rw`
  pattern under a lambda (hence the wrapper `fderiv_translate`).  The pin's
  unused-variable linter warns on the binder `σ` of the helper
  `mapsTo_galCurve` (R4's text, kept; a warning, not an error).

  STATUS: claimed only insofar as scripts/check_axioms.sh reports GREEN on
  the target machine.
-/
import TheoremB.CommunityClass

open Set Filter Topology MeasureTheory InnerProductSpace UnitAddTorus
open scoped ContDiff Laplacian ComplexConjugate

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace TheoremB

open Community

noncomputable section

-- No local measure instance here: this file elaborates no torus integral (Mathlib and the
-- `Community` definitions only; measured standalone by the feasibility critic).

/-- The Galilean-boosted velocity: constant drift `m` plus the flow seen from the moving frame. -/
def galV (m : ℝ³) (w : ℝ³ → ℝ → ℝ³) : ℝ³ → ℝ → ℝ³ := fun x τ => m + w (x - τ • m) τ

/-- The pressure in the moving frame. -/
def galP (m : ℝ³) (q : ℝ³ → ℝ → ℝ) : ℝ³ → ℝ → ℝ := fun x τ => q (x - τ • m) τ

/-- The closed slab `ℝ³ × [0, ∞)`, spelled exactly as in the class. -/
abbrev slab : Set (ℝ³ × ℝ) := (Set.univ : Set ℝ³) ×ˢ Set.Ici (0:ℝ)

/-- The affine change of frame `(x, τ) ↦ (x - τ m, τ)`. -/
def galΦ (m : ℝ³) : ℝ³ × ℝ → ℝ³ × ℝ := fun z => (z.1 - z.2 • m, z.2)

theorem contDiff_galΦ (m : ℝ³) : ContDiff ℝ ∞ (galΦ m) := by
  unfold galΦ
  exact (contDiff_fst.sub (contDiff_snd.smul contDiff_const)).prodMk contDiff_snd

theorem mapsTo_galΦ (m : ℝ³) : MapsTo (galΦ m) slab slab := by
  intro z hz
  exact ⟨mem_univ _, hz.2⟩

theorem uncurry_galV_eq (m : ℝ³) (w : ℝ³ → ℝ → ℝ³) :
    (↿(galV m w)) = fun z : ℝ³ × ℝ => m + ((↿w) ∘ galΦ m) z := rfl

theorem uncurry_galP_eq (m : ℝ³) (q : ℝ³ → ℝ → ℝ) :
    (↿(galP m q)) = (↿q) ∘ galΦ m := rfl

/-- Joint `C^∞` on the closed slab passes to the boosted velocity: `↿(galV m w)` is the
constant `m` plus `↿w ∘ galΦ m`, and `galΦ m` is `C^∞` and maps the slab to itself. -/
theorem contDiffOn_galV {m : ℝ³} {w : ℝ³ → ℝ → ℝ³}
    (hw : ContDiffOn ℝ ∞ (↿w) slab) : ContDiffOn ℝ ∞ (↿(galV m w)) slab := by
  rw [uncurry_galV_eq]
  exact contDiffOn_const.add (hw.comp (contDiff_galΦ m).contDiffOn (mapsTo_galΦ m))

/-- Joint `C^∞` on the closed slab passes to the boosted pressure:
`↿(galP m q) = ↿q ∘ galΦ m`. -/
theorem contDiffOn_galP {m : ℝ³} {q : ℝ³ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ (↿q) slab) : ContDiffOn ℝ ∞ (↿(galP m q)) slab := by
  rw [uncurry_galP_eq]
  exact hq.comp (contDiff_galΦ m).contDiffOn (mapsTo_galΦ m)

/-- A jointly `C^∞` field on the closed slab has a `C^∞` space slice at every time `τ ≥ 0`
(the slice `y ↦ (y, τ)` maps `univ` into the slab). -/
theorem contDiff_space_slice {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    {τ : ℝ} (hτ : 0 ≤ τ) : ContDiff ℝ ∞ (w · τ) := by
  have hs : ContDiff ℝ ∞ (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) := contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) univ slab := fun y _ => ⟨mem_univ _, hτ⟩
  have h := hw.comp hs.contDiffOn hm
  rw [contDiffOn_univ] at h
  exact h

theorem fderiv_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ³ → F) (a x : ℝ³) :
    fderiv ℝ (fun y => g (y - a)) x = fderiv ℝ g (x - a) := fderiv_comp_sub a

/-- `Δ` commutes with translation, for ANY codomain `F` and with NO differentiability
hypothesis (`iteratedFDeriv_comp_sub` is unconditional at the pin). -/
theorem laplacian_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : ℝ³ → F) (a x : ℝ³) :
    Δ (fun y => V (y - a)) x = Δ V (x - a) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (fun y => V (y - a)),
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis V]
  simp only [iteratedFDeriv_comp_sub]

/-- The gradient commutes with translation (`fderiv_comp_sub`, unconditional at the pin). -/
theorem gradient_translate (p : ℝ³ → ℝ) (a x : ℝ³) :
    gradient (fun y => p (y - a)) x = gradient p (x - a) := by
  unfold gradient
  rw [fderiv_comp_sub]

/-- The class's `divergence` commutes with translation (`fderiv_comp_sub`). -/
theorem divergence_translate (V : ℝ³ → ℝ³) (a x : ℝ³) :
    Community.divergence (fun y => V (y - a)) x = Community.divergence V (x - a) := by
  unfold Community.divergence
  rw [fderiv_comp_sub]

/-- Adding a constant vector to a field leaves the class's `divergence` unchanged
(`fderiv_const_add`). -/
theorem divergence_const_add (m : ℝ³) (V : ℝ³ → ℝ³) (x : ℝ³) :
    Community.divergence (fun y => m + V y) x = Community.divergence V x := by
  unfold Community.divergence
  rw [fderiv_const_add]

theorem hasFDerivWithinAt_uncurry {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    {z : ℝ³ × ℝ} (hz : 0 ≤ z.2) :
    HasFDerivWithinAt (↿w) (fderivWithin ℝ (↿w) slab z) slab z :=
  ((hw.differentiableOn (by simp)) z ⟨mem_univ _, hz⟩).hasFDerivWithinAt

theorem hasFDerivAt_space_slice {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (x₀ : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasFDerivAt (w · τ)
      ((fderivWithin ℝ (↿w) slab (x₀, τ)).comp (ContinuousLinearMap.inl ℝ ℝ³ ℝ)) x₀ := by
  have hL := hasFDerivWithinAt_uncurry hw (z := (x₀, τ)) hτ
  have hs : HasFDerivAt (fun y : ℝ³ => ((y, τ) : ℝ³ × ℝ)) (ContinuousLinearMap.inl ℝ ℝ³ ℝ) x₀ :=
    (hasFDerivAt_id x₀).prodMk (hasFDerivAt_const τ x₀)
  have hev : ∀ᶠ y in 𝓝 x₀, ((y, τ) : ℝ³ × ℝ) ∈ slab :=
    Filter.Eventually.of_forall fun y => ⟨mem_univ _, hτ⟩
  exact hL.comp_hasFDerivAt x₀ hs hev

theorem fderiv_space_slice {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (x₀ : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    fderiv ℝ (w · τ) x₀ =
      (fderivWithin ℝ (↿w) slab (x₀, τ)).comp (ContinuousLinearMap.inl ℝ ℝ³ ℝ) :=
  (hasFDerivAt_space_slice hw x₀ hτ).fderiv

theorem hasDerivWithinAt_time_slice {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (x₀ : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivWithinAt (w x₀ ·) (fderivWithin ℝ (↿w) slab (x₀, τ) ((0 : ℝ³), (1 : ℝ)))
      (Ici 0) τ := by
  have hL := hasFDerivWithinAt_uncurry hw (z := (x₀, τ)) hτ
  have hs : HasDerivWithinAt (fun σ : ℝ => ((x₀, σ) : ℝ³ × ℝ)) ((0 : ℝ³), (1 : ℝ)) (Ici 0) τ :=
    ((hasDerivAt_const τ x₀).prodMk (hasDerivAt_id' τ)).hasDerivWithinAt
  have hm : MapsTo (fun σ : ℝ => ((x₀, σ) : ℝ³ × ℝ)) (Ici 0) slab :=
    fun σ hσ => ⟨mem_univ _, hσ⟩
  exact hL.comp_hasDerivWithinAt τ hs hm

theorem derivWithin_time_slice {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (x₀ : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    derivWithin (w x₀ ·) (Ici 0) τ = fderivWithin ℝ (↿w) slab (x₀, τ) ((0 : ℝ³), (1 : ℝ)) :=
  (hasDerivWithinAt_time_slice hw x₀ hτ).derivWithin (uniqueDiffOn_Ici 0 τ hτ)

theorem hasDerivWithinAt_galCurve (m x : ℝ³) (τ : ℝ) :
    HasDerivWithinAt (fun σ : ℝ => ((x - σ • m, σ) : ℝ³ × ℝ)) ((-m, 1) : ℝ³ × ℝ) (Ici 0) τ := by
  have h1 : HasDerivAt (fun σ : ℝ => x - σ • m) (-m) τ := by
    have := ((hasDerivAt_id' τ).smul_const m).const_sub x
    simpa using this
  exact (h1.prodMk (hasDerivAt_id' τ)).hasDerivWithinAt

theorem mapsTo_galCurve (m x : ℝ³) :
    MapsTo (fun σ : ℝ => ((x - σ • m, σ) : ℝ³ × ℝ)) (Ici 0) slab :=
  fun σ hσ => ⟨mem_univ _, hσ⟩

theorem hasDerivWithinAt_galV_time {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (m x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivWithinAt (fun σ => w (x - σ • m) σ)
      (fderivWithin ℝ (↿w) slab (x - τ • m, τ) ((-m, 1) : ℝ³ × ℝ)) (Ici 0) τ := by
  have hL := hasFDerivWithinAt_uncurry hw (z := (x - τ • m, τ)) hτ
  exact hL.comp_hasDerivWithinAt_of_eq τ (hasDerivWithinAt_galCurve m x τ)
    (mapsTo_galCurve m x) rfl

theorem clm_neg_one (L : ℝ³ × ℝ →L[ℝ] ℝ³) (m : ℝ³) :
    L ((-m, 1) : ℝ³ × ℝ) = L ((0 : ℝ³), (1 : ℝ)) - L (m, (0 : ℝ)) := by
  have h : ((-m, 1) : ℝ³ × ℝ) = ((0 : ℝ³), (1 : ℝ)) - (m, (0 : ℝ)) := by
    ext <;> simp
  rw [h, map_sub]

/-- The class's time derivative of the boosted field. -/
theorem derivWithin_galV_time {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (m x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    derivWithin (galV m w x ·) (Ici 0) τ =
      derivWithin (w (x - τ • m) ·) (Ici 0) τ - fderiv ℝ (w · τ) (x - τ • m) m := by
  have h1 : HasDerivWithinAt (galV m w x ·)
      (fderivWithin ℝ (↿w) slab (x - τ • m, τ) ((-m, 1) : ℝ³ × ℝ)) (Ici 0) τ :=
    (hasDerivWithinAt_galV_time hw m x hτ).const_add m
  rw [h1.derivWithin (uniqueDiffOn_Ici 0 τ hτ), derivWithin_time_slice hw (x - τ • m) hτ,
    fderiv_space_slice hw (x - τ • m) hτ, clm_neg_one]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- The space derivative of the boosted velocity at `(x, τ)` is that of `w · τ` at the moved
point `x - τ • m` (the constant drift has zero derivative). -/
theorem fderiv_galV_space {w : ℝ³ → ℝ → ℝ³} (m x : ℝ³) (τ : ℝ) :
    fderiv ℝ (galV m w · τ) x = fderiv ℝ (w · τ) (x - τ • m) := by
  show fderiv ℝ (fun y => m + (fun z => w z τ) (y - τ • m)) x = _
  rw [fderiv_const_add]
  exact fderiv_translate (fun z => w z τ) (τ • m) x

/-- The convection term of the boosted velocity at the boosted point splits as the drift
term `fderiv (w · τ) (x - τ • m) m` plus the convection of `w` at the moved point; the
drift term cancels the one in `derivWithin_galV_time`. -/
theorem convection_galV {w : ℝ³ → ℝ → ℝ³} (m x : ℝ³) (τ : ℝ) :
    fderiv ℝ (galV m w · τ) x (galV m w x τ) =
      fderiv ℝ (w · τ) (x - τ • m) m + fderiv ℝ (w · τ) (x - τ • m) (w (x - τ • m) τ) := by
  rw [fderiv_galV_space]
  show fderiv ℝ (w · τ) (x - τ • m) (m + w (x - τ • m) τ) = _
  rw [map_add]

/-- The Laplacian of the boosted velocity at `(x, τ)`, `τ ≥ 0`, is that of `w · τ` at the
moved point: `Δ` of a constant plus a `C²` field is the field's, and `Δ` commutes with
translation (`laplacian_translate`). -/
theorem laplacian_galV_space {w : ℝ³ → ℝ → ℝ³} (hw : ContDiffOn ℝ ∞ (↿w) slab)
    (m x : ℝ³) {τ : ℝ} (hτ : 0 ≤ τ) :
    Δ (galV m w · τ) x = Δ (w · τ) (x - τ • m) := by
  have hC : ContDiff ℝ ∞ (w · τ) := contDiff_space_slice hw hτ
  have h2 : ContDiffAt ℝ 2 (fun y : ℝ³ => (fun z => w z τ) (y - τ • m)) x :=
    ((hC.comp (contDiff_id.sub contDiff_const)).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  show Δ (((fun _ : ℝ³ => m) + fun y : ℝ³ => (fun z => w z τ) (y - τ • m) : ℝ³ → ℝ³)) x = _
  rw [ContDiffAt.laplacian_add contDiffAt_const h2, laplacian_const,
    laplacian_translate (fun z => w z τ) (τ • m) x]
  simp

/-- The pressure gradient of the boosted pressure at `(x, τ)` is that of `q · τ` at the
moved point (`gradient_translate`). -/
theorem gradient_galP_space {q : ℝ³ → ℝ → ℝ} (m x : ℝ³) (τ : ℝ) :
    gradient (galP m q · τ) x = gradient (q · τ) (x - τ • m) :=
  gradient_translate (fun z => q z τ) (τ • m) x

/-- At time `0` the boosted velocity is `m + w x 0`: the frame change is the identity at
`τ = 0`. -/
theorem galV_zero {w : ℝ³ → ℝ → ℝ³} (m x : ℝ³) : galV m w x 0 = m + w x 0 := by
  simp [galV]

/-- One-periodicity of a time slice passes to the boosted velocity (the moved point shifts
by the same unit vector). -/
theorem isOnePeriodic_galV {w : ℝ³ → ℝ → ℝ³} (m : ℝ³) {τ : ℝ}
    (h : IsOnePeriodic (w · τ)) : IsOnePeriodic (galV m w · τ) := by
  intro x i
  show m + w (x + EuclideanSpace.single i 1 - τ • m) τ = m + w (x - τ • m) τ
  rw [add_sub_right_comm]
  exact congrArg (fun v => m + v) (h (x - τ • m) i)

/-- One-periodicity of a time slice passes to the boosted pressure. -/
theorem isOnePeriodic_galP {q : ℝ³ → ℝ → ℝ} (m : ℝ³) {τ : ℝ}
    (h : IsOnePeriodic (q · τ)) : IsOnePeriodic (galP m q · τ) := by
  intro x i
  show q (x + EuclideanSpace.single i 1 - τ • m) τ = q (x - τ • m) τ
  rw [add_sub_right_comm]
  exact h (x - τ • m) i

/-- Divergence-freeness of a time slice passes to the boosted velocity
(`fderiv_galV_space`). -/
theorem divergence_galV {w : ℝ³ → ℝ → ℝ³} (m : ℝ³) {τ : ℝ}
    (h : ∀ x, Community.divergence (w · τ) x = 0) (x : ℝ³) :
    Community.divergence (galV m w · τ) x = 0 := by
  unfold Community.divergence
  rw [fderiv_galV_space m x τ]
  exact h (x - τ • m)

/-- **THE CLASS TRANSFER (textbook Galilean invariance)**: a member of OUR COPY of the community
class at datum `w₀`, force `0`, boosted by a constant velocity `m`, is a member at datum
`m + w₀`.  Mathlib and the `Community` definitions only; no coefficient-side fact. -/
theorem galilean_class {ν' : ℝ} {w₀ : ℝ³ → ℝ³} {w : ℝ³ → ℝ → ℝ³} {q : ℝ³ → ℝ → ℝ} (m : ℝ³)
    (h : NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' w₀ (f := 0) w q) :
    NavierStokesExistenceAndSmoothnessPeriodic (n := 3) ν' (fun x => m + w₀ x) (f := 0)
      (galV m w) (galP m q) := by
  refine ⟨⟨?_, ?_, ?_, contDiffOn_galV h.velocity_smooth, contDiffOn_galP h.pressure_smooth⟩,
    ?_, ?_⟩
  · -- navier_stokes
    intro x τ hτ
    have hns := h.navier_stokes (x - τ • m) τ hτ
    rw [derivWithin_galV_time h.velocity_smooth m x hτ, convection_galV,
      laplacian_galV_space h.velocity_smooth m x hτ, gradient_galP_space]
    simp only [Pi.zero_apply, add_zero] at hns ⊢
    rw [← hns]
    abel
  · -- div_free
    intro x τ hτ
    exact divergence_galV m (fun y => h.div_free y τ hτ) x
  · -- initial_condition
    intro x
    rw [galV_zero, h.initial_condition]
  · -- isOnePeriodic_velocity
    intro τ hτ
    exact isOnePeriodic_galV m (h.isOnePeriodic_velocity τ hτ)
  · -- isOnePeriodic_pressure
    intro τ hτ
    exact isOnePeriodic_galP m (h.isOnePeriodic_pressure τ hτ)

end

end TheoremB
