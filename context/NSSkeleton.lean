/-
  NSSkeleton.lean  (v2, extended 26 Aug 2026, second session)
  Machine-checked logical skeletons of the two Navier-Stokes theorems
  proved in the expedition (core Lean 4, no Mathlib):

  * Theorem B skeleton (`trap_invariance`): a downward-closed safe set,
    together with dynamics that never ascend while inside it, traps the
    orbit forever.  Analytic reading: S = {kappa*E*Z < nu^4}, descent =
    monotone decay of E (energy identity) and of Z (master inequality).

  * Theorem A skeleton (`riccati_comparison`): any orbit dominated
    stepwise by a monotone map stays below the exact orbit of that map.
    Analytic reading: f(z) = z + c*z^3 is the discretized Riccati
    majorant of dZ/dt <= kappa Z^3 / nu^3.

  * NEW in v2 (`safety_window`, `safety_concrete`): the quantitative
    Theorem A.  Not just "dominated by the majorant" but an explicit
    horizon with an explicit constant: while n * (c * (2*Z0)^3) <= Z0,
    the enstrophy history grows at most linearly and never exceeds
    2 * Z0.  Solving the horizon condition for n gives
    N = 1 / (8 * c * Z0^2) steps; with c = kappa * dt / nu^3 this is
    the discrete shadow of T_safe = nu^3 / (2 * kappa * Z0^2), the
    constant 8 (vs 2) being the price of the crude 2*Z0 cage instead
    of integrating the Riccati ODE exactly.

  The analytic flesh (derivatives, Sobolev embeddings, the PDE itself)
  lives in the paper proof; here the induction hearts are verified by
  the Lean kernel, with the axiom audit printed at the bottom.
-/

namespace NSSkeleton

/-- **Theorem B skeleton.**  If `S` is downward closed for `le`, the
orbit `x` never ascends while inside `S`, and `x 0` starts inside `S`,
then the orbit stays in `S` forever and never rises above `x 0`. -/
theorem trap_invariance {α : Type} (le : α → α → Prop)
    (hrefl : ∀ a, le a a)
    (htrans : ∀ {a b c}, le a b → le b c → le a c)
    (S : α → Prop)
    (hdc : ∀ {a b}, le a b → S b → S a)
    (x : Nat → α)
    (hstep : ∀ n, S (x n) → le (x (n + 1)) (x n))
    (h0 : S (x 0)) :
    ∀ n, S (x n) ∧ le (x n) (x 0) := by
  intro n
  induction n with
  | zero => exact ⟨h0, hrefl (x 0)⟩
  | succ k ih =>
    have hS : S (x k) := ih.1
    have hdown : le (x (k + 1)) (x k) := hstep k hS
    exact ⟨hdc hdown hS, htrans hdown ih.2⟩

/-- **Theorem A skeleton.**  A stepwise-dominated orbit stays below the
exact orbit of a monotone majorant map. -/
theorem riccati_comparison {α : Type} (le : α → α → Prop)
    (htrans : ∀ {a b c}, le a b → le b c → le a c)
    (f : α → α)
    (hmono : ∀ {a b}, le a b → le (f a) (f b))
    (x w : Nat → α)
    (hx : ∀ n, le (x (n + 1)) (f (x n)))
    (hw : ∀ n, w (n + 1) = f (w n))
    (h0 : le (x 0) (w 0)) :
    ∀ n, le (x n) (w n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
    have h1 : le (x (k + 1)) (f (x k)) := hx k
    have h2 : le (f (x k)) (f (w k)) := hmono ih
    have h3 : le (x (k + 1)) (f (w k)) := htrans h1 h2
    rw [hw k]
    exact h3

/-- Concrete Theorem B over scaled integer quantities: if energy `E` and
enstrophy `Z` can only fall while `kappa * E n * Z n < nu4`, and the
initial data satisfies the smallness condition, then the condition
persists forever and the enstrophy never exceeds its initial value.
This is the induction heart of global small-data regularity. -/
theorem trap_concrete (kappa nu4 : Nat) (E Z : Nat → Nat)
    (hE : ∀ n, kappa * E n * Z n < nu4 → E (n + 1) ≤ E n)
    (hZ : ∀ n, kappa * E n * Z n < nu4 → Z (n + 1) ≤ Z n)
    (h0 : kappa * E 0 * Z 0 < nu4) :
    ∀ n, kappa * E n * Z n < nu4 ∧ Z n ≤ Z 0 := by
  have main :=
    trap_invariance (α := Nat × Nat)
      (le := fun p q => p.1 ≤ q.1 ∧ p.2 ≤ q.2)
      (hrefl := fun a => ⟨Nat.le_refl a.1, Nat.le_refl a.2⟩)
      (htrans := fun hab hbc =>
        ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩)
      (S := fun p => kappa * p.1 * p.2 < nu4)
      (hdc := fun {a b} hab hSb =>
        Nat.lt_of_le_of_lt
          (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl kappa) hab.1) hab.2)
          hSb)
      (x := fun n => (E n, Z n))
      (hstep := fun n hS => ⟨hE n hS, hZ n hS⟩)
      (h0 := h0)
  intro n
  exact ⟨(main n).1, (main n).2.2⟩

/-- Concrete Theorem A over scaled integer quantities: an enstrophy
history obeying the discrete Riccati bound `Z (n+1) ≤ Z n + c * Z n ^ 3`
is dominated by the exact Riccati orbit started at or above it.  This is
the induction heart of the safety-time bound. -/
theorem riccati_concrete (c : Nat) (x w : Nat → Nat)
    (hx : ∀ n, x (n + 1) ≤ x n + c * x n ^ 3)
    (hw : ∀ n, w (n + 1) = w n + c * w n ^ 3)
    (h0 : x 0 ≤ w 0) :
    ∀ n, x n ≤ w n :=
  riccati_comparison (α := Nat)
    (le := fun a b => a ≤ b)
    (htrans := fun hab hbc => Nat.le_trans hab hbc)
    (f := fun a => a + c * a ^ 3)
    (hmono := fun {a b} h =>
      Nat.add_le_add h (Nat.mul_le_mul (Nat.le_refl c) (Nat.pow_le_pow_left h 3)))
    (x := x) (w := w) (hx := hx) (hw := hw) (h0 := h0)

/-- **Quantitative Theorem A skeleton (safety window), NEW in v2.**
Write `s = c * (2 * x 0) ^ 3` for the worst-case per-step growth of an
orbit still capped by `2 * x 0`.  Any history obeying the discrete
Riccati bound `x (n+1) ≤ x n + c * x n ^ 3` grows at most linearly,
`x n ≤ x 0 + n * s`, for every `n` inside the horizon `n * s ≤ x 0`.
Solving the horizon for `n` gives `N = 1 / (8 * c * x 0 ^ 2)` steps,
the discrete shadow of `T_safe = ν³ / (2 κ Z₀²)`. -/
theorem safety_window (c : Nat) (x : Nat → Nat)
    (hx : ∀ n, x (n + 1) ≤ x n + c * x n ^ 3) :
    ∀ n, n * (c * (2 * x 0) ^ 3) ≤ x 0 →
      x n ≤ x 0 + n * (c * (2 * x 0) ^ 3) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.zero_mul]
    exact Nat.le_add_right (x 0) 0
  | succ k ih =>
    intro hk1
    -- the horizon at k + 1 implies the horizon at k
    have hmono : k * (c * (2 * x 0) ^ 3) ≤ (k + 1) * (c * (2 * x 0) ^ 3) :=
      Nat.mul_le_mul (Nat.le_succ k) (Nat.le_refl _)
    have hk : k * (c * (2 * x 0) ^ 3) ≤ x 0 := Nat.le_trans hmono hk1
    -- induction: linear growth up to step k
    have hlin : x k ≤ x 0 + k * (c * (2 * x 0) ^ 3) := ih hk
    -- inside the horizon the orbit is capped by 2 * x 0
    have hcap : x k ≤ 2 * x 0 := by
      have h1 : x 0 + k * (c * (2 * x 0) ^ 3) ≤ x 0 + x 0 :=
        Nat.add_le_add (Nat.le_refl (x 0)) hk
      have h2 : x k ≤ x 0 + x 0 := Nat.le_trans hlin h1
      rw [Nat.two_mul]
      exact h2
    -- the cap tames the cube, hence the per-step growth
    have hcube : x k ^ 3 ≤ (2 * x 0) ^ 3 := Nat.pow_le_pow_left hcap 3
    have hstep : c * x k ^ 3 ≤ c * (2 * x 0) ^ 3 :=
      Nat.mul_le_mul (Nat.le_refl c) hcube
    -- one Riccati step stays under the linear envelope
    have hgrow : x (k + 1)
        ≤ (x 0 + k * (c * (2 * x 0) ^ 3)) + c * (2 * x 0) ^ 3 :=
      Nat.le_trans (hx k) (Nat.add_le_add hlin hstep)
    have hexp : (k + 1) * (c * (2 * x 0) ^ 3)
        = k * (c * (2 * x 0) ^ 3) + c * (2 * x 0) ^ 3 :=
      Nat.succ_mul k (c * (2 * x 0) ^ 3)
    rw [hexp, ← Nat.add_assoc]
    exact hgrow

/-- **Theorem A end to end (discrete, explicit constants), NEW in v2.**
Inside the horizon `n * (c * (2 * x 0) ^ 3) ≤ x 0`, a history obeying
the discrete Riccati bound never exceeds twice its initial value. -/
theorem safety_concrete (c : Nat) (x : Nat → Nat)
    (hx : ∀ n, x (n + 1) ≤ x n + c * x n ^ 3) :
    ∀ n, n * (c * (2 * x 0) ^ 3) ≤ x 0 → x n ≤ 2 * x 0 := by
  intro n hn
  have h1 : x n ≤ x 0 + n * (c * (2 * x 0) ^ 3) := safety_window c x hx n hn
  have h2 : x 0 + n * (c * (2 * x 0) ^ 3) ≤ x 0 + x 0 :=
    Nat.add_le_add (Nat.le_refl (x 0)) hn
  have h3 : x n ≤ x 0 + x 0 := Nat.le_trans h1 h2
  rw [Nat.two_mul]
  exact h3

end NSSkeleton

#print axioms NSSkeleton.trap_concrete
#print axioms NSSkeleton.riccati_concrete
#print axioms NSSkeleton.safety_window
#print axioms NSSkeleton.safety_concrete
