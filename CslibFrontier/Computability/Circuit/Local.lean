/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.WireNumber

/-!
# Local labelling rounds

A *labelling* assigns a value to every wire of a circuit, and a *round* `S` computes a new
labelling from an old one. A round is local when the new value of each wire depends only on the
old values of lower-numbered wires, as for one round of evaluation on an ordered topology. Wire
numbers are those of `Cslib.Circuits.Wire.toNat`.

Iterating a local round `n + s` times, once per wire, reaches its unique fixed labelling from any
start. Garbling schemes use this to compute labels by iteration and to identify the result with a
labelling given in closed form.

## Main definitions

* `Cslib.Circuits.IsLocal`: the new value of each wire depends only on lower-numbered wires.

## Main results

* `Cslib.Circuits.IsLocal.isFixed_iterate`: `n + s` rounds reach a labelling the round fixes.
* `Cslib.Circuits.IsLocal.iterate_eq_of_isFixed`: every labelling the round fixes is the
  `n + s`-fold iterate from any start.
* `Cslib.Circuits.IsLocal.eq_of_isFixed`: a local round fixes at most one labelling.
-/

public section

namespace Cslib.Circuits

variable {n s : ℕ} {α : Type*}

/-- A labelling round is *local* when the new label of a wire depends only on the labels of
lower-numbered wires. -/
@[expose] def IsLocal (S : (Wire n s → α) → Wire n s → α) : Prop :=
  ∀ A B w, (∀ v : Wire n s, v.toNat < w.toNat → A v = B v) → S A w = S B w

namespace IsLocal

variable {S : (Wire n s → α) → Wire n s → α}

theorem iterate_succ (hS : IsLocal S) (B : Wire n s → α) :
    ∀ t (w : Wire n s), w.toNat < t → S^[t + 1] B w = S^[t] B w := by
  intro t
  induction t with
  | zero => intro w hw; exact absurd hw (Nat.not_lt_zero _)
  | succ t ih =>
    intro w hw
    calc S^[t + 1 + 1] B w = S (S^[t + 1] B) w := by rw [Function.iterate_succ_apply' S (t + 1)]
      _ = S (S^[t] B) w := hS _ _ w fun v hv => ih v (by omega)
      _ = S^[t + 1] B w := by rw [Function.iterate_succ_apply' S t]

/-- Iterating a local round `n + s` times reaches a labelling it fixes. -/
theorem isFixed_iterate (hS : IsLocal S) (B : Wire n s → α) :
    S (S^[n + s] B) = S^[n + s] B := by
  funext w
  rw [← Function.iterate_succ_apply' S]
  exact hS.iterate_succ B _ w w.toNat_lt

/-- Every labelling fixed by a local round is its `n + s`-fold iterate from any start. -/
theorem iterate_eq_of_isFixed (hS : IsLocal S) (B : Wire n s → α) {A : Wire n s → α}
    (hA : S A = A) : S^[n + s] B = A := by
  have key : ∀ t (w : Wire n s), w.toNat < t → S^[t] B w = A w := by
    intro t
    induction t with
    | zero => intro w hw; exact absurd hw (Nat.not_lt_zero _)
    | succ t ih =>
      intro w hw
      rw [Function.iterate_succ_apply', ← hA]
      exact hS _ _ w fun v hv => ih v (by omega)
  exact funext fun w => key _ w w.toNat_lt

/-- A local round fixes at most one labelling. -/
theorem eq_of_isFixed (hS : IsLocal S) {A B : Wire n s → α} (hA : S A = A) (hB : S B = B) :
    A = B :=
  (hS.iterate_eq_of_isFixed A hA).symm.trans (hS.iterate_eq_of_isFixed A hB)

end IsLocal

end Cslib.Circuits
