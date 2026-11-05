/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorTransition
public import Complexity.Computability.WordRAM.GhostLoop

/-!
# The complete charged in-place Chan–He worklist loop

The native loop executes every pending descriptor, including empty and zero-fuel entries.
Traversal work is paid on every descriptor; solver work is paid only for an actual node.
Exhausting the actual stack gives the complete ordered Boolean fold, without a stored catalogue.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- Every reached loop header admits an actual transition paid by the remaining native work
and exact number of mathematical nodes still awaiting a solver call. -/
theorem transition {r κ n w : ℕ} {target : List Node} {a : Arena}
    (c : Host.Callee r)
    (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w)
    (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack +
      a.capacity))
    (s : Cursor) (x : Data (registerCount r))
    (h : s.Invariant a w κ n target x)
    (hc : (Cond.lt (preprocessingRegisters r ChanHe.Traversal.zero)
      (preprocessingRegisters r (ChanHe.Traversal.registers WordStack.len))).Holds x) :
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ (s' : Cursor) (y : Data (registerCount r)) (t : ℕ), ExecWithin (w + 2) (body c.code) x y t ∧
      s'.Invariant a w κ n target y ∧ t + 2 + s'.credit a T ≤ s.credit a T := by
  let T := Host.callerTime (4 * a.N)
    (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
  rcases s with ⟨pending, ns⟩
  cases pending with
  | nil => exact (h.nonempty hc rfl).elim
  | cons e es =>
    by_cases hs : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
        (e.data 1).length = 0 ∨ (e.data 2).length = 0
    · obtain ⟨y, hy, hi, _, _, hpay, _⟩ := skip_transition c.code e es ns x
        ha h2 hcap h hs
      exact ⟨⟨es, ns⟩, y, 107, hy, hi, by
        change 107 + 2 + (Cursor.mk es ns).credit a T ≤
          (Cursor.mk (e :: es) ns).credit a T
        exact hpay T⟩
    · obtain ⟨s', y, hy, hi, hremaining, hdec, _⟩ := live_transition c e es ns x
        hw ha hresources hready h2 hcap h (fun he => hs (Or.inl he)) (by
          intro j
          fin_cases j
          · exact fun he => hs (Or.inr (Or.inl he))
          · exact fun he => hs (Or.inr (Or.inr (Or.inl he)))
          · exact fun he => hs (Or.inr (Or.inr (Or.inr he))))
      refine ⟨s', y, visitTime a.n a.m a.N + 314 + T, hy, hi, ?_⟩
      have hlen : ((Cursor.mk (e :: es) ns).remaining a).length =
          (s'.remaining a).length + 1 := by
        rw [hremaining, List.length_cons]
      have hwork := Nat.mul_le_mul_right (visitTime a.n a.m a.N + 316) hdec
      simp only [Nat.add_mul, Nat.one_mul] at hwork
      change visitTime a.n a.m a.N + 314 + T + 2 +
        (s'.work * (visitTime a.n a.m a.N + 316) + (s'.remaining a).length * T) ≤
        (Cursor.mk (e :: es) ns).work * (visitTime a.n a.m a.N + 316) +
          ((Cursor.mk (e :: es) ns).remaining a).length * T
      rw [hlen, Nat.add_mul, Nat.one_mul]
      omega

/-- Execute the complete actual native loop and consume its exact target preorder.
The charge includes the final test and every live or skipped iteration's loop control. -/
theorem loop_exec {r κ n w : ℕ} {target : List Node} {a : Arena}
    (c : Host.Callee r)
    (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w)
    (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack +
      a.capacity))
    (s : Cursor) (x : Data (registerCount r))
    (h : s.Invariant a w κ n target x) :
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ y, ExecWithin (w + 2)
        (.loop (.lt (preprocessingRegisters r ChanHe.Traversal.zero)
          (preprocessingRegisters r (ChanHe.Traversal.registers WordStack.len))) (body c.code))
        x y (s.credit a T + 2) ∧ (Cursor.mk [] target).Invariant a w κ n target y := by
  let T := Host.callerTime (4 * a.N)
    (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
  obtain ⟨s', y, he, hi, hexit⟩ := ExecWithin.loop_potential_state
    (fun (s : Cursor) (x : Data (registerCount r)) => s.Invariant a w κ n target x)
    (fun (s : Cursor) => s.credit a T)
    (transition c hw ha hresources hready h2 hcap) h
  obtain ⟨hp, hout⟩ := hi.finished hexit
  refine ⟨y, he, ?_⟩
  cases s' with
  | mk pending ns =>
    change pending = [] at hp
    subst pending
    change ns = target at hout
    subst ns
    exact hi

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
