/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveLeaf
public import CslibFrontier.Computability.PolyTime.CountingLeaf.NativeCost

/-!
# Persistent counting leaves with a separated context cost

Preparation and serialization are linear in the actual word lengths. The local arithmetic is
polynomial only in the count, width, path and index lengths; a separate scalar bounds the
primitive predicate's runtime at the decoded address. All clocks refer to the actual persistent
controller configuration, including its path cursor and the freshly written carry selector.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveLeafCost

open MultiTapeTM Cslib.CountingLeaf

/-- Preparation, serialization and raw evaluation, uniform over a bounded path and index. -/
@[expose] def clock (c d : ℕ) (context count width : List Bool)
    (sizeBudget predicateTime : ℕ) : ℕ :=
  sizeBudget + 3 + 2 * (2 * (context.length + count.length + width.length + sizeBudget) + 7) + 5 +
    c * (context.length + (count.length + width.length + sizeBudget + 2) ^ d + predicateTime + 1)

private theorem clock_le (c d : ℕ) (T : List Bool × ℕ → ℕ)
    (context count width path bits : List Bool) (carry : Bool) (sizeBudget predicateTime : ℕ)
    (hb : path.length + bits.length ≤ sizeBudget)
    (ht : T (context, Cslib.BitString.binaryValue path) ≤ predicateTime) :
    path.length + 3 + Native.cost c d T (CarrySaveLeaf.query context count width path bits carry) ≤
      clock c d context count width sizeBudget predicateTime := by
  have he := length_encRawInput_le (CarrySaveLeaf.query context count width path bits carry)
    sizeBudget hb
  have hs : (CarrySaveLeaf.query context count width path bits carry).localSize + 1 ≤
      count.length + width.length + sizeBudget + 2 := by
    simp only [CarrySaveLeaf.query, RawInput.localSize]
    omega
  have hp := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hs d)
  have hp' := Nat.mul_le_mul_left c ht
  simp only [CarrySaveLeaf.query] at he hp
  simp only [Native.cost, CarrySaveLeaf.query, clock, Nat.mul_add]
  omega

/-- One finite native family answers physical counting-leaf queries. A numerical bound on the
primitive predicate's time is sufficient; no complete leaf-answer certificate is assumed. -/
theorem exists_counting (predicate : List Bool × ℕ → Bool) {T S : List Bool × ℕ → ℕ}
    (hp : ComputableInO predicate (encPair encBits encNat) encBool T S) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (leaf : Bool → MultiTapeTM (k + 12) Bool State) (c d : ℕ),
      ∀ (input context count width height bits path unary : List Bool)
        (frontier : ℤ) (status carry : Bool) (sizeBudget predicateTime : ℕ),
      path.length + bits.length ≤ sizeBudget →
      T (context, Cslib.BitString.binaryValue path) ≤ predicateTime →
      let cfg := CarrySaveLeaf.initial k input context count width height bits path unary
        frontier status
      (leaf carry).runFrom (cfg.withState (some (leaf carry).q₀))
        (clock c d context count width sizeBudget predicateTime) =
        (CarrySaveLeaf.completed (CarrySaveLeaf.prepared cfg carry)
          (CarrySaveLeaf.query context count width path bits carry)
          [runRaw predicate (CarrySaveLeaf.query context count width path bits carry)]).withState
            none := by
  obtain ⟨k, State, hState, tm, c, d, hr⟩ := Native.exists_counting_of_inO predicate hp
  let := hState
  refine ⟨k, _, inferInstance, CarrySaveLeaf.leafMachine tm, c, d, ?_⟩
  intro input context count width height bits path unary frontier status carry sizeBudget
    predicateTime hb ht
  have h := CarrySaveLeaf.runFrom_leafMachine tm input context count width height bits path unary
    frontier status carry _ _ (hr (CarrySaveLeaf.query context count width path bits carry) input)
  dsimp only at h ⊢
  rw [runFrom_eq_of_halt _ _ (clock_le c d T context count width path bits carry sizeBudget
    predicateTime hb ht) (by rw [h]; rfl), h]

end Turing.MultiTapeATM.CarrySaveLeafCost
