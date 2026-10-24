/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Probability.BitString.AffineHash
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Complexity.Computability.Circuit.Boolean.Iteration.Selection
import Complexity.Computability.Circuit.Boolean.Synthesis
import Complexity.Foundations.Data.BitString.Basic

/-!
# Autonomous controllers and affine-payload iteration bounds

When a state splits into an autonomous controller and a payload (`controlledMap`), the controller
evolves independently of the payload and each step applies a controller-selected transformation to
the payload. Iterating for `T` steps therefore applies `g^[T]` to the controller and the composite
payload map `controlledPayload g a T u` to the payload (`controlledMap_iterate`,
`controlledBits_iterate`). Whenever the payload maps belong to a composition-closed family
containing the identity, every iterate's payload map remains in that family
(`controlledPayload_mem`).

On `q` controller bits and `p` payload bits (`controlledBits`), if every payload transformation in a
composition-closed family has a Boolean circuit of size at most `K`, then every fixed iterate
`(controlledBits g a)^[T]` has a circuit of size at most `2 + 2 ^ q * (K + 6 * q + 4 * p + 1)`
(`controlled_family_power`), and an `m`-bit input time costs at most
`m * (2 + 2 ^ q * (K + 6 * q + 4 * p + 1) + 4 * (q + p))` (`controlled_family_variable_time`). No
circuit for the controller transition `g` is assumed or needed: the circuit enumerates all `2 ^ q`
controller states, hardwires `g^[T] u`, runs the circuit for `controlledPayload g a T u`, and
selects the active record.

In particular, affine maps `BitString p →ᵃ[Bool] BitString p` over `Bool` are closed under
composition and are computed by circuits of size at most `p * (5 * (p + 1) + 1)` via their
affine-hash representation (`affineHash_circuit`, `affineHash_affineMapSeed`,
`affine_payload_circuit`). Every fixed iterate of an autonomous `q`-bit controller with a `p`-bit
affine payload therefore has a circuit of size at most `affineControllerBudget q p ≤
32 * 2 ^ q * (q + p ^ 2 + 1)` (`affine_controller_power`, `affineControllerBudget_le`), which is
polynomial in the total width whenever `2 ^ q` is (`affine_controller_polynomial`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.controlledMap`: product map with an autonomous controller and a
  controller-selected payload map.
* `Cslib.Circuits.Boolean.Iteration.controlledPayload`: composite payload transformation after `T`
  steps from a given initial controller state.
* `Cslib.Circuits.Boolean.Iteration.controlledBits`: flat bit-string encoding of a `q`-bit
  controller followed by a `p`-bit payload.
* `Cslib.Circuits.Boolean.Iteration.affineMapSeed`: matrix and offset seed representing a Boolean
  affine map as an affine hash.
* `Cslib.Circuits.Boolean.Iteration.affineControllerBudget`: exact gate budget for a `q`-bit
  autonomous controller with a `p`-bit affine payload.

## Main results

* `Cslib.Circuits.Boolean.Iteration.controlledMap_iterate`,
  `Cslib.Circuits.Boolean.Iteration.controlledBits_iterate`: exact characterization of iterates of a
  controlled map.
* `Cslib.Circuits.Boolean.Iteration.controlledPayload_mem`: closure of composite payload maps in any
  composition-closed family.
* `Cslib.Circuits.Boolean.Iteration.controlled_circuit`,
  `Cslib.Circuits.Boolean.Iteration.controlled_family_power`,
  `Cslib.Circuits.Boolean.Iteration.controlled_family_variable_time`: circuit size bounds for
  selecting and iterating bounded-cost payload families.
* `Cslib.Circuits.Boolean.Iteration.affineHash_circuit`,
  `Cslib.Circuits.Boolean.Iteration.affine_payload_circuit`: quadratic-size circuits for affine
  hashes and Boolean affine maps.
* `Cslib.Circuits.Boolean.Iteration.affine_controller_power`,
  `Cslib.Circuits.Boolean.Iteration.affineControllerBudget_le`,
  `Cslib.Circuits.Boolean.Iteration.affine_controller_polynomial`,
  `Cslib.Circuits.Boolean.Iteration.affine_controller_variable_time`: fixed-power, polynomial, and
  input-time circuit bounds for autonomous controllers with affine payloads.

## References

* Adapted from lean/Proofs/{ControlledMaps,AffinePayload,AffineController}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.BitString.LinearHash
open scoped BigOperators

universe u v

variable {α : Type u} {β : Type v} {q p : ℕ}

/-! ### Autonomous controllers and composite payloads -/

/-- An autonomous controller chooses the transformation of a payload. -/
def controlledMap (g : α → α) (a : α → β → β) (x : α × β) : α × β :=
  (g x.1, a x.1 x.2)

/-- The composite payload map selected by an initial controller and fixed time. -/
def controlledPayload (g : α → α) (a : α → β → β) : ℕ → α → β → β
  | 0, _ => id
  | T + 1, u => a (g^[T] u) ∘ controlledPayload g a T u

/-- Iterating a controlled map advances the autonomous controller and applies the composite
payload map. -/
theorem controlledMap_iterate (g : α → α) (a : α → β → β) (T : ℕ) (u : α) (v : β) :
    (controlledMap g a)^[T] (u, v) = (g^[T] u, controlledPayload g a T u v) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

/-- Composition closure suffices semantically, without any finite-state hypothesis. -/
theorem controlledPayload_mem (g : α → α) (a : α → β → β)
    (family : Set (β → β)) (hid : id ∈ family)
    (hcomp : ∀ f ∈ family, ∀ h ∈ family, f ∘ h ∈ family)
    (ha : ∀ u, a u ∈ family) (T : ℕ) (u : α) :
    controlledPayload g a T u ∈ family := by
  induction T with
  | zero => exact hid
  | succ T ih => exact hcomp _ (ha _) _ ih

/-- Flat Boolean encoding of a `q`-bit controller followed by a `p`-bit payload. -/
def controlledBits (g : BitString q → BitString q)
    (a : BitString q → BitString p → BitString p) (x : BitString (q + p)) :
    BitString (q + p) :=
  Fin.append (g fun i => x (Fin.castAdd p i))
    (a (fun i => x (Fin.castAdd p i)) (fun i => x (Fin.natAdd q i)))

/-- Applying `controlledBits g a` to `Fin.append u v` yields `Fin.append (g u) (a u v)`. -/
@[simp] theorem controlledBits_append (g : BitString q → BitString q)
    (a : BitString q → BitString p → BitString p) (u : BitString q) (v : BitString p) :
    controlledBits g a (Fin.append u v) = Fin.append (g u) (a u v) := by
  simp [controlledBits]

/-- Iterating `controlledBits` is `controlledBits` with the iterated controller and composite
payload map. -/
theorem controlledBits_iterate (g : BitString q → BitString q)
    (a : BitString q → BitString p → BitString p) (T : ℕ) (x : BitString (q + p)) :
    (controlledBits g a)^[T] x = controlledBits (g^[T]) (controlledPayload g a T) x := by
  induction T with
  | zero => simp [controlledBits, controlledPayload, Fin.append_castAdd_natAdd]
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [controlledBits, Fin.append_left, Fin.append_right, controlledPayload,
      Function.comp_apply, Function.iterate_succ_apply']

/-! ### Selecting and powering bounded-cost payload families -/

/-- Selecting among small payload circuits has overhead linear in controller and output width per
controller value. No circuit for `g` is assumed or needed. -/
theorem controlled_circuit (g : BitString q → BitString q)
    (a : BitString q → BitString p → BitString p) (K : ℕ)
    (ha : ∀ u, ∃ c : Circuit signature p p, c.Computes interpretation (a u) ∧ c.size ≤ K) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation (controlledBits g a) ∧
      c.size ≤ 2 + 2 ^ q * (K + 6 * q + 4 * p + 1) := by
  classical
  let e : Fin (2 ^ q) ≃ BitString q := (BitString.equivFin q).symm
  let u := fun x : BitString (q + p) => fun i => x (Fin.castAdd p i)
  let v := fun x : BitString (q + p) => fun i => x (Fin.natAdd q i)
  let flags := fun j x => decide (u x = e j)
  let records := fun j x => Fin.append (g (e j)) (a (e j) (v x))
  let constants : Set (BooleanFunction (q + p)) := {fun _ => false, fun _ => true}
  let src := inputs (q + p) ∪ constants
  have hc (b : Bool) : (fun _ : BitString (q + p) => b) ∈ src := by
    cases b <;> simp [src, constants]
  have hconst : Synthesis interpretation (inputs (q + p)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hflag (j : Fin (2 ^ q)) :
      Synthesis interpretation src {flags j} (2 * q + 1) := by
    have h := Synthesis.word_eq_const (s := src) (fun x => word (u x))
      (fun i => by
        simpa [u, getLsbD_word] using
          (show (fun x : BitString (q + p) => x (Fin.castAdd p i)) ∈ src from Or.inl ⟨_, rfl⟩))
      (word (e j))
    have he (x : BitString (q + p)) : word (u x) = word (e j) ↔ u x = e j := by
      constructor
      · intro hh
        funext i
        simpa only [getLsbD_word] using congrArg (fun w : BitVec q => w.getLsbD i.val) hh
      · exact congrArg word
    simpa only [he] using h
  have hrecord (j : Fin (2 ^ q)) :
      Synthesis interpretation src (wires (records j)) K := by
    obtain ⟨c, hc', hs⟩ := ha (e j)
    have h := Synthesis.circuit (I := interpretation) (s := src) c (fun i x => v x i)
      (fun i => Or.inl ⟨_, rfl⟩)
    have heval : c.eval interpretation = a (e j) := funext hc'
    rw [heval] at h
    have hav : wires (records j) ⊆ src ∪ wires (fun x => a (e j) (v x)) := by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        apply Or.inl
        simpa only [records, Fin.append_left] using hc (g (e j) i)
      | right i =>
        apply Or.inr
        exact ⟨i, by simp only [records, Fin.append_right]⟩
    exact (h.trans (Synthesis.of_subset hav)).mono Set.Subset.rfl Set.Subset.rfl
      (by simpa using hs)
  have hall := Synthesis.iUnion (fun j => {flags j} ∪ wires (records j))
    (fun _ => (2 * q + 1) + K) (fun j => (hflag j).union (hrecord j))
  let all := ⋃ j, {flags j} ∪ wires (records j)
  have hselect := synthesis_chooseRecord (src ∪ all)
    (fun x j => flags j x) (fun x j => records j x) (fun _ _ => false)
    (fun j => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inl rfl⟩))
    (fun j bit => Or.inr (Set.mem_iUnion.mpr ⟨j, Or.inr ⟨bit, rfl⟩⟩))
    (fun _ => Or.inl (hc false))
  have he (x : BitString (q + p)) :
      chooseRecord (fun j => flags j x) (fun j => records j x) (fun _ => false) (2 ^ q) =
        controlledBits g a x := by
    obtain ⟨j, _, hj, hout⟩ := chooseRecord_spec (fun j => flags j x)
      (fun j => records j x) (fun _ => false) (2 ^ q)
      ⟨e.symm (u x), (e.symm (u x)).isLt, by simp [flags]⟩
    have hj' : u x = e j := of_decide_eq_true hj
    rw [hout]
    change Fin.append (g (e j)) (a (e j) (v x)) = Fin.append (g (u x)) (a (u x) (v x))
    rw [hj']
  simp only [he] at hselect
  obtain ⟨c, hc', hs⟩ := (hconst.trans (hall.trans hselect)).exists_circuit_outputs
  refine ⟨c, hc', hs.trans ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- A composition-closed payload family with a uniform gate bound can be powered at a cost
exponential only in the controller width. -/
theorem controlled_family_power (g : BitString q → BitString q)
    (a : BitString q → BitString p → BitString p) (family : Set (BitString p → BitString p))
    (hid : id ∈ family) (hcomp : ∀ f ∈ family, ∀ h ∈ family, f ∘ h ∈ family)
    (ha : ∀ u, a u ∈ family) (K : ℕ)
    (hK : ∀ f ∈ family, ∃ c : Circuit signature p p,
      c.Computes interpretation f ∧ c.size ≤ K) (T : ℕ) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation ((controlledBits g a)^[T]) ∧
      c.size ≤ 2 + 2 ^ q * (K + 6 * q + 4 * p + 1) := by
  obtain ⟨c, hc, hs⟩ := controlled_circuit (g^[T]) (controlledPayload g a T) K
    (fun u => hK _ (controlledPayload_mem g a family hid hcomp ha T u))
  exact ⟨c, fun x => (hc x).trans (controlledBits_iterate g a T x).symm, hs⟩

/-- The same closed family supports an input exponent by conditional binary powers. -/
theorem controlled_family_variable_time (g : BitString q → BitString q)
    (a : BitString q → BitString p → BitString p) (family : Set (BitString p → BitString p))
    (hid : id ∈ family) (hcomp : ∀ f ∈ family, ∀ h ∈ family, f ∘ h ∈ family)
    (ha : ∀ u, a u ∈ family) (K : ℕ)
    (hK : ∀ f ∈ family, ∃ c : Circuit signature p p,
      c.Computes interpretation f ∧ c.size ≤ K) (m : ℕ) :
    ∃ c : Circuit signature ((q + p) + m) (q + p),
      c.Computes interpretation (inputTimeIterate (controlledBits g a) m) ∧
      c.size ≤ m * (2 + 2 ^ q * (K + 6 * q + 4 * p + 1) + 4 * (q + p)) :=
  binary_powering (controlledBits g a) m (2 + 2 ^ q * (K + 6 * q + 4 * p + 1))
    fun j _ => controlled_family_power g a family hid hcomp ha K hK (2 ^ j)

/-! ### Affine payloads and affine-controller bounds -/

/-- Every affine hash `x ↦ A x + b` from `n` bits to `k` bits has a De Morgan circuit of size at
most `k * (5 * (n + 1) + 1)`. -/
theorem affineHash_circuit {k n : ℕ} (seed : (Fin k → BitString n) × BitString k) :
    ∃ c : Circuit signature n k,
      c.Computes interpretation (affineHash seed) ∧ c.size ≤ k * (5 * (n + 1) + 1) := by
  have hrow (row : Fin k) :
      Synthesis interpretation (inputs n) {fun x => affineHash seed x row}
        (5 * (n + 1) + 1) := by
    let term (j : Fin (n + 1)) (x : BitString n) : Bool :=
      Fin.snoc (α := fun _ => Bool) (fun i => seed.1 row i * x i) (seed.2 row) j
    have hterm (j : Fin (n + 1)) :
        Synthesis interpretation (inputs n) {term j} 1 := by
      induction j using Fin.lastCases with
      | last =>
        simpa only [term, Fin.snoc_last] using Synthesis.const (seed.2 row)
      | cast i =>
        simp only [term, Fin.snoc_castSucc]
        cases seed.1 row i
        · simpa only [Bool.mul_eq_and, Bool.false_and] using Synthesis.const false
        · simpa only [Bool.mul_eq_and, Bool.true_and] using
            (Synthesis.of_mem (s := inputs n) ⟨i, rfl⟩).mono
              Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1)
    have hsum := Synthesis.sum (s := inputs n) (Finset.univ : Finset (Fin (n + 1)))
      term (fun _ => 1) fun j _ => hterm j
    have heq : (fun x : BitString n => ∑ j : Fin (n + 1), term j x) =
        fun x => affineHash seed x row := by
      funext x
      rw [Fin.sum_univ_castSucc]
      simp only [term, Fin.snoc_castSucc, Fin.snoc_last, affineHash, BitString.LinearHash.hash,
        dotProduct, Pi.add_apply]
    rw [heq] at hsum
    refine hsum.mono Set.Subset.rfl Set.Subset.rfl ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    omega
  have hfam := Synthesis.family (I := interpretation) (s := inputs n)
    (fun row x => affineHash seed x row) (fun _ => 5 * (n + 1) + 1) hrow
  obtain ⟨c, hc, hs⟩ := hfam.exists_circuit_outputs
  refine ⟨c, hc, hs.trans ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, le_rfl]

/-- The matrix and offset seed of a Boolean affine map. -/
def affineMapSeed (a : BitString p →ᵃ[Bool] BitString p) :
    (Fin p → BitString p) × BitString p :=
  (fun i j => a.linear (Pi.single j 1) i, a 0)

/-- Evaluating the affine hash at `affineMapSeed a` recovers the affine map `a`. -/
theorem affineHash_affineMapSeed (a : BitString p →ᵃ[Bool] BitString p) (v : BitString p) :
    affineHash (affineMapSeed a) v = a v := by
  have hlinear : a.linear v = ∑ j, v j • a.linear (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul]
  have ha : a v = a.linear v + a 0 := congrFun a.decomp v
  funext i
  rw [ha, hlinear]
  simp only [affineHash, affineMapSeed, BitString.LinearHash.hash, dotProduct, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Every affine Boolean payload has a De Morgan circuit of size at most `p * (5 * (p + 1) + 1)`. -/
theorem affine_payload_circuit (a : BitString p →ᵃ[Bool] BitString p) :
    ∃ c : Circuit signature p p,
      c.Computes interpretation a ∧ c.size ≤ p * (5 * (p + 1) + 1) := by
  obtain ⟨c, hc, hs⟩ := affineHash_circuit (affineMapSeed a)
  exact ⟨c, fun v => (hc v).trans (affineHash_affineMapSeed a v), hs⟩

/-- Exact gate budget from affine payload evaluation and autonomous controller selection. -/
def affineControllerBudget (q p : ℕ) : ℕ :=
  2 + 2 ^ q * (p * (5 * (p + 1) + 1) + 6 * q + 4 * p + 1)

/-- Every fixed power has size exponential only in the autonomous controller width. -/
theorem affine_controller_power (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (T : ℕ) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ affineControllerBudget q p := by
  let family : Set (BitString p → BitString p) :=
    Set.range fun f : BitString p →ᵃ[Bool] BitString p => ⇑f
  apply controlled_family_power g (fun u => a u) family
    (show id ∈ family from ⟨AffineMap.id Bool (BitString p), rfl⟩)
    (fun _ ⟨f, hf⟩ _ ⟨h, hh⟩ => ?_) (fun u => ⟨a u, rfl⟩)
    (p * (5 * (p + 1) + 1)) (fun _ ⟨f, hf⟩ => ?_) T
  · exact ⟨f.comp h, by simp only [← hf, ← hh]; rfl⟩
  · exact hf ▸ affine_payload_circuit f

/-- The exact budget is `O(2 ^ q * (q + p ^ 2 + 1))`, including zero-width cases. -/
theorem affineControllerBudget_le (q p : ℕ) :
    affineControllerBudget q p ≤ 32 * 2 ^ q * (q + p ^ 2 + 1) := by
  have hp : p ≤ p ^ 2 := by nlinarith
  have hb : p * (5 * (p + 1) + 1) + 6 * q + 4 * p + 1 ≤
      16 * (q + p ^ 2 + 1) := by nlinarith
  have hpow : 1 ≤ 2 ^ q := Nat.one_le_pow q 2 (by decide)
  have := Nat.mul_le_mul_left (2 ^ q) hb
  unfold affineControllerBudget
  nlinarith

/-- Polynomially many controller states give a polynomial gate bound in the total width, uniformly
over all fixed exponents. -/
theorem affine_controller_polynomial (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (K d : ℕ)
    (hcontroller : 2 ^ q ≤ K * (q + p + 1) ^ d) (T : ℕ) :
    ∃ c : Circuit signature (q + p) (q + p),
      c.Computes interpretation ((controlledBits g (fun u => a u))^[T]) ∧
      c.size ≤ 32 * K * (q + p + 1) ^ (d + 2) := by
  obtain ⟨c, hc, hs⟩ := affine_controller_power g a T
  refine ⟨c, hc, hs.trans ((affineControllerBudget_le q p).trans ?_)⟩
  have hwidth : q + p ^ 2 + 1 ≤ (q + p + 1) ^ 2 := by
    nlinarith only [Nat.zero_le q, Nat.zero_le p,
      Nat.zero_le (q * p), Nat.zero_le (q * q)]
  calc
    32 * 2 ^ q * (q + p ^ 2 + 1) ≤
        32 * (K * (q + p + 1) ^ d) * (q + p + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 32 hcontroller) hwidth
    _ = 32 * K * (q + p + 1) ^ (d + 2) := by rw [pow_add]; ring

/-- An input time uses the same fixed-power bound at each conditional binary stage. -/
theorem affine_controller_variable_time (g : BitString q → BitString q)
    (a : BitString q → (BitString p →ᵃ[Bool] BitString p)) (m : ℕ) :
    ∃ c : Circuit signature ((q + p) + m) (q + p),
      c.Computes interpretation (inputTimeIterate (controlledBits g (fun u => a u)) m) ∧
      c.size ≤ m * (affineControllerBudget q p + 4 * (q + p)) :=
  binary_powering (controlledBits g (fun u => a u)) m (affineControllerBudget q p)
    fun j _ => affine_controller_power g a (2 ^ j)

end Cslib.Circuits.Boolean.Iteration
