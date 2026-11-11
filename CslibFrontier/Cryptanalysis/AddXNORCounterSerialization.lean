/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClasses
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.BinaryPairSums
public import CslibFrontier.Computability.GenericRAM.Native.Certificate
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.BinaryPairSums
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import all CslibFrontier.Cryptanalysis.AddXNORReachability

/-!
# Binary serialization of the reachable-state counter update

[WangLvShenZhang2027], Lemma 8 (PDF pp. 21–22), obtains all low-bit class counts
from a counter at every projected state. Here the two pulled tables of an actual
DP layer are serialized as corresponding pairs, in zero-child/one-child order.
The streaming binary-addition machine computes precisely the next table's leaves.
For both chain directions its actual time and charged prefix workspace on this
input are `2^m` times a polynomial in the original operator count, including zero
counters and coinciding branches. Counter width is derived from the original DP.

This is an arithmetic/serialization stage, not a complete bit-machine DP compiler.
The separate `CounterPairing` route realizes the pull/pair/add pass in numeric
state order. Initialization, numeric-key restoration, the operand loop and readback
still need resource-faithful tape composition. In particular this theorem does
not establish Lemma 8's faster all-count prepass or replace the installed solver.

## Main results

* `forward_layer`, `backward_layer`: exact agreement with the native DP update.
* `forward_layer_append`, `backward_layer_cons`: the next original-input counter table.
* `layer_certificate`: one uniform binary-addition machine, with source-derived bounds.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.WordTable
open Turing.MultiTapeTM Cslib.GenericRAM

/-- All leaves in zero-child before one-child order. Repetitions and zeros are retained. -/
def entries {α : Type} : {m : ℕ} → WordTable α m → List α
  | 0, .leaf v => [v]
  | _ + 1, .node l r => entries l ++ entries r

/-- Pair corresponding leaves, not a Cartesian product of table values. -/
def pairedEntries {α β : Type} : {m : ℕ} → WordTable α m → WordTable β m → List (α × β)
  | 0, .leaf a, .leaf b => [(a, b)]
  | _ + 1, .node a b, .node c d => pairedEntries a c ++ pairedEntries b d

theorem pairedEntries_length {α β : Type} {m : ℕ} (a : WordTable α m)
    (b : WordTable β m) : (pairedEntries a b).length = 2 ^ m := by
  induction a with
  | leaf a => cases b; rfl
  | node l r iha ihb =>
    cases b with
    | node c d => simp [pairedEntries, iha, ihb, pow_succ, Nat.mul_two]

/-- Each serialized pair comes from one common state, even if other states have equal values. -/
theorem mem_pairedEntries {α β : Type} {m : ℕ} (a : WordTable α m)
    (b : WordTable β m) (v : α × β) (hv : v ∈ pairedEntries a b) :
    ∃ s : BitVec m, v = (a.read s, b.read s) := by
  induction a with
  | leaf a =>
    cases b with
    | leaf b =>
      have he : v = (a, b) := by simpa only [pairedEntries, List.mem_singleton] using hv
      exact ⟨0, he⟩
  | @node n l r iha ihb =>
    cases b with
    | node c d =>
      rcases List.mem_append.mp hv with h | h
      · obtain ⟨s, hs⟩ := iha c h
        exact ⟨s.concat false, by simpa only [read_node, Bool.false_eq_true, ite_false] using hs⟩
      · obtain ⟨s, hs⟩ := ihb d h
        exact ⟨s.concat true, by simpa only [read_node, ite_true] using hs⟩

/-- Exact serialized output of the counter addition stage. -/
theorem entries_sumCounters {m : ℕ} (a b : WordTable ℕ m) :
    entries (sumCounters a b).ret = BinaryPairSums.run (pairedEntries a b) := by
  induction a with
  | leaf a => cases b; rfl
  | node l r iha ihb =>
    cases b with
    | node c d =>
      simp only [sumCounters, Cslib.Algorithms.Lean.TimeM.ret_bind,
        Cslib.Algorithms.Lean.TimeM.ret_pure, entries, iha, ihb,
        pairedEntries, BinaryPairSums.run, List.map_append]

/-- Interleaved inputs for the actual forward layer, after the two pull operations. -/
def forwardPairs {m : ℕ} (a : BitVec m) (table : WordTable ℕ m) : List (ℕ × ℕ) :=
  pairedEntries (addPull (stateKey (~~~a)) true table).ret
    (xorPull (stateKey (~~~a)) table).ret

/-- The inverse-chain layer uses addition without carry and the complemented XOR operand. -/
def backwardPairs {m : ℕ} (a : BitVec m) (table : WordTable ℕ m) : List (ℕ × ℕ) :=
  pairedEntries (addPull (stateKey a) false table).ret
    (xorPull (stateKey (~~~a)) table).ret

theorem forward_layer {m : ℕ} (a : BitVec m) (table : WordTable ℕ m) :
    BinaryPairSums.run (forwardPairs a table) = entries (countAdvance (stateKey a) table).ret := by
  simp only [countAdvance, Cslib.Algorithms.Lean.TimeM.ret_bind, complement_ret,
    complement_key, forwardPairs, entries_sumCounters]

theorem backward_layer {m : ℕ} (a : BitVec m) (table : WordTable ℕ m) :
    BinaryPairSums.run (backwardPairs a table) =
      entries (countBackAdvance (stateKey a) table).ret := by
  simp only [countBackAdvance, Cslib.Algorithms.Lean.TimeM.ret_bind, complement_ret,
    complement_key, backwardPairs, entries_sumCounters]

/-- The streaming result is the complete counter table after appending an original operand.
No table correctness premise is supplied by the caller. -/
theorem forward_layer_append {m : ℕ} (as : List (BitVec m)) (s a : BitVec m) :
    BinaryPairSums.run (forwardPairs a (classCounters as s)) =
      entries (classCounters (as ++ [a]) s) := by
  rw [forward_layer]
  simp only [classCounters, List.map_append, List.map_cons, List.map_nil,
    countRun_append, countRun, Cslib.Algorithms.Lean.TimeM.ret_bind,
    Cslib.Algorithms.Lean.TimeM.ret_pure]

/-- Inverse-chain execution prepends an operand, processing the suffix first. -/
theorem backward_layer_cons {m : ℕ} (as : List (BitVec m)) (t a : BitVec m) :
    BinaryPairSums.run (backwardPairs a (backwardCounters as t)) =
      entries (backwardCounters (a :: as) t) := by
  rw [backward_layer]
  simp only [backwardCounters, List.map_cons, countBackRun,
    Cslib.Algorithms.Lean.TimeM.ret_bind, Cslib.Algorithms.Lean.TimeM.ret_pure]

private theorem pair_wire {m B : ℕ} (table : WordTable ℕ m)
    (bound : ∀ s, Nat.size (table.read s) ≤ B) (a x : BitVec m) (carry : Bool) :
    ∀ v ∈ pairedEntries (addPull (stateKey a) carry table).ret
      (xorPull (stateKey x) table).ret,
      (encPair encNat encNat v).length ≤ 3 * B + 1 := by
  intro v hv
  obtain ⟨s, rfl⟩ := mem_pairedEntries _ _ v hv
  have ha := bound (s + a + BitVec.ofNat m carry.toNat)
  have hx := bound (s ^^^ x)
  simp only [length_encPair, addPull_read, xorPull_read, encNat_apply,
    Nat.size_eq_bits_len] at ha hx ⊢
  omega

/-- A single uniform machine adds the serialized pulled counters in either orientation.
Its bounds on these derived inputs are in original operator-count width, not table volume
raised to an unspecified polynomial. Preparing the interleaved input is not charged here. -/
theorem layer_certificate : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∃ c : NativeCertificate BinaryPairSums.run encNatPairList (encList encNat),
      ∀ m q (as : Fin q → BitVec m) (s a : BitVec m),
        c.time (forwardPairs a (classCounters (List.ofFn as) s)) ≤ 2 ^ m * P (q + 1) ∧
        c.space (forwardPairs a (classCounters (List.ofFn as) s)) ≤ 2 ^ m * P (q + 1) ∧
        c.time (backwardPairs a (backwardCounters (List.ofFn as) s)) ≤ 2 ^ m * P (q + 1) ∧
        c.space (backwardPairs a (backwardCounters (List.ofFn as) s)) ≤ 2 ^ m * P (q + 1) := by
  obtain ⟨P, hp, hm, hc⟩ := BinaryPairSums.run_computable
  let resource := fun rows => (encNatPairList rows).length +
    (rows.length + 1) * P (BinaryPairSums.width rows)
  let c : NativeCertificate BinaryPairSums.run encNatPairList (encList encNat) :=
    ⟨resource, resource, hc⟩
  let Q := fun B => 6 * B + 3 + 2 * P (3 * B + 2)
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have mQ : Monotone Q := by
    intro a b hab
    have := hm (by omega : 3 * a + 2 ≤ 3 * b + 2)
    dsimp only [Q]
    omega
  have cost {m B : ℕ} (rows : List (ℕ × ℕ)) (hl : rows.length = 2 ^ m)
      (hw : ∀ v ∈ rows, (encPair encNat encNat v).length ≤ 3 * B + 1) :
      resource rows ≤ 2 ^ m * Q B := by
    have hi := length_encList_le (encPair encNat encNat) rows hw
    have hb : BinaryPairSums.width rows ≤ 3 * B + 2 := by
      change listMax (fun row => (encPair encNat encNat row).length) rows + 1 ≤ _
      have := listMax_le hw
      omega
    have ht := Nat.mul_le_mul_left (rows.length + 1) (hm hb)
    have hn := Nat.two_pow_pos m
    dsimp only [resource, Q]
    change (encNatPairList rows).length ≤ rows.length * (2 * (3 * B + 1) + 1) at hi
    rw [hl] at hi ht
    rw [hl]
    nlinarith
  refine ⟨Q, hQ, mQ, c, fun m q as s a => ?_⟩
  have hf := cost (forwardPairs a (classCounters (List.ofFn as) s))
    (pairedEntries_length _ _) (pair_wire _ (classCounters_size_le as s) _ _ _)
  have hb := cost (backwardPairs a (backwardCounters (List.ofFn as) s))
    (pairedEntries_length _ _) (pair_wire _ (backwardCounters_size_le as s) _ _ _)
  exact ⟨hf, hf, hb, hb⟩

end Cslib.Cryptanalysis.AddXNOR.WordTable
