/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.RecordCircuit
public import Complexity.Computability.Circuit.Boolean.Iteration.Residue
import Mathlib.Tactic.Linarith

/-!
# Reconstructing the fixed power from a detected pair

A detected pair of records determines `f^[T] x` (`reconstruct_spec`). If the prefix state at time
`d` is a checkpoint, the checkpoint's payload is `f^[T - K]` of it, and `K - d` further steps of
the payload give `f^[T] x`; the circuit computes all of the payload's first `K` steps and selects
one (`hitValue`). If the prefix repeats between times `i < j`, the state at the time in `[i, j)`
congruent to `T` is selected from the prefix (`repeatedValue`). All branches are total, also on
pairs that a detector never produces.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.reconstruct`: the state determined by a pair of records.

## Main results

* `Cslib.Circuits.Boolean.Iteration.reconstruct_spec`: a witness pair determines `f^[T] x`.
* `Cslib.Circuits.Boolean.Iteration.synthesis_reconstruct`: its gate count.

## References

* Adapted from lean/Proofs/{Decoder,DecoderCircuits,Reconstruction}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

variable {n w : ℕ}

/-- The state `K - index` steps after `payload`. -/
def hitValue (f : BitString n → BitString n) (K : ℕ) (index : BitVec w) (payload : BitString n) :
    BitString n :=
  selectBits (BitVec.ofNat w K - index) fun j : Fin (K + 1) => f^[j.val] payload

/-- The prefix state at the time in `[lo, hi)` congruent to `T`. -/
def repeatedValue (f : BitString n → BitString n) (T K : ℕ) (x : BitString n) (lo hi : BitVec w) :
    BitString n :=
  selectBits (repeatWordIndex T K lo hi) fun j : Fin (K + 1) => f^[j.val] x

/-- The state determined by a pair of records: by a checkpoint's payload if either is one, and
otherwise by the repeat between the two query times. -/
def reconstruct (f : BitString n → BitString n) (T K : ℕ) (x : BitString n)
    (a b : Record n w) : BitString n :=
  if a.checkpoint then hitValue f K b.index a.payload
  else if b.checkpoint then hitValue f K a.index b.payload
  else if a.index.ult b.index then repeatedValue f T K x a.index b.index
  else repeatedValue f T K x b.index a.index

theorem hitValue_spec (f : BitString n → BitString n) (T K d : ℕ) (x : BitString n)
    (hd : d ≤ K) (hK : K < 2 ^ w) (hT : K ≤ T) :
    hitValue f K (BitVec.ofNat w d) (f^[T - K] (f^[d] x)) = f^[T] x := by
  have he : (BitVec.ofNat w K - BitVec.ofNat w d).toNat = K - d := by
    rw [BitVec.toNat_sub_of_le]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hK, Nat.mod_eq_of_lt (hd.trans_lt hK)]
    · change (BitVec.ofNat w d).toNat ≤ (BitVec.ofNat w K).toNat
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hK,
        Nat.mod_eq_of_lt (hd.trans_lt hK)] using hd
  rw [hitValue, selectBits_of_toNat_lt _ _ (by rw [he]; omega)]
  simp only [he, ← Function.iterate_add_apply]
  congr 1
  omega

private theorem repeatedValue_spec (f : BitString n → BitString n) (T K i j : ℕ) (x : BitString n)
    (hij : i < j) (hj : j ≤ K) (hK : K < 2 ^ w) (hT : K ≤ T) (heq : f^[i] x = f^[j] x) :
    repeatedValue f T K x (BitVec.ofNat w i) (BitVec.ofNat w j) = f^[T] x := by
  have hiw : (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt (by omega)
  have hjw : (BitVec.ofNat w j).toNat = j := Nat.mod_eq_of_lt (by omega)
  have hs := repeatWordIndex_spec (f := f) (x := x)
    (BitVec.ofNat w i) (BitVec.ofNat w j) (by rwa [hiw, hjw]) (by rwa [hjw]) hK hT
    (by rwa [hiw, hjw])
  rw [repeatedValue, selectBits_of_toNat_lt _ _ (by have := hs.2.1; rw [hjw] at this; omega)]
  exact hs.2.2

/-- A witness pair determines the state at time `T`. -/
theorem reconstruct_spec {M : ℕ} (f : BitString n → BitString n) (T K : ℕ)
    (checkpoints : Fin M → BitString n) (x : BitString n) (a b : Record n w)
    (hK : K < 2 ^ w) (hT : K ≤ T) (h : Record.Witness f T K checkpoints x a b) :
    reconstruct f T K x a b = f^[T] x := by
  cases h with
  | hitLeft h d hd heq =>
    simpa only [reconstruct, Record.stored, Record.query, ↓reduceIte, ← heq] using
      hitValue_spec f T K d x hd hK hT
  | hitRight h d hd heq =>
    simpa only [reconstruct, Record.stored, Record.query, Bool.false_eq_true,
      ↓reduceIte, ← heq] using hitValue_spec f T K d x hd hK hT
  | repeated i j hi hj hne heq =>
    simp only [reconstruct, Record.query, Bool.false_eq_true, ↓reduceIte,
      BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi.trans_lt hK),
      Nat.mod_eq_of_lt (hj.trans_lt hK), decide_eq_true_eq]
    split_ifs with hij
    · exact repeatedValue_spec f T K i j x hij hj hK hT heq
    · exact repeatedValue_spec f T K j i x (by omega) hi hK hT heq.symm

/-! ### Gate counts -/

/-- The prefix states up to time `K`. -/
def prefixWires (f : BitString n → BitString n) (K : ℕ) : Set (BooleanFunction n) :=
  Synthesis.stages (fun j => wires fun x => f^[j] x) K

theorem prefix_mem (f : BitString n → BitString n) {K j : ℕ} (hj : j ≤ K) (bit : Fin n) :
    (fun x => f^[j] x bit) ∈ prefixWires f K :=
  Synthesis.subset_stages _ hj ⟨bit, rfl⟩

private theorem synthesis_repeatedValue (s : Set (BooleanFunction n))
    (f : BitString n → BitString n)
    (T K : ℕ) (lo hi : BitString n → BitVec w)
    (hlo : ∀ i : Fin w, (fun x => (lo x).getLsbD i.val) ∈ s)
    (hhi : ∀ i : Fin w, (fun x => (hi x).getLsbD i.val) ∈ s)
    (hp : prefixWires f K ⊆ s) (hc : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Synthesis interpretation s (wires fun x => repeatedValue f T K x (lo x) (hi x))
      (200 * (K + 1) * (n + w + 1) ^ 2) := by
  have hidx := synthesis_repeatWordIndex s T K lo hi hlo hhi hc
  have hsel := Synthesis.selectBits
    (s := s ∪ wordWires fun x => repeatWordIndex T K (lo x) (hi x))
    (fun x => repeatWordIndex T K (lo x) (hi x)) (fun j : Fin (K + 1) => fun x => f^[j.val] x)
    (fun i => Or.inr ⟨i, rfl⟩)
    fun j bit => Or.inl (hp (prefix_mem f (by have := j.isLt; omega) bit))
  apply (hidx.trans hsel).mono Set.Subset.rfl Set.Subset.rfl
  nlinarith [Nat.zero_le (K * n ^ 2), Nat.zero_le (K * n * w), Nat.zero_le (K * w ^ 2)]

theorem synthesis_hitValue {a : ℕ} (s : Set (BooleanFunction a))
    (c : Circuit signature n n) (K : ℕ) (index : BitString a → BitVec w)
    (payload : BitString a → BitString n)
    (hi : ∀ i : Fin w, (fun x => (index x).getLsbD i.val) ∈ s)
    (hp : wires payload ⊆ s) (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) :
    Synthesis interpretation s
      (wires fun x => hitValue (c.eval interpretation) K (index x) (payload x))
      (K * c.size + 200 * (K + 1) * (n + w + 1) ^ 2) := by
  let idx := fun x => BitVec.ofNat w K - index x
  let trace := Synthesis.stages
    (fun j => wires fun x => (c.eval interpretation)^[j] (payload x)) K
  have horbit : Synthesis interpretation s trace (K * c.size) :=
    Synthesis.orbit c payload (fun i => hp ⟨i, rfl⟩) K
  have hidx := Synthesis.word_sub (s := s) (fun _ => BitVec.ofNat w K) index (fun _ => hc _) hi
  have hsel := Synthesis.selectBits (s := s ∪ (trace ∪ wordWires idx)) idx
    (fun j : Fin (K + 1) => fun x => (c.eval interpretation)^[j.val] (payload x))
    (fun i => Or.inr (Or.inr ⟨i, rfl⟩))
    fun j bit => Or.inr (Or.inl (Synthesis.subset_stages _ (Nat.le_of_lt_succ j.isLt) ⟨bit, rfl⟩))
  apply ((horbit.union hidx).trans hsel).mono Set.Subset.rfl Set.Subset.rfl
  nlinarith [Nat.zero_le (K * n ^ 2), Nat.zero_le (K * n * w), Nat.zero_le (K * w ^ 2)]

/-- The reconstruction circuit: two payload orbits, two residue branches and their selection. -/
theorem synthesis_reconstruct (s : Set (BooleanFunction n)) (c : Circuit signature n n)
    (T K : ℕ) (a b : BitString n → Record n w)
    (ha : Record.wireSet a ⊆ s) (hb : Record.wireSet b ⊆ s)
    (hp : prefixWires (c.eval interpretation) K ⊆ s)
    (hc : ∀ b : Bool, (fun _ : BitString n => b) ∈ s) :
    Synthesis interpretation s
      (wires fun x => reconstruct (c.eval interpretation) T K x (a x) (b x))
      (4 * K * c.size + 1000 * (K + 1) * (n + w + 1) ^ 2) := by
  have hleft := synthesis_hitValue s c K (fun x => (b x).index) (fun x => (a x).payload)
    (Record.index_mem hb) (by rintro _ ⟨i, rfl⟩; exact Record.payload_mem ha i) hc
  have hright := synthesis_hitValue s c K (fun x => (a x).index) (fun x => (b x).payload)
    (Record.index_mem ha) (by rintro _ ⟨i, rfl⟩; exact Record.payload_mem hb i) hc
  have hforward := synthesis_repeatedValue s (c.eval interpretation) T K
    (fun x => (a x).index) (fun x => (b x).index) (Record.index_mem ha) (Record.index_mem hb) hp hc
  have hbackward := synthesis_repeatedValue s (c.eval interpretation) T K
    (fun x => (b x).index) (fun x => (a x).index) (Record.index_mem hb) (Record.index_mem ha) hp hc
  have hcmp := Synthesis.word_ult (s := s) (fun x => (a x).index) (fun x => (b x).index)
    (Record.index_mem ha) (Record.index_mem hb)
  have h := synthesis_ite hleft (synthesis_ite hright
    (synthesis_ite hforward hbackward hcmp) (Synthesis.of_mem (Record.checkpoint_mem hb)))
    (Synthesis.of_mem (Record.checkpoint_mem ha))
  apply h.mono Set.Subset.rfl Set.Subset.rfl
  nlinarith [Nat.zero_le (K * c.size)]

end Cslib.Circuits.Boolean.Iteration
