/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Local
public import CslibFrontier.Foundations.Data.BitString.List.Binary

/-!
# Streamed queries through a complete carry-save tree

A query stores a path identifying a subtree, its remaining height, an output word and a bit
position. Each compressor port appends one path bit and subtracts at most two from the bit
position. The semantic tree uses the existing four-to-two compressor; no row is stored by a
query. These are semantic routing bounds, not native Turing-machine running-time bounds.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.CarrySaveQuery

open BitString CarrySaveLocal

/-- A bit query in a complete binary tree of carry-save pairs. -/
structure Query where
  /-- Path from the root to the current subtree. -/
  path : List Bool
  /-- Number of compressor layers remaining. -/
  remaining : ℕ
  /-- Whether the second word is requested. -/
  carry : Bool
  /-- Requested bit position. -/
  bit : ℕ
  deriving DecidableEq

/-- Semantic evaluation of a complete tree, using the existing compressor circuit. -/
def tree {w : ℕ} (leaves : List Bool → BitString (w + w)) :
    ℕ → List Bool → BitString (w + w)
  | 0, path => leaves path
  | n + 1, path => (csa4to2 w).eval interpretation
      (Fin.append (tree leaves n (path ++ [false])) (tree leaves n (path ++ [true])))

/-- Unreduced integer sum of the leaf-pair values. -/
def leafSum {w : ℕ} (leaves : List Bool → BitString (w + w)) : ℕ → List Bool → ℕ
  | 0, path => pairVal (leaves path)
  | n + 1, path => leafSum leaves n (path ++ [false]) + leafSum leaves n (path ++ [true])

/-- Every layer preserves the leaf sum modulo the word precision. -/
theorem pairVal_tree_mod {w : ℕ} (leaves : List Bool → BitString (w + w))
    (n : ℕ) (path : List Bool) :
    pairVal (tree leaves n path) % 2 ^ w = leafSum leaves n path % 2 ^ w := by
  induction n generalizing path with
  | zero => rfl
  | succ n ih =>
    simp only [tree, leafSum, pairVal_eval_csa4to2_mod]
    rw [Nat.add_mod, ih, ih, ← Nat.add_mod]

/-- Binary path indexing enumerates exactly the consecutive leaf interval of a subtree. -/
theorem leafSum_binaryValue {w : ℕ} (leaves : ℕ → BitString (w + w))
    (n : ℕ) (path : List Bool) :
    leafSum (fun p => leaves (binaryValue p)) n path =
      ∑ j ∈ Finset.range (2 ^ n), pairVal (leaves (binaryValue path * 2 ^ n + j)) := by
  induction n generalizing path with
  | zero => simp [leafSum]
  | succ n ih =>
    rw [leafSum, ih, ih]
    simp only [binaryValue_snoc, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
    rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by omega, Finset.sum_range_add]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> congr 2 <;>
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, two_mul]

/-- Select one of the two words of a carry-save pair. -/
def component {w : ℕ} (p : BitString (w + w)) (carry : Bool) : BitString w :=
  if carry then sndBits p else fstBits p

/-- Total semantics, with false padding above the word precision. -/
def value {w : ℕ} (leaves : List Bool → BitString (w + w)) (q : Query) : Bool :=
  if h : q.bit < w then component (tree leaves q.remaining q.path) q.carry ⟨q.bit, h⟩
  else false

/-- The child pair containing a source word. -/
def childSide (word : Fin 4) : Bool := decide (2 ≤ word.val)

/-- The component within the selected child pair. -/
def childCarry (word : Fin 4) : Bool := decide (word.val % 2 = 1)

/-- One streamed compressor move; absent children are the constant false boundary inputs. -/
def descend (q : Query) (port : Fin 7) : Option Query :=
  if q.remaining = 0 then none
  else if (source q.carry port).shift.val ≤ q.bit then
    some ⟨q.path ++ [childSide (source q.carry port).word], q.remaining - 1,
      childCarry (source q.carry port).word, q.bit - (source q.carry port).shift.val⟩
  else none

/-- A local move removes exactly one remaining compressor layer. -/
theorem descend_remaining {q q' : Query} {port : Fin 7} (h : descend q port = some q') :
    q'.remaining + 1 = q.remaining := by
  unfold descend at h
  split at h <;> simp_all
  rcases h with ⟨_, rfl⟩
  simp only
  omega

/-- Appending a path bit conserves the total root-to-leaf height. -/
theorem descend_height {q q' : Query} {port : Fin 7} (h : descend q port = some q') :
    q'.path.length + q'.remaining = q.path.length + q.remaining := by
  have hr := descend_remaining h
  unfold descend at h
  split at h <;> simp_all
  rcases h with ⟨_, rfl⟩
  simp_all
  omega

/-- A local move only decrements the index, and by at most two. -/
theorem descend_bit {q q' : Query} {port : Fin 7} (h : descend q port = some q') :
    q'.bit ≤ q.bit ∧ q.bit ≤ q'.bit + 2 := by
  have hs := source_shift_le q.carry port
  unfold descend at h
  split at h <;> simp_all
  rcases h with ⟨_, rfl⟩
  simp only
  omega

/-- The selected four words are precisely the two components of the two children. -/
theorem component_child {w : ℕ} (p₀ p₁ : BitString (w + w)) (j : Fin 4) :
    component (if childSide j then p₁ else p₀) (childCarry j) =
      (![fstBits p₀, sndBits p₀, fstBits p₁, sndBits p₁] : Fin 4 → BitString w) j := by
  rcases j with ⟨j, hj⟩
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> simp [component, childSide, childCarry]

/-- One tree output bit is evaluated by the fixed seven-input compressor formula. -/
theorem value_layer {w : ℕ} (leaves : List Bool → BitString (w + w))
    (path : List Bool) (n : ℕ) (carry : Bool) (i : Fin w) :
    value leaves ⟨path, n + 1, carry, i.val⟩ =
      (formula carry).eval interpretation (fun port =>
        (descend ⟨path, n + 1, carry, i.val⟩ port).elim false (value leaves)) := by
  let p₀ := tree leaves n (path ++ [false])
  let p₁ := tree leaves n (path ++ [true])
  have hlocal := eval_formula_compressor (fstBits p₀) (sndBits p₀)
    (fstBits p₁) (sndBits p₁) i carry
  rw [append_fstBits_sndBits, append_fstBits_sndBits] at hlocal
  have hout : value leaves ⟨path, n + 1, carry, i.val⟩ =
      (csa4to2 w).eval interpretation (Fin.append p₀ p₁)
        (if carry then Fin.natAdd w i else Fin.castAdd w i) := by
    cases carry <;> simp [value, component, tree, fstBits, sndBits, p₀, p₁]
  rw [hout, ← hlocal]
  congr 1
  funext port
  simp only [CarrySaveLocal.inputs, readBelow, descend, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte, Nat.add_sub_cancel]
  split
  · rename_i hs
    have hi : i.val - (source carry port).shift.val < w := by omega
    simp only [Option.elim_some, value, hi, ↓reduceDIte]
    rw [← component_child]
    cases hside : childSide (source carry port).word <;> rfl
  · rfl

end Cslib.Circuits.Boolean.CarrySaveQuery
