/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.FusionTree.Model
import Complexity.Algorithms.WordRAM.FusionTree.Parameters
import Complexity.Algorithms.WordRAM.FusionTree.ReadHeader

/-! Concrete parameter nonvacuity, serialization, and actual header reads. -/

open Cslib.WordRAM
open Cslib.Algorithms.Lean.FusionTree
open Cslib.Algorithms.WordRAM.FusionTree

namespace FusionTreeLayoutTests

-- The concrete fusion-node capacity starts at 512-bit physical words.
set_option exponentiation.threshold 512 in
private theorem sample_bound (i : Fin 2) : (![2, 9] i) < 2 ^ 512 := by
  have hsmall : (![2, 9] i) < 2 ^ 4 := by fin_cases i <;> decide
  exact hsmall.trans_le (Nat.pow_le_pow_right (n := 2) (i := 4) (j := 512)
    (by decide) (by decide))

/-- All bundled construction hypotheses hold for a concrete two-key node. -/
example : Nonempty (NodeParameters 512 ![2, 9]) :=
  NodeParameters.exists_parameters (by decide) (by decide) sample_bound (by decide) (by decide)

noncomputable def sample : NodeParameters 512 ![2, 9] :=
  NodeParameters.choose (by decide) (by decide) sample_bound (by decide) (by decide)

example (i : Fin 15) : Fits 512 (sample.words i) :=
  sample.words_fit (by decide) (by decide) sample_bound (by decide) (by decide) i

/-- The fifteen words agree with the layout's offsets three through seventeen. In particular
the compressed-payload maximum occupies offset fifteen, rather than a subtree maximum. -/
example {n w : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys) :
    p.words = ![p.C, p.digits 0, p.digits 1, p.digits 2, p.D, p.copies,
      p.packedComplement, p.packed, p.guards, p.b, p.middle, p.radix, p.maximum,
      w - 2 * (w / 2), p.r] := rfl

example {n w : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys) :
    p.words ⟨HeaderOffset.bits - 3, by decide⟩ = p.b ∧
      p.words ⟨HeaderOffset.maximum - 3, by decide⟩ = p.maximum ∧
      p.words ⟨HeaderOffset.packedComplements - 3, by decide⟩ = p.packedComplement :=
  ⟨rfl, rfl, rfl⟩

/-- A zero key is present, rather than confused with an empty leaf. -/
def tree : Tree := .node 0 [.leaf [0], .leaf [7]]

def zeroParameters : Parameters := fun _ _ => 0

example : Tree.Valid 2 tree := by simp [tree, Tree.Valid, Tree.keys]
example : span tree = 58 := by simp [tree, span, headerWords]

/-- At a nonzero base, the actual table interleaves keys and absolute child pointers. -/
example : [50, 51, 52, 53].map (memory zeroParameters tree 32) = [0, 54, 7, 72] := by
  have h : Block.HoldsList 32 (encode zeroParameters 32 tree)
      (memory zeroParameters tree 32) := rep_memory zeroParameters tree 32
  have hread (i : Fin 4) : memory zeroParameters tree 32 (50 + i.val) = ![0, 54, 7, 72] i := by
    have hi := h.get (18 + i.val) (by fin_cases i <;> decide)
    fin_cases i <;>
      simpa [tree, encode, encodeForest, header, zeroParameters, List.ofFn_succ,
        headerWords, childTable, childAddress, span, Tree.minimum] using hi
  exact congrArg (fun f : Fin 4 → ℕ => [f 0, f 1, f 2, f 3]) (funext hread)

example : decode 3 (memory zeroParameters tree 32) 32 = tree :=
  decode_encode (by simp [tree, Tree.Valid, Tree.keys] : Tree.Valid 2 tree)
    (by simp [tree, Cslib.Algorithms.Lean.FusionTree.Tree.height]) zeroParameters 32

def input : Data 21 :=
  ⟨fun i => if i = 0 then 32 else 127, memory zeroParameters tree 32⟩

/-- All constant offsets and loads execute on the real interpreter. -/
example : (ReadHeaderProgram.code.eval 7 0 input).map
    (fun (y, t) => (y.regs 0, y.regs 1, y.regs 2, y.regs 3, y.regs 18, t)) =
      some (32, 1, 2, 0, 0, 54) := by decide

example : Exec 7 ReadHeaderProgram.code input (ReadHeaderProgram.result input) 54 :=
  ReadHeaderProgram.exec input (by decide)

/-- info: 'Cslib.Algorithms.WordRAM.FusionTree.ReadHeaderProgram.exec' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReadHeaderProgram.exec

end FusionTreeLayoutTests
