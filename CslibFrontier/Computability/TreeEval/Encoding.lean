/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Basic
public import Mathlib.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.Append

/-!
# Bit encodings of Tree Evaluation instances

An instance of height `h` and value length `ℓ` is encoded by the unary header `1^ℓ 0 1^h 0`,
followed by its body in pre-order: a leaf is its `ℓ` bits, and a gate `f` is its table, the
`4^ℓ * ℓ` bits `f (α k) (β k) i` for `k < 4^ℓ` and `i < ℓ` in this order, where `α k` and `β k` read
the low and high `ℓ` bits of `k`, followed by the bodies of its children.

The body of a subtree of height `d` has length `bodyLength ℓ d`, so the node at a path starts at the
offset `pathOffset`, which a machine can recompute from the path alone.

## Main definitions

* `Cslib.TreeEval.Tree.body`, `Cslib.TreeEval.Tree.encode`: the body and the full encoding.
* `Cslib.TreeEval.tableBit`: the bit of a gate's table at a position.
* `Cslib.TreeEval.pathOffset`: the offset of the node at a path within a body.

## Main results

* `Cslib.TreeEval.two_pow_ell_le_bodyLength`, `Cslib.TreeEval.two_pow_height_le_bodyLength`:
  exponential lower bounds `2 ^ ℓ ≤ bodyLength ℓ H` (for `1 ≤ ℓ`, `1 ≤ H`) and
  `2 ^ H ≤ bodyLength ℓ H` (for `1 ≤ ℓ`) on the body length.
* `Cslib.TreeEval.Tree.getElem_body_pathOffset`: the bits of the node at a path, read off the body
  at its offset; `Cslib.TreeEval.Tree.getElem_body_gate` and `Cslib.TreeEval.Tree.getElem_body_leaf`
  for gates and leaves.

## References

* [S. Cook, P. McKenzie, D. Wehr, M. Braverman and R. Santhanam, *Pebbles and branching programs
  for tree evaluation*][CMWBS2012] introduce the problem, with gates given by their tables.
-/

@[expose] public section

namespace Cslib.TreeEval

variable {ℓ : ℕ}

/-- The low `ℓ` bits of `k`. -/
def lowBits (ℓ k : ℕ) : Fin ℓ → Bool := fun j => k.testBit j

/-- The bits `ℓ, …, 2ℓ - 1` of `k`. -/
def highBits (ℓ k : ℕ) : Fin ℓ → Bool := fun j => k.testBit (ℓ + j)

/-- The number of bits in the table of a gate on `ℓ`-bit values. -/
def tableLength (ℓ : ℕ) : ℕ := 4 ^ ℓ * ℓ

/-- The bit at position `q` of the table of `f`: output bit `q % ℓ` on the inputs indexed by
`q / ℓ`. -/
def tableBit (f : Gate ℓ) (q : ℕ) : Bool :=
  if h : q % ℓ < ℓ then f (lowBits ℓ (q / ℓ)) (highBits ℓ (q / ℓ)) ⟨q % ℓ, h⟩ else false

/-- The table of a gate. -/
def table (f : Gate ℓ) : List Bool :=
  List.ofFn fun q : Fin (tableLength ℓ) => tableBit f q

@[simp] theorem length_table (f : Gate ℓ) :
    (table f).length = tableLength ℓ := List.length_ofFn

/-- The length of the body of a subtree of height `d`. -/
def bodyLength (ℓ : ℕ) : ℕ → ℕ
  | 0 => ℓ
  | d + 1 => tableLength ℓ + 2 * bodyLength ℓ d

/-- A gate table on `ℓ ≥ 1` bits has at least `2 ^ ℓ` bits. -/
private theorem two_pow_le_tableLength {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 2 ^ ℓ ≤ tableLength ℓ :=
  calc 2 ^ ℓ ≤ 4 ^ ℓ := Nat.pow_le_pow_left (by decide) ℓ
    _ = 4 ^ ℓ * 1 := (Nat.mul_one _).symm
    _ ≤ 4 ^ ℓ * ℓ := Nat.mul_le_mul_left _ hℓ

/-- The body of a height-`H` tree has at least `2 ^ H * ℓ` bits from its leaves alone. -/
private theorem two_pow_mul_le_bodyLength (ℓ H : ℕ) : 2 ^ H * ℓ ≤ bodyLength ℓ H := by
  induction H with
  | zero => simp [bodyLength]
  | succ d ih => simp only [bodyLength, Nat.pow_succ', Nat.mul_assoc]; omega

/-- A tree of positive height includes at least the root gate table. -/
theorem tableLength_le_bodyLength_of_pos {ℓ H : ℕ} (hH : 1 ≤ H) :
    tableLength ℓ ≤ bodyLength ℓ H := by
  rcases H with _ | d
  · omega
  · simp only [bodyLength]; omega

/-- For `1 ≤ ℓ` and `1 ≤ H`, the body has length at least `2 ^ ℓ`. -/
theorem two_pow_ell_le_bodyLength {ℓ H : ℕ} (hℓ : 1 ≤ ℓ) (hH : 1 ≤ H) :
    2 ^ ℓ ≤ bodyLength ℓ H :=
  (two_pow_le_tableLength hℓ).trans (tableLength_le_bodyLength_of_pos hH)

/-- For `1 ≤ ℓ`, the body of a height-`H` tree has length at least `2 ^ H`. -/
theorem two_pow_height_le_bodyLength {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (H : ℕ) :
    2 ^ H ≤ bodyLength ℓ H :=
  calc 2 ^ H = 2 ^ H * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ H * ℓ := Nat.mul_le_mul_left _ hℓ
    _ ≤ bodyLength ℓ H := two_pow_mul_le_bodyLength ℓ H

/-- The offset of the node at a path within the body of a subtree of height `d`. -/
def pathOffset (ℓ : ℕ) : ℕ → List Bool → ℕ
  | _, [] => 0
  | 0, _ :: _ => 0
  | d + 1, b :: P => tableLength ℓ + (if b then bodyLength ℓ d else 0) + pathOffset ℓ d P

namespace Tree

variable {h : ℕ}

/-- The body of an instance: leaves by their values, gates by their tables, in pre-order. -/
def body : {h : ℕ} → Tree ℓ h → List Bool
  | _, leaf v => List.ofFn v
  | _, node f l r => table f ++ l.body ++ r.body

@[simp] theorem length_body (T : Tree ℓ h) : T.body.length = bodyLength ℓ h := by
  induction T with
  | leaf v => simp [body, bodyLength]
  | node f l r ihl ihr => simp [body, bodyLength, ihl, ihr]; omega

/-- The header `1^ℓ 0 1^h 0`. -/
def header (ℓ h : ℕ) : List Bool :=
  List.replicate ℓ true ++ false :: List.replicate h true ++ [false]

@[simp] theorem length_header (ℓ h : ℕ) : (header ℓ h).length = ℓ + h + 2 := by
  simp [header]; omega

/-- The header determines the value length and the height. -/
theorem header_append_inj {ℓ' h' : ℕ} {b b' : List Bool}
    (e : header ℓ h ++ b = header ℓ' h' ++ b') : ℓ = ℓ' ∧ h = h' ∧ b = b' := by
  simp only [header, List.append_assoc, List.cons_append, List.nil_append] at e
  obtain ⟨h₁, e⟩ := List.replicate_true_append_false_inj e
  exact ⟨h₁, List.replicate_true_append_false_inj e⟩

/-- The encoding of an instance: its header, then its body. -/
def encode (T : Tree ℓ h) : List Bool := header ℓ h ++ T.body

@[simp] theorem length_encode (T : Tree ℓ h) :
    T.encode.length = ℓ + h + 2 + bodyLength ℓ h := by
  simp [encode]

/-- The bits of a node in the body: the value of a leaf, the table of a gate. -/
def Node.bits : Node ℓ → List Bool
  | .leaf v => List.ofFn v
  | .gate f => table f
  | .none => []

/-- **The bits of the node at a path**, read off the body at the offset of the path. -/
theorem getElem_body_pathOffset {d : ℕ} (U : Tree ℓ d) {P : List Bool} {q : ℕ}
    (hq : q < (U.nodeAt P).bits.length) :
    U.body[pathOffset ℓ d P + q]? = (U.nodeAt P).bits[q]? := by
  induction U generalizing P with
  | leaf v => rcases P with _ | _ <;> simp_all [nodeAt, Node.bits, body, pathOffset]
  | @node d g l r ihl ihr =>
    rcases P with _ | ⟨_ | _, P⟩
    · simp_all [Node.bits, body, pathOffset, List.getElem?_append_left]
    · have := ihl (P := P) (by simpa using hq)
      have hlt := (List.getElem?_eq_some_iff.mp
        (this.trans (List.getElem?_eq_getElem (by simpa using hq)))).1
      simp only [body, pathOffset, nodeAt_node_false] at this hlt ⊢
      rw [List.append_assoc, List.getElem?_append_right (by simp; omega),
        List.getElem?_append_left (by simp at hlt ⊢; omega)]
      simpa [Nat.add_assoc] using this
    · simp only [body, pathOffset, nodeAt_node_true] at hq ⊢
      rw [List.getElem?_append_right (by simp; omega), ← ihr hq]
      congr 1; simp; omega

/-- **The table of the gate at a path**, read off the body at the offset of the path. -/
theorem getElem_body_gate {d : ℕ} (U : Tree ℓ d) {P : List Bool} {f : Gate ℓ}
    (hP : U.nodeAt P = .gate f) {q : ℕ} (hq : q < tableLength ℓ) :
    U.body[pathOffset ℓ d P + q]? = some (tableBit f q) := by
  rw [getElem_body_pathOffset U (by simpa [hP, Node.bits] using hq)]
  simp [hP, Node.bits, table, hq]

/-- **The value of the leaf at a path**, read off the body at the offset of the path. -/
theorem getElem_body_leaf {d : ℕ} (U : Tree ℓ d) {P : List Bool} {v : Fin ℓ → Bool}
    (hP : U.nodeAt P = .leaf v) (i : Fin ℓ) :
    U.body[pathOffset ℓ d P + i]? = some (v i) := by
  rw [getElem_body_pathOffset U (by simp [hP, Node.bits])]
  simp [hP, Node.bits]

end Tree

end Cslib.TreeEval
