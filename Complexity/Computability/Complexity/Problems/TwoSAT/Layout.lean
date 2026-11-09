/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace
import Mathlib.Data.List.GetD

/-!
# The layout of encoded formulas

A formula is encoded (`Cslib.Complexity.encCNF`) by three levels of framed lists: the clauses,
their literals, and the binary digits of each variable followed by the polarity. Unfolding the
frames gives a flat layout (`Cslib.Complexity.TwoSAT.encCNF_eq_flatMap`): each clause is the
bits of its literals followed by `false`, and a literal `(v, b)` is a group of eight bits for each
binary digit `d` of `v`, seven markers `true` followed by `d`, then the ten bits
`[true, true, true, false, true, true, true, b, true, false]`
(`Cslib.Complexity.TwoSAT.literalBits`). A machine reading the encoding by position can thus
tell a literal from the end of its clause by the first bit, a digit from the end of the
variable by the fourth bit of a group, and read the digit or the polarity from the eighth.

The positions are handled with `Cslib.Complexity.TwoSAT.InfixAt w p u`, which says that the word
`u` occurs in `w` at position `p`.

## Main definitions

* `Cslib.Complexity.TwoSAT.literalBits`, `Cslib.Complexity.TwoSAT.clauseBits`: the flat layout.
* `Cslib.Complexity.TwoSAT.InfixAt`: a word occurring at a position.
* `Cslib.Complexity.TwoSAT.clauseStart`: the position of a clause.

## Main results

* `Cslib.Complexity.TwoSAT.encCNF_eq_flatMap`: the flat layout of an encoded formula.
* `Cslib.Complexity.TwoSAT.InfixAt.literal_digit`, `.literal_end`, `.clause_literal`,
  `.clause_end`, `Cslib.Complexity.TwoSAT.infixAt_clauseStart`: reading the layout by position.
-/

@[expose] public section

namespace Cslib.Complexity

namespace TwoSAT

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The bits of a literal `(v, b)` in an encoded formula: the binary digits of `v`, each after
seven markers, then the end of the digits, the polarity and the end of the literal. -/
def literalBits (v : ℕ) (b : Bool) : List Bool :=
  (v.bits.flatMap fun y => List.replicate 7 true ++ [y]) ++
    [true, true, true, false, true, true, true, b, true, false]

/-- The bits of a clause in an encoded formula: its literals, then `false`. -/
def clauseBits (c : Clause ℕ) : List Bool := c.flatMap (fun l => literalBits l.1 l.2) ++ [false]

@[simp]
theorem length_literalBits (v : ℕ) (b : Bool) :
    (literalBits v b).length = 8 * v.bits.length + 10 := by
  simp [literalBits, List.length_flatMap, Nat.mul_comm]

private theorem doubled_doubled_doubled (l : List Bool) :
    doubled (doubled (doubled l)) = l.flatMap fun y => List.replicate 7 true ++ [y] := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [ih, List.replicate_succ]

private theorem doubled_flatMap {α : Type} (l : List α) (f : α → List Bool) :
    doubled (l.flatMap f) = l.flatMap fun a => doubled (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The frame of a clause is its bits. -/
theorem frame_encClause (c : Clause ℕ) :
    frame (encList (encPair encNat encBool) c) = clauseBits c := by
  rw [frame_eq_doubled, clauseBits]
  congr 1
  change doubled (c.flatMap fun l => frame (encPair encNat encBool l)) = _
  rw [doubled_flatMap]
  congr 1
  funext l
  simp [frame_eq_doubled, doubled_doubled_doubled, literalBits]

/-- **The flat layout of an encoded formula.** -/
theorem encCNF_eq_flatMap (φ : CNF ℕ) : encCNF φ = φ.flatMap clauseBits := by
  change φ.flatMap (fun c => frame (encList (encPair encNat encBool) c)) = _
  simp only [frame_encClause]

/-! ### Positions -/

/-- The word `u` occurs in `w` at the position `p`. -/
def InfixAt (w : List Bool) (p : ℕ) (u : List Bool) : Prop :=
  ∀ q < u.length, w[p + q]? = u[q]?

namespace InfixAt

variable {w u v : List Bool} {p : ℕ}

theorem append : InfixAt w p (u ++ v) ↔ InfixAt w p u ∧ InfixAt w (p + u.length) v := by
  constructor
  · intro h
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · rw [h q (by simp; omega), List.getElem?_append_left hq]
    · rw [Nat.add_assoc, h _ (by simp; omega), List.getElem?_append_right (by omega)]
      simp
  · rintro ⟨h₁, h₂⟩ q hq
    rcases lt_or_ge q u.length with hlt | hge
    · rw [h₁ q hlt, List.getElem?_append_left hlt]
    · have := h₂ (q - u.length) (by simp at hq; omega)
      rw [show p + u.length + (q - u.length) = p + q by omega] at this
      rw [this, List.getElem?_append_right hge]

/-- The word of an element of a list, in the concatenation of the words of the elements. -/
theorem flatMap {α : Type*} {L : List α} {f : α → List Bool} (h : InfixAt w p (L.flatMap f))
    {i : ℕ} (hi : i < L.length) :
    InfixAt w (p + ((L.take i).map fun a => (f a).length).sum) (f L[i]) := by
  have hL : L = L.take i ++ L[i] :: L.drop (i + 1) := by simp
  rw [hL, List.flatMap_append, List.flatMap_cons, append, append] at h
  have := h.2.1
  rwa [List.length_flatMap] at this

/-- The bit at an offset. -/
theorem getElem? (h : InfixAt w p u) {q : ℕ} (hq : q < u.length) : w[p + q]? = u[q]? := h q hq

/-- **A digit of a literal**: the group of the digit `k` of `v` starts at `8 * k`, its fourth bit is
a marker and its eighth bit is the digit. -/
theorem literal_digit {v : ℕ} {b : Bool} (h : InfixAt w p (literalBits v b)) {k : ℕ}
    (hk : k < v.bits.length) :
    w[p + 8 * k]? = some true ∧ w[p + 8 * k + 3]? = some true ∧
      w[p + 8 * k + 7]? = some v.bits[k] := by
  have h₁ := (append.mp h).1
  have h₂ := h₁.flatMap (f := fun y => List.replicate 7 true ++ [y]) hk
  have hsum : ((v.bits.take k).map fun y => (List.replicate 7 true ++ [y]).length).sum = 8 * k := by
    have : (fun y : Bool => (List.replicate 7 true ++ [y]).length) = fun _ => 8 := by
      funext y
      simp
    rw [this, List.map_const', List.sum_replicate, List.length_take, Nat.min_eq_left hk.le,
      smul_eq_mul, Nat.mul_comm]
  rw [hsum] at h₂
  refine ⟨?_, ?_, ?_⟩
  · simpa using h₂ 0 (by simp)
  · simpa [Nat.add_assoc] using h₂ 3 (by simp)
  · simpa [Nat.add_assoc] using h₂ 7 (by simp)

/-- **The end of a literal**: after the groups of the digits, the fourth bit is `false` and the
eighth bit is the polarity; the literal ends ten bits after the digits. -/
theorem literal_end {v : ℕ} {b : Bool} (h : InfixAt w p (literalBits v b)) :
    w[p + 8 * v.bits.length]? = some true ∧ w[p + 8 * v.bits.length + 3]? = some false ∧
      w[p + 8 * v.bits.length + 7]? = some b := by
  have h₂ := (append.mp h).2
  have hlen : (v.bits.flatMap fun y => List.replicate 7 true ++ [y]).length =
      8 * v.bits.length := by
    rw [List.length_flatMap]
    have : (fun y : Bool => (List.replicate 7 true ++ [y]).length) = fun _ => 8 := by
      funext y
      simp
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  rw [hlen] at h₂
  refine ⟨?_, ?_, ?_⟩
  · exact h₂ 0 (by simp)
  · rw [Nat.add_assoc]
    exact h₂ 3 (by simp)
  · rw [Nat.add_assoc]
    exact h₂ 7 (by simp)

/-- **A literal of a clause**, at the offset of the literals before it. -/
theorem clause_literal {c : Clause ℕ} (h : InfixAt w p (clauseBits c)) {j : ℕ}
    (hj : j < c.length) :
    InfixAt w (p + ((c.take j).map fun l => (literalBits l.1 l.2).length).sum)
      (literalBits c[j].1 c[j].2) := by
  have h' : InfixAt w p (c.flatMap (fun l => literalBits l.1 l.2) ++ [false]) := h
  have h₃ := InfixAt.flatMap (L := c) (f := fun l => literalBits l.1 l.2) (append.mp h').1 hj
  beta_reduce at h₃
  exact h₃

/-- **The end of a clause**: `false` after all its literals. -/
theorem clause_end {c : Clause ℕ} (h : InfixAt w p (clauseBits c)) :
    w[p + (c.map fun l => (literalBits l.1 l.2).length).sum]? = some false := by
  have h' : InfixAt w p (c.flatMap (fun l => literalBits l.1 l.2) ++ [false]) := h
  have := (append.mp h').2 0 (by simp)
  rw [List.length_flatMap, Nat.add_zero] at this
  exact this

end InfixAt

/-- The position of the clause `i` in an encoded formula. -/
def clauseStart (φ : CNF ℕ) (i : ℕ) : ℕ := ((φ.take i).map fun c => (clauseBits c).length).sum

/-- **The clauses of an encoded formula**, at their positions. -/
theorem infixAt_clauseStart (φ : CNF ℕ) {i : ℕ} (hi : i < φ.length) :
    InfixAt (encCNF φ) (clauseStart φ i) (clauseBits φ[i]) := by
  have h : InfixAt (encCNF φ) 0 (φ.flatMap clauseBits) := fun q _ => by
    rw [encCNF_eq_flatMap, Nat.zero_add]
  simpa [clauseStart] using h.flatMap hi

/-- The encoding ends after the last clause. -/
theorem getElem?_clauseStart_length (φ : CNF ℕ) :
    (encCNF φ)[clauseStart φ φ.length]? = none := by
  rw [List.getElem?_eq_none]
  rw [encCNF_eq_flatMap, List.length_flatMap, clauseStart, List.take_length]

/-- The clause `i + 1` starts after the clause `i`. -/
theorem clauseStart_succ (φ : CNF ℕ) {i : ℕ} (hi : i < φ.length) :
    clauseStart φ (i + 1) = clauseStart φ i + (clauseBits φ[i]).length := by
  rw [clauseStart, clauseStart, List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

namespace InfixAt

variable {w u : List Bool} {p : ℕ}

/-- A nonempty word occurring in `w` ends within `w`. -/
theorem le_length (h : InfixAt w p u) (hu : u ≠ []) : p + u.length ≤ w.length := by
  have hlen : 0 < u.length := List.length_pos_iff.mpr hu
  have := h (u.length - 1) (by omega)
  rw [List.getElem?_eq_getElem (by omega : u.length - 1 < u.length)] at this
  have := (List.getElem?_eq_some_iff.mp this).1
  omega

/-- A literal starts with a marker. -/
theorem literal_start {v : ℕ} {b : Bool} (h : InfixAt w p (literalBits v b)) :
    w[p]? = some true := by
  have := h 0 (by simp)
  rw [Nat.add_zero] at this
  rw [this]
  rcases hv : v.bits with _ | ⟨y, ys⟩ <;> simp [literalBits, hv]

end InfixAt

/-- The literals `ls` occur at the position `p`, followed by the end of their clause. -/
def LitsAt (w : List Bool) (p : ℕ) (ls : Clause ℕ) : Prop :=
  InfixAt w p (ls.flatMap (fun l => literalBits l.1 l.2) ++ [false])

namespace LitsAt

variable {w : List Bool} {p : ℕ}

/-- The end of a clause is `false`. -/
theorem getElem?_nil (h : LitsAt w p []) : w[p]? = some false := by
  simpa using h 0 (by simp)

/-- A literal, then the rest of the clause. -/
theorem cons {l : Literal ℕ} {ls : Clause ℕ} (h : LitsAt w p (l :: ls)) :
    InfixAt w p (literalBits l.1 l.2) ∧ LitsAt w (p + (literalBits l.1 l.2).length) ls := by
  have h' : InfixAt w p (literalBits l.1 l.2 ++
      (ls.flatMap (fun l => literalBits l.1 l.2) ++ [false])) := by
    simpa [LitsAt, List.append_assoc] using h
  exact InfixAt.append.mp h'

/-- A clause ends within the word. -/
theorem le_length {ls : Clause ℕ} (h : LitsAt w p ls) :
    p + (ls.flatMap fun l => literalBits l.1 l.2).length + 1 ≤ w.length := by
  have := InfixAt.le_length h (by simp)
  simpa [Nat.add_assoc] using this

end LitsAt

/-- The clauses `cs` occur at the position `p`, up to the end of the word. -/
def ClausesAt (w : List Bool) (p : ℕ) (cs : CNF ℕ) : Prop :=
  ∀ q, w[p + q]? = (cs.flatMap clauseBits)[q]?

namespace ClausesAt

variable {w : List Bool} {p : ℕ}

/-- The word ends after the clauses. -/
theorem getElem?_nil (h : ClausesAt w p []) : w[p]? = none := by
  simpa using h 0

/-- A clause, then the rest. -/
theorem cons {c : Clause ℕ} {cs : CNF ℕ} (h : ClausesAt w p (c :: cs)) :
    LitsAt w p c ∧ ClausesAt w (p + (clauseBits c).length) cs := by
  refine ⟨fun q hq => ?_, fun q => ?_⟩
  · rw [h q, List.flatMap_cons, List.getElem?_append_left (by simpa [clauseBits] using hq)]
    rfl
  · rw [Nat.add_assoc, h, List.flatMap_cons, List.getElem?_append_right (by omega)]
    simp

end ClausesAt

/-- **The clauses of an encoded formula** occur from its start. -/
theorem clausesAt_encCNF (φ : CNF ℕ) : ClausesAt (encCNF φ) 0 φ := fun q => by
  rw [Nat.zero_add, encCNF_eq_flatMap]

/-- Overwriting a register with its own value changes nothing. -/
theorem set_getD_self {regs : List ℕ} {i : ℕ} (hi : i < regs.length) :
    regs.set i (regs.getD i 0) = regs := by
  rw [List.getD_eq_getElem _ _ hi, List.set_getElem_self]

end TwoSAT

end Cslib.Complexity
