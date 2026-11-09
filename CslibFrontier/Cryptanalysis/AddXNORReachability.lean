/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORSearch
public import Cslib.Algorithms.Lean.TimeM
import all CslibFrontier.Cryptanalysis.AddXNORSwap
import Mathlib.Tactic.Linarith

/-!
# Exact reachable-state computation on binary truth tables

The dynamic program of [WangLvShenZhang2027], Observation 1 (PDF pp. 2, 20).
Tables branch on bits from least to most significant. Addition is pulled back
with an actual ripple carry, and XOR with actual branch exchanges. There is no
unit-cost whole-word arithmetic or unbounded array lookup in the algorithm.

The executable `TimeM` implementation charges each recursive table inspection,
Boolean operation group, list inspection, and constructor. The cost model is an
immutable pointer machine with constant-time projections, allocation and Boolean
operations; operand and target words are supplied as low-to-high bit lists.
Sharing is permitted, garbage collection is uncharged, and the counter itself is
instrumentation. This is a source-level pointer-machine bound, **not** a native
multitape or `WordRAM.Program` compilation certificate. In particular a pointer
is not charged as a single bit. The advertised native bit-time interpretation
still needs that bridge. The source's bound follows at the algorithmic level
without testing all operator strings: the table work per operand is linear in
`2^m`, independently of the number of reachable states.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Cslib.Algorithms.Lean

/-- A complete binary truth table, branching first on the least significant bit. -/
inductive WordTable (α : Type) : ℕ → Type where
  | leaf (value : α) : WordTable α 0
  | node {n : ℕ} (zero one : WordTable α n) : WordTable α (n + 1)

namespace WordTable

/-- Interpret a table on a low-to-high bit list. Missing bits default to zero;
extra bits are ignored. Valid word encodings have exactly the table's depth. -/
@[expose] def get {α : Type} : {m : ℕ} → WordTable α m → List Bool → α
  | 0, .leaf a, _ => a
  | _ + 1, .node l r, bits => (if bits.headD false then r else l).get bits.tail

/-- Interpretation on actual full-width words, used only in specifications. -/
@[expose] def read {α : Type} {m : ℕ} (t : WordTable α m) (s : BitVec m) : α :=
  t.get (stateKey s)

/-- The state key lists the low bit before the remaining word. -/
theorem stateKey_concat {n : ℕ} (s : BitVec n) (b : Bool) :
    stateKey (s.concat b) = b :: stateKey s := by
  simp [stateKey, List.ofFn_succ]

/-- Reading a node selects the child at the low bit. -/
theorem read_node {α : Type} {n : ℕ} (l r : WordTable α n)
    (s : BitVec n) (b : Bool) :
    (node l r).read (s.concat b) = (if b then r else l).read s := by
  simp [read, stateKey_concat, get]

/-- A constant table uses shared immutable children. -/
@[expose] def constant {α : Type} (a : α) : (m : ℕ) → TimeM ℕ (WordTable α m)
  | 0 => ⟨.leaf a, 1⟩
  | m + 1 => do
    let t ← constant a m
    TimeM.tick 1
    return .node t t

/-- A singleton reachable-state table, constructed from the actual initial bits. -/
@[expose] def point : (m : ℕ) → List Bool → TimeM ℕ (WordTable Bool m)
  | 0, _ => ⟨.leaf true, 1⟩
  | m + 1, bits => do
    let z ← constant false m
    let t ← point m bits.tail
    TimeM.tick 3
    return if bits.headD false then .node z t else .node t z

/-- Pull back a table by addition with carry-in. Both result branches are
computed by a ripple-carry recursion on the actual operand bits. -/
@[expose] def addPull {α : Type} : {m : ℕ} → List Bool → Bool → WordTable α m →
    TimeM ℕ (WordTable α m)
  | 0, _, _, .leaf x => ⟨.leaf x, 1⟩
  | _ + 1, bits, carry, .node l r => do
    let a := bits.headD false
    let z ← addPull bits.tail (Bool.atLeastTwo false a carry) (if a ^^ carry then r else l)
    let o ← addPull bits.tail (Bool.atLeastTwo true a carry) (if !(a ^^ carry) then r else l)
    TimeM.tick 16
    return .node z o

/-- Pull back by XOR, exchanging the branches selected by the operand bit. -/
@[expose] def xorPull {α : Type} : {m : ℕ} → List Bool → WordTable α m →
    TimeM ℕ (WordTable α m)
  | 0, _, .leaf x => ⟨.leaf x, 1⟩
  | _ + 1, bits, .node l r => do
    let z ← xorPull bits.tail (if bits.headD false then r else l)
    let o ← xorPull bits.tail (if bits.headD false then l else r)
    TimeM.tick 6
    return .node z o

/-- Pointwise Boolean union visits the actual two tables together. -/
@[expose] def union : {m : ℕ} → WordTable Bool m → WordTable Bool m →
    TimeM ℕ (WordTable Bool m)
  | 0, .leaf a, .leaf b => ⟨.leaf (a || b), 2⟩
  | _ + 1, .node a b, .node c d => do
    let z ← union a c
    let o ← union b d
    TimeM.tick 3
    return .node z o

/-- Complement the operand bit list, charging its actual traversal. -/
@[expose] def complement : List Bool → TimeM ℕ (List Bool)
  | [] => ⟨[], 1⟩
  | b :: bs => do
    let tail ← complement bs
    TimeM.tick 3
    return (!b) :: tail

/-- The reachable-state update is the union of inverse addition and inverse XNOR. -/
@[expose] def advance {m : ℕ} (bits : List Bool) (t : WordTable Bool m) :
    TimeM ℕ (WordTable Bool m) := do
  let neg ← complement bits
  let a ← addPull neg true t
  let x ← xorPull neg t
  union a x

/-- Execute all layers, retaining only the current table in the source algorithm. -/
@[expose] def run {m : ℕ} : List (List Bool) → WordTable Bool m →
    TimeM ℕ (WordTable Bool m)
  | [], t => ⟨t, 1⟩
  | a :: as, t => do
    let next ← advance a t
    let result ← run as next
    TimeM.tick 2
    return result

/-- Read one answer by following its actual target bits. -/
@[expose] def lookup : {m : ℕ} → WordTable Bool m → List Bool → TimeM ℕ Bool
  | 0, .leaf a, _ => ⟨a, 1⟩
  | _ + 1, .node l r, bits => do
    let a ← lookup (if bits.headD false then r else l) bits.tail
    TimeM.tick 3
    return a

/-- Exact decision from fixed-width bit-list input; no word decoding is executed. -/
@[expose] def decide (m : ℕ) (as : List (List Bool)) (s t : List Bool) : TimeM ℕ Bool := do
  let initial ← point m s
  let final ← run as initial
  lookup final t

@[simp] theorem constant_read {α : Type} (a : α) (m : ℕ) (s : BitVec m) :
    (constant a m).ret.read s = a := by
  induction m with
  | zero => rfl
  | succ n ih =>
    obtain ⟨⟨s, b⟩, rfl⟩ := (concat_bijective n).2 s
    simp only [constant, TimeM.ret_bind, TimeM.ret_pure, read_node]
    cases b <;> exact ih s

/-- Singleton initialization represents equality of full words, including width zero. -/
theorem point_read (m : ℕ) (s t : BitVec m) :
    (point m (stateKey s)).ret.read t = (if s = t then true else false) := by
  induction m with
  | zero => have : s = t := Subsingleton.elim _ _; subst t; simp [point, read, get]
  | succ n ih =>
    obtain ⟨⟨s, b⟩, rfl⟩ := (concat_bijective n).2 s
    obtain ⟨⟨t, c⟩, rfl⟩ := (concat_bijective n).2 t
    cases b <;> cases c <;>
      simp [point, stateKey_concat, read_node, ih, concat_eq_iff, constant_read]

/-- The ripple recursion computes true modular addition, rather than an assigned map. -/
theorem addPull_read {α : Type} {m : ℕ} (table : WordTable α m)
    (a s : BitVec m) (carry : Bool) :
    (addPull (stateKey a) carry table).ret.read s =
      table.read (s + a + BitVec.ofNat m carry.toNat) := by
  induction table generalizing carry with
  | leaf v => rfl
  | @node n l r ihl ihr =>
    obtain ⟨⟨a, b⟩, rfl⟩ := (concat_bijective n).2 a
    obtain ⟨⟨s, c⟩, rfl⟩ := (concat_bijective n).2 s
    rw [concat_add_carry]
    cases b <;> cases c <;> cases carry <;>
      simp [addPull, stateKey_concat, read_node, ihl, ihr, Bool.atLeastTwo]

/-- Branch exchange computes XOR on the actual full-width words. -/
theorem xorPull_read {α : Type} {m : ℕ} (table : WordTable α m) (a s : BitVec m) :
    (xorPull (stateKey a) table).ret.read s = table.read (s ^^^ a) := by
  induction table with
  | leaf v => rfl
  | @node n l r ihl ihr =>
    obtain ⟨⟨a, b⟩, rfl⟩ := (concat_bijective n).2 a
    obtain ⟨⟨s, c⟩, rfl⟩ := (concat_bijective n).2 s
    cases b <;> cases c <;>
      simp [xorPull, stateKey_concat, read_node, BitVec.concat_xor_concat, ihl, ihr]

/-- Union has the expected pointwise meaning, including overlapping tables. -/
theorem union_read {m : ℕ} (a b : WordTable Bool m) (s : BitVec m) :
    (union a b).ret.read s = (a.read s || b.read s) := by
  induction a with
  | leaf a => cases b; rfl
  | @node n left right iha ihb =>
    cases b with
    | node c d =>
      obtain ⟨⟨s, bit⟩, rfl⟩ := (concat_bijective n).2 s
      cases bit <;> simp [union, read_node, iha, ihb]

@[simp] theorem complement_ret (bits : List Bool) :
    (complement bits).ret = bits.map Bool.not := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [complement, ih]

/-- Bit-list complementation agrees with full-width word complementation. -/
theorem complement_key {m : ℕ} (a : BitVec m) :
    (stateKey a).map Bool.not = stateKey (~~~a) := by
  simp [stateKey, List.map_ofFn, Function.comp_def]

/-- One actual update reaches precisely the predecessors under the two allowed steps. -/
theorem advance_read {m : ℕ} (table : WordTable Bool m) (a t : BitVec m) :
    (advance (stateKey a) table).ret.read t =
      (table.read (unstep false t a) || table.read (unstep true t a)) := by
  simp only [advance, TimeM.ret_bind, complement_ret, complement_key, union_read,
    addPull_read, xorPull_read, unstep, Bool.false_eq_true, ↓reduceIte, Bool.toNat_true]
  congr 1
  · congr 1
    simp [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, add_assoc]
  · congr 1
    simp [BitVec.not_xor_right]

/-- Each layer implements the reachable-state recurrence on unrestricted operators. -/
theorem run_read {m : ℕ} (as : List (BitVec m)) (table : WordTable Bool m) (t : BitVec m) :
    (run (as.map stateKey) table).ret.read t = true ↔
      ∃ bs : List Bool, bs.length = as.length ∧
        table.read (backward (bs.zip as) t) = true := by
  induction as generalizing table with
  | nil => simp [run, backward]
  | cons a as ih =>
    simp only [List.map_cons, run, TimeM.ret_bind, TimeM.ret_pure, ih]
    constructor
    · rintro ⟨bs, hlen, hb⟩
      rw [advance_read, Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · exact ⟨false :: bs, by simp [hlen], hb⟩
      · exact ⟨true :: bs, by simp [hlen], hb⟩
    · rintro ⟨bs, hlen, hb⟩
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
        refine ⟨bs, by simpa using hlen, ?_⟩
        rw [advance_read, Bool.or_eq_true]
        cases b with
        | false => exact Or.inl hb
        | true => exact Or.inr hb

@[simp] theorem lookup_ret {m : ℕ} (table : WordTable Bool m) (bits : List Bool) :
    (lookup table bits).ret = table.get bits := by
  induction table generalizing bits with
  | leaf v => rfl
  | node l r ihl ihr =>
    simp only [lookup, TimeM.ret_bind, TimeM.ret_pure, get]
    cases bits.headD false <;> simp [ihl, ihr]

/-- Correctness and completeness of the executable dynamic program for every width. -/
theorem decide_correct {m : ℕ} (as : List (BitVec m)) (s t : BitVec m) :
    (WordTable.decide m (as.map stateKey) (stateKey s) (stateKey t)).ret = true ↔
      Solvable as s t := by
  simp only [WordTable.decide, TimeM.ret_bind, lookup_ret]
  change (run (as.map stateKey) (point m (stateKey s)).ret).ret.read t = true ↔ _
  rw [run_read]
  simp only [point_read, ite_eq_left_iff, Bool.false_eq_true, imp_false, not_not]
  constructor
  · rintro ⟨bs, hlen, hb⟩
    exact ⟨bs, hlen, by rw [hb, eval_backward]⟩
  · rintro ⟨bs, hlen, he⟩
    exact ⟨bs, hlen, by rw [← he, backward_eval]⟩

/-- Constant construction follows one shared child at each level. -/
theorem constant_time {α : Type} (a : α) (m : ℕ) :
    (constant a m).time = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [constant, ih, Nat.add_assoc]

/-- Singleton construction includes the zero siblings and input-bit traversal. -/
theorem point_time_le (m : ℕ) (bits : List Bool) :
    (point m bits).time ≤ (m + 1) * (m + 4) := by
  induction m generalizing bits with
  | zero => simp [point]
  | succ m ih =>
    have h := ih bits.tail
    simp only [point, TimeM.time_bind, constant_time, TimeM.time_tick, TimeM.time_pure]
    nlinarith

/-- Exact ripple traversal cost, derived from its two actual recursive calls. -/
theorem addPull_time {α : Type} {m : ℕ} (table : WordTable α m)
    (bits : List Bool) (carry : Bool) :
    (addPull bits carry table).time + 16 = 17 * 2 ^ m := by
  induction m generalizing bits carry with
  | zero => cases table; rfl
  | succ m ih =>
    cases table with
    | node l r =>
      have hz := ih (if bits.headD false ^^ carry then r else l) bits.tail
        (Bool.atLeastTwo false (bits.headD false) carry)
      have ho := ih (if !(bits.headD false ^^ carry) then r else l) bits.tail
        (Bool.atLeastTwo true (bits.headD false) carry)
      simp only [addPull, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, pow_succ]
      omega

/-- XOR traverses the table, rather than treating a permutation as a unit operation. -/
theorem xorPull_time {α : Type} {m : ℕ} (table : WordTable α m) (bits : List Bool) :
    (xorPull bits table).time + 6 = 7 * 2 ^ m := by
  induction m generalizing bits with
  | zero => cases table; rfl
  | succ m ih =>
    cases table with
    | node l r =>
      have hz := ih (if bits.headD false then r else l) bits.tail
      have ho := ih (if bits.headD false then l else r) bits.tail
      simp only [xorPull, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, pow_succ]
      omega

/-- Union charges all leaves as well as the internal nodes. -/
theorem union_time {m : ℕ} (a b : WordTable Bool m) :
    (union a b).time + 3 = 5 * 2 ^ m := by
  induction a with
  | leaf v => cases b; rfl
  | node l r ihl ihr =>
    cases b with
    | node c d =>
      have hz := ihl c
      have ho := ihr d
      simp only [union, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, pow_succ]
      omega

/-- The operand traversal is linear in its actual supplied list length. -/
theorem complement_time (bits : List Bool) :
    (complement bits).time = 3 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [complement, ih]; omega

/-- One reachable-state layer costs a linear table traversal, including operand handling. -/
theorem advance_time_le {m : ℕ} (bits : List Bool) (t : WordTable Bool m) :
    (advance bits t).time ≤ 29 * 2 ^ m + 3 * bits.length + 1 := by
  have ha := addPull_time t (complement bits).ret true
  have hx := xorPull_time t (complement bits).ret
  have hu := union_time (addPull (complement bits).ret true t).ret
    (xorPull (complement bits).ret t).ret
  simp only [advance, TimeM.time_bind, complement_time]
  omega

/-- Accumulated cost depends on operand count and word width, not witness count. -/
theorem run_time_le {m : ℕ} (as : List (List Bool)) (t : WordTable Bool m)
    (hwidth : ∀ a ∈ as, a.length ≤ m) :
    (run as t).time ≤ as.length * (29 * 2 ^ m + 3 * m + 3) + 1 := by
  induction as generalizing t with
  | nil => simp [run]
  | cons a as ih =>
    have ha := advance_time_le a t
    have hw := hwidth a List.mem_cons_self
    have hr := ih (advance a t).ret (fun b hb => hwidth b (List.mem_cons_of_mem _ hb))
    simp only [run, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
    nlinarith

/-- Target lookup follows only one branch per actual input bit. -/
theorem lookup_time {m : ℕ} (table : WordTable Bool m) (bits : List Bool) :
    (lookup table bits).time = 3 * m + 1 := by
  induction m generalizing bits with
  | zero => cases table; rfl
  | succ m ih =>
    cases table with
    | node l r =>
      simp only [lookup, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      rw [ih]
      omega

/-- Complete executable decision bound in the explicitly stated pointer/Boolean model.
Neither this cost nor its exponential dependence is defined by the desired bound. -/
theorem decide_time_le (m : ℕ) (as : List (List Bool)) (s t : List Bool)
    (hwidth : ∀ a ∈ as, a.length ≤ m) :
    (WordTable.decide m as s t).time ≤
      (m + 1) * (m + 4) + as.length * (29 * 2 ^ m + 3 * m + 3) + 3 * m + 2 := by
  have hp := point_time_le m s
  have hr := run_time_le as (point m s).ret hwidth
  simp only [WordTable.decide, TimeM.time_bind, lookup_time]
  omega

/-- The derived source-model bound has the advertised linear-table exponential
shape. The model remains the pointer/Boolean model stated above, not native
multitape bit complexity. -/
theorem decide_linear_table_work (m : ℕ) (as : List (List Bool)) (s t : List Bool)
    (hwidth : ∀ a ∈ as, a.length ≤ m) :
    (WordTable.decide m as s t).time ≤ 40 * (as.length + 1) * (m + 1) * 2 ^ m := by
  have h := decide_time_le m as s t hwidth
  have hp : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hp1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hinit : (m + 1) * (m + 4) ≤ 4 * (m + 1) * 2 ^ m := by
    nlinarith [Nat.mul_le_mul_left (m + 1) (show m + 4 ≤ 4 * 2 ^ m by omega)]
  have hround : as.length * (29 * 2 ^ m + 3 * m + 3) ≤ as.length * (32 * 2 ^ m) := by
    exact Nat.mul_le_mul_left _ (by omega)
  have htail : 3 * m + 2 ≤ 3 * (m + 1) * 2 ^ m := by nlinarith
  have hcross : 0 ≤ as.length * m * 2 ^ m := Nat.zero_le _
  nlinarith

end WordTable

end Cslib.Cryptanalysis.AddXNOR
