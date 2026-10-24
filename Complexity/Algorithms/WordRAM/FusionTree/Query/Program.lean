/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node
public import Complexity.Algorithms.WordRAM.FusionTree.Binary
public import Complexity.Computability.WordRAM.Compile

/-!
# Actual fusion-tree traversal instructions

The traversal uses eight caller registers, disjoint from both node routines. A width-indexed
choice of node code is made at compilation. The stored tree, its keys and its query remain
runtime inputs. Leaves return an option as a presence flag and a full-key value.

## Main definitions

* `QueryProgram.registers`, `QueryProgram.query`, `QueryProgram.pointer`, `QueryProgram.rank`,
  `QueryProgram.active`, `QueryProgram.found`, `QueryProgram.value`, `QueryProgram.one`,
  `QueryProgram.zero`, `QueryProgram.address`, `QueryProgram.tag`, `QueryProgram.offset`: register
  allocation for the fusion-tree traversal.
* `QueryProgram.setup`, `QueryProgram.leaf`, `QueryProgram.follow`, `QueryProgram.node`,
  `QueryProgram.internal`, `QueryProgram.body`, `QueryProgram.loop`, `QueryProgram.code`,
  `QueryProgram.program`: initialization, leaf inspection, child-pointer descent, node dispatch,
  and the complete structured and flat query programs.
* `QueryProgram.answer`: the conventional two-register option encoding.
* `QueryProgram.Entry`, `QueryProgram.initialized`, `QueryProgram.leafResult`,
  `QueryProgram.followResult`: traversal register invariant and step-result data states.

## Main results

* `QueryProgram.exec_leaf`: literal leaf loads and inclusive full-key comparison.
* `QueryProgram.exec_follow`: the actual stride-two child-pointer load.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.QueryProgram

open Cslib.WordRAM

/-- Both node subroutines use the same fixed register file. -/
abbrev registers : ℕ := 1024
/-- Query key, preserved throughout traversal. -/
abbrev query : Fin registers := 0
/-- Current record pointer. -/
abbrev pointer : Fin registers := 1
/-- Inclusive rank returned by either node routine. -/
abbrev rank : Fin registers := 2
/-- Loop flag. -/
abbrev active : Fin registers := 31
/-- Answer presence flag. -/
abbrev found : Fin registers := 32
/-- Answer full key, zero on absence. -/
abbrev value : Fin registers := 33
/-- Constant one. -/
abbrev one : Fin registers := 34
/-- Constant zero. -/
abbrev zero : Fin registers := 35
/-- Address scratch. -/
abbrev address : Fin registers := 36
/-- Record tag, then leaf key. -/
abbrev tag : Fin registers := 37
/-- Leaf presence or child-table offset. -/
abbrev offset : Fin registers := 38

/-- Conventional presence/value representation, including key zero. -/
def answer (x : Data registers) : Option ℕ :=
  if x.regs found = 0 then none else some (x.regs value)

/-- Constant-register installation is part of the charged query. -/
def setup : Code .standard registers := ram[
  active ← #1; found ← #0; value ← #0; one ← #1; zero ← #0 ]

/-- Inspect a literal leaf record; comparison is inclusive at equality. -/
def leaf : Code .standard registers := ram[
  address ← pointer + one;
  offset ← *address;
  if offset = zero then [active ← #0] else [
    address ← address + one;
    tag ← *address;
    if query < tag then [active ← #0] else [
      found ← one; value ← tag; active ← #0 ] ] ]

/-- Positive rank `r` selects pointer entry `p + 19 + 2(r-1)`. -/
def follow : Code .standard registers := ram[
  offset ← #19;
  address ← rank - one;
  address ← address + address;
  address ← pointer + address;
  address ← address + offset;
  pointer ← *address ]

/-- Code selection depends only on the physical word width. -/
def node (w : ℕ) : Code .standard registers :=
  if 9 ≤ Nat.log 2 w then NodeProgram.code w else BinaryNodeProgram.code

/-- Zero rank terminates with absence; positive rank follows an actual stored pointer. -/
def internal (w : ℕ) : Code .standard registers := ram[
  ⟪node w⟫;
  if rank = zero then [active ← #0] else [⟪follow⟫] ]

/-- One traversal iteration first loads the current record tag. -/
def body (w : ℕ) : Code .standard registers := ram[
  tag ← *pointer;
  if tag = zero then [⟪leaf⟫] else [⟪internal w⟫] ]

/-- Descent terminates at a leaf or a zero child rank. -/
def loop (w : ℕ) : Code .standard registers := .loop (.lt zero active) (body w)

/-- Actual width-indexed query code, with initialization included. -/
def code (w : ℕ) : Code .standard registers := .seq setup (loop w)

/-- Flat query program; it halts with the value register, with presence retained in `found`. -/
def program (w : ℕ) : Program .standard registers := (code w).program value

/-- Persistent registers before visiting a record. No scratch-register assumptions occur. -/
structure Entry (q p : ℕ) (x : Data registers) : Prop where
  query_eq : x.regs query = q
  pointer_eq : x.regs pointer = p
  active_eq : x.regs active = 1
  found_eq : x.regs found = 0
  value_eq : x.regs value = 0
  one_eq : x.regs one = 1
  zero_eq : x.regs zero = 0

/-- Initialization data, with arbitrary preexisting workspace and memory. -/
def initialized (x : Data registers) : Data registers :=
  ((((x.set active 1).set found 0).set value 0).set one 1).set zero 0

/-- Five charged constant instructions establish all traversal constants. -/
theorem exec_initialize {w : ℕ} (x : Data registers) (hw : Fits w 1) :
    Exec w setup x (initialized x) 5 ∧
      Entry (x.regs query) (x.regs pointer) (initialized x) := by
  refine ⟨?_, ?_⟩
  · ram_eval [setup, initialized, hw, fits_zero w]
  · constructor <;> simp +decide [initialized]

/-- Updating traversal scratch preserves the entry invariant. -/
theorem Entry.set_scratch {q p : ℕ} {x : Data registers} (hx : Entry q p x)
    (i : Fin registers) (hi : 36 ≤ i.val) (hi' : i.val ≤ 38) (v : ℕ) :
    Entry q p (x.set i v) := by
  have hne (j : Fin registers) (hj : j.val < 36) : j ≠ i := by
    intro he
    have := congrArg Fin.val he
    omega
  rcases hx with ⟨hq, hp, ha, hf, hv, ho, hz⟩
  constructor <;> simp only [Data.set_regs]
  all_goals rw [Function.update_of_ne (hne _ (by decide))]
  all_goals assumption

/-- Exact literal leaf execution data. -/
def leafResult (x : Data registers) (p q : ℕ) : Data registers :=
  let u := (x.set address (p + 1)).set offset (x.mem (p + 1))
  if x.mem (p + 1) = 0 then u.set active 0
  else
    let v := (u.set address (p + 2)).set tag (x.mem (p + 2))
    if q < x.mem (p + 2) then v.set active 0
    else ((v.set found 1).set value (x.mem (p + 2))).set active 0

/-- Charged presence/key loads and comparisons need at most twelve instructions. -/
theorem exec_leaf {w q p : ℕ} {x : Data registers} (hx : Entry q p x)
    (ha : Fits w (p + 2)) :
    ExecWithin w leaf x (leafResult x p q) 12 := by
  have hp1 := ha.of_le (show p + 1 ≤ p + 2 by omega)
  rcases hx with ⟨hq, hp, _, _, _, ho, hz⟩
  by_cases hn : x.mem (p + 1) = 0
  · ram_eval [leaf, leafResult, hp, hq, ho, hz, hn, hp1, ha, fits_zero w]
  · by_cases hlt : q < x.mem (p + 2)
    · ram_eval [leaf, leafResult, hp, hq, ho, hz, hn, hlt, hp1, ha, fits_zero w]
    · ram_eval [leaf, leafResult, hp, hq, ho, hz, hn, hlt, hp1, ha, fits_zero w]

/-- Leaf execution stops, preserves memory and query, and returns a canonical option. -/
theorem leafResult_spec {q p : ℕ} {x : Data registers} (hx : Entry q p x) :
    (leafResult x p q).regs active = 0 ∧ (leafResult x p q).regs zero = 0 ∧
      (leafResult x p q).mem = x.mem ∧ (leafResult x p q).regs query = q ∧
      (leafResult x p q).regs found ≤ 1 ∧
      answer (leafResult x p q) =
        (if x.mem (p + 1) = 0 ∨ q < x.mem (p + 2) then none
         else some (x.mem (p + 2))) := by
  rcases hx with ⟨hq, hp, ha, hf, hv, ho, hz⟩
  by_cases hn : x.mem (p + 1) = 0
  · simp +decide [leafResult, hn, answer, hq, hf, hz]
  · by_cases hlt : q < x.mem (p + 2) <;>
      simp +decide [leafResult, hn, hlt, answer, hq, hf, hz]

/-- Literal register updates and load for the selected child pointer. -/
def followResult (x : Data registers) (p r : ℕ) : Data registers :=
  let u := ((x.set offset 19).set address (r - 1)).set address (2 * (r - 1))
  let v := (u.set address (p + 2 * (r - 1))).set address (p + 19 + 2 * (r - 1))
  v.set pointer (x.mem (p + 19 + 2 * (r - 1)))

/-- Six real instructions compute and load the interleaved pointer. -/
theorem exec_follow {w q p r : ℕ} {x : Data registers} (hx : Entry q p x)
    (hr : x.regs rank = r) (ha : Fits w (p + 19 + 2 * (r - 1))) :
    Exec w follow x (followResult x p r) 6 := by
  have h19 := ha.of_le (show 19 ≤ p + 19 + 2 * (r - 1) by omega)
  have hr1 := ha.of_le (show r - 1 ≤ p + 19 + 2 * (r - 1) by omega)
  have hr2 := ha.of_le (show 2 * (r - 1) ≤ p + 19 + 2 * (r - 1) by omega)
  have hp2 := ha.of_le (show p + 2 * (r - 1) ≤ p + 19 + 2 * (r - 1) by omega)
  have ha' : Fits w (p + 2 * (r - 1) + 19) := by convert ha using 1; omega
  rcases hx with ⟨hq, hp, _, _, _, ho, hz⟩
  ram_eval [follow, followResult, hr, hp, ho, h19, hr1, hr2, hp2, ha',
    ← two_mul, show p + 2 * (r - 1) + 19 = p + 19 + 2 * (r - 1) by omega, ha]

/-- Following a child preserves the invariant, changing only the current record address. -/
theorem followResult_entry {q p r : ℕ} {x : Data registers} (hx : Entry q p x) :
    Entry q (x.mem (p + 19 + 2 * (r - 1))) (followResult x p r) := by
  rcases hx with ⟨hq, hp, ha, hf, hv, ho, hz⟩
  constructor <;> simp +decide [followResult, hq, ha, hf, hv, ho, hz]

/-- Child-pointer traversal has no memory writes. -/
theorem followResult_mem (x : Data registers) (p r : ℕ) :
    (followResult x p r).mem = x.mem := rfl

end Cslib.Algorithms.WordRAM.FusionTree.QueryProgram
