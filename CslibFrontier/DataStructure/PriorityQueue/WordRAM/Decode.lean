/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.Basic
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Decoding indexed priority-queue answers

These equations apply the existing `PQCode.decode` to actual output-register values. Presence
flags may be any nonzero word; keys and handles are unshifted, and extraction retains the
decoder's handle-range check. These generic decoding equations alone imply no execution or word
bounds. For native typed calls, `nativeResultCode_spec` certifies an actual paid suffix that
normalizes flags and copies lookup keys to one fixed canonical result bank.

## Main results

* `PQCode.decode_isEmpty`: decode a Boolean flag.
* `PQCode.decode_getKey_none`, `PQCode.decode_getKey_some`: decode an optional key.
* `PQCode.decode_extractMin_none`, `PQCode.decode_extractMin_some`: decode an optional typed entry.
* `PQCode.nativeResultCode_spec`: native conversion, canonical parsing, and register/memory framing.
* `PQCode.nativeResultRecoding`: preserve a checked implementation's representation and potential.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.PQCode

open Cslib.WordRAM Cslib.DataStructure.PriorityQueue

variable {B : Basis} {r n K : ℕ} (P : PQCode B r) (regs : Fin r → ℕ)

/-- A canonical Boolean output flag decodes to that Boolean. -/
theorem decode_isEmpty {b : Bool} (hflag : regs P.outFlag = b.toNat) :
    P.decode (n := n) (K_max := K) .isEmpty regs = some b := by
  cases b <;> simp [decode, hflag]

/-- A zero flag decodes to an absent key, regardless of the unused key register. -/
theorem decode_getKey_none (v : Fin n) (hflag : regs P.outFlag = 0) :
    P.decode (K_max := K) (.getKey v) regs = some none := by
  simp [decode, hflag]

/-- A nonzero flag decodes the actual unshifted key register. -/
theorem decode_getKey_some (v : Fin n) {k : ℕ} (hflag : regs P.outFlag ≠ 0)
    (hkey : regs P.outK = k) :
    P.decode (K_max := K) (.getKey v) regs = some (some k) := by
  simp [decode, hflag, hkey]

/-- A zero flag decodes to no extracted entry, even when no handle exists. -/
theorem decode_extractMin_none (hflag : regs P.outFlag = 0) :
    P.decode (n := n) (K_max := K) .extractMin regs = some none := by
  simp [decode, hflag]

/-- A nonzero flag with an actual in-range handle and key decodes to that typed entry. -/
theorem decode_extractMin_some (v : Fin n) {k : ℕ} (hflag : regs P.outFlag ≠ 0)
    (hhandle : regs P.outV = v.val) (hkey : regs P.outK = k) :
    P.decode (K_max := K) .extractMin regs = some (some (v, k)) := by
  simp [decode, hflag, hhandle, hkey, v.isLt]

/-- Canonical structural result format for indexed queues. Its layout depends only on the
result type: flag, then optional handle and key words. -/
@[expose] def nativeResultType (n : ℕ) : IndexedMinPQ.Op n → ResultType
  | .isEmpty => .bool
  | .getKey _ => .option .nat
  | .insert _ _ | .decreaseKey _ _ => .unit
  | .extractMin => .option (.prod (.fin n) .nat)

/-- The indexed queue's explicit canonical result type agrees definitionally with its result. -/
theorem nativeResultType_eq (n K : ℕ) (o : IndexedMinPQ.Op n) :
    (indexedMinPQSpec n K).Result o = (nativeResultType n o).Value := by
  cases o <;> rfl

/-- One fixed output bank: tag, handle (or the copied lookup key), and extraction key. -/
@[expose] def nativeResultBank (P : PQCode B r) (i : ℕ) : Fin r :=
  if i = 0 then P.outFlag else if i = 1 then P.outV else P.outK

/-- The original dispatch tag bits identify the completed operation. The paid conversion reads
these machine words; the operation parameter only states the required precondition. -/
@[expose] def nativeResultReady (P : PQCode B r) {n : ℕ} : IndexedMinPQ.Op n → Data r → Prop
  | .isEmpty, x => x.regs P.tag2 = 0 ∧ x.regs P.tag1 = 0 ∧ x.regs P.tag0 = 0
  | .getKey _, x => x.regs P.tag2 = 0 ∧ x.regs P.tag1 = 0 ∧ x.regs P.tag0 ≠ 0
  | .insert _ _, x => x.regs P.tag2 = 0 ∧ x.regs P.tag1 ≠ 0 ∧ x.regs P.tag0 = 0
  | .decreaseKey _ _, x => x.regs P.tag2 = 0 ∧ x.regs P.tag1 ≠ 0 ∧ x.regs P.tag0 ≠ 0
  | .extractMin, x => x.regs P.tag2 ≠ 0

/-- Paid result conversion: lookup copies its key to the common first payload slot, and every
presence/Boolean flag is reduced to exactly zero or one by native control. -/
@[expose] def nativeResultCode (P : PQCode .standard r) (zero : Fin r) : Code .standard r :=
  .seq
    (.branch (.eq P.tag2 zero)
      (.branch (.eq P.tag1 zero)
        (.branch (.eq P.tag0 zero) (.op (.copy P.outV P.outV))
          (.op (.copy P.outV P.outK)))
        (.op (.copy P.outV P.outV)))
      (.op (.copy P.outV P.outV)))
    (.branch (.eq P.outFlag zero) (.op (.const P.outFlag 0)) (.op (.const P.outFlag 1)))

/-- The conversion runs within eight instructions, produces the canonical observation, and
preserves all memory and all registers except the two result slots it writes. -/
theorem nativeResultCode_spec (P : PQCode .standard r) (zero : Fin r)
    (hfv : P.outFlag ≠ P.outV) (hfk : P.outFlag ≠ P.outK)
    (hvz : P.outV ≠ zero)
    {w : ℕ} {x : Data r} (h1 : Fits w 1) (hzero : x.regs zero = 0)
    {n K : ℕ} (o : IndexedMinPQ.Op n) (a : (indexedMinPQSpec n K).Result o)
    (hready : P.nativeResultReady o x) (hd : P.decode o x.regs = some a) :
    ∃ y, ExecWithin w (P.nativeResultCode zero) x y 8 ∧
      (nativeResultType n o).decode (y.regs ∘ P.nativeResultBank) 0 =
        some (cast (nativeResultType_eq n K o) a) ∧
      y.mem = x.mem ∧
      ∀ i, i ≠ P.outFlag → i ≠ P.outV → y.regs i = x.regs i := by
  cases o <;> simp only [nativeResultReady] at hready
  all_goals
    unfold nativeResultCode
    wram_exec [hzero, hready, hfv, hfk, hvz] <;>
    simp_all only [ne_eq, ne_comm, StateTransitionSpec.ofFn_result, IndexedMinPQ.Op.Result,
      decode, not_true_eq_false, decide_false, decide_true, Option.some.injEq, Bool.false_eq,
      Bool.true_eq, nativeResultType, ResultType.Value, Data.set, Function.update_eq_self,
      ResultType.decode, Function.comp_apply, nativeResultBank, ↓reduceIte, ↓dreduceIte,
      Function.update_self, not_false_eq_true, one_ne_zero, zero_add, Function.update_of_ne,
      Option.map_eq_some_iff, Option.dite_none_right_eq_some, ResultType.words, Nat.reduceAdd,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.map_bind, Option.map_some, implies_true, and_self, and_true] <;>
    try rfl
  case getKey.neg =>
    exact ⟨x.regs P.outK, hd.symm, by rw [← hd]; rfl⟩
  case extractMin.neg =>
    obtain ⟨hlt, ha⟩ := hd
    rw [← ha]
    simp only [hlt, ↓reduceDIte, Option.bind_some]
    rfl

/-- Convert a checked indexed-queue implementation to canonical native observations. The caller
supplies its zero register and verifies that both output slots are outside persistent state. -/
@[expose] def nativeResultRecoding (P : PQCode .standard r) {w base n K : ℕ}
    {params : Fin 1 → ℕ} {s₀ : IndexedMinPQ.State n}
    (C : Cslib.DataStructure.WordRAM.StateTransitionImpl P.toSubroutineCode
      (indexedMinPQSpec n K) w base params s₀)
    (zero : Fin r) (h1 : Fits w 1)
    (hzero : ∀ {s x}, C.rep s x → x.regs zero = 0)
    (hfv : P.outFlag ≠ P.outV) (hfk : P.outFlag ≠ P.outK) (hvz : P.outV ≠ zero)
    (hflag : P.input P.outFlag = true) (hvalue : P.input P.outV = true)
    (hdecode : C.decode = P.decode) :
    NativeResultRecoding (indexedMinPQSpec n K).Result .standard r w
      C.decode C.rep C.potential where
  code := P.nativeResultCode zero
  resultBank := P.nativeResultBank
  resultType := nativeResultType n
  resultType_eq := nativeResultType_eq n K
  time := 8
  ready := P.nativeResultReady
  execute {s} {x} o a hr hb hready hd := by
    rw [hdecode] at hd
    obtain ⟨y, he, ha, hm, hregs⟩ :=
      P.nativeResultCode_spec zero hfv hfk hvz h1 (hzero hr) o a hready hd
    have hp : ∀ i, P.input i = false → y.regs i = x.regs i := by
      intro i hi
      apply hregs i
      · intro h
        subst i
        simp only [hflag, Bool.true_eq_false] at hi
      · intro h
        subst i
        simp only [hvalue, Bool.true_eq_false] at hi
    have hmem : ∀ a ∈ (Block.mk base C.space).footprint, y.mem a = x.mem a :=
      fun _ _ => congrFun hm _
    exact ⟨y, he, ha, C.rep_supported hp hmem (he.bounded hb) hr,
      C.potential_supported hp hmem hr, hm⟩

end Cslib.DataStructure.PriorityQueue.WordRAM.PQCode
