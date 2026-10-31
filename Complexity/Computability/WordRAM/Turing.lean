/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Native
public import Complexity.Computability.WordRAM.Function
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Word-RAM polynomial time gives Turing-machine polynomial time

A fixed word-RAM program that runs within polynomially many instructions gives a multi-tape Turing
machine computing the same function in polynomial time, in the sense of
`Turing.MultiTapeTM.ComputableInPolyTime`. This is the polynomial simulation of random access
machines by Turing machines [Cook and Reckhow][CookReckhow1973], for the unit-cost word RAM with a
word size polynomial in the input length.

## Conventions

* **Cost model.** Unit cost per instruction, the final `halt` included, on `w`-bit words whose
  overflow faults (`WordRAM.Executes`). Each operation of the basis must have a polynomial-time
  checked implementation on a unary width and binary operands; `Basis.standard`, `Basis.additive`,
  `Basis.arithmetic` and `Basis.exact` have one (`WordRAM.Native`).
* **Input.** The instance `a` is given as the bit string `encIn a`. A polynomial-time machine
  computes its word list `encode a` (binary words, framed by `encList encNat`), and the simulation
  stores it as the memory of `State.init (encode a)`: the length at address `0` and the words at
  `1, …, n`. Both conversions are charged.
* **Word size.** The simulating machine computes the word size itself, in unary, as a polynomial in
  `|encIn a|`. In the general theorem the caller supplies this width schedule and its certificate;
  the corollaries choose a width at least the logarithmic threshold `logWidth k (size a)` and the
  encoded length of the input words, which makes the input fit. Since the word-RAM predicates
  promise correctness and the time bound at every admitted fitting width, simulating one such width
  suffices.
* **Output.** The returned word, in binary (`encNat`).
* **Overhead.** Polynomial: the simulator runs `FiniteState.run` for a number of steps polynomial
  in `|encIn a|`, each polynomial in the word size and the number of stored cells, which grows by
  at most one per step (`WordBounded.length_resultEncoding_run_le`). The parameterized machine
  time is that of `WordRAM.transport_inO`; no closed-form degree is stated.

## Limits

These theorems cover one fixed program (`UniformComputableInPolyTime`). A width-indexed family
(`WordRAM.ComputableInPolyTime`) may choose arbitrary, even uncomputable, code at each width, so it
gives Turing-machine polynomial time only with a computable code map, which is not provided. The
size measure must be polynomially bounded in the encoded input length: a polynomial instruction
count in the numeric value of an input number is exponential in its bit length and does not
transfer. Width-dependent word encodings are covered only by the general theorem, with a width
schedule chosen by the caller. Outputs are single words.

## Main definitions

* `Cslib.WordRAM.initEntries`, `Cslib.WordRAM.initMemory`, `Cslib.WordRAM.initState`: the stored
  cells, finite memory and finite simulation state of `State.init`.
* `Cslib.WordRAM.WordBounded`: registers, memory default and stored cells of a finite simulation
  state are `w`-bit words.
* `Cslib.WordRAM.instrTarget`, `Cslib.WordRAM.labelBound`: jump targets and a bound on every
  control label reachable by a program.
* `Cslib.WordRAM.stateBound`: a bound on the encoded size of a word-bounded simulation state.

## Main results

* `Cslib.WordRAM.denote_initState`, `Cslib.WordRAM.initMemory_polyTime`: initialization is
  faithful and polynomial-time.
* `Cslib.WordRAM.wordBounded_initState`, `Cslib.WordRAM.WordBounded.run`,
  `Cslib.WordRAM.WordBounded.length_resultEncoding_run_le`: from a fitting input, simulation states
  hold words and their encodings grow polynomially along a run.
* `Cslib.WordRAM.inputFits_of_length_encList_le`: a word list fits its own encoded length.
* `Cslib.WordRAM.exists_unary_majorant`: a quantity polynomially bounded in the input length has a
  majorant computable in unary in polynomial time.
* `Cslib.WordRAM.Program.DecidesInTime.computesInTime`: a decider computes the indicator.
* `Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime_of_width`: the simulation at a
  supplied polynomial-time width schedule.
* `Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime`,
  `Cslib.WordRAM.UniformComputableInPolyTime.turingComputableInPolyTime`: uniform polynomial
  word-RAM time gives `Turing.MultiTapeTM.ComputableInPolyTime`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM
open Cslib.GenericRAM

/-! ## Word bounds on finite simulation states -/

section Invariant

open GenericRAM.FiniteState

variable {B : Basis} {r w : ℕ}

/-- The jump or branch target of an instruction, and `0` otherwise. -/
def instrTarget : GenericRAM.Instr B.genericModel r → ℕ
  | .jump t => t
  | .branch _ t => t
  | _ => 0

/-- An upper bound on every control label that a run from label `0` reaches. -/
def labelBound (p : GenericRAM.Program B.genericModel r) : ℕ :=
  p.length + (p.map instrTarget).sum

/-- A bound on the encoded outcome of a simulation step with `r` registers, labels at most `L`,
`w`-bit words and at most `E` stored cells. -/
def stateBound (r L w E : ℕ) : ℕ :=
  2 * (encNat L).length + 2 * r * (2 * w + 1) + 2 * w + E * (6 * w + 3) + w + 5

/-- Registers, the memory default and every stored cell (address and value) of a finite
simulation state are `w`-bit words. -/
structure WordBounded (w : ℕ) (s : FiniteState B.genericModel r) : Prop where
  /-- Every register holds a `w`-bit word. -/
  regs_lt : ∀ i, s.regs i < 2 ^ w
  /-- The memory default is a `w`-bit word. -/
  default_lt : s.default < 2 ^ w
  /-- Every stored address and value is a `w`-bit word. -/
  entries_lt : ∀ e ∈ SparseMemory.entries s.memory, e.1 < 2 ^ w ∧ e.2 < 2 ^ w

namespace WordBounded

variable {s t : FiniteState B.genericModel r}

/-- Reading memory returns a `w`-bit word. -/
theorem read_lt (h : WordBounded w s) (a : ℕ) :
    SparseMemory.read s.default a s.memory < 2 ^ w := by
  rw [SparseMemory.read_eq_find]
  cases hf : (SparseMemory.entries s.memory).find? (fun e => decide (a = e.1)) with
  | none => simpa using h.default_lt
  | some e => simpa using (h.entries_lt e (List.mem_of_find?_eq_some hf)).2

/-- Setting a register to a word preserves the bound. -/
theorem set (h : WordBounded w s) (d : Fin r) {v : ℕ} (hv : v < 2 ^ w) :
    WordBounded w (s.set d v) where
  regs_lt i := by
    simp only [FiniteState.set]
    rcases eq_or_ne i d with rfl | hi
    · simpa using hv
    · simpa [Function.update_of_ne hi] using h.regs_lt i
  default_lt := h.default_lt
  entries_lt := h.entries_lt

/-- Storing a word at a word address preserves the bound. -/
theorem write (h : WordBounded w s) {a v : ℕ} (ha : a < 2 ^ w) (hv : v < 2 ^ w) :
    WordBounded w (s.write a v) where
  regs_lt := h.regs_lt
  default_lt := h.default_lt
  entries_lt e he := by
    rcases SparseMemory.mem_entries_insert.mp he with rfl | ⟨he, -⟩
    · exact ⟨ha, hv⟩
    · exact h.entries_lt e he

/-- Changing the control label preserves the bound. -/
theorem withPC (h : WordBounded w s) (pc : ℕ) : WordBounded w { s with pc := pc } where
  regs_lt := h.regs_lt
  default_lt := h.default_lt
  entries_lt := h.entries_lt

private theorem lt_of_checkedConstant {c v : ℕ}
    (h : B.genericModel.checkedConstant c w = some v) : v < 2 ^ w := by
  simp only [GenericRAM.Model.checkedConstant, Basis.genericModel, bind, Option.bind_some] at h
  split at h
  · next hc => cases h; simpa [fits_iff] using hc
  · cases h

private theorem lt_of_checkedOp {f : B.Op} {args : Fin (B.Arity f) → ℕ} {v : ℕ}
    (h : B.genericModel.checkedOp f (w, args) = some v) : v < 2 ^ w := by
  simp only [GenericRAM.Model.checkedOp, Basis.genericModel, bind, Option.bind_eq_some_iff] at h
  obtain ⟨u, -, hu⟩ := h
  split at hu
  · next hc => cases hu; simpa [fits_iff] using hc
  · cases hu

/-- A data instruction keeps every register and stored cell a word. -/
theorem evalOp (h : WordBounded w s) {o : GenericRAM.Op B.genericModel r}
    (ho : FiniteState.evalOp w o s = some t) : WordBounded w t := by
  cases o with
  | const d c =>
    simp only [FiniteState.evalOp, Option.map_eq_some_iff] at ho
    obtain ⟨v, hv, rfl⟩ := ho
    exact h.set d (lt_of_checkedConstant hv)
  | copy d src =>
    simp only [FiniteState.evalOp, FiniteState.move, Basis.genericModel, ite_true,
      Option.some.injEq] at ho
    subst ho
    exact h.set d (h.regs_lt src)
  | alu f d args =>
    simp only [FiniteState.evalOp, Option.map_eq_some_iff] at ho
    obtain ⟨v, hv, rfl⟩ := ho
    exact h.set d (lt_of_checkedOp hv)
  | load d a =>
    simp only [FiniteState.evalOp, FiniteState.move, Basis.genericModel, bind,
      Option.bind_some, ite_true, Option.some.injEq] at ho
    subst ho
    exact h.set d (h.read_lt _)
  | store a src =>
    simp only [FiniteState.evalOp, Basis.genericModel, bind, Option.bind_some, ite_true,
      Option.some.injEq] at ho
    subst ho
    exact h.write (h.regs_lt a) (h.regs_lt src)

private theorem instrTarget_le_sum {p : GenericRAM.Program B.genericModel r}
    {i : GenericRAM.Instr B.genericModel r} (hi : i ∈ p) :
    instrTarget i ≤ (p.map instrTarget).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem hi)

/-- A continuing step keeps the word bound and stays below the label bound. -/
theorem step {p : GenericRAM.Program B.genericModel r} (h : WordBounded w s)
    (hs : FiniteState.step w p s = some (.inl t)) :
    WordBounded w t ∧ t.pc ≤ labelBound p := by
  unfold FiniteState.step at hs
  simp only [Basis.genericModel, ite_true] at hs
  rw [dispatch_eq_getElem? w p 0 s (Nat.zero_le _), Nat.sub_zero] at hs
  simp only [bind, Option.bind_eq_some_iff] at hs
  obtain ⟨i, hi, hs⟩ := hs
  have hmem : i ∈ p := List.mem_of_getElem? hi
  have hlt : s.pc < p.length := (List.getElem?_eq_some_iff.mp hi).1
  have htarget := instrTarget_le_sum hmem
  cases i with
  | op o =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
    obtain ⟨u, ho, hr⟩ := hs
    simp only [resume, Basis.genericModel, ite_true, Option.some.injEq, Sum.inl.injEq] at hr
    subst hr
    exact ⟨(h.evalOp ho).withPC _, by simp [labelBound]; omega⟩
  | jump target =>
    simp only [evalInstr, resume, Basis.genericModel, ite_true, Option.some.injEq,
      Sum.inl.injEq] at hs
    subst hs
    exact ⟨h.withPC _, by simp only [labelBound, instrTarget] at htarget ⊢; omega⟩
  | branch c target =>
    cases c with
    | test f args =>
      simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
      obtain ⟨b, -, hr⟩ := hs
      simp only [resume, Basis.genericModel, ite_true, Option.some.injEq, Sum.inl.injEq] at hr
      subst hr
      refine ⟨h.withPC _, ?_⟩
      simp only [labelBound, instrTarget] at htarget ⊢
      split <;> omega
  | halt idx =>
    simp only [evalInstr, Basis.genericModel, ite_true] at hs
    cases hs

/-- A halting step returns a word. -/
theorem step_halt {p : GenericRAM.Program B.genericModel r} {v : ℕ} (h : WordBounded w s)
    (hs : FiniteState.step w p s = some (.inr v)) : v < 2 ^ w := by
  unfold FiniteState.step at hs
  simp only [Basis.genericModel, ite_true] at hs
  rw [dispatch_eq_getElem? w p 0 s (Nat.zero_le _), Nat.sub_zero] at hs
  simp only [bind, Option.bind_eq_some_iff] at hs
  obtain ⟨i, -, hs⟩ := hs
  cases i with
  | op o =>
    simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
    obtain ⟨u, -, hr⟩ := hs
    simp [resume, Basis.genericModel] at hr
  | jump target => simp [evalInstr, resume, Basis.genericModel] at hs
  | branch c target =>
    cases c with
    | test f args =>
      simp only [evalInstr, bind, Option.bind_eq_some_iff] at hs
      obtain ⟨b, -, hr⟩ := hs
      simp [resume, Basis.genericModel] at hr
  | halt idx =>
    simp only [evalInstr, Basis.genericModel, ite_true, Option.some.injEq, Sum.inr.injEq] at hs
    subst hs
    exact h.regs_lt idx

/-- Every outcome of a clocked run from a word-bounded state below the label bound is
word-bounded: continuing states keep their words and labels, and halted values are words. -/
theorem run {p : GenericRAM.Program B.genericModel r} (h : WordBounded w s)
    (hpc : s.pc ≤ labelBound p) (n : ℕ) :
    (∀ t, FiniteState.run w p n s = some (.inl t) → WordBounded w t ∧ t.pc ≤ labelBound p) ∧
      (∀ v, FiniteState.run w p n s = some (.inr v) → v < 2 ^ w) := by
  induction n generalizing s with
  | zero =>
    refine ⟨fun t ht => ?_, fun v hv => by simp at hv⟩
    simp only [FiniteState.run_zero, Option.some.injEq, Sum.inl.injEq] at ht
    subst ht
    exact ⟨h, hpc⟩
  | succ n ih =>
    rw [FiniteState.run_succ]
    cases hs : FiniteState.step w p s with
    | none => simp
    | some u =>
      cases u with
      | inl u =>
        obtain ⟨hu, hupc⟩ := h.step hs
        exact ih hu hupc
      | inr v =>
        refine ⟨fun t ht => by simp at ht, fun v' hv => ?_⟩
        simp only [Option.some.injEq, Sum.inr.injEq] at hv
        subst hv
        exact h.step_halt hs

private theorem listMax_le {α : Type*} {f : α → ℕ} {l : List α} {m : ℕ}
    (h : ∀ a ∈ l, f a ≤ m) : listMax f l ≤ m := by
  induction l with
  | nil => simp [listMax]
  | cons a l ih =>
    simp only [listMax, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h a (List.mem_cons_self ..)) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem length_encNat_le_of_lt {v : ℕ} (hv : v < 2 ^ w) : (encNat v).length ≤ w := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr hv

/-- Encoded outcomes along a clocked run from a word-bounded state are bounded by `stateBound`,
with at most one new stored cell per step. -/
theorem length_resultEncoding_run_le {p : GenericRAM.Program B.genericModel r}
    (h : WordBounded w s) (hpc : s.pc ≤ labelBound p) (n : ℕ) :
    (resultEncoding B.encoding (FiniteState.run w p n s)).length ≤
      stateBound r (labelBound p) w ((SparseMemory.entries s.memory).length + n) := by
  obtain ⟨hinl, hinr⟩ := h.run hpc n
  cases hrun : FiniteState.run w p n s with
  | none => simp [resultEncoding, encOption_none]
  | some u =>
    cases u with
    | inr v =>
      have hv := length_encNat_le_of_lt (hinr v hrun)
      simp only [resultEncoding, encOption_some, encSum_inr, List.length_cons, Basis.encoding,
        stateBound]
      omega
    | inl t =>
      obtain ⟨ht, htpc⟩ := hinl t hrun
      have hE := length_entries_run_le hrun
      have hlen := FiniteState.length_encoding_le B.encoding t
        (bound := w) fun i => length_encNat_le_of_lt (ht.regs_lt i)
      have hpcl : (encNat t.pc).length ≤ (encNat (labelBound p)).length := by
        simp only [encNat_apply, Nat.size_eq_bits_len]
        exact Nat.size_le_size htpc
      have hdef : (B.encoding.value t.default).length ≤ w :=
        length_encNat_le_of_lt ht.default_lt
      have hkey : SparseMemory.maxKeyLength B.encoding.address t.memory ≤ w :=
        listMax_le fun e he => length_encNat_le_of_lt (ht.entries_lt e he).1
      have hval : SparseMemory.maxValueLength B.encoding.value t.memory ≤ w :=
        listMax_le fun e he => length_encNat_le_of_lt (ht.entries_lt e he).2
      have hmul : (SparseMemory.entries t.memory).length *
            (4 * SparseMemory.maxKeyLength B.encoding.address t.memory +
              2 * SparseMemory.maxValueLength B.encoding.value t.memory + 3) ≤
          ((SparseMemory.entries s.memory).length + n) * (6 * w + 3) :=
        Nat.mul_le_mul hE (by omega)
      simp only [resultEncoding, encOption_some, encSum_inl, List.length_cons, stateBound]
      omega

end WordBounded

end Invariant

/-! ## Initialization -/

section Init

/-- The stored cells of `State.init input`: the length at address `0`, word `i` at `i + 1`. -/
def initEntries (input : List ℕ) : List (ℕ × ℕ) :=
  (0, input.length) :: input.zipIdx.map fun e => (e.2 + 1, e.1)

private theorem keys_zipIdx (l : List ℕ) (n : ℕ) :
    ((l.zipIdx n).map fun e => (e.2 + 1, e.1)).map Prod.fst = List.range' (n + 1) l.length := by
  induction l generalizing n with
  | nil => rfl
  | cons v l ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ, ih]

private theorem nodup_keys_initEntries (input : List ℕ) :
    ((initEntries input).map Prod.fst).Nodup := by
  simp only [initEntries, List.map_cons, keys_zipIdx]
  refine List.nodup_cons.mpr ⟨?_, List.nodup_range'⟩
  simp

/-- The finite memory of `State.init input`. -/
def initMemory (input : List ℕ) : SparseMemory ℕ ℕ :=
  ⟨(initEntries input).map fun e => ⟨e.1, e.2⟩, by
    unfold List.NodupKeys List.keys
    simpa [List.map_map, Function.comp_def] using nodup_keys_initEntries input⟩

theorem entries_initMemory (input : List ℕ) :
    SparseMemory.entries (initMemory input) = initEntries input := by
  simp [SparseMemory.entries, initMemory, List.map_map, Function.comp_def]

private theorem find_zipIdx (l : List ℕ) (n a : ℕ) :
    (((l.zipIdx n).map fun e => (e.2 + 1, e.1)).find? (fun e => decide (a = e.1))).map
        Prod.snd = if n < a then l[a - n - 1]? else none := by
  induction l generalizing n with
  | nil => split <;> simp
  | cons v l ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.find?_cons]
    by_cases ha : a = n + 1
    · subst ha
      simp
    · simp only [ha, decide_false]
      rw [ih]
      by_cases h1 : n + 1 < a
      · have he : a - n - 1 = a - (n + 1) - 1 + 1 := by omega
        simp [h1, show n < a by omega, he]
      · simp [h1, show ¬n < a by omega]

/-- `initMemory` stores the input convention of `State.init`. -/
theorem read_initMemory (input : List ℕ) (a : ℕ) :
    SparseMemory.read 0 a (initMemory input) =
      if a = 0 then input.length else input.getD (a - 1) 0 := by
  rw [SparseMemory.read_eq_find, entries_initMemory, initEntries, List.find?_cons]
  rcases a with _ | a
  · simp
  · have h := find_zipIdx input 0 (a + 1)
    simp only [Nat.add_one_ne_zero, decide_false, ite_false, Nat.zero_lt_succ, ite_true,
      Nat.sub_zero, Nat.add_sub_cancel] at h ⊢
    rw [h, List.getD_eq_getElem?_getD]

/-- The finite simulation state of `State.init input`, at label `0` with zero registers. -/
def initState (B : Basis) (r : ℕ) (input : List ℕ) : FiniteState B.genericModel r :=
  FiniteState.initConst 0 0 (initMemory input)

/-- The finite initial state denotes `State.init`. -/
theorem denote_initState {B : Basis} {r : ℕ} (input : List ℕ) :
    (initState B r input).denote = (State.init input : State r).toGeneric B := by
  simp only [FiniteState.denote, initState, FiniteState.initConst, FiniteState.init,
    State.toGeneric, State.init, Data.toGeneric, Data.init]
  congr 2
  funext a
  exact read_initMemory input a

/-- From an input that fits, the finite initial state holds only words. -/
theorem wordBounded_initState {B : Basis} {r w : ℕ} {input : List ℕ}
    (h : InputFits w input) : WordBounded w (initState B r input) where
  regs_lt _ := Nat.two_pow_pos w
  default_lt := Nat.two_pow_pos w
  entries_lt e he := by
    simp only [initState, FiniteState.initConst, FiniteState.init, entries_initMemory,
      initEntries, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨⟨v, i⟩, hvi, rfl⟩
    · exact ⟨Nat.two_pow_pos w, h.1⟩
    · obtain ⟨hi, hv⟩ := List.mem_zipIdx' hvi
      refine ⟨lt_of_le_of_lt (show i + 1 ≤ input.length by omega) h.1, ?_⟩
      simpa [hv, fits_iff] using h.2 _ (List.getElem_mem hi)

@[simp] theorem initState_pc {B : Basis} {r : ℕ} (input : List ℕ) :
    (initState B r input).pc = 0 := rfl

theorem length_entries_initState {B : Basis} {r : ℕ} (input : List ℕ) :
    (SparseMemory.entries (initState B r input).memory).length = input.length + 1 := by
  simp [initState, FiniteState.initConst, FiniteState.init, entries_initMemory, initEntries]

/-- Building the initial memory is polynomial-time on framed lists of binary words. -/
theorem initMemory_polyTime :
    Turing.MultiTapeTM.ComputableInPolyTime initMemory (encList encNat)
      (SparseMemory.encoding encNat encNat) := by
  have hentries : Turing.MultiTapeTM.ComputableInPolyTime initEntries (encList encNat)
      (encList (encPair encNat encNat)) := by
    unfold initEntries
    fun_prop
  exact hentries.of_enc_eq fun l => by
    simp only [SparseMemory.encoding_apply, entries_initMemory]

/-- A word list fits every word size at least as large as its encoded length. -/
theorem inputFits_of_length_encList_le {w : ℕ} {input : List ℕ}
    (h : (encList encNat input).length ≤ w) : InputFits w input := by
  refine ⟨lt_of_le_of_lt ((length_le_length_encList encNat input).trans h)
    Nat.lt_two_pow_self, fun v hv => ?_⟩
  have hsum := (List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => (encNat x).length) hv)).trans
    (sum_length_le_length_encList encNat input)
  have hsize : v.size ≤ w := by
    rw [← Nat.size_eq_bits_len, ← encNat_apply] at *
    exact hsum.trans h
  exact lt_of_lt_of_le (Nat.lt_size_self v) (Nat.pow_le_pow_right (by norm_num) hsize)

end Init

/-! ## Word RAM ⇒ Turing machine -/

section Main

open NativeCertificate

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- A decider computes the indicator of its problem, `1` on members and `0` otherwise, with the
same time bound and admitted widths. -/
theorem Program.DecidesInTime.computesInTime {p : Program B r} {encode : ℕ → α → List ℕ}
    {A : Set α} {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} [DecidablePred (· ∈ A)]
    (h : p.DecidesInTime encode A time allowed) :
    p.ComputesInTime encode time allowed fun a => if a ∈ A then 1 else 0 := by
  intro a w hw hi
  obtain ⟨v, n, hv, hn, hle, hiff⟩ := h a w hw hi
  change Executes w p _ v n at hv
  refine ⟨n, ?_, hn⟩
  by_cases ha : a ∈ A
  · simpa only [ha, ite_true, (hiff.mpr ha)] using hv
  · have hv0 : v = 0 := by have := mt hiff.mp ha; omega
    simpa only [ha, ite_false, hv0] using hv

/-- A quantity polynomially bounded in the encoded input length has a majorant computable in
unary in polynomial time: a fixed polynomial of the input length. -/
theorem exists_unary_majorant {u : α → ℕ}
    (h : PolyBounded (fun a => (encIn a).length) u) :
    ∃ g : α → ℕ, Turing.MultiTapeTM.ComputableInPolyTime g encIn encUnary ∧ ∀ a, u a ≤ g a := by
  obtain ⟨c, d, h⟩ := h.exists_le
  refine ⟨fun a => (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (encIn a).length,
    (Turing.MultiTapeTM.ComputableInPolyTime.unary_eval _).comp
      (Turing.MultiTapeTM.ComputableInPolyTime.encoding_length encIn),
    fun a => ?_⟩
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one] using h a

/-- **Word-RAM time at a polynomial-time width schedule gives Turing-machine polynomial time.**

Let `p` be a fixed program over a basis whose checked operations are polynomial-time on a unary
width and binary operands. Suppose `width a` is computable in unary in polynomial time, is an
admitted width for `a`, and the word list `encode (width a) a` fits it and is computable in
polynomial time from `encIn a`. If `p` computes `f` (`Program.ComputesInTime`) and its time bound
at `width a` is polynomial in `|encIn a|`, then `f` is computable in polynomial time with binary
output. The simulating machine computes the width, the input words and a step budget, builds the
initial memory and runs the finite-state simulator; all of this is charged. -/
theorem Program.ComputesInTime.turingComputableInPolyTime_of_width
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → ℕ}
    (h : p.ComputesInTime encode time allowed f) {width : α → ℕ}
    (hwidth : Turing.MultiTapeTM.ComputableInPolyTime width encIn encUnary)
    (hallowed : ∀ a, allowed a (width a))
    (hfits : ∀ a, InputFits (width a) (encode (width a) a))
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime (fun a => encode (width a) a) encIn
      (encList encNat))
    (htime : PolyBounded (fun a => (encIn a).length) (fun a => time a (width a))) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat := by
  -- The step budget: a polynomial of the input length, computed in unary.
  obtain ⟨steps, hstepsU, hsteps⟩ := exists_unary_majorant htime
  have hstepsT : Turing.MultiTapeTM.ComputableInPolyTime steps encIn encNat :=
    Turing.MultiTapeTM.ComputableInPolyTime.unary_to_binary.comp hstepsU
  have hExec (a : α) :
      ∃ m ≤ steps a, Executes (width a) p (State.init (encode (width a) a)) (f a) m := by
    obtain ⟨m, hm, hle⟩ := h a (width a) (hallowed a) (hfits a)
    exact ⟨m, hle.trans (hsteps a), hm⟩
  -- Initialization: the memory `0 ↦ n, i + 1 ↦ xᵢ`, zero registers and default.
  have hmem : Turing.MultiTapeTM.ComputableInPolyTime
      (fun a => initMemory (encode (width a) a)) encIn (SparseMemory.encoding encNat encNat) :=
    initMemory_polyTime.comp hencode
  let cInit := FiniteState.initConstCertificate (r := r) B.encoding
    (NativeCertificate.const (ei := encIn) 0) (NativeCertificate.const 0) (ofPolyTime hmem)
  have hInit : cInit.IsPolynomial :=
    FiniteState.initConstCertificate_isPolynomial _ _ _ _ (const_isPolynomial 0)
      (const_isPolynomial 0) (ofPolyTime_isPolynomial hmem)
  -- Every simulated outcome is bounded by a polynomial in the input length.
  let bound : α → ℕ := fun a => stateBound r (labelBound p.toGeneric) (width a)
    ((encode (width a) a).length + 1 + steps a)
  have hbound : PolyBounded (fun a => (encIn a).length) bound := by
    have hw := hwidth.polyBounded
    have hE : PolyBounded (fun a => (encIn a).length)
        (fun a => (encode (width a) a).length + 1 + steps a) :=
      ((hencode.polyBounded_length.mono fun a =>
        length_le_length_encList encNat (encode (width a) a)).add (.const 1)).add
          hstepsU.polyBounded
    exact (((((PolyBounded.const _).add ((PolyBounded.const (2 * r)).mul
      (((PolyBounded.const 2).mul hw).add (.const 1)))).add ((PolyBounded.const 2).mul hw)).add
      (hE.mul (((PolyBounded.const 6).mul hw).add (.const 3)))).add hw).add (.const 5)
  have hOutLen (a : α) (j : ℕ) (hj : j ≤ steps a) :
      (FiniteState.resultEncoding B.encoding (FiniteState.run (width a) p.toGeneric j
        (initState B r (encode (width a) a)))).length ≤ bound a := by
    have hrun := (wordBounded_initState (B := B) (r := r) (hfits a)).length_resultEncoding_run_le
      (p := p.toGeneric) (by simp) j
    rw [length_entries_initState] at hrun
    refine hrun.trans ?_
    simp only [bound, stateBound]
    have := Nat.mul_le_mul_right (6 * width a + 3)
      (show (encode (width a) a).length + 1 + j ≤ (encode (width a) a).length + 1 + steps a by
        omega)
    omega
  exact WordRAM.transport_polyTime B.encoding (B.nativePrimitivesOfPolyTime hop) p
    (ofPolyTime hstepsT) (ofPolyTime hwidth) cInit
    (u := fun a => State.init (encode (width a) a))
    (fun a => denote_initState (encode (width a) a)) hExec
    (B.nativePrimitivesOfPolyTime_isPolynomial hop) (ofPolyTime_isPolynomial hstepsT)
    (ofPolyTime_isPolynomial hwidth) hInit hstepsU.polyBounded hbound hOutLen

/-- **Polynomial word-RAM time gives Turing-machine polynomial time** for a fixed program.

Let `p` be a fixed program over a basis whose checked operations are polynomial-time on a unary
width and binary operands. Suppose that on every input `a` whose words fit, at every word size of
at least `logWidth k (size a)`, `p` halts with `f a` from `State.init (encode a)` within
`T (size a)` instructions, where `T` is polynomially bounded. If the word list `encode a` is
computable in polynomial time from the bit string `encIn a` and `size a` is polynomially bounded
in `|encIn a|`, then `f` is computable in polynomial time with binary output.

The simulating machine chooses a word size polynomial in `|encIn a|`, at least
`logWidth k (size a)` and the encoded length of the input words, so the input fits. -/
theorem Program.ComputesInTime.turingComputableInPolyTime
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : α → List ℕ} {size f : α → ℕ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolynomiallyBounded T) (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (h : p.ComputesInTime (fun _ => encode) (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w) f) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat := by
  have hlog : PolyBounded (fun a => (encIn a).length) (fun a => logWidth k (size a)) :=
    ((PolyBounded.const k).mul (hsize.add (.const 1))).mono fun a =>
      Nat.mul_le_mul_left k (Nat.add_le_add_right (Nat.log_le_self 2 (size a)) 1)
  obtain ⟨width, hwidth, hge⟩ := exists_unary_majorant
    (hlog.add (hencode.polyBounded_length (encMid := encList encNat)))
  exact h.turingComputableInPolyTime_of_width hop hwidth (fun a => by have := hge a; omega)
    (fun a => inputFits_of_length_encList_le (by have := hge a; omega)) hencode
    ((PolyBounded.of_polynomiallyBounded id hT).comp hsize)

/-- **Uniform polynomial word-RAM time gives Turing-machine polynomial time**, for a
width-independent word encoding computable in polynomial time and a size measure polynomially
bounded in the encoded input length. -/
theorem UniformComputableInPolyTime.turingComputableInPolyTime
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {encode : α → List ℕ} {size f : α → ℕ}
    (h : UniformComputableInPolyTime B f (fun _ => encode) size)
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat)) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn encNat := by
  obtain ⟨T, hT, k, -, r, p, hp⟩ := h
  exact hp.turingComputableInPolyTime hop hT hsize hencode

end Main

end Cslib.WordRAM
