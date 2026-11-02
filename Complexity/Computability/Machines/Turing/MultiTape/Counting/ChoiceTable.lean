/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Execution
public import Complexity.Computability.Machines.Turing.MultiTape.Counting.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable

/-!
# Parsimonious binary replay of list-choice machines

A transition occurrence is selected by a fixed-width binary block. The native input and work
tapes remain still while the block is read; its last bit performs the selected native action.
Out-of-range indices reject. After the original machine halts, only zero bits are permitted.
The finite control tracks the original output until the first original halt, so a running
output prefix is never accepted. Equal transition occurrences remain separate binary codes.

## Main definitions

* `CountingChoice.table`: the fixed finite binary replay table.

## Main results

* `CountingChoice.acceptCount_table_div`: exact counts at every binary horizon.
* `CountingChoice.acceptCount_table_of_halts`: stable exact counts after all native branches halt.
-/

public section

namespace Turing.MultiTapeCTM

namespace CountingChoice

open MultiTapeNTM.ChoiceTable Cslib

variable {k : ℕ} {State : Type}

/-- The finite scanner remembers one unfinished binary index and the original output track. -/
structure ScanState (width : ℕ) (State : Type) where
  /-- The original control, with `none` denoting canonical terminal padding. -/
  original : Option State
  /-- Empty, accepting, or other original output. -/
  track : OutputTrack
  /-- The number of digits already read in this block. -/
  cursor : Fin width
  /-- The binary prefix. -/
  value : Fin (2 ^ width)
  deriving Fintype

instance {width : ℕ} [Finite State] : Finite (ScanState width State) := by
  let := Fintype.ofFinite State
  infer_instance

private def startState {width : ℕ} (hw : 0 < width) (original : Option State)
    (track : OutputTrack) : ScanState width State :=
  ⟨original, track, ⟨0, hw⟩, ⟨0, by positivity⟩⟩

/-- Permanently reject, including when an accepting terminal marker was already emitted. -/
private def reject {width : ℕ} : Turing.Action k Bool (ScanState width State) :=
  ⟨0, fun _ => (none, 0), some false, none⟩

private def perform {width : ℕ} (hw : 0 < width) (track : OutputTrack)
    (action : Turing.Action k Bool State) : Turing.Action k Bool (ScanState width State) :=
  let track' := track.emit action.output
  ⟨action.inputTape, action.workTapes,
    if action.state = none ∧ track' = .accept then some true else none,
    some (startState hw action.state track')⟩

private def advance {width : ℕ} (hw : 0 < width) (s : ScanState width State) (bit : Bool) :
    ScanState width State :=
  { s with
    cursor := ⟨min (s.cursor.val + 1) (width - 1), by omega⟩
    value := ⟨min (2 * s.value.val + bit.toNat) (2 ^ width - 1), by
      have : 0 < 2 ^ width := by positivity
      omega⟩ }

private def localActions (machine : MultiTapeCTM k Bool State) (state : State)
    (symbol : Option Bool) (work : Fin k → Option Bool) : List (Turing.Action k Bool State) :=
  (machine.tr state symbol work Empty.elim).map MultiTapeMachine.Action.emptyOracleEquiv

private def scan {width : ℕ} (hw : 0 < width) (machine : MultiTapeCTM k Bool State)
    (s : ScanState width State) (symbol : Option Bool) (work : Fin k → Option Bool)
    (bit : Bool) : Turing.Action k Bool (ScanState width State) :=
  match s.original with
  | none => if bit then reject else idle (some s)
  | some state =>
    if s.cursor.val + 1 = width then
      match (localActions machine state symbol work)[2 * s.value.val + bit.toNat]? with
      | none => reject
      | some action => perform hw s.track action
    else idle (some (advance hw s bit))

/-- The binary table preserves each list occurrence and rejects noncanonical terminal padding. -/
def table {width : ℕ} (hw : 0 < width) (machine : MultiTapeCTM k Bool State) :
    MultiTapePTM k Bool (ScanState width State) where
  initial := startState hw (some machine.initial) .empty
  tr s symbol work _ bit := .step (scan hw machine s symbol work bit) Empty.elim Empty.elim

variable {input : List Bool}

private def bufferCfg {width : ℕ} (cfg : Cfg k Bool State input) (state : State)
    (cursor : Fin width) (value : Fin (2 ^ width)) : Cfg k Bool (ScanState width State) input :=
  ⟨some ⟨some state, OutputTrack.ofWord cfg.output, cursor, value⟩,
    cfg.inputPos, cfg.workTapes, cfg.workTapePos, []⟩

private def simCfg {width : ℕ} (hw : 0 < width) (cfg : Cfg k Bool State input) :
    Cfg k Bool (ScanState width State) input :=
  ⟨some (startState hw cfg.state (OutputTrack.ofWord cfg.output)),
    cfg.inputPos, cfg.workTapes, cfg.workTapePos,
    if cfg.state = none ∧ cfg.output = [true] then [true] else []⟩

private theorem initial_table {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (input : List Bool) :
    ((table hw machine).initialConfig input).tapes =
      simCfg hw (Cfg.init machine.initial input) := rfl

private theorem step_table {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) {cfg : Cfg k Bool (ScanState width State) input}
    {s : ScanState width State} (hs : cfg.state = some s) (bit : Bool) :
    ((table hw machine).withCoin bit).toTM.step cfg =
      (scan hw machine s cfg.inputSymbol cfg.workTapeSymbols bit).apply cfg := by
  rw [MultiTapeTM.step_of_state hs, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  rfl

private theorem simCfg_of_running {width : ℕ} (hw : 0 < width)
    (cfg : Cfg k Bool State input) (state : State) (hs : cfg.state = some state) :
    simCfg hw cfg = bufferCfg cfg state ⟨0, hw⟩ ⟨0, by positivity⟩ := by
  simp only [simCfg, startState, hs, reduceCtorEq, false_and, ↓reduceIte, bufferCfg]

private theorem apply_perform {width : ℕ} (hw : 0 < width)
    (cfg : Cfg k Bool State input) (state : State) (cursor : Fin width)
    (value : Fin (2 ^ width)) (action : Turing.Action k Bool State) :
    (perform hw (OutputTrack.ofWord cfg.output) action).apply (bufferCfg cfg state cursor value) =
      simCfg hw (action.apply cfg) := by
  have hacc : (OutputTrack.ofWord cfg.output).emit action.output = .accept ↔
      cfg.output ++ action.output.toList = [true] := by
    rw [← OutputTrack.ofWord_append, OutputTrack.ofWord_eq_accept_iff]
  simp only [perform, simCfg, Action.apply, bufferCfg, startState, Cfg.mk.injEq,
    List.nil_append, OutputTrack.ofWord_append, true_and, hacc]
  split_ifs with h <;> simp [h]

private theorem step_buffer_before_end {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input) (state : State)
    (cursor : Fin width) (value : Fin (2 ^ width)) (bit : Bool)
    (hcursor : cursor.val + 1 < width) (hvalue : 2 * value.val + bit.toNat < 2 ^ width) :
    ((table hw machine).withCoin bit).toTM.step (bufferCfg cfg state cursor value) =
      bufferCfg cfg state ⟨cursor.val + 1, hcursor⟩
        ⟨2 * value.val + bit.toNat, hvalue⟩ := by
  rw [step_table hw machine rfl]
  simp only [scan, bufferCfg, ite_eq_right (by omega : cursor.val + 1 ≠ width)]
  rw [MultiTapeNTM.ChoiceTable.apply_idle]
  simp only [advance, Cfg.mk.injEq, Option.some.injEq, ScanState.mk.injEq,
    and_true, true_and]
  constructor
  · apply Fin.ext
    change min (cursor.val + 1) (width - 1) = cursor.val + 1
    omega
  · apply Fin.ext
    change min (2 * value.val + bit.toNat) (2 ^ width - 1) = 2 * value.val + bit.toNat
    omega

private theorem step_buffer_at_end {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input) (state : State)
    (cursor : Fin width) (value : Fin (2 ^ width)) (bit : Bool)
    (hcursor : cursor.val + 1 = width) (hs : cfg.state = some state)
    {action : Turing.Action k Bool State}
    (hact : (machine.actions cfg)[2 * value.val + bit.toNat]? = some action) :
    ((table hw machine).withCoin bit).toTM.step (bufferCfg cfg state cursor value) =
      simCfg hw (action.apply cfg) := by
  rw [step_table hw machine rfl]
  have hact' : (localActions machine state cfg.inputSymbol cfg.workTapeSymbols)[
      2 * value.val + bit.toNat]? = some action := by
    simpa only [localActions, actions, hs] using hact
  change (scan hw machine _ cfg.inputSymbol cfg.workTapeSymbols bit).apply _ = _
  simp only [scan, bufferCfg, hcursor, ↓reduceIte]
  rw [hact']
  exact apply_perform hw cfg state cursor value action

private theorem stepCoins_prefix {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input) (state : State)
    (hs : cfg.state = some state) (bits : List Bool) (hlen : bits.length < width) :
    (table hw machine).stepCoins bits (simCfg hw cfg) =
      bufferCfg cfg state ⟨bits.length, hlen⟩
        ⟨BitString.binaryValue bits, (BitString.binaryValue_lt_two_pow bits).trans_le
          (Nat.pow_le_pow_right (by norm_num) hlen.le)⟩ := by
  induction bits using List.reverseRecOn with
  | nil =>
    rw [MultiTapePTM.stepCoins_nil, simCfg_of_running hw cfg state hs]
    rfl
  | append_singleton bits bit ih =>
    have hpre : bits.length < width := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hcursor : bits.length + 1 < width := by
      simpa only [List.length_append, List.length_singleton] using hlen
    have hvalue : 2 * BitString.binaryValue bits + bit.toNat < 2 ^ width := by
      rw [← BitString.binaryValue_snoc]
      exact (BitString.binaryValue_lt_two_pow _).trans_le
        (Nat.pow_le_pow_right (by norm_num) hlen.le)
    rw [MultiTapePTM.stepCoins_append, ih hpre, MultiTapePTM.stepCoins_cons,
      MultiTapePTM.stepCoins_nil,
      step_buffer_before_end hw machine cfg state _ _ bit hcursor hvalue]
    simp only [List.length_append, List.length_singleton, BitString.binaryValue_snoc]

private theorem stepCoins_block_of_valid {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input) (state : State)
    (hs : cfg.state = some state) (bits : List Bool) (hlen : bits.length = width)
    {action : Turing.Action k Bool State}
    (hact : (machine.actions cfg)[BitString.binaryValue bits]? = some action) :
    (table hw machine).stepCoins bits (simCfg hw cfg) = simCfg hw (action.apply cfg) := by
  induction bits using List.reverseRecOn with
  | nil => simp only [List.length_nil] at hlen; omega
  | append_singleton bits bit ih =>
    have hpre : bits.length < width := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    rw [MultiTapePTM.stepCoins_append, stepCoins_prefix hw machine cfg state hs bits hpre,
      MultiTapePTM.stepCoins_cons, MultiTapePTM.stepCoins_nil]
    apply step_buffer_at_end hw machine cfg state _ _ bit
    · simpa only [List.length_append, List.length_singleton] using hlen
    · exact hs
    · simpa only [BitString.binaryValue_snoc] using hact


private theorem stepCoins_of_halted {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool (ScanState width State) input)
    (h : cfg.state = none) (bits : List Bool) :
    (table hw machine).stepCoins bits cfg = cfg := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    rw [MultiTapePTM.stepCoins_cons, MultiTapeTM.step_of_halt h, ih]

private theorem reject_ne_accept {width : ℕ}
    (cfg : Cfg k Bool (ScanState width State) input) :
    (reject.apply cfg).output ≠ [true] := by
  simp only [reject, Action.apply, Option.toList_some]
  intro h
  have := congrArg List.getLast? h
  simp at this

private theorem reject_continuation {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool (ScanState width State) input)
    (bits : List Bool) :
    ((table hw machine).stepCoins bits (reject.apply cfg)).output ≠ [true] := by
  rw [stepCoins_of_halted hw machine _ rfl]
  exact reject_ne_accept cfg

private theorem stepCoins_block_of_invalid {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input) (state : State)
    (hs : cfg.state = some state) (bits : List Bool) (hlen : bits.length = width)
    (hact : (machine.actions cfg)[BitString.binaryValue bits]? = none)
    (rest : List Bool) :
    ((table hw machine).stepCoins (bits ++ rest) (simCfg hw cfg)).output ≠ [true] := by
  induction bits using List.reverseRecOn with
  | nil => simp only [List.length_nil] at hlen; omega
  | append_singleton bits bit ih =>
    have hpre : bits.length < width := by
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    rw [MultiTapePTM.stepCoins_append, MultiTapePTM.stepCoins_append,
      stepCoins_prefix hw machine cfg state hs bits hpre, MultiTapePTM.stepCoins_cons,
      MultiTapePTM.stepCoins_nil, step_table hw machine rfl]
    have hcursor : bits.length + 1 = width := by
      simpa only [List.length_append, List.length_singleton] using hlen
    have hact' : (localActions machine state cfg.inputSymbol cfg.workTapeSymbols)[
        2 * BitString.binaryValue bits + bit.toNat]? = none := by
      simpa only [localActions, actions, hs, BitString.binaryValue_snoc] using hact
    simp only [scan, bufferCfg, hcursor, ↓reduceIte]
    change ((table hw machine).stepCoins rest
      ((match (localActions machine state cfg.inputSymbol cfg.workTapeSymbols)[
          2 * BitString.binaryValue bits + bit.toNat]? with
        | none => reject
        | some action => perform hw (OutputTrack.ofWord cfg.output) action).apply _)).output ≠ _
    rw [hact']
    exact reject_continuation hw machine _ rest

private theorem stepCoins_padding {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input)
    (hs : cfg.state = none) (bits : List Bool) :
    ((table hw machine).stepCoins bits (simCfg hw cfg)).output = [true] ↔
      cfg.output = [true] ∧ bits = List.replicate bits.length false := by
  induction bits with
  | nil =>
    simp only [MultiTapePTM.stepCoins_nil, simCfg, hs, List.length_nil,
      List.replicate_zero, and_true]
    split_ifs <;> simp_all
  | cons bit bits ih =>
    rw [MultiTapePTM.stepCoins_cons, step_table hw machine rfl]
    cases bit with
    | false =>
      simp only [scan, simCfg, startState, hs, Bool.false_eq_true, ↓reduceIte]
      rw [apply_idle]
      have hi := ih
      simp only [simCfg, startState, hs] at hi
      rw [hi]
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
    | true =>
      simp only [scan, simCfg, startState, hs, ↓reduceIte]
      have hreject := reject_continuation hw machine (simCfg hw cfg) bits
      simp only [simCfg, hs] at hreject
      constructor
      · exact fun h => (hreject h).elim
      · rintro ⟨_, h⟩
        have := congrArg List.head? h
        simp only [List.length_cons, List.replicate_succ, List.head?_cons, Option.some.injEq,
          Bool.true_eq_false] at this


private theorem binaryCertificate_zeros (width count : ℕ) :
    binaryCertificate width (List.replicate count 0) = List.replicate (count * width) false := by
  induction count with
  | zero => simp only [List.replicate_zero, binaryCertificate, List.flatMap_nil, Nat.zero_mul]
  | succ count ih =>
    change BitString.binaryWord width 0 ++ binaryCertificate width (List.replicate count 0) = _
    rw [ih]
    simp only [BitString.binaryWord, Nat.zero_bits, List.length_nil, Nat.sub_zero,
      List.reverse_nil, List.append_nil, ← List.replicate_add, Nat.succ_mul, Nat.add_comm]

private theorem binaryCertificate_eq_zeros {width : ℕ} {indices : List ℕ}
    (hsmall : ∀ index ∈ indices, index < 2 ^ width) :
    binaryCertificate width indices =
        List.replicate (binaryCertificate width indices).length false ↔
      indices = List.replicate indices.length 0 := by
  rw [length_binaryCertificate hsmall, ← binaryCertificate_zeros]
  constructor
  · intro h
    have h' := congrArg (binaryIndices indices.length width) h
    rw [binaryIndices_binaryCertificate hsmall] at h'
    have hz : (List.replicate indices.length 0).length = indices.length := List.length_replicate
    have hzero := binaryIndices_binaryCertificate (width := width)
      (indices := List.replicate indices.length 0) (by
        intro index hi
        obtain ⟨_, rfl⟩ := List.mem_replicate.mp hi
        positivity)
    rw [hz] at hzero
    rwa [hzero] at h'
  · exact congrArg (binaryCertificate width)

private theorem append_eq_zeros (left right : List Bool) :
    left ++ right = List.replicate (left ++ right).length false ↔
      left = List.replicate left.length false ∧ right = List.replicate right.length false := by
  constructor
  · intro h
    have hz := (List.eq_replicate_iff.mp h).2
    exact ⟨List.eq_replicate_iff.mpr ⟨rfl, fun _ hi => hz _ (List.mem_append_left _ hi)⟩,
      List.eq_replicate_iff.mpr ⟨rfl, fun _ hi => hz _ (List.mem_append_right _ hi)⟩⟩
  · rintro ⟨hl, hr⟩
    rw [List.length_append, hl, hr, ← List.replicate_add]
    simp only [List.length_replicate]

private theorem stepCoins_certificate_suffix {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input)
    (suffix : List Bool) (hshort : suffix.length < width)
    (indices : List ℕ) (hsmall : ∀ index ∈ indices, index < 2 ^ width) :
    ((table hw machine).stepCoins
      (binaryCertificate width indices ++ suffix) (simCfg hw cfg)).output =
      [true] ↔
    (machine.decodeCertificate cfg indices).any (fun r => r.2.output == [true]) = true ∧
      suffix = List.replicate suffix.length false := by
  induction indices generalizing cfg with
  | nil =>
    cases hs : cfg.state with
    | none =>
      simp only [binaryCertificate, List.flatMap_nil, List.nil_append]
      rw [stepCoins_padding hw machine cfg hs]
      simp only [decodeCertificate, hs, List.length_nil, List.replicate_zero, ↓reduceIte,
        Option.any_some, beq_iff_eq]
    | some state =>
      simp only [binaryCertificate, List.flatMap_nil, List.nil_append]
      rw [stepCoins_prefix hw machine cfg state hs suffix hshort]
      simp only [bufferCfg, reduceCtorEq, decodeCertificate, hs, Option.any_none,
        Bool.false_eq_true, false_and]
  | cons index indices ih =>
    cases hs : cfg.state with
    | none =>
      rw [stepCoins_padding hw machine cfg hs, append_eq_zeros,
        binaryCertificate_eq_zeros hsmall, machine.decodeCertificate_of_halted hs]
      split_ifs with h
      · simp only [Option.any_some, beq_iff_eq]
        tauto
      · simp only [Option.any_none, Bool.false_eq_true, false_and]
        tauto
    | some state =>
      have hindex := hsmall index (List.mem_cons_self ..)
      have hrest : ∀ i ∈ indices, i < 2 ^ width :=
        fun i hi => hsmall i (List.mem_cons_of_mem index hi)
      simp only [binaryCertificate, List.flatMap_cons, List.append_assoc]
      change ((table hw machine).stepCoins
        (BitString.binaryWord width index ++ (binaryCertificate width indices ++ suffix))
        (simCfg hw cfg)).output = [true] ↔ _
      cases hact : (machine.actions cfg)[index]? with
      | none =>
        have hn := stepCoins_block_of_invalid hw machine cfg state hs
          (BitString.binaryWord width index) (BitString.length_binaryWord hindex)
          (by simpa only [BitString.binaryValue_binaryWord] using hact)
          (binaryCertificate width indices ++ suffix)
        simp only [decodeCertificate, hs, step?, hact, Option.map_none, bind, Option.bind_none,
          Option.any_none, Bool.false_eq_true, false_and, iff_false]
        exact hn
      | some action =>
        rw [MultiTapePTM.stepCoins_append, stepCoins_block_of_valid hw machine cfg state hs
          (BitString.binaryWord width index) (BitString.length_binaryWord hindex)
          (by simpa only [BitString.binaryValue_binaryWord] using hact), ih _ hrest]
        simp only [decodeCertificate, hs, step?, hact, Option.map_some, bind, Option.bind_some,
          Option.any_map]


private theorem stepCoins_certificate {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input)
    (indices : List ℕ) (hsmall : ∀ index ∈ indices, index < 2 ^ width) :
    ((table hw machine).stepCoins (binaryCertificate width indices) (simCfg hw cfg)).output =
      [true] ↔
    (machine.decodeCertificate cfg indices).any (fun r => r.2.output == [true]) = true := by
  simpa only [List.append_nil, List.length_nil, List.replicate_zero, and_true] using
    stepCoins_certificate_suffix hw machine cfg [] hw indices hsmall

private theorem stepCoins_full {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input)
    (count : ℕ) (word : List Bool) (hlen : word.length = count * width) :
    ((table hw machine).stepCoins word (simCfg hw cfg)).output = [true] ↔
      machine.certificateAccepts (fun out => out == [true]) cfg
        (binaryIndices count width word) = true := by
  have hsmall : ∀ i ∈ binaryIndices count width word, i < 2 ^ width := by
    intro i hi
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hi
    have hr := BitString.length_of_mem_listRows hrow
    simpa only [hr] using BitString.binaryValue_lt_two_pow row
  have h := stepCoins_certificate hw machine cfg (binaryIndices count width word) hsmall
  rw [binaryCertificate_binaryIndices hlen] at h
  exact h

private theorem stepCoins_full_suffix {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (cfg : Cfg k Bool State input)
    (count : ℕ) (word suffix : List Bool) (hlen : word.length = count * width)
    (hshort : suffix.length < width) :
    ((table hw machine).stepCoins (word ++ suffix) (simCfg hw cfg)).output = [true] ↔
      ((table hw machine).stepCoins word (simCfg hw cfg)).output = [true] ∧
      suffix = List.replicate suffix.length false := by
  have hsmall : ∀ i ∈ binaryIndices count width word, i < 2 ^ width := by
    intro i hi
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hi
    have hr := BitString.length_of_mem_listRows hrow
    simpa only [hr] using BitString.binaryValue_lt_two_pow row
  have h := stepCoins_certificate_suffix hw machine cfg suffix hshort
    (binaryIndices count width word) hsmall
  rw [binaryCertificate_binaryIndices hlen] at h
  rw [stepCoins_full hw machine cfg count word hlen]
  exact h

private theorem acceptCount_partial {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (input : List Bool) (count rest : ℕ)
    (hrest : rest < width) :
    (table hw machine).acceptCount input (count * width + rest) =
      (table hw machine).acceptCount input (count * width) := by
  unfold MultiTapePTM.acceptCount Complexity.acceptCount
  let prefWord (word : Fin (count * width + rest) → Bool) : Fin (count * width) → Bool :=
    fun i => word ⟨i.val, by omega⟩
  have hp (word : Fin (count * width + rest) → Bool) :
      List.ofFn (prefWord word) = (List.ofFn word).take (count * width) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take]
      omega
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getElem_take, prefWord]
  have haccept (word : Fin (count * width + rest) → Bool) :
      (table hw machine).runClosedCoins (List.ofFn word) input = [true] ↔
        (table hw machine).runClosedCoins (List.ofFn (prefWord word)) input = [true] ∧
          (List.ofFn word).drop (count * width) = List.replicate rest false := by
    simp only [MultiTapePTM.runClosedCoins_eq_output_stepCoins]
    change ((table hw machine).stepCoins (List.ofFn word)
      (simCfg hw (Cfg.init machine.initial input))).output = [true] ↔ _
    have ht : ((List.ofFn word).take (count * width)).length = count * width := by
      simp only [List.length_take, List.length_ofFn]
      omega
    have hd : ((List.ofFn word).drop (count * width)).length = rest := by
      simp only [List.length_drop, List.length_ofFn, Nat.add_sub_cancel_left]
    have h := stepCoins_full_suffix hw machine (Cfg.init machine.initial input) count
      ((List.ofFn word).take (count * width)) ((List.ofFn word).drop (count * width))
      ht (by rw [hd]; exact hrest)
    rw [List.take_append_drop, hd, ← hp word] at h
    exact h
  refine Finset.card_bij (fun word _ => prefWord word) ?_ ?_ ?_
  · intro word hw'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [decide_eq_true_eq] using
        (haccept word).mp (by
          simpa only [decide_eq_true_eq] using (Finset.mem_filter.mp hw').2) |>.1⟩
  · intro left hl right hr heq
    apply List.ofFn_injective
    have hleft := (haccept left).mp (by
      simpa only [decide_eq_true_eq] using (Finset.mem_filter.mp hl).2)
    have hright := (haccept right).mp (by
      simpa only [decide_eq_true_eq] using (Finset.mem_filter.mp hr).2)
    rw [← List.take_append_drop (count * width) (List.ofFn left),
      ← List.take_append_drop (count * width) (List.ofFn right), hleft.2, hright.2,
      ← hp left, ← hp right, heq]
  · intro word hword
    let extended := BitString.ofList (count * width + rest)
      (List.ofFn word ++ List.replicate rest false)
    have hext : List.ofFn extended = List.ofFn word ++ List.replicate rest false :=
      BitString.ofFn_ofList (by simp only [List.length_append, List.length_ofFn,
        List.length_replicate])
    have hprefWord : prefWord extended = word := by
      apply List.ofFn_injective
      rw [hp, hext, List.take_left' (by simp)]
    refine ⟨extended, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hprefWord⟩
    simp only [decide_eq_true_eq]
    apply (haccept extended).mpr
    refine ⟨?_, ?_⟩
    · rw [hprefWord]
      simpa only [decide_eq_true_eq] using (Finset.mem_filter.mp hword).2
    · rw [hext, List.drop_left' (by simp)]

/-- Each occurrence-labelled terminal accepting branch corresponds to exactly one binary word.
Repeated actions retain their multiplicity, while early halts have a unique zero continuation. -/
theorem acceptCount_table {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (input : List Bool)
    (hbound : ∀ cfg : Cfg k Bool State input, (machine.actions cfg).length ≤ 2 ^ width)
    (count : ℕ) :
    (table hw machine).acceptCount input (count * width) =
      machine.acceptCount count (Cfg.init machine.initial input) := by
  rw [acceptCount, ← machine.card_binaryCertificateAccepts
    (Cfg.init machine.initial input) hbound count (fun out => out == [true])]
  unfold MultiTapePTM.acceptCount Complexity.acceptCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro word _
  simp only [decide_eq_true_eq, MultiTapePTM.runClosedCoins_eq_output_stepCoins]
  exact stepCoins_full hw machine (Cfg.init machine.initial input) count
    (List.ofFn word) List.length_ofFn

/-- At every horizon, complete binary blocks count native terminal branches; the remaining
partial block has a unique accepting all-zero continuation after a native halt. -/
theorem acceptCount_table_div {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (input : List Bool)
    (hbound : ∀ cfg : Cfg k Bool State input, (machine.actions cfg).length ≤ 2 ^ width)
    (horizon : ℕ) :
    (table hw machine).acceptCount input horizon =
      machine.acceptCount (horizon / width) (Cfg.init machine.initial input) := by
  have hclock : horizon = horizon / width * width + horizon % width := by
    have h := Nat.mod_add_div horizon width
    rw [Nat.mul_comm width] at h
    omega
  conv_lhs => rw [hclock]
  rw [acceptCount_partial hw machine input _ _ (Nat.mod_lt _ hw),
    acceptCount_table hw machine input hbound]

/-- Once every native branch has halted, the exact count is stable at every sufficiently large
binary horizon, including horizons that are not multiples of the fixed block width. -/
theorem acceptCount_table_of_halts {width : ℕ} (hw : 0 < width)
    (machine : MultiTapeCTM k Bool State) (input : List Bool)
    (hbound : ∀ cfg : Cfg k Bool State input, (machine.actions cfg).length ≤ 2 ^ width)
    {time horizon : ℕ} (hhalt : machine.HaltsWithin time (Cfg.init machine.initial input))
    (hle : time * width ≤ horizon) :
    (table hw machine).acceptCount input horizon =
      machine.acceptCount time (Cfg.init machine.initial input) := by
  rw [acceptCount_table_div hw machine input hbound]
  exact hhalt.branchCount_eq ((Nat.le_div_iff_mul_le hw).mpr hle) _

end CountingChoice

end Turing.MultiTapeCTM
