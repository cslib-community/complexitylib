/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic

/-!
# Exact reachability of the compact configuration graph

The invariant is an actual finite view whose radix registers equal the current ID. Arithmetic
steps preserve this invariant, so malformed IDs cannot create spurious accepting paths.
The forward implication only requires that source-reachable views fit the selected radix.

The overflow test (`Turing.MultiTapeNTM.ConfigurationGraph.overflow`) detects the represented
views with a step leaving the radix. When no reachable vertex overflows, every source-reachable
view fits the radix, so the graph is exact without any space bound on the source.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad`: exact native acceptance.
* `Turing.MultiTapeNTM.ConfigurationGraph.overflow_vertexID`: overflow means a step leaving the
  radix.
* `Turing.MultiTapeNTM.ConfigurationGraph.fits_of_not_overflow`: a graph without reachable
  overflow represents every reachable view.
* `Turing.MultiTapeNTM.ConfigurationGraph.not_overflow_of_fits`: conversely.
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM.ConfigurationGraph

variable {k B : ℕ} {State : Type} [Fintype State]
  {ntm : MultiTapeNTM k Bool State} {w : List Bool}

theorem radix_pos (D n : ℕ) : 0 < radix D n := pow_pos (by omega) _

/-- A radix that fits some registers is positive. -/
theorem pos_of_fits {r : Register k → ℕ} (hf : Fits B r) : 0 < B :=
  (Nat.zero_le _).trans_lt (hf .inputPos)

theorem stateCode_injective : Function.Injective (stateCode (State := State)) := by
  intro a b h
  exact (Fintype.equivFin (Option State)).injective (Fin.ext h)

theorem outputCode_lt (w : List Bool) : outputCode w < 3 := by
  unfold outputCode
  split_ifs <;> decide

theorem outputCode_summary (w : List Bool) : outputCode (outputClass w) = outputCode w := by
  unfold outputClass outputCode
  split_ifs <;> simp_all

theorem outputCode_append (w : List Bool) (b : Option Bool) :
    outputCode (outputClass (w ++ b.toList)) = outputStep (outputCode w) b := by
  rw [outputCode_summary]
  rcases b with _ | b
  · simp [outputStep]
  · by_cases h : w = []
    · subst w
      cases b <;> rfl
    · have hnot : w ++ [b] ≠ [true] := by
        intro heq
        have := congrArg List.length heq
        have : w.length = 0 := by simpa using this
        exact h (List.length_eq_zero_iff.mp this)
      have hc : outputCode w ≠ 0 := by
        unfold outputCode
        split_ifs <;> omega
      rw [outputStep, ite_eq_right hc]
      simp [outputCode, h, hnot]

theorem outputCode_eq_one_iff {w : List Bool} : outputCode w = 1 ↔ w = [true] := by
  unfold outputCode
  split_ifs <;> simp_all

omit [Fintype State] in
/-- The arithmetic input move agrees with native clamping. -/
theorem inputMove_eq (v : FiniteCfg k Bool State) (d : SignType) :
    inputMove v.input.length v.inputPos.val d = (moveInputPos v.inputPos d).val := by
  have h := val_moveInputPos_eq v.inputPos d
  have hb := v.inputPos.isLt
  cases d <;> simp only [inputMove, SignType.cast] at * <;> omega

/-- The arithmetic tuple update agrees with the summarized finite view step. -/
theorem registers_step (v : FiniteCfg k Bool State) (a : Action k Bool State) :
    registers (v.step a).summarizeOutput = nextRegisters v.input.length (registers v) a := by
  funext i
  cases i with
  | inputPos => exact (inputMove_eq v a.inputTape).symm
  | control => rfl
  | output => exact outputCode_append v.output a.output
  | head i => exact congrArg Prod.fst (tapeCode_step (v.workTapes i) (a.workTapes i))
  | left i => exact congrArg (fun t => t.2.1) (tapeCode_step (v.workTapes i) (a.workTapes i))
  | right i => exact congrArg (fun t => t.2.2) (tapeCode_step (v.workTapes i) (a.workTapes i))

theorem readRegisters_vertexID {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    readRegisters B (vertexID B v) = registers v := by
  funext i
  exact Cslib.Radix.component_pack (pos_of_fits hf) hf i

theorem vertexID_lt {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    vertexID B v < vertexBound (k := k) B := Cslib.Radix.pack_lt (pos_of_fits hf) hf

theorem valid_vertexID {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    valid (k := k) (State := State) B v.input.length (vertexID B v) = true := by
  have hread := readRegisters_vertexID hf
  have hc : stateCode v.state < Fintype.card (Option State) :=
    (Fintype.equivFin (Option State) v.state).isLt
  simp only [valid, hread, registers, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨vertexID_lt hf, v.inputPos.isLt⟩, hc⟩, outputCode_lt _⟩, ?_⟩
  simp [symbolCode_lt]

theorem fitsB_eq_true {B : ℕ} {r : Register k → ℕ} : fitsB B r = true ↔ Fits B r := by
  simp [fitsB, Fits, List.all_eq_true]

/-- The sole queried symbol agrees with the native input head, including both blank boundaries. -/
theorem inputSymbol_query {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    inputSymbol v.input.length v.inputPos.val
      v.input[queryIndex (k := k) B (vertexID B v)]? = v.inputSymbol := by
  have hread := readRegisters_vertexID hf
  rw [queryIndex, hread]
  rw [FiniteCfg.inputSymbol_eq_getD]
  by_cases hz : v.inputPos.val = 0
  · simp [inputSymbol, hz]
  · by_cases he : v.inputPos.val = v.input.length + 1
    · simp [inputSymbol, he]
    · have hp : v.inputPos.val = (v.inputPos.val - 1) + 1 := by omega
      simp only [registers, inputSymbol, hz, he, or_self, ↓reduceIte]
      conv_rhs => rw [hp]
      simp only [List.getElem?_cons_succ, List.getElem?_map]
      cases v.input[v.inputPos.val - 1]? <;> rfl

theorem matchesEntry_iff (v : FiniteCfg k Bool State) (symbol : Option Bool)
    (t : Instruction k State) :
    matchesEntry v.input.length (registers v) symbol t = true ↔
      v.state = some t.1 ∧ inputSymbol v.input.length v.inputPos.val symbol = t.2.1 ∧
        v.workTapeSymbols = t.2.2.1 := by
  simp only [matchesEntry, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_ofFn, id_eq]
  constructor
  · rintro ⟨⟨hc, hi⟩, hh⟩
    exact ⟨stateCode_injective hc, hi, funext fun i =>
      symbolCode_injective (of_decide_eq_true (hh _ ⟨i, rfl⟩))⟩
  · rintro ⟨hc, hi, hh⟩
    refine ⟨⟨congrArg stateCode hc, hi⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact decide_eq_true (congrArg symbolCode (congrFun hh i))

/-- Validity rejects every ID outside the ambient vertex range. -/
theorem lt_vertexBound_of_valid {B n u : ℕ}
    (h : valid (k := k) (State := State) B n u = true) :
    u < vertexBound (k := k) B := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

/-- Every successful local edge query stays inside the finite ambient graph. -/
theorem lt_vertexBound_of_edgeWithSymbol {B n u v : ℕ} {symbol : Option Bool}
    (h : edgeWithSymbol ntm B n u v symbol = true) :
    u < vertexBound (k := k) B ∧ v < vertexBound (k := k) B := by
  simp only [edgeWithSymbol, Bool.and_eq_true] at h
  exact ⟨lt_vertexBound_of_valid h.1.1, lt_vertexBound_of_valid h.1.2⟩

/-- An edge out of a represented vertex has an actual native view successor. -/
theorem edge_sound {v : FiniteCfg k Bool State} {u : ℕ}
    (hf : Fits B (registers v))
    (he : Edge ntm B v.input (vertexID B v) u) :
    ∃ v', ntm.ViewStep v v' ∧ v'.input = v.input ∧ u = vertexID B v' ∧
      Fits B (registers v') := by
  have hr := readRegisters_vertexID hf
  simp only [Edge, edgeWithSymbol, hr, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true] at he
  rcases he.2 with hh | ⟨t, ht, ⟨⟨hm, hfit⟩, hu⟩⟩
  · have hs : v.state = none := stateCode_injective hh.1
    refine ⟨v, ?_, rfl, hh.2, hf⟩
    simp [ViewStep, hs]
  · obtain ⟨hs, hi, hw⟩ := (matchesEntry_iff _ _ _).mp hm
    rw [inputSymbol_query hf] at hi
    have htr := (mem_instructions ntm t).mp ht
    have hnext : ntm.ViewStep v (v.step t.2.2.2).summarizeOutput := by
      simp only [ViewStep, hs]
      exact ⟨t.2.2.2, by rwa [hi, hw], rfl⟩
    have hf' : Fits B (registers (v.step t.2.2.2).summarizeOutput) := by
      rw [registers_step]
      exact fitsB_eq_true.mp hfit
    refine ⟨_, hnext, rfl, ?_, hf'⟩
    change u = Cslib.Radix.pack B (registers (v.step t.2.2.2).summarizeOutput)
    rwa [registers_step]

/-- Every fitting native view edge is an edge of the compact graph. -/
theorem edge_complete {v v' : FiniteCfg k Bool State}
    (hf : Fits B (registers v))
    (hf' : Fits B (registers v')) (he : ntm.ViewStep v v') :
    Edge ntm B v.input (vertexID B v) (vertexID B v') := by
  have hr := readRegisters_vertexID hf
  cases hs : v.state with
  | none =>
    have hv : v' = v := by simpa [ViewStep, hs] using he
    subst v'
    simp [Edge, edgeWithSymbol, hr, valid_vertexID hf, registers, hs]
  | some q =>
    obtain ⟨a, ha, rfl⟩ : ∃ a, ntm.Tr q v.inputSymbol v.workTapeSymbols a ∧
        v' = (v.step a).summarizeOutput := by simpa [ViewStep, hs] using he
    let t : Instruction k State := (q, v.inputSymbol, v.workTapeSymbols, a)
    have ht : t ∈ instructions ntm := (mem_instructions ntm t).mpr ha
    have hm : matchesEntry v.input.length (registers v)
        v.input[queryIndex (k := k) B (vertexID B v)]? t = true :=
      (matchesEntry_iff _ _ _).mpr ⟨hs, inputSymbol_query hf, rfl⟩
    have hfits : fitsB B (nextRegisters v.input.length (registers v) a) =
        true := fitsB_eq_true.mpr (by rwa [← registers_step])
    simp only [Edge, edgeWithSymbol, hr, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, List.any_eq_true]
    refine ⟨⟨valid_vertexID hf, valid_vertexID hf'⟩, .inr ⟨t, ht, ⟨⟨hm, hfits⟩, ?_⟩⟩⟩
    exact congrArg (Cslib.Radix.pack B) (registers_step v a)

/-- Initial storage has an input-length-only ID. -/
theorem vertexID_init (ntm : MultiTapeNTM k Bool State) (B : ℕ) (w : List Bool) :
    vertexID B (ntm.initView w) = startID ntm B := by
  unfold vertexID startID
  apply congrArg (Cslib.Radix.pack B)
  funext i
  cases i <;> rfl

omit [Fintype State] in
/-- Views reachable on one input retain precisely that input. -/
theorem input_of_reachable {v : FiniteCfg k Bool State}
    (h : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) : v.input = w := by
  obtain ⟨p, hp⟩ := exists_computationPath_of_viewStep h
  exact hp.input

/-- Exact graph reachability, provided all source-reachable views fit the radix. -/
theorem reachable_iff (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) (u : ℕ) :
    Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ↔
      ∃ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v ∧ u = vertexID B v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨_, .refl, (vertexID_init _ _ _).symm⟩
    | @tail a b h he ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      have hi := input_of_reachable hv
      rw [← hi] at he
      obtain ⟨v', hstep, _, hid, _⟩ := edge_sound (hfit v hv) he
      exact ⟨v', hv.tail hstep, hid⟩
  · rintro ⟨v, hv, rfl⟩
    induction hv with
    | refl => rw [vertexID_init]
    | @tail a b h he ih =>
      have hi := input_of_reachable h
      have hedge := edge_complete (hfit a h) (hfit b (h.tail he)) he
      rw [hi] at hedge
      exact ih.tail hedge

/-- `bad` has exactly the native accepting-halt meaning on represented vertices. -/
theorem bad_vertexID {v : FiniteCfg k Bool State}
    (hf : Fits B (registers v)) :
    bad (k := k) (State := State) B v.input.length (vertexID B v) = true ↔
      v.state = none ∧ v.output = [true] := by
  simp only [bad, readRegisters_vertexID hf, valid_vertexID hf, Bool.true_and,
    Bool.and_eq_true, decide_eq_true_eq, registers, outputCode_eq_one_iff]
  constructor
  · rintro ⟨hs, ho⟩
    exact ⟨stateCode_injective hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨congrArg stateCode hs, ho⟩

/-- Native acceptance is exactly reachability of a bad vertex. No totality or time bound on the
source machine is used; the only assumption is that its reachable registers fit the radix. -/
theorem accepts_iff_reachable_bad
    (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) :
    ntm.Accepts w ↔ ∃ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u ∧
      bad (k := k) (State := State) B w.length u = true := by
  rw [accepts_iff_reflTransGen_viewStep]
  constructor
  · rintro ⟨v, hv, hs, ho⟩
    refine ⟨vertexID B v, (reachable_iff hfit _).mpr ⟨v, hv, rfl⟩, ?_⟩
    have hi := input_of_reachable hv
    rw [← hi]
    exact (bad_vertexID (hfit v hv)).mpr ⟨hs, ho⟩
  · rintro ⟨u, hu, hb⟩
    obtain ⟨v, hv, rfl⟩ := (reachable_iff hfit u).mp hu
    have hi := input_of_reachable hv
    rw [← hi] at hb
    exact ⟨v, hv, (bad_vertexID (hfit v hv)).mp hb⟩

/-- **Overflow means a step leaving the radix**: a represented view overflows exactly when one of
its source steps reaches a view that does not fit. -/
theorem overflow_vertexID {v : FiniteCfg k Bool State} (hf : Fits B (registers v)) :
    Overflow ntm B v.input (vertexID B v) ↔
      ∃ v', ntm.ViewStep v v' ∧ ¬ Fits B (registers v') := by
  have hr := readRegisters_vertexID hf
  simp only [Overflow, overflow, hr, valid_vertexID hf, Bool.true_and, List.any_eq_true,
    Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨t, ht, hm, hfit⟩
    obtain ⟨hs, hi, hw⟩ := (matchesEntry_iff _ _ _).mp hm
    rw [inputSymbol_query hf] at hi
    have htr := (mem_instructions ntm t).mp ht
    refine ⟨(v.step t.2.2.2).summarizeOutput, ?_, ?_⟩
    · simp only [ViewStep, hs]
      exact ⟨t.2.2.2, by rwa [hi, hw], rfl⟩
    · rw [registers_step, ← fitsB_eq_true, hfit]
      exact Bool.false_ne_true
  · rintro ⟨v', he, hn⟩
    cases hs : v.state with
    | none =>
      have hv : v' = v := by simpa [ViewStep, hs] using he
      exact absurd (hv ▸ hf) hn
    | some q =>
      obtain ⟨a, ha, rfl⟩ : ∃ a, ntm.Tr q v.inputSymbol v.workTapeSymbols a ∧
          v' = (v.step a).summarizeOutput := by simpa [ViewStep, hs] using he
      let t : Instruction k State := (q, v.inputSymbol, v.workTapeSymbols, a)
      refine ⟨t, (mem_instructions ntm t).mpr ha,
        (matchesEntry_iff _ _ _).mpr ⟨hs, inputSymbol_query hf, rfl⟩, ?_⟩
      rw [registers_step] at hn
      exact Bool.eq_false_iff.mpr fun h => hn (fitsB_eq_true.mp h)

/-- **A graph without reachable overflow is exact**: if the start view fits and no vertex
reachable in the graph overflows, then every source-reachable view fits the radix. -/
theorem fits_of_not_overflow (hstart : Fits B (registers (ntm.initView w)))
    (hno : ∀ u, Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u → ¬ Overflow ntm B w u)
    (v : FiniteCfg k Bool State) (hv : Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v) :
    Fits B (registers v) := by
  suffices h : Fits B (registers v) ∧
      Relation.ReflTransGen (Edge ntm B w) (startID ntm B) (vertexID B v) from h.1
  induction hv with
  | refl => exact ⟨hstart, by rw [vertexID_init]⟩
  | @tail a b h he ih =>
    obtain ⟨hfa, hra⟩ := ih
    have hi := input_of_reachable h
    have hfb : Fits B (registers b) := by
      by_contra hn
      exact hno _ hra (hi ▸ (overflow_vertexID hfa).mpr ⟨b, he, hn⟩)
    have hedge := edge_complete hfa hfb he
    rw [hi] at hedge
    exact ⟨hfb, hra.tail hedge⟩

/-- Conversely, when every source-reachable view fits the radix, no reachable vertex overflows. -/
theorem not_overflow_of_fits (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits B (registers v)) (u : ℕ)
    (hu : Relation.ReflTransGen (Edge ntm B w) (startID ntm B) u) : ¬ Overflow ntm B w u := by
  obtain ⟨v, hv, rfl⟩ := (reachable_iff hfit u).mp hu
  have hi := input_of_reachable hv
  rw [← hi, overflow_vertexID (hfit v hv)]
  rintro ⟨v', he, hn⟩
  exact hn (hfit v' (hv.tail he))

end Turing.MultiTapeNTM.ConfigurationGraph
