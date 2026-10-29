/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Combinators
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import Complexity.Computability.GenericRAM.Simulation.Finite
public import Complexity.Computability.GenericRAM.SparseMemory.Turing
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi

/-!
# Native implementation of fixed-program finite RAM steps

The input contains configuration and the complete finite state, including the memory default.
All encodings are injective representations of finite data, rather than of the denoted total
memory function. Native certificates are assembled directly from arbitrary scalar time/space
bounds, fixed tuple manipulation and parameterized sparse-memory scans. No polynomiality premise
or selection of polynomial bounds is used.

For each fixed program and register count, the resulting finite native machine works on every
encoded input. Constants may depend on that fixed program; this is not an arbitrary-program
interpreter. Initialization, iteration, output decoding and charged configuration selection
remain separate obligations.

## Main definitions

* `FiniteState.encoding`: binary control label, complete register tuple, default and sparse store.
* `FiniteState.inputEncoding`, `FiniteState.resultEncoding`: explicit step interface.
* `FiniteState.stepCertificate`, `FiniteState.stepTime`, `FiniteState.stepSpace`: native
  fixed-program step implementation and its parameterized time and space bounds.
* `FiniteState.opTime`, `.opSpace`, `.instrTime`, `.instrSpace`, `.dispatchTime`, `.dispatchSpace`:
  component cost profiles decomposed across operations, instructions, and program dispatch.

## Main results

* `FiniteState.length_encoding`, `FiniteState.length_encoding_le`: encoded finite-state length
  formula and upper bound in terms of register count, register word bound, default length, and
  stored-cell count.
* `FiniteState.step_inO`: one finite native machine implements `FiniteState.step` for all runtime
  configurations and finite states within `stepTime` and `stepSpace`.
* `FiniteState.stepTime_eq`, `FiniteState.stepSpace_eq`, `FiniteState.dispatchTime_nil`,
  `FiniteState.dispatchTime_cons`, `FiniteState.dispatchSpace_nil`,
  `FiniteState.dispatchSpace_cons`: public cost recurrences.
* `FiniteState.le_opTime_const`, `FiniteState.le_opTime_alu`, `FiniteState.le_opTime_load`,
  `FiniteState.le_opTime_store`, `FiniteState.le_instrTime_op`: retention of supplied scalar and
  sparse-memory resource bounds.

## References

Reuses Christian Reitwiessner's native machine calculus and the certified scalar/sparse-memory
interfaces; finite-state semantics is defined in `Simulation.Finite`.
-/

@[expose] public section

noncomputable section

namespace Cslib.GenericRAM.FiniteState

open Turing.MultiTapeTM
open NativeCertificate

variable {M : Model.{0, 0, 0, 0}} {r : ℕ}

/-- Encode all finite state components, including the default and distinct stored bindings. -/
def encoding (enc : M.Encoding) : FiniteState M r ↪ List Bool :=
  ⟨fun s => encPair encNat (encPair (encPi enc.value)
      (encPair enc.value (SparseMemory.encoding enc.address enc.value)))
      (s.pc, s.regs, s.default, s.memory), by
    intro s t h
    have hp := (encPair encNat (encPair (encPi enc.value)
      (encPair enc.value (SparseMemory.encoding enc.address enc.value)))).injective h
    cases s
    cases t
    cases hp
    rfl⟩

@[simp] theorem encoding_apply (enc : M.Encoding) (s : FiniteState M r) :
    encoding enc s = encPair encNat (encPair (encPi enc.value)
      (encPair enc.value (SparseMemory.encoding enc.address enc.value)))
      (s.pc, s.regs, s.default, s.memory) := rfl

/-- Configuration is a runtime input, alongside the complete finite state. -/
abbrev inputEncoding (enc : M.Encoding) :
    (M.Config × FiniteState M r) ↪ List Bool :=
  encPair enc.config (encoding enc)

/-- Fault, continuing state and halted value have distinct tags. -/
abbrev resultEncoding (enc : M.Encoding) : Result M r ↪ List Bool :=
  encOption (encSum (encoding enc) enc.value)

/-- Exact bit length of an encoded finite state in terms of its four encoded fields. -/
theorem length_encoding (enc : M.Encoding) (s : FiniteState M r) :
    (encoding enc s).length =
      2 * (encNat s.pc).length + 2 * (encPi enc.value s.regs).length +
        2 * (enc.value s.default).length +
        (SparseMemory.encoding enc.address enc.value s.memory).length + 3 := by
  simp only [encoding_apply, length_encPair]
  omega

/-- Bound the encoded finite state from the control label, register bound, default, and store. -/
theorem length_encoding_le (enc : M.Encoding) (s : FiniteState M r)
    {bound : ℕ} (hregs : ∀ i, (enc.value (s.regs i)).length ≤ bound) :
    (encoding enc s).length ≤
      2 * (encNat s.pc).length + 2 * r * (2 * bound + 1) +
        2 * (enc.value s.default).length +
        (SparseMemory.entries s.memory).length *
          (4 * SparseMemory.maxKeyLength enc.address s.memory +
            2 * SparseMemory.maxValueLength enc.value s.memory + 3) + 3 := by
  have hr : (encPi enc.value s.regs).length ≤ r * (2 * bound + 1) := by
    simpa [Fintype.card_fin] using length_encPi_le enc.value s.regs hregs
  have hm := SparseMemory.length_encoding_le enc.address enc.value s.memory
  have he := length_encoding enc s
  nlinarith

namespace Native

/-- The nested tuple representation underlying the finite-state encoding. -/
abbrev tupleEncoding (enc : M.Encoding) :=
  encPair encNat (encPair (encPi (Index := Fin r) enc.value)
    (encPair enc.value (SparseMemory.encoding enc.address enc.value)))

/-- Expose the state fields with exactly the same encoded word. -/
def unpack (enc : M.Encoding) : NativeCertificate
    (fun s : FiniteState M r => (s.pc, s.regs, s.default, s.memory))
    (encoding enc) (tupleEncoding enc) :=
  linear (ComputableInO.of_eq fun _ => rfl)

/-- Construct the state from its identically encoded field tuple. -/
def pack (enc : M.Encoding) : NativeCertificate
    (fun p : ℕ × (Fin r → M.Value) × M.Value × SparseMemory M.Address M.Value =>
      (⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩ : FiniteState M r))
    (tupleEncoding enc) (encoding enc) :=
  linear (ComputableInO.of_eq fun _ => rfl)

variable {α : Type} {ei : α ↪ List Bool} {s : α → FiniteState M r}
  {k : α → M.Config} {v : α → M.Value}

/-- Expose a produced state as its nested field tuple without extra asymptotic cost. -/
def fields (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc)) :=
  post c (unpack enc).computes

@[simp] theorem fields_time (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc)) :
    (fields enc c).time = c.time := rfl

@[simp] theorem fields_space (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc)) :
    (fields enc c).space = c.space := rfl

/-- Read a fixed register, using the complete tuple input-length guarantee. -/
def register (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc)) (i : Fin r) :
    NativeCertificate (fun a => (s a).regs i) ei enc.value :=
  post (fst (snd (fields enc c))) (ComputableInO.pi_apply enc.value i)

@[simp] theorem register_time (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (i : Fin r) : (register enc c i).time = c.time := rfl

@[simp] theorem register_space (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (i : Fin r) : (register enc c i).space = c.space := rfl

/-- Gather a fixed tuple of operand registers, permitting repeated indices. -/
def operands (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {n : ℕ} (args : Fin n → Fin r) :
    NativeCertificate (fun a => (s a).regs ∘ args) ei (encPi enc.value) :=
  post (fst (snd (fields enc c))) (ComputableInO.pi_gather enc.value args)

@[simp] theorem operands_time (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {n : ℕ} (args : Fin n → Fin r) : (operands enc c args).time = c.time := rfl

@[simp] theorem operands_space (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {n : ℕ} (args : Fin n → Fin r) : (operands enc c args).space = c.space := rfl

/-- Update a fixed register and retain all other state fields. -/
def setCertificate (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    (d : Fin r) (value : NativeCertificate v ei enc.value) :
    NativeCertificate (fun a => (s a).set d (v a)) ei (encoding enc) :=
  let fs := fields enc c
  let regs := post (prod (fst (snd fs)) value) (ComputableInO.pi_update enc.value d)
  post (prod (fst fs) (prod regs (snd (snd fs)))) (pack enc).computes

@[simp] theorem setCertificate_time (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc)) (d : Fin r)
    (value : NativeCertificate v ei enc.value) (a : α) :
    (setCertificate enc c d value).time a =
      c.time a + (c.time a + value.time a + c.time a) := rfl

@[simp] theorem setCertificate_space (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc)) (d : Fin r)
    (value : NativeCertificate v ei enc.value) (a : α) :
    (setCertificate enc c d value).space a =
      c.space a + (c.space a + value.space a + c.space a) := rfl

/-- Validate a moved value before updating a fixed register. -/
def moveCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (d : Fin r) (value : NativeCertificate v ei enc.value) :
    NativeCertificate (fun a => (s a).move (k a) d (v a)) ei (encOption (encoding enc)) :=
  branch (N.validMove.comp (prod config value)) (some (setCertificate enc c d value)) (const none)

@[simp] theorem moveCertificate_time (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (d : Fin r) (value : NativeCertificate v ei enc.value) (a : α) :
    (moveCertificate enc N config c d value).time a =
      config.time a + value.time a + N.validMove.time (k a, v a) +
        if M.validMove (k a) (v a) then (setCertificate enc c d value).time a
        else (ei a).length := rfl

@[simp] theorem moveCertificate_space (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (d : Fin r) (value : NativeCertificate v ei enc.value) (a : α) :
    (moveCertificate enc N config c d value).space a =
      config.space a + value.space a + N.validMove.space (k a, v a) +
        if M.validMove (k a) (v a) then (setCertificate enc c d value).space a
        else (ei a).length := rfl

/-- Read sparse memory, with the parameterized scan bound and explicit default. -/
def readCertificate (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address) :
    NativeCertificate (fun x => SparseMemory.read (s x).default (a x) (s x).memory)
      ei enc.value :=
  let fs := fields enc c
  (⟨SparseMemory.readTime enc.address enc.value,
    SparseMemory.readSpace enc.address enc.value,
    SparseMemory.read_inO enc.address enc.value⟩ :
      NativeCertificate _ _ _).comp
      (prod (prod address (snd (snd (snd fs)))) (fst (snd (snd fs))))

@[simp] theorem readCertificate_time (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address) (x : α) :
    (readCertificate enc c address).time x =
      address.time x + c.time x + c.time x +
        SparseMemory.readTime enc.address enc.value ((a x, (s x).memory), (s x).default) := rfl

@[simp] theorem readCertificate_space (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address) (x : α) :
    (readCertificate enc c address).space x =
      address.space x + c.space x + c.space x +
        SparseMemory.readSpace enc.address enc.value ((a x, (s x).memory), (s x).default) := rfl

/-- Write sparse memory, with the parameterized scan bound and complete retained state. -/
def writeCertificate (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address)
    (value : NativeCertificate v ei enc.value) :
    NativeCertificate (fun x => (s x).write (a x) (v x)) ei (encoding enc) :=
  let fs := fields enc c
  let memory :=
    (⟨SparseMemory.writeTime enc.address enc.value,
      SparseMemory.writeSpace enc.address enc.value,
      SparseMemory.insert_inO enc.address enc.value⟩ :
      NativeCertificate _ _ _).comp
        (prod (prod address value) (snd (snd (snd fs))))
  post (prod (fst fs) (prod (fst (snd fs)) (prod (fst (snd (snd fs))) memory)))
    (pack enc).computes

@[simp] theorem writeCertificate_time (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address)
    (value : NativeCertificate v ei enc.value) (x : α) :
    (writeCertificate enc c address value).time x =
      c.time x + (c.time x + (c.time x + (address.time x + value.time x + c.time x +
        SparseMemory.writeTime enc.address enc.value ((a x, v x), (s x).memory)))) := rfl

@[simp] theorem writeCertificate_space (enc : M.Encoding)
    (c : NativeCertificate s ei (encoding enc))
    {a : α → M.Address} (address : NativeCertificate a ei enc.address)
    (value : NativeCertificate v ei enc.value) (x : α) :
    (writeCertificate enc c address value).space x =
      c.space x + (c.space x + (c.space x + (address.space x + value.space x + c.space x +
        SparseMemory.writeSpace enc.address enc.value ((a x, v x), (s x).memory)))) := rfl

/-- Implement one fixed operation from scalar, tuple and sparse-memory certificates. -/
def evalOpCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (o : Op M r) :
    NativeCertificate (fun a => evalOp (k a) o (s a)) ei (encOption (encoding enc)) := by
  cases o with
  | const d literal =>
    exact congr (option ((N.constant literal).comp config) (const none)
      (some (setCertificate enc (pull c enc.value) d (payload ei enc.value))))
      (fun a => by
        simp only [Function.comp_apply, evalOp]
        cases M.checkedConstant literal (k a) <;> rfl)
  | copy d src => exact moveCertificate enc N config c d (register enc c src)
  | alu op d args =>
    exact congr (option ((N.operation op).comp (prod config (operands enc c args))) (const none)
      (some (setCertificate enc (pull c enc.value) d (payload ei enc.value))))
      (fun a => by
        simp only [Function.comp_apply, evalOp]
        cases M.checkedOp op (k a, (s a).regs ∘ args) <;> rfl)
  | load d a =>
    exact congr (option (N.address.comp (prod config (register enc c a))) (const none)
      (moveCertificate enc N (pull config enc.address) (pull c enc.address) d
        (readCertificate enc (pull c enc.address) (payload ei enc.address))))
      (fun x => by
        simp only [Function.comp_apply, evalOp]
        cases M.address (k x) ((s x).regs a) <;> rfl)
  | store a src =>
    exact congr (option (N.address.comp (prod config (register enc c a))) (const none)
      (branch (N.validMove.comp (prod (pull config enc.address)
        (register enc (pull c enc.address) src)))
        (some (writeCertificate enc (pull c enc.address) (payload ei enc.address)
          (register enc (pull c enc.address) src))) (const none)))
      (fun x => by
        simp only [Function.comp_apply, evalOp]
        cases M.address (k x) ((s x).regs a) <;> rfl)

/-- Validate a fixed continuing label and emit the updated state. -/
def resumeCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (pc : ℕ) : NativeCertificate (fun a => resume (k a) pc (s a)) ei (resultEncoding enc) :=
  let fs := fields enc c
  let moved := post (prod (const pc) (snd fs)) (pack enc).computes
  branch (N.validPC.comp (prod config (const pc)))
    (some (inl moved enc.value)) (const none)

/-- Implement a fixed instruction, charging only the selected outcome branches. -/
def evalInstrCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc))
    (nextPC : ℕ) (i : Instr M r) :
    NativeCertificate (fun a => evalInstr (k a) nextPC i (s a)) ei (resultEncoding enc) := by
  cases i with
  | op o =>
    exact congr (option (evalOpCertificate enc N config c o) (const none)
      (resumeCertificate enc N (pull config (encoding enc)) (payload ei (encoding enc)) nextPC))
      (fun a => by
        simp only [evalInstr]
        cases evalOp (k a) o (s a) <;> rfl)
  | jump target => exact resumeCertificate enc N config c target
  | branch test target =>
    cases test with
    | test f args =>
      exact congr (option ((N.test f).comp (prod config (operands enc c args))) (const none)
        (branch (payload ei encBool)
          (resumeCertificate enc N (pull config encBool) (pull c encBool) target)
          (resumeCertificate enc N (pull config encBool) (pull c encBool) nextPC)))
        (fun a => by
          simp only [Function.comp_apply, evalInstr]
          cases h : M.evalTest (k a) f ((s a).regs ∘ args) with
          | none => rfl
          | some b => cases b <;> rfl)
  | halt i =>
    exact branch (N.validMove.comp (prod config (register enc c i)))
      (some (inr (encoding enc) (register enc c i))) (const none)

/-- Compare the current binary control label to a fixed label using native word comparison. -/
def pcEquals (enc : M.Encoding) (c : NativeCertificate s ei (encoding enc)) (pc : ℕ) :
    NativeCertificate (fun a => decide ((s a).pc = pc)) ei encBool :=
  (⟨fun p => ((encNat p.1).length + 1) *
      ((encNat p.1).length + (encNat p.2).length + 1),
    fun p => (encPair encNat encNat p).length,
    ComputableInO.eq encNat⟩ :
    NativeCertificate (fun p : ℕ × ℕ => decide (p.1 = p.2))
      (encPair encNat encNat) encBool).comp
      (prod (fst (fields enc c)) (const pc))

/-- Dispatch a fixed program by comparisons, charging each preceding rejected label. -/
def dispatchCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (config : NativeCertificate k ei enc.config) (c : NativeCertificate s ei (encoding enc)) :
    (p : Program M r) → (pc : ℕ) →
      NativeCertificate (fun a => dispatch (k a) p pc (s a)) ei (resultEncoding enc)
  | [], _ => const none
  | i :: p, pc => congr
      (branch (pcEquals enc c pc) (evalInstrCertificate enc N config c (pc + 1) i)
        (dispatchCertificate enc N config c p (pc + 1)))
      (fun _ => by simp only [dispatch, decide_eq_true_eq])

/-- Top-level runtime configuration projection from the step input. -/
def configInput (enc : M.Encoding) :
    NativeCertificate (Prod.fst : M.Config × FiniteState M r → M.Config)
      (inputEncoding enc) enc.config :=
  linear (ComputableInO.fst enc.config (encoding enc))

@[simp] theorem configInput_time (enc : M.Encoding) (q : M.Config × FiniteState M r) :
    (configInput enc).time q = (inputEncoding enc q).length := rfl

@[simp] theorem configInput_space (enc : M.Encoding) (q : M.Config × FiniteState M r) :
    (configInput enc).space q = (inputEncoding enc q).length := rfl

/-- Top-level finite-state projection from the step input. -/
def stateInput (enc : M.Encoding) :
    NativeCertificate (Prod.snd : M.Config × FiniteState M r → FiniteState M r)
      (inputEncoding enc) (encoding enc) :=
  linear (ComputableInO.snd enc.config (encoding enc))

@[simp] theorem stateInput_time (enc : M.Encoding) (q : M.Config × FiniteState M r) :
    (stateInput enc).time q = (inputEncoding enc q).length := rfl

@[simp] theorem stateInput_space (enc : M.Encoding) (q : M.Config × FiniteState M r) :
    (stateInput enc).space q = (inputEncoding enc q).length := rfl

/-- Top-level operation certificate on the step input encoding. -/
def opCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (o : Op M r) :
    NativeCertificate (fun q : M.Config × FiniteState M r => evalOp q.1 o q.2)
      (inputEncoding enc) (encOption (encoding enc)) :=
  evalOpCertificate enc N (configInput enc) (stateInput enc) o

/-- Top-level instruction certificate on the step input encoding. -/
def instrCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (nextPC : ℕ) (i : Instr M r) :
    NativeCertificate (fun q : M.Config × FiniteState M r => evalInstr q.1 nextPC i q.2)
      (inputEncoding enc) (resultEncoding enc) :=
  evalInstrCertificate enc N (configInput enc) (stateInput enc) nextPC i

/-- Top-level dispatch certificate on the step input encoding. -/
def programCertificate (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (pc : ℕ) :
    NativeCertificate (fun q : M.Config × FiniteState M r => dispatch q.1 p pc q.2)
      (inputEncoding enc) (resultEncoding enc) :=
  dispatchCertificate enc N (configInput enc) (stateInput enc) p pc

end Native

/-- A native finite machine for a fixed program, uniform in runtime configuration and state.

The certificate's bounds are constructed by sums, selected branches and substitution into the
supplied scalar and sparse-memory bounds. Linear tuple manipulation is charged by input length
or absorbed by a producer's output-length guarantee. Fixed control-label equality uses the
native encoded comparison bound. No polynomial bound is selected by this construction. -/
def stepCertificate (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    NativeCertificate (fun q : M.Config × FiniteState M r => step q.1 p q.2)
      (inputEncoding enc) (resultEncoding enc) :=
  branch (N.validPC.comp (prod (Native.configInput enc)
    (fst (Native.fields enc (Native.stateInput enc)))))
    (Native.programCertificate enc N p 0) (const none)

/-- Parameterized operation time on the step input encoding. -/
def opTime (enc : M.Encoding) (N : M.NativePrimitives enc) (o : Op M r) :
    M.Config × FiniteState M r → ℕ := (Native.opCertificate enc N o).time

/-- Parameterized operation space on the step input encoding. -/
def opSpace (enc : M.Encoding) (N : M.NativePrimitives enc) (o : Op M r) :
    M.Config × FiniteState M r → ℕ := (Native.opCertificate enc N o).space

/-- Parameterized instruction time on the step input encoding. -/
def instrTime (enc : M.Encoding) (N : M.NativePrimitives enc) (nextPC : ℕ) (i : Instr M r) :
    M.Config × FiniteState M r → ℕ := (Native.instrCertificate enc N nextPC i).time

/-- Parameterized instruction space on the step input encoding. -/
def instrSpace (enc : M.Encoding) (N : M.NativePrimitives enc) (nextPC : ℕ) (i : Instr M r) :
    M.Config × FiniteState M r → ℕ := (Native.instrCertificate enc N nextPC i).space

/-- Time charged by comparing the current control label against a fixed instruction offset. -/
def pcEqualsTime (enc : M.Encoding) (pc : ℕ) : M.Config × FiniteState M r → ℕ :=
  (Native.pcEquals enc (Native.stateInput enc) pc).time

/-- Space charged by comparing the current control label against a fixed instruction offset. -/
def pcEqualsSpace (enc : M.Encoding) (pc : ℕ) : M.Config × FiniteState M r → ℕ :=
  (Native.pcEquals enc (Native.stateInput enc) pc).space

/-- Parameterized dispatch time from instruction offset `pc`. -/
def dispatchTime (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) (pc : ℕ) :
    M.Config × FiniteState M r → ℕ := (Native.programCertificate enc N p pc).time

/-- Parameterized dispatch space from instruction offset `pc`. -/
def dispatchSpace (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) (pc : ℕ) :
    M.Config × FiniteState M r → ℕ := (Native.programCertificate enc N p pc).space

/-- Parameterized step time, obtained by explicit compositional accounting, not a chosen
polynomial. In particular it retains the time bounds supplied by `N` and sparse-memory scans. -/
def stepTime (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    M.Config × FiniteState M r → ℕ := (stepCertificate enc N p).time

/-- Parameterized step space, also bounding the encoded output up to constants. -/
def stepSpace (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    M.Config × FiniteState M r → ℕ := (stepCertificate enc N p).space

/-- The actual native implementation satisfies the explicitly assembled time and space bounds.
The existential machine and constant are outside the quantifier over all configurations/states;
they may depend on the fixed program and register count. -/
theorem step_inO (enc : M.Encoding) (N : M.NativePrimitives enc) (p : Program M r) :
    ComputableInO (fun q : M.Config × FiniteState M r => step q.1 p q.2)
      (inputEncoding enc) (resultEncoding enc) (stepTime enc N p) (stepSpace enc N p) :=
  (stepCertificate enc N p).computes

@[simp] theorem dispatchTime_nil (enc : M.Encoding) (N : M.NativePrimitives enc)
    (pc : ℕ) (q : M.Config × FiniteState M r) :
    dispatchTime enc N ([] : Program M r) pc q = (inputEncoding enc q).length := rfl

@[simp] theorem dispatchSpace_nil (enc : M.Encoding) (N : M.NativePrimitives enc)
    (pc : ℕ) (q : M.Config × FiniteState M r) :
    dispatchSpace enc N ([] : Program M r) pc q = (inputEncoding enc q).length := rfl

@[simp] theorem dispatchTime_cons (enc : M.Encoding) (N : M.NativePrimitives enc)
    (i : Instr M r) (p : Program M r) (pc : ℕ) (q : M.Config × FiniteState M r) :
    dispatchTime enc N (i :: p) pc q =
      pcEqualsTime enc pc q +
        if q.2.pc = pc then instrTime enc N (pc + 1) i q else dispatchTime enc N p (pc + 1) q := by
  simp [dispatchTime, pcEqualsTime, instrTime, Native.programCertificate,
    Native.dispatchCertificate, Native.instrCertificate]

@[simp] theorem dispatchSpace_cons (enc : M.Encoding) (N : M.NativePrimitives enc)
    (i : Instr M r) (p : Program M r) (pc : ℕ) (q : M.Config × FiniteState M r) :
    dispatchSpace enc N (i :: p) pc q =
      pcEqualsSpace enc pc q +
        if q.2.pc = pc then instrSpace enc N (pc + 1) i q
        else dispatchSpace enc N p (pc + 1) q := by
  simp [dispatchSpace, pcEqualsSpace, instrSpace, Native.programCertificate,
    Native.dispatchCertificate, Native.instrCertificate]

/-- Exact decomposition of `stepTime` into current-label validation and selected branch cost. -/
theorem stepTime_eq (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (q : M.Config × FiniteState M r) :
    stepTime enc N p q =
      2 * (inputEncoding enc q).length + N.validPC.time (q.1, q.2.pc) +
        if M.validPC q.1 q.2.pc then dispatchTime enc N p 0 q
        else (inputEncoding enc q).length := by
  change (inputEncoding enc q).length + (inputEncoding enc q).length +
      N.validPC.time (q.1, q.2.pc) +
      (if M.validPC q.1 q.2.pc then dispatchTime enc N p 0 q
        else (inputEncoding enc q).length) = _
  omega

/-- Exact decomposition of `stepSpace` into current-label validation and selected branch cost. -/
theorem stepSpace_eq (enc : M.Encoding) (N : M.NativePrimitives enc)
    (p : Program M r) (q : M.Config × FiniteState M r) :
    stepSpace enc N p q =
      2 * (inputEncoding enc q).length + N.validPC.space (q.1, q.2.pc) +
        if M.validPC q.1 q.2.pc then dispatchSpace enc N p 0 q
        else (inputEncoding enc q).length := by
  change (inputEncoding enc q).length + (inputEncoding enc q).length +
      N.validPC.space (q.1, q.2.pc) +
      (if M.validPC q.1 q.2.pc then dispatchSpace enc N p 0 q
        else (inputEncoding enc q).length) = _
  omega

/-- Step time on the empty program. -/
theorem stepTime_nil (enc : M.Encoding) (N : M.NativePrimitives enc)
    (q : M.Config × FiniteState M r) :
    stepTime enc N ([] : Program M r) q =
      3 * (inputEncoding enc q).length + N.validPC.time (q.1, q.2.pc) := by
  rw [stepTime_eq, dispatchTime_nil, ite_self]
  omega

/-- Step space on the empty program. -/
theorem stepSpace_nil (enc : M.Encoding) (N : M.NativePrimitives enc)
    (q : M.Config × FiniteState M r) :
    stepSpace enc N ([] : Program M r) q =
      3 * (inputEncoding enc q).length + N.validPC.space (q.1, q.2.pc) := by
  rw [stepSpace_eq, dispatchSpace_nil, ite_self]
  omega

/-- Step time recurrence on a non-empty program. -/
theorem stepTime_cons (enc : M.Encoding) (N : M.NativePrimitives enc)
    (i : Instr M r) (p : Program M r) (q : M.Config × FiniteState M r) :
    stepTime enc N (i :: p) q =
      2 * (inputEncoding enc q).length + N.validPC.time (q.1, q.2.pc) +
        if M.validPC q.1 q.2.pc then
          pcEqualsTime enc 0 q +
            if q.2.pc = 0 then instrTime enc N 1 i q else dispatchTime enc N p 1 q
        else (inputEncoding enc q).length := by
  rw [stepTime_eq, dispatchTime_cons]

/-- Step space recurrence on a non-empty program. -/
theorem stepSpace_cons (enc : M.Encoding) (N : M.NativePrimitives enc)
    (i : Instr M r) (p : Program M r) (q : M.Config × FiniteState M r) :
    stepSpace enc N (i :: p) q =
      2 * (inputEncoding enc q).length + N.validPC.space (q.1, q.2.pc) +
        if M.validPC q.1 q.2.pc then
          pcEqualsSpace enc 0 q +
            if q.2.pc = 0 then instrSpace enc N 1 i q else dispatchSpace enc N p 1 q
        else (inputEncoding enc q).length := by
  rw [stepSpace_eq, dispatchSpace_cons]

/-- Literal operations retain the supplied constant-certificate time bound. -/
theorem le_opTime_const (enc : M.Encoding) (N : M.NativePrimitives enc)
    (d : Fin r) (literal : M.Const) (q : M.Config × FiniteState M r) :
    (N.constant literal).time q.1 ≤ opTime enc N (.const d literal) q := by
  simp only [opTime, Native.opCertificate, Native.evalOpCertificate, congr_time, option_time,
    comp_time]
  omega

/-- Literal operations retain the supplied constant-certificate space bound. -/
theorem le_opSpace_const (enc : M.Encoding) (N : M.NativePrimitives enc)
    (d : Fin r) (literal : M.Const) (q : M.Config × FiniteState M r) :
    (N.constant literal).space q.1 ≤ opSpace enc N (.const d literal) q := by
  simp only [opSpace, Native.opCertificate, Native.evalOpCertificate, congr_space, option_space,
    comp_space]
  omega

/-- ALU operations retain the supplied operation-certificate time bound. -/
theorem le_opTime_alu (enc : M.Encoding) (N : M.NativePrimitives enc)
    (op : M.operations.Op) (d : Fin r) (args : Fin (M.operations.Arity op) → Fin r)
    (q : M.Config × FiniteState M r) :
    (N.operation op).time (q.1, q.2.regs ∘ args) ≤ opTime enc N (.alu op d args) q := by
  simp only [opTime, Native.opCertificate, Native.evalOpCertificate, congr_time, option_time,
    comp_time, prod_time]
  omega

/-- ALU operations retain the supplied operation-certificate space bound. -/
theorem le_opSpace_alu (enc : M.Encoding) (N : M.NativePrimitives enc)
    (op : M.operations.Op) (d : Fin r) (args : Fin (M.operations.Arity op) → Fin r)
    (q : M.Config × FiniteState M r) :
    (N.operation op).space (q.1, q.2.regs ∘ args) ≤ opSpace enc N (.alu op d args) q := by
  simp only [opSpace, Native.opCertificate, Native.evalOpCertificate, congr_space, option_space,
    comp_space, prod_space]
  omega

/-- Load operations retain the parameterized sparse-memory read time when the address succeeds. -/
theorem le_opTime_load (enc : M.Encoding) (N : M.NativePrimitives enc)
    (d a : Fin r) (q : M.Config × FiniteState M r) (addr : M.Address)
    (ha : M.address q.1 (q.2.regs a) = Option.some addr) :
    SparseMemory.readTime enc.address enc.value ((addr, q.2.memory), q.2.default) ≤
      opTime enc N (.load d a) q := by
  simp only [opTime, Native.opCertificate, Native.evalOpCertificate, congr_time, option_time,
    Native.moveCertificate_time, Native.readCertificate_time, Function.comp_apply, ha,
    Option.elim_some]
  omega

/-- Load operations retain the parameterized sparse-memory read space when the address succeeds. -/
theorem le_opSpace_load (enc : M.Encoding) (N : M.NativePrimitives enc)
    (d a : Fin r) (q : M.Config × FiniteState M r) (addr : M.Address)
    (ha : M.address q.1 (q.2.regs a) = Option.some addr) :
    SparseMemory.readSpace enc.address enc.value ((addr, q.2.memory), q.2.default) ≤
      opSpace enc N (.load d a) q := by
  simp only [opSpace, Native.opCertificate, Native.evalOpCertificate, congr_space, option_space,
    Native.moveCertificate_space, Native.readCertificate_space, Function.comp_apply, ha,
    Option.elim_some]
  omega

/-- Store operations retain the parameterized sparse-memory write time on valid stores. -/
theorem le_opTime_store (enc : M.Encoding) (N : M.NativePrimitives enc)
    (a src : Fin r) (q : M.Config × FiniteState M r) (addr : M.Address)
    (ha : M.address q.1 (q.2.regs a) = Option.some addr)
    (hm : M.validMove q.1 (q.2.regs src) = true) :
    SparseMemory.writeTime enc.address enc.value ((addr, q.2.regs src), q.2.memory) ≤
      opTime enc N (.store a src) q := by
  simp only [opTime, Native.opCertificate, Native.evalOpCertificate, congr_time, option_time,
    branch_time, some_time, Native.writeCertificate_time, Function.comp_apply, ha,
    Option.elim_some, hm, ite_true]
  omega

/-- Store operations retain the parameterized sparse-memory write space on valid stores. -/
theorem le_opSpace_store (enc : M.Encoding) (N : M.NativePrimitives enc)
    (a src : Fin r) (q : M.Config × FiniteState M r) (addr : M.Address)
    (ha : M.address q.1 (q.2.regs a) = Option.some addr)
    (hm : M.validMove q.1 (q.2.regs src) = true) :
    SparseMemory.writeSpace enc.address enc.value ((addr, q.2.regs src), q.2.memory) ≤
      opSpace enc N (.store a src) q := by
  simp only [opSpace, Native.opCertificate, Native.evalOpCertificate, congr_space, option_space,
    branch_space, some_space, Native.writeCertificate_space, Function.comp_apply, ha,
    Option.elim_some, hm, ite_true]
  omega

/-- Data instructions retain their operation time bound. -/
theorem le_instrTime_op (enc : M.Encoding) (N : M.NativePrimitives enc)
    (nextPC : ℕ) (o : Op M r) (q : M.Config × FiniteState M r) :
    opTime enc N o q ≤ instrTime enc N nextPC (.op o) q := by
  simp only [instrTime, opTime, Native.instrCertificate, Native.evalInstrCertificate,
    Native.opCertificate, congr_time, option_time]
  omega

/-- Data instructions retain their operation space bound. -/
theorem le_instrSpace_op (enc : M.Encoding) (N : M.NativePrimitives enc)
    (nextPC : ℕ) (o : Op M r) (q : M.Config × FiniteState M r) :
    opSpace enc N o q ≤ instrSpace enc N nextPC (.op o) q := by
  simp only [instrSpace, opSpace, Native.instrCertificate, Native.evalInstrCertificate,
    Native.opCertificate, congr_space, option_space]
  omega

end Cslib.GenericRAM.FiniteState
