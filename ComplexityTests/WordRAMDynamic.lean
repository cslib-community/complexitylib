/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Computability.WordRAM.Subroutine
public import Complexity.DataStructure.WordRAM.StateTransition
public import Complexity.DataStructure.Stack.WordRAM.Basic

/-! Nonvacuous fixed-program clients: a persistent exchange cell and a read-only array.
Both obtain arbitrary-history theorems from the same certificate interface. -/

@[expose] public section

open Cslib Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.WordRAM

namespace WordRAMDynamicTests

/-- Exchange returns the previous contents of the single maintained cell. -/
abbrev exchangeSpec (w : ℕ) : DataStructure.StateTransitionSpec :=
  DataStructure.StateTransitionSpec.ofFn (State := ℕ) (Op := ℕ) (Result := fun _ => ℕ)
    (fun s o => (o, s)) (fun _ o => Fits w o)

/-- One fixed program loads the old cell before overwriting it with the argument. -/
def exchangeProgram (w : ℕ) : DynamicProgram (exchangeSpec w) 3 where
  code := .seq (.op (.const 0 0)) (.seq (.op (.load 2 0)) (.op (.store 0 1)))
  output := 2
  input i := i == 1
  encode o _ := o
  decode _ regs := some (regs 2)

/-- The exchange cell has a genuine execution proof at every bounded word size. -/
def exchangeCertificate (w : ℕ) : DynamicCertificate (exchangeProgram w) w :=
  DynamicCertificate.ofFn (fun s x => x.Bounded w ∧ x.mem 0 = s)
    (fun h => h.1)
    (fun _ h _ _ => h)
    (fun {s x} o hr hv => by
      let x₀ := (exchangeProgram w).prepare o x
      let x₁ := x₀.set 0 0
      let x₂ := x₁.set 2 (x₁.mem (x₁.regs 0))
      let y := x₂.write (x₂.regs 0) (x₂.regs 1)
      have he : Exec w (exchangeProgram w).code x₀ y 3 :=
        (Exec.const (fits_zero w)).seq (Exec.load.seq Exec.store)
      have hy : y.mem 0 = o := by simp [y, x₂, x₁, x₀, DynamicProgram.prepare, exchangeProgram,
        Data.set, Data.write]
      have hout : y.regs 2 = s := by
        simp [y, x₂, x₁, x₀, Data.set, Data.write, DynamicProgram.prepare, hr.2]
      refine ⟨y, 3, he, ?_, ⟨?_, hy⟩⟩
      · exact congrArg some hout
      · exact he.bounded ((exchangeProgram w).prepare_bounded hr.1 (fun _ _ => hv)))

/-- A concrete initial representation exists even at word size zero. -/
theorem exchange_initial (w : ℕ) :
    (exchangeCertificate w).rep 0 (⟨fun _ => 0, fun _ => 0⟩ : Data 3) :=
  ⟨⟨fun _ => fits_zero w, fun _ => fits_zero w⟩, rfl⟩

/-- The exchange cell supports arbitrary admissible adaptive clients. -/
example (w : ℕ) {α : Type} (p : (exchangeSpec w).Client α)
    (hv : (exchangeSpec w).ValidHistory 0 ((exchangeSpec w).runClient 0 p).2.2) :
    ∃ y ts, DataStructure.Executes ((exchangeProgram w).ExecOp w) p
        ⟨fun _ => 0, fun _ => 0⟩ ((exchangeSpec w).runClient 0 p).1 y ts ∧
      (exchangeCertificate w).rep ((exchangeSpec w).runClient 0 p).2.1 y :=
  (exchangeCertificate w).impl.exists_executes p (exchange_initial w) hv

/-- Read-only array queries preserve the abstract array and return the selected entry. -/
abbrev lookupSpec (n : ℕ) : DataStructure.StateTransitionSpec :=
  DataStructure.StateTransitionSpec.ofFn (State := Fin n → ℕ) (Op := Fin n) (Result := fun _ => ℕ)
    fun s i => (s, s i)

/-- Array lookup uses one load and the final halt. -/
def lookupProgram (n : ℕ) : DynamicProgram (lookupSpec n) 2 where
  code := .op (.load 1 0)
  output := 1
  input i := i == 0
  encode i _ := i
  decode _ regs := some (regs 1)

/-- Every represented bounded array has a uniform two-instruction query implementation. -/
def lookupCertificate (w n : ℕ) (hn : Fits w n) :
    DynamicCertificate (lookupProgram n) w :=
  DynamicCertificate.ofFn (fun s x => x.Bounded w ∧ ∀ i : Fin n, x.mem i = s i)
    (fun h => h.1)
    (fun i _ _ _ => lt_trans i.isLt hn)
    (fun {_ x} i hr _ => by
      let x₀ := (lookupProgram n).prepare i x
      let y := x₀.set 1 (x₀.mem (x₀.regs 0))
      have he : Exec w (lookupProgram n).code x₀ y 1 := Exec.load
      refine ⟨y, 1, he, ?_, ⟨?_, ?_⟩⟩
      · simp [lookupProgram, y, x₀, Data.set, DynamicProgram.prepare, hr.2]
      · exact he.bounded ((lookupProgram n).prepare_bounded hr.1
          (fun _ _ => lt_trans i.isLt hn))
      · exact hr.2)

/-- A represented read-only array exists for every width and admissible array size. -/
example (w n : ℕ) (hn : Fits w n) :
    (lookupCertificate w n hn).rep (fun _ => 0) ⟨fun _ => 0, fun _ => 0⟩ :=
  ⟨⟨fun _ => fits_zero w, fun _ => fits_zero w⟩, fun _ => rfl⟩

/-- Framing protects a second cell during a concrete store to the first. -/
example (w : ℕ) (x : Data 2) (h0 : x.regs 0 = 0) (h1 : x.mem 1 = 7) :
    (HeapAssertion.pointsto 1 7).holds (x.write 0 (x.regs 1)).mem := by
  have he : TraceExec (B := .standard) w (.op (.store 0 1)) x (x.write 0 (x.regs 1)) 1
      [.write 0 (x.regs 1)] := by
    simpa [Op.probes, h0] using
      (TraceExec.op (o := .store 0 1) (w := w) (x := x) rfl)
  exact he.frame h1 (by simp [HeapAssertion.pointsto, Probe.writes])

/-- An adaptive client chooses whether to pop from the observed size. -/
def stackClient : (Stack.WordRAM.spec 4 2).Client (Option ℕ × ℕ) :=
  .liftBind (.push 7) fun _ =>
    .liftBind .size fun (n : ℕ) =>
      if n = 1 then
        .liftBind .pop fun v => .liftBind .size fun (m : ℕ) => .pure (v, m)
      else .pure (none, n)

/-- The test client is admissible from the concrete empty representation. -/
example : (Stack.WordRAM.spec 4 2).ValidHistory []
    ((Stack.WordRAM.spec 4 2).runClient [] stackClient).2.2 :=
  by
    change (0 < 2 ∧ Fits 4 7) ∧ True ∧ True ∧ True ∧ True
    decide

/-- The concrete stack realizes an adaptive observation with a cumulative native cost bound. -/
example : ∃ y ts,
    DataStructure.Executes ((Stack.WordRAM.implementation 4 2).ExecOp 4) stackClient
        (Stack.WordRAM.initial 3) (some 7, 0) y ts ∧ Stack.WordRAM.Rep 4 3 2 [] y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions ts ≤ 48 := by
  exact Stack.WordRAM.run_client (base := 3) (by decide : Fits 4 2) (by decide : Fits 4 (3 + 2))
      stackClient (Stack.WordRAM.initial_rep (by decide : Fits 4 (3 + 2))) (by
        change (0 < 2 ∧ Fits 4 7) ∧ True ∧ True ∧ True ∧ True
        decide)

/-- Typed push, empty pop, and size queries on `Stack.WordRAM.implementation 4 2`, plus decoder
rejection and loop-fuel exhaustion on `exchangeProgram 4`. -/
example :
    ((Stack.WordRAM.implementation 4 2).eval 4 0 (.push 7) (Stack.WordRAM.initial 3)).map
      (fun (y, answer, cost) => (y.mem 3, y.regs Stack.WordRAM.len, answer, cost)) =
        some (7, 1, (), 8) ∧
    ((Stack.WordRAM.implementation 4 2).eval 4 0 .pop (Stack.WordRAM.initial 3)).map
      (fun (_, answer, _) => answer) = some none ∧
    ((Stack.WordRAM.implementation 4 2).eval 4 0 .size (Stack.WordRAM.initial 3)).map
      (fun (_, answer, _) => answer) = some 0 ∧
    ({ exchangeProgram 4 with decode := fun _ _ => none } :
      DynamicProgram (exchangeSpec 4) 3 .standard).eval 4 0 7
      ⟨fun _ => 0, fun _ => 0⟩ = none ∧
    ({ exchangeProgram 4 with code := .loop (.eq 0 0) (.op (.copy 0 0)) } :
      DynamicProgram (exchangeSpec 4) 3 .standard).eval 4 2 7
      ⟨fun _ => 0, fun _ => 0⟩ = none := by
  decide

/-- Successful evaluation of a represented, admissible call supplies native execution evidence. -/
example {y : Data 9} {cost : ℕ}
    (he : (Stack.WordRAM.implementation 4 2).eval 4 0 (.push 7) (Stack.WordRAM.initial 3) =
      some (y, (), cost)) :
    ∃ probes, (Stack.WordRAM.implementation 4 2).ExecOp 4 (Stack.WordRAM.initial 3) (.push 7) () y
      ⟨cost, probes⟩ :=
  (Stack.WordRAM.certificate (w := 4) (capacity := 2) (base := 3) (by decide)
    (by decide)).execOp_of_eval
    (Stack.WordRAM.initial_rep (by decide)) (by decide) he

/-- A full stack rejects another push, while the largest fitting word remains a valid value. -/
example : ¬(Stack.WordRAM.spec 4 2).valid [4, 7] (.push 2) ∧
    (Stack.WordRAM.spec 4 2).valid [] (.push 15) := by decide

/--
info: 'Cslib.WordRAM.DynamicCertificate.impl' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicCertificate.impl
/--
info: 'Cslib.WordRAM.TraceExec.exec' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms TraceExec.exec

/-! ## Nondeterministic two-slot allocator `StateTransitionImpl` tests -/

/-- Relational specification of a two-slot allocator: from state `(b₀, b₁) : Bool × Bool`, an
allocation operation `()` nondeterministically returns any free slot `i : Fin 2` and marks slot
`i` occupied. When both slots are free (`(false, false)`), both `0` and `1` are permitted. -/
abbrev TwoSlotAlloc : DataStructure.StateTransitionSpec where
  State := Bool × Bool
  Op := Unit
  Result _ := Fin 2
  valid s _ := s.1 = false ∨ s.2 = false
  step s _ s' i :=
    (i = 0 ∧ s.1 = false ∧ s' = (true, s.2)) ∨
    (i = 1 ∧ s.2 = false ∧ s' = (s.1, true))

instance : TwoSlotAlloc.Total where
  step_total s _ hv := by
    rcases hv with h0 | h1
    · exact ⟨(true, s.2), 0, Or.inl ⟨rfl, h0, rfl⟩⟩
    · exact ⟨(s.1, true), 1, Or.inr ⟨rfl, h1, rfl⟩⟩

/-- Six-register `.exact` Word-RAM subroutine implementing `TwoSlotAlloc` by sequential
allocation of slot `0` followed by slot `1`. -/
abbrev twoSlotCode : SubroutineCode .exact 6 0 where
  allocSpan := .op (.copy 0 1)
  initSetup := .op (.const 5 0)
  code := .seq (.op (.copy 4 5)) (.seq (.op (.const 3 1)) (.op (.exactBin .add 5 5 3)))
  frontierReg := 1
  baseReg := 0
  initParams := Fin.elim0
  curReg := 2
  zeroReg := 3
  oneReg := 4
  incCur := .exactBin .add 2 2 4
  input i := i == 2 || i == 3 || i == 4
  output := 4

/-- Representation invariant for `twoSlotCode` at word width `w` and base address `base`. -/
abbrev twoSlotRep (w base : ℕ) (s : Bool × Bool) (x : Data 6) : Prop :=
  x.Bounded w ∧ x.regs 0 = base ∧
    ((s = (false, false) ∧ x.regs 5 = 0) ∨
     (s = (true, false) ∧ x.regs 5 = 1) ∨
     (s = (true, true) ∧ x.regs 5 = 2))

/-- `StateTransitionImpl` certificate showing that `twoSlotCode` realizes the nondeterministic
`TwoSlotAlloc` specification whenever `Fits w 2`. -/
abbrev twoSlotSubroutine (w base : ℕ) (h2 : Fits w 2) :
    StateTransitionImpl twoSlotCode TwoSlotAlloc w base Fin.elim0 (false, false) where
  space := 0
  spanTime := 1
  setupTime := 1
  initPotential := 0
  charge _ _ := 3
  rep := twoSlotRep w base
  potential _ := 0
  encode _ _ := 0
  argMatch _ _ := True
  decode _ regs := some ⟨regs 4 % 2, Nat.mod_lt _ (by decide)⟩
  bounded hr := hr.1
  arguments_fit _ _ _ _ := fits_zero w
  encode_matches _ _ := trivial
  rep_supported {s x x'} hregs _ hx' hr := by
    refine ⟨hx', ?_, ?_⟩
    · rw [hregs 0 rfl]; exact hr.2.1
    · rw [hregs 5 rfl]; exact hr.2.2
  potential_supported _ _ _ := rfl
  clear_nodup := by decide
  params_not_clear j := j.elim0
  incCur_eval {x} hone hfit := by
    simp only [Op.eval_exactBin, BinOp.evalExact, hone, Option.bind_some, Data.put_of_fits hfit]
  span_exec {x} _ hfr _ := by
    refine ⟨x.set 0 (x.regs 1), ⟨1, Nat.le_refl 1, Exec.copy⟩, rfl, ?_, ?_, fun j => j.elim0⟩
    · simp [Data.set, hfr]
    · simp [Data.set, hfr]
  setup_exec {x₁} hx₁ hb₁ hfr₁ _ _ := by
    refine ⟨x₁.set 5 0, ⟨1, Nat.le_refl 1, Exec.const (fits_zero w)⟩, ?_, ?_, Nat.le_refl 0,
      fun _ _ => rfl⟩
    · simp [Data.set, hfr₁]
    · refine ⟨hx₁.set (fits_zero w), ?_, Or.inl ⟨rfl, by simp [Data.set]⟩⟩
      simp [Data.set, hb₁]
  step_exec {s x} _ hr hv _ := by
    have h1 : Fits w 1 := h2.of_le (by decide)
    rcases hr with ⟨hx, hb, ⟨rfl, h5⟩ | ⟨rfl, h5⟩ | ⟨rfl, _⟩⟩
    · let x₁ := x.set 4 (x.regs 5)
      let x₂ := x₁.set 3 1
      let y := x₂.set 5 (x₂.regs 5 + x₂.regs 3)
      have hfit : Fits w (x₂.regs 5 + x₂.regs 3) := by
        simpa [x₂, x₁, Data.set, h5] using h1
      have heval : (Op.exactBin .add (5 : Fin 6) 5 3).eval w x₂ = some y := by
        simp only [Op.eval_exactBin, BinOp.evalExact, Option.bind_some, Data.put_of_fits hfit, y]
      have hex : Exec w twoSlotCode.code x y 3 :=
        Exec.copy.seq ((Exec.const h1).seq (Exec.op heval))
      have hy_b : y.Bounded w := hex.bounded hx
      refine ⟨y, (true, false), 0, 3, hex, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_,
        fun _ _ => rfl, Nat.le_refl 3⟩
      · simp [y, x₂, x₁, Data.set, h5]
      · refine ⟨hy_b, ?_, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
        · simp [y, x₂, x₁, Data.set, hb]
        · simp [y, x₂, x₁, Data.set, h5]
    · let x₁ := x.set 4 (x.regs 5)
      let x₂ := x₁.set 3 1
      let y := x₂.set 5 (x₂.regs 5 + x₂.regs 3)
      have hfit : Fits w (x₂.regs 5 + x₂.regs 3) := by
        simpa [x₂, x₁, Data.set, h5] using h2
      have heval : (Op.exactBin .add (5 : Fin 6) 5 3).eval w x₂ = some y := by
        simp only [Op.eval_exactBin, BinOp.evalExact, Option.bind_some, Data.put_of_fits hfit, y]
      have hex : Exec w twoSlotCode.code x y 3 :=
        Exec.copy.seq ((Exec.const h1).seq (Exec.op heval))
      have hy_b : y.Bounded w := hex.bounded hx
      refine ⟨y, (true, true), 1, 3, hex, Or.inr ⟨rfl, rfl, rfl⟩, ?_, ?_,
        fun _ _ => rfl, Nat.le_refl 3⟩
      · simp [y, x₂, x₁, Data.set, h5]
      · refine ⟨hy_b, ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
        · simp [y, x₂, x₁, Data.set, hb]
        · simp [y, x₂, x₁, Data.set, h5]
    · cases hv with
      | inl h => cases h
      | inr h => cases h

/-- Adaptive client allocating two slots sequentially and returning both indices. -/
abbrev allocPair : TwoSlotAlloc.Client (Fin 2 × Fin 2) :=
  .liftBind () fun i =>
    .liftBind () fun j =>
      .pure (i, j)

/-- `allocPair` is demonically admissible from `(false, false)` across all permitted outcomes. -/
theorem allocPair_demonicValid :
    TwoSlotAlloc.DemonicValid (false, false) allocPair := by
  refine DataStructure.StateTransitionSpec.DemonicValid.liftBind (D := TwoSlotAlloc) () _
    (Or.inl rfl) fun s₁ i h₁ => ?_
  have hv₂ : TwoSlotAlloc.valid s₁ () := by
    rcases h₁ with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  exact DataStructure.StateTransitionSpec.DemonicValid.liftBind (D := TwoSlotAlloc) () _ hv₂
    fun s₂ j _ => .pure s₂ (i, j)

/-- Standalone adaptive-client bound theorem via `StateTransitionImpl.toStandard` and
`StateTransitionImpl.run_client_demonic_bound`. -/
theorem twoSlot_run_client_amortized (w base : ℕ) (h2 : Fits w 2)
    {x : Data 6} (hr : (twoSlotSubroutine w base h2).rep (false, false) x) :
    ∃ a y traces s' tr,
      DataStructure.Executes
        ((twoSlotSubroutine w base h2).toStandard.toDynamicProgram.ExecOp w)
        allocPair x a y traces ∧
      TwoSlotAlloc.ClientRun (false, false) allocPair a s' tr ∧
      (twoSlotSubroutine w base h2).rep s' y ∧
      traces.length = tr.length ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        TwoSlotAlloc.totalCostTranscript (fun _ _ => 4) (false, false) tr :=
  (twoSlotSubroutine w base h2).toStandard.run_client_demonic_bound (fun _ => rfl)
    allocPair hr allocPair_demonicValid

/-- Canonical injective register embedding `Fin 6 → Fin 8`. -/
def embed6to8 : Fin 6 → Fin 8 := Fin.castLE (by decide)

theorem embed6to8_injective : Function.Injective embed6to8 :=
  (Fin.castLEOrderEmb (by decide : 6 ≤ 8)).injective

/-- Relocated inline call via `StateTransitionImpl.call_rename` inside an 8-register caller. -/
theorem twoSlot_call_rename (w base : ℕ) (h2 : Fits w 2)
    {x : Data 8} (hx : (x.comap embed6to8).Bounded w)
    (hr : (twoSlotSubroutine w base h2).rep (false, false) (x.comap embed6to8)) :
    ∃ z s' a t,
      ExecWithin w (.seq (.op (.const 2 0)) (twoSlotCode.code.rename embed6to8)) x z t ∧
      TwoSlotAlloc.step (false, false) () s' a ∧
      (twoSlotSubroutine w base h2).decode ()
        (z.comap embed6to8).regs = some a ∧
      (twoSlotSubroutine w base h2).rep s' (z.comap embed6to8) ∧
      Modifies (Block.mk base 0).footprint (x.set 2 0).mem z.mem ∧
      (∀ j ∉ Set.range embed6to8, z.regs j = (x.set 2 0).regs j) ∧
      t ≤ 4 := by
  have hprep : ExecWithin (B := .exact) w (.op (.const (2 : Fin 8) 0)) x (x.set 2 0) 1 :=
    ⟨1, Nat.le_refl 1, Exec.const (fits_zero w)⟩
  have hb' : ((x.set 2 0).comap embed6to8).Bounded w := by
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : embed6to8 i = 2
    · simp [Data.comap, Data.set, hi, fits_zero w]
    · simp only [Fin.isValue, Data.comap_regs, Data.set_regs, Function.update_of_ne hi]
      exact hx.1 i
  have hreg : ∀ i : Fin 6, twoSlotCode.input i = false →
      (x.set 2 0).regs (embed6to8 i) = x.regs (embed6to8 i) := by
    intro i hi
    have hne : embed6to8 i ≠ 2 := by
      fin_cases i <;> revert hi <;> decide
    simp [Data.set, Function.update_of_ne hne]
  obtain ⟨z, s', a, t, he, hstep, hdec, hrep, hmod, hframe, ht⟩ :=
    (twoSlotSubroutine w base h2).call_rename
      embed6to8_injective () hr (Or.inl rfl) hprep hb' hreg (fun _ _ => rfl) trivial
  exact ⟨z, s', a, t, he, hstep, hdec, hrep, hmod, hframe, by omega⟩

/-- Two-operation sequence `[(), ()]` is demonically valid from `(false, false)`. -/
theorem twoSlot_validOpSeq :
    TwoSlotAlloc.ValidOpSeq (false, false) [(), ()] := by
  refine ⟨Or.inl rfl, fun s₁ a₁ h₁ => ?_⟩
  rcases h₁ with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
  · exact ⟨Or.inr rfl, fun _ _ _ => trivial⟩
  · exact ⟨Or.inl rfl, fun _ _ _ => trivial⟩

/-- Flat-program execution on fresh zeroed memory via `StateTransitionImpl.run_ops_exact_fresh`. -/
theorem twoSlot_run_ops_fresh (w base : ℕ) (h2 : Fits w 2)
    {d₀ : Data 6} (hd₀ : d₀.Bounded w) (hfr : d₀.regs 1 = base)
    (hz : ∀ a ∈ (Block.mk base 0).footprint, d₀.mem a = 0) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w twoSlotCode.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w twoSlotCode.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base 0).footprint d₀.mem x₀.mem ∧
      (twoSlotSubroutine w base h2).RunsOps
        (twoSlotSubroutine w base h2).prepareRegs (false, false) x₀ [(), ()] tr s_fin z
        t_ops ∧
      tr.ops = [(), ()] ∧
      TwoSlotAlloc.ValidTranscript (false, false) tr s_fin ∧
      (twoSlotSubroutine w base h2).rep s_fin z ∧
      t_init ≤ 2 ∧
      t_ops ≤ TwoSlotAlloc.totalCostTranscript (fun _ _ => 4) (false, false) tr := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
      ht_init, ht_ops⟩ :=
    (twoSlotSubroutine w base h2).run_ops_exact_fresh
      hd₀ hfr (fun j => j.elim0) hz [(), ()] twoSlot_validOpSeq
  exact ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
    ht_init, by simpa using ht_ops⟩

/-- Flat-program execution on reusable dirty memory via
`StateTransitionImpl.run_ops_exact_reusable`. -/
theorem twoSlot_run_ops_reusable (w base : ℕ) (h2 : Fits w 2)
    {d₀ : Data 6} (hd₀ : d₀.Bounded w) (hfr : d₀.regs 1 = base) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w twoSlotCode.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w twoSlotCode.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base 0).footprint d₀.mem x₀.mem ∧
      (twoSlotSubroutine w base h2).RunsOps
        (twoSlotSubroutine w base h2).prepareRegs (false, false) x₀ [(), ()] tr s_fin z
        t_ops ∧
      tr.ops = [(), ()] ∧
      TwoSlotAlloc.ValidTranscript (false, false) tr s_fin ∧
      (twoSlotSubroutine w base h2).rep s_fin z ∧
      t_init ≤ 8 ∧
      t_ops ≤ TwoSlotAlloc.totalCostTranscript (fun _ _ => 4) (false, false) tr := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
      ht_init, ht_ops⟩ :=
    (twoSlotSubroutine w base h2).run_ops_exact_reusable
      hd₀ hfr (fun j => j.elim0) [(), ()] twoSlot_validOpSeq
  exact ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
    ht_init, by simpa using ht_ops⟩

end WordRAMDynamicTests
