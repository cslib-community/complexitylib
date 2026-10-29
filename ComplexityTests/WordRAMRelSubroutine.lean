/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.Computability.WordRAM.RelSubroutine

/-!
# Tests for Relational Word-RAM Subroutine Realizations

Concrete non-vacuous tests for `Cslib.WordRAM.RelSubroutineDS`, `DynamicProgram`,
`RelDynamicCertificate`, `SubroutineDS.toRelSubroutineDS`, `RelSubroutineDS.toStandard`,
`RelSubroutineDS.call_rename`, `RelSubroutineDS.run_client_amortized`,
`RelSubroutineDS.run_ops_exact_fresh`, and `RelSubroutineDS.run_ops_exact_reusable` on a
genuinely nondeterministic two-slot allocator specification.
-/

@[expose] public section

namespace ComplexityTests.WordRAMRelSubroutine

open Cslib Cslib.Stateful Cslib.WordRAM

/-! ## 1. Nondeterministic two-slot allocator specification -/

/-- Relational specification of a two-slot allocator: from state `(b₀, b₁) : Bool × Bool`, an
allocation operation `()` nondeterministically returns any free slot `i : Fin 2` and marks slot
`i` occupied. When both slots are free (`(false, false)`), both `0` and `1` are permitted. -/
abbrev TwoSlotAlloc : RelSpec where
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

/-! ## 2. Concrete `SubroutineCode .exact` implementation and `RelSubroutineDS` certificate -/

/-- Six-register `.exact` Word-RAM subroutine implementing `TwoSlotAlloc` by sequential
allocation of slot `0` followed by slot `1`:
* register `0`: `baseReg` (persistent)
* register `1`: `frontierReg` (persistent)
* register `2`: `curReg` (scratch)
* register `3`: `zeroReg` (scratch)
* register `4`: `oneReg` / `output` (scratch)
* register `5`: persistent next-free-slot counter (`0`, `1`, or `2`). -/
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

/-- `RelSubroutineDS` certificate showing that `twoSlotCode` realizes the nondeterministic
`TwoSlotAlloc` specification whenever `Fits w 2`. -/
abbrev twoSlotSubroutine (w base : ℕ) (h2 : Fits w 2) :
    RelSubroutineDS twoSlotCode TwoSlotAlloc w base Fin.elim0 (false, false) where
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

/-! ## 3. Exercising `call_rename`, `run_client_amortized`, and flat-program execution -/

/-- Adaptive client allocating two slots sequentially and returning both indices. -/
abbrev allocPair : TwoSlotAlloc.Client (Fin 2 × Fin 2) :=
  .liftBind () fun i =>
    .liftBind () fun j =>
      .pure (i, j)

/-- `allocPair` is demonically admissible from `(false, false)` across all permitted outcomes. -/
theorem allocPair_demonicValid :
    TwoSlotAlloc.DemonicValid (false, false) allocPair := by
  refine RelSpec.DemonicValid.liftBind (D := TwoSlotAlloc) () _ (Or.inl rfl) fun s₁ i h₁ => ?_
  have hv₂ : TwoSlotAlloc.valid s₁ () := by
    rcases h₁ with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  exact RelSpec.DemonicValid.liftBind (D := TwoSlotAlloc) () _ hv₂
    fun s₂ j _ => .pure s₂ (i, j)

/-- Standalone adaptive-client amortized theorem via `RelSubroutineDS.toStandard` and
`RelSubroutineDS.run_client_amortized`. -/
theorem twoSlot_run_client_amortized (w base : ℕ) (h2 : Fits w 2)
    {x : Data 6} (hr : (twoSlotSubroutine w base h2).rep (false, false) x) :
    ∃ a y traces s' tr,
      Stateful.Executes
        ((twoSlotSubroutine w base h2).toStandard.toDynamicProgram.ExecOp w)
        allocPair x a y traces ∧
      TwoSlotAlloc.ClientRun (false, false) allocPair a s' tr ∧
      (twoSlotSubroutine w base h2).rep s' y ∧
      traces.length = tr.length ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces ≤
        TwoSlotAlloc.totalCost (fun _ _ => 4) (false, false) tr :=
  (twoSlotSubroutine w base h2).toStandard.run_client_bound (fun _ => rfl)
    allocPair hr allocPair_demonicValid

/-- Canonical injective register embedding `Fin 6 → Fin 8`. -/
def embed6to8 : Fin 6 → Fin 8 := Fin.castLE (by decide)

theorem embed6to8_injective : Function.Injective embed6to8 :=
  (Fin.castLEOrderEmb (by decide : 6 ≤ 8)).injective

/-- Relocated inline call via `RelSubroutineDS.call_rename` inside an 8-register caller. -/
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

/-- Flat-program execution on fresh zeroed memory via `RelSubroutineDS.run_ops_exact_fresh`. -/
theorem twoSlot_run_ops_fresh (w base : ℕ) (h2 : Fits w 2)
    {d₀ : Data 6} (hd₀ : d₀.Bounded w) (hfr : d₀.regs 1 = base)
    (hz : ∀ a ∈ (Block.mk base 0).footprint, d₀.mem a = 0) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w twoSlotCode.initFreshProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w twoSlotCode.initFreshProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base 0).footprint d₀.mem x₀.mem ∧
      (twoSlotSubroutine w base h2).RunsRelOps
        (twoSlotSubroutine w base h2).prepareRegs (false, false) x₀ [(), ()] tr s_fin z
        t_ops ∧
      tr.ops = [(), ()] ∧
      TwoSlotAlloc.ValidTranscript (false, false) tr s_fin ∧
      (twoSlotSubroutine w base h2).rep s_fin z ∧
      t_init ≤ 2 ∧
      t_ops ≤ TwoSlotAlloc.totalCost (fun _ _ => 4) (false, false) tr := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
      ht_init, ht_ops⟩ :=
    (twoSlotSubroutine w base h2).run_ops_exact_fresh
      hd₀ hfr (fun j => j.elim0) hz [(), ()] twoSlot_validOpSeq
  exact ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
    ht_init, by simpa using ht_ops⟩

/-- Flat-program execution on reusable dirty memory via `RelSubroutineDS.run_ops_exact_reusable`. -/
theorem twoSlot_run_ops_reusable (w base : ℕ) (h2 : Fits w 2)
    {d₀ : Data 6} (hd₀ : d₀.Bounded w) (hfr : d₀.regs 1 = base) :
    ∃ pc₀ x₀ t_init tr s_fin z t_ops,
      Runs w twoSlotCode.initClearProg ⟨0, d₀⟩ ⟨pc₀, x₀⟩ t_init ∧
      (∃ out, step w twoSlotCode.initClearProg ⟨pc₀, x₀⟩ = .halt out) ∧
      Modifies (Block.mk base 0).footprint d₀.mem x₀.mem ∧
      (twoSlotSubroutine w base h2).RunsRelOps
        (twoSlotSubroutine w base h2).prepareRegs (false, false) x₀ [(), ()] tr s_fin z
        t_ops ∧
      tr.ops = [(), ()] ∧
      TwoSlotAlloc.ValidTranscript (false, false) tr s_fin ∧
      (twoSlotSubroutine w base h2).rep s_fin z ∧
      t_init ≤ 8 ∧
      t_ops ≤ TwoSlotAlloc.totalCost (fun _ _ => 4) (false, false) tr := by
  obtain ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
      ht_init, ht_ops⟩ :=
    (twoSlotSubroutine w base h2).run_ops_exact_reusable
      hd₀ hfr (fun j => j.elim0) [(), ()] twoSlot_validOpSeq
  exact ⟨pc₀, x₀, t_init, tr, s_fin, z, t_ops, hruns, hhalt, hmod, hops_run, hops, htr, hrep,
    ht_init, by simpa using ht_ops⟩

/-! ## 4. Lifting a deterministic `SubroutineDS` via `SubroutineDS.toRelSubroutineDS` -/

/-- Deterministic specification of a bounded two-step counter (`0 → 1 → 2`). -/
abbrev DetCounter2 : Spec where
  State := ℕ
  Op := Unit
  Result _ := Fin 2
  valid n _ := n < 2
  step n _ := (n + 1, ⟨n % 2, Nat.mod_lt _ (by decide)⟩)

/-- Deterministic `SubroutineDS` certificate for `twoSlotCode` over `DetCounter2`. -/
abbrev detCounter2Subroutine (w base : ℕ) (h2 : Fits w 2) :
    SubroutineDS twoSlotCode DetCounter2 w base Fin.elim0 0 where
  space := 0
  spanTime := 1
  setupTime := 1
  initPotential := 0
  charge _ _ := 3
  rep n x := x.Bounded w ∧ x.regs 0 = base ∧ x.regs 5 = n ∧ n ≤ 2
  potential _ := 0
  encode _ _ := 0
  argMatch _ _ := True
  decode _ regs := some ⟨regs 4 % 2, Nat.mod_lt _ (by decide)⟩
  bounded hr := hr.1
  rep_unique hr₁ hr₂ := hr₁.2.2.1.symm.trans hr₂.2.2.1
  arguments_fit _ _ _ _ := fits_zero w
  encode_matches _ _ := trivial
  rep_supported {s x x'} hregs _ hx' hr := by
    refine ⟨hx', ?_, ?_, hr.2.2.2⟩
    · rw [hregs 0 rfl]; exact hr.2.1
    · rw [hregs 5 rfl]; exact hr.2.2.1
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
    · refine ⟨hx₁.set (fits_zero w), ?_, ?_, Nat.zero_le 2⟩
      · simp [Data.set, hb₁]
      · simp [Data.set]
  step_exec {s x} _ hr hv _ := by
    have h1 : Fits w 1 := h2.of_le (by decide)
    obtain ⟨hx, hb, h5, _⟩ := hr
    let x₁ := x.set 4 (x.regs 5)
    let x₂ := x₁.set 3 1
    let y := x₂.set 5 (x₂.regs 5 + x₂.regs 3)
    have hfit : Fits w (x₂.regs 5 + x₂.regs 3) := by
      have hfit2 : Fits w (s + 1) := h2.of_le hv
      simpa [x₂, x₁, Data.set, h5] using hfit2
    have heval : (Op.exactBin .add (5 : Fin 6) 5 3).eval w x₂ = some y := by
      simp only [Op.eval_exactBin, BinOp.evalExact, Option.bind_some, Data.put_of_fits hfit, y]
    have hex : Exec w twoSlotCode.code x y 3 :=
      Exec.copy.seq ((Exec.const h1).seq (Exec.op heval))
    refine ⟨y, 3, hex, ?_, ⟨hex.bounded hx, ?_, ?_, hv⟩, fun _ _ => rfl, Nat.le_refl 3⟩
    · simp [y, x₂, x₁, Data.set, h5]
    · simp [y, x₂, x₁, Data.set, hb]
    · simp [y, x₂, x₁, Data.set, h5]

/-- Lifting `detCounter2Subroutine` to `RelSubroutineDS` via `SubroutineDS.toRelSubroutineDS`. -/
def detCounter2RelSubroutine (w base : ℕ) (h2 : Fits w 2) :
    RelSubroutineDS twoSlotCode DetCounter2.toRelSpec w base Fin.elim0 0 :=
  (detCounter2Subroutine w base h2).toRelSubroutineDS

end ComplexityTests.WordRAMRelSubroutine
