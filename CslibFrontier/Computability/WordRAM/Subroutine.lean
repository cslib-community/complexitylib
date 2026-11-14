/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Dynamic
public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.MapOp
public import CslibFrontier.Computability.WordRAM.RegisterFrame

import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Composable Word-RAM subroutine infrastructure

This file provides the step-independent Word-RAM machine infrastructure for relocatable bounded-span
subroutines (`SubroutineCode`, `SubroutineBase`), along with general structured-code helpers
(`appendCode`, `execWithin_append`, `ExecWithin.loop_potential_retain`, `Data.*`).

State-transition data-structure implementations built on `SubroutineBase` live in
`CslibFrontier/DataStructure/WordRAM/StateTransition.lean`
(`Cslib.DataStructure.WordRAM.StateTransitionImpl`), and oblivious sequence implementations live in
`CslibFrontier/DataStructure/WordRAM/Randomized/ObliviousSequence.lean`
(`Cslib.DataStructure.WordRAM.Randomized.ObliviousSequenceImpl`).

## Main definitions

* `Cslib.WordRAM.SubroutineCode`, `Cslib.WordRAM.SubroutineBase`: uniform relocatable machine code
  and step-independent initialization/framing bundle for a Word-RAM subroutine.
* `Cslib.WordRAM.SubroutineCode.initFresh`, `Cslib.WordRAM.SubroutineCode.initClear`: fresh
  initialization on zeroed memory, with no zero-fill pass, and generic dirty-memory
  re-initialization, which zero-fills the block before setup.
* `Cslib.WordRAM.SubroutineCode.toDynamicProgram`: standalone canonical `DynamicProgram` projection
  with a checked, paid result-conversion suffix.
* `Cslib.WordRAM.SubroutineCode.initFreshProg`, `Cslib.WordRAM.SubroutineCode.initClearProg`,
  `Cslib.WordRAM.SubroutineCode.opProg`: compiled flat programs.

## Main results

* `Cslib.WordRAM.ExecWithin.loop_potential_retain`: potential-retaining loop rule for nested loops.
* `Cslib.WordRAM.SubroutineCode.zeroFillCode_exec`: generic `4 * space + 6` zero-fill execution.
* `Cslib.WordRAM.SubroutineBase.initFresh_exec`, `Cslib.WordRAM.SubroutineBase.initFresh_rename`,
  `Cslib.WordRAM.SubroutineBase.initClear_exec`, `Cslib.WordRAM.SubroutineBase.initClear_rename`,
  `Cslib.WordRAM.SubroutineBase.frame_caller`: relocated inline initialization and bidirectional
  register/memory framing.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 17][CLRS2009]
* [J. C. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*][Reynolds2002]
-/

@[expose] public section

namespace Cslib.WordRAM

namespace NativeResultRecoding

/-- Transport an actual result-conversion body along a defined-evaluation basis simulation.
Canonical result words, frame guarantees, and the paid budget are unchanged. -/
def mapSimulates {State : Type*} {O : Type*} {Result : O → Type}
    {B B' : Basis} {r w : ℕ}
    {decode : (o : O) → (Fin r → ℕ) → Option (Result o)}
    {rep : State → Data r → Prop} {potential : Data r → ℕ}
    (φ : B.Simulates B') (R : NativeResultRecoding Result B r w decode rep potential) :
    NativeResultRecoding Result B' r w decode rep potential where
  code := R.code.mapSimulates φ
  resultBank := R.resultBank
  resultType := R.resultType
  resultType_eq := R.resultType_eq
  ready := R.ready
  time := R.time
  execute o a hr hb hready hd := by
    obtain ⟨y, he, ha, hr', hp, hm⟩ := R.execute o a hr hb hready hd
    exact ⟨y, he.mapSimulates φ, ha, hr', hp, hm⟩

end NativeResultRecoding

/-! ## Potential-retaining loop rule and general helpers -/

/-- Right-nested sequential composition matching `ram[…]` block expansion. -/
def appendCode {B : Basis} {r : ℕ} : Code B r → Code B r → Code B r
  | .seq c₁ c₂, d => .seq c₁ (appendCode c₂ d)
  | c, d => .seq c d

/-- Bounded-step execution rule for `appendCode`. -/
theorem execWithin_append {B : Basis} {r w T₁ T₂ : ℕ} {c d : Code B r} {x y z : Data r}
    (h₁ : ExecWithin w c x y T₁) (h₂ : ExecWithin w d y z T₂) :
    ExecWithin w (appendCode c d) x z (T₁ + T₂) := by
  induction c generalizing x T₁ with
  | seq c₁ c₂ _ ih =>
    obtain ⟨n, hn, he⟩ := h₁
    cases he with
    | seq he₁ he₂ => exact (he₁.within.seq (ih he₂.within)).mono (by omega)
  | op _ | branch _ _ _ _ _ | loop _ _ _ | rand _ _ => exact h₁.seq h₂

/-- **Potential-retaining loop rule.** Like `ExecWithin.loop_potential`, but retains the remaining
exit potential `Φ z` on the left of `T + Φ z ≤ Φ x + 2` so that amortized data-structure credit
survives inner loops inside nested loops. -/
theorem ExecWithin.loop_potential_retain {B : Basis} {r w : ℕ} {cond : Cond r} {body : Code B r}
    (I : Data r → Prop) (Φ : Data r → ℕ)
    (hbody : ∀ x, I x → cond.Holds x →
      ∃ y T, ExecWithin w body x y T ∧ I y ∧ T + 2 + Φ y ≤ Φ x)
    {x : Data r} (hx : I x) :
    ∃ z T, ExecWithin w (.loop cond body) x z T ∧ I z ∧ ¬cond.Holds z ∧ T + Φ z ≤ Φ x + 2 := by
  induction hm : Φ x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    subst hm
    by_cases hc : cond.Holds x
    · obtain ⟨y, T₁, hy, hIy, hΦ⟩ := hbody x hx hc
      obtain ⟨z, T₂, hz, hIz, hcz, hΦz⟩ := ih (Φ y) (by omega) hIy rfl
      exact ⟨z, T₁ + T₂ + 2, .loop_iter hc hy hz, hIz, hcz, by omega⟩
    · exact ⟨x, 2, .loop_exit hc, hx, hc, by omega⟩

/-- `Data.comap` preserves `Bounded w`. -/
theorem Data.Bounded.comap {r r' w : ℕ} {x : Data r'} (hx : x.Bounded w) (f : Fin r → Fin r') :
    (x.comap f).Bounded w :=
  ⟨fun i => hx.1 (f i), hx.2⟩

/-- `Data.extend` preserves `Bounded w` when both `y` and `x` are bounded. -/
theorem Data.Bounded.extend {r r' w : ℕ} {f : Fin r → Fin r'} (hf : f.Injective)
    {y : Data r} {x : Data r'} (hy : y.Bounded w) (hx : x.Bounded w) :
    (y.extend f x).Bounded w := by
  refine ⟨fun j => ?_, hy.2⟩
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    change Fits w ((y.extend f x).comap f |>.regs i)
    rw [Data.comap_extend hf]
    exact hy.1 i
  · rw [Data.extend_regs_of_notMem y x hj]
    exact hx.1 j

/-! ## `SubroutineCode` and `SubroutineBase` -/

/-- Uniform machine code for a relocatable bounded-footprint data-structure subroutine over `B`,
independent of runtime problem size, base address, and word size `w`. -/
structure SubroutineCode (B : Basis) (r_ds k_init : ℕ) where
  /-- Computes `baseReg ← frontierReg` and `frontierReg ← frontierReg + space` without writes. -/
  allocSpan : Code B r_ds
  /-- Scalar/register initialization assuming `[base, base + space)` already holds zeros. -/
  initSetup : Code B r_ds
  /-- Unified operation dispatcher serving all ADT operations. -/
  code : Code B r_ds
  /-- Bump-pointer frontier register passed in and updated on initialization. -/
  frontierReg : Fin r_ds
  /-- Persistent base-address register of the allocated block. -/
  baseReg : Fin r_ds
  /-- Registers carrying runtime dimension parameters (`params`) into initialization. -/
  initParams : Fin k_init → Fin r_ds
  /-- Scratch pointer register used by generic `initClear` to zero `[base, base + space)`. -/
  curReg : Fin r_ds
  /-- Constant-`0` scratch register used by generic `initClear`. -/
  zeroReg : Fin r_ds
  /-- Constant-`1` scratch register used by generic `initClear`. -/
  oneReg : Fin r_ds
  /-- Single-instruction increment `curReg ← curReg + oneReg` over `B` for `initClear`. -/
  incCur : Op B r_ds
  /-- `true` on caller-overwritable argument/scratch registers; `false` on persistent registers. -/
  input : Fin r_ds → Bool
  /-- Primary output register returned on `halt` in `DynamicProgram`. -/
  output : Fin r_ds

namespace SubroutineCode

variable {B B' : Basis} {r_ds k_init : ℕ}

/-- Initializer when `[frontier, frontier + space)` is already zeroed (e.g. `Data.init`): runs
`allocSpan` then `initSetup`, with no zero-fill pass. `SubroutineBase.initFresh_exec` bounds it by
`SubroutineBase.initTime` instructions (`spanTime + setupTime`). -/
def initFresh (P : SubroutineCode B r_ds k_init) : Code B r_ds :=
  .seq P.allocSpan P.initSetup

/-- Generic zeroing block over `B` clearing `[baseReg, frontierReg)` using `incCur`. -/
def zeroFillCode (P : SubroutineCode B r_ds k_init) : Code B r_ds :=
  .branch (.lt P.baseReg P.frontierReg)
    (.seq (.op (.const P.zeroReg 0)) <|
     .seq (.op (.const P.oneReg 1)) <|
     .seq (.op (.copy P.curReg P.baseReg)) <|
     .loop (.lt P.curReg P.frontierReg)
       (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur)))
    (.op (.const P.zeroReg 0))

/-- Generic reusable initializer on arbitrary dirty memory (`allocSpan`, then `zeroFillCode`, then
`initSetup`). `SubroutineBase.initClear_exec` bounds it by `initTime + 4 * space + 6`
instructions. -/
def initClear (P : SubroutineCode B r_ds k_init) : Code B r_ds :=
  .seq P.allocSpan (.seq P.zeroFillCode P.initSetup)

/-- Translate a `SubroutineCode` bundle along a basis simulation. -/
def mapSimulates (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    SubroutineCode B' r_ds k_init where
  allocSpan := P.allocSpan.mapSimulates φ
  initSetup := P.initSetup.mapSimulates φ
  code := P.code.mapSimulates φ
  frontierReg := P.frontierReg
  baseReg := P.baseReg
  initParams := P.initParams
  curReg := P.curReg
  zeroReg := P.zeroReg
  oneReg := P.oneReg
  incCur := P.incCur.mapSimulates φ
  input := P.input
  output := P.output

/-- Lift an exact-basis `SubroutineCode` to `Basis.standard`. -/
abbrev toStandard (P : SubroutineCode .exact r_ds k_init) : SubroutineCode .standard r_ds k_init :=
  P.mapSimulates .exactStandard

/-- Deliver generic subroutine arguments directly, preserving maintained memory. Argument
preparation does not require constructing a native typed output interface. -/
def prepare (P : SubroutineCode B r_ds k_init) {O : Type*}
    (encode : O → Fin r_ds → ℕ) (o : O) (x : Data r_ds) : Data r_ds :=
  x.prepare P.input (encode o)

/-- Register-only argument delivery preserves every memory cell. -/
@[simp] theorem prepare_mem (P : SubroutineCode B r_ds k_init) {O : Type*}
    (encode : O → Fin r_ds → ℕ) (o : O) (x : Data r_ds) :
    (P.prepare encode o x).mem = x.mem := rfl

/-- Argument delivery preserves each register outside the input mask. -/
theorem prepare_regs_of_not_input (P : SubroutineCode B r_ds k_init) {O : Type*}
    (encode : O → Fin r_ds → ℕ) {i : Fin r_ds} (hi : P.input i = false)
    (o : O) (x : Data r_ds) :
    (P.prepare encode o x).regs i = x.regs i :=
  Data.prepare_regs_of_not_input hi (encode o) x

/-- Direct argument delivery preserves word bounds when all delivered arguments fit. -/
theorem prepare_bounded (P : SubroutineCode B r_ds k_init) {O : Type*}
    (encode : O → Fin r_ds → ℕ) {w : ℕ} {o : O} {x : Data r_ds} (hx : x.Bounded w)
    (ho : ∀ i, P.input i = true → Fits w (encode o i)) : (P.prepare encode o x).Bounded w :=
  Data.prepare_bounded hx ho

/-- Project generic subroutine code to canonical native observations by appending a checked,
paid conversion body. All conversion instructions are part of the returned program. -/
def toDynamicProgram (P : SubroutineCode B r_ds k_init) {O : Type*} {Result : O → Type}
    {State : Type*} {w : ℕ}
    (encode : O → Fin r_ds → ℕ)
    {decode : (o : O) → (Fin r_ds → ℕ) → Option (Result o)}
    {rep : State → Data r_ds → Prop} {potential : Data r_ds → ℕ}
    (R : NativeResultRecoding Result B r_ds w decode rep potential) :
    DynamicProgram ⟨O, Result⟩ r_ds B where
  code := .seq P.code R.code
  output := P.output
  input := P.input
  encode := encode
  resultBank := R.resultBank
  resultType := R.resultType
  resultType_eq := R.resultType_eq

/-- Generic execution of `P.zeroFillCode` clearing `[base, base + space)` in `4 * space + 6`
instructions over any basis `B`. -/
theorem zeroFillCode_exec (P : SubroutineCode B r_ds k_init)
    {w base space : ℕ} {params : Fin k_init → ℕ}
    (hclear : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup)
    (hparams : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg])
    (hinc : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
      P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1)))
    {x₁ : Data r_ds}
    (hx₁ : x₁.Bounded w) (hb₁ : x₁.regs P.baseReg = base)
    (hfr₁ : x₁.regs P.frontierReg = base + space)
    (hpar₁ : ∀ j, x₁.regs (P.initParams j) = params j) :
    ∃ x₂, ExecWithin w P.zeroFillCode x₁ x₂ (4 * space + 6) ∧
      x₂.Bounded w ∧
      x₂.regs P.baseReg = base ∧
      x₂.regs P.frontierReg = base + space ∧
      (∀ j, x₂.regs (P.initParams j) = params j) ∧
      (∀ a ∈ (Block.mk base space).footprint, x₂.mem a = 0) ∧
      Modifies (Block.mk base space).footprint x₁.mem x₂.mem := by
  have hfit_stop : Fits w (base + space) := hfr₁ ▸ hx₁.1 P.frontierReg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hclear
  obtain ⟨⟨hcz, hco, hcb, hcf⟩, ⟨hzo, hzb, hzf⟩, ⟨hob, hof⟩, -⟩ := hclear
  have hpar (j) : ¬P.initParams j = P.curReg ∧ ¬P.initParams j = P.zeroReg ∧
      ¬P.initParams j = P.oneReg := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hparams j
  let x_c := ((x₁.set P.zeroReg 0).set P.oneReg 1).set P.curReg base
  let xs : ℕ → Data r_ds := fun i => ⟨(x_c.set P.curReg (base + i)).regs, clear x₁.mem base i⟩
  have hloop_body (i : ℕ) (hi : i < space) :
      ExecWithin w (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur))
        (xs i) (xs (i + 1)) 2 := by
    wram_exec [xs, x_c]
    refine WP.of_execWithin (Exec.op (hinc (by wram_simp [xs, x_c]) ?_)).within ⟨le_rfl, ?_⟩
    · wram_simp [xs, x_c]
      exact hfit_stop.of_le (by omega)
    · ext a <;> simp [xs, x_c, Data.set, Data.write, Function.update_idem, clear_succ,
        Nat.add_assoc]
  have hloop : ExecWithin w
      (.loop (.lt P.curReg P.frontierReg) (.seq (.op (.store P.curReg P.zeroReg)) (.op P.incCur)))
      x_c (xs space) (space * (2 + 2) + 2) := by
    refine (show xs 0 = x_c by ext a <;> simp [xs, x_c, Data.set_set]) ▸
      ExecWithin.loop xs space 2 (fun i hi => ?_) ?_ hloop_body
    all_goals simp only [Cond.holds_lt, xs]; wram_simp [x_c, hfr₁]
    omega
  refine WP.exists_execWithin (WP.bounded hx₁ ?_)
  unfold zeroFillCode
  wram_exec [hb₁, hfr₁]
  case pos =>
    refine WP.of_execWithin hloop fun hb => ⟨by omega, hb, ?_, ?_, fun j => ?_,
      fun a ha => clear_of_owns (Block.mem_footprint.mp ha),
      fun a ha => clear_of_not_owns (mt Block.mem_footprint.mpr ha)⟩
    · wram_simp [xs, x_c, hb₁]
    · wram_simp [xs, x_c, hfr₁]
    · obtain ⟨h₁, h₂, h₃⟩ := hpar j
      wram_simp [xs, x_c, hpar₁]
  case neg =>
    have hsp0 : space = 0 := by omega
    refine fun hb => ⟨by omega, hb, by wram_simp [hb₁], by wram_simp [hfr₁], fun j => ?_,
      fun a ha => by simp [hsp0, Block.footprint] at ha, Modifies.refl _ _⟩
    obtain ⟨-, h₂, -⟩ := hpar j
    wram_simp [hpar₁]

end SubroutineCode

universe u v z

/-- Step-independent specification, representation, calling-convention, and initialization bundle
for `P : SubroutineCode B r_ds k_init` over a state type `State`, operation type `Op`, observation
family `Result`, and admissibility predicate `valid` at word width `w`, base address `base`,
runtime parameters `params`, and initial state `s₀`.

Extended by `StateTransitionImpl` so that initialization (`initFresh`, `zeroFillCode`, `initClear`),
register relocation, standalone `toDynamicProgram`, and bidirectional framing (`frame_caller`) are
stated and proved once. -/
structure SubroutineBase {B : Basis} {r_ds k_init : ℕ} (P : SubroutineCode B r_ds k_init)
    {State : Type u} {O : Type v} (Result : O → Type z) (valid : State → O → Prop)
    (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : State) where
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Instruction bound for `P.allocSpan`. -/
  spanTime : ℕ
  /-- Instruction bound for `P.initSetup`. -/
  setupTime : ℕ
  /-- Upper bound on initial concrete potential after initialization. -/
  initPotential : ℕ
  /-- Amortized instruction charge per operation (excluding trailing standalone `halt`). -/
  charge : State → O → ℕ
  /-- Representation invariant linking mathematical state `s` to concrete `Data r_ds`. -/
  rep : State → Data r_ds → Prop
  /-- Concrete integer potential depending only on `Data r_ds`. -/
  potential : Data r_ds → ℕ
  /-- Standalone register encoding for `DynamicProgram.prepare`. -/
  encode : O → Fin r_ds → ℕ
  /-- Partial argument-matching predicate for inline callers (refined by `encode`). -/
  argMatch : O → (Fin r_ds → ℕ) → Prop
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : O) → (Fin r_ds → ℕ) → Option (Result o)
  /-- Represented configurations are word-bounded. -/
  bounded : ∀ {s x}, rep s x → x.Bounded w
  /-- Standalone encoded arguments fit in `w`-bit words on admissible calls. -/
  arguments_fit : ∀ {s} (o), valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Full standalone `prepare` delivery satisfies `argMatch`. -/
  encode_matches : ∀ (o : O) (regs : Fin r_ds → ℕ),
    argMatch o (fun i => if P.input i then encode o i else regs i)
  /-- `rep` depends only on persistent registers (`P.input i = false`) and `[base, base + space)`.
  -/
  rep_supported : ∀ {s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    x'.Bounded w → rep s x → rep s x'
  /-- `potential` depends only on persistent registers and `[base, base + space)` under `rep`. -/
  potential_supported : ∀ {s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    (∀ a ∈ (Block.mk base space).footprint, x'.mem a = x.mem a) →
    rep s x → potential x' = potential x
  /-- Distinctness of registers used by `zeroFillCode` relative to `baseReg` and `frontierReg`. -/
  clear_nodup : [P.curReg, P.zeroReg, P.oneReg, P.baseReg, P.frontierReg].Nodup
  /-- Initialization parameter registers are not overwritten by `zeroFillCode`. -/
  params_not_clear : ∀ j, P.initParams j ∉ [P.curReg, P.zeroReg, P.oneReg]
  /-- `P.incCur` increments `P.curReg` by `1` when `P.oneReg = 1` and the sum fits in `w` bits. -/
  incCur_eval : ∀ {x : Data r_ds}, x.regs P.oneReg = 1 → Fits w (x.regs P.curReg + 1) →
    P.incCur.eval w x = some (x.set P.curReg (x.regs P.curReg + 1))
  /-- Execution of `P.allocSpan`: records `baseReg = base` and advances `frontierReg`. -/
  span_exec : ∀ {x : Data r_ds},
    x.Bounded w → x.regs P.frontierReg = base → (∀ j, x.regs (P.initParams j) = params j) →
    ∃ x₁, ExecWithin w P.allocSpan x x₁ spanTime ∧ x₁.mem = x.mem ∧
      x₁.regs P.baseReg = base ∧ x₁.regs P.frontierReg = base + space ∧
      (∀ j, x₁.regs (P.initParams j) = params j)
  /-- Execution of `P.initSetup` once `[base, base + space)` holds zeros. -/
  setup_exec : ∀ {x₁ : Data r_ds},
    x₁.Bounded w → x₁.regs P.baseReg = base → x₁.regs P.frontierReg = base + space →
    (∀ j, x₁.regs (P.initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x₁.mem a = 0) →
    ∃ y, ExecWithin w P.initSetup x₁ y setupTime ∧ y.regs P.frontierReg = base + space ∧
      rep s₀ y ∧ potential y ≤ initPotential ∧
      Modifies (Block.mk base space).footprint x₁.mem y.mem

namespace SubroutineBase

variable {B B' : Basis} {r_ds r_caller k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {State : Type u} {O : Type v}
  {Result : O → Type z} {valid : State → O → Prop} {params : Fin k_init → ℕ} {s₀ : State}

/-- Total instruction bound for `P.initFresh`. -/
def initTime (C : SubroutineBase P Result valid w base params s₀) : ℕ :=
  C.spanTime + C.setupTime

/-- Default register-preparation function overwriting `P.input` registers with `C.encode o`. -/
def prepareRegs (C : SubroutineBase P Result valid w base params s₀) (o : O)
    (regs : Fin r_ds → ℕ) : Fin r_ds → ℕ :=
  fun i => if P.input i then C.encode o i else regs i

/-- Lift a `SubroutineBase` bundle along any defined-evaluation basis simulation. -/
def mapSimulates (φ : B.Simulates B') (C : SubroutineBase P Result valid w base params s₀) :
    SubroutineBase (P.mapSimulates φ) Result valid w base params s₀ where
  space := C.space
  spanTime := C.spanTime
  setupTime := C.setupTime
  initPotential := C.initPotential
  charge := C.charge
  rep := C.rep
  potential := C.potential
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  clear_nodup := C.clear_nodup
  params_not_clear := C.params_not_clear
  incCur_eval h1 hfit := Op.eval_mapSimulates_of_some φ (C.incCur_eval h1 hfit)
  span_exec hx hf hp :=
    let ⟨x₁, he, hm, hb, hfr, hpar⟩ := C.span_exec hx hf hp
    ⟨x₁, he.mapSimulates φ, hm, hb, hfr, hpar⟩
  setup_exec hx₁ hb hfr hpar hz :=
    let ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.setup_exec hx₁ hb hfr hpar hz
    ⟨y, he.mapSimulates φ, hfr', hrep, hpot, hmod⟩

/-- Project a representation-relative subroutine to a native program only with an actual,
paid result conversion preserving its persistent representation, potential, and memory. -/
def toDynamicProgram {Result : O → Type}
    (C : SubroutineBase P Result valid w base params s₀)
    (R : NativeResultRecoding Result B r_ds w C.decode C.rep C.potential) :
    DynamicProgram ⟨O, Result⟩ r_ds B :=
  P.toDynamicProgram C.encode R

/-- Execute `P.initFresh` on zeroed `[base, base + C.space)` in `C.initTime` instructions. -/
theorem initFresh_exec (C : SubroutineBase P Result valid w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ y, ExecWithin w P.initFresh x y C.initTime ∧
      y.regs P.frontierReg = base + C.space ∧
      C.rep s₀ y ∧
      C.potential y ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem y.mem := by
  obtain ⟨x₁, he₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  have hx₁ : x₁.Bounded w := he₁.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base C.space).footprint, x₁.mem a = 0 := by
    intro a ha
    rw [hm₁]
    exact hz a ha
  obtain ⟨y, he₂, hfr₂, hrep, hpot, hmod⟩ := C.setup_exec hx₁ hb₁ hfr₁ hpar₁ hz₁
  rw [hm₁] at hmod
  exact ⟨y, he₁.seq he₂, hfr₂, hrep, hpot, hmod⟩

/-- Relocated fresh initialization along any injective register embedding `f`, in `C.initTime`
instructions. -/
theorem initFresh_rename (C : SubroutineBase P Result valid w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective) {x : Data r_caller}
    (hx : (x.comap f).Bounded w) (hfr : x.regs (f P.frontierReg) = base)
    (hpar : ∀ j, x.regs (f (P.initParams j)) = params j)
    (hz : ∀ a ∈ (Block.mk base C.space).footprint, x.mem a = 0) :
    ∃ z, ExecWithin w (P.initFresh.rename f) x z C.initTime ∧
      z.regs (f P.frontierReg) = base + C.space ∧
      C.rep s₀ (z.comap f) ∧
      C.potential (z.comap f) ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) := by
  obtain ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.initFresh_exec hx hfr hpar hz
  refine ⟨y.extend f x, he.rename hf, ?_, ?_, ?_, hmod,
    fun j hj => Data.extend_regs_of_notMem y x hj⟩
  · change ((y.extend f x).comap f).regs P.frontierReg = base + C.space
    rw [Data.comap_extend hf]
    exact hfr'
  · rw [Data.comap_extend hf]
    exact hrep
  · rw [Data.comap_extend hf]
    exact hpot

/-- Execute `P.initClear` on **arbitrary dirty memory** in `C.initTime + 4 * C.space + 6`
instructions. -/
theorem initClear_exec (C : SubroutineBase P Result valid w base params s₀) {x : Data r_ds}
    (hx : x.Bounded w) (hfr : x.regs P.frontierReg = base)
    (hpar : ∀ j, x.regs (P.initParams j) = params j) :
    ∃ y, ExecWithin w P.initClear x y (C.initTime + 4 * C.space + 6) ∧
      y.regs P.frontierReg = base + C.space ∧
      C.rep s₀ y ∧
      C.potential y ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem y.mem := by
  obtain ⟨x₁, he₁, hm₁, hb₁, hfr₁, hpar₁⟩ := C.span_exec hx hfr hpar
  obtain ⟨x₂, he₂, hx₂, hb₂, hfr₂, hpar₂, hz₂, hmod₂⟩ :=
    P.zeroFillCode_exec C.clear_nodup C.params_not_clear C.incCur_eval
      (he₁.bounded hx) hb₁ hfr₁ hpar₁
  obtain ⟨y, he₃, hfr₃, hrep, hpot, hmod₃⟩ := C.setup_exec hx₂ hb₂ hfr₂ hpar₂ hz₂
  rw [hm₁] at hmod₂
  have hmod : Modifies (Block.mk base C.space).footprint x.mem y.mem := by
    simpa only [Finset.union_idempotent] using hmod₂.trans hmod₃
  exact ⟨y, (he₁.seq (he₂.seq he₃)).mono (by unfold initTime; omega), hfr₃, hrep, hpot, hmod⟩

/-- Relocated dirty-memory initialization along any injective register embedding `f`, in
`C.initTime + 4 * C.space + 6` instructions. -/
theorem initClear_rename (C : SubroutineBase P Result valid w base params s₀)
    {f : Fin r_ds → Fin r_caller} (hf : f.Injective) {x : Data r_caller}
    (hx : (x.comap f).Bounded w) (hfr : x.regs (f P.frontierReg) = base)
    (hpar : ∀ j, x.regs (f (P.initParams j)) = params j) :
    ∃ z, ExecWithin w (P.initClear.rename f) x z (C.initTime + 4 * C.space + 6) ∧
      z.regs (f P.frontierReg) = base + C.space ∧
      C.rep s₀ (z.comap f) ∧
      C.potential (z.comap f) ≤ C.initPotential ∧
      Modifies (Block.mk base C.space).footprint x.mem z.mem ∧
      (∀ j ∉ Set.range f, z.regs j = x.regs j) := by
  obtain ⟨y, he, hfr', hrep, hpot, hmod⟩ := C.initClear_exec hx hfr hpar
  refine ⟨y.extend f x, he.rename hf, ?_, ?_, ?_, hmod,
    fun j hj => Data.extend_regs_of_notMem y x hj⟩
  · change ((y.extend f x).comap f).regs P.frontierReg = base + C.space
    rw [Data.comap_extend hf]
    exact hfr'
  · rw [Data.comap_extend hf]
    exact hrep
  · rw [Data.comap_extend hf]
    exact hpot

/-- Any caller state transition that preserves `(x'.comap f).Bounded w`, leaves persistent DS
registers (`P.input i = false`) unchanged, and writes only to a set `F` disjoint from
`[base, base + C.space)` preserves both `C.rep s (x'.comap f)` and `C.potential (x'.comap f)`. -/
theorem frame_caller (C : SubroutineBase P Result valid w base params s₀)
    {f : Fin r_ds → Fin r_caller} {s : State} {x x' : Data r_caller} {F : Finset ℕ}
    (hr : C.rep s (x.comap f))
    (hb' : (x'.comap f).Bounded w)
    (hreg : ∀ i, P.input i = false → x'.regs (f i) = x.regs (f i))
    (hdisj : Disjoint (Block.mk base C.space).footprint F)
    (hmem : Modifies F x.mem x'.mem) :
    C.rep s (x'.comap f) ∧ C.potential (x'.comap f) = C.potential (x.comap f) := by
  have hag : ∀ a ∈ (Block.mk base C.space).footprint, x'.mem a = x.mem a := fun a ha =>
    hmem a (fun hf => Finset.disjoint_left.mp hdisj ha hf)
  exact ⟨C.rep_supported (x := x.comap f) (x' := x'.comap f) hreg hag hb' hr,
    C.potential_supported (x := x.comap f) (x' := x'.comap f) hreg hag hr⟩

end SubroutineBase

namespace SubroutineCode

variable {B : Basis} {r_ds k_init : ℕ}

/-- Compiled flat `Program B r_ds` for fresh zeroed-memory initialization (`initFresh`). -/
def initFreshProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.initFresh.program P.output

/-- Compiled flat `Program B r_ds` for dirty-memory reusable initialization (`initClear`). -/
def initClearProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.initClear.program P.output

/-- Compiled flat `Program B r_ds` serving all operations of the data structure. -/
def opProg (P : SubroutineCode B r_ds k_init) : Program B r_ds :=
  P.code.program P.output

end SubroutineCode

end Cslib.WordRAM
