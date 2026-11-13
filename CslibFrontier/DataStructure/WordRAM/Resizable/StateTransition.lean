/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.MapOp
public import CslibFrontier.Computability.WordRAM.Resizable.Randomized
public import CslibFrontier.DataStructure.StateTransition.Amortized

/-!
# Deterministic Resizable Word RAM State-Transition Implementations

Reusable deterministic (demonic-growth-resilient) subroutine packaging (`SubroutineCode`) and
potential-amortized ([CLRS2009], Chapter 17) state-transition implementation certificates
(`StateTransitionImpl`) over the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`),
accompanying the word-granular resizable memory models of [LiLiangYuZhou2023Succincter],
Section 2.1, and [KuszmaulLiangZhou2026], Section 5.1, and adapting the bit-granular virtual-memory
variant of [LiLiangYuZhou2024], Section 3.2, at word granularity.

Unlike fixed-capacity `Cslib.DataStructure.WordRAM.StateTransitionImpl` (whose workspace
`[base, base + space)` has a single state-independent length `space`), a Resizable Word RAM
implementation owns the active suffix `[base, x.frontier)` above a caller prefix `[0, base)` and
tracks two state/operation-indexed word bounds:

1. **Resting space bound (`spaceBound : D.State → ℕ`):** after initialization and after every
   completed operation reaching abstract state `s`, the hardware frontier satisfies
   `base ≤ x.frontier ∧ x.frontier ≤ base + spaceBound s` and `x.regs P.baseReg = base`.
2. **Intermediate peak bound (`peakSpaceBound : D.State → D.Op → ℕ`):** while executing `o : D.Op`
   from `s : D.State`, every intermediate machine configuration keeps its hardware frontier
   `≤ base + peakSpaceBound s o` (`RDemonicExec w (base + peakSpaceBound s o) P.code ...`), while
   preserving caller memory `[0, base)` (`∀ addr < base, y.mem addr = x.mem addr`).
3. **Trajectory-relative address-space fit (`PeakFitsOpSeq`, `PeakFitsHistory`):** multi-operation
   execution theorems (`steps_amortized`, `seq_amortized`, `steps_amortized_ofFn`,
   `seq_amortized_ofFn`) require `Fits w (base + peakSpaceBound s_t o_t)` **only** along states
   actually reached by valid `ops`, never globally across all `s : D.State`.

## Main definitions

* `Cslib.DataStructure.WordRAM.Resizable.SubroutineCode`: relocatable Resizable Word RAM subroutine
  code bundle (`baseReg`, injective `initParams`, `input`, `initCode`, `code`).
* `Cslib.DataStructure.WordRAM.Resizable.PeakFitsOpSeq`,
  `Cslib.DataStructure.WordRAM.Resizable.PeakFitsHistory`,
  `Cslib.DataStructure.WordRAM.Resizable.maxPeakSpaceHistory`: trajectory-relative peak-frontier
  admissibility along valid relational and functional operation sequences.
* `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl`: deterministic Resizable Word RAM
  implementation and amortized-cost certificate for `D : StateTransitionSpec`.
* `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.ofFn`: `abbrev` constructor for
  functional specifications (`[D.HasStepFn f]`).
* `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.ExecSteps`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.ExecProgramSteps`: structured
  (`RDemonicExec`) and compiled flat-program (`ExecRProgramDist`) multi-operation execution
  relations.

## Main results

* `Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.mapSimulates`,
  `Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.not_readsWidth_mapSimulates`: basis
  simulation transport and `¬ReadsWidth` preservation on `SubroutineCode`.
* `Cslib.DataStructure.WordRAM.Resizable.peakFitsOpSeq_iff_peakFitsHistory`,
  `Cslib.DataStructure.WordRAM.Resizable.peakFitsHistory_of_fits_maxPeakSpaceHistory`: equivalence
  of relational and functional trajectory fit predicates and reduction to `maxPeakSpaceHistory`.
* `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.mapSimulates`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.toStandard`: basis transport from
  `Basis.exact` to `Basis.standard`.
* `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.steps_amortized`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.seq_amortized`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.steps_amortized_ofFn`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.seq_amortized_ofFn`:
  trajectory-relative multi-operation amortized execution bounds preserving caller memory
  `[0, base)`.
* `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.initProg_exec`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.ExecSteps.toExecProgramSteps`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.seq_program_amortized`,
  `Cslib.DataStructure.WordRAM.Resizable.StateTransitionImpl.seq_program_amortized_ofFn`:
  compilation to flat `RProgram` (`P.initCode.program out`, `P.code.program out`) under
  `ExecRProgramDist`.

## References

* [CLRS2009] Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
  *Introduction to Algorithms*, 3rd ed., MIT Press, 2009, Chapter 17.
* [LiLiangYuZhou2023Succincter] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
  "Succincter"*, FOCS 2023, pp. 1715–1733 (`arXiv:2309.12950v1`, Section 2.1, PDF pp. 6–7 /
  printed pp. 5–6).
* [LiLiangYuZhou2024] Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary
  with Subconstant Wasted Bits per Key*, SODA 2024 (`arXiv:2310.20536v1`, Section 3.2, PDF pp. 9–10
  / printed pp. 8–9).
* [KuszmaulLiangZhou2026] William Kuszmaul, Jingxun Liang, and Renfei Zhou, *Succinct Dynamic
  Rank/Select: Bypassing the Tree-Structure Bottleneck*, SODA 2026 (`arXiv:2510.19175v1`,
  Section 5.1, PDF pp. 16–20 / printed pp. 15–19).
-/

public section

open scoped ENNReal

namespace Cslib.DataStructure.WordRAM.Resizable

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure

universe u v z

/-! ## Relocatable Resizable Word RAM `SubroutineCode` -/

/-- Uniform machine code for a relocatable subroutine over the word-granular Resizable Word RAM
(`RCode B r_ds`). Owns the active suffix `[base, x.frontier)` recorded in `baseReg`, leaving the
caller prefix `[0, base)` untouched. -/
structure SubroutineCode (B : Basis) (r_ds k_init : ℕ) where
  /-- Persistent register holding the base address `base` of this structure's resizable suffix. -/
  baseReg : Fin r_ds
  /-- Injective register map carrying runtime initialization parameters (`params`) into `initCode`.
  -/
  initParams : Fin k_init ↪ Fin r_ds
  /-- Mask marking caller-overwritable argument/scratch registers (`false` on persistent registers).
  -/
  input : Fin r_ds → Bool
  /-- `baseReg` is persistent across standalone argument preparation. -/
  input_baseReg_false : input baseReg = false
  /-- Initializes the structure from `x₀.frontier = base`, recording `base` in `baseReg`. -/
  initCode : RCode B r_ds
  /-- Unified operation dispatcher executing `D.Op` with `.grow` / `.shrink` resizing. -/
  code : RCode B r_ds

namespace SubroutineCode

variable {B B' : Basis} {r_ds k_init : ℕ}

/-- Whether either `initCode` or `code` inspects the ambient word width `w`. -/
@[expose] def ReadsWidth (P : SubroutineCode B r_ds k_init) : Prop :=
  P.initCode.ReadsWidth ∨ P.code.ReadsWidth

/-- Compiled flat initialization `RProgram` halting with register `out`. -/
@[expose] def initProg (P : SubroutineCode B r_ds k_init) (out : Fin r_ds) : RProgram B r_ds :=
  P.initCode.program out

/-- Compiled flat operation `RProgram` halting with register `out`. -/
@[expose] def opProg (P : SubroutineCode B r_ds k_init) (out : Fin r_ds) : RProgram B r_ds :=
  P.code.program out

/-- Standalone register-preparation map overwriting `P.input` registers with `encode o`. -/
@[expose] def prepareRegs (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (regs : Fin r_ds → ℕ) : Fin r_ds → ℕ :=
  fun i => if P.input i then encode o i else regs i

/-- Deliver encoded operation arguments into `P.input` registers while preserving persistent
registers, memory, and `x.frontier`. -/
@[expose] def prepare (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (x : RData r_ds) : RData r_ds :=
  ⟨P.prepareRegs encode o x.regs, x.mem, x.frontier⟩

@[simp]
theorem prepare_regs (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (x : RData r_ds) :
    (P.prepare encode o x).regs = P.prepareRegs encode o x.regs := rfl

@[simp]
theorem prepare_mem (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (x : RData r_ds) :
    (P.prepare encode o x).mem = x.mem := rfl

@[simp]
theorem prepare_frontier (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (x : RData r_ds) :
    (P.prepare encode o x).frontier = x.frontier := rfl

theorem prepare_regs_of_not_input (P : SubroutineCode B r_ds k_init) {Op : Type v}
    {encode : Op → Fin r_ds → ℕ} {i : Fin r_ds} (hi : P.input i = false)
    (o : Op) (x : RData r_ds) :
    (P.prepare encode o x).regs i = x.regs i := by
  simp [prepare, prepareRegs, hi]

@[simp]
theorem prepare_regs_baseReg (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (x : RData r_ds) :
    (P.prepare encode o x).regs P.baseReg = x.regs P.baseReg :=
  P.prepare_regs_of_not_input P.input_baseReg_false o x

/-- `prepare` preserves `RData.Bounded w` whenever the encoded input registers fit in `w` bits. -/
theorem prepare_bounded (P : SubroutineCode B r_ds k_init) {Op : Type v} {w : ℕ}
    {encode : Op → Fin r_ds → ℕ} {o : Op} {x : RData r_ds}
    (hx : x.Bounded w) (hfit : ∀ i, P.input i = true → Fits w (encode o i)) :
    (P.prepare encode o x).Bounded w := by
  refine ⟨⟨fun i => ?_, hx.1.2⟩, hx.2.1, hx.2.2⟩
  dsimp only [prepare, prepareRegs, RData.toData]
  by_cases hi : P.input i = true
  · simp [hi, hfit i hi]
  · have hfalse : P.input i = false := Bool.eq_false_iff.mpr hi
    simp [hfalse, hx.regs_fits i]

/-- Transport a `SubroutineCode` bundle along a defined-evaluation basis simulation. -/
@[expose] def mapSimulates (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    SubroutineCode B' r_ds k_init where
  baseReg := P.baseReg
  initParams := P.initParams
  input := P.input
  input_baseReg_false := P.input_baseReg_false
  initCode := P.initCode.mapSimulates φ
  code := P.code.mapSimulates φ

/-- Transport an exact-basis `SubroutineCode` to `Basis.standard`. -/
abbrev toStandard (P : SubroutineCode .exact r_ds k_init) : SubroutineCode .standard r_ds k_init :=
  P.mapSimulates .exactStandard

@[simp]
theorem mapSimulates_baseReg (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    (P.mapSimulates φ).baseReg = P.baseReg := rfl

@[simp]
theorem mapSimulates_initParams (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    (P.mapSimulates φ).initParams = P.initParams := rfl

@[simp]
theorem mapSimulates_input (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    (P.mapSimulates φ).input = P.input := rfl

@[simp]
theorem mapSimulates_initCode (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    (P.mapSimulates φ).initCode = P.initCode.mapSimulates φ := rfl

@[simp]
theorem mapSimulates_code (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) :
    (P.mapSimulates φ).code = P.code.mapSimulates φ := rfl

@[simp]
theorem mapSimulates_prepare (φ : B.Simulates B') (P : SubroutineCode B r_ds k_init) {Op : Type v}
    (encode : Op → Fin r_ds → ℕ) (o : Op) (x : RData r_ds) :
    (P.mapSimulates φ).prepare encode o x = P.prepare encode o x := rfl

theorem not_readsWidth_initCode_mapSimulates (φ : B.Simulates B')
    {P : SubroutineCode B r_ds k_init} (h : ¬P.initCode.ReadsWidth) :
    ¬(P.mapSimulates φ).initCode.ReadsWidth :=
  fun h' => h (RCode.readsWidth_of_mapSimulates φ h')

theorem not_readsWidth_code_mapSimulates (φ : B.Simulates B')
    {P : SubroutineCode B r_ds k_init} (h : ¬P.code.ReadsWidth) :
    ¬(P.mapSimulates φ).code.ReadsWidth :=
  fun h' => h (RCode.readsWidth_of_mapSimulates φ h')

theorem not_readsWidth_mapSimulates (φ : B.Simulates B')
    {P : SubroutineCode B r_ds k_init} (h : ¬P.ReadsWidth) :
    ¬(P.mapSimulates φ).ReadsWidth := by
  rintro (hi | hc)
  · exact h (Or.inl (RCode.readsWidth_of_mapSimulates φ hi))
  · exact h (Or.inr (RCode.readsWidth_of_mapSimulates φ hc))

end SubroutineCode

/-! ## Trajectory-relative peak-frontier admissibility -/

/-- Trajectory-relative peak-frontier fit along a relational operation sequence `ops` from `s`:
requires `Fits w (base + peakSpaceBound s_t o_t)` only at states `s_t` reachable along `ops` under
`D.step`, never globally across all `s : D.State`. -/
@[expose] def PeakFitsOpSeq {D : StateTransitionSpec.{u, v, z}}
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) : List D.Op → Prop
  | [] => True
  | o :: ops =>
    Fits w (base + peakSpaceBound s o) ∧
      ∀ s' a, D.step s o s' a → PeakFitsOpSeq w base peakSpaceBound s' ops

@[simp]
theorem peakFitsOpSeq_nil {D : StateTransitionSpec.{u, v, z}}
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) :
    PeakFitsOpSeq w base peakSpaceBound s [] ↔ True := Iff.rfl

@[simp]
theorem peakFitsOpSeq_cons {D : StateTransitionSpec.{u, v, z}}
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) (o : D.Op)
    (ops : List D.Op) :
    PeakFitsOpSeq w base peakSpaceBound s (o :: ops) ↔
      Fits w (base + peakSpaceBound s o) ∧
        ∀ s' a, D.step s o s' a → PeakFitsOpSeq w base peakSpaceBound s' ops := Iff.rfl

/-- Trajectory-relative peak-frontier fit along a functional operation history `ops` from `s`
(`[D.HasStepFn f]`). -/
@[expose] def PeakFitsHistory {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) : List D.Op → Prop
  | [] => True
  | o :: os =>
    Fits w (base + peakSpaceBound s o) ∧
      PeakFitsHistory w base peakSpaceBound (D.stepFn s o).1 os

@[simp]
theorem peakFitsHistory_nil {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) :
    PeakFitsHistory w base peakSpaceBound s [] ↔ True := Iff.rfl

@[simp]
theorem peakFitsHistory_cons {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) (o : D.Op)
    (os : List D.Op) :
    PeakFitsHistory w base peakSpaceBound s (o :: os) ↔
      Fits w (base + peakSpaceBound s o) ∧
        PeakFitsHistory w base peakSpaceBound (D.stepFn s o).1 os := Iff.rfl

/-- On any functional specification `[D.HasStepFn f]`, `PeakFitsOpSeq` and `PeakFitsHistory`
coincide. -/
theorem peakFitsOpSeq_iff_peakFitsHistory {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (w base : ℕ) (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) (ops : List D.Op) :
    PeakFitsOpSeq w base peakSpaceBound s ops ↔ PeakFitsHistory w base peakSpaceBound s ops := by
  induction ops generalizing s with
  | nil => exact Iff.rfl
  | cons o os ih =>
    refine ⟨fun ⟨hfit, hnext⟩ => ⟨hfit, (ih _).mp (hnext _ _ (D.step_stepFn s o))⟩,
      fun ⟨hfit, hnext⟩ => ⟨hfit, fun s' a hstep => ?_⟩⟩
    have hpair := (D.step_iff_stepFn s o s' a).mp hstep
    have hs' : s' = (D.stepFn s o).1 := congrArg Prod.fst hpair
    subst hs'
    exact (ih _).mpr hnext

/-- Maximum `peakSpaceBound s_t o_t` encountered along the deterministic trajectory of `ops` from
`s` (`[D.HasStepFn f]`). -/
@[expose] def maxPeakSpaceHistory {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) : List D.Op → ℕ
  | [] => 0
  | o :: os =>
    max (peakSpaceBound s o) (maxPeakSpaceHistory peakSpaceBound (D.stepFn s o).1 os)

@[simp]
theorem maxPeakSpaceHistory_nil {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) :
    maxPeakSpaceHistory peakSpaceBound s [] = 0 := rfl

@[simp]
theorem maxPeakSpaceHistory_cons {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (peakSpaceBound : D.State → D.Op → ℕ) (s : D.State) (o : D.Op) (os : List D.Op) :
    maxPeakSpaceHistory peakSpaceBound s (o :: os) =
      max (peakSpaceBound s o) (maxPeakSpaceHistory peakSpaceBound (D.stepFn s o).1 os) := rfl

/-- Bounding `base + maxPeakSpaceHistory peakSpaceBound s ops` by `2 ^ w` establishes
`PeakFitsHistory` along `ops`. -/
theorem peakFitsHistory_of_fits_maxPeakSpaceHistory {D : StateTransitionSpec.{u, v, z}}
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    {w base : ℕ} {peakSpaceBound : D.State → D.Op → ℕ} {s : D.State} {ops : List D.Op}
    (h : Fits w (base + maxPeakSpaceHistory peakSpaceBound s ops)) :
    PeakFitsHistory w base peakSpaceBound s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons o os ih =>
    simp only [maxPeakSpaceHistory_cons] at h
    exact ⟨h.of_le (by omega), ih (h.of_le (by omega))⟩

/-! ## Deterministic Resizable Word RAM `StateTransitionImpl` -/

/-- Reusable deterministic (demonic-growth-resilient) Resizable Word RAM implementation certificate
for `P : SubroutineCode B r_ds k_init` realizing `D : StateTransitionSpec` at word width `w`, base
address `base`, runtime initialization parameters `params`, and initial state `s₀`, with
potential-amortized operation charges ([CLRS2009], Chapter 17), state-dependent resting footprint
`[base, base + spaceBound s)`, and intermediate peak bound `[base, base + peakSpaceBound s o)`. -/
structure StateTransitionImpl {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init) (D : StateTransitionSpec.{u, v, z})
    (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State) : Type (max u v z) where
  /-- Resting post-operation word-footprint upper bound `x.frontier ≤ base + spaceBound s`. -/
  spaceBound : D.State → ℕ
  /-- Peak intermediate word-footprint upper bound `y.frontier ≤ base + peakSpaceBound s o`
  across every machine configuration visited while executing `o` from `s`. -/
  peakSpaceBound : D.State → D.Op → ℕ
  /-- Worst-case instruction bound for `P.initCode`. -/
  initTime : ℕ
  /-- Upper bound on initial concrete potential after initialization (`0` when unamortized). -/
  initPotential : ℕ := 0
  /-- Amortized instruction charge per operation (excluding trailing standalone `halt`). -/
  charge : D.State → D.Op → ℕ
  /-- Representation invariant linking abstract state `D.State` and concrete `RData r_ds`. -/
  rep : D.State → RData r_ds → Prop
  /-- Concrete nonnegative integer potential (`0` when worst-case / unamortized). -/
  potential : RData r_ds → ℕ := fun _ => 0
  /-- Standalone register encoding for argument delivery. -/
  encode : D.Op → Fin r_ds → ℕ
  /-- Partial argument-matching predicate for inline callers (refined by `encode`). -/
  argMatch : D.Op → (Fin r_ds → ℕ) → Prop
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o)
  /-- Represented configurations satisfy `RData.Bounded w`. -/
  bounded : ∀ {s x}, rep s x → x.Bounded w
  /-- Resting frontier bounds and persistent `baseReg = base` invariant on represented states. -/
  frontier_le : ∀ {s x}, rep s x →
    base ≤ x.frontier ∧ x.frontier ≤ base + spaceBound s ∧ x.regs P.baseReg = base
  /-- `rep` depends only on persistent registers (`P.input i = false`), `x.frontier`, and active
  words `[base, x.frontier)` (caller prefix `[0, base)` may hold arbitrary `w`-bit words, and all
  words `≥ x.frontier` hold `0` under `Bounded w`). -/
  rep_supported : ∀ {s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    x'.frontier = x.frontier →
    (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
    x'.Bounded w → rep s x → rep s x'
  /-- `potential` depends only on persistent registers, `x.frontier`, and `[base, x.frontier)`
  under `rep`. -/
  potential_supported : ∀ {s x x'},
    (∀ i, P.input i = false → x'.regs i = x.regs i) →
    x'.frontier = x.frontier →
    (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
    rep s x → potential x' = potential x
  /-- Standalone encoded arguments fit in `w`-bit words on admissible calls. -/
  arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Full standalone argument delivery satisfies `argMatch`. -/
  encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
    argMatch o (fun i => if P.input i then encode o i else regs i)
  /-- Demonic-safe initialization of `P.initCode` from `x₀.frontier = base` when
  `Fits w (base + spaceBound s₀)`, preserving caller memory `[0, base)`. -/
  init_exec : ∀ {x₀ : RData r_ds},
    x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
    Fits w (base + spaceBound s₀) →
    ∃ y : RData r_ds,
      RDemonicExec w (base + spaceBound s₀) P.initCode x₀ initTime (· = y) ∧
      rep s₀ y ∧
      potential y ≤ initPotential ∧
      (∀ addr < base, y.mem addr = x₀.mem addr)
  /-- Demonic-safe execution of `P.code` on admissible `o` when
  `Fits w (base + peakSpaceBound s o)`, preserving caller memory `[0, base)` and satisfying
  `n + potential y ≤ charge s o + potential x`. -/
  step_exec : ∀ {s : D.State} {x : RData r_ds} (o : D.Op),
    rep s x → D.valid s o → argMatch o x.regs →
    Fits w (base + peakSpaceBound s o) →
    ∃ (y : RData r_ds) (s' : D.State) (a : D.Result o) (n : ℕ),
      RDemonicExec w (base + peakSpaceBound s o) P.code x n (· = y) ∧
      D.step s o s' a ∧
      decode o y.regs = some a ∧
      rep s' y ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      n + potential y ≤ charge s o + potential x

namespace StateTransitionImpl

variable {B B' : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init} {D : StateTransitionSpec.{u, v, z}}
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Construct a `StateTransitionImpl` for a deterministic specification (`[D.HasStepFn f]`) from a
functional `step_exec` proof at `D.stepFn s o`. Defined as `abbrev` so `D.Result` reduces
transparently without unfolding `StateTransitionSpec.ofFn`. -/
abbrev ofFn {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (spaceBound : D.State → ℕ)
    (peakSpaceBound : D.State → D.Op → ℕ)
    (initTime : ℕ)
    (initPotential : ℕ := 0)
    (charge : D.State → D.Op → ℕ)
    (rep : D.State → RData r_ds → Prop)
    (potential : RData r_ds → ℕ := fun _ => 0)
    (encode : D.Op → Fin r_ds → ℕ)
    (argMatch : D.Op → (Fin r_ds → ℕ) → Prop)
    (decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o))
    (bounded : ∀ {s x}, rep s x → x.Bounded w)
    (frontier_le : ∀ {s x}, rep s x →
      base ≤ x.frontier ∧ x.frontier ≤ base + spaceBound s ∧ x.regs P.baseReg = base)
    (rep_supported : ∀ {s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      x'.frontier = x.frontier →
      (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
      x'.Bounded w → rep s x → rep s x')
    (potential_supported : ∀ {s x x'},
      (∀ i, P.input i = false → x'.regs i = x.regs i) →
      x'.frontier = x.frontier →
      (∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a) →
      rep s x → potential x' = potential x)
    (arguments_fit : ∀ {s} (o), D.valid s o → ∀ i, P.input i = true → Fits w (encode o i))
    (encode_matches : ∀ (o : D.Op) (regs : Fin r_ds → ℕ),
      argMatch o (fun i => if P.input i then encode o i else regs i))
    (init_exec : ∀ {x₀ : RData r_ds},
      x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
      Fits w (base + spaceBound s₀) →
      ∃ y : RData r_ds,
        RDemonicExec w (base + spaceBound s₀) P.initCode x₀ initTime (· = y) ∧
        rep s₀ y ∧
        potential y ≤ initPotential ∧
        (∀ addr < base, y.mem addr = x₀.mem addr))
    (step_exec : ∀ {s : D.State} {x : RData r_ds} (o : D.Op),
      rep s x → D.valid s o → argMatch o x.regs →
      Fits w (base + peakSpaceBound s o) →
      ∃ (y : RData r_ds) (n : ℕ),
        RDemonicExec w (base + peakSpaceBound s o) P.code x n (· = y) ∧
        decode o y.regs = some (D.stepFn s o).2 ∧
        rep (D.stepFn s o).1 y ∧
        (∀ addr < base, y.mem addr = x.mem addr) ∧
        n + potential y ≤ charge s o + potential x) :
    StateTransitionImpl P D w base params s₀ where
  spaceBound := spaceBound
  peakSpaceBound := peakSpaceBound
  initTime := initTime
  initPotential := initPotential
  charge := charge
  rep := rep
  potential := potential
  encode := encode
  argMatch := argMatch
  decode := decode
  bounded := bounded
  frontier_le := frontier_le
  rep_supported := rep_supported
  potential_supported := potential_supported
  arguments_fit := arguments_fit
  encode_matches := encode_matches
  init_exec := init_exec
  step_exec {s _} o hr hv harg hfit := by
    obtain ⟨y, n, he, hdec, hrep, hcaller, hpot⟩ := step_exec o hr hv harg hfit
    exact ⟨y, (D.stepFn s o).1, (D.stepFn s o).2, n, he, D.step_stepFn s o, hdec, hrep,
      hcaller, hpot⟩

/-- Lift a `StateTransitionImpl` certificate along any defined-evaluation basis simulation. -/
@[expose] def mapSimulates (φ : B.Simulates B') (C : StateTransitionImpl P D w base params s₀) :
    StateTransitionImpl (P.mapSimulates φ) D w base params s₀ where
  spaceBound := C.spaceBound
  peakSpaceBound := C.peakSpaceBound
  initTime := C.initTime
  initPotential := C.initPotential
  charge := C.charge
  rep := C.rep
  potential := C.potential
  encode := C.encode
  argMatch := C.argMatch
  decode := C.decode
  bounded := C.bounded
  frontier_le := C.frontier_le
  rep_supported := C.rep_supported
  potential_supported := C.potential_supported
  arguments_fit := C.arguments_fit
  encode_matches := C.encode_matches
  init_exec hx₀ hfr hpar hfit := by
    obtain ⟨y, he, hrep, hpot, hcaller⟩ := C.init_exec hx₀ hfr hpar hfit
    exact ⟨y, he.mapSimulates φ, hrep, hpot, hcaller⟩
  step_exec o hr hv harg hfit := by
    obtain ⟨y, s', a, n, he, hstep, hdec, hrep, hcaller, hpot⟩ :=
      C.step_exec o hr hv harg hfit
    exact ⟨y, s', a, n, he.mapSimulates φ, hstep, hdec, hrep, hcaller, hpot⟩

/-- Lift an exact-basis `StateTransitionImpl` certificate to `Basis.standard`. -/
abbrev toStandard {P : SubroutineCode .exact r_ds k_init}
    (C : StateTransitionImpl P D w base params s₀) :
    StateTransitionImpl P.toStandard D w base params s₀ :=
  C.mapSimulates .exactStandard

/-- Prepare registers for operation `o` on `x`. -/
@[expose] def prepare (C : StateTransitionImpl P D w base params s₀) (o : D.Op) (x : RData r_ds) :
    RData r_ds :=
  P.prepare C.encode o x

theorem prepare_bounded (C : StateTransitionImpl P D w base params s₀)
    {s : D.State} {o : D.Op} {x : RData r_ds} (hx : x.Bounded w) (hv : D.valid s o) :
    (C.prepare o x).Bounded w :=
  P.prepare_bounded hx (C.arguments_fit o hv)

theorem prepare_rep (C : StateTransitionImpl P D w base params s₀)
    {s : D.State} {o : D.Op} {x : RData r_ds} (hr : C.rep s x) (hv : D.valid s o) :
    C.rep s (C.prepare o x) :=
  C.rep_supported
    (fun _ hi => P.prepare_regs_of_not_input hi o x)
    rfl
    (fun _ _ _ => rfl)
    (C.prepare_bounded (C.bounded hr) hv)
    hr

theorem prepare_potential (C : StateTransitionImpl P D w base params s₀)
    {s : D.State} {o : D.Op} {x : RData r_ds} (hr : C.rep s x) :
    C.potential (C.prepare o x) = C.potential x :=
  C.potential_supported
    (fun _ hi => P.prepare_regs_of_not_input hi o x)
    rfl
    (fun _ _ _ => rfl)
    hr

theorem prepare_argMatch (C : StateTransitionImpl P D w base params s₀)
    (o : D.Op) (x : RData r_ds) :
    C.argMatch o (C.prepare o x).regs :=
  C.encode_matches o x.regs

/-- Caller-frame preservation: any caller step that preserves persistent registers, `frontier`,
`[base, x.frontier)`, and `RData.Bounded w` preserves `C.rep` and `C.potential`. -/
theorem frame_caller (C : StateTransitionImpl P D w base params s₀)
    {s : D.State} {x x' : RData r_ds}
    (hregs : ∀ i, P.input i = false → x'.regs i = x.regs i)
    (hfr : x'.frontier = x.frontier)
    (hmem : ∀ a, base ≤ a → a < x.frontier → x'.mem a = x.mem a)
    (hb : x'.Bounded w) (hr : C.rep s x) :
    C.rep s x' ∧ C.potential x' = C.potential x :=
  ⟨C.rep_supported hregs hfr hmem hb hr, C.potential_supported hregs hfr hmem hr⟩

/-! ## Trajectory-relative multi-operation execution and flat `RProgram` compilation -/

/-- Structured multi-operation execution relation `C.ExecSteps s x ops tr s_fin z t_ops` over
`RDemonicExec`: at every step `o`, `P.code` executes within peak frontier
`base + C.peakSpaceBound s o`, witnesses a valid transition `D.step s o s₁ a` with decoded output
`C.decode o y.regs = some a`, preserves `C.rep` (hence resting frontier
`base ≤ y.frontier ≤ base + C.spaceBound s₁` and `y.regs P.baseReg = base`), and preserves caller
memory `[0, base)`. -/
inductive ExecSteps (C : StateTransitionImpl P D w base params s₀) :
    D.State → RData r_ds → List D.Op → D.Transcript → D.State → RData r_ds → ℕ → Prop where
  | nil (s : D.State) (x : RData r_ds) :
      C.ExecSteps s x [] [] s x 0
  | cons {s s₁ s_fin : D.State} {x y z : RData r_ds} {o : D.Op} {ops : List D.Op}
      {a : D.Result o} {tr : D.Transcript} {n rest : ℕ} :
      RDemonicExec w (base + C.peakSpaceBound s o) P.code (C.prepare o x) n (· = y) →
      D.step s o s₁ a →
      C.decode o y.regs = some a →
      C.rep s₁ y →
      (∀ addr < base, y.mem addr = x.mem addr) →
      C.ExecSteps s₁ y ops tr s_fin z rest →
      C.ExecSteps s x (o :: ops) (⟨o, a, s₁⟩ :: tr) s_fin z (n + rest)

/-- `ExecSteps` preserves caller memory `[0, base)` across the entire operation sequence. -/
theorem ExecSteps.caller_mem {C : StateTransitionImpl P D w base params s₀}
    {s s_fin : D.State} {x z : RData r_ds} {ops : List D.Op} {tr : D.Transcript} {t_ops : ℕ}
    (h : C.ExecSteps s x ops tr s_fin z t_ops) :
    ∀ addr < base, z.mem addr = x.mem addr := by
  induction h with
  | nil _ _ => exact fun _ _ => rfl
  | cons _ _ _ _ hcaller _ ih => exact fun addr hlt => (ih addr hlt).trans (hcaller addr hlt)

/-- **Trajectory-relative multi-operation amortized theorem (`steps_amortized`).**
Requires `PeakFitsOpSeq w base C.peakSpaceBound s ops` **only** along states reached by `ops` from
`s`, never globally over all `D.State`. -/
theorem steps_amortized (C : StateTransitionImpl P D w base params s₀) :
    ∀ (ops : List D.Op) {s : D.State} {x : RData r_ds},
      C.rep s x →
      D.ValidOpSeq s ops →
      PeakFitsOpSeq w base C.peakSpaceBound s ops →
      ∃ tr s_fin z t_ops,
        C.ExecSteps s x ops tr s_fin z t_ops ∧
        tr.ops = ops ∧
        D.ValidTranscript s tr s_fin ∧
        C.rep s_fin z ∧
        (∀ addr < base, z.mem addr = x.mem addr) ∧
        t_ops + C.potential z ≤ D.totalCostTranscript C.charge s tr + C.potential x
  | [], s, x, hr, _, _ =>
    ⟨[], s, x, 0, .nil s x, rfl, .nil s, hr, fun _ _ => rfl, by simp⟩
  | o :: ops, s, x, hr, ⟨hv_o, hv_rest⟩, ⟨hfit_o, hfit_rest⟩ => by
    have hr' : C.rep s (C.prepare o x) := C.prepare_rep hr hv_o
    have hpot' : C.potential (C.prepare o x) = C.potential x := C.prepare_potential hr
    obtain ⟨y, s₁, a, n, he_op, hstep, hdec, hr_y, hcaller_y, hpot_n⟩ :=
      C.step_exec o hr' hv_o (C.prepare_argMatch o x) hfit_o
    rw [hpot'] at hpot_n
    obtain ⟨tr, s_fin, z, rest, hrest, hops, htr, hr_z, hcaller_z, hpot_rest⟩ :=
      C.steps_amortized ops hr_y (hv_rest s₁ a hstep) (hfit_rest s₁ a hstep)
    refine ⟨⟨o, a, s₁⟩ :: tr, s_fin, z, n + rest,
      .cons he_op hstep hdec hr_y hcaller_y hrest,
      congrArg (o :: ·) hops, .cons _ hv_o hstep htr, hr_z,
      fun addr hlt => (hcaller_z addr hlt).trans (hcaller_y addr hlt), ?_⟩
    simp only [StateTransitionSpec.totalCostTranscript_cons]
    omega

/-- **End-to-end deterministic amortized sequence theorem (`seq_amortized`).** -/
theorem seq_amortized (C : StateTransitionImpl P D w base params s₀)
    {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidOpSeq s₀ ops)
    (hfit_ops : PeakFitsOpSeq w base C.peakSpaceBound s₀ ops) :
    ∃ (y₀ : RData r_ds) (tr : D.Transcript) (s_fin : D.State) (z : RData r_ds) (t_ops : ℕ),
      RDemonicExec w (base + C.spaceBound s₀) P.initCode x₀ C.initTime (· = y₀) ∧
      C.rep s₀ y₀ ∧
      (∀ addr < base, y₀.mem addr = x₀.mem addr) ∧
      C.ExecSteps s₀ y₀ ops tr s_fin z t_ops ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      (∀ addr < base, z.mem addr = x₀.mem addr) ∧
      C.initTime + t_ops + C.potential z ≤
        C.initTime + C.initPotential + D.totalCostTranscript C.charge s₀ tr := by
  obtain ⟨y₀, he_init, hr₀, hpot₀, hcaller₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  obtain ⟨tr, s_fin, z, t_ops, hsteps, hops, htr, hr_z, hcaller_z, hbound⟩ :=
    C.steps_amortized ops hr₀ hv hfit_ops
  exact ⟨y₀, tr, s_fin, z, t_ops, he_init, hr₀, hcaller₀, hsteps, hops, htr, hr_z,
    fun addr hlt => (hcaller_z addr hlt).trans (hcaller₀ addr hlt), by omega⟩

/-- Functional-specification specialization of `steps_amortized` (`[D.HasStepFn f]`). -/
theorem steps_amortized_ofFn
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (C : StateTransitionImpl P D w base params s₀)
    (ops : List D.Op) {s : D.State} {x : RData r_ds}
    (hr : C.rep s x)
    (hv : D.ValidHistory s ops)
    (hfit : PeakFitsHistory w base C.peakSpaceBound s ops) :
    ∃ z t_ops,
      C.ExecSteps s x ops (D.canonicalTranscript s ops) (D.run s ops).1 z t_ops ∧
      C.rep (D.run s ops).1 z ∧
      (∀ addr < base, z.mem addr = x.mem addr) ∧
      t_ops + C.potential z ≤ D.totalCost C.charge s ops + C.potential x := by
  obtain ⟨tr, s_fin, z, t_ops, hsteps, hops, htr, hr_z, hcaller, hbound⟩ :=
    C.steps_amortized ops hr
      ((D.validOpSeq_iff_validHistory s ops).mpr hv)
      ((peakFitsOpSeq_iff_peakFitsHistory w base C.peakSpaceBound s ops).mpr hfit)
  obtain ⟨_, hs_fin, htr_eq⟩ := (D.validTranscript_iff_run s tr s_fin).mp htr
  rw [hops] at hs_fin htr_eq
  subst hs_fin; subst htr_eq
  rw [D.totalCostTranscript_canonicalTranscript] at hbound
  exact ⟨z, t_ops, hsteps, hr_z, hcaller, hbound⟩

/-- **End-to-end deterministic amortized sequence theorem for functional specifications
(`seq_amortized_ofFn`).** -/
theorem seq_amortized_ofFn
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (C : StateTransitionImpl P D w base params s₀)
    {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidHistory s₀ ops)
    (hfit_ops : PeakFitsHistory w base C.peakSpaceBound s₀ ops) :
    ∃ (y₀ z : RData r_ds) (t_ops : ℕ),
      RDemonicExec w (base + C.spaceBound s₀) P.initCode x₀ C.initTime (· = y₀) ∧
      C.rep s₀ y₀ ∧
      (∀ addr < base, y₀.mem addr = x₀.mem addr) ∧
      C.ExecSteps s₀ y₀ ops (D.canonicalTranscript s₀ ops) (D.run s₀ ops).1 z t_ops ∧
      C.rep (D.run s₀ ops).1 z ∧
      (∀ addr < base, z.mem addr = x₀.mem addr) ∧
      C.initTime + t_ops + C.potential z ≤
        C.initTime + C.initPotential + D.totalCost C.charge s₀ ops := by
  obtain ⟨y₀, he_init, hr₀, hpot₀, hcaller₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  obtain ⟨z, t_ops, hsteps, hr_z, hcaller_z, hbound⟩ :=
    C.steps_amortized_ofFn ops hr₀ hv hfit_ops
  exact ⟨y₀, z, t_ops, he_init, hr₀, hcaller₀, hsteps, hr_z,
    fun addr hlt => (hcaller_z addr hlt).trans (hcaller₀ addr hlt), by omega⟩

/-- Compile `P.initCode` to the flat `RProgram` specification `ExecRProgramDist` (`P.initProg out`).
-/
theorem initProg_exec (C : StateTransitionImpl P D w base params s₀) (out : Fin r_ds)
    {x₀ : RData r_ds} (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound s₀)) :
    ∃ y₀ : RData r_ds,
      ExecRProgramDist w (P.initProg out) out x₀ (PMF.pure y₀)
        ((C.initTime + 1 : ℕ) : ℝ≥0∞) (base + C.spaceBound s₀) ∧
      C.rep s₀ y₀ ∧
      C.potential y₀ ≤ C.initPotential ∧
      (∀ addr < base, y₀.mem addr = x₀.mem addr) := by
  obtain ⟨y₀, he_init, hr₀, hpot₀, hcaller₀⟩ := C.init_exec hx₀ hfr₀ hpar hfit₀
  refine ⟨y₀, ?_, hr₀, hpot₀, hcaller₀⟩
  simpa [SubroutineCode.initProg, Nat.cast_add, Nat.cast_one] using
    (ExecRCodeDist.of_demonicExec he_init).toExecRProgramDist out

/-- Sequential flat-`RProgram` execution relation `C.ExecProgramSteps p_op out` over
`ExecRProgramDist`: ties every post-state `y` to the operational halting distribution of `p_op` at
`.halted (y.regs out) y`, enforcing `PeakFrontierLe` (`base + C.peakSpaceBound s o`), output
decoding, `C.rep`, and caller-prefix `[0, base)` preservation at every step. -/
inductive ExecProgramSteps (C : StateTransitionImpl P D w base params s₀)
    (p_op : RProgram B r_ds) (out : Fin r_ds) :
    D.State → RData r_ds → List D.Op → D.Transcript → D.State → RData r_ds → ℕ → Prop where
  | nil (s : D.State) (x : RData r_ds) :
      C.ExecProgramSteps p_op out s x [] [] s x 0
  | cons {s s₁ s_fin : D.State} {x y z : RData r_ds} {o : D.Op} {ops : List D.Op}
      {a : D.Result o} {tr : D.Transcript} {n_op rest : ℕ} :
      ExecRProgramDist w p_op out (C.prepare o x) (PMF.pure y)
        (n_op : ℝ≥0∞) (base + C.peakSpaceBound s o) →
      D.step s o s₁ a →
      C.decode o y.regs = some a →
      C.rep s₁ y →
      (∀ addr < base, y.mem addr = x.mem addr) →
      C.ExecProgramSteps p_op out s₁ y ops tr s_fin z rest →
      C.ExecProgramSteps p_op out s x (o :: ops) (⟨o, a, s₁⟩ :: tr) s_fin z (n_op + rest)

/-- Compile any structured `C.ExecSteps` derivation to `C.ExecProgramSteps (P.opProg out) out`,
charging `+ 1` instruction per operation for the trailing `halt out`. -/
theorem ExecSteps.toExecProgramSteps {C : StateTransitionImpl P D w base params s₀}
    (out : Fin r_ds) {s s_fin : D.State} {x z : RData r_ds}
    {ops : List D.Op} {tr : D.Transcript} {t_ops : ℕ}
    (h : C.ExecSteps s x ops tr s_fin z t_ops) :
    C.ExecProgramSteps (P.opProg out) out s x ops tr s_fin z (t_ops + ops.length) := by
  induction h with
  | nil s x => simpa using ExecProgramSteps.nil s x
  | @cons s s₁ s_fin x y z o ops a tr n rest he hstep hdec hrep hcaller _ ih =>
    have hprog : ExecRProgramDist w (P.opProg out) out (C.prepare o x) (PMF.pure y)
        ((n + 1 : ℕ) : ℝ≥0∞) (base + C.peakSpaceBound s o) := by
      simpa [SubroutineCode.opProg, Nat.cast_add, Nat.cast_one] using
        (ExecRCodeDist.of_demonicExec he).toExecRProgramDist out
    have hlen : (n + 1) + (rest + ops.length) = (n + rest) + (o :: ops).length := by
      simp [List.length_cons]; omega
    exact hlen ▸ ExecProgramSteps.cons hprog hstep hdec hrep hcaller ih

/-- **End-to-end flat-`RProgram` amortized sequence theorem (`seq_program_amortized`).** -/
theorem seq_program_amortized (C : StateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidOpSeq s₀ ops)
    (hfit_ops : PeakFitsOpSeq w base C.peakSpaceBound s₀ ops) :
    ∃ (y₀ : RData r_ds) (tr : D.Transcript) (s_fin : D.State) (z : RData r_ds) (t_prog : ℕ),
      ExecRProgramDist w (P.initProg out) out x₀ (PMF.pure y₀)
        ((C.initTime + 1 : ℕ) : ℝ≥0∞) (base + C.spaceBound s₀) ∧
      C.rep s₀ y₀ ∧
      (∀ addr < base, y₀.mem addr = x₀.mem addr) ∧
      C.ExecProgramSteps (P.opProg out) out s₀ y₀ ops tr s_fin z t_prog ∧
      tr.ops = ops ∧
      D.ValidTranscript s₀ tr s_fin ∧
      C.rep s_fin z ∧
      (∀ addr < base, z.mem addr = x₀.mem addr) ∧
      (C.initTime + 1) + t_prog + C.potential z ≤
        (C.initTime + 1) + C.initPotential +
          D.totalCostTranscript (fun st o => C.charge st o + 1) s₀ tr := by
  obtain ⟨y₀, tr, s_fin, z, t_ops, he_init, hr₀, hcaller₀, hsteps, hops, htr, hr_z, hcaller_z,
      hbound⟩ := C.seq_amortized ops hx₀ hfr₀ hpar hfit₀ hv hfit_ops
  have hinit_prog : ExecRProgramDist w (P.initProg out) out x₀ (PMF.pure y₀)
      ((C.initTime + 1 : ℕ) : ℝ≥0∞) (base + C.spaceBound s₀) := by
    simpa [SubroutineCode.initProg, Nat.cast_add, Nat.cast_one] using
      (ExecRCodeDist.of_demonicExec he_init).toExecRProgramDist out
  have hcost_add : ∀ {s_c : D.State} {tr_c : D.Transcript},
      D.totalCostTranscript C.charge s_c tr_c + tr_c.length =
        D.totalCostTranscript (fun st o => C.charge st o + 1) s_c tr_c := by
    intro s_c tr_c
    induction tr_c generalizing s_c with
    | nil => simp
    | cons lbl tr_tail ih =>
      rcases lbl with ⟨o_lbl, a_lbl, s_next⟩
      simp only [StateTransitionSpec.totalCostTranscript_cons, List.length_cons]
      have := ih (s_c := s_next)
      omega
  have htr_len : tr.length = ops.length := by
    simpa [StateTransitionSpec.Transcript.ops] using congrArg List.length hops
  refine ⟨y₀, tr, s_fin, z, t_ops + ops.length, hinit_prog, hr₀, hcaller₀,
    hsteps.toExecProgramSteps out, hops, htr, hr_z, hcaller_z, ?_⟩
  rw [← htr_len, ← hcost_add]
  omega

/-- **End-to-end flat-`RProgram` amortized sequence theorem for functional specifications
(`seq_program_amortized_ofFn`).** -/
theorem seq_program_amortized_ofFn
    {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]
    (C : StateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {x₀ : RData r_ds} (ops : List D.Op)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (P.initParams j) = params j)
    (hfit₀ : Fits w (base + C.spaceBound s₀))
    (hv : D.ValidHistory s₀ ops)
    (hfit_ops : PeakFitsHistory w base C.peakSpaceBound s₀ ops) :
    ∃ (y₀ z : RData r_ds) (t_prog : ℕ),
      ExecRProgramDist w (P.initProg out) out x₀ (PMF.pure y₀)
        ((C.initTime + 1 : ℕ) : ℝ≥0∞) (base + C.spaceBound s₀) ∧
      C.rep s₀ y₀ ∧
      (∀ addr < base, y₀.mem addr = x₀.mem addr) ∧
      C.ExecProgramSteps (P.opProg out) out s₀ y₀ ops
        (D.canonicalTranscript s₀ ops) (D.run s₀ ops).1 z t_prog ∧
      C.rep (D.run s₀ ops).1 z ∧
      (∀ addr < base, z.mem addr = x₀.mem addr) ∧
      (C.initTime + 1) + t_prog + C.potential z ≤
        (C.initTime + 1) + C.initPotential +
          D.totalCost (fun st o => C.charge st o + 1) s₀ ops := by
  obtain ⟨y₀, tr, s_fin, z, t_prog, hinit, hr₀, hcaller₀, hprog, hops, htr, hr_z, hcaller_z,
      hbound⟩ :=
    C.seq_program_amortized out ops hx₀ hfr₀ hpar hfit₀
      ((D.validOpSeq_iff_validHistory s₀ ops).mpr hv)
      ((peakFitsOpSeq_iff_peakFitsHistory w base C.peakSpaceBound s₀ ops).mpr hfit_ops)
  obtain ⟨_, hs_fin, htr_eq⟩ := (D.validTranscript_iff_run s₀ tr s_fin).mp htr
  rw [hops] at hs_fin htr_eq
  subst hs_fin; subst htr_eq
  rw [D.totalCostTranscript_canonicalTranscript] at hbound
  exact ⟨y₀, z, t_prog, hinit, hr₀, hcaller₀, hprog, hr_z, hcaller_z, hbound⟩

/-- **`.halt`-rejection soundness lemma (`not_execProgramSteps_halt`):** a 1-instruction
`[.halt out]` stub cannot satisfy `C.ExecProgramSteps [.halt out] out` on `(o :: ops)` whenever
every valid post-state `(s₁, a)` from `(s, o)` is incompatible with the unmodified prepared state
`C.prepare o x`. -/
theorem not_execProgramSteps_halt (C : StateTransitionImpl P D w base params s₀)
    (out : Fin r_ds) {s s_fin : D.State} {x z : RData r_ds}
    {o : D.Op} {ops : List D.Op} {tr : D.Transcript} {t_prog : ℕ}
    (hbad : ∀ s₁ a, D.step s o s₁ a →
      ¬(C.decode o (C.prepare o x).regs = some a ∧ C.rep s₁ (C.prepare o x))) :
    ¬C.ExecProgramSteps [.halt out] out s x (o :: ops) tr s_fin z t_prog := by
  intro h
  cases h with
  | @cons _ s₁ _ _ y _ _ _ a _ _ _ hprog hstep hdec hrep _ _ =>
    by_cases hyx : y = C.prepare o x
    · subst hyx
      exact hbad s₁ a hstep ⟨hdec, hrep⟩
    · exact not_execRProgramDist_halt (by simp : y ∈ (PMF.pure y).support) hyx hprog

end StateTransitionImpl

end Cslib.DataStructure.WordRAM.Resizable
