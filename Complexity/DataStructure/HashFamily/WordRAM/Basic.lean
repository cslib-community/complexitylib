/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.HashFamily.Spec
public import Complexity.DataStructure.WordRAM.Randomized.ObliviousSequence
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Word-RAM Hash-Family Implementation Interface

`Cslib.DataStructure.HashFamily.WordRAM.Impl` packages a Word-RAM hash-function data structure at
`[base, base + space)` with a finite seed type `Seed`, pure evaluation map
`eval : Seed → Fin U → Fin m`, optional deterministic table initialization `initTableCode`
(`initTableSteps`), randomized seed resampling `resampleCode` (`resampleSteps`, inducing
`PMF.uniformOfFintype Seed`), and deterministic query evaluation `evalCode` (`evalSteps`, computing
`(eval θ u).val` without modifying memory).

Every `H : Impl` canonically induces an `ObliviousSequenceImpl` certificate over
`H.subroutineCode`:
* `H.toKWiseObliviousSequenceImpl` realizing `DataStructure.HashFamily.kWiseSpec k U m` when
  `IsKWiseIndependentHash k H.eval`;
* `H.toWhpKWiseObliviousSequenceImpl` realizing `DataStructure.HashFamily.whpKWiseSpec k U m δ` when
  `H` has a two-level `(1 - δ)`-good top-seed decomposition.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.coreReg`, `opReg`, `curReg`, `zeroReg`, `oneReg`,
  `frontierReg`: register embeddings for the 5-register subroutine wrapper around `r_core` core
  hash registers.
* `Cslib.DataStructure.HashFamily.WordRAM.Impl`: Word-RAM hash-family implementation interface.
* `Cslib.DataStructure.HashFamily.WordRAM.Impl.subroutineCode`, `encode`, `decode`, `charge`,
  `initInv`: canonical `SubroutineCode` wrapper and operation encoding/decoding for
  `HashFamily.Op U`.
* `Cslib.DataStructure.HashFamily.WordRAM.Impl.toObliviousSequenceImpl`,
  `toKWiseObliviousSequenceImpl`, `toWhpKWiseObliviousSequenceImpl`: canonical
  `ObliviousSequenceImpl` certificates induced by `H : Impl`.

## Main results

* `Cslib.DataStructure.HashFamily.WordRAM.Impl.resample_exec_of_execRand`: builds the
  `resample_exec` field of `Impl` from an `ExecRand` computation and a memory seed extractor.
* `Cslib.DataStructure.HashFamily.WordRAM.Impl.arguments_fit`: encoded `HashFamily.Op U` arguments
  fit in `w`-bit words on all input registers of `H.subroutineCode`.
* `Cslib.DataStructure.HashFamily.WordRAM.Impl.evalOps_execSteps`: executing any
  `ops : List (HashFamily.Op U)` on `H.subroutineCode` induces the exact pure transcript
  distribution `HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval ops`.

## References

* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

open Cslib.WordRAM Cslib.WordRAM.Randomized Cslib.DataStructure.WordRAM.Randomized Cslib.Probability
open scoped ENNReal

namespace Cslib.DataStructure.HashFamily.WordRAM

/-- Embed a core hash-family register `i : Fin r_core` into `Fin (r_core + 5)`. -/
@[expose] def coreReg {r_core : ℕ} (i : Fin r_core) : Fin (r_core + 5) :=
  Fin.castAdd 5 i

/-- Operation-tag register `r_core` (`0` for `.resample`, `1` for `.eval u`). -/
@[expose] def opReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core, by omega⟩

/-- Scratch pointer register `r_core + 1` for `zeroFillCode` and `allocSpan`. -/
@[expose] def curReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 1, by omega⟩

/-- Constant-`0` scratch register `r_core + 2` for `zeroFillCode` and operation dispatch. -/
@[expose] def zeroReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 2, by omega⟩

/-- Constant-`1` scratch register `r_core + 3` for `zeroFillCode`. -/
@[expose] def oneReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 3, by omega⟩

/-- Bump-pointer frontier register `r_core + 4` for `allocSpan` and `zeroFillCode`. -/
@[expose] def frontierReg (r_core : ℕ) : Fin (r_core + 5) :=
  ⟨r_core + 4, by omega⟩

private theorem coreReg_injective {r_core : ℕ} :
    Function.Injective (@coreReg r_core) := by
  intro i j h
  simpa [coreReg, Fin.ext_iff] using h

private theorem coreReg_ne_of_val_ge {r_core : ℕ} (i : Fin r_core) {r : Fin (r_core + 5)}
    (hr : r_core ≤ r.val) : coreReg i ≠ r := by
  intro h
  have hval := congrArg Fin.val h
  dsimp only [coreReg, Fin.val_castAdd] at hval
  omega

private theorem frontierReg_notMem_range_coreReg {r_core : ℕ} :
    frontierReg r_core ∉ Set.range (@coreReg r_core) := by
  rintro ⟨i, hi⟩
  exact coreReg_ne_of_val_ge i (by dsimp [frontierReg]; omega) hi

/-- Reusable Word-RAM implementation certificate for a resamplable hash-family data structure over
universe `Fin U` and codomain `Fin m` at word width `w`, base address `base`, and runtime
initialization parameters `params : Fin k_init → ℕ`.

Separates deterministic table precomputation (`initTableCode`, establishing `tableRep`), randomized
seed resampling (`resampleCode`, preserving `tableRep` and sampling `Seed` uniformly into
`seedRep`), and deterministic evaluation (`evalCode`, computing `(eval θ u).val` in `outReg` without
modifying memory). -/
structure Impl (B : Basis) (r_core k_init w base U m : ℕ)
    (params : Fin k_init → ℕ) : Type 1 where
  /-- Finite type of hash seeds. -/
  Seed : Type
  /-- Finiteness instance on `Seed`. -/
  [seedFintype : Fintype Seed]
  /-- Nonemptiness instance on `Seed`. -/
  [seedNonempty : Nonempty Seed]
  /-- Pure mathematical hash evaluation map `Seed → Fin U → Fin m`. -/
  eval : Seed → Fin U → Fin m
  /-- Contiguous memory footprint length `[base, base + space)`. -/
  space : ℕ
  /-- Deterministic precomputed table invariant on memory (`fun _ => True` when none). -/
  tableRep : (ℕ → ℕ) → Prop := fun _ => True
  /-- Seed representation invariant linking `θ : Seed` to memory. -/
  seedRep : Seed → (ℕ → ℕ) → Prop
  /-- Persistent base-address register in `Fin r_core`. -/
  baseReg : Fin r_core
  /-- Input key register in `Fin r_core` for `evalCode`. -/
  keyReg : Fin r_core
  /-- Output hash-value register in `Fin r_core` for `evalCode`. -/
  outReg : Fin r_core
  /-- Registers carrying runtime parameters `params` into `initTableCode`. -/
  initParams : Fin k_init → Fin r_core
  /-- The input key register is distinct from `baseReg` so key preparation preserves `base`. -/
  key_ne_base : keyReg ≠ baseReg
  /-- Runtime parameter registers are distinct from `baseReg` so `allocSpan` preserves `params`. -/
  params_ne_base : ∀ j, initParams j ≠ baseReg
  /-- The end of the allocated footprint `base + space` fits in a `w`-bit word. -/
  fits_space : Fits w (base + space)
  /-- The evaluation dispatch tag `1` fits in a `w`-bit word. -/
  fits_tag : Fits w 1
  /-- Every universe key `u : Fin U` fits in a `w`-bit word. -/
  fits_key : ∀ u : Fin U, Fits w u.val
  /-- Single-instruction register addition `d ← a + b` over `B` on `Data (r_core + 5)`. -/
  addReg : Fin (r_core + 5) → Fin (r_core + 5) → Fin (r_core + 5) → WordRAM.Op B (r_core + 5)
  /-- `addReg d a b` sets register `d` to `x.regs a + x.regs b` when the sum fits in `w` bits. -/
  addReg_eval : ∀ {x : Data (r_core + 5)} (d a b : Fin (r_core + 5)),
    Fits w (x.regs a + x.regs b) →
    (addReg d a b).eval w x = some (x.set d (x.regs a + x.regs b))
  /-- Deterministic table initialization program on `Data r_core`. -/
  initTableCode : Code B r_core
  /-- Worst-case instruction bound for `initTableCode`. -/
  initTableSteps : ℕ
  /-- Randomized seed-resampling program on `Data r_core`. -/
  resampleCode : Code B r_core
  /-- Expected instruction bound for `resampleCode`. -/
  resampleSteps : ℕ
  /-- Deterministic hash-evaluation program on `Data r_core`. -/
  evalCode : Code B r_core
  /-- Worst-case instruction bound for `evalCode`. -/
  evalSteps : ℕ
  /-- Correctness and complexity of `initTableCode`: establishes `tableRep` and preserves `baseReg`
  while modifying only `[base, base + space)`. -/
  initTable_exec : ∀ {x : Data r_core},
    x.Bounded w → x.regs baseReg = base →
    (∀ j, x.regs (initParams j) = params j) →
    (∀ a ∈ (Block.mk base space).footprint, x.mem a = 0) →
    ∃ x₁, ExecWithin w initTableCode x x₁ initTableSteps ∧
      x₁.regs baseReg = base ∧
      tableRep x₁.mem ∧
      Modifies (Block.mk base space).footprint x.mem x₁.mem
  /-- Correctness and complexity of `resampleCode`: from any word-bounded state with
  `x.regs baseReg = base` and `tableRep x.mem`, produces a coupled distribution
  `ν : PMF (LatentState Seed r_core)` whose seed marginal is `PMF.uniformOfFintype Seed`,
  preserving `baseReg` and `tableRep`, establishing `seedRep`, and modifying only
  `[base, base + space)`. -/
  resample_exec : ∀ {x : Data r_core},
    x.Bounded w → x.regs baseReg = base → tableRep x.mem →
    ∃ ν : PMF (LatentState Seed r_core),
      ExecCodeDist w resampleCode x (ν.map LatentState.data) resampleSteps ∧
      ν.map LatentState.latent = PMF.uniformOfFintype Seed ∧
      ∀ p ∈ ν.support,
        p.data.regs baseReg = base ∧
        tableRep p.data.mem ∧
        seedRep p.latent p.data.mem ∧
        Modifies (Block.mk base space).footprint x.mem p.data.mem
  /-- Correctness and complexity of `evalCode`: from any word-bounded state with
  `x.regs baseReg = base`, `x.regs keyReg = u.val`, `tableRep x.mem`, and `seedRep θ x.mem`, halts
  within `evalSteps` instructions with `y.mem = x.mem`, `y.regs baseReg = base`, and
  `y.regs outReg = (eval θ u).val`. -/
  eval_exec : ∀ (θ : Seed) (u : Fin U) {x : Data r_core},
    x.Bounded w → x.regs baseReg = base → x.regs keyReg = u.val →
    tableRep x.mem → seedRep θ x.mem →
    ∃ y, ExecWithin w evalCode x y evalSteps ∧
      y.mem = x.mem ∧
      y.regs baseReg = base ∧
      y.regs outReg = (eval θ u).val

attribute [instance] Impl.seedFintype Impl.seedNonempty

namespace Impl

variable {B B' : Basis} {r_core k_init w base U m : ℕ} {params : Fin k_init → ℕ}

/-- Build the `resample_exec` obligation of `Impl` from an `ExecRand` computation
`m : ProbComp (Data r_core × ℕ)` and a memory seed-extraction function
`extractSeed : (ℕ → ℕ) → Seed`. -/
theorem resample_exec_of_execRand {Seed : Type} [Fintype Seed] [Nonempty Seed]
    {space resampleSteps : ℕ} {resampleCode : Code B r_core}
    {baseReg : Fin r_core} {tableRep : (ℕ → ℕ) → Prop} {seedRep : Seed → (ℕ → ℕ) → Prop}
    (extractSeed : (ℕ → ℕ) → Seed)
    {x : Data r_core} {m_comp : ProbComp (Data r_core × ℕ)}
    (hm : ExecRand w resampleCode x m_comp)
    (hunif : m_comp.eval.map (fun z => extractSeed z.1.mem) = PMF.uniformOfFintype Seed)
    (hsupp : ∀ z ∈ m_comp.support,
      z.1.regs baseReg = base ∧
      tableRep z.1.mem ∧
      seedRep (extractSeed z.1.mem) z.1.mem ∧
      Modifies (Block.mk base space).footprint x.mem z.1.mem ∧
      z.2 ≤ resampleSteps) :
    ∃ ν : PMF (LatentState Seed r_core),
      ExecCodeDist w resampleCode x (ν.map LatentState.data) resampleSteps ∧
      ν.map LatentState.latent = PMF.uniformOfFintype Seed ∧
      ∀ p ∈ ν.support,
        p.data.regs baseReg = base ∧
        tableRep p.data.mem ∧
        seedRep p.latent p.data.mem ∧
        Modifies (Block.mk base space).footprint x.mem p.data.mem := by
  let lift : Data r_core × ℕ → LatentState Seed r_core :=
    fun z => ⟨extractSeed z.1.mem, z.1⟩
  refine ⟨m_comp.eval.map lift, ?_, ?_, ?_⟩
  · refine (ExecCodeDist.of_execRand hm).congr_dist ?_ ?_
    · rw [ProbComp.eval_map, PMF.map_comp]
      rfl
    · calc
        ProbComp.expect m_comp (fun z => (z.2 : ℝ≥0∞))
          ≤ ProbComp.expect m_comp (fun _ => (resampleSteps : ℝ≥0∞)) :=
            ProbComp.expect_mono_on_support fun z hz => Nat.cast_le.mpr (hsupp z hz).2.2.2.2
        _ = (resampleSteps : ℝ≥0∞) := ProbComp.expect_const m_comp _
  · rw [PMF.map_comp]
    exact hunif
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    rw [ProbComp.support_eval] at hz
    obtain ⟨hb, htab, hseed, hmod, _⟩ := hsupp z hz
    exact ⟨hb, htab, hseed, hmod⟩

/-- Lift an `Impl` certificate along a basis simulation `φ : B.Simulates B'`. -/
def mapSimulates (φ : B.Simulates B')
    (H : Impl B r_core k_init w base U m params) :
    Impl B' r_core k_init w base U m params where
  Seed := H.Seed
  eval := H.eval
  space := H.space
  tableRep := H.tableRep
  seedRep := H.seedRep
  baseReg := H.baseReg
  keyReg := H.keyReg
  outReg := H.outReg
  initParams := H.initParams
  key_ne_base := H.key_ne_base
  params_ne_base := H.params_ne_base
  fits_space := H.fits_space
  fits_tag := H.fits_tag
  fits_key := H.fits_key
  addReg d a b := (H.addReg d a b).mapSimulates φ
  addReg_eval d a b hfit := WordRAM.Op.eval_mapSimulates_of_some φ (H.addReg_eval d a b hfit)
  initTableCode := H.initTableCode.mapSimulates φ
  initTableSteps := H.initTableSteps
  resampleCode := H.resampleCode.mapSimulates φ
  resampleSteps := H.resampleSteps
  evalCode := H.evalCode.mapSimulates φ
  evalSteps := H.evalSteps
  initTable_exec hx hb hpar hz := by
    obtain ⟨x₁, he, hb₁, htab₁, hmod₁⟩ := H.initTable_exec hx hb hpar hz
    exact ⟨x₁, he.mapSimulates φ, hb₁, htab₁, hmod₁⟩
  resample_exec hx hb htab := by
    obtain ⟨ν, he, hunif, hsupp⟩ := H.resample_exec hx hb htab
    exact ⟨ν, he.mapSimulates φ, hunif, hsupp⟩
  eval_exec θ u {x} hx hb hk htab hseed := by
    obtain ⟨y, he, hmem, hb', hout⟩ := H.eval_exec θ u hx hb hk htab hseed
    exact ⟨y, he.mapSimulates φ, hmem, hb', hout⟩

/-- Lift an `Impl` certificate from `Basis.exact` to `Basis.standard`. -/
def toStandard (H : Impl .exact r_core k_init w base U m params) :
    Impl .standard r_core k_init w base U m params :=
  H.mapSimulates .exactStandard

/-- Canonical `SubroutineCode` on `Data (r_core + 5)` wrapping `H : Impl`:
* `allocSpan` copies `frontierReg` into `coreReg H.baseReg` and advances `frontierReg` by
  `H.space`;
* `initSetup` runs `H.initTableCode` followed by `H.resampleCode` on the core registers;
* `code` sets `zeroReg r_core ← 0` and branches on `opReg r_core == 0` between
  `H.resampleCode` (`.resample`) and `H.evalCode` (`.eval u`). -/
@[expose] def subroutineCode (H : Impl B r_core k_init w base U m params) :
    SubroutineCode B (r_core + 5) k_init where
  allocSpan :=
    .seq (.op (.copy (coreReg H.baseReg) (frontierReg r_core)))
    (.seq (.op (.const (curReg r_core) H.space))
          (.op (H.addReg (frontierReg r_core) (frontierReg r_core) (curReg r_core))))
  initSetup :=
    .seq (H.initTableCode.rename coreReg) (H.resampleCode.rename coreReg)
  code :=
    .seq (.op (.const (zeroReg r_core) 0))
         (.branch (.eq (opReg r_core) (zeroReg r_core))
           (H.resampleCode.rename coreReg)
           (H.evalCode.rename coreReg))
  frontierReg := frontierReg r_core
  baseReg := coreReg H.baseReg
  initParams j := coreReg (H.initParams j)
  curReg := curReg r_core
  zeroReg := zeroReg r_core
  oneReg := oneReg r_core
  incCur := H.addReg (curReg r_core) (curReg r_core) (oneReg r_core)
  input r := decide (r = opReg r_core ∨ r = coreReg H.keyReg)
  output := coreReg H.outReg

/-- Standalone register encoding for `HashFamily.Op U` on `H.subroutineCode`:
* `.resample` sets `opReg r_core ← 0` and `coreReg H.keyReg ← 0`;
* `.eval u` sets `opReg r_core ← 1` and `coreReg H.keyReg ← u.val`. -/
@[expose] def encode (H : Impl B r_core k_init w base U m params) :
    HashFamily.Op U → Fin (r_core + 5) → ℕ
  | .resample, _ => 0
  | .eval u, r =>
    if r = opReg r_core then 1
    else if r = coreReg H.keyReg then u.val
    else 0

/-- Every encoded `HashFamily.Op U` argument fits in a `w`-bit word on all input registers of
`H.subroutineCode`. -/
theorem arguments_fit (H : Impl B r_core k_init w base U m params)
    (o : HashFamily.Op U) (i : Fin (r_core + 5))
    (hi : H.subroutineCode.input i = true) :
    Fits w (H.encode o i) := by
  have hfit0 : Fits w 0 := H.fits_space.of_le (Nat.zero_le _)
  rcases of_decide_eq_true hi with rfl | rfl <;> cases o with
  | resample => exact hfit0
  | eval u =>
    dsimp only [encode]
    split_ifs <;> first | exact H.fits_tag | exact H.fits_key u | exact hfit0

/-- Output decoder for `HashFamily.Op U` on `H.subroutineCode`: returns `some PUnit.unit` on
`.resample` and reads `regs (coreReg H.outReg) < m` on `.eval u`. -/
@[expose] def decode (H : Impl B r_core k_init w base U m params) :
    (o : HashFamily.Op U) → (Fin (r_core + 5) → ℕ) → Option (HashFamily.Result m o)
  | .resample, _ => some PUnit.unit
  | .eval _, regs =>
    if h : regs (coreReg H.outReg) < m then
      some ⟨regs (coreReg H.outReg), h⟩
    else
      none

/-- Per-operation instruction charge on `H.subroutineCode`: `H.resampleSteps + 2` for `.resample`
and `H.evalSteps + 3` for `.eval u`. -/
@[expose] def charge (H : Impl B r_core k_init w base U m params) :
    HashFamily.Op U → ℕ
  | .resample => H.resampleSteps + 2
  | .eval _ => H.evalSteps + 3

/-- Distributional invariant on the initial state distribution produced by
`H.subroutineCode.initSetup`. -/
@[expose] def initInv (H : Impl B r_core k_init w base U m params)
    (ν₀ : PMF (LatentState H.Seed (r_core + 5))) : Prop :=
  ν₀.map LatentState.latent = PMF.uniformOfFintype H.Seed ∧
  ∀ t ∈ ν₀.support,
    t.data.Bounded w ∧
    t.data.regs (coreReg H.baseReg) = base ∧
    H.tableRep t.data.mem ∧
    H.seedRep t.latent t.data.mem

private theorem clear_nodup_subroutineCode
    (H : Impl B r_core k_init w base U m params) :
    [H.subroutineCode.curReg, H.subroutineCode.zeroReg, H.subroutineCode.oneReg,
      H.subroutineCode.baseReg, H.subroutineCode.frontierReg].Nodup := by
  have hb := H.baseReg.isLt
  simp only [subroutineCode, curReg, zeroReg, oneReg, coreReg, frontierReg,
    Fin.castAdd, Fin.castLE, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    Fin.mk.injEq, List.nodup_nil, not_false_eq_true, and_true]
  omega

private theorem params_not_clear_subroutineCode
    (H : Impl B r_core k_init w base U m params) (j : Fin k_init) :
    H.subroutineCode.initParams j ∉
      [H.subroutineCode.curReg, H.subroutineCode.zeroReg, H.subroutineCode.oneReg] := by
  have hj := (H.initParams j).isLt
  simp only [subroutineCode, curReg, zeroReg, oneReg, coreReg,
    Fin.castAdd, Fin.castLE, List.mem_cons, List.not_mem_nil, or_false, not_or, Fin.mk.injEq]
  omega

private theorem span_exec_subroutineCode
    (H : Impl B r_core k_init w base U m params)
    {x : Data (r_core + 5)}
    (hfr : x.regs H.subroutineCode.frontierReg = base)
    (hpar : ∀ j, x.regs (H.subroutineCode.initParams j) = params j) :
    ∃ x₁, ExecWithin w H.subroutineCode.allocSpan x x₁ 3 ∧ x₁.mem = x.mem ∧
      x₁.regs H.subroutineCode.baseReg = base ∧
      x₁.regs H.subroutineCode.frontierReg = base + H.space ∧
      (∀ j, x₁.regs (H.subroutineCode.initParams j) = params j) := by
  have hfr' : x.regs (frontierReg r_core) = base := hfr
  have hfit_sp : Fits w H.space := H.fits_space.of_le (Nat.le_add_left H.space base)
  set s₁ := x.set (coreReg H.baseReg) base
  have e₁ : ExecWithin (B := B) w
      (.op (.copy (coreReg H.baseReg) (frontierReg r_core))) x s₁ 1 := by
    simpa [s₁, hfr'] using
      (Exec.copy (B := B) (w := w) (d := coreReg H.baseReg)
        (s := frontierReg r_core) (x := x)).within
  set s₂ := s₁.set (curReg r_core) H.space
  have e₂ : ExecWithin (B := B) w (.op (.const (curReg r_core) H.space)) s₁ s₂ 1 :=
    (Exec.const hfit_sp).within
  have hs₂_fr : s₂.regs (frontierReg r_core) = base := by
    have hne₁ : frontierReg r_core ≠ curReg r_core := by
      simp [frontierReg, curReg, Fin.ext_iff]
    have hne₂ : frontierReg r_core ≠ coreReg H.baseReg :=
      (coreReg_ne_of_val_ge H.baseReg (by simp [frontierReg])).symm
    simp [s₂, s₁, Data.set, Function.update_of_ne hne₁, Function.update_of_ne hne₂, hfr']
  have hs₂_cur : s₂.regs (curReg r_core) = H.space := by simp [s₂]
  set s₃ := s₂.set (frontierReg r_core) (base + H.space)
  have e₃ : ExecWithin w
      (.op (H.addReg (frontierReg r_core) (frontierReg r_core) (curReg r_core)))
      s₂ s₃ 1 := by
    have heval := H.addReg_eval (x := s₂)
      (frontierReg r_core) (frontierReg r_core) (curReg r_core)
      (by rw [hs₂_fr, hs₂_cur]; exact H.fits_space)
    rw [hs₂_fr, hs₂_cur] at heval
    exact (Exec.op heval).within
  refine ⟨s₃, (e₁.seq (e₂.seq e₃)).mono (by omega), rfl, ?_, by simp [s₃, subroutineCode], ?_⟩
  · have hne₁ : coreReg H.baseReg ≠ frontierReg r_core :=
      coreReg_ne_of_val_ge H.baseReg (by simp [frontierReg])
    have hne₂ : coreReg H.baseReg ≠ curReg r_core :=
      coreReg_ne_of_val_ge H.baseReg (by simp [curReg])
    simp [s₃, s₂, s₁, subroutineCode, Data.set,
      Function.update_of_ne hne₁, Function.update_of_ne hne₂]
  · intro j
    have hne₁ : coreReg (H.initParams j) ≠ frontierReg r_core :=
      coreReg_ne_of_val_ge (H.initParams j) (by simp [frontierReg])
    have hne₂ : coreReg (H.initParams j) ≠ curReg r_core :=
      coreReg_ne_of_val_ge (H.initParams j) (by simp [curReg])
    have hne₃ : coreReg (H.initParams j) ≠ coreReg H.baseReg :=
      fun h => H.params_ne_base j (coreReg_injective h)
    simp only [s₃, s₂, s₁, subroutineCode, Data.set,
      Function.update_of_ne hne₁, Function.update_of_ne hne₂, Function.update_of_ne hne₃]
    exact hpar j

private theorem setup_exec_subroutineCode
    (H : Impl B r_core k_init w base U m params)
    {x₁ : Data (r_core + 5)}
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs H.subroutineCode.baseReg = base)
    (hfr : x₁.regs H.subroutineCode.frontierReg = base + H.space)
    (hpar : ∀ j, x₁.regs (H.subroutineCode.initParams j) = params j)
    (hz : ∀ a ∈ (Block.mk base H.space).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (LatentState H.Seed (r_core + 5)),
      ExecCodeDist w H.subroutineCode.initSetup x₁ (ν₀.map LatentState.data)
        ((H.initTableSteps + H.resampleSteps : ℕ) : ℝ≥0∞) ∧
      H.initInv ν₀ ∧
      ∀ t ∈ ν₀.support,
        t.data.Bounded w ∧
        t.data.regs H.subroutineCode.frontierReg = base + H.space ∧
        Modifies (Block.mk base H.space).footprint x₁.mem t.data.mem := by
  obtain ⟨y_tab, he_tab, hy_base, hy_tab, hy_mod⟩ :=
    H.initTable_exec (hx₁.comap coreReg) hb hpar hz
  have hy_bdd : y_tab.Bounded w := he_tab.bounded (hx₁.comap coreReg)
  let x₂ : Data (r_core + 5) := y_tab.extend coreReg x₁
  have hx₂_bdd : x₂.Bounded w := hy_bdd.extend coreReg_injective hx₁
  have he_tab_ren : ExecCodeDist w (H.initTableCode.rename coreReg) x₁ (PMF.pure x₂)
      (H.initTableSteps : ℝ≥0∞) := by
    simpa [x₂] using (ExecCodeDist.of_execWithin he_tab).rename coreReg_injective
  have hx₂_comap : x₂.comap coreReg = y_tab :=
    Data.comap_extend coreReg_injective y_tab x₁
  obtain ⟨ν_core, he_res, hunif, hsupp_res⟩ :=
    H.resample_exec (x := x₂.comap coreReg)
      (hx₂_bdd.comap coreReg)
      (by rw [hx₂_comap]; exact hy_base)
      (by rw [hx₂_comap]; exact hy_tab)
  have he_res_ren := he_res.rename coreReg_injective
  let lift0 : LatentState H.Seed r_core → LatentState H.Seed (r_core + 5) :=
    fun p => ⟨p.latent, p.data.extend coreReg x₂⟩
  let ν₀ : PMF (LatentState H.Seed (r_core + 5)) := ν_core.map lift0
  have he_res_ν₀ : ExecCodeDist w (H.resampleCode.rename coreReg) x₂
      (ν₀.map LatentState.data) (H.resampleSteps : ℝ≥0∞) := by
    refine he_res_ren.congr_dist ?_ le_rfl
    dsimp only [ν₀, lift0]
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  refine ⟨ν₀, ?_, ⟨?_, ?_⟩, ?_⟩
  · simpa only [subroutineCode, Nat.cast_add] using he_tab_ren.seq_pure he_res_ν₀
  · dsimp only [ν₀, lift0]
    rw [PMF.map_comp]
    exact hunif
  · intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    obtain ⟨hp_base, hp_tab, hp_seed, _⟩ := hsupp_res p hp
    have hp_bdd : p.data.Bounded w :=
      he_res.bounded (hx₂_bdd.comap coreReg) p.data
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩)
    have hreg : (p.data.extend coreReg x₂).regs (coreReg H.baseReg) = base := by
      change ((p.data.extend coreReg x₂).comap coreReg).regs H.baseReg = base
      rw [Data.comap_extend coreReg_injective]
      exact hp_base
    exact ⟨hp_bdd.extend coreReg_injective hx₂_bdd, hreg, hp_tab, hp_seed⟩
  · intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    obtain ⟨_, _, _, hp_mod⟩ := hsupp_res p hp
    have hp_bdd : p.data.Bounded w :=
      he_res.bounded (hx₂_bdd.comap coreReg) p.data
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩)
    have hfr_t : (p.data.extend coreReg x₂).regs (frontierReg r_core) = base + H.space := by
      rw [Data.extend_regs_of_notMem _ _ frontierReg_notMem_range_coreReg,
        Data.extend_regs_of_notMem _ _ frontierReg_notMem_range_coreReg]
      exact hfr
    have hmod_t : Modifies (Block.mk base H.space).footprint x₁.mem p.data.mem := by
      simpa only [Data.comap, Finset.union_idempotent] using hy_mod.trans hp_mod
    exact ⟨hp_bdd.extend coreReg_injective hx₂_bdd, hfr_t, hmod_t⟩

private theorem step_resample_subroutineCode
    (H : Impl B r_core k_init w base U m params)
    (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5))
    (hbdd : t.data.Bounded w)
    (hb : t.data.regs (coreReg H.baseReg) = base)
    (htab : H.tableRep t.data.mem) :
    ∃ μ_t : PMF (StepOutcome H.Seed PUnit (r_core + 5)),
      ExecCodeDist w H.subroutineCode.code
        ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare .resample t.data)
        (μ_t.map StepOutcome.data) ((H.charge .resample : ℕ) : ℝ≥0∞) ∧
      μ_t.map StepOutcome.latent = PMF.uniformOfFintype H.Seed ∧
      ∀ q ∈ μ_t.support,
        q.data.Bounded w ∧
        H.decode .resample q.data.regs = some q.result ∧
        Modifies (Block.mk base H.space).footprint t.data.mem q.data.mem ∧
        q.data.regs (coreReg H.baseReg) = base ∧
        H.tableRep q.data.mem ∧
        H.seedRep q.latent q.data.mem := by
  let x_prep := (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare .resample t.data
  have hx_prep : x_prep.Bounded w :=
    (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare_bounded hbdd
      (H.arguments_fit .resample)
  let x_z := x_prep.set (zeroReg r_core) 0
  have he_z : ExecCodeDist (B := B) w (.op (.const (zeroReg r_core) 0))
      x_prep (PMF.pure x_z) 1 := by
    simpa [x_z] using ExecCodeDist.of_exec (Exec.const (H.fits_space.of_le (Nat.zero_le _)))
  have hx_z : x_z.Bounded w := he_z.bounded hx_prep x_z (by simp)
  have hc_pos : (Cond.eq (opReg r_core) (zeroReg r_core)).Holds x_z := by
    have hne : opReg r_core ≠ zeroReg r_core := by
      simp [opReg, zeroReg, Fin.ext_iff]
    simp [Cond.Holds, x_z, x_prep, SubroutineCode.toDynamicProgram, DynamicProgram.prepare,
      subroutineCode, encode, Data.set, Function.update_of_ne hne]
  have hxz_base : (x_z.comap coreReg).regs H.baseReg = base := by
    have hne_z : coreReg H.baseReg ≠ zeroReg r_core :=
      coreReg_ne_of_val_ge H.baseReg (by simp [zeroReg])
    have hne_op : coreReg H.baseReg ≠ opReg r_core :=
      coreReg_ne_of_val_ge H.baseReg (by simp [opReg])
    have hne_key : coreReg H.baseReg ≠ coreReg H.keyReg :=
      fun h => H.key_ne_base (coreReg_injective h.symm)
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, subroutineCode,
      hne_op, hne_key, hb]
  have hxz_mem : (x_z.comap coreReg).mem = t.data.mem := rfl
  obtain ⟨ν_core, he_res, hunif, hsupp⟩ :=
    H.resample_exec (hx_z.comap coreReg) hxz_base (by rw [hxz_mem]; exact htab)
  have he_res_ren := he_res.rename coreReg_injective
  let liftStep : LatentState H.Seed r_core → StepOutcome H.Seed PUnit (r_core + 5) :=
    fun p => ⟨p.latent, p.data.extend coreReg x_z, PUnit.unit⟩
  let μ_t : PMF (StepOutcome H.Seed PUnit (r_core + 5)) := ν_core.map liftStep
  have he_branch : ExecCodeDist w
      (.branch (.eq (opReg r_core) (zeroReg r_core))
        (H.resampleCode.rename coreReg)
        (H.evalCode.rename coreReg))
      x_z (μ_t.map StepOutcome.data) ((H.resampleSteps : ℝ≥0∞) + 1) := by
    refine (ExecCodeDist.branch_pos hc_pos he_res_ren).congr_dist ?_ le_rfl
    dsimp only [μ_t, liftStep]
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  refine ⟨μ_t, ?_, ?_, ?_⟩
  · have hseq := he_z.seq_pure he_branch
    refine hseq.congr_dist rfl (le_of_eq ?_)
    simp only [charge, Nat.cast_add, Nat.cast_ofNat]
    ring
  · dsimp only [μ_t, liftStep]
    rw [PMF.map_comp]
    exact hunif
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨hp_base, hp_tab, hp_seed, hp_mod⟩ := hsupp p hp
    have hp_bdd : p.data.Bounded w :=
      he_res.bounded (hx_z.comap coreReg) p.data
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp, rfl⟩)
    have hreg : (p.data.extend coreReg x_z).regs (coreReg H.baseReg) = base := by
      change ((p.data.extend coreReg x_z).comap coreReg).regs H.baseReg = base
      rw [Data.comap_extend coreReg_injective]
      exact hp_base
    exact ⟨hp_bdd.extend coreReg_injective hx_z, rfl, hp_mod, hreg, hp_tab, hp_seed⟩

private theorem step_eval_subroutineCode
    (H : Impl B r_core k_init w base U m params) (u : Fin U)
    (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5))
    (hbdd : t.data.Bounded w)
    (hb : t.data.regs (coreReg H.baseReg) = base)
    (htab : H.tableRep t.data.mem)
    (hseed : H.seedRep t.latent t.data.mem) :
    ∃ y_ext : Data (r_core + 5),
      ExecCodeDist w H.subroutineCode.code
        ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare (.eval u) t.data)
        (PMF.pure y_ext) ((H.charge (.eval u) : ℕ) : ℝ≥0∞) ∧
      y_ext.Bounded w ∧
      H.decode (.eval u) y_ext.regs = some (H.eval t.latent u) ∧
      y_ext.mem = t.data.mem ∧
      y_ext.regs (coreReg H.baseReg) = base := by
  let x_prep := (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare (.eval u) t.data
  have hx_prep : x_prep.Bounded w :=
    (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare_bounded hbdd
      (H.arguments_fit (.eval u))
  let x_z := x_prep.set (zeroReg r_core) 0
  have he_z : ExecCodeDist (B := B) w (.op (.const (zeroReg r_core) 0))
      x_prep (PMF.pure x_z) 1 := by
    simpa [x_z] using ExecCodeDist.of_exec (Exec.const (H.fits_space.of_le (Nat.zero_le _)))
  have hx_z : x_z.Bounded w := he_z.bounded hx_prep x_z (by simp)
  have hc_neg : ¬(Cond.eq (opReg r_core) (zeroReg r_core)).Holds x_z := by
    have hne : opReg r_core ≠ zeroReg r_core := by
      simp [opReg, zeroReg, Fin.ext_iff]
    simp [Cond.Holds, x_z, x_prep, SubroutineCode.toDynamicProgram, DynamicProgram.prepare,
      subroutineCode, encode, Data.set, Function.update_of_ne hne]
  have hxz_base : (x_z.comap coreReg).regs H.baseReg = base := by
    have hne_z : coreReg H.baseReg ≠ zeroReg r_core :=
      coreReg_ne_of_val_ge H.baseReg (by simp [zeroReg])
    have hne_op : coreReg H.baseReg ≠ opReg r_core :=
      coreReg_ne_of_val_ge H.baseReg (by simp [opReg])
    have hne_key : coreReg H.baseReg ≠ coreReg H.keyReg :=
      fun h => H.key_ne_base (coreReg_injective h.symm)
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, subroutineCode,
      hne_op, hne_key, hb]
  have hxz_key : (x_z.comap coreReg).regs H.keyReg = u.val := by
    have hne_z : coreReg H.keyReg ≠ zeroReg r_core :=
      coreReg_ne_of_val_ge H.keyReg (by simp [zeroReg])
    have hne_op : coreReg H.keyReg ≠ opReg r_core :=
      coreReg_ne_of_val_ge H.keyReg (by simp [opReg])
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, subroutineCode,
      encode, hne_op]
  obtain ⟨y_core, he_eval, hy_mem, hy_base, hy_out⟩ :=
    H.eval_exec t.latent u (hx_z.comap coreReg) hxz_base hxz_key htab hseed
  have hy_bdd : y_core.Bounded w := he_eval.bounded (hx_z.comap coreReg)
  let y_ext : Data (r_core + 5) := y_core.extend coreReg x_z
  have hy_ext_bdd : y_ext.Bounded w := hy_bdd.extend coreReg_injective hx_z
  have he_eval_ren : ExecCodeDist w (H.evalCode.rename coreReg) x_z
      (PMF.pure y_ext) (H.evalSteps : ℝ≥0∞) := by
    simpa [y_ext] using (ExecCodeDist.of_execWithin he_eval).rename coreReg_injective
  have he_branch : ExecCodeDist w
      (.branch (.eq (opReg r_core) (zeroReg r_core))
        (H.resampleCode.rename coreReg)
        (H.evalCode.rename coreReg))
      x_z (PMF.pure y_ext) ((H.evalSteps : ℝ≥0∞) + 2) :=
    ExecCodeDist.branch_neg hc_neg he_eval_ren
  have hy_out_ext : y_ext.regs (coreReg H.outReg) = (H.eval t.latent u).val := by
    change (y_ext.comap coreReg).regs H.outReg = (H.eval t.latent u).val
    rw [Data.comap_extend coreReg_injective]
    exact hy_out
  have hy_base_ext : y_ext.regs (coreReg H.baseReg) = base := by
    change (y_ext.comap coreReg).regs H.baseReg = base
    rw [Data.comap_extend coreReg_injective]
    exact hy_base
  refine ⟨y_ext, ?_, hy_ext_bdd, ?_, hy_mem, hy_base_ext⟩
  · refine (he_z.seq_pure he_branch).congr_dist rfl (le_of_eq ?_)
    simp only [charge, Nat.cast_add, Nat.cast_ofNat]
    ring
  · simp [decode, hy_out_ext, (H.eval t.latent u).isLt]

private theorem steps_subroutineCode
    (H : Impl B r_core k_init w base U m params)
    (ValidOpSeq : List (HashFamily.Op U) → Prop)
    (Contract : List (HashFamily.Op U) → PMF (List (HashFamily.Label U m)) → Prop)
    (remOps : List (HashFamily.Op U))
    (ν : PMF (SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)))
    (hsupp : ∀ t ∈ ν.support,
      t.data.Bounded w ∧
      t.data.regs (coreReg H.baseReg) = base ∧
      H.tableRep t.data.mem ∧
      H.seedRep t.latent t.data.mem) :
    let S : DataStructure.ObliviousSequenceSpec :=
      ⟨HashFamily.Op U, @HashFamily.Result U m, ValidOpSeq, Contract⟩
    ∃ (ν_final : PMF (SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)))
      (T_ops : ℝ≥0∞),
      ExecSteps H.subroutineCode S H.Seed w base H.space H.encode H.decode
        remOps ν ν_final T_ops ∧
      ν_final.map SeqOutcome.transcript =
        ν.bind (fun t =>
          (HashFamily.evalOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval t.latent
            remOps).map (fun suf => t.transcript ++ suf)) ∧
      T_ops ≤ (((remOps.map H.charge).sum : ℕ) : ℝ≥0∞) := by
  intro S
  induction remOps generalizing ν with
  | nil =>
    refine ⟨ν, 0, ExecSteps.nil (S := S) ν, ?_, by simp⟩
    ext tr
    simp [HashFamily.evalOpsFromSeed]
  | cons o os ih =>
    cases o with
    | resample =>
      classical
      let hasInv (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)) : Prop :=
        t.data.Bounded w ∧ t.data.regs (coreReg H.baseReg) = base ∧ H.tableRep t.data.mem
      let θ₀ : H.Seed := Classical.arbitrary H.Seed
      let μ_step (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)) :
          PMF (StepOutcome H.Seed PUnit (r_core + 5)) :=
        if ht : hasInv t then
          Classical.choose (H.step_resample_subroutineCode t ht.1 ht.2.1 ht.2.2)
        else
          PMF.pure ⟨θ₀, t.data, PUnit.unit⟩
      let T_step : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5) → ℝ≥0∞ :=
        fun _ => ((H.charge .resample : ℕ) : ℝ≥0∞)
      let ν₁ := ν.bind fun t => (μ_step t).map (t.appendStep .resample)
      have hsupp₁ : ∀ q_seq ∈ ν₁.support,
          q_seq.data.Bounded w ∧
          q_seq.data.regs (coreReg H.baseReg) = base ∧
          H.tableRep q_seq.data.mem ∧
          H.seedRep q_seq.latent q_seq.data.mem := by
        intro q_seq hq_seq
        rw [PMF.mem_support_bind_iff] at hq_seq
        obtain ⟨t, ht, hq_map⟩ := hq_seq
        rw [PMF.mem_support_map_iff] at hq_map
        obtain ⟨q, hq, rfl⟩ := hq_map
        have ht_inv : hasInv t := ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1⟩
        have hμ_eq : μ_step t =
            Classical.choose (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2.1 ht_inv.2.2) := by
          simp [μ_step, ht_inv]
        rw [hμ_eq] at hq
        have hspec := (Classical.choose_spec
          (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2.1 ht_inv.2.2)).2.2 q hq
        exact ⟨hspec.1, hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩
      obtain ⟨ν_final, T_rest, hex_rest, htr_rest, hcost_rest⟩ := ih ν₁ hsupp₁
      have hex_cons : ExecSteps H.subroutineCode S H.Seed w base H.space
          H.encode H.decode (.resample :: os) ν ν_final
          ((∑' t, ν t * T_step t) + T_rest) := by
        refine ExecSteps.cons (S := S) (μ_step := μ_step) (T_step := T_step)
          (fun t ht => ?_) hex_rest
        have ht_inv : hasInv t := ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1⟩
        have hμ_eq : μ_step t =
            Classical.choose (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2.1 ht_inv.2.2) := by
          simp [μ_step, ht_inv]
        have hspec := Classical.choose_spec
          (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2.1 ht_inv.2.2)
        rw [hμ_eq]
        exact ⟨ht_inv.1, H.arguments_fit .resample,
          (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare_bounded ht_inv.1
            (H.arguments_fit .resample),
          hspec.1,
          fun q hq => ⟨(hspec.2.2 q hq).1, (hspec.2.2 q hq).2.1, (hspec.2.2 q hq).2.2.1⟩⟩
      have hT₁ : (∑' t, ν t * T_step t) = ((H.charge .resample : ℕ) : ℝ≥0∞) := by
        dsimp only [T_step]
        rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
      refine ⟨ν_final, (∑' t, ν t * T_step t) + T_rest, hex_cons, ?_, ?_⟩
      · rw [htr_rest]
        dsimp only [ν₁]
        rw [PMF.bind_bind]
        refine PMF.bind_congr_on_support _ _ _ fun t ht => ?_
        have ht_inv : hasInv t := ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1⟩
        have hμ_eq : μ_step t =
            Classical.choose (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2.1 ht_inv.2.2) := by
          simp [μ_step, ht_inv]
        have hunif_t : (μ_step t).map StepOutcome.latent = PMF.uniformOfFintype H.Seed := by
          rw [hμ_eq]
          exact (Classical.choose_spec
            (H.step_resample_subroutineCode t ht_inv.1 ht_inv.2.1 ht_inv.2.2)).2.1
        rw [PMF.bind_map, HashFamily.evalOpsFromSeed, PMF.map_bind, ← hunif_t, PMF.bind_map]
        refine congrArg ((μ_step t).bind ·) (funext fun q => ?_)
        rcases q with ⟨θ', x_q, ⟨⟩⟩
        dsimp only [Function.comp_apply, StepOutcome.latent]
        rw [PMF.map_comp]
        refine congrArg (PMF.map · _) (funext fun suf => ?_)
        simp [SeqOutcome.appendStep]
      · simp only [List.map_cons, List.sum_cons, Nat.cast_add, hT₁]
        exact add_le_add le_rfl hcost_rest
    | eval u =>
      classical
      let hasInv (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)) : Prop :=
        t.data.Bounded w ∧
        t.data.regs (coreReg H.baseReg) = base ∧
        H.tableRep t.data.mem ∧
        H.seedRep t.latent t.data.mem
      let yOf (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)) :
          Data (r_core + 5) :=
        if ht : hasInv t then
          Classical.choose (H.step_eval_subroutineCode u t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2)
        else
          t.data
      let μ_step (t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)) :
          PMF (StepOutcome H.Seed (Fin m) (r_core + 5)) :=
        PMF.pure ⟨t.latent, yOf t, H.eval t.latent u⟩
      let T_step : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5) → ℝ≥0∞ :=
        fun _ => ((H.charge (.eval u) : ℕ) : ℝ≥0∞)
      let ν₁ := ν.bind fun t => (μ_step t).map (t.appendStep (.eval u))
      have hsupp₁ : ∀ q_seq ∈ ν₁.support,
          q_seq.data.Bounded w ∧
          q_seq.data.regs (coreReg H.baseReg) = base ∧
          H.tableRep q_seq.data.mem ∧
          H.seedRep q_seq.latent q_seq.data.mem := by
        intro q_seq hq_seq
        rw [PMF.mem_support_bind_iff] at hq_seq
        obtain ⟨t, ht, hq_map⟩ := hq_seq
        rw [PMF.mem_support_map_iff] at hq_map
        obtain ⟨q, hq, rfl⟩ := hq_map
        dsimp only [μ_step] at hq
        rw [PMF.support_pure, Set.mem_singleton_iff] at hq
        subst hq
        have ht_inv : hasInv t := hsupp t ht
        have hy_eq : yOf t = Classical.choose
            (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2.1 ht_inv.2.2.2) := by
          simp [yOf, ht_inv]
        have hspec := Classical.choose_spec
          (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2.1 ht_inv.2.2.2)
        dsimp only [SeqOutcome.appendStep]
        rw [hy_eq, hspec.2.2.2.1]
        exact ⟨hspec.2.1, hspec.2.2.2.2, ht_inv.2.2.1, ht_inv.2.2.2⟩
      obtain ⟨ν_final, T_rest, hex_rest, htr_rest, hcost_rest⟩ := ih ν₁ hsupp₁
      have hex_cons : ExecSteps H.subroutineCode S H.Seed w base H.space
          H.encode H.decode (.eval u :: os) ν ν_final
          ((∑' t, ν t * T_step t) + T_rest) := by
        refine ExecSteps.cons (S := S) (μ_step := μ_step) (T_step := T_step)
          (fun t ht => ?_) hex_rest
        have ht_inv : hasInv t := hsupp t ht
        have hy_eq : yOf t = Classical.choose
            (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2.1 ht_inv.2.2.2) := by
          simp [yOf, ht_inv]
        have hspec := Classical.choose_spec
          (H.step_eval_subroutineCode u t ht_inv.1 ht_inv.2.1 ht_inv.2.2.1 ht_inv.2.2.2)
        refine ⟨ht_inv.1, H.arguments_fit (.eval u),
          (H.subroutineCode.toDynamicProgram H.encode H.decode).prepare_bounded ht_inv.1
            (H.arguments_fit (.eval u)), ?_, ?_⟩
        · simpa [μ_step, hy_eq] using hspec.1
        · intro q hq
          dsimp only [μ_step] at hq
          rw [PMF.support_pure, Set.mem_singleton_iff] at hq
          subst hq
          refine ⟨by simpa [hy_eq] using hspec.2.1, by simpa [hy_eq] using hspec.2.2.1, ?_⟩
          rw [hy_eq, hspec.2.2.2.1]
          exact Modifies.refl _ _
      have hT₁ : (∑' t, ν t * T_step t) = ((H.charge (.eval u) : ℕ) : ℝ≥0∞) := by
        dsimp only [T_step]
        rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
      refine ⟨ν_final, (∑' t, ν t * T_step t) + T_rest, hex_cons, ?_, ?_⟩
      · rw [htr_rest]
        dsimp only [ν₁, μ_step]
        rw [PMF.bind_bind]
        refine PMF.bind_congr_on_support _ _ _ fun t _ => ?_
        rw [PMF.pure_map, PMF.pure_bind, HashFamily.evalOpsFromSeed, PMF.map_comp]
        refine congrArg (PMF.map · _) (funext fun suf => ?_)
        simp [SeqOutcome.appendStep]
      · simp only [List.map_cons, List.sum_cons, Nat.cast_add, hT₁]
        exact add_le_add le_rfl hcost_rest

/-- Executing any `ops : List (HashFamily.Op U)` on `H.subroutineCode` from an initial distribution
`ν₀` satisfying `H.initInv ν₀` produces a final state distribution `ν_final` whose transcript
marginal equals `HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval ops`. -/
theorem evalOps_execSteps
    (H : Impl B r_core k_init w base U m params)
    (ValidOpSeq : List (HashFamily.Op U) → Prop)
    (Contract : List (HashFamily.Op U) → PMF (List (HashFamily.Label U m)) → Prop)
    (ops : List (HashFamily.Op U))
    (ν₀ : PMF (LatentState H.Seed (r_core + 5)))
    (hinv : H.initInv ν₀) :
    let S : DataStructure.ObliviousSequenceSpec :=
      ⟨HashFamily.Op U, @HashFamily.Result U m, ValidOpSeq, Contract⟩
    ∃ (ν_final : PMF (SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5)))
      (T_ops : ℝ≥0∞),
      ExecSteps H.subroutineCode S H.Seed w base H.space H.encode H.decode
        ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      ν_final.map SeqOutcome.transcript =
        HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval ops ∧
      T_ops ≤ (((ops.map H.charge).sum : ℕ) : ℝ≥0∞) := by
  intro S
  have hsupp_seq : ∀ t ∈ (ν₀.map (SeqOutcome.ofLatentState
      (Result := @HashFamily.Result U m))).support,
      t.data.Bounded w ∧
      t.data.regs (coreReg H.baseReg) = base ∧
      H.tableRep t.data.mem ∧
      H.seedRep t.latent t.data.mem := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact hinv.2 u hu
  obtain ⟨ν_final, T_ops, hex, htr, hcost⟩ :=
    H.steps_subroutineCode ValidOpSeq Contract ops (ν₀.map SeqOutcome.ofLatentState) hsupp_seq
  refine ⟨ν_final, T_ops, hex, ?_, hcost⟩
  rw [htr, PMF.bind_map]
  have hbind_eq :
      (ν₀.bind
        ((fun t : SeqOutcome H.Seed (@HashFamily.Result U m) (r_core + 5) =>
            (HashFamily.evalOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval t.latent
              ops).map fun suf => t.transcript ++ suf) ∘
          SeqOutcome.ofLatentState)) =
        (ν₀.map LatentState.latent).bind
          (fun θ₀ =>
            HashFamily.evalOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval θ₀ ops) := by
    rw [PMF.bind_map]
    refine congrArg (ν₀.bind ·) (funext fun u => ?_)
    dsimp only [Function.comp_apply, SeqOutcome.ofLatentState, List.nil_append]
    exact PMF.map_id _
  rw [hbind_eq, hinv.1]
  rfl

/-- Package `H : Impl` into an `ObliviousSequenceImpl` certificate for any oblivious-sequence
specification `⟨HashFamily.Op U, HashFamily.Result m, ValidOpSeq, Contract⟩` satisfied by
`HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval`. -/
@[expose] noncomputable def toObliviousSequenceImpl
    (H : Impl B r_core k_init w base U m params)
    (ValidOpSeq : List (HashFamily.Op U) → Prop)
    (Contract : List (HashFamily.Op U) → PMF (List (HashFamily.Label U m)) → Prop)
    (hcontract : ∀ ops, ValidOpSeq ops →
      Contract ops (HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval ops)) :
    ObliviousSequenceImpl.{0, 0, 0} H.subroutineCode
      ⟨HashFamily.Op U, @HashFamily.Result U m, ValidOpSeq, Contract⟩
      w base params where
  Latent := H.Seed
  space := H.space
  spanTime := 3
  setupTime := ((H.initTableSteps + H.resampleSteps : ℕ) : ℝ≥0∞)
  initPotential := 0
  charge := H.charge
  initInv := H.initInv
  encode := H.encode
  decode := H.decode
  bounded hinv t ht := (hinv.2 t ht).1
  arguments_fit o _ := H.arguments_fit o
  clear_nodup := by exact H.clear_nodup_subroutineCode
  params_not_clear := by exact H.params_not_clear_subroutineCode
  incCur_eval {x} hone hfit := by
    have h := H.addReg_eval (x := x) (curReg r_core) (curReg r_core) (oneReg r_core)
    rw [show x.regs (oneReg r_core) = 1 from hone] at h
    exact h hfit
  span_exec _ hfr hpar := by exact H.span_exec_subroutineCode hfr hpar
  setup_exec hx₁ hb hfr hpar hz := by exact H.setup_exec_subroutineCode hx₁ hb hfr hpar hz
  steps_exec ops ν₀ hv hinv := by
    obtain ⟨ν_final, T_ops, hex, htr, hcost⟩ :=
      H.evalOps_execSteps ValidOpSeq Contract ops ν₀ hinv
    refine ⟨ν_final, T_ops, hex, ?_, ?_⟩
    · dsimp only
      rw [htr]
      exact hcontract ops hv
    · simpa using hcost

@[simp]
theorem toObliviousSequenceImpl_space
    (H : Impl B r_core k_init w base U m params)
    (ValidOpSeq) (Contract) (hcontract) :
    (H.toObliviousSequenceImpl ValidOpSeq Contract hcontract).space = H.space := by rfl

@[simp]
theorem toObliviousSequenceImpl_initPotential
    (H : Impl B r_core k_init w base U m params)
    (ValidOpSeq) (Contract) (hcontract) :
    (H.toObliviousSequenceImpl ValidOpSeq Contract hcontract).initPotential = 0 := by rfl

@[simp]
theorem toObliviousSequenceImpl_charge
    (H : Impl B r_core k_init w base U m params)
    (ValidOpSeq) (Contract) (hcontract) :
    (H.toObliviousSequenceImpl ValidOpSeq Contract hcontract).charge = H.charge := by rfl

/-- **Canonical `ObliviousSequenceImpl` certificate for `HashFamily.kWiseSpec k U m`:**
every `H : Impl` whose evaluation map satisfies `IsKWiseIndependentHash k H.eval`
canonically realizes `DataStructure.HashFamily.kWiseSpec k U m`. -/
@[expose] noncomputable def toKWiseObliviousSequenceImpl [NeZero m]
    (H : Impl B r_core k_init w base U m params)
    {k : ℕ} (hk : IsKWiseIndependentHash k H.eval) :
    ObliviousSequenceImpl.{0, 0, 0} H.subroutineCode
      (HashFamily.kWiseSpec k U m) w base params :=
  H.toObliviousSequenceImpl
    (HashFamily.kWiseSpec k U m).ValidOpSeq
    (HashFamily.kWiseSpec k U m).Contract
    (fun _ hv => HashFamily.kWiseSpec_contract_evalOps hk hv)

/-- **Canonical `ObliviousSequenceImpl` certificate for `HashFamily.whpKWiseSpec k U m δ`:**
every `H : Impl` with a two-level seed decomposition `e : H.Seed ≃ (TopSeed × BotSeed)` and
a good top-seed set `GoodTop : Finset TopSeed` on which `fun β => H.eval (e.symm (α, β))` is
`k`-wise independent canonically realizes `DataStructure.HashFamily.whpKWiseSpec k U m δ` with
`δ = (#(Finset.univ \ GoodTop) : ℝ≥0∞) / (Fintype.card TopSeed : ℝ≥0∞)`. -/
@[expose] noncomputable def toWhpKWiseObliviousSequenceImpl [NeZero m]
    {TopSeed BotSeed : Type} [Fintype TopSeed] [DecidableEq TopSeed] [Nonempty TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    (H : Impl B r_core k_init w base U m params)
    (e : H.Seed ≃ (TopSeed × BotSeed))
    {k : ℕ} (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop,
      IsKWiseIndependentHash k (fun β : BotSeed => H.eval (e.symm (α, β)))) :
    ObliviousSequenceImpl.{0, 0, 0} H.subroutineCode
      (HashFamily.whpKWiseSpec k U m
        (((Finset.univ \ GoodTop).card : ℝ≥0∞) / (Fintype.card TopSeed : ℝ≥0∞)))
      w base params :=
  let δ := (((Finset.univ \ GoodTop).card : ℝ≥0∞) / (Fintype.card TopSeed : ℝ≥0∞))
  H.toObliviousSequenceImpl
    (HashFamily.whpKWiseSpec k U m δ).ValidOpSeq
    (HashFamily.whpKWiseSpec k U m δ).Contract
    (fun _ hv =>
      HashFamily.whpKWiseSpec_contract_evalOps_equiv H.eval e GoodTop hgood hv)

end Impl

end Cslib.DataStructure.HashFamily.WordRAM
